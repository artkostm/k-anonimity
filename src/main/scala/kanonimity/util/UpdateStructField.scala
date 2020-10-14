package kanonimity.util

import org.apache.spark.sql.catalyst.InternalRow
import org.apache.spark.sql.catalyst.analysis.TypeCheckResult
import org.apache.spark.sql.catalyst.expressions.codegen.Block._
import org.apache.spark.sql.catalyst.expressions.{Expression, GenericInternalRow}
import org.apache.spark.sql.catalyst.expressions.codegen.{CodeGenerator, CodegenContext, ExprCode, FalseLiteral}
import org.apache.spark.sql.catalyst.plans.logical.LogicalPlan
import org.apache.spark.sql.catalyst.rules.Rule
import org.apache.spark.sql.types.{StringType, StructField, StructType}
import org.apache.spark.unsafe.types.UTF8String

import scala.annotation.tailrec

object UpdateStructField {
  object simplifyUpdateStructFields extends Rule[LogicalPlan] {
    override def apply(plan: LogicalPlan): LogicalPlan = plan transformExpressions {
      case UpdateStructField(UpdateStructField(exprsA) :: exprsB) =>
        UpdateStructField(exprsA ++ exprsB)
//      case y@UpdateStructField(x) =>
//        println(x.lastOption)
//        y
    }
  }

  lazy val rules: Seq[Rule[LogicalPlan]] = Seq(
    simplifyUpdateStructFields
  )
}

protected[util] case class UpdateStructField(children: Seq[Expression]) extends Expression {
  private lazy val struct: Expression = children.head
  private lazy val (nameExpr, valExpr) = children
    .drop(1)
    .grouped(2)
    .map {
      case Seq(name, value) => (name, value)
    }
    .toList
    .unzip
  private lazy val fieldNames               = nameExpr.map(_.eval().asInstanceOf[UTF8String].toString)
  private lazy val pairs                    = fieldNames.zip(valExpr)
  private lazy val ogStructType: StructType = struct.dataType.asInstanceOf[StructType]

  override def nullable: Boolean = struct.nullable

  override def eval(input: InternalRow): Any = {
    val structValue = struct.eval(input)
    if (structValue == null) {
      null
    } else {
      val existingValues =
        ogStructType.fieldNames.zip(structValue.asInstanceOf[InternalRow].toSeq(ogStructType))
      val addOrReplaceValues = pairs.map {
        case (fieldName, expression) => (fieldName, expression.eval(input))
      }
      val newValues = loop(existingValues, addOrReplaceValues).map(_._2)
      InternalRow.fromSeq(newValues)
    }
  }

  override def dataType: StructType = {
    val existingFields = ogStructType.fields.map(x => (x.name, x))
    val addOrReplaceFields = pairs.map {
      case (fieldName, field) => (fieldName, StructField(fieldName, field.dataType, field.nullable))
    }

    val newFields = loop(existingFields, addOrReplaceFields).map(_._2)
    StructType(newFields)
  }

  override def checkInputDataTypes(): TypeCheckResult =
    if (children.size % 2 == 0)
      TypeCheckResult.TypeCheckFailure(s"$prettyName expects an odd number of args.")
    else if (struct.dataType.typeName != StructType(Nil).typeName)
      TypeCheckResult.TypeCheckFailure(
        s"Only ${StructType(Nil).typeName} is allowed to appear at first position."
      )
    else if (nameExpr.contains(null) || nameExpr.exists(e => !(e.foldable && e.dataType == StringType)))
      TypeCheckResult.TypeCheckFailure(
        s"Only non-null foldable ${StringType.catalogString} expressions are allowed to appear at even position."
      )
    else if (valExpr.contains(null))
      TypeCheckResult.TypeCheckFailure(
        s"Only non-null expressions are allowed to appear at odd positions after first position."
      )
    else TypeCheckResult.TypeCheckSuccess

  override def prettyName: String = "UpdateStructField"

  override protected def doGenCode(ctx: CodegenContext, ev: ExprCode): ExprCode = {
    val structGen             = struct.genCode(ctx)
    val addOrReplaceFieldsGen = valExpr.map(_.genCode(ctx))
    val resultCode: String = {
      val structVar = structGen.value
      type NullCheck = String
      type NonNullValue = String
      val existingFieldsCode: Seq[(String, (NullCheck, NonNullValue))] =
        ogStructType.fields.zipWithIndex.map {
          case (structField, i) =>
            val nullCheck = s"$structVar.isNullAt($i)"
            val nonNullValue = CodeGenerator.getValue(structVar, structField.dataType, i.toString)
            (structField.name, (nullCheck, nonNullValue))
        }
      val addOrReplaceFieldsCode: Seq[(String, (NullCheck, NonNullValue))] =
        fieldNames.zip(addOrReplaceFieldsGen).map {
          case (fieldName, fieldExprCode) =>
            val nullCheck = fieldExprCode.isNull.code
            val nonNullValue = fieldExprCode.value.code
            (fieldName, (nullCheck, nonNullValue))
        }
      val newFieldsCode = loop(existingFieldsCode, addOrReplaceFieldsCode)
      val rowClass = classOf[GenericInternalRow].getName
      val rowValuesVar = ctx.freshName("rowValues")
      val populateRowValuesVar = newFieldsCode.zipWithIndex.map {
        case ((_, (nullCheck, nonNullValue)), i) =>
          s"""
             |if ($nullCheck) {
             | $rowValuesVar[$i] = null;
             |} else {
             | $rowValuesVar[$i] = $nonNullValue;
             |}""".stripMargin
      }.mkString("\n|")

      s"""
         |Object[] $rowValuesVar = new Object[${dataType.length}];
         |
         |${addOrReplaceFieldsGen.map(_.code).mkString("\n")}
         |$populateRowValuesVar
         |
         |${ev.value} = new $rowClass($rowValuesVar);
          """.stripMargin
    }

    if (nullable) {
      val nullSafeEval =
        structGen.code + ctx.nullSafeExec(struct.nullable, structGen.isNull) {
          s"""
             |${ev.isNull} = false; // resultCode could change nullability.
             |$resultCode
             |""".stripMargin
        }

      ev.copy(code =
        code"""
          boolean ${ev.isNull} = true;
          ${CodeGenerator.javaType(dataType)} ${ev.value} = ${CodeGenerator.defaultValue(dataType)};
          $nullSafeEval
          """)
    } else {
      ev.copy(code =
        code"""
          ${structGen.code}
          ${CodeGenerator.javaType(dataType)} ${ev.value} = ${CodeGenerator.defaultValue(dataType)};
          $resultCode
          """, isNull = FalseLiteral)
    }
  }

  @tailrec private def loop[X](existingFields: Seq[(String, X)],
                               addOrReplaceFields: Seq[(String, X)]): Seq[(String, X)] =
    addOrReplaceFields match {
      case head :: tail =>
        if (existingFields.exists(p => p._1 == head._1)) {
          loop(existingFields.map {
            case (fieldName, _) if fieldName == head._1 => head
            case x                                      => x
          }, tail)
        } else {
          loop(existingFields :+ head, tail)
        }
      case Nil => existingFields
    }
}
