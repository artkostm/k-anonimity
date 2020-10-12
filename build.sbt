lazy val k_anonimity = (project in file(".")).settings(
  name := "k-anonimity",
  version := "1.0",
  scalaVersion := "2.12.10",
  libraryDependencies ++= Seq(
    "io.argonaut" %% "argonaut" % "6.2.2",
    "org.apache.spark" %% "spark-core" % "3.0.0" % Provided,
    "org.apache.spark" %% "spark-sql" % "3.0.0" % Provided
  )
)