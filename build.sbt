lazy val commonSettings = Seq(
  name := "ostrich",
  organization := "uuverifiers",
  version := "1.0",
  scalaVersion := "2.11.12",
  publishTo := Some(
    Resolver.file("file", new File("/home/wv/public_html/maven/"))
  ),
  fork in run := true,
  cancelable in Global := true,
  parallelExecution in Test := false,
  scalacOptions ++= Seq(
    "-deprecation",
    //"-Xfatal-warnings",
    "-unchecked",
    "-Xlint",
    // "-feature",
    // "-optimize",
    "-Ywarn-dead-code",
    "-Ywarn-unused"
  ),
  resolvers += ("uuverifiers" at "http://logicrunch.research.it.uu.se/maven/")
    .withAllowInsecureProtocol(true),
  libraryDependencies += "uuverifiers" %% "princess" % "nightly-SNAPSHOT",
  libraryDependencies += "org.scalacheck" %% "scalacheck" % "1.14.0" % "test",
  libraryDependencies += "org.scalatest" %% "scalatest" % "3.0.8" % "test",
  libraryDependencies += "ch.qos.logback" % "logback-classic" % "1.2.3",
  libraryDependencies += "com.typesafe.scala-logging" %% "scala-logging" % "3.9.2"
)


lazy val root = (project in file("."))
  .settings(commonSettings: _*)
  .settings(
    mainClass in Compile := Some("strsolver.SMTLIBMain")
    // unmanagedSourceDirectories in Test += baseDirectory.value / "replaceall-benchmarks" / "src" / "test" / "scala"
  )
