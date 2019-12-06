lazy val commonSettings = Seq(
  name := "ostrich",
  organization := "uuverifiers",
  version := "1.0",
  scalaVersion := "2.11.8",
  crossScalaVersions := Seq("2.11.8", "2.12.6"),
  publishTo := Some(
    Resolver.file("file", new File("/home/wv/public_html/maven/"))
  ),
  scalacOptions ++= Seq(
    "-deprecation",
    //"-Xfatal-warnings",
    "-unchecked",
    "-Xlint",
    "-feature",
    "-optimize",
    "-Ywarn-dead-code",
    "-Ywarn-unused"
  ),
  resolvers += ("uuverifiers" at "http://logicrunch.research.it.uu.se/maven/")
    .withAllowInsecureProtocol(true),
  libraryDependencies += "uuverifiers" %% "princess" % "2018-10-26",
//  libraryDependencies += "uuverifiers" %% "princess" % "nightly-SNAPSHOT",
  libraryDependencies += "org.sat4j" % "org.sat4j.core" % "2.3.1",
  libraryDependencies += "org.scalacheck" %% "scalacheck" % "1.14.0" % "test"
)

lazy val root = (project in file("."))
  .settings(commonSettings: _*)
  .settings(
    mainClass in Compile := Some("strsolver.SMTLIBMain")
    // unmanagedSourceDirectories in Test += baseDirectory.value / "replaceall-benchmarks" / "src" / "test" / "scala"
  )
