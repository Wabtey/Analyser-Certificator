name := "TP67_ACF"

version := "0.1"

scalaVersion := "2.13.9"

//scalacOptions ++= Seq("-deprecation","-feature")

libraryDependencies += "org.scala-lang.modules" %% "scala-parser-combinators" % "1.1.2"

unmanagedBase := baseDirectory.value / "libJars/"
