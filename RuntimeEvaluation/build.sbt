name := "RuntimeEvaluation"

version := "1.0"

organization := "ch.epfl.lara"

scalaVersion := "2.11.7"

fork in run := true

scalaSource in Compile := baseDirectory.value / "src"

//javaOptions in run ++= Seq("-Xmx3G", "-Xms3G", "-Xss500M")

//unmanagedJars in Compile += file("lib/macmemo.jar")

//scalacOptions ++= Seq("-optimise")

//libraryDependencies += "org.scala-lang" % "scala-reflect" % "2.11.5"
