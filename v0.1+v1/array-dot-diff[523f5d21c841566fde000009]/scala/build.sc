import mill._, scalalib._

object array_dot_diff extends RootModule with ScalaModule {
  def scalaVersion = "3.3.1"

  object sample extends ScalaTests with TestModule.ScalaTest {
    def ivyDeps = Agg(ivy"org.scalatest::scalatest:3.2.10")
  }
}
