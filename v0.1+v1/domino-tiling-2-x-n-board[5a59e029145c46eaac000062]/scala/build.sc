import mill._, scalalib._

object `package` extends RootModule with ScalaModule {
  def scalaVersion = "2.13.15"

  object sample extends ScalaTests with TestModule.ScalaTest {
    def ivyDeps = Agg(ivy"org.scalatest::scalatest:3.0.8")
  }
}
