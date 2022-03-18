// build.sc
import mill._, scalalib._

object scalaTage extends CrossSbtModule {
    // override def millSourcePath = millOuterCtx.millSourcePath
    def crossScalaVersion  = "2.13.8"
}   