package scalaTage

import scala.collection.mutable
import scala.util.matching.Regex
import scala.collection.immutable.Queue
import scala.collection.immutable.HashMap
// import scala.collection.immutable._
import scala.math._
import scala.util._
import sys.process._
import java.io.File
import sys._

trait ArgParser {
    val usage = """
        Usage: [--log-in-debug logname] | [--run-cputest]
    """
    type OptionMap = Map[Symbol, Any]
    
    def getLogs(path: String): Array[String] = {
        val files = s"ls $path".!!.split('\n')
        val logPattern = raw"log".r.unanchored
        files.map(f => if ((logPattern findAllIn f).length != 0) path+f else "").filter(_ != "").toArray
    }

    def parse(args: Array[String]) = {
        if (args.length == 0) println(usage)
        val arglist = args.toList

        def fileToPathInDebug(file: String) = env("NOOP_HOME") + "/debug/" + file + ".log"
        def fileToPath(file: String) = env("NOOP_HOME") + "/" + file + ".log"
        @scala.annotation.tailrec
        def nextOption(map : OptionMap, list: List[String]) : OptionMap = {
            def isSwitch(s : String)= (s(0) == '-')
            list match {
                case Nil => map
                case "--log-in-debug" :: file :: tail => 
                    nextOption(map ++ Map('file -> fileToPathInDebug(file)), tail)
                case "--log" :: file :: tail =>
                    nextOption(map ++ Map('file -> fileToPath(file)), tail)
                case "--raw" :: file :: tail =>
                    nextOption(map ++ Map('file -> file), tail)
                case "--run-cputest" :: tail =>
                    nextOption(map ++ Map('multipleFiles -> getLogs("/home/glr/nexus-am/tests/cputest/build/")), tail)
                case "--his" :: value :: tail =>
                    nextOption(map ++ Map('hislen -> value.toInt), tail)
                case "--updateOnUncond" :: tail =>
                    nextOption(map ++ Map('updateOnUncond -> true), tail)
                case "--withLoop" :: tail =>
                    nextOption(map ++ Map('withLoop -> true), tail)
                case "--superscalar" :: tail =>
                    nextOption(map ++ Map('superscalar -> true), tail)
                case "--useGem5" :: tail =>
                    nextOption(map ++ Map('useGem5 -> true), tail)
                case "--useXS" :: tail =>
                    nextOption(map ++ Map('useXS -> true), tail)
                case "--useSC" :: tail =>
                    nextOption(map ++ Map('useStatisticalCorrector -> true), tail)
                case "--tageCtrBits" :: value :: tail =>
                    nextOption(map ++ Map('tageCtrBits -> value.toInt), tail)
                case "-t" :: threads :: tail =>
                    nextOption(map ++ Map('threads -> threads.toInt), tail)
                case "--hist-lengths" :: h :: tail => {
                    // println(h)
                    val hlArr = h.split(",").map(_.toInt)
                    // println(hlArr.mkString)
                    nextOption(map ++ Map('hl -> hlArr), tail)
                }
                // case string :: opt2 :: tail if isSwitch(opt2) => 
                //                     nextOption(map ++ Map('infile -> string), list.tail)
                // case string :: Nil =>  nextOption(map ++ Map('infile -> string), list.tail)
                case option :: tail => { println("Unknown option "+option); nextOption(map, list.tail); }
            }
        }
        val ops = nextOption(Map(),arglist)
        // if (!ops.contains('file))
        //     ops ++ Map('file -> fileToPathInDebug("dhrystone"))
        // else
        ops
    }
}

trait RunnerUtils {
    this: ArgParser =>
    def getName(ops: OptionMap): String = ""
}


class BranchPredictorRunner() extends RunnerUtils with ArgParser with FileIOUtils {
    val tw = new TraceWrapper()

    val maxBrPrint = 10

    val defaultInput = "/home/glr/XiangShan/debug/dhrystone.log"
    
    //                    pc  , (mis, cor)
    type Stats = HashMap [Long, List[Int]]

    case class UpdateQueueElem(cycle: Long, isBr: Boolean, pc: Long, taken: Boolean, misPred: Boolean) {}
    case class PcycleQueueElem(pcycle: Long, pc: Long, isBr: Boolean) {}
    
    type UpdateQ = Queue[UpdateQueueElem]
    type PcycleQ = Queue[PcycleQueueElem]


    def getCfiPreds(s: scala.io.BufferedSource): Iterator[Any]   = tw.getCFIPredInfosFromSource(s)
    def getCfiUpdates(s: scala.io.BufferedSource): Iterator[Any] = tw.getCFIUpdateInfosFromSource(s)
    def getGeneralCfiInfos(s: scala.io.BufferedSource): Iterator[Any] = tw.getGeneralCFIInfosFromSource(s)

    def dumbCFI = CFIUpdateInfo(0, false, 0, false, false, 0, 0, 0, false)

    def getAndPrintPreds(stats: Stats): (Int, Int, Int) = {
        var brPrint = 0
        var totalPred = 0
        var totalMiss = 0
        var totalCorr = 0
        stats.toList.sortBy(_._2(0)).reverse.foreach{ case(pc, arr) => {
            val miss = arr(0)
            val corr = arr(1)
            if (brPrint < maxBrPrint) { println(f"pc: $pc%x, mispredict: ${miss}%10d, correct: ${corr}%10d, total: ${miss+corr}%10d, missrate: ${miss*100/(miss+corr).toDouble}%3.2f%%"); brPrint += 1; }
            totalMiss += arr(0)
            totalCorr += arr(1)
            totalPred += arr.reduce(_+_)
        }}
        (totalMiss, totalCorr, totalPred)
    }
    
    @scala.annotation.tailrec
    private def consumeCFI(stats: Stats, it: Iterator[Any])(implicit bp: BasePredictor): Stats = {
        def onCFI(pc: Long, isBr: Boolean, taken: Boolean): Option[Tuple2[Long, List[Int]]] = {
            bp.predict(pc, isBr)
            if (isBr) {
                val mispred = bp.update(pc, taken)
                val l = 
                    if (mispred) {
                        if (stats.contains(pc)) List(stats(pc)(0) + 1, stats(pc)(1))
                        else List(1, 0)
                    }
                    else {
                        if (stats.contains(pc)) List(stats(pc)(0), stats(pc)(1) + 1)
                        else List(0, 1)
                    }
                Some((pc, l))
            } else {
                bp.updateUncond(pc)
                None
            }
        }
        def emptyStats = HashMap[Long, List[Int]]()

        if (it.hasNext) {
            it.next() match {
                case CFIUpdateInfo(cycle, isBr, pc, taken, misPred, pcycle, _, _, _) => {
                    val newStat = onCFI(pc, isBr, taken)
                    if (newStat.isDefined) {
                        consumeCFI(stats + newStat.get, it)
                    } else {
                        consumeCFI(stats, it)
                    }
                }
                case GeneralCFIInfo(pc, ty, target, taken) => {
                    val newStat = onCFI(pc, ty == 0, taken)
                    if (newStat.isDefined) {
                        consumeCFI(stats + newStat.get, it)
                    } else {
                        consumeCFI(stats, it)
                    }
                }
                case "--------20M--------" => { // warm up finishes, reset stats
                    consumeCFI(emptyStats, it)
                }
                case _ => consumeCFI(stats, it)
            }
        }
        else {
            println("ends")
            stats
        }
    }

    def runWithCFIInfo(cfis: Iterator[Any])(implicit bp: BasePredictor) = {
        val emptyStats = HashMap[Long, List[Int]]()
        val uQ  = Queue[UpdateQueueElem]()
        val pQ  = Queue[PcycleQueueElem]()

        val stats = consumeCFI(emptyStats, cfis)
        bp.onFinish

        println(f"Printing top $maxBrPrint%d mispredicted branches:")

        val (totalMispred, totalCorrect, totalBrs) = getAndPrintPreds(stats)

        println(f"Totally mispredicted $totalMispred%d out of $totalBrs%d branches")

        // after one program is done, flush predictor for the next program
        bp.flush

        (totalCorrect, totalMispred)
    }

    def runWithLog(log: String)(implicit bp: BasePredictor): (String, (Int, Int)) = {
        val l = new File(log)
        if (l.exists()) {
            println(s"processing log $l")
            val res = readFile[(Int, Int)](log, s => runWithCFIInfo(getCfiUpdates(s))).get//OrElse((1,1))
            // val res = readFile[(Int, Int)](log, s => runWithCFIInfo(getGeneralCfiInfos(s))).get//OrElse((1,1))
            (log, res)
        }
        else {
            println(s"$l not exists, returning null result")
            (log, (1, 1))
        }
    }

    def runWithLogs(logs: Array[String])(implicit bp: BasePredictor): Array[(String, (Int, Int))] = logs.map(runWithLog(_)).toArray

    def printRes(res: Array[(String, (Int, Int))]) = {
        var mr = 100.0
        res.foreach { case(l, (c, m)) => {
            val missrate = (m*100).toDouble/(c+m)
            println(f"test: ${l.split('/').last}%20s, $m%6d/${c+m}%8d mispredicted, missrate: ${missrate}%3.3f%%")
            mr = missrate
        }}
        mr
    }

    def checkOps(ops: OptionMap) = {
        if (ops.contains('file) && ops.contains('multipleFiles)) {
            println("Conflict arguments, you could only use --log-in-debug OR --run-cputest")
            System.exit(1)
        }
    }

    def run(ops: OptionMap) = {
        implicit val bp = if (true) Tage(ops) else PerceptronBP(ops)
        println(f"Running with ${bp}%s")
        checkOps(ops)
        val res = 
            if (ops.contains('file)) {
                // tw.getXSResult(ops('file).toString)
                Array(runWithLog(ops('file).toString))
            }
            else if (ops.contains('multipleFiles)) {
                val files = ops('multipleFiles).asInstanceOf[Array[String]]
                files.foreach(tw.getXSResult(_))
                runWithLogs(files)
            }
            else {
                println("No input specified, running on default dhrystone\n")
                Array(runWithLog(defaultInput))
            }
        printRes(res)
    }
}

object BranchPredictorRunnerTest extends RunnerUtils with ArgParser {
    def main(args: Array[String]): Unit = {
        val options = parse(args)
        println(options.mkString)
        val bpr = new BranchPredictorRunner()
        val mr = bpr.run(options)
        println(mr)
    }
}