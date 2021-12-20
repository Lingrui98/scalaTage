package scalaTage

import scala.collection.mutable
// import scala.collection.immutable._
import scala.math._
import scala.util._


trait PredictorUtils {
    def satUpdate(taken: Boolean, oldCtr: Int, ctrBits: Int, signed: Boolean = false): Int = {
        val maxVal = if (signed)  (1 << (ctrBits - 1)) - 1 else (1 << ctrBits) - 1
        val minVal = if (signed) -(1 << (ctrBits - 1))     else 0
        // println(f"ctrBits $ctrBits%d, maxVal $maxVal%d, minVal $minVal%d")
        val newCtr = oldCtr match {
            case x if (x >= maxVal && taken) => maxVal
            case y if (y <= minVal && !taken) => minVal
            case _ => if (taken) {oldCtr + 1} else {oldCtr - 1}
        }
        // println(f"old $oldCtr%d -> new $newCtr%d")
        newCtr
    }

    def isPowerOf2(x: Int): Boolean = (x & (x - 1)) == 0
    def log2(x: Int): Int = (log(x) / log(2)).toInt
    def log2Up(x: Int): Int = if (isPowerOf2(x)) log2(x) else log2(x) + 1
    def getMask(len: Int) = (1 << len) - 1
    def getBit(x: Long, pos: Int): Int = (x & (1L << pos)).toInt
    // from 1 to 3: get bits (1,2,3)
    def getBits(x: Long, from: Int, to: Int): Int = (from until to+1).map(i => getBit(x, i)).reduce(_|_) >>> from
    def divUp(x: Int, y: Int): Int = (x / y) + (if (x % y != 0) 1 else 0)

    def boolArrayToLong(arr: Array[Boolean]): Long = {
        // println(f"boolArrayToLong: arr size = ${arr.size}%d")
        arr.zipWithIndex.map{ case (b, i) => (if (b) 1L << i else 0L) }.reduce(_|_)
    }
    def boolArrayToInt(arr: Array[Boolean]): Int = boolArrayToLong(arr).toInt
    def toBoolArray(x: Long, len: Int): Array[Boolean] = {
        (0 until len).map(i => ((x >>> i) & 1) == 1).toArray
    }
    def toBoolArray(x: Int, len: Int): Array[Boolean] = {
        (0 until len).map(i => ((x >>> i) & 1) == 1).toArray
    }
    def PriorityEncoder(arr: Array[Boolean]): Int = {
        def getFirst(arr: List[Boolean], i: Int): Int = {
            arr match {
                case Nil => i - 1
                case true :: tail => i
                case false :: tail => getFirst(tail, i+1)
            }
        }
        getFirst(arr.toList, 0)
    }
    def PriorityEncoder(x: Int, len: Int): Int = PriorityEncoder(toBoolArray(x, len))

    def boolArrayToString(arr: Array[Boolean]): String = arr.map(if(_) "1" else "0").reduce(_+_)

}

trait LogHelper {
    val debug = false
    def Debug(cond: Boolean, info: String): Unit = if (cond && debug) println(info)
    def Debug(info: String): Unit = Debug(debug, info)
}

abstract class BasePredictor extends PredictorUtils with LogHelper {
    def predict(pc: Long, isBr: Boolean): Boolean
    def update(pc: Long, taken: Boolean): Boolean
    def updateUncond(pc: Long): Unit
    def onFinish: Unit
    def flush: Unit
    def name: String
    val updateOnUncond = false

    abstract class PredictionMeta {}
    val obq: mutable.Queue[_ <: PredictionMeta]
    val ghist: GlobalHistory
}

abstract class PredictorComponents extends PredictorUtils {}

class GlobalHistory(val maxHisLen: Int) extends PredictorUtils {
    val arrMaxLen = maxHisLen + 32
    val hist: Array[Boolean] = Array.fill[Boolean](arrMaxLen)(false)
    var ptr: Int = 0
    var count: Int = 0
    def getHistPtr = this.ptr
    def getHist(len: Int = maxHisLen, ptr: Int = this.ptr): Array[Boolean] = {
        if (ptr - len >= 0)
            hist.slice(ptr-len, ptr).reverse
        else
            (hist.slice(ptr-len+arrMaxLen, arrMaxLen) ++ hist.slice(0, ptr)).reverse
    }

    def apply(ptr: Int = this.ptr) = if (ptr >= 0) hist(ptr) else hist(ptr + arrMaxLen)

    def getHistStr(len: Int = maxHisLen, ptr: Int = this.ptr): String = boolArrayToString(this.getHist(len, ptr))

    def updateHist(taken: Boolean) = {
        count += 1
        hist.update(ptr, taken)
        ptr = if (ptr + 1 >= arrMaxLen) 0 else ptr + 1
    }

    def recover(oldPtr: Int) = {
        ptr = oldPtr
    }
}

class FoldedHist(val totalLen: Int, val compLen: Int) extends PredictorUtils {
    var comp: Int = 0
    val outPoint: Int = if (compLen > 0) totalLen % compLen else 0
    val mask = getMask(compLen)
    // println(this)
    def toInt(b: Boolean) = if (b) 1 else 0
    def update(hNew: Boolean, hOld: Boolean): Unit = {
        val temp = comp
        comp = (comp << 1) | toInt(hNew)
        comp ^= toInt(hOld) << outPoint // evict bit
        comp ^= comp >>> compLen        // this highset bit is xored into new hist bit
        comp &= mask
        // println(f"$this%s, outPoint $outPoint%d, oldHist${boolArrayToString(toBoolArray(temp, compLen))}%s, hNew $hNew, hOld $hOld")
    }
    def recover(old: Int) = {
        comp = old & mask
    }
    def apply(): Int = this.comp
    override def toString(): String = f"totalLen:$totalLen%d, foldedLen:$compLen%d, foldedHist:${boolArrayToString(toBoolArray(comp, compLen))}%s"
}

class PathHistory(val len: Int, val selPos: Int = 2) extends PredictorUtils {
    var p: Int = 0
    val mask = getMask(len)
    def update(pc: Long): Unit = p = (((p << 1) | (getBit(pc, selPos) >>> selPos)) & mask).toInt
    def recover(old: Int): Unit = p = old & mask
    def apply() = p
    override def toString(): String = f"pathLen:$len%d, pathHist:${boolArrayToString(toBoolArray(p, len))}%s"
}

case class SatCounter(val bits: Int, val ctr: Int, val signed: Boolean = false) extends PredictorUtils {
    def initVal = 1 << (bits-1)
    def update(inc: Boolean) = this.copy(ctr = satUpdate(inc, this.ctr, this.bits, signed))
    def apply(): Int = if (signed) ctr else ctr - initVal
    def apply(h: Boolean): Int = if (h) apply() else -apply()
    def saturatedPos: Int = if (signed) (1 << (bits - 1)) - 1 else (1 << bits) - 1
    def saturatedNeg: Int = if (signed) -(1 << (bits - 1))    else 0
    def isSaturatedPos(): Boolean = ctr == saturatedPos
    def isSaturatedNeg(): Boolean = ctr == saturatedNeg
}

trait GTimer {
    var cycle: Long = 0
    def step(x: Long) = cycle += x
    def isCycle(x: Long): Boolean = cycle == x
}