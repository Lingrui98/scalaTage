package scalaTage

import scala.collection.mutable
// import scala.collection.immutable._
import scala.math._
import scala.util._


case class TageParams (
    val BimEntries: Int = 4096,
    val BimRatio: Int = 1,
    val minHist: Int = 4,
    val maxHist: Int = 640,
    //                                    Sets  Hist   Tag
    val t: Seq[Tuple3[Int, Int, Int]]  = Seq(( 1024,    4,   7),
                                             ( 1024,    6,   7),
                                             ( 2048,   10,   8),
                                             ( 2048,   16,   8),
                                             ( 2048,   25,   9),
                                             ( 2048,   40,  10),
                                             ( 1024,   64,  11),
                                             ( 1024,  101,  12),
                                             ( 1024,  160,  12),
                                             ( 1024,  254,  13),
                                             (  512,  403,  14),
                                             (  512,  640,  15)),
    val TageBanks: Int = 16, // FetchWidth
    val UBitPeriod: Int = 4096,
    val SuperScalar: Boolean = false,
    val useGem5: Boolean = false,
    val useStatisticalCorrector: Boolean = false,
    val sct: Seq[Tuple2[Int, Int]] = Seq.fill(4)((1024,6)),
    val TageCtrBits: Int = 3
    )
{
    val scThresInit: Int = sct.size
    val TableInfo = t

    val TageNTables = TableInfo.size

    val TageTableBits = TableInfo.map { case (s, h, t) => s * (1+t+TageCtrBits+1) }.reduce(_+_)
    val TotalBits: Int =
        TageTableBits + TageTableBits/2 + BimEntries + BimEntries / (1 << BimRatio) +
        (if (useStatisticalCorrector) sct.length * sct(0)._1 * 2 * sct(0)._2 else 0)

    override def toString: String = TableInfo.zipWithIndex.map {case((r, h, t),i) => {f"TageTable[$i%d]: $r%3d rows, $h%3d bits history, $t%2d bits tag\n"}}.reduce(_+_) +
        f"bim: $BimEntries%d entries\n" +
        f"UBitPeriod: $UBitPeriod%d\n" +
        f"Totally consumed ${TotalBits/8192}%dKB"
}

abstract class TageComponents()(implicit params: TageParams) extends PredictorComponents {}

class SCTable(val numRows: Int, val ctrBits: Int, val histLen: Int)(implicit val p: TageParams) extends TageComponents()(p) {
    val superscalar = false
    val nRows = if (superscalar) { numRows / p.TageBanks } else numRows
    val nBanks = p.TageBanks
    println(s"numRows: $nRows")
    lazy val scTable = Array.fill[Array[SatCounter]](nRows)(Array.fill[SatCounter](2)(SatCounter(ctrBits, 0, signed=true)))
    lazy val scTables = Array.fill[Array[Array[SatCounter]]](p.TageBanks)(Array.fill[Array[SatCounter]](nRows)(Array.fill[SatCounter](2)(SatCounter(ctrBits, 0, signed=true))))
    val rowMask = getMask(log2Up(nRows))
    val bankMask = getMask(log2Up(nBanks))

    var debugIdx: Int = 0
    def getBank(pc: Long): Int = ((pc >>> 2) & bankMask).toInt
    def getIdx(pc: Long, hist: Int): Int = {
        val unhashed = 
            if (superscalar)
                (pc >>> (1 + log2Up(nBanks))).toInt
            else
                (pc >>> 2).toInt
        (unhashed ^ hist) & rowMask
    }
    def lookup(pc: Long, hist: Int): List[Int] = {
        val bank = getBank(pc)
        val idx = getIdx(pc, hist)
        val e = if (superscalar) scTables(bank)(idx) else scTable(idx)
        val res = e.map(_()).toList
        // println(f"idx $idx, res $res")
        debugIdx = idx
        res
    }
    def update(pc: Long, hist: Int, tageTaken: Boolean, predCorr: Boolean): Unit = {
        val bank = getBank(pc)
        val idx = getIdx(pc, hist)
        val subIdx = if (tageTaken) 1 else 0
        assert(debugIdx == idx)
        if (superscalar) {
            scTables(bank)(idx)(subIdx) = scTables(bank)(idx)(subIdx).update(predCorr)
        } else {
            scTable(idx)(subIdx) = scTable(idx)(subIdx).update(predCorr)
        }
    }
}

case class SCThreshold(val threshold: Int, val tc: SatCounter = SatCounter(6, 0, signed=true)) {
    def initialThres: Int = 5 // to be validated
    def apply() = this.threshold
    def maxThres: Int = 255
    def minThres: Int = 5
    def update(cause: Boolean): SCThreshold = {
        // println(f"Updating TC because of ${if (cause) "mis_reverted" else "below threshold"}")
        val newTC = tc.update(cause)
        if (newTC.isSaturatedPos && threshold < maxThres) {
            println(f"threshold incremented $threshold -> ${threshold+2}")
            this.copy(tc=this.tc.copy(ctr=0), threshold=this.threshold+2)
        }
        else if (newTC.isSaturatedNeg && threshold > minThres) {
            println(f"threshold incremented $threshold -> ${threshold-2}")
            this.copy(tc=this.tc.copy(ctr=0), threshold=this.threshold-2)
        } 
        else this.copy(tc=newTC)
    }
}

class TageTable (val numRows: Int, val histLen: Int, val tagLen: Int, val uBitPeriod: Int, val i: Int)(implicit val p: TageParams) extends TageComponents()(p) {
    val useGem5     = p.useGem5
    val SuperScalar = p.SuperScalar
    val TageBanks   = p.TageBanks
    val TageCtrBits = p.TageCtrBits
    val nRows = if (SuperScalar) numRows / TageBanks else numRows
    
    
    val tagMask = getMask(tagLen)
    val ctrMask = getMask(TageCtrBits)
    val rowMask = getMask(log2Up(nRows))
    val bankMask = getMask(log2Up(p.TageBanks))

    val lastBanks = Array.fill(2)(0)

    class Entry () {
        var valid: Boolean = false
        var tag: Int = 0
        var ctr: Int = 0
        var u: Int = 0
        def this(tag: Int, ctr: Int, u: Int) = {
            this()
            this.valid = true
            this.tag = tag & tagMask
            this.ctr = ctr & ctrMask
            this.u = u
        }
        def decrementU = this.u = satUpdate(false, this.u, 2)
    }

    lazy val tables = Array.fill[Array[Entry]](TageBanks)(Array.fill[Entry](nRows)(new Entry))
    lazy val table  = Array.fill[Entry](nRows)(new Entry)
    println(f"size of table(${i}%d): ${table.size}%d")

    private def ctrUpdate(oldCtr: Int, taken: Boolean): Int = satUpdate(taken, oldCtr, TageCtrBits)

    private def getBank(pc: Long): Int = ((pc >>> 1) & bankMask).toInt
    private def getUnhashedIdx(pc: Long): Long = pc >>> (1 + (if (SuperScalar) log2(p.TageBanks) else 0))

    private def F(phist: Int, size: Int): Int = {
        var a1: Int = 0
        var a2: Int = 0

        val masked = phist & getMask(size)
        a1 = masked & rowMask
        a2 = masked >>> log2Up(nRows)
        a2 = (a2 << i) & rowMask + (a2 >> (log2Up(nRows) - i))
        val a3 = a1 ^ a2
        val res = ((a3 << i) & rowMask) + (a3 >> (log2Up(nRows) - i))
        res
    }

    private def getIdx(pc: Long, idxHist: Int, phist: Int): Int = 
        if (useGem5)
            (((pc >>> 1) ^ ((pc >>> 1) >>> (abs(log2Up(nRows)-i)+2)) ^ idxHist) & rowMask).toInt
        else
            // (((pc >>> 1) ^ ((pc >>> 1) >>> (abs(log2Up(nRows)-i)+2)) ^ (idxHist << 2)) & rowMask).toInt
            (((getUnhashedIdx(pc) >>> 2) ^ (idxHist << 2)/*  ^ phist */) & rowMask).toInt
    
    private def getTag(pc: Long, tagHist: List[Int]): Int = {
        assert(tagHist.length == 2)
        if (useGem5)
            (((pc >>> 1) ^ tagHist(0) ^ (tagHist(1) << 1)) & tagMask).toInt
        else
            ((getUnhashedIdx(pc) ^ tagHist(0) ^ (tagHist(1) << 1)) & tagMask).toInt
    }

    private def getBIT(pc: Long, idxHist: Int,
        tagHist: List[Int], phist: Int): (Int, Int, Int) = (getBank(pc), getIdx(pc, idxHist, phist), getTag(pc, tagHist))

    def flush = if (SuperScalar) tables.foreach(b => b.foreach(e => e.valid = false))
                else             table.foreach(e => e.valid = false)

    def lookUp(pc: Long, idxHist: Int, tagHist: List[Int], phist: Int): TableResp = {
        val (bank, idx, tag) = getBIT(pc, idxHist, tagHist, phist)
        var bankTemp = ((pc >> 1) & 3).toInt
        // while (bankTemp == lastBanks(0) || bankTemp == lastBanks(1)) {
        //     // println(f"bankTemp $bankTemp conflict")
        //     bankTemp = (bankTemp + 1) & 3
        // }
        val newIdx = ((idx & 0xfffffc) | bankTemp) & rowMask
        val e = if (SuperScalar) tables(bank)(newIdx) else table(newIdx)
        // println(f"in lookup table_$i ", lastBanks(1), lastBanks(0), idx & 3, bankTemp)
        lastBanks(1) = lastBanks(0)
        lastBanks(0) = bankTemp
        // println(f"after lookup table$i ", lastBanks(1), lastBanks(0), idx & 3, bankTemp)
        TableResp(e.ctr, e.u, tag == e.tag && e.valid, bankTemp)
    }

    
    def update(pc: Long, valid: Boolean, taken: Boolean,
        alloc: Boolean, oldCtr: Int, uValid: Boolean, u: Int,
        fhist: List[Int], phist: Int, b: Option[Int]) = {

        val idxHist = fhist(0)
        val tagHist = List(fhist(1), fhist(2))
        val (bank, idx, tag) = getBIT(pc, idxHist, tagHist, phist)
        val previousBank = ((pc >> 1) & 3).toInt
        var realBank = previousBank
        b.map(realBank = _)
        val newIdx = ((idx & 0xfffffc) | realBank) & rowMask
        // println(f"in update table_$i ", previousBank, realBank, if (previousBank != realBank) "conflicted" else "")
        if (valid) {
            val newCtr = if (alloc) {if (taken) 1 << (TageCtrBits-1) else (1 << (TageCtrBits-1)) - 1} else ctrUpdate(oldCtr, taken)
            val targetEntry = if (SuperScalar) tables(bank)(newIdx) else table(newIdx)
            targetEntry.valid = true
            targetEntry.tag   = tag
            targetEntry.ctr   = newCtr
            // println(f"${if (alloc) "Allocating" else "Updating"}%s entry $idx of table $i, tag is $tag%x, ctr is $newCtr")
        }

        if (uValid) {
            if (SuperScalar) tables(bank)(newIdx).u = u
            else             table(newIdx).u = u
            // printf(f"updating u of bank $bank%d, idx $idx%d to $u%d\n")
        }
    }

    def pvdrUpdate(pc: Long, taken: Boolean, oldCtr: Int, u: Int, fhist: List[Int], phist: Int, bank: Int) = {
        update(pc, true, taken, false, oldCtr, true, u, fhist, phist, Some(bank))
    }

    def allocUpdate(pc: Long, taken: Boolean, fhist: List[Int], phist: Int) = {
        update(pc, true, taken, true, 0, true, 0, fhist, phist, None)
    }

    def decrementU(pc: Long, idxHist: Int, phist: Int) = {
        val bank = getBank(pc)
        val idx = getIdx(pc, idxHist, phist)
        if (SuperScalar) tables(bank)(i).decrementU
        else             table(i).decrementU
    }

    def decayU() = {
        if (SuperScalar) tables.foreach(b => b.foreach(e => e.decrementU))
        else             table.foreach(e => e.decrementU)
    }
}

class Bim (val nEntries: Int, val ratio: Int)(implicit val p: TageParams) extends TageComponents()(p) {
    val predTable = Array.fill[Boolean](nEntries)(false)
    val hystTable = Array.fill[Boolean](nEntries >> ratio)(true)
    val ctrBits = 2
    val idxMask = getMask(log2Up(nEntries))
    def flush = {
        (0 until nEntries).foreach(predTable.update(_, true))
        (0 until nEntries >> ratio).foreach(hystTable.update(_, false))
    }
    def getIdx(pc: Long): (Int, Int) = {
        val pind = ((pc >>> 1) & idxMask).toInt
        (pind, pind >>> ratio)
    }
    def toInt(b: Boolean): Int = if (b) 1 else 0
    def toBool(i: Int): Boolean = if (i > 0) true else false
    def getCtr(ind: (Int, Int)): Int = (toInt(predTable(ind._1)) << 1) + toInt(hystTable(ind._2))
    def ctrUpdate(old: Int, taken: Boolean): Int = satUpdate(taken, old, ctrBits)
    def lookUp(pc: Long): Boolean = predTable(getIdx(pc)._1)
    def update(pc: Long, taken: Boolean): Unit = {
        val ind    = getIdx(pc)
        val oldCtr = getCtr(ind)
        val newCtr = ctrUpdate(oldCtr, taken)
        predTable.update(ind._1, toBool(newCtr & 0x2))
        hystTable.update(ind._2, toBool(newCtr & 0x1))
        // printf(f"bim updating idx $idx%d to $newCtr%d\n")
    }
}

case class TableResp (val ctr: Int, val u: Int, val hit: Boolean, val bank: Int) {}
case class TageHistories(val foldedHists: List[List[Int]], val pHist: Int) {}



class Tage(params: TageParams = TageParams()) extends BasePredictor {

    val instantUpdate = true
    // override val debug = true
    

    implicit val p: TageParams = params

    val TageNTables  = params.TageNTables
    val TageCtrBits  = params.TageCtrBits
    val UBitPeriod   = params.UBitPeriod
    val maxHist      = params.maxHist
    val TableInfo    = params.TableInfo
    val BimEntries   = params.BimEntries
    val BimRatio     = params.BimRatio
    val SuperScalar  = params.SuperScalar
    val TageBanks    = params.TageBanks
    val UseSC        = params.useStatisticalCorrector
    val SCConfigs    = params.sct
    val SCThresInit  = params.scThresInit

    val scNumTables = SCConfigs.length
    // Use the same history length as TAGE tables
    val scHistLens = List(0, 4, 10, 16)
    // val scHistLens = List(0, 2, 4, 8, 16, 32)
    val scTableInfos = SCConfigs zip scHistLens map { case ((nRows, cBits), h) => (nRows, cBits, h) }
    val scThresholds = Array.fill(TageBanks)(SCThreshold(SCThresInit))

    var brCount = 0


    val bim = new Bim(BimEntries, BimRatio)

    val tables = TableInfo.zipWithIndex.map { case((nRows, histLen, tagLen), i) => new TageTable(nRows, histLen, tagLen, UBitPeriod, i) }
    val scTables = scTableInfos.map { case (nRows, cBits, h) => new SCTable(nRows, cBits, h)}
    val ghist = new GlobalHistory(maxHist)

    val tageIdxHists = TableInfo.map { case (nRows, h, tL) => new FoldedHist(h, (if (SuperScalar) log2(nRows/TageBanks) else log2(nRows))-2)}
    val tageTagHistsTemp = TableInfo.map { case (nRows, h, tL) => (new FoldedHist(h, tL), new FoldedHist(h, tL-1))}.unzip

    val tageTagHists = List(tageTagHistsTemp._1.toList, tageTagHistsTemp._2.toList)

    val phist = new PathHistory(30, 2)
    lazy val scHists = scTableInfos.map { case (nRows, _, h) => new FoldedHist(h, log2Up(nRows))}.toList


    // ------------------------------------ perf counters ------------------------------------//
    val perTableNumHits = Array.fill(tables.length)(0)
    val perTableHitCorrects = Array.fill(tables.length)(0)
    val perTableHitMispreds = Array.fill(tables.length)(0)
    val perTableAltCorrects = Array.fill(tables.length)(0)
    val perTableAltMispreds = Array.fill(tables.length)(0)
    val perTableCorrectedBySC = Array.fill(tables.length)(0)
    val perTableMisledBySC = Array.fill(tables.length)(0)
    var scCorrectTage = 0
    var scMisleadTage = 0
    var useBim = 0
    var bimCorrect = 0
    var bimWrong = 0


    case class TageMeta(
        val hist: TageHistories,
        val pvdr: Int,
        val pvdrValid: Boolean,
        val altDiff: Boolean,
        val pvdrU: Int,
        val pvdrCtr: Int,
        val pvdrBank: Int,
        val altPvdr: Int,
        val altPvdrValid: Boolean,
        val altPvdrCtr: Int,
        val altPvdrBank: Int,
        val allocMask: List[Boolean],
        tagePred: Boolean)
    {
        override def toString: String = {
            f"pvdr($pvdrValid%5b): $pvdr%d, altDiff: $altDiff%5b, pvdrU: $pvdrU%d, pvdrCtr: $pvdrCtr%d, allocMask: $allocMask"
        }
    }
    
    case class SCMeta(val hist: List[Int], val tagePred: Boolean, val scUsed: Boolean,
        val scPred: Boolean, val sum: Int) {}

    case class TagePredictionMeta(val pc: Long, val histPtr: Int, val tageMeta: TageMeta, val scMeta: SCMeta,
        val pred: Boolean, val isBr: Boolean) extends PredictionMeta {}

    val obq = new mutable.Queue[TagePredictionMeta]

    def predict(pc: Long) = true

    def predict(pc: Long, mask: Int): Boolean = true

    def predict(pc: Long, isBr: Boolean): Boolean = {

        def tagePredict(tageResp: List[TableResp], bimResp: Boolean): (Boolean, Int, Int, Boolean, Boolean, Int, Int) = {
            // @scala.annotation.tailrec
            // def tageCalRes(tResp: List[TableResp], ti: Int, provided: Boolean, provider: Int,
            //     altPred: Boolean, finalAltPred: Boolean, res: Boolean): (Boolean, Int, Boolean, Boolean, Boolean) = {
            //     val TableResp(ctr, u, hit) = tResp(0)
            //     tResp match {
            //         case Nil => {println("Should not reach here"); (false, 0, false, false, false)}
            //         case resp :: Nil => {
            //             if (resp.hit) (true, ti, ctr >= 4, altPred, if ((ctr == 3 || ctr == 4) && u == 0) altPred else ctr >= 4)
            //             else (provided, provider, altPred, finalAltPred, res)
            //         }
            //         case resp :: tail => {
            //             if (resp.hit) tageCalRes(tail, ti+1, true, ti, ctr >= 4, altPred, (if ((ctr == 3 || ctr == 4) && u == 0) altPred else (ctr >= 4)))
            //             else tageCalRes(tail, ti+1, provided, provider, altPred, finalAltPred, res)
            //         }
            //     }
            // }
            // tageCalRes(tageResp.toList, 0, false, 0, bimResp, bimResp, bimResp)

            val respArr = tageResp.toArray
            val numTables = tageResp.length
            var provided = false
            var provider = 0
            var providerCtr = -1

            var providerRes = bimResp

            var altProvider = 0

            var altPred = bimResp
            var finalAltPred = bimResp

            var break = false
            for (i <- numTables-1 to 0 by -1 if !break) {
                val resp = respArr(i)
                if (resp.hit) {
                    provided = true
                    provider = i
                    providerCtr = resp.ctr
                    providerRes = resp.ctr >= (1 << (TageCtrBits-1))
                    break = true
                }
            }
            break = false
            if (provided && provider > 0) {
                for (i <- provider-1 to 0 by -1 if !break) {
                    val resp = respArr(i)
                    if (resp.hit) {
                        altPred = resp.ctr >= (1 << (TageCtrBits-1))
                        finalAltPred = resp.ctr >= (1 << (TageCtrBits-1))
                        altProvider = i
                        break = true
                    }
                }
            }
            if (providerCtr == (1 << (TageCtrBits-1)) - 1 || providerCtr ==  (1 << (TageCtrBits-1))) {
                (provided, provider, altProvider, finalAltPred, finalAltPred, respArr(provider).bank, respArr(altProvider).bank)
            } else {
                (provided, provider, altProvider, finalAltPred, providerRes, respArr(provider).bank, respArr(altProvider).bank)
            }

        }

        def scPredict(pc: Long, tageRes: Boolean, tageProvided: Boolean, tageProvider: Int, tageProviderCtr: Int): (Boolean, SCMeta) = {
            if (UseSC && tageProvided) {
                val scHist = (scHists map {(i: FoldedHist) => i match {case t=> t.apply()}}).toList
                val scResps = (scTables zip scHist) map { case (t, h) => t.lookup(pc, h) }
                val scs = scResps map { case List(rnt, rt) => if (tageRes) rt else rnt }
                val scCentered = scs map (r => 2 * r + 1)
                val scSum = scCentered reduce (_+_)
                val tagePredCenteredVal = 2 * (tageProviderCtr - (1 << (TageCtrBits-1))) + 1
                val totalSum = scSum + 8 * tagePredCenteredVal
                val bank = ((pc >> 1) & 0xf).toInt
                val thres = scThresholds(bank)()
                val sumBelowThreshold = abs(totalSum) <= thres
                // val sumBelowUpdateThreshold = abs(totalSum) < (21 + 8 * scThreshold())
                val scPred = if (!sumBelowThreshold) totalSum >= 0 else tageRes
                Debug(UseSC, f"[SCPred] pc: $pc%x scCtred: $scCentered, tageCtred: $tagePredCenteredVal, sum: $totalSum, thres: ${thres}, reverted: ${scPred != tageRes}, res: $scPred")
                (scPred, SCMeta(scHist, tageRes, !sumBelowThreshold, scPred, totalSum))
            }
            else {
                (tageRes, SCMeta(List(0), tageRes, false, tageRes, 0))
            }
        }

        // returns (allocEntry, alloced)
        def tageAlloc(tageResp: List[TableResp], provider: Int, provided: Boolean): List[Boolean] = {
            val allocatableArray = tageResp.zipWithIndex.map{ case(r, i) => !r.hit && r.u == 0 && ((i > provider && provided) || !provided) }.toArray
            val allocatable = boolArrayToInt(allocatableArray)
            val allocMask   = scala.util.Random.nextInt((1 << TageNTables))
            toBoolArray(allocatable & allocMask, TageNTables).toList
            // val maskedEntry = PriorityEncoder(allocatable & allocMask, TageNTables)
            // val firstEntry  = PriorityEncoder(allocatable, TageNTables)
            // val allocEntry  = if (allocatableArray(maskedEntry)) maskedEntry else firstEntry
            // (allocEntry, allocatable != 0)
        }

        val nowPtr = ghist.getHistPtr
         
        if (isBr) {
            // println("----")
            val tageTableResps = tables.map {
                case t => {
                    val i = t.i
                    val ph = phist()
                    t.lookUp(pc, tageIdxHists(i)(), List(tageTagHists(0)(i)(), tageTagHists(1)(i)()), ph)
                }
            }
            val bimResp: Boolean = bim.lookUp(pc)

            val (provided, provider, altProvider, finalAltPred, tageRes, providerBank, altProviderBank) = tagePredict(tageTableResps.toList, bimResp)
            val providerU = tageTableResps(provider).u
            val providerCtr = tageTableResps(provider).ctr
            val altProviderCtr = tageTableResps(altProvider).ctr
            val altProviderValid = tageTableResps(altProvider).hit
            val altDiffers = tageRes != finalAltPred
            // val (allocEntry, allocated) = tageAlloc(tageTableResps.toList, provider, provided)
            // val (altAllocEntry, altAllocated) = tageAlloc(tageTableResps.toList, provider, provided)
            val allocMask = tageAlloc(tageTableResps.toList, provider, provided)
            val tageFolded = (tageIdxHists map (_()),
                              tageTagHists(0) map (_()),
                              tageTagHists(1) map (_())).zipped.toList.map{case (a, b, c) => List(a, b, c)}.toList
            val tageHist = TageHistories(tageFolded, phist())
            val tageMeta = TageMeta(tageHist, provider, provided, altDiffers,
                                providerU, providerCtr, providerBank, altProvider, altProviderValid,
                                altProviderCtr, altProviderBank, allocMask, tageRes)

            val (scRes, scMeta) = scPredict(pc, tageRes, provided, provider, tageTableResps(provider).ctr)
            val res = scRes

            val meta = new TagePredictionMeta(pc, nowPtr, tageMeta, scMeta, res, isBr)
            obq.enqueue(meta)


            if (!UseSC) assert(tageRes == res) // Ensure tage prediction is not altered when SC is off

            // // Debug(f"pc:0x$pc%x predicted to be ${if (res) "taken" else "not taken"}%s")
            res 
        }
        else {
            if (updateOnUncond) {
                obq.enqueue(new TagePredictionMeta(pc, nowPtr,
                      TageMeta(TageHistories(List(List(0)), 0), 0, false, false, 0, 0, 0, 0, false, 0, 0, List.fill(tables.length)(false), true),
                      SCMeta(List(0), true, false, false, 0),
                      true, false))
            }
            true
        }
    }

    def updateFoldedHistories(taken: Boolean, histPtr: Int) = {
        def updateWithOldBit(x: List[Tuple3[FoldedHist, Boolean, Int]]) = 
            x.foreach {
                case (h, o, p) => {
                    val oldTemp = h()
                    h.update(taken, o)
                    // Debug(f"oldBitsPos $p, from $oldTemp to ${h()}")
                } 
            }
        // Debug(f"updating with histptr $histPtr")
        val tageOldBitPos = tables.map(t => histPtr - t.histLen)
        val tageOldBits = tageOldBitPos.map(ghist(_))
        Seq(tageIdxHists, tageTagHists(0), tageTagHists(1)) foreach {h => updateWithOldBit((h, tageOldBits, tageOldBitPos).zipped.toList)}
        if (UseSC) {
            val scOldBitPos = scHistLens.map(histPtr-_)
            val scOldBits   = scOldBitPos.map(ghist(_))
            updateWithOldBit((scHists, scOldBits, scOldBitPos).zipped.toList)
        }
    }

    def updateUncond(pc: Long) = {
        if (updateOnUncond) {
            val meta = obq.dequeue()
            if (pc != meta.pc) Debug("update pc does not correspond with expected pc\n")
            ghist.updateHist(true)
            updateFoldedHistories(true, meta.histPtr)
            phist.update(pc)
        }
    }

    def update(pc: Long, taken: Boolean) = {
        def tageUpdate(meta: TagePredictionMeta, misPred: Boolean) = {
            val tageMeta = meta.tageMeta
            val tageHists = tageMeta.hist
            if (tageMeta.pvdrValid) {
                tables(tageMeta.pvdr).pvdrUpdate(pc, taken, tageMeta.pvdrCtr, 
                    if(tageMeta.altDiff) satUpdate(!misPred, tageMeta.pvdrU, 2) else tageMeta.pvdrU,
                    tageHists.foldedHists(tageMeta.pvdr), tageHists.pHist, tageMeta.pvdrBank)
                if (misPred && tageMeta.altPvdrValid && (tageMeta.pvdrCtr == (1 << (TageCtrBits-1)) - 1 || tageMeta.pvdrCtr == (1 << (TageCtrBits-1)))) {
                    tables(tageMeta.altPvdr).update(pc, true, taken, false, tageMeta.altPvdrCtr, false, 0,
                        tageHists.foldedHists(tageMeta.pvdr), tageHists.pHist, Some(tageMeta.altPvdrBank))
                }

                perTableNumHits(tageMeta.pvdr) += 1
                val scReverted = meta.scMeta.scUsed && (meta.tageMeta.tagePred != meta.pred)
                if (!scReverted) {
                    if (misPred) {
                        perTableHitMispreds(tageMeta.pvdr) += 1
                    } else {
                        perTableHitCorrects(tageMeta.pvdr) += 1
                    }
                } else {
                    val tageCorrect = meta.tageMeta.tagePred == taken
                    if (tageCorrect) {
                        perTableMisledBySC(tageMeta.pvdr) += 1
                    } else {
                        perTableCorrectedBySC(tageMeta.pvdr) += 1
                    }
                }
            } else {
                useBim += 1
                if (misPred) {
                    bimWrong += 1
                } else {
                    bimCorrect += 1
                }
            }
            val pvdrUnconfButCorrect =
                tageMeta.pvdrCtr == (1 << (TageCtrBits-1)) - 1 && !taken ||
                tageMeta.pvdrCtr == (1 << (TageCtrBits-1)) &&  taken
            if (misPred && !pvdrUnconfButCorrect) {
                val idxHists = tageHists.foldedHists.map(h => h(0)).toList
                // Debug(f"idxHist list length ${idxHists.length}")
                val pHist = tageHists.pHist
                val allocValid = tageMeta.allocMask.reduce(_||_)
                if (allocValid) {
                    val allocIndices = tageMeta.allocMask.zipWithIndex.filter(_._1).map(_._2)
                    // println(allocIndices)
                    val allocatable = allocIndices.length
                    allocIndices.take(2).map(i => tables(i).allocUpdate(pc, taken, tageHists.foldedHists(i), tageHists.pHist))
                }
                else {
                    (0 until TageNTables).foreach(i => if (i > tageMeta.pvdr) tables(i).decrementU(pc, idxHists(i), pHist))
                }
            }
        }

        def scUpdate(scMeta: SCMeta, taken: Boolean) = {
            val scHist = scMeta.hist
            val scReverted = (scMeta.tagePred != scMeta.scPred) && scMeta.scUsed
            val mispred = scMeta.scPred != taken
            Debug(UseSC, f"[scUpdate]: scReverted($scReverted%5s), mispred($mispred%5s) pc($pc%x) taken($taken)")
            if (scMeta.scUsed) {
                // println("scUsed")
                val sumAbs = abs(scMeta.sum)
                val bank = ((pc >> 1) & 0xf).toInt
                val thres = scThresholds(bank)
                val thresVal = thres()
                val sumBelowThreshold = sumAbs <= thresVal
                if (!sumBelowThreshold && scReverted) {
                    if (mispred) {
                        scMisleadTage += 1
                    } else {
                        scCorrectTage += 1
                    }
                }
                val scPred = scMeta.scPred
                val tagePred = scMeta.tagePred
                if (scPred != tagePred) {
                    // println(f"scPred != taken, sum $sumAbs use $thres ")
                    
                    if (sumAbs <= thresVal - 2 && sumAbs >= thresVal - 4) {
                        scThresholds.update(bank, thres.update(scPred != taken)) 
                    }
                }
                // if (scPred == taken && sumAbs <= thres) {
                //     scThreshold = scThreshold.update(false)
                // }
                if (scPred != taken || sumAbs <= thresVal * 8 + 21) {
                    (scTables zip scHist) foreach { case (t, h) => t.update(pc, h, tagePred, taken) }
                }
            }
        }

        val meta = obq.head
        val pred = meta.pred
        val misPred = taken != pred
        val tageMisPred = taken != meta.tageMeta.tagePred

        if (pc != meta.pc) {
            println("update pc does not correspond with expected pc\n")
        } else {
            obq.dequeue()
            tageUpdate(meta, misPred)
            if (UseSC) { scUpdate(meta.scMeta, taken) }
            ghist.updateHist(taken)
            bim.update(pc, taken)
            updateFoldedHistories(taken, meta.histPtr)
            phist.update(pc)
            brCount += 1
            if (brCount % UBitPeriod == 0) { tables.foreach(t => t.decayU()) }
            // Debug("[update meta] " + meta.tageMeta + f" | ${if (taken) " T" else "NT"}%s pred to ${if (pred) " T" else "NT"}%s -> ${if(misPred) "miss" else "corr"}%s")
            // Debug(f"[update hist] ${ghist.getHistStr(ptr=meta.histPtr)}%s")
        } //
        misPred
    }

    def flush() = {
        bim.flush
        tables.foreach(_.flush)
    }

    def onFinish() = {
        println(s"sc correct tage: $scCorrectTage, sc wrongly revert tage: $scMisleadTage")
        println(f"bim used $useBim, correct $bimCorrect, wrong $bimWrong")
        for (i <- 0 until tables.length) {
            val tableHit = perTableNumHits(i)
            val hitCorrect = perTableHitCorrects(i)
            val hitMispred = perTableHitMispreds(i)
            val hitCorrectedBySC = perTableCorrectedBySC(i)
            val hitMisledBySC = perTableMisledBySC(i)
            val misrate = hitMispred.toDouble / tableHit.toDouble * 100
            println(f"tage table $i hit $tableHit%8s correct $hitCorrect%8s wrong $hitMispred%8s," +
              f"corrected by sc $hitCorrectedBySC%8s, misled by sc $hitMisledBySC%8s misrate: $misrate")
        }
    }
    def name: String = "BOOM_TAGE"
    override def toString: String = f"${this.name}%s with params:\n${params}%s\nUsing global history ${if(updateOnUncond) "with" else "without"}%s jumps\n"
}

object Tage {
    // This is a factory method to produce Tage instances according to passed option
    def apply(ops: Map[Symbol, Any]): Tage = new Tage(wrapParams(ops, TageParams()))

    @scala.annotation.tailrec
    def wrapParams(ops: Map[Symbol, Any], p: TageParams = TageParams()): TageParams = 
        ops match {
            case o if (o.isEmpty) => p
            case o if (o.contains('hislen)) => {
                println(f"max history length set to ${ops('hislen).asInstanceOf[Int]}%d")
                wrapParams(ops - 'hislen, p.copy(maxHist=ops('hislen).asInstanceOf[Int]))
            }
            case o if (o.contains('superscalar)) => {
                println(f"tables set to superscalar")
                wrapParams(ops - 'superscalar, p.copy(SuperScalar=true))
            }
            case o if (o.contains('updateOnUncond)) => {
                println(f"updating history on unconditional jumps")
                wrapParams(ops - 'updateOnUncond, p.copy()) // TODO: implement this case
            }
            case o if (o.contains('useGem5)) => {
                println(f"Using gem5 indexing")
                wrapParams(ops - 'useGem5, p.copy(useGem5=true))
            }
            case o if (o.contains('useXS)) => {
                println(f"Using XS params")
                val previous = Seq(( 1024,   2,  7),
                                   ( 1024,   4,  7),
                                   ( 2048,   8,  8),
                                   ( 2048,   16, 8),
                                   ( 1024,   32, 9),
                                   ( 1024,   65, 9)/* ,
                                   ( 1024,  10) */)
                val xst: Seq[Tuple3[Int, Int, Int]]  = Seq(( 2048,   4,     9),
                                                           ( 2048,   16,    9),
                                                           ( 2048,   64,    9),
                                                           ( 2048,   256,   9)/* ,
                                                           ( 1024,   64,   9),
                                                           ( 1024,   90,   9),
                                                           ( 1024,   160,  9),
                                                           ( 1024,   260,  9) */)
                // val xst = previous
                if (o.contains('hl)) {
                    val hArray = ops('hl).asInstanceOf[Array[Int]]
                    require(hArray.length == xst.length)
                    val xst_hl_substituted = (xst zip hArray) map {case ((nRows, h, t), newH) => (nRows, newH, t)}
                    wrapParams(ops - 'useXS - 'hl, p.copy(useGem5=false, t=xst_hl_substituted, SuperScalar=false, minHist=2, maxHist=640))
                } else {
                    wrapParams(ops - 'useXS, p.copy(useGem5=false, t=xst, SuperScalar=false, minHist=2, maxHist=640))
                }
            }
            case o if (o.contains('useStatisticalCorrector)) => {
                println(f"Using statistical corrector")
                wrapParams(ops - 'useStatisticalCorrector, p.copy(useStatisticalCorrector=true))
            }
            case o if (o.contains('tageCtrBits)) => {
                println(f"tageCtrBits is ${ops('tageCtrBits)}")
                wrapParams(o - 'tageCtrBits, p.copy(TageCtrBits = o('tageCtrBits).asInstanceOf[Int]))
            }
            case _ =>
                wrapParams(Map(), p)
        }
}

// object TageTest extends PredictorUtils{
//     def main(args: Array[String]): Unit = {
//         val bpd = new Tage
//         var hist: Long = 0
//         for (i <- 0 until 1000) {
//             // val pred = bpd.predict(0x80000000L)
//             val taken = i % 2 == 0
//             bpd.ghist.updateHist(taken)
//             hist = (hist << 1) | (if (taken) 1 else 0)
//             val tageHist = boolArrayToLong(bpd.ghist.getHist(len=64))
//             var wrong = false
//             if (tageHist != hist) {
//                 println(f"at br$i%d, ref_hist:$hist%x, tageHist:$tageHist%x, ptr:${bpd.ghist.getHistPtr}")
//                 wrong = true
//             }
//             if (wrong) println("Wrong!")
//         }
//     }
// }
