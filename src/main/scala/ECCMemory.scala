import chisel3._
import chisel3.util._
import chiselsby._


class ECCMemory(size: Int) extends Module with Formal {
  val nw       = log2Ceil(size)
  val capacity = math.pow(2, nw.toDouble).toInt
  val io       = IO(new Bundle {
    val wrEna  = Input(Bool())
    val wrAddr = Input(UInt(nw.W))
    val wrData = Input(UInt(8.W))
    val rdAddr = Input(UInt(nw.W))
    val rdData = Output(UInt(8.W))
    val rdOK   = Output(Bool())
  })

  val mem = Mem(capacity, UInt(8.W))


  // Seq used for registers reset
  val colParitySeq = WireInit(VecInit(Seq.fill(6)(false.B)))

  var m  = 2
  var id = 0
  while (m != 16) {
    val wireTmp0   = WireInit(VecInit(Seq.fill(capacity * 4)(false.B)))
    val wireTmp1   = WireInit(VecInit(Seq.fill(capacity * 4)(false.B)))
    var cnt0, cnt1 = 0
    val mid        = m / 2
    for (j <- 0 until 8) {
      if (j % m < mid) {
        for (i <- 0 until capacity) {
          wireTmp0(cnt0) := mem(i)(j)
          cnt0 += 1
        }
      } else {
        for (i <- 0 until capacity) {
          wireTmp1(cnt1) := mem(i)(j)
          cnt1 += 1
        }
      }
    }
    colParitySeq(id * 2) := wireTmp0.reduce(_ ^ _)
    colParitySeq(id * 2 + 1) := wireTmp1.reduce(_ ^ _)
    id += 1
    m *= 2
  }


  val rowParitySeq = WireInit(VecInit(Seq.fill(2 * nw)(false.B)))

  m = 2
  id = 0
  while (m != capacity * 2) {
    val wireTmp0   = WireInit(VecInit(Seq.fill(capacity / 2)(false.B)))
    val wireTmp1   = WireInit(VecInit(Seq.fill(capacity / 2)(false.B)))
    var cnt0, cnt1 = 0
    val mid        = m / 2
    for (i <- 0 until capacity) {
      if (i % m < mid) {
        wireTmp0(cnt0) := mem(i).xorR
        cnt0 += 1
      } else {
        wireTmp1(cnt1) := mem(i).xorR
        cnt1 += 1
      }
    }
    rowParitySeq(id * 2) := wireTmp0.reduce(_ ^ _)
    rowParitySeq(id * 2 + 1) := wireTmp1.reduce(_ ^ _)
    id += 1
    m *= 2
  }

  val colParity = RegInit(colParitySeq)
  val rowParity = RegInit(rowParitySeq)

  when(io.wrEna) {
    val oldV = mem(io.wrAddr)
    val newV = io.wrData
    var m    = 2
    var id   = 0
    while (m != 16) {
      val mid = m / 2
      for (j <- 0 until 8) {
        when(oldV(j) =/= newV(j)) {
          if (j % m < mid) {
            colParity(id * 2) := colParity(id * 2) ^ true.B
          } else {
            colParity(id * 2 + 1) := colParity(id * 2 + 1) ^ true.B
          }
        }
      }
      id += 1
      m *= 2
    }
    when(oldV.xorR =/= newV.xorR) {
      m = 2
      id = 0
      while (m != capacity * 2) {
        val mid = m / 2
        when(io.wrAddr % m.U < mid.U) {
          rowParity(id * 2) := rowParity(id * 2) ^ true.B
        }.otherwise {
          rowParity(id * 2 + 1) := rowParity(id * 2 + 1) ^ true.B
        }
        id += 1
        m *= 2
      }
    }

    mem(io.wrAddr) := io.wrData
  }
  io.rdData := mem(io.rdAddr)


  io.rdOK := true.B

  for (i <- 0 until 6) {
    when(colParitySeq(i) =/= colParity(i)) {
      io.rdOK := false.B
    }
  }
  for (i <- 0 until 2 * nw) {
    when(rowParitySeq(i) =/= rowParity(i)) {
      io.rdOK := false.B
    }
  }


  // Formal Verification
  val flag_value = WireInit(0.U(1.W))
  val addr       = anyconst(nw)
  val flag       = initialReg(1, 0)
  val data       = Reg(UInt(8.W))

  flag.io.in := flag_value
  when(io.wrAddr === addr & io.wrEna) {
    flag_value := 1.U
    data := io.wrData
  }
  when(io.rdAddr === addr && flag.io.out === 1.U) {
    assert(data === io.rdData)
  }
  assert(io.rdOK === true.B)
}


object ECCMemory extends App {
  //  Check.generateRTL(() => new ECCMemory(16))
  Check.kInduction(() => new ECCMemory(8))
}
