import chisel3._
import chisel3.util._
import chisel3.util.random.XOR
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
  var resetColParitySeq = Seq.fill(capacity)(false.B)
  for (i <- 0 until capacity) {
    val v  = mem(i)
    var m  = 2
    var id = 0
    while (m != 16) {
      val mid = m / 2
      for (j <- 0 until 8) {
        if (j % m < mid) {
          resetColParitySeq.updated(id * 2, resetColParitySeq(id * 2) ^ v(j))
        } else {
          resetColParitySeq.updated(id * 2 + 1, resetColParitySeq(id * 2 + 1) ^ v(j))

        }
      }
      id += 1
      m *= 2
    }
  }
  var resetRowParitySeq = Seq.fill(2 * nw)(false.B)
  for (i <- 0 until capacity) {
    val v = WireInit(false.B)
    v := mem(i).xorR
    var m  = 2
    var id = 0
    while (m != capacity * 2) {
      val mid = m / 2
      if (i % m < mid) {
        resetRowParitySeq.updated(id * 2, resetRowParitySeq(id * 2) ^ v)
      } else {
        resetRowParitySeq.updated(id * 2 + 1, resetRowParitySeq(id * 2 + 1) ^ v)
      }
      id += 1
      m *= 2
    }
  }

  val colParity = RegInit(VecInit(resetColParitySeq))
  val rowParity = RegInit(VecInit(resetRowParitySeq))

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
    when (oldV.xorR =/= newV.xorR) {
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
}


object ECCMemory extends App {
//  Check.generateRTL(() => new ECCMemory(16))
    Check.kInduction(() => new ECCMemory(8))
}
