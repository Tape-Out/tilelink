package Tilelink;

import RegIf::*;
import Bus::*;

// TileLink Uncached Lightweight（SiFive TileLink Specification 1.8.1 第 7 章）：请求只有 Get、PutFullData、
// PutPartialData，答复只有 AccessAck、AccessAckData，一笔一个字。A、D 两个通道各自 ready/valid（4.1）：
// valid 不许看同拍的 ready，所以 D 通道的答复出自寄存器，a_ready 也只看手上有没有没交出去的答复。
// a_size 在 TL-UL 里不超过总线字宽（7.2），64 位以内 2 位就够；d_sink 按 7.2.4、7.2.5 可以是任意值，给 1 位恒 0。

Bit#(3) opPutFull    = 0;
Bit#(3) opPutPartial = 1;
Bit#(3) opArith      = 2;
Bit#(3) opLogic      = 3;
Bit#(3) opGet        = 4;
Bit#(3) opAck        = 0;
Bit#(3) opAckData    = 1;

interface TlulSlavePins#(numeric type aw, numeric type dw, numeric type sw);
  (* always_ready, always_enabled, prefix = "" *)
  method Action a_in((* port = "a_valid" *)   Bool               av,
                     (* port = "a_opcode" *)  Bit#(3)            op,
                     (* port = "a_param" *)   Bit#(3)            param,
                     (* port = "a_size" *)    Bit#(2)            size,
                     (* port = "a_source" *)  Bit#(sw)           source,
                     (* port = "a_address" *) Bit#(aw)           address,
                     (* port = "a_mask" *)    Bit#(TDiv#(dw, 8)) mask,
                     (* port = "a_data" *)    Bit#(dw)           data,
                     (* port = "a_corrupt" *) Bool               corrupt);
  (* always_ready, result = "a_ready" *)   method Bool     a_ready;
  (* always_ready, result = "d_valid" *)   method Bool     d_valid;
  (* always_ready, result = "d_opcode" *)  method Bit#(3)  d_opcode;
  (* always_ready, result = "d_param" *)   method Bit#(2)  d_param;
  (* always_ready, result = "d_size" *)    method Bit#(2)  d_size;
  (* always_ready, result = "d_source" *)  method Bit#(sw) d_source;
  (* always_ready, result = "d_sink" *)    method Bit#(1)  d_sink;
  (* always_ready, result = "d_denied" *)  method Bool     d_denied;
  (* always_ready, result = "d_data" *)    method Bit#(dw) d_data;
  (* always_ready, result = "d_corrupt" *) method Bool     d_corrupt;
  (* always_ready, always_enabled, prefix = "" *)
  method Action d_in((* port = "d_ready" *) Bool dr);
endinterface

typedef struct {
  Bit#(3)            op;
  Bit#(2)            size;
  Bit#(sw)           source;
  Bit#(aw)           address;
  Bit#(TDiv#(dw, 8)) mask;
  Bit#(dw)           data;
  Bool               corrupt;
} TlA#(numeric type aw, numeric type dw, numeric type sw) deriving (Bits);

typedef struct {
  Bit#(3)  opcode;
  Bit#(2)  size;
  Bit#(sw) source;
  Bool     denied;
  Bit#(dw) data;
  Bool     corrupt;
} TlD#(numeric type dw, numeric type sw) deriving (Bits);

// 一笔请求落到中立契约上是什么：Get 读、两种 Put 写。TL-UL 没有的操作码不碰目标，直接拒；
// 带坏数据的写也拒，被拒的访问不许有副作用（4.4）
function Maybe#(RegReq#(aw, dw)) accessOf(TlA#(aw, dw, sw) a);
  if (a.op == opGet)
    return tagged Valid RegReq { addr: a.address, write: False, wdata: 0, wstrb: 0 };
  else if ((a.op == opPutFull || a.op == opPutPartial) && !a.corrupt)
    return tagged Valid RegReq { addr: a.address, write: True, wdata: a.data, wstrb: a.mask };
  else
    return tagged Invalid;
endfunction

// 答复的操作码跟着请求走：Get 与两种运算的答复带数据（表 12），其余不带
function Bit#(3) ackOf(Bit#(3) op) = (op == opGet || op == opArith || op == opLogic) ? opAckData : opAck;

// d_size、d_source 照抄请求（7.2.4、7.2.5）；拒掉带数据的答复时 d_corrupt 必须一起拉高（4.4、7.2.5）
function TlD#(dw, sw) answer(TlA#(aw, dw, sw) a, Bool denied, Bit#(dw) rdata);
  Bit#(3) op = ackOf(a.op);
  return TlD { opcode: op, size: a.size, source: a.source, denied: denied,
               data: op == opAckData ? rdata : 0, corrupt: denied && op == opAckData };
endfunction

// 零等待目标接 TL-UL
module mkTlulBind#(RegIf#(aw, dw) rf)(TlulSlavePins#(aw, dw, sw));
  Wire#(Maybe#(TlA#(aw, dw, sw))) aIn <- mkBypassWire;
  Wire#(Bool)                     dIn <- mkBypassWire;
  Reg#(Bool)                      dV  <- mkReg(False);
  Reg#(TlD#(dw, sw))              dR  <- mkReg(unpack(0));

  // 手上的答复没被取走之前不收下一笔
  Bool aRdy = !dV;

  rule step;
    Bool nV = dV && !dIn;
    TlD#(dw, sw) nD = dR;
    if (aIn matches tagged Valid .a &&& aRdy) begin
      Bool     denied = True;
      Bit#(dw) rdata  = 0;
      if (accessOf(a) matches tagged Valid .q) begin
        let x <- rf.access(q);
        denied = x.err;
        rdata  = x.rdata;
      end
      nV = True;
      nD = answer(a, denied, rdata);
    end
    dV <= nV;
    dR <= nD;
  endrule

  method Action a_in(Bool av, Bit#(3) op, Bit#(3) param, Bit#(2) size, Bit#(sw) source,
                     Bit#(aw) address, Bit#(TDiv#(dw, 8)) mask, Bit#(dw) data, Bool corrupt);
    aIn <= av ? tagged Valid TlA { op: op, size: size, source: source, address: address,
                                   mask: mask, data: data, corrupt: corrupt }
              : tagged Invalid;
  endmethod
  method Bool     a_ready   = aRdy;
  method Bool     d_valid   = dV;
  method Bit#(3)  d_opcode  = dR.opcode;
  method Bit#(2)  d_param   = 0;
  method Bit#(2)  d_size    = dR.size;
  method Bit#(sw) d_source  = dR.source;
  method Bit#(1)  d_sink    = 0;
  method Bool     d_denied  = dR.denied;
  method Bit#(dw) d_data    = dR.data;
  method Bool     d_corrupt = dR.corrupt;
  method Action d_in(Bool dr);
    dIn <= dr;
  endmethod
endmodule

// 会停顿的目标接 TL-UL：收下的一笔交给目标，等 rspValid 再出答复
module mkTlulBindT#(RegTarget#(aw, dw) t)(TlulSlavePins#(aw, dw, sw));
  Wire#(Maybe#(TlA#(aw, dw, sw))) aIn  <- mkBypassWire;
  Wire#(Bool)                     dIn  <- mkBypassWire;
  Reg#(Maybe#(TlA#(aw, dw, sw)))  held <- mkReg(tagged Invalid);
  Reg#(Bool)                      dV   <- mkReg(False);
  Reg#(TlD#(dw, sw))              dR   <- mkReg(unpack(0));

  Bool aRdy = !isValid(held) && !dV;

  // 发与收分两条规则，道理同 hwcore 的 mkPipe
  rule send;
    Maybe#(RegReq#(aw, dw)) q = tagged Invalid;
    if (held matches tagged Valid .a) q = accessOf(a);
    t.req(isValid(q), fromMaybe(unpack(0), q));
  endrule

  rule step;
    Bool nV = dV && !dIn;
    TlD#(dw, sw) nD = dR;
    Maybe#(TlA#(aw, dw, sw)) nh = held;
    if (held matches tagged Valid .a) begin
      if (t.rspValid) begin
        let x = t.rsp;
        nV = True;
        nD = answer(a, x.err, x.rdata);
        nh = tagged Invalid;
      end
    end else if (aIn matches tagged Valid .b &&& aRdy) begin
      if (isValid(accessOf(b))) nh = tagged Valid b;
      else begin
        nV = True;
        nD = answer(b, True, 0);
      end
    end
    held <= nh;
    dV <= nV;
    dR <= nD;
  endrule

  method Action a_in(Bool av, Bit#(3) op, Bit#(3) param, Bit#(2) size, Bit#(sw) source,
                     Bit#(aw) address, Bit#(TDiv#(dw, 8)) mask, Bit#(dw) data, Bool corrupt);
    aIn <= av ? tagged Valid TlA { op: op, size: size, source: source, address: address,
                                   mask: mask, data: data, corrupt: corrupt }
              : tagged Invalid;
  endmethod
  method Bool     a_ready   = aRdy;
  method Bool     d_valid   = dV;
  method Bit#(3)  d_opcode  = dR.opcode;
  method Bit#(2)  d_param   = 0;
  method Bit#(2)  d_size    = dR.size;
  method Bit#(sw) d_source  = dR.source;
  method Bit#(1)  d_sink    = 0;
  method Bool     d_denied  = dR.denied;
  method Bit#(dw) d_data    = dR.data;
  method Bool     d_corrupt = dR.corrupt;
  method Action d_in(Bool dr);
    dIn <= dr;
  endmethod
endmodule

// ---------------- 发起方一侧：收编 TL-UL 完成方、出芯片的引脚、总线类型类的实例 ----------------

// 收编 TL-UL 完成方，出来的是会停顿的目标。一次一笔、source 固定 0。A 通道出自寄存器（4.1：valid 不许看 ready）；
// d_ready 恒高：同拍组合出来的答复也要收，发起方拉低 d_ready 等 a_valid 撤掉会死锁（4.1 之后的说明）
module mkTlulAdopt#(TlulSlavePins#(aw, dw, sw) sl)(RegTarget#(aw, dw))
    provisos (Mul#(TDiv#(dw, 8), 8, dw));
  Reg#(UInt#(2))         st    <- mkReg(0);   // 0 空闲 · 1 A 通道在发 · 2 等 D
  Reg#(RegReq#(aw, dw))  held  <- mkReg(unpack(0));
  Reg#(Bool)             ansV  <- mkReg(False);
  Reg#(RegRsp#(dw))      ansX  <- mkReg(unpack(0));
  Wire#(Bool)            takeV <- mkDWire(False);
  Wire#(RegReq#(aw, dw)) takeR <- mkDWire(unpack(0));

  // 选通全 1 发 PutFullData，否则 PutPartialData；读一个整字：a_size 是字节数的对数，a_mask 全高（7.2）
  Bit#(3) op   = !held.write ? opGet : (held.wstrb == '1 ? opPutFull : opPutPartial);
  Bit#(2) size = fromInteger(log2(valueOf(TDiv#(dw, 8))));
  // 地址按字对齐：rocket-chip 的 TLMonitor 对 Get、两种 Put 都断言 address 与 size 对齐，而 APB4 的 PADDR
  // 可以落在字中间（上游写 0x1001 就会发出不合法的 TL-UL 请求）。一笔访问一个整字，低位清零不改语义
  Bit#(aw) lowBits = fromInteger(valueOf(TDiv#(dw, 8)) - 1);

  // 发与收分两条规则：完成方的答复可以与请求同拍组合出来（4.1），同一条规则里又写又读会成环，道理同 mkPipe
  rule send;
    sl.a_in(st == 1, op, 0, size, 0, held.addr & ~lowBits, held.write ? held.wstrb : '1,
            held.write ? held.wdata : 0, False);
    sl.d_in(True);
  endrule

  rule take;
    UInt#(2)        nst = st;
    Bool            nan = False;
    RegRsp#(dw)     nax = ansX;
    RegReq#(aw, dw) nhd = held;
    Bool aHs = st == 1 && sl.a_ready;
    if (st == 0) begin
      if (takeV) begin nhd = takeR; nst = 1; end
    end else if ((aHs || st == 2) && sl.d_valid) begin
      // 答复的操作码要对得上请求；被拒、或者带数据的答复标了坏数据，都记错（4.4、7.2.5）
      Bit#(3) want = ackOf(op);
      Bool bad = sl.d_denied || sl.d_opcode != want || (want == opAckData && sl.d_corrupt);
      nst = 0; nan = True;
      nax = RegRsp { rdata: want == opAckData ? sl.d_data : 0, err: bad };
    end else if (aHs)
      nst = 2;
    st <= nst; held <= nhd; ansV <= nan; ansX <= nax;
  endrule

  method Action req(Bool valid, RegReq#(aw, dw) r);
    if (valid && st == 0 && !ansV) begin takeV <= True; takeR <= r; end
  endmethod
  method Bool ready = st == 0 && !ansV;
  method Bool rspValid = ansV;
  method RegRsp#(dw) rsp = ansX;
endmodule

// 发起方引脚：完成方引脚的对偶，片外接一个 TL-UL 完成方
interface TlulMasterPins#(numeric type aw, numeric type dw, numeric type sw);
  (* always_ready, result = "a_valid" *)   method Bool               a_valid;
  (* always_ready, result = "a_opcode" *)  method Bit#(3)            a_opcode;
  (* always_ready, result = "a_param" *)   method Bit#(3)            a_param;
  (* always_ready, result = "a_size" *)    method Bit#(2)            a_size;
  (* always_ready, result = "a_source" *)  method Bit#(sw)           a_source;
  (* always_ready, result = "a_address" *) method Bit#(aw)           a_address;
  (* always_ready, result = "a_mask" *)    method Bit#(TDiv#(dw, 8)) a_mask;
  (* always_ready, result = "a_data" *)    method Bit#(dw)           a_data;
  (* always_ready, result = "a_corrupt" *) method Bool               a_corrupt;
  (* always_ready, always_enabled, prefix = "" *)
  method Action a_rdy((* port = "a_ready" *) Bool r);
  (* always_ready, always_enabled, prefix = "" *)
  method Action d_rsp((* port = "d_valid" *)   Bool     v,
                      (* port = "d_opcode" *)  Bit#(3)  op,
                      (* port = "d_param" *)   Bit#(2)  param,
                      (* port = "d_size" *)    Bit#(2)  size,
                      (* port = "d_source" *)  Bit#(sw) source,
                      (* port = "d_sink" *)    Bit#(1)  sink,
                      (* port = "d_denied" *)  Bool     denied,
                      (* port = "d_data" *)    Bit#(dw) data,
                      (* port = "d_corrupt" *) Bool     corrupt);
  (* always_ready, result = "d_ready" *)   method Bool               d_ready;
endinterface

interface TlulWire#(numeric type aw, numeric type dw, numeric type sw);
  interface TlulSlavePins#(aw, dw, sw)  slave;
  interface TlulMasterPins#(aw, dw, sw) master;
endinterface

typedef struct {
  Bool               valid;
  Bit#(3)            op;
  Bit#(3)            param;
  Bit#(2)            size;
  Bit#(sw)           source;
  Bit#(aw)           address;
  Bit#(TDiv#(dw, 8)) mask;
  Bit#(dw)           data;
  Bool               corrupt;
} TlAWire#(numeric type aw, numeric type dw, numeric type sw) deriving (Bits);

module mkTlulWire(TlulWire#(aw, dw, sw));
  Wire#(TlAWire#(aw, dw, sw))    aW   <- mkBypassWire;
  Wire#(Bool)                    aR   <- mkBypassWire;
  Wire#(Tuple2#(Bool, TlD#(dw, sw))) dW <- mkBypassWire;
  Wire#(Bool)                    dRdy <- mkBypassWire;

  interface TlulSlavePins slave;
    method Action a_in(Bool av, Bit#(3) op, Bit#(3) param, Bit#(2) size, Bit#(sw) source,
                       Bit#(aw) address, Bit#(TDiv#(dw, 8)) mask, Bit#(dw) data, Bool corrupt);
      aW <= TlAWire { valid: av, op: op, param: param, size: size, source: source,
                      address: address, mask: mask, data: data, corrupt: corrupt };
    endmethod
    method Bool     a_ready   = aR;
    method Bool     d_valid   = tpl_1(dW);
    method Bit#(3)  d_opcode  = tpl_2(dW).opcode;
    method Bit#(2)  d_param   = 0;
    method Bit#(2)  d_size    = tpl_2(dW).size;
    method Bit#(sw) d_source  = tpl_2(dW).source;
    method Bit#(1)  d_sink    = 0;
    method Bool     d_denied  = tpl_2(dW).denied;
    method Bit#(dw) d_data    = tpl_2(dW).data;
    method Bool     d_corrupt = tpl_2(dW).corrupt;
    method Action d_in(Bool dr); dRdy <= dr; endmethod
  endinterface

  interface TlulMasterPins master;
    method Bool               a_valid   = aW.valid;
    method Bit#(3)            a_opcode  = aW.op;
    method Bit#(3)            a_param   = aW.param;
    method Bit#(2)            a_size    = aW.size;
    method Bit#(sw)           a_source  = aW.source;
    method Bit#(aw)           a_address = aW.address;
    method Bit#(TDiv#(dw, 8)) a_mask    = aW.mask;
    method Bit#(dw)           a_data    = aW.data;
    method Bool               a_corrupt = aW.corrupt;
    method Action a_rdy(Bool r); aR <= r; endmethod
    method Action d_rsp(Bool v, Bit#(3) op, Bit#(2) param, Bit#(2) size, Bit#(sw) source, Bit#(1) sink,
                        Bool denied, Bit#(dw) data, Bool corrupt);
      dW <= tuple2(v, TlD { opcode: op, size: size, source: source, denied: denied, data: data, corrupt: corrupt });
    endmethod
    method Bool               d_ready   = dRdy;
  endinterface
endmodule

instance Bus#(TlulSlavePins#(aw, dw, sw), aw, dw)
    provisos (Mul#(TDiv#(dw, 8), 8, dw));
  function Module#(TlulSlavePins#(aw, dw, sw)) bindT(RegTarget#(aw, dw) t) = mkTlulBindT(t);
  function Module#(RegTarget#(aw, dw)) adopt(TlulSlavePins#(aw, dw, sw) p) = mkTlulAdopt(p);
endinstance

endpackage
