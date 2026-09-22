package TilelinkTb;

import TilelinkCfg::*;

import StmtFSM::*;
import ConfigReg::*;
import RegIf::*;
import Tilelink::*;

// 零等待假外设：0x04 读写（按掩码合并）· 0x08 读回写过几次（被拒的请求不许动它）· 0x0C 一律回错
module mkTlPeriph(RegIf#(AW, DW));
  Reg#(Bit#(DW)) v  <- mkReg(0);
  Reg#(Bit#(16)) wc <- mkReg(0);

  method ActionValue#(RegRsp#(DW)) access(RegReq#(AW, DW) r);
    Bool     er = r.addr == 'h0C;
    Bit#(DW) rd = r.addr == 'h08 ? zeroExtend(wc) : v;
    if (r.write && !er) begin
      wc <= wc + 1;
      if (r.addr == 'h04) v <= applyStrb(v, r.wdata, r.wstrb);
    end
    return RegRsp { rdata: rd, err: er };
  endmethod
endmodule

// 会停顿的同一个外设，压 n 拍才答。端口 0 归规则，端口 1 归方法
module mkTlSlow#(Integer n)(RegTarget#(AW, DW));
  Reg#(Bit#(8))        cnt[2]  <- mkCReg(2, 0);
  Reg#(Bool)           busy[2] <- mkCReg(2, False);
  Reg#(Bool)           ansV[2] <- mkCReg(2, False);
  Reg#(RegReq#(AW, DW)) q[2]    <- mkCReg(2, unpack(0));
  Reg#(RegRsp#(DW))    ans[2]  <- mkCReg(2, unpack(0));
  Reg#(Bit#(DW))       v       <- mkReg(0);
  Reg#(Bit#(16))       wc      <- mkReg(0);

  rule tick;
    if (busy[0] && cnt[0] == 0) begin
      let r = q[0];
      Bool er = r.addr == 'h0C;
      busy[0] <= False;
      ansV[0] <= True;
      ans[0]  <= RegRsp { rdata: r.addr == 'h08 ? zeroExtend(wc) : v, err: er };
      if (r.write && !er) begin
        wc <= wc + 1;
        if (r.addr == 'h04) v <= applyStrb(v, r.wdata, r.wstrb);
      end
    end else begin
      if (busy[0]) cnt[0] <= cnt[0] - 1;
      ansV[0] <= False;
    end
  endrule

  method Action req(Bool valid, RegReq#(AW, DW) r);
    if (valid && !busy[1] && !ansV[1]) begin
      busy[1] <= True;
      cnt[1]  <= fromInteger(n);
      q[1]    <= r;
    end
  endmethod
  method Bool ready = !busy[1] && !ansV[1];
  method Bool rspValid = ansV[1];
  method RegRsp#(DW) rsp = ans[1];
endmodule

// 一个 TL-UL 主机。从设备输出都出自寄存器，读 a_ready、d_valid 与驱动引脚写在同一条规则里。
// 主机寄存器端口 0 归这条规则，端口 1 归命令序列。
(* synthesize *)
module mkTilelinkTb(Empty);
  RegIf#(AW, DW)            dev  <- mkTlPeriph;
  RegTarget#(AW, DW)        sdev <- mkTlSlow(2);
  TlulSlavePins#(AW, DW, 4) sa   <- mkTlulBind(dev);
  TlulSlavePins#(AW, DW, 4) sb   <- mkTlulBindT(sdev);

  Reg#(Bool)     onB       <- mkReg(False);
  Reg#(Bool)     av[2]     <- mkCReg(2, False);
  Reg#(Bool)     aTaken[2] <- mkCReg(2, False);
  Reg#(Bool)     got[2]    <- mkCReg(2, False);
  Reg#(Bool)     bad[2]    <- mkCReg(2, False);
  Reg#(Bit#(3))  op   <- mkReg(0);
  Reg#(Bit#(4))  src  <- mkReg(0);
  Reg#(Bit#(AW))  adr  <- mkReg(0);
  Reg#(Bit#(TDiv#(DW, 8)))  msk  <- mkReg('1);
  Reg#(Bit#(DW)) dat  <- mkReg(0);
  Reg#(Bool)     crp  <- mkReg(False);
  Reg#(Bool)     drdy <- mkReg(True);

  // 主机规则写、命令序列读：用 ConfigReg，两边才排得出先后（否则 G0010，命令序列饿死）
  Reg#(Bit#(3))  gOp  <- mkConfigReg(0);
  Reg#(Bit#(2))  gPar <- mkConfigReg(0);
  Reg#(Bit#(2))  gSz  <- mkConfigReg(0);
  Reg#(Bit#(4))  gSrc <- mkConfigReg(0);
  Reg#(Bool)     gDen <- mkConfigReg(False);
  Reg#(Bit#(DW)) gDat <- mkConfigReg(0);
  Reg#(Bool)     gCor <- mkConfigReg(False);

  Reg#(Bool)     pV    <- mkReg(False);
  Reg#(Bool)     pHs   <- mkReg(False);
  Reg#(Bit#(DW)) pDat  <- mkReg(0);
  Reg#(Bit#(4))  pSrc  <- mkReg(0);
  Reg#(Bool)     said0 <- mkReg(False);
  Reg#(Bool)     said1 <- mkReg(False);

  rule master;
    Bool     ar   = onB ? sb.a_ready   : sa.a_ready;
    Bool     dv   = onB ? sb.d_valid   : sa.d_valid;
    Bit#(3)  dop  = onB ? sb.d_opcode  : sa.d_opcode;
    Bit#(2)  dpar = onB ? sb.d_param   : sa.d_param;
    Bit#(2)  dsz  = onB ? sb.d_size    : sa.d_size;
    Bit#(4)  dsrc = onB ? sb.d_source  : sa.d_source;
    Bool     dden = onB ? sb.d_denied  : sa.d_denied;
    Bit#(DW) ddat = onB ? sb.d_data    : sa.d_data;
    Bool     dcor = onB ? sb.d_corrupt : sa.d_corrupt;

    sa.a_in(av[0] && !onB, op, 0, 2, src, adr, msk, dat, crp);
    sb.a_in(av[0] && onB,  op, 0, 2, src, adr, msk, dat, crp);
    sa.d_in(drdy);
    sb.d_in(drdy);

    if (av[0] && ar) begin av[0] <= False; aTaken[0] <= True; end
    Bool hs = dv && drdy;
    if (hs) begin
      got[0] <= True;
      gOp <= dop; gPar <= dpar; gSz <= dsz; gSrc <= dsrc; gDen <= dden; gDat <= ddat; gCor <= dcor;
    end

    Bool fail = False;
    if (dv && !aTaken[0] && !said0) begin
      $display("FAIL d_valid came before the request was accepted");
      said0 <= True; fail = True;
    end
    if (pV && !pHs && (!dv || ddat != pDat || dsrc != pSrc) && !said1) begin
      $display("FAIL d_valid, d_data or d_source changed before d_ready took the response");
      said1 <= True; fail = True;
    end
    pV <= dv; pHs <= hs; pDat <= ddat; pSrc <= dsrc;
    if (fail) bad[0] <= True;
  endrule

  function Action offer(Bit#(3) o, Bit#(4) s, Bit#(AW) a, Bit#(TDiv#(DW, 8)) m, Bit#(DW) d, Bool c) = action
    op <= o; src <= s; adr <= a; msk <= m; dat <= d; crp <= c;
    aTaken[1] <= False; got[1] <= False; av[1] <= True;
  endaction;

  function Stmt request(Bit#(3) o, Bit#(4) s, Bit#(AW) a, Bit#(TDiv#(DW, 8)) m, Bit#(DW) d, Bool c) = seq
    offer(o, s, a, m, d, c);
    await(got[1]);
  endseq;

  function Stmt want(Bit#(3) o, Bit#(4) s, Bool den, Bool cor, Bool checkData, Bit#(DW) d, String what) = seq
    action
      Bool wrong = gOp != o || gSrc != s || gDen != den || gCor != cor || gSz != 2 || gPar != 0
                   || (checkData && gDat != d);
      if (wrong) begin
        $display("FAIL %s: d_opcode %0d d_source %0d d_denied %0d d_corrupt %0d d_size %0d d_param %0d d_data %08h",
                 what, gOp, gSrc, gDen, gCor, gSz, gPar, gDat);
        bad[1] <= True;
      end
    endaction
  endseq;

  Stmt suite = seq
    request(0, 4'h3, 'h04, '1, 'h11111111, False);    want(0, 4'h3, False, False, False, 0, "PutFullData");
    request(4, 4'h5, 'h04, '1, 0, False);               want(1, 4'h5, False, False, True, 'h11111111, "Get after PutFullData");
    request(1, 4'h6, 'h04, 'b1010, 'hAABBCCDD, False); want(0, 4'h6, False, False, False, 0, "PutPartialData on bytes 1 and 3");
    request(4, 4'h7, 'h04, '1, 0, False);               want(1, 4'h7, False, False, True, 'hAA11CC11, "Get after PutPartialData");
    request(0, 4'h8, 'h0C, '1, 0, False);               want(0, 4'h8, True, False, False, 0, "PutFullData to the address that errors");
    request(4, 4'h9, 'h0C, '1, 0, False);               want(1, 4'h9, True, True, False, 0, "Get of the address that errors");
    request(2, 4'hA, 'h04, '1, 'hFFFFFFFF, False);    want(1, 4'hA, True, True, False, 0, "ArithmeticData, which TL-UL does not have");
    request(0, 4'hB, 'h04, '1, 'hFFFFFFFF, True);     want(0, 4'hB, True, False, False, 0, "PutFullData with a_corrupt");
    request(4, 4'hC, 'h08, '1, 0, False);               want(1, 4'hC, False, False, True, 2, "the write count after two accepted writes");
    request(4, 4'hE, 'h04, '1, 0, False);               want(1, 4'hE, False, False, True, 'hAA11CC11, "the register after the denied requests");

    // 答复要等 d_ready，等的时候不许变
    action drdy <= False; endaction
    offer(4, 4'hD, 'h04, '1, 0, False);
    delay(8);
    action drdy <= True; endaction
    await(got[1]);                                         want(1, 4'hD, False, False, True, 'hAA11CC11, "a Get whose response waited eight cycles for d_ready");
  endseq;

  Stmt test = seq
    suite;
    action onB <= True; endaction
    suite;
  endseq;

  FSM fsm <- mkFSM(test);
  Reg#(Bool)      started <- mkReg(False);
  Reg#(UInt#(16)) cyc     <- mkReg(0);

  rule go (!started);
    started <= True;
    fsm.start;
  endrule

  rule count;
    cyc <= cyc + 1;
    if (cyc > 4000) begin
      $display("TIMEOUT");
      $finish(1);
    end
  endrule

  rule fin (started && fsm.done);
    if (bad[1]) $display("FAILED");
    else $display("PASS tilelink: Get and both Puts answer with the right opcode, size and source, masks merge, "
                  + "errors, unsupported opcodes and corrupt writes are denied without side effects with denied "
                  + "data marked corrupt, and responses hold until d_ready, for a zero-wait and a stalling target");
    $finish(bad[1] ? 1 : 0);
  endrule
endmodule

endpackage
