# tilelink

TileLink TL-UL bindings for the neutral register contract.

![maturity](https://img.shields.io/badge/maturity-simulated-yellow) ![license](https://img.shields.io/badge/license-MulanPSL--2.0-blue)

Part of the [Tape-Out](https://github.com/Tape-Out) IP library: Bluespec IP over the
bus-neutral contracts in [`hwcore`](https://github.com/Tape-Out/hwcore), assembled by
[`xirang`](https://github.com/Tape-Out/xirang). Maturity runs `planned` -> `simulated` ->
`fpga-proven` -> `asic-ready` -> `silicon-proven`.

## Status

Simulated. Two binders attach an IP that only speaks the bus-neutral contract to TileLink Uncached Lightweight slave pins, following the SiFive TileLink Specification 1.8.1:

| Binder | Target |
| :-- | :-- |
| `mkTlulBind` | `RegIf`, answers at once |
| `mkTlulBindT` | `RegTarget`, may stall |

Get reads the target and answers AccessAckData; PutFullData and PutPartialData write it with `a_mask` as the byte strobes and answer AccessAck. The response copies `a_size` and `a_source`. The Channel D response comes from registers one cycle after the request is accepted, and `a_ready` depends only on whether a response is still waiting. A target error sets `d_denied`, and a denied response that carries data also sets `d_corrupt`. Opcodes TL-UL does not have, and writes with `a_corrupt` set, are denied without touching the target.

The testbench drives a TL-UL master against a zero-wait and a stalling target, using a different source id for every request. It checks both kinds of Put and Get, mask merging, denied and corrupt responses, that denied requests leave the register and write count unchanged, and that a response holds while `d_ready` is low.

`mkTlulAdopt` is the requester side: it turns TL-UL slave pins, such as a third-party slave, into a stalling `RegTarget`. It sends one request at a time with source 0 and channel A from registers, holds `d_ready` high so a response in the same cycle as the request is taken, sends a read as Get with a full `a_mask`, a fully strobed write as PutFullData and any other write as PutPartialData, and treats `d_denied`, a corrupt AccessAckData or a wrong response opcode as an error. Every request covers a whole word, so the address is aligned to `a_size` by clearing its low bits; an upstream bus such as APB4 may present an address inside a word, which TileLink does not allow.

The rules were also checked against the protocol monitor in rocket-chip (`TLMonitor`, commit `ece7b9ad`). When the binders are attached to a rocket-chip bus, declare the slave with `mayDenyPut` and `mayDenyGet`, because target errors come back denied, and with a minimum latency of one cycle. `mkTlulWire` joins slave pins driven inside the chip to master pins that leave it. TL-UL is an instance of the `Bus` type class in `hwcore`, so the generic `bridge` function and the [`bridge`](https://github.com/Tape-Out/bridge) library can bridge it to other buses.

TL-UH and TL-C operations and several requests in flight at once are not implemented.

## Specification sources

The specifications this IP is implemented against, with their links, digests and the clause-by-clause comparison, are kept on the [`spec` branch](https://github.com/Tape-Out/tilelink/tree/spec).

## License

Mulan PSL v2.
