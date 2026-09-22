"""tilelink 的测试台配置：把这一点的位宽发成 BSV 的数值类型。

库包是全库参数化最彻底的东西，测试台却钉死在一种位宽上——总线库的位宽算术
错了会同时打中每一个 IP。
"""
import json
import pathlib
import sys

out = pathlib.Path(sys.argv[1] if len(sys.argv) > 1 else ".")
out.mkdir(parents=True, exist_ok=True)
k = (json.loads(sys.argv[2]) if len(sys.argv) > 2 else {}).get("knobs", {})

(out / "TilelinkCfg.bsv").write_text(
    "package TilelinkCfg;\n\n"
    f"typedef {int(k.get('aw', 8))} AW;\n"
    f"typedef {int(k.get('dw', 32))} DW;\n\n"
    "endpackage\n", encoding="utf-8")
