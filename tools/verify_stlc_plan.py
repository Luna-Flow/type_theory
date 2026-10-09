#!/usr/bin/env python3
"""Compare STLC normalization with the frozen, merged PR #30 implementation.

Run from the module root. Requires the baseline Git object and MoonBit tools.
Generates a temporary whitebox oracle; removes it even when comparison fails.
This is a bounded compatibility check, not a universal proof.
"""
import argparse
from pathlib import Path
import re
import subprocess

BASELINE = "db53d775e9248e8712a240adc8327be72675c80f"
CORPUS = r'''
///|
test "issue 27: bounded differential oracle from merged PR30" {
  let name = fn(s) { @core.Name::new(s) }
  let a = Ty::Base(name("A"))
  let u = Ty::Unit
  let aa = Ty::Arrow(a, a)
  let sig = Signature::empty().extend_with(name("c"), a).extend_with(name("h"), Ty::Arrow(aa, a))
  let ctx = TypeContext::empty().extend_with(name("x"), a).extend_with(name("f"), aa)
  let x : Term = @syntax.Variable(name("x"))
  let y : Term = @syntax.Variable(name("y"))
  let seeds : Array[Term] = [x, y, @syntax.Variable(name("f")), @syntax.Value(Atom::UnitLit), @syntax.Value(Atom::Const(name("c"))), @syntax.Value(Atom::Const(name("missing"))), @syntax.Bind(name("x"), x), @syntax.Apply(x, [])]
  let layer = seeds.copy()
  for body in seeds {
    layer.push(@syntax.Bind(name("x"), body))
    layer.push(@syntax.Bind(name("y"), body))
    for argument in seeds { layer.push(@syntax.Apply(body, [argument])) }
  }
  let terms = layer.copy()
  for head in layer {
    terms.push(@syntax.Bind(name("x"), head))
    for argument in layer { terms.push(@syntax.Apply(head, [argument])) }
    for argument in seeds { terms.push(@syntax.Apply(head, [argument, x])) }
  }
  let mut count = 0
  for term in terms {
    assert_eq(infer(sig, ctx, term), oracle_infer(sig, ctx, term))
    for ty in [a, u, aa, Ty::Arrow(u, aa), Ty::Arrow(aa, a)] {
      assert_eq(check(sig, ctx, term, ty), oracle_check(sig, ctx, term, ty))
      let expected = oracle_normalize_eta_long(sig, ctx, term, ty)
      let actual = normalize_eta_long(sig, ctx, term, ty)
      // Compare exact output, including generated names, as well as errors.
      assert_eq(actual, expected)
      count = count + 1
    }
  }
  println(count)
}
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--target", choices=["native", "js", "wasm", "wasm-gc", "all"], default="native")
    args = parser.parse_args()
    oracle = Path("src/stlc/issue27_oracle_wbtest.mbt")
    if oracle.exists():
        raise SystemExit(f"Refusing to overwrite {oracle}")
    source = "\n".join(subprocess.check_output(
        ["git", "show", BASELINE + ":" + path], text=True
    ) for path in ("src/stlc/nbe.mbt", "src/stlc/typecheck.mbt"))
    functions = re.findall(r"(?:pub )?fn (\w+)\(", source)
    types = re.findall(r"priv (?:enum|struct) (\w+)", source)
    variants = []
    for block in re.findall(r"priv enum \w+ \{(.*?)\n\}", source, re.S):
        variants.extend(re.findall(r"^  ([A-Z]\w*)(?:\(|\s*$)", block, re.M))
    for symbol in sorted(set(functions + types + variants), key=len, reverse=True):
        prefix = "oracle_" if symbol[0].islower() else "Oracle_"
        source = re.sub(r"\b" + symbol + r"\b", prefix + symbol, source)
    source = source.replace("pub fn", "fn").replace("@syntax.Oracle_Value", "@syntax.Value")
    targets = ["wasm-gc", "js", "native", "wasm"] if args.target == "all" else [args.target]
    try:
        oracle.write_text(source + CORPUS)
        for target in targets:
            subprocess.run(["moon", "test", "src/stlc", "--target", target,
                            "--filter", "issue 27: bounded differential oracle*"], check=True)
    finally:
        oracle.unlink(missing_ok=True)


if __name__ == "__main__":
    main()
