#!/usr/bin/env python3
"""Generic Pratt primality certificate generator.

Generates Lean proofs of `Nat.Prime <P>` for a given prime `P`, using
Mathlib's `lucas_primality` theorem applied recursively to every prime
factor of (P-1) that exceeds `norm_num`'s trial-division threshold.

The generated certificate lives between marker comments:

    -- BEGIN generated Pratt certificate (scripts/gen_pratt.py) --
    ...
    -- END generated Pratt certificate --

Everything outside the markers (imports, header docstring, `primeNat`
/ `prime` definitions, instances, ...) is hand-maintained and never
touched by this script.

Usage:
    # Regenerate the certificate region of an existing file, in place.
    # Only the text between the markers is replaced; the rest of the
    # file is preserved byte-for-byte.
    python3 scripts/gen_pratt.py --prime <decimal-or-hex> \
        --update <path/to/Prime.lean>

    # Bootstrap a scaffold for a brand-new prime (written to stdout).
    # The scaffold uses a generic header/footer that the author then
    # hand-tunes; subsequent regenerations should use --update.
    python3 scripts/gen_pratt.py --prime <decimal-or-hex> \
        --namespace <Name> > Lampe/Lampe/Crypto/<Name>/Prime.lean

Requires: sympy (for factorization and primality oracle).
"""

import argparse
import sys

try:
    from sympy import factorint
except ImportError:
    print(
        "error: sympy not installed. Install with: "
        "pip3 install --user --break-system-packages sympy",
        file=sys.stderr,
    )
    sys.exit(1)


BEGIN_MARKER = "-- BEGIN generated Pratt certificate (scripts/gen_pratt.py) --"
END_MARKER = "-- END generated Pratt certificate --"
DO_NOT_EDIT_NOTE = (
    "-- Do not edit between the markers; regenerate with"
    " `scripts/gen_pratt.py --update`."
)


def find_generator(p, factors_p_minus_1):
    n = p - 1
    for a in range(2, 200):
        if pow(a, n, p) != 1:
            continue
        if all(pow(a, n // q, p) != 1 for q in factors_p_minus_1):
            return a
    raise RuntimeError(f"no small generator found for prime {p}")


def build_nodes(p, nodes):
    if p in nodes or p == 2:
        return
    factors = factorint(p - 1)
    nodes[p] = {"generator": find_generator(p, factors), "factors": factors}
    for q in factors:
        if q > 2 and q.bit_length() > 25:
            build_nodes(q, nodes)


def factor_product_str(factors):
    parts = [str(q) if e == 1 else f"{q}^{e}" for q, e in sorted(factors.items())]
    if len(parts) == 1:
        return parts[0]
    result = parts[-1]
    for part in reversed(parts[:-1]):
        result = f"{part} * ({result})"
    return result


def emit_have_block(factors):
    lines = []
    for q in sorted(factors.keys()):
        if q == 2:
            lines.append(f"    have h{q} : Nat.Prime {q} := Nat.prime_two")
        elif q == 3:
            lines.append(f"    have h{q} : Nat.Prime {q} := Nat.prime_three")
        elif q.bit_length() <= 25:
            lines.append(f"    have h{q} : Nat.Prime {q} := by norm_num")
        else:
            lines.append(f"    have h{q} : Nat.Prime {q} := prime_{q}")
    return lines


def emit_case_split(factors):
    lines = []
    items = sorted(factors.items())

    def emit_leaf(indent, hyp, q, e):
        if e == 1:
            lines.append(f"{indent}rw [(Nat.prime_dvd_prime_iff_eq hq h{q}).mp {hyp}]")
        else:
            lines.append(f"{indent}have hdvd_q : q ∣ {q} := hq.dvd_of_dvd_pow {hyp}")
            lines.append(f"{indent}rw [(Nat.prime_dvd_prime_iff_eq hq h{q}).mp hdvd_q]")
        lines.append(f"{indent}native_decide")

    def recurse(indent, items_, hyp):
        if len(items_) == 1:
            q, e = items_[0]
            lines.append(f"{indent}-- {hyp} : q ∣ {q}^{e}")
            emit_leaf(indent, hyp, q, e)
            return
        q, e = items_[0]
        rest = items_[1:]
        lines.append(f"{indent}rcases (hq.dvd_mul).mp {hyp} with hcase | hrest")
        lines.append(f"{indent}· -- q ∣ {q}^{e}")
        emit_leaf(indent + "  ", "hcase", q, e)
        lines.append(f"{indent}· -- q ∣ rest")
        recurse(indent + "  ", rest, "hrest")

    recurse("    ", items, "hdvd")
    return lines


def emit_pratt_node(p, n):
    factors = n["factors"]
    gen = n["generator"]
    out = [
        f"private theorem prime_{p} : Nat.Prime {p} := by",
        f"  refine lucas_primality {p} ({gen} : ZMod {p}) ?_ ?_",
        f"  · -- {gen}^({p}-1) = 1 mod {p}",
        f"    native_decide",
        f"  · intro q hq hdvd",
        f"    have h_eq : ({p} - 1 : ℕ) = {factor_product_str(factors)} := by decide",
        f"    rw [h_eq] at hdvd",
    ]
    out.extend(emit_have_block(factors))
    out.extend(emit_case_split(factors))
    return out


INVOCATION_TEMPLATE = """\
    python3 scripts/gen_pratt.py \\
      --prime {prime_arg} \\
      --update Lampe/Lampe/Crypto/{name}/Prime.lean\
"""

HEADER_TEMPLATE = """\
import Lampe.Tp
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.NormNum.Prime

/-!
# {name} field-prime Pratt primality certificate

The Pratt-certificate section of this file (between the BEGIN/END
markers below) is **mechanically generated by** `scripts/gen_pratt.py`.
Do not edit that region by hand; regenerate it in place with:

{invocation}

Everything outside the markers is hand-maintained.

It provides:
- A formal Pratt primality certificate for the {name} field prime
  ({bits}-bit), using Mathlib's `lucas_primality` theorem.
- `primeNat : Nat`, `primeNat_prime : Nat.Prime primeNat`,
  and the canonical `Lampe.Prime` value `prime`.
-/

namespace Lampe.Crypto.{name}
"""

FOOTER_TEMPLATE = """
/-- The {name} field prime literal. -/
def primeNat : Nat :=
  {prime}

/-- Primality of the {name} field prime, established via the Pratt
certificate above. -/
theorem primeNat_prime : Nat.Prime primeNat :=
  prime_{prime}

private lemma primeNat_gt_two : primeNat > 2 := by unfold primeNat; norm_num

/-- The canonical {name} `Lampe.Prime` value. -/
def prime : Lampe.Prime := Lampe.Prime.ofNat primeNat primeNat_prime primeNat_gt_two

end Lampe.Crypto.{name}
"""


def parse_prime(s: str) -> int:
    s = s.strip()
    if s.lower().startswith("0x"):
        return int(s, 16)
    return int(s)


def generate_region(P) -> str:
    """The full marked region: BEGIN marker through END marker."""
    nodes = {}
    build_nodes(P, nodes)

    out = [BEGIN_MARKER, DO_NOT_EDIT_NOTE]
    out.append("/-! ### Pratt certificate")
    out.append("")
    out.append("Each `prime_<p>` lemma proves `Nat.Prime <p>` via Mathlib's")
    out.append("`lucas_primality`. The certificate tree:")
    out.append("")
    out.append("```")
    for p in sorted(nodes):
        n = nodes[p]
        out.append(
            f"  {p}  (gen={n['generator']}, p-1 = {factor_product_str(n['factors'])})"
        )
    out.append("```")
    out.append("")
    out.append("Power conditions are discharged by `native_decide`; small prime")
    out.append("factors by `norm_num` (Mathlib's trial-division extension).")
    out.append("-/")
    out.append("")
    for p in sorted(nodes):
        out.extend(emit_pratt_node(p, nodes[p]))
        out.append("")
    out.append(END_MARKER)
    return "\n".join(out)


def find_unique_marker(text: str, marker: str, path: str) -> int:
    first = text.find(marker)
    if first == -1:
        print(f"error: marker {marker!r} not found in {path}", file=sys.stderr)
        sys.exit(1)
    if text.find(marker, first + len(marker)) != -1:
        print(f"error: marker {marker!r} appears more than once in {path}", file=sys.stderr)
        sys.exit(1)
    return first


def update_file(path: str, P: int) -> None:
    with open(path, encoding="utf-8") as f:
        text = f.read()

    begin = find_unique_marker(text, BEGIN_MARKER, path)
    end = find_unique_marker(text, END_MARKER, path)
    if end < begin:
        print(f"error: END marker precedes BEGIN marker in {path}", file=sys.stderr)
        sys.exit(1)

    prefix = text[:begin]
    suffix = text[end + len(END_MARKER):]

    if f"prime_{P}" not in prefix + suffix:
        print(
            f"error: {path} never references `prime_{P}` outside the generated "
            f"region; is --prime correct for this file?",
            file=sys.stderr,
        )
        sys.exit(1)

    new_text = prefix + generate_region(P) + suffix
    if new_text == text:
        print(f"{path}: up to date", file=sys.stderr)
        return
    with open(path, "w", encoding="utf-8") as f:
        f.write(new_text)
    print(f"{path}: regenerated certificate region", file=sys.stderr)


def bootstrap(P: int, prime_arg: str, name: str) -> None:
    invocation = INVOCATION_TEMPLATE.format(prime_arg=prime_arg, name=name)
    header = HEADER_TEMPLATE.format(
        name=name, bits=P.bit_length(), invocation=invocation
    )
    footer = FOOTER_TEMPLATE.format(name=name, prime=P)
    print("\n".join([header, generate_region(P), footer]))


def main():
    parser = argparse.ArgumentParser(
        description="Generate Pratt primality certificates as Lean proofs."
    )
    parser.add_argument(
        "--prime", required=True, help="prime literal (decimal or 0x-hex)"
    )
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument(
        "--update",
        metavar="FILE",
        help="regenerate the marked certificate region of FILE in place",
    )
    mode.add_argument(
        "--namespace",
        help="bootstrap a new scaffold under Lampe.Crypto.<Name> (to stdout)",
    )
    args = parser.parse_args()

    P = parse_prime(args.prime)
    if args.update:
        update_file(args.update, P)
    else:
        bootstrap(P, args.prime, args.namespace)


if __name__ == "__main__":
    main()
