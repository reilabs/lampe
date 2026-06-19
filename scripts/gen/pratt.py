#!/usr/bin/env python3
"""Pratt primality certificate generator.

Regenerates the `Nat.Prime <P>` certificate region of a `Prime.lean`
file in place, using Mathlib's `lucas_primality` theorem applied
recursively to every prime factor of (P-1) that exceeds `norm_num`'s
trial-division threshold.

The prime `P` is read from the target file's own `def primeNat : Nat :=`
definition (outside the markers). The certificate lives between:

    -- BEGIN generated Pratt certificate --
    ...
    -- END generated Pratt certificate --

Everything outside the markers is hand-maintained and untouched.

Usage:
    python3 scripts/gen/pratt.py <path/to/Prime.lean>

Requires: sympy (for factorization and primality oracle).
"""

import re
import sys

from _lean import update_region

try:
    from sympy import factorint
except ImportError:
    print(
        "error: sympy not installed. Install with: "
        "pip3 install --user --break-system-packages sympy",
        file=sys.stderr,
    )
    sys.exit(1)


LABEL = "Pratt certificate"
DO_NOT_EDIT_NOTE = (
    "-- Do not edit between the markers; regenerate with"
    " `scripts/gen/pratt.py <path>`."
)

# Named constants the BN254 file uses in place of a decimal literal.
NAMED_PRIMES = {
    "r_scalar": 21888242871839275222246405745257275088548364400416034343698204186575808495617,
}


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


def generate_body(P) -> str:
    """The text between the BEGIN/END markers."""
    nodes = {}
    build_nodes(P, nodes)

    out = [DO_NOT_EDIT_NOTE]
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
    return "\n".join(out)


def read_prime(path: str) -> int:
    """Parse the prime from the file's `def primeNat : Nat :=` value."""
    with open(path, encoding="utf-8") as f:
        text = f.read()
    m = re.search(r"def\s+primeNat\s*:\s*Nat\s*:=\s*([^\n]*)", text)
    if not m:
        print(f"error: no `def primeNat : Nat :=` found in {path}", file=sys.stderr)
        sys.exit(1)
    value = m.group(1).strip()
    if not value:
        # Literal on the next line.
        m2 = re.search(r"def\s+primeNat\s*:\s*Nat\s*:=\s*\n\s*([^\n]+)", text)
        if not m2:
            print(f"error: cannot read primeNat value in {path}", file=sys.stderr)
            sys.exit(1)
        value = m2.group(1).strip()
    if value.isdigit():
        return int(value)
    if value in NAMED_PRIMES:
        return NAMED_PRIMES[value]
    print(
        f"error: unrecognized primeNat value {value!r} in {path}",
        file=sys.stderr,
    )
    sys.exit(1)


def main():
    if len(sys.argv) != 2:
        print("usage: pratt.py <path/to/Prime.lean>", file=sys.stderr)
        sys.exit(1)
    path = sys.argv[1]
    P = read_prime(path)
    update_region(path, generate_body(P), label=LABEL)


if __name__ == "__main__":
    main()
