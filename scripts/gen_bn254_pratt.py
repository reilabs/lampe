#!/usr/bin/env python3
"""Generate the BN254 scalar-field Pratt primality certificate as a Lean file.

Produces `stdlib/lampe/Stdlib/Field/Bn254/Prime.lean`. Uses Mathlib's
`lucas_primality` theorem: a number `p` is prime if there exists `a` such
that `a^(p-1) = 1 mod p` and `a^((p-1)/q) != 1 mod p` for every prime
factor `q` of `p-1`. Applied recursively, each `q` itself needs a
primality witness — yielding a Pratt certificate tree.

For the BN254 scalar-field prime (254 bits) the tree has 8 nodes:

    21888242871839275222246405745257275088548364400416034343698204186575808495617
    ├── 405928799
    ├── 1670836401704629 ─→ 5156902474397 ─→ 12048837557
    └── 13818364434197438864469338081 ─→ 65865678001877903 ─→ 639533339

Run from the repository root::

    python3 scripts/gen_bn254_pratt.py > stdlib/lampe/Stdlib/Field/Bn254/Prime.lean

Requires: sympy (for factorization + primality checks).
"""

import sys

try:
    from sympy import factorint, isprime
except ImportError:
    print(
        "error: sympy not installed. Install with: "
        "pip3 install --user --break-system-packages sympy",
        file=sys.stderr,
    )
    sys.exit(1)

# The BN254 scalar-field prime.
R = 21888242871839275222246405745257275088548364400416034343698204186575808495617


def find_generator(p, factors_p_minus_1):
    """Find a generator a of (Z/pZ)* via Lucas: a^(p-1) = 1 and
    a^((p-1)/q) != 1 for every prime factor q of p-1."""
    n = p - 1
    for a in range(2, 200):
        if pow(a, n, p) != 1:
            continue
        if all(pow(a, n // q, p) != 1 for q in factors_p_minus_1):
            return a
    raise RuntimeError(f"no small generator found for prime {p}")


def build_nodes(p, nodes):
    """Populate `nodes[p] = {generator, factors}` and recurse into sub-primes
    that exceed 25 bits (`norm_num`'s trial-division threshold)."""
    if p in nodes or p == 2:
        return
    factors = factorint(p - 1)
    nodes[p] = {"generator": find_generator(p, factors), "factors": factors}
    for q in factors:
        if q > 2 and q.bit_length() > 25:
            build_nodes(q, nodes)


def factor_product_str(factors):
    """Right-associated product of all factors with multiplicities."""
    parts = [str(q) if e == 1 else f"{q}^{e}" for q, e in sorted(factors.items())]
    if len(parts) == 1:
        return parts[0]
    result = parts[-1]
    for part in reversed(parts[:-1]):
        result = f"{part} * ({result})"
    return result


def emit_have_block(factors):
    """Emit `have h<N> : Nat.Prime <N> := ...` lines."""
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
    """Emit the `rcases ... ` chain handling each prime factor.

    The factor list is consumed right-associated by `dvd_mul`; each middle
    factor splits into `hcase | hrest`, and the **final** factor is the
    residue `hrest`, used directly without a `let`-rename.
    """
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
    """Emit one `private theorem prime_<p>` block."""
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


HEADER = """\
import Stdlib.Field.Bn254
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.NormNum.Prime

/-!
# BN254 scalar-field prime: Pratt certificate and canonical `Lampe.Prime`

This file is **mechanically generated by** `scripts/gen_bn254_pratt.py`.
Do not edit by hand; rerun the script if the cert needs to change.

It provides:
- A formal Pratt primality certificate for the BN254 scalar-field prime
  (a 254-bit number), using Mathlib's `lucas_primality` theorem.
- The canonical `Bn254.prime : Lampe.Prime` value built from that cert.
- The `Bn254.Prime Bn254.prime` typeclass instance.

Downstream consumers that need a concrete BN254-context `p : Lampe.Prime`
should import this file. Files that only use BN254 algebraic facts
(via the `[Bn254.Prime p]` instance argument) can stay with just
`Stdlib.Field.Bn254` and let downstream callers provide the instance.
-/

namespace Lampe.Stdlib.Field.Bn254
"""

FOOTER_TEMPLATE = """
/-- The BN254 scalar-field prime literal. -/
def primeNat : Nat :=
  {R}

/-- Primality of the BN254 scalar-field prime, established via a Pratt
certificate using `lucas_primality` (see the certificate above). -/
theorem primeNat_prime : Nat.Prime primeNat :=
  prime_{R}

private lemma primeNat_gt_two : primeNat > 2 := by unfold primeNat; norm_num

/-- The canonical BN254 `Lampe.Prime` value. -/
def prime : Lampe.Prime := Lampe.Prime.ofNat primeNat primeNat_prime primeNat_gt_two

/-- The canonical `Bn254.Prime Bn254.prime` instance.

Resolves automatically for downstream specs that take `[Bn254.Prime p]`. -/
instance : Bn254.Prime Bn254.prime where
  modulus_eq := by native_decide

end Lampe.Stdlib.Field.Bn254
"""


def main():
    nodes = {}
    build_nodes(R, nodes)

    out = [HEADER]
    out.append("/-! ### Pratt certificate")
    out.append("")
    out.append("Each `prime_<p>` lemma proves `Nat.Prime <p>` via Mathlib's")
    out.append("`lucas_primality`. The certificate has 8 nodes:")
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

    out.append(FOOTER_TEMPLATE.format(R=R))
    print("\n".join(out))


if __name__ == "__main__":
    main()
