import Lampe
import Stdlib.Tp

namespace Lampe.Stdlib.Tuple

set_option Lampe.pp.Expr false
set_option Lampe.pp.STHoare false

/--
A useful shorthand for declaring the Lampe type of tuples containing `memberTypes` fields.

Specifically these are Noir _tuples_, despite the shared representation with structs, as they have
no name.
-/
def type (memberTypes : List Tp) := Tp.tuple none memberTypes

/--
A useful shorthand for declaring the type of values with tuple types.

Specifically these are Noir _tuples_, despite the shared representation with structs, as they have
no name.
-/
def denote (p : Prime) (memberTypes : List Tp) := Tp.denoteArgs p memberTypes

/--
Implements the ordering relation on Noir's tuples, as is expressed in the various implementations of
`std::cmp::Ord` for the various tuple sizes.
-/
@[reducible]
def compare {p memTps}
    (memEmbOrdFns : HList (Tp.comparator p) memTps)
    (self other : denote p memTps)
  : Ordering :=
match memTps, memEmbOrdFns with
| tp :: tps, .cons f fs =>
  match f self.1 other.1 with
  | .eq => compare fs self.2 other.2
  | o => o
| [], .nil => .eq

@[reducible]
def mk {p memTps} (args : HList (Tp.denote p) memTps) : denote p memTps :=
match memTps, args with
| tp :: tps, .cons arg args =>
  let rest := mk args
  (arg, rest)
| [], .nil => ()

@[reducible]
def snoc (hs : denote p tps) (a : Tp.denote p tp) : denote p (tps ++ [tp]) :=
match tps, hs with
| [], () => (a, ())
| _::_, (h, hs) => (h, snoc hs a)

lemma compare_singleton : compare h![ordA] a b = ordA a.1 b.1 := by
  simp only [compare]
  split <;> simp_all

lemma compare_snoc {p}
    {A : Tp}
    {As : List Tp}
    {ordA}
    {ords : HList (Tp.comparator p) As}
    {a1 b1 : A.denote p}
    {as1 bs1}
  : compare (HList.snoc ords ordA) (snoc as1 a1) (snoc bs1 b1) =
    (compare ords as1 bs1 |>.then (ordA a1 b1)) := by
  induction As with
  | nil =>
    cases ords; cases as1; cases bs1;
    simp only [compare, snoc, List.nil_append]
    split <;> simp_all
  | cons _ _ ih =>
    cases ords; cases as1; cases bs1;
    simp only [List.cons_append, compare, ih, Ordering.then]
    split
    · rfl
    · split <;> simp_all

theorem compare_snoc_of_init_eq_eq {p}
    {A : Tp}
    {As : List Tp}
    {ordA}
    {ords : HList (Tp.comparator p) As}
    {a1 b1 : A.denote p}
    {as1 bs1}
    (h : compare ords as1 bs1 = .eq)
  : compare (HList.snoc ords ordA) (snoc as1 a1) (snoc bs1 b1) = ordA a1 b1 := by
  simp [compare_snoc, h]

theorem compare_snoc_of_init_ne_eq {p}
    {A : Tp}
    {As : List Tp}
    {ordA}
    {ords : HList (Tp.comparator p) As}
    {a1 b1 : A.denote p}
    {as1 bs1}
    (h : compare ords as1 bs1 ≠ .eq)
  : compare (HList.snoc ords ordA) (snoc as1 a1) (snoc bs1 b1) = compare ords as1 bs1 := by
  simp [compare_snoc, Ordering.then]

