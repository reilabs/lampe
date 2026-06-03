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
match memEmbOrdFns with
| .cons f fs =>
  match f self.1 other.1 with
  | .eq => compare fs self.2 other.2
  | o => o
| .nil => .eq

@[reducible]
def mk {p memTps} : HList (Tp.denote p) memTps → denote p memTps
| .cons arg args => (arg, mk args)
| .nil => ()

@[reducible]
def snoc {tps} (hs : denote p tps) (a : Tp.denote p tp) : denote p (tps ++ [tp]) :=
match tps, hs with
| [], _ => (a, ())
| _::_, hs => (hs.1, snoc hs.2 a)

lemma compare_singleton : compare h![ordA] a b = ordA a.1 b.1 := by
  unfold compare
  cases ordA a.1 b.1 <;> rfl

lemma compare_snoc {p}
    {A : Tp}
    {As : List Tp}
    {ordA}
    {ords : HList (Tp.comparator p) As}
    {a1 b1 : A.denote p}
    {as1 bs1}
  : compare (HList.snoc ords ordA) (snoc as1 a1) (snoc bs1 b1) =
    (compare ords as1 bs1 |>.then (ordA a1 b1)) := by
  induction ords with
  | nil =>
    cases as1; cases bs1
    show compare h![ordA] (a1, ()) (b1, ()) = Ordering.eq.then (ordA a1 b1)
    rw [compare_singleton]
    cases ordA a1 b1 <;> rfl
  | cons aHd ordsTl ih =>
    cases as1 with | mk asHd asTl =>
    cases bs1 with | mk bsHd bsTl =>
    show (match aHd asHd bsHd with
            | .eq => compare (ordsTl.snoc ordA) (snoc asTl a1) (snoc bsTl b1)
            | o => o) =
          (match aHd asHd bsHd with
            | .eq => compare ordsTl asTl bsTl
            | o => o).then (ordA a1 b1)
    cases aHd asHd bsHd <;> first | (dsimp only; exact ih) | rfl

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

