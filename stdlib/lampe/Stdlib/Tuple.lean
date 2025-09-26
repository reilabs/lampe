import Lampe
import Stdlib.Tp

namespace Lampe.Stdlib.Tuple

set_option Lampe.pp.Expr false
set_option Lampe.pp.STHoare false

/--
Implements the ordering relation on Noir's tuples, as is expressed in the various implementations of
`std::cmp::Ord` for the various tuple sizes.
-/
@[reducible]
def compare {p memTps}
    (memEmbOrdFns : HList (Tp.comparator p) memTps)
    (self other : Tp.denote p (.tuple none memTps))
  : Ordering :=
match memTps, memEmbOrdFns with
| tp :: tps, .cons f fs =>
  match f self.1 other.1 with
  | .eq => compare fs self.2 other.2
  | o => o
| [], .nil => .eq

@[reducible]
def mk {p memTps} (args : HList (Tp.denote p) memTps)
  : Tp.denote p (.tuple none memTps) :=
match memTps, args with
| tp :: tps, .cons arg args =>
  let rest := mk args
  (arg, rest)
| [], .nil => ()

@[reducible]
def snoc
    (hs : Tp.denote p (Tp.tuple none tps))
    (a : Tp.denote p tp)
  : Tp.denote p (Tp.tuple none (tps ++ [tp])) :=
match tps, hs with
| [], () => (a, ())
| _::_, (h, hs) => (h, snoc hs a)

lemma head_eq_fst {p}
    {tp : Tp}
    {tps : List Tp}
    {tuple : Tp.denote p (.tuple none (tp :: tps))}
  : Builtin.indexTpl tuple Builtin.Member.head = tuple.1 := by
  cases tuple; rfl

lemma tail_head_eq_snd {p}
    {t1 : Tp}
    {t2 : Tp}
    {tps : List Tp}
    {tuple : Tp.denote p (.tuple none (t1 :: t2 :: tps))}
  : Builtin.indexTpl tuple Builtin.Member.head.tail = tuple.2.1 := by
  cases tuple; rfl

lemma tail_tail_head_eq_third {p}
    {t1 : Tp}
    {t2 : Tp}
    {t3 : Tp}
    {tps : List Tp}
    {tuple : Tp.denote p (.tuple none (t1 :: t2 :: t3 :: tps))}
  : Builtin.indexTpl tuple Builtin.Member.head.tail.tail = tuple.2.2.1 := by
  cases tuple; rfl

lemma tail_tail_tail_head_eq_fourth {p}
    {t1 : Tp}
    {t2 : Tp}
    {t3 : Tp}
    {t4 : Tp}
    {tps : List Tp}
    {tuple : Tp.denote p (.tuple none (t1 :: t2 :: t3 :: t4 :: tps))}
  : Builtin.indexTpl tuple Builtin.Member.head.tail.tail.tail = tuple.2.2.2.1 := by
  cases tuple; rfl

lemma tail_tail_tail_tail_head_eq_fifth {p}
    {t1 : Tp}
    {t2 : Tp}
    {t3 : Tp}
    {t4 : Tp}
    {t5 : Tp}
    {tps : List Tp}
    {tuple : Tp.denote p (.tuple none (t1 :: t2 :: t3 :: t4 :: t5 :: tps))}
  : Builtin.indexTpl tuple Builtin.Member.head.tail.tail.tail.tail = tuple.2.2.2.2.1 := by
  cases tuple; rfl

lemma compare_of_head_ne_eq {p}
    {A : Tp}
    {Bs: List Tp}
    (ordA)
    (ords : HList (Tp.comparator p) Bs)
    {a1 a2 : A.denote p}
    {bs1 bs2}
    (h : ordA a1 a2 ≠ .eq)
  : compare (HList.cons ordA ords) (a1, bs1) (a2, bs2) = ordA a1 a2 := by
  simp [compare, h]

lemma compare_of_head_eq_eq {p}
    {A : Tp}
    {Bs : List Tp}
    (ordA)
    (ords : HList (Tp.comparator p) Bs)
    {a1 a2 : A.denote p}
    {bs1 bs2}
    (h : ordA a1 a2 = .eq)
  : compare (HList.cons ordA ords) (a1, bs1) (a2, bs2) = compare ords bs1 bs2 := by
  simp [compare, h]

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

