import «std-1.0.0-beta.12».Extracted
import Lampe

namespace Lampe.Stdlib.Tuple

open «std-1.0.0-beta.12»

set_option Lampe.pp.Expr false
set_option Lampe.pp.STHoare false

/-- 
Implements the ordering relation on Noir's tuples, as is expressed in the various implementations of
`std::cmp::Ord` for the various tuple sizes.
-/
@[reducible]
def compare {p memTps}
    (memEmbOrdFns : HList (fun t => t.denote p → t.denote p → Ordering) memTps)
    (self other : Tp.denote p (.tuple none memTps))
  : Ordering := match memTps, memEmbOrdFns with
  | tp :: tps, .cons f fs => 
    match f self.1 other.1 with
    | .eq => compare fs self.2 other.2
    | o => o
  | [], .nil => .eq

@[reducible]
def mk {p memTps} (args : HList (Tp.denote p) memTps) 
  : Tp.denote p (.tuple none memTps) := match memTps, args with
  | tp :: tps, .cons arg args => 
    let rest := mk args
    (arg, rest)
  | [], .nil => ()

@[simp]
lemma head_eq_fst {p} 
    {tp : Tp} 
    {tps : List Tp} 
    {tuple : Tp.denote p (.tuple none (tp :: tps))} 
  : Builtin.indexTpl tuple Builtin.Member.head = tuple.1 := by
  cases tuple; rfl

@[simp]
lemma tail_head_eq_snd {p} 
    {t1 : Tp} 
    {t2 : Tp}
    {tps : List Tp} 
    {tuple : Tp.denote p (.tuple none (t1 :: t2 :: tps))}
  : Builtin.indexTpl tuple Builtin.Member.head.tail = tuple.2.1 := by
  cases tuple; rfl

@[simp]
lemma tail_tail_head_eq_third {p} 
    {t1 : Tp} 
    {t2 : Tp}
    {t3 : Tp}
    {tps : List Tp} 
    {tuple : Tp.denote p (.tuple none (t1 :: t2 :: t3 :: tps))}
  : Builtin.indexTpl tuple Builtin.Member.head.tail.tail = tuple.2.2.1 := by
  cases tuple; rfl

@[simp]
lemma tail_tail_tail_head_eq_fourth {p} 
    {t1 : Tp} 
    {t2 : Tp}
    {t3 : Tp}
    {t4 : Tp}
    {tps : List Tp} 
    {tuple : Tp.denote p (.tuple none (t1 :: t2 :: t3 :: t4 :: tps))}
  : Builtin.indexTpl tuple Builtin.Member.head.tail.tail.tail = tuple.2.2.2.1 := by
  cases tuple; rfl

@[simp]
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

