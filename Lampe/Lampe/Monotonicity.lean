import Lampe.Ast
import Lampe.Hoare.SepTotal
import Lampe.Hoare.Total
import Lampe.Semantics
import Lampe.Tactic.SL
import Lampe.Tp

namespace Lampe

-- TODO stick this in the STHoare namespace

-- States that a given theorem on a Hoare Triple is valid for any environment Γₒ that contains the
-- environment Γᵢ for which the theorem was originally proven.
--
-- In detail:
--
-- - `p` is the value of the field prime under which the proof should hold.
-- - `Γᵢ` is the "inner" environment, namely the one for which a proof of the Hoare triple already
--   exists, while `Γₒ` is the "outer" environment, the one for which we want our existing proof to
--   hold.
-- - `pre` is the precondition for our Hoare triples, namely the state in which our program is
--   before executing `expr`.
-- - `expr` is the program expression to be "executed" in both cases.
-- - `post` is the postcondition for our Hoare triples, namely the state in which our program will
--   end up if `expr` evaluates.
--
-- See the documentation for `STHoare` for more detail.
theorem STHoare.is_monotonic 
    {p : Prime} 
    {Γᵢ Γₒ : Env}
    {pre : SLP (State p)}
    {expr : Expr (Tp.denote p) tp}
    {post : Tp.denote p tp → SLP (State p)}
    {innerSubsetOuter : Γᵢ ⊆ Γₒ}
  : STHoare p Γᵢ pre expr post → STHoare p Γₒ pre expr post := 
  sorry

end Lampe
