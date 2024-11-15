import Mathlib
import Lampe.Ast

namespace Lampe

abbrev TpLambdaRef := Tp.ref .unit

def newLambda (argTps : List Tp) (outTp : Tp)
(body : (rep : Tp → Type) → HList Kind.denote [] → HList rep argTps → Expr rep outTp) : Function :=  {
  generics := []
  inTps := fun _ => argTps
  outTp := fun _ => outTp
  body := body
}

def Ident.ofLambdaRef (lambdaRef : Tp.denote p TpLambdaRef) : Ident := toString lambdaRef.val

end Lampe
