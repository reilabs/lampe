import Mathlib
import Lampe.Ast

namespace Lampe

def newLambda (argTps : List Tp) {outTp : Tp} (body : HList rep argTps → Expr rep outTp) : Function :=  {
  generics := []
  inTps := fun _ => argTps
  outTp := fun _ => outTp
  rep := rep
  body := fun _ => body
}

def Ident.ofLambdaRef (lambdaRef : Ref) : Ident := toString lambdaRef.val

end Lampe
