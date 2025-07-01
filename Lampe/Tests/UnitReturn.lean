import Lampe

open Lampe

noir_def foo<>() → Unit := {
  let (a: Field) = 3: Field;
  #_skip
}

noir_def bar<>() → Unit := {
  let mut (a: Field) = 3: Field;
  #_skip
}
