import Lampe

open Lampe

noir_def foo<>() → Unit := {
  let a = 3: Field;
  #_skip
}

noir_def bar<>() → Unit := {
  let a = (#_ref returning & Field)(3: Field);
  #_skip
}
