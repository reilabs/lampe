import Lampe

open Lampe

noir_global_def FOO: Field = (42: Field);

/- 
Internally, globals get modeled as functions that take no arguments, so we have to call them as such. 
This transformation is handled by the extractor at the "reference site" of said global.
-/
noir_global_def FOOS : Array<Field, 2: u32> =
  (#_mkArray returning Array<Field, 2: u32>)(
    (FOO<> as λ() -> Field)(), (#_fAdd returning Field)((FOO<> as λ() -> Field)(), (1: Field))
  );

