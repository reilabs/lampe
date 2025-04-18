-- Generated by lampe

import Patterns.Extracted.GeneratedTypes
import Lampe

open Lampe

namespace Extracted

nr_def «Option2»::«some»<T>(value : T) -> Option2<T> {
    Option2<T> { true, value };
}

nr_def «pattern_test»<>() -> Unit {
    let opt = (@Option2::some<bool> as λ(bool) → Option2<bool>)(true);
    let t = `(1 : Field, opt, 3 : Field);
    let π0 = t;
    let x = π0.0;
    let mut is_some = (π0.1 as Option2<bool>).is_some;
    let mut value = (π0.1 as Option2<bool>).value;
    let mut z = π0.2;
    let lam = |π0 : `(bool, bool, bool), k : Field| -> bool     {
        let x = π0.0;
        let mut y = π0.1;
        let z = π0.2;
        {
            x;
        }
        };
}


def Main.env := Lampe.Env.mk [«Option2::some», «pattern_test»] []