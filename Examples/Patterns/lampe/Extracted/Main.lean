-- Generated by lampe

import Lampe

open Lampe

namespace Extracted

nr_struct_def Option2<T> {
    _is_some : bool,
    _value : T
}

nr_def «pattern_test»<>() -> Unit {
    let opt = (@Option2::some<bool> as λ(bool) → Option2<bool>)(true);
    let t = `(1 : Field, opt, 3 : Field);
    let π0 = t;
    let x = π0.0;
    let mut _is_some = (π0.1 as Option2<bool>)._is_some;
    let mut _value = (π0.1 as Option2<bool>)._value;
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

nr_def «Option2»::«some»<T>(_value : T) -> Option2<T> {
    Option2<T> { true, _value };
}


def env := Lampe.Env.mk [«pattern_test», «Option2::some»] []