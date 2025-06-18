pub mod uncons;

use uncons::weird_eq_witness;

// This is pointless, but demonstrated how we can use unconstrained functions
pub fn weird_assert_eq(a : Field, b : Field) {
    // Safety: Foobar
    let wit = unsafe { weird_eq_witness(a, b) };
    assert(wit == a);
    assert(wit == b);
}
