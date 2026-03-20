pub mod quicksort;
use crate::quicksort::quicksort::quicksort as quicksort;
use crate::quicksort::quicksort_explicit::quicksort as quicksort_explicit;
use dep::check_shuffle::{check_shuffle, get_shuffle_indices};

/**
 * Given an input array of type T, return a sorted array.
 * Type `T` must satisfy the Ord and Eq trait
 * The Eq function is used within an unconstrained function so its constraint-efficiently is not relevant
 * Note: sort_extended is likely more efficient as constraining `x < y` can typically be described
 *       more efficiently than returning a boolean that describes whether `x < y`
 **/
pub fn sort<T, let N: u32>(input: [T; N]) -> [T; N]
where
    T: std::cmp::Ord + std::cmp::Eq,
{
    // Safety: validated using check_shuffle. See its documentation for more info.
    let sorted = unsafe { quicksort(input) };

    for i in 0..N - 1 {
        assert(sorted[i] <= sorted[i + 1]);
    }
    check_shuffle(input, sorted);
    sorted
}

/**
 * Given an input array of type T, return a sorted array.
 * Type `T` must satisfy the Eq trait
 * The Eq function is used within an unconstrained function so its constraint-efficiently is not relevant
 *
 * The `sortfn` parameter is a function that descibes whether, given two elements `a, b` of type T, `a <= b`
 * Note: sort_extended is likely more efficient as constraining `x < y` can typically be described
 *       more efficiently than returning a boolean that describes whether `x < y`
 **/
pub fn sort_via<T, let N: u32>(input: [T; N], sortfn: fn(T, T) -> bool) -> [T; N]
where
    T: std::cmp::Eq,
{
    // Safety: validated using check_shuffle. See its documentation for more info.
    let sorted = unsafe { quicksort_explicit(input, sortfn) };

    for i in 0..N - 1 {
        assert(sortfn(sorted[i], sorted[i + 1]));
    }
    check_shuffle(input, sorted);
    sorted
}

/**
 * Given an input array of type T, return a sorted array.
 * Type `T` must satisfy the Eq trait
 * The Eq function is used within an unconstrained function so its constraint-efficiently is not relevant
 *
 * The `sortfn` parameter is a function that descibes whether, given two elements `a, b` of type T, `a <= b`
 * The `sortfn_assert` parameter is a function that *asserts* that `a <= b`
 *
 * `sortfn` is used in unconstrained functions only
 * `sortfn_assert` is used in constrained functions

 * Note: This is likely the most efficient sort function as constraining `x < y` can typically be described
 *       more efficiently than returning a boolean that describes whether `x < y`
 **/
pub fn sort_extended<T, let N: u32>(
    input: [T; N],
    sortfn: unconstrained fn(T, T) -> bool,
    sortfn_assert: fn(T, T) -> (),
) -> [T; N]
where
    T: std::cmp::Eq,
{
    // Safety: validated using check_shuffle. See its documentation for more info.
    let sorted = unsafe { quicksort_explicit(input, sortfn) };

    for i in 0..N - 1 {
        sortfn_assert(sorted[i], sorted[i + 1]);
    }
    check_shuffle(input, sorted);
    sorted
}

pub struct SortResult<T, let N: u32> {
    pub sorted: [T; N],
    pub sort_indices: [u32; N],
}

pub fn sort_advanced<T, let N: u32>(
    input: [T; N],
    sortfn: unconstrained fn(T, T) -> bool,
    sortfn_assert: fn(T, T) -> (),
) -> SortResult<T, N>
where
    T: std::cmp::Eq,
{
    // Safety: validated using check_shuffle. See its documentation for more info.
    let sorted = unsafe { quicksort_explicit(input, sortfn) };

    let sort_indices = get_shuffle_indices(input, sorted);

    for i in 0..N - 1 {
        sortfn_assert(sorted[i], sorted[i + 1]);
    }
    SortResult { sorted, sort_indices }
}

mod test {
    fn sort_u32(a: u32, b: u32) -> bool {
        a <= b
    }

    unconstrained fn __sort_u32(a: u32, b: u32) -> bool {
        a <= b
    }

    // unconditional_lt will cost fewer constraints than the `<=` operator
    // as we do not need to constrain the case where `a > b`, and assign a boolean variable to the result
    fn unconditional_lt(_a: u32, _b: u32) {
        let a = _a as Field;
        let b = _b as Field;

        let diff = b - a;
        diff.assert_max_bit_size::<32>();
    }
}
