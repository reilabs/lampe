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
    use crate::sort;
    use crate::sort_extended;
    use crate::sort_via;

    global arr_with_100_values: [u32; 100] = [
        42, 123, 87, 93, 48, 80, 50, 5, 104, 84, 70, 47, 119, 66, 71, 121, 3, 29, 42, 118, 2, 54,
        89, 44, 81, 0, 26, 106, 68, 96, 84, 48, 95, 54, 45, 32, 89, 100, 109, 19, 37, 41, 19, 98,
        53, 114, 107, 66, 6, 74, 13, 19, 105, 64, 123, 28, 44, 50, 89, 58, 123, 126, 21, 43, 86, 35,
        21, 62, 82, 0, 108, 120, 72, 72, 62, 80, 12, 71, 70, 86, 116, 73, 38, 15, 127, 81, 30, 8,
        125, 28, 26, 69, 114, 63, 27, 28, 61, 42, 13, 32,
    ];
    global expected_with_100_values: [u32; 100] = [
        0, 0, 2, 3, 5, 6, 8, 12, 13, 13, 15, 19, 19, 19, 21, 21, 26, 26, 27, 28, 28, 28, 29, 30, 32,
        32, 35, 37, 38, 41, 42, 42, 42, 43, 44, 44, 45, 47, 48, 48, 50, 50, 53, 54, 54, 58, 61, 62,
        62, 63, 64, 66, 66, 68, 69, 70, 70, 71, 71, 72, 72, 73, 74, 80, 80, 81, 81, 82, 84, 84, 86,
        86, 87, 89, 89, 89, 93, 95, 96, 98, 100, 104, 105, 106, 107, 108, 109, 114, 114, 116, 118,
        119, 120, 121, 123, 123, 123, 125, 126, 127,
    ];
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

    #[test]
    fn test_sort() {
        let mut arr: [u32; 7] = [3, 6, 8, 10, 1, 2, 1];

        let sorted = sort(arr);

        let expected: [u32; 7] = [1, 1, 2, 3, 6, 8, 10];
        assert(sorted == expected);
    }

    #[test]
    fn test_sort_100_values() {
        let mut arr: [u32; 100] = [
            42, 123, 87, 93, 48, 80, 50, 5, 104, 84, 70, 47, 119, 66, 71, 121, 3, 29, 42, 118, 2,
            54, 89, 44, 81, 0, 26, 106, 68, 96, 84, 48, 95, 54, 45, 32, 89, 100, 109, 19, 37, 41,
            19, 98, 53, 114, 107, 66, 6, 74, 13, 19, 105, 64, 123, 28, 44, 50, 89, 58, 123, 126, 21,
            43, 86, 35, 21, 62, 82, 0, 108, 120, 72, 72, 62, 80, 12, 71, 70, 86, 116, 73, 38, 15,
            127, 81, 30, 8, 125, 28, 26, 69, 114, 63, 27, 28, 61, 42, 13, 32,
        ];

        let sorted = sort(arr);

        let expected: [u32; 100] = [
            0, 0, 2, 3, 5, 6, 8, 12, 13, 13, 15, 19, 19, 19, 21, 21, 26, 26, 27, 28, 28, 28, 29, 30,
            32, 32, 35, 37, 38, 41, 42, 42, 42, 43, 44, 44, 45, 47, 48, 48, 50, 50, 53, 54, 54, 58,
            61, 62, 62, 63, 64, 66, 66, 68, 69, 70, 70, 71, 71, 72, 72, 73, 74, 80, 80, 81, 81, 82,
            84, 84, 86, 86, 87, 89, 89, 89, 93, 95, 96, 98, 100, 104, 105, 106, 107, 108, 109, 114,
            114, 116, 118, 119, 120, 121, 123, 123, 123, 125, 126, 127,
        ];
        assert(sorted == expected);
    }

    #[test]
    fn test_sort_100_values_comptime() {
        let sorted = sort(arr_with_100_values);
        assert(sorted == expected_with_100_values);
    }

    #[test]
    fn test_sort_via() {
        let mut arr: [u32; 7] = [3, 6, 8, 10, 1, 2, 1];

        let sorted = sort_via(arr, sort_u32);

        let expected: [u32; 7] = [1, 1, 2, 3, 6, 8, 10];
        assert(sorted == expected);
    }

    #[test]
    fn test_sort_via_100_values() {
        let mut arr: [u32; 100] = [
            42, 123, 87, 93, 48, 80, 50, 5, 104, 84, 70, 47, 119, 66, 71, 121, 3, 29, 42, 118, 2,
            54, 89, 44, 81, 0, 26, 106, 68, 96, 84, 48, 95, 54, 45, 32, 89, 100, 109, 19, 37, 41,
            19, 98, 53, 114, 107, 66, 6, 74, 13, 19, 105, 64, 123, 28, 44, 50, 89, 58, 123, 126, 21,
            43, 86, 35, 21, 62, 82, 0, 108, 120, 72, 72, 62, 80, 12, 71, 70, 86, 116, 73, 38, 15,
            127, 81, 30, 8, 125, 28, 26, 69, 114, 63, 27, 28, 61, 42, 13, 32,
        ];

        let sorted = sort_via(arr, sort_u32);

        let expected: [u32; 100] = [
            0, 0, 2, 3, 5, 6, 8, 12, 13, 13, 15, 19, 19, 19, 21, 21, 26, 26, 27, 28, 28, 28, 29, 30,
            32, 32, 35, 37, 38, 41, 42, 42, 42, 43, 44, 44, 45, 47, 48, 48, 50, 50, 53, 54, 54, 58,
            61, 62, 62, 63, 64, 66, 66, 68, 69, 70, 70, 71, 71, 72, 72, 73, 74, 80, 80, 81, 81, 82,
            84, 84, 86, 86, 87, 89, 89, 89, 93, 95, 96, 98, 100, 104, 105, 106, 107, 108, 109, 114,
            114, 116, 118, 119, 120, 121, 123, 123, 123, 125, 126, 127,
        ];
        assert(sorted == expected);
    }

    #[test]
    fn test_sort_extended() {
        let mut arr: [u32; 7] = [3, 6, 8, 10, 1, 2, 1];

        let sorted = sort_extended(arr, __sort_u32, unconditional_lt);

        let expected: [u32; 7] = [1, 1, 2, 3, 6, 8, 10];
        assert(sorted == expected);
    }
}
