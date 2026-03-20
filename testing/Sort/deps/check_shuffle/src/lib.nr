unconstrained fn __get_shuffle_indices<T, let N: u32>(lhs: [T; N], rhs: [T; N]) -> [u32; N]
where
    T: std::cmp::Eq,
{
    let mut shuffle_indices: [u32; N] = [0; N];

    let mut shuffle_mask: [bool; N] = [false; N];
    for i in 0..N {
        let mut found = false;
        for j in 0..N {
            if ((shuffle_mask[j] == false) & (!found)) {
                if (lhs[i] == rhs[j]) {
                    found = true;
                    shuffle_indices[i] = j;
                    shuffle_mask[j] = true;
                }
            }
            if (found) {
                continue;
            }
        }
        assert(found == true, "check_shuffle, lhs and rhs arrays do not contain equivalent values");
    }

    shuffle_indices
}

unconstrained fn __get_index<let N: u32>(indices: [u32; N], idx: u32) -> u32 {
    let mut result = 0;
    for i in 0..N {
        if (indices[i] == idx) {
            result = i;
            break;
        }
    }
    result
}

pub fn check_shuffle<T, let N: u32>(lhs: [T; N], rhs: [T; N])
where
    T: std::cmp::Eq,
{
    //@Safety: check the comments below
    let shuffle_indices = unsafe { __get_shuffle_indices(lhs, rhs) };

    for i in 0..N {
        let idx = unsafe { __get_index(shuffle_indices, i) };
        // checks the relation between shuffle_indices and output of __get_index
        assert_eq(shuffle_indices[idx], i);
    }
    for i in 0..N {
        let idx = shuffle_indices[i];
        let expected = rhs[idx];
        let result = lhs[i];
        // checks the relation between shuffle_indices and the lhs, rhs inputs
        assert_eq(expected, result);
    }
}

pub fn get_shuffle_indices<T, let N: u32>(lhs: [T; N], rhs: [T; N]) -> [u32; N]
where
    T: std::cmp::Eq,
{
    //@Safety: as explained in check_shuffle function
    let shuffle_indices = unsafe { __get_shuffle_indices(lhs, rhs) };
    for i in 0..N {
        let idx = unsafe { __get_index(shuffle_indices, i) };
        assert_eq(shuffle_indices[idx], i);
    }
    for i in 0..N {
        let idx = shuffle_indices[i];
        let expected = rhs[idx];
        let result = lhs[i];
        assert_eq(expected, result);
    }
    shuffle_indices
}

mod test {
    struct CompoundStruct {
        a: bool,
        b: Field,
        c: u64,
    }
    impl std::cmp::Eq for CompoundStruct {
        fn eq(self, other: Self) -> bool {
            (self.a == other.a) & (self.b == other.b) & (self.c == other.c)
        }
    }

    use crate::check_shuffle;
    #[test]
    fn test_shuffle() {
        let lhs: [Field; 5] = [0, 1, 2, 3, 4];
        let rhs: [Field; 5] = [2, 0, 3, 1, 4];
        check_shuffle(lhs, rhs);
    }

    #[test]
    fn test_shuffle_identity() {
        let lhs: [Field; 5] = [0, 1, 2, 3, 4];
        let rhs: [Field; 5] = [0, 1, 2, 3, 4];
        check_shuffle(lhs, rhs);
    }

    #[test(should_fail_with = "check_shuffle, lhs and rhs arrays do not contain equivalent values")]
    fn test_shuffle_fail() {
        let lhs: [Field; 5] = [0, 1, 2, 3, 4];
        let rhs: [Field; 5] = [0, 1, 2, 3, 5];
        check_shuffle(lhs, rhs);
    }

    #[test(should_fail_with = "check_shuffle, lhs and rhs arrays do not contain equivalent values")]
    fn test_shuffle_duplicates() {
        let lhs: [Field; 5] = [0, 1, 2, 3, 4];
        let rhs: [Field; 5] = [0, 1, 2, 3, 3];
        check_shuffle(lhs, rhs);
    }

    #[test]
    fn test_shuffle_compound_struct() {
        let lhs: [CompoundStruct; 5] = [
            CompoundStruct { a: false, b: 0, c: 12345 },
            CompoundStruct { a: false, b: -100, c: 54321 },
            CompoundStruct { a: true, b: 5, c: 0xffffffffffffffff },
            CompoundStruct { a: true, b: 9814, c: 0xeeffee0011001133 },
            CompoundStruct { a: false, b: 0x155, c: 0 },
        ];
        let rhs: [CompoundStruct; 5] = [
            CompoundStruct { a: false, b: 0x155, c: 0 },
            CompoundStruct { a: false, b: 0, c: 12345 },
            CompoundStruct { a: false, b: -100, c: 54321 },
            CompoundStruct { a: true, b: 9814, c: 0xeeffee0011001133 },
            CompoundStruct { a: true, b: 5, c: 0xffffffffffffffff },
        ];
        check_shuffle(lhs, rhs);
    }
}

mod benchmark {
    use crate::check_shuffle;
    #[export]
    fn bench_shuffle(lhs: [Field; 5], rhs: [Field; 5]) {
        check_shuffle(lhs, rhs);
    }
}
