global FOOS: [Field; 2] = [FOO, FOO + 1];

global FOO: Field  = 42;

fn main() -> pub Field {
    FOOS[1]
}
