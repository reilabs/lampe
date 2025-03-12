use crate::{bar, compress, permute, rl, rotate_left, sbox, SIGMA, square};

#[test]
fn test_rl() {
    assert_eq(rl(1), 2);
    assert_eq(rl(170), 85);
    assert_eq(rl(85), 170);
    assert_eq(rl(128), 1);
}

#[test]
fn test_rotate_left() {
    assert_eq(rotate_left(1, 1), 2);
    assert_eq(rotate_left(1, 2), 4);
    assert_eq(rotate_left(85, 2), 85);
    assert_eq(rotate_left(144, 5), 18);
}

#[test]
fn test_sbox() {
    assert_eq(sbox(34), 34);
    assert_eq(sbox(19), 3);
    assert_eq(sbox(254), 250);
    assert_eq(sbox(219), 75);
}

#[test]
fn test_bar() {
    assert_eq(bar(0), 0);
    assert_eq(bar(34), 11569600475311907757754736652680119189504);
    assert_eq(bar(123456789), 227189284417390087395336095752969451572618592256);
    assert_eq(bar(10066193), 380599362036098173552978694294891540917518336);
}

#[test]
fn test_square() {
    assert_eq(square(1), SIGMA);
    assert_eq(square(0), 0);
    assert_eq(square(17), 289 * SIGMA);
    assert_eq(
        square(123456789),
        8942935588434003749808093666007174270110007839183014576630749919696542333842,
    );
}

#[test]
fn test_permute() {
    assert_eq(
        permute([0, 0]),
        [
            4917414381541712472046478074478919031714240661792445462937012286213950773535,
            4379833446663089036544422104237712138698562758431049307252304943265001524837,
        ],
    );
    assert_eq(
        permute([39, 103]),
        [
            6899527471890563794256702102712795090036753313277466831073492498514009367466,
            14228486150082268264521380519565659428999584206683517340774310237779763178333,
        ],
    );
}

#[test]
fn test_compress() {
    assert_eq(
        compress(59, 63),
        1371215436639737956096583003039945495199328362545687675803593078153452178251,
    );

    assert_eq(
        compress(0xfffffffffffffffffff, 0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb),
        18507154490486557774337134565359308231878883333573331619242076812280103649854,
    );
}

