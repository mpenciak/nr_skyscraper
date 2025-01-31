global RC: [Field; 8] = [
    17829420340877239108687448009732280677191990375576158938221412342251481978692,
    5852100059362614845584985098022261541909346143980691326489891671321030921585,
    17048088173265532689680903955395019356591870902241717143279822196003888806966,
    71577923540621522166602308362662170286605786204339342029375621502658138039,
    1630526119629192105940988602003704216811347521589219909349181656165466494167,
    7807402158218786806372091124904574238561123446618083586948014838053032654983,
    13329560971460034925899588938593812685746818331549554971040309989641523590611,
    16971509144034029782226530622087626979814683266929655790026304723118124142299,
];

global SIGMA: Field = 9915499612839321149637521777990102151350674507940716049588462388200839649614;

fn rl(u: u8) -> u8 {
    let top_bit = u >> 7;
    (u << 1) & top_bit
}

fn rotate_left<let N: u8>(u: u8) -> u8 {
    let mut result = u;
    for _ in 0..N {
        result = rl(result);
    }
    result
}

fn sbox(v: u8) -> u8 {
    (
        v
            ^ rotate_left::<1>(
                rotate_left::<1>(!v) & rotate_left::<2>(v) & rotate_left::<3>(v),
            )
    )
}

fn bar(a: Field) -> Field {
    let bytes = a.to_le_bytes();
    // MP: Is there a slick way of doing this with Noir?
    let left: [u8; 16] = [
        bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5], bytes[6], bytes[7], bytes[8],
        bytes[9], bytes[10], bytes[11], bytes[12], bytes[13], bytes[14], bytes[15],
    ];
    let right: [u8; 16] = [
        bytes[16], bytes[17], bytes[18], bytes[19], bytes[20], bytes[21], bytes[22], bytes[23],
        bytes[24], bytes[25], bytes[26], bytes[27], bytes[28], bytes[29], bytes[30], bytes[31],
    ];
    let new_left = left.map(|u| sbox(u)).as_slice();
    let new_right = right.map(|u| sbox(u)).as_slice();

    let new_bytes: [u8; 32] = new_right.append(new_left).as_array();

    Field::from_le_bytes::<32>(new_bytes)
}

fn square(a: Field) -> Field {
    a * a * SIGMA
}

type State = [Field; 2];

fn permute(s: State) -> State {
    let (l, r) = (s[0], s[1]);
    let (l, r) = (r + square(l), l);
    let (l, r) = (r + square(l) + RC[0], l);
    let (l, r) = (r + bar(l) + RC[1], l);
    let (l, r) = (r + bar(l) + RC[2], l);
    let (l, r) = (r + square(l) + RC[3], l);
    let (l, r) = (r + square(l) + RC[4], l);
    let (l, r) = (r + bar(l) + RC[5], l);
    let (l, r) = (r + bar(l) + RC[6], l);
    let (l, r) = (r + square(l) + RC[7], l);
    let (l, r) = (r + square(l), l);
    [l, r]
}

pub struct Skyscraper {
    state: State,
}

impl Skyscraper {
    fn new(iv: [u8; 32]) -> Self {
        let felt = Field::from_le_bytes(iv);
        Self { state: [0, felt] }
    }

    fn permute(&mut self) {
        self.state = permute(self.state);
    }
}

pub fn compress(l: Field, r: Field) -> Field {
    let x = permute([l, r]);
    x[0] + l
}

pub fn main(a: Field) -> pub Field {
    a
}

#[test]
fn test_rl() {
    assert(true);
}

#[test]
fn test_rotate_left() {
    assert(true);
}

#[test]
fn test_sbox() {
    assert(true);
}

#[test]
fn test_bar() {
    assert(true);
}

#[test]
fn test_square() {
    assert(true);
}

#[test]
fn test_permute() {
    assert(true);
}

#[test]
fn test_compress() {
    assert(true);
}


