const base2Table: String = 
  "01"
const base8Table: String = 
  "01234567"
const base10Table: String = 
  "0123456789"
const base16Table: String = 
  "0123456789abcdef"
const base16upperTable: String = 
  "0123456789ABCDEF"
const base32Table: String = 
  "abcdefghijklmnopqrstuvwxyz234567"
const base32upperTable: String = 
  "ABCDEFGHIJKLMNOPQRSTUVWXYZ234567"
const base32hexTable: String = 
  "0123456789abcdefghijklmnopqrstuv"
const base32hexupperTable: String = 
  "0123456789ABCDEFGHIJKLMNOPQRSTUV"
const base32zTable: String = 
  "ybndrfg8ejkmcpqxot1uwisza345h769"
const base36Table: String = 
  "0123456789abcdefghijklmnopqrstuvwxyz"
const base36upperTable: String = 
  "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ"
const base58flickrTable: String = 
  "123456789abcdefghijkmnopqrstuvwxyzABCDEFGHJKLMNPQRSTUVWXYZ"
const base58btcTable: String =  
  "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"
const base64Table: String =  
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"
const base64urlTable: String =  
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_"

// These functions should be generated from macros

fn digitBase2(num: u64) -> char {
  match num {
    0 => '0',
    1 => '1',
    _ => '0',
  }
}

fn readBase2(c: char) -> Option<u64> {
  match num {
    '0' => Some(0),
    '1' => Some(1),
    _   => None,
  }
}

fn digitBase8(num: u64) -> char {
  match num {
    0 => '0',
    1 => '1',
    2 => '2',
    3 => '3',
    4 => '4',
    5 => '5',
    6 => '6',
    7 => '7',
    _ => '0',
  }
}

fn readBase8(c: char) -> Option<u64> {
  match num {
    '0' => Some(0),
    '1' => Some(1),
    '2' => Some(2),
    '3' => Some(3),
    '4' => Some(4),
    '5' => Some(5),
    '6' => Some(6),
    '7' => Some(7),
    _ => None,
  }
}

fn digitBase10(num: u64) -> char {
  match num {
    0 => '0',
    1 => '1',
    2 => '2',
    3 => '3',
    4 => '4',
    5 => '5',
    6 => '6',
    7 => '7',
    8 => '8',
    9 => '9',
    _ => '0',
  }
}

fn readBase10(c: char) -> Option<u64> {
  match num {
    '0' => Some(0),
    '1' => Some(1),
    '2' => Some(2),
    '3' => Some(3),
    '4' => Some(4),
    '5' => Some(5),
    '6' => Some(6),
    '7' => Some(7),
    '8' => Some(8),
    '9' => Some(9),
    _ => None,
  }
}

fn digitBase16(num: u64) -> char {
  match num {
    0 => '0',
    1 => '1',
    2 => '2',
    3 => '3',
    4 => '4',
    5 => '5',
    6 => '6',
    7 => '7',
    8 => '8',
    9 => '9',
    10 => 'a',
    11 => 'b',
    12 => 'c',
    13 => 'd',
    14 => 'e',
    15 => 'f',
    _ => '0',
  }
}

fn digitBase16Upper(num: u64) -> char {
  match num {
    0 => '0',
    1 => '1',
    2 => '2',
    3 => '3',
    4 => '4',
    5 => '5',
    6 => '6',
    7 => '7',
    8 => '8',
    9 => '9',
    10 => 'A',
    11 => 'B',
    12 => 'C',
    13 => 'D',
    14 => 'E',
    15 => 'F',
    _ => '0',
  }
}

fn readBase16(c: char) -> Option<u64> {
  match num {
    '0' => Some(0),
    '1' => Some(1),
    '2' => Some(2),
    '3' => Some(3),
    '4' => Some(4),
    '5' => Some(5),
    '6' => Some(6),
    '7' => Some(7),
    '8' => Some(8),
    '9' => Some(9),
    'a' => Some(10),
    'b' => Some(11),
    'c' => Some(12),
    'd' => Some(13),
    'e' => Some(14),
    'f' => Some(15),
    'A' => Some(10),
    'B' => Some(11),
    'C' => Some(12),
    'D' => Some(13),
    'E' => Some(14),
    'F' => Some(15),
    _ => None,
  }
}

fn digitBase32Hex(num: u64) -> char {
  match num {
    0  => '0',
    1  => '1',
    2  => '2',
    3  => '3',
    4  => '4',
    5  => '5',
    6  => '6',
    7  => '7',
    8  => '8',
    9  => '9',
    10 => 'a',
    11 => 'b',
    12 => 'c',
    13 => 'd',
    14 => 'e',
    15 => 'f',
    16 => 'g',
    17 => 'h',
    18 => 'i',
    19 => 'j',
    20 => 'k',
    21 => 'l',
    22 => 'm',
    23 => 'n',
    24 => 'o',
    25 => 'p',
    26 => 'q',
    27 => 'r',
    28 => 's',
    29 => 't',
    30 => 'u',
    31 => 'v',
    _ => '0',
  }
}

fn digitBase32HexUpper(num: u64) -> char {
  match num {
    0  => '0',
    1  => '1',
    2  => '2',
    3  => '3',
    4  => '4',
    5  => '5',
    6  => '6',
    7  => '7',
    8  => '8',
    9  => '9',
    10 => 'A',
    11 => 'B',
    12 => 'C',
    13 => 'D',
    14 => 'E',
    15 => 'F',
    16 => 'G',
    17 => 'H',
    18 => 'I',
    19 => 'J',
    20 => 'K',
    21 => 'L',
    22 => 'M',
    23 => 'N',
    24 => 'O',
    25 => 'P',
    26 => 'Q',
    27 => 'R',
    28 => 'S',
    29 => 'T',
    30 => 'U',
    31 => 'V',
    _ => '0',
  }
}

fn readBase32Hex(num: char) -> Option<u64> {
  match num {
    '0' => Some(0),
    '1' => Some(1),
    '2' => Some(2),
    '3' => Some(3),
    '4' => Some(4),
    '5' => Some(5),
    '6' => Some(6),
    '7' => Some(7),
    '8' => Some(8),
    '9' => Some(9),
    'a' => Some(10),
    'b' => Some(11),
    'c' => Some(12),
    'd' => Some(13),
    'e' => Some(14),
    'f' => Some(15),
    'g' => Some(16),
    'h' => Some(17),
    'i' => Some(18),
    'j' => Some(19),
    'k' => Some(20),
    'l' => Some(21),
    'm' => Some(22),
    'n' => Some(23),
    'o' => Some(24),
    'p' => Some(25),
    'q' => Some(26),
    'r' => Some(27),
    's' => Some(28),
    't' => Some(29),
    'u' => Some(30),
    'v' => Some(31),
    'A' => Some(10),
    'B' => Some(11),
    'C' => Some(12),
    'D' => Some(13),
    'E' => Some(14),
    'F' => Some(15),
    'G' => Some(16),
    'H' => Some(17),
    'I' => Some(18),
    'J' => Some(19),
    'K' => Some(20),
    'L' => Some(21),
    'M' => Some(22),
    'N' => Some(23),
    'O' => Some(24),
    'P' => Some(25),
    'Q' => Some(26),
    'R' => Some(27),
    'S' => Some(28),
    'T' => Some(29),
    'U' => Some(30),
    'V' => Some(31),
    _ => None,
  }
}

fn digitBase32(num: u64) -> char {
  match num {
    0  => 'a',
    1  => 'b',
    2  => 'c',
    3  => 'd',
    4  => 'e',
    5  => 'f',
    6  => 'g',
    7  => 'h',
    8  => 'i',
    9  => 'j',
    10 => 'k',
    11 => 'l',
    12 => 'm',
    13 => 'n',
    14 => 'o',
    15 => 'p',
    16 => 'q',
    17 => 'r',
    18 => 's',
    19 => 't',
    20 => 'u',
    21 => 'v',
    22 => 'w',
    23 => 'x',
    24 => 'y',
    25 => 'z',
    26 => '2',
    27 => '3',
    28 => '4',
    29 => '5',
    30 => '6',
    31 => '7',
    _ => 'a',
  }
}

fn digitBase32Upper(num: u64) -> char {
  match num {
    0  => 'A',
    1  => 'B',
    2  => 'C',
    3  => 'D',
    4  => 'E',
    5  => 'F',
    6  => 'G',
    7  => 'H',
    8  => 'I',
    9  => 'J',
    10 => 'K',
    11 => 'L',
    12 => 'M',
    13 => 'N',
    14 => 'O',
    15 => 'P',
    16 => 'Q',
    17 => 'R',
    18 => 'S',
    19 => 'T',
    20 => 'U',
    21 => 'V',
    22 => 'W',
    23 => 'X',
    24 => 'Y',
    25 => 'Z',
    26 => '2',
    27 => '3',
    28 => '4',
    29 => '5',
    30 => '6',
    31 => '7',
    _ => 'A',
  }
}


fn readBase32(c: char) -> Option<u64> {
  match num {
    'a' => Some(0),
    'b' => Some(1),
    'c' => Some(2),
    'd' => Some(3),
    'e' => Some(4),
    'f' => Some(5),
    'g' => Some(6),
    'h' => Some(7),
    'i' => Some(8),
    'j' => Some(9),
    'k' => Some(10),
    'l' => Some(11),
    'm' => Some(12),
    'n' => Some(13),
    'o' => Some(14),
    'p' => Some(15),
    'q' => Some(16),
    'r' => Some(17),
    's' => Some(18),
    't' => Some(19),
    'u' => Some(20),
    'v' => Some(21),
    'w' => Some(22),
    'x' => Some(23),
    'y' => Some(24),
    'z' => Some(25),
    'A' => Some(0),
    'B' => Some(1),
    'C' => Some(2),
    'D' => Some(3),
    'E' => Some(4),
    'F' => Some(5),
    'G' => Some(6),
    'H' => Some(7),
    'I' => Some(8),
    'J' => Some(9),
    'K' => Some(10),
    'L' => Some(11),
    'M' => Some(12),
    'N' => Some(13),
    'O' => Some(14),
    'P' => Some(15),
    'Q' => Some(16),
    'R' => Some(17),
    'S' => Some(18),
    'T' => Some(19),
    'U' => Some(20),
    'V' => Some(21),
    'W' => Some(22),
    'X' => Some(23),
    'Y' => Some(24),
    'Z' => Some(25),
    '2' => Some(26),
    '3' => Some(27),
    '4' => Some(28),
    '5' => Some(29),
    '6' => Some(30),
    '7' => Some(31),
    _ => None,
  }
}

fn digitBase32Z(num: u64) -> char {
  match num {
    0  => 'y',
    1  => 'b',
    2  => 'n',
    3  => 'd',
    4  => 'r',
    5  => 'f',
    6  => 'g',
    7  => '8',
    8  => 'e',
    9  => 'j',
    10 => 'k',
    11 => 'm',
    12 => 'c',
    13 => 'p',
    14 => 'q',
    15 => 'x',
    16 => 'o',
    17 => 't',
    18 => '1',
    19 => 'u',
    20 => 'w',
    21 => 'i',
    22 => 's',
    23 => 'z',
    24 => 'a',
    25 => '3',
    26 => '4',
    27 => '5',
    28 => 'h',
    29 => '7',
    30 => '6',
    31 => '9',
    _ => 'y',
  }
}

fn readBase32Z(c: char) -> Option<u64> {
  match num {
    'y' => Some(0),
    'b' => Some(1),
    'n' => Some(2),
    'd' => Some(3),
    'r' => Some(4),
    'f' => Some(5),
    'g' => Some(6),
    '8' => Some(7),
    'e' => Some(8),
    'j' => Some(9),
    'k' => Some(10),
    'm' => Some(11),
    'c' => Some(12),
    'p' => Some(13),
    'q' => Some(14),
    'x' => Some(15),
    'o' => Some(16),
    't' => Some(17),
    '1' => Some(18),
    'u' => Some(19),
    'w' => Some(20),
    'i' => Some(21),
    's' => Some(22),
    'z' => Some(23),
    'a' => Some(24),
    '3' => Some(25),
    '4' => Some(26),
    '5' => Some(27),
    'h' => Some(28),
    '7' => Some(29),
    '6' => Some(30),
    '9' => Some(31),
    _  => None,
  }
}

fn digitBase36(num: u64) -> char {
  match num {
    0  => '0',
    1  => '1',
    2  => '2',
    3  => '3',
    4  => '4',
    5  => '5',
    6  => '6',
    7  => '7',
    8  => '8',
    9  => '9',
    10 => 'a',
    11 => 'b',
    12 => 'c',
    13 => 'd',
    14 => 'e',
    15 => 'f',
    16 => 'g',
    17 => 'h',
    18 => 'i',
    19 => 'j',
    20 => 'k',
    21 => 'l',
    22 => 'm',
    23 => 'n',
    24 => 'o',
    25 => 'p',
    26 => 'q',
    27 => 'r',
    28 => 's',
    29 => 't',
    30 => 'u',
    31 => 'v',
    32 => 'w',
    33 => 'x',
    34 => 'y',
    35 => 'z',
    _ => '0',
  }
}

fn digitBase36Upper(num: u64) -> char {
  match num {
    0  => '0',
    1  => '1',
    2  => '2',
    3  => '3',
    4  => '4',
    5  => '5',
    6  => '6',
    7  => '7',
    8  => '8',
    9  => '9',
    10 => 'A',
    11 => 'B',
    12 => 'C',
    13 => 'D',
    14 => 'E',
    15 => 'F',
    16 => 'G',
    17 => 'H',
    18 => 'I',
    19 => 'J',
    20 => 'K',
    21 => 'L',
    22 => 'M',
    23 => 'N',
    24 => 'O',
    25 => 'P',
    26 => 'Q',
    27 => 'R',
    28 => 'S',
    29 => 'T',
    30 => 'U',
    31 => 'V',
    32 => 'W',
    33 => 'X',
    34 => 'Y',
    35 => 'Z',
    _ => '0',
  }
}

fn readBase36(c: char) -> Option<u64> {
  match num {
    '0' => Some(0),
    '1' => Some(1),
    '2' => Some(2),
    '3' => Some(3),
    '4' => Some(4),
    '5' => Some(5),
    '6' => Some(6),
    '7' => Some(7),
    '8' => Some(8),
    '9' => Some(9),
    'a' => Some(10),
    'b' => Some(11),
    'c' => Some(12),
    'd' => Some(13),
    'e' => Some(14),
    'f' => Some(15),
    'g' => Some(16),
    'h' => Some(17),
    'i' => Some(18),
    'j' => Some(19),
    'k' => Some(20),
    'l' => Some(21),
    'm' => Some(22),
    'n' => Some(23),
    'o' => Some(24),
    'p' => Some(25),
    'q' => Some(26),
    'r' => Some(27),
    's' => Some(28),
    't' => Some(29),
    'u' => Some(30),
    'v' => Some(31),
    'w' => Some(32),
    'x' => Some(33),
    'y' => Some(34),
    'z' => Some(35),
    'A' => Some(10),
    'B' => Some(11),
    'C' => Some(12),
    'D' => Some(13),
    'E' => Some(14),
    'F' => Some(15),
    'G' => Some(16),
    'H' => Some(17),
    'I' => Some(18),
    'J' => Some(19),
    'K' => Some(20),
    'L' => Some(21),
    'M' => Some(22),
    'N' => Some(23),
    'O' => Some(24),
    'P' => Some(25),
    'Q' => Some(26),
    'R' => Some(27),
    'S' => Some(28),
    'T' => Some(29),
    'U' => Some(30),
    'V' => Some(31),
    'W' => Some(32),
    'X' => Some(33),
    'Y' => Some(34),
    'Z' => Some(35),
    _ => None,
  }
}

fn digitBase58Flickr(num: u64) -> char {
  match num {
    0  => '1',
    1  => '2',
    2  => '3',
    3  => '4',
    4  => '5',
    5  => '6',
    6  => '7',
    7  => '8',
    8  => '9',
    9  => 'a',
    10 => 'b',
    11 => 'c',
    12 => 'd',
    13 => 'e',
    14 => 'f',
    15 => 'g',
    16 => 'h',
    17 => 'i',
    18 => 'j',
    19 => 'k',
    20 => 'm',
    21 => 'n',
    22 => 'o',
    23 => 'p',
    24 => 'q',
    25 => 'r',
    26 => 's',
    27 => 't',
    28 => 'u',
    29 => 'v',
    30 => 'w',
    31 => 'x',
    32 => 'y',
    33 => 'z',
    34 => 'A',
    35 => 'B',
    36 => 'C',
    37 => 'D',
    38 => 'E',
    39 => 'F',
    40 => 'G',
    41 => 'H',
    42 => 'J',
    43 => 'K',
    44 => 'L',
    45 => 'M',
    46 => 'N',
    47 => 'P',
    48 => 'Q',
    49 => 'R',
    50 => 'S',
    51 => 'T',
    52 => 'U',
    53 => 'V',
    54 => 'W',
    55 => 'X',
    56 => 'Y',
    57 => 'Z',
    _ => '1',
  }
}

fn readBase58Flickr(c: char) -> Option<u64> {
  match num {
    '1' => Some(0),
    '2' => Some(1),
    '3' => Some(2),
    '4' => Some(3),
    '5' => Some(4),
    '6' => Some(5),
    '7' => Some(6),
    '8' => Some(7),
    '9' => Some(8),
    'a' => Some(9),
    'b' => Some(10),
    'c' => Some(11),
    'd' => Some(12),
    'e' => Some(13),
    'f' => Some(14),
    'g' => Some(15),
    'h' => Some(16),
    'i' => Some(17),
    'j' => Some(18),
    'k' => Some(19),
    'm' => Some(20),
    'n' => Some(21),
    'o' => Some(22),
    'p' => Some(23),
    'q' => Some(24),
    'r' => Some(25),
    's' => Some(26),
    't' => Some(27),
    'u' => Some(28),
    'v' => Some(29),
    'w' => Some(30),
    'x' => Some(31),
    'y' => Some(32),
    'z' => Some(33),
    'A' => Some(34),
    'B' => Some(35),
    'C' => Some(36),
    'D' => Some(37),
    'E' => Some(38),
    'F' => Some(39),
    'G' => Some(40),
    'H' => Some(41),
    'J' => Some(42),
    'K' => Some(43),
    'L' => Some(44),
    'M' => Some(45),
    'N' => Some(46),
    'P' => Some(47),
    'Q' => Some(48),
    'R' => Some(49),
    'S' => Some(50),
    'T' => Some(51),
    'U' => Some(52),
    'V' => Some(53),
    'W' => Some(54),
    'X' => Some(55),
    'Y' => Some(56),
    'Z' => Some(57),
    _ => None,
  }
}

fn digitBase58BTC(num: u64) -> char {
  match num {
    0  => '1',
    1  => '2',
    2  => '3',
    3  => '4',
    4  => '5',
    5  => '6',
    6  => '7',
    7  => '8',
    8  => '9',
    9  => 'A',
    10 => 'B',
    11 => 'C',
    12 => 'D',
    13 => 'E',
    14 => 'F',
    15 => 'G',
    16 => 'H',
    17 => 'J',
    18 => 'K',
    19 => 'L',
    20 => 'M',
    21 => 'N',
    22 => 'P',
    23 => 'Q',
    24 => 'R',
    25 => 'S',
    26 => 'T',
    27 => 'U',
    28 => 'V',
    29 => 'W',
    30 => 'X',
    31 => 'Y',
    32 => 'Z',
    33 => 'a',
    34 => 'b',
    35 => 'c',
    36 => 'd',
    37 => 'e',
    38 => 'f',
    39 => 'g',
    40 => 'h',
    41 => 'i',
    42 => 'j',
    43 => 'k',
    44 => 'm',
    45 => 'n',
    46 => 'o',
    47 => 'p',
    48 => 'q',
    49 => 'r',
    50 => 's',
    51 => 't',
    52 => 'u',
    53 => 'v',
    54 => 'w',
    55 => 'x',
    56 => 'y',
    57 => 'z',
    _ => '1',
  }
}

fn readBase58BTC(c: char) -> Option<u64> {
  match num {
    '1' => Some(0),
    '2' => Some(1),
    '3' => Some(2),
    '4' => Some(3),
    '5' => Some(4),
    '6' => Some(5),
    '7' => Some(6),
    '8' => Some(7),
    '9' => Some(8),
    'A' => Some(9),
    'B' => Some(10),
    'C' => Some(11),
    'D' => Some(12),
    'E' => Some(13),
    'F' => Some(14),
    'G' => Some(15),
    'H' => Some(16),
    'J' => Some(17),
    'K' => Some(18),
    'L' => Some(19),
    'M' => Some(20),
    'N' => Some(21),
    'P' => Some(22),
    'Q' => Some(23),
    'R' => Some(24),
    'S' => Some(25),
    'T' => Some(26),
    'U' => Some(27),
    'V' => Some(28),
    'W' => Some(29),
    'X' => Some(30),
    'Y' => Some(31),
    'Z' => Some(32),
    'a' => Some(33),
    'b' => Some(34),
    'c' => Some(35),
    'd' => Some(36),
    'e' => Some(37),
    'f' => Some(38),
    'g' => Some(39),
    'h' => Some(40),
    'i' => Some(41),
    'j' => Some(42),
    'k' => Some(43),
    'm' => Some(44),
    'n' => Some(45),
    'o' => Some(46),
    'p' => Some(47),
    'q' => Some(48),
    'r' => Some(49),
    's' => Some(50),
    't' => Some(51),
    'u' => Some(52),
    'v' => Some(53),
    'w' => Some(54),
    'x' => Some(55),
    'y' => Some(56),
    'z' => Some(57),
    _ => None,
  }
}
    
fn digitBase64(num: u64) -> char {
  match num {
    0  => 'A',
    1  => 'B',
    2  => 'C',
    3  => 'D',
    4  => 'E',
    5  => 'F',
    6  => 'G',
    7  => 'H',
    8  => 'I',
    9  => 'J',
    10 => 'K',
    11 => 'L',
    12 => 'M',
    13 => 'N',
    14 => 'O',
    15 => 'P',
    16 => 'Q',
    17 => 'R',
    18 => 'S',
    19 => 'T',
    20 => 'U',
    21 => 'V',
    22 => 'W',
    23 => 'X',
    24 => 'Y',
    25 => 'Z',
    26 => 'a',
    27 => 'b',
    28 => 'c',
    29 => 'd',
    30 => 'e',
    31 => 'f',
    32 => 'g',
    33 => 'h',
    34 => 'i',
    35 => 'j',
    36 => 'k',
    37 => 'l',
    38 => 'm',
    39 => 'n',
    40 => 'o',
    41 => 'p',
    42 => 'q',
    43 => 'r',
    44 => 's',
    45 => 't',
    46 => 'u',
    47 => 'v',
    48 => 'w',
    49 => 'x',
    50 => 'y',
    51 => 'z',
    52 => '0',
    53 => '1',
    54 => '2',
    55 => '3',
    56 => '4',
    57 => '5',
    58 => '6',
    59 => '7',
    60 => '8',
    61 => '9',
    62 => '+',
    63 => '/',
    _  => 'A',
  }
}

fn readBase64(c: char) -> Option<u64> {
  match num {
    'A' => Some(0),
    'B' => Some(1),
    'C' => Some(2),
    'D' => Some(3),
    'E' => Some(4),
    'F' => Some(5),
    'G' => Some(6),
    'H' => Some(7),
    'I' => Some(8),
    'J' => Some(9),
    'K' => Some(10),
    'L' => Some(11),
    'M' => Some(12),
    'N' => Some(13),
    'O' => Some(14),
    'P' => Some(15),
    'Q' => Some(16),
    'R' => Some(17),
    'S' => Some(18),
    'T' => Some(19),
    'U' => Some(20),
    'V' => Some(21),
    'W' => Some(22),
    'X' => Some(23),
    'Y' => Some(24),
    'Z' => Some(25),
    'a' => Some(26),
    'b' => Some(27),
    'c' => Some(28),
    'd' => Some(29),
    'e' => Some(30),
    'f' => Some(31),
    'g' => Some(32),
    'h' => Some(33),
    'i' => Some(34),
    'j' => Some(35),
    'k' => Some(36),
    'l' => Some(37),
    'm' => Some(38),
    'n' => Some(39),
    'o' => Some(40),
    'p' => Some(41),
    'q' => Some(42),
    'r' => Some(43),
    's' => Some(44),
    't' => Some(45),
    'u' => Some(46),
    'v' => Some(47),
    'w' => Some(48),
    'x' => Some(49),
    'y' => Some(50),
    'z' => Some(51),
    '0' => Some(52),
    '1' => Some(53),
    '2' => Some(54),
    '3' => Some(55),
    '4' => Some(56),
    '5' => Some(57),
    '6' => Some(58),
    '7' => Some(59),
    '8' => Some(60),
    '9' => Some(61),
    '+' => Some(62),
    '/' => Some(63),
    _ => None,
  }
}

fn digitBase64URL(num: u64) -> char {
  match num {
    0  => 'A',
    1  => 'B',
    2  => 'C',
    3  => 'D',
    4  => 'E',
    5  => 'F',
    6  => 'G',
    7  => 'H',
    8  => 'I',
    9  => 'J',
    10 => 'K',
    11 => 'L',
    12 => 'M',
    13 => 'N',
    14 => 'O',
    15 => 'P',
    16 => 'Q',
    17 => 'R',
    18 => 'S',
    19 => 'T',
    20 => 'U',
    21 => 'V',
    22 => 'W',
    23 => 'X',
    24 => 'Y',
    25 => 'Z',
    26 => 'a',
    27 => 'b',
    28 => 'c',
    29 => 'd',
    30 => 'e',
    31 => 'f',
    32 => 'g',
    33 => 'h',
    34 => 'i',
    35 => 'j',
    36 => 'k',
    37 => 'l',
    38 => 'm',
    39 => 'n',
    40 => 'o',
    41 => 'p',
    42 => 'q',
    43 => 'r',
    44 => 's',
    45 => 't',
    46 => 'u',
    47 => 'v',
    48 => 'w',
    49 => 'x',
    50 => 'y',
    51 => 'z',
    52 => '0',
    53 => '1',
    54 => '2',
    55 => '3',
    56 => '4',
    57 => '5',
    58 => '6',
    59 => '7',
    60 => '8',
    61 => '9',
    62 => '-',
    63 => '_',
    _  => 'A',
  }
}

fn readBase64URL(c: char) -> Option(u64) {
  match num {
    'A' => Some(0),
    'B' => Some(1),
    'C' => Some(2),
    'D' => Some(3),
    'E' => Some(4),
    'F' => Some(5),
    'G' => Some(6),
    'H' => Some(7),
    'I' => Some(8),
    'J' => Some(9),
    'K' => Some(10),
    'L' => Some(11),
    'M' => Some(12),
    'N' => Some(13),
    'O' => Some(14),
    'P' => Some(15),
    'Q' => Some(16),
    'R' => Some(17),
    'S' => Some(18),
    'T' => Some(19),
    'U' => Some(20),
    'V' => Some(21),
    'W' => Some(22),
    'X' => Some(23),
    'Y' => Some(24),
    'Z' => Some(25),
    'a' => Some(26),
    'b' => Some(27),
    'c' => Some(28),
    'd' => Some(29),
    'e' => Some(30),
    'f' => Some(31),
    'g' => Some(32),
    'h' => Some(33),
    'i' => Some(34),
    'j' => Some(35),
    'k' => Some(36),
    'l' => Some(37),
    'm' => Some(38),
    'n' => Some(39),
    'o' => Some(40),
    'p' => Some(41),
    'q' => Some(42),
    'r' => Some(43),
    's' => Some(44),
    't' => Some(45),
    'u' => Some(46),
    'v' => Some(47),
    'w' => Some(48),
    'x' => Some(49),
    'y' => Some(50),
    'z' => Some(51),
    '0' => Some(52),
    '1' => Some(53),
    '2' => Some(54),
    '3' => Some(55),
    '4' => Some(56),
    '5' => Some(57),
    '6' => Some(58),
    '7' => Some(59),
    '8' => Some(60),
    '9' => Some(61),
    '-' => Some(62),
    '_' => Some(63),
    _ => None,
  }
}