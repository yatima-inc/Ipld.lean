import Ipld.Utils
import Ipld.Multibase.Impl

/-- An instance of the Multibase specification for a given base `β` -/
class Multibase (β: Type) where
  code      : Char
  alpha     : String
  digit     : Nat → Char
  read      : Char → Option Nat
  rfc4648   : Bool
  pad       : Bool

namespace Multibase
  -- We define associated functions derived from the class in the same namespace
  -- Ideally there would be a way to make `β` implicit and inferrable
  variable (β: Type)
  def zero [Multibase β]: Char := (alpha β)[0]
  def base [Multibase β]: Nat  := (alpha β).length
  def log2Base [Multibase β]: Nat  := Nat.log2' (base β)

  -- This computes the least-common-multiple of the (log2 base) and 8, in order
  -- for us to determine the minimal number of padding bits to add in rfc4648
  def lcm8 [Multibase β] : Nat :=
    let x := (log2Base β)
    if x % 8 == 0 then x else
    if x % 4 == 0 then x * 2 else
    if x % 2 == 0 then x * 4 else
    x * 8

  -- This is a little slow. We gain some in-kernel performance by
  -- requiring Multibase instances to hardcode a `digit` function, even though
  -- semantically it's derivable from `alpha`
  def digit' [Multibase β] (i : Nat): Char :=
    if i >= (alpha β).length then zero β else String.get (alpha β) i

  -- This is very slow because of the String.posOf call. We can't reduce
  -- encodings in-kernel unless we hardcode the `read` function in the instance
  def read' [Multibase β] (c: Char): Option Nat :=
   let x := String.posOf (alpha β) c
   if x == (alpha β).length then Option.none else Option.some x

  def validDigit [Multibase β] (x: Char): Bool := (read β x) != Option.none
  def validate [Multibase β] (x: String): Bool := List.all x.data (validDigit β)

  def toStringCore [Multibase β]: Nat → Nat → String → String
  | 0, n, str => str
  | fuel+1, 0, str => str
  | fuel+1, n, str =>
    let dig := (digit β (n % (base β)))
    toStringCore fuel (n / (base β)) (String.append (String.singleton dig) str)

  def toString [m: Multibase β]: Nat → String
  | 0 => String.singleton (alpha β)[0]
  | n => toStringCore β (n+1) n ""

  def padRight (input: String) : Nat → String
  | 0 => input
  | n+1 => padRight (String.push input '=') n

  def encode [Multibase β] (x: ByteArray): String :=
    let lzs := ByteArray.leadingZeroBits x
    let log := Multibase.log2Base β
    let left := String.mk (List.replicate (lzs / log) '0')
    let rfc := Multibase.rfc4648 β
    let lcm := Multibase.lcm8 β / 8
    let rfcbytes := (lcm - x.size % lcm) % lcm
    let x := if rfc then ByteArray.pushZeros x rfcbytes else x
    let n := Nat.fromByteArrayBE x
    let str := (Multibase.toStringCore β (n+1) n "")
    let rfcchars := ((rfcbytes * 8) / log)
    let str' := if rfc then str.dropRight rfcchars else str
    let str' := if rfc && Multibase.pad β
      then Multibase.padRight str' rfcchars else str'
    String.singleton (Multibase.code β) ++ left ++ str'

  def fromStringCore [Multibase β]: Nat → Nat → String → Option Nat
  | 0, acc, input => Option.some acc
  | fuel+1, acc, "" => Option.some acc
  | fuel+1, acc, input => do
  let dig := (read β input[0])
  Option.bind dig (fun d =>
    fromStringCore fuel (acc * (base β) + d) (String.drop input 1))

  def fromString [m: Multibase β]: String -> Option Nat
  | "" => Option.none
  | s => fromStringCore β (s.length) 0 s

end Multibase

structure Base2
structure Base8
structure Base10
structure Base16
structure Base16Upper
structure Base32Hex
structure Base32HexUpper
structure Base32HexPad
structure Base32HexPadUpper
structure Base32
structure Base32Upper
structure Base32Pad
structure Base32PadUpper
structure Base32Z
structure Base36
structure Base36Upper
structure Base58BTC
structure Base58Flickr
structure Base64
structure Base64Pad
structure Base64URL
structure Base64URLPad

instance : Multibase Base2 where
  code := '0'
  alpha := "01"
  digit := digitBase2
  read := readBase2
  rfc4648 := false
  pad := false

instance : Multibase Base8 where
  code := '7'
  alpha: String := "01234567"
  digit := digitBase8
  read := readBase8
  rfc4648 := true
  pad := false

instance : Multibase Base10 where
  code := '9'
  alpha: String := "0123456789"
  digit := digitBase10
  read := readBase10
  rfc4648 := false
  pad := false

instance : Multibase Base16 where
  code := 'f'
  alpha: String := "0123456789abcdef"
  digit := digitBase16
  read := readBase16
  rfc4648 := false
  pad := false

instance : Multibase Base16Upper where
  code := 'F'
  alpha: String := "0123456789ABCDEF"
  digit := digitBase16Upper
  read := readBase16
  rfc4648 := false
  pad := false

instance : Multibase Base32Hex where
  code := 'v'
  alpha: String := "0123456789abcdefghijklmnopqrstuv"
  digit := digitBase32Hex
  read := readBase32Hex
  rfc4648 := true
  pad := false

instance : Multibase Base32HexUpper where
  code := 'V'
  alpha: String := "0123456789ABCDEFGHIJKLMNOPQRSTUV"
  digit := digitBase32HexUpper
  read := readBase32Hex
  rfc4648 := true
  pad := false

instance : Multibase Base32HexPad where
  code := 't'
  alpha: String := "0123456789abcdefghijklmnopqrstuv"
  digit := digitBase32Hex
  read := readBase32Hex
  rfc4648 := true
  pad := true

instance : Multibase Base32HexPadUpper where
  code := 'T'
  alpha: String := "0123456789ABCDEFGHIJKLMNOPQRSTUV"
  digit := digitBase32HexUpper
  read := readBase32Hex
  rfc4648 := true
  pad := true

instance : Multibase Base32 where
  code := 'b'
  alpha: String := "abcdefghijklmnopqrstuvwxyz234567"
  digit := digitBase32
  read := readBase32
  rfc4648 := true
  pad := false

instance : Multibase Base32Upper where
  code := 'B'
  alpha: String := "ABCDEFGHIJKLMNOPQRSTUVWXYZ234567"
  digit := digitBase32Upper
  read := readBase32
  rfc4648 := true
  pad := false

instance : Multibase Base32Pad where
  code := 'c'
  alpha: String := "abcdefghijklmnopqrstuvwxyz234567"
  digit := digitBase32
  read := readBase32
  rfc4648 := true
  pad := true

instance : Multibase Base32PadUpper where
  code := 'C'
  alpha: String := "ABCDEFGHIJKLMNOPQRSTUVWXYZ234567"
  digit := digitBase32Upper
  read := readBase32
  rfc4648 := true
  pad := true

instance : Multibase Base32Z where
  code := 'h'
  alpha: String := "ybndrfg8ejkmcpqxot1uwisza345h769"
  digit := digitBase32Z
  read := readBase32Z
  rfc4648 := false
  pad := false

instance : Multibase Base36 where
  code := 'k'
  alpha: String := "0123456789abcdefghijklmnopqrstuvwxyz"
  digit := digitBase36
  read := readBase36
  rfc4648 := false
  pad := false

instance : Multibase Base36Upper where
  code := 'K'
  alpha: String := "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ"
  digit := digitBase36Upper
  read := readBase36
  rfc4648 := false
  pad := false

instance : Multibase Base58Flickr where
  code := 'Z'
  alpha: String := 
    "123456789abcdefghijkmnopqrstuvwxyzABCDEFGHJKLMNPQRSTUVWXYZ"
  digit := digitBase58Flickr
  read := readBase58Flickr
  rfc4648 := false
  pad := false

instance : Multibase Base58BTC where
  code := 'z'
  alpha: String := 
    "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"
  digit := digitBase58BTC
  read := readBase58BTC
  rfc4648 := false
  pad := false

instance : Multibase Base64 where
  code := 'm'
  alpha: String := 
    "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"
  digit := digitBase64
  read := readBase64
  rfc4648 := true
  pad := false

instance : Multibase Base64Pad where
  code := 'M'
  alpha: String := 
    "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"
  digit := digitBase64
  read := readBase64
  rfc4648 := true
  pad := true

instance : Multibase Base64URL where
  code := 'u'
  alpha: String := 
    "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_"
  digit := digitBase64URL
  read := readBase64URL
  rfc4648 := true
  pad := false

instance : Multibase Base64URLPad where
  code := 'U'
  alpha: String := 
    "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_"
  digit := digitBase64URL
  read := readBase64URL
  rfc4648 := true
  pad := true

namespace Test
  open Multibase
  #eval fromString Base8 (toString Base8 1)

  #check (rfl : fromString Base8 (toString Base8 1) = some 1)
  #check (rfl : fromString Base2 (toString Base2 1) = some 1)
  #check (rfl : fromString Base10 (toString Base10 35) = some 35)
  #check (rfl : toString Base10 <$> (fromString Base10 "35") = some "35")

  -- basic.csv
  #eval "yes mani !".toUTF8
  def basic := ByteArray.mk #[121, 101, 115, 32, 109, 97, 110, 105, 32, 33]
  set_option maxRecDepth 1000
  #check (rfl : (encode Base2             basic) = 
    "001111001011001010111001100100000011011010110000101101110011010010010000000100001")
  #check (rfl : (encode Base8             basic) = "7362625631006654133464440102")
  #check (rfl : (encode Base10            basic) = "9573277761329450583662625")
  #check (rfl : (encode Base16            basic) = "f796573206d616e692021")
  #check (rfl : (encode Base16Upper       basic) = "F796573206D616E692021")
  #check (rfl : (encode Base32Hex         basic) = "vf5in683dc5n6i811")
  #check (rfl : (encode Base32HexUpper    basic) = "VF5IN683DC5N6I811")
  #check (rfl : (encode Base32HexPad      basic) = "tf5in683dc5n6i811")
  #check (rfl : (encode Base32HexPadUpper basic) = "TF5IN683DC5N6I811")
  #check (rfl : (encode Base32            basic) = "bpfsxgidnmfxgsibb")
  #check (rfl : (encode Base32Upper       basic) = "BPFSXGIDNMFXGSIBB")
  #check (rfl : (encode Base32Pad         basic) = "cpfsxgidnmfxgsibb")
  #check (rfl : (encode Base32PadUpper    basic) = "CPFSXGIDNMFXGSIBB")
  #check (rfl : (encode Base32Z           basic) = "hxf1zgedpcfzg1ebb")
  #check (rfl : (encode Base36            basic) = "k2lcpzo5yikidynfl")
  #check (rfl : (encode Base36Upper       basic) = "K2LCPZO5YIKIDYNFL")
  #check (rfl : (encode Base58Flickr      basic) = "Z7Pznk19XTTzBtx")
  #check (rfl : (encode Base58BTC         basic) = "z7paNL19xttacUY")
  #check (rfl : (encode Base64            basic) = "meWVzIG1hbmkgIQ")
  #check (rfl : (encode Base64Pad         basic) = "MeWVzIG1hbmkgIQ==")
  #check (rfl : (encode Base64URL         basic) = "ueWVzIG1hbmkgIQ")
  #check (rfl : (encode Base64URLPad      basic) = "UeWVzIG1hbmkgIQ==")

  -- RFC4648 Test Vectors: https://datatracker.ietf.org/doc/html/rfc4648#section-10
  -- test vector `i` is the first `i` letters of the string "foobar" as UTF8
  #eval "foobar".toUTF8
  def rfc0 := ByteArray.mk #[]
  def rfc1 := ByteArray.mk #[102]
  def rfc2:= ByteArray.mk #[102, 111]
  def rfc3 := ByteArray.mk #[102, 111, 111]
  def rfc4 := ByteArray.mk #[102, 111, 111, 98]
  def rfc5 := ByteArray.mk #[102, 111, 111, 98, 97]
  def rfc6 := ByteArray.mk #[102, 111, 111, 98, 97, 114]

  #check (rfl : encode Base16Upper rfc0 = "F")
  #check (rfl : encode Base16Upper rfc1 = "F66")
  #check (rfl : encode Base16Upper rfc2 = "F666F")
  #check (rfl : encode Base16Upper rfc3 = "F666F6F")
  #check (rfl : encode Base16Upper rfc4 = "F666F6F62")
  #check (rfl : encode Base16Upper rfc5 = "F666F6F6261")
  #check (rfl : encode Base16Upper rfc6 = "F666F6F626172")

  #check (rfl : (encode Base32Hex         rfc0) = "v")
  #check (rfl : (encode Base32Hex         rfc1) = "vco")
  #check (rfl : (encode Base32Hex         rfc2) = "vcpng")
  #check (rfl : (encode Base32Hex         rfc3) = "vcpnmu")
  #check (rfl : (encode Base32Hex         rfc4) = "vcpnmuog")
  #check (rfl : (encode Base32Hex         rfc5) = "vcpnmuoj1")
  #check (rfl : (encode Base32Hex         rfc6) = "vcpnmuoj1e8")

  #check (rfl : (encode Base32HexUpper    rfc0) = "V")
  #check (rfl : (encode Base32HexUpper    rfc1) = "VCO")
  #check (rfl : (encode Base32HexUpper    rfc2) = "VCPNG")
  #check (rfl : (encode Base32HexUpper    rfc3) = "VCPNMU")
  #check (rfl : (encode Base32HexUpper    rfc4) = "VCPNMUOG")
  #check (rfl : (encode Base32HexUpper    rfc5) = "VCPNMUOJ1")
  #check (rfl : (encode Base32HexUpper    rfc6) = "VCPNMUOJ1E8")

  #check (rfl : (encode Base32HexPad      rfc0) = "t")
  #check (rfl : (encode Base32HexPad      rfc1) = "tco======")
  #check (rfl : (encode Base32HexPad      rfc2) = "tcpng====")
  #check (rfl : (encode Base32HexPad      rfc3) = "tcpnmu===")
  #check (rfl : (encode Base32HexPad      rfc4) = "tcpnmuog=")
  #check (rfl : (encode Base32HexPad      rfc5) = "tcpnmuoj1")
  #check (rfl : (encode Base32HexPad      rfc6) = "tcpnmuoj1e8======")

  #check (rfl : (encode Base32HexPadUpper rfc0) = "T")
  #check (rfl : (encode Base32HexPadUpper rfc1) = "TCO======")
  #check (rfl : (encode Base32HexPadUpper rfc2) = "TCPNG====")
  #check (rfl : (encode Base32HexPadUpper rfc3) = "TCPNMU===")
  #check (rfl : (encode Base32HexPadUpper rfc4) = "TCPNMUOG=")
  #check (rfl : (encode Base32HexPadUpper rfc5) = "TCPNMUOJ1")
  #check (rfl : (encode Base32HexPadUpper rfc6) = "TCPNMUOJ1E8======")

  #check (rfl : (encode Base32 rfc0) = "b")
  #check (rfl : (encode Base32 rfc1) = "bmy")
  #check (rfl : (encode Base32 rfc2) = "bmzxq")
  #check (rfl : (encode Base32 rfc3) = "bmzxw6")
  #check (rfl : (encode Base32 rfc4) = "bmzxw6yq")
  #check (rfl : (encode Base32 rfc5) = "bmzxw6ytb")
  #check (rfl : (encode Base32 rfc6) = "bmzxw6ytboi")

  #check (rfl : (encode Base32Upper rfc0) = "B")
  #check (rfl : (encode Base32Upper rfc1) = "BMY")
  #check (rfl : (encode Base32Upper rfc2) = "BMZXQ")
  #check (rfl : (encode Base32Upper rfc3) = "BMZXW6")
  #check (rfl : (encode Base32Upper rfc4) = "BMZXW6YQ")
  #check (rfl : (encode Base32Upper rfc5) = "BMZXW6YTB")
  #check (rfl : (encode Base32Upper rfc6) = "BMZXW6YTBOI")

  #check (rfl : (encode Base32Pad rfc0) = "c")
  #check (rfl : (encode Base32Pad rfc1) = "cmy======")
  #check (rfl : (encode Base32Pad rfc2) = "cmzxq====")
  #check (rfl : (encode Base32Pad rfc3) = "cmzxw6===")
  #check (rfl : (encode Base32Pad rfc4) = "cmzxw6yq=")
  #check (rfl : (encode Base32Pad rfc5) = "cmzxw6ytb")
  #check (rfl : (encode Base32Pad rfc6) = "cmzxw6ytboi======")

  #check (rfl : (encode Base32PadUpper rfc0) = "C")
  #check (rfl : (encode Base32PadUpper rfc1) = "CMY======")
  #check (rfl : (encode Base32PadUpper rfc2) = "CMZXQ====")
  #check (rfl : (encode Base32PadUpper rfc3) = "CMZXW6===")
  #check (rfl : (encode Base32PadUpper rfc4) = "CMZXW6YQ=")
  #check (rfl : (encode Base32PadUpper rfc5) = "CMZXW6YTB")
  #check (rfl : (encode Base32PadUpper rfc6) = "CMZXW6YTBOI======")

  #check (rfl : (encode Base64         rfc0) = "m")
  #check (rfl : (encode Base64         rfc1) = "mZg")
  #check (rfl : (encode Base64         rfc2) = "mZm8")
  #check (rfl : (encode Base64         rfc3) = "mZm9v")
  #check (rfl : (encode Base64         rfc4) = "mZm9vYg")
  #check (rfl : (encode Base64         rfc5) = "mZm9vYmE")
  #check (rfl : (encode Base64         rfc6) = "mZm9vYmFy")

  #check (rfl : (encode Base64Pad      rfc0) = "M")
  #check (rfl : (encode Base64Pad      rfc1) = "MZg==")
  #check (rfl : (encode Base64Pad      rfc2) = "MZm8=")
  #check (rfl : (encode Base64Pad      rfc3) = "MZm9v")
  #check (rfl : (encode Base64Pad      rfc4) = "MZm9vYg==")
  #check (rfl : (encode Base64Pad      rfc5) = "MZm9vYmE=")
  #check (rfl : (encode Base64Pad      rfc6) = "MZm9vYmFy")

  #check (rfl : (encode Base64URLPad         rfc0) = "U")
  #check (rfl : (encode Base64URLPad         rfc1) = "UZg==")
  #check (rfl : (encode Base64URLPad         rfc2) = "UZm8=")
  #check (rfl : (encode Base64URLPad         rfc3) = "UZm9v")
  #check (rfl : (encode Base64URLPad         rfc4) = "UZm9vYg==")
  #check (rfl : (encode Base64URLPad         rfc5) = "UZm9vYmE=")
  #check (rfl : (encode Base64URLPad         rfc6) = "UZm9vYmFy")

end Test
