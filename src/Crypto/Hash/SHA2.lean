import Crypto.Serial

open Crypto
open Crypto.Serial


namespace Crypto.Hash.SHA2


-- Based on https://datatracker.ietf.org/doc/html/rfc6234


inductive Bits where
| SHA_224
| SHA_256
| SHA_384
| SHA_512
deriving Repr

open Bits

def uint : Bits → Type
| SHA_224 => UInt32
| SHA_256 => UInt32
| SHA_384 => UInt64
| SHA_512 => UInt64

instance : OfNat (uint SHA_224) x := UInt32.instOfNat
instance : OfNat (uint SHA_256) x := UInt32.instOfNat
instance : OfNat (uint SHA_384) x := UInt64.instOfNat
instance : OfNat (uint SHA_512) x := UInt64.instOfNat

instance : Inhabited (uint SHA_224) := instInhabitedUInt32
instance : Inhabited (uint SHA_256) := instInhabitedUInt32
instance : Inhabited (uint SHA_384) := instInhabitedUInt64
instance : Inhabited (uint SHA_512) := instInhabitedUInt64

instance : Add (uint SHA_224) := instAddUInt32
instance : Add (uint SHA_256) := instAddUInt32
instance : Add (uint SHA_384) := instAddUInt64
instance : Add (uint SHA_512) := instAddUInt64


private def H₀ (b : Bits) : Array (uint b) :=
  match b with
  | SHA_224 =>
      #[
         0xc1059ed8
       , 0x367cd507
       , 0x3070dd17
       , 0xf70e5939
       , 0xffc00b31
       , 0x68581511
       , 0x64f98fa7
       , 0xbefa4fa4
       ]
  | SHA_256 =>
      #[
         0x6a09e667
       , 0xbb67ae85
       , 0x3c6ef372
       , 0xa54ff53a
       , 0x510e527f
       , 0x9b05688c
       , 0x1f83d9ab
       , 0x5be0cd19
       ]
  | SHA_384 =>
      #[
         0xcbbb9d5dc1059ed8
       , 0x629a292a367cd507
       , 0x9159015a3070dd17
       , 0x152fecd8f70e5939
       , 0x67332667ffc00b31
       , 0x8eb44a8768581511
       , 0xdb0c2e0d64f98fa7
       , 0x47b5481dbefa4fa4
       ]
  | SHA_512 =>
      #[
         0x6a09e667f3bcc908
       , 0xbb67ae8584caa73b
       , 0x3c6ef372fe94f82b
       , 0xa54ff53a5f1d36f1
       , 0x510e527fade682d1
       , 0x9b05688c2b3e6c1f
       , 0x1f83d9abfb41bd6b
       , 0x5be0cd19137e2179
       ]


private def K32 : Array UInt32 :=
  #[
     0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5
   , 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5
   , 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3
   , 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174
   , 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc
   , 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da
   , 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7
   , 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967
   , 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13
   , 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85
   , 0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3
   , 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070
   , 0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5
   , 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3
   , 0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208
   , 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
   ]

private def K64 : Array UInt64 :=
  #[
     0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc
   , 0x3956c25bf348b538, 0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118
   , 0xd807aa98a3030242, 0x12835b0145706fbe, 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2
   , 0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235, 0xc19bf174cf692694
   , 0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65
   , 0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5
   , 0x983e5152ee66dfab, 0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4
   , 0xc6e00bf33da88fc2, 0xd5a79147930aa725, 0x06ca6351e003826f, 0x142929670a0e6e70
   , 0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed, 0x53380d139d95b3df
   , 0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b
   , 0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30
   , 0xd192e819d6ef5218, 0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8
   , 0x19a4c116b8d2d0c8, 0x1e376c085141ab53, 0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8
   , 0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373, 0x682e6ff3d6b2b8a3
   , 0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec
   , 0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b
   , 0xca273eceea26619c, 0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178
   , 0x06f067aa72176fba, 0x0a637dc5a2c898a6, 0x113f9804bef90dae, 0x1b710b35131c471b
   , 0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc, 0x431d67c49c100d4c
   , 0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817
   ]

private def Ks (b : Bits) : Array (uint b) :=
  match b with
  | SHA_224 => K32
  | SHA_256 => K32
  | SHA_384 => K64
  | SHA_512 => K64


class Ops (a : Type) where
  SHR : a → a → a
  ROTR : a → a → a
  ROTL : a → a → a
  CH : a → a → a → a
  MAJ : a → a → a → a
  BSIG0 : a → a
  BSIG1 : a → a
  SSIG0 : a → a
  SSIG1 : a → a

open Ops

private def implSHR [ShiftRight a] (n x : a) : a := x >>> n

private def implROTR [ShiftRight a] [ShiftLeft a] [OrOp a] [Sub a] (w n x : a) : a := (x >>> n) ||| (x <<< (w - n))

private def implROTL [ShiftRight a] [ShiftLeft a] [OrOp a] [Sub a] (w n x : a) : a := (x <<< n) ||| (x >>> (w - n))

instance instOpsUInt32 : Ops UInt32 where
  SHR := implSHR
  ROTR := implROTR 32
  ROTL := implROTL 32
  CH x y z := (x &&& y) ^^^ ((~~~ x) &&& z)
  MAJ x y z := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)
  BSIG0 x := implROTR 32 2 x ^^^ implROTR 32 13 x ^^^ implROTR 32 22 x
  BSIG1 x := implROTR 32 6 x ^^^ implROTR 32 11 x ^^^ implROTR 32 25 x
  SSIG0 x := implROTR 32 7 x ^^^ implROTR 32 18 x ^^^ implSHR 3 x
  SSIG1 x := implROTR 32 17 x ^^^ implROTR 32 19 x ^^^ implSHR 10 x

instance instOpsUInt64 : Ops UInt64 where
  SHR := implSHR
  ROTR := implROTR 64
  ROTL := implROTL 64
  CH x y z := (x &&& y) ^^^ ((~~~ x) &&& z)
  MAJ x y z := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)
  BSIG0 x := implROTR 64 28 x ^^^ implROTR 64 34 x ^^^ implROTR 64 39 x
  BSIG1 x := implROTR 64 14 x ^^^ implROTR 64 18 x ^^^ implROTR 64 41 x
  SSIG0 x := implROTR 64 1 x ^^^ implROTR 64 8 x ^^^ implSHR 7 x
  SSIG1 x := implROTR 64 19 x ^^^ implROTR 64 61 x ^^^ implSHR 6 x

instance : Ops (uint SHA_224) := instOpsUInt32
instance : Ops (uint SHA_256) := instOpsUInt32
instance : Ops (uint SHA_384) := instOpsUInt64
instance : Ops (uint SHA_512) := instOpsUInt64


def hashBlock (b : Bits) [Inhabited (uint b)] [Add (uint b)] [Ops (uint b)] (H' : Array (uint b)) (M : Array (uint b)) : Array (uint b) :=
  let n :=
    match b with
    | SHA_224 => 64
    | SHA_256 => 64
    | SHA_384 => 80
    | SHA_512 => 80
  let H := H'.get!
  let K := (Ks b).get!
  let nextW (W' : Array (uint b)) : Array (uint b) :=
    let W t := W'.get! t
    let t := W'.size
    let x := SSIG1 (W (t-2)) + W (t-7) + SSIG0 (W (t-15)) + W (t-16)
    W'.push x
  let W := (Nat.iterate nextW (n - 16) M).get!
  let mainHash : uint b × uint b × uint b × uint b × uint b × uint b × uint b × uint b → Nat → uint b × uint b × uint b × uint b × uint b × uint b × uint b × uint b
      | ⟨ a, b, c, d, e, f, g, h ⟩, t =>
          let T1 := h + BSIG1 e + CH e f g  + K t + W t
          let T2 := BSIG0 a + MAJ a b c
          let h' := g
          let g' := f
          let f' := e
          let e' := d + T1
          let d' := c
          let c' := b
          let b' := a
          let a' := T1 + T2
          ⟨ a', b', c', d', e', f', g', h' ⟩
  let ⟨a, b, c, d, e, f, g, h⟩ :=
        List.foldl
          mainHash
          ⟨H 0, H 1, H 2, H 3, H 4, H 5, H 6, H 7⟩
          $ List.range n
  #[
     a + H 0
   , b + H 1
   , c + H 2
   , d + H 3
   , e + H 4
   , f + H 5
   , g + H 6
   , h + H 7
  ]

def hashBlocks (b : Bits) [Inhabited (uint b)] [Add (uint b)] [Ops (uint b)] (Ms : List (Array (uint b))) : Array (uint b) :=
  List.foldl (hashBlock b) (H₀ b) Ms


open Words

instance : Words Nat (uint SHA_224) := instWordsNatUInt32
instance : Words Nat (uint SHA_256) := instWordsNatUInt32
instance : Words Nat (uint SHA_384) := instWordsNatUInt64
instance : Words Nat (uint SHA_512) := instWordsNatUInt64

instance : Words ByteArray (uint SHA_224) := instWordsByteArrayUInt32
instance : Words ByteArray (uint SHA_256) := instWordsByteArrayUInt32
instance : Words ByteArray (uint SHA_384) := instWordsByteArrayUInt64
instance : Words ByteArray (uint SHA_512) := instWordsByteArrayUInt64


def pad (b : Bits) [Words Nat (uint b)] [Words ByteArray (uint b)] (x : ByteArray) : Array (uint b) :=
  let m := match b with
           | SHA_224 => 1
           | SHA_256 => 1
           | SHA_384 => 2
           | SHA_512 => 2
  let n := m * 512
  let L := 8 * x.size
  let K := n - (L + 1 + m * 64) % n
  let L' := toWords L
  let y := x.append $ ByteArray.mk #[0x80] ++ ByteArray.mk (Array.mk $ List.replicate ((K - 7) / 8 + 2 * m - L'.size) 0)
  toWords y ++ L'


-- FIXME: Prove termination.
private partial def toChunks (k : Nat) (x : Array u) : List (Array u) :=
  let n := x.size
  let y := x.extract 0 k
  if n <= k
    then [y]
    else y :: toChunks k (x.extract k n)

def hashBytes (b : Bits) [Inhabited (uint b)] [Add (uint b)] [Ops (uint b)] [Words Nat (uint b)] [Words ByteArray (uint b)] : ByteArray → Array (uint b) :=
  hashBlocks b ∘ toChunks 16 ∘ pad b


def sha (b : Bits) [Words a (uint SHA_224)] [Words a (uint SHA_256)] [Words a (uint SHA_384)] [Words a (uint SHA_512)] : ByteArray → a :=
  match b with
  | SHA_224 => fromWords ∘ Array.pop ∘ hashBytes SHA_224
  | SHA_256 => fromWords ∘ hashBytes SHA_256
  | SHA_384 => fromWords ∘ Array.pop ∘ Array.pop ∘ hashBytes SHA_384
  | SHA_512 => fromWords ∘ hashBytes SHA_512

def sha224 [Words a (uint SHA_224)] : ByteArray → a := fromWords ∘ Array.pop ∘ hashBytes SHA_224
def sha256 [Words a (uint SHA_256)] : ByteArray → a := fromWords ∘ hashBytes SHA_256
def sha384 [Words a (uint SHA_384)] : ByteArray → a := fromWords ∘ Array.pop ∘ Array.pop ∘ hashBytes SHA_384
def sha512 [Words a (uint SHA_512)] : ByteArray → a := fromWords ∘ hashBytes SHA_512


end Crypto.Hash.SHA2
