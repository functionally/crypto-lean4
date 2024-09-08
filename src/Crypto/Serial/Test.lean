import Crypto.Serial
import LSpec
import Mathlib.Control.Random

open LSpec


namespace Crypto.Serial.Test


instance [Monad m] : Random m UInt32 where
  random :=
    let m := UInt32.size - 1
    Nat.toUInt32 <$> Random.randBound Nat 0 m (Nat.zero_le m)

instance [Monad m] : Random m UInt64 where
  random :=
    let m := UInt64.size - 1
    Nat.toUInt64 <$> Random.randBound Nat 0 m (Nat.zero_le m)

instance [Monad m] : Random m Char where
  random := Char.ofNat <$> Random.randBound Nat 0 255 (Nat.zero_le 255)

instance [Monad m] : Random m String where
  random :=
    do
      let i ← Random.randBound Nat 0 9 (Nat.zero_le 9)
      String.mk <$> Monad.sequence (List.replicate i Random.random)

instance : SlimCheck.Shrinkable String where
  shrink := List.map String.mk ∘ List.sublists ∘ String.toList

instance : SlimCheck.SampleableExt String :=
  SlimCheck.SampleableExt.mkSelfContained (Random.random : Rand String)


#lspec group "Serializable"
  $ group "String" (
      group "encode" (
        test "ASCII" ((Serializable.encode "Hello").toList = [0x48, 0x65, 0x6C, 0x6C, 0x6F])
      $ test "Unicode" ((Serializable.encode "αβγδε").toList = [0xCE, 0xB1, 0xCE, 0xB2, 0xCE, 0xB3, 0xCE, 0xB4, 0xCE, 0xB5])
      )
    $ group "decode" (
        test "ASCII" (Serializable.decode (ByteArray.mk #[0x48, 0x65, 0x6C, 0x6C, 0x6F]) = some "Hello")
      $ test "Unicode" (Serializable.decode (ByteArray.mk #[0xCE, 0xB1, 0xCE, 0xB2, 0xCE, 0xB3, 0xCE, 0xB4, 0xCE, 0xB5]) = some "αβγδε")
    )
    $ check "decode ∘ encode" (∀ x : String, Serializable.decode (Serializable.encode x) = some x)
  )


instance : Repr (ByteArray) where
  reprPrec
  | ⟨ x ⟩ , n => Repr.reprPrec x n


structure TestCase (n : Type) (u : Type) where
  x : n
  y : Array u
deriving Repr

instance : SlimCheck.Shrinkable (TestCase n u) where
  shrink _ := []

instance [Repr (TestCase n u)] [Random Id u] [Words n u ] : SlimCheck.SampleableExt (TestCase n u) :=
  SlimCheck.SampleableExt.mkSelfContained $ do
    let i ← (Random.randBound Nat 0 9 (Nat.zero_le 9) : Rand Nat)
    let y ← List.toArray <$> (Monad.sequence (List.replicate (i + 1) Random.random) : Rand (List u))
    let x := Words.fromWords y
    pure ⟨ x , y ⟩


#lspec group "instWordsNatUInt32"
  $ group "toWords" (
    (
      test "Case 1" (
        instWordsNatUInt32.toWords 5735816763073854953388147237921 = #[0x48, 0x656c6c6f, 0x2c20776f, 0x726c6421]
      )
    $ test "Case 2" (
        instWordsNatUInt32.toWords 147417349505148463632964036834065426931243456166647359166983602732608220718 = #[0x536F6D, 0x65206173, 0x63696920, 0x74657874, 0x20666F72, 0x20636F6E, 0x76657273, 0x696F6E2E]
      )
    )
  )
  $ check "toWords ∘ fromWords" (∀ tc : TestCase Nat UInt32, Words.toWords tc.x = tc.y)

#lspec group "instWordsNatUInt64"
  $ group "toWords" (
    (
      test "Case 1" (
        instWordsNatUInt64.toWords 5735816763073854953388147237921 = #[0x48656c6c6f, 0x2c20776f726c6421]
      )
    $ test "Case 2" (
        instWordsNatUInt64.toWords 147417349505148463632964036834065426931243456166647359166983602732608220718 = #[0x536F6D65206173, 0x6369692074657874, 0x20666F7220636F6E, 0x76657273696F6E2E]
      )
    )
  )
  $ check "toWords ∘ fromWords" (∀ tc : TestCase Nat UInt64, Words.toWords tc.x = tc.y)


#lspec group "instWordsByteArrayUInt32"
  $ group "toWords" (
    (
      test "Two bytes" (
        instWordsByteArrayUInt32.toWords (ByteArray.mk [1,2].toArray) =
        #[UInt32.ofNat $ 1 * 2^24 + 2 * 2^16]
      )
    $ test "Four bytes" (
        instWordsByteArrayUInt32.toWords (ByteArray.mk [1,2,3,4].toArray) =
        #[UInt32.ofNat $ 1 * 2^24 + 2 * 2^16 + 3 * 2^8 + 4]
      )
    $ test "Five bytes" (
        instWordsByteArrayUInt32.toWords (ByteArray.mk [1,2,3,4,5].toArray) =
        #[UInt32.ofNat $ 1 * 2^24 + 2 * 2^16 + 3 * 2^8 + 4, UInt32.ofNat $ 5 * 2^24]
      )
    $ test "Eight bytes" (
        instWordsByteArrayUInt32.toWords (ByteArray.mk [1,2,3,4,5,6,7,8].toArray) =
        #[UInt32.ofNat $ 1 * 2^24 + 2 * 2^16 + 3 * 2^8 + 4, UInt32.ofNat $ 5 * 2^24 + 6 * 2^16 + 7 * 2^8 + 8]
      )
    $ test "Nine bytes" (
        instWordsByteArrayUInt32.toWords (ByteArray.mk [1,2,3,4,5,6,7,8,9].toArray) =
        #[UInt32.ofNat $ 1 * 2^24 + 2 * 2^16 + 3 * 2^8 + 4, UInt32.ofNat $ 5 * 2^24 + 6 * 2^16 + 7 * 2^8 + 8, UInt32.ofNat $ 9 * 2^24]
      )
    )
  )
  $ check "toWords ∘ fromWords" (∀ tc : TestCase ByteArray UInt32, Words.toWords tc.x = tc.y)


#lspec group "instWordsByteArrayUInt64"
  $ group "toWords" (
    (
      test "Two bytes" (
        instWordsByteArrayUInt64.toWords (ByteArray.mk [1,2].toArray) =
        #[UInt64.ofNat $ 1 * 2^56 + 2 * 2^48]
      )
    $ test "Eight bytes" (
        instWordsByteArrayUInt64.toWords (ByteArray.mk [1,2,3,4,5,6,7,8].toArray) =
        #[UInt64.ofNat $ 1 * 2^56 + 2 * 2^48 + 3 * 2^40 + 4 * 2^32 + 5 * 2^24 + 6 * 2^16 + 7 * 2^8 + 8]
      )
    $ test "Nine bytes" (
        instWordsByteArrayUInt64.toWords (ByteArray.mk [1,2,3,4,5,6,7,8,9].toArray) =
        #[UInt64.ofNat $ 1 * 2^56 + 2 * 2^48 + 3 * 2^40 + 4 * 2^32 + 5 * 2^24 + 6 * 2^16 + 7 * 2^8 + 8, UInt64.ofNat $ 9 * 2^56]
      )
    )
  )
  $ check "toWords ∘ fromWords" (∀ tc : TestCase ByteArray UInt64, Words.toWords tc.x = tc.y)


#lspec group "bytesToHex"
  $ test "ASCII" (
      bytesToHex "abcdefghijklmnopqrstuvwxyz0123456789".toUTF8 =
      "6162636465666768696a6b6c6d6e6f707172737475767778797a30313233343536373839"
    )
  $ test "Unicode" (
      bytesToHex "ΑαΒβΓγΔδΕεΖζΗηΘθΙιΚκΛλΜμΝνΞξΟοΠπΡρΣσςΤτΥυΦφΧχΨψΩω".toUTF8 =
      "ce91ceb1ce92ceb2ce93ceb3ce94ceb4ce95ceb5ce96ceb6ce97ceb7ce98ceb8ce99ceb9ce9acebace9bcebbce9ccebcce9dcebdce9ecebece9fcebfcea0cf80cea1cf81cea3cf83cf82cea4cf84cea5cf85cea6cf86cea7cf87cea8cf88cea9cf89"
    )


end Crypto.Serial.Test
