import Mathlib.Data.Vector


namespace Crypto


class Serializable (a : Type) where
  encode : a → ByteArray
  decode : ByteArray → Option a

instance : Serializable ByteArray where
  encode := id
  decode := some

instance : Serializable String where
  encode := String.toUTF8
  decode := some ∘ String.fromUTF8Unchecked


namespace Serial

  class Words (n : Type) (u : Type) where
    toWords : n → Array u
    fromWords : Array u → n

  open Words

  -- FIXME: Prove termination.
  private partial def natFromUInt32s (x : Array UInt32) : Nat :=
    match x.size with
    | 0 => 0
    | 1 => (x.get! 0).toNat
    | n => (x.get! 0).toNat <<< 32 + natFromUInt32s (x.extract 1 n)

  -- FIXME: Prove termination.
  private partial def natFromUInt64s (x : Array UInt64) : Nat :=
    match x.size with
    | 0 => 0
    | 1 => (x.get! 0).toNat
    | n => (x.get! 0).toNat <<< 64 + natFromUInt64s (x.extract 1 n)

  instance instWordsNatUInt32 : Words Nat UInt32 where
    toWords i :=
      Array.map UInt32.ofNat
        #[
           i / UInt32.size
         , i % UInt32.size
         ]
    fromWords := natFromUInt32s

  instance instWordsNatUInt64 : Words Nat UInt64 where
    toWords i :=
      Array.map UInt64.ofNat
        #[
           i / UInt64.size
         , i % UInt64.size
         ]
    fromWords := natFromUInt64s

  private def bytesToUInt32s (x : Array UInt8) : Array UInt32 :=
    let n := x.size
    let k := 4 - n % 4
    let u := UInt32.ofNat ∘ Nat.sum $ (List.range $ k).map (fun i => (x.get! i).toNat <<< (8 * (3 - i)))
    if n < 5
      then #[u]
      else #[u] ++ bytesToUInt32s (x.extract 4 n)
  termination_by x.size

  private def bytesToUInt64s (x : Array UInt8) : Array UInt64 :=
    let n := x.size
    let k := 8 - n % 8
    let u := UInt64.ofNat ∘ Nat.sum $ (List.range $ k).map (fun i => (x.get! i).toNat <<< (8 * (7 - i)))
    if n < 9
      then #[u]
      else #[u] ++ bytesToUInt64s (x.extract 8 n)
  termination_by x.size

  -- FIXME: Prove termination.
  private partial def byteArrayFromUInt32s (x : Array UInt32) : Array UInt8 :=
    let f (y : UInt32) : Array UInt8 :=
          Array.mk
            $ (List.range 4).map
            $ fun i => (y >>> (8 * UInt32.ofNat i)).toUInt8
    match x.size with
    | 0 => Array.empty
    | 1 => f (x.get! 0)
    | n => f (x.get! 0) ++ byteArrayFromUInt32s (x.extract 1 n)

  -- FIXME: Prove termination.
  private partial def byteArrayFromUInt64s (x : Array UInt64) : Array UInt8 :=
    let f (y : UInt64) : Array UInt8 :=
          Array.mk
            $ (List.range 8).map
            $ fun i => (y >>> (8 * UInt64.ofNat i)).toUInt8
    match x.size with
    | 0 => Array.empty
    | 1 => f (x.get! 0)
    | n => f (x.get! 0) ++ byteArrayFromUInt64s (x.extract 1 n)

  instance instWordsByteArrayUInt32 : Words ByteArray UInt32 where
    toWords := bytesToUInt32s ∘ ByteArray.data
    fromWords := ByteArray.mk ∘ byteArrayFromUInt32s

  instance instWordsByteArrayUInt64 : Words ByteArray UInt64 where
    toWords := bytesToUInt64s ∘ ByteArray.data
    fromWords := ByteArray.mk ∘ byteArrayFromUInt64s

end Serial


end Crypto
