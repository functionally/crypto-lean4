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
  decode := some ∘ String.fromUTF8Unchecked -- FIXME: Check this.


namespace Serial


  class Words (n : Type) (u : Type) where
    toWords : n → Array u
    fromWords : Array u → n

  open Words

  -- FIXME: Prove termination.
  private partial def natFromUInt8s (x : Array UInt8) : Nat :=
    match x.size with
    | 0 => 0
    | 1 => (x.get! 0).toNat
    | n => (x.get! 0).toNat <<< (8 * (x.size - 1)) + natFromUInt8s (x.extract 1 n)

  -- FIXME: Prove termination.
  private partial def natFromUInt32s (x : Array UInt32) : Nat :=
    match x.size with
    | 0 => 0
    | 1 => (x.get! 0).toNat
    | n => (x.get! 0).toNat <<< (32 * (x.size - 1)) + natFromUInt32s (x.extract 1 n)

  -- FIXME: Prove termination.
  private partial def natFromUInt64s (x : Array UInt64) : Nat :=
    match x.size with
    | 0 => 0
    | 1 => (x.get! 0).toNat
    | n => (x.get! 0).toNat <<< (64 * (x.size - 1)) + natFromUInt64s (x.extract 1 n)

  -- FIXME: Prove termination.
  private partial def natToUInt8s (x : Nat) : List UInt8 :=
    if x < UInt8.size
      then [x.toUInt8]
      else (x % UInt8.size).toUInt8 :: natToUInt8s (x / UInt8.size)

  -- FIXME: Prove termination.
  private partial def natToUInt32s (x : Nat) : List UInt32 :=
    if x < UInt32.size
      then [x.toUInt32]
      else (x % UInt32.size).toUInt32 :: natToUInt32s (x / UInt32.size)

  -- FIXME: Prove termination.
  private partial def natToUInt64s (x : Nat) : List UInt64 :=
    if x < UInt64.size
      then [x.toUInt64]
      else (x % UInt64.size).toUInt64 :: natToUInt64s (x / UInt64.size)

  instance instWordsNatUInt8 : Words Nat UInt8 where
    toWords := List.toArray ∘ List.reverse ∘ natToUInt8s
    fromWords := natFromUInt8s

  instance instWordsNatUInt32 : Words Nat UInt32 where
    toWords := List.toArray ∘ List.reverse ∘ natToUInt32s
    fromWords := natFromUInt32s

  instance instWordsNatUInt64 : Words Nat UInt64 where
    toWords := List.toArray ∘ List.reverse ∘ natToUInt64s
    fromWords := natFromUInt64s

  def natToBytes : Nat → ByteArray :=
    ByteArray.mk ∘ Words.toWords

  def BytesToNat : ByteArray → Nat
  | ⟨ x ⟩ =>  Words.fromWords x

  private def bytesToUInt32s (x : Array UInt8) : Array UInt32 :=
    let n := x.size
    let k := min 4 n
    let u := UInt32.ofNat ∘ Nat.sum $ (List.range k).map (fun i => (x.get! i).toNat <<< (8 * (3 - i)))
    if n < 5
      then #[u]
      else #[u] ++ bytesToUInt32s (x.extract 4 n)
  termination_by x.size

  private def bytesToUInt64s (x : Array UInt8) : Array UInt64 :=
    let n := x.size
    let k := min 8 n
    let u := UInt64.ofNat ∘ Nat.sum $ (List.range k).map (fun i => (x.get! i).toNat <<< (8 * (7 - i)))
    if n < 9
      then #[u]
      else #[u] ++ bytesToUInt64s (x.extract 8 n)
  termination_by x.size

  -- FIXME: Prove termination.
  private partial def bytesFromUInt32s (x : Array UInt32) : Array UInt8 :=
    let f (y : UInt32) : Array UInt8 :=
          Array.mk
            $ (List.range 4).reverse.map
            $ fun i => (y >>> (8 * UInt32.ofNat i)).toUInt8
    match x.size with
    | 0 => Array.empty
    | 1 => f (x.get! 0)
    | n => f (x.get! 0) ++ bytesFromUInt32s (x.extract 1 n)

  -- FIXME: Prove termination.
  private partial def bytesFromUInt64s (x : Array UInt64) : Array UInt8 :=
    let f (y : UInt64) : Array UInt8 :=
          Array.mk
            $ (List.range 8).reverse.map
            $ fun i => (y >>> (8 * UInt64.ofNat i)).toUInt8
    match x.size with
    | 0 => Array.empty
    | 1 => f (x.get! 0)
    | n => f (x.get! 0) ++ bytesFromUInt64s (x.extract 1 n)

  instance instWordsByteArrayUInt32 : Words ByteArray UInt32 where
    toWords := bytesToUInt32s ∘ ByteArray.data
    fromWords := ByteArray.mk ∘ bytesFromUInt32s

  instance instWordsByteArrayUInt64 : Words ByteArray UInt64 where
    toWords := bytesToUInt64s ∘ ByteArray.data
    fromWords := ByteArray.mk ∘ bytesFromUInt64s


  def bytesToHex : ByteArray → String :=
    "".intercalate
      ∘ List.map (BitVec.toHex ∘ BitVec.ofNat 8 ∘ UInt8.toNat)
      ∘ ByteArray.toList

  -- FIXME: Add inverse of `bytesToHex`.


end Serial


end Crypto
