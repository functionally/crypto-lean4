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


end Crypto
