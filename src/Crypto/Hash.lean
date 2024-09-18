import Crypto.Hash.SHA2
import Crypto.Serial
import Mathlib.Data.Vector

open Crypto.Hash
open Vector


namespace Crypto


structure CHash (n : Nat) where
  data : ByteArray

instance : Repr (CHash n) where
  reprPrec := Repr.reprPrec ∘ ByteArray.toList ∘ CHash.data

namespace CHash

  inductive Algorithm where
  | SHA2_224
  | SHA2_256
  | SHA2_384
  | SHA2_512
  deriving Repr, DecidableEq, BEq

  namespace Algorithm

    def length : Algorithm → Nat
    | SHA2_224 => 28
    | SHA2_256 => 32
    | SHA2_384 => 56
    | SHA2_512 => 64

    def chash [Serializable a] : a → (alg : Algorithm) → CHash alg.length
    | x , SHA2_224 => CHash.mk ∘ SHA2.sha224 $ Serializable.encode x
    | x , SHA2_256 => CHash.mk ∘ SHA2.sha256 $ Serializable.encode x
    | x , SHA2_384 => CHash.mk ∘ SHA2.sha384 $ Serializable.encode x
    | x , SHA2_512 => CHash.mk ∘ SHA2.sha512 $ Serializable.encode x

  end Algorithm

end CHash


end Crypto
