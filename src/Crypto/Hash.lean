import Mathlib.Data.Vector

open Vector


namespace Crypto


abbrev CHash := Vector UInt8

variable {n : Nat}

class CHashable (n : Nat) (a : Type) where
  chash : a → CHash n

instance [Hashable a] : CHashable 8 a where
  chash x :=
    let n := hash x
    let f k := UInt8.ofNat ∘ UInt64.toNat $ (n >>> k) &&& 0xFF
    ⟨ [f 0, f 8, f 16, f 24, f 32, f 40, f 48, f 56] , rfl ⟩

#eval (CHashable.chash "A message" : CHash 8)


end Crypto
