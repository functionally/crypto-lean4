import Crypto.Field.Fp
import Crypto.EllipticCurve
import Mathlib.Control.Random

open Crypto
open Crypto.Field
open Crypto.EllipticCurve


namespace Crypto.ECDSA


variable {p : Nat}
variable {ec : EllipticCurve (Fp p)}
variable {g : EllipticCurve.Group ec}


def trySign (kp : Group.KeyPair g) (z : Fp g.n) (k : Fp g.n) : Option (Fp p × Fp g.n) :=
  let P : Point ec := k.val * g.G
  let r : Fp p := P.x
  let s : Fp g.n := (z + r.castFp * kp.prv.castFp) / k
  if r = 0 ∨ s = 0
    then none
    else some ⟨ r , s ⟩

partial def sign [RandomGen g'] [Monad m] (kp : Group.KeyPair g) (z : Fp g.n) : RandGT g' m (Fp p × Fp g.n) :=
  do
    let k ← Random.random
    match trySign kp z k with
    | none => sign kp z
    | some result => pure result

def verify {p : Nat} {ec : EllipticCurve (Fp p)} {g : EllipticCurve.Group ec} (pk : EllipticCurve.Group.PubKey g) (z : Fp g.n) : Fp p × Fp g.n → Bool
| ⟨ r , s ⟩ => let u₁ := z / s
               let u₂ := r.castFp / s
               let P := u₁ * g.G + u₂ * pk.pub
               r = P.x


end Crypto.ECDSA
