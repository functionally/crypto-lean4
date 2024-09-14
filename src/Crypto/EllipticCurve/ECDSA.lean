import Crypto.EllipticCurve
import Crypto.Field.Fp
import Mathlib.Control.Random

open Crypto
open Crypto.EllipticCurve
open Crypto.Field


namespace Crypto.EllipticCurve.ECDSA


variable {p : Nat}
variable {ec : EllipticCurve (Fp p)}

structure Signature (g : EllipticCurve.Group ec) where
  challenge : Fp g.n
  proof : Fp g.n
deriving Repr, DecidableEq, BEq, Inhabited

variable {g : EllipticCurve.Group ec}

def rawSign (kp : Group.KeyPair g) (item : Fp g.n) (k : Fp g.n) (R : Point ec) : Signature g :=
  let r := R.x.castFp
  let s := (item + r.castFp * kp.prv.castFp) / k
  ⟨ r , s ⟩

def trySign (kp : Group.KeyPair g) (item : Fp g.n) (k : Fp g.n) : Option (Signature g) :=
  let R := k.val * g.G
  let rs := rawSign kp item k R
  if rs.challenge = 0 ∨ rs.proof = 0
    then none
    else some rs

partial def sign [RandomGen gen] [Monad m] (kp : Group.KeyPair g) (item : Fp g.n) : RandGT gen m (Signature g) :=
  do
    let k ← Random.random
    match trySign kp item k with
    | none => sign kp item
    | some result => pure result

def verify (pk : EllipticCurve.Group.PubKey g) (item : Fp g.n) : Signature g → Bool
| ⟨ r , s ⟩ => let u₁ := item / s
               let u₂ := r.castFp / s
               let P := u₁ * g.G + u₂ * pk.pub
               r = P.x.castFp


end Crypto.EllipticCurve.ECDSA
