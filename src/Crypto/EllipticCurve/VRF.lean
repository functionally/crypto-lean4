import Crypto.EllipticCurve

open Crypto.EllipticCurve
open Crypto.Field


namespace Crypto.EllipticCurve.VRF

variable {α : Type}
variable {p : Nat}
variable {ec : EllipticCurve (Fp p)}

structure Proof (g : Group ec) where
  output : Point ec
  challenge : Fp g.n
  response : Fp g.n
deriving Repr, DecidableEq, BEq, Inhabited

variable {g : EllipticCurve.Group ec}

def prove [RandomGen gen] [Monad m] (htc : Point ec → α → Point ec) (commit : Point ec → Point ec → Point ec → Point ec → Fp g.n) (kp : Group.KeyPair g) (x : α) : RandGT gen m (Proof g) :=
  do
    let H := htc kp.pub x
    let Z := kp.prv * H
    let r ← Random.random
    let RB := r * g.G
    let RH := r * g.G
    let c := commit H Z RB RH
    let s := r + kp.prv * c
    pure ⟨ Z , c , s ⟩

def verify (htc : Point ec → α → Point ec) (commit : Point ec → Point ec → Point ec → Point ec → Fp g.n) (pk : Group.PubKey g) (x : α) : Proof g → Bool
| ⟨ Z , c , s ⟩ => let H := htc pk.pub x
                   let RB := s * g.G - c * pk.pub
                   let RH := s * H - c * Z
                   c = commit H Z RB RH


end Crypto.EllipticCurve.VRF
