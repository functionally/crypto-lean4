import Crypto.EllipticCurve
import Crypto.Field.Fp
import Mathlib.Control.Random

open Crypto.EllipticCurve
open Crypto.Field


namespace Crypto.EllipticCurve.ECIES


variable {p : Nat}
variable {ec : EllipticCurve (Fp p)}


structure Encrypted (g : Group ec) where
  cipher : Fp p
  proof : Point ec
deriving Repr, DecidableEq, BEq

-- https://medium.com/@francomangone18/cryptography-101-encryption-and-digital-signatures-210960778765

def encrypt [RandomGen gen] [Monad m] {g : Group ec} (key : Group.PubKey g) (z : Fp p) : RandGT gen m (Encrypted g) :=
  do
    let nonce : Fp g.n ← Random.random
    let mask := nonce * key.pub
    let cipher := mask.x.xor z
    let proof := nonce * g.G
    pure ⟨ cipher , proof ⟩

def decrypt {g : Group ec} (key : Group.KeyPair g) : Encrypted g → Fp p
| ⟨ cipher , proof ⟩ =>
  let mask := key.prv * proof
  mask.x.xor cipher


end Crypto.EllipticCurve.ECIES
