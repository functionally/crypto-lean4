import Crypto.EllipticCurve
import Crypto.EllipticCurve.ECIES
import Crypto.EllipticCurve.Secp256k1
import Crypto.Field.Fp
import Mathlib.Control.Random
import LSpec

open Crypto.EllipticCurve
open Crypto.EllipticCurve.ECIES
open Crypto.Field
open LSpec


namespace Crypto.EllipticCurve.ECIES.Test


variable {p : Nat}
variable {ec : EllipticCurve (Fp p)}


structure TestCase (g : Group ec) where
  key : Group.KeyPair g
  message : Fp g.n
  encrypted : Encrypted g
deriving Repr

instance : SlimCheck.Shrinkable (TestCase g) where
  shrink _ := []

instance {g : Group ec} : SlimCheck.SampleableExt (TestCase g) :=
  SlimCheck.SampleableExt.mkSelfContained $ do
    let key ← (Random.random : Rand (Group.KeyPair g))
    let message ← (Random.random : Rand (Fp g.n))
    let encrypted ← (encrypt key.pubKey message : Rand (Encrypted g))
    pure ⟨ key , message , encrypted ⟩

#lspec check "decrypt ∘ encrypt" (∀ tc : TestCase Secp256k1, tc.message = decrypt tc.key tc.encrypted)


end Crypto.EllipticCurve.ECIES.Test
