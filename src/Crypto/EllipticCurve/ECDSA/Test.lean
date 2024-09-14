import Crypto.EllipticCurve
import Crypto.EllipticCurve.ECDSA
import Crypto.EllipticCurve.Secp256k1
import Crypto.Field.Fp
import LSpec
import Mathlib.Control.Random

open Crypto
open Crypto.EllipticCurve
open Crypto.EllipticCurve.ECDSA
open Crypto.Field
open LSpec


namespace Crypto.EllipticCurve.ECDSA.Test

variable {ec : EllipticCurve (Fp p)}

structure TestCase  (g : Group ec) where
  keyPair : Group.KeyPair g
  item : Fp g.n
  signature : Signature g
deriving Repr

instance : SlimCheck.Shrinkable (TestCase g) where
  shrink _ := []

instance : SlimCheck.SampleableExt (TestCase g) :=
  SlimCheck.SampleableExt.mkSelfContained $
    do
      let kp ← (Random.random : Rand (Group.KeyPair g))
      let item ← (Random.random : Rand (Fp g.n))
      let signature ← (sign kp item : Rand (Signature g))
      pure $ ⟨ kp , item , signature ⟩

#lspec check "Verify signature" (∀ tc : TestCase Secp256k1, verify tc.keyPair.pubKey tc.item tc.signature)


end Crypto.EllipticCurve.ECDSA.Test
