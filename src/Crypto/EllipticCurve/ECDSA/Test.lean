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
  hash : Fp g.n
  sig : Signature g
deriving Repr

instance : SlimCheck.Shrinkable (TestCase g) where
  shrink _ := []

instance : SlimCheck.SampleableExt (TestCase g) :=
  SlimCheck.SampleableExt.mkSelfContained $
    do
      let kp ← (Random.random : Rand (Group.KeyPair g))
      let z ← (Random.random : Rand (Fp g.n))
      let rs ← (sign kp z : Rand (Signature g))
      pure $ TestCase.mk kp z rs

#lspec check "Verify signature" (∀ tc : TestCase Secp256k1, verify tc.keyPair.pubKey tc.hash tc.sig)


end Crypto.EllipticCurve.ECDSA.Test
