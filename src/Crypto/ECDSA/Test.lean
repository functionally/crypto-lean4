import LSpec
import Crypto.Field.Fp
import Crypto.EllipticCurve
import Crypto.EllipticCurve.Secp256k1
import Crypto.ECDSA
import Mathlib.Control.Random

open Crypto
open Crypto.Field
open Crypto.EllipticCurve
open Crypto.ECDSA
open LSpec


namespace Crypto.ECDSA.Test

variable {ec : EllipticCurve (Fp p)}

structure TestCase  (g : Group ec) where
  keyPair : Group.KeyPair g
  hash : Fp g.n
  sig : Signature g
deriving Repr

def genTestable (g : Group ec) : SlimCheck.Gen (TestCase g) :=
  do
    let kp ← (Random.random : Rand (Group.KeyPair g))
    let z ← (Random.random : Rand (Fp g.n))
    let rs ← (sign kp z : Rand (Signature g))
    pure $ TestCase.mk kp z rs

instance : SlimCheck.Shrinkable (TestCase g) where
  shrink _ := []

instance : SlimCheck.SampleableExt (TestCase g) :=
  SlimCheck.SampleableExt.mkSelfContained $ genTestable g

#lspec check "Verify signature" (∀ tc : TestCase Secp256k1, verify tc.keyPair.pubKey tc.hash tc.sig)


end Crypto.ECDSA.Test
