
import LSpec

import Crypto.EllipticCurve.Secp256k1
import Crypto.Field.Fp
import Crypto.SSS
import Crypto.SSS.Test
import Crypto.TSS
import Mathlib.Control.Random

open Crypto
open Crypto.EllipticCurve
open Crypto.Field
open Crypto.TSS
open LSpec


namespace Crypto.TSS.Test


variable {p : Nat}
variable {ec : EllipticCurve (Fp p)}


structure TestCase (g : EllipticCurve.Group ec) where
  key : Group.KeyPair g
  parties : Nat
  threshold : Nat
  shares : SSS.Shares (field g) (field g)
deriving Repr

namespace TestCase

  def pubs : TestCase g → SSS.Shares (field g) (g.point) := Functor.map (fun y => y * g.G) ∘ TestCase.shares

end TestCase

def genTestable (g : EllipticCurve.Group ec) : SlimCheck.Gen (TestCase g) :=
  do
    let key ← (Group.randKeyPair : Rand (Group.KeyPair g))
    let parties ← SlimCheck.Gen.choose Nat 1 10
    let threshold ← SlimCheck.Gen.choose Nat 1 parties
    let shares ← (share g key.prv threshold : Rand (SSS.PrivShares (field g) parties))
    let parties' ← SlimCheck.Gen.choose Nat 0 parties
    let shares' ← SSS.Shares.mk <$> SSS.Test.sublist parties' shares.toShares.xys
    pure $ TestCase.mk key parties threshold shares'

instance : SlimCheck.Shrinkable (TestCase g) where
  shrink _ := []

instance : SlimCheck.SampleableExt (TestCase g) :=
  SlimCheck.SampleableExt.mkSelfContained $ genTestable g

#lspec group "assemble"
  $ check "private key" (∀ tc : TestCase Secp256k1, tc.shares.count < tc.threshold ∨ SSS.assemble tc.shares = tc.key.prv)
  $ check "public key" (∀ tc : TestCase Secp256k1, tc.shares.xys.length < tc.threshold ∨ assemble tc.pubs = tc.key.pub)


end Crypto.TSS.Test
