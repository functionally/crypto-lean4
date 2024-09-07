import LSpec
import Crypto.Field.Fp
import Crypto.SSS
import Mathlib.Control.Random

open Crypto.Field
open Crypto.SSS
open LSpec


namespace Crypto.SSS.Test


def sublist (n : Nat) (xs : List a) : SlimCheck.Gen (List a) :=
  List.drop (xs.length - n) <$> SlimCheck.Gen.permutationOf xs

structure TestCase (p : Nat) where
  secret : Fp p
  parties : Nat
  threshold : Nat
  shares : Shares (Fp p) (Fp p)
deriving Repr

def genTestable (p : Nat) : SlimCheck.Gen (TestCase p) :=
  do
    let secret ← (Fp.randFp : Rand (Fp p))
    let parties ← SlimCheck.Gen.choose Nat 1 10
    let threshold ← SlimCheck.Gen.choose Nat 1 parties
    let shares ← (share secret threshold : Rand (PrivShares (Fp p) parties))
    let parties' ← SlimCheck.Gen.choose Nat 0 parties
    let shares' ← Shares.mk <$> sublist parties' shares.toShares.xys
    pure $ TestCase.mk secret parties threshold shares'

instance : SlimCheck.Shrinkable (TestCase p) where
  shrink _ := []

instance : SlimCheck.SampleableExt (TestCase p) :=
  SlimCheck.SampleableExt.mkSelfContained $ genTestable p

#lspec
  group "assemble"
    $ check "positive" (∀ tc : TestCase 101, tc.shares.count < tc.threshold ∨ tc.secret = assemble tc.shares)
    $ check "negative" (∀ tc : TestCase 223, tc.shares.count ≥ tc.threshold ↔ ¬ tc.shares.xys.length = 0 ∧ tc.secret = assemble tc.shares)
    -- FIXME: The negative test could fail due to coincidence!


end Crypto.SSS.Test
