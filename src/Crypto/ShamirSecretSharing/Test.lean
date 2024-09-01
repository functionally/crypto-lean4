import LSpec
import Crypto.Field.Fp
import Crypto.ShamirSecretSharing
import Mathlib.Control.Random

open Crypto.Field
open Crypto.ShamirSecretSharing
open LSpec


namespace Crypt.ShamirSecretSharing.Test


def sublist (n : Nat) (xs : List a) : SlimCheck.Gen (List a) :=
  List.drop (xs.length - n) <$> SlimCheck.Gen.permutationOf xs

structure TestCase (p : Nat) where
  secret : Fp p
  parties : Nat
  trust : Nat
  shares : List (Share (Fp p))
deriving Repr

def genTestable (p : Nat) : SlimCheck.Gen (TestCase p) :=
  do
    let secret ← (Fp.randFp : Rand (Fp p))
    let parties ← SlimCheck.Gen.choose Nat 1 10
    let trust ← SlimCheck.Gen.choose Nat 1 parties
    let shares ← (share secret trust parties : Rand (List (Share (Fp p))))
    let parties' ← SlimCheck.Gen.choose Nat 0 parties
    let shares' ← sublist parties' shares
    pure $ TestCase.mk secret parties trust shares'

instance : SlimCheck.Shrinkable (TestCase p) where
  shrink _ := []

instance : SlimCheck.SampleableExt (TestCase p) :=
  SlimCheck.SampleableExt.mkSelfContained $ genTestable p

#lspec
  group "sharePolynomial_recover"
    $ check "positive" (∀ tc : TestCase 101, tc.shares.length < tc.trust ∨ tc.secret = recover tc.shares)
    $ check "negative" (∀ tc : TestCase 223, tc.shares.length ≥ tc.trust ↔ ¬ tc.shares.length = 0 ∧ tc.secret = recover tc.shares)
    -- FIXME: The negative test could fail due to coincidence!


end Crypt.ShamirSecretSharing.Test
