import Crypto.Field.Fp
import Crypto.Polynomial.SSS
import LSpec
import Mathlib.Control.Random

open Crypto.Field
open Crypto.Polynomial.SSS
open LSpec


namespace Crypto.Polynomial.SSS.Test


def sublist (n : Nat) (xs : List a) : SlimCheck.Gen (List a) :=
  List.drop (xs.length - n) <$> SlimCheck.Gen.permutationOf xs

structure TestCase (p : Nat) where
  secret : Fp p
  parties : Nat
  threshold : Nat
  shares : Shares (Fp p) (Fp p)
deriving Repr

instance : SlimCheck.Shrinkable (TestCase p) where
  shrink _ := []

instance : SlimCheck.SampleableExt (TestCase p) :=
  SlimCheck.SampleableExt.mkSelfContained $
    do
      let secret ← (Fp.randFp : Rand (Fp p))
      let parties ← SlimCheck.Gen.choose Nat 1 10
      let threshold ← SlimCheck.Gen.choose Nat 1 parties
      let shares ← (share secret threshold : Rand (PrivShares (Fp p) parties))
      let parties' ← SlimCheck.Gen.choose Nat 0 parties
      let shares' ← Shares.mk <$> sublist parties' shares.toShares.xys
      pure $ TestCase.mk secret parties threshold shares'

#lspec
  group "assemble"
    $ check "Fp 101" (∀ tc : TestCase 101, tc.shares.count < tc.threshold ∨ tc.secret = assemble tc.shares)
    $ check "Fp 223" (∀ tc : TestCase 223, tc.shares.count < tc.threshold ∨ tc.secret = assemble tc.shares)


end Crypto.Polynomial.SSS.Test
