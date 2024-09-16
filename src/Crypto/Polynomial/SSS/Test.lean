import Crypto.EllipticCurve
import Crypto.EllipticCurve.SECG.Secp256k1
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


namespace Sharing

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

end Sharing

namespace Commitment

  variable {p : Nat}
  variable {ec : EllipticCurve (Fp p)}

  structure TestCase  (g : EllipticCurve.Group ec) where
    secret : Fp g.n
    parties : Nat
    threshold : Nat
    shares : List (Fp g.n)
    comms : List (EllipticCurve.Point ec)
  deriving Repr

  instance : SlimCheck.Shrinkable (TestCase g) where
    shrink _ := []

  instance {g : EllipticCurve.Group ec} : SlimCheck.SampleableExt (TestCase g) :=
    SlimCheck.SampleableExt.mkSelfContained $
      do
        let secret ← (Fp.randFp : Rand (Fp g.n))
        let parties ← SlimCheck.Gen.choose Nat 1 10
        let threshold ← SlimCheck.Gen.choose Nat 1 parties
        let sc ← (shareWithCommitments secret threshold g.G : Rand (PrivShares (Fp g.n) parties × List (EllipticCurve.Point ec)))
        pure ⟨ secret , parties , threshold , sc.fst.ys.toList , sc.snd ⟩

  def verify (tc : TestCase g) : Bool :=
    List.and
      $ List.zipWith
        (fun i s => PrivShares.confirm (i + 1) (s * g.G) tc.comms)
        (List.range tc.shares.length)
        tc.shares

  #lspec check "confirm commitments" (∀ tc : TestCase EllipticCurve.Secp256k1, verify tc)

end Commitment

end Crypto.Polynomial.SSS.Test
