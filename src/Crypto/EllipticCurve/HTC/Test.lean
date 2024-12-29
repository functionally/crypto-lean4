import Crypto.EllipticCurve
import Crypto.EllipticCurve.HTC
import Crypto.EllipticCurve.SECG.Secp256k1
import Crypto.Field.Fp
import LSpec

open Crypto
open Crypto.EllipticCurve.HTC
open Crypto.Field
open LSpec


namespace Crypto.EllipticCurve.HTC.Test


abbrev p1 := 43
abbrev F1 := Fp p1
def hasSqrt1 : Fp.Is3Mod4 p1 := rfl
instance iSqrt1 : Sqrt F1 := Fp.instSqrt3Mod4 hasSqrt1
def ec1 : EllipticCurve (Fp p1) := ⟨ 0, 7 ⟩

abbrev p2 := 10099
abbrev F2 := Fp p2
def hasSqrt2 : Fp.Is3Mod4 p2 := rfl
instance iSqrt2 : Sqrt F2 := Fp.instSqrt3Mod4 hasSqrt2
def ec2 : EllipticCurve (Fp p2) := ⟨ 0, 7 ⟩

abbrev p := Secp256k1.p
abbrev F := Secp256k1.F
theorem hasSqrt : Fp.Is3Mod4 p := rfl
instance iSqrt : Sqrt F := Fp.instSqrt3Mod4 hasSqrt
def ec := Secp256k1.curve

instance : SlimCheck.Shrinkable F where
  shrink _ := []

instance : SlimCheck.SampleableExt F :=
  SlimCheck.SampleableExt.mkSelfContained
    $ do
      let x ← (Fp.randFp : Rand F)
      pure x

#lspec group "Map to point"
  $ group "tryAndIncrement"
    (
      group "https://asecuritysite.com/hash/hash_to_ecc"
      (
        test "y^2=x^3+7, p = 43, x = 10" (
          let expected : EllipticCurve.Point ec1 := EllipticCurve.Point.mk 12 31
          MapToCurve.tryAndIncrement 10 = expected
        )
      $ test "y^2=x^3+7, p = 43, x = 12" (
          let expected : EllipticCurve.Point ec1 := EllipticCurve.Point.mk 12 31
          MapToCurve.tryAndIncrement 12 = expected
        )
      $ test "y^2=x^3+7, p = 10099, x = 1032" (
          let expected : EllipticCurve.Point ec2 := EllipticCurve.Point.mk 1036 1112
          MapToCurve.tryAndIncrement 1032 = expected
        )
      $ test "y^2=x^3+7, p = 10099, x = 1030" (
          let expected : EllipticCurve.Point ec2 := EllipticCurve.Point.mk 1036 1112
          MapToCurve.tryAndIncrement 1032 = expected
        )
      )
    $ check "On curve" (
        ∀ x : F,
        let actual : EllipticCurve.Point ec := MapToCurve.tryAndIncrement x
        EllipticCurve.Point.onCurve' actual
      )
    )

end Crypto.EllipticCurve.HTC.Test
