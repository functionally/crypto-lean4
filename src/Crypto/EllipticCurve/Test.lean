import Crypto.EllipticCurve
import Crypto.Field.Fp
import LSpec

open Crypto
open Crypto.EllipticCurve
open Crypto.Field
open LSpec


namespace Crypto.EllipticCurve.Test


def testAdd (n : Nat) (ec : EllipticCurve (Fp n)) (px py qx qy rx ry : Fp n) :=
  let p : EllipticCurve.Point ec := EllipticCurve.Point.mk px py
  let q : EllipticCurve.Point ec := EllipticCurve.Point.mk qx qy
  let r : EllipticCurve.Point ec := EllipticCurve.Point.mk rx ry
  p + q == r

#lspec group "add"
  $ (
      group "https://www.cs.purdue.edu/homes/ssw/cs655/ec.pdf"
        $ test "Case #1" (testAdd 7 ⟨3,4⟩ 1 1 2 5 6 0)
        $ test "Case #2" (testAdd 7 ⟨3,4⟩ 1 1 2 5 6 0)
        $ test "Case #3" (testAdd 7 ⟨3,4⟩ 2 2 2 2 0 2)
        $ test "Case #4" (testAdd 2773 ⟨4,4⟩ 1 3 1 3 1771 705)
    ) ++ (
      group "https://math.umd.edu/~jmr/456/ellcurve.pdf"
        $ test "Case #1" (testAdd 5782975327 ⟨1,6⟩ 3 6 3 6 3212764070 2141842716)
        $ test "Case #2" (testAdd 5782975327 ⟨1,6⟩ 3 6 3 6 3212764070 2141842716)
        $ test "Case #3" (testAdd 5782975327 ⟨1,6⟩ 3 6 3212764070 2141842716 813230904 5658731715)
    ) ++ (
      group "https://andrea.corbellini.name/ecc/interactive/modk-add.html"
        $ test "Case #1" (testAdd 37 ⟨0,7⟩ 6 1 8 1 23 36)
        $ test "Case #2" (testAdd 37 ⟨0,7⟩ 6 1 9 12 19 13)
        $ test "Case #3" (testAdd 37 ⟨0,7⟩ 17 6 9 12 0 9)
        $ test "Case #4" (testAdd 7 ⟨3,4⟩ 0 2 1 1 0 5)
        $ test "Case #5" (testAdd 7 ⟨3,4⟩ 2 2 1 6 6 0)
        $ test "Case #6" (testAdd 7 ⟨3,4⟩ 2 2 1 1 5 2)
        $ test "Case #7" (testAdd 7 ⟨3,4⟩ 2 2 5 2 0 5)
    ) ++ (
      group "https://chatgpt.com/g/g-0S5FXLyFN-wolfram/c/80988174-31a1-4b14-a9cd-e656343aa0c2"
        $ test "Case #1" (testAdd 97 ⟨2,3⟩ 3 6 80 10 80 87)
    )

-- FIXME: Test commutativity.
-- FIXME: Test associativity.


def testMul (n : Nat) (ec : EllipticCurve (Fp n)) (k : Nat) (px py rx ry : Fp n) :=
  let p : EllipticCurve.Point ec := EllipticCurve.Point.mk px py
  let r : EllipticCurve.Point ec := EllipticCurve.Point.mk rx ry
  k * p == r

#lspec group "mul"
  $ (
    group "https://math.umd.edu/~jmr/456/ellcurve.pdf"
        $ test "Case #1" (testMul 5782975327 ⟨1,6⟩ 1 3 6 3 6)
        $ test "Case #2" (testMul 5782975327 ⟨1,6⟩ 2 3 6 3212764070 2141842716)
        $ test "Case #3" (testMul 5782975327 ⟨1,6⟩ 3 3 6 813230904 5658731715)
  ) ++ (
    group "https://math.umd.edu/~jmr/456/ellcurve.pdf"
        $ test "Case #1" (testMul 5782975327 ⟨1,6⟩ 2 3 6 3212764070 2141842716)
        $ test "Case #2" (testMul 5782975327 ⟨1,6⟩ 3 3 6 813230904 5658731715)
  ) ++ (
    group "https://andrea.corbellini.name/ecc/interactive/modk-mul.html"
        $ test "Case #1" (testMul 97 ⟨2,3⟩ 2 3 6 80 10)
        $ test "Case #2" (testMul 97 ⟨2,3⟩ 4 3 6 3 91)
        $ test "Case #3" (testMul 97 ⟨2,3⟩ 6 3 6 3 6)
  )

-- FIXME: Test commutativity.
-- FIXME: Test associativity.


end Crypto.EllipticCurve.Test
