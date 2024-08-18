import Crypto.Field.Fp
import Crypto.EllipticCurve

open Crypto
open Crypto.Field
open Crypto.EllipticCurve


private def testAdd (n : Nat) (ec : EllipticCurve (Fp n)) (px py qx qy rx ry : Fp n) : Prop :=
  let p : EllipticCurve.Point (Fp n) ec := EllipticCurve.Point.mk px py
  let q : EllipticCurve.Point (Fp n) ec := EllipticCurve.Point.mk qx qy
  let r : EllipticCurve.Point (Fp n) ec := EllipticCurve.Point.mk rx ry
  p + q = r

private def testAdd' (n : Nat) (ec : EllipticCurve (Fp n)) (px py qx qy rx ry : Fp n) :=
  let p : EllipticCurve.Point (Fp n) ec := EllipticCurve.Point.mk px py
  let q : EllipticCurve.Point (Fp n) ec := EllipticCurve.Point.mk qx qy
  let r : EllipticCurve.Point (Fp n) ec := EllipticCurve.Point.mk rx ry
  Prod.mk (p + q == r)
    $ Prod.mk (p + q) r

-- https://www.cs.purdue.edu/homes/ssw/cs655/ec.pdf
example : testAdd 7 ⟨3,4⟩ 1 1 2 5 6 0 := by rfl
example : testAdd 7 ⟨3,4⟩ 1 1 2 5 6 0 := by rfl
example : testAdd 7 ⟨3,4⟩ 2 2 2 2 0 2 := by rfl
example : testAdd 2773 ⟨4,4⟩ 1 3 1 3 1771 705 := by rfl

-- https://math.umd.edu/~jmr/456/ellcurve.pdf
example : testAdd 5782975327 ⟨1,6⟩ 3 6 3 6 3212764070 2141842716 := by rfl
example : testAdd 5782975327 ⟨1,6⟩ 3 6 3 6 3212764070 2141842716 := by rfl
#eval (testAdd' 5782975327 ⟨1,6⟩ 3 6 3212764070 2141842716 813230904 5658731715).fst

-- https://asecuritysite.com/ecc/ecc_points_add2
-- https://andrea.corbellini.name/ecc/interactive/modk-add.html
example : testAdd 37 ⟨0,7⟩ 6 1 8 1 23 36 := by rfl
example : testAdd 37 ⟨0,7⟩ 6 1 9 12 19 13 := by rfl
example : testAdd 37 ⟨0,7⟩ 17 6 9 12 0 9 := by rfl
example : testAdd 7 ⟨3,4⟩ 0 2 1 1 0 5 := by rfl
example : testAdd 7 ⟨3,4⟩ 2 2 1 6 6 0 := by rfl
example : testAdd 7 ⟨3,4⟩ 2 2 1 1 5 2 := by rfl
example : testAdd 7 ⟨3,4⟩ 2 2 5 2 0 5 := by rfl
