import Crypto.Field.Fp
import Crypto.EllipticCurve

open Crypto
open Crypto.Field
open Crypto.EllipticCurve


namespace Crypto.EllipticCurve.Test


def testAdd (n : Nat) (ec : EllipticCurve (Fp n)) (px py qx qy rx ry : Fp n) : Prop :=
  let p : EllipticCurve.Point (Fp n) ec := EllipticCurve.Point.mk px py
  let q : EllipticCurve.Point (Fp n) ec := EllipticCurve.Point.mk qx qy
  let r : EllipticCurve.Point (Fp n) ec := EllipticCurve.Point.mk rx ry
  p + q = r

def testAdd' (n : Nat) (ec : EllipticCurve (Fp n)) (px py qx qy rx ry : Fp n) :=
  let p : EllipticCurve.Point (Fp n) ec := EllipticCurve.Point.mk px py
  let q : EllipticCurve.Point (Fp n) ec := EllipticCurve.Point.mk qx qy
  let r : EllipticCurve.Point (Fp n) ec := EllipticCurve.Point.mk rx ry
  p + q == r

-- https://www.cs.purdue.edu/homes/ssw/cs655/ec.pdf
example : testAdd 7 ⟨3,4⟩ 1 1 2 5 6 0 := by rfl
example : testAdd 7 ⟨3,4⟩ 1 1 2 5 6 0 := by rfl
example : testAdd 7 ⟨3,4⟩ 2 2 2 2 0 2 := by rfl
example : testAdd 2773 ⟨4,4⟩ 1 3 1 3 1771 705 := by rfl

-- https://math.umd.edu/~jmr/456/ellcurve.pdf
example : testAdd 5782975327 ⟨1,6⟩ 3 6 3 6 3212764070 2141842716 := by rfl
example : testAdd 5782975327 ⟨1,6⟩ 3 6 3 6 3212764070 2141842716 := by rfl
#eval testAdd' 5782975327 ⟨1,6⟩ 3 6 3212764070 2141842716 813230904 5658731715

-- https://asecuritysite.com/ecc/ecc_points_add2
-- https://andrea.corbellini.name/ecc/interactive/modk-add.html
example : testAdd 37 ⟨0,7⟩ 6 1 8 1 23 36 := by rfl
example : testAdd 37 ⟨0,7⟩ 6 1 9 12 19 13 := by rfl
example : testAdd 37 ⟨0,7⟩ 17 6 9 12 0 9 := by rfl
example : testAdd 7 ⟨3,4⟩ 0 2 1 1 0 5 := by rfl
example : testAdd 7 ⟨3,4⟩ 2 2 1 6 6 0 := by rfl
example : testAdd 7 ⟨3,4⟩ 2 2 1 1 5 2 := by rfl
example : testAdd 7 ⟨3,4⟩ 2 2 5 2 0 5 := by rfl

-- https://chatgpt.com/g/g-0S5FXLyFN-wolfram/c/80988174-31a1-4b14-a9cd-e656343aa0c2
example : testAdd 97 ⟨2,3⟩ 3 6 80 10 80 87 := by rfl

def testMul (n : Nat) (ec : EllipticCurve (Fp n)) (k : Nat) (px py rx ry : Fp n) :=
  let p : EllipticCurve.Point (Fp n) ec := EllipticCurve.Point.mk px py
  let r : EllipticCurve.Point (Fp n) ec := EllipticCurve.Point.mk rx ry
  k * p = r

def testMul' (n : Nat) (ec : EllipticCurve (Fp n)) (k : Nat) (px py rx ry : Fp n) :=
  let p : EllipticCurve.Point (Fp n) ec := EllipticCurve.Point.mk px py
  let r : EllipticCurve.Point (Fp n) ec := EllipticCurve.Point.mk rx ry
  Prod.mk (k * p == r)
    $ k * p

example : testMul 5782975327 ⟨1,6⟩ 1 3 6 3 6 := by rfl

-- https://math.umd.edu/~jmr/456/ellcurve.pdf
example : testMul 5782975327 ⟨1,6⟩ 2 3 6 3212764070 2141842716 := by rfl
#eval testMul' 5782975327 ⟨1,6⟩ 3 3 6 813230904 5658731715


-- https://andrea.corbellini.name/ecc/interactive/modk-mul.html
example : testMul 97 ⟨2,3⟩ 2 3 6 80 10 := by rfl
example : testMul 97 ⟨2,3⟩ 4 3 6 3 91 := by rfl
example : testMul 97 ⟨2,3⟩ 6 3 6 3 6 := by rfl


end Crypto.EllipticCurve.Test
