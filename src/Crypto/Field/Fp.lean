namespace Crypto.Field


inductive Fp (p : Int) where
| mk : Int → Fp p
| infinity : Fp p
deriving Repr

namespace Fp

  def wellFormed : Fp p → Prop
  | mk x => x % p = x
  | infinity => True

end Fp

instance : BEq (Fp p) where
  beq
  | Fp.mk x, Fp.mk y => x % p == y % p
  | Fp.infinity, Fp.infinity => true
  | Fp.infinity, _ => false
  | _, Fp.infinity => false

instance : OfNat (Fp p) n where
  ofNat := Fp.mk n

instance : Add (Fp p) where
  add x y := Fp.mk $ (x.value + y.value) % p

instance : Sub (Fp p) where
  sub x y := ⟨ (x.value - y.value) % p ⟩

instance : Mul (Fp p) where
  mul x y := ⟨ (x.value * y.value) % p ⟩

private partial def gcdExtended (a : Int) (b : Int) : Int × Int × Int :=
  -- FIXME: Prove termination.
  if a == 0
    then ⟨ b, 0, 1 ⟩
    else let ⟨ gcd, x', y' ⟩ := gcdExtended (b % a) a
         let x := y' - (b / a) * x'
         let y := x'
         ⟨ gcd, x, y ⟩

def inverse (x : Fp p) : Fp p :=
  let ⟨ gcd , y , _ ⟩ := gcdExtended x.value p
  if gcd == 1
    then ⟨ y ⟩
    else none

instance : Div (Fp p) where
  div x y := x * inverse y

instance : Neg (Fp p) where
  neg x := ⟨ (- x.value) % p ⟩

private partial def modExp (m : Int) (x : Int) : Nat → Int
  -- FIXME: Prove termination.
  | 0 => 1
  | n => let y := modExp m (x * x % m) (n / 2)
         if n % 2 == 1
           then x * y % m
           else y

instance : Pow (Fp p) Nat where
  pow x n := ⟨ modExp p x.value n ⟩

/-
private theorem power_zero (x : Fp p) : Pow.pow x 0 = ⟨ 1 ⟩ := by
  simp [Pow.pow, modExp]

private theorem power_one (x : Fp p) : Fp.wellFormed x → x = Pow.pow x 1 := by
  intro h
  simp [Pow.pow, modExp]
  rw [h]

-- FIXME: Prove the general case.
-/

/-x
inductive Montgomery (p : Int) where
| mk (r : Fp p) (rinv : Fp p) : Option.isSome (inverse r) → Montgomery p

#check Montgomery.mk ⟨ 1 ⟩ ⟨ 2 ⟩
-/

/-
structure Montgomery (p : Int) where
  r : Fp p
--valid  := Option.isSome (inverse r) = true
  valid  := Option.isSome (inverse r) = true
  rinv : Fp p :=
    let h := valid = true
    Option.get (inverse r) $ by
      sorry
-/

end Crypto.Field
