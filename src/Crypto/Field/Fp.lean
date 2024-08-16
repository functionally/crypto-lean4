namespace Crypto.Field


private def gcdExtended (a : Nat) (b : Nat) : Nat × Nat × Nat :=
  if a = 0
    then ⟨ b, 0, 1 ⟩
    else let ⟨ gcd, x', y' ⟩ := gcdExtended (b % a) a
         let x := y' - (b / a) * x'
         let y := x'
         ⟨ gcd, x, y ⟩
termination_by a
decreasing_by
  simp_wf
  apply Nat.mod_lt
  apply Nat.zero_lt_of_ne_zero
  assumption

private def modExp (m : Nat) (x : Nat) (n : Nat) : Nat :=
  if n = 0
    then 1
    else let y := modExp m (x * x % m) (n / 2)
         if n % 2 == 1
           then x * y % m
           else y


structure Fp (p : Nat) where
  private mkUnsafe ::
  val : Nat
deriving Repr

namespace Fp

  def mk (x : Nat) : Fp p :=
    Fp.mkUnsafe $ x % p

  def canonical (x : Fp p) : Prop :=
    x.val < p

  def nonzero (x : Fp p) : Prop :=
    ¬ x.val % p = 0

  def invertible (x : Fp p) : Prop :=
    let ⟨ gcd , _ , _ ⟩ := gcdExtended x.val p
    gcd = 1

  /-
  theorem nonzero_invertible (x : Fp p) : nonzero x → invertible x := by
    sorry

  theorem invertible_nonzero (x : Fp p) : invertible x → nonzero x := by
    sorry
  -/

  def inverse (x : Fp p) : Option (Fp p) :=
    let ⟨ gcd , y , _ ⟩ := gcdExtended x.val p
    if gcd = 1
      then some ⟨ y ⟩
      else none

end Fp

instance : BEq (Fp p) where
  beq x y := x.val % p == y.val % p

instance : OfNat (Fp p) n where
  ofNat := Fp.mk n

instance : Add (Fp p) where
  add x y := ⟨ (x.val + y.val) % p ⟩

instance : Neg (Fp p) where
  neg x := ⟨ (p - x.val) % p ⟩

instance : Sub (Fp p) where
  sub x y := ⟨ (x.val - y.val) % p ⟩

instance : Mul (Fp p) where
  mul x y := ⟨ (x.val * y.val) % p ⟩

/-
instance : Div (Fp p) where
  div x y := x * Fp.inverse y
-/

instance : Pow (Fp p) Nat where
  pow x n := ⟨ modExp p x.val n ⟩

end Crypto.Field
