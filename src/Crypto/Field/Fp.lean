namespace Crypto.Field


private def gcdExtended (a : Nat) (b : Nat) : Int × Int × Int :=
  if a = 0
    then ⟨ b , 0 , 1 ⟩
    else let ⟨ gcd , x' , y' ⟩ := gcdExtended (b % a) a
         let x := y' - (b / a) * x'
         let y := x'
         ⟨ gcd , x , y ⟩
termination_by a
decreasing_by
  simp_wf
  apply Nat.mod_lt
  apply Nat.zero_lt_of_ne_zero
  simp
  assumption


private def modExp (m : Nat) (x : Nat) (n : Nat) : Nat :=
  if n = 0
    then 1
    else let y := modExp m (x * x % m) (n / 2)
         if n % 2 = 1
           then x * y % m
           else y


-- FIXME: Consider using `{p : Nat // p > 0}` instead of `Nat`.
structure Fp (p : Nat) where
  private mkUnsafe ::
  val : Nat
deriving Repr, DecidableEq, BEq

namespace Fp

  def mk (x : Nat) : Fp p :=
    ⟨ x % p ⟩

  def canonical (x : Fp p) : Prop :=
    x.val < p

  def invertible (x : Fp p) : Prop :=
    let ⟨ gcd , _ , _ ⟩ := gcdExtended x.val p
    gcd = 1

  def inverse (x : Fp p) : Option (Fp p) :=
    let ⟨ gcd , xi , _ ⟩ := gcdExtended x.val p
    if gcd = 1
      then some ⟨ (xi % p).toNat ⟩
      else none

end Fp

instance : OfNat (Fp p) n where
  ofNat := Fp.mk n

instance : Add (Fp p) where
  add x y := ⟨ (x.val + y.val) % p ⟩

instance : Neg (Fp p) where
  neg x := ⟨ p - x.val % p ⟩

instance : Sub (Fp p) where
  sub x y := ⟨ (p + x.val - y.val) % p ⟩

instance : Mul (Fp p) where
  mul x y := ⟨ (x.val * y.val) % p ⟩

instance : Pow (Fp p) Nat where
  pow x n := ⟨ modExp p x.val n ⟩

-- FIXME: Unsafe!
instance : Div (Fp p) where
  div x y :=
    match Fp.inverse y with
    | some yi => x * yi
    | none => 0

instance : HDiv (Fp p) (Fp p) (Option (Fp p)) where
  hDiv x y := Functor.map (Mul.mul x) $ Fp.inverse y


-- FIXME: Remove this or develop it further.
structure NonZeroFp (p : Nat) where
  private mkUnsafe ::
  val : Nat
  nonzero : ¬ val % p = 0

namespace NonZeroFp

  def mk (x : Fp p) (h : ¬ x.val % p = 0) : NonZeroFp p :=
    NonZeroFp.mkUnsafe x.val h

  def fp (x : NonZeroFp p) : Fp p :=
    ⟨ x.val ⟩

/-
  private theorem invertible (x : NonZeroFp p) : (gcdExtended x.val p).fst = 1 := by
    rw [gcdExtended]
    simp
    sorry
-/
  -- FIXME: Strengthen this to yield `NonZeroFp p` instead of `Fp p`.
  def inverse (x : NonZeroFp p) : Fp p :=
    let ⟨ _ , xi , _⟩ := gcdExtended x.val p
    ⟨ (xi % p).toNat ⟩

end NonZeroFp

instance : HDiv (Fp p) (NonZeroFp p) (Fp p) where
  hDiv x y := x * y.inverse


end Crypto.Field
