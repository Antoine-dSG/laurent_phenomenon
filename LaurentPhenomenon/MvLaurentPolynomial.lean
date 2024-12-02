import Mathlib.Tactic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Group.Units
import Mathlib.Data.Finsupp.Defs

-- This is heavily inspired by the file MvPolynomials.lean in mathlib.

noncomputable section

open Set Function Finsupp AddMonoidAlgebra
open scoped Pointwise

-- We define the type of Laurent polynomials in `n` variables with coefficients in `ℤ`.
def MvLaurentPolynomial (σ : Type*) (R : Type*) [CommSemiring R] :=
  AddMonoidAlgebra R (σ →₀ ℤ)


namespace MvLaurentPolynomial
-- We list a few instances for multivariate Laurent polynomials. These are copied from the
-- multivariate polynomial file.
section Instances



-- The set of MvLaurentPolynomials indexed by σ with coefficients in R forms a `comm_semiring`.
instance commSemiring [CommSemiring R] : CommSemiring (MvLaurentPolynomial σ R) :=
  AddMonoidAlgebra.commSemiring

variable (σ : Type*) (R : Type*) [CommSemiring R]
variable (a : (MvLaurentPolynomial σ R))

-- Proof that `MvLaurentPolynomial σ R` is non-empty
instance inhabitedZero [CommSemiring R] : Inhabited (MvLaurentPolynomial σ R) :=
  ⟨0⟩
lemma zeroHasEmptySupport : (0 : MvLaurentPolynomial σ R).support = ∅ := by
  exact rfl

lemma EmptySupportIsZero : (a.support = ∅) ↔ (a = 0) := by
  exact Finsupp.support_eq_empty

lemma zeroToFun : (0 : MvLaurentPolynomial σ R).toFun = 0 := by
  exact rfl

instance inhabitedOne [CommSemiring R] : Inhabited (MvLaurentPolynomial σ R) :=
  ⟨1⟩




--  A commutative semiring is in particular a commutative monoid. Useful for units
instance commMonoid [CommSemiring R] : CommMonoid (MvLaurentPolynomial σ R) := by
  exact inferInstance
-- If equality in R is decidable and equality in σ is decidable, then equality in
-- `MvLaurentPolynomial σ R` is decidable
instance decidableEqMvLaurentPolynomial [CommSemiring R] [DecidableEq σ] [DecidableEq R] :
    DecidableEq (MvLaurentPolynomial σ R) :=
  Finsupp.instDecidableEq
/- An action by a monoid on the coefficients induces an action on the commutative semiring of multivariate
 Laurent polynomials. -/
instance distribuMulAction [Monoid R] [CommSemiring S₁] [DistribMulAction R S₁] :
    DistribMulAction R (MvLaurentPolynomial σ S₁) :=
  AddMonoidAlgebra.distribMulAction

/- If the coefficient semiring S₁ has a scalar multiplication by R, then so does the ring of multivariate Laurent polynomials
 with coefficients in S₁ -/
instance smulZeroClass [CommSemiring S₁] [SMulZeroClass R S₁] :
    SMulZeroClass R (MvLaurentPolynomial σ S₁) :=
  AddMonoidAlgebra.smulZeroClass

/- If the coefficient semiring S₁ has a faithful multiplication by R, then so does the ring of multivariate Laurent polynomials
 with coefficients in S₁ -/
instance faithfulSMul [CommSemiring S₁] [SMulZeroClass R S₁] [FaithfulSMul R S₁] :
    FaithfulSMul R (MvLaurentPolynomial σ S₁) :=
  AddMonoidAlgebra.faithfulSMul

instance module [Semiring R] [CommSemiring S₁] [Module R S₁] : Module R (MvLaurentPolynomial σ S₁) :=
  AddMonoidAlgebra.module

instance isScalarTower [CommSemiring S₂] [SMul R S₁] [SMulZeroClass R S₂] [SMulZeroClass S₁ S₂]
    [IsScalarTower R S₁ S₂] : IsScalarTower R S₁ (MvLaurentPolynomial σ S₂) :=
  AddMonoidAlgebra.isScalarTower

instance smulCommClass [CommSemiring S₂] [SMulZeroClass R S₂] [SMulZeroClass S₁ S₂]
    [SMulCommClass R S₁ S₂] : SMulCommClass R S₁ (MvLaurentPolynomial σ S₂) :=
  AddMonoidAlgebra.smulCommClass

instance isCentralScalar [CommSemiring S₁] [SMulZeroClass R S₁] [SMulZeroClass Rᵐᵒᵖ S₁]
    [IsCentralScalar R S₁] : IsCentralScalar R (MvLaurentPolynomial σ S₁) :=
  AddMonoidAlgebra.isCentralScalar

instance algebra [CommSemiring R] [CommSemiring S₁] [Algebra R S₁] :
    Algebra R (MvLaurentPolynomial σ S₁) :=
  AddMonoidAlgebra.algebra

instance isScalarTower_right [CommSemiring S₁] [DistribSMul R S₁] [IsScalarTower R S₁ S₁] :
    IsScalarTower R (MvLaurentPolynomial σ S₁) (MvLaurentPolynomial σ S₁) :=
  AddMonoidAlgebra.isScalarTower_self _

instance smulCommClass_right [CommSemiring S₁] [DistribSMul R S₁] [SMulCommClass R S₁ S₁] :
    SMulCommClass R (MvLaurentPolynomial σ S₁) (MvLaurentPolynomial σ S₁) :=
  AddMonoidAlgebra.smulCommClass_self _

/-- If `R` is a subsingleton, then `MvLaurentPolynomial σ R` has a unique element -/
instance unique [CommSemiring R] [Subsingleton R] : Unique (MvLaurentPolynomial σ R) :=
  AddMonoidAlgebra.unique

end Instances

variable [CommSemiring R] [CommSemiring S₁] {p q : MvLaurentPolynomial σ R}

/-- `LaurentMonomial s a` is the Laurent monomial with coefficient `a` and exponents given by `s`  -/
def LaurentMonomial (s : σ →₀ ℤ) : R →ₗ[R] MvLaurentPolynomial σ R :=
 lsingle s

theorem single_eq_LaurentMonomial (s : σ →₀ ℤ) (a : R) : Finsupp.single s a = LaurentMonomial s a :=
  rfl

/- Multiplication of multivariate Laurent Polynomials -/
/- p.sum fun m a => ... iterates over each term
of the polynomial p, where m represents the exponents
of the term and a represents the coefficient.-/
theorem mul_def : p * q =
p.sum fun m a =>
  q.sum fun n b =>
    LaurentMonomial (m + n) (a * b) := by
  apply AddMonoidAlgebra.mul_def


@[simp]
theorem LaurentMonomial_mul (s s' : σ→₀ℤ) (a a' : R) : LaurentMonomial s a * LaurentMonomial s' a' = LaurentMonomial (s+s') (a*a') := by
  apply AddMonoidAlgebra.single_mul_single


def C : R →+* MvLaurentPolynomial σ R :=
  { singleZeroRingHom with toFun := LaurentMonomial 0 }

variable (R σ)

@[simp]
theorem algebraMap_eq [CommSemiring R] : algebraMap R (MvLaurentPolynomial σ R) = C :=
  rfl

variable {R σ}

/-- `X n` is the evaluation of the degree `1` monomial $X_n$. -/
def X [CommSemiring R] (n : σ) : MvLaurentPolynomial σ R :=
  LaurentMonomial (Finsupp.single n 1) 1

theorem LaurentMonomial_left_injective [CommSemiring R] {r : R} (hr : r ≠ 0) :
    Function.Injective fun s : σ →₀ ℤ => LaurentMonomial s r :=
  Finsupp.single_left_injective hr

-- Two Laurent monomials with the same non-zero coefficient are equal iff they have the same exponents.
@[simp]
theorem LaurentMonomial_exp_inj [CommSemiring R] {s t : σ →₀ ℤ} {r : R} (hr : r ≠ 0) :
    LaurentMonomial s r = LaurentMonomial t r ↔ s = t :=
  Finsupp.single_left_inj hr

-- Two Laurent monomials with same exponent are equal iff they have the same coefficient.
@[simp]
theorem LaurentMonomial_coef_inj [CommSemiring R] {s : σ →₀ ℤ} {r₁ r₂ : R} :
    LaurentMonomial s r₁ = LaurentMonomial s r₂ ↔ r₁ = r₂ := by
    constructor
    intro h
    rw [←single_eq_LaurentMonomial, ←single_eq_LaurentMonomial] at h
    apply Finsupp.single_injective s
    assumption
    · intro H
      rw [H]

theorem C_apply [CommSemiring R] : (C a : MvLaurentPolynomial σ R) = LaurentMonomial 0 a :=
rfl

@[simp]
theorem C_0 [CommSemiring R] : C 0 = (0 : MvLaurentPolynomial σ R) := map_zero _

@[simp]
theorem C_1 [CommSemiring R] : C 1 = (1 : MvLaurentPolynomial σ R) :=
rfl

@[simp]
theorem C_mul_LaurentMonomial [CommSemiring R] : C (a : R) * LaurentMonomial s a' = LaurentMonomial s (a*a') := by
  rw [C_apply]
  rw [LaurentMonomial_mul]
  simp

@[simp]
theorem C_add [CommSemiring R] : (C ((a : R) + a') : MvLaurentPolynomial σ R) = C a + C a' := by
  simp

@[simp]
theorem C_mul [CommSemiring R] : (C (a * a') : MvLaurentPolynomial σ R) = C a * C a' := by
  simp

@[simp]
theorem C_pow [CommSemiring R] (a : R) (n : ℕ) : (C (a ^ n) : MvLaurentPolynomial σ R) = C a ^ n := by
  simp

theorem C_injective (σ : Type*) (R : Type*) [CommSemiring R] :
    Function.Injective (C : R → MvLaurentPolynomial σ R) :=
    Finsupp.single_injective _



@[simp]
theorem C_inj {σ : Type*} (R : Type*) [CommSemiring R] (r s : R) :
    (C r : MvLaurentPolynomial σ R) = C s ↔ r = s :=
    (C_injective σ R).eq_iff



theorem C_surjective {R : Type*} [CommSemiring R] (σ : Type*) [IsEmpty σ] :
    Function.Surjective (C : R → MvLaurentPolynomial σ R) := by
    refine fun p => ⟨p.toFun 0, Finsupp.ext fun a => ?_⟩
    simp only [C_apply, ← single_eq_LaurentMonomial, (Finsupp.ext isEmptyElim (α := σ) : a = 0),
    single_eq_same]
    rfl

-- We need to spell out more of the algebraic structure to make this work.
-- 1) Additive identity of MvLaurentPolynomial
-- 2) Additive inverse of MvLaurentPolynomial
-- 3) Multiplicative identity of MvLaurentPolynomial
-- 4) Multiplicative inverse of MvLaurentMonomial
-- 5) Determine set of units in MvLaurentPolynomial

variable (R : Type*) [CommSemiring R]

-- 1) Define which elements are invertible in the Laurent polynomial ring.
theorem LMonomial_IsUnit (s₁ : σ →₀ ℤ) (r₁ r₂ : R) (hr : r₁*r₂ = 1) :
∃ (s₂ : σ →₀ ℤ), LaurentMonomial s₁ r₁ * LaurentMonomial s₂ r₂ = 1 := by
  use -s₁
  rw [LaurentMonomial_mul, hr]
  simp
  admit






/-- Divide by `LaurentMonomial 1 s`, discarding terms not divisible by this. -/
def divLMonomial {R : Type*} [CommSemiring R] (p : MvLaurentPolynomial σ R) (s : σ →₀ ℤ) : MvLaurentPolynomial σ R :=
  AddMonoidAlgebra.divOf p s

-- Definition in type A₂ :
def X1 : MvLaurentPolynomial ℕ ℤ := X 1
def X2 : MvLaurentPolynomial ℕ ℤ := X 2
def X3 : MvLaurentPolynomial ℕ ℤ := sorry
  -- (C 1 + X 1)/ (X 2)
  -- This currently doesn't work
  -- We need to define division first
def X4 : MvLaurentPolynomial ℕ ℤ := sorry
def X5 : MvLaurentPolynomial ℕ ℤ := sorry
