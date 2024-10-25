import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Tactic

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

-- If equality in R is decidable and equality in σ is decidable, then equality in
-- `MvLaurentPolynomial σ R` is decidable
instance decidableEqMvLaurentPolynomial [CommSemiring R] [DecidableEq σ] [DecidableEq R] :
    DecidableEq (MvLaurentPolynomial σ R) :=
  Finsupp.instDecidableEq

-- The set of MvLaurentPolynomials indexed by σ with coefficients in R forms a `comm_semiring`.
instance commSemiring [CommSemiring R] : CommSemiring (MvLaurentPolynomial σ R) :=
  AddMonoidAlgebra.commSemiring

-- Proof that `MvLaurentPolynomial σ R` is non-empty
instance inhabited [CommSemiring R] : Inhabited (MvLaurentPolynomial σ R) :=
  ⟨0⟩

-- An action by a monoid on the coefficients induces an action on the commutative semiring of multivariate
-- Laurent polynomials.
instance distribuMulAction [Monoid R] [CommSemiring S₁] [DistribMulAction R S₁] :
    DistribMulAction R (MvLaurentPolynomial σ S₁) :=
  AddMonoidAlgebra.distribMulAction


instance smulZeroClass [CommSemiring S₁] [SMulZeroClass R S₁] :
    SMulZeroClass R (MvLaurentPolynomial σ S₁) :=
  AddMonoidAlgebra.smulZeroClass

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

theorem mul_def : p * q = p.sum fun m a => q.sum fun n b => LaurentMonomial (m + n) (a * b) :=
  AddMonoidAlgebra.mul_def

/-- `C a` is the constant polynomial with value `a` -/
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
