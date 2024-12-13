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

/- (σ →₀ ℤ) -/
/-
`Finsupp α M`, denoted `α →₀ M`, is the type of functions `f : α → M` such that
  `f x = 0` for all but finitely many `x`.

structure Finsupp (α : Type*) (M : Type*) [Zero M] where
  /-- The support of a finitely supported function (aka `Finsupp`). -/
  support : Finset α
  /-- The underlying function of a bundled finitely supported function (aka `Finsupp`). -/
  toFun : α → M
  /-- The witness that the support of a `Finsupp` is indeed the exact locus where its
  underlying function is nonzero. -/
  mem_support_toFun : ∀ a, a ∈ support ↔ toFun a ≠ 0
-/

-- By definition, AddMonoidAlgebra R M is the type "function from M to R with finite support"
-- In other words, AddMonoidAlgebra R M is (M →₀ R)
-- Thus we are saying that AddMonoidAlgebra R (σ →₀ ℤ) is ((σ →₀ ℤ) →₀ R)

-- single (a : G) (b : k) : k[G] := Finsupp.single a b
-- Finsupp.single {α : Type u_1} {M : Type u_5} [Zero M] (a : α) (b : M) : α →₀ M
-- single a b is the finitely supported function with value b at a and zero otherwise.

def constantMvLP (σ : Type*) (R : Type*) [CommSemiring R] (r : R) :
    MvLaurentPolynomial σ R :=
  Finsupp.single 0 r

-- Define x_n as the Laurent monomial with coefficient 1
def x (σ : Type*) (n : σ)(R : Type*) [CommSemiring R] : MvLaurentPolynomial σ R :=
  Finsupp.single (Finsupp.single n 1) 1



def x' (σ : Type*) (n : σ)(R : Type*) [CommSemiring R] : MvLaurentPolynomial σ R :=
  AddMonoidAlgebra.single (Finsupp.single n 1) 1

lemma x_eq_x' (σ : Type*) (n : σ) (R : Type*) [CommSemiring R] :
    x σ n R = x' σ n R := by
  exact rfl

-- Define the kth power of x_n as the Laurent monomial with coefficient 1
def x_pow_k (σ : Type*) (n : σ) (R : Type*) [CommSemiring R] (k : ℤ) : MvLaurentPolynomial σ R :=
  Finsupp.single (Finsupp.single n k) 1

def x'_pow_k (σ : Type*) (n : σ) (R : Type*) [CommSemiring R] (k : ℤ) : MvLaurentPolynomial σ R :=
  AddMonoidAlgebra.single (Finsupp.single n k) 1

lemma x_pow_k_eq_x'_pow_k (σ : Type*) (n : σ) (R : Type*) [CommSemiring R] (k : ℤ) :
    x_pow_k σ n R k = x'_pow_k σ n R k := by
  exact rfl

-- When k =1, the kth power of x_n is just x_n
lemma x_pow_1_eq_x (σ : Type*) (n : σ) (R : Type*) [CommSemiring R] :
    x_pow_k σ n R 1 = x σ n R := by
  exact rfl



namespace MvLaurentPolynomial
section Instances


-- The set of MvLaurentPolynomials indexed by σ with coefficients in R forms a `comm_semiring`.
instance commSemiring [CommSemiring R] : CommSemiring (MvLaurentPolynomial σ R) :=
  AddMonoidAlgebra.commSemiring

lemma x_times_x_pow_neg_1_eq_one (σ : Type*) (n : σ) (R : Type*) [CommSemiring R] :
    x σ n R * x_pow_k σ n R (-1) = 1 := by
    rw [x_eq_x',x_pow_k_eq_x'_pow_k]
    unfold x' x'_pow_k
    rw [AddMonoidAlgebra.single_mul_single]
    simp
    exact rfl


lemma x_pow_neg_1_times_x_eq_one (σ : Type*) (n : σ) (R : Type*) [CommSemiring R] :
    x_pow_k σ n R (-1) * x σ n R = 1 := by
    rw [x_eq_x',x_pow_k_eq_x'_pow_k]
    unfold x' x'_pow_k
    rw [AddMonoidAlgebra.single_mul_single]
    simp
    exact rfl


variable (σ : Type*) (R : Type*) [CommSemiring R]
variable (a : (MvLaurentPolynomial σ R))

-- The unit (i.e. the quadruple) associated to the monomial x_n
def x_unit (σ : Type*) (n : σ) (R : Type*) [CommSemiring R] : Units (MvLaurentPolynomial σ R) :=
  ⟨x σ n R, x_pow_k σ n R (-1), x_times_x_pow_neg_1_eq_one σ n R, x_pow_neg_1_times_x_eq_one σ n R⟩


-- The x_n's are units
lemma x_n_are_units (σ : Type*) (R : Type*) [CommSemiring R] :
  ∀ n : σ, IsUnit (x σ n R) := by
  intro n
  unfold x IsUnit
  use x_unit σ n R
  have this : ↑(x_unit σ n R) = x σ n R := by
    exact rfl
  rw [this]
  unfold x
  exact rfl


-- Defining the monomial m_i among all functions

def m_i {d : ℕ} (i : Fin d) : Finsupp (Fin d) ℤ :=
  ⟨{i},λ n ↦ if n = i then 1 else 0, by simp⟩

def m_i_neg {d : ℕ} (i : Fin d) : Finsupp (Fin d) ℤ :=
  ⟨{i},λ n ↦ if n = i then -1 else 0, by simp⟩

-- Single monomial with coefficient 1
def x_i {d : ℕ} (i : Fin d) : MvLaurentPolynomial (Fin d) ℤ :=
  ⟨{m_i i}, λ n ↦ if n = (m_i i) then 1 else 0, by simp⟩

def x_i_inv {d : ℕ} (i : Fin d) : MvLaurentPolynomial (Fin d) ℤ :=
  ⟨{m_i_neg i}, λ n ↦ if n = (m_i_neg i) then 1 else 0, by simp⟩

-- It is best to use the finsupp API in order to avoid having to unfold the definitions...

-- Non-zero monomial with coefficient k
def x_i_coeff_k (d : ℕ) (i : Fin d) (k : ℤ) (h : ¬k = 0) : MvLaurentPolynomial (Fin d) ℤ := by
  exact ⟨{m_i i}, λ n ↦ if n = (m_i i) then k else 0, by simp; apply h⟩

-- This is how we write the lower bound variable (1 + x₂)/x₁
def lower_bound (d : ℕ) (i₁ i₂ : Fin d) : MvLaurentPolynomial (Fin d) ℤ :=
  (1 + (x_i i₂))*(x_i_inv i₁)


-- Prove that the ring of Laurent polynomials has the structure Inv
instance : Inv (MvLaurentPolynomial σ R) := by admit

-- Prove that the ring of Laurent polynomials has the structure Div
instance : Div (MvLaurentPolynomial σ R) := by admit

instance : DivisionMonoid (MvLaurentPolynomial σ R) := by admit


--  A commutative semiring is in particular a commutative monoid. Useful for units
instance commMonoid [CommSemiring R] : CommMonoid (MvLaurentPolynomial σ R) := by
  exact inferInstance


lemma inverse_of_monomials (σ : Type*) (n : σ) (R : Type*) [CommSemiring R] : (x σ n R)⁻¹ = x_pow_k σ n R (-1) := by
  have h₂ : (x σ n R)⁻¹ = (x_unit σ n R)⁻¹.val := by admit
  rw [h₂]
  unfold x_unit
  simp


def lower_bounds (σ : Type*) (R : Type*) [CommSemiring R] (n₁ n₂ : σ) :
MvLaurentPolynomial σ R :=
  (1+ x σ n₂ R) * (x σ n₁ R)⁻¹



-- If equality in R is decidable and equality in σ is decidable, then equality in
-- `MvLaurentPolynomial σ R` is decidable
instance decidableEqMvLaurentPolynomial [CommSemiring R] [DecidableEq σ] [DecidableEq R] :
    DecidableEq (MvLaurentPolynomial σ R) :=
  Finsupp.instDecidableEq







-- The x_n's are linearly independent


-- Proof that `MvLaurentPolynomial σ R` is non-empty
instance inhabitedZero [CommSemiring R] : Inhabited (MvLaurentPolynomial σ R) :=
  ⟨0⟩

@[simp]
lemma silly0 (σ : Type*) (R : Type*) [CommSemiring R] :
(0 : MvLaurentPolynomial σ R) = constantMvLP σ R 0 := by
  unfold constantMvLP
  simp


lemma zeroHasEmptySupport : (0 : MvLaurentPolynomial σ R).support = ∅ := by
  exact rfl

lemma EmptySupportIsZero : (a.support = ∅) ↔ (a = 0) := by
  exact Finsupp.support_eq_empty

lemma zeroToFun : (0 : MvLaurentPolynomial σ R).toFun = 0 := by
  exact rfl




instance inhabitedOne [CommSemiring R] : Inhabited (MvLaurentPolynomial σ R) :=
  ⟨1⟩

@[simp]
lemma silly1 (σ : Type*) (R : Type*) [CommSemiring R] :
(1 : MvLaurentPolynomial σ R) = constantMvLP σ R 1 := by
  exact rfl













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
