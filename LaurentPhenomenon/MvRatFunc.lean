import Mathlib.FieldTheory.RatFunc.Defs
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.OreLocalization.Ring
import Mathlib.RingTheory.Polynomial.Basic

noncomputable section
-- Definition of the field of fractions of a multivariable polynomial ring
def MvRatFunc (σ : Type*) :=
  (OreLocalization (nonZeroDivisors (MvPolynomial σ ℚ)) (MvPolynomial σ ℚ))

-- The set of rational function is a field
instance (σ : Type*) : Field (MvRatFunc σ) :=
  OreLocalization.instFieldNonZeroDivisors

end
