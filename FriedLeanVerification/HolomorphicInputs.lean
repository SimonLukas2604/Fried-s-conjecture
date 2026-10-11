module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Tactic

@[expose] public section

set_option warningAsError true
namespace FriedLeanVerification
open Filter Topology

/-- Evenness kills the first derivative at the origin. -/
theorem even_derivative_zero (f : ℂ → ℂ) (d : ℂ)
    (hd : HasDerivAt f d 0) (heven : ∀ z, f (-z) = f z) : d = 0 := by
  have hd' : HasDerivAt f d (-0) := by simpa using hd
  have hcomp := hd'.comp (0 : ℂ) (hasDerivAt_neg (0 : ℂ))
  simp only [mul_neg_one] at hcomp
  have heq : (f ∘ Neg.neg) = f := funext heven
  rw [heq] at hcomp
  have h := hd.unique hcomp
  linear_combination (1 / 2 : ℂ) * h

/-- An even analytic coefficient vanishing at zero has a quadratic analytic
factor. This is a single-parameter result; it does not claim continuity of the
factor as a metric parameter varies or prove the uniform spectral disk. -/
theorem even_analytic_quadratic_factor
    (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0)
    (heven : ∀ z, f (-z) = f z) (hzero : f 0 = 0) :
    ∃ q : ℂ → ℂ, AnalyticAt ℂ q 0 ∧ ∀ z, f z = z ^ 2 * q z := by
  have hd : deriv f 0 = 0 :=
    even_derivative_zero f (deriv f 0) hf.differentiableAt.hasDerivAt heven
  obtain ⟨q, hq, heq⟩ := hf.exists_eq_sum_add_pow_mul 2
  refine ⟨q, hq, ?_⟩
  intro z
  simpa [Finset.sum_range_succ, iteratedDeriv_succ, hd, hzero, smul_eq_mul] using heq z

/-- A nonzero constant coefficient of the quadratic quotient excludes all
nearby nonzero scalar characters. Joint continuity of the quotient is the
explicit metric-character input. -/
theorem quadratic_factor_eventually_nonzero
    (C : ℝ × ℝ → ℂ) (hC : ContinuousAt C (0, 0)) (hC0 : C (0, 0) ≠ 0) :
    ∀ᶠ p : ℝ × ℝ in 𝓝 (0, 0), p.1 ≠ 0 → (p.1 : ℂ) ^ 2 * C p ≠ 0 := by
  filter_upwards [hC.tendsto.eventually_ne hC0] with p hp hθ
  exact mul_ne_zero (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hθ)) hp

end FriedLeanVerification
