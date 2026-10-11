module

public import FriedLeanVerification.CrossingConsequences

@[expose] public section

set_option warningAsError true
namespace FriedLeanVerification
open Filter Topology

/-- A conditional assembly of crossing selection, the normalized-ratio limit,
and eventual strict discrepancy for an ordinary value function. Every
coefficient, divisor, variation-bound, and calibration input is a hypothesis.
This does not instantiate them using a hyperbolic manifold or Ruelle zeta. -/
theorem conditional_crossing_obstruction
    (θ : ℕ → ℝ) (K r Kvar : ℝ) (hK : 0 < K) (hr : 0 < r)
    (base perturb : ℕ → ℝ → ℝ)
    (hθpos : ∀ n, 0 < θ n) (hθ : Tendsto θ atTop (𝓝 0))
    (hleft : ∀ n, base n 0 + (θ n) ^ 2 * perturb n 0 < 0)
    (haxis : ∀ n τ, τ ∈ Set.Icc 0 (4 * K * (θ n) ^ 2 / r) →
      r / 2 * τ ≤ base n τ)
    (hbound : ∀ n τ, τ ∈ Set.Icc 0 (4 * K * (θ n) ^ 2 / r) →
      |perturb n τ| ≤ K)
    (hcont : ∀ n, ContinuousOn (fun τ => base n τ + (θ n) ^ 2 * perturb n τ)
      (Set.Icc 0 (4 * K * (θ n) ^ 2 / r)))
    (C A : ℝ × ℝ → ℂ)
    (hC : ContinuousAt C (0, 0)) (hA : ContinuousAt A (0, 0))
    (hC0 : C (0, 0) ≠ 0) (hA0 : A (0, 0) = 0)
    (G₀ : ℕ → ℂ) (u Z : ℕ → ℝ → ℂ) (target : ℕ → ℝ)
    (hG₀ : ∀ᶠ n in atTop, G₀ n ≠ 0)
    (huBound : ∀ n τ, τ ∈ Set.Icc 0 (4 * K * (θ n) ^ 2 / r) →
      ‖u n τ‖ ≤ Kvar * |τ|)
    (hZbase : ∀ n, Z n 0 = -G₀ n * (((θ n : ℂ) ^ 2 * C (θ n, 0)) ^ 2))
    (hZcross : ∀ n τ, base n τ + (θ n) ^ 2 * perturb n τ = 0 →
      Z n τ = (G₀ n * Complex.exp (u n τ)) *
        ((θ n : ℂ) ^ 2 * C (θ n, τ)) * ((θ n : ℂ) ^ 2 * A (θ n, τ)))
    (hcalibration : ∀ᶠ n in atTop, target n = ‖Z n 0‖) :
    ∃ σ : ℕ → ℝ,
      Tendsto σ atTop (𝓝 0) ∧
      (∀ n, 0 < σ n ∧ σ n ≤ 4 * K * (θ n) ^ 2 / r ∧
        base n (σ n) + (θ n) ^ 2 * perturb n (σ n) = 0) ∧
      Tendsto (fun n => Z n (σ n) / Z n 0) atTop (𝓝 (0 : ℂ)) ∧
      (∀ᶠ n in atTop, 0 < target n ∧ ‖Z n (σ n)‖ < target n ∧
        ‖Z n (σ n)‖ ≠ target n) := by
  obtain ⟨σ, hσ, hroots⟩ := crossing_sequence_exists θ K r hK hr base perturb
    hθpos hθ hleft haxis hbound hcont
  have hθne : ∀ n, θ n ≠ 0 := fun n => ne_of_gt (hθpos n)
  have hu : ∀ᶠ n in atTop, ‖u n (σ n)‖ ≤ Kvar * |σ n| := by
    filter_upwards with n
    exact huBound n (σ n) ⟨(hroots n).1.le, (hroots n).2.1⟩
  have hlim := abstract_counterexample_ratio θ σ G₀ (fun n => u n (σ n))
    Kvar C A hθ hσ (Filter.Eventually.of_forall hθne)
    hG₀ hC hA hC0 hA0 hu
  have hratio : Tendsto (fun n => Z n (σ n) / Z n 0) atTop (𝓝 (0 : ℂ)) := by
    apply hlim.congr'
    filter_upwards with n
    rw [hZcross n (σ n) (hroots n).2.2, hZbase n]
  have hp : Tendsto (fun n => (θ n, (0 : ℝ))) atTop (𝓝 (0, 0)) := by
    simpa [nhds_prod_eq] using hθ.prodMk tendsto_const_nhds
  have hCne := (hC.tendsto.comp hp).eventually_ne hC0
  have hZne : ∀ᶠ n in atTop, Z n 0 ≠ 0 := by
    filter_upwards [hG₀, hCne] with n hGn hCn
    rw [hZbase n]
    exact mul_ne_zero (neg_ne_zero.mpr hGn)
      (pow_ne_zero 2 (mul_ne_zero
        (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (hθne n))) hCn))
  exact ⟨σ, hσ, hroots, hratio,
    ordinary_value_obstruction_of_ratio_limit (fun n => Z n (σ n))
      (fun n => Z n 0) target hZne hcalibration hratio⟩

end FriedLeanVerification
