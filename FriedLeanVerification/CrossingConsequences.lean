module

public import FriedLeanVerification

@[expose] public section

set_option warningAsError true
namespace FriedLeanVerification
open Filter Topology

/-- Endpoint exactness of the full split complex gives the two horizontal
map properties used in the manuscript. The differential formulas and the
full-complex exactness at degrees one and four are explicit hypotheses. -/
theorem horizontal_maps_of_full_complex_endpoints
    {V₁ V₂ V₃ : Type*}
    [AddCommGroup V₁] [Module ℂ V₁]
    [AddCommGroup V₂] [Module ℂ V₂]
    [AddCommGroup V₃] [Module ℂ V₃]
    (D₁ : V₁ →ₗ[ℂ] V₂) (D₂ : V₂ →ₗ[ℂ] V₃)
    (d₁ : V₁ →ₗ[ℂ] V₂ × V₁) (d₃ : V₃ × V₂ →ₗ[ℂ] V₃)
    (hformula₁ : ∀ u, d₁ u = (D₁ u, 0))
    (hformula₃ : ∀ u v, d₃ (u, v) = -D₂ v)
    (hexact₁ : LinearMap.ker d₁ = ⊥)
    (hexact₄ : LinearMap.range d₃ = ⊤) :
    Function.Injective D₁ ∧ Function.Surjective D₂ := by
  constructor
  · intro u v huv
    apply LinearMap.ker_eq_bot.mp hexact₁
    rw [hformula₁, hformula₁, huv]
  · intro w
    obtain ⟨⟨u, v⟩, hv⟩ := LinearMap.range_eq_top.mp hexact₄ (-w)
    refine ⟨v, ?_⟩
    rw [hformula₃] at hv
    exact neg_injective hv

/-- The exhaustive crossing cases follow from full-complex endpoint exactness,
the Cartan complex identity, the rank-four cut bound, and the identification
of generalized zero-space dimension with algebraic multiplicity. -/
theorem resonant_crossing_polynomial_cases
    {V₁ V₂ V₃ : Type*}
    [AddCommGroup V₁] [Module ℂ V₁] [FiniteDimensional ℂ V₁]
    [AddCommGroup V₂] [Module ℂ V₂] [FiniteDimensional ℂ V₂]
    [AddCommGroup V₃] [Module ℂ V₃] [FiniteDimensional ℂ V₃]
    (D₁ : V₁ →ₗ[ℂ] V₂) (D₂ : V₂ →ₗ[ℂ] V₃)
    (d₁ : V₁ →ₗ[ℂ] V₂ × V₁) (d₃ : V₃ × V₂ →ₗ[ℂ] V₃)
    (hformula₁ : ∀ u, d₁ u = (D₁ u, 0))
    (hformula₃ : ∀ u v, d₃ (u, v) = -D₂ v)
    (hexact₁ : LinearMap.ker d₁ = ⊥)
    (hexact₄ : LinearMap.range d₃ = ⊤)
    (hV₁ : Module.finrank ℂ V₁ = 1) (hV₃ : Module.finrank ℂ V₃ = 1)
    (hcomplex : D₂.comp D₁ = 0) (hcut : Module.finrank ℂ V₂ ≤ 3)
    (c e₁ e₂ : ℂ) (hc : c ≠ 0)
    (hidentify : (middleCrossingPolynomial c e₁ e₂).rootMultiplicity 0 =
      Module.finrank ℂ V₂) :
    e₂ = 0 ∧ (Module.finrank ℂ V₂ = 3 ↔ e₁ = 0) ∧
      (Module.finrank ℂ V₂ = 2 ↔ e₁ ≠ 0) := by
  have hmaps := horizontal_maps_of_full_complex_endpoints D₁ D₂ d₁ d₃
    hformula₁ hformula₃ hexact₁ hexact₄
  have hlow := exact_middle_dimension_lower_bound D₁ D₂ hV₁ hV₃
    hmaps.1 hmaps.2 hcomplex
  have hcases := middle_crossing_multiplicity_cases c e₁ e₂ hc
    (by simpa [hidentify] using hlow) (by simpa [hidentify] using hcut)
  simpa [hidentify] using hcases

/-- Crossings can be chosen along a positive character sequence; every such
choice tends to zero. No uniqueness or monotonicity is required. -/
theorem crossing_sequence_exists
    (θ : ℕ → ℝ) (K r : ℝ) (hK : 0 < K) (hr : 0 < r)
    (base perturb : ℕ → ℝ → ℝ)
    (hθpos : ∀ n, 0 < θ n) (hθ : Tendsto θ atTop (𝓝 0))
    (hleft : ∀ n, base n 0 + (θ n) ^ 2 * perturb n 0 < 0)
    (haxis : ∀ n τ, τ ∈ Set.Icc 0 (4 * K * (θ n) ^ 2 / r) →
      r / 2 * τ ≤ base n τ)
    (hbound : ∀ n τ, τ ∈ Set.Icc 0 (4 * K * (θ n) ^ 2 / r) →
      |perturb n τ| ≤ K)
    (hcont : ∀ n, ContinuousOn (fun τ => base n τ + (θ n) ^ 2 * perturb n τ)
      (Set.Icc 0 (4 * K * (θ n) ^ 2 / r))) :
    ∃ σ : ℕ → ℝ, Tendsto σ atTop (𝓝 0) ∧
      ∀ n, 0 < σ n ∧ σ n ≤ 4 * K * (θ n) ^ 2 / r ∧
        base n (σ n) + (θ n) ^ 2 * perturb n (σ n) = 0 := by
  have hex : ∀ n, ∃ σ : ℝ, 0 < σ ∧ σ ≤ 4 * K * (θ n) ^ 2 / r ∧
      base n σ + (θ n) ^ 2 * perturb n σ = 0 := by
    intro n
    exact crossing_exists_with_quadratic_bound (θ n) K r (hθpos n) hK hr
      (base n) (perturb n) (hleft n) (haxis n) (hbound n) (hcont n)
  choose σ hσ using hex
  refine ⟨σ, ?_, hσ⟩
  apply crossing_roots_tendsto_zero θ σ base perturb K r hK hr hθ
    (fun n => (hσ n).1.le)
  · intro n
    exact haxis n (σ n) ⟨(hσ n).1.le, (hσ n).2.1⟩
  · exact fun n => (hσ n).2.2
  · intro n
    exact hbound n (σ n) ⟨(hσ n).1.le, (hσ n).2.1⟩

/-- Calibration to a nonzero hyperbolic value and a vanishing ratio imply
strict ordinary-value discrepancy, including when the crossing value is zero. -/
theorem ordinary_value_obstruction_of_ratio_limit
    (Z Z₀ : ℕ → ℂ) (target : ℕ → ℝ)
    (hZ₀ : ∀ᶠ n in atTop, Z₀ n ≠ 0)
    (hcalibration : ∀ᶠ n in atTop, target n = ‖Z₀ n‖)
    (hratio : Tendsto (fun n => Z n / Z₀ n) atTop (𝓝 (0 : ℂ))) :
    ∀ᶠ n in atTop, 0 < target n ∧ ‖Z n‖ < target n ∧ ‖Z n‖ ≠ target n := by
  have hnorm : Tendsto (fun n => ‖Z n / Z₀ n‖) atTop (𝓝 (0 : ℝ)) := by
    simpa using hratio.norm
  have hsmall : ∀ᶠ n in atTop, ‖Z n / Z₀ n‖ < 1 :=
    hnorm.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hZ₀, hcalibration, hsmall] with n hn hcal hsmalln
  rw [hcal]
  have hpos : 0 < ‖Z₀ n‖ := norm_pos_iff.mpr hn
  have hlt : ‖Z n‖ < ‖Z₀ n‖ := by
    rw [norm_div] at hsmalln
    exact (div_lt_one hpos).mp hsmalln
  exact ⟨hpos, hlt, ne_of_lt hlt⟩

end FriedLeanVerification
