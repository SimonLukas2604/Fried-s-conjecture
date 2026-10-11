module

public import FriedLeanVerification.AlgebraInputs
public import FriedLeanVerification.AnalyticInputs
public import FriedLeanVerification.HolomorphicInputs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.Tendsto
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

@[expose] public section

set_option warningAsError true

/-!
# Lean check of the crossing-to-obstruction algebra

The source manuscript's analytic work supplies three coefficient-ratio
limits at the crossing: the complementary determinant ratio tends to `1`,
the scalar-root ratio tends to `1`, and the quadratic coefficient ratio
tends to `0`. This file checks that these inputs imply the claimed vanishing
of the normalized zeta value. It does not formalize the geometric or
microlocal analysis used to establish those limits.
-/

open Filter Topology

namespace FriedLeanVerification

/-- The exact ratio identity from equation (exactratio) of the manuscript. -/
theorem exact_crossing_ratio
    (G₀ G c₀ c e : ℂ) (hG₀ : G₀ ≠ 0) (hc₀ : c₀ ≠ 0) :
    (G * c * e) / (-G₀ * c₀ ^ 2) =
      -((G / G₀) * (c / c₀) * (e / c₀)) := by
  field_simp [hG₀, hc₀]

/-- The finite-cut determinants telescope to the divisor displayed in the
manuscript. This is the scalar cancellation remaining after the contact
Lefschetz equalities `P₃=P₁` and `P₄=P₀` are inserted. -/
theorem full_cut_divisor_cancellation
    (s c t q : ℂ) (hsc : s ≠ c) (hst : s ≠ t) (hq : q ≠ 0) :
    (((s - c) * (s - t)) ^ 2) /
        ((s - c) * ((s - c) * (s - t) * q) * (s - c)) =
      (s - t) / ((s - c) * q) := by
  field_simp [hsc, hst, hq]

/--
If the three factors in the exact crossing ratio tend to `1`, `1`, and `0`,
the complex normalized zeta ratio tends to zero. The nonvanishing hypotheses
are the denominators in the exact ratio identity.
-/
theorem normalized_ratio_tendsTo_zero
    (G₀ G c₀ c e : ℕ → ℂ)
    (hG₀ : ∀ᶠ n in atTop, G₀ n ≠ 0)
    (hc₀ : ∀ᶠ n in atTop, c₀ n ≠ 0)
    (hG : Tendsto (fun n => G n / G₀ n) atTop (𝓝 (1 : ℂ)))
    (hc : Tendsto (fun n => c n / c₀ n) atTop (𝓝 (1 : ℂ)))
    (he : Tendsto (fun n => e n / c₀ n) atTop (𝓝 (0 : ℂ))) :
    Tendsto (fun n => (G n * c n * e n) / (-G₀ n * c₀ n ^ 2))
      atTop (𝓝 (0 : ℂ)) := by
  have hprod : Tendsto
      (fun n => (G n / G₀ n) * (c n / c₀ n) * (e n / c₀ n))
      atTop (𝓝 ((1 : ℂ) * 1 * 0)) := (hG.mul hc).mul he
  have hneg : Tendsto
      (fun n => -((G n / G₀ n) * (c n / c₀ n) * (e n / c₀ n)))
      atTop (𝓝 (-((1 : ℂ) * 1 * 0))) := hprod.neg
  have hratio := hneg.congr' (by
    filter_upwards [hG₀, hc₀] with n hG₀n hc₀n
    exact (exact_crossing_ratio (G₀ n) (G n) (c₀ n) (c n) (e n)
      hG₀n hc₀n).symm)
  simpa using hratio

/-- The modulus of the complex ratio also tends to zero. -/
theorem normalized_modulus_tendsTo_zero
    (G₀ G c₀ c e : ℕ → ℂ)
    (hG₀ : ∀ᶠ n in atTop, G₀ n ≠ 0)
    (hc₀ : ∀ᶠ n in atTop, c₀ n ≠ 0)
    (hG : Tendsto (fun n => G n / G₀ n) atTop (𝓝 (1 : ℂ)))
    (hc : Tendsto (fun n => c n / c₀ n) atTop (𝓝 (1 : ℂ)))
    (he : Tendsto (fun n => e n / c₀ n) atTop (𝓝 (0 : ℂ))) :
    Tendsto (fun n => ‖(G n * c n * e n) / (-G₀ n * c₀ n ^ 2)‖)
      atTop (𝓝 (0 : ℝ)) := by
  have h := (normalized_ratio_tendsTo_zero G₀ G c₀ c e hG₀ hc₀ hG hc he).norm
  simpa using h

end FriedLeanVerification

namespace FriedLeanVerification

/-! ## Crossing existence

This isolates the intermediate-value step in the manuscript. The spectral
analysis supplies the continuous function and opposite endpoint signs; this
Lean theorem proves that those facts force a crossing in the interval. -/

theorem crossing_from_endpoint_signs
    (f : ℝ → ℝ) (T : ℝ) (hT : 0 < T)
    (hf : ContinuousOn f (Set.Icc 0 T))
    (hleft : f 0 < 0) (hright : 0 < f T) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ T ∧ f σ = 0 := by
  have hzero_mem : (0 : ℝ) ∈ Set.Icc (f 0) (f T) :=
    ⟨le_of_lt hleft, le_of_lt hright⟩
  obtain ⟨σ, hσ, hroot⟩ :=
    (intermediate_value_Icc (a := 0) (b := T) hT.le hf) hzero_mem
  refine ⟨σ, ?_, hσ.2, hroot⟩
  by_contra hnot
  have hσzero : σ = 0 := by linarith [hσ.1]
  subst σ
  linarith

/-- Any zero satisfying the manuscript's root equation and axis estimate is
bounded by the required quadratic scale. -/
theorem crossing_bound_of_root
    (θ K r σ m Tval : ℝ)
    (hr : 0 < r)
    (haxis : r / 2 * σ ≤ m)
    (hroot : m + θ ^ 2 * Tval = 0)
    (hT : |Tval| ≤ K) :
    σ ≤ 4 * K * θ ^ 2 / r := by
  have hTlo : -K ≤ Tval := (abs_le.mp hT).1
  have hK0 : 0 ≤ K := le_trans (abs_nonneg Tval) hT
  have hmupper : m ≤ K * θ ^ 2 := by nlinarith [hroot]
  have hσsmall : r / 2 * σ ≤ K * θ ^ 2 := le_trans haxis hmupper
  have hmul : σ * (r / 2) ≤ K * θ ^ 2 := by nlinarith [hσsmall]
  have hfinal : σ * r ≤ 2 * K * θ ^ 2 := by nlinarith [hmul]
  apply (le_div_iff₀ hr).2
  nlinarith [hfinal, sq_nonneg θ]

/-- The complete real-variable crossing argument: a negative value at zero,
the positive axis slope, and a uniformly bounded quadratic character term
give a crossing by the intermediate value theorem, and every root in the
interval has the asserted quadratic bound. -/
theorem crossing_exists_with_quadratic_bound
    (θ K r : ℝ) (hθ : 0 < θ) (hK : 0 < K) (hr : 0 < r)
    (base perturb : ℝ → ℝ)
    (hleft : base 0 + θ ^ 2 * perturb 0 < 0)
    (haxis : ∀ τ ∈ Set.Icc 0 (4 * K * θ ^ 2 / r),
      r / 2 * τ ≤ base τ)
    (hbound : ∀ τ ∈ Set.Icc 0 (4 * K * θ ^ 2 / r),
      |perturb τ| ≤ K)
    (hcont : ContinuousOn (fun τ => base τ + θ ^ 2 * perturb τ)
      (Set.Icc 0 (4 * K * θ ^ 2 / r))) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 4 * K * θ ^ 2 / r ∧
      base σ + θ ^ 2 * perturb σ = 0 := by
  have hU : 0 < 4 * K * θ ^ 2 / r := by positivity
  have hUmem : (4 * K * θ ^ 2 / r) ∈ Set.Icc 0 (4 * K * θ ^ 2 / r) :=
    ⟨le_of_lt hU, le_rfl⟩
  have haxisU := haxis _ hUmem
  have hboundU := hbound _ hUmem
  have hUidentity : r / 2 * (4 * K * θ ^ 2 / r) = 2 * K * θ ^ 2 := by
    field_simp
    ring
  have hright : 0 < base (4 * K * θ ^ 2 / r) +
      θ ^ 2 * perturb (4 * K * θ ^ 2 / r) := by
    have hpertLower : -K ≤ perturb (4 * K * θ ^ 2 / r) :=
      (abs_le.mp hboundU).1
    have hbaseLower : 2 * K * θ ^ 2 ≤ base (4 * K * θ ^ 2 / r) := by
      rw [← hUidentity]
      exact haxisU
    nlinarith [sq_nonneg θ]
  have hex := crossing_from_endpoint_signs
    (fun τ => base τ + θ ^ 2 * perturb τ)
    (4 * K * θ ^ 2 / r) hU hcont hleft hright
  obtain ⟨σ, hσpos, hσle, hσroot⟩ := hex
  refine ⟨σ, hσpos, hσle, hσroot⟩

/-! ## Finite-dimensional exactness input

The manuscript uses exactness of the full resonant de Rham complex to prove
that the horizontal middle zero space has dimension at least two. The
following linear-algebra lemma formalizes the rank-nullity argument used
there, independently of the microlocal theorem identifying that complex. -/

theorem exact_middle_dimension_lower_bound
    {V₁ V₂ V₃ : Type*}
    [AddCommGroup V₁] [Module ℂ V₁] [FiniteDimensional ℂ V₁]
    [AddCommGroup V₂] [Module ℂ V₂] [FiniteDimensional ℂ V₂]
    [AddCommGroup V₃] [Module ℂ V₃] [FiniteDimensional ℂ V₃]
    (D₁ : V₁ →ₗ[ℂ] V₂) (D₂ : V₂ →ₗ[ℂ] V₃)
    (hV₁ : Module.finrank ℂ V₁ = 1)
    (hV₃ : Module.finrank ℂ V₃ = 1)
    (hD₁inj : Function.Injective D₁)
    (hD₂surj : Function.Surjective D₂)
    (hcomplex : D₂.comp D₁ = 0) :
    2 ≤ Module.finrank ℂ V₂ := by
  have hrange : LinearMap.range D₁ ≤ LinearMap.ker D₂ :=
    LinearMap.range_le_ker_iff.mpr hcomplex
  have hD₁rank : Module.finrank ℂ (LinearMap.range D₁) = 1 := by
    rw [D₁.finrank_range_of_inj hD₁inj, hV₁]
  have hD₂range : LinearMap.range D₂ = ⊤ :=
    LinearMap.range_eq_top.mpr hD₂surj
  have hD₂rank : Module.finrank ℂ (LinearMap.range D₂) = 1 := by
    rw [hD₂range]
    simp [hV₃]
  have hkerLower : 1 ≤ Module.finrank ℂ (LinearMap.ker D₂) := by
    calc
      1 = Module.finrank ℂ (LinearMap.range D₁) := hD₁rank.symm
      _ ≤ Module.finrank ℂ (LinearMap.ker D₂) := Submodule.finrank_mono hrange
  have hRankNullity := D₂.finrank_range_add_finrank_ker
  rw [hD₂rank] at hRankNullity
  omega

/-- Adding the one-dimensional nonzero root in the middle cut leaves the
manuscript's two possible zero-space dimensions: two or three. -/
theorem exact_middle_dimension_two_or_three
    {V₁ V₂ V₃ : Type*}
    [AddCommGroup V₁] [Module ℂ V₁] [FiniteDimensional ℂ V₁]
    [AddCommGroup V₂] [Module ℂ V₂] [FiniteDimensional ℂ V₂]
    [AddCommGroup V₃] [Module ℂ V₃] [FiniteDimensional ℂ V₃]
    (D₁ : V₁ →ₗ[ℂ] V₂) (D₂ : V₂ →ₗ[ℂ] V₃)
    (hV₁ : Module.finrank ℂ V₁ = 1)
    (hV₃ : Module.finrank ℂ V₃ = 1)
    (hD₁inj : Function.Injective D₁)
    (hD₂surj : Function.Surjective D₂)
    (hcomplex : D₂.comp D₁ = 0)
    (hcut : Module.finrank ℂ V₂ ≤ 3) :
    Module.finrank ℂ V₂ = 2 ∨ Module.finrank ℂ V₂ = 3 := by
  have hlow := exact_middle_dimension_lower_bound D₁ D₂ hV₁ hV₃
    hD₁inj hD₂surj hcomplex
  omega

/-- A quadratic-scale bound on crossing parameters forces the crossings to
approach the zero-twist metric. -/
theorem crossing_parameter_tendsto_zero
    (θ σ : ℕ → ℝ) (hθ : Tendsto θ atTop (𝓝 0))
    (hscale : ∃ B > 0, ∀ᶠ n in atTop, |σ n| ≤ B * (θ n) ^ 2) :
    Tendsto σ atTop (𝓝 0) := by
  obtain ⟨B, hB, hbound⟩ := hscale
  have hθsq : Tendsto (fun n => (θ n) ^ 2) atTop (𝓝 0) := by
    simpa using hθ.pow 2
  have hupper : Tendsto (fun n => B * (θ n) ^ 2) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hθsq)
  have hlower : Tendsto (fun n => -(B * (θ n) ^ 2)) atTop (𝓝 0) := by
    simpa using hupper.neg
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hlower hupper
  · filter_upwards [hbound] with n hn
    have hn' := abs_le.mp hn
    exact hn'.1
  · filter_upwards [hbound] with n hn
    have hn' := abs_le.mp hn
    exact hn'.2

/-- If each member of a character sequence has a positive crossing satisfying
the manuscript's root equation and axis/perturbation estimates, then the
chosen crossings tend to the unperturbed metric. -/
theorem crossing_roots_tendsto_zero
    (θ σ : ℕ → ℝ) (base perturb : ℕ → ℝ → ℝ)
    (K r : ℝ) (hK : 0 < K) (hr : 0 < r)
    (hθ : Tendsto θ atTop (𝓝 0))
    (hσpos : ∀ n, 0 ≤ σ n)
    (haxis : ∀ n, r / 2 * σ n ≤ base n (σ n))
    (hroot : ∀ n, base n (σ n) + (θ n) ^ 2 * perturb n (σ n) = 0)
    (hpert : ∀ n, |perturb n (σ n)| ≤ K) :
    Tendsto σ atTop (𝓝 0) := by
  have hbound : ∀ n, |σ n| ≤ (4 * K / r) * (θ n) ^ 2 := by
    intro n
    have h := crossing_bound_of_root (θ n) K r (σ n)
      (base n (σ n)) (perturb n (σ n)) hr (haxis n) (hroot n) (hpert n)
    rw [abs_of_nonneg (hσpos n)]
    calc
      σ n ≤ 4 * K * (θ n) ^ 2 / r := h
      _ = (4 * K / r) * (θ n) ^ 2 := by ring
  apply crossing_parameter_tendsto_zero θ σ hθ
  refine ⟨4 * K / r, by positivity, ?_⟩
  exact Filter.Eventually.of_forall hbound

/-! ## Quotient estimates from continuity

The manuscript factors the roots and residual coefficient as
`c = θ² C` and `e₁ = θ² A`. At a crossing with `σθ → 0`, continuity of
`C` and `A` supplies the two coefficient-ratio limits. The following theorem
formalizes that implication on the real character axis. -/

theorem coefficient_quotients_of_continuity
    (θ σ : ℕ → ℝ) (hθ : Tendsto θ atTop (𝓝 0))
    (hσ : Tendsto σ atTop (𝓝 0))
    (C A : ℝ × ℝ → ℂ)
    (hC : ContinuousAt C (0, 0)) (hA : ContinuousAt A (0, 0))
    (hC0 : C (0, 0) ≠ 0) (hA0 : A (0, 0) = 0) :
    Tendsto (fun n => C (θ n, σ n) / C (θ n, 0)) atTop (𝓝 (1 : ℂ)) ∧
    Tendsto (fun n => A (θ n, σ n) / C (θ n, 0)) atTop (𝓝 (0 : ℂ)) := by
  have hcrossPair : Tendsto (fun n => (θ n, σ n)) atTop (𝓝 (0, 0)) :=
    by simpa [nhds_prod_eq] using hθ.prodMk hσ
  have hbasePair : Tendsto (fun n => (θ n, (0 : ℝ))) atTop (𝓝 (0, 0)) := by
    simpa [nhds_prod_eq] using hθ.prodMk tendsto_const_nhds
  have hCcross : Tendsto (fun n => C (θ n, σ n)) atTop (𝓝 (C (0, 0))) :=
    hC.tendsto.comp hcrossPair
  have hCbase : Tendsto (fun n => C (θ n, 0)) atTop (𝓝 (C (0, 0))) :=
    hC.tendsto.comp hbasePair
  have hAcross : Tendsto (fun n => A (θ n, σ n)) atTop (𝓝 (A (0, 0))) :=
    hA.tendsto.comp hcrossPair
  have hratioC := hCcross.div hCbase hC0
  have hratioA := hAcross.div hCbase hC0
  constructor
  · change Tendsto
      ((fun n => C (θ n, σ n)) / (fun n => C (θ n, 0))) atTop (𝓝 (1 : ℂ))
    simpa [hC0] using hratioC
  · change Tendsto
      ((fun n => A (θ n, σ n)) / (fun n => C (θ n, 0))) atTop (𝓝 (0 : ℂ))
    simpa [hA0, hC0] using hratioA

/-- Substituting the manuscript's factorizations `c = z² C` and `e₁ = z² A`
into the quotients cancels the common nonzero character factor. -/
theorem factored_root_quotients
    (θ σ : ℕ → ℝ) (hθ : Tendsto θ atTop (𝓝 0))
    (hσ : Tendsto σ atTop (𝓝 0))
    (C A : ℝ × ℝ → ℂ)
    (hC : ContinuousAt C (0, 0)) (hA : ContinuousAt A (0, 0))
    (hC0 : C (0, 0) ≠ 0) (hA0 : A (0, 0) = 0)
    (hθne : ∀ n, θ n ≠ 0) :
    Tendsto
      (fun n => (((θ n : ℂ) ^ 2 * C (θ n, σ n)) /
        ((θ n : ℂ) ^ 2 * C (θ n, 0)))) atTop (𝓝 (1 : ℂ)) ∧
    Tendsto
      (fun n => (((θ n : ℂ) ^ 2 * A (θ n, σ n)) /
        ((θ n : ℂ) ^ 2 * C (θ n, 0)))) atTop (𝓝 (0 : ℂ)) := by
  have hcoeff := coefficient_quotients_of_continuity θ σ hθ hσ C A hC hA hC0 hA0
  have hbasePair : Tendsto (fun n => (θ n, (0 : ℝ))) atTop (𝓝 (0, 0)) := by
    simpa [nhds_prod_eq] using hθ.prodMk tendsto_const_nhds
  have hCbaseTendsto : Tendsto (fun n => C (θ n, 0)) atTop (𝓝 (C (0, 0))) :=
    hC.tendsto.comp hbasePair
  have hCbase : ∀ᶠ n in atTop, C (θ n, 0) ≠ 0 :=
    hCbaseTendsto.eventually_ne hC0
  constructor
  · apply hcoeff.1.congr'
    filter_upwards [hCbase] with n hCn
    field_simp [hθne n, hCn]
  · apply hcoeff.2.congr'
    filter_upwards [hCbase] with n hCn
    field_simp [hθne n, hCn]

/-! ## Normalization factor

The paper's finite-cut variation formula writes the complementary factor as
an exponential of an integral whose absolute value is bounded by a constant
times the crossing parameter. This theorem proves the limiting implication
from that bound; proving the finite-dimensional variation formula itself is
part of the geometric input boundary. -/

theorem exponential_normalization_tends_to_one
    (u : ℕ → ℂ) (σ : ℕ → ℝ) (K : ℝ)
    (hσ : Tendsto σ atTop (𝓝 0))
    (huBound : ∀ᶠ n in atTop, ‖u n‖ ≤ K * |σ n|) :
    Tendsto (fun n => Complex.exp (u n)) atTop (𝓝 1) := by
  have hσabs : Tendsto (fun n => |σ n|) atTop (𝓝 0) := by
    simpa only [abs_zero, Function.comp_apply] using hσ.abs
  have hup : Tendsto (fun n => K * |σ n|) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hσabs)
  have hnorm : Tendsto (fun n => ‖u n‖) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hup
      (by filter_upwards with n; positivity)
      huBound
  have hu : Tendsto u atTop (𝓝 (0 : ℂ)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa using hnorm
  have hexp := NormedSpace.exp_continuous.tendsto 0 |>.comp hu
  rw [Complex.exp_eq_exp_ℂ]
  change Tendsto (NormedSpace.exp ∘ u) atTop (𝓝 1)
  simpa only [NormedSpace.exp_zero] using hexp

/-! ## End-to-end abstract theorem

This theorem assembles the formal parts of the proof. Its hypotheses are the
analytic conclusions that the manuscript must establish: a common quadratic
factorization with continuous coefficients, nonvanishing of the scalar root,
and a bounded logarithmic variation for the complementary factor. -/

theorem abstract_counterexample_ratio
    (θ σ : ℕ → ℝ) (G₀ u : ℕ → ℂ) (K : ℝ)
    (C A : ℝ × ℝ → ℂ)
    (hθ : Tendsto θ atTop (𝓝 0)) (hσ : Tendsto σ atTop (𝓝 0))
    (hθne : ∀ n, θ n ≠ 0)
    (hG₀ : ∀ᶠ n in atTop, G₀ n ≠ 0)
    (hC : ContinuousAt C (0, 0)) (hA : ContinuousAt A (0, 0))
    (hC₀ : C (0, 0) ≠ 0) (hA₀ : A (0, 0) = 0)
    (huBound : ∀ᶠ n in atTop, ‖u n‖ ≤ K * |σ n|) :
    Tendsto
      (fun n =>
        ((G₀ n * Complex.exp (u n)) *
          (((θ n : ℂ) ^ 2) * C (θ n, σ n)) *
          (((θ n : ℂ) ^ 2) * A (θ n, σ n))) /
          (-G₀ n * ((((θ n : ℂ) ^ 2) * C (θ n, 0)) ^ 2)))
      atTop (𝓝 (0 : ℂ)) := by
  let G : ℕ → ℂ := fun n => G₀ n * Complex.exp (u n)
  let c₀ : ℕ → ℂ := fun n => (θ n : ℂ) ^ 2 * C (θ n, 0)
  let c : ℕ → ℂ := fun n => (θ n : ℂ) ^ 2 * C (θ n, σ n)
  let e : ℕ → ℂ := fun n => (θ n : ℂ) ^ 2 * A (θ n, σ n)
  have hbasePair : Tendsto (fun n => (θ n, (0 : ℝ))) atTop (𝓝 (0, 0)) := by
    simpa [nhds_prod_eq] using hθ.prodMk tendsto_const_nhds
  have hCbase : ∀ᶠ n in atTop, C (θ n, 0) ≠ 0 :=
    (hC.tendsto.comp hbasePair).eventually_ne hC₀
  have hc₀ : ∀ᶠ n in atTop, c₀ n ≠ 0 := by
    filter_upwards [hCbase] with n hCn
    dsimp [c₀]
    exact mul_ne_zero (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (hθne n)))
      hCn
  have hG : Tendsto (fun n => G n / G₀ n) atTop (𝓝 (1 : ℂ)) := by
    have hexp := exponential_normalization_tends_to_one u σ K hσ huBound
    apply hexp.congr'
    filter_upwards [hG₀] with n hG₀n
    dsimp [G]
    field_simp [hG₀n]
  have hcoeff := factored_root_quotients θ σ hθ hσ C A hC hA hC₀ hA₀ hθne
  have hc : Tendsto (fun n => c n / c₀ n) atTop (𝓝 (1 : ℂ)) := by
    exact hcoeff.1.congr' (Filter.Eventually.of_forall fun _ => rfl)
  have he : Tendsto (fun n => e n / c₀ n) atTop (𝓝 (0 : ℂ)) := by
    exact hcoeff.2.congr' (Filter.Eventually.of_forall fun _ => rfl)
  have hratio := normalized_ratio_tendsTo_zero G₀ G c₀ c e hG₀ hc₀ hG hc he
  exact hratio.congr' (Filter.Eventually.of_forall fun n => by
    simp only [G, c₀, c, e])

end FriedLeanVerification
