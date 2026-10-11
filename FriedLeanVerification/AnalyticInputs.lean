module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Tactic

@[expose] public section

set_option warningAsError true
namespace FriedLeanVerification
open Filter Topology

/-- Uniform bounds on a twist multiplier and a reference resolvent give one
nonzero character disk on which the Neumann factor is invertible. This is a
Banach-algebra theorem; the anisotropic spaces and the stated bounds are not
constructed here. -/
theorem uniform_neumann_disk
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (V R : A) (hV : ‖V‖ ≤ D) (hR : ‖R‖ ≤ C)
    (z : ℂ) (hz : ‖z‖ < 1 / (2 * (C + 1) * (D + 1))) :
    IsUnit (1 + z • (V * R)) := by
  have hnorm : ‖z • (V * R)‖ ≤ ‖z‖ * ((D + 1) * (C + 1)) := by
    calc
      ‖z • (V * R)‖ = ‖z‖ * ‖V * R‖ := norm_smul _ _
      _ ≤ ‖z‖ * (‖V‖ * ‖R‖) := by gcongr; exact norm_mul_le _ _
      _ ≤ ‖z‖ * ((D + 1) * (C + 1)) := by gcongr <;> linarith
  have hz' : ‖z‖ * (2 * (C + 1) * (D + 1)) < 1 :=
    (lt_div_iff₀ (by positivity)).mp hz
  have hsmall : ‖-(z • (V * R))‖ < 1 := by
    rw [norm_neg]
    nlinarith
  simpa using isUnit_one_sub_of_norm_lt_one hsmall

/-- Two close projections have an injective transfer between their ranges.
This verifies the functional-analysis rank-stability step without constructing
any microlocal projector. -/
theorem projection_transfer_injective
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (P Q : E →L[ℂ] E) (hP : ∀ v, P (P v) = P v)
    (hclose : ‖P - Q‖ < 1) :
    Function.Injective
      (fun u : LinearMap.range P.toLinearMap =>
        (⟨Q u, ⟨u, rfl⟩⟩ : LinearMap.range Q.toLinearMap)) := by
  intro u v huv
  apply Subtype.ext
  have hPu : P u = u := by
    obtain ⟨x, hx⟩ := u.property
    change P x = (u : E) at hx
    rw [← hx]
    exact hP x
  have hPv : P v = v := by
    obtain ⟨x, hx⟩ := v.property
    change P x = (v : E) at hx
    rw [← hx]
    exact hP x
  have hQ : Q u = Q v := congrArg Subtype.val huv
  have hEq : (P - Q) ((u : E) - v) = (u : E) - v := by
    simp [map_sub, hPu, hPv, hQ]
  have hle := (P - Q).le_opNorm ((u : E) - v)
  rw [hEq] at hle
  have hz : ‖(u : E) - v‖ = 0 := by
    nlinarith [norm_nonneg ((u : E) - v)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

/-- Finite-rank projections closer than one have equal ranks, even if the
ambient anisotropic space is infinite dimensional. -/
theorem close_projections_equal_rank
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (P Q : E →L[ℂ] E)
    [FiniteDimensional ℂ (LinearMap.range P.toLinearMap)]
    [FiniteDimensional ℂ (LinearMap.range Q.toLinearMap)]
    (hP : ∀ v, P (P v) = P v) (hQ : ∀ v, Q (Q v) = Q v)
    (hclose : ‖P - Q‖ < 1) :
    Module.finrank ℂ (LinearMap.range P.toLinearMap) =
      Module.finrank ℂ (LinearMap.range Q.toLinearMap) := by
  let f : LinearMap.range P.toLinearMap →ₗ[ℂ] LinearMap.range Q.toLinearMap :=
    { toFun := fun u => ⟨Q u, ⟨u, rfl⟩⟩
      map_add' := by intros; apply Subtype.ext; simp
      map_smul' := by intros; apply Subtype.ext; simp }
  let g : LinearMap.range Q.toLinearMap →ₗ[ℂ] LinearMap.range P.toLinearMap :=
    { toFun := fun u => ⟨P u, ⟨u, rfl⟩⟩
      map_add' := by intros; apply Subtype.ext; simp
      map_smul' := by intros; apply Subtype.ext; simp }
  apply le_antisymm
  · exact LinearMap.finrank_le_finrank_of_injective (f := f)
      (projection_transfer_injective P Q hP hclose : Function.Injective f)
  · have hclose' : ‖Q - P‖ < 1 := by simpa only [norm_sub_rev] using hclose
    exact LinearMap.finrank_le_finrank_of_injective (f := g)
      (projection_transfer_injective Q P hQ hclose' : Function.Injective g)

/-- A bounded finite trace gives the exponent bound used in the normalization
limit. The integral identity identifying this exponent with the complementary
determinant ratio remains an explicit premise in the main theorem. -/
theorem finite_trace_integral_bound
    (H : ℝ → ℂ) (K τ : ℝ)
    (hbound : ∀ v ∈ Set.uIoc 0 τ, ‖H v‖ ≤ K) :
    ‖∫ v in (0 : ℝ)..τ, H v‖ ≤ K * |τ| := by
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const hbound

/-- First-order information on the untwisted axis and continuity of the
quadratic character coefficient determine the leading crossing scale. -/
theorem crossing_asymptotic
    (θ σ : ℕ → ℝ) (r κ : ℝ) (hr : r ≠ 0)
    (T : ℝ × ℝ → ℝ) (η : ℝ → ℝ)
    (hθ : Tendsto θ atTop (𝓝 0)) (hσ : Tendsto σ atTop (𝓝 0))
    (hθne : ∀ n, θ n ≠ 0)
    (hT : ContinuousAt T (0, 0)) (hT0 : T (0, 0) = -κ / 2)
    (hη : ContinuousAt η 0) (hη0 : η 0 = 0)
    (hroot : ∀ n, σ n * (r + η (σ n)) + (θ n) ^ 2 * T (θ n, σ n) = 0) :
    Tendsto (fun n => σ n / (θ n) ^ 2) atTop (𝓝 (κ / (2 * r))) := by
  have hp : Tendsto (fun n => (θ n, σ n)) atTop (𝓝 (0, 0)) := by
    simpa [nhds_prod_eq] using hθ.prodMk hσ
  have ht : Tendsto (fun n => -T (θ n, σ n)) atTop (𝓝 (κ / 2)) := by
    simpa only [Function.comp_apply, hT0, neg_div, neg_neg] using
      (hT.tendsto.comp hp).neg
  have hd : Tendsto (fun n => r + η (σ n)) atTop (𝓝 r) := by
    simpa [hη0] using tendsto_const_nhds.add (hη.tendsto.comp hσ)
  have hdne := hd.eventually_ne hr
  have hq := ht.div hd hr
  have hlimit : (κ / 2) / r = κ / (2 * r) := by ring
  rw [hlimit] at hq
  apply hq.congr'
  filter_upwards [hdne] with n hn
  have hrootn := hroot n
  change -T (θ n, σ n) / (r + η (σ n)) = σ n / (θ n) ^ 2
  symm
  apply (div_eq_div_iff (pow_ne_zero 2 (hθne n)) hn).mpr
  nlinarith [hrootn]

end FriedLeanVerification
