module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.Tendsto
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

@[expose] public section

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

/--
If the three factors in the exact crossing ratio tend to `1`, `1`, and `0`,
the complex normalized zeta ratio tends to zero. The nonvanishing hypotheses
are the denominators in the exact ratio identity.
-/
theorem normalized_ratio_tendsTo_zero
    (G₀ G c₀ c e : ℕ → ℂ)
    (hG₀ : ∀ n, G₀ n ≠ 0)
    (hc₀ : ∀ n, c₀ n ≠ 0)
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
    filter_upwards with n
    exact (exact_crossing_ratio (G₀ n) (G n) (c₀ n) (c n) (e n)
      (hG₀ n) (hc₀ n)).symm)
  simpa using hratio

/-- The modulus of the complex ratio also tends to zero. -/
theorem normalized_modulus_tendsTo_zero
    (G₀ G c₀ c e : ℕ → ℂ)
    (hG₀ : ∀ n, G₀ n ≠ 0)
    (hc₀ : ∀ n, c₀ n ≠ 0)
    (hG : Tendsto (fun n => G n / G₀ n) atTop (𝓝 (1 : ℂ)))
    (hc : Tendsto (fun n => c n / c₀ n) atTop (𝓝 (1 : ℂ)))
    (he : Tendsto (fun n => e n / c₀ n) atTop (𝓝 (0 : ℂ))) :
    Tendsto (fun n => ‖(G n * c n * e n) / (-G₀ n * c₀ n ^ 2)‖)
      atTop (𝓝 (0 : ℝ)) := by
  have h := (normalized_ratio_tendsTo_zero G₀ G c₀ c e hG₀ hc₀ hG hc he).norm
  simpa using h

end FriedLeanVerification
