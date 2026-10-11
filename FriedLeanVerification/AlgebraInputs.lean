module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.Algebra.Polynomial.Eval.Irreducible
public import Mathlib.Algebra.CharP.Two
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Tactic

@[expose] public section

set_option warningAsError true
namespace FriedLeanVerification
open Polynomial Matrix Filter Topology

/-! Algebraic inputs for the geometric construction. These computations do not
construct a surface, a mapping class, or a hyperbolic manifold. -/
def monodromyMatrix : Matrix (Fin 4) (Fin 4) ℤ :=
  !![2, 1, -1, 0; 1, -1, 0, -1; 1, 0, 0, 0; 0, 1, 0, 0]

def intersectionMatrix : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0, 0, 1, 0; 0, 0, 0, 1; -1, 0, 0, 0; 0, -1, 0, 0]

theorem monodromy_preserves_intersection :
    monodromyMatrix.transpose * intersectionMatrix * monodromyMatrix =
      intersectionMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [monodromyMatrix, intersectionMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

theorem monodromy_charpoly :
    monodromyMatrix.charpoly = X ^ 4 - X ^ 3 - X ^ 2 - X + 1 := by
  simp [Matrix.charpoly, Matrix.charmatrix, Matrix.det_succ_row_zero,
    monodromyMatrix,
    Matrix.submatrix, Fin.sum_univ_succ, Matrix.scalar, Matrix.diagonal, Fin.succAbove]
  ring

theorem monodromy_no_fixed_determinant :
    (1 - monodromyMatrix).det = -1 := by
  have h := congrArg (fun p : ℤ[X] => p.eval 1) monodromy_charpoly
  simpa [Matrix.eval_charpoly, Matrix.scalar, Matrix.diagonal] using h


/-- Reduction of the actual characteristic polynomial modulo two. -/
theorem monodromy_mod_two :
    monodromyMatrix.charpoly.map (Int.castRingHom (ZMod 2)) =
      cyclotomic 5 (ZMod 2) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [monodromy_charpoly, cyclotomic_prime]
  simp [Finset.sum_range_succ, CharTwo.sub_eq_add]
  ring

theorem two_order_mod_five :
    orderOf (ZMod.unitOfCoprime 2 (show Nat.Coprime 2 5 by norm_num)) = 4 := by
  apply (orderOf_eq_iff (by norm_num : 0 < 4)).mpr
  constructor
  · decide
  · intro m hmlt hmpos
    interval_cases m <;> decide

theorem monodromy_charpoly_irreducible_mod_two :
    Irreducible (monodromyMatrix.charpoly.map (Int.castRingHom (ZMod 2))) := by
  rw [monodromy_mod_two]
  apply ZMod.irreducible_of_dvd_cyclotomic_of_natDegree (p := 2) (n := 5)
    (by norm_num) (dvd_refl _)
  rw [natDegree_cyclotomic, two_order_mod_five]
  norm_num [Nat.totient_prime (by norm_num : Nat.Prime 5)]

theorem monodromy_charpoly_irreducible_int : Irreducible monodromyMatrix.charpoly := by
  exact Polynomial.Monic.irreducible_of_irreducible_map
    (Int.castRingHom (ZMod 2)) _ monodromyMatrix.charpoly_monic
    monodromy_charpoly_irreducible_mod_two

theorem monodromy_charpoly_irreducible_rat :
    Irreducible (monodromyMatrix.charpoly.map (Int.castRingHom ℚ)) := by
  exact (monodromyMatrix.charpoly_monic.irreducible_iff_irreducible_map_fraction_map
    (K := ℚ)).mp monodromy_charpoly_irreducible_int

/-- The explicit characteristic polynomial has a real root beyond the unit
circle. This proves the numerical root claim, without invoking the geometric
homological criterion or classifying cyclotomic polynomials. -/
theorem monodromy_real_root :
    ∃ x : ℝ, 1 < x ∧ x < 2 ∧ x ^ 4 - x ^ 3 - x ^ 2 - x + 1 = 0 := by
  have hcont : Continuous (fun x : ℝ => x ^ 4 - x ^ 3 - x ^ 2 - x + 1) := by
    fun_prop
  obtain ⟨x, hx, heq⟩ :=
    intermediate_value_Icc (show (1 : ℝ) ≤ 2 by norm_num) hcont.continuousOn
      (show (0 : ℝ) ∈ Set.Icc (1 ^ 4 - 1 ^ 3 - 1 ^ 2 - 1 + 1)
        (2 ^ 4 - 2 ^ 3 - 2 ^ 2 - 2 + 1) by norm_num)
  refine ⟨x, ?_, ?_, heq⟩
  · have hne : x ≠ 1 := by intro h; subst x; norm_num at heq
    exact lt_of_le_of_ne hx.1 (Ne.symm hne)
  · have hne : x ≠ 2 := by intro h; subst x; norm_num at heq
    exact lt_of_le_of_ne hx.2 hne

/-- The real root beyond one excludes every cyclotomic polynomial. -/
theorem monodromy_not_cyclotomic (n : ℕ) (hn : 0 < n) :
    monodromyMatrix.charpoly ≠ cyclotomic n ℤ := by
  intro h
  obtain ⟨x, hx, _, hp⟩ := monodromy_real_root
  have hroot : (monodromyMatrix.charpoly.map (Int.castRingHom ℂ)).IsRoot (x : ℂ) := by
    rw [IsRoot.def, monodromy_charpoly]
    simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_one, eval_add, eval_sub, eval_pow, eval_X, eval_one]
    exact_mod_cast hp
  rw [h, map_cyclotomic] at hroot
  have hprim := (isRoot_cyclotomic_iff_charZero hn).mp hroot
  have hxnorm : |x| = 1 := by
    simpa using hprim.norm'_eq_one (ne_of_gt hn)
  rw [abs_of_pos (by linarith : 0 < x)] at hxnorm
  linarith

/-- The nonzero linear coefficient excludes a proper power substitution. -/
theorem monodromy_not_power_composition (k : ℕ) (hk : 1 < k) (q : ℤ[X]) :
    monodromyMatrix.charpoly ≠ q.comp (X ^ k) := by
  intro h
  have hcoeff := congrArg (fun p : ℤ[X] => p.coeff 1) h
  rw [monodromy_charpoly, ← expand_eq_comp_X_pow, coeff_expand (by omega)] at hcoeff
  have hnot : ¬ k ∣ 1 := by
    intro hd
    have := Nat.le_of_dvd (by norm_num : 0 < 1) hd
    omega
  norm_num [hnot, coeff_one] at hcoeff

/-! Rank-one spectral-slot argument from the Hodge appendix. The existence of
the spectral slot, its eigenvector, and the Hodge identifications are premises.
This theorem only proves that a positive-eigenvalue vector spanning the slot
excludes a zero eigenvector in that slot. -/
theorem rank_one_slot_excludes_kernel
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (A : V →ₗ[ℂ] V) (v : V) (μ : ℂ)
    (hdim : Module.finrank ℂ V = 1) (hv : v ≠ 0)
    (hμ : μ ≠ 0) (heigen : A v = μ • v) : LinearMap.ker A = ⊥ := by
  apply LinearMap.ker_eq_bot'.mpr
  intro w hw
  obtain ⟨a, rfl⟩ := (finrank_eq_one_iff_of_nonzero' v hv).mp hdim w
  have hamu : a * μ = 0 := by
    have h := hw
    rw [map_smul, heigen, smul_smul] at h
    exact (smul_eq_zero.mp h).resolve_right hv
  have ha : a = 0 := (mul_eq_zero.mp hamu).resolve_right hμ
  simp [ha]

/-! Polynomial information at a crossing. The bridge identifying root
multiplicity with the dimension of the generalized resonant zero space remains
an analytic/spectral premise. -/
noncomputable def middleCrossingPolynomial (c e₁ e₂ : ℂ) : ℂ[X] :=
  (X - C c) * X * (X ^ 2 - C e₁ * X + C e₂)

theorem middle_polynomial_coefficients (c e₁ e₂ : ℂ) :
    (middleCrossingPolynomial c e₁ e₂).coeff 1 = -c * e₂ ∧
    (middleCrossingPolynomial c e₁ e₂).coeff 2 = c * e₁ + e₂ ∧
    (middleCrossingPolynomial c e₁ e₂).coeff 3 = -c - e₁ ∧
    (middleCrossingPolynomial c e₁ e₂).coeff 4 = 1 := by
  simp [middleCrossingPolynomial, coeff_mul, Finset.Nat.antidiagonal_succ, coeff_X]
  ring

theorem middle_crossing_constant_coefficient_zero
    (c e₁ e₂ : ℂ) (hc : c ≠ 0)
    (horder : X ^ 2 ∣ middleCrossingPolynomial c e₁ e₂) : e₂ = 0 := by
  have h := (X_pow_dvd_iff.mp horder) 1 (by omega)
  rw [(middle_polynomial_coefficients c e₁ e₂).1] at h
  exact (mul_eq_zero.mp h).resolve_left (neg_ne_zero.mpr hc)

theorem middle_crossing_third_order_iff
    (c e₁ : ℂ) (hc : c ≠ 0) :
    X ^ 3 ∣ middleCrossingPolynomial c e₁ 0 ↔ e₁ = 0 := by
  constructor
  · intro h
    have h₂ := (X_pow_dvd_iff.mp h) 2 (by omega)
    rw [(middle_polynomial_coefficients c e₁ 0).2.1] at h₂
    simp only [add_zero] at h₂
    exact (mul_eq_zero.mp h₂).resolve_left hc
  · intro h
    subst e₁
    refine ⟨X - C c, ?_⟩
    simp [middleCrossingPolynomial]
    ring

/-- For a middle polynomial of zero multiplicity between two and three, the
constant coefficient vanishes and the remaining coefficient determines the
multiplicity exactly. No diagonalizability assumption is used. -/
theorem middle_crossing_multiplicity_cases
    (c e₁ e₂ : ℂ) (hc : c ≠ 0)
    (hlower : 2 ≤ (middleCrossingPolynomial c e₁ e₂).rootMultiplicity 0)
    (hupper : (middleCrossingPolynomial c e₁ e₂).rootMultiplicity 0 ≤ 3) :
    e₂ = 0 ∧
    ((middleCrossingPolynomial c e₁ e₂).rootMultiplicity 0 = 3 ↔ e₁ = 0) ∧
    ((middleCrossingPolynomial c e₁ e₂).rootMultiplicity 0 = 2 ↔ e₁ ≠ 0) := by
  have hp : middleCrossingPolynomial c e₁ e₂ ≠ 0 := by
    intro h
    have h₄ := (middle_polynomial_coefficients c e₁ e₂).2.2.2
    rw [h] at h₄
    simp at h₄
  have hdiv : X ^ 2 ∣ middleCrossingPolynomial c e₁ e₂ := by
    simpa using (le_rootMultiplicity_iff hp).mp hlower
  have he₂ := middle_crossing_constant_coefficient_zero c e₁ e₂ hc hdiv
  refine ⟨he₂, ?_, ?_⟩
  · have h₃ : 3 ≤ (middleCrossingPolynomial c e₁ e₂).rootMultiplicity 0 ↔ e₁ = 0 := by
      rw [le_rootMultiplicity_iff hp]
      simpa [he₂] using middle_crossing_third_order_iff c e₁ hc
    constructor
    · intro h; exact h₃.mp (by omega)
    · intro h; have := h₃.mpr h; omega
  · have h₃ : 3 ≤ (middleCrossingPolynomial c e₁ e₂).rootMultiplicity 0 ↔ e₁ = 0 := by
      rw [le_rootMultiplicity_iff hp]
      simpa [he₂] using middle_crossing_third_order_iff c e₁ hc
    constructor
    · intro h he; have := h₃.mpr he; omega
    · intro h; have hn := mt h₃.mp h; omega

/-- The complete weighted full-cut product telescopes before the contact
Lefschetz identifications are inserted. All determinant denominators are
explicitly required to be nonzero. -/
theorem weighted_full_cut_telescoping
    (P₀ P₁ P₂ P₃ P₄ : ℂ)
    (h₀ : P₀ ≠ 0) (h₁ : P₁ ≠ 0) (h₂ : P₂ ≠ 0)
    (h₃ : P₃ ≠ 0) (h₄ : P₄ ≠ 0) :
    ((P₂ * P₁) ^ 2 * (P₄ * P₃) ^ 4) /
      ((P₁ * P₀) * (P₃ * P₂) ^ 3 * P₄ ^ 5) =
      (P₁ * P₃) / (P₀ * P₂ * P₄) := by
  field_simp

/-- Scalar cancellation of the finite chirality traces in the variation
calculation. The geometric diagonal-block identities remain premises. -/
theorem chirality_trace_cancellation (a₀ a₁ h₀ h₁ h₂ : ℂ) :
    -(a₀ - h₀) + (a₀ + h₀ + a₁ - h₁) - (a₁ + h₁ - h₂) =
      2 * h₀ - 2 * h₁ + h₂ := by ring

theorem torsion_supertrace_sign (h₀ h₁ h₂ : ℂ) :
    2 * h₀ - 2 * h₁ + h₂ = -(-h₀ + h₁ - h₂ + h₁ - h₀) := by ring

/-- The Cartan identity proves injectivity of the horizontal differential
when the compressed generator and the Lefschetz map are injective. -/
theorem horizontal_injective_of_cartan
    {U V W : Type*}
    [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (D : U →ₗ[ℂ] V) (Dnext : V →ₗ[ℂ] W)
    (B : U →ₗ[ℂ] U) (Lef : U →ₗ[ℂ] W)
    (hcartan : Dnext.comp D = Lef.comp B)
    (hB : Function.Injective B) (hLef : Function.Injective Lef) :
    Function.Injective D := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro u hu
  apply hB
  apply hLef
  have h := congrArg (fun F : U →ₗ[ℂ] W => F u) hcartan
  simpa [hu] using h.symm

/-- A contracting homotopy gives exactness on a nonzero resonance block.
The existence of the Cartan contraction is an input from the operator theory. -/
theorem contraction_implies_exactness
    {U V W : Type*}
    [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (prev : U →ₗ[ℂ] V) (next : V →ₗ[ℂ] W)
    (hprev : V →ₗ[ℂ] U) (hnext : W →ₗ[ℂ] V)
    (hcomplex : next.comp prev = 0)
    (hcontract : prev.comp hprev + hnext.comp next = LinearMap.id) :
    LinearMap.range prev = LinearMap.ker next := by
  apply le_antisymm
  · exact LinearMap.range_le_ker_iff.mpr hcomplex
  · intro v hv
    refine ⟨hprev v, ?_⟩
    have h := congrArg (fun F : V →ₗ[ℂ] V => F v) hcontract
    simpa [LinearMap.mem_ker.mp hv] using h

/-- Divisor specialization is valid away from the removable singularity. -/
theorem crossing_divisor_cancellation (G s c e : ℂ) (hs : s ≠ 0) :
    G * ((s - c) * (s ^ 2 - e * s)) / s = G * (s - c) * (s - e) := by
  field_simp

/-- For a fixed crossing parameter, continuity extends the cancelled
punctured divisor identity to its value at zero. This theorem makes no claim
about joint evaluation across changing metric parameters. -/
theorem crossing_value_of_punctured_divisor
    (Z G : ℂ → ℂ) (c e : ℂ)
    (hZ : ContinuousAt Z 0) (hG : ContinuousAt G 0)
    (hdiv : ∀ᶠ s in 𝓝[≠] (0 : ℂ),
      Z s = G s * ((s - c) * (s ^ 2 - e * s)) / s) :
    Z 0 = G 0 * c * e := by
  have hcancel : Z =ᶠ[𝓝[≠] (0 : ℂ)] (fun s => G s * (s - c) * (s - e)) := by
    filter_upwards [hdiv, self_mem_nhdsWithin] with s hs hne
    rw [hs]
    apply crossing_divisor_cancellation
    simpa using hne
  have hprod : ContinuousAt (fun s => G s * (s - c) * (s - e)) 0 :=
    (hG.mul (continuousAt_id.sub continuousAt_const)).mul
      (continuousAt_id.sub continuousAt_const)
  have heq := tendsto_nhds_unique_of_eventuallyEq
    (hZ.tendsto.mono_left nhdsWithin_le_nhds)
    (hprod.tendsto.mono_left nhdsWithin_le_nhds) hcancel
  simpa using heq

/-- The specialized value vanishes exactly in the third-multiplicity case. -/
theorem crossing_value_zero_iff (G c e : ℂ) (hG : G ≠ 0) (hc : c ≠ 0) :
    G * c * e = 0 ↔ e = 0 := by
  simp [mul_eq_zero, hG, hc]

/-- A simple zero is certified by its nonzero derivative. Differentiability
of the complementary factor is an explicit premise, not a torsion theorem. -/
theorem crossing_simple_zero
    (G : ℂ → ℂ) (G' c : ℂ) (hG : HasDerivAt G G' 0)
    (hG0 : G 0 ≠ 0) (hc : c ≠ 0) :
    (G 0 * (0 - c) * 0 = 0) ∧
    HasDerivAt (fun s => G s * (s - c) * s) (-G 0 * c) 0 ∧
    -G 0 * c ≠ 0 := by
  refine ⟨by simp, ?_, mul_ne_zero (neg_ne_zero.mpr hG0) hc⟩
  have h := (hG.mul ((hasDerivAt_id (0 : ℂ)).sub_const c)).mul
    (hasDerivAt_id (0 : ℂ))
  simpa [Pi.mul_def, id_eq] using h

/-- With analyticity of the complementary factor, the simple-zero
certificate gives analytic order exactly one. -/
theorem crossing_analytic_order_one
    (G : ℂ → ℂ) (c : ℂ) (hG : AnalyticAt ℂ G 0) (hG0 : G 0 ≠ 0) (hc : c ≠ 0) :
    analyticOrderAt (fun s => G s * (s - c) * s) 0 = 1 := by
  have hprod : AnalyticAt ℂ (fun s => G s * (s - c) * s) 0 := by fun_prop
  have hsimple := crossing_simple_zero G (deriv G 0) c
    hG.differentiableAt.hasDerivAt hG0 hc
  apply hprod.analyticOrderAt_eq_one_of_zero_deriv_ne_zero (by simp)
  rw [hsimple.2.1.deriv]
  exact hsimple.2.2

end FriedLeanVerification
