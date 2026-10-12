# Lean verification work for the Fried-obstruction manuscript

**Status: 54 checked theorems; a full verification of the geometric
counterexample is still incomplete.** This project proves algebraic,
finite-dimensional, Banach-algebra, analytic-function, and limiting deductions
from explicit premises. It does not construct the manuscript's manifold,
geodesic flow, resonant spaces, Ruelle zeta, or analytic torsion. A successful
build therefore does not certify the manuscript's main counterexample theorem.

The manuscript is `ordinary_fried_obstruction.tex`, SHA-256:

```
23672871936c6af5c6b13fc556a701027014a770ab291bb1c59652902ee5681e
```

## Announcement manuscript

The announcement is available as a [PDF](Fried_conjecture.pdf) and
[LaTeX source](main-55.tex). These files preserve the supplied manuscript snapshot.

## Reproducing the checks

The toolchain is pinned to `leanprover/lean4:v4.35.0-rc3`; Mathlib is pinned to
commit `331d5244f0d3aad530d9ab00ded135b4c7691502`. With Lean/Lake available:

```sh
lake exe cache get
lake build
```

The first command obtains Mathlib's precompiled dependencies. `lake build`
checks the main module, its imported submodules, the conditional obstruction
module, and the complete theorem axiom report. Every project proof module
sets `warningAsError` to `true`. No project theorem uses `sorry`, `admit`, a
custom axiom, `unsafe`, or `native_decide`. `AxiomsCheck.lean` prints the
transitive axioms of all 54 project theorems. The audit permits only Lean's
standard `propext`, `Classical.choice`, and `Quot.sound`; these are logical
axioms, not assumed results about geometry or torsion. Mathematical assumptions
remain visible as theorem arguments, even when the axiom report is clean.

`build.log` contains the build and axiom evidence for this source snapshot.
`verification.json` records the theorem count, source hashes, toolchain,
Mathlib revision, and audit outcome. The pinned Lake manifest is included so
the dependency versions used by the check can be reproduced.

## Strongest assembled theorem

`FriedLeanVerification.conditional_crossing_obstruction`, in
`FriedLeanVerification/ConditionalObstruction.lean`, proves the following for
an abstract ordinary-value function `Z`, under its explicitly listed inputs:

- There exists a crossing sequence `σ` with
  `0 < σ n ≤ 4 * K * (θ n)^2 / r` and the exact root equation.
- Its metric parameters tend to zero.
- The complex ratio `Z n (σ n) / Z n 0` tends to zero.
- Eventually the calibrated target is positive and
  `‖Z n (σ n)‖ < target n`, hence the ordinary value does not have the target
  modulus. This conclusion includes zero crossing values.

The theorem assumes positive characters tending to zero. This is sufficient
for the existence of a counterexample sequence if the geometric inputs can
be supplied. It does not prove the manuscript's statement for every small
nonzero real character.

Its premises are concrete: continuous crossing functions with the axis lower
bound, bounded quadratic perturbation, and negative endpoint; continuous
coefficient factors `C,A` with `C(0,0) ≠ 0` and `A(0,0)=0`; nonvanishing
reference factor `G₀`; a bounded exponent for its variation; the hyperbolic
value identity; the specialized crossing value identity; and calibration of
the target to the reference modulus. `Z` and `target` are abstract functions.
Neither is identified in Lean with Ruelle zeta or Ray–Singer torsion.

`abstract_counterexample_ratio` remains available as the earlier, weaker
conditional limit theorem. It assumes convergence of the crossing parameters;
the new theorem constructs them from IVT input estimates and includes eventual
strict discrepancy. Neither conditional theorem closes the geometric gap.

The factored quotient and abstract ratio theorems now require the character
parameter to be nonzero only eventually, which is sufficient for their limits.
`finite_trace_exponential_tends_to_one` also composes the bounded finite-trace
integral estimate directly with the exponential normalization limit; its trace
bound need only hold eventually.

## Checked results and their boundaries

| Manuscript component | Checked Lean result | Still required to apply it to the manuscript |
|---|---|---|
| Appendix matrix construction | The explicit integral 4×4 matrix preserves the intersection form; its characteristic polynomial is `X⁴-X³-X²-X+1`; `det(I-T)=-1`. | Identify this matrix as the action of a surface mapping class. |
| Homological polynomial criterion | Reduction modulo two is the fifth cyclotomic polynomial; the order of two modulo five is four; irreducibility over `F₂`, `ℤ`, and `ℚ`; a real root in `(1,2)`; noncyclotomicity; no proper substitution `q(Xᵏ)`. | Mapping-class surjectivity, the pseudo-Anosov criterion, and hyperbolization. |
| Small Hodge slot | A nonzero eigenvector with nonzero eigenvalue spanning a rank-one slot excludes its kernel. | Construct the spectral slots, prove their ranks and eigenvector relation, and identify Hodge kernels with cohomology. |
| Uniform character disk | Uniform multiplier/resolvent norm bounds give an explicit common disk with an invertible Neumann factor. | Construct the anisotropic spaces and resolvents, establish the bounds and inverse factorization, and prove holomorphic/metric dependence. |
| Cut rank persistence | Finite-rank continuous projections at operator distance less than one have equal ranks, even on an infinite-dimensional ambient space. | Construct the spectral projections, prove idempotence and the closeness estimate, and compute reference ranks. |
| Even coefficient factorization | Evenness kills the derivative at zero; an analytic coefficient vanishing there factors as `z² q(z)` with `q` analytic at zero. Joint continuity and a nonzero constant quotient imply nearby nonvanishing. | Derive evenness of the geometric determinants and uniform metric continuity of these quadratic quotients on one complex disk. A fixed-metric analytic factorization alone does not give this. |
| Cartan injectivity | The identity `Dnext ∘ D = W ∘ B`, with injective `W,B`, implies injectivity of `D`. | Prove the geometric operator identities, contact Lefschetz isomorphisms, and compatibility with the cut. |
| Nonzero-block exactness | A cochain contraction implies `range(prev)=ker(next)`. | Construct the Cartan contraction on generalized nonzero resonances. |
| Crossing | Endpoint IVT; quadratic crossing bound; selection of a crossing sequence tending to zero; the sharper asymptotic `σ/θ² → κ/(2r)` from the displayed root equation and coefficient/axis limits. | Derive the negative scalar root, positive axis slope, joint coefficient limits, reality, continuity, and bounds for the actual spectral family. |
| Full zero complex | From the full split complex's endpoint differential formulas and exactness, derive horizontal injection and surjection. Rank-nullity gives middle dimension at least two, and the cut bound gives two or three. | Construct the resonant complex; prove its exactness from pullback acyclicity; establish the differential formulas and zero-space dimensions. Horizontal exactness is not assumed. |
| Crossing multiplicities | For `(X-c)X(X²-e₁X+e₂)`, lower zero multiplicity two implies `e₂=0`; with multiplicity at most three, the two cases are exactly `m=3 ↔ e₁=0` and `m=2 ↔ e₁≠0`. | Identify this polynomial as the middle cut characteristic polynomial and its root multiplicity as generalized zero-space dimension. |
| Full cut divisor | The five-degree weighted determinant product telescopes; contact-specialized factors cancel; the punctured crossing identity extends to the value at zero under continuity. | Prove the actual full/horizontal cut determinant identities and the zeta/complementary-factor bridge, including its conventions. |
| Ordinary zero case | Nonzero `G(0),c` give the exact zero/nonzero criterion; when `e₁=0`, the derivative is nonzero and the analytic order is exactly one. | Identify the actual fixed-parameter zeta germ with the specialized analytic product and prove its complementary factor is analytic/nonzero. |
| Finite-cut torsion variation | The displayed chirality traces cancel with the claimed supertrace sign. An eventually bounded finite trace bounds the integral exponent and gives an exponential normalization tending to one. | Prove chirality preservation and determinant-line torsion differentiation, the diagonal-block formulas, projector transport regularity, the dynamical torsion bridge and invariance, and the uniform trace bound. |
| Relative coefficient limits | Joint continuity and `c=θ²C`, `e₁=θ²A` give the two root quotients tending to one and zero. | Construct the uniform quotients with their hyperbolic origin values. |
| Final normalized value | Exact ratio identity, complex/modulus limit zero, and eventual strict discrepancy under calibration. | Fried's hyperbolic modulus identity, odd-dimensional unitary analytic-torsion metric invariance, and the identification with the conjecture's actual target. |

## Remaining hypotheses needed for a full counterexample verification

1. **Geometry and topology.** Construct the closed oriented genus-two surface,
   a pseudo-Anosov mapping class inducing the checked matrix, its mapping
   torus, and the hyperbolic metric. Formalize the Wang sequence calculation
   giving `b₁=1`, a nonzero harmonic form, and a smooth conformal metric family
   with negative curvature and smooth convergence as the parameter vanishes.
   Matrix arithmetic does not supply these existence theorems.
2. **Twisted Hodge acyclicity.** Define the unitary local system, holonomy and
   twisted differential/adjoint. Prove the nontrivial character interval,
   elliptic spectral projection continuity and ranks, positivity and quadratic
   expansion of the small scalar eigenvalue, exactness of the one-form slot,
   duality in the remaining degrees, the coexact gap, and acyclicity of the
   sphere-bundle pullback. The rank-one slot lemma only checks a deduction
   after these analytic and cohomological objects have been supplied.
3. **Selberg calibration and microlocal spectra.** Define the geometric
   Ruelle/Selberg determinants, their continuation and zero multisets. Verify
   the manuscript's convention translations, degreewise multiplicities,
   scalar zero exclusion, common spectral cut and ranks, contact splitting,
   and characteristic-polynomial identities, including the spectral
   dimension/multiplicity bridge. None follows merely from a formal polynomial
   supplied as a theorem argument.
4. **CDDP perturbation and symmetry.** Construct the smoothing operator and
   conformal direction; prove nondegeneracy and the positive slope with the
   chosen orientation/sign convention. Establish the reversal pairing and
   holomorphic continuation that make the characteristic coefficients even
   and real, and transport the untwisted/hyperbolic axis identities.
5. **Uniform holomorphy and quotient continuity.** The Neumann-factor and
   projection-rank lemmas are generic functional analysis. The anisotropic
   level bounds, metric continuity with loss of level, contour projector
   moments, finite frames, and joint regularity of compressed matrices are
   unproved. The fixed-disk Cauchy quotient representation and its uniform
   parameter estimate must also be formalized. The final theorem currently
   assumes joint continuity of `C,A`; it does not derive it from holomorphy.
6. **Resonant complex identification.** Prove that the full generalized zero
   complex computes the twisted de Rham cohomology, and hence is exact for
   the constructed acyclic character. Verify the endpoint formulas,
   one-dimensional zero generators, zero restrictions of the Lie derivative,
   Cartan relation, cut bound and generalized multiplicity identification.
   The finite-dimensional deduction then applies without horizontal exactness
   or semisimplicity assumptions.
7. **Full-cut torsion and actual ordinary value.** Construct finite-complex
   chirality torsion and the dynamical torsion invariant; prove their
   differentiability and the arbitrary full-cut variation formula. Establish
   the compressed trace's bounded extension at the trivial character. Prove
   the divisor/normalization identities for the actual zeta germ at each
   fixed crossing. Finally formalize Fried calibration, metric invariance of
   acyclic unitary analytic torsion on the base, and the conjecture's precise
   regularity, nonvanishing and modulus assertion.

These are unproved mathematical premises, not added Lean axioms and not
proved merely by citing their names. This project does not independently
validate the applicability or conventions of the external results cited in
the manuscript, and the successful checks should not be presented as such.

## Source modules

- `FriedLeanVerification.lean`: original scalar algebra, IVT, dimension lower
  bound, continuity quotient limits, and abstract ratio theorem.
- `FriedLeanVerification/AlgebraInputs.lean`: matrix and polynomial criteria,
  spectral-slot deduction, Cartan/contraction algebra, crossing multiplicities,
  cut telescoping, trace cancellation, divisor specialization and analytic order.
- `FriedLeanVerification/AnalyticInputs.lean`: common Neumann disk, projection
  transfer/rank stability, bounded trace integral and crossing asymptotic.
- `FriedLeanVerification/HolomorphicInputs.lean`: even derivative and local
  quadratic analytic factor, and joint-continuity nonvanishing deduction.
- `FriedLeanVerification/CrossingConsequences.lean`: endpoint full-complex
  deduction, resonant polynomial cases, crossing sequence and strict discrepancy.
- `FriedLeanVerification/ConditionalObstruction.lean`: explicit conditional
  assembly of crossing construction, ratio limit and eventual discrepancy.
- `AxiomsCheck.lean`: all-theorem transitive axiom audit, included in the build.
