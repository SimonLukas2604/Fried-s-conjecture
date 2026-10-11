# Lean check for the Fried-obstruction manuscript

This project formalizes the algebraic crossing step in
[`ordinary_fried_obstruction.tex`](ordinary_fried_obstruction.tex): the exact
ratio identity and the implication that coefficient-ratio limits `1`, `1`,
and `0` force the normalized zeta ratio (and its modulus) to tend to zero.

Run the check with:

```sh
lake build
```

The proof is conditional on those three coefficient limits. The manuscript's
geometric construction, resonance-crossing argument, uniform holomorphy, and
finite-cut torsion variation are analytic inputs and are not formalized here.
