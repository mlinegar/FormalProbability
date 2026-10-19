# CLT: probability foundations and the central limit theorem

This area builds, on top of Mathlib, the probability needed for a proof of the classical
i.i.d. central limit theorem by characteristic functions.

- **Foundations.** `Core` defines expectation, i.i.d. sequences, sample means, and
  convergence in probability and in distribution; the econometrics, DSL, and ML areas
  import it. `ProbabilityLaws`, `Distributions`, `GeneratingFunctions`, `WeakLaw`, and
  `Normal` cover laws of random variables, standard distributions, probability generating
  functions, the weak law of large numbers, and the standard normal.
- **Analytic tools.** `HellySelection` extracts convergent subsequences of distribution
  functions, and `LevyContinuity` proves that convergence of characteristic functions to
  those of a probability measure implies weak convergence
  (`tendsto_probabilityMeasure_of_tendsto_charFun`).
- **The theorem.** `CLT` proves `central_limit_theorem_iid_finite_variance`: for i.i.d.
  mean-zero variables with variance σ², the law of the normalized sum converges weakly to
  the normal distribution with variance σ². It also gives variants, including a form for
  distribution functions.

The Lindeberg-Feller (triangular-array) CLT is not formalized. For the earlier Isabelle/HOL
formalization, see Avigad, Hölzl & Serafin, "A formally verified proof of the Central Limit
Theorem" ([arXiv:1405.7012](https://arxiv.org/abs/1405.7012)); Rémy Degenne's Lean
development (https://github.com/RemyDegenne/CLT) also predates this one.
