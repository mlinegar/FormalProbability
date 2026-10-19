# CLT: probability foundations and the central limit theorem

This directory builds the probability needed for a proof of the classical i.i.d. central
limit theorem, on top of Mathlib. Every module here is imported by `CLT.lean` and is built.
Every theorem is fully proved.

- **Foundations.** `Core`, `ProbabilityLaws`, `Distributions`, `GeneratingFunctions`,
  `WeakLaw`, `Normal`. `Core` provides `expectation`, `IID`, `sampleMean`, and the
  convergence notions that `Econometrics` and `ML` import.
- **Analytic tools.** `HellySelection` and `LevyContinuity`. The main tool is
  `tendsto_probabilityMeasure_of_tendsto_charFun`: if characteristic functions converge to
  those of a probability measure μ, the measures converge weakly to μ.
- **CLT.** `CLT.lean` proves `central_limit_theorem_iid_finite_variance`, its bounded and
  third-moment variants, and a CDF form.

The Lindeberg-Feller (triangular-array) CLT is not formalized. `lean_clt.pdf` is a copy of
the Avigad, Hölzl & Serafin paper (arXiv:1405.7012v4), the prior Isabelle formalization; it
is not documentation for this code.

For per-module results and status, see the [module map](../../README.md#probability-clt-all-built).
The import graph is in [docs/OVERVIEW.md](../../docs/OVERVIEW.md#clt-and-shared).
