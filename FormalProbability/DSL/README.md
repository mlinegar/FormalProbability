# DSL: design-based supervised learning

This directory formalizes design-based supervised learning (Egami, Hinck, Stewart & Wei).
Here "DSL" does not mean debiased/double machine learning. Automated (e.g. LLM)
annotations are available for all documents, and expert labels for a subset sampled with
known probability π. The design-adjusted outcome Ỹ = Ŷ − (R/π)(Ŷ − Y) then gives unbiased
moments regardless of prediction accuracy. The built modules depend only on Mathlib, not
on `CLT/`.

- **Estimator chain.** This chain is imported through `DSL.lean`.
  - `CoreDefinitions`, `SamplingTheory`, and `MomentFunctions` set up the objects.
  - `DSLEstimator` proves `DSL_unbiased` and `DSLMoment_unbiased`.
  - `CrossFitting` and `BiasAnalysis` cover cross-fitting and the bias of naive estimators.
  - `AsymptoticTheory` and the model files build on these, and `MainTheorems` collects the
    headline results.
- **Asymptotic results are conditional.** The asymptotic results (`DSL_consistent`,
  `DSL_asymptotic_normal`, `DSL_valid_coverage`, and the theorems built on them) follow
  from the assumption bundle `MEstimationAxioms`, whose fields state those conclusions. See
  the README's [caveats](../../README.md#caveats-on-the-asymptotic-results).
- **IPW, clustering, and judges.** `IPWTheory`, `ClusteredVariance`, and `JudgeCalibration`
  are imported directly by the root module. They cover:
  - Horvitz-Thompson and Hájek estimators with logged propensities;
  - document-clustered standard errors;
  - judge-versus-oracle calibration for LLM judges.
- **Not built.** `MEstimationCore` is not imported by anything, and it imports a missing
  module (`FormalProbability.Probability.Core`).

For per-module results and status, see the
[module map](../../README.md#design-based-supervised-learning-dsl). The import graph is in
[docs/OVERVIEW.md](../../docs/OVERVIEW.md#dsl).
