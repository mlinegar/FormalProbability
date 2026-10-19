# DSL: design-based supervised learning

This area formalizes design-based supervised learning (Egami, Hinck, Stewart & Wei,
NeurIPS 2023). Here "DSL" does not mean double/debiased machine learning. Automated (for
example, LLM) annotations are available for every document, and expert labels for a
subset sampled with known probability π. The design-adjusted outcome
Ỹ = Ŷ − (R/π)(Ŷ − Y) then yields unbiased moments regardless of how accurate the
predictions are.

- **Estimator.** `CoreDefinitions`, `SamplingTheory`, and `MomentFunctions` set up
  documents, oracle labels, the sampling design, and moment functions for common models.
  `DSLEstimator` proves that the design-adjusted outcome and moment are unbiased
  (`DSL_unbiased`, `DSLMoment_unbiased`). `CrossFitting` extends the moment to
  cross-fitted predictors.
- **Bias and variance.** `BiasAnalysis` and `AsymptoticTheory` show how ignoring
  prediction error biases naive estimators (`naive_estimator_biased_general`).
  `VarianceDecomposition` studies how precision depends on the number of expert labels and
  on prediction quality.
- **Asymptotics and models.** `AsymptoticTheory`, `MEstimationCore`, the model files
  (linear and logistic regression, category proportions, fixed effects, and moment
  functions for multinomial logit, instrumental variables, and regression discontinuity),
  and `MainTheorems` state the paper's consistency, asymptotic-normality, and coverage
  results. These are currently stated relative to explicit assumption structures rather
  than derived from the CLT area.
- **IPW, clustering, and judges.** `IPWTheory` covers Horvitz-Thompson and Hájek
  estimators with logged sampling propensities, `ClusteredVariance` covers standard errors
  when many observations share a document, and `JudgeCalibration` covers calibrating an LLM
  judge against an oracle on a propensity-weighted calibration set.
