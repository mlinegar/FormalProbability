/-!
# DSL: design-based supervised learning

## Overview

This area formalizes design-based supervised learning (DSL; Egami, Hinck, Stewart & Wei,
NeurIPS 2023): using automated (for example, LLM) annotations in downstream estimation,
corrected by a design-based sample of expert labels with known sampling probabilities. It
also contains:

- inverse probability weighting (Horvitz-Thompson and Hájek estimators)
- cross-fitting
- document-clustered standard errors
- calibration of an LLM judge against an oracle
- M-estimation scaffolding linked to the probability definitions in `CLT/Core`

## Main results

| Declaration | File | Statement |
|-------------|------|-----------|
| `DSL_unbiased`, `DSLMoment_unbiased` | DSLEstimator | The design-adjusted outcome and moment are unbiased when E[R] = π |
| `naive_estimator_biased_general` | AsymptoticTheory | The naive plug-in moment is biased when prediction error shifts its expectation |
| `variance_decreases_with_n` | VarianceDecomposition | More expert labels reduce the approximate variance |
| `hajek_bounded_by_value_bound` | IPWTheory | The Hájek estimate is bounded by the bound on the values |
| `variance_inflation_icc` | ClusteredVariance | The design effect is at least 1 |
| `judge_error_decomposition` | JudgeCalibration | Weighted MSE = bias² + variance |

The asymptotic results (consistency, asymptotic normality, coverage) are stated relative to
the assumption structures `MEstimationAxioms` and `CoverageAxioms`, whose fields are those
asymptotic properties. They record the paper's claims in a precise form; deriving them from
the CLT area is future work.

## File structure

```
DSL/
├── CoreDefinitions.lean         # documents, oracle access, outcome specifications
├── SamplingTheory.lean          # design-based sampling (Assumption 1)
├── MomentFunctions.lean         # moment functions for GLMs
├── MEstimationCore.lean         # population and empirical moments, M-estimation assumptions
├── DSLEstimator.lean            # design-adjusted outcome and moments
├── CrossFitting.lean            # cross-fitted predictors
├── BiasAnalysis.lean            # bias from ignoring prediction error
├── AsymptoticTheory.lean        # consistency, normality, sandwich variance
├── VarianceDecomposition.lean   # variance and power
├── LinearRegression.lean        # DSL linear regression
├── LogisticRegression.lean      # DSL logistic regression
├── MultinomialLogistic.lean     # multinomial logit moments
├── InstrumentalVariables.lean   # IV moments
├── RegressionDiscontinuity.lean # regression discontinuity moments
├── CategoryProportion.lean      # category proportions
├── FixedEffects.lean            # panel data with fixed effects
├── MainTheorems.lean            # summary of the main statements
├── IPWTheory.lean               # Horvitz-Thompson and Hájek estimators
├── ClusteredVariance.lean       # clustered standard errors
├── JudgeCalibration.lean        # judge-versus-oracle calibration
└── README.lean                  # this file
```

## Key formulas

Design-adjusted outcome (Equation 4): Ỹ = Ŷ - (R/π)(Ŷ - Y).

DSL linear regression (Equation 6): β̂_DSL = (X'X)⁻¹X'Ỹ.

Clustered variance: Var(θ̂) = Σ_c Var(Σ_{i∈c} ψ_i), rather than assuming independence
across observations.

## Assumptions

Assumptions are bundled as structures that appear as explicit theorem parameters, not as
Lean `axiom` declarations.

| Structure | Location | Purpose |
|-----------|----------|---------|
| `OracleAccess` | CoreDefinitions | Expert labels equal oracle labels |
| `MEstimationAxioms` | AsymptoticTheory | M-estimation asymptotics |
| `CoverageAxioms` | AsymptoticTheory | Confidence-interval coverage |
| `MEstimationAssumptions` | MEstimationCore | i.i.d. sampling, identification, law of large numbers |
-/
