/-!
# DSL Module: Design-based Supervised Learning

## Overview

This module formalizes **design-based supervised learning** (DSL; Egami, Hinck, Stewart,
Wei): using automated (e.g. LLM) annotations in downstream estimation, corrected by a
design-based sample of expert labels with known sampling probabilities. It also contains:

- Inverse probability weighting (Horvitz-Thompson / Hajek estimators)
- Cross-fitting and sample splitting
- Clustered standard errors
- Judge-versus-oracle calibration
- M-estimation scaffolding

## Main Results

| Theorem | File | Statement |
|---------|------|-----------|
| `DSL_unbiased`, `DSLMoment_unbiased` | DSLEstimator | E[design-adjusted - true] = 0 for a linear expectation with E[R] = pi |
| `naive_estimator_biased_general` | AsymptoticTheory | Naive plug-in moment is biased when prediction error shifts the expected moment |
| `hajek_bounded_by_value_bound` | IPWTheory | Hajek estimate is bounded by the bound on the values |
| `variance_inflation_icc` | ClusteredVariance | Design effect is at least 1 |
| `judge_error_decomposition` | JudgeCalibration | Weighted MSE = bias^2 + variance |
| `DSLMomentCF_eq_of_const` | CrossFitting | Cross-fitting with one shared predictor reduces to the DSL moment |

Status notes: `DSL_consistent`, `DSL_asymptotic_normal`, `DSL_valid_coverage` and the
theorems built on them are applications of the `MEstimationAxioms` / `CoverageAxioms`
bundles (see Assumptions below). `hajek_unbiased_axiom` and `hajek_variance_bound` have
conclusion `True` (placeholders). `MEstimationCore.lean` is not imported anywhere and imports
a missing module.

## File Structure

```
DSL/
├── CoreDefinitions.lean       # Basic types for DSL
├── SamplingTheory.lean        # Sampling and probability foundations
├── CrossFitting.lean          # Sample splitting for bias reduction
├── MomentFunctions.lean       # Moment conditions for estimation
├── DSLEstimator.lean          # DSL estimator (design-adjusted outcome)
├── AsymptoticTheory.lean      # Asymptotic normality results
├── BiasAnalysis.lean          # Bias decomposition
├── VarianceDecomposition.lean # Variance estimation
├── LinearRegression.lean      # DSL linear regression (OLS on adjusted outcome)
├── LogisticRegression.lean    # Logistic regression
├── MultinomialLogistic.lean   # Multinomial logit
├── FixedEffects.lean          # Panel data models
├── InstrumentalVariables.lean # IV estimation
├── RegressionDiscontinuity.lean # RDD design
├── CategoryProportion.lean    # Categorical outcomes
├── MEstimationCore.lean       # General M-estimation (not built; missing import)
├── MainTheorems.lean          # Curated exports
├── IPWTheory.lean             # Inverse probability weighting
├── ClusteredVariance.lean     # Clustered standard errors
├── JudgeCalibration.lean      # Judge model calibration
```

## Key Concepts

### Inverse Probability Weighting (IPW)

IPW reweights samples to correct for selection bias:
```
E[Y·w(X)] = E[Y | treated]
```
where w(X) = 1/P(treated | X).

### Cross-Fitting

Split data into K folds, fit nuisance parameters on K-1 folds,
evaluate on held-out fold. Reduces bias from overfitting.

### Clustered Standard Errors

When observations are correlated within clusters:
```
Var(θ̂) = Σ_c Var(Σ_{i∈c} ψ_i)
```
rather than assuming independence.

## Assumptions

This module bundles assumptions as **structures** (explicit theorem parameters)
rather than Lean `axiom` declarations. This makes them explicit parameters to theorems,
which is cleaner for a formalization that aims to be modular.

| Structure | Location | Purpose | Justification |
|-----------|----------|---------|---------------|
| `OracleAccess` | CoreDefinitions | Expert labels = oracle labels | Design assumption |
| `MEstimationAxioms` | AsymptoticTheory | M-estimation asymptotics | Newey & McFadden 1994 |
| `CoverageAxioms` | AsymptoticTheory | CI coverage properties | Standard asymptotic theory |

Note: the fields of `MEstimationAxioms` and `CoverageAxioms` are the asymptotic conclusions
themselves, quantified over arbitrary sequences, and `RegularityConditions` / `NormalLimit`
have only `True` fields. The theorems that take these bundles record the intended results;
they are not yet proofs of them.
-/
