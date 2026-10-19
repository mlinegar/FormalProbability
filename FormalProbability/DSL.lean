-- Core definitions and the sampling design
import FormalProbability.DSL.CoreDefinitions
import FormalProbability.DSL.SamplingTheory

-- Moment functions and the DSL estimator
import FormalProbability.DSL.MomentFunctions
import FormalProbability.DSL.MEstimationCore
import FormalProbability.DSL.DSLEstimator
import FormalProbability.DSL.CrossFitting

-- Bias, asymptotics, and variance
import FormalProbability.DSL.BiasAnalysis
import FormalProbability.DSL.AsymptoticTheory
import FormalProbability.DSL.VarianceDecomposition

-- Specific models
import FormalProbability.DSL.LinearRegression
import FormalProbability.DSL.LogisticRegression
import FormalProbability.DSL.MultinomialLogistic
import FormalProbability.DSL.InstrumentalVariables
import FormalProbability.DSL.RegressionDiscontinuity
import FormalProbability.DSL.CategoryProportion
import FormalProbability.DSL.FixedEffects

-- Summary of the main statements
import FormalProbability.DSL.MainTheorems

-- Inverse probability weighting, clustered variance, and judge calibration
import FormalProbability.DSL.IPWTheory
import FormalProbability.DSL.ClusteredVariance
import FormalProbability.DSL.JudgeCalibration

/-!
# FormalProbability.DSL

Entry point for the formalization of design-based supervised learning (DSL; Egami, Hinck,
Stewart & Wei, NeurIPS 2023).

DSL uses automated annotations (for example, LLM labels) for every document, together with
expert labels for a subset sampled with known probability π. The design-adjusted outcome

  Ỹ = Ŷ - (R/π)(Ŷ - Y)

corrects for prediction error by construction, so downstream moments stay unbiased however
good or bad the predictions are. This area states the estimator and its sampling design,
proves the design-correction and bias results, and records the asymptotic theory against
explicit assumption structures. It also covers the Horvitz-Thompson and Hájek estimators,
document-clustered variance, and calibration of an LLM judge against an oracle.
-/
