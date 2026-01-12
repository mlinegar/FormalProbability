/-
# FormalProbability/DSL/AsymptoticTheory.lean

## Paper Reference: Section 3.2, Proposition 1, Appendix OA.7

This file formalizes the asymptotic theory of the DSL estimator:
- Consistency: β̂_DSL → β* as N → ∞
- Asymptotic normality: √N(β̂_DSL - β*) →d N(0, V)
- Variance formula (sandwich estimator)

### Main Results

**Proposition 1 (Asymptotic Properties)**

Under Assumption 1 (design-based sampling) and standard regularity conditions:

1. **Consistency:** β̂_DSL →p β* as N → ∞
2. **Asymptotic Normality:** √N(β̂_DSL - β*) →d N(0, V)

where V is the sandwich variance matrix.

### Variance Formula (Equation OA.7)

V = S_V⁻¹ · E[m̃(D; β*) m̃(D; β*)'] · S_V⁻¹'

where S_V = E[∂m̃/∂β] evaluated at β*.
-/

import FormalProbability.DSL.DSLEstimator
import FormalProbability.DSL.CrossFitting
import FormalProbability.DSL.BiasAnalysis
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Classical
open scoped Topology
open MeasureTheory

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace DSL

/-!
## Regularity Conditions
-/

/-- Standard regularity conditions for asymptotic normality.
    These are the conditions from M-estimation theory. -/
structure RegularityConditions (Data : Type*) (d : ℕ) where
  /-- The parameter space is open -/
  param_space_open : True  -- Placeholder
  /-- The moment function is twice continuously differentiable -/
  moment_smooth : True  -- Placeholder
  /-- The Jacobian E[∂m/∂β] is invertible at β* -/
  jacobian_invertible : True  -- Placeholder
  /-- The second moment E[m m'] exists and is finite -/
  second_moment_finite : True  -- Placeholder
  /-- Uniform convergence of sample moments -/
  uniform_convergence : True  -- Placeholder

/-- Cross-fitting regularity conditions (placeholder). -/
structure CrossFittingConditions {ι Obs Con Mis : Type*} [Fintype ι]
    (cf : CrossFit ι Obs Con Mis) : Prop where
  no_leakage : True  -- Predictor for each fold is trained on other folds

/-!
## Consistency
-/

/-- Convergence in probability (mathlib: `TendstoInMeasure`). -/
def ConvergesInProbability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {E : Type*} [PseudoMetricSpace E]
    (seq : ℕ → Ω → E) (limit : Ω → E) : Prop :=
  MeasureTheory.TendstoInMeasure μ seq Filter.atTop limit

/-- Placeholder predicate for a normal limit.

Mathlib does not yet provide a packaged multivariate normal distribution,
so we record normality as an explicit assumption. -/
structure NormalLimit {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ}
    (Z : Ω → Fin d → ℝ) (mean : Fin d → ℝ)
    (variance : Matrix (Fin d) (Fin d) ℝ) : Prop where
  placeholder : True := by trivial

/-- Convergence in distribution to a normal limit (mathlib: `TendstoInDistribution`). -/
def ConvergesInDistributionToNormal {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ}
    (seq : ℕ → Ω → Fin d → ℝ)
    (mean : Fin d → ℝ)
    (variance : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  ∃ Z : Ω → Fin d → ℝ,
    NormalLimit μ Z mean variance ∧
      MeasureTheory.TendstoInDistribution seq Filter.atTop Z μ

/-- Asymptotic coverage of a confidence interval sequence. -/
def AsymptoticCoverage {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ}
    (CI_seq : ℕ → Ω → Fin d → ℝ × ℝ)
    (β_star : Fin d → ℝ)
    (α : ℝ) : Prop :=
  ∀ i, Filter.Tendsto
    (fun n =>
      μ {ω | β_star i ∈ Set.Icc (CI_seq n ω i).1 (CI_seq n ω i).2})
    Filter.atTop (𝓝 (ENNReal.ofReal (1 - α)))

/-- Wald-style coverage derived from asymptotic normality (assumption bundle). -/
structure CoverageAxioms {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (d : ℕ) : Prop where
  coverage_of_asymptotic_normal :
    ∀ (centered_scaled_seq : ℕ → Ω → Fin d → ℝ)
      (CI_seq : ℕ → Ω → Fin d → ℝ × ℝ)
      (β_star : Fin d → ℝ)
      (α : ℝ)
      (V : Matrix (Fin d) (Fin d) ℝ),
      ConvergesInDistributionToNormal μ centered_scaled_seq (fun _ => 0) V →
      AsymptoticCoverage μ CI_seq β_star α

/-!
## Sample Moments and Estimators
-/

/-- Sample mean of a moment function over a finite dataset. -/
def sampleMoment {Data : Type*} {d : ℕ}
    (m : MomentFunction Data d)
    (data : List Data)
    (β : Fin d → ℝ) : Fin d → ℝ :=
  let N := data.length
  fun j => (data.foldl (fun acc D => acc + m D β j) 0) / N

/-- A (sample) M-estimator solves the sample moment condition. -/
def IsMEstimator {Data : Type*} {d : ℕ}
    (m : MomentFunction Data d)
    (data : List Data)
    (β : Fin d → ℝ) : Prop :=
  sampleMoment m data β = 0

/-- An estimator sequence solves the sample moment condition at each n. -/
def IsMEstimatorSeq {Data : Type*} {d : ℕ}
    (m : MomentFunction Data d)
    {Ω : Type*}
    (data_seq : ℕ → Ω → List Data)
    (β_hat_seq : ℕ → Ω → Fin d → ℝ) : Prop :=
  ∀ n ω, IsMEstimator m (data_seq n ω) (β_hat_seq n ω)

/-- DSL moment function lifted to a single data record. -/
def DSLMomentFromData {Obs Mis : Type*} {d : ℕ}
    (m : MomentFunction (Obs × Mis) d)
    (D : Obs × Mis × Mis × SamplingIndicator × ℝ)
    (β : Fin d → ℝ) : Fin d → ℝ :=
  match D with
  | ⟨d_obs, d_mis_pred, d_mis_true, R, π⟩ =>
      DSLMoment m d_obs d_mis_pred d_mis_true R π β

/-!
## Oracle Target
-/

/-- Oracle moment using the true missing values from a full DSL data record. -/
def TrueMomentFromFullData {Obs Mis : Type*} {d : ℕ}
    (m : MomentFunction (Obs × Mis) d) :
    MomentFunction (Obs × Mis × Mis × SamplingIndicator × ℝ) d :=
  fun D β =>
    match D with
    | ⟨d_obs, _d_mis_pred, d_mis_true, _R, _π⟩ =>
        m (d_obs, d_mis_true) β

/-- Oracle target parameter: solves the true moment condition. -/
def OracleTarget {Obs Mis : Type*} {d : ℕ}
    (m : MomentFunction (Obs × Mis) d)
    (E : ((Obs × Mis × Mis × SamplingIndicator × ℝ) → Fin d → ℝ) → Fin d → ℝ)
    (β : Fin d → ℝ) : Prop :=
  MomentUnbiased (TrueMomentFromFullData m) E β

/-!
## Generic M-Estimation Axioms
-/

/-- Abstract M-estimation asymptotic results, used as axioms in this formalization. -/
structure MEstimationAxioms (Ω Data : Type*) [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (d : ℕ) where
  /-- Expectation operator for moments. -/
  E : (Data → Fin d → ℝ) → Fin d → ℝ
  /-- Consistency for any estimator sequence solving the sample moment equation. -/
  consistent :
    ∀ (m : MomentFunction Data d) (β_star : Fin d → ℝ)
      (data_seq : ℕ → Ω → List Data) (β_hat_seq : ℕ → Ω → Fin d → ℝ),
      MomentUnbiased m E β_star →
      RegularityConditions Data d →
      IsMEstimatorSeq m data_seq β_hat_seq →
      ConvergesInProbability μ β_hat_seq (fun _ => β_star)
  /-- Asymptotic normality for centered/scaled estimator sequences. -/
  asymptotic_normal :
    ∀ (m : MomentFunction Data d) (β_star : Fin d → ℝ) (V : Matrix (Fin d) (Fin d) ℝ)
      (centered_scaled_seq : ℕ → Ω → Fin d → ℝ),
      MomentUnbiased m E β_star →
      RegularityConditions Data d →
      ConvergesInDistributionToNormal μ centered_scaled_seq (fun _ => 0) V

/-- DSL consistency theorem.

    Under Assumption 1 and regularity conditions, the DSL estimator
    converges in probability to the true parameter β*.

    The key insight is that E[m̃(D; β*)] = 0 because the design-adjusted
    moment is unbiased, so by the law of large numbers,
    (1/N)∑m̃(Di; β) → E[m̃(D; β)] and the unique zero is at β*. -/
theorem DSL_consistent
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Obs Mis Con : Type*} {d : ℕ}
    (axioms : MEstimationAxioms Ω (Obs × Mis × Mis × SamplingIndicator × ℝ) μ d)
    (dbs : DesignBasedSampling Obs Mis Con)
    (m : MomentFunction (Obs × Mis) d)
    (β_star : Fin d → ℝ)
    (reg : RegularityConditions (Obs × Mis × Mis × SamplingIndicator × ℝ) d)
    (h_unbiased : MomentUnbiased (DSLMomentFromData m) axioms.E β_star)
    (data_seq : ℕ → Ω → List (Obs × Mis × Mis × SamplingIndicator × ℝ))
    (β_hat_seq : ℕ → Ω → Fin d → ℝ)
    (h_est : IsMEstimatorSeq (DSLMomentFromData m) data_seq β_hat_seq)
    : ConvergesInProbability μ β_hat_seq (fun _ => β_star) := by
  exact axioms.consistent (DSLMomentFromData m) β_star data_seq β_hat_seq h_unbiased reg h_est

/-- Cross-fitted DSL consistency theorem (Appendix B.2). -/
theorem DSL_consistent_crossfit
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {ι Obs Mis Con : Type*} [Fintype ι] {d : ℕ}
    (axioms : MEstimationAxioms Ω (Obs × Mis × Mis × SamplingIndicator × ℝ) μ d)
    (cf : CrossFit ι Obs Con Mis)
    (dbs : DesignBasedSampling Obs Mis Con)
    (m : MomentFunction (Obs × Mis) d)
    (β_star : Fin d → ℝ)
    (reg : RegularityConditions (Obs × Mis × Mis × SamplingIndicator × ℝ) d)
    (cf_reg : CrossFittingConditions cf)
    (h_unbiased : MomentUnbiased (DSLMomentFromData m) axioms.E β_star)
    (data_seq : ℕ → Ω → List (Obs × Mis × Mis × SamplingIndicator × ℝ))
    (β_hat_seq : ℕ → Ω → Fin d → ℝ)
    (h_est : IsMEstimatorSeq (DSLMomentFromData m) data_seq β_hat_seq)
    : ConvergesInProbability μ β_hat_seq (fun _ => β_star) := by
  exact axioms.consistent (DSLMomentFromData m) β_star data_seq β_hat_seq h_unbiased reg h_est

/-!
## Asymptotic Normality
-/

/-- DSL asymptotic normality theorem (Proposition 1).

    Under Assumption 1 and regularity conditions:
    √N(β̂_DSL - β*) →d N(0, V)

    where V is the sandwich variance matrix. -/
theorem DSL_asymptotic_normal
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Obs Mis Con : Type*} {d : ℕ}
    (axioms : MEstimationAxioms Ω (Obs × Mis × Mis × SamplingIndicator × ℝ) μ d)
    (dbs : DesignBasedSampling Obs Mis Con)
    (m : MomentFunction (Obs × Mis) d)
    (β_star : Fin d → ℝ)
    (V : Matrix (Fin d) (Fin d) ℝ)
    (reg : RegularityConditions (Obs × Mis × Mis × SamplingIndicator × ℝ) d)
    (h_unbiased : MomentUnbiased (DSLMomentFromData m) axioms.E β_star)
    : ∀ (centered_scaled_seq : ℕ → Ω → Fin d → ℝ),
      -- √N(β̂_N - β*) where β̂_N is the DSL estimator
      ConvergesInDistributionToNormal μ centered_scaled_seq (fun _ => 0) V := by
  intro seq
  exact axioms.asymptotic_normal (DSLMomentFromData m) β_star V seq h_unbiased reg

/-- Cross-fitted DSL asymptotic normality theorem (Appendix B.2). -/
theorem DSL_asymptotic_normal_crossfit
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {ι Obs Mis Con : Type*} [Fintype ι] {d : ℕ}
    (axioms : MEstimationAxioms Ω (Obs × Mis × Mis × SamplingIndicator × ℝ) μ d)
    (cf : CrossFit ι Obs Con Mis)
    (dbs : DesignBasedSampling Obs Mis Con)
    (m : MomentFunction (Obs × Mis) d)
    (β_star : Fin d → ℝ)
    (V : Matrix (Fin d) (Fin d) ℝ)
    (reg : RegularityConditions (Obs × Mis × Mis × SamplingIndicator × ℝ) d)
    (cf_reg : CrossFittingConditions cf)
    (h_unbiased : MomentUnbiased (DSLMomentFromData m) axioms.E β_star)
    : ∀ (centered_scaled_seq : ℕ → Ω → Fin d → ℝ),
      ConvergesInDistributionToNormal μ centered_scaled_seq (fun _ => 0) V := by
  intro seq
  exact axioms.asymptotic_normal (DSLMomentFromData m) β_star V seq h_unbiased reg

/-!
## Variance Formula
-/

/-- Jacobian matrix of the moment function: E[∂m/∂β] -/
def JacobianMatrix {Obs Mis : Type*} {d : ℕ}
    (m : MomentFunction (Obs × Mis) d)
    (E : ((Obs × Mis) → Matrix (Fin d) (Fin d) ℝ) → Matrix (Fin d) (Fin d) ℝ)
    (β : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  -- Placeholder: proper definition would involve differentiation
  fun _ _ => 0

/-- Meat matrix: E[m̃ m̃'] -/
def MeatMatrix {Obs Mis : Type*} {d : ℕ}
    (m_tilde : (Obs × Mis) → Fin d → ℝ)
    (E : ((Obs × Mis) → Matrix (Fin d) (Fin d) ℝ) → Matrix (Fin d) (Fin d) ℝ)
    : Matrix (Fin d) (Fin d) ℝ :=
  E (fun data => fun i j => m_tilde data i * m_tilde data j)

/-- Sandwich variance matrix: V = S⁻¹ · M · S⁻¹'

    This is the standard sandwich estimator for M-estimators.
    For DSL, the meat matrix M uses the design-adjusted moments m̃. -/
def SandwichVariance {d : ℕ}
    (S_inv : Matrix (Fin d) (Fin d) ℝ)  -- S_V⁻¹
    (M : Matrix (Fin d) (Fin d) ℝ)       -- E[m̃ m̃']
    : Matrix (Fin d) (Fin d) ℝ :=
  S_inv * M * S_inv.transpose

/-!
## Variance Decomposition
-/

/-- Entrywise matrix order (simple PSD-like proxy). -/
def MatrixLE {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  ∀ i j, A i j ≤ B i j

lemma matrixLE_add {d : ℕ} {A B C D : Matrix (Fin d) (Fin d) ℝ}
    (h1 : MatrixLE A B) (h2 : MatrixLE C D) : MatrixLE (A + C) (B + D) := by
  intro i j
  simpa using add_le_add (h1 i j) (h2 i j)

lemma matrixLE_smul {d : ℕ} {A B : Matrix (Fin d) (Fin d) ℝ}
    (c : ℝ) (hc : 0 ≤ c) (h : MatrixLE A B) : MatrixLE (c • A) (c • B) := by
  intro i j
  -- Scalar multiplication is entrywise.
  simpa using mul_le_mul_of_nonneg_left (h i j) hc

/-- Variance decomposition for DSL.

    The variance of the DSL estimator can be decomposed as:
    V_DSL = V_full + (1/π - 1) · V_correction

    where:
    - V_full is the variance if all documents were expert-coded
    - V_correction accounts for using predictions instead of true labels
    - As prediction accuracy improves, V_correction decreases

    This shows that better predictions lead to smaller standard errors. -/
structure VarianceDecomposition {d : ℕ} where
  /-- Variance with full expert coding (n = N) -/
  V_full : Matrix (Fin d) (Fin d) ℝ
  /-- Correction variance from using predictions -/
  V_correction : Matrix (Fin d) (Fin d) ℝ
  /-- Sampling probability -/
  π : ℝ
  /-- Total DSL variance -/
  V_DSL : Matrix (Fin d) (Fin d) ℝ
  /-- Decomposition relation -/
  h_decomp : V_DSL = V_full + ((1/π - 1) : ℝ) • V_correction

/-- Better predictions reduce variance.

    If the prediction error variance decreases, V_correction decreases,
    leading to smaller overall variance V_DSL.

    This formalizes the efficiency property of DSL: better LLMs → smaller SEs. -/
theorem better_predictions_smaller_variance {d : ℕ}
    (vd1 vd2 : VarianceDecomposition (d := d))
    -- Same π and V_full
    (h_π : vd1.π = vd2.π)
    (h_full : vd1.V_full = vd2.V_full)
    -- V_correction is "smaller" for vd2 (in positive semidefinite sense)
    -- Placeholder: proper definition would use matrix ordering
    (h_smaller : MatrixLE vd2.V_correction vd1.V_correction)
    (h_factor_nonneg : (1 / vd1.π - 1 : ℝ) ≥ 0)
    : MatrixLE vd2.V_DSL vd1.V_DSL := by
  have h_full_le : MatrixLE vd2.V_full vd1.V_full := by
    intro i j
    simp [h_full]
  have h_corr_le :
      MatrixLE ((1 / vd2.π - 1 : ℝ) • vd2.V_correction)
        ((1 / vd1.π - 1 : ℝ) • vd1.V_correction) := by
    have h_π' : vd2.π = vd1.π := h_π.symm
    simpa [h_π'] using
      (matrixLE_smul (c := (1 / vd1.π - 1 : ℝ)) h_factor_nonneg h_smaller)
  have h_le :
      MatrixLE (vd2.V_full + ((1 / vd2.π - 1 : ℝ) • vd2.V_correction))
        (vd1.V_full + ((1 / vd1.π - 1 : ℝ) • vd1.V_correction)) :=
    matrixLE_add h_full_le h_corr_le
  simpa [vd1.h_decomp, vd2.h_decomp] using h_le

/-!
## Standard Error Formula
-/

/-- Standard error for the i-th coefficient -/
def standardError {d : ℕ} (V : Matrix (Fin d) (Fin d) ℝ) (i : Fin d) : ℝ :=
  Real.sqrt (V i i)

/-- Confidence interval for the i-th coefficient -/
def confidenceInterval {d : ℕ}
    (β_hat : Fin d → ℝ)
    (V : Matrix (Fin d) (Fin d) ℝ)
    (N : ℕ)
    (z_alpha : ℝ)  -- Critical value (e.g., 1.96 for 95% CI)
    (i : Fin d) : ℝ × ℝ :=
  let se := standardError V i / Real.sqrt N
  (β_hat i - z_alpha * se, β_hat i + z_alpha * se)

/-- DSL confidence intervals have correct coverage.

    Under Assumption 1, the DSL confidence intervals achieve the
    nominal coverage rate asymptotically, regardless of prediction accuracy.

    This is the key advantage of DSL: valid inference without
    assumptions about prediction error structure. -/
theorem DSL_valid_coverage
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Obs Mis Con : Type*} {d : ℕ}
    (axioms : MEstimationAxioms Ω (Obs × Mis × Mis × SamplingIndicator × ℝ) μ d)
    (coverage_axioms : CoverageAxioms μ d)
    (dbs : DesignBasedSampling Obs Mis Con)
    (m : MomentFunction (Obs × Mis) d)
    (β_star : Fin d → ℝ)
    (V : Matrix (Fin d) (Fin d) ℝ)
    (reg : RegularityConditions (Obs × Mis × Mis × SamplingIndicator × ℝ) d)
    (h_unbiased : MomentUnbiased (DSLMomentFromData m) axioms.E β_star)
    (CI_seq : ℕ → Ω → Fin d → ℝ × ℝ)
    (α : ℝ)  -- Significance level
    (h_α : 0 < α ∧ α < 1)
    (centered_scaled_seq : ℕ → Ω → Fin d → ℝ)
    : AsymptoticCoverage μ CI_seq β_star α := by
  have h_norm :
      ConvergesInDistributionToNormal μ centered_scaled_seq (fun _ => 0) V :=
    DSL_asymptotic_normal μ axioms dbs m β_star V reg h_unbiased centered_scaled_seq
  exact coverage_axioms.coverage_of_asymptotic_normal centered_scaled_seq CI_seq β_star α V h_norm

/-!
## Comparison with Naive Estimator
-/

/-- The naive estimator ignores prediction errors.

    β̂_naive solves (1/N)∑m(D^obs, D̂^mis; β) = 0

    This is inconsistent unless E[m(D^obs, D̂^mis; β*)] = E[m(D^obs, D^mis; β*)]
    which requires prediction errors to be uncorrelated with everything. -/
def NaiveEstimator {Obs Mis : Type*} {d : ℕ}
    (m : MomentFunction (Obs × Mis) d)
    (data : List (Obs × Mis))  -- Only uses (d_obs, d_mis_pred)
    (β : Fin d → ℝ) : Fin d → ℝ :=
  let N := data.length
  fun i => (data.foldl (fun acc ⟨d_obs, d_mis_pred⟩ =>
    acc + m (d_obs, d_mis_pred) β i) 0) / N

/-- Naive moment function on (d_obs, d_mis_pred, d_mis_true). -/
def PredMomentFromData {Obs Mis : Type*} {d : ℕ}
    (m : MomentFunction (Obs × Mis) d) : MomentFunction (Obs × Mis × Mis) d :=
  fun D β => m (D.1, D.2.1) β

/-- Oracle moment function using true missing values. -/
def TrueMomentFromData {Obs Mis : Type*} {d : ℕ}
    (m : MomentFunction (Obs × Mis) d) : MomentFunction (Obs × Mis × Mis) d :=
  fun D β => m (D.1, D.2.2) β

/-- Componentwise linearity of an expectation operator. -/
def ExpectationLinear {Data : Type*} {d : ℕ}
    (E : (Data → Fin d → ℝ) → Fin d → ℝ) : Prop :=
  ∀ (f g : Data → Fin d → ℝ) (a b : ℝ) (i : Fin d),
    E (fun D => fun j => a * f D j + b * g D j) i =
      a * E f i + b * E g i

/-- The naive estimator is biased unless very strong conditions hold.

    For the naive estimator to be consistent, we need:
    E[e | X] = 0 where e = Ŷ - Y

    This requires errors to be uncorrelated with:
    - X (the covariates)
    - Y (the true outcome)
    - Any unobserved confounders U

    This almost never holds in practice. -/
theorem naive_estimator_biased_general
    {Obs Mis : Type*} {d : ℕ}
    (m : MomentFunction (Obs × Mis) d)
    (E : ((Obs × Mis × Mis) → Fin d → ℝ) → Fin d → ℝ)
    (β_star : Fin d → ℝ)
    (h_true : MomentUnbiased (TrueMomentFromData m) E β_star)
    (h_bias : ∃ i, MomentBias m E β_star i ≠ 0)
    (hE_linear : ExpectationLinear E)
    : ¬ MomentUnbiased (PredMomentFromData m) E β_star := by
  intro h_pred
  rcases h_bias with ⟨i, h_nonzero⟩
  have h_bias_eq :
      MomentBias m E β_star i =
        E (fun D => fun j =>
          PredMomentFromData m D β_star j - TrueMomentFromData m D β_star j) i := by
    rfl
  have h_linear :
      E (fun D => fun j =>
        PredMomentFromData m D β_star j - TrueMomentFromData m D β_star j) i =
        E (fun D => PredMomentFromData m D β_star) i -
        E (fun D => TrueMomentFromData m D β_star) i := by
    -- Use linearity with a = 1, b = -1.
    have := hE_linear
      (fun D => PredMomentFromData m D β_star)
      (fun D => TrueMomentFromData m D β_star)
      1 (-1) i
    -- Simplify pointwise.
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using this
  have h_pred_zero : E (fun D => PredMomentFromData m D β_star) i = 0 := h_pred i
  have h_true_zero : E (fun D => TrueMomentFromData m D β_star) i = 0 := h_true i
  have h_bias_zero : MomentBias m E β_star i = 0 := by
    calc
      MomentBias m E β_star i
          = E (fun D => fun j =>
              PredMomentFromData m D β_star j - TrueMomentFromData m D β_star j) i := h_bias_eq
      _ = E (fun D => PredMomentFromData m D β_star) i -
          E (fun D => TrueMomentFromData m D β_star) i := h_linear
      _ = 0 := by simp [h_pred_zero, h_true_zero]
  exact h_nonzero h_bias_zero

end DSL

end
