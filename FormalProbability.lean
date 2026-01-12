-- ============================================================================
-- Shared Infrastructure
-- ============================================================================
import FormalProbability.Shared.Config
import FormalProbability.Shared.BoundedMetricSpace

-- ============================================================================
-- CLT Module: Central Limit Theorem
-- ============================================================================
import FormalProbability.CLT

-- ============================================================================
-- Econometrics Module: Foundations for IPW
-- ============================================================================
import FormalProbability.Econometrics

-- ============================================================================
-- ML Module: Supervised Learning Foundations
-- ============================================================================
import FormalProbability.ML

-- ============================================================================
-- DSL Module: Debiased/Double Machine Learning
-- ============================================================================
import FormalProbability.DSL
import FormalProbability.DSL.IPWTheory
import FormalProbability.DSL.ClusteredVariance
import FormalProbability.DSL.JudgeCalibration

/-!
# FormalProbability - Modular Formalization of Probability and Econometrics

This file re-exports all modules in dependency order, organized into four main sections:
- **CLT**: Central Limit Theorem and probability theory
- **Econometrics**: Potential outcomes + IPW foundations
- **ML**: Supervised learning primitives
- **DSL**: Debiased/Double Machine Learning

## Proof Status

✅ **656+ theorems/lemmas** - All proved (no sorry)

## Quick Navigation

| Module | Entry Point | What It Proves |
|--------|-------------|----------------|
| **CLT** | `FormalProbability.CLT` | Central Limit Theorem |
| **Econometrics** | `FormalProbability.Econometrics` | Potential outcomes + IPW foundations |
| **ML** | `FormalProbability.ML` | Supervised learning basics |
| **DSL** | `FormalProbability.DSL` | Debiased ML, IPW, clustered SEs |
-/
