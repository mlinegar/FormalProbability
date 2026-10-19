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
-- DSL Module: Design-based Supervised Learning (Egami, Hinck, Stewart, Wei)
-- ============================================================================
import FormalProbability.DSL
import FormalProbability.DSL.IPWTheory
import FormalProbability.DSL.ClusteredVariance
import FormalProbability.DSL.JudgeCalibration

/-!
# FormalProbability - Modular Formalization of Probability and Econometrics

This file is the root of the default build target. It imports four main sections:
- **CLT**: Central Limit Theorem and probability theory
- **Econometrics**: Potential outcomes + IPW foundations
- **ML**: Supervised learning primitives
- **DSL**: Design-based Supervised Learning (Egami, Hinck, Stewart, Wei)

Not imported here (so not checked by `lake build`): the Econometrics OLS/IV/Panel/Diagnostics
submodules and `DSL.MEstimationCore`.

## Proof Status

No `sorry` and no `axiom` declarations. The modules imported here contain 221
theorem/lemma declarations (346 in the whole repository). Some statements are placeholders
or rest on assumption bundles; see README.md and docs/OVERVIEW.md for per-module status.

## Quick Navigation

| Module | Entry Point | What It Proves |
|--------|-------------|----------------|
| **CLT** | `FormalProbability.CLT` | Central Limit Theorem |
| **Econometrics** | `FormalProbability.Econometrics` | Potential outcomes + IPW foundations |
| **ML** | `FormalProbability.ML` | Supervised learning basics |
| **DSL** | `FormalProbability.DSL` | Design-based supervised learning, IPW, clustered SEs |
-/
