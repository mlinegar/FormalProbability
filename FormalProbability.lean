import FormalProbability.Shared.BoundedMetricSpace
import FormalProbability.CLT
import FormalProbability.Econometrics
import FormalProbability.ML
import FormalProbability.DSL

/-!
# FormalProbability

Root of the default build target: `lake build` checks this module and everything it imports.

- `FormalProbability.CLT`: probability foundations and the classical i.i.d. central limit
  theorem.
- `FormalProbability.Econometrics`: potential outcomes, propensity scores, IPW
  identification of the average treatment effect, and finite-sample OLS.
- `FormalProbability.DSL`: design-based supervised learning (Egami, Hinck, Stewart & Wei),
  together with inverse-probability weighting, clustered variance, and judge calibration.
- `FormalProbability.ML`: basic supervised-learning vocabulary (risk, ERM, decision trees).
- `FormalProbability.Shared.BoundedMetricSpace`: bounded (pseudo)metric space typeclasses.

Modules under `FormalProbability/WIP/` are work in progress and are deliberately not
imported here.
-/
