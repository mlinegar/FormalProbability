# FormalProbability

[![Lean Action CI](https://github.com/mlinegar/FormalProbability/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/mlinegar/FormalProbability/actions/workflows/lean_action_ci.yml)

Lean 4 / Mathlib formalizations of probability, causal inference, and the statistics of
using machine-learning (including LLM) annotations in downstream estimation. Estimators
that correct for prediction error are easy to describe informally and easy to get subtly
wrong; writing them in Lean forces every assumption into the statement and lets the proof
assistant check what actually follows from them. The project starts from the probability
needed for asymptotic arguments (through the central limit theorem) and builds up to
design-based supervised learning and the related estimators used when an LLM stands in for
a human coder.

Author: [Mitchell Linegar](https://mlinegar.github.io)

## Areas

- **Probability and the central limit theorem** (`FormalProbability/CLT`). Laws of random
  variables, standard distributions, the weak law of large numbers, Helly selection, and a
  form of Lévy's continuity theorem, leading to a proof of the classical i.i.d. central
  limit theorem via characteristic functions
  (`central_limit_theorem_iid_finite_variance`, built on
  `tendsto_probabilityMeasure_of_tendsto_charFun`).
- **Causal inference and econometrics** (`FormalProbability/Econometrics`). The
  potential-outcomes model, the propensity score as a measurable function of covariates
  (`propensityScore_exists`), and a measure-theoretic proof that inverse probability
  weighting identifies the average treatment effect (`ipw_identifies_ATE`). Finite-sample
  OLS covers unbiasedness, the variance formula, and the Gauss-Markov theorem
  (`ols_unbiased`, `gauss_markov`), plus the sum-of-squares decomposition and R-squared
  (`tss_decomposition`, `rsquared_is_squared_correlation`).
- **Design-based supervised learning** (`FormalProbability/DSL`). A formalization of DSL
  (Egami, Hinck, Stewart & Wei): automated labels for every document, expert labels for a
  subset sampled with known probability, and a design-adjusted outcome whose moments are
  unbiased whatever the prediction quality (`DSL_unbiased`, `DSLMoment_unbiased`). It also
  shows that naive plug-in moments are biased whenever prediction error shifts them
  (`naive_estimator_biased_general`), and covers Horvitz-Thompson and Hájek estimators,
  document-clustered variance, and calibrating an LLM judge against an oracle. The
  asymptotic theory (consistency, asymptotic normality, coverage) is currently stated
  relative to explicit assumption structures rather than derived from the CLT area;
  connecting the two is ongoing work.
- **Machine learning** (`FormalProbability/ML`). Shared vocabulary: hypotheses, losses and
  risk, empirical risk minimization, and decision trees with impurity measures and
  cost-complexity pruning.
- **Work in progress** (`FormalProbability/WIP`). Drafts that are not part of the default
  build, currently the remaining econometrics material (OLS inference and asymptotics,
  instrumental variables, panel data, regression diagnostics). Many statements there are
  still placeholders.

[docs/OVERVIEW.md](docs/OVERVIEW.md) describes how the modules depend on each other.

## Connection to research

This repository supports my research on auditing LLM-generated summaries and labels. In
that setting a model produces outputs at scale, and a much smaller set of trusted labels
(from experts, or from a stronger model acting as an oracle) is collected under a known
sampling design. Getting valid estimates and confidence intervals out of that combination
rests on the tools formalized here: design-based correction of predicted labels,
inverse-probability weighting with logged sampling propensities, variance estimates that
respect clustering (many judgments per document), and calibration of an LLM judge against
the oracle. More on the research side is at [mlinegar.github.io](https://mlinegar.github.io).

## Build

Requirements: [elan](https://github.com/leanprover/elan), the Lean toolchain manager. It
reads `lean-toolchain` and installs `leanprover/lean4:v4.27.0-rc1`; Mathlib is pinned to
`v4.27.0-rc1` in `lakefile.toml` and `lake-manifest.json`.

```bash
# install elan (once)
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

git clone https://github.com/mlinegar/FormalProbability
cd FormalProbability
lake exe cache get   # download prebuilt Mathlib files
lake build           # build the FormalProbability library
```

`lake build` checks the root module `FormalProbability.lean` and everything it imports,
which is every module outside `WIP/`. CI runs the same build on every push and pull
request. A work-in-progress module can be checked by name, for example:

```bash
lake build FormalProbability.WIP.Econometrics.IV.TwoSLS
```

## Repository layout

```
FormalProbability.lean    root module (default build target)
FormalProbability/
  CLT/            probability foundations and the central limit theorem
  Econometrics/   potential outcomes, IPW identification, finite-sample OLS
  DSL/            design-based supervised learning; IPW, clustered variance, judge calibration
  ML/             risk, ERM, decision trees
  Shared/         bounded metric space typeclasses
  WIP/            work in progress, not imported by the root module
docs/OVERVIEW.md  how the areas and modules fit together
```

## Prior work and attribution

- Rémy Degenne's Lean CLT development (https://github.com/RemyDegenne/CLT) predates this
  work, and full credit goes to it.
- The first formalized CLT (Isabelle/HOL) is Jeremy Avigad, Johannes Hölzl, and Luke
  Serafin, "A formally verified proof of the Central Limit Theorem"
  ([arXiv:1405.7012](https://arxiv.org/abs/1405.7012)). That paper was provided to the AI
  assistants used to draft parts of this development.
- DSL: Naoki Egami, Musashi Hinck, Brandon M. Stewart, and Hanying Wei, "Using Imperfect
  Surrogates for Downstream Inference: Design-based Supervised Learning for Social Science
  Applications of Large Language Models" (NeurIPS 2023).

## License

MIT (see `LICENSE`).
