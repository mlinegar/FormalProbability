# ML: supervised-learning vocabulary

This directory holds minimal definitions and a few structural lemmas. `ML.lean` imports
every module here, and all of them are built.

- `Core`: hypotheses, losses, population risk.
- `ERM`: empirical risk, ERM, generalization gap.
- `DecisionTree`: binary decision trees, routing, Gini and entropy impurity, cost-complexity
  pruning, axis-aligned splits. It also proves `DecisionTree.measurable_eval`.

No other module uses these definitions yet. For details, see the
[module map](../../README.md#machine-learning-ml-all-built).
