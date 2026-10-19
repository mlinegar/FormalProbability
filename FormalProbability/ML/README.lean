/-!
# ML: supervised-learning vocabulary

## Overview

Lightweight, textbook-style definitions meant to be shared with the other areas:
- supervised-learning primitives (hypotheses, losses, population risk)
- empirical risk minimization (ERM) and the generalization gap
- decision trees as a hypothesis class (routing, impurity, pruning, axis-aligned splits)

## File structure

```
ML/
├── Core.lean          # hypotheses, loss, population risk
├── ERM.lean           # empirical risk and ERM
├── DecisionTree.lean  # decision tree hypothesis class
└── README.lean        # this file
```

## Design principles

- Keep definitions minimal and composable.
- Prefer explicit assumptions to global axioms.
- Align with Mathlib's probability infrastructure where possible.
-/
