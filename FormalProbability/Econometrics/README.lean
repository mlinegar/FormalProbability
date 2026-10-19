/-!
# Econometrics: potential outcomes, IPW identification, and OLS

## Core model

- Treatment indicator D in {0, 1}
- Potential outcomes Y0, Y1 : Omega -> R
- Observed outcome by consistency: Y = D * Y1 + (1 - D) * Y0
- Target: the average treatment effect ATE = E[Y1 - Y0]

## Propensity score and identification

The propensity score e(X) = E[D | X] is constructed both as a random variable and, by
Doob-Dynkin factorization, as a measurable function of the covariates. Under consistency,
unconfoundedness, positivity, and integrability, `ipw_identifies_ATE` proves

  ATE = E[ D * Y / e(X) - (1 - D) * Y / (1 - e(X)) ].

## Finite-sample OLS

`OLS/GaussMarkov` proves unbiasedness, the variance formula, and the Gauss-Markov theorem
for a fixed design; `OLS/RSquared` proves the sum-of-squares decomposition and properties
of R-squared.

## File structure

```
Econometrics/
├── Core.lean               # treatment, potential outcomes, observed outcome, ATE
├── Assumptions.lean        # consistency, unconfoundedness, positivity
├── PropensityScore.lean    # e(X) = E[D | X] and Doob-Dynkin factorization
├── IPWIdentification.lean  # identification of the ATE by IPW
├── OLS/
│   ├── GaussMarkov.lean    # unbiasedness, variance, Gauss-Markov
│   ├── RSquared.lean       # TSS = ESS + RSS, R-squared
│   └── README.lean
└── README.lean             # this file
```

Drafts for OLS inference and asymptotics, instrumental variables, panel data, and
diagnostics are in `FormalProbability/WIP/Econometrics` and are not part of the default
build.
-/
