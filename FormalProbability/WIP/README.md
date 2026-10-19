# WIP: work in progress

Modules here are drafts. They are not imported by `FormalProbability.lean`, so the default
`lake build` (and CI) does not check them, and many of their statements are still
placeholders that record the intended result rather than prove it. They move into the main
tree once their statements are filled in and proved.

- `Econometrics/OLS`: inference (t and F statistics) and asymptotic OLS.
- `Econometrics/IV`: two-stage least squares, identification, weak instruments.
- `Econometrics/Panel`: fixed effects, random effects, the Hausman test.
- `Econometrics/Diagnostics`: omitted-variable bias, heteroskedasticity, functional form.

A draft can be checked by name, for example
`lake build FormalProbability.WIP.Econometrics.IV.TwoSLS`.
