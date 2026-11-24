# Blueprint: the Legendre family, its Picard–Fuchs equation and its monodromy

Notation (all in `Legendre/Defs.lean`, namespace `Legendre`):

- `F z = ₂F₁(1/2,1/2;1;z)` (Mathlib `ordinaryHypergeometric`), `F z = ∑ aₙ zⁿ` for `|z|<1`
- `aₙ = coeff n = (C(2n,n)/4ⁿ)²`, so `a₀ = 1` and `(n+1)² a_{n+1} = (n+1/2)² aₙ`, and `0 ≤ aₙ ≤ 1`
- `hₙ = harm n = ∑_{k<n} 2/((k+1)(2k+1))`, so `h₀ = 0`, `h_{n+1} - hₙ = 2/((n+1)(2n+1))`,
  and `0 ≤ hₙ ≤ 4` (indeed `hₙ ≤ 2∑ 1/(k(2k-1)) ≤ 2(1 + ∑_{k≥2} 1/(k(k-1)))= 4`)
- `G z = ∑ aₙ hₙ zⁿ`, `L z = F z · log z + G z`
- `D = ball 0 1 ∩ slitPlane` (open, star-convex about `1/2`, excludes `0` and `1`)
- `legendreOp y z = z(1-z) y'' + (1-2z) y' - y/4`

Everything below was checked numerically to 30 digits (mpmath).

## 1. Power series toolkit (`Legendre/PowerSeries.lean`)

For `c : ℕ → ℂ` with `‖c n‖ ≤ C` (bounded), `S c z := ∑' n, c n * z^n` on `ball 0 1`:

- summable, `HasDerivAt (S c) (S (fun n => (n+1) * c (n+1)) z) z`; hence
  `deriv (S c) = S (shift c)` on the ball and `DifferentiableOn ℂ (S c) (ball 0 1)`.
  The derived sequence `(n+1) c(n+1)` is no longer bounded but is polynomially bounded;
  it is cleanest to state the toolkit for coefficient sequences with
  `‖c n‖ ≤ C * (n+1)^k`. (Possible Mathlib routes: `FormalMultilinearSeries.ofScalars`
  plus `HasFPowerSeriesOnBall.hasDerivAt`/`derivSeries`, or `hasDerivAt_tsum_of_isPreconnected`
  / `hasDerivAt_tsum` from `Mathlib/Analysis/Calculus/SmoothSeries.lean`.)
- algebra: `z * S c z = S (fun n => if n = 0 then 0 else c (n-1)) z`, linearity.
- identity: if all coefficients of the combination vanish, the function vanishes.

## 2. ODEs (`Legendre/Solutions.lean`)

Coefficient of `zⁿ` in `legendreOp (S c)`:
`(n+1)² c_{n+1} - (n+1/2)² cₙ`.
(From `z y'' = ∑ n(n-1)cₙ z^{n-1}`, `-z²y'' = -∑ n(n-1) cₙ zⁿ`, `y' = ∑ n cₙ z^{n-1}`,
`-2z y' = -∑ 2n cₙ zⁿ`, `-y/4`.)

- **F solves**: `(n+1)² a_{n+1} = (n+1/2)² aₙ` (from `C(2n+2,n+1) = C(2n,n)·2(2n+1)/(n+1)`).
  `F_eq_tsum`: Mathlib's coefficient `n!⁻¹ (1/2)ₙ (1/2)ₙ / (1)ₙ` equals `aₙ`
  (`(1/2)ₙ/n! = C(2n,n)/4ⁿ`, `(1)ₙ = n!`). Mathlib: `ordinaryHypergeometric_eq_tsum`,
  `ordinaryHypergeometricSeries_radius_eq_one`, `ascPochhammer`.
- **G inhomogeneous ODE**: `z(1-z)G'' + (1-2z)G' - G/4 = F - 2(1-z)F'` on `ball 0 1`.
  Coefficientwise: `(n+1)² a_{n+1}h_{n+1} - (n+1/2)² aₙhₙ = (2n+1)aₙ - 2(n+1)a_{n+1}`.
  Using the `a` recursion, LHS `= (n+1/2)² aₙ (h_{n+1}-hₙ)` and RHS `= (2n+1)aₙ/(2(n+1))`;
  both equal `(2n+1) aₙ/(2(n+1))` because `h_{n+1}-hₙ = 2/((n+1)(2n+1))`.
- **L solves on D**: on `D`, `log` is holomorphic with `log' = 1/z`
  (`Complex.hasDerivAt_log` with `slitPlane`), so
  `L' = F' log + F/z + G'`, `L'' = F'' log + 2F'/z - F/z² + G''`, and
  `legendreOp L = log·legendreOp F + [2(1-z)F' - F] + [legendreOp-part of G]`
  `= 0 + 2(1-z)F' - F + (F - 2(1-z)F') = 0`.
  Note `deriv (deriv L)` needs `deriv L` to agree with the formula on a neighbourhood
  (use `D` open and `Filter.EventuallyEq.deriv_eq`).
- **Wronskian**: let `h(z) = (1-z) F² + z(1-z)(F G' - F' G)`, holomorphic on the ball.
  On `D`, `z(1-z)·(F L' - F' L) = z(1-z)(F²/z + F G' - F' G) = h(z)`.
  `h' = 0` on the ball (differentiate, use the ODEs of `F` and `G`; the ODE terms are
  `z(1-z)F'' = -(1-2z)F' + F/4` and `z(1-z)G'' = -(1-2z)G' + G/4 + F - 2(1-z)F'`;
  a direct expansion gives `h' = 0`), and `h(0) = F(0)² = 1`, so `h ≡ 1` on the ball
  (`IsOpen.is_const_of_deriv_eq_zero` / convexity). Hence `F L' - F' L = 1/(z(1-z))` on `D`.
  (Abel: `(z(1-z) W)' = 0` for any two solutions.)

## 3. Uniqueness (`Legendre/Uniqueness.lean`)

Let `U` be open and preconnected, `y` holomorphic on `U` with `legendreOp y = 0` on `U`.

- Induction on `k`: for all `z ∈ U`,
  `z(1-z) y^{(k+2)} + (k+1)(1-2z) y^{(k+1)} - (k+1/2)² y^{(k)} = 0`,
  where `y^{(k)} = iteratedDeriv k y` (equivalently `deriv^[k] y`). Step: the left side is
  identically zero on the open set `U`, so its derivative is zero on `U`; the product rule
  gives `z(1-z) y^{(k+3)} + (k+2)(1-2z) y^{(k+2)} - (k+3/2)² y^{(k+1)}`
  (check: `2(k+1) + (k+1/2)² = (k+3/2)²`).
  Holomorphic on open ⇒ every `deriv^[k] y` is holomorphic on `U` (`DifferentiableOn.deriv`
  with `IsOpen`).
- If `z₀ ∈ U`, `z₀ ≠ 0, 1` and `y z₀ = y' z₀ = 0`, strong induction gives
  `y^{(k)}(z₀) = 0` for all `k` (divide by `z₀(1-z₀) ≠ 0`).
- Taylor: on a ball `B ⊆ U` around `z₀`, `Complex.taylorSeries_eq_on_ball`
  (`Mathlib/Analysis/Complex/TaylorSeries.lean`) gives `y = 0` on `B`.
- Identity theorem: `AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero`
  (`DifferentiableOn.analyticOnNhd` on open sets) gives `y = 0` on `U`.
- `D` preconnected: it is star-convex about `1/2` (ball is convex; `starConvex_slitPlane`
  in `Mathlib/Analysis/Complex/Convex.lean`; intersect), so `StarConvex.isPreconnected`.

## 4. Classification (`Legendre/Classification.lean`)

For open preconnected nonempty `U ⊆ D`: given a solution `y`, take `z₀ ∈ U`,
`W = F L' - F' L = 1/(z₀(1-z₀)) ≠ 0`, `b = (F y' - F' y)/W`, `a = (y L' - y' L)/W` at `z₀`;
`y - aF - bL` has zero Cauchy data at `z₀`, so vanishes on `U`. Converse: `legendreOp` is
linear and local (open `U`). Independence: evaluate value and derivative at `z₀`, use `W ≠ 0`.

## 5. Period integral (`Legendre/Period.lean`)

For `|z| < 1` and `x ∈ (0,1)`:
`1/(1-zx)^{1/2} = ∑ ((1/2)ₙ/n!) (zx)ⁿ`, Mathlib
`one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero` (`Mathlib/Analysis/Analytic/Binomial.lean`),
coefficient `Ring.choose (1/2 + n - 1) n = (1/2)ₙ/n! = C(2n,n)/4ⁿ`.
Term-by-term (dominated: `‖term‖ ≤ |z|ⁿ · (x(1-x))^{-1/2}`, the latter integrable with
integral `π`):
`∫₀¹ x^{n-1/2}(1-x)^{-1/2} dx = B(n+1/2, 1/2) = Γ(n+1/2)Γ(1/2)/Γ(n+1) = π (1/2)ₙ/n!`
(Mathlib `Complex.betaIntegral`, `Complex.Gamma_mul_Gamma_eq_betaIntegral`,
`Complex.Gamma_one_half_eq`, `Gamma_add_one`), so
`∫ = ∑ ((1/2)ₙ/n!) zⁿ π ((1/2)ₙ/n!) = π ∑ aₙ zⁿ = π F z`.
Note `√(x(1-x)) · (1-zx)^{1/2}` with `x^{-1/2}(1-x)^{-1/2} = 1/√(x(1-x))` for `x ∈ (0,1)`.

## 6. Monodromy (`Legendre/Monodromy.lean`)

`g z = F z · (log(-z) + iπ) + G z` is holomorphic on `ball 0 1 \ [0,1)`
(`-z ∈ slitPlane`). For `Im z > 0`: `log(-z) + iπ = log z`; for `Im z < 0`:
`log(-z) + iπ = log z + 2πi` (arguments: `arg(-z) = arg z ∓ π`).

## 7. Connection formula (`Legendre/Connection.lean`)

Lens `U = ball 0 1 ∩ ball 1 1` is convex, open, `⊆ D`. `u z = F(1-z)` is holomorphic on
`U` and solves the ODE (the operator is invariant under `z ↦ 1-z`: `y(z) = F(1-z)`,
`y' = -F'(1-z)`, `y'' = F''(1-z)`, and `z(1-z)` and `(1-2z)` map to themselves up to the sign
matching `y'`). By §4, `u = αF + βL` on `U`. Determine `α, β` from the asymptotics as
`x → 0⁺` (real):

- `F x → 1`, `G x → 0`, `(F x - 1) log x → 0`, so `αF(x) + βL(x) = α + β log x + o(1)`.
- **Key asymptotic**: `F(1-x) + (1/π) log x → 4 log 2/π`. Proof (classical, `K(k) ~ log(4/k')`):
  by §5 with `z = 1-x` real and the substitution `t = sin²θ`,
  `π F(1-x) = 2 K` with `K = ∫₀^{π/2} dθ/√(x + (1-x)cos²θ)`. Put `k = √(1-x)`, `k' = √x`.
  `I₁ = ∫₀^{π/2} k sinθ dθ/√(k'² + k²cos²θ) = arsinh(k/k') = log((1+k)/k')` (substitute
  `u = k cos θ`). And `K - I₁ = ∫₀^{π/2} (1 - k sinθ)/√(k'² + k²cos²θ) dθ →
  ∫₀^{π/2} (1-sinθ)/cosθ dθ = log 2` by dominated convergence (integrand `≤ 2`:
  `(1-k)/k' ≤ 1` and `k(1-sinθ)/(k cosθ) ≤ 1`). So `K = log(4/k') + o(1) = 2 log 2 - (1/2)log x + o(1)`
  and `π F(1-x) = 4 log 2 - log x + o(1)`.
  *As formalized* (`Legendre/ConnectionAsymptotic.lean`), the same limit is reached without
  trigonometry: `t = 1 - s²` gives `π F(1-x) = J x = 2∫₀¹ ds/(√(1-s²)√(x+(1-x)s²))`; splitting
  `1/√(1-s²) = k + (1/√(1-s²) - k)` with `k = √(1-x)`, the first piece integrates exactly to
  `log(k+1) - (log x)/2` (antiderivative `log(ks + √(x+k²s²))`), and the remainder tends to
  `∫₀¹ s/(√(1-s²)(1+√(1-s²))) ds = log 2` by dominated convergence (bound `1/√(1-s²) + 1`).
- Comparing: `β log x + α - (4 log 2 - log x)/π → 0` forces `β = -1/π` (else unbounded), then
  `α = 4 log 2/π`.
