# legendre-monodromy: the Legendre family in Lean 4

[![consolidated build](https://github.com/gnostrich/legendre-monodromy/actions/workflows/build.yml/badge.svg)](https://github.com/gnostrich/legendre-monodromy/actions/workflows/build.yml)

A Lean 4 and Mathlib formalization of the classical analytic theory of the
Legendre family of elliptic curves `E_λ : y² = x(x-1)(x-λ)` near `λ = 0`: its
period function, its Picard–Fuchs equation, the full space of solutions on the
slit disc, the local monodromy at `0`, and the connection formula linking the
Frobenius bases at `λ = 0` and `λ = 1`.

The period function is `F(λ) = ₂F₁(1/2, 1/2; 1; λ)`, Mathlib's
`ordinaryHypergeometric`. Its second Frobenius solution at `0` is
`L(λ) = F(λ) log λ + G(λ)`, where `G(λ) = ∑ aₙ hₙ λⁿ`,
`aₙ = (C(2n,n)/4ⁿ)²` and `hₙ = ∑_{k=1}^{n} 2/(k(2k-1))`.

Registered in the Palomar registry as
[PALOMAR-2026-11-24-000008](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-24-000008&version=1)
(version 1, commit `5856d40`).

## Exact claims

[`Challenge.lean`](Challenge.lean) imports only Mathlib and states the seven
compared theorems with `sorry`. It is the file to read to see exactly what is
claimed. [`Solution.lean`](Solution.lean) restates them and proves each by
appeal to the development in [`Legendre/`](Legendre). `comparator.json`
selects all seven.

| Theorem (`LegendreChallenge.`) | Statement |
|---|---|
| `F_solves_picardFuchs` | `F` is holomorphic on the unit disc and `λ(1-λ)F'' + (1-2λ)F' - F/4 = 0` there |
| `F_eq_period_integral` | `F(λ) = (1/π) ∫₀¹ dx / (√(x(1-x)) (1-λx)^{1/2})` for `|λ| < 1` (principal branch) |
| `wronskian_F_L` | `F L' - F' L = 1/(λ(1-λ))` on the slit disc `D = {|λ|<1} \ (-1,0]` |
| `solution_space` | `y` is holomorphic on `D` and solves the equation there iff `y = aF + bL` on `D` for constants `a, b` |
| `F_L_linearIndependent` | `aF + bL = 0` on `D` implies `a = b = 0` |
| `monodromy_at_zero` | `L` continues holomorphically across `(-1,0)`, from the upper half-disc to `L + 2πi F` on the lower half-disc |
| `connection_formula` | `F(1-λ) = (4 log 2 · F(λ) - L(λ))/π` on `{|λ|<1} ∩ {|λ-1|<1}` |

Together, `solution_space`, `F_L_linearIndependent` and `monodromy_at_zero`
say that `(F, L)` is a basis of the local solutions at `0` in which the local
monodromy is the unipotent matrix `[[1, 2πi], [0, 1]]`. `connection_formula`
expresses the solution `F(1-λ)`, which is regular at `λ = 1`, in that basis.

### Not claimed

- The global monodromy group (the level-2 congruence subgroup `Γ(2)`) is not
  formalized: Mathlib has no analytic continuation along paths. Only the
  local monodromy at `0`, and the connection formula on the lens where both
  local bases are defined, are proved.
- The geometric statement that `F` is a period of `E_λ` is represented only
  by the integral formula. Elliptic curves, differential forms and homology
  are not used.
- These are classical results, formalized here for the first time in Lean to
  our knowledge. They are not new mathematics.

## Layout

| File | Contents |
|---|---|
| `Legendre/Defs.lean` | `F`, `coeff`, `harm`, `G`, `L`, `D`, `legendreOp` (copied verbatim into the Challenge) |
| `Legendre/PowerSeries.lean` | Term-by-term differentiation for polynomially bounded coefficients; `legendreOp` on a power series |
| `Legendre/Solutions.lean` | `F` and `G` on the disc, `L` on `D`, the Picard–Fuchs equations, the Wronskian (Abel's identity) |
| `Legendre/Uniqueness.lean` | Vanishing Cauchy data at an ordinary point implies vanishing on a connected open set (derivative recursion, Taylor series, identity theorem) |
| `Legendre/Classification.lean` | The solution space on any connected open subset of `D` |
| `Legendre/Period.lean` | The period integral (binomial series, term-by-term integration, Beta integrals) |
| `Legendre/Monodromy.lean` | The continuation of `L` across the negative real axis |
| `Legendre/ConnectionAsymptotic.lean`, `Legendre/Connection.lean` | `F(1-x) + (1/π) log x → 4 log 2/π` as `x → 0⁺` (the classical `K(k) ~ log(4/k')`), and the connection formula |
| `BLUEPRINT.md` | The mathematical blueprint the proofs follow |

## Second entry: one node, one density (`comparator-node.json`)

The node `f(w) = w₁w₂` on the unit square `[0,1]²` is the local model of the
Legendre family's degeneration at `λ = 0`. Its density of states `P(s) = -log s`
controls the toy singular learning model `K(w) = (w₁w₂)²` with uniform prior.
The general monomial (normal-crossing) case is also proved: the zeta function, its
pole order (λ, m), and the free energy `λ log n − (m−1) log log n + O(1)`. This is the
form every singular-learning-theory computation reaches after resolution of
singularities (the resolution step is not formalized). [`ChallengeNode.lean`](ChallengeNode.lean) states eleven theorems, proved in
[`Node/`](Node) and selected by `comparator-node.json`. Metadata:
[`node/formalization.yaml`](node/formalization.yaml).

| Theorem (`NodeChallenge.`) | Statement |
|---|---|
| `node_density_of_states` | The pushforward of Lebesgue measure on `[0,1]²` under `w ↦ w₁w₂` has density `-log s` on `(0,1]` |
| `node_learning_zeta_integrable` | `∫_{[0,1]²} ((w₁w₂)²)^z` is finite iff `z > -1/2` (real `z`) |
| `node_learning_zeta` | For real `z > -1/2`, `∫_{[0,1]²} ((w₁w₂)²)^z = 1/(2z+1)²`: double pole at `-1/2`, i.e. `λ = 1/2`, `m = 2` |
| `monomial_zeta_integrable` | For `K = ∏ wⱼ^(2kⱼ)` and prior density `∏ wⱼ^(hⱼ)` on `[0,1]^d`: `K^z φ` is integrable iff every `2kⱼz + hⱼ + 1 > 0` |
| `monomial_zeta` | Then `∫_{[0,1]^d} K^z φ = ∏ⱼ 1/(2kⱼz + hⱼ + 1)` |
| `monomial_pole` | With `λ = minⱼ (hⱼ+1)/(2kⱼ)` attained by `m ≥ 1` indices, `(z+λ)^m ζ(z)` has a nonzero limit as `z → -λ⁺`: a pole of order exactly `m` |
| `monomial_partition_asymptotic` | For the same models (`hⱼ > -1`), `Z(n) = ∫ e^{-nK} φ ≍ n^{-λ} (log n)^{m-1}` |
| `monomial_free_energy` | `F(n) = -log Z(n) = λ log n - (m-1) log log n + O(1)` |
| `node_partition_sharp` | `Z(n) = ∫ e^{-nK} = (√π/(4√n))(log n + γ + 2 log 2) + O(e^{-n})` |
| `node_free_energy` | `-log Z(n) - (½ log n - log log n) → log(4/√π)` |
| `node_period_monodromy` | For Mathlib's covering map `exp` and the loop `θ ↦ e^{2πiθ}`, `IsCoveringMap.monodromy` sends `0` to `2πi`: `P = -log` continues to `P - 2πi` |

In the development, the zeta function, partition function and free energy are
all derived from one transfer lemma, which follows from the density theorem.
The zeta function is the Mellin transform of `-log s`, and `Z(n)` is its
Gaussian Laplace transform. The `log log n` term and the unipotent monodromy
therefore come from the same density `-log s`; that is the precise sense of the
entry's title.

Not claimed: general singular learning theory beyond the monomial case
(resolution of singularities, the reduction of a general model to normal-crossing
form; the free-energy asymptotic is proved for all monomial models but not for
general ones), b-functions, Picard–Lefschetz theory,
meromorphic continuation of zeta, and the categorical framing (Pugh et al.,
arXiv:2502.13810 and arXiv:2604.15100) mentioned in the metadata as background.
The results are classical or elementary. We found no prior formalization in the
Palomar registry or Mathlib, but searched nothing else, so priority among Lean
formalizations is unknown.

## Building

```bash
curl -sSfL https://elan.lean-lang.org/elan-init.sh | sh -s -- -y --default-toolchain none
lake exe cache get
lake build                       # Legendre/ and Solution.lean
lake build Challenge             # the sorried statement file
```

Toolchain `leanprover/lean4:v4.35.0`, Mathlib `v4.35.0`, Lean module system
throughout. CI (`.github/workflows/build.yml`) builds everything, fails on
any `sorry` outside `Challenge.lean`, and runs the toolchain's
`lake comparator` with `comparator.json`. That check covers statement match,
the axiom allowlist (`propext`, `Quot.sound`, `Classical.choice`) and replay
through Lean's kernel, NanoDa and con-ron.
`.github/workflows/palomar-preflight.yml` runs the Palomar registry's own
preflight.

## Provenance

Claude (Anthropic) wrote the blueprint and the Lean proofs, using agents
that iterated against the Lean compiler on the pinned toolchain. The author
chose the problem, approved the statements and takes responsibility for the
claims. No human has reviewed the proof terms line by line. The trust model
is Lean's kernel together with the axiom audit and the comparator check.
`formalization.yaml` records the details.

## Licence

Apache-2.0 (see `LICENSE`).
