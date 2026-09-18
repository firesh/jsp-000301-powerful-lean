# JSP-000301 / Erdős Problem 365

Lean 4 formalization of Solomon W. Golomb's counterexample to the question:
if two consecutive positive integers are powerful, must at least one be a
perfect square?

The answer is no. The main theorem `Jsp000301.jsp000301` proves the negation of
the universal statement, while `Jsp000301.golomb_counterexample` supplies the
explicit witness:

```text
12167 = 23³
12168 = 2³ · 3² · 13²
```

Both are powerful and consecutive; both lie strictly between `110²` and
`111²`, so neither is a square.

## Completeness

The project formalizes the standard definition of a powerful number and proves
its equivalence to a finite `Nat.primeFactors` certificate for positive
integers. The concrete prime-factor certificates use kernel reduction
(`decide +kernel`), not `native_decide`. There are no `sorry`, `admit`, custom
axioms, or unproved hypotheses standing in for the result.

## Build and audit

```bash
lake exe cache get
lake build
```

`AxiomAudit.lean` prints the axioms of both final theorems. The expected output
is only Lean/mathlib's standard `propext`, `Classical.choice`, and `Quot.sound`.

Tested with Lean `v4.33.0-rc1` and mathlib commit
`ae0d973d69b779efa724095bd41793b8cf233831`.

## Attribution

- Mathematical counterexample: Solomon W. Golomb, “Powerful numbers,”
  *American Mathematical Monthly* 77(8), 1970, 848–852,
  [DOI 10.2307/2317020](https://doi.org/10.2307/2317020).
- Problem: [Erdős Problem 365](https://www.erdosproblems.com/365), tracked as
  [JSP-000301](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0301-0400.md#JSP-000301).
- Formalization contributor: [firesh](https://github.com/firesh), with OpenAI
  Codex assistance.

This repository is an independently structured formalization of the explicit
counterexample. Other public formalizations and claims for the same problem may
exist; no claim of priority is made.

## License

Apache License 2.0. See [LICENSE](LICENSE).
