# NS-P23-Lean

Lean 4 formalization of Original Question 4.3 for minimally four-generated nearly Gorenstein numerical semigroups.

## Overview

This repository formalizes the type-two and type-three branches of Original Question 4.3 for minimally four-generated numerical semigroups. For a numerical semigroup `D`, the formal development uses its type `t = D.semigroupType`, relation number `rho = D.semigroupRho`, the project predicate `SemigroupNearlyGorenstein`, and the branch in which `D` is not almost symmetric.

Under the project's PF nearly-Gorenstein vector criterion and the not-almost-symmetric hypothesis, Lean proves:

- if `t = 2`, then `rho = 4` or `rho = 5`;
- if `t = 3`, then `rho = 6`.

Release status:

```text
ORIGINAL NS-P23 MATHEMATICS: CLOSED
LEAN FORMALIZATION: FINAL ARTIFACT ACCEPTED
P23.Main: FROZEN
```

## Formalized almost-symmetry forcing theorem

For type two or three, the project formalizes that

```text
rho >= type + 4
```

under `SemigroupNearlyGorenstein` forces almost symmetry.

## Main Lean entry point

Downstream users should import only:

```lean
import P23.Main
```

The stable public theorems are:

```lean
P23.high_relation_number_forces_almost_symmetric
P23.type_two_nearly_gorenstein_not_almost_symmetric
P23.type_three_nearly_gorenstein_not_almost_symmetric
P23.original_p23
P23.original_p23_of_type_two_or_three
```

## Build

The accepted environment is:

```text
Lean/mathlib: v4.34.0-rc1
mathlib commit: de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11
```

From the repository root, run:

```powershell
lake build
```

The checked-in `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` pin the artifact's actual Lake configuration.

## Certification

```text
Production solver dependency: none
Project-local sorry/admit/axiom: 0
Final independent artifact audit: PASS (accepted release status)
```

The locally available certification material is:

- [Final certification report](docs/FINAL_CERTIFICATION_REPORT.md)
- [Run38 package receipt](docs/RUN38_PACKAGE_RECEIPT.md)

The separate independent-audit Markdown document was not available locally when this public bundle was assembled, so it is not included or linked. Its absence does not alter the accepted release status recorded above.

## Semantic scope

`SemigroupNearlyGorenstein` is this project's formal PF nearly-Gorenstein vector predicate.

This repository does **not** formalize the equivalence between that predicate and the one-dimensional numerical-semigroup-ring trace definition. Accordingly, it does not claim that the full ring-theoretic notion has been Lean-certified.

## Non-formalized corollaries

The independent theorem

```text
e = 4 and almost symmetric -> rho <= 7
```

is not part of this Lean certification. The derived unconditional statement

```text
e = 4 and nearly Gorenstein -> rho <= 7
```

is also not Lean-certified in this repository.

## Author and citation

```text
Author: Keisuke Sato
Affiliation: Independent researcher, Japan
ORCID: https://orcid.org/0009-0005-4230-0268
```

Citation: [CITATION.cff](CITATION.cff)

DOI: pending Zenodo publication

## License

License: Apache-2.0

See the full standard license text in [LICENSE](LICENSE).

