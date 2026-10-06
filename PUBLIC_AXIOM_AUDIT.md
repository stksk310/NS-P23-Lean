# Public axiom audit

Date: 2026-10-06 (Asia/Tokyo)

## Result

```text
PUBLIC AXIOM AUDIT: PASS
PROJECT-LOCAL AXIOMS: 0
```

The audit compiled `Tests/P23/AxiomCheckMain.lean`, which imports only
`P23.Main`, with OS process exit code `0`.

Every stable public theorem reported exactly the permitted standard Lean
axioms:

| Declaration | Axiom dependencies |
| --- | --- |
| `P23.high_relation_number_forces_almost_symmetric` | `propext`, `Classical.choice`, `Quot.sound` |
| `P23.type_two_nearly_gorenstein_not_almost_symmetric` | `propext`, `Classical.choice`, `Quot.sound` |
| `P23.type_three_nearly_gorenstein_not_almost_symmetric` | `propext`, `Classical.choice`, `Quot.sound` |
| `P23.original_p23` | `propext`, `Classical.choice`, `Quot.sound` |
| `P23.original_p23_of_type_two_or_three` | `propext`, `Classical.choice`, `Quot.sound` |

No project-local axiom appears in any result.

