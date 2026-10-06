# Public semantic-scope audit

Date: 2026-10-06 (Asia/Tokyo)

## Result

```text
SEMANTIC OVERCLAIMS: 0
STATUS: PASS
```

The public Markdown was red-teamed for claims about ring-trace equivalence,
the independent almost-symmetric embedding-dimension-four bound, and the
derived unconditional nearly-Gorenstein bound.

The release correctly limits Lean certification to the project's formal
pseudo-Frobenius nearly-Gorenstein vector predicate
`SemigroupNearlyGorenstein`. It explicitly records all of the following as
outside this Lean certification:

1. equivalence with the one-dimensional numerical-semigroup-ring trace
   definition;
2. the independent theorem `e = 4` and almost symmetric implies `rho <= 7`;
3. the derived unconditional statement `e = 4` and nearly Gorenstein implies
   `rho <= 7`.

No public text presents any of these three statements as Lean-certified.

