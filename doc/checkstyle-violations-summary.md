# Remaining checkstyle violations (non-suppressed)

**Generated from:** `mvn checkstyle:check` (without nocs profile)

## Summary by rule

| Rule | Count |
|------|-------|
| MissingJavadocMethod | 1,136 |
| Indentation | 936 |
| SummaryJavadoc | 601 |
| VariableDeclarationUsageDistance | 416 |
| AbbreviationAsWordInName | 354 |
| JavadocParagraph | 191 |
| MethodName | 31 |
| OverloadMethodsDeclarationOrder | 24 |
| ParameterName | 4 |
| JavadocTagContinuationIndentation | 2 |
| RecordComponentName | 2 |
| TypeName | 1 |
| **Total** | **~3,698** |

## Module distribution

- **jacop-core**: Majority of violations (constraints, cumulative, core, search, util)
- **jacop-floats**: Floats constraints, examples (circle_intersection, six_hump_camel_function, etc.)
- **jacop-sets**: Set constraints
- **jacop-sat**: Sat translation
- **jacop-flatzinc**: MethodName suppressed (0 MethodName violations)
- **jacop-examples-java**: Example classes

## MethodName violations (31 – only non-flatzinc)

- `no_sum` – Binpacking.java:505
- `FindGeneralizedMatching` – GCC.java:608
- `SCCs` – GCC.java:847
- `SCCsWithoutS` – GCC.java:988
- `ReachedFromY` – GCC.java:1077
- `circle_intersection` – CircleIntersection.java
- `curve_fitting3` – CurveFitting.java
- `markov_chains_taha` – Markov.java
- `min_cost_flow` – MinCostFlow.java
- `six_hump_camel_function` – SixHumpCamelFunction.java
- `tiny_tsp` – TinyTSP.java
- (and others in jacop-floats, jacop-sets, jacop-sat)

## Top violation types

1. **MissingJavadocMethod** – Public/protected methods missing Javadoc
2. **Indentation** – Incorrect indentation (typically nested if/for blocks)
3. **SummaryJavadoc** – First sentence missing period or forbidden fragments
4. **VariableDeclarationUsageDistance** – Variable declared too far from first use
5. **AbbreviationAsWordInName** – Names like `LBpruning`, `updateLB`, `lbSDom` (max 1 consecutive caps)

Full output: run `mvn checkstyle:check` and inspect console output.
