# Sonar Triage Decisions

This file records explicit decisions for Sonar rules that are intentionally deferred or rejected.

## Ignored / Deferred Rules

### Import order rule

- **Rule pattern**: `Reorder this single-type import to come before static single-type imports.`
- **Decision**: Ignored for this repository backlog.
- **Reason**: Current repository formatting/tooling enforces static imports first (Checkstyle `CustomImportOrder` + Spotless/google-java-format workflow). Enforcing the opposite order in Sonar would create formatter-vs-linter churn.
- **Action**: Do not fix existing findings of this type during current complaint-reduction batches.

### Abbreviation-as-word naming rule (targeted readability exception)

- **Rule pattern**: `Abbreviation in name '<name>' must contain no more than '1' consecutive capital letters.`
- **Decision**: Deferred for selected readability-sensitive helper names.
- **Reason**: For Sudoku primitive helpers, names like `addXneqYConstraints` are intentionally kept because they directly reflect the underlying JaCoP primitive constraint notation (`XneqY`) and are clearer than alternatives.
- **Example complaint**: `jacop-examples-java/src/main/java/org/jacop/examples/fd/Sudoku.java` — `Abbreviation in name 'addXneqYConstraints' must contain no more than '1' consecutive capital letters.`
- **Action**: Keep these specific names; do not rewrite them only to satisfy this rule.

