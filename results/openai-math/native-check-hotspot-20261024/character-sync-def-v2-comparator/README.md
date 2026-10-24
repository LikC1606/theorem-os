# Standalone comparator entry-point probe

This probe copied the genuine completed V2 `Submission.olean`, its exact source,
the original challenge and the original comparator configuration (changing only
the challenge/solution module names, as in the native evaluator). The original
challenge compiled successfully in 1.52 seconds. The unchanged comparator binary
then exited 1 because this standalone directory has no Lake project configuration.
Its `safeLakeBuild` step requires a complete Lake project before exporting or
comparing declarations.

No mathematical comparison ran, no second compilation of Submission ran, and this
receipt does not contradict the successful full-source compile or axiom audit.
The native attempt already has the complete frozen project and continues through
the unchanged evaluator. This probe does not establish comparator or native
acceptance. Its original logs and exit codes are retained.
