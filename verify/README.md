# Independent finite-model checks

This engine checks the finite models at N = 4, 6, 8, including full-space comparisons and corruption controls. It does not certify arbitrary-state lower bounds or a complete compiled game. The ancillary README documents its relation labels and scope.

Run one command at a time with numerical-library thread counts set to one:

```
python -B run_e2.py 8
python -B run_e2.py 4 6 --full 4 6 --ablate 4 6
python -B compiler_checks.py
python -B dims_study.py
python -B report_tables.py
```

The N = 8 run has an observed peak working set of about 656 MB. The combined N = 4, 6 full-space and ablation command has a larger previously observed peak of about 1.31 GB; a monitored process-tree run reached 1.36 GB (1,360,596,992 bytes). Use a monitored process-tree ceiling below 1.5 GB; do not run these commands concurrently. Recorded results are in `out/`, covered with the sources by `SHA256SUMS`.
