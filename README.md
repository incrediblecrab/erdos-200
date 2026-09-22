# Erdős #200 — the longest arithmetic progression of primes in {1,…,N}

**Question.** Does it have length $o(\log N)$? **Status: open.** Not solved here.

**Objective.** Establish what is rigorously true, recompute $L(N)$ as far as compute
allows, test the standard heuristic against measured counts, and quantify why sieve
methods cannot close the gap.

**Inputs.** A local mirror of erdosproblems.com/200; OEIS A005115, A113827, A093364, A133277; Luhn's
records page; Granville, *Prime Number Patterns*; the Green–Tao note. Run
`refs/fetch.sh` — none are redistributed here.

**Findings.** $L(N)$ independently re-derived for every $N\le5.73\times10^{11}$. The
Hardy–Littlewood model matches exhaustive counts to within 1 % over 30 tests; it predicts
$L(N)\sim2\log N/\log\log N$, so the answer is conjecturally **yes** — but the decay is
$2/\log\log N$, invisible to any computation. The classical sieve bound is vacuous for
every $k$ and $N$. The known upper bound is now **machine-checked in Lean 4**:
$L(N)\le(1+o(1))\log N$ with **no hypotheses** — the statement DeepMind's
FormalConjectures leaves as `sorry`. Mathlib has no prime number theorem, so `lean/`
proves that form conditionally and gets $1/\log2=1.4427$ unconditionally; `lean-pnt/`
discharges the hypothesis against `PrimeNumberTheoremAnd` and recovers the constant $1$.

Read [`NOTES.md`](NOTES.md), and [`lean/README.md`](lean/README.md) and
[`lean-pnt/README.md`](lean-pnt/README.md) for the formal part. Reproduce with
`bash scripts/reproduce.sh`, `bash lean/verify.sh` and `bash lean-pnt/verify.sh`.

| path | contents |
|---|---|
| `src/apsearch.c` | exhaustive $k$-AP enumerator (C, pthreads) |
| `src/ref_bruteforce.py` | assumption-free reference; validates it |
| `src/verify_records.py` | 26 records, four independent checks |
| `src/heuristic.py` | Hardy–Littlewood singular series |
| `src/compare_counts.py`, `src/calibration.py` | model vs measurement |
| `src/barrier.py` | the sieve obstruction |
| `src/analysis.py` | the $L(N)$ tables |
| `src/final_check.py` | re-derives every claim; exit 0 = pass |
| `lean/` | Lean 4 + Mathlib formalisation; `lean/verify.sh`, exit 0 = pass |
| `lean-pnt/` | same bound without the PNT hypothesis, via `PrimeNumberTheoremAnd`; `lean-pnt/verify.sh`, exit 0 = pass |
| `data/`, `results/` | verified records, measured artifacts |
