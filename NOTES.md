# Erdős problem #200 — notes

**Question.** Let $L(N)$ be the length of the longest arithmetic progression of primes
contained in $\{1,\dots,N\}$. Is $L(N) = o(\log N)$?

**Status: open.** From a local mirror of
[erdosproblems.com/200](https://www.erdosproblems.com/200) (scraped 2026-09-22), the
status is `OPEN`, the statement is *"Does the longest arithmetic progression of primes in
$\{1,\ldots,N\}$ have length $o(\log N)$?"*, the recorded progress is *"It follows from
the prime number theorem that such a progression has length $\leq(1+o(1))\log N$"*, the
sources are `["ErGr79", "ErGr80"]`, and the linked sequence is `A005115`. The site itself
is JS-rendered behind Cloudflare and has no JSON API, so the mirror — not a scrape — is
the source used here. Re-checked 2026-09-22 against the upstream dataset
[`teorth/erdosproblems`](https://github.com/teorth/erdosproblems) `data/problems.yaml`,
which also records `state: "open"`; the live page carries no comments and no proof
claims. The DeepMind Lean formalisation
`FormalConjectures/ErdosProblems/200.lean` states the question and the known variant
$L(N)\le(1+o(1))\log N$; both are `sorry`, so nothing is proved there. [`lean/`](lean/)
and [`lean-pnt/`](lean-pnt/) discharge the second (§9) — unconditionally, with the
literature constant $1$.

**This document does not solve the problem.** It records an explicit rigorous upper
bound, an independent exhaustive re-derivation of $L(N)$ as far as compute allows, a
validated heuristic predicting that the answer is *yes*, and a quantitative statement
of why the standard method cannot reach it.

---

## 0. Summary of claims and their status

| # | Claim | Status |
|---|---|---|
| 1 | Structure theorem for APs of primes (Prop. 1) | proved below; checked numerically against all 26 records; **machine-checked in Lean** (`structure_of_primeAP`) |
| 2 | $\theta(L(N)) \le \log N + 1/(L(N)-1)$, hence $L(N)\le(1+o(1))\log N$ (Prop. 2) | proved below; not new — this is the standard PNT bound made explicit; **machine-checked in Lean** (`theta_lt_sharp`) |
| 3 | $L(N)$ exactly, for all $N \le 5.73\times10^{11}$ | **independently recomputed here** (exhaustive) |
| 4 | $L(N)$ exactly, for all $N < a(27)$ — certainly for all $N < a(26)=1.28\times10^{16}$, since $a(27)$ is known only to satisfy $a(27)\le 6.96\times10^{17}$ | cited (OEIS A005115, Luhn), verified for consistency, not recomputed |
| 5 | Hardy–Littlewood model of the AP count | validated against exact counts, geometric mean ratio 0.9939 over 30 tests |
| 6 | $L(N)\sim 2\log N/\log\log N$, so the answer is **yes** | heuristic only — *not* a proof |
| 7 | No sieve upper bound of the classical shape yields $L(N)\le c\log N$ for any $c$ | computed below; vacuous by a margin of $\ge 10^{3.2}$, growing without bound |
| 8 | Best known lower bound: $L(N)\gg\log_2^{(7)}N$ | cited (Green–Tao), verified verbatim from the source |
| 9 | $L(N)\le(1+o(1))\log N$, **unconditionally** | **machine-checked in Lean 4** (§9) — DeepMind's `erdos_200.variants.upper`, which they leave `sorry`. The PNT is imported from `PrimeNumberTheoremAnd`; `lean/` alone yields the weaker constant $1/\log2$ |

Nothing here improves the known upper bound. Claim 7 explains why that should be
expected from sieve methods, and is the main negative content of these notes.

---

## 1. Structure of an AP of primes

Write $W_k=\prod_{p\le k}p$ for the primorial, so $\log W_k=\theta(k)$.

> **Proposition 1.** Let $a,a+d,\dots,a+(k-1)d$ be primes with $k\ge3$ and $d\ge1$.
> Then exactly one of the following holds.
>
> **(A)** $a>k$ and $W_k \mid d$.
> **(B)** $k$ is prime, $a=k$, and $(W_k/k)\mid d$.

*Proof.* First, a general observation. Let $p\le k$ be prime with $p\nmid d$. Then $d$
is invertible mod $p$, so as $i$ runs through $0,1,\dots,p-1$ — a subrange of
$0,\dots,k-1$ since $p\le k$ — the terms $a+id$ run through every residue class mod
$p$. Hence some term is divisible by $p$; being prime, that term *equals* $p$. As
$a\le a+id$, this forces $a\le p\le k$.

Contrapositive: if $a>k$ then $p\mid d$ for every prime $p\le k$, and since these primes
are distinct, $W_k\mid d$. That is (A).

Now suppose $a\le k$. Then $a$ is a prime $q\le k$. If $q\mid d$ then $a+d=q+d$ is a
multiple of $q$ strictly larger than $q$, contradicting primality; so $q\nmid d$. The
term of index $q$, namely $a+qd=q(1+d)$, is a multiple of $q$ strictly larger than $q$,
so it cannot be a term of the progression: the index $q$ must exceed $k-1$, i.e.
$q\ge k$. With $q\le k$ this gives $q=k$, so $a=k$ and $k$ is prime. Finally, for any
prime $p\le k$ with $p\ne k$: if $p\nmid d$ then by the observation $a\le p<k=a$, absurd;
so $p\mid d$, and therefore $(W_k/k)\mid d$. That is (B).

The two cases are mutually exclusive since $a>k$ in (A) and $a=k$ in (B). $\blacksquare$

Case B is not vacuous: $3,5,7$ and $5,11,17,23,29$ and $7,157,\dots,907$ are exactly the
records for $k=3,5,7$. It is, however, rare — no record for $k\ge8$ is of Case B, and
none of the 5,503,986 progressions enumerated in §3 for $k\ge8$ is either.
Forgetting Case B is the natural bug here, and it changes the answer: see §3.2.

## 2. An explicit upper bound

> **Proposition 2.** If $\{1,\dots,N\}$ contains a $k$-term AP of primes, $k\ge3$, then
> $$N \;\ge\; \begin{cases}
> \min\bigl(p_k^{+}+(k-1)W_k,\;\; k+(k-1)W_k/k\bigr), & k \text{ prime},\\[2pt]
> p_k^{+}+(k-1)W_k, & k \text{ composite},
> \end{cases}$$
> where $p_k^{+}$ is the least prime $>k$. In either case
> $$W_k \;<\; \frac{k}{k-1}\,N, \qquad\text{equivalently}\qquad \theta(k) \;<\; \log N+\frac{1}{k-1}.$$

*Proof.* By Prop. 1 the progression is of Case A or Case B. In Case A, $d\ge W_k$ and
$a\ge p_k^{+}$, so the last term is $a+(k-1)d\ge p_k^{+}+(k-1)W_k$. In Case B,
$d\ge W_k/k$ and $a=k$, so the last term is $\ge k+(k-1)W_k/k>(k-1)W_k/k$. The Case B
bound is the smaller of the two, giving $(k-1)W_k/k<N$; take logarithms and use
$\log\frac{k}{k-1}=-\log(1-\tfrac1k)\le\frac{1}{k-1}$. $\blacksquare$

> **Corollary.** $\theta(L(N))<\log N+\tfrac{1}{L(N)-1}$, and since $\theta(x)\sim x$
> (prime number theorem), $L(N)\le(1+o(1))\log N$. With an effective lower bound of the
> shape $\theta(x)>x(1-1/\log x)$ this becomes
> $$L(N)\;\le\;\log N+\bigl(1+o(1)\bigr)\frac{\log N}{\log\log N}.$$

This is the bound quoted on the problem page; Prop. 2 just makes the $o(1)$ explicit and
identifies the binding constraint as Case B. The operational form used in
`analysis.py` is sharper still: $L(N)\le\max\{k: \text{(Prop. 2 bound)}\le N\}$, computed
directly from the primorial. That form is exact and needs no estimate for $\theta$.

*A note on the effective $\theta$ estimate.* The inequality $\theta(x)>x(1-1/\log x)$ for
$x\ge41$ is attributed to Rosser–Schoenfeld (1962). I verified it numerically here for
$41\le x<5\times10^6$ (348,500 evaluation points, one just below each prime where the
inequality is tightest; zero violations, minimum margin 0.400), but I **could not
retrieve the paper** — Project Euclid serves a JS wall and the AMS mirror returns 403 —
so the equation number is not confirmed and is deliberately not cited. Nothing in §§1–3
depends on it; it enters only the asymptotic restatement in the Corollary.

**Sanity check.** At $N=a(26)=1.2783\times10^{16}$, Prop. 2 gives $L\le43$ while the
truth is $L=26$. The bound's ratio to $\log N$ decreases to $1.0058$ at $N=10^{10^4}$,
confirming that it really does realise the $(1+o(1))\log N$ ceiling and not something
weaker.

## 3. Exhaustive computation

### 3.1 Method

Prop. 1 turns the search into something cache-friendly. For Case A every term lies in
one residue class $r \bmod W_k$ with $\gcd(r,W_k)=1$; for each of the $\varphi(W_k)$
classes we sieve the arithmetic progression $r, r+W_k, r+2W_k,\dots$ into a bitset and
look for $k$ positions in AP by intersecting shifted copies of the bitset. Case B is a
separate, much smaller loop. `src/apsearch.c` implements this with pthreads.

### 3.2 Validation of the search

Prop. 1 is an *assumption* from the search's point of view, so it is checked against a
program that does not use it. `src/ref_bruteforce.py` loops over every difference $d$
and every first term $a$ with no structural shortcut, shares no code with `apsearch.c`,
and is written in numpy rather than C.

* **Agreement:** exact, on all 11 $(k,B)$ pairs tested — both the total number of
  progressions and the minimal last term.
* **Negative control:** recompiling with Case B deliberately disabled makes the two
  disagree, as it must — $k=3$: 186267 vs 186647 progressions, minimum 17 vs 7;
  $k=5$: 13789 vs 13835, minimum 127 vs 29; $k=7$: 2508 vs 2515, minimum 1307 vs 907.
  So the cross-check has teeth; it is not passing vacuously.

### 3.3 Results

Exhaustive enumeration reproduced $a(k)$ — the least possible last term of a $k$-AP of
primes, OEIS [A005115](https://oeis.org/A005115) — together with its first term and
common difference, for $k=3,\dots,20$.

The $k=20$ run went to $B=a(20)=572945039351$ and found **exactly one** 20-term
progression, namely $214861583621+18846497670i$, $0\le i\le19$. A 21-term AP with last
term $\le B$ would contain two distinct 20-term APs with last term $\le B$ (its terms
$1..20$ and its terms $2..21$), so a single 20-term AP rules out any 21-term AP below
$B$. The same argument at $k=19$, whose run to $B=1.5\times10^{11}$ also returned exactly
one progression, independently rules out a 20-term AP below $1.5\times10^{11}$. Hence:

> $L(N)$ has been **independently re-derived here for every $N\le5.73\times10^{11}$**.

Beyond that range, $L(N)=\max\{k:a(k)\le N\}$ is determined by the tabulated records
$a(21),\dots,a(26)$, which are cited rather than recomputed. $L(N)$ is unknown for
$N\ge a(27)$; the least known 27-term AP ends at $696112717486210091$, and its
minimality is not proved.

### 3.4 The record table

All 26 known values of $a(k)$ were checked four independent ways: the terms form an AP,
`sympy.isprime`, an independently written deterministic Miller–Rabin, distinctness, and
agreement with Norman Luhn's records page (a source independent of OEIS). 26 records,
0 failures. Minimality of $a(k)$ for $k=23,\dots,26$ is itself a computational result of
Perrenet and Petukhov, cited from Luhn's page, not reproved here.

The relevant column is $k/\log a(k)$ — the largest value of $L(N)/\log N$ attained when
$L$ jumps to $k$:

| $k$ | $a(k)$ | $k/\log a(k)$ |
|---|---|---|
| 3 | 7 | 1.5417 |
| 10 | 2089 | 1.3081 |
| 13 | 725663 | 0.9633 |
| 17 | 4827507229 | 0.7624 |
| 20 | 572945039351 | 0.7387 |
| 23 | 449924511422857 | 0.6817 |
| 26 | 12783396861134173 | 0.7011 |

The ratio has fallen from $1.54$ to about $0.70$ and is drifting down slowly and
non-monotonically. §5 explains why this is exactly what the conjecture predicts and why
it is not evidence either way.

## 4. The Hardy–Littlewood model

For a fixed difference $d$, the expected number of $k$-APs of primes with first term
near $t$ is $\mathfrak S(d)\prod_{i=0}^{k-1}1/\log(t+id)$, where the singular series is
$$\mathfrak S(d)=\prod_p\frac{1-\omega_d(p)/p}{(1-1/p)^k},\qquad
\omega_d(p)=\begin{cases}1,&p\mid d\\ \min(k,p),&p\nmid d.\end{cases}$$
For $W_k\mid d$ this factors as $\mathfrak S(W_km)=A_kT_k\,g(m)$ with
$A_k=\prod_{p\le k}(1-1/p)^{1-k}$, $T_k=\prod_{p>k}(1-k/p)(1-1/p)^{-k}$, and
$g(m)=\prod_{p\mid m,\,p>k}\frac{1-1/p}{1-k/p}$. Summing over $d=W_km$ gives
$$C_k(N)\;\approx\;\frac{A_kT_k\,\mathbb E[g]\,N^2}{2(k-1)W_k(\log N)^k}.$$
The shape $N^2/(2(k-1)\log^kN)$ times a singular series is the same normalisation Tao
and Teräväinen state in Example 1.7 of [arXiv:2107.02158](https://arxiv.org/abs/2107.02158),
which is an independent check on the constant.

**Validation.** Predicted counts were compared with *exhaustively measured* counts at 30
$(k,N)$ points, $k=8,\dots,16$ and $N$ from $9.8\times10^5$ to $8\times10^9$, with measured
counts ranging from 22 to 4,513,153:

> geometric mean predicted/observed = **0.9939**, geometric s.d. **1.036**, full range
> 0.900 – 1.093.

The model was fitted to nothing: every constant is the Hardy–Littlewood one. Reproduced by
`src/compare_counts.py`, which reads the histograms emitted by the exhaustive runs and is
re-checked by `src/final_check.py`.

**Calibration.** $a(k)$ is a *minimum*, so the right test is not whether
$a(k)/\text{threshold}\approx1$ — it will not be — but whether
$U_k=\exp(-C_k(a(k)))$ is uniform, as a Poisson model implies. Over the 21 records whose
extremal AP is of Case A (the model covers Case A only; $k=3,5,7$ are excluded):

> Kolmogorov–Smirnov $D=0.128$, $p=0.86$; mean $U=0.494$ against an expected $0.500$.

A regression of $\log C_k(a(k))$ on $k$ gives slope $+0.098\pm0.042$ ($t=2.31$) over all
21 points, which looks like a mild systematic drift. It is not: restricting to $k\ge11$
gives $+0.007\pm0.058$ ($t=0.11$), $k\ge14$ gives $-0.090\pm0.058$, $k\ge17$ gives
$-0.070\pm0.082$. The apparent trend is driven entirely by the small-$k$ records, where
$a(k)$ is 23, 157, 1669 — far too small for an asymptotic prime-density model to apply.

**Cross-check against Granville.** Granville (*Prime Number Patterns*, Amer. Math.
Monthly **115** (2008) 279–296, §2.1, eq. (2.1);
[DOI:10.1080/00029890.2008.11920529](https://doi.org/10.1080/00029890.2008.11920529))
conjectures that the largest prime of
the smallest $k$-AP is about $(e^{1-\gamma}k/2)^{k/2}$, and states that dividing $a(k)$
by it leaves a quotient "in $(2/5,2)$ for each $n$, $15\le n\le21$". My implementation
reproduces that interval exactly for all seven values — 1.9915, 0.4025, 1.6709, 0.9773,
0.7749, 0.8356, 1.4021 — which confirms the formula is implemented as he wrote it.
Extending to the records published since: 1.197, 2.206, 0.855, 0.569, **0.173** for
$k=22,\dots,26$. The tight interval does not persist; $a(26)$ in particular is well below
both his formula and the Hardy–Littlewood threshold. Under the Poisson model that is a
$U=0.81$ event, unremarkable on its own, but it is an honest caveat against reading too
much into the fit.

*(Eq. (2.1) and the tower below were read from a 400 dpi render of the page, not from
the PDF text layer, which mangles both.)*

## 5. What the model predicts, and why no computation can confirm it

Setting $C_k(N)=1$ and using Mertens' $\prod_{p\le k}(1-1/p)^{-1}\sim e^{\gamma}\log k$:
$$2\log N \;\approx\; k\bigl(\log\log N-\log\log k+1-\gamma\bigr),$$
so
$$\boxed{\;L(N)\;\sim\;\frac{2\log N}{\log\log N}\;}$$
more precisely $L(N)\approx 2\log N/(\log\log N-\log\log\log N+1-\gamma)$. This is
$o(\log N)$: **the conjectured answer to Erdős's question is yes.** It agrees with
Granville's (2.1), which is the same statement solved for $a(k)$ — though the inversion
is mine: Granville prints a conjecture about the *endpoint* $a(k)$, hedged with "about",
not a ratio asymptotic for $L(N)$. No published source states $L(N)\sim2\log N/\log\log N$
in that form, so treat the constant 2 as re-derived here and corroborated by him, not
quoted from him.

The decay is, however, only $2/\log\log N$, and that is the honest punchline:

| $N$ | conjectured $L(N)/\log N$ |
|---|---|
| $10^{16}$ | 0.678 |
| $10^{30}$ | 0.584 |
| $10^{100}$ | 0.456 |
| $10^{1000}$ | 0.316 |
| $10^{10^6}$ | 0.159 |
| $10^{10^9}$ | 0.105 |

The measured value at $N=a(26)\approx10^{16.1}$ is 0.701, against 0.678 predicted. The
ratio is still above $2/3$ at $N=10^{30}$ and does not fall below $1/2$ until about
$N=10^{100}$. **No computation will ever make the $o(1)$ visible.** Data sitting near
0.7 is not evidence against the conjecture; it is precisely what the conjecture predicts.
Anyone arguing from the numerical table in either direction is over-reading it.

## 6. Why sieve methods give nothing

This is the substantive negative result, and it is computed in `src/barrier.py`.

The classical $k$-dimensional Selberg / Halberstam–Richert upper bound for an admissible
$k$-tuple loses a factor $2^kk!$ against the conjectured truth:
$$\#\{a\le x: a+h_1,\dots,a+h_k \text{ all prime}\}\;\le\;\bigl(2^kk!+o(1)\bigr)\mathfrak S(H)\frac{x}{(\log x)^k}.$$
Applying it for every admissible $d$ and summing gives $B(k,N)=2^kk!\,C_k(N)$. If
$B(k,N)<1$ for some $k=c\log N$ with $c<1$, that would prove $L(N)<c\log N$ and settle
the problem. Substituting the asymptotics of §4, $B(k,N)<1$ requires
$$\log\log k+\log c+\gamma+\log 2-2+\frac{2}{c}\;<\;0 .$$
The function $\log c+2/c$ is minimised at $c=2$ with value $1+\log2$, so the requirement
is at best $\log\log k<2-\gamma-2\log2-1=-0.9635$, i.e. **$k<1.465$**. At $c=1$ it is
$k<1.33$; at $c=1/2$, $k<1.08$.

> **No $k\ge3$ qualifies, at any $c$.** The classical sieve bound is vacuous for every
> $k$ and every $N$ — it does not even recover the trivial primorial bound of Prop. 2.

Evaluated numerically on a grid of $\log_{10}N$ from $2$ to $10^{100}$ and
$c\in\{0.2,\dots,1.0\}$: $\min\log_{10}B=3.21$, attained at the very smallest case, and
$\log_{10}B$ grows without bound thereafter (e.g. $2.8\times10^9$ at
$\log_{10}N=10^9$, $c=0.5$). The asymptotic form of $C_k$ used there *under*states the
exact heuristic by a factor of about 2 (geometric mean 0.539 over 12 test points), so
$B$ is understated and the conclusion is conservative.

The obstruction is sharp enough to quantify. The overshoot factor is
$\exp\bigl(k[\log\log k+\log c+\gamma+\log2-2+2/c]\bigr)$, whose leading $k$-dependence
is $(\log k)^{k}$. So one would need to **beat the Selberg constant $2^kk!$ by a further
factor $(\log k)^{k(1+o(1))}$**. Elliott–Halberstam-type improvements save at most
$2^k$ — nowhere near enough. And a *perfect* sieve, with constant $1$, returns exactly
the Hardy–Littlewood threshold $k\sim2\log N/\log\log N$, i.e. it would answer the
question. The entire difficulty of Erdős #200 sits in that gap, which is the parity
problem.

(Applying the sieve bound for *every* $d$ is generous: when $d$ is comparable to $N$ the
tuple diameter is comparable to $x$ and the bound in that form is not available at all.
Granting it anyway only inflates $B$, so the demonstration that $B>1$ is a fortiori.)

## 7. Lower bounds: what is actually known

For completeness, in the other direction. The only *explicit* threshold in the
literature is the Green–Tao expository note *A bound for progressions of length k in the
primes*, which extracts from their theorem that the first $k$-AP of primes is bounded by
an exponential tower. Verbatim from the abstract:

> "the argument shows that those primes are bounded by an exponential tower in $k$ of
> height seven"

and the final display is $O(NW)\le 2\uparrow2\uparrow2\uparrow2\uparrow2\uparrow2\uparrow2\uparrow O(k)$
— seven 2's. (Check it with `pdftotext refs/green_tao_envelope.pdf -`: the last line
containing $\uparrow$ is `O(NW ) ⩽ 2 ↑ 2 ↑ 2 ↑ 2 ↑ 2 ↑ 2 ↑ 2 ↑ O(k).`, seven arrows.
Do not count arrows document-wide; the note uses $\uparrow$ for ordinary exponentiation
throughout, 185 times.) Green and Tao add the remark that
"$100k$ will certainly suffice" for the implied constant. Inverting gives
$$L(N)\;\gg\;\log_2^{(7)}N,$$
a seven-fold iterated logarithm. That is the best explicit lower bound I could source.

Two corrections to things commonly repeated:

* **Granville renders the tower with eight 2's**, $2^{2^{2^{2^{2^{2^{2^{2^{100k}}}}}}}}$,
  one level taller than Green–Tao's own stated height of seven. Both readings were
  confirmed from the rendered pages. Granville's "8 twos" is what he wrote; it is not
  what Green–Tao claim.
* **Leng–Sah–Sawhney ([2402.17994](https://arxiv.org/abs/2402.17994),
  [2402.17995](https://arxiv.org/abs/2402.17995)) do not state any bound for the
  primes.** They improve the inverse theorem to quasipolynomial and Szemerédi to
  $r_k(N)\ll N\exp(-(\log\log N)^{c_k})$, both for *dense sets*. The word "prime" occurs
  in them only as a technical modulus and in historical remarks.

The real modern advance is Tao–Teräväinen ([2107.02158](https://arxiv.org/abs/2107.02158),
JEMS 2023), which makes the $k$-AP-in-primes *count* effective with error
$O((\log\log N)^{-c})$. In principle that yields a vastly better $N_0(k)$ than the tower,
but they do not write one down and the $k$-dependence of the constants is left implicit,
so no explicit $L(N)\gg(\log\log N)^{c}$ statement exists in the literature that I could
find. I am not asserting one.

Teräväinen–Wang, *On the Green–Tao theorem for sparse sets*
([2603.09281](https://arxiv.org/abs/2603.09281), 10 Mar 2026), is the most recent
quantitative work in this direction: if $\mathcal{A}$ has relative density $\delta$ in the
primes up to $N$ and contains no nontrivial $k$-AP with $k\ge4$, then
$\delta\ll\exp(-(\log\log\log N)^{c_k})$. Taken at $\delta=1$ — $\mathcal{A}$ the whole set
of primes — this forces a $k$-AP once $(\log\log\log N)^{c_k}$ exceeds the implied
constant, which is a *triple*-logarithmic threshold rather than a seven-fold tower. **It
still does not produce an explicit lower bound for $L(N)$**, because inverting it requires
knowing how $c_k$ and the implied constant degrade in $k$, and the abstract states neither.
Recorded here as the current frontier, not as a bound. *I read the abstract only; I have
not worked through the paper.*

**Upper bound.** No constant $c<1$ with $L(N)\le(c+o(1))\log N$ is known. That is the
whole problem. A literature search (2026-09-22) found no improvement on the constant $1$
— not unconditionally, not under GRH, not under Elliott–Halberstam, and not under uniform
Hardy–Littlewood. That is a negative search result, not a proof that none exists.

## 8. What would count as progress

1. Any $c<1$ with $L(N)\le c\log N$ for large $N$. By §6 this cannot come from a
   classical sieve. It is worth being precise about *why*, because the obvious escape
   route is already closed. One might hope to exploit the **rigidity** of an AP — all
   $k$ terms lie in one progression, rather than forming an arbitrary admissible
   $k$-tuple. But the bound $B(k,N)$ of §6 already exploits that fully: by Prop. 1 the
   common difference satisfies $W_k\mid d$, and $B$ is obtained by summing the tuple
   bound only over those $d$, which is exactly what puts $(k-1)W_k$ in the denominator
   of $C_k(N)$. Rigidity is therefore already spent, and the entire remaining deficit is
   the per-tuple constant $2^kk!$. So the requirement is not "use more structure" but
   specifically: **obtain a $k$-tuple upper bound with constant
   $2^kk!/(\log k)^{k(1+o(1))}$ or better, uniformly for $k\asymp\log N$.** A constant of
   $1$ — a perfect sieve — would return the Hardy–Littlewood threshold itself and settle
   the problem outright. That gap is the parity problem, and nothing short of breaking it
   is known to help.
2. An unconditional bound $L(N)=o(\log N)$ with any decay rate, however slow — the
   conjecture says the truth is $2/\log\log N$, so even $\log N/\log\log\log N$ would be
   a first.
3. In the other direction, extracting an explicit $N_0(k)$ from Tao–Teräväinen would
   replace the seven-fold iterated logarithm with something enormously better, and is
   apparently just bookkeeping through Manners' constants — but it is bookkeeping nobody
   has published.

An accessible-*sounding* computational contribution would be $a(27)$: the least 27-term
AP of primes is known only as an upper bound, $\le 696112717486210091$. But the cost
model above rules it out here. For $k=27$, $W_{27}=223092870$ and
$\varphi(W_{27})=36495360$, so $M=B/(26W_{27})\approx1.20\times10^{8}$ and the
enumerator needs $\varphi(W)M^2/(2\cdot26\cdot64)\approx1.6\times10^{20}$
word-operations — about $3.2\times10^{12}$ core-seconds, or $10^{5}$ core-years at the
$4.9\times10^{7}$/core-second measured in §3. That is four to five orders of magnitude
beyond a single machine *for this enumerator*.

It does not follow that $a(27)$ is out of reach, and an earlier draft of these notes
wrongly said the $a(23)$–$a(26)$ minimality proofs were distributed efforts. They were
not. Joris Perrenet's
[`arithmetic-progression`](https://github.com/jorisperrenet/arithmetic-progression/blob/6507fcb038a91a3711e486365c60b3aa37662778/README.md)
records $a(25)$ "proven minimal-end" in **~2 days** and $a(26)$ in **~3 days**, both on a
**single RTX 4090**, searching the restricted shape $(a+bn)\cdot23\#+c$ rather than all
integers. The relevant gap is therefore not core-count but algorithm and hardware: a
generic CPU enumerator over all residues is the wrong instrument by some five orders of
magnitude. Perrenet attaches his own disclaimer — "Sadly I lost track of which ones were
used to produce the records above" — so the runtimes are reported, not reproduced here.
Verified independently: his AP-26 witness $(15626261+1666981n)\cdot23\#+59138353$ has
last term $12783396861134173$, exactly OEIS $a(26)$.

## 9. Machine-checked formalisation

Propositions 1 and 2 above are informal proofs, and the bound they imply is the one Erdős
and Graham already credit to the prime number theorem. What was missing was a machine
check. DeepMind's `FormalConjectures/ErdosProblems/200.lean` states the problem and the
known variant, and both declarations are `sorry` — verified directly in the revision
pinned here (`e5f4281`), at lines 44 and 52 of that file.

[`lean/`](lean/) closes the second one. The development is 673 lines of Lean 4 against
Mathlib `0df444a3` (toolchain `v4.33.1`), and depends on `formal-conjectures` itself, so
the statement being proved is *their* statement rather than a paraphrase of it.

| theorem | content |
|---|---|
| `structure_of_primeAP` | Proposition 1 |
| `mul_primorial_lt` | $(k-1)W_k<kN$ |
| `theta_lt_sharp` | $\theta(k)<\log N+1/(k-1)$ — Proposition 2 |
| `upper_unconditional` | $L(n)\le(1/\log2+o(1))\log n$, **no hypotheses** |
| `erdos_200_variants_upper` | `PNT →` $L(n)\le(1+o(1))\log n$ |

**The unconditional constant there is $1/\log 2 = 1.4427$, not $1$.** Mathlib does not
contain the prime number theorem; the sharpest Chebyshev-type lower bound it has is
`Chebyshev.theta_ge`, $\theta(n)\ge n\log2-\log(n+1)-2\sqrt n\log n$, whose leading
constant is $\log 2=0.693$. So the unconditional result *in that project* is 44 % weaker
than the literature. Recovering the literature constant needs $\theta(x)/x\to1$, which
appears in the development as a `def PNT : Prop`, an *assumed* hypothesis, proved nowhere
in `lean/`. Both results come from one transfer lemma, `eventually_longest_le`: any
$\theta(k)\ge(c-o(1))k$ gives $L(n)\le(1/c+o(1))\log n$.

### 9.1 Discharging the hypothesis

That hypothesis is no longer needed. Mathlib still has no PNT, but
[`PrimeNumberTheoremAnd`](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) (PNT+)
proves `chebyshev_asymptotic : θ ~[atTop] id`, which *is* `PNT`.
[`lean-pnt/`](lean-pnt/) bridges the two and obtains

$$\texttt{erdos\_200\_variants\_upper\_unconditional} \;:\; L(n)\le(1+o(1))\log n$$

with **no hypothesis** — DeepMind's statement, unconditionally, machine-checked. The
port cost exactly one identifier (`Set.mem_ofPred_eq` → `Set.mem_setOf_eq`, renamed in
Mathlib on 2026-07-09); `lean/` remains canonical and the shared modules are generated by
`lean-pnt/scripts/sync.sh`.

Two caveats, both structural:

* PNT+ pins Lean `v4.32.2` and `formal-conjectures` pins `v4.33.1`. Two Mathlib revisions
  cannot coexist in one Lake project, so `lean-pnt/` cannot depend on `formal-conjectures`
  and the `Expr`-level fidelity check of `lean/` is unavailable there. The definitions are
  copied verbatim into `FCShim.lean` and `scripts/check_shim.py` re-downloads
  `formal-conjectures` `main` and fails on any difference. That is a weaker guarantee than
  `Expr` identity, and is stated rather than glossed.
* PNT+ itself contains two `sorry`s, at `Wiener.lean:323` and `:342`. Both are dead code:
  `prelim_decay_2` is referenced nowhere, and `prelim_decay_3` only by `decay_alt`, which
  is also referenced nowhere across its 27 source files. That is a textual argument;
  `#assert_axioms chebyshev_asymptotic` is what settles it, reporting
  `[propext, Classical.choice, Quot.sound]`. For contrast `#print axioms prelim_decay_3`
  reports `sorryAx`, so the check is not vacuous.

Consequently **no result in this repository now depends on an unformalised hypothesis.**

### 9.2 Checking the checkers

Two mechanical checks run as part of `lean/verify.sh`:

1. **Axioms.** `#assert_axioms` walks the transitive dependency graph of each of the 20
   theorems with `Lean.collectAxioms` and errors if `sorryAx` appears. All 20 rest on
   exactly `{propext, Classical.choice, Quot.sound}`.
2. **Statement fidelity.** A `run_cmd` compares the elaborated `Expr` of the conclusion of
   `erdos_200_variants_upper`, with the `PNT` binder stripped, against the elaborated
   `Expr` of `Erdos200.erdos_200.variants.upper`. They are structurally identical. This
   check exists because check 1 cannot detect the failure that matters — a complete proof
   of the wrong statement.

A checker that has never failed is not evidence, so both were tested against planted
defects. A `sorry` in `primorial_lt_two_mul` propagated `sorryAx` to six downstream
theorems and failed the build; a `sorry` in `primorial_dvd` made `verify.sh` exit 1; and
reassociating the conclusion to `log n * (1 + o n)` — mathematically identical, and still
fully proved — was rejected by check 2 with `statement mismatch`. `lean-pnt/verify.sh`
was tested the same way: altering `n < l` to `n ≤ l` in the copied `IsAPOfLengthWith`, and
merging two non-contiguous declarations into one verbatim block, each made
`check_shim.py` exit 1 with the offending line flagged.

### 9.3 What this does not establish

Nothing about the open question. Erdős 200 asks whether
$L(N)=o(\log N)$; §5 argues the answer is conjecturally yes with decay $2/\log\log N$, and
that remains a heuristic. The formalisation covers the known upper bound only. It is also
not a new mathematical argument: it is Proposition 2 plus Chebyshev, transcribed, and the
unconditional form now leans on PNT+, which is someone else's formalisation of someone
else's theorem.

It also does **not** close the `sorry` upstream. `formal-conjectures` depends on Mathlib
alone, and Mathlib has no PNT, so `lean-pnt/`'s proof cannot be submitted there as-is. It
becomes submittable when either PNT+ updates to Lean `v4.33.1` or Mathlib absorbs the
prime number theorem. Until then the unconditional result lives here, not upstream.

## 10. Reproducing

```sh
cc -O3 -march=native -funroll-loops -pthread -o src/apsearch src/apsearch.c
sh refs/fetch.sh                      # re-download the primary sources
python src/verify_records.py          # 26 records, 4 independent checks
python src/ref_bruteforce.py          # assumption-free reference
./src/apsearch 20 572945039351 10    # ~67 min on 10 threads
python src/heuristic.py               # singular series vs exact counts
python src/compare_counts.py          # measured vs predicted, 30 points
python src/calibration.py             # KS test of the Poisson model
python src/barrier.py                 # the sieve barrier
python src/analysis.py                # Tables 1 and 2
python src/final_check.py             # re-derives every claim above; exit 0 = pass
bash lean/verify.sh                   # Lean: axiom audit + statement fidelity; exit 0 = pass
bash lean-pnt/verify.sh               # Lean: same bound with no PNT hypothesis; exit 0 = pass
```

`lean-pnt/verify.sh` builds `PrimeNumberTheoremAnd` from source. Measured cold: 3708 jobs
in 3 min 17 s, and 3717 jobs for the full project, on the same machine. It also re-fetches
`formal-conjectures` `main` over the network to run `scripts/check_shim.py`, so it needs
connectivity; `lean/verify.sh` does not.

Timings on 10 threads (5 performance cores, Apple silicon): $k=17$ to $2\times10^{10}$,
139 s; $k=18$ to $3\times10^{10}$, 291 s; $k=19$ to $1.5\times10^{11}$, 390 s; $k=20$ to
$5.73\times10^{11}$, 4027 s. Cost scales as $\varphi(W_k)M^2/(2(k-1)\cdot64)$
word-operations at roughly $4.9\times10^7$ per core-second, which is what makes
$k\ge21$ impractical here. These are wall times on an otherwise idle machine; the
$k\le16$ runs were re-measured later under heavy competing load and took up to
$14\times$ longer, so treat any single timing as indicative only.
