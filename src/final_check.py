"""final_check.py -- re-derive every claim in NOTES.md from the stored artifacts.

This is the trusted validation path.  It shares no code with apsearch.c and does not
use heuristic.py; it re-tests primality independently, re-checks the structure theorem
against all 26 known records, re-checks the rigorous upper bound against them, and
re-derives the range of N over which L(N) has been independently determined here.

Exit code is nonzero if any check fails.
"""
import json
import math
import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
FAIL = []


def check(name, cond, detail=""):
    print("  [%s] %s%s" % ("ok" if cond else "FAIL", name, ("  " + detail) if detail else ""))
    if not cond:
        FAIL.append(name)


def is_prime(n):
    """Deterministic Miller-Rabin for n < 3.3e24 (first 13 primes as bases)."""
    if n < 2:
        return False
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41):
        if n % p == 0:
            return n == p
    d, r = n - 1, 0
    while d % 2 == 0:
        d //= 2
        r += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41):
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            continue
        for _ in range(r - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def primes_upto(n):
    s = bytearray([1]) * (n + 1)
    s[0:2] = b"\x00\x00"
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]:
            s[i * i::i] = bytearray(len(s[i * i::i]))
    return [i for i in range(n + 1) if s[i]]


def primorial(k):
    r = 1
    for p in primes_upto(k):
        r *= p
    return r


def main():
    recs = json.load(open(os.path.join(ROOT, "data", "records.json")))
    a = {r["k"]: r["a_k"] for r in recs}
    first = {r["k"]: r["first"] for r in recs}
    diff = {r["k"]: r["diff"] for r in recs}

    print("A. the 26 records are genuine k-APs of distinct primes")
    allok = True
    for r in recs:
        k, f, d, last = r["k"], r["first"], r["diff"], r["a_k"]
        terms = [f + i * d for i in range(k)]
        ok = (terms[-1] == last and len(set(terms)) == k
              and all(is_prime(t) for t in terms))
        allok &= ok
        if not ok:
            print("     k=%d FAILED" % k)
    check("all 26 records verified by independent Miller-Rabin", allok)
    check("a(k) strictly increasing", all(a[k] < a[k + 1] for k in range(1, 26)))

    print("\nB. structure theorem (Prop. 1) holds for every record with k >= 3")
    allok = True
    for k in range(3, 27):
        f, d, W = first[k], diff[k], primorial(k)
        caseA = (f > k) and (d % W == 0)
        caseB = (is_prime(k) and f == k and d % (W // k) == 0)
        if not (caseA ^ caseB):
            allok = False
            print("     k=%d: caseA=%s caseB=%s  (f=%d d=%d W=%d)" % (k, caseA, caseB, f, d, W))
    check("every record is exactly one of Case A / Case B", allok)
    cb = [k for k in range(3, 27) if first[k] == k]
    check("Case B records identified", cb == [3, 5, 7], "k = %s" % cb)

    print("\nC. rigorous upper bound (Prop. 2) is satisfied by every record")
    allok = True
    for k in range(3, 27):
        W = primorial(k)
        nxt = next(p for p in range(k + 1, 4 * k) if is_prime(p))
        lb = nxt + (k - 1) * W
        if is_prime(k):
            lb = min(lb, k + (k - 1) * (W // k))
        if a[k] < lb:
            allok = False
            print("     k=%d: a(k)=%d < lower bound %d" % (k, a[k], lb))
    check("a(k) >= min_last_lower_bound(k) for k=3..26", allok)

    # the weaker but cleaner form: W_k <= a(k) * k/(k-1)
    allok = all(primorial(k) <= a[k] * k / (k - 1) for k in range(3, 27))
    check("W_k <= a(k)*k/(k-1)  (i.e. theta(L) <= log N + 1/(L-1))", allok)

    print("\nD. range over which L(N) is independently determined by this work")
    runs = {}
    for fn in os.listdir(os.path.join(ROOT, "results")):
        if not fn.endswith(".json"):
            continue
        try:
            d = json.load(open(os.path.join(ROOT, "results", fn)))
        except Exception:
            continue
        if isinstance(d, dict) and "B" in d and "min_last" in d:
            k = d["k"]
            if k not in runs or d["B"] > runs[k]["B"]:
                runs[k] = d
    for k in sorted(runs):
        r = runs[k]
        check("exhaustive k=%d to B=%d reproduces a(%d)" % (k, r["B"], k),
              r["min_last"] == a[k], "found %d" % r["min_last"])

    # ref_bruteforce.py is assumption-free (no structure theorem, no shared code)
    ref = json.load(open(os.path.join(ROOT, "results", "reference.json")))
    for ks, r in sorted(ref.items(), key=lambda t: int(t[0])):
        k = int(ks)
        check("brute force k=%d to B=%d reproduces a(%d)" % (k, r["B"], k),
              r["min_last"] == a[k], "found %d" % r["min_last"])

    kmax = max(runs)
    enum_total = sum(r["total"] for k, r in runs.items() if k >= 8)
    enum_caseB = sum(r["caseB_count"] for k, r in runs.items() if k >= 8)
    check("no Case B progression among the %d enumerated for k>=8" % enum_total,
          enum_caseB == 0, "caseB total %d" % enum_caseB)
    # A (k+1)-AP with last term <= B contains two k-APs with last term <= B
    # (terms 1..k and terms 2..k+1), so total == 1 rules out any (k+1)-AP <= B.
    top = runs[kmax]
    check("k=%d run has total==1, so no %d-AP exists below B=%d"
          % (kmax, kmax + 1, top["B"]), top["total"] == 1)
    verified_to = top["B"]
    covered = set(runs) | {int(x) for x in ref}
    missing = [k for k in range(3, kmax + 1) if k not in covered]
    check("a(k) reproduced by some run for every k in 3..%d" % kmax,
          not missing, "missing: %s" % missing if missing else "no gaps")
    print("\n  => L(N) independently re-derived for all N <= %d  (%.3g)"
          % (verified_to, verified_to))
    print("     L(N) = max{k : a(k) <= N}; beyond this range a(%d)..a(26) are cited,"
          % (kmax + 1))
    print("     not recomputed here, and L(N) is unknown for N >= a(27).")

    print("\nE. extremal ratio")
    rows = [(k, a[k], k / math.log(a[k])) for k in range(3, 27)]
    best = max(rows, key=lambda r: r[2])
    print("     max k/log a(k) over 3<=k<=26 = %.4f at k=%d" % (best[2], best[0]))
    print("     value at k=26                = %.4f" % rows[-1][2])
    check("ratio at k=26 is below 0.71", rows[-1][2] < 0.71, "%.4f" % rows[-1][2])

    print("\nF. Hardy-Littlewood model vs exhaustively measured counts")
    cpath = os.path.join(ROOT, "results", "count_comparison.json")
    if not os.path.exists(cpath):
        check("count_comparison.json present", False, "missing")
    else:
        comp = json.load(open(cpath))
        # Re-derive the measured column straight from the raw histograms, with a
        # cumulative sum written independently of src/compare_counts.py.  The
        # histogram keys are bucket LOWER edges, so every bucket with lo <= N
        # lies entirely at or below N.
        raw, bad = {}, []
        for k in sorted({int(r["k"]) for r in comp}):
            f = os.path.join(ROOT, "results", "count_k%d.json" % k)
            raw[k] = json.load(open(f))
        for r in comp:
            k, N = int(r["k"]), float(r["N"])
            tot = sum(v for lo, v in raw[k]["hist"].items() if float(lo) <= N)
            if tot != int(r["measured"]):
                bad.append((k, N, tot, r["measured"]))
        check("measured counts re-derived from raw histograms",
              not bad, "%d rows, %d mismatched" % (len(comp), len(bad)))
        # each k's largest tabulated N must recover that run's own total
        tot_bad = [k for k in raw
                   if max((int(r["measured"]) for r in comp if int(r["k"]) == k),
                          default=-1) != raw[k]["total"]]
        check("largest N per k recovers the run total", not tot_bad, str(tot_bad))

        ratios = [r["predicted"] / r["measured"] for r in comp]
        lg = [math.log(x) for x in ratios]
        gm = math.exp(sum(lg) / len(lg))
        gsd = math.exp(math.sqrt(sum((x - math.log(gm)) ** 2 for x in lg) / (len(lg) - 1)))
        ks = sorted({int(r["k"]) for r in comp})
        print("     %d points, k=%d..%d, N=%.3g..%.3g, measured %d..%d"
              % (len(comp), ks[0], ks[-1],
                 min(r["N"] for r in comp), max(r["N"] for r in comp),
                 min(int(r["measured"]) for r in comp),
                 max(int(r["measured"]) for r in comp)))
        print("     geometric mean pred/obs = %.4f, geometric sd = %.4f, range %.4f..%.4f"
              % (gm, gsd, min(ratios), max(ratios)))
        # the claim made in NOTES.md section 4
        check("geometric mean within 3% of 1", abs(gm - 1.0) < 0.03, "%.4f" % gm)
        check("every point within 15% of prediction",
              max(max(ratios), 1 / min(ratios)) < 1.15,
              "worst %.4f" % max(max(ratios), 1 / min(ratios)))
        check("no Case B progression found in any counting run",
              all(int(r["caseB"]) == 0 for r in comp)
              and all(v["caseB_count"] == 0 for v in raw.values()), "")

    print("\n%s" % ("ALL CHECKS PASSED" if not FAIL else "FAILURES: %s" % FAIL))
    return 1 if FAIL else 0


if __name__ == "__main__":
    sys.exit(main())
