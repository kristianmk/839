/-
Simple673/Local/Checker.lean — the executable branch-and-bound checker for the eight-point
local inequality (second window, clipping level `c = 2`).

This file imports nothing (core Lean only), so that it can be compiled to native code
(`precompileModules`) and evaluated by `native_decide` at native speed. It contains definitions
only; the soundness proof is in `Simple673/Local/Soundness.lean` and the files it imports.
The check exists in two forms with the same search: `checkAll` (one thread) and `checkAllPar`
(the search cut into parts that are evaluated as tasks).

The algorithm is that of `Distinct839/Local/Checker.lean`, with frames of eight points in place
of seven, and of the reference verifier `verifier/verify.cpp` of the accompanying files, built
for eight points (the reference run for the present data is that program on
`certificate_line/inputs.json`). Against `Distinct839` the sizes of the arrays, the index
formulas and the bounds of the loops are those of eight points, seven gaps and `28` pairs, and
the constants and the frozen tables are those of the present certificate. Conventions:

* a gap is `x / H` with `H = 16384`; a box is a pair `lo hi : Array Nat` of seven entries, read
  with default `0`;
* `tab[k]` is a lower bound for `V · K(t)²` on the cell `[k/H, (k+1)/H]`, `V = 2²⁸`; a read out
  of range gives `0`, which is also a lower bound;
* coefficients are in units of `10⁻⁶`, and every tested quantity is twice the local inequality
  multiplied by `10⁶ · V`;
* all arithmetic is in `Nat`. A signed quantity is a pair `SInt = (p, n)` meaning `p - n`.
  (Lean's `Int` leaves the fast scalar representation at `2³¹`, `Nat` only at `2⁶³`.)

Labels. The general format of the certificate has two labels per site (`0`, `1`), three pair
types (`0`, `1`, `2` = sum of the two labels) and `2⁸ = 256` labelings. The present certificate
is label-blind: the pair weights, the site rewards and the potentials are the same for every
label, and the statement `Simple673.LocalInequality` has no labels. The checker keeps the general
format and its arrays hold the label-blind data once per type, exactly as the reference run
(its data file repeats each table). So it makes the decisions of the reference run: the label
penalty is `0`, and the tests for the `256` labelings all agree with the test for labeling `0`.
The soundness proof uses the labeling `0` only (`Simple673/Local/Bridge.lean`).
-/

namespace Simple673
namespace Local

/-! ## Signed integers as differences of naturals -/

/-- A signed integer `p - n`, stored as two naturals. -/
structure SInt where
  /-- positive part -/
  p : Nat
  /-- negative part -/
  n : Nat

namespace SInt

/-- The integer represented by a pair. -/
def toInt (a : SInt) : Int := (a.p : Int) - (a.n : Int)

@[inline] def zero : SInt := ⟨0, 0⟩
@[inline] def ofNat (a : Nat) : SInt := ⟨a, 0⟩
@[inline] def add (a b : SInt) : SInt := ⟨a.p + b.p, a.n + b.n⟩
@[inline] def sub (a b : SInt) : SInt := ⟨a.p + b.n, a.n + b.p⟩
/-- multiplication by a natural number -/
@[inline] def smul (a : SInt) (c : Nat) : SInt := ⟨a.p * c, a.n * c⟩
/-- `a ≤ b` -/
@[inline] def le (a b : SInt) : Bool := decide (a.p + b.n ≤ b.p + a.n)
@[inline] def min (a b : SInt) : SInt := if a.le b then a else b

end SInt

/-! ## Small loops -/

/-- `∑_{k < n} f k` -/
@[specialize] def sumTo (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumTo f n + f n

/-- `∑_{k < n} f k` for signed values -/
@[specialize] def ssumTo (f : Nat → SInt) : Nat → SInt
  | 0 => SInt.zero
  | n + 1 => (ssumTo f n).add (f n)

/-- `p m ∧ p (m+1) ∧ … ∧ p (m+n-1)`, evaluated in this order, stopping at the first failure. -/
@[specialize] def allFromTo (p : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => true
  | n + 1, m => p m && allFromTo p n (m + 1)

/-- entry `r` of a box side, `0` if out of range -/
@[inline] def g (a : Array Nat) (r : Nat) : Nat := a.getD r 0

/-! ## Constants and frozen tables (units of `10⁻⁶`) -/

/-- last cell of the kernel table -/
def cR : Nat := 262143
/-- value scale `V = 2²⁸` -/
def cV : Nat := 268435456
/-- lower end of the root box, `13926 / 16384 < 17/20` -/
def cLo : Nat := 13926
/-- pressure per grid step: `10⁶ α · V / H = 627 · 16384` -/
def cP : Nat := 10272768
/-- `∑ h_{i,1}`: the sum of the site rewards for label `0` (`= 10⁶ x₁`) -/
def cH1 : Nat := 8722
/-- `∑ h_{i,2}`: the sum of the site rewards for label `1` (the same number: label-blind data) -/
def cH2 : Nat := 8722
/-- bound for the total negative part of the seven potentials
(`0 + 0 + 425 + 444 + 425 + 0 + 0`) -/
def cBudget : Nat := 1294

/-- pair weights, index `t * 64 + i * 8 + j` (zero unless `i < j`); the three blocks `t = 0, 1, 2`
are equal -/
def wArr : Array Nat := #[
    0, 159939, 0, 280438, 143766, 709387, 1000000, 2000000,
    0, 0, 264496, 385569, 340591, 856233, 581225, 1000000,
    0, 0, 0, 389188, 614430, 757940, 856233, 709387,
    0, 0, 0, 0, 372750, 614430, 340591, 143766,
    0, 0, 0, 0, 0, 389188, 385569, 280438,
    0, 0, 0, 0, 0, 0, 264496, 0,
    0, 0, 0, 0, 0, 0, 0, 159939,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 159939, 0, 280438, 143766, 709387, 1000000, 2000000,
    0, 0, 264496, 385569, 340591, 856233, 581225, 1000000,
    0, 0, 0, 389188, 614430, 757940, 856233, 709387,
    0, 0, 0, 0, 372750, 614430, 340591, 143766,
    0, 0, 0, 0, 0, 389188, 385569, 280438,
    0, 0, 0, 0, 0, 0, 264496, 0,
    0, 0, 0, 0, 0, 0, 0, 159939,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 159939, 0, 280438, 143766, 709387, 1000000, 2000000,
    0, 0, 264496, 385569, 340591, 856233, 581225, 1000000,
    0, 0, 0, 389188, 614430, 757940, 856233, 709387,
    0, 0, 0, 0, 372750, 614430, 340591, 143766,
    0, 0, 0, 0, 0, 389188, 385569, 280438,
    0, 0, 0, 0, 0, 0, 264496, 0,
    0, 0, 0, 0, 0, 0, 0, 159939,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- pair weight of type `t` for the sites `i < j` -/
@[inline] def wT (t i j : Nat) : Nat := wArr.getD (t * 64 + i * 8 + j) 0

/-- site rewards for label `0` -/
def h0Arr : Array Nat := #[0, 0, 0, 8722, 0, 0, 0, 0]
/-- site rewards for label `1` (the same) -/
def h1Arr : Array Nat := #[0, 0, 0, 8722, 0, 0, 0, 0]

/-- site reward for label `a` at site `i` -/
@[inline] def hT (a i : Nat) : Nat := if a = 0 then h0Arr.getD i 0 else h1Arr.getD i 0

/-- positive parts of the knot values, index `(r * 3 + t) * 14 + k`; the three rows `t = 0, 1, 2`
of each position `r` are equal -/
def kpArr : Array Nat := #[
    0, 647, 555, 518, 647, 647, 647, 0, 0, 270, 325, 0, 647, 0,
    0, 647, 555, 518, 647, 647, 647, 0, 0, 270, 325, 0, 647, 0,
    0, 647, 555, 518, 647, 647, 647, 0, 0, 270, 325, 0, 647, 0,
    0, 0, 91, 45, 0, 0, 0, 0, 0, 86, 58, 0, 0, 0,
    0, 0, 91, 45, 0, 0, 0, 0, 0, 86, 58, 0, 0, 0,
    0, 0, 91, 45, 0, 0, 0, 0, 0, 86, 58, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 221, 221, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 221, 221, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 221, 221, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 850, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 850, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 850, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 221, 221, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 221, 221, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 221, 221, 0, 0, 0, 0, 0,
    0, 0, 91, 45, 0, 0, 0, 0, 0, 86, 58, 0, 0, 0,
    0, 0, 91, 45, 0, 0, 0, 0, 0, 86, 58, 0, 0, 0,
    0, 0, 91, 45, 0, 0, 0, 0, 0, 86, 58, 0, 0, 0,
    0, 647, 555, 518, 647, 647, 647, 0, 0, 270, 325, 0, 647, 0,
    0, 647, 555, 518, 647, 647, 647, 0, 0, 270, 325, 0, 647, 0,
    0, 647, 555, 518, 647, 647, 647, 0, 0, 270, 325, 0, 647, 0]

/-- negative parts of the knot values, index `(r * 3 + t) * 14 + k` -/
def knArr : Array Nat := #[
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 425, 425, 342, 425, 425, 425, 0, 0, 275, 244, 425, 425, 0,
    0, 425, 425, 342, 425, 425, 425, 0, 0, 275, 244, 425, 425, 0,
    0, 425, 425, 342, 425, 425, 425, 0, 0, 275, 244, 425, 425, 0,
    0, 444, 442, 442, 444, 444, 444, 442, 442, 162, 278, 0, 444, 0,
    0, 444, 442, 442, 444, 444, 444, 442, 442, 162, 278, 0, 444, 0,
    0, 444, 442, 442, 444, 444, 444, 442, 442, 162, 278, 0, 444, 0,
    0, 425, 425, 342, 425, 425, 425, 0, 0, 275, 244, 425, 425, 0,
    0, 425, 425, 342, 425, 425, 425, 0, 0, 275, 244, 425, 425, 0,
    0, 425, 425, 342, 425, 425, 425, 0, 0, 275, 244, 425, 425, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- knot value `k` of the potential at position `r` for pair type `t` -/
@[inline] def knot (r t k : Nat) : SInt :=
  ⟨kpArr.getD ((r * 3 + t) * 14 + k) 0, knArr.getD ((r * 3 + t) * 14 + k) 0⟩

/-! ## Range minima of the kernel table -/

/-- One doubling step of the sparse table: entry `i` becomes `min prev[i] prev[i + s]`. -/
def nextLevel (prev : Array Nat) (s : Nat) : Array Nat :=
  Array.ofFn (n := prev.size) fun i => min (prev.getD i.val 0) (prev.getD (i.val + s) 0)

/-- `sparseAux n k cur acc` appends the levels `k, …, k + n - 1`, where `cur` is level `k`. -/
def sparseAux : Nat → Nat → Array Nat → Array (Array Nat) → Array (Array Nat)
  | 0, _, _, acc => acc
  | n + 1, k, cur, acc => sparseAux n (k + 1) (nextLevel cur (2 ^ k)) (acc.push cur)

/-- The sparse table: level `k` at index `i` is the minimum of `tab[i], …, tab[i + 2^k - 1]`
(entries beyond the end of the table count as `0`). There are eighteen levels, `k = 0, …, 17`.
The table has `262144 = 2¹⁸` entries, so a query over the full length `2¹⁸` would ask for
level `18`, which is absent; `rmin` then reads `0`, which is a valid lower bound. This does not
occur in the search: every pair distance is at least `13926` cells, so a query has length at
most `262144 - 13926 < 2¹⁸` and uses a level `≤ 17`. -/
def sparse (tab : Array Nat) : Array (Array Nat) := sparseAux 18 0 tab #[]

/-- A lower bound for (in fact the minimum of) `tab[l], …, tab[r]`, for `l ≤ r`. -/
@[inline] def rmin (sp : Array (Array Nat)) (l r : Nat) : Nat :=
  let k := (r + 1 - l).log2
  let lev := sp.getD k #[]
  min (lev.getD l 0) (lev.getD (r + 1 - 2 ^ k) 0)

/-! ## The piecewise linear potentials on the integer grid

Knot `k` is at `12288 + 2048 k` (that is `3/4 + k/8`), `k = 0, …, 13`; the last knot is `38912`.
Values are scaled by `10⁶ · V`. -/

/-- `10⁶ V · B_r^t(x / H)` for an integer `x`. -/
def bv (r t x : Nat) : SInt :=
  if x ≤ 12288 ∨ 38912 ≤ x then SInt.zero else
    let k := (x - 12288) / 2048
    let q := (x - 12288) % 2048
    (((knot r t k).smul (2048 - q)).add ((knot r t (k + 1)).smul q)).smul 131072

/-- Loop of `pmin` over the knots `j - 1, …, 0`. -/
@[specialize] def pminLoop (f : Nat → SInt) (lo hi : Nat) : Nat → SInt → SInt
  | 0, acc => acc
  | j + 1, acc =>
    let x := 12288 + j * 2048
    pminLoop f lo hi j (if lo < x ∧ x < hi then SInt.min acc (f x) else acc)

/-- Minimum of `f` over the two end points `lo`, `hi` and the knots strictly between them. For a
function that is linear between consecutive knots this is its minimum over `[lo, hi]`. -/
@[specialize] def pmin (f : Nat → SInt) (lo hi : Nat) : SInt :=
  pminLoop f lo hi 14 (SInt.min (f lo) (f hi))

/-- An affine function `x ↦ s · x + o`. -/
structure Aff where
  /-- slope -/
  s : SInt
  /-- intercept -/
  o : SInt

/-- The slope of `10⁶ V · B_r^t` (per grid step) on the linear piece containing the midpoint of
`[lo, hi]` (`0` outside the knots). -/
def pslope (r t lo hi : Nat) : SInt :=
  let mid := (lo + hi) / 2
  if 12288 < mid ∧ mid < 38912 then
    let k := (mid - 12288) / 2048
    ((knot r t (k + 1)).sub (knot r t k)).smul 131072
  else SInt.zero

/-- Twice an affine lower support of `10⁶ V · B_r^t` on `[lo, hi]`: the slope is `pslope`, the
intercept is the exact minimum of the difference. -/
def paff (r t lo hi : Nat) : Aff :=
  let s := pslope r t lo hi
  ⟨s.smul 2, (pmin (fun x => (bv r t x).sub (s.smul x)) lo hi).smul 2⟩

/-! ## Data of a pair of sites on a box -/

/-- Cell range and kernel bound for a pair `i < j`. -/
structure Edge where
  /-- first cell that the distance can reach -/
  ls : Nat
  /-- last cell that the distance can reach -/
  hs : Nat
  /-- lower bound for `V K²` over these cells -/
  kv : Nat

/-- The edge data of the pair `i < j` on the box `lo hi`, where `total = ∑ lo` and distances
are cut at `R - (total - l)` (larger ones are covered by the pressure term). -/
def mkEdge (sp : Array (Array Nat)) (lo hi : Array Nat) (total i j : Nat) : Edge :=
  let l := sumTo (fun k => g lo (i + k)) (j - i)
  let h := min (sumTo (fun k => g hi (i + k)) (j - i)) (cR + l - total)
  let last := max l (h - 1)
  ⟨l, last, rmin sp l last⟩

/-- Edge data for all pairs, index `i * 8 + j`. -/
def edges (sp : Array (Array Nat)) (lo hi : Array Nat) (total : Nat) : Array Edge :=
  Array.ofFn (n := 64) fun q =>
    if q.val / 8 < q.val % 8 then mkEdge sp lo hi total (q.val / 8) (q.val % 8) else ⟨0, 0, 0⟩

@[inline] def edAt (ed : Array Edge) (i j : Nat) : Edge := ed.getD (i * 8 + j) ⟨0, 0, 0⟩

/-! ## The test for all labelings at once -/

/-- Minima of the potentials over the box, index `r * 3 + t`: for `t = 0` of `B_r^0`, for
`t = 1, 2` of the difference `B_r^t - B_r^0`. -/
def bmArr (lo hi : Array Nat) : Array SInt :=
  Array.ofFn (n := 21) fun q =>
    let r := q.val / 3
    let t := q.val % 3
    if t = 0 then pmin (bv r 0) (g lo r) (g hi r)
    else pmin (fun x => (bv r t x).sub (bv r 0 x)) (g lo r) (g hi r)

@[inline] def bmAt (bm : Array SInt) (r t : Nat) : SInt := bm.getD (r * 3 + t) SInt.zero

/-- `η_e = min(2 u_e, v_e)` for the pair `i < j`: a lower bound for the cost of raising one
label of the pair, and for half the cost of raising both. -/
def incOf (ed : Array Edge) (bm : Array SInt) (i j : Nat) : SInt :=
  let kv := (edAt ed i j).kv
  let a := SInt.ofNat (2 * (wT 1 i j - wT 0 i j) * kv)
  let b := SInt.ofNat ((wT 2 i j - wT 0 i j) * kv)
  if j = i + 1 then SInt.min (a.add ((bmAt bm i 1).smul 2)) (b.add (bmAt bm i 2))
  else SInt.min a b

/-- `η` for all pairs, index `i * 8 + j`. -/
def incArr (ed : Array Edge) (bm : Array SInt) : Array SInt :=
  Array.ofFn (n := 64) fun q =>
    if q.val / 8 < q.val % 8 then incOf ed bm (q.val / 8) (q.val % 8) else SInt.zero

@[inline] def incAt (inc : Array SInt) (i j : Nat) : SInt := inc.getD (i * 8 + j) SInt.zero

/-- `∑_i min(0, ∑_{e ∋ i} η_e - 2 V (h_{i,2} - h_{i,1}))`: the most that raising labels can cost
(`0` for label-blind data). -/
def penalty (inc : Array SInt) : SInt :=
  ssumTo (fun i =>
    let deg := ssumTo (fun j =>
      if i < j then incAt inc i j else if j < i then incAt inc j i else SInt.zero) 8
    SInt.min SInt.zero (deg.sub (SInt.ofNat (2 * (hT 1 i - hT 0 i) * cV)))) 8

/-- The lower bound for the labeling `0` from range minima: pressure at the lower corner,
kernel minima, potential minima. -/
def baseOf (total : Nat) (ed : Array Edge) (bm : Array SInt) : SInt :=
  (SInt.ofNat (total * cP
      + sumTo (fun j => sumTo (fun i => wT 0 i j * (edAt ed i j).kv) j) 8)).add
    (ssumTo (fun r => bmAt bm r 0) 7)

/-! ## Affine supports -/

/-- `min acc (min_{t < n} (2 tab[k - t] + c + s t))` -/
def cellMinDown (tab : Array Nat) (s : Nat) : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, acc => acc
  | n + 1, k, c, acc => cellMinDown tab s n (k - 1) (c + s) (min acc (2 * tab.getD k 0 + c))

/-- `min acc (min_{t < n} (2 tab[k + t] + c + s t))` -/
def cellMinUp (tab : Array Nat) (s : Nat) : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, acc => acc
  | n + 1, k, c, acc => cellMinUp tab s n (k + 1) (c + s) (min acc (2 * tab.getD k 0 + c))

/-- An affine lower support `d ↦ s d + o` of `2 V K(d/H)²` over the cells of an edge: the slope
is the central difference of the table at the middle cell, and the intercept is
`min_k (2 tab[k] - max(s k, s (k+1)))`. -/
def kaff (tab : Array Nat) (e : Edge) : Aff :=
  let mid := (e.ls + e.hs) / 2
  let a := if mid = 0 ∨ cR ≤ mid then 0 else tab.getD (mid + 1) 0
  let b := if mid = 0 ∨ cR ≤ mid then 0 else tab.getD (mid - 1) 0
  let n := e.hs + 1 - e.ls
  if b ≤ a then
    let s := a - b
    ⟨⟨s, 0⟩, ⟨cellMinDown tab s n e.hs 0 (2 * tab.getD e.hs 0), s * (e.hs + 1)⟩⟩
  else
    let s := b - a
    ⟨⟨0, s⟩, ⟨cellMinUp tab s n e.ls (s * e.ls) (2 * tab.getD e.ls 0 + s * e.ls), 0⟩⟩

/-- Kernel supports for all pairs, index `i * 8 + j`. -/
def affArr (tab : Array Nat) (ed : Array Edge) : Array Aff :=
  Array.ofFn (n := 64) fun q =>
    if q.val / 8 < q.val % 8 then kaff tab (edAt ed (q.val / 8) (q.val % 8))
    else ⟨SInt.zero, SInt.zero⟩

/-- Weighted slopes `W^t_{ij} s_{ij}`, index `t * 64 + i * 8 + j`. -/
def wkArr (af : Array Aff) : Array SInt :=
  Array.ofFn (n := 192) fun q =>
    ((af.getD (q.val % 64) ⟨SInt.zero, SInt.zero⟩).s).smul (wArr.getD q.val 0)

/-- Weighted intercepts `W^t_{ij} o_{ij}`, index `t * 64 + i * 8 + j`. -/
def woArr (af : Array Aff) : Array SInt :=
  Array.ofFn (n := 192) fun q =>
    ((af.getD (q.val % 64) ⟨SInt.zero, SInt.zero⟩).o).smul (wArr.getD q.val 0)

@[inline] def w3At (a : Array SInt) (t i j : Nat) : SInt := a.getD (t * 64 + i * 8 + j) SInt.zero

/-- Doubled potential supports, index `r * 3 + t`. -/
def paArr (lo hi : Array Nat) : Array Aff :=
  Array.ofFn (n := 21) fun q => paff (q.val / 3) (q.val % 3) (g lo (q.val / 3)) (g hi (q.val / 3))

@[inline] def paAt (pa : Array Aff) (r t : Nat) : Aff := pa.getD (r * 3 + t) ⟨SInt.zero, SInt.zero⟩

/-- label of site `i` in the labeling coded by `m` -/
@[inline] def bit (m i : Nat) : Nat := (m >>> i) % 2

/-- The minimum over the box of the affine lower bound for labeling `m` (without the reward):
intercept plus, for each gap, the linear coefficient times the lower or upper end. -/
def valOf (lo hi : Array Nat) (wk wo : Array SInt) (pa : Array Aff) (m : Nat) : SInt :=
  let inter :=
    (ssumTo (fun r => (paAt pa r (bit m r + bit m (r + 1))).o) 7).add
      (ssumTo (fun j => ssumTo (fun i => w3At wo (bit m i + bit m j) i j) j) 8)
  inter.add (ssumTo (fun r =>
    let lin := ((SInt.ofNat (2 * cP)).add (paAt pa r (bit m r + bit m (r + 1))).s).add
      (ssumTo (fun i => ssumTo (fun k =>
        w3At wk (bit m i + bit m (r + 1 + k)) i (r + 1 + k)) (7 - r)) (r + 1))
    if lin.n ≤ lin.p then lin.smul (g lo r) else lin.smul (g hi r)) 7)

/-- twice the scaled reward of labeling `m` -/
def rhsOf (m : Nat) : Nat := 2 * cV * sumTo (fun i => hT (bit m i) i) 8

/-- The affine tests: first for all labelings at once (labeling `0` plus penalty), then
one labeling at a time. (For label-blind data the penalty is `0`, so the first test is the test
for the labeling `0`, and the loop stops at its first step if that test fails.) -/
def affineOK (tab : Array Nat) (lo hi : Array Nat) (ed : Array Edge) (pen : SInt) : Bool :=
  let af := affArr tab ed
  let wk := wkArr af
  let wo := woArr af
  let pa := paArr lo hi
  (SInt.ofNat (2 * cH1 * cV)).le ((valOf lo hi wk wo pa 0).add pen) ||
    allFromTo (fun m => (SInt.ofNat (rhsOf m)).le (valOf lo hi wk wo pa m)) 256 0

/-! ## One node of the search -/

/-- Upper ends cut at `∑ x ≤ R`: `hi_r ← min(hi_r, R - (total - lo_r))`. -/
def clamp (lo hi : Array Nat) (total : Nat) : Array Nat :=
  Array.ofFn (n := 7) fun r => min (g hi r.val) (cR + g lo r.val - total)

/-- Width and index of the first widest gap among the first `n`. -/
def widest (lo hi : Array Nat) : Nat → Nat × Nat
  | 0 => (0, 0)
  | n + 1 =>
    let ws := widest lo hi n
    if ws.1 < g hi n - g lo n then (g hi n - g lo n, n) else ws

/-- Result of the tests on one box. -/
inductive Verdict where
  /-- the inequality holds on the box (`stage`: `0` pressure, `1` range minima, `2` affine) -/
  | ok (stage : Nat)
  /-- a box of width one that no test accepts -/
  | fail
  /-- split gap `r` at `mid`; `hi'` is the clamped upper corner -/
  | split (hi' : Array Nat) (r mid : Nat)

/-- The tests on the box `lo hi`. -/
def node (tab : Array Nat) (sp : Array (Array Nat)) (lo hi : Array Nat) : Verdict :=
  let total := sumTo (g lo) 7
  if (cH2 + cBudget) * cV ≤ total * cP then .ok 0 else
  let hi' := clamp lo hi total
  let ed := edges sp lo hi' total
  let bm := bmArr lo hi'
  let pen := penalty (incArr ed bm)
  if (SInt.ofNat (2 * cH1 * cV)).le (((baseOf total ed bm).smul 2).add pen) then .ok 1 else
  let ws := widest lo hi' 7
  if ws.1 ≤ 512 && affineOK tab lo hi' ed pen then .ok 2 else
  if ws.1 ≤ 1 then .fail else .split hi' ws.2 ((g lo ws.2 + g hi' ws.2) / 2)

/-! ## The search

The search is written for an arbitrary verdict function `nd`, and used with `nd = node tab sp`.
(Keeping `nd` abstract also keeps the unfolding lemmas of the recursion cheap to check.) -/

/-- Branch and bound on the box `lo hi`, with recursion depth at most `fuel`. -/
def searchBox (nd : Array Nat → Array Nat → Verdict) : Nat → Array Nat → Array Nat → Bool
  | 0, _, _ => false
  | fuel + 1, lo, hi =>
    match nd lo hi with
    | .ok _ => true
    | .fail => false
    | .split hi' r mid =>
      searchBox nd fuel lo (hi'.setIfInBounds r mid) &&
        searchBox nd fuel (lo.setIfInBounds r mid) hi'

/-- Follow `depth` splits chosen by the binary digits of `path` (lowest digit first; digit `0`
is the lower half), then run `searchBox`. A box accepted on the way counts as checked. -/
def searchPath (nd : Array Nat → Array Nat → Verdict) (fuel : Nat) :
    Nat → Nat → Array Nat → Array Nat → Bool
  | 0, _, lo, hi => searchBox nd fuel lo hi
  | depth + 1, path, lo, hi =>
    match nd lo hi with
    | .ok _ => true
    | .fail => false
    | .split hi' r mid =>
      if path % 2 = 0 then searchPath nd fuel depth (path / 2) lo (hi'.setIfInBounds r mid)
      else searchPath nd fuel depth (path / 2) (lo.setIfInBounds r mid) hi'

/-- lower corner of the root box -/
def rootLo : Array Nat := #[13926, 13926, 13926, 13926, 13926, 13926, 13926]
/-- upper corner of the root box -/
def rootHi : Array Nat := #[262143, 262143, 262143, 262143, 262143, 262143, 262143]

/-- Recursion depth allowed below the root box (below a chunk root, for `checkChunk`). Nothing
limits the number of boxes: both halves of a split get the remaining depth. For any table, a
path of the search from the root box has at most `7 · 18 = 126` splits, so the depth `127` is
enough: a gap of the root box has width below `2¹⁸`, a split replaces the width `w ≥ 2` of the
widest gap by `⌊w/2⌋` or `⌈w/2⌉`, and a box whose widest gap has width at most `1` is not
split. -/
def cFuel : Nat := 400

/-- Chunk `i` of `nChunks` at depth `depth`: the sub-boxes reached by the paths `p < 2^depth`
with `p % nChunks = i`. The chunks `i = 0, …, nChunks - 1` together cover the root box. -/
def checkChunk (tab : Array Nat) (depth nChunks i : Nat) : Bool :=
  let sp := sparse tab
  allFromTo (fun p => p % nChunks != i || searchPath (node tab sp) cFuel depth p rootLo rootHi)
    (2 ^ depth) 0

/-! ## The search in parallel parts

The same search, cut into parts that compiled code can evaluate on several threads. `frontier`
walks the boxes that the search reaches with fewer than `depth` splits and returns the boxes it
reaches after exactly `depth` splits; the searches below these boxes are dealt out to `parts`
parts (`checkPart`), and `checkAllPar` below starts one task for each part. -/

/-- The boxes that the search from `lo hi` reaches after exactly `depth` splits, put in front of
`acc` (the one found last comes first); `none` if a box with fewer splits fails. A box that is
accepted with fewer splits contributes nothing: it is checked. -/
def frontier (nd : Array Nat → Array Nat → Verdict) :
    Nat → Array Nat → Array Nat → List (Array Nat × Array Nat) →
      Option (List (Array Nat × Array Nat))
  | 0, lo, hi, acc => some ((lo, hi) :: acc)
  | depth + 1, lo, hi, acc =>
    match nd lo hi with
    | .ok _ => some acc
    | .fail => none
    | .split hi' r mid =>
      match frontier nd depth lo (hi'.setIfInBounds r mid) acc with
      | none => none
      | some acc' => frontier nd depth (lo.setIfInBounds r mid) hi' acc'

/-- `searchBox` on those boxes of a list whose number is `i` modulo `parts`; the boxes of the list
have the numbers `k, k + 1, …`. -/
def searchEvery (nd : Array Nat → Array Nat → Verdict) (parts i : Nat) :
    Nat → List (Array Nat × Array Nat) → Bool
  | _, [] => true
  | k, b :: bs =>
    (k % parts != i || searchBox nd cFuel b.1 b.2) && searchEvery nd parts i (k + 1) bs

/-- A copy of a table: a new array with the same entries. Each part of the parallel search reads
a copy of its own, so that the parts share no object whose reference count would have to be
updated from several threads. -/
def copyTab (tab : Array Nat) : Array Nat :=
  Array.ofFn (n := tab.size) fun i => tab.getD i.val 0

/-- Part `i` of `parts`: the search below the boxes of the list whose number (from `0`) is `i`
modulo `parts`, on a copy of the table. The parts `i = 0, …, parts - 1` together search below
every box of the list. -/
def checkPart (tab : Array Nat) (boxes : List (Array Nat × Array Nat)) (parts i : Nat) : Bool :=
  let tab' := copyTab tab
  searchEvery (node tab' (sparse tab')) parts i 0 boxes

end Local

/-- The complete check of the local inequality on the root box `[13926, 262143]⁷` (grid units),
given a table of lower bounds for `2²⁸ K²` on the cells of width `1/16384`. -/
def checkAll (tab : Array Nat) : Bool :=
  Local.searchBox (Local.node tab (Local.sparse tab)) Local.cFuel Local.rootLo Local.rootHi

/-- The complete check of the local inequality in `parts` parallel parts, cut at depth `depth`.
It is the search of `checkAll`: the boxes with fewer than `depth` splits are examined first, in
the order of `checkAll`, and the searches below the boxes with exactly `depth` splits are dealt
out to `parts` tasks. `Task.spawn f` is by definition the task whose value is `f ()`, so the
value of `checkAllPar` does not depend on how the tasks are scheduled; compiled code runs each
task on a thread of its own (priority `dedicated`), and the operating system shares the
processors among them. -/
def checkAllPar (tab : Array Nat) (depth parts : Nat) : Bool :=
  match Local.frontier (Local.node tab (Local.sparse tab)) depth Local.rootLo Local.rootHi [] with
  | none => false
  | some boxes =>
    ((List.range parts).map fun i =>
      Task.spawn (prio := Task.Priority.dedicated) fun _ =>
        Local.checkPart tab boxes parts i).all Task.get

end Simple673
