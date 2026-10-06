/-
Distinct839/Local/RunCheck.lean — command line driver for the checker of
`Distinct839/Local/Checker.lean` (not part of the proof).

It reads a kernel table from a binary file (little-endian `uint32` entries, as
`certificate/kernel_lower.bin`) and runs the checker on it, with node counts and timing.

Usage:
  localcheck FILE                    count nodes of the whole search (single thread)
  localcheck FILE all                evaluate `checkAll`
  localcheck FILE chunk D N I        evaluate `checkChunk tab D N I`
  localcheck FILE sizes D N          node counts of the `N` chunks at depth `D`
  localcheck FILE paths D            node count below each path of depth `D` (one per line)
  localcheck FILE spot               the terminal boxes accepted by range minima that reach the
                                     fewest table cells (candidates for kernel spot-checks)
-/
import Distinct839.Local.Checker

open Distinct839 Distinct839.Local

/-- Decode little-endian 32-bit unsigned integers. -/
def decodeU32 (b : ByteArray) : Array Nat := Id.run do
  let n := b.size / 4
  let mut out : Array Nat := Array.mkEmpty n
  for k in [0:n] do
    let v := (b.get! (4 * k)).toNat + (b.get! (4 * k + 1)).toNat * 256
      + (b.get! (4 * k + 2)).toNat * 65536 + (b.get! (4 * k + 3)).toNat * 16777216
    out := out.push v
  return out

/-- Counters of a search. -/
structure Cnt where
  nodes : Nat := 0
  leaves : Nat := 0
  pressure : Nat := 0
  basic : Nat := 0
  affine : Nat := 0
  failed : Nat := 0
  maxDepth : Nat := 0

/-- The search of `searchBox (node tab sp)`, with counters (it does not stop at a failure). -/
partial def countBox (tab : Array Nat) (sp : Array (Array Nat)) (depth : Nat)
    (lo hi : Array Nat) (c : Cnt) : Cnt :=
  let c := { c with nodes := c.nodes + 1, maxDepth := max c.maxDepth depth }
  match node tab sp lo hi with
  | .ok 0 => { c with leaves := c.leaves + 1, pressure := c.pressure + 1 }
  | .ok 1 => { c with leaves := c.leaves + 1, basic := c.basic + 1 }
  | .ok _ => { c with leaves := c.leaves + 1, affine := c.affine + 1 }
  | .fail => { c with failed := c.failed + 1 }
  | .split hi' r mid =>
    let c := countBox tab sp (depth + 1) lo (hi'.setIfInBounds r mid) c
    countBox tab sp (depth + 1) (lo.setIfInBounds r mid) hi' c

/-- The search of `searchPath (node tab sp)`, with counters: nodes strictly above the chunk
root are not counted. -/
partial def countPath (tab : Array Nat) (sp : Array (Array Nat)) :
    Nat → Nat → Array Nat → Array Nat → Cnt → Cnt
  | 0, _, lo, hi, c => countBox tab sp 0 lo hi c
  | depth + 1, path, lo, hi, c =>
    match node tab sp lo hi with
    | .ok _ => c
    | .fail => c
    | .split hi' r mid =>
      if path % 2 = 0 then countPath tab sp depth (path / 2) lo (hi'.setIfInBounds r mid) c
      else countPath tab sp depth (path / 2) (lo.setIfInBounds r mid) hi' c

/-- Number of table cells that the pair distances of a box can reach, and whether the box is
cut by the constraint `∑ u ≤ R`. -/
def cellCount (sp : Array (Array Nat)) (lo hi : Array Nat) : Nat × Bool :=
  let total := sumTo (g lo) 6
  let hi' := clamp lo hi total
  let ed := edges sp lo hi' total
  (sumTo (fun q => if q / 7 < q % 7 then (edAt ed (q / 7) (q % 7)).hs + 1 - (edAt ed (q / 7) (q % 7)).ls
    else 0) 49, hi' != hi)

/-- Insert a candidate into a list sorted by cell count, keeping at most `k` entries. -/
def insertBest (k : Nat) (x : Nat × Array Nat × Array Nat) :
    List (Nat × Array Nat × Array Nat) → List (Nat × Array Nat × Array Nat)
  | [] => if k = 0 then [] else [x]
  | y :: ys =>
    if k = 0 then [] else if x.1 < y.1 then x :: (y :: ys).take (k - 1)
    else y :: insertBest (k - 1) x ys

/-- The search, collecting the `k` boxes accepted by range minima (and not cut by `∑ u ≤ R`)
that reach the fewest table cells. -/
partial def spotBox (tab : Array Nat) (sp : Array (Array Nat)) (k : Nat) (lo hi : Array Nat)
    (best : List (Nat × Array Nat × Array Nat)) : List (Nat × Array Nat × Array Nat) :=
  match node tab sp lo hi with
  | .ok 1 =>
    let (n, cut) := cellCount sp lo hi
    if cut then best else
    match best.getLast? with
    | some w => if best.length < k || n < w.1 then insertBest k (n, lo, hi) best else best
    | none => insertBest k (n, lo, hi) best
  | .ok _ => best
  | .fail => best
  | .split hi' r mid =>
    let best := spotBox tab sp k lo (hi'.setIfInBounds r mid) best
    spotBox tab sp k (lo.setIfInBounds r mid) hi' best

def showCnt (c : Cnt) : String :=
  s!"nodes={c.nodes} leaves={c.leaves} pressure={c.pressure} basic={c.basic} " ++
  s!"affine={c.affine} failed={c.failed} maxDepth={c.maxDepth}"

def main (args : List String) : IO UInt32 := do
  match args with
  | [] =>
    IO.eprintln "usage: localcheck FILE [all | chunk D N I | sizes D N]"
    return 2
  | file :: rest =>
    let bytes ← IO.FS.readBinFile file
    let tab := decodeU32 bytes
    IO.println s!"table entries: {tab.size}"
    let t0 ← IO.monoMsNow
    match rest with
    | [] =>
      let sp := sparse tab
      let c := countBox tab sp 0 rootLo rootHi {}
      IO.println (showCnt c)
      let t1 ← IO.monoMsNow
      IO.println s!"status: {if c.failed = 0 then "PASS" else "FAIL"}  wall ms: {t1 - t0}"
      return (if c.failed = 0 then 0 else 1)
    | ["all"] =>
      let ok := checkAll tab
      let t1 ← IO.monoMsNow
      IO.println s!"checkAll = {ok}  wall ms: {t1 - t0}"
      return (if ok then 0 else 1)
    | ["chunk", d, n, i] =>
      let ok := checkChunk tab d.toNat! n.toNat! i.toNat!
      let t1 ← IO.monoMsNow
      IO.println s!"checkChunk {d} {n} {i} = {ok}  wall ms: {t1 - t0}"
      return (if ok then 0 else 1)
    | ["sizes", d, n] =>
      let sp := sparse tab
      let d := d.toNat!
      let n := n.toNat!
      let mut sizes : Array Nat := Array.replicate n 0
      let mut total := 0
      for p in [0:2 ^ d] do
        let c := countPath tab sp d p rootLo rootHi {}
        sizes := sizes.modify (p % n) (· + c.nodes)
        total := total + c.nodes
      IO.println s!"nodes at or below depth {d}: {total}"
      IO.println s!"chunk sizes: {sizes}"
      let t1 ← IO.monoMsNow
      IO.println s!"wall ms: {t1 - t0}"
      return 0
    | ["paths", d] =>
      let sp := sparse tab
      let d := d.toNat!
      for p in [0:2 ^ d] do
        let c := countPath tab sp d p rootLo rootHi {}
        IO.println s!"{p} {c.nodes}"
      return 0
    | ["spot"] =>
      let sp := sparse tab
      let best := spotBox tab sp 8 rootLo rootHi []
      for b in best do
        IO.println s!"cells={b.1} lo={b.2.1} hi={b.2.2}"
      let t1 ← IO.monoMsNow
      IO.println s!"wall ms: {t1 - t0}"
      return 0
    | _ =>
      IO.eprintln "bad arguments"
      return 2
