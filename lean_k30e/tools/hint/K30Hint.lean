import K30B.Local
import Std.Data.HashMap

/-!
# k30hint: hints and a compiled pre-check for one K30E shard (untrusted tool)

`k30hint DATADIR NT NUM DEN LO CNT MODS OUT`

For the states `LO, …, LO + CNT - 1` it computes the slot hints (`hintState`) and the dead-cell hints (`deadHints`)
of `K30B.Check3c`, with the records read from the data files `DATADIR/m%05d.bin` of the modules `MODS` (comma
separated, each `m` or `m:u`), and evaluates the compiled conditions of `checkState3cL`: the state's module and each
child's module are listed, and `checkState3c` holds. Rows `i|h|[d0]|[d1]|[d2]` go to OUT, failing states to stderr;
the exit code is 1 if a state fails. Every 4096th record is also decoded through `recOf30` and compared.
The kernel re-checks everything the hints are used for, so this tool only affects which proofs are attempted.
-/

open Saw38aCore Saw38aK K30B

/-- Little-endian `UInt64` at byte offset `o`. -/
def u64At (a : ByteArray) (o : Nat) : UInt64 := Id.run do
  let mut x : UInt64 := 0
  for k in [0:8] do
    x := x ||| ((a.get! (o + k)).toUInt64 <<< (8 * k).toUInt64)
  return x

/-- The record at byte offset `o` (layout of `recOf30`), from machine words. -/
def decodeAt (a : ByteArray) (o : Nat) : Rec :=
  let w0 := u64At a o
  let w1 := u64At a (o + 8)
  let w2 := u64At a (o + 16)
  let w3 := u64At a (o + 20) >>> 32
  ⟨(w0 &&& 63).toNat, ((w0 >>> 6) &&& 0xFFFFFFFFFFFF).toNat, ((w0 >>> 54) ||| ((w1 &&& 0x1FFFFFF) <<< 10)).toNat,
    ((w1 >>> 25) &&& 0x7FFFFFFFF).toNat, ((w1 >>> 60) ||| ((w2 &&& 0x7FFFFFFF) <<< 4)).toNat,
    ((w2 >>> 31) ||| ((w3 &&& 0xFFFFFFF) <<< 33)).toNat⟩

/-- The 224-bit record at byte offset `o` as a natural number, then `recOf30` (the reference decode). -/
def decodeRef (a : ByteArray) (o : Nat) : Rec :=
  recOf30 ((List.range 28).foldr (fun k acc => acc * 256 + (a.get! (o + k)).toNat) 0)

def sameRec (r s : Rec) : Bool :=
  r.n == s.n && r.T == s.T && r.c0 == s.c0 && r.c1 == s.c1 && r.c2 == s.c2 && r.V == s.V

def showL (l : List Nat) : String := "[" ++ String.intercalate ", " (l.map toString) ++ "]"

def pad5 (m : Nat) : String := let s := toString m; "".pushn '0' (5 - s.length) ++ s

def main (args : List String) : IO UInt32 := do
  let [dir, ntS, numS, denS, loS, cntS, modsS, out] := args
    | IO.eprintln "usage: k30hint DATADIR NT NUM DEN LO CNT MODS OUT"; return 2
  let some NT := ntS.toNat? | IO.eprintln "bad NT"; return 2
  let some num := numS.toNat? | IO.eprintln "bad NUM"; return 2
  let some den := denS.toNat? | IO.eprintln "bad DEN"; return 2
  let some lo := loS.toNat? | IO.eprintln "bad LO"; return 2
  let some cnt := cntS.toNat? | IO.eprintln "bad CNT"; return 2
  let mut mods : List Nat := []
  for t in modsS.splitOn "," do
    match ((t.splitOn ":").headD "").toNat? with
    | some m => mods := mods ++ [m]
    | none => IO.eprintln s!"bad module {t}"; return 2
  let mut tbl : Std.HashMap Nat ByteArray := {}
  for m in mods do
    tbl := tbl.insert m (← IO.FS.readBinFile s!"{dir}/m{pad5 m}.bin")
  let rd : Nat → Rec := fun i =>
    match tbl.get? (i >>> 20) with
    | some a => decodeAt a (28 * (i &&& 1048575))
    | none => ⟨0, 0, 0, 0, 0, 0⟩
  let ms : List (Nat × BT Nat) := mods.map fun m => (m, .leaf)
  let mut rows : Array String := Array.mkEmpty cnt
  let mut bad := 0
  for j in [0:cnt] do
    let i := lo + j
    if j % 4096 == 0 then
      match tbl.get? (i >>> 20) with
      | some a =>
        if !sameRec (decodeAt a (28 * (i &&& 1048575))) (decodeRef a (28 * (i &&& 1048575))) then
          IO.eprintln s!"DECODE MISMATCH {i}"; return 3
      | none => pure ()
    let r := rd i
    let hs := hintState rd NT i
    let d0 := deadHints rd i 0 (hs % 16)
    let d1 := deadHints rd i 1 ((hs / 16) % 16)
    let d2 := deadHints rd i 2 (hs / 256)
    let ok := modIn (i >>> 20) ms && kidIn ms r.c0 && kidIn ms r.c1 && kidIn ms r.c2 &&
      checkState3c rd NT num den i hs d0 d1 d2
    if !ok then
      bad := bad + 1
      IO.eprintln s!"FAIL {i} {hs}"
    rows := rows.push s!"{i}|{hs}|{showL d0}|{showL d1}|{showL d2}"
  IO.FS.writeFile out (String.intercalate "\n" rows.toList ++ "\n")
  IO.println s!"states {cnt} failed {bad}"
  return if bad == 0 then 0 else 1
