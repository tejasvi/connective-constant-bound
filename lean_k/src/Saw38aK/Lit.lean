import Lean
import Saw38aK.CheckK

/-!
# Literal elaborators for generated data (untrusted)

They build data terms directly as raw natural-number literals and Braun-tree constructors. The kernel checks every
statement about the terms they produce; their correctness does not matter for soundness.
-/

namespace Saw38aK

open Lean Elab Term Meta

/-- `nat_lit% "123"`: the raw natural-number literal `123` (decimal digits). -/
elab "nat_lit% " s:str : term => do
  match s.getString.toNat? with
  | some n => return mkRawNatLit n
  | none => throwError "nat_lit%: not a natural number"

/-- The Braun tree of `xs` (index `0` at the root, odd indices left, even right), as constructor terms of `BT α`. -/
partial def braunExpr (α : Expr) (xs : Array Expr) : Expr :=
  if xs.isEmpty then mkApp (mkConst ``BT.leaf) α
  else
    let odd := (List.range xs.size).filter (fun i => i % 2 = 1) |>.map (xs[·]!) |>.toArray
    let even := (List.range xs.size).filter (fun i => i % 2 = 0 ∧ i > 0) |>.map (xs[·]!) |>.toArray
    mkApp4 (mkConst ``BT.node) α xs[0]! (braunExpr α odd) (braunExpr α even)

/-- `nat_bt% "a b c …"`: the Braun tree (`BT Nat`) of the listed natural numbers (decimal, space separated). -/
elab "nat_bt% " s:str : term => do
  let toks := (s.getString.splitOn " ").filter (· ≠ "")
  let mut xs : Array Expr := #[]
  for t in toks do
    match t.toNat? with
    | some n => xs := xs.push (mkRawNatLit n)
    | none => throwError "nat_bt%: bad entry"
  return braunExpr (mkConst ``Nat) xs

/-- `bt_of% c₀ c₁ …`: the Braun tree (`BT (BT Nat)`) of the listed constants. -/
elab "bt_of% " xs:ident* : term => do
  let mut es : Array Expr := #[]
  for x in xs do
    es := es.push (mkConst x.getId)
  return braunExpr (mkApp (mkConst ``BT) (mkConst ``Nat)) es

end Saw38aK
