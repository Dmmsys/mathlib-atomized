/-
Copyright (c) 2025 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
module

public import Mathlib.Data.Fin.Tuple.Reflection
public meta import Mathlib.Util.Qq


/-! # The vecPerm simproc

The `vecPerm` simproc computes the new entries of a vector after applying a permutation to them.

-/

namespace Mathlib.Tactic.FinVec

open Lean Meta Qq

meta section

/--
Definition of `Matrix.matchVecConsPrefixQ` / `Matrix.matchVecConsPrefixQ` 的定义

English:
definition Matrix.matchVecConsPrefixQ
  signature: {u : Level} {α : Q(Type u)} {n : Q(Nat)}
  body: do
  let (l, m, vec) ← Matrix.matchVecConsPrefix n vec
  let l ← l.toArray.mapM fun a => do
    let some aQ ← checkTypeQ a q($α) | throwError m!"Expected {a} to have type {α}"
    return aQ
  let some vecQ ← checkTypeQ vec q(Fin $m -> $α)
    | throwError m!"Expected {vec} to have type {q(Fin $m -> 

中文:
定义 Matrix.matchVecConsPrefixQ
  签名: {u : Level} {α : Q(类型u)} {n : Q(自然数)}
  定义体: do
  let (l, m, vec) ← Matrix.matchVecConsPrefix n vec
  let l ← l.toArray.mapM fun a => do
    let some aQ ← checkTypeQ a q($α) | throwError m!"Expected {a} to have type {α}"
    return aQ
  let some vecQ ← checkTypeQ vec q(Fin $m -> $α)
    | throwError m!"Expected {vec} to have type {q(Fin $m -> 
-/
partial def Matrix.matchVecConsPrefixQ {u : Level} {α : Q(Type u)} {n : Q(Nat)}
    (vec : Q(Fin $n -> $α)) : MetaM (Array Q($α) × (m : Q(Nat)) × Q(Fin $m -> $α)) := do
  let (l, m, vec) ← Matrix.matchVecConsPrefix n vec
  let l ← l.toArray.mapM fun a => do
    let some aQ ← checkTypeQ a q($α) | throwError m!"Expected {a} to have type {α}"
    return aQ
  let some vecQ ← checkTypeQ vec q(Fin $m -> $α)
    | throwError m!"Expected {vec} to have type {q(Fin $m -> $α)}"
  return (l, ⟨m, vecQ⟩)

/--
Definition of `permArray` / `permArray` 的定义

English:
definition permArray
  signature: {α : Type*} [Inhabited α] (vec : Array α) (perm : Array Nat)
  body: perm.map (vec[·]!)

中文:
定义 permArray
  签名: {α : 类型} [Inhabited α] (vec : Array α) (perm : Array 自然数)
  定义体: perm.map (vec[·]!)
-/
private def permArray {α : Type*} [Inhabited α] (vec : Array α) (perm : Array Nat) : Array α :=
  perm.map (vec[·]!)

/--
Definition of `mkFin` / `mkFin` 的定义

English:
definition mkFin
  signature: (n m : Q(Nat))
  body: do
  return q(⟨$n, $(← mkDecideProofQ q($n < $m))⟩)

中文:
定义 mkFin
  签名: (n m : Q(自然数))
  定义体: do
  return q(⟨$n, $(← mkDecideProofQ q($n < $m))⟩)
-/
def mkFin (n m : Q(Nat)) : MetaM Q(Fin $m) := do
  return q(⟨$n, $(← mkDecideProofQ q($n < $m))⟩)

/--
Definition of `arrayOfVecFinQ` / `arrayOfVecFinQ` 的定义

English:
definition arrayOfVecFinQ
  signature: (n : Q(Nat)) (vn : Nat) (perm : Q(Fin $n -> Fin $n))
  body: do
  let mut out : Array Nat := #[]
  for idx in *...vn do
    let idxQ := mkNatLitQ idx
    let idxQNew ← mkFin idxQ n
    let outIdxQ := q(($perm $idxQNew : Nat))
    let outIdxExpr ← Lean.Meta.Simp.dsimp outIdxQ
    let some outIdx ← Lean.Meta.getNatValue? outIdxExpr | return none
    out := out.

中文:
定义 arrayOfVecFinQ
  签名: (n : Q(自然数)) (vn : 自然数) (perm : Q(Fin $n -> Fin $n))
  定义体: do
  let mut out : Array Nat := #[]
  for idx in *...vn do
    let idxQ := mkNatLitQ idx
    let idxQNew ← mkFin idxQ n
    let outIdxQ := q(($perm $idxQNew : Nat))
    let outIdxExpr ← Lean.Meta.Simp.dsimp outIdxQ
    let some outIdx ← Lean.Meta.getNatValue? outIdxExpr | return none
    out := out.
-/
def arrayOfVecFinQ (n : Q(Nat)) (vn : Nat) (perm : Q(Fin $n -> Fin $n)) :
    SimpM (Option <| Array Nat) := do
  let mut out : Array Nat := #[]
  for idx in *...vn do
    let idxQ := mkNatLitQ idx
    let idxQNew ← mkFin idxQ n
    let outIdxQ := q(($perm $idxQNew : Nat))
    let outIdxExpr ← Lean.Meta.Simp.dsimp outIdxQ
    let some outIdx ← Lean.Meta.getNatValue? outIdxExpr | return none
    out := out.push outIdx
  return out

/--
theorem `eq_etaExpand` / 定理 `eq_etaExpand`

English:
theorem eq_etaExpand
  given: {α : Type*} {m : Nat} (v : Fin m -> α)
  statement: v = FinVec.etaExpand v
  proof: (FinVec.etaExpand_eq _).symm

中文:
定理 eq_etaExpand
  条件: {α : 类型} {m : 自然数} (v : Fin m -> α)
  结论: v = FinVec.etaExpand v
  证明: (FinVec.etaExpand_eq _).symm

Depends on / 依赖: FinVec, FinVec.etaExpand_eq, etaExpand_eq
-/
theorem eq_etaExpand {α : Type*} {m : Nat} (v : Fin m -> α) : v = FinVec.etaExpand v :=
  (FinVec.etaExpand_eq _).symm

end

public section

/--
The `vecPerm` simproc computes the new entries of a vector after applying a permutation to them.
This can be used to simplify expressions as follows:
```
example {a b c : Nat} : ![a, b, c] ∘ Equiv.swap 0 1 = ![b, a, c] := by
  simp [vecPerm, Equiv.swap_apply_def]
```
Note that for this simproc to work, dsimp needs to be able to simplify the individual applications
of the permutation.
-/
simproc_decl vecPerm (_ ∘ (_ : Fin _ -> Fin _)) := fun e => do
  let ⟨_, ~q(Fin $n -> $α), ~q(($v) ∘ ($p : _ -> Fin $n'))⟩ ← inferTypeQ' e | return .continue
  let .defEq _ ← isDefEqQ q($n) q($n') | return .continue
  let (unperm, ⟨m, _⟩) ← Matrix.matchVecConsPrefixQ v
  unless ← isDefEq m q(0) do return .continue
  let some perm ← arrayOfVecFinQ n unperm.size p | return .continue
  let out := permArray unperm perm
  let out := PiFin.mkLiteralQ (n := out.size) (out[·]!)
  let pf ← mkAppM ``FinVec.eq_etaExpand #[e]
return .continue some { expr := out, proof? := pf }

end

end Mathlib.Tactic.FinVec
