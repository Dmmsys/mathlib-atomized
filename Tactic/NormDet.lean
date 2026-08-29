/-
Copyright (c) 2026 Paul Cadman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Cadman
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Bird.Correctness
public meta import Mathlib.Tactic.Determinant.Bird.Cert

/-!
# `norm_det` simproc and `eval_det` tactic

This module defines the `norm_det` simproc and the `eval_det` tactic for
normalizing determinants of matrix literals over a commutative ring.
-/

public meta section

open Lean Meta Qq
open Mathlib.Tactic.Determinant

/--
Definition of `normalizeBirdDet` / `normalizeBirdDet` 的定义

English:
definition normalizeBirdDet
  signature: (e : Expr)
  body: do
  let ⟨rα, ctx⟩ ← reifyBirdDet e
.run .reducible .run ctx .run' {} let detNorm ← certBirdDet (rα := rα)
  Mathlib.Tactic.RingNF.cleanup {} {expr := detNorm.norm, proof? := some detNorm.proof}

中文:
定义 normalizeBirdDet
  签名: (e : Expr)
  定义体: do
  let ⟨rα, ctx⟩ ← reifyBirdDet e
.run .reducible .run ctx .run' {} let detNorm ← certBirdDet (rα := rα)
  Mathlib.Tactic.RingNF.cleanup {} {expr := detNorm.norm, proof? := some detNorm.proof}
-/
private def normalizeBirdDet (e : Expr) : MetaM Simp.Result := do
  let ⟨rα, ctx⟩ ← reifyBirdDet e
.run .reducible .run ctx .run' {} let detNorm ← certBirdDet (rα := rα)
  Mathlib.Tactic.RingNF.cleanup {} {expr := detNorm.norm, proof? := some detNorm.proof}

/--
Definition of `normalizeDetFromEntries` / `normalizeDetFromEntries` 的定义

English:
definition normalizeDetFromEntries
  signature: {u : Level} {α : Q(Type u)} {n : Q(Nat)} (rα : Q(CommRing $α))
  body: do
  let xs : Q(List $α) ← mkListLit α entries.toList
  let arrayExpr : Q(Array $α) := q(List.toArray $xs)
  -- `List.ofFn` is exposed (unlike `Array.ofFn`) and so this reduction can be
  -- checked by the kernel
have : (List.ofFn fun k : Fin ($n * $n) => $A k.divNat k.modNat) =Q xs := ⟨⟩
  let hlis

中文:
定义 normalizeDetFromEntries
  签名: {u : Level} {α : Q(类型u)} {n : Q(自然数)} (rα : Q(CommRing $α))
  定义体: do
  let xs : Q(List $α) ← mkListLit α entries.toList
  let arrayExpr : Q(Array $α) := q(List.toArray $xs)
  -- `List.ofFn` is exposed (unlike `Array.ofFn`) and so this reduction can be
  -- checked by the kernel
have : (List.ofFn fun k : Fin ($n * $n) => $A k.divNat k.modNat) =Q xs := ⟨⟩
  let hlis

Depends on / 依赖: CofiniteTopology, CofiniteTopology.isClosed_iff.mpr, isClosed_iff
-/
private def normalizeDetFromEntries {u : Level} {α : Q(Type u)} {n : Q(Nat)} (rα : Q(CommRing $α))
  (A : Q(Matrix (Fin $n) (Fin $n) $α)) (entries : Array Q($α)) :
    MetaM Simp.Result := do
  let xs : Q(List $α) ← mkListLit α entries.toList
  let arrayExpr : Q(Array $α) := q(List.toArray $xs)
  -- `List.ofFn` is exposed (unlike `Array.ofFn`) and so this reduction can be
  -- checked by the kernel
have : (List.ofFn fun k : Fin ($n * $n) => $A k.divNat k.modNat) =Q xs := ⟨⟩
  let hlist : Q(List.ofFn (fun k : Fin ($n * $n) => $A k.divNat k.modNat) = $xs) := q(rfl)
  let hArray := q($hlist ▸ List.toArray_ofFn)
  let birdDet := q(BirdDet.birdDet $n $arrayExpr)
  let detEqBirdDet := q($hArray ▸ Matrix.ofArray_ofFn $A ▸ BirdDet.det_eq_birdDet
    (Array.ofFn fun k : Fin ($n * $n) => $A k.divNat k.modNat) Array.size_ofFn)
  let birdDetNorm ← normalizeBirdDet birdDet
  let detEqBirdDetRes : Simp.Result := ⟨birdDet, some detEqBirdDet, true⟩
  detEqBirdDetRes.mkEqTrans birdDetNorm

/--
Definition of `entriesOfMatrixLiteral?` / `entriesOfMatrixLiteral?` 的定义

English:
definition entriesOfMatrixLiteral?
  signature: {u : Level} {α : Q(Type u)} {n : Q(Nat)}
  body: do
  let some dim ← getNatValue? n | return none
  let ~q(Matrix.of $rows) := A | return none
  let (matrixRows, _, _) ← Matrix.matchVecConsPrefix n rows
  unless matrixRows.length == dim do return none
  let entriesByRow ← matrixRows.mapM fun row => do
    let (entries, _, _) ← Matrix.matchVecConsP

中文:
定义 entriesOfMatrixLiteral?
  签名: {u : Level} {α : Q(类型u)} {n : Q(自然数)}
  定义体: do
  let some dim ← getNatValue? n | return none
  let ~q(Matrix.of $rows) := A | return none
  let (matrixRows, _, _) ← Matrix.matchVecConsPrefix n rows
  unless matrixRows.length == dim do return none
  let entriesByRow ← matrixRows.mapM fun row => do
    let (entries, _, _) ← Matrix.matchVecConsP
-/
private def entriesOfMatrixLiteral? {u : Level} {α : Q(Type u)} {n : Q(Nat)}
    (A : Q(Matrix (Fin $n) (Fin $n) $α)) :
    MetaM (Option (Array Q($α))) := do
  let some dim ← getNatValue? n | return none
  let ~q(Matrix.of $rows) := A | return none
  let (matrixRows, _, _) ← Matrix.matchVecConsPrefix n rows
  unless matrixRows.length == dim do return none
  let entriesByRow ← matrixRows.mapM fun row => do
    let (entries, _, _) ← Matrix.matchVecConsPrefix n row
    return entries
  unless entriesByRow.all (·.length == dim) do return none
  let entries ← entriesByRow.flatten.mapM fun entry => do
    let some entry ← checkTypeQ entry α | throwError "expected matrix entry to have type {α}"
    return entry
  return some entries.toArray

/-- The `norm_det` simproc normalizes determinants of matrices written using `!![...]`
notation over a commutative ring. -/
simproc_decl norm_det (Matrix.det _) := fun e => do
  let e ← instantiateMVars e
  let ⟨_, _, e⟩ ← inferTypeQ' e
  let ~q(@Matrix.det (Fin $n) _ _ _ $rα $matrix) := e | return .continue
  let some entries ← entriesOfMatrixLiteral? matrix | return .continue
  return .done (← normalizeDetFromEntries rα matrix entries)

/--
`eval_det` normalizes determinants of matrices written using `!![...]` notation
over a commutative ring.

Examples:

```lean
example : Matrix.det (R := ℤ) !![1, 2; 3, 4] = -2 := by
  eval_det

example {R : Type*} [CommRing R] (a b c d : R) :
    Matrix.det !![a, b; c, d] = a * d - b * c := by
  eval_det
  ring
```
-/
macro (name := evalDet) "eval_det" : tactic => `(tactic| simp only [norm_det])

end
