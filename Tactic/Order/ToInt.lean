/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Batteries.Data.List.Pairwise
public import Batteries.Tactic.GeneralizeProofs
public import Mathlib.Tactic.Order.CollectFacts
public meta import Mathlib.Util.AtomM
public meta import Mathlib.Util.Qq
public meta import Std.Data.HashMap.AdditionalOperations

/-!
# Translating linear orders to ℤ

In this file we implement the translation of a problem in any linearly ordered type to a problem in
`ℤ`. This allows us to use the `lia` tactic to solve it.

While the core algorithm of the `order` tactic is complete for the theory of linear orders in the
signature (`<`, `≤`),
it becomes incomplete in the signature with lattice operations `⊓` and `⊔`. With these operations,
the problem becomes NP-hard, and the idea is to reuse a smart and efficient procedure, such as
`lia`.

## TODO

Migrate to `grind` when it is ready.
-/

public meta section

namespace Mathlib.Tactic.Order.ToInt

variable {α : Type*} [LinearOrder α] {n : Nat} (val : Fin n -> α)

/--
theorem `exists_translation` / 定理 `exists_translation`

English:
theorem exists_translation
  statement: exists tr : Fin n -> Int, forall i j, val i <= val j ↔ tr i <= tr j
  proof: by
  let li := List.ofFn val
  let sli := li.mergeSort
  have (i : Fin n) : exists j : Fin sli.length, sli[j] = val i := by
    apply List.get_of_mem
    rw [List.Perm.mem_iff (List.mergeSort_perm _ _)]
    simp [li]
  use fun i => (this i).choose
  intro i j
  simp only [Fin.getElem_fin, Int.ofNat_

中文:
定理 存在_translation
  结论: 存在 tr : 有限集 n -> 整数, 对任意 i j, val i <= val j ↔ tr i <= tr j
  证明: by
  let li := List.ofFn val
  let sli := li.mergeSort
  have (i : Fin n) : exists j : Fin sli.length, sli[j] = val i := by
    apply List.get_of_mem
    rw [List.Perm.mem_iff (List.mergeSort_perm _ _)]
    simp [li]
  use fun i => (this i).choose
  intro i j
  simp only [Fin.getElem_fin, Int.ofNat_

Depends on / 依赖: Fin.getElem_fin, Int.ofNat_le, List.Perm.mem_iff, List.get_of_mem, List.mergeSort_perm, List.ofFn, choose_spec, conv_lhs, generalize_proofs, getElem_fin, get_of_mem, h_eq, hi.choose_spec, hj.choose_spec, length, li.mergeSort, li.pairwise_mergeSort, mem_iff, mergeSort, mergeSort_perm
-/
theorem exists_translation : exists tr : Fin n -> Int, forall i j, val i <= val j ↔ tr i <= tr j := by
  let li := List.ofFn val
  let sli := li.mergeSort
  have (i : Fin n) : exists j : Fin sli.length, sli[j] = val i := by
    apply List.get_of_mem
    rw [List.Perm.mem_iff (List.mergeSort_perm _ _)]
    simp [li]
  use fun i => (this i).choose
  intro i j
  simp only [Fin.getElem_fin, Int.ofNat_le]
  by_cases h_eq : val i = val j
  · simp [h_eq]
  generalize_proofs _ hi hj
  rw [← hi.choose_spec]; rw [← hj.choose_spec] at h_eq
  conv_lhs => rw [← hi.choose_spec, ← hj.choose_spec]
  have := li.pairwise_mergeSort (le := fun a b => decide (a <= b))
      (fun a b c => by simpa using le_trans) (by simpa using le_total)
  rw [List.pairwise_iff_get] at this
  refine ⟨fun h => ?_, fun h => ?_⟩
  · contrapose! h
    exact lt_of_le_of_ne (by simpa using (this hj.choose hi.choose (by simpa)))
      (fun h => h_eq (h.symm))
  · simpa using this hi.choose hj.choose (by apply lt_of_le_of_ne h; contrapose h_eq; simp [h_eq])

/--
Definition of `toInt` / `toInt` 的定义

English:
definition toInt
  signature: (k : Fin n)
  body: (exists_translation val).choose k

中文:
定义 to整数
  签名: (k : 有限集 n)
  定义体: (exists_translation val).choose k

Depends on / 依赖: exists_translation
-/
noncomputable def toInt (k : Fin n) : Int :=
  (exists_translation val).choose k

variable (i j k : Fin n)

/--
theorem `toInt_le_toInt` / 定理 `toInt_le_toInt`

English:
theorem toInt_le_toInt
  statement: toInt val i <= toInt val j ↔ val i <= val j
  proof: by
  simp [toInt, (exists_translation val).choose_spec]

中文:
定理 to整数_le_to整数
  结论: to整数 val i <= to整数 val j ↔ val i <= val j
  证明: by
  simp [toInt, (exists_translation val).choose_spec]

Depends on / 依赖: choose_spec, exists_translation
-/
theorem toInt_le_toInt : toInt val i <= toInt val j ↔ val i <= val j := by
  simp [toInt, (exists_translation val).choose_spec]

/--
theorem `toInt_lt_toInt` / 定理 `toInt_lt_toInt`

English:
theorem toInt_lt_toInt
  statement: toInt val i < toInt val j ↔ val i < val j
  proof: by
  simpa using (toInt_le_toInt val j i).not

中文:
定理 to整数_lt_to整数
  结论: to整数 val i < to整数 val j ↔ val i < val j
  证明: by
  simpa using (toInt_le_toInt val j i).not

Depends on / 依赖: toInt_le_toInt
-/
theorem toInt_lt_toInt : toInt val i < toInt val j ↔ val i < val j := by
  simpa using (toInt_le_toInt val j i).not

/--
theorem `toInt_eq_toInt` / 定理 `toInt_eq_toInt`

English:
theorem toInt_eq_toInt
  statement: toInt val i = toInt val j ↔ val i = val j
  proof: by
  simp [toInt_le_toInt, le_antisymm_iff]

中文:
定理 to整数_eq_to整数
  结论: to整数 val i = to整数 val j ↔ val i = val j
  证明: by
  simp [toInt_le_toInt, le_antisymm_iff]

Depends on / 依赖: le_antisymm_iff, toInt_le_toInt
-/
theorem toInt_eq_toInt : toInt val i = toInt val j ↔ val i = val j := by
  simp [toInt_le_toInt, le_antisymm_iff]

/--
theorem `toInt_ne_toInt` / 定理 `toInt_ne_toInt`

English:
theorem toInt_ne_toInt
  statement: toInt val i != toInt val j ↔ val i != val j
  proof: by
  simpa using (toInt_eq_toInt val i j).not

中文:
定理 to整数_ne_to整数
  结论: to整数 val i != to整数 val j ↔ val i != val j
  证明: by
  simpa using (toInt_eq_toInt val i j).not

Depends on / 依赖: toInt_eq_toInt
-/
theorem toInt_ne_toInt : toInt val i != toInt val j ↔ val i != val j := by
  simpa using (toInt_eq_toInt val i j).not

/--
theorem `toInt_nle_toInt` / 定理 `toInt_nle_toInt`

English:
theorem toInt_nle_toInt
  statement: ¬toInt val i <= toInt val j ↔ ¬val i <= val j
  proof: by
  simpa using toInt_lt_toInt val j i

中文:
定理 to整数_nle_to整数
  结论: ¬to整数 val i <= to整数 val j ↔ ¬val i <= val j
  证明: by
  simpa using toInt_lt_toInt val j i

Depends on / 依赖: toInt_lt_toInt
-/
theorem toInt_nle_toInt : ¬toInt val i <= toInt val j ↔ ¬val i <= val j := by
  simpa using toInt_lt_toInt val j i

/--
theorem `toInt_nlt_toInt` / 定理 `toInt_nlt_toInt`

English:
theorem toInt_nlt_toInt
  statement: ¬toInt val i < toInt val j ↔ ¬val i < val j
  proof: by
  simpa using toInt_le_toInt val j i

中文:
定理 to整数_nlt_to整数
  结论: ¬to整数 val i < to整数 val j ↔ ¬val i < val j
  证明: by
  simpa using toInt_le_toInt val j i

Depends on / 依赖: toInt_le_toInt
-/
theorem toInt_nlt_toInt : ¬toInt val i < toInt val j ↔ ¬val i < val j := by
  simpa using toInt_le_toInt val j i

/--
theorem `toInt_sup_toInt_eq_toInt` / 定理 `toInt_sup_toInt_eq_toInt`

English:
theorem toInt_sup_toInt_eq_toInt
  proof: by
  simp [le_antisymm_iff, sup_le_iff, le_sup_iff, toInt_le_toInt]

中文:
定理 to整数_sup_to整数_eq_to整数
  证明: by
  simp [le_antisymm_iff, sup_le_iff, le_sup_iff, toInt_le_toInt]

Depends on / 依赖: le_antisymm_iff, le_sup_iff, sup_le_iff, toInt_le_toInt
-/
theorem toInt_sup_toInt_eq_toInt :
    toInt val i ⊔ toInt val j = toInt val k ↔ val i ⊔ val j = val k := by
  simp [le_antisymm_iff, sup_le_iff, le_sup_iff, toInt_le_toInt]

/--
theorem `toInt_inf_toInt_eq_toInt` / 定理 `toInt_inf_toInt_eq_toInt`

English:
theorem toInt_inf_toInt_eq_toInt
  proof: by
  simp [le_antisymm_iff, inf_le_iff, le_inf_iff, toInt_le_toInt]

中文:
定理 to整数_inf_to整数_eq_to整数
  证明: by
  simp [le_antisymm_iff, inf_le_iff, le_inf_iff, toInt_le_toInt]

Depends on / 依赖: inf_le_iff, le_antisymm_iff, le_inf_iff, toInt_le_toInt
-/
theorem toInt_inf_toInt_eq_toInt :
    toInt val i ⊓ toInt val j = toInt val k ↔ val i ⊓ val j = val k := by
  simp [le_antisymm_iff, inf_le_iff, le_inf_iff, toInt_le_toInt]

open Lean Meta Qq

/--
Definition of `mkFinFun` / `mkFinFun` 的定义

English:
definition mkFinFun
  signature: {u : Level} {α : Q(Type $u)} (atoms : Array Q($α))
  body: do
  if h : atoms.isEmpty then
    return q(Fin.elim0 : Fin 0 -> $α)
  else
    let rarray := RArray.ofArray atoms (by simpa [Array.size_pos_iff] using h)
    let rarrayExpr : Q(RArray $α) ← rarray.toExpr α (fun x => x)
    haveI m : Q(Nat) := mkNatLit atoms.size
    return q(fun (x : Fin $m) => ($r

中文:
定义 mkFinFun
  签名: {u : Level} {α : Q(类型 $u)} (atoms : 数组 Q($α))
  定义体: do
  if h : atoms.isEmpty then
    return q(Fin.elim0 : Fin 0 -> $α)
  else
    let rarray := RArray.ofArray atoms (by simpa [Array.size_pos_iff] using h)
    let rarrayExpr : Q(RArray $α) ← rarray.toExpr α (fun x => x)
    haveI m : Q(Nat) := mkNatLit atoms.size
    return q(fun (x : Fin $m) => ($r
-/
def mkFinFun {u : Level} {α : Q(Type $u)} (atoms : Array Q($α)) : MetaM Expr := do
  if h : atoms.isEmpty then
    return q(Fin.elim0 : Fin 0 -> $α)
  else
    let rarray := RArray.ofArray atoms (by simpa [Array.size_pos_iff] using h)
    let rarrayExpr : Q(RArray $α) ← rarray.toExpr α (fun x => x)
    haveI m : Q(Nat) := mkNatLit atoms.size
    return q(fun (x : Fin $m) => ($rarrayExpr).get x.val)

/--
Definition of `translateToInt` / `translateToInt` 的定义

English:
definition translateToInt
  signature: {u : Lean.Level} (type : Q(Type u)) (inst : Q(LinearOrder $type))
  body: do
  let mut idxToAtom : Std.HashMap Nat Q($type) := ∅
  for atom in (← get).atoms do
    -- `atoms` contains atoms for all types we are working on, so here we need to filter only
    -- those of type `type`
if ← withReducible isDefEq type (← inferType atom) then
      idxToAtom := idxToAtom.insert 

中文:
定义 translateTo整数
  签名: {u : Lean.Level} (type : Q(类型u)) (inst : Q(线性序 $type))
  定义体: do
  let mut idxToAtom : Std.HashMap Nat Q($type) := ∅
  for atom in (← get).atoms do
    -- `atoms` contains atoms for all types we are working on, so here we need to filter only
    -- those of type `type`
if ← withReducible isDefEq type (← inferType atom) then
      idxToAtom := idxToAtom.insert 
-/
def translateToInt {u : Lean.Level} (type : Q(Type u)) (inst : Q(LinearOrder $type))
    (facts : Array AtomicFact) :
AtomM Std.HashMap Nat Q(Int) × Array AtomicFact := do
  let mut idxToAtom : Std.HashMap Nat Q($type) := ∅
  for atom in (← get).atoms do
    -- `atoms` contains atoms for all types we are working on, so here we need to filter only
    -- those of type `type`
if ← withReducible isDefEq type (← inferType atom) then
      idxToAtom := idxToAtom.insert idxToAtom.size atom
  haveI nE : Q(Nat) := mkNatLitQ idxToAtom.size
  haveI finFun : Q(Fin $nE -> $type) :=
    ← mkFinFun (Array.ofFn fun (n : Fin idxToAtom.size) => idxToAtom[n]!)
  let toFinUnsafe : Nat -> Q(Fin $nE) := fun k =>
    haveI kE := mkNatLitQ k
    haveI heq : decide ($kE < $nE) =Q true := ⟨⟩
    q(⟨$kE, of_decide_eq_true $heq⟩)
return Prod.snd facts.foldl (fun (curr, map, facts) fact =>
    match fact with
    | .eq lhs rhs prf =>
      (curr, map, facts.push (
        haveI lhsFin := toFinUnsafe lhs
        haveI rhsFin := toFinUnsafe rhs
        haveI prfQ : Q($finFun $lhsFin = $finFun $rhsFin) := prf
        .eq lhs rhs q((toInt_eq_toInt $finFun $lhsFin $rhsFin).mpr $prfQ)
      ))
    | .ne lhs rhs prf =>
      (curr, map, facts.push (
        haveI lhsFin := toFinUnsafe lhs
        haveI rhsFin := toFinUnsafe rhs
        haveI prfQ : Q($finFun $lhsFin != $finFun $rhsFin) := prf
        .ne lhs rhs q((toInt_ne_toInt $finFun $lhsFin $rhsFin).mpr $prfQ)
      ))
    | .le lhs rhs prf =>
      (curr, map, facts.push (
        haveI lhsFin := toFinUnsafe lhs
        haveI rhsFin := toFinUnsafe rhs
        haveI prfQ : Q($finFun $lhsFin <= $finFun $rhsFin) := prf
        .le lhs rhs q((toInt_le_toInt $finFun $lhsFin $rhsFin).mpr $prfQ)
      ))
    | .lt lhs rhs prf =>
      (curr, map, facts.push (
        haveI lhsFin := toFinUnsafe lhs
        haveI rhsFin := toFinUnsafe rhs
        haveI prfQ : Q($finFun $lhsFin < $finFun $rhsFin) := prf
        .lt lhs rhs q((toInt_lt_toInt $finFun $lhsFin $rhsFin).mpr $prfQ)
      ))
    | .nle lhs rhs prf =>
      (curr, map, facts.push (
        haveI lhsFin := toFinUnsafe lhs
        haveI rhsFin := toFinUnsafe rhs
        haveI prfQ : Q(¬$finFun $lhsFin <= $finFun $rhsFin) := prf
        .nle lhs rhs q((toInt_nle_toInt $finFun $lhsFin $rhsFin).mpr $prfQ)
      ))
    | .nlt lhs rhs prf =>
      (curr, map, facts.push (
        haveI lhsFin := toFinUnsafe lhs
        haveI rhsFin := toFinUnsafe rhs
        haveI prfQ : Q(¬$finFun $lhsFin < $finFun $rhsFin) := prf
        .nlt lhs rhs q((toInt_nlt_toInt $finFun $lhsFin $rhsFin).mpr $prfQ)
      ))
    | .isBot _
    | .isTop _ => (curr, map, facts)
    | .isSup lhs rhs val =>
      haveI lhsFin := toFinUnsafe lhs
      haveI rhsFin := toFinUnsafe rhs
      haveI valFin := toFinUnsafe val
haveI heq : max («$finFun» «$lhsFin») («$finFun» «$rhsFin») =Q « finFun» « valFin» := ⟨⟩
      (curr + 1, map.insert curr q(toInt $finFun $lhsFin ⊔ toInt $finFun $rhsFin),
        (facts.push (.isSup lhs rhs curr)).push (.eq curr val
          q((toInt_sup_toInt_eq_toInt $finFun $lhsFin $rhsFin $valFin).mpr $heq)
        )
      )
    | .isInf lhs rhs val =>
      haveI lhsFin := toFinUnsafe lhs
      haveI rhsFin := toFinUnsafe rhs
      haveI valFin := toFinUnsafe val
haveI heq : min («$finFun» «$lhsFin») («$finFun» «$rhsFin») =Q « finFun» « valFin» := ⟨⟩
      (curr + 1, map.insert curr q(toInt $finFun $lhsFin ⊓ toInt $finFun $rhsFin),
        (facts.push (.isInf lhs rhs curr)).push (.eq curr val
          q((toInt_inf_toInt_eq_toInt $finFun $lhsFin $rhsFin $valFin).mpr $heq)
        )
      ))
    (idxToAtom.size, idxToAtom.map fun k _ =>
      haveI kFin := toFinUnsafe k
      q(toInt $finFun $kFin), Array.emptyWithCapacity idxToAtom.size)

end Mathlib.Tactic.Order.ToInt

export Mathlib.Tactic.Order.ToInt (translateToInt)
