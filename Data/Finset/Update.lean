/-
Copyright (c) 2023 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Data.Finset.Pi
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Logic.Function.DependsOn

/-!
# Update a function on a set of values

This file defines `Function.updateFinset`, the operation that updates a function on a
(finite) set of values.

This is a very specific function used for `MeasureTheory.marginal`, and possibly not that useful
for other purposes.
-/

@[expose] public section
variable {ι : Sort _} {π : ι -> Sort _} {x : forall i, π i} [DecidableEq ι]
  {s t : Finset ι} {y : forall i : s, π i} {z : forall i : t, π i} {i : ι}

namespace Function

/--
Definition of `updateFinset` / `updateFinset` 的定义

English:
definition updateFinset
  signature: (x : forall i, π i) (s : Finset ι) (y : forall i : ↥s, π i) (i : ι)
  body: if hi : i in s then y ⟨i, hi⟩ else x i

中文:
定义 updateFinset
  签名: (x : 对任意 i, π i) (s : Finset ι) (y : 对任意 i : ↥s, π i) (i : ι)
  定义体: if hi : i in s then y ⟨i, hi⟩ else x i
-/
def updateFinset (x : forall i, π i) (s : Finset ι) (y : forall i : ↥s, π i) (i : ι) : π i :=
  if hi : i in s then y ⟨i, hi⟩ else x i

open Finset Equiv

/--
theorem `updateFinset_def` / 定理 `updateFinset_def`

English:
theorem updateFinset_def
  proof: rfl

中文:
定理 updateFinset_def
  证明: rfl
-/
theorem updateFinset_def :
    updateFinset x s y = fun i => if hi : i in s then y ⟨i, hi⟩ else x i :=
  rfl

/--
theorem `updateFinset_empty` / 定理 `updateFinset_empty`

English:
theorem updateFinset_empty
  given: {y}
  statement: updateFinset x ∅ y = x
  proof: rfl

中文:
定理 updateFinset_empty
  条件: {y}
  结论: updateFinset x ∅ y = x
  证明: rfl
-/
@[simp] theorem updateFinset_empty {y} : updateFinset x ∅ y = x :=
  rfl

/--
theorem `updateFinset_singleton` / 定理 `updateFinset_singleton`

English:
theorem updateFinset_singleton
  given: {y}
  proof: by
  congr with j
  by_cases hj : j = i
  · cases hj
    simp only [dif_pos, Finset.mem_singleton, update_self, updateFinset]
  · simp [hj, updateFinset]

中文:
定理 updateFinset_singleton
  条件: {y}
  证明: by
  congr with j
  by_cases hj : j = i
  · cases hj
    simp only [dif_pos, Finset.mem_singleton, update_self, updateFinset]
  · simp [hj, updateFinset]

Depends on / 依赖: Finset, Finset.mem_singleton, dif_pos, mem_singleton, updateFinset, update_self
-/
theorem updateFinset_singleton {y} :
    updateFinset x {i} y = Function.update x i (y ⟨i, mem_singleton_self i⟩) := by
  congr with j
  by_cases hj : j = i
  · cases hj
    simp only [dif_pos, Finset.mem_singleton, update_self, updateFinset]
  · simp [hj, updateFinset]

/--
theorem `update_eq_updateFinset` / 定理 `update_eq_updateFinset`

English:
theorem update_eq_updateFinset
  given: {y}
  proof: by
  congr with j
  by_cases hj : j = i
  · cases hj
    simp only [dif_pos, Finset.mem_singleton, update_self, updateFinset]
    exact uniqueElim_default (α := fun j : ({i} : Finset ι) => π j) y
  · simp [hj, updateFinset]

中文:
定理 update_eq_updateFinset
  条件: {y}
  证明: by
  congr with j
  by_cases hj : j = i
  · cases hj
    simp only [dif_pos, Finset.mem_singleton, update_self, updateFinset]
    exact uniqueElim_default (α := fun j : ({i} : Finset ι) => π j) y
  · simp [hj, updateFinset]

Depends on / 依赖: Finset, Finset.mem_singleton, dif_pos, mem_singleton, uniqueElim_default, updateFinset, update_self
-/
theorem update_eq_updateFinset {y} :
    Function.update x i y = updateFinset x {i} (uniqueElim y) := by
  congr with j
  by_cases hj : j = i
  · cases hj
    simp only [dif_pos, Finset.mem_singleton, update_self, updateFinset]
    exact uniqueElim_default (α := fun j : ({i} : Finset ι) => π j) y
  · simp [hj, updateFinset]

/--
theorem `_root_.DependsOn.updateFinset` / 定理 `_root_.DependsOn.updateFinset`

English:
theorem _root_.DependsOn.updateFinset
  statement: {α : Type*} {f : (Π i, π i) -> α} {s : Set ι}
  proof: by
  refine fun x₁ x₂ h => hf (fun i hi => ?_)
  simp only [Function.updateFinset]
  split_ifs; · rfl
  simp_all

中文:
定理 _root_.DependsOn.updateFinset
  结论: {α : 类型} {f : (Π i, π i) -> α} {s : Set ι}
  证明: by
  refine fun x₁ x₂ h => hf (fun i hi => ?_)
  simp only [Function.updateFinset]
  split_ifs; · rfl
  simp_all

Depends on / 依赖: Function, Function.updateFinset, split_ifs, updateFinset
-/
theorem _root_.DependsOn.updateFinset {α : Type*} {f : (Π i, π i) -> α} {s : Set ι}
    (hf : DependsOn f s) {t : Finset ι} (y : Π i : t, π i) :
    DependsOn (fun x => f (updateFinset x t y)) (s \ t) := by
  refine fun x₁ x₂ h => hf (fun i hi => ?_)
  simp only [Function.updateFinset]
  split_ifs; · rfl
  simp_all

/--
theorem `_root_.DependsOn.update` / 定理 `_root_.DependsOn.update`

English:
theorem _root_.DependsOn.update
  statement: {α : Type*} {f : (Π i, π i) -> α} {s : Finset ι} (hf : DependsOn f s)
  proof: by
  simp_rw [Function.update_eq_updateFinset, erase_eq, coe_sdiff]
  exact hf.updateFinset _

中文:
定理 _root_.DependsOn.update
  结论: {α : 类型} {f : (Π i, π i) -> α} {s : Finset ι} (hf : DependsOn f s)
  证明: by
  simp_rw [Function.update_eq_updateFinset, erase_eq, coe_sdiff]
  exact hf.updateFinset _

Depends on / 依赖: Function, Function.update_eq_updateFinset, coe_sdiff, erase_eq, hf.updateFinset, simp_rw, updateFinset, update_eq_updateFinset
-/
theorem _root_.DependsOn.update {α : Type*} {f : (Π i, π i) -> α} {s : Finset ι} (hf : DependsOn f s)
    (i : ι) (y : π i) : DependsOn (fun x => f (Function.update x i y)) (s.erase i) := by
  simp_rw [Function.update_eq_updateFinset, erase_eq, coe_sdiff]
  exact hf.updateFinset _

/--
theorem `updateFinset_updateFinset` / 定理 `updateFinset_updateFinset`

English:
theorem updateFinset_updateFinset
  given: (hst : Disjoint s t)
  proof: by
  set e := Equiv.Finset.union s t hst
  ext i
  by_cases his : i in s <;> by_cases hit : i in t <;>
    simp only [updateFinset, his, hit, dif_pos, dif_neg, Finset.mem_union, false_or, not_false_iff]
  · exfalso; exact Finset.disjoint_left.mp hst his hit
.symm · exact piCongrLeft_sumInl (fun b : 

中文:
定理 updateFinset_updateFinset
  条件: (hst : Disjoint s t)
  证明: by
  set e := Equiv.Finset.union s t hst
  ext i
  by_cases his : i in s <;> by_cases hit : i in t <;>
    simp only [updateFinset, his, hit, dif_pos, dif_neg, Finset.mem_union, false_or, not_false_iff]
  · exfalso; exact Finset.disjoint_left.mp hst his hit
.symm · exact piCongrLeft_sumInl (fun b : 

Depends on / 依赖: Equiv.Finset.union, Finset, Finset.disjoint_left.mp, Finset.mem_union, dif_neg, dif_pos, disjoint_left, false_or, mem_union, not_false_iff, piCongrLeft_sumInl, piCongrLeft_sumInr, updateFinset
-/
theorem updateFinset_updateFinset (hst : Disjoint s t) :
    updateFinset (updateFinset x s y) t z =
    updateFinset x (s union t) (Equiv.piFinsetUnion π hst ⟨y, z⟩) := by
  set e := Equiv.Finset.union s t hst
  ext i
  by_cases his : i in s <;> by_cases hit : i in t <;>
    simp only [updateFinset, his, hit, dif_pos, dif_neg, Finset.mem_union, false_or, not_false_iff]
  · exfalso; exact Finset.disjoint_left.mp hst his hit
.symm · exact piCongrLeft_sumInl (fun b : ↥(s union t) => π b) e y z ⟨i, his⟩
.symm · exact piCongrLeft_sumInr (fun b : ↥(s union t) => π b) e y z ⟨i, hit⟩

/--
lemma `updateFinset_updateFinset_of_subset` / 引理 `updateFinset_updateFinset_of_subset`

English:
lemma updateFinset_updateFinset_of_subset
  statement: {s t : Finset ι} (hst : s subseteq t)
  proof: by
  grind [updateFinset]

中文:
引理 updateFinset_updateFinset_of_subset
  结论: {s t : Finset ι} (hst : s subseteq t)
  证明: by
  grind [updateFinset]

Depends on / 依赖: updateFinset
-/
lemma updateFinset_updateFinset_of_subset {s t : Finset ι} (hst : s subseteq t)
    (x : Π i, π i) (y : Π i : s, π i) (z : Π i : t, π i) :
    updateFinset (updateFinset x s y) t z = updateFinset x t z := by
  grind [updateFinset]

/--
lemma `restrict_updateFinset_of_subset` / 引理 `restrict_updateFinset_of_subset`

English:
lemma restrict_updateFinset_of_subset
  statement: {s t : Finset ι} (hst : s subseteq t) (x : Π i, π i)
  proof: by
  ext i
  simp [updateFinset, dif_pos (hst i.2)]

中文:
引理 restrict_updateFinset_of_subset
  结论: {s t : Finset ι} (hst : s subseteq t) (x : Π i, π i)
  证明: by
  ext i
  simp [updateFinset, dif_pos (hst i.2)]

Depends on / 依赖: dif_pos, updateFinset
-/
lemma restrict_updateFinset_of_subset {s t : Finset ι} (hst : s subseteq t) (x : Π i, π i)
    (y : Π i : t, π i) : s.restrict (updateFinset x t y) = restrict₂ hst y := by
  ext i
  simp [updateFinset, dif_pos (hst i.2)]

/--
lemma `restrict_updateFinset` / 引理 `restrict_updateFinset`

English:
lemma restrict_updateFinset
  given: {s : Finset ι} (x : Π i, π i) (y : Π i : s, π i)
  proof: by
  rw [restrict_updateFinset_of_subset subset_rfl]
  rfl

@[simp]

中文:
引理 restrict_updateFinset
  条件: {s : Finset ι} (x : Π i, π i) (y : Π i : s, π i)
  证明: by
  rw [restrict_updateFinset_of_subset subset_rfl]
  rfl

@[simp]

Depends on / 依赖: restrict_updateFinset_of_subset, subset_rfl
-/
lemma restrict_updateFinset {s : Finset ι} (x : Π i, π i) (y : Π i : s, π i) :
    s.restrict (updateFinset x s y) = y := by
  rw [restrict_updateFinset_of_subset subset_rfl]
  rfl

@[simp]
/--
lemma `updateFinset_restrict` / 引理 `updateFinset_restrict`

English:
lemma updateFinset_restrict
  given: {s : Finset ι} (x : Π i, π i)
  proof: by
  ext i
  simp [updateFinset]

中文:
引理 updateFinset_restrict
  条件: {s : Finset ι} (x : Π i, π i)
  证明: by
  ext i
  simp [updateFinset]

Depends on / 依赖: updateFinset
-/
lemma updateFinset_restrict {s : Finset ι} (x : Π i, π i) :
    updateFinset x s (s.restrict x) = x := by
  ext i
  simp [updateFinset]

-- this would be slightly nicer if we had a version of `Equiv.piFinsetUnion` for `insert`.
/--
theorem `update_updateFinset` / 定理 `update_updateFinset`

English:
theorem update_updateFinset
  given: {z} (hi : i ∉ s)
  proof: by
  rw [update_eq_updateFinset]; rw [updateFinset_updateFinset]

中文:
定理 update_updateFinset
  条件: {z} (hi : i ∉ s)
  证明: by
  rw [update_eq_updateFinset]; rw [updateFinset_updateFinset]

Depends on / 依赖: updateFinset_updateFinset, update_eq_updateFinset
-/
theorem update_updateFinset {z} (hi : i ∉ s) :
    Function.update (updateFinset x s y) i z = updateFinset x (s union {i})
      ((Equiv.piFinsetUnion π <| Finset.disjoint_singleton_right.mpr hi) (y, uniqueElim z)) := by
  rw [update_eq_updateFinset]; rw [updateFinset_updateFinset]

/--
theorem `updateFinset_congr` / 定理 `updateFinset_congr`

English:
theorem updateFinset_congr
  given: (h : s = t)
  proof: by
  subst h; rfl

中文:
定理 updateFinset_congr
  条件: (h : s = t)
  证明: by
  subst h; rfl
-/
theorem updateFinset_congr (h : s = t) :
    updateFinset x s y = updateFinset x t (fun i => y ⟨i, h ▸ i.prop⟩) := by
  subst h; rfl

/--
theorem `updateFinset_univ` / 定理 `updateFinset_univ`

English:
theorem updateFinset_univ
  given: [Fintype ι] {y : forall i : Finset.univ, π i}
  proof: by
  simp [updateFinset_def]

中文:
定理 updateFinset_univ
  条件: [Fintype ι] {y : 对任意 i : Finset.univ, π i}
  证明: by
  simp [updateFinset_def]

Depends on / 依赖: updateFinset_def
-/
theorem updateFinset_univ [Fintype ι] {y : forall i : Finset.univ, π i} :
    updateFinset x .univ y = fun i : ι => y ⟨i, Finset.mem_univ i⟩ := by
  simp [updateFinset_def]

/--
theorem `updateFinset_univ_apply` / 定理 `updateFinset_univ_apply`

English:
theorem updateFinset_univ_apply
  given: [Fintype ι] {y : forall i : Finset.univ, π i} {i : ι}
  proof: by
  simp [updateFinset_def]

中文:
定理 updateFinset_univ_apply
  条件: [Fintype ι] {y : 对任意 i : Finset.univ, π i} {i : ι}
  证明: by
  simp [updateFinset_def]

Depends on / 依赖: updateFinset_def
-/
theorem updateFinset_univ_apply [Fintype ι] {y : forall i : Finset.univ, π i} {i : ι} :
    updateFinset x .univ y i = y ⟨i, Finset.mem_univ i⟩ := by
  simp [updateFinset_def]

end Function
