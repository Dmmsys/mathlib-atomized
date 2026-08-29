/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Set.Piecewise
public import Mathlib.Order.Interval.Set.Basic

/-!
# Functions defined piecewise on a finset

This file defines `Finset.piecewise`: Given two functions `f`, `g`, `s.piecewise f g` is a function
which is equal to `f` on `s` and `g` on the complement.

## TODO

Should we deduplicate this from `Set.piecewise`?
-/

@[expose] public section

open Function

namespace Finset
variable {ι : Type*} {π : ι -> Sort*} (s : Finset ι) (f g : forall i, π i)

/--
Definition of `piecewise` / `piecewise` 的定义

English:
definition piecewise
  signature: [forall j, Decidable (j in s)]
  body: fun i => if i in s then f i else g i

中文:
定义 piecewise
  签名: [对任意 j, Decidable (j in s)]
  定义体: fun i => if i in s then f i else g i
-/
def piecewise [forall j, Decidable (j in s)] : forall i, π i := fun i => if i in s then f i else g i

/--
lemma `piecewise_insert_self` / 引理 `piecewise_insert_self`

English:
lemma piecewise_insert_self
  given: [DecidableEq ι] {j : ι} [forall i, Decidable (i in insert j s)]
  proof: by simp [piecewise]

@[simp]

中文:
引理 piecewise_insert_self
  条件: [DecidableEq ι] {j : ι} [对任意 i, Decidable (i in insert j s)]
  证明: by simp [piecewise]

@[simp]

Depends on / 依赖: piecewise
-/
lemma piecewise_insert_self [DecidableEq ι] {j : ι} [forall i, Decidable (i in insert j s)] :
    (insert j s).piecewise f g j = f j := by simp [piecewise]

@[simp]
/--
lemma `piecewise_empty` / 引理 `piecewise_empty`

English:
lemma piecewise_empty
  given: [forall i : ι, Decidable (i in (∅ : Finset ι))]
  statement: piecewise ∅ f g = g
  proof: by
  ext i
  simp [piecewise]

中文:
引理 piecewise_empty
  条件: [对任意 i : ι, Decidable (i in (∅ : Finset ι))]
  结论: piecewise ∅ f g = g
  证明: by
  ext i
  simp [piecewise]

Depends on / 依赖: piecewise
-/
lemma piecewise_empty [forall i : ι, Decidable (i in (∅ : Finset ι))] : piecewise ∅ f g = g := by
  ext i
  simp [piecewise]

variable [forall j, Decidable (j in s)]

-- TODO: fix this in norm_cast
@[norm_cast move]
/--
lemma `piecewise_coe` / 引理 `piecewise_coe`

English:
lemma piecewise_coe
  statement: (s : Set ι).piecewise f g = s.piecewise f g
  proof: by
  ext
  congr

@[simp]

中文:
引理 piecewise_coe
  结论: (s : Set ι).piecewise f g = s.piecewise f g
  证明: by
  ext
  congr

@[simp]
-/
lemma piecewise_coe : (s : Set ι).piecewise f g = s.piecewise f g := by
  ext
  congr

@[simp]
/--
lemma `piecewise_eq_of_mem` / 引理 `piecewise_eq_of_mem`

English:
lemma piecewise_eq_of_mem
  given: {i : ι} (hi : i in s)
  statement: s.piecewise f g i = f i
  proof: by
  simp [piecewise, hi]

@[simp]

中文:
引理 piecewise_eq_of_mem
  条件: {i : ι} (hi : i in s)
  结论: s.piecewise f g i = f i
  证明: by
  simp [piecewise, hi]

@[simp]

Depends on / 依赖: piecewise
-/
lemma piecewise_eq_of_mem {i : ι} (hi : i in s) : s.piecewise f g i = f i := by
  simp [piecewise, hi]

@[simp]
/--
lemma `piecewise_eq_of_notMem` / 引理 `piecewise_eq_of_notMem`

English:
lemma piecewise_eq_of_notMem
  given: {i : ι} (hi : i ∉ s)
  statement: s.piecewise f g i = g i
  proof: by
  simp [piecewise, hi]

中文:
引理 piecewise_eq_of_notMem
  条件: {i : ι} (hi : i ∉ s)
  结论: s.piecewise f g i = g i
  证明: by
  simp [piecewise, hi]

Depends on / 依赖: piecewise
-/
lemma piecewise_eq_of_notMem {i : ι} (hi : i ∉ s) : s.piecewise f g i = g i := by
  simp [piecewise, hi]

/--
lemma `piecewise_congr` / 引理 `piecewise_congr`

English:
lemma piecewise_congr
  statement: {f f' g g' : forall i, π i} (hf : forall i in s, f i = f' i)
  proof: funext fun i => if_ctx_congr Iff.rfl (hf i) (hg i)

@[simp]

中文:
引理 piecewise_congr
  结论: {f f' g g' : 对任意 i, π i} (hf : 对任意 i in s, f i = f' i)
  证明: funext fun i => if_ctx_congr Iff.rfl (hf i) (hg i)

@[simp]

Depends on / 依赖: Iff.rfl, if_ctx_congr
-/
lemma piecewise_congr {f f' g g' : forall i, π i} (hf : forall i in s, f i = f' i)
    (hg : forall i ∉ s, g i = g' i) : s.piecewise f g = s.piecewise f' g' :=
  funext fun i => if_ctx_congr Iff.rfl (hf i) (hg i)

@[simp]
/--
lemma `piecewise_insert_of_ne` / 引理 `piecewise_insert_of_ne`

English:
lemma piecewise_insert_of_ne
  statement: [DecidableEq ι] {i j : ι} [forall i, Decidable (i in insert j s)]
  proof: by simp [piecewise, h]

中文:
引理 piecewise_insert_of_ne
  结论: [DecidableEq ι] {i j : ι} [对任意 i, Decidable (i in insert j s)]
  证明: by simp [piecewise, h]

Depends on / 依赖: piecewise
-/
lemma piecewise_insert_of_ne [DecidableEq ι] {i j : ι} [forall i, Decidable (i in insert j s)]
    (h : i != j) : (insert j s).piecewise f g i = s.piecewise f g i := by simp [piecewise, h]

/--
lemma `piecewise_insert` / 引理 `piecewise_insert`

English:
lemma piecewise_insert
  given: [DecidableEq ι] (j : ι) [forall i, Decidable (i in insert j s)]
  proof: by
  simp only [← piecewise_coe, ← Set.piecewise_insert]
  ext
  congr
  simp

中文:
引理 piecewise_insert
  条件: [DecidableEq ι] (j : ι) [对任意 i, Decidable (i in insert j s)]
  证明: by
  simp only [← piecewise_coe, ← Set.piecewise_insert]
  ext
  congr
  simp

Depends on / 依赖: Set.piecewise_insert, piecewise_coe, piecewise_insert
-/
lemma piecewise_insert [DecidableEq ι] (j : ι) [forall i, Decidable (i in insert j s)] :
    (insert j s).piecewise f g = update (s.piecewise f g) j (f j) := by
  simp only [← piecewise_coe, ← Set.piecewise_insert]
  ext
  congr
  simp

/--
lemma `piecewise_cases` / 引理 `piecewise_cases`

English:
lemma piecewise_cases
  given: {i} (p : π i -> Prop) (hf : p (f i)) (hg : p (g i))
  proof: by
  by_cases hi : i in s <;> simpa [hi]

中文:
引理 piecewise_cases
  条件: {i} (p : π i -> 命题) (hf : p (f i)) (hg : p (g i))
  证明: by
  by_cases hi : i in s <;> simpa [hi]
-/
lemma piecewise_cases {i} (p : π i -> Prop) (hf : p (f i)) (hg : p (g i)) :
    p (s.piecewise f g i) := by
  by_cases hi : i in s <;> simpa [hi]

/--
lemma `piecewise_singleton` / 引理 `piecewise_singleton`

English:
lemma piecewise_singleton
  given: [DecidableEq ι] (i : ι)
  statement: piecewise {i} f g = update g i (f i)
  proof: by
  rw [← insert_empty_eq]; rw [piecewise_insert]; rw [piecewise_empty]

中文:
引理 piecewise_singleton
  条件: [DecidableEq ι] (i : ι)
  结论: piecewise {i} f g = update g i (f i)
  证明: by
  rw [← insert_empty_eq]; rw [piecewise_insert]; rw [piecewise_empty]

Depends on / 依赖: insert_empty_eq, piecewise_empty, piecewise_insert
-/
lemma piecewise_singleton [DecidableEq ι] (i : ι) : piecewise {i} f g = update g i (f i) := by
  rw [← insert_empty_eq]; rw [piecewise_insert]; rw [piecewise_empty]

/--
lemma `piecewise_piecewise_of_subset_left` / 引理 `piecewise_piecewise_of_subset_left`

English:
lemma piecewise_piecewise_of_subset_left
  statement: {s t : Finset ι} [forall i, Decidable (i in s)]
  proof: s.piecewise_congr (fun _i hi => piecewise_eq_of_mem _ _ _ (h hi)) fun _ _ => rfl

@[simp]

中文:
引理 piecewise_piecewise_of_subset_left
  结论: {s t : Finset ι} [对任意 i, Decidable (i in s)]
  证明: s.piecewise_congr (fun _i hi => piecewise_eq_of_mem _ _ _ (h hi)) fun _ _ => rfl

@[simp]

Depends on / 依赖: piecewise_congr, piecewise_eq_of_mem, s.piecewise_congr
-/
lemma piecewise_piecewise_of_subset_left {s t : Finset ι} [forall i, Decidable (i in s)]
    [forall i, Decidable (i in t)] (h : s subseteq t) (f₁ f₂ g : forall a, π a) :
    s.piecewise (t.piecewise f₁ f₂) g = s.piecewise f₁ g :=
  s.piecewise_congr (fun _i hi => piecewise_eq_of_mem _ _ _ (h hi)) fun _ _ => rfl

@[simp]
/--
lemma `piecewise_idem_left` / 引理 `piecewise_idem_left`

English:
lemma piecewise_idem_left
  given: (f₁ f₂ g : forall a, π a)
  proof: piecewise_piecewise_of_subset_left (Subset.refl _) _ _ _

中文:
引理 piecewise_idem_left
  条件: (f₁ f₂ g : 对任意 a, π a)
  证明: piecewise_piecewise_of_subset_left (Subset.refl _) _ _ _

Depends on / 依赖: Subset, Subset.refl, piecewise_piecewise_of_subset_left
-/
lemma piecewise_idem_left (f₁ f₂ g : forall a, π a) :
    s.piecewise (s.piecewise f₁ f₂) g = s.piecewise f₁ g :=
  piecewise_piecewise_of_subset_left (Subset.refl _) _ _ _

/--
lemma `piecewise_piecewise_of_subset_right` / 引理 `piecewise_piecewise_of_subset_right`

English:
lemma piecewise_piecewise_of_subset_right
  statement: {s t : Finset ι} [forall i, Decidable (i in s)]
  proof: s.piecewise_congr (fun _ _ => rfl) fun _i hi => t.piecewise_eq_of_notMem _ _ (mt (@h _) hi)

@[simp]

中文:
引理 piecewise_piecewise_of_subset_right
  结论: {s t : Finset ι} [对任意 i, Decidable (i in s)]
  证明: s.piecewise_congr (fun _ _ => rfl) fun _i hi => t.piecewise_eq_of_notMem _ _ (mt (@h _) hi)

@[simp]

Depends on / 依赖: piecewise_congr, piecewise_eq_of_notMem, s.piecewise_congr, t.piecewise_eq_of_notMem
-/
lemma piecewise_piecewise_of_subset_right {s t : Finset ι} [forall i, Decidable (i in s)]
    [forall i, Decidable (i in t)] (h : t subseteq s) (f g₁ g₂ : forall a, π a) :
    s.piecewise f (t.piecewise g₁ g₂) = s.piecewise f g₂ :=
  s.piecewise_congr (fun _ _ => rfl) fun _i hi => t.piecewise_eq_of_notMem _ _ (mt (@h _) hi)

@[simp]
/--
lemma `piecewise_idem_right` / 引理 `piecewise_idem_right`

English:
lemma piecewise_idem_right
  given: (f g₁ g₂ : forall a, π a)
  proof: piecewise_piecewise_of_subset_right (Subset.refl _) f g₁ g₂

中文:
引理 piecewise_idem_right
  条件: (f g₁ g₂ : 对任意 a, π a)
  证明: piecewise_piecewise_of_subset_right (Subset.refl _) f g₁ g₂

Depends on / 依赖: Subset, Subset.refl, piecewise_piecewise_of_subset_right
-/
lemma piecewise_idem_right (f g₁ g₂ : forall a, π a) :
    s.piecewise f (s.piecewise g₁ g₂) = s.piecewise f g₂ :=
  piecewise_piecewise_of_subset_right (Subset.refl _) f g₁ g₂

/--
lemma `update_eq_piecewise` / 引理 `update_eq_piecewise`

English:
lemma update_eq_piecewise
  given: {β : Type*} [DecidableEq ι] (f : ι -> β) (i : ι) (v : β)
  proof: (piecewise_singleton (fun _ => v) _ _).symm

中文:
引理 update_eq_piecewise
  条件: {β : 类型} [DecidableEq ι] (f : ι -> β) (i : ι) (v : β)
  证明: (piecewise_singleton (fun _ => v) _ _).symm

Depends on / 依赖: piecewise_singleton
-/
lemma update_eq_piecewise {β : Type*} [DecidableEq ι] (f : ι -> β) (i : ι) (v : β) :
    update f i v = piecewise (singleton i) (fun _ => v) f :=
  (piecewise_singleton (fun _ => v) _ _).symm

/--
lemma `update_piecewise` / 引理 `update_piecewise`

English:
lemma update_piecewise
  given: [DecidableEq ι] (i : ι) (v : π i)
  proof: by
  ext j
  rcases em (j = i) with (rfl | hj) <;> by_cases hs : j in s <;> simp [*]

中文:
引理 update_piecewise
  条件: [DecidableEq ι] (i : ι) (v : π i)
  证明: by
  ext j
  rcases em (j = i) with (rfl | hj) <;> by_cases hs : j in s <;> simp [*]
-/
lemma update_piecewise [DecidableEq ι] (i : ι) (v : π i) :
    update (s.piecewise f g) i v = s.piecewise (update f i v) (update g i v) := by
  ext j
  rcases em (j = i) with (rfl | hj) <;> by_cases hs : j in s <;> simp [*]

/--
lemma `update_piecewise_of_mem` / 引理 `update_piecewise_of_mem`

English:
lemma update_piecewise_of_mem
  given: [DecidableEq ι] {i : ι} (hi : i in s) (v : π i)
  proof: by
  rw [update_piecewise]
  refine s.piecewise_congr (fun _ _ => rfl) fun j hj => update_of_ne ?_ ..
  exact fun h => hj (h.symm ▸ hi)

中文:
引理 update_piecewise_of_mem
  条件: [DecidableEq ι] {i : ι} (hi : i in s) (v : π i)
  证明: by
  rw [update_piecewise]
  refine s.piecewise_congr (fun _ _ => rfl) fun j hj => update_of_ne ?_ ..
  exact fun h => hj (h.symm ▸ hi)

Depends on / 依赖: h.symm, piecewise_congr, s.piecewise_congr, update_of_ne, update_piecewise
-/
lemma update_piecewise_of_mem [DecidableEq ι] {i : ι} (hi : i in s) (v : π i) :
    update (s.piecewise f g) i v = s.piecewise (update f i v) g := by
  rw [update_piecewise]
  refine s.piecewise_congr (fun _ _ => rfl) fun j hj => update_of_ne ?_ ..
  exact fun h => hj (h.symm ▸ hi)

/--
lemma `update_piecewise_of_notMem` / 引理 `update_piecewise_of_notMem`

English:
lemma update_piecewise_of_notMem
  given: [DecidableEq ι] {i : ι} (hi : i ∉ s) (v : π i)
  proof: by
  rw [update_piecewise]
  refine s.piecewise_congr (fun j hj => update_of_ne ?_ ..) fun _ _ => rfl
  exact fun h => hi (h ▸ hj)

中文:
引理 update_piecewise_of_notMem
  条件: [DecidableEq ι] {i : ι} (hi : i ∉ s) (v : π i)
  证明: by
  rw [update_piecewise]
  refine s.piecewise_congr (fun j hj => update_of_ne ?_ ..) fun _ _ => rfl
  exact fun h => hi (h ▸ hj)

Depends on / 依赖: piecewise_congr, s.piecewise_congr, update_of_ne, update_piecewise
-/
lemma update_piecewise_of_notMem [DecidableEq ι] {i : ι} (hi : i ∉ s) (v : π i) :
    update (s.piecewise f g) i v = s.piecewise f (update g i v) := by
  rw [update_piecewise]
  refine s.piecewise_congr (fun j hj => update_of_ne ?_ ..) fun _ _ => rfl
  exact fun h => hi (h ▸ hj)

/--
lemma `piecewise_same` / 引理 `piecewise_same`

English:
lemma piecewise_same
  statement: s.piecewise f f = f
  proof: by
  ext i
  by_cases h : i in s <;> simp [h]

中文:
引理 piecewise_same
  结论: s.piecewise f f = f
  证明: by
  ext i
  by_cases h : i in s <;> simp [h]
-/
lemma piecewise_same : s.piecewise f f = f := by
  ext i
  by_cases h : i in s <;> simp [h]

section Fintype
variable [Fintype ι]

@[simp]
/--
lemma `piecewise_univ` / 引理 `piecewise_univ`

English:
lemma piecewise_univ
  given: [forall i, Decidable (i in (univ : Finset ι))] (f g : forall i, π i)
  proof: by
  ext i
  simp [piecewise]

中文:
引理 piecewise_univ
  条件: [对任意 i, Decidable (i in (univ : Finset ι))] (f g : 对任意 i, π i)
  证明: by
  ext i
  simp [piecewise]

Depends on / 依赖: piecewise
-/
lemma piecewise_univ [forall i, Decidable (i in (univ : Finset ι))] (f g : forall i, π i) :
    univ.piecewise f g = f := by
  ext i
  simp [piecewise]

/--
lemma `piecewise_compl` / 引理 `piecewise_compl`

English:
lemma piecewise_compl
  statement: [DecidableEq ι] (s : Finset ι) [forall i, Decidable (i in s)]
  proof: by
  ext i
  simp [piecewise]

@[simp]

中文:
引理 piecewise_compl
  结论: [DecidableEq ι] (s : Finset ι) [对任意 i, Decidable (i in s)]
  证明: by
  ext i
  simp [piecewise]

@[simp]

Depends on / 依赖: piecewise
-/
lemma piecewise_compl [DecidableEq ι] (s : Finset ι) [forall i, Decidable (i in s)]
    [forall i, Decidable (i in sᶜ)] (f g : forall i, π i) :
    sᶜ.piecewise f g = s.piecewise g f := by
  ext i
  simp [piecewise]

@[simp]
/--
lemma `piecewise_erase_univ` / 引理 `piecewise_erase_univ`

English:
lemma piecewise_erase_univ
  given: [DecidableEq ι] (i : ι) (f g : forall i, π i)
  proof: by
  rw [← compl_singleton]; rw [piecewise_compl]; rw [piecewise_singleton]

中文:
引理 piecewise_erase_univ
  条件: [DecidableEq ι] (i : ι) (f g : 对任意 i, π i)
  证明: by
  rw [← compl_singleton]; rw [piecewise_compl]; rw [piecewise_singleton]

Depends on / 依赖: compl_singleton, piecewise_compl, piecewise_singleton
-/
lemma piecewise_erase_univ [DecidableEq ι] (i : ι) (f g : forall i, π i) :
    (Finset.univ.erase i).piecewise f g = Function.update f i (g i) := by
  rw [← compl_singleton]; rw [piecewise_compl]; rw [piecewise_singleton]

end Fintype

variable {π : ι -> Type*} {t : Set ι} {t' : forall i, Set (π i)} {f g f' g' h : forall i, π i}

/--
lemma `piecewise_mem_set_pi` / 引理 `piecewise_mem_set_pi`

English:
lemma piecewise_mem_set_pi
  given: (hf : f in Set.pi t t') (hg : g in Set.pi t t')
  proof: by
  rw [← piecewise_coe]; exact Set.piecewise_mem_pi (↑s) hf hg

中文:
引理 piecewise_mem_set_pi
  条件: (hf : f in Set.pi t t') (hg : g in Set.pi t t')
  证明: by
  rw [← piecewise_coe]; exact Set.piecewise_mem_pi (↑s) hf hg

Depends on / 依赖: Set.piecewise_mem_pi, piecewise_coe, piecewise_mem_pi
-/
lemma piecewise_mem_set_pi (hf : f in Set.pi t t') (hg : g in Set.pi t t') :
    s.piecewise f g in Set.pi t t' := by
  rw [← piecewise_coe]; exact Set.piecewise_mem_pi (↑s) hf hg

variable [forall i, Preorder (π i)]

/--
lemma `piecewise_le_of_le_of_le` / 引理 `piecewise_le_of_le_of_le`

English:
lemma piecewise_le_of_le_of_le
  given: (hf : f <= h) (hg : g <= h)
  statement: s.piecewise f g <= h
  proof: fun x =>
  piecewise_cases s f g (· <= h x) (hf x) (hg x)

中文:
引理 piecewise_le_of_le_of_le
  条件: (hf : f <= h) (hg : g <= h)
  结论: s.piecewise f g <= h
  证明: fun x =>
  piecewise_cases s f g (· <= h x) (hf x) (hg x)
-/
lemma piecewise_le_of_le_of_le (hf : f <= h) (hg : g <= h) : s.piecewise f g <= h := fun x =>
  piecewise_cases s f g (· <= h x) (hf x) (hg x)

/--
lemma `le_piecewise_of_le_of_le` / 引理 `le_piecewise_of_le_of_le`

English:
lemma le_piecewise_of_le_of_le
  given: (hf : h <= f) (hg : h <= g)
  statement: h <= s.piecewise f g
  proof: fun x =>
  piecewise_cases s f g (fun y => h x <= y) (hf x) (hg x)

中文:
引理 le_piecewise_of_le_of_le
  条件: (hf : h <= f) (hg : h <= g)
  结论: h <= s.piecewise f g
  证明: fun x =>
  piecewise_cases s f g (fun y => h x <= y) (hf x) (hg x)
-/
lemma le_piecewise_of_le_of_le (hf : h <= f) (hg : h <= g) : h <= s.piecewise f g := fun x =>
  piecewise_cases s f g (fun y => h x <= y) (hf x) (hg x)

/--
lemma `piecewise_le_piecewise'` / 引理 `piecewise_le_piecewise'`

English:
lemma piecewise_le_piecewise'
  given: (hf : forall x in s, f x <= f' x) (hg : forall x ∉ s, g x <= g' x)
  proof: fun x => by by_cases hx : x in s <;> simp [*]

中文:
引理 piecewise_le_piecewise'
  条件: (hf : 对任意 x in s, f x <= f' x) (hg : 对任意 x ∉ s, g x <= g' x)
  证明: fun x => by by_cases hx : x in s <;> simp [*]
-/
lemma piecewise_le_piecewise' (hf : forall x in s, f x <= f' x) (hg : forall x ∉ s, g x <= g' x) :
    s.piecewise f g <= s.piecewise f' g' := fun x => by by_cases hx : x in s <;> simp [*]

/--
lemma `piecewise_le_piecewise` / 引理 `piecewise_le_piecewise`

English:
lemma piecewise_le_piecewise
  given: (hf : f <= f') (hg : g <= g')
  statement: s.piecewise f g <= s.piecewise f' g'
  proof: s.piecewise_le_piecewise' (fun x _ => hf x) fun x _ => hg x

中文:
引理 piecewise_le_piecewise
  条件: (hf : f <= f') (hg : g <= g')
  结论: s.piecewise f g <= s.piecewise f' g'
  证明: s.piecewise_le_piecewise' (fun x _ => hf x) fun x _ => hg x

Depends on / 依赖: piecewise_le_piecewise, s.piecewise_le_piecewise
-/
lemma piecewise_le_piecewise (hf : f <= f') (hg : g <= g') : s.piecewise f g <= s.piecewise f' g' :=
  s.piecewise_le_piecewise' (fun x _ => hf x) fun x _ => hg x

/--
lemma `piecewise_mem_Icc_of_mem_of_mem` / 引理 `piecewise_mem_Icc_of_mem_of_mem`

English:
lemma piecewise_mem_Icc_of_mem_of_mem
  given: (hf : f in Set.Icc f' g') (hg : g in Set.Icc f' g')
  proof: ⟨le_piecewise_of_le_of_le _ hf.1 hg.1, piecewise_le_of_le_of_le _ hf.2 hg.2⟩

中文:
引理 piecewise_mem_Icc_of_mem_of_mem
  条件: (hf : f in Set.Icc f' g') (hg : g in Set.Icc f' g')
  证明: ⟨le_piecewise_of_le_of_le _ hf.1 hg.1, piecewise_le_of_le_of_le _ hf.2 hg.2⟩

Depends on / 依赖: le_piecewise_of_le_of_le, piecewise_le_of_le_of_le
-/
lemma piecewise_mem_Icc_of_mem_of_mem (hf : f in Set.Icc f' g') (hg : g in Set.Icc f' g') :
    s.piecewise f g in Set.Icc f' g' :=
  ⟨le_piecewise_of_le_of_le _ hf.1 hg.1, piecewise_le_of_le_of_le _ hf.2 hg.2⟩

/--
lemma `piecewise_mem_Icc` / 引理 `piecewise_mem_Icc`

English:
lemma piecewise_mem_Icc
  given: (h : f <= g)
  statement: s.piecewise f g in Set.Icc f g
  proof: piecewise_mem_Icc_of_mem_of_mem _ (Set.left_mem_Icc.2 h) (Set.right_mem_Icc.2 h)

中文:
引理 piecewise_mem_Icc
  条件: (h : f <= g)
  结论: s.piecewise f g in Set.Icc f g
  证明: piecewise_mem_Icc_of_mem_of_mem _ (Set.left_mem_Icc.2 h) (Set.right_mem_Icc.2 h)

Depends on / 依赖: Set.left_mem_Icc, Set.right_mem_Icc, left_mem_Icc, piecewise_mem_Icc_of_mem_of_mem, right_mem_Icc
-/
lemma piecewise_mem_Icc (h : f <= g) : s.piecewise f g in Set.Icc f g :=
  piecewise_mem_Icc_of_mem_of_mem _ (Set.left_mem_Icc.2 h) (Set.right_mem_Icc.2 h)

/--
lemma `piecewise_mem_Icc'` / 引理 `piecewise_mem_Icc'`

English:
lemma piecewise_mem_Icc'
  given: (h : g <= f)
  statement: s.piecewise f g in Set.Icc g f
  proof: piecewise_mem_Icc_of_mem_of_mem _ (Set.right_mem_Icc.2 h) (Set.left_mem_Icc.2 h)

中文:
引理 piecewise_mem_Icc'
  条件: (h : g <= f)
  结论: s.piecewise f g in Set.Icc g f
  证明: piecewise_mem_Icc_of_mem_of_mem _ (Set.right_mem_Icc.2 h) (Set.left_mem_Icc.2 h)

Depends on / 依赖: Set.left_mem_Icc, Set.right_mem_Icc, left_mem_Icc, piecewise_mem_Icc_of_mem_of_mem, right_mem_Icc
-/
lemma piecewise_mem_Icc' (h : g <= f) : s.piecewise f g in Set.Icc g f :=
  piecewise_mem_Icc_of_mem_of_mem _ (Set.right_mem_Icc.2 h) (Set.left_mem_Icc.2 h)

end Finset
