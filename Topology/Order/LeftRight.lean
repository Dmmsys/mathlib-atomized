/-
Copyright (c) 2021 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Order.Antichain
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Order.Interval.Set.UnorderedInterval

/-!
# Left and right continuity

In this file we prove a few lemmas about left and right continuous functions:

* `continuousWithinAt_Ioi_iff_Ici`: two definitions of right continuity
  (with `(a, ∞)` and with `[a, ∞)`) are equivalent;
* `continuousWithinAt_Iio_iff_Iic`: two definitions of left continuity
  (with `(-∞, a)` and with `(-∞, a]`) are equivalent;
* `continuousAt_iff_continuous_left_right`, `continuousAt_iff_continuous_left'_right'` :
  a function is continuous at `a` if and only if it is left and right continuous at `a`.

## Tags

left continuous, right continuous
-/

public section


open Set Filter Topology

section Preorder

variable {α : Type*} [TopologicalSpace α] [Preorder α]

@[to_dual frequently_gt_nhds]
/--
lemma `frequently_lt_nhds` / 引理 `frequently_lt_nhds`

English:
lemma frequently_lt_nhds
  given: (a : α) [NeBot (𝓝[<] a)]
  statement: existsᶠ x in 𝓝 a, x < a
  proof: frequently_iff_neBot.2 ‹_›

@[to_dual exists_gt]

中文:
引理 frequently_lt_nhds
  条件: (a : α) [NeBot (𝓝[<] a)]
  结论: 存在ᶠ x in 𝓝 a, x < a
  证明: frequently_iff_neBot.2 ‹_›

@[to_dual exists_gt]

Depends on / 依赖: frequently_iff_neBot
-/
lemma frequently_lt_nhds (a : α) [NeBot (𝓝[<] a)] : existsᶠ x in 𝓝 a, x < a :=
  frequently_iff_neBot.2 ‹_›

@[to_dual exists_gt]
/--
theorem `Filter.Eventually.exists_lt` / 定理 `Filter.Eventually.exists_lt`

English:
theorem Filter.Eventually.exists_lt
  statement: {a : α} [NeBot (𝓝[<] a)] {p : α -> Prop}
  proof: ((frequently_lt_nhds a).and_eventually h).exists

@[to_dual]

中文:
定理 Filter.Eventually.exists_lt
  结论: {a : α} [NeBot (𝓝[<] a)] {p : α -> 命题}
  证明: ((frequently_lt_nhds a).and_eventually h).exists

@[to_dual]

Depends on / 依赖: and_eventually, frequently_lt_nhds
-/
theorem Filter.Eventually.exists_lt {a : α} [NeBot (𝓝[<] a)] {p : α -> Prop}
    (h : forallᶠ x in 𝓝 a, p x) : exists b < a, p b :=
  ((frequently_lt_nhds a).and_eventually h).exists

@[to_dual]
/--
theorem `nhdsWithin_Ici_neBot` / 定理 `nhdsWithin_Ici_neBot`

English:
theorem nhdsWithin_Ici_neBot
  given: {a b : α} (H₂ : a <= b)
  statement: NeBot (𝓝[Ici a] b)
  proof: nhdsWithin_neBot_of_mem H₂

@[to_dual]

中文:
定理 nhdsWithin_Ici_neBot
  条件: {a b : α} (H₂ : a <= b)
  结论: NeBot (𝓝[Ici a] b)
  证明: nhdsWithin_neBot_of_mem H₂

@[to_dual]

Depends on / 依赖: nhdsWithin_neBot_of_mem
-/
theorem nhdsWithin_Ici_neBot {a b : α} (H₂ : a <= b) : NeBot (𝓝[Ici a] b) :=
  nhdsWithin_neBot_of_mem H₂

@[to_dual]
/--
Instance `nhdsLE_neBot` / 实例 `nhdsLE_neBot`

English:
instance nhdsLE_neBot
  signature: (a : α)
  body: nhdsWithin_Iic_neBot (le_refl a)

@[to_dual]

中文:
实例 nhdsLE_neBot
  签名: (a : α)
  定义体: nhdsWithin_Iic_neBot (le_refl a)

@[to_dual]

Depends on / 依赖: le_refl, nhdsWithin_Iic_neBot
-/
instance nhdsLE_neBot (a : α) : NeBot (𝓝[<=] a) := nhdsWithin_Iic_neBot (le_refl a)

@[to_dual]
/--
theorem `nhdsLT_le_nhdsNE` / 定理 `nhdsLT_le_nhdsNE`

English:
theorem nhdsLT_le_nhdsNE
  given: (a : α)
  statement: 𝓝[<] a <= 𝓝[!=] a
  proof: nhdsWithin_mono a fun _ => ne_of_lt

中文:
定理 nhdsLT_le_nhdsNE
  条件: (a : α)
  结论: 𝓝[<] a <= 𝓝[!=] a
  证明: nhdsWithin_mono a fun _ => ne_of_lt

Depends on / 依赖: ne_of_lt, nhdsWithin_mono
-/
theorem nhdsLT_le_nhdsNE (a : α) : 𝓝[<] a <= 𝓝[!=] a :=
  nhdsWithin_mono a fun _ => ne_of_lt

-- TODO: add instances for `NeBot (𝓝[<] x)` on (indexed) product types

/--
lemma `IsAntichain.interior_eq_empty` / 引理 `IsAntichain.interior_eq_empty`

English:
lemma IsAntichain.interior_eq_empty
  statement: [forall x : α, (𝓝[<] x).NeBot] {s : Set α}
  proof: by
  refine eq_empty_of_forall_notMem fun x hx => ?_
  have : forallᶠ y in 𝓝 x, y in s := mem_interior_iff_mem_nhds.1 hx
  rcases this.exists_lt with ⟨y, hyx, hys⟩
  exact hs hys (interior_subset hx) hyx.ne hyx.le

中文:
引理 IsAntichain.interior_eq_empty
  结论: [对任意 x : α, (𝓝[<] x).NeBot] {s : Set α}
  证明: by
  refine eq_empty_of_forall_notMem fun x hx => ?_
  have : forallᶠ y in 𝓝 x, y in s := mem_interior_iff_mem_nhds.1 hx
  rcases this.exists_lt with ⟨y, hyx, hys⟩
  exact hs hys (interior_subset hx) hyx.ne hyx.le

Depends on / 依赖: eq_empty_of_forall_notMem, exists_lt, hyx.le, hyx.ne, interior_subset, mem_interior_iff_mem_nhds, this.exists_lt
-/
lemma IsAntichain.interior_eq_empty [forall x : α, (𝓝[<] x).NeBot] {s : Set α}
    (hs : IsAntichain (· <= ·) s) : interior s = ∅ := by
  refine eq_empty_of_forall_notMem fun x hx => ?_
  have : forallᶠ y in 𝓝 x, y in s := mem_interior_iff_mem_nhds.1 hx
  rcases this.exists_lt with ⟨y, hyx, hys⟩
  exact hs hys (interior_subset hx) hyx.ne hyx.le

/--
lemma `IsAntichain.interior_eq_empty'` / 引理 `IsAntichain.interior_eq_empty'`

English:
lemma IsAntichain.interior_eq_empty'
  statement: [forall x : α, (𝓝[>] x).NeBot] {s : Set α}
  proof: have : forall x : αᵒᵈ, NeBot (𝓝[<] x) := ‹_›
  hs.to_dual.interior_eq_empty

中文:
引理 IsAntichain.interior_eq_empty'
  结论: [对任意 x : α, (𝓝[>] x).NeBot] {s : Set α}
  证明: have : forall x : αᵒᵈ, NeBot (𝓝[<] x) := ‹_›
  hs.to_dual.interior_eq_empty

Depends on / 依赖: hs.to_dual.interior_eq_empty, interior_eq_empty, to_dual
-/
lemma IsAntichain.interior_eq_empty' [forall x : α, (𝓝[>] x).NeBot] {s : Set α}
    (hs : IsAntichain (· <= ·) s) : interior s = ∅ :=
  have : forall x : αᵒᵈ, NeBot (𝓝[<] x) := ‹_›
  hs.to_dual.interior_eq_empty

end Preorder

section PartialOrder

variable {α β : Type*} [TopologicalSpace α] [PartialOrder α] [TopologicalSpace β]

@[to_dual]
/--
theorem `continuousWithinAt_Ioi_iff_Ici` / 定理 `continuousWithinAt_Ioi_iff_Ici`

English:
theorem continuousWithinAt_Ioi_iff_Ici
  given: {a : α} {f : α -> β}
  proof: by
  simp only [← Ici_sdiff_left, continuousWithinAt_sdiff_self]

@[to_dual]

中文:
定理 continuousWithinAt_Ioi_iff_Ici
  条件: {a : α} {f : α -> β}
  证明: by
  simp only [← Ici_sdiff_left, continuousWithinAt_sdiff_self]

@[to_dual]

Depends on / 依赖: Ici_sdiff_left, continuousWithinAt_sdiff_self
-/
theorem continuousWithinAt_Ioi_iff_Ici {a : α} {f : α -> β} :
    ContinuousWithinAt f (Ioi a) a ↔ ContinuousWithinAt f (Ici a) a := by
  simp only [← Ici_sdiff_left, continuousWithinAt_sdiff_self]

@[to_dual]
/--
theorem `continuousWithinAt_inter_Ioi_iff_Ici` / 定理 `continuousWithinAt_inter_Ioi_iff_Ici`

English:
theorem continuousWithinAt_inter_Ioi_iff_Ici
  given: {a : α} {f : α -> β} {s : Set α}
  proof: by
  simp [← Ici_sdiff_left, ← inter_sdiff_assoc, continuousWithinAt_sdiff_self]

中文:
定理 continuousWithinAt_inter_Ioi_iff_Ici
  条件: {a : α} {f : α -> β} {s : Set α}
  证明: by
  simp [← Ici_sdiff_left, ← inter_sdiff_assoc, continuousWithinAt_sdiff_self]

Depends on / 依赖: Ici_sdiff_left, continuousWithinAt_sdiff_self, inter_sdiff_assoc
-/
theorem continuousWithinAt_inter_Ioi_iff_Ici {a : α} {f : α -> β} {s : Set α} :
    ContinuousWithinAt f (s inter Ioi a) a ↔ ContinuousWithinAt f (s inter Ici a) a := by
  simp [← Ici_sdiff_left, ← inter_sdiff_assoc, continuousWithinAt_sdiff_self]

end PartialOrder

section TopologicalSpace

variable {α β : Type*} [TopologicalSpace α] [LinearOrder α] [TopologicalSpace β] {s : Set α}

@[to_dual nhdsGE_sup_nhdsLE]
/--
theorem `nhdsLE_sup_nhdsGE` / 定理 `nhdsLE_sup_nhdsGE`

English:
theorem nhdsLE_sup_nhdsGE
  given: (a : α)
  statement: 𝓝[<=] a ⊔ 𝓝[>=] a = 𝓝 a
  proof: by
  rw [← nhdsWithin_union]; rw [Iic_union_Ici]; rw [nhdsWithin_univ]

@[to_dual nhdsWithinGE_sup_nhdsWithinLE]

中文:
定理 nhdsLE_sup_nhdsGE
  条件: (a : α)
  结论: 𝓝[<=] a ⊔ 𝓝[>=] a = 𝓝 a
  证明: by
  rw [← nhdsWithin_union]; rw [Iic_union_Ici]; rw [nhdsWithin_univ]

@[to_dual nhdsWithinGE_sup_nhdsWithinLE]

Depends on / 依赖: Iic_union_Ici, nhdsWithin_union, nhdsWithin_univ
-/
theorem nhdsLE_sup_nhdsGE (a : α) : 𝓝[<=] a ⊔ 𝓝[>=] a = 𝓝 a := by
  rw [← nhdsWithin_union]; rw [Iic_union_Ici]; rw [nhdsWithin_univ]

@[to_dual nhdsWithinGE_sup_nhdsWithinLE]
/--
theorem `nhdsWithinLE_sup_nhdsWithinGE` / 定理 `nhdsWithinLE_sup_nhdsWithinGE`

English:
theorem nhdsWithinLE_sup_nhdsWithinGE
  given: (a : α)
  statement: 𝓝[s inter Iic a] a ⊔ 𝓝[s inter Ici a] a = 𝓝[s] a
  proof: by
  rw [← nhdsWithin_union]; rw [← inter_union_distrib_left]; rw [Iic_union_Ici]; rw [inter_univ]

@[to_dual nhdsGT_sup_nhdsLE]

中文:
定理 nhdsWithinLE_sup_nhdsWithinGE
  条件: (a : α)
  结论: 𝓝[s inter Iic a] a ⊔ 𝓝[s inter Ici a] a = 𝓝[s] a
  证明: by
  rw [← nhdsWithin_union]; rw [← inter_union_distrib_left]; rw [Iic_union_Ici]; rw [inter_univ]

@[to_dual nhdsGT_sup_nhdsLE]

Depends on / 依赖: Iic_union_Ici, inter_union_distrib_left, inter_univ, nhdsWithin_union
-/
theorem nhdsWithinLE_sup_nhdsWithinGE (a : α) : 𝓝[s inter Iic a] a ⊔ 𝓝[s inter Ici a] a = 𝓝[s] a := by
  rw [← nhdsWithin_union]; rw [← inter_union_distrib_left]; rw [Iic_union_Ici]; rw [inter_univ]

@[to_dual nhdsGT_sup_nhdsLE]
/--
theorem `nhdsLT_sup_nhdsGE` / 定理 `nhdsLT_sup_nhdsGE`

English:
theorem nhdsLT_sup_nhdsGE
  given: (a : α)
  statement: 𝓝[<] a ⊔ 𝓝[>=] a = 𝓝 a
  proof: by
  rw [← nhdsWithin_union]; rw [Iio_union_Ici]; rw [nhdsWithin_univ]

@[to_dual nhdsWithinGT_sup_nhdsWithinLE]

中文:
定理 nhdsLT_sup_nhdsGE
  条件: (a : α)
  结论: 𝓝[<] a ⊔ 𝓝[>=] a = 𝓝 a
  证明: by
  rw [← nhdsWithin_union]; rw [Iio_union_Ici]; rw [nhdsWithin_univ]

@[to_dual nhdsWithinGT_sup_nhdsWithinLE]

Depends on / 依赖: Iio_union_Ici, nhdsWithin_union, nhdsWithin_univ
-/
theorem nhdsLT_sup_nhdsGE (a : α) : 𝓝[<] a ⊔ 𝓝[>=] a = 𝓝 a := by
  rw [← nhdsWithin_union]; rw [Iio_union_Ici]; rw [nhdsWithin_univ]

@[to_dual nhdsWithinGT_sup_nhdsWithinLE]
/--
theorem `nhdsWithinLT_sup_nhdsWithinGE` / 定理 `nhdsWithinLT_sup_nhdsWithinGE`

English:
theorem nhdsWithinLT_sup_nhdsWithinGE
  given: (a : α)
  statement: 𝓝[s inter Iio a] a ⊔ 𝓝[s inter Ici a] a = 𝓝[s] a
  proof: by
  rw [← nhdsWithin_union]; rw [← inter_union_distrib_left]; rw [Iio_union_Ici]; rw [inter_univ]

@[to_dual nhdsGE_sup_nhdsLT]

中文:
定理 nhdsWithinLT_sup_nhdsWithinGE
  条件: (a : α)
  结论: 𝓝[s inter Iio a] a ⊔ 𝓝[s inter Ici a] a = 𝓝[s] a
  证明: by
  rw [← nhdsWithin_union]; rw [← inter_union_distrib_left]; rw [Iio_union_Ici]; rw [inter_univ]

@[to_dual nhdsGE_sup_nhdsLT]

Depends on / 依赖: Iio_union_Ici, inter_union_distrib_left, inter_univ, nhdsWithin_union
-/
theorem nhdsWithinLT_sup_nhdsWithinGE (a : α) : 𝓝[s inter Iio a] a ⊔ 𝓝[s inter Ici a] a = 𝓝[s] a := by
  rw [← nhdsWithin_union]; rw [← inter_union_distrib_left]; rw [Iio_union_Ici]; rw [inter_univ]

@[to_dual nhdsGE_sup_nhdsLT]
/--
theorem `nhdsLE_sup_nhdsGT` / 定理 `nhdsLE_sup_nhdsGT`

English:
theorem nhdsLE_sup_nhdsGT
  given: (a : α)
  statement: 𝓝[<=] a ⊔ 𝓝[>] a = 𝓝 a
  proof: by
  rw [← nhdsWithin_union]; rw [Iic_union_Ioi]; rw [nhdsWithin_univ]

@[to_dual nhdsWithinGE_sup_nhdsWithinLT]

中文:
定理 nhdsLE_sup_nhdsGT
  条件: (a : α)
  结论: 𝓝[<=] a ⊔ 𝓝[>] a = 𝓝 a
  证明: by
  rw [← nhdsWithin_union]; rw [Iic_union_Ioi]; rw [nhdsWithin_univ]

@[to_dual nhdsWithinGE_sup_nhdsWithinLT]

Depends on / 依赖: Iic_union_Ioi, nhdsWithin_union, nhdsWithin_univ
-/
theorem nhdsLE_sup_nhdsGT (a : α) : 𝓝[<=] a ⊔ 𝓝[>] a = 𝓝 a := by
  rw [← nhdsWithin_union]; rw [Iic_union_Ioi]; rw [nhdsWithin_univ]

@[to_dual nhdsWithinGE_sup_nhdsWithinLT]
/--
theorem `nhdsWithinLE_sup_nhdsWithinGT` / 定理 `nhdsWithinLE_sup_nhdsWithinGT`

English:
theorem nhdsWithinLE_sup_nhdsWithinGT
  given: (a : α)
  statement: 𝓝[s inter Iic a] a ⊔ 𝓝[s inter Ioi a] a = 𝓝[s] a
  proof: by
  rw [← nhdsWithin_union]; rw [← inter_union_distrib_left]; rw [Iic_union_Ioi]; rw [inter_univ]

@[to_dual nhdsGT_sup_nhdsLT]

中文:
定理 nhdsWithinLE_sup_nhdsWithinGT
  条件: (a : α)
  结论: 𝓝[s inter Iic a] a ⊔ 𝓝[s inter Ioi a] a = 𝓝[s] a
  证明: by
  rw [← nhdsWithin_union]; rw [← inter_union_distrib_left]; rw [Iic_union_Ioi]; rw [inter_univ]

@[to_dual nhdsGT_sup_nhdsLT]

Depends on / 依赖: Iic_union_Ioi, inter_union_distrib_left, inter_univ, nhdsWithin_union
-/
theorem nhdsWithinLE_sup_nhdsWithinGT (a : α) : 𝓝[s inter Iic a] a ⊔ 𝓝[s inter Ioi a] a = 𝓝[s] a := by
  rw [← nhdsWithin_union]; rw [← inter_union_distrib_left]; rw [Iic_union_Ioi]; rw [inter_univ]

@[to_dual nhdsGT_sup_nhdsLT]
/--
theorem `nhdsLT_sup_nhdsGT` / 定理 `nhdsLT_sup_nhdsGT`

English:
theorem nhdsLT_sup_nhdsGT
  given: (a : α)
  statement: 𝓝[<] a ⊔ 𝓝[>] a = 𝓝[!=] a
  proof: by
  rw [← nhdsWithin_union]; rw [Iio_union_Ioi]

@[to_dual nhdsWithinGT_sup_nhdsWithinLT]

中文:
定理 nhdsLT_sup_nhdsGT
  条件: (a : α)
  结论: 𝓝[<] a ⊔ 𝓝[>] a = 𝓝[!=] a
  证明: by
  rw [← nhdsWithin_union]; rw [Iio_union_Ioi]

@[to_dual nhdsWithinGT_sup_nhdsWithinLT]

Depends on / 依赖: Iio_union_Ioi, nhdsWithin_union
-/
theorem nhdsLT_sup_nhdsGT (a : α) : 𝓝[<] a ⊔ 𝓝[>] a = 𝓝[!=] a := by
  rw [← nhdsWithin_union]; rw [Iio_union_Ioi]

@[to_dual nhdsWithinGT_sup_nhdsWithinLT]
/--
theorem `nhdsWithinLT_sup_nhdsWithinGT` / 定理 `nhdsWithinLT_sup_nhdsWithinGT`

English:
theorem nhdsWithinLT_sup_nhdsWithinGT
  given: (a : α)
  proof: by
  rw [← nhdsWithin_union]; rw [← inter_union_distrib_left]; rw [Iio_union_Ioi]; rw [compl_eq_univ_sdiff]; rw [inter_sdiff_left_comm]; rw [univ_inter]

@[to_dual nhdsLT_sup_nhdsWithin_singleton]

中文:
定理 nhdsWithinLT_sup_nhdsWithinGT
  条件: (a : α)
  证明: by
  rw [← nhdsWithin_union]; rw [← inter_union_distrib_left]; rw [Iio_union_Ioi]; rw [compl_eq_univ_sdiff]; rw [inter_sdiff_left_comm]; rw [univ_inter]

@[to_dual nhdsLT_sup_nhdsWithin_singleton]

Depends on / 依赖: Iio_union_Ioi, compl_eq_univ_sdiff, inter_sdiff_left_comm, inter_union_distrib_left, nhdsWithin_union, univ_inter
-/
theorem nhdsWithinLT_sup_nhdsWithinGT (a : α) :
    𝓝[s inter Iio a] a ⊔ 𝓝[s inter Ioi a] a = 𝓝[s \ {a}] a := by
  rw [← nhdsWithin_union]; rw [← inter_union_distrib_left]; rw [Iio_union_Ioi]; rw [compl_eq_univ_sdiff]; rw [inter_sdiff_left_comm]; rw [univ_inter]

@[to_dual nhdsLT_sup_nhdsWithin_singleton]
/--
lemma `nhdsGT_sup_nhdsWithin_singleton` / 引理 `nhdsGT_sup_nhdsWithin_singleton`

English:
lemma nhdsGT_sup_nhdsWithin_singleton
  given: (a : α)
  proof: by
  simp only [union_singleton, Ioi_insert, ← nhdsWithin_union]

中文:
引理 nhdsGT_sup_nhdsWithin_singleton
  条件: (a : α)
  证明: by
  simp only [union_singleton, Ioi_insert, ← nhdsWithin_union]

Depends on / 依赖: Ioi_insert, nhdsWithin_union, union_singleton
-/
lemma nhdsGT_sup_nhdsWithin_singleton (a : α) :
    𝓝[>] a ⊔ 𝓝[{a}] a = 𝓝[>=] a := by
  simp only [union_singleton, Ioi_insert, ← nhdsWithin_union]

/--
lemma `nhdsWithin_uIoo_left_le_nhdsNE` / 引理 `nhdsWithin_uIoo_left_le_nhdsNE`

English:
lemma nhdsWithin_uIoo_left_le_nhdsNE
  given: {a b : α}
  statement: 𝓝[uIoo a b] a <= 𝓝[!=] a
  proof: nhdsWithin_mono _ (by simp)

中文:
引理 nhdsWithin_uIoo_left_le_nhdsNE
  条件: {a b : α}
  结论: 𝓝[uIoo a b] a <= 𝓝[!=] a
  证明: nhdsWithin_mono _ (by simp)

Depends on / 依赖: nhdsWithin_mono
-/
lemma nhdsWithin_uIoo_left_le_nhdsNE {a b : α} : 𝓝[uIoo a b] a <= 𝓝[!=] a :=
  nhdsWithin_mono _ (by simp)

/--
lemma `nhdsWithin_uIoo_right_le_nhdsNE` / 引理 `nhdsWithin_uIoo_right_le_nhdsNE`

English:
lemma nhdsWithin_uIoo_right_le_nhdsNE
  given: {a b : α}
  statement: 𝓝[uIoo a b] b <= 𝓝[!=] b
  proof: nhdsWithin_mono _ (by simp)

@[to_dual none]

中文:
引理 nhdsWithin_uIoo_right_le_nhdsNE
  条件: {a b : α}
  结论: 𝓝[uIoo a b] b <= 𝓝[!=] b
  证明: nhdsWithin_mono _ (by simp)

@[to_dual none]

Depends on / 依赖: nhdsWithin_mono
-/
lemma nhdsWithin_uIoo_right_le_nhdsNE {a b : α} : 𝓝[uIoo a b] b <= 𝓝[!=] b :=
  nhdsWithin_mono _ (by simp)

@[to_dual none]
/--
theorem `continuousAt_iff_continuous_left_right` / 定理 `continuousAt_iff_continuous_left_right`

English:
theorem continuousAt_iff_continuous_left_right
  given: {a : α} {f : α -> β}
  proof: by
  simp only [ContinuousWithinAt, ContinuousAt, ← tendsto_sup, nhdsLE_sup_nhdsGE]

@[to_dual none]

中文:
定理 continuousAt_iff_continuous_left_right
  条件: {a : α} {f : α -> β}
  证明: by
  simp only [ContinuousWithinAt, ContinuousAt, ← tendsto_sup, nhdsLE_sup_nhdsGE]

@[to_dual none]

Depends on / 依赖: ContinuousAt, ContinuousWithinAt, nhdsLE_sup_nhdsGE, tendsto_sup
-/
theorem continuousAt_iff_continuous_left_right {a : α} {f : α -> β} :
    ContinuousAt f a ↔ ContinuousWithinAt f (Iic a) a ∧ ContinuousWithinAt f (Ici a) a := by
  simp only [ContinuousWithinAt, ContinuousAt, ← tendsto_sup, nhdsLE_sup_nhdsGE]

@[to_dual none]
/--
theorem `continuousAt_iff_continuous_left'_right'` / 定理 `continuousAt_iff_continuous_left'_right'`

English:
theorem continuousAt_iff_continuous_left'_right'
  given: {a : α} {f : α -> β}
  proof: by
  rw [continuousWithinAt_Ioi_iff_Ici]; rw [continuousWithinAt_Iio_iff_Iic]; rw [continuousAt_iff_continuous_left_right]

@[to_dual none]

中文:
定理 continuousAt_iff_continuous_left'_right'
  条件: {a : α} {f : α -> β}
  证明: by
  rw [continuousWithinAt_Ioi_iff_Ici]; rw [continuousWithinAt_Iio_iff_Iic]; rw [continuousAt_iff_continuous_left_right]

@[to_dual none]

Depends on / 依赖: continuousAt_iff_continuous_left_right, continuousWithinAt_Iio_iff_Iic, continuousWithinAt_Ioi_iff_Ici
-/
theorem continuousAt_iff_continuous_left'_right' {a : α} {f : α -> β} :
    ContinuousAt f a ↔ ContinuousWithinAt f (Iio a) a ∧ ContinuousWithinAt f (Ioi a) a := by
  rw [continuousWithinAt_Ioi_iff_Ici]; rw [continuousWithinAt_Iio_iff_Iic]; rw [continuousAt_iff_continuous_left_right]

@[to_dual none]
/--
theorem `continuousWithinAt_iff_continuous_left_right` / 定理 `continuousWithinAt_iff_continuous_left_right`

English:
theorem continuousWithinAt_iff_continuous_left_right
  given: {a : α} {f : α -> β}
  proof: by
  simp only [ContinuousWithinAt, ← tendsto_sup, nhdsWithinLE_sup_nhdsWithinGE]

@[to_dual none]

中文:
定理 continuousWithinAt_iff_continuous_left_right
  条件: {a : α} {f : α -> β}
  证明: by
  simp only [ContinuousWithinAt, ← tendsto_sup, nhdsWithinLE_sup_nhdsWithinGE]

@[to_dual none]

Depends on / 依赖: ContinuousWithinAt, nhdsWithinLE_sup_nhdsWithinGE, tendsto_sup
-/
theorem continuousWithinAt_iff_continuous_left_right {a : α} {f : α -> β} :
    ContinuousWithinAt f s a ↔
      ContinuousWithinAt f (s inter Iic a) a ∧ ContinuousWithinAt f (s inter Ici a) a := by
  simp only [ContinuousWithinAt, ← tendsto_sup, nhdsWithinLE_sup_nhdsWithinGE]

@[to_dual none]
/--
theorem `continuousWithinAt_iff_continuous_left'_right'` / 定理 `continuousWithinAt_iff_continuous_left'_right'`

English:
theorem continuousWithinAt_iff_continuous_left'_right'
  given: {a : α} {f : α -> β}
  proof: by
  rw [continuousWithinAt_inter_Ioi_iff_Ici]; rw [continuousWithinAt_inter_Iio_iff_Iic]; rw [continuousWithinAt_iff_continuous_left_right]

中文:
定理 continuousWithinAt_iff_continuous_left'_right'
  条件: {a : α} {f : α -> β}
  证明: by
  rw [continuousWithinAt_inter_Ioi_iff_Ici]; rw [continuousWithinAt_inter_Iio_iff_Iic]; rw [continuousWithinAt_iff_continuous_left_right]

Depends on / 依赖: continuousWithinAt_iff_continuous_left_right, continuousWithinAt_inter_Iio_iff_Iic, continuousWithinAt_inter_Ioi_iff_Ici
-/
theorem continuousWithinAt_iff_continuous_left'_right' {a : α} {f : α -> β} :
    ContinuousWithinAt f s a ↔
      ContinuousWithinAt f (s inter Iio a) a ∧ ContinuousWithinAt f (s inter Ioi a) a := by
  rw [continuousWithinAt_inter_Ioi_iff_Ici]; rw [continuousWithinAt_inter_Iio_iff_Iic]; rw [continuousWithinAt_iff_continuous_left_right]

end TopologicalSpace
