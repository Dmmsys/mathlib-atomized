/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Topology.Bornology.Basic

/-!
# Bornology structure on products and subtypes

In this file we define `Bornology` and `BoundedSpace` instances on `α × β`, `Π i, X i`, and
`{x // p x}`. We also prove basic lemmas about `Bornology.cobounded` and `Bornology.IsBounded`
on these types.
-/

public section


open Set Filter Bornology Function

open Filter

variable {α β ι : Type*} {X : ι -> Type*} [Bornology α] [Bornology β]
  [forall i, Bornology (X i)]

/--
Instance `Prod.instBornology` / 实例 `Prod.instBornology`

English:
instance Prod.instBornology
  signature: : Bornology (α × β) where
  body: (cobounded α).coprod (cobounded β)
  le_cofinite :=
    @coprod_cofinite α β ▸ coprod_mono ‹Bornology α›.le_cofinite ‹Bornology β›.le_cofinite

中文:
实例 积类型.instBornology
  签名: : 有界结构 (α × β) where
  定义体: (cobounded α).coprod (cobounded β)
  le_cofinite :=
    @coprod_cofinite α β ▸ coprod_mono ‹Bornology α›.le_cofinite ‹Bornology β›.le_cofinite

Depends on / 依赖: cobounded, coprod
-/
instance Prod.instBornology : Bornology (α × β) where
  cobounded := (cobounded α).coprod (cobounded β)
  le_cofinite :=
    @coprod_cofinite α β ▸ coprod_mono ‹Bornology α›.le_cofinite ‹Bornology β›.le_cofinite

/--
Instance `Pi.instBornology` / 实例 `Pi.instBornology`

English:
instance Pi.instBornology
  signature: : Bornology (forall i, X i) where
  body: Filter.coprodᵢ fun i => cobounded (X i)
  le_cofinite := iSup_le fun _ => (comap_mono (Bornology.le_cofinite _)).trans (comap_cofinite_le _)

中文:
实例 依赖函数类型.instBornology
  签名: : 有界结构 (对任意 i, X i) where
  定义体: Filter.coprodᵢ fun i => cobounded (X i)
  le_cofinite := iSup_le fun _ => (comap_mono (Bornology.le_cofinite _)).trans (comap_cofinite_le _)

Depends on / 依赖: Filter, Filter.coprod, cobounded
-/
instance Pi.instBornology : Bornology (forall i, X i) where
  cobounded := Filter.coprodᵢ fun i => cobounded (X i)
  le_cofinite := iSup_le fun _ => (comap_mono (Bornology.le_cofinite _)).trans (comap_cofinite_le _)

/--
Definition of `Bornology.induced` / `Bornology.induced` 的定义

English:
abbreviation Bornology.induced
  signature: {α β : Type*} [Bornology β] (f : α -> β)
  body: comap f (cobounded β)
  le_cofinite := (comap_mono (Bornology.le_cofinite β)).trans (comap_cofinite_le _)

中文:
缩写 有界结构.induced
  签名: {α β : 类型} [有界结构 β] (f : α -> β)
  定义体: comap f (cobounded β)
  le_cofinite := (comap_mono (Bornology.le_cofinite β)).trans (comap_cofinite_le _)

Depends on / 依赖: cobounded
-/
abbrev Bornology.induced {α β : Type*} [Bornology β] (f : α -> β) : Bornology α where
  cobounded := comap f (cobounded β)
  le_cofinite := (comap_mono (Bornology.le_cofinite β)).trans (comap_cofinite_le _)

instance {p : α -> Prop} : Bornology (Subtype p) :=
  Bornology.induced (Subtype.val : Subtype p -> α)

namespace Bornology



/--
theorem `cobounded_prod` / 定理 `cobounded_prod`

English:
theorem cobounded_prod
  statement: cobounded (α × β) = (cobounded α).coprod (cobounded β)
  proof: rfl

中文:
定理 cobounded_prod
  结论: cobounded (α × β) = (cobounded α).coprod (cobounded β)
  证明: rfl
-/
theorem cobounded_prod : cobounded (α × β) = (cobounded α).coprod (cobounded β) :=
  rfl

/--
theorem `isBounded_image_fst_and_snd` / 定理 `isBounded_image_fst_and_snd`

English:
theorem isBounded_image_fst_and_snd
  given: {s : Set (α × β)}
  proof: compl_mem_coprod.symm

中文:
定理 isBounded_image_fst_and_snd
  条件: {s : 集合 (α × β)}
  证明: compl_mem_coprod.symm

Depends on / 依赖: compl_mem_coprod, compl_mem_coprod.symm
-/
theorem isBounded_image_fst_and_snd {s : Set (α × β)} :
    IsBounded (Prod.fst '' s) ∧ IsBounded (Prod.snd '' s) ↔ IsBounded s :=
  compl_mem_coprod.symm

/--
lemma `IsBounded.image_fst` / 引理 `IsBounded.image_fst`

English:
lemma IsBounded.image_fst
  given: {s : Set (α × β)} (hs : IsBounded s)
  statement: IsBounded (Prod.fst '' s)
  proof: (isBounded_image_fst_and_snd.2 hs).1

中文:
引理 IsBounded.image_fst
  条件: {s : 集合 (α × β)} (hs : IsBounded s)
  结论: IsBounded (积类型.fst '' s)
  证明: (isBounded_image_fst_and_snd.2 hs).1

Depends on / 依赖: isBounded_image_fst_and_snd
-/
lemma IsBounded.image_fst {s : Set (α × β)} (hs : IsBounded s) : IsBounded (Prod.fst '' s) :=
  (isBounded_image_fst_and_snd.2 hs).1

/--
lemma `IsBounded.image_snd` / 引理 `IsBounded.image_snd`

English:
lemma IsBounded.image_snd
  given: {s : Set (α × β)} (hs : IsBounded s)
  statement: IsBounded (Prod.snd '' s)
  proof: (isBounded_image_fst_and_snd.2 hs).2

中文:
引理 IsBounded.image_snd
  条件: {s : 集合 (α × β)} (hs : IsBounded s)
  结论: IsBounded (积类型.snd '' s)
  证明: (isBounded_image_fst_and_snd.2 hs).2

Depends on / 依赖: isBounded_image_fst_and_snd
-/
lemma IsBounded.image_snd {s : Set (α × β)} (hs : IsBounded s) : IsBounded (Prod.snd '' s) :=
  (isBounded_image_fst_and_snd.2 hs).2

variable {s : Set α} {t : Set β} {S : forall i, Set (X i)}

/--
theorem `IsBounded.fst_of_prod` / 定理 `IsBounded.fst_of_prod`

English:
theorem IsBounded.fst_of_prod
  given: (h : IsBounded (s ×ˢ t)) (ht : t.Nonempty)
  statement: IsBounded s
  proof: fst_image_prod s ht ▸ h.image_fst

中文:
定理 IsBounded.fst_of_prod
  条件: (h : IsBounded (s ×ˢ t)) (ht : t.非空)
  结论: IsBounded s
  证明: fst_image_prod s ht ▸ h.image_fst

Depends on / 依赖: fst_image_prod, h.image_fst, image_fst
-/
theorem IsBounded.fst_of_prod (h : IsBounded (s ×ˢ t)) (ht : t.Nonempty) : IsBounded s :=
  fst_image_prod s ht ▸ h.image_fst

/--
theorem `IsBounded.snd_of_prod` / 定理 `IsBounded.snd_of_prod`

English:
theorem IsBounded.snd_of_prod
  given: (h : IsBounded (s ×ˢ t)) (hs : s.Nonempty)
  statement: IsBounded t
  proof: snd_image_prod hs t ▸ h.image_snd

中文:
定理 IsBounded.snd_of_prod
  条件: (h : IsBounded (s ×ˢ t)) (hs : s.非空)
  结论: IsBounded t
  证明: snd_image_prod hs t ▸ h.image_snd

Depends on / 依赖: h.image_snd, image_snd, snd_image_prod
-/
theorem IsBounded.snd_of_prod (h : IsBounded (s ×ˢ t)) (hs : s.Nonempty) : IsBounded t :=
  snd_image_prod hs t ▸ h.image_snd

/--
theorem `IsBounded.prod` / 定理 `IsBounded.prod`

English:
theorem IsBounded.prod
  given: (hs : IsBounded s) (ht : IsBounded t)
  statement: IsBounded (s ×ˢ t)
  proof: isBounded_image_fst_and_snd.1
⟨hs.subset fst_image_prod_subset _ _, ht.subset snd_image_prod_subset _ _⟩

中文:
定理 IsBounded.乘积
  条件: (hs : IsBounded s) (ht : IsBounded t)
  结论: IsBounded (s ×ˢ t)
  证明: isBounded_image_fst_and_snd.1
⟨hs.subset fst_image_prod_subset _ _, ht.subset snd_image_prod_subset _ _⟩

Depends on / 依赖: fst_image_prod_subset, hs.subset, ht.subset, isBounded_image_fst_and_snd, snd_image_prod_subset, subset
-/
theorem IsBounded.prod (hs : IsBounded s) (ht : IsBounded t) : IsBounded (s ×ˢ t) :=
  isBounded_image_fst_and_snd.1
⟨hs.subset fst_image_prod_subset _ _, ht.subset snd_image_prod_subset _ _⟩

/--
theorem `isBounded_prod_of_nonempty` / 定理 `isBounded_prod_of_nonempty`

English:
theorem isBounded_prod_of_nonempty
  given: (hne : Set.Nonempty (s ×ˢ t))
  proof: ⟨fun h => ⟨h.fst_of_prod hne.snd, h.snd_of_prod hne.fst⟩, fun h => h.1.prod h.2⟩

中文:
定理 isBounded_prod_of_nonempty
  条件: (hne : 集合.非空 (s ×ˢ t))
  证明: ⟨fun h => ⟨h.fst_of_prod hne.snd, h.snd_of_prod hne.fst⟩, fun h => h.1.prod h.2⟩

Depends on / 依赖: fst_of_prod, h.fst_of_prod, h.snd_of_prod, hne.fst, hne.snd, snd_of_prod
-/
theorem isBounded_prod_of_nonempty (hne : Set.Nonempty (s ×ˢ t)) :
    IsBounded (s ×ˢ t) ↔ IsBounded s ∧ IsBounded t :=
  ⟨fun h => ⟨h.fst_of_prod hne.snd, h.snd_of_prod hne.fst⟩, fun h => h.1.prod h.2⟩

/--
theorem `isBounded_prod` / 定理 `isBounded_prod`

English:
theorem isBounded_prod
  statement: IsBounded (s ×ˢ t) ↔ s = ∅ ∨ t = ∅ ∨ IsBounded s ∧ IsBounded t
  proof: by
  rcases s.eq_empty_or_nonempty with (rfl | hs); · simp
  rcases t.eq_empty_or_nonempty with (rfl | ht); · simp
  simp only [hs.ne_empty, ht.ne_empty, isBounded_prod_of_nonempty (hs.prod ht), false_or]

中文:
定理 isBounded_prod
  结论: IsBounded (s ×ˢ t) ↔ s = ∅ ∨ t = ∅ ∨ IsBounded s ∧ IsBounded t
  证明: by
  rcases s.eq_empty_or_nonempty with (rfl | hs); · simp
  rcases t.eq_empty_or_nonempty with (rfl | ht); · simp
  simp only [hs.ne_empty, ht.ne_empty, isBounded_prod_of_nonempty (hs.prod ht), false_or]

Depends on / 依赖: eq_empty_or_nonempty, false_or, hs.ne_empty, hs.prod, ht.ne_empty, isBounded_prod_of_nonempty, ne_empty, s.eq_empty_or_nonempty, t.eq_empty_or_nonempty
-/
theorem isBounded_prod : IsBounded (s ×ˢ t) ↔ s = ∅ ∨ t = ∅ ∨ IsBounded s ∧ IsBounded t := by
  rcases s.eq_empty_or_nonempty with (rfl | hs); · simp
  rcases t.eq_empty_or_nonempty with (rfl | ht); · simp
  simp only [hs.ne_empty, ht.ne_empty, isBounded_prod_of_nonempty (hs.prod ht), false_or]

/--
theorem `isBounded_prod_self` / 定理 `isBounded_prod_self`

English:
theorem isBounded_prod_self
  statement: IsBounded (s ×ˢ s) ↔ IsBounded s
  proof: by
  rcases s.eq_empty_or_nonempty with (rfl | hs); · simp
  exact (isBounded_prod_of_nonempty (hs.prod hs)).trans and_self_iff

中文:
定理 isBounded_prod_self
  结论: IsBounded (s ×ˢ s) ↔ IsBounded s
  证明: by
  rcases s.eq_empty_or_nonempty with (rfl | hs); · simp
  exact (isBounded_prod_of_nonempty (hs.prod hs)).trans and_self_iff

Depends on / 依赖: and_self_iff, eq_empty_or_nonempty, hs.prod, isBounded_prod_of_nonempty, s.eq_empty_or_nonempty
-/
theorem isBounded_prod_self : IsBounded (s ×ˢ s) ↔ IsBounded s := by
  rcases s.eq_empty_or_nonempty with (rfl | hs); · simp
  exact (isBounded_prod_of_nonempty (hs.prod hs)).trans and_self_iff



/--
theorem `cobounded_pi` / 定理 `cobounded_pi`

English:
theorem cobounded_pi
  statement: cobounded (forall i, X i) = Filter.coprodᵢ fun i => cobounded (X i)
  proof: rfl

中文:
定理 cobounded_pi
  结论: cobounded (对任意 i, X i) = 滤子.coprodᵢ fun i => cobounded (X i)
  证明: rfl
-/
theorem cobounded_pi : cobounded (forall i, X i) = Filter.coprodᵢ fun i => cobounded (X i) :=
  rfl

/--
theorem `forall_isBounded_image_eval_iff` / 定理 `forall_isBounded_image_eval_iff`

English:
theorem forall_isBounded_image_eval_iff
  given: {s : Set (forall i, X i)}
  proof: compl_mem_coprodᵢ.symm

中文:
定理 对任意_isBounded_image_eval_iff
  条件: {s : 集合 (对任意 i, X i)}
  证明: compl_mem_coprodᵢ.symm
-/
theorem forall_isBounded_image_eval_iff {s : Set (forall i, X i)} :
    (forall i, IsBounded (eval i '' s)) ↔ IsBounded s :=
  compl_mem_coprodᵢ.symm

/--
lemma `IsBounded.image_eval` / 引理 `IsBounded.image_eval`

English:
lemma IsBounded.image_eval
  given: {s : Set (forall i, X i)} (hs : IsBounded s) (i : ι)
  proof: forall_isBounded_image_eval_iff.2 hs i

中文:
引理 IsBounded.image_eval
  条件: {s : 集合 (对任意 i, X i)} (hs : IsBounded s) (i : ι)
  证明: forall_isBounded_image_eval_iff.2 hs i

Depends on / 依赖: forall_isBounded_image_eval_iff
-/
lemma IsBounded.image_eval {s : Set (forall i, X i)} (hs : IsBounded s) (i : ι) :
    IsBounded (eval i '' s) :=
  forall_isBounded_image_eval_iff.2 hs i

/--
theorem `IsBounded.pi` / 定理 `IsBounded.pi`

English:
theorem IsBounded.pi
  given: (h : forall i, IsBounded (S i))
  statement: IsBounded (pi univ S)
  proof: forall_isBounded_image_eval_iff.1 fun i => (h i).subset eval_image_univ_pi_subset

中文:
定理 IsBounded.pi
  条件: (h : 对任意 i, IsBounded (S i))
  结论: IsBounded (pi univ S)
  证明: forall_isBounded_image_eval_iff.1 fun i => (h i).subset eval_image_univ_pi_subset

Depends on / 依赖: eval_image_univ_pi_subset, forall_isBounded_image_eval_iff, subset
-/
theorem IsBounded.pi (h : forall i, IsBounded (S i)) : IsBounded (pi univ S) :=
  forall_isBounded_image_eval_iff.1 fun i => (h i).subset eval_image_univ_pi_subset

/--
theorem `isBounded_pi_of_nonempty` / 定理 `isBounded_pi_of_nonempty`

English:
theorem isBounded_pi_of_nonempty
  given: (hne : (pi univ S).Nonempty)
  proof: ⟨fun H i => @eval_image_univ_pi _ _ _ i hne ▸ forall_isBounded_image_eval_iff.2 H i, IsBounded.pi⟩

中文:
定理 isBounded_pi_of_nonempty
  条件: (hne : (pi univ S).非空)
  证明: ⟨fun H i => @eval_image_univ_pi _ _ _ i hne ▸ forall_isBounded_image_eval_iff.2 H i, IsBounded.pi⟩

Depends on / 依赖: IsBounded, IsBounded.pi, eval_image_univ_pi, forall_isBounded_image_eval_iff
-/
theorem isBounded_pi_of_nonempty (hne : (pi univ S).Nonempty) :
    IsBounded (pi univ S) ↔ forall i, IsBounded (S i) :=
  ⟨fun H i => @eval_image_univ_pi _ _ _ i hne ▸ forall_isBounded_image_eval_iff.2 H i, IsBounded.pi⟩

/--
theorem `isBounded_pi` / 定理 `isBounded_pi`

English:
theorem isBounded_pi
  statement: IsBounded (pi univ S) ↔ (exists i, S i = ∅) ∨ forall i, IsBounded (S i)
  proof: by
  by_cases hne : exists i, S i = ∅
  · simp [hne, univ_pi_eq_empty_iff.2 hne]
  · simp only [hne, false_or]
    simp only [not_exists, ← nonempty_iff_ne_empty, ← univ_pi_nonempty_iff] at hne
    exact isBounded_pi_of_nonempty hne

中文:
定理 isBounded_pi
  结论: IsBounded (pi univ S) ↔ (存在 i, S i = ∅) ∨ 对任意 i, IsBounded (S i)
  证明: by
  by_cases hne : exists i, S i = ∅
  · simp [hne, univ_pi_eq_empty_iff.2 hne]
  · simp only [hne, false_or]
    simp only [not_exists, ← nonempty_iff_ne_empty, ← univ_pi_nonempty_iff] at hne
    exact isBounded_pi_of_nonempty hne

Depends on / 依赖: false_or, isBounded_pi_of_nonempty, nonempty_iff_ne_empty, not_exists, univ_pi_eq_empty_iff, univ_pi_nonempty_iff
-/
theorem isBounded_pi : IsBounded (pi univ S) ↔ (exists i, S i = ∅) ∨ forall i, IsBounded (S i) := by
  by_cases hne : exists i, S i = ∅
  · simp [hne, univ_pi_eq_empty_iff.2 hne]
  · simp only [hne, false_or]
    simp only [not_exists, ← nonempty_iff_ne_empty, ← univ_pi_nonempty_iff] at hne
    exact isBounded_pi_of_nonempty hne



/--
theorem `isBounded_induced` / 定理 `isBounded_induced`

English:
theorem isBounded_induced
  given: {α β : Type*} [Bornology β] {f : α -> β} {s : Set α}
  proof: compl_mem_comap

中文:
定理 isBounded_induced
  条件: {α β : 类型} [有界结构 β] {f : α -> β} {s : 集合 α}
  证明: compl_mem_comap

Depends on / 依赖: compl_mem_comap
-/
theorem isBounded_induced {α β : Type*} [Bornology β] {f : α -> β} {s : Set α} :
    @IsBounded α (Bornology.induced f) s ↔ IsBounded (f '' s) :=
  compl_mem_comap

/--
theorem `isBounded_image_subtype_val` / 定理 `isBounded_image_subtype_val`

English:
theorem isBounded_image_subtype_val
  given: {p : α -> Prop} {s : Set { x // p x }}
  proof: isBounded_induced.symm

中文:
定理 isBounded_image_subtype_val
  条件: {p : α -> 命题} {s : 集合 { x // p x }}
  证明: isBounded_induced.symm

Depends on / 依赖: isBounded_induced, isBounded_induced.symm
-/
theorem isBounded_image_subtype_val {p : α -> Prop} {s : Set { x // p x }} :
    IsBounded (Subtype.val '' s) ↔ IsBounded s :=
  isBounded_induced.symm

end Bornology

/-!
### Bounded spaces
-/


open Bornology

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [BoundedSpace
  signature: α] [BoundedSpace β] : BoundedSpace (α × β)
  body: by
  simp [← cobounded_eq_bot_iff, cobounded_prod]

中文:
实例 [有界空间
  签名: α] [有界空间 β] : 有界空间 (α × β)
  定义体: by
  simp [← cobounded_eq_bot_iff, cobounded_prod]

Depends on / 依赖: cobounded_eq_bot_iff, cobounded_prod
-/
instance [BoundedSpace α] [BoundedSpace β] : BoundedSpace (α × β) := by
  simp [← cobounded_eq_bot_iff, cobounded_prod]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, BoundedSpace (X i)] : BoundedSpace (forall i, X i)
  body: by
  simp [← cobounded_eq_bot_iff, cobounded_pi]

中文:
实例 [对任意
  签名: i, 有界空间 (X i)] : 有界空间 (对任意 i, X i)
  定义体: by
  simp [← cobounded_eq_bot_iff, cobounded_pi]

Depends on / 依赖: cobounded_eq_bot_iff, cobounded_pi
-/
instance [forall i, BoundedSpace (X i)] : BoundedSpace (forall i, X i) := by
  simp [← cobounded_eq_bot_iff, cobounded_pi]

/--
theorem `boundedSpace_induced_iff` / 定理 `boundedSpace_induced_iff`

English:
theorem boundedSpace_induced_iff
  given: {α β : Type*} [Bornology β] {f : α -> β}
  proof: by
  rw [← @isBounded_univ]; rw [isBounded_induced]; rw [image_univ]

中文:
定理 boundedSpace_induced_iff
  条件: {α β : 类型} [有界结构 β] {f : α -> β}
  证明: by
  rw [← @isBounded_univ]; rw [isBounded_induced]; rw [image_univ]

Depends on / 依赖: image_univ, isBounded_induced, isBounded_univ
-/
theorem boundedSpace_induced_iff {α β : Type*} [Bornology β] {f : α -> β} :
    @BoundedSpace α (Bornology.induced f) ↔ IsBounded (range f) := by
  rw [← @isBounded_univ]; rw [isBounded_induced]; rw [image_univ]

/--
theorem `boundedSpace_subtype_iff` / 定理 `boundedSpace_subtype_iff`

English:
theorem boundedSpace_subtype_iff
  given: {p : α -> Prop}
  proof: by
  rw [boundedSpace_induced_iff]; rw [Subtype.range_coe_subtype]

中文:
定理 boundedSpace_subtype_iff
  条件: {p : α -> 命题}
  证明: by
  rw [boundedSpace_induced_iff]; rw [Subtype.range_coe_subtype]

Depends on / 依赖: Subtype, Subtype.range_coe_subtype, boundedSpace_induced_iff, range_coe_subtype
-/
theorem boundedSpace_subtype_iff {p : α -> Prop} :
    BoundedSpace (Subtype p) ↔ IsBounded { x | p x } := by
  rw [boundedSpace_induced_iff]; rw [Subtype.range_coe_subtype]

/--
theorem `boundedSpace_val_set_iff` / 定理 `boundedSpace_val_set_iff`

English:
theorem boundedSpace_val_set_iff
  given: {s : Set α}
  statement: BoundedSpace s ↔ IsBounded s
  proof: boundedSpace_subtype_iff

alias ⟨_, Bornology.IsBounded.boundedSpace_subtype⟩ := boundedSpace_subtype_iff

alias ⟨_, Bornology.IsBounded.boundedSpace_val⟩ := boundedSpace_val_set_iff

中文:
定理 boundedSpace_val_set_iff
  条件: {s : 集合 α}
  结论: 有界空间 s ↔ IsBounded s
  证明: boundedSpace_subtype_iff

alias ⟨_, Bornology.IsBounded.boundedSpace_subtype⟩ := boundedSpace_subtype_iff

alias ⟨_, Bornology.IsBounded.boundedSpace_val⟩ := boundedSpace_val_set_iff

Depends on / 依赖: boundedSpace_subtype_iff
-/
theorem boundedSpace_val_set_iff {s : Set α} : BoundedSpace s ↔ IsBounded s :=
  boundedSpace_subtype_iff

alias ⟨_, Bornology.IsBounded.boundedSpace_subtype⟩ := boundedSpace_subtype_iff

alias ⟨_, Bornology.IsBounded.boundedSpace_val⟩ := boundedSpace_val_set_iff

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [BoundedSpace
  signature: α] {p
  body: (IsBounded.all { x | p x }).boundedSpace_subtype

中文:
实例 [有界空间
  签名: α] {p
  定义体: (IsBounded.all { x | p x }).boundedSpace_subtype

Depends on / 依赖: IsBounded, IsBounded.all, boundedSpace_subtype
-/
instance [BoundedSpace α] {p : α -> Prop} : BoundedSpace (Subtype p) :=
  (IsBounded.all { x | p x }).boundedSpace_subtype



/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Bornology (Additive α)
  body: ‹Bornology α›

中文:
实例 :
  签名: 有界结构 (加性 α)
  定义体: ‹Bornology α›

Depends on / 依赖: Bornology
-/
instance : Bornology (Additive α) :=
  ‹Bornology α›

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Bornology (Multiplicative α)
  body: ‹Bornology α›

中文:
实例 :
  签名: 有界结构 (Multiplicative α)
  定义体: ‹Bornology α›

Depends on / 依赖: Bornology
-/
instance : Bornology (Multiplicative α) :=
  ‹Bornology α›

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [BoundedSpace
  signature: α] : BoundedSpace (Additive α)
  body: ‹BoundedSpace α›

中文:
实例 [有界空间
  签名: α] : 有界空间 (加性 α)
  定义体: ‹BoundedSpace α›

Depends on / 依赖: BoundedSpace
-/
instance [BoundedSpace α] : BoundedSpace (Additive α) :=
  ‹BoundedSpace α›

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [BoundedSpace
  signature: α] : BoundedSpace (Multiplicative α)
  body: ‹BoundedSpace α›

中文:
实例 [有界空间
  签名: α] : 有界空间 (Multiplicative α)
  定义体: ‹BoundedSpace α›

Depends on / 依赖: BoundedSpace
-/
instance [BoundedSpace α] : BoundedSpace (Multiplicative α) :=
  ‹BoundedSpace α›



/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Bornology αᵒᵈ
  body: ‹Bornology α›

中文:
实例 :
  签名: 有界结构 αᵒᵈ
  定义体: ‹Bornology α›

Depends on / 依赖: Bornology
-/
instance : Bornology αᵒᵈ :=
  ‹Bornology α›

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [BoundedSpace
  signature: α] : BoundedSpace αᵒᵈ
  body: ‹BoundedSpace α›

中文:
实例 [有界空间
  签名: α] : 有界空间 αᵒᵈ
  定义体: ‹BoundedSpace α›

Depends on / 依赖: BoundedSpace
-/
instance [BoundedSpace α] : BoundedSpace αᵒᵈ :=
  ‹BoundedSpace α›
