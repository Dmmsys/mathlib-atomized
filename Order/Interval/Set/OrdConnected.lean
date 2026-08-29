/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Order.Interval.Set.OrderEmbedding
public import Mathlib.Order.Antichain
public import Mathlib.Order.SetNotation

/-!
# Order-connected sets

We say that a set `s : Set α` is `OrdConnected` if for all `x y ∈ s` it includes the
interval `[[x, y]]`. If `α` is a `DenselyOrdered` `ConditionallyCompleteLinearOrder` with
the `OrderTopology`, then this condition is equivalent to `IsPreconnected s`. If `α` is a
linearly ordered field, then this condition is also equivalent to `Convex α s`.

In this file we prove that intersection of a family of `OrdConnected` sets is `OrdConnected` and
that all standard intervals are `OrdConnected`.
-/

@[expose] public section

open scoped Interval
open Set
open OrderDual (toDual ofDual)

namespace Set

section Preorder

variable {α β : Type*} [Preorder α] [Preorder β] {s : Set α}

/--
theorem `OrdConnected.out` / 定理 `OrdConnected.out`

English:
theorem OrdConnected.out
  given: (h : OrdConnected s)
  statement: forall ⦃x⦄ (_ : x in s) ⦃y⦄ (_ : y in s), Icc x y subseteq s
  proof: h.1

中文:
定理 序连通.out
  条件: (h : 序连通 s)
  结论: 对任意 ⦃x⦄ (_ : x in s) ⦃y⦄ (_ : y in s), 闭区间 x y subseteq s
  证明: h.1
-/
theorem OrdConnected.out (h : OrdConnected s) : forall ⦃x⦄ (_ : x in s) ⦃y⦄ (_ : y in s), Icc x y subseteq s :=
  h.1

/--
theorem `ordConnected_def` / 定理 `ordConnected_def`

English:
theorem ordConnected_def
  statement: OrdConnected s ↔ forall ⦃x⦄ (_ : x in s) ⦃y⦄ (_ : y in s), Icc x y subseteq s
  proof: ⟨fun h => h.1, fun h => ⟨h⟩⟩

中文:
定理 ordConnected_def
  结论: 序连通 s ↔ 对任意 ⦃x⦄ (_ : x in s) ⦃y⦄ (_ : y in s), 闭区间 x y subseteq s
  证明: ⟨fun h => h.1, fun h => ⟨h⟩⟩
-/
theorem ordConnected_def : OrdConnected s ↔ forall ⦃x⦄ (_ : x in s) ⦃y⦄ (_ : y in s), Icc x y subseteq s :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

/--
theorem `ordConnected_iff` / 定理 `ordConnected_iff`

English:
theorem ordConnected_iff
  statement: OrdConnected s ↔ forall x in s, forall y in s, x <= y -> Icc x y subseteq s
  proof: ordConnected_def.trans
    ⟨fun hs _ hx _ hy _ => hs hx hy, fun H x hx y hy _ hz => H x hx y hy (le_trans hz.1 hz.2) hz⟩

中文:
定理 ordConnected_iff
  结论: 序连通 s ↔ 对任意 x in s, 对任意 y in s, x <= y -> 闭区间 x y subseteq s
  证明: ordConnected_def.trans
    ⟨fun hs _ hx _ hy _ => hs hx hy, fun H x hx y hy _ hz => H x hx y hy (le_trans hz.1 hz.2) hz⟩

Depends on / 依赖: le_trans, ordConnected_def, ordConnected_def.trans
-/
theorem ordConnected_iff : OrdConnected s ↔ forall x in s, forall y in s, x <= y -> Icc x y subseteq s :=
  ordConnected_def.trans
    ⟨fun hs _ hx _ hy _ => hs hx hy, fun H x hx y hy _ hz => H x hx y hy (le_trans hz.1 hz.2) hz⟩

/--
theorem `ordConnected_of_Ioo` / 定理 `ordConnected_of_Ioo`

English:
theorem ordConnected_of_Ioo
  statement: {α : Type*} [PartialOrder α] {s : Set α}
  proof: by
  rw [ordConnected_iff]
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hxy with (rfl | hxy'); · simpa
  rw [← Ioc_insert_left hxy]; rw [← Ioo_insert_right hxy']
  exact insert_subset_iff.2 ⟨hx, insert_subset_iff.2 ⟨hy, hs x hx y hy hxy'⟩⟩

中文:
定理 ordConnected_of_Ioo
  结论: {α : 类型} [偏序 α] {s : 集合 α}
  证明: by
  rw [ordConnected_iff]
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hxy with (rfl | hxy'); · simpa
  rw [← Ioc_insert_left hxy]; rw [← Ioo_insert_right hxy']
  exact insert_subset_iff.2 ⟨hx, insert_subset_iff.2 ⟨hy, hs x hx y hy hxy'⟩⟩

Depends on / 依赖: Ioc_insert_left, Ioo_insert_right, eq_or_lt_of_le, insert_subset_iff, ordConnected_iff
-/
theorem ordConnected_of_Ioo {α : Type*} [PartialOrder α] {s : Set α}
    (hs : forall x in s, forall y in s, x < y -> Ioo x y subseteq s) : OrdConnected s := by
  rw [ordConnected_iff]
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hxy with (rfl | hxy'); · simpa
  rw [← Ioc_insert_left hxy]; rw [← Ioo_insert_right hxy']
  exact insert_subset_iff.2 ⟨hx, insert_subset_iff.2 ⟨hy, hs x hx y hy hxy'⟩⟩

/--
theorem `OrdConnected.preimage_mono` / 定理 `OrdConnected.preimage_mono`

English:
theorem OrdConnected.preimage_mono
  given: {f : β -> α} (hs : OrdConnected s) (hf : Monotone f)
  proof: ⟨fun _ hx _ hy _ hz => hs.out hx hy ⟨hf hz.1, hf hz.2⟩⟩

中文:
定理 序连通.preimage_mono
  条件: {f : β -> α} (hs : 序连通 s) (hf : 递增 f)
  证明: ⟨fun _ hx _ hy _ hz => hs.out hx hy ⟨hf hz.1, hf hz.2⟩⟩

Depends on / 依赖: hs.out
-/
theorem OrdConnected.preimage_mono {f : β -> α} (hs : OrdConnected s) (hf : Monotone f) :
    OrdConnected (f ⁻¹' s) :=
  ⟨fun _ hx _ hy _ hz => hs.out hx hy ⟨hf hz.1, hf hz.2⟩⟩

/--
theorem `OrdConnected.preimage_anti` / 定理 `OrdConnected.preimage_anti`

English:
theorem OrdConnected.preimage_anti
  given: {f : β -> α} (hs : OrdConnected s) (hf : Antitone f)
  proof: ⟨fun _ hx _ hy _ hz => hs.out hy hx ⟨hf hz.2, hf hz.1⟩⟩

中文:
定理 序连通.preimage_anti
  条件: {f : β -> α} (hs : 序连通 s) (hf : 递减 f)
  证明: ⟨fun _ hx _ hy _ hz => hs.out hy hx ⟨hf hz.2, hf hz.1⟩⟩

Depends on / 依赖: hs.out
-/
theorem OrdConnected.preimage_anti {f : β -> α} (hs : OrdConnected s) (hf : Antitone f) :
    OrdConnected (f ⁻¹' s) :=
  ⟨fun _ hx _ hy _ hz => hs.out hy hx ⟨hf hz.2, hf hz.1⟩⟩

/--
theorem `Icc_subset` / 定理 `Icc_subset`

English:
theorem Icc_subset
  given: (s : Set α) [hs : OrdConnected s] {x y} (hx : x in s) (hy : y in s)
  proof: hs.out hx hy

中文:
定理 Icc_subset
  条件: (s : 集合 α) [hs : 序连通 s] {x y} (hx : x in s) (hy : y in s)
  证明: hs.out hx hy
-/
protected theorem Icc_subset (s : Set α) [hs : OrdConnected s] {x y} (hx : x in s) (hy : y in s) :
    Icc x y subseteq s :=
  hs.out hx hy

end Preorder

end Set

namespace OrderEmbedding

variable {α β : Type*} [Preorder α] [Preorder β]

/--
theorem `image_Icc` / 定理 `image_Icc`

English:
theorem image_Icc
  given: (e : α ↪o β) (he : OrdConnected (range e)) (x y : α)
  proof: by
  rw [← e.preimage_Icc]; rw [image_preimage_eq_inter_range]; rw [inter_eq_left.2 (he.out ⟨_]; rw [rfl⟩ ⟨_]; rw [rfl⟩)]

中文:
定理 image_Icc
  条件: (e : α ↪o β) (he : 序连通 (range e)) (x y : α)
  证明: by
  rw [← e.preimage_Icc]; rw [image_preimage_eq_inter_range]; rw [inter_eq_left.2 (he.out ⟨_]; rw [rfl⟩ ⟨_]; rw [rfl⟩)]

Depends on / 依赖: e.preimage_Icc, he.out, image_preimage_eq_inter_range, inter_eq_left, preimage_Icc
-/
theorem image_Icc (e : α ↪o β) (he : OrdConnected (range e)) (x y : α) :
    e '' Icc x y = Icc (e x) (e y) := by
  rw [← e.preimage_Icc]; rw [image_preimage_eq_inter_range]; rw [inter_eq_left.2 (he.out ⟨_]; rw [rfl⟩ ⟨_]; rw [rfl⟩)]

/--
theorem `image_Ico` / 定理 `image_Ico`

English:
theorem image_Ico
  given: (e : α ↪o β) (he : OrdConnected (range e)) (x y : α)
  proof: by
  rw [← e.preimage_Ico]; rw [image_preimage_eq_inter_range]; rw [inter_eq_left.2 Ico_subset_Icc_self.trans he.out ⟨_]; rw [rfl⟩ ⟨_]; rw [rfl⟩]

中文:
定理 image_Ico
  条件: (e : α ↪o β) (he : 序连通 (range e)) (x y : α)
  证明: by
  rw [← e.preimage_Ico]; rw [image_preimage_eq_inter_range]; rw [inter_eq_left.2 Ico_subset_Icc_self.trans he.out ⟨_]; rw [rfl⟩ ⟨_]; rw [rfl⟩]

Depends on / 依赖: Ico_subset_Icc_self, Ico_subset_Icc_self.trans, e.preimage_Ico, he.out, image_preimage_eq_inter_range, inter_eq_left, preimage_Ico
-/
theorem image_Ico (e : α ↪o β) (he : OrdConnected (range e)) (x y : α) :
    e '' Ico x y = Ico (e x) (e y) := by
  rw [← e.preimage_Ico]; rw [image_preimage_eq_inter_range]; rw [inter_eq_left.2 Ico_subset_Icc_self.trans he.out ⟨_]; rw [rfl⟩ ⟨_]; rw [rfl⟩]

/--
theorem `image_Ioc` / 定理 `image_Ioc`

English:
theorem image_Ioc
  given: (e : α ↪o β) (he : OrdConnected (range e)) (x y : α)
  proof: by
  rw [← e.preimage_Ioc]; rw [image_preimage_eq_inter_range]; rw [inter_eq_left.2 Ioc_subset_Icc_self.trans he.out ⟨_]; rw [rfl⟩ ⟨_]; rw [rfl⟩]

中文:
定理 image_Ioc
  条件: (e : α ↪o β) (he : 序连通 (range e)) (x y : α)
  证明: by
  rw [← e.preimage_Ioc]; rw [image_preimage_eq_inter_range]; rw [inter_eq_left.2 Ioc_subset_Icc_self.trans he.out ⟨_]; rw [rfl⟩ ⟨_]; rw [rfl⟩]

Depends on / 依赖: Ioc_subset_Icc_self, Ioc_subset_Icc_self.trans, e.preimage_Ioc, he.out, image_preimage_eq_inter_range, inter_eq_left, preimage_Ioc
-/
theorem image_Ioc (e : α ↪o β) (he : OrdConnected (range e)) (x y : α) :
    e '' Ioc x y = Ioc (e x) (e y) := by
  rw [← e.preimage_Ioc]; rw [image_preimage_eq_inter_range]; rw [inter_eq_left.2 Ioc_subset_Icc_self.trans he.out ⟨_]; rw [rfl⟩ ⟨_]; rw [rfl⟩]

/--
theorem `image_Ioo` / 定理 `image_Ioo`

English:
theorem image_Ioo
  given: (e : α ↪o β) (he : OrdConnected (range e)) (x y : α)
  proof: by
  rw [← e.preimage_Ioo]; rw [image_preimage_eq_inter_range]; rw [inter_eq_left.2 Ioo_subset_Icc_self.trans he.out ⟨_]; rw [rfl⟩ ⟨_]; rw [rfl⟩]

中文:
定理 image_Ioo
  条件: (e : α ↪o β) (he : 序连通 (range e)) (x y : α)
  证明: by
  rw [← e.preimage_Ioo]; rw [image_preimage_eq_inter_range]; rw [inter_eq_left.2 Ioo_subset_Icc_self.trans he.out ⟨_]; rw [rfl⟩ ⟨_]; rw [rfl⟩]

Depends on / 依赖: Ioo_subset_Icc_self, Ioo_subset_Icc_self.trans, e.preimage_Ioo, he.out, image_preimage_eq_inter_range, inter_eq_left, preimage_Ioo
-/
theorem image_Ioo (e : α ↪o β) (he : OrdConnected (range e)) (x y : α) :
    e '' Ioo x y = Ioo (e x) (e y) := by
  rw [← e.preimage_Ioo]; rw [image_preimage_eq_inter_range]; rw [inter_eq_left.2 Ioo_subset_Icc_self.trans he.out ⟨_]; rw [rfl⟩ ⟨_]; rw [rfl⟩]

end OrderEmbedding

namespace Set

section Preorder

variable {α β : Type*} [Preorder α] [Preorder β]

@[simp]
/--
lemma `image_subtype_val_Icc` / 引理 `image_subtype_val_Icc`

English:
lemma image_subtype_val_Icc
  given: {s : Set α} [OrdConnected s] (x y : s)
  proof: (OrderEmbedding.subtype (· in s)).image_Icc (by simpa) x y

@[simp]

中文:
引理 image_subtype_val_Icc
  条件: {s : 集合 α} [序连通 s] (x y : s)
  证明: (OrderEmbedding.subtype (· in s)).image_Icc (by simpa) x y

@[simp]

Depends on / 依赖: OrderEmbedding, OrderEmbedding.subtype, image_Icc, subtype
-/
lemma image_subtype_val_Icc {s : Set α} [OrdConnected s] (x y : s) :
    Subtype.val '' Icc x y = Icc x.1 y :=
  (OrderEmbedding.subtype (· in s)).image_Icc (by simpa) x y

@[simp]
/--
lemma `image_subtype_val_Ico` / 引理 `image_subtype_val_Ico`

English:
lemma image_subtype_val_Ico
  given: {s : Set α} [OrdConnected s] (x y : s)
  proof: (OrderEmbedding.subtype (· in s)).image_Ico (by simpa) x y

@[simp]

中文:
引理 image_subtype_val_Ico
  条件: {s : 集合 α} [序连通 s] (x y : s)
  证明: (OrderEmbedding.subtype (· in s)).image_Ico (by simpa) x y

@[simp]

Depends on / 依赖: OrderEmbedding, OrderEmbedding.subtype, image_Ico, subtype
-/
lemma image_subtype_val_Ico {s : Set α} [OrdConnected s] (x y : s) :
    Subtype.val '' Ico x y = Ico x.1 y :=
  (OrderEmbedding.subtype (· in s)).image_Ico (by simpa) x y

@[simp]
/--
lemma `image_subtype_val_Ioc` / 引理 `image_subtype_val_Ioc`

English:
lemma image_subtype_val_Ioc
  given: {s : Set α} [OrdConnected s] (x y : s)
  proof: (OrderEmbedding.subtype (· in s)).image_Ioc (by simpa) x y

@[simp]

中文:
引理 image_subtype_val_Ioc
  条件: {s : 集合 α} [序连通 s] (x y : s)
  证明: (OrderEmbedding.subtype (· in s)).image_Ioc (by simpa) x y

@[simp]

Depends on / 依赖: OrderEmbedding, OrderEmbedding.subtype, image_Ioc, subtype
-/
lemma image_subtype_val_Ioc {s : Set α} [OrdConnected s] (x y : s) :
    Subtype.val '' Ioc x y = Ioc x.1 y :=
  (OrderEmbedding.subtype (· in s)).image_Ioc (by simpa) x y

@[simp]
/--
lemma `image_subtype_val_Ioo` / 引理 `image_subtype_val_Ioo`

English:
lemma image_subtype_val_Ioo
  given: {s : Set α} [OrdConnected s] (x y : s)
  proof: (OrderEmbedding.subtype (· in s)).image_Ioo (by simpa) x y

中文:
引理 image_subtype_val_Ioo
  条件: {s : 集合 α} [序连通 s] (x y : s)
  证明: (OrderEmbedding.subtype (· in s)).image_Ioo (by simpa) x y

Depends on / 依赖: OrderEmbedding, OrderEmbedding.subtype, image_Ioo, subtype
-/
lemma image_subtype_val_Ioo {s : Set α} [OrdConnected s] (x y : s) :
    Subtype.val '' Ioo x y = Ioo x.1 y :=
  (OrderEmbedding.subtype (· in s)).image_Ioo (by simpa) x y

/--
theorem `OrdConnected.inter` / 定理 `OrdConnected.inter`

English:
theorem OrdConnected.inter
  given: {s t : Set α} (hs : OrdConnected s) (ht : OrdConnected t)
  proof: ⟨fun _ hx _ hy => subset_inter (hs.out hx.1 hy.1) (ht.out hx.2 hy.2)⟩

中文:
定理 序连通.inter
  条件: {s t : 集合 α} (hs : 序连通 s) (ht : 序连通 t)
  证明: ⟨fun _ hx _ hy => subset_inter (hs.out hx.1 hy.1) (ht.out hx.2 hy.2)⟩

Depends on / 依赖: hs.out, ht.out, subset_inter
-/
theorem OrdConnected.inter {s t : Set α} (hs : OrdConnected s) (ht : OrdConnected t) :
    OrdConnected (s inter t) :=
  ⟨fun _ hx _ hy => subset_inter (hs.out hx.1 hy.1) (ht.out hx.2 hy.2)⟩

/--
Instance `OrdConnected.inter'` / 实例 `OrdConnected.inter'`

English:
instance OrdConnected.inter'
  signature: {s t : Set α} [OrdConnected s] [OrdConnected t]
  body: OrdConnected.inter ‹_› ‹_›

中文:
实例 序连通.inter'
  签名: {s t : 集合 α} [序连通 s] [序连通 t]
  定义体: OrdConnected.inter ‹_› ‹_›

Depends on / 依赖: OrdConnected, OrdConnected.inter
-/
instance OrdConnected.inter' {s t : Set α} [OrdConnected s] [OrdConnected t] :
    OrdConnected (s inter t) :=
  OrdConnected.inter ‹_› ‹_›

/--
theorem `OrdConnected.dual` / 定理 `OrdConnected.dual`

English:
theorem OrdConnected.dual
  given: {s : Set α} (hs : OrdConnected s)
  proof: ⟨fun _ hx _ hy _ hz => hs.out hy hx ⟨hz.2, hz.1⟩⟩

@[instance]

中文:
定理 序连通.dual
  条件: {s : 集合 α} (hs : 序连通 s)
  证明: ⟨fun _ hx _ hy _ hz => hs.out hy hx ⟨hz.2, hz.1⟩⟩

@[instance]

Depends on / 依赖: hs.out
-/
theorem OrdConnected.dual {s : Set α} (hs : OrdConnected s) :
    OrdConnected (OrderDual.ofDual ⁻¹' s) :=
  ⟨fun _ hx _ hy _ hz => hs.out hy hx ⟨hz.2, hz.1⟩⟩

@[instance]
/--
theorem `dual_ordConnected` / 定理 `dual_ordConnected`

English:
theorem dual_ordConnected
  given: {s : Set α} [OrdConnected s]
  statement: OrdConnected (ofDual ⁻¹' s)
  proof: .dual ‹OrdConnected s›

@[simp]

中文:
定理 dual_ordConnected
  条件: {s : 集合 α} [序连通 s]
  结论: 序连通 (ofDual ⁻¹' s)
  证明: .dual ‹OrdConnected s›

@[simp]

Depends on / 依赖: OrdConnected
-/
theorem dual_ordConnected {s : Set α} [OrdConnected s] : OrdConnected (ofDual ⁻¹' s) :=
  .dual ‹OrdConnected s›

@[simp]
/--
theorem `ordConnected_dual` / 定理 `ordConnected_dual`

English:
theorem ordConnected_dual
  given: {s : Set α}
  statement: OrdConnected (OrderDual.ofDual ⁻¹' s) ↔ OrdConnected s
  proof: ⟨fun h => by simpa only [ordConnected_def] using! h.dual, fun h => h.dual⟩

中文:
定理 ordConnected_dual
  条件: {s : 集合 α}
  结论: 序连通 (OrderDual.ofDual ⁻¹' s) ↔ 序连通 s
  证明: ⟨fun h => by simpa only [ordConnected_def] using! h.dual, fun h => h.dual⟩

Depends on / 依赖: h.dual, ordConnected_def
-/
theorem ordConnected_dual {s : Set α} : OrdConnected (OrderDual.ofDual ⁻¹' s) ↔ OrdConnected s :=
  ⟨fun h => by simpa only [ordConnected_def] using! h.dual, fun h => h.dual⟩

/--
theorem `ordConnected_sInter` / 定理 `ordConnected_sInter`

English:
theorem ordConnected_sInter
  given: {S : Set (Set α)} (hS : forall s in S, OrdConnected s)
  proof: ⟨fun _x hx _y hy _z hz s hs => (hS s hs).out (hx s hs) (hy s hs) hz⟩

中文:
定理 ordConnected_s整数er
  条件: {S : 集合 (集合 α)} (hS : 对任意 s in S, 序连通 s)
  证明: ⟨fun _x hx _y hy _z hz s hs => (hS s hs).out (hx s hs) (hy s hs) hz⟩
-/
theorem ordConnected_sInter {S : Set (Set α)} (hS : forall s in S, OrdConnected s) :
    OrdConnected (⋂₀ S) :=
  ⟨fun _x hx _y hy _z hz s hs => (hS s hs).out (hx s hs) (hy s hs) hz⟩

/--
theorem `ordConnected_iInter` / 定理 `ordConnected_iInter`

English:
theorem ordConnected_iInter
  given: {ι : Sort*} {s : ι -> Set α} (hs : forall i, OrdConnected (s i))
  proof: ordConnected_sInter forall_mem_range.2 hs

中文:
定理 ordConnected_i整数er
  条件: {ι : 类型层*} {s : ι -> 集合 α} (hs : 对任意 i, 序连通 (s i))
  证明: ordConnected_sInter forall_mem_range.2 hs

Depends on / 依赖: forall_mem_range, ordConnected_sInter
-/
theorem ordConnected_iInter {ι : Sort*} {s : ι -> Set α} (hs : forall i, OrdConnected (s i)) :
    OrdConnected (⋂ i, s i) :=
ordConnected_sInter forall_mem_range.2 hs

/--
Instance `ordConnected_iInter'` / 实例 `ordConnected_iInter'`

English:
instance ordConnected_iInter'
  signature: {ι : Sort*} {s : ι -> Set α} [forall i, OrdConnected (s i)]
  body: ordConnected_iInter ‹_›

中文:
实例 ordConnected_i整数er'
  签名: {ι : 类型层*} {s : ι -> 集合 α} [对任意 i, 序连通 (s i)]
  定义体: ordConnected_iInter ‹_›

Depends on / 依赖: ordConnected_iInter
-/
instance ordConnected_iInter' {ι : Sort*} {s : ι -> Set α} [forall i, OrdConnected (s i)] :
    OrdConnected (⋂ i, s i) :=
  ordConnected_iInter ‹_›

/--
theorem `ordConnected_biInter` / 定理 `ordConnected_biInter`

English:
theorem ordConnected_biInter
  statement: {ι : Sort*} {p : ι -> Prop} {s : forall i, p i -> Set α}
  proof: ordConnected_iInter fun i => ordConnected_iInter hs i

中文:
定理 ordConnected_bi整数er
  结论: {ι : 类型层*} {p : ι -> 命题} {s : 对任意 i, p i -> 集合 α}
  证明: ordConnected_iInter fun i => ordConnected_iInter hs i

Depends on / 依赖: ordConnected_iInter
-/
theorem ordConnected_biInter {ι : Sort*} {p : ι -> Prop} {s : forall i, p i -> Set α}
    (hs : forall i hi, OrdConnected (s i hi)) : OrdConnected (⋂ (i) (hi), s i hi) :=
ordConnected_iInter fun i => ordConnected_iInter hs i

/--
theorem `ordConnected_pi` / 定理 `ordConnected_pi`

English:
theorem ordConnected_pi
  statement: {ι : Type*} {α : ι -> Type*} [forall i, Preorder (α i)] {s : Set ι}
  proof: ⟨fun _ hx _ hy _ hz i hi => (h i hi).out (hx i hi) (hy i hi) ⟨hz.1 i, hz.2 i⟩⟩

中文:
定理 ordConnected_pi
  结论: {ι : 类型} {α : ι -> 类型} [对任意 i, 预序 (α i)] {s : 集合 ι}
  证明: ⟨fun _ hx _ hy _ hz i hi => (h i hi).out (hx i hi) (hy i hi) ⟨hz.1 i, hz.2 i⟩⟩
-/
theorem ordConnected_pi {ι : Type*} {α : ι -> Type*} [forall i, Preorder (α i)] {s : Set ι}
    {t : forall i, Set (α i)} (h : forall i in s, OrdConnected (t i)) : OrdConnected (s.pi t) :=
  ⟨fun _ hx _ hy _ hz i hi => (h i hi).out (hx i hi) (hy i hi) ⟨hz.1 i, hz.2 i⟩⟩

/--
Instance `ordConnected_pi'` / 实例 `ordConnected_pi'`

English:
instance ordConnected_pi'
  signature: {ι : Type*} {α : ι -> Type*} [forall i, Preorder (α i)] {s : Set ι}
  body: ordConnected_pi fun i _ => h i

@[to_dual]

中文:
实例 ordConnected_pi'
  签名: {ι : 类型} {α : ι -> 类型} [对任意 i, 预序 (α i)] {s : 集合 ι}
  定义体: ordConnected_pi fun i _ => h i

@[to_dual]

Depends on / 依赖: ordConnected_pi
-/
instance ordConnected_pi' {ι : Type*} {α : ι -> Type*} [forall i, Preorder (α i)] {s : Set ι}
    {t : forall i, Set (α i)} [h : forall i, OrdConnected (t i)] : OrdConnected (s.pi t) :=
  ordConnected_pi fun i _ => h i

@[to_dual]
/--
Instance `ordConnected_Ici` / 实例 `ordConnected_Ici`

English:
instance ordConnected_Ici
  signature: {a : α}
  body: ⟨fun _ hx _ _ _ hz => le_trans hx hz.1⟩

@[to_dual]

中文:
实例 ordConnected_Ici
  签名: {a : α}
  定义体: ⟨fun _ hx _ _ _ hz => le_trans hx hz.1⟩

@[to_dual]

Depends on / 依赖: le_trans
-/
instance ordConnected_Ici {a : α} : OrdConnected (Ici a) :=
  ⟨fun _ hx _ _ _ hz => le_trans hx hz.1⟩

@[to_dual]
/--
Instance `ordConnected_Ioi` / 实例 `ordConnected_Ioi`

English:
instance ordConnected_Ioi
  signature: {a : α}
  body: ⟨fun _ hx _ _ _ hz => lt_of_lt_of_le hx hz.1⟩

@[to_dual self]

中文:
实例 ordConnected_Ioi
  签名: {a : α}
  定义体: ⟨fun _ hx _ _ _ hz => lt_of_lt_of_le hx hz.1⟩

@[to_dual self]

Depends on / 依赖: lt_of_lt_of_le
-/
instance ordConnected_Ioi {a : α} : OrdConnected (Ioi a) :=
  ⟨fun _ hx _ _ _ hz => lt_of_lt_of_le hx hz.1⟩

@[to_dual self]
/--
Instance `ordConnected_Icc` / 实例 `ordConnected_Icc`

English:
instance ordConnected_Icc
  signature: {a b : α}
  body: ordConnected_Ici.inter ordConnected_Iic

@[to_dual]

中文:
实例 ordConnected_Icc
  签名: {a b : α}
  定义体: ordConnected_Ici.inter ordConnected_Iic

@[to_dual]

Depends on / 依赖: ordConnected_Ici, ordConnected_Ici.inter, ordConnected_Iic
-/
instance ordConnected_Icc {a b : α} : OrdConnected (Icc a b) :=
  ordConnected_Ici.inter ordConnected_Iic

@[to_dual]
/--
Instance `ordConnected_Ico` / 实例 `ordConnected_Ico`

English:
instance ordConnected_Ico
  signature: {a b : α}
  body: ordConnected_Ici.inter ordConnected_Iio

@[to_dual self]

中文:
实例 ordConnected_Ico
  签名: {a b : α}
  定义体: ordConnected_Ici.inter ordConnected_Iio

@[to_dual self]

Depends on / 依赖: ordConnected_Ici, ordConnected_Ici.inter, ordConnected_Iio
-/
instance ordConnected_Ico {a b : α} : OrdConnected (Ico a b) :=
  ordConnected_Ici.inter ordConnected_Iio

@[to_dual self]
/--
Instance `ordConnected_Ioo` / 实例 `ordConnected_Ioo`

English:
instance ordConnected_Ioo
  signature: {a b : α}
  body: ordConnected_Ioi.inter ordConnected_Iio

@[instance]

中文:
实例 ordConnected_Ioo
  签名: {a b : α}
  定义体: ordConnected_Ioi.inter ordConnected_Iio

@[instance]

Depends on / 依赖: ordConnected_Iio, ordConnected_Ioi, ordConnected_Ioi.inter
-/
instance ordConnected_Ioo {a b : α} : OrdConnected (Ioo a b) :=
  ordConnected_Ioi.inter ordConnected_Iio

@[instance]
/--
theorem `ordConnected_singleton` / 定理 `ordConnected_singleton`

English:
theorem ordConnected_singleton
  given: {α : Type*} [PartialOrder α] {a : α}
  proof: by
  rw [← Icc_self]
  exact ordConnected_Icc

@[instance]

中文:
定理 ordConnected_singleton
  条件: {α : 类型} [偏序 α] {a : α}
  证明: by
  rw [← Icc_self]
  exact ordConnected_Icc

@[instance]

Depends on / 依赖: Icc_self, ordConnected_Icc
-/
theorem ordConnected_singleton {α : Type*} [PartialOrder α] {a : α} :
    OrdConnected ({a} : Set α) := by
  rw [← Icc_self]
  exact ordConnected_Icc

@[instance]
/--
theorem `ordConnected_empty` / 定理 `ordConnected_empty`

English:
theorem ordConnected_empty
  statement: OrdConnected (∅ : Set α)
  proof: ⟨fun _ => False.elim⟩

@[instance]

中文:
定理 ordConnected_empty
  结论: 序连通 (∅ : 集合 α)
  证明: ⟨fun _ => False.elim⟩

@[instance]

Depends on / 依赖: False.elim
-/
theorem ordConnected_empty : OrdConnected (∅ : Set α) :=
  ⟨fun _ => False.elim⟩

@[instance]
/--
theorem `ordConnected_univ` / 定理 `ordConnected_univ`

English:
theorem ordConnected_univ
  statement: OrdConnected (univ : Set α)
  proof: ⟨fun _ _ _ _ => subset_univ _⟩

中文:
定理 ordConnected_univ
  结论: 序连通 (univ : 集合 α)
  证明: ⟨fun _ _ _ _ => subset_univ _⟩

Depends on / 依赖: subset_univ
-/
theorem ordConnected_univ : OrdConnected (univ : Set α) :=
  ⟨fun _ _ _ _ => subset_univ _⟩

/--
Instance `instDenselyOrdered` / 实例 `instDenselyOrdered`

English:
instance instDenselyOrdered
  signature: [DenselyOrdered α] {s : Set α} [hs : OrdConnected s]
  body: ⟨fun a b (h : (a : α) < b) =>
    let ⟨x, H⟩ := exists_between h
    ⟨⟨x, (hs.out a.2 b.2) (Ioo_subset_Icc_self H)⟩, H⟩⟩

@[instance]

中文:
实例 instDenselyOrdered
  签名: [稠密序 α] {s : 集合 α} [hs : 序连通 s]
  定义体: ⟨fun a b (h : (a : α) < b) =>
    let ⟨x, H⟩ := exists_between h
    ⟨⟨x, (hs.out a.2 b.2) (Ioo_subset_Icc_self H)⟩, H⟩⟩

@[instance]

Depends on / 依赖: Ioo_subset_Icc_self, exists_between, hs.out
-/
instance instDenselyOrdered [DenselyOrdered α] {s : Set α} [hs : OrdConnected s] :
    DenselyOrdered s :=
  ⟨fun a b (h : (a : α) < b) =>
    let ⟨x, H⟩ := exists_between h
    ⟨⟨x, (hs.out a.2 b.2) (Ioo_subset_Icc_self H)⟩, H⟩⟩

@[instance]
/--
theorem `ordConnected_preimage` / 定理 `ordConnected_preimage`

English:
theorem ordConnected_preimage
  statement: {F : Type*} [FunLike F α β] [OrderHomClass F α β] (f : F)
  proof: ⟨fun _ hx _ hy _ hz => hs.out hx hy ⟨OrderHomClass.mono _ hz.1, OrderHomClass.mono _ hz.2⟩⟩

@[instance]

中文:
定理 ordConnected_preimage
  结论: {F : 类型} [函数状 F α β] [序态射类 F α β] (f : F)
  证明: ⟨fun _ hx _ hy _ hz => hs.out hx hy ⟨OrderHomClass.mono _ hz.1, OrderHomClass.mono _ hz.2⟩⟩

@[instance]

Depends on / 依赖: OrderHomClass, OrderHomClass.mono, hs.out
-/
theorem ordConnected_preimage {F : Type*} [FunLike F α β] [OrderHomClass F α β] (f : F)
    {s : Set β} [hs : OrdConnected s] : OrdConnected (f ⁻¹' s) :=
  ⟨fun _ hx _ hy _ hz => hs.out hx hy ⟨OrderHomClass.mono _ hz.1, OrderHomClass.mono _ hz.2⟩⟩

@[instance]
/--
theorem `ordConnected_image` / 定理 `ordConnected_image`

English:
theorem ordConnected_image
  statement: {E : Type*} [EquivLike E α β] [OrderIsoClass E α β] (e : E) {s : Set α}
  proof: by
  erw [(e : α ≃o β).image_eq_preimage_symm]
  apply ordConnected_preimage (e : α ≃o β).symm

@[instance]

中文:
定理 ordConnected_image
  结论: {E : 类型} [等价状 E α β] [OrderIso类 E α β] (e : E) {s : 集合 α}
  证明: by
  erw [(e : α ≃o β).image_eq_preimage_symm]
  apply ordConnected_preimage (e : α ≃o β).symm

@[instance]

Depends on / 依赖: image_eq_preimage_symm, ordConnected_preimage
-/
theorem ordConnected_image {E : Type*} [EquivLike E α β] [OrderIsoClass E α β] (e : E) {s : Set α}
    [hs : OrdConnected s] : OrdConnected (e '' s) := by
  erw [(e : α ≃o β).image_eq_preimage_symm]
  apply ordConnected_preimage (e : α ≃o β).symm

@[instance]
/--
theorem `ordConnected_range` / 定理 `ordConnected_range`

English:
theorem ordConnected_range
  given: {E : Type*} [EquivLike E α β] [OrderIsoClass E α β] (e : E)
  proof: by
  simp_rw [← image_univ]
  exact ordConnected_image (e : α ≃o β)

中文:
定理 ordConnected_range
  条件: {E : 类型} [等价状 E α β] [OrderIso类 E α β] (e : E)
  证明: by
  simp_rw [← image_univ]
  exact ordConnected_image (e : α ≃o β)

Depends on / 依赖: image_univ, ordConnected_image, simp_rw
-/
theorem ordConnected_range {E : Type*} [EquivLike E α β] [OrderIsoClass E α β] (e : E) :
    OrdConnected (range e) := by
  simp_rw [← image_univ]
  exact ordConnected_image (e : α ≃o β)

/--
theorem `OrdConnected.preimage_monotoneOn` / 定理 `OrdConnected.preimage_monotoneOn`

English:
theorem OrdConnected.preimage_monotoneOn
  statement: {f : β -> α} {t : Set β} {s : Set α}
  proof: by
  let u := {x | (exists y in t, y <= x ∧ f y in s) ∧ (exists z in t, x <= z ∧ f z in s)}
  refine ⟨u, ⟨?_⟩, Subset.antisymm ?_ ?_⟩
  · rintro x ⟨⟨y, yt, yx, ys⟩, -⟩ x' ⟨-, ⟨z, zt, x'z, zs⟩⟩ a ha
    exact ⟨⟨y, yt, yx.trans ha.1, ys⟩, ⟨z, zt, ha.2.trans x'z, zs⟩⟩
  · rintro x ⟨xt, xs⟩
    exact ⟨x

中文:
定理 序连通.preimage_monotoneOn
  结论: {f : β -> α} {t : 集合 β} {s : 集合 α}
  证明: by
  let u := {x | (exists y in t, y <= x ∧ f y in s) ∧ (exists z in t, x <= z ∧ f z in s)}
  refine ⟨u, ⟨?_⟩, Subset.antisymm ?_ ?_⟩
  · rintro x ⟨⟨y, yt, yx, ys⟩, -⟩ x' ⟨-, ⟨z, zt, x'z, zs⟩⟩ a ha
    exact ⟨⟨y, yt, yx.trans ha.1, ys⟩, ⟨z, zt, ha.2.trans x'z, zs⟩⟩
  · rintro x ⟨xt, xs⟩
    exact ⟨x

Depends on / 依赖: Subset, Subset.antisymm, antisymm, hs.out, le_rfl, yx.trans
-/
theorem OrdConnected.preimage_monotoneOn {f : β -> α} {t : Set β} {s : Set α}
    (hs : OrdConnected s) (hf : MonotoneOn f t) :
    exists u, OrdConnected u ∧ t inter f ⁻¹' s = t inter u := by
  let u := {x | (exists y in t, y <= x ∧ f y in s) ∧ (exists z in t, x <= z ∧ f z in s)}
  refine ⟨u, ⟨?_⟩, Subset.antisymm ?_ ?_⟩
  · rintro x ⟨⟨y, yt, yx, ys⟩, -⟩ x' ⟨-, ⟨z, zt, x'z, zs⟩⟩ a ha
    exact ⟨⟨y, yt, yx.trans ha.1, ys⟩, ⟨z, zt, ha.2.trans x'z, zs⟩⟩
  · rintro x ⟨xt, xs⟩
    exact ⟨xt, ⟨x, xt, le_rfl, xs⟩, ⟨x, xt, le_rfl, xs⟩⟩
  · rintro x ⟨xt, ⟨y, yt, yx, ys⟩, ⟨z, zt, xz, zs⟩⟩
    refine ⟨xt, ?_⟩
    apply hs.out ys zs
    exact ⟨hf yt xt yx, hf xt zt xz⟩

/--
theorem `OrdConnected.preimage_antitoneOn` / 定理 `OrdConnected.preimage_antitoneOn`

English:
theorem OrdConnected.preimage_antitoneOn
  statement: {f : β -> α} {t : Set β} {s : Set α}
  proof: (OrdConnected.preimage_monotoneOn hs.dual hf.dual_right :)

中文:
定理 序连通.preimage_antitoneOn
  结论: {f : β -> α} {t : 集合 β} {s : 集合 α}
  证明: (OrdConnected.preimage_monotoneOn hs.dual hf.dual_right :)

Depends on / 依赖: OrdConnected, OrdConnected.preimage_monotoneOn, dual_right, hf.dual_right, hs.dual, preimage_monotoneOn
-/
theorem OrdConnected.preimage_antitoneOn {f : β -> α} {t : Set β} {s : Set α}
    (hs : OrdConnected s) (hf : AntitoneOn f t) :
    exists u, OrdConnected u ∧ t inter f ⁻¹' s = t inter u :=
  (OrdConnected.preimage_monotoneOn hs.dual hf.dual_right :)

end Preorder

section PartialOrder

variable {α : Type*} [PartialOrder α] {s : Set α} {x y : α}

/--
theorem `_root_.IsAntichain.ordConnected` / 定理 `_root_.IsAntichain.ordConnected`

English:
theorem _root_.IsAntichain.ordConnected
  given: (hs : IsAntichain (· <= ·) s)
  statement: s.OrdConnected
  proof: ⟨fun x hx y hy z hz => by
    obtain rfl := hs.eq hx hy (hz.1.trans hz.2)
    rw [Icc_self]; rw [mem_singleton_iff] at hz
    rwa [hz]⟩

中文:
定理 _root_.IsAntichain.ordConnected
  条件: (hs : IsAntichain (· <= ·) s)
  结论: s.序连通
  证明: ⟨fun x hx y hy z hz => by
    obtain rfl := hs.eq hx hy (hz.1.trans hz.2)
    rw [Icc_self]; rw [mem_singleton_iff] at hz
    rwa [hz]⟩
-/
protected theorem _root_.IsAntichain.ordConnected (hs : IsAntichain (· <= ·) s) : s.OrdConnected :=
  ⟨fun x hx y hy z hz => by
    obtain rfl := hs.eq hx hy (hz.1.trans hz.2)
    rw [Icc_self]; rw [mem_singleton_iff] at hz
    rwa [hz]⟩

/--
lemma `ordConnected_inter_Icc_of_subset` / 引理 `ordConnected_inter_Icc_of_subset`

English:
lemma ordConnected_inter_Icc_of_subset
  given: (h : Ioo x y subseteq s)
  statement: OrdConnected (s inter Icc x y)
  proof: ordConnected_of_Ioo fun _u ⟨_, hu, _⟩ _v ⟨_, _, hv⟩ _ =>
.trans subset_inter h Ioo_subset_Icc_self Ioo_subset_Ioo hu hv

中文:
引理 ordConnected_inter_Icc_of_subset
  条件: (h : 开区间 x y subseteq s)
  结论: 序连通 (s inter 闭区间 x y)
  证明: ordConnected_of_Ioo fun _u ⟨_, hu, _⟩ _v ⟨_, _, hv⟩ _ =>
.trans subset_inter h Ioo_subset_Icc_self Ioo_subset_Ioo hu hv

Depends on / 依赖: Ioo_subset_Icc_self, Ioo_subset_Ioo, ordConnected_of_Ioo, subset_inter
-/
lemma ordConnected_inter_Icc_of_subset (h : Ioo x y subseteq s) : OrdConnected (s inter Icc x y) :=
  ordConnected_of_Ioo fun _u ⟨_, hu, _⟩ _v ⟨_, _, hv⟩ _ =>
.trans subset_inter h Ioo_subset_Icc_self Ioo_subset_Ioo hu hv

/--
lemma `ordConnected_inter_Icc_iff` / 引理 `ordConnected_inter_Icc_iff`

English:
lemma ordConnected_inter_Icc_iff
  given: (hx : x in s) (hy : y in s)
  proof: by
  refine ⟨fun h => Ioo_subset_Icc_self.trans fun z hz => ?_, ordConnected_inter_Icc_of_subset⟩
  have hxy : x <= y := hz.1.trans hz.2
.1 exact h.out ⟨hx, left_mem_Icc.2 hxy⟩ ⟨hy, right_mem_Icc.2 hxy⟩ hz

中文:
引理 ordConnected_inter_Icc_iff
  条件: (hx : x in s) (hy : y in s)
  证明: by
  refine ⟨fun h => Ioo_subset_Icc_self.trans fun z hz => ?_, ordConnected_inter_Icc_of_subset⟩
  have hxy : x <= y := hz.1.trans hz.2
.1 exact h.out ⟨hx, left_mem_Icc.2 hxy⟩ ⟨hy, right_mem_Icc.2 hxy⟩ hz

Depends on / 依赖: Ioo_subset_Icc_self, Ioo_subset_Icc_self.trans, h.out, left_mem_Icc, ordConnected_inter_Icc_of_subset, right_mem_Icc
-/
lemma ordConnected_inter_Icc_iff (hx : x in s) (hy : y in s) :
    OrdConnected (s inter Icc x y) ↔ Ioo x y subseteq s := by
  refine ⟨fun h => Ioo_subset_Icc_self.trans fun z hz => ?_, ordConnected_inter_Icc_of_subset⟩
  have hxy : x <= y := hz.1.trans hz.2
.1 exact h.out ⟨hx, left_mem_Icc.2 hxy⟩ ⟨hy, right_mem_Icc.2 hxy⟩ hz

/--
lemma `not_ordConnected_inter_Icc_iff` / 引理 `not_ordConnected_inter_Icc_iff`

English:
lemma not_ordConnected_inter_Icc_iff
  given: (hx : x in s) (hy : y in s)
  proof: by
  simp_rw [ordConnected_inter_Icc_iff hx hy, subset_def, not_forall, exists_prop, and_comm]

中文:
引理 not_ordConnected_inter_Icc_iff
  条件: (hx : x in s) (hy : y in s)
  证明: by
  simp_rw [ordConnected_inter_Icc_iff hx hy, subset_def, not_forall, exists_prop, and_comm]

Depends on / 依赖: and_comm, exists_prop, not_forall, ordConnected_inter_Icc_iff, simp_rw, subset_def
-/
lemma not_ordConnected_inter_Icc_iff (hx : x in s) (hy : y in s) :
    ¬ OrdConnected (s inter Icc x y) ↔ exists z ∉ s, z in Ioo x y := by
  simp_rw [ordConnected_inter_Icc_iff hx hy, subset_def, not_forall, exists_prop, and_comm]

end PartialOrder

section LinearOrder

open scoped Interval

variable {α : Type*} [LinearOrder α] {s : Set α} {x : α}

@[instance]
/--
theorem `ordConnected_uIcc` / 定理 `ordConnected_uIcc`

English:
theorem ordConnected_uIcc
  given: {a b : α}
  statement: OrdConnected [[a, b]]
  proof: ordConnected_Icc

@[instance]

中文:
定理 ordConnected_uIcc
  条件: {a b : α}
  结论: 序连通 [[a, b]]
  证明: ordConnected_Icc

@[instance]

Depends on / 依赖: ordConnected_Icc
-/
theorem ordConnected_uIcc {a b : α} : OrdConnected [[a, b]] :=
  ordConnected_Icc

@[instance]
/--
theorem `ordConnected_uIoc` / 定理 `ordConnected_uIoc`

English:
theorem ordConnected_uIoc
  given: {a b : α}
  statement: OrdConnected (Ι a b)
  proof: ordConnected_Ioc

中文:
定理 ordConnected_uIoc
  条件: {a b : α}
  结论: 序连通 (Ι a b)
  证明: ordConnected_Ioc

Depends on / 依赖: ordConnected_Ioc
-/
theorem ordConnected_uIoc {a b : α} : OrdConnected (Ι a b) :=
  ordConnected_Ioc

/--
theorem `OrdConnected.uIcc_subset` / 定理 `OrdConnected.uIcc_subset`

English:
theorem OrdConnected.uIcc_subset
  given: (hs : OrdConnected s) ⦃x⦄ (hx : x in s) ⦃y⦄ (hy : y in s)
  proof: hs.out (min_rec' (· in s) hx hy) (max_rec' (· in s) hx hy)

中文:
定理 序连通.uIcc_subset
  条件: (hs : 序连通 s) ⦃x⦄ (hx : x in s) ⦃y⦄ (hy : y in s)
  证明: hs.out (min_rec' (· in s) hx hy) (max_rec' (· in s) hx hy)

Depends on / 依赖: hs.out, max_rec, min_rec
-/
theorem OrdConnected.uIcc_subset (hs : OrdConnected s) ⦃x⦄ (hx : x in s) ⦃y⦄ (hy : y in s) :
    [[x, y]] subseteq s :=
  hs.out (min_rec' (· in s) hx hy) (max_rec' (· in s) hx hy)

/--
theorem `OrdConnected.uIoc_subset` / 定理 `OrdConnected.uIoc_subset`

English:
theorem OrdConnected.uIoc_subset
  given: (hs : OrdConnected s) ⦃x⦄ (hx : x in s) ⦃y⦄ (hy : y in s)
  proof: Ioc_subset_Icc_self.trans hs.uIcc_subset hx hy

中文:
定理 序连通.uIoc_subset
  条件: (hs : 序连通 s) ⦃x⦄ (hx : x in s) ⦃y⦄ (hy : y in s)
  证明: Ioc_subset_Icc_self.trans hs.uIcc_subset hx hy

Depends on / 依赖: Ioc_subset_Icc_self, Ioc_subset_Icc_self.trans, hs.uIcc_subset, uIcc_subset
-/
theorem OrdConnected.uIoc_subset (hs : OrdConnected s) ⦃x⦄ (hx : x in s) ⦃y⦄ (hy : y in s) :
    Ι x y subseteq s :=
Ioc_subset_Icc_self.trans hs.uIcc_subset hx hy

/--
theorem `ordConnected_iff_uIcc_subset` / 定理 `ordConnected_iff_uIcc_subset`

English:
theorem ordConnected_iff_uIcc_subset
  proof: ⟨fun h => h.uIcc_subset, fun H => ⟨fun _ hx _ hy => Icc_subset_uIcc.trans H hx hy⟩⟩

中文:
定理 ordConnected_iff_uIcc_subset
  证明: ⟨fun h => h.uIcc_subset, fun H => ⟨fun _ hx _ hy => Icc_subset_uIcc.trans H hx hy⟩⟩

Depends on / 依赖: Icc_subset_uIcc, Icc_subset_uIcc.trans, h.uIcc_subset, uIcc_subset
-/
theorem ordConnected_iff_uIcc_subset :
    OrdConnected s ↔ forall ⦃x⦄ (_ : x in s) ⦃y⦄ (_ : y in s), [[x, y]] subseteq s :=
⟨fun h => h.uIcc_subset, fun H => ⟨fun _ hx _ hy => Icc_subset_uIcc.trans H hx hy⟩⟩

/--
theorem `ordConnected_of_uIcc_subset_left` / 定理 `ordConnected_of_uIcc_subset_left`

English:
theorem ordConnected_of_uIcc_subset_left
  given: (h : forall y in s, [[x, y]] subseteq s)
  statement: OrdConnected s
  proof: ordConnected_iff_uIcc_subset.2 fun y hy z hz =>
    calc
      [[y, z]] subseteq [[y, x]] union [[x, z]] := uIcc_subset_uIcc_union_uIcc
      _ = [[x, y]] union [[x, z]] := by rw [uIcc_comm]
      _ subseteq s := union_subset (h y hy) (h z hz)

中文:
定理 ordConnected_of_uIcc_subset_left
  条件: (h : 对任意 y in s, [[x, y]] subseteq s)
  结论: 序连通 s
  证明: ordConnected_iff_uIcc_subset.2 fun y hy z hz =>
    calc
      [[y, z]] subseteq [[y, x]] union [[x, z]] := uIcc_subset_uIcc_union_uIcc
      _ = [[x, y]] union [[x, z]] := by rw [uIcc_comm]
      _ subseteq s := union_subset (h y hy) (h z hz)

Depends on / 依赖: ordConnected_iff_uIcc_subset, subseteq, uIcc_comm, uIcc_subset_uIcc_union_uIcc, union_subset
-/
theorem ordConnected_of_uIcc_subset_left (h : forall y in s, [[x, y]] subseteq s) : OrdConnected s :=
  ordConnected_iff_uIcc_subset.2 fun y hy z hz =>
    calc
      [[y, z]] subseteq [[y, x]] union [[x, z]] := uIcc_subset_uIcc_union_uIcc
      _ = [[x, y]] union [[x, z]] := by rw [uIcc_comm]
      _ subseteq s := union_subset (h y hy) (h z hz)

/--
theorem `ordConnected_iff_uIcc_subset_left` / 定理 `ordConnected_iff_uIcc_subset_left`

English:
theorem ordConnected_iff_uIcc_subset_left
  given: (hx : x in s)
  proof: ⟨fun hs => hs.uIcc_subset hx, ordConnected_of_uIcc_subset_left⟩

中文:
定理 ordConnected_iff_uIcc_subset_left
  条件: (hx : x in s)
  证明: ⟨fun hs => hs.uIcc_subset hx, ordConnected_of_uIcc_subset_left⟩

Depends on / 依赖: hs.uIcc_subset, ordConnected_of_uIcc_subset_left, uIcc_subset
-/
theorem ordConnected_iff_uIcc_subset_left (hx : x in s) :
    OrdConnected s ↔ forall ⦃y⦄, y in s -> [[x, y]] subseteq s :=
  ⟨fun hs => hs.uIcc_subset hx, ordConnected_of_uIcc_subset_left⟩

/--
theorem `ordConnected_iff_uIcc_subset_right` / 定理 `ordConnected_iff_uIcc_subset_right`

English:
theorem ordConnected_iff_uIcc_subset_right
  given: (hx : x in s)
  proof: by
  simp_rw [ordConnected_iff_uIcc_subset_left hx, uIcc_comm]

@[simp]

中文:
定理 ordConnected_iff_uIcc_subset_right
  条件: (hx : x in s)
  证明: by
  simp_rw [ordConnected_iff_uIcc_subset_left hx, uIcc_comm]

@[simp]

Depends on / 依赖: ordConnected_iff_uIcc_subset_left, simp_rw, uIcc_comm
-/
theorem ordConnected_iff_uIcc_subset_right (hx : x in s) :
    OrdConnected s ↔ forall ⦃y⦄, y in s -> [[y, x]] subseteq s := by
  simp_rw [ordConnected_iff_uIcc_subset_left hx, uIcc_comm]

@[simp]
/--
theorem `image_subtype_val_uIcc` / 定理 `image_subtype_val_uIcc`

English:
theorem image_subtype_val_uIcc
  given: [OrdConnected s] (a b : s)
  proof: by
  simp [uIcc, (Subtype.mono_coe (· in s)).map_inf, (Subtype.mono_coe (· in s)).map_sup]

@[simp]

中文:
定理 image_subtype_val_uIcc
  条件: [序连通 s] (a b : s)
  证明: by
  simp [uIcc, (Subtype.mono_coe (· in s)).map_inf, (Subtype.mono_coe (· in s)).map_sup]

@[simp]

Depends on / 依赖: Subtype, Subtype.mono_coe, map_inf, map_sup, mono_coe
-/
theorem image_subtype_val_uIcc [OrdConnected s] (a b : s) :
    Subtype.val '' [[a, b]] = [[a.1, b.1]] := by
  simp [uIcc, (Subtype.mono_coe (· in s)).map_inf, (Subtype.mono_coe (· in s)).map_sup]

@[simp]
/--
theorem `image_subtype_val_uIoc` / 定理 `image_subtype_val_uIoc`

English:
theorem image_subtype_val_uIoc
  given: [OrdConnected s] (a b : s)
  proof: by
  simp [uIoc, (Subtype.mono_coe (· in s)).map_inf, (Subtype.mono_coe (· in s)).map_sup]

@[simp]

中文:
定理 image_subtype_val_uIoc
  条件: [序连通 s] (a b : s)
  证明: by
  simp [uIoc, (Subtype.mono_coe (· in s)).map_inf, (Subtype.mono_coe (· in s)).map_sup]

@[simp]

Depends on / 依赖: Subtype, Subtype.mono_coe, map_inf, map_sup, mono_coe
-/
theorem image_subtype_val_uIoc [OrdConnected s] (a b : s) :
    Subtype.val '' uIoc a b = uIoc a.1 b.1 := by
  simp [uIoc, (Subtype.mono_coe (· in s)).map_inf, (Subtype.mono_coe (· in s)).map_sup]

@[simp]
/--
theorem `image_subtype_val_uIoo` / 定理 `image_subtype_val_uIoo`

English:
theorem image_subtype_val_uIoo
  given: [OrdConnected s] (a b : s)
  proof: by
  simp [uIoo, (Subtype.mono_coe (· in s)).map_inf, (Subtype.mono_coe (· in s)).map_sup]

中文:
定理 image_subtype_val_uIoo
  条件: [序连通 s] (a b : s)
  证明: by
  simp [uIoo, (Subtype.mono_coe (· in s)).map_inf, (Subtype.mono_coe (· in s)).map_sup]

Depends on / 依赖: Subtype, Subtype.mono_coe, map_inf, map_sup, mono_coe
-/
theorem image_subtype_val_uIoo [OrdConnected s] (a b : s) :
    Subtype.val '' uIoo a b = uIoo a.1 b.1 := by
  simp [uIoo, (Subtype.mono_coe (· in s)).map_inf, (Subtype.mono_coe (· in s)).map_sup]

end LinearOrder

end Set
