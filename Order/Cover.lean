/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Violeta Hernández Palacios, Grayson Burton, Floris van Doorn, Bhavik Mehta
-/
module

public import Mathlib.Order.Antisymmetrization
public import Mathlib.Order.Hom.WithTopBot
public import Mathlib.Order.Interval.Set.OrdConnected
public import Mathlib.Order.Interval.Set.WithBotTop

/-!
# The covering relation

This file proves properties of the covering relation in an order.
We say that `b` *covers* `a` if `a < b` and there is no element in between.
We say that `b` *weakly covers* `a` if `a ≤ b` and there is no element between `a` and `b`.
In a partial order this is equivalent to `a ⋖ b ∨ a = b`,
in a preorder this is equivalent to `a ⋖ b ∨ (a ≤ b ∧ b ≤ a)`

## Notation

* `a ⋖ b` means that `b` covers `a`.
* `a ⩿ b` means that `b` weakly covers `a`.
-/

public section


open Set OrderDual

variable {α β : Type*}

section WeaklyCovers

section Preorder

variable [Preorder α] [Preorder β] {a b c : α}

@[to_dual self]
/--
theorem `WCovBy.le` / 定理 `WCovBy.le`

English:
theorem WCovBy.le
  given: (h : a ⩿ b)
  statement: a <= b
  proof: h.1

中文:
定理 WCovBy.le
  条件: (h : a ⩿ b)
  结论: a <= b
  证明: h.1
-/
theorem WCovBy.le (h : a ⩿ b) : a <= b :=
  h.1

/--
theorem `WCovBy.refl` / 定理 `WCovBy.refl`

English:
theorem WCovBy.refl
  given: (a : α)
  statement: a ⩿ a
  proof: ⟨le_rfl, fun _ hc => hc.not_gt⟩

中文:
定理 WCovBy.refl
  条件: (a : α)
  结论: a ⩿ a
  证明: ⟨le_rfl, fun _ hc => hc.not_gt⟩

Depends on / 依赖: hc.not_gt, le_rfl, not_gt
-/
theorem WCovBy.refl (a : α) : a ⩿ a :=
  ⟨le_rfl, fun _ hc => hc.not_gt⟩

/--
lemma `WCovBy.rfl` / 引理 `WCovBy.rfl`

English:
lemma WCovBy.rfl
  statement: a ⩿ a
  proof: WCovBy.refl a

@[to_dual wcovBy']

中文:
引理 WCovBy.rfl
  结论: a ⩿ a
  证明: WCovBy.refl a

@[to_dual wcovBy']
-/
@[simp] lemma WCovBy.rfl : a ⩿ a := WCovBy.refl a

@[to_dual wcovBy']
/--
theorem `Eq.wcovBy` / 定理 `Eq.wcovBy`

English:
theorem Eq.wcovBy
  given: (h : a = b)
  statement: a ⩿ b
  proof: h ▸ WCovBy.rfl

@[to_dual self]

中文:
定理 相等.wcovBy
  条件: (h : a = b)
  结论: a ⩿ b
  证明: h ▸ WCovBy.rfl

@[to_dual self]
-/
protected theorem Eq.wcovBy (h : a = b) : a ⩿ b :=
  h ▸ WCovBy.rfl

@[to_dual self]
/--
theorem `wcovBy_of_le_of_le` / 定理 `wcovBy_of_le_of_le`

English:
theorem wcovBy_of_le_of_le
  given: (h1 : a <= b) (h2 : b <= a)
  statement: a ⩿ b
  proof: ⟨h1, fun _ hac hcb => (hac.trans hcb).not_ge h2⟩

@[to_dual self]
alias LE.le.wcovBy_of_le := wcovBy_of_le_of_le

中文:
定理 wcovBy_of_le_of_le
  条件: (h1 : a <= b) (h2 : b <= a)
  结论: a ⩿ b
  证明: ⟨h1, fun _ hac hcb => (hac.trans hcb).not_ge h2⟩

@[to_dual self]
alias LE.le.wcovBy_of_le := wcovBy_of_le_of_le

Depends on / 依赖: hac.trans, not_ge
-/
theorem wcovBy_of_le_of_le (h1 : a <= b) (h2 : b <= a) : a ⩿ b :=
  ⟨h1, fun _ hac hcb => (hac.trans hcb).not_ge h2⟩

@[to_dual self]
alias LE.le.wcovBy_of_le := wcovBy_of_le_of_le

/--
theorem `AntisymmRel.wcovBy` / 定理 `AntisymmRel.wcovBy`

English:
theorem AntisymmRel.wcovBy
  given: (h : AntisymmRel (· <= ·) a b)
  statement: a ⩿ b
  proof: wcovBy_of_le_of_le h.1 h.2

@[to_dual self]

中文:
定理 AntisymmRel.wcovBy
  条件: (h : AntisymmRel (· <= ·) a b)
  结论: a ⩿ b
  证明: wcovBy_of_le_of_le h.1 h.2

@[to_dual self]

Depends on / 依赖: wcovBy_of_le_of_le
-/
theorem AntisymmRel.wcovBy (h : AntisymmRel (· <= ·) a b) : a ⩿ b :=
  wcovBy_of_le_of_le h.1 h.2

@[to_dual self]
/--
theorem `WCovBy.wcovBy_iff_le` / 定理 `WCovBy.wcovBy_iff_le`

English:
theorem WCovBy.wcovBy_iff_le
  given: (hab : a ⩿ b)
  statement: b ⩿ a ↔ b <= a
  proof: ⟨fun h => h.le, fun h => h.wcovBy_of_le hab.le⟩

@[to_dual none]

中文:
定理 WCovBy.wcovBy_iff_le
  条件: (hab : a ⩿ b)
  结论: b ⩿ a ↔ b <= a
  证明: ⟨fun h => h.le, fun h => h.wcovBy_of_le hab.le⟩

@[to_dual none]

Depends on / 依赖: h.le, h.wcovBy_of_le, hab.le, wcovBy_of_le
-/
theorem WCovBy.wcovBy_iff_le (hab : a ⩿ b) : b ⩿ a ↔ b <= a :=
  ⟨fun h => h.le, fun h => h.wcovBy_of_le hab.le⟩

@[to_dual none]
/--
theorem `wcovBy_of_eq_or_eq` / 定理 `wcovBy_of_eq_or_eq`

English:
theorem wcovBy_of_eq_or_eq
  given: (hab : a <= b) (h : forall c, a <= c -> c <= b -> c = a ∨ c = b)
  statement: a ⩿ b
  proof: ⟨hab, fun c ha hb => (h c ha.le hb.le).elim ha.ne' hb.ne⟩

中文:
定理 wcovBy_of_eq_or_eq
  条件: (hab : a <= b) (h : 对任意 c, a <= c -> c <= b -> c = a ∨ c = b)
  结论: a ⩿ b
  证明: ⟨hab, fun c ha hb => (h c ha.le hb.le).elim ha.ne' hb.ne⟩

Depends on / 依赖: ha.le, ha.ne, hb.le, hb.ne
-/
theorem wcovBy_of_eq_or_eq (hab : a <= b) (h : forall c, a <= c -> c <= b -> c = a ∨ c = b) : a ⩿ b :=
  ⟨hab, fun c ha hb => (h c ha.le hb.le).elim ha.ne' hb.ne⟩

/--
theorem `AntisymmRel.trans_wcovBy` / 定理 `AntisymmRel.trans_wcovBy`

English:
theorem AntisymmRel.trans_wcovBy
  given: (hab : AntisymmRel (· <= ·) a b) (hbc : b ⩿ c)
  statement: a ⩿ c
  proof: ⟨hab.1.trans hbc.le, fun _ had hdc => hbc.2 (hab.2.trans_lt had) hdc⟩

中文:
定理 AntisymmRel.trans_wcovBy
  条件: (hab : AntisymmRel (· <= ·) a b) (hbc : b ⩿ c)
  结论: a ⩿ c
  证明: ⟨hab.1.trans hbc.le, fun _ had hdc => hbc.2 (hab.2.trans_lt had) hdc⟩

Depends on / 依赖: hbc.le, trans_lt
-/
theorem AntisymmRel.trans_wcovBy (hab : AntisymmRel (· <= ·) a b) (hbc : b ⩿ c) : a ⩿ c :=
  ⟨hab.1.trans hbc.le, fun _ had hdc => hbc.2 (hab.2.trans_lt had) hdc⟩

/--
theorem `wcovBy_congr_left` / 定理 `wcovBy_congr_left`

English:
theorem wcovBy_congr_left
  given: (hab : AntisymmRel (· <= ·) a b)
  statement: a ⩿ c ↔ b ⩿ c
  proof: ⟨hab.symm.trans_wcovBy, hab.trans_wcovBy⟩

中文:
定理 wcovBy_congr_left
  条件: (hab : AntisymmRel (· <= ·) a b)
  结论: a ⩿ c ↔ b ⩿ c
  证明: ⟨hab.symm.trans_wcovBy, hab.trans_wcovBy⟩

Depends on / 依赖: hab.symm.trans_wcovBy, hab.trans_wcovBy, trans_wcovBy
-/
theorem wcovBy_congr_left (hab : AntisymmRel (· <= ·) a b) : a ⩿ c ↔ b ⩿ c :=
  ⟨hab.symm.trans_wcovBy, hab.trans_wcovBy⟩

/--
theorem `WCovBy.trans_antisymm_rel` / 定理 `WCovBy.trans_antisymm_rel`

English:
theorem WCovBy.trans_antisymm_rel
  given: (hab : a ⩿ b) (hbc : AntisymmRel (· <= ·) b c)
  statement: a ⩿ c
  proof: ⟨hab.le.trans hbc.1, fun _ had hdc => hab.2 had hdc.trans_le hbc.2⟩

中文:
定理 WCovBy.trans_antisymm_rel
  条件: (hab : a ⩿ b) (hbc : AntisymmRel (· <= ·) b c)
  结论: a ⩿ c
  证明: ⟨hab.le.trans hbc.1, fun _ had hdc => hab.2 had hdc.trans_le hbc.2⟩

Depends on / 依赖: hab.le.trans, hdc.trans_le, trans_le
-/
theorem WCovBy.trans_antisymm_rel (hab : a ⩿ b) (hbc : AntisymmRel (· <= ·) b c) : a ⩿ c :=
⟨hab.le.trans hbc.1, fun _ had hdc => hab.2 had hdc.trans_le hbc.2⟩

/--
theorem `wcovBy_congr_right` / 定理 `wcovBy_congr_right`

English:
theorem wcovBy_congr_right
  given: (hab : AntisymmRel (· <= ·) a b)
  statement: c ⩿ a ↔ c ⩿ b
  proof: ⟨fun h => h.trans_antisymm_rel hab, fun h => h.trans_antisymm_rel hab.symm⟩

中文:
定理 wcovBy_congr_right
  条件: (hab : AntisymmRel (· <= ·) a b)
  结论: c ⩿ a ↔ c ⩿ b
  证明: ⟨fun h => h.trans_antisymm_rel hab, fun h => h.trans_antisymm_rel hab.symm⟩

Depends on / 依赖: h.trans_antisymm_rel, hab.symm, trans_antisymm_rel
-/
theorem wcovBy_congr_right (hab : AntisymmRel (· <= ·) a b) : c ⩿ a ↔ c ⩿ b :=
  ⟨fun h => h.trans_antisymm_rel hab, fun h => h.trans_antisymm_rel hab.symm⟩

/-- If `a ≤ b`, then `b` does not cover `a` iff there's an element in between. -/
@[to_dual none]
/--
theorem `not_wcovBy_iff` / 定理 `not_wcovBy_iff`

English:
theorem not_wcovBy_iff
  given: (h : a <= b)
  statement: ¬a ⩿ b ↔ exists c, a < c ∧ c < b
  proof: by
  simp_rw [WCovBy, h, true_and, not_forall, exists_prop, not_not]

@[to_dual stdRefl']

中文:
定理 not_wcovBy_iff
  条件: (h : a <= b)
  结论: ¬a ⩿ b ↔ 存在 c, a < c ∧ c < b
  证明: by
  simp_rw [WCovBy, h, true_and, not_forall, exists_prop, not_not]

@[to_dual stdRefl']

Depends on / 依赖: WCovBy, exists_prop, not_forall, not_not, simp_rw, true_and
-/
theorem not_wcovBy_iff (h : a <= b) : ¬a ⩿ b ↔ exists c, a < c ∧ c < b := by
  simp_rw [WCovBy, h, true_and, not_forall, exists_prop, not_not]

@[to_dual stdRefl']
/--
Instance `WCovBy.stdRefl` / 实例 `WCovBy.stdRefl`

English:
instance WCovBy.stdRefl
  signature: : @Std.Refl α (· ⩿ ·)
  body: ⟨WCovBy.refl⟩

@[to_dual self]

中文:
实例 WCovBy.stdRefl
  签名: : @Std.Refl α (· ⩿ ·)
  定义体: ⟨WCovBy.refl⟩

@[to_dual self]

Depends on / 依赖: WCovBy, WCovBy.refl
-/
instance WCovBy.stdRefl : @Std.Refl α (· ⩿ ·) :=
  ⟨WCovBy.refl⟩

@[to_dual self]
/--
theorem `WCovBy.Ioo_eq` / 定理 `WCovBy.Ioo_eq`

English:
theorem WCovBy.Ioo_eq
  given: (h : a ⩿ b)
  statement: Ioo a b = ∅
  proof: eq_empty_iff_forall_notMem.2 fun _ hx => h.2 hx.1 hx.2

@[to_dual self]

中文:
定理 WCovBy.Ioo_eq
  条件: (h : a ⩿ b)
  结论: 开区间 a b = ∅
  证明: eq_empty_iff_forall_notMem.2 fun _ hx => h.2 hx.1 hx.2

@[to_dual self]

Depends on / 依赖: eq_empty_iff_forall_notMem
-/
theorem WCovBy.Ioo_eq (h : a ⩿ b) : Ioo a b = ∅ :=
  eq_empty_iff_forall_notMem.2 fun _ hx => h.2 hx.1 hx.2

@[to_dual self]
/--
theorem `wcovBy_iff_Ioo_eq` / 定理 `wcovBy_iff_Ioo_eq`

English:
theorem wcovBy_iff_Ioo_eq
  statement: a ⩿ b ↔ a <= b ∧ Ioo a b = ∅
  proof: and_congr_right' by simp [eq_empty_iff_forall_notMem]

@[to_dual of_le_of_le']

中文:
定理 wcovBy_iff_Ioo_eq
  结论: a ⩿ b ↔ a <= b ∧ 开区间 a b = ∅
  证明: and_congr_right' by simp [eq_empty_iff_forall_notMem]

@[to_dual of_le_of_le']

Depends on / 依赖: and_congr_right, eq_empty_iff_forall_notMem
-/
theorem wcovBy_iff_Ioo_eq : a ⩿ b ↔ a <= b ∧ Ioo a b = ∅ :=
and_congr_right' by simp [eq_empty_iff_forall_notMem]

@[to_dual of_le_of_le']
/--
lemma `WCovBy.of_le_of_le` / 引理 `WCovBy.of_le_of_le`

English:
lemma WCovBy.of_le_of_le
  given: (hac : a ⩿ c) (hab : a <= b) (hbc : b <= c)
  statement: b ⩿ c
  proof: ⟨hbc, fun _x hbx hxc => hac.2 (hab.trans_lt hbx) hxc⟩

@[to_dual self]

中文:
引理 WCovBy.of_le_of_le
  条件: (hac : a ⩿ c) (hab : a <= b) (hbc : b <= c)
  结论: b ⩿ c
  证明: ⟨hbc, fun _x hbx hxc => hac.2 (hab.trans_lt hbx) hxc⟩

@[to_dual self]

Depends on / 依赖: hab.trans_lt, trans_lt
-/
lemma WCovBy.of_le_of_le (hac : a ⩿ c) (hab : a <= b) (hbc : b <= c) : b ⩿ c :=
  ⟨hbc, fun _x hbx hxc => hac.2 (hab.trans_lt hbx) hxc⟩

@[to_dual self]
/--
theorem `WCovBy.of_image` / 定理 `WCovBy.of_image`

English:
theorem WCovBy.of_image
  given: (f : α ↪o β) (h : f a ⩿ f b)
  statement: a ⩿ b
  proof: ⟨f.le_iff_le.mp h.le, fun _ hac hcb => h.2 (f.lt_iff_lt.mpr hac) (f.lt_iff_lt.mpr hcb)⟩

@[to_dual self]

中文:
定理 WCovBy.of_image
  条件: (f : α ↪o β) (h : f a ⩿ f b)
  结论: a ⩿ b
  证明: ⟨f.le_iff_le.mp h.le, fun _ hac hcb => h.2 (f.lt_iff_lt.mpr hac) (f.lt_iff_lt.mpr hcb)⟩

@[to_dual self]

Depends on / 依赖: f.le_iff_le.mp, f.lt_iff_lt.mpr, h.le, le_iff_le, lt_iff_lt
-/
theorem WCovBy.of_image (f : α ↪o β) (h : f a ⩿ f b) : a ⩿ b :=
  ⟨f.le_iff_le.mp h.le, fun _ hac hcb => h.2 (f.lt_iff_lt.mpr hac) (f.lt_iff_lt.mpr hcb)⟩

@[to_dual self]
/--
theorem `WCovBy.image` / 定理 `WCovBy.image`

English:
theorem WCovBy.image
  given: (f : α ↪o β) (hab : a ⩿ b) (h : (range f).OrdConnected)
  statement: f a ⩿ f b
  proof: by
  refine ⟨f.monotone hab.le, fun c ha hb => ?_⟩
  obtain ⟨c, rfl⟩ := h.out (mem_range_self _) (mem_range_self _) ⟨ha.le, hb.le⟩
  rw [f.lt_iff_lt] at ha hb
  exact hab.2 ha hb

@[to_dual self]

中文:
定理 WCovBy.像
  条件: (f : α ↪o β) (hab : a ⩿ b) (h : (range f).序连通)
  结论: f a ⩿ f b
  证明: by
  refine ⟨f.monotone hab.le, fun c ha hb => ?_⟩
  obtain ⟨c, rfl⟩ := h.out (mem_range_self _) (mem_range_self _) ⟨ha.le, hb.le⟩
  rw [f.lt_iff_lt] at ha hb
  exact hab.2 ha hb

@[to_dual self]

Depends on / 依赖: f.lt_iff_lt, f.monotone, h.out, ha.le, hab.le, hb.le, lt_iff_lt, mem_range_self, monotone
-/
theorem WCovBy.image (f : α ↪o β) (hab : a ⩿ b) (h : (range f).OrdConnected) : f a ⩿ f b := by
  refine ⟨f.monotone hab.le, fun c ha hb => ?_⟩
  obtain ⟨c, rfl⟩ := h.out (mem_range_self _) (mem_range_self _) ⟨ha.le, hb.le⟩
  rw [f.lt_iff_lt] at ha hb
  exact hab.2 ha hb

@[to_dual self]
/--
theorem `Set.OrdConnected.apply_wcovBy_apply_iff` / 定理 `Set.OrdConnected.apply_wcovBy_apply_iff`

English:
theorem Set.OrdConnected.apply_wcovBy_apply_iff
  given: (f : α ↪o β) (h : (range f).OrdConnected)
  proof: ⟨fun h2 => h2.of_image f, fun hab => hab.image f h⟩

@[simp, to_dual self]

中文:
定理 集合.序连通.apply_wcovBy_apply_iff
  条件: (f : α ↪o β) (h : (range f).序连通)
  证明: ⟨fun h2 => h2.of_image f, fun hab => hab.image f h⟩

@[simp, to_dual self]

Depends on / 依赖: h2.of_image, hab.image, of_image
-/
theorem Set.OrdConnected.apply_wcovBy_apply_iff (f : α ↪o β) (h : (range f).OrdConnected) :
    f a ⩿ f b ↔ a ⩿ b :=
  ⟨fun h2 => h2.of_image f, fun hab => hab.image f h⟩

@[simp, to_dual self]
/--
theorem `apply_wcovBy_apply_iff` / 定理 `apply_wcovBy_apply_iff`

English:
theorem apply_wcovBy_apply_iff
  given: {E : Type*} [EquivLike E α β] [OrderIsoClass E α β] (e : E)
  proof: (ordConnected_range (e : α ≃o β)).apply_wcovBy_apply_iff ((e : α ≃o β) : α ↪o β)

@[simp, to_dual self]

中文:
定理 apply_wcovBy_apply_iff
  条件: {E : 类型} [等价状 E α β] [OrderIso类 E α β] (e : E)
  证明: (ordConnected_range (e : α ≃o β)).apply_wcovBy_apply_iff ((e : α ≃o β) : α ↪o β)

@[simp, to_dual self]

Depends on / 依赖: apply_wcovBy_apply_iff, ordConnected_range
-/
theorem apply_wcovBy_apply_iff {E : Type*} [EquivLike E α β] [OrderIsoClass E α β] (e : E) :
    e a ⩿ e b ↔ a ⩿ b :=
  (ordConnected_range (e : α ≃o β)).apply_wcovBy_apply_iff ((e : α ≃o β) : α ↪o β)

@[simp, to_dual self]
/--
theorem `toDual_wcovBy_toDual_iff` / 定理 `toDual_wcovBy_toDual_iff`

English:
theorem toDual_wcovBy_toDual_iff
  statement: toDual b ⩿ toDual a ↔ a ⩿ b
  proof: and_congr_right' forall_congr' fun _ => forall_comm

@[simp, to_dual self]

中文:
定理 toDual_wcovBy_toDual_iff
  结论: toDual b ⩿ toDual a ↔ a ⩿ b
  证明: and_congr_right' forall_congr' fun _ => forall_comm

@[simp, to_dual self]

Depends on / 依赖: and_congr_right, forall_comm, forall_congr
-/
theorem toDual_wcovBy_toDual_iff : toDual b ⩿ toDual a ↔ a ⩿ b :=
and_congr_right' forall_congr' fun _ => forall_comm

@[simp, to_dual self]
/--
theorem `ofDual_wcovBy_ofDual_iff` / 定理 `ofDual_wcovBy_ofDual_iff`

English:
theorem ofDual_wcovBy_ofDual_iff
  given: {a b : αᵒᵈ}
  statement: ofDual a ⩿ ofDual b ↔ b ⩿ a
  proof: and_congr_right' forall_congr' fun _ => forall_comm

@[to_dual self]
alias ⟨_, WCovBy.toDual⟩ := toDual_wcovBy_toDual_iff

@[to_dual self]
alias ⟨_, WCovBy.ofDual⟩ := ofDual_wcovBy_ofDual_iff

中文:
定理 ofDual_wcovBy_ofDual_iff
  条件: {a b : αᵒᵈ}
  结论: ofDual a ⩿ ofDual b ↔ b ⩿ a
  证明: and_congr_right' forall_congr' fun _ => forall_comm

@[to_dual self]
alias ⟨_, WCovBy.toDual⟩ := toDual_wcovBy_toDual_iff

@[to_dual self]
alias ⟨_, WCovBy.ofDual⟩ := ofDual_wcovBy_ofDual_iff

Depends on / 依赖: and_congr_right, forall_comm, forall_congr
-/
theorem ofDual_wcovBy_ofDual_iff {a b : αᵒᵈ} : ofDual a ⩿ ofDual b ↔ b ⩿ a :=
and_congr_right' forall_congr' fun _ => forall_comm

@[to_dual self]
alias ⟨_, WCovBy.toDual⟩ := toDual_wcovBy_toDual_iff

@[to_dual self]
alias ⟨_, WCovBy.ofDual⟩ := ofDual_wcovBy_ofDual_iff

end Preorder

section PartialOrder

variable [PartialOrder α] {a b c : α}

@[to_dual none]
/--
theorem `WCovBy.eq_or_eq` / 定理 `WCovBy.eq_or_eq`

English:
theorem WCovBy.eq_or_eq
  given: (h : a ⩿ b) (h2 : a <= c) (h3 : c <= b)
  statement: c = a ∨ c = b
  proof: by
  rcases h2.eq_or_lt with (h2 | h2); · exact Or.inl h2.symm
  rcases h3.eq_or_lt with (h3 | h3); · exact Or.inr h3
  exact (h.2 h2 h3).elim

中文:
定理 WCovBy.eq_or_eq
  条件: (h : a ⩿ b) (h2 : a <= c) (h3 : c <= b)
  结论: c = a ∨ c = b
  证明: by
  rcases h2.eq_or_lt with (h2 | h2); · exact Or.inl h2.symm
  rcases h3.eq_or_lt with (h3 | h3); · exact Or.inr h3
  exact (h.2 h2 h3).elim

Depends on / 依赖: Or.inl, Or.inr, eq_or_lt, h2.eq_or_lt, h2.symm, h3.eq_or_lt
-/
theorem WCovBy.eq_or_eq (h : a ⩿ b) (h2 : a <= c) (h3 : c <= b) : c = a ∨ c = b := by
  rcases h2.eq_or_lt with (h2 | h2); · exact Or.inl h2.symm
  rcases h3.eq_or_lt with (h3 | h3); · exact Or.inr h3
  exact (h.2 h2 h3).elim

/-- An `iff` version of `WCovBy.eq_or_eq` and `wcovBy_of_eq_or_eq`. -/
@[to_dual none]
/--
theorem `wcovBy_iff_le_and_eq_or_eq` / 定理 `wcovBy_iff_le_and_eq_or_eq`

English:
theorem wcovBy_iff_le_and_eq_or_eq
  statement: a ⩿ b ↔ a <= b ∧ forall c, a <= c -> c <= b -> c = a ∨ c = b
  proof: ⟨fun h => ⟨h.le, fun _ => h.eq_or_eq⟩, And.rec wcovBy_of_eq_or_eq⟩

@[to_dual none]

中文:
定理 wcovBy_iff_le_and_eq_or_eq
  结论: a ⩿ b ↔ a <= b ∧ 对任意 c, a <= c -> c <= b -> c = a ∨ c = b
  证明: ⟨fun h => ⟨h.le, fun _ => h.eq_or_eq⟩, And.rec wcovBy_of_eq_or_eq⟩

@[to_dual none]

Depends on / 依赖: And.rec, eq_or_eq, h.eq_or_eq, h.le, wcovBy_of_eq_or_eq
-/
theorem wcovBy_iff_le_and_eq_or_eq : a ⩿ b ↔ a <= b ∧ forall c, a <= c -> c <= b -> c = a ∨ c = b :=
  ⟨fun h => ⟨h.le, fun _ => h.eq_or_eq⟩, And.rec wcovBy_of_eq_or_eq⟩

@[to_dual none]
/--
theorem `WCovBy.le_and_le_iff` / 定理 `WCovBy.le_and_le_iff`

English:
theorem WCovBy.le_and_le_iff
  given: (h : a ⩿ b)
  statement: a <= c ∧ c <= b ↔ c = a ∨ c = b
  proof: by
  refine ⟨fun h2 => h.eq_or_eq h2.1 h2.2, ?_⟩; rintro (rfl | rfl)
  exacts [⟨le_rfl, h.le⟩, ⟨h.le, le_rfl⟩]

@[to_dual none]

中文:
定理 WCovBy.le_and_le_iff
  条件: (h : a ⩿ b)
  结论: a <= c ∧ c <= b ↔ c = a ∨ c = b
  证明: by
  refine ⟨fun h2 => h.eq_or_eq h2.1 h2.2, ?_⟩; rintro (rfl | rfl)
  exacts [⟨le_rfl, h.le⟩, ⟨h.le, le_rfl⟩]

@[to_dual none]

Depends on / 依赖: eq_or_eq, exacts, h.eq_or_eq, h.le, le_rfl
-/
theorem WCovBy.le_and_le_iff (h : a ⩿ b) : a <= c ∧ c <= b ↔ c = a ∨ c = b := by
  refine ⟨fun h2 => h.eq_or_eq h2.1 h2.2, ?_⟩; rintro (rfl | rfl)
  exacts [⟨le_rfl, h.le⟩, ⟨h.le, le_rfl⟩]

@[to_dual none]
/--
theorem `WCovBy.Icc_eq` / 定理 `WCovBy.Icc_eq`

English:
theorem WCovBy.Icc_eq
  given: (h : a ⩿ b)
  statement: Icc a b = {a, b}
  proof: by
  ext c
  exact h.le_and_le_iff

中文:
定理 WCovBy.Icc_eq
  条件: (h : a ⩿ b)
  结论: 闭区间 a b = {a, b}
  证明: by
  ext c
  exact h.le_and_le_iff

Depends on / 依赖: h.le_and_le_iff, le_and_le_iff
-/
theorem WCovBy.Icc_eq (h : a ⩿ b) : Icc a b = {a, b} := by
  ext c
  exact h.le_and_le_iff

/--
theorem `WCovBy.Ico_subset` / 定理 `WCovBy.Ico_subset`

English:
theorem WCovBy.Ico_subset
  given: (h : a ⩿ b)
  statement: Ico a b subseteq {a}
  proof: by
  rw [← Icc_sdiff_right]; rw [h.Icc_eq]; rw [sdiff_singleton_subset_iff]; rw [pair_comm]

中文:
定理 WCovBy.Ico_subset
  条件: (h : a ⩿ b)
  结论: 左闭右开区间 a b subseteq {a}
  证明: by
  rw [← Icc_sdiff_right]; rw [h.Icc_eq]; rw [sdiff_singleton_subset_iff]; rw [pair_comm]

Depends on / 依赖: Icc_eq, Icc_sdiff_right, h.Icc_eq, pair_comm, sdiff_singleton_subset_iff
-/
theorem WCovBy.Ico_subset (h : a ⩿ b) : Ico a b subseteq {a} := by
  rw [← Icc_sdiff_right]; rw [h.Icc_eq]; rw [sdiff_singleton_subset_iff]; rw [pair_comm]

/--
theorem `WCovBy.Ioc_subset` / 定理 `WCovBy.Ioc_subset`

English:
theorem WCovBy.Ioc_subset
  given: (h : a ⩿ b)
  statement: Ioc a b subseteq {b}
  proof: by
  rw [← Icc_sdiff_left]; rw [h.Icc_eq]; rw [sdiff_singleton_subset_iff]

中文:
定理 WCovBy.Ioc_subset
  条件: (h : a ⩿ b)
  结论: 左开右闭区间 a b subseteq {b}
  证明: by
  rw [← Icc_sdiff_left]; rw [h.Icc_eq]; rw [sdiff_singleton_subset_iff]

Depends on / 依赖: Icc_eq, Icc_sdiff_left, h.Icc_eq, sdiff_singleton_subset_iff
-/
theorem WCovBy.Ioc_subset (h : a ⩿ b) : Ioc a b subseteq {b} := by
  rw [← Icc_sdiff_left]; rw [h.Icc_eq]; rw [sdiff_singleton_subset_iff]

end PartialOrder

section SemilatticeSup

variable [SemilatticeSup α] {a b c : α}

@[to_dual]
/--
theorem `WCovBy.sup_eq` / 定理 `WCovBy.sup_eq`

English:
theorem WCovBy.sup_eq
  given: (hac : a ⩿ c) (hbc : b ⩿ c) (hab : a != b)
  statement: a ⊔ b = c
  proof: (sup_le hac.le hbc.le).eq_of_not_lt fun h =>
    hab.lt_sup_or_lt_sup.elim (fun h' => hac.2 h' h) fun h' => hbc.2 h' h

中文:
定理 WCovBy.sup_eq
  条件: (hac : a ⩿ c) (hbc : b ⩿ c) (hab : a != b)
  结论: a ⊔ b = c
  证明: (sup_le hac.le hbc.le).eq_of_not_lt fun h =>
    hab.lt_sup_or_lt_sup.elim (fun h' => hac.2 h' h) fun h' => hbc.2 h' h

Depends on / 依赖: eq_of_not_lt, hab.lt_sup_or_lt_sup.elim, hac.le, hbc.le, lt_sup_or_lt_sup, sup_le
-/
theorem WCovBy.sup_eq (hac : a ⩿ c) (hbc : b ⩿ c) (hab : a != b) : a ⊔ b = c :=
  (sup_le hac.le hbc.le).eq_of_not_lt fun h =>
    hab.lt_sup_or_lt_sup.elim (fun h' => hac.2 h' h) fun h' => hbc.2 h' h

end SemilatticeSup

end WeaklyCovers

section LT

variable [LT α] {a b : α}

@[to_dual self]
/--
theorem `CovBy.lt` / 定理 `CovBy.lt`

English:
theorem CovBy.lt
  given: (h : a ⋖ b)
  statement: a < b
  proof: h.1

中文:
定理 CovBy.lt
  条件: (h : a ⋖ b)
  结论: a < b
  证明: h.1
-/
theorem CovBy.lt (h : a ⋖ b) : a < b :=
  h.1

/-- If `a < b`, then `b` does not cover `a` iff there's an element in between. -/
@[to_dual none]
/--
theorem `not_covBy_iff` / 定理 `not_covBy_iff`

English:
theorem not_covBy_iff
  given: (h : a < b)
  statement: ¬a ⋖ b ↔ exists c, a < c ∧ c < b
  proof: by
  simp_rw [CovBy, h, true_and, not_forall, exists_prop, not_not]

@[to_dual none]
alias ⟨exists_lt_lt_of_not_covBy, _⟩ := not_covBy_iff

@[to_dual none]
alias LT.lt.exists_lt_lt := exists_lt_lt_of_not_covBy

中文:
定理 not_covBy_iff
  条件: (h : a < b)
  结论: ¬a ⋖ b ↔ 存在 c, a < c ∧ c < b
  证明: by
  simp_rw [CovBy, h, true_and, not_forall, exists_prop, not_not]

@[to_dual none]
alias ⟨exists_lt_lt_of_not_covBy, _⟩ := not_covBy_iff

@[to_dual none]
alias LT.lt.exists_lt_lt := exists_lt_lt_of_not_covBy

Depends on / 依赖: exists_prop, not_forall, not_not, simp_rw, true_and
-/
theorem not_covBy_iff (h : a < b) : ¬a ⋖ b ↔ exists c, a < c ∧ c < b := by
  simp_rw [CovBy, h, true_and, not_forall, exists_prop, not_not]

@[to_dual none]
alias ⟨exists_lt_lt_of_not_covBy, _⟩ := not_covBy_iff

@[to_dual none]
alias LT.lt.exists_lt_lt := exists_lt_lt_of_not_covBy

/-- In a dense order, nothing covers anything. -/
@[to_dual self]
/--
theorem `not_covBy` / 定理 `not_covBy`

English:
theorem not_covBy
  given: [DenselyOrdered α]
  statement: ¬a ⋖ b
  proof: fun h =>
  let ⟨_, hc⟩ := exists_between h.1
  h.2 hc.1 hc.2

中文:
定理 not_covBy
  条件: [稠密序 α]
  结论: ¬a ⋖ b
  证明: fun h =>
  let ⟨_, hc⟩ := exists_between h.1
  h.2 hc.1 hc.2
-/
theorem not_covBy [DenselyOrdered α] : ¬a ⋖ b := fun h =>
  let ⟨_, hc⟩ := exists_between h.1
  h.2 hc.1 hc.2

/--
theorem `denselyOrdered_iff_forall_not_covBy` / 定理 `denselyOrdered_iff_forall_not_covBy`

English:
theorem denselyOrdered_iff_forall_not_covBy
  statement: DenselyOrdered α ↔ forall a b : α, ¬a ⋖ b
  proof: ⟨fun h _ _ => @not_covBy _ _ _ _ h, fun h =>
⟨fun _ _ hab => exists_lt_lt_of_not_covBy hab h _ _⟩⟩

@[to_dual self, simp]

中文:
定理 denselyOrdered_iff_对任意_not_covBy
  结论: 稠密序 α ↔ 对任意 a b : α, ¬a ⋖ b
  证明: ⟨fun h _ _ => @not_covBy _ _ _ _ h, fun h =>
⟨fun _ _ hab => exists_lt_lt_of_not_covBy hab h _ _⟩⟩

@[to_dual self, simp]

Depends on / 依赖: exists_lt_lt_of_not_covBy, not_covBy
-/
theorem denselyOrdered_iff_forall_not_covBy : DenselyOrdered α ↔ forall a b : α, ¬a ⋖ b :=
  ⟨fun h _ _ => @not_covBy _ _ _ _ h, fun h =>
⟨fun _ _ hab => exists_lt_lt_of_not_covBy hab h _ _⟩⟩

@[to_dual self, simp]
/--
theorem `toDual_covBy_toDual_iff` / 定理 `toDual_covBy_toDual_iff`

English:
theorem toDual_covBy_toDual_iff
  statement: toDual b ⋖ toDual a ↔ a ⋖ b
  proof: and_congr_right' forall_congr' fun _ => forall_comm

@[to_dual self, simp]

中文:
定理 toDual_covBy_toDual_iff
  结论: toDual b ⋖ toDual a ↔ a ⋖ b
  证明: and_congr_right' forall_congr' fun _ => forall_comm

@[to_dual self, simp]

Depends on / 依赖: and_congr_right, forall_comm, forall_congr
-/
theorem toDual_covBy_toDual_iff : toDual b ⋖ toDual a ↔ a ⋖ b :=
and_congr_right' forall_congr' fun _ => forall_comm

@[to_dual self, simp]
/--
theorem `ofDual_covBy_ofDual_iff` / 定理 `ofDual_covBy_ofDual_iff`

English:
theorem ofDual_covBy_ofDual_iff
  given: {a b : αᵒᵈ}
  statement: ofDual a ⋖ ofDual b ↔ b ⋖ a
  proof: and_congr_right' forall_congr' fun _ => forall_comm

@[to_dual self]
alias ⟨_, CovBy.toDual⟩ := toDual_covBy_toDual_iff

@[to_dual self]
alias ⟨_, CovBy.ofDual⟩ := ofDual_covBy_ofDual_iff

中文:
定理 ofDual_covBy_ofDual_iff
  条件: {a b : αᵒᵈ}
  结论: ofDual a ⋖ ofDual b ↔ b ⋖ a
  证明: and_congr_right' forall_congr' fun _ => forall_comm

@[to_dual self]
alias ⟨_, CovBy.toDual⟩ := toDual_covBy_toDual_iff

@[to_dual self]
alias ⟨_, CovBy.ofDual⟩ := ofDual_covBy_ofDual_iff

Depends on / 依赖: and_congr_right, forall_comm, forall_congr
-/
theorem ofDual_covBy_ofDual_iff {a b : αᵒᵈ} : ofDual a ⋖ ofDual b ↔ b ⋖ a :=
and_congr_right' forall_congr' fun _ => forall_comm

@[to_dual self]
alias ⟨_, CovBy.toDual⟩ := toDual_covBy_toDual_iff

@[to_dual self]
alias ⟨_, CovBy.ofDual⟩ := ofDual_covBy_ofDual_iff

end LT

section Preorder

variable [Preorder α] [Preorder β] {a b c : α}

/--
lemma `covBy_irrefl` / 引理 `covBy_irrefl`

English:
lemma covBy_irrefl
  statement: ¬ a ⋖ a
  proof: by simp [CovBy]

@[to_dual self]

中文:
引理 covBy_irrefl
  结论: ¬ a ⋖ a
  证明: by simp [CovBy]

@[to_dual self]
-/
@[simp] lemma covBy_irrefl : ¬ a ⋖ a := by simp [CovBy]

@[to_dual self]
/--
theorem `not_covBy_iff_nonempty_Ioo` / 定理 `not_covBy_iff_nonempty_Ioo`

English:
theorem not_covBy_iff_nonempty_Ioo
  given: (h : a < b)
  statement: ¬a ⋖ b ↔ (Ioo a b).Nonempty
  proof: not_covBy_iff h

@[to_dual self]

中文:
定理 not_covBy_iff_nonempty_Ioo
  条件: (h : a < b)
  结论: ¬a ⋖ b ↔ (开区间 a b).非空
  证明: not_covBy_iff h

@[to_dual self]

Depends on / 依赖: not_covBy_iff
-/
theorem not_covBy_iff_nonempty_Ioo (h : a < b) : ¬a ⋖ b ↔ (Ioo a b).Nonempty :=
  not_covBy_iff h

@[to_dual self]
/--
theorem `CovBy.le` / 定理 `CovBy.le`

English:
theorem CovBy.le
  given: (h : a ⋖ b)
  statement: a <= b
  proof: h.1.le

@[to_dual ne']

中文:
定理 CovBy.le
  条件: (h : a ⋖ b)
  结论: a <= b
  证明: h.1.le

@[to_dual ne']
-/
theorem CovBy.le (h : a ⋖ b) : a <= b :=
  h.1.le

@[to_dual ne']
/--
theorem `CovBy.ne` / 定理 `CovBy.ne`

English:
theorem CovBy.ne
  given: (h : a ⋖ b)
  statement: a != b
  proof: h.lt.ne

@[to_dual self]

中文:
定理 CovBy.ne
  条件: (h : a ⋖ b)
  结论: a != b
  证明: h.lt.ne

@[to_dual self]
-/
protected theorem CovBy.ne (h : a ⋖ b) : a != b :=
  h.lt.ne

@[to_dual self]
/--
theorem `CovBy.wcovBy` / 定理 `CovBy.wcovBy`

English:
theorem CovBy.wcovBy
  given: (h : a ⋖ b)
  statement: a ⩿ b
  proof: ⟨h.le, h.2⟩

@[to_dual self]

中文:
定理 CovBy.wcovBy
  条件: (h : a ⋖ b)
  结论: a ⩿ b
  证明: ⟨h.le, h.2⟩

@[to_dual self]
-/
protected theorem CovBy.wcovBy (h : a ⋖ b) : a ⩿ b :=
  ⟨h.le, h.2⟩

@[to_dual self]
/--
theorem `WCovBy.covBy_of_not_le` / 定理 `WCovBy.covBy_of_not_le`

English:
theorem WCovBy.covBy_of_not_le
  given: (h : a ⩿ b) (h2 : ¬b <= a)
  statement: a ⋖ b
  proof: ⟨h.le.lt_of_not_ge h2, h.2⟩

@[to_dual self]

中文:
定理 WCovBy.covBy_of_not_le
  条件: (h : a ⩿ b) (h2 : ¬b <= a)
  结论: a ⋖ b
  证明: ⟨h.le.lt_of_not_ge h2, h.2⟩

@[to_dual self]

Depends on / 依赖: h.le.lt_of_not_ge, lt_of_not_ge
-/
theorem WCovBy.covBy_of_not_le (h : a ⩿ b) (h2 : ¬b <= a) : a ⋖ b :=
  ⟨h.le.lt_of_not_ge h2, h.2⟩

@[to_dual self]
/--
theorem `WCovBy.covBy_of_lt` / 定理 `WCovBy.covBy_of_lt`

English:
theorem WCovBy.covBy_of_lt
  given: (h : a ⩿ b) (h2 : a < b)
  statement: a ⋖ b
  proof: ⟨h2, h.2⟩

中文:
定理 WCovBy.covBy_of_lt
  条件: (h : a ⩿ b) (h2 : a < b)
  结论: a ⋖ b
  证明: ⟨h2, h.2⟩
-/
theorem WCovBy.covBy_of_lt (h : a ⩿ b) (h2 : a < b) : a ⋖ b :=
  ⟨h2, h.2⟩

/--
lemma `CovBy.of_le_of_lt` / 引理 `CovBy.of_le_of_lt`

English:
lemma CovBy.of_le_of_lt
  given: (hac : a ⋖ c) (hab : a <= b) (hbc : b < c)
  statement: b ⋖ c
  proof: ⟨hbc, fun _x hbx hxc => hac.2 (hab.trans_lt hbx) hxc⟩

中文:
引理 CovBy.of_le_of_lt
  条件: (hac : a ⋖ c) (hab : a <= b) (hbc : b < c)
  结论: b ⋖ c
  证明: ⟨hbc, fun _x hbx hxc => hac.2 (hab.trans_lt hbx) hxc⟩

Depends on / 依赖: hab.trans_lt, trans_lt
-/
lemma CovBy.of_le_of_lt (hac : a ⋖ c) (hab : a <= b) (hbc : b < c) : b ⋖ c :=
  ⟨hbc, fun _x hbx hxc => hac.2 (hab.trans_lt hbx) hxc⟩

/--
lemma `CovBy.of_lt_of_le` / 引理 `CovBy.of_lt_of_le`

English:
lemma CovBy.of_lt_of_le
  given: (hac : a ⋖ c) (hab : a < b) (hbc : b <= c)
  statement: a ⋖ b
  proof: ⟨hab, fun _x hax hxb => hac.2 hax hxb.trans_le hbc⟩

@[to_dual self (reorder := a c, h₁ h₂)]

中文:
引理 CovBy.of_lt_of_le
  条件: (hac : a ⋖ c) (hab : a < b) (hbc : b <= c)
  结论: a ⋖ b
  证明: ⟨hab, fun _x hax hxb => hac.2 hax hxb.trans_le hbc⟩

@[to_dual self (reorder := a c, h₁ h₂)]

Depends on / 依赖: hxb.trans_le, trans_le
-/
lemma CovBy.of_lt_of_le (hac : a ⋖ c) (hab : a < b) (hbc : b <= c) : a ⋖ b :=
⟨hab, fun _x hax hxb => hac.2 hax hxb.trans_le hbc⟩

@[to_dual self (reorder := a c, h₁ h₂)]
/--
theorem `not_covBy_of_lt_of_lt` / 定理 `not_covBy_of_lt_of_lt`

English:
theorem not_covBy_of_lt_of_lt
  given: (h₁ : a < b) (h₂ : b < c)
  statement: ¬a ⋖ c
  proof: (not_covBy_iff (h₁.trans h₂)).2 ⟨b, h₁, h₂⟩

@[to_dual self]

中文:
定理 not_covBy_of_lt_of_lt
  条件: (h₁ : a < b) (h₂ : b < c)
  结论: ¬a ⋖ c
  证明: (not_covBy_iff (h₁.trans h₂)).2 ⟨b, h₁, h₂⟩

@[to_dual self]

Depends on / 依赖: not_covBy_iff
-/
theorem not_covBy_of_lt_of_lt (h₁ : a < b) (h₂ : b < c) : ¬a ⋖ c :=
  (not_covBy_iff (h₁.trans h₂)).2 ⟨b, h₁, h₂⟩

@[to_dual self]
/--
theorem `not_covBy_iff_exists_mem_Ioo` / 定理 `not_covBy_iff_exists_mem_Ioo`

English:
theorem not_covBy_iff_exists_mem_Ioo
  given: (h : a < b)
  statement: ¬a ⋖ b ↔ exists c, c in Set.Ioo a b
  proof: not_covBy_iff h

@[to_dual self]

中文:
定理 not_covBy_iff_存在_mem_Ioo
  条件: (h : a < b)
  结论: ¬a ⋖ b ↔ 存在 c, c in 集合.开区间 a b
  证明: not_covBy_iff h

@[to_dual self]

Depends on / 依赖: not_covBy_iff
-/
theorem not_covBy_iff_exists_mem_Ioo (h : a < b) : ¬a ⋖ b ↔ exists c, c in Set.Ioo a b :=
  not_covBy_iff h

@[to_dual self]
/--
theorem `covBy_iff_wcovBy_and_lt` / 定理 `covBy_iff_wcovBy_and_lt`

English:
theorem covBy_iff_wcovBy_and_lt
  statement: a ⋖ b ↔ a ⩿ b ∧ a < b
  proof: ⟨fun h => ⟨h.wcovBy, h.lt⟩, fun h => h.1.covBy_of_lt h.2⟩

@[to_dual self]

中文:
定理 covBy_iff_wcovBy_and_lt
  结论: a ⋖ b ↔ a ⩿ b ∧ a < b
  证明: ⟨fun h => ⟨h.wcovBy, h.lt⟩, fun h => h.1.covBy_of_lt h.2⟩

@[to_dual self]

Depends on / 依赖: covBy_of_lt, h.lt, h.wcovBy, wcovBy
-/
theorem covBy_iff_wcovBy_and_lt : a ⋖ b ↔ a ⩿ b ∧ a < b :=
  ⟨fun h => ⟨h.wcovBy, h.lt⟩, fun h => h.1.covBy_of_lt h.2⟩

@[to_dual self]
/--
theorem `covBy_iff_wcovBy_and_not_le` / 定理 `covBy_iff_wcovBy_and_not_le`

English:
theorem covBy_iff_wcovBy_and_not_le
  statement: a ⋖ b ↔ a ⩿ b ∧ ¬b <= a
  proof: ⟨fun h => ⟨h.wcovBy, h.lt.not_ge⟩, fun h => h.1.covBy_of_not_le h.2⟩

@[to_dual self]

中文:
定理 covBy_iff_wcovBy_and_not_le
  结论: a ⋖ b ↔ a ⩿ b ∧ ¬b <= a
  证明: ⟨fun h => ⟨h.wcovBy, h.lt.not_ge⟩, fun h => h.1.covBy_of_not_le h.2⟩

@[to_dual self]

Depends on / 依赖: covBy_of_not_le, h.lt.not_ge, h.wcovBy, not_ge, wcovBy
-/
theorem covBy_iff_wcovBy_and_not_le : a ⋖ b ↔ a ⩿ b ∧ ¬b <= a :=
  ⟨fun h => ⟨h.wcovBy, h.lt.not_ge⟩, fun h => h.1.covBy_of_not_le h.2⟩

@[to_dual self]
/--
theorem `wcovBy_iff_covBy_or_le_and_le` / 定理 `wcovBy_iff_covBy_or_le_and_le`

English:
theorem wcovBy_iff_covBy_or_le_and_le
  statement: a ⩿ b ↔ a ⋖ b ∨ a <= b ∧ b <= a
  proof: ⟨fun h => or_iff_not_imp_right.mpr fun h' => h.covBy_of_not_le fun hba => h' ⟨h.le, hba⟩,
    fun h' => h'.elim (fun h => h.wcovBy) fun h => h.1.wcovBy_of_le h.2⟩

@[to_dual self]
alias ⟨WCovBy.covBy_or_le_and_le, _⟩ := wcovBy_iff_covBy_or_le_and_le

中文:
定理 wcovBy_iff_covBy_or_le_and_le
  结论: a ⩿ b ↔ a ⋖ b ∨ a <= b ∧ b <= a
  证明: ⟨fun h => or_iff_not_imp_right.mpr fun h' => h.covBy_of_not_le fun hba => h' ⟨h.le, hba⟩,
    fun h' => h'.elim (fun h => h.wcovBy) fun h => h.1.wcovBy_of_le h.2⟩

@[to_dual self]
alias ⟨WCovBy.covBy_or_le_and_le, _⟩ := wcovBy_iff_covBy_or_le_and_le

Depends on / 依赖: covBy_of_not_le, h.covBy_of_not_le, h.le, h.wcovBy, or_iff_not_imp_right, or_iff_not_imp_right.mpr, wcovBy, wcovBy_of_le
-/
theorem wcovBy_iff_covBy_or_le_and_le : a ⩿ b ↔ a ⋖ b ∨ a <= b ∧ b <= a :=
  ⟨fun h => or_iff_not_imp_right.mpr fun h' => h.covBy_of_not_le fun hba => h' ⟨h.le, hba⟩,
    fun h' => h'.elim (fun h => h.wcovBy) fun h => h.1.wcovBy_of_le h.2⟩

@[to_dual self]
alias ⟨WCovBy.covBy_or_le_and_le, _⟩ := wcovBy_iff_covBy_or_le_and_le

/--
theorem `AntisymmRel.trans_covBy` / 定理 `AntisymmRel.trans_covBy`

English:
theorem AntisymmRel.trans_covBy
  given: (hab : AntisymmRel (· <= ·) a b) (hbc : b ⋖ c)
  statement: a ⋖ c
  proof: ⟨hab.1.trans_lt hbc.lt, fun _ had hdc => hbc.2 (hab.2.trans_lt had) hdc⟩

中文:
定理 AntisymmRel.trans_covBy
  条件: (hab : AntisymmRel (· <= ·) a b) (hbc : b ⋖ c)
  结论: a ⋖ c
  证明: ⟨hab.1.trans_lt hbc.lt, fun _ had hdc => hbc.2 (hab.2.trans_lt had) hdc⟩

Depends on / 依赖: hbc.lt, trans_lt
-/
theorem AntisymmRel.trans_covBy (hab : AntisymmRel (· <= ·) a b) (hbc : b ⋖ c) : a ⋖ c :=
  ⟨hab.1.trans_lt hbc.lt, fun _ had hdc => hbc.2 (hab.2.trans_lt had) hdc⟩

/--
theorem `covBy_congr_left` / 定理 `covBy_congr_left`

English:
theorem covBy_congr_left
  given: (hab : AntisymmRel (· <= ·) a b)
  statement: a ⋖ c ↔ b ⋖ c
  proof: ⟨hab.symm.trans_covBy, hab.trans_covBy⟩

中文:
定理 covBy_congr_left
  条件: (hab : AntisymmRel (· <= ·) a b)
  结论: a ⋖ c ↔ b ⋖ c
  证明: ⟨hab.symm.trans_covBy, hab.trans_covBy⟩

Depends on / 依赖: hab.symm.trans_covBy, hab.trans_covBy, trans_covBy
-/
theorem covBy_congr_left (hab : AntisymmRel (· <= ·) a b) : a ⋖ c ↔ b ⋖ c :=
  ⟨hab.symm.trans_covBy, hab.trans_covBy⟩

/--
theorem `CovBy.trans_antisymmRel` / 定理 `CovBy.trans_antisymmRel`

English:
theorem CovBy.trans_antisymmRel
  given: (hab : a ⋖ b) (hbc : AntisymmRel (· <= ·) b c)
  statement: a ⋖ c
  proof: ⟨hab.lt.trans_le hbc.1, fun _ had hdb => hab.2 had hdb.trans_le hbc.2⟩

中文:
定理 CovBy.trans_antisymmRel
  条件: (hab : a ⋖ b) (hbc : AntisymmRel (· <= ·) b c)
  结论: a ⋖ c
  证明: ⟨hab.lt.trans_le hbc.1, fun _ had hdb => hab.2 had hdb.trans_le hbc.2⟩

Depends on / 依赖: hab.lt.trans_le, hdb.trans_le, trans_le
-/
theorem CovBy.trans_antisymmRel (hab : a ⋖ b) (hbc : AntisymmRel (· <= ·) b c) : a ⋖ c :=
⟨hab.lt.trans_le hbc.1, fun _ had hdb => hab.2 had hdb.trans_le hbc.2⟩

/--
theorem `covBy_congr_right` / 定理 `covBy_congr_right`

English:
theorem covBy_congr_right
  given: (hab : AntisymmRel (· <= ·) a b)
  statement: c ⋖ a ↔ c ⋖ b
  proof: ⟨fun h => h.trans_antisymmRel hab, fun h => h.trans_antisymmRel hab.symm⟩

中文:
定理 covBy_congr_right
  条件: (hab : AntisymmRel (· <= ·) a b)
  结论: c ⋖ a ↔ c ⋖ b
  证明: ⟨fun h => h.trans_antisymmRel hab, fun h => h.trans_antisymmRel hab.symm⟩

Depends on / 依赖: h.trans_antisymmRel, hab.symm, trans_antisymmRel
-/
theorem covBy_congr_right (hab : AntisymmRel (· <= ·) a b) : c ⋖ a ↔ c ⋖ b :=
  ⟨fun h => h.trans_antisymmRel hab, fun h => h.trans_antisymmRel hab.symm⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsNonstrictStrictOrder α (· ⩿ ·) (· ⋖ ·)
  body: ⟨fun _ _ =>
covBy_iff_wcovBy_and_not_le.trans and_congr_right fun h => h.wcovBy_iff_le.not.symm⟩

中文:
实例 :
  签名: 是NonstrictStrict序 α (· ⩿ ·) (· ⋖ ·)
  定义体: ⟨fun _ _ =>
covBy_iff_wcovBy_and_not_le.trans and_congr_right fun h => h.wcovBy_iff_le.not.symm⟩

Depends on / 依赖: and_congr_right, covBy_iff_wcovBy_and_not_le, covBy_iff_wcovBy_and_not_le.trans, h.wcovBy_iff_le.not.symm, wcovBy_iff_le
-/
instance : IsNonstrictStrictOrder α (· ⩿ ·) (· ⋖ ·) :=
  ⟨fun _ _ =>
covBy_iff_wcovBy_and_not_le.trans and_congr_right fun h => h.wcovBy_iff_le.not.symm⟩

/--
Instance `CovBy.irrefl` / 实例 `CovBy.irrefl`

English:
instance CovBy.irrefl
  signature: : @Std.Irrefl α (· ⋖ ·)
  body: ⟨fun _ ha => ha.ne rfl⟩

@[to_dual self]

中文:
实例 CovBy.irrefl
  签名: : @Std.Irrefl α (· ⋖ ·)
  定义体: ⟨fun _ ha => ha.ne rfl⟩

@[to_dual self]

Depends on / 依赖: ha.ne
-/
instance CovBy.irrefl : @Std.Irrefl α (· ⋖ ·) :=
  ⟨fun _ ha => ha.ne rfl⟩

@[to_dual self]
/--
theorem `CovBy.Ioo_eq` / 定理 `CovBy.Ioo_eq`

English:
theorem CovBy.Ioo_eq
  given: (h : a ⋖ b)
  statement: Ioo a b = ∅
  proof: h.wcovBy.Ioo_eq

@[to_dual self]

中文:
定理 CovBy.Ioo_eq
  条件: (h : a ⋖ b)
  结论: 开区间 a b = ∅
  证明: h.wcovBy.Ioo_eq

@[to_dual self]

Depends on / 依赖: Ioo_eq, h.wcovBy.Ioo_eq, wcovBy
-/
theorem CovBy.Ioo_eq (h : a ⋖ b) : Ioo a b = ∅ :=
  h.wcovBy.Ioo_eq

@[to_dual self]
/--
theorem `covBy_iff_Ioo_eq` / 定理 `covBy_iff_Ioo_eq`

English:
theorem covBy_iff_Ioo_eq
  statement: a ⋖ b ↔ a < b ∧ Ioo a b = ∅
  proof: and_congr_right' by simp [eq_empty_iff_forall_notMem]

@[to_dual self]

中文:
定理 covBy_iff_Ioo_eq
  结论: a ⋖ b ↔ a < b ∧ 开区间 a b = ∅
  证明: and_congr_right' by simp [eq_empty_iff_forall_notMem]

@[to_dual self]

Depends on / 依赖: and_congr_right, eq_empty_iff_forall_notMem
-/
theorem covBy_iff_Ioo_eq : a ⋖ b ↔ a < b ∧ Ioo a b = ∅ :=
and_congr_right' by simp [eq_empty_iff_forall_notMem]

@[to_dual self]
/--
theorem `CovBy.of_image` / 定理 `CovBy.of_image`

English:
theorem CovBy.of_image
  given: (f : α ↪o β) (h : f a ⋖ f b)
  statement: a ⋖ b
  proof: ⟨f.lt_iff_lt.mp h.lt, fun _ hac hcb => h.2 (f.lt_iff_lt.mpr hac) (f.lt_iff_lt.mpr hcb)⟩

@[to_dual self]

中文:
定理 CovBy.of_image
  条件: (f : α ↪o β) (h : f a ⋖ f b)
  结论: a ⋖ b
  证明: ⟨f.lt_iff_lt.mp h.lt, fun _ hac hcb => h.2 (f.lt_iff_lt.mpr hac) (f.lt_iff_lt.mpr hcb)⟩

@[to_dual self]

Depends on / 依赖: f.lt_iff_lt.mp, f.lt_iff_lt.mpr, h.lt, lt_iff_lt
-/
theorem CovBy.of_image (f : α ↪o β) (h : f a ⋖ f b) : a ⋖ b :=
  ⟨f.lt_iff_lt.mp h.lt, fun _ hac hcb => h.2 (f.lt_iff_lt.mpr hac) (f.lt_iff_lt.mpr hcb)⟩

@[to_dual self]
/--
theorem `CovBy.image` / 定理 `CovBy.image`

English:
theorem CovBy.image
  given: (f : α ↪o β) (hab : a ⋖ b) (h : (range f).OrdConnected)
  statement: f a ⋖ f b
  proof: (hab.wcovBy.image f h).covBy_of_lt f.strictMono hab.lt

@[to_dual self]

中文:
定理 CovBy.像
  条件: (f : α ↪o β) (hab : a ⋖ b) (h : (range f).序连通)
  结论: f a ⋖ f b
  证明: (hab.wcovBy.image f h).covBy_of_lt f.strictMono hab.lt

@[to_dual self]

Depends on / 依赖: covBy_of_lt, f.strictMono, hab.lt, hab.wcovBy.image, strictMono, wcovBy
-/
theorem CovBy.image (f : α ↪o β) (hab : a ⋖ b) (h : (range f).OrdConnected) : f a ⋖ f b :=
(hab.wcovBy.image f h).covBy_of_lt f.strictMono hab.lt

@[to_dual self]
/--
theorem `Set.OrdConnected.apply_covBy_apply_iff` / 定理 `Set.OrdConnected.apply_covBy_apply_iff`

English:
theorem Set.OrdConnected.apply_covBy_apply_iff
  given: (f : α ↪o β) (h : (range f).OrdConnected)
  proof: ⟨CovBy.of_image f, fun hab => hab.image f h⟩

@[to_dual self, simp]

中文:
定理 集合.序连通.apply_covBy_apply_iff
  条件: (f : α ↪o β) (h : (range f).序连通)
  证明: ⟨CovBy.of_image f, fun hab => hab.image f h⟩

@[to_dual self, simp]

Depends on / 依赖: CovBy.of_image, hab.image, of_image
-/
theorem Set.OrdConnected.apply_covBy_apply_iff (f : α ↪o β) (h : (range f).OrdConnected) :
    f a ⋖ f b ↔ a ⋖ b :=
  ⟨CovBy.of_image f, fun hab => hab.image f h⟩

@[to_dual self, simp]
/--
theorem `apply_covBy_apply_iff` / 定理 `apply_covBy_apply_iff`

English:
theorem apply_covBy_apply_iff
  given: {E : Type*} [EquivLike E α β] [OrderIsoClass E α β] (e : E)
  proof: (ordConnected_range (e : α ≃o β)).apply_covBy_apply_iff ((e : α ≃o β) : α ↪o β)

@[to_dual none]

中文:
定理 apply_covBy_apply_iff
  条件: {E : 类型} [等价状 E α β] [OrderIso类 E α β] (e : E)
  证明: (ordConnected_range (e : α ≃o β)).apply_covBy_apply_iff ((e : α ≃o β) : α ↪o β)

@[to_dual none]

Depends on / 依赖: apply_covBy_apply_iff, ordConnected_range
-/
theorem apply_covBy_apply_iff {E : Type*} [EquivLike E α β] [OrderIsoClass E α β] (e : E) :
    e a ⋖ e b ↔ a ⋖ b :=
  (ordConnected_range (e : α ≃o β)).apply_covBy_apply_iff ((e : α ≃o β) : α ↪o β)

@[to_dual none]
/--
theorem `covBy_of_eq_or_eq` / 定理 `covBy_of_eq_or_eq`

English:
theorem covBy_of_eq_or_eq
  given: (hab : a < b) (h : forall c, a <= c -> c <= b -> c = a ∨ c = b)
  statement: a ⋖ b
  proof: ⟨hab, fun c ha hb => (h c ha.le hb.le).elim ha.ne' hb.ne⟩

中文:
定理 covBy_of_eq_or_eq
  条件: (hab : a < b) (h : 对任意 c, a <= c -> c <= b -> c = a ∨ c = b)
  结论: a ⋖ b
  证明: ⟨hab, fun c ha hb => (h c ha.le hb.le).elim ha.ne' hb.ne⟩

Depends on / 依赖: ha.le, ha.ne, hb.le, hb.ne
-/
theorem covBy_of_eq_or_eq (hab : a < b) (h : forall c, a <= c -> c <= b -> c = a ∨ c = b) : a ⋖ b :=
  ⟨hab, fun c ha hb => (h c ha.le hb.le).elim ha.ne' hb.ne⟩

end Preorder

section PartialOrder

variable [PartialOrder α] {a b c : α}

@[to_dual none]
/--
theorem `WCovBy.covBy_of_ne` / 定理 `WCovBy.covBy_of_ne`

English:
theorem WCovBy.covBy_of_ne
  given: (h : a ⩿ b) (h2 : a != b)
  statement: a ⋖ b
  proof: ⟨h.le.lt_of_ne h2, h.2⟩

@[to_dual none]

中文:
定理 WCovBy.covBy_of_ne
  条件: (h : a ⩿ b) (h2 : a != b)
  结论: a ⋖ b
  证明: ⟨h.le.lt_of_ne h2, h.2⟩

@[to_dual none]

Depends on / 依赖: h.le.lt_of_ne, lt_of_ne
-/
theorem WCovBy.covBy_of_ne (h : a ⩿ b) (h2 : a != b) : a ⋖ b :=
  ⟨h.le.lt_of_ne h2, h.2⟩

@[to_dual none]
/--
theorem `covBy_iff_wcovBy_and_ne` / 定理 `covBy_iff_wcovBy_and_ne`

English:
theorem covBy_iff_wcovBy_and_ne
  statement: a ⋖ b ↔ a ⩿ b ∧ a != b
  proof: ⟨fun h => ⟨h.wcovBy, h.ne⟩, fun h => h.1.covBy_of_ne h.2⟩

@[to_dual none]

中文:
定理 covBy_iff_wcovBy_and_ne
  结论: a ⋖ b ↔ a ⩿ b ∧ a != b
  证明: ⟨fun h => ⟨h.wcovBy, h.ne⟩, fun h => h.1.covBy_of_ne h.2⟩

@[to_dual none]

Depends on / 依赖: covBy_of_ne, h.ne, h.wcovBy, wcovBy
-/
theorem covBy_iff_wcovBy_and_ne : a ⋖ b ↔ a ⩿ b ∧ a != b :=
  ⟨fun h => ⟨h.wcovBy, h.ne⟩, fun h => h.1.covBy_of_ne h.2⟩

@[to_dual none]
/--
theorem `wcovBy_iff_covBy_or_eq` / 定理 `wcovBy_iff_covBy_or_eq`

English:
theorem wcovBy_iff_covBy_or_eq
  statement: a ⩿ b ↔ a ⋖ b ∨ a = b
  proof: by
  rw [le_antisymm_iff]; rw [wcovBy_iff_covBy_or_le_and_le]

@[to_dual none]

中文:
定理 wcovBy_iff_covBy_or_eq
  结论: a ⩿ b ↔ a ⋖ b ∨ a = b
  证明: by
  rw [le_antisymm_iff]; rw [wcovBy_iff_covBy_or_le_and_le]

@[to_dual none]

Depends on / 依赖: le_antisymm_iff, wcovBy_iff_covBy_or_le_and_le
-/
theorem wcovBy_iff_covBy_or_eq : a ⩿ b ↔ a ⋖ b ∨ a = b := by
  rw [le_antisymm_iff]; rw [wcovBy_iff_covBy_or_le_and_le]

@[to_dual none]
/--
theorem `wcovBy_iff_eq_or_covBy` / 定理 `wcovBy_iff_eq_or_covBy`

English:
theorem wcovBy_iff_eq_or_covBy
  statement: a ⩿ b ↔ a = b ∨ a ⋖ b
  proof: wcovBy_iff_covBy_or_eq.trans or_comm

@[to_dual none]
alias ⟨WCovBy.covBy_or_eq, _⟩ := wcovBy_iff_covBy_or_eq

@[to_dual none]
alias ⟨WCovBy.eq_or_covBy, _⟩ := wcovBy_iff_eq_or_covBy

@[to_dual none]

中文:
定理 wcovBy_iff_eq_or_covBy
  结论: a ⩿ b ↔ a = b ∨ a ⋖ b
  证明: wcovBy_iff_covBy_or_eq.trans or_comm

@[to_dual none]
alias ⟨WCovBy.covBy_or_eq, _⟩ := wcovBy_iff_covBy_or_eq

@[to_dual none]
alias ⟨WCovBy.eq_or_covBy, _⟩ := wcovBy_iff_eq_or_covBy

@[to_dual none]

Depends on / 依赖: or_comm, wcovBy_iff_covBy_or_eq, wcovBy_iff_covBy_or_eq.trans
-/
theorem wcovBy_iff_eq_or_covBy : a ⩿ b ↔ a = b ∨ a ⋖ b :=
  wcovBy_iff_covBy_or_eq.trans or_comm

@[to_dual none]
alias ⟨WCovBy.covBy_or_eq, _⟩ := wcovBy_iff_covBy_or_eq

@[to_dual none]
alias ⟨WCovBy.eq_or_covBy, _⟩ := wcovBy_iff_eq_or_covBy

@[to_dual none]
/--
theorem `CovBy.eq_or_eq` / 定理 `CovBy.eq_or_eq`

English:
theorem CovBy.eq_or_eq
  given: (h : a ⋖ b) (h2 : a <= c) (h3 : c <= b)
  statement: c = a ∨ c = b
  proof: h.wcovBy.eq_or_eq h2 h3

中文:
定理 CovBy.eq_or_eq
  条件: (h : a ⋖ b) (h2 : a <= c) (h3 : c <= b)
  结论: c = a ∨ c = b
  证明: h.wcovBy.eq_or_eq h2 h3

Depends on / 依赖: eq_or_eq, h.wcovBy.eq_or_eq, wcovBy
-/
theorem CovBy.eq_or_eq (h : a ⋖ b) (h2 : a <= c) (h3 : c <= b) : c = a ∨ c = b :=
  h.wcovBy.eq_or_eq h2 h3

/-- An `iff` version of `CovBy.eq_or_eq` and `covBy_of_eq_or_eq`. -/
@[to_dual none]
/--
theorem `covBy_iff_lt_and_eq_or_eq` / 定理 `covBy_iff_lt_and_eq_or_eq`

English:
theorem covBy_iff_lt_and_eq_or_eq
  statement: a ⋖ b ↔ a < b ∧ forall c, a <= c -> c <= b -> c = a ∨ c = b
  proof: ⟨fun h => ⟨h.lt, fun _ => h.eq_or_eq⟩, And.rec covBy_of_eq_or_eq⟩

@[to_dual]

中文:
定理 covBy_iff_lt_and_eq_or_eq
  结论: a ⋖ b ↔ a < b ∧ 对任意 c, a <= c -> c <= b -> c = a ∨ c = b
  证明: ⟨fun h => ⟨h.lt, fun _ => h.eq_or_eq⟩, And.rec covBy_of_eq_or_eq⟩

@[to_dual]

Depends on / 依赖: And.rec, covBy_of_eq_or_eq, eq_or_eq, h.eq_or_eq, h.lt
-/
theorem covBy_iff_lt_and_eq_or_eq : a ⋖ b ↔ a < b ∧ forall c, a <= c -> c <= b -> c = a ∨ c = b :=
  ⟨fun h => ⟨h.lt, fun _ => h.eq_or_eq⟩, And.rec covBy_of_eq_or_eq⟩

@[to_dual]
/--
theorem `CovBy.Ico_eq` / 定理 `CovBy.Ico_eq`

English:
theorem CovBy.Ico_eq
  given: (h : a ⋖ b)
  statement: Ico a b = {a}
  proof: by
  rw [← Ioo_union_left h.lt]; rw [h.Ioo_eq]; rw [empty_union]

@[to_dual none]

中文:
定理 CovBy.Ico_eq
  条件: (h : a ⋖ b)
  结论: 左闭右开区间 a b = {a}
  证明: by
  rw [← Ioo_union_left h.lt]; rw [h.Ioo_eq]; rw [empty_union]

@[to_dual none]

Depends on / 依赖: Ioo_eq, Ioo_union_left, empty_union, h.Ioo_eq, h.lt
-/
theorem CovBy.Ico_eq (h : a ⋖ b) : Ico a b = {a} := by
  rw [← Ioo_union_left h.lt]; rw [h.Ioo_eq]; rw [empty_union]

@[to_dual none]
/--
theorem `CovBy.Icc_eq` / 定理 `CovBy.Icc_eq`

English:
theorem CovBy.Icc_eq
  given: (h : a ⋖ b)
  statement: Icc a b = {a, b}
  proof: h.wcovBy.Icc_eq

@[to_dual]

中文:
定理 CovBy.Icc_eq
  条件: (h : a ⋖ b)
  结论: 闭区间 a b = {a, b}
  证明: h.wcovBy.Icc_eq

@[to_dual]

Depends on / 依赖: Algebra, Algebra.EssFiniteType, Algebra.EssFiniteType.finset, EssFiniteType, Icc_eq, f.toAlgebra, finset, h.wcovBy.Icc_eq, toAlgebra, wcovBy
-/
theorem CovBy.Icc_eq (h : a ⋖ b) : Icc a b = {a, b} :=
  h.wcovBy.Icc_eq

@[to_dual]
/--
theorem `Set.Ico_eq_singleton_iff` / 定理 `Set.Ico_eq_singleton_iff`

English:
theorem Set.Ico_eq_singleton_iff
  statement: Ico a b = {c} ↔ a = c ∧ a ⋖ b where
  proof: by
    simp_rw [Set.ext_iff, mem_Ico, mem_singleton_iff] at h
    have ⟨hac, hcb⟩ := (h c).mpr rfl
    obtain rfl := (h a).mp ⟨le_refl a, hac.trans_lt hcb⟩
    exact ⟨rfl, ⟨hcb, fun d hcd hdb => hcd.ne ((h d).mp ⟨hcd.le, hdb⟩).symm⟩⟩
  mpr := fun ⟨rfl, hcov⟩ => hcov.Ico_eq

@[to_dual Ioc_eq_singleton_right_iff]

中文:
定理 集合.Ico_eq_singleton_iff
  结论: 左闭右开区间 a b = {c} ↔ a = c ∧ a ⋖ b where
  证明: by
    simp_rw [Set.ext_iff, mem_Ico, mem_singleton_iff] at h
    have ⟨hac, hcb⟩ := (h c).mpr rfl
    obtain rfl := (h a).mp ⟨le_refl a, hac.trans_lt hcb⟩
    exact ⟨rfl, ⟨hcb, fun d hcd hdb => hcd.ne ((h d).mp ⟨hcd.le, hdb⟩).symm⟩⟩
  mpr := fun ⟨rfl, hcov⟩ => hcov.Ico_eq

@[to_dual Ioc_eq_singleton_right_iff]

Depends on / 依赖: Ico_eq, Set.ext_iff, ext_iff, hac.trans_lt, hcd.le, hcd.ne, hcov.Ico_eq, le_refl, mem_Ico, mem_singleton_iff, simp_rw, trans_lt
-/
theorem Set.Ico_eq_singleton_iff : Ico a b = {c} ↔ a = c ∧ a ⋖ b where
  mp h := by
    simp_rw [Set.ext_iff, mem_Ico, mem_singleton_iff] at h
    have ⟨hac, hcb⟩ := (h c).mpr rfl
    obtain rfl := (h a).mp ⟨le_refl a, hac.trans_lt hcb⟩
    exact ⟨rfl, ⟨hcb, fun d hcd hdb => hcd.ne ((h d).mp ⟨hcd.le, hdb⟩).symm⟩⟩
  mpr := fun ⟨rfl, hcov⟩ => hcov.Ico_eq

@[to_dual Ioc_eq_singleton_right_iff]
/--
lemma `Set.Ico_eq_singleton_left_iff` / 引理 `Set.Ico_eq_singleton_left_iff`

English:
lemma Set.Ico_eq_singleton_left_iff
  statement: Ico a b = {a} ↔ a ⋖ b
  proof: by
  simp [Ico_eq_singleton_iff]

中文:
引理 集合.Ico_eq_singleton_left_iff
  结论: 左闭右开区间 a b = {a} ↔ a ⋖ b
  证明: by
  simp [Ico_eq_singleton_iff]

Depends on / 依赖: Ico_eq_singleton_iff
-/
lemma Set.Ico_eq_singleton_left_iff : Ico a b = {a} ↔ a ⋖ b := by
  simp [Ico_eq_singleton_iff]

end PartialOrder

section LinearOrder

variable [LinearOrder α] {a b c : α}

@[to_dual ge_of_gt]
/--
theorem `WCovBy.le_of_lt` / 定理 `WCovBy.le_of_lt`

English:
theorem WCovBy.le_of_lt
  given: (hab : a ⩿ b) (hcb : c < b)
  statement: c <= a
  proof: not_lt.1 fun hac => hab.2 hac hcb

@[to_dual ge_of_gt]

中文:
定理 WCovBy.le_of_lt
  条件: (hab : a ⩿ b) (hcb : c < b)
  结论: c <= a
  证明: not_lt.1 fun hac => hab.2 hac hcb

@[to_dual ge_of_gt]

Depends on / 依赖: not_lt
-/
theorem WCovBy.le_of_lt (hab : a ⩿ b) (hcb : c < b) : c <= a :=
  not_lt.1 fun hac => hab.2 hac hcb

@[to_dual ge_of_gt]
/--
theorem `CovBy.le_of_lt` / 定理 `CovBy.le_of_lt`

English:
theorem CovBy.le_of_lt
  given: (hab : a ⋖ b)
  statement: c < b -> c <= a
  proof: hab.wcovBy.le_of_lt

中文:
定理 CovBy.le_of_lt
  条件: (hab : a ⋖ b)
  结论: c < b -> c <= a
  证明: hab.wcovBy.le_of_lt

Depends on / 依赖: hab.wcovBy.le_of_lt, le_of_lt, wcovBy
-/
theorem CovBy.le_of_lt (hab : a ⋖ b) : c < b -> c <= a :=
  hab.wcovBy.le_of_lt

/--
theorem `CovBy.Ioi_eq` / 定理 `CovBy.Ioi_eq`

English:
theorem CovBy.Ioi_eq
  given: (h : a ⋖ b)
  statement: Ioi a = Ici b
  proof: by
  rw [← Ioo_union_Ici_eq_Ioi h.lt]; rw [h.Ioo_eq]; rw [empty_union]

@[to_dual existing]

中文:
定理 CovBy.Ioi_eq
  条件: (h : a ⋖ b)
  结论: 左开右无界区间 a = 左闭右无界区间 b
  证明: by
  rw [← Ioo_union_Ici_eq_Ioi h.lt]; rw [h.Ioo_eq]; rw [empty_union]

@[to_dual existing]

Depends on / 依赖: Ioo_eq, Ioo_union_Ici_eq_Ioi, empty_union, h.Ioo_eq, h.lt
-/
theorem CovBy.Ioi_eq (h : a ⋖ b) : Ioi a = Ici b := by
  rw [← Ioo_union_Ici_eq_Ioi h.lt]; rw [h.Ioo_eq]; rw [empty_union]

@[to_dual existing]
/--
theorem `CovBy.Iio_eq` / 定理 `CovBy.Iio_eq`

English:
theorem CovBy.Iio_eq
  given: (h : a ⋖ b)
  statement: Iio b = Iic a
  proof: by
  rw [← Iic_union_Ioo_eq_Iio h.lt]; rw [h.Ioo_eq]; rw [union_empty]

@[to_dual]

中文:
定理 CovBy.Iio_eq
  条件: (h : a ⋖ b)
  结论: 左无界右开区间 b = 左无界右闭区间 a
  证明: by
  rw [← Iic_union_Ioo_eq_Iio h.lt]; rw [h.Ioo_eq]; rw [union_empty]

@[to_dual]

Depends on / 依赖: Iic_union_Ioo_eq_Iio, Ioo_eq, h.Ioo_eq, h.lt, union_empty
-/
theorem CovBy.Iio_eq (h : a ⋖ b) : Iio b = Iic a := by
  rw [← Iic_union_Ioo_eq_Iio h.lt]; rw [h.Ioo_eq]; rw [union_empty]

@[to_dual]
/--
theorem `CovBy.Ioo_eq_Ico` / 定理 `CovBy.Ioo_eq_Ico`

English:
theorem CovBy.Ioo_eq_Ico
  given: (h : a ⋖ b) (c : α)
  statement: Ioo a c = Ico b c
  proof: subset_antisymm (fun _x hx => ⟨h.ge_of_gt hx.1, hx.2⟩) Ico_subset_Ioo_left h.lt

@[to_dual none]

中文:
定理 CovBy.Ioo_eq_Ico
  条件: (h : a ⋖ b) (c : α)
  结论: 开区间 a c = 左闭右开区间 b c
  证明: subset_antisymm (fun _x hx => ⟨h.ge_of_gt hx.1, hx.2⟩) Ico_subset_Ioo_left h.lt

@[to_dual none]

Depends on / 依赖: Ico_subset_Ioo_left, ge_of_gt, h.ge_of_gt, h.lt, subset_antisymm
-/
theorem CovBy.Ioo_eq_Ico (h : a ⋖ b) (c : α) : Ioo a c = Ico b c :=
subset_antisymm (fun _x hx => ⟨h.ge_of_gt hx.1, hx.2⟩) Ico_subset_Ioo_left h.lt

@[to_dual none]
/--
theorem `Set.Ioo_eq_singleton_iff` / 定理 `Set.Ioo_eq_singleton_iff`

English:
theorem Set.Ioo_eq_singleton_iff
  statement: Ioo a b = {c} ↔ a ⋖ c ∧ c ⋖ b where
  proof: by
    simp_rw [Set.ext_iff, mem_Ioo, mem_singleton_iff] at h
    have ⟨hac, hcb⟩ := (h c).mpr rfl
    exact ⟨⟨hac, fun d had hdc => hdc.ne ((h d).mp ⟨had, hdc.trans hcb⟩)⟩,
      ⟨hcb, fun d hcd hdb => hcd.ne ((h d).mp ⟨hac.trans hcd, hdb⟩).symm⟩⟩
  mpr := fun ⟨hac, hcb⟩ => by
    rw [← Ioc_union_Ico_eq_Ioo hac.lt hcb.lt]; rw [hac.Ioc_eq]; rw [hcb.Ico_eq]; rw [union_self]

@[to_dual]

中文:
定理 集合.Ioo_eq_singleton_iff
  结论: 开区间 a b = {c} ↔ a ⋖ c ∧ c ⋖ b where
  证明: by
    simp_rw [Set.ext_iff, mem_Ioo, mem_singleton_iff] at h
    have ⟨hac, hcb⟩ := (h c).mpr rfl
    exact ⟨⟨hac, fun d had hdc => hdc.ne ((h d).mp ⟨had, hdc.trans hcb⟩)⟩,
      ⟨hcb, fun d hcd hdb => hcd.ne ((h d).mp ⟨hac.trans hcd, hdb⟩).symm⟩⟩
  mpr := fun ⟨hac, hcb⟩ => by
    rw [← Ioc_union_Ico_eq_Ioo hac.lt hcb.lt]; rw [hac.Ioc_eq]; rw [hcb.Ico_eq]; rw [union_self]

@[to_dual]

Depends on / 依赖: Ico_eq, Ioc_eq, Ioc_union_Ico_eq_Ioo, Set.ext_iff, ext_iff, hac.Ioc_eq, hac.lt, hac.trans, hcb.Ico_eq, hcb.lt, hcd.ne, hdc.ne, hdc.trans, mem_Ioo, mem_singleton_iff, simp_rw, union_self
-/
theorem Set.Ioo_eq_singleton_iff : Ioo a b = {c} ↔ a ⋖ c ∧ c ⋖ b where
  mp h := by
    simp_rw [Set.ext_iff, mem_Ioo, mem_singleton_iff] at h
    have ⟨hac, hcb⟩ := (h c).mpr rfl
    exact ⟨⟨hac, fun d had hdc => hdc.ne ((h d).mp ⟨had, hdc.trans hcb⟩)⟩,
      ⟨hcb, fun d hcd hdb => hcd.ne ((h d).mp ⟨hac.trans hcd, hdb⟩).symm⟩⟩
  mpr := fun ⟨hac, hcb⟩ => by
    rw [← Ioc_union_Ico_eq_Ioo hac.lt hcb.lt]; rw [hac.Ioc_eq]; rw [hcb.Ico_eq]; rw [union_self]

@[to_dual]
/--
theorem `Set.Ioi_eq_singleton_iff` / 定理 `Set.Ioi_eq_singleton_iff`

English:
theorem Set.Ioi_eq_singleton_iff
  statement: Ioi a = {b} ↔ IsTop b ∧ a ⋖ b where
  proof: by
    simp_rw [Set.ext_iff, mem_Ioi, mem_singleton_iff] at h
    have hb : a < b := (h b).mpr rfl
    exact ⟨fun c => not_lt.mp fun hc => hc.ne.symm ((h c).mp (hb.trans hc)),
      ⟨hb, fun c hac hcb => hcb.ne ((h c).mp hac)⟩⟩
  mpr := fun ⟨hb, hab⟩ => by
    cases b, hb using IsTop.rec; rwa [← Ioc_top, Ioc_eq_singleton_right_iff]

@[to_dual unique_right]

中文:
定理 集合.Ioi_eq_singleton_iff
  结论: 左开右无界区间 a = {b} ↔ IsTop b ∧ a ⋖ b where
  证明: by
    simp_rw [Set.ext_iff, mem_Ioi, mem_singleton_iff] at h
    have hb : a < b := (h b).mpr rfl
    exact ⟨fun c => not_lt.mp fun hc => hc.ne.symm ((h c).mp (hb.trans hc)),
      ⟨hb, fun c hac hcb => hcb.ne ((h c).mp hac)⟩⟩
  mpr := fun ⟨hb, hab⟩ => by
    cases b, hb using IsTop.rec; rwa [← Ioc_top, Ioc_eq_singleton_right_iff]

@[to_dual unique_right]

Depends on / 依赖: Ioc_eq_singleton_right_iff, Ioc_top, IsTop.rec, Set.ext_iff, ext_iff, hb.trans, hc.ne.symm, hcb.ne, mem_Ioi, mem_singleton_iff, not_lt, not_lt.mp, simp_rw
-/
theorem Set.Ioi_eq_singleton_iff : Ioi a = {b} ↔ IsTop b ∧ a ⋖ b where
  mp h := by
    simp_rw [Set.ext_iff, mem_Ioi, mem_singleton_iff] at h
    have hb : a < b := (h b).mpr rfl
    exact ⟨fun c => not_lt.mp fun hc => hc.ne.symm ((h c).mp (hb.trans hc)),
      ⟨hb, fun c hac hcb => hcb.ne ((h c).mp hac)⟩⟩
  mpr := fun ⟨hb, hab⟩ => by
    cases b, hb using IsTop.rec; rwa [← Ioc_top, Ioc_eq_singleton_right_iff]

@[to_dual unique_right]
/--
theorem `CovBy.unique_left` / 定理 `CovBy.unique_left`

English:
theorem CovBy.unique_left
  given: (ha : a ⋖ c) (hb : b ⋖ c)
  statement: a = b
  proof: (hb.le_of_lt ha.lt).antisymm ha.le_of_lt hb.lt

中文:
定理 CovBy.unique_left
  条件: (ha : a ⋖ c) (hb : b ⋖ c)
  结论: a = b
  证明: (hb.le_of_lt ha.lt).antisymm ha.le_of_lt hb.lt

Depends on / 依赖: antisymm, ha.le_of_lt, ha.lt, hb.le_of_lt, hb.lt, le_of_lt
-/
theorem CovBy.unique_left (ha : a ⋖ c) (hb : b ⋖ c) : a = b :=
(hb.le_of_lt ha.lt).antisymm ha.le_of_lt hb.lt

/-- If `a`, `b`, `c` are consecutive and `a < x < c` then `x = b`. -/
@[to_dual self (reorder := a c, hab hbc, hax hxc)]
/--
theorem `CovBy.eq_of_between` / 定理 `CovBy.eq_of_between`

English:
theorem CovBy.eq_of_between
  given: {x : α} (hab : a ⋖ b) (hbc : b ⋖ c) (hax : a < x) (hxc : x < c)
  proof: le_antisymm (le_of_not_gt fun h => hbc.2 h hxc) (le_of_not_gt <| hab.2 hax)

@[to_dual covBy_iff_lt_iff_le_right]

中文:
定理 CovBy.eq_of_between
  条件: {x : α} (hab : a ⋖ b) (hbc : b ⋖ c) (hax : a < x) (hxc : x < c)
  证明: le_antisymm (le_of_not_gt fun h => hbc.2 h hxc) (le_of_not_gt <| hab.2 hax)

@[to_dual covBy_iff_lt_iff_le_right]

Depends on / 依赖: le_antisymm, le_of_not_gt
-/
theorem CovBy.eq_of_between {x : α} (hab : a ⋖ b) (hbc : b ⋖ c) (hax : a < x) (hxc : x < c) :
    x = b :=
  le_antisymm (le_of_not_gt fun h => hbc.2 h hxc) (le_of_not_gt <| hab.2 hax)

@[to_dual covBy_iff_lt_iff_le_right]
/--
theorem `covBy_iff_lt_iff_le_left` / 定理 `covBy_iff_lt_iff_le_left`

English:
theorem covBy_iff_lt_iff_le_left
  given: {x y : α}
  statement: x ⋖ y ↔ forall {z}, z < y ↔ z <= x where
  proof: fun hx _z => ⟨hx.le_of_lt, fun hz => hz.trans_lt hx.lt⟩
  mpr := fun H => ⟨H.2 le_rfl, fun _z hx hz => (H.1 hz).not_gt hx⟩

@[to_dual covBy_iff_le_iff_lt_right]

中文:
定理 covBy_iff_lt_iff_le_left
  条件: {x y : α}
  结论: x ⋖ y ↔ 对任意 {z}, z < y ↔ z <= x where
  证明: fun hx _z => ⟨hx.le_of_lt, fun hz => hz.trans_lt hx.lt⟩
  mpr := fun H => ⟨H.2 le_rfl, fun _z hx hz => (H.1 hz).not_gt hx⟩

@[to_dual covBy_iff_le_iff_lt_right]

Depends on / 依赖: hx.le_of_lt, hx.lt, hz.trans_lt, le_of_lt, trans_lt
-/
theorem covBy_iff_lt_iff_le_left {x y : α} : x ⋖ y ↔ forall {z}, z < y ↔ z <= x where
  mp := fun hx _z => ⟨hx.le_of_lt, fun hz => hz.trans_lt hx.lt⟩
  mpr := fun H => ⟨H.2 le_rfl, fun _z hx hz => (H.1 hz).not_gt hx⟩

@[to_dual covBy_iff_le_iff_lt_right]
/--
theorem `covBy_iff_le_iff_lt_left` / 定理 `covBy_iff_le_iff_lt_left`

English:
theorem covBy_iff_le_iff_lt_left
  given: {x y : α}
  statement: x ⋖ y ↔ forall {z}, z <= x ↔ z < y
  proof: by
  simp_rw [covBy_iff_lt_iff_le_left, iff_comm]

@[to_dual lt_iff_le_right]
alias ⟨CovBy.lt_iff_le_left, _⟩ := covBy_iff_lt_iff_le_left

@[to_dual le_iff_lt_right]
alias ⟨CovBy.le_iff_lt_left, _⟩ := covBy_iff_le_iff_lt_left

中文:
定理 covBy_iff_le_iff_lt_left
  条件: {x y : α}
  结论: x ⋖ y ↔ 对任意 {z}, z <= x ↔ z < y
  证明: by
  simp_rw [covBy_iff_lt_iff_le_left, iff_comm]

@[to_dual lt_iff_le_right]
alias ⟨CovBy.lt_iff_le_left, _⟩ := covBy_iff_lt_iff_le_left

@[to_dual le_iff_lt_right]
alias ⟨CovBy.le_iff_lt_left, _⟩ := covBy_iff_le_iff_lt_left

Depends on / 依赖: covBy_iff_lt_iff_le_left, iff_comm, simp_rw
-/
theorem covBy_iff_le_iff_lt_left {x y : α} : x ⋖ y ↔ forall {z}, z <= x ↔ z < y := by
  simp_rw [covBy_iff_lt_iff_le_left, iff_comm]

@[to_dual lt_iff_le_right]
alias ⟨CovBy.lt_iff_le_left, _⟩ := covBy_iff_lt_iff_le_left

@[to_dual le_iff_lt_right]
alias ⟨CovBy.le_iff_lt_left, _⟩ := covBy_iff_le_iff_lt_left

/-- If `a < b` then there exist `a' > a` and `b' < b` such that `Set.Iio a'` is strictly to the left
of `Set.Ioi b'`. -/
@[to_dual none]
/--
lemma `LT.lt.exists_disjoint_Iio_Ioi` / 引理 `LT.lt.exists_disjoint_Iio_Ioi`

English:
lemma LT.lt.exists_disjoint_Iio_Ioi
  given: (h : a < b)
  proof: by
  grind

中文:
引理 LT.lt.存在_disjoint_Iio_Ioi
  条件: (h : a < b)
  证明: by
  grind
-/
lemma LT.lt.exists_disjoint_Iio_Ioi (h : a < b) :
    exists a' > a, exists b' < b, forall x < a', forall y > b', x < y := by
  grind

end LinearOrder

namespace Bool

/--
theorem `wcovBy_iff` / 定理 `wcovBy_iff`

English:
theorem wcovBy_iff
  statement: forall {a b : Bool}, a ⩿ b ↔ a <= b
  proof: by unfold WCovBy; decide

中文:
定理 wcovBy_iff
  结论: 对任意 {a b : 布尔值}, a ⩿ b ↔ a <= b
  证明: by unfold WCovBy; decide
-/
@[simp] theorem wcovBy_iff : forall {a b : Bool}, a ⩿ b ↔ a <= b := by unfold WCovBy; decide
/--
theorem `covBy_iff` / 定理 `covBy_iff`

English:
theorem covBy_iff
  statement: forall {a b : Bool}, a ⋖ b ↔ a < b
  proof: by unfold CovBy; decide

中文:
定理 covBy_iff
  结论: 对任意 {a b : 布尔值}, a ⋖ b ↔ a < b
  证明: by unfold CovBy; decide
-/
@[simp] theorem covBy_iff : forall {a b : Bool}, a ⋖ b ↔ a < b := by unfold CovBy; decide

/--
Instance `instDecidableRelWCovBy` / 实例 `instDecidableRelWCovBy`

English:
instance instDecidableRelWCovBy
  signature: : DecidableRel (· ⩿ · : Bool -> Bool -> Prop)
  body: fun _ _ =>
  decidable_of_iff _ wcovBy_iff.symm

中文:
实例 instDecidableRelWCovBy
  签名: : DecidableRel (· ⩿ · : 布尔值 -> 布尔值 -> 命题)
  定义体: fun _ _ =>
  decidable_of_iff _ wcovBy_iff.symm
-/
instance instDecidableRelWCovBy : DecidableRel (· ⩿ · : Bool -> Bool -> Prop) := fun _ _ =>
  decidable_of_iff _ wcovBy_iff.symm

/--
Instance `instDecidableRelCovBy` / 实例 `instDecidableRelCovBy`

English:
instance instDecidableRelCovBy
  signature: : DecidableRel (· ⋖ · : Bool -> Bool -> Prop)
  body: fun _ _ =>
  decidable_of_iff _ covBy_iff.symm

中文:
实例 instDecidableRelCovBy
  签名: : DecidableRel (· ⋖ · : 布尔值 -> 布尔值 -> 命题)
  定义体: fun _ _ =>
  decidable_of_iff _ covBy_iff.symm
-/
instance instDecidableRelCovBy : DecidableRel (· ⋖ · : Bool -> Bool -> Prop) := fun _ _ =>
  decidable_of_iff _ covBy_iff.symm

end Bool

namespace Set
variable {s t : Set α} {a : α}

/--
lemma `wcovBy_insert` / 引理 `wcovBy_insert`

English:
lemma wcovBy_insert
  given: (x : α) (s : Set α)
  statement: s ⩿ insert x s
  proof: by
  refine wcovBy_of_eq_or_eq (subset_insert x s) fun t hst h2t => ?_
  by_cases h : x in t
  · exact Or.inr (subset_antisymm h2t <| insert_subset_iff.mpr ⟨h, hst⟩)
  · refine Or.inl (subset_antisymm ?_ hst)
    rwa [← sdiff_singleton_eq_self h, sdiff_singleton_subset_iff]

中文:
引理 wcovBy_insert
  条件: (x : α) (s : 集合 α)
  结论: s ⩿ insert x s
  证明: by
  refine wcovBy_of_eq_or_eq (subset_insert x s) fun t hst h2t => ?_
  by_cases h : x in t
  · exact Or.inr (subset_antisymm h2t <| insert_subset_iff.mpr ⟨h, hst⟩)
  · refine Or.inl (subset_antisymm ?_ hst)
    rwa [← sdiff_singleton_eq_self h, sdiff_singleton_subset_iff]
-/
@[simp] lemma wcovBy_insert (x : α) (s : Set α) : s ⩿ insert x s := by
  refine wcovBy_of_eq_or_eq (subset_insert x s) fun t hst h2t => ?_
  by_cases h : x in t
  · exact Or.inr (subset_antisymm h2t <| insert_subset_iff.mpr ⟨h, hst⟩)
  · refine Or.inl (subset_antisymm ?_ hst)
    rwa [← sdiff_singleton_eq_self h, sdiff_singleton_subset_iff]

/--
lemma `sdiff_singleton_wcovBy` / 引理 `sdiff_singleton_wcovBy`

English:
lemma sdiff_singleton_wcovBy
  given: (s : Set α) (a : α)
  statement: s \ {a} ⩿ s
  proof: by
  by_cases ha : a in s
  · convert! wcovBy_insert a _
    ext
    simp [ha]
  · simp [ha]

中文:
引理 sdiff_singleton_wcovBy
  条件: (s : 集合 α) (a : α)
  结论: s \ {a} ⩿ s
  证明: by
  by_cases ha : a in s
  · convert! wcovBy_insert a _
    ext
    simp [ha]
  · simp [ha]
-/
@[simp] lemma sdiff_singleton_wcovBy (s : Set α) (a : α) : s \ {a} ⩿ s := by
  by_cases ha : a in s
  · convert! wcovBy_insert a _
    ext
    simp [ha]
  · simp [ha]

/--
lemma `covBy_insert` / 引理 `covBy_insert`

English:
lemma covBy_insert
  given: (ha : a ∉ s)
  statement: s ⋖ insert a s
  proof: (wcovBy_insert _ _).covBy_of_lt ssubset_insert ha

中文:
引理 covBy_insert
  条件: (ha : a ∉ s)
  结论: s ⋖ insert a s
  证明: (wcovBy_insert _ _).covBy_of_lt ssubset_insert ha
-/
@[simp] lemma covBy_insert (ha : a ∉ s) : s ⋖ insert a s :=
(wcovBy_insert _ _).covBy_of_lt ssubset_insert ha

/--
lemma `empty_covBy_singleton` / 引理 `empty_covBy_singleton`

English:
lemma empty_covBy_singleton
  given: (a : α)
  statement: ∅ ⋖ ({a} : Set α)
  proof: insert_empty_eq (β := Set α) a ▸ covBy_insert notMem_empty a

中文:
引理 empty_covBy_singleton
  条件: (a : α)
  结论: ∅ ⋖ ({a} : 集合 α)
  证明: insert_empty_eq (β := Set α) a ▸ covBy_insert notMem_empty a
-/
@[simp] lemma empty_covBy_singleton (a : α) : ∅ ⋖ ({a} : Set α) :=
insert_empty_eq (β := Set α) a ▸ covBy_insert notMem_empty a

/--
lemma `sdiff_singleton_covBy` / 引理 `sdiff_singleton_covBy`

English:
lemma sdiff_singleton_covBy
  given: (ha : a in s)
  statement: s \ {a} ⋖ s
  proof: ⟨sdiff_lt (singleton_subset_iff.2 ha) singleton_ne_empty _, (sdiff_singleton_wcovBy _ _).2⟩

中文:
引理 sdiff_singleton_covBy
  条件: (ha : a in s)
  结论: s \ {a} ⋖ s
  证明: ⟨sdiff_lt (singleton_subset_iff.2 ha) singleton_ne_empty _, (sdiff_singleton_wcovBy _ _).2⟩
-/
@[simp] lemma sdiff_singleton_covBy (ha : a in s) : s \ {a} ⋖ s :=
⟨sdiff_lt (singleton_subset_iff.2 ha) singleton_ne_empty _, (sdiff_singleton_wcovBy _ _).2⟩

/--
lemma `_root_.CovBy.exists_set_insert` / 引理 `_root_.CovBy.exists_set_insert`

English:
lemma _root_.CovBy.exists_set_insert
  given: (h : s ⋖ t)
  statement: exists a ∉ s, insert a s = t
  proof: let ⟨a, ha, hst⟩ := ssubset_iff_insert.1 h.lt
  ⟨a, ha, (hst.eq_of_not_ssuperset <| h.2 <| ssubset_insert ha).symm⟩

中文:
引理 _root_.CovBy.存在_set_insert
  条件: (h : s ⋖ t)
  结论: 存在 a ∉ s, insert a s = t
  证明: let ⟨a, ha, hst⟩ := ssubset_iff_insert.1 h.lt
  ⟨a, ha, (hst.eq_of_not_ssuperset <| h.2 <| ssubset_insert ha).symm⟩

Depends on / 依赖: eq_of_not_ssuperset, h.lt, hst.eq_of_not_ssuperset, ssubset_iff_insert, ssubset_insert
-/
lemma _root_.CovBy.exists_set_insert (h : s ⋖ t) : exists a ∉ s, insert a s = t :=
  let ⟨a, ha, hst⟩ := ssubset_iff_insert.1 h.lt
  ⟨a, ha, (hst.eq_of_not_ssuperset <| h.2 <| ssubset_insert ha).symm⟩

/--
lemma `_root_.CovBy.exists_set_sdiff_singleton` / 引理 `_root_.CovBy.exists_set_sdiff_singleton`

English:
lemma _root_.CovBy.exists_set_sdiff_singleton
  given: (h : s ⋖ t)
  statement: exists a in t, t \ {a} = s
  proof: let ⟨a, ha, hst⟩ := ssubset_iff_sdiff_singleton.1 h.lt
  ⟨a, ha, (hst.eq_of_not_ssubset fun h' => h.2 h' <|
sdiff_lt (singleton_subset_iff.2 ha) singleton_ne_empty _).symm⟩

中文:
引理 _root_.CovBy.存在_set_sdiff_singleton
  条件: (h : s ⋖ t)
  结论: 存在 a in t, t \ {a} = s
  证明: let ⟨a, ha, hst⟩ := ssubset_iff_sdiff_singleton.1 h.lt
  ⟨a, ha, (hst.eq_of_not_ssubset fun h' => h.2 h' <|
sdiff_lt (singleton_subset_iff.2 ha) singleton_ne_empty _).symm⟩

Depends on / 依赖: eq_of_not_ssubset, h.lt, hst.eq_of_not_ssubset, sdiff_lt, singleton_ne_empty, singleton_subset_iff, ssubset_iff_sdiff_singleton
-/
lemma _root_.CovBy.exists_set_sdiff_singleton (h : s ⋖ t) : exists a in t, t \ {a} = s :=
  let ⟨a, ha, hst⟩ := ssubset_iff_sdiff_singleton.1 h.lt
  ⟨a, ha, (hst.eq_of_not_ssubset fun h' => h.2 h' <|
sdiff_lt (singleton_subset_iff.2 ha) singleton_ne_empty _).symm⟩

/--
lemma `covBy_iff_exists_insert` / 引理 `covBy_iff_exists_insert`

English:
lemma covBy_iff_exists_insert
  statement: s ⋖ t ↔ exists a ∉ s, insert a s = t
  proof: ⟨CovBy.exists_set_insert, by rintro ⟨a, ha, rfl⟩; exact covBy_insert ha⟩

中文:
引理 covBy_iff_存在_insert
  结论: s ⋖ t ↔ 存在 a ∉ s, insert a s = t
  证明: ⟨CovBy.exists_set_insert, by rintro ⟨a, ha, rfl⟩; exact covBy_insert ha⟩

Depends on / 依赖: CovBy.exists_set_insert, covBy_insert, exists_set_insert
-/
lemma covBy_iff_exists_insert : s ⋖ t ↔ exists a ∉ s, insert a s = t :=
  ⟨CovBy.exists_set_insert, by rintro ⟨a, ha, rfl⟩; exact covBy_insert ha⟩

/--
lemma `covBy_iff_exists_sdiff_singleton` / 引理 `covBy_iff_exists_sdiff_singleton`

English:
lemma covBy_iff_exists_sdiff_singleton
  statement: s ⋖ t ↔ exists a in t, t \ {a} = s
  proof: ⟨CovBy.exists_set_sdiff_singleton, by rintro ⟨a, ha, rfl⟩; exact sdiff_singleton_covBy ha⟩

中文:
引理 covBy_iff_存在_sdiff_singleton
  结论: s ⋖ t ↔ 存在 a in t, t \ {a} = s
  证明: ⟨CovBy.exists_set_sdiff_singleton, by rintro ⟨a, ha, rfl⟩; exact sdiff_singleton_covBy ha⟩

Depends on / 依赖: CovBy.exists_set_sdiff_singleton, exists_set_sdiff_singleton, sdiff_singleton_covBy
-/
lemma covBy_iff_exists_sdiff_singleton : s ⋖ t ↔ exists a in t, t \ {a} = s :=
  ⟨CovBy.exists_set_sdiff_singleton, by rintro ⟨a, ha, rfl⟩; exact sdiff_singleton_covBy ha⟩

end Set

section Relation

open Relation

/--
lemma `wcovBy_eq_reflGen_covBy` / 引理 `wcovBy_eq_reflGen_covBy`

English:
lemma wcovBy_eq_reflGen_covBy
  given: [PartialOrder α]
  statement: (· ⩿ · : α -> α -> Prop) = ReflGen (· ⋖ ·)
  proof: by
  ext x y; simp_rw [wcovBy_iff_eq_or_covBy, @eq_comm _ x, reflGen_iff]

中文:
引理 wcovBy_eq_reflGen_covBy
  条件: [偏序 α]
  结论: (· ⩿ · : α -> α -> 命题) = ReflGen (· ⋖ ·)
  证明: by
  ext x y; simp_rw [wcovBy_iff_eq_or_covBy, @eq_comm _ x, reflGen_iff]

Depends on / 依赖: eq_comm, reflGen_iff, simp_rw, wcovBy_iff_eq_or_covBy
-/
lemma wcovBy_eq_reflGen_covBy [PartialOrder α] : (· ⩿ · : α -> α -> Prop) = ReflGen (· ⋖ ·) := by
  ext x y; simp_rw [wcovBy_iff_eq_or_covBy, @eq_comm _ x, reflGen_iff]

/--
lemma `transGen_wcovBy_eq_reflTransGen_covBy` / 引理 `transGen_wcovBy_eq_reflTransGen_covBy`

English:
lemma transGen_wcovBy_eq_reflTransGen_covBy
  given: [PartialOrder α]
  proof: by
  rw [wcovBy_eq_reflGen_covBy]; rw [transGen_reflGen]

中文:
引理 transGen_wcovBy_eq_reflTransGen_covBy
  条件: [偏序 α]
  证明: by
  rw [wcovBy_eq_reflGen_covBy]; rw [transGen_reflGen]

Depends on / 依赖: transGen_reflGen, wcovBy_eq_reflGen_covBy
-/
lemma transGen_wcovBy_eq_reflTransGen_covBy [PartialOrder α] :
    TransGen (· ⩿ · : α -> α -> Prop) = ReflTransGen (· ⋖ ·) := by
  rw [wcovBy_eq_reflGen_covBy]; rw [transGen_reflGen]

/--
lemma `reflTransGen_wcovBy_eq_reflTransGen_covBy` / 引理 `reflTransGen_wcovBy_eq_reflTransGen_covBy`

English:
lemma reflTransGen_wcovBy_eq_reflTransGen_covBy
  given: [PartialOrder α]
  proof: by
  rw [wcovBy_eq_reflGen_covBy]; rw [reflTransGen_reflGen]

中文:
引理 reflTransGen_wcovBy_eq_reflTransGen_covBy
  条件: [偏序 α]
  证明: by
  rw [wcovBy_eq_reflGen_covBy]; rw [reflTransGen_reflGen]

Depends on / 依赖: reflTransGen_reflGen, wcovBy_eq_reflGen_covBy
-/
lemma reflTransGen_wcovBy_eq_reflTransGen_covBy [PartialOrder α] :
    ReflTransGen (· ⩿ · : α -> α -> Prop) = ReflTransGen (· ⋖ ·) := by
  rw [wcovBy_eq_reflGen_covBy]; rw [reflTransGen_reflGen]

end Relation

namespace Prod

variable [PartialOrder α] [PartialOrder β] {a a₁ a₂ : α} {b b₁ b₂ : β} {x y : α × β}

@[to_dual self, simp]
/--
theorem `swap_wcovBy_swap` / 定理 `swap_wcovBy_swap`

English:
theorem swap_wcovBy_swap
  statement: x.swap ⩿ y.swap ↔ x ⩿ y
  proof: apply_wcovBy_apply_iff (OrderIso.prodComm : α × β ≃o β × α)

@[to_dual self, simp]

中文:
定理 swap_wcovBy_swap
  结论: x.swap ⩿ y.swap ↔ x ⩿ y
  证明: apply_wcovBy_apply_iff (OrderIso.prodComm : α × β ≃o β × α)

@[to_dual self, simp]

Depends on / 依赖: OrderIso, OrderIso.prodComm, apply_wcovBy_apply_iff, prodComm
-/
theorem swap_wcovBy_swap : x.swap ⩿ y.swap ↔ x ⩿ y :=
  apply_wcovBy_apply_iff (OrderIso.prodComm : α × β ≃o β × α)

@[to_dual self, simp]
/--
theorem `swap_covBy_swap` / 定理 `swap_covBy_swap`

English:
theorem swap_covBy_swap
  statement: x.swap ⋖ y.swap ↔ x ⋖ y
  proof: apply_covBy_apply_iff (OrderIso.prodComm : α × β ≃o β × α)

@[to_dual none]

中文:
定理 swap_covBy_swap
  结论: x.swap ⋖ y.swap ↔ x ⋖ y
  证明: apply_covBy_apply_iff (OrderIso.prodComm : α × β ≃o β × α)

@[to_dual none]

Depends on / 依赖: OrderIso, OrderIso.prodComm, apply_covBy_apply_iff, prodComm
-/
theorem swap_covBy_swap : x.swap ⋖ y.swap ↔ x ⋖ y :=
  apply_covBy_apply_iff (OrderIso.prodComm : α × β ≃o β × α)

@[to_dual none]
/--
theorem `fst_eq_or_snd_eq_of_wcovBy` / 定理 `fst_eq_or_snd_eq_of_wcovBy`

English:
theorem fst_eq_or_snd_eq_of_wcovBy
  statement: x ⩿ y -> x.1 = y.1 ∨ x.2 = y.2
  proof: by
  intro h
  by_contra! ⟨ha, hb⟩
  exact
    h.2 (mk_lt_mk.2 <| Or.inl ⟨ha.lt_of_le h.1.1, le_rfl⟩)
      (mk_lt_mk.2 <| Or.inr ⟨le_rfl, hb.lt_of_le h.1.2⟩)

@[to_dual self]

中文:
定理 fst_eq_or_snd_eq_of_wcovBy
  结论: x ⩿ y -> x.1 = y.1 ∨ x.2 = y.2
  证明: by
  intro h
  by_contra! ⟨ha, hb⟩
  exact
    h.2 (mk_lt_mk.2 <| Or.inl ⟨ha.lt_of_le h.1.1, le_rfl⟩)
      (mk_lt_mk.2 <| Or.inr ⟨le_rfl, hb.lt_of_le h.1.2⟩)

@[to_dual self]

Depends on / 依赖: Or.inl, Or.inr, ha.lt_of_le, hb.lt_of_le, le_rfl, lt_of_le, mk_lt_mk
-/
theorem fst_eq_or_snd_eq_of_wcovBy : x ⩿ y -> x.1 = y.1 ∨ x.2 = y.2 := by
  intro h
  by_contra! ⟨ha, hb⟩
  exact
    h.2 (mk_lt_mk.2 <| Or.inl ⟨ha.lt_of_le h.1.1, le_rfl⟩)
      (mk_lt_mk.2 <| Or.inr ⟨le_rfl, hb.lt_of_le h.1.2⟩)

@[to_dual self]
/--
theorem `_root_.WCovBy.fst` / 定理 `_root_.WCovBy.fst`

English:
theorem _root_.WCovBy.fst
  given: (h : x ⩿ y)
  statement: x.1 ⩿ y.1
  proof: ⟨h.1.1, fun _ h₁ h₂ => h.2 (mk_lt_mk_iff_left.2 h₁) ⟨⟨h₂.le, h.1.2⟩, fun hc => h₂.not_ge hc.1⟩⟩

@[to_dual self]

中文:
定理 _root_.WCovBy.fst
  条件: (h : x ⩿ y)
  结论: x.1 ⩿ y.1
  证明: ⟨h.1.1, fun _ h₁ h₂ => h.2 (mk_lt_mk_iff_left.2 h₁) ⟨⟨h₂.le, h.1.2⟩, fun hc => h₂.not_ge hc.1⟩⟩

@[to_dual self]

Depends on / 依赖: mk_lt_mk_iff_left, not_ge
-/
theorem _root_.WCovBy.fst (h : x ⩿ y) : x.1 ⩿ y.1 :=
  ⟨h.1.1, fun _ h₁ h₂ => h.2 (mk_lt_mk_iff_left.2 h₁) ⟨⟨h₂.le, h.1.2⟩, fun hc => h₂.not_ge hc.1⟩⟩

@[to_dual self]
/--
theorem `_root_.WCovBy.snd` / 定理 `_root_.WCovBy.snd`

English:
theorem _root_.WCovBy.snd
  given: (h : x ⩿ y)
  statement: x.2 ⩿ y.2
  proof: ⟨h.1.2, fun _ h₁ h₂ => h.2 (mk_lt_mk_iff_right.2 h₁) ⟨⟨h.1.1, h₂.le⟩, fun hc => h₂.not_ge hc.2⟩⟩

@[to_dual self]

中文:
定理 _root_.WCovBy.snd
  条件: (h : x ⩿ y)
  结论: x.2 ⩿ y.2
  证明: ⟨h.1.2, fun _ h₁ h₂ => h.2 (mk_lt_mk_iff_right.2 h₁) ⟨⟨h.1.1, h₂.le⟩, fun hc => h₂.not_ge hc.2⟩⟩

@[to_dual self]

Depends on / 依赖: mk_lt_mk_iff_right, not_ge
-/
theorem _root_.WCovBy.snd (h : x ⩿ y) : x.2 ⩿ y.2 :=
  ⟨h.1.2, fun _ h₁ h₂ => h.2 (mk_lt_mk_iff_right.2 h₁) ⟨⟨h.1.1, h₂.le⟩, fun hc => h₂.not_ge hc.2⟩⟩

@[to_dual self]
/--
theorem `mk_wcovBy_mk_iff_left` / 定理 `mk_wcovBy_mk_iff_left`

English:
theorem mk_wcovBy_mk_iff_left
  statement: (a₁, b) ⩿ (a₂, b) ↔ a₁ ⩿ a₂
  proof: by
  refine ⟨WCovBy.fst, (And.imp mk_le_mk_iff_left.2) fun h c h₁ h₂ => ?_⟩
  have : c.2 = b := h₂.le.2.antisymm h₁.le.2
  rw [← @Prod.mk.eta _ _ c]; rw [this]; rw [mk_lt_mk_iff_left] at h₁ h₂
  exact h h₁ h₂

@[to_dual self]

中文:
定理 mk_wcovBy_mk_iff_left
  结论: (a₁, b) ⩿ (a₂, b) ↔ a₁ ⩿ a₂
  证明: by
  refine ⟨WCovBy.fst, (And.imp mk_le_mk_iff_left.2) fun h c h₁ h₂ => ?_⟩
  have : c.2 = b := h₂.le.2.antisymm h₁.le.2
  rw [← @Prod.mk.eta _ _ c]; rw [this]; rw [mk_lt_mk_iff_left] at h₁ h₂
  exact h h₁ h₂

@[to_dual self]

Depends on / 依赖: And.imp, Prod.mk.eta, WCovBy, WCovBy.fst, antisymm, mk_le_mk_iff_left, mk_lt_mk_iff_left
-/
theorem mk_wcovBy_mk_iff_left : (a₁, b) ⩿ (a₂, b) ↔ a₁ ⩿ a₂ := by
  refine ⟨WCovBy.fst, (And.imp mk_le_mk_iff_left.2) fun h c h₁ h₂ => ?_⟩
  have : c.2 = b := h₂.le.2.antisymm h₁.le.2
  rw [← @Prod.mk.eta _ _ c]; rw [this]; rw [mk_lt_mk_iff_left] at h₁ h₂
  exact h h₁ h₂

@[to_dual self]
/--
theorem `mk_wcovBy_mk_iff_right` / 定理 `mk_wcovBy_mk_iff_right`

English:
theorem mk_wcovBy_mk_iff_right
  statement: (a, b₁) ⩿ (a, b₂) ↔ b₁ ⩿ b₂
  proof: swap_wcovBy_swap.trans mk_wcovBy_mk_iff_left

@[to_dual self]

中文:
定理 mk_wcovBy_mk_iff_right
  结论: (a, b₁) ⩿ (a, b₂) ↔ b₁ ⩿ b₂
  证明: swap_wcovBy_swap.trans mk_wcovBy_mk_iff_left

@[to_dual self]

Depends on / 依赖: mk_wcovBy_mk_iff_left, swap_wcovBy_swap, swap_wcovBy_swap.trans
-/
theorem mk_wcovBy_mk_iff_right : (a, b₁) ⩿ (a, b₂) ↔ b₁ ⩿ b₂ :=
  swap_wcovBy_swap.trans mk_wcovBy_mk_iff_left

@[to_dual self]
/--
theorem `mk_covBy_mk_iff_left` / 定理 `mk_covBy_mk_iff_left`

English:
theorem mk_covBy_mk_iff_left
  statement: (a₁, b) ⋖ (a₂, b) ↔ a₁ ⋖ a₂
  proof: by
  simp_rw [covBy_iff_wcovBy_and_lt, mk_wcovBy_mk_iff_left, mk_lt_mk_iff_left]

@[to_dual self]

中文:
定理 mk_covBy_mk_iff_left
  结论: (a₁, b) ⋖ (a₂, b) ↔ a₁ ⋖ a₂
  证明: by
  simp_rw [covBy_iff_wcovBy_and_lt, mk_wcovBy_mk_iff_left, mk_lt_mk_iff_left]

@[to_dual self]

Depends on / 依赖: covBy_iff_wcovBy_and_lt, mk_lt_mk_iff_left, mk_wcovBy_mk_iff_left, simp_rw
-/
theorem mk_covBy_mk_iff_left : (a₁, b) ⋖ (a₂, b) ↔ a₁ ⋖ a₂ := by
  simp_rw [covBy_iff_wcovBy_and_lt, mk_wcovBy_mk_iff_left, mk_lt_mk_iff_left]

@[to_dual self]
/--
theorem `mk_covBy_mk_iff_right` / 定理 `mk_covBy_mk_iff_right`

English:
theorem mk_covBy_mk_iff_right
  statement: (a, b₁) ⋖ (a, b₂) ↔ b₁ ⋖ b₂
  proof: by
  simp_rw [covBy_iff_wcovBy_and_lt, mk_wcovBy_mk_iff_right, mk_lt_mk_iff_right]

@[to_dual none]

中文:
定理 mk_covBy_mk_iff_right
  结论: (a, b₁) ⋖ (a, b₂) ↔ b₁ ⋖ b₂
  证明: by
  simp_rw [covBy_iff_wcovBy_and_lt, mk_wcovBy_mk_iff_right, mk_lt_mk_iff_right]

@[to_dual none]

Depends on / 依赖: covBy_iff_wcovBy_and_lt, mk_lt_mk_iff_right, mk_wcovBy_mk_iff_right, simp_rw
-/
theorem mk_covBy_mk_iff_right : (a, b₁) ⋖ (a, b₂) ↔ b₁ ⋖ b₂ := by
  simp_rw [covBy_iff_wcovBy_and_lt, mk_wcovBy_mk_iff_right, mk_lt_mk_iff_right]

@[to_dual none]
/--
theorem `mk_wcovBy_mk_iff` / 定理 `mk_wcovBy_mk_iff`

English:
theorem mk_wcovBy_mk_iff
  statement: (a₁, b₁) ⩿ (a₂, b₂) ↔ a₁ ⩿ a₂ ∧ b₁ = b₂ ∨ b₁ ⩿ b₂ ∧ a₁ = a₂
  proof: by
  refine ⟨fun h => ?_, ?_⟩
  · obtain rfl | rfl : a₁ = a₂ ∨ b₁ = b₂ := fst_eq_or_snd_eq_of_wcovBy h
    · exact Or.inr ⟨mk_wcovBy_mk_iff_right.1 h, rfl⟩
    · exact Or.inl ⟨mk_wcovBy_mk_iff_left.1 h, rfl⟩
  · rintro (⟨h, rfl⟩ | ⟨h, rfl⟩)
    · exact mk_wcovBy_mk_iff_left.2 h
    · exact mk_wcovBy_mk_iff_right.2 h

@[to_dual none]

中文:
定理 mk_wcovBy_mk_iff
  结论: (a₁, b₁) ⩿ (a₂, b₂) ↔ a₁ ⩿ a₂ ∧ b₁ = b₂ ∨ b₁ ⩿ b₂ ∧ a₁ = a₂
  证明: by
  refine ⟨fun h => ?_, ?_⟩
  · obtain rfl | rfl : a₁ = a₂ ∨ b₁ = b₂ := fst_eq_or_snd_eq_of_wcovBy h
    · exact Or.inr ⟨mk_wcovBy_mk_iff_right.1 h, rfl⟩
    · exact Or.inl ⟨mk_wcovBy_mk_iff_left.1 h, rfl⟩
  · rintro (⟨h, rfl⟩ | ⟨h, rfl⟩)
    · exact mk_wcovBy_mk_iff_left.2 h
    · exact mk_wcovBy_mk_iff_right.2 h

@[to_dual none]

Depends on / 依赖: Or.inl, Or.inr, fst_eq_or_snd_eq_of_wcovBy, mk_wcovBy_mk_iff_left, mk_wcovBy_mk_iff_right
-/
theorem mk_wcovBy_mk_iff : (a₁, b₁) ⩿ (a₂, b₂) ↔ a₁ ⩿ a₂ ∧ b₁ = b₂ ∨ b₁ ⩿ b₂ ∧ a₁ = a₂ := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain rfl | rfl : a₁ = a₂ ∨ b₁ = b₂ := fst_eq_or_snd_eq_of_wcovBy h
    · exact Or.inr ⟨mk_wcovBy_mk_iff_right.1 h, rfl⟩
    · exact Or.inl ⟨mk_wcovBy_mk_iff_left.1 h, rfl⟩
  · rintro (⟨h, rfl⟩ | ⟨h, rfl⟩)
    · exact mk_wcovBy_mk_iff_left.2 h
    · exact mk_wcovBy_mk_iff_right.2 h

@[to_dual none]
/--
theorem `mk_covBy_mk_iff` / 定理 `mk_covBy_mk_iff`

English:
theorem mk_covBy_mk_iff
  statement: (a₁, b₁) ⋖ (a₂, b₂) ↔ a₁ ⋖ a₂ ∧ b₁ = b₂ ∨ b₁ ⋖ b₂ ∧ a₁ = a₂
  proof: by
  refine ⟨fun h => ?_, ?_⟩
  · obtain rfl | rfl : a₁ = a₂ ∨ b₁ = b₂ := fst_eq_or_snd_eq_of_wcovBy h.wcovBy
    · exact Or.inr ⟨mk_covBy_mk_iff_right.1 h, rfl⟩
    · exact Or.inl ⟨mk_covBy_mk_iff_left.1 h, rfl⟩
  · rintro (⟨h, rfl⟩ | ⟨h, rfl⟩)
    · exact mk_covBy_mk_iff_left.2 h
    · exact mk_covBy_mk_iff_right.2 h

@[to_dual none]

中文:
定理 mk_covBy_mk_iff
  结论: (a₁, b₁) ⋖ (a₂, b₂) ↔ a₁ ⋖ a₂ ∧ b₁ = b₂ ∨ b₁ ⋖ b₂ ∧ a₁ = a₂
  证明: by
  refine ⟨fun h => ?_, ?_⟩
  · obtain rfl | rfl : a₁ = a₂ ∨ b₁ = b₂ := fst_eq_or_snd_eq_of_wcovBy h.wcovBy
    · exact Or.inr ⟨mk_covBy_mk_iff_right.1 h, rfl⟩
    · exact Or.inl ⟨mk_covBy_mk_iff_left.1 h, rfl⟩
  · rintro (⟨h, rfl⟩ | ⟨h, rfl⟩)
    · exact mk_covBy_mk_iff_left.2 h
    · exact mk_covBy_mk_iff_right.2 h

@[to_dual none]

Depends on / 依赖: Or.inl, Or.inr, fst_eq_or_snd_eq_of_wcovBy, h.wcovBy, mk_covBy_mk_iff_left, mk_covBy_mk_iff_right, wcovBy
-/
theorem mk_covBy_mk_iff : (a₁, b₁) ⋖ (a₂, b₂) ↔ a₁ ⋖ a₂ ∧ b₁ = b₂ ∨ b₁ ⋖ b₂ ∧ a₁ = a₂ := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain rfl | rfl : a₁ = a₂ ∨ b₁ = b₂ := fst_eq_or_snd_eq_of_wcovBy h.wcovBy
    · exact Or.inr ⟨mk_covBy_mk_iff_right.1 h, rfl⟩
    · exact Or.inl ⟨mk_covBy_mk_iff_left.1 h, rfl⟩
  · rintro (⟨h, rfl⟩ | ⟨h, rfl⟩)
    · exact mk_covBy_mk_iff_left.2 h
    · exact mk_covBy_mk_iff_right.2 h

@[to_dual none]
/--
theorem `wcovBy_iff` / 定理 `wcovBy_iff`

English:
theorem wcovBy_iff
  statement: x ⩿ y ↔ x.1 ⩿ y.1 ∧ x.2 = y.2 ∨ x.2 ⩿ y.2 ∧ x.1 = y.1
  proof: by
  cases x
  cases y
  exact mk_wcovBy_mk_iff

@[to_dual none]

中文:
定理 wcovBy_iff
  结论: x ⩿ y ↔ x.1 ⩿ y.1 ∧ x.2 = y.2 ∨ x.2 ⩿ y.2 ∧ x.1 = y.1
  证明: by
  cases x
  cases y
  exact mk_wcovBy_mk_iff

@[to_dual none]

Depends on / 依赖: mk_wcovBy_mk_iff
-/
theorem wcovBy_iff : x ⩿ y ↔ x.1 ⩿ y.1 ∧ x.2 = y.2 ∨ x.2 ⩿ y.2 ∧ x.1 = y.1 := by
  cases x
  cases y
  exact mk_wcovBy_mk_iff

@[to_dual none]
/--
theorem `covBy_iff` / 定理 `covBy_iff`

English:
theorem covBy_iff
  statement: x ⋖ y ↔ x.1 ⋖ y.1 ∧ x.2 = y.2 ∨ x.2 ⋖ y.2 ∧ x.1 = y.1
  proof: by
  cases x
  cases y
  exact mk_covBy_mk_iff

中文:
定理 covBy_iff
  结论: x ⋖ y ↔ x.1 ⋖ y.1 ∧ x.2 = y.2 ∨ x.2 ⋖ y.2 ∧ x.1 = y.1
  证明: by
  cases x
  cases y
  exact mk_covBy_mk_iff

Depends on / 依赖: mk_covBy_mk_iff
-/
theorem covBy_iff : x ⋖ y ↔ x.1 ⋖ y.1 ∧ x.2 = y.2 ∨ x.2 ⋖ y.2 ∧ x.1 = y.1 := by
  cases x
  cases y
  exact mk_covBy_mk_iff

end Prod

namespace Pi

section Preorder

variable {ι : Type*} {α : ι -> Type*} [forall i, Preorder (α i)] {a b : (i : ι) -> α i}

@[to_dual self]
/--
lemma `_root_.WCovBy.eval` / 引理 `_root_.WCovBy.eval`

English:
lemma _root_.WCovBy.eval
  given: (h : a ⩿ b) (i : ι)
  statement: a i ⩿ b i
  proof: by
  classical
  refine ⟨h.1 i, fun ci h₁ h₂ => ?_⟩
  have hcb : Function.update a i ci <= b := by simpa [update_le_iff, h₂.le] using fun j hj => h.1 j
  refine h.2 (by simpa) (lt_of_le_not_ge hcb ?_)
  simp [le_update_iff, h₂.not_ge]

中文:
引理 _root_.WCovBy.eval
  条件: (h : a ⩿ b) (i : ι)
  结论: a i ⩿ b i
  证明: by
  classical
  refine ⟨h.1 i, fun ci h₁ h₂ => ?_⟩
  have hcb : Function.update a i ci <= b := by simpa [update_le_iff, h₂.le] using fun j hj => h.1 j
  refine h.2 (by simpa) (lt_of_le_not_ge hcb ?_)
  simp [le_update_iff, h₂.not_ge]

Depends on / 依赖: Function, Function.update, classical, le_update_iff, lt_of_le_not_ge, not_ge, update, update_le_iff
-/
lemma _root_.WCovBy.eval (h : a ⩿ b) (i : ι) : a i ⩿ b i := by
  classical
  refine ⟨h.1 i, fun ci h₁ h₂ => ?_⟩
  have hcb : Function.update a i ci <= b := by simpa [update_le_iff, h₂.le] using fun j hj => h.1 j
  refine h.2 (by simpa) (lt_of_le_not_ge hcb ?_)
  simp [le_update_iff, h₂.not_ge]

/--
lemma `exists_forall_antisymmRel_of_covBy` / 引理 `exists_forall_antisymmRel_of_covBy`

English:
lemma exists_forall_antisymmRel_of_covBy
  given: (h : a ⋖ b)
  proof: by
  classical
  simp only [CovBy, Pi.lt_def, not_and, and_imp, forall_exists_index, not_exists] at h
  obtain ⟨⟨hab, ⟨i, hi⟩⟩, h⟩ := h
  refine ⟨i, fun j hj => ?_⟩
  let c : (i : ι) -> α i := Function.update a i (b i)
  have h₁ : c <= b := by simpa [update_le_iff, c] using fun k hk => hab k
  have h₂ : ¬ c j < b j := h (by simp [c, hi.le]) i (by simpa [c]) h₁ j
  exact ⟨hab j, by simpa [lt_iff_le_not_ge, hab j, c, hj] using h₂⟩

中文:
引理 存在_对任意_antisymmRel_of_covBy
  条件: (h : a ⋖ b)
  证明: by
  classical
  simp only [CovBy, Pi.lt_def, not_and, and_imp, forall_exists_index, not_exists] at h
  obtain ⟨⟨hab, ⟨i, hi⟩⟩, h⟩ := h
  refine ⟨i, fun j hj => ?_⟩
  let c : (i : ι) -> α i := Function.update a i (b i)
  have h₁ : c <= b := by simpa [update_le_iff, c] using fun k hk => hab k
  have h₂ : ¬ c j < b j := h (by simp [c, hi.le]) i (by simpa [c]) h₁ j
  exact ⟨hab j, by simpa [lt_iff_le_not_ge, hab j, c, hj] using h₂⟩

Depends on / 依赖: Function, Function.update, Pi.lt_def, and_imp, classical, forall_exists_index, hi.le, lt_def, lt_iff_le_not_ge, not_and, not_exists, update, update_le_iff
-/
lemma exists_forall_antisymmRel_of_covBy (h : a ⋖ b) :
    exists i, forall j != i, AntisymmRel (· <= ·) (a j) (b j) := by
  classical
  simp only [CovBy, Pi.lt_def, not_and, and_imp, forall_exists_index, not_exists] at h
  obtain ⟨⟨hab, ⟨i, hi⟩⟩, h⟩ := h
  refine ⟨i, fun j hj => ?_⟩
  let c : (i : ι) -> α i := Function.update a i (b i)
  have h₁ : c <= b := by simpa [update_le_iff, c] using fun k hk => hab k
  have h₂ : ¬ c j < b j := h (by simp [c, hi.le]) i (by simpa [c]) h₁ j
  exact ⟨hab j, by simpa [lt_iff_le_not_ge, hab j, c, hj] using h₂⟩

/--
lemma `exists_forall_antisymmRel_of_wcovBy` / 引理 `exists_forall_antisymmRel_of_wcovBy`

English:
lemma exists_forall_antisymmRel_of_wcovBy
  given: [Nonempty ι] (h : a ⩿ b)
  proof: by
  rw [wcovBy_iff_covBy_or_le_and_le] at h
  obtain h | h := h
  · exact exists_forall_antisymmRel_of_covBy h
  · inhabit ι
    exact ⟨default, fun j hj => ⟨h.left j, h.right j⟩⟩

中文:
引理 存在_对任意_antisymmRel_of_wcovBy
  条件: [非空 ι] (h : a ⩿ b)
  证明: by
  rw [wcovBy_iff_covBy_or_le_and_le] at h
  obtain h | h := h
  · exact exists_forall_antisymmRel_of_covBy h
  · inhabit ι
    exact ⟨default, fun j hj => ⟨h.left j, h.right j⟩⟩

Depends on / 依赖: exists_forall_antisymmRel_of_covBy, h.left, h.right, inhabit, wcovBy_iff_covBy_or_le_and_le
-/
lemma exists_forall_antisymmRel_of_wcovBy [Nonempty ι] (h : a ⩿ b) :
    exists i, forall j != i, AntisymmRel (· <= ·) (a j) (b j) := by
  rw [wcovBy_iff_covBy_or_le_and_le] at h
  obtain h | h := h
  · exact exists_forall_antisymmRel_of_covBy h
  · inhabit ι
    exact ⟨default, fun j hj => ⟨h.left j, h.right j⟩⟩

/--
lemma `wcovBy_iff_antisymmRel` / 引理 `wcovBy_iff_antisymmRel`

English:
lemma wcovBy_iff_antisymmRel
  given: [Nonempty ι]
  proof: by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := exists_forall_antisymmRel_of_wcovBy h
    exact ⟨i, h.eval _, hi⟩
  rintro ⟨i, hab, h⟩
  refine ⟨fun j => (eq_or_ne j i).elim (· ▸ hab.1) (h j · |>.1), fun c hac hcb => ?_⟩
  have haci : a i < c i := by
    obtain ⟨hac, j, hj⟩ := Pi.lt_def.1 hac
    exact (eq_or_ne j i).elim (· ▸ hj) fun hj' =>
      ((lt_of_antisymmRel_of_lt (h j hj').symm hj).not_ge (hcb.le j)).elim
  have hcbi : c i < b i := by
    obtain ⟨hcb, j, hj⟩ := Pi.lt_def.1 hcb
    exact (eq_or_ne j i).elim (· ▸ hj) fun hj' =>
      ((lt_of_lt_of_antisymmRel hj (h j hj').symm).not_ge (hac.le j)).elim
  exact hab.2 haci hcbi

中文:
引理 wcovBy_iff_antisymmRel
  条件: [非空 ι]
  证明: by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := exists_forall_antisymmRel_of_wcovBy h
    exact ⟨i, h.eval _, hi⟩
  rintro ⟨i, hab, h⟩
  refine ⟨fun j => (eq_or_ne j i).elim (· ▸ hab.1) (h j · |>.1), fun c hac hcb => ?_⟩
  have haci : a i < c i := by
    obtain ⟨hac, j, hj⟩ := Pi.lt_def.1 hac
    exact (eq_or_ne j i).elim (· ▸ hj) fun hj' =>
      ((lt_of_antisymmRel_of_lt (h j hj').symm hj).not_ge (hcb.le j)).elim
  have hcbi : c i < b i := by
    obtain ⟨hcb, j, hj⟩ := Pi.lt_def.1 hcb
    exact (eq_or_ne j i).elim (· ▸ hj) fun hj' =>
      ((lt_of_lt_of_antisymmRel hj (h j hj').symm).not_ge (hac.le j)).elim
  exact hab.2 haci hcbi

Depends on / 依赖: Pi.lt_def, eq_or_ne, exists_forall_antisymmRel_of_wcovBy, h.eval, hcb.le, lt_def, lt_of_antisymmRel_of_lt, not_ge
-/
lemma wcovBy_iff_antisymmRel [Nonempty ι] :
    a ⩿ b ↔ exists i, a i ⩿ b i ∧ forall j != i, AntisymmRel (· <= ·) (a j) (b j) := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := exists_forall_antisymmRel_of_wcovBy h
    exact ⟨i, h.eval _, hi⟩
  rintro ⟨i, hab, h⟩
  refine ⟨fun j => (eq_or_ne j i).elim (· ▸ hab.1) (h j · |>.1), fun c hac hcb => ?_⟩
  have haci : a i < c i := by
    obtain ⟨hac, j, hj⟩ := Pi.lt_def.1 hac
    exact (eq_or_ne j i).elim (· ▸ hj) fun hj' =>
      ((lt_of_antisymmRel_of_lt (h j hj').symm hj).not_ge (hcb.le j)).elim
  have hcbi : c i < b i := by
    obtain ⟨hcb, j, hj⟩ := Pi.lt_def.1 hcb
    exact (eq_or_ne j i).elim (· ▸ hj) fun hj' =>
      ((lt_of_lt_of_antisymmRel hj (h j hj').symm).not_ge (hac.le j)).elim
  exact hab.2 haci hcbi

/--
lemma `covBy_iff_antisymmRel` / 引理 `covBy_iff_antisymmRel`

English:
lemma covBy_iff_antisymmRel
  proof: by
  constructor
  · intro h
    obtain ⟨j, hj⟩ := (Pi.lt_def.1 h.1).2
    have : Nonempty ι := ⟨j⟩
    obtain ⟨i, hi⟩ := exists_forall_antisymmRel_of_wcovBy h.wcovBy
    obtain rfl : i = j := by_contra fun this => (hi j (Ne.symm this)).2.not_gt hj
    exact ⟨i, covBy_iff_wcovBy_and_lt.2 ⟨h.wcovBy.eval i, hj⟩, hi⟩
  rintro ⟨i, hi, h⟩
  have : Nonempty ι := ⟨i⟩
  refine covBy_iff_wcovBy_and_lt.2 ⟨wcovBy_iff_antisymmRel.2 ⟨i, hi.wcovBy, h⟩, ?_⟩
  exact Pi.lt_def.2 ⟨fun j => (eq_or_ne j i).elim (· ▸ hi.1.le) (h j · |>.1), i, hi.1⟩

中文:
引理 covBy_iff_antisymmRel
  证明: by
  constructor
  · intro h
    obtain ⟨j, hj⟩ := (Pi.lt_def.1 h.1).2
    have : Nonempty ι := ⟨j⟩
    obtain ⟨i, hi⟩ := exists_forall_antisymmRel_of_wcovBy h.wcovBy
    obtain rfl : i = j := by_contra fun this => (hi j (Ne.symm this)).2.not_gt hj
    exact ⟨i, covBy_iff_wcovBy_and_lt.2 ⟨h.wcovBy.eval i, hj⟩, hi⟩
  rintro ⟨i, hi, h⟩
  have : Nonempty ι := ⟨i⟩
  refine covBy_iff_wcovBy_and_lt.2 ⟨wcovBy_iff_antisymmRel.2 ⟨i, hi.wcovBy, h⟩, ?_⟩
  exact Pi.lt_def.2 ⟨fun j => (eq_or_ne j i).elim (· ▸ hi.1.le) (h j · |>.1), i, hi.1⟩

Depends on / 依赖: Ne.symm, Nonempty, Pi.lt_def, covBy_iff_wcovBy_and_lt, eq_or_ne, exists_forall_antisymmRel_of_wcovBy, h.wcovBy, h.wcovBy.eval, hi.wcovBy, lt_def, not_gt, wcovBy, wcovBy_iff_antisymmRel
-/
lemma covBy_iff_antisymmRel :
    a ⋖ b ↔ exists i, a i ⋖ b i ∧ forall j != i, AntisymmRel (· <= ·) (a j) (b j) := by
  constructor
  · intro h
    obtain ⟨j, hj⟩ := (Pi.lt_def.1 h.1).2
    have : Nonempty ι := ⟨j⟩
    obtain ⟨i, hi⟩ := exists_forall_antisymmRel_of_wcovBy h.wcovBy
    obtain rfl : i = j := by_contra fun this => (hi j (Ne.symm this)).2.not_gt hj
    exact ⟨i, covBy_iff_wcovBy_and_lt.2 ⟨h.wcovBy.eval i, hj⟩, hi⟩
  rintro ⟨i, hi, h⟩
  have : Nonempty ι := ⟨i⟩
  refine covBy_iff_wcovBy_and_lt.2 ⟨wcovBy_iff_antisymmRel.2 ⟨i, hi.wcovBy, h⟩, ?_⟩
  exact Pi.lt_def.2 ⟨fun j => (eq_or_ne j i).elim (· ▸ hi.1.le) (h j · |>.1), i, hi.1⟩

end Preorder

section PartialOrder

variable {ι : Type*} {α : ι -> Type*} [forall i, PartialOrder (α i)] {a b : (i : ι) -> α i}

/--
lemma `exists_forall_eq_of_covBy` / 引理 `exists_forall_eq_of_covBy`

English:
lemma exists_forall_eq_of_covBy
  given: (h : a ⋖ b)
  statement: exists i, forall j != i, a j = b j
  proof: by
  obtain ⟨i, hi⟩ := exists_forall_antisymmRel_of_covBy h
  exact ⟨i, fun j hj => AntisymmRel.eq (hi _ hj)⟩

中文:
引理 存在_对任意_eq_of_covBy
  条件: (h : a ⋖ b)
  结论: 存在 i, 对任意 j != i, a j = b j
  证明: by
  obtain ⟨i, hi⟩ := exists_forall_antisymmRel_of_covBy h
  exact ⟨i, fun j hj => AntisymmRel.eq (hi _ hj)⟩

Depends on / 依赖: AntisymmRel, AntisymmRel.eq, exists_forall_antisymmRel_of_covBy
-/
lemma exists_forall_eq_of_covBy (h : a ⋖ b) : exists i, forall j != i, a j = b j := by
  obtain ⟨i, hi⟩ := exists_forall_antisymmRel_of_covBy h
  exact ⟨i, fun j hj => AntisymmRel.eq (hi _ hj)⟩

/--
lemma `exists_forall_eq_of_wcovBy` / 引理 `exists_forall_eq_of_wcovBy`

English:
lemma exists_forall_eq_of_wcovBy
  given: [Nonempty ι] (h : a ⩿ b)
  statement: exists i, forall j != i, a j = b j
  proof: by
  obtain ⟨i, hi⟩ := exists_forall_antisymmRel_of_wcovBy h
  exact ⟨i, fun j hj => AntisymmRel.eq (hi _ hj)⟩

中文:
引理 存在_对任意_eq_of_wcovBy
  条件: [非空 ι] (h : a ⩿ b)
  结论: 存在 i, 对任意 j != i, a j = b j
  证明: by
  obtain ⟨i, hi⟩ := exists_forall_antisymmRel_of_wcovBy h
  exact ⟨i, fun j hj => AntisymmRel.eq (hi _ hj)⟩

Depends on / 依赖: AntisymmRel, AntisymmRel.eq, exists_forall_antisymmRel_of_wcovBy
-/
lemma exists_forall_eq_of_wcovBy [Nonempty ι] (h : a ⩿ b) : exists i, forall j != i, a j = b j := by
  obtain ⟨i, hi⟩ := exists_forall_antisymmRel_of_wcovBy h
  exact ⟨i, fun j hj => AntisymmRel.eq (hi _ hj)⟩

/--
lemma `wcovBy_iff` / 引理 `wcovBy_iff`

English:
lemma wcovBy_iff
  given: [Nonempty ι]
  statement: a ⩿ b ↔ exists i, a i ⩿ b i ∧ forall j != i, a j = b j
  proof: by
  simp [wcovBy_iff_antisymmRel]

中文:
引理 wcovBy_iff
  条件: [非空 ι]
  结论: a ⩿ b ↔ 存在 i, a i ⩿ b i ∧ 对任意 j != i, a j = b j
  证明: by
  simp [wcovBy_iff_antisymmRel]

Depends on / 依赖: wcovBy_iff_antisymmRel
-/
lemma wcovBy_iff [Nonempty ι] : a ⩿ b ↔ exists i, a i ⩿ b i ∧ forall j != i, a j = b j := by
  simp [wcovBy_iff_antisymmRel]

/--
lemma `covBy_iff` / 引理 `covBy_iff`

English:
lemma covBy_iff
  statement: a ⋖ b ↔ exists i, a i ⋖ b i ∧ forall j != i, a j = b j
  proof: by
  simp [covBy_iff_antisymmRel]

中文:
引理 covBy_iff
  结论: a ⋖ b ↔ 存在 i, a i ⋖ b i ∧ 对任意 j != i, a j = b j
  证明: by
  simp [covBy_iff_antisymmRel]

Depends on / 依赖: covBy_iff_antisymmRel
-/
lemma covBy_iff : a ⋖ b ↔ exists i, a i ⋖ b i ∧ forall j != i, a j = b j := by
  simp [covBy_iff_antisymmRel]

/--
lemma `wcovBy_iff_exists_right_eq` / 引理 `wcovBy_iff_exists_right_eq`

English:
lemma wcovBy_iff_exists_right_eq
  given: [Nonempty ι] [DecidableEq ι]
  proof: by
  rw [wcovBy_iff]
  constructor
  · rintro ⟨i, hi, h⟩
    exact ⟨i, b i, hi, by simpa [Function.eq_update_iff, eq_comm] using h⟩
  · rintro ⟨i, x, h, rfl⟩
    exact ⟨i, by simpa +contextual⟩

中文:
引理 wcovBy_iff_存在_right_eq
  条件: [非空 ι] [DecidableEq ι]
  证明: by
  rw [wcovBy_iff]
  constructor
  · rintro ⟨i, hi, h⟩
    exact ⟨i, b i, hi, by simpa [Function.eq_update_iff, eq_comm] using h⟩
  · rintro ⟨i, x, h, rfl⟩
    exact ⟨i, by simpa +contextual⟩

Depends on / 依赖: Function, Function.eq_update_iff, contextual, eq_comm, eq_update_iff, wcovBy_iff
-/
lemma wcovBy_iff_exists_right_eq [Nonempty ι] [DecidableEq ι] :
    a ⩿ b ↔ exists i x, a i ⩿ x ∧ b = Function.update a i x := by
  rw [wcovBy_iff]
  constructor
  · rintro ⟨i, hi, h⟩
    exact ⟨i, b i, hi, by simpa [Function.eq_update_iff, eq_comm] using h⟩
  · rintro ⟨i, x, h, rfl⟩
    exact ⟨i, by simpa +contextual⟩

/--
lemma `covBy_iff_exists_right_eq` / 引理 `covBy_iff_exists_right_eq`

English:
lemma covBy_iff_exists_right_eq
  given: [DecidableEq ι]
  proof: by
  rw [covBy_iff]
  constructor
  · rintro ⟨i, hi, h⟩
    exact ⟨i, b i, hi, by simpa [Function.eq_update_iff, eq_comm] using h⟩
  · rintro ⟨i, x, h, rfl⟩
    exact ⟨i, by simpa +contextual⟩

中文:
引理 covBy_iff_存在_right_eq
  条件: [DecidableEq ι]
  证明: by
  rw [covBy_iff]
  constructor
  · rintro ⟨i, hi, h⟩
    exact ⟨i, b i, hi, by simpa [Function.eq_update_iff, eq_comm] using h⟩
  · rintro ⟨i, x, h, rfl⟩
    exact ⟨i, by simpa +contextual⟩

Depends on / 依赖: Function, Function.eq_update_iff, contextual, covBy_iff, eq_comm, eq_update_iff
-/
lemma covBy_iff_exists_right_eq [DecidableEq ι] :
    a ⋖ b ↔ exists i x, a i ⋖ x ∧ b = Function.update a i x := by
  rw [covBy_iff]
  constructor
  · rintro ⟨i, hi, h⟩
    exact ⟨i, b i, hi, by simpa [Function.eq_update_iff, eq_comm] using h⟩
  · rintro ⟨i, x, h, rfl⟩
    exact ⟨i, by simpa +contextual⟩

/--
lemma `wcovBy_iff_exists_left_eq` / 引理 `wcovBy_iff_exists_left_eq`

English:
lemma wcovBy_iff_exists_left_eq
  given: [Nonempty ι] [DecidableEq ι]
  proof: by
  rw [wcovBy_iff]
  constructor
  · rintro ⟨i, hi, h⟩
    exact ⟨i, a i, hi, by simpa [Function.eq_update_iff, eq_comm] using h⟩
  · rintro ⟨i, x, h, rfl⟩
    exact ⟨i, by simpa +contextual⟩

中文:
引理 wcovBy_iff_存在_left_eq
  条件: [非空 ι] [DecidableEq ι]
  证明: by
  rw [wcovBy_iff]
  constructor
  · rintro ⟨i, hi, h⟩
    exact ⟨i, a i, hi, by simpa [Function.eq_update_iff, eq_comm] using h⟩
  · rintro ⟨i, x, h, rfl⟩
    exact ⟨i, by simpa +contextual⟩

Depends on / 依赖: Function, Function.eq_update_iff, contextual, eq_comm, eq_update_iff, wcovBy_iff
-/
lemma wcovBy_iff_exists_left_eq [Nonempty ι] [DecidableEq ι] :
    a ⩿ b ↔ exists i x, x ⩿ b i ∧ a = Function.update b i x := by
  rw [wcovBy_iff]
  constructor
  · rintro ⟨i, hi, h⟩
    exact ⟨i, a i, hi, by simpa [Function.eq_update_iff, eq_comm] using h⟩
  · rintro ⟨i, x, h, rfl⟩
    exact ⟨i, by simpa +contextual⟩

/--
lemma `covBy_iff_exists_left_eq` / 引理 `covBy_iff_exists_left_eq`

English:
lemma covBy_iff_exists_left_eq
  given: [DecidableEq ι]
  proof: by
  rw [covBy_iff]
  constructor
  · rintro ⟨i, hi, h⟩
    exact ⟨i, a i, hi, by simpa [Function.eq_update_iff, eq_comm] using h⟩
  · rintro ⟨i, x, h, rfl⟩
    exact ⟨i, by simpa +contextual⟩

中文:
引理 covBy_iff_存在_left_eq
  条件: [DecidableEq ι]
  证明: by
  rw [covBy_iff]
  constructor
  · rintro ⟨i, hi, h⟩
    exact ⟨i, a i, hi, by simpa [Function.eq_update_iff, eq_comm] using h⟩
  · rintro ⟨i, x, h, rfl⟩
    exact ⟨i, by simpa +contextual⟩

Depends on / 依赖: Function, Function.eq_update_iff, contextual, covBy_iff, eq_comm, eq_update_iff
-/
lemma covBy_iff_exists_left_eq [DecidableEq ι] :
    a ⋖ b ↔ exists i x, x ⋖ b i ∧ a = Function.update b i x := by
  rw [covBy_iff]
  constructor
  · rintro ⟨i, hi, h⟩
    exact ⟨i, a i, hi, by simpa [Function.eq_update_iff, eq_comm] using h⟩
  · rintro ⟨i, x, h, rfl⟩
    exact ⟨i, by simpa +contextual⟩

end PartialOrder

end Pi

namespace WithTop

variable [Preorder α] {a b : α}

@[to_dual (attr := simp, norm_cast)]
/--
lemma `coe_wcovBy_coe` / 引理 `coe_wcovBy_coe`

English:
lemma coe_wcovBy_coe
  statement: (a : WithTop α) ⩿ b ↔ a ⩿ b
  proof: Set.OrdConnected.apply_wcovBy_apply_iff WithTop.coeOrderHom by
    simp [WithTop.range_coe, ordConnected_Iio]

@[to_dual (attr := simp, norm_cast)]

中文:
引理 coe_wcovBy_coe
  结论: (a : WithTop α) ⩿ b ↔ a ⩿ b
  证明: Set.OrdConnected.apply_wcovBy_apply_iff WithTop.coeOrderHom by
    simp [WithTop.range_coe, ordConnected_Iio]

@[to_dual (attr := simp, norm_cast)]

Depends on / 依赖: OrdConnected, Set.OrdConnected.apply_wcovBy_apply_iff, WithTop, WithTop.coeOrderHom, WithTop.range_coe, apply_wcovBy_apply_iff, coeOrderHom, ordConnected_Iio, range_coe
-/
lemma coe_wcovBy_coe : (a : WithTop α) ⩿ b ↔ a ⩿ b :=
Set.OrdConnected.apply_wcovBy_apply_iff WithTop.coeOrderHom by
    simp [WithTop.range_coe, ordConnected_Iio]

@[to_dual (attr := simp, norm_cast)]
/--
lemma `coe_covBy_coe` / 引理 `coe_covBy_coe`

English:
lemma coe_covBy_coe
  statement: (a : WithTop α) ⋖ b ↔ a ⋖ b
  proof: Set.OrdConnected.apply_covBy_apply_iff WithTop.coeOrderHom by
    simp [WithTop.range_coe, ordConnected_Iio]

@[to_dual]

中文:
引理 coe_covBy_coe
  结论: (a : WithTop α) ⋖ b ↔ a ⋖ b
  证明: Set.OrdConnected.apply_covBy_apply_iff WithTop.coeOrderHom by
    simp [WithTop.range_coe, ordConnected_Iio]

@[to_dual]

Depends on / 依赖: OrdConnected, Set.OrdConnected.apply_covBy_apply_iff, WithTop, WithTop.coeOrderHom, WithTop.range_coe, apply_covBy_apply_iff, coeOrderHom, ordConnected_Iio, range_coe
-/
lemma coe_covBy_coe : (a : WithTop α) ⋖ b ↔ a ⋖ b :=
Set.OrdConnected.apply_covBy_apply_iff WithTop.coeOrderHom by
    simp [WithTop.range_coe, ordConnected_Iio]

@[to_dual]
/--
theorem `covBy_top_iff` / 定理 `covBy_top_iff`

English:
theorem covBy_top_iff
  given: {a : WithTop α}
  statement: a ⋖ ⊤ ↔ exists b : α, IsMax b ∧ a = b
  proof: by
  cases a with
  | coe a => simp [CovBy, WithTop.forall, isMax_iff_forall_not_lt]
  | top => simp [CovBy]

@[to_dual (attr := simp)]

中文:
定理 covBy_top_iff
  条件: {a : WithTop α}
  结论: a ⋖ ⊤ ↔ 存在 b : α, IsMax b ∧ a = b
  证明: by
  cases a with
  | coe a => simp [CovBy, WithTop.forall, isMax_iff_forall_not_lt]
  | top => simp [CovBy]

@[to_dual (attr := simp)]

Depends on / 依赖: WithTop, WithTop.forall, isMax_iff_forall_not_lt
-/
theorem covBy_top_iff {a : WithTop α} : a ⋖ ⊤ ↔ exists b : α, IsMax b ∧ a = b := by
  cases a with
  | coe a => simp [CovBy, WithTop.forall, isMax_iff_forall_not_lt]
  | top => simp [CovBy]

@[to_dual (attr := simp)]
/--
theorem `not_covBy_top` / 定理 `not_covBy_top`

English:
theorem not_covBy_top
  given: [NoMaxOrder α] {a : WithTop α}
  statement: ¬ a ⋖ ⊤
  proof: by
  simp [covBy_top_iff]

@[to_dual (attr := simp) bot_covBy_coe]

中文:
定理 not_covBy_top
  条件: [NoMax序 α] {a : WithTop α}
  结论: ¬ a ⋖ ⊤
  证明: by
  simp [covBy_top_iff]

@[to_dual (attr := simp) bot_covBy_coe]

Depends on / 依赖: covBy_top_iff
-/
theorem not_covBy_top [NoMaxOrder α] {a : WithTop α} : ¬ a ⋖ ⊤ := by
  simp [covBy_top_iff]

@[to_dual (attr := simp) bot_covBy_coe]
/--
lemma `coe_covBy_top` / 引理 `coe_covBy_top`

English:
lemma coe_covBy_top
  statement: (a : WithTop α) ⋖ ⊤ ↔ IsMax a
  proof: by
  simp [covBy_iff_Ioo_eq, ← image_coe_Ioi]

@[to_dual (attr := simp) bot_wcovBy_coe]

中文:
引理 coe_covBy_top
  结论: (a : WithTop α) ⋖ ⊤ ↔ IsMax a
  证明: by
  simp [covBy_iff_Ioo_eq, ← image_coe_Ioi]

@[to_dual (attr := simp) bot_wcovBy_coe]

Depends on / 依赖: covBy_iff_Ioo_eq, image_coe_Ioi
-/
lemma coe_covBy_top : (a : WithTop α) ⋖ ⊤ ↔ IsMax a := by
  simp [covBy_iff_Ioo_eq, ← image_coe_Ioi]

@[to_dual (attr := simp) bot_wcovBy_coe]
/--
lemma `coe_wcovBy_top` / 引理 `coe_wcovBy_top`

English:
lemma coe_wcovBy_top
  statement: (a : WithTop α) ⩿ ⊤ ↔ IsMax a
  proof: by
  simp only [wcovBy_iff_Ioo_eq, ← image_coe_Ioi, le_top, image_eq_empty, true_and, Ioi_eq_empty_iff]

中文:
引理 coe_wcovBy_top
  结论: (a : WithTop α) ⩿ ⊤ ↔ IsMax a
  证明: by
  simp only [wcovBy_iff_Ioo_eq, ← image_coe_Ioi, le_top, image_eq_empty, true_and, Ioi_eq_empty_iff]

Depends on / 依赖: Ioi_eq_empty_iff, image_coe_Ioi, image_eq_empty, le_top, true_and, wcovBy_iff_Ioo_eq
-/
lemma coe_wcovBy_top : (a : WithTop α) ⩿ ⊤ ↔ IsMax a := by
  simp only [wcovBy_iff_Ioo_eq, ← image_coe_Ioi, le_top, image_eq_empty, true_and, Ioi_eq_empty_iff]

end WithTop

section WellFounded

variable [Preorder α]

@[to_dual]
/--
lemma `exists_covBy_of_wellFoundedLT` / 引理 `exists_covBy_of_wellFoundedLT`

English:
lemma exists_covBy_of_wellFoundedLT
  given: [wf : WellFoundedLT α] ⦃a
  statement: α⦄ (h : ¬ IsMax a) :
  proof: by
  rw [not_isMax_iff] at h
  exact ⟨_, wellFounded_lt.min_mem (Ioi a) h, fun a' => wf.wf.not_lt_min (Ioi a)⟩

中文:
引理 存在_covBy_of_wellFoundedLT
  条件: [wf : WellFoundedLT α] ⦃a
  结论: α⦄ (h : ¬ IsMax a) :
  证明: by
  rw [not_isMax_iff] at h
  exact ⟨_, wellFounded_lt.min_mem (Ioi a) h, fun a' => wf.wf.not_lt_min (Ioi a)⟩

Depends on / 依赖: min_mem, not_isMax_iff, not_lt_min, wellFounded_lt, wellFounded_lt.min_mem, wf.wf.not_lt_min
-/
lemma exists_covBy_of_wellFoundedLT [wf : WellFoundedLT α] ⦃a : α⦄ (h : ¬ IsMax a) :
    exists a', a ⋖ a' := by
  rw [not_isMax_iff] at h
  exact ⟨_, wellFounded_lt.min_mem (Ioi a) h, fun a' => wf.wf.not_lt_min (Ioi a)⟩

end WellFounded
