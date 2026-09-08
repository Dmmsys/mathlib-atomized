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
/-
**WCovBy.le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WCovBy.le (h : a ⩿ b) : a <= b
参数：h : a ⩿ b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem WCovBy.le (h : a ⩿ b) : a ≤ b :=
  h.1
/-
**WCovBy.refl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WCovBy.refl (a : α) : a ⩿ a
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `LT.lt.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 < a
-/
theorem WCovBy.refl (a : α) : a ⩿ a :=
  ⟨le_rfl, fun _ hc => hc.not_gt⟩
/-
**WCovBy.rfl** 是 Mathlib 中的一个定理，位于命名空间 `WCovBy`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {a : α}, a ⩿ a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WCovBy.refl`：WCovBy.refl (a : α) : a ⩿ a
-/
@[simp] lemma WCovBy.rfl : a ⩿ a := WCovBy.refl a

@[to_dual wcovBy']
/-
**Eq.wcovBy** 是 Mathlib 中的一个定理，位于命名空间 `Eq`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ⩿ b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WCovBy.rfl`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, a ⩿ a
-/
protected theorem Eq.wcovBy (h : a = b) : a ⩿ b :=
  h ▸ WCovBy.rfl

@[to_dual self]
/-
**wcovBy_of_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：wcovBy_of_le_of_le (h1 : a <= b) (h2 : b <= a) : a ⩿ b
参数：h1 : a <= b；h2 : b <= a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
-/
theorem wcovBy_of_le_of_le (h1 : a ≤ b) (h2 : b ≤ a) : a ⩿ b :=
  ⟨h1, fun _ hac hcb => (hac.trans hcb).not_ge h2⟩

@[to_dual self]
alias LE.le.wcovBy_of_le := wcovBy_of_le_of_le
/-
**AntisymmRel.wcovBy** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntisymmRel.wcovBy (h : AntisymmRel (· <= ·) a b) : a ⩿ b
参数：h : AntisymmRel (· <= ·) a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `wcovBy_of_le_of_le`：wcovBy_of_le_of_le (h1 : a <= b) (h2 : b <= a) : a ⩿
 b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem AntisymmRel.wcovBy (h : AntisymmRel (· ≤ ·) a b) : a ⩿ b :=
  wcovBy_of_le_of_le h.1 h.2

@[to_dual self]
/-
**WCovBy.wcovBy_iff_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WCovBy.wcovBy_iff_le (hab : a ⩿ b) : b ⩿ a ↔ b <= a
参数：hab : a ⩿ b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WCovBy.le`：WCovBy.le (h : a ⩿ b) : a <= b
· 使用定理 `LE.le.wcovBy_of_le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ 
b → b ≤ a → a ⩿ b
-/
theorem WCovBy.wcovBy_iff_le (hab : a ⩿ b) : b ⩿ a ↔ b ≤ a :=
  ⟨fun h => h.le, fun h => h.wcovBy_of_le hab.le⟩

@[to_dual none]
/-
**wcovBy_of_eq_or_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：wcovBy_of_eq_or_eq (hab : a <= b) (h : forall c, a <= c -> c <= b -> c = a
 ∨ c = b) : a ⩿ b
参数：hab : a <= b；h : forall c, a <= c -> c <= b -> c = a ∨ c = b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
-/
theorem wcovBy_of_eq_or_eq (hab : a ≤ b) (h : ∀ c, a ≤ c → c ≤ b → c = a ∨ c = b) : a ⩿ b :=
  ⟨hab, fun c ha hb => (h c ha.le hb.le).elim ha.ne' hb.ne⟩
/-
**AntisymmRel.trans_wcovBy** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntisymmRel.trans_wcovBy (hab : AntisymmRel (· <= ·) a b) (hbc : b ⩿ c) : 
a ⩿ c
参数：hab : AntisymmRel (· <= ·) a b；hbc : b ⩿ c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `WCovBy.le`：WCovBy.le (h : a ⩿ b) : a <= b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
-/
theorem AntisymmRel.trans_wcovBy (hab : AntisymmRel (· ≤ ·) a b) (hbc : b ⩿ c) : a ⩿ c :=
  ⟨hab.1.trans hbc.le, fun _ had hdc => hbc.2 (hab.2.trans_lt had) hdc⟩
/-
**wcovBy_congr_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：wcovBy_congr_left (hab : AntisymmRel (· <= ·) a b) : a ⩿ c ↔ b ⩿ c
参数：hab : AntisymmRel (· <= ·) a b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntisymmRel.trans_wcovBy`：AntisymmRel.trans_wcovBy (hab : AntisymmRel (·
 <= ·) a b) (hbc : b ⩿ c) : a ⩿ c
· 使用定理 `AntisymmRel.symm`：AntisymmRel.symm : AntisymmRel r a b -> AntisymmRel r 
b a
-/
theorem wcovBy_congr_left (hab : AntisymmRel (· ≤ ·) a b) : a ⩿ c ↔ b ⩿ c :=
  ⟨hab.symm.trans_wcovBy, hab.trans_wcovBy⟩
/-
**WCovBy.trans_antisymm_rel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WCovBy.trans_antisymm_rel (hab : a ⩿ b) (hbc : AntisymmRel (· <= ·) b c) :
 a ⩿ c
参数：hab : a ⩿ b；hbc : AntisymmRel (· <= ·) b c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `WCovBy.le`：WCovBy.le (h : a ⩿ b) : a <= b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
-/
theorem WCovBy.trans_antisymm_rel (hab : a ⩿ b) (hbc : AntisymmRel (· ≤ ·) b c) : a ⩿ c :=
  ⟨hab.le.trans hbc.1, fun _ had hdc => hab.2 had <| hdc.trans_le hbc.2⟩
/-
**wcovBy_congr_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：wcovBy_congr_right (hab : AntisymmRel (· <= ·) a b) : c ⩿ a ↔ c ⩿ b
参数：hab : AntisymmRel (· <= ·) a b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WCovBy.trans_antisymm_rel`：WCovBy.trans_antisymm_rel (hab : a ⩿ b) (hbc 
: AntisymmRel (· <= ·) b c) : a ⩿ c
· 使用定理 `AntisymmRel.symm`：AntisymmRel.symm : AntisymmRel r a b -> AntisymmRel r 
b a
-/
theorem wcovBy_congr_right (hab : AntisymmRel (· ≤ ·) a b) : c ⩿ a ↔ c ⩿ b :=
  ⟨fun h => h.trans_antisymm_rel hab, fun h => h.trans_antisymm_rel hab.symm⟩

/-- If `a ≤ b`, then `b` does not cover `a` iff there's an element in between. -/
@[to_dual none]
/-
**not_wcovBy_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_wcovBy_iff (h : a <= b) : ¬a ⩿ b ↔ exists c, a < c ∧ c < b
参数：h : a <= b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
If `a ≤ b`, then `b` does not cover `a` iff there's an element in between.
-/
theorem not_wcovBy_iff (h : a ≤ b) : ¬a ⩿ b ↔ ∃ c, a < c ∧ c < b := by
  simp_rw [WCovBy, h, true_and, not_forall, exists_prop, not_not]

@[to_dual stdRefl']
/-
**WCovBy.stdRefl** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：WCovBy.stdRefl : @Std.Refl α (· ⩿ ·)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `WCovBy.refl`：WCovBy.refl (a : α) : a ⩿ a
-/
instance WCovBy.stdRefl : @Std.Refl α (· ⩿ ·) :=
  ⟨WCovBy.refl⟩

@[to_dual self]
/-
**WCovBy.Ioo_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WCovBy.Ioo_eq (h : a ⩿ b) : Ioo a b = ∅
参数：h : a ⩿ b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.eq_empty_iff_forall_notMem`：eq_empty_iff_forall_notMem {s : Set α} :
 s = ∅ ↔ forall x, x ∉ s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem WCovBy.Ioo_eq (h : a ⩿ b) : Ioo a b = ∅ :=
  eq_empty_iff_forall_notMem.2 fun _ hx => h.2 hx.1 hx.2

@[to_dual self]
/-
**wcovBy_iff_Ioo_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：wcovBy_iff_Ioo_eq : a ⩿ b ↔ a <= b ∧ Ioo a b = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `and_congr_right'`：∀ {b c a : Prop}, (b ↔ c) → (a ∧ b ↔ a ∧ c)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem wcovBy_iff_Ioo_eq : a ⩿ b ↔ a ≤ b ∧ Ioo a b = ∅ :=
  and_congr_right' <| by simp [eq_empty_iff_forall_notMem]

@[to_dual of_le_of_le']
/-
**WCovBy.of_le_of_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：WCovBy.of_le_of_le (hac : a ⩿ c) (hab : a <= b) (hbc : b <= c) : b ⩿ c
参数：hac : a ⩿ c；hab : a <= b；hbc : b <= c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
-/
lemma WCovBy.of_le_of_le (hac : a ⩿ c) (hab : a ≤ b) (hbc : b ≤ c) : b ⩿ c :=
  ⟨hbc, fun _x hbx hxc ↦ hac.2 (hab.trans_lt hbx) hxc⟩

@[to_dual self]
/-
**WCovBy.of_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WCovBy.of_image (f : α ↪o β) (h : f a ⩿ f b) : a ⩿ b
参数：f : α ↪o β；h : f a ⩿ f b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `OrderEmbedding.le_iff_le`：le_iff_le {a b} : f a <= f b ↔ a <= b
· 使用定理 `WCovBy.le`：WCovBy.le (h : a ⩿ b) : a <= b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `OrderEmbedding.lt_iff_lt`：lt_iff_lt {a b} : f a < f b ↔ a < b
-/
theorem WCovBy.of_image (f : α ↪o β) (h : f a ⩿ f b) : a ⩿ b :=
  ⟨f.le_iff_le.mp h.le, fun _ hac hcb => h.2 (f.lt_iff_lt.mpr hac) (f.lt_iff_lt.mpr hcb)⟩

@[to_dual self]
/-
**WCovBy.image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WCovBy.image (f : α ↪o β) (hab : a ⩿ b) (h : (range f).OrdConnected) : f a
 ⩿ f b
参数：f : α ↪o β；hab : a ⩿ b；h : (range f).OrdConnected。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorde
r α] [inst_1 : Preorder β] (f : α ↪o β), Monotone ⇑f
· 使用定理 `WCovBy.le`：WCovBy.le (h : a ⩿ b) : a <= b
· 使用定理 `Set.OrdConnected.out`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α}, 
s.OrdConnected → ∀ ⦃x : α⦄, x ∈ s → ∀ ⦃y : α⦄, y ∈ s → Set.Icc x y ⊆ s
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrderEmbedding.lt_iff_lt`：lt_iff_lt {a b} : f a < f b ↔ a < b
-/
theorem WCovBy.image (f : α ↪o β) (hab : a ⩿ b) (h : (range f).OrdConnected) : f a ⩿ f b := by
  refine ⟨f.monotone hab.le, fun c ha hb => ?_⟩
  obtain ⟨c, rfl⟩ := h.out (mem_range_self _) (mem_range_self _) ⟨ha.le, hb.le⟩
  rw [f.lt_iff_lt] at ha hb
  exact hab.2 ha hb

@[to_dual self]
/-
**Set.OrdConnected.apply_wcovBy_apply_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.OrdConnected.apply_wcovBy_apply_iff (f : α ↪o β) (h : (range f).OrdCon
nected) : f a ⩿ f b ↔ a ⩿ b
参数：f : α ↪o β；h : (range f).OrdConnected。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WCovBy.of_image`：WCovBy.of_image (f : α ↪o β) (h : f a ⩿ f b) : a ⩿ b
· 使用定理 `WCovBy.image`：WCovBy.image (f : α ↪o β) (hab : a ⩿ b) (h : (range f).Ord
Connected) : f a ⩿ f b
-/
theorem Set.OrdConnected.apply_wcovBy_apply_iff (f : α ↪o β) (h : (range f).OrdConnected) :
    f a ⩿ f b ↔ a ⩿ b :=
  ⟨fun h2 => h2.of_image f, fun hab => hab.image f h⟩

@[simp, to_dual self]
/-
**apply_wcovBy_apply_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：apply_wcovBy_apply_iff {E : Type*} [EquivLike E α β] [OrderIsoClass E α β]
 (e : E) : e a ⩿ e b ↔ a ⩿ b
参数：e : E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.OrdConnected.apply_wcovBy_apply_iff`：Set.OrdConnected.apply_wcovBy_a
pply_iff (f : α ↪o β) (h : (range f).OrdConnected) : f a ⩿ f b ↔ a ⩿ b
· 使用定理 `Set.ordConnected_range`：ordConnected_range {E : Type*} [EquivLike E α β]
 [OrderIsoClass E α β] (e : E) : OrdConnected (range e)
· 使用定理 `OrderIso.instOrderIsoClass`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α
] [inst_1 : LE β], OrderIsoClass (α ≃o β) α β
-/
theorem apply_wcovBy_apply_iff {E : Type*} [EquivLike E α β] [OrderIsoClass E α β] (e : E) :
    e a ⩿ e b ↔ a ⩿ b :=
  (ordConnected_range (e : α ≃o β)).apply_wcovBy_apply_iff ((e : α ≃o β) : α ↪o β)

@[simp, to_dual self]
/-
**toDual_wcovBy_toDual_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toDual_wcovBy_toDual_iff : toDual b ⩿ toDual a ↔ a ⩿ b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `and_congr_right'`：∀ {b c a : Prop}, (b ↔ c) → (a ∧ b ↔ a ∧ c)
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
-/
theorem toDual_wcovBy_toDual_iff : toDual b ⩿ toDual a ↔ a ⩿ b :=
  and_congr_right' <| forall_congr' fun _ => forall_comm

@[simp, to_dual self]
/-
**ofDual_wcovBy_ofDual_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofDual_wcovBy_ofDual_iff {a b : αᵒᵈ} : ofDual a ⩿ ofDual b ↔ b ⩿ a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `and_congr_right'`：∀ {b c a : Prop}, (b ↔ c) → (a ∧ b ↔ a ∧ c)
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
-/
theorem ofDual_wcovBy_ofDual_iff {a b : αᵒᵈ} : ofDual a ⩿ ofDual b ↔ b ⩿ a :=
  and_congr_right' <| forall_congr' fun _ => forall_comm

@[to_dual self]
alias ⟨_, WCovBy.toDual⟩ := toDual_wcovBy_toDual_iff

@[to_dual self]
alias ⟨_, WCovBy.ofDual⟩ := ofDual_wcovBy_ofDual_iff

end Preorder

section PartialOrder

variable [PartialOrder α] {a b c : α}

@[to_dual none]
/-
**WCovBy.eq_or_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WCovBy.eq_or_eq (h : a ⩿ b) (h2 : a <= c) (h3 : c <= b) : c = a ∨ c = b
参数：h : a ⩿ b；h2 : a <= c；h3 : c <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem WCovBy.eq_or_eq (h : a ⩿ b) (h2 : a ≤ c) (h3 : c ≤ b) : c = a ∨ c = b := by
  rcases h2.eq_or_lt with (h2 | h2); · exact Or.inl h2.symm
  rcases h3.eq_or_lt with (h3 | h3); · exact Or.inr h3
  exact (h.2 h2 h3).elim

/-- An `iff` version of `WCovBy.eq_or_eq` and `wcovBy_of_eq_or_eq`. -/
@[to_dual none]
/-
**wcovBy_iff_le_and_eq_or_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：wcovBy_iff_le_and_eq_or_eq : a ⩿ b ↔ a <= b ∧ forall c, a <= c -> c <= b -
> c = a ∨ c = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WCovBy.le`：WCovBy.le (h : a ⩿ b) : a <= b
· 使用定理 `WCovBy.eq_or_eq`：WCovBy.eq_or_eq (h : a ⩿ b) (h2 : a <= c) (h3 : c <= b)
 : c = a ∨ c = b
· 使用定理 `wcovBy_of_eq_or_eq`：wcovBy_of_eq_or_eq (hab : a <= b) (h : forall c, a <
= c -> c <= b -> c = a ∨ c = b) : a ⩿ b

--- 原说明 ---
An `iff` version of `WCovBy.eq_or_eq` and `wcovBy_of_eq_or_eq`.
-/
theorem wcovBy_iff_le_and_eq_or_eq : a ⩿ b ↔ a ≤ b ∧ ∀ c, a ≤ c → c ≤ b → c = a ∨ c = b :=
  ⟨fun h => ⟨h.le, fun _ => h.eq_or_eq⟩, And.rec wcovBy_of_eq_or_eq⟩

@[to_dual none]
/-
**WCovBy.le_and_le_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WCovBy.le_and_le_iff (h : a ⩿ b) : a <= c ∧ c <= b ↔ c = a ∨ c = b
参数：h : a ⩿ b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WCovBy.eq_or_eq`：WCovBy.eq_or_eq (h : a ⩿ b) (h2 : a <= c) (h3 : c <= b)
 : c = a ∨ c = b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `WCovBy.le`：WCovBy.le (h : a ⩿ b) : a <= b
-/
theorem WCovBy.le_and_le_iff (h : a ⩿ b) : a ≤ c ∧ c ≤ b ↔ c = a ∨ c = b := by
  refine ⟨fun h2 => h.eq_or_eq h2.1 h2.2, ?_⟩; rintro (rfl | rfl)
  exacts [⟨le_rfl, h.le⟩, ⟨h.le, le_rfl⟩]

@[to_dual none]
/-
**WCovBy.Icc_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WCovBy.Icc_eq (h : a ⩿ b) : Icc a b = {a, b}
参数：h : a ⩿ b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `WCovBy.le_and_le_iff`：WCovBy.le_and_le_iff (h : a ⩿ b) : a <= c ∧ c <= b
 ↔ c = a ∨ c = b
-/
theorem WCovBy.Icc_eq (h : a ⩿ b) : Icc a b = {a, b} := by
  ext c
  exact h.le_and_le_iff
/-
**WCovBy.Ico_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WCovBy.Ico_subset (h : a ⩿ b) : Ico a b subseteq {a}
参数：h : a ⩿ b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Icc_sdiff_right`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α},
 Set.Icc b a \ {a} = Set.Ico b a
· 使用定理 `WCovBy.Icc_eq`：WCovBy.Icc_eq (h : a ⩿ b) : Icc a b = {a, b}
· 使用引理 `Set.sdiff_singleton_subset_iff`：sdiff_singleton_subset_iff : s \ {a} sub
seteq t ↔ s subseteq insert a t
· 使用定理 `Set.pair_comm`：pair_comm (a b : α) : ({a, b} : Set α) = {b, a}
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem WCovBy.Ico_subset (h : a ⩿ b) : Ico a b ⊆ {a} := by
  rw [← Icc_sdiff_right, h.Icc_eq, sdiff_singleton_subset_iff, pair_comm]
/-
**WCovBy.Ioc_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WCovBy.Ioc_subset (h : a ⩿ b) : Ioc a b subseteq {b}
参数：h : a ⩿ b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Icc_sdiff_left`：Icc_sdiff_left : Icc a b \ {a} = Ioc a b
· 使用定理 `WCovBy.Icc_eq`：WCovBy.Icc_eq (h : a ⩿ b) : Icc a b = {a, b}
· 使用引理 `Set.sdiff_singleton_subset_iff`：sdiff_singleton_subset_iff : s \ {a} sub
seteq t ↔ s subseteq insert a t
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem WCovBy.Ioc_subset (h : a ⩿ b) : Ioc a b ⊆ {b} := by
  rw [← Icc_sdiff_left, h.Icc_eq, sdiff_singleton_subset_iff]

end PartialOrder

section SemilatticeSup

variable [SemilatticeSup α] {a b c : α}

@[to_dual]
/-
**WCovBy.sup_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WCovBy.sup_eq (hac : a ⩿ c) (hbc : b ⩿ c) (hab : a != b) : a ⊔ b = c
参数：hac : a ⩿ c；hbc : b ⩿ c；hab : a != b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_of_not_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, 
a ≤ b → ¬a < b → a = b
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `WCovBy.le`：WCovBy.le (h : a ⩿ b) : a <= b
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Ne.lt_sup_or_lt_sup`：Ne.lt_sup_or_lt_sup (hab : a != b) : a < a ⊔ b ∨ b 
< a ⊔ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem WCovBy.sup_eq (hac : a ⩿ c) (hbc : b ⩿ c) (hab : a ≠ b) : a ⊔ b = c :=
  (sup_le hac.le hbc.le).eq_of_not_lt fun h =>
    hab.lt_sup_or_lt_sup.elim (fun h' => hac.2 h' h) fun h' => hbc.2 h' h

end SemilatticeSup

end WeaklyCovers

section LT

variable [LT α] {a b : α}

@[to_dual self]
/-
**CovBy.lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CovBy.lt (h : a ⋖ b) : a < b
参数：h : a ⋖ b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem CovBy.lt (h : a ⋖ b) : a < b :=
  h.1

/-- If `a < b`, then `b` does not cover `a` iff there's an element in between. -/
@[to_dual none]
/-
**not_covBy_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_covBy_iff (h : a < b) : ¬a ⋖ b ↔ exists c, a < c ∧ c < b
参数：h : a < b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
If `a < b`, then `b` does not cover `a` iff there's an element in between.
-/
theorem not_covBy_iff (h : a < b) : ¬a ⋖ b ↔ ∃ c, a < c ∧ c < b := by
  simp_rw [CovBy, h, true_and, not_forall, exists_prop, not_not]

@[to_dual none]
alias ⟨exists_lt_lt_of_not_covBy, _⟩ := not_covBy_iff

@[to_dual none]
alias LT.lt.exists_lt_lt := exists_lt_lt_of_not_covBy

/-- In a dense order, nothing covers anything. -/
@[to_dual self]
/-
**not_covBy** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_covBy [DenselyOrdered α] : ¬a ⋖ b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_between`：exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a
₁ < a₂ -> exists a, a₁ < a ∧ a < a₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
In a dense order, nothing covers anything.
-/
theorem not_covBy [DenselyOrdered α] : ¬a ⋖ b := fun h =>
  let ⟨_, hc⟩ := exists_between h.1
  h.2 hc.1 hc.2
/-
**denselyOrdered_iff_forall_not_covBy** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：denselyOrdered_iff_forall_not_covBy : DenselyOrdered α ↔ forall a b : α, ¬
a ⋖ b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_covBy`：not_covBy [DenselyOrdered α] : ¬a ⋖ b
· 使用定理 `exists_lt_lt_of_not_covBy`：∀ {α : Type u_1} [inst : LT α] {a b : α}, a <
 b → ¬a ⋖ b → ∃ c, a < c ∧ c < b
-/
theorem denselyOrdered_iff_forall_not_covBy : DenselyOrdered α ↔ ∀ a b : α, ¬a ⋖ b :=
  ⟨fun h _ _ => @not_covBy _ _ _ _ h, fun h =>
    ⟨fun _ _ hab => exists_lt_lt_of_not_covBy hab <| h _ _⟩⟩

@[to_dual self, simp]
/-
**toDual_covBy_toDual_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toDual_covBy_toDual_iff : toDual b ⋖ toDual a ↔ a ⋖ b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `and_congr_right'`：∀ {b c a : Prop}, (b ↔ c) → (a ∧ b ↔ a ∧ c)
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
-/
theorem toDual_covBy_toDual_iff : toDual b ⋖ toDual a ↔ a ⋖ b :=
  and_congr_right' <| forall_congr' fun _ => forall_comm

@[to_dual self, simp]
/-
**ofDual_covBy_ofDual_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofDual_covBy_ofDual_iff {a b : αᵒᵈ} : ofDual a ⋖ ofDual b ↔ b ⋖ a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `and_congr_right'`：∀ {b c a : Prop}, (b ↔ c) → (a ∧ b ↔ a ∧ c)
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
-/
theorem ofDual_covBy_ofDual_iff {a b : αᵒᵈ} : ofDual a ⋖ ofDual b ↔ b ⋖ a :=
  and_congr_right' <| forall_congr' fun _ => forall_comm

@[to_dual self]
alias ⟨_, CovBy.toDual⟩ := toDual_covBy_toDual_iff

@[to_dual self]
alias ⟨_, CovBy.ofDual⟩ := ofDual_covBy_ofDual_iff

end LT

section Preorder

variable [Preorder α] [Preorder β] {a b c : α}

/-
**covBy_irrefl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {a : α}, ¬a ⋖ a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
@[simp] lemma covBy_irrefl : ¬ a ⋖ a := by simp [CovBy]

@[to_dual self]
/-
**not_covBy_iff_nonempty_Ioo** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_covBy_iff_nonempty_Ioo (h : a < b) : ¬a ⋖ b ↔ (Ioo a b).Nonempty
参数：h : a < b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_covBy_iff`：not_covBy_iff (h : a < b) : ¬a ⋖ b ↔ exists c, a < c ∧ c 
< b
-/
theorem not_covBy_iff_nonempty_Ioo (h : a < b) : ¬a ⋖ b ↔ (Ioo a b).Nonempty :=
  not_covBy_iff h

@[to_dual self]
/-
**CovBy.le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CovBy.le (h : a ⋖ b) : a <= b
参数：h : a ⋖ b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem CovBy.le (h : a ⋖ b) : a ≤ b :=
  h.1.le

@[to_dual ne']
/-
**CovBy.ne** 是 Mathlib 中的一个定理，位于命名空间 `CovBy`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ⋖ b → a ≠ b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `CovBy.lt`：CovBy.lt (h : a ⋖ b) : a < b
-/
protected theorem CovBy.ne (h : a ⋖ b) : a ≠ b :=
  h.lt.ne

@[to_dual self]
/-
**CovBy.wcovBy** 是 Mathlib 中的一个定理，位于命名空间 `CovBy`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ⋖ b → a ⩿ b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CovBy.le`：CovBy.le (h : a ⋖ b) : a <= b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
protected theorem CovBy.wcovBy (h : a ⋖ b) : a ⩿ b :=
  ⟨h.le, h.2⟩

@[to_dual self]
/-
**WCovBy.covBy_of_not_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WCovBy.covBy_of_not_le (h : a ⩿ b) (h2 : ¬b <= a) : a ⋖ b
参数：h : a ⩿ b；h2 : ¬b <= a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.lt_of_not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ 
b → ¬b ≤ a → a < b
· 使用定理 `WCovBy.le`：WCovBy.le (h : a ⩿ b) : a <= b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem WCovBy.covBy_of_not_le (h : a ⩿ b) (h2 : ¬b ≤ a) : a ⋖ b :=
  ⟨h.le.lt_of_not_ge h2, h.2⟩

@[to_dual self]
/-
**WCovBy.covBy_of_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WCovBy.covBy_of_lt (h : a ⩿ b) (h2 : a < b) : a ⋖ b
参数：h : a ⩿ b；h2 : a < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem WCovBy.covBy_of_lt (h : a ⩿ b) (h2 : a < b) : a ⋖ b :=
  ⟨h2, h.2⟩
/-
**CovBy.of_le_of_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CovBy.of_le_of_lt (hac : a ⋖ c) (hab : a <= b) (hbc : b < c) : b ⋖ c
参数：hac : a ⋖ c；hab : a <= b；hbc : b < c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
-/
lemma CovBy.of_le_of_lt (hac : a ⋖ c) (hab : a ≤ b) (hbc : b < c) : b ⋖ c :=
  ⟨hbc, fun _x hbx hxc ↦ hac.2 (hab.trans_lt hbx) hxc⟩
/-
**CovBy.of_lt_of_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CovBy.of_lt_of_le (hac : a ⋖ c) (hab : a < b) (hbc : b <= c) : a ⋖ b
参数：hac : a ⋖ c；hab : a < b；hbc : b <= c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
-/
lemma CovBy.of_lt_of_le (hac : a ⋖ c) (hab : a < b) (hbc : b ≤ c) : a ⋖ b :=
  ⟨hab, fun _x hax hxb ↦ hac.2 hax <| hxb.trans_le hbc⟩

@[to_dual self (reorder := a c, h₁ h₂)]
/-
**not_covBy_of_lt_of_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_covBy_of_lt_of_lt (h₁ : a < b) (h₂ : b < c) : ¬a ⋖ c
参数：h₁ : a < b；h₂ : b < c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_covBy_iff`：not_covBy_iff (h : a < b) : ¬a ⋖ b ↔ exists c, a < c ∧ c 
< b
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
-/
theorem not_covBy_of_lt_of_lt (h₁ : a < b) (h₂ : b < c) : ¬a ⋖ c :=
  (not_covBy_iff (h₁.trans h₂)).2 ⟨b, h₁, h₂⟩

@[to_dual self]
/-
**not_covBy_iff_exists_mem_Ioo** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_covBy_iff_exists_mem_Ioo (h : a < b) : ¬a ⋖ b ↔ exists c, c in Set.Ioo
 a b
参数：h : a < b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_covBy_iff`：not_covBy_iff (h : a < b) : ¬a ⋖ b ↔ exists c, a < c ∧ c 
< b
-/
theorem not_covBy_iff_exists_mem_Ioo (h : a < b) : ¬a ⋖ b ↔ ∃ c, c ∈ Set.Ioo a b :=
  not_covBy_iff h

@[to_dual self]
/-
**covBy_iff_wcovBy_and_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：covBy_iff_wcovBy_and_lt : a ⋖ b ↔ a ⩿ b ∧ a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CovBy.wcovBy`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ⋖ b → a 
⩿ b
· 使用定理 `CovBy.lt`：CovBy.lt (h : a ⋖ b) : a < b
· 使用定理 `WCovBy.covBy_of_lt`：WCovBy.covBy_of_lt (h : a ⩿ b) (h2 : a < b) : a ⋖ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem covBy_iff_wcovBy_and_lt : a ⋖ b ↔ a ⩿ b ∧ a < b :=
  ⟨fun h => ⟨h.wcovBy, h.lt⟩, fun h => h.1.covBy_of_lt h.2⟩

@[to_dual self]
/-
**covBy_iff_wcovBy_and_not_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：covBy_iff_wcovBy_and_not_le : a ⋖ b ↔ a ⩿ b ∧ ¬b <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CovBy.wcovBy`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ⋖ b → a 
⩿ b
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `CovBy.lt`：CovBy.lt (h : a ⋖ b) : a < b
· 使用定理 `WCovBy.covBy_of_not_le`：WCovBy.covBy_of_not_le (h : a ⩿ b) (h2 : ¬b <= a
) : a ⋖ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem covBy_iff_wcovBy_and_not_le : a ⋖ b ↔ a ⩿ b ∧ ¬b ≤ a :=
  ⟨fun h => ⟨h.wcovBy, h.lt.not_ge⟩, fun h => h.1.covBy_of_not_le h.2⟩

@[to_dual self]
/-
**wcovBy_iff_covBy_or_le_and_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：wcovBy_iff_covBy_or_le_and_le : a ⩿ b ↔ a ⋖ b ∨ a <= b ∧ b <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_right`：∀ {a b : Prop}, a ∨ b ↔ ¬b → a
· 使用定理 `WCovBy.covBy_of_not_le`：WCovBy.covBy_of_not_le (h : a ⩿ b) (h2 : ¬b <= a
) : a ⋖ b
· 使用定理 `WCovBy.le`：WCovBy.le (h : a ⩿ b) : a <= b
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `CovBy.wcovBy`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ⋖ b → a 
⩿ b
· 使用定理 `LE.le.wcovBy_of_le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ 
b → b ≤ a → a ⩿ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem wcovBy_iff_covBy_or_le_and_le : a ⩿ b ↔ a ⋖ b ∨ a ≤ b ∧ b ≤ a :=
  ⟨fun h => or_iff_not_imp_right.mpr fun h' => h.covBy_of_not_le fun hba => h' ⟨h.le, hba⟩,
    fun h' => h'.elim (fun h => h.wcovBy) fun h => h.1.wcovBy_of_le h.2⟩

@[to_dual self]
alias ⟨WCovBy.covBy_or_le_and_le, _⟩ := wcovBy_iff_covBy_or_le_and_le
/-
**AntisymmRel.trans_covBy** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntisymmRel.trans_covBy (hab : AntisymmRel (· <= ·) a b) (hbc : b ⋖ c) : a
 ⋖ c
参数：hab : AntisymmRel (· <= ·) a b；hbc : b ⋖ c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `CovBy.lt`：CovBy.lt (h : a ⋖ b) : a < b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem AntisymmRel.trans_covBy (hab : AntisymmRel (· ≤ ·) a b) (hbc : b ⋖ c) : a ⋖ c :=
  ⟨hab.1.trans_lt hbc.lt, fun _ had hdc => hbc.2 (hab.2.trans_lt had) hdc⟩
/-
**covBy_congr_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：covBy_congr_left (hab : AntisymmRel (· <= ·) a b) : a ⋖ c ↔ b ⋖ c
参数：hab : AntisymmRel (· <= ·) a b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntisymmRel.trans_covBy`：AntisymmRel.trans_covBy (hab : AntisymmRel (· <
= ·) a b) (hbc : b ⋖ c) : a ⋖ c
· 使用定理 `AntisymmRel.symm`：AntisymmRel.symm : AntisymmRel r a b -> AntisymmRel r 
b a
-/
theorem covBy_congr_left (hab : AntisymmRel (· ≤ ·) a b) : a ⋖ c ↔ b ⋖ c :=
  ⟨hab.symm.trans_covBy, hab.trans_covBy⟩
/-
**CovBy.trans_antisymmRel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CovBy.trans_antisymmRel (hab : a ⋖ b) (hbc : AntisymmRel (· <= ·) b c) : a
 ⋖ c
参数：hab : a ⋖ b；hbc : AntisymmRel (· <= ·) b c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `CovBy.lt`：CovBy.lt (h : a ⋖ b) : a < b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem CovBy.trans_antisymmRel (hab : a ⋖ b) (hbc : AntisymmRel (· ≤ ·) b c) : a ⋖ c :=
  ⟨hab.lt.trans_le hbc.1, fun _ had hdb => hab.2 had <| hdb.trans_le hbc.2⟩
/-
**covBy_congr_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：covBy_congr_right (hab : AntisymmRel (· <= ·) a b) : c ⋖ a ↔ c ⋖ b
参数：hab : AntisymmRel (· <= ·) a b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CovBy.trans_antisymmRel`：CovBy.trans_antisymmRel (hab : a ⋖ b) (hbc : An
tisymmRel (· <= ·) b c) : a ⋖ c
· 使用定理 `AntisymmRel.symm`：AntisymmRel.symm : AntisymmRel r a b -> AntisymmRel r 
b a
-/
theorem covBy_congr_right (hab : AntisymmRel (· ≤ ·) a b) : c ⋖ a ↔ c ⋖ b :=
  ⟨fun h => h.trans_antisymmRel hab, fun h => h.trans_antisymmRel hab.symm⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsNonstrictStrictOrder α (· ⩿ ·) (· ⋖ ·) :=
  ⟨fun _ _ =>
    covBy_iff_wcovBy_and_not_le.trans <| and_congr_right fun h => h.wcovBy_iff_le.not.symm⟩
/-
**CovBy.irrefl** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：CovBy.irrefl : @Std.Irrefl α (· ⋖ ·)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CovBy.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ⋖ b → a ≠ b
-/
instance CovBy.irrefl : @Std.Irrefl α (· ⋖ ·) :=
  ⟨fun _ ha => ha.ne rfl⟩

@[to_dual self]
/-
**CovBy.Ioo_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CovBy.Ioo_eq (h : a ⋖ b) : Ioo a b = ∅
参数：h : a ⋖ b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WCovBy.Ioo_eq`：WCovBy.Ioo_eq (h : a ⩿ b) : Ioo a b = ∅
· 使用定理 `CovBy.wcovBy`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ⋖ b → a 
⩿ b
-/
theorem CovBy.Ioo_eq (h : a ⋖ b) : Ioo a b = ∅ :=
  h.wcovBy.Ioo_eq

@[to_dual self]
/-
**covBy_iff_Ioo_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：covBy_iff_Ioo_eq : a ⋖ b ↔ a < b ∧ Ioo a b = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `and_congr_right'`：∀ {b c a : Prop}, (b ↔ c) → (a ∧ b ↔ a ∧ c)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem covBy_iff_Ioo_eq : a ⋖ b ↔ a < b ∧ Ioo a b = ∅ :=
  and_congr_right' <| by simp [eq_empty_iff_forall_notMem]

@[to_dual self]
/-
**CovBy.of_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CovBy.of_image (f : α ↪o β) (h : f a ⋖ f b) : a ⋖ b
参数：f : α ↪o β；h : f a ⋖ f b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `OrderEmbedding.lt_iff_lt`：lt_iff_lt {a b} : f a < f b ↔ a < b
· 使用定理 `CovBy.lt`：CovBy.lt (h : a ⋖ b) : a < b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem CovBy.of_image (f : α ↪o β) (h : f a ⋖ f b) : a ⋖ b :=
  ⟨f.lt_iff_lt.mp h.lt, fun _ hac hcb => h.2 (f.lt_iff_lt.mpr hac) (f.lt_iff_lt.mpr hcb)⟩

@[to_dual self]
/-
**CovBy.image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CovBy.image (f : α ↪o β) (hab : a ⋖ b) (h : (range f).OrdConnected) : f a 
⋖ f b
参数：f : α ↪o β；hab : a ⋖ b；h : (range f).OrdConnected。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WCovBy.covBy_of_lt`：WCovBy.covBy_of_lt (h : a ⩿ b) (h2 : a < b) : a ⋖ b
· 使用定理 `WCovBy.image`：WCovBy.image (f : α ↪o β) (hab : a ⩿ b) (h : (range f).Ord
Connected) : f a ⩿ f b
· 使用定理 `CovBy.wcovBy`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ⋖ b → a 
⩿ b
· 使用定理 `OrderEmbedding.strictMono`：∀ {α : Type u_2} {β : Type u_3} [inst : Preor
der α] [inst_1 : Preorder β] (f : α ↪o β), StrictMono ⇑f
· 使用定理 `CovBy.lt`：CovBy.lt (h : a ⋖ b) : a < b
-/
theorem CovBy.image (f : α ↪o β) (hab : a ⋖ b) (h : (range f).OrdConnected) : f a ⋖ f b :=
  (hab.wcovBy.image f h).covBy_of_lt <| f.strictMono hab.lt

@[to_dual self]
/-
**Set.OrdConnected.apply_covBy_apply_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.OrdConnected.apply_covBy_apply_iff (f : α ↪o β) (h : (range f).OrdConn
ected) : f a ⋖ f b ↔ a ⋖ b
参数：f : α ↪o β；h : (range f).OrdConnected。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CovBy.of_image`：CovBy.of_image (f : α ↪o β) (h : f a ⋖ f b) : a ⋖ b
· 使用定理 `CovBy.image`：CovBy.image (f : α ↪o β) (hab : a ⋖ b) (h : (range f).OrdCo
nnected) : f a ⋖ f b
-/
theorem Set.OrdConnected.apply_covBy_apply_iff (f : α ↪o β) (h : (range f).OrdConnected) :
    f a ⋖ f b ↔ a ⋖ b :=
  ⟨CovBy.of_image f, fun hab => hab.image f h⟩

@[to_dual self, simp]
/-
**apply_covBy_apply_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：apply_covBy_apply_iff {E : Type*} [EquivLike E α β] [OrderIsoClass E α β] 
(e : E) : e a ⋖ e b ↔ a ⋖ b
参数：e : E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.OrdConnected.apply_covBy_apply_iff`：Set.OrdConnected.apply_covBy_app
ly_iff (f : α ↪o β) (h : (range f).OrdConnected) : f a ⋖ f b ↔ a ⋖ b
· 使用定理 `Set.ordConnected_range`：ordConnected_range {E : Type*} [EquivLike E α β]
 [OrderIsoClass E α β] (e : E) : OrdConnected (range e)
· 使用定理 `OrderIso.instOrderIsoClass`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α
] [inst_1 : LE β], OrderIsoClass (α ≃o β) α β
-/
theorem apply_covBy_apply_iff {E : Type*} [EquivLike E α β] [OrderIsoClass E α β] (e : E) :
    e a ⋖ e b ↔ a ⋖ b :=
  (ordConnected_range (e : α ≃o β)).apply_covBy_apply_iff ((e : α ≃o β) : α ↪o β)

@[to_dual none]
/-
**covBy_of_eq_or_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：covBy_of_eq_or_eq (hab : a < b) (h : forall c, a <= c -> c <= b -> c = a ∨
 c = b) : a ⋖ b
参数：hab : a < b；h : forall c, a <= c -> c <= b -> c = a ∨ c = b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
-/
theorem covBy_of_eq_or_eq (hab : a < b) (h : ∀ c, a ≤ c → c ≤ b → c = a ∨ c = b) : a ⋖ b :=
  ⟨hab, fun c ha hb => (h c ha.le hb.le).elim ha.ne' hb.ne⟩

end Preorder

section PartialOrder

variable [PartialOrder α] {a b c : α}

@[to_dual none]
/-
**WCovBy.covBy_of_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WCovBy.covBy_of_ne (h : a ⩿ b) (h2 : a != b) : a ⋖ b
参数：h : a ⩿ b；h2 : a != b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用定理 `WCovBy.le`：WCovBy.le (h : a ⩿ b) : a <= b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem WCovBy.covBy_of_ne (h : a ⩿ b) (h2 : a ≠ b) : a ⋖ b :=
  ⟨h.le.lt_of_ne h2, h.2⟩

@[to_dual none]
/-
**covBy_iff_wcovBy_and_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：covBy_iff_wcovBy_and_ne : a ⋖ b ↔ a ⩿ b ∧ a != b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CovBy.wcovBy`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ⋖ b → a 
⩿ b
· 使用定理 `CovBy.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ⋖ b → a ≠ b
· 使用定理 `WCovBy.covBy_of_ne`：WCovBy.covBy_of_ne (h : a ⩿ b) (h2 : a != b) : a ⋖ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem covBy_iff_wcovBy_and_ne : a ⋖ b ↔ a ⩿ b ∧ a ≠ b :=
  ⟨fun h => ⟨h.wcovBy, h.ne⟩, fun h => h.1.covBy_of_ne h.2⟩

@[to_dual none]
/-
**wcovBy_iff_covBy_or_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：wcovBy_iff_covBy_or_eq : a ⩿ b ↔ a ⋖ b ∨ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `le_antisymm_iff`：le_antisymm_iff : a = b ↔ a <= b ∧ b <= a
· 使用定理 `wcovBy_iff_covBy_or_le_and_le`：wcovBy_iff_covBy_or_le_and_le : a ⩿ b ↔ a
 ⋖ b ∨ a <= b ∧ b <= a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem wcovBy_iff_covBy_or_eq : a ⩿ b ↔ a ⋖ b ∨ a = b := by
  rw [le_antisymm_iff, wcovBy_iff_covBy_or_le_and_le]

@[to_dual none]
/-
**wcovBy_iff_eq_or_covBy** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：wcovBy_iff_eq_or_covBy : a ⩿ b ↔ a = b ∨ a ⋖ b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `wcovBy_iff_covBy_or_eq`：wcovBy_iff_covBy_or_eq : a ⩿ b ↔ a ⋖ b ∨ a = b
· 使用定理 `or_comm`：∀ {a b : Prop}, a ∨ b ↔ b ∨ a
-/
theorem wcovBy_iff_eq_or_covBy : a ⩿ b ↔ a = b ∨ a ⋖ b :=
  wcovBy_iff_covBy_or_eq.trans or_comm

@[to_dual none]
alias ⟨WCovBy.covBy_or_eq, _⟩ := wcovBy_iff_covBy_or_eq

@[to_dual none]
alias ⟨WCovBy.eq_or_covBy, _⟩ := wcovBy_iff_eq_or_covBy

@[to_dual none]
/-
**CovBy.eq_or_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CovBy.eq_or_eq (h : a ⋖ b) (h2 : a <= c) (h3 : c <= b) : c = a ∨ c = b
参数：h : a ⋖ b；h2 : a <= c；h3 : c <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WCovBy.eq_or_eq`：WCovBy.eq_or_eq (h : a ⩿ b) (h2 : a <= c) (h3 : c <= b)
 : c = a ∨ c = b
· 使用定理 `CovBy.wcovBy`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ⋖ b → a 
⩿ b
-/
theorem CovBy.eq_or_eq (h : a ⋖ b) (h2 : a ≤ c) (h3 : c ≤ b) : c = a ∨ c = b :=
  h.wcovBy.eq_or_eq h2 h3

/-- An `iff` version of `CovBy.eq_or_eq` and `covBy_of_eq_or_eq`. -/
@[to_dual none]
/-
**covBy_iff_lt_and_eq_or_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：covBy_iff_lt_and_eq_or_eq : a ⋖ b ↔ a < b ∧ forall c, a <= c -> c <= b -> 
c = a ∨ c = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CovBy.lt`：CovBy.lt (h : a ⋖ b) : a < b
· 使用定理 `CovBy.eq_or_eq`：CovBy.eq_or_eq (h : a ⋖ b) (h2 : a <= c) (h3 : c <= b) :
 c = a ∨ c = b
· 使用定理 `covBy_of_eq_or_eq`：covBy_of_eq_or_eq (hab : a < b) (h : forall c, a <= c
 -> c <= b -> c = a ∨ c = b) : a ⋖ b

--- 原说明 ---
An `iff` version of `CovBy.eq_or_eq` and `covBy_of_eq_or_eq`.
-/
theorem covBy_iff_lt_and_eq_or_eq : a ⋖ b ↔ a < b ∧ ∀ c, a ≤ c → c ≤ b → c = a ∨ c = b :=
  ⟨fun h => ⟨h.lt, fun _ => h.eq_or_eq⟩, And.rec covBy_of_eq_or_eq⟩

@[to_dual]
/-
**CovBy.Ico_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CovBy.Ico_eq (h : a ⋖ b) : Ico a b = {a}
参数：h : a ⋖ b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Ioo_union_left`：Ioo_union_left (hab : a < b) : Ioo a b union {a} = I
co a b
· 使用定理 `CovBy.lt`：CovBy.lt (h : a ⋖ b) : a < b
· 使用定理 `CovBy.Ioo_eq`：CovBy.Ioo_eq (h : a ⋖ b) : Ioo a b = ∅
· 使用定理 `Set.empty_union`：empty_union (a : Set α) : ∅ union a = a
-/
theorem CovBy.Ico_eq (h : a ⋖ b) : Ico a b = {a} := by
  rw [← Ioo_union_left h.lt, h.Ioo_eq, empty_union]

@[to_dual none]
/-
**CovBy.Icc_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CovBy.Icc_eq (h : a ⋖ b) : Icc a b = {a, b}
参数：h : a ⋖ b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WCovBy.Icc_eq`：WCovBy.Icc_eq (h : a ⩿ b) : Icc a b = {a, b}
· 使用定理 `CovBy.wcovBy`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ⋖ b → a 
⩿ b
-/
theorem CovBy.Icc_eq (h : a ⋖ b) : Icc a b = {a, b} :=
  h.wcovBy.Icc_eq

@[to_dual]
/-
**Set.Ico_eq_singleton_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Ico_eq_singleton_iff : Ico a b = {c} ↔ a = c ∧ a ⋖ b where mp h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `CovBy.Ico_eq`：CovBy.Ico_eq (h : a ⋖ b) : Ico a b = {a}
-/
theorem Set.Ico_eq_singleton_iff : Ico a b = {c} ↔ a = c ∧ a ⋖ b where
  mp h := by
    simp_rw [Set.ext_iff, mem_Ico, mem_singleton_iff] at h
    have ⟨hac, hcb⟩ := (h c).mpr rfl
    obtain rfl := (h a).mp ⟨le_refl a, hac.trans_lt hcb⟩
    exact ⟨rfl, ⟨hcb, fun d hcd hdb ↦ hcd.ne ((h d).mp ⟨hcd.le, hdb⟩).symm⟩⟩
  mpr := fun ⟨rfl, hcov⟩ ↦ hcov.Ico_eq

@[to_dual Ioc_eq_singleton_right_iff]
/-
**Set.Ico_eq_singleton_left_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Set.Ico_eq_singleton_left_iff : Ico a b = {a} ↔ a ⋖ b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma Set.Ico_eq_singleton_left_iff : Ico a b = {a} ↔ a ⋖ b := by
  simp [Ico_eq_singleton_iff]

end PartialOrder

section LinearOrder

variable [LinearOrder α] {a b c : α}

@[to_dual ge_of_gt]
/-
**WCovBy.le_of_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WCovBy.le_of_lt (hab : a ⩿ b) (hcb : c < b) : c <= a
参数：hab : a ⩿ b；hcb : c < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem WCovBy.le_of_lt (hab : a ⩿ b) (hcb : c < b) : c ≤ a :=
  not_lt.1 fun hac => hab.2 hac hcb

@[to_dual ge_of_gt]
/-
**CovBy.le_of_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CovBy.le_of_lt (hab : a ⋖ b) : c < b -> c <= a
参数：hab : a ⋖ b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WCovBy.le_of_lt`：WCovBy.le_of_lt (hab : a ⩿ b) (hcb : c < b) : c <= a
· 使用定理 `CovBy.wcovBy`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ⋖ b → a 
⩿ b
-/
theorem CovBy.le_of_lt (hab : a ⋖ b) : c < b → c ≤ a :=
  hab.wcovBy.le_of_lt
/-
**CovBy.Ioi_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CovBy.Ioi_eq (h : a ⋖ b) : Ioi a = Ici b
参数：h : a ⋖ b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Ioo_union_Ici_eq_Ioi`：Ioo_union_Ici_eq_Ioi (h : a < b) : Ioo a b uni
on Ici b = Ioi a
· 使用定理 `CovBy.lt`：CovBy.lt (h : a ⋖ b) : a < b
· 使用定理 `CovBy.Ioo_eq`：CovBy.Ioo_eq (h : a ⋖ b) : Ioo a b = ∅
· 使用定理 `Set.empty_union`：empty_union (a : Set α) : ∅ union a = a
-/
theorem CovBy.Ioi_eq (h : a ⋖ b) : Ioi a = Ici b := by
  rw [← Ioo_union_Ici_eq_Ioi h.lt, h.Ioo_eq, empty_union]

@[to_dual existing]
/-
**CovBy.Iio_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CovBy.Iio_eq (h : a ⋖ b) : Iio b = Iic a
参数：h : a ⋖ b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Iic_union_Ioo_eq_Iio`：Iic_union_Ioo_eq_Iio (h : a < b) : Iic a union
 Ioo a b = Iio b
· 使用定理 `CovBy.lt`：CovBy.lt (h : a ⋖ b) : a < b
· 使用定理 `CovBy.Ioo_eq`：CovBy.Ioo_eq (h : a ⋖ b) : Ioo a b = ∅
· 使用定理 `Set.union_empty`：union_empty (a : Set α) : a union ∅ = a
-/
theorem CovBy.Iio_eq (h : a ⋖ b) : Iio b = Iic a := by
  rw [← Iic_union_Ioo_eq_Iio h.lt, h.Ioo_eq, union_empty]

@[to_dual]
/-
**CovBy.Ioo_eq_Ico** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CovBy.Ioo_eq_Ico (h : a ⋖ b) (c : α) : Ioo a c = Ico b c
参数：h : a ⋖ b；c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `CovBy.ge_of_gt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, b ⋖
 a → b < c → a ≤ c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.Ico_subset_Ioo_left`：Ico_subset_Ioo_left (h : a₁ < a₂) : Ico a₂ b su
bseteq Ioo a₁ b
· 使用定理 `CovBy.lt`：CovBy.lt (h : a ⋖ b) : a < b
-/
theorem CovBy.Ioo_eq_Ico (h : a ⋖ b) (c : α) : Ioo a c = Ico b c :=
  subset_antisymm (fun _x hx ↦ ⟨h.ge_of_gt hx.1, hx.2⟩) <| Ico_subset_Ioo_left h.lt

@[to_dual none]
/-
**Set.Ioo_eq_singleton_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Ioo_eq_singleton_iff : Ioo a b = {c} ↔ a ⋖ c ∧ c ⋖ b where mp h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Ioc_union_Ico_eq_Ioo`：Ioc_union_Ico_eq_Ioo (h₁ : a < b) (h₂ : b < c)
 : Ioc a b union Ico b c = Ioo a c
· 使用定理 `CovBy.lt`：CovBy.lt (h : a ⋖ b) : a < b
· 使用定理 `CovBy.Ioc_eq`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ⋖ a 
→ Set.Ioc b a = {a}
· 使用定理 `CovBy.Ico_eq`：CovBy.Ico_eq (h : a ⋖ b) : Ico a b = {a}
· 使用定理 `Set.union_self`：union_self (a : Set α) : a union a = a
-/
theorem Set.Ioo_eq_singleton_iff : Ioo a b = {c} ↔ a ⋖ c ∧ c ⋖ b where
  mp h := by
    simp_rw [Set.ext_iff, mem_Ioo, mem_singleton_iff] at h
    have ⟨hac, hcb⟩ := (h c).mpr rfl
    exact ⟨⟨hac, fun d had hdc ↦ hdc.ne ((h d).mp ⟨had, hdc.trans hcb⟩)⟩,
      ⟨hcb, fun d hcd hdb ↦ hcd.ne ((h d).mp ⟨hac.trans hcd, hdb⟩).symm⟩⟩
  mpr := fun ⟨hac, hcb⟩ ↦ by
    rw [← Ioc_union_Ico_eq_Ioo hac.lt hcb.lt, hac.Ioc_eq, hcb.Ico_eq, union_self]

@[to_dual]
/-
**Set.Ioi_eq_singleton_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Ioi_eq_singleton_iff : Ioi a = {b} ↔ IsTop b ∧ a ⋖ b where mp h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `isTop_top`：isTop_top : IsTop (⊤ : α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Ioc_top`：Ioc_top : Ioc a ⊤ = Ioi a
· 使用定理 `Set.Ioc_eq_singleton_right_iff`：∀ {α : Type u_1} [inst : PartialOrder α]
 {a b : α}, Set.Ioc b a = {a} ↔ b ⋖ a
-/
theorem Set.Ioi_eq_singleton_iff : Ioi a = {b} ↔ IsTop b ∧ a ⋖ b where
  mp h := by
    simp_rw [Set.ext_iff, mem_Ioi, mem_singleton_iff] at h
    have hb : a < b := (h b).mpr rfl
    exact ⟨fun c ↦ not_lt.mp fun hc ↦ hc.ne.symm ((h c).mp (hb.trans hc)),
      ⟨hb, fun c hac hcb ↦ hcb.ne ((h c).mp hac)⟩⟩
  mpr := fun ⟨hb, hab⟩ ↦ by
    cases b, hb using IsTop.rec; rwa [← Ioc_top, Ioc_eq_singleton_right_iff]

@[to_dual unique_right]
/-
**CovBy.unique_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CovBy.unique_left (ha : a ⋖ c) (hb : b ⋖ c) : a = b
参数：ha : a ⋖ c；hb : b ⋖ c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `CovBy.le_of_lt`：CovBy.le_of_lt (hab : a ⋖ b) : c < b -> c <= a
· 使用定理 `CovBy.lt`：CovBy.lt (h : a ⋖ b) : a < b
-/
theorem CovBy.unique_left (ha : a ⋖ c) (hb : b ⋖ c) : a = b :=
  (hb.le_of_lt ha.lt).antisymm <| ha.le_of_lt hb.lt

/-- If `a`, `b`, `c` are consecutive and `a < x < c` then `x = b`. -/
@[to_dual self (reorder := a c, hab hbc, hax hxc)]
/-
**CovBy.eq_of_between** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CovBy.eq_of_between {x : α} (hab : a ⋖ b) (hbc : b ⋖ c) (hax : a < x) (hxc
 : x < c) : x = b
参数：hab : a ⋖ b；hbc : b ⋖ c；hax : a < x；hxc : x < c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
If `a`, `b`, `c` are consecutive and `a < x < c` then `x = b`.
-/
theorem CovBy.eq_of_between {x : α} (hab : a ⋖ b) (hbc : b ⋖ c) (hax : a < x) (hxc : x < c) :
    x = b :=
  le_antisymm (le_of_not_gt fun h => hbc.2 h hxc) (le_of_not_gt <| hab.2 hax)

@[to_dual covBy_iff_lt_iff_le_right]
/-
**covBy_iff_lt_iff_le_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：covBy_iff_lt_iff_le_left {x y : α} : x ⋖ y ↔ forall {z}, z < y ↔ z <= x wh
ere mp
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CovBy.le_of_lt`：CovBy.le_of_lt (hab : a ⋖ b) : c < b -> c <= a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `CovBy.lt`：CovBy.lt (h : a ⋖ b) : a < b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem covBy_iff_lt_iff_le_left {x y : α} : x ⋖ y ↔ ∀ {z}, z < y ↔ z ≤ x where
  mp := fun hx _z ↦ ⟨hx.le_of_lt, fun hz ↦ hz.trans_lt hx.lt⟩
  mpr := fun H ↦ ⟨H.2 le_rfl, fun _z hx hz ↦ (H.1 hz).not_gt hx⟩

@[to_dual covBy_iff_le_iff_lt_right]
/-
**covBy_iff_le_iff_lt_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：covBy_iff_le_iff_lt_left {x y : α} : x ⋖ y ↔ forall {z}, z <= x ↔ z < y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem covBy_iff_le_iff_lt_left {x y : α} : x ⋖ y ↔ ∀ {z}, z ≤ x ↔ z < y := by
  simp_rw [covBy_iff_lt_iff_le_left, iff_comm]

@[to_dual lt_iff_le_right]
alias ⟨CovBy.lt_iff_le_left, _⟩ := covBy_iff_lt_iff_le_left

@[to_dual le_iff_lt_right]
alias ⟨CovBy.le_iff_lt_left, _⟩ := covBy_iff_le_iff_lt_left

/-- If `a < b` then there exist `a' > a` and `b' < b` such that `Set.Iio a'` is strictly to the left
of `Set.Ioi b'`. -/
@[to_dual none]
/-
**LT.lt.exists_disjoint_Iio_Ioi** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LT.lt.exists_disjoint_Iio_Ioi (h : a < b) : exists a' > a, exists b' < b, 
forall x < a', forall y > b', x < y
参数：h : a < b。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `a < b` then there exist `a' > a` and `b' < b` such that `Set.Iio a'` is stri
ctly to the left
of `Set.Ioi b'`.
-/
lemma LT.lt.exists_disjoint_Iio_Ioi (h : a < b) :
    ∃ a' > a, ∃ b' < b, ∀ x < a', ∀ y > b', x < y := by
  grind

end LinearOrder

namespace Bool

/-
**Bool.wcovBy_iff** 是 Mathlib 中的一个定理，位于命名空间 `Bool`。
形式化陈述：∀ {a b : Bool}, a ⩿ b ↔ a ≤ b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
@[simp] theorem wcovBy_iff : ∀ {a b : Bool}, a ⩿ b ↔ a ≤ b := by unfold WCovBy; decide
/-
**Bool.covBy_iff** 是 Mathlib 中的一个定理，位于命名空间 `Bool`。
形式化陈述：∀ {a b : Bool}, a ⋖ b ↔ a < b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
@[simp] theorem covBy_iff : ∀ {a b : Bool}, a ⋖ b ↔ a < b := by unfold CovBy; decide
/-
**Bool.instDecidableRelWCovBy** 是 Mathlib 中的一个实例，位于命名空间 `Bool`。
形式化陈述：instDecidableRelWCovBy : DecidableRel (· ⩿ · : Bool -> Bool -> Prop)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDecidableRelWCovBy : DecidableRel (· ⩿ · : Bool → Bool → Prop) := fun _ _ ↦
  decidable_of_iff _ wcovBy_iff.symm
/-
**Bool.instDecidableRelCovBy** 是 Mathlib 中的一个实例，位于命名空间 `Bool`。
形式化陈述：instDecidableRelCovBy : DecidableRel (· ⋖ · : Bool -> Bool -> Prop)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDecidableRelCovBy : DecidableRel (· ⋖ · : Bool → Bool → Prop) := fun _ _ ↦
  decidable_of_iff _ covBy_iff.symm

end Bool

namespace Set
variable {s t : Set α} {a : α}

/-
**Set.wcovBy_insert** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} (x : α) (s : Set α), s ⩿ insert x s
参数：x : α；s : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `wcovBy_of_eq_or_eq`：wcovBy_of_eq_or_eq (hab : a <= b) (h : forall c, a <
= c -> c <= b -> c = a ∨ c = b) : a ⩿ b
· 使用定理 `Set.subset_insert`：subset_insert (x : α) (s : Set α) : s subseteq insert
 x s
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.insert_subset_iff`：insert_subset_iff : insert a s subseteq t ↔ a in 
t ∧ s subseteq t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.sdiff_singleton_eq_self`：sdiff_singleton_eq_self (h : a ∉ s) : s \ {
a} = s
· 使用引理 `Set.sdiff_singleton_subset_iff`：sdiff_singleton_subset_iff : s \ {a} sub
seteq t ↔ s subseteq insert a t
-/
@[simp] lemma wcovBy_insert (x : α) (s : Set α) : s ⩿ insert x s := by
  refine wcovBy_of_eq_or_eq (subset_insert x s) fun t hst h2t => ?_
  by_cases h : x ∈ t
  · exact Or.inr (subset_antisymm h2t <| insert_subset_iff.mpr ⟨h, hst⟩)
  · refine Or.inl (subset_antisymm ?_ hst)
    rwa [← sdiff_singleton_eq_self h, sdiff_singleton_subset_iff]
/-
**Set.sdiff_singleton_wcovBy** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} (s : Set α) (a : α), s \ {a} ⩿ s
参数：s : Set α；a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.insert_sdiff_self_of_mem`：∀ {α : Type u_1} {s : Set α} {a : α}, a ∈ 
s → insert a (s \ {a}) = s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Set.wcovBy_insert`：∀ {α : Type u_1} (x : α) (s : Set α), s ⩿ insert x s
· 使用引理 `Set.sdiff_singleton_eq_self`：sdiff_singleton_eq_self (h : a ∉ s) : s \ {
a} = s
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
@[simp] lemma sdiff_singleton_wcovBy (s : Set α) (a : α) : s \ {a} ⩿ s := by
  by_cases ha : a ∈ s
  · convert! wcovBy_insert a _
    ext
    simp [ha]
  · simp [ha]
/-
**Set.covBy_insert** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} {s : Set α} {a : α}, a ∉ s → s ⋖ insert a s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WCovBy.covBy_of_lt`：WCovBy.covBy_of_lt (h : a ⩿ b) (h2 : a < b) : a ⋖ b
· 使用定理 `Set.wcovBy_insert`：∀ {α : Type u_1} (x : α) (s : Set α), s ⩿ insert x s
· 使用定理 `Set.ssubset_insert`：ssubset_insert {s : Set α} {a : α} (h : a ∉ s) : s ⊂
 insert a s
-/
@[simp] lemma covBy_insert (ha : a ∉ s) : s ⋖ insert a s :=
  (wcovBy_insert _ _).covBy_of_lt <| ssubset_insert ha
/-
**Set.empty_covBy_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} (a : α), ∅ ⋖ {a}
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.covBy_insert`：∀ {α : Type u_1} {s : Set α} {a : α}, a ∉ s → s ⋖ inse
rt a s
· 使用定理 `LawfulSingleton.insert_empty_eq`：∀ {α : Type u} {β : Type v} {inst : Emp
tyCollection β} {inst_1 : Insert α β} {inst_2 : Singleton α β}   [self : LawfulS
ingleton α β] (x : α)…
· 使用定理 `Set.instLawfulSingleton`：∀ {α : Type u_1}, LawfulSingleton α (Set α)
· 使用定理 `Set.notMem_empty`：notMem_empty (x : α) : x ∉ (∅ : Set α)
-/
@[simp] lemma empty_covBy_singleton (a : α) : ∅ ⋖ ({a} : Set α) :=
  insert_empty_eq (β := Set α) a ▸ covBy_insert <| notMem_empty a
/-
**Set.sdiff_singleton_covBy** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} {s : Set α} {a : α}, a ∈ s → s \ {a} ⋖ s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sdiff_lt`：sdiff_lt (hx : y <= x) (hy : y != ⊥) : x \ y < x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `Set.singleton_ne_empty`：singleton_ne_empty (a : α) : ({a} : Set α) != ∅
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.sdiff_singleton_wcovBy`：∀ {α : Type u_1} (s : Set α) (a : α), s \ {a
} ⩿ s
-/
@[simp] lemma sdiff_singleton_covBy (ha : a ∈ s) : s \ {a} ⋖ s :=
  ⟨sdiff_lt (singleton_subset_iff.2 ha) <| singleton_ne_empty _, (sdiff_singleton_wcovBy _ _).2⟩
/-
**Set._root_.CovBy.exists_set_insert** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.CovBy.exists_set_insert (h : s ⋖ t) : ∃ a ∉ s, insert a s = t :=
  let ⟨a, ha, hst⟩ := ssubset_iff_insert.1 h.lt
  ⟨a, ha, (hst.eq_of_not_ssuperset <| h.2 <| ssubset_insert ha).symm⟩
/-
**Set._root_.CovBy.exists_set_sdiff_singleton** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.CovBy.exists_set_sdiff_singleton (h : s ⋖ t) : ∃ a ∈ t, t \ {a} = s :=
  let ⟨a, ha, hst⟩ := ssubset_iff_sdiff_singleton.1 h.lt
  ⟨a, ha, (hst.eq_of_not_ssubset fun h' ↦ h.2 h' <|
    sdiff_lt (singleton_subset_iff.2 ha) <| singleton_ne_empty _).symm⟩
/-
**Set.covBy_iff_exists_insert** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：covBy_iff_exists_insert : s ⋖ t ↔ exists a ∉ s, insert a s = t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CovBy.exists_set_insert`：∀ {α : Type u_1} {s t : Set α}, s ⋖ t → ∃ a ∉ s
, insert a s = t
· 使用定理 `Set.covBy_insert`：∀ {α : Type u_1} {s : Set α} {a : α}, a ∉ s → s ⋖ inse
rt a s
-/
lemma covBy_iff_exists_insert : s ⋖ t ↔ ∃ a ∉ s, insert a s = t :=
  ⟨CovBy.exists_set_insert, by rintro ⟨a, ha, rfl⟩; exact covBy_insert ha⟩
/-
**Set.covBy_iff_exists_sdiff_singleton** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：covBy_iff_exists_sdiff_singleton : s ⋖ t ↔ exists a in t, t \ {a} = s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CovBy.exists_set_sdiff_singleton`：∀ {α : Type u_1} {s t : Set α}, s ⋖ t 
→ ∃ a ∈ t, t \ {a} = s
· 使用定理 `Set.sdiff_singleton_covBy`：∀ {α : Type u_1} {s : Set α} {a : α}, a ∈ s →
 s \ {a} ⋖ s
-/
lemma covBy_iff_exists_sdiff_singleton : s ⋖ t ↔ ∃ a ∈ t, t \ {a} = s :=
  ⟨CovBy.exists_set_sdiff_singleton, by rintro ⟨a, ha, rfl⟩; exact sdiff_singleton_covBy ha⟩

end Set

section Relation

open Relation

/-
**wcovBy_eq_reflGen_covBy** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：wcovBy_eq_reflGen_covBy [PartialOrder α] : (· ⩿ · : α -> α -> Prop) = Refl
Gen (· ⋖ ·)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma wcovBy_eq_reflGen_covBy [PartialOrder α] : (· ⩿ · : α → α → Prop) = ReflGen (· ⋖ ·) := by
  ext x y; simp_rw [wcovBy_iff_eq_or_covBy, @eq_comm _ x, reflGen_iff]
/-
**transGen_wcovBy_eq_reflTransGen_covBy** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：transGen_wcovBy_eq_reflTransGen_covBy [PartialOrder α] : TransGen (· ⩿ · :
 α -> α -> Prop) = ReflTransGen (· ⋖ ·)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `wcovBy_eq_reflGen_covBy`：wcovBy_eq_reflGen_covBy [PartialOrder α] : (· ⩿
 · : α -> α -> Prop) = ReflGen (· ⋖ ·)
· 使用定理 `Relation.transGen_reflGen`：∀ {α : Type u_1} {r : α → α → Prop}, Relation
.TransGen (Relation.ReflGen r) = Relation.ReflTransGen r
-/
lemma transGen_wcovBy_eq_reflTransGen_covBy [PartialOrder α] :
    TransGen (· ⩿ · : α → α → Prop) = ReflTransGen (· ⋖ ·) := by
  rw [wcovBy_eq_reflGen_covBy, transGen_reflGen]
/-
**reflTransGen_wcovBy_eq_reflTransGen_covBy** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：reflTransGen_wcovBy_eq_reflTransGen_covBy [PartialOrder α] : ReflTransGen 
(· ⩿ · : α -> α -> Prop) = ReflTransGen (· ⋖ ·)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `wcovBy_eq_reflGen_covBy`：wcovBy_eq_reflGen_covBy [PartialOrder α] : (· ⩿
 · : α -> α -> Prop) = ReflGen (· ⋖ ·)
· 使用定理 `Relation.reflTransGen_reflGen`：∀ {α : Type u_1} {r : α → α → Prop}, Rela
tion.ReflTransGen (Relation.ReflGen r) = Relation.ReflTransGen r
-/
lemma reflTransGen_wcovBy_eq_reflTransGen_covBy [PartialOrder α] :
    ReflTransGen (· ⩿ · : α → α → Prop) = ReflTransGen (· ⋖ ·) := by
  rw [wcovBy_eq_reflGen_covBy, reflTransGen_reflGen]

end Relation

namespace Prod

variable [PartialOrder α] [PartialOrder β] {a a₁ a₂ : α} {b b₁ b₂ : β} {x y : α × β}

@[to_dual self, simp]
/-
**Prod.swap_wcovBy_swap** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：swap_wcovBy_swap : x.swap ⩿ y.swap ↔ x ⩿ y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `apply_wcovBy_apply_iff`：apply_wcovBy_apply_iff {E : Type*} [EquivLike E 
α β] [OrderIsoClass E α β] (e : E) : e a ⩿ e b ↔ a ⩿ b
· 使用定理 `OrderIso.instOrderIsoClass`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α
] [inst_1 : LE β], OrderIsoClass (α ≃o β) α β
-/
theorem swap_wcovBy_swap : x.swap ⩿ y.swap ↔ x ⩿ y :=
  apply_wcovBy_apply_iff (OrderIso.prodComm : α × β ≃o β × α)

@[to_dual self, simp]
/-
**Prod.swap_covBy_swap** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：swap_covBy_swap : x.swap ⋖ y.swap ↔ x ⋖ y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `apply_covBy_apply_iff`：apply_covBy_apply_iff {E : Type*} [EquivLike E α 
β] [OrderIsoClass E α β] (e : E) : e a ⋖ e b ↔ a ⋖ b
· 使用定理 `OrderIso.instOrderIsoClass`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α
] [inst_1 : LE β], OrderIsoClass (α ≃o β) α β
-/
theorem swap_covBy_swap : x.swap ⋖ y.swap ↔ x ⋖ y :=
  apply_covBy_apply_iff (OrderIso.prodComm : α × β ≃o β × α)

@[to_dual none]
/-
**Prod.fst_eq_or_snd_eq_of_wcovBy** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：fst_eq_or_snd_eq_of_wcovBy : x ⩿ y -> x.1 = y.1 ∨ x.2 = y.2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Prod.mk_lt_mk`：mk_lt_mk : (a₁, b₁) < (a₂, b₂) ↔ a₁ < a₂ ∧ b₁ <= b₂ ∨ a₁ 
<= a₂ ∧ b₁ < b₂
· 使用定理 `Ne.lt_of_le`：Ne.lt_of_le : a != b -> a <= b -> a < b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem fst_eq_or_snd_eq_of_wcovBy : x ⩿ y → x.1 = y.1 ∨ x.2 = y.2 := by
  intro h
  by_contra! ⟨ha, hb⟩
  exact
    h.2 (mk_lt_mk.2 <| Or.inl ⟨ha.lt_of_le h.1.1, le_rfl⟩)
      (mk_lt_mk.2 <| Or.inr ⟨le_rfl, hb.lt_of_le h.1.2⟩)

@[to_dual self]
/-
**Prod._root_.WCovBy.fst** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.WCovBy.fst (h : x ⩿ y) : x.1 ⩿ y.1 :=
  ⟨h.1.1, fun _ h₁ h₂ => h.2 (mk_lt_mk_iff_left.2 h₁) ⟨⟨h₂.le, h.1.2⟩, fun hc => h₂.not_ge hc.1⟩⟩

@[to_dual self]
/-
**Prod._root_.WCovBy.snd** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.WCovBy.snd (h : x ⩿ y) : x.2 ⩿ y.2 :=
  ⟨h.1.2, fun _ h₁ h₂ => h.2 (mk_lt_mk_iff_right.2 h₁) ⟨⟨h.1.1, h₂.le⟩, fun hc => h₂.not_ge hc.2⟩⟩

@[to_dual self]
/-
**Prod.mk_wcovBy_mk_iff_left** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：mk_wcovBy_mk_iff_left : (a₁, b) ⩿ (a₂, b) ↔ a₁ ⩿ a₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WCovBy.fst`：∀ {α : Type u_1} {β : Type u_2} [inst : PartialOrder α] [ins
t_1 : PartialOrder β] {x y : α × β}, x ⩿ y → x.1 ⩿ y.1
· 使用定理 `And.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∧ b → c ∧ d
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Prod.mk_le_mk_iff_left`：mk_le_mk_iff_left : (a₁, b) <= (a₂, b) ↔ a₁ <= a
₂
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Prod.mk_lt_mk_iff_left`：mk_lt_mk_iff_left : (a₁, b) < (a₂, b) ↔ a₁ < a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Prod.mk.eta`：∀ {α : Type u_1} {β : Type u_2} {p : α × β}, (p.1, p.2) = p
-/
theorem mk_wcovBy_mk_iff_left : (a₁, b) ⩿ (a₂, b) ↔ a₁ ⩿ a₂ := by
  refine ⟨WCovBy.fst, (And.imp mk_le_mk_iff_left.2) fun h c h₁ h₂ => ?_⟩
  have : c.2 = b := h₂.le.2.antisymm h₁.le.2
  rw [← @Prod.mk.eta _ _ c, this, mk_lt_mk_iff_left] at h₁ h₂
  exact h h₁ h₂

@[to_dual self]
/-
**Prod.mk_wcovBy_mk_iff_right** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：mk_wcovBy_mk_iff_right : (a, b₁) ⩿ (a, b₂) ↔ b₁ ⩿ b₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Prod.swap_wcovBy_swap`：swap_wcovBy_swap : x.swap ⩿ y.swap ↔ x ⩿ y
· 使用定理 `Prod.mk_wcovBy_mk_iff_left`：mk_wcovBy_mk_iff_left : (a₁, b) ⩿ (a₂, b) ↔ 
a₁ ⩿ a₂
-/
theorem mk_wcovBy_mk_iff_right : (a, b₁) ⩿ (a, b₂) ↔ b₁ ⩿ b₂ :=
  swap_wcovBy_swap.trans mk_wcovBy_mk_iff_left

@[to_dual self]
/-
**Prod.mk_covBy_mk_iff_left** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：mk_covBy_mk_iff_left : (a₁, b) ⋖ (a₂, b) ↔ a₁ ⋖ a₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mk_covBy_mk_iff_left : (a₁, b) ⋖ (a₂, b) ↔ a₁ ⋖ a₂ := by
  simp_rw [covBy_iff_wcovBy_and_lt, mk_wcovBy_mk_iff_left, mk_lt_mk_iff_left]

@[to_dual self]
/-
**Prod.mk_covBy_mk_iff_right** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：mk_covBy_mk_iff_right : (a, b₁) ⋖ (a, b₂) ↔ b₁ ⋖ b₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mk_covBy_mk_iff_right : (a, b₁) ⋖ (a, b₂) ↔ b₁ ⋖ b₂ := by
  simp_rw [covBy_iff_wcovBy_and_lt, mk_wcovBy_mk_iff_right, mk_lt_mk_iff_right]

@[to_dual none]
/-
**Prod.mk_wcovBy_mk_iff** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：mk_wcovBy_mk_iff : (a₁, b₁) ⩿ (a₂, b₂) ↔ a₁ ⩿ a₂ ∧ b₁ = b₂ ∨ b₁ ⩿ b₂ ∧ a₁ 
= a₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.fst_eq_or_snd_eq_of_wcovBy`：fst_eq_or_snd_eq_of_wcovBy : x ⩿ y -> x
.1 = y.1 ∨ x.2 = y.2
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Prod.mk_wcovBy_mk_iff_right`：mk_wcovBy_mk_iff_right : (a, b₁) ⩿ (a, b₂) 
↔ b₁ ⩿ b₂
· 使用定理 `Prod.mk_wcovBy_mk_iff_left`：mk_wcovBy_mk_iff_left : (a₁, b) ⩿ (a₂, b) ↔ 
a₁ ⩿ a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
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
/-
**Prod.mk_covBy_mk_iff** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：mk_covBy_mk_iff : (a₁, b₁) ⋖ (a₂, b₂) ↔ a₁ ⋖ a₂ ∧ b₁ = b₂ ∨ b₁ ⋖ b₂ ∧ a₁ =
 a₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.fst_eq_or_snd_eq_of_wcovBy`：fst_eq_or_snd_eq_of_wcovBy : x ⩿ y -> x
.1 = y.1 ∨ x.2 = y.2
· 使用定理 `CovBy.wcovBy`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ⋖ b → a 
⩿ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Prod.mk_covBy_mk_iff_right`：mk_covBy_mk_iff_right : (a, b₁) ⋖ (a, b₂) ↔ 
b₁ ⋖ b₂
· 使用定理 `Prod.mk_covBy_mk_iff_left`：mk_covBy_mk_iff_left : (a₁, b) ⋖ (a₂, b) ↔ a₁
 ⋖ a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
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
/-
**Prod.wcovBy_iff** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：wcovBy_iff : x ⩿ y ↔ x.1 ⩿ y.1 ∧ x.2 = y.2 ∨ x.2 ⩿ y.2 ∧ x.1 = y.1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.mk_wcovBy_mk_iff`：mk_wcovBy_mk_iff : (a₁, b₁) ⩿ (a₂, b₂) ↔ a₁ ⩿ a₂ 
∧ b₁ = b₂ ∨ b₁ ⩿ b₂ ∧ a₁ = a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem wcovBy_iff : x ⩿ y ↔ x.1 ⩿ y.1 ∧ x.2 = y.2 ∨ x.2 ⩿ y.2 ∧ x.1 = y.1 := by
  cases x
  cases y
  exact mk_wcovBy_mk_iff

@[to_dual none]
/-
**Prod.covBy_iff** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：covBy_iff : x ⋖ y ↔ x.1 ⋖ y.1 ∧ x.2 = y.2 ∨ x.2 ⋖ y.2 ∧ x.1 = y.1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.mk_covBy_mk_iff`：mk_covBy_mk_iff : (a₁, b₁) ⋖ (a₂, b₂) ↔ a₁ ⋖ a₂ ∧ 
b₁ = b₂ ∨ b₁ ⋖ b₂ ∧ a₁ = a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem covBy_iff : x ⋖ y ↔ x.1 ⋖ y.1 ∧ x.2 = y.2 ∨ x.2 ⋖ y.2 ∧ x.1 = y.1 := by
  cases x
  cases y
  exact mk_covBy_mk_iff

end Prod

namespace Pi

section Preorder

variable {ι : Type*} {α : ι → Type*} [∀ i, Preorder (α i)] {a b : (i : ι) → α i}

@[to_dual self]
/-
**Pi._root_.WCovBy.eval** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.WCovBy.eval (h : a ⩿ b) (i : ι) : a i ⩿ b i := by
  classical
  refine ⟨h.1 i, fun ci h₁ h₂ ↦ ?_⟩
  have hcb : Function.update a i ci ≤ b := by simpa [update_le_iff, h₂.le] using fun j hj ↦ h.1 j
  refine h.2 (by simpa) (lt_of_le_not_ge hcb ?_)
  simp [le_update_iff, h₂.not_ge]
/-
**Pi.exists_forall_antisymmRel_of_covBy** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：exists_forall_antisymmRel_of_covBy (h : a ⋖ b) : exists i, forall j != i, 
AntisymmRel (· <= ·) (a j) (b j)
参数：h : a ⋖ b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma exists_forall_antisymmRel_of_covBy (h : a ⋖ b) :
    ∃ i, ∀ j ≠ i, AntisymmRel (· ≤ ·) (a j) (b j) := by
  classical
  simp only [CovBy, Pi.lt_def, not_and, and_imp, forall_exists_index, not_exists] at h
  obtain ⟨⟨hab, ⟨i, hi⟩⟩, h⟩ := h
  refine ⟨i, fun j hj ↦ ?_⟩
  let c : (i : ι) → α i := Function.update a i (b i)
  have h₁ : c ≤ b := by simpa [update_le_iff, c] using fun k hk ↦ hab k
  have h₂ : ¬ c j < b j := h (by simp [c, hi.le]) i (by simpa [c]) h₁ j
  exact ⟨hab j, by simpa [lt_iff_le_not_ge, hab j, c, hj] using h₂⟩
/-
**Pi.exists_forall_antisymmRel_of_wcovBy** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：exists_forall_antisymmRel_of_wcovBy [Nonempty ι] (h : a ⩿ b) : exists i, f
orall j != i, AntisymmRel (· <= ·) (a j) (b j)
参数：h : a ⩿ b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `wcovBy_iff_covBy_or_le_and_le`：wcovBy_iff_covBy_or_le_and_le : a ⩿ b ↔ a
 ⋖ b ∨ a <= b ∧ b <= a
· 使用引理 `Pi.exists_forall_antisymmRel_of_covBy`：exists_forall_antisymmRel_of_covB
y (h : a ⋖ b) : exists i, forall j != i, AntisymmRel (· <= ·) (a j) (b j)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma exists_forall_antisymmRel_of_wcovBy [Nonempty ι] (h : a ⩿ b) :
    ∃ i, ∀ j ≠ i, AntisymmRel (· ≤ ·) (a j) (b j) := by
  rw [wcovBy_iff_covBy_or_le_and_le] at h
  obtain h | h := h
  · exact exists_forall_antisymmRel_of_covBy h
  · inhabit ι
    exact ⟨default, fun j hj ↦ ⟨h.left j, h.right j⟩⟩

/--
A characterisation of the `WCovBy` relation in products of preorders. See `Pi.wcovBy_iff` for the
(more common) version in products of partial orders.
-/
/-
**Pi.wcovBy_iff_antisymmRel** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：wcovBy_iff_antisymmRel [Nonempty ι] : a ⩿ b ↔ exists i, a i ⩿ b i ∧ forall
 j != i, AntisymmRel (· <= ·) (a j) (b j)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Pi.exists_forall_antisymmRel_of_wcovBy`：exists_forall_antisymmRel_of_wco
vBy [Nonempty ι] (h : a ⩿ b) : exists i, forall j != i, AntisymmRel (· <= ·) (a 
j) (b j)
· 使用定理 `WCovBy.eval`：∀ {ι : Type u_3} {α : ι → Type u_4} [inst : (i : ι) → Preor
der (α i)] {a b : (i : ι) → α i},   a ⩿ b → ∀ (i : ι), a i ⩿ b i
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Pi.lt_def`：Pi.lt_def [forall i, Preorder (π i)] {x y : forall i, π i} : 
x < y ↔ x <= y ∧ exists i, x i < y i
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `lt_of_antisymmRel_of_lt`：lt_of_antisymmRel_of_lt (h₁ : AntisymmRel (· <=
 ·) a b) (h₂ : b < c) : a < c
· 使用定理 `AntisymmRel.symm`：AntisymmRel.symm : AntisymmRel r a b -> AntisymmRel r 
b a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `lt_of_lt_of_antisymmRel`：lt_of_lt_of_antisymmRel (h₁ : a < b) (h₂ : Anti
symmRel (· <= ·) b c) : a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
A characterisation of the `WCovBy` relation in products of preorders. See `Pi.wc
ovBy_iff` for the
(more common) version in products of partial orders.
-/
lemma wcovBy_iff_antisymmRel [Nonempty ι] :
    a ⩿ b ↔ ∃ i, a i ⩿ b i ∧ ∀ j ≠ i, AntisymmRel (· ≤ ·) (a j) (b j) := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := exists_forall_antisymmRel_of_wcovBy h
    exact ⟨i, h.eval _, hi⟩
  rintro ⟨i, hab, h⟩
  refine ⟨fun j ↦ (eq_or_ne j i).elim (· ▸ hab.1) (h j · |>.1), fun c hac hcb ↦ ?_⟩
  have haci : a i < c i := by
    obtain ⟨hac, j, hj⟩ := Pi.lt_def.1 hac
    exact (eq_or_ne j i).elim (· ▸ hj) fun hj' ↦
      ((lt_of_antisymmRel_of_lt (h j hj').symm hj).not_ge (hcb.le j)).elim
  have hcbi : c i < b i := by
    obtain ⟨hcb, j, hj⟩ := Pi.lt_def.1 hcb
    exact (eq_or_ne j i).elim (· ▸ hj) fun hj' ↦
      ((lt_of_lt_of_antisymmRel hj (h j hj').symm).not_ge (hac.le j)).elim
  exact hab.2 haci hcbi

/--
A characterisation of the `CovBy` relation in products of preorders. See `Pi.covBy_iff` for the
(more common) version in products of partial orders.
-/
/-
**Pi.covBy_iff_antisymmRel** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：covBy_iff_antisymmRel : a ⋖ b ↔ exists i, a i ⋖ b i ∧ forall j != i, Antis
ymmRel (· <= ·) (a j) (b j)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Pi.lt_def`：Pi.lt_def [forall i, Preorder (π i)] {x y : forall i, π i} : 
x < y ↔ x <= y ∧ exists i, x i < y i
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `Pi.exists_forall_antisymmRel_of_wcovBy`：exists_forall_antisymmRel_of_wco
vBy [Nonempty ι] (h : a ⩿ b) : exists i, forall j != i, AntisymmRel (· <= ·) (a 
j) (b j)
· 使用定理 `CovBy.wcovBy`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ⋖ b → a 
⩿ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `covBy_iff_wcovBy_and_lt`：covBy_iff_wcovBy_and_lt : a ⋖ b ↔ a ⩿ b ∧ a < b
· 使用定理 `WCovBy.eval`：∀ {ι : Type u_3} {α : ι → Type u_4} [inst : (i : ι) → Preor
der (α i)] {a b : (i : ι) → α i},   a ⩿ b → ∀ (i : ι), a i ⩿ b i
· 使用定理 `by_contra`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用引理 `Pi.wcovBy_iff_antisymmRel`：wcovBy_iff_antisymmRel [Nonempty ι] : a ⩿ b ↔
 exists i, a i ⩿ b i ∧ forall j != i, AntisymmRel (· <= ·) (a j) (b j)
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
A characterisation of the `CovBy` relation in products of preorders. See `Pi.cov
By_iff` for the
(more common) version in products of partial orders.
-/
lemma covBy_iff_antisymmRel :
    a ⋖ b ↔ ∃ i, a i ⋖ b i ∧ ∀ j ≠ i, AntisymmRel (· ≤ ·) (a j) (b j) := by
  constructor
  · intro h
    obtain ⟨j, hj⟩ := (Pi.lt_def.1 h.1).2
    have : Nonempty ι := ⟨j⟩
    obtain ⟨i, hi⟩ := exists_forall_antisymmRel_of_wcovBy h.wcovBy
    obtain rfl : i = j := by_contra fun this ↦ (hi j (Ne.symm this)).2.not_gt hj
    exact ⟨i, covBy_iff_wcovBy_and_lt.2 ⟨h.wcovBy.eval i, hj⟩, hi⟩
  rintro ⟨i, hi, h⟩
  have : Nonempty ι := ⟨i⟩
  refine covBy_iff_wcovBy_and_lt.2 ⟨wcovBy_iff_antisymmRel.2 ⟨i, hi.wcovBy, h⟩, ?_⟩
  exact Pi.lt_def.2 ⟨fun j ↦ (eq_or_ne j i).elim (· ▸ hi.1.le) (h j · |>.1), i, hi.1⟩

end Preorder

section PartialOrder

variable {ι : Type*} {α : ι → Type*} [∀ i, PartialOrder (α i)] {a b : (i : ι) → α i}

/-
**Pi.exists_forall_eq_of_covBy** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：exists_forall_eq_of_covBy (h : a ⋖ b) : exists i, forall j != i, a j = b j
参数：h : a ⋖ b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Pi.exists_forall_antisymmRel_of_covBy`：exists_forall_antisymmRel_of_covB
y (h : a ⋖ b) : exists i, forall j != i, AntisymmRel (· <= ·) (a j) (b j)
· 使用定理 `AntisymmRel.eq`：∀ {α : Type u_1} {a b : α} {r : α → α → Prop} [Std.Refl 
r] [Std.Antisymm r], AntisymmRel r a b → a = b
-/
lemma exists_forall_eq_of_covBy (h : a ⋖ b) : ∃ i, ∀ j ≠ i, a j = b j := by
  obtain ⟨i, hi⟩ := exists_forall_antisymmRel_of_covBy h
  exact ⟨i, fun j hj ↦ AntisymmRel.eq (hi _ hj)⟩
/-
**Pi.exists_forall_eq_of_wcovBy** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：exists_forall_eq_of_wcovBy [Nonempty ι] (h : a ⩿ b) : exists i, forall j !
= i, a j = b j
参数：h : a ⩿ b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Pi.exists_forall_antisymmRel_of_wcovBy`：exists_forall_antisymmRel_of_wco
vBy [Nonempty ι] (h : a ⩿ b) : exists i, forall j != i, AntisymmRel (· <= ·) (a 
j) (b j)
· 使用定理 `AntisymmRel.eq`：∀ {α : Type u_1} {a b : α} {r : α → α → Prop} [Std.Refl 
r] [Std.Antisymm r], AntisymmRel r a b → a = b
-/
lemma exists_forall_eq_of_wcovBy [Nonempty ι] (h : a ⩿ b) : ∃ i, ∀ j ≠ i, a j = b j := by
  obtain ⟨i, hi⟩ := exists_forall_antisymmRel_of_wcovBy h
  exact ⟨i, fun j hj ↦ AntisymmRel.eq (hi _ hj)⟩
/-
**Pi.wcovBy_iff** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：wcovBy_iff [Nonempty ι] : a ⩿ b ↔ exists i, a i ⩿ b i ∧ forall j != i, a j
 = b j
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma wcovBy_iff [Nonempty ι] : a ⩿ b ↔ ∃ i, a i ⩿ b i ∧ ∀ j ≠ i, a j = b j := by
  simp [wcovBy_iff_antisymmRel]
/-
**Pi.covBy_iff** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：covBy_iff : a ⋖ b ↔ exists i, a i ⋖ b i ∧ forall j != i, a j = b j
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma covBy_iff : a ⋖ b ↔ ∃ i, a i ⋖ b i ∧ ∀ j ≠ i, a j = b j := by
  simp [covBy_iff_antisymmRel]
/-
**Pi.wcovBy_iff_exists_right_eq** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：wcovBy_iff_exists_right_eq [Nonempty ι] [DecidableEq ι] : a ⩿ b ↔ exists i
 x, a i ⩿ x ∧ b = Function.update a i x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Pi.wcovBy_iff`：wcovBy_iff [Nonempty ι] : a ⩿ b ↔ exists i, a i ⩿ b i ∧ f
orall j != i, a j = b j
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma wcovBy_iff_exists_right_eq [Nonempty ι] [DecidableEq ι] :
    a ⩿ b ↔ ∃ i x, a i ⩿ x ∧ b = Function.update a i x := by
  rw [wcovBy_iff]
  constructor
  · rintro ⟨i, hi, h⟩
    exact ⟨i, b i, hi, by simpa [Function.eq_update_iff, eq_comm] using h⟩
  · rintro ⟨i, x, h, rfl⟩
    exact ⟨i, by simpa +contextual⟩
/-
**Pi.covBy_iff_exists_right_eq** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：covBy_iff_exists_right_eq [DecidableEq ι] : a ⋖ b ↔ exists i x, a i ⋖ x ∧ 
b = Function.update a i x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Pi.covBy_iff`：covBy_iff : a ⋖ b ↔ exists i, a i ⋖ b i ∧ forall j != i, a
 j = b j
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma covBy_iff_exists_right_eq [DecidableEq ι] :
    a ⋖ b ↔ ∃ i x, a i ⋖ x ∧ b = Function.update a i x := by
  rw [covBy_iff]
  constructor
  · rintro ⟨i, hi, h⟩
    exact ⟨i, b i, hi, by simpa [Function.eq_update_iff, eq_comm] using h⟩
  · rintro ⟨i, x, h, rfl⟩
    exact ⟨i, by simpa +contextual⟩
/-
**Pi.wcovBy_iff_exists_left_eq** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：wcovBy_iff_exists_left_eq [Nonempty ι] [DecidableEq ι] : a ⩿ b ↔ exists i 
x, x ⩿ b i ∧ a = Function.update b i x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Pi.wcovBy_iff`：wcovBy_iff [Nonempty ι] : a ⩿ b ↔ exists i, a i ⩿ b i ∧ f
orall j != i, a j = b j
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma wcovBy_iff_exists_left_eq [Nonempty ι] [DecidableEq ι] :
    a ⩿ b ↔ ∃ i x, x ⩿ b i ∧ a = Function.update b i x := by
  rw [wcovBy_iff]
  constructor
  · rintro ⟨i, hi, h⟩
    exact ⟨i, a i, hi, by simpa [Function.eq_update_iff, eq_comm] using h⟩
  · rintro ⟨i, x, h, rfl⟩
    exact ⟨i, by simpa +contextual⟩
/-
**Pi.covBy_iff_exists_left_eq** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：covBy_iff_exists_left_eq [DecidableEq ι] : a ⋖ b ↔ exists i x, x ⋖ b i ∧ a
 = Function.update b i x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Pi.covBy_iff`：covBy_iff : a ⋖ b ↔ exists i, a i ⋖ b i ∧ forall j != i, a
 j = b j
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma covBy_iff_exists_left_eq [DecidableEq ι] :
    a ⋖ b ↔ ∃ i x, x ⋖ b i ∧ a = Function.update b i x := by
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
/-
**WithTop.coe_wcovBy_coe** 是 Mathlib 中的一个引理，位于命名空间 `WithTop`。
形式化陈述：coe_wcovBy_coe : (a : WithTop α) ⩿ b ↔ a ⩿ b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.OrdConnected.apply_wcovBy_apply_iff`：Set.OrdConnected.apply_wcovBy_a
pply_iff (f : α ↪o β) (h : (range f).OrdConnected) : f a ⩿ f b ↔ a ⩿ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithTop.range_coe`：range_coe : range (some : α -> WithTop α) = Iio ⊤
-/
lemma coe_wcovBy_coe : (a : WithTop α) ⩿ b ↔ a ⩿ b :=
  Set.OrdConnected.apply_wcovBy_apply_iff WithTop.coeOrderHom <| by
    simp [WithTop.range_coe, ordConnected_Iio]

@[to_dual (attr := simp, norm_cast)]
/-
**WithTop.coe_covBy_coe** 是 Mathlib 中的一个引理，位于命名空间 `WithTop`。
形式化陈述：coe_covBy_coe : (a : WithTop α) ⋖ b ↔ a ⋖ b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.OrdConnected.apply_covBy_apply_iff`：Set.OrdConnected.apply_covBy_app
ly_iff (f : α ↪o β) (h : (range f).OrdConnected) : f a ⋖ f b ↔ a ⋖ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithTop.range_coe`：range_coe : range (some : α -> WithTop α) = Iio ⊤
-/
lemma coe_covBy_coe : (a : WithTop α) ⋖ b ↔ a ⋖ b :=
  Set.OrdConnected.apply_covBy_apply_iff WithTop.coeOrderHom <| by
    simp [WithTop.range_coe, ordConnected_Iio]

@[to_dual]
/-
**WithTop.covBy_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：covBy_top_iff {a : WithTop α} : a ⋖ ⊤ ↔ exists b : α, IsMax b ∧ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
theorem covBy_top_iff {a : WithTop α} : a ⋖ ⊤ ↔ ∃ b : α, IsMax b ∧ a = b := by
  cases a with
  | coe a => simp [CovBy, WithTop.forall, isMax_iff_forall_not_lt]
  | top => simp [CovBy]

@[to_dual (attr := simp)]
/-
**WithTop.not_covBy_top** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：not_covBy_top [NoMaxOrder α] {a : WithTop α} : ¬ a ⋖ ⊤
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem not_covBy_top [NoMaxOrder α] {a : WithTop α} : ¬ a ⋖ ⊤ := by
  simp [covBy_top_iff]

@[to_dual (attr := simp) bot_covBy_coe]
/-
**WithTop.coe_covBy_top** 是 Mathlib 中的一个引理，位于命名空间 `WithTop`。
形式化陈述：coe_covBy_top : (a : WithTop α) ⋖ ⊤ ↔ IsMax a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma coe_covBy_top : (a : WithTop α) ⋖ ⊤ ↔ IsMax a := by
  simp [covBy_iff_Ioo_eq, ← image_coe_Ioi]

@[to_dual (attr := simp) bot_wcovBy_coe]
/-
**WithTop.coe_wcovBy_top** 是 Mathlib 中的一个引理，位于命名空间 `WithTop`。
形式化陈述：coe_wcovBy_top : (a : WithTop α) ⩿ ⊤ ↔ IsMax a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma coe_wcovBy_top : (a : WithTop α) ⩿ ⊤ ↔ IsMax a := by
  simp only [wcovBy_iff_Ioo_eq, ← image_coe_Ioi, le_top, image_eq_empty, true_and, Ioi_eq_empty_iff]

end WithTop

section WellFounded

variable [Preorder α]

@[to_dual]
/-
**exists_covBy_of_wellFoundedLT** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：exists_covBy_of_wellFoundedLT [wf : WellFoundedLT α] ⦃a : α⦄ (h : ¬ IsMax 
a) : exists a', a ⋖ a'
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `wellFounded_lt`：wellFounded_lt [LT α] [WellFoundedLT α] : @WellFounded α
 (· < ·)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_isMax_iff`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, ¬IsMax a ↔ 
∃ b, a < b
· 使用定理 `WellFounded.min_mem`：min_mem {r : α -> α -> Prop} (H : WellFounded r) (s
 : Set α) (h : s.Nonempty) : H.min s h in s
· 使用定理 `WellFounded.not_lt_min`：not_lt_min {r : α -> α -> Prop} (H : WellFounded
 r) (s : Set α) {x} (hx : x in s) : ¬r x (H.min s ⟨x, hx⟩)
· 使用定理 `IsWellFounded.wf`：∀ {α : Type u} {r : α → α → Prop} [self : IsWellFounde
d α r], WellFounded r
-/
lemma exists_covBy_of_wellFoundedLT [wf : WellFoundedLT α] ⦃a : α⦄ (h : ¬ IsMax a) :
    ∃ a', a ⋖ a' := by
  rw [not_isMax_iff] at h
  exact ⟨_, wellFounded_lt.min_mem (Ioi a) h, fun a' ↦ wf.wf.not_lt_min (Ioi a)⟩

end WellFounded

