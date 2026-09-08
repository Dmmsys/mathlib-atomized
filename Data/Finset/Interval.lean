/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Yury Kudryashov
-/
module

public import Mathlib.Data.Finset.Grade
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Order.Interval.Finset.Basic

/-!
# Intervals of finsets as finsets

This file provides the `LocallyFiniteOrder` instance for `Finset α` and calculates the cardinality
of finite intervals of finsets.

If `s t : Finset α`, then `Finset.Icc s t` is the finset of finsets which include `s` and are
included in `t`. For example,
`Finset.Icc {0, 1} {0, 1, 2, 3} = {{0, 1}, {0, 1, 2}, {0, 1, 3}, {0, 1, 2, 3}}`
and
`Finset.Icc {0, 1, 2} {0, 1, 3} = {}`.

In addition, this file gives characterizations of monotone and strictly monotone functions
out of `Finset α` in terms of `Finset.insert`
-/

public section


variable {α β : Type*}

namespace Finset

section Decidable

/-- `LocallyFiniteOrder` instance for `Finset α`.

We provide an optimized definition for `Finset.Icc (s : Finset α) t`,
then define the other intervals based on `Icc`.

We do not define, e.g., `Finset.Ico` based on `Finset.ssubsets`,
because it would require more code without performance gain.
-/
/-
**Finset.instLocallyFiniteOrder** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
形式化陈述：instLocallyFiniteOrder [DecidableEq α] : LocallyFiniteOrder (Finset α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`LocallyFiniteOrder` instance for `Finset α`.

We provide an optimized definition for `Finset.Icc (s : Finset α) t`,
then define the other intervals based on `Icc`.

We do not define, e.g., `Finset.Ico` based on `Finset.ssubsets`,
because it would require more code without performance gain.
-/
instance instLocallyFiniteOrder [DecidableEq α] : LocallyFiniteOrder (Finset α) :=
  .ofIcc _ (fun s t ↦
    if s ⊆ t then
      (t \ s).powerset.attach.map ⟨fun u ↦ u.1.disjUnion s <|
        disjoint_sdiff_self_left.mono_left <| mem_powerset.mp u.2, fun u₁ u₂ h ↦ by
          simpa only [disjUnion_inj_left, Subtype.ext_iff] using h⟩
    else ∅) fun s t u ↦ by
      by_cases hst : s ⊆ t
      · suffices (∃ a ⊆ t, Disjoint a s ∧ a ∪ s = u) ↔ s ⊆ u ∧ u ⊆ t by
          simpa [hst, subset_sdiff, and_assoc]
        constructor
        · rintro ⟨u, hut, -, rfl⟩
          exact ⟨subset_union_right, union_subset hut hst⟩
        · rintro ⟨hsu, hut⟩
          exact ⟨u \ s, sdiff_subset.trans hut, disjoint_sdiff_self_left, sdiff_union_of_subset hsu⟩
      · suffices s ⊆ u → ¬u ⊆ t by simpa [hst]
        exact fun hsu hut ↦ hst (hsu.trans hut)

variable [DecidableEq α] (s t : Finset α)
/-
**Finset.Icc_eq_filter_powerset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Icc_eq_filter_powerset : Icc s t = {u in t.powerset | s subseteq u}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Icc_eq_filter_powerset : Icc s t = {u ∈ t.powerset | s ⊆ u} := by ext; simp [and_comm]
/-
**Finset.Ico_eq_filter_ssubsets** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ico_eq_filter_ssubsets : Ico s t = {u in t.ssubsets | s subseteq u}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Ico_eq_filter_ssubsets : Ico s t = {u ∈ t.ssubsets | s ⊆ u} := by ext; simp [and_comm]
/-
**Finset.Ioc_eq_filter_powerset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ioc_eq_filter_powerset : Ioc s t = {u in t.powerset | s ⊂ u}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Ioc_eq_filter_powerset : Ioc s t = {u ∈ t.powerset | s ⊂ u} := by ext; simp [and_comm]
/-
**Finset.Ioo_eq_filter_ssubsets** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ioo_eq_filter_ssubsets : Ioo s t = {u in t.ssubsets | s ⊂ u}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Ioo_eq_filter_ssubsets : Ioo s t = {u ∈ t.ssubsets | s ⊂ u} := by ext; simp [and_comm]
/-
**Finset.Iic_eq_powerset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Iic_eq_powerset : Iic s = s.powerset
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Iic_eq_powerset : Iic s = s.powerset := by ext; simp
/-
**Finset.Iio_eq_ssubsets** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Iio_eq_ssubsets : Iio s = s.ssubsets
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Iio_eq_ssubsets : Iio s = s.ssubsets := by ext; simp

variable {s t}
/-
**Finset.Icc_eq_image_powerset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Icc_eq_image_powerset (h : s subseteq t) : Icc s t = (t \ s).powerset.imag
e (s union ·)
参数：h : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.disjUnion_eq_union`：disjUnion_eq_union (s t h) : @disjUnion α s t
 h = s union t
· 使用定理 `Finset.union_comm`：union_comm (s₁ s₂ : Finset α) : s₁ union s₂ = s₂ unio
n s₁
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Function.Embedding.mk.congr_simp`：∀ {α : Sort u_1} {β : Sort u_2} (toFun
 toFun_1 : α → β) (e_toFun : toFun = toFun_1) (inj' : Function.Injective toFun),
   { toFun := toFun, i…
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Icc_eq_image_powerset (h : s ⊆ t) : Icc s t = (t \ s).powerset.image (s ∪ ·) := by
  unfold Finset.Icc instLocallyFiniteOrder LocallyFiniteOrder.ofIcc
  ext
  simp [h, union_comm]
/-
**Finset.Ico_eq_image_ssubsets** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ico_eq_image_ssubsets (h : s subseteq t) : Ico s t = (t \ s).ssubsets.imag
e (s union ·)
参数：h : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sdiff_lt_sdiff_right`：sdiff_lt_sdiff_right (h : x < y) (hz : z <= x) : x
 \ z < y \ z
· 使用定理 `sup_sdiff_cancel_right`：sup_sdiff_cancel_right (h : a <= b) : a ⊔ b \ a 
= b
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `sup_lt_of_lt_sdiff_left`：sup_lt_of_lt_sdiff_left (h : y < z \ x) (hxz : 
x <= z) : x ⊔ y < z
-/
theorem Ico_eq_image_ssubsets (h : s ⊆ t) : Ico s t = (t \ s).ssubsets.image (s ∪ ·) := by
  ext u
  simp_rw [mem_Ico, mem_image, mem_ssubsets]
  constructor
  · rintro ⟨hs, ht⟩
    exact ⟨u \ s, sdiff_lt_sdiff_right ht hs, sup_sdiff_cancel_right hs⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨le_sup_left, sup_lt_of_lt_sdiff_left hv h⟩

/-- Cardinality of a non-empty `Icc` of finsets. -/
/-
**Finset.card_Icc_finset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_Icc_finset (h : s subseteq t) : (Icc s t).card = 2 ^ (t.card - s.card
)
参数：h : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.disjUnion_eq_union`：disjUnion_eq_union (s t h) : @disjUnion α s t
 h = s union t
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Function.Embedding.mk.congr_simp`：∀ {α : Sort u_1} {β : Sort u_2} (toFun
 toFun_1 : α → β) (e_toFun : toFun = toFun_1) (inj' : Function.Injective toFun),
   { toFun := toFun, i…
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用定理 `Finset.card_attach`：card_attach : #s.attach = #s
· 使用定理 `Finset.card_powerset`：card_powerset (s : Finset α) : card (powerset s) =
 2 ^ card s
· 使用定理 `Finset.card_sdiff_of_subset`：card_sdiff_of_subset (h : s subseteq t) : #
(t \ s) = #t - #s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Cardinality of a non-empty `Icc` of finsets.
-/
theorem card_Icc_finset (h : s ⊆ t) : (Icc s t).card = 2 ^ (t.card - s.card) := by
  unfold Finset.Icc instLocallyFiniteOrder LocallyFiniteOrder.ofIcc
  simp [h, card_sdiff_of_subset]

/-- Cardinality of an `Ico` of finsets. -/
/-
**Finset.card_Ico_finset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_Ico_finset (h : s subseteq t) : (Ico s t).card = 2 ^ (t.card - s.card
) - 1
参数：h : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_Ico_eq_card_Icc_sub_one`：card_Ico_eq_card_Icc_sub_one (a b :
 α) : #(Ico a b) = #(Icc a b) - 1
· 使用定理 `Finset.card_Icc_finset`：card_Icc_finset (h : s subseteq t) : (Icc s t).c
ard = 2 ^ (t.card - s.card)

--- 原说明 ---
Cardinality of an `Ico` of finsets.
-/
theorem card_Ico_finset (h : s ⊆ t) : (Ico s t).card = 2 ^ (t.card - s.card) - 1 := by
  rw [card_Ico_eq_card_Icc_sub_one, card_Icc_finset h]

/-- Cardinality of an `Ioc` of finsets. -/
/-
**Finset.card_Ioc_finset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_Ioc_finset (h : s subseteq t) : (Ioc s t).card = 2 ^ (t.card - s.card
) - 1
参数：h : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_Ioc_eq_card_Icc_sub_one`：card_Ioc_eq_card_Icc_sub_one (a b :
 α) : #(Ioc a b) = #(Icc a b) - 1
· 使用定理 `Finset.card_Icc_finset`：card_Icc_finset (h : s subseteq t) : (Icc s t).c
ard = 2 ^ (t.card - s.card)

--- 原说明 ---
Cardinality of an `Ioc` of finsets.
-/
theorem card_Ioc_finset (h : s ⊆ t) : (Ioc s t).card = 2 ^ (t.card - s.card) - 1 := by
  rw [card_Ioc_eq_card_Icc_sub_one, card_Icc_finset h]

/-- Cardinality of an `Ioo` of finsets. -/
/-
**Finset.card_Ioo_finset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_Ioo_finset (h : s subseteq t) : (Ioo s t).card = 2 ^ (t.card - s.card
) - 2
参数：h : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_Ioo_eq_card_Icc_sub_two`：card_Ioo_eq_card_Icc_sub_two (a b :
 α) : #(Ioo a b) = #(Icc a b) - 2
· 使用定理 `Finset.card_Icc_finset`：card_Icc_finset (h : s subseteq t) : (Icc s t).c
ard = 2 ^ (t.card - s.card)

--- 原说明 ---
Cardinality of an `Ioo` of finsets.
-/
theorem card_Ioo_finset (h : s ⊆ t) : (Ioo s t).card = 2 ^ (t.card - s.card) - 2 := by
  rw [card_Ioo_eq_card_Icc_sub_two, card_Icc_finset h]

/-- Cardinality of an `Iic` of finsets. -/
/-
**Finset.card_Iic_finset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_Iic_finset : (Iic s).card = 2 ^ s.card
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.Iic_eq_powerset`：Iic_eq_powerset : Iic s = s.powerset
· 使用定理 `Finset.card_powerset`：card_powerset (s : Finset α) : card (powerset s) =
 2 ^ card s

--- 原说明 ---
Cardinality of an `Iic` of finsets.
-/
theorem card_Iic_finset : (Iic s).card = 2 ^ s.card := by rw [Iic_eq_powerset, card_powerset]

/-- Cardinality of an `Iio` of finsets. -/
/-
**Finset.card_Iio_finset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_Iio_finset : (Iio s).card = 2 ^ s.card - 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.Iio_eq_ssubsets`：Iio_eq_ssubsets : Iio s = s.ssubsets
· 使用定理 `Finset.ssubsets.eq_1`：∀ {α : Type u_1} [inst : DecidableEq α] (s : Finse
t α), s.ssubsets = s.powerset.erase s
· 使用定理 `Finset.card_erase_of_mem`：card_erase_of_mem : a in s -> #(s.erase a) = #
s - 1
· 使用定理 `Finset.mem_powerset_self`：mem_powerset_self (s : Finset α) : s in powers
et s
· 使用定理 `Finset.card_powerset`：card_powerset (s : Finset α) : card (powerset s) =
 2 ^ card s

--- 原说明 ---
Cardinality of an `Iio` of finsets.
-/
theorem card_Iio_finset : (Iio s).card = 2 ^ s.card - 1 := by
  rw [Iio_eq_ssubsets, ssubsets, card_erase_of_mem (mem_powerset_self _), card_powerset]

end Decidable

variable [Preorder β] {s t : Finset α} {f : Finset α → β}

section Cons

/-- A function `f` from `Finset α` is monotone if and only if `f s ≤ f (cons a s ha)` for all `s`
and `a ∉ s`. -/
/-
**Finset.monotone_iff_forall_le_cons** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：monotone_iff_forall_le_cons : Monotone f ↔ forall s, forall ⦃a⦄ (ha), f s 
<= f (cons a s ha)
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.cons_eq_insert`：cons_eq_insert (a s h) : @cons α a s h = insert a
 s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A function `f` from `Finset α` is monotone if and only if `f s ≤ f (cons a s ha)
` for all `s`
and `a ∉ s`.
-/
lemma monotone_iff_forall_le_cons : Monotone f ↔ ∀ s, ∀ ⦃a⦄ (ha), f s ≤ f (cons a s ha) := by
  classical simp [monotone_iff_forall_covBy, covBy_iff_exists_cons]

/-- A function `f` from `Finset α` is antitone if and only if `f (cons a s ha) ≤ f s` for all
`s` and `a ∉ s`. -/
/-
**Finset.antitone_iff_forall_cons_le** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：antitone_iff_forall_cons_le : Antitone f ↔ forall s ⦃a⦄ ha, f (cons a s ha
) <= f s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.monotone_iff_forall_le_cons`：monotone_iff_forall_le_cons : Monoto
ne f ↔ forall s, forall ⦃a⦄ (ha), f s <= f (cons a s ha)

--- 原说明 ---
A function `f` from `Finset α` is antitone if and only if `f (cons a s ha) ≤ f s
` for all
`s` and `a ∉ s`.
-/
lemma antitone_iff_forall_cons_le : Antitone f ↔ ∀ s ⦃a⦄ ha, f (cons a s ha) ≤ f s :=
  monotone_iff_forall_le_cons (β := βᵒᵈ)

/-- A function `f` from `Finset α` is strictly monotone if and only if `f s < f (cons a s ha)` for
all `s` and `a ∉ s`. -/
/-
**Finset.strictMono_iff_forall_lt_cons** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：strictMono_iff_forall_lt_cons : StrictMono f ↔ forall s ⦃a⦄ ha, f s < f (c
ons a s ha)
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.cons_eq_insert`：cons_eq_insert (a s h) : @cons α a s h = insert a
 s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A function `f` from `Finset α` is strictly monotone if and only if `f s < f (con
s a s ha)` for
all `s` and `a ∉ s`.
-/
lemma strictMono_iff_forall_lt_cons : StrictMono f ↔ ∀ s ⦃a⦄ ha, f s < f (cons a s ha) := by
  classical simp [strictMono_iff_forall_covBy, covBy_iff_exists_cons]

/-- A function `f` from `Finset α` is strictly antitone if and only if `f (cons a s ha) < f s` for
all `s` and `a ∉ s`. -/
/-
**Finset.strictAnti_iff_forall_cons_lt** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：strictAnti_iff_forall_cons_lt : StrictAnti f ↔ forall s ⦃a⦄ ha, f (cons a 
s ha) < f s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.strictMono_iff_forall_lt_cons`：strictMono_iff_forall_lt_cons : St
rictMono f ↔ forall s ⦃a⦄ ha, f s < f (cons a s ha)

--- 原说明 ---
A function `f` from `Finset α` is strictly antitone if and only if `f (cons a s 
ha) < f s` for
all `s` and `a ∉ s`.
-/
lemma strictAnti_iff_forall_cons_lt : StrictAnti f ↔ ∀ s ⦃a⦄ ha, f (cons a s ha) < f s :=
  strictMono_iff_forall_lt_cons (β := βᵒᵈ)

end Cons

section Insert

variable [DecidableEq α]

/-- A function `f` from `Finset α` is monotone if and only if `f s ≤ f (insert a s)` for all `s` and
`a ∉ s`. -/
/-
**Finset.monotone_iff_forall_le_insert** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：monotone_iff_forall_le_insert : Monotone f ↔ forall s ⦃a⦄, a ∉ s -> f s <=
 f (insert a s)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Finset.cons_eq_insert`：cons_eq_insert (a s h) : @cons α a s h = insert a
 s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A function `f` from `Finset α` is monotone if and only if `f s ≤ f (insert a s)`
 for all `s` and
`a ∉ s`.
-/
lemma monotone_iff_forall_le_insert : Monotone f ↔ ∀ s ⦃a⦄, a ∉ s → f s ≤ f (insert a s) := by
  simp [monotone_iff_forall_le_cons]

/-- A function `f` from `Finset α` is antitone if and only if `f (insert a s) ≤ f s` for all
`s` and `a ∉ s`. -/
/-
**Finset.antitone_iff_forall_insert_le** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：antitone_iff_forall_insert_le : Antitone f ↔ forall s ⦃a⦄, a ∉ s -> f (ins
ert a s) <= f s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.monotone_iff_forall_le_insert`：monotone_iff_forall_le_insert : Mo
notone f ↔ forall s ⦃a⦄, a ∉ s -> f s <= f (insert a s)

--- 原说明 ---
A function `f` from `Finset α` is antitone if and only if `f (insert a s) ≤ f s`
 for all
`s` and `a ∉ s`.
-/
lemma antitone_iff_forall_insert_le : Antitone f ↔ ∀ s ⦃a⦄, a ∉ s → f (insert a s) ≤ f s :=
  monotone_iff_forall_le_insert (β := βᵒᵈ)

/-- A function `f` from `Finset α` is strictly monotone if and only if `f s < f (insert a s)` for
all `s` and `a ∉ s`. -/
/-
**Finset.strictMono_iff_forall_lt_insert** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：strictMono_iff_forall_lt_insert : StrictMono f ↔ forall s ⦃a⦄, a ∉ s -> f 
s < f (insert a s)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Finset.cons_eq_insert`：cons_eq_insert (a s h) : @cons α a s h = insert a
 s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A function `f` from `Finset α` is strictly monotone if and only if `f s < f (ins
ert a s)` for
all `s` and `a ∉ s`.
-/
lemma strictMono_iff_forall_lt_insert : StrictMono f ↔ ∀ s ⦃a⦄, a ∉ s → f s < f (insert a s) := by
  simp [strictMono_iff_forall_lt_cons]

/-- A function `f` from `Finset α` is strictly antitone if and only if `f (insert a s) < f s` for
all `s` and `a ∉ s`. -/
/-
**Finset.strictAnti_iff_forall_lt_insert** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：strictAnti_iff_forall_lt_insert : StrictAnti f ↔ forall s ⦃a⦄, a ∉ s -> f 
(insert a s) < f s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.strictMono_iff_forall_lt_insert`：strictMono_iff_forall_lt_insert 
: StrictMono f ↔ forall s ⦃a⦄, a ∉ s -> f s < f (insert a s)

--- 原说明 ---
A function `f` from `Finset α` is strictly antitone if and only if `f (insert a 
s) < f s` for
all `s` and `a ∉ s`.
-/
lemma strictAnti_iff_forall_lt_insert : StrictAnti f ↔ ∀ s ⦃a⦄, a ∉ s → f (insert a s) < f s :=
  strictMono_iff_forall_lt_insert (β := βᵒᵈ)

end Insert

end Finset

