/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Data.Set.Image
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Order.WithBot

/-!
# Intervals in `WithTop α` and `WithBot α`

In this file we prove various lemmas about `Set.image`s and `Set.preimage`s of intervals under
`some : α → WithTop α` and `some : α → WithBot α`.
-/

public section

open Set

variable {α : Type*}

namespace WithTop

@[to_dual (attr := simp)]
/-
**WithTop.preimage_coe_top** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：preimage_coe_top : (some : α -> WithTop α) ⁻¹' {⊤} = (∅ : Set α)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_of_subset_empty`：eq_empty_of_subset_empty {s : Set α} : s s
ubseteq ∅ -> s = ∅
· 使用定理 `WithTop.coe_ne_top`：∀ {α : Type u_1} {a : α}, ↑a ≠ ⊤
-/
theorem preimage_coe_top : (some : α → WithTop α) ⁻¹' {⊤} = (∅ : Set α) :=
  eq_empty_of_subset_empty fun _ => coe_ne_top

variable [Preorder α] {a b : α}

@[to_dual]
/-
**WithTop.range_coe** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：range_coe : range (some : α -> WithTop α) = Iio ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem range_coe : range (some : α → WithTop α) = Iio ⊤ := by
  ext; simp [mem_range, WithTop.lt_top_iff_ne_top, ne_top_iff_exists]

@[to_dual (attr := simp)]
/-
**WithTop.preimage_coe_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：preimage_coe_Ioi : (some : α -> WithTop α) ⁻¹' Ioi a = Ioi a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `WithTop.coe_lt_coe`：∀ {α : Type u_1} {a b : α} [inst : LT α], ↑b < ↑a ↔ 
b < a
-/
theorem preimage_coe_Ioi : (some : α → WithTop α) ⁻¹' Ioi a = Ioi a :=
  ext fun _ => coe_lt_coe

@[to_dual (attr := simp)]
/-
**WithTop.preimage_coe_Ici** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：preimage_coe_Ici : (some : α -> WithTop α) ⁻¹' Ici a = Ici a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `WithTop.coe_le_coe`：∀ {α : Type u_1} {a b : α} [inst : LE α], ↑b ≤ ↑a ↔ 
b ≤ a
-/
theorem preimage_coe_Ici : (some : α → WithTop α) ⁻¹' Ici a = Ici a :=
  ext fun _ => coe_le_coe

@[to_dual (attr := simp)]
/-
**WithTop.preimage_coe_Iio** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：preimage_coe_Iio : (some : α -> WithTop α) ⁻¹' Iio a = Iio a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `WithTop.coe_lt_coe`：∀ {α : Type u_1} {a b : α} [inst : LT α], ↑b < ↑a ↔ 
b < a
-/
theorem preimage_coe_Iio : (some : α → WithTop α) ⁻¹' Iio a = Iio a :=
  ext fun _ => coe_lt_coe

@[to_dual (attr := simp)]
/-
**WithTop.preimage_coe_Iic** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：preimage_coe_Iic : (some : α -> WithTop α) ⁻¹' Iic a = Iic a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `WithTop.coe_le_coe`：∀ {α : Type u_1} {a b : α} [inst : LE α], ↑b ≤ ↑a ↔ 
b ≤ a
-/
theorem preimage_coe_Iic : (some : α → WithTop α) ⁻¹' Iic a = Iic a :=
  ext fun _ => coe_le_coe

@[to_dual (attr := simp)]
/-
**WithTop.preimage_coe_Icc** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：preimage_coe_Icc : (some : α -> WithTop α) ⁻¹' Icc a b = Icc a b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `WithTop.preimage_coe_Ici`：preimage_coe_Ici : (some : α -> WithTop α) ⁻¹'
 Ici a = Ici a
· 使用定理 `WithTop.preimage_coe_Iic`：preimage_coe_Iic : (some : α -> WithTop α) ⁻¹'
 Iic a = Iic a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preimage_coe_Icc : (some : α → WithTop α) ⁻¹' Icc a b = Icc a b := by simp [← Ici_inter_Iic]

@[to_dual (attr := simp)]
/-
**WithTop.preimage_coe_Ico** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：preimage_coe_Ico : (some : α -> WithTop α) ⁻¹' Ico a b = Ico a b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `WithTop.preimage_coe_Ici`：preimage_coe_Ici : (some : α -> WithTop α) ⁻¹'
 Ici a = Ici a
· 使用定理 `WithTop.preimage_coe_Iio`：preimage_coe_Iio : (some : α -> WithTop α) ⁻¹'
 Iio a = Iio a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preimage_coe_Ico : (some : α → WithTop α) ⁻¹' Ico a b = Ico a b := by simp [← Ici_inter_Iio]

@[to_dual (attr := simp)]
/-
**WithTop.preimage_coe_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：preimage_coe_Ioc : (some : α -> WithTop α) ⁻¹' Ioc a b = Ioc a b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `WithTop.preimage_coe_Ioi`：preimage_coe_Ioi : (some : α -> WithTop α) ⁻¹'
 Ioi a = Ioi a
· 使用定理 `WithTop.preimage_coe_Iic`：preimage_coe_Iic : (some : α -> WithTop α) ⁻¹'
 Iic a = Iic a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preimage_coe_Ioc : (some : α → WithTop α) ⁻¹' Ioc a b = Ioc a b := by simp [← Ioi_inter_Iic]

@[to_dual (attr := simp)]
/-
**WithTop.preimage_coe_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：preimage_coe_Ioo : (some : α -> WithTop α) ⁻¹' Ioo a b = Ioo a b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `WithTop.preimage_coe_Ioi`：preimage_coe_Ioi : (some : α -> WithTop α) ⁻¹'
 Ioi a = Ioi a
· 使用定理 `WithTop.preimage_coe_Iio`：preimage_coe_Iio : (some : α -> WithTop α) ⁻¹'
 Iio a = Iio a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preimage_coe_Ioo : (some : α → WithTop α) ⁻¹' Ioo a b = Ioo a b := by simp [← Ioi_inter_Iio]

@[to_dual (attr := simp)]
/-
**WithTop.preimage_coe_Iio_top** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：preimage_coe_Iio_top : (some : α -> WithTop α) ⁻¹' Iio ⊤ = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithTop.range_coe`：range_coe : range (some : α -> WithTop α) = Iio ⊤
· 使用定理 `Set.preimage_range`：preimage_range (f : α -> β) : f ⁻¹' range f = univ
-/
theorem preimage_coe_Iio_top : (some : α → WithTop α) ⁻¹' Iio ⊤ = univ := by
  rw [← range_coe, preimage_range]

@[to_dual (attr := simp)]
/-
**WithTop.preimage_coe_Ico_top** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：preimage_coe_Ico_top : (some : α -> WithTop α) ⁻¹' Ico a ⊤ = Ici a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `WithTop.preimage_coe_Ici`：preimage_coe_Ici : (some : α -> WithTop α) ⁻¹'
 Ici a = Ici a
· 使用定理 `WithTop.preimage_coe_Iio_top`：preimage_coe_Iio_top : (some : α -> WithTo
p α) ⁻¹' Iio ⊤ = univ
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preimage_coe_Ico_top : (some : α → WithTop α) ⁻¹' Ico a ⊤ = Ici a := by
  simp [← Ici_inter_Iio]

@[to_dual (attr := simp)]
/-
**WithTop.preimage_coe_Ioo_top** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：preimage_coe_Ioo_top : (some : α -> WithTop α) ⁻¹' Ioo a ⊤ = Ioi a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `WithTop.preimage_coe_Ioi`：preimage_coe_Ioi : (some : α -> WithTop α) ⁻¹'
 Ioi a = Ioi a
· 使用定理 `WithTop.preimage_coe_Iio_top`：preimage_coe_Iio_top : (some : α -> WithTo
p α) ⁻¹' Iio ⊤ = univ
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preimage_coe_Ioo_top : (some : α → WithTop α) ⁻¹' Ioo a ⊤ = Ioi a := by
  simp [← Ioi_inter_Iio]

@[to_dual]
/-
**WithTop.image_coe_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：image_coe_Ioi : (some : α -> WithTop α) '' Ioi a = Ioo (a : WithTop α) ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithTop.preimage_coe_Ioi`：preimage_coe_Ioi : (some : α -> WithTop α) ⁻¹'
 Ioi a = Ioi a
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用定理 `WithTop.range_coe`：range_coe : range (some : α -> WithTop α) = Iio ⊤
· 使用定理 `Set.Ioi_inter_Iio`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.I
oi a ∩ Set.Iio b = Set.Ioo a b
-/
theorem image_coe_Ioi : (some : α → WithTop α) '' Ioi a = Ioo (a : WithTop α) ⊤ := by
  rw [← preimage_coe_Ioi, image_preimage_eq_inter_range, range_coe, Ioi_inter_Iio]

@[to_dual]
/-
**WithTop.image_coe_Ici** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：image_coe_Ici : (some : α -> WithTop α) '' Ici a = Ico (a : WithTop α) ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithTop.preimage_coe_Ici`：preimage_coe_Ici : (some : α -> WithTop α) ⁻¹'
 Ici a = Ici a
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用定理 `WithTop.range_coe`：range_coe : range (some : α -> WithTop α) = Iio ⊤
· 使用定理 `Set.Ici_inter_Iio`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.I
ci a ∩ Set.Iio b = Set.Ico a b
-/
theorem image_coe_Ici : (some : α → WithTop α) '' Ici a = Ico (a : WithTop α) ⊤ := by
  rw [← preimage_coe_Ici, image_preimage_eq_inter_range, range_coe, Ici_inter_Iio]

@[to_dual]
/-
**WithTop.image_coe_Iio** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：image_coe_Iio : (some : α -> WithTop α) '' Iio a = Iio (a : WithTop α)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithTop.preimage_coe_Iio`：preimage_coe_Iio : (some : α -> WithTop α) ⁻¹'
 Iio a = Iio a
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用定理 `WithTop.range_coe`：range_coe : range (some : α -> WithTop α) = Iio ⊤
· 使用定理 `Set.inter_eq_self_of_subset_left`：inter_eq_self_of_subset_left {s t : Se
t α} : s subseteq t -> s inter t = s
· 使用定理 `Set.Iio_subset_Iio`：Iio_subset_Iio (h : a <= b) : Iio a subseteq Iio b
· 使用定理 `le_top`：le_top : a <= ⊤
-/
theorem image_coe_Iio : (some : α → WithTop α) '' Iio a = Iio (a : WithTop α) := by
  rw [← preimage_coe_Iio, image_preimage_eq_inter_range, range_coe,
    inter_eq_self_of_subset_left (Iio_subset_Iio le_top)]

@[to_dual]
/-
**WithTop.image_coe_Iic** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：image_coe_Iic : (some : α -> WithTop α) '' Iic a = Iic (a : WithTop α)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithTop.preimage_coe_Iic`：preimage_coe_Iic : (some : α -> WithTop α) ⁻¹'
 Iic a = Iic a
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用定理 `WithTop.range_coe`：range_coe : range (some : α -> WithTop α) = Iio ⊤
· 使用定理 `Set.inter_eq_self_of_subset_left`：inter_eq_self_of_subset_left {s t : Se
t α} : s subseteq t -> s inter t = s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.Iic_subset_Iio`：Iic_subset_Iio : Iic a subseteq Iio b ↔ a < b
· 使用定理 `WithTop.coe_lt_top`：∀ {α : Type u_1} [inst : LT α] (a : α), ↑a < ⊤
-/
theorem image_coe_Iic : (some : α → WithTop α) '' Iic a = Iic (a : WithTop α) := by
  rw [← preimage_coe_Iic, image_preimage_eq_inter_range, range_coe,
    inter_eq_self_of_subset_left (Iic_subset_Iio.2 <| coe_lt_top a)]

@[to_dual]
/-
**WithTop.image_coe_Icc** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：image_coe_Icc : (some : α -> WithTop α) '' Icc a b = Icc (a : WithTop α) b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithTop.preimage_coe_Icc`：preimage_coe_Icc : (some : α -> WithTop α) ⁻¹'
 Icc a b = Icc a b
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用定理 `WithTop.range_coe`：range_coe : range (some : α -> WithTop α) = Iio ⊤
· 使用定理 `Set.inter_eq_self_of_subset_left`：inter_eq_self_of_subset_left {s t : Se
t α} : s subseteq t -> s inter t = s
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Set.Icc_subset_Iic_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Icc a b ⊆ Set.Iic b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.Iic_subset_Iio`：Iic_subset_Iio : Iic a subseteq Iio b ↔ a < b
· 使用定理 `WithTop.coe_lt_top`：∀ {α : Type u_1} [inst : LT α] (a : α), ↑a < ⊤
-/
theorem image_coe_Icc : (some : α → WithTop α) '' Icc a b = Icc (a : WithTop α) b := by
  rw [← preimage_coe_Icc, image_preimage_eq_inter_range, range_coe,
    inter_eq_self_of_subset_left
      (Subset.trans Icc_subset_Iic_self <| Iic_subset_Iio.2 <| coe_lt_top b)]

@[to_dual]
/-
**WithTop.image_coe_Ico** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：image_coe_Ico : (some : α -> WithTop α) '' Ico a b = Ico (a : WithTop α) b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithTop.preimage_coe_Ico`：preimage_coe_Ico : (some : α -> WithTop α) ⁻¹'
 Ico a b = Ico a b
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用定理 `WithTop.range_coe`：range_coe : range (some : α -> WithTop α) = Iio ⊤
· 使用定理 `Set.inter_eq_self_of_subset_left`：inter_eq_self_of_subset_left {s t : Se
t α} : s subseteq t -> s inter t = s
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Set.Ico_subset_Iio_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ico a b ⊆ Set.Iio b
· 使用定理 `Set.Iio_subset_Iio`：Iio_subset_Iio (h : a <= b) : Iio a subseteq Iio b
· 使用定理 `le_top`：le_top : a <= ⊤
-/
theorem image_coe_Ico : (some : α → WithTop α) '' Ico a b = Ico (a : WithTop α) b := by
  rw [← preimage_coe_Ico, image_preimage_eq_inter_range, range_coe,
    inter_eq_self_of_subset_left (Subset.trans Ico_subset_Iio_self <| Iio_subset_Iio le_top)]

@[to_dual]
/-
**WithTop.image_coe_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：image_coe_Ioc : (some : α -> WithTop α) '' Ioc a b = Ioc (a : WithTop α) b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithTop.preimage_coe_Ioc`：preimage_coe_Ioc : (some : α -> WithTop α) ⁻¹'
 Ioc a b = Ioc a b
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用定理 `WithTop.range_coe`：range_coe : range (some : α -> WithTop α) = Iio ⊤
· 使用定理 `Set.inter_eq_self_of_subset_left`：inter_eq_self_of_subset_left {s t : Se
t α} : s subseteq t -> s inter t = s
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Set.Ioc_subset_Iic_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc a b ⊆ Set.Iic b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.Iic_subset_Iio`：Iic_subset_Iio : Iic a subseteq Iio b ↔ a < b
· 使用定理 `WithTop.coe_lt_top`：∀ {α : Type u_1} [inst : LT α] (a : α), ↑a < ⊤
-/
theorem image_coe_Ioc : (some : α → WithTop α) '' Ioc a b = Ioc (a : WithTop α) b := by
  rw [← preimage_coe_Ioc, image_preimage_eq_inter_range, range_coe,
    inter_eq_self_of_subset_left
      (Subset.trans Ioc_subset_Iic_self <| Iic_subset_Iio.2 <| coe_lt_top b)]

@[to_dual]
/-
**WithTop.image_coe_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：image_coe_Ioo : (some : α -> WithTop α) '' Ioo a b = Ioo (a : WithTop α) b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithTop.preimage_coe_Ioo`：preimage_coe_Ioo : (some : α -> WithTop α) ⁻¹'
 Ioo a b = Ioo a b
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用定理 `WithTop.range_coe`：range_coe : range (some : α -> WithTop α) = Iio ⊤
· 使用定理 `Set.inter_eq_self_of_subset_left`：inter_eq_self_of_subset_left {s t : Se
t α} : s subseteq t -> s inter t = s
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Set.Ioo_subset_Iio_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo a b ⊆ Set.Iio b
· 使用定理 `Set.Iio_subset_Iio`：Iio_subset_Iio (h : a <= b) : Iio a subseteq Iio b
· 使用定理 `le_top`：le_top : a <= ⊤
-/
theorem image_coe_Ioo : (some : α → WithTop α) '' Ioo a b = Ioo (a : WithTop α) b := by
  rw [← preimage_coe_Ioo, image_preimage_eq_inter_range, range_coe,
    inter_eq_self_of_subset_left (Subset.trans Ioo_subset_Iio_self <| Iio_subset_Iio le_top)]

@[to_dual]
/-
**WithTop.Ioi_coe** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：Ioi_coe : Ioi (a : WithTop α) = (↑) '' (Ioi a) union {⊤}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
-/
theorem Ioi_coe : Ioi (a : WithTop α) = (↑) '' (Ioi a) ∪ {⊤} := by
  ext x; induction x <;> simp

@[to_dual]
/-
**WithTop.Ici_coe** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：Ici_coe : Ici (a : WithTop α) = (↑) '' (Ici a) union {⊤}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
-/
theorem Ici_coe : Ici (a : WithTop α) = (↑) '' (Ici a) ∪ {⊤} := by
  ext x; induction x <;> simp

@[to_dual]
/-
**WithTop.Iio_coe** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：Iio_coe : Iio (a : WithTop α) = (↑) '' (Iio a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithTop.image_coe_Iio`：image_coe_Iio : (some : α -> WithTop α) '' Iio a 
= Iio (a : WithTop α)
-/
theorem Iio_coe : Iio (a : WithTop α) = (↑) '' (Iio a) := image_coe_Iio.symm

@[to_dual]
/-
**WithTop.Iic_coe** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：Iic_coe : Iic (a : WithTop α) = (↑) '' (Iic a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithTop.image_coe_Iic`：image_coe_Iic : (some : α -> WithTop α) '' Iic a 
= Iic (a : WithTop α)
-/
theorem Iic_coe : Iic (a : WithTop α) = (↑) '' (Iic a) := image_coe_Iic.symm

@[to_dual]
/-
**WithTop.Icc_coe** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：Icc_coe : Icc (a : WithTop α) b = (↑) '' (Icc a b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithTop.image_coe_Icc`：image_coe_Icc : (some : α -> WithTop α) '' Icc a 
b = Icc (a : WithTop α) b
-/
theorem Icc_coe : Icc (a : WithTop α) b = (↑) '' (Icc a b) := image_coe_Icc.symm

@[to_dual]
/-
**WithTop.Ico_coe** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：Ico_coe : Ico (a : WithTop α) b = (↑) '' (Ico a b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithTop.image_coe_Ico`：image_coe_Ico : (some : α -> WithTop α) '' Ico a 
b = Ico (a : WithTop α) b
-/
theorem Ico_coe : Ico (a : WithTop α) b = (↑) '' (Ico a b) := image_coe_Ico.symm

@[to_dual]
/-
**WithTop.Ioc_coe** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：Ioc_coe : Ioc (a : WithTop α) b = (↑) '' (Ioc a b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithTop.image_coe_Ioc`：image_coe_Ioc : (some : α -> WithTop α) '' Ioc a 
b = Ioc (a : WithTop α) b
-/
theorem Ioc_coe : Ioc (a : WithTop α) b = (↑) '' (Ioc a b) := image_coe_Ioc.symm

@[to_dual]
/-
**WithTop.Ioo_coe** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：Ioo_coe : Ioo (a : WithTop α) b = (↑) '' (Ioo a b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithTop.image_coe_Ioo`：image_coe_Ioo : (some : α -> WithTop α) '' Ioo a 
b = Ioo (a : WithTop α) b
-/
theorem Ioo_coe : Ioo (a : WithTop α) b = (↑) '' (Ioo a b) := image_coe_Ioo.symm

end WithTop

