/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Algebra.Order.Sub.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE

/-!
# Lemmas about subtraction in an unbundled canonically ordered monoids
-/

public section

-- These are about *unbundled* canonically ordered monoids
assert_not_exists IsOrderedMonoid

variable {α : Type*}

section ExistsAddOfLE

variable [AddCommSemigroup α] [PartialOrder α] [ExistsAddOfLE α]
  [AddLeftMono α] [Sub α] [OrderedSub α] {a b c d : α}

@[simp]
/-
**add_tsub_cancel_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：add_tsub_cancel_of_le (h : a <= b) : a + (b - a) = b
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `ExistsAddOfLE.exists_add_of_le`：∀ {α : Type u} {inst : Add α} {inst_1 : 
LE α} [self : ExistsAddOfLE α] {a b : α}, a ≤ b → ∃ c, b = a + c
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `add_tsub_le_left`：add_tsub_le_left : a + b - a <= b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_add_tsub`：le_add_tsub : a <= b + (a - b)
-/
theorem add_tsub_cancel_of_le (h : a ≤ b) : a + (b - a) = b := by
  refine le_antisymm ?_ le_add_tsub
  obtain ⟨c, rfl⟩ := exists_add_of_le h
  grw [add_tsub_le_left]
/-
**tsub_add_cancel_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsub_add_cancel_of_le (h : a <= b) : b - a + a = b
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `add_tsub_cancel_of_le`：add_tsub_cancel_of_le (h : a <= b) : a + (b - a) 
= b
-/
theorem tsub_add_cancel_of_le (h : a ≤ b) : b - a + a = b := by
  rw [add_comm]
  exact add_tsub_cancel_of_le h
/-
**add_le_of_le_tsub_right_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：add_le_of_le_tsub_right_of_le (h : b <= c) (h2 : a <= c - b) : a + b <= c
参数：h : b <= c；h2 : a <= c - b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
-/
theorem add_le_of_le_tsub_right_of_le (h : b ≤ c) (h2 : a ≤ c - b) : a + b ≤ c := by
  grw [h2, tsub_add_cancel_of_le h]
/-
**add_le_of_le_tsub_left_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：add_le_of_le_tsub_left_of_le (h : a <= c) (h2 : b <= c - a) : a + b <= c
参数：h : a <= c；h2 : b <= c - a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_tsub_cancel_of_le`：add_tsub_cancel_of_le (h : a <= b) : a + (b - a) 
= b
-/
theorem add_le_of_le_tsub_left_of_le (h : a ≤ c) (h2 : b ≤ c - a) : a + b ≤ c := by
  grw [h2, add_tsub_cancel_of_le h]
/-
**tsub_le_tsub_iff_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsub_le_tsub_iff_right (h : c <= b) : a - c <= b - c ↔ a <= b
参数：h : c <= b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tsub_le_iff_right`：tsub_le_iff_right [LE α] [Add α] [Sub α] [OrderedSub 
α] {a b c : α} : a - b <= c ↔ a <= c + b
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem tsub_le_tsub_iff_right (h : c ≤ b) : a - c ≤ b - c ↔ a ≤ b := by
  rw [tsub_le_iff_right, tsub_add_cancel_of_le h]
/-
**tsub_left_inj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsub_left_inj (h1 : c <= a) (h2 : c <= b) : a - c = b - c ↔ a = b
参数：h1 : c <= a；h2 : c <= b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `tsub_le_tsub_iff_right`：tsub_le_tsub_iff_right (h : c <= b) : a - c <= b
 - c ↔ a <= b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem tsub_left_inj (h1 : c ≤ a) (h2 : c ≤ b) : a - c = b - c ↔ a = b := by
  simp_rw [le_antisymm_iff, tsub_le_tsub_iff_right h1, tsub_le_tsub_iff_right h2]
/-
**tsub_inj_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsub_inj_left (h₁ : a <= b) (h₂ : a <= c) : b - a = c - a -> b = c
参数：h₁ : a <= b；h₂ : a <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `tsub_left_inj`：tsub_left_inj (h1 : c <= a) (h2 : c <= b) : a - c = b - c
 ↔ a = b
-/
theorem tsub_inj_left (h₁ : a ≤ b) (h₂ : a ≤ c) : b - a = c - a → b = c :=
  (tsub_left_inj h₁ h₂).1

/-- See `lt_of_tsub_lt_tsub_right` for a stronger statement in a linear order. -/
/-
**lt_of_tsub_lt_tsub_right_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_of_tsub_lt_tsub_right_of_le (h : c <= b) (h2 : a - c < b - c) : a < b
参数：h : c <= b；h2 : a - c < b - c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `tsub_le_tsub_iff_right`：tsub_le_tsub_iff_right (h : c <= b) : a - c <= b
 - c ↔ a <= b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LT.lt.false`：∀ {α : Type u_2} [inst : Preorder α] {a : α}, a < a → False

--- 原说明 ---
See `lt_of_tsub_lt_tsub_right` for a stronger statement in a linear order.
-/
theorem lt_of_tsub_lt_tsub_right_of_le (h : c ≤ b) (h2 : a - c < b - c) : a < b := by
  refine ((tsub_le_tsub_iff_right h).mp h2.le).lt_of_ne ?_
  rintro rfl
  exact h2.false
/-
**tsub_add_tsub_cancel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsub_add_tsub_cancel (hab : b <= a) (hcb : c <= b) : a - b + (b - c) = a -
 c
参数：hab : b <= a；hcb : c <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tsub_tsub`：tsub_tsub (b a c : α) : b - a - c = b - (a + c)
· 使用定理 `add_tsub_cancel_of_le`：add_tsub_cancel_of_le (h : a <= b) : a + (b - a) 
= b
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
· 使用定理 `tsub_le_tsub_right`：tsub_le_tsub_right (h : a <= b) (c : α) : a - c <= b
 - c
-/
theorem tsub_add_tsub_cancel (hab : b ≤ a) (hcb : c ≤ b) : a - b + (b - c) = a - c := by
  convert! tsub_add_cancel_of_le (tsub_le_tsub_right hab c) using 2
  rw [tsub_tsub, add_tsub_cancel_of_le hcb]
/-
**tsub_tsub_tsub_cancel_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsub_tsub_tsub_cancel_right (h : c <= b) : a - c - (b - c) = a - b
参数：h : c <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tsub_tsub`：tsub_tsub (b a c : α) : b - a - c = b - (a + c)
· 使用定理 `add_tsub_cancel_of_le`：add_tsub_cancel_of_le (h : a <= b) : a + (b - a) 
= b
-/
theorem tsub_tsub_tsub_cancel_right (h : c ≤ b) : a - c - (b - c) = a - b := by
  rw [tsub_tsub, add_tsub_cancel_of_le h]

/-! #### Lemmas that assume that an element is `AddLECancellable`. -/


namespace AddLECancellable

/-
**AddLECancellable.eq_tsub_iff_add_eq_of_le** 是 Mathlib 中的一个定理，位于命名空间 `AddLECanc
ellable`。
形式化陈述：∀ {α : Type u_1} [inst : AddCommSemigroup α] [inst_1 : PartialOrder α] [Ex
istsAddOfLE α] [AddLeftMono α]   [inst_4 : Sub α] [OrderedSub α] {a b c : α}, Ad
dLECancellable c → c ≤ b → (a = b - c ↔ a + c = b)
参数：a = b - c ↔ a + c = b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddLECancellable.eq_tsub_of_add_eq`：∀ {α : Type u_1} [inst : PartialOrde
r α] [inst_1 : AddCommSemigroup α] [inst_2 : Sub α] [OrderedSub α] {a b c : α}, 
  AddLECancellable c → a…
-/
protected theorem eq_tsub_iff_add_eq_of_le (hc : AddLECancellable c) (h : c ≤ b) :
    a = b - c ↔ a + c = b :=
  ⟨by
    rintro rfl
    exact tsub_add_cancel_of_le h, hc.eq_tsub_of_add_eq⟩
/-
**AddLECancellable.tsub_eq_iff_eq_add_of_le** 是 Mathlib 中的一个定理，位于命名空间 `AddLECanc
ellable`。
形式化陈述：∀ {α : Type u_1} [inst : AddCommSemigroup α] [inst_1 : PartialOrder α] [Ex
istsAddOfLE α] [AddLeftMono α]   [inst_4 : Sub α] [OrderedSub α] {a b c : α}, Ad
dLECancellable b → b ≤ a → (a - b = c ↔ a = c + b)
参数：a - b = c ↔ a = c + b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `AddLECancellable.eq_tsub_iff_add_eq_of_le`：∀ {α : Type u_1} [inst : AddC
ommSemigroup α] [inst_1 : PartialOrder α] [ExistsAddOfLE α] [AddLeftMono α]   [i
nst_4 : Sub α] [OrderedSub α] {…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected theorem tsub_eq_iff_eq_add_of_le (hb : AddLECancellable b) (h : b ≤ a) :
    a - b = c ↔ a = c + b := by rw [eq_comm, hb.eq_tsub_iff_add_eq_of_le h, eq_comm]
/-
**AddLECancellable.add_tsub_assoc_of_le** 是 Mathlib 中的一个定理，位于命名空间 `AddLECancella
ble`。
形式化陈述：∀ {α : Type u_1} [inst : AddCommSemigroup α] [inst_1 : PartialOrder α] [Ex
istsAddOfLE α] [AddLeftMono α]   [inst_4 : Sub α] [OrderedSub α] {b c : α}, AddL
ECancellable c → c ≤ b → ∀ (a : α), a + b - c = a + (b - c)
参数：a : α；b - c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_tsub_cancel_of_le`：add_tsub_cancel_of_le (h : a <= b) : a + (b - a) 
= b
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `AddLECancellable.add_tsub_cancel_right`：∀ {α : Type u_1} [inst : Partial
Order α] [inst_1 : AddCommSemigroup α] [inst_2 : Sub α] [OrderedSub α] {a b : α}
,   AddLECancellable b → a +…
-/
protected theorem add_tsub_assoc_of_le (hc : AddLECancellable c) (h : c ≤ b) (a : α) :
    a + b - c = a + (b - c) := by
  conv_lhs => rw [← add_tsub_cancel_of_le h, add_comm c, ← add_assoc, hc.add_tsub_cancel_right]
/-
**AddLECancellable.tsub_add_eq_add_tsub** 是 Mathlib 中的一个定理，位于命名空间 `AddLECancella
ble`。
形式化陈述：∀ {α : Type u_1} [inst : AddCommSemigroup α] [inst_1 : PartialOrder α] [Ex
istsAddOfLE α] [AddLeftMono α]   [inst_4 : Sub α] [OrderedSub α] {a b c : α}, Ad
dLECancellable b → b ≤ a → a - b + c = a + c - b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `AddLECancellable.add_tsub_assoc_of_le`：∀ {α : Type u_1} [inst : AddCommS
emigroup α] [inst_1 : PartialOrder α] [ExistsAddOfLE α] [AddLeftMono α]   [inst_
4 : Sub α] [OrderedSub α] {…
-/
protected theorem tsub_add_eq_add_tsub (hb : AddLECancellable b) (h : b ≤ a) :
    a - b + c = a + c - b := by rw [add_comm a, hb.add_tsub_assoc_of_le h, add_comm]
/-
**AddLECancellable.tsub_tsub_assoc** 是 Mathlib 中的一个定理，位于命名空间 `AddLECancellable`。
形式化陈述：∀ {α : Type u_1} [inst : AddCommSemigroup α] [inst_1 : PartialOrder α] [Ex
istsAddOfLE α] [AddLeftMono α]   [inst_4 : Sub α] [OrderedSub α] {a b c : α}, Ad
dLECancellable (b - c) → b ≤ a → c ≤ b → a - (b - c) = a - b + c
参数：b - c；b - c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.tsub_eq_of_eq_add`：∀ {α : Type u_1} [inst : PartialOrde
r α] [inst_1 : AddCommSemigroup α] [inst_2 : Sub α] [OrderedSub α] {a b c : α}, 
  AddLECancellable b → a…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `add_tsub_cancel_of_le`：add_tsub_cancel_of_le (h : a <= b) : a + (b - a) 
= b
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
-/
protected theorem tsub_tsub_assoc (hbc : AddLECancellable (b - c)) (h₁ : b ≤ a) (h₂ : c ≤ b) :
    a - (b - c) = a - b + c :=
  hbc.tsub_eq_of_eq_add <| by rw [add_assoc, add_tsub_cancel_of_le h₂, tsub_add_cancel_of_le h₁]
/-
**AddLECancellable.tsub_add_tsub_comm** 是 Mathlib 中的一个定理，位于命名空间 `AddLECancellabl
e`。
形式化陈述：∀ {α : Type u_1} [inst : AddCommSemigroup α] [inst_1 : PartialOrder α] [Ex
istsAddOfLE α] [AddLeftMono α]   [inst_4 : Sub α] [OrderedSub α] {a b c d : α}, 
  AddLECancellable b → AddLECancellable d → b ≤ a → d ≤ c → a - b + (c - d) = a 
+ c - (b + d)
参数：c - d；b + d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddLECancellable.tsub_add_eq_add_tsub`：∀ {α : Type u_1} [inst : AddCommS
emigroup α] [inst_1 : PartialOrder α] [ExistsAddOfLE α] [AddLeftMono α]   [inst_
4 : Sub α] [OrderedSub α] {…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddLECancellable.add_tsub_assoc_of_le`：∀ {α : Type u_1} [inst : AddCommS
emigroup α] [inst_1 : PartialOrder α] [ExistsAddOfLE α] [AddLeftMono α]   [inst_
4 : Sub α] [OrderedSub α] {…
· 使用定理 `tsub_tsub`：tsub_tsub (b a c : α) : b - a - c = b - (a + c)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
protected theorem tsub_add_tsub_comm (hb : AddLECancellable b) (hd : AddLECancellable d)
    (hba : b ≤ a) (hdc : d ≤ c) : a - b + (c - d) = a + c - (b + d) := by
  rw [hb.tsub_add_eq_add_tsub hba, ← hd.add_tsub_assoc_of_le hdc, tsub_tsub, add_comm d]
/-
**AddLECancellable.le_tsub_iff_left** 是 Mathlib 中的一个定理，位于命名空间 `AddLECancellable`
。
形式化陈述：∀ {α : Type u_1} [inst : AddCommSemigroup α] [inst_1 : PartialOrder α] [Ex
istsAddOfLE α] [AddLeftMono α]   [inst_4 : Sub α] [OrderedSub α] {a b c : α}, Ad
dLECancellable a → a ≤ c → (b ≤ c - a ↔ a + b ≤ c)
参数：b ≤ c - a ↔ a + b ≤ c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_le_of_le_tsub_left_of_le`：add_le_of_le_tsub_left_of_le (h : a <= c) 
(h2 : b <= c - a) : a + b <= c
· 使用定理 `AddLECancellable.le_tsub_of_add_le_left`：∀ {α : Type u_1} [inst : Preord
er α] [inst_1 : AddCommSemigroup α] [inst_2 : Sub α] [OrderedSub α] {a b c : α},
   AddLECancellable a → a + b…
-/
protected theorem le_tsub_iff_left (ha : AddLECancellable a) (h : a ≤ c) : b ≤ c - a ↔ a + b ≤ c :=
  ⟨add_le_of_le_tsub_left_of_le h, ha.le_tsub_of_add_le_left⟩
/-
**AddLECancellable.le_tsub_iff_right** 是 Mathlib 中的一个定理，位于命名空间 `AddLECancellable
`。
形式化陈述：∀ {α : Type u_1} [inst : AddCommSemigroup α] [inst_1 : PartialOrder α] [Ex
istsAddOfLE α] [AddLeftMono α]   [inst_4 : Sub α] [OrderedSub α] {a b c : α}, Ad
dLECancellable a → a ≤ c → (b ≤ c - a ↔ b + a ≤ c)
参数：b ≤ c - a ↔ b + a ≤ c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `AddLECancellable.le_tsub_iff_left`：∀ {α : Type u_1} [inst : AddCommSemig
roup α] [inst_1 : PartialOrder α] [ExistsAddOfLE α] [AddLeftMono α]   [inst_4 : 
Sub α] [OrderedSub α] {…
-/
protected theorem le_tsub_iff_right (ha : AddLECancellable a) (h : a ≤ c) :
    b ≤ c - a ↔ b + a ≤ c := by
  rw [add_comm]
  exact ha.le_tsub_iff_left h
/-
**AddLECancellable.tsub_lt_iff_left** 是 Mathlib 中的一个定理，位于命名空间 `AddLECancellable`
。
形式化陈述：∀ {α : Type u_1} [inst : AddCommSemigroup α] [inst_1 : PartialOrder α] [Ex
istsAddOfLE α] [AddLeftMono α]   [inst_4 : Sub α] [OrderedSub α] {a b c : α}, Ad
dLECancellable b → b ≤ a → (a - b < c ↔ a < b + c)
参数：a - b < c ↔ a < b + c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.lt_add_of_tsub_lt_left`：∀ {α : Type u_1} [inst : Partia
lOrder α] [inst_1 : AddCommSemigroup α] [inst_2 : Sub α] [OrderedSub α] {a b c :
 α},   AddLECancellable b → a…
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tsub_le_iff_left`：tsub_le_iff_left : a - b <= c ↔ a <= b + c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `add_tsub_cancel_of_le`：add_tsub_cancel_of_le (h : a <= b) : a + (b - a) 
= b
-/
protected theorem tsub_lt_iff_left (hb : AddLECancellable b) (hba : b ≤ a) :
    a - b < c ↔ a < b + c := by
  refine ⟨hb.lt_add_of_tsub_lt_left, ?_⟩
  intro h; refine (tsub_le_iff_left.mpr h.le).lt_of_ne ?_
  rintro rfl; exact h.ne' (add_tsub_cancel_of_le hba)
/-
**AddLECancellable.tsub_lt_iff_right** 是 Mathlib 中的一个定理，位于命名空间 `AddLECancellable
`。
形式化陈述：∀ {α : Type u_1} [inst : AddCommSemigroup α] [inst_1 : PartialOrder α] [Ex
istsAddOfLE α] [AddLeftMono α]   [inst_4 : Sub α] [OrderedSub α] {a b c : α}, Ad
dLECancellable b → b ≤ a → (a - b < c ↔ a < c + b)
参数：a - b < c ↔ a < c + b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `AddLECancellable.tsub_lt_iff_left`：∀ {α : Type u_1} [inst : AddCommSemig
roup α] [inst_1 : PartialOrder α] [ExistsAddOfLE α] [AddLeftMono α]   [inst_4 : 
Sub α] [OrderedSub α] {…
-/
protected theorem tsub_lt_iff_right (hb : AddLECancellable b) (hba : b ≤ a) :
    a - b < c ↔ a < c + b := by
  rw [add_comm]
  exact hb.tsub_lt_iff_left hba
/-
**AddLECancellable.tsub_lt_iff_tsub_lt** 是 Mathlib 中的一个定理，位于命名空间 `AddLECancellab
le`。
形式化陈述：∀ {α : Type u_1} [inst : AddCommSemigroup α] [inst_1 : PartialOrder α] [Ex
istsAddOfLE α] [AddLeftMono α]   [inst_4 : Sub α] [OrderedSub α] {a b c : α},   
AddLECancellable b → AddLECancellable c → b ≤ a → c ≤ a → (a - b < c ↔ a - c < b
)
参数：a - b < c ↔ a - c < b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddLECancellable.tsub_lt_iff_left`：∀ {α : Type u_1} [inst : AddCommSemig
roup α] [inst_1 : PartialOrder α] [ExistsAddOfLE α] [AddLeftMono α]   [inst_4 : 
Sub α] [OrderedSub α] {…
· 使用定理 `AddLECancellable.tsub_lt_iff_right`：∀ {α : Type u_1} [inst : AddCommSemi
group α] [inst_1 : PartialOrder α] [ExistsAddOfLE α] [AddLeftMono α]   [inst_4 :
 Sub α] [OrderedSub α] {…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected theorem tsub_lt_iff_tsub_lt (hb : AddLECancellable b) (hc : AddLECancellable c)
    (h₁ : b ≤ a) (h₂ : c ≤ a) : a - b < c ↔ a - c < b := by
  rw [hb.tsub_lt_iff_left h₁, hc.tsub_lt_iff_right h₂]
/-
**AddLECancellable.le_tsub_iff_le_tsub** 是 Mathlib 中的一个定理，位于命名空间 `AddLECancellab
le`。
形式化陈述：∀ {α : Type u_1} [inst : AddCommSemigroup α] [inst_1 : PartialOrder α] [Ex
istsAddOfLE α] [AddLeftMono α]   [inst_4 : Sub α] [OrderedSub α] {a b c : α},   
AddLECancellable a → AddLECancellable c → a ≤ b → c ≤ b → (a ≤ b - c ↔ c ≤ b - a
)
参数：a ≤ b - c ↔ c ≤ b - a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddLECancellable.le_tsub_iff_left`：∀ {α : Type u_1} [inst : AddCommSemig
roup α] [inst_1 : PartialOrder α] [ExistsAddOfLE α] [AddLeftMono α]   [inst_4 : 
Sub α] [OrderedSub α] {…
· 使用定理 `AddLECancellable.le_tsub_iff_right`：∀ {α : Type u_1} [inst : AddCommSemi
group α] [inst_1 : PartialOrder α] [ExistsAddOfLE α] [AddLeftMono α]   [inst_4 :
 Sub α] [OrderedSub α] {…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected theorem le_tsub_iff_le_tsub (ha : AddLECancellable a) (hc : AddLECancellable c)
    (h₁ : a ≤ b) (h₂ : c ≤ b) : a ≤ b - c ↔ c ≤ b - a := by
  rw [ha.le_tsub_iff_left h₁, hc.le_tsub_iff_right h₂]
/-
**AddLECancellable.lt_tsub_iff_right_of_le** 是 Mathlib 中的一个定理，位于命名空间 `AddLECance
llable`。
形式化陈述：∀ {α : Type u_1} [inst : AddCommSemigroup α] [inst_1 : PartialOrder α] [Ex
istsAddOfLE α] [AddLeftMono α]   [inst_4 : Sub α] [OrderedSub α] {a b c : α}, Ad
dLECancellable c → c ≤ b → (a < b - c ↔ a + c < b)
参数：a < b - c ↔ a + c < b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用定理 `add_le_of_le_tsub_right_of_le`：add_le_of_le_tsub_right_of_le (h : b <= c
) (h2 : a <= c - b) : a + b <= c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `AddLECancellable.add_tsub_cancel_right`：∀ {α : Type u_1} [inst : Partial
Order α] [inst_1 : AddCommSemigroup α] [inst_2 : Sub α] [OrderedSub α] {a b : α}
,   AddLECancellable b → a +…
· 使用定理 `AddLECancellable.lt_tsub_of_add_lt_right`：∀ {α : Type u_1} [inst : Parti
alOrder α] [inst_1 : AddCommSemigroup α] [inst_2 : Sub α] [OrderedSub α] {a b c 
: α},   AddLECancellable c → a…
-/
protected theorem lt_tsub_iff_right_of_le (hc : AddLECancellable c) (h : c ≤ b) :
    a < b - c ↔ a + c < b := by
  refine ⟨fun h' => (add_le_of_le_tsub_right_of_le h h'.le).lt_of_ne ?_, hc.lt_tsub_of_add_lt_right⟩
  rintro rfl
  exact h'.ne' hc.add_tsub_cancel_right
/-
**AddLECancellable.lt_tsub_iff_left_of_le** 是 Mathlib 中的一个定理，位于命名空间 `AddLECancel
lable`。
形式化陈述：∀ {α : Type u_1} [inst : AddCommSemigroup α] [inst_1 : PartialOrder α] [Ex
istsAddOfLE α] [AddLeftMono α]   [inst_4 : Sub α] [OrderedSub α] {a b c : α}, Ad
dLECancellable c → c ≤ b → (a < b - c ↔ c + a < b)
参数：a < b - c ↔ c + a < b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `AddLECancellable.lt_tsub_iff_right_of_le`：∀ {α : Type u_1} [inst : AddCo
mmSemigroup α] [inst_1 : PartialOrder α] [ExistsAddOfLE α] [AddLeftMono α]   [in
st_4 : Sub α] [OrderedSub α] {…
-/
protected theorem lt_tsub_iff_left_of_le (hc : AddLECancellable c) (h : c ≤ b) :
    a < b - c ↔ c + a < b := by
  rw [add_comm]
  exact hc.lt_tsub_iff_right_of_le h
/-
**AddLECancellable.tsub_inj_right** 是 Mathlib 中的一个定理，位于命名空间 `AddLECancellable`。
形式化陈述：∀ {α : Type u_1} [inst : AddCommSemigroup α] [inst_1 : PartialOrder α] [Ex
istsAddOfLE α] [AddLeftMono α]   [inst_4 : Sub α] [OrderedSub α] {a b c : α}, Ad
dLECancellable (a - b) → b ≤ a → c ≤ a → a - b = a - c → b = c
参数：a - b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddLECancellable.inj`：∀ {α : Type u_1} [inst : Add α] [inst_1 : PartialO
rder α] {a b c : α}, AddLECancellable a → (a + b = a + c ↔ b = c)
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
-/
protected theorem tsub_inj_right (hab : AddLECancellable (a - b)) (h₁ : b ≤ a) (h₂ : c ≤ a)
    (h₃ : a - b = a - c) : b = c := by
  rw [← hab.inj]
  rw [tsub_add_cancel_of_le h₁, h₃, tsub_add_cancel_of_le h₂]
/-
**AddLECancellable.lt_of_tsub_lt_tsub_left_of_le** 是 Mathlib 中的一个定理，位于命名空间 `AddL
ECancellable`。
形式化陈述：∀ {α : Type u_1} [inst : AddCommSemigroup α] [inst_1 : PartialOrder α] [Ex
istsAddOfLE α] [AddLeftMono α]   [inst_4 : Sub α] [OrderedSub α] {a b c : α} [Ad
dLeftReflectLT α], AddLECancellable b → c ≤ a → a - b < a - c → c < b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_of_add_lt_add_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [
AddLeftReflectLT α] {a b c : α}, a + b < a + c → b < c
· 使用定理 `AddLECancellable.lt_add_of_tsub_lt_right`：∀ {α : Type u_1} [inst : Parti
alOrder α] [inst_1 : AddCommSemigroup α] [inst_2 : Sub α] [OrderedSub α] {a b c 
: α},   AddLECancellable c → a…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
-/
protected theorem lt_of_tsub_lt_tsub_left_of_le [AddLeftReflectLT α]
    (hb : AddLECancellable b) (hca : c ≤ a) (h : a - b < a - c) : c < b := by
  conv_lhs at h => rw [← tsub_add_cancel_of_le hca]
  exact lt_of_add_lt_add_left (hb.lt_add_of_tsub_lt_right h)
/-
**AddLECancellable.tsub_lt_tsub_left_of_le** 是 Mathlib 中的一个定理，位于命名空间 `AddLECance
llable`。
形式化陈述：∀ {α : Type u_1} [inst : AddCommSemigroup α] [inst_1 : PartialOrder α] [Ex
istsAddOfLE α] [AddLeftMono α]   [inst_4 : Sub α] [OrderedSub α] {a b c : α}, Ad
dLECancellable (a - b) → b ≤ a → c < b → a - b < a - c
参数：a - b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用定理 `tsub_le_tsub_left`：tsub_le_tsub_left (h : a <= b) (c : α) : c - b <= c -
 a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `AddLECancellable.tsub_inj_right`：∀ {α : Type u_1} [inst : AddCommSemigro
up α] [inst_1 : PartialOrder α] [ExistsAddOfLE α] [AddLeftMono α]   [inst_4 : Su
b α] [OrderedSub α] {…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
protected theorem tsub_lt_tsub_left_of_le (hab : AddLECancellable (a - b)) (h₁ : b ≤ a)
    (h : c < b) : a - b < a - c :=
  (tsub_le_tsub_left h.le _).lt_of_ne fun h' => h.ne' <| hab.tsub_inj_right h₁ (h.le.trans h₁) h'
/-
**AddLECancellable.tsub_lt_tsub_right_of_le** 是 Mathlib 中的一个定理，位于命名空间 `AddLECanc
ellable`。
形式化陈述：∀ {α : Type u_1} [inst : AddCommSemigroup α] [inst_1 : PartialOrder α] [Ex
istsAddOfLE α] [AddLeftMono α]   [inst_4 : Sub α] [OrderedSub α] {a b c : α}, Ad
dLECancellable c → c ≤ a → a < b → a - c < b - c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.lt_tsub_of_add_lt_left`：∀ {α : Type u_1} [inst : Partia
lOrder α] [inst_1 : AddCommSemigroup α] [inst_2 : Sub α] [OrderedSub α] {a b c :
 α},   AddLECancellable a → a…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_tsub_cancel_of_le`：add_tsub_cancel_of_le (h : a <= b) : a + (b - a) 
= b
-/
protected theorem tsub_lt_tsub_right_of_le (hc : AddLECancellable c) (h : c ≤ a) (h2 : a < b) :
    a - c < b - c := by
  apply hc.lt_tsub_of_add_lt_left
  rwa [add_tsub_cancel_of_le h]
/-
**AddLECancellable.tsub_lt_tsub_iff_left_of_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 `
AddLECancellable`。
形式化陈述：∀ {α : Type u_1} [inst : AddCommSemigroup α] [inst_1 : PartialOrder α] [Ex
istsAddOfLE α] [AddLeftMono α]   [inst_4 : Sub α] [OrderedSub α] {a b c : α} [Ad
dLeftReflectLT α],   AddLECancellable b → AddLECancellable (a - b) → b ≤ a → c ≤
 a → (a - b < a - c ↔ c < b)
参数：a - b；a - b < a - c ↔ c < b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.lt_of_tsub_lt_tsub_left_of_le`：∀ {α : Type u_1} [inst :
 AddCommSemigroup α] [inst_1 : PartialOrder α] [ExistsAddOfLE α] [AddLeftMono α]
   [inst_4 : Sub α] [OrderedSub α] {…
· 使用定理 `AddLECancellable.tsub_lt_tsub_left_of_le`：∀ {α : Type u_1} [inst : AddCo
mmSemigroup α] [inst_1 : PartialOrder α] [ExistsAddOfLE α] [AddLeftMono α]   [in
st_4 : Sub α] [OrderedSub α] {…
-/
protected theorem tsub_lt_tsub_iff_left_of_le_of_le [AddLeftReflectLT α]
    (hb : AddLECancellable b) (hab : AddLECancellable (a - b)) (h₁ : b ≤ a) (h₂ : c ≤ a) :
    a - b < a - c ↔ c < b :=
  ⟨hb.lt_of_tsub_lt_tsub_left_of_le h₂, hab.tsub_lt_tsub_left_of_le h₁⟩

@[simp]
/-
**AddLECancellable.add_add_tsub_cancel** 是 Mathlib 中的一个定理，位于命名空间 `AddLECancellab
le`。
形式化陈述：∀ {α : Type u_1} [inst : AddCommSemigroup α] [inst_1 : PartialOrder α] [Ex
istsAddOfLE α] [AddLeftMono α]   [inst_4 : Sub α] [OrderedSub α] {a b c : α}, Ad
dLECancellable c → c ≤ b → a + c + (b - c) = a + b
参数：b - c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddLECancellable.add_tsub_assoc_of_le`：∀ {α : Type u_1} [inst : AddCommS
emigroup α] [inst_1 : PartialOrder α] [ExistsAddOfLE α] [AddLeftMono α]   [inst_
4 : Sub α] [OrderedSub α] {…
· 使用定理 `add_right_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G)
, a + b + c = a + c + b
· 使用定理 `AddLECancellable.add_tsub_cancel_right`：∀ {α : Type u_1} [inst : Partial
Order α] [inst_1 : AddCommSemigroup α] [inst_2 : Sub α] [OrderedSub α] {a b : α}
,   AddLECancellable b → a +…
-/
protected lemma add_add_tsub_cancel (hc : AddLECancellable c) (hcb : c ≤ b) :
    a + c + (b - c) = a + b := by
  rw [← hc.add_tsub_assoc_of_le hcb, add_right_comm, hc.add_tsub_cancel_right]

@[simp]
/-
**AddLECancellable.add_tsub_tsub_cancel** 是 Mathlib 中的一个定理，位于命名空间 `AddLECancella
ble`。
形式化陈述：∀ {α : Type u_1} [inst : AddCommSemigroup α] [inst_1 : PartialOrder α] [Ex
istsAddOfLE α] [AddLeftMono α]   [inst_4 : Sub α] [OrderedSub α] {a b c : α}, Ad
dLECancellable (a - c) → c ≤ a → a + b - (a - c) = b + c
参数：a - c；a - c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.tsub_eq_of_eq_add`：∀ {α : Type u_1} [inst : PartialOrde
r α] [inst_1 : AddCommSemigroup α] [inst_2 : Sub α] [OrderedSub α] {a b c : α}, 
  AddLECancellable b → a…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `add_tsub_cancel_of_le`：add_tsub_cancel_of_le (h : a <= b) : a + (b - a) 
= b
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
protected theorem add_tsub_tsub_cancel (hac : AddLECancellable (a - c)) (h : c ≤ a) :
    a + b - (a - c) = b + c :=
  hac.tsub_eq_of_eq_add <| by rw [add_assoc, add_tsub_cancel_of_le h, add_comm]
/-
**AddLECancellable.tsub_tsub_cancel_of_le** 是 Mathlib 中的一个定理，位于命名空间 `AddLECancel
lable`。
形式化陈述：∀ {α : Type u_1} [inst : AddCommSemigroup α] [inst_1 : PartialOrder α] [Ex
istsAddOfLE α] [AddLeftMono α]   [inst_4 : Sub α] [OrderedSub α] {a b : α}, AddL
ECancellable (b - a) → a ≤ b → b - (b - a) = a
参数：b - a；b - a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.tsub_eq_of_eq_add`：∀ {α : Type u_1} [inst : PartialOrde
r α] [inst_1 : AddCommSemigroup α] [inst_2 : Sub α] [OrderedSub α] {a b c : α}, 
  AddLECancellable b → a…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_tsub_cancel_of_le`：add_tsub_cancel_of_le (h : a <= b) : a + (b - a) 
= b
-/
protected theorem tsub_tsub_cancel_of_le (hba : AddLECancellable (b - a)) (h : a ≤ b) :
    b - (b - a) = a :=
  hba.tsub_eq_of_eq_add (add_tsub_cancel_of_le h).symm
/-
**AddLECancellable.tsub_tsub_tsub_cancel_left** 是 Mathlib 中的一个定理，位于命名空间 `AddLECa
ncellable`。
形式化陈述：∀ {α : Type u_1} [inst : AddCommSemigroup α] [inst_1 : PartialOrder α] [Ex
istsAddOfLE α] [AddLeftMono α]   [inst_4 : Sub α] [OrderedSub α] {a b c : α}, Ad
dLECancellable (a - b) → b ≤ a → a - c - (a - b) = b - c
参数：a - b；a - b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tsub_right_comm`：tsub_right_comm : a - b - c = a - c - b
· 使用定理 `AddLECancellable.tsub_tsub_cancel_of_le`：∀ {α : Type u_1} [inst : AddCom
mSemigroup α] [inst_1 : PartialOrder α] [ExistsAddOfLE α] [AddLeftMono α]   [ins
t_4 : Sub α] [OrderedSub α] {…
-/
protected theorem tsub_tsub_tsub_cancel_left (hab : AddLECancellable (a - b)) (h : b ≤ a) :
    a - c - (a - b) = b - c := by rw [tsub_right_comm, hab.tsub_tsub_cancel_of_le h]

end AddLECancellable

section Contra

/-! ### Lemmas where addition is order-reflecting. -/


variable [AddLeftReflectLE α]

/-
**eq_tsub_iff_add_eq_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_tsub_iff_add_eq_of_le (h : c <= b) : a = b - c ↔ a + c = b
参数：h : c <= b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.eq_tsub_iff_add_eq_of_le`：∀ {α : Type u_1} [inst : AddC
ommSemigroup α] [inst_1 : PartialOrder α] [ExistsAddOfLE α] [AddLeftMono α]   [i
nst_4 : Sub α] [OrderedSub α] {…
· 使用定理 `Contravariant.AddLECancellable`：∀ {α : Type u_1} [inst : Add α] [inst_1 
: LE α] [AddLeftReflectLE α] {a : α}, AddLECancellable a
-/
theorem eq_tsub_iff_add_eq_of_le (h : c ≤ b) : a = b - c ↔ a + c = b :=
  Contravariant.AddLECancellable.eq_tsub_iff_add_eq_of_le h
/-
**tsub_eq_iff_eq_add_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsub_eq_iff_eq_add_of_le (h : b <= a) : a - b = c ↔ a = c + b
参数：h : b <= a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.tsub_eq_iff_eq_add_of_le`：∀ {α : Type u_1} [inst : AddC
ommSemigroup α] [inst_1 : PartialOrder α] [ExistsAddOfLE α] [AddLeftMono α]   [i
nst_4 : Sub α] [OrderedSub α] {…
· 使用定理 `Contravariant.AddLECancellable`：∀ {α : Type u_1} [inst : Add α] [inst_1 
: LE α] [AddLeftReflectLE α] {a : α}, AddLECancellable a
-/
theorem tsub_eq_iff_eq_add_of_le (h : b ≤ a) : a - b = c ↔ a = c + b :=
  Contravariant.AddLECancellable.tsub_eq_iff_eq_add_of_le h

/-- See `add_tsub_le_assoc` for an inequality. -/
/-
**add_tsub_assoc_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：add_tsub_assoc_of_le (h : c <= b) (a : α) : a + b - c = a + (b - c)
参数：h : c <= b；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.add_tsub_assoc_of_le`：∀ {α : Type u_1} [inst : AddCommS
emigroup α] [inst_1 : PartialOrder α] [ExistsAddOfLE α] [AddLeftMono α]   [inst_
4 : Sub α] [OrderedSub α] {…
· 使用定理 `Contravariant.AddLECancellable`：∀ {α : Type u_1} [inst : Add α] [inst_1 
: LE α] [AddLeftReflectLE α] {a : α}, AddLECancellable a

--- 原说明 ---
See `add_tsub_le_assoc` for an inequality.
-/
theorem add_tsub_assoc_of_le (h : c ≤ b) (a : α) : a + b - c = a + (b - c) :=
  Contravariant.AddLECancellable.add_tsub_assoc_of_le h a
/-
**tsub_add_eq_add_tsub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsub_add_eq_add_tsub (h : b <= a) : a - b + c = a + c - b
参数：h : b <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.tsub_add_eq_add_tsub`：∀ {α : Type u_1} [inst : AddCommS
emigroup α] [inst_1 : PartialOrder α] [ExistsAddOfLE α] [AddLeftMono α]   [inst_
4 : Sub α] [OrderedSub α] {…
· 使用定理 `Contravariant.AddLECancellable`：∀ {α : Type u_1} [inst : Add α] [inst_1 
: LE α] [AddLeftReflectLE α] {a : α}, AddLECancellable a
-/
theorem tsub_add_eq_add_tsub (h : b ≤ a) : a - b + c = a + c - b :=
  Contravariant.AddLECancellable.tsub_add_eq_add_tsub h
/-
**tsub_tsub_assoc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsub_tsub_assoc (h₁ : b <= a) (h₂ : c <= b) : a - (b - c) = a - b + c
参数：h₁ : b <= a；h₂ : c <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.tsub_tsub_assoc`：∀ {α : Type u_1} [inst : AddCommSemigr
oup α] [inst_1 : PartialOrder α] [ExistsAddOfLE α] [AddLeftMono α]   [inst_4 : S
ub α] [OrderedSub α] {…
· 使用定理 `Contravariant.AddLECancellable`：∀ {α : Type u_1} [inst : Add α] [inst_1 
: LE α] [AddLeftReflectLE α] {a : α}, AddLECancellable a
-/
theorem tsub_tsub_assoc (h₁ : b ≤ a) (h₂ : c ≤ b) : a - (b - c) = a - b + c :=
  Contravariant.AddLECancellable.tsub_tsub_assoc h₁ h₂
/-
**tsub_add_tsub_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsub_add_tsub_comm (hba : b <= a) (hdc : d <= c) : a - b + (c - d) = a + c
 - (b + d)
参数：hba : b <= a；hdc : d <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.tsub_add_tsub_comm`：∀ {α : Type u_1} [inst : AddCommSem
igroup α] [inst_1 : PartialOrder α] [ExistsAddOfLE α] [AddLeftMono α]   [inst_4 
: Sub α] [OrderedSub α] {…
· 使用定理 `Contravariant.AddLECancellable`：∀ {α : Type u_1} [inst : Add α] [inst_1 
: LE α] [AddLeftReflectLE α] {a : α}, AddLECancellable a
-/
theorem tsub_add_tsub_comm (hba : b ≤ a) (hdc : d ≤ c) : a - b + (c - d) = a + c - (b + d) :=
  Contravariant.AddLECancellable.tsub_add_tsub_comm Contravariant.AddLECancellable hba hdc
/-
**le_tsub_iff_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_tsub_iff_left (h : a <= c) : b <= c - a ↔ a + b <= c
参数：h : a <= c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.le_tsub_iff_left`：∀ {α : Type u_1} [inst : AddCommSemig
roup α] [inst_1 : PartialOrder α] [ExistsAddOfLE α] [AddLeftMono α]   [inst_4 : 
Sub α] [OrderedSub α] {…
· 使用定理 `Contravariant.AddLECancellable`：∀ {α : Type u_1} [inst : Add α] [inst_1 
: LE α] [AddLeftReflectLE α] {a : α}, AddLECancellable a
-/
theorem le_tsub_iff_left (h : a ≤ c) : b ≤ c - a ↔ a + b ≤ c :=
  Contravariant.AddLECancellable.le_tsub_iff_left h
/-
**le_tsub_iff_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_tsub_iff_right (h : a <= c) : b <= c - a ↔ b + a <= c
参数：h : a <= c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.le_tsub_iff_right`：∀ {α : Type u_1} [inst : AddCommSemi
group α] [inst_1 : PartialOrder α] [ExistsAddOfLE α] [AddLeftMono α]   [inst_4 :
 Sub α] [OrderedSub α] {…
· 使用定理 `Contravariant.AddLECancellable`：∀ {α : Type u_1} [inst : Add α] [inst_1 
: LE α] [AddLeftReflectLE α] {a : α}, AddLECancellable a
-/
theorem le_tsub_iff_right (h : a ≤ c) : b ≤ c - a ↔ b + a ≤ c :=
  Contravariant.AddLECancellable.le_tsub_iff_right h
/-
**tsub_lt_iff_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsub_lt_iff_left (hbc : b <= a) : a - b < c ↔ a < b + c
参数：hbc : b <= a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.tsub_lt_iff_left`：∀ {α : Type u_1} [inst : AddCommSemig
roup α] [inst_1 : PartialOrder α] [ExistsAddOfLE α] [AddLeftMono α]   [inst_4 : 
Sub α] [OrderedSub α] {…
· 使用定理 `Contravariant.AddLECancellable`：∀ {α : Type u_1} [inst : Add α] [inst_1 
: LE α] [AddLeftReflectLE α] {a : α}, AddLECancellable a
-/
theorem tsub_lt_iff_left (hbc : b ≤ a) : a - b < c ↔ a < b + c :=
  Contravariant.AddLECancellable.tsub_lt_iff_left hbc
/-
**tsub_lt_iff_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsub_lt_iff_right (hbc : b <= a) : a - b < c ↔ a < c + b
参数：hbc : b <= a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.tsub_lt_iff_right`：∀ {α : Type u_1} [inst : AddCommSemi
group α] [inst_1 : PartialOrder α] [ExistsAddOfLE α] [AddLeftMono α]   [inst_4 :
 Sub α] [OrderedSub α] {…
· 使用定理 `Contravariant.AddLECancellable`：∀ {α : Type u_1} [inst : Add α] [inst_1 
: LE α] [AddLeftReflectLE α] {a : α}, AddLECancellable a
-/
theorem tsub_lt_iff_right (hbc : b ≤ a) : a - b < c ↔ a < c + b :=
  Contravariant.AddLECancellable.tsub_lt_iff_right hbc
/-
**tsub_lt_iff_tsub_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsub_lt_iff_tsub_lt (h₁ : b <= a) (h₂ : c <= a) : a - b < c ↔ a - c < b
参数：h₁ : b <= a；h₂ : c <= a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.tsub_lt_iff_tsub_lt`：∀ {α : Type u_1} [inst : AddCommSe
migroup α] [inst_1 : PartialOrder α] [ExistsAddOfLE α] [AddLeftMono α]   [inst_4
 : Sub α] [OrderedSub α] {…
· 使用定理 `Contravariant.AddLECancellable`：∀ {α : Type u_1} [inst : Add α] [inst_1 
: LE α] [AddLeftReflectLE α] {a : α}, AddLECancellable a
-/
theorem tsub_lt_iff_tsub_lt (h₁ : b ≤ a) (h₂ : c ≤ a) : a - b < c ↔ a - c < b :=
  Contravariant.AddLECancellable.tsub_lt_iff_tsub_lt Contravariant.AddLECancellable h₁ h₂
/-
**le_tsub_iff_le_tsub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_tsub_iff_le_tsub (h₁ : a <= b) (h₂ : c <= b) : a <= b - c ↔ c <= b - a
参数：h₁ : a <= b；h₂ : c <= b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.le_tsub_iff_le_tsub`：∀ {α : Type u_1} [inst : AddCommSe
migroup α] [inst_1 : PartialOrder α] [ExistsAddOfLE α] [AddLeftMono α]   [inst_4
 : Sub α] [OrderedSub α] {…
· 使用定理 `Contravariant.AddLECancellable`：∀ {α : Type u_1} [inst : Add α] [inst_1 
: LE α] [AddLeftReflectLE α] {a : α}, AddLECancellable a
-/
theorem le_tsub_iff_le_tsub (h₁ : a ≤ b) (h₂ : c ≤ b) : a ≤ b - c ↔ c ≤ b - a :=
  Contravariant.AddLECancellable.le_tsub_iff_le_tsub Contravariant.AddLECancellable h₁ h₂

/-- See `lt_tsub_iff_right` for a stronger statement in a linear order. -/
/-
**lt_tsub_iff_right_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_tsub_iff_right_of_le (h : c <= b) : a < b - c ↔ a + c < b
参数：h : c <= b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.lt_tsub_iff_right_of_le`：∀ {α : Type u_1} [inst : AddCo
mmSemigroup α] [inst_1 : PartialOrder α] [ExistsAddOfLE α] [AddLeftMono α]   [in
st_4 : Sub α] [OrderedSub α] {…
· 使用定理 `Contravariant.AddLECancellable`：∀ {α : Type u_1} [inst : Add α] [inst_1 
: LE α] [AddLeftReflectLE α] {a : α}, AddLECancellable a

--- 原说明 ---
See `lt_tsub_iff_right` for a stronger statement in a linear order.
-/
theorem lt_tsub_iff_right_of_le (h : c ≤ b) : a < b - c ↔ a + c < b :=
  Contravariant.AddLECancellable.lt_tsub_iff_right_of_le h

/-- See `lt_tsub_iff_left` for a stronger statement in a linear order. -/
/-
**lt_tsub_iff_left_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_tsub_iff_left_of_le (h : c <= b) : a < b - c ↔ c + a < b
参数：h : c <= b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.lt_tsub_iff_left_of_le`：∀ {α : Type u_1} [inst : AddCom
mSemigroup α] [inst_1 : PartialOrder α] [ExistsAddOfLE α] [AddLeftMono α]   [ins
t_4 : Sub α] [OrderedSub α] {…
· 使用定理 `Contravariant.AddLECancellable`：∀ {α : Type u_1} [inst : Add α] [inst_1 
: LE α] [AddLeftReflectLE α] {a : α}, AddLECancellable a

--- 原说明 ---
See `lt_tsub_iff_left` for a stronger statement in a linear order.
-/
theorem lt_tsub_iff_left_of_le (h : c ≤ b) : a < b - c ↔ c + a < b :=
  Contravariant.AddLECancellable.lt_tsub_iff_left_of_le h

/-- See `lt_of_tsub_lt_tsub_left` for a stronger statement in a linear order. -/
/-
**lt_of_tsub_lt_tsub_left_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_of_tsub_lt_tsub_left_of_le [AddLeftReflectLT α] (hca : c <= a) (h : a -
 b < a - c) : c < b
参数：hca : c <= a；h : a - b < a - c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.lt_of_tsub_lt_tsub_left_of_le`：∀ {α : Type u_1} [inst :
 AddCommSemigroup α] [inst_1 : PartialOrder α] [ExistsAddOfLE α] [AddLeftMono α]
   [inst_4 : Sub α] [OrderedSub α] {…
· 使用定理 `Contravariant.AddLECancellable`：∀ {α : Type u_1} [inst : Add α] [inst_1 
: LE α] [AddLeftReflectLE α] {a : α}, AddLECancellable a

--- 原说明 ---
See `lt_of_tsub_lt_tsub_left` for a stronger statement in a linear order.
-/
theorem lt_of_tsub_lt_tsub_left_of_le [AddLeftReflectLT α] (hca : c ≤ a)
    (h : a - b < a - c) : c < b :=
  Contravariant.AddLECancellable.lt_of_tsub_lt_tsub_left_of_le hca h
/-
**tsub_lt_tsub_left_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsub_lt_tsub_left_of_le : b <= a -> c < b -> a - b < a - c
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.tsub_lt_tsub_left_of_le`：∀ {α : Type u_1} [inst : AddCo
mmSemigroup α] [inst_1 : PartialOrder α] [ExistsAddOfLE α] [AddLeftMono α]   [in
st_4 : Sub α] [OrderedSub α] {…
· 使用定理 `Contravariant.AddLECancellable`：∀ {α : Type u_1} [inst : Add α] [inst_1 
: LE α] [AddLeftReflectLE α] {a : α}, AddLECancellable a
-/
theorem tsub_lt_tsub_left_of_le : b ≤ a → c < b → a - b < a - c :=
  Contravariant.AddLECancellable.tsub_lt_tsub_left_of_le
/-
**tsub_lt_tsub_right_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsub_lt_tsub_right_of_le (h : c <= a) (h2 : a < b) : a - c < b - c
参数：h : c <= a；h2 : a < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.tsub_lt_tsub_right_of_le`：∀ {α : Type u_1} [inst : AddC
ommSemigroup α] [inst_1 : PartialOrder α] [ExistsAddOfLE α] [AddLeftMono α]   [i
nst_4 : Sub α] [OrderedSub α] {…
· 使用定理 `Contravariant.AddLECancellable`：∀ {α : Type u_1} [inst : Add α] [inst_1 
: LE α] [AddLeftReflectLE α] {a : α}, AddLECancellable a
-/
theorem tsub_lt_tsub_right_of_le (h : c ≤ a) (h2 : a < b) : a - c < b - c :=
  Contravariant.AddLECancellable.tsub_lt_tsub_right_of_le h h2
/-
**tsub_inj_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsub_inj_right (h₁ : b <= a) (h₂ : c <= a) (h₃ : a - b = a - c) : b = c
参数：h₁ : b <= a；h₂ : c <= a；h₃ : a - b = a - c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.tsub_inj_right`：∀ {α : Type u_1} [inst : AddCommSemigro
up α] [inst_1 : PartialOrder α] [ExistsAddOfLE α] [AddLeftMono α]   [inst_4 : Su
b α] [OrderedSub α] {…
· 使用定理 `Contravariant.AddLECancellable`：∀ {α : Type u_1} [inst : Add α] [inst_1 
: LE α] [AddLeftReflectLE α] {a : α}, AddLECancellable a
-/
theorem tsub_inj_right (h₁ : b ≤ a) (h₂ : c ≤ a) (h₃ : a - b = a - c) : b = c :=
  Contravariant.AddLECancellable.tsub_inj_right h₁ h₂ h₃

/-- See `tsub_lt_tsub_iff_left_of_le` for a stronger statement in a linear order. -/
/-
**tsub_lt_tsub_iff_left_of_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsub_lt_tsub_iff_left_of_le_of_le [AddLeftReflectLT α] (h₁ : b <= a) (h₂ :
 c <= a) : a - b < a - c ↔ c < b
参数：h₁ : b <= a；h₂ : c <= a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.tsub_lt_tsub_iff_left_of_le_of_le`：∀ {α : Type u_1} [in
st : AddCommSemigroup α] [inst_1 : PartialOrder α] [ExistsAddOfLE α] [AddLeftMon
o α]   [inst_4 : Sub α] [OrderedSub α] {…
· 使用定理 `Contravariant.AddLECancellable`：∀ {α : Type u_1} [inst : Add α] [inst_1 
: LE α] [AddLeftReflectLE α] {a : α}, AddLECancellable a

--- 原说明 ---
See `tsub_lt_tsub_iff_left_of_le` for a stronger statement in a linear order.
-/
theorem tsub_lt_tsub_iff_left_of_le_of_le [AddLeftReflectLT α] (h₁ : b ≤ a)
    (h₂ : c ≤ a) : a - b < a - c ↔ c < b :=
  Contravariant.AddLECancellable.tsub_lt_tsub_iff_left_of_le_of_le Contravariant.AddLECancellable h₁
    h₂

@[simp]
/-
**add_add_tsub_cancel** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：add_add_tsub_cancel (hcb : c <= b) : a + c + (b - c) = a + b
参数：hcb : c <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.add_add_tsub_cancel`：∀ {α : Type u_1} [inst : AddCommSe
migroup α] [inst_1 : PartialOrder α] [ExistsAddOfLE α] [AddLeftMono α]   [inst_4
 : Sub α] [OrderedSub α] {…
· 使用定理 `Contravariant.AddLECancellable`：∀ {α : Type u_1} [inst : Add α] [inst_1 
: LE α] [AddLeftReflectLE α] {a : α}, AddLECancellable a
-/
lemma add_add_tsub_cancel (hcb : c ≤ b) : a + c + (b - c) = a + b :=
  Contravariant.AddLECancellable.add_add_tsub_cancel hcb

@[simp]
/-
**add_tsub_tsub_cancel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：add_tsub_tsub_cancel (h : c <= a) : a + b - (a - c) = b + c
参数：h : c <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.add_tsub_tsub_cancel`：∀ {α : Type u_1} [inst : AddCommS
emigroup α] [inst_1 : PartialOrder α] [ExistsAddOfLE α] [AddLeftMono α]   [inst_
4 : Sub α] [OrderedSub α] {…
· 使用定理 `Contravariant.AddLECancellable`：∀ {α : Type u_1} [inst : Add α] [inst_1 
: LE α] [AddLeftReflectLE α] {a : α}, AddLECancellable a
-/
theorem add_tsub_tsub_cancel (h : c ≤ a) : a + b - (a - c) = b + c :=
  Contravariant.AddLECancellable.add_tsub_tsub_cancel h

/-- See `tsub_tsub_le` for an inequality. -/
/-
**tsub_tsub_cancel_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsub_tsub_cancel_of_le (h : a <= b) : b - (b - a) = a
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.tsub_tsub_cancel_of_le`：∀ {α : Type u_1} [inst : AddCom
mSemigroup α] [inst_1 : PartialOrder α] [ExistsAddOfLE α] [AddLeftMono α]   [ins
t_4 : Sub α] [OrderedSub α] {…
· 使用定理 `Contravariant.AddLECancellable`：∀ {α : Type u_1} [inst : Add α] [inst_1 
: LE α] [AddLeftReflectLE α] {a : α}, AddLECancellable a

--- 原说明 ---
See `tsub_tsub_le` for an inequality.
-/
theorem tsub_tsub_cancel_of_le (h : a ≤ b) : b - (b - a) = a :=
  Contravariant.AddLECancellable.tsub_tsub_cancel_of_le h
/-
**tsub_tsub_tsub_cancel_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsub_tsub_tsub_cancel_left (h : b <= a) : a - c - (a - b) = b - c
参数：h : b <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.tsub_tsub_tsub_cancel_left`：∀ {α : Type u_1} [inst : Ad
dCommSemigroup α] [inst_1 : PartialOrder α] [ExistsAddOfLE α] [AddLeftMono α]   
[inst_4 : Sub α] [OrderedSub α] {…
· 使用定理 `Contravariant.AddLECancellable`：∀ {α : Type u_1} [inst : Add α] [inst_1 
: LE α] [AddLeftReflectLE α] {a : α}, AddLECancellable a
-/
theorem tsub_tsub_tsub_cancel_left (h : b ≤ a) : a - c - (a - b) = b - c :=
  Contravariant.AddLECancellable.tsub_tsub_tsub_cancel_left h

-- note: not generalized to `AddLECancellable` because `add_tsub_add_eq_tsub_left` isn't
/-- The `tsub` version of `sub_sub_eq_add_sub`. -/
/-
**tsub_tsub_eq_add_tsub_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsub_tsub_eq_add_tsub_of_le (h : c <= b) : a - (b - c) = a + c - b
参数：h : c <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ExistsAddOfLE.exists_add_of_le`：∀ {α : Type u} {inst : Add α} {inst_1 : 
LE α} [self : ExistsAddOfLE α] {a b : α}, a ≤ b → ∃ c, b = a + c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_tsub_cancel_left`：add_tsub_cancel_left (a b : α) : a + b - a = b
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `add_tsub_add_eq_tsub_left`：add_tsub_add_eq_tsub_left (a b c : α) : a + b
 - (a + c) = b - c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The `tsub` version of `sub_sub_eq_add_sub`.
-/
theorem tsub_tsub_eq_add_tsub_of_le
    (h : c ≤ b) : a - (b - c) = a + c - b := by
  obtain ⟨d, rfl⟩ := exists_add_of_le h
  rw [add_tsub_cancel_left c, add_comm a c, add_tsub_add_eq_tsub_left]

end Contra

end ExistsAddOfLE

