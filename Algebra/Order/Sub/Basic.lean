/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Algebra.Order.Sub.Unbundled.Basic
public import Mathlib.Algebra.Group.Equiv.Basic
public import Mathlib.Algebra.Group.Even
/-!
# Lemmas about subtraction in unbundled canonically ordered monoids
-/

public section

variable {α : Type*}

section CanonicallyOrderedAddCommMonoid

variable [AddCommMonoid α] [PartialOrder α] [CanonicallyOrderedAdd α]
  [Sub α] [OrderedSub α] {a b c : α}

/-
**add_tsub_cancel_iff_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：add_tsub_cancel_iff_le : a + (b - a) = b ↔ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `le_iff_exists_add`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [Canoni
callyOrderedAdd α] {a b : α}, a ≤ b ↔ ∃ c, b = a + c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_tsub_cancel_of_le`：add_tsub_cancel_of_le (h : a <= b) : a + (b - a) 
= b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `CanonicallyOrderedAdd.toAddLeftMono`：∀ {α : Type u} [inst : AddSemigroup
 α] [inst_1 : LE α] [CanonicallyOrderedAdd α], AddLeftMono α
-/
theorem add_tsub_cancel_iff_le : a + (b - a) = b ↔ a ≤ b :=
  ⟨fun h => le_iff_exists_add.mpr ⟨b - a, h.symm⟩, add_tsub_cancel_of_le⟩
/-
**tsub_add_cancel_iff_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsub_add_cancel_iff_le : b - a + a = b ↔ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `add_tsub_cancel_iff_le`：add_tsub_cancel_iff_le : a + (b - a) = b ↔ a <= 
b
-/
theorem tsub_add_cancel_iff_le : b - a + a = b ↔ a ≤ b := by
  rw [add_comm]
  exact add_tsub_cancel_iff_le

-- This was previously a `@[simp]` lemma, but it is not necessarily a good idea, e.g. in
-- `example (h : n - m = 0) : a + (n - m) = a := by simp_all`
/-
**tsub_eq_zero_iff_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsub_eq_zero_iff_le : a - b = 0 ↔ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `tsub_le_iff_left`：tsub_le_iff_left : a - b <= c ↔ a <= b + c
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem tsub_eq_zero_iff_le : a - b = 0 ↔ a ≤ b := by
  rw [← nonpos_iff_eq_zero, tsub_le_iff_left, add_zero]

alias ⟨_, tsub_eq_zero_of_le⟩ := tsub_eq_zero_iff_le

@[simp]
/-
**tsub_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsub_self (a : α) : a - a = 0
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tsub_eq_zero_of_le`：∀ {α : Type u_1} [inst : AddCommMonoid α] [inst_1 : 
PartialOrder α] [CanonicallyOrderedAdd α] [inst_3 : Sub α]   [OrderedSub α] {a b
 : α}, a…
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem tsub_self (a : α) : a - a = 0 :=
  tsub_eq_zero_of_le le_rfl
/-
**tsub_le_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsub_le_self : a - b <= a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tsub_le_iff_left`：tsub_le_iff_left : a - b <= c ↔ a <= b + c
· 使用定理 `le_add_left`：∀ {α : Type u} [inst : Add α] [inst_1 : Preorder α] [Canoni
callyOrderedAdd α] {a b c : α}, a ≤ c → a ≤ b + c
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem tsub_le_self : a - b ≤ a :=
  tsub_le_iff_left.mpr <| le_add_left le_rfl

@[simp]
/-
**zero_tsub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：zero_tsub (a : α) : 0 - a = 0
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tsub_eq_zero_of_le`：∀ {α : Type u_1} [inst : AddCommMonoid α] [inst_1 : 
PartialOrder α] [CanonicallyOrderedAdd α] [inst_3 : Sub α]   [OrderedSub α] {a b
 : α}, a…
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
-/
theorem zero_tsub (a : α) : 0 - a = 0 :=
  tsub_eq_zero_of_le zero_le
/-
**tsub_self_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsub_self_add (a b : α) : a - (a + b) = 0
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tsub_eq_zero_of_le`：∀ {α : Type u_1} [inst : AddCommMonoid α] [inst_1 : 
PartialOrder α] [CanonicallyOrderedAdd α] [inst_3 : Sub α]   [OrderedSub α] {a b
 : α}, a…
· 使用定理 `self_le_add_right`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [Canoni
callyOrderedAdd α] (a b : α), a ≤ a + b
-/
theorem tsub_self_add (a b : α) : a - (a + b) = 0 :=
  tsub_eq_zero_of_le <| self_le_add_right _ _
/-
**tsub_pos_iff_not_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsub_pos_iff_not_le : 0 < a - b ↔ ¬a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `tsub_eq_zero_iff_le`：tsub_eq_zero_iff_le : a - b = 0 ↔ a <= b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem tsub_pos_iff_not_le : 0 < a - b ↔ ¬a ≤ b := by
  rw [pos_iff_ne_zero, Ne, tsub_eq_zero_iff_le]
/-
**tsub_pos_of_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsub_pos_of_lt (h : a < b) : 0 < b - a
参数：h : a < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tsub_pos_iff_not_le`：tsub_pos_iff_not_le : 0 < a - b ↔ ¬a <= b
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
-/
theorem tsub_pos_of_lt (h : a < b) : 0 < b - a :=
  tsub_pos_iff_not_le.mpr h.not_ge
/-
**tsub_lt_of_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsub_lt_of_lt (h : a < b) : a - c < b
参数：h : a < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `tsub_le_self`：tsub_le_self : a - b <= a
-/
theorem tsub_lt_of_lt (h : a < b) : a - c < b :=
  lt_of_le_of_lt tsub_le_self h

namespace AddLECancellable

/-
**AddLECancellable.tsub_le_tsub_iff_left** 是 Mathlib 中的一个定理，位于命名空间 `AddLECancell
able`。
形式化陈述：∀ {α : Type u_1} [inst : AddCommMonoid α] [inst_1 : PartialOrder α] [Canon
icallyOrderedAdd α] [inst_3 : Sub α]   [OrderedSub α] {a b c : α}, AddLECancella
ble a → AddLECancellable c → c ≤ a → (a - b ≤ a - c ↔ c ≤ b)
参数：a - b ≤ a - c ↔ c ≤ b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tsub_le_iff_left`：tsub_le_iff_left : a - b <= c ↔ a <= b + c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddLECancellable.add_tsub_assoc_of_le`：∀ {α : Type u_1} [inst : AddCommS
emigroup α] [inst_1 : PartialOrder α] [ExistsAddOfLE α] [AddLeftMono α]   [inst_
4 : Sub α] [OrderedSub α] {…
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `CanonicallyOrderedAdd.toAddLeftMono`：∀ {α : Type u} [inst : AddSemigroup
 α] [inst_1 : LE α] [CanonicallyOrderedAdd α], AddLeftMono α
· 使用定理 `AddLECancellable.le_tsub_iff_right`：∀ {α : Type u_1} [inst : AddCommSemi
group α] [inst_1 : PartialOrder α] [ExistsAddOfLE α] [AddLeftMono α]   [inst_4 :
 Sub α] [OrderedSub α] {…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_add_self`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ b + a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `tsub_le_tsub_left`：tsub_le_tsub_left (h : a <= b) (c : α) : c - b <= c -
 a
-/
protected theorem tsub_le_tsub_iff_left (ha : AddLECancellable a) (hc : AddLECancellable c)
    (h : c ≤ a) : a - b ≤ a - c ↔ c ≤ b := by
  refine ⟨?_, fun h => tsub_le_tsub_left h a⟩
  rw [tsub_le_iff_left, ← hc.add_tsub_assoc_of_le h, hc.le_tsub_iff_right (h.trans le_add_self),
    add_comm b]
  apply ha
/-
**AddLECancellable.tsub_right_inj** 是 Mathlib 中的一个定理，位于命名空间 `AddLECancellable`。
形式化陈述：∀ {α : Type u_1} [inst : AddCommMonoid α] [inst_1 : PartialOrder α] [Canon
icallyOrderedAdd α] [inst_3 : Sub α]   [OrderedSub α] {a b c : α},   AddLECancel
lable a → AddLECancellable b → AddLECancellable c → b ≤ a → c ≤ a → (a - b = a -
 c ↔ b = c)
参数：a - b = a - c ↔ b = c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AddLECancellable.tsub_le_tsub_iff_left`：∀ {α : Type u_1} [inst : AddComm
Monoid α] [inst_1 : PartialOrder α] [CanonicallyOrderedAdd α] [inst_3 : Sub α]  
 [OrderedSub α] {a b c : α},…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected theorem tsub_right_inj (ha : AddLECancellable a) (hb : AddLECancellable b)
    (hc : AddLECancellable c) (hba : b ≤ a) (hca : c ≤ a) : a - b = a - c ↔ b = c := by
  simp_rw [le_antisymm_iff, ha.tsub_le_tsub_iff_left hb hba, ha.tsub_le_tsub_iff_left hc hca,
    and_comm]

end AddLECancellable

/-! #### Lemmas where addition is order-reflecting. -/


section Contra

variable [AddLeftReflectLE α]

/-
**tsub_le_tsub_iff_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsub_le_tsub_iff_left (h : c <= a) : a - b <= a - c ↔ c <= b
参数：h : c <= a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.tsub_le_tsub_iff_left`：∀ {α : Type u_1} [inst : AddComm
Monoid α] [inst_1 : PartialOrder α] [CanonicallyOrderedAdd α] [inst_3 : Sub α]  
 [OrderedSub α] {a b c : α},…
· 使用定理 `Contravariant.AddLECancellable`：∀ {α : Type u_1} [inst : Add α] [inst_1 
: LE α] [AddLeftReflectLE α] {a : α}, AddLECancellable a
-/
theorem tsub_le_tsub_iff_left (h : c ≤ a) : a - b ≤ a - c ↔ c ≤ b :=
  Contravariant.AddLECancellable.tsub_le_tsub_iff_left Contravariant.AddLECancellable h
/-
**tsub_right_inj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsub_right_inj (hba : b <= a) (hca : c <= a) : a - b = a - c ↔ b = c
参数：hba : b <= a；hca : c <= a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.tsub_right_inj`：∀ {α : Type u_1} [inst : AddCommMonoid 
α] [inst_1 : PartialOrder α] [CanonicallyOrderedAdd α] [inst_3 : Sub α]   [Order
edSub α] {a b c : α},…
· 使用定理 `Contravariant.AddLECancellable`：∀ {α : Type u_1} [inst : Add α] [inst_1 
: LE α] [AddLeftReflectLE α] {a : α}, AddLECancellable a
-/
theorem tsub_right_inj (hba : b ≤ a) (hca : c ≤ a) : a - b = a - c ↔ b = c :=
  Contravariant.AddLECancellable.tsub_right_inj Contravariant.AddLECancellable
    Contravariant.AddLECancellable hba hca

variable (α)

/-- A `CanonicallyOrderedAddCommMonoid` with ordered subtraction and order-reflecting addition is
cancellative. This is not an instance as it would form a typeclass loop.

See note [reducible non-instances]. -/
/-
**CanonicallyOrderedAddCommMonoid.toAddCancelCommMonoid** 是 Mathlib 中的一个缩写定义，位于命
名空间 ``。
形式化陈述：CanonicallyOrderedAddCommMonoid.toAddCancelCommMonoid : AddCancelCommMonoi
d α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `CanonicallyOrderedAddCommMonoid` with ordered subtraction and order-reflectin
g addition is
cancellative. This is not an instance as it would form a typeclass loop.

See note [reducible non-instances].
-/
abbrev CanonicallyOrderedAddCommMonoid.toAddCancelCommMonoid : AddCancelCommMonoid α :=
  { (by infer_instance : AddCommMonoid α) with
    add_left_cancel := fun a b c h => by
      simpa only [add_tsub_cancel_left] using congr_arg (fun x => x - a) h }

end Contra

end CanonicallyOrderedAddCommMonoid

/-! ### Lemmas in a linearly canonically ordered monoid. -/


section CanonicallyLinearOrderedAddCommMonoid

variable [AddCommMonoid α] [LinearOrder α] [CanonicallyOrderedAdd α] [Sub α] [OrderedSub α]
  {a b c : α}

@[simp]
/-
**tsub_pos_iff_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsub_pos_iff_lt : 0 < a - b ↔ b < a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tsub_pos_iff_not_le`：tsub_pos_iff_not_le : 0 < a - b ↔ ¬a <= b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem tsub_pos_iff_lt : 0 < a - b ↔ b < a := by rw [tsub_pos_iff_not_le, not_le]
/-
**tsub_eq_tsub_min** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsub_eq_tsub_min (a b : α) : a - b = a - min a b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `min_eq_left`：min_eq_left (h : a <= b) : min a b = a
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `tsub_eq_zero_of_le`：∀ {α : Type u_1} [inst : AddCommMonoid α] [inst_1 : 
PartialOrder α] [CanonicallyOrderedAdd α] [inst_3 : Sub α]   [OrderedSub α] {a b
 : α}, a…
· 使用引理 `min_eq_right`：min_eq_right (h : b <= a) : min a b = b
-/
theorem tsub_eq_tsub_min (a b : α) : a - b = a - min a b := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, tsub_self, tsub_eq_zero_of_le h]
  · rw [min_eq_right h]

namespace AddLECancellable

omit [CanonicallyOrderedAdd α] in
/-
**AddLECancellable.lt_tsub_iff_right** 是 Mathlib 中的一个定理，位于命名空间 `AddLECancellable
`。
形式化陈述：∀ {α : Type u_1} [inst : AddCommMonoid α] [inst_1 : LinearOrder α] [inst_2
 : Sub α] [OrderedSub α] {a b c : α},   AddLECancellable c → (a < b - c ↔ a + c 
< b)
参数：a < b - c ↔ a + c < b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_imp_lt_of_le_imp_le`：lt_imp_lt_of_le_imp_le {β} [LinearOrder α] [Preo
rder β] {a b : α} {c d : β} (H : a <= b -> c <= d) (h : d < c) : b < a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tsub_le_iff_right`：tsub_le_iff_right [LE α] [Add α] [Sub α] [OrderedSub 
α] {a b c : α} : a - b <= c ↔ a <= c + b
· 使用定理 `AddLECancellable.lt_tsub_of_add_lt_right`：∀ {α : Type u_1} [inst : Parti
alOrder α] [inst_1 : AddCommSemigroup α] [inst_2 : Sub α] [OrderedSub α] {a b c 
: α},   AddLECancellable c → a…
-/
protected theorem lt_tsub_iff_right (hc : AddLECancellable c) : a < b - c ↔ a + c < b :=
  ⟨lt_imp_lt_of_le_imp_le tsub_le_iff_right.mpr, hc.lt_tsub_of_add_lt_right⟩

omit [CanonicallyOrderedAdd α] in
/-
**AddLECancellable.lt_tsub_iff_left** 是 Mathlib 中的一个定理，位于命名空间 `AddLECancellable`
。
形式化陈述：∀ {α : Type u_1} [inst : AddCommMonoid α] [inst_1 : LinearOrder α] [inst_2
 : Sub α] [OrderedSub α] {a b c : α},   AddLECancellable c → (a < b - c ↔ c + a 
< b)
参数：a < b - c ↔ c + a < b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_imp_lt_of_le_imp_le`：lt_imp_lt_of_le_imp_le {β} [LinearOrder α] [Preo
rder β] {a b : α} {c d : β} (H : a <= b -> c <= d) (h : d < c) : b < a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tsub_le_iff_left`：tsub_le_iff_left : a - b <= c ↔ a <= b + c
· 使用定理 `AddLECancellable.lt_tsub_of_add_lt_left`：∀ {α : Type u_1} [inst : Partia
lOrder α] [inst_1 : AddCommSemigroup α] [inst_2 : Sub α] [OrderedSub α] {a b c :
 α},   AddLECancellable a → a…
-/
protected theorem lt_tsub_iff_left (hc : AddLECancellable c) : a < b - c ↔ c + a < b :=
  ⟨lt_imp_lt_of_le_imp_le tsub_le_iff_left.mpr, hc.lt_tsub_of_add_lt_left⟩
/-
**AddLECancellable.tsub_lt_tsub_iff_right** 是 Mathlib 中的一个定理，位于命名空间 `AddLECancel
lable`。
形式化陈述：∀ {α : Type u_1} [inst : AddCommMonoid α] [inst_1 : LinearOrder α] [Canoni
callyOrderedAdd α] [inst_3 : Sub α]   [OrderedSub α] {a b c : α}, AddLECancellab
le c → c ≤ a → (a - c < b - c ↔ a < b)
参数：a - c < b - c ↔ a < b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddLECancellable.lt_tsub_iff_left`：∀ {α : Type u_1} [inst : AddCommMonoi
d α] [inst_1 : LinearOrder α] [inst_2 : Sub α] [OrderedSub α] {a b c : α},   Add
LECancellable c → (a < …
· 使用定理 `add_tsub_cancel_of_le`：add_tsub_cancel_of_le (h : a <= b) : a + (b - a) 
= b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `CanonicallyOrderedAdd.toAddLeftMono`：∀ {α : Type u} [inst : AddSemigroup
 α] [inst_1 : LE α] [CanonicallyOrderedAdd α], AddLeftMono α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected theorem tsub_lt_tsub_iff_right (hc : AddLECancellable c) (h : c ≤ a) :
    a - c < b - c ↔ a < b := by rw [hc.lt_tsub_iff_left, add_tsub_cancel_of_le h]
/-
**AddLECancellable.tsub_lt_self** 是 Mathlib 中的一个定理，位于命名空间 `AddLECancellable`。
形式化陈述：∀ {α : Type u_1} [inst : AddCommMonoid α] [inst_1 : LinearOrder α] [Canoni
callyOrderedAdd α] [inst_3 : Sub α]   [OrderedSub α] {a b : α}, AddLECancellable
 a → 0 < a → 0 < b → a - b < a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用定理 `tsub_le_self`：tsub_le_self : a - b <= a
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AddLECancellable.add_le_iff_nonpos_left`：∀ {α : Type u_1} [inst : LE α] 
[inst_1 : AddZeroClass α] [IsAddCommutative α] [AddLeftMono α] {a b : α},   AddL
ECancellable a → (b + a ≤ a ↔…
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `CanonicallyOrderedAdd.toAddLeftMono`：∀ {α : Type u} [inst : AddSemigroup
 α] [inst_1 : LE α] [CanonicallyOrderedAdd α], AddLeftMono α
· 使用定理 `add_le_of_le_tsub_left_of_le`：add_le_of_le_tsub_left_of_le (h : a <= c) 
(h2 : b <= c - a) : a + b <= c
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tsub_pos_iff_lt`：tsub_pos_iff_lt : 0 < a - b ↔ b < a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
-/
protected theorem tsub_lt_self (ha : AddLECancellable a) (h₁ : 0 < a) (h₂ : 0 < b) : a - b < a := by
  refine tsub_le_self.lt_of_ne fun h => ?_
  rw [← h, tsub_pos_iff_lt] at h₁
  exact h₂.not_ge (ha.add_le_iff_nonpos_left.1 <| add_le_of_le_tsub_left_of_le h₁.le h.ge)
/-
**AddLECancellable.tsub_lt_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `AddLECancellable`
。
形式化陈述：∀ {α : Type u_1} [inst : AddCommMonoid α] [inst_1 : LinearOrder α] [Canoni
callyOrderedAdd α] [inst_3 : Sub α]   [OrderedSub α] {a b : α}, AddLECancellable
 a → (a - b < a ↔ 0 < a ∧ 0 < b)
参数：a - b < a ↔ 0 < a ∧ 0 < b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.pos`：∀ {α : Type u_1} {a b : α} [inst : Preorder α] [inst_1 : Zero
 α] [IsBotZeroClass α], a < b → 0 < b
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `pos_of_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_1
 : Zero α] [IsBotZeroClass α], a ≠ 0 → 0 < a
· 使用定理 `LT.lt.false`：∀ {α : Type u_2} [inst : Preorder α] {a : α}, a < a → False
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tsub_zero`：tsub_zero (a : α) : a - 0 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddLECancellable.tsub_lt_self`：∀ {α : Type u_1} [inst : AddCommMonoid α]
 [inst_1 : LinearOrder α] [CanonicallyOrderedAdd α] [inst_3 : Sub α]   [OrderedS
ub α] {a b : α}, Ad…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
protected theorem tsub_lt_self_iff (ha : AddLECancellable a) : a - b < a ↔ 0 < a ∧ 0 < b := by
  refine ⟨fun h => ⟨h.pos, pos_of_ne_zero ?_⟩, fun h => ha.tsub_lt_self h.1 h.2⟩
  rintro rfl
  rw [tsub_zero] at h
  exact h.false

/-- See `lt_tsub_iff_left_of_le_of_le` for a weaker statement in a partial order. -/
/-
**AddLECancellable.tsub_lt_tsub_iff_left_of_le** 是 Mathlib 中的一个定理，位于命名空间 `AddLEC
ancellable`。
形式化陈述：∀ {α : Type u_1} [inst : AddCommMonoid α] [inst_1 : LinearOrder α] [Canoni
callyOrderedAdd α] [inst_3 : Sub α]   [OrderedSub α] {a b c : α}, AddLECancellab
le a → AddLECancellable b → b ≤ a → (a - b < a - c ↔ c < b)
参数：a - b < a - c ↔ c < b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_iff_lt_of_le_iff_le`：lt_iff_lt_of_le_iff_le {β} [LinearOrder α] [Line
arOrder β] {a b : α} {c d : β} (H : a <= b ↔ c <= d) : b < a ↔ d < c
· 使用定理 `AddLECancellable.tsub_le_tsub_iff_left`：∀ {α : Type u_1} [inst : AddComm
Monoid α] [inst_1 : PartialOrder α] [CanonicallyOrderedAdd α] [inst_3 : Sub α]  
 [OrderedSub α] {a b c : α},…

--- 原说明 ---
See `lt_tsub_iff_left_of_le_of_le` for a weaker statement in a partial order.
-/
protected theorem tsub_lt_tsub_iff_left_of_le (ha : AddLECancellable a) (hb : AddLECancellable b)
    (h : b ≤ a) : a - b < a - c ↔ c < b :=
  lt_iff_lt_of_le_iff_le <| ha.tsub_le_tsub_iff_left hb h

end AddLECancellable

section Contra

variable [AddLeftReflectLE α]

/-- This lemma also holds for `ENNReal`, but we need a different proof for that. -/
/-
**tsub_lt_tsub_iff_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsub_lt_tsub_iff_right (h : c <= a) : a - c < b - c ↔ a < b
参数：h : c <= a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.tsub_lt_tsub_iff_right`：∀ {α : Type u_1} [inst : AddCom
mMonoid α] [inst_1 : LinearOrder α] [CanonicallyOrderedAdd α] [inst_3 : Sub α]  
 [OrderedSub α] {a b c : α}, …
· 使用定理 `Contravariant.AddLECancellable`：∀ {α : Type u_1} [inst : Add α] [inst_1 
: LE α] [AddLeftReflectLE α] {a : α}, AddLECancellable a

--- 原说明 ---
This lemma also holds for `ENNReal`, but we need a different proof for that.
-/
theorem tsub_lt_tsub_iff_right (h : c ≤ a) : a - c < b - c ↔ a < b :=
  Contravariant.AddLECancellable.tsub_lt_tsub_iff_right h
/-
**tsub_lt_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsub_lt_self : 0 < a -> 0 < b -> a - b < a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.tsub_lt_self`：∀ {α : Type u_1} [inst : AddCommMonoid α]
 [inst_1 : LinearOrder α] [CanonicallyOrderedAdd α] [inst_3 : Sub α]   [OrderedS
ub α] {a b : α}, Ad…
· 使用定理 `Contravariant.AddLECancellable`：∀ {α : Type u_1} [inst : Add α] [inst_1 
: LE α] [AddLeftReflectLE α] {a : α}, AddLECancellable a
-/
theorem tsub_lt_self : 0 < a → 0 < b → a - b < a :=
  Contravariant.AddLECancellable.tsub_lt_self
/-
**tsub_lt_self_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : AddCommMonoid α] [inst_1 : LinearOrder α] [Canoni
callyOrderedAdd α] [inst_3 : Sub α]   [OrderedSub α] {a b : α} [AddLeftReflectLE
 α], a - b < a ↔ 0 < a ∧ 0 < b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.tsub_lt_self_iff`：∀ {α : Type u_1} [inst : AddCommMonoi
d α] [inst_1 : LinearOrder α] [CanonicallyOrderedAdd α] [inst_3 : Sub α]   [Orde
redSub α] {a b : α}, Ad…
· 使用定理 `Contravariant.AddLECancellable`：∀ {α : Type u_1} [inst : Add α] [inst_1 
: LE α] [AddLeftReflectLE α] {a : α}, AddLECancellable a
-/
@[simp] theorem tsub_lt_self_iff : a - b < a ↔ 0 < a ∧ 0 < b :=
  Contravariant.AddLECancellable.tsub_lt_self_iff

/-- See `lt_tsub_iff_left_of_le_of_le` for a weaker statement in a partial order. -/
/-
**tsub_lt_tsub_iff_left_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsub_lt_tsub_iff_left_of_le (h : b <= a) : a - b < a - c ↔ c < b
参数：h : b <= a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.tsub_lt_tsub_iff_left_of_le`：∀ {α : Type u_1} [inst : A
ddCommMonoid α] [inst_1 : LinearOrder α] [CanonicallyOrderedAdd α] [inst_3 : Sub
 α]   [OrderedSub α] {a b c : α}, …
· 使用定理 `Contravariant.AddLECancellable`：∀ {α : Type u_1} [inst : Add α] [inst_1 
: LE α] [AddLeftReflectLE α] {a : α}, AddLECancellable a

--- 原说明 ---
See `lt_tsub_iff_left_of_le_of_le` for a weaker statement in a partial order.
-/
theorem tsub_lt_tsub_iff_left_of_le (h : b ≤ a) : a - b < a - c ↔ c < b :=
  Contravariant.AddLECancellable.tsub_lt_tsub_iff_left_of_le Contravariant.AddLECancellable h
/-
**tsub_tsub_eq_min** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tsub_tsub_eq_min (a b : α) : a - (a - b) = min a b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tsub_eq_tsub_min`：tsub_eq_tsub_min (a b : α) : a - b = a - min a b
· 使用定理 `tsub_tsub_cancel_of_le`：tsub_tsub_cancel_of_le (h : a <= b) : b - (b - a
) = a
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `CanonicallyOrderedAdd.toAddLeftMono`：∀ {α : Type u} [inst : AddSemigroup
 α] [inst_1 : LE α] [CanonicallyOrderedAdd α], AddLeftMono α
· 使用引理 `min_le_left`：min_le_left (a b : α) : min a b <= a
-/
lemma tsub_tsub_eq_min (a b : α) : a - (a - b) = min a b := by
  rw [tsub_eq_tsub_min _ b, tsub_tsub_cancel_of_le (min_le_left a _)]

end Contra

/-! ### Lemmas about `max` and `min`. -/


/-
**tsub_add_eq_max** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsub_add_eq_max : a - b + b = max a b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `max_eq_right`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b →
 max a b = b
· 使用定理 `tsub_eq_zero_of_le`：∀ {α : Type u_1} [inst : AddCommMonoid α] [inst_1 : 
PartialOrder α] [CanonicallyOrderedAdd α] [inst_3 : Sub α]   [OrderedSub α] {a b
 : α}, a…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `max_eq_left`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a → 
max a b = a
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `CanonicallyOrderedAdd.toAddLeftMono`：∀ {α : Type u} [inst : AddSemigroup
 α] [inst_1 : LE α] [CanonicallyOrderedAdd α], AddLeftMono α

--- 原说明 ---
### Lemmas about `max` and `min`.
-/
theorem tsub_add_eq_max : a - b + b = max a b := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, tsub_eq_zero_of_le h, zero_add]
  · rw [max_eq_left h, tsub_add_cancel_of_le h]
/-
**add_tsub_eq_max** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：add_tsub_eq_max : a + (b - a) = max a b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `max_comm`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), max a b = m
ax b a
· 使用定理 `tsub_add_eq_max`：tsub_add_eq_max : a - b + b = max a b
-/
theorem add_tsub_eq_max : a + (b - a) = max a b := by rw [add_comm, max_comm, tsub_add_eq_max]
/-
**tsub_min** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsub_min : a - min a b = a - b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tsub_eq_tsub_min`：tsub_eq_tsub_min (a b : α) : a - b = a - min a b
-/
theorem tsub_min : a - min a b = a - b := (tsub_eq_tsub_min a b).symm
/-
**tsub_add_min** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsub_add_min : a - b + min a b = a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tsub_min`：tsub_min : a - min a b = a - b
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `CanonicallyOrderedAdd.toAddLeftMono`：∀ {α : Type u} [inst : AddSemigroup
 α] [inst_1 : LE α] [CanonicallyOrderedAdd α], AddLeftMono α
· 使用引理 `min_le_left`：min_le_left (a b : α) : min a b <= a
-/
theorem tsub_add_min : a - b + min a b = a := by
  rw [← tsub_min, @tsub_add_cancel_of_le]
  apply min_le_left

-- TODO: Should we introduce `Odd.tsub`? It will probably only be used by `ℕ`.
/-
**Even.tsub** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Even.tsub [AddLeftReflectLE α] {m n : α} (hm : Even m) (hn : Even n) : Eve
n (m - n)
参数：hm : Even m；hn : Even n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tsub_eq_zero_of_le`：∀ {α : Type u_1} [inst : AddCommMonoid α] [inst_1 : 
PartialOrder α] [CanonicallyOrderedAdd α] [inst_3 : Sub α]   [OrderedSub α] {a b
 : α}, a…
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `CanonicallyOrderedAdd.toAddLeftMono`：∀ {α : Type u} [inst : AddSemigroup
 α] [inst_1 : LE α] [CanonicallyOrderedAdd α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tsub_add_tsub_comm`：tsub_add_tsub_comm (hba : b <= a) (hdc : d <= c) : a
 - b + (c - d) = a + c - (b + d)
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
-/
lemma Even.tsub [AddLeftReflectLE α] {m n : α} (hm : Even m) (hn : Even n) :
    Even (m - n) := by
  obtain ⟨a, rfl⟩ := hm
  obtain ⟨b, rfl⟩ := hn
  refine ⟨a - b, ?_⟩
  obtain h | h := le_total a b
  · rw [tsub_eq_zero_of_le h, tsub_eq_zero_of_le (add_le_add h h), add_zero]
  · exact (tsub_add_tsub_comm h h).symm

end CanonicallyLinearOrderedAddCommMonoid

/-! ### `Sub` structure in linearly canonically ordered monoid using choice. -/

namespace CanonicallyOrderedAdd

variable [AddCommMonoid α] [LinearOrder α] [CanonicallyOrderedAdd α]

-- See note [reducible non-instances]
/-- `Sub` structure in linearly canonically ordered monoid using choice. -/
/-
**CanonicallyOrderedAdd.toSub** 是 Mathlib 中的一个缩写定义，位于命名空间 `CanonicallyOrderedAdd
`。
形式化陈述：toSub : Sub α where sub x y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Sub` structure in linearly canonically ordered monoid using choice.
-/
noncomputable abbrev toSub : Sub α where
  sub x y := if h : y ≤ x then (exists_add_of_le h).choose else 0

attribute [local instance] toSub

/-- The `Sub` structure using choice satisfies `OrderedSub`. -/
/-
**CanonicallyOrderedAdd.toOrderedSub** 是 Mathlib 中的一个定理，位于命名空间 `CanonicallyOrder
edAdd`。
形式化陈述：toOrderedSub [AddRightReflectLE α] : OrderedSub α where tsub_le_iff_right 
a b c
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `ExistsAddOfLE.exists_add_of_le`：∀ {α : Type u} {inst : Add α} {inst_1 : 
LE α} [self : ExistsAddOfLE α] {a b : α}, a ≤ b → ∃ c, b = a + c
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `add_le_add_iff_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [A
ddRightMono α] [AddRightReflectLE α] (a : α) {b c : α},   b + a ≤ c + a ↔ b ≤ c
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `CanonicallyOrderedAdd.toAddLeftMono`：∀ {α : Type u} [inst : AddSemigroup
 α] [inst_1 : LE α] [CanonicallyOrderedAdd α], AddLeftMono α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α

--- 原说明 ---
The `Sub` structure using choice satisfies `OrderedSub`.
-/
theorem toOrderedSub [AddRightReflectLE α] : OrderedSub α where
  tsub_le_iff_right a b c := by
    change dite _ _ _ ≤ c ↔ _
    split_ifs with h
    · have := (exists_add_of_le h).choose_spec
      rw [this] at h
      conv_rhs => rw [this, add_comm]
      rw [add_le_add_iff_right]
    · rw [not_le] at h
      constructor <;> intro h'
      · simpa using add_le_add h' h.le
      · exact zero_le

end CanonicallyOrderedAdd

