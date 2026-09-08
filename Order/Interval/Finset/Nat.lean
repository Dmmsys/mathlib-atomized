/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Embedding
public import Mathlib.Order.Interval.Multiset

/-!
# Finite intervals of naturals

This file proves that `ℕ` is a `LocallyFiniteOrder` and calculates the cardinality of its
intervals as finsets and fintypes.

## TODO

Some lemmas can be generalized using `IsOrderedAddMonoid`, `CanonicallyOrderedAdd` or `SuccOrder`
and subsequently be moved upstream to `Order.Interval.Finset`.
-/

public section

assert_not_exists Ring

open Finset Nat

variable (a b c : ℕ)

namespace Nat

set_option backward.isDefEq.respectTransparency false in
/-
**Nat.instLocallyFiniteOrder** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
形式化陈述：instLocallyFiniteOrder : LocallyFiniteOrder Nat where finsetIcc a b
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `List.range'`：range'_0 (a b : Nat) : range' a b 0 = replicate b a
-/
instance instLocallyFiniteOrder : LocallyFiniteOrder ℕ where
  finsetIcc a b := ⟨List.range' a (b + 1 - a), List.nodup_range'⟩
  finsetIco a b := ⟨List.range' a (b - a), List.nodup_range'⟩
  finsetIoc a b := ⟨List.range' (a + 1) (b - a), List.nodup_range'⟩
  finsetIoo a b := ⟨List.range' (a + 1) (b - a - 1), List.nodup_range'⟩
  finset_mem_Icc a b x := by rw [Finset.mem_mk, Multiset.mem_coe, List.mem_range'_1]; lia
  finset_mem_Ico a b x := by rw [Finset.mem_mk, Multiset.mem_coe, List.mem_range'_1]; lia
  finset_mem_Ioc a b x := by rw [Finset.mem_mk, Multiset.mem_coe, List.mem_range'_1]; lia
  finset_mem_Ioo a b x := by rw [Finset.mem_mk, Multiset.mem_coe, List.mem_range'_1]; lia
/-
**Nat.** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Unique (Iic 0) := by
  rw [← Nat.bot_eq_zero]
  infer_instance
/-
**Nat.Icc_eq_range'** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：Icc_eq_range' : Icc a b = ⟨List.range' a (b + 1 - a), List.nodup_range'⟩
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Icc_eq_range' : Icc a b = ⟨List.range' a (b + 1 - a), List.nodup_range'⟩ :=
  rfl
/-
**Nat.Ico_eq_range'** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：Ico_eq_range' : Ico a b = ⟨List.range' a (b - a), List.nodup_range'⟩
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ico_eq_range' : Ico a b = ⟨List.range' a (b - a), List.nodup_range'⟩ :=
  rfl
/-
**Nat.Ioc_eq_range'** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：Ioc_eq_range' : Ioc a b = ⟨List.range' (a + 1) (b - a), List.nodup_range'⟩
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ioc_eq_range' : Ioc a b = ⟨List.range' (a + 1) (b - a), List.nodup_range'⟩ :=
  rfl
/-
**Nat.Ioo_eq_range'** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：Ioo_eq_range' : Ioo a b = ⟨List.range' (a + 1) (b - a - 1), List.nodup_ran
ge'⟩
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ioo_eq_range' : Ioo a b = ⟨List.range' (a + 1) (b - a - 1), List.nodup_range'⟩ :=
  rfl
/-
**Nat.uIcc_eq_range'** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：uIcc_eq_range' : uIcc a b = ⟨List.range' (min a b) (max a b + 1 - min a b)
, List.nodup_range'⟩
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem uIcc_eq_range' :
    uIcc a b = ⟨List.range' (min a b) (max a b + 1 - min a b), List.nodup_range'⟩ := rfl
/-
**Nat.Iio_eq_range** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：Iio_eq_range : Iio a = range a
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Iio_eq_range : Iio a = range a := by
  grind

@[simp]
/-
**Nat.Ico_zero_eq_range** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：Ico_zero_eq_range : Ico 0 a = range a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.bot_eq_zero`：⊥ = 0
· 使用定理 `Finset.Iio_eq_Ico`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : Locall
yFiniteOrder α] [inst_2 : OrderBot α] (a : α),   Finset.Iio a = Finset.Ico ⊥ a
· 使用定理 `Nat.Iio_eq_range`：Iio_eq_range : Iio a = range a
-/
theorem Ico_zero_eq_range : Ico 0 a = range a := by
  rw [← Nat.bot_eq_zero, ← Iio_eq_Ico, Iio_eq_range]
/-
**Nat.range_eq_Icc_zero_sub_one** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：range_eq_Icc_zero_sub_one (n : Nat) (hn : n != 0) : range n = Icc 0 (n - 1
)
参数：n : Nat；hn : n != 0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma range_eq_Icc_zero_sub_one (n : ℕ) (hn : n ≠ 0) : range n = Icc 0 (n - 1) := by
  grind
/-
**Nat._root_.Finset.range_eq_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Finset.range_eq_Ico : range a = Ico 0 a :=
  (Ico_zero_eq_range a).symm
/-
**Nat.range_succ_eq_Icc_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：range_succ_eq_Icc_zero (n : Nat) : range (n + 1) = Icc 0 n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.range_eq_Icc_zero_sub_one`：range_eq_Icc_zero_sub_one (n : Nat) (hn :
 n != 0) : range n = Icc 0 (n - 1)
· 使用定理 `Nat.add_one_ne_zero`：∀ (n : ℕ), n + 1 ≠ 0
· 使用定理 `Nat.add_sub_cancel_right`：∀ (n m : ℕ), n + m - m = n
-/
theorem range_succ_eq_Icc_zero (n : ℕ) : range (n + 1) = Icc 0 n := by
  rw [range_eq_Icc_zero_sub_one _ (Nat.add_one_ne_zero _), Nat.add_sub_cancel_right]
/-
**Nat.range_succ_eq_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：range_succ_eq_Iic (n : Nat) : range (n + 1) = Iic n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.range_succ_eq_Icc_zero`：range_succ_eq_Icc_zero (n : Nat) : range (n 
+ 1) = Icc 0 n
-/
theorem range_succ_eq_Iic (n : ℕ) : range (n + 1) = Iic n := by
  rw [range_succ_eq_Icc_zero]
  rfl
/-
**Nat.card_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (a b : ℕ), (Finset.Icc a b).card = b + 1 - a
参数：a b : ℕ；Finset.Icc a b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.length_range'`：∀ {s step n : ℕ}, (List.range' s n step).length = n
-/
@[simp] lemma card_Icc : #(Icc a b) = b + 1 - a := List.length_range' ..
/-
**Nat.card_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (a b : ℕ), (Finset.Ico a b).card = b - a
参数：a b : ℕ；Finset.Ico a b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.length_range'`：∀ {s step n : ℕ}, (List.range' s n step).length = n
-/
@[simp] lemma card_Ico : #(Ico a b) = b - a := List.length_range' ..
/-
**Nat.card_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (a b : ℕ), (Finset.Ioc a b).card = b - a
参数：a b : ℕ；Finset.Ioc a b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.length_range'`：∀ {s step n : ℕ}, (List.range' s n step).length = n
-/
@[simp] lemma card_Ioc : #(Ioc a b) = b - a := List.length_range' ..
/-
**Nat.card_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (a b : ℕ), (Finset.Ioo a b).card = b - a - 1
参数：a b : ℕ；Finset.Ioo a b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.length_range'`：∀ {s step n : ℕ}, (List.range' s n step).length = n
-/
@[simp] lemma card_Ioo : #(Ioo a b) = b - a - 1 := List.length_range' ..

@[simp]
/-
**Nat.card_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：card_uIcc : #(uIcc a b) = (b - a : Int).natAbs + 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.card_Icc`：∀ (a b : ℕ), (Finset.Icc a b).card = b + 1 - a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.natCast_inj`：∀ {m n : ℕ}, ↑m = ↑n ↔ m = n
· 使用定理 `Int.ofNat_sub`：∀ {m n : ℕ}, m ≤ n → ↑(n - m) = ↑n - ↑m
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
-/
theorem card_uIcc : #(uIcc a b) = (b - a : ℤ).natAbs + 1 :=
  (card_Icc _ _).trans <| by rw [← Int.natCast_inj, Int.ofNat_sub] <;> omega

@[simp]
/-
**Nat.card_Iic** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：card_Iic : #(Iic b) = b + 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.Iic_eq_Icc`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : Locall
yFiniteOrder α] [inst_2 : OrderBot α] (a : α),   Finset.Iic a = Finset.Icc ⊥ a
· 使用定理 `Nat.card_Icc`：∀ (a b : ℕ), (Finset.Icc a b).card = b + 1 - a
· 使用定理 `Nat.bot_eq_zero`：⊥ = 0
· 使用定理 `Nat.sub_zero`：∀ (n : ℕ), n - 0 = n
-/
lemma card_Iic : #(Iic b) = b + 1 := by rw [Iic_eq_Icc, card_Icc, Nat.bot_eq_zero, Nat.sub_zero]

@[simp]
/-
**Nat.card_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：card_Iio : #(Iio b) = b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.Iio_eq_Ico`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : Locall
yFiniteOrder α] [inst_2 : OrderBot α] (a : α),   Finset.Iio a = Finset.Ico ⊥ a
· 使用定理 `Nat.card_Ico`：∀ (a b : ℕ), (Finset.Ico a b).card = b - a
· 使用定理 `Nat.bot_eq_zero`：⊥ = 0
· 使用定理 `Nat.sub_zero`：∀ (n : ℕ), n - 0 = n
-/
theorem card_Iio : #(Iio b) = b := by rw [Iio_eq_Ico, card_Ico, Nat.bot_eq_zero, Nat.sub_zero]

-- TODO: Generalise the following series of lemmas.

@[simp]
/-
**Nat.Ico_succ_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：Ico_succ_singleton : Ico a (a + 1) = {a}
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ico_succ_singleton : Ico a (a + 1) = {a} := by grind

@[simp]
/-
**Nat.Ico_pred_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：Ico_pred_singleton {a : Nat} (h : 0 < a) : Ico (a - 1) a = {a - 1}
参数：h : 0 < a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_Ico`：mem_Ico : x in Ico a b ↔ a <= x ∧ x < b
· 使用定理 `Finset.mem_singleton`：mem_singleton {a b : α} : b in ({a} : Finset α) ↔ 
b = a
-/
theorem Ico_pred_singleton {a : ℕ} (h : 0 < a) : Ico (a - 1) a = {a - 1} := by
  ext x
  rw [mem_Ico, mem_singleton]
  lia

@[simp]
/-
**Nat.Ioc_succ_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：Ioc_succ_singleton : Ioc b (b + 1) = {b + 1}
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ioc_succ_singleton : Ioc b (b + 1) = {b + 1} := by grind

variable {a b c}
/-
**Nat.mem_Ioc_succ** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：mem_Ioc_succ : a in Ioc b (b + 1) ↔ a = b + 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.Ioc_succ_singleton`：Ioc_succ_singleton : Ioc b (b + 1) = {b + 1}
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_Ioc_succ : a ∈ Ioc b (b + 1) ↔ a = b + 1 := by simp
/-
**Nat.mem_Ioc_succ'** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：mem_Ioc_succ' (a : Ioc b (b + 1)) : a = ⟨b + 1, mem_Ioc.2 (by lia)⟩
参数：a : Ioc b (b + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_Ioc`：mem_Ioc : x in Ioc a b ↔ a < x ∧ x <= b
· 使用定理 `Subtype.val_inj`：val_inj {a b : Subtype p} : a.val = b.val ↔ a = b
· 使用引理 `Nat.mem_Ioc_succ`：mem_Ioc_succ : a in Ioc b (b + 1) ↔ a = b + 1
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma mem_Ioc_succ' (a : Ioc b (b + 1)) : a = ⟨b + 1, mem_Ioc.2 (by lia)⟩ :=
  Subtype.val_inj.1 (mem_Ioc_succ.1 a.2)
/-
**Nat.image_sub_const_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：image_sub_const_Ico (h : c <= a) : ((Ico a b).image fun x => x - c) = Ico 
(a - c) (b - c)
参数：h : c <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem image_sub_const_Ico (h : c ≤ a) :
    ((Ico a b).image fun x => x - c) = Ico (a - c) (b - c) := by
  ext x
  simp_rw [mem_image, mem_Ico]
  refine ⟨?_, fun h ↦ ⟨x + c, by lia⟩⟩
  rintro ⟨x, hx, rfl⟩
  lia
/-
**Nat.Ico_image_const_sub_eq_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：Ico_image_const_sub_eq_Ico (hac : a <= c) : ((Ico a b).image fun x => c - 
x) = Ico (c + 1 - b) (c + 1 - a)
参数：hac : a <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem Ico_image_const_sub_eq_Ico (hac : a ≤ c) :
    ((Ico a b).image fun x => c - x) = Ico (c + 1 - b) (c + 1 - a) := by
  ext x
  simp_rw [mem_image, mem_Ico]
  refine ⟨?_, fun h ↦ ⟨c - x, by lia⟩⟩
  rintro ⟨x, hx, rfl⟩
  lia
/-
**Nat.Ico_succ_left_eq_erase_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：Ico_succ_left_eq_erase_Ico : Ico a.succ b = erase (Ico a b) a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
theorem Ico_succ_left_eq_erase_Ico : Ico a.succ b = erase (Ico a b) a := by
  ext x
  simp_rw [mem_erase, mem_Ico]
  lia
/-
**Nat.Ico_succ_right_eq_insert_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：Ico_succ_right_eq_insert_Ico (h : a <= b) : Ico a b.succ = insert b (Ico a
 b)
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
theorem Ico_succ_right_eq_insert_Ico (h : a ≤ b) : Ico a b.succ = insert b (Ico a b) := by
  ext x
  simp_rw [mem_insert, mem_Ico]
  lia
/-
**Nat.mod_injOn_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：mod_injOn_Ico (n a : Nat) : Set.InjOn (· % a) (Finset.Ico n (n + a))
参数：n a : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.Ico_zero_eq_range`：Ico_zero_eq_range : Ico 0 a = range a
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
· 使用定理 `Nat.Ico_succ_left_eq_erase_Ico`：Ico_succ_left_eq_erase_Ico : Ico a.succ 
b = erase (Ico a b) a
· 使用定理 `Nat.succ_add`：∀ (n m : ℕ), n.succ + m = (n + m).succ
· 使用定理 `Nat.succ_eq_add_one`：∀ (n : ℕ), n.succ = n + 1
· 使用定理 `Nat.Ico_succ_right_eq_insert_Ico`：Ico_succ_right_eq_insert_Ico (h : a <=
 b) : Ico a b.succ = insert b (Ico a b)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.pos_iff_ne_zero`：∀ {n : ℕ}, 0 < n ↔ n ≠ 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Finset.Ico_eq_empty_of_le`：Ico_eq_empty_of_le (h : b <= a) : Ico a b = ∅
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LawfulSingleton.insert_empty_eq`：∀ {α : Type u} {β : Type v} {inst : Emp
tyCollection β} {inst_1 : Insert α β} {inst_2 : Singleton α β}   [self : LawfulS
ingleton α β] (x : α)…
· 使用定理 `Finset.instLawfulSingleton`：∀ {α : Type u_1} [inst : DecidableEq α], Law
fulSingleton α (Finset α)
· 使用定理 `Finset.erase_singleton`：erase_singleton (a : α) : ({a} : Finset α).erase
 a = ∅
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_Ico`：coe_Ico (a b : α) : (Ico a b : Set α) = Set.Ico a b
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Nat.lt_add_of_pos_right`：∀ {k n : ℕ}, 0 < k → n < n + k
· 使用定理 `Nat.add_mod_right`：∀ (x z : ℕ), (x + z) % z = x % z
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem mod_injOn_Ico (n a : ℕ) : Set.InjOn (· % a) (Finset.Ico n (n + a)) := by
  induction n with
  | zero =>
    simp only [zero_add, Ico_zero_eq_range]
    rintro k hk l hl (hkl : k % a = l % a)
    simp only [Finset.mem_range, Finset.mem_coe] at hk hl
    rwa [mod_eq_of_lt hk, mod_eq_of_lt hl] at hkl
  | succ n ih =>
    rw [Ico_succ_left_eq_erase_Ico, succ_add, succ_eq_add_one,
      Ico_succ_right_eq_insert_Ico (by lia)]
    rintro k hk l hl (hkl : k % a = l % a)
    have ha : 0 < a := Nat.pos_iff_ne_zero.2 <| by rintro rfl; simp at hk
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_erase] at hk hl
    rcases hk with ⟨hkn, rfl | hk⟩ <;> rcases hl with ⟨hln, rfl | hl⟩
    · rfl
    · rw [add_mod_right] at hkl
      refine (hln <| ih hl ?_ hkl.symm).elim
      simpa using Nat.lt_add_of_pos_right (n := n) ha
    · rw [add_mod_right] at hkl
      suffices k = n by contradiction
      refine ih hk ?_ hkl
      simpa using Nat.lt_add_of_pos_right (n := n) ha
    · refine ih ?_ ?_ hkl <;> simp only [Finset.mem_coe, hk, hl]

/-- Note that while this lemma cannot be easily generalized to a type class, it holds for ℤ as
well. See `Int.image_Ico_emod` for the ℤ version. -/
/-
**Nat.image_Ico_mod** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：image_Ico_mod (n a : Nat) : (Ico n (n + a)).image (· % a) = range a
参数：n a : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.range_zero`：range_zero : range 0 = ∅
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Finset.Ico_self`：Ico_self : Ico a a = ∅
· 使用定理 `Finset.image_empty`：image_empty (f : α -> β) : (∅ : Finset α).image f = 
∅
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
· 使用定理 `Nat.mod_add_div`：∀ (m k : ℕ), m % k + k * (m / k) = m
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Nat.mul_add`：∀ (n m k : ℕ), n * (m + k) = n * m + n * k
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Nat.add_le_add_right`：∀ {n m : ℕ}, n ≤ m → ∀ (k : ℕ), n + k ≤ m + k
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.add_le_add`：∀ {a b c d : ℕ}, a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Nat.add_lt_add_right`：∀ {n m : ℕ}, n < m → ∀ (k : ℕ), n + k < m + k
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
Note that while this lemma cannot be easily generalized to a type class, it hold
s for ℤ as
well. See `Int.image_Ico_emod` for the ℤ version.
-/
theorem image_Ico_mod (n a : ℕ) : (Ico n (n + a)).image (· % a) = range a := by
  obtain rfl | ha := eq_or_ne a 0
  · rw [range_zero, add_zero, Ico_self, image_empty]
  ext i
  simp only [mem_image, mem_range, mem_Ico]
  constructor
  · rintro ⟨i, _, rfl⟩
    exact mod_lt i ha.bot_lt
  intro hia
  have hn := Nat.mod_add_div n a
  obtain hi | hi := lt_or_ge i (n % a)
  · refine ⟨i + a * (n / a + 1), ⟨?_, ?_⟩, ?_⟩
    · rw [add_comm (n / a), Nat.mul_add, mul_one, ← add_assoc]
      refine hn.symm.le.trans (Nat.add_le_add_right ?_ _)
      simpa only [zero_add] using add_le_add (zero_le i) (Nat.mod_lt n ha.bot_lt).le
    · refine lt_of_lt_of_le (Nat.add_lt_add_right hi (a * (n / a + 1))) ?_
      rw [Nat.mul_add, mul_one, ← add_assoc, hn]
    · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hia]
  · refine ⟨i + a * (n / a), ⟨?_, ?_⟩, ?_⟩
    · lia
    · lia
    · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hia]

section Multiset

open Multiset

/-
**Nat.multiset_Ico_map_mod** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：multiset_Ico_map_mod (n a : Nat) : (Multiset.Ico n (n + a)).map (· % a) = 
Multiset.range a
参数：n a : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.Nodup.dedup`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Multi
set α}, s.Nodup → s.dedup = s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.nodup_map_iff_inj_on`：nodup_map_iff_inj_on {f : α -> β} {s : Mu
ltiset α} (d : Nodup s) : Nodup (map f s) ↔ forall x in s, forall y in s, f x = 
f y -> x = y
· 使用定理 `Finset.nodup`：∀ {α : Type u_4} (self : Finset α), self.val.Nodup
· 使用定理 `Nat.mod_injOn_Ico`：mod_injOn_Ico (n a : Nat) : Set.InjOn (· % a) (Finset
.Ico n (n + a))
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Nat.image_Ico_mod`：image_Ico_mod (n a : Nat) : (Ico n (n + a)).image (· 
% a) = range a
-/
theorem multiset_Ico_map_mod (n a : ℕ) :
    (Multiset.Ico n (n + a)).map (· % a) = Multiset.range a := by
  convert! congr_arg Finset.val (image_Ico_mod n a)
  refine ((nodup_map_iff_inj_on (Finset.Ico _ _).nodup).2 <| ?_).dedup.symm
  exact mod_injOn_Ico _ _

end Multiset

end Nat

namespace List

/-
**List.toFinset_range'_1** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ (a b : ℕ), (List.range' a b).toFinset = Finset.Ico a (a + b)
参数：a b : ℕ；List.range' a b；a + b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用引理 `List.range'`：range'_0 (a b : Nat) : range' a b 0 = replicate b a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.mem_toFinset`：mem_toFinset : a in l.toFinset ↔ a in l
· 使用定理 `List.mem_range'_1`：∀ {s n m : ℕ}, m ∈ List.range' s n ↔ s ≤ m ∧ m < s + 
n
· 使用定理 `Finset.mem_Ico`：mem_Ico : x in Ico a b ↔ a <= x ∧ x < b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma toFinset_range'_1 (a b : ℕ) : (List.range' a b).toFinset = Ico a (a + b) := by
  ext x
  rw [List.mem_toFinset, List.mem_range'_1, Finset.mem_Ico]
/-
**List.toFinset_range'_1_1** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ (a : ℕ), (List.range' 1 a).toFinset = Finset.Icc 1 a
参数：a : ℕ；List.range' 1 a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用引理 `List.range'`：range'_0 (a b : Nat) : range' a b 0 = replicate b a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.mem_toFinset`：mem_toFinset : a in l.toFinset ↔ a in l
· 使用定理 `List.mem_range'_1`：∀ {s n m : ℕ}, m ∈ List.range' s n ↔ s ≤ m ∧ m < s + 
n
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Nat.lt_succ_iff`：∀ {m n : ℕ}, m < n.succ ↔ m ≤ n
· 使用定理 `Finset.mem_Icc`：mem_Icc : x in Icc a b ↔ a <= x ∧ x <= b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma toFinset_range'_1_1 (a : ℕ) : (List.range' 1 a).toFinset = Icc 1 a := by
  ext x
  rw [List.mem_toFinset, List.mem_range'_1, add_comm, Nat.lt_succ_iff, Finset.mem_Icc]
/-
**List.toFinset_range** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：toFinset_range (a : Nat) : (List.range a).toFinset = Finset.range a
参数：a : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.mem_toFinset`：mem_toFinset : a in l.toFinset ↔ a in l
· 使用定理 `List.mem_range`：∀ {m n : ℕ}, m ∈ List.range n ↔ m < n
· 使用定理 `Finset.mem_range`：mem_range : m in range n ↔ m < n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma toFinset_range (a : ℕ) : (List.range a).toFinset = Finset.range a := by
  ext x
  rw [List.mem_toFinset, List.mem_range, Finset.mem_range]

end List

namespace Finset

/-
**Finset.range_image_pred_top_sub** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：range_image_pred_top_sub (n : Nat) : ((Finset.range n).image fun j => n - 
1 - j) = Finset.range n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.range_zero`：range_zero : range 0 = ∅
· 使用定理 `Finset.image_empty`：image_empty (f : α -> β) : (∅ : Finset α).image f = 
∅
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.range_eq_Ico`：∀ (a : ℕ), Finset.range a = Finset.Ico 0 a
· 使用定理 `Nat.Ico_image_const_sub_eq_Ico`：Ico_image_const_sub_eq_Ico (hac : a <= c
) : ((Ico a b).image fun x => c - x) = Ico (c + 1 - b) (c + 1 - a)
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.succ_sub_succ`：∀ (n m : ℕ), n.succ - m.succ = n - m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.sub_self`：∀ (n : ℕ), n - n = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem range_image_pred_top_sub (n : ℕ) :
    ((Finset.range n).image fun j => n - 1 - j) = Finset.range n := by
  cases n
  · rw [range_zero, image_empty]
  · rw [Finset.range_eq_Ico, Nat.Ico_image_const_sub_eq_Ico (Nat.zero_le _)]
    simp_rw [succ_sub_succ, Nat.sub_zero, Nat.sub_self]
/-
**Finset.range_add_eq_union** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：range_add_eq_union : range (a + b) = range a union (range b).map (addLeftE
mbedding a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.range_eq_Ico`：∀ (a : ℕ), Finset.range a = Finset.Ico 0 a
· 使用定理 `Finset.map_eq_image`：map_eq_image (f : α ↪ β) (s : Finset α) : s.map f =
 s.image f
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.Ico_zero_eq_range`：Ico_zero_eq_range : Ico 0 a = range a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `addLeftEmbedding_apply`：∀ {G : Type u_1} [inst : Add G] [inst_1 : IsLeft
CancelAdd G] (g h : G), (addLeftEmbedding g) h = g + h
· 使用定理 `Finset.Ico_union_Ico_eq_Ico`：Ico_union_Ico_eq_Ico {a b c : α} (hab : a <
= b) (hbc : b <= c) : Ico a b union Ico b c = Ico a c
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
-/
theorem range_add_eq_union : range (a + b) = range a ∪ (range b).map (addLeftEmbedding a) := by
  simp_rw [Finset.range_eq_Ico, map_eq_image]
  convert! (Ico_union_Ico_eq_Ico a.zero_le (a.le_add_right b)).symm
  ext x
  simp only [Ico_zero_eq_range, mem_image, mem_range, addLeftEmbedding_apply, mem_Ico]
  constructor
  · lia
  · rintro h
    exact ⟨x - a, by lia⟩

end Finset

section Induction

variable {P : ℕ → Prop}

/-
**Nat.decreasing_induction_of_not_bddAbove** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nat.decreasing_induction_of_not_bddAbove (h : forall n, P (n + 1) -> P n) 
(hP : ¬BddAbove { x | P x }) (n : Nat) : P n
参数：h : forall n, P (n + 1) -> P n；hP : ¬BddAbove { x | P x }；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_bddAbove_iff`：not_bddAbove_iff {α : Type*} [LinearOrder α] {s : Set 
α} : ¬BddAbove s ↔ forall x, exists y in s, x < y
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem Nat.decreasing_induction_of_not_bddAbove (h : ∀ n, P (n + 1) → P n)
    (hP : ¬BddAbove { x | P x }) (n : ℕ) : P n :=
  let ⟨_, hm, hl⟩ := not_bddAbove_iff.1 hP n
  decreasingInduction (fun _ _ => h _) hm hl.le

@[elab_as_elim]
/-
**Nat.strong_decreasing_induction** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Nat.strong_decreasing_induction (base : exists n, forall m > n, P m) (step
 : forall n, (forall m > n, P m) -> P n) (n : Nat) : P n
参数：base : exists n, forall m > n, P m；step : forall n, (forall m > n, P m) -> P 
n；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.decreasing_induction_of_not_bddAbove`：Nat.decreasing_induction_of_no
t_bddAbove (h : forall n, P (n + 1) -> P n) (hP : ¬BddAbove { x | P x }) (n : Na
t) : P n
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma Nat.strong_decreasing_induction (base : ∃ n, ∀ m > n, P m) (step : ∀ n, (∀ m > n, P m) → P n)
    (n : ℕ) : P n := by
  apply Nat.decreasing_induction_of_not_bddAbove (P := fun n ↦ ∀ m ≥ n, P m) _ _ n n le_rfl
  · intro n ih m hm
    rcases hm.eq_or_lt with rfl | hm
    · exact step n ih
    · exact ih m hm
  · rintro ⟨b, hb⟩
    rcases base with ⟨n, hn⟩
    specialize @hb (n + b + 1) (fun m hm ↦ hn _ _)
    all_goals lia
/-
**Nat.decreasing_induction_of_infinite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nat.decreasing_induction_of_infinite (h : forall n, P (n + 1) -> P n) (hP 
: { x | P x }.Infinite) (n : Nat) : P n
参数：h : forall n, P (n + 1) -> P n；hP : { x | P x }.Infinite；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.decreasing_induction_of_not_bddAbove`：Nat.decreasing_induction_of_no
t_bddAbove (h : forall n, P (n + 1) -> P n) (hP : ¬BddAbove { x | P x }) (n : Na
t) : P n
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `BddAbove.finite`：∀ {α : Type u_2} [inst : Preorder α] [LocallyFiniteOrde
rBot α] {s : Set α}, BddAbove s → s.Finite
-/
theorem Nat.decreasing_induction_of_infinite
    (h : ∀ n, P (n + 1) → P n) (hP : { x | P x }.Infinite) (n : ℕ) : P n :=
  Nat.decreasing_induction_of_not_bddAbove h (mt BddAbove.finite hP) n
/-
**Nat.cauchy_induction'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nat.cauchy_induction' (seed : Nat) (h : forall n, P (n + 1) -> P n) (hs : 
P seed) (hi : forall x, seed <= x -> P x -> exists y, x < y ∧ P y) (n : Nat) : P
 n
参数：seed : Nat；h : forall n, P (n + 1) -> P n；hs : P seed；hi : forall x, seed <= 
x -> P x -> exists y, x < y ∧ P y；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.decreasing_induction_of_infinite`：Nat.decreasing_induction_of_infini
te (h : forall n, P (n + 1) -> P n) (hP : { x | P x }.Infinite) (n : Nat) : P n
· 使用定理 `Set.Finite.exists_maximal`：∀ {α : Type u_2} [inst : LE α] [IsTrans α LE.
le] {s : Set α}, s.Finite → s.Nonempty → ∃ i, Maximal (fun x => x ∈ s) i
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `not_lt_iff_le_imp_ge`：not_lt_iff_le_imp_ge : ¬ a < b ↔ (a <= b -> b <= a
)
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem Nat.cauchy_induction' (seed : ℕ) (h : ∀ n, P (n + 1) → P n) (hs : P seed)
    (hi : ∀ x, seed ≤ x → P x → ∃ y, x < y ∧ P y) (n : ℕ) : P n := by
  apply Nat.decreasing_induction_of_infinite h fun hf => _
  intro hf
  obtain ⟨m, hP, hm⟩ := hf.exists_maximal ⟨seed, hs⟩
  obtain ⟨y, hl, hy⟩ := hi m (le_of_not_gt <| not_lt_iff_le_imp_ge.2 <| hm hs) hP
  exact hl.not_ge (hm hy hl.le)
/-
**Nat.cauchy_induction** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nat.cauchy_induction (h : forall n, P (n + 1) -> P n) (seed : Nat) (hs : P
 seed) (f : Nat -> Nat) (hf : forall x, seed <= x -> P x -> x < f x ∧ P (f x)) (
n : Nat) : P n
参数：h : forall n, P (n + 1) -> P n；seed : Nat；hs : P seed；f : Nat -> Nat；hf : for
all x, seed <= x -> P x -> x < f x ∧ P (f x)；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.cauchy_induction'`：Nat.cauchy_induction' (seed : Nat) (h : forall n,
 P (n + 1) -> P n) (hs : P seed) (hi : forall x, seed <= x -> P x -> exists y, x
 < y ∧ P y)…
-/
theorem Nat.cauchy_induction (h : ∀ n, P (n + 1) → P n) (seed : ℕ) (hs : P seed) (f : ℕ → ℕ)
    (hf : ∀ x, seed ≤ x → P x → x < f x ∧ P (f x)) (n : ℕ) : P n :=
  seed.cauchy_induction' h hs (fun x hl hx => ⟨f x, hf x hl hx⟩) n
/-
**Nat.cauchy_induction_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nat.cauchy_induction_mul (h : forall (n : Nat), P (n + 1) -> P n) (k seed 
: Nat) (hk : 1 < k) (hs : P seed.succ) (hm : forall x, seed < x -> P x -> P (k *
 x)) (n : Nat) : P n
参数：h : forall (n : Nat), P (n + 1) -> P n；k seed : Nat；hk : 1 < k；hs : P seed.su
cc；hm : forall x, seed < x -> P x -> P (k * x)；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.cauchy_induction`：Nat.cauchy_induction (h : forall n, P (n + 1) -> P
 n) (seed : Nat) (hs : P seed) (f : Nat -> Nat) (hf : forall x, seed <= x -> P x
 -> x < f …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.mul_lt_mul_right`：∀ {a b c : ℕ}, 0 < a → (b * a < c * a ↔ b < c)
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
-/
theorem Nat.cauchy_induction_mul (h : ∀ (n : ℕ), P (n + 1) → P n) (k seed : ℕ) (hk : 1 < k)
    (hs : P seed.succ) (hm : ∀ x, seed < x → P x → P (k * x)) (n : ℕ) : P n := by
  apply Nat.cauchy_induction h _ hs (k * ·) fun x hl hP => ⟨_, hm x hl hP⟩
  intro _ hl _
  convert! (Nat.mul_lt_mul_right <| seed.succ_pos.trans_le hl).2 hk
  rw [one_mul]
/-
**Nat.cauchy_induction_two_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nat.cauchy_induction_two_mul (h : forall n, P (n + 1) -> P n) (seed : Nat)
 (hs : P seed.succ) (hm : forall x, seed < x -> P x -> P (2 * x)) (n : Nat) : P 
n
参数：h : forall n, P (n + 1) -> P n；seed : Nat；hs : P seed.succ；hm : forall x, see
d < x -> P x -> P (2 * x)；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.cauchy_induction_mul`：Nat.cauchy_induction_mul (h : forall (n : Nat)
, P (n + 1) -> P n) (k seed : Nat) (hk : 1 < k) (hs : P seed.succ) (hm : forall 
x, seed < x ->…
· 使用定理 `Nat.one_lt_two`：1 < 2
-/
theorem Nat.cauchy_induction_two_mul (h : ∀ n, P (n + 1) → P n) (seed : ℕ) (hs : P seed.succ)
    (hm : ∀ x, seed < x → P x → P (2 * x)) (n : ℕ) : P n :=
  Nat.cauchy_induction_mul h 2 seed Nat.one_lt_two hs hm n
/-
**Nat.pow_imp_self_of_one_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nat.pow_imp_self_of_one_lt {M} [Monoid M] (k : Nat) (hk : 1 < k) (P : M ->
 Prop) (hmul : forall x y, P x -> P (x * y) ∨ P (y * x)) (hpow : forall x, P (x 
^ k) -> P x) : forall n x, P (x ^ n) -> P x
参数：k : Nat；hk : 1 < k；P : M -> Prop；hmul : forall x y, P x -> P (x * y) ∨ P (y *
 x)；hpow : forall x, P (x ^ k) -> P x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.cauchy_induction_mul`：Nat.cauchy_induction_mul (h : forall (n : Nat)
, P (n + 1) -> P n) (k seed : Nat) (hk : 1 < k) (hs : P seed.succ) (hm : forall 
x, seed < x ->…
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Eq.subst`：∀ {α : Sort u} {motive : α → Prop} {a b : α}, a = b → motive a
 → motive b
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
-/
theorem Nat.pow_imp_self_of_one_lt {M} [Monoid M] (k : ℕ) (hk : 1 < k)
    (P : M → Prop) (hmul : ∀ x y, P x → P (x * y) ∨ P (y * x))
    (hpow : ∀ x, P (x ^ k) → P x) : ∀ n x, P (x ^ n) → P x :=
  k.cauchy_induction_mul (fun n ih x hx ↦ ih x <| (hmul _ x hx).elim
    (fun h ↦ by rwa [_root_.pow_succ]) fun h ↦ by rwa [_root_.pow_succ']) 0 hk
    (fun x hx ↦ pow_one x ▸ hx) fun n _ hn x hx ↦ hpow x <| hn _ <| (pow_mul x k n).subst hx

end Induction

