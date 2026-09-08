/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Interval.Set.UnorderedInterval

/-!
# (Pre)images of set intervals under `Fin` operations

In this file we prove basic lemmas about preimages and images of the intervals
under the following operations:

- `Fin.val`,
- `Fin.castLE` (preimages only),
- `Fin.castAdd`,
- `Fin.cast`,
- `Fin.castSucc`,
- `Fin.natAdd`,
- `Fin.addNat`,
- `Fin.succ`,
- `Fin.rev`.
-/

public section

open Function Set

namespace Fin

variable {m n : ℕ}

/-!
### (Pre)images under `Fin.val`
-/

@[simp]
/-
**Fin.range_val** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：range_val : range ((↑) : Fin n -> Nat) = Set.Iio n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
### (Pre)images under `Fin.val`
-/
theorem range_val : range ((↑) : Fin n → ℕ) = Set.Iio n := by ext; simp [Fin.exists_iff]
/-
**Fin.preimage_val_Ici_val** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n : ℕ} (i : Fin n), Fin.val ⁻¹' Set.Ici ↑i = Set.Ici i
参数：i : Fin n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem preimage_val_Ici_val (i : Fin n) : (↑) ⁻¹' Ici (i : ℕ) = Ici i := rfl
/-
**Fin.preimage_val_Ioi_val** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n : ℕ} (i : Fin n), Fin.val ⁻¹' Set.Ioi ↑i = Set.Ioi i
参数：i : Fin n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem preimage_val_Ioi_val (i : Fin n) : (↑) ⁻¹' Ioi (i : ℕ) = Ioi i := rfl
/-
**Fin.preimage_val_Iic_val** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n : ℕ} (i : Fin n), Fin.val ⁻¹' Set.Iic ↑i = Set.Iic i
参数：i : Fin n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem preimage_val_Iic_val (i : Fin n) : (↑) ⁻¹' Iic (i : ℕ) = Iic i := rfl
/-
**Fin.preimage_val_Iio_val** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n : ℕ} (i : Fin n), Fin.val ⁻¹' Set.Iio ↑i = Set.Iio i
参数：i : Fin n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem preimage_val_Iio_val (i : Fin n) : (↑) ⁻¹' Iio (i : ℕ) = Iio i := rfl
/-
**Fin.preimage_val_Icc_val** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n : ℕ} (i j : Fin n), Fin.val ⁻¹' Set.Icc ↑i ↑j = Set.Icc i j
参数：i j : Fin n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem preimage_val_Icc_val (i j : Fin n) : (↑) ⁻¹' Icc (i : ℕ) j = Icc i j := rfl
/-
**Fin.preimage_val_Ico_val** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n : ℕ} (i j : Fin n), Fin.val ⁻¹' Set.Ico ↑i ↑j = Set.Ico i j
参数：i j : Fin n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem preimage_val_Ico_val (i j : Fin n) : (↑) ⁻¹' Ico (i : ℕ) j = Ico i j := rfl
/-
**Fin.preimage_val_Ioc_val** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n : ℕ} (i j : Fin n), Fin.val ⁻¹' Set.Ioc ↑i ↑j = Set.Ioc i j
参数：i j : Fin n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem preimage_val_Ioc_val (i j : Fin n) : (↑) ⁻¹' Ioc (i : ℕ) j = Ioc i j := rfl
/-
**Fin.preimage_val_Ioo_val** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n : ℕ} (i j : Fin n), Fin.val ⁻¹' Set.Ioo ↑i ↑j = Set.Ioo i j
参数：i j : Fin n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem preimage_val_Ioo_val (i j : Fin n) : (↑) ⁻¹' Ioo (i : ℕ) j = Ioo i j := rfl
/-
**Fin.preimage_val_uIcc_val** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n : ℕ} (i j : Fin n), Fin.val ⁻¹' Set.uIcc ↑i ↑j = Set.uIcc i j
参数：i j : Fin n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem preimage_val_uIcc_val (i j : Fin n) : (↑) ⁻¹' uIcc (i : ℕ) j = uIcc i j := rfl
/-
**Fin.preimage_val_uIoc_val** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n : ℕ} (i j : Fin n), Fin.val ⁻¹' Set.uIoc ↑i ↑j = Set.uIoc i j
参数：i j : Fin n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem preimage_val_uIoc_val (i j : Fin n) : (↑) ⁻¹' uIoc (i : ℕ) j = uIoc i j := rfl
/-
**Fin.preimage_val_uIoo_val** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n : ℕ} (i j : Fin n), Fin.val ⁻¹' Set.uIoo ↑i ↑j = Set.uIoo i j
参数：i j : Fin n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem preimage_val_uIoo_val (i j : Fin n) : (↑) ⁻¹' uIoo (i : ℕ) j = uIoo i j := rfl

@[simp]
/-
**Fin.image_val_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：image_val_Ici (i : Fin n) : (↑) '' Ici i = Ico (i : Nat) n
参数：i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.preimage_val_Ici_val`：∀ {n : ℕ} (i : Fin n), Fin.val ⁻¹' Set.Ici ↑i 
= Set.Ici i
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用定理 `Fin.range_val`：range_val : range ((↑) : Fin n -> Nat) = Set.Iio n
· 使用定理 `Set.Ici_inter_Iio`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.I
ci a ∩ Set.Iio b = Set.Ico a b
-/
theorem image_val_Ici (i : Fin n) : (↑) '' Ici i = Ico (i : ℕ) n := by
  rw [← preimage_val_Ici_val, image_preimage_eq_inter_range, range_val, Ici_inter_Iio]

@[simp]
/-
**Fin.image_val_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：image_val_Iic (i : Fin n) : (↑) '' Iic i = Iic (i : Nat)
参数：i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.preimage_val_Iic_val`：∀ {n : ℕ} (i : Fin n), Fin.val ⁻¹' Set.Iic ↑i 
= Set.Iic i
· 使用定理 `Set.image_preimage_eq_of_subset`：image_preimage_eq_of_subset {f : α -> β
} {s : Set β} (hs : s subseteq range f) : f '' f ⁻¹' s = s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Fin.range_val`：range_val : range ((↑) : Fin n -> Nat) = Set.Iio n
-/
theorem image_val_Iic (i : Fin n) : (↑) '' Iic i = Iic (i : ℕ) := by
  rw [← preimage_val_Iic_val, image_preimage_eq_of_subset]
  simp [range_val]

@[simp]
/-
**Fin.image_val_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：image_val_Ioi (i : Fin n) : (↑) '' Ioi i = Ioo (i : Nat) n
参数：i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.preimage_val_Ioi_val`：∀ {n : ℕ} (i : Fin n), Fin.val ⁻¹' Set.Ioi ↑i 
= Set.Ioi i
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用定理 `Fin.range_val`：range_val : range ((↑) : Fin n -> Nat) = Set.Iio n
· 使用定理 `Set.Ioi_inter_Iio`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.I
oi a ∩ Set.Iio b = Set.Ioo a b
-/
theorem image_val_Ioi (i : Fin n) : (↑) '' Ioi i = Ioo (i : ℕ) n := by
  rw [← preimage_val_Ioi_val, image_preimage_eq_inter_range, range_val, Ioi_inter_Iio]

@[simp]
/-
**Fin.image_val_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：image_val_Iio (i : Fin n) : (↑) '' Iio i = Iio (i : Nat)
参数：i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.preimage_val_Iio_val`：∀ {n : ℕ} (i : Fin n), Fin.val ⁻¹' Set.Iio ↑i 
= Set.Iio i
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用定理 `Fin.range_val`：range_val : range ((↑) : Fin n -> Nat) = Set.Iio n
· 使用定理 `Set.inter_eq_left`：∀ {α : Type u} {s t : Set α}, s ∩ t = s ↔ s ⊆ t
· 使用定理 `Set.Iio_subset_Iio`：Iio_subset_Iio (h : a <= b) : Iio a subseteq Iio b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Fin.is_lt`：∀ {n : ℕ} (a : Fin n), ↑a < n
-/
theorem image_val_Iio (i : Fin n) : (↑) '' Iio i = Iio (i : ℕ) := by
  rw [← preimage_val_Iio_val, image_preimage_eq_inter_range, range_val, inter_eq_left]
  exact Iio_subset_Iio i.is_lt.le

@[simp]
/-
**Fin.image_val_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：image_val_Icc (i j : Fin n) : (↑) '' Icc i j = Icc (i : Nat) j
参数：i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.preimage_val_Icc_val`：∀ {n : ℕ} (i j : Fin n), Fin.val ⁻¹' Set.Icc ↑
i ↑j = Set.Icc i j
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用定理 `Fin.range_val`：range_val : range ((↑) : Fin n -> Nat) = Set.Iio n
· 使用定理 `Set.inter_eq_left`：∀ {α : Type u} {s t : Set α}, s ∩ t = s ↔ s ⊆ t
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Fin.is_lt`：∀ {n : ℕ} (a : Fin n), ↑a < n
-/
theorem image_val_Icc (i j : Fin n) : (↑) '' Icc i j = Icc (i : ℕ) j := by
  rw [← preimage_val_Icc_val, image_preimage_eq_inter_range, range_val, inter_eq_left]
  exact fun k hk ↦ hk.2.trans_lt j.is_lt

@[simp]
/-
**Fin.image_val_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：image_val_Ico (i j : Fin n) : (↑) '' Ico i j = Ico (i : Nat) j
参数：i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.preimage_val_Ico_val`：∀ {n : ℕ} (i j : Fin n), Fin.val ⁻¹' Set.Ico ↑
i ↑j = Set.Ico i j
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用定理 `Fin.range_val`：range_val : range ((↑) : Fin n -> Nat) = Set.Iio n
· 使用定理 `Set.inter_eq_left`：∀ {α : Type u} {s t : Set α}, s ∩ t = s ↔ s ⊆ t
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Fin.is_lt`：∀ {n : ℕ} (a : Fin n), ↑a < n
-/
theorem image_val_Ico (i j : Fin n) : (↑) '' Ico i j = Ico (i : ℕ) j := by
  rw [← preimage_val_Ico_val, image_preimage_eq_inter_range, range_val, inter_eq_left]
  exact fun k hk ↦ hk.2.trans j.is_lt

@[simp]
/-
**Fin.image_val_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：image_val_Ioc (i j : Fin n) : (↑) '' Ioc i j = Ioc (i : Nat) j
参数：i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.preimage_val_Ioc_val`：∀ {n : ℕ} (i j : Fin n), Fin.val ⁻¹' Set.Ioc ↑
i ↑j = Set.Ioc i j
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用定理 `Fin.range_val`：range_val : range ((↑) : Fin n -> Nat) = Set.Iio n
· 使用定理 `Set.inter_eq_left`：∀ {α : Type u} {s t : Set α}, s ∩ t = s ↔ s ⊆ t
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Fin.is_lt`：∀ {n : ℕ} (a : Fin n), ↑a < n
-/
theorem image_val_Ioc (i j : Fin n) : (↑) '' Ioc i j = Ioc (i : ℕ) j := by
  rw [← preimage_val_Ioc_val, image_preimage_eq_inter_range, range_val, inter_eq_left]
  exact fun k hk ↦ hk.2.trans_lt j.is_lt

@[simp]
/-
**Fin.image_val_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：image_val_Ioo (i j : Fin n) : (↑) '' Ioo i j = Ioo (i : Nat) j
参数：i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.preimage_val_Ioo_val`：∀ {n : ℕ} (i j : Fin n), Fin.val ⁻¹' Set.Ioo ↑
i ↑j = Set.Ioo i j
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用定理 `Fin.range_val`：range_val : range ((↑) : Fin n -> Nat) = Set.Iio n
· 使用定理 `Set.inter_eq_left`：∀ {α : Type u} {s t : Set α}, s ∩ t = s ↔ s ⊆ t
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Fin.is_lt`：∀ {n : ℕ} (a : Fin n), ↑a < n
-/
theorem image_val_Ioo (i j : Fin n) : (↑) '' Ioo i j = Ioo (i : ℕ) j := by
  rw [← preimage_val_Ioo_val, image_preimage_eq_inter_range, range_val, inter_eq_left]
  exact fun k hk ↦ hk.2.trans j.is_lt
/-
**Fin.image_val_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n : ℕ} (i j : Fin n), Fin.val '' Set.uIcc i j = Set.uIcc ↑i ↑j
参数：i j : Fin n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.image_val_Icc`：image_val_Icc (i j : Fin n) : (↑) '' Icc i j = Icc (i
 : Nat) j
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem image_val_uIcc (i j : Fin n) : (↑) '' uIcc i j = uIcc (i : ℕ) j := by simp [uIcc]
/-
**Fin.image_val_uIoc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n : ℕ} (i j : Fin n), Fin.val '' Set.uIoc i j = Set.uIoc ↑i ↑j
参数：i j : Fin n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.image_val_Ioc`：image_val_Ioc (i j : Fin n) : (↑) '' Ioc i j = Ioc (i
 : Nat) j
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem image_val_uIoc (i j : Fin n) : (↑) '' uIoc i j = uIoc (i : ℕ) j := by simp [uIoc]
/-
**Fin.image_val_uIoo** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n : ℕ} (i j : Fin n), Fin.val '' Set.uIoo i j = Set.uIoo ↑i ↑j
参数：i j : Fin n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.image_val_Ioo`：image_val_Ioo (i j : Fin n) : (↑) '' Ioo i j = Ioo (i
 : Nat) j
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem image_val_uIoo (i j : Fin n) : (↑) '' uIoo i j = uIoo (i : ℕ) j := by simp [uIoo]

/-!
### Preimages under `Fin.castLE`
-/

@[simp]
/-
**Fin.preimage_castLE_Ici_castLE** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_castLE_Ici_castLE (i : Fin m) (h : m <= n) : castLE h ⁻¹' Ici (ca
stLE h i) = Ici i
参数：i : Fin m；h : m <= n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Preimages under `Fin.castLE`
-/
theorem preimage_castLE_Ici_castLE (i : Fin m) (h : m ≤ n) :
    castLE h ⁻¹' Ici (castLE h i) = Ici i :=
  rfl

@[simp]
/-
**Fin.preimage_castLE_Ioi_castLE** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_castLE_Ioi_castLE (i : Fin m) (h : m <= n) : castLE h ⁻¹' Ioi (ca
stLE h i) = Ioi i
参数：i : Fin m；h : m <= n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_castLE_Ioi_castLE (i : Fin m) (h : m ≤ n) :
    castLE h ⁻¹' Ioi (castLE h i) = Ioi i :=
  rfl

@[simp]
/-
**Fin.preimage_castLE_Iic_castLE** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_castLE_Iic_castLE (i : Fin m) (h : m <= n) : castLE h ⁻¹' Iic (ca
stLE h i) = Iic i
参数：i : Fin m；h : m <= n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_castLE_Iic_castLE (i : Fin m) (h : m ≤ n) :
    castLE h ⁻¹' Iic (castLE h i) = Iic i :=
  rfl

@[simp]
/-
**Fin.preimage_castLE_Iio_castLE** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_castLE_Iio_castLE (i : Fin m) (h : m <= n) : castLE h ⁻¹' Iio (ca
stLE h i) = Iio i
参数：i : Fin m；h : m <= n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_castLE_Iio_castLE (i : Fin m) (h : m ≤ n) :
    castLE h ⁻¹' Iio (castLE h i) = Iio i :=
  rfl

@[simp]
/-
**Fin.preimage_castLE_Icc_castLE** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_castLE_Icc_castLE (i j : Fin m) (h : m <= n) : castLE h ⁻¹' Icc (
castLE h i) (castLE h j) = Icc i j
参数：i j : Fin m；h : m <= n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_castLE_Icc_castLE (i j : Fin m) (h : m ≤ n) :
    castLE h ⁻¹' Icc (castLE h i) (castLE h j) = Icc i j :=
  rfl

@[simp]
/-
**Fin.preimage_castLE_Ico_castLE** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_castLE_Ico_castLE (i j : Fin m) (h : m <= n) : castLE h ⁻¹' Ico (
castLE h i) (castLE h j) = Ico i j
参数：i j : Fin m；h : m <= n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_castLE_Ico_castLE (i j : Fin m) (h : m ≤ n) :
    castLE h ⁻¹' Ico (castLE h i) (castLE h j) = Ico i j :=
  rfl

@[simp]
/-
**Fin.preimage_castLE_Ioc_castLE** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_castLE_Ioc_castLE (i j : Fin m) (h : m <= n) : castLE h ⁻¹' Ioc (
castLE h i) (castLE h j) = Ioc i j
参数：i j : Fin m；h : m <= n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_castLE_Ioc_castLE (i j : Fin m) (h : m ≤ n) :
    castLE h ⁻¹' Ioc (castLE h i) (castLE h j) = Ioc i j :=
  rfl

@[simp]
/-
**Fin.preimage_castLE_Ioo_castLE** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_castLE_Ioo_castLE (i j : Fin m) (h : m <= n) : castLE h ⁻¹' Ioo (
castLE h i) (castLE h j) = Ioo i j
参数：i j : Fin m；h : m <= n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_castLE_Ioo_castLE (i j : Fin m) (h : m ≤ n) :
    castLE h ⁻¹' Ioo (castLE h i) (castLE h j) = Ioo i j :=
  rfl

@[simp]
/-
**Fin.preimage_castLE_uIcc_castLE** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_castLE_uIcc_castLE (i j : Fin m) (h : m <= n) : castLE h ⁻¹' uIcc
 (castLE h i) (castLE h j) = uIcc i j
参数：i j : Fin m；h : m <= n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_castLE_uIcc_castLE (i j : Fin m) (h : m ≤ n) :
    castLE h ⁻¹' uIcc (castLE h i) (castLE h j) = uIcc i j :=
  rfl

@[simp]
/-
**Fin.preimage_castLE_uIoc_castLE** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_castLE_uIoc_castLE (i j : Fin m) (h : m <= n) : castLE h ⁻¹' uIoc
 (castLE h i) (castLE h j) = uIoc i j
参数：i j : Fin m；h : m <= n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_castLE_uIoc_castLE (i j : Fin m) (h : m ≤ n) :
    castLE h ⁻¹' uIoc (castLE h i) (castLE h j) = uIoc i j :=
  rfl

@[simp]
/-
**Fin.preimage_castLE_uIoo_castLE** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_castLE_uIoo_castLE (i j : Fin m) (h : m <= n) : castLE h ⁻¹' uIoo
 (castLE h i) (castLE h j) = uIoo i j
参数：i j : Fin m；h : m <= n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_castLE_uIoo_castLE (i j : Fin m) (h : m ≤ n) :
    castLE h ⁻¹' uIoo (castLE h i) (castLE h j) = uIoo i j :=
  rfl

@[simp]
/-
**Fin.image_castLE_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：image_castLE_Iic (i : Fin m) (h : m <= n) : castLE h '' Iic i = Iic (castL
E h i)
参数：i : Fin m；h : m <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.image_injective`：∀ {α : Type u_1} {β : Type u_2} {f :
 α → β}, Function.Injective f → Function.Injective (Set.image f)
· 使用定理 `Fin.val_injective`：val_injective : Function.Injective (@Fin.val n)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Fin.image_val_Iic`：image_val_Iic (i : Fin n) : (↑) '' Iic i = Iic (i : N
at)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_castLE_Iic (i : Fin m) (h : m ≤ n) : castLE h '' Iic i = Iic (castLE h i) :=
  val_injective.image_injective <| by simp [image_image]

@[simp]
/-
**Fin.image_castLE_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：image_castLE_Iio (i : Fin m) (h : m <= n) : castLE h '' Iio i = Iio (castL
E h i)
参数：i : Fin m；h : m <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.image_injective`：∀ {α : Type u_1} {β : Type u_2} {f :
 α → β}, Function.Injective f → Function.Injective (Set.image f)
· 使用定理 `Fin.val_injective`：val_injective : Function.Injective (@Fin.val n)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Fin.image_val_Iio`：image_val_Iio (i : Fin n) : (↑) '' Iio i = Iio (i : N
at)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_castLE_Iio (i : Fin m) (h : m ≤ n) : castLE h '' Iio i = Iio (castLE h i) :=
  val_injective.image_injective <| by simp [image_image]

@[simp]
/-
**Fin.image_castLE_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：image_castLE_Icc (i j : Fin m) (h : m <= n) : castLE h '' Icc i j = Icc (c
astLE h i) (castLE h j)
参数：i j : Fin m；h : m <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.image_injective`：∀ {α : Type u_1} {β : Type u_2} {f :
 α → β}, Function.Injective f → Function.Injective (Set.image f)
· 使用定理 `Fin.val_injective`：val_injective : Function.Injective (@Fin.val n)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Fin.image_val_Icc`：image_val_Icc (i j : Fin n) : (↑) '' Icc i j = Icc (i
 : Nat) j
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_castLE_Icc (i j : Fin m) (h : m ≤ n) :
    castLE h '' Icc i j = Icc (castLE h i) (castLE h j) :=
  val_injective.image_injective <| by simp [image_image]

@[simp]
/-
**Fin.image_castLE_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：image_castLE_Ico (i j : Fin m) (h : m <= n) : castLE h '' Ico i j = Ico (c
astLE h i) (castLE h j)
参数：i j : Fin m；h : m <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.image_injective`：∀ {α : Type u_1} {β : Type u_2} {f :
 α → β}, Function.Injective f → Function.Injective (Set.image f)
· 使用定理 `Fin.val_injective`：val_injective : Function.Injective (@Fin.val n)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Fin.image_val_Ico`：image_val_Ico (i j : Fin n) : (↑) '' Ico i j = Ico (i
 : Nat) j
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_castLE_Ico (i j : Fin m) (h : m ≤ n) :
    castLE h '' Ico i j = Ico (castLE h i) (castLE h j) :=
  val_injective.image_injective <| by simp [image_image]

@[simp]
/-
**Fin.image_castLE_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：image_castLE_Ioc (i j : Fin m) (h : m <= n) : castLE h '' Ioc i j = Ioc (c
astLE h i) (castLE h j)
参数：i j : Fin m；h : m <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.image_injective`：∀ {α : Type u_1} {β : Type u_2} {f :
 α → β}, Function.Injective f → Function.Injective (Set.image f)
· 使用定理 `Fin.val_injective`：val_injective : Function.Injective (@Fin.val n)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Fin.image_val_Ioc`：image_val_Ioc (i j : Fin n) : (↑) '' Ioc i j = Ioc (i
 : Nat) j
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_castLE_Ioc (i j : Fin m) (h : m ≤ n) :
    castLE h '' Ioc i j = Ioc (castLE h i) (castLE h j) :=
  val_injective.image_injective <| by simp [image_image]

@[simp]
/-
**Fin.image_castLE_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：image_castLE_Ioo (i j : Fin m) (h : m <= n) : castLE h '' Ioo i j = Ioo (c
astLE h i) (castLE h j)
参数：i j : Fin m；h : m <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.image_injective`：∀ {α : Type u_1} {β : Type u_2} {f :
 α → β}, Function.Injective f → Function.Injective (Set.image f)
· 使用定理 `Fin.val_injective`：val_injective : Function.Injective (@Fin.val n)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Fin.image_val_Ioo`：image_val_Ioo (i j : Fin n) : (↑) '' Ioo i j = Ioo (i
 : Nat) j
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_castLE_Ioo (i j : Fin m) (h : m ≤ n) :
    castLE h '' Ioo i j = Ioo (castLE h i) (castLE h j) :=
  val_injective.image_injective <| by simp [image_image]

@[simp]
/-
**Fin.image_castLE_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：image_castLE_uIcc (i j : Fin m) (h : m <= n) : castLE h '' uIcc i j = uIcc
 (castLE h i) (castLE h j)
参数：i j : Fin m；h : m <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.image_injective`：∀ {α : Type u_1} {β : Type u_2} {f :
 α → β}, Function.Injective f → Function.Injective (Set.image f)
· 使用定理 `Fin.val_injective`：val_injective : Function.Injective (@Fin.val n)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Fin.image_val_uIcc`：∀ {n : ℕ} (i j : Fin n), Fin.val '' Set.uIcc i j = S
et.uIcc ↑i ↑j
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_castLE_uIcc (i j : Fin m) (h : m ≤ n) :
    castLE h '' uIcc i j = uIcc (castLE h i) (castLE h j) :=
  val_injective.image_injective <| by simp [image_image]

@[simp]
/-
**Fin.image_castLE_uIoc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：image_castLE_uIoc (i j : Fin m) (h : m <= n) : castLE h '' uIoc i j = uIoc
 (castLE h i) (castLE h j)
参数：i j : Fin m；h : m <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.image_injective`：∀ {α : Type u_1} {β : Type u_2} {f :
 α → β}, Function.Injective f → Function.Injective (Set.image f)
· 使用定理 `Fin.val_injective`：val_injective : Function.Injective (@Fin.val n)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Fin.image_val_uIoc`：∀ {n : ℕ} (i j : Fin n), Fin.val '' Set.uIoc i j = S
et.uIoc ↑i ↑j
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_castLE_uIoc (i j : Fin m) (h : m ≤ n) :
    castLE h '' uIoc i j = uIoc (castLE h i) (castLE h j) :=
  val_injective.image_injective <| by simp [image_image]

@[simp]
/-
**Fin.image_castLE_uIoo** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：image_castLE_uIoo (i j : Fin m) (h : m <= n) : castLE h '' uIoo i j = uIoo
 (castLE h i) (castLE h j)
参数：i j : Fin m；h : m <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.image_injective`：∀ {α : Type u_1} {β : Type u_2} {f :
 α → β}, Function.Injective f → Function.Injective (Set.image f)
· 使用定理 `Fin.val_injective`：val_injective : Function.Injective (@Fin.val n)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Fin.image_val_uIoo`：∀ {n : ℕ} (i j : Fin n), Fin.val '' Set.uIoo i j = S
et.uIoo ↑i ↑j
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_castLE_uIoo (i j : Fin m) (h : m ≤ n) :
    castLE h '' uIoo i j = uIoo (castLE h i) (castLE h j) :=
  val_injective.image_injective <| by simp [image_image]

/-!
### (Pre)images under `Fin.castAdd`
-/

@[simp]
/-
**Fin.range_castAdd** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：range_castAdd [NeZero m] : range (castAdd m : Fin n -> Fin (n + m)) = Iio 
(natAdd n 0)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.image_injective`：∀ {α : Type u_1} {β : Type u_2} {f :
 α → β}, Function.Injective f → Function.Injective (Set.image f)
· 使用定理 `Fin.val_injective`：val_injective : Function.Injective (@Fin.val n)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.range_val`：range_val : range ((↑) : Fin n -> Nat) = Set.Iio n
· 使用定理 `Fin.image_val_Iio`：image_val_Iio (i : Fin n) : (↑) '' Iio i = Iio (i : N
at)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
### (Pre)images under `Fin.castAdd`
-/
theorem range_castAdd [NeZero m] : range (castAdd m : Fin n → Fin (n + m)) = Iio (natAdd n 0) :=
  val_injective.image_injective <| by simp [← range_comp, comp_def]

@[simp]
/-
**Fin.preimage_castAdd_Ici_castAdd** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_castAdd_Ici_castAdd (m) (i : Fin n) : castAdd m ⁻¹' Ici (castAdd 
m i) = Ici i
参数：m；i : Fin n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_castAdd_Ici_castAdd (m) (i : Fin n) : castAdd m ⁻¹' Ici (castAdd m i) = Ici i :=
  rfl

@[simp]
/-
**Fin.preimage_castAdd_Ioi_castAdd** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_castAdd_Ioi_castAdd (m) (i : Fin n) : castAdd m ⁻¹' Ioi (castAdd 
m i) = Ioi i
参数：m；i : Fin n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_castAdd_Ioi_castAdd (m) (i : Fin n) : castAdd m ⁻¹' Ioi (castAdd m i) = Ioi i :=
  rfl

@[simp]
/-
**Fin.preimage_castAdd_Iic_castAdd** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_castAdd_Iic_castAdd (m) (i : Fin n) : castAdd m ⁻¹' Iic (castAdd 
m i) = Iic i
参数：m；i : Fin n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_castAdd_Iic_castAdd (m) (i : Fin n) : castAdd m ⁻¹' Iic (castAdd m i) = Iic i :=
  rfl

@[simp]
/-
**Fin.preimage_castAdd_Iio_castAdd** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_castAdd_Iio_castAdd (m) (i : Fin n) : castAdd m ⁻¹' Iio (castAdd 
m i) = Iio i
参数：m；i : Fin n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_castAdd_Iio_castAdd (m) (i : Fin n) : castAdd m ⁻¹' Iio (castAdd m i) = Iio i :=
  rfl

@[simp]
/-
**Fin.preimage_castAdd_Icc_castAdd** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_castAdd_Icc_castAdd (m) (i j : Fin n) : castAdd m ⁻¹' Icc (castAd
d m i) (castAdd m j) = Icc i j
参数：m；i j : Fin n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_castAdd_Icc_castAdd (m) (i j : Fin n) :
    castAdd m ⁻¹' Icc (castAdd m i) (castAdd m j) = Icc i j :=
  rfl

@[simp]
/-
**Fin.preimage_castAdd_Ico_castAdd** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_castAdd_Ico_castAdd (m) (i j : Fin n) : castAdd m ⁻¹' Ico (castAd
d m i) (castAdd m j) = Ico i j
参数：m；i j : Fin n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_castAdd_Ico_castAdd (m) (i j : Fin n) :
    castAdd m ⁻¹' Ico (castAdd m i) (castAdd m j) = Ico i j :=
  rfl

@[simp]
/-
**Fin.preimage_castAdd_Ioc_castAdd** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_castAdd_Ioc_castAdd (m) (i j : Fin n) : castAdd m ⁻¹' Ioc (castAd
d m i) (castAdd m j) = Ioc i j
参数：m；i j : Fin n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_castAdd_Ioc_castAdd (m) (i j : Fin n) :
    castAdd m ⁻¹' Ioc (castAdd m i) (castAdd m j) = Ioc i j :=
  rfl

@[simp]
/-
**Fin.preimage_castAdd_Ioo_castAdd** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_castAdd_Ioo_castAdd (m) (i j : Fin n) : castAdd m ⁻¹' Ioo (castAd
d m i) (castAdd m j) = Ioo i j
参数：m；i j : Fin n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_castAdd_Ioo_castAdd (m) (i j : Fin n) :
    castAdd m ⁻¹' Ioo (castAdd m i) (castAdd m j) = Ioo i j :=
  rfl

@[simp]
/-
**Fin.preimage_castAdd_uIcc_castAdd** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_castAdd_uIcc_castAdd (m) (i j : Fin n) : castAdd m ⁻¹' uIcc (cast
Add m i) (castAdd m j) = uIcc i j
参数：m；i j : Fin n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_castAdd_uIcc_castAdd (m) (i j : Fin n) :
    castAdd m ⁻¹' uIcc (castAdd m i) (castAdd m j) = uIcc i j :=
  rfl

@[simp]
/-
**Fin.preimage_castAdd_uIoc_castAdd** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_castAdd_uIoc_castAdd (m) (i j : Fin n) : castAdd m ⁻¹' uIoc (cast
Add m i) (castAdd m j) = uIoc i j
参数：m；i j : Fin n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_castAdd_uIoc_castAdd (m) (i j : Fin n) :
    castAdd m ⁻¹' uIoc (castAdd m i) (castAdd m j) = uIoc i j :=
  rfl

@[simp]
/-
**Fin.preimage_castAdd_uIoo_castAdd** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_castAdd_uIoo_castAdd (m) (i j : Fin n) : castAdd m ⁻¹' uIoo (cast
Add m i) (castAdd m j) = uIoo i j
参数：m；i j : Fin n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_castAdd_uIoo_castAdd (m) (i j : Fin n) :
    castAdd m ⁻¹' uIoo (castAdd m i) (castAdd m j) = uIoo i j :=
  rfl

@[simp]
/-
**Fin.image_castAdd_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：image_castAdd_Ici (m) [NeZero m] (i : Fin n) : castAdd m '' Ici i = Ico (c
astAdd m i) (natAdd n 0)
参数：m；i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.image_injective`：∀ {α : Type u_1} {β : Type u_2} {f :
 α → β}, Function.Injective f → Function.Injective (Set.image f)
· 使用定理 `Fin.val_injective`：val_injective : Function.Injective (@Fin.val n)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Fin.image_val_Ici`：image_val_Ici (i : Fin n) : (↑) '' Ici i = Ico (i : N
at) n
· 使用定理 `Fin.image_val_Ico`：image_val_Ico (i j : Fin n) : (↑) '' Ico i j = Ico (i
 : Nat) j
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_castAdd_Ici (m) [NeZero m] (i : Fin n) :
    castAdd m '' Ici i = Ico (castAdd m i) (natAdd n 0) :=
  val_injective.image_injective <| by simp [← image_comp]

@[simp]
/-
**Fin.image_castAdd_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：image_castAdd_Ioi (m) [NeZero m] (i : Fin n) : castAdd m '' Ioi i = Ioo (c
astAdd m i) (natAdd n 0)
参数：m；i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.image_injective`：∀ {α : Type u_1} {β : Type u_2} {f :
 α → β}, Function.Injective f → Function.Injective (Set.image f)
· 使用定理 `Fin.val_injective`：val_injective : Function.Injective (@Fin.val n)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Fin.image_val_Ioi`：image_val_Ioi (i : Fin n) : (↑) '' Ioi i = Ioo (i : N
at) n
· 使用定理 `Fin.image_val_Ioo`：image_val_Ioo (i j : Fin n) : (↑) '' Ioo i j = Ioo (i
 : Nat) j
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_castAdd_Ioi (m) [NeZero m] (i : Fin n) :
    castAdd m '' Ioi i = Ioo (castAdd m i) (natAdd n 0) :=
  val_injective.image_injective <| by simp [← image_comp]

@[simp]
/-
**Fin.image_castAdd_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：image_castAdd_Iic (m) (i : Fin n) : castAdd m '' Iic i = Iic (castAdd m i)
参数：m；i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.image_castLE_Iic`：image_castLE_Iic (i : Fin m) (h : m <= n) : castLE
 h '' Iic i = Iic (castLE h i)
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
-/
theorem image_castAdd_Iic (m) (i : Fin n) : castAdd m '' Iic i = Iic (castAdd m i) :=
  image_castLE_Iic i _

@[simp]
/-
**Fin.image_castAdd_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：image_castAdd_Iio (m) (i : Fin n) : castAdd m '' Iio i = Iio (castAdd m i)
参数：m；i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.image_castLE_Iio`：image_castLE_Iio (i : Fin m) (h : m <= n) : castLE
 h '' Iio i = Iio (castLE h i)
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
-/
theorem image_castAdd_Iio (m) (i : Fin n) : castAdd m '' Iio i = Iio (castAdd m i) :=
  image_castLE_Iio ..

@[simp]
/-
**Fin.image_castAdd_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：image_castAdd_Icc (m) (i j : Fin n) : castAdd m '' Icc i j = Icc (castAdd 
m i) (castAdd m j)
参数：m；i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.image_castLE_Icc`：image_castLE_Icc (i j : Fin m) (h : m <= n) : cast
LE h '' Icc i j = Icc (castLE h i) (castLE h j)
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
-/
theorem image_castAdd_Icc (m) (i j : Fin n) :
    castAdd m '' Icc i j = Icc (castAdd m i) (castAdd m j) :=
  image_castLE_Icc ..

@[simp]
/-
**Fin.image_castAdd_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：image_castAdd_Ico (m) (i j : Fin n) : castAdd m '' Ico i j = Ico (castAdd 
m i) (castAdd m j)
参数：m；i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.image_castLE_Ico`：image_castLE_Ico (i j : Fin m) (h : m <= n) : cast
LE h '' Ico i j = Ico (castLE h i) (castLE h j)
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
-/
theorem image_castAdd_Ico (m) (i j : Fin n) :
    castAdd m '' Ico i j = Ico (castAdd m i) (castAdd m j) :=
  image_castLE_Ico ..

@[simp]
/-
**Fin.image_castAdd_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：image_castAdd_Ioc (m) (i j : Fin n) : castAdd m '' Ioc i j = Ioc (castAdd 
m i) (castAdd m j)
参数：m；i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.image_castLE_Ioc`：image_castLE_Ioc (i j : Fin m) (h : m <= n) : cast
LE h '' Ioc i j = Ioc (castLE h i) (castLE h j)
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
-/
theorem image_castAdd_Ioc (m) (i j : Fin n) :
    castAdd m '' Ioc i j = Ioc (castAdd m i) (castAdd m j) :=
  image_castLE_Ioc ..

@[simp]
/-
**Fin.image_castAdd_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：image_castAdd_Ioo (m) (i j : Fin n) : castAdd m '' Ioo i j = Ioo (castAdd 
m i) (castAdd m j)
参数：m；i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.image_castLE_Ioo`：image_castLE_Ioo (i j : Fin m) (h : m <= n) : cast
LE h '' Ioo i j = Ioo (castLE h i) (castLE h j)
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
-/
theorem image_castAdd_Ioo (m) (i j : Fin n) :
    castAdd m '' Ioo i j = Ioo (castAdd m i) (castAdd m j) :=
  image_castLE_Ioo ..

@[simp]
/-
**Fin.image_castAdd_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：image_castAdd_uIcc (m) (i j : Fin n) : castAdd m '' uIcc i j = uIcc (castA
dd m i) (castAdd m j)
参数：m；i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.image_castLE_uIcc`：image_castLE_uIcc (i j : Fin m) (h : m <= n) : ca
stLE h '' uIcc i j = uIcc (castLE h i) (castLE h j)
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
-/
theorem image_castAdd_uIcc (m) (i j : Fin n) :
    castAdd m '' uIcc i j = uIcc (castAdd m i) (castAdd m j) :=
  image_castLE_uIcc ..

@[simp]
/-
**Fin.image_castAdd_uIoc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：image_castAdd_uIoc (m) (i j : Fin n) : castAdd m '' uIoc i j = uIoc (castA
dd m i) (castAdd m j)
参数：m；i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.image_castLE_uIoc`：image_castLE_uIoc (i j : Fin m) (h : m <= n) : ca
stLE h '' uIoc i j = uIoc (castLE h i) (castLE h j)
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
-/
theorem image_castAdd_uIoc (m) (i j : Fin n) :
    castAdd m '' uIoc i j = uIoc (castAdd m i) (castAdd m j) :=
  image_castLE_uIoc ..

@[simp]
/-
**Fin.image_castAdd_uIoo** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：image_castAdd_uIoo (m) (i j : Fin n) : castAdd m '' uIoo i j = uIoo (castA
dd m i) (castAdd m j)
参数：m；i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.image_castLE_uIoo`：image_castLE_uIoo (i j : Fin m) (h : m <= n) : ca
stLE h '' uIoo i j = uIoo (castLE h i) (castLE h j)
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
-/
theorem image_castAdd_uIoo (m) (i j : Fin n) :
    castAdd m '' uIoo i j = uIoo (castAdd m i) (castAdd m j) :=
  image_castLE_uIoo ..

/-!
### (Pre)images under `Fin.cast`
-/

/-
**Fin.image_cast** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：image_cast (h : m = n) (s : Set (Fin m)) : Fin.cast h '' s = Fin.cast h.sy
mm ⁻¹' s
参数：h : m = n；s : Set (Fin m)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Equiv.image_eq_preimage_symm`：image_eq_preimage_symm (e : α ≃ β) (s : Se
t α) : e '' s = e.symm ⁻¹' s

--- 原说明 ---
### (Pre)images under `Fin.cast`
-/
theorem image_cast (h : m = n) (s : Set (Fin m)) : Fin.cast h '' s = Fin.cast h.symm ⁻¹' s :=
  (finCongr h).image_eq_preimage_symm _

@[simp]
/-
**Fin.image_cast_fun** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：image_cast_fun (h : m = n) : image (Fin.cast h) = preimage (Fin.cast h.sym
m)
参数：h : m = n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.image_cast`：image_cast (h : m = n) (s : Set (Fin m)) : Fin.cast h ''
 s = Fin.cast h.symm ⁻¹' s
-/
theorem image_cast_fun (h : m = n) : image (Fin.cast h) = preimage (Fin.cast h.symm) :=
  funext <| image_cast h

@[simp]
/-
**Fin.preimage_cast_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_cast_Ici (h : m = n) (i : Fin n) : .cast h ⁻¹' Ici i = Ici (i.cas
t h.symm)
参数：h : m = n；i : Fin n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_cast_Ici (h : m = n) (i : Fin n) : .cast h ⁻¹' Ici i = Ici (i.cast h.symm) := rfl

@[simp]
/-
**Fin.preimage_cast_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_cast_Ioi (h : m = n) (i : Fin n) : .cast h ⁻¹' Ioi i = Ioi (i.cas
t h.symm)
参数：h : m = n；i : Fin n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_cast_Ioi (h : m = n) (i : Fin n) : .cast h ⁻¹' Ioi i = Ioi (i.cast h.symm) := rfl

@[simp]
/-
**Fin.preimage_cast_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_cast_Iic (h : m = n) (i : Fin n) : .cast h ⁻¹' Iic i = Iic (i.cas
t h.symm)
参数：h : m = n；i : Fin n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_cast_Iic (h : m = n) (i : Fin n) : .cast h ⁻¹' Iic i = Iic (i.cast h.symm) := rfl

@[simp]
/-
**Fin.preimage_cast_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_cast_Iio (h : m = n) (i : Fin n) : .cast h ⁻¹' Iio i = Iio (i.cas
t h.symm)
参数：h : m = n；i : Fin n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_cast_Iio (h : m = n) (i : Fin n) : .cast h ⁻¹' Iio i = Iio (i.cast h.symm) := rfl

@[simp]
/-
**Fin.preimage_cast_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_cast_Icc (h : m = n) (i j : Fin n) : .cast h ⁻¹' Icc i j = Icc (i
.cast h.symm) (j.cast h.symm)
参数：h : m = n；i j : Fin n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_cast_Icc (h : m = n) (i j : Fin n) :
    .cast h ⁻¹' Icc i j = Icc (i.cast h.symm) (j.cast h.symm) :=
  rfl

@[simp]
/-
**Fin.preimage_cast_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_cast_Ico (h : m = n) (i j : Fin n) : .cast h ⁻¹' Ico i j = Ico (i
.cast h.symm) (j.cast h.symm)
参数：h : m = n；i j : Fin n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_cast_Ico (h : m = n) (i j : Fin n) :
    .cast h ⁻¹' Ico i j = Ico (i.cast h.symm) (j.cast h.symm) :=
  rfl

@[simp]
/-
**Fin.preimage_cast_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_cast_Ioc (h : m = n) (i j : Fin n) : .cast h ⁻¹' Ioc i j = Ioc (i
.cast h.symm) (j.cast h.symm)
参数：h : m = n；i j : Fin n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_cast_Ioc (h : m = n) (i j : Fin n) :
    .cast h ⁻¹' Ioc i j = Ioc (i.cast h.symm) (j.cast h.symm) :=
  rfl

@[simp]
/-
**Fin.preimage_cast_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_cast_Ioo (h : m = n) (i j : Fin n) : .cast h ⁻¹' Ioo i j = Ioo (i
.cast h.symm) (j.cast h.symm)
参数：h : m = n；i j : Fin n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_cast_Ioo (h : m = n) (i j : Fin n) :
    .cast h ⁻¹' Ioo i j = Ioo (i.cast h.symm) (j.cast h.symm) :=
  rfl

@[simp]
/-
**Fin.preimage_cast_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_cast_uIcc (h : m = n) (i j : Fin n) : .cast h ⁻¹' uIcc i j = uIcc
 (i.cast h.symm) (j.cast h.symm)
参数：h : m = n；i j : Fin n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_cast_uIcc (h : m = n) (i j : Fin n) :
    .cast h ⁻¹' uIcc i j = uIcc (i.cast h.symm) (j.cast h.symm) :=
  rfl

@[simp]
/-
**Fin.preimage_cast_uIoc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_cast_uIoc (h : m = n) (i j : Fin n) : .cast h ⁻¹' uIoc i j = uIoc
 (i.cast h.symm) (j.cast h.symm)
参数：h : m = n；i j : Fin n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_cast_uIoc (h : m = n) (i j : Fin n) :
    .cast h ⁻¹' uIoc i j = uIoc (i.cast h.symm) (j.cast h.symm) :=
  rfl

@[simp]
/-
**Fin.preimage_cast_uIoo** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_cast_uIoo (h : m = n) (i j : Fin n) : .cast h ⁻¹' uIoo i j = uIoo
 (i.cast h.symm) (j.cast h.symm)
参数：h : m = n；i j : Fin n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_cast_uIoo (h : m = n) (i j : Fin n) :
    .cast h ⁻¹' uIoo i j = uIoo (i.cast h.symm) (j.cast h.symm) :=
  rfl

/-!
### `Fin.castSucc`
-/

@[simp]
/-
**Fin.preimage_castSucc_Ici_castSucc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_castSucc_Ici_castSucc (i : Fin n) : castSucc ⁻¹' Ici i.castSucc =
 Ici i
参数：i : Fin n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### `Fin.castSucc`
-/
theorem preimage_castSucc_Ici_castSucc (i : Fin n) : castSucc ⁻¹' Ici i.castSucc = Ici i := rfl

@[simp]
/-
**Fin.preimage_castSucc_Ioi_castSucc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_castSucc_Ioi_castSucc (i : Fin n) : castSucc ⁻¹' Ioi i.castSucc =
 Ioi i
参数：i : Fin n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_castSucc_Ioi_castSucc (i : Fin n) : castSucc ⁻¹' Ioi i.castSucc = Ioi i := rfl

@[simp]
/-
**Fin.preimage_castSucc_Iic_castSucc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_castSucc_Iic_castSucc (i : Fin n) : castSucc ⁻¹' Iic i.castSucc =
 Iic i
参数：i : Fin n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_castSucc_Iic_castSucc (i : Fin n) : castSucc ⁻¹' Iic i.castSucc = Iic i := rfl

@[simp]
/-
**Fin.preimage_castSucc_Iio_castSucc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_castSucc_Iio_castSucc (i : Fin n) : castSucc ⁻¹' Iio i.castSucc =
 Iio i
参数：i : Fin n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_castSucc_Iio_castSucc (i : Fin n) : castSucc ⁻¹' Iio i.castSucc = Iio i := rfl

@[simp]
/-
**Fin.preimage_castSucc_Icc_castSucc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_castSucc_Icc_castSucc (i j : Fin n) : castSucc ⁻¹' Icc i.castSucc
 j.castSucc = Icc i j
参数：i j : Fin n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_castSucc_Icc_castSucc (i j : Fin n) :
    castSucc ⁻¹' Icc i.castSucc j.castSucc = Icc i j :=
  rfl

@[simp]
/-
**Fin.preimage_castSucc_Ico_castSucc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_castSucc_Ico_castSucc (i j : Fin n) : castSucc ⁻¹' Ico i.castSucc
 j.castSucc = Ico i j
参数：i j : Fin n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_castSucc_Ico_castSucc (i j : Fin n) :
    castSucc ⁻¹' Ico i.castSucc j.castSucc = Ico i j :=
  rfl

@[simp]
/-
**Fin.preimage_castSucc_Ioc_castSucc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_castSucc_Ioc_castSucc (i j : Fin n) : castSucc ⁻¹' Ioc i.castSucc
 j.castSucc = Ioc i j
参数：i j : Fin n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_castSucc_Ioc_castSucc (i j : Fin n) :
    castSucc ⁻¹' Ioc i.castSucc j.castSucc = Ioc i j :=
  rfl

@[simp]
/-
**Fin.preimage_castSucc_Ioo_castSucc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_castSucc_Ioo_castSucc (i j : Fin n) : castSucc ⁻¹' Ioo i.castSucc
 j.castSucc = Ioo i j
参数：i j : Fin n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_castSucc_Ioo_castSucc (i j : Fin n) :
    castSucc ⁻¹' Ioo i.castSucc j.castSucc = Ioo i j :=
  rfl

@[simp]
/-
**Fin.preimage_castSucc_uIcc_castSucc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_castSucc_uIcc_castSucc (i j : Fin n) : castSucc ⁻¹' uIcc i.castSu
cc j.castSucc = uIcc i j
参数：i j : Fin n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_castSucc_uIcc_castSucc (i j : Fin n) :
    castSucc ⁻¹' uIcc i.castSucc j.castSucc = uIcc i j :=
  rfl

@[simp]
/-
**Fin.preimage_castSucc_uIoc_castSucc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_castSucc_uIoc_castSucc (i j : Fin n) : castSucc ⁻¹' uIoc i.castSu
cc j.castSucc = uIoc i j
参数：i j : Fin n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_castSucc_uIoc_castSucc (i j : Fin n) :
    castSucc ⁻¹' uIoc i.castSucc j.castSucc = uIoc i j :=
  rfl

@[simp]
/-
**Fin.preimage_castSucc_uIoo_castSucc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_castSucc_uIoo_castSucc (i j : Fin n) : castSucc ⁻¹' uIoo i.castSu
cc j.castSucc = uIoo i j
参数：i j : Fin n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_castSucc_uIoo_castSucc (i j : Fin n) :
    castSucc ⁻¹' uIoo i.castSucc j.castSucc = uIoo i j :=
  rfl

@[simp]
/-
**Fin.image_castSucc_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：image_castSucc_Ici (i : Fin n) : castSucc '' Ici i = Ico i.castSucc (.last
 n)
参数：i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.image_castAdd_Ici`：image_castAdd_Ici (m) [NeZero m] (i : Fin n) : ca
stAdd m '' Ici i = Ico (castAdd m i) (natAdd n 0)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem image_castSucc_Ici (i : Fin n) : castSucc '' Ici i = Ico i.castSucc (.last n) :=
  image_castAdd_Ici ..

@[simp]
/-
**Fin.image_castSucc_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：image_castSucc_Ioi (i : Fin n) : castSucc '' Ioi i = Ioo i.castSucc (.last
 n)
参数：i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.image_castAdd_Ioi`：image_castAdd_Ioi (m) [NeZero m] (i : Fin n) : ca
stAdd m '' Ioi i = Ioo (castAdd m i) (natAdd n 0)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem image_castSucc_Ioi (i : Fin n) : castSucc '' Ioi i = Ioo i.castSucc (.last n) :=
  image_castAdd_Ioi ..

@[simp]
/-
**Fin.image_castSucc_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：image_castSucc_Iic (i : Fin n) : castSucc '' Iic i = Iic i.castSucc
参数：i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.image_castAdd_Iic`：image_castAdd_Iic (m) (i : Fin n) : castAdd m '' 
Iic i = Iic (castAdd m i)
-/
theorem image_castSucc_Iic (i : Fin n) : castSucc '' Iic i = Iic i.castSucc :=
  image_castAdd_Iic ..

@[simp]
/-
**Fin.image_castSucc_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：image_castSucc_Iio (i : Fin n) : castSucc '' Iio i = Iio i.castSucc
参数：i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.image_castAdd_Iio`：image_castAdd_Iio (m) (i : Fin n) : castAdd m '' 
Iio i = Iio (castAdd m i)
-/
theorem image_castSucc_Iio (i : Fin n) : castSucc '' Iio i = Iio i.castSucc :=
  image_castAdd_Iio ..

@[simp]
/-
**Fin.image_castSucc_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：image_castSucc_Icc (i j : Fin n) : castSucc '' Icc i j = Icc i.castSucc j.
castSucc
参数：i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.image_castAdd_Icc`：image_castAdd_Icc (m) (i j : Fin n) : castAdd m '
' Icc i j = Icc (castAdd m i) (castAdd m j)
-/
theorem image_castSucc_Icc (i j : Fin n) : castSucc '' Icc i j = Icc i.castSucc j.castSucc :=
  image_castAdd_Icc ..

@[simp]
/-
**Fin.image_castSucc_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：image_castSucc_Ico (i j : Fin n) : castSucc '' Ico i j = Ico i.castSucc j.
castSucc
参数：i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.image_castAdd_Ico`：image_castAdd_Ico (m) (i j : Fin n) : castAdd m '
' Ico i j = Ico (castAdd m i) (castAdd m j)
-/
theorem image_castSucc_Ico (i j : Fin n) : castSucc '' Ico i j = Ico i.castSucc j.castSucc :=
  image_castAdd_Ico ..

@[simp]
/-
**Fin.image_castSucc_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：image_castSucc_Ioc (i j : Fin n) : castSucc '' Ioc i j = Ioc i.castSucc j.
castSucc
参数：i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.image_castAdd_Ioc`：image_castAdd_Ioc (m) (i j : Fin n) : castAdd m '
' Ioc i j = Ioc (castAdd m i) (castAdd m j)
-/
theorem image_castSucc_Ioc (i j : Fin n) : castSucc '' Ioc i j = Ioc i.castSucc j.castSucc :=
  image_castAdd_Ioc ..

@[simp]
/-
**Fin.image_castSucc_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：image_castSucc_Ioo (i j : Fin n) : castSucc '' Ioo i j = Ioo i.castSucc j.
castSucc
参数：i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.image_castAdd_Ioo`：image_castAdd_Ioo (m) (i j : Fin n) : castAdd m '
' Ioo i j = Ioo (castAdd m i) (castAdd m j)
-/
theorem image_castSucc_Ioo (i j : Fin n) : castSucc '' Ioo i j = Ioo i.castSucc j.castSucc :=
  image_castAdd_Ioo ..

@[simp]
/-
**Fin.image_castSucc_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：image_castSucc_uIcc (i j : Fin n) : castSucc '' uIcc i j = uIcc i.castSucc
 j.castSucc
参数：i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.image_castAdd_uIcc`：image_castAdd_uIcc (m) (i j : Fin n) : castAdd m
 '' uIcc i j = uIcc (castAdd m i) (castAdd m j)
-/
theorem image_castSucc_uIcc (i j : Fin n) : castSucc '' uIcc i j = uIcc i.castSucc j.castSucc :=
  image_castAdd_uIcc ..

@[simp]
/-
**Fin.image_castSucc_uIoc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：image_castSucc_uIoc (i j : Fin n) : castSucc '' uIoc i j = uIoc i.castSucc
 j.castSucc
参数：i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.image_castAdd_uIoc`：image_castAdd_uIoc (m) (i j : Fin n) : castAdd m
 '' uIoc i j = uIoc (castAdd m i) (castAdd m j)
-/
theorem image_castSucc_uIoc (i j : Fin n) : castSucc '' uIoc i j = uIoc i.castSucc j.castSucc :=
  image_castAdd_uIoc ..

@[simp]
/-
**Fin.image_castSucc_uIoo** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：image_castSucc_uIoo (i j : Fin n) : castSucc '' uIoo i j = uIoo i.castSucc
 j.castSucc
参数：i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.image_castAdd_uIoo`：image_castAdd_uIoo (m) (i j : Fin n) : castAdd m
 '' uIoo i j = uIoo (castAdd m i) (castAdd m j)
-/
theorem image_castSucc_uIoo (i j : Fin n) : castSucc '' uIoo i j = uIoo i.castSucc j.castSucc :=
  image_castAdd_uIoo ..

/-!
### `Fin.natAdd`
-/

/-
**Fin.range_natAdd** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：range_natAdd (m n : Nat) : range (natAdd m : Fin n -> Fin (m + n)) = {i | 
m <= i.1}
参数：m n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Fin.le_coe_natAdd`：∀ {n : ℕ} (m : ℕ) (i : Fin n), m ≤ ↑(Fin.natAdd m i)
· 使用定理 `Fin.ext`：∀ {n : ℕ} {a b : Fin n}, ↑a = ↑b → a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.mk.congr_simp`：∀ {n : ℕ} (val val_1 : ℕ) (e_val : val = val_1) (isLt
 : val < n), ⟨val, isLt⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Nat.add_sub_cancel'`：∀ {n m : ℕ}, m ≤ n → m + (n - m) = n
· 使用定理 `Nat.add_lt_add_left`：∀ {n m : ℕ}, n < m → ∀ (k : ℕ), k + n < k + m
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
### `Fin.natAdd`
-/
theorem range_natAdd (m n : ℕ) : range (natAdd m : Fin n → Fin (m + n)) = {i | m ≤ i.1} := by
  ext i
  constructor
  · rintro ⟨i, rfl⟩
    apply le_coe_natAdd
  · refine fun (hi : m ≤ i) ↦ ⟨⟨i - m, by lia⟩, ?_⟩
    ext
    simp [hi]
/-
**Fin.range_natAdd_eq_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：range_natAdd_eq_Ici (m n : Nat) [NeZero n] : range (natAdd m : Fin n -> Fi
n (m + n)) = Ici (natAdd m 0)
参数：m n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.range_natAdd`：range_natAdd (m n : Nat) : range (natAdd m : Fin n -> 
Fin (m + n)) = {i | m <= i.1}
-/
theorem range_natAdd_eq_Ici (m n : ℕ) [NeZero n] :
    range (natAdd m : Fin n → Fin (m + n)) = Ici (natAdd m 0) :=
  range_natAdd m n
/-
**Fin.range_natAdd_eq_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：range_natAdd_eq_Ioi (m n : Nat) [NeZero m] : range (natAdd m : Fin n -> Fi
n (m + n)) = Ioi (castAdd n ⊤)
参数：m n : Nat。
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
· 使用定理 `Fin.range_natAdd`：range_natAdd (m n : Nat) : range (natAdd m : Fin n -> 
Fin (m + n)) = {i | m <= i.1}
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.one_le_iff_ne_zero`：∀ {n : ℕ}, 1 ≤ n ↔ n ≠ 0
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem range_natAdd_eq_Ioi (m n : ℕ) [NeZero m] :
    range (natAdd m : Fin n → Fin (m + n)) = Ioi (castAdd n ⊤) := by
  ext ⟨_, _⟩
  simp [range_natAdd, lt_def, ← Nat.succ_le_iff, Nat.one_le_iff_ne_zero.mpr (NeZero.ne m)]

@[simp]
/-
**Fin.preimage_natAdd_Ici_natAdd** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_natAdd_Ici_natAdd (m) (i : Fin n) : natAdd m ⁻¹' Ici (natAdd m i)
 = Ici i
参数：m；i : Fin n。
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
theorem preimage_natAdd_Ici_natAdd (m) (i : Fin n) : natAdd m ⁻¹' Ici (natAdd m i) = Ici i := by
  ext; simp

@[simp]
/-
**Fin.preimage_natAdd_Ioi_natAdd** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_natAdd_Ioi_natAdd (m) (i : Fin n) : natAdd m ⁻¹' Ioi (natAdd m i)
 = Ioi i
参数：m；i : Fin n。
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
theorem preimage_natAdd_Ioi_natAdd (m) (i : Fin n) : natAdd m ⁻¹' Ioi (natAdd m i) = Ioi i := by
  ext; simp

@[simp]
/-
**Fin.preimage_natAdd_Iic_natAdd** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_natAdd_Iic_natAdd (m) (i : Fin n) : natAdd m ⁻¹' Iic (natAdd m i)
 = Iic i
参数：m；i : Fin n。
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
theorem preimage_natAdd_Iic_natAdd (m) (i : Fin n) : natAdd m ⁻¹' Iic (natAdd m i) = Iic i := by
  ext; simp

@[simp]
/-
**Fin.preimage_natAdd_Iio_natAdd** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_natAdd_Iio_natAdd (m) (i : Fin n) : natAdd m ⁻¹' Iio (natAdd m i)
 = Iio i
参数：m；i : Fin n。
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
theorem preimage_natAdd_Iio_natAdd (m) (i : Fin n) : natAdd m ⁻¹' Iio (natAdd m i) = Iio i := by
  ext; simp

@[simp]
/-
**Fin.preimage_natAdd_Icc_natAdd** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_natAdd_Icc_natAdd (m) (i j : Fin n) : natAdd m ⁻¹' Icc (natAdd m 
i) (natAdd m j) = Icc i j
参数：m；i j : Fin n。
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
theorem preimage_natAdd_Icc_natAdd (m) (i j : Fin n) :
    natAdd m ⁻¹' Icc (natAdd m i) (natAdd m j) = Icc i j := by
  ext; simp

@[simp]
/-
**Fin.preimage_natAdd_Ico_natAdd** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_natAdd_Ico_natAdd (m) (i j : Fin n) : natAdd m ⁻¹' Ico (natAdd m 
i) (natAdd m j) = Ico i j
参数：m；i j : Fin n。
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
theorem preimage_natAdd_Ico_natAdd (m) (i j : Fin n) :
    natAdd m ⁻¹' Ico (natAdd m i) (natAdd m j) = Ico i j := by
  ext; simp

@[simp]
/-
**Fin.preimage_natAdd_Ioc_natAdd** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_natAdd_Ioc_natAdd (m) (i j : Fin n) : natAdd m ⁻¹' Ioc (natAdd m 
i) (natAdd m j) = Ioc i j
参数：m；i j : Fin n。
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
theorem preimage_natAdd_Ioc_natAdd (m) (i j : Fin n) :
    natAdd m ⁻¹' Ioc (natAdd m i) (natAdd m j) = Ioc i j := by
  ext; simp

@[simp]
/-
**Fin.preimage_natAdd_Ioo_natAdd** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_natAdd_Ioo_natAdd (m) (i j : Fin n) : natAdd m ⁻¹' Ioo (natAdd m 
i) (natAdd m j) = Ioo i j
参数：m；i j : Fin n。
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
theorem preimage_natAdd_Ioo_natAdd (m) (i j : Fin n) :
    natAdd m ⁻¹' Ioo (natAdd m i) (natAdd m j) = Ioo i j := by
  ext; simp

@[simp]
/-
**Fin.preimage_natAdd_uIcc_natAdd** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_natAdd_uIcc_natAdd (m) (i j : Fin n) : natAdd m ⁻¹' uIcc (natAdd 
m i) (natAdd m j) = uIcc i j
参数：m；i j : Fin n。
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Monotone.map_min`：∀ {α : Type u} {β : Type v} [inst : LinearOrder α] [in
st_1 : LinearOrder β] {f : α → β} {a b : α},   Monotone f → f (min a b) = min (f
 a) (f…
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用引理 `Fin.strictMono_natAdd`：strictMono_natAdd (n) : StrictMono (natAdd n : Fi
n m -> Fin (n + m))
· 使用定理 `Monotone.map_max`：Monotone.map_max (hf : Monotone f) : f (max a b) = max
 (f a) (f b)
· 使用定理 `Fin.preimage_natAdd_Icc_natAdd`：preimage_natAdd_Icc_natAdd (m) (i j : Fi
n n) : natAdd m ⁻¹' Icc (natAdd m i) (natAdd m j) = Icc i j
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preimage_natAdd_uIcc_natAdd (m) (i j : Fin n) :
    natAdd m ⁻¹' uIcc (natAdd m i) (natAdd m j) = uIcc i j := by
  simp [uIcc, ← (strictMono_natAdd m).monotone.map_max, ← (strictMono_natAdd m).monotone.map_min]

@[simp]
/-
**Fin.preimage_natAdd_uIoc_natAdd** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_natAdd_uIoc_natAdd (m) (i j : Fin n) : natAdd m ⁻¹' uIoc (natAdd 
m i) (natAdd m j) = uIoc i j
参数：m；i j : Fin n。
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Monotone.map_min`：∀ {α : Type u} {β : Type v} [inst : LinearOrder α] [in
st_1 : LinearOrder β] {f : α → β} {a b : α},   Monotone f → f (min a b) = min (f
 a) (f…
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用引理 `Fin.strictMono_natAdd`：strictMono_natAdd (n) : StrictMono (natAdd n : Fi
n m -> Fin (n + m))
· 使用定理 `Monotone.map_max`：Monotone.map_max (hf : Monotone f) : f (max a b) = max
 (f a) (f b)
· 使用定理 `Fin.preimage_natAdd_Ioc_natAdd`：preimage_natAdd_Ioc_natAdd (m) (i j : Fi
n n) : natAdd m ⁻¹' Ioc (natAdd m i) (natAdd m j) = Ioc i j
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preimage_natAdd_uIoc_natAdd (m) (i j : Fin n) :
    natAdd m ⁻¹' uIoc (natAdd m i) (natAdd m j) = uIoc i j := by
  simp [uIoc, ← (strictMono_natAdd m).monotone.map_max, ← (strictMono_natAdd m).monotone.map_min]

@[simp]
/-
**Fin.preimage_natAdd_uIoo_natAdd** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_natAdd_uIoo_natAdd (m) (i j : Fin n) : natAdd m ⁻¹' uIoo (natAdd 
m i) (natAdd m j) = uIoo i j
参数：m；i j : Fin n。
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Monotone.map_min`：∀ {α : Type u} {β : Type v} [inst : LinearOrder α] [in
st_1 : LinearOrder β] {f : α → β} {a b : α},   Monotone f → f (min a b) = min (f
 a) (f…
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用引理 `Fin.strictMono_natAdd`：strictMono_natAdd (n) : StrictMono (natAdd n : Fi
n m -> Fin (n + m))
· 使用定理 `Monotone.map_max`：Monotone.map_max (hf : Monotone f) : f (max a b) = max
 (f a) (f b)
· 使用定理 `Fin.preimage_natAdd_Ioo_natAdd`：preimage_natAdd_Ioo_natAdd (m) (i j : Fi
n n) : natAdd m ⁻¹' Ioo (natAdd m i) (natAdd m j) = Ioo i j
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preimage_natAdd_uIoo_natAdd (m) (i j : Fin n) :
    natAdd m ⁻¹' uIoo (natAdd m i) (natAdd m j) = uIoo i j := by
  simp [uIoo, ← (strictMono_natAdd m).monotone.map_max, ← (strictMono_natAdd m).monotone.map_min]

@[simp]
/-
**Fin.image_natAdd_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：image_natAdd_Ici (m) (i : Fin n) : natAdd m '' Ici i = Ici (natAdd m i)
参数：m；i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.preimage_natAdd_Ici_natAdd`：preimage_natAdd_Ici_natAdd (m) (i : Fin 
n) : natAdd m ⁻¹' Ici (natAdd m i) = Ici i
· 使用定理 `Set.image_preimage_eq_of_subset`：image_preimage_eq_of_subset {f : α -> β
} {s : Set β} (hs : s subseteq range f) : f '' f ⁻¹' s = s
· 使用定理 `Fin.range_natAdd`：range_natAdd (m n : Nat) : range (natAdd m : Fin n -> 
Fin (m + n)) = {i | m <= i.1}
· 使用定理 `Nat.le_trans`：∀ {n m k : ℕ}, n ≤ m → m ≤ k → n ≤ k
· 使用定理 `Fin.le_coe_natAdd`：∀ {n : ℕ} (m : ℕ) (i : Fin n), m ≤ ↑(Fin.natAdd m i)
-/
theorem image_natAdd_Ici (m) (i : Fin n) : natAdd m '' Ici i = Ici (natAdd m i) := by
  rw [← preimage_natAdd_Ici_natAdd, image_preimage_eq_of_subset]
  rw [range_natAdd]
  exact fun j hj ↦ Nat.le_trans (le_coe_natAdd ..) hj

@[simp]
/-
**Fin.image_natAdd_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：image_natAdd_Ioi (m) (i : Fin n) : natAdd m '' Ioi i = Ioi (natAdd m i)
参数：m；i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.preimage_natAdd_Ioi_natAdd`：preimage_natAdd_Ioi_natAdd (m) (i : Fin 
n) : natAdd m ⁻¹' Ioi (natAdd m i) = Ioi i
· 使用定理 `Set.image_preimage_eq_of_subset`：image_preimage_eq_of_subset {f : α -> β
} {s : Set β} (hs : s subseteq range f) : f '' f ⁻¹' s = s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.Ioi_subset_Ici_self`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, S
et.Ioi a ⊆ Set.Ici a
· 使用定理 `Set.image_subset_range`：image_subset_range (f : α -> β) (s) : f '' s sub
seteq range f
· 使用定理 `Fin.image_natAdd_Ici`：image_natAdd_Ici (m) (i : Fin n) : natAdd m '' Ici
 i = Ici (natAdd m i)
-/
theorem image_natAdd_Ioi (m) (i : Fin n) : natAdd m '' Ioi i = Ioi (natAdd m i) := by
  rw [← preimage_natAdd_Ioi_natAdd, image_preimage_eq_of_subset]
  exact Ioi_subset_Ici_self.trans <| image_natAdd_Ici m i ▸ image_subset_range _ _

@[simp]
/-
**Fin.image_natAdd_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：image_natAdd_Icc (m) (i j : Fin n) : natAdd m '' Icc i j = Icc (natAdd m i
) (natAdd m j)
参数：m；i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.preimage_natAdd_Icc_natAdd`：preimage_natAdd_Icc_natAdd (m) (i j : Fi
n n) : natAdd m ⁻¹' Icc (natAdd m i) (natAdd m j) = Icc i j
· 使用定理 `Set.image_preimage_eq_of_subset`：image_preimage_eq_of_subset {f : α -> β
} {s : Set β} (hs : s subseteq range f) : f '' f ⁻¹' s = s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.Icc_subset_Ici_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Icc b a ⊆ Set.Ici b
· 使用定理 `Set.image_subset_range`：image_subset_range (f : α -> β) (s) : f '' s sub
seteq range f
· 使用定理 `Fin.image_natAdd_Ici`：image_natAdd_Ici (m) (i : Fin n) : natAdd m '' Ici
 i = Ici (natAdd m i)
-/
theorem image_natAdd_Icc (m) (i j : Fin n) :
    natAdd m '' Icc i j = Icc (natAdd m i) (natAdd m j) := by
  rw [← preimage_natAdd_Icc_natAdd, image_preimage_eq_of_subset]
  exact Icc_subset_Ici_self.trans <| image_natAdd_Ici m i ▸ image_subset_range _ _

@[simp]
/-
**Fin.image_natAdd_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：image_natAdd_Ico (m) (i j : Fin n) : natAdd m '' Ico i j = Ico (natAdd m i
) (natAdd m j)
参数：m；i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.preimage_natAdd_Ico_natAdd`：preimage_natAdd_Ico_natAdd (m) (i j : Fi
n n) : natAdd m ⁻¹' Ico (natAdd m i) (natAdd m j) = Ico i j
· 使用定理 `Set.image_preimage_eq_of_subset`：image_preimage_eq_of_subset {f : α -> β
} {s : Set β} (hs : s subseteq range f) : f '' f ⁻¹' s = s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.Ico_subset_Ici_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ico b a ⊆ Set.Ici b
· 使用定理 `Set.image_subset_range`：image_subset_range (f : α -> β) (s) : f '' s sub
seteq range f
· 使用定理 `Fin.image_natAdd_Ici`：image_natAdd_Ici (m) (i : Fin n) : natAdd m '' Ici
 i = Ici (natAdd m i)
-/
theorem image_natAdd_Ico (m) (i j : Fin n) :
    natAdd m '' Ico i j = Ico (natAdd m i) (natAdd m j) := by
  rw [← preimage_natAdd_Ico_natAdd, image_preimage_eq_of_subset]
  exact Ico_subset_Ici_self.trans <| image_natAdd_Ici m i ▸ image_subset_range _ _

@[simp]
/-
**Fin.image_natAdd_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：image_natAdd_Ioc (m) (i j : Fin n) : natAdd m '' Ioc i j = Ioc (natAdd m i
) (natAdd m j)
参数：m；i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.preimage_natAdd_Ioc_natAdd`：preimage_natAdd_Ioc_natAdd (m) (i j : Fi
n n) : natAdd m ⁻¹' Ioc (natAdd m i) (natAdd m j) = Ioc i j
· 使用定理 `Set.image_preimage_eq_of_subset`：image_preimage_eq_of_subset {f : α -> β
} {s : Set β} (hs : s subseteq range f) : f '' f ⁻¹' s = s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.Ioc_subset_Ioi_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc b a ⊆ Set.Ioi b
· 使用定理 `Set.image_subset_range`：image_subset_range (f : α -> β) (s) : f '' s sub
seteq range f
· 使用定理 `Fin.image_natAdd_Ioi`：image_natAdd_Ioi (m) (i : Fin n) : natAdd m '' Ioi
 i = Ioi (natAdd m i)
-/
theorem image_natAdd_Ioc (m) (i j : Fin n) :
    natAdd m '' Ioc i j = Ioc (natAdd m i) (natAdd m j) := by
  rw [← preimage_natAdd_Ioc_natAdd, image_preimage_eq_of_subset]
  exact Ioc_subset_Ioi_self.trans <| image_natAdd_Ioi m i ▸ image_subset_range _ _

@[simp]
/-
**Fin.image_natAdd_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：image_natAdd_Ioo (m) (i j : Fin n) : natAdd m '' Ioo i j = Ioo (natAdd m i
) (natAdd m j)
参数：m；i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.preimage_natAdd_Ioo_natAdd`：preimage_natAdd_Ioo_natAdd (m) (i j : Fi
n n) : natAdd m ⁻¹' Ioo (natAdd m i) (natAdd m j) = Ioo i j
· 使用定理 `Set.image_preimage_eq_of_subset`：image_preimage_eq_of_subset {f : α -> β
} {s : Set β} (hs : s subseteq range f) : f '' f ⁻¹' s = s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.Ioo_subset_Ioi_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo b a ⊆ Set.Ioi b
· 使用定理 `Set.image_subset_range`：image_subset_range (f : α -> β) (s) : f '' s sub
seteq range f
· 使用定理 `Fin.image_natAdd_Ioi`：image_natAdd_Ioi (m) (i : Fin n) : natAdd m '' Ioi
 i = Ioi (natAdd m i)
-/
theorem image_natAdd_Ioo (m) (i j : Fin n) :
    natAdd m '' Ioo i j = Ioo (natAdd m i) (natAdd m j) := by
  rw [← preimage_natAdd_Ioo_natAdd, image_preimage_eq_of_subset]
  exact Ioo_subset_Ioi_self.trans <| image_natAdd_Ioi m i ▸ image_subset_range _ _

@[simp]
/-
**Fin.image_natAdd_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：image_natAdd_uIcc (m) (i j : Fin n) : natAdd m '' uIcc i j = uIcc (natAdd 
m i) (natAdd m j)
参数：m；i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.image_natAdd_Icc`：image_natAdd_Icc (m) (i j : Fin n) : natAdd m '' I
cc i j = Icc (natAdd m i) (natAdd m j)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Monotone.map_min`：∀ {α : Type u} {β : Type v} [inst : LinearOrder α] [in
st_1 : LinearOrder β] {f : α → β} {a b : α},   Monotone f → f (min a b) = min (f
 a) (f…
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用引理 `Fin.strictMono_natAdd`：strictMono_natAdd (n) : StrictMono (natAdd n : Fi
n m -> Fin (n + m))
· 使用定理 `Monotone.map_max`：Monotone.map_max (hf : Monotone f) : f (max a b) = max
 (f a) (f b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_natAdd_uIcc (m) (i j : Fin n) :
    natAdd m '' uIcc i j = uIcc (natAdd m i) (natAdd m j) := by
  simp [uIcc, ← (strictMono_natAdd m).monotone.map_max, ← (strictMono_natAdd m).monotone.map_min]

@[simp]
/-
**Fin.image_natAdd_uIoc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：image_natAdd_uIoc (m) (i j : Fin n) : natAdd m '' uIoc i j = uIoc (natAdd 
m i) (natAdd m j)
参数：m；i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.image_natAdd_Ioc`：image_natAdd_Ioc (m) (i j : Fin n) : natAdd m '' I
oc i j = Ioc (natAdd m i) (natAdd m j)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Monotone.map_min`：∀ {α : Type u} {β : Type v} [inst : LinearOrder α] [in
st_1 : LinearOrder β] {f : α → β} {a b : α},   Monotone f → f (min a b) = min (f
 a) (f…
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用引理 `Fin.strictMono_natAdd`：strictMono_natAdd (n) : StrictMono (natAdd n : Fi
n m -> Fin (n + m))
· 使用定理 `Monotone.map_max`：Monotone.map_max (hf : Monotone f) : f (max a b) = max
 (f a) (f b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_natAdd_uIoc (m) (i j : Fin n) :
    natAdd m '' uIoc i j = uIoc (natAdd m i) (natAdd m j) := by
  simp [uIoc, ← (strictMono_natAdd m).monotone.map_max, ← (strictMono_natAdd m).monotone.map_min]

@[simp]
/-
**Fin.image_natAdd_uIoo** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：image_natAdd_uIoo (m) (i j : Fin n) : natAdd m '' uIoo i j = uIoo (natAdd 
m i) (natAdd m j)
参数：m；i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.image_natAdd_Ioo`：image_natAdd_Ioo (m) (i j : Fin n) : natAdd m '' I
oo i j = Ioo (natAdd m i) (natAdd m j)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Monotone.map_min`：∀ {α : Type u} {β : Type v} [inst : LinearOrder α] [in
st_1 : LinearOrder β] {f : α → β} {a b : α},   Monotone f → f (min a b) = min (f
 a) (f…
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用引理 `Fin.strictMono_natAdd`：strictMono_natAdd (n) : StrictMono (natAdd n : Fi
n m -> Fin (n + m))
· 使用定理 `Monotone.map_max`：Monotone.map_max (hf : Monotone f) : f (max a b) = max
 (f a) (f b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_natAdd_uIoo (m) (i j : Fin n) :
    natAdd m '' uIoo i j = uIoo (natAdd m i) (natAdd m j) := by
  simp [uIoo, ← (strictMono_natAdd m).monotone.map_max, ← (strictMono_natAdd m).monotone.map_min]

/-!
### `Fin.addNat`
-/

@[simp]
/-
**Fin.preimage_addNat_Ici_addNat** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_addNat_Ici_addNat (m) (i : Fin n) : (addNat · m) ⁻¹' Ici (i.addNa
t m) = Ici i
参数：m；i : Fin n。
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

--- 原说明 ---
### `Fin.addNat`
-/
theorem preimage_addNat_Ici_addNat (m) (i : Fin n) : (addNat · m) ⁻¹' Ici (i.addNat m) = Ici i := by
  ext; simp

@[simp]
/-
**Fin.preimage_addNat_Ioi_addNat** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_addNat_Ioi_addNat (m) (i : Fin n) : (addNat · m) ⁻¹' Ioi (i.addNa
t m) = Ioi i
参数：m；i : Fin n。
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
theorem preimage_addNat_Ioi_addNat (m) (i : Fin n) : (addNat · m) ⁻¹' Ioi (i.addNat m) = Ioi i := by
  ext; simp

@[simp]
/-
**Fin.preimage_addNat_Iic_addNat** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_addNat_Iic_addNat (m) (i : Fin n) : (addNat · m) ⁻¹' Iic (i.addNa
t m) = Iic i
参数：m；i : Fin n。
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
theorem preimage_addNat_Iic_addNat (m) (i : Fin n) : (addNat · m) ⁻¹' Iic (i.addNat m) = Iic i := by
  ext; simp

@[simp]
/-
**Fin.preimage_addNat_Iio_addNat** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_addNat_Iio_addNat (m) (i : Fin n) : (addNat · m) ⁻¹' Iio (i.addNa
t m) = Iio i
参数：m；i : Fin n。
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
theorem preimage_addNat_Iio_addNat (m) (i : Fin n) : (addNat · m) ⁻¹' Iio (i.addNat m) = Iio i := by
  ext; simp

@[simp]
/-
**Fin.preimage_addNat_Icc_addNat** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_addNat_Icc_addNat (m) (i j : Fin n) : (addNat · m) ⁻¹' Icc (i.add
Nat m) (j.addNat m) = Icc i j
参数：m；i j : Fin n。
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
theorem preimage_addNat_Icc_addNat (m) (i j : Fin n) :
    (addNat · m) ⁻¹' Icc (i.addNat m) (j.addNat m) = Icc i j := by
  ext; simp

@[simp]
/-
**Fin.preimage_addNat_Ico_addNat** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_addNat_Ico_addNat (m) (i j : Fin n) : (addNat · m) ⁻¹' Ico (i.add
Nat m) (j.addNat m) = Ico i j
参数：m；i j : Fin n。
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
theorem preimage_addNat_Ico_addNat (m) (i j : Fin n) :
    (addNat · m) ⁻¹' Ico (i.addNat m) (j.addNat m) = Ico i j := by
  ext; simp

@[simp]
/-
**Fin.preimage_addNat_Ioc_addNat** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_addNat_Ioc_addNat (m) (i j : Fin n) : (addNat · m) ⁻¹' Ioc (i.add
Nat m) (j.addNat m) = Ioc i j
参数：m；i j : Fin n。
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
theorem preimage_addNat_Ioc_addNat (m) (i j : Fin n) :
    (addNat · m) ⁻¹' Ioc (i.addNat m) (j.addNat m) = Ioc i j := by
  ext; simp

@[simp]
/-
**Fin.preimage_addNat_Ioo_addNat** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_addNat_Ioo_addNat (m) (i j : Fin n) : (addNat · m) ⁻¹' Ioo (i.add
Nat m) (j.addNat m) = Ioo i j
参数：m；i j : Fin n。
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
theorem preimage_addNat_Ioo_addNat (m) (i j : Fin n) :
    (addNat · m) ⁻¹' Ioo (i.addNat m) (j.addNat m) = Ioo i j := by
  ext; simp

@[simp]
/-
**Fin.preimage_addNat_uIcc_addNat** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_addNat_uIcc_addNat (m) (i j : Fin n) : (addNat · m) ⁻¹' uIcc (i.a
ddNat m) (j.addNat m) = uIcc i j
参数：m；i j : Fin n。
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Monotone.map_min`：∀ {α : Type u} {β : Type v} [inst : LinearOrder α] [in
st_1 : LinearOrder β] {f : α → β} {a b : α},   Monotone f → f (min a b) = min (f
 a) (f…
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用引理 `Fin.strictMono_addNat`：strictMono_addNat (m) : StrictMono ((addNat · m) 
: Fin n -> Fin (n + m))
· 使用定理 `Monotone.map_max`：Monotone.map_max (hf : Monotone f) : f (max a b) = max
 (f a) (f b)
· 使用定理 `Fin.preimage_addNat_Icc_addNat`：preimage_addNat_Icc_addNat (m) (i j : Fi
n n) : (addNat · m) ⁻¹' Icc (i.addNat m) (j.addNat m) = Icc i j
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preimage_addNat_uIcc_addNat (m) (i j : Fin n) :
    (addNat · m) ⁻¹' uIcc (i.addNat m) (j.addNat m) = uIcc i j := by
  simp [uIcc, ← (strictMono_addNat m).monotone.map_max, ← (strictMono_addNat m).monotone.map_min]

@[simp]
/-
**Fin.preimage_addNat_uIoc_addNat** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_addNat_uIoc_addNat (m) (i j : Fin n) : (addNat · m) ⁻¹' uIoc (i.a
ddNat m) (j.addNat m) = uIoc i j
参数：m；i j : Fin n。
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Monotone.map_min`：∀ {α : Type u} {β : Type v} [inst : LinearOrder α] [in
st_1 : LinearOrder β] {f : α → β} {a b : α},   Monotone f → f (min a b) = min (f
 a) (f…
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用引理 `Fin.strictMono_addNat`：strictMono_addNat (m) : StrictMono ((addNat · m) 
: Fin n -> Fin (n + m))
· 使用定理 `Monotone.map_max`：Monotone.map_max (hf : Monotone f) : f (max a b) = max
 (f a) (f b)
· 使用定理 `Fin.preimage_addNat_Ioc_addNat`：preimage_addNat_Ioc_addNat (m) (i j : Fi
n n) : (addNat · m) ⁻¹' Ioc (i.addNat m) (j.addNat m) = Ioc i j
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preimage_addNat_uIoc_addNat (m) (i j : Fin n) :
    (addNat · m) ⁻¹' uIoc (i.addNat m) (j.addNat m) = uIoc i j := by
  simp [uIoc, ← (strictMono_addNat m).monotone.map_max, ← (strictMono_addNat m).monotone.map_min]

@[simp]
/-
**Fin.preimage_addNat_uIoo_addNat** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_addNat_uIoo_addNat (m) (i j : Fin n) : (addNat · m) ⁻¹' uIoo (i.a
ddNat m) (j.addNat m) = uIoo i j
参数：m；i j : Fin n。
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Monotone.map_min`：∀ {α : Type u} {β : Type v} [inst : LinearOrder α] [in
st_1 : LinearOrder β] {f : α → β} {a b : α},   Monotone f → f (min a b) = min (f
 a) (f…
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用引理 `Fin.strictMono_addNat`：strictMono_addNat (m) : StrictMono ((addNat · m) 
: Fin n -> Fin (n + m))
· 使用定理 `Monotone.map_max`：Monotone.map_max (hf : Monotone f) : f (max a b) = max
 (f a) (f b)
· 使用定理 `Fin.preimage_addNat_Ioo_addNat`：preimage_addNat_Ioo_addNat (m) (i j : Fi
n n) : (addNat · m) ⁻¹' Ioo (i.addNat m) (j.addNat m) = Ioo i j
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preimage_addNat_uIoo_addNat (m) (i j : Fin n) :
    (addNat · m) ⁻¹' uIoo (i.addNat m) (j.addNat m) = uIoo i j := by
  simp [uIoo, ← (strictMono_addNat m).monotone.map_max, ← (strictMono_addNat m).monotone.map_min]

@[simp]
/-
**Fin.image_addNat_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：image_addNat_Ici (m) (i : Fin n) : (addNat · m) '' Ici i = Ici (i.addNat m
)
参数：m；i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.preimage_addNat_Ici_addNat`：preimage_addNat_Ici_addNat (m) (i : Fin 
n) : (addNat · m) ⁻¹' Ici (i.addNat m) = Ici i
· 使用定理 `Set.image_preimage_eq_of_subset`：image_preimage_eq_of_subset {f : α -> β
} {s : Set β} (hs : s subseteq range f) : f '' f ⁻¹' s = s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fin.mk.congr_simp`：∀ {n : ℕ} (val val_1 : ℕ) (e_val : val = val_1) (isLt
 : val < n), ⟨val, isLt⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用定理 `Nat.add_lt_add_right`：∀ {n m : ℕ}, n < m → ∀ (k : ℕ), n + k < m + k
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_addNat_Ici (m) (i : Fin n) : (addNat · m) '' Ici i = Ici (i.addNat m) := by
  rw [← preimage_addNat_Ici_addNat, image_preimage_eq_of_subset]
  intro j hj
  have : (i : ℕ) + m ≤ j := hj
  refine ⟨⟨j - m, by lia⟩, ?_⟩
  simp (disch := lia)

@[simp]
/-
**Fin.image_addNat_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：image_addNat_Ioi (m) (i : Fin n) : (addNat · m) '' Ioi i = Ioi (i.addNat m
)
参数：m；i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.preimage_addNat_Ioi_addNat`：preimage_addNat_Ioi_addNat (m) (i : Fin 
n) : (addNat · m) ⁻¹' Ioi (i.addNat m) = Ioi i
· 使用定理 `Set.image_preimage_eq_of_subset`：image_preimage_eq_of_subset {f : α -> β
} {s : Set β} (hs : s subseteq range f) : f '' f ⁻¹' s = s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.Ioi_subset_Ici_self`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, S
et.Ioi a ⊆ Set.Ici a
· 使用定理 `Set.image_subset_range`：image_subset_range (f : α -> β) (s) : f '' s sub
seteq range f
· 使用定理 `Fin.image_addNat_Ici`：image_addNat_Ici (m) (i : Fin n) : (addNat · m) ''
 Ici i = Ici (i.addNat m)
-/
theorem image_addNat_Ioi (m) (i : Fin n) : (addNat · m) '' Ioi i = Ioi (i.addNat m) := by
  rw [← preimage_addNat_Ioi_addNat, image_preimage_eq_of_subset]
  exact Ioi_subset_Ici_self.trans <| image_addNat_Ici m i ▸ image_subset_range _ _

@[simp]
/-
**Fin.image_addNat_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：image_addNat_Icc (m) (i j : Fin n) : (addNat · m) '' Icc i j = Icc (i.addN
at m) (j.addNat m)
参数：m；i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.preimage_addNat_Icc_addNat`：preimage_addNat_Icc_addNat (m) (i j : Fi
n n) : (addNat · m) ⁻¹' Icc (i.addNat m) (j.addNat m) = Icc i j
· 使用定理 `Set.image_preimage_eq_of_subset`：image_preimage_eq_of_subset {f : α -> β
} {s : Set β} (hs : s subseteq range f) : f '' f ⁻¹' s = s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.Icc_subset_Ici_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Icc b a ⊆ Set.Ici b
· 使用定理 `Set.image_subset_range`：image_subset_range (f : α -> β) (s) : f '' s sub
seteq range f
· 使用定理 `Fin.image_addNat_Ici`：image_addNat_Ici (m) (i : Fin n) : (addNat · m) ''
 Ici i = Ici (i.addNat m)
-/
theorem image_addNat_Icc (m) (i j : Fin n) :
    (addNat · m) '' Icc i j = Icc (i.addNat m) (j.addNat m) := by
  rw [← preimage_addNat_Icc_addNat, image_preimage_eq_of_subset]
  exact Icc_subset_Ici_self.trans <| image_addNat_Ici m i ▸ image_subset_range _ _

@[simp]
/-
**Fin.image_addNat_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：image_addNat_Ico (m) (i j : Fin n) : (addNat · m) '' Ico i j = Ico (i.addN
at m) (j.addNat m)
参数：m；i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.preimage_addNat_Ico_addNat`：preimage_addNat_Ico_addNat (m) (i j : Fi
n n) : (addNat · m) ⁻¹' Ico (i.addNat m) (j.addNat m) = Ico i j
· 使用定理 `Set.image_preimage_eq_of_subset`：image_preimage_eq_of_subset {f : α -> β
} {s : Set β} (hs : s subseteq range f) : f '' f ⁻¹' s = s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.Ico_subset_Ici_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ico b a ⊆ Set.Ici b
· 使用定理 `Set.image_subset_range`：image_subset_range (f : α -> β) (s) : f '' s sub
seteq range f
· 使用定理 `Fin.image_addNat_Ici`：image_addNat_Ici (m) (i : Fin n) : (addNat · m) ''
 Ici i = Ici (i.addNat m)
-/
theorem image_addNat_Ico (m) (i j : Fin n) :
    (addNat · m) '' Ico i j = Ico (i.addNat m) (j.addNat m) := by
  rw [← preimage_addNat_Ico_addNat, image_preimage_eq_of_subset]
  exact Ico_subset_Ici_self.trans <| image_addNat_Ici m i ▸ image_subset_range _ _

@[simp]
/-
**Fin.image_addNat_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：image_addNat_Ioc (m) (i j : Fin n) : (addNat · m) '' Ioc i j = Ioc (i.addN
at m) (j.addNat m)
参数：m；i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.preimage_addNat_Ioc_addNat`：preimage_addNat_Ioc_addNat (m) (i j : Fi
n n) : (addNat · m) ⁻¹' Ioc (i.addNat m) (j.addNat m) = Ioc i j
· 使用定理 `Set.image_preimage_eq_of_subset`：image_preimage_eq_of_subset {f : α -> β
} {s : Set β} (hs : s subseteq range f) : f '' f ⁻¹' s = s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.Ioc_subset_Ioi_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc b a ⊆ Set.Ioi b
· 使用定理 `Set.image_subset_range`：image_subset_range (f : α -> β) (s) : f '' s sub
seteq range f
· 使用定理 `Fin.image_addNat_Ioi`：image_addNat_Ioi (m) (i : Fin n) : (addNat · m) ''
 Ioi i = Ioi (i.addNat m)
-/
theorem image_addNat_Ioc (m) (i j : Fin n) :
    (addNat · m) '' Ioc i j = Ioc (i.addNat m) (j.addNat m) := by
  rw [← preimage_addNat_Ioc_addNat, image_preimage_eq_of_subset]
  exact Ioc_subset_Ioi_self.trans <| image_addNat_Ioi m i ▸ image_subset_range _ _

@[simp]
/-
**Fin.image_addNat_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：image_addNat_Ioo (m) (i j : Fin n) : (addNat · m) '' Ioo i j = Ioo (i.addN
at m) (j.addNat m)
参数：m；i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.preimage_addNat_Ioo_addNat`：preimage_addNat_Ioo_addNat (m) (i j : Fi
n n) : (addNat · m) ⁻¹' Ioo (i.addNat m) (j.addNat m) = Ioo i j
· 使用定理 `Set.image_preimage_eq_of_subset`：image_preimage_eq_of_subset {f : α -> β
} {s : Set β} (hs : s subseteq range f) : f '' f ⁻¹' s = s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.Ioo_subset_Ioi_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo b a ⊆ Set.Ioi b
· 使用定理 `Set.image_subset_range`：image_subset_range (f : α -> β) (s) : f '' s sub
seteq range f
· 使用定理 `Fin.image_addNat_Ioi`：image_addNat_Ioi (m) (i : Fin n) : (addNat · m) ''
 Ioi i = Ioi (i.addNat m)
-/
theorem image_addNat_Ioo (m) (i j : Fin n) :
    (addNat · m) '' Ioo i j = Ioo (i.addNat m) (j.addNat m) := by
  rw [← preimage_addNat_Ioo_addNat, image_preimage_eq_of_subset]
  exact Ioo_subset_Ioi_self.trans <| image_addNat_Ioi m i ▸ image_subset_range _ _

@[simp]
/-
**Fin.image_addNat_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：image_addNat_uIcc (m) (i j : Fin n) : (addNat · m) '' uIcc i j = uIcc (i.a
ddNat m) (j.addNat m)
参数：m；i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.image_addNat_Icc`：image_addNat_Icc (m) (i j : Fin n) : (addNat · m) 
'' Icc i j = Icc (i.addNat m) (j.addNat m)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Monotone.map_min`：∀ {α : Type u} {β : Type v} [inst : LinearOrder α] [in
st_1 : LinearOrder β] {f : α → β} {a b : α},   Monotone f → f (min a b) = min (f
 a) (f…
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用引理 `Fin.strictMono_addNat`：strictMono_addNat (m) : StrictMono ((addNat · m) 
: Fin n -> Fin (n + m))
· 使用定理 `Monotone.map_max`：Monotone.map_max (hf : Monotone f) : f (max a b) = max
 (f a) (f b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_addNat_uIcc (m) (i j : Fin n) :
    (addNat · m) '' uIcc i j = uIcc (i.addNat m) (j.addNat m) := by
  simp [uIcc, ← (strictMono_addNat m).monotone.map_max, ← (strictMono_addNat m).monotone.map_min]

@[simp]
/-
**Fin.image_addNat_uIoc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：image_addNat_uIoc (m) (i j : Fin n) : (addNat · m) '' uIoc i j = uIoc (i.a
ddNat m) (j.addNat m)
参数：m；i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.image_addNat_Ioc`：image_addNat_Ioc (m) (i j : Fin n) : (addNat · m) 
'' Ioc i j = Ioc (i.addNat m) (j.addNat m)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Monotone.map_min`：∀ {α : Type u} {β : Type v} [inst : LinearOrder α] [in
st_1 : LinearOrder β] {f : α → β} {a b : α},   Monotone f → f (min a b) = min (f
 a) (f…
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用引理 `Fin.strictMono_addNat`：strictMono_addNat (m) : StrictMono ((addNat · m) 
: Fin n -> Fin (n + m))
· 使用定理 `Monotone.map_max`：Monotone.map_max (hf : Monotone f) : f (max a b) = max
 (f a) (f b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_addNat_uIoc (m) (i j : Fin n) :
    (addNat · m) '' uIoc i j = uIoc (i.addNat m) (j.addNat m) := by
  simp [uIoc, ← (strictMono_addNat m).monotone.map_max, ← (strictMono_addNat m).monotone.map_min]

@[simp]
/-
**Fin.image_addNat_uIoo** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：image_addNat_uIoo (m) (i j : Fin n) : (addNat · m) '' uIoo i j = uIoo (i.a
ddNat m) (j.addNat m)
参数：m；i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.image_addNat_Ioo`：image_addNat_Ioo (m) (i j : Fin n) : (addNat · m) 
'' Ioo i j = Ioo (i.addNat m) (j.addNat m)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Monotone.map_min`：∀ {α : Type u} {β : Type v} [inst : LinearOrder α] [in
st_1 : LinearOrder β] {f : α → β} {a b : α},   Monotone f → f (min a b) = min (f
 a) (f…
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用引理 `Fin.strictMono_addNat`：strictMono_addNat (m) : StrictMono ((addNat · m) 
: Fin n -> Fin (n + m))
· 使用定理 `Monotone.map_max`：Monotone.map_max (hf : Monotone f) : f (max a b) = max
 (f a) (f b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_addNat_uIoo (m) (i j : Fin n) :
    (addNat · m) '' uIoo i j = uIoo (i.addNat m) (j.addNat m) := by
  simp [uIoo, ← (strictMono_addNat m).monotone.map_max, ← (strictMono_addNat m).monotone.map_min]

/-!
### `Fin.succ`
-/

@[simp]
/-
**Fin.preimage_succ_Ici_succ** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_succ_Ici_succ (i : Fin n) : succ ⁻¹' Ici i.succ = Ici i
参数：i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.preimage_addNat_Ici_addNat`：preimage_addNat_Ici_addNat (m) (i : Fin 
n) : (addNat · m) ⁻¹' Ici (i.addNat m) = Ici i

--- 原说明 ---
### `Fin.succ`
-/
theorem preimage_succ_Ici_succ (i : Fin n) : succ ⁻¹' Ici i.succ = Ici i :=
  preimage_addNat_Ici_addNat ..

@[simp]
/-
**Fin.preimage_succ_Ioi_succ** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_succ_Ioi_succ (i : Fin n) : succ ⁻¹' Ioi i.succ = Ioi i
参数：i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.preimage_addNat_Ioi_addNat`：preimage_addNat_Ioi_addNat (m) (i : Fin 
n) : (addNat · m) ⁻¹' Ioi (i.addNat m) = Ioi i
-/
theorem preimage_succ_Ioi_succ (i : Fin n) : succ ⁻¹' Ioi i.succ = Ioi i :=
  preimage_addNat_Ioi_addNat ..

@[simp]
/-
**Fin.preimage_succ_Iic_succ** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_succ_Iic_succ (i : Fin n) : succ ⁻¹' Iic i.succ = Iic i
参数：i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.preimage_addNat_Iic_addNat`：preimage_addNat_Iic_addNat (m) (i : Fin 
n) : (addNat · m) ⁻¹' Iic (i.addNat m) = Iic i
-/
theorem preimage_succ_Iic_succ (i : Fin n) : succ ⁻¹' Iic i.succ = Iic i :=
  preimage_addNat_Iic_addNat ..

@[simp]
/-
**Fin.preimage_succ_Iio_succ** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_succ_Iio_succ (i : Fin n) : succ ⁻¹' Iio i.succ = Iio i
参数：i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.preimage_addNat_Iio_addNat`：preimage_addNat_Iio_addNat (m) (i : Fin 
n) : (addNat · m) ⁻¹' Iio (i.addNat m) = Iio i
-/
theorem preimage_succ_Iio_succ (i : Fin n) : succ ⁻¹' Iio i.succ = Iio i :=
  preimage_addNat_Iio_addNat ..

@[simp]
/-
**Fin.preimage_succ_Icc_succ** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_succ_Icc_succ (i j : Fin n) : succ ⁻¹' Icc i.succ j.succ = Icc i 
j
参数：i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.preimage_addNat_Icc_addNat`：preimage_addNat_Icc_addNat (m) (i j : Fi
n n) : (addNat · m) ⁻¹' Icc (i.addNat m) (j.addNat m) = Icc i j
-/
theorem preimage_succ_Icc_succ (i j : Fin n) : succ ⁻¹' Icc i.succ j.succ = Icc i j :=
  preimage_addNat_Icc_addNat ..

@[simp]
/-
**Fin.preimage_succ_Ico_succ** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_succ_Ico_succ (i j : Fin n) : succ ⁻¹' Ico i.succ j.succ = Ico i 
j
参数：i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.preimage_addNat_Ico_addNat`：preimage_addNat_Ico_addNat (m) (i j : Fi
n n) : (addNat · m) ⁻¹' Ico (i.addNat m) (j.addNat m) = Ico i j
-/
theorem preimage_succ_Ico_succ (i j : Fin n) : succ ⁻¹' Ico i.succ j.succ = Ico i j :=
  preimage_addNat_Ico_addNat ..

@[simp]
/-
**Fin.preimage_succ_Ioc_succ** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_succ_Ioc_succ (i j : Fin n) : succ ⁻¹' Ioc i.succ j.succ = Ioc i 
j
参数：i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.preimage_addNat_Ioc_addNat`：preimage_addNat_Ioc_addNat (m) (i j : Fi
n n) : (addNat · m) ⁻¹' Ioc (i.addNat m) (j.addNat m) = Ioc i j
-/
theorem preimage_succ_Ioc_succ (i j : Fin n) : succ ⁻¹' Ioc i.succ j.succ = Ioc i j :=
  preimage_addNat_Ioc_addNat ..

@[simp]
/-
**Fin.preimage_succ_Ioo_succ** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_succ_Ioo_succ (i j : Fin n) : succ ⁻¹' Ioo i.succ j.succ = Ioo i 
j
参数：i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.preimage_addNat_Ioo_addNat`：preimage_addNat_Ioo_addNat (m) (i j : Fi
n n) : (addNat · m) ⁻¹' Ioo (i.addNat m) (j.addNat m) = Ioo i j
-/
theorem preimage_succ_Ioo_succ (i j : Fin n) : succ ⁻¹' Ioo i.succ j.succ = Ioo i j :=
  preimage_addNat_Ioo_addNat ..

@[simp]
/-
**Fin.preimage_succ_uIcc_succ** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_succ_uIcc_succ (i j : Fin n) : succ ⁻¹' uIcc i.succ j.succ = uIcc
 i j
参数：i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.preimage_addNat_uIcc_addNat`：preimage_addNat_uIcc_addNat (m) (i j : 
Fin n) : (addNat · m) ⁻¹' uIcc (i.addNat m) (j.addNat m) = uIcc i j
-/
theorem preimage_succ_uIcc_succ (i j : Fin n) : succ ⁻¹' uIcc i.succ j.succ = uIcc i j :=
  preimage_addNat_uIcc_addNat ..

@[simp]
/-
**Fin.preimage_succ_uIoc_succ** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_succ_uIoc_succ (i j : Fin n) : succ ⁻¹' uIoc i.succ j.succ = uIoc
 i j
参数：i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.preimage_addNat_uIoc_addNat`：preimage_addNat_uIoc_addNat (m) (i j : 
Fin n) : (addNat · m) ⁻¹' uIoc (i.addNat m) (j.addNat m) = uIoc i j
-/
theorem preimage_succ_uIoc_succ (i j : Fin n) : succ ⁻¹' uIoc i.succ j.succ = uIoc i j :=
  preimage_addNat_uIoc_addNat ..

@[simp]
/-
**Fin.preimage_succ_uIoo_succ** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_succ_uIoo_succ (i j : Fin n) : succ ⁻¹' uIoo i.succ j.succ = uIoo
 i j
参数：i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.preimage_addNat_uIoo_addNat`：preimage_addNat_uIoo_addNat (m) (i j : 
Fin n) : (addNat · m) ⁻¹' uIoo (i.addNat m) (j.addNat m) = uIoo i j
-/
theorem preimage_succ_uIoo_succ (i j : Fin n) : succ ⁻¹' uIoo i.succ j.succ = uIoo i j :=
  preimage_addNat_uIoo_addNat ..
/-
**Fin.image_succ_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n : ℕ} (i : Fin n), Fin.succ '' Set.Ici i = Set.Ici i.succ
参数：i : Fin n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.image_addNat_Ici`：image_addNat_Ici (m) (i : Fin n) : (addNat · m) ''
 Ici i = Ici (i.addNat m)
-/
@[simp] theorem image_succ_Ici (i : Fin n) : succ '' Ici i = Ici i.succ := image_addNat_Ici ..
/-
**Fin.image_succ_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n : ℕ} (i : Fin n), Fin.succ '' Set.Ioi i = Set.Ioi i.succ
参数：i : Fin n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.image_addNat_Ioi`：image_addNat_Ioi (m) (i : Fin n) : (addNat · m) ''
 Ioi i = Ioi (i.addNat m)
-/
@[simp] theorem image_succ_Ioi (i : Fin n) : succ '' Ioi i = Ioi i.succ := image_addNat_Ioi ..

@[simp]
/-
**Fin.image_succ_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：image_succ_Iic (i : Fin n) : succ '' Iic i = Ioc 0 i.succ
参数：i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `Fin.succ_pos`：∀ {n : ℕ} (a : Fin n), 0 < a.succ
· 使用定理 `Fin.succ_le_succ_iff`：∀ {n : ℕ} {a b : Fin n}, a.succ ≤ b.succ ↔ a ≤ b
· 使用定理 `Fin.exists_succ_eq_of_ne_zero`：exists_succ_eq_of_ne_zero {x : Fin (n + 1
)} (h : x != 0) : exists y, Fin.succ y = x
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem image_succ_Iic (i : Fin n) : succ '' Iic i = Ioc 0 i.succ := by
  refine Subset.antisymm (image_subset_iff.mpr fun j hj ↦ ⟨j.succ_pos, succ_le_succ_iff.2 hj⟩) ?_
  rintro j ⟨hj₀, hj⟩
  rcases exists_succ_eq_of_ne_zero hj₀.ne' with ⟨j, rfl⟩
  exact mem_image_of_mem _ <| succ_le_succ_iff.mp hj

@[simp]
/-
**Fin.image_succ_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：image_succ_Iio (i : Fin n) : succ '' Iio i = Ioo 0 i.succ
参数：i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `Fin.succ_pos`：∀ {n : ℕ} (a : Fin n), 0 < a.succ
· 使用定理 `Fin.succ_lt_succ_iff`：∀ {n : ℕ} {a b : Fin n}, a.succ < b.succ ↔ a < b
· 使用定理 `Fin.exists_succ_eq_of_ne_zero`：exists_succ_eq_of_ne_zero {x : Fin (n + 1
)} (h : x != 0) : exists y, Fin.succ y = x
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem image_succ_Iio (i : Fin n) : succ '' Iio i = Ioo 0 i.succ := by
  refine Subset.antisymm (image_subset_iff.mpr fun j hj ↦ ⟨j.succ_pos, succ_lt_succ_iff.2 hj⟩) ?_
  rintro j ⟨hj₀, hj⟩
  rcases exists_succ_eq_of_ne_zero hj₀.ne' with ⟨j, rfl⟩
  exact mem_image_of_mem _ <| succ_lt_succ_iff.mp hj

@[simp]
/-
**Fin.image_succ_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：image_succ_Icc (i j : Fin n) : succ '' Icc i j = Icc i.succ j.succ
参数：i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.image_addNat_Icc`：image_addNat_Icc (m) (i j : Fin n) : (addNat · m) 
'' Icc i j = Icc (i.addNat m) (j.addNat m)
-/
theorem image_succ_Icc (i j : Fin n) : succ '' Icc i j = Icc i.succ j.succ := image_addNat_Icc ..

@[simp]
/-
**Fin.image_succ_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：image_succ_Ico (i j : Fin n) : succ '' Ico i j = Ico i.succ j.succ
参数：i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.image_addNat_Ico`：image_addNat_Ico (m) (i j : Fin n) : (addNat · m) 
'' Ico i j = Ico (i.addNat m) (j.addNat m)
-/
theorem image_succ_Ico (i j : Fin n) : succ '' Ico i j = Ico i.succ j.succ := image_addNat_Ico ..

@[simp]
/-
**Fin.image_succ_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：image_succ_Ioc (i j : Fin n) : succ '' Ioc i j = Ioc i.succ j.succ
参数：i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.image_addNat_Ioc`：image_addNat_Ioc (m) (i j : Fin n) : (addNat · m) 
'' Ioc i j = Ioc (i.addNat m) (j.addNat m)
-/
theorem image_succ_Ioc (i j : Fin n) : succ '' Ioc i j = Ioc i.succ j.succ := image_addNat_Ioc ..

@[simp]
/-
**Fin.image_succ_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：image_succ_Ioo (i j : Fin n) : succ '' Ioo i j = Ioo i.succ j.succ
参数：i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.image_addNat_Ioo`：image_addNat_Ioo (m) (i j : Fin n) : (addNat · m) 
'' Ioo i j = Ioo (i.addNat m) (j.addNat m)
-/
theorem image_succ_Ioo (i j : Fin n) : succ '' Ioo i j = Ioo i.succ j.succ := image_addNat_Ioo ..

@[simp]
/-
**Fin.image_succ_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：image_succ_uIcc (i j : Fin n) : succ '' uIcc i j = uIcc i.succ j.succ
参数：i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.image_addNat_uIcc`：image_addNat_uIcc (m) (i j : Fin n) : (addNat · m
) '' uIcc i j = uIcc (i.addNat m) (j.addNat m)
-/
theorem image_succ_uIcc (i j : Fin n) : succ '' uIcc i j = uIcc i.succ j.succ :=
  image_addNat_uIcc ..

@[simp]
/-
**Fin.image_succ_uIoc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：image_succ_uIoc (i j : Fin n) : succ '' uIoc i j = uIoc i.succ j.succ
参数：i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.image_addNat_uIoc`：image_addNat_uIoc (m) (i j : Fin n) : (addNat · m
) '' uIoc i j = uIoc (i.addNat m) (j.addNat m)
-/
theorem image_succ_uIoc (i j : Fin n) : succ '' uIoc i j = uIoc i.succ j.succ :=
  image_addNat_uIoc ..

@[simp]
/-
**Fin.image_succ_uIoo** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：image_succ_uIoo (i j : Fin n) : succ '' uIoo i j = uIoo i.succ j.succ
参数：i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.image_addNat_uIoo`：image_addNat_uIoo (m) (i j : Fin n) : (addNat · m
) '' uIoo i j = uIoo (i.addNat m) (j.addNat m)
-/
theorem image_succ_uIoo (i j : Fin n) : succ '' uIoo i j = uIoo i.succ j.succ :=
  image_addNat_uIoo ..

/-!
### `Fin.rev`
-/

@[simp]
/-
**Fin.range_rev** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：range_rev : range (rev : Fin n -> Fin n) = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.range_eq`：∀ {α : Type u_1} {ι : Sort u_4} {f : ι → α
}, Function.Surjective f → Set.range f = Set.univ
· 使用定理 `Fin.rev_surjective`：rev_surjective : Surjective (@rev n)

--- 原说明 ---
### `Fin.rev`
-/
theorem range_rev : range (rev : Fin n → Fin n) = univ := rev_surjective.range_eq
/-
**Fin.image_rev** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：image_rev (s : Set (Fin n)) : rev '' s = rev ⁻¹' s
参数：s : Set (Fin n)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Equiv.image_eq_preimage_symm`：image_eq_preimage_symm (e : α ≃ β) (s : Se
t α) : e '' s = e.symm ⁻¹' s
-/
theorem image_rev (s : Set (Fin n)) : rev '' s = rev ⁻¹' s := revPerm.image_eq_preimage_symm s

@[simp]
/-
**Fin.image_rev_fun** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：image_rev_fun : image (@rev n) = preimage rev
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fin.image_rev`：image_rev (s : Set (Fin n)) : rev '' s = rev ⁻¹' s
-/
theorem image_rev_fun : image (@rev n) = preimage rev := funext image_rev

@[simp]
/-
**Fin.preimage_rev_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_rev_Ici (i : Fin n) : rev ⁻¹' Ici i = Iic i.rev
参数：i : Fin n。
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
theorem preimage_rev_Ici (i : Fin n) : rev ⁻¹' Ici i = Iic i.rev := by ext; simp [le_rev_iff]

@[simp]
/-
**Fin.preimage_rev_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_rev_Ioi (i : Fin n) : rev ⁻¹' Ioi i = Iio i.rev
参数：i : Fin n。
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
theorem preimage_rev_Ioi (i : Fin n) : rev ⁻¹' Ioi i = Iio i.rev := by ext; simp [lt_rev_iff]

@[simp]
/-
**Fin.preimage_rev_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_rev_Iic (i : Fin n) : rev ⁻¹' Iic i = Ici i.rev
参数：i : Fin n。
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
theorem preimage_rev_Iic (i : Fin n) : rev ⁻¹' Iic i = Ici i.rev := by ext; simp [rev_le_iff]

@[simp]
/-
**Fin.preimage_rev_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_rev_Iio (i : Fin n) : rev ⁻¹' Iio i = Ioi i.rev
参数：i : Fin n。
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
theorem preimage_rev_Iio (i : Fin n) : rev ⁻¹' Iio i = Ioi i.rev := by ext; simp [rev_lt_iff]

@[simp]
/-
**Fin.preimage_rev_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_rev_Icc (i j : Fin n) : rev ⁻¹' Icc i j = Icc j.rev i.rev
参数：i j : Fin n。
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
theorem preimage_rev_Icc (i j : Fin n) : rev ⁻¹' Icc i j = Icc j.rev i.rev := by
  ext; simp [le_rev_iff, rev_le_iff, and_comm]

@[simp]
/-
**Fin.preimage_rev_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_rev_Ico (i j : Fin n) : rev ⁻¹' Ico i j = Ioc j.rev i.rev
参数：i j : Fin n。
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
theorem preimage_rev_Ico (i j : Fin n) : rev ⁻¹' Ico i j = Ioc j.rev i.rev := by
  ext; simp [le_rev_iff, rev_lt_iff, and_comm]

@[simp]
/-
**Fin.preimage_rev_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_rev_Ioc (i j : Fin n) : rev ⁻¹' Ioc i j = Ico j.rev i.rev
参数：i j : Fin n。
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
theorem preimage_rev_Ioc (i j : Fin n) : rev ⁻¹' Ioc i j = Ico j.rev i.rev := by
  ext; simp [lt_rev_iff, rev_le_iff, and_comm]

@[simp]
/-
**Fin.preimage_rev_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_rev_Ioo (i j : Fin n) : rev ⁻¹' Ioo i j = Ioo j.rev i.rev
参数：i j : Fin n。
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
theorem preimage_rev_Ioo (i j : Fin n) : rev ⁻¹' Ioo i j = Ioo j.rev i.rev := by
  ext; simp [lt_rev_iff, rev_lt_iff, and_comm]

@[simp]
/-
**Fin.preimage_rev_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_rev_uIcc (i j : Fin n) : rev ⁻¹' uIcc i j = uIcc i.rev j.rev
参数：i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.preimage_rev_Icc`：preimage_rev_Icc (i j : Fin n) : rev ⁻¹' Icc i j =
 Icc j.rev i.rev
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Antitone.map_max`：Antitone.map_max (hf : Antitone f) : f (max a b) = min
 (f a) (f b)
· 使用引理 `Fin.rev_anti`：rev_anti : Antitone (@rev n)
· 使用定理 `Antitone.map_min`：∀ {α : Type u} {β : Type v} [inst : LinearOrder α] [in
st_1 : LinearOrder β] {f : α → β} {a b : α},   Antitone f → f (min a b) = max (f
 a) (f…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preimage_rev_uIcc (i j : Fin n) : rev ⁻¹' uIcc i j = uIcc i.rev j.rev := by
  simp [uIcc, ← rev_anti.map_min, ← rev_anti.map_max]

@[simp]
/-
**Fin.preimage_rev_uIoo** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：preimage_rev_uIoo (i j : Fin n) : rev ⁻¹' uIoo i j = uIoo i.rev j.rev
参数：i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.preimage_rev_Ioo`：preimage_rev_Ioo (i j : Fin n) : rev ⁻¹' Ioo i j =
 Ioo j.rev i.rev
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Antitone.map_max`：Antitone.map_max (hf : Antitone f) : f (max a b) = min
 (f a) (f b)
· 使用引理 `Fin.rev_anti`：rev_anti : Antitone (@rev n)
· 使用定理 `Antitone.map_min`：∀ {α : Type u} {β : Type v} [inst : LinearOrder α] [in
st_1 : LinearOrder β] {f : α → β} {a b : α},   Antitone f → f (min a b) = max (f
 a) (f…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preimage_rev_uIoo (i j : Fin n) : rev ⁻¹' uIoo i j = uIoo i.rev j.rev := by
  simp [uIoo, ← rev_anti.map_min, ← rev_anti.map_max]

end Fin

