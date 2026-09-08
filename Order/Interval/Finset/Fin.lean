/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Yury Kudryashov
-/
module

public import Mathlib.Data.Finset.Fin
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Order.Interval.Set.Fin

/-!
# Finite intervals in `Fin n`

This file proves that `Fin n` is a `LocallyFiniteOrder` and calculates the cardinality of its
intervals as Finsets and Fintypes.
-/

public section

assert_not_exists MonoidWithZero

open Finset Function

namespace Fin

variable (n : ℕ)

/-!
### Locally finite order etc. instances
-/

/-
**Fin.instLocallyFiniteOrder** 是 Mathlib 中的一个实例，位于命名空间 `Fin`。
形式化陈述：instLocallyFiniteOrder (n : Nat) : LocallyFiniteOrder (Fin n) where finset
Icc a b
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Locally finite order etc. instances
-/
instance instLocallyFiniteOrder (n : ℕ) : LocallyFiniteOrder (Fin n) where
  finsetIcc a b := attachFin (Icc a b) fun x hx ↦ (mem_Icc.mp hx).2.trans_lt b.2
  finsetIco a b := attachFin (Ico a b) fun x hx ↦ (mem_Ico.mp hx).2.trans b.2
  finsetIoc a b := attachFin (Ioc a b) fun x hx ↦ (mem_Ioc.mp hx).2.trans_lt b.2
  finsetIoo a b := attachFin (Ioo a b) fun x hx ↦ (mem_Ioo.mp hx).2.trans b.2
  finset_mem_Icc a b := by simp
  finset_mem_Ico a b := by simp
  finset_mem_Ioc a b := by simp
  finset_mem_Ioo a b := by simp
/-
**Fin.instLocallyFiniteOrderBot** 是 Mathlib 中的一个定义，位于命名空间 `Fin`。
形式化陈述：(n : ℕ) → LocallyFiniteOrderBot (Fin n)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instLocallyFiniteOrderBot : ∀ n, LocallyFiniteOrderBot (Fin n)
  | 0 => IsEmpty.toLocallyFiniteOrderBot
  | _ + 1 => inferInstance
/-
**Fin.instLocallyFiniteOrderTop** 是 Mathlib 中的一个定义，位于命名空间 `Fin`。
形式化陈述：(n : ℕ) → LocallyFiniteOrderTop (Fin n)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instLocallyFiniteOrderTop : ∀ n, LocallyFiniteOrderTop (Fin n)
  | 0 => IsEmpty.toLocallyFiniteOrderTop
  | _ + 1 => inferInstance

variable {n}
variable {m : ℕ} (a b : Fin n)

@[simp]
/-
**Fin.attachFin_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：attachFin_Icc : attachFin (Icc a b) (fun _x hx => (mem_Icc.mp hx).2.trans_
lt b.2) = Icc a b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_Icc`：mem_Icc : x in Icc a b ↔ a <= x ∧ x <= b
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
-/
theorem attachFin_Icc :
    attachFin (Icc a b) (fun _x hx ↦ (mem_Icc.mp hx).2.trans_lt b.2) = Icc a b :=
  rfl

@[simp]
/-
**Fin.attachFin_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：attachFin_Ico : attachFin (Ico a b) (fun _x hx => (mem_Ico.mp hx).2.trans 
b.2) = Ico a b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_Ico`：mem_Ico : x in Ico a b ↔ a <= x ∧ x < b
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
-/
theorem attachFin_Ico :
    attachFin (Ico a b) (fun _x hx ↦ (mem_Ico.mp hx).2.trans b.2) = Ico a b :=
  rfl

@[simp]
/-
**Fin.attachFin_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：attachFin_Ioc : attachFin (Ioc a b) (fun _x hx => (mem_Ioc.mp hx).2.trans_
lt b.2) = Ioc a b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_Ioc`：mem_Ioc : x in Ioc a b ↔ a < x ∧ x <= b
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
-/
theorem attachFin_Ioc :
    attachFin (Ioc a b) (fun _x hx ↦ (mem_Ioc.mp hx).2.trans_lt b.2) = Ioc a b :=
  rfl

@[simp]
/-
**Fin.attachFin_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：attachFin_Ioo : attachFin (Ioo a b) (fun _x hx => (mem_Ioo.mp hx).2.trans 
b.2) = Ioo a b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_Ioo`：mem_Ioo : x in Ioo a b ↔ a < x ∧ x < b
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
-/
theorem attachFin_Ioo :
    attachFin (Ioo a b) (fun _x hx ↦ (mem_Ioo.mp hx).2.trans b.2) = Ioo a b :=
  rfl

@[simp]
/-
**Fin.attachFin_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：attachFin_uIcc : attachFin (uIcc a b) (fun _x hx => (mem_Icc.mp hx).2.tran
s_lt (max a b).2) = uIcc a b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_Icc`：mem_Icc : x in Icc a b ↔ a <= x ∧ x <= b
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
-/
theorem attachFin_uIcc :
    attachFin (uIcc a b) (fun _x hx ↦ (mem_Icc.mp hx).2.trans_lt (max a b).2) = uIcc a b :=
  rfl

@[simp]
/-
**Fin.attachFin_Ico_eq_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：attachFin_Ico_eq_Ici : attachFin (Ico a n) (fun _x hx => (mem_Ico.mp hx).2
) = Ici a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_Ico`：mem_Ico : x in Ico a b ↔ a <= x ∧ x < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem attachFin_Ico_eq_Ici : attachFin (Ico a n) (fun _x hx ↦ (mem_Ico.mp hx).2) = Ici a := by
  ext; simp

@[simp]
/-
**Fin.attachFin_Ioo_eq_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：attachFin_Ioo_eq_Ioi : attachFin (Ioo a n) (fun _x hx => (mem_Ioo.mp hx).2
) = Ioi a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_Ioo`：mem_Ioo : x in Ioo a b ↔ a < x ∧ x < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem attachFin_Ioo_eq_Ioi : attachFin (Ioo a n) (fun _x hx ↦ (mem_Ioo.mp hx).2) = Ioi a := by
  ext; simp

@[simp]
/-
**Fin.attachFin_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：attachFin_Iic : attachFin (Iic a) (fun _x hx => (mem_Iic.mp hx).trans_lt a
.2) = Iic a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_Iic`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] {a x : α}, x ∈ Finset.Iic a ↔ x ≤ a
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem attachFin_Iic : attachFin (Iic a) (fun _x hx ↦ (mem_Iic.mp hx).trans_lt a.2) = Iic a := by
  ext; simp

@[simp]
/-
**Fin.attachFin_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：attachFin_Iio : attachFin (Iio a) (fun _x hx => (mem_Iio.mp hx).trans a.2)
 = Iio a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_Iio`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] {a x : α}, x ∈ Finset.Iio a ↔ x < a
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem attachFin_Iio : attachFin (Iio a) (fun _x hx ↦ (mem_Iio.mp hx).trans a.2) = Iio a := by
  ext; simp

section val

/-!
### Images under `Fin.val`
-/

@[simp]
/-
**Fin.finsetImage_val_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_val_Icc : (Icc a b).image val = Icc (a : Nat) b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.image_val_attachFin`：image_val_attachFin {s : Finset Nat} (h : fo
rall m in s, m < n) : image Fin.val (s.attachFin h) = s

--- 原说明 ---
### Images under `Fin.val`
-/
theorem finsetImage_val_Icc : (Icc a b).image val = Icc (a : ℕ) b :=
  image_val_attachFin _

@[simp]
/-
**Fin.finsetImage_val_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_val_Ico : (Ico a b).image val = Ico (a : Nat) b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.image_val_attachFin`：image_val_attachFin {s : Finset Nat} (h : fo
rall m in s, m < n) : image Fin.val (s.attachFin h) = s
-/
theorem finsetImage_val_Ico : (Ico a b).image val = Ico (a : ℕ) b :=
  image_val_attachFin _

@[simp]
/-
**Fin.finsetImage_val_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_val_Ioc : (Ioc a b).image val = Ioc (a : Nat) b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.image_val_attachFin`：image_val_attachFin {s : Finset Nat} (h : fo
rall m in s, m < n) : image Fin.val (s.attachFin h) = s
-/
theorem finsetImage_val_Ioc : (Ioc a b).image val = Ioc (a : ℕ) b :=
  image_val_attachFin _

@[simp]
/-
**Fin.finsetImage_val_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_val_Ioo : (Ioo a b).image val = Ioo (a : Nat) b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.image_val_attachFin`：image_val_attachFin {s : Finset Nat} (h : fo
rall m in s, m < n) : image Fin.val (s.attachFin h) = s
-/
theorem finsetImage_val_Ioo : (Ioo a b).image val = Ioo (a : ℕ) b :=
  image_val_attachFin _

@[simp]
/-
**Fin.finsetImage_val_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_val_uIcc : (uIcc a b).image val = uIcc (a : Nat) b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.finsetImage_val_Icc`：finsetImage_val_Icc : (Icc a b).image val = Icc
 (a : Nat) b
-/
theorem finsetImage_val_uIcc : (uIcc a b).image val = uIcc (a : ℕ) b :=
  finsetImage_val_Icc _ _

@[simp]
/-
**Fin.finsetImage_val_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_val_Ici : (Ici a).image val = Ico (a : Nat) n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Finset.coe_Ici`：coe_Ici (a : α) : (Ici a : Set α) = Set.Ici a
· 使用定理 `Fin.image_val_Ici`：image_val_Ici (i : Fin n) : (↑) '' Ici i = Ico (i : N
at) n
· 使用定理 `Finset.coe_Ico`：coe_Ico (a b : α) : (Ico a b : Set α) = Set.Ico a b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finsetImage_val_Ici : (Ici a).image val = Ico (a : ℕ) n := by simp [← coe_inj]

@[simp]
/-
**Fin.finsetImage_val_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_val_Ioi : (Ioi a).image val = Ioo (a : Nat) n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Finset.coe_Ioi`：coe_Ioi (a : α) : (Ioi a : Set α) = Set.Ioi a
· 使用定理 `Fin.image_val_Ioi`：image_val_Ioi (i : Fin n) : (↑) '' Ioi i = Ioo (i : N
at) n
· 使用定理 `Finset.coe_Ioo`：coe_Ioo (a b : α) : (Ioo a b : Set α) = Set.Ioo a b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finsetImage_val_Ioi : (Ioi a).image val = Ioo (a : ℕ) n := by simp [← coe_inj]

@[simp]
/-
**Fin.finsetImage_val_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_val_Iic : (Iic a).image val = Iic (a : Nat)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Finset.coe_Iic`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] (a : α), ↑(Finset.Iic a) = Set.Iic a
· 使用定理 `Fin.image_val_Iic`：image_val_Iic (i : Fin n) : (↑) '' Iic i = Iic (i : N
at)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finsetImage_val_Iic : (Iic a).image val = Iic (a : ℕ) := by simp [← coe_inj]

@[simp]
/-
**Fin.finsetImage_val_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_val_Iio : (Iio b).image val = Iio (b : Nat)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Finset.coe_Iio`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] (a : α), ↑(Finset.Iio a) = Set.Iio a
· 使用定理 `Fin.image_val_Iio`：image_val_Iio (i : Fin n) : (↑) '' Iio i = Iio (i : N
at)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finsetImage_val_Iio : (Iio b).image val = Iio (b : ℕ) := by simp [← coe_inj]

/-!
### `Finset.map` along `Fin.valEmbedding`
-/

@[simp]
/-
**Fin.map_valEmbedding_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_valEmbedding_Icc : (Icc a b).map Fin.valEmbedding = Icc (a : Nat) b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.map_valEmbedding_attachFin`：map_valEmbedding_attachFin {s : Finse
t Nat} (h : forall m in s, m < n) : map Fin.valEmbedding (s.attachFin h) = s

--- 原说明 ---
### `Finset.map` along `Fin.valEmbedding`
-/
theorem map_valEmbedding_Icc : (Icc a b).map Fin.valEmbedding = Icc (a : ℕ) b :=
  map_valEmbedding_attachFin _

@[simp]
/-
**Fin.map_valEmbedding_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_valEmbedding_Ico : (Ico a b).map Fin.valEmbedding = Ico (a : Nat) b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.map_valEmbedding_attachFin`：map_valEmbedding_attachFin {s : Finse
t Nat} (h : forall m in s, m < n) : map Fin.valEmbedding (s.attachFin h) = s
-/
theorem map_valEmbedding_Ico : (Ico a b).map Fin.valEmbedding = Ico (a : ℕ) b :=
  map_valEmbedding_attachFin _

@[simp]
/-
**Fin.map_valEmbedding_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_valEmbedding_Ioc : (Ioc a b).map Fin.valEmbedding = Ioc (a : Nat) b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.map_valEmbedding_attachFin`：map_valEmbedding_attachFin {s : Finse
t Nat} (h : forall m in s, m < n) : map Fin.valEmbedding (s.attachFin h) = s
-/
theorem map_valEmbedding_Ioc : (Ioc a b).map Fin.valEmbedding = Ioc (a : ℕ) b :=
  map_valEmbedding_attachFin _

@[simp]
/-
**Fin.map_valEmbedding_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_valEmbedding_Ioo : (Ioo a b).map Fin.valEmbedding = Ioo (a : Nat) b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.map_valEmbedding_attachFin`：map_valEmbedding_attachFin {s : Finse
t Nat} (h : forall m in s, m < n) : map Fin.valEmbedding (s.attachFin h) = s
-/
theorem map_valEmbedding_Ioo : (Ioo a b).map Fin.valEmbedding = Ioo (a : ℕ) b :=
  map_valEmbedding_attachFin _

@[simp]
/-
**Fin.map_valEmbedding_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_valEmbedding_uIcc : (uIcc a b).map valEmbedding = uIcc (a : Nat) b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.map_valEmbedding_Icc`：map_valEmbedding_Icc : (Icc a b).map Fin.valEm
bedding = Icc (a : Nat) b
-/
theorem map_valEmbedding_uIcc : (uIcc a b).map valEmbedding = uIcc (a : ℕ) b :=
  map_valEmbedding_Icc _ _

@[simp]
/-
**Fin.map_valEmbedding_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_valEmbedding_Ici : (Ici a).map Fin.valEmbedding = Ico (a : Nat) n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_Ico`：mem_Ico : x in Ico a b ↔ a <= x ∧ x < b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.attachFin_Ico_eq_Ici`：attachFin_Ico_eq_Ici : attachFin (Ico a n) (fu
n _x hx => (mem_Ico.mp hx).2) = Ici a
· 使用引理 `Finset.map_valEmbedding_attachFin`：map_valEmbedding_attachFin {s : Finse
t Nat} (h : forall m in s, m < n) : map Fin.valEmbedding (s.attachFin h) = s
-/
theorem map_valEmbedding_Ici : (Ici a).map Fin.valEmbedding = Ico (a : ℕ) n := by
  rw [← attachFin_Ico_eq_Ici, map_valEmbedding_attachFin]

@[simp]
/-
**Fin.map_valEmbedding_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_valEmbedding_Ioi : (Ioi a).map Fin.valEmbedding = Ioo (a : Nat) n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_Ioo`：mem_Ioo : x in Ioo a b ↔ a < x ∧ x < b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.attachFin_Ioo_eq_Ioi`：attachFin_Ioo_eq_Ioi : attachFin (Ioo a n) (fu
n _x hx => (mem_Ioo.mp hx).2) = Ioi a
· 使用引理 `Finset.map_valEmbedding_attachFin`：map_valEmbedding_attachFin {s : Finse
t Nat} (h : forall m in s, m < n) : map Fin.valEmbedding (s.attachFin h) = s
-/
theorem map_valEmbedding_Ioi : (Ioi a).map Fin.valEmbedding = Ioo (a : ℕ) n := by
  rw [← attachFin_Ioo_eq_Ioi, map_valEmbedding_attachFin]

@[simp]
/-
**Fin.map_valEmbedding_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_valEmbedding_Iic : (Iic a).map Fin.valEmbedding = Iic (a : Nat)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_Iic`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] {a x : α}, x ∈ Finset.Iic a ↔ x ≤ a
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.attachFin_Iic`：attachFin_Iic : attachFin (Iic a) (fun _x hx => (mem_
Iic.mp hx).trans_lt a.2) = Iic a
· 使用引理 `Finset.map_valEmbedding_attachFin`：map_valEmbedding_attachFin {s : Finse
t Nat} (h : forall m in s, m < n) : map Fin.valEmbedding (s.attachFin h) = s
-/
theorem map_valEmbedding_Iic : (Iic a).map Fin.valEmbedding = Iic (a : ℕ) := by
  rw [← attachFin_Iic, map_valEmbedding_attachFin]

@[simp]
/-
**Fin.map_valEmbedding_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_valEmbedding_Iio : (Iio a).map Fin.valEmbedding = Iio (a : Nat)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_Iio`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] {a x : α}, x ∈ Finset.Iio a ↔ x < a
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.attachFin_Iio`：attachFin_Iio : attachFin (Iio a) (fun _x hx => (mem_
Iio.mp hx).trans a.2) = Iio a
· 使用引理 `Finset.map_valEmbedding_attachFin`：map_valEmbedding_attachFin {s : Finse
t Nat} (h : forall m in s, m < n) : map Fin.valEmbedding (s.attachFin h) = s
-/
theorem map_valEmbedding_Iio : (Iio a).map Fin.valEmbedding = Iio (a : ℕ) := by
  rw [← attachFin_Iio, map_valEmbedding_attachFin]

end val

section castLE

/-!
### Image under `Fin.castLE`
-/

@[simp]
/-
**Fin.finsetImage_castLE_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_castLE_Icc (h : n <= m) : (Icc a b).image (castLE h) = Icc (ca
stLE h a) (castLE h b)
参数：h : n <= m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Finset.coe_Icc`：coe_Icc (a b : α) : (Icc a b : Set α) = Set.Icc a b
· 使用定理 `Fin.image_castLE_Icc`：image_castLE_Icc (i j : Fin m) (h : m <= n) : cast
LE h '' Icc i j = Icc (castLE h i) (castLE h j)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
### Image under `Fin.castLE`
-/
theorem finsetImage_castLE_Icc (h : n ≤ m) :
    (Icc a b).image (castLE h) = Icc (castLE h a) (castLE h b) := by simp [← coe_inj]

@[simp]
/-
**Fin.finsetImage_castLE_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_castLE_Ico (h : n <= m) : (Ico a b).image (castLE h) = Ico (ca
stLE h a) (castLE h b)
参数：h : n <= m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Finset.coe_Ico`：coe_Ico (a b : α) : (Ico a b : Set α) = Set.Ico a b
· 使用定理 `Fin.image_castLE_Ico`：image_castLE_Ico (i j : Fin m) (h : m <= n) : cast
LE h '' Ico i j = Ico (castLE h i) (castLE h j)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finsetImage_castLE_Ico (h : n ≤ m) :
    (Ico a b).image (castLE h) = Ico (castLE h a) (castLE h b) := by simp [← coe_inj]

@[simp]
/-
**Fin.finsetImage_castLE_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_castLE_Ioc (h : n <= m) : (Ioc a b).image (castLE h) = Ioc (ca
stLE h a) (castLE h b)
参数：h : n <= m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Finset.coe_Ioc`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrder α] (b a : α), ↑(Finset.Ioc b a) = Set.Ioc b a
· 使用定理 `Fin.image_castLE_Ioc`：image_castLE_Ioc (i j : Fin m) (h : m <= n) : cast
LE h '' Ioc i j = Ioc (castLE h i) (castLE h j)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finsetImage_castLE_Ioc (h : n ≤ m) :
    (Ioc a b).image (castLE h) = Ioc (castLE h a) (castLE h b) := by simp [← coe_inj]

@[simp]
/-
**Fin.finsetImage_castLE_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_castLE_Ioo (h : n <= m) : (Ioo a b).image (castLE h) = Ioo (ca
stLE h a) (castLE h b)
参数：h : n <= m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Finset.coe_Ioo`：coe_Ioo (a b : α) : (Ioo a b : Set α) = Set.Ioo a b
· 使用定理 `Fin.image_castLE_Ioo`：image_castLE_Ioo (i j : Fin m) (h : m <= n) : cast
LE h '' Ioo i j = Ioo (castLE h i) (castLE h j)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finsetImage_castLE_Ioo (h : n ≤ m) :
    (Ioo a b).image (castLE h) = Ioo (castLE h a) (castLE h b) := by simp [← coe_inj]

@[simp]
/-
**Fin.finsetImage_castLE_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_castLE_uIcc (h : n <= m) : (uIcc a b).image (castLE h) = uIcc 
(castLE h a) (castLE h b)
参数：h : n <= m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Finset.coe_uIcc`：coe_uIcc (a b : α) : (Finset.uIcc a b : Set α) = Set.uI
cc a b
· 使用定理 `Fin.image_castLE_uIcc`：image_castLE_uIcc (i j : Fin m) (h : m <= n) : ca
stLE h '' uIcc i j = uIcc (castLE h i) (castLE h j)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finsetImage_castLE_uIcc (h : n ≤ m) :
    (uIcc a b).image (castLE h) = uIcc (castLE h a) (castLE h b) := by simp [← coe_inj]

@[simp]
/-
**Fin.finsetImage_castLE_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_castLE_Iic (h : n <= m) : (Iic a).image (castLE h) = Iic (cast
LE h a)
参数：h : n <= m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Finset.coe_Iic`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] (a : α), ↑(Finset.Iic a) = Set.Iic a
· 使用定理 `Fin.image_castLE_Iic`：image_castLE_Iic (i : Fin m) (h : m <= n) : castLE
 h '' Iic i = Iic (castLE h i)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finsetImage_castLE_Iic (h : n ≤ m) :
    (Iic a).image (castLE h) = Iic (castLE h a) := by simp [← coe_inj]

@[simp]
/-
**Fin.finsetImage_castLE_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_castLE_Iio (h : n <= m) : (Iio a).image (castLE h) = Iio (cast
LE h a)
参数：h : n <= m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Finset.coe_Iio`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] (a : α), ↑(Finset.Iio a) = Set.Iio a
· 使用定理 `Fin.image_castLE_Iio`：image_castLE_Iio (i : Fin m) (h : m <= n) : castLE
 h '' Iio i = Iio (castLE h i)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finsetImage_castLE_Iio (h : n ≤ m) :
    (Iio a).image (castLE h) = Iio (castLE h a) := by simp [← coe_inj]

/-!
### `Finset.map` along `Fin.castLEEmb`
-/

@[simp]
/-
**Fin.map_castLEEmb_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_castLEEmb_Icc (h : n <= m) : (Icc a b).map (castLEEmb h) = Icc (castLE
 h a) (castLE h b)
参数：h : n <= m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Fin.castLEEmb_apply`：∀ {n m : ℕ} (h : n ≤ m) (i : Fin n), (Fin.castLEEmb
 h) i = Fin.castLE h i
· 使用定理 `Finset.coe_Icc`：coe_Icc (a b : α) : (Icc a b : Set α) = Set.Icc a b
· 使用定理 `Fin.image_castLE_Icc`：image_castLE_Icc (i j : Fin m) (h : m <= n) : cast
LE h '' Icc i j = Icc (castLE h i) (castLE h j)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
### `Finset.map` along `Fin.castLEEmb`
-/
theorem map_castLEEmb_Icc (h : n ≤ m) :
    (Icc a b).map (castLEEmb h) = Icc (castLE h a) (castLE h b) := by simp [← coe_inj]

@[simp]
/-
**Fin.map_castLEEmb_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_castLEEmb_Ico (h : n <= m) : (Ico a b).map (castLEEmb h) = Ico (castLE
 h a) (castLE h b)
参数：h : n <= m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Fin.castLEEmb_apply`：∀ {n m : ℕ} (h : n ≤ m) (i : Fin n), (Fin.castLEEmb
 h) i = Fin.castLE h i
· 使用定理 `Finset.coe_Ico`：coe_Ico (a b : α) : (Ico a b : Set α) = Set.Ico a b
· 使用定理 `Fin.image_castLE_Ico`：image_castLE_Ico (i j : Fin m) (h : m <= n) : cast
LE h '' Ico i j = Ico (castLE h i) (castLE h j)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_castLEEmb_Ico (h : n ≤ m) :
    (Ico a b).map (castLEEmb h) = Ico (castLE h a) (castLE h b) := by simp [← coe_inj]

@[simp]
/-
**Fin.map_castLEEmb_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_castLEEmb_Ioc (h : n <= m) : (Ioc a b).map (castLEEmb h) = Ioc (castLE
 h a) (castLE h b)
参数：h : n <= m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Fin.castLEEmb_apply`：∀ {n m : ℕ} (h : n ≤ m) (i : Fin n), (Fin.castLEEmb
 h) i = Fin.castLE h i
· 使用定理 `Finset.coe_Ioc`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrder α] (b a : α), ↑(Finset.Ioc b a) = Set.Ioc b a
· 使用定理 `Fin.image_castLE_Ioc`：image_castLE_Ioc (i j : Fin m) (h : m <= n) : cast
LE h '' Ioc i j = Ioc (castLE h i) (castLE h j)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_castLEEmb_Ioc (h : n ≤ m) :
    (Ioc a b).map (castLEEmb h) = Ioc (castLE h a) (castLE h b) := by simp [← coe_inj]

@[simp]
/-
**Fin.map_castLEEmb_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_castLEEmb_Ioo (h : n <= m) : (Ioo a b).map (castLEEmb h) = Ioo (castLE
 h a) (castLE h b)
参数：h : n <= m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Fin.castLEEmb_apply`：∀ {n m : ℕ} (h : n ≤ m) (i : Fin n), (Fin.castLEEmb
 h) i = Fin.castLE h i
· 使用定理 `Finset.coe_Ioo`：coe_Ioo (a b : α) : (Ioo a b : Set α) = Set.Ioo a b
· 使用定理 `Fin.image_castLE_Ioo`：image_castLE_Ioo (i j : Fin m) (h : m <= n) : cast
LE h '' Ioo i j = Ioo (castLE h i) (castLE h j)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_castLEEmb_Ioo (h : n ≤ m) :
    (Ioo a b).map (castLEEmb h) = Ioo (castLE h a) (castLE h b) := by simp [← coe_inj]

@[simp]
/-
**Fin.map_castLEEmb_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_castLEEmb_uIcc (h : n <= m) : (uIcc a b).map (castLEEmb h) = uIcc (cas
tLE h a) (castLE h b)
参数：h : n <= m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Fin.castLEEmb_apply`：∀ {n m : ℕ} (h : n ≤ m) (i : Fin n), (Fin.castLEEmb
 h) i = Fin.castLE h i
· 使用定理 `Finset.coe_uIcc`：coe_uIcc (a b : α) : (Finset.uIcc a b : Set α) = Set.uI
cc a b
· 使用定理 `Fin.image_castLE_uIcc`：image_castLE_uIcc (i j : Fin m) (h : m <= n) : ca
stLE h '' uIcc i j = uIcc (castLE h i) (castLE h j)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_castLEEmb_uIcc (h : n ≤ m) :
    (uIcc a b).map (castLEEmb h) = uIcc (castLE h a) (castLE h b) := by simp [← coe_inj]

@[simp]
/-
**Fin.map_castLEEmb_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_castLEEmb_Iic (h : n <= m) : (Iic a).map (castLEEmb h) = Iic (castLE h
 a)
参数：h : n <= m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Fin.castLEEmb_apply`：∀ {n m : ℕ} (h : n ≤ m) (i : Fin n), (Fin.castLEEmb
 h) i = Fin.castLE h i
· 使用定理 `Finset.coe_Iic`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] (a : α), ↑(Finset.Iic a) = Set.Iic a
· 使用定理 `Fin.image_castLE_Iic`：image_castLE_Iic (i : Fin m) (h : m <= n) : castLE
 h '' Iic i = Iic (castLE h i)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_castLEEmb_Iic (h : n ≤ m) :
    (Iic a).map (castLEEmb h) = Iic (castLE h a) := by simp [← coe_inj]

@[simp]
/-
**Fin.map_castLEEmb_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_castLEEmb_Iio (h : n <= m) : (Iio a).map (castLEEmb h) = Iio (castLE h
 a)
参数：h : n <= m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Fin.castLEEmb_apply`：∀ {n m : ℕ} (h : n ≤ m) (i : Fin n), (Fin.castLEEmb
 h) i = Fin.castLE h i
· 使用定理 `Finset.coe_Iio`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] (a : α), ↑(Finset.Iio a) = Set.Iio a
· 使用定理 `Fin.image_castLE_Iio`：image_castLE_Iio (i : Fin m) (h : m <= n) : castLE
 h '' Iio i = Iio (castLE h i)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_castLEEmb_Iio (h : n ≤ m) :
    (Iio a).map (castLEEmb h) = Iio (castLE h a) := by simp [← coe_inj]

end castLE

section castAdd

/-!
### Images under `Fin.castAdd`
-/

@[simp]
/-
**Fin.finsetImage_castAdd_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_castAdd_Icc (m) (i j : Fin n) : (Icc i j).image (castAdd m) = 
Icc (castAdd m i) (castAdd m j)
参数：m；i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.finsetImage_castLE_Icc`：finsetImage_castLE_Icc (h : n <= m) : (Icc a
 b).image (castLE h) = Icc (castLE h a) (castLE h b)
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k

--- 原说明 ---
### Images under `Fin.castAdd`
-/
theorem finsetImage_castAdd_Icc (m) (i j : Fin n) :
    (Icc i j).image (castAdd m) = Icc (castAdd m i) (castAdd m j) :=
  finsetImage_castLE_Icc ..

@[simp]
/-
**Fin.finsetImage_castAdd_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_castAdd_Ico (m) (i j : Fin n) : (Ico i j).image (castAdd m) = 
Ico (castAdd m i) (castAdd m j)
参数：m；i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.finsetImage_castLE_Ico`：finsetImage_castLE_Ico (h : n <= m) : (Ico a
 b).image (castLE h) = Ico (castLE h a) (castLE h b)
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
-/
theorem finsetImage_castAdd_Ico (m) (i j : Fin n) :
    (Ico i j).image (castAdd m) = Ico (castAdd m i) (castAdd m j) :=
  finsetImage_castLE_Ico ..

@[simp]
/-
**Fin.finsetImage_castAdd_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_castAdd_Ioc (m) (i j : Fin n) : (Ioc i j).image (castAdd m) = 
Ioc (castAdd m i) (castAdd m j)
参数：m；i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.finsetImage_castLE_Ioc`：finsetImage_castLE_Ioc (h : n <= m) : (Ioc a
 b).image (castLE h) = Ioc (castLE h a) (castLE h b)
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
-/
theorem finsetImage_castAdd_Ioc (m) (i j : Fin n) :
    (Ioc i j).image (castAdd m) = Ioc (castAdd m i) (castAdd m j) :=
  finsetImage_castLE_Ioc ..

@[simp]
/-
**Fin.finsetImage_castAdd_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_castAdd_Ioo (m) (i j : Fin n) : (Ioo i j).image (castAdd m) = 
Ioo (castAdd m i) (castAdd m j)
参数：m；i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.finsetImage_castLE_Ioo`：finsetImage_castLE_Ioo (h : n <= m) : (Ioo a
 b).image (castLE h) = Ioo (castLE h a) (castLE h b)
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
-/
theorem finsetImage_castAdd_Ioo (m) (i j : Fin n) :
    (Ioo i j).image (castAdd m) = Ioo (castAdd m i) (castAdd m j) :=
  finsetImage_castLE_Ioo ..

@[simp]
/-
**Fin.finsetImage_castAdd_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_castAdd_uIcc (m) (i j : Fin n) : (uIcc i j).image (castAdd m) 
= uIcc (castAdd m i) (castAdd m j)
参数：m；i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.finsetImage_castLE_uIcc`：finsetImage_castLE_uIcc (h : n <= m) : (uIc
c a b).image (castLE h) = uIcc (castLE h a) (castLE h b)
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
-/
theorem finsetImage_castAdd_uIcc (m) (i j : Fin n) :
    (uIcc i j).image (castAdd m) = uIcc (castAdd m i) (castAdd m j) :=
  finsetImage_castLE_uIcc ..

@[simp]
/-
**Fin.finsetImage_castAdd_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_castAdd_Ici (m) [NeZero m] (i : Fin n) : (Ici i).image (castAd
d m) = Ico (castAdd m i) (natAdd n 0)
参数：m；i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Finset.coe_Ici`：coe_Ici (a : α) : (Ici a : Set α) = Set.Ici a
· 使用定理 `Fin.image_castAdd_Ici`：image_castAdd_Ici (m) [NeZero m] (i : Fin n) : ca
stAdd m '' Ici i = Ico (castAdd m i) (natAdd n 0)
· 使用定理 `Finset.coe_Ico`：coe_Ico (a b : α) : (Ico a b : Set α) = Set.Ico a b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finsetImage_castAdd_Ici (m) [NeZero m] (i : Fin n) :
    (Ici i).image (castAdd m) = Ico (castAdd m i) (natAdd n 0) := by
  simp [← coe_inj]

@[simp]
/-
**Fin.finsetImage_castAdd_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_castAdd_Ioi (m) [NeZero m] (i : Fin n) : (Ioi i).image (castAd
d m) = Ioo (castAdd m i) (natAdd n 0)
参数：m；i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Finset.coe_Ioi`：coe_Ioi (a : α) : (Ioi a : Set α) = Set.Ioi a
· 使用定理 `Fin.image_castAdd_Ioi`：image_castAdd_Ioi (m) [NeZero m] (i : Fin n) : ca
stAdd m '' Ioi i = Ioo (castAdd m i) (natAdd n 0)
· 使用定理 `Finset.coe_Ioo`：coe_Ioo (a b : α) : (Ioo a b : Set α) = Set.Ioo a b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finsetImage_castAdd_Ioi (m) [NeZero m] (i : Fin n) :
    (Ioi i).image (castAdd m) = Ioo (castAdd m i) (natAdd n 0) := by
  simp [← coe_inj]

@[simp]
/-
**Fin.finsetImage_castAdd_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_castAdd_Iic (m) (i : Fin n) : (Iic i).image (castAdd m) = Iic 
(castAdd m i)
参数：m；i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.finsetImage_castLE_Iic`：finsetImage_castLE_Iic (h : n <= m) : (Iic a
).image (castLE h) = Iic (castLE h a)
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
-/
theorem finsetImage_castAdd_Iic (m) (i : Fin n) : (Iic i).image (castAdd m) = Iic (castAdd m i) :=
  finsetImage_castLE_Iic i _

@[simp]
/-
**Fin.finsetImage_castAdd_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_castAdd_Iio (m) (i : Fin n) : (Iio i).image (castAdd m) = Iio 
(castAdd m i)
参数：m；i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.finsetImage_castLE_Iio`：finsetImage_castLE_Iio (h : n <= m) : (Iio a
).image (castLE h) = Iio (castLE h a)
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
-/
theorem finsetImage_castAdd_Iio (m) (i : Fin n) : (Iio i).image (castAdd m) = Iio (castAdd m i) :=
  finsetImage_castLE_Iio ..

/-!
### `Finset.map` along `Fin.castAddEmb`
-/

@[simp]
/-
**Fin.map_castAddEmb_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_castAddEmb_Icc (m) (i j : Fin n) : (Icc i j).map (castAddEmb m) = Icc 
(castAdd m i) (castAdd m j)
参数：m；i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.map_castLEEmb_Icc`：map_castLEEmb_Icc (h : n <= m) : (Icc a b).map (c
astLEEmb h) = Icc (castLE h a) (castLE h b)
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k

--- 原说明 ---
### `Finset.map` along `Fin.castAddEmb`
-/
theorem map_castAddEmb_Icc (m) (i j : Fin n) :
    (Icc i j).map (castAddEmb m) = Icc (castAdd m i) (castAdd m j) :=
  map_castLEEmb_Icc ..

@[simp]
/-
**Fin.map_castAddEmb_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_castAddEmb_Ico (m) (i j : Fin n) : (Ico i j).map (castAddEmb m) = Ico 
(castAdd m i) (castAdd m j)
参数：m；i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.map_castLEEmb_Ico`：map_castLEEmb_Ico (h : n <= m) : (Ico a b).map (c
astLEEmb h) = Ico (castLE h a) (castLE h b)
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
-/
theorem map_castAddEmb_Ico (m) (i j : Fin n) :
    (Ico i j).map (castAddEmb m) = Ico (castAdd m i) (castAdd m j) :=
  map_castLEEmb_Ico ..

@[simp]
/-
**Fin.map_castAddEmb_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_castAddEmb_Ioc (m) (i j : Fin n) : (Ioc i j).map (castAddEmb m) = Ioc 
(castAdd m i) (castAdd m j)
参数：m；i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.map_castLEEmb_Ioc`：map_castLEEmb_Ioc (h : n <= m) : (Ioc a b).map (c
astLEEmb h) = Ioc (castLE h a) (castLE h b)
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
-/
theorem map_castAddEmb_Ioc (m) (i j : Fin n) :
    (Ioc i j).map (castAddEmb m) = Ioc (castAdd m i) (castAdd m j) :=
  map_castLEEmb_Ioc ..

@[simp]
/-
**Fin.map_castAddEmb_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_castAddEmb_Ioo (m) (i j : Fin n) : (Ioo i j).map (castAddEmb m) = Ioo 
(castAdd m i) (castAdd m j)
参数：m；i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.map_castLEEmb_Ioo`：map_castLEEmb_Ioo (h : n <= m) : (Ioo a b).map (c
astLEEmb h) = Ioo (castLE h a) (castLE h b)
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
-/
theorem map_castAddEmb_Ioo (m) (i j : Fin n) :
    (Ioo i j).map (castAddEmb m) = Ioo (castAdd m i) (castAdd m j) :=
  map_castLEEmb_Ioo ..

@[simp]
/-
**Fin.map_castAddEmb_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_castAddEmb_uIcc (m) (i j : Fin n) : (uIcc i j).map (castAddEmb m) = uI
cc (castAdd m i) (castAdd m j)
参数：m；i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.map_castLEEmb_uIcc`：map_castLEEmb_uIcc (h : n <= m) : (uIcc a b).map
 (castLEEmb h) = uIcc (castLE h a) (castLE h b)
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
-/
theorem map_castAddEmb_uIcc (m) (i j : Fin n) :
    (uIcc i j).map (castAddEmb m) = uIcc (castAdd m i) (castAdd m j) :=
  map_castLEEmb_uIcc ..

@[simp]
/-
**Fin.map_castAddEmb_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_castAddEmb_Ici (m) [NeZero m] (i : Fin n) : (Ici i).map (castAddEmb m)
 = Ico (castAdd m i) (natAdd n 0)
参数：m；i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.map_eq_image`：map_eq_image (f : α ↪ β) (s : Finset α) : s.map f =
 s.image f
· 使用定理 `Fin.finsetImage_castAdd_Ici`：finsetImage_castAdd_Ici (m) [NeZero m] (i :
 Fin n) : (Ici i).image (castAdd m) = Ico (castAdd m i) (natAdd n 0)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_castAddEmb_Ici (m) [NeZero m] (i : Fin n) :
    (Ici i).map (castAddEmb m) = Ico (castAdd m i) (natAdd n 0) := by
  simp [map_eq_image]

@[simp]
/-
**Fin.map_castAddEmb_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_castAddEmb_Ioi (m) [NeZero m] (i : Fin n) : (Ioi i).map (castAddEmb m)
 = Ioo (castAdd m i) (natAdd n 0)
参数：m；i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Finset.coe_Ioi`：coe_Ioi (a : α) : (Ioi a : Set α) = Set.Ioi a
· 使用定理 `Fin.image_castAdd_Ioi`：image_castAdd_Ioi (m) [NeZero m] (i : Fin n) : ca
stAdd m '' Ioi i = Ioo (castAdd m i) (natAdd n 0)
· 使用定理 `Finset.coe_Ioo`：coe_Ioo (a b : α) : (Ioo a b : Set α) = Set.Ioo a b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_castAddEmb_Ioi (m) [NeZero m] (i : Fin n) :
    (Ioi i).map (castAddEmb m) = Ioo (castAdd m i) (natAdd n 0) := by
  simp [← coe_inj]

@[simp]
/-
**Fin.map_castAddEmb_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_castAddEmb_Iic (m) (i : Fin n) : (Iic i).map (castAddEmb m) = Iic (cas
tAdd m i)
参数：m；i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.map_castLEEmb_Iic`：map_castLEEmb_Iic (h : n <= m) : (Iic a).map (cas
tLEEmb h) = Iic (castLE h a)
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
-/
theorem map_castAddEmb_Iic (m) (i : Fin n) : (Iic i).map (castAddEmb m) = Iic (castAdd m i) :=
  map_castLEEmb_Iic i _

@[simp]
/-
**Fin.map_castAddEmb_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_castAddEmb_Iio (m) (i : Fin n) : (Iio i).map (castAddEmb m) = Iio (cas
tAdd m i)
参数：m；i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.map_castLEEmb_Iio`：map_castLEEmb_Iio (h : n <= m) : (Iio a).map (cas
tLEEmb h) = Iio (castLE h a)
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
-/
theorem map_castAddEmb_Iio (m) (i : Fin n) : (Iio i).map (castAddEmb m) = Iio (castAdd m i) :=
  map_castLEEmb_Iio ..

end castAdd

section cast

/-!
### Images under `Fin.cast`
-/

@[simp]
/-
**Fin.finsetImage_cast_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_cast_Icc (h : n = m) (i j : Fin n) : (Icc i j).image (.cast h)
 = Icc (i.cast h) (j.cast h)
参数：h : n = m；i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Finset.coe_Icc`：coe_Icc (a b : α) : (Icc a b : Set α) = Set.Icc a b
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Fin.image_cast_fun`：image_cast_fun (h : m = n) : image (Fin.cast h) = pr
eimage (Fin.cast h.symm)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
### Images under `Fin.cast`
-/
theorem finsetImage_cast_Icc (h : n = m) (i j : Fin n) :
    (Icc i j).image (.cast h) = Icc (i.cast h) (j.cast h) := by
  simp [← coe_inj]

@[simp]
/-
**Fin.finsetImage_cast_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_cast_Ico (h : n = m) (i j : Fin n) : (Ico i j).image (.cast h)
 = Ico (i.cast h) (j.cast h)
参数：h : n = m；i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Finset.coe_Ico`：coe_Ico (a b : α) : (Ico a b : Set α) = Set.Ico a b
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Fin.image_cast_fun`：image_cast_fun (h : m = n) : image (Fin.cast h) = pr
eimage (Fin.cast h.symm)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finsetImage_cast_Ico (h : n = m) (i j : Fin n) :
    (Ico i j).image (.cast h) = Ico (i.cast h) (j.cast h) := by
  simp [← coe_inj]

@[simp]
/-
**Fin.finsetImage_cast_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_cast_Ioc (h : n = m) (i j : Fin n) : (Ioc i j).image (.cast h)
 = Ioc (i.cast h) (j.cast h)
参数：h : n = m；i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Finset.coe_Ioc`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrder α] (b a : α), ↑(Finset.Ioc b a) = Set.Ioc b a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Fin.image_cast_fun`：image_cast_fun (h : m = n) : image (Fin.cast h) = pr
eimage (Fin.cast h.symm)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finsetImage_cast_Ioc (h : n = m) (i j : Fin n) :
    (Ioc i j).image (.cast h) = Ioc (i.cast h) (j.cast h) := by
  simp [← coe_inj]

@[simp]
/-
**Fin.finsetImage_cast_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_cast_Ioo (h : n = m) (i j : Fin n) : (Ioo i j).image (.cast h)
 = Ioo (i.cast h) (j.cast h)
参数：h : n = m；i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Finset.coe_Ioo`：coe_Ioo (a b : α) : (Ioo a b : Set α) = Set.Ioo a b
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Fin.image_cast_fun`：image_cast_fun (h : m = n) : image (Fin.cast h) = pr
eimage (Fin.cast h.symm)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finsetImage_cast_Ioo (h : n = m) (i j : Fin n) :
    (Ioo i j).image (.cast h) = Ioo (i.cast h) (j.cast h) := by
  simp [← coe_inj]

@[simp]
/-
**Fin.finsetImage_cast_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_cast_uIcc (h : n = m) (i j : Fin n) : (uIcc i j).image (.cast 
h) = uIcc (i.cast h) (j.cast h)
参数：h : n = m；i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Finset.coe_uIcc`：coe_uIcc (a b : α) : (Finset.uIcc a b : Set α) = Set.uI
cc a b
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Fin.image_cast_fun`：image_cast_fun (h : m = n) : image (Fin.cast h) = pr
eimage (Fin.cast h.symm)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finsetImage_cast_uIcc (h : n = m) (i j : Fin n) :
    (uIcc i j).image (.cast h) = uIcc (i.cast h) (j.cast h) := by
  simp [← coe_inj]

@[simp]
/-
**Fin.finsetImage_cast_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_cast_Ici (h : n = m) (i : Fin n) : (Ici i).image (.cast h) = I
ci (i.cast h)
参数：h : n = m；i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Finset.coe_Ici`：coe_Ici (a : α) : (Ici a : Set α) = Set.Ici a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Fin.image_cast_fun`：image_cast_fun (h : m = n) : image (Fin.cast h) = pr
eimage (Fin.cast h.symm)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finsetImage_cast_Ici (h : n = m) (i : Fin n) :
    (Ici i).image (.cast h) = Ici (i.cast h) := by
  simp [← coe_inj]

@[simp]
/-
**Fin.finsetImage_cast_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_cast_Ioi (h : n = m) (i : Fin n) : (Ioi i).image (.cast h) = I
oi (i.cast h)
参数：h : n = m；i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Finset.coe_Ioi`：coe_Ioi (a : α) : (Ioi a : Set α) = Set.Ioi a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Fin.image_cast_fun`：image_cast_fun (h : m = n) : image (Fin.cast h) = pr
eimage (Fin.cast h.symm)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finsetImage_cast_Ioi (h : n = m) (i : Fin n) :
    (Ioi i).image (.cast h) = Ioi (i.cast h) := by
  simp [← coe_inj]

@[simp]
/-
**Fin.finsetImage_cast_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_cast_Iic (h : n = m) (i : Fin n) : (Iic i).image (.cast h) = I
ic (i.cast h)
参数：h : n = m；i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Finset.coe_Iic`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] (a : α), ↑(Finset.Iic a) = Set.Iic a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Fin.image_cast_fun`：image_cast_fun (h : m = n) : image (Fin.cast h) = pr
eimage (Fin.cast h.symm)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finsetImage_cast_Iic (h : n = m) (i : Fin n) :
    (Iic i).image (.cast h) = Iic (i.cast h) := by
  simp [← coe_inj]

@[simp]
/-
**Fin.finsetImage_cast_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_cast_Iio (h : n = m) (i : Fin n) : (Iio i).image (.cast h) = I
io (i.cast h)
参数：h : n = m；i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Finset.coe_Iio`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] (a : α), ↑(Finset.Iio a) = Set.Iio a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Fin.image_cast_fun`：image_cast_fun (h : m = n) : image (Fin.cast h) = pr
eimage (Fin.cast h.symm)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finsetImage_cast_Iio (h : n = m) (i : Fin n) :
    (Iio i).image (.cast h) = Iio (i.cast h) := by
  simp [← coe_inj]

/-!
### `Finset.map` along `finCongr`
-/

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Fin.map_finCongr_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_finCongr_Icc (h : n = m) (i j : Fin n) : (Icc i j).map (finCongr h).to
Embedding = Icc (i.cast h) (j.cast h)
参数：h : n = m；i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `finCongr_apply`：∀ {n m : ℕ} (eq : n = m) (i : Fin n), (finCongr eq) i = 
Fin.cast eq i
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Fin.image_cast_fun`：image_cast_fun (h : m = n) : image (Fin.cast h) = pr
eimage (Fin.cast h.symm)
· 使用定理 `Finset.coe_Icc`：coe_Icc (a b : α) : (Icc a b : Set α) = Set.Icc a b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
### `Finset.map` along `finCongr`
-/
theorem map_finCongr_Icc (h : n = m) (i j : Fin n) :
    (Icc i j).map (finCongr h).toEmbedding = Icc (i.cast h) (j.cast h) := by
  simp [← coe_inj]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Fin.map_finCongr_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_finCongr_Ico (h : n = m) (i j : Fin n) : (Ico i j).map (finCongr h).to
Embedding = Ico (i.cast h) (j.cast h)
参数：h : n = m；i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `finCongr_apply`：∀ {n m : ℕ} (eq : n = m) (i : Fin n), (finCongr eq) i = 
Fin.cast eq i
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Fin.image_cast_fun`：image_cast_fun (h : m = n) : image (Fin.cast h) = pr
eimage (Fin.cast h.symm)
· 使用定理 `Finset.coe_Ico`：coe_Ico (a b : α) : (Ico a b : Set α) = Set.Ico a b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_finCongr_Ico (h : n = m) (i j : Fin n) :
    (Ico i j).map (finCongr h).toEmbedding = Ico (i.cast h) (j.cast h) := by
  simp [← coe_inj]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Fin.map_finCongr_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_finCongr_Ioc (h : n = m) (i j : Fin n) : (Ioc i j).map (finCongr h).to
Embedding = Ioc (i.cast h) (j.cast h)
参数：h : n = m；i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `finCongr_apply`：∀ {n m : ℕ} (eq : n = m) (i : Fin n), (finCongr eq) i = 
Fin.cast eq i
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Fin.image_cast_fun`：image_cast_fun (h : m = n) : image (Fin.cast h) = pr
eimage (Fin.cast h.symm)
· 使用定理 `Finset.coe_Ioc`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrder α] (b a : α), ↑(Finset.Ioc b a) = Set.Ioc b a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_finCongr_Ioc (h : n = m) (i j : Fin n) :
    (Ioc i j).map (finCongr h).toEmbedding = Ioc (i.cast h) (j.cast h) := by
  simp [← coe_inj]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Fin.map_finCongr_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_finCongr_Ioo (h : n = m) (i j : Fin n) : (Ioo i j).map (finCongr h).to
Embedding = Ioo (i.cast h) (j.cast h)
参数：h : n = m；i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `finCongr_apply`：∀ {n m : ℕ} (eq : n = m) (i : Fin n), (finCongr eq) i = 
Fin.cast eq i
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Fin.image_cast_fun`：image_cast_fun (h : m = n) : image (Fin.cast h) = pr
eimage (Fin.cast h.symm)
· 使用定理 `Finset.coe_Ioo`：coe_Ioo (a b : α) : (Ioo a b : Set α) = Set.Ioo a b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_finCongr_Ioo (h : n = m) (i j : Fin n) :
    (Ioo i j).map (finCongr h).toEmbedding = Ioo (i.cast h) (j.cast h) := by
  simp [← coe_inj]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Fin.map_finCongr_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_finCongr_uIcc (h : n = m) (i j : Fin n) : (uIcc i j).map (finCongr h).
toEmbedding = uIcc (i.cast h) (j.cast h)
参数：h : n = m；i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `finCongr_apply`：∀ {n m : ℕ} (eq : n = m) (i : Fin n), (finCongr eq) i = 
Fin.cast eq i
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Fin.image_cast_fun`：image_cast_fun (h : m = n) : image (Fin.cast h) = pr
eimage (Fin.cast h.symm)
· 使用定理 `Finset.coe_uIcc`：coe_uIcc (a b : α) : (Finset.uIcc a b : Set α) = Set.uI
cc a b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_finCongr_uIcc (h : n = m) (i j : Fin n) :
    (uIcc i j).map (finCongr h).toEmbedding = uIcc (i.cast h) (j.cast h) := by
  simp [← coe_inj]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Fin.map_finCongr_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_finCongr_Ici (h : n = m) (i : Fin n) : (Ici i).map (finCongr h).toEmbe
dding = Ici (i.cast h)
参数：h : n = m；i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `finCongr_apply`：∀ {n m : ℕ} (eq : n = m) (i : Fin n), (finCongr eq) i = 
Fin.cast eq i
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Fin.image_cast_fun`：image_cast_fun (h : m = n) : image (Fin.cast h) = pr
eimage (Fin.cast h.symm)
· 使用定理 `Finset.coe_Ici`：coe_Ici (a : α) : (Ici a : Set α) = Set.Ici a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_finCongr_Ici (h : n = m) (i : Fin n) :
    (Ici i).map (finCongr h).toEmbedding = Ici (i.cast h) := by
  simp [← coe_inj]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Fin.map_finCongr_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_finCongr_Ioi (h : n = m) (i : Fin n) : (Ioi i).map (finCongr h).toEmbe
dding = Ioi (i.cast h)
参数：h : n = m；i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `finCongr_apply`：∀ {n m : ℕ} (eq : n = m) (i : Fin n), (finCongr eq) i = 
Fin.cast eq i
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Fin.image_cast_fun`：image_cast_fun (h : m = n) : image (Fin.cast h) = pr
eimage (Fin.cast h.symm)
· 使用定理 `Finset.coe_Ioi`：coe_Ioi (a : α) : (Ioi a : Set α) = Set.Ioi a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_finCongr_Ioi (h : n = m) (i : Fin n) :
    (Ioi i).map (finCongr h).toEmbedding = Ioi (i.cast h) := by
  simp [← coe_inj]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Fin.map_finCongr_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_finCongr_Iic (h : n = m) (i : Fin n) : (Iic i).map (finCongr h).toEmbe
dding = Iic (i.cast h)
参数：h : n = m；i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `finCongr_apply`：∀ {n m : ℕ} (eq : n = m) (i : Fin n), (finCongr eq) i = 
Fin.cast eq i
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Fin.image_cast_fun`：image_cast_fun (h : m = n) : image (Fin.cast h) = pr
eimage (Fin.cast h.symm)
· 使用定理 `Finset.coe_Iic`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] (a : α), ↑(Finset.Iic a) = Set.Iic a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_finCongr_Iic (h : n = m) (i : Fin n) :
    (Iic i).map (finCongr h).toEmbedding = Iic (i.cast h) := by
  simp [← coe_inj]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Fin.map_finCongr_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_finCongr_Iio (h : n = m) (i : Fin n) : (Iio i).map (finCongr h).toEmbe
dding = Iio (i.cast h)
参数：h : n = m；i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `finCongr_apply`：∀ {n m : ℕ} (eq : n = m) (i : Fin n), (finCongr eq) i = 
Fin.cast eq i
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Fin.image_cast_fun`：image_cast_fun (h : m = n) : image (Fin.cast h) = pr
eimage (Fin.cast h.symm)
· 使用定理 `Finset.coe_Iio`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] (a : α), ↑(Finset.Iio a) = Set.Iio a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_finCongr_Iio (h : n = m) (i : Fin n) :
    (Iio i).map (finCongr h).toEmbedding = Iio (i.cast h) := by
  simp [← coe_inj]

end cast

section castSucc

/-!
### Images under `Fin.castSucc`
-/

@[simp]
/-
**Fin.finsetImage_castSucc_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_castSucc_Icc (i j : Fin n) : (Icc i j).image castSucc = Icc i.
castSucc j.castSucc
参数：i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.finsetImage_castAdd_Icc`：finsetImage_castAdd_Icc (m) (i j : Fin n) :
 (Icc i j).image (castAdd m) = Icc (castAdd m i) (castAdd m j)

--- 原说明 ---
### Images under `Fin.castSucc`
-/
theorem finsetImage_castSucc_Icc (i j : Fin n) :
    (Icc i j).image castSucc = Icc i.castSucc j.castSucc :=
  finsetImage_castAdd_Icc ..

@[simp]
/-
**Fin.finsetImage_castSucc_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_castSucc_Ico (i j : Fin n) : (Ico i j).image castSucc = Ico i.
castSucc j.castSucc
参数：i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.finsetImage_castAdd_Ico`：finsetImage_castAdd_Ico (m) (i j : Fin n) :
 (Ico i j).image (castAdd m) = Ico (castAdd m i) (castAdd m j)
-/
theorem finsetImage_castSucc_Ico (i j : Fin n) :
    (Ico i j).image castSucc = Ico i.castSucc j.castSucc :=
  finsetImage_castAdd_Ico ..

@[simp]
/-
**Fin.finsetImage_castSucc_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_castSucc_Ioc (i j : Fin n) : (Ioc i j).image castSucc = Ioc i.
castSucc j.castSucc
参数：i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.finsetImage_castAdd_Ioc`：finsetImage_castAdd_Ioc (m) (i j : Fin n) :
 (Ioc i j).image (castAdd m) = Ioc (castAdd m i) (castAdd m j)
-/
theorem finsetImage_castSucc_Ioc (i j : Fin n) :
    (Ioc i j).image castSucc = Ioc i.castSucc j.castSucc :=
  finsetImage_castAdd_Ioc ..

@[simp]
/-
**Fin.finsetImage_castSucc_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_castSucc_Ioo (i j : Fin n) : (Ioo i j).image castSucc = Ioo i.
castSucc j.castSucc
参数：i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.finsetImage_castAdd_Ioo`：finsetImage_castAdd_Ioo (m) (i j : Fin n) :
 (Ioo i j).image (castAdd m) = Ioo (castAdd m i) (castAdd m j)
-/
theorem finsetImage_castSucc_Ioo (i j : Fin n) :
    (Ioo i j).image castSucc = Ioo i.castSucc j.castSucc :=
  finsetImage_castAdd_Ioo ..

@[simp]
/-
**Fin.finsetImage_castSucc_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_castSucc_uIcc (i j : Fin n) : (uIcc i j).image castSucc = uIcc
 i.castSucc j.castSucc
参数：i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.finsetImage_castAdd_uIcc`：finsetImage_castAdd_uIcc (m) (i j : Fin n)
 : (uIcc i j).image (castAdd m) = uIcc (castAdd m i) (castAdd m j)
-/
theorem finsetImage_castSucc_uIcc (i j : Fin n) :
    (uIcc i j).image castSucc = uIcc i.castSucc j.castSucc :=
  finsetImage_castAdd_uIcc ..

@[simp]
/-
**Fin.finsetImage_castSucc_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_castSucc_Ici (i : Fin n) : (Ici i).image castSucc = Ico i.cast
Succ (.last n)
参数：i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.finsetImage_castAdd_Ici`：finsetImage_castAdd_Ici (m) [NeZero m] (i :
 Fin n) : (Ici i).image (castAdd m) = Ico (castAdd m i) (natAdd n 0)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem finsetImage_castSucc_Ici (i : Fin n) : (Ici i).image castSucc = Ico i.castSucc (.last n) :=
  finsetImage_castAdd_Ici ..

@[simp]
/-
**Fin.finsetImage_castSucc_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_castSucc_Ioi (i : Fin n) : (Ioi i).image castSucc = Ioo i.cast
Succ (.last n)
参数：i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.finsetImage_castAdd_Ioi`：finsetImage_castAdd_Ioi (m) [NeZero m] (i :
 Fin n) : (Ioi i).image (castAdd m) = Ioo (castAdd m i) (natAdd n 0)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem finsetImage_castSucc_Ioi (i : Fin n) : (Ioi i).image castSucc = Ioo i.castSucc (.last n) :=
  finsetImage_castAdd_Ioi ..

@[simp]
/-
**Fin.finsetImage_castSucc_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_castSucc_Iic (i : Fin n) : (Iic i).image castSucc = Iic i.cast
Succ
参数：i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.finsetImage_castAdd_Iic`：finsetImage_castAdd_Iic (m) (i : Fin n) : (
Iic i).image (castAdd m) = Iic (castAdd m i)
-/
theorem finsetImage_castSucc_Iic (i : Fin n) : (Iic i).image castSucc = Iic i.castSucc :=
  finsetImage_castAdd_Iic ..

@[simp]
/-
**Fin.finsetImage_castSucc_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_castSucc_Iio (i : Fin n) : (Iio i).image castSucc = Iio i.cast
Succ
参数：i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.finsetImage_castAdd_Iio`：finsetImage_castAdd_Iio (m) (i : Fin n) : (
Iio i).image (castAdd m) = Iio (castAdd m i)
-/
theorem finsetImage_castSucc_Iio (i : Fin n) : (Iio i).image castSucc = Iio i.castSucc :=
  finsetImage_castAdd_Iio ..

/-!
### `Finset.map` along `Fin.castSuccEmb`
-/

@[simp]
/-
**Fin.map_castSuccEmb_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_castSuccEmb_Icc (i j : Fin n) : (Icc i j).map castSuccEmb = Icc i.cast
Succ j.castSucc
参数：i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.map_castAddEmb_Icc`：map_castAddEmb_Icc (m) (i j : Fin n) : (Icc i j)
.map (castAddEmb m) = Icc (castAdd m i) (castAdd m j)

--- 原说明 ---
### `Finset.map` along `Fin.castSuccEmb`
-/
theorem map_castSuccEmb_Icc (i j : Fin n) :
    (Icc i j).map castSuccEmb = Icc i.castSucc j.castSucc :=
  map_castAddEmb_Icc ..

@[simp]
/-
**Fin.map_castSuccEmb_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_castSuccEmb_Ico (i j : Fin n) : (Ico i j).map castSuccEmb = Ico i.cast
Succ j.castSucc
参数：i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.map_castAddEmb_Ico`：map_castAddEmb_Ico (m) (i j : Fin n) : (Ico i j)
.map (castAddEmb m) = Ico (castAdd m i) (castAdd m j)
-/
theorem map_castSuccEmb_Ico (i j : Fin n) :
    (Ico i j).map castSuccEmb = Ico i.castSucc j.castSucc :=
  map_castAddEmb_Ico ..

@[simp]
/-
**Fin.map_castSuccEmb_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_castSuccEmb_Ioc (i j : Fin n) : (Ioc i j).map castSuccEmb = Ioc i.cast
Succ j.castSucc
参数：i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.map_castAddEmb_Ioc`：map_castAddEmb_Ioc (m) (i j : Fin n) : (Ioc i j)
.map (castAddEmb m) = Ioc (castAdd m i) (castAdd m j)
-/
theorem map_castSuccEmb_Ioc (i j : Fin n) :
    (Ioc i j).map castSuccEmb = Ioc i.castSucc j.castSucc :=
  map_castAddEmb_Ioc ..

@[simp]
/-
**Fin.map_castSuccEmb_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_castSuccEmb_Ioo (i j : Fin n) : (Ioo i j).map castSuccEmb = Ioo i.cast
Succ j.castSucc
参数：i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.map_castAddEmb_Ioo`：map_castAddEmb_Ioo (m) (i j : Fin n) : (Ioo i j)
.map (castAddEmb m) = Ioo (castAdd m i) (castAdd m j)
-/
theorem map_castSuccEmb_Ioo (i j : Fin n) :
    (Ioo i j).map castSuccEmb = Ioo i.castSucc j.castSucc :=
  map_castAddEmb_Ioo ..

@[simp]
/-
**Fin.map_castSuccEmb_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_castSuccEmb_uIcc (i j : Fin n) : (uIcc i j).map castSuccEmb = uIcc i.c
astSucc j.castSucc
参数：i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.map_castAddEmb_uIcc`：map_castAddEmb_uIcc (m) (i j : Fin n) : (uIcc i
 j).map (castAddEmb m) = uIcc (castAdd m i) (castAdd m j)
-/
theorem map_castSuccEmb_uIcc (i j : Fin n) :
    (uIcc i j).map castSuccEmb = uIcc i.castSucc j.castSucc :=
  map_castAddEmb_uIcc ..

@[simp]
/-
**Fin.map_castSuccEmb_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_castSuccEmb_Ici (i : Fin n) : (Ici i).map castSuccEmb = Ico i.castSucc
 (.last n)
参数：i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.map_castAddEmb_Ici`：map_castAddEmb_Ici (m) [NeZero m] (i : Fin n) : 
(Ici i).map (castAddEmb m) = Ico (castAdd m i) (natAdd n 0)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem map_castSuccEmb_Ici (i : Fin n) : (Ici i).map castSuccEmb = Ico i.castSucc (.last n) :=
  map_castAddEmb_Ici ..

@[simp]
/-
**Fin.map_castSuccEmb_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_castSuccEmb_Ioi (i : Fin n) : (Ioi i).map castSuccEmb = Ioo i.castSucc
 (.last n)
参数：i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.map_castAddEmb_Ioi`：map_castAddEmb_Ioi (m) [NeZero m] (i : Fin n) : 
(Ioi i).map (castAddEmb m) = Ioo (castAdd m i) (natAdd n 0)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem map_castSuccEmb_Ioi (i : Fin n) : (Ioi i).map castSuccEmb = Ioo i.castSucc (.last n) :=
  map_castAddEmb_Ioi ..

@[simp]
/-
**Fin.map_castSuccEmb_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_castSuccEmb_Iic (i : Fin n) : (Iic i).map castSuccEmb = Iic i.castSucc
参数：i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.map_castAddEmb_Iic`：map_castAddEmb_Iic (m) (i : Fin n) : (Iic i).map
 (castAddEmb m) = Iic (castAdd m i)
-/
theorem map_castSuccEmb_Iic (i : Fin n) : (Iic i).map castSuccEmb = Iic i.castSucc :=
  map_castAddEmb_Iic ..

@[simp]
/-
**Fin.map_castSuccEmb_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_castSuccEmb_Iio (i : Fin n) : (Iio i).map castSuccEmb = Iio i.castSucc
参数：i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.map_castAddEmb_Iio`：map_castAddEmb_Iio (m) (i : Fin n) : (Iio i).map
 (castAddEmb m) = Iio (castAdd m i)
-/
theorem map_castSuccEmb_Iio (i : Fin n) : (Iio i).map castSuccEmb = Iio i.castSucc :=
  map_castAddEmb_Iio ..

end castSucc

section natAdd

/-!
### Images under `Fin.natAdd`
-/

@[simp]
/-
**Fin.finsetImage_natAdd_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_natAdd_Icc (m) (i j : Fin n) : (Icc i j).image (natAdd m) = Ic
c (natAdd m i) (natAdd m j)
参数：m；i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Finset.coe_Icc`：coe_Icc (a b : α) : (Icc a b : Set α) = Set.Icc a b
· 使用定理 `Fin.image_natAdd_Icc`：image_natAdd_Icc (m) (i j : Fin n) : natAdd m '' I
cc i j = Icc (natAdd m i) (natAdd m j)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
### Images under `Fin.natAdd`
-/
theorem finsetImage_natAdd_Icc (m) (i j : Fin n) :
    (Icc i j).image (natAdd m) = Icc (natAdd m i) (natAdd m j) := by
  simp [← coe_inj]

@[simp]
/-
**Fin.finsetImage_natAdd_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_natAdd_Ico (m) (i j : Fin n) : (Ico i j).image (natAdd m) = Ic
o (natAdd m i) (natAdd m j)
参数：m；i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Finset.coe_Ico`：coe_Ico (a b : α) : (Ico a b : Set α) = Set.Ico a b
· 使用定理 `Fin.image_natAdd_Ico`：image_natAdd_Ico (m) (i j : Fin n) : natAdd m '' I
co i j = Ico (natAdd m i) (natAdd m j)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finsetImage_natAdd_Ico (m) (i j : Fin n) :
    (Ico i j).image (natAdd m) = Ico (natAdd m i) (natAdd m j) := by
  simp [← coe_inj]

@[simp]
/-
**Fin.finsetImage_natAdd_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_natAdd_Ioc (m) (i j : Fin n) : (Ioc i j).image (natAdd m) = Io
c (natAdd m i) (natAdd m j)
参数：m；i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Finset.coe_Ioc`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrder α] (b a : α), ↑(Finset.Ioc b a) = Set.Ioc b a
· 使用定理 `Fin.image_natAdd_Ioc`：image_natAdd_Ioc (m) (i j : Fin n) : natAdd m '' I
oc i j = Ioc (natAdd m i) (natAdd m j)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finsetImage_natAdd_Ioc (m) (i j : Fin n) :
    (Ioc i j).image (natAdd m) = Ioc (natAdd m i) (natAdd m j) := by
  simp [← coe_inj]

@[simp]
/-
**Fin.finsetImage_natAdd_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_natAdd_Ioo (m) (i j : Fin n) : (Ioo i j).image (natAdd m) = Io
o (natAdd m i) (natAdd m j)
参数：m；i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Finset.coe_Ioo`：coe_Ioo (a b : α) : (Ioo a b : Set α) = Set.Ioo a b
· 使用定理 `Fin.image_natAdd_Ioo`：image_natAdd_Ioo (m) (i j : Fin n) : natAdd m '' I
oo i j = Ioo (natAdd m i) (natAdd m j)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finsetImage_natAdd_Ioo (m) (i j : Fin n) :
    (Ioo i j).image (natAdd m) = Ioo (natAdd m i) (natAdd m j) := by
  simp [← coe_inj]

@[simp]
/-
**Fin.finsetImage_natAdd_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_natAdd_uIcc (m) (i j : Fin n) : (uIcc i j).image (natAdd m) = 
uIcc (natAdd m i) (natAdd m j)
参数：m；i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Finset.coe_uIcc`：coe_uIcc (a b : α) : (Finset.uIcc a b : Set α) = Set.uI
cc a b
· 使用定理 `Fin.image_natAdd_uIcc`：image_natAdd_uIcc (m) (i j : Fin n) : natAdd m ''
 uIcc i j = uIcc (natAdd m i) (natAdd m j)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finsetImage_natAdd_uIcc (m) (i j : Fin n) :
    (uIcc i j).image (natAdd m) = uIcc (natAdd m i) (natAdd m j) := by
  simp [← coe_inj]

@[simp]
/-
**Fin.finsetImage_natAdd_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_natAdd_Ici (m) (i : Fin n) : (Ici i).image (natAdd m) = Ici (n
atAdd m i)
参数：m；i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Finset.coe_Ici`：coe_Ici (a : α) : (Ici a : Set α) = Set.Ici a
· 使用定理 `Fin.image_natAdd_Ici`：image_natAdd_Ici (m) (i : Fin n) : natAdd m '' Ici
 i = Ici (natAdd m i)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finsetImage_natAdd_Ici (m) (i : Fin n) : (Ici i).image (natAdd m) = Ici (natAdd m i) := by
  simp [← coe_inj]

@[simp]
/-
**Fin.finsetImage_natAdd_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_natAdd_Ioi (m) (i : Fin n) : (Ioi i).image (natAdd m) = Ioi (n
atAdd m i)
参数：m；i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Finset.coe_Ioi`：coe_Ioi (a : α) : (Ioi a : Set α) = Set.Ioi a
· 使用定理 `Fin.image_natAdd_Ioi`：image_natAdd_Ioi (m) (i : Fin n) : natAdd m '' Ioi
 i = Ioi (natAdd m i)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finsetImage_natAdd_Ioi (m) (i : Fin n) : (Ioi i).image (natAdd m) = Ioi (natAdd m i) := by
  simp [← coe_inj]

/-!
### `Finset.map` along `Fin.natAddEmb`
-/

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Fin.map_natAddEmb_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_natAddEmb_Icc (m) (i j : Fin n) : (Icc i j).map (natAddEmb m) = Icc (n
atAdd m i) (natAdd m j)
参数：m；i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Fin.natAddEmb_apply`：∀ (n : ℕ) {m : ℕ} (i : Fin m), (Fin.natAddEmb n) i 
= Fin.natAdd n i
· 使用定理 `Finset.coe_Icc`：coe_Icc (a b : α) : (Icc a b : Set α) = Set.Icc a b
· 使用定理 `Fin.image_natAdd_Icc`：image_natAdd_Icc (m) (i j : Fin n) : natAdd m '' I
cc i j = Icc (natAdd m i) (natAdd m j)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
### `Finset.map` along `Fin.natAddEmb`
-/
theorem map_natAddEmb_Icc (m) (i j : Fin n) :
    (Icc i j).map (natAddEmb m) = Icc (natAdd m i) (natAdd m j) := by
  simp [← coe_inj]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Fin.map_natAddEmb_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_natAddEmb_Ico (m) (i j : Fin n) : (Ico i j).map (natAddEmb m) = Ico (n
atAdd m i) (natAdd m j)
参数：m；i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Fin.natAddEmb_apply`：∀ (n : ℕ) {m : ℕ} (i : Fin m), (Fin.natAddEmb n) i 
= Fin.natAdd n i
· 使用定理 `Finset.coe_Ico`：coe_Ico (a b : α) : (Ico a b : Set α) = Set.Ico a b
· 使用定理 `Fin.image_natAdd_Ico`：image_natAdd_Ico (m) (i j : Fin n) : natAdd m '' I
co i j = Ico (natAdd m i) (natAdd m j)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_natAddEmb_Ico (m) (i j : Fin n) :
    (Ico i j).map (natAddEmb m) = Ico (natAdd m i) (natAdd m j) := by
  simp [← coe_inj]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Fin.map_natAddEmb_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_natAddEmb_Ioc (m) (i j : Fin n) : (Ioc i j).map (natAddEmb m) = Ioc (n
atAdd m i) (natAdd m j)
参数：m；i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Fin.natAddEmb_apply`：∀ (n : ℕ) {m : ℕ} (i : Fin m), (Fin.natAddEmb n) i 
= Fin.natAdd n i
· 使用定理 `Finset.coe_Ioc`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrder α] (b a : α), ↑(Finset.Ioc b a) = Set.Ioc b a
· 使用定理 `Fin.image_natAdd_Ioc`：image_natAdd_Ioc (m) (i j : Fin n) : natAdd m '' I
oc i j = Ioc (natAdd m i) (natAdd m j)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_natAddEmb_Ioc (m) (i j : Fin n) :
    (Ioc i j).map (natAddEmb m) = Ioc (natAdd m i) (natAdd m j) := by
  simp [← coe_inj]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Fin.map_natAddEmb_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_natAddEmb_Ioo (m) (i j : Fin n) : (Ioo i j).map (natAddEmb m) = Ioo (n
atAdd m i) (natAdd m j)
参数：m；i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Fin.natAddEmb_apply`：∀ (n : ℕ) {m : ℕ} (i : Fin m), (Fin.natAddEmb n) i 
= Fin.natAdd n i
· 使用定理 `Finset.coe_Ioo`：coe_Ioo (a b : α) : (Ioo a b : Set α) = Set.Ioo a b
· 使用定理 `Fin.image_natAdd_Ioo`：image_natAdd_Ioo (m) (i j : Fin n) : natAdd m '' I
oo i j = Ioo (natAdd m i) (natAdd m j)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_natAddEmb_Ioo (m) (i j : Fin n) :
    (Ioo i j).map (natAddEmb m) = Ioo (natAdd m i) (natAdd m j) := by
  simp [← coe_inj]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Fin.map_natAddEmb_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_natAddEmb_uIcc (m) (i j : Fin n) : (uIcc i j).map (natAddEmb m) = uIcc
 (natAdd m i) (natAdd m j)
参数：m；i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Fin.natAddEmb_apply`：∀ (n : ℕ) {m : ℕ} (i : Fin m), (Fin.natAddEmb n) i 
= Fin.natAdd n i
· 使用定理 `Finset.coe_uIcc`：coe_uIcc (a b : α) : (Finset.uIcc a b : Set α) = Set.uI
cc a b
· 使用定理 `Fin.image_natAdd_uIcc`：image_natAdd_uIcc (m) (i j : Fin n) : natAdd m ''
 uIcc i j = uIcc (natAdd m i) (natAdd m j)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_natAddEmb_uIcc (m) (i j : Fin n) :
    (uIcc i j).map (natAddEmb m) = uIcc (natAdd m i) (natAdd m j) := by
  simp [← coe_inj]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Fin.map_natAddEmb_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_natAddEmb_Ici (m) (i : Fin n) : (Ici i).map (natAddEmb m) = Ici (natAd
d m i)
参数：m；i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Fin.natAddEmb_apply`：∀ (n : ℕ) {m : ℕ} (i : Fin m), (Fin.natAddEmb n) i 
= Fin.natAdd n i
· 使用定理 `Finset.coe_Ici`：coe_Ici (a : α) : (Ici a : Set α) = Set.Ici a
· 使用定理 `Fin.image_natAdd_Ici`：image_natAdd_Ici (m) (i : Fin n) : natAdd m '' Ici
 i = Ici (natAdd m i)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_natAddEmb_Ici (m) (i : Fin n) : (Ici i).map (natAddEmb m) = Ici (natAdd m i) := by
  simp [← coe_inj]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Fin.map_natAddEmb_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_natAddEmb_Ioi (m) (i : Fin n) : (Ioi i).map (natAddEmb m) = Ioi (natAd
d m i)
参数：m；i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Fin.natAddEmb_apply`：∀ (n : ℕ) {m : ℕ} (i : Fin m), (Fin.natAddEmb n) i 
= Fin.natAdd n i
· 使用定理 `Finset.coe_Ioi`：coe_Ioi (a : α) : (Ioi a : Set α) = Set.Ioi a
· 使用定理 `Fin.image_natAdd_Ioi`：image_natAdd_Ioi (m) (i : Fin n) : natAdd m '' Ioi
 i = Ioi (natAdd m i)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_natAddEmb_Ioi (m) (i : Fin n) : (Ioi i).map (natAddEmb m) = Ioi (natAdd m i) := by
  simp [← coe_inj]

end natAdd

section addNat

/-!
### Images under `Fin.addNat`
-/

@[simp]
/-
**Fin.finsetImage_addNat_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_addNat_Icc (m) (i j : Fin n) : (Icc i j).image (addNat · m) = 
Icc (i.addNat m) (j.addNat m)
参数：m；i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Finset.coe_Icc`：coe_Icc (a b : α) : (Icc a b : Set α) = Set.Icc a b
· 使用定理 `Fin.image_addNat_Icc`：image_addNat_Icc (m) (i j : Fin n) : (addNat · m) 
'' Icc i j = Icc (i.addNat m) (j.addNat m)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
### Images under `Fin.addNat`
-/
theorem finsetImage_addNat_Icc (m) (i j : Fin n) :
    (Icc i j).image (addNat · m) = Icc (i.addNat m) (j.addNat m) := by
  simp [← coe_inj]

@[simp]
/-
**Fin.finsetImage_addNat_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_addNat_Ico (m) (i j : Fin n) : (Ico i j).image (addNat · m) = 
Ico (i.addNat m) (j.addNat m)
参数：m；i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Finset.coe_Ico`：coe_Ico (a b : α) : (Ico a b : Set α) = Set.Ico a b
· 使用定理 `Fin.image_addNat_Ico`：image_addNat_Ico (m) (i j : Fin n) : (addNat · m) 
'' Ico i j = Ico (i.addNat m) (j.addNat m)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finsetImage_addNat_Ico (m) (i j : Fin n) :
    (Ico i j).image (addNat · m) = Ico (i.addNat m) (j.addNat m) := by
  simp [← coe_inj]

@[simp]
/-
**Fin.finsetImage_addNat_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_addNat_Ioc (m) (i j : Fin n) : (Ioc i j).image (addNat · m) = 
Ioc (i.addNat m) (j.addNat m)
参数：m；i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Finset.coe_Ioc`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrder α] (b a : α), ↑(Finset.Ioc b a) = Set.Ioc b a
· 使用定理 `Fin.image_addNat_Ioc`：image_addNat_Ioc (m) (i j : Fin n) : (addNat · m) 
'' Ioc i j = Ioc (i.addNat m) (j.addNat m)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finsetImage_addNat_Ioc (m) (i j : Fin n) :
    (Ioc i j).image (addNat · m) = Ioc (i.addNat m) (j.addNat m) := by
  simp [← coe_inj]

@[simp]
/-
**Fin.finsetImage_addNat_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_addNat_Ioo (m) (i j : Fin n) : (Ioo i j).image (addNat · m) = 
Ioo (i.addNat m) (j.addNat m)
参数：m；i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Finset.coe_Ioo`：coe_Ioo (a b : α) : (Ioo a b : Set α) = Set.Ioo a b
· 使用定理 `Fin.image_addNat_Ioo`：image_addNat_Ioo (m) (i j : Fin n) : (addNat · m) 
'' Ioo i j = Ioo (i.addNat m) (j.addNat m)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finsetImage_addNat_Ioo (m) (i j : Fin n) :
    (Ioo i j).image (addNat · m) = Ioo (i.addNat m) (j.addNat m) := by
  simp [← coe_inj]

@[simp]
/-
**Fin.finsetImage_addNat_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_addNat_uIcc (m) (i j : Fin n) : (uIcc i j).image (addNat · m) 
= uIcc (i.addNat m) (j.addNat m)
参数：m；i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Finset.coe_uIcc`：coe_uIcc (a b : α) : (Finset.uIcc a b : Set α) = Set.uI
cc a b
· 使用定理 `Fin.image_addNat_uIcc`：image_addNat_uIcc (m) (i j : Fin n) : (addNat · m
) '' uIcc i j = uIcc (i.addNat m) (j.addNat m)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finsetImage_addNat_uIcc (m) (i j : Fin n) :
    (uIcc i j).image (addNat · m) = uIcc (i.addNat m) (j.addNat m) := by
  simp [← coe_inj]

@[simp]
/-
**Fin.finsetImage_addNat_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_addNat_Ici (m) (i : Fin n) : (Ici i).image (addNat · m) = Ici 
(i.addNat m)
参数：m；i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Finset.coe_Ici`：coe_Ici (a : α) : (Ici a : Set α) = Set.Ici a
· 使用定理 `Fin.image_addNat_Ici`：image_addNat_Ici (m) (i : Fin n) : (addNat · m) ''
 Ici i = Ici (i.addNat m)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finsetImage_addNat_Ici (m) (i : Fin n) : (Ici i).image (addNat · m) = Ici (i.addNat m) := by
  simp [← coe_inj]

@[simp]
/-
**Fin.finsetImage_addNat_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_addNat_Ioi (m) (i : Fin n) : (Ioi i).image (addNat · m) = Ioi 
(i.addNat m)
参数：m；i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Finset.coe_Ioi`：coe_Ioi (a : α) : (Ioi a : Set α) = Set.Ioi a
· 使用定理 `Fin.image_addNat_Ioi`：image_addNat_Ioi (m) (i : Fin n) : (addNat · m) ''
 Ioi i = Ioi (i.addNat m)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finsetImage_addNat_Ioi (m) (i : Fin n) : (Ioi i).image (addNat · m) = Ioi (i.addNat m) := by
  simp [← coe_inj]

/-!
### `Finset.map` along `Fin.addNatEmb`
-/

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Fin.map_addNatEmb_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_addNatEmb_Icc (m) (i j : Fin n) : (Icc i j).map (addNatEmb m) = Icc (i
.addNat m) (j.addNat m)
参数：m；i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Fin.addNatEmb_apply`：∀ {n : ℕ} (m : ℕ) (x : Fin n), (Fin.addNatEmb m) x 
= x.addNat m
· 使用定理 `Finset.coe_Icc`：coe_Icc (a b : α) : (Icc a b : Set α) = Set.Icc a b
· 使用定理 `Fin.image_addNat_Icc`：image_addNat_Icc (m) (i j : Fin n) : (addNat · m) 
'' Icc i j = Icc (i.addNat m) (j.addNat m)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
### `Finset.map` along `Fin.addNatEmb`
-/
theorem map_addNatEmb_Icc (m) (i j : Fin n) :
    (Icc i j).map (addNatEmb m) = Icc (i.addNat m) (j.addNat m) := by
  simp [← coe_inj]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Fin.map_addNatEmb_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_addNatEmb_Ico (m) (i j : Fin n) : (Ico i j).map (addNatEmb m) = Ico (i
.addNat m) (j.addNat m)
参数：m；i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Fin.addNatEmb_apply`：∀ {n : ℕ} (m : ℕ) (x : Fin n), (Fin.addNatEmb m) x 
= x.addNat m
· 使用定理 `Finset.coe_Ico`：coe_Ico (a b : α) : (Ico a b : Set α) = Set.Ico a b
· 使用定理 `Fin.image_addNat_Ico`：image_addNat_Ico (m) (i j : Fin n) : (addNat · m) 
'' Ico i j = Ico (i.addNat m) (j.addNat m)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_addNatEmb_Ico (m) (i j : Fin n) :
    (Ico i j).map (addNatEmb m) = Ico (i.addNat m) (j.addNat m) := by
  simp [← coe_inj]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Fin.map_addNatEmb_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_addNatEmb_Ioc (m) (i j : Fin n) : (Ioc i j).map (addNatEmb m) = Ioc (i
.addNat m) (j.addNat m)
参数：m；i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Fin.addNatEmb_apply`：∀ {n : ℕ} (m : ℕ) (x : Fin n), (Fin.addNatEmb m) x 
= x.addNat m
· 使用定理 `Finset.coe_Ioc`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrder α] (b a : α), ↑(Finset.Ioc b a) = Set.Ioc b a
· 使用定理 `Fin.image_addNat_Ioc`：image_addNat_Ioc (m) (i j : Fin n) : (addNat · m) 
'' Ioc i j = Ioc (i.addNat m) (j.addNat m)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_addNatEmb_Ioc (m) (i j : Fin n) :
    (Ioc i j).map (addNatEmb m) = Ioc (i.addNat m) (j.addNat m) := by
  simp [← coe_inj]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Fin.map_addNatEmb_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_addNatEmb_Ioo (m) (i j : Fin n) : (Ioo i j).map (addNatEmb m) = Ioo (i
.addNat m) (j.addNat m)
参数：m；i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Fin.addNatEmb_apply`：∀ {n : ℕ} (m : ℕ) (x : Fin n), (Fin.addNatEmb m) x 
= x.addNat m
· 使用定理 `Finset.coe_Ioo`：coe_Ioo (a b : α) : (Ioo a b : Set α) = Set.Ioo a b
· 使用定理 `Fin.image_addNat_Ioo`：image_addNat_Ioo (m) (i j : Fin n) : (addNat · m) 
'' Ioo i j = Ioo (i.addNat m) (j.addNat m)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_addNatEmb_Ioo (m) (i j : Fin n) :
    (Ioo i j).map (addNatEmb m) = Ioo (i.addNat m) (j.addNat m) := by
  simp [← coe_inj]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Fin.map_addNatEmb_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_addNatEmb_uIcc (m) (i j : Fin n) : (uIcc i j).map (addNatEmb m) = uIcc
 (i.addNat m) (j.addNat m)
参数：m；i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Fin.addNatEmb_apply`：∀ {n : ℕ} (m : ℕ) (x : Fin n), (Fin.addNatEmb m) x 
= x.addNat m
· 使用定理 `Finset.coe_uIcc`：coe_uIcc (a b : α) : (Finset.uIcc a b : Set α) = Set.uI
cc a b
· 使用定理 `Fin.image_addNat_uIcc`：image_addNat_uIcc (m) (i j : Fin n) : (addNat · m
) '' uIcc i j = uIcc (i.addNat m) (j.addNat m)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_addNatEmb_uIcc (m) (i j : Fin n) :
    (uIcc i j).map (addNatEmb m) = uIcc (i.addNat m) (j.addNat m) := by
  simp [← coe_inj]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Fin.map_addNatEmb_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_addNatEmb_Ici (m) (i : Fin n) : (Ici i).map (addNatEmb m) = Ici (i.add
Nat m)
参数：m；i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Fin.addNatEmb_apply`：∀ {n : ℕ} (m : ℕ) (x : Fin n), (Fin.addNatEmb m) x 
= x.addNat m
· 使用定理 `Finset.coe_Ici`：coe_Ici (a : α) : (Ici a : Set α) = Set.Ici a
· 使用定理 `Fin.image_addNat_Ici`：image_addNat_Ici (m) (i : Fin n) : (addNat · m) ''
 Ici i = Ici (i.addNat m)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_addNatEmb_Ici (m) (i : Fin n) : (Ici i).map (addNatEmb m) = Ici (i.addNat m) := by
  simp [← coe_inj]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Fin.map_addNatEmb_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_addNatEmb_Ioi (m) (i : Fin n) : (Ioi i).map (addNatEmb m) = Ioi (i.add
Nat m)
参数：m；i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Fin.addNatEmb_apply`：∀ {n : ℕ} (m : ℕ) (x : Fin n), (Fin.addNatEmb m) x 
= x.addNat m
· 使用定理 `Finset.coe_Ioi`：coe_Ioi (a : α) : (Ioi a : Set α) = Set.Ioi a
· 使用定理 `Fin.image_addNat_Ioi`：image_addNat_Ioi (m) (i : Fin n) : (addNat · m) ''
 Ioi i = Ioi (i.addNat m)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_addNatEmb_Ioi (m) (i : Fin n) : (Ioi i).map (addNatEmb m) = Ioi (i.addNat m) := by
  simp [← coe_inj]

end addNat

section succ

/-!
### Images under `Fin.succ`
-/

@[simp]
/-
**Fin.finsetImage_succ_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_succ_Icc (i j : Fin n) : (Icc i j).image succ = Icc i.succ j.s
ucc
参数：i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.finsetImage_addNat_Icc`：finsetImage_addNat_Icc (m) (i j : Fin n) : (
Icc i j).image (addNat · m) = Icc (i.addNat m) (j.addNat m)

--- 原说明 ---
### Images under `Fin.succ`
-/
theorem finsetImage_succ_Icc (i j : Fin n) : (Icc i j).image succ = Icc i.succ j.succ :=
  finsetImage_addNat_Icc ..

@[simp]
/-
**Fin.finsetImage_succ_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_succ_Ico (i j : Fin n) : (Ico i j).image succ = Ico i.succ j.s
ucc
参数：i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.finsetImage_addNat_Ico`：finsetImage_addNat_Ico (m) (i j : Fin n) : (
Ico i j).image (addNat · m) = Ico (i.addNat m) (j.addNat m)
-/
theorem finsetImage_succ_Ico (i j : Fin n) : (Ico i j).image succ = Ico i.succ j.succ :=
  finsetImage_addNat_Ico ..

@[simp]
/-
**Fin.finsetImage_succ_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_succ_Ioc (i j : Fin n) : (Ioc i j).image succ = Ioc i.succ j.s
ucc
参数：i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.finsetImage_addNat_Ioc`：finsetImage_addNat_Ioc (m) (i j : Fin n) : (
Ioc i j).image (addNat · m) = Ioc (i.addNat m) (j.addNat m)
-/
theorem finsetImage_succ_Ioc (i j : Fin n) : (Ioc i j).image succ = Ioc i.succ j.succ :=
  finsetImage_addNat_Ioc ..

@[simp]
/-
**Fin.finsetImage_succ_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_succ_Ioo (i j : Fin n) : (Ioo i j).image succ = Ioo i.succ j.s
ucc
参数：i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.finsetImage_addNat_Ioo`：finsetImage_addNat_Ioo (m) (i j : Fin n) : (
Ioo i j).image (addNat · m) = Ioo (i.addNat m) (j.addNat m)
-/
theorem finsetImage_succ_Ioo (i j : Fin n) : (Ioo i j).image succ = Ioo i.succ j.succ :=
  finsetImage_addNat_Ioo ..

@[simp]
/-
**Fin.finsetImage_succ_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_succ_uIcc (i j : Fin n) : (uIcc i j).image succ = uIcc i.succ 
j.succ
参数：i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.finsetImage_addNat_uIcc`：finsetImage_addNat_uIcc (m) (i j : Fin n) :
 (uIcc i j).image (addNat · m) = uIcc (i.addNat m) (j.addNat m)
-/
theorem finsetImage_succ_uIcc (i j : Fin n) : (uIcc i j).image succ = uIcc i.succ j.succ :=
  finsetImage_addNat_uIcc ..

@[simp]
/-
**Fin.finsetImage_succ_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_succ_Ici (i : Fin n) : (Ici i).image succ = Ici i.succ
参数：i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.finsetImage_addNat_Ici`：finsetImage_addNat_Ici (m) (i : Fin n) : (Ic
i i).image (addNat · m) = Ici (i.addNat m)
-/
theorem finsetImage_succ_Ici (i : Fin n) : (Ici i).image succ = Ici i.succ :=
  finsetImage_addNat_Ici ..

@[simp]
/-
**Fin.finsetImage_succ_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_succ_Ioi (i : Fin n) : (Ioi i).image succ = Ioi i.succ
参数：i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.finsetImage_addNat_Ioi`：finsetImage_addNat_Ioi (m) (i : Fin n) : (Io
i i).image (addNat · m) = Ioi (i.addNat m)
-/
theorem finsetImage_succ_Ioi (i : Fin n) : (Ioi i).image succ = Ioi i.succ :=
  finsetImage_addNat_Ioi ..

@[simp]
/-
**Fin.finsetImage_succ_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_succ_Iic (i : Fin n) : (Iic i).image succ = Ioc 0 i.succ
参数：i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Finset.coe_Iic`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] (a : α), ↑(Finset.Iic a) = Set.Iic a
· 使用定理 `Fin.image_succ_Iic`：image_succ_Iic (i : Fin n) : succ '' Iic i = Ioc 0 i
.succ
· 使用定理 `Finset.coe_Ioc`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrder α] (b a : α), ↑(Finset.Ioc b a) = Set.Ioc b a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finsetImage_succ_Iic (i : Fin n) : (Iic i).image succ = Ioc 0 i.succ := by
  simp [← coe_inj]

@[simp]
/-
**Fin.finsetImage_succ_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_succ_Iio (i : Fin n) : (Iio i).image succ = Ioo 0 i.succ
参数：i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Finset.coe_Iio`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] (a : α), ↑(Finset.Iio a) = Set.Iio a
· 使用定理 `Fin.image_succ_Iio`：image_succ_Iio (i : Fin n) : succ '' Iio i = Ioo 0 i
.succ
· 使用定理 `Finset.coe_Ioo`：coe_Ioo (a b : α) : (Ioo a b : Set α) = Set.Ioo a b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finsetImage_succ_Iio (i : Fin n) : (Iio i).image succ = Ioo 0 i.succ := by
  simp [← coe_inj]

/-!
### `Finset.map` along `Fin.succEmb`
-/

@[simp]
/-
**Fin.map_succEmb_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_succEmb_Icc (i j : Fin n) : (Icc i j).map (succEmb n) = Icc i.succ j.s
ucc
参数：i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.map_addNatEmb_Icc`：map_addNatEmb_Icc (m) (i j : Fin n) : (Icc i j).m
ap (addNatEmb m) = Icc (i.addNat m) (j.addNat m)

--- 原说明 ---
### `Finset.map` along `Fin.succEmb`
-/
theorem map_succEmb_Icc (i j : Fin n) : (Icc i j).map (succEmb n) = Icc i.succ j.succ :=
  map_addNatEmb_Icc ..

@[simp]
/-
**Fin.map_succEmb_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_succEmb_Ico (i j : Fin n) : (Ico i j).map (succEmb n) = Ico i.succ j.s
ucc
参数：i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.map_addNatEmb_Ico`：map_addNatEmb_Ico (m) (i j : Fin n) : (Ico i j).m
ap (addNatEmb m) = Ico (i.addNat m) (j.addNat m)
-/
theorem map_succEmb_Ico (i j : Fin n) : (Ico i j).map (succEmb n) = Ico i.succ j.succ :=
  map_addNatEmb_Ico ..

@[simp]
/-
**Fin.map_succEmb_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_succEmb_Ioc (i j : Fin n) : (Ioc i j).map (succEmb n) = Ioc i.succ j.s
ucc
参数：i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.map_addNatEmb_Ioc`：map_addNatEmb_Ioc (m) (i j : Fin n) : (Ioc i j).m
ap (addNatEmb m) = Ioc (i.addNat m) (j.addNat m)
-/
theorem map_succEmb_Ioc (i j : Fin n) : (Ioc i j).map (succEmb n) = Ioc i.succ j.succ :=
  map_addNatEmb_Ioc ..

@[simp]
/-
**Fin.map_succEmb_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_succEmb_Ioo (i j : Fin n) : (Ioo i j).map (succEmb n) = Ioo i.succ j.s
ucc
参数：i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.map_addNatEmb_Ioo`：map_addNatEmb_Ioo (m) (i j : Fin n) : (Ioo i j).m
ap (addNatEmb m) = Ioo (i.addNat m) (j.addNat m)
-/
theorem map_succEmb_Ioo (i j : Fin n) : (Ioo i j).map (succEmb n) = Ioo i.succ j.succ :=
  map_addNatEmb_Ioo ..

@[simp]
/-
**Fin.map_succEmb_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_succEmb_uIcc (i j : Fin n) : (uIcc i j).map (succEmb n) = uIcc i.succ 
j.succ
参数：i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.map_addNatEmb_uIcc`：map_addNatEmb_uIcc (m) (i j : Fin n) : (uIcc i j
).map (addNatEmb m) = uIcc (i.addNat m) (j.addNat m)
-/
theorem map_succEmb_uIcc (i j : Fin n) : (uIcc i j).map (succEmb n) = uIcc i.succ j.succ :=
  map_addNatEmb_uIcc ..

@[simp]
/-
**Fin.map_succEmb_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_succEmb_Ici (i : Fin n) : (Ici i).map (succEmb n) = Ici i.succ
参数：i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.map_addNatEmb_Ici`：map_addNatEmb_Ici (m) (i : Fin n) : (Ici i).map (
addNatEmb m) = Ici (i.addNat m)
-/
theorem map_succEmb_Ici (i : Fin n) : (Ici i).map (succEmb n) = Ici i.succ :=
  map_addNatEmb_Ici ..

@[simp]
/-
**Fin.map_succEmb_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_succEmb_Ioi (i : Fin n) : (Ioi i).map (succEmb n) = Ioi i.succ
参数：i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.map_addNatEmb_Ioi`：map_addNatEmb_Ioi (m) (i : Fin n) : (Ioi i).map (
addNatEmb m) = Ioi (i.addNat m)
-/
theorem map_succEmb_Ioi (i : Fin n) : (Ioi i).map (succEmb n) = Ioi i.succ :=
  map_addNatEmb_Ioi ..

@[simp]
/-
**Fin.map_succEmb_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_succEmb_Iic (i : Fin n) : (Iic i).map (succEmb n) = Ioc 0 i.succ
参数：i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Finset.coe_Iic`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] (a : α), ↑(Finset.Iic a) = Set.Iic a
· 使用定理 `Fin.image_succ_Iic`：image_succ_Iic (i : Fin n) : succ '' Iic i = Ioc 0 i
.succ
· 使用定理 `Finset.coe_Ioc`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrder α] (b a : α), ↑(Finset.Ioc b a) = Set.Ioc b a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_succEmb_Iic (i : Fin n) : (Iic i).map (succEmb n) = Ioc 0 i.succ := by
  simp [← coe_inj]

@[simp]
/-
**Fin.map_succEmb_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_succEmb_Iio (i : Fin n) : (Iio i).map (succEmb n) = Ioo 0 i.succ
参数：i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Finset.coe_Iio`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] (a : α), ↑(Finset.Iio a) = Set.Iio a
· 使用定理 `Fin.image_succ_Iio`：image_succ_Iio (i : Fin n) : succ '' Iio i = Ioo 0 i
.succ
· 使用定理 `Finset.coe_Ioo`：coe_Ioo (a b : α) : (Ioo a b : Set α) = Set.Ioo a b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_succEmb_Iio (i : Fin n) : (Iio i).map (succEmb n) = Ioo 0 i.succ := by
  simp [← coe_inj]

end succ

section rev

/-!
### Images under `Fin.rev`
-/

@[simp]
/-
**Fin.finsetImage_rev_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_rev_Icc (i j : Fin n) : (Icc i j).image rev = Icc j.rev i.rev
参数：i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Finset.coe_Icc`：coe_Icc (a b : α) : (Icc a b : Set α) = Set.Icc a b
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Fin.image_rev_fun`：image_rev_fun : image (@rev n) = preimage rev
· 使用定理 `Fin.preimage_rev_Icc`：preimage_rev_Icc (i j : Fin n) : rev ⁻¹' Icc i j =
 Icc j.rev i.rev
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
### Images under `Fin.rev`
-/
theorem finsetImage_rev_Icc (i j : Fin n) : (Icc i j).image rev = Icc j.rev i.rev := by
  simp [← coe_inj]

@[simp]
/-
**Fin.finsetImage_rev_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_rev_Ico (i j : Fin n) : (Ico i j).image rev = Ioc j.rev i.rev
参数：i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Finset.coe_Ico`：coe_Ico (a b : α) : (Ico a b : Set α) = Set.Ico a b
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Fin.image_rev_fun`：image_rev_fun : image (@rev n) = preimage rev
· 使用定理 `Fin.preimage_rev_Ico`：preimage_rev_Ico (i j : Fin n) : rev ⁻¹' Ico i j =
 Ioc j.rev i.rev
· 使用定理 `Finset.coe_Ioc`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrder α] (b a : α), ↑(Finset.Ioc b a) = Set.Ioc b a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finsetImage_rev_Ico (i j : Fin n) : (Ico i j).image rev = Ioc j.rev i.rev := by
  simp [← coe_inj]

@[simp]
/-
**Fin.finsetImage_rev_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_rev_Ioc (i j : Fin n) : (Ioc i j).image rev = Ico j.rev i.rev
参数：i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Finset.coe_Ioc`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrder α] (b a : α), ↑(Finset.Ioc b a) = Set.Ioc b a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Fin.image_rev_fun`：image_rev_fun : image (@rev n) = preimage rev
· 使用定理 `Fin.preimage_rev_Ioc`：preimage_rev_Ioc (i j : Fin n) : rev ⁻¹' Ioc i j =
 Ico j.rev i.rev
· 使用定理 `Finset.coe_Ico`：coe_Ico (a b : α) : (Ico a b : Set α) = Set.Ico a b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finsetImage_rev_Ioc (i j : Fin n) : (Ioc i j).image rev = Ico j.rev i.rev := by
  simp [← coe_inj]

@[simp]
/-
**Fin.finsetImage_rev_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_rev_Ioo (i j : Fin n) : (Ioo i j).image rev = Ioo j.rev i.rev
参数：i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Finset.coe_Ioo`：coe_Ioo (a b : α) : (Ioo a b : Set α) = Set.Ioo a b
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Fin.image_rev_fun`：image_rev_fun : image (@rev n) = preimage rev
· 使用定理 `Fin.preimage_rev_Ioo`：preimage_rev_Ioo (i j : Fin n) : rev ⁻¹' Ioo i j =
 Ioo j.rev i.rev
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finsetImage_rev_Ioo (i j : Fin n) : (Ioo i j).image rev = Ioo j.rev i.rev := by
  simp [← coe_inj]

@[simp]
/-
**Fin.finsetImage_rev_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_rev_uIcc (i j : Fin n) : (uIcc i j).image rev = uIcc i.rev j.r
ev
参数：i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Finset.coe_uIcc`：coe_uIcc (a b : α) : (Finset.uIcc a b : Set α) = Set.uI
cc a b
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Fin.image_rev_fun`：image_rev_fun : image (@rev n) = preimage rev
· 使用定理 `Fin.preimage_rev_uIcc`：preimage_rev_uIcc (i j : Fin n) : rev ⁻¹' uIcc i 
j = uIcc i.rev j.rev
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finsetImage_rev_uIcc (i j : Fin n) : (uIcc i j).image rev = uIcc i.rev j.rev := by
  simp [← coe_inj]

@[simp]
/-
**Fin.finsetImage_rev_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_rev_Ici (i : Fin n) : (Ici i).image rev = Iic i.rev
参数：i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Finset.coe_Ici`：coe_Ici (a : α) : (Ici a : Set α) = Set.Ici a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Fin.image_rev_fun`：image_rev_fun : image (@rev n) = preimage rev
· 使用定理 `Fin.preimage_rev_Ici`：preimage_rev_Ici (i : Fin n) : rev ⁻¹' Ici i = Iic
 i.rev
· 使用定理 `Finset.coe_Iic`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] (a : α), ↑(Finset.Iic a) = Set.Iic a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finsetImage_rev_Ici (i : Fin n) : (Ici i).image rev = Iic i.rev := by simp [← coe_inj]

@[simp]
/-
**Fin.finsetImage_rev_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_rev_Ioi (i : Fin n) : (Ioi i).image rev = Iio i.rev
参数：i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Finset.coe_Ioi`：coe_Ioi (a : α) : (Ioi a : Set α) = Set.Ioi a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Fin.image_rev_fun`：image_rev_fun : image (@rev n) = preimage rev
· 使用定理 `Fin.preimage_rev_Ioi`：preimage_rev_Ioi (i : Fin n) : rev ⁻¹' Ioi i = Iio
 i.rev
· 使用定理 `Finset.coe_Iio`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] (a : α), ↑(Finset.Iio a) = Set.Iio a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finsetImage_rev_Ioi (i : Fin n) : (Ioi i).image rev = Iio i.rev := by simp [← coe_inj]

@[simp]
/-
**Fin.finsetImage_rev_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_rev_Iic (i : Fin n) : (Iic i).image rev = Ici i.rev
参数：i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Finset.coe_Iic`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] (a : α), ↑(Finset.Iic a) = Set.Iic a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Fin.image_rev_fun`：image_rev_fun : image (@rev n) = preimage rev
· 使用定理 `Fin.preimage_rev_Iic`：preimage_rev_Iic (i : Fin n) : rev ⁻¹' Iic i = Ici
 i.rev
· 使用定理 `Finset.coe_Ici`：coe_Ici (a : α) : (Ici a : Set α) = Set.Ici a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finsetImage_rev_Iic (i : Fin n) : (Iic i).image rev = Ici i.rev := by simp [← coe_inj]

@[simp]
/-
**Fin.finsetImage_rev_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：finsetImage_rev_Iio (i : Fin n) : (Iio i).image rev = Ioi i.rev
参数：i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Finset.coe_Iio`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] (a : α), ↑(Finset.Iio a) = Set.Iio a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Fin.image_rev_fun`：image_rev_fun : image (@rev n) = preimage rev
· 使用定理 `Fin.preimage_rev_Iio`：preimage_rev_Iio (i : Fin n) : rev ⁻¹' Iio i = Ioi
 i.rev
· 使用定理 `Finset.coe_Ioi`：coe_Ioi (a : α) : (Ioi a : Set α) = Set.Ioi a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finsetImage_rev_Iio (i : Fin n) : (Iio i).image rev = Ioi i.rev := by simp [← coe_inj]

/-!
### `Finset.map` along `revPerm`
-/

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Fin.map_revPerm_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_revPerm_Icc (i j : Fin n) : (Icc i j).map revPerm.toEmbedding = Icc j.
rev i.rev
参数：i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Fin.revPerm_apply`：∀ {n : ℕ} (i : Fin n), Fin.revPerm i = i.rev
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Fin.image_rev_fun`：image_rev_fun : image (@rev n) = preimage rev
· 使用定理 `Finset.coe_Icc`：coe_Icc (a b : α) : (Icc a b : Set α) = Set.Icc a b
· 使用定理 `Fin.preimage_rev_Icc`：preimage_rev_Icc (i j : Fin n) : rev ⁻¹' Icc i j =
 Icc j.rev i.rev
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
### `Finset.map` along `revPerm`
-/
theorem map_revPerm_Icc (i j : Fin n) : (Icc i j).map revPerm.toEmbedding = Icc j.rev i.rev := by
  simp [← coe_inj]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Fin.map_revPerm_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_revPerm_Ico (i j : Fin n) : (Ico i j).map revPerm.toEmbedding = Ioc j.
rev i.rev
参数：i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Fin.revPerm_apply`：∀ {n : ℕ} (i : Fin n), Fin.revPerm i = i.rev
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Fin.image_rev_fun`：image_rev_fun : image (@rev n) = preimage rev
· 使用定理 `Finset.coe_Ico`：coe_Ico (a b : α) : (Ico a b : Set α) = Set.Ico a b
· 使用定理 `Fin.preimage_rev_Ico`：preimage_rev_Ico (i j : Fin n) : rev ⁻¹' Ico i j =
 Ioc j.rev i.rev
· 使用定理 `Finset.coe_Ioc`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrder α] (b a : α), ↑(Finset.Ioc b a) = Set.Ioc b a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_revPerm_Ico (i j : Fin n) : (Ico i j).map revPerm.toEmbedding = Ioc j.rev i.rev := by
  simp [← coe_inj]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Fin.map_revPerm_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_revPerm_Ioc (i j : Fin n) : (Ioc i j).map revPerm.toEmbedding = Ico j.
rev i.rev
参数：i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Fin.revPerm_apply`：∀ {n : ℕ} (i : Fin n), Fin.revPerm i = i.rev
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Fin.image_rev_fun`：image_rev_fun : image (@rev n) = preimage rev
· 使用定理 `Finset.coe_Ioc`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrder α] (b a : α), ↑(Finset.Ioc b a) = Set.Ioc b a
· 使用定理 `Fin.preimage_rev_Ioc`：preimage_rev_Ioc (i j : Fin n) : rev ⁻¹' Ioc i j =
 Ico j.rev i.rev
· 使用定理 `Finset.coe_Ico`：coe_Ico (a b : α) : (Ico a b : Set α) = Set.Ico a b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_revPerm_Ioc (i j : Fin n) : (Ioc i j).map revPerm.toEmbedding = Ico j.rev i.rev := by
  simp [← coe_inj]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Fin.map_revPerm_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_revPerm_Ioo (i j : Fin n) : (Ioo i j).map revPerm.toEmbedding = Ioo j.
rev i.rev
参数：i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Fin.revPerm_apply`：∀ {n : ℕ} (i : Fin n), Fin.revPerm i = i.rev
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Fin.image_rev_fun`：image_rev_fun : image (@rev n) = preimage rev
· 使用定理 `Finset.coe_Ioo`：coe_Ioo (a b : α) : (Ioo a b : Set α) = Set.Ioo a b
· 使用定理 `Fin.preimage_rev_Ioo`：preimage_rev_Ioo (i j : Fin n) : rev ⁻¹' Ioo i j =
 Ioo j.rev i.rev
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_revPerm_Ioo (i j : Fin n) : (Ioo i j).map revPerm.toEmbedding = Ioo j.rev i.rev := by
  simp [← coe_inj]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Fin.map_revPerm_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_revPerm_uIcc (i j : Fin n) : (uIcc i j).map revPerm.toEmbedding = uIcc
 i.rev j.rev
参数：i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Fin.revPerm_apply`：∀ {n : ℕ} (i : Fin n), Fin.revPerm i = i.rev
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Fin.image_rev_fun`：image_rev_fun : image (@rev n) = preimage rev
· 使用定理 `Finset.coe_uIcc`：coe_uIcc (a b : α) : (Finset.uIcc a b : Set α) = Set.uI
cc a b
· 使用定理 `Fin.preimage_rev_uIcc`：preimage_rev_uIcc (i j : Fin n) : rev ⁻¹' uIcc i 
j = uIcc i.rev j.rev
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_revPerm_uIcc (i j : Fin n) : (uIcc i j).map revPerm.toEmbedding = uIcc i.rev j.rev := by
  simp [← coe_inj]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Fin.map_revPerm_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_revPerm_Ici (i : Fin n) : (Ici i).map revPerm.toEmbedding = Iic i.rev
参数：i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Fin.revPerm_apply`：∀ {n : ℕ} (i : Fin n), Fin.revPerm i = i.rev
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Fin.image_rev_fun`：image_rev_fun : image (@rev n) = preimage rev
· 使用定理 `Finset.coe_Ici`：coe_Ici (a : α) : (Ici a : Set α) = Set.Ici a
· 使用定理 `Fin.preimage_rev_Ici`：preimage_rev_Ici (i : Fin n) : rev ⁻¹' Ici i = Iic
 i.rev
· 使用定理 `Finset.coe_Iic`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] (a : α), ↑(Finset.Iic a) = Set.Iic a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_revPerm_Ici (i : Fin n) : (Ici i).map revPerm.toEmbedding = Iic i.rev := by
  simp [← coe_inj]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Fin.map_revPerm_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_revPerm_Ioi (i : Fin n) : (Ioi i).map revPerm.toEmbedding = Iio i.rev
参数：i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Fin.revPerm_apply`：∀ {n : ℕ} (i : Fin n), Fin.revPerm i = i.rev
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Fin.image_rev_fun`：image_rev_fun : image (@rev n) = preimage rev
· 使用定理 `Finset.coe_Ioi`：coe_Ioi (a : α) : (Ioi a : Set α) = Set.Ioi a
· 使用定理 `Fin.preimage_rev_Ioi`：preimage_rev_Ioi (i : Fin n) : rev ⁻¹' Ioi i = Iio
 i.rev
· 使用定理 `Finset.coe_Iio`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] (a : α), ↑(Finset.Iio a) = Set.Iio a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_revPerm_Ioi (i : Fin n) : (Ioi i).map revPerm.toEmbedding = Iio i.rev := by
  simp [← coe_inj]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Fin.map_revPerm_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_revPerm_Iic (i : Fin n) : (Iic i).map revPerm.toEmbedding = Ici i.rev
参数：i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Fin.revPerm_apply`：∀ {n : ℕ} (i : Fin n), Fin.revPerm i = i.rev
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Fin.image_rev_fun`：image_rev_fun : image (@rev n) = preimage rev
· 使用定理 `Finset.coe_Iic`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] (a : α), ↑(Finset.Iic a) = Set.Iic a
· 使用定理 `Fin.preimage_rev_Iic`：preimage_rev_Iic (i : Fin n) : rev ⁻¹' Iic i = Ici
 i.rev
· 使用定理 `Finset.coe_Ici`：coe_Ici (a : α) : (Ici a : Set α) = Set.Ici a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_revPerm_Iic (i : Fin n) : (Iic i).map revPerm.toEmbedding = Ici i.rev := by
  simp [← coe_inj]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Fin.map_revPerm_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：map_revPerm_Iio (i : Fin n) : (Iio i).map revPerm.toEmbedding = Ioi i.rev
参数：i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Fin.revPerm_apply`：∀ {n : ℕ} (i : Fin n), Fin.revPerm i = i.rev
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Fin.image_rev_fun`：image_rev_fun : image (@rev n) = preimage rev
· 使用定理 `Finset.coe_Iio`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] (a : α), ↑(Finset.Iio a) = Set.Iio a
· 使用定理 `Fin.preimage_rev_Iio`：preimage_rev_Iio (i : Fin n) : rev ⁻¹' Iio i = Ioi
 i.rev
· 使用定理 `Finset.coe_Ioi`：coe_Ioi (a : α) : (Ioi a : Set α) = Set.Ioi a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_revPerm_Iio (i : Fin n) : (Iio i).map revPerm.toEmbedding = Ioi i.rev := by
  simp [← coe_inj]

end rev

/-!
### Cardinalities of the intervals
-/

section card

@[simp]
/-
**Fin.card_Icc** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：card_Icc : #(Icc a b) = b + 1 - a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.card_Icc`：∀ (a b : ℕ), (Finset.Icc a b).card = b + 1 - a
· 使用定理 `Fin.map_valEmbedding_Icc`：map_valEmbedding_Icc : (Icc a b).map Fin.valEm
bedding = Icc (a : Nat) b
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
-/
lemma card_Icc : #(Icc a b) = b + 1 - a := by rw [← Nat.card_Icc, ← map_valEmbedding_Icc, card_map]

@[simp]
/-
**Fin.card_Ico** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：card_Ico : #(Ico a b) = b - a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.card_Ico`：∀ (a b : ℕ), (Finset.Ico a b).card = b - a
· 使用定理 `Fin.map_valEmbedding_Ico`：map_valEmbedding_Ico : (Ico a b).map Fin.valEm
bedding = Ico (a : Nat) b
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
-/
lemma card_Ico : #(Ico a b) = b - a := by rw [← Nat.card_Ico, ← map_valEmbedding_Ico, card_map]

@[simp]
/-
**Fin.card_Ioc** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：card_Ioc : #(Ioc a b) = b - a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.card_Ioc`：∀ (a b : ℕ), (Finset.Ioc a b).card = b - a
· 使用定理 `Fin.map_valEmbedding_Ioc`：map_valEmbedding_Ioc : (Ioc a b).map Fin.valEm
bedding = Ioc (a : Nat) b
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
-/
lemma card_Ioc : #(Ioc a b) = b - a := by rw [← Nat.card_Ioc, ← map_valEmbedding_Ioc, card_map]

@[simp]
/-
**Fin.card_Ioo** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：card_Ioo : #(Ioo a b) = b - a - 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.card_Ioo`：∀ (a b : ℕ), (Finset.Ioo a b).card = b - a - 1
· 使用定理 `Fin.map_valEmbedding_Ioo`：map_valEmbedding_Ioo : (Ioo a b).map Fin.valEm
bedding = Ioo (a : Nat) b
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
-/
lemma card_Ioo : #(Ioo a b) = b - a - 1 := by rw [← Nat.card_Ioo, ← map_valEmbedding_Ioo, card_map]

@[simp]
/-
**Fin.card_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：card_uIcc : #(uIcc a b) = (b - a : Int).natAbs + 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.card_uIcc`：card_uIcc : #(uIcc a b) = (b - a : Int).natAbs + 1
· 使用定理 `Fin.map_valEmbedding_uIcc`：map_valEmbedding_uIcc : (uIcc a b).map valEmb
edding = uIcc (a : Nat) b
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
-/
theorem card_uIcc : #(uIcc a b) = (b - a : ℤ).natAbs + 1 := by
  rw [← Nat.card_uIcc, ← map_valEmbedding_uIcc, card_map]

@[simp]
/-
**Fin.card_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：card_Ici : #(Ici a) = n - a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_Ico`：mem_Ico : x in Ico a b ↔ a <= x ∧ x < b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.attachFin_Ico_eq_Ici`：attachFin_Ico_eq_Ici : attachFin (Ico a n) (fu
n _x hx => (mem_Ico.mp hx).2) = Ici a
· 使用定理 `Finset.card_attachFin`：card_attachFin (s : Finset Nat) (h : forall m in 
s, m < n) : (s.attachFin h).card = s.card
· 使用定理 `Nat.card_Ico`：∀ (a b : ℕ), (Finset.Ico a b).card = b - a
-/
theorem card_Ici : #(Ici a) = n - a := by
  rw [← attachFin_Ico_eq_Ici, card_attachFin, Nat.card_Ico]

@[simp]
/-
**Fin.card_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：card_Ioi : #(Ioi a) = n - 1 - a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用定理 `Fin.map_valEmbedding_Ioi`：map_valEmbedding_Ioi : (Ioi a).map Fin.valEmbe
dding = Ioo (a : Nat) n
· 使用定理 `Nat.card_Ioo`：∀ (a b : ℕ), (Finset.Ioo a b).card = b - a - 1
· 使用定理 `Nat.sub_right_comm`：∀ (m n k : ℕ), m - n - k = m - k - n
-/
theorem card_Ioi : #(Ioi a) = n - 1 - a := by
  rw [← card_map, map_valEmbedding_Ioi, Nat.card_Ioo, Nat.sub_right_comm]

@[simp]
/-
**Fin.card_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：card_Iic : #(Iic b) = b + 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Nat.card_Iic`：card_Iic : #(Iic b) = b + 1
· 使用定理 `Fin.map_valEmbedding_Iic`：map_valEmbedding_Iic : (Iic a).map Fin.valEmbe
dding = Iic (a : Nat)
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
-/
theorem card_Iic : #(Iic b) = b + 1 := by rw [← Nat.card_Iic b, ← map_valEmbedding_Iic, card_map]

@[simp]
/-
**Fin.card_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：card_Iio : #(Iio b) = b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.card_Iio`：card_Iio : #(Iio b) = b
· 使用定理 `Fin.map_valEmbedding_Iio`：map_valEmbedding_Iio : (Iio a).map Fin.valEmbe
dding = Iio (a : Nat)
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
-/
theorem card_Iio : #(Iio b) = b := by rw [← Nat.card_Iio b, ← map_valEmbedding_Iio, card_map]

end card

/-! ### Perturbations of endpoints by one -/

/-
Note: the `haveI`s in the statements below are needed for `0` and `1`
to be defined in `Fin n`. One could instead add `[NeZero n]` at the
top of this section, but then this instance would be required to
rewrite using the lemmas.
-/

section pm_one

/-
**Fin.Iio_add_one_eq_Iic** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：Iio_add_one_eq_Iic {n : Nat} {b : Fin n} (hb : b + 1 < n) : haveI
参数：hb : b + 1 < n。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Iio_add_one_eq_Iic {n : ℕ} {b : Fin n} (hb : b + 1 < n) :
    haveI := b.neZero
    Iio (b + 1) = Iic b := by
  grind [= Fin.lt_def, = Fin.le_def, = Fin.val_add_one_of_lt']
/-
**Fin.Iic_sub_one_eq_Iio** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：Iic_sub_one_eq_Iio {n : Nat} {b : Fin n} : haveI
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Iic_sub_one_eq_Iio {n : ℕ} {b : Fin n} :
    haveI := b.neZero
    (hb : 0 < b) → Iic (b - 1) = Iio b := by
  grind [= Fin.val_sub_one_of_ne_zero]
/-
**Fin.Ici_add_one_eq_Ioi** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：Ici_add_one_eq_Ioi {n : Nat} {a : Fin n} (ha : a + 1 < n) : haveI
参数：ha : a + 1 < n。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Ici_add_one_eq_Ioi {n : ℕ} {a : Fin n} (ha : a + 1 < n) :
    haveI := a.neZero
    Ici (a + 1) = Ioi a := by
  grind [= Fin.le_def, = Fin.val_add_one_of_lt']
/-
**Fin.Ioi_sub_one_eq_Ici** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：Ioi_sub_one_eq_Ici {n : Nat} {a : Fin n} : haveI
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Ioi_sub_one_eq_Ici {n : ℕ} {a : Fin n} :
    haveI := a.neZero
    (ha : 0 < a) → Ioi (a - 1) = Ici a := by
  grind [= Fin.lt_def, = Fin.le_def, = Fin.val_sub_one_of_ne_zero]
/-
**Fin.Ioc_sub_one_eq_Icc** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：Ioc_sub_one_eq_Icc {n : Nat} {a b : Fin n} : haveI
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Ioc_sub_one_eq_Icc {n : ℕ} {a b : Fin n} :
    haveI := a.neZero
    (ha : 0 < a) → Ioc (a - 1) b = Icc a b := by
  grind [= Fin.lt_def, = Fin.le_def, = Fin.val_sub_one_of_ne_zero]
/-
**Fin.Icc_add_one_eq_Ioc** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：Icc_add_one_eq_Ioc {n : Nat} {a b : Fin n} (ha : a + 1 < n) : haveI
参数：ha : a + 1 < n。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Icc_add_one_eq_Ioc {n : ℕ} {a b : Fin n} (ha : a + 1 < n) :
    haveI := a.neZero
    Icc (a + 1) b = Ioc a b := by
  grind [= Fin.lt_def, = Fin.le_def, = Fin.val_add_one_of_lt']
/-
**Fin.Ioo_sub_one_eq_Ico** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：Ioo_sub_one_eq_Ico {n : Nat} {a b : Fin n} : haveI
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Ioo_sub_one_eq_Ico {n : ℕ} {a b : Fin n} :
    haveI := a.neZero
    (ha : 0 < a) → Ioo (a - 1) b = Ico a b := by
  grind [= Fin.lt_def, = Fin.le_def, = Fin.val_sub_one_of_ne_zero]
/-
**Fin.Ico_add_one_eq_Ioo** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：Ico_add_one_eq_Ioo {n : Nat} {a b : Fin n} (ha : a + 1 < n) : haveI
参数：ha : a + 1 < n。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Ico_add_one_eq_Ioo {n : ℕ} {a b : Fin n} (ha : a + 1 < n) :
    haveI := a.neZero
    Ico (a + 1) b = Ioo a b := by
  grind [= Fin.lt_def, = Fin.le_def, = Fin.val_add_one_of_lt']
/-
**Fin.Icc_sub_one_eq_Ico** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：Icc_sub_one_eq_Ico {n : Nat} {a b : Fin n} : haveI
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Icc_sub_one_eq_Ico {n : ℕ} {a b : Fin n} :
    haveI := a.neZero
    (hb : 0 < b) → Icc a (b - 1) = Ico a b := by
  grind [= Fin.lt_def, = Fin.le_def, = Fin.val_sub_one_of_ne_zero]
/-
**Fin.Ico_add_one_eq_Icc** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：Ico_add_one_eq_Icc {n : Nat} {a b : Fin n} (hb : b + 1 < n) : haveI
参数：hb : b + 1 < n。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Ico_add_one_eq_Icc {n : ℕ} {a b : Fin n} (hb : b + 1 < n) :
    haveI := a.neZero
    Ico a (b + 1) = Icc a b := by
  grind [= Fin.lt_def, = Fin.le_def, = Fin.val_add_one_of_lt']
/-
**Fin.Ioc_sub_one_eq_Ioo** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：Ioc_sub_one_eq_Ioo {n : Nat} {a b : Fin n} : haveI
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Ioc_sub_one_eq_Ioo {n : ℕ} {a b : Fin n} :
    haveI := a.neZero
    (hb : 0 < b) → Ioc a (b - 1) = Ioo a b := by
  grind [= Fin.lt_def, = Fin.le_def, = Fin.val_sub_one_of_ne_zero]
/-
**Fin.Ioo_add_one_eq_Ioc** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：Ioo_add_one_eq_Ioc {n : Nat} {a b : Fin n} (hb : b + 1 < n) : haveI
参数：hb : b + 1 < n。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Ioo_add_one_eq_Ioc {n : ℕ} {a b : Fin n} (hb : b + 1 < n) :
    haveI := a.neZero
    Ioo a (b + 1) = Ioc a b := by
  grind [= Fin.lt_def, = Fin.le_def, = Fin.val_add_one_of_lt']

end pm_one

end Fin

