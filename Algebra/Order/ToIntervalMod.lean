/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Algebra.Group.ModEq
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Data.Int.SuccPred
public import Mathlib.Order.Circular
import Mathlib.Algebra.Order.Interval.Set.Group
import Mathlib.GroupTheory.QuotientGroup.ModEq

/-!
# Reducing to an interval modulo its length

This file defines operations that reduce a number (in an archimedean linearly ordered abelian group)
to a number in a given interval, modulo the length of that interval.

## Main definitions

* `toIcoDiv hp a b` (where `hp : 0 < p`): The unique integer such that this multiple of `p`,
  subtracted from `b`, is in `Ico a (a + p)`.
* `toIcoMod hp a b` (where `hp : 0 < p`): Reduce `b` to the interval `Ico a (a + p)`.
* `toIocDiv hp a b` (where `hp : 0 < p`): The unique integer such that this multiple of `p`,
  subtracted from `b`, is in `Ioc a (a + p)`.
* `toIocMod hp a b` (where `hp : 0 < p`): Reduce `b` to the interval `Ioc a (a + p)`.
-/

@[expose] public section

assert_not_exists TwoSidedIdeal

noncomputable section

section LinearOrderedAddCommGroup

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

section
include hp

/--
The unique integer such that this multiple of `p`, subtracted from `b`, is in `Ico a (a + p)`. -/
/-
**toIcoDiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：toIcoDiv (a b : α) : Int
参数：a b : α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `existsUnique_sub_zsmul_mem_Ico`：∀ {G : Type u_1} [inst : AddCommGroup G]
 [inst_1 : LinearOrder G] [IsOrderedAddMonoid G] [Archimedean G] {a : G},   0 < 
a → ∀ (b c : G), ∃! …

--- 原说明 ---
The unique integer such that this multiple of `p`, subtracted from `b`, is in `I
co a (a + p)`.
-/
def toIcoDiv (a b : α) : ℤ :=
  (existsUnique_sub_zsmul_mem_Ico hp b a).choose
/-
**sub_toIcoDiv_zsmul_mem_Ico** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sub_toIcoDiv_zsmul_mem_Ico (a b : α) : b - toIcoDiv hp a b • p in Set.Ico 
a (a + p)
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `existsUnique_sub_zsmul_mem_Ico`：∀ {G : Type u_1} [inst : AddCommGroup G]
 [inst_1 : LinearOrder G] [IsOrderedAddMonoid G] [Archimedean G] {a : G},   0 < 
a → ∀ (b c : G), ∃! …
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem sub_toIcoDiv_zsmul_mem_Ico (a b : α) : b - toIcoDiv hp a b • p ∈ Set.Ico a (a + p) :=
  (existsUnique_sub_zsmul_mem_Ico hp b a).choose_spec.1
/-
**toIcoDiv_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoDiv_eq_iff : toIcoDiv hp a b = n ↔ b - n • p in Set.Ico a (a + p)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ExistsUnique.choose_eq_iff`：ExistsUnique.choose_eq_iff {p : α -> Prop} {
a : α} (h : exists! x, p x) : h.choose = a ↔ p a
· 使用定理 `existsUnique_sub_zsmul_mem_Ico`：∀ {G : Type u_1} [inst : AddCommGroup G]
 [inst_1 : LinearOrder G] [IsOrderedAddMonoid G] [Archimedean G] {a : G},   0 < 
a → ∀ (b c : G), ∃! …
-/
theorem toIcoDiv_eq_iff : toIcoDiv hp a b = n ↔ b - n • p ∈ Set.Ico a (a + p) :=
  (existsUnique_sub_zsmul_mem_Ico hp b a).choose_eq_iff

alias ⟨_, toIcoDiv_eq_of_sub_zsmul_mem_Ico⟩ := toIcoDiv_eq_iff

/--
The unique integer such that this multiple of `p`, subtracted from `b`, is in `Ioc a (a + p)`. -/
/-
**toIocDiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：toIocDiv (a b : α) : Int
参数：a b : α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `existsUnique_sub_zsmul_mem_Ioc`：∀ {G : Type u_1} [inst : AddCommGroup G]
 [inst_1 : LinearOrder G] [IsOrderedAddMonoid G] [Archimedean G] {a : G},   0 < 
a → ∀ (b c : G), ∃! …

--- 原说明 ---
The unique integer such that this multiple of `p`, subtracted from `b`, is in `I
oc a (a + p)`.
-/
def toIocDiv (a b : α) : ℤ :=
  (existsUnique_sub_zsmul_mem_Ioc hp b a).choose
/-
**sub_toIocDiv_zsmul_mem_Ioc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sub_toIocDiv_zsmul_mem_Ioc (a b : α) : b - toIocDiv hp a b • p in Set.Ioc 
a (a + p)
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `existsUnique_sub_zsmul_mem_Ioc`：∀ {G : Type u_1} [inst : AddCommGroup G]
 [inst_1 : LinearOrder G] [IsOrderedAddMonoid G] [Archimedean G] {a : G},   0 < 
a → ∀ (b c : G), ∃! …
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem sub_toIocDiv_zsmul_mem_Ioc (a b : α) : b - toIocDiv hp a b • p ∈ Set.Ioc a (a + p) :=
  (existsUnique_sub_zsmul_mem_Ioc hp b a).choose_spec.1
/-
**toIocDiv_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocDiv_eq_iff : toIocDiv hp a b = n ↔ b - n • p in Set.Ioc a (a + p)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ExistsUnique.choose_eq_iff`：ExistsUnique.choose_eq_iff {p : α -> Prop} {
a : α} (h : exists! x, p x) : h.choose = a ↔ p a
· 使用定理 `existsUnique_sub_zsmul_mem_Ioc`：∀ {G : Type u_1} [inst : AddCommGroup G]
 [inst_1 : LinearOrder G] [IsOrderedAddMonoid G] [Archimedean G] {a : G},   0 < 
a → ∀ (b c : G), ∃! …
-/
theorem toIocDiv_eq_iff : toIocDiv hp a b = n ↔ b - n • p ∈ Set.Ioc a (a + p) :=
  (existsUnique_sub_zsmul_mem_Ioc hp b a).choose_eq_iff

alias ⟨_, toIocDiv_eq_of_sub_zsmul_mem_Ioc⟩ := toIocDiv_eq_iff

/-- Reduce `b` to the interval `Ico a (a + p)`. -/
/-
**toIcoMod** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：toIcoMod (a b : α) : α
参数：a b : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reduce `b` to the interval `Ico a (a + p)`.
-/
def toIcoMod (a b : α) : α :=
  b - toIcoDiv hp a b • p

/-- Reduce `b` to the interval `Ioc a (a + p)`. -/
/-
**toIocMod** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：toIocMod (a b : α) : α
参数：a b : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reduce `b` to the interval `Ioc a (a + p)`.
-/
def toIocMod (a b : α) : α :=
  b - toIocDiv hp a b • p
/-
**toIcoMod_mem_Ico** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoMod_mem_Ico (a b : α) : toIcoMod hp a b in Set.Ico a (a + p)
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sub_toIcoDiv_zsmul_mem_Ico`：sub_toIcoDiv_zsmul_mem_Ico (a b : α) : b - t
oIcoDiv hp a b • p in Set.Ico a (a + p)
-/
theorem toIcoMod_mem_Ico (a b : α) : toIcoMod hp a b ∈ Set.Ico a (a + p) :=
  sub_toIcoDiv_zsmul_mem_Ico hp a b
/-
**toIcoMod_mem_Ico'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoMod_mem_Ico' (b : α) : toIcoMod hp 0 b in Set.Ico 0 p
参数：b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `toIcoMod_mem_Ico`：toIcoMod_mem_Ico (a b : α) : toIcoMod hp a b in Set.Ic
o a (a + p)
-/
theorem toIcoMod_mem_Ico' (b : α) : toIcoMod hp 0 b ∈ Set.Ico 0 p := by
  convert! toIcoMod_mem_Ico hp 0 b
  exact (zero_add p).symm
/-
**toIocMod_mem_Ioc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocMod_mem_Ioc (a b : α) : toIocMod hp a b in Set.Ioc a (a + p)
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sub_toIocDiv_zsmul_mem_Ioc`：sub_toIocDiv_zsmul_mem_Ioc (a b : α) : b - t
oIocDiv hp a b • p in Set.Ioc a (a + p)
-/
theorem toIocMod_mem_Ioc (a b : α) : toIocMod hp a b ∈ Set.Ioc a (a + p) :=
  sub_toIocDiv_zsmul_mem_Ioc hp a b
/-
**left_le_toIcoMod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：left_le_toIcoMod (a b : α) : a <= toIcoMod hp a b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_Ico`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.I
co a b ↔ a ≤ x ∧ x < b
· 使用定理 `toIcoMod_mem_Ico`：toIcoMod_mem_Ico (a b : α) : toIcoMod hp a b in Set.Ic
o a (a + p)
-/
theorem left_le_toIcoMod (a b : α) : a ≤ toIcoMod hp a b :=
  (Set.mem_Ico.1 (toIcoMod_mem_Ico hp a b)).1
/-
**left_lt_toIocMod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：left_lt_toIocMod (a b : α) : a < toIocMod hp a b
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_Ioc`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.I
oc a b ↔ a < x ∧ x ≤ b
· 使用定理 `toIocMod_mem_Ioc`：toIocMod_mem_Ioc (a b : α) : toIocMod hp a b in Set.Io
c a (a + p)
-/
theorem left_lt_toIocMod (a b : α) : a < toIocMod hp a b :=
  (Set.mem_Ioc.1 (toIocMod_mem_Ioc hp a b)).1
/-
**toIcoMod_lt_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoMod_lt_right (a b : α) : toIcoMod hp a b < a + p
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_Ico`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.I
co a b ↔ a ≤ x ∧ x < b
· 使用定理 `toIcoMod_mem_Ico`：toIcoMod_mem_Ico (a b : α) : toIcoMod hp a b in Set.Ic
o a (a + p)
-/
theorem toIcoMod_lt_right (a b : α) : toIcoMod hp a b < a + p :=
  (Set.mem_Ico.1 (toIcoMod_mem_Ico hp a b)).2
/-
**toIocMod_le_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocMod_le_right (a b : α) : toIocMod hp a b <= a + p
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_Ioc`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.I
oc a b ↔ a < x ∧ x ≤ b
· 使用定理 `toIocMod_mem_Ioc`：toIocMod_mem_Ioc (a b : α) : toIocMod hp a b in Set.Io
c a (a + p)
-/
theorem toIocMod_le_right (a b : α) : toIocMod hp a b ≤ a + p :=
  (Set.mem_Ioc.1 (toIocMod_mem_Ioc hp a b)).2

@[simp]
/-
**self_sub_toIcoDiv_zsmul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：self_sub_toIcoDiv_zsmul (a b : α) : b - toIcoDiv hp a b • p = toIcoMod hp 
a b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem self_sub_toIcoDiv_zsmul (a b : α) : b - toIcoDiv hp a b • p = toIcoMod hp a b :=
  rfl

@[simp]
/-
**self_sub_toIocDiv_zsmul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：self_sub_toIocDiv_zsmul (a b : α) : b - toIocDiv hp a b • p = toIocMod hp 
a b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem self_sub_toIocDiv_zsmul (a b : α) : b - toIocDiv hp a b • p = toIocMod hp a b :=
  rfl

@[simp]
/-
**toIcoDiv_zsmul_sub_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoDiv_zsmul_sub_self (a b : α) : toIcoDiv hp a b • p - b = -toIcoMod hp
 a b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIcoMod.eq_1`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : Linear
Order α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p : α} (hp : 0 
< p…
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
-/
theorem toIcoDiv_zsmul_sub_self (a b : α) : toIcoDiv hp a b • p - b = -toIcoMod hp a b := by
  rw [toIcoMod, neg_sub]

@[simp]
/-
**toIocDiv_zsmul_sub_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocDiv_zsmul_sub_self (a b : α) : toIocDiv hp a b • p - b = -toIocMod hp
 a b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIocMod.eq_1`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : Linear
Order α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p : α} (hp : 0 
< p…
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
-/
theorem toIocDiv_zsmul_sub_self (a b : α) : toIocDiv hp a b • p - b = -toIocMod hp a b := by
  rw [toIocMod, neg_sub]

@[simp]
/-
**toIcoMod_sub_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoMod_sub_self (a b : α) : toIcoMod hp a b - b = -toIcoDiv hp a b • p
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIcoMod.eq_1`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : Linear
Order α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p : α} (hp : 0 
< p…
· 使用定理 `sub_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a - b - a = -b
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
-/
theorem toIcoMod_sub_self (a b : α) : toIcoMod hp a b - b = -toIcoDiv hp a b • p := by
  rw [toIcoMod, sub_sub_cancel_left, neg_smul]

@[simp]
/-
**toIocMod_sub_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocMod_sub_self (a b : α) : toIocMod hp a b - b = -toIocDiv hp a b • p
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIocMod.eq_1`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : Linear
Order α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p : α} (hp : 0 
< p…
· 使用定理 `sub_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a - b - a = -b
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
-/
theorem toIocMod_sub_self (a b : α) : toIocMod hp a b - b = -toIocDiv hp a b • p := by
  rw [toIocMod, sub_sub_cancel_left, neg_smul]

@[simp]
/-
**self_sub_toIcoMod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：self_sub_toIcoMod (a b : α) : b - toIcoMod hp a b = toIcoDiv hp a b • p
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIcoMod.eq_1`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : Linear
Order α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p : α} (hp : 0 
< p…
· 使用定理 `sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - 
(a - b) = b
-/
theorem self_sub_toIcoMod (a b : α) : b - toIcoMod hp a b = toIcoDiv hp a b • p := by
  rw [toIcoMod, sub_sub_cancel]

@[simp]
/-
**self_sub_toIocMod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：self_sub_toIocMod (a b : α) : b - toIocMod hp a b = toIocDiv hp a b • p
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIocMod.eq_1`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : Linear
Order α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p : α} (hp : 0 
< p…
· 使用定理 `sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - 
(a - b) = b
-/
theorem self_sub_toIocMod (a b : α) : b - toIocMod hp a b = toIocDiv hp a b • p := by
  rw [toIocMod, sub_sub_cancel]

@[simp]
/-
**toIcoMod_add_toIcoDiv_zsmul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoMod_add_toIcoDiv_zsmul (a b : α) : toIcoMod hp a b + toIcoDiv hp a b 
• p = b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIcoMod.eq_1`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : Linear
Order α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p : α} (hp : 0 
< p…
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
-/
theorem toIcoMod_add_toIcoDiv_zsmul (a b : α) : toIcoMod hp a b + toIcoDiv hp a b • p = b := by
  rw [toIcoMod, sub_add_cancel]

@[simp]
/-
**toIocMod_add_toIocDiv_zsmul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocMod_add_toIocDiv_zsmul (a b : α) : toIocMod hp a b + toIocDiv hp a b 
• p = b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIocMod.eq_1`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : Linear
Order α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p : α} (hp : 0 
< p…
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
-/
theorem toIocMod_add_toIocDiv_zsmul (a b : α) : toIocMod hp a b + toIocDiv hp a b • p = b := by
  rw [toIocMod, sub_add_cancel]

@[simp]
/-
**toIcoDiv_zsmul_sub_toIcoMod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoDiv_zsmul_sub_toIcoMod (a b : α) : toIcoDiv hp a b • p + toIcoMod hp 
a b = b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `toIcoMod_add_toIcoDiv_zsmul`：toIcoMod_add_toIcoDiv_zsmul (a b : α) : toI
coMod hp a b + toIcoDiv hp a b • p = b
-/
theorem toIcoDiv_zsmul_sub_toIcoMod (a b : α) : toIcoDiv hp a b • p + toIcoMod hp a b = b := by
  rw [add_comm, toIcoMod_add_toIcoDiv_zsmul]

@[simp]
/-
**toIocDiv_zsmul_sub_toIocMod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocDiv_zsmul_sub_toIocMod (a b : α) : toIocDiv hp a b • p + toIocMod hp 
a b = b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `toIocMod_add_toIocDiv_zsmul`：toIocMod_add_toIocDiv_zsmul (a b : α) : toI
ocMod hp a b + toIocDiv hp a b • p = b
-/
theorem toIocDiv_zsmul_sub_toIocMod (a b : α) : toIocDiv hp a b • p + toIocMod hp a b = b := by
  rw [add_comm, toIocMod_add_toIocDiv_zsmul]
/-
**toIcoMod_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoMod_eq_iff : toIcoMod hp a b = c ↔ c in Set.Ico a (a + p) ∧ exists z 
: Int, b = c + z • p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `toIcoMod_mem_Ico`：toIcoMod_mem_Ico (a b : α) : toIcoMod hp a b in Set.Ic
o a (a + p)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `toIcoMod_add_toIcoDiv_zsmul`：toIcoMod_add_toIcoDiv_zsmul (a b : α) : toI
coMod hp a b + toIcoDiv hp a b • p = b
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `toIcoDiv_eq_of_sub_zsmul_mem_Ico`：∀ {α : Type u_1} [inst : AddCommGroup 
α] [inst_1 : LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]
   {p : α} (hp : 0 < p…
· 使用定理 `toIcoMod.eq_1`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : Linear
Order α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p : α} (hp : 0 
< p…
-/
theorem toIcoMod_eq_iff : toIcoMod hp a b = c ↔ c ∈ Set.Ico a (a + p) ∧ ∃ z : ℤ, b = c + z • p := by
  refine
    ⟨fun h =>
      ⟨h ▸ toIcoMod_mem_Ico hp a b, toIcoDiv hp a b, h ▸ (toIcoMod_add_toIcoDiv_zsmul _ _ _).symm⟩,
      ?_⟩
  simp_rw [← @sub_eq_iff_eq_add]
  rintro ⟨hc, n, rfl⟩
  rw [← toIcoDiv_eq_of_sub_zsmul_mem_Ico hp hc, toIcoMod]
/-
**toIocMod_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocMod_eq_iff : toIocMod hp a b = c ↔ c in Set.Ioc a (a + p) ∧ exists z 
: Int, b = c + z • p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `toIocMod_mem_Ioc`：toIocMod_mem_Ioc (a b : α) : toIocMod hp a b in Set.Io
c a (a + p)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `toIocMod_add_toIocDiv_zsmul`：toIocMod_add_toIocDiv_zsmul (a b : α) : toI
ocMod hp a b + toIocDiv hp a b • p = b
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `toIocDiv_eq_of_sub_zsmul_mem_Ioc`：∀ {α : Type u_1} [inst : AddCommGroup 
α] [inst_1 : LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]
   {p : α} (hp : 0 < p…
· 使用定理 `toIocMod.eq_1`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : Linear
Order α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p : α} (hp : 0 
< p…
-/
theorem toIocMod_eq_iff : toIocMod hp a b = c ↔ c ∈ Set.Ioc a (a + p) ∧ ∃ z : ℤ, b = c + z • p := by
  refine
    ⟨fun h =>
      ⟨h ▸ toIocMod_mem_Ioc hp a b, toIocDiv hp a b, h ▸ (toIocMod_add_toIocDiv_zsmul hp _ _).symm⟩,
      ?_⟩
  simp_rw [← @sub_eq_iff_eq_add]
  rintro ⟨hc, n, rfl⟩
  rw [← toIocDiv_eq_of_sub_zsmul_mem_Ioc hp hc, toIocMod]

@[simp]
/-
**toIcoDiv_apply_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoDiv_apply_left (a : α) : toIcoDiv hp a a = 0
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `toIcoDiv_eq_of_sub_zsmul_mem_Ico`：∀ {α : Type u_1} [inst : AddCommGroup 
α] [inst_1 : LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]
   {p : α} (hp : 0 < p…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem toIcoDiv_apply_left (a : α) : toIcoDiv hp a a = 0 :=
  toIcoDiv_eq_of_sub_zsmul_mem_Ico hp <| by simp [hp]

@[simp]
/-
**toIocDiv_apply_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocDiv_apply_left (a : α) : toIocDiv hp a a = -1
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `toIocDiv_eq_of_sub_zsmul_mem_Ioc`：∀ {α : Type u_1} [inst : AddCommGroup 
α] [inst_1 : LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]
   {p : α} (hp : 0 < p…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem toIocDiv_apply_left (a : α) : toIocDiv hp a a = -1 :=
  toIocDiv_eq_of_sub_zsmul_mem_Ioc hp <| by simp [hp]

@[simp]
/-
**toIcoMod_apply_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoMod_apply_left (a : α) : toIcoMod hp a a = a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIcoMod_eq_iff`：toIcoMod_eq_iff : toIcoMod hp a b = c ↔ c in Set.Ico a 
(a + p) ∧ exists z : Int, b = c + z • p
· 使用定理 `Set.left_mem_Ico`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ Se
t.Ico a b ↔ a < b
· 使用定理 `lt_add_of_pos_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : 
LT α] [AddLeftStrictMono α] (a : α) {b : α}, 0 < b → a < a + b
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toIcoMod_apply_left (a : α) : toIcoMod hp a a = a := by
  rw [toIcoMod_eq_iff hp, Set.left_mem_Ico]
  exact ⟨lt_add_of_pos_right _ hp, 0, by simp⟩

@[simp]
/-
**toIocMod_apply_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocMod_apply_left (a : α) : toIocMod hp a a = a + p
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIocMod_eq_iff`：toIocMod_eq_iff : toIocMod hp a b = c ↔ c in Set.Ioc a 
(a + p) ∧ exists z : Int, b = c + z • p
· 使用定理 `Set.right_mem_Ioc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ S
et.Ioc b a ↔ b < a
· 使用定理 `lt_add_of_pos_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : 
LT α] [AddLeftStrictMono α] (a : α) {b : α}, 0 < b → a < a + b
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `add_neg_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b + -b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toIocMod_apply_left (a : α) : toIocMod hp a a = a + p := by
  rw [toIocMod_eq_iff hp, Set.right_mem_Ioc]
  exact ⟨lt_add_of_pos_right _ hp, -1, by simp⟩
/-
**toIcoDiv_apply_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoDiv_apply_right (a : α) : toIcoDiv hp a (a + p) = 1
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `toIcoDiv_eq_of_sub_zsmul_mem_Ico`：∀ {α : Type u_1} [inst : AddCommGroup 
α] [inst_1 : LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]
   {p : α} (hp : 0 < p…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem toIcoDiv_apply_right (a : α) : toIcoDiv hp a (a + p) = 1 :=
  toIcoDiv_eq_of_sub_zsmul_mem_Ico hp <| by simp [hp]
/-
**toIocDiv_apply_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocDiv_apply_right (a : α) : toIocDiv hp a (a + p) = 0
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `toIocDiv_eq_of_sub_zsmul_mem_Ioc`：∀ {α : Type u_1} [inst : AddCommGroup 
α] [inst_1 : LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]
   {p : α} (hp : 0 < p…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem toIocDiv_apply_right (a : α) : toIocDiv hp a (a + p) = 0 :=
  toIocDiv_eq_of_sub_zsmul_mem_Ioc hp <| by simp [hp]
/-
**toIcoMod_apply_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoMod_apply_right (a : α) : toIcoMod hp a (a + p) = a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIcoMod_eq_iff`：toIcoMod_eq_iff : toIcoMod hp a b = c ↔ c in Set.Ico a 
(a + p) ∧ exists z : Int, b = c + z • p
· 使用定理 `Set.left_mem_Ico`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ Se
t.Ico a b ↔ a < b
· 使用定理 `lt_add_of_pos_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : 
LT α] [AddLeftStrictMono α] (a : α) {b : α}, 0 < b → a < a + b
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toIcoMod_apply_right (a : α) : toIcoMod hp a (a + p) = a := by
  rw [toIcoMod_eq_iff hp, Set.left_mem_Ico]
  exact ⟨lt_add_of_pos_right _ hp, 1, by simp⟩
/-
**toIocMod_apply_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocMod_apply_right (a : α) : toIocMod hp a (a + p) = a + p
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIocMod_eq_iff`：toIocMod_eq_iff : toIocMod hp a b = c ↔ c in Set.Ioc a 
(a + p) ∧ exists z : Int, b = c + z • p
· 使用定理 `Set.right_mem_Ioc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ S
et.Ioc b a ↔ b < a
· 使用定理 `lt_add_of_pos_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : 
LT α] [AddLeftStrictMono α] (a : α) {b : α}, 0 < b → a < a + b
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toIocMod_apply_right (a : α) : toIocMod hp a (a + p) = a + p := by
  rw [toIocMod_eq_iff hp, Set.right_mem_Ioc]
  exact ⟨lt_add_of_pos_right _ hp, 0, by simp⟩

@[simp]
/-
**toIcoDiv_add_zsmul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoDiv_add_zsmul (a b : α) (m : Int) : toIcoDiv hp a (b + m • p) = toIco
Div hp a b + m
参数：a b : α；m : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `toIcoDiv_eq_of_sub_zsmul_mem_Ico`：∀ {α : Type u_1} [inst : AddCommGroup 
α] [inst_1 : LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]
   {p : α} (hp : 0 < p…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `add_sub_add_right_eq_sub`：∀ {G : Type u_3} [inst : AddGroup G] (a b c : 
G), a + c - (b + c) = a - b
· 使用定理 `sub_toIcoDiv_zsmul_mem_Ico`：sub_toIcoDiv_zsmul_mem_Ico (a b : α) : b - t
oIcoDiv hp a b • p in Set.Ico a (a + p)
-/
theorem toIcoDiv_add_zsmul (a b : α) (m : ℤ) : toIcoDiv hp a (b + m • p) = toIcoDiv hp a b + m :=
  toIcoDiv_eq_of_sub_zsmul_mem_Ico hp <| by
    simpa only [add_smul, add_sub_add_right_eq_sub] using sub_toIcoDiv_zsmul_mem_Ico hp a b

@[simp]
/-
**toIcoDiv_add_nsmul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoDiv_add_nsmul (a b : α) (m : Nat) : toIcoDiv hp a (b + m • p) = toIco
Div hp a b + m
参数：a b : α；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIcoDiv.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用定理 `toIcoDiv_add_zsmul`：toIcoDiv_add_zsmul (a b : α) (m : Int) : toIcoDiv hp
 a (b + m • p) = toIcoDiv hp a b + m
-/
theorem toIcoDiv_add_nsmul (a b : α) (m : ℕ) : toIcoDiv hp a (b + m • p) = toIcoDiv hp a b + m :=
  mod_cast toIcoDiv_add_zsmul hp a b m

@[simp]
/-
**toIcoDiv_add_zsmul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoDiv_add_zsmul' (a b : α) (m : Int) : toIcoDiv hp (a + m • p) b = toIc
oDiv hp a b - m
参数：a b : α；m : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `toIcoDiv_eq_of_sub_zsmul_mem_Ico`：∀ {α : Type u_1} [inst : AddCommGroup 
α] [inst_1 : LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]
   {p : α} (hp : 0 < p…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_add`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c : α), 
a - b + c = a - (b - c)
· 使用定理 `add_right_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G)
, a + b + c = a + c + b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `sub_toIcoDiv_zsmul_mem_Ico`：sub_toIcoDiv_zsmul_mem_Ico (a b : α) : b - t
oIcoDiv hp a b • p in Set.Ico a (a + p)
-/
theorem toIcoDiv_add_zsmul' (a b : α) (m : ℤ) :
    toIcoDiv hp (a + m • p) b = toIcoDiv hp a b - m := by
  refine toIcoDiv_eq_of_sub_zsmul_mem_Ico _ ?_
  rw [sub_smul, ← sub_add, add_right_comm]
  simpa using sub_toIcoDiv_zsmul_mem_Ico hp a b

@[simp]
/-
**toIcoDiv_add_nsmul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoDiv_add_nsmul' (a b : α) (m : Nat) : toIcoDiv hp (a + m • p) b = toIc
oDiv hp a b - m
参数：a b : α；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIcoDiv.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用定理 `toIcoDiv_add_zsmul'`：toIcoDiv_add_zsmul' (a b : α) (m : Int) : toIcoDiv 
hp (a + m • p) b = toIcoDiv hp a b - m
-/
theorem toIcoDiv_add_nsmul' (a b : α) (m : ℕ) : toIcoDiv hp (a + m • p) b = toIcoDiv hp a b - m :=
  mod_cast toIcoDiv_add_zsmul' hp a b m

@[simp]
/-
**toIocDiv_add_zsmul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocDiv_add_zsmul (a b : α) (m : Int) : toIocDiv hp a (b + m • p) = toIoc
Div hp a b + m
参数：a b : α；m : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `toIocDiv_eq_of_sub_zsmul_mem_Ioc`：∀ {α : Type u_1} [inst : AddCommGroup 
α] [inst_1 : LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]
   {p : α} (hp : 0 < p…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `add_sub_add_right_eq_sub`：∀ {G : Type u_3} [inst : AddGroup G] (a b c : 
G), a + c - (b + c) = a - b
· 使用定理 `sub_toIocDiv_zsmul_mem_Ioc`：sub_toIocDiv_zsmul_mem_Ioc (a b : α) : b - t
oIocDiv hp a b • p in Set.Ioc a (a + p)
-/
theorem toIocDiv_add_zsmul (a b : α) (m : ℤ) : toIocDiv hp a (b + m • p) = toIocDiv hp a b + m :=
  toIocDiv_eq_of_sub_zsmul_mem_Ioc hp <| by
    simpa only [add_smul, add_sub_add_right_eq_sub] using sub_toIocDiv_zsmul_mem_Ioc hp a b

@[simp]
/-
**toIocDiv_add_nsmul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocDiv_add_nsmul (a b : α) (m : Nat) : toIocDiv hp a (b + m • p) = toIoc
Div hp a b + m
参数：a b : α；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIocDiv.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用定理 `toIocDiv_add_zsmul`：toIocDiv_add_zsmul (a b : α) (m : Int) : toIocDiv hp
 a (b + m • p) = toIocDiv hp a b + m
-/
theorem toIocDiv_add_nsmul (a b : α) (m : ℕ) : toIocDiv hp a (b + m • p) = toIocDiv hp a b + m :=
  mod_cast toIocDiv_add_zsmul hp a b m

@[simp]
/-
**toIocDiv_add_zsmul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocDiv_add_zsmul' (a b : α) (m : Int) : toIocDiv hp (a + m • p) b = toIo
cDiv hp a b - m
参数：a b : α；m : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `toIocDiv_eq_of_sub_zsmul_mem_Ioc`：∀ {α : Type u_1} [inst : AddCommGroup 
α] [inst_1 : LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]
   {p : α} (hp : 0 < p…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_add`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c : α), 
a - b + c = a - (b - c)
· 使用定理 `add_right_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G)
, a + b + c = a + c + b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `sub_toIocDiv_zsmul_mem_Ioc`：sub_toIocDiv_zsmul_mem_Ioc (a b : α) : b - t
oIocDiv hp a b • p in Set.Ioc a (a + p)
-/
theorem toIocDiv_add_zsmul' (a b : α) (m : ℤ) :
    toIocDiv hp (a + m • p) b = toIocDiv hp a b - m := by
  refine toIocDiv_eq_of_sub_zsmul_mem_Ioc _ ?_
  rw [sub_smul, ← sub_add, add_right_comm]
  simpa using sub_toIocDiv_zsmul_mem_Ioc hp a b

@[simp]
/-
**toIocDiv_add_nsmul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocDiv_add_nsmul' (a b : α) (m : Nat) : toIocDiv hp (a + m • p) b = toIo
cDiv hp a b - m
参数：a b : α；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIocDiv.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用定理 `toIocDiv_add_zsmul'`：toIocDiv_add_zsmul' (a b : α) (m : Int) : toIocDiv 
hp (a + m • p) b = toIocDiv hp a b - m
-/
theorem toIocDiv_add_nsmul' (a b : α) (m : ℕ) : toIocDiv hp (a + m • p) b = toIocDiv hp a b - m :=
  mod_cast toIocDiv_add_zsmul' hp a b m

@[simp]
/-
**toIcoDiv_zsmul_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoDiv_zsmul_add (a b : α) (m : Int) : toIcoDiv hp a (m • p + b) = m + t
oIcoDiv hp a b
参数：a b : α；m : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `toIcoDiv_add_zsmul`：toIcoDiv_add_zsmul (a b : α) (m : Int) : toIcoDiv hp
 a (b + m • p) = toIcoDiv hp a b + m
-/
theorem toIcoDiv_zsmul_add (a b : α) (m : ℤ) : toIcoDiv hp a (m • p + b) = m + toIcoDiv hp a b := by
  rw [add_comm, toIcoDiv_add_zsmul, add_comm]

@[simp]
/-
**toIcoDiv_nsmul_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoDiv_nsmul_add (a b : α) (m : Nat) : toIcoDiv hp a (m • p + b) = m + t
oIcoDiv hp a b
参数：a b : α；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIcoDiv.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用定理 `toIcoDiv_zsmul_add`：toIcoDiv_zsmul_add (a b : α) (m : Int) : toIcoDiv hp
 a (m • p + b) = m + toIcoDiv hp a b
-/
theorem toIcoDiv_nsmul_add (a b : α) (m : ℕ) : toIcoDiv hp a (m • p + b) = m + toIcoDiv hp a b :=
  mod_cast toIcoDiv_zsmul_add hp a b m

/-! Note we omit `toIcoDiv_zsmul_add'` as `-m + toIcoDiv hp a b` is not very convenient. -/


@[simp]
/-
**toIocDiv_zsmul_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocDiv_zsmul_add (a b : α) (m : Int) : toIocDiv hp a (m • p + b) = m + t
oIocDiv hp a b
参数：a b : α；m : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `toIocDiv_add_zsmul`：toIocDiv_add_zsmul (a b : α) (m : Int) : toIocDiv hp
 a (b + m • p) = toIocDiv hp a b + m

--- 原说明 ---
Note we omit `toIcoDiv_zsmul_add'` as `-m + toIcoDiv hp a b` is not very conveni
ent.
-/
theorem toIocDiv_zsmul_add (a b : α) (m : ℤ) : toIocDiv hp a (m • p + b) = m + toIocDiv hp a b := by
  rw [add_comm, toIocDiv_add_zsmul, add_comm]

@[simp]
/-
**toIocDiv_nsmul_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocDiv_nsmul_add (a b : α) (m : Nat) : toIocDiv hp a (m • p + b) = m + t
oIocDiv hp a b
参数：a b : α；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIocDiv.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用定理 `toIocDiv_zsmul_add`：toIocDiv_zsmul_add (a b : α) (m : Int) : toIocDiv hp
 a (m • p + b) = m + toIocDiv hp a b
-/
theorem toIocDiv_nsmul_add (a b : α) (m : ℕ) : toIocDiv hp a (m • p + b) = m + toIocDiv hp a b :=
  mod_cast toIocDiv_zsmul_add hp a b m

/-! Note we omit `toIocDiv_zsmul_add'` as `-m + toIocDiv hp a b` is not very convenient. -/


@[simp]
/-
**toIcoDiv_sub_zsmul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoDiv_sub_zsmul (a b : α) (m : Int) : toIcoDiv hp a (b - m • p) = toIco
Div hp a b - m
参数：a b : α；m : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `toIcoDiv_add_zsmul`：toIcoDiv_add_zsmul (a b : α) (m : Int) : toIcoDiv hp
 a (b + m • p) = toIcoDiv hp a b + m

--- 原说明 ---
Note we omit `toIocDiv_zsmul_add'` as `-m + toIocDiv hp a b` is not very conveni
ent.
-/
theorem toIcoDiv_sub_zsmul (a b : α) (m : ℤ) : toIcoDiv hp a (b - m • p) = toIcoDiv hp a b - m := by
  rw [sub_eq_add_neg, ← neg_smul, toIcoDiv_add_zsmul, sub_eq_add_neg]

@[simp]
/-
**toIcoDiv_sub_nsmul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoDiv_sub_nsmul (a b : α) (m : Nat) : toIcoDiv hp a (b - m • p) = toIco
Div hp a b - m
参数：a b : α；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIcoDiv.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用定理 `toIcoDiv_sub_zsmul`：toIcoDiv_sub_zsmul (a b : α) (m : Int) : toIcoDiv hp
 a (b - m • p) = toIcoDiv hp a b - m
-/
theorem toIcoDiv_sub_nsmul (a b : α) (m : ℕ) : toIcoDiv hp a (b - m • p) = toIcoDiv hp a b - m :=
  mod_cast toIcoDiv_sub_zsmul hp a b m

@[simp]
/-
**toIcoDiv_sub_zsmul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoDiv_sub_zsmul' (a b : α) (m : Int) : toIcoDiv hp (a - m • p) b = toIc
oDiv hp a b + m
参数：a b : α；m : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `toIcoDiv_add_zsmul'`：toIcoDiv_add_zsmul' (a b : α) (m : Int) : toIcoDiv 
hp (a + m • p) b = toIcoDiv hp a b - m
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
-/
theorem toIcoDiv_sub_zsmul' (a b : α) (m : ℤ) :
    toIcoDiv hp (a - m • p) b = toIcoDiv hp a b + m := by
  rw [sub_eq_add_neg, ← neg_smul, toIcoDiv_add_zsmul', sub_neg_eq_add]

@[simp]
/-
**toIcoDiv_sub_nsmul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoDiv_sub_nsmul' (a b : α) (m : Nat) : toIcoDiv hp (a - m • p) b = toIc
oDiv hp a b + m
参数：a b : α；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIcoDiv.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用定理 `toIcoDiv_sub_zsmul'`：toIcoDiv_sub_zsmul' (a b : α) (m : Int) : toIcoDiv 
hp (a - m • p) b = toIcoDiv hp a b + m
-/
theorem toIcoDiv_sub_nsmul' (a b : α) (m : ℕ) : toIcoDiv hp (a - m • p) b = toIcoDiv hp a b + m :=
  mod_cast toIcoDiv_sub_zsmul' hp a b m

@[simp]
/-
**toIocDiv_sub_zsmul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocDiv_sub_zsmul (a b : α) (m : Int) : toIocDiv hp a (b - m • p) = toIoc
Div hp a b - m
参数：a b : α；m : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `toIocDiv_add_zsmul`：toIocDiv_add_zsmul (a b : α) (m : Int) : toIocDiv hp
 a (b + m • p) = toIocDiv hp a b + m
-/
theorem toIocDiv_sub_zsmul (a b : α) (m : ℤ) : toIocDiv hp a (b - m • p) = toIocDiv hp a b - m := by
  rw [sub_eq_add_neg, ← neg_smul, toIocDiv_add_zsmul, sub_eq_add_neg]

@[simp]
/-
**toIocDiv_sub_nsmul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocDiv_sub_nsmul (a b : α) (m : Nat) : toIocDiv hp a (b - m • p) = toIoc
Div hp a b - m
参数：a b : α；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIocDiv.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用定理 `toIocDiv_sub_zsmul`：toIocDiv_sub_zsmul (a b : α) (m : Int) : toIocDiv hp
 a (b - m • p) = toIocDiv hp a b - m
-/
theorem toIocDiv_sub_nsmul (a b : α) (m : ℕ) : toIocDiv hp a (b - m • p) = toIocDiv hp a b - m :=
  mod_cast toIocDiv_sub_zsmul hp a b m

@[simp]
/-
**toIocDiv_sub_zsmul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocDiv_sub_zsmul' (a b : α) (m : Int) : toIocDiv hp (a - m • p) b = toIo
cDiv hp a b + m
参数：a b : α；m : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `toIocDiv_add_zsmul'`：toIocDiv_add_zsmul' (a b : α) (m : Int) : toIocDiv 
hp (a + m • p) b = toIocDiv hp a b - m
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
-/
theorem toIocDiv_sub_zsmul' (a b : α) (m : ℤ) :
    toIocDiv hp (a - m • p) b = toIocDiv hp a b + m := by
  rw [sub_eq_add_neg, ← neg_smul, toIocDiv_add_zsmul', sub_neg_eq_add]

@[simp]
/-
**toIocDiv_sub_nsmul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocDiv_sub_nsmul' (a b : α) (m : Nat) : toIocDiv hp (a - m • p) b = toIo
cDiv hp a b + m
参数：a b : α；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIocDiv.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用定理 `toIocDiv_sub_zsmul'`：toIocDiv_sub_zsmul' (a b : α) (m : Int) : toIocDiv 
hp (a - m • p) b = toIocDiv hp a b + m
-/
theorem toIocDiv_sub_nsmul' (a b : α) (m : ℕ) : toIocDiv hp (a - m • p) b = toIocDiv hp a b + m :=
  mod_cast toIocDiv_sub_zsmul' hp a b m

@[simp]
/-
**toIcoDiv_add_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoDiv_add_right (a b : α) : toIcoDiv hp a (b + p) = toIcoDiv hp a b + 1
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIcoDiv.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用定理 `one_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 1 • a = a
· 使用定理 `toIcoDiv_add_zsmul`：toIcoDiv_add_zsmul (a b : α) (m : Int) : toIcoDiv hp
 a (b + m • p) = toIcoDiv hp a b + m
-/
theorem toIcoDiv_add_right (a b : α) : toIcoDiv hp a (b + p) = toIcoDiv hp a b + 1 := by
  simpa only [one_zsmul] using toIcoDiv_add_zsmul hp a b 1

@[simp]
/-
**toIcoDiv_add_right'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoDiv_add_right' (a b : α) : toIcoDiv hp (a + p) b = toIcoDiv hp a b - 
1
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIcoDiv.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用定理 `one_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 1 • a = a
· 使用定理 `toIcoDiv_add_zsmul'`：toIcoDiv_add_zsmul' (a b : α) (m : Int) : toIcoDiv 
hp (a + m • p) b = toIcoDiv hp a b - m
-/
theorem toIcoDiv_add_right' (a b : α) : toIcoDiv hp (a + p) b = toIcoDiv hp a b - 1 := by
  simpa only [one_zsmul] using toIcoDiv_add_zsmul' hp a b 1

@[simp]
/-
**toIocDiv_add_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocDiv_add_right (a b : α) : toIocDiv hp a (b + p) = toIocDiv hp a b + 1
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIocDiv.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用定理 `one_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 1 • a = a
· 使用定理 `toIocDiv_add_zsmul`：toIocDiv_add_zsmul (a b : α) (m : Int) : toIocDiv hp
 a (b + m • p) = toIocDiv hp a b + m
-/
theorem toIocDiv_add_right (a b : α) : toIocDiv hp a (b + p) = toIocDiv hp a b + 1 := by
  simpa only [one_zsmul] using toIocDiv_add_zsmul hp a b 1

@[simp]
/-
**toIocDiv_add_right'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocDiv_add_right' (a b : α) : toIocDiv hp (a + p) b = toIocDiv hp a b - 
1
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIocDiv.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用定理 `one_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 1 • a = a
· 使用定理 `toIocDiv_add_zsmul'`：toIocDiv_add_zsmul' (a b : α) (m : Int) : toIocDiv 
hp (a + m • p) b = toIocDiv hp a b - m
-/
theorem toIocDiv_add_right' (a b : α) : toIocDiv hp (a + p) b = toIocDiv hp a b - 1 := by
  simpa only [one_zsmul] using toIocDiv_add_zsmul' hp a b 1

@[simp]
/-
**toIcoDiv_add_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoDiv_add_left (a b : α) : toIcoDiv hp a (p + b) = toIcoDiv hp a b + 1
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `toIcoDiv_add_right`：toIcoDiv_add_right (a b : α) : toIcoDiv hp a (b + p)
 = toIcoDiv hp a b + 1
-/
theorem toIcoDiv_add_left (a b : α) : toIcoDiv hp a (p + b) = toIcoDiv hp a b + 1 := by
  rw [add_comm, toIcoDiv_add_right]

@[simp]
/-
**toIcoDiv_add_left'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoDiv_add_left' (a b : α) : toIcoDiv hp (p + a) b = toIcoDiv hp a b - 1
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `toIcoDiv_add_right'`：toIcoDiv_add_right' (a b : α) : toIcoDiv hp (a + p)
 b = toIcoDiv hp a b - 1
-/
theorem toIcoDiv_add_left' (a b : α) : toIcoDiv hp (p + a) b = toIcoDiv hp a b - 1 := by
  rw [add_comm, toIcoDiv_add_right']

@[simp]
/-
**toIocDiv_add_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocDiv_add_left (a b : α) : toIocDiv hp a (p + b) = toIocDiv hp a b + 1
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `toIocDiv_add_right`：toIocDiv_add_right (a b : α) : toIocDiv hp a (b + p)
 = toIocDiv hp a b + 1
-/
theorem toIocDiv_add_left (a b : α) : toIocDiv hp a (p + b) = toIocDiv hp a b + 1 := by
  rw [add_comm, toIocDiv_add_right]

@[simp]
/-
**toIocDiv_add_left'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocDiv_add_left' (a b : α) : toIocDiv hp (p + a) b = toIocDiv hp a b - 1
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `toIocDiv_add_right'`：toIocDiv_add_right' (a b : α) : toIocDiv hp (a + p)
 b = toIocDiv hp a b - 1
-/
theorem toIocDiv_add_left' (a b : α) : toIocDiv hp (p + a) b = toIocDiv hp a b - 1 := by
  rw [add_comm, toIocDiv_add_right']

@[simp]
/-
**toIcoDiv_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoDiv_sub (a b : α) : toIcoDiv hp a (b - p) = toIcoDiv hp a b - 1
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIcoDiv.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用定理 `one_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 1 • a = a
· 使用定理 `toIcoDiv_sub_zsmul`：toIcoDiv_sub_zsmul (a b : α) (m : Int) : toIcoDiv hp
 a (b - m • p) = toIcoDiv hp a b - m
-/
theorem toIcoDiv_sub (a b : α) : toIcoDiv hp a (b - p) = toIcoDiv hp a b - 1 := by
  simpa only [one_zsmul] using toIcoDiv_sub_zsmul hp a b 1

@[simp]
/-
**toIcoDiv_sub'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoDiv_sub' (a b : α) : toIcoDiv hp (a - p) b = toIcoDiv hp a b + 1
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIcoDiv.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用定理 `one_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 1 • a = a
· 使用定理 `toIcoDiv_sub_zsmul'`：toIcoDiv_sub_zsmul' (a b : α) (m : Int) : toIcoDiv 
hp (a - m • p) b = toIcoDiv hp a b + m
-/
theorem toIcoDiv_sub' (a b : α) : toIcoDiv hp (a - p) b = toIcoDiv hp a b + 1 := by
  simpa only [one_zsmul] using toIcoDiv_sub_zsmul' hp a b 1

@[simp]
/-
**toIocDiv_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocDiv_sub (a b : α) : toIocDiv hp a (b - p) = toIocDiv hp a b - 1
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIocDiv.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用定理 `one_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 1 • a = a
· 使用定理 `toIocDiv_sub_zsmul`：toIocDiv_sub_zsmul (a b : α) (m : Int) : toIocDiv hp
 a (b - m • p) = toIocDiv hp a b - m
-/
theorem toIocDiv_sub (a b : α) : toIocDiv hp a (b - p) = toIocDiv hp a b - 1 := by
  simpa only [one_zsmul] using toIocDiv_sub_zsmul hp a b 1

@[simp]
/-
**toIocDiv_sub'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocDiv_sub' (a b : α) : toIocDiv hp (a - p) b = toIocDiv hp a b + 1
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIocDiv.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用定理 `one_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 1 • a = a
· 使用定理 `toIocDiv_sub_zsmul'`：toIocDiv_sub_zsmul' (a b : α) (m : Int) : toIocDiv 
hp (a - m • p) b = toIocDiv hp a b + m
-/
theorem toIocDiv_sub' (a b : α) : toIocDiv hp (a - p) b = toIocDiv hp a b + 1 := by
  simpa only [one_zsmul] using toIocDiv_sub_zsmul' hp a b 1
/-
**toIcoDiv_sub_eq_toIcoDiv_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoDiv_sub_eq_toIcoDiv_add (a b c : α) : toIcoDiv hp a (b - c) = toIcoDi
v hp (a + c) b
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `toIcoDiv_eq_of_sub_zsmul_mem_Ico`：∀ {α : Type u_1} [inst : AddCommGroup 
α] [inst_1 : LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]
   {p : α} (hp : 0 < p…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_right_comm`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c
 : α), a - b - c = a - c - b
· 使用定理 `Set.sub_mem_Ico_iff_left`：sub_mem_Ico_iff_left : a - b in Set.Ico c d ↔ 
a in Set.Ico (c + b) (d + b)
· 使用定理 `add_right_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G)
, a + b + c = a + c + b
· 使用定理 `sub_toIcoDiv_zsmul_mem_Ico`：sub_toIcoDiv_zsmul_mem_Ico (a b : α) : b - t
oIcoDiv hp a b • p in Set.Ico a (a + p)
-/
theorem toIcoDiv_sub_eq_toIcoDiv_add (a b c : α) :
    toIcoDiv hp a (b - c) = toIcoDiv hp (a + c) b := by
  apply toIcoDiv_eq_of_sub_zsmul_mem_Ico
  rw [← sub_right_comm, Set.sub_mem_Ico_iff_left, add_right_comm]
  exact sub_toIcoDiv_zsmul_mem_Ico hp (a + c) b
/-
**toIocDiv_sub_eq_toIocDiv_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocDiv_sub_eq_toIocDiv_add (a b c : α) : toIocDiv hp a (b - c) = toIocDi
v hp (a + c) b
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `toIocDiv_eq_of_sub_zsmul_mem_Ioc`：∀ {α : Type u_1} [inst : AddCommGroup 
α] [inst_1 : LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]
   {p : α} (hp : 0 < p…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_right_comm`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c
 : α), a - b - c = a - c - b
· 使用定理 `Set.sub_mem_Ioc_iff_left`：sub_mem_Ioc_iff_left : a - b in Set.Ioc c d ↔ 
a in Set.Ioc (c + b) (d + b)
· 使用定理 `add_right_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G)
, a + b + c = a + c + b
· 使用定理 `sub_toIocDiv_zsmul_mem_Ioc`：sub_toIocDiv_zsmul_mem_Ioc (a b : α) : b - t
oIocDiv hp a b • p in Set.Ioc a (a + p)
-/
theorem toIocDiv_sub_eq_toIocDiv_add (a b c : α) :
    toIocDiv hp a (b - c) = toIocDiv hp (a + c) b := by
  apply toIocDiv_eq_of_sub_zsmul_mem_Ioc
  rw [← sub_right_comm, Set.sub_mem_Ioc_iff_left, add_right_comm]
  exact sub_toIocDiv_zsmul_mem_Ioc hp (a + c) b
/-
**toIcoDiv_sub_eq_toIcoDiv_add'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoDiv_sub_eq_toIcoDiv_add' (a b c : α) : toIcoDiv hp (a - c) b = toIcoD
iv hp a (b + c)
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `toIcoDiv_sub_eq_toIcoDiv_add`：toIcoDiv_sub_eq_toIcoDiv_add (a b c : α) :
 toIcoDiv hp a (b - c) = toIcoDiv hp (a + c) b
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
-/
theorem toIcoDiv_sub_eq_toIcoDiv_add' (a b c : α) :
    toIcoDiv hp (a - c) b = toIcoDiv hp a (b + c) := by
  rw [← sub_neg_eq_add, toIcoDiv_sub_eq_toIcoDiv_add, sub_eq_add_neg]
/-
**toIocDiv_sub_eq_toIocDiv_add'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocDiv_sub_eq_toIocDiv_add' (a b c : α) : toIocDiv hp (a - c) b = toIocD
iv hp a (b + c)
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `toIocDiv_sub_eq_toIocDiv_add`：toIocDiv_sub_eq_toIocDiv_add (a b c : α) :
 toIocDiv hp a (b - c) = toIocDiv hp (a + c) b
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
-/
theorem toIocDiv_sub_eq_toIocDiv_add' (a b c : α) :
    toIocDiv hp (a - c) b = toIocDiv hp a (b + c) := by
  rw [← sub_neg_eq_add, toIocDiv_sub_eq_toIocDiv_add, sub_eq_add_neg]
/-
**toIcoDiv_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoDiv_neg (a b : α) : toIcoDiv hp a (-b) = -(toIocDiv hp (-a) b + 1)
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_eq_iff_eq_neg`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, 
-a = b ↔ a = -b
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `toIocDiv_eq_of_sub_zsmul_mem_Ioc`：∀ {α : Type u_1} [inst : AddCommGroup 
α] [inst_1 : LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]
   {p : α} (hp : 0 < p…
· 使用定理 `sub_toIcoDiv_zsmul_mem_Ico`：sub_toIcoDiv_zsmul_mem_Ico (a b : α) : b - t
oIcoDiv hp a b • p in Set.Ico a (a + p)
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `neg_sub'`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b : α), -
(a - b) = -a - -b
· 使用定理 `neg_lt_neg_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddL
eftStrictMono α] {a b : α} [AddRightStrictMono α],   -a < -b ↔ b < a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `neg_le_neg_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddL
eftMono α] {a b : α} [AddRightMono α], -a ≤ -b ↔ b ≤ a
· 使用定理 `neg_add`：neg_add {R} [CommRing R] {a₁ a₂ b₁ b₂ : R} (_ : -a₁ = b₁) (_ : 
-a₂ = b₂) : -(a₁ + a₂) = b₁ + b₂
· 使用定理 `neg_add_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ -b + b = a
· 使用定理 `toIocDiv_add_right`：toIocDiv_add_right (a b : α) : toIocDiv hp a (b + p)
 = toIocDiv hp a b + 1
· 使用定理 `toIocDiv_sub_eq_toIocDiv_add'`：toIocDiv_sub_eq_toIocDiv_add' (a b c : α)
 : toIocDiv hp (a - c) b = toIocDiv hp a (b + c)
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
-/
theorem toIcoDiv_neg (a b : α) : toIcoDiv hp a (-b) = -(toIocDiv hp (-a) b + 1) := by
  suffices toIcoDiv hp a (-b) = -toIocDiv hp (-(a + p)) b by
    rwa [neg_add, ← sub_eq_add_neg, toIocDiv_sub_eq_toIocDiv_add', toIocDiv_add_right] at this
  rw [← neg_eq_iff_eq_neg, eq_comm]
  apply toIocDiv_eq_of_sub_zsmul_mem_Ioc
  obtain ⟨hc, ho⟩ := sub_toIcoDiv_zsmul_mem_Ico hp a (-b)
  rw [← neg_lt_neg_iff, neg_sub' (-b), neg_neg, ← neg_smul] at ho
  rw [← neg_le_neg_iff, neg_sub' (-b), neg_neg, ← neg_smul] at hc
  refine ⟨ho, hc.trans_eq ?_⟩
  rw [neg_add, neg_add_cancel_right]
/-
**toIcoDiv_neg'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoDiv_neg' (a b : α) : toIcoDiv hp (-a) b = -(toIocDiv hp a (-b) + 1)
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIcoDiv.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `toIocDiv.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用定理 `toIcoDiv_neg`：toIcoDiv_neg (a b : α) : toIcoDiv hp a (-b) = -(toIocDiv h
p (-a) b + 1)
-/
theorem toIcoDiv_neg' (a b : α) : toIcoDiv hp (-a) b = -(toIocDiv hp a (-b) + 1) := by
  simpa only [neg_neg] using toIcoDiv_neg hp (-a) (-b)
/-
**toIocDiv_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocDiv_neg (a b : α) : toIocDiv hp a (-b) = -(toIcoDiv hp (-a) b + 1)
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `toIcoDiv_neg`：toIcoDiv_neg (a b : α) : toIcoDiv hp a (-b) = -(toIocDiv h
p (-a) b + 1)
· 使用定理 `neg_add'`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b : α), -
(a + b) = -a - b
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
-/
theorem toIocDiv_neg (a b : α) : toIocDiv hp a (-b) = -(toIcoDiv hp (-a) b + 1) := by
  rw [← neg_neg b, toIcoDiv_neg, neg_neg, neg_neg, neg_add', neg_neg, add_sub_cancel_right]
/-
**toIocDiv_neg'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocDiv_neg' (a b : α) : toIocDiv hp (-a) b = -(toIcoDiv hp a (-b) + 1)
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIocDiv.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `toIcoDiv.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用定理 `toIocDiv_neg`：toIocDiv_neg (a b : α) : toIocDiv hp a (-b) = -(toIcoDiv h
p (-a) b + 1)
-/
theorem toIocDiv_neg' (a b : α) : toIocDiv hp (-a) b = -(toIcoDiv hp a (-b) + 1) := by
  simpa only [neg_neg] using toIocDiv_neg hp (-a) (-b)

@[simp]
/-
**toIcoMod_add_zsmul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoMod_add_zsmul (a b : α) (m : Int) : toIcoMod hp a (b + m • p) = toIco
Mod hp a b
参数：a b : α；m : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIcoMod.eq_1`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : Linear
Order α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p : α} (hp : 0 
< p…
· 使用定理 `toIcoDiv_add_zsmul`：toIcoDiv_add_zsmul (a b : α) (m : Int) : toIcoDiv hp
 a (b + m • p) = toIcoDiv hp a b + m
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `_private.Mathlib.Algebra.Order.ToIntervalMod.0.toIcoMod_add_zsmul._abel_
1_2`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : LinearOrder α] [inst_2 :
 IsOrderedAddMonoid α] [hα : Archimedean α]   {p : α} (hp : 0 < p…
-/
theorem toIcoMod_add_zsmul (a b : α) (m : ℤ) : toIcoMod hp a (b + m • p) = toIcoMod hp a b := by
  rw [toIcoMod, toIcoDiv_add_zsmul, toIcoMod, add_smul]
  abel

@[simp]
/-
**toIcoMod_add_nsmul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoMod_add_nsmul (a b : α) (m : Nat) : toIcoMod hp a (b + m • p) = toIco
Mod hp a b
参数：a b : α；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIcoMod.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用定理 `toIcoMod_add_zsmul`：toIcoMod_add_zsmul (a b : α) (m : Int) : toIcoMod hp
 a (b + m • p) = toIcoMod hp a b
-/
theorem toIcoMod_add_nsmul (a b : α) (m : ℕ) : toIcoMod hp a (b + m • p) = toIcoMod hp a b :=
  mod_cast toIcoMod_add_zsmul hp a b m

@[simp]
/-
**toIcoMod_add_zsmul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoMod_add_zsmul' (a b : α) (m : Int) : toIcoMod hp (a + m • p) b = toIc
oMod hp a b + m • p
参数：a b : α；m : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `toIcoDiv_add_zsmul'`：toIcoDiv_add_zsmul' (a b : α) (m : Int) : toIcoDiv 
hp (a + m • p) b = toIcoDiv hp a b - m
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
· 使用定理 `sub_add`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c : α), 
a - b + c = a - (b - c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toIcoMod_add_zsmul' (a b : α) (m : ℤ) :
    toIcoMod hp (a + m • p) b = toIcoMod hp a b + m • p := by
  simp only [toIcoMod, toIcoDiv_add_zsmul', sub_smul, sub_add]

@[simp]
/-
**toIcoMod_add_nsmul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoMod_add_nsmul' (a b : α) (m : Nat) : toIcoMod hp (a + m • p) b = toIc
oMod hp a b + m • p
参数：a b : α；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIcoMod.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用定理 `toIcoMod_add_zsmul'`：toIcoMod_add_zsmul' (a b : α) (m : Int) : toIcoMod 
hp (a + m • p) b = toIcoMod hp a b + m • p
-/
theorem toIcoMod_add_nsmul' (a b : α) (m : ℕ) :
    toIcoMod hp (a + m • p) b = toIcoMod hp a b + m • p :=
  mod_cast toIcoMod_add_zsmul' hp a b m

@[simp]
/-
**toIocMod_add_zsmul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocMod_add_zsmul (a b : α) (m : Int) : toIocMod hp a (b + m • p) = toIoc
Mod hp a b
参数：a b : α；m : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIocMod.eq_1`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : Linear
Order α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p : α} (hp : 0 
< p…
· 使用定理 `toIocDiv_add_zsmul`：toIocDiv_add_zsmul (a b : α) (m : Int) : toIocDiv hp
 a (b + m • p) = toIocDiv hp a b + m
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `_private.Mathlib.Algebra.Order.ToIntervalMod.0.toIocMod_add_zsmul._abel_
1_2`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : LinearOrder α] [inst_2 :
 IsOrderedAddMonoid α] [hα : Archimedean α]   {p : α} (hp : 0 < p…
-/
theorem toIocMod_add_zsmul (a b : α) (m : ℤ) : toIocMod hp a (b + m • p) = toIocMod hp a b := by
  rw [toIocMod, toIocDiv_add_zsmul, toIocMod, add_smul]
  abel

@[simp]
/-
**toIocMod_add_nsmul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocMod_add_nsmul (a b : α) (m : Nat) : toIocMod hp a (b + m • p) = toIoc
Mod hp a b
参数：a b : α；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIocMod.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用定理 `toIocMod_add_zsmul`：toIocMod_add_zsmul (a b : α) (m : Int) : toIocMod hp
 a (b + m • p) = toIocMod hp a b
-/
theorem toIocMod_add_nsmul (a b : α) (m : ℕ) : toIocMod hp a (b + m • p) = toIocMod hp a b :=
  mod_cast toIocMod_add_zsmul hp a b m

@[simp]
/-
**toIocMod_add_zsmul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocMod_add_zsmul' (a b : α) (m : Int) : toIocMod hp (a + m • p) b = toIo
cMod hp a b + m • p
参数：a b : α；m : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `toIocDiv_add_zsmul'`：toIocDiv_add_zsmul' (a b : α) (m : Int) : toIocDiv 
hp (a + m • p) b = toIocDiv hp a b - m
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
· 使用定理 `sub_add`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c : α), 
a - b + c = a - (b - c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toIocMod_add_zsmul' (a b : α) (m : ℤ) :
    toIocMod hp (a + m • p) b = toIocMod hp a b + m • p := by
  simp only [toIocMod, toIocDiv_add_zsmul', sub_smul, sub_add]

@[simp]
/-
**toIocMod_add_nsmul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocMod_add_nsmul' (a b : α) (m : Nat) : toIocMod hp (a + m • p) b = toIo
cMod hp a b + m • p
参数：a b : α；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIocMod.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用定理 `toIocMod_add_zsmul'`：toIocMod_add_zsmul' (a b : α) (m : Int) : toIocMod 
hp (a + m • p) b = toIocMod hp a b + m • p
-/
theorem toIocMod_add_nsmul' (a b : α) (m : ℕ) :
    toIocMod hp (a + m • p) b = toIocMod hp a b + m • p :=
  mod_cast toIocMod_add_zsmul' hp a b m

@[simp]
/-
**toIcoMod_zsmul_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoMod_zsmul_add (a b : α) (m : Int) : toIcoMod hp a (m • p + b) = toIco
Mod hp a b
参数：a b : α；m : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `toIcoMod_add_zsmul`：toIcoMod_add_zsmul (a b : α) (m : Int) : toIcoMod hp
 a (b + m • p) = toIcoMod hp a b
-/
theorem toIcoMod_zsmul_add (a b : α) (m : ℤ) : toIcoMod hp a (m • p + b) = toIcoMod hp a b := by
  rw [add_comm, toIcoMod_add_zsmul]

@[simp]
/-
**toIcoMod_nsmul_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoMod_nsmul_add (a b : α) (m : Nat) : toIcoMod hp a (m • p + b) = toIco
Mod hp a b
参数：a b : α；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIcoMod.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用定理 `toIcoMod_zsmul_add`：toIcoMod_zsmul_add (a b : α) (m : Int) : toIcoMod hp
 a (m • p + b) = toIcoMod hp a b
-/
theorem toIcoMod_nsmul_add (a b : α) (m : ℕ) : toIcoMod hp a (m • p + b) = toIcoMod hp a b :=
  mod_cast toIcoMod_zsmul_add hp a b m

@[simp]
/-
**toIcoMod_zsmul_add'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoMod_zsmul_add' (a b : α) (m : Int) : toIcoMod hp (m • p + a) b = m • 
p + toIcoMod hp a b
参数：a b : α；m : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `toIcoMod_add_zsmul'`：toIcoMod_add_zsmul' (a b : α) (m : Int) : toIcoMod 
hp (a + m • p) b = toIcoMod hp a b + m • p
-/
theorem toIcoMod_zsmul_add' (a b : α) (m : ℤ) :
    toIcoMod hp (m • p + a) b = m • p + toIcoMod hp a b := by
  rw [add_comm, toIcoMod_add_zsmul', add_comm]

@[simp]
/-
**toIcoMod_nsmul_add'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoMod_nsmul_add' (a b : α) (m : Nat) : toIcoMod hp (m • p + a) b = m • 
p + toIcoMod hp a b
参数：a b : α；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIcoMod.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用定理 `toIcoMod_zsmul_add'`：toIcoMod_zsmul_add' (a b : α) (m : Int) : toIcoMod 
hp (m • p + a) b = m • p + toIcoMod hp a b
-/
theorem toIcoMod_nsmul_add' (a b : α) (m : ℕ) :
    toIcoMod hp (m • p + a) b = m • p + toIcoMod hp a b :=
  mod_cast toIcoMod_zsmul_add' hp a b m

@[simp]
/-
**toIocMod_zsmul_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocMod_zsmul_add (a b : α) (m : Int) : toIocMod hp a (m • p + b) = toIoc
Mod hp a b
参数：a b : α；m : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `toIocMod_add_zsmul`：toIocMod_add_zsmul (a b : α) (m : Int) : toIocMod hp
 a (b + m • p) = toIocMod hp a b
-/
theorem toIocMod_zsmul_add (a b : α) (m : ℤ) : toIocMod hp a (m • p + b) = toIocMod hp a b := by
  rw [add_comm, toIocMod_add_zsmul]

@[simp]
/-
**toIocMod_nsmul_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocMod_nsmul_add (a b : α) (m : Nat) : toIocMod hp a (m • p + b) = toIoc
Mod hp a b
参数：a b : α；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIocMod.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用定理 `toIocMod_zsmul_add`：toIocMod_zsmul_add (a b : α) (m : Int) : toIocMod hp
 a (m • p + b) = toIocMod hp a b
-/
theorem toIocMod_nsmul_add (a b : α) (m : ℕ) : toIocMod hp a (m • p + b) = toIocMod hp a b :=
  mod_cast toIocMod_zsmul_add hp a b m

@[simp]
/-
**toIocMod_zsmul_add'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocMod_zsmul_add' (a b : α) (m : Int) : toIocMod hp (m • p + a) b = m • 
p + toIocMod hp a b
参数：a b : α；m : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `toIocMod_add_zsmul'`：toIocMod_add_zsmul' (a b : α) (m : Int) : toIocMod 
hp (a + m • p) b = toIocMod hp a b + m • p
-/
theorem toIocMod_zsmul_add' (a b : α) (m : ℤ) :
    toIocMod hp (m • p + a) b = m • p + toIocMod hp a b := by
  rw [add_comm, toIocMod_add_zsmul', add_comm]

@[simp]
/-
**toIocMod_nsmul_add'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocMod_nsmul_add' (a b : α) (m : Nat) : toIocMod hp (m • p + a) b = m • 
p + toIocMod hp a b
参数：a b : α；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIocMod.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用定理 `toIocMod_zsmul_add'`：toIocMod_zsmul_add' (a b : α) (m : Int) : toIocMod 
hp (m • p + a) b = m • p + toIocMod hp a b
-/
theorem toIocMod_nsmul_add' (a b : α) (m : ℕ) :
    toIocMod hp (m • p + a) b = m • p + toIocMod hp a b :=
  mod_cast toIocMod_zsmul_add' hp a b m

@[simp]
/-
**toIcoMod_sub_zsmul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoMod_sub_zsmul (a b : α) (m : Int) : toIcoMod hp a (b - m • p) = toIco
Mod hp a b
参数：a b : α；m : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `toIcoMod_add_zsmul`：toIcoMod_add_zsmul (a b : α) (m : Int) : toIcoMod hp
 a (b + m • p) = toIcoMod hp a b
-/
theorem toIcoMod_sub_zsmul (a b : α) (m : ℤ) : toIcoMod hp a (b - m • p) = toIcoMod hp a b := by
  rw [sub_eq_add_neg, ← neg_smul, toIcoMod_add_zsmul]

@[simp]
/-
**toIcoMod_sub_nsmul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoMod_sub_nsmul (a b : α) (m : Nat) : toIcoMod hp a (b - m • p) = toIco
Mod hp a b
参数：a b : α；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIcoMod.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用定理 `toIcoMod_sub_zsmul`：toIcoMod_sub_zsmul (a b : α) (m : Int) : toIcoMod hp
 a (b - m • p) = toIcoMod hp a b
-/
theorem toIcoMod_sub_nsmul (a b : α) (m : ℕ) : toIcoMod hp a (b - m • p) = toIcoMod hp a b :=
  mod_cast toIcoMod_sub_zsmul hp a b m

@[simp]
/-
**toIcoMod_sub_zsmul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoMod_sub_zsmul' (a b : α) (m : Int) : toIcoMod hp (a - m • p) b = toIc
oMod hp a b - m • p
参数：a b : α；m : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIcoMod.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `toIcoMod_add_zsmul'`：toIcoMod_add_zsmul' (a b : α) (m : Int) : toIcoMod 
hp (a + m • p) b = toIcoMod hp a b + m • p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toIcoMod_sub_zsmul' (a b : α) (m : ℤ) :
    toIcoMod hp (a - m • p) b = toIcoMod hp a b - m • p := by
  simp_rw [sub_eq_add_neg, ← neg_smul, toIcoMod_add_zsmul']

@[simp]
/-
**toIcoMod_sub_nsmul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoMod_sub_nsmul' (a b : α) (m : Nat) : toIcoMod hp (a - m • p) b = toIc
oMod hp a b - m • p
参数：a b : α；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIcoMod.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用定理 `toIcoMod_sub_zsmul'`：toIcoMod_sub_zsmul' (a b : α) (m : Int) : toIcoMod 
hp (a - m • p) b = toIcoMod hp a b - m • p
-/
theorem toIcoMod_sub_nsmul' (a b : α) (m : ℕ) :
    toIcoMod hp (a - m • p) b = toIcoMod hp a b - m • p :=
  mod_cast toIcoMod_sub_zsmul' hp a b m

@[simp]
/-
**toIocMod_sub_zsmul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocMod_sub_zsmul (a b : α) (m : Int) : toIocMod hp a (b - m • p) = toIoc
Mod hp a b
参数：a b : α；m : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `toIocMod_add_zsmul`：toIocMod_add_zsmul (a b : α) (m : Int) : toIocMod hp
 a (b + m • p) = toIocMod hp a b
-/
theorem toIocMod_sub_zsmul (a b : α) (m : ℤ) : toIocMod hp a (b - m • p) = toIocMod hp a b := by
  rw [sub_eq_add_neg, ← neg_smul, toIocMod_add_zsmul]

@[simp]
/-
**toIocMod_sub_nsmul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocMod_sub_nsmul (a b : α) (m : Nat) : toIocMod hp a (b - m • p) = toIoc
Mod hp a b
参数：a b : α；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIocMod.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用定理 `toIocMod_sub_zsmul`：toIocMod_sub_zsmul (a b : α) (m : Int) : toIocMod hp
 a (b - m • p) = toIocMod hp a b
-/
theorem toIocMod_sub_nsmul (a b : α) (m : ℕ) : toIocMod hp a (b - m • p) = toIocMod hp a b :=
  mod_cast toIocMod_sub_zsmul hp a b m

@[simp]
/-
**toIocMod_sub_zsmul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocMod_sub_zsmul' (a b : α) (m : Int) : toIocMod hp (a - m • p) b = toIo
cMod hp a b - m • p
参数：a b : α；m : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIocMod.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `toIocMod_add_zsmul'`：toIocMod_add_zsmul' (a b : α) (m : Int) : toIocMod 
hp (a + m • p) b = toIocMod hp a b + m • p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toIocMod_sub_zsmul' (a b : α) (m : ℤ) :
    toIocMod hp (a - m • p) b = toIocMod hp a b - m • p := by
  simp_rw [sub_eq_add_neg, ← neg_smul, toIocMod_add_zsmul']

@[simp]
/-
**toIocMod_sub_nsmul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocMod_sub_nsmul' (a b : α) (m : Nat) : toIocMod hp (a - m • p) b = toIo
cMod hp a b - m • p
参数：a b : α；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIocMod.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用定理 `toIocMod_sub_zsmul'`：toIocMod_sub_zsmul' (a b : α) (m : Int) : toIocMod 
hp (a - m • p) b = toIocMod hp a b - m • p
-/
theorem toIocMod_sub_nsmul' (a b : α) (m : ℕ) :
    toIocMod hp (a - m • p) b = toIocMod hp a b - m • p :=
  mod_cast toIocMod_sub_zsmul' hp a b m

@[simp]
/-
**toIcoMod_add_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoMod_add_right (a b : α) : toIcoMod hp a (b + p) = toIcoMod hp a b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIcoMod.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用定理 `one_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 1 • a = a
· 使用定理 `toIcoMod_add_zsmul`：toIcoMod_add_zsmul (a b : α) (m : Int) : toIcoMod hp
 a (b + m • p) = toIcoMod hp a b
-/
theorem toIcoMod_add_right (a b : α) : toIcoMod hp a (b + p) = toIcoMod hp a b := by
  simpa only [one_zsmul] using toIcoMod_add_zsmul hp a b 1

@[simp]
/-
**toIcoMod_add_right'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoMod_add_right' (a b : α) : toIcoMod hp (a + p) b = toIcoMod hp a b + 
p
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIcoMod.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用定理 `one_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 1 • a = a
· 使用定理 `toIcoMod_add_zsmul'`：toIcoMod_add_zsmul' (a b : α) (m : Int) : toIcoMod 
hp (a + m • p) b = toIcoMod hp a b + m • p
-/
theorem toIcoMod_add_right' (a b : α) : toIcoMod hp (a + p) b = toIcoMod hp a b + p := by
  simpa only [one_zsmul] using toIcoMod_add_zsmul' hp a b 1

@[simp]
/-
**toIocMod_add_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocMod_add_right (a b : α) : toIocMod hp a (b + p) = toIocMod hp a b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIocMod.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用定理 `one_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 1 • a = a
· 使用定理 `toIocMod_add_zsmul`：toIocMod_add_zsmul (a b : α) (m : Int) : toIocMod hp
 a (b + m • p) = toIocMod hp a b
-/
theorem toIocMod_add_right (a b : α) : toIocMod hp a (b + p) = toIocMod hp a b := by
  simpa only [one_zsmul] using toIocMod_add_zsmul hp a b 1

@[simp]
/-
**toIocMod_add_right'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocMod_add_right' (a b : α) : toIocMod hp (a + p) b = toIocMod hp a b + 
p
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIocMod.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用定理 `one_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 1 • a = a
· 使用定理 `toIocMod_add_zsmul'`：toIocMod_add_zsmul' (a b : α) (m : Int) : toIocMod 
hp (a + m • p) b = toIocMod hp a b + m • p
-/
theorem toIocMod_add_right' (a b : α) : toIocMod hp (a + p) b = toIocMod hp a b + p := by
  simpa only [one_zsmul] using toIocMod_add_zsmul' hp a b 1

@[simp]
/-
**toIcoMod_add_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoMod_add_left (a b : α) : toIcoMod hp a (p + b) = toIcoMod hp a b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `toIcoMod_add_right`：toIcoMod_add_right (a b : α) : toIcoMod hp a (b + p)
 = toIcoMod hp a b
-/
theorem toIcoMod_add_left (a b : α) : toIcoMod hp a (p + b) = toIcoMod hp a b := by
  rw [add_comm, toIcoMod_add_right]

@[simp]
/-
**toIcoMod_add_left'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoMod_add_left' (a b : α) : toIcoMod hp (p + a) b = p + toIcoMod hp a b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `toIcoMod_add_right'`：toIcoMod_add_right' (a b : α) : toIcoMod hp (a + p)
 b = toIcoMod hp a b + p
-/
theorem toIcoMod_add_left' (a b : α) : toIcoMod hp (p + a) b = p + toIcoMod hp a b := by
  rw [add_comm, toIcoMod_add_right', add_comm]

@[simp]
/-
**toIocMod_add_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocMod_add_left (a b : α) : toIocMod hp a (p + b) = toIocMod hp a b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `toIocMod_add_right`：toIocMod_add_right (a b : α) : toIocMod hp a (b + p)
 = toIocMod hp a b
-/
theorem toIocMod_add_left (a b : α) : toIocMod hp a (p + b) = toIocMod hp a b := by
  rw [add_comm, toIocMod_add_right]

@[simp]
/-
**toIocMod_add_left'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocMod_add_left' (a b : α) : toIocMod hp (p + a) b = p + toIocMod hp a b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `toIocMod_add_right'`：toIocMod_add_right' (a b : α) : toIocMod hp (a + p)
 b = toIocMod hp a b + p
-/
theorem toIocMod_add_left' (a b : α) : toIocMod hp (p + a) b = p + toIocMod hp a b := by
  rw [add_comm, toIocMod_add_right', add_comm]

@[simp]
/-
**toIcoMod_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoMod_sub (a b : α) : toIcoMod hp a (b - p) = toIcoMod hp a b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIcoMod.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用定理 `one_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 1 • a = a
· 使用定理 `toIcoMod_sub_zsmul`：toIcoMod_sub_zsmul (a b : α) (m : Int) : toIcoMod hp
 a (b - m • p) = toIcoMod hp a b
-/
theorem toIcoMod_sub (a b : α) : toIcoMod hp a (b - p) = toIcoMod hp a b := by
  simpa only [one_zsmul] using toIcoMod_sub_zsmul hp a b 1

@[simp]
/-
**toIcoMod_sub'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoMod_sub' (a b : α) : toIcoMod hp (a - p) b = toIcoMod hp a b - p
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIcoMod.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用定理 `one_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 1 • a = a
· 使用定理 `toIcoMod_sub_zsmul'`：toIcoMod_sub_zsmul' (a b : α) (m : Int) : toIcoMod 
hp (a - m • p) b = toIcoMod hp a b - m • p
-/
theorem toIcoMod_sub' (a b : α) : toIcoMod hp (a - p) b = toIcoMod hp a b - p := by
  simpa only [one_zsmul] using toIcoMod_sub_zsmul' hp a b 1

@[simp]
/-
**toIocMod_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocMod_sub (a b : α) : toIocMod hp a (b - p) = toIocMod hp a b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIocMod.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用定理 `one_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 1 • a = a
· 使用定理 `toIocMod_sub_zsmul`：toIocMod_sub_zsmul (a b : α) (m : Int) : toIocMod hp
 a (b - m • p) = toIocMod hp a b
-/
theorem toIocMod_sub (a b : α) : toIocMod hp a (b - p) = toIocMod hp a b := by
  simpa only [one_zsmul] using toIocMod_sub_zsmul hp a b 1

@[simp]
/-
**toIocMod_sub'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocMod_sub' (a b : α) : toIocMod hp (a - p) b = toIocMod hp a b - p
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIocMod.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用定理 `one_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 1 • a = a
· 使用定理 `toIocMod_sub_zsmul'`：toIocMod_sub_zsmul' (a b : α) (m : Int) : toIocMod 
hp (a - m • p) b = toIocMod hp a b - m • p
-/
theorem toIocMod_sub' (a b : α) : toIocMod hp (a - p) b = toIocMod hp a b - p := by
  simpa only [one_zsmul] using toIocMod_sub_zsmul' hp a b 1
/-
**toIcoMod_sub_eq_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoMod_sub_eq_sub (a b c : α) : toIcoMod hp a (b - c) = toIcoMod hp (a +
 c) b - c
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIcoDiv_sub_eq_toIcoDiv_add`：toIcoDiv_sub_eq_toIcoDiv_add (a b c : α) :
 toIcoDiv hp a (b - c) = toIcoDiv hp (a + c) b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_right_comm`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c
 : α), a - b - c = a - c - b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toIcoMod_sub_eq_sub (a b c : α) : toIcoMod hp a (b - c) = toIcoMod hp (a + c) b - c := by
  simp_rw [toIcoMod, toIcoDiv_sub_eq_toIcoDiv_add, sub_right_comm]
/-
**toIocMod_sub_eq_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocMod_sub_eq_sub (a b c : α) : toIocMod hp a (b - c) = toIocMod hp (a +
 c) b - c
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIocDiv_sub_eq_toIocDiv_add`：toIocDiv_sub_eq_toIocDiv_add (a b c : α) :
 toIocDiv hp a (b - c) = toIocDiv hp (a + c) b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_right_comm`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c
 : α), a - b - c = a - c - b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toIocMod_sub_eq_sub (a b c : α) : toIocMod hp a (b - c) = toIocMod hp (a + c) b - c := by
  simp_rw [toIocMod, toIocDiv_sub_eq_toIocDiv_add, sub_right_comm]
/-
**toIcoMod_add_right_eq_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoMod_add_right_eq_add (a b c : α) : toIcoMod hp a (b + c) = toIcoMod h
p (a - c) b + c
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `toIcoDiv_sub_eq_toIcoDiv_add'`：toIcoDiv_sub_eq_toIcoDiv_add' (a b c : α)
 : toIcoDiv hp (a - c) b = toIcoDiv hp a (b + c)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_add_eq_add_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a
 b c : α), a - b + c = a + c - b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toIcoMod_add_right_eq_add (a b c : α) :
    toIcoMod hp a (b + c) = toIcoMod hp (a - c) b + c := by
  simp_rw [toIcoMod, toIcoDiv_sub_eq_toIcoDiv_add', sub_add_eq_add_sub]
/-
**toIocMod_add_right_eq_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocMod_add_right_eq_add (a b c : α) : toIocMod hp a (b + c) = toIocMod h
p (a - c) b + c
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `toIocDiv_sub_eq_toIocDiv_add'`：toIocDiv_sub_eq_toIocDiv_add' (a b c : α)
 : toIocDiv hp (a - c) b = toIocDiv hp a (b + c)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_add_eq_add_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a
 b c : α), a - b + c = a + c - b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toIocMod_add_right_eq_add (a b c : α) :
    toIocMod hp a (b + c) = toIocMod hp (a - c) b + c := by
  simp_rw [toIocMod, toIocDiv_sub_eq_toIocDiv_add', sub_add_eq_add_sub]
/-
**toIcoMod_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoMod_neg (a b : α) : toIcoMod hp a (-b) = p - toIocMod hp (-a) b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIcoDiv_neg`：toIcoDiv_neg (a b : α) : toIcoDiv hp a (-b) = -(toIocDiv h
p (-a) b + 1)
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `_private.Mathlib.Algebra.Order.ToIntervalMod.0.toIcoMod_neg._abel_1_7`：∀
 {α : Type u_1} [inst : AddCommGroup α] [inst_1 : LinearOrder α] [inst_2 : IsOrd
eredAddMonoid α] [hα : Archimedean α]   {p : α} (hp : 0 < p…
-/
theorem toIcoMod_neg (a b : α) : toIcoMod hp a (-b) = p - toIocMod hp (-a) b := by
  simp_rw [toIcoMod, toIocMod, toIcoDiv_neg, neg_smul, add_smul]
  abel
/-
**toIcoMod_neg'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoMod_neg' (a b : α) : toIcoMod hp (-a) b = p - toIocMod hp a (-b)
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIcoMod.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `toIocMod.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用定理 `toIcoMod_neg`：toIcoMod_neg (a b : α) : toIcoMod hp a (-b) = p - toIocMod
 hp (-a) b
-/
theorem toIcoMod_neg' (a b : α) : toIcoMod hp (-a) b = p - toIocMod hp a (-b) := by
  simpa only [neg_neg] using toIcoMod_neg hp (-a) (-b)
/-
**toIocMod_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocMod_neg (a b : α) : toIocMod hp a (-b) = p - toIcoMod hp (-a) b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIocDiv_neg`：toIocDiv_neg (a b : α) : toIocDiv hp a (-b) = -(toIcoDiv h
p (-a) b + 1)
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `_private.Mathlib.Algebra.Order.ToIntervalMod.0.toIocMod_neg._abel_1_7`：∀
 {α : Type u_1} [inst : AddCommGroup α] [inst_1 : LinearOrder α] [inst_2 : IsOrd
eredAddMonoid α] [hα : Archimedean α]   {p : α} (hp : 0 < p…
-/
theorem toIocMod_neg (a b : α) : toIocMod hp a (-b) = p - toIcoMod hp (-a) b := by
  simp_rw [toIocMod, toIcoMod, toIocDiv_neg, neg_smul, add_smul]
  abel
/-
**toIocMod_neg'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocMod_neg' (a b : α) : toIocMod hp (-a) b = p - toIcoMod hp a (-b)
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIocMod.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `toIcoMod.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用定理 `toIocMod_neg`：toIocMod_neg (a b : α) : toIocMod hp a (-b) = p - toIcoMod
 hp (-a) b
-/
theorem toIocMod_neg' (a b : α) : toIocMod hp (-a) b = p - toIcoMod hp a (-b) := by
  simpa only [neg_neg] using toIocMod_neg hp (-a) (-b)
/-
**toIcoMod_eq_toIcoMod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoMod_eq_toIcoMod : toIcoMod hp a b = toIcoMod hp a c ↔ exists n : Int,
 c - b = n • p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `toIcoMod_add_toIcoDiv_zsmul`：toIcoMod_add_toIcoDiv_zsmul (a b : α) : toI
coMod hp a b + toIcoDiv hp a b • p = b
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
· 使用定理 `_private.Mathlib.Algebra.Order.ToIntervalMod.0.toIcoMod_eq_toIcoMod._abe
l_1_1`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : LinearOrder α] [inst_2
 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p : α} (hp : 0 < p…
· 使用定理 `sub_eq_iff_eq_add`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a -
 b = c ↔ a = c + b
· 使用定理 `toIcoMod_zsmul_add`：toIcoMod_zsmul_add (a b : α) (m : Int) : toIcoMod hp
 a (m • p + b) = toIcoMod hp a b
-/
theorem toIcoMod_eq_toIcoMod : toIcoMod hp a b = toIcoMod hp a c ↔ ∃ n : ℤ, c - b = n • p := by
  refine ⟨fun h => ⟨toIcoDiv hp a c - toIcoDiv hp a b, ?_⟩, fun h => ?_⟩
  · conv_lhs => rw [← toIcoMod_add_toIcoDiv_zsmul hp a b, ← toIcoMod_add_toIcoDiv_zsmul hp a c]
    rw [h, sub_smul]
    abel
  · rcases h with ⟨z, hz⟩
    rw [sub_eq_iff_eq_add] at hz
    rw [hz, toIcoMod_zsmul_add]
/-
**toIocMod_eq_toIocMod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocMod_eq_toIocMod : toIocMod hp a b = toIocMod hp a c ↔ exists n : Int,
 c - b = n • p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `toIocMod_add_toIocDiv_zsmul`：toIocMod_add_toIocDiv_zsmul (a b : α) : toI
ocMod hp a b + toIocDiv hp a b • p = b
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
· 使用定理 `_private.Mathlib.Algebra.Order.ToIntervalMod.0.toIocMod_eq_toIocMod._abe
l_1_1`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : LinearOrder α] [inst_2
 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p : α} (hp : 0 < p…
· 使用定理 `sub_eq_iff_eq_add`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a -
 b = c ↔ a = c + b
· 使用定理 `toIocMod_zsmul_add`：toIocMod_zsmul_add (a b : α) (m : Int) : toIocMod hp
 a (m • p + b) = toIocMod hp a b
-/
theorem toIocMod_eq_toIocMod : toIocMod hp a b = toIocMod hp a c ↔ ∃ n : ℤ, c - b = n • p := by
  refine ⟨fun h => ⟨toIocDiv hp a c - toIocDiv hp a b, ?_⟩, fun h => ?_⟩
  · conv_lhs => rw [← toIocMod_add_toIocDiv_zsmul hp a b, ← toIocMod_add_toIocDiv_zsmul hp a c]
    rw [h, sub_smul]
    abel
  · rcases h with ⟨z, hz⟩
    rw [sub_eq_iff_eq_add] at hz
    rw [hz, toIocMod_zsmul_add]

/-! ### Links between the `Ico` and `Ioc` variants applied to the same element -/


section IcoIoc

namespace AddCommGroup

/-
**AddCommGroup.modEq_iff_toIcoMod_eq_left** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGrou
p`。
形式化陈述：modEq_iff_toIcoMod_eq_left : a ≡ b [PMOD p] ↔ toIcoMod hp a b = a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `AddCommGroup.modEq_iff_eq_add_zsmul`：modEq_iff_eq_add_zsmul : a ≡ b [PMO
D p] ↔ exists z : Int, b = a + z • p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIcoMod_add_zsmul`：toIcoMod_add_zsmul (a b : α) (m : Int) : toIcoMod hp
 a (b + m • p) = toIcoMod hp a b
· 使用定理 `toIcoMod_apply_left`：toIcoMod_apply_left (a : α) : toIcoMod hp a a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_add_of_sub_eq`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a - 
c = b → a = b + c
-/
theorem modEq_iff_toIcoMod_eq_left : a ≡ b [PMOD p] ↔ toIcoMod hp a b = a :=
  modEq_iff_eq_add_zsmul.trans
    ⟨by
      rintro ⟨n, rfl⟩
      rw [toIcoMod_add_zsmul, toIcoMod_apply_left], fun h => ⟨toIcoDiv hp a b, eq_add_of_sub_eq h⟩⟩
/-
**AddCommGroup.modEq_iff_toIocMod_eq_right** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGro
up`。
形式化陈述：modEq_iff_toIocMod_eq_right : a ≡ b [PMOD p] ↔ toIocMod hp a b = a + p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `AddCommGroup.modEq_iff_eq_add_zsmul`：modEq_iff_eq_add_zsmul : a ≡ b [PMO
D p] ↔ exists z : Int, b = a + z • p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIocMod_add_zsmul`：toIocMod_add_zsmul (a b : α) (m : Int) : toIocMod hp
 a (b + m • p) = toIocMod hp a b
· 使用定理 `toIocMod_apply_left`：toIocMod_apply_left (a : α) : toIocMod hp a a = a +
 p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_one_zsmul`：∀ {G : Type u_3} [inst : AddGroup G] (a : G) (n : ℤ), (n 
+ 1) • a = n • a + a
· 使用定理 `add_left_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G),
 a + (b + c) = b + (a + c)
· 使用定理 `sub_eq_iff_eq_add'`：∀ {G : Type u_3} [inst : AddCommGroup G] {a b c : G}
, a - b = c ↔ a = b + c
-/
theorem modEq_iff_toIocMod_eq_right : a ≡ b [PMOD p] ↔ toIocMod hp a b = a + p := by
  refine modEq_iff_eq_add_zsmul.trans ⟨?_, fun h => ⟨toIocDiv hp a b + 1, ?_⟩⟩
  · rintro ⟨z, rfl⟩
    rw [toIocMod_add_zsmul, toIocMod_apply_left]
  · rwa [add_one_zsmul, add_left_comm, ← sub_eq_iff_eq_add']

alias ⟨ModEq.toIcoMod_eq_left, _⟩ := modEq_iff_toIcoMod_eq_left

alias ⟨ModEq.toIcoMod_eq_right, _⟩ := modEq_iff_toIocMod_eq_right

variable (a b)

open List in
/-
**AddCommGroup.tfae_modEq** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGroup`。
形式化陈述：tfae_modEq : TFAE [a ≡ b [PMOD p], forall z : Int, b - z • p ∉ Set.Ioo a (
a + p), toIcoMod hp a b != toIocMod hp a b, toIcoMod hp a b + p = toIocMod hp a 
b]
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddCommGroup.modEq_iff_toIcoMod_eq_left`：modEq_iff_toIcoMod_eq_left : a 
≡ b [PMOD p] ↔ toIcoMod hp a b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_exists`：∀ {α : Sort u_1} {p : α → Prop}, (¬∃ x, p x) ↔ ∀ (x : α), ¬p
 x
· 使用定理 `not_imp_not`：not_imp_not : ¬a -> ¬b ↔ b -> a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `toIcoMod_eq_iff`：toIcoMod_eq_iff : toIcoMod hp a b = c ↔ c in Set.Ico a 
(a + p) ∧ exists z : Int, b = c + z • p
· 使用定理 `Set.Ioo_subset_Ico_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo a b ⊆ Set.Ico a b
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `toIocMod_eq_iff`：toIocMod_eq_iff : toIocMod hp a b = c ↔ c in Set.Ioc a 
(a + p) ∧ exists z : Int, b = c + z • p
· 使用定理 `Set.Ioo_subset_Ioc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo b a ⊆ Set.Ioc b a
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `add_eq_left`：∀ {M : Type u_4} [inst : AddMonoid M] [IsLeftCancelAdd M] {
a b : M}, a + b = a ↔ b = 0
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Set.right_mem_Ioc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ S
et.Ioc b a ↔ b < a
· 使用定理 `lt_add_of_pos_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : 
LT α] [AddLeftStrictMono α] (a : α) {b : α}, 0 < b → a < a + b
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `sub_one_zsmul`：∀ {G : Type u_3} [inst : AddGroup G] (a : G) (n : ℤ), (n 
- 1) • a = n • a + -a
· 使用定理 `add_add_add_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c d 
: G), a + b + (c + d) = a + c + (b + d)
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `toIcoMod_add_toIcoDiv_zsmul`：toIcoMod_add_toIcoDiv_zsmul (a b : α) : toI
coMod hp a b + toIcoDiv hp a b • p = b
· 使用定理 `not_imp_comm`：not_imp_comm : ¬a -> b ↔ ¬b -> a
· 使用定理 `toIcoMod_mem_Ico`：toIcoMod_mem_Ico (a b : α) : toIcoMod hp a b in Set.Ic
o a (a + p)
· 使用定理 `LE.le.lt_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
（共 33 条，此处仅展示前 30 条）
-/
theorem tfae_modEq :
    TFAE
      [a ≡ b [PMOD p], ∀ z : ℤ, b - z • p ∉ Set.Ioo a (a + p), toIcoMod hp a b ≠ toIocMod hp a b,
        toIcoMod hp a b + p = toIocMod hp a b] := by
  rw [modEq_iff_toIcoMod_eq_left hp]
  tfae_have 3 → 2 := by
    rw [← not_exists, not_imp_not]
    exact fun ⟨i, hi⟩ =>
      ((toIcoMod_eq_iff hp).2 ⟨Set.Ioo_subset_Ico_self hi, i, (sub_add_cancel b _).symm⟩).trans
        ((toIocMod_eq_iff hp).2 ⟨Set.Ioo_subset_Ioc_self hi, i, (sub_add_cancel b _).symm⟩).symm
  tfae_have 4 → 3
  | h => by
    rw [← h, Ne, eq_comm, add_eq_left]
    exact hp.ne'
  tfae_have 1 → 4
  | h => by
    rw [h, eq_comm, toIocMod_eq_iff, Set.right_mem_Ioc]
    refine ⟨lt_add_of_pos_right a hp, toIcoDiv hp a b - 1, ?_⟩
    rw [sub_one_zsmul, add_add_add_comm, add_neg_cancel, add_zero]
    conv_lhs => rw [← toIcoMod_add_toIcoDiv_zsmul hp a b, h]
  tfae_have 2 → 1 := by
    rw [← not_exists, not_imp_comm]
    have h' := toIcoMod_mem_Ico hp a b
    exact fun h => ⟨_, h'.1.lt_of_ne' h, h'.2⟩
  tfae_finish

variable {a b}
/-
**AddCommGroup.modEq_iff_forall_notMem_Ioo_mod** 是 Mathlib 中的一个定理，位于命名空间 `AddCom
mGroup`。
形式化陈述：modEq_iff_forall_notMem_Ioo_mod : a ≡ b [PMOD p] ↔ forall z : Int, b - z •
 p ∉ Set.Ioo a (a + p)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `AddCommGroup.tfae_modEq`：tfae_modEq : TFAE [a ≡ b [PMOD p], forall z : I
nt, b - z • p ∉ Set.Ioo a (a + p), toIcoMod hp a b != toIocMod hp a b, toIcoMod 
hp a b + p = …
-/
theorem modEq_iff_forall_notMem_Ioo_mod :
    a ≡ b [PMOD p] ↔ ∀ z : ℤ, b - z • p ∉ Set.Ioo a (a + p) :=
  (tfae_modEq hp a b).out 0 1
/-
**AddCommGroup.modEq_iff_toIcoMod_ne_toIocMod** 是 Mathlib 中的一个定理，位于命名空间 `AddComm
Group`。
形式化陈述：modEq_iff_toIcoMod_ne_toIocMod : a ≡ b [PMOD p] ↔ toIcoMod hp a b != toIoc
Mod hp a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `AddCommGroup.tfae_modEq`：tfae_modEq : TFAE [a ≡ b [PMOD p], forall z : I
nt, b - z • p ∉ Set.Ioo a (a + p), toIcoMod hp a b != toIocMod hp a b, toIcoMod 
hp a b + p = …
-/
theorem modEq_iff_toIcoMod_ne_toIocMod : a ≡ b [PMOD p] ↔ toIcoMod hp a b ≠ toIocMod hp a b :=
  (tfae_modEq hp a b).out 0 2
/-
**AddCommGroup.modEq_iff_toIcoMod_add_period_eq_toIocMod** 是 Mathlib 中的一个定理，位于命名
空间 `AddCommGroup`。
形式化陈述：modEq_iff_toIcoMod_add_period_eq_toIocMod : a ≡ b [PMOD p] ↔ toIcoMod hp a
 b + p = toIocMod hp a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `AddCommGroup.tfae_modEq`：tfae_modEq : TFAE [a ≡ b [PMOD p], forall z : I
nt, b - z • p ∉ Set.Ioo a (a + p), toIcoMod hp a b != toIocMod hp a b, toIcoMod 
hp a b + p = …
-/
theorem modEq_iff_toIcoMod_add_period_eq_toIocMod :
    a ≡ b [PMOD p] ↔ toIcoMod hp a b + p = toIocMod hp a b :=
  (tfae_modEq hp a b).out 0 3
/-
**AddCommGroup.not_modEq_iff_toIcoMod_eq_toIocMod** 是 Mathlib 中的一个定理，位于命名空间 `Add
CommGroup`。
形式化陈述：not_modEq_iff_toIcoMod_eq_toIocMod : ¬a ≡ b [PMOD p] ↔ toIcoMod hp a b = t
oIocMod hp a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not_left`：Iff.not_left (h : a ↔ ¬b) : ¬a ↔ b
· 使用定理 `AddCommGroup.modEq_iff_toIcoMod_ne_toIocMod`：modEq_iff_toIcoMod_ne_toIoc
Mod : a ≡ b [PMOD p] ↔ toIcoMod hp a b != toIocMod hp a b
-/
theorem not_modEq_iff_toIcoMod_eq_toIocMod : ¬a ≡ b [PMOD p] ↔ toIcoMod hp a b = toIocMod hp a b :=
  (modEq_iff_toIcoMod_ne_toIocMod _).not_left
/-
**AddCommGroup.not_modEq_iff_toIcoDiv_eq_toIocDiv** 是 Mathlib 中的一个定理，位于命名空间 `Add
CommGroup`。
形式化陈述：not_modEq_iff_toIcoDiv_eq_toIocDiv : ¬a ≡ b [PMOD p] ↔ toIcoDiv hp a b = t
oIocDiv hp a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddCommGroup.not_modEq_iff_toIcoMod_eq_toIocMod`：not_modEq_iff_toIcoMod_
eq_toIocMod : ¬a ≡ b [PMOD p] ↔ toIcoMod hp a b = toIocMod hp a b
· 使用定理 `toIcoMod.eq_1`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : Linear
Order α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p : α} (hp : 0 
< p…
· 使用定理 `toIocMod.eq_1`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : Linear
Order α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p : α} (hp : 0 
< p…
· 使用定理 `sub_right_inj`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a - b =
 a - c ↔ b = c
· 使用定理 `zsmul_left_inj`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : Parti
alOrder α] [IsOrderedAddMonoid α] {a : α},   0 < a → ∀ {m n : ℤ}, m • a = n • a 
↔ m …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem not_modEq_iff_toIcoDiv_eq_toIocDiv :
    ¬a ≡ b [PMOD p] ↔ toIcoDiv hp a b = toIocDiv hp a b := by
  rw [not_modEq_iff_toIcoMod_eq_toIocMod hp, toIcoMod, toIocMod, sub_right_inj,
    zsmul_left_inj hp]
/-
**AddCommGroup.modEq_iff_toIcoDiv_eq_toIocDiv_add_one** 是 Mathlib 中的一个定理，位于命名空间 
`AddCommGroup`。
形式化陈述：modEq_iff_toIcoDiv_eq_toIocDiv_add_one : a ≡ b [PMOD p] ↔ toIcoDiv hp a b 
= toIocDiv hp a b + 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddCommGroup.modEq_iff_toIcoMod_add_period_eq_toIocMod`：modEq_iff_toIcoM
od_add_period_eq_toIocMod : a ≡ b [PMOD p] ↔ toIcoMod hp a b + p = toIocMod hp a
 b
· 使用定理 `toIcoMod.eq_1`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : Linear
Order α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p : α} (hp : 0 
< p…
· 使用定理 `toIocMod.eq_1`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : Linear
Order α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p : α} (hp : 0 
< p…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_sub_iff_add_eq`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a =
 b - c ↔ a + c = b
· 使用定理 `sub_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c : α), 
a - b - c = a - (b + c)
· 使用定理 `sub_right_inj`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a - b =
 a - c ↔ b = c
· 使用定理 `add_one_zsmul`：∀ {G : Type u_3} [inst : AddGroup G] (a : G) (n : ℤ), (n 
+ 1) • a = n • a + a
· 使用定理 `zsmul_left_inj`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : Parti
alOrder α] [IsOrderedAddMonoid α] {a : α},   0 < a → ∀ {m n : ℤ}, m • a = n • a 
↔ m …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem modEq_iff_toIcoDiv_eq_toIocDiv_add_one :
    a ≡ b [PMOD p] ↔ toIcoDiv hp a b = toIocDiv hp a b + 1 := by
  rw [modEq_iff_toIcoMod_add_period_eq_toIocMod hp, toIcoMod, toIocMod, ← eq_sub_iff_add_eq,
    sub_sub, sub_right_inj, ← add_one_zsmul, zsmul_left_inj hp]

end AddCommGroup

open AddCommGroup

/-- If `a` and `b` fall within the same cycle w.r.t. `c`, then they are congruent modulo `p`. -/
@[simp]
/-
**toIcoMod_inj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoMod_inj {c : α} : toIcoMod hp c a = toIcoMod hp c b ↔ a ≡ b [PMOD p]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIcoMod_eq_toIcoMod`：toIcoMod_eq_toIcoMod : toIcoMod hp a b = toIcoMod 
hp a c ↔ exists n : Int, c - b = n • p
· 使用定理 `AddCommGroup.modEq_iff_zsmul'`：modEq_iff_zsmul' : a ≡ b [PMOD p] ↔ exist
s m : Int, b - a = m • p
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
If `a` and `b` fall within the same cycle w.r.t. `c`, then they are congruent mo
dulo `p`.
-/
theorem toIcoMod_inj {c : α} : toIcoMod hp c a = toIcoMod hp c b ↔ a ≡ b [PMOD p] := by
  rw [toIcoMod_eq_toIcoMod, AddCommGroup.modEq_iff_zsmul']

alias ⟨_, AddCommGroup.ModEq.toIcoMod_eq_toIcoMod⟩ := toIcoMod_inj
/-
**Ico_eq_locus_Ioc_eq_iUnion_Ioo** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ico_eq_locus_Ioc_eq_iUnion_Ioo : { b | toIcoMod hp a b = toIocMod hp a b }
 = ⋃ z : Int, Set.Ioo (a + z • p) (a + p + z • p)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AddCommGroup.modEq_iff_forall_notMem_Ioo_mod`：modEq_iff_forall_notMem_Io
o_mod : a ≡ b [PMOD p] ↔ forall z : Int, b - z • p ∉ Set.Ioo a (a + p)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Ico_eq_locus_Ioc_eq_iUnion_Ioo :
    { b | toIcoMod hp a b = toIocMod hp a b } = ⋃ z : ℤ, Set.Ioo (a + z • p) (a + p + z • p) := by
  ext1
  simp_rw [Set.mem_ofPred, Set.mem_iUnion, ← Set.sub_mem_Ioo_iff_left, ←
    not_modEq_iff_toIcoMod_eq_toIocMod, modEq_iff_forall_notMem_Ioo_mod hp, not_forall,
    Classical.not_not]
/-
**toIocDiv_wcovBy_toIcoDiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocDiv_wcovBy_toIcoDiv (a b : α) : toIocDiv hp a b ⩿ toIcoDiv hp a b
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddCommGroup.not_modEq_iff_toIcoDiv_eq_toIocDiv`：not_modEq_iff_toIcoDiv_
eq_toIocDiv : ¬a ≡ b [PMOD p] ↔ toIcoDiv hp a b = toIocDiv hp a b
· 使用定理 `AddCommGroup.modEq_iff_toIcoDiv_eq_toIocDiv_add_one`：modEq_iff_toIcoDiv_
eq_toIocDiv_add_one : a ≡ b [PMOD p] ↔ toIcoDiv hp a b = toIocDiv hp a b + 1
· 使用定理 `em'`：em' (p : Prop) : ¬p ∨ p
· 使用定理 `wcovBy_iff_eq_or_covBy`：wcovBy_iff_eq_or_covBy : a ⩿ b ↔ a = b ∨ a ⋖ b
· 使用定理 `Order.succ_eq_iff_covBy`：succ_eq_iff_covBy : succ a = b ↔ a ⋖ b
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
-/
theorem toIocDiv_wcovBy_toIcoDiv (a b : α) : toIocDiv hp a b ⩿ toIcoDiv hp a b := by
  suffices toIocDiv hp a b = toIcoDiv hp a b ∨ toIocDiv hp a b + 1 = toIcoDiv hp a b by
    rwa [wcovBy_iff_eq_or_covBy, ← Order.succ_eq_iff_covBy]
  rw [eq_comm, ← not_modEq_iff_toIcoDiv_eq_toIocDiv, eq_comm, ←
    modEq_iff_toIcoDiv_eq_toIocDiv_add_one]
  exact em' _
/-
**toIcoMod_le_toIocMod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoMod_le_toIocMod (a b : α) : toIcoMod hp a b <= toIocMod hp a b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIcoMod.eq_1`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : Linear
Order α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p : α} (hp : 0 
< p…
· 使用定理 `toIocMod.eq_1`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : Linear
Order α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p : α} (hp : 0 
< p…
· 使用定理 `sub_le_sub_iff_left`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] 
[AddLeftMono α] [AddRightMono α] {b c : α} (a : α),   a - b ≤ a - c ↔ c ≤ b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `zsmul_left_mono`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : Part
ialOrder α] [IsOrderedAddMonoid α] {a : α},   0 ≤ a → Monotone fun n => n • a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `WCovBy.le`：WCovBy.le (h : a ⩿ b) : a <= b
· 使用定理 `toIocDiv_wcovBy_toIcoDiv`：toIocDiv_wcovBy_toIcoDiv (a b : α) : toIocDiv 
hp a b ⩿ toIcoDiv hp a b
-/
theorem toIcoMod_le_toIocMod (a b : α) : toIcoMod hp a b ≤ toIocMod hp a b := by
  rw [toIcoMod, toIocMod, sub_le_sub_iff_left]
  exact zsmul_left_mono hp.le (toIocDiv_wcovBy_toIcoDiv _ _ _).le
/-
**toIocMod_le_toIcoMod_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocMod_le_toIcoMod_add (a b : α) : toIocMod hp a b <= toIcoMod hp a b + 
p
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIcoMod.eq_1`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : Linear
Order α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p : α} (hp : 0 
< p…
· 使用定理 `toIocMod.eq_1`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : Linear
Order α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p : α} (hp : 0 
< p…
· 使用定理 `sub_add`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c : α), 
a - b + c = a - (b - c)
· 使用定理 `sub_le_sub_iff_left`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] 
[AddLeftMono α] [AddRightMono α] {b c : α} (a : α),   a - b ≤ a - c ↔ c ≤ b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `sub_le_iff_le_add`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [A
ddRightMono α] {a b c : α}, a - c ≤ b ↔ a ≤ b + c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_one_zsmul`：∀ {G : Type u_3} [inst : AddGroup G] (a : G) (n : ℤ), (n 
+ 1) • a = n • a + a
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用定理 `zsmul_left_strictMono`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 
: PartialOrder α] [IsOrderedAddMonoid α] {a : α},   0 < a → StrictMono fun n => 
n • a
· 使用定理 `WCovBy.le_succ`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : SuccOrder
 α] {a b : α}, a ⩿ b → b ≤ Order.succ a
· 使用定理 `toIocDiv_wcovBy_toIcoDiv`：toIocDiv_wcovBy_toIcoDiv (a b : α) : toIocDiv 
hp a b ⩿ toIcoDiv hp a b
-/
theorem toIocMod_le_toIcoMod_add (a b : α) : toIocMod hp a b ≤ toIcoMod hp a b + p := by
  rw [toIcoMod, toIocMod, sub_add, sub_le_sub_iff_left, sub_le_iff_le_add, ← add_one_zsmul,
    (zsmul_left_strictMono hp).le_iff_le]
  apply (toIocDiv_wcovBy_toIcoDiv _ _ _).le_succ

end IcoIoc

open AddCommGroup

/-
**toIcoMod_eq_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoMod_eq_self : toIcoMod hp a b = b ↔ b in Set.Ico a (a + p)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIcoMod_eq_iff`：toIcoMod_eq_iff : toIcoMod hp a b = c ↔ c in Set.Ico a 
(a + p) ∧ exists z : Int, b = c + z • p
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toIcoMod_eq_self : toIcoMod hp a b = b ↔ b ∈ Set.Ico a (a + p) := by
  rw [toIcoMod_eq_iff, and_iff_left]
  exact ⟨0, by simp⟩
/-
**toIocMod_eq_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocMod_eq_self : toIocMod hp a b = b ↔ b in Set.Ioc a (a + p)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIocMod_eq_iff`：toIocMod_eq_iff : toIocMod hp a b = c ↔ c in Set.Ioc a 
(a + p) ∧ exists z : Int, b = c + z • p
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toIocMod_eq_self : toIocMod hp a b = b ↔ b ∈ Set.Ioc a (a + p) := by
  rw [toIocMod_eq_iff, and_iff_left]
  exact ⟨0, by simp⟩

@[simp]
/-
**toIcoMod_toIcoMod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoMod_toIcoMod (a₁ a₂ b : α) : toIcoMod hp a₁ (toIcoMod hp a₂ b) = toIc
oMod hp a₁ b
参数：a₁ a₂ b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `toIcoMod_eq_toIcoMod`：toIcoMod_eq_toIcoMod : toIcoMod hp a b = toIcoMod 
hp a c ↔ exists n : Int, c - b = n • p
· 使用定理 `self_sub_toIcoMod`：self_sub_toIcoMod (a b : α) : b - toIcoMod hp a b = t
oIcoDiv hp a b • p
-/
theorem toIcoMod_toIcoMod (a₁ a₂ b : α) : toIcoMod hp a₁ (toIcoMod hp a₂ b) = toIcoMod hp a₁ b :=
  (toIcoMod_eq_toIcoMod _).2 ⟨toIcoDiv hp a₂ b, self_sub_toIcoMod hp a₂ b⟩

@[simp]
/-
**toIcoMod_toIocMod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoMod_toIocMod (a₁ a₂ b : α) : toIcoMod hp a₁ (toIocMod hp a₂ b) = toIc
oMod hp a₁ b
参数：a₁ a₂ b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `toIcoMod_eq_toIcoMod`：toIcoMod_eq_toIcoMod : toIcoMod hp a b = toIcoMod 
hp a c ↔ exists n : Int, c - b = n • p
· 使用定理 `self_sub_toIocMod`：self_sub_toIocMod (a b : α) : b - toIocMod hp a b = t
oIocDiv hp a b • p
-/
theorem toIcoMod_toIocMod (a₁ a₂ b : α) : toIcoMod hp a₁ (toIocMod hp a₂ b) = toIcoMod hp a₁ b :=
  (toIcoMod_eq_toIcoMod _).2 ⟨toIocDiv hp a₂ b, self_sub_toIocMod hp a₂ b⟩

@[simp]
/-
**toIocMod_toIocMod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocMod_toIocMod (a₁ a₂ b : α) : toIocMod hp a₁ (toIocMod hp a₂ b) = toIo
cMod hp a₁ b
参数：a₁ a₂ b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `toIocMod_eq_toIocMod`：toIocMod_eq_toIocMod : toIocMod hp a b = toIocMod 
hp a c ↔ exists n : Int, c - b = n • p
· 使用定理 `self_sub_toIocMod`：self_sub_toIocMod (a b : α) : b - toIocMod hp a b = t
oIocDiv hp a b • p
-/
theorem toIocMod_toIocMod (a₁ a₂ b : α) : toIocMod hp a₁ (toIocMod hp a₂ b) = toIocMod hp a₁ b :=
  (toIocMod_eq_toIocMod _).2 ⟨toIocDiv hp a₂ b, self_sub_toIocMod hp a₂ b⟩

@[simp]
/-
**toIocMod_toIcoMod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocMod_toIcoMod (a₁ a₂ b : α) : toIocMod hp a₁ (toIcoMod hp a₂ b) = toIo
cMod hp a₁ b
参数：a₁ a₂ b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `toIocMod_eq_toIocMod`：toIocMod_eq_toIocMod : toIocMod hp a b = toIocMod 
hp a c ↔ exists n : Int, c - b = n • p
· 使用定理 `self_sub_toIcoMod`：self_sub_toIcoMod (a b : α) : b - toIcoMod hp a b = t
oIcoDiv hp a b • p
-/
theorem toIocMod_toIcoMod (a₁ a₂ b : α) : toIocMod hp a₁ (toIcoMod hp a₂ b) = toIocMod hp a₁ b :=
  (toIocMod_eq_toIocMod _).2 ⟨toIcoDiv hp a₂ b, self_sub_toIcoMod hp a₂ b⟩
/-
**toIcoMod_periodic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoMod_periodic (a : α) : Function.Periodic (toIcoMod hp a) p
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `toIcoMod_add_right`：toIcoMod_add_right (a b : α) : toIcoMod hp a (b + p)
 = toIcoMod hp a b
-/
theorem toIcoMod_periodic (a : α) : Function.Periodic (toIcoMod hp a) p :=
  toIcoMod_add_right hp a
/-
**toIocMod_periodic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocMod_periodic (a : α) : Function.Periodic (toIocMod hp a) p
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `toIocMod_add_right`：toIocMod_add_right (a b : α) : toIocMod hp a (b + p)
 = toIocMod hp a b
-/
theorem toIocMod_periodic (a : α) : Function.Periodic (toIocMod hp a) p :=
  toIocMod_add_right hp a

-- helper lemmas for when `a = 0`
section Zero

/-
**toIcoMod_zero_sub_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoMod_zero_sub_comm (a b : α) : toIcoMod hp 0 (a - b) = p - toIocMod hp
 0 (b - a)
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `toIcoMod_neg`：toIcoMod_neg (a b : α) : toIcoMod hp a (-b) = p - toIocMod
 hp (-a) b
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
-/
theorem toIcoMod_zero_sub_comm (a b : α) : toIcoMod hp 0 (a - b) = p - toIocMod hp 0 (b - a) := by
  rw [← neg_sub, toIcoMod_neg, neg_zero]
/-
**toIocMod_zero_sub_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocMod_zero_sub_comm (a b : α) : toIocMod hp 0 (a - b) = p - toIcoMod hp
 0 (b - a)
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `toIocMod_neg`：toIocMod_neg (a b : α) : toIocMod hp a (-b) = p - toIcoMod
 hp (-a) b
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
-/
theorem toIocMod_zero_sub_comm (a b : α) : toIocMod hp 0 (a - b) = p - toIcoMod hp 0 (b - a) := by
  rw [← neg_sub, toIocMod_neg, neg_zero]
/-
**toIcoDiv_eq_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoDiv_eq_sub (a b : α) : toIcoDiv hp a b = toIcoDiv hp 0 (b - a)
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIcoDiv_sub_eq_toIcoDiv_add`：toIcoDiv_sub_eq_toIcoDiv_add (a b c : α) :
 toIcoDiv hp a (b - c) = toIcoDiv hp (a + c) b
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem toIcoDiv_eq_sub (a b : α) : toIcoDiv hp a b = toIcoDiv hp 0 (b - a) := by
  rw [toIcoDiv_sub_eq_toIcoDiv_add, zero_add]
/-
**toIocDiv_eq_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocDiv_eq_sub (a b : α) : toIocDiv hp a b = toIocDiv hp 0 (b - a)
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIocDiv_sub_eq_toIocDiv_add`：toIocDiv_sub_eq_toIocDiv_add (a b c : α) :
 toIocDiv hp a (b - c) = toIocDiv hp (a + c) b
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem toIocDiv_eq_sub (a b : α) : toIocDiv hp a b = toIocDiv hp 0 (b - a) := by
  rw [toIocDiv_sub_eq_toIocDiv_add, zero_add]
/-
**toIcoMod_eq_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoMod_eq_sub (a b : α) : toIcoMod hp a b = toIcoMod hp 0 (b - a) + a
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIcoMod_sub_eq_sub`：toIcoMod_sub_eq_sub (a b c : α) : toIcoMod hp a (b 
- c) = toIcoMod hp (a + c) b - c
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
-/
theorem toIcoMod_eq_sub (a b : α) : toIcoMod hp a b = toIcoMod hp 0 (b - a) + a := by
  rw [toIcoMod_sub_eq_sub, zero_add, sub_add_cancel]
/-
**toIocMod_eq_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocMod_eq_sub (a b : α) : toIocMod hp a b = toIocMod hp 0 (b - a) + a
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIocMod_sub_eq_sub`：toIocMod_sub_eq_sub (a b c : α) : toIocMod hp a (b 
- c) = toIocMod hp (a + c) b - c
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
-/
theorem toIocMod_eq_sub (a b : α) : toIocMod hp a b = toIocMod hp 0 (b - a) + a := by
  rw [toIocMod_sub_eq_sub, zero_add, sub_add_cancel]
/-
**toIcoMod_add_toIocMod_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoMod_add_toIocMod_zero (a b : α) : toIcoMod hp 0 (a - b) + toIocMod hp
 0 (b - a) = p
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIcoMod_zero_sub_comm`：toIcoMod_zero_sub_comm (a b : α) : toIcoMod hp 0
 (a - b) = p - toIocMod hp 0 (b - a)
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
-/
theorem toIcoMod_add_toIocMod_zero (a b : α) :
    toIcoMod hp 0 (a - b) + toIocMod hp 0 (b - a) = p := by
  rw [toIcoMod_zero_sub_comm, sub_add_cancel]
/-
**toIocMod_add_toIcoMod_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocMod_add_toIcoMod_zero (a b : α) : toIocMod hp 0 (a - b) + toIcoMod hp
 0 (b - a) = p
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `toIcoMod_add_toIocMod_zero`：toIcoMod_add_toIocMod_zero (a b : α) : toIco
Mod hp 0 (a - b) + toIocMod hp 0 (b - a) = p
-/
theorem toIocMod_add_toIcoMod_zero (a b : α) :
    toIocMod hp 0 (a - b) + toIcoMod hp 0 (b - a) = p := by
  rw [_root_.add_comm, toIcoMod_add_toIocMod_zero]

end Zero

/-- `toIcoMod` as an equiv from the quotient. -/
@[simps symm_apply]
/-
**QuotientAddGroup.equivIcoMod** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：QuotientAddGroup.equivIcoMod (a : α) : α ⧸ AddSubgroup.zmultiples p ≃ Set.
Ico a (a + p) where toFun b
参数：a : α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `toIcoMod_periodic`：toIcoMod_periodic (a : α) : Function.Periodic (toIcoM
od hp a) p

--- 原说明 ---
`toIcoMod` as an equiv from the quotient.
-/
def QuotientAddGroup.equivIcoMod (a : α) : α ⧸ AddSubgroup.zmultiples p ≃ Set.Ico a (a + p) where
  toFun b :=
    ⟨(toIcoMod_periodic hp a).lift b, QuotientAddGroup.induction_on b <| toIcoMod_mem_Ico hp a⟩
  invFun := (↑)
  right_inv b := Subtype.ext <| (toIcoMod_eq_self hp).mpr b.prop
  left_inv b := by
    induction b using QuotientAddGroup.induction_on
    dsimp
    rw [QuotientAddGroup.eq_iff_sub_mem, toIcoMod_sub_self]
    apply AddSubgroup.zsmul_mem_zmultiples

@[simp]
/-
**QuotientAddGroup.equivIcoMod_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：QuotientAddGroup.equivIcoMod_coe (a b : α) : QuotientAddGroup.equivIcoMod 
hp a ↑b = ⟨toIcoMod hp a b, toIcoMod_mem_Ico hp a _⟩
参数：a b : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem QuotientAddGroup.equivIcoMod_coe (a b : α) :
    QuotientAddGroup.equivIcoMod hp a ↑b = ⟨toIcoMod hp a b, toIcoMod_mem_Ico hp a _⟩ :=
  rfl

@[simp]
/-
**QuotientAddGroup.equivIcoMod_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：QuotientAddGroup.equivIcoMod_zero (a : α) : QuotientAddGroup.equivIcoMod h
p a 0 = ⟨toIcoMod hp a 0, toIcoMod_mem_Ico hp a _⟩
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem QuotientAddGroup.equivIcoMod_zero (a : α) :
    QuotientAddGroup.equivIcoMod hp a 0 = ⟨toIcoMod hp a 0, toIcoMod_mem_Ico hp a _⟩ :=
  rfl

/-- `toIocMod` as an equiv from the quotient. -/
@[simps symm_apply]
/-
**QuotientAddGroup.equivIocMod** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：QuotientAddGroup.equivIocMod (a : α) : α ⧸ AddSubgroup.zmultiples p ≃ Set.
Ioc a (a + p) where toFun b
参数：a : α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `toIocMod_periodic`：toIocMod_periodic (a : α) : Function.Periodic (toIocM
od hp a) p

--- 原说明 ---
`toIocMod` as an equiv from the quotient.
-/
def QuotientAddGroup.equivIocMod (a : α) : α ⧸ AddSubgroup.zmultiples p ≃ Set.Ioc a (a + p) where
  toFun b :=
    ⟨(toIocMod_periodic hp a).lift b, QuotientAddGroup.induction_on b <| toIocMod_mem_Ioc hp a⟩
  invFun := (↑)
  right_inv b := Subtype.ext <| (toIocMod_eq_self hp).mpr b.prop
  left_inv b := by
    induction b using QuotientAddGroup.induction_on
    dsimp
    rw [QuotientAddGroup.eq_iff_sub_mem, toIocMod_sub_self]
    apply AddSubgroup.zsmul_mem_zmultiples

@[simp]
/-
**QuotientAddGroup.equivIocMod_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：QuotientAddGroup.equivIocMod_coe (a b : α) : QuotientAddGroup.equivIocMod 
hp a ↑b = ⟨toIocMod hp a b, toIocMod_mem_Ioc hp a _⟩
参数：a b : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem QuotientAddGroup.equivIocMod_coe (a b : α) :
    QuotientAddGroup.equivIocMod hp a ↑b = ⟨toIocMod hp a b, toIocMod_mem_Ioc hp a _⟩ :=
  rfl

@[simp]
/-
**QuotientAddGroup.equivIocMod_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：QuotientAddGroup.equivIocMod_zero (a : α) : QuotientAddGroup.equivIocMod h
p a 0 = ⟨toIocMod hp a 0, toIocMod_mem_Ioc hp a _⟩
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem QuotientAddGroup.equivIocMod_zero (a : α) :
    QuotientAddGroup.equivIocMod hp a 0 = ⟨toIocMod hp a 0, toIocMod_mem_Ioc hp a _⟩ :=
  rfl
end

/-!
### The circular order structure on `α ⧸ AddSubgroup.zmultiples p`
-/


section Circular

open AddCommGroup

/-
**toIxxMod_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem toIxxMod_iff (x₁ x₂ x₃ : α) : toIcoMod hp x₁ x₂ ≤ toIocMod hp x₁ x₃ ↔
    toIcoMod hp 0 (x₂ - x₁) + toIcoMod hp 0 (x₁ - x₃) ≤ p := by
  rw [toIcoMod_eq_sub, toIocMod_eq_sub _ x₁, add_le_add_iff_right, ← neg_sub x₁ x₃, toIocMod_neg,
    neg_zero, le_sub_iff_add_le]
/-
**toIxxMod_cyclic_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem toIxxMod_cyclic_left {x₁ x₂ x₃ : α} (h : toIcoMod hp x₁ x₂ ≤ toIocMod hp x₁ x₃) :
    toIcoMod hp x₂ x₃ ≤ toIocMod hp x₂ x₁ := by
  let x₂' := toIcoMod hp x₁ x₂
  let x₃' := toIcoMod hp x₂' x₃
  have h : x₂' ≤ toIocMod hp x₁ x₃' := by simpa [x₃']
  have h₂₁ : x₂' < x₁ + p := toIcoMod_lt_right _ _ _
  have h₃₂ : x₃' - p < x₂' := sub_lt_iff_lt_add.2 (toIcoMod_lt_right _ _ _)
  suffices hequiv : x₃' ≤ toIocMod hp x₂' x₁ by
    obtain ⟨z, hd⟩ : ∃ z : ℤ, x₂ = x₂' + z • p := ((toIcoMod_eq_iff hp).1 rfl).2
    simpa [hd, toIocMod_add_zsmul', toIcoMod_add_zsmul', add_le_add_iff_right]
  rcases le_or_gt x₃' (x₁ + p) with h₃₁ | h₁₃
  · suffices hIoc₂₁ : toIocMod hp x₂' x₁ = x₁ + p from hIoc₂₁.trans_ge h₃₁
    apply (toIocMod_eq_iff hp).2
    exact ⟨⟨h₂₁, by simp [x₂', left_le_toIcoMod]⟩, -1, by simp⟩
  have hIoc₁₃ : toIocMod hp x₁ x₃' = x₃' - p := by
    apply (toIocMod_eq_iff hp).2
    exact ⟨⟨lt_sub_iff_add_lt.2 h₁₃, le_of_lt (h₃₂.trans h₂₁)⟩, 1, by simp⟩
  have not_h₃₂ := (h.trans hIoc₁₃.le).not_gt
  contradiction
/-
**toIxxMod_antisymm** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem toIxxMod_antisymm (h₁₂₃ : toIcoMod hp a b ≤ toIocMod hp a c)
    (h₁₃₂ : toIcoMod hp a c ≤ toIocMod hp a b) :
    b ≡ a [PMOD p] ∨ c ≡ b [PMOD p] ∨ a ≡ c [PMOD p] := by
  by_contra! h
  rw [modEq_comm] at h
  rw [← (not_modEq_iff_toIcoMod_eq_toIocMod hp).mp h.2.2] at h₁₂₃
  rw [← (not_modEq_iff_toIcoMod_eq_toIocMod hp).mp h.1] at h₁₃₂
  exact h.2.1 ((toIcoMod_inj _).1 <| h₁₃₂.antisymm h₁₂₃)
/-
**toIxxMod_total'** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem toIxxMod_total' (a b c : α) :
    toIcoMod hp b a ≤ toIocMod hp b c ∨ toIcoMod hp b c ≤ toIocMod hp b a := by
  /- an essential ingredient is the lemma saying {a-b} + {b-a} = period if a ≠ b (and = 0 if a = b).
    Thus if a ≠ b and b ≠ c then ({a-b} + {b-c}) + ({c-b} + {b-a}) = 2 * period, so one of
    `{a-b} + {b-c}` and `{c-b} + {b-a}` must be `≤ period` -/
  have := congr_arg₂ (· + ·) (toIcoMod_add_toIocMod_zero hp a b) (toIcoMod_add_toIocMod_zero hp c b)
  simp only [add_add_add_comm] at this
  rw [_root_.add_comm (toIocMod _ _ _), add_add_add_comm, ← two_nsmul] at this
  replace := min_le_of_add_le_two_nsmul this.le
  rw [min_le_iff] at this
  rw [toIxxMod_iff, toIxxMod_iff]
  grw [← toIcoMod_le_toIocMod, ← toIcoMod_le_toIocMod] at this
  exact this
/-
**toIxxMod_total** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem toIxxMod_total (a b c : α) :
    toIcoMod hp a b ≤ toIocMod hp a c ∨ toIcoMod hp c b ≤ toIocMod hp c a :=
  (toIxxMod_total' _ _ _ _).imp_right <| toIxxMod_cyclic_left _
/-
**toIxxMod_trans** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem toIxxMod_trans {x₁ x₂ x₃ x₄ : α}
    (h₁₂₃ : toIcoMod hp x₁ x₂ ≤ toIocMod hp x₁ x₃ ∧ ¬toIcoMod hp x₃ x₂ ≤ toIocMod hp x₃ x₁)
    (h₂₃₄ : toIcoMod hp x₂ x₄ ≤ toIocMod hp x₂ x₃ ∧ ¬toIcoMod hp x₃ x₄ ≤ toIocMod hp x₃ x₂) :
    toIcoMod hp x₁ x₄ ≤ toIocMod hp x₁ x₃ ∧ ¬toIcoMod hp x₃ x₄ ≤ toIocMod hp x₃ x₁ := by
  constructor
  · suffices h : ¬x₃ ≡ x₂ [PMOD p] by
      have h₁₂₃' := toIxxMod_cyclic_left _ (toIxxMod_cyclic_left _ h₁₂₃.1)
      have h₂₃₄' := toIxxMod_cyclic_left _ (toIxxMod_cyclic_left _ h₂₃₄.1)
      rw [(not_modEq_iff_toIcoMod_eq_toIocMod hp).1 h] at h₂₃₄'
      exact toIxxMod_cyclic_left _ (h₁₂₃'.trans h₂₃₄')
    by_contra h
    rw [(modEq_iff_toIcoMod_eq_left hp).1 h] at h₁₂₃
    exact h₁₂₃.2 (left_lt_toIocMod _ _ _).le
  · rw [not_le] at h₁₂₃ h₂₃₄ ⊢
    exact (h₁₂₃.2.trans_le (toIcoMod_le_toIocMod _ x₃ x₂)).trans h₂₃₄.2

namespace QuotientAddGroup

variable [hp' : Fact (0 < p)]

/-
**QuotientAddGroup.** 是 Mathlib 中的一个实例，位于命名空间 `QuotientAddGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Btw (α ⧸ AddSubgroup.zmultiples p) where
  btw x₁ x₂ x₃ := (equivIcoMod hp'.out 0 (x₂ - x₁) : α) ≤ equivIocMod hp'.out 0 (x₃ - x₁)
/-
**QuotientAddGroup.btw_coe_iff'** 是 Mathlib 中的一个定理，位于命名空间 `QuotientAddGroup`。
形式化陈述：btw_coe_iff' {x₁ x₂ x₃ : α} : Btw.btw (x₁ : α ⧸ AddSubgroup.zmultiples p) 
x₂ x₃ ↔ toIcoMod hp'.out 0 (x₂ - x₁) <= toIocMod hp'.out 0 (x₃ - x₁)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem btw_coe_iff' {x₁ x₂ x₃ : α} :
    Btw.btw (x₁ : α ⧸ AddSubgroup.zmultiples p) x₂ x₃ ↔
      toIcoMod hp'.out 0 (x₂ - x₁) ≤ toIocMod hp'.out 0 (x₃ - x₁) :=
  Iff.rfl

-- maybe harder to use than the primed one?
/-
**QuotientAddGroup.btw_coe_iff** 是 Mathlib 中的一个定理，位于命名空间 `QuotientAddGroup`。
形式化陈述：btw_coe_iff {x₁ x₂ x₃ : α} : Btw.btw (x₁ : α ⧸ AddSubgroup.zmultiples p) x
₂ x₃ ↔ toIcoMod hp'.out x₁ x₂ <= toIocMod hp'.out x₁ x₃
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QuotientAddGroup.btw_coe_iff'`：btw_coe_iff' {x₁ x₂ x₃ : α} : Btw.btw (x₁
 : α ⧸ AddSubgroup.zmultiples p) x₂ x₃ ↔ toIcoMod hp'.out 0 (x₂ - x₁) <= toIocMo
d hp'.out 0 (x₃ - x…
· 使用定理 `toIocMod_sub_eq_sub`：toIocMod_sub_eq_sub (a b c : α) : toIocMod hp a (b 
- c) = toIocMod hp (a + c) b - c
· 使用定理 `toIcoMod_sub_eq_sub`：toIcoMod_sub_eq_sub (a b c : α) : toIcoMod hp a (b 
- c) = toIcoMod hp (a + c) b - c
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `sub_le_sub_iff_right`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α]
 [AddRightMono α] {a b : α} (c : α), a - c ≤ b - c ↔ a ≤ b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem btw_coe_iff {x₁ x₂ x₃ : α} :
    Btw.btw (x₁ : α ⧸ AddSubgroup.zmultiples p) x₂ x₃ ↔
      toIcoMod hp'.out x₁ x₂ ≤ toIocMod hp'.out x₁ x₃ := by
  rw [btw_coe_iff', toIocMod_sub_eq_sub, toIcoMod_sub_eq_sub, zero_add, sub_le_sub_iff_right]
/-
**QuotientAddGroup.circularPreorder** 是 Mathlib 中的一个实例，位于命名空间 `QuotientAddGroup`
。
形式化陈述：circularPreorder : CircularPreorder (α ⧸ AddSubgroup.zmultiples p) where b
tw_refl x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance circularPreorder : CircularPreorder (α ⧸ AddSubgroup.zmultiples p) where
  btw_refl x := show _ ≤ _ by simp [sub_self, hp'.out.le]
  btw_cyclic_left {x₁ x₂ x₃} h := by
    induction x₁ using QuotientAddGroup.induction_on
    induction x₂ using QuotientAddGroup.induction_on
    induction x₃ using QuotientAddGroup.induction_on
    simp_rw [btw_coe_iff] at h ⊢
    apply toIxxMod_cyclic_left _ h
  sbtw := _
  sbtw_iff_btw_not_btw := Iff.rfl
  sbtw_trans_left {x₁ x₂ x₃ x₄} (h₁₂₃ : _ ∧ _) (h₂₃₄ : _ ∧ _) :=
    show _ ∧ _ by
      induction x₁ using QuotientAddGroup.induction_on
      induction x₂ using QuotientAddGroup.induction_on
      induction x₃ using QuotientAddGroup.induction_on
      induction x₄ using QuotientAddGroup.induction_on
      simp_rw [btw_coe_iff] at h₁₂₃ h₂₃₄ ⊢
      apply toIxxMod_trans _ h₁₂₃ h₂₃₄
/-
**QuotientAddGroup.circularOrder** 是 Mathlib 中的一个实例，位于命名空间 `QuotientAddGroup`。
形式化陈述：circularOrder : CircularOrder (α ⧸ AddSubgroup.zmultiples p)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance circularOrder : CircularOrder (α ⧸ AddSubgroup.zmultiples p) :=
  { QuotientAddGroup.circularPreorder with
    btw_antisymm := fun {x₁ x₂ x₃} h₁₂₃ h₃₂₁ => by
      induction x₁ using QuotientAddGroup.induction_on
      induction x₂ using QuotientAddGroup.induction_on
      induction x₃ using QuotientAddGroup.induction_on
      rw [btw_cyclic] at h₃₂₁
      simp_rw [btw_coe_iff] at h₁₂₃ h₃₂₁
      simp_rw [← modEq_iff_eq_mod_zmultiples]
      simpa only [modEq_comm] using toIxxMod_antisymm _ h₁₂₃ h₃₂₁
    btw_total := fun x₁ x₂ x₃ => by
      induction x₁ using QuotientAddGroup.induction_on
      induction x₂ using QuotientAddGroup.induction_on
      induction x₃ using QuotientAddGroup.induction_on
      simp_rw [btw_coe_iff]
      apply toIxxMod_total }

end QuotientAddGroup

end Circular

end LinearOrderedAddCommGroup

/-!
### `simp` confluence lemmas for rings

In rings, we simplify `(m : ℤ) • x` to `↑m * x`, so we need to restate some lemmas
using `↑m * x` instead of `m • x`. In some lemmas, `m` is a variable,
in other lemmas `m = toIcoDiv _ _ _` or `m = toIocDiv _ _ _`.
-/

section Ring

variable {R : Type*} [NonAssocRing R] [LinearOrder R] [IsOrderedAddMonoid R] [Archimedean R] {p : R}
  (hp : 0 < p)

@[simp]
/-
**self_sub_toIcoDiv_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：self_sub_toIcoDiv_mul (a b : R) : b - toIcoDiv hp a b * p = toIcoMod hp a 
b
参数：a b : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `self_sub_toIcoDiv_zsmul`：self_sub_toIcoDiv_zsmul (a b : α) : b - toIcoDi
v hp a b • p = toIcoMod hp a b
-/
theorem self_sub_toIcoDiv_mul (a b : R) : b - toIcoDiv hp a b * p = toIcoMod hp a b := by
  simpa using self_sub_toIcoDiv_zsmul hp a b

@[simp]
/-
**self_sub_toIocDiv_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：self_sub_toIocDiv_mul (a b : R) : b - toIocDiv hp a b * p = toIocMod hp a 
b
参数：a b : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `self_sub_toIocDiv_zsmul`：self_sub_toIocDiv_zsmul (a b : α) : b - toIocDi
v hp a b • p = toIocMod hp a b
-/
theorem self_sub_toIocDiv_mul (a b : R) : b - toIocDiv hp a b * p = toIocMod hp a b := by
  simpa using self_sub_toIocDiv_zsmul hp a b

@[simp]
/-
**toIcoDiv_mul_sub_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoDiv_mul_sub_self (a b : R) : toIcoDiv hp a b * p - b = -toIcoMod hp a
 b
参数：a b : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `toIcoDiv_zsmul_sub_self`：toIcoDiv_zsmul_sub_self (a b : α) : toIcoDiv hp
 a b • p - b = -toIcoMod hp a b
-/
theorem toIcoDiv_mul_sub_self (a b : R) : toIcoDiv hp a b * p - b = -toIcoMod hp a b := by
  simpa using toIcoDiv_zsmul_sub_self hp a b

@[simp]
/-
**toIocDiv_mul_sub_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocDiv_mul_sub_self (a b : R) : toIocDiv hp a b * p - b = -toIocMod hp a
 b
参数：a b : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `toIocDiv_zsmul_sub_self`：toIocDiv_zsmul_sub_self (a b : α) : toIocDiv hp
 a b • p - b = -toIocMod hp a b
-/
theorem toIocDiv_mul_sub_self (a b : R) : toIocDiv hp a b * p - b = -toIocMod hp a b := by
  simpa using toIocDiv_zsmul_sub_self hp a b
/-
**toIcoMod_sub_self_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoMod_sub_self_eq_mul (a b : R) : toIcoMod hp a b - b = -toIcoDiv hp a 
b * p
参数：a b : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIcoMod_sub_self`：toIcoMod_sub_self (a b : α) : toIcoMod hp a b - b = -
toIcoDiv hp a b • p
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toIcoMod_sub_self_eq_mul (a b : R) : toIcoMod hp a b - b = -toIcoDiv hp a b * p := by
  simp
/-
**toIocMod_sub_self_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocMod_sub_self_eq_mul (a b : R) : toIocMod hp a b - b = -toIocDiv hp a 
b * p
参数：a b : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIocMod_sub_self`：toIocMod_sub_self (a b : α) : toIocMod hp a b - b = -
toIocDiv hp a b • p
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toIocMod_sub_self_eq_mul (a b : R) : toIocMod hp a b - b = -toIocDiv hp a b * p := by
  simp
/-
**self_sub_toIcoMod_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：self_sub_toIcoMod_eq_mul (a b : R) : b - toIcoMod hp a b = toIcoDiv hp a b
 * p
参数：a b : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `self_sub_toIcoMod`：self_sub_toIcoMod (a b : α) : b - toIcoMod hp a b = t
oIcoDiv hp a b • p
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem self_sub_toIcoMod_eq_mul (a b : R) : b - toIcoMod hp a b = toIcoDiv hp a b * p := by
  simp
/-
**self_sub_toIocMod_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：self_sub_toIocMod_eq_mul (a b : R) : b - toIocMod hp a b = toIocDiv hp a b
 * p
参数：a b : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `self_sub_toIocMod`：self_sub_toIocMod (a b : α) : b - toIocMod hp a b = t
oIocDiv hp a b • p
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem self_sub_toIocMod_eq_mul (a b : R) : b - toIocMod hp a b = toIocDiv hp a b * p := by
  simp

@[simp]
/-
**toIcoMod_add_toIcoDiv_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoMod_add_toIcoDiv_mul (a b : R) : toIcoMod hp a b + toIcoDiv hp a b * 
p = b
参数：a b : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `toIcoMod_add_toIcoDiv_zsmul`：toIcoMod_add_toIcoDiv_zsmul (a b : α) : toI
coMod hp a b + toIcoDiv hp a b • p = b
-/
theorem toIcoMod_add_toIcoDiv_mul (a b : R) : toIcoMod hp a b + toIcoDiv hp a b * p = b := by
  simpa using toIcoMod_add_toIcoDiv_zsmul hp a b

@[simp]
/-
**toIocMod_add_toIocDiv_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocMod_add_toIocDiv_mul (a b : R) : toIocMod hp a b + toIocDiv hp a b * 
p = b
参数：a b : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `toIocMod_add_toIocDiv_zsmul`：toIocMod_add_toIocDiv_zsmul (a b : α) : toI
ocMod hp a b + toIocDiv hp a b • p = b
-/
theorem toIocMod_add_toIocDiv_mul (a b : R) : toIocMod hp a b + toIocDiv hp a b * p = b := by
  simpa using toIocMod_add_toIocDiv_zsmul hp a b

@[simp]
/-
**toIcoDiv_mul_sub_toIcoMod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoDiv_mul_sub_toIcoMod (a b : R) : toIcoDiv hp a b * p + toIcoMod hp a 
b = b
参数：a b : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `toIcoMod_add_toIcoDiv_mul`：toIcoMod_add_toIcoDiv_mul (a b : R) : toIcoMo
d hp a b + toIcoDiv hp a b * p = b
-/
theorem toIcoDiv_mul_sub_toIcoMod (a b : R) : toIcoDiv hp a b * p + toIcoMod hp a b = b := by
  rw [add_comm, toIcoMod_add_toIcoDiv_mul]

@[simp]
/-
**toIocDiv_mul_sub_toIocMod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocDiv_mul_sub_toIocMod (a b : R) : toIocDiv hp a b * p + toIocMod hp a 
b = b
参数：a b : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `toIocMod_add_toIocDiv_mul`：toIocMod_add_toIocDiv_mul (a b : R) : toIocMo
d hp a b + toIocDiv hp a b * p = b
-/
theorem toIocDiv_mul_sub_toIocMod (a b : R) : toIocDiv hp a b * p + toIocMod hp a b = b := by
  rw [add_comm, toIocMod_add_toIocDiv_mul]

@[simp]
/-
**toIcoDiv_add_intCast_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoDiv_add_intCast_mul (a b : R) (m : Int) : toIcoDiv hp a (b + m * p) =
 toIcoDiv hp a b + m
参数：a b : R；m : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIcoDiv.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `toIcoDiv_add_zsmul`：toIcoDiv_add_zsmul (a b : α) (m : Int) : toIcoDiv hp
 a (b + m • p) = toIcoDiv hp a b + m
-/
theorem toIcoDiv_add_intCast_mul (a b : R) (m : ℤ) :
    toIcoDiv hp a (b + m * p) = toIcoDiv hp a b + m := by
  simpa using toIcoDiv_add_zsmul hp a b m

@[simp]
/-
**toIcoDiv_add_natCast_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoDiv_add_natCast_mul (a b : R) (m : Nat) : toIcoDiv hp a (b + m * p) =
 toIcoDiv hp a b + m
参数：a b : R；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIcoDiv.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `toIcoDiv_add_intCast_mul`：toIcoDiv_add_intCast_mul (a b : R) (m : Int) :
 toIcoDiv hp a (b + m * p) = toIcoDiv hp a b + m
-/
theorem toIcoDiv_add_natCast_mul (a b : R) (m : ℕ) :
    toIcoDiv hp a (b + m * p) = toIcoDiv hp a b + m :=
  mod_cast toIcoDiv_add_intCast_mul hp a b m

@[simp]
/-
**toIcoDiv_add_ofNat_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoDiv_add_ofNat_mul (a b : R) (m : Nat) [m.AtLeastTwo] : toIcoDiv hp a 
(b + ofNat(m) * p) = toIcoDiv hp a b + ofNat(m)
参数：a b : R；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `toIcoDiv_add_natCast_mul`：toIcoDiv_add_natCast_mul (a b : R) (m : Nat) :
 toIcoDiv hp a (b + m * p) = toIcoDiv hp a b + m
-/
theorem toIcoDiv_add_ofNat_mul (a b : R) (m : ℕ) [m.AtLeastTwo] :
    toIcoDiv hp a (b + ofNat(m) * p) = toIcoDiv hp a b + ofNat(m) :=
  toIcoDiv_add_natCast_mul hp a b m

@[simp]
/-
**toIcoDiv_add_intCast_mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoDiv_add_intCast_mul' (a b : R) (m : Int) : toIcoDiv hp (a + m * p) b 
= toIcoDiv hp a b - m
参数：a b : R；m : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIcoDiv.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `toIcoDiv_add_zsmul'`：toIcoDiv_add_zsmul' (a b : α) (m : Int) : toIcoDiv 
hp (a + m • p) b = toIcoDiv hp a b - m
-/
theorem toIcoDiv_add_intCast_mul' (a b : R) (m : ℤ) :
    toIcoDiv hp (a + m * p) b = toIcoDiv hp a b - m := by
  simpa using toIcoDiv_add_zsmul' hp a b m

@[simp]
/-
**toIcoDiv_add_natCast_mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoDiv_add_natCast_mul' (a b : R) (m : Nat) : toIcoDiv hp (a + m * p) b 
= toIcoDiv hp a b - m
参数：a b : R；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIcoDiv.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `toIcoDiv_add_intCast_mul'`：toIcoDiv_add_intCast_mul' (a b : R) (m : Int)
 : toIcoDiv hp (a + m * p) b = toIcoDiv hp a b - m
-/
theorem toIcoDiv_add_natCast_mul' (a b : R) (m : ℕ) :
    toIcoDiv hp (a + m * p) b = toIcoDiv hp a b - m :=
  mod_cast toIcoDiv_add_intCast_mul' hp a b m

@[simp]
/-
**toIcoDiv_add_ofNat_mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoDiv_add_ofNat_mul' (a b : R) (m : Nat) [m.AtLeastTwo] : toIcoDiv hp (
a + ofNat(m) * p) b = toIcoDiv hp a b - ofNat(m)
参数：a b : R；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `toIcoDiv_add_natCast_mul'`：toIcoDiv_add_natCast_mul' (a b : R) (m : Nat)
 : toIcoDiv hp (a + m * p) b = toIcoDiv hp a b - m
-/
theorem toIcoDiv_add_ofNat_mul' (a b : R) (m : ℕ) [m.AtLeastTwo] :
    toIcoDiv hp (a + ofNat(m) * p) b = toIcoDiv hp a b - ofNat(m) :=
  toIcoDiv_add_natCast_mul' hp a b m

@[simp]
/-
**toIocDiv_add_intCast_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocDiv_add_intCast_mul (a b : R) (m : Int) : toIocDiv hp a (b + m * p) =
 toIocDiv hp a b + m
参数：a b : R；m : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIocDiv.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `toIocDiv_add_zsmul`：toIocDiv_add_zsmul (a b : α) (m : Int) : toIocDiv hp
 a (b + m • p) = toIocDiv hp a b + m
-/
theorem toIocDiv_add_intCast_mul (a b : R) (m : ℤ) :
    toIocDiv hp a (b + m * p) = toIocDiv hp a b + m := by
  simpa using toIocDiv_add_zsmul hp a b m

@[simp]
/-
**toIocDiv_add_natCast_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocDiv_add_natCast_mul (a b : R) (m : Nat) : toIocDiv hp a (b + m * p) =
 toIocDiv hp a b + m
参数：a b : R；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIocDiv.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `toIocDiv_add_intCast_mul`：toIocDiv_add_intCast_mul (a b : R) (m : Int) :
 toIocDiv hp a (b + m * p) = toIocDiv hp a b + m
-/
theorem toIocDiv_add_natCast_mul (a b : R) (m : ℕ) :
    toIocDiv hp a (b + m * p) = toIocDiv hp a b + m :=
  mod_cast toIocDiv_add_intCast_mul hp a b m

@[simp]
/-
**toIocDiv_add_ofNat_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocDiv_add_ofNat_mul (a b : R) (m : Nat) [m.AtLeastTwo] : toIocDiv hp a 
(b + ofNat(m) * p) = toIocDiv hp a b + ofNat(m)
参数：a b : R；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `toIocDiv_add_natCast_mul`：toIocDiv_add_natCast_mul (a b : R) (m : Nat) :
 toIocDiv hp a (b + m * p) = toIocDiv hp a b + m
-/
theorem toIocDiv_add_ofNat_mul (a b : R) (m : ℕ) [m.AtLeastTwo] :
    toIocDiv hp a (b + ofNat(m) * p) = toIocDiv hp a b + ofNat(m) :=
  toIocDiv_add_natCast_mul hp a b m

@[simp]
/-
**toIocDiv_add_intCast_mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocDiv_add_intCast_mul' (a b : R) (m : Int) : toIocDiv hp (a + m * p) b 
= toIocDiv hp a b - m
参数：a b : R；m : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIocDiv.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `toIocDiv_add_zsmul'`：toIocDiv_add_zsmul' (a b : α) (m : Int) : toIocDiv 
hp (a + m • p) b = toIocDiv hp a b - m
-/
theorem toIocDiv_add_intCast_mul' (a b : R) (m : ℤ) :
    toIocDiv hp (a + m * p) b = toIocDiv hp a b - m := by
  simpa using toIocDiv_add_zsmul' hp a b m

@[simp]
/-
**toIocDiv_add_natCast_mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocDiv_add_natCast_mul' (a b : R) (m : Nat) : toIocDiv hp (a + m * p) b 
= toIocDiv hp a b - m
参数：a b : R；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIocDiv.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `toIocDiv_add_intCast_mul'`：toIocDiv_add_intCast_mul' (a b : R) (m : Int)
 : toIocDiv hp (a + m * p) b = toIocDiv hp a b - m
-/
theorem toIocDiv_add_natCast_mul' (a b : R) (m : ℕ) :
    toIocDiv hp (a + m * p) b = toIocDiv hp a b - m :=
  mod_cast toIocDiv_add_intCast_mul' hp a b m

@[simp]
/-
**toIocDiv_add_ofNat_mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocDiv_add_ofNat_mul' (a b : R) (m : Nat) [m.AtLeastTwo] : toIocDiv hp (
a + ofNat(m) * p) b = toIocDiv hp a b - ofNat(m)
参数：a b : R；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `toIocDiv_add_natCast_mul'`：toIocDiv_add_natCast_mul' (a b : R) (m : Nat)
 : toIocDiv hp (a + m * p) b = toIocDiv hp a b - m
-/
theorem toIocDiv_add_ofNat_mul' (a b : R) (m : ℕ) [m.AtLeastTwo] :
    toIocDiv hp (a + ofNat(m) * p) b = toIocDiv hp a b - ofNat(m) :=
  toIocDiv_add_natCast_mul' hp a b m

@[simp]
/-
**toIcoDiv_intCast_mul_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoDiv_intCast_mul_add (a b : R) (m : Int) : toIcoDiv hp a (m * p + b) =
 m + toIcoDiv hp a b
参数：a b : R；m : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIcoDiv.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `toIcoDiv_zsmul_add`：toIcoDiv_zsmul_add (a b : α) (m : Int) : toIcoDiv hp
 a (m • p + b) = m + toIcoDiv hp a b
-/
theorem toIcoDiv_intCast_mul_add (a b : R) (m : ℤ) :
    toIcoDiv hp a (m * p + b) = m + toIcoDiv hp a b := by
  simpa using toIcoDiv_zsmul_add hp a b m

@[simp]
/-
**toIcoDiv_natCast_mul_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoDiv_natCast_mul_add (a b : R) (m : Nat) : toIcoDiv hp a (m * p + b) =
 m + toIcoDiv hp a b
参数：a b : R；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIcoDiv.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `toIcoDiv_intCast_mul_add`：toIcoDiv_intCast_mul_add (a b : R) (m : Int) :
 toIcoDiv hp a (m * p + b) = m + toIcoDiv hp a b
-/
theorem toIcoDiv_natCast_mul_add (a b : R) (m : ℕ) :
    toIcoDiv hp a (m * p + b) = m + toIcoDiv hp a b :=
  mod_cast toIcoDiv_intCast_mul_add hp a b m

@[simp]
/-
**toIcoDiv_ofNat_mul_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoDiv_ofNat_mul_add (a b : R) (m : Nat) [m.AtLeastTwo] : toIcoDiv hp a 
(ofNat(m) * p + b) = ofNat(m) + toIcoDiv hp a b
参数：a b : R；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `toIcoDiv_natCast_mul_add`：toIcoDiv_natCast_mul_add (a b : R) (m : Nat) :
 toIcoDiv hp a (m * p + b) = m + toIcoDiv hp a b
-/
theorem toIcoDiv_ofNat_mul_add (a b : R) (m : ℕ) [m.AtLeastTwo] :
    toIcoDiv hp a (ofNat(m) * p + b) = ofNat(m) + toIcoDiv hp a b :=
  toIcoDiv_natCast_mul_add hp a b m

/-! Note we omit `toIcoDiv_intCast_mul_add'` as `-m + toIcoDiv hp a b` is not very convenient. -/

@[simp]
/-
**toIocDiv_intCast_mul_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocDiv_intCast_mul_add (a b : R) (m : Int) : toIocDiv hp a (m * p + b) =
 m + toIocDiv hp a b
参数：a b : R；m : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIocDiv.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `toIocDiv_zsmul_add`：toIocDiv_zsmul_add (a b : α) (m : Int) : toIocDiv hp
 a (m • p + b) = m + toIocDiv hp a b

--- 原说明 ---
Note we omit `toIcoDiv_intCast_mul_add'` as `-m + toIcoDiv hp a b` is not very c
onvenient.
-/
theorem toIocDiv_intCast_mul_add (a b : R) (m : ℤ) :
    toIocDiv hp a (m * p + b) = m + toIocDiv hp a b := by
  simpa using toIocDiv_zsmul_add hp a b m

@[simp]
/-
**toIocDiv_natCast_mul_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocDiv_natCast_mul_add (a b : R) (m : Nat) : toIocDiv hp a (m * p + b) =
 m + toIocDiv hp a b
参数：a b : R；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIocDiv.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `toIocDiv_intCast_mul_add`：toIocDiv_intCast_mul_add (a b : R) (m : Int) :
 toIocDiv hp a (m * p + b) = m + toIocDiv hp a b
-/
theorem toIocDiv_natCast_mul_add (a b : R) (m : ℕ) :
    toIocDiv hp a (m * p + b) = m + toIocDiv hp a b :=
  mod_cast toIocDiv_intCast_mul_add hp a b m

@[simp]
/-
**toIocDiv_ofNat_mul_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocDiv_ofNat_mul_add (a b : R) (m : Nat) [m.AtLeastTwo] : toIocDiv hp a 
(ofNat(m) * p + b) = ofNat(m) + toIocDiv hp a b
参数：a b : R；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `toIocDiv_natCast_mul_add`：toIocDiv_natCast_mul_add (a b : R) (m : Nat) :
 toIocDiv hp a (m * p + b) = m + toIocDiv hp a b
-/
theorem toIocDiv_ofNat_mul_add (a b : R) (m : ℕ) [m.AtLeastTwo] :
    toIocDiv hp a (ofNat(m) * p + b) = ofNat(m) + toIocDiv hp a b :=
  toIocDiv_natCast_mul_add hp a b m

/-! Note we omit `toIocDiv_intCast_mul_add'` as `-m + toIocDiv hp a b` is not very convenient. -/

@[simp]
/-
**toIcoDiv_sub_intCast_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoDiv_sub_intCast_mul (a b : R) (m : Int) : toIcoDiv hp a (b - m * p) =
 toIcoDiv hp a b - m
参数：a b : R；m : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIcoDiv.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `toIcoDiv_sub_zsmul`：toIcoDiv_sub_zsmul (a b : α) (m : Int) : toIcoDiv hp
 a (b - m • p) = toIcoDiv hp a b - m

--- 原说明 ---
Note we omit `toIocDiv_intCast_mul_add'` as `-m + toIocDiv hp a b` is not very c
onvenient.
-/
theorem toIcoDiv_sub_intCast_mul (a b : R) (m : ℤ) :
    toIcoDiv hp a (b - m * p) = toIcoDiv hp a b - m := by
  simpa using toIcoDiv_sub_zsmul hp a b m

@[simp]
/-
**toIcoDiv_sub_natCast_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoDiv_sub_natCast_mul (a b : R) (m : Nat) : toIcoDiv hp a (b - m * p) =
 toIcoDiv hp a b - m
参数：a b : R；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIcoDiv.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `toIcoDiv_sub_intCast_mul`：toIcoDiv_sub_intCast_mul (a b : R) (m : Int) :
 toIcoDiv hp a (b - m * p) = toIcoDiv hp a b - m
-/
theorem toIcoDiv_sub_natCast_mul (a b : R) (m : ℕ) :
    toIcoDiv hp a (b - m * p) = toIcoDiv hp a b - m :=
  mod_cast toIcoDiv_sub_intCast_mul hp a b m

@[simp]
/-
**toIcoDiv_sub_ofNat_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoDiv_sub_ofNat_mul (a b : R) (m : Nat) [m.AtLeastTwo] : toIcoDiv hp a 
(b - ofNat(m) * p) = toIcoDiv hp a b - ofNat(m)
参数：a b : R；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `toIcoDiv_sub_natCast_mul`：toIcoDiv_sub_natCast_mul (a b : R) (m : Nat) :
 toIcoDiv hp a (b - m * p) = toIcoDiv hp a b - m
-/
theorem toIcoDiv_sub_ofNat_mul (a b : R) (m : ℕ) [m.AtLeastTwo] :
    toIcoDiv hp a (b - ofNat(m) * p) = toIcoDiv hp a b - ofNat(m) :=
  toIcoDiv_sub_natCast_mul hp a b m

@[simp]
/-
**toIcoDiv_sub_intCast_mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoDiv_sub_intCast_mul' (a b : R) (m : Int) : toIcoDiv hp (a - m * p) b 
= toIcoDiv hp a b + m
参数：a b : R；m : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIcoDiv.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `toIcoDiv_sub_zsmul'`：toIcoDiv_sub_zsmul' (a b : α) (m : Int) : toIcoDiv 
hp (a - m • p) b = toIcoDiv hp a b + m
-/
theorem toIcoDiv_sub_intCast_mul' (a b : R) (m : ℤ) :
    toIcoDiv hp (a - m * p) b = toIcoDiv hp a b + m := by
  simpa using toIcoDiv_sub_zsmul' hp a b m

@[simp]
/-
**toIcoDiv_sub_natCast_mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoDiv_sub_natCast_mul' (a b : R) (m : Nat) : toIcoDiv hp (a - m * p) b 
= toIcoDiv hp a b + m
参数：a b : R；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIcoDiv.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `toIcoDiv_sub_intCast_mul'`：toIcoDiv_sub_intCast_mul' (a b : R) (m : Int)
 : toIcoDiv hp (a - m * p) b = toIcoDiv hp a b + m
-/
theorem toIcoDiv_sub_natCast_mul' (a b : R) (m : ℕ) :
    toIcoDiv hp (a - m * p) b = toIcoDiv hp a b + m :=
  mod_cast toIcoDiv_sub_intCast_mul' hp a b m

@[simp]
/-
**toIcoDiv_sub_ofNat_mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoDiv_sub_ofNat_mul' (a b : R) (m : Nat) [m.AtLeastTwo] : toIcoDiv hp (
a - ofNat(m) * p) b = toIcoDiv hp a b + ofNat(m)
参数：a b : R；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `toIcoDiv_sub_natCast_mul'`：toIcoDiv_sub_natCast_mul' (a b : R) (m : Nat)
 : toIcoDiv hp (a - m * p) b = toIcoDiv hp a b + m
-/
theorem toIcoDiv_sub_ofNat_mul' (a b : R) (m : ℕ) [m.AtLeastTwo] :
    toIcoDiv hp (a - ofNat(m) * p) b = toIcoDiv hp a b + ofNat(m) :=
  toIcoDiv_sub_natCast_mul' hp a b m

@[simp]
/-
**toIocDiv_sub_intCast_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocDiv_sub_intCast_mul (a b : R) (m : Int) : toIocDiv hp a (b - m * p) =
 toIocDiv hp a b - m
参数：a b : R；m : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIocDiv.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `toIocDiv_sub_zsmul`：toIocDiv_sub_zsmul (a b : α) (m : Int) : toIocDiv hp
 a (b - m • p) = toIocDiv hp a b - m
-/
theorem toIocDiv_sub_intCast_mul (a b : R) (m : ℤ) :
    toIocDiv hp a (b - m * p) = toIocDiv hp a b - m := by
  simpa using toIocDiv_sub_zsmul hp a b m

@[simp]
/-
**toIocDiv_sub_natCast_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocDiv_sub_natCast_mul (a b : R) (m : Nat) : toIocDiv hp a (b - m * p) =
 toIocDiv hp a b - m
参数：a b : R；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIocDiv.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `toIocDiv_sub_intCast_mul`：toIocDiv_sub_intCast_mul (a b : R) (m : Int) :
 toIocDiv hp a (b - m * p) = toIocDiv hp a b - m
-/
theorem toIocDiv_sub_natCast_mul (a b : R) (m : ℕ) :
    toIocDiv hp a (b - m * p) = toIocDiv hp a b - m :=
  mod_cast toIocDiv_sub_intCast_mul hp a b m

@[simp]
/-
**toIocDiv_sub_ofNat_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocDiv_sub_ofNat_mul (a b : R) (m : Nat) [m.AtLeastTwo] : toIocDiv hp a 
(b - ofNat(m) * p) = toIocDiv hp a b - ofNat(m)
参数：a b : R；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `toIocDiv_sub_natCast_mul`：toIocDiv_sub_natCast_mul (a b : R) (m : Nat) :
 toIocDiv hp a (b - m * p) = toIocDiv hp a b - m
-/
theorem toIocDiv_sub_ofNat_mul (a b : R) (m : ℕ) [m.AtLeastTwo] :
    toIocDiv hp a (b - ofNat(m) * p) = toIocDiv hp a b - ofNat(m) :=
  toIocDiv_sub_natCast_mul hp a b m

@[simp]
/-
**toIocDiv_sub_intCast_mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocDiv_sub_intCast_mul' (a b : R) (m : Int) : toIocDiv hp (a - m * p) b 
= toIocDiv hp a b + m
参数：a b : R；m : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIocDiv.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `toIocDiv_sub_zsmul'`：toIocDiv_sub_zsmul' (a b : α) (m : Int) : toIocDiv 
hp (a - m • p) b = toIocDiv hp a b + m
-/
theorem toIocDiv_sub_intCast_mul' (a b : R) (m : ℤ) :
    toIocDiv hp (a - m * p) b = toIocDiv hp a b + m := by
  simpa using toIocDiv_sub_zsmul' hp a b m

@[simp]
/-
**toIocDiv_sub_natCast_mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocDiv_sub_natCast_mul' (a b : R) (m : Nat) : toIocDiv hp (a - m * p) b 
= toIocDiv hp a b + m
参数：a b : R；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIocDiv.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `toIocDiv_sub_intCast_mul'`：toIocDiv_sub_intCast_mul' (a b : R) (m : Int)
 : toIocDiv hp (a - m * p) b = toIocDiv hp a b + m
-/
theorem toIocDiv_sub_natCast_mul' (a b : R) (m : ℕ) :
    toIocDiv hp (a - m * p) b = toIocDiv hp a b + m :=
  mod_cast toIocDiv_sub_intCast_mul' hp a b m

@[simp]
/-
**toIocDiv_sub_ofNat_mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocDiv_sub_ofNat_mul' (a b : R) (m : Nat) [m.AtLeastTwo] : toIocDiv hp (
a - ofNat(m) * p) b = toIocDiv hp a b + ofNat(m)
参数：a b : R；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `toIocDiv_sub_natCast_mul'`：toIocDiv_sub_natCast_mul' (a b : R) (m : Nat)
 : toIocDiv hp (a - m * p) b = toIocDiv hp a b + m
-/
theorem toIocDiv_sub_ofNat_mul' (a b : R) (m : ℕ) [m.AtLeastTwo] :
    toIocDiv hp (a - ofNat(m) * p) b = toIocDiv hp a b + ofNat(m) :=
  toIocDiv_sub_natCast_mul' hp a b m

@[simp]
/-
**toIcoMod_add_intCast_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoMod_add_intCast_mul (a b : R) (m : Int) : toIcoMod hp a (b + m * p) =
 toIcoMod hp a b
参数：a b : R；m : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIcoMod.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `toIcoMod_add_zsmul`：toIcoMod_add_zsmul (a b : α) (m : Int) : toIcoMod hp
 a (b + m • p) = toIcoMod hp a b
-/
theorem toIcoMod_add_intCast_mul (a b : R) (m : ℤ) :
    toIcoMod hp a (b + m * p) = toIcoMod hp a b := by
  simpa using toIcoMod_add_zsmul hp a b m

@[simp]
/-
**toIcoMod_add_natCast_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoMod_add_natCast_mul (a b : R) (m : Nat) : toIcoMod hp a (b + m * p) =
 toIcoMod hp a b
参数：a b : R；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIcoMod.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `toIcoMod_add_intCast_mul`：toIcoMod_add_intCast_mul (a b : R) (m : Int) :
 toIcoMod hp a (b + m * p) = toIcoMod hp a b
-/
theorem toIcoMod_add_natCast_mul (a b : R) (m : ℕ) :
    toIcoMod hp a (b + m * p) = toIcoMod hp a b :=
  mod_cast toIcoMod_add_intCast_mul hp a b m

@[simp]
/-
**toIcoMod_add_ofNat_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoMod_add_ofNat_mul (a b : R) (m : Nat) [m.AtLeastTwo] : toIcoMod hp a 
(b + ofNat(m) * p) = toIcoMod hp a b
参数：a b : R；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIcoMod.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `toIcoMod_add_intCast_mul`：toIcoMod_add_intCast_mul (a b : R) (m : Int) :
 toIcoMod hp a (b + m * p) = toIcoMod hp a b
-/
theorem toIcoMod_add_ofNat_mul (a b : R) (m : ℕ) [m.AtLeastTwo] :
    toIcoMod hp a (b + ofNat(m) * p) = toIcoMod hp a b :=
  mod_cast toIcoMod_add_intCast_mul hp a b m

@[simp]
/-
**toIcoMod_add_intCast_mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoMod_add_intCast_mul' (a b : R) (m : Int) : toIcoMod hp (a + m * p) b 
= toIcoMod hp a b + m * p
参数：a b : R；m : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIcoMod.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `toIcoMod_add_zsmul'`：toIcoMod_add_zsmul' (a b : α) (m : Int) : toIcoMod 
hp (a + m • p) b = toIcoMod hp a b + m • p
-/
theorem toIcoMod_add_intCast_mul' (a b : R) (m : ℤ) :
    toIcoMod hp (a + m * p) b = toIcoMod hp a b + m * p := by
  simpa using toIcoMod_add_zsmul' hp a b m

@[simp]
/-
**toIcoMod_add_natCast_mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoMod_add_natCast_mul' (a b : R) (m : Nat) : toIcoMod hp (a + m * p) b 
= toIcoMod hp a b + m * p
参数：a b : R；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIcoMod.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `toIcoMod_add_intCast_mul'`：toIcoMod_add_intCast_mul' (a b : R) (m : Int)
 : toIcoMod hp (a + m * p) b = toIcoMod hp a b + m * p
-/
theorem toIcoMod_add_natCast_mul' (a b : R) (m : ℕ) :
    toIcoMod hp (a + m * p) b = toIcoMod hp a b + m * p :=
  mod_cast toIcoMod_add_intCast_mul' hp a b m

@[simp]
/-
**toIcoMod_add_ofNat_mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoMod_add_ofNat_mul' (a b : R) (m : Nat) [m.AtLeastTwo] : toIcoMod hp (
a + ofNat(m) * p) b = toIcoMod hp a b + ofNat(m) * p
参数：a b : R；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `toIcoMod_add_natCast_mul'`：toIcoMod_add_natCast_mul' (a b : R) (m : Nat)
 : toIcoMod hp (a + m * p) b = toIcoMod hp a b + m * p
-/
theorem toIcoMod_add_ofNat_mul' (a b : R) (m : ℕ) [m.AtLeastTwo] :
    toIcoMod hp (a + ofNat(m) * p) b = toIcoMod hp a b + ofNat(m) * p :=
  toIcoMod_add_natCast_mul' hp a b m

@[simp]
/-
**toIocMod_add_intCast_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocMod_add_intCast_mul (a b : R) (m : Int) : toIocMod hp a (b + m * p) =
 toIocMod hp a b
参数：a b : R；m : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIocMod.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `toIocMod_add_zsmul`：toIocMod_add_zsmul (a b : α) (m : Int) : toIocMod hp
 a (b + m • p) = toIocMod hp a b
-/
theorem toIocMod_add_intCast_mul (a b : R) (m : ℤ) :
    toIocMod hp a (b + m * p) = toIocMod hp a b := by
  simpa using toIocMod_add_zsmul hp a b m

@[simp]
/-
**toIocMod_add_natCast_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocMod_add_natCast_mul (a b : R) (m : Nat) : toIocMod hp a (b + m * p) =
 toIocMod hp a b
参数：a b : R；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIocMod.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `toIocMod_add_intCast_mul`：toIocMod_add_intCast_mul (a b : R) (m : Int) :
 toIocMod hp a (b + m * p) = toIocMod hp a b
-/
theorem toIocMod_add_natCast_mul (a b : R) (m : ℕ) :
    toIocMod hp a (b + m * p) = toIocMod hp a b :=
  mod_cast toIocMod_add_intCast_mul hp a b m

@[simp]
/-
**toIocMod_add_ofNat_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocMod_add_ofNat_mul (a b : R) (m : Nat) [m.AtLeastTwo] : toIocMod hp a 
(b + ofNat(m) * p) = toIocMod hp a b
参数：a b : R；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `toIocMod_add_natCast_mul`：toIocMod_add_natCast_mul (a b : R) (m : Nat) :
 toIocMod hp a (b + m * p) = toIocMod hp a b
-/
theorem toIocMod_add_ofNat_mul (a b : R) (m : ℕ) [m.AtLeastTwo] :
    toIocMod hp a (b + ofNat(m) * p) = toIocMod hp a b :=
  toIocMod_add_natCast_mul hp a b m

@[simp]
/-
**toIocMod_add_intCast_mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocMod_add_intCast_mul' (a b : R) (m : Int) : toIocMod hp (a + m * p) b 
= toIocMod hp a b + m * p
参数：a b : R；m : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIocMod.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `toIocMod_add_zsmul'`：toIocMod_add_zsmul' (a b : α) (m : Int) : toIocMod 
hp (a + m • p) b = toIocMod hp a b + m • p
-/
theorem toIocMod_add_intCast_mul' (a b : R) (m : ℤ) :
    toIocMod hp (a + m * p) b = toIocMod hp a b + m * p := by
  simpa using toIocMod_add_zsmul' hp a b m

@[simp]
/-
**toIocMod_add_natCast_mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocMod_add_natCast_mul' (a b : R) (m : Nat) : toIocMod hp (a + m * p) b 
= toIocMod hp a b + m * p
参数：a b : R；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIocMod.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `toIocMod_add_intCast_mul'`：toIocMod_add_intCast_mul' (a b : R) (m : Int)
 : toIocMod hp (a + m * p) b = toIocMod hp a b + m * p
-/
theorem toIocMod_add_natCast_mul' (a b : R) (m : ℕ) :
    toIocMod hp (a + m * p) b = toIocMod hp a b + m * p :=
  mod_cast toIocMod_add_intCast_mul' hp a b m

@[simp]
/-
**toIocMod_add_ofNat_mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocMod_add_ofNat_mul' (a b : R) (m : Nat) [m.AtLeastTwo] : toIocMod hp (
a + ofNat(m) * p) b = toIocMod hp a b + ofNat(m) * p
参数：a b : R；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `toIocMod_add_natCast_mul'`：toIocMod_add_natCast_mul' (a b : R) (m : Nat)
 : toIocMod hp (a + m * p) b = toIocMod hp a b + m * p
-/
theorem toIocMod_add_ofNat_mul' (a b : R) (m : ℕ) [m.AtLeastTwo] :
    toIocMod hp (a + ofNat(m) * p) b = toIocMod hp a b + ofNat(m) * p :=
  toIocMod_add_natCast_mul' hp a b m

@[simp]
/-
**toIcoMod_intCast_mul_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoMod_intCast_mul_add (a b : R) (m : Int) : toIcoMod hp a (m * p + b) =
 toIcoMod hp a b
参数：a b : R；m : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIcoMod.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `toIcoMod_zsmul_add`：toIcoMod_zsmul_add (a b : α) (m : Int) : toIcoMod hp
 a (m • p + b) = toIcoMod hp a b
-/
theorem toIcoMod_intCast_mul_add (a b : R) (m : ℤ) :
    toIcoMod hp a (m * p + b) = toIcoMod hp a b := by
  simpa using toIcoMod_zsmul_add hp a b m

@[simp]
/-
**toIcoMod_natCast_mul_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoMod_natCast_mul_add (a b : R) (m : Nat) : toIcoMod hp a (m * p + b) =
 toIcoMod hp a b
参数：a b : R；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIcoMod.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `toIcoMod_intCast_mul_add`：toIcoMod_intCast_mul_add (a b : R) (m : Int) :
 toIcoMod hp a (m * p + b) = toIcoMod hp a b
-/
theorem toIcoMod_natCast_mul_add (a b : R) (m : ℕ) :
    toIcoMod hp a (m * p + b) = toIcoMod hp a b :=
  mod_cast toIcoMod_intCast_mul_add hp a b m

@[simp]
/-
**toIcoMod_ofNat_mul_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoMod_ofNat_mul_add (a b : R) (m : Nat) [m.AtLeastTwo] : toIcoMod hp a 
(ofNat(m) * p + b) = toIcoMod hp a b
参数：a b : R；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `toIcoMod_natCast_mul_add`：toIcoMod_natCast_mul_add (a b : R) (m : Nat) :
 toIcoMod hp a (m * p + b) = toIcoMod hp a b
-/
theorem toIcoMod_ofNat_mul_add (a b : R) (m : ℕ) [m.AtLeastTwo] :
    toIcoMod hp a (ofNat(m) * p + b) = toIcoMod hp a b :=
  toIcoMod_natCast_mul_add hp a b m

@[simp]
/-
**toIcoMod_intCast_mul_add'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoMod_intCast_mul_add' (a b : R) (m : Int) : toIcoMod hp (m * p + a) b 
= m * p + toIcoMod hp a b
参数：a b : R；m : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `toIcoMod_add_intCast_mul'`：toIcoMod_add_intCast_mul' (a b : R) (m : Int)
 : toIcoMod hp (a + m * p) b = toIcoMod hp a b + m * p
-/
theorem toIcoMod_intCast_mul_add' (a b : R) (m : ℤ) :
    toIcoMod hp (m * p + a) b = m * p + toIcoMod hp a b := by
  rw [add_comm, toIcoMod_add_intCast_mul', add_comm]

@[simp]
/-
**toIcoMod_natCast_mul_add'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoMod_natCast_mul_add' (a b : R) (m : Nat) : toIcoMod hp (m * p + a) b 
= m * p + toIcoMod hp a b
参数：a b : R；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIcoMod.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `toIcoMod_intCast_mul_add'`：toIcoMod_intCast_mul_add' (a b : R) (m : Int)
 : toIcoMod hp (m * p + a) b = m * p + toIcoMod hp a b
-/
theorem toIcoMod_natCast_mul_add' (a b : R) (m : ℕ) :
    toIcoMod hp (m * p + a) b = m * p + toIcoMod hp a b :=
  mod_cast toIcoMod_intCast_mul_add' hp a b m

@[simp]
/-
**toIcoMod_ofNat_mul_add'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoMod_ofNat_mul_add' (a b : R) (m : Nat) [m.AtLeastTwo] : toIcoMod hp (
ofNat(m) * p + a) b = ofNat(m) * p + toIcoMod hp a b
参数：a b : R；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `toIcoMod_natCast_mul_add'`：toIcoMod_natCast_mul_add' (a b : R) (m : Nat)
 : toIcoMod hp (m * p + a) b = m * p + toIcoMod hp a b
-/
theorem toIcoMod_ofNat_mul_add' (a b : R) (m : ℕ) [m.AtLeastTwo] :
    toIcoMod hp (ofNat(m) * p + a) b = ofNat(m) * p + toIcoMod hp a b :=
  toIcoMod_natCast_mul_add' hp a b m

@[simp]
/-
**toIocMod_intCast_mul_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocMod_intCast_mul_add (a b : R) (m : Int) : toIocMod hp a (m * p + b) =
 toIocMod hp a b
参数：a b : R；m : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `toIocMod_add_intCast_mul`：toIocMod_add_intCast_mul (a b : R) (m : Int) :
 toIocMod hp a (b + m * p) = toIocMod hp a b
-/
theorem toIocMod_intCast_mul_add (a b : R) (m : ℤ) :
    toIocMod hp a (m * p + b) = toIocMod hp a b := by
  rw [add_comm, toIocMod_add_intCast_mul]

@[simp]
/-
**toIocMod_natCast_mul_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocMod_natCast_mul_add (a b : R) (m : Nat) : toIocMod hp a (m * p + b) =
 toIocMod hp a b
参数：a b : R；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIocMod.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `toIocMod_intCast_mul_add`：toIocMod_intCast_mul_add (a b : R) (m : Int) :
 toIocMod hp a (m * p + b) = toIocMod hp a b
-/
theorem toIocMod_natCast_mul_add (a b : R) (m : ℕ) :
    toIocMod hp a (m * p + b) = toIocMod hp a b :=
  mod_cast toIocMod_intCast_mul_add hp a b m

@[simp]
/-
**toIocMod_ofNat_mul_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocMod_ofNat_mul_add (a b : R) (m : Nat) [m.AtLeastTwo] : toIocMod hp a 
(ofNat(m) * p + b) = toIocMod hp a b
参数：a b : R；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `toIocMod_natCast_mul_add`：toIocMod_natCast_mul_add (a b : R) (m : Nat) :
 toIocMod hp a (m * p + b) = toIocMod hp a b
-/
theorem toIocMod_ofNat_mul_add (a b : R) (m : ℕ) [m.AtLeastTwo] :
    toIocMod hp a (ofNat(m) * p + b) = toIocMod hp a b :=
  toIocMod_natCast_mul_add hp a b m

@[simp]
/-
**toIocMod_intCast_mul_add'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocMod_intCast_mul_add' (a b : R) (m : Int) : toIocMod hp (m * p + a) b 
= m * p + toIocMod hp a b
参数：a b : R；m : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `toIocMod_add_intCast_mul'`：toIocMod_add_intCast_mul' (a b : R) (m : Int)
 : toIocMod hp (a + m * p) b = toIocMod hp a b + m * p
-/
theorem toIocMod_intCast_mul_add' (a b : R) (m : ℤ) :
    toIocMod hp (m * p + a) b = m * p + toIocMod hp a b := by
  rw [add_comm, toIocMod_add_intCast_mul', add_comm]

@[simp]
/-
**toIocMod_natCast_mul_add'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocMod_natCast_mul_add' (a b : R) (m : Nat) : toIocMod hp (m * p + a) b 
= m * p + toIocMod hp a b
参数：a b : R；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIocMod.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `toIocMod_intCast_mul_add'`：toIocMod_intCast_mul_add' (a b : R) (m : Int)
 : toIocMod hp (m * p + a) b = m * p + toIocMod hp a b
-/
theorem toIocMod_natCast_mul_add' (a b : R) (m : ℕ) :
    toIocMod hp (m * p + a) b = m * p + toIocMod hp a b :=
  mod_cast toIocMod_intCast_mul_add' hp a b m

@[simp]
/-
**toIocMod_ofNat_mul_add'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocMod_ofNat_mul_add' (a b : R) (m : Nat) [m.AtLeastTwo] : toIocMod hp (
ofNat(m) * p + a) b = ofNat(m) * p + toIocMod hp a b
参数：a b : R；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `toIocMod_natCast_mul_add'`：toIocMod_natCast_mul_add' (a b : R) (m : Nat)
 : toIocMod hp (m * p + a) b = m * p + toIocMod hp a b
-/
theorem toIocMod_ofNat_mul_add' (a b : R) (m : ℕ) [m.AtLeastTwo] :
    toIocMod hp (ofNat(m) * p + a) b = ofNat(m) * p + toIocMod hp a b :=
  toIocMod_natCast_mul_add' hp a b m

@[simp]
/-
**toIcoMod_sub_intCast_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoMod_sub_intCast_mul (a b : R) (m : Int) : toIcoMod hp a (b - m * p) =
 toIcoMod hp a b
参数：a b : R；m : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIcoMod.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `toIcoMod_sub_zsmul`：toIcoMod_sub_zsmul (a b : α) (m : Int) : toIcoMod hp
 a (b - m • p) = toIcoMod hp a b
-/
theorem toIcoMod_sub_intCast_mul (a b : R) (m : ℤ) :
    toIcoMod hp a (b - m * p) = toIcoMod hp a b := by
  simpa using toIcoMod_sub_zsmul hp a b m

@[simp]
/-
**toIcoMod_sub_natCast_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoMod_sub_natCast_mul (a b : R) (m : Nat) : toIcoMod hp a (b - m * p) =
 toIcoMod hp a b
参数：a b : R；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIcoMod.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `toIcoMod_sub_intCast_mul`：toIcoMod_sub_intCast_mul (a b : R) (m : Int) :
 toIcoMod hp a (b - m * p) = toIcoMod hp a b
-/
theorem toIcoMod_sub_natCast_mul (a b : R) (m : ℕ) :
    toIcoMod hp a (b - m * p) = toIcoMod hp a b :=
  mod_cast toIcoMod_sub_intCast_mul hp a b m

@[simp]
/-
**toIcoMod_sub_ofNat_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoMod_sub_ofNat_mul (a b : R) (m : Nat) [m.AtLeastTwo] : toIcoMod hp a 
(b - ofNat(m) * p) = toIcoMod hp a b
参数：a b : R；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `toIcoMod_sub_natCast_mul`：toIcoMod_sub_natCast_mul (a b : R) (m : Nat) :
 toIcoMod hp a (b - m * p) = toIcoMod hp a b
-/
theorem toIcoMod_sub_ofNat_mul (a b : R) (m : ℕ) [m.AtLeastTwo] :
    toIcoMod hp a (b - ofNat(m) * p) = toIcoMod hp a b :=
  toIcoMod_sub_natCast_mul hp a b m

@[simp]
/-
**toIcoMod_sub_intCast_mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoMod_sub_intCast_mul' (a b : R) (m : Int) : toIcoMod hp (a - m * p) b 
= toIcoMod hp a b - m * p
参数：a b : R；m : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIcoMod.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `toIcoMod_sub_zsmul'`：toIcoMod_sub_zsmul' (a b : α) (m : Int) : toIcoMod 
hp (a - m • p) b = toIcoMod hp a b - m • p
-/
theorem toIcoMod_sub_intCast_mul' (a b : R) (m : ℤ) :
    toIcoMod hp (a - m * p) b = toIcoMod hp a b - m * p := by
  simpa using toIcoMod_sub_zsmul' hp a b m

@[simp]
/-
**toIcoMod_sub_natCast_mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoMod_sub_natCast_mul' (a b : R) (m : Nat) : toIcoMod hp (a - m * p) b 
= toIcoMod hp a b - m * p
参数：a b : R；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIcoMod.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `toIcoMod_sub_intCast_mul'`：toIcoMod_sub_intCast_mul' (a b : R) (m : Int)
 : toIcoMod hp (a - m * p) b = toIcoMod hp a b - m * p
-/
theorem toIcoMod_sub_natCast_mul' (a b : R) (m : ℕ) :
    toIcoMod hp (a - m * p) b = toIcoMod hp a b - m * p :=
  mod_cast toIcoMod_sub_intCast_mul' hp a b m

@[simp]
/-
**toIcoMod_sub_ofNat_mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoMod_sub_ofNat_mul' (a b : R) (m : Nat) [m.AtLeastTwo] : toIcoMod hp (
a - ofNat(m) * p) b = toIcoMod hp a b - ofNat(m) * p
参数：a b : R；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `toIcoMod_sub_natCast_mul'`：toIcoMod_sub_natCast_mul' (a b : R) (m : Nat)
 : toIcoMod hp (a - m * p) b = toIcoMod hp a b - m * p
-/
theorem toIcoMod_sub_ofNat_mul' (a b : R) (m : ℕ) [m.AtLeastTwo] :
    toIcoMod hp (a - ofNat(m) * p) b = toIcoMod hp a b - ofNat(m) * p :=
  toIcoMod_sub_natCast_mul' hp a b m

@[simp]
/-
**toIocMod_sub_intCast_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocMod_sub_intCast_mul (a b : R) (m : Int) : toIocMod hp a (b - m * p) =
 toIocMod hp a b
参数：a b : R；m : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIocMod.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `toIocMod_sub_zsmul`：toIocMod_sub_zsmul (a b : α) (m : Int) : toIocMod hp
 a (b - m • p) = toIocMod hp a b
-/
theorem toIocMod_sub_intCast_mul (a b : R) (m : ℤ) :
    toIocMod hp a (b - m * p) = toIocMod hp a b := by
  simpa using toIocMod_sub_zsmul hp a b m

@[simp]
/-
**toIocMod_sub_natCast_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocMod_sub_natCast_mul (a b : R) (m : Nat) : toIocMod hp a (b - m * p) =
 toIocMod hp a b
参数：a b : R；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIocMod.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `toIocMod_sub_intCast_mul`：toIocMod_sub_intCast_mul (a b : R) (m : Int) :
 toIocMod hp a (b - m * p) = toIocMod hp a b
-/
theorem toIocMod_sub_natCast_mul (a b : R) (m : ℕ) :
    toIocMod hp a (b - m * p) = toIocMod hp a b :=
  mod_cast toIocMod_sub_intCast_mul hp a b m

@[simp]
/-
**toIocMod_sub_ofNat_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocMod_sub_ofNat_mul (a b : R) (m : Nat) [m.AtLeastTwo] : toIocMod hp a 
(b - ofNat(m) * p) = toIocMod hp a b
参数：a b : R；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `toIocMod_sub_natCast_mul`：toIocMod_sub_natCast_mul (a b : R) (m : Nat) :
 toIocMod hp a (b - m * p) = toIocMod hp a b
-/
theorem toIocMod_sub_ofNat_mul (a b : R) (m : ℕ) [m.AtLeastTwo] :
    toIocMod hp a (b - ofNat(m) * p) = toIocMod hp a b :=
  toIocMod_sub_natCast_mul hp a b m

@[simp]
/-
**toIocMod_sub_intCast_mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocMod_sub_intCast_mul' (a b : R) (m : Int) : toIocMod hp (a - m * p) b 
= toIocMod hp a b - m * p
参数：a b : R；m : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIocMod.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `toIocMod_sub_zsmul'`：toIocMod_sub_zsmul' (a b : α) (m : Int) : toIocMod 
hp (a - m • p) b = toIocMod hp a b - m • p
-/
theorem toIocMod_sub_intCast_mul' (a b : R) (m : ℤ) :
    toIocMod hp (a - m * p) b = toIocMod hp a b - m * p := by
  simpa using toIocMod_sub_zsmul' hp a b m

@[simp]
/-
**toIocMod_sub_natCast_mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocMod_sub_natCast_mul' (a b : R) (m : Nat) : toIocMod hp (a - m * p) b 
= toIocMod hp a b - m * p
参数：a b : R；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIocMod.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `toIocMod_sub_intCast_mul'`：toIocMod_sub_intCast_mul' (a b : R) (m : Int)
 : toIocMod hp (a - m * p) b = toIocMod hp a b - m * p
-/
theorem toIocMod_sub_natCast_mul' (a b : R) (m : ℕ) :
    toIocMod hp (a - m * p) b = toIocMod hp a b - m * p :=
  mod_cast toIocMod_sub_intCast_mul' hp a b m

@[simp]
/-
**toIocMod_sub_ofNat_mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocMod_sub_ofNat_mul' (a b : R) (m : Nat) [m.AtLeastTwo] : toIocMod hp (
a - ofNat(m) * p) b = toIocMod hp a b - ofNat(m) * p
参数：a b : R；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `toIocMod_sub_natCast_mul'`：toIocMod_sub_natCast_mul' (a b : R) (m : Nat)
 : toIocMod hp (a - m * p) b = toIocMod hp a b - m * p
-/
theorem toIocMod_sub_ofNat_mul' (a b : R) (m : ℕ) [m.AtLeastTwo] :
    toIocMod hp (a - ofNat(m) * p) b = toIocMod hp a b - ofNat(m) * p :=
  toIocMod_sub_natCast_mul' hp a b m

end Ring

/-!
### Connections to `Int.floor` and `Int.fract`
-/


section LinearOrderedField

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]
  {p : α} (hp : 0 < p)

/-
**toIcoDiv_eq_floor** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoDiv_eq_floor (a b : α) : toIcoDiv hp a b = ⌊(b - a) / p⌋
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `toIcoDiv_eq_of_sub_zsmul_mem_Ico`：∀ {α : Type u_1} [inst : AddCommGroup 
α] [inst_1 : LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]
   {p : α} (hp : 0 < p…
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `FloorRing.archimedean`：∀ (K : Type u_5) [inst : Field K] [inst_1 : Linea
rOrder K] [IsStrictOrderedRing K] [FloorRing K], Archimedean K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_Ico`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.I
co a b ↔ a ≤ x ∧ x < b
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `sub_right_comm`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c
 : α), a - b - c = a - c - b
· 使用定理 `sub_lt_iff_lt_add`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [A
ddRightStrictMono α] {a b c : α}, a - c < b ↔ a < b + c
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Int.sub_floor_div_mul_nonneg`：sub_floor_div_mul_nonneg (a : k) (hb : 0 <
 b) : 0 <= a - ⌊a / b⌋ * b
· 使用定理 `Int.sub_floor_div_mul_lt`：sub_floor_div_mul_lt (a : k) (hb : 0 < b) : a 
- ⌊a / b⌋ * b < b
-/
theorem toIcoDiv_eq_floor (a b : α) : toIcoDiv hp a b = ⌊(b - a) / p⌋ := by
  refine toIcoDiv_eq_of_sub_zsmul_mem_Ico hp ?_
  rw [Set.mem_Ico, zsmul_eq_mul, ← sub_nonneg, add_comm, sub_right_comm, ← sub_lt_iff_lt_add,
    sub_right_comm _ _ a]
  exact ⟨Int.sub_floor_div_mul_nonneg _ hp, Int.sub_floor_div_mul_lt _ hp⟩
/-
**toIocDiv_eq_neg_floor** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocDiv_eq_neg_floor (a b : α) : toIocDiv hp a b = -⌊(a + p - b) / p⌋
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `toIocDiv_eq_of_sub_zsmul_mem_Ioc`：∀ {α : Type u_1} [inst : AddCommGroup 
α] [inst_1 : LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]
   {p : α} (hp : 0 < p…
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `FloorRing.archimedean`：∀ (K : Type u_5) [inst : Field K] [inst_1 : Linea
rOrder K] [IsStrictOrderedRing K] [FloorRing K], Archimedean K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_Ioc`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.I
oc a b ↔ a < x ∧ x ≤ b
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `sub_add_eq_sub_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a
 b c : α), a - (b + c) = a - b - c
· 使用定理 `add_lt_add_iff_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [A
ddRightStrictMono α] [AddRightReflectLT α] (a : α) {b c : α},   b + a < c + a ↔ 
b < c
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `sub_lt_iff_lt_add`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [A
ddRightStrictMono α] {a b c : α}, a - c < b ↔ a < b + c
· 使用定理 `Int.sub_floor_div_mul_lt`：sub_floor_div_mul_lt (a : k) (hb : 0 < b) : a 
- ⌊a / b⌋ * b < b
· 使用定理 `Int.sub_floor_div_mul_nonneg`：sub_floor_div_mul_nonneg (a : k) (hb : 0 <
 b) : 0 <= a - ⌊a / b⌋ * b
-/
theorem toIocDiv_eq_neg_floor (a b : α) : toIocDiv hp a b = -⌊(a + p - b) / p⌋ := by
  refine toIocDiv_eq_of_sub_zsmul_mem_Ioc hp ?_
  rw [Set.mem_Ioc, zsmul_eq_mul, Int.cast_neg, neg_mul, sub_neg_eq_add, ← sub_nonneg,
    sub_add_eq_sub_sub]
  refine ⟨?_, Int.sub_floor_div_mul_nonneg _ hp⟩
  rw [← add_lt_add_iff_right p, add_assoc, add_comm b, ← sub_lt_iff_lt_add, add_comm (_ * _), ←
    sub_lt_iff_lt_add]
  exact Int.sub_floor_div_mul_lt _ hp
/-
**toIcoDiv_zero_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoDiv_zero_one (b : α) : toIcoDiv (zero_lt_one' α) 0 b = ⌊b⌋
参数：b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `FloorRing.archimedean`：∀ (K : Type u_5) [inst : Field K] [inst_1 : Linea
rOrder K] [IsStrictOrderedRing K] [FloorRing K], Archimedean K
· 使用引理 `zero_lt_one'`：zero_lt_one' : (0 : α) < 1
· 使用定理 `FloorSemiring.instZeroLEOneClass`：∀ {α : Type u_2} [inst : Semiring α] [
inst_1 : PartialOrder α] [FloorSemiring α], ZeroLEOneClass α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIcoDiv_eq_floor`：toIcoDiv_eq_floor (a b : α) : toIcoDiv hp a b = ⌊(b -
 a) / p⌋
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toIcoDiv_zero_one (b : α) : toIcoDiv (zero_lt_one' α) 0 b = ⌊b⌋ := by
  simp [toIcoDiv_eq_floor]
/-
**toIcoMod_eq_add_fract_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoMod_eq_add_fract_mul (a b : α) : toIcoMod hp a b = a + Int.fract ((b 
- a) / p) * p
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `FloorRing.archimedean`：∀ (K : Type u_5) [inst : Field K] [inst_1 : Linea
rOrder K] [IsStrictOrderedRing K] [FloorRing K], Archimedean K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIcoMod.eq_1`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : Linear
Order α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p : α} (hp : 0 
< p…
· 使用定理 `toIcoDiv_eq_floor`：toIcoDiv_eq_floor (a b : α) : toIcoDiv hp a b = ⌊(b -
 a) / p⌋
· 使用定理 `Int.fract.eq_1`：∀ {α : Type u_2} [inst : Ring α] [inst_1 : LinearOrder α
] [inst_2 : FloorRing α] (a : α), Int.fract a = a - ↑⌊a⌋
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `Mathlib.Tactic.FieldSimp.subst_sub`：subst_sub {M : Type*} [Ring M] {x₁ x
₂ X₁ X₂ Y y a : M} (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ - X₂ = Y) 
(hy : a * Y = y) : x₁ - …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons`：eval_mul_eval_cons [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : L.eval * ((n, e) ::ᵣ l).eval = …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_div_of_eq_one_of_subst`：eq_div_of_eq_one_of_
subst {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1) (hn : l_n 
= n) : l = n
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_eq_div_of_eq_div`：cons_eq_div_of_eq_div
 [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M} (h : t.eval = t_n.ev
al / t_d.eval) : ((n, e) ::ᵣ t).eval = …
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons`：∀ {M : Type u_1} [inst : CommGrou
pWithZero M] (p : ℤ × M) (l : Mathlib.Tactic.FieldSimp.NF M),   (p ::ᵣ l).eval =
 l.eval * Mathlib.Tactic.Fi…
· 使用定理 `Mathlib.Tactic.FieldSimp.zpow'_one`：∀ {α : Type u_1} [inst : GroupWithZe
ro α] (a : α), Mathlib.Tactic.FieldSimp.zpow' a 1 = a
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₃`：mul_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval * l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.subst_add`：subst_add {M : Type*} [Semiring M] {
x₁ x₂ X₁ X₂ Y y a : M} (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ + X₂ =
 Y) (hy : a * Y = y) : x…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval`：div_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al / l₂.eval = l.eval) : x₁ /…
（共 72 条，此处仅展示前 30 条）
-/
theorem toIcoMod_eq_add_fract_mul (a b : α) :
    toIcoMod hp a b = a + Int.fract ((b - a) / p) * p := by
  rw [toIcoMod, toIcoDiv_eq_floor, Int.fract]
  simp [field, -Int.self_sub_floor]
  ring
/-
**toIcoMod_eq_fract_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoMod_eq_fract_mul (b : α) : toIcoMod hp 0 b = Int.fract (b / p) * p
参数：b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `FloorRing.archimedean`：∀ (K : Type u_5) [inst : Field K] [inst_1 : Linea
rOrder K] [IsStrictOrderedRing K] [FloorRing K], Archimedean K
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIcoMod_eq_add_fract_mul`：toIcoMod_eq_add_fract_mul (a b : α) : toIcoMo
d hp a b = a + Int.fract ((b - a) / p) * p
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toIcoMod_eq_fract_mul (b : α) : toIcoMod hp 0 b = Int.fract (b / p) * p := by
  simp [toIcoMod_eq_add_fract_mul]
/-
**toIocMod_eq_sub_fract_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIocMod_eq_sub_fract_mul (a b : α) : toIocMod hp a b = a + p - Int.fract 
((a + p - b) / p) * p
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `FloorRing.archimedean`：∀ (K : Type u_5) [inst : Field K] [inst_1 : Linea
rOrder K] [IsStrictOrderedRing K] [FloorRing K], Archimedean K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIocMod.eq_1`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : Linear
Order α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p : α} (hp : 0 
< p…
· 使用定理 `toIocDiv_eq_neg_floor`：toIocDiv_eq_neg_floor (a b : α) : toIocDiv hp a b
 = -⌊(a + p - b) / p⌋
· 使用定理 `Int.fract.eq_1`：∀ {α : Type u_2} [inst : Ring α] [inst_1 : LinearOrder α
] [inst_2 : FloorRing α] (a : α), Int.fract a = a - ↑⌊a⌋
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `Mathlib.Tactic.FieldSimp.subst_add`：subst_add {M : Type*} [Semiring M] {
x₁ x₂ X₁ X₂ Y y a : M} (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ + X₂ =
 Y) (hy : a * Y = y) : x…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons`：eval_mul_eval_cons [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : L.eval * ((n, e) ::ᵣ l).eval = …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_div_of_eq_one_of_subst`：eq_div_of_eq_one_of_
subst {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1) (hn : l_n 
= n) : l = n
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_eq_div_of_eq_div`：cons_eq_div_of_eq_div
 [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M} (h : t.eval = t_n.ev
al / t_d.eval) : ((n, e) ::ᵣ t).eval = …
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons`：∀ {M : Type u_1} [inst : CommGrou
pWithZero M] (p : ℤ × M) (l : Mathlib.Tactic.FieldSimp.NF M),   (p ::ᵣ l).eval =
 l.eval * Mathlib.Tactic.Fi…
· 使用定理 `Mathlib.Tactic.FieldSimp.zpow'_one`：∀ {α : Type u_1} [inst : GroupWithZe
ro α] (a : α), Mathlib.Tactic.FieldSimp.zpow' a 1 = a
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₃`：mul_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval * l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
（共 74 条，此处仅展示前 30 条）
-/
theorem toIocMod_eq_sub_fract_mul (a b : α) :
    toIocMod hp a b = a + p - Int.fract ((a + p - b) / p) * p := by
  rw [toIocMod, toIocDiv_eq_neg_floor, Int.fract]
  simp [field, -Int.self_sub_floor]
  ring
/-
**toIcoMod_zero_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoMod_zero_one (b : α) : toIcoMod (zero_lt_one' α) 0 b = Int.fract b
参数：b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `FloorRing.archimedean`：∀ (K : Type u_5) [inst : Field K] [inst_1 : Linea
rOrder K] [IsStrictOrderedRing K] [FloorRing K], Archimedean K
· 使用引理 `zero_lt_one'`：zero_lt_one' : (0 : α) < 1
· 使用定理 `FloorSemiring.instZeroLEOneClass`：∀ {α : Type u_2} [inst : Semiring α] [
inst_1 : PartialOrder α] [FloorSemiring α], ZeroLEOneClass α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIcoMod_eq_add_fract_mul`：toIcoMod_eq_add_fract_mul (a b : α) : toIcoMo
d hp a b = a + Int.fract ((b - a) / p) * p
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toIcoMod_zero_one (b : α) : toIcoMod (zero_lt_one' α) 0 b = Int.fract b := by
  simp [toIcoMod_eq_add_fract_mul]

end LinearOrderedField

/-! ### Lemmas about unions of translates of intervals -/


section Union

open Set Int

section LinearOrderedAddCommGroup

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [Archimedean α]
  {p : α} (hp : 0 < p) (a : α)
include hp

/-
**iUnion_Ioc_add_zsmul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iUnion_Ioc_add_zsmul : ⋃ n : Int, Ioc (a + n • p) (a + (n + 1) • p) = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.eq_univ_iff_forall`：eq_univ_iff_forall {s : Set α} : s = univ ↔ fora
ll x, x in s
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `sub_toIocDiv_zsmul_mem_Ioc`：sub_toIocDiv_zsmul_mem_Ioc (a b : α) : b - t
oIocDiv hp a b • p in Set.Ioc a (a + p)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `lt_sub_iff_add_lt`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [A
ddRightStrictMono α] {a b c : α}, a < c - b ↔ a + b < c
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `_private.Mathlib.Algebra.Order.ToIntervalMod.0.iUnion_Ioc_add_zsmul._abe
l_1_1`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : LinearOrder α] [inst_2
 : IsOrderedAddMonoid α]   [inst_3 : Archimedean α] {p : α} (hp : 0…
· 使用定理 `sub_le_iff_le_add`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [A
ddRightMono α] {a b c : α}, a - c ≤ b ↔ a ≤ b + c
-/
theorem iUnion_Ioc_add_zsmul : ⋃ n : ℤ, Ioc (a + n • p) (a + (n + 1) • p) = univ := by
  refine eq_univ_iff_forall.mpr fun b => mem_iUnion.mpr ?_
  rcases sub_toIocDiv_zsmul_mem_Ioc hp a b with ⟨hl, hr⟩
  refine ⟨toIocDiv hp a b, ⟨lt_sub_iff_add_lt.mp hl, ?_⟩⟩
  rw [add_smul, one_smul, ← add_assoc]
  convert! sub_le_iff_le_add.mp hr using 1; abel
/-
**iUnion_Ico_add_zsmul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iUnion_Ico_add_zsmul : ⋃ n : Int, Ico (a + n • p) (a + (n + 1) • p) = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.eq_univ_iff_forall`：eq_univ_iff_forall {s : Set α} : s = univ ↔ fora
ll x, x in s
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `sub_toIcoDiv_zsmul_mem_Ico`：sub_toIcoDiv_zsmul_mem_Ico (a b : α) : b - t
oIcoDiv hp a b • p in Set.Ico a (a + p)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_sub_iff_add_le`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [A
ddRightMono α] {a b c : α}, a ≤ c - b ↔ a + b ≤ c
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `_private.Mathlib.Algebra.Order.ToIntervalMod.0.iUnion_Ico_add_zsmul._abe
l_1_1`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : LinearOrder α] [inst_2
 : IsOrderedAddMonoid α]   [inst_3 : Archimedean α] {p : α} (hp : 0…
· 使用定理 `sub_lt_iff_lt_add`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [A
ddRightStrictMono α] {a b c : α}, a - c < b ↔ a < b + c
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
-/
theorem iUnion_Ico_add_zsmul : ⋃ n : ℤ, Ico (a + n • p) (a + (n + 1) • p) = univ := by
  refine eq_univ_iff_forall.mpr fun b => mem_iUnion.mpr ?_
  rcases sub_toIcoDiv_zsmul_mem_Ico hp a b with ⟨hl, hr⟩
  refine ⟨toIcoDiv hp a b, ⟨le_sub_iff_add_le.mp hl, ?_⟩⟩
  rw [add_smul, one_smul, ← add_assoc]
  convert! sub_lt_iff_lt_add.mp hr using 1; abel
/-
**iUnion_Icc_add_zsmul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iUnion_Icc_add_zsmul : ⋃ n : Int, Icc (a + n • p) (a + (n + 1) • p) = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iUnion_Ioc_add_zsmul`：iUnion_Ioc_add_zsmul : ⋃ n : Int, Ioc (a + n • p) 
(a + (n + 1) • p) = univ
· 使用定理 `Set.iUnion_mono`：iUnion_mono {s t : ι -> Set α} (h : forall i, s i subse
teq t i) : ⋃ i, s i subseteq ⋃ i, t i
· 使用定理 `Set.Ioc_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc a b ⊆ Set.Icc a b
-/
theorem iUnion_Icc_add_zsmul : ⋃ n : ℤ, Icc (a + n • p) (a + (n + 1) • p) = univ := by
  simpa only [iUnion_Ioc_add_zsmul hp a, univ_subset_iff] using
    iUnion_mono fun n : ℤ => (Ioc_subset_Icc_self : Ioc (a + n • p) (a + (n + 1) • p) ⊆ Icc _ _)
/-
**iUnion_Ioc_zsmul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iUnion_Ioc_zsmul : ⋃ n : Int, Ioc (n • p) ((n + 1) • p) = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `iUnion_Ioc_add_zsmul`：iUnion_Ioc_add_zsmul : ⋃ n : Int, Ioc (a + n • p) 
(a + (n + 1) • p) = univ
-/
theorem iUnion_Ioc_zsmul : ⋃ n : ℤ, Ioc (n • p) ((n + 1) • p) = univ := by
  simpa only [zero_add] using iUnion_Ioc_add_zsmul hp 0
/-
**iUnion_Ico_zsmul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iUnion_Ico_zsmul : ⋃ n : Int, Ico (n • p) ((n + 1) • p) = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `iUnion_Ico_add_zsmul`：iUnion_Ico_add_zsmul : ⋃ n : Int, Ico (a + n • p) 
(a + (n + 1) • p) = univ
-/
theorem iUnion_Ico_zsmul : ⋃ n : ℤ, Ico (n • p) ((n + 1) • p) = univ := by
  simpa only [zero_add] using iUnion_Ico_add_zsmul hp 0
/-
**iUnion_Icc_zsmul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iUnion_Icc_zsmul : ⋃ n : Int, Icc (n • p) ((n + 1) • p) = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `iUnion_Icc_add_zsmul`：iUnion_Icc_add_zsmul : ⋃ n : Int, Icc (a + n • p) 
(a + (n + 1) • p) = univ
-/
theorem iUnion_Icc_zsmul : ⋃ n : ℤ, Icc (n • p) ((n + 1) • p) = univ := by
  simpa only [zero_add] using iUnion_Icc_add_zsmul hp 0

end LinearOrderedAddCommGroup

section LinearOrderedRing

variable {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α] [Archimedean α] (a : α)

/-
**iUnion_Ioc_add_intCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iUnion_Ioc_add_intCast : ⋃ n : Int, Ioc (a + n) (a + n + 1) = Set.univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zsmul_one`：∀ {R : Type u_1} [inst : AddGroupWithOne R] (n : ℤ), n • 1 = 
↑n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Int.cast_add`：∀ {R : Type u} [inst : AddGroupWithOne R] (m n : ℤ), ↑(m +
 n) = ↑m + ↑n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `iUnion_Ioc_add_zsmul`：iUnion_Ioc_add_zsmul : ⋃ n : Int, Ioc (a + n • p) 
(a + (n + 1) • p) = univ
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
-/
theorem iUnion_Ioc_add_intCast : ⋃ n : ℤ, Ioc (a + n) (a + n + 1) = Set.univ := by
  simpa only [zsmul_one, Int.cast_add, Int.cast_one, ← add_assoc] using
    iUnion_Ioc_add_zsmul zero_lt_one a
/-
**iUnion_Ico_add_intCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iUnion_Ico_add_intCast : ⋃ n : Int, Ico (a + n) (a + n + 1) = Set.univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zsmul_one`：∀ {R : Type u_1} [inst : AddGroupWithOne R] (n : ℤ), n • 1 = 
↑n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Int.cast_add`：∀ {R : Type u} [inst : AddGroupWithOne R] (m n : ℤ), ↑(m +
 n) = ↑m + ↑n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `iUnion_Ico_add_zsmul`：iUnion_Ico_add_zsmul : ⋃ n : Int, Ico (a + n • p) 
(a + (n + 1) • p) = univ
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
-/
theorem iUnion_Ico_add_intCast : ⋃ n : ℤ, Ico (a + n) (a + n + 1) = Set.univ := by
  simpa only [zsmul_one, Int.cast_add, Int.cast_one, ← add_assoc] using
    iUnion_Ico_add_zsmul zero_lt_one a
/-
**iUnion_Icc_add_intCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iUnion_Icc_add_intCast : ⋃ n : Int, Icc (a + n) (a + n + 1) = Set.univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zsmul_one`：∀ {R : Type u_1} [inst : AddGroupWithOne R] (n : ℤ), n • 1 = 
↑n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Int.cast_add`：∀ {R : Type u} [inst : AddGroupWithOne R] (m n : ℤ), ↑(m +
 n) = ↑m + ↑n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `iUnion_Icc_add_zsmul`：iUnion_Icc_add_zsmul : ⋃ n : Int, Icc (a + n • p) 
(a + (n + 1) • p) = univ
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
-/
theorem iUnion_Icc_add_intCast : ⋃ n : ℤ, Icc (a + n) (a + n + 1) = Set.univ := by
  simpa only [zsmul_one, Int.cast_add, Int.cast_one, ← add_assoc] using
    iUnion_Icc_add_zsmul zero_lt_one a

variable (α)
/-
**iUnion_Ioc_intCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iUnion_Ioc_intCast : ⋃ n : Int, Ioc (n : α) (n + 1) = Set.univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `iUnion_Ioc_add_intCast`：iUnion_Ioc_add_intCast : ⋃ n : Int, Ioc (a + n) 
(a + n + 1) = Set.univ
-/
theorem iUnion_Ioc_intCast : ⋃ n : ℤ, Ioc (n : α) (n + 1) = Set.univ := by
  simpa only [zero_add] using iUnion_Ioc_add_intCast (0 : α)
/-
**iUnion_Ico_intCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iUnion_Ico_intCast : ⋃ n : Int, Ico (n : α) (n + 1) = Set.univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `iUnion_Ico_add_intCast`：iUnion_Ico_add_intCast : ⋃ n : Int, Ico (a + n) 
(a + n + 1) = Set.univ
-/
theorem iUnion_Ico_intCast : ⋃ n : ℤ, Ico (n : α) (n + 1) = Set.univ := by
  simpa only [zero_add] using iUnion_Ico_add_intCast (0 : α)
/-
**iUnion_Icc_intCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iUnion_Icc_intCast : ⋃ n : Int, Icc (n : α) (n + 1) = Set.univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `iUnion_Icc_add_intCast`：iUnion_Icc_add_intCast : ⋃ n : Int, Icc (a + n) 
(a + n + 1) = Set.univ
-/
theorem iUnion_Icc_intCast : ⋃ n : ℤ, Icc (n : α) (n + 1) = Set.univ := by
  simpa only [zero_add] using iUnion_Icc_add_intCast (0 : α)

end LinearOrderedRing

end Union

