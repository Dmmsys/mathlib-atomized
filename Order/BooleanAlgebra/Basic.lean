/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Bryan Gin-ge Chen
-/
module

public import Mathlib.Order.BooleanAlgebra.Defs
public import Mathlib.Tactic.GRewrite

/-!
# Basic properties of Boolean algebras

This file provides some basic definitions, functions as well as lemmas for functions and type
classes related to Boolean algebras as defined in `Mathlib/Order/BooleanAlgebra/Defs.lean`.

## References

* <https://en.wikipedia.org/wiki/Boolean_algebra_(structure)#Generalizations>
* [*Postulates for Boolean Algebras and Generalized Boolean Algebras*, M.H. Stone][Stone1935]
* [*Lattice Theory: Foundation*, George Grätzer][Gratzer2011]

## Tags

generalized Boolean algebras, Boolean algebras, lattices, sdiff, compl

-/

public section

universe u v

variable {α : Type u} {β : Type*} {x y z : α}

/-!
### Generalized Boolean algebras

Some of the lemmas in this section are from:

* [*Lattice Theory: Foundation*, George Grätzer][Gratzer2011]
* <https://ncatlab.org/nlab/show/relative+complement>
* <https://people.math.gatech.edu/~mccuan/courses/4317/symmetricdifference.pdf>

-/

-- We might want an `IsCompl_of` predicate (for relative complements) generalizing `IsCompl`,
-- however we'd need another type class for lattices with bot, and all the API for that.
section GeneralizedBooleanAlgebra

variable [GeneralizedBooleanAlgebra α]

@[simp]
/-
**sup_inf_sdiff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sup_inf_sdiff (x y : α) : x ⊓ y ⊔ x \ y = x
参数：x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GeneralizedBooleanAlgebra.sup_inf_sdiff`：∀ {α : Type u} [self : Generali
zedBooleanAlgebra α] (a b : α), a ⊓ b ⊔ a \ b = a
-/
theorem sup_inf_sdiff (x y : α) : x ⊓ y ⊔ x \ y = x :=
  GeneralizedBooleanAlgebra.sup_inf_sdiff _ _

@[simp]
/-
**inf_inf_sdiff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inf_inf_sdiff (x y : α) : x ⊓ y ⊓ x \ y = ⊥
参数：x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GeneralizedBooleanAlgebra.inf_inf_sdiff`：∀ {α : Type u} [self : Generali
zedBooleanAlgebra α] (a b : α), a ⊓ b ⊓ a \ b = ⊥
-/
theorem inf_inf_sdiff (x y : α) : x ⊓ y ⊓ x \ y = ⊥ :=
  GeneralizedBooleanAlgebra.inf_inf_sdiff _ _

@[simp]
/-
**sup_sdiff_inf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sup_sdiff_inf (x y : α) : x \ y ⊔ x ⊓ y = x
参数：x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `sup_inf_sdiff`：sup_inf_sdiff (x y : α) : x ⊓ y ⊔ x \ y = x
-/
theorem sup_sdiff_inf (x y : α) : x \ y ⊔ x ⊓ y = x := by rw [sup_comm, sup_inf_sdiff]

@[simp]
/-
**inf_sdiff_inf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inf_sdiff_inf (x y : α) : x \ y ⊓ (x ⊓ y) = ⊥
参数：x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `inf_inf_sdiff`：inf_inf_sdiff (x y : α) : x ⊓ y ⊓ x \ y = ⊥
-/
theorem inf_sdiff_inf (x y : α) : x \ y ⊓ (x ⊓ y) = ⊥ := by rw [inf_comm, inf_inf_sdiff]

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) GeneralizedBooleanAlgebra.toOrderBot : OrderBot α where
  __ := GeneralizedBooleanAlgebra.toBot
  bot_le a := by
    rw [← inf_inf_sdiff a a, inf_assoc]
    exact inf_le_left
/-
**disjoint_inf_sdiff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：disjoint_inf_sdiff : Disjoint (x ⊓ y) (x \ y)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `disjoint_iff_inf_le`：disjoint_iff_inf_le : Disjoint a b ↔ a ⊓ b <= ⊥
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `inf_inf_sdiff`：inf_inf_sdiff (x y : α) : x ⊓ y ⊓ x \ y = ⊥
-/
theorem disjoint_inf_sdiff : Disjoint (x ⊓ y) (x \ y) :=
  disjoint_iff_inf_le.mpr (inf_inf_sdiff x y).le

-- TODO: in distributive lattices, relative complements are unique when they exist
/-
**sdiff_unique** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sdiff_unique (s : x ⊓ y ⊔ z = x) (i : x ⊓ y ⊓ z = ⊥) : x \ y = z
参数：s : x ⊓ y ⊔ z = x；i : x ⊓ y ⊓ z = ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_inf_eq_sup_eq`：eq_of_inf_eq_sup_eq {a b c : α} (h₁ : b ⊓ a = c ⊓ a
) (h₂ : b ⊔ a = c ⊔ a) : b = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `inf_inf_sdiff`：inf_inf_sdiff (x y : α) : x ⊓ y ⊓ x \ y = ⊥
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `sup_inf_sdiff`：sup_inf_sdiff (x y : α) : x ⊓ y ⊔ x \ y = x
-/
theorem sdiff_unique (s : x ⊓ y ⊔ z = x) (i : x ⊓ y ⊓ z = ⊥) : x \ y = z := by
  conv_rhs at s => rw [← sup_inf_sdiff x y, sup_comm]
  rw [sup_comm] at s
  conv_rhs at i => rw [← inf_inf_sdiff x y, inf_comm]
  rw [inf_comm] at i
  exact (eq_of_inf_eq_sup_eq i s).symm

-- Use `sdiff_le`
/-
**sdiff_le'** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem sdiff_le' : x \ y ≤ x :=
  calc
    x \ y ≤ x ⊓ y ⊔ x \ y := le_sup_right
    _ = x := sup_inf_sdiff x y

set_option backward.privateInPublic true in
-- Use `sdiff_sup_self`
/-
**sdiff_sup_self'** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem sdiff_sup_self' : y \ x ⊔ x = y ⊔ x :=
  calc
    y \ x ⊔ x = y \ x ⊔ (x ⊔ x ⊓ y) := by rw [sup_inf_self]
    _ = y ⊓ x ⊔ y \ x ⊔ x := by ac_rfl
    _ = y ⊔ x := by rw [sup_inf_sdiff]

@[simp]
/-
**sdiff_inf_sdiff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sdiff_inf_sdiff : x \ y ⊓ y \ x = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_inf_sdiff`：inf_inf_sdiff (x y : α) : x ⊓ y ⊓ x \ y = ⊥
· 使用定理 `sup_inf_sdiff`：sup_inf_sdiff (x y : α) : x ⊓ y ⊔ x \ y = x
· 使用定理 `inf_sup_left`：inf_sup_left (a b c : α) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Lean.Data.AC.Context.eq_of_norm`：∀ {α : Sort u_1} (ctx : Data.AC.Context
 α) (a b : Data.AC.Expr),   (Data.AC.norm ctx a == Data.AC.norm ctx b) = true → 
Data.AC.eval α ctx a …
· 使用定理 `instAssociativeMin_mathlib`：∀ {α : Type u} [inst : SemilatticeInf α], St
d.Associative fun x1 x2 => x1 ⊓ x2
· 使用定理 `instCommutativeMin_mathlib`：∀ {α : Type u} [inst : SemilatticeInf α], St
d.Commutative fun x1 x2 => x1 ⊓ x2
· 使用定理 `instIdempotentOpMin_mathlib`：∀ {α : Type u} [inst : SemilatticeInf α], S
td.IdempotentOp fun x1 x2 => x1 ⊓ x2
· 使用定理 `instAssociativeMax_mathlib`：∀ {α : Type u} [inst : SemilatticeSup α], St
d.Associative fun x1 x2 => x1 ⊔ x2
· 使用定理 `instCommutativeMax_mathlib`：∀ {α : Type u} [inst : SemilatticeSup α], St
d.Commutative fun x1 x2 => x1 ⊔ x2
· 使用定理 `instIdempotentOpMax_mathlib`：∀ {α : Type u} [inst : SemilatticeSup α], S
td.IdempotentOp fun x1 x2 => x1 ⊔ x2
· 使用定理 `inf_idem`：∀ {α : Type u} [inst : SemilatticeInf α] (a : α), a ⊓ a = a
· 使用定理 `inf_sup_right`：inf_sup_right (a b c : α) : (a ⊔ b) ⊓ c = a ⊓ c ⊔ b ⊓ c
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `bot_sup_eq`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : OrderBo
t α] (a : α), ⊥ ⊔ a = a
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `_private.Mathlib.Order.BooleanAlgebra.Basic.0.sdiff_le'`：∀ {α : Type u} 
{x y : α} [inst : GeneralizedBooleanAlgebra α], x \ y ≤ x
-/
theorem sdiff_inf_sdiff : x \ y ⊓ y \ x = ⊥ :=
  Eq.symm <|
    calc
      ⊥ = x ⊓ (y ⊓ x ⊔ y \ x) ⊓ x \ y := by rw [← inf_inf_sdiff, sup_inf_sdiff]
      _ = (x ⊓ (y ⊓ x) ⊔ x ⊓ y \ x) ⊓ x \ y := by rw [inf_sup_left]
      _ = (y ⊓ (x ⊓ x) ⊔ x ⊓ y \ x) ⊓ x \ y := by ac_rfl
      _ = x ⊓ y \ x ⊓ x \ y := by
          rw [inf_idem, inf_sup_right, ← inf_comm x y, inf_inf_sdiff, bot_sup_eq]
      _ = x ⊓ x \ y ⊓ y \ x := by ac_rfl
      _ = x \ y ⊓ y \ x := by rw [inf_of_le_right sdiff_le']
/-
**disjoint_sdiff_sdiff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：disjoint_sdiff_sdiff : Disjoint (x \ y) (y \ x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `disjoint_iff_inf_le`：disjoint_iff_inf_le : Disjoint a b ↔ a ⊓ b <= ⊥
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `sdiff_inf_sdiff`：sdiff_inf_sdiff : x \ y ⊓ y \ x = ⊥
-/
theorem disjoint_sdiff_sdiff : Disjoint (x \ y) (y \ x) :=
  disjoint_iff_inf_le.mpr sdiff_inf_sdiff.le

@[simp]
/-
**inf_sdiff_self_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inf_sdiff_self_right : x ⊓ y \ x = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_inf_sdiff`：sup_inf_sdiff (x y : α) : x ⊓ y ⊔ x \ y = x
· 使用定理 `inf_sup_right`：inf_sup_right (a b c : α) : (a ⊔ b) ⊓ c = a ⊓ c ⊔ b ⊓ c
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `inf_inf_sdiff`：inf_inf_sdiff (x y : α) : x ⊓ y ⊓ x \ y = ⊥
· 使用定理 `sdiff_inf_sdiff`：sdiff_inf_sdiff : x \ y ⊓ y \ x = ⊥
· 使用定理 `bot_sup_eq`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : OrderBo
t α] (a : α), ⊥ ⊔ a = a
-/
theorem inf_sdiff_self_right : x ⊓ y \ x = ⊥ :=
  calc
    x ⊓ y \ x = (x ⊓ y ⊔ x \ y) ⊓ y \ x := by rw [sup_inf_sdiff]
    _ = ⊥ := by rw [inf_sup_right, inf_comm x y, inf_inf_sdiff, sdiff_inf_sdiff, bot_sup_eq]

@[simp]
/-
**inf_sdiff_self_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inf_sdiff_self_left : y \ x ⊓ x = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `inf_sdiff_self_right`：inf_sdiff_self_right : x ⊓ y \ x = ⊥
-/
theorem inf_sdiff_self_left : y \ x ⊓ x = ⊥ := by rw [inf_comm, inf_sdiff_self_right]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra :
    GeneralizedCoheytingAlgebra α where
  __ := ‹GeneralizedBooleanAlgebra α›
  __ := GeneralizedBooleanAlgebra.toOrderBot
  sdiff := (· \ ·)
  sdiff_le_iff y x z :=
    ⟨fun h =>
      le_of_inf_le_sup_le
        (le_of_eq
          (by grind [sdiff_le', inf_of_le_right, inf_eq_right, inf_sdiff_self_right, bot_sup_eq,
            inf_sup_right]))
        (calc
          y ⊔ y \ x ≤ y \ x ⊔ x ⊔ z := by
            grind [sup_of_le_left, sdiff_le', le_sup_left, sdiff_sup_self']
          _ = x ⊔ z ⊔ y \ x := by ac_rfl),
      fun h => le_of_inf_le_sup_le (inf_sdiff_self_left.trans_le bot_le) (calc
        y \ x ⊔ x = y ⊔ x := sdiff_sup_self'
        _ ≤ x ⊔ z ⊔ x := sup_le_sup_right h x
        _ ≤ z ⊔ x := by rw [sup_assoc, sup_comm, sup_assoc, sup_idem])⟩
/-
**disjoint_sdiff_self_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：disjoint_sdiff_self_left : Disjoint (y \ x) x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `disjoint_iff_inf_le`：disjoint_iff_inf_le : Disjoint a b ↔ a ⊓ b <= ⊥
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `inf_sdiff_self_left`：inf_sdiff_self_left : y \ x ⊓ x = ⊥
-/
theorem disjoint_sdiff_self_left : Disjoint (y \ x) x :=
  disjoint_iff_inf_le.mpr inf_sdiff_self_left.le
/-
**disjoint_sdiff_self_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：disjoint_sdiff_self_right : Disjoint x (y \ x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `disjoint_iff_inf_le`：disjoint_iff_inf_le : Disjoint a b ↔ a ⊓ b <= ⊥
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `inf_sdiff_self_right`：inf_sdiff_self_right : x ⊓ y \ x = ⊥
-/
theorem disjoint_sdiff_self_right : Disjoint x (y \ x) :=
  disjoint_iff_inf_le.mpr inf_sdiff_self_right.le
/-
**le_sdiff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_sdiff : x <= y \ z ↔ x <= y ∧ Disjoint x z
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `sdiff_le`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a b :
 α}, a \ b ≤ a
· 使用定理 `Disjoint.mono_left`：Disjoint.mono_left (h : a <= b) : Disjoint b c -> Di
sjoint a c
· 使用定理 `disjoint_sdiff_self_left`：disjoint_sdiff_self_left : Disjoint (y \ x) x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Disjoint.sdiff_eq_left`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlg
ebra α] {a b : α}, Disjoint a b → a \ b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `sdiff_le_sdiff_right`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgeb
ra α] {a b c : α}, b ≤ a → b \ c ≤ a \ c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma le_sdiff : x ≤ y \ z ↔ x ≤ y ∧ Disjoint x z :=
  ⟨fun h ↦ ⟨h.trans sdiff_le, disjoint_sdiff_self_left.mono_left h⟩, fun h ↦
    by rw [← h.2.sdiff_eq_left]; exact sdiff_le_sdiff_right h.1⟩
/-
**sdiff_eq_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} {x y : α} [inst : GeneralizedBooleanAlgebra α], x \ y = x ↔
 Disjoint x y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.mono_left`：Disjoint.mono_left (h : a <= b) : Disjoint b c -> Di
sjoint a c
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `disjoint_sdiff_self_left`：disjoint_sdiff_self_left : Disjoint (y \ x) x
· 使用定理 `Disjoint.sdiff_eq_left`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlg
ebra α] {a b : α}, Disjoint a b → a \ b = a
-/
@[simp] lemma sdiff_eq_left : x \ y = x ↔ Disjoint x y :=
  ⟨fun h ↦ disjoint_sdiff_self_left.mono_left h.ge, Disjoint.sdiff_eq_left⟩

/- TODO: we could make an alternative constructor for `GeneralizedBooleanAlgebra` using
`Disjoint x (y \ x)` and `x ⊔ (y \ x) = y` as axioms. -/
/-
**Disjoint.sdiff_eq_of_sup_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Disjoint.sdiff_eq_of_sup_eq (hi : Disjoint x z) (hs : x ⊔ z = y) : y \ x =
 z
参数：hi : Disjoint x z；hs : x ⊔ z = y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inf_eq_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
= b ↔ b ≤ a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `sdiff_unique`：sdiff_unique (s : x ⊓ y ⊔ z = x) (i : x ⊓ y ⊓ z = ⊥) : x \
 y = z
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Disjoint.eq_bot`：Disjoint.eq_bot : Disjoint a b -> a ⊓ b = ⊥

--- 原说明 ---
TODO: we could make an alternative constructor for `GeneralizedBooleanAlgebra` u
sing
`Disjoint x (y \ x)` and `x ⊔ (y \ x) = y` as axioms.
-/
theorem Disjoint.sdiff_eq_of_sup_eq (hi : Disjoint x z) (hs : x ⊔ z = y) : y \ x = z :=
  have h : y ⊓ x = x := inf_eq_right.2 <| le_sup_left.trans hs.le
  sdiff_unique (by rw [h, hs]) (by rw [h, hi.eq_bot])
/-
**Disjoint.sdiff_unique** 是 Mathlib 中的一个定理，位于命名空间 `Disjoint`。
形式化陈述：∀ {α : Type u} {x y z : α} [inst : GeneralizedBooleanAlgebra α], Disjoint 
x z → z ≤ y → y ≤ x ⊔ z → y \ x = z
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sdiff_unique`：sdiff_unique (s : x ⊓ y ⊔ z = x) (i : x ⊓ y ⊓ z = ⊥) : x \
 y = z
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_inf_right`：sup_inf_right (a b c : α) : a ⊓ b ⊔ c = (a ⊔ c) ⊓ (b ⊔ c)
· 使用定理 `inf_sup_right`：inf_sup_right (a b c : α) : (a ⊔ b) ⊓ c = a ⊓ c ⊔ b ⊓ c
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `inf_sup_self`：inf_sup_self : a ⊓ (a ⊔ b) = a
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inf_eq_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
= b ↔ b ≤ a
· 使用定理 `sup_eq_left`：sup_eq_left : a ⊔ b = a ↔ b <= a
· 使用定理 `inf_assoc`：∀ {α : Type u} [inst : SemilatticeInf α] (a b c : α), a ⊓ b ⊓
 c = a ⊓ (b ⊓ c)
· 使用定理 `Disjoint.eq_bot`：Disjoint.eq_bot : Disjoint a b -> a ⊓ b = ⊥
· 使用定理 `inf_bot_eq`：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : OrderBo
t α] (a : α), a ⊓ ⊥ = ⊥
-/
protected theorem Disjoint.sdiff_unique (hd : Disjoint x z) (hz : z ≤ y) (hs : y ≤ x ⊔ z) :
    y \ x = z :=
  sdiff_unique
    (by
      rw [← inf_eq_right] at hs
      rwa [sup_inf_right, inf_sup_right, sup_comm x, inf_sup_self, inf_comm, sup_comm z,
        hs, sup_eq_left])
    (by rw [inf_assoc, hd.eq_bot, inf_bot_eq])

-- cf. `IsCompl.disjoint_left_iff` and `IsCompl.disjoint_right_iff`
/-
**disjoint_sdiff_iff_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：disjoint_sdiff_iff_le (hz : z <= y) (hx : x <= y) : Disjoint z (y \ x) ↔ z
 <= x
参数：hz : z <= y；hx : x <= y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_inf_le_sup_le`：le_of_inf_le_sup_le (h₁ : x ⊓ z <= y ⊓ z) (h₂ : x ⊔
 z <= y ⊔ z) : x <= y
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Disjoint.le_bot`：Disjoint.le_bot : Disjoint a b -> a ⊓ b <= ⊥
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_sdiff_cancel_right`：sup_sdiff_cancel_right (h : a <= b) : a ⊔ b \ a 
= b
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `sup_le_sup`：sup_le_sup (h₁ : a <= b) (h₂ : c <= d) : a ⊔ c <= b ⊔ d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `sdiff_le`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a b :
 α}, a \ b ≤ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sup_eq_right`：sup_eq_right : a ⊔ b = b ↔ a <= b
· 使用定理 `Disjoint.mono_left`：Disjoint.mono_left (h : a <= b) : Disjoint b c -> Di
sjoint a c
· 使用定理 `disjoint_sdiff_self_right`：disjoint_sdiff_self_right : Disjoint x (y \ x
)
-/
theorem disjoint_sdiff_iff_le (hz : z ≤ y) (hx : x ≤ y) : Disjoint z (y \ x) ↔ z ≤ x :=
  ⟨fun H =>
    le_of_inf_le_sup_le (le_trans H.le_bot bot_le)
      (by
        rw [sup_sdiff_cancel_right hx]
        grw [sdiff_le]
        rw [sup_eq_right.2 hz]),
    fun H => disjoint_sdiff_self_right.mono_left H⟩

-- cf. `IsCompl.le_left_iff` and `IsCompl.le_right_iff`
/-
**le_iff_disjoint_sdiff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_iff_disjoint_sdiff (hz : z <= y) (hx : x <= y) : z <= x ↔ Disjoint z (y
 \ x)
参数：hz : z <= y；hx : x <= y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `disjoint_sdiff_iff_le`：disjoint_sdiff_iff_le (hz : z <= y) (hx : x <= y)
 : Disjoint z (y \ x) ↔ z <= x
-/
theorem le_iff_disjoint_sdiff (hz : z ≤ y) (hx : x ≤ y) : z ≤ x ↔ Disjoint z (y \ x) :=
  (disjoint_sdiff_iff_le hz hx).symm

-- cf. `IsCompl.inf_left_eq_bot_iff` and `IsCompl.inf_right_eq_bot_iff`
/-
**inf_sdiff_eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inf_sdiff_eq_bot_iff (hz : z <= y) (hx : x <= y) : z ⊓ y \ x = ⊥ ↔ z <= x
参数：hz : z <= y；hx : x <= y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `disjoint_iff`：disjoint_iff : Disjoint a b ↔ a ⊓ b = ⊥
· 使用定理 `disjoint_sdiff_iff_le`：disjoint_sdiff_iff_le (hz : z <= y) (hx : x <= y)
 : Disjoint z (y \ x) ↔ z <= x
-/
theorem inf_sdiff_eq_bot_iff (hz : z ≤ y) (hx : x ≤ y) : z ⊓ y \ x = ⊥ ↔ z ≤ x := by
  rw [← disjoint_iff]
  exact disjoint_sdiff_iff_le hz hx

-- cf. `IsCompl.left_le_iff` and `IsCompl.right_le_iff`
/-
**le_iff_eq_sup_sdiff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_iff_eq_sup_sdiff (hz : z <= y) (hx : x <= y) : x <= z ↔ y = z ⊔ y \ x
参数：hz : z <= y；hx : x <= y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sup_sdiff_cancel'`：sup_sdiff_cancel' (hab : a <= b) (hbc : b <= c) : b ⊔
 c \ a = c
· 使用定理 `le_of_inf_le_sup_le`：le_of_inf_le_sup_le (h₁ : x ⊓ z <= y ⊓ z) (h₂ : x ⊔
 z <= y ⊔ z) : x <= y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_sdiff_self_right`：inf_sdiff_self_right : x ⊓ y \ x = ⊥
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sup_sdiff_cancel_right`：sup_sdiff_cancel_right (h : a <= b) : a ⊔ b \ a 
= b
-/
theorem le_iff_eq_sup_sdiff (hz : z ≤ y) (hx : x ≤ y) : x ≤ z ↔ y = z ⊔ y \ x :=
  ⟨fun H => (sup_sdiff_cancel' H hz).symm,
    fun H => by
    conv_lhs at H => rw [← sup_sdiff_cancel_right hx]
    refine le_of_inf_le_sup_le ?_ H.le
    rw [inf_sdiff_self_right]
    exact bot_le⟩

-- cf. `IsCompl.sup_inf`
/-
**sdiff_sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sdiff_sup : y \ (x ⊔ z) = y \ x ⊓ y \ z
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sdiff_unique`：sdiff_unique (s : x ⊓ y ⊔ z = x) (i : x ⊓ y ⊓ z = ⊥) : x \
 y = z
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_inf_left`：sup_inf_left (a b c : α) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c)
· 使用定理 `inf_sup_left`：inf_sup_left (a b c : α) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Lean.Data.AC.Context.eq_of_norm`：∀ {α : Sort u_1} (ctx : Data.AC.Context
 α) (a b : Data.AC.Expr),   (Data.AC.norm ctx a == Data.AC.norm ctx b) = true → 
Data.AC.eval α ctx a …
· 使用定理 `instAssociativeMin_mathlib`：∀ {α : Type u} [inst : SemilatticeInf α], St
d.Associative fun x1 x2 => x1 ⊓ x2
· 使用定理 `instCommutativeMin_mathlib`：∀ {α : Type u} [inst : SemilatticeInf α], St
d.Commutative fun x1 x2 => x1 ⊓ x2
· 使用定理 `instIdempotentOpMin_mathlib`：∀ {α : Type u} [inst : SemilatticeInf α], S
td.IdempotentOp fun x1 x2 => x1 ⊓ x2
· 使用定理 `instAssociativeMax_mathlib`：∀ {α : Type u} [inst : SemilatticeSup α], St
d.Associative fun x1 x2 => x1 ⊔ x2
· 使用定理 `instCommutativeMax_mathlib`：∀ {α : Type u} [inst : SemilatticeSup α], St
d.Commutative fun x1 x2 => x1 ⊔ x2
· 使用定理 `instIdempotentOpMax_mathlib`：∀ {α : Type u} [inst : SemilatticeSup α], S
td.IdempotentOp fun x1 x2 => x1 ⊔ x2
· 使用定理 `sup_inf_sdiff`：sup_inf_sdiff (x y : α) : x ⊓ y ⊔ x \ y = x
· 使用定理 `sup_inf_self`：∀ {α : Type u} [inst : Lattice α] {a b : α}, a ⊔ a ⊓ b = a
· 使用定理 `inf_idem`：∀ {α : Type u} [inst : SemilatticeInf α] (a : α), a ⊓ a = a
· 使用定理 `inf_sup_right`：inf_sup_right (a b c : α) : (a ⊔ b) ⊓ c = a ⊓ c ⊔ b ⊓ c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `inf_inf_sdiff`：inf_inf_sdiff (x y : α) : x ⊓ y ⊓ x \ y = ⊥
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `inf_sdiff_inf`：inf_sdiff_inf (x y : α) : x \ y ⊓ (x ⊓ y) = ⊥
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sdiff_sup : y \ (x ⊔ z) = y \ x ⊓ y \ z :=
  sdiff_unique
    (calc
      y ⊓ (x ⊔ z) ⊔ y \ x ⊓ y \ z = (y ⊓ x ⊔ y ⊓ z ⊔ y \ x) ⊓ (y ⊓ x ⊔ y ⊓ z ⊔ y \ z) := by
          rw [sup_inf_left, inf_sup_left y]
      _ = (y ⊓ z ⊔ (y ⊓ x ⊔ y \ x)) ⊓ (y ⊓ x ⊔ (y ⊓ z ⊔ y \ z)) := by ac_rfl
      _ = (y ⊓ z ⊔ y) ⊓ (y ⊓ x ⊔ y) := by rw [sup_inf_sdiff, sup_inf_sdiff]
      _ = (y ⊔ y ⊓ z) ⊓ (y ⊔ y ⊓ x) := by ac_rfl
      _ = y := by rw [sup_inf_self, sup_inf_self, inf_idem])
    (calc
      y ⊓ (x ⊔ z) ⊓ (y \ x ⊓ y \ z) = y ⊓ x ⊓ (y \ x ⊓ y \ z) ⊔ y ⊓ z ⊓ (y \ x ⊓ y \ z) := by
          rw [inf_sup_left, inf_sup_right]
      _ = y ⊓ x ⊓ y \ x ⊓ y \ z ⊔ y \ x ⊓ (y \ z ⊓ (y ⊓ z)) := by ac_rfl
      _ = ⊥ := by simp)
/-
**sdiff_eq_sdiff_iff_inf_eq_inf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sdiff_eq_sdiff_iff_inf_eq_inf : y \ x = y \ z ↔ y ⊓ x = y ⊓ z
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_inf_eq_sup_eq`：eq_of_inf_eq_sup_eq {a b c : α} (h₁ : b ⊓ a = c ⊓ a
) (h₂ : b ⊔ a = c ⊔ a) : b = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_inf_sdiff`：inf_inf_sdiff (x y : α) : x ⊓ y ⊓ x \ y = ⊥
· 使用定理 `sup_inf_sdiff`：sup_inf_sdiff (x y : α) : x ⊓ y ⊔ x \ y = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sdiff_inf_self_right`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgeb
ra α] (a b : α), b \ (a ⊓ b) = b \ a
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
-/
theorem sdiff_eq_sdiff_iff_inf_eq_inf : y \ x = y \ z ↔ y ⊓ x = y ⊓ z :=
  ⟨fun h => eq_of_inf_eq_sup_eq (a := y \ x) (by rw [inf_inf_sdiff, h, inf_inf_sdiff])
    (by rw [sup_inf_sdiff, h, sup_inf_sdiff]),
    fun h => by rw [← sdiff_inf_self_right, ← sdiff_inf_self_right z y, inf_comm, h, inf_comm]⟩
/-
**sdiff_eq_self_iff_disjoint** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sdiff_eq_self_iff_disjoint : x \ y = x ↔ Disjoint y x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `sdiff_eq_left`：∀ {α : Type u} {x y : α} [inst : GeneralizedBooleanAlgebr
a α], x \ y = x ↔ Disjoint x y
· 使用定理 `disjoint_comm`：disjoint_comm : Disjoint a b ↔ Disjoint b a
-/
theorem sdiff_eq_self_iff_disjoint : x \ y = x ↔ Disjoint y x := sdiff_eq_left.trans disjoint_comm
/-
**sdiff_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sdiff_lt (hx : y <= x) (hy : y != ⊥) : x \ y < x
参数：hx : y <= x；hy : y != ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用定理 `sdiff_le`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a b :
 α}, a \ b ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `disjoint_iff`：disjoint_iff : Disjoint a b ↔ a ⊓ b = ⊥
· 使用定理 `sdiff_eq_left`：∀ {α : Type u} {x y : α} [inst : GeneralizedBooleanAlgebr
a α], x \ y = x ↔ Disjoint x y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inf_eq_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
= b ↔ b ≤ a
-/
theorem sdiff_lt (hx : y ≤ x) (hy : y ≠ ⊥) : x \ y < x := by
  refine sdiff_le.lt_of_ne fun h => hy ?_
  rw [sdiff_eq_left, disjoint_iff] at h
  rw [← h, inf_eq_right.mpr hx]
/-
**sdiff_lt_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sdiff_lt_left : x \ y < x ↔ ¬ Disjoint y x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `lt_iff_le_and_ne`：lt_iff_le_and_ne : a < b ↔ a <= b ∧ a != b
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `sdiff_eq_self_iff_disjoint`：sdiff_eq_self_iff_disjoint : x \ y = x ↔ Dis
joint y x
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `sdiff_le`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a b :
 α}, a \ b ≤ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sdiff_lt_left : x \ y < x ↔ ¬ Disjoint y x := by
  rw [lt_iff_le_and_ne, Ne, sdiff_eq_self_iff_disjoint, and_iff_right sdiff_le]

@[simp]
/-
**le_sdiff_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_sdiff_right : x <= y \ x ↔ x = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `disjoint_self`：disjoint_self : Disjoint a a ↔ a = ⊥
· 使用定理 `Disjoint.mono_right`：Disjoint.mono_right (h : b <= c) : Disjoint a c -> 
Disjoint a b
· 使用定理 `disjoint_sdiff_self_right`：disjoint_sdiff_self_right : Disjoint x (y \ x
)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
-/
theorem le_sdiff_right : x ≤ y \ x ↔ x = ⊥ :=
  ⟨fun h => disjoint_self.1 (disjoint_sdiff_self_right.mono_right h), fun h => h.le.trans bot_le⟩
/-
**sdiff_eq_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} {x y : α} [inst : GeneralizedBooleanAlgebra α], x \ y = y ↔
 x = ⊥ ∧ y = ⊥
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Disjoint.eq_iff`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Orde
rBot α] {a b : α}, Disjoint a b → (a = b ↔ a = ⊥ ∧ b = ⊥)
· 使用定理 `disjoint_sdiff_self_left`：disjoint_sdiff_self_left : Disjoint (y \ x) x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] lemma sdiff_eq_right : x \ y = y ↔ x = ⊥ ∧ y = ⊥ := by
  rw [disjoint_sdiff_self_left.eq_iff]; simp_all
/-
**sdiff_ne_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sdiff_ne_right : x \ y != y ↔ x != ⊥ ∨ y != ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `sdiff_eq_right`：∀ {α : Type u} {x y : α} [inst : GeneralizedBooleanAlgeb
ra α], x \ y = y ↔ x = ⊥ ∧ y = ⊥
· 使用定理 `not_and_or`：not_and_or : ¬(a ∧ b) ↔ ¬a ∨ ¬b
-/
lemma sdiff_ne_right : x \ y ≠ y ↔ x ≠ ⊥ ∨ y ≠ ⊥ := sdiff_eq_right.not.trans not_and_or
/-
**sdiff_lt_sdiff_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sdiff_lt_sdiff_right (h : x < y) (hz : z <= x) : x \ z < y \ z
参数：h : x < y；hz : z <= x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.lt_of_not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ 
b → ¬b ≤ a → a < b
· 使用定理 `sdiff_le_sdiff_right`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgeb
ra α] {a b c : α}, b ≤ a → b \ c ≤ a \ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_sdiff_sup`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a
 b : α}, b ≤ b \ a ⊔ a
· 使用定理 `sup_le_of_le_sdiff_right`：sup_le_of_le_sdiff_right (h : a <= c \ b) (hbc
 : b <= c) : a ⊔ b <= c
-/
theorem sdiff_lt_sdiff_right (h : x < y) (hz : z ≤ x) : x \ z < y \ z :=
  (sdiff_le_sdiff_right h.le).lt_of_not_ge
    fun h' => h.not_ge <| le_sdiff_sup.trans <| sup_le_of_le_sdiff_right h' hz
/-
**sup_inf_inf_sdiff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sup_inf_inf_sdiff : x ⊓ y ⊓ z ⊔ y \ z = x ⊓ y ⊔ y \ z
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_assoc`：∀ {α : Type u} [inst : SemilatticeInf α] (a b c : α), a ⊓ b ⊓
 c = a ⊓ (b ⊓ c)
· 使用定理 `sup_inf_right`：sup_inf_right (a b c : α) : a ⊓ b ⊔ c = (a ⊔ c) ⊓ (b ⊔ c)
· 使用定理 `sup_inf_sdiff`：sup_inf_sdiff (x y : α) : x ⊓ y ⊔ x \ y = x
· 使用定理 `inf_sup_right`：inf_sup_right (a b c : α) : (a ⊔ b) ⊓ c = a ⊓ c ⊔ b ⊓ c
· 使用定理 `inf_sdiff_left`：inf_sdiff_left : a \ b ⊓ a = a \ b
-/
theorem sup_inf_inf_sdiff : x ⊓ y ⊓ z ⊔ y \ z = x ⊓ y ⊔ y \ z := by
  rw [inf_assoc, sup_inf_right, sup_inf_sdiff, inf_sup_right, inf_sdiff_left]
/-
**sdiff_sdiff_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sdiff_sdiff_right : x \ (y \ z) = x \ y ⊔ x ⊓ y ⊓ z
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inf_assoc`：∀ {α : Type u} [inst : SemilatticeInf α] (a b c : α), a ⊓ b ⊓
 c = a ⊓ (b ⊓ c)
· 使用定理 `sup_inf_inf_sdiff`：sup_inf_inf_sdiff : x ⊓ y ⊓ z ⊔ y \ z = x ⊓ y ⊔ y \ z
· 使用定理 `sdiff_unique`：sdiff_unique (s : x ⊓ y ⊔ z = x) (i : x ⊓ y ⊓ z = ⊥) : x \
 y = z
· 使用定理 `sup_inf_right`：sup_inf_right (a b c : α) : a ⊓ b ⊔ c = (a ⊔ c) ⊓ (b ⊔ c)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Lean.Data.AC.Context.eq_of_norm`：∀ {α : Sort u_1} (ctx : Data.AC.Context
 α) (a b : Data.AC.Expr),   (Data.AC.norm ctx a == Data.AC.norm ctx b) = true → 
Data.AC.eval α ctx a …
· 使用定理 `instAssociativeMin_mathlib`：∀ {α : Type u} [inst : SemilatticeInf α], St
d.Associative fun x1 x2 => x1 ⊓ x2
· 使用定理 `instCommutativeMin_mathlib`：∀ {α : Type u} [inst : SemilatticeInf α], St
d.Commutative fun x1 x2 => x1 ⊓ x2
· 使用定理 `instIdempotentOpMin_mathlib`：∀ {α : Type u} [inst : SemilatticeInf α], S
td.IdempotentOp fun x1 x2 => x1 ⊓ x2
· 使用定理 `instAssociativeMax_mathlib`：∀ {α : Type u} [inst : SemilatticeSup α], St
d.Associative fun x1 x2 => x1 ⊔ x2
· 使用定理 `instCommutativeMax_mathlib`：∀ {α : Type u} [inst : SemilatticeSup α], St
d.Commutative fun x1 x2 => x1 ⊔ x2
· 使用定理 `instIdempotentOpMax_mathlib`：∀ {α : Type u} [inst : SemilatticeSup α], S
td.IdempotentOp fun x1 x2 => x1 ⊔ x2
· 使用定理 `sup_inf_self`：∀ {α : Type u} [inst : Lattice α] {a b : α}, a ⊔ a ⊓ b = a
· 使用定理 `sup_sdiff_left`：sup_sdiff_left : a ⊔ a \ b = a
· 使用定理 `sup_assoc`：sup_assoc (a b c : α) : a ⊔ b ⊔ c = a ⊔ (b ⊔ c)
· 使用定理 `sup_inf_left`：sup_inf_left (a b c : α) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c)
· 使用定理 `_private.Mathlib.Order.BooleanAlgebra.Basic.0.sdiff_sup_self'`：∀ {α : Ty
pe u} {x y : α} [inst : GeneralizedBooleanAlgebra α], y \ x ⊔ x = y ⊔ x
· 使用定理 `inf_sup_right`：inf_sup_right (a b c : α) : (a ⊔ b) ⊓ c = a ⊓ c ⊔ b ⊓ c
· 使用定理 `inf_sdiff_sup_right`：inf_sdiff_sup_right : a \ c ⊓ (b ⊔ a) = a \ c
· 使用定理 `inf_sup_left`：inf_sup_left (a b c : α) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `sup_inf_sdiff`：sup_inf_sdiff (x y : α) : x ⊓ y ⊔ x \ y = x
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
（共 37 条，此处仅展示前 30 条）
-/
theorem sdiff_sdiff_right : x \ (y \ z) = x \ y ⊔ x ⊓ y ⊓ z := by
  rw [sup_comm, inf_comm, ← inf_assoc, sup_inf_inf_sdiff]
  apply sdiff_unique
  · calc
      x ⊓ y \ z ⊔ (z ⊓ x ⊔ x \ y) = (x ⊔ (z ⊓ x ⊔ x \ y)) ⊓ (y \ z ⊔ (z ⊓ x ⊔ x \ y)) := by
          rw [sup_inf_right]
      _ = (x ⊔ x ⊓ z ⊔ x \ y) ⊓ (y \ z ⊔ (x ⊓ z ⊔ x \ y)) := by ac_rfl
      _ = x ⊓ (y \ z ⊔ (x ⊓ z ⊔ x ⊓ y) ⊔ x \ y) := by
          rw [sup_inf_self, sup_sdiff_left, ← sup_assoc, sup_inf_left, sdiff_sup_self',
            inf_sup_right, sup_comm y, inf_sdiff_sup_right, inf_sup_left x z y]
      _ = x ⊓ (y \ z ⊔ (x ⊓ z ⊔ (x ⊓ y ⊔ x \ y))) := by ac_rfl
      _ = x := by simp
  · calc
      x ⊓ y \ z ⊓ (z ⊓ x ⊔ x \ y) = x ⊓ y \ z ⊓ (z ⊓ x) ⊔ x ⊓ y \ z ⊓ x \ y := by rw [inf_sup_left]
      _ = x ⊓ (y \ z ⊓ z ⊓ x) ⊔ x ⊓ y \ z ⊓ x \ y := by ac_rfl
      _ = x ⊓ y \ z ⊓ x \ y := by rw [inf_sdiff_self_left, bot_inf_eq, inf_bot_eq, bot_sup_eq]
      _ = x ⊓ (y \ z ⊓ y) ⊓ x \ y := by conv_lhs => rw [← inf_sdiff_left]
      _ = x ⊓ (y \ z ⊓ (y ⊓ x \ y)) := by ac_rfl
      _ = ⊥ := by rw [inf_sdiff_self_right, inf_bot_eq, inf_bot_eq]
/-
**sdiff_sdiff_right'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sdiff_sdiff_right' : x \ (y \ z) = x \ y ⊔ x ⊓ z
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sdiff_sdiff_right`：sdiff_sdiff_right : x \ (y \ z) = x \ y ⊔ x ⊓ y ⊓ z
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Lean.Data.AC.Context.eq_of_norm`：∀ {α : Sort u_1} (ctx : Data.AC.Context
 α) (a b : Data.AC.Expr),   (Data.AC.norm ctx a == Data.AC.norm ctx b) = true → 
Data.AC.eval α ctx a …
· 使用定理 `instAssociativeMin_mathlib`：∀ {α : Type u} [inst : SemilatticeInf α], St
d.Associative fun x1 x2 => x1 ⊓ x2
· 使用定理 `instCommutativeMin_mathlib`：∀ {α : Type u} [inst : SemilatticeInf α], St
d.Commutative fun x1 x2 => x1 ⊓ x2
· 使用定理 `instIdempotentOpMin_mathlib`：∀ {α : Type u} [inst : SemilatticeInf α], S
td.IdempotentOp fun x1 x2 => x1 ⊓ x2
· 使用定理 `instAssociativeMax_mathlib`：∀ {α : Type u} [inst : SemilatticeSup α], St
d.Associative fun x1 x2 => x1 ⊔ x2
· 使用定理 `instCommutativeMax_mathlib`：∀ {α : Type u} [inst : SemilatticeSup α], St
d.Commutative fun x1 x2 => x1 ⊔ x2
· 使用定理 `instIdempotentOpMax_mathlib`：∀ {α : Type u} [inst : SemilatticeSup α], S
td.IdempotentOp fun x1 x2 => x1 ⊔ x2
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sup_inf_inf_sdiff`：sup_inf_inf_sdiff : x ⊓ y ⊓ z ⊔ y \ z = x ⊓ y ⊔ y \ z
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
-/
theorem sdiff_sdiff_right' : x \ (y \ z) = x \ y ⊔ x ⊓ z :=
  calc
    x \ (y \ z) = x \ y ⊔ x ⊓ y ⊓ z := sdiff_sdiff_right
    _ = z ⊓ x ⊓ y ⊔ x \ y := by ac_rfl
    _ = x \ y ⊔ x ⊓ z := by rw [sup_inf_inf_sdiff, sup_comm, inf_comm]
/-
**sdiff_sdiff_eq_sdiff_sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sdiff_sdiff_eq_sdiff_sup (h : z <= x) : x \ (y \ z) = x \ y ⊔ z
参数：h : z <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sdiff_sdiff_right'`：sdiff_sdiff_right' : x \ (y \ z) = x \ y ⊔ x ⊓ z
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inf_eq_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
= b ↔ b ≤ a
-/
theorem sdiff_sdiff_eq_sdiff_sup (h : z ≤ x) : x \ (y \ z) = x \ y ⊔ z := by
  rw [sdiff_sdiff_right', inf_eq_right.2 h]

@[simp]
/-
**sdiff_sdiff_right_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sdiff_sdiff_right_self : x \ (x \ y) = x ⊓ y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sdiff_sdiff_right`：sdiff_sdiff_right : x \ (y \ z) = x \ y ⊔ x ⊓ y ⊓ z
· 使用定理 `inf_idem`：∀ {α : Type u} [inst : SemilatticeInf α] (a : α), a ⊓ a = a
· 使用定理 `sdiff_self`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a :
 α}, a \ a = ⊥
· 使用定理 `bot_sup_eq`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : OrderBo
t α] (a : α), ⊥ ⊔ a = a
-/
theorem sdiff_sdiff_right_self : x \ (x \ y) = x ⊓ y := by
  rw [sdiff_sdiff_right, inf_idem, sdiff_self, bot_sup_eq]
/-
**sdiff_sdiff_eq_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sdiff_sdiff_eq_self (h : y <= x) : x \ (x \ y) = y
参数：h : y <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sdiff_sdiff_right_self`：sdiff_sdiff_right_self : x \ (x \ y) = x ⊓ y
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
-/
theorem sdiff_sdiff_eq_self (h : y ≤ x) : x \ (x \ y) = y := by
  rw [sdiff_sdiff_right_self, inf_of_le_right h]
/-
**sdiff_eq_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sdiff_eq_symm (hy : y <= x) (h : x \ y = z) : x \ z = y
参数：hy : y <= x；h : x \ y = z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sdiff_sdiff_eq_self`：sdiff_sdiff_eq_self (h : y <= x) : x \ (x \ y) = y
-/
theorem sdiff_eq_symm (hy : y ≤ x) (h : x \ y = z) : x \ z = y := by
  rw [← h, sdiff_sdiff_eq_self hy]
/-
**sdiff_eq_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sdiff_eq_comm (hy : y <= x) (hz : z <= x) : x \ y = z ↔ x \ z = y
参数：hy : y <= x；hz : z <= x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sdiff_eq_symm`：sdiff_eq_symm (hy : y <= x) (h : x \ y = z) : x \ z = y
-/
theorem sdiff_eq_comm (hy : y ≤ x) (hz : z ≤ x) : x \ y = z ↔ x \ z = y :=
  ⟨sdiff_eq_symm hy, sdiff_eq_symm hz⟩
/-
**sdiff_right_inj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sdiff_right_inj (hxz : x <= z) (hyz : y <= z) : z \ x = z \ y ↔ x = y
参数：hxz : x <= z；hyz : y <= z。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sdiff_sdiff_eq_self`：sdiff_sdiff_eq_self (h : y <= x) : x \ (x \ y) = y
-/
theorem sdiff_right_inj (hxz : x ≤ z) (hyz : y ≤ z) : z \ x = z \ y ↔ x = y :=
  ⟨fun h => by rw [← sdiff_sdiff_eq_self hxz, h, sdiff_sdiff_eq_self hyz], congrArg (z \ ·)⟩

@[deprecated sdiff_right_inj (since := "2026-04-16")]
/-
**eq_of_sdiff_eq_sdiff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_of_sdiff_eq_sdiff (hxz : x <= z) (hyz : y <= z) (h : z \ x = z \ y) : x
 = y
参数：hxz : x <= z；hyz : y <= z；h : z \ x = z \ y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sdiff_right_inj`：sdiff_right_inj (hxz : x <= z) (hyz : y <= z) : z \ x =
 z \ y ↔ x = y
-/
theorem eq_of_sdiff_eq_sdiff (hxz : x ≤ z) (hyz : y ≤ z) (h : z \ x = z \ y) : x = y :=
  (sdiff_right_inj hxz hyz).mp h
/-
**sdiff_le_sdiff_iff_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sdiff_le_sdiff_iff_le (hx : x <= z) (hy : y <= z) : z \ x <= z \ y ↔ y <= 
x
参数：hx : x <= z；hy : y <= z。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sdiff_sdiff_eq_self`：sdiff_sdiff_eq_self (h : y <= x) : x \ (x \ y) = y
· 使用定理 `sdiff_le_sdiff_left`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebr
a α] {a b c : α}, b ≤ a → c \ a ≤ c \ b
-/
theorem sdiff_le_sdiff_iff_le (hx : x ≤ z) (hy : y ≤ z) : z \ x ≤ z \ y ↔ y ≤ x := by
  refine ⟨fun h ↦ ?_, sdiff_le_sdiff_left⟩
  rw [← sdiff_sdiff_eq_self hx, ← sdiff_sdiff_eq_self hy]
  exact sdiff_le_sdiff_left h
/-
**sdiff_sdiff_left'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sdiff_sdiff_left' : (x \ y) \ z = x \ y ⊓ x \ z
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sdiff_sdiff_left`：sdiff_sdiff_left : (a \ b) \ c = a \ (b ⊔ c)
· 使用定理 `sdiff_sup`：sdiff_sup : y \ (x ⊔ z) = y \ x ⊓ y \ z
-/
theorem sdiff_sdiff_left' : (x \ y) \ z = x \ y ⊓ x \ z := by rw [sdiff_sdiff_left, sdiff_sup]
/-
**sdiff_sdiff_sup_sdiff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sdiff_sdiff_sup_sdiff : z \ (x \ y ⊔ y \ x) = z ⊓ (z \ x ⊔ y) ⊓ (z \ y ⊔ x
)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sdiff_sup`：sdiff_sup : y \ (x ⊔ z) = y \ x ⊓ y \ z
· 使用定理 `sdiff_sdiff_right`：sdiff_sdiff_right : x \ (y \ z) = x \ y ⊔ x ⊓ y ⊓ z
· 使用定理 `sup_inf_left`：sup_inf_left (a b c : α) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c)
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `sup_inf_sdiff`：sup_inf_sdiff (x y : α) : x ⊓ y ⊔ x \ y = x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Lean.Data.AC.Context.eq_of_norm`：∀ {α : Sort u_1} (ctx : Data.AC.Context
 α) (a b : Data.AC.Expr),   (Data.AC.norm ctx a == Data.AC.norm ctx b) = true → 
Data.AC.eval α ctx a …
· 使用定理 `instAssociativeMax_mathlib`：∀ {α : Type u} [inst : SemilatticeSup α], St
d.Associative fun x1 x2 => x1 ⊔ x2
· 使用定理 `instCommutativeMax_mathlib`：∀ {α : Type u} [inst : SemilatticeSup α], St
d.Commutative fun x1 x2 => x1 ⊔ x2
· 使用定理 `instIdempotentOpMax_mathlib`：∀ {α : Type u} [inst : SemilatticeSup α], S
td.IdempotentOp fun x1 x2 => x1 ⊔ x2
· 使用定理 `instAssociativeMin_mathlib`：∀ {α : Type u} [inst : SemilatticeInf α], St
d.Associative fun x1 x2 => x1 ⊓ x2
· 使用定理 `instCommutativeMin_mathlib`：∀ {α : Type u} [inst : SemilatticeInf α], St
d.Commutative fun x1 x2 => x1 ⊓ x2
· 使用定理 `instIdempotentOpMin_mathlib`：∀ {α : Type u} [inst : SemilatticeInf α], S
td.IdempotentOp fun x1 x2 => x1 ⊓ x2
· 使用定理 `inf_idem`：∀ {α : Type u} [inst : SemilatticeInf α] (a : α), a ⊓ a = a
-/
theorem sdiff_sdiff_sup_sdiff : z \ (x \ y ⊔ y \ x) = z ⊓ (z \ x ⊔ y) ⊓ (z \ y ⊔ x) :=
  calc
    z \ (x \ y ⊔ y \ x) = z ⊓ (z \ x ⊔ y) ⊓ (z ⊓ (z \ y ⊔ x)) := by
        rw [sdiff_sup, sdiff_sdiff_right, sdiff_sdiff_right, sup_inf_left, sup_comm, sup_inf_sdiff,
          sup_inf_left, sup_comm (z \ y), sup_inf_sdiff]
    _ = z ⊓ z ⊓ (z \ x ⊔ y) ⊓ (z \ y ⊔ x) := by ac_rfl
    _ = z ⊓ (z \ x ⊔ y) ⊓ (z \ y ⊔ x) := by rw [inf_idem]
/-
**sdiff_sdiff_sup_sdiff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sdiff_sdiff_sup_sdiff' : z \ (x \ y ⊔ y \ x) = z ⊓ x ⊓ y ⊔ z \ x ⊓ z \ y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sdiff_sup`：sdiff_sup : y \ (x ⊔ z) = y \ x ⊓ y \ z
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sdiff_sdiff_right`：sdiff_sdiff_right : x \ (y \ z) = x \ y ⊔ x ⊓ y ⊓ z
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Lean.Data.AC.Context.eq_of_norm`：∀ {α : Sort u_1} (ctx : Data.AC.Context
 α) (a b : Data.AC.Expr),   (Data.AC.norm ctx a == Data.AC.norm ctx b) = true → 
Data.AC.eval α ctx a …
· 使用定理 `instAssociativeMin_mathlib`：∀ {α : Type u} [inst : SemilatticeInf α], St
d.Associative fun x1 x2 => x1 ⊓ x2
· 使用定理 `instCommutativeMin_mathlib`：∀ {α : Type u} [inst : SemilatticeInf α], St
d.Commutative fun x1 x2 => x1 ⊓ x2
· 使用定理 `instIdempotentOpMin_mathlib`：∀ {α : Type u} [inst : SemilatticeInf α], S
td.IdempotentOp fun x1 x2 => x1 ⊓ x2
· 使用定理 `instAssociativeMax_mathlib`：∀ {α : Type u} [inst : SemilatticeSup α], St
d.Associative fun x1 x2 => x1 ⊔ x2
· 使用定理 `instCommutativeMax_mathlib`：∀ {α : Type u} [inst : SemilatticeSup α], St
d.Commutative fun x1 x2 => x1 ⊔ x2
· 使用定理 `instIdempotentOpMax_mathlib`：∀ {α : Type u} [inst : SemilatticeSup α], S
td.IdempotentOp fun x1 x2 => x1 ⊔ x2
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sup_inf_right`：sup_inf_right (a b c : α) : a ⊓ b ⊔ c = (a ⊔ c) ⊓ (b ⊔ c)
-/
theorem sdiff_sdiff_sup_sdiff' : z \ (x \ y ⊔ y \ x) = z ⊓ x ⊓ y ⊔ z \ x ⊓ z \ y :=
  calc
    z \ (x \ y ⊔ y \ x) = z \ (x \ y) ⊓ z \ (y \ x) := sdiff_sup
    _ = (z \ x ⊔ z ⊓ x ⊓ y) ⊓ (z \ y ⊔ z ⊓ y ⊓ x) := by rw [sdiff_sdiff_right, sdiff_sdiff_right]
    _ = (z \ x ⊔ z ⊓ y ⊓ x) ⊓ (z \ y ⊔ z ⊓ y ⊓ x) := by ac_rfl
    _ = z \ x ⊓ z \ y ⊔ z ⊓ y ⊓ x := by rw [← sup_inf_right]
    _ = z ⊓ x ⊓ y ⊔ z \ x ⊓ z \ y := by ac_rfl
/-
**sdiff_sdiff_sdiff_cancel_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sdiff_sdiff_sdiff_cancel_left (hca : z <= x) : (x \ y) \ (x \ z) = z \ y
参数：hca : z <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `sdiff_sdiff_sdiff_le_sdiff`：sdiff_sdiff_sdiff_le_sdiff : (a \ b) \ (a \ 
c) <= c \ b
· 使用定理 `Disjoint.le_sdiff_of_le_left`：∀ {α : Type u_2} [inst : GeneralizedCoheyt
ingAlgebra α] {a b c : α}, Disjoint a c → a ≤ b → a ≤ b \ c
· 使用定理 `Disjoint.mono_left`：Disjoint.mono_left (h : a <= b) : Disjoint b c -> Di
sjoint a c
· 使用定理 `sdiff_le`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a b :
 α}, a \ b ≤ a
· 使用定理 `disjoint_sdiff_self_right`：disjoint_sdiff_self_right : Disjoint x (y \ x
)
· 使用定理 `sdiff_le_sdiff_right`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgeb
ra α] {a b c : α}, b ≤ a → b \ c ≤ a \ c
-/
lemma sdiff_sdiff_sdiff_cancel_left (hca : z ≤ x) : (x \ y) \ (x \ z) = z \ y :=
  sdiff_sdiff_sdiff_le_sdiff.antisymm <|
    (disjoint_sdiff_self_right.mono_left sdiff_le).le_sdiff_of_le_left <| sdiff_le_sdiff_right hca
/-
**sdiff_sdiff_sdiff_cancel_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sdiff_sdiff_sdiff_cancel_right (hcb : z <= y) : (x \ z) \ (y \ z) = x \ y
参数：hcb : z <= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `le_antisymm_iff`：le_antisymm_iff : a = b ↔ a <= b ∧ b <= a
· 使用定理 `sdiff_le_comm`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {
a b c : α}, c \ b ≤ a ↔ c \ a ≤ b
· 使用定理 `sdiff_sdiff_sdiff_le_sdiff`：sdiff_sdiff_sdiff_le_sdiff : (a \ b) \ (a \ 
c) <= c \ b
· 使用定理 `Disjoint.le_sdiff_of_le_left`：∀ {α : Type u_2} [inst : GeneralizedCoheyt
ingAlgebra α] {a b c : α}, Disjoint a c → a ≤ b → a ≤ b \ c
· 使用定理 `Disjoint.mono_right`：Disjoint.mono_right (h : b <= c) : Disjoint a c -> 
Disjoint a b
· 使用定理 `sdiff_le`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a b :
 α}, a \ b ≤ a
· 使用定理 `disjoint_sdiff_self_left`：disjoint_sdiff_self_left : Disjoint (y \ x) x
· 使用定理 `sdiff_le_sdiff_left`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebr
a α] {a b c : α}, b ≤ a → c \ a ≤ c \ b
-/
lemma sdiff_sdiff_sdiff_cancel_right (hcb : z ≤ y) : (x \ z) \ (y \ z) = x \ y := by
  rw [le_antisymm_iff, sdiff_le_comm]
  exact ⟨sdiff_sdiff_sdiff_le_sdiff,
    (disjoint_sdiff_self_left.mono_right sdiff_le).le_sdiff_of_le_left <| sdiff_le_sdiff_left hcb⟩
/-
**inf_sdiff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inf_sdiff : (x ⊓ y) \ z = x \ z ⊓ y \ z
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sdiff_unique`：sdiff_unique (s : x ⊓ y ⊔ z = x) (i : x ⊓ y ⊓ z = ⊥) : x \
 y = z
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_inf_left`：sup_inf_left (a b c : α) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c)
· 使用定理 `sup_inf_right`：sup_inf_right (a b c : α) : a ⊓ b ⊔ c = (a ⊔ c) ⊓ (b ⊔ c)
· 使用定理 `sup_sdiff_self_right`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgeb
ra α] (a b : α), a ⊔ b \ a = a ⊔ b
· 使用定理 `inf_sup_right`：inf_sup_right (a b c : α) : (a ⊔ b) ⊓ c = a ⊓ c ⊔ b ⊓ c
· 使用定理 `inf_sdiff_sup_right`：inf_sdiff_sup_right : a \ c ⊓ (b ⊔ a) = a \ c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Lean.Data.AC.Context.eq_of_norm`：∀ {α : Sort u_1} (ctx : Data.AC.Context
 α) (a b : Data.AC.Expr),   (Data.AC.norm ctx a == Data.AC.norm ctx b) = true → 
Data.AC.eval α ctx a …
· 使用定理 `instAssociativeMax_mathlib`：∀ {α : Type u} [inst : SemilatticeSup α], St
d.Associative fun x1 x2 => x1 ⊔ x2
· 使用定理 `instCommutativeMax_mathlib`：∀ {α : Type u} [inst : SemilatticeSup α], St
d.Commutative fun x1 x2 => x1 ⊔ x2
· 使用定理 `instIdempotentOpMax_mathlib`：∀ {α : Type u} [inst : SemilatticeSup α], S
td.IdempotentOp fun x1 x2 => x1 ⊔ x2
· 使用定理 `instAssociativeMin_mathlib`：∀ {α : Type u} [inst : SemilatticeInf α], St
d.Associative fun x1 x2 => x1 ⊓ x2
· 使用定理 `instCommutativeMin_mathlib`：∀ {α : Type u} [inst : SemilatticeInf α], St
d.Commutative fun x1 x2 => x1 ⊓ x2
· 使用定理 `instIdempotentOpMin_mathlib`：∀ {α : Type u} [inst : SemilatticeInf α], S
td.IdempotentOp fun x1 x2 => x1 ⊓ x2
· 使用定理 `inf_sup_self`：inf_sup_self : a ⊓ (a ⊔ b) = a
· 使用定理 `sup_inf_inf_sdiff`：sup_inf_inf_sdiff : x ⊓ y ⊓ z ⊔ y \ z = x ⊓ y ⊔ y \ z
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sup_eq_left`：sup_eq_left : a ⊔ b = a ↔ b <= a
· 使用定理 `inf_le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {a b c d : α}, b ≤ 
a → d ≤ c → b ⊓ d ≤ a ⊓ c
· 使用定理 `sdiff_le`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a b :
 α}, a \ b ≤ a
· 使用定理 `inf_sdiff_self_right`：inf_sdiff_self_right : x ⊓ y \ x = ⊥
· 使用定理 `inf_bot_eq`：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : OrderBo
t α] (a : α), a ⊓ ⊥ = ⊥
· 使用定理 `bot_inf_eq`：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : OrderBo
t α] (a : α), ⊥ ⊓ a = ⊥
-/
theorem inf_sdiff : (x ⊓ y) \ z = x \ z ⊓ y \ z :=
  sdiff_unique
    (calc
      _ = (x ⊓ y ⊓ (z ⊔ x) ⊔ x \ z) ⊓ (x ⊓ y ⊓ z ⊔ y \ z) := by
          rw [sup_inf_left, sup_inf_right, sup_sdiff_self_right, inf_sup_right, inf_sdiff_sup_right]
      _ = (y ⊓ (x ⊓ (x ⊔ z)) ⊔ x \ z) ⊓ (x ⊓ y ⊓ z ⊔ y \ z) := by ac_rfl
      _ = x ⊓ y ⊔ x \ z ⊓ y \ z := by rw [inf_sup_self, sup_inf_inf_sdiff, inf_comm y, sup_inf_left]
      _ = x ⊓ y := sup_eq_left.2 (inf_le_inf sdiff_le sdiff_le))
    (calc
      x ⊓ y ⊓ z ⊓ (x \ z ⊓ y \ z) = x ⊓ y ⊓ (z ⊓ x \ z) ⊓ y \ z := by ac_rfl
      _ = ⊥ := by rw [inf_sdiff_self_right, inf_bot_eq, bot_inf_eq])

/-- See also `sdiff_inf_right_comm`. -/
/-
**inf_sdiff_assoc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inf_sdiff_assoc (x y z : α) : (x ⊓ y) \ z = x ⊓ y \ z
参数：x y z : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sdiff_unique`：sdiff_unique (s : x ⊓ y ⊔ z = x) (i : x ⊓ y ⊓ z = ⊥) : x \
 y = z
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_assoc`：∀ {α : Type u} [inst : SemilatticeInf α] (a b c : α), a ⊓ b ⊓
 c = a ⊓ (b ⊓ c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inf_sup_left`：inf_sup_left (a b c : α) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c
· 使用定理 `sup_inf_sdiff`：sup_inf_sdiff (x y : α) : x ⊓ y ⊔ x \ y = x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Lean.Data.AC.Context.eq_of_norm`：∀ {α : Sort u_1} (ctx : Data.AC.Context
 α) (a b : Data.AC.Expr),   (Data.AC.norm ctx a == Data.AC.norm ctx b) = true → 
Data.AC.eval α ctx a …
· 使用定理 `instAssociativeMin_mathlib`：∀ {α : Type u} [inst : SemilatticeInf α], St
d.Associative fun x1 x2 => x1 ⊓ x2
· 使用定理 `instCommutativeMin_mathlib`：∀ {α : Type u} [inst : SemilatticeInf α], St
d.Commutative fun x1 x2 => x1 ⊓ x2
· 使用定理 `instIdempotentOpMin_mathlib`：∀ {α : Type u} [inst : SemilatticeInf α], S
td.IdempotentOp fun x1 x2 => x1 ⊓ x2
· 使用定理 `inf_inf_sdiff`：inf_inf_sdiff (x y : α) : x ⊓ y ⊓ x \ y = ⊥
· 使用定理 `inf_bot_eq`：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : OrderBo
t α] (a : α), a ⊓ ⊥ = ⊥

--- 原说明 ---
See also `sdiff_inf_right_comm`.
-/
theorem inf_sdiff_assoc (x y z : α) : (x ⊓ y) \ z = x ⊓ y \ z :=
  sdiff_unique (by rw [inf_assoc, ← inf_sup_left, sup_inf_sdiff]) <| calc
    x ⊓ y ⊓ z ⊓ (x ⊓ y \ z) = x ⊓ x ⊓ (y ⊓ z ⊓ y \ z) := by ac_rfl
    _ = ⊥ := by rw [inf_inf_sdiff, inf_bot_eq]

/-- See also `inf_sdiff_assoc`. -/
/-
**sdiff_inf_right_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sdiff_inf_right_comm (x y z : α) : x \ z ⊓ y = (x ⊓ y) \ z
参数：x y z : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `inf_sdiff_assoc`：inf_sdiff_assoc (x y z : α) : (x ⊓ y) \ z = x ⊓ y \ z

--- 原说明 ---
See also `inf_sdiff_assoc`.
-/
theorem sdiff_inf_right_comm (x y z : α) : x \ z ⊓ y = (x ⊓ y) \ z := by
  rw [inf_comm x, inf_comm, inf_sdiff_assoc]
/-
**inf_sdiff_left_comm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：inf_sdiff_left_comm (a b c : α) : a ⊓ (b \ c) = b ⊓ (a \ c)
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inf_sdiff_left_comm (a b c : α) : a ⊓ (b \ c) = b ⊓ (a \ c) := by
  simp_rw [← inf_sdiff_assoc, inf_comm]
/-
**inf_sdiff_distrib_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inf_sdiff_distrib_left (a b c : α) : a ⊓ b \ c = (a ⊓ b) \ (a ⊓ c)
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sdiff_inf`：sdiff_inf : a \ (b ⊓ c) = a \ b ⊔ a \ c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sdiff_eq_bot_iff`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α
] {a b : α}, b \ a = ⊥ ↔ b ≤ a
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `bot_sup_eq`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : OrderBo
t α] (a : α), ⊥ ⊔ a = a
· 使用定理 `inf_sdiff_assoc`：inf_sdiff_assoc (x y z : α) : (x ⊓ y) \ z = x ⊓ y \ z
-/
theorem inf_sdiff_distrib_left (a b c : α) : a ⊓ b \ c = (a ⊓ b) \ (a ⊓ c) := by
  rw [sdiff_inf, (sdiff_eq_bot_iff (α := α)).2 inf_le_left, bot_sup_eq, inf_sdiff_assoc]
/-
**inf_sdiff_distrib_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inf_sdiff_distrib_right (a b c : α) : a \ b ⊓ c = (a ⊓ c) \ (b ⊓ c)
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inf_sdiff_distrib_left`：inf_sdiff_distrib_left (a b c : α) : a ⊓ b \ c =
 (a ⊓ b) \ (a ⊓ c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inf_sdiff_distrib_right (a b c : α) : a \ b ⊓ c = (a ⊓ c) \ (b ⊓ c) := by
  simp_rw [inf_comm _ c, inf_sdiff_distrib_left]
/-
**disjoint_sdiff_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：disjoint_sdiff_comm : Disjoint (x \ z) y ↔ Disjoint x (y \ z)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sdiff_inf_right_comm`：sdiff_inf_right_comm (x y z : α) : x \ z ⊓ y = (x 
⊓ y) \ z
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `inf_sdiff_assoc`：inf_sdiff_assoc (x y z : α) : (x ⊓ y) \ z = x ⊓ y \ z
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem disjoint_sdiff_comm : Disjoint (x \ z) y ↔ Disjoint x (y \ z) := by
  simp_rw [disjoint_iff, sdiff_inf_right_comm, inf_sdiff_assoc]
/-
**sup_eq_sdiff_sup_sdiff_sup_inf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sup_eq_sdiff_sup_sdiff_sup_inf : x ⊔ y = x \ y ⊔ y \ x ⊔ x ⊓ y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_inf_left`：sup_inf_left (a b c : α) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Lean.Data.AC.Context.eq_of_norm`：∀ {α : Sort u_1} (ctx : Data.AC.Context
 α) (a b : Data.AC.Expr),   (Data.AC.norm ctx a == Data.AC.norm ctx b) = true → 
Data.AC.eval α ctx a …
· 使用定理 `instAssociativeMax_mathlib`：∀ {α : Type u} [inst : SemilatticeSup α], St
d.Associative fun x1 x2 => x1 ⊔ x2
· 使用定理 `instCommutativeMax_mathlib`：∀ {α : Type u} [inst : SemilatticeSup α], St
d.Commutative fun x1 x2 => x1 ⊔ x2
· 使用定理 `instIdempotentOpMax_mathlib`：∀ {α : Type u} [inst : SemilatticeSup α], S
td.IdempotentOp fun x1 x2 => x1 ⊔ x2
· 使用定理 `instAssociativeMin_mathlib`：∀ {α : Type u} [inst : SemilatticeInf α], St
d.Associative fun x1 x2 => x1 ⊓ x2
· 使用定理 `instCommutativeMin_mathlib`：∀ {α : Type u} [inst : SemilatticeInf α], St
d.Commutative fun x1 x2 => x1 ⊓ x2
· 使用定理 `instIdempotentOpMin_mathlib`：∀ {α : Type u} [inst : SemilatticeInf α], S
td.IdempotentOp fun x1 x2 => x1 ⊓ x2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `sup_sdiff_self`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] 
(a b : α), a ⊔ b \ a = a ⊔ b
· 使用定理 `sdiff_sup_self`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] 
(a b : α), b \ a ⊔ a = b ⊔ a
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sup_eq_sdiff_sup_sdiff_sup_inf : x ⊔ y = x \ y ⊔ y \ x ⊔ x ⊓ y :=
  Eq.symm <|
    calc
      x \ y ⊔ y \ x ⊔ x ⊓ y = (x \ y ⊔ y \ x ⊔ x) ⊓ (x \ y ⊔ y \ x ⊔ y) := by rw [sup_inf_left]
      _ = (x \ y ⊔ x ⊔ y \ x) ⊓ (x \ y ⊔ (y \ x ⊔ y)) := by ac_rfl
      _ = x ⊔ y := by simp
/-
**sup_lt_of_lt_sdiff_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sup_lt_of_lt_sdiff_left (h : y < z \ x) (hxz : x <= z) : x ⊔ y < z
参数：h : y < z \ x；hxz : x <= z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sup_sdiff_cancel_right`：sup_sdiff_cancel_right (h : a <= b) : a ⊔ b \ a 
= b
· 使用定理 `LE.le.lt_of_not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ 
b → ¬b ≤ a → a < b
· 使用定理 `sup_le_sup_left`：sup_le_sup_left (h₁ : a <= b) (c) : c ⊔ a <= c ⊔ b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `sdiff_idem`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a b
 : α}, (a \ b) \ b = a \ b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `sdiff_le_sdiff_of_sup_le_sup_left`：sdiff_le_sdiff_of_sup_le_sup_left (h 
: c ⊔ a <= c ⊔ b) : a \ c <= b \ c
· 使用定理 `sdiff_le`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a b :
 α}, a \ b ≤ a
-/
theorem sup_lt_of_lt_sdiff_left (h : y < z \ x) (hxz : x ≤ z) : x ⊔ y < z := by
  rw [← sup_sdiff_cancel_right hxz]
  refine (sup_le_sup_left h.le _).lt_of_not_ge fun h' => h.not_ge ?_
  rw [← sdiff_idem]
  exact (sdiff_le_sdiff_of_sup_le_sup_left h').trans sdiff_le
/-
**sup_lt_of_lt_sdiff_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sup_lt_of_lt_sdiff_right (h : x < z \ y) (hyz : y <= z) : x ⊔ y < z
参数：h : x < z \ y；hyz : y <= z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sdiff_sup_cancel`：sdiff_sup_cancel (h : b <= a) : a \ b ⊔ b = a
· 使用引理 `lt_of_le_not_ge`：lt_of_le_not_ge (hab : a <= b) (hba : ¬ b <= a) : a < b
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `sup_le_sup`：sup_le_sup (h₁ : a <= b) (h₂ : c <= d) : a ⊔ c <= b ⊔ d
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `sdiff_idem`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a b
 : α}, (a \ b) \ b = a \ b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `sdiff_le_sdiff_of_sup_le_sup_right`：sdiff_le_sdiff_of_sup_le_sup_right (
h : a ⊔ c <= b ⊔ c) : a \ c <= b \ c
· 使用定理 `sdiff_le`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a b :
 α}, a \ b ≤ a
-/
theorem sup_lt_of_lt_sdiff_right (h : x < z \ y) (hyz : y ≤ z) : x ⊔ y < z := by
  rw [← sdiff_sup_cancel hyz]
  refine lt_of_le_not_ge (by grw [h]) fun h' => h.not_ge ?_
  rw [← sdiff_idem]
  exact (sdiff_le_sdiff_of_sup_le_sup_right h').trans sdiff_le
/-
**Prod.instGeneralizedBooleanAlgebra** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.instGeneralizedBooleanAlgebra [GeneralizedBooleanAlgebra β] : General
izedBooleanAlgebra (α × β) where sup_inf_sdiff _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Prod.instGeneralizedBooleanAlgebra [GeneralizedBooleanAlgebra β] :
    GeneralizedBooleanAlgebra (α × β) where
  sup_inf_sdiff _ _ := Prod.ext (sup_inf_sdiff _ _) (sup_inf_sdiff _ _)
  inf_inf_sdiff _ _ := Prod.ext (inf_inf_sdiff _ _) (inf_inf_sdiff _ _)

-- Porting note: Once `pi_instance` has been ported, this is just `by pi_instance`.
/-
**Pi.instGeneralizedBooleanAlgebra** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.instGeneralizedBooleanAlgebra {ι : Type*} {α : ι -> Type*} [forall i, G
eneralizedBooleanAlgebra (α i)] : GeneralizedBooleanAlgebra (forall i, α i) wher
e sup_inf_sdiff
参数：α i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Pi.instGeneralizedBooleanAlgebra {ι : Type*} {α : ι → Type*}
    [∀ i, GeneralizedBooleanAlgebra (α i)] : GeneralizedBooleanAlgebra (∀ i, α i) where
  sup_inf_sdiff := fun f g => funext fun a => sup_inf_sdiff (f a) (g a)
  inf_inf_sdiff := fun f g => funext fun a => inf_inf_sdiff (f a) (g a)

end GeneralizedBooleanAlgebra


/-!
### Boolean algebras
-/
-- See note [reducible non-instances]
/-- A bounded generalized Boolean algebra is a Boolean algebra. -/
/-
**GeneralizedBooleanAlgebra.toBooleanAlgebra** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：GeneralizedBooleanAlgebra.toBooleanAlgebra [GeneralizedBooleanAlgebra α] [
OrderTop α] : BooleanAlgebra α where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A bounded generalized Boolean algebra is a Boolean algebra.
-/
abbrev GeneralizedBooleanAlgebra.toBooleanAlgebra [GeneralizedBooleanAlgebra α] [OrderTop α] :
    BooleanAlgebra α where
  __ := ‹GeneralizedBooleanAlgebra α›
  __ := GeneralizedBooleanAlgebra.toOrderBot
  __ := ‹OrderTop α›
  compl a := ⊤ \ a
  inf_compl_le_bot _ := disjoint_sdiff_self_right.le_bot
  top_le_sup_compl _ := le_sup_sdiff
  sdiff_eq a b := by
    change _ = a ⊓ (⊤ \ b)
    rw [← inf_sdiff_assoc, inf_top_eq]

section BooleanAlgebra

variable [BooleanAlgebra α]

/-
**inf_compl_eq_bot'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inf_compl_eq_bot' : x ⊓ xᶜ = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bot_unique`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ → a = ⊥
· 使用定理 `BooleanAlgebra.inf_compl_le_bot`：∀ {α : Type u} [self : BooleanAlgebra α
] (x : α), x ⊓ xᶜ ≤ ⊥
-/
theorem inf_compl_eq_bot' : x ⊓ xᶜ = ⊥ :=
  bot_unique <| BooleanAlgebra.inf_compl_le_bot x

@[simp]
/-
**sup_compl_eq_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sup_compl_eq_top : x ⊔ xᶜ = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `top_unique`：top_unique (h : ⊤ <= a) : a = ⊤
· 使用定理 `BooleanAlgebra.top_le_sup_compl`：∀ {α : Type u} [self : BooleanAlgebra α
] (x : α), ⊤ ≤ x ⊔ xᶜ
-/
theorem sup_compl_eq_top : x ⊔ xᶜ = ⊤ :=
  top_unique <| BooleanAlgebra.top_le_sup_compl x

@[simp]
/-
**compl_sup_eq_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compl_sup_eq_top : xᶜ ⊔ x = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `sup_compl_eq_top`：sup_compl_eq_top : x ⊔ xᶜ = ⊤
-/
theorem compl_sup_eq_top : xᶜ ⊔ x = ⊤ := by rw [sup_comm, sup_compl_eq_top]
/-
**isCompl_compl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCompl_compl : IsCompl x xᶜ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompl.of_eq`：of_eq (h₁ : x ⊓ y = ⊥) (h₂ : x ⊔ y = ⊤) : IsCompl x y
· 使用定理 `inf_compl_eq_bot'`：inf_compl_eq_bot' : x ⊓ xᶜ = ⊥
· 使用定理 `sup_compl_eq_top`：sup_compl_eq_top : x ⊔ xᶜ = ⊤
-/
theorem isCompl_compl : IsCompl x xᶜ :=
  IsCompl.of_eq inf_compl_eq_bot' sup_compl_eq_top
/-
**sdiff_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sdiff_eq : x \ y = x ⊓ yᶜ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BooleanAlgebra.sdiff_eq`：∀ {α : Type u} [self : BooleanAlgebra α] (x y :
 α), x \ y = x ⊓ yᶜ
-/
theorem sdiff_eq : x \ y = x ⊓ yᶜ :=
  BooleanAlgebra.sdiff_eq x y
/-
**himp_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：himp_eq : x ⇨ y = y ⊔ xᶜ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BooleanAlgebra.himp_eq`：∀ {α : Type u} [self : BooleanAlgebra α] (x y : 
α), x ⇨ y = y ⊔ xᶜ
-/
theorem himp_eq : x ⇨ y = y ⊔ xᶜ :=
  BooleanAlgebra.himp_eq x y
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) BooleanAlgebra.toComplementedLattice : ComplementedLattice α :=
  ⟨fun x => ⟨xᶜ, isCompl_compl⟩⟩

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) BooleanAlgebra.toGeneralizedBooleanAlgebra :
    GeneralizedBooleanAlgebra α where
  __ := ‹BooleanAlgebra α›
  sup_inf_sdiff a b := by rw [sdiff_eq, ← inf_sup_left, sup_compl_eq_top, inf_top_eq]
  inf_inf_sdiff a b := by
    rw [sdiff_eq, ← inf_inf_distrib_left, inf_compl_eq_bot', inf_bot_eq]

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) BooleanAlgebra.toBiheytingAlgebra : BiheytingAlgebra α where
  __ := ‹BooleanAlgebra α›
  __ := GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra
  hnot := compl
  le_himp_iff a b c := by rw [himp_eq, isCompl_compl.le_sup_right_iff_inf_left_le]
  himp_bot _ := _root_.himp_eq.trans (bot_sup_eq _)
  top_sdiff a := by rw [sdiff_eq, top_inf_eq]

@[simp]
/-
**hnot_eq_compl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hnot_eq_compl : ￢x = xᶜ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hnot_eq_compl : ￢x = xᶜ :=
  rfl

/- NOTE: Is this theorem needed at all or can we use `top_sdiff'`. -/
/-
**top_sdiff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：top_sdiff : ⊤ \ x = xᶜ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `top_sdiff'`：∀ {α : Type u_2} [inst : CoheytingAlgebra α] (a : α), ⊤ \ a 
= ￢a

--- 原说明 ---
NOTE: Is this theorem needed at all or can we use `top_sdiff'`.
-/
theorem top_sdiff : ⊤ \ x = xᶜ :=
  top_sdiff' x
/-
**eq_compl_iff_isCompl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_compl_iff_isCompl : x = yᶜ ↔ IsCompl x y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsCompl.symm`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bounded
Order α] {x y : α}, IsCompl x y → IsCompl y x
· 使用定理 `isCompl_compl`：isCompl_compl : IsCompl x xᶜ
· 使用定理 `IsCompl.eq_compl`：IsCompl.eq_compl (h : IsCompl a b) : a = bᶜ
-/
theorem eq_compl_iff_isCompl : x = yᶜ ↔ IsCompl x y :=
  ⟨fun h => by
    rw [h]
    exact isCompl_compl.symm, IsCompl.eq_compl⟩
/-
**compl_eq_iff_isCompl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compl_eq_iff_isCompl : xᶜ = y ↔ IsCompl x y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isCompl_compl`：isCompl_compl : IsCompl x xᶜ
· 使用定理 `IsCompl.compl_eq`：IsCompl.compl_eq (h : IsCompl a b) : aᶜ = b
-/
theorem compl_eq_iff_isCompl : xᶜ = y ↔ IsCompl x y :=
  ⟨fun h => by
    rw [← h]
    exact isCompl_compl, IsCompl.compl_eq⟩
/-
**compl_eq_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compl_eq_comm : xᶜ = y ↔ yᶜ = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `compl_eq_iff_isCompl`：compl_eq_iff_isCompl : xᶜ = y ↔ IsCompl x y
· 使用定理 `eq_compl_iff_isCompl`：eq_compl_iff_isCompl : x = yᶜ ↔ IsCompl x y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem compl_eq_comm : xᶜ = y ↔ yᶜ = x := by
  rw [eq_comm, compl_eq_iff_isCompl, eq_compl_iff_isCompl]
/-
**eq_compl_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_compl_comm : x = yᶜ ↔ y = xᶜ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `compl_eq_iff_isCompl`：compl_eq_iff_isCompl : xᶜ = y ↔ IsCompl x y
· 使用定理 `eq_compl_iff_isCompl`：eq_compl_iff_isCompl : x = yᶜ ↔ IsCompl x y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem eq_compl_comm : x = yᶜ ↔ y = xᶜ := by
  rw [eq_comm, compl_eq_iff_isCompl, eq_compl_iff_isCompl]

@[simp]
/-
**compl_compl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compl_compl (x : α) : xᶜᶜ = x
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompl.compl_eq`：IsCompl.compl_eq (h : IsCompl a b) : aᶜ = b
· 使用定理 `IsCompl.symm`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bounded
Order α] {x y : α}, IsCompl x y → IsCompl y x
· 使用定理 `isCompl_compl`：isCompl_compl : IsCompl x xᶜ
-/
theorem compl_compl (x : α) : xᶜᶜ = x :=
  (@isCompl_compl _ x _).symm.compl_eq
/-
**compl_comp_compl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compl_comp_compl : compl ∘ compl = @id α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
-/
theorem compl_comp_compl : compl ∘ compl = @id α :=
  funext compl_compl

@[simp]
/-
**compl_involutive** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compl_involutive : Function.Involutive (compl : α -> α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
-/
theorem compl_involutive : Function.Involutive (compl : α → α) :=
  compl_compl
/-
**compl_bijective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compl_bijective : Function.Bijective (compl : α -> α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Involutive.bijective`：∀ {α : Sort u} {f : α → α}, Function.Invo
lutive f → Function.Bijective f
· 使用定理 `compl_involutive`：compl_involutive : Function.Involutive (compl : α -> α
)
-/
theorem compl_bijective : Function.Bijective (compl : α → α) :=
  compl_involutive.bijective
/-
**compl_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compl_surjective : Function.Surjective (compl : α -> α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Involutive.surjective`：∀ {α : Sort u} {f : α → α}, Function.Inv
olutive f → Function.Surjective f
· 使用定理 `compl_involutive`：compl_involutive : Function.Involutive (compl : α -> α
)
-/
theorem compl_surjective : Function.Surjective (compl : α → α) :=
  compl_involutive.surjective
/-
**compl_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compl_injective : Function.Injective (compl : α -> α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Involutive.injective`：∀ {α : Sort u} {f : α → α}, Function.Invo
lutive f → Function.Injective f
· 使用定理 `compl_involutive`：compl_involutive : Function.Involutive (compl : α -> α
)
-/
theorem compl_injective : Function.Injective (compl : α → α) :=
  compl_involutive.injective

@[simp]
/-
**compl_inj_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compl_inj_iff : xᶜ = yᶜ ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `compl_injective`：compl_injective : Function.Injective (compl : α -> α)
-/
theorem compl_inj_iff : xᶜ = yᶜ ↔ x = y :=
  compl_injective.eq_iff
/-
**IsCompl.compl_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompl.compl_eq_iff (h : IsCompl x y) : zᶜ = y ↔ z = x
参数：h : IsCompl x y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `compl_inj_iff`：compl_inj_iff : xᶜ = yᶜ ↔ x = y
· 使用定理 `IsCompl.compl_eq`：IsCompl.compl_eq (h : IsCompl a b) : aᶜ = b
-/
theorem IsCompl.compl_eq_iff (h : IsCompl x y) : zᶜ = y ↔ z = x :=
  h.compl_eq ▸ compl_inj_iff

@[simp]
/-
**compl_eq_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compl_eq_top : xᶜ = ⊤ ↔ x = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompl.compl_eq_iff`：IsCompl.compl_eq_iff (h : IsCompl x y) : zᶜ = y ↔ 
z = x
· 使用定理 `isCompl_bot_top`：isCompl_bot_top : IsCompl (⊥ : α) ⊤
-/
theorem compl_eq_top : xᶜ = ⊤ ↔ x = ⊥ :=
  isCompl_bot_top.compl_eq_iff

@[simp]
/-
**compl_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compl_eq_bot : xᶜ = ⊥ ↔ x = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompl.compl_eq_iff`：IsCompl.compl_eq_iff (h : IsCompl x y) : zᶜ = y ↔ 
z = x
· 使用定理 `isCompl_top_bot`：isCompl_top_bot : IsCompl (⊤ : α) ⊥
-/
theorem compl_eq_bot : xᶜ = ⊥ ↔ x = ⊤ :=
  isCompl_top_bot.compl_eq_iff

@[simp]
/-
**compl_inf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compl_inf : (x ⊓ y)ᶜ = xᶜ ⊔ yᶜ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hnot_inf_distrib`：∀ {α : Type u_2} [inst : CoheytingAlgebra α] (a b : α)
, ￢(a ⊓ b) = ￢a ⊔ ￢b
-/
theorem compl_inf : (x ⊓ y)ᶜ = xᶜ ⊔ yᶜ :=
  hnot_inf_distrib _ _

@[simp]
/-
**compl_le_compl_iff_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compl_le_compl_iff_le : yᶜ <= xᶜ ↔ x <= y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `compl_le_compl`：compl_le_compl (h : a <= b) : bᶜ <= aᶜ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
-/
theorem compl_le_compl_iff_le : yᶜ ≤ xᶜ ↔ x ≤ y :=
  ⟨fun h => by have h := compl_le_compl h; simpa using h, compl_le_compl⟩
/-
**compl_lt_compl_iff_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} {x y : α} [inst : BooleanAlgebra α], yᶜ < xᶜ ↔ x < y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_iff_lt_of_le_iff_le'`：lt_iff_lt_of_le_iff_le' {β} [Preorder α] [Preor
der β] {a b : α} {c d : β} (H : a <= b ↔ c <= d) (H' : b <= a ↔ d <= c) : b < a 
↔ d < c
· 使用定理 `compl_le_compl_iff_le`：compl_le_compl_iff_le : yᶜ <= xᶜ ↔ x <= y
-/
@[simp] lemma compl_lt_compl_iff_lt : yᶜ < xᶜ ↔ x < y :=
  lt_iff_lt_of_le_iff_le' compl_le_compl_iff_le compl_le_compl_iff_le
/-
**compl_le_of_compl_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compl_le_of_compl_le (h : yᶜ <= x) : xᶜ <= y
参数：h : yᶜ <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `compl_le_compl`：compl_le_compl (h : a <= b) : bᶜ <= aᶜ
-/
theorem compl_le_of_compl_le (h : yᶜ ≤ x) : xᶜ ≤ y := by
  simpa only [compl_compl] using compl_le_compl h
/-
**compl_le_iff_compl_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compl_le_iff_compl_le : xᶜ <= y ↔ yᶜ <= x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `compl_le_of_compl_le`：compl_le_of_compl_le (h : yᶜ <= x) : xᶜ <= y
-/
theorem compl_le_iff_compl_le : xᶜ ≤ y ↔ yᶜ ≤ x :=
  ⟨compl_le_of_compl_le, compl_le_of_compl_le⟩
/-
**compl_le_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} {x : α} [inst : BooleanAlgebra α], xᶜ ≤ x ↔ x = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `le_compl_self`：le_compl_self : a <= aᶜ ↔ a = ⊥
-/
@[simp] theorem compl_le_self : xᶜ ≤ x ↔ x = ⊤ := by simpa using le_compl_self (a := xᶜ)
/-
**compl_lt_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} {x : α} [inst : BooleanAlgebra α] [Nontrivial α], xᶜ < x ↔ 
x = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `lt_compl_self`：lt_compl_self [Nontrivial α] : a < aᶜ ↔ a = ⊥
-/
@[simp] theorem compl_lt_self [Nontrivial α] : xᶜ < x ↔ x = ⊤ := by
  simpa using lt_compl_self (a := xᶜ)

@[simp]
/-
**sdiff_compl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sdiff_compl : x \ yᶜ = x ⊓ y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sdiff_eq`：sdiff_eq : x \ y = x ⊓ yᶜ
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
-/
theorem sdiff_compl : x \ yᶜ = x ⊓ y := by rw [sdiff_eq, compl_compl]
/-
**OrderDual.instBooleanAlgebra** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：OrderDual.instBooleanAlgebra : BooleanAlgebra αᵒᵈ where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance OrderDual.instBooleanAlgebra : BooleanAlgebra αᵒᵈ where
  __ := instDistribLattice α
  __ := instHeytingAlgebra
  sdiff_eq _ _ := @himp_eq α _ _ _
  himp_eq _ _ := @sdiff_eq α _ _ _
  inf_compl_le_bot a := (@codisjoint_hnot_right _ _ (ofDual a)).top_le
  top_le_sup_compl a := (@disjoint_compl_right _ _ (ofDual a)).le_bot

@[simp]
/-
**sup_inf_inf_compl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sup_inf_inf_compl : x ⊓ y ⊔ x ⊓ yᶜ = x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sdiff_eq`：sdiff_eq : x \ y = x ⊓ yᶜ
· 使用定理 `sup_inf_sdiff`：sup_inf_sdiff (x y : α) : x ⊓ y ⊔ x \ y = x
-/
theorem sup_inf_inf_compl : x ⊓ y ⊔ x ⊓ yᶜ = x := by rw [← sdiff_eq, sup_inf_sdiff _ _]
/-
**compl_sdiff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compl_sdiff : (x \ y)ᶜ = x ⇨ y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sdiff_eq`：sdiff_eq : x \ y = x ⊓ yᶜ
· 使用定理 `himp_eq`：himp_eq : x ⇨ y = y ⊔ xᶜ
· 使用定理 `compl_inf`：compl_inf : (x ⊓ y)ᶜ = xᶜ ⊔ yᶜ
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
-/
theorem compl_sdiff : (x \ y)ᶜ = x ⇨ y := by
  rw [sdiff_eq, himp_eq, compl_inf, compl_compl, sup_comm]

@[simp]
/-
**compl_himp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compl_himp : (x ⇨ y)ᶜ = x \ y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `compl_sdiff`：compl_sdiff : (x \ y)ᶜ = x ⇨ y
-/
theorem compl_himp : (x ⇨ y)ᶜ = x \ y :=
  @compl_sdiff αᵒᵈ _ _ _
/-
**compl_sdiff_compl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compl_sdiff_compl : xᶜ \ yᶜ = y \ x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sdiff_compl`：sdiff_compl : x \ yᶜ = x ⊓ y
· 使用定理 `sdiff_eq`：sdiff_eq : x \ y = x ⊓ yᶜ
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
-/
theorem compl_sdiff_compl : xᶜ \ yᶜ = y \ x := by rw [sdiff_compl, sdiff_eq, inf_comm]

@[simp]
/-
**compl_himp_compl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compl_himp_compl : xᶜ ⇨ yᶜ = y ⇨ x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `compl_sdiff_compl`：compl_sdiff_compl : xᶜ \ yᶜ = y \ x
-/
theorem compl_himp_compl : xᶜ ⇨ yᶜ = y ⇨ x :=
  @compl_sdiff_compl αᵒᵈ _ _ _
/-
**disjoint_compl_left_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：disjoint_compl_left_iff : Disjoint xᶜ y ↔ y <= x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_compl_iff_disjoint_left`：le_compl_iff_disjoint_left : a <= bᶜ ↔ Disjo
int b a
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem disjoint_compl_left_iff : Disjoint xᶜ y ↔ y ≤ x := by
  rw [← le_compl_iff_disjoint_left, compl_compl]
/-
**disjoint_compl_right_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：disjoint_compl_right_iff : Disjoint x yᶜ ↔ x <= y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_compl_iff_disjoint_right`：le_compl_iff_disjoint_right : a <= bᶜ ↔ Dis
joint a b
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem disjoint_compl_right_iff : Disjoint x yᶜ ↔ x ≤ y := by
  rw [← le_compl_iff_disjoint_right, compl_compl]
/-
**codisjoint_himp_self_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：codisjoint_himp_self_left : Codisjoint (x ⇨ y) x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `disjoint_sdiff_self_left`：disjoint_sdiff_self_left : Disjoint (y \ x) x
-/
theorem codisjoint_himp_self_left : Codisjoint (x ⇨ y) x :=
  @disjoint_sdiff_self_left αᵒᵈ _ _ _
/-
**codisjoint_himp_self_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：codisjoint_himp_self_right : Codisjoint x (x ⇨ y)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `disjoint_sdiff_self_right`：disjoint_sdiff_self_right : Disjoint x (y \ x
)
-/
theorem codisjoint_himp_self_right : Codisjoint x (x ⇨ y) :=
  @disjoint_sdiff_self_right αᵒᵈ _ _ _
/-
**himp_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：himp_le : x ⇨ y <= z ↔ y <= z ∧ Codisjoint x z
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `himp_eq`：himp_eq : x ⇨ y = y ⊔ xᶜ
· 使用定理 `sup_le_iff`：sup_le_iff : a ⊔ b <= c ↔ a <= c ∧ b <= c
· 使用定理 `and_congr_right_iff`：∀ {a b c : Prop}, (a ∧ b ↔ a ∧ c) ↔ a → (b ↔ c)
· 使用定理 `hnot_le_iff_codisjoint_right`：∀ {α : Type u_2} [inst : CoheytingAlgebra 
α] {a b : α}, ￢b ≤ a ↔ Codisjoint b a
-/
theorem himp_le : x ⇨ y ≤ z ↔ y ≤ z ∧ Codisjoint x z := by
  rw [himp_eq, sup_le_iff, and_congr_right_iff]
  exact fun _ => hnot_le_iff_codisjoint_right
/-
**himp_le_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} {x y : α} [inst : BooleanAlgebra α], x ⇨ y ≤ x ↔ x = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `codisjoint_self`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Orde
rTop α] {a : α}, Codisjoint a a ↔ a = ⊤
· 使用定理 `Codisjoint.mono_right`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 
: OrderTop α] {a b c : α}, c ≤ b → Codisjoint a c → Codisjoint a b
· 使用定理 `codisjoint_himp_self_right`：codisjoint_himp_self_right : Codisjoint x (x
 ⇨ y)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
-/
@[simp] lemma himp_le_left : x ⇨ y ≤ x ↔ x = ⊤ :=
  ⟨fun h ↦ codisjoint_self.1 <| codisjoint_himp_self_right.mono_right h, fun h ↦ le_top.trans h.ge⟩
/-
**himp_eq_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} {x y : α} [inst : BooleanAlgebra α], x ⇨ y = x ↔ x = ⊤ ∧ y 
= ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Codisjoint.eq_iff`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Or
derTop α] {a b : α}, Codisjoint a b → (a = b ↔ a = ⊤ ∧ b = ⊤)
· 使用定理 `codisjoint_himp_self_left`：codisjoint_himp_self_left : Codisjoint (x ⇨ y
) x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
@[simp] lemma himp_eq_left : x ⇨ y = x ↔ x = ⊤ ∧ y = ⊤ := by
  rw [codisjoint_himp_self_left.eq_iff]; aesop
/-
**himp_ne_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：himp_ne_right : x ⇨ y != x ↔ x != ⊤ ∨ y != ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `himp_eq_left`：∀ {α : Type u} {x y : α} [inst : BooleanAlgebra α], x ⇨ y 
= x ↔ x = ⊤ ∧ y = ⊤
· 使用定理 `not_and_or`：not_and_or : ¬(a ∧ b) ↔ ¬a ∨ ¬b
-/
lemma himp_ne_right : x ⇨ y ≠ x ↔ x ≠ ⊤ ∨ y ≠ ⊤ := himp_eq_left.not.trans not_and_or
/-
**codisjoint_iff_compl_le_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：codisjoint_iff_compl_le_left : Codisjoint x y ↔ yᶜ <= x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `hnot_le_iff_codisjoint_left`：∀ {α : Type u_2} [inst : CoheytingAlgebra α
] {a b : α}, ￢b ≤ a ↔ Codisjoint a b
-/
lemma codisjoint_iff_compl_le_left : Codisjoint x y ↔ yᶜ ≤ x :=
  hnot_le_iff_codisjoint_left.symm
/-
**codisjoint_iff_compl_le_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：codisjoint_iff_compl_le_right : Codisjoint x y ↔ xᶜ <= y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `hnot_le_iff_codisjoint_right`：∀ {α : Type u_2} [inst : CoheytingAlgebra 
α] {a b : α}, ￢b ≤ a ↔ Codisjoint b a
-/
lemma codisjoint_iff_compl_le_right : Codisjoint x y ↔ xᶜ ≤ y :=
  hnot_le_iff_codisjoint_right.symm

end BooleanAlgebra

/-
**Prod.instBooleanAlgebra** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.instBooleanAlgebra [BooleanAlgebra α] [BooleanAlgebra β] : BooleanAlg
ebra (α × β) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Prod.instBooleanAlgebra [BooleanAlgebra α] [BooleanAlgebra β] :
    BooleanAlgebra (α × β) where
  __ := instDistribLattice α β
  __ := instHeytingAlgebra
  himp_eq x y := by ext <;> simp [himp_eq]
  sdiff_eq x y := by ext <;> simp [sdiff_eq]
  inf_compl_le_bot x := by constructor <;> simp
  top_le_sup_compl x := by constructor <;> simp
/-
**Pi.instBooleanAlgebra** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.instBooleanAlgebra {ι : Type u} {α : ι -> Type v} [forall i, BooleanAlg
ebra (α i)] : BooleanAlgebra (forall i, α i) where __
参数：α i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Pi.instBooleanAlgebra {ι : Type u} {α : ι → Type v} [∀ i, BooleanAlgebra (α i)] :
    BooleanAlgebra (∀ i, α i) where
  __ := instDistribLattice
  __ := instHeytingAlgebra
  sdiff_eq _ _ := funext fun _ => sdiff_eq
  himp_eq _ _ := funext fun _ => himp_eq
  inf_compl_le_bot _ _ := BooleanAlgebra.inf_compl_le_bot _
  top_le_sup_compl _ _ := BooleanAlgebra.top_le_sup_compl _

section lift

-- See note [reducible non-instances]
/-- Pullback a `GeneralizedBooleanAlgebra` along an injection. -/
/-
**Function.Injective.generalizedBooleanAlgebra** 是 Mathlib 中的一个定义，位于命名空间 `Functi
on.Injective`。
形式化陈述：{α : Type u} →   {β : Type u_1} →     [inst : Max α] →       [inst_1 : Min
 α] →         [inst_2 : LE α] →           [inst_3 : LT α] →             [inst_4 
: Bot α] →               [inst_5 : SDiff α] →                 [inst_6 : Generali
zedBooleanAlgebra β] →                   (f : α → β) →                     Funct
ion.Injective f →                       (∀ {x y : α}, f x ≤ f y ↔ x ≤ y) →      
                   (∀ {x y : α}, f x < f y ↔ x < y) →                           
(∀ (a b : α), f (a ⊔ b) = f a ⊔ f b) →                             (∀ (a b : α),
 f (a ⊓ b) = f a ⊓ f b) →                               f ⊥ = ⊥ → (∀ (a b : α), 
f (a \ b) = f a \ f b) → GeneralizedBooleanAlgebra α
参数：f : α → β；∀ {x y : α}, f x ≤ f y ↔ x ≤ y；∀ {x y : α}, f x < f y ↔ x < y；∀ (a 
b : α), f (a ⊔ b) = f a ⊔ f b；∀ (a b : α), f (a ⊓ b) = f a ⊓ f b；∀ (a b : α), f 
(a \ b) = f a \ f b。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `DistribLattice.le_sup_inf`：∀ {α : Type u_1} [self : DistribLattice α] (x
 y z : α), (x ⊔ y) ⊓ (x ⊔ z) ≤ x ⊔ y ⊓ z

--- 原说明 ---
Pullback a `GeneralizedBooleanAlgebra` along an injection.
-/
protected abbrev Function.Injective.generalizedBooleanAlgebra [Max α] [Min α]
    [LE α] [LT α] [Bot α] [SDiff α] [GeneralizedBooleanAlgebra β] (f : α → β) (hf : Injective f)
    (le : ∀ {x y}, f x ≤ f y ↔ x ≤ y) (lt : ∀ {x y}, f x < f y ↔ x < y)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b)
    (map_bot : f ⊥ = ⊥) (map_sdiff : ∀ a b, f (a \ b) = f a \ f b) :
    GeneralizedBooleanAlgebra α where
  __ := hf.generalizedCoheytingAlgebra f le lt map_sup map_inf map_bot map_sdiff
  __ := hf.distribLattice f le lt map_sup map_inf
  sup_inf_sdiff a b := hf <| by rw [map_sup, map_sdiff, map_inf, sup_inf_sdiff]
  inf_inf_sdiff a b := hf <| by rw [map_inf, map_sdiff, map_inf, inf_inf_sdiff, map_bot]

-- See note [reducible non-instances]
/-- Pullback a `BooleanAlgebra` along an injection. -/
/-
**Function.Injective.booleanAlgebra** 是 Mathlib 中的一个定义，位于命名空间 `Function.Injectiv
e`。
形式化陈述：{α : Type u} →   {β : Type u_1} →     [inst : Max α] →       [inst_1 : Min
 α] →         [inst_2 : LE α] →           [inst_3 : LT α] →             [inst_4 
: Top α] →               [inst_5 : Bot α] →                 [inst_6 : Compl α] →
                   [inst_7 : SDiff α] →                     [inst_8 : HImp α] → 
                      [inst_9 : BooleanAlgebra β] →                         (f :
 α → β) →                           Function.Injective f →                      
       (∀ {x y : α}, f x ≤ f y ↔ x ≤ y) →                               (∀ {x y 
: α}, f x < f y ↔ x < y) →                                 (∀ (a b : α), f (a ⊔ 
b) = f a ⊔ f b) →                                   (∀ (a b : α), f (a ⊓ b) = f 
a ⊓ f b) →                                     f ⊤ = ⊤ →                        
               f ⊥ = ⊥ →                                         (∀ (a : α), f a
ᶜ = (f a)ᶜ) →                                           (∀ (a b : α), f (a \ b) 
= f a \ f b) →                                             (∀ (a b : α), f (a ⇨ 
b) = f a ⇨ f b) → BooleanAlgebra α
参数：f : α → β；∀ {x y : α}, f x ≤ f y ↔ x ≤ y；∀ {x y : α}, f x < f y ↔ x < y；∀ (a 
b : α), f (a ⊔ b) = f a ⊔ f b；∀ (a b : α), f (a ⊓ b) = f a ⊓ f b；∀ (a : α), f aᶜ
 = (f a)ᶜ；∀ (a b : α), f (a \ b) = f a \ f b；∀ (a b : α), f (a ⇨ b) = f a ⇨ f b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pullback a `BooleanAlgebra` along an injection.
-/
protected abbrev Function.Injective.booleanAlgebra [Max α] [Min α] [LE α] [LT α] [Top α] [Bot α]
    [Compl α] [SDiff α] [HImp α] [BooleanAlgebra β] (f : α → β) (hf : Injective f)
    (le : ∀ {x y}, f x ≤ f y ↔ x ≤ y) (lt : ∀ {x y}, f x < f y ↔ x < y)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b)
    (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) (map_compl : ∀ a, f aᶜ = (f a)ᶜ)
    (map_sdiff : ∀ a b, f (a \ b) = f a \ f b) (map_himp : ∀ a b, f (a ⇨ b) = f a ⇨ f b) :
    BooleanAlgebra α where
  __ := hf.generalizedBooleanAlgebra f le lt map_sup map_inf map_bot map_sdiff
  le_top _ := le.1 <| (@le_top β _ _ _).trans map_top.ge
  bot_le _ := le.1 <| map_bot.le.trans bot_le
  inf_compl_le_bot a := le.1 ((map_inf _ _).trans <| by
    rw [map_compl, inf_compl_eq_bot, map_bot]).le
  top_le_sup_compl a := le.1 ((map_sup _ _).trans <| by
    rw [map_compl, sup_compl_eq_top, map_top]).ge
  sdiff_eq a b := hf <| (map_sdiff _ _).trans <| sdiff_eq.trans <| by rw [map_inf, map_compl]
  himp_eq a b := hf <| (map_himp _ _).trans <| himp_eq.trans <| by rw [map_sup, map_compl]

namespace Equiv

variable (e : α ≃ β)

/-- Transfer `GeneralizedBooleanAlgebra` across an `Equiv`. -/
/-
**Equiv.generalizedBooleanAlgebra** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u} → {β : Type u_1} → α ≃ β → [GeneralizedBooleanAlgebra β] → Ge
neralizedBooleanAlgebra α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e

--- 原说明 ---
Transfer `GeneralizedBooleanAlgebra` across an `Equiv`.
-/
protected abbrev generalizedBooleanAlgebra [GeneralizedBooleanAlgebra β] :
    GeneralizedBooleanAlgebra α := by
  let bot := e.bot
  let sdiff := e.sdiff
  let distribLattice := e.distribLattice
  apply e.injective.generalizedBooleanAlgebra <;> intros <;>
  first | rfl | exact e.apply_symm_apply _

/-- Transfer `BooleanAlgebra` across an `Equiv`. -/
/-
**Equiv.booleanAlgebra** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u} → {β : Type u_1} → α ≃ β → [BooleanAlgebra β] → BooleanAlgebr
a α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e

--- 原说明 ---
Transfer `BooleanAlgebra` across an `Equiv`.
-/
protected abbrev booleanAlgebra [BooleanAlgebra β] : BooleanAlgebra α := by
  let top := e.top
  let compl := e.compl
  let himp := e.himp
  let generalizedBooleanAlgebra := e.generalizedBooleanAlgebra
  apply e.injective.booleanAlgebra <;> intros <;> first | rfl | exact e.apply_symm_apply _

end Equiv

end lift

