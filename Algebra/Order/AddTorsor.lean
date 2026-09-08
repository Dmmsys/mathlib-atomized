/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Order.Monoid.Defs

/-!
# Ordered scalar multiplication and vector addition

This file defines ordered scalar multiplication and vector addition, and proves some properties.
In the additive case, a motivating example is given by the additive action of `ℤ` on subsets of
reals that are closed under integer translation.  The order compatibility allows for a treatment of
the `R((z))`-module structure on `(z ^ s) V((z))` for an `R`-module `V`, using the formalism of Hahn
series.  In the multiplicative case, a standard example is the action of non-negative rationals on
an ordered field.

## Implementation notes
* Because these classes mix the algebra and order hierarchies, we write them as `Prop`-valued
  mixins.
* Despite the file name, Ordered AddTorsors are not defined as a separate class.  To implement them,
  combine `[AddTorsor G P]` with `[IsOrderedCancelVAdd G P]`

## Definitions
* IsOrderedSMul : inequalities are preserved by scalar multiplication.
* IsOrderedVAdd : inequalities are preserved by translation.
* IsCancelSMul : the scalar multiplication version of cancellative multiplication
* IsCancelVAdd : the vector addition version of cancellative addition
* IsOrderedCancelSMul : inequalities are preserved and reflected by scalar multiplication.
* IsOrderedCancelVAdd : inequalities are preserved and reflected by translation.

## Instances
* `IsOrderedMonoid.toIsOrderedSMul`
* `IsOrderedAddMonoid.toIsOrderedVAdd`
* `IsOrderedSMul.toCovariantClassLeft`
* `IsOrderedVAdd.toCovariantClassLeft`
* `IsOrderedCancelSMul.toCancelSMul`
* `IsOrderedCancelVAdd.toCancelVAdd`
* `IsOrderedCancelMonoid.toIsOrderedCancelSMul`
* `IsOrderedCancelAddMonoid.toIsOrderedCancelVAdd`
* `IsOrderedCancelSMul.toContravariantClassLeft`
* `IsOrderedCancelVAdd.toContravariantClassLeft`

## TODO
* (lex) prod instances
* Pi instances
* WithTop (in a different file?)
-/

public section

open Function

variable {G P : Type*}

/-- An ordered vector addition is a bi-monotone vector addition. -/
/-
**IsOrderedVAdd** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(G : Type u_3) → (P : Type u_4) → [LE G] → [LE P] → [VAdd G P] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An ordered vector addition is a bi-monotone vector addition.
-/
class IsOrderedVAdd (G P : Type*) [LE G] [LE P] [VAdd G P] : Prop where
  protected vadd_le_vadd_left : ∀ a b : P, a ≤ b → ∀ c : G, c +ᵥ a ≤ c +ᵥ b
  protected vadd_le_vadd_right : ∀ c d : G, c ≤ d → ∀ a : P, c +ᵥ a ≤ d +ᵥ a

/-- An ordered scalar multiplication is a bi-monotone scalar multiplication. Note that this is
different from `IsOrderedModule` whose defining conditions are restricted to nonnegative elements.
-/
@[to_additive]
/-
**IsOrderedSMul** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(G : Type u_3) → (P : Type u_4) → [LE G] → [LE P] → [SMul G P] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An ordered scalar multiplication is a bi-monotone scalar multiplication. Note th
at this is
different from `IsOrderedModule` whose defining conditions are restricted to non
negative elements.
-/
class IsOrderedSMul (G P : Type*) [LE G] [LE P] [SMul G P] : Prop where
  protected smul_le_smul_left : ∀ a b : P, a ≤ b → ∀ c : G, c • a ≤ c • b
  protected smul_le_smul_right : ∀ c d : G, c ≤ d → ∀ a : P, c • a ≤ d • a

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LE G] [LE P] [SMul G P] [IsOrderedSMul G P] : CovariantClass G P (· • ·) (· ≤ ·) where
  elim := fun a _ _ bc ↦ IsOrderedSMul.smul_le_smul_left _ _ bc a

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CommMonoid G] [Preorder G] [IsOrderedMonoid G] : IsOrderedSMul G G where
  smul_le_smul_left _ _ := mul_le_mul_right
  smul_le_smul_right _ _ := mul_le_mul_left

@[to_additive (attr := gcongr)]
/-
**IsOrderedSMul.smul_le_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOrderedSMul.smul_le_smul [LE G] [Preorder P] [SMul G P] [IsOrderedSMul G
 P] {a b : G} {c d : P} (hab : a <= b) (hcd : c <= d) : a • c <= b • d
参数：hab : a <= b；hcd : c <= d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `IsOrderedSMul.smul_le_smul_left`：∀ {G : Type u_3} {P : Type u_4} {inst :
 LE G} {inst_1 : LE P} {inst_2 : SMul G P} [self : IsOrderedSMul G P] (a b : P),
   a ≤ b → ∀ (c : G),…
· 使用定理 `IsOrderedSMul.smul_le_smul_right`：∀ {G : Type u_3} {P : Type u_4} {inst 
: LE G} {inst_1 : LE P} {inst_2 : SMul G P} [self : IsOrderedSMul G P] (c d : G)
,   c ≤ d → ∀ (a : P),…
-/
theorem IsOrderedSMul.smul_le_smul [LE G] [Preorder P] [SMul G P] [IsOrderedSMul G P]
    {a b : G} {c d : P} (hab : a ≤ b) (hcd : c ≤ d) : a • c ≤ b • d :=
  (IsOrderedSMul.smul_le_smul_left _ _ hcd _).trans (IsOrderedSMul.smul_le_smul_right _ _ hab _)

@[to_additive]
/-
**Monotone.smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.smul {γ : Type*} [Preorder G] [Preorder P] [Preorder γ] [SMul G P
] [IsOrderedSMul G P] {f : γ -> G} {g : γ -> P} (hf : Monotone f) (hg : Monotone
 g) : Monotone fun x => f x • g x
参数：hf : Monotone f；hg : Monotone g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `IsOrderedSMul.smul_le_smul_left`：∀ {G : Type u_3} {P : Type u_4} {inst :
 LE G} {inst_1 : LE P} {inst_2 : SMul G P} [self : IsOrderedSMul G P] (a b : P),
   a ≤ b → ∀ (c : G),…
· 使用定理 `IsOrderedSMul.smul_le_smul_right`：∀ {G : Type u_3} {P : Type u_4} {inst 
: LE G} {inst_1 : LE P} {inst_2 : SMul G P} [self : IsOrderedSMul G P] (c d : G)
,   c ≤ d → ∀ (a : P),…
-/
theorem Monotone.smul {γ : Type*} [Preorder G] [Preorder P] [Preorder γ] [SMul G P]
    [IsOrderedSMul G P] {f : γ → G} {g : γ → P} (hf : Monotone f) (hg : Monotone g) :
    Monotone fun x => f x • g x :=
  fun _ _ hab => (IsOrderedSMul.smul_le_smul_left _ _ (hg hab) _).trans
    (IsOrderedSMul.smul_le_smul_right _ _ (hf hab) _)

/-- An ordered cancellative vector addition is an ordered vector addition that is cancellative. -/
/-
**IsOrderedCancelVAdd** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(G : Type u_3) → (P : Type u_4) → [LE G] → [LE P] → [VAdd G P] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An ordered cancellative vector addition is an ordered vector addition that is ca
ncellative.
-/
class IsOrderedCancelVAdd (G P : Type*) [LE G] [LE P] [VAdd G P] : Prop
    extends IsOrderedVAdd G P where
  protected le_of_vadd_le_vadd_left : ∀ (a : G) (b c : P), a +ᵥ b ≤ a +ᵥ c → b ≤ c
  protected le_of_vadd_le_vadd_right : ∀ (a b : G) (c : P), a +ᵥ c ≤ b +ᵥ c → a ≤ b

/-- An ordered cancellative scalar multiplication is an ordered scalar multiplication that is
  cancellative. -/
@[to_additive]
/-
**IsOrderedCancelSMul** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(G : Type u_3) → (P : Type u_4) → [LE G] → [LE P] → [SMul G P] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An ordered cancellative scalar multiplication is an ordered scalar multiplicatio
n that is
  cancellative.
-/
class IsOrderedCancelSMul (G P : Type*) [LE G] [LE P] [SMul G P] : Prop
    extends IsOrderedSMul G P where
  protected le_of_smul_le_smul_left : ∀ (a : G) (b c : P), a • b ≤ a • c → b ≤ c
  protected le_of_smul_le_smul_right : ∀ (a b : G) (c : P), a • c ≤ b • c → a ≤ b

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [PartialOrder G] [PartialOrder P] [SMul G P] [IsOrderedCancelSMul G P] :
    IsCancelSMul G P where
  left_cancel' a b c h := (IsOrderedCancelSMul.le_of_smul_le_smul_left a b c h.le).antisymm
    (IsOrderedCancelSMul.le_of_smul_le_smul_left a c b h.ge)
  right_cancel' a b c h := (IsOrderedCancelSMul.le_of_smul_le_smul_right a b c h.le).antisymm
    (IsOrderedCancelSMul.le_of_smul_le_smul_right b a c h.ge)

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CommMonoid G] [Preorder G] [IsOrderedCancelMonoid G] : IsOrderedCancelSMul G G where
  le_of_smul_le_smul_left _ _ _ := le_of_mul_le_mul_left'
  le_of_smul_le_smul_right _ _ _ := le_of_mul_le_mul_right'

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 200) [LE G] [LE P] [SMul G P] [IsOrderedCancelSMul G P] :
    ContravariantClass G P (· • ·) (· ≤ ·) :=
  ⟨IsOrderedCancelSMul.le_of_smul_le_smul_left⟩

namespace SMul

@[to_additive]
/-
**SMul.smul_lt_smul_of_le_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `SMul`。
形式化陈述：smul_lt_smul_of_le_of_lt [LE G] [Preorder P] [SMul G P] [IsOrderedCancelSM
ul G P] {a b : G} {c d : P} (h₁ : a <= b) (h₂ : c < d) : a • c < b • d
参数：h₁ : a <= b；h₂ : c < d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `IsOrderedSMul.smul_le_smul_right`：∀ {G : Type u_3} {P : Type u_4} {inst 
: LE G} {inst_1 : LE P} {inst_2 : SMul G P} [self : IsOrderedSMul G P] (c d : G)
,   c ≤ d → ∀ (a : P),…
· 使用定理 `IsOrderedCancelSMul.toIsOrderedSMul`：∀ {G : Type u_3} {P : Type u_4} {in
st : LE G} {inst_1 : LE P} {inst_2 : SMul G P} [self : IsOrderedCancelSMul G P],
   IsOrderedSMul G P
· 使用引理 `lt_of_le_not_ge`：lt_of_le_not_ge (hab : a <= b) (hba : ¬ b <= a) : a < b
· 使用定理 `IsOrderedSMul.smul_le_smul_left`：∀ {G : Type u_3} {P : Type u_4} {inst :
 LE G} {inst_1 : LE P} {inst_2 : SMul G P} [self : IsOrderedSMul G P] (a b : P),
   a ≤ b → ∀ (c : G),…
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `IsOrderedCancelSMul.le_of_smul_le_smul_left`：∀ {G : Type u_3} {P : Type 
u_4} {inst : LE G} {inst_1 : LE P} {inst_2 : SMul G P} [self : IsOrderedCancelSM
ul G P]   (a : G) (b c : P), a • …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用引理 `lt_iff_le_not_ge`：lt_iff_le_not_ge : a < b ↔ a <= b ∧ ¬b <= a
-/
theorem smul_lt_smul_of_le_of_lt [LE G] [Preorder P] [SMul G P] [IsOrderedCancelSMul G P]
    {a b : G} {c d : P} (h₁ : a ≤ b) (h₂ : c < d) :
    a • c < b • d := by
  refine lt_of_le_of_lt (IsOrderedSMul.smul_le_smul_right a b h₁ c) ?_
  refine lt_of_le_not_ge (IsOrderedSMul.smul_le_smul_left c d (le_of_lt h₂) b) ?_
  by_contra hbdc
  have h : d ≤ c := IsOrderedCancelSMul.le_of_smul_le_smul_left b d c hbdc
  rw [@lt_iff_le_not_ge] at h₂
  simp_all only [not_true_eq_false, and_false]

@[to_additive]
/-
**SMul.smul_lt_smul_of_lt_of_le** 是 Mathlib 中的一个定理，位于命名空间 `SMul`。
形式化陈述：smul_lt_smul_of_lt_of_le [Preorder G] [Preorder P] [SMul G P] [IsOrderedCa
ncelSMul G P] {a b : G} {c d : P} (h₁ : a < b) (h₂ : c <= d) : a • c < b • d
参数：h₁ : a < b；h₂ : c <= d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `IsOrderedSMul.smul_le_smul_left`：∀ {G : Type u_3} {P : Type u_4} {inst :
 LE G} {inst_1 : LE P} {inst_2 : SMul G P} [self : IsOrderedSMul G P] (a b : P),
   a ≤ b → ∀ (c : G),…
· 使用定理 `IsOrderedCancelSMul.toIsOrderedSMul`：∀ {G : Type u_3} {P : Type u_4} {in
st : LE G} {inst_1 : LE P} {inst_2 : SMul G P} [self : IsOrderedCancelSMul G P],
   IsOrderedSMul G P
· 使用引理 `lt_of_le_not_ge`：lt_of_le_not_ge (hab : a <= b) (hba : ¬ b <= a) : a < b
· 使用定理 `IsOrderedSMul.smul_le_smul_right`：∀ {G : Type u_3} {P : Type u_4} {inst 
: LE G} {inst_1 : LE P} {inst_2 : SMul G P} [self : IsOrderedSMul G P] (c d : G)
,   c ≤ d → ∀ (a : P),…
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `IsOrderedCancelSMul.le_of_smul_le_smul_right`：∀ {G : Type u_3} {P : Type
 u_4} {inst : LE G} {inst_1 : LE P} {inst_2 : SMul G P} [self : IsOrderedCancelS
Mul G P]   (a b : G) (c : P), a • …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用引理 `lt_iff_le_not_ge`：lt_iff_le_not_ge : a < b ↔ a <= b ∧ ¬b <= a
-/
theorem smul_lt_smul_of_lt_of_le [Preorder G] [Preorder P] [SMul G P] [IsOrderedCancelSMul G P]
    {a b : G} {c d : P} (h₁ : a < b) (h₂ : c ≤ d) : a • c < b • d := by
  refine lt_of_le_of_lt (IsOrderedSMul.smul_le_smul_left c d h₂ a) ?_
  refine lt_of_le_not_ge (IsOrderedSMul.smul_le_smul_right a b (le_of_lt h₁) d) ?_
  by_contra hbad
  have h : b ≤ a := IsOrderedCancelSMul.le_of_smul_le_smul_right b a d hbad
  rw [@lt_iff_le_not_ge] at h₁
  simp_all only [not_true_eq_false, and_false]

end SMul

