/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johan Commelin
-/
module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Option.Basic
public import Mathlib.Logic.Nontrivial.Basic
public import Mathlib.Tactic.Common

/-!
# Adjoining a zero/one to semigroups and related algebraic structures

This file contains different results about adjoining an element to an algebraic structure which then
behaves like a zero or a one. An example is adjoining a one to a semigroup to obtain a monoid. That
this provides an example of an adjunction is proved in
`Mathlib/Algebra/Category/MonCat/Adjunctions.lean`.

Another result says that adjoining to a group an element `zero` gives a `GroupWithZero`. For more
information about these structures (which are not that standard in informal mathematics, see
`Mathlib/Algebra/GroupWithZero/Basic.lean`)

## TODO

`WithOne.coe_mul` and `WithZero.coe_mul` have inconsistent use of implicit parameters
-/

@[expose] public section

-- Check that we haven't needed to import all the basic lemmas about groups,
-- by asserting a random sample don't exist here:
assert_not_exists inv_involutive div_right_inj pow_ite MonoidWithZero DenselyOrdered

universe u v w

variable {α : Type u}

/-- Add an extra element `1` to a type -/
@[to_additive /-- Add an extra element `0` to a type -/]
/-
**WithOne** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：WithOne (α)
参数：α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Add an extra element `1` to a type
-/
def WithOne (α) :=
  Option α
/-
**WithZero.instRepr** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：WithZero.instRepr [Repr α] : Repr (WithZero α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance WithZero.instRepr [Repr α] : Repr (WithZero α) :=
  ⟨fun o _ =>
    match o with
    | none => "0"
    | some a => "↑" ++ repr a⟩

namespace WithOne

@[to_additive existing]
/-
**WithOne.** 是 Mathlib 中的一个实例，位于命名空间 `WithOne`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Repr α] : Repr (WithOne α) :=
  ⟨fun o _ =>
    match o with
    | none => "1"
    | some a => "↑" ++ repr a⟩

@[to_additive]
/-
**WithOne.instMonad** 是 Mathlib 中的一个实例，位于命名空间 `WithOne`。
形式化陈述：instMonad : Monad WithOne
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMonad : Monad WithOne :=
  inferInstanceAs <| Monad Option

@[to_additive]
/-
**WithOne.instOne** 是 Mathlib 中的一个实例，位于命名空间 `WithOne`。
形式化陈述：instOne : One (WithOne α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instOne : One (WithOne α) :=
  ⟨none⟩

@[to_additive]
/-
**WithOne.instMul** 是 Mathlib 中的一个实例，位于命名空间 `WithOne`。
形式化陈述：instMul [Mul α] : Mul (WithOne α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMul [Mul α] : Mul (WithOne α) :=
  ⟨Option.merge (· * ·)⟩

@[to_additive]
/-
**WithOne.instInv** 是 Mathlib 中的一个实例，位于命名空间 `WithOne`。
形式化陈述：instInv [Inv α] : Inv (WithOne α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInv [Inv α] : Inv (WithOne α) :=
  ⟨fun a => Option.map Inv.inv a⟩

@[to_additive]
/-
**WithOne.instInvOneClass** 是 Mathlib 中的一个实例，位于命名空间 `WithOne`。
形式化陈述：instInvOneClass [Inv α] : InvOneClass (WithOne α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInvOneClass [Inv α] : InvOneClass (WithOne α) :=
  { WithOne.instOne, WithOne.instInv with inv_one := rfl }

@[to_additive]
/-
**WithOne.inhabited** 是 Mathlib 中的一个实例，位于命名空间 `WithOne`。
形式化陈述：inhabited : Inhabited (WithOne α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inhabited : Inhabited (WithOne α) :=
  ⟨1⟩

@[to_additive]
/-
**WithOne.instNontrivial** 是 Mathlib 中的一个实例，位于命名空间 `WithOne`。
形式化陈述：instNontrivial [Nonempty α] : Nontrivial (WithOne α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNontrivial [Nonempty α] : Nontrivial (WithOne α) :=
  Option.nontrivial

@[to_additive]
/-
**WithOne.** 是 Mathlib 中的一个实例，位于命名空间 `WithOne`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsEmpty α] : Subsingleton (WithOne α) :=
  inferInstanceAs <| Subsingleton (Option α)

/-- The canonical map from `α` into `WithOne α` -/
@[to_additive (attr := coe, match_pattern) /-- The canonical map from `α` into `WithZero α` -/]
/-
**WithOne.coe** 是 Mathlib 中的一个定义，位于命名空间 `WithOne`。
形式化陈述：coe : α -> WithOne α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map from `α` into `WithOne α`
-/
def coe : α → WithOne α :=
  Option.some

@[to_additive]
/-
**WithOne.instCoeTC** 是 Mathlib 中的一个实例，位于命名空间 `WithOne`。
形式化陈述：instCoeTC : CoeTC α (WithOne α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCoeTC : CoeTC α (WithOne α) :=
  ⟨coe⟩

@[to_additive]
/-
**WithOne.** 是 Mathlib 中的一个引理，位于命名空间 `WithOne`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma «forall» {p : WithOne α → Prop} : (∀ x, p x) ↔ p 1 ∧ ∀ a : α, p a := Option.forall

@[to_additive]
/-
**WithOne.** 是 Mathlib 中的一个引理，位于命名空间 `WithOne`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma «exists» {p : WithOne α → Prop} : (∃ x, p x) ↔ p 1 ∨ ∃ a : α, p a := Option.exists

/-- Recursor for `WithZero` using the preferred forms `0` and `↑a`. -/
@[elab_as_elim, induction_eliminator, cases_eliminator]
/-
**WithOne._root_.WithZero.recZeroCoe** 是 Mathlib 中的一个定义，位于命名空间 `WithOne`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Recursor for `WithZero` using the preferred forms `0` and `↑a`.
-/
def _root_.WithZero.recZeroCoe {motive : WithZero α → Sort*} (zero : motive 0)
    (coe : ∀ a : α, motive a) : ∀ n : WithZero α, motive n
  | Option.none => zero
  | Option.some x => coe x

/-- Recursor for `WithOne` using the preferred forms `1` and `↑a`. -/
@[to_additive existing, elab_as_elim, induction_eliminator, cases_eliminator]
/-
**WithOne.recOneCoe** 是 Mathlib 中的一个定义，位于命名空间 `WithOne`。
形式化陈述：{α : Type u} → {motive : WithOne α → Sort u_1} → motive 1 → ((a : α) → mot
ive ↑a) → (n : WithOne α) → motive n
参数：(a : α) → motive ↑a；n : WithOne α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Recursor for `WithOne` using the preferred forms `1` and `↑a`.
-/
def recOneCoe {motive : WithOne α → Sort*} (one : motive 1) (coe : ∀ a : α, motive a) :
    ∀ n : WithOne α, motive n
  | Option.none => one
  | Option.some x => coe x

@[to_additive (attr := simp)]
/-
**WithOne.recOneCoe_one** 是 Mathlib 中的一个引理，位于命名空间 `WithOne`。
形式化陈述：recOneCoe_one {motive : WithOne α -> Sort*} (h₁ h₂) : recOneCoe h₁ h₂ (1 :
 WithOne α) = (h₁ : motive 1)
参数：h₁ h₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma recOneCoe_one {motive : WithOne α → Sort*} (h₁ h₂) :
    recOneCoe h₁ h₂ (1 : WithOne α) = (h₁ : motive 1) :=
  rfl

@[to_additive (attr := simp)]
/-
**WithOne.recOneCoe_coe** 是 Mathlib 中的一个引理，位于命名空间 `WithOne`。
形式化陈述：recOneCoe_coe {motive : WithOne α -> Sort*} (h₁ h₂) (a : α) : recOneCoe h₁
 h₂ (a : WithOne α) = (h₂ : forall a : α, motive a) a
参数：h₁ h₂；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma recOneCoe_coe {motive : WithOne α → Sort*} (h₁ h₂) (a : α) :
    recOneCoe h₁ h₂ (a : WithOne α) = (h₂ : ∀ a : α, motive a) a :=
  rfl

/-- Deconstruct an `x : WithOne α` to the underlying value in `α`, given a proof that `x ≠ 1`. -/
@[to_additive
/-- Deconstruct an `x : WithZero α` to the underlying value in `α`, given a proof that `x ≠ 0`. -/]
/-
**WithOne.unone** 是 Mathlib 中的一个定义，位于命名空间 `WithOne`。
形式化陈述：{α : Type u} → {x : WithOne α} → x ≠ 1 → α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def unone : ∀ {x : WithOne α}, x ≠ 1 → α | (x : α), _ => x

@[to_additive (attr := simp)]
/-
**WithOne.unone_coe** 是 Mathlib 中的一个定理，位于命名空间 `WithOne`。
形式化陈述：unone_coe {x : α} (hx : (x : WithOne α) != 1) : unone hx = x
参数：hx : (x : WithOne α) != 1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unone_coe {x : α} (hx : (x : WithOne α) ≠ 1) : unone hx = x :=
  rfl

@[to_additive (attr := simp)]
/-
**WithOne.coe_unone** 是 Mathlib 中的一个定理，位于命名空间 `WithOne`。
形式化陈述：∀ {α : Type u} {x : WithOne α} (hx : x ≠ 1), ↑(WithOne.unone hx) = x
参数：hx : x ≠ 1；WithOne.unone hx。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_unone : ∀ {x : WithOne α} (hx : x ≠ 1), unone hx = x
  | (x : α), _ => rfl

@[to_additive (attr := simp)]
/-
**WithOne.coe_ne_one** 是 Mathlib 中的一个定理，位于命名空间 `WithOne`。
形式化陈述：coe_ne_one {a : α} : (a : WithOne α) != (1 : WithOne α)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Option.some_ne_none`：∀ {α : Type u_1} (x : α), some x ≠ none
-/
theorem coe_ne_one {a : α} : (a : WithOne α) ≠ (1 : WithOne α) :=
  Option.some_ne_none a

@[to_additive (attr := simp)]
/-
**WithOne.one_ne_coe** 是 Mathlib 中的一个定理，位于命名空间 `WithOne`。
形式化陈述：one_ne_coe {a : α} : (1 : WithOne α) != a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `WithOne.coe_ne_one`：coe_ne_one {a : α} : (a : WithOne α) != (1 : WithOne
 α)
-/
theorem one_ne_coe {a : α} : (1 : WithOne α) ≠ a :=
  coe_ne_one.symm

@[to_additive]
/-
**WithOne.ne_one_iff_exists** 是 Mathlib 中的一个定理，位于命名空间 `WithOne`。
形式化陈述：ne_one_iff_exists {x : WithOne α} : x != 1 ↔ exists a : α, ↑a = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Option.ne_none_iff_exists`：∀ {α : Type u_1} {o : Option α}, o ≠ none ↔ ∃
 x, some x = o
-/
theorem ne_one_iff_exists {x : WithOne α} : x ≠ 1 ↔ ∃ a : α, ↑a = x :=
  Option.ne_none_iff_exists

@[to_additive]
/-
**WithOne.instCanLift** 是 Mathlib 中的一个实例，位于命名空间 `WithOne`。
形式化陈述：instCanLift : CanLift (WithOne α) α (↑) fun a => a != 1 where prf _
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `WithOne.ne_one_iff_exists`：ne_one_iff_exists {x : WithOne α} : x != 1 ↔ 
exists a : α, ↑a = x
-/
instance instCanLift : CanLift (WithOne α) α (↑) fun a => a ≠ 1 where
  prf _ := ne_one_iff_exists.1

@[to_additive (attr := simp, norm_cast)]
/-
**WithOne.coe_inj** 是 Mathlib 中的一个定理，位于命名空间 `WithOne`。
形式化陈述：coe_inj {a b : α} : (a : WithOne α) = b ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Option.some_inj`：∀ {α : Type u_1} {a b : α}, some a = some b ↔ a = b
-/
theorem coe_inj {a b : α} : (a : WithOne α) = b ↔ a = b :=
  Option.some_inj

@[to_additive]
/-
**WithOne.coe_injective** 是 Mathlib 中的一个引理，位于命名空间 `WithOne`。
形式化陈述：coe_injective : Function.Injective (coe : α -> WithOne α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Option.some_injective`：some_injective (α : Type*) : Function.Injective (
@some α)
-/
lemma coe_injective : Function.Injective (coe : α → WithOne α) :=
  Option.some_injective _

@[to_additive (attr := elab_as_elim)]
/-
**WithOne.cases_on** 是 Mathlib 中的一个定理，位于命名空间 `WithOne`。
形式化陈述：∀ {α : Type u} {P : WithOne α → Prop} (x : WithOne α), P 1 → (∀ (a : α), P
 ↑a) → P x
参数：x : WithOne α；∀ (a : α), P ↑a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem cases_on {P : WithOne α → Prop} : ∀ x : WithOne α, P 1 → (∀ a : α, P a) → P x :=
  Option.casesOn

@[to_additive]
/-
**WithOne.instMulOneClass** 是 Mathlib 中的一个实例，位于命名空间 `WithOne`。
形式化陈述：instMulOneClass [Mul α] : MulOneClass (WithOne α) where one_mul
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMulOneClass [Mul α] : MulOneClass (WithOne α) where
  one_mul := (Option.lawfulIdentity_merge _).left_id
  mul_one := (Option.lawfulIdentity_merge _).right_id

@[to_additive (attr := simp, norm_cast)]
/-
**WithOne.coe_mul** 是 Mathlib 中的一个引理，位于命名空间 `WithOne`。
形式化陈述：coe_mul [Mul α] (a b : α) : (↑(a * b) : WithOne α) = a * b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_mul [Mul α] (a b : α) : (↑(a * b) : WithOne α) = a * b := rfl

@[to_additive]
/-
**WithOne.instMonoid** 是 Mathlib 中的一个实例，位于命名空间 `WithOne`。
形式化陈述：instMonoid [Semigroup α] : Monoid (WithOne α) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMonoid [Semigroup α] : Monoid (WithOne α) where
  __ := instMulOneClass
  mul_assoc
    | 1, b, c => by simp
    | (a : α), 1, c => by simp
    | (a : α), (b : α), 1 => by simp
    | (a : α), (b : α), (c : α) => by simp_rw [← coe_mul, mul_assoc]

@[to_additive]
/-
**WithOne.instCommMonoid** 是 Mathlib 中的一个定义，位于命名空间 `WithOne`。
形式化陈述：{α : Type u} → [CommSemigroup α] → CommMonoid (WithOne α)
参数：WithOne α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCommMonoid [CommSemigroup α] : CommMonoid (WithOne α) where
  mul_comm
    | (a : α), (b : α) => congr_arg some (mul_comm a b)
    | (_ : α), 1 => rfl
    | 1, (_ : α) => rfl
    | 1, 1 => rfl

@[to_additive (attr := simp, norm_cast)]
/-
**WithOne.coe_inv** 是 Mathlib 中的一个定理，位于命名空间 `WithOne`。
形式化陈述：coe_inv [Inv α] (a : α) : ((a⁻¹ : α) : WithOne α) = (a : WithOne α)⁻¹
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inv [Inv α] (a : α) : ((a⁻¹ : α) : WithOne α) = (a : WithOne α)⁻¹ :=
  rfl

/--
Specialization of `Option.getD` to values in `WithOne α` that respects API boundaries.
-/
@[to_additive
  /-- Specialization of `Option.getD` to values in `WithZero α` that respects API boundaries. -/]
/-
**WithOne.unoneD** 是 Mathlib 中的一个定义，位于命名空间 `WithOne`。
形式化陈述：unoneD (d : α) (x : WithOne α) : α
参数：d : α；x : WithOne α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def unoneD (d : α) (x : WithOne α) : α := recOneCoe d id x

@[to_additive (attr := simp)]
/-
**WithOne.unoneD_one** 是 Mathlib 中的一个定理，位于命名空间 `WithOne`。
形式化陈述：unoneD_one (d : α) : unoneD d 1 = d
参数：d : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unoneD_one (d : α) : unoneD d 1 = d :=
  rfl

@[to_additive (attr := simp)]
/-
**WithOne.unoneD_coe** 是 Mathlib 中的一个定理，位于命名空间 `WithOne`。
形式化陈述：unoneD_coe (d x : α) : unoneD d x = x
参数：d x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unoneD_coe (d x : α) : unoneD d x = x :=
  rfl

@[to_additive]
/-
**WithOne.unoneD_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `WithOne`。
形式化陈述：unoneD_eq_iff {d y : α} {x : WithOne α} : unoneD d x = y ↔ x = y ∨ x = 1 ∧
 y = d
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
-/
theorem unoneD_eq_iff {d y : α} {x : WithOne α} : unoneD d x = y ↔ x = y ∨ x = 1 ∧ y = d := by
  induction x <;> simp [@eq_comm _ d]

@[to_additive (attr := simp)]
/-
**WithOne.unoneD_eq_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `WithOne`。
形式化陈述：unoneD_eq_self_iff {d : α} {x : WithOne α} : unoneD d x = d ↔ x = d ∨ x = 
1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem unoneD_eq_self_iff {d : α} {x : WithOne α} : unoneD d x = d ↔ x = d ∨ x = 1 := by
  simp [unoneD_eq_iff]

@[to_additive]
/-
**WithOne.unoneD_eq_unoneD_iff** 是 Mathlib 中的一个定理，位于命名空间 `WithOne`。
形式化陈述：unoneD_eq_unoneD_iff {d : α} {x y : WithOne α} : unoneD d x = unoneD d y ↔
 x = y ∨ x = d ∧ y = 1 ∨ x = 1 ∧ y = d
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem unoneD_eq_unoneD_iff {d : α} {x y : WithOne α} :
    unoneD d x = unoneD d y ↔ x = y ∨ x = d ∧ y = 1 ∨ x = 1 ∧ y = d := by
  induction y <;> simp [unoneD_eq_iff, or_comm]

@[to_additive]
/-
**WithOne.unoneD_eq_unone** 是 Mathlib 中的一个引理，位于命名空间 `WithOne`。
形式化陈述：unoneD_eq_unone {d : α} {x : WithOne α} (hx : x != 1) : unoneD d x = unone
 hx
参数：hx : x != 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithOne.coe_unone`：∀ {α : Type u} {x : WithOne α} (hx : x ≠ 1), ↑(WithOn
e.unone hx) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
lemma unoneD_eq_unone {d : α} {x : WithOne α} (hx : x ≠ 1) : unoneD d x = unone hx := by
  simp [unoneD_eq_iff]

end WithOne

