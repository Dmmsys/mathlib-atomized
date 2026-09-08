/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Action.TypeTags

/-!
# Pretransitive group actions

This file defines a typeclass for pretransitive group actions.

## Notation

- `a • b` is used as notation for `SMul.smul a b`.
- `a +ᵥ b` is used as notation for `VAdd.vadd a b`.

## Implementation details

This file should avoid depending on other parts of `GroupTheory`, to avoid import cycles.
More sophisticated lemmas belong in `GroupTheory.GroupAction`.

## Tags

group action
-/

public section

assert_not_exists MonoidWithZero

open Function (Injective Surjective)

variable {M G α β : Type*}

/-!
### (Pre)transitive action

`M` acts pretransitively on `α` if for any `x y` there is `g` such that `g • x = y` (or `g +ᵥ x = y`
for an additive action). A transitive action should furthermore have `α` nonempty.

In this section we define typeclasses `MulAction.IsPretransitive` and
`AddAction.IsPretransitive` and provide `MulAction.exists_smul_eq`/`AddAction.exists_vadd_eq`,
`MulAction.surjective_smul`/`AddAction.surjective_vadd` as public interface to access this
property. We do not provide typeclasses `*Action.IsTransitive`; users should assume
`[MulAction.IsPretransitive M α] [Nonempty α]` instead.
-/

/-- `M` acts pretransitively on `α` if for any `x y` there is `g` such that `g +ᵥ x = y`.
  A transitive action should furthermore have `α` nonempty. -/
/-
**AddAction.IsPretransitive** 是 Mathlib 中的一个归纳类型，位于命名空间 `AddAction`。
形式化陈述：(M : Type u_5) → (α : Type u_6) → [VAdd M α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`M` acts pretransitively on `α` if for any `x y` there is `g` such that `g +ᵥ x 
= y`.
  A transitive action should furthermore have `α` nonempty.
-/
class AddAction.IsPretransitive (M α : Type*) [VAdd M α] : Prop where
  /-- There is `g` such that `g +ᵥ x = y`. -/
  exists_vadd_eq : ∀ x y : α, ∃ g : M, g +ᵥ x = y

/-- `M` acts pretransitively on `α` if for any `x y` there is `g` such that `g • x = y`.
  A transitive action should furthermore have `α` nonempty. -/
@[to_additive (attr := mk_iff)]
/-
**MulAction.IsPretransitive** 是 Mathlib 中的一个归纳类型，位于命名空间 `MulAction`。
形式化陈述：(M : Type u_5) → (α : Type u_6) → [SMul M α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`M` acts pretransitively on `α` if for any `x y` there is `g` such that `g • x =
 y`.
  A transitive action should furthermore have `α` nonempty.
-/
class MulAction.IsPretransitive (M α : Type*) [SMul M α] : Prop where
  /-- There is `g` such that `g • x = y`. -/
  exists_smul_eq : ∀ x y : α, ∃ g : M, g • x = y

@[to_additive]
/-
**MulAction.instIsPretransitiveOfSubsingleton** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：MulAction.instIsPretransitiveOfSubsingleton {M α : Type*} [Monoid M] [MulA
ction M α] [Subsingleton α] : MulAction.IsPretransitive M α where exists_smul_eq
 x y
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance MulAction.instIsPretransitiveOfSubsingleton
    {M α : Type*} [Monoid M] [MulAction M α] [Subsingleton α] :
    MulAction.IsPretransitive M α where
  exists_smul_eq x y := ⟨1, by
    simp only [one_smul, Subsingleton.elim x y] ⟩

namespace MulAction
variable (M) [SMul M α] [IsPretransitive M α]

@[to_additive]
/-
**MulAction.exists_smul_eq** 是 Mathlib 中的一个引理，位于命名空间 `MulAction`。
形式化陈述：exists_smul_eq (x y : α) : exists m : M, m • x = y
参数：x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulAction.IsPretransitive.exists_smul_eq`：∀ {M : Type u_5} {α : Type u_6
} {inst : SMul M α} [self : MulAction.IsPretransitive M α] (x y : α), ∃ g, g • x
 = y
-/
lemma exists_smul_eq (x y : α) : ∃ m : M, m • x = y := IsPretransitive.exists_smul_eq x y

@[to_additive]
/-
**MulAction.surjective_smul** 是 Mathlib 中的一个引理，位于命名空间 `MulAction`。
形式化陈述：surjective_smul (x : α) : Surjective fun c : M => c • x
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MulAction.exists_smul_eq`：exists_smul_eq (x y : α) : exists m : M, m • x
 = y
-/
lemma surjective_smul (x : α) : Surjective fun c : M ↦ c • x := exists_smul_eq M x

/-- The left regular action of a group on itself is transitive. -/
@[to_additive /-- The regular action of a group on itself is transitive. -/]
/-
**MulAction.Regular.isPretransitive** 是 Mathlib 中的一个定理，位于命名空间 `MulAction.Regular
`。
形式化陈述：∀ {G : Type u_2} [inst : Group G], MulAction.IsPretransitive G G
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inv_mul_cancel_right`：inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a

--- 原说明 ---
The left regular action of a group on itself is transitive.
-/
instance Regular.isPretransitive [Group G] : IsPretransitive G G :=
  ⟨fun x y ↦ ⟨y * x⁻¹, inv_mul_cancel_right _ _⟩⟩

/-- The right regular action of a group on itself is transitive. -/
@[to_additive /-- The right regular action of an additive group on itself is transitive. -/]
/-
**MulAction.Regular.isPretransitive_mulOpposite** 是 Mathlib 中的一个定理，位于命名空间 `MulAc
tion.Regular`。
形式化陈述：∀ {G : Type u_2} [inst : Group G], MulAction.IsPretransitive Gᵐᵒᵖ G
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b

--- 原说明 ---
The right regular action of a group on itself is transitive.
-/
instance Regular.isPretransitive_mulOpposite [Group G] : IsPretransitive Gᵐᵒᵖ G :=
  ⟨fun x y ↦ ⟨.op (x⁻¹ * y), mul_inv_cancel_left _ _⟩⟩

/-- If `G` is a group acting multiplicatively on a set, then the action is transitive if there is
a single element whose orbit is everything. -/
@[to_additive /-- If `G` is a group acting additively on a set, then the action is transitive if
there is a single element whose orbit is everything. -/]
/-
**MulAction.IsPretransitive.of_orbit** 是 Mathlib 中的一个定理，位于命名空间 `MulAction.IsPret
ransitive`。
形式化陈述：∀ {G : Type u_2} {X : Type u_5} [inst : Group G] [inst_1 : MulAction G X] 
{x₀ : X},   (∀ (x : X), ∃ g, g • x₀ = x) → MulAction.IsPretransitive G X
参数：∀ (x : X), ∃ g, g • x₀ = x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用引理 `inv_smul_smul`：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsPretransitive.of_orbit {X : Type*} [Group G] [MulAction G X] {x₀ : X}
    (ha : ∀ x, ∃ g : G, g • x₀ = x) :
    IsPretransitive G X := by
  constructor
  intro x y
  rcases ha x with ⟨g, rfl⟩
  rcases ha y with ⟨h, rfl⟩
  exact ⟨h * g⁻¹, by simp [mul_smul]⟩

end MulAction

namespace MulAction

@[to_additive]
/-
**MulAction.IsPretransitive.of_smul_eq** 是 Mathlib 中的一个定理，位于命名空间 `MulAction.IsPr
etransitive`。
形式化陈述：∀ {M : Type u_5} {N : Type u_6} {α : Type u_7} [inst : SMul M α] [inst_1 :
 SMul N α] [MulAction.IsPretransitive M α]   (f : M → N), (∀ {c : M} {x : α}, f 
c • x = c • x) → MulAction.IsPretransitive N α
参数：f : M → N；∀ {c : M} {x : α}, f c • x = c • x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `MulAction.IsPretransitive.exists_smul_eq`：∀ {M : Type u_5} {α : Type u_6
} {inst : SMul M α} [self : MulAction.IsPretransitive M α] (x y : α), ∃ g, g • x
 = y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
lemma IsPretransitive.of_smul_eq {M N α : Type*} [SMul M α] [SMul N α] [IsPretransitive M α]
    (f : M → N) (hf : ∀ {c : M} {x : α}, f c • x = c • x) : IsPretransitive N α where
  exists_smul_eq x y := (exists_smul_eq x y).elim fun m h ↦ ⟨f m, hf.trans h⟩

end MulAction

section CompatibleScalar

@[to_additive]
/-
**MulAction.IsPretransitive.of_isScalarTower** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MulAction.IsPretransitive.of_isScalarTower (M : Type*) {N α : Type*} [Mono
id N] [SMul M N] [MulAction N α] [SMul M α] [IsScalarTower M N α] [IsPretransiti
ve M α] : IsPretransitive N α
参数：M : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulAction.IsPretransitive.of_smul_eq`：∀ {M : Type u_5} {N : Type u_6} {α
 : Type u_7} [inst : SMul M α] [inst_1 : SMul N α] [MulAction.IsPretransitive M 
α]   (f : M → N), (∀ {c : …
· 使用引理 `smul_one_smul`：smul_one_smul {M} (N) [Monoid N] [SMul M N] [MulAction N 
α] [SMul M α] [IsScalarTower M N α] (x : M) (y : α) : (x • (1 : N)) • y = x • y
-/
lemma MulAction.IsPretransitive.of_isScalarTower (M : Type*) {N α : Type*} [Monoid N] [SMul M N]
    [MulAction N α] [SMul M α] [IsScalarTower M N α] [IsPretransitive M α] : IsPretransitive N α :=
  of_smul_eq (fun x : M ↦ x • 1) (smul_one_smul N _ _)

end CompatibleScalar

/-! ### `Additive`, `Multiplicative` -/

section

open Additive Multiplicative

/-
**Additive.addAction_isPretransitive** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Additive.addAction_isPretransitive [Monoid α] [MulAction α β] [MulAction.I
sPretransitive α β] : AddAction.IsPretransitive (Additive α) β
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `MulAction.exists_smul_eq`：exists_smul_eq (x y : α) : exists m : M, m • x
 = y
-/
instance Additive.addAction_isPretransitive [Monoid α] [MulAction α β]
    [MulAction.IsPretransitive α β] : AddAction.IsPretransitive (Additive α) β :=
  ⟨@MulAction.exists_smul_eq α _ _ _⟩
/-
**Multiplicative.mulAction_isPretransitive** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Multiplicative.mulAction_isPretransitive [AddMonoid α] [AddAction α β] [Ad
dAction.IsPretransitive α β] : MulAction.IsPretransitive (Multiplicative α) β
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AddAction.exists_vadd_eq`：∀ (M : Type u_1) {α : Type u_3} [inst : VAdd M
 α] [AddAction.IsPretransitive M α] (x y : α), ∃ m, m +ᵥ x = y
-/
instance Multiplicative.mulAction_isPretransitive [AddMonoid α] [AddAction α β]
    [AddAction.IsPretransitive α β] : MulAction.IsPretransitive (Multiplicative α) β :=
  ⟨@AddAction.exists_vadd_eq α _ _ _⟩

end

