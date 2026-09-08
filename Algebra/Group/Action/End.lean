/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.Algebra.Group.Action.Hom
public import Mathlib.Algebra.Group.End

/-!
# Interaction between actions and endomorphisms/automorphisms

This file provides two things:
* The tautological actions by endomorphisms/automorphisms on their base type.
* An action by a monoid/group on a type is the same as a hom from the monoid/group to
  endomorphisms/automorphisms of the type.

## Tags

monoid action, group action
-/

@[expose] public section

assert_not_exists MonoidWithZero

open Function (Injective Surjective)

variable {G M N A α : Type*}

/-! ### Tautological actions -/

/-! #### Tautological action by `Function.End` -/

namespace Function.End

/-- The tautological action by `Function.End α` on `α`.

This is generalized to bundled endomorphisms by:
* `Equiv.Perm.applyMulAction`
* `AddMonoid.End.applyDistribMulAction`
* `AddMonoid.End.applyModule`
* `AddAut.applyDistribMulAction`
* `MulAut.applyMulDistribMulAction`
* `LinearEquiv.applyDistribMulAction`
* `LinearMap.applyModule`
* `RingHom.applyMulSemiringAction`
* `RingAut.applyMulSemiringAction`
* `AlgEquiv.applyMulSemiringAction`
* `RelHom.applyMulAction`
* `RelEmbedding.applyMulAction`
* `RelIso.applyMulAction`
-/
/-
**Function.End.applyMulAction** 是 Mathlib 中的一个实例，位于命名空间 `Function.End`。
形式化陈述：applyMulAction : MulAction (Function.End α) α where smul
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tautological action by `Function.End α` on `α`.

This is generalized to bundled endomorphisms by:
* `Equiv.Perm.applyMulAction`
* `AddMonoid.End.applyDistribMulAction`
* `AddMonoid.End.applyModule`
* `AddAut.applyDistribMulAction`
* `MulAut.applyMulDistribMulAction`
* `LinearEquiv.applyDistribMulAction`
* `LinearMap.applyModule`
* `RingHom.applyMulSemiringAction`
* `RingAut.applyMulSemiringAction`
* `AlgEquiv.applyMulSemiringAction`
* `RelHom.applyMulAction`
* `RelEmbedding.applyMulAction`
* `RelIso.applyMulAction`
-/
instance applyMulAction : MulAction (Function.End α) α where
  smul := (· <| ·)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- The tautological additive action by `Additive (Function.End α)` on `α`. -/
/-
**Function.End.applyAddAction** 是 Mathlib 中的一个实例，位于命名空间 `Function.End`。
形式化陈述：applyAddAction : AddAction (Additive (Function.End α)) α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tautological additive action by `Additive (Function.End α)` on `α`.
-/
instance applyAddAction : AddAction (Additive (Function.End α)) α := inferInstance
/-
**Function.End.smul_def** 是 Mathlib 中的一个定理，位于命名空间 `Function.End`。
形式化陈述：∀ {α : Type u_5} (f : Function.End α) (a : α), f • a = f a
参数：f : Function.End α；a : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma smul_def (f : Function.End α) (a : α) : f • a = f a := rfl

--TODO - This statement should be something like `toFun (f * g) = toFun f ∘ toFun g`
/-
**Function.End.mul_def** 是 Mathlib 中的一个引理，位于命名空间 `Function.End`。
形式化陈述：mul_def (f g : Function.End α) : (f * g) = f ∘ g
参数：f g : Function.End α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mul_def (f g : Function.End α) : (f * g) = f ∘ g := rfl

--TODO - This statement should be something like `toFun 1 = id`
/-
**Function.End.one_def** 是 Mathlib 中的一个引理，位于命名空间 `Function.End`。
形式化陈述：one_def : (1 : Function.End α) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma one_def : (1 : Function.End α) = id := rfl

/-- `Function.End.applyMulAction` is faithful. -/
/-
**Function.End.apply_FaithfulSMul** 是 Mathlib 中的一个实例，位于命名空间 `Function.End`。
形式化陈述：apply_FaithfulSMul : FaithfulSMul (Function.End α) α where eq_of_smul_eq_s
mul
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g

--- 原说明 ---
`Function.End.applyMulAction` is faithful.
-/
instance apply_FaithfulSMul : FaithfulSMul (Function.End α) α where eq_of_smul_eq_smul := funext

end Function.End

/-! #### Tautological action by `Equiv.Perm` -/

namespace Equiv.Perm

/-- The tautological action by `Equiv.Perm α` on `α`.

This generalizes `Function.End.applyMulAction`. -/
/-
**Equiv.Perm.applyMulAction** 是 Mathlib 中的一个实例，位于命名空间 `Equiv.Perm`。
形式化陈述：applyMulAction (α : Type*) : MulAction (Perm α) α where smul f a
参数：α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tautological action by `Equiv.Perm α` on `α`.

This generalizes `Function.End.applyMulAction`.
-/
instance applyMulAction (α : Type*) : MulAction (Perm α) α where
  smul f a := f a
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp]
/-
**Equiv.Perm.smul_def** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：∀ {α : Type u_6} (f : Equiv.Perm α) (a : α), f • a = f a
参数：f : Equiv.Perm α；a : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma smul_def {α : Type*} (f : Perm α) (a : α) : f • a = f a := rfl

/-- `Equiv.Perm.applyMulAction` is faithful. -/
/-
**Equiv.Perm.applyFaithfulSMul** 是 Mathlib 中的一个实例，位于命名空间 `Equiv.Perm`。
形式化陈述：applyFaithfulSMul (α : Type*) : FaithfulSMul (Perm α) α
参数：α : Type*。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t

--- 原说明 ---
`Equiv.Perm.applyMulAction` is faithful.
-/
instance applyFaithfulSMul (α : Type*) : FaithfulSMul (Perm α) α := ⟨Equiv.ext⟩

/-- The permutation group of `α` acts transitively on `α`. -/
/-
**Equiv.Perm.** 是 Mathlib 中的一个实例，位于命名空间 `Equiv.Perm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The permutation group of `α` acts transitively on `α`.
-/
instance : MulAction.IsPretransitive (Perm α) α := by
  rw [MulAction.isPretransitive_iff]
  classical
  intro x y
  use Equiv.swap x y
  simp

end Equiv.Perm

/-! #### Tautological action by `MulAut` -/

namespace MulAut
variable [Monoid M]

/-- The tautological action by `MulAut M` on `M`. -/
@[to_additive /-- The tautological action by `AddAut M` on `M`. -/]
/-
**MulAut.applyMulAction** 是 Mathlib 中的一个实例，位于命名空间 `MulAut`。
形式化陈述：applyMulAction : MulAction (MulAut M) M where smul
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tautological action by `MulAut M` on `M`.
-/
instance applyMulAction : MulAction (MulAut M) M where
  smul := (· <| ·)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- The tautological action by `MulAut M` on `M`.

This generalizes `Function.End.applyMulAction`. -/
@[to_additive /-- The tautological action by `AddAut M` on `M`. -/]
/-
**MulAut.applyMulDistribMulAction** 是 Mathlib 中的一个实例，位于命名空间 `MulAut`。
形式化陈述：applyMulDistribMulAction : MulDistribMulAction (MulAut M) M where smul_one
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tautological action by `MulAut M` on `M`.

This generalizes `Function.End.applyMulAction`.
-/
instance applyMulDistribMulAction : MulDistribMulAction (MulAut M) M where
  smul_one := map_one
  smul_mul := map_mul
/-
**MulAut.smul_def** 是 Mathlib 中的一个定理，位于命名空间 `MulAut`。
形式化陈述：∀ {M : Type u_2} [inst : Monoid M] (f : MulAut M) (a : M), f • a = f a
参数：f : MulAut M；a : M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive (attr := simp)] protected lemma smul_def (f : MulAut M) (a : M) : f • a = f a := rfl

/-- `MulAut.applyDistribMulAction` is faithful. -/
@[to_additive /-- `AddAut.applyAddDistribAddAction` is faithful. -/]
/-
**MulAut.apply_faithfulSMul** 是 Mathlib 中的一个实例，位于命名空间 `MulAut`。
形式化陈述：apply_faithfulSMul : FaithfulSMul (MulAut M) M where eq_of_smul_eq_smul
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquiv.ext`：ext {f g : MulEquiv M N} (h : forall x, f x = g x) : f = g

--- 原说明 ---
`MulAut.applyDistribMulAction` is faithful.
-/
instance apply_faithfulSMul : FaithfulSMul (MulAut M) M where eq_of_smul_eq_smul := MulEquiv.ext

end MulAut

/-! #### Tautological action by `AddAut` -/

namespace AddAut
variable [AddMonoid M]

@[deprecated (since := "2026-05-26")] alias smul_def := AddAut.vadd_def
@[deprecated (since := "2026-05-26")] alias apply_faithfulSMul := apply_faithfulVAdd

end AddAut

/-! ### Converting actions to and from homs to the monoid/group of endomorphisms/automorphisms -/

section Monoid
variable [Monoid M]

/-- The monoid hom representing a monoid action.

When `M` is a group, see `MulAction.toPermHom`. -/
/-
**MulAction.toEndHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MulAction.toEndHom [MulAction M α] : M ->* Function.End α where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The monoid hom representing a monoid action.

When `M` is a group, see `MulAction.toPermHom`.
-/
def MulAction.toEndHom [MulAction M α] : M →* Function.End α where
  toFun := (· • ·)
  map_one' := funext (one_smul M)
  map_mul' x y := funext (mul_smul x y)

/-- The monoid action induced by a monoid hom to `Function.End α`

See note [reducible non-instances]. -/
/-
**MulAction.ofEndHom** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：MulAction.ofEndHom (f : M ->* Function.End α) : MulAction M α
参数：f : M ->* Function.End α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The monoid action induced by a monoid hom to `Function.End α`

See note [reducible non-instances].
-/
abbrev MulAction.ofEndHom (f : M →* Function.End α) : MulAction M α := .compHom α f

end Monoid

section AddMonoid
variable [AddMonoid M]

/-- The additive monoid hom representing an additive monoid action.

When `M` is a group, see `AddAction.toPermHom`. -/
/-
**AddAction.toEndHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AddAction.toEndHom [AddAction M α] : M ->+ Additive (Function.End α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The additive monoid hom representing an additive monoid action.

When `M` is a group, see `AddAction.toPermHom`.
-/
def AddAction.toEndHom [AddAction M α] : M →+ Additive (Function.End α) :=
  MulAction.toEndHom.toAdditiveRight

/-- The additive action induced by a hom to `Additive (Function.End α)`

See note [reducible non-instances]. -/
/-
**AddAction.ofEndHom** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：AddAction.ofEndHom (f : M ->+ Additive (Function.End α)) : AddAction M α
参数：f : M ->+ Additive (Function.End α)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The additive action induced by a hom to `Additive (Function.End α)`

See note [reducible non-instances].
-/
abbrev AddAction.ofEndHom (f : M →+ Additive (Function.End α)) : AddAction M α := .compHom α f

end AddMonoid

section Group
variable (G α) [Group G] [MulAction G α]

/-- Given an action of a group `G` on a set `α`, each `g : G` defines a permutation of `α`. -/
@[simps]
/-
**MulAction.toPermHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MulAction.toPermHom : G ->* Equiv.Perm α where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an action of a group `G` on a set `α`, each `g : G` defines a permutation 
of `α`.
-/
def MulAction.toPermHom : G →* Equiv.Perm α where
  toFun := MulAction.toPerm
  map_one' := Equiv.ext <| one_smul G
  map_mul' u₁ u₂ := Equiv.ext <| mul_smul (u₁ : G) u₂
/-
**MulAction.coe_toPermHom** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MulAction.coe_toPermHom : ⇑(MulAction.toPermHom G α) = MulAction.toPerm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma MulAction.coe_toPermHom :
    ⇑(MulAction.toPermHom G α) = MulAction.toPerm :=
  rfl
/-
**MulAction.toPerm_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MulAction.toPerm_one : (MulAction.toPerm (1 : G)) = (1 : Equiv.Perm α)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.ext`：∀ {α : Sort u} {σ τ : Equiv.Perm α}, (∀ (x : α), σ x = τ
 x) → σ = τ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulAction.toPerm_apply`：∀ {α : Type u_5} {β : Type u_6} [inst : Group α]
 [inst_1 : MulAction α β] (a : α) (x : β),   (MulAction.toPerm a) x = a • x
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma MulAction.toPerm_one :
    (MulAction.toPerm (1 : G)) = (1 : Equiv.Perm α) := by
  aesop

end Group

section AddGroup
variable (G α) [AddGroup G] [AddAction G α]

/-- Given an action of an additive group `G` on a set `α`, each `g : G` defines a permutation of
`α`. -/
@[simps!]
/-
**AddAction.toPermHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AddAction.toPermHom : G ->+ Additive (Equiv.Perm α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an action of an additive group `G` on a set `α`, each `g : G` defines a pe
rmutation of
`α`.
-/
def AddAction.toPermHom : G →+ Additive (Equiv.Perm α) := (MulAction.toPermHom ..).toAdditiveRight
/-
**AddAction.coe_toPermHom** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AddAction.coe_toPermHom : ⇑(AddAction.toPermHom G α) = AddAction.toPerm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma AddAction.coe_toPermHom :
    ⇑(AddAction.toPermHom G α) = AddAction.toPerm :=
  rfl
/-
**AddAction.toPerm_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AddAction.toPerm_zero : (AddAction.toPerm (0 : G)) = (1 : Equiv.Perm α)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.ext`：∀ {α : Sort u} {σ τ : Equiv.Perm α}, (∀ (x : α), σ x = τ
 x) → σ = τ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddAction.toPerm_apply`：∀ {α : Type u_5} {β : Type u_6} [inst : AddGroup
 α] [inst_1 : AddAction α β] (a : α) (x : β),   (AddAction.toPerm a) x = a +ᵥ x
· 使用定理 `zero_vadd`：∀ (M : Type u_1) {α : Type u_5} [inst : AddMonoid M] [inst_1 
: AddAction M α] (b : α), 0 +ᵥ b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem AddAction.toPerm_zero :
    (AddAction.toPerm (0 : G)) = (1 : Equiv.Perm α) := by
  aesop

end AddGroup

section MulDistribMulAction
variable (M) [Group G] [Monoid M] [MulDistribMulAction G M]

/-- Each element of the group defines a multiplicative monoid isomorphism.

This is a stronger version of `MulAction.toPerm`. -/
@[simps +simpRhs]
/-
**MulDistribMulAction.toMulEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MulDistribMulAction.toMulEquiv (x : G) : M ≃* M
参数：x : G。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun

--- 原说明 ---
Each element of the group defines a multiplicative monoid isomorphism.

This is a stronger version of `MulAction.toPerm`.
-/
def MulDistribMulAction.toMulEquiv (x : G) : M ≃* M :=
  { MulDistribMulAction.toMonoidHom M x, MulAction.toPermHom G M x with }

variable (G) in
/-- Each element of the group defines a multiplicative monoid isomorphism.

This is a stronger version of `MulAction.toPermHom`. -/
@[simps]
/-
**MulDistribMulAction.toMulAut** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MulDistribMulAction.toMulAut : G ->* MulAut M where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Each element of the group defines a multiplicative monoid isomorphism.

This is a stronger version of `MulAction.toPermHom`.
-/
def MulDistribMulAction.toMulAut : G →* MulAut M where
  toFun := MulDistribMulAction.toMulEquiv M
  map_one' := MulEquiv.ext (one_smul _)
  map_mul' _ _ := MulEquiv.ext (mul_smul _ _)

end MulDistribMulAction

section Arrow
variable [Group G] [MulAction G A] [Monoid M]

attribute [local instance] arrowMulDistribMulAction

/-- Given groups `G H` with `G` acting on `A`, `G` acts by
multiplicative automorphisms on `A → H`. -/
/-
**mulAutArrow** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：{G : Type u_1} →   {M : Type u_2} → {A : Type u_4} → [inst : Group G] → [M
ulAction G A] → [inst_2 : Monoid M] → G →* MulAut (A → M)
参数：A → M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given groups `G H` with `G` acting on `A`, `G` acts by
multiplicative automorphisms on `A → H`.
-/
@[simps!] def mulAutArrow : G →* MulAut (A → M) := MulDistribMulAction.toMulAut _ _

end Arrow

