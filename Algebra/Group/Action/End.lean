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

/--
Instance `applyMulAction` / 实例 `applyMulAction`

English:
instance applyMulAction
  signature: : MulAction (Function.End α) α where
  body: (· <| ·)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

中文:
实例 applyMulAction
  签名: : MulAction (Function.End α) α where
  定义体: (· <| ·)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
-/
instance applyMulAction : MulAction (Function.End α) α where
  smul := (· <| ·)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/--
Instance `applyAddAction` / 实例 `applyAddAction`

English:
instance applyAddAction
  signature: : AddAction (Additive (Function.End α)) α
  body: inferInstance

中文:
实例 applyAddAction
  签名: : AddAction (Additive (Function.End α)) α
  定义体: inferInstance
-/
instance applyAddAction : AddAction (Additive (Function.End α)) α := inferInstance

/--
lemma `smul_def` / 引理 `smul_def`

English:
lemma smul_def
  given: (f : Function.End α) (a : α)
  statement: f • a = f a
  proof: rfl

中文:
引理 smul_def
  条件: (f : Function.End α) (a : α)
  结论: f • a = f a
  证明: rfl
-/
@[simp] lemma smul_def (f : Function.End α) (a : α) : f • a = f a := rfl

--TODO - This statement should be something like `toFun (f * g) = toFun f ∘ toFun g`
/--
lemma `mul_def` / 引理 `mul_def`

English:
lemma mul_def
  given: (f g : Function.End α)
  statement: (f * g) = f ∘ g
  proof: rfl

中文:
引理 mul_def
  条件: (f g : Function.End α)
  结论: (f * g) = f ∘ g
  证明: rfl
-/
lemma mul_def (f g : Function.End α) : (f * g) = f ∘ g := rfl

--TODO - This statement should be something like `toFun 1 = id`
/--
lemma `one_def` / 引理 `one_def`

English:
lemma one_def
  statement: (1 : Function.End α) = id
  proof: rfl

中文:
引理 one_def
  结论: (1 : Function.End α) = id
  证明: rfl
-/
lemma one_def : (1 : Function.End α) = id := rfl

/--
Instance `apply_FaithfulSMul` / 实例 `apply_FaithfulSMul`

English:
instance apply_FaithfulSMul
  signature: : FaithfulSMul (Function.End α) α where eq_of_smul_eq_smul
  body: funext

中文:
实例 apply_FaithfulSMul
  签名: : FaithfulSMul (Function.End α) α where eq_of_smul_eq_smul
  定义体: funext
-/
instance apply_FaithfulSMul : FaithfulSMul (Function.End α) α where eq_of_smul_eq_smul := funext

end Function.End

/-! #### Tautological action by `Equiv.Perm` -/

namespace Equiv.Perm

/--
Instance `applyMulAction` / 实例 `applyMulAction`

English:
instance applyMulAction
  signature: (α : Type*)
  body: f a
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp]

中文:
实例 applyMulAction
  签名: (α : 类型)
  定义体: f a
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp]
-/
instance applyMulAction (α : Type*) : MulAction (Perm α) α where
  smul f a := f a
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp]
/--
lemma `smul_def` / 引理 `smul_def`

English:
lemma smul_def
  given: {α : Type*} (f : Perm α) (a : α)
  statement: f • a = f a
  proof: rfl

中文:
引理 smul_def
  条件: {α : 类型} (f : Perm α) (a : α)
  结论: f • a = f a
  证明: rfl
-/
protected lemma smul_def {α : Type*} (f : Perm α) (a : α) : f • a = f a := rfl

/--
Instance `applyFaithfulSMul` / 实例 `applyFaithfulSMul`

English:
instance applyFaithfulSMul
  signature: (α : Type*)
  body: ⟨Equiv.ext⟩

中文:
实例 applyFaithfulSMul
  签名: (α : 类型)
  定义体: ⟨Equiv.ext⟩

Depends on / 依赖: Equiv.ext
-/
instance applyFaithfulSMul (α : Type*) : FaithfulSMul (Perm α) α := ⟨Equiv.ext⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulAction.IsPretransitive (Perm α) α
  body: by
  rw [MulAction.isPretransitive_iff]
  classical
  intro x y
  use Equiv.swap x y
  simp

中文:
实例 :
  签名: MulAction.IsPretransitive (Perm α) α
  定义体: by
  rw [MulAction.isPretransitive_iff]
  classical
  intro x y
  use Equiv.swap x y
  simp

Depends on / 依赖: Equiv.swap, MulAction, MulAction.isPretransitive_iff, classical, isPretransitive_iff
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
/--
Instance `applyMulAction` / 实例 `applyMulAction`

English:
instance applyMulAction
  signature: : MulAction (MulAut M) M where
  body: (· <| ·)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

中文:
实例 applyMulAction
  签名: : MulAction (MulAut M) M where
  定义体: (· <| ·)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
-/
instance applyMulAction : MulAction (MulAut M) M where
  smul := (· <| ·)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- The tautological action by `MulAut M` on `M`.

This generalizes `Function.End.applyMulAction`. -/
@[to_additive /-- The tautological action by `AddAut M` on `M`. -/]
/--
Instance `applyMulDistribMulAction` / 实例 `applyMulDistribMulAction`

English:
instance applyMulDistribMulAction
  signature: : MulDistribMulAction (MulAut M) M where
  body: map_one
  smul_mul := map_mul

中文:
实例 applyMulDistribMulAction
  签名: : MulDistribMulAction (MulAut M) M where
  定义体: map_one
  smul_mul := map_mul

Depends on / 依赖: map_one
-/
instance applyMulDistribMulAction : MulDistribMulAction (MulAut M) M where
  smul_one := map_one
  smul_mul := map_mul

/--
lemma `smul_def` / 引理 `smul_def`

English:
lemma smul_def
  given: (f : MulAut M) (a : M)
  statement: f • a = f a
  proof: rfl

中文:
引理 smul_def
  条件: (f : MulAut M) (a : M)
  结论: f • a = f a
  证明: rfl
-/
@[to_additive (attr := simp)] protected lemma smul_def (f : MulAut M) (a : M) : f • a = f a := rfl

/-- `MulAut.applyDistribMulAction` is faithful. -/
@[to_additive /-- `AddAut.applyAddDistribAddAction` is faithful. -/]
/--
Instance `apply_faithfulSMul` / 实例 `apply_faithfulSMul`

English:
instance apply_faithfulSMul
  signature: : FaithfulSMul (MulAut M) M where eq_of_smul_eq_smul
  body: MulEquiv.ext

中文:
实例 apply_faithfulSMul
  签名: : FaithfulSMul (MulAut M) M where eq_of_smul_eq_smul
  定义体: MulEquiv.ext

Depends on / 依赖: MulEquiv, MulEquiv.ext
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

/--
Definition of `MulAction.toEndHom` / `MulAction.toEndHom` 的定义

English:
definition MulAction.toEndHom
  signature: [MulAction M α]
  body: (· • ·)
  map_one' := funext (one_smul M)
  map_mul' x y := funext (mul_smul x y)

中文:
定义 MulAction.toEndHom
  签名: [MulAction M α]
  定义体: (· • ·)
  map_one' := funext (one_smul M)
  map_mul' x y := funext (mul_smul x y)
-/
def MulAction.toEndHom [MulAction M α] : M ->* Function.End α where
  toFun := (· • ·)
  map_one' := funext (one_smul M)
  map_mul' x y := funext (mul_smul x y)

/--
Definition of `MulAction.ofEndHom` / `MulAction.ofEndHom` 的定义

English:
abbreviation MulAction.ofEndHom
  signature: (f : M ->* Function.End α)
  body: .compHom α f

中文:
缩写 MulAction.ofEndHom
  签名: (f : M ->* Function.End α)
  定义体: .compHom α f

Depends on / 依赖: compHom
-/
abbrev MulAction.ofEndHom (f : M ->* Function.End α) : MulAction M α := .compHom α f

end Monoid

section AddMonoid
variable [AddMonoid M]

/--
Definition of `AddAction.toEndHom` / `AddAction.toEndHom` 的定义

English:
definition AddAction.toEndHom
  signature: [AddAction M α]
  body: MulAction.toEndHom.toAdditiveRight

中文:
定义 AddAction.toEndHom
  签名: [AddAction M α]
  定义体: MulAction.toEndHom.toAdditiveRight

Depends on / 依赖: MulAction, MulAction.toEndHom.toAdditiveRight, toAdditiveRight, toEndHom
-/
def AddAction.toEndHom [AddAction M α] : M ->+ Additive (Function.End α) :=
  MulAction.toEndHom.toAdditiveRight

/--
Definition of `AddAction.ofEndHom` / `AddAction.ofEndHom` 的定义

English:
abbreviation AddAction.ofEndHom
  signature: (f : M ->+ Additive (Function.End α))
  body: .compHom α f

中文:
缩写 AddAction.ofEndHom
  签名: (f : M ->+ Additive (Function.End α))
  定义体: .compHom α f

Depends on / 依赖: compHom
-/
abbrev AddAction.ofEndHom (f : M ->+ Additive (Function.End α)) : AddAction M α := .compHom α f

end AddMonoid

section Group
variable (G α) [Group G] [MulAction G α]

/-- Given an action of a group `G` on a set `α`, each `g : G` defines a permutation of `α`. -/
@[simps]
/--
Definition of `MulAction.toPermHom` / `MulAction.toPermHom` 的定义

English:
definition MulAction.toPermHom
  signature: : G ->* Equiv.Perm α where
  body: MulAction.toPerm
map_one' := Equiv.ext one_smul G
map_mul' u₁ u₂ := Equiv.ext mul_smul (u₁ : G) u₂

中文:
定义 MulAction.toPermHom
  签名: : G ->* Equiv.Perm α where
  定义体: MulAction.toPerm
map_one' := Equiv.ext one_smul G
map_mul' u₁ u₂ := Equiv.ext mul_smul (u₁ : G) u₂

Depends on / 依赖: MulAction, MulAction.toPerm, toPerm
-/
def MulAction.toPermHom : G ->* Equiv.Perm α where
  toFun := MulAction.toPerm
map_one' := Equiv.ext one_smul G
map_mul' u₁ u₂ := Equiv.ext mul_smul (u₁ : G) u₂

/--
lemma `MulAction.coe_toPermHom` / 引理 `MulAction.coe_toPermHom`

English:
lemma MulAction.coe_toPermHom
  proof: rfl

中文:
引理 MulAction.coe_toPermHom
  证明: rfl
-/
lemma MulAction.coe_toPermHom :
    ⇑(MulAction.toPermHom G α) = MulAction.toPerm :=
  rfl

/--
lemma `MulAction.toPerm_one` / 引理 `MulAction.toPerm_one`

English:
lemma MulAction.toPerm_one
  proof: by
  aesop

中文:
引理 MulAction.toPerm_one
  证明: by
  aesop
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
/--
Definition of `AddAction.toPermHom` / `AddAction.toPermHom` 的定义

English:
definition AddAction.toPermHom
  signature: : G ->+ Additive (Equiv.Perm α)
  body: (MulAction.toPermHom ..).toAdditiveRight

中文:
定义 AddAction.toPermHom
  签名: : G ->+ Additive (Equiv.Perm α)
  定义体: (MulAction.toPermHom ..).toAdditiveRight

Depends on / 依赖: MulAction, MulAction.toPermHom, toAdditiveRight, toPermHom
-/
def AddAction.toPermHom : G ->+ Additive (Equiv.Perm α) := (MulAction.toPermHom ..).toAdditiveRight

/--
lemma `AddAction.coe_toPermHom` / 引理 `AddAction.coe_toPermHom`

English:
lemma AddAction.coe_toPermHom
  proof: rfl

中文:
引理 AddAction.coe_toPermHom
  证明: rfl
-/
lemma AddAction.coe_toPermHom :
    ⇑(AddAction.toPermHom G α) = AddAction.toPerm :=
  rfl

/--
theorem `AddAction.toPerm_zero` / 定理 `AddAction.toPerm_zero`

English:
theorem AddAction.toPerm_zero
  proof: by
  aesop

中文:
定理 AddAction.toPerm_zero
  证明: by
  aesop
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
/--
Definition of `MulDistribMulAction.toMulEquiv` / `MulDistribMulAction.toMulEquiv` 的定义

English:
definition MulDistribMulAction.toMulEquiv
  signature: (x : G)
  body: { MulDistribMulAction.toMonoidHom M x, MulAction.toPermHom G M x with }

中文:
定义 MulDistribMulAction.toMulEquiv
  签名: (x : G)
  定义体: { MulDistribMulAction.toMonoidHom M x, MulAction.toPermHom G M x with }

Depends on / 依赖: MulAction, MulAction.toPermHom, MulDistribMulAction, MulDistribMulAction.toMonoidHom, toMonoidHom, toPermHom
-/
def MulDistribMulAction.toMulEquiv (x : G) : M ≃* M :=
  { MulDistribMulAction.toMonoidHom M x, MulAction.toPermHom G M x with }

variable (G) in
/-- Each element of the group defines a multiplicative monoid isomorphism.

This is a stronger version of `MulAction.toPermHom`. -/
@[simps]
/--
Definition of `MulDistribMulAction.toMulAut` / `MulDistribMulAction.toMulAut` 的定义

English:
definition MulDistribMulAction.toMulAut
  signature: : G ->* MulAut M where
  body: MulDistribMulAction.toMulEquiv M
  map_one' := MulEquiv.ext (one_smul _)
  map_mul' _ _ := MulEquiv.ext (mul_smul _ _)

中文:
定义 MulDistribMulAction.toMulAut
  签名: : G ->* MulAut M where
  定义体: MulDistribMulAction.toMulEquiv M
  map_one' := MulEquiv.ext (one_smul _)
  map_mul' _ _ := MulEquiv.ext (mul_smul _ _)

Depends on / 依赖: MulDistribMulAction, MulDistribMulAction.toMulEquiv, toMulEquiv
-/
def MulDistribMulAction.toMulAut : G ->* MulAut M where
  toFun := MulDistribMulAction.toMulEquiv M
  map_one' := MulEquiv.ext (one_smul _)
  map_mul' _ _ := MulEquiv.ext (mul_smul _ _)

end MulDistribMulAction

section Arrow
variable [Group G] [MulAction G A] [Monoid M]

attribute [local instance] arrowMulDistribMulAction

/--
Definition of `mulAutArrow` / `mulAutArrow` 的定义

English:
definition mulAutArrow
  signature: : G ->* MulAut (A -> M)
  body: MulDistribMulAction.toMulAut _ _

中文:
定义 mulAutArrow
  签名: : G ->* MulAut (A -> M)
  定义体: MulDistribMulAction.toMulAut _ _
-/
@[simps!] def mulAutArrow : G ->* MulAut (A -> M) := MulDistribMulAction.toMulAut _ _

end Arrow
