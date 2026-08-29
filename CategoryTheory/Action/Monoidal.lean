/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.CategoryTheory.Monoidal.Linear
public import Mathlib.CategoryTheory.Monoidal.Rigid.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence
public import Mathlib.CategoryTheory.Monoidal.Transport
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.Action.Concrete
public import Mathlib.CategoryTheory.Action.Limits

/-!
# Induced monoidal structure on `Action V G`

We show:

* When `V` is monoidal, braided, or symmetric, so is `Action V G`.
* When `V` is rigid and `G` is a group, `Action V G` is also rigid.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

variable {V : Type*} [Category* V] {G : Type*} [Monoid G]

namespace Action

section Monoidal

open MonoidalCategory

variable [MonoidalCategory V]

@[simps! tensorUnit_V tensorObj_V tensorHom_hom whiskerLeft_hom whiskerRight_hom
  associator_hom_hom associator_inv_hom leftUnitor_hom_hom leftUnitor_inv_hom
  rightUnitor_hom_hom rightUnitor_inv_hom, reducible]
/--
Instance `instMonoidalCategory` / 实例 `instMonoidalCategory`

English:
instance instMonoidalCategory
  signature: : MonoidalCategory (Action V G) where
  body: Action.mk (X.V otimes Y.V) _
  tensorUnit := Action.mk (𝟙_ _) _
  __ := Monoidal.transport (Action.functorCategoryEquivalence _ _).symm

@[simp]

中文:
实例 instMonoidalCategory
  签名: : 幺半群范畴 (作用 V G) where
  定义体: Action.mk (X.V otimes Y.V) _
  tensorUnit := Action.mk (𝟙_ _) _
  __ := Monoidal.transport (Action.functorCategoryEquivalence _ _).symm

@[simp]

Depends on / 依赖: Action, Action.mk, otimes
-/
instance instMonoidalCategory : MonoidalCategory (Action V G) where
  tensorObj X Y := Action.mk (X.V otimes Y.V) _
  tensorUnit := Action.mk (𝟙_ _) _
  __ := Monoidal.transport (Action.functorCategoryEquivalence _ _).symm

@[simp]
/--
theorem `tensorUnit_ρ` / 定理 `tensorUnit_ρ`

English:
theorem tensorUnit_ρ
  given: {g : G}
  proof: rfl

@[simp]

中文:
定理 tensorUnit_ρ
  条件: {g : G}
  证明: rfl

@[simp]
-/
theorem tensorUnit_ρ {g : G} :
    @DFunLike.coe (G ->* End (𝟙_ V)) _ _ _ (𝟙_ (Action V G)).ρ g = 𝟙 (𝟙_ V) :=
  rfl

@[simp]
/--
theorem `tensor_ρ` / 定理 `tensor_ρ`

English:
theorem tensor_ρ
  given: {X Y : Action V G} {g : G}
  proof: rfl

中文:
定理 tensor_ρ
  条件: {X Y : 作用 V G} {g : G}
  证明: rfl
-/
theorem tensor_ρ {X Y : Action V G} {g : G} :
    @DFunLike.coe (G ->* End (X.V otimes Y.V)) _ _ _ (X otimes Y).ρ g = X.ρ g otimesₘ Y.ρ g :=
  rfl

/--
Definition of `tensorUnitIso` / `tensorUnitIso` 的定义

English:
definition tensorUnitIso
  signature: {X : V} (f : 𝟙_ V ≅ X)
  body: Action.mkIso f

中文:
定义 tensorUnitIso
  签名: {X : V} (f : 𝟙_ V ≅ X)
  定义体: Action.mkIso f

Depends on / 依赖: Action, Action.mkIso
-/
def tensorUnitIso {X : V} (f : 𝟙_ V ≅ X) : 𝟙_ (Action V G) ≅ Action.mk X 1 :=
  Action.mkIso f

variable (V G)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (Action.forget V G).Monoidal
  body: Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun _ _ => Iso.refl _ }

中文:
实例 :
  签名: (作用.forget V G).幺半群
  定义体: Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun _ _ => Iso.refl _ }

Depends on / 依赖: CoreMonoidal, Functor, Functor.CoreMonoidal.toMonoidal, Iso.refl, toMonoidal
-/
instance : (Action.forget V G).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun _ _ => Iso.refl _ }

open Functor.LaxMonoidal Functor.OplaxMonoidal

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `forget_ε` / 引理 `forget_ε`

English:
lemma forget_ε
  statement: ε (Action.forget V G) = 𝟙 _
  proof: rfl

中文:
引理 forget_ε
  结论: ε (作用.forget V G) = 𝟙 _
  证明: rfl
-/
@[simp] lemma forget_ε : ε (Action.forget V G) = 𝟙 _ := rfl
set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `forget_η` / 引理 `forget_η`

English:
lemma forget_η
  statement: η (Action.forget V G) = 𝟙 _
  proof: rfl

中文:
引理 forget_η
  结论: η (作用.forget V G) = 𝟙 _
  证明: rfl
-/
@[simp] lemma forget_η : η (Action.forget V G) = 𝟙 _ := rfl

variable {V G}

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `forget_μ` / 引理 `forget_μ`

English:
lemma forget_μ
  given: (X Y : Action V G)
  statement: μ (Action.forget V G) X Y = 𝟙 _
  proof: rfl

中文:
引理 forget_μ
  条件: (X Y : 作用 V G)
  结论: μ (作用.forget V G) X Y = 𝟙 _
  证明: rfl
-/
@[simp] lemma forget_μ (X Y : Action V G) : μ (Action.forget V G) X Y = 𝟙 _ := rfl
set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `forget_δ` / 引理 `forget_δ`

English:
lemma forget_δ
  given: (X Y : Action V G)
  statement: δ (Action.forget V G) X Y = 𝟙 _
  proof: rfl

中文:
引理 forget_δ
  条件: (X Y : 作用 V G)
  结论: δ (作用.forget V G) X Y = 𝟙 _
  证明: rfl
-/
@[simp] lemma forget_δ (X Y : Action V G) : δ (Action.forget V G) X Y = 𝟙 _ := rfl

variable (V G)

section

variable [BraidedCategory V]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: BraidedCategory (Action V G)
  body: .ofFaithful (Action.forget V G) fun X Y => mkIso (β_ _ _) fun g => by simp

@[simp]

中文:
实例 :
  签名: 辫范畴 (作用 V G)
  定义体: .ofFaithful (Action.forget V G) fun X Y => mkIso (β_ _ _) fun g => by simp

@[simp]

Depends on / 依赖: Action, Action.forget, forget, ofFaithful
-/
instance : BraidedCategory (Action V G) :=
  .ofFaithful (Action.forget V G) fun X Y => mkIso (β_ _ _) fun g => by simp

@[simp]
/--
theorem `β_hom_hom` / 定理 `β_hom_hom`

English:
theorem β_hom_hom
  given: {X Y : Action V G}
  statement: (β_ X Y).hom.hom = (β_ X.V Y.V).hom
  proof: rfl

@[simp]

中文:
定理 β_hom_hom
  条件: {X Y : 作用 V G}
  结论: (β_ X Y).hom.hom = (β_ X.V Y.V).hom
  证明: rfl

@[simp]
-/
theorem β_hom_hom {X Y : Action V G} : (β_ X Y).hom.hom = (β_ X.V Y.V).hom := rfl

@[simp]
/--
theorem `β_inv_hom` / 定理 `β_inv_hom`

English:
theorem β_inv_hom
  given: {X Y : Action V G}
  statement: (β_ X Y).inv.hom = (β_ X.V Y.V).inv
  proof: rfl

中文:
定理 β_inv_hom
  条件: {X Y : 作用 V G}
  结论: (β_ X Y).inv.hom = (β_ X.V Y.V).inv
  证明: rfl
-/
theorem β_inv_hom {X Y : Action V G} : (β_ X Y).inv.hom = (β_ X.V Y.V).inv := rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (Action.forget V G).Braided

中文:
实例 :
  签名: (作用.forget V G).辫
-/
instance : (Action.forget V G).Braided where

end

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SymmetricCategory
  signature: V] : SymmetricCategory (Action V G)
  body: .ofFaithful (Action.forget V G)

中文:
实例 [对称范畴
  签名: V] : 对称范畴 (作用 V G)
  定义体: .ofFaithful (Action.forget V G)

Depends on / 依赖: Action, Action.forget, forget, ofFaithful
-/
instance [SymmetricCategory V] : SymmetricCategory (Action V G) :=
  .ofFaithful (Action.forget V G)

section

variable [Preadditive V] [MonoidalPreadditive V]

attribute [local simp] MonoidalPreadditive.whiskerLeft_add MonoidalPreadditive.add_whiskerRight

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MonoidalPreadditive (Action V G)

中文:
实例 :
  签名: 幺半群预加性 (作用 V G)
-/
instance : MonoidalPreadditive (Action V G) where

variable {R : Type*} [Semiring R] [Linear R V] [MonoidalLinear R V]

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MonoidalLinear R (Action V G)

中文:
实例 :
  签名: 幺半群线性 R (作用 V G)
-/
instance : MonoidalLinear R (Action V G) where

end

noncomputable section

/--
Instance `FunctorCategoryEquivalence.functorMonoidal` / 实例 `FunctorCategoryEquivalence.functorMonoidal`

English:
instance FunctorCategoryEquivalence.functorMonoidal
  signature: :
  body: inferInstanceAs (Monoidal.equivalenceTransported
    (Action.functorCategoryEquivalence V G).symm).inverse.Monoidal

中文:
实例 FunctorCategoryEquivalence.functorMonoidal
  签名: :
  定义体: inferInstanceAs (Monoidal.equivalenceTransported
    (Action.functorCategoryEquivalence V G).symm).inverse.Monoidal

Depends on / 依赖: Monoidal
-/
instance FunctorCategoryEquivalence.functorMonoidal :
    (FunctorCategoryEquivalence.functor (V := V) (G := G)).Monoidal :=
  inferInstanceAs (Monoidal.equivalenceTransported
    (Action.functorCategoryEquivalence V G).symm).inverse.Monoidal

/--
Instance `functorCategoryEquivalenceFunctorMonoidal` / 实例 `functorCategoryEquivalenceFunctorMonoidal`

English:
instance functorCategoryEquivalenceFunctorMonoidal
  signature: :
  body: inferInstanceAs FunctorCategoryEquivalence.functor.Monoidal

中文:
实例 functorCategoryEquivalenceFunctorMonoidal
  签名: :
  定义体: inferInstanceAs FunctorCategoryEquivalence.functor.Monoidal

Depends on / 依赖: FunctorCategoryEquivalence, FunctorCategoryEquivalence.functor.Monoidal, Monoidal, functor
-/
instance functorCategoryEquivalenceFunctorMonoidal :
    (functorCategoryEquivalence V G).functor.Monoidal :=
  inferInstanceAs FunctorCategoryEquivalence.functor.Monoidal

/--
Instance `FunctorCategoryEquivalence.inverseMonoidal` / 实例 `FunctorCategoryEquivalence.inverseMonoidal`

English:
instance FunctorCategoryEquivalence.inverseMonoidal
  signature: :
  body: inferInstanceAs (Monoidal.equivalenceTransported
    (Action.functorCategoryEquivalence V G).symm).functor.Monoidal

中文:
实例 FunctorCategoryEquivalence.inverseMonoidal
  签名: :
  定义体: inferInstanceAs (Monoidal.equivalenceTransported
    (Action.functorCategoryEquivalence V G).symm).functor.Monoidal

Depends on / 依赖: Monoidal
-/
instance FunctorCategoryEquivalence.inverseMonoidal :
    (FunctorCategoryEquivalence.inverse (V := V) (G := G)).Monoidal :=
  inferInstanceAs (Monoidal.equivalenceTransported
    (Action.functorCategoryEquivalence V G).symm).functor.Monoidal

/--
Instance `functorCategoryEquivalenceInverseMonoidal` / 实例 `functorCategoryEquivalenceInverseMonoidal`

English:
instance functorCategoryEquivalenceInverseMonoidal
  signature: :
  body: inferInstanceAs FunctorCategoryEquivalence.inverse.Monoidal

@[simp]

中文:
实例 functorCategoryEquivalenceInverseMonoidal
  签名: :
  定义体: inferInstanceAs FunctorCategoryEquivalence.inverse.Monoidal

@[simp]

Depends on / 依赖: FunctorCategoryEquivalence, FunctorCategoryEquivalence.inverse.Monoidal, Monoidal, inverse
-/
instance functorCategoryEquivalenceInverseMonoidal :
    (functorCategoryEquivalence V G).inverse.Monoidal :=
  inferInstanceAs FunctorCategoryEquivalence.inverse.Monoidal

@[simp]
/--
lemma `FunctorCategoryEquivalence.functor_ε` / 引理 `FunctorCategoryEquivalence.functor_ε`

English:
lemma FunctorCategoryEquivalence.functor_ε
  proof: rfl

@[simp]

中文:
引理 FunctorCategoryEquivalence.functor_ε
  证明: rfl

@[simp]
-/
lemma FunctorCategoryEquivalence.functor_ε :
    ε (FunctorCategoryEquivalence.functor (V := V) (G := G)) = 𝟙 _ := rfl

@[simp]
/--
lemma `FunctorCategoryEquivalence.functor_η` / 引理 `FunctorCategoryEquivalence.functor_η`

English:
lemma FunctorCategoryEquivalence.functor_η
  proof: rfl

@[simp]

中文:
引理 FunctorCategoryEquivalence.functor_η
  证明: rfl

@[simp]
-/
lemma FunctorCategoryEquivalence.functor_η :
    η (FunctorCategoryEquivalence.functor (V := V) (G := G)) = 𝟙 _ := rfl

@[simp]
/--
lemma `FunctorCategoryEquivalence.functor_μ` / 引理 `FunctorCategoryEquivalence.functor_μ`

English:
lemma FunctorCategoryEquivalence.functor_μ
  given: (A B : Action V G)
  proof: rfl

@[simp]

中文:
引理 FunctorCategoryEquivalence.functor_μ
  条件: (A B : 作用 V G)
  证明: rfl

@[simp]
-/
lemma FunctorCategoryEquivalence.functor_μ (A B : Action V G) :
    μ FunctorCategoryEquivalence.functor A B = 𝟙 _ := rfl

@[simp]
/--
lemma `FunctorCategoryEquivalence.functor_δ` / 引理 `FunctorCategoryEquivalence.functor_δ`

English:
lemma FunctorCategoryEquivalence.functor_δ
  given: (A B : Action V G)
  proof: rfl

中文:
引理 FunctorCategoryEquivalence.functor_δ
  条件: (A B : 作用 V G)
  证明: rfl
-/
lemma FunctorCategoryEquivalence.functor_δ (A B : Action V G) :
    δ FunctorCategoryEquivalence.functor A B = 𝟙 _ := rfl


variable (H : Type*) [Group H]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [RightRigidCategory
  signature: V] : RightRigidCategory (SingleObj H ⥤ V)
  body: by
  infer_instance

中文:
实例 [RightRigid范畴
  签名: V] : RightRigid范畴 (SingleObj H ⥤ V)
  定义体: by
  infer_instance

Depends on / 依赖: infer_instance
-/
instance [RightRigidCategory V] : RightRigidCategory (SingleObj H ⥤ V) := by
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [RightRigidCategory
  signature: V] : RightRigidCategory (Action V H)
  body: rightRigidCategoryOfEquivalence
    (functorCategoryEquivalence V H).toAdjunction

中文:
实例 [RightRigid范畴
  签名: V] : RightRigid范畴 (作用 V H)
  定义体: rightRigidCategoryOfEquivalence
    (functorCategoryEquivalence V H).toAdjunction

Depends on / 依赖: functorCategoryEquivalence, rightRigidCategoryOfEquivalence, toAdjunction
-/
instance [RightRigidCategory V] : RightRigidCategory (Action V H) :=
  rightRigidCategoryOfEquivalence
    (functorCategoryEquivalence V H).toAdjunction

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LeftRigidCategory
  signature: V] : LeftRigidCategory (SingleObj H ⥤ V)
  body: by
  infer_instance

中文:
实例 [LeftRigid范畴
  签名: V] : LeftRigid范畴 (SingleObj H ⥤ V)
  定义体: by
  infer_instance

Depends on / 依赖: infer_instance
-/
instance [LeftRigidCategory V] : LeftRigidCategory (SingleObj H ⥤ V) := by
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LeftRigidCategory
  signature: V] : LeftRigidCategory (Action V H)
  body: leftRigidCategoryOfEquivalence (functorCategoryEquivalence V H).toAdjunction

中文:
实例 [LeftRigid范畴
  签名: V] : LeftRigid范畴 (作用 V H)
  定义体: leftRigidCategoryOfEquivalence (functorCategoryEquivalence V H).toAdjunction

Depends on / 依赖: functorCategoryEquivalence, leftRigidCategoryOfEquivalence, toAdjunction
-/
instance [LeftRigidCategory V] : LeftRigidCategory (Action V H) :=
  leftRigidCategoryOfEquivalence (functorCategoryEquivalence V H).toAdjunction

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [RigidCategory
  signature: V] : RigidCategory (SingleObj H ⥤ V)
  body: by
  infer_instance

中文:
实例 [Rigid范畴
  签名: V] : Rigid范畴 (SingleObj H ⥤ V)
  定义体: by
  infer_instance

Depends on / 依赖: infer_instance
-/
instance [RigidCategory V] : RigidCategory (SingleObj H ⥤ V) := by
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [RigidCategory
  signature: V] : RigidCategory (Action V H)
  body: rigidCategoryOfEquivalence (functorCategoryEquivalence V H).toAdjunction

中文:
实例 [Rigid范畴
  签名: V] : Rigid范畴 (作用 V H)
  定义体: rigidCategoryOfEquivalence (functorCategoryEquivalence V H).toAdjunction

Depends on / 依赖: functorCategoryEquivalence, rigidCategoryOfEquivalence, toAdjunction
-/
instance [RigidCategory V] : RigidCategory (Action V H) :=
  rigidCategoryOfEquivalence (functorCategoryEquivalence V H).toAdjunction

variable {V H}
variable (X : Action V H)

@[simp]
/--
theorem `rightDual_v` / 定理 `rightDual_v`

English:
theorem rightDual_v
  given: [RightRigidCategory V]
  statement: Xᘁ.V = X.Vᘁ
  proof: rfl

@[simp]

中文:
定理 rightDual_v
  条件: [RightRigid范畴 V]
  结论: Xᘁ.V = X.Vᘁ
  证明: rfl

@[simp]

Depends on / 依赖: fun_prop
-/
theorem rightDual_v [RightRigidCategory V] : Xᘁ.V = X.Vᘁ :=
  rfl

@[simp]
/--
theorem `leftDual_v` / 定理 `leftDual_v`

English:
theorem leftDual_v
  given: [LeftRigidCategory V]
  statement: (ᘁX).V = ᘁX.V
  proof: rfl

中文:
定理 leftDual_v
  条件: [LeftRigid范畴 V]
  结论: (ᘁX).V = ᘁX.V
  证明: rfl
-/
theorem leftDual_v [LeftRigidCategory V] : (ᘁX).V = ᘁX.V :=
  rfl

/--
theorem `rightDual_ρ` / 定理 `rightDual_ρ`

English:
theorem rightDual_ρ
  given: [RightRigidCategory V] (h : H)
  statement: Xᘁ.ρ h = (X.ρ (h⁻¹ : H))ᘁ
  proof: by
  rw [← SingleObj.inv_as_inv]; rfl

中文:
定理 rightDual_ρ
  条件: [RightRigid范畴 V] (h : H)
  结论: Xᘁ.ρ h = (X.ρ (h⁻¹ : H))ᘁ
  证明: by
  rw [← SingleObj.inv_as_inv]; rfl

Depends on / 依赖: SingleObj, SingleObj.inv_as_inv, inv_as_inv
-/
theorem rightDual_ρ [RightRigidCategory V] (h : H) : Xᘁ.ρ h = (X.ρ (h⁻¹ : H))ᘁ := by
  rw [← SingleObj.inv_as_inv]; rfl

/--
theorem `leftDual_ρ` / 定理 `leftDual_ρ`

English:
theorem leftDual_ρ
  given: [LeftRigidCategory V] (h : H)
  statement: (ᘁX).ρ h = ᘁX.ρ (h⁻¹ : H)
  proof: by
  rw [← SingleObj.inv_as_inv]; rfl

中文:
定理 leftDual_ρ
  条件: [LeftRigid范畴 V] (h : H)
  结论: (ᘁX).ρ h = ᘁX.ρ (h⁻¹ : H)
  证明: by
  rw [← SingleObj.inv_as_inv]; rfl

Depends on / 依赖: SingleObj, SingleObj.inv_as_inv, inv_as_inv
-/
theorem leftDual_ρ [LeftRigidCategory V] (h : H) : (ᘁX).ρ h = ᘁX.ρ (h⁻¹ : H) := by
  rw [← SingleObj.inv_as_inv]; rfl

end

end Monoidal

section

open MonoidalCategory

variable (G : Type u)

/-- The natural isomorphism of `G`-sets `Gⁿ⁺¹ ≅ G × Gⁿ`, where `G` acts by left multiplication on
each factor. -/
@[simps! hom_hom inv_hom]
/--
Definition of `diagonalSuccIsoTensorDiagonal` / `diagonalSuccIsoTensorDiagonal` 的定义

English:
definition diagonalSuccIsoTensorDiagonal
  signature: [Monoid G] (n : Nat)
  body: mkIso (Fin.consEquiv _).symm.toIso fun _ => rfl

中文:
定义 diagonalSuccIsoTensorDiagonal
  签名: [幺半群 G] (n : 自然数)
  定义体: mkIso (Fin.consEquiv _).symm.toIso fun _ => rfl

Depends on / 依赖: Fin.consEquiv, consEquiv, symm.toIso
-/
noncomputable def diagonalSuccIsoTensorDiagonal [Monoid G] (n : Nat) :
    diagonal G (n + 1) ≅ leftRegular G otimes diagonal G n :=
  mkIso (Fin.consEquiv _).symm.toIso fun _ => rfl

variable [Group G]

set_option backward.isDefEq.respectTransparency.types false in
/-- Given `X : Action (Type u) G` for `G` a group, then `G × X` (with `G` acting as left
multiplication on the first factor and by `X.ρ` on the second) is isomorphic as a `G`-set to
`G × X` (with `G` acting as left multiplication on the first factor and trivially on the second).
The isomorphism is given by `(g, x) ↦ (g, g⁻¹ • x)`. -/
@[simps! hom_hom inv_hom]
/--
Definition of `leftRegularTensorIso` / `leftRegularTensorIso` 的定义

English:
definition leftRegularTensorIso
  signature: (X : Action (Type u) G)
  body: mkIso (Equiv.toIso {
    toFun g := ⟨g.1, (X.ρ (g.1⁻¹ : G) g.2 : X.V)⟩
    invFun g := ⟨g.1, X.ρ g.1 g.2⟩
left_inv _ := Prod.ext rfl by simp
right_inv _ := Prod.ext rfl by simp }) <| fun _ => by
      ext _
      simp only [tensorObj_V, tensor_ρ]
      simp [types_tensorObj_def]
      rfl

中文:
定义 leftRegularTensorIso
  签名: (X : 作用 (类型u) G)
  定义体: mkIso (Equiv.toIso {
    toFun g := ⟨g.1, (X.ρ (g.1⁻¹ : G) g.2 : X.V)⟩
    invFun g := ⟨g.1, X.ρ g.1 g.2⟩
left_inv _ := Prod.ext rfl by simp
right_inv _ := Prod.ext rfl by simp }) <| fun _ => by
      ext _
      simp only [tensorObj_V, tensor_ρ]
      simp [types_tensorObj_def]
      rfl

Depends on / 依赖: Equiv.toIso, Prod.ext, invFun, left_inv, right_inv, tensorObj_V, types_tensorObj_def
-/
noncomputable def leftRegularTensorIso (X : Action (Type u) G) :
    leftRegular G otimes X ≅ leftRegular G otimes trivial G X.V :=
  mkIso (Equiv.toIso {
    toFun g := ⟨g.1, (X.ρ (g.1⁻¹ : G) g.2 : X.V)⟩
    invFun g := ⟨g.1, X.ρ g.1 g.2⟩
left_inv _ := Prod.ext rfl by simp
right_inv _ := Prod.ext rfl by simp }) <| fun _ => by
      ext _
      simp only [tensorObj_V, tensor_ρ]
      simp [types_tensorObj_def]
      rfl


/--
Definition of `diagonalSuccIsoTensorTrivial` / `diagonalSuccIsoTensorTrivial` 的定义

English:
definition diagonalSuccIsoTensorTrivial
  signature: :

中文:
定义 diagonalSuccIsoTensorTrivial
  签名: :
-/
noncomputable def diagonalSuccIsoTensorTrivial :
    forall n : Nat, diagonal G (n + 1) ≅ leftRegular G otimes trivial G (Fin n -> G)
  | 0 =>
    diagonalOneIsoLeftRegular G ≪≫
      (ρ_ _).symm ≪≫ tensorIso (Iso.refl _) (tensorUnitIso (Equiv.ofUnique PUnit _).toIso)
  | n + 1 =>
    diagonalSuccIsoTensorDiagonal _ _ ≪≫
      tensorIso (Iso.refl _) (diagonalSuccIsoTensorTrivial n) ≪≫
        leftRegularTensorIso _ _ ≪≫
          tensorIso (Iso.refl _)
            (mkIso (Fin.insertNthEquiv (fun _ => G) 0).toIso fun _ => rfl)

variable {G}

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `diagonalSuccIsoTensorTrivial_hom_hom_apply` / 定理 `diagonalSuccIsoTensorTrivial_hom_hom_apply`

English:
theorem diagonalSuccIsoTensorTrivial_hom_hom_apply
  given: {n : Nat} (f : Fin (n + 1) -> G)
  proof: by
  induction n with
  | zero => exact Prod.ext rfl (funext fun x => Fin.elim0 x)
  | succ n hn =>
    refine Prod.ext rfl (funext fun x => ?_)
    induction x using Fin.cases
    <;> simp_all [diagonalSuccIsoTensorTrivial, types_tensorObj_def]
    <;> rfl

中文:
定理 diagonalSuccIsoTensorTrivial_hom_hom_apply
  条件: {n : 自然数} (f : 有限集 (n + 1) -> G)
  证明: by
  induction n with
  | zero => exact Prod.ext rfl (funext fun x => Fin.elim0 x)
  | succ n hn =>
    refine Prod.ext rfl (funext fun x => ?_)
    induction x using Fin.cases
    <;> simp_all [diagonalSuccIsoTensorTrivial, types_tensorObj_def]
    <;> rfl

Depends on / 依赖: Fin.cases, Fin.elim0, Prod.ext, diagonalSuccIsoTensorTrivial, types_tensorObj_def
-/
theorem diagonalSuccIsoTensorTrivial_hom_hom_apply {n : Nat} (f : Fin (n + 1) -> G) :
    dsimp% (diagonalSuccIsoTensorTrivial G n).hom.hom f =
      (f 0, fun i => (f (Fin.castSucc i))⁻¹ * f i.succ) := by
  induction n with
  | zero => exact Prod.ext rfl (funext fun x => Fin.elim0 x)
  | succ n hn =>
    refine Prod.ext rfl (funext fun x => ?_)
    induction x using Fin.cases
    <;> simp_all [diagonalSuccIsoTensorTrivial, types_tensorObj_def]
    <;> rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `diagonalSuccIsoTensorTrivial_inv_hom_apply` / 定理 `diagonalSuccIsoTensorTrivial_inv_hom_apply`

English:
theorem diagonalSuccIsoTensorTrivial_inv_hom_apply
  given: {n : Nat} (g : G) (f : Fin n -> G)
  proof: by
  induction n generalizing g with
  | zero =>
    funext (x : Fin 1)
    simp [diagonalSuccIsoTensorTrivial, diagonalOneIsoLeftRegular, Subsingleton.elim x 0,
      ofMulAction_V, types_tensorObj_def, types_tensorUnit_def]
  | succ n hn =>
    funext x
    induction x using Fin.cases with
    | zero => simp; rfl
    | succ i =>
      simpa [diagonalSuccIsoTensorTrivial, types_tensorObj_def, mul_assoc, Fin.partialProd_succ',
        ofMulAction_V] using! congrFun (hn (g * f 0) (Fin.tail f)) i

中文:
定理 diagonalSuccIsoTensorTrivial_inv_hom_apply
  条件: {n : 自然数} (g : G) (f : 有限集 n -> G)
  证明: by
  induction n generalizing g with
  | zero =>
    funext (x : Fin 1)
    simp [diagonalSuccIsoTensorTrivial, diagonalOneIsoLeftRegular, Subsingleton.elim x 0,
      ofMulAction_V, types_tensorObj_def, types_tensorUnit_def]
  | succ n hn =>
    funext x
    induction x using Fin.cases with
    | zero => simp; rfl
    | succ i =>
      simpa [diagonalSuccIsoTensorTrivial, types_tensorObj_def, mul_assoc, Fin.partialProd_succ',
        ofMulAction_V] using! congrFun (hn (g * f 0) (Fin.tail f)) i

Depends on / 依赖: Fin.cases, Fin.partialProd_succ, Fin.tail, Subsingleton, Subsingleton.elim, diagonalOneIsoLeftRegular, diagonalSuccIsoTensorTrivial, generalizing, mul_assoc, ofMulAction_V, partialProd_succ, types_tensorObj_def, types_tensorUnit_def
-/
theorem diagonalSuccIsoTensorTrivial_inv_hom_apply {n : Nat} (g : G) (f : Fin n -> G) :
    dsimp% (diagonalSuccIsoTensorTrivial G n).inv.hom (g, f) =
      (g • Fin.partialProd f : Fin (n + 1) -> G) := by
  induction n generalizing g with
  | zero =>
    funext (x : Fin 1)
    simp [diagonalSuccIsoTensorTrivial, diagonalOneIsoLeftRegular, Subsingleton.elim x 0,
      ofMulAction_V, types_tensorObj_def, types_tensorUnit_def]
  | succ n hn =>
    funext x
    induction x using Fin.cases with
    | zero => simp; rfl
    | succ i =>
      simpa [diagonalSuccIsoTensorTrivial, types_tensorObj_def, mul_assoc, Fin.partialProd_succ',
        ofMulAction_V] using! congrFun (hn (g * f 0) (Fin.tail f)) i

end

end Action

namespace CategoryTheory.Functor

open Action

variable {W : Type*} [Category* W] [MonoidalCategory V] [MonoidalCategory W]
  (F : V ⥤ W)

open Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [F.LaxMonoidal]
  signature: : (F.mapAction G).LaxMonoidal where
  body: { hom := ε F
      comm := fun g => by
        dsimp [FunctorCategoryEquivalence.inverse, Functor.mapAction]
        rw [Category.id_comp]; rw [F.map_id]; rw [Category.comp_id] }
  μ X Y :=
    { hom := μ F X.V Y.V
      comm := fun g => μ_natural F (X.ρ g) (Y.ρ g) }
  μ_natural_left _ _ := by ext; simp
  μ_natural_right _ _ := by ext; simp
  associativity _ _ _ := by ext; simp
  left_unitality _ := by ext; simp
  right_unitality _ := by ext; simp

中文:
实例 [F.松弛幺半群]
  签名: : (F.mapAction G).松弛幺半群 where
  定义体: { hom := ε F
      comm := fun g => by
        dsimp [FunctorCategoryEquivalence.inverse, Functor.mapAction]
        rw [Category.id_comp]; rw [F.map_id]; rw [Category.comp_id] }
  μ X Y :=
    { hom := μ F X.V Y.V
      comm := fun g => μ_natural F (X.ρ g) (Y.ρ g) }
  μ_natural_left _ _ := by ext; simp
  μ_natural_right _ _ := by ext; simp
  associativity _ _ _ := by ext; simp
  left_unitality _ := by ext; simp
  right_unitality _ := by ext; simp

Depends on / 依赖: Category, Category.comp_id, Category.id_comp, F.map_id, Functor, Functor.mapAction, FunctorCategoryEquivalence, FunctorCategoryEquivalence.inverse, associativity, comp_id, id_comp, inverse, left_unitality, mapAction, map_id, right_unitality
-/
instance [F.LaxMonoidal] : (F.mapAction G).LaxMonoidal where
  ε :=
    { hom := ε F
      comm := fun g => by
        dsimp [FunctorCategoryEquivalence.inverse, Functor.mapAction]
        rw [Category.id_comp]; rw [F.map_id]; rw [Category.comp_id] }
  μ X Y :=
    { hom := μ F X.V Y.V
      comm := fun g => μ_natural F (X.ρ g) (Y.ρ g) }
  μ_natural_left _ _ := by ext; simp
  μ_natural_right _ _ := by ext; simp
  associativity _ _ _ := by ext; simp
  left_unitality _ := by ext; simp
  right_unitality _ := by ext; simp

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `mapAction_ε_hom` / 引理 `mapAction_ε_hom`

English:
lemma mapAction_ε_hom
  given: [F.LaxMonoidal]
  statement: (ε (F.mapAction G)).hom = ε F
  proof: rfl

中文:
引理 mapAction_ε_hom
  条件: [F.松弛幺半群]
  结论: (ε (F.mapAction G)).hom = ε F
  证明: rfl
-/
lemma mapAction_ε_hom [F.LaxMonoidal] : (ε (F.mapAction G)).hom = ε F := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `mapAction_μ_hom` / 引理 `mapAction_μ_hom`

English:
lemma mapAction_μ_hom
  given: [F.LaxMonoidal] (X Y : Action V G)
  proof: rfl

中文:
引理 mapAction_μ_hom
  条件: [F.松弛幺半群] (X Y : 作用 V G)
  证明: rfl
-/
lemma mapAction_μ_hom [F.LaxMonoidal] (X Y : Action V G) :
    (μ (F.mapAction G) X Y).hom = μ F X.V Y.V := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [F.OplaxMonoidal]
  signature: : (F.mapAction G).OplaxMonoidal where
  body: { hom := η F
      comm := fun g => by
        dsimp [FunctorCategoryEquivalence.inverse, Functor.mapAction]
        rw [map_id]; rw [Category.id_comp]; rw [Category.comp_id] }
  δ X Y :=
    { hom := δ F X.V Y.V
      comm := fun g => (δ_natural F (X.ρ g) (Y.ρ g)).symm }
  δ_natural_left _ _ := by ext; simp
  δ_natural_right _ _ := by ext; simp
  oplax_associativity _ _ _ := by ext; simp
  oplax_left_unitality _ := by ext; simp
  oplax_right_unitality _ := by ext; simp

中文:
实例 [F.反松弛幺半群]
  签名: : (F.mapAction G).反松弛幺半群 where
  定义体: { hom := η F
      comm := fun g => by
        dsimp [FunctorCategoryEquivalence.inverse, Functor.mapAction]
        rw [map_id]; rw [Category.id_comp]; rw [Category.comp_id] }
  δ X Y :=
    { hom := δ F X.V Y.V
      comm := fun g => (δ_natural F (X.ρ g) (Y.ρ g)).symm }
  δ_natural_left _ _ := by ext; simp
  δ_natural_right _ _ := by ext; simp
  oplax_associativity _ _ _ := by ext; simp
  oplax_left_unitality _ := by ext; simp
  oplax_right_unitality _ := by ext; simp

Depends on / 依赖: Category, Category.comp_id, Category.id_comp, Functor, Functor.mapAction, FunctorCategoryEquivalence, FunctorCategoryEquivalence.inverse, comp_id, id_comp, inverse, mapAction, map_id, oplax_associativity, oplax_left_unitality, oplax_right_unitality
-/
instance [F.OplaxMonoidal] : (F.mapAction G).OplaxMonoidal where
  η :=
    { hom := η F
      comm := fun g => by
        dsimp [FunctorCategoryEquivalence.inverse, Functor.mapAction]
        rw [map_id]; rw [Category.id_comp]; rw [Category.comp_id] }
  δ X Y :=
    { hom := δ F X.V Y.V
      comm := fun g => (δ_natural F (X.ρ g) (Y.ρ g)).symm }
  δ_natural_left _ _ := by ext; simp
  δ_natural_right _ _ := by ext; simp
  oplax_associativity _ _ _ := by ext; simp
  oplax_left_unitality _ := by ext; simp
  oplax_right_unitality _ := by ext; simp

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `mapAction_η_hom` / 引理 `mapAction_η_hom`

English:
lemma mapAction_η_hom
  given: [F.OplaxMonoidal]
  statement: (η (F.mapAction G)).hom = η F
  proof: rfl

中文:
引理 mapAction_η_hom
  条件: [F.反松弛幺半群]
  结论: (η (F.mapAction G)).hom = η F
  证明: rfl
-/
lemma mapAction_η_hom [F.OplaxMonoidal] : (η (F.mapAction G)).hom = η F := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `mapAction_δ_hom` / 引理 `mapAction_δ_hom`

English:
lemma mapAction_δ_hom
  given: [F.OplaxMonoidal] (X Y : Action V G)
  proof: rfl

中文:
引理 mapAction_δ_hom
  条件: [F.反松弛幺半群] (X Y : 作用 V G)
  证明: rfl
-/
lemma mapAction_δ_hom [F.OplaxMonoidal] (X Y : Action V G) :
    (δ (F.mapAction G) X Y).hom = δ F X.V Y.V := rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [F.Monoidal]
  signature: : (F.mapAction G).Monoidal where
  body: by ext; dsimp; rw [η_ε]
  ε_η := by ext; dsimp; rw [ε_η]
  μ_δ _ _ := by ext; dsimp; rw [μ_δ]
  δ_μ _ _ := by ext; dsimp; rw [δ_μ]

中文:
实例 [F.幺半群]
  签名: : (F.mapAction G).幺半群 where
  定义体: by ext; dsimp; rw [η_ε]
  ε_η := by ext; dsimp; rw [ε_η]
  μ_δ _ _ := by ext; dsimp; rw [μ_δ]
  δ_μ _ _ := by ext; dsimp; rw [δ_μ]
-/
instance [F.Monoidal] : (F.mapAction G).Monoidal where
  η_ε := by ext; dsimp; rw [η_ε]
  ε_η := by ext; dsimp; rw [ε_η]
  μ_δ _ _ := by ext; dsimp; rw [μ_δ]
  δ_μ _ _ := by ext; dsimp; rw [δ_μ]

end CategoryTheory.Functor
