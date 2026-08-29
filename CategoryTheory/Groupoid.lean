/-
Copyright (c) 2018 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Kim Morrison, David Wärn
-/
module

public import Mathlib.Combinatorics.Quiver.Symmetric
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Basic

/-!
# Groupoids

We define `Groupoid` as a typeclass extending `Category`,
asserting that all morphisms have inverses.

The instance `IsIso.ofGroupoid (f : X ⟶ Y) : IsIso f` means that you can then write
`inv f` to access the inverse of any morphism `f`.

`Groupoid.isoEquivHom : (X ≅ Y) ≃ (X ⟶ Y)` provides the equivalence between
isomorphisms and morphisms in a groupoid.

We provide a (non-instance) constructor `Groupoid.ofIsIso` from an existing category
with `IsIso f` for every `f`.

## See also

See also `CategoryTheory.Core` for the groupoid of isomorphisms in a category.
-/

@[expose] public section

namespace CategoryTheory

universe v v₂ u u₂

-- morphism levels before object levels. See note [category theory universes].
/--
Definition of `Groupoid` / `Groupoid` 的定义

English:
class Groupoid
  parameters: (obj : Type u)
  extends: Category.{v} obj
  axioms and operations (3):
    - inv : forall {X Y : obj}, (X ⟶ Y) -> (Y ⟶ X)
    - inv_comp : forall {X Y : obj} (f : X ⟶ Y), comp (inv f) f = id Y  [default: by cat_disch]
    - comp_inv : forall {X Y : obj} (f : X ⟶ Y), comp f (inv f) = id X  [default: by cat_disch]

中文:
类 Groupoid
  参数: (obj : 类型u)
  继承: Category.{v} obj
  公理与运算 (3 个):
    - inv : 对任意 {X Y : obj}, (X ⟶ Y) -> (Y ⟶ X)
    - inv_comp : 对任意 {X Y : obj} (f : X ⟶ Y), comp (inv f) f = id Y  [默认: by cat_disch]
    - comp_inv : 对任意 {X Y : obj} (f : X ⟶ Y), comp f (inv f) = id X  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
class Groupoid (obj : Type u) : Type max u (v + 1) extends Category.{v} obj where
  /-- The inverse morphism -/
  inv : forall {X Y : obj}, (X ⟶ Y) -> (Y ⟶ X)
  /-- `inv f` composed `f` is the identity -/
  inv_comp : forall {X Y : obj} (f : X ⟶ Y), comp (inv f) f = id Y := by cat_disch
  /-- `f` composed with `inv f` is the identity -/
  comp_inv : forall {X Y : obj} (f : X ⟶ Y), comp f (inv f) = id X := by cat_disch

initialize_simps_projections Groupoid (-Hom)

/--
Definition of `LargeGroupoid` / `LargeGroupoid` 的定义

English:
abbreviation LargeGroupoid
  signature: (C : Type (u + 1))
  body: Groupoid.{u} C

中文:
缩写 LargeGroupoid
  签名: (C : Type (u + 1))
  定义体: Groupoid.{u} C

Depends on / 依赖: Groupoid
-/
abbrev LargeGroupoid (C : Type (u + 1)) : Type (u + 1) :=
  Groupoid.{u} C

/--
Definition of `SmallGroupoid` / `SmallGroupoid` 的定义

English:
abbreviation SmallGroupoid
  signature: (C : Type u)
  body: Groupoid.{u} C

中文:
缩写 SmallGroupoid
  签名: (C : 类型u)
  定义体: Groupoid.{u} C

Depends on / 依赖: Groupoid
-/
abbrev SmallGroupoid (C : Type u) : Type (u + 1) :=
  Groupoid.{u} C

section

variable {C : Type u} [Groupoid.{v} C] {X Y : C}

-- see Note [lower instance priority]
instance (priority := 100) IsIso.of_groupoid (f : X ⟶ Y) : IsIso f :=
  ⟨⟨Groupoid.inv f, Groupoid.comp_inv f, Groupoid.inv_comp f⟩⟩

@[simp]
/--
theorem `Groupoid.inv_eq_inv` / 定理 `Groupoid.inv_eq_inv`

English:
theorem Groupoid.inv_eq_inv
  given: (f : X ⟶ Y)
  statement: Groupoid.inv f = CategoryTheory.inv f
  proof: IsIso.eq_inv_of_hom_inv_id Groupoid.comp_inv f

中文:
定理 Groupoid.inv_eq_inv
  条件: (f : X ⟶ Y)
  结论: Groupoid.inv f = CategoryTheory.inv f
  证明: IsIso.eq_inv_of_hom_inv_id Groupoid.comp_inv f

Depends on / 依赖: Groupoid, Groupoid.comp_inv, IsIso.eq_inv_of_hom_inv_id, comp_inv, eq_inv_of_hom_inv_id
-/
theorem Groupoid.inv_eq_inv (f : X ⟶ Y) : Groupoid.inv f = CategoryTheory.inv f :=
IsIso.eq_inv_of_hom_inv_id Groupoid.comp_inv f

/-- `Groupoid.inv` is involutive. -/
@[simps]
/--
Definition of `Groupoid.invEquiv` / `Groupoid.invEquiv` 的定义

English:
definition Groupoid.invEquiv
  signature: : (X ⟶ Y) ≃ (Y ⟶ X)
  body: ⟨Groupoid.inv, Groupoid.inv, fun f => by simp, fun f => by simp⟩

中文:
定义 Groupoid.invEquiv
  签名: : (X ⟶ Y) ≃ (Y ⟶ X)
  定义体: ⟨Groupoid.inv, Groupoid.inv, fun f => by simp, fun f => by simp⟩

Depends on / 依赖: Groupoid, Groupoid.inv
-/
def Groupoid.invEquiv : (X ⟶ Y) ≃ (Y ⟶ X) :=
  ⟨Groupoid.inv, Groupoid.inv, fun f => by simp, fun f => by simp⟩

instance (priority := 100) groupoidHasInvolutiveReverse : Quiver.HasInvolutiveReverse C where
  reverse' f := Groupoid.inv f
  inv' f := by
    dsimp [Quiver.reverse]
    simp

@[simp]
/--
theorem `Groupoid.reverse_eq_inv` / 定理 `Groupoid.reverse_eq_inv`

English:
theorem Groupoid.reverse_eq_inv
  given: (f : X ⟶ Y)
  statement: Quiver.reverse f = Groupoid.inv f
  proof: rfl

中文:
定理 Groupoid.reverse_eq_inv
  条件: (f : X ⟶ Y)
  结论: Quiver.reverse f = Groupoid.inv f
  证明: rfl
-/
theorem Groupoid.reverse_eq_inv (f : X ⟶ Y) : Quiver.reverse f = Groupoid.inv f :=
  rfl

set_option backward.defeqAttrib.useBackward true in
/--
Instance `functorMapReverse` / 实例 `functorMapReverse`

English:
instance functorMapReverse
  signature: {D : Type*} [Groupoid D] (F : C ⥤ D)
  body: by simp

中文:
实例 functorMapReverse
  签名: {D : 类型} [Groupoid D] (F : C ⥤ D)
  定义体: by simp

Depends on / 依赖: Fan.proj, opCoproductIsoProduct
-/
instance functorMapReverse {D : Type*} [Groupoid D] (F : C ⥤ D) : F.toPrefunctor.MapReverse where
  map_reverse' f := by simp

variable (X Y)

/-- In a groupoid, isomorphisms are equivalent to morphisms. -/
@[simps!]
/--
Definition of `Groupoid.isoEquivHom` / `Groupoid.isoEquivHom` 的定义

English:
definition Groupoid.isoEquivHom
  signature: : (X ≅ Y) ≃ (X ⟶ Y) where
  body: Iso.hom
  invFun f := { hom := f, inv := Groupoid.inv f }

中文:
定义 Groupoid.isoEquivHom
  签名: : (X ≅ Y) ≃ (X ⟶ Y) where
  定义体: Iso.hom
  invFun f := { hom := f, inv := Groupoid.inv f }

Depends on / 依赖: Iso.hom
-/
def Groupoid.isoEquivHom : (X ≅ Y) ≃ (X ⟶ Y) where
  toFun := Iso.hom
  invFun f := { hom := f, inv := Groupoid.inv f }

variable (C)

set_option backward.defeqAttrib.useBackward true in
/-- The equivalence from a groupoid `C` to its opposite sending every morphism to its inverse. -/
@[simps]
/--
Definition of `Groupoid.invEquivalence` / `Groupoid.invEquivalence` 的定义

English:
definition Groupoid.invEquivalence
  signature: : C ≌ Cᵒᵖ where
  body: Opposite.op
  functor.map {_ _} f := (inv f).op
  inverse.obj := Opposite.unop
  inverse.map {x y} f := inv f.unop
  unitIso := NatIso.ofComponents (fun _ => .refl _)
  counitIso := NatIso.ofComponents (fun _ => .refl _)

中文:
定义 Groupoid.invEquivalence
  签名: : C ≌ Cᵒᵖ where
  定义体: Opposite.op
  functor.map {_ _} f := (inv f).op
  inverse.obj := Opposite.unop
  inverse.map {x y} f := inv f.unop
  unitIso := NatIso.ofComponents (fun _ => .refl _)
  counitIso := NatIso.ofComponents (fun _ => .refl _)

Depends on / 依赖: Cofan.IsColimit.op, IsColimit, IsLimit, IsLimit.conePointUniqueUpToIso_inv_comp, Opposite, Opposite.op, conePointUniqueUpToIso_inv_comp
-/
def Groupoid.invEquivalence : C ≌ Cᵒᵖ where
  functor.obj := Opposite.op
  functor.map {_ _} f := (inv f).op
  inverse.obj := Opposite.unop
  inverse.map {x y} f := inv f.unop
  unitIso := NatIso.ofComponents (fun _ => .refl _)
  counitIso := NatIso.ofComponents (fun _ => .refl _)

end

section

/--
Definition of `IsGroupoid` / `IsGroupoid` 的定义

English:
class IsGroupoid
  parameters: (C : Type u) [Category.{v} C]
  axioms and operations (1):
    - all_isIso({X Y : C} (f : X ⟶ Y)) : IsIso f  [default: by infer_instance]

中文:
类 IsGroupoid
  参数: (C : 类型u) [Category.{v} C]
  公理与运算 (1 个):
    - all_isIso({X Y : C} (f : X ⟶ Y)) : IsIso f  [默认: by infer_instance]

Depends on / 依赖: Category, Category.assoc, Discrete, Discrete.functor_obj, IsColimit, IsColimit.comp_coconePointUniqueUpToIso_inv, Iso.hom_inv_id_assoc, Iso.op_inv, Quiver, Quiver.Hom.op_inj, Quiver.Hom.op_unop, Quiver.Hom.unop_inj, Quiver.Hom.unop_op, _inv_comp_inj, comp_coconePointUniqueUpToIso_inv, functor_obj, hom_ext, hom_inv_id_assoc, infer_instance, opCoproductIsoProduct
-/
class IsGroupoid (C : Type u) [Category.{v} C] : Prop where
  all_isIso {X Y : C} (f : X ⟶ Y) : IsIso f := by infer_instance

attribute [instance] IsGroupoid.all_isIso

noncomputable instance {C : Type u} [Groupoid.{v} C] : IsGroupoid C where

variable {C : Type u} [Category.{v} C]

/-- Promote (noncomputably) an `IsGroupoid` to a `Groupoid` structure. -/
@[instance_reducible]
/--
Definition of `Groupoid.ofIsGroupoid` / `Groupoid.ofIsGroupoid` 的定义

English:
definition Groupoid.ofIsGroupoid
  signature: [IsGroupoid C]
  body: fun f => CategoryTheory.inv f

中文:
定义 Groupoid.ofIsGroupoid
  签名: [IsGroupoid C]
  定义体: fun f => CategoryTheory.inv f

Depends on / 依赖: CategoryTheory, CategoryTheory.inv
-/
noncomputable def Groupoid.ofIsGroupoid [IsGroupoid C] :
    Groupoid.{v} C where
  inv := fun f => CategoryTheory.inv f

/-- A category where every morphism `IsIso` is a groupoid. -/
@[instance_reducible]
/--
Definition of `Groupoid.ofIsIso` / `Groupoid.ofIsIso` 的定义

English:
definition Groupoid.ofIsIso
  signature: (all_is_iso : forall {X Y : C} (f : X ⟶ Y), IsIso f)
  body: fun f => CategoryTheory.inv f

中文:
定义 Groupoid.ofIsIso
  签名: (all_is_iso : 对任意 {X Y : C} (f : X ⟶ Y), IsIso f)
  定义体: fun f => CategoryTheory.inv f

Depends on / 依赖: CategoryTheory, CategoryTheory.inv
-/
noncomputable def Groupoid.ofIsIso (all_is_iso : forall {X Y : C} (f : X ⟶ Y), IsIso f) :
    Groupoid.{v} C where
  inv := fun f => CategoryTheory.inv f

/-- A category with a unique morphism between any two objects is a groupoid -/
@[instance_reducible]
/--
Definition of `Groupoid.ofHomUnique` / `Groupoid.ofHomUnique` 的定义

English:
definition Groupoid.ofHomUnique
  signature: (all_unique : forall {X Y : C}, Unique (X ⟶ Y))
  body: all_unique.default

中文:
定义 Groupoid.ofHomUnique
  签名: (all_unique : 对任意 {X Y : C}, Unique (X ⟶ Y))
  定义体: all_unique.default

Depends on / 依赖: all_unique, all_unique.default
-/
def Groupoid.ofHomUnique (all_unique : forall {X Y : C}, Unique (X ⟶ Y)) : Groupoid.{v} C where
  inv _ := all_unique.default

end

/--
lemma `isGroupoid_of_reflects_iso` / 引理 `isGroupoid_of_reflects_iso`

English:
lemma isGroupoid_of_reflects_iso
  statement: {C D : Type*} [Category* C] [Category* D]
  proof: isIso_of_reflects_iso _ F

中文:
引理 isGroupoid_of_reflects_iso
  结论: {C D : 类型} [Category* C] [Category* D]
  证明: isIso_of_reflects_iso _ F

Depends on / 依赖: isIso_of_reflects_iso
-/
lemma isGroupoid_of_reflects_iso {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) [F.ReflectsIsomorphisms] [IsGroupoid D] :
    IsGroupoid C where
  all_isIso _ := isIso_of_reflects_iso _ F

/-- A category equipped with a fully faithful functor to a groupoid is fully faithful -/
@[instance_reducible]
/--
Definition of `Groupoid.ofFullyFaithfulToGroupoid` / `Groupoid.ofFullyFaithfulToGroupoid` 的定义

English:
definition Groupoid.ofFullyFaithfulToGroupoid
  signature: {C : Type*} [𝒞 : Category C] {D : Type u} [Groupoid.{v} D]
  body: { 𝒞 with
inv f := h.preimage Groupoid.inv (F.map f)
    inv_comp f := by
      apply h.map_injective
      simp
    comp_inv f := by
      apply h.map_injective
      simp }

中文:
定义 Groupoid.ofFullyFaithfulToGroupoid
  签名: {C : 类型} [𝒞 : Category C] {D : 类型u} [Groupoid.{v} D]
  定义体: { 𝒞 with
inv f := h.preimage Groupoid.inv (F.map f)
    inv_comp f := by
      apply h.map_injective
      simp
    comp_inv f := by
      apply h.map_injective
      simp }

Depends on / 依赖: F.map, Groupoid, Groupoid.inv, comp_inv, h.map_injective, h.preimage, inv_comp, map_injective, preimage
-/
def Groupoid.ofFullyFaithfulToGroupoid {C : Type*} [𝒞 : Category C] {D : Type u} [Groupoid.{v} D]
    (F : C ⥤ D) (h : F.FullyFaithful) : Groupoid C :=
  { 𝒞 with
inv f := h.preimage Groupoid.inv (F.map f)
    inv_comp f := by
      apply h.map_injective
      simp
    comp_inv f := by
      apply h.map_injective
      simp }

/--
Instance `InducedCategory.groupoid` / 实例 `InducedCategory.groupoid`

English:
instance InducedCategory.groupoid
  signature: {C : Type u} (D : Type u₂) [Groupoid.{v} D] (F : C -> D)
  body: Groupoid.ofFullyFaithfulToGroupoid (inducedFunctor F) (fullyFaithfulInducedFunctor F)

中文:
实例 InducedCategory.groupoid
  签名: {C : 类型u} (D : 类型u₂) [Groupoid.{v} D] (F : C -> D)
  定义体: Groupoid.ofFullyFaithfulToGroupoid (inducedFunctor F) (fullyFaithfulInducedFunctor F)

Depends on / 依赖: Groupoid, Groupoid.ofFullyFaithfulToGroupoid, fullyFaithfulInducedFunctor, inducedFunctor, ofFullyFaithfulToGroupoid
-/
instance InducedCategory.groupoid {C : Type u} (D : Type u₂) [Groupoid.{v} D] (F : C -> D) :
    Groupoid.{v} (InducedCategory D F) :=
  Groupoid.ofFullyFaithfulToGroupoid (inducedFunctor F) (fullyFaithfulInducedFunctor F)

/--
Instance `InducedCategory.isGroupoid` / 实例 `InducedCategory.isGroupoid`

English:
instance InducedCategory.isGroupoid
  signature: {C : Type u} (D : Type u₂)
  body: isGroupoid_of_reflects_iso (inducedFunctor F)

中文:
实例 InducedCategory.isGroupoid
  签名: {C : 类型u} (D : 类型u₂)
  定义体: isGroupoid_of_reflects_iso (inducedFunctor F)

Depends on / 依赖: inducedFunctor, isGroupoid_of_reflects_iso
-/
instance InducedCategory.isGroupoid {C : Type u} (D : Type u₂)
    [Category.{v} D] [IsGroupoid D] (F : C -> D) :
    IsGroupoid (InducedCategory D F) :=
  isGroupoid_of_reflects_iso (inducedFunctor F)

section

/--
Instance `groupoidPi` / 实例 `groupoidPi`

English:
instance groupoidPi
  signature: {I : Type u} {J : I -> Type u₂} [forall i, Groupoid.{v} (J i)]
  body: fun i : I => Groupoid.inv (f i)
  comp_inv := fun f => by funext i; apply Groupoid.comp_inv
  inv_comp := fun f => by funext i; apply Groupoid.inv_comp

中文:
实例 groupoidPi
  签名: {I : 类型u} {J : I -> 类型u₂} [对任意 i, Groupoid.{v} (J i)]
  定义体: fun i : I => Groupoid.inv (f i)
  comp_inv := fun f => by funext i; apply Groupoid.comp_inv
  inv_comp := fun f => by funext i; apply Groupoid.inv_comp

Depends on / 依赖: Groupoid, Groupoid.inv
-/
instance groupoidPi {I : Type u} {J : I -> Type u₂} [forall i, Groupoid.{v} (J i)] :
    Groupoid.{max u v} (forall i : I, J i) where
  inv f := fun i : I => Groupoid.inv (f i)
  comp_inv := fun f => by funext i; apply Groupoid.comp_inv
  inv_comp := fun f => by funext i; apply Groupoid.inv_comp

/--
Instance `groupoidProd` / 实例 `groupoidProd`

English:
instance groupoidProd
  signature: {α : Type u} {β : Type v} [Groupoid.{u₂} α] [Groupoid.{v₂} β]
  body: (Groupoid.inv f.1, Groupoid.inv f.2)

中文:
实例 groupoidProd
  签名: {α : 类型u} {β : 类型v} [Groupoid.{u₂} α] [Groupoid.{v₂} β]
  定义体: (Groupoid.inv f.1, Groupoid.inv f.2)

Depends on / 依赖: Groupoid, Groupoid.inv
-/
instance groupoidProd {α : Type u} {β : Type v} [Groupoid.{u₂} α] [Groupoid.{v₂} β] :
    Groupoid.{max u₂ v₂} (α × β) where
  inv f := (Groupoid.inv f.1, Groupoid.inv f.2)

/--
Instance `isGroupoidPi` / 实例 `isGroupoidPi`

English:
instance isGroupoidPi
  signature: {I : Type u} {J : I -> Type u₂}
  body: (isIso_pi_iff f).mpr (fun _ => inferInstance)

中文:
实例 isGroupoidPi
  签名: {I : 类型u} {J : I -> 类型u₂}
  定义体: (isIso_pi_iff f).mpr (fun _ => inferInstance)

Depends on / 依赖: isIso_pi_iff
-/
instance isGroupoidPi {I : Type u} {J : I -> Type u₂}
    [forall i, Category.{v} (J i)] [forall i, IsGroupoid (J i)] :
    IsGroupoid (forall i : I, J i) where
  all_isIso f := (isIso_pi_iff f).mpr (fun _ => inferInstance)

/--
Instance `isGroupoidProd` / 实例 `isGroupoidProd`

English:
instance isGroupoidProd
  signature: {α : Type u} {β : Type u₂} [Category.{v} α] [Category.{v₂} β]
  body: (isIso_prod_iff (f := f)).mpr ⟨inferInstance, inferInstance⟩

中文:
实例 isGroupoidProd
  签名: {α : 类型u} {β : 类型u₂} [Category.{v} α] [Category.{v₂} β]
  定义体: (isIso_prod_iff (f := f)).mpr ⟨inferInstance, inferInstance⟩

Depends on / 依赖: isIso_prod_iff
-/
instance isGroupoidProd {α : Type u} {β : Type u₂} [Category.{v} α] [Category.{v₂} β]
    [IsGroupoid α] [IsGroupoid β] :
    IsGroupoid (α × β) where
  all_isIso f := (isIso_prod_iff (f := f)).mpr ⟨inferInstance, inferInstance⟩

end

open MorphismProperty in
/--
lemma `isGroupoid_iff_isomorphisms_eq_top` / 引理 `isGroupoid_iff_isomorphisms_eq_top`

English:
lemma isGroupoid_iff_isomorphisms_eq_top
  given: (C : Type*) [Category* C]
  proof: by
  constructor
  · rw [eq_top_iff]
    intro _ _
    simp only [isomorphisms.iff, top_apply]
    infer_instance
  · intro h
    exact ⟨of_eq_top h⟩

中文:
引理 isGroupoid_iff_isomorphisms_eq_top
  条件: (C : 类型) [Category* C]
  证明: by
  constructor
  · rw [eq_top_iff]
    intro _ _
    simp only [isomorphisms.iff, top_apply]
    infer_instance
  · intro h
    exact ⟨of_eq_top h⟩

Depends on / 依赖: Category, Category.assoc, Category.comp_id, Discrete, Discrete.functor_obj, IsLimit, IsLimit.conePointUniqueUpToIso_inv_comp, Iso.hom_inv_id, Iso.op_inv, Quiver, Quiver.Hom.op_inj, Quiver.Hom.op_unop, Quiver.Hom.unop_inj, Quiver.Hom.unop_op, _hom, comp_id, conePointUniqueUpToIso_inv_comp, eq_top_iff, f.proj, functor_obj
-/
lemma isGroupoid_iff_isomorphisms_eq_top (C : Type*) [Category* C] :
    IsGroupoid C ↔ isomorphisms C = ⊤ := by
  constructor
  · rw [eq_top_iff]
    intro _ _
    simp only [isomorphisms.iff, top_apply]
    infer_instance
  · intro h
    exact ⟨of_eq_top h⟩

instance {I : Type*} : IsGroupoid (Discrete I) where

end CategoryTheory
