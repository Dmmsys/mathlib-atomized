/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Adjunction.Reflective
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
/-!

# Sheafification

Given a site `(C, J)` we define a typeclass `HasSheafify J A` saying that the inclusion functor from
`A`-valued sheaves on `C` to presheaves admits a left exact left adjoint (sheafification).

Note: to access the `HasSheafify` instance for suitable concrete categories, import the file
`Mathlib/CategoryTheory/Sites/LeftExact.lean`.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Limits

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
variable (A : Type u₂) [Category.{v₂} A]

/--
Definition of `HasWeakSheafify` / `HasWeakSheafify` 的定义

English:
abbreviation HasWeakSheafify
  signature: : Prop
  body: (sheafToPresheaf J A).IsRightAdjoint

中文:
缩写 HasWeakSheafify
  签名: : 命题
  定义体: (sheafToPresheaf J A).IsRightAdjoint

Depends on / 依赖: IsRightAdjoint, sheafToPresheaf
-/
abbrev HasWeakSheafify : Prop := (sheafToPresheaf J A).IsRightAdjoint

/--
Definition of `HasSheafify` / `HasSheafify` 的定义

English:
class HasSheafify
  parameters: : Prop where
  axioms and operations (2):
    - isRightAdjoint : HasWeakSheafify J A
    - isLeftExact : PreservesFiniteLimits ((sheafToPresheaf J A).leftAdjoint)

中文:
类 HasSheafify
  参数: : 命题 where
  公理与运算 (2 个):
    - isRightAdjoint : HasWeakSheafify J A
    - isLeftExact : PreservesFiniteLimits ((sheafToPresheaf J A).leftAdjoint)

Depends on / 依赖: _apply, _eq_zero_iff_forall_adj, hA.reachable, reachable
-/
class HasSheafify : Prop where
  isRightAdjoint : HasWeakSheafify J A
  isLeftExact : PreservesFiniteLimits ((sheafToPresheaf J A).leftAdjoint)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasSheafify
  signature: J A] : HasWeakSheafify J A
  body: HasSheafify.isRightAdjoint

noncomputable section

中文:
实例 [HasSheafify
  签名: J A] : HasWeakSheafify J A
  定义体: HasSheafify.isRightAdjoint

noncomputable section

Depends on / 依赖: HasSheafify, HasSheafify.isRightAdjoint, isRightAdjoint
-/
instance [HasSheafify J A] : HasWeakSheafify J A := HasSheafify.isRightAdjoint

noncomputable section

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasSheafify
  signature: J A] : PreservesFiniteLimits ((sheafToPresheaf J A).leftAdjoint)
  body: HasSheafify.isLeftExact

中文:
实例 [HasSheafify
  签名: J A] : PreservesFiniteLimits ((sheafToPresheaf J A).leftAdjoint)
  定义体: HasSheafify.isLeftExact

Depends on / 依赖: HasSheafify, HasSheafify.isLeftExact, isLeftExact
-/
instance [HasSheafify J A] : PreservesFiniteLimits ((sheafToPresheaf J A).leftAdjoint) :=
  HasSheafify.isLeftExact

/--
theorem `HasSheafify.mk'` / 定理 `HasSheafify.mk'`

English:
theorem HasSheafify.mk'
  statement: {F : (Cᵒᵖ ⥤ A) ⥤ Sheaf J A} (adj : F ⊣ sheafToPresheaf J A)
  proof: ⟨F, ⟨adj⟩⟩
  isLeftExact := ⟨by
    have : (sheafToPresheaf J A).IsRightAdjoint := ⟨_, ⟨adj⟩⟩
    exact fun _ _ _ => preservesLimitsOfShape_of_natIso
      (adj.leftAdjointUniq (Adjunction.ofIsRightAdjoint (sheafToPresheaf J A)))⟩

中文:
定理 HasSheafify.mk'
  结论: {F : (Cᵒᵖ ⥤ A) ⥤ Sheaf J A} (adj : F ⊣ sheafToPresheaf J A)
  证明: ⟨F, ⟨adj⟩⟩
  isLeftExact := ⟨by
    have : (sheafToPresheaf J A).IsRightAdjoint := ⟨_, ⟨adj⟩⟩
    exact fun _ _ _ => preservesLimitsOfShape_of_natIso
      (adj.leftAdjointUniq (Adjunction.ofIsRightAdjoint (sheafToPresheaf J A)))⟩
-/
theorem HasSheafify.mk' {F : (Cᵒᵖ ⥤ A) ⥤ Sheaf J A} (adj : F ⊣ sheafToPresheaf J A)
    [PreservesFiniteLimits F] : HasSheafify J A where
  isRightAdjoint := ⟨F, ⟨adj⟩⟩
  isLeftExact := ⟨by
    have : (sheafToPresheaf J A).IsRightAdjoint := ⟨_, ⟨adj⟩⟩
    exact fun _ _ _ => preservesLimitsOfShape_of_natIso
      (adj.leftAdjointUniq (Adjunction.ofIsRightAdjoint (sheafToPresheaf J A)))⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasSheafify (⊥ : GrothendieckTopology C) A
  body: HasSheafify.mk' _ _
    (sheafBotEquivalence A).symm.toAdjunction

中文:
实例 :
  签名: HasSheafify (⊥ : GrothendieckTopology C) A
  定义体: HasSheafify.mk' _ _
    (sheafBotEquivalence A).symm.toAdjunction

Depends on / 依赖: HasSheafify, HasSheafify.mk, sheafBotEquivalence, symm.toAdjunction, toAdjunction
-/
instance : HasSheafify (⊥ : GrothendieckTopology C) A :=
  HasSheafify.mk' _ _
    (sheafBotEquivalence A).symm.toAdjunction

instance {F G : Sheaf J A} [HasWeakSheafify J A] (f : F ⟶ G) [Mono f] : Mono f.hom :=
  inferInstanceAs (Mono ((sheafToPresheaf J A).map f))

/--
Definition of `presheafToSheaf` / `presheafToSheaf` 的定义

English:
definition presheafToSheaf
  signature: [HasWeakSheafify J A]
  body: (sheafToPresheaf J A).leftAdjoint

中文:
定义 presheafToSheaf
  签名: [HasWeakSheafify J A]
  定义体: (sheafToPresheaf J A).leftAdjoint

Depends on / 依赖: leftAdjoint, sheafToPresheaf
-/
def presheafToSheaf [HasWeakSheafify J A] : (Cᵒᵖ ⥤ A) ⥤ Sheaf J A :=
  (sheafToPresheaf J A).leftAdjoint

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasSheafify
  signature: J A] : PreservesFiniteLimits (presheafToSheaf J A)
  body: HasSheafify.isLeftExact

中文:
实例 [HasSheafify
  签名: J A] : PreservesFiniteLimits (presheafToSheaf J A)
  定义体: HasSheafify.isLeftExact

Depends on / 依赖: HasSheafify, HasSheafify.isLeftExact, isLeftExact
-/
instance [HasSheafify J A] : PreservesFiniteLimits (presheafToSheaf J A) :=
  HasSheafify.isLeftExact

/--
Definition of `sheafificationAdjunction` / `sheafificationAdjunction` 的定义

English:
definition sheafificationAdjunction
  signature: [HasWeakSheafify J A]
  body: Adjunction.ofIsRightAdjoint _

中文:
定义 sheafificationAdjunction
  签名: [HasWeakSheafify J A]
  定义体: Adjunction.ofIsRightAdjoint _

Depends on / 依赖: Adjunction, Adjunction.ofIsRightAdjoint, ofIsRightAdjoint
-/
def sheafificationAdjunction [HasWeakSheafify J A] :
    presheafToSheaf J A ⊣ sheafToPresheaf J A := Adjunction.ofIsRightAdjoint _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasWeakSheafify
  signature: J A] : (presheafToSheaf J A).IsLeftAdjoint
  body: ⟨_, ⟨sheafificationAdjunction J A⟩⟩

中文:
实例 [HasWeakSheafify
  签名: J A] : (presheafToSheaf J A).IsLeftAdjoint
  定义体: ⟨_, ⟨sheafificationAdjunction J A⟩⟩

Depends on / 依赖: sheafificationAdjunction
-/
instance [HasWeakSheafify J A] : (presheafToSheaf J A).IsLeftAdjoint :=
  ⟨_, ⟨sheafificationAdjunction J A⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasWeakSheafify
  signature: J A] : Reflective (sheafToPresheaf J A) where
  body: presheafToSheaf J A
  adj := sheafificationAdjunction _ _

中文:
实例 [HasWeakSheafify
  签名: J A] : Reflective (sheafToPresheaf J A) where
  定义体: presheafToSheaf J A
  adj := sheafificationAdjunction _ _

Depends on / 依赖: presheafToSheaf
-/
instance [HasWeakSheafify J A] : Reflective (sheafToPresheaf J A) where
  L := presheafToSheaf J A
  adj := sheafificationAdjunction _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasSheafify
  signature: J A] : PreservesFiniteLimits (reflector (sheafToPresheaf J A))
  body: inferInstanceAs (PreservesFiniteLimits (presheafToSheaf _ _))

中文:
实例 [HasSheafify
  签名: J A] : PreservesFiniteLimits (reflector (sheafToPresheaf J A))
  定义体: inferInstanceAs (PreservesFiniteLimits (presheafToSheaf _ _))

Depends on / 依赖: PreservesFiniteLimits, presheafToSheaf
-/
instance [HasSheafify J A] : PreservesFiniteLimits (reflector (sheafToPresheaf J A)) :=
  inferInstanceAs (PreservesFiniteLimits (presheafToSheaf _ _))

end

variable {D : Type*} [Category* D] [HasWeakSheafify J D]

/--
Definition of `sheafify` / `sheafify` 的定义

English:
abbreviation sheafify
  signature: (P : Cᵒᵖ ⥤ D)
  body: .obj .obj P presheafToSheaf J D

中文:
缩写 sheafify
  签名: (P : Cᵒᵖ ⥤ D)
  定义体: .obj .obj P presheafToSheaf J D

Depends on / 依赖: presheafToSheaf
-/
noncomputable abbrev sheafify (P : Cᵒᵖ ⥤ D) : Cᵒᵖ ⥤ D :=
.obj .obj P presheafToSheaf J D

/--
Definition of `toSheafify` / `toSheafify` 的定义

English:
abbreviation toSheafify
  signature: (P : Cᵒᵖ ⥤ D)
  body: .unit.app P sheafificationAdjunction J D

@[simp]

中文:
缩写 toSheafify
  签名: (P : Cᵒᵖ ⥤ D)
  定义体: .unit.app P sheafificationAdjunction J D

@[simp]

Depends on / 依赖: sheafificationAdjunction, unit.app
-/
noncomputable abbrev toSheafify (P : Cᵒᵖ ⥤ D) : P ⟶ sheafify J P :=
.unit.app P sheafificationAdjunction J D

@[simp]
/--
theorem `sheafificationAdjunction_unit_app` / 定理 `sheafificationAdjunction_unit_app`

English:
theorem sheafificationAdjunction_unit_app
  given: (P : Cᵒᵖ ⥤ D)
  proof: rfl

中文:
定理 sheafificationAdjunction_unit_app
  条件: (P : Cᵒᵖ ⥤ D)
  证明: rfl
-/
theorem sheafificationAdjunction_unit_app (P : Cᵒᵖ ⥤ D) :
    (sheafificationAdjunction J D).unit.app P = toSheafify J P := rfl

/--
Definition of `sheafifyMap` / `sheafifyMap` 的定义

English:
abbreviation sheafifyMap
  signature: {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q)
  body: .hom .map η presheafToSheaf J D

@[simp]

中文:
缩写 sheafifyMap
  签名: {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q)
  定义体: .hom .map η presheafToSheaf J D

@[simp]

Depends on / 依赖: presheafToSheaf
-/
noncomputable abbrev sheafifyMap {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) : sheafify J P ⟶ sheafify J Q :=
.hom .map η presheafToSheaf J D

@[simp]
/--
theorem `sheafifyMap_id` / 定理 `sheafifyMap_id`

English:
theorem sheafifyMap_id
  given: (P : Cᵒᵖ ⥤ D)
  statement: sheafifyMap J (𝟙 P) = 𝟙 (sheafify J P)
  proof: by
  simp [sheafifyMap, sheafify]

@[simp]

中文:
定理 sheafifyMap_id
  条件: (P : Cᵒᵖ ⥤ D)
  结论: sheafifyMap J (𝟙 P) = 𝟙 (sheafify J P)
  证明: by
  simp [sheafifyMap, sheafify]

@[simp]

Depends on / 依赖: sheafify, sheafifyMap
-/
theorem sheafifyMap_id (P : Cᵒᵖ ⥤ D) : sheafifyMap J (𝟙 P) = 𝟙 (sheafify J P) := by
  simp [sheafifyMap, sheafify]

@[simp]
/--
theorem `sheafifyMap_comp` / 定理 `sheafifyMap_comp`

English:
theorem sheafifyMap_comp
  given: {P Q R : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (γ : Q ⟶ R)
  proof: by
  simp [sheafifyMap, sheafify]

@[reassoc (attr := simp)]

中文:
定理 sheafifyMap_comp
  条件: {P Q R : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (γ : Q ⟶ R)
  证明: by
  simp [sheafifyMap, sheafify]

@[reassoc (attr := simp)]

Depends on / 依赖: sheafify, sheafifyMap
-/
theorem sheafifyMap_comp {P Q R : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (γ : Q ⟶ R) :
    sheafifyMap J (η ≫ γ) = sheafifyMap J η ≫ sheafifyMap J γ := by
  simp [sheafifyMap, sheafify]

@[reassoc (attr := simp)]
/--
theorem `toSheafify_naturality` / 定理 `toSheafify_naturality`

English:
theorem toSheafify_naturality
  given: {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q)
  proof: .unit.naturality η sheafificationAdjunction J D

中文:
定理 toSheafify_naturality
  条件: {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q)
  证明: .unit.naturality η sheafificationAdjunction J D

Depends on / 依赖: naturality, sheafificationAdjunction, unit.naturality
-/
theorem toSheafify_naturality {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) :
    η ≫ toSheafify J _ = toSheafify J _ ≫ sheafifyMap J η :=
.unit.naturality η sheafificationAdjunction J D

variable (D)

/--
Definition of `sheafification` / `sheafification` 的定义

English:
abbreviation sheafification
  signature: : (Cᵒᵖ ⥤ D) ⥤ Cᵒᵖ ⥤ D
  body: presheafToSheaf J D ⋙ sheafToPresheaf J D

中文:
缩写 sheafification
  签名: : (Cᵒᵖ ⥤ D) ⥤ Cᵒᵖ ⥤ D
  定义体: presheafToSheaf J D ⋙ sheafToPresheaf J D

Depends on / 依赖: presheafToSheaf, sheafToPresheaf
-/
noncomputable abbrev sheafification : (Cᵒᵖ ⥤ D) ⥤ Cᵒᵖ ⥤ D :=
  presheafToSheaf J D ⋙ sheafToPresheaf J D

/--
theorem `sheafification_obj` / 定理 `sheafification_obj`

English:
theorem sheafification_obj
  given: (P : Cᵒᵖ ⥤ D)
  statement: (sheafification J D).obj P = sheafify J P
  proof: rfl

中文:
定理 sheafification_obj
  条件: (P : Cᵒᵖ ⥤ D)
  结论: (sheafification J D).obj P = sheafify J P
  证明: rfl
-/
theorem sheafification_obj (P : Cᵒᵖ ⥤ D) : (sheafification J D).obj P = sheafify J P :=
  rfl

/--
theorem `sheafification_map` / 定理 `sheafification_map`

English:
theorem sheafification_map
  given: {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q)
  proof: rfl

中文:
定理 sheafification_map
  条件: {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q)
  证明: rfl
-/
theorem sheafification_map {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) :
    (sheafification J D).map η = sheafifyMap J η :=
  rfl

/--
Definition of `toSheafification` / `toSheafification` 的定义

English:
abbreviation toSheafification
  signature: : 𝟭 _ ⟶ sheafification J D
  body: .unit sheafificationAdjunction J D

中文:
缩写 toSheafification
  签名: : 𝟭 _ ⟶ sheafification J D
  定义体: .unit sheafificationAdjunction J D

Depends on / 依赖: sheafificationAdjunction
-/
noncomputable abbrev toSheafification : 𝟭 _ ⟶ sheafification J D :=
.unit sheafificationAdjunction J D

/--
theorem `toSheafification_app` / 定理 `toSheafification_app`

English:
theorem toSheafification_app
  given: (P : Cᵒᵖ ⥤ D)
  statement: (toSheafification J D).app P = toSheafify J P
  proof: rfl

中文:
定理 toSheafification_app
  条件: (P : Cᵒᵖ ⥤ D)
  结论: (toSheafification J D).app P = toSheafify J P
  证明: rfl
-/
theorem toSheafification_app (P : Cᵒᵖ ⥤ D) : (toSheafification J D).app P = toSheafify J P :=
  rfl

variable {D}

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
theorem `isIso_toSheafify` / 定理 `isIso_toSheafify`

English:
theorem isIso_toSheafify
  given: {P : Cᵒᵖ ⥤ D} (hP : Presheaf.IsSheaf J P)
  statement: IsIso (toSheafify J P)
  proof: by
  refine ⟨(sheafificationAdjunction J D |>.counit.app ⟨P, hP⟩).hom, ?_, ?_⟩
.right_triangle_components ⟨P, hP⟩ · exact sheafificationAdjunction J D
  · change (sheafToPresheaf _ _).map _ ≫ _ = _
    change _ ≫ (sheafificationAdjunction J D).unit.app ((sheafToPresheaf J D).obj ⟨P, hP⟩) = _
    rw 

中文:
定理 isIso_toSheafify
  条件: {P : Cᵒᵖ ⥤ D} (hP : Presheaf.IsSheaf J P)
  结论: IsIso (toSheafify J P)
  证明: by
  refine ⟨(sheafificationAdjunction J D |>.counit.app ⟨P, hP⟩).hom, ?_, ?_⟩
.right_triangle_components ⟨P, hP⟩ · exact sheafificationAdjunction J D
  · change (sheafToPresheaf _ _).map _ ≫ _ = _
    change _ ≫ (sheafificationAdjunction J D).unit.app ((sheafToPresheaf J D).obj ⟨P, hP⟩) = _
    rw 

Depends on / 依赖: counit, counit.app, inv_counit_map, right_triangle_components, sheafToPresheaf, sheafificationAdjunction, unit.app
-/
theorem isIso_toSheafify {P : Cᵒᵖ ⥤ D} (hP : Presheaf.IsSheaf J P) : IsIso (toSheafify J P) := by
  refine ⟨(sheafificationAdjunction J D |>.counit.app ⟨P, hP⟩).hom, ?_, ?_⟩
.right_triangle_components ⟨P, hP⟩ · exact sheafificationAdjunction J D
  · change (sheafToPresheaf _ _).map _ ≫ _ = _
    change _ ≫ (sheafificationAdjunction J D).unit.app ((sheafToPresheaf J D).obj ⟨P, hP⟩) = _
    rw [← (sheafificationAdjunction J D).inv_counit_map (X := ⟨P]; rw [hP⟩)]
    simp

/--
Definition of `isoSheafify` / `isoSheafify` 的定义

English:
definition isoSheafify
  signature: {P : Cᵒᵖ ⥤ D} (hP : Presheaf.IsSheaf J P)
  body: letI := isIso_toSheafify J hP
  asIso (toSheafify J P)

@[simp]

中文:
定义 isoSheafify
  签名: {P : Cᵒᵖ ⥤ D} (hP : Presheaf.IsSheaf J P)
  定义体: letI := isIso_toSheafify J hP
  asIso (toSheafify J P)

@[simp]

Depends on / 依赖: isIso_toSheafify, toSheafify
-/
noncomputable def isoSheafify {P : Cᵒᵖ ⥤ D} (hP : Presheaf.IsSheaf J P) : P ≅ sheafify J P :=
  letI := isIso_toSheafify J hP
  asIso (toSheafify J P)

@[simp]
/--
theorem `isoSheafify_hom` / 定理 `isoSheafify_hom`

English:
theorem isoSheafify_hom
  given: {P : Cᵒᵖ ⥤ D} (hP : Presheaf.IsSheaf J P)
  proof: rfl

中文:
定理 isoSheafify_hom
  条件: {P : Cᵒᵖ ⥤ D} (hP : Presheaf.IsSheaf J P)
  证明: rfl
-/
theorem isoSheafify_hom {P : Cᵒᵖ ⥤ D} (hP : Presheaf.IsSheaf J P) :
    (isoSheafify J hP).hom = toSheafify J P :=
  rfl

/--
Definition of `sheafifyLift` / `sheafifyLift` 的定义

English:
definition sheafifyLift
  signature: {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q)
  body: .hom .symm η (sheafificationAdjunction J D).homEquiv P ⟨Q, hQ⟩

中文:
定义 sheafifyLift
  签名: {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q)
  定义体: .hom .symm η (sheafificationAdjunction J D).homEquiv P ⟨Q, hQ⟩

Depends on / 依赖: homEquiv, sheafificationAdjunction
-/
noncomputable def sheafifyLift {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q) :
    sheafify J P ⟶ Q :=
.hom .symm η (sheafificationAdjunction J D).homEquiv P ⟨Q, hQ⟩

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `sheafificationAdjunction_counit_app_val` / 定理 `sheafificationAdjunction_counit_app_val`

English:
theorem sheafificationAdjunction_counit_app_val
  given: (P : Sheaf J D)
  proof: by
  unfold sheafifyLift
  rw [Adjunction.homEquiv_counit]
  simp

@[reassoc (attr := simp)]

中文:
定理 sheafificationAdjunction_counit_app_val
  条件: (P : Sheaf J D)
  证明: by
  unfold sheafifyLift
  rw [Adjunction.homEquiv_counit]
  simp

@[reassoc (attr := simp)]

Depends on / 依赖: Adjunction, Adjunction.homEquiv_counit, homEquiv_counit, sheafifyLift
-/
theorem sheafificationAdjunction_counit_app_val (P : Sheaf J D) :
    ((sheafificationAdjunction J D).counit.app P).hom = sheafifyLift J (𝟙 P.obj) P.property := by
  unfold sheafifyLift
  rw [Adjunction.homEquiv_counit]
  simp

@[reassoc (attr := simp)]
/--
theorem `toSheafify_sheafifyLift` / 定理 `toSheafify_sheafifyLift`

English:
theorem toSheafify_sheafifyLift
  given: {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q)
  proof: by
  rw [toSheafify]; rw [sheafifyLift]; rw [Adjunction.homEquiv_counit]
  change _ ≫ (sheafToPresheaf J D).map _ ≫ _ = _
  simp only [Adjunction.unit_naturality_assoc]
  change _ ≫ (sheafificationAdjunction J D).unit.app ((sheafToPresheaf J D).obj ⟨Q, hQ⟩) ≫ _ = _
  change _ ≫ _ ≫ (sheafToPresheaf 

中文:
定理 toSheafify_sheafifyLift
  条件: {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q)
  证明: by
  rw [toSheafify]; rw [sheafifyLift]; rw [Adjunction.homEquiv_counit]
  change _ ≫ (sheafToPresheaf J D).map _ ≫ _ = _
  simp only [Adjunction.unit_naturality_assoc]
  change _ ≫ (sheafificationAdjunction J D).unit.app ((sheafToPresheaf J D).obj ⟨Q, hQ⟩) ≫ _ = _
  change _ ≫ _ ≫ (sheafToPresheaf 

Depends on / 依赖: Adjunction, Adjunction.homEquiv_counit, Adjunction.unit_naturality_assoc, homEquiv_counit, right_triangle_components, sheafToPresheaf, sheafificationAdjunction, sheafifyLift, toSheafify, unit.app, unit_naturality_assoc
-/
theorem toSheafify_sheafifyLift {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q) :
    toSheafify J P ≫ sheafifyLift J η hQ = η := by
  rw [toSheafify]; rw [sheafifyLift]; rw [Adjunction.homEquiv_counit]
  change _ ≫ (sheafToPresheaf J D).map _ ≫ _ = _
  simp only [Adjunction.unit_naturality_assoc]
  change _ ≫ (sheafificationAdjunction J D).unit.app ((sheafToPresheaf J D).obj ⟨Q, hQ⟩) ≫ _ = _
  change _ ≫ _ ≫ (sheafToPresheaf J D).map _ = _
  rw [sheafificationAdjunction J D |>.right_triangle_components (Y := ⟨Q]; rw [hQ⟩)]
  simp

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `sheafifyLift_unique` / 定理 `sheafifyLift_unique`

English:
theorem sheafifyLift_unique
  statement: {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q)
  proof: by
  intro h
  rw [toSheafify] at h
  rw [sheafifyLift]
  let γ' : (presheafToSheaf J D).obj P ⟶ ⟨Q, hQ⟩ := ⟨γ⟩
  change γ'.hom = _
  rw [← Sheaf.hom_ext_iff]; rw [← Adjunction.homEquiv_apply_eq]; rw [Adjunction.homEquiv_unit]
  exact h

@[simp]

中文:
定理 sheafifyLift_unique
  结论: {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q)
  证明: by
  intro h
  rw [toSheafify] at h
  rw [sheafifyLift]
  let γ' : (presheafToSheaf J D).obj P ⟶ ⟨Q, hQ⟩ := ⟨γ⟩
  change γ'.hom = _
  rw [← Sheaf.hom_ext_iff]; rw [← Adjunction.homEquiv_apply_eq]; rw [Adjunction.homEquiv_unit]
  exact h

@[simp]

Depends on / 依赖: Adjunction, Adjunction.homEquiv_apply_eq, Adjunction.homEquiv_unit, Sheaf.hom_ext_iff, homEquiv_apply_eq, homEquiv_unit, hom_ext_iff, presheafToSheaf, sheafifyLift, toSheafify
-/
theorem sheafifyLift_unique {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q)
    (γ : sheafify J P ⟶ Q) : toSheafify J P ≫ γ = η -> γ = sheafifyLift J η hQ := by
  intro h
  rw [toSheafify] at h
  rw [sheafifyLift]
  let γ' : (presheafToSheaf J D).obj P ⟶ ⟨Q, hQ⟩ := ⟨γ⟩
  change γ'.hom = _
  rw [← Sheaf.hom_ext_iff]; rw [← Adjunction.homEquiv_apply_eq]; rw [Adjunction.homEquiv_unit]
  exact h

@[simp]
/--
theorem `isoSheafify_inv` / 定理 `isoSheafify_inv`

English:
theorem isoSheafify_inv
  given: {P : Cᵒᵖ ⥤ D} (hP : Presheaf.IsSheaf J P)
  proof: by
  apply sheafifyLift_unique
  simp [Iso.comp_inv_eq]

中文:
定理 isoSheafify_inv
  条件: {P : Cᵒᵖ ⥤ D} (hP : Presheaf.IsSheaf J P)
  证明: by
  apply sheafifyLift_unique
  simp [Iso.comp_inv_eq]

Depends on / 依赖: Iso.comp_inv_eq, comp_inv_eq, sheafifyLift_unique
-/
theorem isoSheafify_inv {P : Cᵒᵖ ⥤ D} (hP : Presheaf.IsSheaf J P) :
    (isoSheafify J hP).inv = sheafifyLift J (𝟙 _) hP := by
  apply sheafifyLift_unique
  simp [Iso.comp_inv_eq]

/--
theorem `sheafify_hom_ext` / 定理 `sheafify_hom_ext`

English:
theorem sheafify_hom_ext
  statement: {P Q : Cᵒᵖ ⥤ D} (η γ : sheafify J P ⟶ Q) (hQ : Presheaf.IsSheaf J Q)
  proof: by
  rw [sheafifyLift_unique J _ hQ _ h]; rw [← h]
  exact (sheafifyLift_unique J _ hQ _ h.symm).symm

@[reassoc (attr := simp)]

中文:
定理 sheafify_hom_ext
  结论: {P Q : Cᵒᵖ ⥤ D} (η γ : sheafify J P ⟶ Q) (hQ : Presheaf.IsSheaf J Q)
  证明: by
  rw [sheafifyLift_unique J _ hQ _ h]; rw [← h]
  exact (sheafifyLift_unique J _ hQ _ h.symm).symm

@[reassoc (attr := simp)]

Depends on / 依赖: h.symm, sheafifyLift_unique
-/
theorem sheafify_hom_ext {P Q : Cᵒᵖ ⥤ D} (η γ : sheafify J P ⟶ Q) (hQ : Presheaf.IsSheaf J Q)
    (h : toSheafify J P ≫ η = toSheafify J P ≫ γ) : η = γ := by
  rw [sheafifyLift_unique J _ hQ _ h]; rw [← h]
  exact (sheafifyLift_unique J _ hQ _ h.symm).symm

@[reassoc (attr := simp)]
/--
theorem `sheafifyMap_sheafifyLift` / 定理 `sheafifyMap_sheafifyLift`

English:
theorem sheafifyMap_sheafifyLift
  statement: {P Q R : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (γ : Q ⟶ R)
  proof: by
  apply sheafifyLift_unique
  rw [← Category.assoc]; rw [← toSheafify_naturality]; rw [Category.assoc]; rw [toSheafify_sheafifyLift]

中文:
定理 sheafifyMap_sheafifyLift
  结论: {P Q R : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (γ : Q ⟶ R)
  证明: by
  apply sheafifyLift_unique
  rw [← Category.assoc]; rw [← toSheafify_naturality]; rw [Category.assoc]; rw [toSheafify_sheafifyLift]

Depends on / 依赖: Category, Category.assoc, sheafifyLift_unique, toSheafify_naturality, toSheafify_sheafifyLift
-/
theorem sheafifyMap_sheafifyLift {P Q R : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (γ : Q ⟶ R)
    (hR : Presheaf.IsSheaf J R) :
    sheafifyMap J η ≫ sheafifyLift J γ hR = sheafifyLift J (η ≫ γ) hR := by
  apply sheafifyLift_unique
  rw [← Category.assoc]; rw [← toSheafify_naturality]; rw [Category.assoc]; rw [toSheafify_sheafifyLift]

/--
lemma `sheafifyLift_comp` / 引理 `sheafifyLift_comp`

English:
lemma sheafifyLift_comp
  statement: {F P Q : Cᵒᵖ ⥤ D} (a : F ⟶ P) (hP : Presheaf.IsSheaf J P)
  proof: (sheafifyLift_unique _ _ _ _ (by simp)).symm

中文:
引理 sheafifyLift_comp
  结论: {F P Q : Cᵒᵖ ⥤ D} (a : F ⟶ P) (hP : Presheaf.IsSheaf J P)
  证明: (sheafifyLift_unique _ _ _ _ (by simp)).symm

Depends on / 依赖: sheafifyLift_unique
-/
lemma sheafifyLift_comp {F P Q : Cᵒᵖ ⥤ D} (a : F ⟶ P) (hP : Presheaf.IsSheaf J P)
    (η : P ⟶ Q) (hQ : CategoryTheory.Presheaf.IsSheaf J Q) :
    sheafifyLift J (a ≫ η) hQ = sheafifyLift _ a hP ≫ η :=
  (sheafifyLift_unique _ _ _ _ (by simp)).symm

variable {J}

/-- A sheaf `P` is isomorphic to its own sheafification. -/
@[simps]
/--
Definition of `sheafificationIso` / `sheafificationIso` 的定义

English:
definition sheafificationIso
  signature: (P : Sheaf J D)
  body: ⟨(isoSheafify J P.2).hom⟩
  inv := ⟨(isoSheafify J P.2).inv⟩
  hom_inv_id := by
    ext1
    apply (isoSheafify J P.2).hom_inv_id
  inv_hom_id := by
    ext1
    apply (isoSheafify J P.2).inv_hom_id

中文:
定义 sheafificationIso
  签名: (P : Sheaf J D)
  定义体: ⟨(isoSheafify J P.2).hom⟩
  inv := ⟨(isoSheafify J P.2).inv⟩
  hom_inv_id := by
    ext1
    apply (isoSheafify J P.2).hom_inv_id
  inv_hom_id := by
    ext1
    apply (isoSheafify J P.2).inv_hom_id

Depends on / 依赖: isoSheafify
-/
noncomputable def sheafificationIso (P : Sheaf J D) : P ≅ (presheafToSheaf J D).obj P.obj where
  hom := ⟨(isoSheafify J P.2).hom⟩
  inv := ⟨(isoSheafify J P.2).inv⟩
  hom_inv_id := by
    ext1
    apply (isoSheafify J P.2).hom_inv_id
  inv_hom_id := by
    ext1
    apply (isoSheafify J P.2).inv_hom_id

/--
Instance `isIso_sheafificationAdjunction_counit` / 实例 `isIso_sheafificationAdjunction_counit`

English:
instance isIso_sheafificationAdjunction_counit
  signature: (P : Sheaf J D)
  body: isIso_of_fully_faithful (sheafToPresheaf J D) _

中文:
实例 isIso_sheafificationAdjunction_counit
  签名: (P : Sheaf J D)
  定义体: isIso_of_fully_faithful (sheafToPresheaf J D) _

Depends on / 依赖: isIso_of_fully_faithful, sheafToPresheaf
-/
instance isIso_sheafificationAdjunction_counit (P : Sheaf J D) :
    IsIso ((sheafificationAdjunction J D).counit.app P) :=
  isIso_of_fully_faithful (sheafToPresheaf J D) _

instance (P : Sheaf J D) :
    IsIso ((sheafificationAdjunction J D).counit.app P).hom :=
  inferInstanceAs (IsIso ((sheafToPresheaf J D).map _))

/--
Instance `sheafification_reflective` / 实例 `sheafification_reflective`

English:
instance sheafification_reflective
  signature: : IsIso (sheafificationAdjunction J D).counit
  body: NatIso.isIso_of_isIso_app _

中文:
实例 sheafification_reflective
  签名: : IsIso (sheafificationAdjunction J D).counit
  定义体: NatIso.isIso_of_isIso_app _

Depends on / 依赖: NatIso, NatIso.isIso_of_isIso_app, isIso_of_isIso_app
-/
instance sheafification_reflective : IsIso (sheafificationAdjunction J D).counit :=
  NatIso.isIso_of_isIso_app _

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `sheafifyLift_id_toSheafify` / 引理 `sheafifyLift_id_toSheafify`

English:
lemma sheafifyLift_id_toSheafify
  given: {P : Cᵒᵖ ⥤ D} (hP : Presheaf.IsSheaf J P)
  proof: by
  rw [← cancel_mono ((sheafificationAdjunction J D).counit.app ⟨P]; rw [hP⟩).hom]
  cat_disch

中文:
引理 sheafifyLift_id_toSheafify
  条件: {P : Cᵒᵖ ⥤ D} (hP : Presheaf.IsSheaf J P)
  证明: by
  rw [← cancel_mono ((sheafificationAdjunction J D).counit.app ⟨P]; rw [hP⟩).hom]
  cat_disch

Depends on / 依赖: cancel_mono, cat_disch, counit, counit.app, sheafificationAdjunction
-/
lemma sheafifyLift_id_toSheafify {P : Cᵒᵖ ⥤ D} (hP : Presheaf.IsSheaf J P) :
    sheafifyLift J (𝟙 P) hP ≫ toSheafify J P = 𝟙 (sheafify J P) := by
  rw [← cancel_mono ((sheafificationAdjunction J D).counit.app ⟨P]; rw [hP⟩).hom]
  cat_disch

variable (J D)

set_option backward.defeqAttrib.useBackward true in
/-- The natural isomorphism `𝟭 (Sheaf J D) ≅ sheafToPresheaf J D ⋙ presheafToSheaf J D`. -/
@[simps!]
/--
Definition of `sheafificationNatIso` / `sheafificationNatIso` 的定义

English:
definition sheafificationNatIso
  signature: :
  body: NatIso.ofComponents (fun P => sheafificationIso P) (by cat_disch)

中文:
定义 sheafificationNatIso
  签名: :
  定义体: NatIso.ofComponents (fun P => sheafificationIso P) (by cat_disch)

Depends on / 依赖: NatIso, NatIso.ofComponents, cat_disch, ofComponents, sheafificationIso
-/
noncomputable def sheafificationNatIso :
    𝟭 (Sheaf J D) ≅ sheafToPresheaf J D ⋙ presheafToSheaf J D :=
  NatIso.ofComponents (fun P => sheafificationIso P) (by cat_disch)

end CategoryTheory
