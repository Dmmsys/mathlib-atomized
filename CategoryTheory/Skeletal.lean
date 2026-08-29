/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.Thin

/-!
# Skeleton of a category

Define skeletal categories as categories in which any two isomorphic objects are equal.

Construct the skeleton of an arbitrary category by taking isomorphism classes, and show it is a
skeleton of the original category.

In addition, construct the skeleton of a thin category as a partial ordering, and (noncomputably)
show it is a skeleton of the original category. The advantage of this special case being handled
separately is that lemmas and definitions about orderings can be used directly, for example for the
subobject lattice. In addition, some of the commutative diagrams about the functors commute
definitionally on the nose which is convenient in practice.
-/

@[expose] public section


universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Category

variable (C : Type u₁) [Category.{v₁} C]
variable (D : Type u₂) [Category.{v₂} D]
variable {E : Type u₃} [Category.{v₃} E]

/--
Definition of `Skeletal` / `Skeletal` 的定义

English:
definition Skeletal
  signature: : Prop
  body: forall ⦃X Y : C⦄, IsIsomorphic X Y -> X = Y

中文:
定义 Skeletal
  签名: : 命题
  定义体: forall ⦃X Y : C⦄, IsIsomorphic X Y -> X = Y

Depends on / 依赖: IsIsomorphic
-/
def Skeletal : Prop :=
  forall ⦃X Y : C⦄, IsIsomorphic X Y -> X = Y

/--
Definition of `IsSkeletonOf` / `IsSkeletonOf` 的定义

English:
structure IsSkeletonOf
  parameters: (F : D ⥤ C)
  axioms and operations (2):
    - skel : Skeletal D
    - eqv : F.IsEquivalence  [default: by infer_instance]

中文:
结构 是SkeletonOf
  参数: (F : D ⥤ C)
  公理与运算 (2 个):
    - skel : Skeletal D
    - eqv : F.是等价  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
structure IsSkeletonOf (F : D ⥤ C) : Prop where
  /-- The category `D` has isomorphic objects equal -/
  skel : Skeletal D
  /-- The functor `F` is an equivalence -/
  eqv : F.IsEquivalence := by infer_instance

attribute [local instance] isIsomorphicSetoid

variable {C D}

/--
theorem `Functor.eq_of_iso` / 定理 `Functor.eq_of_iso`

English:
theorem Functor.eq_of_iso
  given: {F₁ F₂ : D ⥤ C} [Quiver.IsThin C] (hC : Skeletal C) (hF : F₁ ≅ F₂)
  proof: Functor.ext (fun X => hC ⟨hF.app X⟩) fun _ _ _ => Subsingleton.elim _ _

中文:
定理 函子.eq_of_iso
  条件: {F₁ F₂ : D ⥤ C} [箭图.IsThin C] (hC : Skeletal C) (hF : F₁ ≅ F₂)
  证明: Functor.ext (fun X => hC ⟨hF.app X⟩) fun _ _ _ => Subsingleton.elim _ _

Depends on / 依赖: Functor, Functor.ext, Subsingleton, Subsingleton.elim, hF.app
-/
theorem Functor.eq_of_iso {F₁ F₂ : D ⥤ C} [Quiver.IsThin C] (hC : Skeletal C) (hF : F₁ ≅ F₂) :
    F₁ = F₂ :=
  Functor.ext (fun X => hC ⟨hF.app X⟩) fun _ _ _ => Subsingleton.elim _ _

/--
theorem `functor_skeletal` / 定理 `functor_skeletal`

English:
theorem functor_skeletal
  given: [Quiver.IsThin C] (hC : Skeletal C)
  statement: Skeletal (D ⥤ C)
  proof: fun _ _ h =>
  h.elim (Functor.eq_of_iso hC)

中文:
定理 functor_skeletal
  条件: [箭图.IsThin C] (hC : Skeletal C)
  结论: Skeletal (D ⥤ C)
  证明: fun _ _ h =>
  h.elim (Functor.eq_of_iso hC)
-/
theorem functor_skeletal [Quiver.IsThin C] (hC : Skeletal C) : Skeletal (D ⥤ C) := fun _ _ h =>
  h.elim (Functor.eq_of_iso hC)

variable (C D)

noncomputable section

/--
Definition of `Skeleton` / `Skeleton` 的定义

English:
definition Skeleton
  signature: : Type u₁
  body: InducedCategory (C := Quotient (isIsomorphicSetoid C)) C Quotient.out
deriving
  Category,
  [Inhabited C] -> Inhabited _

中文:
定义 Skeleton
  签名: : 类型u₁
  定义体: InducedCategory (C := Quotient (isIsomorphicSetoid C)) C Quotient.out
deriving
  Category,
  [Inhabited C] -> Inhabited _

Depends on / 依赖: InducedCategory, Quotient, Quotient.out, isIsomorphicSetoid
-/
def Skeleton : Type u₁ := InducedCategory (C := Quotient (isIsomorphicSetoid C)) C Quotient.out
deriving
  Category,
  [Inhabited C] -> Inhabited _

-- Without this we get errors in Mathlib/RingTheory/PicardGroup.lean
set_option backward.inferInstanceAs.wrap.data false in
deriving instance (α : Sort _) -> [CoeSort C α] -> CoeSort _ α for Skeleton C

end

/-- The functor from the skeleton of `C` to `C`. -/
@[simps!]
/--
Definition of `fromSkeleton` / `fromSkeleton` 的定义

English:
definition fromSkeleton
  signature: : Skeleton C ⥤ C
  body: inducedFunctor _

中文:
定义 fromSkeleton
  签名: : Skeleton C ⥤ C
  定义体: inducedFunctor _

Depends on / 依赖: inducedFunctor
-/
noncomputable def fromSkeleton : Skeleton C ⥤ C :=
  inducedFunctor _
-- The `Full, Faithful` instances should be constructed by a deriving handler.
-- https://github.com/leanprover-community/mathlib4/issues/380
-- Note(kmill): `derive Functor.Full, Functor.Faithful` does not create instances
-- that are in terms of `Skeleton`, but rather `InducedCategory`, which can't be applied.
-- With `deriving @Functor.Full (Skeleton C)`, the instance can't be derived, for a similar reason.

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (fromSkeleton C).Full
  body: by
  apply InducedCategory.full

中文:
实例 :
  签名: (fromSkeleton C).满
  定义体: by
  apply InducedCategory.full

Depends on / 依赖: InducedCategory, InducedCategory.full
-/
noncomputable instance : (fromSkeleton C).Full := by
  apply InducedCategory.full
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (fromSkeleton C).Faithful
  body: by
  apply InducedCategory.faithful

中文:
实例 :
  签名: (fromSkeleton C).忠实
  定义体: by
  apply InducedCategory.faithful

Depends on / 依赖: InducedCategory, InducedCategory.faithful, faithful
-/
noncomputable instance : (fromSkeleton C).Faithful := by
  apply InducedCategory.faithful

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (fromSkeleton C).EssSurj
  body: ⟨Quotient.mk' X, Quotient.mk_out X⟩

中文:
实例 :
  签名: (fromSkeleton C).本质满射
  定义体: ⟨Quotient.mk' X, Quotient.mk_out X⟩

Depends on / 依赖: Quotient, Quotient.mk, Quotient.mk_out, mk_out
-/
instance : (fromSkeleton C).EssSurj where mem_essImage X := ⟨Quotient.mk' X, Quotient.mk_out X⟩

/--
Instance `fromSkeleton.isEquivalence` / 实例 `fromSkeleton.isEquivalence`

English:
instance fromSkeleton.isEquivalence
  signature: : (fromSkeleton C).IsEquivalence where

中文:
实例 fromSkeleton.isEquivalence
  签名: : (fromSkeleton C).是等价 where
-/
noncomputable instance fromSkeleton.isEquivalence : (fromSkeleton C).IsEquivalence where

variable {C}

/--
Definition of `toSkeleton` / `toSkeleton` 的定义

English:
abbreviation toSkeleton
  signature: (X : C)
  body: ⟦X⟧

中文:
缩写 toSkeleton
  签名: (X : C)
  定义体: ⟦X⟧
-/
abbrev toSkeleton (X : C) : Skeleton C := ⟦X⟧

/--
Definition of `fromSkeletonToSkeletonIso` / `fromSkeletonToSkeletonIso` 的定义

English:
definition fromSkeletonToSkeletonIso
  signature: (X : C)
  body: Nonempty.some (Quotient.mk_out X)

@[reassoc, simp]

中文:
定义 fromSkeletonToSkeletonIso
  签名: (X : C)
  定义体: Nonempty.some (Quotient.mk_out X)

@[reassoc, simp]

Depends on / 依赖: Nonempty, Nonempty.some, Quotient, Quotient.mk_out, mk_out
-/
noncomputable def fromSkeletonToSkeletonIso (X : C) : (fromSkeleton C).obj (toSkeleton X) ≅ X :=
  Nonempty.some (Quotient.mk_out X)

@[reassoc, simp]
/--
lemma `Skeleton.comp_hom` / 引理 `Skeleton.comp_hom`

English:
lemma Skeleton.comp_hom
  given: {X Y Z : Skeleton C} (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: rfl

中文:
引理 Skeleton.comp_hom
  条件: {X Y Z : Skeleton C} (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: rfl
-/
lemma Skeleton.comp_hom {X Y Z : Skeleton C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = f.hom ≫ g.hom := rfl

variable (C)

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `toSkeletonFunctor` / `toSkeletonFunctor` 的定义

English:
definition toSkeletonFunctor
  signature: : C ⥤ Skeleton C where
  body: toSkeleton
  map {X Y} f :=
    { hom := (fromSkeletonToSkeletonIso X).hom ≫ f ≫ (fromSkeletonToSkeletonIso Y).inv }
  map_id _ := by aesop
  map_comp _ _ := InducedCategory.hom_ext (by simp)

中文:
定义 toSkeletonFunctor
  签名: : C ⥤ Skeleton C where
  定义体: toSkeleton
  map {X Y} f :=
    { hom := (fromSkeletonToSkeletonIso X).hom ≫ f ≫ (fromSkeletonToSkeletonIso Y).inv }
  map_id _ := by aesop
  map_comp _ _ := InducedCategory.hom_ext (by simp)
-/
@[simps] noncomputable def toSkeletonFunctor : C ⥤ Skeleton C where
  obj := toSkeleton
  map {X Y} f :=
    { hom := (fromSkeletonToSkeletonIso X).hom ≫ f ≫ (fromSkeletonToSkeletonIso Y).inv }
  map_id _ := by aesop
  map_comp _ _ := InducedCategory.hom_ext (by simp)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `skeletonEquivalence` / `skeletonEquivalence` 的定义

English:
definition skeletonEquivalence
  signature: : Skeleton C ≌ C where
  body: fromSkeleton C
  inverse := toSkeletonFunctor C
  unitIso := NatIso.ofComponents
    (fun X => InducedCategory.isoMk (Nonempty.some <| Quotient.mk_out X.out).symm)
    (fun f => InducedCategory.hom_ext (Iso.inv_hom_id_assoc _ _).symm)
  counitIso := NatIso.ofComponents fromSkeletonToSkeletonIso
  functor_unitIso_comp _ := Iso.inv_hom_id _

中文:
定义 skeletonEquivalence
  签名: : Skeleton C ≌ C where
  定义体: fromSkeleton C
  inverse := toSkeletonFunctor C
  unitIso := NatIso.ofComponents
    (fun X => InducedCategory.isoMk (Nonempty.some <| Quotient.mk_out X.out).symm)
    (fun f => InducedCategory.hom_ext (Iso.inv_hom_id_assoc _ _).symm)
  counitIso := NatIso.ofComponents fromSkeletonToSkeletonIso
  functor_unitIso_comp _ := Iso.inv_hom_id _
-/
@[simps] noncomputable def skeletonEquivalence : Skeleton C ≌ C where
  functor := fromSkeleton C
  inverse := toSkeletonFunctor C
  unitIso := NatIso.ofComponents
    (fun X => InducedCategory.isoMk (Nonempty.some <| Quotient.mk_out X.out).symm)
    (fun f => InducedCategory.hom_ext (Iso.inv_hom_id_assoc _ _).symm)
  counitIso := NatIso.ofComponents fromSkeletonToSkeletonIso
  functor_unitIso_comp _ := Iso.inv_hom_id _

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `skeleton_skeletal` / 定理 `skeleton_skeletal`

English:
theorem skeleton_skeletal
  statement: Skeletal (Skeleton C)
  proof: by
  rintro X Y ⟨h⟩
  have : X.out ≈ Y.out := ⟨(fromSkeleton C).mapIso h⟩
  simpa using! Quotient.sound this

中文:
定理 skeleton_skeletal
  结论: Skeletal (Skeleton C)
  证明: by
  rintro X Y ⟨h⟩
  have : X.out ≈ Y.out := ⟨(fromSkeleton C).mapIso h⟩
  simpa using! Quotient.sound this

Depends on / 依赖: Quotient, Quotient.sound, X.out, Y.out, fromSkeleton, mapIso
-/
theorem skeleton_skeletal : Skeletal (Skeleton C) := by
  rintro X Y ⟨h⟩
  have : X.out ≈ Y.out := ⟨(fromSkeleton C).mapIso h⟩
  simpa using! Quotient.sound this

/--
lemma `skeleton_isSkeleton` / 引理 `skeleton_isSkeleton`

English:
lemma skeleton_isSkeleton
  statement: IsSkeletonOf C (Skeleton C) (fromSkeleton C) where
  proof: skeleton_skeletal C
  eqv := fromSkeleton.isEquivalence C

中文:
引理 skeleton_isSkeleton
  结论: 是SkeletonOf C (Skeleton C) (fromSkeleton C) where
  证明: skeleton_skeletal C
  eqv := fromSkeleton.isEquivalence C

Depends on / 依赖: skeleton_skeletal
-/
lemma skeleton_isSkeleton : IsSkeletonOf C (Skeleton C) (fromSkeleton C) where
  skel := skeleton_skeletal C
  eqv := fromSkeleton.isEquivalence C

variable {C D}

/--
lemma `toSkeleton_fromSkeleton_obj` / 引理 `toSkeleton_fromSkeleton_obj`

English:
lemma toSkeleton_fromSkeleton_obj
  given: (X : Skeleton C)
  statement: toSkeleton ((fromSkeleton C).obj X) = X
  proof: Quotient.out_eq _

中文:
引理 toSkeleton_fromSkeleton_obj
  条件: (X : Skeleton C)
  结论: toSkeleton ((fromSkeleton C).obj X) = X
  证明: Quotient.out_eq _

Depends on / 依赖: Quotient, Quotient.out_eq, out_eq
-/
lemma toSkeleton_fromSkeleton_obj (X : Skeleton C) : toSkeleton ((fromSkeleton C).obj X) = X :=
  Quotient.out_eq _

/--
lemma `toSkeleton_eq_toSkeleton_iff` / 引理 `toSkeleton_eq_toSkeleton_iff`

English:
lemma toSkeleton_eq_toSkeleton_iff
  given: {X Y : C}
  statement: toSkeleton X = toSkeleton Y ↔ Nonempty (X ≅ Y)
  proof: Quotient.eq

中文:
引理 toSkeleton_eq_toSkeleton_iff
  条件: {X Y : C}
  结论: toSkeleton X = toSkeleton Y ↔ 非空 (X ≅ Y)
  证明: Quotient.eq

Depends on / 依赖: Quotient, Quotient.eq
-/
lemma toSkeleton_eq_toSkeleton_iff {X Y : C} : toSkeleton X = toSkeleton Y ↔ Nonempty (X ≅ Y) :=
  Quotient.eq

/--
lemma `congr_toSkeleton_of_iso` / 引理 `congr_toSkeleton_of_iso`

English:
lemma congr_toSkeleton_of_iso
  given: {X Y : C} (e : X ≅ Y)
  statement: toSkeleton X = toSkeleton Y
  proof: Quotient.sound ⟨e⟩

中文:
引理 congr_toSkeleton_of_iso
  条件: {X Y : C} (e : X ≅ Y)
  结论: toSkeleton X = toSkeleton Y
  证明: Quotient.sound ⟨e⟩

Depends on / 依赖: Quotient, Quotient.sound
-/
lemma congr_toSkeleton_of_iso {X Y : C} (e : X ≅ Y) : toSkeleton X = toSkeleton Y :=
  Quotient.sound ⟨e⟩

/--
Definition of `Skeleton.isoOfEq` / `Skeleton.isoOfEq` 的定义

English:
definition Skeleton.isoOfEq
  signature: {X Y : C} (h : toSkeleton X = toSkeleton Y)
  body: .some Quotient.exact h

中文:
定义 Skeleton.isoOfEq
  签名: {X Y : C} (h : toSkeleton X = toSkeleton Y)
  定义体: .some Quotient.exact h

Depends on / 依赖: Quotient, Quotient.exact
-/
noncomputable def Skeleton.isoOfEq {X Y : C} (h : toSkeleton X = toSkeleton Y) :
    X ≅ Y :=
.some Quotient.exact h

/--
lemma `toSkeleton_eq_iff` / 引理 `toSkeleton_eq_iff`

English:
lemma toSkeleton_eq_iff
  given: {X : C} {Y : Skeleton C}
  proof: Quotient.mk_eq_iff_out

中文:
引理 toSkeleton_eq_iff
  条件: {X : C} {Y : Skeleton C}
  证明: Quotient.mk_eq_iff_out

Depends on / 依赖: Quotient, Quotient.mk_eq_iff_out, mk_eq_iff_out
-/
lemma toSkeleton_eq_iff {X : C} {Y : Skeleton C} :
    toSkeleton X = Y ↔ Nonempty (X ≅ (fromSkeleton C).obj Y) :=
  Quotient.mk_eq_iff_out

namespace Functor

/--
Definition of `mapSkeleton` / `mapSkeleton` 的定义

English:
definition mapSkeleton
  signature: (F : C ⥤ D)
  body: (skeletonEquivalence C).functor ⋙ F ⋙ (skeletonEquivalence D).inverse

中文:
定义 mapSkeleton
  签名: (F : C ⥤ D)
  定义体: (skeletonEquivalence C).functor ⋙ F ⋙ (skeletonEquivalence D).inverse

Depends on / 依赖: functor, inverse, skeletonEquivalence
-/
noncomputable def mapSkeleton (F : C ⥤ D) : Skeleton C ⥤ Skeleton D :=
  (skeletonEquivalence C).functor ⋙ F ⋙ (skeletonEquivalence D).inverse

variable (F : C ⥤ D)

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `mapSkeleton_obj_toSkeleton` / 引理 `mapSkeleton_obj_toSkeleton`

English:
lemma mapSkeleton_obj_toSkeleton
  given: (X : C)
  proof: congr_toSkeleton_of_iso F.mapIso fromSkeletonToSkeletonIso X

中文:
引理 mapSkeleton_obj_toSkeleton
  条件: (X : C)
  证明: congr_toSkeleton_of_iso F.mapIso fromSkeletonToSkeletonIso X

Depends on / 依赖: F.mapIso, congr_toSkeleton_of_iso, fromSkeletonToSkeletonIso, mapIso
-/
lemma mapSkeleton_obj_toSkeleton (X : C) :
    F.mapSkeleton.obj (toSkeleton X) = toSkeleton (F.obj X) :=
congr_toSkeleton_of_iso F.mapIso fromSkeletonToSkeletonIso X

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [F.Full]
  signature: : F.mapSkeleton.Full
  body: inferInstanceAs (_ ⋙ _).Full

中文:
实例 [F.满]
  签名: : F.mapSkeleton.满
  定义体: inferInstanceAs (_ ⋙ _).Full
-/
instance [F.Full] : F.mapSkeleton.Full := inferInstanceAs (_ ⋙ _).Full

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [F.Faithful]
  signature: : F.mapSkeleton.Faithful
  body: inferInstanceAs (_ ⋙ _).Faithful

中文:
实例 [F.忠实]
  签名: : F.mapSkeleton.忠实
  定义体: inferInstanceAs (_ ⋙ _).Faithful

Depends on / 依赖: Faithful
-/
instance [F.Faithful] : F.mapSkeleton.Faithful := inferInstanceAs (_ ⋙ _).Faithful

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [F.EssSurj]
  signature: : F.mapSkeleton.EssSurj
  body: inferInstanceAs (_ ⋙ _).EssSurj

中文:
实例 [F.本质满射]
  签名: : F.mapSkeleton.本质满射
  定义体: inferInstanceAs (_ ⋙ _).EssSurj

Depends on / 依赖: EssSurj
-/
instance [F.EssSurj] : F.mapSkeleton.EssSurj := inferInstanceAs (_ ⋙ _).EssSurj

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `toSkeletonFunctorCompMapSkeletonIso` / `toSkeletonFunctorCompMapSkeletonIso` 的定义

English:
definition toSkeletonFunctorCompMapSkeletonIso
  signature: :
  body: NatIso.ofComponents
    (fun X => (toSkeletonFunctor D).mapIso <| F.mapIso <| fromSkeletonToSkeletonIso X)
    (fun f => InducedCategory.hom_ext (show (_ ≫ _) ≫ _ = _ ≫ _ by simp))

中文:
定义 toSkeletonFunctorCompMapSkeletonIso
  签名: :
  定义体: NatIso.ofComponents
    (fun X => (toSkeletonFunctor D).mapIso <| F.mapIso <| fromSkeletonToSkeletonIso X)
    (fun f => InducedCategory.hom_ext (show (_ ≫ _) ≫ _ = _ ≫ _ by simp))

Depends on / 依赖: F.mapIso, InducedCategory, InducedCategory.hom_ext, NatIso, NatIso.ofComponents, fromSkeletonToSkeletonIso, hom_ext, mapIso, ofComponents, toSkeletonFunctor
-/
noncomputable def toSkeletonFunctorCompMapSkeletonIso :
    toSkeletonFunctor C ⋙ F.mapSkeleton ≅ F ⋙ toSkeletonFunctor D :=
  NatIso.ofComponents
    (fun X => (toSkeletonFunctor D).mapIso <| F.mapIso <| fromSkeletonToSkeletonIso X)
    (fun f => InducedCategory.hom_ext (show (_ ≫ _) ≫ _ = _ ≫ _ by simp))

/--
lemma `mapSkeleton_injective` / 引理 `mapSkeleton_injective`

English:
lemma mapSkeleton_injective
  given: [F.Full] [F.Faithful]
  statement: Function.Injective F.mapSkeleton.obj
  proof: fun _ _ h => skeleton_skeletal C ⟨F.mapSkeleton.preimageIso eqToIso h⟩

中文:
引理 mapSkeleton_injective
  条件: [F.满] [F.忠实]
  结论: 函数.单射 F.mapSkeleton.obj
  证明: fun _ _ h => skeleton_skeletal C ⟨F.mapSkeleton.preimageIso eqToIso h⟩

Depends on / 依赖: F.mapSkeleton.preimageIso, eqToIso, mapSkeleton, preimageIso, skeleton_skeletal
-/
lemma mapSkeleton_injective [F.Full] [F.Faithful] : Function.Injective F.mapSkeleton.obj :=
fun _ _ h => skeleton_skeletal C ⟨F.mapSkeleton.preimageIso eqToIso h⟩

/--
lemma `mapSkeleton_surjective` / 引理 `mapSkeleton_surjective`

English:
lemma mapSkeleton_surjective
  given: [F.EssSurj]
  statement: Function.Surjective F.mapSkeleton.obj
  proof: fun Y => let ⟨X, h⟩ := EssSurj.mem_essImage F.mapSkeleton Y; ⟨X, skeleton_skeletal D h⟩

中文:
引理 mapSkeleton_surjective
  条件: [F.本质满射]
  结论: 函数.满射 F.mapSkeleton.obj
  证明: fun Y => let ⟨X, h⟩ := EssSurj.mem_essImage F.mapSkeleton Y; ⟨X, skeleton_skeletal D h⟩

Depends on / 依赖: EssSurj, EssSurj.mem_essImage, F.mapSkeleton, mapSkeleton, mem_essImage, skeleton_skeletal
-/
lemma mapSkeleton_surjective [F.EssSurj] : Function.Surjective F.mapSkeleton.obj :=
  fun Y => let ⟨X, h⟩ := EssSurj.mem_essImage F.mapSkeleton Y; ⟨X, skeleton_skeletal D h⟩

end Functor

/--
Definition of `Equivalence.skeletonEquiv` / `Equivalence.skeletonEquiv` 的定义

English:
definition Equivalence.skeletonEquiv
  signature: (e : C ≌ D)
  body: let f := ((skeletonEquivalence C).trans e).trans (skeletonEquivalence D).symm
  { toFun := f.functor.obj
    invFun := f.inverse.obj
    left_inv := fun X => skeleton_skeletal C ⟨(f.unitIso.app X).symm⟩
    right_inv := fun Y => skeleton_skeletal D ⟨f.counitIso.app Y⟩ }

中文:
定义 等价.skeletonEquiv
  签名: (e : C ≌ D)
  定义体: let f := ((skeletonEquivalence C).trans e).trans (skeletonEquivalence D).symm
  { toFun := f.functor.obj
    invFun := f.inverse.obj
    left_inv := fun X => skeleton_skeletal C ⟨(f.unitIso.app X).symm⟩
    right_inv := fun Y => skeleton_skeletal D ⟨f.counitIso.app Y⟩ }

Depends on / 依赖: counitIso, f.counitIso.app, f.functor.obj, f.inverse.obj, f.unitIso.app, functor, invFun, inverse, left_inv, right_inv, skeletonEquivalence, skeleton_skeletal, unitIso
-/
noncomputable def Equivalence.skeletonEquiv (e : C ≌ D) : Skeleton C ≃ Skeleton D :=
  let f := ((skeletonEquivalence C).trans e).trans (skeletonEquivalence D).symm
  { toFun := f.functor.obj
    invFun := f.inverse.obj
    left_inv := fun X => skeleton_skeletal C ⟨(f.unitIso.app X).symm⟩
    right_inv := fun Y => skeleton_skeletal D ⟨f.counitIso.app Y⟩ }

variable (C D)

/-- Construct the skeleton category by taking the quotient of objects. This construction gives a
preorder with nice definitional properties, but is only really appropriate for thin categories.
If your original category is not thin, you probably want to be using `Skeleton` instead of this.
-/
@[implicit_reducible]
/--
Definition of `ThinSkeleton` / `ThinSkeleton` 的定义

English:
definition ThinSkeleton
  signature: : Type u₁
  body: Quotient (isIsomorphicSetoid C)

中文:
定义 ThinSkeleton
  签名: : 类型u₁
  定义体: Quotient (isIsomorphicSetoid C)

Depends on / 依赖: Quotient, isIsomorphicSetoid
-/
def ThinSkeleton : Type u₁ :=
  Quotient (isIsomorphicSetoid C)

variable {C} in
/--
Definition of `ThinSkeleton.mk` / `ThinSkeleton.mk` 的定义

English:
abbreviation ThinSkeleton.mk
  signature: (c : C)
  body: Quotient.mk' c

中文:
缩写 ThinSkeleton.mk
  签名: (c : C)
  定义体: Quotient.mk' c

Depends on / 依赖: Quotient, Quotient.mk
-/
abbrev ThinSkeleton.mk (c : C) : ThinSkeleton C := Quotient.mk' c

/--
Instance `inhabitedThinSkeleton` / 实例 `inhabitedThinSkeleton`

English:
instance inhabitedThinSkeleton
  signature: [Inhabited C]
  body: ⟨ThinSkeleton.mk default⟩

中文:
实例 inhabitedThinSkeleton
  签名: [可居 C]
  定义体: ⟨ThinSkeleton.mk default⟩

Depends on / 依赖: ThinSkeleton, ThinSkeleton.mk
-/
instance inhabitedThinSkeleton [Inhabited C] : Inhabited (ThinSkeleton C) :=
  ⟨ThinSkeleton.mk default⟩

/--
Instance `ThinSkeleton.preorder` / 实例 `ThinSkeleton.preorder`

English:
instance ThinSkeleton.preorder
  signature: : Preorder (ThinSkeleton C) where
  body: @Quotient.lift₂ C C _ (isIsomorphicSetoid C) (isIsomorphicSetoid C)
      (fun X Y => Nonempty (X ⟶ Y))
        (by
          rintro _ _ _ _ ⟨i₁⟩ ⟨i₂⟩
          exact
            propext
              ⟨Nonempty.map fun f => i₁.inv ≫ f ≫ i₂.hom,
                Nonempty.map fun f => i₁.hom ≫ f ≫ i₂.inv⟩)
  le_refl := by
    refine Quotient.ind fun a => ?_
    exact ⟨𝟙 _⟩
  le_trans a b c := Quotient.inductionOn₃ a b c fun _ _ _ => Nonempty.map2 (· ≫ ·)

中文:
实例 ThinSkeleton.preorder
  签名: : 预序 (ThinSkeleton C) where
  定义体: @Quotient.lift₂ C C _ (isIsomorphicSetoid C) (isIsomorphicSetoid C)
      (fun X Y => Nonempty (X ⟶ Y))
        (by
          rintro _ _ _ _ ⟨i₁⟩ ⟨i₂⟩
          exact
            propext
              ⟨Nonempty.map fun f => i₁.inv ≫ f ≫ i₂.hom,
                Nonempty.map fun f => i₁.hom ≫ f ≫ i₂.inv⟩)
  le_refl := by
    refine Quotient.ind fun a => ?_
    exact ⟨𝟙 _⟩
  le_trans a b c := Quotient.inductionOn₃ a b c fun _ _ _ => Nonempty.map2 (· ≫ ·)

Depends on / 依赖: Nonempty, Nonempty.map, Nonempty.map2, Quotient, Quotient.ind, Quotient.inductionOn, Quotient.lift, isIsomorphicSetoid, le_refl, le_trans, propext
-/
instance ThinSkeleton.preorder : Preorder (ThinSkeleton C) where
  le :=
    @Quotient.lift₂ C C _ (isIsomorphicSetoid C) (isIsomorphicSetoid C)
      (fun X Y => Nonempty (X ⟶ Y))
        (by
          rintro _ _ _ _ ⟨i₁⟩ ⟨i₂⟩
          exact
            propext
              ⟨Nonempty.map fun f => i₁.inv ≫ f ≫ i₂.hom,
                Nonempty.map fun f => i₁.hom ≫ f ≫ i₂.inv⟩)
  le_refl := by
    refine Quotient.ind fun a => ?_
    exact ⟨𝟙 _⟩
  le_trans a b c := Quotient.inductionOn₃ a b c fun _ _ _ => Nonempty.map2 (· ≫ ·)

/-- The functor from a category to its thin skeleton. -/
@[simps, implicit_reducible]
/--
Definition of `toThinSkeleton` / `toThinSkeleton` 的定义

English:
definition toThinSkeleton
  signature: : C ⥤ ThinSkeleton C where
  body: ThinSkeleton.mk
  map f := homOfLE (Nonempty.intro f)

中文:
定义 toThinSkeleton
  签名: : C ⥤ ThinSkeleton C where
  定义体: ThinSkeleton.mk
  map f := homOfLE (Nonempty.intro f)

Depends on / 依赖: ThinSkeleton, ThinSkeleton.mk
-/
def toThinSkeleton : C ⥤ ThinSkeleton C where
  obj := ThinSkeleton.mk
  map f := homOfLE (Nonempty.intro f)

/-!
The constructions here are intended to be used when the category `C` is thin, even though
some of the statements can be shown without this assumption.
-/


namespace ThinSkeleton

/--
Instance `thin` / 实例 `thin`

English:
instance thin
  signature: : Quiver.IsThin (ThinSkeleton C)
  body: fun _ _ =>
  ⟨by
    rintro ⟨⟨f₁⟩⟩ ⟨⟨_⟩⟩
    rfl⟩

中文:
实例 thin
  签名: : 箭图.IsThin (ThinSkeleton C)
  定义体: fun _ _ =>
  ⟨by
    rintro ⟨⟨f₁⟩⟩ ⟨⟨_⟩⟩
    rfl⟩
-/
instance thin : Quiver.IsThin (ThinSkeleton C) := fun _ _ =>
  ⟨by
    rintro ⟨⟨f₁⟩⟩ ⟨⟨_⟩⟩
    rfl⟩

variable {C} {D}

set_option backward.isDefEq.respectTransparency.types false in
/-- A functor `C ⥤ D` computably lowers to a functor `ThinSkeleton C ⥤ ThinSkeleton D`. -/
@[simps]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (F : C ⥤ D)
  body: Quotient.map F.obj fun _ _ ⟨hX⟩ => ⟨F.mapIso hX⟩
  map {X} {Y} := Quotient.recOnSubsingleton₂ X Y fun _ _ k => homOfLE (k.le.elim fun t => ⟨F.map t⟩)

中文:
定义 map
  签名: (F : C ⥤ D)
  定义体: Quotient.map F.obj fun _ _ ⟨hX⟩ => ⟨F.mapIso hX⟩
  map {X} {Y} := Quotient.recOnSubsingleton₂ X Y fun _ _ k => homOfLE (k.le.elim fun t => ⟨F.map t⟩)

Depends on / 依赖: F.mapIso, F.obj, Quotient, Quotient.map, mapIso
-/
def map (F : C ⥤ D) : ThinSkeleton C ⥤ ThinSkeleton D where
  obj := Quotient.map F.obj fun _ _ ⟨hX⟩ => ⟨F.mapIso hX⟩
  map {X} {Y} := Quotient.recOnSubsingleton₂ X Y fun _ _ k => homOfLE (k.le.elim fun t => ⟨F.map t⟩)

/--
theorem `comp_toThinSkeleton` / 定理 `comp_toThinSkeleton`

English:
theorem comp_toThinSkeleton
  given: (F : C ⥤ D)
  statement: F ⋙ toThinSkeleton D = toThinSkeleton C ⋙ map F
  proof: rfl

中文:
定理 comp_toThinSkeleton
  条件: (F : C ⥤ D)
  结论: F ⋙ toThinSkeleton D = toThinSkeleton C ⋙ map F
  证明: rfl
-/
theorem comp_toThinSkeleton (F : C ⥤ D) : F ⋙ toThinSkeleton D = toThinSkeleton C ⋙ map F :=
  rfl

/--
Definition of `mapNatTrans` / `mapNatTrans` 的定义

English:
definition mapNatTrans
  signature: {F₁ F₂ : C ⥤ D} (k : F₁ ⟶ F₂)
  body: Quotient.recOnSubsingleton X fun x => ⟨⟨⟨k.app x⟩⟩⟩

中文:
定义 map自然数Trans
  签名: {F₁ F₂ : C ⥤ D} (k : F₁ ⟶ F₂)
  定义体: Quotient.recOnSubsingleton X fun x => ⟨⟨⟨k.app x⟩⟩⟩

Depends on / 依赖: Quotient, Quotient.recOnSubsingleton, k.app, recOnSubsingleton
-/
def mapNatTrans {F₁ F₂ : C ⥤ D} (k : F₁ ⟶ F₂) : map F₁ ⟶ map F₂ where
  app X := Quotient.recOnSubsingleton X fun x => ⟨⟨⟨k.app x⟩⟩⟩

/- Porting note: `map₂ObjMap`, `map₂Functor`, and `map₂NatTrans` were all extracted
from the original `map₂` proof. Lean needed an extensive amount of explicit type
annotations to figure things out. This also translated into repeated deterministic
timeouts. The extracted defs allow for explicit motives for the multiple
descents to the quotients.

It would be better to prove that
`ThinSkeleton (C × D) ≌ ThinSkeleton C × ThinSkeleton D`
which is more immediate from comparing the preorders. Then one could get
`map₂` by currying.
-/
/--
Definition of `map₂ObjMap` / `map₂ObjMap` 的定义

English:
definition map₂ObjMap
  signature: (F : C ⥤ D ⥤ E)
  body: fun x y =>
    @Quotient.map₂ C D (isIsomorphicSetoid C) (isIsomorphicSetoid D) E (isIsomorphicSetoid E)
      (fun X Y => (F.obj X).obj Y)
          (fun X₁ _ ⟨hX⟩ _ Y₂ ⟨hY⟩ => ⟨(F.obj X₁).mapIso hY ≪≫ (F.mapIso hX).app Y₂⟩) x y

中文:
定义 map₂ObjMap
  签名: (F : C ⥤ D ⥤ E)
  定义体: fun x y =>
    @Quotient.map₂ C D (isIsomorphicSetoid C) (isIsomorphicSetoid D) E (isIsomorphicSetoid E)
      (fun X Y => (F.obj X).obj Y)
          (fun X₁ _ ⟨hX⟩ _ Y₂ ⟨hY⟩ => ⟨(F.obj X₁).mapIso hY ≪≫ (F.mapIso hX).app Y₂⟩) x y

Depends on / 依赖: F.mapIso, F.obj, Quotient, Quotient.map, isIsomorphicSetoid, mapIso
-/
def map₂ObjMap (F : C ⥤ D ⥤ E) : ThinSkeleton C -> ThinSkeleton D -> ThinSkeleton E :=
  fun x y =>
    @Quotient.map₂ C D (isIsomorphicSetoid C) (isIsomorphicSetoid D) E (isIsomorphicSetoid E)
      (fun X Y => (F.obj X).obj Y)
          (fun X₁ _ ⟨hX⟩ _ Y₂ ⟨hY⟩ => ⟨(F.obj X₁).mapIso hY ≪≫ (F.mapIso hX).app Y₂⟩) x y

/--
Definition of `map₂Functor` / `map₂Functor` 的定义

English:
definition map₂Functor
  signature: (F : C ⥤ D ⥤ E)
  body: fun x =>
    { obj := fun y => map₂ObjMap F x y
      map := fun {y₁} {y₂} => @Quotient.recOnSubsingleton C (isIsomorphicSetoid C)
        (fun x => (y₁ ⟶ y₂) -> (map₂ObjMap F x y₁ ⟶ map₂ObjMap F x y₂)) _ x fun X
          => Quotient.recOnSubsingleton₂ y₁ y₂ fun _ _ hY =>
            homOfLE (hY.le.elim fun g => ⟨(F.obj X).map g⟩) }

中文:
定义 map₂Functor
  签名: (F : C ⥤ D ⥤ E)
  定义体: fun x =>
    { obj := fun y => map₂ObjMap F x y
      map := fun {y₁} {y₂} => @Quotient.recOnSubsingleton C (isIsomorphicSetoid C)
        (fun x => (y₁ ⟶ y₂) -> (map₂ObjMap F x y₁ ⟶ map₂ObjMap F x y₂)) _ x fun X
          => Quotient.recOnSubsingleton₂ y₁ y₂ fun _ _ hY =>
            homOfLE (hY.le.elim fun g => ⟨(F.obj X).map g⟩) }

Depends on / 依赖: F.obj, Quotient, Quotient.recOnSubsingleton, hY.le.elim, homOfLE, isIsomorphicSetoid, recOnSubsingleton
-/
def map₂Functor (F : C ⥤ D ⥤ E) : ThinSkeleton C -> ThinSkeleton D ⥤ ThinSkeleton E :=
  fun x =>
    { obj := fun y => map₂ObjMap F x y
      map := fun {y₁} {y₂} => @Quotient.recOnSubsingleton C (isIsomorphicSetoid C)
        (fun x => (y₁ ⟶ y₂) -> (map₂ObjMap F x y₁ ⟶ map₂ObjMap F x y₂)) _ x fun X
          => Quotient.recOnSubsingleton₂ y₁ y₂ fun _ _ hY =>
            homOfLE (hY.le.elim fun g => ⟨(F.obj X).map g⟩) }

/--
Definition of `map₂NatTrans` / `map₂NatTrans` 的定义

English:
definition map₂NatTrans
  signature: (F : C ⥤ D ⥤ E)
  body: fun {x₁} {x₂} =>
  @Quotient.recOnSubsingleton₂ C C (isIsomorphicSetoid C) (isIsomorphicSetoid C)
    (fun x x' : ThinSkeleton C => (x ⟶ x') -> (map₂Functor F x ⟶ map₂Functor F x')) _ x₁ x₂
    (fun X₁ X₂ f => { app := fun y =>
      Quotient.recOnSubsingleton y fun Y => homOfLE (f.le.elim fun f' => ⟨(F.map f').app Y⟩) })

中文:
定义 map₂自然数Trans
  签名: (F : C ⥤ D ⥤ E)
  定义体: fun {x₁} {x₂} =>
  @Quotient.recOnSubsingleton₂ C C (isIsomorphicSetoid C) (isIsomorphicSetoid C)
    (fun x x' : ThinSkeleton C => (x ⟶ x') -> (map₂Functor F x ⟶ map₂Functor F x')) _ x₁ x₂
    (fun X₁ X₂ f => { app := fun y =>
      Quotient.recOnSubsingleton y fun Y => homOfLE (f.le.elim fun f' => ⟨(F.map f').app Y⟩) })
-/
def map₂NatTrans (F : C ⥤ D ⥤ E) : {x₁ x₂ : ThinSkeleton C} -> (x₁ ⟶ x₂) ->
    (map₂Functor F x₁ ⟶ map₂Functor F x₂) := fun {x₁} {x₂} =>
  @Quotient.recOnSubsingleton₂ C C (isIsomorphicSetoid C) (isIsomorphicSetoid C)
    (fun x x' : ThinSkeleton C => (x ⟶ x') -> (map₂Functor F x ⟶ map₂Functor F x')) _ x₁ x₂
    (fun X₁ X₂ f => { app := fun y =>
      Quotient.recOnSubsingleton y fun Y => homOfLE (f.le.elim fun f' => ⟨(F.map f').app Y⟩) })

-- TODO: state the lemmas about what happens when you compose with `toThinSkeleton`
/-- A functor `C ⥤ D ⥤ E` computably lowers to a functor
`ThinSkeleton C ⥤ ThinSkeleton D ⥤ ThinSkeleton E` -/
@[simps]
/--
Definition of `map₂` / `map₂` 的定义

English:
definition map₂
  signature: (F : C ⥤ D ⥤ E)
  body: map₂Functor F
  map := map₂NatTrans F

中文:
定义 map₂
  签名: (F : C ⥤ D ⥤ E)
  定义体: map₂Functor F
  map := map₂NatTrans F
-/
def map₂ (F : C ⥤ D ⥤ E) : ThinSkeleton C ⥤ ThinSkeleton D ⥤ ThinSkeleton E where
  obj := map₂Functor F
  map := map₂NatTrans F

variable (C)

section

variable [Quiver.IsThin C]

/--
Instance `toThinSkeleton_faithful` / 实例 `toThinSkeleton_faithful`

English:
instance toThinSkeleton_faithful
  signature: : (toThinSkeleton C).Faithful where

中文:
实例 toThinSkeleton_faithful
  签名: : (toThinSkeleton C).忠实 where
-/
instance toThinSkeleton_faithful : (toThinSkeleton C).Faithful where

/-- Use `Quotient.out` to create a functor out of the thin skeleton. -/
@[simps]
/--
Definition of `fromThinSkeleton` / `fromThinSkeleton` 的定义

English:
definition fromThinSkeleton
  signature: : ThinSkeleton C ⥤ C where
  body: Quotient.out
  map {x} {y} :=
    Quotient.recOnSubsingleton₂ x y fun X Y f =>
      (Nonempty.some (Quotient.mk_out X)).hom ≫ f.le.some ≫ (Nonempty.some (Quotient.mk_out Y)).inv

中文:
定义 fromThinSkeleton
  签名: : ThinSkeleton C ⥤ C where
  定义体: Quotient.out
  map {x} {y} :=
    Quotient.recOnSubsingleton₂ x y fun X Y f =>
      (Nonempty.some (Quotient.mk_out X)).hom ≫ f.le.some ≫ (Nonempty.some (Quotient.mk_out Y)).inv

Depends on / 依赖: Quotient, Quotient.out
-/
noncomputable def fromThinSkeleton : ThinSkeleton C ⥤ C where
  obj := Quotient.out
  map {x} {y} :=
    Quotient.recOnSubsingleton₂ x y fun X Y f =>
      (Nonempty.some (Quotient.mk_out X)).hom ≫ f.le.some ≫ (Nonempty.some (Quotient.mk_out Y)).inv

/--
Definition of `equivalence` / `equivalence` 的定义

English:
definition equivalence
  signature: : ThinSkeleton C ≌ C where
  body: fromThinSkeleton C
  inverse := toThinSkeleton C
  counitIso := NatIso.ofComponents fun X => Nonempty.some (Quotient.mk_out X)
  unitIso := NatIso.ofComponents fun x => Quotient.recOnSubsingleton x fun X =>
    eqToIso (Quotient.sound ⟨(Nonempty.some (Quotient.mk_out X)).symm⟩)

中文:
定义 equivalence
  签名: : ThinSkeleton C ≌ C where
  定义体: fromThinSkeleton C
  inverse := toThinSkeleton C
  counitIso := NatIso.ofComponents fun X => Nonempty.some (Quotient.mk_out X)
  unitIso := NatIso.ofComponents fun x => Quotient.recOnSubsingleton x fun X =>
    eqToIso (Quotient.sound ⟨(Nonempty.some (Quotient.mk_out X)).symm⟩)

Depends on / 依赖: fromThinSkeleton
-/
noncomputable def equivalence : ThinSkeleton C ≌ C where
  functor := fromThinSkeleton C
  inverse := toThinSkeleton C
  counitIso := NatIso.ofComponents fun X => Nonempty.some (Quotient.mk_out X)
  unitIso := NatIso.ofComponents fun x => Quotient.recOnSubsingleton x fun X =>
    eqToIso (Quotient.sound ⟨(Nonempty.some (Quotient.mk_out X)).symm⟩)

/--
Instance `fromThinSkeleton_isEquivalence` / 实例 `fromThinSkeleton_isEquivalence`

English:
instance fromThinSkeleton_isEquivalence
  signature: : (fromThinSkeleton C).IsEquivalence
  body: (equivalence C).isEquivalence_functor

中文:
实例 fromThinSkeleton_isEquivalence
  签名: : (fromThinSkeleton C).是等价
  定义体: (equivalence C).isEquivalence_functor

Depends on / 依赖: equivalence, isEquivalence_functor
-/
noncomputable instance fromThinSkeleton_isEquivalence : (fromThinSkeleton C).IsEquivalence :=
  (equivalence C).isEquivalence_functor

variable {C}

/--
theorem `equiv_of_both_ways` / 定理 `equiv_of_both_ways`

English:
theorem equiv_of_both_ways
  given: {X Y : C} (f : X ⟶ Y) (g : Y ⟶ X)
  statement: X ≈ Y
  proof: ⟨iso_of_both_ways f g⟩

中文:
定理 equiv_of_both_ways
  条件: {X Y : C} (f : X ⟶ Y) (g : Y ⟶ X)
  结论: X ≈ Y
  证明: ⟨iso_of_both_ways f g⟩

Depends on / 依赖: iso_of_both_ways
-/
theorem equiv_of_both_ways {X Y : C} (f : X ⟶ Y) (g : Y ⟶ X) : X ≈ Y :=
  ⟨iso_of_both_ways f g⟩

/--
Instance `thinSkeletonPartialOrder` / 实例 `thinSkeletonPartialOrder`

English:
instance thinSkeletonPartialOrder
  signature: : PartialOrder (ThinSkeleton C)
  body: { CategoryTheory.ThinSkeleton.preorder C with
    le_antisymm :=
      Quotient.ind₂
        (by
          rintro _ _ ⟨f⟩ ⟨g⟩
          apply Quotient.sound (equiv_of_both_ways f g)) }

中文:
实例 thinSkeletonPartialOrder
  签名: : 偏序 (ThinSkeleton C)
  定义体: { CategoryTheory.ThinSkeleton.preorder C with
    le_antisymm :=
      Quotient.ind₂
        (by
          rintro _ _ ⟨f⟩ ⟨g⟩
          apply Quotient.sound (equiv_of_both_ways f g)) }

Depends on / 依赖: CategoryTheory, CategoryTheory.ThinSkeleton.preorder, Quotient, Quotient.ind, Quotient.sound, ThinSkeleton, equiv_of_both_ways, le_antisymm, preorder
-/
instance thinSkeletonPartialOrder : PartialOrder (ThinSkeleton C) :=
  { CategoryTheory.ThinSkeleton.preorder C with
    le_antisymm :=
      Quotient.ind₂
        (by
          rintro _ _ ⟨f⟩ ⟨g⟩
          apply Quotient.sound (equiv_of_both_ways f g)) }

/--
theorem `skeletal` / 定理 `skeletal`

English:
theorem skeletal
  statement: Skeletal (ThinSkeleton C)
  proof: fun X Y =>
  Quotient.inductionOn₂ X Y fun _ _ h => h.elim fun i => i.1.le.antisymm i.2.le

中文:
定理 skeletal
  结论: Skeletal (ThinSkeleton C)
  证明: fun X Y =>
  Quotient.inductionOn₂ X Y fun _ _ h => h.elim fun i => i.1.le.antisymm i.2.le
-/
theorem skeletal : Skeletal (ThinSkeleton C) := fun X Y =>
  Quotient.inductionOn₂ X Y fun _ _ h => h.elim fun i => i.1.le.antisymm i.2.le

/--
theorem `map_comp_eq` / 定理 `map_comp_eq`

English:
theorem map_comp_eq
  given: (F : E ⥤ D) (G : D ⥤ C)
  statement: map (F ⋙ G) = map F ⋙ map G
  proof: Functor.eq_of_iso skeletal
    NatIso.ofComponents fun X => Quotient.recOnSubsingleton X fun _ => Iso.refl _

中文:
定理 map_comp_eq
  条件: (F : E ⥤ D) (G : D ⥤ C)
  结论: map (F ⋙ G) = map F ⋙ map G
  证明: Functor.eq_of_iso skeletal
    NatIso.ofComponents fun X => Quotient.recOnSubsingleton X fun _ => Iso.refl _

Depends on / 依赖: Functor, Functor.eq_of_iso, Iso.refl, NatIso, NatIso.ofComponents, Quotient, Quotient.recOnSubsingleton, eq_of_iso, ofComponents, recOnSubsingleton, skeletal
-/
theorem map_comp_eq (F : E ⥤ D) (G : D ⥤ C) : map (F ⋙ G) = map F ⋙ map G :=
Functor.eq_of_iso skeletal
    NatIso.ofComponents fun X => Quotient.recOnSubsingleton X fun _ => Iso.refl _

/--
theorem `map_id_eq` / 定理 `map_id_eq`

English:
theorem map_id_eq
  statement: map (𝟭 C) = 𝟭 (ThinSkeleton C)
  proof: Functor.eq_of_iso skeletal
    NatIso.ofComponents fun X => Quotient.recOnSubsingleton X fun _ => Iso.refl _

中文:
定理 map_id_eq
  结论: map (𝟭 C) = 𝟭 (ThinSkeleton C)
  证明: Functor.eq_of_iso skeletal
    NatIso.ofComponents fun X => Quotient.recOnSubsingleton X fun _ => Iso.refl _

Depends on / 依赖: Functor, Functor.eq_of_iso, Iso.refl, NatIso, NatIso.ofComponents, Quotient, Quotient.recOnSubsingleton, eq_of_iso, ofComponents, recOnSubsingleton, skeletal
-/
theorem map_id_eq : map (𝟭 C) = 𝟭 (ThinSkeleton C) :=
Functor.eq_of_iso skeletal
    NatIso.ofComponents fun X => Quotient.recOnSubsingleton X fun _ => Iso.refl _

/--
theorem `map_iso_eq` / 定理 `map_iso_eq`

English:
theorem map_iso_eq
  given: {F₁ F₂ : D ⥤ C} (h : F₁ ≅ F₂)
  statement: map F₁ = map F₂
  proof: Functor.eq_of_iso skeletal
    { hom := mapNatTrans h.hom
      inv := mapNatTrans h.inv }

中文:
定理 map_iso_eq
  条件: {F₁ F₂ : D ⥤ C} (h : F₁ ≅ F₂)
  结论: map F₁ = map F₂
  证明: Functor.eq_of_iso skeletal
    { hom := mapNatTrans h.hom
      inv := mapNatTrans h.inv }

Depends on / 依赖: Functor, Functor.eq_of_iso, eq_of_iso, h.hom, h.inv, mapNatTrans, skeletal
-/
theorem map_iso_eq {F₁ F₂ : D ⥤ C} (h : F₁ ≅ F₂) : map F₁ = map F₂ :=
  Functor.eq_of_iso skeletal
    { hom := mapNatTrans h.hom
      inv := mapNatTrans h.inv }

/--
Definition of `fromThinSkeletonCompToThinSkeletonIso` / `fromThinSkeletonCompToThinSkeletonIso` 的定义

English:
definition fromThinSkeletonCompToThinSkeletonIso
  signature: (F : C ⥤ D)
  body: Functor.isoWhiskerLeft (fromThinSkeleton C) (Iso.refl _) ≪≫
    Functor.isoWhiskerRight (equivalence C).unitIso.symm (map F) ≪≫
    Functor.leftUnitor (map F)

中文:
定义 fromThinSkeletonCompToThinSkeletonIso
  签名: (F : C ⥤ D)
  定义体: Functor.isoWhiskerLeft (fromThinSkeleton C) (Iso.refl _) ≪≫
    Functor.isoWhiskerRight (equivalence C).unitIso.symm (map F) ≪≫
    Functor.leftUnitor (map F)

Depends on / 依赖: Functor, Functor.isoWhiskerLeft, Functor.isoWhiskerRight, Functor.leftUnitor, Iso.refl, equivalence, fromThinSkeleton, isoWhiskerLeft, isoWhiskerRight, leftUnitor, unitIso, unitIso.symm
-/
noncomputable def fromThinSkeletonCompToThinSkeletonIso (F : C ⥤ D) :
    fromThinSkeleton C ⋙ F ⋙ toThinSkeleton D ≅ map F :=
  Functor.isoWhiskerLeft (fromThinSkeleton C) (Iso.refl _) ≪≫
    Functor.isoWhiskerRight (equivalence C).unitIso.symm (map F) ≪≫
    Functor.leftUnitor (map F)

/--
Definition of `mapCompFromThinSkeletonIso` / `mapCompFromThinSkeletonIso` 的定义

English:
definition mapCompFromThinSkeletonIso
  signature: [Quiver.IsThin D] (F : C ⥤ D)
  body: Functor.isoWhiskerRight (fromThinSkeletonCompToThinSkeletonIso F).symm _ ≪≫
    Functor.isoWhiskerLeft (fromThinSkeleton C ⋙ F) (equivalence D).counitIso ≪≫
    Functor.rightUnitor (fromThinSkeleton C ⋙ F)

中文:
定义 mapCompFromThinSkeletonIso
  签名: [箭图.IsThin D] (F : C ⥤ D)
  定义体: Functor.isoWhiskerRight (fromThinSkeletonCompToThinSkeletonIso F).symm _ ≪≫
    Functor.isoWhiskerLeft (fromThinSkeleton C ⋙ F) (equivalence D).counitIso ≪≫
    Functor.rightUnitor (fromThinSkeleton C ⋙ F)

Depends on / 依赖: Functor, Functor.isoWhiskerLeft, Functor.isoWhiskerRight, Functor.rightUnitor, counitIso, equivalence, fromThinSkeleton, fromThinSkeletonCompToThinSkeletonIso, isoWhiskerLeft, isoWhiskerRight, rightUnitor
-/
noncomputable def mapCompFromThinSkeletonIso [Quiver.IsThin D] (F : C ⥤ D) :
    map F ⋙ fromThinSkeleton D ≅ fromThinSkeleton C ⋙ F :=
  Functor.isoWhiskerRight (fromThinSkeletonCompToThinSkeletonIso F).symm _ ≪≫
    Functor.isoWhiskerLeft (fromThinSkeleton C ⋙ F) (equivalence D).counitIso ≪≫
    Functor.rightUnitor (fromThinSkeleton C ⋙ F)

/--
lemma `thinSkeleton_isSkeleton` / 引理 `thinSkeleton_isSkeleton`

English:
lemma thinSkeleton_isSkeleton
  statement: IsSkeletonOf C (ThinSkeleton C) (fromThinSkeleton C) where
  proof: skeletal

中文:
引理 thinSkeleton_isSkeleton
  结论: 是SkeletonOf C (ThinSkeleton C) (fromThinSkeleton C) where
  证明: skeletal

Depends on / 依赖: skeletal
-/
lemma thinSkeleton_isSkeleton : IsSkeletonOf C (ThinSkeleton C) (fromThinSkeleton C) where
  skel := skeletal

/--
Instance `isSkeletonOfInhabited` / 实例 `isSkeletonOfInhabited`

English:
instance isSkeletonOfInhabited
  signature: :
  body: ⟨thinSkeleton_isSkeleton⟩

中文:
实例 isSkeletonOfInhabited
  签名: :
  定义体: ⟨thinSkeleton_isSkeleton⟩

Depends on / 依赖: thinSkeleton_isSkeleton
-/
instance isSkeletonOfInhabited :
    Inhabited (IsSkeletonOf C (ThinSkeleton C) (fromThinSkeleton C)) :=
  ⟨thinSkeleton_isSkeleton⟩

end

variable {C}

/--
Definition of `lowerAdjunction` / `lowerAdjunction` 的定义

English:
definition lowerAdjunction
  signature: (R : D ⥤ C) (L : C ⥤ D) (h : L ⊣ R)
  body: { app := fun X => by
        letI := isIsomorphicSetoid C
        exact Quotient.recOnSubsingleton X fun x => homOfLE ⟨h.unit.app x⟩ }
      -- TODO: make quotient.rec_on_subsingleton' so the letI isn't needed
  counit :=
    { app := fun X => by
        letI := isIsomorphicSetoid D
        exact Quotient.recOnSubsingleton X fun x => homOfLE ⟨h.counit.app x⟩ }

中文:
定义 lowerAdjunction
  签名: (R : D ⥤ C) (L : C ⥤ D) (h : L ⊣ R)
  定义体: { app := fun X => by
        letI := isIsomorphicSetoid C
        exact Quotient.recOnSubsingleton X fun x => homOfLE ⟨h.unit.app x⟩ }
      -- TODO: make quotient.rec_on_subsingleton' so the letI isn't needed
  counit :=
    { app := fun X => by
        letI := isIsomorphicSetoid D
        exact Quotient.recOnSubsingleton X fun x => homOfLE ⟨h.counit.app x⟩ }

Depends on / 依赖: Quotient, Quotient.recOnSubsingleton, h.unit.app, homOfLE, isIsomorphicSetoid, recOnSubsingleton
-/
def lowerAdjunction (R : D ⥤ C) (L : C ⥤ D) (h : L ⊣ R) :
    ThinSkeleton.map L ⊣ ThinSkeleton.map R where
  unit :=
    { app := fun X => by
        letI := isIsomorphicSetoid C
        exact Quotient.recOnSubsingleton X fun x => homOfLE ⟨h.unit.app x⟩ }
      -- TODO: make quotient.rec_on_subsingleton' so the letI isn't needed
  counit :=
    { app := fun X => by
        letI := isIsomorphicSetoid D
        exact Quotient.recOnSubsingleton X fun x => homOfLE ⟨h.counit.app x⟩ }

end ThinSkeleton

open ThinSkeleton

section

variable {C} {α : Type*} [PartialOrder α]

/--
Definition of `Equivalence.thinSkeletonOrderIso` / `Equivalence.thinSkeletonOrderIso` 的定义

English:
definition Equivalence.thinSkeletonOrderIso
  signature: [Quiver.IsThin C] (e : C ≌ α)
  body: ((ThinSkeleton.equivalence C).trans e).toOrderIso

中文:
定义 等价.thinSkeletonOrderIso
  签名: [箭图.IsThin C] (e : C ≌ α)
  定义体: ((ThinSkeleton.equivalence C).trans e).toOrderIso

Depends on / 依赖: ThinSkeleton, ThinSkeleton.equivalence, equivalence, toOrderIso
-/
noncomputable def Equivalence.thinSkeletonOrderIso [Quiver.IsThin C] (e : C ≌ α) :
    ThinSkeleton C ≃o α :=
  ((ThinSkeleton.equivalence C).trans e).toOrderIso

end

end CategoryTheory
