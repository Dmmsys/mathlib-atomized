/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.LeftResolution.Transport
public import Mathlib.CategoryTheory.Idempotents.FunctorExtension
public import Mathlib.CategoryTheory.MorphismProperty.Retract

/-!
# Left resolutions which preserve the zero object

The structure `LeftResolution` allows to define a functorial
resolution of an object (see `LeftResolution.chainComplexFunctor`
in the file `Mathlib/Algebra/Homology/LeftResolution/Basic.lean`). In
order to extend this resolution to complexes, we not only
need the functoriality but also that zero morphisms
are sent to zero. In this file, given `ι : C ⥤ A`,
we extend `Λ : LeftResolution ι` to idempotent completions as
`Λ.karoubi : LeftResolution ((functorExtension₂ C A).obj ι)`, and
when both `C` and `A` are idempotent complete, we define
`Λ.reduced : LeftResolution ι` in such a way that the
functor `Λ.reduced.F : A ⥤ C` preserves zero morphisms.

For example, if `A := ModuleCat R` and `C` is the full subcategory
of flat `R`-modules, we may first define `Λ` by using the
functor which sends an `R`-module `M` to the free `R`-module
on the elements of `M`. Then, `Λ.reduced.F.obj M` will be obtained
from the free `R`-module on `M` by factoring out the direct factor
corresponding to the submodule spanned by the generator corresponding
to `0 : M` (TODO).

-/

@[expose] public section

namespace CategoryTheory.Abelian

variable {A C : Type*} [Category* C] [Category* A] {ι : C ⥤ A}
  (Λ : LeftResolution ι)

open Idempotents Limits MorphismProperty

namespace LeftResolution

variable [Preadditive C] [Preadditive A] [ι.Additive]

/-- Auxiliary definition for `LeftResolution.karoubi`. -/
@[simps]
/--
Definition of `karoubi.F'` / `karoubi.F'` 的定义

English:
definition karoubi.F'
  signature: : A ⥤ Karoubi C where
  body: ⟨Λ.F.obj X, 𝟙 _ - Λ.F.map 0, by simp [← Functor.map_comp]⟩
  map {X Y} f := ⟨Λ.F.map f - Λ.F.map 0, by simp [← Functor.map_comp]⟩
  map_comp _ _ := by simp [← Functor.map_comp]

中文:
定义 karoubi.F'
  签名: : A ⥤ Karoubi C where
  定义体: ⟨Λ.F.obj X, 𝟙 _ - Λ.F.map 0, by simp [← Functor.map_comp]⟩
  map {X Y} f := ⟨Λ.F.map f - Λ.F.map 0, by simp [← Functor.map_comp]⟩
  map_comp _ _ := by simp [← Functor.map_comp]

Depends on / 依赖: F.map, F.obj, Functor, Functor.map_comp, map_comp
-/
def karoubi.F' : A ⥤ Karoubi C where
  obj X := ⟨Λ.F.obj X, 𝟙 _ - Λ.F.map 0, by simp [← Functor.map_comp]⟩
  map {X Y} f := ⟨Λ.F.map f - Λ.F.map 0, by simp [← Functor.map_comp]⟩
  map_comp _ _ := by simp [← Functor.map_comp]

/-- Auxiliary definition for `LeftResolution.karoubi`. -/
@[simps!]
/--
Definition of `karoubi.F` / `karoubi.F` 的定义

English:
definition karoubi.F
  signature: : Karoubi A ⥤ Karoubi C
  body: (functorExtension₁ A C).obj (karoubi.F' Λ)

中文:
定义 karoubi.F
  签名: : Karoubi A ⥤ Karoubi C
  定义体: (functorExtension₁ A C).obj (karoubi.F' Λ)

Depends on / 依赖: karoubi, karoubi.F
-/
def karoubi.F : Karoubi A ⥤ Karoubi C := (functorExtension₁ A C).obj (karoubi.F' Λ)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (karoubi.F Λ).PreservesZeroMorphisms

中文:
实例 :
  签名: (karoubi.F Λ).PreservesZeroMorphisms
-/
instance : (karoubi.F Λ).PreservesZeroMorphisms where

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `LeftResolution.karoubi`. -/
@[simps]
/--
Definition of `karoubi.π'` / `karoubi.π'` 的定义

English:
definition karoubi.π'
  signature: : toKaroubi A ⋙ F Λ ⋙ (functorExtension₂ C A).obj ι ⟶ toKaroubi A where
  body: ⟨Λ.π.app X, by simp⟩

中文:
定义 karoubi.π'
  签名: : toKaroubi A ⋙ F Λ ⋙ (functorExtension₂ C A).obj ι ⟶ toKaroubi A where
  定义体: ⟨Λ.π.app X, by simp⟩
-/
def karoubi.π' : toKaroubi A ⋙ F Λ ⋙ (functorExtension₂ C A).obj ι ⟶ toKaroubi A where
  app X := ⟨Λ.π.app X, by simp⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `karoubi.retractArrow` / `karoubi.retractArrow` 的定义

English:
definition karoubi.retractArrow
  signature: (X : A)
  body: Arrow.homMk ⟨ι.map ((karoubi.F' Λ).obj X).p, by simp [← Functor.map_comp]⟩ (𝟙 _)
  r := Arrow.homMk ⟨ι.map ((karoubi.F' Λ).obj X).p, by simp [← Functor.map_comp]⟩ (𝟙 _)
  retract := by
    ext
    · simp [← Functor.map_comp]
    · simp

中文:
定义 karoubi.retractArrow
  签名: (X : A)
  定义体: Arrow.homMk ⟨ι.map ((karoubi.F' Λ).obj X).p, by simp [← Functor.map_comp]⟩ (𝟙 _)
  r := Arrow.homMk ⟨ι.map ((karoubi.F' Λ).obj X).p, by simp [← Functor.map_comp]⟩ (𝟙 _)
  retract := by
    ext
    · simp [← Functor.map_comp]
    · simp

Depends on / 依赖: Arrow.homMk, Functor, Functor.map_comp, karoubi, karoubi.F, map_comp
-/
def karoubi.retractArrow (X : A) :
    RetractArrow ((karoubi.π' Λ).app X) ((toKaroubi _).map (Λ.π.app X)) where
  i := Arrow.homMk ⟨ι.map ((karoubi.F' Λ).obj X).p, by simp [← Functor.map_comp]⟩ (𝟙 _)
  r := Arrow.homMk ⟨ι.map ((karoubi.F' Λ).obj X).p, by simp [← Functor.map_comp]⟩ (𝟙 _)
  retract := by
    ext
    · simp [← Functor.map_comp]
    · simp

instance (X : A) : Epi ((karoubi.π' Λ).app X) :=
  of_retract (P := epimorphisms _) (karoubi.retractArrow Λ X)
    (epimorphisms.infer_property _)

/--
Definition of `karoubi.π` / `karoubi.π` 的定义

English:
definition karoubi.π
  signature: : karoubi.F Λ ⋙ (functorExtension₂ C A).obj ι ⟶ 𝟭 (Karoubi A)
  body: whiskeringLeftObjToKaroubiFullyFaithful.preimage (karoubi.π' Λ)

中文:
定义 karoubi.π
  签名: : karoubi.F Λ ⋙ (functorExtension₂ C A).obj ι ⟶ 𝟭 (Karoubi A)
  定义体: whiskeringLeftObjToKaroubiFullyFaithful.preimage (karoubi.π' Λ)

Depends on / 依赖: karoubi, preimage, whiskeringLeftObjToKaroubiFullyFaithful, whiskeringLeftObjToKaroubiFullyFaithful.preimage
-/
def karoubi.π : karoubi.F Λ ⋙ (functorExtension₂ C A).obj ι ⟶ 𝟭 (Karoubi A) :=
  whiskeringLeftObjToKaroubiFullyFaithful.preimage (karoubi.π' Λ)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `karoubi.π_app_toKaroubi_obj` / 引理 `karoubi.π_app_toKaroubi_obj`

English:
lemma karoubi.π_app_toKaroubi_obj
  given: (X : A)
  proof: by
  simp [π, whiskeringLeftObjToKaroubiFullyFaithful]

中文:
引理 karoubi.π_app_toKaroubi_obj
  条件: (X : A)
  证明: by
  simp [π, whiskeringLeftObjToKaroubiFullyFaithful]

Depends on / 依赖: whiskeringLeftObjToKaroubiFullyFaithful
-/
lemma karoubi.π_app_toKaroubi_obj (X : A) :
    (karoubi.π Λ).app ((toKaroubi _).obj X) = (karoubi.π' Λ).app X := by
  simp [π, whiskeringLeftObjToKaroubiFullyFaithful]

instance (X : A) : Epi ((karoubi.π Λ).app ((toKaroubi _).obj X)) := by
  rw [karoubi.π_app_toKaroubi_obj]
  infer_instance

instance (X : Karoubi A) : Epi ((karoubi.π Λ).app X) :=
  of_retract (P := epimorphisms _) (NatTrans.retractArrowApp (karoubi.π Λ) X.retract)
    (epimorphisms.infer_property _)

/-- Given `ι : C ⥤ A`, this is the extension of `Λ : LeftResolution ι` to
`LeftResolution ((functorExtension₂ C A).obj ι)`, where
`(functorExtension₂ C A).obj ι : Karoubi C ⥤ Karoubi A` is the extension of `ι`. -/
@[simps]
/--
Definition of `karoubi` / `karoubi` 的定义

English:
definition karoubi
  signature: : LeftResolution ((functorExtension₂ C A).obj ι) where
  body: karoubi.F Λ
  π := karoubi.π Λ

中文:
定义 karoubi
  签名: : LeftResolution ((functorExtension₂ C A).obj ι) where
  定义体: karoubi.F Λ
  π := karoubi.π Λ

Depends on / 依赖: karoubi, karoubi.F
-/
noncomputable def karoubi : LeftResolution ((functorExtension₂ C A).obj ι) where
  F := karoubi.F Λ
  π := karoubi.π Λ

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Λ.karoubi.F.PreservesZeroMorphisms

中文:
实例 :
  签名: Λ.karoubi.F.PreservesZeroMorphisms
-/
instance : Λ.karoubi.F.PreservesZeroMorphisms where

section

variable [IsIdempotentComplete A] [IsIdempotentComplete C]

/--
Definition of `reduced` / `reduced` 的定义

English:
definition reduced
  signature: : LeftResolution ι
  body: Λ.karoubi.transport (toKaroubiEquivalence A) (toKaroubiEquivalence C)
     ((karoubiUniversal₁ C A).unitIso.app _)

中文:
定义 reduced
  签名: : LeftResolution ι
  定义体: Λ.karoubi.transport (toKaroubiEquivalence A) (toKaroubiEquivalence C)
     ((karoubiUniversal₁ C A).unitIso.app _)

Depends on / 依赖: karoubi, karoubi.transport, toKaroubiEquivalence, transport, unitIso, unitIso.app
-/
noncomputable def reduced : LeftResolution ι :=
  Λ.karoubi.transport (toKaroubiEquivalence A) (toKaroubiEquivalence C)
     ((karoubiUniversal₁ C A).unitIso.app _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Λ.reduced.F.PreservesZeroMorphisms
  body: by
  dsimp [reduced, transport]
  infer_instance

中文:
实例 :
  签名: Λ.reduced.F.PreservesZeroMorphisms
  定义体: by
  dsimp [reduced, transport]
  infer_instance

Depends on / 依赖: infer_instance, reduced, transport
-/
instance : Λ.reduced.F.PreservesZeroMorphisms := by
  dsimp [reduced, transport]
  infer_instance

end

end LeftResolution

end CategoryTheory.Abelian
