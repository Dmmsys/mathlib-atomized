/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne, Paul Lezeau
-/
module

public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.FiberedCategory.Fibered

/-!

# Fibers of functors

In this file we introduce a typeclass `HasFibers` for a functor `p : 𝒳 ⥤ 𝒮`, consisting of:
- A collection of categories `Fib S` for every `S` in `𝒮` (the fiber categories)
- Functors `ι : Fib S ⥤ 𝒳` such that `ι ⋙ p = const (Fib S) S`
- The induced functor `Fib S ⥤ Fiber p S` is an equivalence.

We also provide a canonical `HasFibers` instance, which uses the standard fibers `Fiber p S`
(see `Mathlib/CategoryTheory/FiberedCategory/Fiber.lean`). This makes it so that any result proven
about `HasFibers` can be used for the standard fibers as well.

The reason for introducing this typeclass is that in practice, when working with (pre)fibered
categories one often already has a collection of categories `Fib S` for every `S` that are
equivalent to the fibers `Fiber p S`. One would then like to use these categories `Fib S` directly,
instead of working through this equivalence of categories. By developing an API for the `HasFibers`
typeclass, this will be possible.

Here is an example of when this typeclass is useful. Suppose we have a presheaf of types
`F : 𝒮ᵒᵖ ⥤ Type _`. The associated fibered category then has objects `(S, a)` where `S : 𝒮` and `a`
is an element of `F(S)`. The fiber category `Fiber p S` is then equivalent to the discrete category
`Fib S` with objects `a` in `F(S)`. In this case, the `HasFibers` instance is given by the
categories `F(S)` and the functor `ι` sends `a : F(S)` to `(S, a)` in the fibered category.

## Main API
The following API is developed so that the fibers from a `HasFibers` instance can be used
analogously to the standard fibers.

- `Fib.homMk φ` is a lift of a morphism `φ : (ι S).obj a ⟶ (ι S).obj b` in `𝒳`, which lies over
  `𝟙 S`, to a morphism in the fiber over `S`.
- `Fib.mk` gives an object in the fiber over `S` which is isomorphic to a given `a : 𝒳` that
  satisfies `p(a) = S`. The isomorphism is given by `Fib.mkIsoSelf`.
- `HasFibers.mkPullback` is a version of `IsPreFibered.mkPullback` which ensures that the object
  lies in a given fiber. The corresponding Cartesian morphism is given by `HasFibers.pullbackMap`.
- `HasFibers.inducedMap` is a version of `IsCartesian.inducedMap` which gives the corresponding
  morphism in the fiber category.
- `fiber_factorization` is the statement that any morphism in `𝒳` can be factored as a morphism in
  some fiber followed by a pullback.

-/

@[expose] public section

universe v₃ u₃ v₂ u₂ v₁ u₁

open CategoryTheory Functor Category IsCartesian IsHomLift Fiber

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₂} 𝒳]

set_option linter.checkUnivs false in
/--
Definition of `HasFibers` / `HasFibers` 的定义

English:
class HasFibers
  parameters: (p : 𝒳 ⥤ 𝒮)
  axioms and operations (5):
    - Fib((S : 𝒮)) : Type u₃
    - category((S : 𝒮)) : Category.{v₃} (Fib S)  [default: by infer_instance]
    - ι((S : 𝒮)) : Fib S ⥤ 𝒳
    - comp_const((S : 𝒮)) : ι S ⋙ p = (const (Fib S)).obj S
    - equiv((S : 𝒮)) : Functor.IsEquivalence (inducedFunctor (comp_const S))  [default: by infer_instance]

中文:
类 HasFibers
  参数: (p : 𝒳 ⥤ 𝒮)
  公理与运算 (5 个):
    - Fib((S : 𝒮)) : 类型u₃
    - category((S : 𝒮)) : Category.{v₃} (Fib S)  [默认: by infer_instance]
    - ι((S : 𝒮)) : Fib S ⥤ 𝒳
    - comp_const((S : 𝒮)) : ι S ⋙ p = (const (Fib S)).obj S
    - equiv((S : 𝒮)) : Functor.IsEquivalence (inducedFunctor (comp_const S))  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
class HasFibers (p : 𝒳 ⥤ 𝒮) where
  /-- The type of objects of the category `Fib S` for each `S`. -/
  Fib (S : 𝒮) : Type u₃
  /-- `Fib S` is a category. -/
  category (S : 𝒮) : Category.{v₃} (Fib S) := by infer_instance
  /-- The functor `ι : Fib S ⥤ 𝒳`. -/
  ι (S : 𝒮) : Fib S ⥤ 𝒳
  /-- The composition with the functor `p` is *equal* to the constant functor mapping to `S`. -/
  comp_const (S : 𝒮) : ι S ⋙ p = (const (Fib S)).obj S
  /-- The induced functor from `Fib S` to the fiber of `𝒳 ⥤ 𝒮` over `S` is an equivalence. -/
  equiv (S : 𝒮) : Functor.IsEquivalence (inducedFunctor (comp_const S)) := by infer_instance

namespace HasFibers

/-- The `HasFibers` on `p : 𝒳 ⥤ 𝒮` given by the fibers of `p` -/
@[instance_reducible]
/--
Definition of `canonical` / `canonical` 的定义

English:
definition canonical
  signature: (p : 𝒳 ⥤ 𝒮)
  body: Fiber p
  ι S := fiberInclusion
  comp_const S := fiberInclusion_comp_eq_const
  equiv S := by exact isEquivalence_of_iso (F := 𝟭 (Fiber p S)) (Iso.refl _)

中文:
定义 canonical
  签名: (p : 𝒳 ⥤ 𝒮)
  定义体: Fiber p
  ι S := fiberInclusion
  comp_const S := fiberInclusion_comp_eq_const
  equiv S := by exact isEquivalence_of_iso (F := 𝟭 (Fiber p S)) (Iso.refl _)
-/
def canonical (p : 𝒳 ⥤ 𝒮) : HasFibers p where
  Fib := Fiber p
  ι S := fiberInclusion
  comp_const S := fiberInclusion_comp_eq_const
  equiv S := by exact isEquivalence_of_iso (F := 𝟭 (Fiber p S)) (Iso.refl _)

section

variable (p : 𝒳 ⥤ 𝒮) [HasFibers p] (S : 𝒮)

attribute [instance_reducible, instance] category

/-- The induced functor from `Fib p S` to the standard fiber. -/
@[simps!]
/--
Definition of `inducedFunctor` / `inducedFunctor` 的定义

English:
definition inducedFunctor
  signature: : Fib p S ⥤ Fiber p S
  body: Fiber.inducedFunctor (comp_const S)

中文:
定义 inducedFunctor
  签名: : Fib p S ⥤ Fiber p S
  定义体: Fiber.inducedFunctor (comp_const S)

Depends on / 依赖: Fiber.inducedFunctor, comp_const, inducedFunctor
-/
def inducedFunctor : Fib p S ⥤ Fiber p S :=
  Fiber.inducedFunctor (comp_const S)

/--
Definition of `inducedFunctor.natIso` / `inducedFunctor.natIso` 的定义

English:
definition inducedFunctor.natIso
  signature: : ι S ≅ (inducedFunctor p S) ⋙ fiberInclusion
  body: Fiber.inducedFunctorCompIsoSelf (comp_const S)

中文:
定义 inducedFunctor.natIso
  签名: : ι S ≅ (inducedFunctor p S) ⋙ fiberInclusion
  定义体: Fiber.inducedFunctorCompIsoSelf (comp_const S)

Depends on / 依赖: Fiber.inducedFunctorCompIsoSelf, comp_const, inducedFunctorCompIsoSelf
-/
def inducedFunctor.natIso : ι S ≅ (inducedFunctor p S) ⋙ fiberInclusion :=
  Fiber.inducedFunctorCompIsoSelf (comp_const S)

/--
lemma `inducedFunctor_comp` / 引理 `inducedFunctor_comp`

English:
lemma inducedFunctor_comp
  statement: ι S = (inducedFunctor p S) ⋙ fiberInclusion
  proof: Fiber.inducedFunctor_comp (comp_const S)

中文:
引理 inducedFunctor_comp
  结论: ι S = (inducedFunctor p S) ⋙ fiberInclusion
  证明: Fiber.inducedFunctor_comp (comp_const S)

Depends on / 依赖: Fiber.inducedFunctor_comp, comp_const, inducedFunctor_comp
-/
lemma inducedFunctor_comp : ι S = (inducedFunctor p S) ⋙ fiberInclusion :=
  Fiber.inducedFunctor_comp (comp_const S)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Functor.IsEquivalence (inducedFunctor p S)
  body: equiv S

中文:
实例 :
  签名: Functor.IsEquivalence (inducedFunctor p S)
  定义体: equiv S
-/
instance : Functor.IsEquivalence (inducedFunctor p S) := equiv S

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Functor.Faithful (ι (p := p) S)
  body: Functor.Faithful.of_iso (inducedFunctor.natIso p S).symm

中文:
实例 :
  签名: Functor.Faithful (ι (p := p) S)
  定义体: Functor.Faithful.of_iso (inducedFunctor.natIso p S).symm
-/
instance : Functor.Faithful (ι (p := p) S) :=
  Functor.Faithful.of_iso (inducedFunctor.natIso p S).symm

end

section

variable {p : 𝒳 ⥤ 𝒮} [HasFibers p]

@[simp]
/--
lemma `proj_eq` / 引理 `proj_eq`

English:
lemma proj_eq
  given: {S : 𝒮} (a : Fib p S)
  statement: p.obj ((ι S).obj a) = S
  proof: by
  simp only [← comp_obj, comp_const, const_obj_obj]

中文:
引理 proj_eq
  条件: {S : 𝒮} (a : Fib p S)
  结论: p.obj ((ι S).obj a) = S
  证明: by
  simp only [← comp_obj, comp_const, const_obj_obj]

Depends on / 依赖: comp_const, comp_obj, const_obj_obj
-/
lemma proj_eq {S : 𝒮} (a : Fib p S) : p.obj ((ι S).obj a) = S := by
  simp only [← comp_obj, comp_const, const_obj_obj]

/--
Definition of `projMap` / `projMap` 的定义

English:
definition projMap
  signature: {R S : 𝒮} {a : Fib p R} {b : Fib p S}
  body: eqToHom (proj_eq a).symm ≫ (p.map φ) ≫ eqToHom (proj_eq b)

中文:
定义 projMap
  签名: {R S : 𝒮} {a : Fib p R} {b : Fib p S}
  定义体: eqToHom (proj_eq a).symm ≫ (p.map φ) ≫ eqToHom (proj_eq b)

Depends on / 依赖: eqToHom, p.map, proj_eq
-/
def projMap {R S : 𝒮} {a : Fib p R} {b : Fib p S}
    (φ : (ι R).obj a ⟶ (ι S).obj b) : R ⟶ S :=
  eqToHom (proj_eq a).symm ≫ (p.map φ) ≫ eqToHom (proj_eq b)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Instance `homLift` / 实例 `homLift`

English:
instance homLift
  signature: {S : 𝒮} {a b : Fib p S} (φ : a ⟶ b)
  body: by
  apply of_fac p _ _ (proj_eq a) (proj_eq b)
  rw [← Functor.comp_map]; rw [Functor.congr_hom (comp_const S)]
  simp

中文:
实例 homLift
  签名: {S : 𝒮} {a b : Fib p S} (φ : a ⟶ b)
  定义体: by
  apply of_fac p _ _ (proj_eq a) (proj_eq b)
  rw [← Functor.comp_map]; rw [Functor.congr_hom (comp_const S)]
  simp

Depends on / 依赖: Functor, Functor.comp_map, Functor.congr_hom, comp_const, comp_map, congr_hom, of_fac, proj_eq
-/
instance homLift {S : 𝒮} {a b : Fib p S} (φ : a ⟶ b) : IsHomLift p (𝟙 S) ((ι S).map φ) := by
  apply of_fac p _ _ (proj_eq a) (proj_eq b)
  rw [← Functor.comp_map]; rw [Functor.congr_hom (comp_const S)]
  simp

/--
Definition of `Fib.homMk` / `Fib.homMk` 的定义

English:
definition Fib.homMk
  signature: {S : 𝒮} {a b : Fib p S} (φ : (ι S).obj a ⟶ (ι S).obj b)
  body: (inducedFunctor _ S).preimage (Fiber.homMk p S φ)

中文:
定义 Fib.homMk
  签名: {S : 𝒮} {a b : Fib p S} (φ : (ι S).obj a ⟶ (ι S).obj b)
  定义体: (inducedFunctor _ S).preimage (Fiber.homMk p S φ)

Depends on / 依赖: Fiber.homMk, inducedFunctor, preimage
-/
noncomputable def Fib.homMk {S : 𝒮} {a b : Fib p S} (φ : (ι S).obj a ⟶ (ι S).obj b)
    [IsHomLift p (𝟙 S) φ] : a ⟶ b :=
  (inducedFunctor _ S).preimage (Fiber.homMk p S φ)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `Fib.map_homMk` / 引理 `Fib.map_homMk`

English:
lemma Fib.map_homMk
  statement: {S : 𝒮} {a b : Fib p S} (φ : (ι S).obj a ⟶ (ι S).obj b)
  proof: by
  simp [Fib.homMk, congr_hom (inducedFunctor_comp p S)]

@[ext]

中文:
引理 Fib.map_homMk
  结论: {S : 𝒮} {a b : Fib p S} (φ : (ι S).obj a ⟶ (ι S).obj b)
  证明: by
  simp [Fib.homMk, congr_hom (inducedFunctor_comp p S)]

@[ext]

Depends on / 依赖: Fib.homMk, congr_hom, inducedFunctor_comp
-/
lemma Fib.map_homMk {S : 𝒮} {a b : Fib p S} (φ : (ι S).obj a ⟶ (ι S).obj b)
    [IsHomLift p (𝟙 S) φ] : (ι S).map (homMk φ) = φ := by
  simp [Fib.homMk, congr_hom (inducedFunctor_comp p S)]

@[ext]
/--
lemma `Fib.hom_ext` / 引理 `Fib.hom_ext`

English:
lemma Fib.hom_ext
  statement: {S : 𝒮} {a b : Fib p S} {f g : a ⟶ b}
  proof: (ι S).map_injective h

中文:
引理 Fib.hom_ext
  结论: {S : 𝒮} {a b : Fib p S} {f g : a ⟶ b}
  证明: (ι S).map_injective h

Depends on / 依赖: map_injective
-/
lemma Fib.hom_ext {S : 𝒮} {a b : Fib p S} {f g : a ⟶ b}
    (h : (ι S).map f = (ι S).map g) : f = g :=
  (ι S).map_injective h

/-- The lift of an isomorphism `Φ : (ι S).obj a ≅ (ι S).obj b` lying over `𝟙 S` to an isomorphism
in `Fib S`. -/
@[simps]
/--
Definition of `Fib.isoMk` / `Fib.isoMk` 的定义

English:
definition Fib.isoMk
  signature: {S : 𝒮} {a b : Fib p S}
  body: Fib.homMk Φ.hom
  inv := Fib.homMk Φ.inv

中文:
定义 Fib.isoMk
  签名: {S : 𝒮} {a b : Fib p S}
  定义体: Fib.homMk Φ.hom
  inv := Fib.homMk Φ.inv

Depends on / 依赖: Fib.homMk
-/
noncomputable def Fib.isoMk {S : 𝒮} {a b : Fib p S}
    (Φ : (ι S).obj a ≅ (ι S).obj b) (hΦ : IsHomLift p (𝟙 S) Φ.hom) : a ≅ b where
  hom := Fib.homMk Φ.hom
  inv := Fib.homMk Φ.inv

/--
Definition of `Fib.mk` / `Fib.mk` 的定义

English:
definition Fib.mk
  signature: {S : 𝒮} {a : 𝒳} (ha : p.obj a = S)
  body: Functor.objPreimage (inducedFunctor p S) (Fiber.mk ha)

中文:
定义 Fib.mk
  签名: {S : 𝒮} {a : 𝒳} (ha : p.obj a = S)
  定义体: Functor.objPreimage (inducedFunctor p S) (Fiber.mk ha)

Depends on / 依赖: Fiber.mk, Functor, Functor.objPreimage, inducedFunctor, objPreimage
-/
noncomputable def Fib.mk {S : 𝒮} {a : 𝒳} (ha : p.obj a = S) : Fib p S :=
  Functor.objPreimage (inducedFunctor p S) (Fiber.mk ha)

/--
Definition of `Fib.mkIsoSelf` / `Fib.mkIsoSelf` 的定义

English:
definition Fib.mkIsoSelf
  signature: {S : 𝒮} {a : 𝒳} (ha : p.obj a = S)
  body: fiberInclusion.mapIso (Functor.objObjPreimageIso (inducedFunctor p S) (Fiber.mk ha))

中文:
定义 Fib.mkIsoSelf
  签名: {S : 𝒮} {a : 𝒳} (ha : p.obj a = S)
  定义体: fiberInclusion.mapIso (Functor.objObjPreimageIso (inducedFunctor p S) (Fiber.mk ha))

Depends on / 依赖: Fiber.mk, Functor, Functor.objObjPreimageIso, fiberInclusion, fiberInclusion.mapIso, inducedFunctor, mapIso, objObjPreimageIso
-/
noncomputable def Fib.mkIsoSelf {S : 𝒮} {a : 𝒳} (ha : p.obj a = S) :
    (ι S).obj (Fib.mk ha) ≅ a :=
  fiberInclusion.mapIso (Functor.objObjPreimageIso (inducedFunctor p S) (Fiber.mk ha))

/--
Instance `Fib.mkIsoSelfIsHomLift` / 实例 `Fib.mkIsoSelfIsHomLift`

English:
instance Fib.mkIsoSelfIsHomLift
  signature: {S : 𝒮} {a : 𝒳} (ha : p.obj a = S)
  body: (Functor.objObjPreimageIso (inducedFunctor p S) (Fiber.mk ha)).hom.2

中文:
实例 Fib.mkIsoSelfIsHomLift
  签名: {S : 𝒮} {a : 𝒳} (ha : p.obj a = S)
  定义体: (Functor.objObjPreimageIso (inducedFunctor p S) (Fiber.mk ha)).hom.2

Depends on / 依赖: Fiber.mk, Functor, Functor.objObjPreimageIso, inducedFunctor, objObjPreimageIso
-/
instance Fib.mkIsoSelfIsHomLift {S : 𝒮} {a : 𝒳} (ha : p.obj a = S) :
    IsHomLift p (𝟙 S) (Fib.mkIsoSelf ha).hom :=
  (Functor.objObjPreimageIso (inducedFunctor p S) (Fiber.mk ha)).hom.2

section

variable [IsPreFibered p] {R S : 𝒮} {a : 𝒳} (f : R ⟶ S) (ha : p.obj a = S)

/--
Definition of `mkPullback` / `mkPullback` 的定义

English:
definition mkPullback
  signature: : Fib p R
  body: Fib.mk (domain_eq p f (IsPreFibered.pullbackMap ha f))

中文:
定义 mkPullback
  签名: : Fib p R
  定义体: Fib.mk (domain_eq p f (IsPreFibered.pullbackMap ha f))

Depends on / 依赖: Fib.mk, IsPreFibered, IsPreFibered.pullbackMap, domain_eq, pullbackMap
-/
noncomputable def mkPullback : Fib p R :=
  Fib.mk (domain_eq p f (IsPreFibered.pullbackMap ha f))

/--
Definition of `pullbackMap` / `pullbackMap` 的定义

English:
definition pullbackMap
  signature: : (ι R).obj (mkPullback f ha) ⟶ a
  body: (Fib.mkIsoSelf (domain_eq p f (IsPreFibered.pullbackMap ha f))).hom ≫
    (IsPreFibered.pullbackMap ha f)

中文:
定义 pullbackMap
  签名: : (ι R).obj (mkPullback f ha) ⟶ a
  定义体: (Fib.mkIsoSelf (domain_eq p f (IsPreFibered.pullbackMap ha f))).hom ≫
    (IsPreFibered.pullbackMap ha f)

Depends on / 依赖: Fib.mkIsoSelf, IsPreFibered, IsPreFibered.pullbackMap, domain_eq, mkIsoSelf, pullbackMap
-/
noncomputable def pullbackMap : (ι R).obj (mkPullback f ha) ⟶ a :=
  (Fib.mkIsoSelf (domain_eq p f (IsPreFibered.pullbackMap ha f))).hom ≫
    (IsPreFibered.pullbackMap ha f)

set_option backward.isDefEq.respectTransparency false in
/--
Instance `pullbackMap.isCartesian` / 实例 `pullbackMap.isCartesian`

English:
instance pullbackMap.isCartesian
  signature: : IsCartesian p f (pullbackMap f ha)
  body: by
  conv in f => rw [← id_comp f]
  simp only [id_comp, pullbackMap]
  infer_instance

中文:
实例 pullbackMap.isCartesian
  签名: : IsCartesian p f (pullbackMap f ha)
  定义体: by
  conv in f => rw [← id_comp f]
  simp only [id_comp, pullbackMap]
  infer_instance

Depends on / 依赖: id_comp, infer_instance, pullbackMap
-/
instance pullbackMap.isCartesian : IsCartesian p f (pullbackMap f ha) := by
  conv in f => rw [← id_comp f]
  simp only [id_comp, pullbackMap]
  infer_instance

end

section

variable {R S : 𝒮} {a : 𝒳} {b b' : Fib p R} (f : R ⟶ S) (ψ : (ι R).obj b' ⟶ a)
    [IsCartesian p f ψ] (φ : (ι R).obj b ⟶ a) [IsHomLift p f φ]

/--
Definition of `inducedMap` / `inducedMap` 的定义

English:
definition inducedMap
  signature: : b ⟶ b'
  body: Fib.homMk (IsCartesian.map p f ψ φ)

@[reassoc]

中文:
定义 inducedMap
  签名: : b ⟶ b'
  定义体: Fib.homMk (IsCartesian.map p f ψ φ)

@[reassoc]

Depends on / 依赖: Fib.homMk, IsCartesian, IsCartesian.map
-/
noncomputable def inducedMap : b ⟶ b' :=
  Fib.homMk (IsCartesian.map p f ψ φ)

@[reassoc]
/--
lemma `inducedMap_comp` / 引理 `inducedMap_comp`

English:
lemma inducedMap_comp
  statement: (ι R).map (inducedMap f ψ φ) ≫ ψ = φ
  proof: by
  simp only [inducedMap, Fib.map_homMk, IsCartesian.fac]

中文:
引理 inducedMap_comp
  结论: (ι R).map (inducedMap f ψ φ) ≫ ψ = φ
  证明: by
  simp only [inducedMap, Fib.map_homMk, IsCartesian.fac]

Depends on / 依赖: Fib.map_homMk, IsCartesian, IsCartesian.fac, inducedMap, map_homMk
-/
lemma inducedMap_comp : (ι R).map (inducedMap f ψ φ) ≫ ψ = φ := by
  simp only [inducedMap, Fib.map_homMk, IsCartesian.fac]

end

section

variable [IsFibered p] {R S : 𝒮} {a : 𝒳} {b : Fib p R}

/--
lemma `fiber_factorization` / 引理 `fiber_factorization`

English:
lemma fiber_factorization
  statement: (ha : p.obj a = S) {b : Fib p R} (f : R ⟶ S) (φ : (ι R).obj b ⟶ a)
  proof: let ψ := pullbackMap f ha
  ⟨mkPullback f ha, inducedMap f ψ φ, ψ, inferInstance, inducedMap_comp f ψ φ⟩

中文:
引理 fiber_factorization
  结论: (ha : p.obj a = S) {b : Fib p R} (f : R ⟶ S) (φ : (ι R).obj b ⟶ a)
  证明: let ψ := pullbackMap f ha
  ⟨mkPullback f ha, inducedMap f ψ φ, ψ, inferInstance, inducedMap_comp f ψ φ⟩

Depends on / 依赖: inducedMap, inducedMap_comp, mkPullback, pullbackMap
-/
lemma fiber_factorization (ha : p.obj a = S) {b : Fib p R} (f : R ⟶ S) (φ : (ι R).obj b ⟶ a)
    [IsHomLift p f φ] : exists (b' : Fib p R) (τ : b ⟶ b') (ψ : (ι R).obj b' ⟶ a),
      IsStronglyCartesian p f ψ ∧ (((ι R).map τ) ≫ ψ = φ) :=
  let ψ := pullbackMap f ha
  ⟨mkPullback f ha, inducedMap f ψ φ, ψ, inferInstance, inducedMap_comp f ψ φ⟩

end

end

end HasFibers
