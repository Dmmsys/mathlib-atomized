/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.CofilteredSystem
public import Mathlib.CategoryTheory.Galois.Decomposition
public import Mathlib.CategoryTheory.Limits.IndYoneda
public import Mathlib.CategoryTheory.Limits.Preserves.Ulift

/-!
# Pro-Representability of fiber functors

We show that any fiber functor is pro-representable, i.e. there exists a pro-object
`X : I ⥤ C` such that `F` is naturally isomorphic to the colimit of `X ⋙ coyoneda`.

From this we deduce the canonical isomorphism of `Aut F` with the limit over the automorphism
groups of all Galois objects.

## Main definitions

- `PointedGaloisObject`: the category of pointed Galois objects
- `PointedGaloisObject.cocone`: a cocone on `(PointedGaloisObject.incl F).op ≫ coyoneda` with
  point `F ⋙ FintypeCat.incl`.
- `autGaloisSystem`: the system of automorphism groups indexed by the pointed Galois objects.

## Main results

- `PointedGaloisObject.isColimit`: the cocone `PointedGaloisObject.cocone` is a colimit cocone.
- `autMulEquivAutGalois`: `Aut F` is canonically isomorphic to the limit over the automorphism
  groups of all Galois objects.
- `FiberFunctor.isPretransitive_of_isConnected`: The `Aut F` action on the fiber of a connected
  object is transitive.

## Implementation details

The pro-representability statement and the isomorphism of `Aut F` with the limit over the
automorphism groups of all Galois objects naturally forces `F` to take values in `FintypeCat.{u₂}`
where `u₂` is the `Hom`-universe of `C`. Since this is used to show that `Aut F` acts
transitively on `F.obj X` for connected `X`, we a priori only obtain this result for
the mentioned specialized universe setup. To obtain the result for `F` taking values in an arbitrary
`FintypeCat.{w}`, we postcompose with an equivalence `FintypeCat.{w} ≌ FintypeCat.{u₂}` and apply
the specialized result.

In the following the section `Specialized` is reserved for the setup where `F` takes values in
`FintypeCat.{u₂}` and the section `General` contains results holding for `F` taking values in
an arbitrary `FintypeCat.{w}`.

## References

* [lenstraGSchemes]: H. W. Lenstra. Galois theory for schemes.

-/

@[expose] public section

universe u₁ u₂ w

namespace CategoryTheory

namespace PreGaloisCategory

open Limits CategoryTheory.Functor

variable {C : Type u₁} [Category.{u₂} C] [GaloisCategory C]

/--
Definition of `PointedGaloisObject` / `PointedGaloisObject` 的定义

English:
structure PointedGaloisObject
  parameters: (F : C ⥤ FintypeCat.{w})
  axioms and operations (3):
    - obj : C
    - pt : F.obj obj
    - isGalois : IsGalois obj  [default: by infer_instance]

中文:
结构 PointedGaloisObject
  参数: (F : C ⥤ FintypeCat.{w})
  公理与运算 (3 个):
    - obj : C
    - pt : F.obj obj
    - isGalois : 是Galois obj  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
structure PointedGaloisObject (F : C ⥤ FintypeCat.{w}) : Type (max u₁ u₂ w) where
  /-- The underlying object of `C`. -/
  obj : C
  /-- An element of the fiber of `obj`. -/
  pt : F.obj obj
  /-- `obj` is Galois. -/
  isGalois : IsGalois obj := by infer_instance

namespace PointedGaloisObject

section General

variable (F : C ⥤ FintypeCat.{w})

attribute [instance] isGalois

instance (X : PointedGaloisObject F) : CoeDep (PointedGaloisObject F) X C where
  coe := X.obj

variable {F} in
/-- The type of homomorphisms between two pointed Galois objects. This is a homomorphism
of the underlying objects of `C` that maps the distinguished points to each other. -/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (A B : PointedGaloisObject F)
  axioms and operations (2):
    - val : A.obj ⟶ B.obj
    - comp : F.map val A.pt = B.pt  [default: by simp]

中文:
结构 态射
  参数: (A B : PointedGaloisObject F)
  公理与运算 (2 个):
    - val : A.obj ⟶ B.obj
    - comp : F.map val A.pt = B.pt  [默认: by simp]
-/
structure Hom (A B : PointedGaloisObject F) where
  /-- The underlying homomorphism of `C`. -/
  val : A.obj ⟶ B.obj
  /-- The distinguished point of `A` is mapped to the distinguished point of `B`. -/
  comp : F.map val A.pt = B.pt := by simp

attribute [simp] Hom.comp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category.{u₂} (PointedGaloisObject F)
  body: Hom A B
  id A := { val := 𝟙 (A : C) }
  comp {A B C} f g := { val := f.val ≫ g.val }

中文:
实例 :
  签名: 范畴.{u₂} (PointedGaloisObject F)
  定义体: Hom A B
  id A := { val := 𝟙 (A : C) }
  comp {A B C} f g := { val := f.val ≫ g.val }
-/
instance : Category.{u₂} (PointedGaloisObject F) where
  Hom A B := Hom A B
  id A := { val := 𝟙 (A : C) }
  comp {A B C} f g := { val := f.val ≫ g.val }

instance {A B : PointedGaloisObject F} : Coe (Hom A B) (A.obj ⟶ B.obj) where
  coe f := f.val

variable {F}

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {A B : PointedGaloisObject F} {f g : A ⟶ B} (h : f.val = g.val)
  statement: f = g
  proof: Hom.ext h

@[simp]

中文:
引理 hom_ext
  条件: {A B : PointedGaloisObject F} {f g : A ⟶ B} (h : f.val = g.val)
  结论: f = g
  证明: Hom.ext h

@[simp]

Depends on / 依赖: Hom.ext
-/
lemma hom_ext {A B : PointedGaloisObject F} {f g : A ⟶ B} (h : f.val = g.val) : f = g :=
  Hom.ext h

@[simp]
/--
lemma `id_val` / 引理 `id_val`

English:
lemma id_val
  given: (A : PointedGaloisObject F)
  statement: 𝟙 A = 𝟙 A.obj
  proof: rfl

@[simp, reassoc]

中文:
引理 id_val
  条件: (A : PointedGaloisObject F)
  结论: 𝟙 A = 𝟙 A.obj
  证明: rfl

@[simp, reassoc]
-/
lemma id_val (A : PointedGaloisObject F) : 𝟙 A = 𝟙 A.obj :=
  rfl

@[simp, reassoc]
/--
lemma `comp_val` / 引理 `comp_val`

English:
lemma comp_val
  given: {A B C : PointedGaloisObject F} (f : A ⟶ B) (g : B ⟶ C)
  proof: rfl

中文:
引理 comp_val
  条件: {A B C : PointedGaloisObject F} (f : A ⟶ B) (g : B ⟶ C)
  证明: rfl
-/
lemma comp_val {A B C : PointedGaloisObject F} (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).val = f.val ≫ g.val :=
  rfl

variable (F)

/--
Definition of `incl` / `incl` 的定义

English:
definition incl
  signature: : PointedGaloisObject F ⥤ C where
  body: fun A => A
  map := fun ⟨f, _⟩ => f

@[simp]

中文:
定义 incl
  签名: : PointedGaloisObject F ⥤ C where
  定义体: fun A => A
  map := fun ⟨f, _⟩ => f

@[simp]
-/
def incl : PointedGaloisObject F ⥤ C where
  obj := fun A => A
  map := fun ⟨f, _⟩ => f

@[simp]
/--
lemma `incl_obj` / 引理 `incl_obj`

English:
lemma incl_obj
  given: (A : PointedGaloisObject F)
  statement: (incl F).obj A = A
  proof: rfl

@[simp]

中文:
引理 incl_obj
  条件: (A : PointedGaloisObject F)
  结论: (incl F).obj A = A
  证明: rfl

@[simp]
-/
lemma incl_obj (A : PointedGaloisObject F) : (incl F).obj A = A :=
  rfl

@[simp]
/--
lemma `incl_map` / 引理 `incl_map`

English:
lemma incl_map
  given: {A B : PointedGaloisObject F} (f : A ⟶ B)
  statement: (incl F).map f = f.val
  proof: rfl

中文:
引理 incl_map
  条件: {A B : PointedGaloisObject F} (f : A ⟶ B)
  结论: (incl F).map f = f.val
  证明: rfl
-/
lemma incl_map {A B : PointedGaloisObject F} (f : A ⟶ B) : (incl F).map f = f.val :=
  rfl

end General

section Specialized

variable (F : C ⥤ FintypeCat.{u₂})

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `cocone` / `cocone` 的定义

English:
definition cocone
  signature: : Cocone ((incl F).op ⋙ coyoneda) where
  body: F ⋙ FintypeCat.incl
  ι := {
    app := fun ⟨A, a, _⟩ => { app X := ↾fun (f : (A : C) ⟶ X) => F.map f a }
    naturality := fun ⟨A, a, _⟩ ⟨B, b, _⟩ ⟨f, (hf : F.map f b = a)⟩ => by
      ext Y (g : (A : C) ⟶ Y)
      suffices h : F.map g (F.map f b) = F.map g a by simpa
      rw [hf]
  }

@[simp]

中文:
定义 cocone
  签名: : 余锥 ((incl F).op ⋙ coyoneda) where
  定义体: F ⋙ FintypeCat.incl
  ι := {
    app := fun ⟨A, a, _⟩ => { app X := ↾fun (f : (A : C) ⟶ X) => F.map f a }
    naturality := fun ⟨A, a, _⟩ ⟨B, b, _⟩ ⟨f, (hf : F.map f b = a)⟩ => by
      ext Y (g : (A : C) ⟶ Y)
      suffices h : F.map g (F.map f b) = F.map g a by simpa
      rw [hf]
  }

@[simp]

Depends on / 依赖: FintypeCat, FintypeCat.incl
-/
def cocone : Cocone ((incl F).op ⋙ coyoneda) where
  pt := F ⋙ FintypeCat.incl
  ι := {
    app := fun ⟨A, a, _⟩ => { app X := ↾fun (f : (A : C) ⟶ X) => F.map f a }
    naturality := fun ⟨A, a, _⟩ ⟨B, b, _⟩ ⟨f, (hf : F.map f b = a)⟩ => by
      ext Y (g : (A : C) ⟶ Y)
      suffices h : F.map g (F.map f b) = F.map g a by simpa
      rw [hf]
  }

@[simp]
/--
lemma `cocone_app` / 引理 `cocone_app`

English:
lemma cocone_app
  given: (A : PointedGaloisObject F) (B : C)
  proof: rfl

中文:
引理 cocone_app
  条件: (A : PointedGaloisObject F) (B : C)
  证明: rfl
-/
lemma cocone_app (A : PointedGaloisObject F) (B : C) :
    ((cocone F).ι.app ⟨A⟩).app B = ↾fun (f : (A : C) ⟶ B) => F.map f A.pt :=
  rfl

variable [FiberFunctor F]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsCofilteredOrEmpty (PointedGaloisObject F)
  body: fun ⟨A, a, _⟩ ⟨B, b, _⟩ => by
    obtain ⟨Z, f, z, hgal, hfz⟩ := exists_hom_from_galois_of_fiber F (A ⨯ B)
 (fiberBinaryProductEquiv F A B).symm (a, b)
    refine ⟨⟨Z, z, hgal⟩, ⟨f ≫ prod.fst, ?_⟩, ⟨f ≫ prod.snd, ?_⟩, trivial⟩
    · simp only [F.map_comp, hfz, FintypeCat.comp_apply, fiberBinaryProductEquiv_symm_fst_apply]
    · simp only [F.map_comp, hfz, FintypeCat.comp_apply, fiberBinaryProductEquiv_symm_snd_apply]
  cone_maps := fun ⟨A, a, _⟩ ⟨B, b, _⟩ ⟨f, hf⟩ ⟨g, hg⟩ => by
    obtain ⟨Z, h, z, hgal, hhz⟩ := exists_hom_from_galois_of_fiber F A a
    refine ⟨⟨Z, z, hgal⟩, ⟨h, hhz⟩, hom_ext ?_⟩
    apply evaluation_injective_of_isConnected F Z B z
    simp [hhz, hf, hg]

中文:
实例 :
  签名: 是余filteredOrEmpty (PointedGaloisObject F)
  定义体: fun ⟨A, a, _⟩ ⟨B, b, _⟩ => by
    obtain ⟨Z, f, z, hgal, hfz⟩ := exists_hom_from_galois_of_fiber F (A ⨯ B)
 (fiberBinaryProductEquiv F A B).symm (a, b)
    refine ⟨⟨Z, z, hgal⟩, ⟨f ≫ prod.fst, ?_⟩, ⟨f ≫ prod.snd, ?_⟩, trivial⟩
    · simp only [F.map_comp, hfz, FintypeCat.comp_apply, fiberBinaryProductEquiv_symm_fst_apply]
    · simp only [F.map_comp, hfz, FintypeCat.comp_apply, fiberBinaryProductEquiv_symm_snd_apply]
  cone_maps := fun ⟨A, a, _⟩ ⟨B, b, _⟩ ⟨f, hf⟩ ⟨g, hg⟩ => by
    obtain ⟨Z, h, z, hgal, hhz⟩ := exists_hom_from_galois_of_fiber F A a
    refine ⟨⟨Z, z, hgal⟩, ⟨h, hhz⟩, hom_ext ?_⟩
    apply evaluation_injective_of_isConnected F Z B z
    simp [hhz, hf, hg]

Depends on / 依赖: F.map_comp, FintypeCat, FintypeCat.comp_apply, comp_apply, cone_maps, exists_hom_from_galois_of_fiber, fiberBinaryProductEquiv, fiberBinaryProductEquiv_symm_fst_apply, fiberBinaryProductEquiv_symm_snd_apply, map_comp, prod.fst, prod.snd
-/
instance : IsCofilteredOrEmpty (PointedGaloisObject F) where
  cone_objs := fun ⟨A, a, _⟩ ⟨B, b, _⟩ => by
    obtain ⟨Z, f, z, hgal, hfz⟩ := exists_hom_from_galois_of_fiber F (A ⨯ B)
 (fiberBinaryProductEquiv F A B).symm (a, b)
    refine ⟨⟨Z, z, hgal⟩, ⟨f ≫ prod.fst, ?_⟩, ⟨f ≫ prod.snd, ?_⟩, trivial⟩
    · simp only [F.map_comp, hfz, FintypeCat.comp_apply, fiberBinaryProductEquiv_symm_fst_apply]
    · simp only [F.map_comp, hfz, FintypeCat.comp_apply, fiberBinaryProductEquiv_symm_snd_apply]
  cone_maps := fun ⟨A, a, _⟩ ⟨B, b, _⟩ ⟨f, hf⟩ ⟨g, hg⟩ => by
    obtain ⟨Z, h, z, hgal, hhz⟩ := exists_hom_from_galois_of_fiber F A a
    refine ⟨⟨Z, z, hgal⟩, ⟨h, hhz⟩, hom_ext ?_⟩
    apply evaluation_injective_of_isConnected F Z B z
    simp [hhz, hf, hg]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isColimit` / `isColimit` 的定义

English:
definition isColimit
  signature: : IsColimit (cocone F)
  body: by
  refine evaluationJointlyReflectsColimits _ (fun X => ?_)
  refine Types.FilteredColimit.isColimitOf _ _ ?_ ?_
  · intro (x : F.obj X)
    obtain ⟨Y, i, y, h1, _, _⟩ := fiber_in_connected_component F X x
    obtain ⟨Z, f, z, hgal, hfz⟩ := exists_hom_from_galois_of_fiber F Y y
    refine ⟨⟨Z, z, hgal⟩, f ≫ i, ?_⟩
    simp [← hfz, ← h1]
  · intro ⟨A, a, _⟩ ⟨B, b, _⟩ (u : (A : C) ⟶ X) (v : (B : C) ⟶ X) (h : F.map u a = F.map v b)
    obtain ⟨⟨Z, z, _⟩, ⟨f, hf⟩, ⟨g, hg⟩, _⟩ :=
      IsFilteredOrEmpty.cocone_objs (C := (PointedGaloisObject F)ᵒᵖ)
        ⟨{ obj := A, pt := a}⟩ ⟨{obj := B, pt := b}⟩
    refine ⟨⟨{ obj := Z, pt := z }⟩, ⟨f, hf⟩, ⟨g, hg⟩, ?_⟩
    apply evaluation_injective_of_isConnected F Z X z
    change F.map (f ≫ u) z = F.map (g ≫ v) z
    rw [map_comp]; rw [FintypeCat.comp_apply]; rw [hf]; rw [map_comp]; rw [FintypeCat.comp_apply]; rw [hg]; rw [h]

中文:
定义 isColimit
  签名: : 是余极限 (cocone F)
  定义体: by
  refine evaluationJointlyReflectsColimits _ (fun X => ?_)
  refine Types.FilteredColimit.isColimitOf _ _ ?_ ?_
  · intro (x : F.obj X)
    obtain ⟨Y, i, y, h1, _, _⟩ := fiber_in_connected_component F X x
    obtain ⟨Z, f, z, hgal, hfz⟩ := exists_hom_from_galois_of_fiber F Y y
    refine ⟨⟨Z, z, hgal⟩, f ≫ i, ?_⟩
    simp [← hfz, ← h1]
  · intro ⟨A, a, _⟩ ⟨B, b, _⟩ (u : (A : C) ⟶ X) (v : (B : C) ⟶ X) (h : F.map u a = F.map v b)
    obtain ⟨⟨Z, z, _⟩, ⟨f, hf⟩, ⟨g, hg⟩, _⟩ :=
      IsFilteredOrEmpty.cocone_objs (C := (PointedGaloisObject F)ᵒᵖ)
        ⟨{ obj := A, pt := a}⟩ ⟨{obj := B, pt := b}⟩
    refine ⟨⟨{ obj := Z, pt := z }⟩, ⟨f, hf⟩, ⟨g, hg⟩, ?_⟩
    apply evaluation_injective_of_isConnected F Z X z
    change F.map (f ≫ u) z = F.map (g ≫ v) z
    rw [map_comp]; rw [FintypeCat.comp_apply]; rw [hf]; rw [map_comp]; rw [FintypeCat.comp_apply]; rw [hg]; rw [h]

Depends on / 依赖: F.map, F.obj, FilteredColimit, IsFilteredOrEmpty, IsFilteredOrEmpty.cocone_objs, PointedGa, Types.FilteredColimit.isColimitOf, cocone_objs, evaluationJointlyReflectsColimits, exists_hom_from_galois_of_fiber, fiber_in_connected_component, isColimitOf
-/
noncomputable def isColimit : IsColimit (cocone F) := by
  refine evaluationJointlyReflectsColimits _ (fun X => ?_)
  refine Types.FilteredColimit.isColimitOf _ _ ?_ ?_
  · intro (x : F.obj X)
    obtain ⟨Y, i, y, h1, _, _⟩ := fiber_in_connected_component F X x
    obtain ⟨Z, f, z, hgal, hfz⟩ := exists_hom_from_galois_of_fiber F Y y
    refine ⟨⟨Z, z, hgal⟩, f ≫ i, ?_⟩
    simp [← hfz, ← h1]
  · intro ⟨A, a, _⟩ ⟨B, b, _⟩ (u : (A : C) ⟶ X) (v : (B : C) ⟶ X) (h : F.map u a = F.map v b)
    obtain ⟨⟨Z, z, _⟩, ⟨f, hf⟩, ⟨g, hg⟩, _⟩ :=
      IsFilteredOrEmpty.cocone_objs (C := (PointedGaloisObject F)ᵒᵖ)
        ⟨{ obj := A, pt := a}⟩ ⟨{obj := B, pt := b}⟩
    refine ⟨⟨{ obj := Z, pt := z }⟩, ⟨f, hf⟩, ⟨g, hg⟩, ?_⟩
    apply evaluation_injective_of_isConnected F Z X z
    change F.map (f ≫ u) z = F.map (g ≫ v) z
    rw [map_comp]; rw [FintypeCat.comp_apply]; rw [hf]; rw [map_comp]; rw [FintypeCat.comp_apply]; rw [hg]; rw [h]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasColimit ((incl F).op ⋙ coyoneda)
  body: ⟨cocone F, isColimit F⟩

中文:
实例 :
  签名: 有余极限 ((incl F).op ⋙ coyoneda)
  定义体: ⟨cocone F, isColimit F⟩

Depends on / 依赖: cocone, isColimit
-/
instance : HasColimit ((incl F).op ⋙ coyoneda) where
  exists_colimit := ⟨cocone F, isColimit F⟩

end Specialized

end PointedGaloisObject

open PointedGaloisObject

section Specialized

variable (F : C ⥤ FintypeCat.{u₂})

/-- The diagram sending each pointed Galois object to its automorphism group
as an object of `C`. -/
@[simps]
/--
Definition of `autGaloisSystem` / `autGaloisSystem` 的定义

English:
definition autGaloisSystem
  signature: : PointedGaloisObject F ⥤ GrpCat.{u₂} where
  body: fun A => GrpCat.of Aut (A : C)
  map := fun {A B} f => GrpCat.ofHom (autMapHom f)

中文:
定义 autGaloisSystem
  签名: : PointedGaloisObject F ⥤ 群范畴.{u₂} where
  定义体: fun A => GrpCat.of Aut (A : C)
  map := fun {A B} f => GrpCat.ofHom (autMapHom f)

Depends on / 依赖: GrpCat, GrpCat.of
-/
noncomputable def autGaloisSystem : PointedGaloisObject F ⥤ GrpCat.{u₂} where
obj := fun A => GrpCat.of Aut (A : C)
  map := fun {A B} f => GrpCat.ofHom (autMapHom f)

/--
Definition of `AutGalois` / `AutGalois` 的定义

English:
definition AutGalois
  signature: : Type (max u₁ u₂)
  body: (autGaloisSystem F ⋙ forget _).sections

中文:
定义 AutGalois
  签名: : 类型 (最大值 u₁ u₂)
  定义体: (autGaloisSystem F ⋙ forget _).sections

Depends on / 依赖: autGaloisSystem, forget, sections
-/
noncomputable def AutGalois : Type (max u₁ u₂) :=
  (autGaloisSystem F ⋙ forget _).sections

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Group (AutGalois F)
  body: inferInstanceAs Group (autGaloisSystem F ⋙ forget _).sections

中文:
实例 :
  签名: 群 (AutGalois F)
  定义体: inferInstanceAs Group (autGaloisSystem F ⋙ forget _).sections

Depends on / 依赖: autGaloisSystem, forget, sections
-/
noncomputable instance : Group (AutGalois F) :=
inferInstanceAs Group (autGaloisSystem F ⋙ forget _).sections

/--
Definition of `AutGalois.π` / `AutGalois.π` 的定义

English:
definition AutGalois.π
  signature: (A : PointedGaloisObject F)
  body: GrpCat.sectionsπMonoidHom (autGaloisSystem F) A

中文:
定义 AutGalois.π
  签名: (A : PointedGaloisObject F)
  定义体: GrpCat.sectionsπMonoidHom (autGaloisSystem F) A

Depends on / 依赖: GrpCat, GrpCat.sections, autGaloisSystem
-/
noncomputable def AutGalois.π (A : PointedGaloisObject F) : AutGalois F ->* Aut (A : C) :=
  GrpCat.sectionsπMonoidHom (autGaloisSystem F) A

/--
lemma `AutGalois.π_apply` / 引理 `AutGalois.π_apply`

English:
lemma AutGalois.π_apply
  given: (A : PointedGaloisObject F) (x : AutGalois F)
  proof: rfl

中文:
引理 AutGalois.π_apply
  条件: (A : PointedGaloisObject F) (x : AutGalois F)
  证明: rfl
-/
lemma AutGalois.π_apply (A : PointedGaloisObject F) (x : AutGalois F) :
    AutGalois.π F A x = x.val A :=
  rfl

/--
lemma `autGaloisSystem_map_surjective` / 引理 `autGaloisSystem_map_surjective`

English:
lemma autGaloisSystem_map_surjective
  given: ⦃A B
  statement: PointedGaloisObject F⦄ (f : A ⟶ B) :
  proof: by
  intro (φ : Aut B.obj)
  obtain ⟨ψ, hψ⟩ := autMap_surjective_of_isGalois f.val φ
  use ψ
  simp only [autGaloisSystem_map]
  exact hψ

中文:
引理 autGaloisSystem_map_surjective
  条件: ⦃A B
  结论: PointedGaloisObject F⦄ (f : A ⟶ B) :
  证明: by
  intro (φ : Aut B.obj)
  obtain ⟨ψ, hψ⟩ := autMap_surjective_of_isGalois f.val φ
  use ψ
  simp only [autGaloisSystem_map]
  exact hψ

Depends on / 依赖: B.obj, autGaloisSystem_map, autMap_surjective_of_isGalois, f.val
-/
lemma autGaloisSystem_map_surjective ⦃A B : PointedGaloisObject F⦄ (f : A ⟶ B) :
    Function.Surjective ((autGaloisSystem F).map f) := by
  intro (φ : Aut B.obj)
  obtain ⟨ψ, hψ⟩ := autMap_surjective_of_isGalois f.val φ
  use ψ
  simp only [autGaloisSystem_map]
  exact hψ

/--
lemma `AutGalois.ext` / 引理 `AutGalois.ext`

English:
lemma AutGalois.ext
  statement: {f g : AutGalois F}
  proof: by
  dsimp only [AutGalois]
  ext A
  exact h A

中文:
引理 AutGalois.ext
  结论: {f g : AutGalois F}
  证明: by
  dsimp only [AutGalois]
  ext A
  exact h A

Depends on / 依赖: AutGalois
-/
lemma AutGalois.ext {f g : AutGalois F}
    (h : forall (A : PointedGaloisObject F), AutGalois.π F A f = AutGalois.π F A g) : f = g := by
  dsimp only [AutGalois]
  ext A
  exact h A

variable [FiberFunctor F]

/--
theorem `AutGalois.π_surjective` / 定理 `AutGalois.π_surjective`

English:
theorem AutGalois.π_surjective
  given: (A : PointedGaloisObject F)
  proof: fun (σ : Aut A.obj) => by
  have (i : PointedGaloisObject F) : Finite ((autGaloisSystem F ⋙ forget _).obj i) :=
inferInstanceAs Finite (Aut (i.obj))
  exact eval_section_surjective_of_surjective
    (autGaloisSystem F ⋙ forget _) (autGaloisSystem_map_surjective F) A σ

中文:
定理 AutGalois.π_surjective
  条件: (A : PointedGaloisObject F)
  证明: fun (σ : Aut A.obj) => by
  have (i : PointedGaloisObject F) : Finite ((autGaloisSystem F ⋙ forget _).obj i) :=
inferInstanceAs Finite (Aut (i.obj))
  exact eval_section_surjective_of_surjective
    (autGaloisSystem F ⋙ forget _) (autGaloisSystem_map_surjective F) A σ

Depends on / 依赖: A.obj, Finite, PointedGaloisObject, autGaloisSystem, autGaloisSystem_map_surjective, eval_section_surjective_of_surjective, forget, i.obj
-/
theorem AutGalois.π_surjective (A : PointedGaloisObject F) :
    Function.Surjective (AutGalois.π F A) := fun (σ : Aut A.obj) => by
  have (i : PointedGaloisObject F) : Finite ((autGaloisSystem F ⋙ forget _).obj i) :=
inferInstanceAs Finite (Aut (i.obj))
  exact eval_section_surjective_of_surjective
    (autGaloisSystem F ⋙ forget _) (autGaloisSystem_map_surjective F) A σ

section EndAutGaloisIsomorphism

/-!

### Isomorphism between `Aut F` and `AutGalois F`

In this section we establish the isomorphism between the automorphism group of `F` and
the limit over the automorphism groups of all Galois objects.

We first establish the isomorphism between `End F` and `AutGalois F`, from which we deduce that
`End F` is a group, hence `End F = Aut F`. The isomorphism is built in multiple steps:

- `endEquivSectionsFibers : End F ≅ (incl F ⋙ F').sections`: the endomorphisms of
  `F` are isomorphic to the limit over `F.obj A` for all Galois objects `A`.
  This is obtained as the composition (slightly simplified):

  `End F ≅ (colimit ((incl F).op ⋙ coyoneda) ⟶ F) ≅ (incl F ⋙ F).sections`

  Where the first isomorphism is induced from the pro-representability of `F` and the second one
  from the pro-coyoneda lemma.

- `endEquivAutGalois : End F ≅ AutGalois F`: this is the composition of `endEquivSectionsFibers`
  with:

  `(incl F ⋙ F).sections ≅ (autGaloisSystem F ⋙ forget GrpCat).sections`

  which is induced from the level-wise equivalence `Aut A ≃ F.obj A` for a Galois object `A`.

-/

-- Local notation for `F` considered as a functor to types instead of finite types.
local notation "F'" => F ⋙ FintypeCat.incl

/--
Definition of `endEquivSectionsFibers` / `endEquivSectionsFibers` 的定义

English:
definition endEquivSectionsFibers
  signature: : End F ≃ (incl F ⋙ F').sections
  body: let i1 : End F ≃ End F' :=
    (FullyFaithful.whiskeringRight (FullyFaithful.ofFullyFaithful FintypeCat.incl) C).homEquiv
  let i2 : End F' ≅ (colimit ((incl F).op ⋙ coyoneda) ⟶ F') :=
    (yoneda.obj (F ⋙ FintypeCat.incl)).mapIso (colimit.isoColimitCocone ⟨cocone F, isColimit F⟩).op
  let i3 : (colimit ((incl F).op ⋙ coyoneda) ⟶ F') ≅
      limit ((incl F ⋙ F') ⋙ uliftFunctor.{u₁}) :=
    colimitCoyonedaHomIsoLimit' (incl F) F'
  let i4 : limit (incl F ⋙ F' ⋙ uliftFunctor.{u₁}) ≃
      ((incl F ⋙ F') ⋙ uliftFunctor.{u₁}).sections :=
    Types.limitEquivSections (incl F ⋙ (F ⋙ FintypeCat.incl) ⋙ uliftFunctor.{u₁, u₂})
  let i5 : ((incl F ⋙ F') ⋙ uliftFunctor.{u₁}).sections ≃ (incl F ⋙ F').sections :=
    (Types.sectionsEquiv (incl F ⋙ F')).symm
i1.trans i2.toEquiv.trans i3.toEquiv.trans i4.trans i5

中文:
定义 endEquivSectionsFibers
  签名: : End F ≃ (incl F ⋙ F').sections
  定义体: let i1 : End F ≃ End F' :=
    (FullyFaithful.whiskeringRight (FullyFaithful.ofFullyFaithful FintypeCat.incl) C).homEquiv
  let i2 : End F' ≅ (colimit ((incl F).op ⋙ coyoneda) ⟶ F') :=
    (yoneda.obj (F ⋙ FintypeCat.incl)).mapIso (colimit.isoColimitCocone ⟨cocone F, isColimit F⟩).op
  let i3 : (colimit ((incl F).op ⋙ coyoneda) ⟶ F') ≅
      limit ((incl F ⋙ F') ⋙ uliftFunctor.{u₁}) :=
    colimitCoyonedaHomIsoLimit' (incl F) F'
  let i4 : limit (incl F ⋙ F' ⋙ uliftFunctor.{u₁}) ≃
      ((incl F ⋙ F') ⋙ uliftFunctor.{u₁}).sections :=
    Types.limitEquivSections (incl F ⋙ (F ⋙ FintypeCat.incl) ⋙ uliftFunctor.{u₁, u₂})
  let i5 : ((incl F ⋙ F') ⋙ uliftFunctor.{u₁}).sections ≃ (incl F ⋙ F').sections :=
    (Types.sectionsEquiv (incl F ⋙ F')).symm
i1.trans i2.toEquiv.trans i3.toEquiv.trans i4.trans i5

Depends on / 依赖: FintypeCat, FintypeCat.incl, FullyFaithful, FullyFaithful.ofFullyFaithful, FullyFaithful.whiskeringRight, cocone, colimit, colimit.isoColimitCocone, colimitCoyonedaHomIsoLimit, coyoneda, homEquiv, isColimit, isoColimitCocone, mapIso, ofFullyFaithful, uliftFunctor, whiskeringRight, yoneda, yoneda.obj
-/
noncomputable def endEquivSectionsFibers : End F ≃ (incl F ⋙ F').sections :=
  let i1 : End F ≃ End F' :=
    (FullyFaithful.whiskeringRight (FullyFaithful.ofFullyFaithful FintypeCat.incl) C).homEquiv
  let i2 : End F' ≅ (colimit ((incl F).op ⋙ coyoneda) ⟶ F') :=
    (yoneda.obj (F ⋙ FintypeCat.incl)).mapIso (colimit.isoColimitCocone ⟨cocone F, isColimit F⟩).op
  let i3 : (colimit ((incl F).op ⋙ coyoneda) ⟶ F') ≅
      limit ((incl F ⋙ F') ⋙ uliftFunctor.{u₁}) :=
    colimitCoyonedaHomIsoLimit' (incl F) F'
  let i4 : limit (incl F ⋙ F' ⋙ uliftFunctor.{u₁}) ≃
      ((incl F ⋙ F') ⋙ uliftFunctor.{u₁}).sections :=
    Types.limitEquivSections (incl F ⋙ (F ⋙ FintypeCat.incl) ⋙ uliftFunctor.{u₁, u₂})
  let i5 : ((incl F ⋙ F') ⋙ uliftFunctor.{u₁}).sections ≃ (incl F ⋙ F').sections :=
    (Types.sectionsEquiv (incl F ⋙ F')).symm
i1.trans i2.toEquiv.trans i3.toEquiv.trans i4.trans i5

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `endEquivSectionsFibers_π` / 引理 `endEquivSectionsFibers_π`

English:
lemma endEquivSectionsFibers_π
  given: (f : End F) (A : PointedGaloisObject F)
  proof: by
  dsimp [endEquivSectionsFibers, Types.sectionsEquiv]
  erw [Types.limitEquivSections_apply, colimitCoyonedaHomIsoLimit'_π_apply]
  change (((FullyFaithful.whiskeringRight (FullyFaithful.ofFullyFaithful
      FintypeCat.incl) C).homEquiv) f).app A
    (((colimit.ι _ _) ≫ (colimit.isoColimitCocone ⟨cocone F, isColimit F⟩).hom).app
      A _) = f.app A A.pt
  simp
  rfl

中文:
引理 endEquivSectionsFibers_π
  条件: (f : End F) (A : PointedGaloisObject F)
  证明: by
  dsimp [endEquivSectionsFibers, Types.sectionsEquiv]
  erw [Types.limitEquivSections_apply, colimitCoyonedaHomIsoLimit'_π_apply]
  change (((FullyFaithful.whiskeringRight (FullyFaithful.ofFullyFaithful
      FintypeCat.incl) C).homEquiv) f).app A
    (((colimit.ι _ _) ≫ (colimit.isoColimitCocone ⟨cocone F, isColimit F⟩).hom).app
      A _) = f.app A A.pt
  simp
  rfl

Depends on / 依赖: A.pt, FintypeCat, FintypeCat.incl, FullyFaithful, FullyFaithful.ofFullyFaithful, FullyFaithful.whiskeringRight, Types.limitEquivSections_apply, Types.sectionsEquiv, cocone, colimit, colimit.isoColimitCocone, colimitCoyonedaHomIsoLimit, endEquivSectionsFibers, f.app, homEquiv, isColimit, isoColimitCocone, limitEquivSections_apply, ofFullyFaithful, sectionsEquiv
-/
lemma endEquivSectionsFibers_π (f : End F) (A : PointedGaloisObject F) :
    (endEquivSectionsFibers F f).val A = f.app A A.pt := by
  dsimp [endEquivSectionsFibers, Types.sectionsEquiv]
  erw [Types.limitEquivSections_apply, colimitCoyonedaHomIsoLimit'_π_apply]
  change (((FullyFaithful.whiskeringRight (FullyFaithful.ofFullyFaithful
      FintypeCat.incl) C).homEquiv) f).app A
    (((colimit.ι _ _) ≫ (colimit.isoColimitCocone ⟨cocone F, isColimit F⟩).hom).app
      A _) = f.app A A.pt
  simp
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `autIsoFibers` / `autIsoFibers` 的定义

English:
definition autIsoFibers
  signature: :
  body: NatIso.ofComponents (fun A => ((evaluationEquivOfIsGalois F A A.pt).toIso))
    (fun f => by
      ext
      simp [evaluationEquivOfIsGalois, -Hom.comp, ← f.comp])

中文:
定义 autIsoFibers
  签名: :
  定义体: NatIso.ofComponents (fun A => ((evaluationEquivOfIsGalois F A A.pt).toIso))
    (fun f => by
      ext
      simp [evaluationEquivOfIsGalois, -Hom.comp, ← f.comp])

Depends on / 依赖: A.pt, Hom.comp, NatIso, NatIso.ofComponents, evaluationEquivOfIsGalois, f.comp, ofComponents
-/
noncomputable def autIsoFibers :
    autGaloisSystem F ⋙ forget GrpCat ≅ incl F ⋙ F' :=
  NatIso.ofComponents (fun A => ((evaluationEquivOfIsGalois F A A.pt).toIso))
    (fun f => by
      ext
      simp [evaluationEquivOfIsGalois, -Hom.comp, ← f.comp])

/--
lemma `autIsoFibers_inv_app` / 引理 `autIsoFibers_inv_app`

English:
lemma autIsoFibers_inv_app
  given: (A : PointedGaloisObject F) (b : F.obj A)
  proof: rfl

中文:
引理 autIsoFibers_inv_app
  条件: (A : PointedGaloisObject F) (b : F.obj A)
  证明: rfl
-/
lemma autIsoFibers_inv_app (A : PointedGaloisObject F) (b : F.obj A) :
    (autIsoFibers F).inv.app A b = (evaluationEquivOfIsGalois F A A.pt).symm b :=
  rfl

/--
Definition of `endEquivAutGalois` / `endEquivAutGalois` 的定义

English:
definition endEquivAutGalois
  signature: : End F ≃ AutGalois F
  body: let e1 := endEquivSectionsFibers F
  let e2 := ((Functor.sectionsFunctor _).mapIso (autIsoFibers F).symm).toEquiv
  e1.trans e2

中文:
定义 endEquivAutGalois
  签名: : End F ≃ AutGalois F
  定义体: let e1 := endEquivSectionsFibers F
  let e2 := ((Functor.sectionsFunctor _).mapIso (autIsoFibers F).symm).toEquiv
  e1.trans e2

Depends on / 依赖: Functor, Functor.sectionsFunctor, autIsoFibers, e1.trans, endEquivSectionsFibers, mapIso, sectionsFunctor, toEquiv
-/
noncomputable def endEquivAutGalois : End F ≃ AutGalois F :=
  let e1 := endEquivSectionsFibers F
  let e2 := ((Functor.sectionsFunctor _).mapIso (autIsoFibers F).symm).toEquiv
  e1.trans e2

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `endEquivAutGalois_π` / 引理 `endEquivAutGalois_π`

English:
lemma endEquivAutGalois_π
  given: (f : End F) (A : PointedGaloisObject F)
  proof: by
  dsimp [endEquivAutGalois, AutGalois.π_apply]
  change F.map ((((sectionsFunctor _).map (autIsoFibers F).inv) _).val A).hom A.pt = _
  dsimp [autIsoFibers]
  simp only [endEquivSectionsFibers_π]
  erw [evaluationEquivOfIsGalois_symm_fiber]

中文:
引理 endEquivAutGalois_π
  条件: (f : End F) (A : PointedGaloisObject F)
  证明: by
  dsimp [endEquivAutGalois, AutGalois.π_apply]
  change F.map ((((sectionsFunctor _).map (autIsoFibers F).inv) _).val A).hom A.pt = _
  dsimp [autIsoFibers]
  simp only [endEquivSectionsFibers_π]
  erw [evaluationEquivOfIsGalois_symm_fiber]

Depends on / 依赖: A.pt, AutGalois, F.map, autIsoFibers, endEquivAutGalois, evaluationEquivOfIsGalois_symm_fiber, sectionsFunctor
-/
lemma endEquivAutGalois_π (f : End F) (A : PointedGaloisObject F) :
    F.map (AutGalois.π F A (endEquivAutGalois F f)).hom A.pt = f.app A A.pt := by
  dsimp [endEquivAutGalois, AutGalois.π_apply]
  change F.map ((((sectionsFunctor _).map (autIsoFibers F).inv) _).val A).hom A.pt = _
  dsimp [autIsoFibers]
  simp only [endEquivSectionsFibers_π]
  erw [evaluationEquivOfIsGalois_symm_fiber]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `endEquivAutGalois_mul` / 定理 `endEquivAutGalois_mul`

English:
theorem endEquivAutGalois_mul
  given: (f g : End F)
  proof: by
  refine AutGalois.ext F (fun A => evaluation_aut_injective_of_isConnected F A A.pt ?_)
  simp only [map_mul, endEquivAutGalois_π, Aut.Aut_mul_def, NatTrans.comp_app, Iso.trans_hom]
  simp only [map_comp, FintypeCat.comp_apply, endEquivAutGalois_π]
  change f.app A (g.app A A.pt) =
    (f.app A ≫ F.map ((AutGalois.π F A) ((endEquivAutGalois F) g)).hom) A.pt
  rw [← f.naturality]; rw [FintypeCat.comp_apply]; rw [endEquivAutGalois_π]

中文:
定理 endEquivAutGalois_mul
  条件: (f g : End F)
  证明: by
  refine AutGalois.ext F (fun A => evaluation_aut_injective_of_isConnected F A A.pt ?_)
  simp only [map_mul, endEquivAutGalois_π, Aut.Aut_mul_def, NatTrans.comp_app, Iso.trans_hom]
  simp only [map_comp, FintypeCat.comp_apply, endEquivAutGalois_π]
  change f.app A (g.app A A.pt) =
    (f.app A ≫ F.map ((AutGalois.π F A) ((endEquivAutGalois F) g)).hom) A.pt
  rw [← f.naturality]; rw [FintypeCat.comp_apply]; rw [endEquivAutGalois_π]

Depends on / 依赖: A.pt, Aut.Aut_mul_def, AutGalois, AutGalois.ext, Aut_mul_def, F.map, FintypeCat, FintypeCat.comp_apply, Iso.trans_hom, NatTrans, NatTrans.comp_app, comp_app, comp_apply, endEquivAutGalois, evaluation_aut_injective_of_isConnected, f.app, f.naturality, g.app, map_comp, map_mul
-/
theorem endEquivAutGalois_mul (f g : End F) :
    (endEquivAutGalois F) (g ≫ f) = (endEquivAutGalois F g) * (endEquivAutGalois F f) := by
  refine AutGalois.ext F (fun A => evaluation_aut_injective_of_isConnected F A A.pt ?_)
  simp only [map_mul, endEquivAutGalois_π, Aut.Aut_mul_def, NatTrans.comp_app, Iso.trans_hom]
  simp only [map_comp, FintypeCat.comp_apply, endEquivAutGalois_π]
  change f.app A (g.app A A.pt) =
    (f.app A ≫ F.map ((AutGalois.π F A) ((endEquivAutGalois F) g)).hom) A.pt
  rw [← f.naturality]; rw [FintypeCat.comp_apply]; rw [endEquivAutGalois_π]

/--
Definition of `endMulEquivAutGalois` / `endMulEquivAutGalois` 的定义

English:
definition endMulEquivAutGalois
  signature: : End F ≃* (AutGalois F)ᵐᵒᵖ
  body: MulEquiv.mk (Equiv.trans (endEquivAutGalois F) MulOpposite.opEquiv) (by simp)

中文:
定义 endMulEquivAutGalois
  签名: : End F ≃* (AutGalois F)ᵐᵒᵖ
  定义体: MulEquiv.mk (Equiv.trans (endEquivAutGalois F) MulOpposite.opEquiv) (by simp)

Depends on / 依赖: Equiv.trans, MulEquiv, MulEquiv.mk, MulOpposite, MulOpposite.opEquiv, endEquivAutGalois, opEquiv
-/
noncomputable def endMulEquivAutGalois : End F ≃* (AutGalois F)ᵐᵒᵖ :=
  MulEquiv.mk (Equiv.trans (endEquivAutGalois F) MulOpposite.opEquiv) (by simp)

/--
lemma `endMulEquivAutGalois_pi` / 引理 `endMulEquivAutGalois_pi`

English:
lemma endMulEquivAutGalois_pi
  given: (f : End F) (A : PointedGaloisObject F)
  proof: endEquivAutGalois_π F f A

中文:
引理 endMulEquivAutGalois_pi
  条件: (f : End F) (A : PointedGaloisObject F)
  证明: endEquivAutGalois_π F f A
-/
lemma endMulEquivAutGalois_pi (f : End F) (A : PointedGaloisObject F) :
    F.map (AutGalois.π F A (endMulEquivAutGalois F f).unop).hom A.2 = f.app A A.pt :=
  endEquivAutGalois_π F f A

/--
theorem `FibreFunctor.end_isUnit` / 定理 `FibreFunctor.end_isUnit`

English:
theorem FibreFunctor.end_isUnit
  given: (f : End F)
  statement: IsUnit f
  proof: (isUnit_map_iff (endMulEquivAutGalois F) _).mp
    (Group.isUnit ((endMulEquivAutGalois F) f))

中文:
定理 FibreFunctor.end_isUnit
  条件: (f : End F)
  结论: 是单位 f
  证明: (isUnit_map_iff (endMulEquivAutGalois F) _).mp
    (Group.isUnit ((endMulEquivAutGalois F) f))

Depends on / 依赖: Group.isUnit, endMulEquivAutGalois, isUnit, isUnit_map_iff
-/
theorem FibreFunctor.end_isUnit (f : End F) : IsUnit f :=
  (isUnit_map_iff (endMulEquivAutGalois F) _).mp
    (Group.isUnit ((endMulEquivAutGalois F) f))

/--
Instance `FibreFunctor.end_isIso` / 实例 `FibreFunctor.end_isIso`

English:
instance FibreFunctor.end_isIso
  signature: (f : End F)
  body: by
  rw [← isUnit_iff_isIso]
  exact FibreFunctor.end_isUnit F f

中文:
实例 FibreFunctor.end_isIso
  签名: (f : End F)
  定义体: by
  rw [← isUnit_iff_isIso]
  exact FibreFunctor.end_isUnit F f

Depends on / 依赖: FibreFunctor, FibreFunctor.end_isUnit, end_isUnit, isUnit_iff_isIso
-/
instance FibreFunctor.end_isIso (f : End F) : IsIso f := by
  rw [← isUnit_iff_isIso]
  exact FibreFunctor.end_isUnit F f

/--
Definition of `autMulEquivAutGalois` / `autMulEquivAutGalois` 的定义

English:
definition autMulEquivAutGalois
  signature: : Aut F ≃* (AutGalois F)ᵐᵒᵖ where
  body: MonoidHom.comp (endMulEquivAutGalois F) (Aut.toEnd F)
  invFun t := asIso ((endMulEquivAutGalois F).symm t)
  left_inv t := by
    simp only [MonoidHom.coe_comp, MonoidHom.coe_coe, Function.comp_apply,
      MulEquiv.symm_apply_apply]
    exact Aut.ext rfl
  right_inv t := by
    simp only [MonoidHom.coe_comp, MonoidHom.coe_coe]
    exact (MulEquiv.eq_symm_apply (endMulEquivAutGalois F)).mp rfl
  map_mul' := by simp [map_mul]

中文:
定义 autMulEquivAutGalois
  签名: : Aut F ≃* (AutGalois F)ᵐᵒᵖ where
  定义体: MonoidHom.comp (endMulEquivAutGalois F) (Aut.toEnd F)
  invFun t := asIso ((endMulEquivAutGalois F).symm t)
  left_inv t := by
    simp only [MonoidHom.coe_comp, MonoidHom.coe_coe, Function.comp_apply,
      MulEquiv.symm_apply_apply]
    exact Aut.ext rfl
  right_inv t := by
    simp only [MonoidHom.coe_comp, MonoidHom.coe_coe]
    exact (MulEquiv.eq_symm_apply (endMulEquivAutGalois F)).mp rfl
  map_mul' := by simp [map_mul]

Depends on / 依赖: Aut.toEnd, MonoidHom, MonoidHom.comp, endMulEquivAutGalois
-/
noncomputable def autMulEquivAutGalois : Aut F ≃* (AutGalois F)ᵐᵒᵖ where
  toFun := MonoidHom.comp (endMulEquivAutGalois F) (Aut.toEnd F)
  invFun t := asIso ((endMulEquivAutGalois F).symm t)
  left_inv t := by
    simp only [MonoidHom.coe_comp, MonoidHom.coe_coe, Function.comp_apply,
      MulEquiv.symm_apply_apply]
    exact Aut.ext rfl
  right_inv t := by
    simp only [MonoidHom.coe_comp, MonoidHom.coe_coe]
    exact (MulEquiv.eq_symm_apply (endMulEquivAutGalois F)).mp rfl
  map_mul' := by simp [map_mul]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `autMulEquivAutGalois_π` / 引理 `autMulEquivAutGalois_π`

English:
lemma autMulEquivAutGalois_π
  given: (f : Aut F) (A : C) [IsGalois A] (a : F.obj A)
  proof: by
  dsimp [autMulEquivAutGalois, endMulEquivAutGalois]
  rw [endEquivAutGalois_π]
  rfl

中文:
引理 autMulEquivAutGalois_π
  条件: (f : Aut F) (A : C) [是Galois A] (a : F.obj A)
  证明: by
  dsimp [autMulEquivAutGalois, endMulEquivAutGalois]
  rw [endEquivAutGalois_π]
  rfl

Depends on / 依赖: autMulEquivAutGalois
-/
lemma autMulEquivAutGalois_π (f : Aut F) (A : C) [IsGalois A] (a : F.obj A) :
    F.map (AutGalois.π F { obj := A, pt := a } (autMulEquivAutGalois F f).unop).hom a =
      f.hom.app A a := by
  dsimp [autMulEquivAutGalois, endMulEquivAutGalois]
  rw [endEquivAutGalois_π]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `autMulEquivAutGalois_symm_app` / 引理 `autMulEquivAutGalois_symm_app`

English:
lemma autMulEquivAutGalois_symm_app
  given: (x : AutGalois F) (A : C) [IsGalois A] (a : F.obj A)
  proof: by
  rw [← autMulEquivAutGalois_π]; rw [MulEquiv.apply_symm_apply]
  rfl

中文:
引理 autMulEquivAutGalois_symm_app
  条件: (x : AutGalois F) (A : C) [是Galois A] (a : F.obj A)
  证明: by
  rw [← autMulEquivAutGalois_π]; rw [MulEquiv.apply_symm_apply]
  rfl

Depends on / 依赖: MulEquiv, MulEquiv.apply_symm_apply, apply_symm_apply
-/
lemma autMulEquivAutGalois_symm_app (x : AutGalois F) (A : C) [IsGalois A] (a : F.obj A) :
    ((autMulEquivAutGalois F).symm ⟨x⟩).hom.app A a =
      F.map (AutGalois.π F ⟨A, a, inferInstance⟩ x).hom a := by
  rw [← autMulEquivAutGalois_π]; rw [MulEquiv.apply_symm_apply]
  rfl

end EndAutGaloisIsomorphism

/--
theorem `FiberFunctor.isPretransitive_of_isGalois` / 定理 `FiberFunctor.isPretransitive_of_isGalois`

English:
theorem FiberFunctor.isPretransitive_of_isGalois
  given: (X : C) [IsGalois X]
  proof: by
  refine ⟨fun x y => ?_⟩
  obtain ⟨(φ : Aut X), h⟩ := MulAction.IsPretransitive.exists_smul_eq (M := Aut X) x y
  obtain ⟨a, ha⟩ := AutGalois.π_surjective F ⟨X, x, inferInstance⟩ φ
  use (autMulEquivAutGalois F).symm ⟨a⟩
  simpa [mulAction_def, ha]

中文:
定理 Fiber函子.isPretransitive_of_isGalois
  条件: (X : C) [是Galois X]
  证明: by
  refine ⟨fun x y => ?_⟩
  obtain ⟨(φ : Aut X), h⟩ := MulAction.IsPretransitive.exists_smul_eq (M := Aut X) x y
  obtain ⟨a, ha⟩ := AutGalois.π_surjective F ⟨X, x, inferInstance⟩ φ
  use (autMulEquivAutGalois F).symm ⟨a⟩
  simpa [mulAction_def, ha]

Depends on / 依赖: AutGalois, IsPretransitive, MulAction, MulAction.IsPretransitive.exists_smul_eq, autMulEquivAutGalois, exists_smul_eq, mulAction_def
-/
theorem FiberFunctor.isPretransitive_of_isGalois (X : C) [IsGalois X] :
    MulAction.IsPretransitive (Aut F) (F.obj X) := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨(φ : Aut X), h⟩ := MulAction.IsPretransitive.exists_smul_eq (M := Aut X) x y
  obtain ⟨a, ha⟩ := AutGalois.π_surjective F ⟨X, x, inferInstance⟩ φ
  use (autMulEquivAutGalois F).symm ⟨a⟩
  simpa [mulAction_def, ha]

/--
Instance `FiberFunctor.isPretransitive_of_isConnected'` / 实例 `FiberFunctor.isPretransitive_of_isConnected'`

English:
instance FiberFunctor.isPretransitive_of_isConnected'
  signature: (X : C) [IsConnected X]
  body: by
  obtain ⟨A, f, hgal⟩ := exists_hom_from_galois_of_connected F X
  have hs : Function.Surjective (F.map f) := surjective_of_nonempty_fiber_of_isConnected F f
  refine ⟨fun x y => ?_⟩
  obtain ⟨a, ha⟩ := hs x
  obtain ⟨b, hb⟩ := hs y
  have : MulAction.IsPretransitive (Aut F) (F.obj A) := isPretransitive_of_isGalois F A
  obtain ⟨σ, (hσ : σ.hom.app A a = b)⟩ := MulAction.exists_smul_eq (Aut F) a b
  use σ
  rw [← ha]; rw [← hb]
  change (F.map f ≫ σ.hom.app X) a = F.map f b
  rw [σ.hom.naturality]; rw [FintypeCat.comp_apply]; rw [hσ]

中文:
实例 Fiber函子.isPretransitive_of_isConnected'
  签名: (X : C) [是连通 X]
  定义体: by
  obtain ⟨A, f, hgal⟩ := exists_hom_from_galois_of_connected F X
  have hs : Function.Surjective (F.map f) := surjective_of_nonempty_fiber_of_isConnected F f
  refine ⟨fun x y => ?_⟩
  obtain ⟨a, ha⟩ := hs x
  obtain ⟨b, hb⟩ := hs y
  have : MulAction.IsPretransitive (Aut F) (F.obj A) := isPretransitive_of_isGalois F A
  obtain ⟨σ, (hσ : σ.hom.app A a = b)⟩ := MulAction.exists_smul_eq (Aut F) a b
  use σ
  rw [← ha]; rw [← hb]
  change (F.map f ≫ σ.hom.app X) a = F.map f b
  rw [σ.hom.naturality]; rw [FintypeCat.comp_apply]; rw [hσ]

Depends on / 依赖: F.map, F.map_comp, F.map_id, G.obj, IsReflexivePair, IsReflexivePair.mk, adj.left_triangle_components, adj.right_triangle_components, adj.unit.app, left_triangle_components, map_comp, map_id, right_triangle_components
-/
private instance FiberFunctor.isPretransitive_of_isConnected' (X : C) [IsConnected X] :
    MulAction.IsPretransitive (Aut F) (F.obj X) := by
  obtain ⟨A, f, hgal⟩ := exists_hom_from_galois_of_connected F X
  have hs : Function.Surjective (F.map f) := surjective_of_nonempty_fiber_of_isConnected F f
  refine ⟨fun x y => ?_⟩
  obtain ⟨a, ha⟩ := hs x
  obtain ⟨b, hb⟩ := hs y
  have : MulAction.IsPretransitive (Aut F) (F.obj A) := isPretransitive_of_isGalois F A
  obtain ⟨σ, (hσ : σ.hom.app A a = b)⟩ := MulAction.exists_smul_eq (Aut F) a b
  use σ
  rw [← ha]; rw [← hb]
  change (F.map f ≫ σ.hom.app X) a = F.map f b
  rw [σ.hom.naturality]; rw [FintypeCat.comp_apply]; rw [hσ]

end Specialized

section General

variable (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `FiberFunctor.isPretransitive_of_isConnected` / 实例 `FiberFunctor.isPretransitive_of_isConnected`

English:
instance FiberFunctor.isPretransitive_of_isConnected
  signature: (X : C) [IsConnected X]
  body: by
    let F' : C ⥤ FintypeCat.{u₂} := F ⋙ FintypeCat.uSwitch.{w, u₂}
    let : FiberFunctor F' := FiberFunctor.comp_right _
    let e (Y : C) : F'.obj Y ≃ F.obj Y := (F.obj Y).uSwitchEquiv
    set x' : F'.obj X := (e X).symm x with hx'
    set y' : F'.obj X := (e X).symm y with hy'
    obtain ⟨g', (hg' : g'.hom.app X x' = y')⟩ := MulAction.exists_smul_eq (Aut F') x' y'
let gapp (Y : C) : F.obj Y ≅ F.obj Y := FintypeCat.equivEquivIso
(e Y).symm.trans (FintypeCat.equivEquivIso.symm (g'.app Y)).trans (e Y)
let g : F ≅ F := NatIso.ofComponents gapp fun {X Y} f => by
      ext x
      dsimp [gapp, e]
      erw [FintypeCat.uSwitchEquiv_naturality (F.map f)]
      rw [← Functor.comp_map]
      erw [← NatTrans.naturality_apply, FintypeCat.uSwitchEquiv_symm_naturality (F.map f)]
      rfl
    refine ⟨g, show (gapp X).hom x = y from ?_⟩
    simp [gapp, ← hx', hg', hy', Equiv.apply_symm_apply]

中文:
实例 Fiber函子.isPretransitive_of_isConnected
  签名: (X : C) [是连通 X]
  定义体: by
    let F' : C ⥤ FintypeCat.{u₂} := F ⋙ FintypeCat.uSwitch.{w, u₂}
    let : FiberFunctor F' := FiberFunctor.comp_right _
    let e (Y : C) : F'.obj Y ≃ F.obj Y := (F.obj Y).uSwitchEquiv
    set x' : F'.obj X := (e X).symm x with hx'
    set y' : F'.obj X := (e X).symm y with hy'
    obtain ⟨g', (hg' : g'.hom.app X x' = y')⟩ := MulAction.exists_smul_eq (Aut F') x' y'
let gapp (Y : C) : F.obj Y ≅ F.obj Y := FintypeCat.equivEquivIso
(e Y).symm.trans (FintypeCat.equivEquivIso.symm (g'.app Y)).trans (e Y)
let g : F ≅ F := NatIso.ofComponents gapp fun {X Y} f => by
      ext x
      dsimp [gapp, e]
      erw [FintypeCat.uSwitchEquiv_naturality (F.map f)]
      rw [← Functor.comp_map]
      erw [← NatTrans.naturality_apply, FintypeCat.uSwitchEquiv_symm_naturality (F.map f)]
      rfl
    refine ⟨g, show (gapp X).hom x = y from ?_⟩
    simp [gapp, ← hx', hg', hy', Equiv.apply_symm_apply]

Depends on / 依赖: F.obj, FiberFunctor, FiberFunctor.comp_right, FintypeCat, FintypeCat.equivEquivIso, FintypeCat.equivEquivIso.symm, FintypeCat.uSwitch, MulAction, MulAction.exists_smul_eq, comp_right, equivEquivIso, exists_smul_eq, hom.app, symm.trans, uSwitch, uSwitchEquiv
-/
instance FiberFunctor.isPretransitive_of_isConnected (X : C) [IsConnected X] :
    MulAction.IsPretransitive (Aut F) (F.obj X) where
  exists_smul_eq x y := by
    let F' : C ⥤ FintypeCat.{u₂} := F ⋙ FintypeCat.uSwitch.{w, u₂}
    let : FiberFunctor F' := FiberFunctor.comp_right _
    let e (Y : C) : F'.obj Y ≃ F.obj Y := (F.obj Y).uSwitchEquiv
    set x' : F'.obj X := (e X).symm x with hx'
    set y' : F'.obj X := (e X).symm y with hy'
    obtain ⟨g', (hg' : g'.hom.app X x' = y')⟩ := MulAction.exists_smul_eq (Aut F') x' y'
let gapp (Y : C) : F.obj Y ≅ F.obj Y := FintypeCat.equivEquivIso
(e Y).symm.trans (FintypeCat.equivEquivIso.symm (g'.app Y)).trans (e Y)
let g : F ≅ F := NatIso.ofComponents gapp fun {X Y} f => by
      ext x
      dsimp [gapp, e]
      erw [FintypeCat.uSwitchEquiv_naturality (F.map f)]
      rw [← Functor.comp_map]
      erw [← NatTrans.naturality_apply, FintypeCat.uSwitchEquiv_symm_naturality (F.map f)]
      rfl
    refine ⟨g, show (gapp X).hom x = y from ?_⟩
    simp [gapp, ← hx', hg', hy', Equiv.apply_symm_apply]

end General

end PreGaloisCategory

end CategoryTheory
