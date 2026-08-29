/-
Copyright (c) 2025 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne, Fernando Chu, Christian Merten
-/
module

public import Mathlib.CategoryTheory.Bicategory.Grothendieck
public import Mathlib.CategoryTheory.FiberedCategory.HasFibers

/-!
# The Grothendieck construction gives a fibered category

In this file we show that the Grothendieck construction applied to a pseudofunctor `F`
gives a fibered category over the base category.

We also provide a `HasFibers` instance to `∫ᶜ F`, such that the fiber over `S` is the
category `F(S)`.

## References
[Vistoli2008] "Notes on Grothendieck Topologies, Fibered Categories and Descent Theory" by
Angelo Vistoli

-/

@[expose] public section

namespace CategoryTheory.Pseudofunctor.CoGrothendieck

open CategoryTheory.Functor Opposite Bicategory Fiber

variable {𝒮 : Type*} [Category* 𝒮] {F : LocallyDiscrete 𝒮ᵒᵖ ⥤ᵖ Cat}

section

variable {R S : 𝒮} (a : F.obj ⟨op S⟩) (f : R ⟶ S)

/--
Definition of `domainCartesianLift` / `domainCartesianLift` 的定义

English:
abbreviation domainCartesianLift
  signature: : ∫ᶜ F
  body: ⟨R, (F.map f.op.toLoc).toFunctor.obj a⟩

中文:
缩写 domainCartesianLift
  签名: : ∫ᶜ F
  定义体: ⟨R, (F.map f.op.toLoc).toFunctor.obj a⟩

Depends on / 依赖: F.map, f.op.toLoc, toFunctor, toFunctor.obj
-/
abbrev domainCartesianLift : ∫ᶜ F := ⟨R, (F.map f.op.toLoc).toFunctor.obj a⟩

/--
Definition of `cartesianLift` / `cartesianLift` 的定义

English:
abbreviation cartesianLift
  signature: : domainCartesianLift a f ⟶ ⟨S, a⟩
  body: ⟨f, 𝟙 _⟩

中文:
缩写 cartesianLift
  签名: : domainCartesianLift a f ⟶ ⟨S, a⟩
  定义体: ⟨f, 𝟙 _⟩
-/
abbrev cartesianLift : domainCartesianLift a f ⟶ ⟨S, a⟩ := ⟨f, 𝟙 _⟩

/--
Instance `isHomLift_cartesianLift` / 实例 `isHomLift_cartesianLift`

English:
instance isHomLift_cartesianLift
  signature: : IsHomLift (forget F) f (cartesianLift a f)
  body: IsHomLift.map (forget F) (cartesianLift a f)

中文:
实例 isHomLift_cartesianLift
  签名: : IsHomLift (forget F) f (cartesianLift a f)
  定义体: IsHomLift.map (forget F) (cartesianLift a f)

Depends on / 依赖: HasBiproduct, HasProduct, IsHomLift, IsHomLift.map, cartesianLift, forget, hasProduct_of_hasBiproduct
-/
instance isHomLift_cartesianLift : IsHomLift (forget F) f (cartesianLift a f) :=
  IsHomLift.map (forget F) (cartesianLift a f)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
variable {a} in
/--
Definition of `homCartesianLift` / `homCartesianLift` 的定义

English:
abbreviation homCartesianLift
  signature: {a' : ∫ᶜ F} (g : a'.1 ⟶ R) (φ' : a' ⟶ ⟨S, a⟩)
  body: g
  fiber :=
    have : φ'.base = g ≫ f := by simpa using IsHomLift.fac' (forget F) (g ≫ f) φ'
    φ'.fiber ≫ eqToHom (by simp [this]) ≫ (F.mapComp f.op.toLoc g.op.toLoc).hom.toNatTrans.app a

中文:
缩写 homCartesianLift
  签名: {a' : ∫ᶜ F} (g : a'.1 ⟶ R) (φ' : a' ⟶ ⟨S, a⟩)
  定义体: g
  fiber :=
    have : φ'.base = g ≫ f := by simpa using IsHomLift.fac' (forget F) (g ≫ f) φ'
    φ'.fiber ≫ eqToHom (by simp [this]) ≫ (F.mapComp f.op.toLoc g.op.toLoc).hom.toNatTrans.app a

Depends on / 依赖: HasBiproduct, HasCoproduct, hasCoproduct_of_hasBiproduct
-/
abbrev homCartesianLift {a' : ∫ᶜ F} (g : a'.1 ⟶ R) (φ' : a' ⟶ ⟨S, a⟩)
    [IsHomLift (forget F) (g ≫ f) φ'] : a' ⟶ domainCartesianLift a f where
  base := g
  fiber :=
    have : φ'.base = g ≫ f := by simpa using IsHomLift.fac' (forget F) (g ≫ f) φ'
    φ'.fiber ≫ eqToHom (by simp [this]) ≫ (F.mapComp f.op.toLoc g.op.toLoc).hom.toNatTrans.app a

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `isHomLift_homCartesianLift` / 实例 `isHomLift_homCartesianLift`

English:
instance isHomLift_homCartesianLift
  signature: {a' : ∫ᶜ F} {φ' : a' ⟶ ⟨S, a⟩} {g : a'.1 ⟶ R}
  body: IsHomLift.map (forget F) (homCartesianLift f g φ')

中文:
实例 isHomLift_homCartesianLift
  签名: {a' : ∫ᶜ F} {φ' : a' ⟶ ⟨S, a⟩} {g : a'.1 ⟶ R}
  定义体: IsHomLift.map (forget F) (homCartesianLift f g φ')

Depends on / 依赖: IsHomLift, IsHomLift.map, forget, homCartesianLift
-/
instance isHomLift_homCartesianLift {a' : ∫ᶜ F} {φ' : a' ⟶ ⟨S, a⟩} {g : a'.1 ⟶ R}
    [IsHomLift (forget F) (g ≫ f) φ'] : IsHomLift (forget F) g (homCartesianLift f g φ') :=
  IsHomLift.map (forget F) (homCartesianLift f g φ')

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `isStronglyCartesian_homCartesianLift` / 引理 `isStronglyCartesian_homCartesianLift`

English:
lemma isStronglyCartesian_homCartesianLift
  proof: by
    refine ⟨homCartesianLift f g φ', ⟨inferInstance, ?_⟩, ?_⟩
    · exact Hom.ext _ _ (by simpa using IsHomLift.fac (forget F) (g ≫ f) φ')
        (by simp [← Cat.Hom₂.comp_app])
    rintro χ' ⟨hχ'.symm, rfl⟩
    obtain ⟨rfl⟩ : g = χ'.1 := by simpa using IsHomLift.fac (forget F) g χ'
    ext <;> simp [← Cat.Hom₂.comp_app]

中文:
引理 isStronglyCartesian_homCartesianLift
  证明: by
    refine ⟨homCartesianLift f g φ', ⟨inferInstance, ?_⟩, ?_⟩
    · exact Hom.ext _ _ (by simpa using IsHomLift.fac (forget F) (g ≫ f) φ')
        (by simp [← Cat.Hom₂.comp_app])
    rintro χ' ⟨hχ'.symm, rfl⟩
    obtain ⟨rfl⟩ : g = χ'.1 := by simpa using IsHomLift.fac (forget F) g χ'
    ext <;> simp [← Cat.Hom₂.comp_app]

Depends on / 依赖: Cat.Hom, Finite, HasFiniteBiproducts, Hom.ext, IsHomLift, IsHomLift.fac, comp_app, forget, hasBiproductsOfShape_finite, homCartesianLift
-/
lemma isStronglyCartesian_homCartesianLift :
    IsStronglyCartesian (forget F) f (cartesianLift a f) where
  universal_property' {a'} g φ' hφ' := by
    refine ⟨homCartesianLift f g φ', ⟨inferInstance, ?_⟩, ?_⟩
    · exact Hom.ext _ _ (by simpa using IsHomLift.fac (forget F) (g ≫ f) φ')
        (by simp [← Cat.Hom₂.comp_app])
    rintro χ' ⟨hχ'.symm, rfl⟩
    obtain ⟨rfl⟩ : g = χ'.1 := by simpa using IsHomLift.fac (forget F) g χ'
    ext <;> simp [← Cat.Hom₂.comp_app]

end

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsFibered (forget F)
  body: IsFibered.of_exists_isStronglyCartesian (fun a _ f =>
    ⟨domainCartesianLift a.2 f, cartesianLift a.2 f, isStronglyCartesian_homCartesianLift a.2 f⟩)

中文:
实例 :
  签名: 是Fibered (forget F)
  定义体: IsFibered.of_exists_isStronglyCartesian (fun a _ f =>
    ⟨domainCartesianLift a.2 f, cartesianLift a.2 f, isStronglyCartesian_homCartesianLift a.2 f⟩)

Depends on / 依赖: HasFiniteBiproducts, IsFibered, IsFibered.of_exists_isStronglyCartesian, cartesianLift, domainCartesianLift, hasFiniteProducts_of_hasFiniteBiproducts, isStronglyCartesian_homCartesianLift, of_exists_isStronglyCartesian
-/
instance : IsFibered (forget F) :=
  IsFibered.of_exists_isStronglyCartesian (fun a _ f =>
    ⟨domainCartesianLift a.2 f, cartesianLift a.2 f, isStronglyCartesian_homCartesianLift a.2 f⟩)

variable (F) (S : 𝒮)

set_option backward.isDefEq.respectTransparency false in
attribute [local simp] PrelaxFunctor.map₂_eqToHom in
/-- The inclusion map from `F(S)` into `∫ᶜ F`. -/
@[simps]
/--
Definition of `ι` / `ι` 的定义

English:
definition ι
  signature: : F.obj ⟨op S⟩ ⥤ ∫ᶜ F where
  body: { base := S, fiber := a }
  map {a b} φ := { base := 𝟙 S, fiber := φ ≫ (F.mapId ⟨op S⟩).inv.toNatTrans.app b }
  map_comp {a b c} φ ψ := by
    ext
    · simp
    · simp [← (F.mapId ⟨op S⟩).inv.toNatTrans.naturality_assoc ψ, F.whiskerRight_mapId_inv_app,
        Strict.leftUnitor_eqToIso, ← Cat.Hom₂.comp_app]

#adaptation_note

中文:
定义 ι
  签名: : F.obj ⟨op S⟩ ⥤ ∫ᶜ F where
  定义体: { base := S, fiber := a }
  map {a b} φ := { base := 𝟙 S, fiber := φ ≫ (F.mapId ⟨op S⟩).inv.toNatTrans.app b }
  map_comp {a b c} φ ψ := by
    ext
    · simp
    · simp [← (F.mapId ⟨op S⟩).inv.toNatTrans.naturality_assoc ψ, F.whiskerRight_mapId_inv_app,
        Strict.leftUnitor_eqToIso, ← Cat.Hom₂.comp_app]

#adaptation_note

Depends on / 依赖: HasFiniteBiproducts, hasFiniteCoproducts_of_hasFiniteBiproducts
-/
def ι : F.obj ⟨op S⟩ ⥤ ∫ᶜ F where
  obj a := { base := S, fiber := a }
  map {a b} φ := { base := 𝟙 S, fiber := φ ≫ (F.mapId ⟨op S⟩).inv.toNatTrans.app b }
  map_comp {a b c} φ ψ := by
    ext
    · simp
    · simp [← (F.mapId ⟨op S⟩).inv.toNatTrans.naturality_assoc ψ, F.whiskerRight_mapId_inv_app,
        Strict.leftUnitor_eqToIso, ← Cat.Hom₂.comp_app]

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The natural isomorphism encoding `comp_const`. -/
@[simps!]
/--
Definition of `compIso` / `compIso` 的定义

English:
definition compIso
  signature: : (ι F S) ⋙ forget F ≅ (const (F.obj ⟨op S⟩)).obj S
  body: NatIso.ofComponents (fun a => eqToIso rfl)

中文:
定义 compIso
  签名: : (ι F S) ⋙ forget F ≅ (const (F.obj ⟨op S⟩)).obj S
  定义体: NatIso.ofComponents (fun a => eqToIso rfl)

Depends on / 依赖: HasBiproductsOfShape, NatIso, NatIso.ofComponents, eqToIso, hasProductsOfShape_of_hasBiproductsOfShape, ofComponents
-/
def compIso : (ι F S) ⋙ forget F ≅ (const (F.obj ⟨op S⟩)).obj S :=
  NatIso.ofComponents (fun a => eqToIso rfl)

/--
lemma `comp_const` / 引理 `comp_const`

English:
lemma comp_const
  statement: (ι F S) ⋙ forget F = (const (F.obj ⟨op S⟩)).obj S
  proof: Functor.ext_of_iso (compIso F S) (fun _ => rfl) (fun _ => rfl)

中文:
引理 comp_const
  结论: (ι F S) ⋙ forget F = (const (F.obj ⟨op S⟩)).obj S
  证明: Functor.ext_of_iso (compIso F S) (fun _ => rfl) (fun _ => rfl)

Depends on / 依赖: Functor, Functor.ext_of_iso, HasBiproductsOfShape, compIso, ext_of_iso, hasCoproductsOfShape_of_hasBiproductsOfShape
-/
lemma comp_const : (ι F S) ⋙ forget F = (const (F.obj ⟨op S⟩)).obj S :=
  Functor.ext_of_iso (compIso F S) (fun _ => rfl) (fun _ => rfl)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (Fiber.inducedFunctor (comp_const F S)).Full
  body: by
    have hf : (fiberInclusion.map f).base = 𝟙 S := by
      simpa using (IsHomLift.fac (forget F) (𝟙 S) (fiberInclusion.map f)).symm
    use (fiberInclusion.map f).fiber ≫ eqToHom (by simp [hf]) ≫
      (F.mapId ⟨op S⟩).hom.toNatTrans.app Y
    ext <;> simp [hf, ← Cat.Hom₂.comp_app]

中文:
实例 :
  签名: (Fiber.inducedFunctor (comp_const F S)).满
  定义体: by
    have hf : (fiberInclusion.map f).base = 𝟙 S := by
      simpa using (IsHomLift.fac (forget F) (𝟙 S) (fiberInclusion.map f)).symm
    use (fiberInclusion.map f).fiber ≫ eqToHom (by simp [hf]) ≫
      (F.mapId ⟨op S⟩).hom.toNatTrans.app Y
    ext <;> simp [hf, ← Cat.Hom₂.comp_app]

Depends on / 依赖: Cat.Hom, F.mapId, IsHomLift, IsHomLift.fac, comp_app, eqToHom, fiberInclusion, fiberInclusion.map, forget, hom.toNatTrans.app, toNatTrans
-/
noncomputable instance : (Fiber.inducedFunctor (comp_const F S)).Full where
  map_surjective {X Y} f := by
    have hf : (fiberInclusion.map f).base = 𝟙 S := by
      simpa using (IsHomLift.fac (forget F) (𝟙 S) (fiberInclusion.map f)).symm
    use (fiberInclusion.map f).fiber ≫ eqToHom (by simp [hf]) ≫
      (F.mapId ⟨op S⟩).hom.toNatTrans.app Y
    ext <;> simp [hf, ← Cat.Hom₂.comp_app]

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (Fiber.inducedFunctor (comp_const F S)).Faithful
  body: by
    intro f g heq
    replace heq := fiberInclusion.congr_map heq
    simpa [cancel_mono, ← Cat.Hom.toNatIso_hom,
      ← Cat.Hom.toNatIso_inv] using ((Hom.ext_iff _ _).mp heq).2

中文:
实例 :
  签名: (Fiber.inducedFunctor (comp_const F S)).忠实
  定义体: by
    intro f g heq
    replace heq := fiberInclusion.congr_map heq
    simpa [cancel_mono, ← Cat.Hom.toNatIso_hom,
      ← Cat.Hom.toNatIso_inv] using ((Hom.ext_iff _ _).mp heq).2

Depends on / 依赖: Cat.Hom.toNatIso_hom, Cat.Hom.toNatIso_inv, Hom.ext_iff, cancel_mono, congr_map, ext_iff, fiberInclusion, fiberInclusion.congr_map, replace, toNatIso_hom, toNatIso_inv
-/
instance : (Fiber.inducedFunctor (comp_const F S)).Faithful where
  map_injective {a b} := by
    intro f g heq
    replace heq := fiberInclusion.congr_map heq
    simpa [cancel_mono, ← Cat.Hom.toNatIso_hom,
      ← Cat.Hom.toNatIso_inv] using ((Hom.ext_iff _ _).mp heq).2

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (Fiber.inducedFunctor (comp_const F S)).EssSurj
  body: by
  apply essSurj_of_surj
  intro Y
  have hYS : (fiberInclusion.obj Y).base = S := by simpa using! Y.2
  use hYS ▸ (fiberInclusion.obj Y).fiber
  apply fiberInclusion_obj_inj
  ext <;> simp [hYS]

中文:
实例 :
  签名: (Fiber.inducedFunctor (comp_const F S)).本质满射
  定义体: by
  apply essSurj_of_surj
  intro Y
  have hYS : (fiberInclusion.obj Y).base = S := by simpa using! Y.2
  use hYS ▸ (fiberInclusion.obj Y).fiber
  apply fiberInclusion_obj_inj
  ext <;> simp [hYS]

Depends on / 依赖: essSurj_of_surj, fiberInclusion, fiberInclusion.obj, fiberInclusion_obj_inj
-/
noncomputable instance : (Fiber.inducedFunctor (comp_const F S)).EssSurj := by
  apply essSurj_of_surj
  intro Y
  have hYS : (fiberInclusion.obj Y).base = S := by simpa using! Y.2
  use hYS ▸ (fiberInclusion.obj Y).fiber
  apply fiberInclusion_obj_inj
  ext <;> simp [hYS]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (Fiber.inducedFunctor (comp_const F S)).IsEquivalence

中文:
实例 :
  签名: (Fiber.inducedFunctor (comp_const F S)).是等价
-/
noncomputable instance : (Fiber.inducedFunctor (comp_const F S)).IsEquivalence where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasFibers (forget F)
  body: F.obj ⟨op S⟩
  ι := ι F
  comp_const := comp_const F

中文:
实例 :
  签名: 有Fibers (forget F)
  定义体: F.obj ⟨op S⟩
  ι := ι F
  comp_const := comp_const F

Depends on / 依赖: F.obj
-/
noncomputable instance : HasFibers (forget F) where
  Fib S := F.obj ⟨op S⟩
  ι := ι F
  comp_const := comp_const F

end CategoryTheory.Pseudofunctor.CoGrothendieck
