/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.Tactic.ApplyFun
/-!
# Cover-preserving functors between sites.

In order to show that a functor is continuous, we define cover-preserving functors
between sites as functors that push covering sieves to covering sieves.
Then, a cover-preserving and compatible-preserving functor is continuous.

## Main definitions

* `CategoryTheory.CoverPreserving`: a functor between sites is cover-preserving if it
  pushes covering sieves to covering sieves
* `CategoryTheory.CompatiblePreserving`: a functor between sites is compatible-preserving
  if it pushes compatible families of elements to compatible families.

## Main results

- `CategoryTheory.isContinuous_of_coverPreserving`: If `G : C ⥤ D` is
  cover-preserving and compatible-preserving, then `G` is a continuous functor,
  i.e. `G.op ⋙ -` as a functor `(Dᵒᵖ ⥤ A) ⥤ (Cᵒᵖ ⥤ A)` of presheaves maps sheaves to sheaves.

## References

* [Elephant]: *Sketches of an Elephant*, P. T. Johnstone: C2.3.
* https://stacks.math.columbia.edu/tag/00WU

-/

public section


universe w v₁ v₂ v₃ u₁ u₂ u₃

noncomputable section

open CategoryTheory Opposite CategoryTheory.Presieve.FamilyOfElements CategoryTheory.Presieve
  CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)
variable {A : Type u₃} [Category.{v₃} A]
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable {L : GrothendieckTopology A}

/--
Definition of `CoverPreserving` / `CoverPreserving` 的定义

English:
structure CoverPreserving
  parameters: (G : C ⥤ D)
  axioms and operations (1):
    - cover_preserve : forall {U : C} {S : Sieve U} (_ : S in J U), S.functorPushforward G in K (G.obj U)

中文:
结构 CoverPreserving
  参数: (G : C ⥤ D)
  公理与运算 (1 个):
    - cover_preserve : 对任意 {U : C} {S : Sieve U} (_ : S in J U), S.functorPushforward G in K (G.obj U)
-/
structure CoverPreserving (G : C ⥤ D) : Prop where
  cover_preserve : forall {U : C} {S : Sieve U} (_ : S in J U), S.functorPushforward G in K (G.obj U)

/--
theorem `idCoverPreserving` / 定理 `idCoverPreserving`

English:
theorem idCoverPreserving
  statement: CoverPreserving J J (𝟭 _)
  proof: ⟨fun hS => by simpa using! hS⟩

中文:
定理 idCoverPreserving
  结论: CoverPreserving J J (𝟭 _)
  证明: ⟨fun hS => by simpa using! hS⟩
-/
theorem idCoverPreserving : CoverPreserving J J (𝟭 _) :=
  ⟨fun hS => by simpa using! hS⟩

/--
theorem `CoverPreserving.comp` / 定理 `CoverPreserving.comp`

English:
theorem CoverPreserving.comp
  given: {F} (hF : CoverPreserving J K F) {G} (hG : CoverPreserving K L G)
  proof: ⟨fun hS => by
    rw [Sieve.functorPushforward_comp]
    exact hG.cover_preserve (hF.cover_preserve hS)⟩

中文:
定理 CoverPreserving.comp
  条件: {F} (hF : CoverPreserving J K F) {G} (hG : CoverPreserving K L G)
  证明: ⟨fun hS => by
    rw [Sieve.functorPushforward_comp]
    exact hG.cover_preserve (hF.cover_preserve hS)⟩

Depends on / 依赖: Sieve.functorPushforward_comp, cover_preserve, functorPushforward_comp, hF.cover_preserve, hG.cover_preserve
-/
theorem CoverPreserving.comp {F} (hF : CoverPreserving J K F) {G} (hG : CoverPreserving K L G) :
    CoverPreserving J L (F ⋙ G) :=
  ⟨fun hS => by
    rw [Sieve.functorPushforward_comp]
    exact hG.cover_preserve (hF.cover_preserve hS)⟩

/--
Definition of `CompatiblePreserving` / `CompatiblePreserving` 的定义

English:
structure CompatiblePreserving
  parameters: (K : GrothendieckTopology D) (G : C ⥤ D)
  axioms and operations (1):
    - compatible : forall (ℱ : Sheaf K (Type w)) {Z} {T : Presieve Z} {x : FamilyOfElements (G.op ⋙ ℱ.obj) T} (_ : x.Compatible) {Y₁ Y₂} {X} (f₁ : X ⟶ G.obj Y₁) (f₂ : X ⟶ G.obj Y₂) {g₁ : Y₁ ⟶ Z} {g₂ : Y₂ ⟶ Z} (hg₁ : T g₁) (hg₂ : T g₂) (_ : f₁ ≫ G.map g₁ = f₂ ≫ G.map g₂), ℱ.obj.map f₁.op (x g₁ hg₁) = ℱ.obj.map f₂.op (x g₂ hg₂)

中文:
结构 CompatiblePreserving
  参数: (K : GrothendieckTopology D) (G : C ⥤ D)
  公理与运算 (1 个):
    - compatible : 对任意 (ℱ : Sheaf K (Type w)) {Z} {T : Presieve Z} {x : FamilyOfElements (G.op ⋙ ℱ.obj) T} (_ : x.Compatible) {Y₁ Y₂} {X} (f₁ : X ⟶ G.obj Y₁) (f₂ : X ⟶ G.obj Y₂) {g₁ : Y₁ ⟶ Z} {g₂ : Y₂ ⟶ Z} (hg₁ : T g₁) (hg₂ : T g₂) (_ : f₁ ≫ G.map g₁ = f₂ ≫ G.map g₂), ℱ.obj.map f₁.op (x g₁ hg₁) = ℱ.obj.map f₂.op (x g₂ hg₂)
-/
structure CompatiblePreserving (K : GrothendieckTopology D) (G : C ⥤ D) : Prop where
  compatible :
    forall (ℱ : Sheaf K (Type w)) {Z} {T : Presieve Z} {x : FamilyOfElements (G.op ⋙ ℱ.obj) T}
      (_ : x.Compatible) {Y₁ Y₂} {X} (f₁ : X ⟶ G.obj Y₁) (f₂ : X ⟶ G.obj Y₂) {g₁ : Y₁ ⟶ Z}
      {g₂ : Y₂ ⟶ Z} (hg₁ : T g₁) (hg₂ : T g₂) (_ : f₁ ≫ G.map g₁ = f₂ ≫ G.map g₂),
      ℱ.obj.map f₁.op (x g₁ hg₁) = ℱ.obj.map f₂.op (x g₂ hg₂)

section
variable {J K} {G : C ⥤ D} (hG : CompatiblePreserving.{w} K G) (ℱ : Sheaf K (Type w)) {Z : C}
variable {T : Presieve Z} {x : FamilyOfElements (G.op ⋙ ℱ.obj) T} (h : x.Compatible)
include hG h

/--
theorem `Presieve.FamilyOfElements.Compatible.functorPushforward` / 定理 `Presieve.FamilyOfElements.Compatible.functorPushforward`

English:
theorem Presieve.FamilyOfElements.Compatible.functorPushforward
  proof: by
  rintro Z₁ Z₂ W g₁ g₂ f₁' f₂' H₁ H₂ eq
  unfold FamilyOfElements.functorPushforward
  rcases getFunctorPushforwardStructure H₁ with ⟨X₁, f₁, h₁, hf₁, rfl⟩
  rcases getFunctorPushforwardStructure H₂ with ⟨X₂, f₂, h₂, hf₂, rfl⟩
  suffices ℱ.obj.map (g₁ ≫ h₁).op (x f₁ hf₁) = ℱ.obj.map (g₂ ≫ h₂).op 

中文:
定理 Presieve.FamilyOfElements.Compatible.functorPushforward
  证明: by
  rintro Z₁ Z₂ W g₁ g₂ f₁' f₂' H₁ H₂ eq
  unfold FamilyOfElements.functorPushforward
  rcases getFunctorPushforwardStructure H₁ with ⟨X₁, f₁, h₁, hf₁, rfl⟩
  rcases getFunctorPushforwardStructure H₂ with ⟨X₂, f₂, h₂, hf₂, rfl⟩
  suffices ℱ.obj.map (g₁ ≫ h₁).op (x f₁ hf₁) = ℱ.obj.map (g₂ ≫ h₂).op 

Depends on / 依赖: FamilyOfElements, FamilyOfElements.functorPushforward, compatible, functorPushforward, getFunctorPushforwardStructure, hG.compatible, obj.map
-/
theorem Presieve.FamilyOfElements.Compatible.functorPushforward :
    (x.functorPushforward G).Compatible := by
  rintro Z₁ Z₂ W g₁ g₂ f₁' f₂' H₁ H₂ eq
  unfold FamilyOfElements.functorPushforward
  rcases getFunctorPushforwardStructure H₁ with ⟨X₁, f₁, h₁, hf₁, rfl⟩
  rcases getFunctorPushforwardStructure H₂ with ⟨X₂, f₂, h₂, hf₂, rfl⟩
  suffices ℱ.obj.map (g₁ ≫ h₁).op (x f₁ hf₁) = ℱ.obj.map (g₂ ≫ h₂).op (x f₂ hf₂) by
    simpa using this
  apply hG.compatible ℱ h _ _ hf₁ hf₂
  simpa using eq

@[simp]
/--
theorem `CompatiblePreserving.apply_map` / 定理 `CompatiblePreserving.apply_map`

English:
theorem CompatiblePreserving.apply_map
  given: {Y : C} {f : Y ⟶ Z} (hf : T f)
  proof: by
  unfold FamilyOfElements.functorPushforward
  rcases getFunctorPushforwardStructure (image_mem_functorPushforward G T hf) with
    ⟨X, g, f', hg, eq⟩
  simpa using hG.compatible ℱ h f' (𝟙 _) hg hf (by simp [eq])

中文:
定理 CompatiblePreserving.apply_map
  条件: {Y : C} {f : Y ⟶ Z} (hf : T f)
  证明: by
  unfold FamilyOfElements.functorPushforward
  rcases getFunctorPushforwardStructure (image_mem_functorPushforward G T hf) with
    ⟨X, g, f', hg, eq⟩
  simpa using hG.compatible ℱ h f' (𝟙 _) hg hf (by simp [eq])

Depends on / 依赖: FamilyOfElements, FamilyOfElements.functorPushforward, compatible, functorPushforward, getFunctorPushforwardStructure, hG.compatible, image_mem_functorPushforward
-/
theorem CompatiblePreserving.apply_map {Y : C} {f : Y ⟶ Z} (hf : T f) :
    x.functorPushforward G (G.map f) (image_mem_functorPushforward G T hf) = x f hf := by
  unfold FamilyOfElements.functorPushforward
  rcases getFunctorPushforwardStructure (image_mem_functorPushforward G T hf) with
    ⟨X, g, f', hg, eq⟩
  simpa using hG.compatible ℱ h f' (𝟙 _) hg hf (by simp [eq])

end

open Limits.WalkingCospan

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `compatiblePreservingOfFlat` / 定理 `compatiblePreservingOfFlat`

English:
theorem compatiblePreservingOfFlat
  statement: {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  proof: by
  constructor
  intro ℱ Z T x hx Y₁ Y₂ X f₁ f₂ g₁ g₂ hg₁ hg₂ e
  -- First, `f₁` and `f₂` form a cone over `cospan g₁ g₂ ⋙ u`.
  let c : Cone (cospan g₁ g₂ ⋙ G) :=
    (Cone.postcompose (diagramIsoCospan (cospan g₁ g₂ ⋙ G)).inv).obj (PullbackCone.mk f₁ f₂ e)
  /-
    This can then be viewed as a c

中文:
定理 compatiblePreservingOfFlat
  结论: {C : 类型u₁} [Category.{v₁} C] {D : 类型u₂} [Category.{v₂} D]
  证明: by
  constructor
  intro ℱ Z T x hx Y₁ Y₂ X f₁ f₂ g₁ g₂ hg₁ hg₂ e
  -- First, `f₁` and `f₂` form a cone over `cospan g₁ g₂ ⋙ u`.
  let c : Cone (cospan g₁ g₂ ⋙ G) :=
    (Cone.postcompose (diagramIsoCospan (cospan g₁ g₂ ⋙ G)).inv).obj (PullbackCone.mk f₁ f₂ e)
  /-
    This can then be viewed as a c
-/
theorem compatiblePreservingOfFlat {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (K : GrothendieckTopology D) (G : C ⥤ D) [RepresentablyFlat G] : CompatiblePreserving K G := by
  constructor
  intro ℱ Z T x hx Y₁ Y₂ X f₁ f₂ g₁ g₂ hg₁ hg₂ e
  -- First, `f₁` and `f₂` form a cone over `cospan g₁ g₂ ⋙ u`.
  let c : Cone (cospan g₁ g₂ ⋙ G) :=
    (Cone.postcompose (diagramIsoCospan (cospan g₁ g₂ ⋙ G)).inv).obj (PullbackCone.mk f₁ f₂ e)
  /-
    This can then be viewed as a cospan of structured arrows, and we may obtain an arbitrary cone
    over it since `StructuredArrow W u` is cofiltered.
    Then, it suffices to prove that it is compatible when restricted onto `u(c'.X.right)`.
    -/
  let c' := IsCofiltered.cone (c.toStructuredArrow ⋙ StructuredArrow.pre _ _ _)
  have eq₁ : f₁ = (c'.pt.hom ≫ G.map (c'.π.app left).right) ≫ eqToHom (by simp) := by simp [c]
  have eq₂ : f₂ = (c'.pt.hom ≫ G.map (c'.π.app right).right) ≫ eqToHom (by simp) := by simp [c]
  conv_lhs => rw [eq₁]
  conv_rhs => rw [eq₂]
  simp only [c, op_comp, Functor.map_comp, types_comp_apply, eqToHom_op, eqToHom_map]
  apply congr_arg -- Porting note: was `congr 1` which for some reason doesn't do anything here
  -- despite goal being of the form f a = f b, with f=`ℱ.val.map (Quiver.Hom.op c'.pt.hom)`
  /-
    Since everything now falls in the image of `u`,
    the result follows from the compatibility of `x` in the image of `u`.
    -/
  injection c'.π.naturality WalkingCospan.Hom.inl with _ e₁
  injection c'.π.naturality WalkingCospan.Hom.inr with _ e₂
  exact hx (c'.π.app left).right (c'.π.app right).right hg₁ hg₂ (e₁.symm.trans e₂)

set_option backward.defeqAttrib.useBackward true in
/--
theorem `compatiblePreservingOfDownwardsClosed` / 定理 `compatiblePreservingOfDownwardsClosed`

English:
theorem compatiblePreservingOfDownwardsClosed
  statement: (F : C ⥤ D) [F.Full] [F.Faithful]
  proof: by
  constructor
  introv hx he
  obtain ⟨X', e⟩ := hF f₁
  apply (ℱ.1.mapIso e.op).toEquiv.injective
  simp only [Iso.op_hom, Iso.toEquiv_fun, ℱ.1.mapIso_hom, ← Functor.map_comp_apply]
  simpa using!
    hx (F.preimage <| e.hom ≫ f₁) (F.preimage <| e.hom ≫ f₂) hg₁ hg₂
      (F.map_injective <| by s

中文:
定理 compatiblePreservingOfDownwardsClosed
  结论: (F : C ⥤ D) [F.Full] [F.Faithful]
  证明: by
  constructor
  introv hx he
  obtain ⟨X', e⟩ := hF f₁
  apply (ℱ.1.mapIso e.op).toEquiv.injective
  simp only [Iso.op_hom, Iso.toEquiv_fun, ℱ.1.mapIso_hom, ← Functor.map_comp_apply]
  simpa using!
    hx (F.preimage <| e.hom ≫ f₁) (F.preimage <| e.hom ≫ f₂) hg₁ hg₂
      (F.map_injective <| by s

Depends on / 依赖: F.map_injective, F.preimage, Functor, Functor.map_comp_apply, Iso.op_hom, Iso.toEquiv_fun, e.hom, e.op, injective, introv, mapIso, mapIso_hom, map_comp_apply, map_injective, op_hom, preimage, toEquiv, toEquiv.injective, toEquiv_fun
-/
theorem compatiblePreservingOfDownwardsClosed (F : C ⥤ D) [F.Full] [F.Faithful]
    (hF : forall {c : C} {d : D} (_ : d ⟶ F.obj c), Σ c', F.obj c' ≅ d) : CompatiblePreserving K F := by
  constructor
  introv hx he
  obtain ⟨X', e⟩ := hF f₁
  apply (ℱ.1.mapIso e.op).toEquiv.injective
  simp only [Iso.op_hom, Iso.toEquiv_fun, ℱ.1.mapIso_hom, ← Functor.map_comp_apply]
  simpa using!
    hx (F.preimage <| e.hom ≫ f₁) (F.preimage <| e.hom ≫ f₂) hg₁ hg₂
      (F.map_injective <| by simpa using! he)

variable {F J K}

/-- If `F` is cover-preserving and compatible-preserving, then `F` is a continuous functor. -/
@[stacks 00WW "This is basically this Stacks entry."]
/--
lemma `Functor.isContinuous_of_coverPreserving` / 引理 `Functor.isContinuous_of_coverPreserving`

English:
lemma Functor.isContinuous_of_coverPreserving
  statement: (hF₁ : CompatiblePreserving.{max u₁ v₁ u₂ v₂} K F)
  proof: by
    apply existsUnique_of_exists_of_unique
    · have H := (isSheaf_iff_isSheaf_of_type _ _).1 G.2 _ (hF₂.cover_preserve hS)
      exact ⟨H.amalgamate (x.functorPushforward F) (hx.functorPushforward hF₁),
        fun V f hf => (H.isAmalgamation (hx.functorPushforward hF₁) (F.map f) _).trans
     

中文:
引理 Functor.isContinuous_of_coverPreserving
  结论: (hF₁ : CompatiblePreserving.{max u₁ v₁ u₂ v₂} K F)
  证明: by
    apply existsUnique_of_exists_of_unique
    · have H := (isSheaf_iff_isSheaf_of_type _ _).1 G.2 _ (hF₂.cover_preserve hS)
      exact ⟨H.amalgamate (x.functorPushforward F) (hx.functorPushforward hF₁),
        fun V f hf => (H.isAmalgamation (hx.functorPushforward hF₁) (F.map f) _).trans
     

Depends on / 依赖: F.map, H.amalgamate, H.isAmalgamation, amalgamate, apply_map, cover_preserve, existsUnique_of_exists_of_unique, functorPushforward, hx.functorPushforward, isAmalgamation, isSeparated, isSheaf_iff_isSheaf_of_type, x.functorPushforward
-/
lemma Functor.isContinuous_of_coverPreserving (hF₁ : CompatiblePreserving.{max u₁ v₁ u₂ v₂} K F)
    (hF₂ : CoverPreserving J K F) : Functor.IsContinuous F J K where
  op_comp_isSheaf_of_types G X S hS x hx := by
    apply existsUnique_of_exists_of_unique
    · have H := (isSheaf_iff_isSheaf_of_type _ _).1 G.2 _ (hF₂.cover_preserve hS)
      exact ⟨H.amalgamate (x.functorPushforward F) (hx.functorPushforward hF₁),
        fun V f hf => (H.isAmalgamation (hx.functorPushforward hF₁) (F.map f) _).trans
          (hF₁.apply_map _ hx hf)⟩
    · intro y₁ y₂ hy₁ hy₂
      apply (((isSheaf_iff_isSheaf_of_type _ _).1 G.2).isSeparated _ (hF₂.cover_preserve hS)).ext
      rintro Y _ ⟨Z, g, h, hg, rfl⟩
      simpa using! congrArg _ ((hy₁ g hg).trans (hy₂ g hg).symm)

variable (F J K) in
/--
lemma `CoverPreserving.of_isContinuous` / 引理 `CoverPreserving.of_isContinuous`

English:
lemma CoverPreserving.of_isContinuous
  given: [F.IsContinuous J K]
  statement: CoverPreserving J K F where
  proof: by
    rw [K.mem_iff_isSheafFor_closedSieves]
    obtain ⟨ι, Y, f, rfl⟩ := S.exists_eq_ofArrows
    rw [Sieve.ofArrows]; rw [← Sieve.generate_map_eq_functorPushforward]; rw [← Presieve.isSheafFor_iff_generate]; rw [Presieve.map_ofArrows]
    have := Functor.op_comp_isSheaf_of_isSheaf_type F J (class

中文:
引理 CoverPreserving.of_isContinuous
  条件: [F.IsContinuous J K]
  结论: CoverPreserving J K F where
  证明: by
    rw [K.mem_iff_isSheafFor_closedSieves]
    obtain ⟨ι, Y, f, rfl⟩ := S.exists_eq_ofArrows
    rw [Sieve.ofArrows]; rw [← Sieve.generate_map_eq_functorPushforward]; rw [← Presieve.isSheafFor_iff_generate]; rw [Presieve.map_ofArrows]
    have := Functor.op_comp_isSheaf_of_isSheaf_type F J (class

Depends on / 依赖: Functo, Functor, Functor.op_comp_isSheaf_of_isSheaf_type, K.mem_iff_isSheafFor_closedSieves, Presieve, Presieve.isSheafFor_arrows_iff, Presieve.isSheafFor_iff_generate, Presieve.map_ofArrows, S.exists_eq_ofArrows, Sieve.generate_map_eq_functorPushforward, Sieve.ofArrows, classifier_isSheaf, exists_eq_ofArrows, generate_map_eq_functorPushforward, isSheafFor_arrows_iff, isSheafFor_iff_generate, map_ofArrows, mem_iff_isSheafFor_closedSieves, ofArrows, op_comp_isSheaf_of_isSheaf_type
-/
lemma CoverPreserving.of_isContinuous [F.IsContinuous J K] : CoverPreserving J K F where
  cover_preserve {X S} hS := by
    rw [K.mem_iff_isSheafFor_closedSieves]
    obtain ⟨ι, Y, f, rfl⟩ := S.exists_eq_ofArrows
    rw [Sieve.ofArrows]; rw [← Sieve.generate_map_eq_functorPushforward]; rw [← Presieve.isSheafFor_iff_generate]; rw [Presieve.map_ofArrows]
    have := Functor.op_comp_isSheaf_of_isSheaf_type F J (classifier_isSheaf K) _ hS
    rw [Sieve.ofArrows]; rw [← Presieve.isSheafFor_iff_generate] at this
    rw [Presieve.isSheafFor_arrows_iff] at this ⊢
    intro x hx
    refine this x fun i j Z gi gj hgij => hx _ _ _ _ _ ?_
    simp [← Functor.map_comp, hgij]

/--
lemma `Functor.isContinuous_iff_coverPreserving` / 引理 `Functor.isContinuous_iff_coverPreserving`

English:
lemma Functor.isContinuous_iff_coverPreserving
  given: [RepresentablyFlat F]
  proof: by
  refine ⟨fun h => .of_isContinuous _ _ _, fun h => ?_⟩
  apply Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _) h

中文:
引理 Functor.isContinuous_iff_coverPreserving
  条件: [RepresentablyFlat F]
  证明: by
  refine ⟨fun h => .of_isContinuous _ _ _, fun h => ?_⟩
  apply Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _) h

Depends on / 依赖: Functor, Functor.isContinuous_of_coverPreserving, compatiblePreservingOfFlat, isContinuous_of_coverPreserving, of_isContinuous
-/
lemma Functor.isContinuous_iff_coverPreserving [RepresentablyFlat F] :
    F.IsContinuous J K ↔ CoverPreserving J K F := by
  refine ⟨fun h => .of_isContinuous _ _ _, fun h => ?_⟩
  apply Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _) h

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `Functor.PreservesOneHypercovers.of_coverPreserving` / 引理 `Functor.PreservesOneHypercovers.of_coverPreserving`

English:
lemma Functor.PreservesOneHypercovers.of_coverPreserving
  statement: [HasPullbacks C]
  proof: by
  refine fun {U} E => ⟨?_, fun i₁ i₂ W p₁ p₂ h => ?_⟩
  · simp [PreZeroHypercover.sieve₀_map, H.cover_preserve E.mem₀]
  · let P : C := pullback (E.f i₁) (E.f i₂)
    have : HasPullback ((E.toPreOneHypercover.map F).f i₁) ((E.toPreOneHypercover.map F).f i₂) :=
      hasPullback_of_preservesPullba

中文:
引理 Functor.PreservesOneHypercovers.of_coverPreserving
  结论: [HasPullbacks C]
  证明: by
  refine fun {U} E => ⟨?_, fun i₁ i₂ W p₁ p₂ h => ?_⟩
  · simp [PreZeroHypercover.sieve₀_map, H.cover_preserve E.mem₀]
  · let P : C := pullback (E.f i₁) (E.f i₂)
    have : HasPullback ((E.toPreOneHypercover.map F).f i₁) ((E.toPreOneHypercover.map F).f i₂) :=
      hasPullback_of_preservesPullba

Depends on / 依赖: E.mem, E.toPreOneHypercover.map, H.cover_preserve, HasPullback, PreOneHypercover, PreOneHypercover.functorPushforward_sieve, PreZeroHypercover, PreZeroHypercover.sieve, condition, cover_preserve, hasPullback_of_preservesPullback, pullback, pullback.condition, pullback.fst, toPreOneHypercover
-/
lemma Functor.PreservesOneHypercovers.of_coverPreserving [HasPullbacks C]
    [PreservesLimitsOfShape WalkingCospan F] (H : CoverPreserving J K F) :
    Functor.PreservesOneHypercovers.{w} F J K := by
  refine fun {U} E => ⟨?_, fun i₁ i₂ W p₁ p₂ h => ?_⟩
  · simp [PreZeroHypercover.sieve₀_map, H.cover_preserve E.mem₀]
  · let P : C := pullback (E.f i₁) (E.f i₂)
    have : HasPullback ((E.toPreOneHypercover.map F).f i₁) ((E.toPreOneHypercover.map F).f i₂) :=
      hasPullback_of_preservesPullback F (E.f i₁) (E.f i₂)
    have := H.cover_preserve (E.mem₁ i₁ i₂ (pullback.fst (E.f i₁) (E.f i₂)) _ pullback.condition)
    rw [PreOneHypercover.functorPushforward_sieve₁_of_preservesPullbacks _ _ _
      pullback.condition] at this
    refine K.superset_covering ?_
      (K.pullback_stable (IsPullback.lift (.map _ (.of_hasPullback _ _)) p₁ p₂ h) this)
    simp [PreOneHypercover.pullback_sieve₁]

end CategoryTheory
