/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Fangming Li
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion

/-!
# Stalks of a Scheme

## Main definitions and results

- `AlgebraicGeometry.Scheme.fromSpecStalk`: The canonical morphism `Spec 𝒪_{X, x} ⟶ X`.
- `AlgebraicGeometry.Scheme.range_fromSpecStalk`: The range of the map `Spec 𝒪_{X, x} ⟶ X` is
  exactly the `y`s that specialize to `x`.
- `AlgebraicGeometry.SpecToEquivOfLocalRing`:
  Given a local ring `R` and scheme `X`, morphisms `Spec R ⟶ X` corresponds to pairs
  `(x, f)` where `x : X` and `f : 𝒪_{X, x} ⟶ R` is a local ring homomorphism.
-/

@[expose] public section

namespace AlgebraicGeometry

open CategoryTheory Opposite TopologicalSpace IsLocalRing

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)

section fromSpecStalk

/--
Definition of `IsAffineOpen.fromSpecStalk` / `IsAffineOpen.fromSpecStalk` 的定义

English:
definition IsAffineOpen.fromSpecStalk
  body: Spec.map (X.presheaf.germ _ x hxU) ≫ hU.fromSpec

中文:
定义 是仿射开集.fromSpecStalk
  定义体: Spec.map (X.presheaf.germ _ x hxU) ≫ hU.fromSpec

Depends on / 依赖: Spec.map, X.presheaf.germ, fromSpec, hU.fromSpec, presheaf
-/
noncomputable def IsAffineOpen.fromSpecStalk
    {X : Scheme} {U : X.Opens} (hU : IsAffineOpen U) {x : X} (hxU : x in U) :
    Spec (X.presheaf.stalk x) ⟶ X :=
  Spec.map (X.presheaf.germ _ x hxU) ≫ hU.fromSpec

/--
theorem `IsAffineOpen.fromSpecStalk_eq` / 定理 `IsAffineOpen.fromSpecStalk_eq`

English:
theorem IsAffineOpen.fromSpecStalk_eq
  given: (x : X) (hxU : x in U) (hxV : x in V)
  proof: by
  obtain ⟨U', h₁, h₂, h₃ : U' <= U ⊓ V⟩ :=
    Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens (show x in U ⊓ V from ⟨hxU, hxV⟩)
  transitivity fromSpecStalk h₁ h₂
  · delta fromSpecStalk
    rw [← hU.map_fromSpec h₁ (homOfLE <| h₃.trans inf_le_left).op]; rw [← Spec.map_comp_assoc]; rw [TopCat.Pr

中文:
定理 是仿射开集.fromSpecStalk_eq
  条件: (x : X) (hxU : x in U) (hxV : x in V)
  证明: by
  obtain ⟨U', h₁, h₂, h₃ : U' <= U ⊓ V⟩ :=
    Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens (show x in U ⊓ V from ⟨hxU, hxV⟩)
  transitivity fromSpecStalk h₁ h₂
  · delta fromSpecStalk
    rw [← hU.map_fromSpec h₁ (homOfLE <| h₃.trans inf_le_left).op]; rw [← Spec.map_comp_assoc]; rw [TopCat.Pr

Depends on / 依赖: Opens.isBasis_iff_nbhd.mp, Presheaf, Spec.map_comp_assoc, TopCat, TopCat.Presheaf.germ_res, X.isBasis_affineOpens, fromSpecStalk, germ_res, hU.map_fromSpec, hV.map_fromSpec, homOfLE, inf_le_left, inf_le_right, isBasis_affineOpens, isBasis_iff_nbhd, map_comp_assoc, map_fromSpec, transitivity
-/
theorem IsAffineOpen.fromSpecStalk_eq (x : X) (hxU : x in U) (hxV : x in V) :
    hU.fromSpecStalk hxU = hV.fromSpecStalk hxV := by
  obtain ⟨U', h₁, h₂, h₃ : U' <= U ⊓ V⟩ :=
    Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens (show x in U ⊓ V from ⟨hxU, hxV⟩)
  transitivity fromSpecStalk h₁ h₂
  · delta fromSpecStalk
    rw [← hU.map_fromSpec h₁ (homOfLE <| h₃.trans inf_le_left).op]; rw [← Spec.map_comp_assoc]; rw [TopCat.Presheaf.germ_res]
  · delta fromSpecStalk
    rw [← hV.map_fromSpec h₁ (homOfLE <| h₃.trans inf_le_right).op]; rw [← Spec.map_comp_assoc]; rw [TopCat.Presheaf.germ_res]

/--
Definition of `Scheme.fromSpecStalk` / `Scheme.fromSpecStalk` 的定义

English:
definition Scheme.fromSpecStalk
  signature: (X : Scheme) (x : X)
  body: (isAffineOpen_opensRange (X.affineCover.f (X.affineCover.idx x))).fromSpecStalk
    (X.affineCover.covers x)

@[simps over] noncomputable

中文:
定义 概形.fromSpecStalk
  签名: (X : 概形) (x : X)
  定义体: (isAffineOpen_opensRange (X.affineCover.f (X.affineCover.idx x))).fromSpecStalk
    (X.affineCover.covers x)

@[simps over] noncomputable

Depends on / 依赖: X.affineCover.covers, X.affineCover.f, X.affineCover.idx, affineCover, covers, fromSpecStalk, isAffineOpen_opensRange
-/
noncomputable def Scheme.fromSpecStalk (X : Scheme) (x : X) :
    Spec (X.presheaf.stalk x) ⟶ X :=
  (isAffineOpen_opensRange (X.affineCover.f (X.affineCover.idx x))).fromSpecStalk
    (X.affineCover.covers x)

@[simps over] noncomputable
instance (X : Scheme.{u}) (x : X) : (Spec (X.presheaf.stalk x)).Over X := ⟨X.fromSpecStalk x⟩

noncomputable
instance (X : Scheme.{u}) (x : X) : (Spec (X.presheaf.stalk x)).CanonicallyOver X where

@[simp]
/--
theorem `IsAffineOpen.fromSpecStalk_eq_fromSpecStalk` / 定理 `IsAffineOpen.fromSpecStalk_eq_fromSpecStalk`

English:
theorem IsAffineOpen.fromSpecStalk_eq_fromSpecStalk
  given: {x : X} (hxU : x in U)
  proof: fromSpecStalk_eq ..

中文:
定理 是仿射开集.fromSpecStalk_eq_fromSpecStalk
  条件: {x : X} (hxU : x in U)
  证明: fromSpecStalk_eq ..

Depends on / 依赖: fromSpecStalk_eq
-/
theorem IsAffineOpen.fromSpecStalk_eq_fromSpecStalk {x : X} (hxU : x in U) :
    hU.fromSpecStalk hxU = X.fromSpecStalk x := fromSpecStalk_eq ..

/--
Instance `IsAffineOpen.fromSpecStalk_isPreimmersion` / 实例 `IsAffineOpen.fromSpecStalk_isPreimmersion`

English:
instance IsAffineOpen.fromSpecStalk_isPreimmersion
  signature: {X : Scheme.{u}} {U : Opens X}
  body: by
  dsimp [IsAffineOpen.fromSpecStalk]
  have : IsPreimmersion (Spec.map (X.presheaf.germ U x hx)) :=
    letI : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hx).hom.toAlgebra
    haveI := hU.isLocalization_stalk ⟨x, hx⟩
    IsPreimmersion.of_isLocalization (R := Γ(X, U)) (S := X.pr

中文:
实例 是仿射开集.fromSpecStalk_isPreimmersion
  签名: {X : 概形.{u}} {U : Opens X}
  定义体: by
  dsimp [IsAffineOpen.fromSpecStalk]
  have : IsPreimmersion (Spec.map (X.presheaf.germ U x hx)) :=
    letI : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hx).hom.toAlgebra
    haveI := hU.isLocalization_stalk ⟨x, hx⟩
    IsPreimmersion.of_isLocalization (R := Γ(X, U)) (S := X.pr

Depends on / 依赖: Algebra, IsAffineOpen, IsAffineOpen.fromSpecStalk, IsPreimmersion, IsPreimmersion.comp, IsPreimmersion.of_isLocalization, Spec.map, X.presheaf.germ, X.presheaf.stalk, asIdeal, asIdeal.primeCompl, fromSpecStalk, hU.isLocalization_stalk, hU.primeIdealOf, hom.toAlgebra, isLocalization_stalk, of_isLocalization, presheaf, primeCompl, primeIdealOf
-/
instance IsAffineOpen.fromSpecStalk_isPreimmersion {X : Scheme.{u}} {U : Opens X}
    (hU : IsAffineOpen U) (x : X) (hx : x in U) : IsPreimmersion (hU.fromSpecStalk hx) := by
  dsimp [IsAffineOpen.fromSpecStalk]
  have : IsPreimmersion (Spec.map (X.presheaf.germ U x hx)) :=
    letI : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hx).hom.toAlgebra
    haveI := hU.isLocalization_stalk ⟨x, hx⟩
    IsPreimmersion.of_isLocalization (R := Γ(X, U)) (S := X.presheaf.stalk x)
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
  apply IsPreimmersion.comp

instance {X : Scheme.{u}} (x : X) : IsPreimmersion (X.fromSpecStalk x) :=
  IsAffineOpen.fromSpecStalk_isPreimmersion _ _ _

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `IsAffineOpen.fromSpecStalk_closedPoint` / 引理 `IsAffineOpen.fromSpecStalk_closedPoint`

English:
lemma IsAffineOpen.fromSpecStalk_closedPoint
  statement: {U : Opens X} (hU : IsAffineOpen U)
  proof: by
  rw [IsAffineOpen.fromSpecStalk]; rw [Scheme.Hom.comp_apply]
  rw [← hU.primeIdealOf_eq_map_closedPoint ⟨x]; rw [hxU⟩]; rw [hU.fromSpec_primeIdealOf ⟨x]; rw [hxU⟩]

中文:
引理 是仿射开集.fromSpecStalk_closedPoint
  结论: {U : Opens X} (hU : 是仿射开集 U)
  证明: by
  rw [IsAffineOpen.fromSpecStalk]; rw [Scheme.Hom.comp_apply]
  rw [← hU.primeIdealOf_eq_map_closedPoint ⟨x]; rw [hxU⟩]; rw [hU.fromSpec_primeIdealOf ⟨x]; rw [hxU⟩]

Depends on / 依赖: IsAffineOpen, IsAffineOpen.fromSpecStalk, Scheme, Scheme.Hom.comp_apply, comp_apply, fromSpecStalk, fromSpec_primeIdealOf, hU.fromSpec_primeIdealOf, hU.primeIdealOf_eq_map_closedPoint, primeIdealOf_eq_map_closedPoint
-/
lemma IsAffineOpen.fromSpecStalk_closedPoint {U : Opens X} (hU : IsAffineOpen U)
    {x : X} (hxU : x in U) :
    hU.fromSpecStalk hxU (closedPoint (X.presheaf.stalk x)) = x := by
  rw [IsAffineOpen.fromSpecStalk]; rw [Scheme.Hom.comp_apply]
  rw [← hU.primeIdealOf_eq_map_closedPoint ⟨x]; rw [hxU⟩]; rw [hU.fromSpec_primeIdealOf ⟨x]; rw [hxU⟩]

namespace Scheme

@[simp]
/--
lemma `fromSpecStalk_closedPoint` / 引理 `fromSpecStalk_closedPoint`

English:
lemma fromSpecStalk_closedPoint
  given: {x : X}
  proof: IsAffineOpen.fromSpecStalk_closedPoint _ _

中文:
引理 fromSpecStalk_closedPoint
  条件: {x : X}
  证明: IsAffineOpen.fromSpecStalk_closedPoint _ _

Depends on / 依赖: IsAffineOpen, IsAffineOpen.fromSpecStalk_closedPoint, fromSpecStalk_closedPoint
-/
lemma fromSpecStalk_closedPoint {x : X} :
    X.fromSpecStalk x (closedPoint (X.presheaf.stalk x)) = x :=
  IsAffineOpen.fromSpecStalk_closedPoint _ _

set_option backward.isDefEq.respectTransparency false in
/--
lemma `fromSpecStalk_app` / 引理 `fromSpecStalk_app`

English:
lemma fromSpecStalk_app
  given: {x : X} (hxU : x in U)
  proof: by
  obtain ⟨_, ⟨V : X.Opens, hV, rfl⟩, hxV, hVU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    hxU U.2
  rw [← hV.fromSpecStalk_eq_fromSpecStalk hxV]; rw [IsAffineOpen.fromSpecStalk]; rw [Scheme.Hom.comp_app]; rw [hV.fromSpec_app_of_le _ hVU]; rw [← X.presheaf.germ_res (homOfLE hVU) x hxV]

中文:
引理 fromSpecStalk_app
  条件: {x : X} (hxU : x in U)
  证明: by
  obtain ⟨_, ⟨V : X.Opens, hV, rfl⟩, hxV, hVU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    hxU U.2
  rw [← hV.fromSpecStalk_eq_fromSpecStalk hxV]; rw [IsAffineOpen.fromSpecStalk]; rw [Scheme.Hom.comp_app]; rw [hV.fromSpec_app_of_le _ hVU]; rw [← X.presheaf.germ_res (homOfLE hVU) x hxV]

Depends on / 依赖: Category, Category.assoc, IsAffineOpen, IsAffineOpen.fromSpecStalk, Scheme, Scheme.Hom.comp_app, X.Opens, X.isBasis_affineOpens.exists_subset_of_mem_open, X.presheaf.germ_res, comp_app, exists_subset_of_mem_open, fromSpecStalk, fromSpecStalk_eq_fromSpecStalk, fromSpec_app_of_le, germ_res, hV.fromSpecStalk_eq_fromSpecStalk, hV.fromSpec_app_of_le, homOfLE, isBasis_affineOpens, presheaf
-/
lemma fromSpecStalk_app {x : X} (hxU : x in U) :
    (X.fromSpecStalk x).app U =
      X.presheaf.germ U x hxU ≫
        (ΓSpecIso (X.presheaf.stalk x)).inv ≫
          (Spec (X.presheaf.stalk x)).presheaf.map (homOfLE le_top).op := by
  obtain ⟨_, ⟨V : X.Opens, hV, rfl⟩, hxV, hVU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    hxU U.2
  rw [← hV.fromSpecStalk_eq_fromSpecStalk hxV]; rw [IsAffineOpen.fromSpecStalk]; rw [Scheme.Hom.comp_app]; rw [hV.fromSpec_app_of_le _ hVU]; rw [← X.presheaf.germ_res (homOfLE hVU) x hxV]
  simp [Category.assoc, ← ΓSpecIso_inv_naturality_assoc]

/--
lemma `fromSpecStalk_appTop` / 引理 `fromSpecStalk_appTop`

English:
lemma fromSpecStalk_appTop
  given: {x : X}
  proof: fromSpecStalk_app ..

中文:
引理 fromSpecStalk_appTop
  条件: {x : X}
  证明: fromSpecStalk_app ..

Depends on / 依赖: fromSpecStalk_app
-/
lemma fromSpecStalk_appTop {x : X} :
    (X.fromSpecStalk x).appTop =
      X.presheaf.germ ⊤ x trivial ≫
        (ΓSpecIso (X.presheaf.stalk x)).inv ≫
          (Spec (X.presheaf.stalk x)).presheaf.map (homOfLE le_top).op :=
  fromSpecStalk_app ..

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
lemma `SpecMap_stalkSpecializes_fromSpecStalk` / 引理 `SpecMap_stalkSpecializes_fromSpecStalk`

English:
lemma SpecMap_stalkSpecializes_fromSpecStalk
  given: {x y : X} (h : x ⤳ y)
  proof: by
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have hxU : x in U := h.mem_open U.2 hyU
  rw [← hU.fromSpecStalk_eq_fromSpecStalk hyU]; rw [← hU.fromSpecStalk_eq_fromSpecStalk hxU]; rw [IsAffineOpen.fromSpecStalk]; rw [IsAff

中文:
引理 SpecMap_stalkSpecializes_fromSpecStalk
  条件: {x y : X} (h : x ⤳ y)
  证明: by
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have hxU : x in U := h.mem_open U.2 hyU
  rw [← hU.fromSpecStalk_eq_fromSpecStalk hyU]; rw [← hU.fromSpecStalk_eq_fromSpecStalk hxU]; rw [IsAffineOpen.fromSpecStalk]; rw [IsAff

Depends on / 依赖: Category, Category.assoc, IsAffineOpen, IsAffineOpen.fromSpecStalk, Presheaf, Set.mem_univ, Spec.map_comp, TopCat, TopCat.Presheaf.germ_stalkSpecializes, X.isBasis_affineOpens.exists_subset_of_mem_open, exists_subset_of_mem_open, fromSpecStalk, fromSpecStalk_eq_fromSpecStalk, germ_stalkSpecializes, h.mem_open, hU.fromSpecStalk_eq_fromSpecStalk, isBasis_affineOpens, isOpen_univ, map_comp, mem_open
-/
lemma SpecMap_stalkSpecializes_fromSpecStalk {x y : X} (h : x ⤳ y) :
    Spec.map (X.presheaf.stalkSpecializes h) ≫ X.fromSpecStalk y = X.fromSpecStalk x := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have hxU : x in U := h.mem_open U.2 hyU
  rw [← hU.fromSpecStalk_eq_fromSpecStalk hyU]; rw [← hU.fromSpecStalk_eq_fromSpecStalk hxU]; rw [IsAffineOpen.fromSpecStalk]; rw [IsAffineOpen.fromSpecStalk]; rw [← Category.assoc]; rw [← Spec.map_comp]; rw [TopCat.Presheaf.germ_stalkSpecializes]

instance {x y : X} (h : x ⤳ y) : (Spec.map (X.presheaf.stalkSpecializes h)).IsOver X where

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
lemma `SpecMap_stalkMap_fromSpecStalk` / 引理 `SpecMap_stalkMap_fromSpecStalk`

English:
lemma SpecMap_stalkMap_fromSpecStalk
  given: {x}
  proof: by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    hxU (f ⁻¹ᵁ U).2
  rw [← hU.fromSpecStalk_eq_fromSpecStalk hxU]; rw [← hV.fromSpecS

中文:
引理 SpecMap_stalkMap_fromSpecStalk
  条件: {x}
  证明: by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    hxU (f ⁻¹ᵁ U).2
  rw [← hU.fromSpecStalk_eq_fromSpecStalk hxU]; rw [← hV.fromSpecS

Depends on / 依赖: IsAffineOpen, IsAffineOpen.fromSpecStalk, Scheme, Scheme.Hom.germ_stalkMap, Set.mem_univ, Spec.map_comp_assoc, X.isBasis_affineOpens.exists_subset_of_mem_open, X.presheaf.germ_res, Y.isBasis_affineOpens.exists_subset_of_mem_open, exists_subset_of_mem_open, fromSpecStalk, fromSpecStalk_eq_fromSpecStalk, germ_res, germ_stalkMap, hU.fromSpecStalk_eq_fromSpecStalk, hV.fromSpecStalk_eq_fromSpecStalk, isBasis_affineOpens, isOpen_univ, map_comp_assoc, mem_univ
-/
lemma SpecMap_stalkMap_fromSpecStalk {x} :
    Spec.map (f.stalkMap x) ≫ Y.fromSpecStalk _ = X.fromSpecStalk x ≫ f := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    hxU (f ⁻¹ᵁ U).2
  rw [← hU.fromSpecStalk_eq_fromSpecStalk hxU]; rw [← hV.fromSpecStalk_eq_fromSpecStalk hxV]; rw [IsAffineOpen.fromSpecStalk]; rw [← Spec.map_comp_assoc]; rw [Scheme.Hom.germ_stalkMap f _ x hxU]; rw [IsAffineOpen.fromSpecStalk]; rw [Spec.map_comp_assoc]; rw [← X.presheaf.germ_res (homOfLE hVU) x hxV]; rw [Spec.map_comp_assoc]; rw [Category.assoc]; rw [← Spec.map_comp_assoc (f.app _)]; rw [Hom.app_eq_appLE]; rw [Hom.appLE_map]; rw [IsAffineOpen.SpecMap_appLE_fromSpec]

.IsOver Y where instance [X.Over Y] {x} : Spec.map ((X ↘ Y).stalkMap x)

@[stacks 01J7]
/--
lemma `range_fromSpecStalk` / 引理 `range_fromSpecStalk`

English:
lemma range_fromSpecStalk
  given: {x : X}
  proof: by
  ext y
  constructor
  · rintro ⟨y, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint y).map (X.fromSpecStalk x).continuous).trans
      (specializes_of_eq fromSpecStalk_closedPoint)
  · rintro (hy : y ⤳ x)
    have := fromSpecStalk_closedPoint (x := y)
    rw [← SpecMap_stalkSpecializes_from

中文:
引理 range_fromSpecStalk
  条件: {x : X}
  证明: by
  ext y
  constructor
  · rintro ⟨y, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint y).map (X.fromSpecStalk x).continuous).trans
      (specializes_of_eq fromSpecStalk_closedPoint)
  · rintro (hy : y ⤳ x)
    have := fromSpecStalk_closedPoint (x := y)
    rw [← SpecMap_stalkSpecializes_from

Depends on / 依赖: IsLocalRing, IsLocalRing.specializes_closedPoint, SpecMap_stalkSpecializes_fromSpecStalk, X.fromSpecStalk, continuous, fromSpecStalk, fromSpecStalk_closedPoint, specializes_closedPoint, specializes_of_eq
-/
lemma range_fromSpecStalk {x : X} :
    Set.range (X.fromSpecStalk x) = { y | y ⤳ x } := by
  ext y
  constructor
  · rintro ⟨y, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint y).map (X.fromSpecStalk x).continuous).trans
      (specializes_of_eq fromSpecStalk_closedPoint)
  · rintro (hy : y ⤳ x)
    have := fromSpecStalk_closedPoint (x := y)
    rw [← SpecMap_stalkSpecializes_fromSpecStalk hy] at this
    exact ⟨_, this⟩

set_option backward.isDefEq.respectTransparency false in
/-- The canonical map `Spec 𝒪_{X, x} ⟶ U` given `x ∈ U ⊆ X`. -/
noncomputable
/--
Definition of `Opens.fromSpecStalkOfMem` / `Opens.fromSpecStalkOfMem` 的定义

English:
definition Opens.fromSpecStalkOfMem
  signature: {X : Scheme.{u}} (U : X.Opens) (x : X) (hxU : x in U)
  body: Spec.map (inv (U.ι.stalkMap ⟨x, hxU⟩)) ≫ U.toScheme.fromSpecStalk ⟨x, hxU⟩

中文:
定义 Opens.fromSpecStalkOfMem
  签名: {X : 概形.{u}} (U : X.Opens) (x : X) (hxU : x in U)
  定义体: Spec.map (inv (U.ι.stalkMap ⟨x, hxU⟩)) ≫ U.toScheme.fromSpecStalk ⟨x, hxU⟩

Depends on / 依赖: Spec.map, U.toScheme.fromSpecStalk, fromSpecStalk, stalkMap, toScheme
-/
def Opens.fromSpecStalkOfMem {X : Scheme.{u}} (U : X.Opens) (x : X) (hxU : x in U) :
    Spec (X.presheaf.stalk x) ⟶ U :=
  Spec.map (inv (U.ι.stalkMap ⟨x, hxU⟩)) ≫ U.toScheme.fromSpecStalk ⟨x, hxU⟩

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
lemma `Opens.fromSpecStalkOfMem_ι` / 引理 `Opens.fromSpecStalkOfMem_ι`

English:
lemma Opens.fromSpecStalkOfMem_ι
  given: {X : Scheme.{u}} (U : X.Opens) (x : X) (hxU : x in U)
  proof: by
  simp only [Opens.fromSpecStalkOfMem, Spec.map_inv, Category.assoc, IsIso.inv_comp_eq]
  exact (Scheme.SpecMap_stalkMap_fromSpecStalk U.ι (x := ⟨x, hxU⟩)).symm

中文:
引理 Opens.fromSpecStalkOfMem_ι
  条件: {X : 概形.{u}} (U : X.Opens) (x : X) (hxU : x in U)
  证明: by
  simp only [Opens.fromSpecStalkOfMem, Spec.map_inv, Category.assoc, IsIso.inv_comp_eq]
  exact (Scheme.SpecMap_stalkMap_fromSpecStalk U.ι (x := ⟨x, hxU⟩)).symm

Depends on / 依赖: Category, Category.assoc, IsIso.inv_comp_eq, Opens.fromSpecStalkOfMem, Scheme, Scheme.SpecMap_stalkMap_fromSpecStalk, Spec.map_inv, SpecMap_stalkMap_fromSpecStalk, fromSpecStalkOfMem, inv_comp_eq, map_inv
-/
lemma Opens.fromSpecStalkOfMem_ι {X : Scheme.{u}} (U : X.Opens) (x : X) (hxU : x in U) :
    U.fromSpecStalkOfMem x hxU ≫ U.ι = X.fromSpecStalk x := by
  simp only [Opens.fromSpecStalkOfMem, Spec.map_inv, Category.assoc, IsIso.inv_comp_eq]
  exact (Scheme.SpecMap_stalkMap_fromSpecStalk U.ι (x := ⟨x, hxU⟩)).symm

instance {X : Scheme.{u}} (U : X.Opens) (x : X) (hxU : x in U) :
    (U.fromSpecStalkOfMem x hxU).IsOver X where

@[reassoc]
/--
lemma `fromSpecStalk_toSpecΓ` / 引理 `fromSpecStalk_toSpecΓ`

English:
lemma fromSpecStalk_toSpecΓ
  given: (X : Scheme.{u}) (x : X)
  proof: by
  rw [Scheme.toSpecΓ_naturality]; rw [← SpecMap_ΓSpecIso_hom]; rw [← Spec.map_comp]; rw [Scheme.fromSpecStalk_appTop]
  simp

中文:
引理 fromSpecStalk_toSpecΓ
  条件: (X : 概形.{u}) (x : X)
  证明: by
  rw [Scheme.toSpecΓ_naturality]; rw [← SpecMap_ΓSpecIso_hom]; rw [← Spec.map_comp]; rw [Scheme.fromSpecStalk_appTop]
  simp

Depends on / 依赖: Scheme, Scheme.fromSpecStalk_appTop, Scheme.toSpec, Spec.map_comp, fromSpecStalk_appTop, map_comp
-/
lemma fromSpecStalk_toSpecΓ (X : Scheme.{u}) (x : X) :
    X.fromSpecStalk x ≫ X.toSpecΓ = Spec.map (X.presheaf.germ ⊤ x trivial) := by
  rw [Scheme.toSpecΓ_naturality]; rw [← SpecMap_ΓSpecIso_hom]; rw [← Spec.map_comp]; rw [Scheme.fromSpecStalk_appTop]
  simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `Opens.fromSpecStalkOfMem_toSpecΓ` / 引理 `Opens.fromSpecStalkOfMem_toSpecΓ`

English:
lemma Opens.fromSpecStalkOfMem_toSpecΓ
  given: {X : Scheme.{u}} (U : X.Opens) (x : X) (hxU : x in U)
  proof: by
  rw [fromSpecStalkOfMem]; rw [Opens.toSpecΓ]; rw [Category.assoc]; rw [fromSpecStalk_toSpecΓ_assoc]; rw [← Spec.map_comp]; rw [← Spec.map_comp]
  congr 1
  rw [IsIso.comp_inv_eq]; rw [Iso.inv_comp_eq]
  erw [Hom.germ_stalkMap U.ι U ⟨x, hxU⟩]
  rw [Opens.ι_app]; rw [Opens.topIso_hom]; rw [← Funct

中文:
引理 Opens.fromSpecStalkOfMem_toSpecΓ
  条件: {X : 概形.{u}} (U : X.Opens) (x : X) (hxU : x in U)
  证明: by
  rw [fromSpecStalkOfMem]; rw [Opens.toSpecΓ]; rw [Category.assoc]; rw [fromSpecStalk_toSpecΓ_assoc]; rw [← Spec.map_comp]; rw [← Spec.map_comp]
  congr 1
  rw [IsIso.comp_inv_eq]; rw [Iso.inv_comp_eq]
  erw [Hom.germ_stalkMap U.ι U ⟨x, hxU⟩]
  rw [Opens.ι_app]; rw [Opens.topIso_hom]; rw [← Funct

Depends on / 依赖: Category, Category.assoc, Functor, Functor.map_comp_assoc, Hom.germ_stalkMap, IsIso.comp_inv_eq, Iso.inv_comp_eq, Opens.toSpec, Opens.topIso_hom, Spec.map_comp, U.toScheme.presheaf.germ_res, comp_inv_eq, fromSpecStalkOfMem, germ_res, germ_stalkMap, homOfLE, inv_comp_eq, le_top, map_comp, map_comp_assoc
-/
lemma Opens.fromSpecStalkOfMem_toSpecΓ {X : Scheme.{u}} (U : X.Opens) (x : X) (hxU : x in U) :
    U.fromSpecStalkOfMem x hxU ≫ U.toSpecΓ = Spec.map (X.presheaf.germ U x hxU) := by
  rw [fromSpecStalkOfMem]; rw [Opens.toSpecΓ]; rw [Category.assoc]; rw [fromSpecStalk_toSpecΓ_assoc]; rw [← Spec.map_comp]; rw [← Spec.map_comp]
  congr 1
  rw [IsIso.comp_inv_eq]; rw [Iso.inv_comp_eq]
  erw [Hom.germ_stalkMap U.ι U ⟨x, hxU⟩]
  rw [Opens.ι_app]; rw [Opens.topIso_hom]; rw [← Functor.map_comp_assoc]
  exact (U.toScheme.presheaf.germ_res (homOfLE le_top) ⟨x, hxU⟩ (U := U.ι ⁻¹ᵁ U) hxU).symm

end Scheme

section Spec

variable (R : CommRingCat) (x)

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `Spec.fromSpecStalk_eq` / 引理 `Spec.fromSpecStalk_eq`

English:
lemma Spec.fromSpecStalk_eq
  proof: by
  rw [← (isAffineOpen_top (Spec R)).fromSpecStalk_eq_fromSpecStalk (x := x) trivial]; rw [IsAffineOpen.fromSpecStalk]; rw [IsAffineOpen.fromSpec_top]; rw [Scheme.isoSpec_Spec_inv]; rw [← Spec.map_comp]

中文:
引理 Spec.fromSpecStalk_eq
  证明: by
  rw [← (isAffineOpen_top (Spec R)).fromSpecStalk_eq_fromSpecStalk (x := x) trivial]; rw [IsAffineOpen.fromSpecStalk]; rw [IsAffineOpen.fromSpec_top]; rw [Scheme.isoSpec_Spec_inv]; rw [← Spec.map_comp]

Depends on / 依赖: IsAffineOpen, IsAffineOpen.fromSpecStalk, IsAffineOpen.fromSpec_top, Scheme, Scheme.isoSpec_Spec_inv, Spec.map_comp, fromSpecStalk, fromSpecStalk_eq_fromSpecStalk, fromSpec_top, isAffineOpen_top, isoSpec_Spec_inv, map_comp
-/
lemma Spec.fromSpecStalk_eq :
    (Spec R).fromSpecStalk x =
      Spec.map ((Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.germ ⊤ x trivial) := by
  rw [← (isAffineOpen_top (Spec R)).fromSpecStalk_eq_fromSpecStalk (x := x) trivial]; rw [IsAffineOpen.fromSpecStalk]; rw [IsAffineOpen.fromSpec_top]; rw [Scheme.isoSpec_Spec_inv]; rw [← Spec.map_comp]

-- This is not a simp lemma to respect the abstraction boundaries
/--
lemma `Spec.fromSpecStalk_eq'` / 引理 `Spec.fromSpecStalk_eq'`

English:
lemma Spec.fromSpecStalk_eq'
  statement: (Spec R).fromSpecStalk x = Spec.map (StructureSheaf.toStalk R _)
  proof: Spec.fromSpecStalk_eq _ _

@[deprecated (since := "2026-02-05")] alias Scheme.Spec_fromSpecStalk := Spec.fromSpecStalk_eq
@[deprecated (since := "2026-02-05")] alias Scheme.Spec_fromSpecStalk' := Spec.fromSpecStalk_eq'

中文:
引理 Spec.fromSpecStalk_eq'
  结论: (Spec R).fromSpecStalk x = Spec.map (StructureSheaf.toStalk R _)
  证明: Spec.fromSpecStalk_eq _ _

@[deprecated (since := "2026-02-05")] alias Scheme.Spec_fromSpecStalk := Spec.fromSpecStalk_eq
@[deprecated (since := "2026-02-05")] alias Scheme.Spec_fromSpecStalk' := Spec.fromSpecStalk_eq'

Depends on / 依赖: Spec.fromSpecStalk_eq, fromSpecStalk_eq
-/
lemma Spec.fromSpecStalk_eq' : (Spec R).fromSpecStalk x = Spec.map (StructureSheaf.toStalk R _) :=
  Spec.fromSpecStalk_eq _ _

@[deprecated (since := "2026-02-05")] alias Scheme.Spec_fromSpecStalk := Spec.fromSpecStalk_eq
@[deprecated (since := "2026-02-05")] alias Scheme.Spec_fromSpecStalk' := Spec.fromSpecStalk_eq'

end Spec

end fromSpecStalk

variable (R : CommRingCat.{u}) [IsLocalRing R]

section stalkClosedPointIso

/-- For a local ring `(R, 𝔪)`,
this is the isomorphism between the stalk of `Spec R` at `𝔪` and `R`. -/
noncomputable
/--
Definition of `stalkClosedPointIso` / `stalkClosedPointIso` 的定义

English:
definition stalkClosedPointIso
  signature: :
  body: Spec.stalkIso _ _ ≪≫ (IsLocalization.atUnits R
      (closedPoint R).asIdeal.primeCompl fun _ => not_not.mp).toRingEquiv.toCommRingCatIso.symm

中文:
定义 stalkClosedPointIso
  签名: :
  定义体: Spec.stalkIso _ _ ≪≫ (IsLocalization.atUnits R
      (closedPoint R).asIdeal.primeCompl fun _ => not_not.mp).toRingEquiv.toCommRingCatIso.symm

Depends on / 依赖: IsLocalization, IsLocalization.atUnits, Spec.stalkIso, asIdeal, asIdeal.primeCompl, atUnits, closedPoint, not_not, not_not.mp, primeCompl, stalkIso, toCommRingCatIso, toRingEquiv, toRingEquiv.toCommRingCatIso.symm
-/
def stalkClosedPointIso :
    (Spec R).presheaf.stalk (closedPoint R) ≅ R :=
  Spec.stalkIso _ _ ≪≫ (IsLocalization.atUnits R
      (closedPoint R).asIdeal.primeCompl fun _ => not_not.mp).toRingEquiv.toCommRingCatIso.symm

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `stalkClosedPointIso_inv` / 引理 `stalkClosedPointIso_inv`

English:
lemma stalkClosedPointIso_inv
  proof: by
  ext x
  exact (StructureSheaf.stalkIso _ _).commutes _

中文:
引理 stalkClosedPointIso_inv
  证明: by
  ext x
  exact (StructureSheaf.stalkIso _ _).commutes _

Depends on / 依赖: StructureSheaf, StructureSheaf.stalkIso, commutes, stalkIso
-/
lemma stalkClosedPointIso_inv :
    (stalkClosedPointIso R).inv = StructureSheaf.toStalk R _ := by
  ext x
  exact (StructureSheaf.stalkIso _ _).commutes _

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `ΓSpecIso_hom_stalkClosedPointIso_inv` / 引理 `ΓSpecIso_hom_stalkClosedPointIso_inv`

English:
lemma ΓSpecIso_hom_stalkClosedPointIso_inv
  proof: by
  rw [stalkClosedPointIso_inv]; rw [← Iso.eq_inv_comp]
  rfl

@[reassoc (attr := simp)]

中文:
引理 ΓSpecIso_hom_stalkClosedPointIso_inv
  证明: by
  rw [stalkClosedPointIso_inv]; rw [← Iso.eq_inv_comp]
  rfl

@[reassoc (attr := simp)]

Depends on / 依赖: Iso.eq_inv_comp, eq_inv_comp, stalkClosedPointIso_inv
-/
lemma ΓSpecIso_hom_stalkClosedPointIso_inv :
    (Scheme.ΓSpecIso R).hom ≫ (stalkClosedPointIso R).inv =
      (Spec R).presheaf.germ ⊤ (closedPoint _) trivial := by
  rw [stalkClosedPointIso_inv]; rw [← Iso.eq_inv_comp]
  rfl

@[reassoc (attr := simp)]
/--
lemma `germ_stalkClosedPointIso_hom` / 引理 `germ_stalkClosedPointIso_hom`

English:
lemma germ_stalkClosedPointIso_hom
  proof: by
  rw [← ΓSpecIso_hom_stalkClosedPointIso_inv]; rw [Category.assoc]; rw [Iso.inv_hom_id]; rw [Category.comp_id]

中文:
引理 germ_stalkClosedPointIso_hom
  证明: by
  rw [← ΓSpecIso_hom_stalkClosedPointIso_inv]; rw [Category.assoc]; rw [Iso.inv_hom_id]; rw [Category.comp_id]

Depends on / 依赖: Category, Category.assoc, Category.comp_id, Iso.inv_hom_id, comp_id, inv_hom_id
-/
lemma germ_stalkClosedPointIso_hom :
    (Spec R).presheaf.germ ⊤ (closedPoint _) trivial ≫ (stalkClosedPointIso R).hom =
      (Scheme.ΓSpecIso R).hom := by
  rw [← ΓSpecIso_hom_stalkClosedPointIso_inv]; rw [Category.assoc]; rw [Iso.inv_hom_id]; rw [Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `Spec_stalkClosedPointIso` / 引理 `Spec_stalkClosedPointIso`

English:
lemma Spec_stalkClosedPointIso
  proof: by
  rw [stalkClosedPointIso_inv]; rw [Spec.fromSpecStalk_eq']

中文:
引理 Spec_stalkClosedPointIso
  证明: by
  rw [stalkClosedPointIso_inv]; rw [Spec.fromSpecStalk_eq']

Depends on / 依赖: Spec.fromSpecStalk_eq, fromSpecStalk_eq, stalkClosedPointIso_inv
-/
lemma Spec_stalkClosedPointIso :
    Spec.map (stalkClosedPointIso R).inv = (Spec R).fromSpecStalk (closedPoint R) := by
  rw [stalkClosedPointIso_inv]; rw [Spec.fromSpecStalk_eq']

end stalkClosedPointIso

section stalkClosedPointTo

variable {R} (f : Spec R ⟶ X)

namespace Scheme

/--
Given a local ring `(R, 𝔪)` and a morphism `f : Spec R ⟶ X`,
they induce a (local) ring homomorphism `φ : 𝒪_{X, f 𝔪} ⟶ R`.

This is inverse to `φ ↦ Spec.map φ ≫ X.fromSpecStalk (f 𝔪)`. See `SpecToEquivOfLocalRing`.
-/
noncomputable
/--
Definition of `stalkClosedPointTo` / `stalkClosedPointTo` 的定义

English:
definition stalkClosedPointTo
  signature: :
  body: f.stalkMap (closedPoint R) ≫ (stalkClosedPointIso R).hom

中文:
定义 stalkClosedPointTo
  签名: :
  定义体: f.stalkMap (closedPoint R) ≫ (stalkClosedPointIso R).hom

Depends on / 依赖: closedPoint, f.stalkMap, stalkClosedPointIso, stalkMap
-/
def stalkClosedPointTo :
    X.presheaf.stalk (f (closedPoint R)) ⟶ R :=
  f.stalkMap (closedPoint R) ≫ (stalkClosedPointIso R).hom

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `isLocalHom_stalkClosedPointTo` / 实例 `isLocalHom_stalkClosedPointTo`

English:
instance isLocalHom_stalkClosedPointTo
  signature: :
  body: inferInstanceAs IsLocalHom (f.stalkMap (closedPoint R) ≫ (stalkClosedPointIso R).hom).hom

中文:
实例 isLocalHom_stalkClosedPointTo
  签名: :
  定义体: inferInstanceAs IsLocalHom (f.stalkMap (closedPoint R) ≫ (stalkClosedPointIso R).hom).hom

Depends on / 依赖: IsLocalHom, closedPoint, f.stalkMap, stalkClosedPointIso, stalkMap
-/
instance isLocalHom_stalkClosedPointTo :
    IsLocalHom (stalkClosedPointTo f).hom :=
inferInstanceAs IsLocalHom (f.stalkMap (closedPoint R) ≫ (stalkClosedPointIso R).hom).hom

/--
Instance `isLocalHom_stalkClosedPointTo'` / 实例 `isLocalHom_stalkClosedPointTo'`

English:
instance isLocalHom_stalkClosedPointTo'
  signature: {R : Type u} [CommRing R] [IsLocalRing R]
  body: isLocalHom_stalkClosedPointTo f

中文:
实例 isLocalHom_stalkClosedPointTo'
  签名: {R : 类型u} [交换环 R] [是局部环 R]
  定义体: isLocalHom_stalkClosedPointTo f

Depends on / 依赖: isLocalHom_stalkClosedPointTo
-/
instance isLocalHom_stalkClosedPointTo' {R : Type u} [CommRing R] [IsLocalRing R]
    (f : Spec (.of R) ⟶ X) :
    IsLocalHom (stalkClosedPointTo f).hom :=
  isLocalHom_stalkClosedPointTo f

/--
lemma `preimage_eq_top_of_closedPoint_mem` / 引理 `preimage_eq_top_of_closedPoint_mem`

English:
lemma preimage_eq_top_of_closedPoint_mem
  proof: IsLocalRing.closed_point_mem_iff.mp hU

中文:
引理 preimage_eq_top_of_closedPoint_mem
  证明: IsLocalRing.closed_point_mem_iff.mp hU

Depends on / 依赖: IsLocalRing, IsLocalRing.closed_point_mem_iff.mp, closed_point_mem_iff
-/
lemma preimage_eq_top_of_closedPoint_mem
    {U : Opens X} (hU : f (closedPoint R) in U) : f ⁻¹ᵁ U = ⊤ :=
  IsLocalRing.closed_point_mem_iff.mp hU

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `stalkClosedPointTo_comp` / 引理 `stalkClosedPointTo_comp`

English:
lemma stalkClosedPointTo_comp
  given: (g : X ⟶ Y)
  proof: by
  rw [stalkClosedPointTo]; rw [Scheme.Hom.stalkMap_comp]
  exact Category.assoc _ _ _

中文:
引理 stalkClosedPointTo_comp
  条件: (g : X ⟶ Y)
  证明: by
  rw [stalkClosedPointTo]; rw [Scheme.Hom.stalkMap_comp]
  exact Category.assoc _ _ _

Depends on / 依赖: Category, Category.assoc, Scheme, Scheme.Hom.stalkMap_comp, stalkClosedPointTo, stalkMap_comp
-/
lemma stalkClosedPointTo_comp (g : X ⟶ Y) :
    stalkClosedPointTo (f ≫ g) = g.stalkMap _ ≫ stalkClosedPointTo f := by
  rw [stalkClosedPointTo]; rw [Scheme.Hom.stalkMap_comp]
  exact Category.assoc _ _ _

set_option backward.isDefEq.respectTransparency false in
/--
lemma `germ_stalkClosedPointTo_Spec` / 引理 `germ_stalkClosedPointTo_Spec`

English:
lemma germ_stalkClosedPointTo_Spec
  given: {R S : CommRingCat} [IsLocalRing S] (φ : R ⟶ S)
  proof: by
  rw [stalkClosedPointTo]; rw [Scheme.Hom.germ_stalkMap_assoc]; rw [← Iso.inv_comp_eq]; rw [← ΓSpecIso_inv_naturality_assoc]
  simp_rw [Opens.map_top]
  rw [germ_stalkClosedPointIso_hom]; rw [Iso.inv_hom_id]; rw [Category.comp_id]

中文:
引理 germ_stalkClosedPointTo_Spec
  条件: {R S : 交换环范畴} [是局部环 S] (φ : R ⟶ S)
  证明: by
  rw [stalkClosedPointTo]; rw [Scheme.Hom.germ_stalkMap_assoc]; rw [← Iso.inv_comp_eq]; rw [← ΓSpecIso_inv_naturality_assoc]
  simp_rw [Opens.map_top]
  rw [germ_stalkClosedPointIso_hom]; rw [Iso.inv_hom_id]; rw [Category.comp_id]

Depends on / 依赖: Category, Category.comp_id, Iso.inv_comp_eq, Iso.inv_hom_id, Opens.map_top, Scheme, Scheme.Hom.germ_stalkMap_assoc, comp_id, germ_stalkClosedPointIso_hom, germ_stalkMap_assoc, inv_comp_eq, inv_hom_id, map_top, simp_rw, stalkClosedPointTo
-/
lemma germ_stalkClosedPointTo_Spec {R S : CommRingCat} [IsLocalRing S] (φ : R ⟶ S) :
    (Spec R).presheaf.germ ⊤ _ trivial ≫ stalkClosedPointTo (Spec.map φ) =
      (ΓSpecIso R).hom ≫ φ := by
  rw [stalkClosedPointTo]; rw [Scheme.Hom.germ_stalkMap_assoc]; rw [← Iso.inv_comp_eq]; rw [← ΓSpecIso_inv_naturality_assoc]
  simp_rw [Opens.map_top]
  rw [germ_stalkClosedPointIso_hom]; rw [Iso.inv_hom_id]; rw [Category.comp_id]

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/--
lemma `germ_stalkClosedPointTo` / 引理 `germ_stalkClosedPointTo`

English:
lemma germ_stalkClosedPointTo
  given: (U : Opens X) (hU : f (closedPoint R) in U)
  proof: by
  rw [stalkClosedPointTo]; rw [Scheme.Hom.germ_stalkMap_assoc]; rw [Iso.trans_hom]
  congr 1
  rw [← Iso.eq_comp_inv]; rw [Category.assoc]; rw [ΓSpecIso_hom_stalkClosedPointIso_inv]
  simp only [Functor.mapIso_hom, Iso.op_hom, eqToIso.hom,
    TopCat.Presheaf.germ_res]

中文:
引理 germ_stalkClosedPointTo
  条件: (U : Opens X) (hU : f (closedPoint R) in U)
  证明: by
  rw [stalkClosedPointTo]; rw [Scheme.Hom.germ_stalkMap_assoc]; rw [Iso.trans_hom]
  congr 1
  rw [← Iso.eq_comp_inv]; rw [Category.assoc]; rw [ΓSpecIso_hom_stalkClosedPointIso_inv]
  simp only [Functor.mapIso_hom, Iso.op_hom, eqToIso.hom,
    TopCat.Presheaf.germ_res]

Depends on / 依赖: Category, Category.assoc, Functor, Functor.mapIso_hom, Iso.eq_comp_inv, Iso.op_hom, Iso.trans_hom, Presheaf, Scheme, Scheme.Hom.germ_stalkMap_assoc, TopCat, TopCat.Presheaf.germ_res, eqToIso, eqToIso.hom, eq_comp_inv, germ_res, germ_stalkMap_assoc, mapIso_hom, op_hom, stalkClosedPointTo
-/
lemma germ_stalkClosedPointTo (U : Opens X) (hU : f (closedPoint R) in U) :
    X.presheaf.germ U _ hU ≫ stalkClosedPointTo f = f.app U ≫
      ((Spec R).presheaf.mapIso (eqToIso (preimage_eq_top_of_closedPoint_mem f hU).symm).op ≪≫
        ΓSpecIso R).hom := by
  rw [stalkClosedPointTo]; rw [Scheme.Hom.germ_stalkMap_assoc]; rw [Iso.trans_hom]
  congr 1
  rw [← Iso.eq_comp_inv]; rw [Category.assoc]; rw [ΓSpecIso_hom_stalkClosedPointIso_inv]
  simp only [Functor.mapIso_hom, Iso.op_hom, eqToIso.hom,
    TopCat.Presheaf.germ_res]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `germ_stalkClosedPointTo_Spec_fromSpecStalk` / 引理 `germ_stalkClosedPointTo_Spec_fromSpecStalk`

English:
lemma germ_stalkClosedPointTo_Spec_fromSpecStalk
  proof: by
  have : (Spec.map f ≫ X.fromSpecStalk x) (closedPoint R) = x := by
    rw [Hom.comp_apply]; rw [Spec_closedPoint]; rw [fromSpecStalk_closedPoint]
  have : x in U := this ▸ hU
  simp only [germ_stalkClosedPointTo, Hom.comp_app,
    fromSpecStalk_app (X := X) (x := x) this, Category.assoc, Iso.tra

中文:
引理 germ_stalkClosedPointTo_Spec_fromSpecStalk
  证明: by
  have : (Spec.map f ≫ X.fromSpecStalk x) (closedPoint R) = x := by
    rw [Hom.comp_apply]; rw [Spec_closedPoint]; rw [fromSpecStalk_closedPoint]
  have : x in U := this ▸ hU
  simp only [germ_stalkClosedPointTo, Hom.comp_app,
    fromSpecStalk_app (X := X) (x := x) this, Category.assoc, Iso.tra

Depends on / 依赖: Category, Category.assoc, Functor, Functor.mapIso_hom, Hom.appLE_map_assoc, Hom.comp_app, Hom.comp_apply, Hom.map_appLE_assoc, Iso.inv_h, Iso.trans_hom, Opens.map_top, Spec.map, Spec_closedPoint, X.fromSpecStalk, appLE_map_assoc, app_eq_appLE, closedPoint, comp_app, comp_apply, fromSpecStalk
-/
lemma germ_stalkClosedPointTo_Spec_fromSpecStalk
    {x : X} (f : X.presheaf.stalk x ⟶ R) [IsLocalHom f.hom] (U : Opens X) (hU) :
    X.presheaf.germ U _ hU ≫ stalkClosedPointTo (Spec.map f ≫ X.fromSpecStalk x) =
      X.presheaf.germ U x (by simpa using hU) ≫ f := by
  have : (Spec.map f ≫ X.fromSpecStalk x) (closedPoint R) = x := by
    rw [Hom.comp_apply]; rw [Spec_closedPoint]; rw [fromSpecStalk_closedPoint]
  have : x in U := this ▸ hU
  simp only [germ_stalkClosedPointTo, Hom.comp_app,
    fromSpecStalk_app (X := X) (x := x) this, Category.assoc, Iso.trans_hom, Functor.mapIso_hom,
      (Spec.map f).app_eq_appLE, Hom.appLE_map_assoc, Hom.map_appLE_assoc]
  simp_rw [← Opens.map_top (Spec.map f).base]
  rw [← (Spec.map f).app_eq_appLE]; rw [ΓSpecIso_naturality]; rw [Iso.inv_hom_id_assoc]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `stalkClosedPointTo_fromSpecStalk` / 引理 `stalkClosedPointTo_fromSpecStalk`

English:
lemma stalkClosedPointTo_fromSpecStalk
  given: (x : X)
  proof: by
  refine TopCat.Presheaf.stalk_hom_ext _ fun U hxU => ?_
  simp only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.germ_stalkSpecializes]
  have : X.fromSpecStalk x = Spec.map (𝟙 (X.presheaf.stalk x)) ≫ X.fromSpecStalk x := by simp
  convert! germ_stalkClosedPointTo_Spec_fromSpecStalk (𝟙 (X.pr

中文:
引理 stalkClosedPointTo_fromSpecStalk
  条件: (x : X)
  证明: by
  refine TopCat.Presheaf.stalk_hom_ext _ fun U hxU => ?_
  simp only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.germ_stalkSpecializes]
  have : X.fromSpecStalk x = Spec.map (𝟙 (X.presheaf.stalk x)) ≫ X.fromSpecStalk x := by simp
  convert! germ_stalkClosedPointTo_Spec_fromSpecStalk (𝟙 (X.pr

Depends on / 依赖: Presheaf, Spec.map, TopCat, TopCat.Presheaf.germ_stalkSpecializes, TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalk_hom_ext, X.fromSpecStalk, X.presheaf.stalk, convert, fromSpecStalk, germ_stalkClosedPointTo_Spec_fromSpecStalk, germ_stalkSpecializes, presheaf, stalkCongr_hom, stalk_hom_ext
-/
lemma stalkClosedPointTo_fromSpecStalk (x : X) :
    stalkClosedPointTo (X.fromSpecStalk x) =
      (X.presheaf.stalkCongr (by rw [fromSpecStalk_closedPoint]; rfl)).hom := by
  refine TopCat.Presheaf.stalk_hom_ext _ fun U hxU => ?_
  simp only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.germ_stalkSpecializes]
  have : X.fromSpecStalk x = Spec.map (𝟙 (X.presheaf.stalk x)) ≫ X.fromSpecStalk x := by simp
  convert! germ_stalkClosedPointTo_Spec_fromSpecStalk (𝟙 (X.presheaf.stalk x)) U hxU

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/--
lemma `Spec_stalkClosedPointTo_fromSpecStalk` / 引理 `Spec_stalkClosedPointTo_fromSpecStalk`

English:
lemma Spec_stalkClosedPointTo_fromSpecStalk
  proof: by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (f (closedPoint R))) isOpen_univ
  have := IsAffineOpen.SpecMap_appLE_fromSpec f hU (isAffineOpen_top _)
    (preimage_eq_top_of_closedPoint_mem f hxU).ge
  rw [IsAffineOpen.fromSpec_top]; rw [

中文:
引理 Spec_stalkClosedPointTo_fromSpecStalk
  证明: by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (f (closedPoint R))) isOpen_univ
  have := IsAffineOpen.SpecMap_appLE_fromSpec f hU (isAffineOpen_top _)
    (preimage_eq_top_of_closedPoint_mem f hxU).ge
  rw [IsAffineOpen.fromSpec_top]; rw [

Depends on / 依赖: IsAffineOpen, IsAffineOpen.SpecMap_appLE_fromSpec, IsAffineOpen.fromSpecStalk, IsAffineOpen.fromSpec_top, Iso.eq_inv_comp, Iso.trans_hom, Set.mem_univ, Spec.map_comp_assoc, SpecMap_appLE_fromSpec, X.isBasis_affineOpens.exists_subset_of_mem_open, closedPoint, eq_inv_comp, exists_subset_of_mem_open, fromSpecStalk, fromSpecStalk_eq_fromSpecStalk, fromSpec_top, germ_stalkClosedPointTo, hU.fromSpecStalk_eq_fromSpecStalk, isAffineOpen_top, isBasis_affineOpens
-/
lemma Spec_stalkClosedPointTo_fromSpecStalk :
    Spec.map (stalkClosedPointTo f) ≫ X.fromSpecStalk _ = f := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (f (closedPoint R))) isOpen_univ
  have := IsAffineOpen.SpecMap_appLE_fromSpec f hU (isAffineOpen_top _)
    (preimage_eq_top_of_closedPoint_mem f hxU).ge
  rw [IsAffineOpen.fromSpec_top]; rw [Iso.eq_inv_comp]; rw [isoSpec_Spec_hom] at this
  rw [← hU.fromSpecStalk_eq_fromSpecStalk hxU]; rw [IsAffineOpen.fromSpecStalk]; rw [← Spec.map_comp_assoc]; rw [germ_stalkClosedPointTo]
  simpa only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, Category.assoc,
    Hom.app_eq_appLE, Hom.appLE_map_assoc, Spec.map_comp_assoc]

end Scheme

end stalkClosedPointTo

variable {R}

omit [IsLocalRing R] in
/--
lemma `SpecToEquivOfLocalRing_eq_iff` / 引理 `SpecToEquivOfLocalRing_eq_iff`

English:
lemma SpecToEquivOfLocalRing_eq_iff
  proof: by
  constructor
  · rintro rfl; simp
  · obtain ⟨x₁, ⟨f₁, h₁⟩⟩ := f₁
    obtain ⟨x₂, ⟨f₂, h₂⟩⟩ := f₂
    rintro ⟨rfl : x₁ = x₂, e : f₁ = _⟩
    simp [e]

中文:
引理 SpecToEquivOfLocalRing_eq_iff
  证明: by
  constructor
  · rintro rfl; simp
  · obtain ⟨x₁, ⟨f₁, h₁⟩⟩ := f₁
    obtain ⟨x₂, ⟨f₂, h₂⟩⟩ := f₂
    rintro ⟨rfl : x₁ = x₂, e : f₁ = _⟩
    simp [e]
-/
lemma SpecToEquivOfLocalRing_eq_iff
    {f₁ f₂ : Σ x, { f : X.presheaf.stalk x ⟶ R // IsLocalHom f.hom }} :
    f₁ = f₂ ↔ exists h₁ : f₁.1 = f₂.1, f₁.2.1 =
      (X.presheaf.stalkCongr (by rw [h₁]; rfl)).hom ≫ f₂.2.1 := by
  constructor
  · rintro rfl; simp
  · obtain ⟨x₁, ⟨f₁, h₁⟩⟩ := f₁
    obtain ⟨x₂, ⟨f₂, h₂⟩⟩ := f₂
    rintro ⟨rfl : x₁ = x₂, e : f₁ = _⟩
    simp [e]

variable (X R)

set_option backward.isDefEq.respectTransparency.types false in
/--
Given a local ring `R` and scheme `X`, morphisms `Spec R ⟶ X` corresponds to pairs
`(x, f)` where `x : X` and `f : 𝒪_{X, x} ⟶ R` is a local ring homomorphism.
-/
@[simps]
noncomputable
/--
Definition of `SpecToEquivOfLocalRing` / `SpecToEquivOfLocalRing` 的定义

English:
definition SpecToEquivOfLocalRing
  signature: :
  body: ⟨f (closedPoint R), Scheme.stalkClosedPointTo f, inferInstance⟩
  invFun xf := Spec.map xf.2.1 ≫ X.fromSpecStalk xf.1
  left_inv := Scheme.Spec_stalkClosedPointTo_fromSpecStalk
  right_inv xf := by
    obtain ⟨x, ⟨f, hf⟩⟩ := xf
    symm
    refine SpecToEquivOfLocalRing_eq_iff.mpr ⟨?_, ?_⟩
    · sim

中文:
定义 SpecToEquivOfLocalRing
  签名: :
  定义体: ⟨f (closedPoint R), Scheme.stalkClosedPointTo f, inferInstance⟩
  invFun xf := Spec.map xf.2.1 ≫ X.fromSpecStalk xf.1
  left_inv := Scheme.Spec_stalkClosedPointTo_fromSpecStalk
  right_inv xf := by
    obtain ⟨x, ⟨f, hf⟩⟩ := xf
    symm
    refine SpecToEquivOfLocalRing_eq_iff.mpr ⟨?_, ?_⟩
    · sim

Depends on / 依赖: Scheme, Scheme.stalkClosedPointTo, closedPoint, stalkClosedPointTo
-/
def SpecToEquivOfLocalRing :
    (Spec R ⟶ X) ≃ Σ x, { f : X.presheaf.stalk x ⟶ R // IsLocalHom f.hom } where
  toFun f := ⟨f (closedPoint R), Scheme.stalkClosedPointTo f, inferInstance⟩
  invFun xf := Spec.map xf.2.1 ≫ X.fromSpecStalk xf.1
  left_inv := Scheme.Spec_stalkClosedPointTo_fromSpecStalk
  right_inv xf := by
    obtain ⟨x, ⟨f, hf⟩⟩ := xf
    symm
    refine SpecToEquivOfLocalRing_eq_iff.mpr ⟨?_, ?_⟩
    · simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply, Spec_closedPoint,
        Scheme.fromSpecStalk_closedPoint]
    · refine TopCat.Presheaf.stalk_hom_ext _ fun U hxU => ?_
      simp only [Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk,
        TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.germ_stalkSpecializes_assoc]

end AlgebraicGeometry
