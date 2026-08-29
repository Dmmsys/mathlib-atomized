/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.Ideal.IdempotentFG
public import Mathlib.RingTheory.RingHom.Unramified
public import Mathlib.RingTheory.Unramified.LocalRing

/-!
# Formally unramified morphisms

A morphism of schemes `f : X ⟶ Y` is formally unramified if for each affine `U ⊆ Y` and
`V ⊆ f ⁻¹' U`, the induced map `Γ(Y, U) ⟶ Γ(X, V)` is formally unramified.

We show that these properties are local, and are stable under compositions and base change.

-/

public section


noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v u

open AlgebraicGeometry

/--
Instance `Algebra.FormallyUnramified.isOpenImmersion_SpecMap_lmul` / 实例 `Algebra.FormallyUnramified.isOpenImmersion_SpecMap_lmul`

English:
instance Algebra.FormallyUnramified.isOpenImmersion_SpecMap_lmul
  signature: {R S : Type u} [CommRing R]
  body: by
  rw [isOpenImmersion_SpecMap_iff_of_surjective _ (fun x => ⟨1 otimesₜ x]; rw [by simp⟩)]
  apply (Ideal.isIdempotentElem_iff_of_fg _ (KaehlerDifferential.ideal_fg R S)).mp
  apply (Ideal.cotangent_subsingleton_iff _).mp
exact inferInstanceAs Subsingleton Ω[S⁄R]

中文:
实例 代数.形式非分歧.isOpenImmersion_SpecMap_lmul
  签名: {R S : 类型u} [交换环 R]
  定义体: by
  rw [isOpenImmersion_SpecMap_iff_of_surjective _ (fun x => ⟨1 otimesₜ x]; rw [by simp⟩)]
  apply (Ideal.isIdempotentElem_iff_of_fg _ (KaehlerDifferential.ideal_fg R S)).mp
  apply (Ideal.cotangent_subsingleton_iff _).mp
exact inferInstanceAs Subsingleton Ω[S⁄R]

Depends on / 依赖: Ideal.cotangent_subsingleton_iff, Ideal.isIdempotentElem_iff_of_fg, KaehlerDifferential, KaehlerDifferential.ideal_fg, Subsingleton, cotangent_subsingleton_iff, ideal_fg, isIdempotentElem_iff_of_fg, isOpenImmersion_SpecMap_iff_of_surjective, toRingHom
-/
instance Algebra.FormallyUnramified.isOpenImmersion_SpecMap_lmul {R S : Type u} [CommRing R]
    [CommRing S] [Algebra R S] [Algebra.FormallyUnramified R S] [Algebra.EssFiniteType R S] :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (TensorProduct.lmul' R (S := S)).toRingHom)) := by
  rw [isOpenImmersion_SpecMap_iff_of_surjective _ (fun x => ⟨1 otimesₜ x]; rw [by simp⟩)]
  apply (Ideal.isIdempotentElem_iff_of_fg _ (KaehlerDifferential.ideal_fg R S)).mp
  apply (Ideal.cotangent_subsingleton_iff _).mp
exact inferInstanceAs Subsingleton Ω[S⁄R]

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A morphism of schemes `f : X ⟶ Y` is formally unramified if for each affine `U ⊆ Y` and
`V ⊆ f ⁻¹' U`, The induced map `Γ(Y, U) ⟶ Γ(X, V)` is formally unramified.

See `FormallyUnramified.hom_ext` and `FormallyUnramified.of_hom_ext`
for the infinitesimal lifting criterion. -/
@[mk_iff]
/--
Definition of `FormallyUnramified` / `FormallyUnramified` 的定义

English:
class FormallyUnramified
  parameters: (f : X ⟶ Y)
  axioms and operations (1):
    - formallyUnramified_appLE((f)) : forall {U : Y.Opens} (_ : IsAffineOpen U) {V : X.Opens} (_ : IsAffineOpen V) (e : V <= f ⁻¹ᵁ U), (f.appLE U V e).hom.FormallyUnramified

中文:
类 形式非分歧
  参数: (f : X ⟶ Y)
  公理与运算 (1 个):
    - formallyUnramified_appLE((f)) : 对任意 {U : Y.Opens} (_ : 是仿射开集 U) {V : X.Opens} (_ : 是仿射开集 V) (e : V <= f ⁻¹ᵁ U), (f.appLE U V e).hom.形式非分歧

Depends on / 依赖: FormallyUnramified, FormallyUnramified.formallyUnramified_appLE, formallyUnramified_appLE
-/
class FormallyUnramified (f : X ⟶ Y) : Prop where
  formallyUnramified_appLE (f) :
    forall {U : Y.Opens} (_ : IsAffineOpen U) {V : X.Opens} (_ : IsAffineOpen V) (e : V <= f ⁻¹ᵁ U),
      (f.appLE U V e).hom.FormallyUnramified

alias Scheme.Hom.formallyUnramified_appLE := FormallyUnramified.formallyUnramified_appLE

@[deprecated (since := "2026-01-20")]
alias FormallyUnramified.formallyUnramified_of_affine_subset := Scheme.Hom.formallyUnramified_appLE

namespace FormallyUnramified

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasRingHomProperty @FormallyUnramified RingHom.FormallyUnramified
  body: RingHom.FormallyUnramified.propertyIsLocal
  eq_affineLocally' := by
    ext X Y f
    rw [formallyUnramified_iff]; rw [affineLocally_iff_forall_isAffineOpen]

中文:
实例 :
  签名: 有RingHomProperty @形式非分歧 环态射.形式非分歧
  定义体: RingHom.FormallyUnramified.propertyIsLocal
  eq_affineLocally' := by
    ext X Y f
    rw [formallyUnramified_iff]; rw [affineLocally_iff_forall_isAffineOpen]

Depends on / 依赖: FormallyUnramified, RingHom, RingHom.FormallyUnramified.propertyIsLocal, propertyIsLocal
-/
instance : HasRingHomProperty @FormallyUnramified RingHom.FormallyUnramified where
  isLocal_ringHomProperty := RingHom.FormallyUnramified.propertyIsLocal
  eq_affineLocally' := by
    ext X Y f
    rw [formallyUnramified_iff]; rw [affineLocally_iff_forall_isAffineOpen]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MorphismProperty.IsStableUnderComposition @FormallyUnramified
  body: HasRingHomProperty.stableUnderComposition RingHom.FormallyUnramified.stableUnderComposition

中文:
实例 :
  签名: MorphismProperty.是StableUnderComposition @形式非分歧
  定义体: HasRingHomProperty.stableUnderComposition RingHom.FormallyUnramified.stableUnderComposition

Depends on / 依赖: FormallyUnramified, HasRingHomProperty, HasRingHomProperty.stableUnderComposition, RingHom, RingHom.FormallyUnramified.stableUnderComposition, stableUnderComposition
-/
instance : MorphismProperty.IsStableUnderComposition @FormallyUnramified :=
  HasRingHomProperty.stableUnderComposition RingHom.FormallyUnramified.stableUnderComposition

set_option backward.isDefEq.respectTransparency.types false in
/-- `f : X ⟶ S` is formally unramified if `X ⟶ X ×ₛ X` is an open immersion.
In particular, monomorphisms (e.g. immersions) are formally unramified.
The converse is true if `f` is locally of finite type. -/
instance (priority := 900) [IsOpenImmersion (pullback.diagonal f)] : FormallyUnramified f := by
  wlog hY : exists R, Y = Spec R
  · rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @FormallyUnramified) Y.affineCover]
    intro i
    have inst : IsOpenImmersion (pullback.diagonal (pullback.snd f (Y.affineCover.f i))) :=
      MorphismProperty.pullback_snd (P := .diagonal @IsOpenImmersion) _ _ ‹_›
    exact this (pullback.snd _ _) ⟨_, rfl⟩
  obtain ⟨R, rfl⟩ := hY
  wlog hX : exists S, X = Spec S generalizing X
  · rw [IsZariskiLocalAtSource.iff_of_openCover (P := @FormallyUnramified) X.affineCover]
    intro i
    have inst : IsOpenImmersion (pullback.diagonal (X.affineCover.f i ≫ f)) :=
      MorphismProperty.comp_mem (.diagonal @IsOpenImmersion) _ _
        (inferInstanceAs (IsOpenImmersion _)) ‹_›
    exact this (_ ≫ _) ⟨_, rfl⟩
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl : Spec.map φ = f⟩ := Spec.homEquiv.symm.surjective f
  rw [HasRingHomProperty.Spec_iff (P := @FormallyUnramified)]
  algebraize [φ.hom]
  let F := (Algebra.TensorProduct.lmul' R (S := S)).toRingHom
  have hF : Function.Surjective F := fun x => ⟨.mk _ _ _ x 1, by simp [F]⟩
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom F)) := by
    rwa [← MorphismProperty.cancel_right_of_respectsIso (P := @IsOpenImmersion) _
      (pullbackSpecIso R S S).inv, ← AlgebraicGeometry.diagonal_SpecMap R S]
  obtain ⟨e, he, he'⟩ := (isOpenImmersion_SpecMap_iff_of_surjective _ hF).mp this
  refine ⟨subsingleton_of_forall_eq 0 fun x => ?_⟩
  obtain ⟨⟨x, hx⟩, rfl⟩ := Ideal.toCotangent_surjective _ x
  obtain ⟨x, rfl⟩ := Ideal.mem_span_singleton.mp (he'.le hx)
  refine (Ideal.toCotangent_eq_zero _ _).mpr ?_
  rw [pow_two]; rw [Subtype.coe_mk]; rw [← he]; rw [mul_assoc]
  exact Ideal.mul_mem_mul (he'.ge (Ideal.mem_span_singleton_self e)) hx

/--
theorem `of_comp` / 定理 `of_comp`

English:
theorem of_comp
  statement: {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: HasRingHomProperty.of_comp (fun {R S T _ _ _} f g H => by
    algebraize [f, g, g.comp f]
    exact Algebra.FormallyUnramified.of_restrictScalars R S T) ‹_›

中文:
定理 of_comp
  结论: {X Y Z : 概形} (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: HasRingHomProperty.of_comp (fun {R S T _ _ _} f g H => by
    algebraize [f, g, g.comp f]
    exact Algebra.FormallyUnramified.of_restrictScalars R S T) ‹_›

Depends on / 依赖: Algebra, Algebra.FormallyUnramified.of_restrictScalars, FormallyUnramified, HasRingHomProperty, HasRingHomProperty.of_comp, algebraize, g.comp, of_comp, of_restrictScalars
-/
theorem of_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [FormallyUnramified (f ≫ g)] : FormallyUnramified f :=
  HasRingHomProperty.of_comp (fun {R S T _ _ _} f g H => by
    algebraize [f, g, g.comp f]
    exact Algebra.FormallyUnramified.of_restrictScalars R S T) ‹_›

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MorphismProperty.IsMultiplicative @FormallyUnramified
  body: inferInstance

中文:
实例 :
  签名: MorphismProperty.是Multiplicative @形式非分歧
  定义体: inferInstance
-/
instance : MorphismProperty.IsMultiplicative @FormallyUnramified where
  id_mem _ := inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MorphismProperty.IsStableUnderBaseChange @FormallyUnramified
  body: HasRingHomProperty.isStableUnderBaseChange RingHom.FormallyUnramified.isStableUnderBaseChange

中文:
实例 :
  签名: MorphismProperty.是StableUnderBaseChange @形式非分歧
  定义体: HasRingHomProperty.isStableUnderBaseChange RingHom.FormallyUnramified.isStableUnderBaseChange

Depends on / 依赖: FormallyUnramified, HasRingHomProperty, HasRingHomProperty.isStableUnderBaseChange, RingHom, RingHom.FormallyUnramified.isStableUnderBaseChange, isStableUnderBaseChange
-/
instance : MorphismProperty.IsStableUnderBaseChange @FormallyUnramified :=
  HasRingHomProperty.isStableUnderBaseChange RingHom.FormallyUnramified.isStableUnderBaseChange

set_option backward.isDefEq.respectTransparency.types false in
open MorphismProperty in
/--
Instance `isOpenImmersion_diagonal` / 实例 `isOpenImmersion_diagonal`

English:
instance isOpenImmersion_diagonal
  signature: [FormallyUnramified f] [LocallyOfFiniteType f]
  body: by
  wlog hX : (exists S, X = Spec S) ∧ exists R, Y = Spec R
  · let 𝒰Y := Y.affineCover
    let 𝒰X (j : (Y.affineCover.pullback₁ f).I₀) :
        ((Y.affineCover.pullback₁ f).X j).OpenCover := Scheme.affineCover _
    apply IsZariskiLocalAtTarget.of_range_subset_iSup _
      (Scheme.Pullback.range_

中文:
实例 isOpenImmersion_diagonal
  签名: [形式非分歧 f] [局部有限型 f]
  定义体: by
  wlog hX : (exists S, X = Spec S) ∧ exists R, Y = Spec R
  · let 𝒰Y := Y.affineCover
    let 𝒰X (j : (Y.affineCover.pullback₁ f).I₀) :
        ((Y.affineCover.pullback₁ f).X j).OpenCover := Scheme.affineCover _
    apply IsZariskiLocalAtTarget.of_range_subset_iSup _
      (Scheme.Pullback.range_

Depends on / 依赖: FormallyUnramified, IsOpenImmersion, IsZariskiLocalAtTarget, IsZariskiLocalAtTarget.of_range_subset_iSup, OpenCover, Pullback, Scheme, Scheme.Pullback.diagonalRestrictIsoDiagonal, Scheme.Pullback.range_diagonal_subset_diagonalCoverDiagonalRange, Scheme.affineCover, Y.affineCover, Y.affineCover.pullback, affineCover, arrow_mk_iso_iff, diagonalRestrictIsoDiagonal, of_range_subset_iSup, pullback, pullback.snd, range_diagonal_subset_diagonalCoverDiagonalRange
-/
instance isOpenImmersion_diagonal [FormallyUnramified f] [LocallyOfFiniteType f] :
    IsOpenImmersion (pullback.diagonal f) := by
  wlog hX : (exists S, X = Spec S) ∧ exists R, Y = Spec R
  · let 𝒰Y := Y.affineCover
    let 𝒰X (j : (Y.affineCover.pullback₁ f).I₀) :
        ((Y.affineCover.pullback₁ f).X j).OpenCover := Scheme.affineCover _
    apply IsZariskiLocalAtTarget.of_range_subset_iSup _
      (Scheme.Pullback.range_diagonal_subset_diagonalCoverDiagonalRange f 𝒰Y 𝒰X)
    intro ⟨i, j⟩
    rw [arrow_mk_iso_iff (P := @IsOpenImmersion)
      (Scheme.Pullback.diagonalRestrictIsoDiagonal f 𝒰Y 𝒰X i j)]
    have hu : FormallyUnramified ((𝒰X i).f j ≫ pullback.snd f (𝒰Y.f i)) :=
      comp_mem _ _ _ inferInstance (pullback_snd _ _ inferInstance)
    have hfin : LocallyOfFiniteType ((𝒰X i).f j ≫ pullback.snd f (𝒰Y.f i)) :=
      comp_mem _ _ _ inferInstance (pullback_snd _ _ inferInstance)
    exact this _ ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩
  obtain ⟨⟨S, rfl⟩, R, rfl⟩ := hX
  obtain ⟨f, rfl⟩ := Spec.map_surjective f
  rw [HasRingHomProperty.Spec_iff (P := @FormallyUnramified)]; rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at *
  algebraize [f.hom]
  rw [show f = CommRingCat.ofHom (algebraMap R S) from rfl]; rw [diagonal_SpecMap R S]; rw [cancel_right_of_respectsIso (P := @IsOpenImmersion)]
  infer_instance

/--
lemma `stalkMap` / 引理 `stalkMap`

English:
lemma stalkMap
  given: [FormallyUnramified f] (x : X)
  statement: (f.stalkMap x).hom.FormallyUnramified
  proof: HasRingHomProperty.stalkMap
    (fun f hf p q =>
      RingHom.FormallyUnramified.holdsForLocalization.localRingHom
        RingHom.FormallyUnramified.stableUnderComposition
        RingHom.FormallyUnramified.isStableUnderBaseChange.localizationPreserves _ hf) ‹_› x

中文:
引理 stalkMap
  条件: [形式非分歧 f] (x : X)
  结论: (f.stalkMap x).hom.形式非分歧
  证明: HasRingHomProperty.stalkMap
    (fun f hf p q =>
      RingHom.FormallyUnramified.holdsForLocalization.localRingHom
        RingHom.FormallyUnramified.stableUnderComposition
        RingHom.FormallyUnramified.isStableUnderBaseChange.localizationPreserves _ hf) ‹_› x

Depends on / 依赖: FormallyUnramified, HasRingHomProperty, HasRingHomProperty.stalkMap, RingHom, RingHom.FormallyUnramified.holdsForLocalization.localRingHom, RingHom.FormallyUnramified.isStableUnderBaseChange.localizationPreserves, RingHom.FormallyUnramified.stableUnderComposition, holdsForLocalization, isStableUnderBaseChange, localRingHom, localizationPreserves, stableUnderComposition, stalkMap
-/
lemma stalkMap [FormallyUnramified f] (x : X) : (f.stalkMap x).hom.FormallyUnramified :=
  HasRingHomProperty.stalkMap
    (fun f hf p q =>
      RingHom.FormallyUnramified.holdsForLocalization.localRingHom
        RingHom.FormallyUnramified.stableUnderComposition
        RingHom.FormallyUnramified.isStableUnderBaseChange.localizationPreserves _ hf) ‹_› x

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [FormallyUnramified
  signature: f] [LocallyOfFiniteType f] (x
  body: (f.residueFieldMap x).hom.toAlgebra
    Algebra.IsSeparable (Y.residueField (f.base x)) (X.residueField x) := by
  algebraize [(f.stalkMap x).hom]
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
inferInstanceAs IsLocalHom (f.stalkMap x).hom
  suffices h : Algebra.Is

中文:
实例 [形式非分歧
  签名: f] [局部有限型 f] (x
  定义体: (f.residueFieldMap x).hom.toAlgebra
    Algebra.IsSeparable (Y.residueField (f.base x)) (X.residueField x) := by
  algebraize [(f.stalkMap x).hom]
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
inferInstanceAs IsLocalHom (f.stalkMap x).hom
  suffices h : Algebra.Is

Depends on / 依赖: Algebra, Algebra.IsSeparable, Algebra.algebra_ext, IsLocalHom, IsLocalRing, IsLocalRing.ResidueField, IsLocalRing.residue_su, IsSeparable, ResidueField, X.presheaf.stalk, X.residueField, Y.presheaf.stalk, Y.residueField, algebraMap, algebra_ext, algebraize, convert, f.base, f.residueFieldMap, f.stalkMap
-/
instance [FormallyUnramified f] [LocallyOfFiniteType f] (x : X) :
    letI : Algebra (Y.residueField (f.base x)) (X.residueField x) :=
      (f.residueFieldMap x).hom.toAlgebra
    Algebra.IsSeparable (Y.residueField (f.base x)) (X.residueField x) := by
  algebraize [(f.stalkMap x).hom]
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
inferInstanceAs IsLocalHom (f.stalkMap x).hom
  suffices h : Algebra.IsSeparable
      (IsLocalRing.ResidueField <| Y.presheaf.stalk (f x))
      (IsLocalRing.ResidueField <| X.presheaf.stalk x) by
    convert! h
    refine Algebra.algebra_ext _ _ fun x => ?_
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective x
    rfl
  have : Algebra.EssFiniteType (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := by
    rw [← RingHom.essFiniteType_algebraMap]; rw [RingHom.algebraMap_toAlgebra]
    exact LocallyOfFiniteType.stalkMap f x
  have : Algebra.FormallyUnramified (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := by
    rw [← RingHom.formallyUnramified_algebraMap]; rw [RingHom.algebraMap_toAlgebra]
    exact stalkMap f x
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/--
Given any commuting diagram
```
Z' --→ X
| |
↓ ↓
Z --→ Y
```
With `X ⟶ Y` formally unramified and `Z' ⟶ Z` an infinitesimal thickening, there exists at most
one arrow `Z ⟶ X` making the diagram commute.
-/
@[stacks 04F1]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  statement: {Z' Z : Scheme} (i : Z' ⟶ Z) (hi : IsNilpotent i.ker) [IsClosedImmersion i]
  proof: by
  have : IsDominant i := by
    obtain ⟨n, hn⟩ := hi
    rw [isDominant_iff]; rw [denseRange_iff_closure_range]; rw [← i.support_ker]; rw [← i.ker.support_pow (n + 1) (by simp)]; rw [pow_succ]; rw [hn]
    simp
  refine Scheme.hom_ext_of_forall _ _ fun x => ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :

中文:
引理 hom_ext
  结论: {Z' Z : 概形} (i : Z' ⟶ Z) (hi : 是幂零 i.ker) [是闭浸入 i]
  证明: by
  have : IsDominant i := by
    obtain ⟨n, hn⟩ := hi
    rw [isDominant_iff]; rw [denseRange_iff_closure_range]; rw [← i.support_ker]; rw [← i.ker.support_pow (n + 1) (by simp)]; rw [pow_succ]; rw [hn]
    simp
  refine Scheme.hom_ext_of_forall _ _ fun x => ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :
-/
protected lemma hom_ext {Z' Z : Scheme} (i : Z' ⟶ Z) (hi : IsNilpotent i.ker) [IsClosedImmersion i]
    (f : X ⟶ Y) [FormallyUnramified f]
    {g₁ g₂ : Z ⟶ X} (hig : i ≫ g₁ = i ≫ g₂) (hgf : g₁ ≫ f = g₂ ≫ f) : g₁ = g₂ := by
  have : IsDominant i := by
    obtain ⟨n, hn⟩ := hi
    rw [isDominant_iff]; rw [denseRange_iff_closure_range]; rw [← i.support_ker]; rw [← i.ker.support_pow (n + 1) (by simp)]; rw [pow_succ]; rw [hn]
    simp
  refine Scheme.hom_ext_of_forall _ _ fun x => ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f (g₁ x))) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU : V <= f ⁻¹ᵁ U⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (f ⁻¹ᵁ U).isOpen
  have : g₁.base = g₂.base := by ext x; obtain ⟨x, rfl⟩ := i.surjective x; exact congr($hig x)
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV : W <= _⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open
    (And.intro hxV (by simpa [← this])) (g₁ ⁻¹ᵁ V ⊓ g₂ ⁻¹ᵁ V).isOpen
  refine ⟨W, hxW, ?_⟩
  have := f.formallyUnramified_appLE hU hV hVU
  algebraize [(f.appLE U V hVU).hom,
    ((g₁ ≫ f).appLE U W (by grw [hWV, inf_le_left, hVU]; rfl)).hom]
  let ψ₁ : Γ(X, V) ->ₐ[Γ(Y, U)] Γ(Z, W) := ⟨(g₁.appLE _ _ (hWV.trans inf_le_left)).hom, fun r => by
    simp [RingHom.algebraMap_toAlgebra, ← CategoryTheory.comp_apply, -CommRingCat.hom_comp,
      Scheme.Hom.appLE_comp_appLE]⟩
  let ψ₂ : Γ(X, V) ->ₐ[Γ(Y, U)] Γ(Z, W) := ⟨(g₂.appLE _ _ (hWV.trans inf_le_right)).hom, fun r => by
    simp [RingHom.algebraMap_toAlgebra, ← CategoryTheory.comp_apply, -CommRingCat.hom_comp,
      Scheme.Hom.appLE_comp_appLE, hgf, -Scheme.Hom.comp_appLE]⟩
  suffices ψ₁ = ψ₂ by
    simpa [ψ₁, ψ₂, -Iso.cancel_iso_hom_left, IsAffineOpen.isoSpec_hom] using
      congr(hW.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom ($this).toRingHom) ≫ hV.fromSpec)
  refine Algebra.FormallyUnramified.ext' (i.app W).hom ?_ ψ₁ ψ₂ ?_
  · obtain ⟨n, hn⟩ := hi
    exact ⟨n, by simpa using congr(($hn).ideal ⟨W, hW⟩)⟩
  · simp [ψ₁, ψ₂, ← CategoryTheory.comp_apply, -CommRingCat.hom_comp, hig,
      Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, -Scheme.Hom.comp_appLE]

/--
lemma `of_hom_ext` / 引理 `of_hom_ext`

English:
lemma of_hom_ext
  statement: (f : X ⟶ Y)
  proof: by
  refine ⟨fun {U hU V hV hVU} => ?_⟩
  let := (f.appLE U V hVU).hom.toAlgebra
  refine Algebra.FormallyUnramified.iff_comp_injective.mpr fun R _ _ I hI g₁ g₂ hg₁g₂ => ?_
  have hg₁ : f.appLE U V hVU ≫ CommRingCat.ofHom g₁ = CommRingCat.ofHom (algebraMap _ R) :=
    CommRingCat.hom_ext g₁.comp_alg

中文:
引理 of_hom_ext
  结论: (f : X ⟶ Y)
  证明: by
  refine ⟨fun {U hU V hV hVU} => ?_⟩
  let := (f.appLE U V hVU).hom.toAlgebra
  refine Algebra.FormallyUnramified.iff_comp_injective.mpr fun R _ _ I hI g₁ g₂ hg₁g₂ => ?_
  have hg₁ : f.appLE U V hVU ≫ CommRingCat.ofHom g₁ = CommRingCat.ofHom (algebraMap _ R) :=
    CommRingCat.hom_ext g₁.comp_alg

Depends on / 依赖: Finite, X.obj, Y.obj
-/
protected lemma of_hom_ext (f : X ⟶ Y)
    (H : forall (R S : CommRingCat) (φ : R ⟶ S) (_ : Function.Surjective φ)
      (_ : RingHom.ker φ.hom ^ 2 = ⊥) (g₁ g₂ : Spec R ⟶ X)
      (_ : Spec.map φ ≫ g₁ = Spec.map φ ≫ g₂) (_ : g₁ ≫ f = g₂ ≫ f), g₁ = g₂) :
    FormallyUnramified f := by
  refine ⟨fun {U hU V hV hVU} => ?_⟩
  let := (f.appLE U V hVU).hom.toAlgebra
  refine Algebra.FormallyUnramified.iff_comp_injective.mpr fun R _ _ I hI g₁ g₂ hg₁g₂ => ?_
  have hg₁ : f.appLE U V hVU ≫ CommRingCat.ofHom g₁ = CommRingCat.ofHom (algebraMap _ R) :=
    CommRingCat.hom_ext g₁.comp_algebraMap
  have hg₂ : f.appLE U V hVU ≫ CommRingCat.ofHom g₂ = CommRingCat.ofHom (algebraMap _ R) :=
    CommRingCat.hom_ext g₂.comp_algebraMap
  have := H (.of R) (.of (R ⧸ I)) (CommRingCat.ofHom (Ideal.Quotient.mkₐ Γ(Y, U) I))
    Ideal.Quotient.mk_surjective (by simpa)
    (Spec.map (CommRingCat.ofHom g₁) ≫ hV.fromSpec) (Spec.map (CommRingCat.ofHom g₂) ≫ hV.fromSpec)
    (by simp only [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, ← AlgHom.comp_toRingHom, *])
    (by simp only [Category.assoc, ← hU.SpecMap_appLE_fromSpec f hV hVU, ← Spec.map_comp_assoc, *])
  rw [cancel_mono]; rw [Spec.map_inj] at this
  exact AlgHom.ext fun x => congr($this x)

end FormallyUnramified

end AlgebraicGeometry
