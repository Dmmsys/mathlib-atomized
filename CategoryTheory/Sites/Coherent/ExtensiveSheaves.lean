/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Filippo A. E. Nuccio, Riccardo Brasca
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Sites.Canonical
public import Mathlib.CategoryTheory.Sites.Coherent.Basic
public import Mathlib.CategoryTheory.Sites.Preserves
/-!

# Sheaves for the extensive topology

This file characterises sheaves for the extensive topology.

## Main result

* `isSheaf_iff_preservesFiniteProducts`: In a finitary extensive category, the sheaves for the
  extensive topology are precisely those preserving finite products.
-/

public section

universe w

namespace CategoryTheory

open Limits Presieve Opposite

variable {C : Type*} [Category* C] {D : Type*} [Category* D]

variable [FinitaryPreExtensive C]

/--
Definition of `Presieve.Extensive` / `Presieve.Extensive` 的定义

English:
class Presieve.Extensive
  parameters: {X : C} (R : Presieve X)
  axioms and operations (1):
    - arrows_nonempty_isColimit : exists (α : Type) (_ : Finite α) (Z : α -> C) (π : (a : α) -> (Z a ⟶ X)), R = Presieve.ofArrows Z π ∧ Nonempty (IsColimit (Cofan.mk X π))

中文:
类 Presieve.Extensive
  参数: {X : C} (R : Presieve X)
  公理与运算 (1 个):
    - arrows_nonempty_isColimit : 存在 (α : Type) (_ : Finite α) (Z : α -> C) (π : (a : α) -> (Z a ⟶ X)), R = Presieve.ofArrows Z π ∧ Nonempty (IsColimit (Cofan.mk X π))
-/
class Presieve.Extensive {X : C} (R : Presieve X) : Prop where
  /-- `R` consists of a finite collection of arrows that together induce an isomorphism from the
  coproduct of their sources. -/
  arrows_nonempty_isColimit : exists (α : Type) (_ : Finite α) (Z : α -> C) (π : (a : α) -> (Z a ⟶ X)),
    R = Presieve.ofArrows Z π ∧ Nonempty (IsColimit (Cofan.mk X π))

instance {X : C} (S : Presieve X) [S.Extensive] : S.HasPairwisePullbacks where
  has_pullbacks := by
    obtain ⟨_, _, _, _, rfl, ⟨hc⟩⟩ := Presieve.Extensive.arrows_nonempty_isColimit (R := S)
    intro _ _ _ _ _ hg
    cases hg
    apply FinitaryPreExtensive.hasPullbacks_of_is_coproduct hc

/--
theorem `isSheafFor_extensive_of_preservesFiniteProducts` / 定理 `isSheafFor_extensive_of_preservesFiniteProducts`

English:
theorem isSheafFor_extensive_of_preservesFiniteProducts
  statement: {X : C} (S : Presieve X) [S.Extensive]
  proof: by
  obtain ⟨α, _, Z, π, rfl, ⟨hc⟩⟩ := Extensive.arrows_nonempty_isColimit (R := S)
  have : (ofArrows Z (Cofan.mk X π).inj).HasPairwisePullbacks :=
    (inferInstance : (ofArrows Z π).HasPairwisePullbacks)
  cases nonempty_fintype α
  exact isSheafFor_of_preservesProduct F _ hc

中文:
定理 isSheafFor_extensive_of_preservesFiniteProducts
  结论: {X : C} (S : Presieve X) [S.Extensive]
  证明: by
  obtain ⟨α, _, Z, π, rfl, ⟨hc⟩⟩ := Extensive.arrows_nonempty_isColimit (R := S)
  have : (ofArrows Z (Cofan.mk X π).inj).HasPairwisePullbacks :=
    (inferInstance : (ofArrows Z π).HasPairwisePullbacks)
  cases nonempty_fintype α
  exact isSheafFor_of_preservesProduct F _ hc

Depends on / 依赖: Cofan.mk, Extensive, Extensive.arrows_nonempty_isColimit, HasPairwisePullbacks, arrows_nonempty_isColimit, isSheafFor_of_preservesProduct, nonempty_fintype, ofArrows
-/
theorem isSheafFor_extensive_of_preservesFiniteProducts {X : C} (S : Presieve X) [S.Extensive]
    (F : Cᵒᵖ ⥤ Type w) [PreservesFiniteProducts F] : S.IsSheafFor F := by
  obtain ⟨α, _, Z, π, rfl, ⟨hc⟩⟩ := Extensive.arrows_nonempty_isColimit (R := S)
  have : (ofArrows Z (Cofan.mk X π).inj).HasPairwisePullbacks :=
    (inferInstance : (ofArrows Z π).HasPairwisePullbacks)
  cases nonempty_fintype α
  exact isSheafFor_of_preservesProduct F _ hc

instance {α : Type} [Finite α] (Z : α -> C) : (ofArrows Z (fun i => Sigma.ι Z i)).Extensive :=
  ⟨⟨α, inferInstance, Z, (fun i => Sigma.ι Z i), rfl, ⟨coproductIsCoproduct _⟩⟩⟩

/--
theorem `extensiveTopology.isSheaf_yoneda_obj` / 定理 `extensiveTopology.isSheaf_yoneda_obj`

English:
theorem extensiveTopology.isSheaf_yoneda_obj
  given: (W : C)
  statement: Presieve.IsSheaf (extensiveTopology C)
  proof: by
  rw [extensiveTopology]; rw [isSheaf_coverage]
  intro X R ⟨Y, α, Z, π, hR, hi⟩
  have : IsIso (Sigma.desc (Cofan.inj (Cofan.mk X π))) := hi
  have : R.Extensive := ⟨Y, α, Z, π, hR, ⟨Cofan.isColimitOfIsIsoSigmaDesc (Cofan.mk X π)⟩⟩
  exact isSheafFor_extensive_of_preservesFiniteProducts _ _

中文:
定理 extensiveTopology.isSheaf_yoneda_obj
  条件: (W : C)
  结论: Presieve.IsSheaf (extensiveTopology C)
  证明: by
  rw [extensiveTopology]; rw [isSheaf_coverage]
  intro X R ⟨Y, α, Z, π, hR, hi⟩
  have : IsIso (Sigma.desc (Cofan.inj (Cofan.mk X π))) := hi
  have : R.Extensive := ⟨Y, α, Z, π, hR, ⟨Cofan.isColimitOfIsIsoSigmaDesc (Cofan.mk X π)⟩⟩
  exact isSheafFor_extensive_of_preservesFiniteProducts _ _

Depends on / 依赖: Cofan.inj, Cofan.isColimitOfIsIsoSigmaDesc, Cofan.mk, Extensive, R.Extensive, Sigma.desc, extensiveTopology, isColimitOfIsIsoSigmaDesc, isSheafFor_extensive_of_preservesFiniteProducts, isSheaf_coverage
-/
theorem extensiveTopology.isSheaf_yoneda_obj (W : C) : Presieve.IsSheaf (extensiveTopology C)
    (yoneda.obj W) := by
  rw [extensiveTopology]; rw [isSheaf_coverage]
  intro X R ⟨Y, α, Z, π, hR, hi⟩
  have : IsIso (Sigma.desc (Cofan.inj (Cofan.mk X π))) := hi
  have : R.Extensive := ⟨Y, α, Z, π, hR, ⟨Cofan.isColimitOfIsIsoSigmaDesc (Cofan.mk X π)⟩⟩
  exact isSheafFor_extensive_of_preservesFiniteProducts _ _

/--
Instance `extensiveTopology.subcanonical` / 实例 `extensiveTopology.subcanonical`

English:
instance extensiveTopology.subcanonical
  signature: : (extensiveTopology C).Subcanonical
  body: GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj _ isSheaf_yoneda_obj

中文:
实例 extensiveTopology.subcanonical
  签名: : (extensiveTopology C).Subcanonical
  定义体: GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj _ isSheaf_yoneda_obj

Depends on / 依赖: GrothendieckTopology, GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj, Subcanonical, isSheaf_yoneda_obj, of_isSheaf_yoneda_obj
-/
instance extensiveTopology.subcanonical : (extensiveTopology C).Subcanonical :=
  GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj _ isSheaf_yoneda_obj

variable [FinitaryExtensive C]

/--
theorem `Presieve.isSheaf_iff_preservesFiniteProducts` / 定理 `Presieve.isSheaf_iff_preservesFiniteProducts`

English:
theorem Presieve.isSheaf_iff_preservesFiniteProducts
  given: (F : Cᵒᵖ ⥤ Type w)
  proof: by
  refine ⟨fun hF => ⟨fun n => ⟨fun {K} => ?_⟩⟩, fun hF => ?_⟩
  · rw [extensiveTopology, isSheaf_coverage] at hF
    let Z : Fin n -> C := fun i => unop (K.obj ⟨i⟩)
    have : (ofArrows Z (Cofan.mk (∐ Z) (Sigma.ι Z)).inj).HasPairwisePullbacks :=
      inferInstanceAs (ofArrows Z (Sigma.ι Z)).HasP

中文:
定理 Presieve.isSheaf_iff_preservesFiniteProducts
  条件: (F : Cᵒᵖ ⥤ Type w)
  证明: by
  refine ⟨fun hF => ⟨fun n => ⟨fun {K} => ?_⟩⟩, fun hF => ?_⟩
  · rw [extensiveTopology, isSheaf_coverage] at hF
    let Z : Fin n -> C := fun i => unop (K.obj ⟨i⟩)
    have : (ofArrows Z (Cofan.mk (∐ Z) (Sigma.ι Z)).inj).HasPairwisePullbacks :=
      inferInstanceAs (ofArrows Z (Sigma.ι Z)).HasP

Depends on / 依赖: Cofan.inj, Cofan.mk, Discrete, Discrete.functor, Discrete.natIsoF, HasPairwisePullbacks, K.obj, extensiveTopology, functor, isSheaf_coverage, natIsoF, ofArrows
-/
theorem Presieve.isSheaf_iff_preservesFiniteProducts (F : Cᵒᵖ ⥤ Type w) :
    Presieve.IsSheaf (extensiveTopology C) F ↔ PreservesFiniteProducts F := by
  refine ⟨fun hF => ⟨fun n => ⟨fun {K} => ?_⟩⟩, fun hF => ?_⟩
  · rw [extensiveTopology, isSheaf_coverage] at hF
    let Z : Fin n -> C := fun i => unop (K.obj ⟨i⟩)
    have : (ofArrows Z (Cofan.mk (∐ Z) (Sigma.ι Z)).inj).HasPairwisePullbacks :=
      inferInstanceAs (ofArrows Z (Sigma.ι Z)).HasPairwisePullbacks
    have : forall (i : Fin n), Mono (Cofan.inj (Cofan.mk (∐ Z) (Sigma.ι Z)) i) :=
inferInstanceAs forall (i : Fin n), Mono (Sigma.ι Z i)
    let i : K ≅ Discrete.functor (fun i => op (Z i)) := Discrete.natIsoFunctor
    let _ : PreservesLimit (Discrete.functor (fun i => op (Z i))) F :=
        Presieve.preservesProduct_of_isSheafFor F ?_ initialIsInitial _ (coproductIsCoproduct Z)
        (FinitaryExtensive.isPullback_initial_to_sigma_ι Z)
        (hF (Presieve.ofArrows Z (fun i => Sigma.ι Z i)) ?_)
    · exact preservesLimit_of_iso_diagram F i.symm
    · apply hF
      refine ⟨Empty, inferInstance, Empty.elim, IsEmpty.elim inferInstance, rfl, ⟨default,?_, ?_⟩⟩
      · ext b
        cases b
      · simp only [eq_iff_true_of_subsingleton]
    · exact ⟨Fin n, inferInstance, Z, (fun i => Sigma.ι Z i), rfl, instIsIsoDescι⟩
  · rw [extensiveTopology, Presieve.isSheaf_coverage]
    intro X R ⟨Y, α, Z, π, hR, hi⟩
    have : IsIso (Sigma.desc (Cofan.inj (Cofan.mk X π))) := hi
    have : R.Extensive := ⟨Y, α, Z, π, hR, ⟨Cofan.isColimitOfIsIsoSigmaDesc (Cofan.mk X π)⟩⟩
    exact isSheafFor_extensive_of_preservesFiniteProducts R F

/--
theorem `Presheaf.isSheaf_iff_preservesFiniteProducts` / 定理 `Presheaf.isSheaf_iff_preservesFiniteProducts`

English:
theorem Presheaf.isSheaf_iff_preservesFiniteProducts
  given: (F : Cᵒᵖ ⥤ D)
  proof: by
  constructor
  · intro h
    rw [IsSheaf] at h
    refine ⟨fun n => ⟨fun {K} => ⟨fun {c} hc => ?_⟩⟩⟩
    constructor
    apply coyonedaJointlyReflectsLimits
    intro ⟨E⟩
    specialize h E
    rw [Presieve.isSheaf_iff_preservesFiniteProducts] at h
    exact isLimitOfPreserves (F.comp (coyoneda.

中文:
定理 Presheaf.isSheaf_iff_preservesFiniteProducts
  条件: (F : Cᵒᵖ ⥤ D)
  证明: by
  constructor
  · intro h
    rw [IsSheaf] at h
    refine ⟨fun n => ⟨fun {K} => ⟨fun {c} hc => ?_⟩⟩⟩
    constructor
    apply coyonedaJointlyReflectsLimits
    intro ⟨E⟩
    specialize h E
    rw [Presieve.isSheaf_iff_preservesFiniteProducts] at h
    exact isLimitOfPreserves (F.comp (coyoneda.

Depends on / 依赖: F.comp, IsSheaf, Presieve, Presieve.isSheaf_iff_preservesFiniteProducts, coyoneda, coyoneda.obj, coyonedaJointlyReflectsLimits, isLimitOfPreserves, isSheaf_iff_preservesFiniteProducts, specialize
-/
theorem Presheaf.isSheaf_iff_preservesFiniteProducts (F : Cᵒᵖ ⥤ D) :
    IsSheaf (extensiveTopology C) F ↔ PreservesFiniteProducts F := by
  constructor
  · intro h
    rw [IsSheaf] at h
    refine ⟨fun n => ⟨fun {K} => ⟨fun {c} hc => ?_⟩⟩⟩
    constructor
    apply coyonedaJointlyReflectsLimits
    intro ⟨E⟩
    specialize h E
    rw [Presieve.isSheaf_iff_preservesFiniteProducts] at h
    exact isLimitOfPreserves (F.comp (coyoneda.obj ⟨E⟩)) hc
  · intro _ E
    rw [Presieve.isSheaf_iff_preservesFiniteProducts]
    exact ⟨inferInstance⟩

instance (F : Sheaf (extensiveTopology C) D) : PreservesFiniteProducts F.obj :=
  (Presheaf.isSheaf_iff_preservesFiniteProducts F.obj).mp F.property

end CategoryTheory
