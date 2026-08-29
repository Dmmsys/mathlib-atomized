/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Sites.Coherent.Comparison
public import Mathlib.Topology.Category.CompHausLike.Limits
/-!

# Effective epimorphisms in `CompHausLike`

In any category of compact Hausdorff spaces, continuous surjections are effective epimorphisms.

We deduce that if the converse holds and explicit pullbacks exist, then `CompHausLike P` is
preregular.

If furthermore explicit finite coproducts exist, then `CompHausLike P` is precoherent.
-/

@[expose] public section

universe u

open CategoryTheory Limits Topology

namespace CompHausLike

variable {P : TopCat.{u} -> Prop}

/--
If `π` is a surjective morphism in `CompHausLike P`, then it is an effective epi.
-/
noncomputable
/--
Definition of `effectiveEpiStruct` / `effectiveEpiStruct` 的定义

English:
definition effectiveEpiStruct
  signature: {B X : CompHausLike P} (π : X ⟶ B) (hπ : Function.Surjective π)
  body: ofHom _ ((IsQuotientMap.of_surjective_continuous hπ π.hom.hom.continuous).lift e.hom.hom
      fun a b hab =>
        CategoryTheory.congr_fun (h
          (ofHom _ ⟨fun _ => a, continuous_const⟩)
          (ofHom _ ⟨fun _ => b, continuous_const⟩)
        (by ext; exact hab)) a)
  fac e h :=
    Ind

中文:
定义 effectiveEpiStruct
  签名: {B X : 余mpHausLike P} (π : X ⟶ B) (hπ : 函数.满射 π)
  定义体: ofHom _ ((IsQuotientMap.of_surjective_continuous hπ π.hom.hom.continuous).lift e.hom.hom
      fun a b hab =>
        CategoryTheory.congr_fun (h
          (ofHom _ ⟨fun _ => a, continuous_const⟩)
          (ofHom _ ⟨fun _ => b, continuous_const⟩)
        (by ext; exact hab)) a)
  fac e h :=
    Ind

Depends on / 依赖: CategoryTheory, CategoryTheory.congr_fun, InducedCategory, InducedCategory.hom_ext, IsQuotientMap, IsQuotientMap.of_surjective_continuous, TopCat, TopCat.hom_ext, congr_fun, continuous, continuous_const, e.hom.hom, hom.hom.continuous, hom_ext, liftEquiv, lift_comp, of_surjective_continuous
-/
def effectiveEpiStruct {B X : CompHausLike P} (π : X ⟶ B) (hπ : Function.Surjective π) :
    EffectiveEpiStruct π where
  desc e h :=
    ofHom _ ((IsQuotientMap.of_surjective_continuous hπ π.hom.hom.continuous).lift e.hom.hom
      fun a b hab =>
        CategoryTheory.congr_fun (h
          (ofHom _ ⟨fun _ => a, continuous_const⟩)
          (ofHom _ ⟨fun _ => b, continuous_const⟩)
        (by ext; exact hab)) a)
  fac e h :=
    InducedCategory.hom_ext (TopCat.hom_ext
      ((IsQuotientMap.of_surjective_continuous hπ π.hom.hom.continuous).lift_comp _ _))
  uniq e h g hm := by
    suffices g = ofHom _
        ((IsQuotientMap.of_surjective_continuous hπ π.hom.hom.continuous).liftEquiv ⟨e.hom.hom,
      fun a b hab => CategoryTheory.congr_fun
        (h
          (ofHom _ ⟨fun _ => a, continuous_const⟩)
          (ofHom _ ⟨fun _ => b, continuous_const⟩)
          (by ext; exact hab))
        a⟩) by assumption
    apply ConcreteCategory.ext
    rw [hom_ofHom]; rw [← Equiv.symm_apply_eq
      (IsQuotientMap.of_surjective_continuous hπ π.hom.hom.continuous).liftEquiv]
    ext
    simp only [IsQuotientMap.liftEquiv_symm_apply_coe, ContinuousMap.comp_apply, ← hm]
    rfl

/--
theorem `preregular` / 定理 `preregular`

English:
theorem preregular
  statement: [HasExplicitPullbacks P]
  proof: by
    intro X Y Z f π hπ
    refine ⟨pullback f π, pullback.fst f π, ⟨⟨effectiveEpiStruct _ ?_⟩⟩, pullback.snd f π,
      (pullback.condition _ _).symm⟩
    intro y
    obtain ⟨z, hz⟩ := hs π hπ (f y)
    exact ⟨⟨(y, z), hz.symm⟩, rfl⟩

中文:
定理 preregular
  结论: [有ExplicitPullbacks P]
  证明: by
    intro X Y Z f π hπ
    refine ⟨pullback f π, pullback.fst f π, ⟨⟨effectiveEpiStruct _ ?_⟩⟩, pullback.snd f π,
      (pullback.condition _ _).symm⟩
    intro y
    obtain ⟨z, hz⟩ := hs π hπ (f y)
    exact ⟨⟨(y, z), hz.symm⟩, rfl⟩

Depends on / 依赖: condition, effectiveEpiStruct, hz.symm, pullback, pullback.condition, pullback.fst, pullback.snd
-/
theorem preregular [HasExplicitPullbacks P]
    (hs : forall ⦃X Y : CompHausLike P⦄ (f : X ⟶ Y), EffectiveEpi f -> Function.Surjective f) :
    Preregular (CompHausLike P) where
  exists_fac := by
    intro X Y Z f π hπ
    refine ⟨pullback f π, pullback.fst f π, ⟨⟨effectiveEpiStruct _ ?_⟩⟩, pullback.snd f π,
      (pullback.condition _ _).symm⟩
    intro y
    obtain ⟨z, hz⟩ := hs π hπ (f y)
    exact ⟨⟨(y, z), hz.symm⟩, rfl⟩

/--
theorem `precoherent` / 定理 `precoherent`

English:
theorem precoherent
  statement: [HasExplicitPullbacks P] [HasExplicitFiniteCoproducts.{0} P]
  proof: by
  have : Preregular (CompHausLike P) := preregular hs
  infer_instance

中文:
定理 precoherent
  结论: [有ExplicitPullbacks P] [有ExplicitFiniteCoproducts.{0} P]
  证明: by
  have : Preregular (CompHausLike P) := preregular hs
  infer_instance

Depends on / 依赖: CompHausLike, Preregular, infer_instance, preregular
-/
theorem precoherent [HasExplicitPullbacks P] [HasExplicitFiniteCoproducts.{0} P]
    (hs : forall ⦃X Y : CompHausLike P⦄ (f : X ⟶ Y), EffectiveEpi f -> Function.Surjective f) :
    Precoherent (CompHausLike P) := by
  have : Preregular (CompHausLike P) := preregular hs
  infer_instance

end CompHausLike
