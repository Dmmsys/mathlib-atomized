/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

/-!
# Flat monomorphisms of finite presentation are open immersions

We show the titular result `AlgebraicGeometry.IsOpenImmersion.of_flat_of_mono` by fpqc descent.
-/

public section

universe u

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry

@[stacks 06NC]
/--
lemma `Flat.isIso_of_surjective_of_mono` / 引理 `Flat.isIso_of_surjective_of_mono`

English:
lemma Flat.isIso_of_surjective_of_mono
  statement: {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
  proof: by
  apply MorphismProperty.of_pullback_fst_of_descendsAlong
    (P := isomorphisms Scheme.{u}) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (f := f) (g := f)
  · tauto
· exact inferInstanceAs IsIso (pullback.fst f f)

中文:
引理 平坦.isIso_of_surjective_of_mono
  结论: {X Y : 概形.{u}} (f : X ⟶ Y) [平坦 f]
  证明: by
  apply MorphismProperty.of_pullback_fst_of_descendsAlong
    (P := isomorphisms Scheme.{u}) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (f := f) (g := f)
  · tauto
· exact inferInstanceAs IsIso (pullback.fst f f)

Depends on / 依赖: Category, Category.assoc, False.elim, MorphismProperty, MorphismProperty.of_pullback_fst_of_descendsAlong, Multicofork, Multicofork.of, QuasiCompact, Scheme, Surjective, cancel_epi, convert, facePairIso, faceSingletonComplIso, fin_cases, isomorphisms, of_pullback_fst_of_descendsAlong, pullback, pullback.fst, stdSimplex
-/
lemma Flat.isIso_of_surjective_of_mono {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    [QuasiCompact f] [Surjective f] [Mono f] : IsIso f := by
  apply MorphismProperty.of_pullback_fst_of_descendsAlong
    (P := isomorphisms Scheme.{u}) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (f := f) (g := f)
  · tauto
· exact inferInstanceAs IsIso (pullback.fst f f)

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `IsOpenImmersion.of_flat_of_mono` / 定理 `IsOpenImmersion.of_flat_of_mono`

English:
theorem IsOpenImmersion.of_flat_of_mono
  statement: {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
  proof: by
  wlog hf : Surjective f
  · let U : Y.Opens := ⟨Set.range f.base, f.isOpenMap.isOpen_range⟩
    -- needed to prevent `wlog` to go in a typeclass loop
    have hU : IsOpenImmersion U.ι := U.instIsOpenImmersionι
    let f' := hU.lift U.ι f (by simp [U])
    have heq : f = f' ≫ U.ι := by simp [f']
    have hflat : Flat f' :=
      of_postcomp (W := @Flat) f' U.ι hU (by rwa [← heq])
    have hfinpres : LocallyOfFinitePresentation f' :=
      of_postcomp (W := @LocallyOfFinitePresentation) f' U.ι hU (by rwa [← heq])
    have hmono : Mono f' := mono_of_mono_fac heq.symm
    rw [heq]
    have := this f' ⟨fun ⟨x, ⟨y, hy⟩⟩ =>
      ⟨y, by apply U.ι.injective; simp [← Scheme.Hom.comp_apply, f', hy]⟩⟩
    infer_instance
  have hhomeo : IsHomeomorph f.base := ⟨f.continuous, f.isOpenMap, f.injective, f.surjective⟩
  have : QuasiCompact f := ⟨fun U hU hc => hhomeo.homeomorph.isCompact_preimage.mpr hc⟩
  have := Flat.isIso_of_surjective_of_mono f
  exact .of_isIso f

中文:
定理 是开浸入.of_flat_of_mono
  结论: {X Y : 概形.{u}} (f : X ⟶ Y) [平坦 f]
  证明: by
  wlog hf : Surjective f
  · let U : Y.Opens := ⟨Set.range f.base, f.isOpenMap.isOpen_range⟩
    -- needed to prevent `wlog` to go in a typeclass loop
    have hU : IsOpenImmersion U.ι := U.instIsOpenImmersionι
    let f' := hU.lift U.ι f (by simp [U])
    have heq : f = f' ≫ U.ι := by simp [f']
    have hflat : Flat f' :=
      of_postcomp (W := @Flat) f' U.ι hU (by rwa [← heq])
    have hfinpres : LocallyOfFinitePresentation f' :=
      of_postcomp (W := @LocallyOfFinitePresentation) f' U.ι hU (by rwa [← heq])
    have hmono : Mono f' := mono_of_mono_fac heq.symm
    rw [heq]
    have := this f' ⟨fun ⟨x, ⟨y, hy⟩⟩ =>
      ⟨y, by apply U.ι.injective; simp [← Scheme.Hom.comp_apply, f', hy]⟩⟩
    infer_instance
  have hhomeo : IsHomeomorph f.base := ⟨f.continuous, f.isOpenMap, f.injective, f.surjective⟩
  have : QuasiCompact f := ⟨fun U hU hc => hhomeo.homeomorph.isCompact_preimage.mpr hc⟩
  have := Flat.isIso_of_surjective_of_mono f
  exact .of_isIso f

Depends on / 依赖: Set.range, Surjective, Y.Opens, f.base, f.isOpenMap.isOpen_range, isOpenMap, isOpen_range
-/
theorem IsOpenImmersion.of_flat_of_mono {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    [LocallyOfFinitePresentation f] [Mono f] : IsOpenImmersion f := by
  wlog hf : Surjective f
  · let U : Y.Opens := ⟨Set.range f.base, f.isOpenMap.isOpen_range⟩
    -- needed to prevent `wlog` to go in a typeclass loop
    have hU : IsOpenImmersion U.ι := U.instIsOpenImmersionι
    let f' := hU.lift U.ι f (by simp [U])
    have heq : f = f' ≫ U.ι := by simp [f']
    have hflat : Flat f' :=
      of_postcomp (W := @Flat) f' U.ι hU (by rwa [← heq])
    have hfinpres : LocallyOfFinitePresentation f' :=
      of_postcomp (W := @LocallyOfFinitePresentation) f' U.ι hU (by rwa [← heq])
    have hmono : Mono f' := mono_of_mono_fac heq.symm
    rw [heq]
    have := this f' ⟨fun ⟨x, ⟨y, hy⟩⟩ =>
      ⟨y, by apply U.ι.injective; simp [← Scheme.Hom.comp_apply, f', hy]⟩⟩
    infer_instance
  have hhomeo : IsHomeomorph f.base := ⟨f.continuous, f.isOpenMap, f.injective, f.surjective⟩
  have : QuasiCompact f := ⟨fun U hU hc => hhomeo.homeomorph.isCompact_preimage.mpr hc⟩
  have := Flat.isIso_of_surjective_of_mono f
  exact .of_isIso f

end AlgebraicGeometry
