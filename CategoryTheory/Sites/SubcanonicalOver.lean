/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Canonical
public import Mathlib.CategoryTheory.Sites.Over

/-!
# Topology on `Over X` is subcanonical if the base is

We show that if `J` is subcanonical, then also `J.over X` is subcanonical.
-/

public section

namespace CategoryTheory.GrothendieckTopology

variable {C : Type*} [Category* C]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `subcanonical_over` / 实例 `subcanonical_over`

English:
instance subcanonical_over
  signature: (J : GrothendieckTopology C) [J.Subcanonical] (X : C)
  body: by
  refine .of_isSheaf_yoneda_obj _ fun E Z R hR t ht => ?_
  obtain ⟨ι, T, g, rfl⟩ := R.exists_eq_ofArrows
  let hg : Presieve.Arrows.Compatible (CategoryTheory.yoneda.obj E.left)
      (fun i => (g i).left) (fun i => (t (g i) (Sieve.ofArrows_mk T g i)).left) :=
    fun i j Z gi gj hgij => congr($

中文:
实例 subcanonical_over
  签名: (J : Grothendieck拓扑 C) [J.子典范] (X : C)
  定义体: by
  refine .of_isSheaf_yoneda_obj _ fun E Z R hR t ht => ?_
  obtain ⟨ι, T, g, rfl⟩ := R.exists_eq_ofArrows
  let hg : Presieve.Arrows.Compatible (CategoryTheory.yoneda.obj E.left)
      (fun i => (g i).left) (fun i => (t (g i) (Sieve.ofArrows_mk T g i)).left) :=
    fun i j Z gi gj hgij => congr($

Depends on / 依赖: Arrows, CategoryTheory, CategoryTheory.yoneda.obj, Compatible, E.left, Over.homMk, Over.mk, Over.w, Presieve, Presieve.Arrows.Compatible, R.exists_eq_ofArrows, Sieve.ofArrows_mk, exists_eq_ofArrows, ofArrows_mk, of_isSheaf_yoneda_obj, reassoc_of, yoneda
-/
instance subcanonical_over (J : GrothendieckTopology C) [J.Subcanonical] (X : C) :
    (J.over X).Subcanonical := by
  refine .of_isSheaf_yoneda_obj _ fun E Z R hR t ht => ?_
  obtain ⟨ι, T, g, rfl⟩ := R.exists_eq_ofArrows
  let hg : Presieve.Arrows.Compatible (CategoryTheory.yoneda.obj E.left)
      (fun i => (g i).left) (fun i => (t (g i) (Sieve.ofArrows_mk T g i)).left) :=
    fun i j Z gi gj hgij => congr($(ht (Over.homMk (U := Over.mk (gi ≫ (T i).hom)) gi rfl)
      (Over.homMk (U := Over.mk (gi ≫ (T i).hom)) gj
      (by dsimp; rw [← Over.w (g i), reassoc_of% hgij, ← Over.w (g j)]))
      (Sieve.ofArrows_mk _ _ i) (Sieve.ofArrows_mk _ _ j) (by ext; exact hgij)).left)
  rw [J.mem_over_iff]; rw [Sieve.ofArrows]; rw [Sieve.overEquiv_generate]; rw [← Sieve.arrows_generate_map_eq_functorPushforward]; rw [Sieve.generate_sieve]; rw [Presieve.map_ofArrows] at hR
  obtain ⟨a, ha, huniq⟩ := Subcanonical.isSheaf_of_isRepresentable
    (CategoryTheory.yoneda.obj E.left) _ hR _ hg.familyOfElements_compatible.sieveExtend
  refine ⟨?_, ?_, fun y hty => ?_⟩
  · refine Over.homMk a ?_
    refine (Subcanonical.isSheaf_of_isRepresentable <| CategoryTheory.yoneda.obj X)
.isSeparatedFor.ext ?_ (.ofArrows _ <| fun i => (g i).left) hR
    rintro W u ⟨V, v, _, ⟨i⟩, rfl⟩
    have := ha _ (Sieve.ofArrows_mk _ _ i)
    dsimp at this
    simp [reassoc_of% this, Presieve.extend_agrees hg.familyOfElements_compatible (.mk i)]
  · rintro W p ⟨V, v, _, ⟨i⟩, rfl⟩
    refine Over.OverMorphism.ext ?_
    have := ha (g i).left (Sieve.ofArrows_mk _ _ i)
    dsimp at this
    simp [Category.assoc, this, Presieve.extend_agrees hg.familyOfElements_compatible (.mk i),
      Presieve.FamilyOfElements.comp_of_compatible _ ht (Sieve.ofArrows_mk _ _ i)]
  · refine Over.OverMorphism.ext (huniq _ ?_)
    rintro W p ⟨V, v, _, ⟨i⟩, rfl⟩
    have := congr($(hty _ (Sieve.ofArrows_mk _ _ i)).left)
    dsimp at this
    simp [Presieve.FamilyOfElements.comp_of_compatible _
      hg.familyOfElements_compatible.sieveExtend (Sieve.ofArrows_mk _ _ i),
      Presieve.extend_agrees hg.familyOfElements_compatible (.mk i), this]

end CategoryTheory.GrothendieckTopology
