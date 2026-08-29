/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Sites.Coherent.SheafComparison
public import Mathlib.CategoryTheory.Sites.Equivalence
/-!

# Coherence and equivalence of categories

This file proves that the coherent and regular topologies transfer nicely along equivalences of
categories.
-/

@[expose] public section

namespace CategoryTheory

variable {C : Type*} [Category* C]

open GrothendieckTopology

namespace Equivalence

variable {D : Type*} [Category* D]

section Coherent

variable [Precoherent C]

/--
theorem `precoherent` / 定理 `precoherent`

English:
theorem precoherent
  given: (e : C ≌ D)
  statement: Precoherent D
  proof: e.inverse.reflects_precoherent

中文:
定理 precoherent
  条件: (e : C ≌ D)
  结论: Precoherent D
  证明: e.inverse.reflects_precoherent

Depends on / 依赖: e.inverse.reflects_precoherent, inverse, reflects_precoherent
-/
theorem precoherent (e : C ≌ D) : Precoherent D := e.inverse.reflects_precoherent

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [EssentiallySmall
  signature: C] :
  body: (equivSmallModel C).precoherent

中文:
实例 [EssentiallySmall
  签名: C] :
  定义体: (equivSmallModel C).precoherent

Depends on / 依赖: equivSmallModel, precoherent
-/
instance [EssentiallySmall C] :
    Precoherent (SmallModel C) := (equivSmallModel C).precoherent

instance (e : C ≌ D) : haveI := precoherent e
    e.inverse.IsDenseSubsite (coherentTopology D) (coherentTopology C) where
  functorPushforward_mem_iff := by
    simp [coherentTopology.eq_induced e.inverse]

variable (A : Type*) [Category* A]

/--
Equivalent precoherent categories give equivalent coherent toposes.
-/
@[simps!]
/--
Definition of `sheafCongrPrecoherent` / `sheafCongrPrecoherent` 的定义

English:
definition sheafCongrPrecoherent
  signature: (e : C ≌ D)
  body: e.precoherent
    Sheaf (coherentTopology C) A ≌ Sheaf (coherentTopology D) A := e.sheafCongr _ _ _

中文:
定义 sheafCongrPrecoherent
  签名: (e : C ≌ D)
  定义体: e.precoherent
    Sheaf (coherentTopology C) A ≌ Sheaf (coherentTopology D) A := e.sheafCongr _ _ _

Depends on / 依赖: e.precoherent, precoherent
-/
def sheafCongrPrecoherent (e : C ≌ D) : haveI := e.precoherent
    Sheaf (coherentTopology C) A ≌ Sheaf (coherentTopology D) A := e.sheafCongr _ _ _

open Presheaf

/--
theorem `precoherent_isSheaf_iff` / 定理 `precoherent_isSheaf_iff`

English:
theorem precoherent_isSheaf_iff
  given: (e : C ≌ D) (F : Cᵒᵖ ⥤ A)
  statement: haveI
  proof: e.precoherent
    IsSheaf (coherentTopology C) F ↔ IsSheaf (coherentTopology D) (e.inverse.op ⋙ F) := by
  refine ⟨fun hF => ((e.sheafCongrPrecoherent A).functor.obj ⟨F, hF⟩).property, fun hF => ?_⟩
  rw [isSheaf_of_iso_iff (P' := e.functor.op ⋙ e.inverse.op ⋙ F)]
.property · exact (e.sheafCongrPrec

中文:
定理 precoherent_isSheaf_iff
  条件: (e : C ≌ D) (F : Cᵒᵖ ⥤ A)
  结论: haveI
  证明: e.precoherent
    IsSheaf (coherentTopology C) F ↔ IsSheaf (coherentTopology D) (e.inverse.op ⋙ F) := by
  refine ⟨fun hF => ((e.sheafCongrPrecoherent A).functor.obj ⟨F, hF⟩).property, fun hF => ?_⟩
  rw [isSheaf_of_iso_iff (P' := e.functor.op ⋙ e.inverse.op ⋙ F)]
.property · exact (e.sheafCongrPrec

Depends on / 依赖: e.precoherent, precoherent
-/
theorem precoherent_isSheaf_iff (e : C ≌ D) (F : Cᵒᵖ ⥤ A) : haveI := e.precoherent
    IsSheaf (coherentTopology C) F ↔ IsSheaf (coherentTopology D) (e.inverse.op ⋙ F) := by
  refine ⟨fun hF => ((e.sheafCongrPrecoherent A).functor.obj ⟨F, hF⟩).property, fun hF => ?_⟩
  rw [isSheaf_of_iso_iff (P' := e.functor.op ⋙ e.inverse.op ⋙ F)]
.property · exact (e.sheafCongrPrecoherent A).inverse.obj ⟨e.inverse.op ⋙ F, hF⟩
  · exact Functor.isoWhiskerRight e.op.unitIso F

/--
theorem `precoherent_isSheaf_iff_of_essentiallySmall` / 定理 `precoherent_isSheaf_iff_of_essentiallySmall`

English:
theorem precoherent_isSheaf_iff_of_essentiallySmall
  given: [EssentiallySmall C] (F : Cᵒᵖ ⥤ A)
  proof: precoherent_isSheaf_iff _ _ _

中文:
定理 precoherent_isSheaf_iff_of_essentiallySmall
  条件: [EssentiallySmall C] (F : Cᵒᵖ ⥤ A)
  证明: precoherent_isSheaf_iff _ _ _

Depends on / 依赖: precoherent_isSheaf_iff
-/
theorem precoherent_isSheaf_iff_of_essentiallySmall [EssentiallySmall C] (F : Cᵒᵖ ⥤ A) :
    IsSheaf (coherentTopology C) F ↔
      IsSheaf (coherentTopology (SmallModel C)) ((equivSmallModel C).inverse.op ⋙ F) :=
  precoherent_isSheaf_iff _ _ _

end Coherent

section Regular

variable [Preregular C]

/--
theorem `preregular` / 定理 `preregular`

English:
theorem preregular
  given: (e : C ≌ D)
  statement: Preregular D
  proof: e.inverse.reflects_preregular

中文:
定理 preregular
  条件: (e : C ≌ D)
  结论: Preregular D
  证明: e.inverse.reflects_preregular

Depends on / 依赖: e.inverse.reflects_preregular, inverse, reflects_preregular
-/
theorem preregular (e : C ≌ D) : Preregular D := e.inverse.reflects_preregular

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [EssentiallySmall
  signature: C] :
  body: (equivSmallModel C).preregular

中文:
实例 [EssentiallySmall
  签名: C] :
  定义体: (equivSmallModel C).preregular

Depends on / 依赖: equivSmallModel, preregular
-/
instance [EssentiallySmall C] :
    Preregular (SmallModel C) := (equivSmallModel C).preregular

instance (e : C ≌ D) : haveI := preregular e
    e.inverse.IsDenseSubsite (regularTopology D) (regularTopology C) where
  functorPushforward_mem_iff := by
    simp [regularTopology.eq_induced e.inverse]

variable (A : Type*) [Category* A]

/--
Equivalent preregular categories give equivalent regular toposes.
-/
@[simps!]
/--
Definition of `sheafCongrPreregular` / `sheafCongrPreregular` 的定义

English:
definition sheafCongrPreregular
  signature: (e : C ≌ D)
  body: e.preregular
    Sheaf (regularTopology C) A ≌ Sheaf (regularTopology D) A := e.sheafCongr _ _ _

中文:
定义 sheafCongrPreregular
  签名: (e : C ≌ D)
  定义体: e.preregular
    Sheaf (regularTopology C) A ≌ Sheaf (regularTopology D) A := e.sheafCongr _ _ _

Depends on / 依赖: e.preregular, preregular
-/
def sheafCongrPreregular (e : C ≌ D) : haveI := e.preregular
    Sheaf (regularTopology C) A ≌ Sheaf (regularTopology D) A := e.sheafCongr _ _ _

open Presheaf

/--
theorem `preregular_isSheaf_iff` / 定理 `preregular_isSheaf_iff`

English:
theorem preregular_isSheaf_iff
  given: (e : C ≌ D) (F : Cᵒᵖ ⥤ A)
  statement: haveI
  proof: e.preregular
    IsSheaf (regularTopology C) F ↔ IsSheaf (regularTopology D) (e.inverse.op ⋙ F) := by
  refine ⟨fun hF => ((e.sheafCongrPreregular A).functor.obj ⟨F, hF⟩).property, fun hF => ?_⟩
  rw [isSheaf_of_iso_iff (P' := e.functor.op ⋙ e.inverse.op ⋙ F)]
.property · exact (e.sheafCongrPreregul

中文:
定理 preregular_isSheaf_iff
  条件: (e : C ≌ D) (F : Cᵒᵖ ⥤ A)
  结论: haveI
  证明: e.preregular
    IsSheaf (regularTopology C) F ↔ IsSheaf (regularTopology D) (e.inverse.op ⋙ F) := by
  refine ⟨fun hF => ((e.sheafCongrPreregular A).functor.obj ⟨F, hF⟩).property, fun hF => ?_⟩
  rw [isSheaf_of_iso_iff (P' := e.functor.op ⋙ e.inverse.op ⋙ F)]
.property · exact (e.sheafCongrPreregul

Depends on / 依赖: e.preregular, preregular
-/
theorem preregular_isSheaf_iff (e : C ≌ D) (F : Cᵒᵖ ⥤ A) : haveI := e.preregular
    IsSheaf (regularTopology C) F ↔ IsSheaf (regularTopology D) (e.inverse.op ⋙ F) := by
  refine ⟨fun hF => ((e.sheafCongrPreregular A).functor.obj ⟨F, hF⟩).property, fun hF => ?_⟩
  rw [isSheaf_of_iso_iff (P' := e.functor.op ⋙ e.inverse.op ⋙ F)]
.property · exact (e.sheafCongrPreregular A).inverse.obj ⟨e.inverse.op ⋙ F, hF⟩
  · exact Functor.isoWhiskerRight e.op.unitIso F

/--
theorem `preregular_isSheaf_iff_of_essentiallySmall` / 定理 `preregular_isSheaf_iff_of_essentiallySmall`

English:
theorem preregular_isSheaf_iff_of_essentiallySmall
  given: [EssentiallySmall C] (F : Cᵒᵖ ⥤ A)
  proof: preregular_isSheaf_iff _ _ _

中文:
定理 preregular_isSheaf_iff_of_essentiallySmall
  条件: [EssentiallySmall C] (F : Cᵒᵖ ⥤ A)
  证明: preregular_isSheaf_iff _ _ _

Depends on / 依赖: preregular_isSheaf_iff
-/
theorem preregular_isSheaf_iff_of_essentiallySmall [EssentiallySmall C] (F : Cᵒᵖ ⥤ A) :
    IsSheaf (regularTopology C) F ↔ IsSheaf (regularTopology (SmallModel C))
    ((equivSmallModel C).inverse.op ⋙ F) := preregular_isSheaf_iff _ _ _

end Regular

end Equivalence

end CategoryTheory
