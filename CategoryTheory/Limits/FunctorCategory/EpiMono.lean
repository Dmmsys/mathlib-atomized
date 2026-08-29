/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# Monomorphisms and epimorphisms in functor categories

A natural transformation `f : F ⟶ G` between functors `K ⥤ C`
is a mono (resp. epi) iff for all `k : K`, `f.app k` is,
at least when `C` has pullbacks (resp. pushouts),
see `NatTrans.mono_iff_mono_app` and `NatTrans.epi_iff_epi_app`.

-/

public section

universe v v' v'' u u' u''

namespace CategoryTheory

open Limits CategoryTheory.Functor

variable {K : Type u} [Category.{v} K] {C : Type u'} [Category.{v'} C]
  {D : Type u''} [Category.{v''} D] {F G : K ⥤ C} (f : F ⟶ G)
section

variable [HasPullbacks C]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mono
  signature: f] (k
  body: inferInstanceAs (Mono (((evaluation K C).obj k).map f))

中文:
实例 [Mono
  签名: f] (k
  定义体: inferInstanceAs (Mono (((evaluation K C).obj k).map f))

Depends on / 依赖: evaluation
-/
instance [Mono f] (k : K) : Mono (f.app k) :=
  inferInstanceAs (Mono (((evaluation K C).obj k).map f))

/--
lemma `NatTrans.mono_iff_mono_app` / 引理 `NatTrans.mono_iff_mono_app`

English:
lemma NatTrans.mono_iff_mono_app
  statement: Mono f ↔ forall (k : K), Mono (f.app k)
  proof: ⟨fun _ => inferInstance, fun _ => mono_of_mono_app _⟩

中文:
引理 NatTrans.mono_iff_mono_app
  结论: Mono f ↔ 对任意 (k : K), Mono (f.app k)
  证明: ⟨fun _ => inferInstance, fun _ => mono_of_mono_app _⟩

Depends on / 依赖: mono_of_mono_app
-/
lemma NatTrans.mono_iff_mono_app : Mono f ↔ forall (k : K), Mono (f.app k) :=
  ⟨fun _ => inferInstance, fun _ => mono_of_mono_app _⟩

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mono
  signature: f] (H
  body: by
  have : forall X, Mono ((whiskerRight f H).app X) := by intros; dsimp; infer_instance
  apply NatTrans.mono_of_mono_app

中文:
实例 [Mono
  签名: f] (H
  定义体: by
  have : forall X, Mono ((whiskerRight f H).app X) := by intros; dsimp; infer_instance
  apply NatTrans.mono_of_mono_app

Depends on / 依赖: NatTrans, NatTrans.mono_of_mono_app, infer_instance, intros, mono_of_mono_app, whiskerRight
-/
instance [Mono f] (H : C ⥤ D) [H.PreservesMonomorphisms] :
    Mono (whiskerRight f H) := by
  have : forall X, Mono ((whiskerRight f H).app X) := by intros; dsimp; infer_instance
  apply NatTrans.mono_of_mono_app

set_option backward.defeqAttrib.useBackward true in
instance (F : C ⥤ D) [F.PreservesMonomorphisms] :
    ((Functor.whiskeringRight K C D).obj F).PreservesMonomorphisms where
  preserves f _ := by dsimp; infer_instance

end

section

variable [HasPushouts C]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Epi
  signature: f] (k
  body: inferInstanceAs (Epi (((evaluation K C).obj k).map f))

中文:
实例 [Epi
  签名: f] (k
  定义体: inferInstanceAs (Epi (((evaluation K C).obj k).map f))

Depends on / 依赖: evaluation
-/
instance [Epi f] (k : K) : Epi (f.app k) :=
  inferInstanceAs (Epi (((evaluation K C).obj k).map f))

/--
lemma `NatTrans.epi_iff_epi_app` / 引理 `NatTrans.epi_iff_epi_app`

English:
lemma NatTrans.epi_iff_epi_app
  statement: Epi f ↔ forall (k : K), Epi (f.app k)
  proof: ⟨fun _ => inferInstance, fun _ => epi_of_epi_app _⟩

中文:
引理 NatTrans.epi_iff_epi_app
  结论: Epi f ↔ 对任意 (k : K), Epi (f.app k)
  证明: ⟨fun _ => inferInstance, fun _ => epi_of_epi_app _⟩

Depends on / 依赖: epi_of_epi_app
-/
lemma NatTrans.epi_iff_epi_app : Epi f ↔ forall (k : K), Epi (f.app k) :=
  ⟨fun _ => inferInstance, fun _ => epi_of_epi_app _⟩

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Epi
  signature: f] (H
  body: by
  have : forall X, Epi ((whiskerRight f H).app X) := by intros; dsimp; infer_instance
  apply NatTrans.epi_of_epi_app

中文:
实例 [Epi
  签名: f] (H
  定义体: by
  have : forall X, Epi ((whiskerRight f H).app X) := by intros; dsimp; infer_instance
  apply NatTrans.epi_of_epi_app

Depends on / 依赖: NatTrans, NatTrans.epi_of_epi_app, epi_of_epi_app, infer_instance, intros, whiskerRight
-/
instance [Epi f] (H : C ⥤ D) [H.PreservesEpimorphisms] :
    Epi (whiskerRight f H) := by
  have : forall X, Epi ((whiskerRight f H).app X) := by intros; dsimp; infer_instance
  apply NatTrans.epi_of_epi_app

end

end CategoryTheory
