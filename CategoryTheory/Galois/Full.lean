/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Galois.Action

/-!

# Fiber functors are (faithfully) full

Any (fiber) functor `F : C ⥤ FintypeCat` factors via the forgetful functor
from finite `Aut F`-sets to finite sets. The induced functor
`H : C ⥤ Action FintypeCat (Aut F)` is faithfully full. The faithfulness
follows easily from the faithfulness of `F`. In this file we show that `H` is also full.

## Main results

- `PreGaloisCategory.exists_lift_of_mono`: If `Y` is a sub-`Aut F`-set of `F.obj X`, there exists
  a sub-object `Z` of `X` such that `F.obj Z ≅ Y` as `Aut F`-sets.
- `PreGaloisCategory.functorToAction_full`: The induced functor `H` from above is full.

The main input for this is that the induced functor `H : C ⥤ Action FintypeCat (Aut F)`
preserves connectedness, which translates to the fact that `Aut F` acts transitively on
the fibers of connected objects.

-/

public section

universe u

namespace CategoryTheory

namespace PreGaloisCategory

open Limits CategoryTheory.Functor

variable {C : Type*} [Category* C] (F : C ⥤ FintypeCat.{u}) [GaloisCategory C] [FiberFunctor F]

/--
lemma `exists_lift_of_mono_of_isConnected` / 引理 `exists_lift_of_mono_of_isConnected`

English:
lemma exists_lift_of_mono_of_isConnected
  statement: (X : C) (Y : Action FintypeCat.{u} (Aut F))
  proof: by
  obtain ⟨y⟩ := nonempty_fiber_of_isConnected (forget₂ _ FintypeCat) Y
  obtain ⟨Z, f, z, hz, hc, hm⟩ := fiber_in_connected_component F X (i.hom y)
  have : IsConnected ((functorToAction F).obj Z) := PreservesIsConnected.preserves
  obtain ⟨u, hu⟩ := connected_component_unique
    (forget₂ (Action FintypeCat (Aut F)) FintypeCat) (B := (functorToAction F).obj Z)
    y z i ((functorToAction F).map f) hz.symm
  refine ⟨Z, f, u, hc, hm, ?_⟩
  apply evaluation_injective_of_isConnected
    (forget₂ (Action FintypeCat (Aut F)) FintypeCat) Y ((functorToAction F).obj X) y
  suffices h : i.hom y = F.map f z by simpa [hu]
  exact hz.symm

中文:
引理 存在_lift_of_mono_of_isConnected
  结论: (X : C) (Y : 作用 FintypeCat.{u} (Aut F))
  证明: by
  obtain ⟨y⟩ := nonempty_fiber_of_isConnected (forget₂ _ FintypeCat) Y
  obtain ⟨Z, f, z, hz, hc, hm⟩ := fiber_in_connected_component F X (i.hom y)
  have : IsConnected ((functorToAction F).obj Z) := PreservesIsConnected.preserves
  obtain ⟨u, hu⟩ := connected_component_unique
    (forget₂ (Action FintypeCat (Aut F)) FintypeCat) (B := (functorToAction F).obj Z)
    y z i ((functorToAction F).map f) hz.symm
  refine ⟨Z, f, u, hc, hm, ?_⟩
  apply evaluation_injective_of_isConnected
    (forget₂ (Action FintypeCat (Aut F)) FintypeCat) Y ((functorToAction F).obj X) y
  suffices h : i.hom y = F.map f z by simpa [hu]
  exact hz.symm

Depends on / 依赖: Action, FintypeCat, IsConnected, PreservesIsConnected, PreservesIsConnected.preserves, connected_component_unique, evaluation_injective_of_isConnected, fiber_in_connected_component, functorToAction, hz.symm, i.hom, nonempty_fiber_of_isConnected, preserves
-/
lemma exists_lift_of_mono_of_isConnected (X : C) (Y : Action FintypeCat.{u} (Aut F))
    (i : Y ⟶ (functorToAction F).obj X) [Mono i] [IsConnected Y] : exists (Z : C) (f : Z ⟶ X)
    (u : Y ≅ (functorToAction F).obj Z),
    IsConnected Z ∧ Mono f ∧ i = u.hom ≫ (functorToAction F).map f := by
  obtain ⟨y⟩ := nonempty_fiber_of_isConnected (forget₂ _ FintypeCat) Y
  obtain ⟨Z, f, z, hz, hc, hm⟩ := fiber_in_connected_component F X (i.hom y)
  have : IsConnected ((functorToAction F).obj Z) := PreservesIsConnected.preserves
  obtain ⟨u, hu⟩ := connected_component_unique
    (forget₂ (Action FintypeCat (Aut F)) FintypeCat) (B := (functorToAction F).obj Z)
    y z i ((functorToAction F).map f) hz.symm
  refine ⟨Z, f, u, hc, hm, ?_⟩
  apply evaluation_injective_of_isConnected
    (forget₂ (Action FintypeCat (Aut F)) FintypeCat) Y ((functorToAction F).obj X) y
  suffices h : i.hom y = F.map f z by simpa [hu]
  exact hz.symm

set_option backward.isDefEq.respectTransparency false in
/--
lemma `exists_lift_of_mono` / 引理 `exists_lift_of_mono`

English:
lemma exists_lift_of_mono
  statement: (X : C) (Y : Action FintypeCat.{u} (Aut F))
  proof: by
  obtain ⟨ι, hf, f, t, hc⟩ := has_decomp_connected_components' Y
  let i' (j : ι) : f j ⟶ (functorToAction F).obj X := Sigma.ι f j ≫ t.hom ≫ i
  choose gZ gf gu _ _ h using fun i => exists_lift_of_mono_of_isConnected F X (f i) (i' i)
  let is2 : (functorToAction F).obj (∐ gZ) ≅ ∐ fun i => (functorToAction F).obj (gZ i) :=
    PreservesCoproduct.iso (functorToAction F) gZ
  let u' : ∐ f ≅ ∐ fun i => (functorToAction F).obj (gZ i) := Sigma.mapIso gu
  have heq : (functorToAction F).map (Sigma.desc gf) = (t.symm ≪≫ u' ≪≫ is2.symm).inv ≫ i := by
    simp only [Iso.trans_inv, Iso.symm_inv, Category.assoc]
    rw [← Iso.inv_comp_eq]
    refine Sigma.hom_ext _ _ (fun j => ?_)
    suffices (functorToAction F).map (gf j) = (gu j).inv ≫ i' j by
      simpa [is2, u']
    simp only [h, Iso.inv_hom_id_assoc]
  refine ⟨∐ gZ, Sigma.desc gf, t.symm ≪≫ u' ≪≫ is2.symm, ?_, by simp [heq]⟩
  · exact mono_of_mono_map (functorToAction F) (heq ▸ mono_comp _ _)

中文:
引理 存在_lift_of_mono
  结论: (X : C) (Y : 作用 FintypeCat.{u} (Aut F))
  证明: by
  obtain ⟨ι, hf, f, t, hc⟩ := has_decomp_connected_components' Y
  let i' (j : ι) : f j ⟶ (functorToAction F).obj X := Sigma.ι f j ≫ t.hom ≫ i
  choose gZ gf gu _ _ h using fun i => exists_lift_of_mono_of_isConnected F X (f i) (i' i)
  let is2 : (functorToAction F).obj (∐ gZ) ≅ ∐ fun i => (functorToAction F).obj (gZ i) :=
    PreservesCoproduct.iso (functorToAction F) gZ
  let u' : ∐ f ≅ ∐ fun i => (functorToAction F).obj (gZ i) := Sigma.mapIso gu
  have heq : (functorToAction F).map (Sigma.desc gf) = (t.symm ≪≫ u' ≪≫ is2.symm).inv ≫ i := by
    simp only [Iso.trans_inv, Iso.symm_inv, Category.assoc]
    rw [← Iso.inv_comp_eq]
    refine Sigma.hom_ext _ _ (fun j => ?_)
    suffices (functorToAction F).map (gf j) = (gu j).inv ≫ i' j by
      simpa [is2, u']
    simp only [h, Iso.inv_hom_id_assoc]
  refine ⟨∐ gZ, Sigma.desc gf, t.symm ≪≫ u' ≪≫ is2.symm, ?_, by simp [heq]⟩
  · exact mono_of_mono_map (functorToAction F) (heq ▸ mono_comp _ _)

Depends on / 依赖: PreservesCoproduct, PreservesCoproduct.iso, Sigma.desc, Sigma.mapIso, exists_lift_of_mono_of_isConnected, functorToAction, has_decomp_connected_components, mapIso, t.hom, t.sym
-/
lemma exists_lift_of_mono (X : C) (Y : Action FintypeCat.{u} (Aut F))
    (i : Y ⟶ (functorToAction F).obj X) [Mono i] : exists (Z : C) (f : Z ⟶ X)
    (u : Y ≅ (functorToAction F).obj Z), Mono f ∧ u.hom ≫ (functorToAction F).map f = i := by
  obtain ⟨ι, hf, f, t, hc⟩ := has_decomp_connected_components' Y
  let i' (j : ι) : f j ⟶ (functorToAction F).obj X := Sigma.ι f j ≫ t.hom ≫ i
  choose gZ gf gu _ _ h using fun i => exists_lift_of_mono_of_isConnected F X (f i) (i' i)
  let is2 : (functorToAction F).obj (∐ gZ) ≅ ∐ fun i => (functorToAction F).obj (gZ i) :=
    PreservesCoproduct.iso (functorToAction F) gZ
  let u' : ∐ f ≅ ∐ fun i => (functorToAction F).obj (gZ i) := Sigma.mapIso gu
  have heq : (functorToAction F).map (Sigma.desc gf) = (t.symm ≪≫ u' ≪≫ is2.symm).inv ≫ i := by
    simp only [Iso.trans_inv, Iso.symm_inv, Category.assoc]
    rw [← Iso.inv_comp_eq]
    refine Sigma.hom_ext _ _ (fun j => ?_)
    suffices (functorToAction F).map (gf j) = (gu j).inv ≫ i' j by
      simpa [is2, u']
    simp only [h, Iso.inv_hom_id_assoc]
  refine ⟨∐ gZ, Sigma.desc gf, t.symm ≪≫ u' ≪≫ is2.symm, ?_, by simp [heq]⟩
  · exact mono_of_mono_map (functorToAction F) (heq ▸ mono_comp _ _)

set_option backward.isDefEq.respectTransparency false in
/--
Instance `functorToAction_full` / 实例 `functorToAction_full`

English:
instance functorToAction_full
  signature: : Functor.Full (functorToAction F) where
  body: by
    let u : (functorToAction F).obj X ⟶ (functorToAction F).obj X ⨯ (functorToAction F).obj Y :=
      prod.lift (𝟙 _) f
    let i : (functorToAction F).obj X ⟶ (functorToAction F).obj (X ⨯ Y) :=
      u ≫ (PreservesLimitPair.iso (functorToAction F) X Y).inv
    have : Mono i := by
      have : Mono (u ≫ prod.fst) := prod.lift_fst (𝟙 _) f ▸ inferInstance
      have : Mono u := mono_of_mono u prod.fst
      apply mono_comp u _
    obtain ⟨Z, g, v, _, hvgi⟩ := exists_lift_of_mono F (Limits.prod X Y)
      ((functorToAction F).obj X) i
    let ψ : Z ⟶ X := g ≫ prod.fst
    have hgvi : (functorToAction F).map g = v.inv ≫ i := by simp [← hvgi]
    have : IsIso ((functorToAction F).map ψ) := by
      simp only [map_comp, hgvi, Category.assoc, ψ]
      have : IsIso (i ≫ (functorToAction F).map prod.fst) := by
        suffices h : IsIso (𝟙 ((functorToAction F).obj X)) by simpa [i, u]
        infer_instance
      apply IsIso.comp_isIso
    have : IsIso ψ := isIso_of_reflects_iso ψ (functorToAction F)
    use inv ψ ≫ g ≫ prod.snd
    rw [← cancel_epi ((functorToAction F).map ψ)]
    ext (z : F.obj Z)
    simp [-FintypeCat.comp_apply, -Action.comp_hom, i, u, ψ, hgvi]

中文:
实例 functorToAction_full
  签名: : 函子.满 (functorToAction F) where
  定义体: by
    let u : (functorToAction F).obj X ⟶ (functorToAction F).obj X ⨯ (functorToAction F).obj Y :=
      prod.lift (𝟙 _) f
    let i : (functorToAction F).obj X ⟶ (functorToAction F).obj (X ⨯ Y) :=
      u ≫ (PreservesLimitPair.iso (functorToAction F) X Y).inv
    have : Mono i := by
      have : Mono (u ≫ prod.fst) := prod.lift_fst (𝟙 _) f ▸ inferInstance
      have : Mono u := mono_of_mono u prod.fst
      apply mono_comp u _
    obtain ⟨Z, g, v, _, hvgi⟩ := exists_lift_of_mono F (Limits.prod X Y)
      ((functorToAction F).obj X) i
    let ψ : Z ⟶ X := g ≫ prod.fst
    have hgvi : (functorToAction F).map g = v.inv ≫ i := by simp [← hvgi]
    have : IsIso ((functorToAction F).map ψ) := by
      simp only [map_comp, hgvi, Category.assoc, ψ]
      have : IsIso (i ≫ (functorToAction F).map prod.fst) := by
        suffices h : IsIso (𝟙 ((functorToAction F).obj X)) by simpa [i, u]
        infer_instance
      apply IsIso.comp_isIso
    have : IsIso ψ := isIso_of_reflects_iso ψ (functorToAction F)
    use inv ψ ≫ g ≫ prod.snd
    rw [← cancel_epi ((functorToAction F).map ψ)]
    ext (z : F.obj Z)
    simp [-FintypeCat.comp_apply, -Action.comp_hom, i, u, ψ, hgvi]

Depends on / 依赖: Limits, Limits.prod, PreservesLimitPair, PreservesLimitPair.iso, exists_lift_of_mono, functorToAction, lift_fst, mono_comp, mono_of_mono, prod.fst, prod.lift, prod.lift_fst
-/
instance functorToAction_full : Functor.Full (functorToAction F) where
  map_surjective {X Y} f := by
    let u : (functorToAction F).obj X ⟶ (functorToAction F).obj X ⨯ (functorToAction F).obj Y :=
      prod.lift (𝟙 _) f
    let i : (functorToAction F).obj X ⟶ (functorToAction F).obj (X ⨯ Y) :=
      u ≫ (PreservesLimitPair.iso (functorToAction F) X Y).inv
    have : Mono i := by
      have : Mono (u ≫ prod.fst) := prod.lift_fst (𝟙 _) f ▸ inferInstance
      have : Mono u := mono_of_mono u prod.fst
      apply mono_comp u _
    obtain ⟨Z, g, v, _, hvgi⟩ := exists_lift_of_mono F (Limits.prod X Y)
      ((functorToAction F).obj X) i
    let ψ : Z ⟶ X := g ≫ prod.fst
    have hgvi : (functorToAction F).map g = v.inv ≫ i := by simp [← hvgi]
    have : IsIso ((functorToAction F).map ψ) := by
      simp only [map_comp, hgvi, Category.assoc, ψ]
      have : IsIso (i ≫ (functorToAction F).map prod.fst) := by
        suffices h : IsIso (𝟙 ((functorToAction F).obj X)) by simpa [i, u]
        infer_instance
      apply IsIso.comp_isIso
    have : IsIso ψ := isIso_of_reflects_iso ψ (functorToAction F)
    use inv ψ ≫ g ≫ prod.snd
    rw [← cancel_epi ((functorToAction F).map ψ)]
    ext (z : F.obj Z)
    simp [-FintypeCat.comp_apply, -Action.comp_hom, i, u, ψ, hgvi]

end PreGaloisCategory

end CategoryTheory
