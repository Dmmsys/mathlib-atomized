/-
Copyright (c) 2025 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
-/
module

public import Mathlib.Topology.Separation.CompletelyRegular

import Mathlib.Topology.UniformSpace.OfCompactT2

/-!
# Uniformizable Spaces

A topological space is uniformizable (there exists a uniformity that
generates the same topology) iff it is completely regular.

## Main Results

* `UniformSpace.toCompletelyRegularSpace`: Uniform spaces are completely regular
* `CompletelyRegularSpace.exists_uniformSpace`: Completely regular spaces are uniformizable
* `CompletelyRegularSpace.of_exists_uniformSpace`: Uniformizable spaces are completely regular
* `completelyRegularSpace_iff_exists_uniformSpace`: A space is completely regular
  iff it is uniformizable

## Implementation Details

Urysohn's lemma is reused in the proof of `UniformSpace.completelyRegularSpace`.

## References

* <https://www.math.wm.edu/~vinroot/PadicGroups/519probset1.pdf>
-/

variable {X : Type*}

open Filter Set Uniformity UniformSpace SetRel

section UniformSpace
variable [UniformSpace X]

/--
Definition of `IsThickening` / `IsThickening` 的定义

English:
definition IsThickening
  signature: (c u : Set X)
  body: exists (x : X) (uc s : SetRel X X),
    IsOpen uc ∧ uc in 𝓤 X ∧ c = closure (ball x uc) ∧
    ball x (s ○ uc ○ s) subseteq u ∧ s in 𝓤 X

中文:
定义 IsThickening
  签名: (c u : 集合 X)
  定义体: exists (x : X) (uc s : SetRel X X),
    IsOpen uc ∧ uc in 𝓤 X ∧ c = closure (ball x uc) ∧
    ball x (s ○ uc ○ s) subseteq u ∧ s in 𝓤 X

Depends on / 依赖: IsOpen, SetRel, closure, subseteq
-/
def IsThickening (c u : Set X) :=
  exists (x : X) (uc s : SetRel X X),
    IsOpen uc ∧ uc in 𝓤 X ∧ c = closure (ball x uc) ∧
    ball x (s ○ uc ○ s) subseteq u ∧ s in 𝓤 X

/--
theorem `urysohns_main` / 定理 `urysohns_main`

English:
theorem urysohns_main
  given: {c u : Set X} (IsThickeningcu : IsThickening c u)
  proof: by
  obtain ⟨x, uc, s, huc, ucu, rfl, hn, hs⟩ := IsThickeningcu
  obtain ⟨(ds : SetRel X X), hdsu, hdso, -, hdsd⟩ := comp_open_symm_mem_uniformity_sets hs
  have ho : IsOpen (ds ○ uc ○ ds) := (hdso.relComp huc).relComp hdso
  have hsub := calc ds ○ (ds ○ uc ○ ds) ○ ds
    _ = (ds ○ ds) ○ uc ○ (ds ○ ds) := by simp [comp_assoc]
    _ subseteq s ○ uc ○ s := comp_subset_comp (comp_subset_comp_left hdsd) hdsd
  replace hsub := (ball_mono hsub x).trans hn
  have : ds.IsRefl := id_subset_iff.1 (refl_le_uniformity hdsu)
  refine ⟨ball x (ds ○ uc ○ ds), isOpen_ball x ho, ?_, subset_trans ?_ hsub,
      ⟨x, uc, ds, huc, ucu, rfl, subset_rfl, hdsu⟩,
      ⟨x, ds ○ uc ○ ds, ds, ho, mem_of_superset ucu (right_subset_comp.trans left_subset_comp),
        rfl, hsub, hdsu⟩⟩ <;>
  · refine closure_ball_subset.trans (ball_mono ?_ x)
    rw [closure_eq_inter_uniformity]
    exact iInter₂_subset_of_subset ds hdsu (by simp [comp_assoc])

public instance UniformSpace.toCompletelyRegularSpace : CompletelyRegularSpace X where
  completely_regular x K hK hx :=
    have ⟨O, hOu, hOo, hbO⟩ := isOpen_iff_isOpen_ball_subset.mp hK.isOpen_compl x hx
    have ⟨(u3 : SetRel X X), hu3u, _, hu3O⟩ := comp_comp_symm_mem_uniformity_sets hOu
    have hu3O := ((comp_subset_comp_left (comp_subset_comp_right interior_subset))).trans hu3O
    let c : Urysohns.CU IsThickening :=
    { C := closure (ball x (interior u3))
      U := ball x O
      closed_C := isClosed_closure
      open_U := isOpen_ball x hOo
subset := closure_ball_subset.trans (ball_mono · x) by
        simp_rw [closure_eq_inter_uniformity, ← comp_assoc]
        exact (iInter₂_subset u3 hu3u).trans hu3O
      hP _ IsThickeningcu _ _ := urysohns_main IsThickeningcu
      P_C_U := ⟨x, interior u3, u3,
        isOpen_interior, interior_mem_uniformity hu3u, rfl, ball_mono hu3O x, hu3u⟩ }
    ⟨fun x => ⟨c.lim x, c.lim_mem_Icc x⟩, c.continuous_lim.subtype_mk c.lim_mem_Icc,
      Subtype.ext (c.lim_of_mem_C x <| subset_closure (refl_mem_uniformity <|
        interior_mem_uniformity hu3u)), fun y hy => Subtype.ext (c.lim_of_notMem_U y (hbO · hy))⟩

中文:
定理 urysohns_main
  条件: {c u : 集合 X} (IsThickeningcu : IsThickening c u)
  证明: by
  obtain ⟨x, uc, s, huc, ucu, rfl, hn, hs⟩ := IsThickeningcu
  obtain ⟨(ds : SetRel X X), hdsu, hdso, -, hdsd⟩ := comp_open_symm_mem_uniformity_sets hs
  have ho : IsOpen (ds ○ uc ○ ds) := (hdso.relComp huc).relComp hdso
  have hsub := calc ds ○ (ds ○ uc ○ ds) ○ ds
    _ = (ds ○ ds) ○ uc ○ (ds ○ ds) := by simp [comp_assoc]
    _ subseteq s ○ uc ○ s := comp_subset_comp (comp_subset_comp_left hdsd) hdsd
  replace hsub := (ball_mono hsub x).trans hn
  have : ds.IsRefl := id_subset_iff.1 (refl_le_uniformity hdsu)
  refine ⟨ball x (ds ○ uc ○ ds), isOpen_ball x ho, ?_, subset_trans ?_ hsub,
      ⟨x, uc, ds, huc, ucu, rfl, subset_rfl, hdsu⟩,
      ⟨x, ds ○ uc ○ ds, ds, ho, mem_of_superset ucu (right_subset_comp.trans left_subset_comp),
        rfl, hsub, hdsu⟩⟩ <;>
  · refine closure_ball_subset.trans (ball_mono ?_ x)
    rw [closure_eq_inter_uniformity]
    exact iInter₂_subset_of_subset ds hdsu (by simp [comp_assoc])

public instance UniformSpace.toCompletelyRegularSpace : CompletelyRegularSpace X where
  completely_regular x K hK hx :=
    have ⟨O, hOu, hOo, hbO⟩ := isOpen_iff_isOpen_ball_subset.mp hK.isOpen_compl x hx
    have ⟨(u3 : SetRel X X), hu3u, _, hu3O⟩ := comp_comp_symm_mem_uniformity_sets hOu
    have hu3O := ((comp_subset_comp_left (comp_subset_comp_right interior_subset))).trans hu3O
    let c : Urysohns.CU IsThickening :=
    { C := closure (ball x (interior u3))
      U := ball x O
      closed_C := isClosed_closure
      open_U := isOpen_ball x hOo
subset := closure_ball_subset.trans (ball_mono · x) by
        simp_rw [closure_eq_inter_uniformity, ← comp_assoc]
        exact (iInter₂_subset u3 hu3u).trans hu3O
      hP _ IsThickeningcu _ _ := urysohns_main IsThickeningcu
      P_C_U := ⟨x, interior u3, u3,
        isOpen_interior, interior_mem_uniformity hu3u, rfl, ball_mono hu3O x, hu3u⟩ }
    ⟨fun x => ⟨c.lim x, c.lim_mem_Icc x⟩, c.continuous_lim.subtype_mk c.lim_mem_Icc,
      Subtype.ext (c.lim_of_mem_C x <| subset_closure (refl_mem_uniformity <|
        interior_mem_uniformity hu3u)), fun y hy => Subtype.ext (c.lim_of_notMem_U y (hbO · hy))⟩

Depends on / 依赖: IsOpen, IsRefl, IsThickeningcu, SetRel, ball_mono, comp_assoc, comp_open_symm_mem_uniformity_sets, comp_subset_comp, comp_subset_comp_left, ds.IsRefl, hdso.relComp, id_subset_iff, refl_le_uniformity, relComp, replace, subseteq
-/
theorem urysohns_main {c u : Set X} (IsThickeningcu : IsThickening c u) :
    exists (v : Set X), IsOpen v ∧ c subseteq v ∧ closure v subseteq u ∧
      IsThickening c v ∧ IsThickening (closure v) u := by
  obtain ⟨x, uc, s, huc, ucu, rfl, hn, hs⟩ := IsThickeningcu
  obtain ⟨(ds : SetRel X X), hdsu, hdso, -, hdsd⟩ := comp_open_symm_mem_uniformity_sets hs
  have ho : IsOpen (ds ○ uc ○ ds) := (hdso.relComp huc).relComp hdso
  have hsub := calc ds ○ (ds ○ uc ○ ds) ○ ds
    _ = (ds ○ ds) ○ uc ○ (ds ○ ds) := by simp [comp_assoc]
    _ subseteq s ○ uc ○ s := comp_subset_comp (comp_subset_comp_left hdsd) hdsd
  replace hsub := (ball_mono hsub x).trans hn
  have : ds.IsRefl := id_subset_iff.1 (refl_le_uniformity hdsu)
  refine ⟨ball x (ds ○ uc ○ ds), isOpen_ball x ho, ?_, subset_trans ?_ hsub,
      ⟨x, uc, ds, huc, ucu, rfl, subset_rfl, hdsu⟩,
      ⟨x, ds ○ uc ○ ds, ds, ho, mem_of_superset ucu (right_subset_comp.trans left_subset_comp),
        rfl, hsub, hdsu⟩⟩ <;>
  · refine closure_ball_subset.trans (ball_mono ?_ x)
    rw [closure_eq_inter_uniformity]
    exact iInter₂_subset_of_subset ds hdsu (by simp [comp_assoc])

public instance UniformSpace.toCompletelyRegularSpace : CompletelyRegularSpace X where
  completely_regular x K hK hx :=
    have ⟨O, hOu, hOo, hbO⟩ := isOpen_iff_isOpen_ball_subset.mp hK.isOpen_compl x hx
    have ⟨(u3 : SetRel X X), hu3u, _, hu3O⟩ := comp_comp_symm_mem_uniformity_sets hOu
    have hu3O := ((comp_subset_comp_left (comp_subset_comp_right interior_subset))).trans hu3O
    let c : Urysohns.CU IsThickening :=
    { C := closure (ball x (interior u3))
      U := ball x O
      closed_C := isClosed_closure
      open_U := isOpen_ball x hOo
subset := closure_ball_subset.trans (ball_mono · x) by
        simp_rw [closure_eq_inter_uniformity, ← comp_assoc]
        exact (iInter₂_subset u3 hu3u).trans hu3O
      hP _ IsThickeningcu _ _ := urysohns_main IsThickeningcu
      P_C_U := ⟨x, interior u3, u3,
        isOpen_interior, interior_mem_uniformity hu3u, rfl, ball_mono hu3O x, hu3u⟩ }
    ⟨fun x => ⟨c.lim x, c.lim_mem_Icc x⟩, c.continuous_lim.subtype_mk c.lim_mem_Icc,
      Subtype.ext (c.lim_of_mem_C x <| subset_closure (refl_mem_uniformity <|
        interior_mem_uniformity hu3u)), fun y hy => Subtype.ext (c.lim_of_notMem_U y (hbO · hy))⟩

end UniformSpace

section TopologicalSpace
variable [t : TopologicalSpace X]

public theorem CompletelyRegularSpace.of_exists_uniformSpace
    (h : exists u : UniformSpace X, u.toTopologicalSpace = t) :
    CompletelyRegularSpace X := by
  obtain ⟨u, rfl⟩ := h
  infer_instance

public theorem CompletelyRegularSpace.exists_uniformSpace [CompletelyRegularSpace X] :
    exists u : UniformSpace X, u.toTopologicalSpace = t :=
  ⟨uniformSpaceOfCompactR1.comap stoneCechUnit, isInducing_stoneCechUnit.eq_induced.symm⟩

public theorem completelyRegularSpace_iff_exists_uniformSpace :
    CompletelyRegularSpace X ↔ exists u : UniformSpace X, u.toTopologicalSpace = t :=
  ⟨(·.exists_uniformSpace), .of_exists_uniformSpace⟩

end TopologicalSpace
