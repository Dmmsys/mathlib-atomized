/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Combinatorics.Quiver.Path

/-!
# Path Decomposition and Boundary Crossing

This section provides lemmas for decomposing non-empty paths and for reasoning about paths that
cross the boundary of a given set of vertices `S`.
-/

public section
namespace Quiver.Path

section BoundaryEdges

variable {V : Type*} [Quiver V]

/--
theorem `exists_notMem_mem_hom_path_path_of_notMem_mem` / 定理 `exists_notMem_mem_hom_path_path_of_notMem_mem`

English:
theorem exists_notMem_mem_hom_path_path_of_notMem_mem
  statement: {a b : V} (p : Path a b) (S : Set V)
  proof: by
  induction h_len : p.length generalizing a b S ha_not_in_S hb_in_S with
  | zero =>
    obtain rfl := eq_of_length_zero p h_len
    exact (ha_not_in_S hb_in_S).elim
  | succ n ih =>
    have h_pos : 0 < p.length := by simp [h_len]
    obtain ⟨c, p', e, rfl⟩ := (length_ne_zero_iff_eq_cons p).mp h

中文:
定理 存在_notMem_mem_hom_path_path_of_notMem_mem
  结论: {a b : V} (p : 道路 a b) (S : 集合 V)
  证明: by
  induction h_len : p.length generalizing a b S ha_not_in_S hb_in_S with
  | zero =>
    obtain rfl := eq_of_length_zero p h_len
    exact (ha_not_in_S hb_in_S).elim
  | succ n ih =>
    have h_pos : 0 < p.length := by simp [h_len]
    obtain ⟨c, p', e, rfl⟩ := (length_ne_zero_iff_eq_cons p).mp h

Depends on / 依赖: _len, e.toPat, e_uv, eq_of_length_zero, generalizing, h_len, h_pos, h_pos.ne, ha_not_in_S, hb_in_S, hc_in_S, hu_not_S, hv_S, length, length_ne_zero_iff_eq_cons, p.length
-/
theorem exists_notMem_mem_hom_path_path_of_notMem_mem {a b : V} (p : Path a b) (S : Set V)
    (ha_not_in_S : a ∉ S) (hb_in_S : b in S) :
    existsᵉ (u ∉ S) (v in S) (e : u ⟶ v) (p₁ : Path a u) (p₂ : Path v b),
      p = p₁.comp (e.toPath.comp p₂) := by
  induction h_len : p.length generalizing a b S ha_not_in_S hb_in_S with
  | zero =>
    obtain rfl := eq_of_length_zero p h_len
    exact (ha_not_in_S hb_in_S).elim
  | succ n ih =>
    have h_pos : 0 < p.length := by simp [h_len]
    obtain ⟨c, p', e, rfl⟩ := (length_ne_zero_iff_eq_cons p).mp h_pos.ne'
    by_cases hc_in_S : c in S
    · have p'_len : p'.length = n := by simp_all
      obtain ⟨u, hu_not_S, v, hv_S, e_uv, p₁, p₂, hp'⟩ :=
        ih p' S ha_not_in_S hc_in_S p'_len
      refine ⟨u, hu_not_S, v, hv_S, e_uv, p₁, p₂.comp e.toPath, ?_⟩
      simp [hp', comp_toPath_eq_cons]
    · refine ⟨c, hc_in_S, b, hb_in_S, e, p', Path.nil, ?_⟩
      simp [comp_toPath_eq_cons]

/--
theorem `exists_mem_notMem_hom_path_path_of_notMem_mem` / 定理 `exists_mem_notMem_hom_path_path_of_notMem_mem`

English:
theorem exists_mem_notMem_hom_path_path_of_notMem_mem
  statement: {a b : V} (p : Path a b) (S : Set V)
  proof: by
  have ha_not_in_compl : a ∉ Sᶜ := by simpa
  have hb_in_compl : b in Sᶜ := by simpa
  obtain ⟨u, hu_not_in_compl, v, hv_in_compl, e, p₁, p₂, hp⟩ :=
    exists_notMem_mem_hom_path_path_of_notMem_mem p Sᶜ ha_not_in_compl hb_in_compl
  simp only [Set.mem_compl_iff, not_not] at hu_not_in_compl hv_in

中文:
定理 存在_mem_notMem_hom_path_path_of_notMem_mem
  结论: {a b : V} (p : 道路 a b) (S : 集合 V)
  证明: by
  have ha_not_in_compl : a ∉ Sᶜ := by simpa
  have hb_in_compl : b in Sᶜ := by simpa
  obtain ⟨u, hu_not_in_compl, v, hv_in_compl, e, p₁, p₂, hp⟩ :=
    exists_notMem_mem_hom_path_path_of_notMem_mem p Sᶜ ha_not_in_compl hb_in_compl
  simp only [Set.mem_compl_iff, not_not] at hu_not_in_compl hv_in

Depends on / 依赖: Set.mem_compl_iff, exists_notMem_mem_hom_path_path_of_notMem_mem, ha_not_in_compl, hb_in_compl, hu_not_in_compl, hv_in_compl, mem_compl_iff, not_not
-/
theorem exists_mem_notMem_hom_path_path_of_notMem_mem {a b : V} (p : Path a b) (S : Set V)
    (ha_in_S : a in S) (hb_not_in_S : b ∉ S) :
    existsᵉ (u in S) (v ∉ S) (e : u ⟶ v) (p₁ : Path a u) (p₂ : Path v b),
      p = p₁.comp (e.toPath.comp p₂) := by
  have ha_not_in_compl : a ∉ Sᶜ := by simpa
  have hb_in_compl : b in Sᶜ := by simpa
  obtain ⟨u, hu_not_in_compl, v, hv_in_compl, e, p₁, p₂, hp⟩ :=
    exists_notMem_mem_hom_path_path_of_notMem_mem p Sᶜ ha_not_in_compl hb_in_compl
  simp only [Set.mem_compl_iff, not_not] at hu_not_in_compl hv_in_compl
  refine ⟨u, hu_not_in_compl, v, hv_in_compl, e, p₁, p₂, hp⟩

end BoundaryEdges

end Quiver.Path
