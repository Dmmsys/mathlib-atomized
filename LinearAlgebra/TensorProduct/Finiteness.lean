/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Map

/-!

# Some finiteness results of tensor product

This file contains some finiteness results of tensor product.

- `TensorProduct.exists_multiset`, `TensorProduct.exists_finsupp_left`,
  `TensorProduct.exists_finsupp_right`, `TensorProduct.exists_finset`:
  any element of `M ⊗[R] N` can be written as a finite sum of pure tensors.
  See also `TensorProduct.span_tmul_eq_top`.

- `TensorProduct.exists_finite_submodule_left_of_setFinite`,
  `TensorProduct.exists_finite_submodule_right_of_setFinite`,
  `TensorProduct.exists_finite_submodule_of_setFinite`:
  any finite subset of `M ⊗[R] N` is contained in `M' ⊗[R] N`,
  resp. `M ⊗[R] N'`, resp. `M' ⊗[R] N'`,
  for some finitely generated submodules `M'` and `N'` of `M` and `N`, respectively.

- `TensorProduct.exists_finite_submodule_left_of_setFinite'`,
  `TensorProduct.exists_finite_submodule_right_of_setFinite'`,
  `TensorProduct.exists_finite_submodule_of_setFinite'`:
  variation of the above results where `M` and `N` are already submodules.

## Tags

tensor product, finitely generated

-/

public section

open scoped TensorProduct

open Submodule

variable {R M N : Type*}

variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]

variable {M₁ M₂ : Submodule R M} {N₁ N₂ : Submodule R N}

namespace TensorProduct

/--
theorem `exists_multiset` / 定理 `exists_multiset`

English:
theorem exists_multiset
  given: (x : M otimes[R] N)
  proof: by
  induction x with
  | zero => exact ⟨0, by simp⟩
  | tmul x y => exact ⟨{(x, y)}, by simp⟩
  | add x y hx hy =>
    obtain ⟨Sx, hx⟩ := hx
    obtain ⟨Sy, hy⟩ := hy
    exact ⟨Sx + Sy, by rw [Multiset.map_add, Multiset.sum_add, hx, hy]⟩

中文:
定理 存在_multiset
  条件: (x : M otimes[R] N)
  证明: by
  induction x with
  | zero => exact ⟨0, by simp⟩
  | tmul x y => exact ⟨{(x, y)}, by simp⟩
  | add x y hx hy =>
    obtain ⟨Sx, hx⟩ := hx
    obtain ⟨Sy, hy⟩ := hy
    exact ⟨Sx + Sy, by rw [Multiset.map_add, Multiset.sum_add, hx, hy]⟩

Depends on / 依赖: Multiset, Multiset.map_add, Multiset.sum_add, map_add, sum_add
-/
theorem exists_multiset (x : M otimes[R] N) :
    exists S : Multiset (M × N), x = (S.map fun i => i.1 otimesₜ[R] i.2).sum := by
  induction x with
  | zero => exact ⟨0, by simp⟩
  | tmul x y => exact ⟨{(x, y)}, by simp⟩
  | add x y hx hy =>
    obtain ⟨Sx, hx⟩ := hx
    obtain ⟨Sy, hy⟩ := hy
    exact ⟨Sx + Sy, by rw [Multiset.map_add, Multiset.sum_add, hx, hy]⟩

/--
theorem `exists_finsupp_left` / 定理 `exists_finsupp_left`

English:
theorem exists_finsupp_left
  given: (x : M otimes[R] N)
  proof: by
  induction x with
  | zero => exact ⟨0, by simp⟩
  | tmul x y => exact ⟨Finsupp.single x y, by simp⟩
  | add x y hx hy =>
    obtain ⟨Sx, hx⟩ := hx
    obtain ⟨Sy, hy⟩ := hy
    use Sx + Sy
    rw [hx]; rw [hy]
    exact (Finsupp.sum_add_index' (by simp) TensorProduct.tmul_add).symm

中文:
定理 存在_finsupp_left
  条件: (x : M otimes[R] N)
  证明: by
  induction x with
  | zero => exact ⟨0, by simp⟩
  | tmul x y => exact ⟨Finsupp.single x y, by simp⟩
  | add x y hx hy =>
    obtain ⟨Sx, hx⟩ := hx
    obtain ⟨Sy, hy⟩ := hy
    use Sx + Sy
    rw [hx]; rw [hy]
    exact (Finsupp.sum_add_index' (by simp) TensorProduct.tmul_add).symm

Depends on / 依赖: Finsupp, Finsupp.single, Finsupp.sum_add_index, TensorProduct, TensorProduct.tmul_add, single, sum_add_index, tmul_add
-/
theorem exists_finsupp_left (x : M otimes[R] N) :
    exists S : M ->₀ N, x = S.sum fun m n => m otimesₜ[R] n := by
  induction x with
  | zero => exact ⟨0, by simp⟩
  | tmul x y => exact ⟨Finsupp.single x y, by simp⟩
  | add x y hx hy =>
    obtain ⟨Sx, hx⟩ := hx
    obtain ⟨Sy, hy⟩ := hy
    use Sx + Sy
    rw [hx]; rw [hy]
    exact (Finsupp.sum_add_index' (by simp) TensorProduct.tmul_add).symm

/--
theorem `exists_finsupp_right` / 定理 `exists_finsupp_right`

English:
theorem exists_finsupp_right
  given: (x : M otimes[R] N)
  proof: by
  obtain ⟨S, h⟩ := exists_finsupp_left (TensorProduct.comm R M N x)
  refine ⟨S, (TensorProduct.comm R M N).injective ?_⟩
  simp_rw [h, Finsupp.sum, map_sum, comm_tmul]

中文:
定理 存在_finsupp_right
  条件: (x : M otimes[R] N)
  证明: by
  obtain ⟨S, h⟩ := exists_finsupp_left (TensorProduct.comm R M N x)
  refine ⟨S, (TensorProduct.comm R M N).injective ?_⟩
  simp_rw [h, Finsupp.sum, map_sum, comm_tmul]

Depends on / 依赖: Finsupp, Finsupp.sum, TensorProduct, TensorProduct.comm, comm_tmul, exists_finsupp_left, injective, map_sum, simp_rw
-/
theorem exists_finsupp_right (x : M otimes[R] N) :
    exists S : N ->₀ M, x = S.sum fun n m => m otimesₜ[R] n := by
  obtain ⟨S, h⟩ := exists_finsupp_left (TensorProduct.comm R M N x)
  refine ⟨S, (TensorProduct.comm R M N).injective ?_⟩
  simp_rw [h, Finsupp.sum, map_sum, comm_tmul]

/--
theorem `exists_finset` / 定理 `exists_finset`

English:
theorem exists_finset
  given: (x : M otimes[R] N)
  proof: by
  obtain ⟨S, h⟩ := exists_finsupp_left x
  use S.graph
  rw [h]; rw [Finsupp.sum]
  apply Finset.sum_nbij' (fun m => ⟨m, S m⟩) Prod.fst <;> simp

中文:
定理 存在_finset
  条件: (x : M otimes[R] N)
  证明: by
  obtain ⟨S, h⟩ := exists_finsupp_left x
  use S.graph
  rw [h]; rw [Finsupp.sum]
  apply Finset.sum_nbij' (fun m => ⟨m, S m⟩) Prod.fst <;> simp

Depends on / 依赖: Finset, Finset.sum_nbij, Finsupp, Finsupp.sum, Prod.fst, S.graph, exists_finsupp_left, sum_nbij
-/
theorem exists_finset (x : M otimes[R] N) :
    exists S : Finset (M × N), x = S.sum fun i => i.1 otimesₜ[R] i.2 := by
  obtain ⟨S, h⟩ := exists_finsupp_left x
  use S.graph
  rw [h]; rw [Finsupp.sum]
  apply Finset.sum_nbij' (fun m => ⟨m, S m⟩) Prod.fst <;> simp

/--
theorem `exists_finite_submodule_of_setFinite` / 定理 `exists_finite_submodule_of_setFinite`

English:
theorem exists_finite_submodule_of_setFinite
  given: (s : Set (M otimes[R] N)) (hs : s.Finite)
  proof: by
  simp_rw [Module.Finite.iff_fg]
  induction s, hs using Set.Finite.induction_on with
  | empty => exact ⟨_, _, fg_bot, fg_bot, Set.empty_subset _⟩
  | @insert a s _ _ ih =>
  obtain ⟨M', N', hM', hN', h⟩ := ih
  refine TensorProduct.induction_on a ?_ (fun x y => ?_) fun x y hx hy => ?_
  · exact

中文:
定理 存在_finite_submodule_of_setFinite
  条件: (s : 集合 (M otimes[R] N)) (hs : s.有限)
  证明: by
  simp_rw [Module.Finite.iff_fg]
  induction s, hs using Set.Finite.induction_on with
  | empty => exact ⟨_, _, fg_bot, fg_bot, Set.empty_subset _⟩
  | @insert a s _ _ ih =>
  obtain ⟨M', N', hM', hN', h⟩ := ih
  refine TensorProduct.induction_on a ?_ (fun x y => ?_) fun x y hx hy => ?_
  · exact

Depends on / 依赖: Finite, Module, Module.Finite.iff_fg, Set.Finite.induction_on, Set.empty_subset, Set.insert_subset, TensorProduct, TensorProduct.induction_on, empty_subset, fg_bot, fg_span_singleton, iff_fg, induction_on, insert, insert_subset, mem_span_singleto, mem_sup_right, simp_rw, zero_mem
-/
theorem exists_finite_submodule_of_setFinite (s : Set (M otimes[R] N)) (hs : s.Finite) :
    exists (M' : Submodule R M) (N' : Submodule R N), Module.Finite R M' ∧ Module.Finite R N' ∧
      s subseteq LinearMap.range (mapIncl M' N') := by
  simp_rw [Module.Finite.iff_fg]
  induction s, hs using Set.Finite.induction_on with
  | empty => exact ⟨_, _, fg_bot, fg_bot, Set.empty_subset _⟩
  | @insert a s _ _ ih =>
  obtain ⟨M', N', hM', hN', h⟩ := ih
  refine TensorProduct.induction_on a ?_ (fun x y => ?_) fun x y hx hy => ?_
  · exact ⟨M', N', hM', hN', Set.insert_subset (zero_mem _) h⟩
  · refine ⟨_, _, hM'.sup (fg_span_singleton x),
      hN'.sup (fg_span_singleton y), Set.insert_subset ?_ fun z hz => ?_⟩
    · exact ⟨⟨x, mem_sup_right (mem_span_singleton_self x)⟩ otimesₜ
        ⟨y, mem_sup_right (mem_span_singleton_self y)⟩, rfl⟩
    · exact range_mapIncl_mono le_sup_left le_sup_left (h hz)
  · obtain ⟨M₁', N₁', hM₁', hN₁', h₁⟩ := hx
    obtain ⟨M₂', N₂', hM₂', hN₂', h₂⟩ := hy
    refine ⟨_, _, hM₁'.sup hM₂', hN₁'.sup hN₂', Set.insert_subset (add_mem ?_ ?_) fun z hz => ?_⟩
    · exact range_mapIncl_mono le_sup_left le_sup_left (h₁ (Set.mem_insert x s))
    · exact range_mapIncl_mono le_sup_right le_sup_right (h₂ (Set.mem_insert y s))
    · exact range_mapIncl_mono le_sup_left le_sup_left (h₁ (Set.subset_insert x s hz))

/--
theorem `exists_finite_submodule_left_of_setFinite` / 定理 `exists_finite_submodule_left_of_setFinite`

English:
theorem exists_finite_submodule_left_of_setFinite
  given: (s : Set (M otimes[R] N)) (hs : s.Finite)
  proof: by
  obtain ⟨M', _, hfin, _, h⟩ := exists_finite_submodule_of_setFinite s hs
  refine ⟨M', hfin, ?_⟩
  rw [mapIncl]; rw [← LinearMap.rTensor_comp_lTensor] at h
  exact h.trans (LinearMap.range_comp_le_range _ _)

中文:
定理 存在_finite_submodule_left_of_setFinite
  条件: (s : 集合 (M otimes[R] N)) (hs : s.有限)
  证明: by
  obtain ⟨M', _, hfin, _, h⟩ := exists_finite_submodule_of_setFinite s hs
  refine ⟨M', hfin, ?_⟩
  rw [mapIncl]; rw [← LinearMap.rTensor_comp_lTensor] at h
  exact h.trans (LinearMap.range_comp_le_range _ _)

Depends on / 依赖: LinearMap, LinearMap.rTensor_comp_lTensor, LinearMap.range_comp_le_range, exists_finite_submodule_of_setFinite, h.trans, mapIncl, rTensor_comp_lTensor, range_comp_le_range
-/
theorem exists_finite_submodule_left_of_setFinite (s : Set (M otimes[R] N)) (hs : s.Finite) :
    exists M' : Submodule R M, Module.Finite R M' ∧ s subseteq LinearMap.range (M'.subtype.rTensor N) := by
  obtain ⟨M', _, hfin, _, h⟩ := exists_finite_submodule_of_setFinite s hs
  refine ⟨M', hfin, ?_⟩
  rw [mapIncl]; rw [← LinearMap.rTensor_comp_lTensor] at h
  exact h.trans (LinearMap.range_comp_le_range _ _)

/--
theorem `exists_finite_submodule_right_of_setFinite` / 定理 `exists_finite_submodule_right_of_setFinite`

English:
theorem exists_finite_submodule_right_of_setFinite
  given: (s : Set (M otimes[R] N)) (hs : s.Finite)
  proof: by
  obtain ⟨_, N', _, hfin, h⟩ := exists_finite_submodule_of_setFinite s hs
  refine ⟨N', hfin, ?_⟩
  rw [mapIncl]; rw [← LinearMap.lTensor_comp_rTensor] at h
  exact h.trans (LinearMap.range_comp_le_range _ _)

中文:
定理 存在_finite_submodule_right_of_setFinite
  条件: (s : 集合 (M otimes[R] N)) (hs : s.有限)
  证明: by
  obtain ⟨_, N', _, hfin, h⟩ := exists_finite_submodule_of_setFinite s hs
  refine ⟨N', hfin, ?_⟩
  rw [mapIncl]; rw [← LinearMap.lTensor_comp_rTensor] at h
  exact h.trans (LinearMap.range_comp_le_range _ _)

Depends on / 依赖: LinearMap, LinearMap.lTensor_comp_rTensor, LinearMap.range_comp_le_range, exists_finite_submodule_of_setFinite, h.trans, lTensor_comp_rTensor, mapIncl, range_comp_le_range
-/
theorem exists_finite_submodule_right_of_setFinite (s : Set (M otimes[R] N)) (hs : s.Finite) :
    exists N' : Submodule R N, Module.Finite R N' ∧ s subseteq LinearMap.range (N'.subtype.lTensor M) := by
  obtain ⟨_, N', _, hfin, h⟩ := exists_finite_submodule_of_setFinite s hs
  refine ⟨N', hfin, ?_⟩
  rw [mapIncl]; rw [← LinearMap.lTensor_comp_rTensor] at h
  exact h.trans (LinearMap.range_comp_le_range _ _)

/--
theorem `exists_finite_submodule_of_setFinite'` / 定理 `exists_finite_submodule_of_setFinite'`

English:
theorem exists_finite_submodule_of_setFinite'
  given: (s : Set (M₁ otimes[R] N₁)) (hs : s.Finite)
  proof: by
  obtain ⟨M', N', _, _, h⟩ := exists_finite_submodule_of_setFinite s hs
  have hM := map_subtype_le M₁ M'
  have hN := map_subtype_le N₁ N'
  refine ⟨_, _, hM, hN, .map _ _, .map _ _, ?_⟩
  rw [mapIncl]; rw [show M'.subtype = inclusion hM ∘ₗ M₁.subtype.submoduleMap M' by ext; simp]; rw [show N'.s

中文:
定理 存在_finite_submodule_of_setFinite'
  条件: (s : 集合 (M₁ otimes[R] N₁)) (hs : s.有限)
  证明: by
  obtain ⟨M', N', _, _, h⟩ := exists_finite_submodule_of_setFinite s hs
  have hM := map_subtype_le M₁ M'
  have hN := map_subtype_le N₁ N'
  refine ⟨_, _, hM, hN, .map _ _, .map _ _, ?_⟩
  rw [mapIncl]; rw [show M'.subtype = inclusion hM ∘ₗ M₁.subtype.submoduleMap M' by ext; simp]; rw [show N'.s

Depends on / 依赖: LinearMap, LinearMap.range_comp_le_range, exists_finite_submodule_of_setFinite, h.trans, inclusion, mapIncl, map_comp, map_subtype_le, range_comp_le_range, submoduleMap, subtype, subtype.submoduleMap
-/
theorem exists_finite_submodule_of_setFinite' (s : Set (M₁ otimes[R] N₁)) (hs : s.Finite) :
    exists (M' : Submodule R M) (N' : Submodule R N) (hM : M' <= M₁) (hN : N' <= N₁),
      Module.Finite R M' ∧ Module.Finite R N' ∧
        s subseteq LinearMap.range (TensorProduct.map (inclusion hM) (inclusion hN)) := by
  obtain ⟨M', N', _, _, h⟩ := exists_finite_submodule_of_setFinite s hs
  have hM := map_subtype_le M₁ M'
  have hN := map_subtype_le N₁ N'
  refine ⟨_, _, hM, hN, .map _ _, .map _ _, ?_⟩
  rw [mapIncl]; rw [show M'.subtype = inclusion hM ∘ₗ M₁.subtype.submoduleMap M' by ext; simp]; rw [show N'.subtype = inclusion hN ∘ₗ N₁.subtype.submoduleMap N' by ext; simp]; rw [map_comp] at h
  exact h.trans (LinearMap.range_comp_le_range _ _)

/--
theorem `exists_finite_submodule_left_of_setFinite'` / 定理 `exists_finite_submodule_left_of_setFinite'`

English:
theorem exists_finite_submodule_left_of_setFinite'
  given: (s : Set (M₁ otimes[R] N₁)) (hs : s.Finite)
  proof: by
  obtain ⟨M', _, hM, _, hfin, _, h⟩ := exists_finite_submodule_of_setFinite' s hs
  refine ⟨M', hM, hfin, ?_⟩
  rw [← LinearMap.rTensor_comp_lTensor] at h
  exact h.trans (LinearMap.range_comp_le_range _ _)

中文:
定理 存在_finite_submodule_left_of_setFinite'
  条件: (s : 集合 (M₁ otimes[R] N₁)) (hs : s.有限)
  证明: by
  obtain ⟨M', _, hM, _, hfin, _, h⟩ := exists_finite_submodule_of_setFinite' s hs
  refine ⟨M', hM, hfin, ?_⟩
  rw [← LinearMap.rTensor_comp_lTensor] at h
  exact h.trans (LinearMap.range_comp_le_range _ _)

Depends on / 依赖: LinearMap, LinearMap.rTensor_comp_lTensor, LinearMap.range_comp_le_range, exists_finite_submodule_of_setFinite, h.trans, rTensor_comp_lTensor, range_comp_le_range
-/
theorem exists_finite_submodule_left_of_setFinite' (s : Set (M₁ otimes[R] N₁)) (hs : s.Finite) :
    exists (M' : Submodule R M) (hM : M' <= M₁), Module.Finite R M' ∧
      s subseteq LinearMap.range ((inclusion hM).rTensor N₁) := by
  obtain ⟨M', _, hM, _, hfin, _, h⟩ := exists_finite_submodule_of_setFinite' s hs
  refine ⟨M', hM, hfin, ?_⟩
  rw [← LinearMap.rTensor_comp_lTensor] at h
  exact h.trans (LinearMap.range_comp_le_range _ _)

/--
theorem `exists_finite_submodule_right_of_setFinite'` / 定理 `exists_finite_submodule_right_of_setFinite'`

English:
theorem exists_finite_submodule_right_of_setFinite'
  given: (s : Set (M₁ otimes[R] N₁)) (hs : s.Finite)
  proof: by
  obtain ⟨_, N', _, hN, _, hfin, h⟩ := exists_finite_submodule_of_setFinite' s hs
  refine ⟨N', hN, hfin, ?_⟩
  rw [← LinearMap.lTensor_comp_rTensor] at h
  exact h.trans (LinearMap.range_comp_le_range _ _)

中文:
定理 存在_finite_submodule_right_of_setFinite'
  条件: (s : 集合 (M₁ otimes[R] N₁)) (hs : s.有限)
  证明: by
  obtain ⟨_, N', _, hN, _, hfin, h⟩ := exists_finite_submodule_of_setFinite' s hs
  refine ⟨N', hN, hfin, ?_⟩
  rw [← LinearMap.lTensor_comp_rTensor] at h
  exact h.trans (LinearMap.range_comp_le_range _ _)

Depends on / 依赖: LinearMap, LinearMap.lTensor_comp_rTensor, LinearMap.range_comp_le_range, exists_finite_submodule_of_setFinite, h.trans, lTensor_comp_rTensor, range_comp_le_range
-/
theorem exists_finite_submodule_right_of_setFinite' (s : Set (M₁ otimes[R] N₁)) (hs : s.Finite) :
    exists (N' : Submodule R N) (hN : N' <= N₁), Module.Finite R N' ∧
      s subseteq LinearMap.range ((inclusion hN).lTensor M₁) := by
  obtain ⟨_, N', _, hN, _, hfin, h⟩ := exists_finite_submodule_of_setFinite' s hs
  refine ⟨N', hN, hfin, ?_⟩
  rw [← LinearMap.lTensor_comp_rTensor] at h
  exact h.trans (LinearMap.range_comp_le_range _ _)

/--
lemma `exists_sum_tmul_eq` / 引理 `exists_sum_tmul_eq`

English:
lemma exists_sum_tmul_eq
  given: (x : M otimes[R] N)
  proof: by
  induction x with
  | zero => exact ⟨0, IsEmpty.elim inferInstance, IsEmpty.elim inferInstance, by simp⟩
  | tmul x y => exact ⟨1, fun _ => x, fun _ => y, by simp⟩
  | add x y hx hy =>
    obtain ⟨kx, mx, nx, rfl⟩ := hx
    obtain ⟨ky, my, ny, rfl⟩ := hy
    use kx + ky, Fin.addCases mx my, Fin.

中文:
引理 存在_sum_tmul_eq
  条件: (x : M otimes[R] N)
  证明: by
  induction x with
  | zero => exact ⟨0, IsEmpty.elim inferInstance, IsEmpty.elim inferInstance, by simp⟩
  | tmul x y => exact ⟨1, fun _ => x, fun _ => y, by simp⟩
  | add x y hx hy =>
    obtain ⟨kx, mx, nx, rfl⟩ := hx
    obtain ⟨ky, my, ny, rfl⟩ := hy
    use kx + ky, Fin.addCases mx my, Fin.

Depends on / 依赖: Fin.addCases, Fin.sum_univ_add, IsEmpty, IsEmpty.elim, addCases, sum_univ_add
-/
lemma exists_sum_tmul_eq (x : M otimes[R] N) :
    exists (k : Nat) (m : Fin k -> M) (n : Fin k -> N), x = ∑ j, m j otimesₜ n j := by
  induction x with
  | zero => exact ⟨0, IsEmpty.elim inferInstance, IsEmpty.elim inferInstance, by simp⟩
  | tmul x y => exact ⟨1, fun _ => x, fun _ => y, by simp⟩
  | add x y hx hy =>
    obtain ⟨kx, mx, nx, rfl⟩ := hx
    obtain ⟨ky, my, ny, rfl⟩ := hy
    use kx + ky, Fin.addCases mx my, Fin.addCases nx ny
    simp [Fin.sum_univ_add]

end TensorProduct
