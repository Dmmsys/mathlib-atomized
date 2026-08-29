/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.LocallyConvex.Bounded
public import Mathlib.Topology.Algebra.Module.Multilinear.Basic

/-!
# Images of (von Neumann) bounded sets under continuous multilinear maps

In this file we prove that continuous multilinear maps
send von Neumann bounded sets to von Neumann bounded sets.

We prove 2 versions of the theorem:
one assumes that the index type is nonempty,
and the other assumes that the codomain is a topological vector space.

## Implementation notes

We do not assume the index type `ι` to be finite.
While for a nonzero continuous multilinear map
the family `∀ i, E i` has to be essentially finite
(more precisely, all but finitely many `E i` has to be trivial),
proving theorems without a `[Finite ι]` assumption saves us some typeclass searches here and there.
-/

public section

open Bornology Filter Set Function
open scoped Topology

namespace Bornology.IsVonNBounded

variable {ι 𝕜 F : Type*} {E : ι -> Type*} [NormedField 𝕜]
  [forall i, AddCommGroup (E i)] [forall i, Module 𝕜 (E i)] [forall i, TopologicalSpace (E i)]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]

/--
theorem `image_multilinear'` / 定理 `image_multilinear'`

English:
theorem image_multilinear'
  statement: [Nonempty ι] {s : Set (forall i, E i)} (hs : IsVonNBounded 𝕜 s)
  proof: fun V hV => by
  classical
  if h₁ : forall c : 𝕜, ‖c‖ <= 1 then
    exact absorbs_iff_norm.2 ⟨2, fun c hc => by linarith [h₁ c]⟩
  else
    let _ : NontriviallyNormedField 𝕜 := ⟨by simpa using h₁⟩
    obtain ⟨I, t, ht₀, hft⟩ :
        exists (I : Finset ι) (t : forall i, Set (E i)), (forall i, t i in 𝓝 0) ∧ Set.pi I t subseteq f ⁻¹' V := by
      have hfV : f ⁻¹' V in 𝓝 0 := (map_continuous f).tendsto' _ _ f.map_zero hV
      rwa [nhds_pi, Filter.mem_pi, exists_finite_iff_finset] at hfV
    have : forall i, exists c : 𝕜, c != 0 ∧ forall c' : 𝕜, ‖c'‖ <= ‖c‖ -> forall x in s, c' • x i in t i := fun i => by
      rw [isVonNBounded_pi_iff] at hs
      have := (hs i).tendsto_smallSets_nhds.eventually (mem_lift' (ht₀ i))
      rcases NormedAddGroup.nhds_zero_basis_norm_lt.eventually_iff.1 this with ⟨r, hr₀, hr⟩
      rcases NormedField.exists_norm_lt 𝕜 hr₀ with ⟨c, hc₀, hc⟩
      refine ⟨c, norm_pos_iff.1 hc₀, fun c' hle x hx => ?_⟩
      exact hr (hle.trans_lt hc) ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    choose c hc₀ hc using this
    rw [absorbs_iff_eventually_nhds_zero (mem_of_mem_nhds hV)]; rw [NormedAddGroup.nhds_zero_basis_norm_lt.eventually_iff]
    have hc₀' : ∏ i in I, c i != 0 := Finset.prod_ne_zero_iff.2 fun i _ => hc₀ i
    refine ⟨‖∏ i in I, c i‖, norm_pos_iff.2 hc₀', fun a ha => mapsTo_image_iff.2 fun x hx => ?_⟩
    let ⟨i₀⟩ := ‹Nonempty ι›
    set y := I.piecewise (fun i => c i • x i) x
    calc
      f (update y i₀ ((a / ∏ i in I, c i) • y i₀)) in V := hft fun i hi => by
        rcases eq_or_ne i i₀ with rfl | hne
        · simp_rw [update_self, y, I.piecewise_eq_of_mem _ _ hi, smul_smul]
          refine hc _ _ ?_ _ hx
          calc
            ‖(a / ∏ i in I, c i) * c i‖ <= (‖∏ i in I, c i‖ / ‖∏ i in I, c i‖) * ‖c i‖ := by
              rw [norm_mul]; rw [norm_div]; gcongr; exact ha.out.le
            _ <= 1 * ‖c i‖ := by gcongr; apply div_self_le_one
            _ = ‖c i‖ := one_mul _
        · simp_rw [update_of_ne hne, y, I.piecewise_eq_of_mem _ _ hi]
          exact hc _ _ le_rfl _ hx
      _ = a • f x := by
        rw [f.map_update_smul]; rw [update_eq_self]; rw [f.map_piecewise_smul]; rw [div_eq_mul_inv]; rw [mul_smul]; rw [inv_smul_smul₀ hc₀']

中文:
定理 image_multilinear'
  结论: [非空 ι] {s : 集合 (对任意 i, E i)} (hs : IsVonNBounded 𝕜 s)
  证明: fun V hV => by
  classical
  if h₁ : forall c : 𝕜, ‖c‖ <= 1 then
    exact absorbs_iff_norm.2 ⟨2, fun c hc => by linarith [h₁ c]⟩
  else
    let _ : NontriviallyNormedField 𝕜 := ⟨by simpa using h₁⟩
    obtain ⟨I, t, ht₀, hft⟩ :
        exists (I : Finset ι) (t : forall i, Set (E i)), (forall i, t i in 𝓝 0) ∧ Set.pi I t subseteq f ⁻¹' V := by
      have hfV : f ⁻¹' V in 𝓝 0 := (map_continuous f).tendsto' _ _ f.map_zero hV
      rwa [nhds_pi, Filter.mem_pi, exists_finite_iff_finset] at hfV
    have : forall i, exists c : 𝕜, c != 0 ∧ forall c' : 𝕜, ‖c'‖ <= ‖c‖ -> forall x in s, c' • x i in t i := fun i => by
      rw [isVonNBounded_pi_iff] at hs
      have := (hs i).tendsto_smallSets_nhds.eventually (mem_lift' (ht₀ i))
      rcases NormedAddGroup.nhds_zero_basis_norm_lt.eventually_iff.1 this with ⟨r, hr₀, hr⟩
      rcases NormedField.exists_norm_lt 𝕜 hr₀ with ⟨c, hc₀, hc⟩
      refine ⟨c, norm_pos_iff.1 hc₀, fun c' hle x hx => ?_⟩
      exact hr (hle.trans_lt hc) ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    choose c hc₀ hc using this
    rw [absorbs_iff_eventually_nhds_zero (mem_of_mem_nhds hV)]; rw [NormedAddGroup.nhds_zero_basis_norm_lt.eventually_iff]
    have hc₀' : ∏ i in I, c i != 0 := Finset.prod_ne_zero_iff.2 fun i _ => hc₀ i
    refine ⟨‖∏ i in I, c i‖, norm_pos_iff.2 hc₀', fun a ha => mapsTo_image_iff.2 fun x hx => ?_⟩
    let ⟨i₀⟩ := ‹Nonempty ι›
    set y := I.piecewise (fun i => c i • x i) x
    calc
      f (update y i₀ ((a / ∏ i in I, c i) • y i₀)) in V := hft fun i hi => by
        rcases eq_or_ne i i₀ with rfl | hne
        · simp_rw [update_self, y, I.piecewise_eq_of_mem _ _ hi, smul_smul]
          refine hc _ _ ?_ _ hx
          calc
            ‖(a / ∏ i in I, c i) * c i‖ <= (‖∏ i in I, c i‖ / ‖∏ i in I, c i‖) * ‖c i‖ := by
              rw [norm_mul]; rw [norm_div]; gcongr; exact ha.out.le
            _ <= 1 * ‖c i‖ := by gcongr; apply div_self_le_one
            _ = ‖c i‖ := one_mul _
        · simp_rw [update_of_ne hne, y, I.piecewise_eq_of_mem _ _ hi]
          exact hc _ _ le_rfl _ hx
      _ = a • f x := by
        rw [f.map_update_smul]; rw [update_eq_self]; rw [f.map_piecewise_smul]; rw [div_eq_mul_inv]; rw [mul_smul]; rw [inv_smul_smul₀ hc₀']

Depends on / 依赖: Filter, Filter.mem_pi, Finset, NontriviallyNormedField, Set.pi, absorbs_iff_norm, classical, exists_finite_iff_finset, f.map_zero, map_continuous, map_zero, mem_pi, nhds_pi, subseteq, tendsto
-/
theorem image_multilinear' [Nonempty ι] {s : Set (forall i, E i)} (hs : IsVonNBounded 𝕜 s)
    (f : ContinuousMultilinearMap 𝕜 E F) : IsVonNBounded 𝕜 (f '' s) := fun V hV => by
  classical
  if h₁ : forall c : 𝕜, ‖c‖ <= 1 then
    exact absorbs_iff_norm.2 ⟨2, fun c hc => by linarith [h₁ c]⟩
  else
    let _ : NontriviallyNormedField 𝕜 := ⟨by simpa using h₁⟩
    obtain ⟨I, t, ht₀, hft⟩ :
        exists (I : Finset ι) (t : forall i, Set (E i)), (forall i, t i in 𝓝 0) ∧ Set.pi I t subseteq f ⁻¹' V := by
      have hfV : f ⁻¹' V in 𝓝 0 := (map_continuous f).tendsto' _ _ f.map_zero hV
      rwa [nhds_pi, Filter.mem_pi, exists_finite_iff_finset] at hfV
    have : forall i, exists c : 𝕜, c != 0 ∧ forall c' : 𝕜, ‖c'‖ <= ‖c‖ -> forall x in s, c' • x i in t i := fun i => by
      rw [isVonNBounded_pi_iff] at hs
      have := (hs i).tendsto_smallSets_nhds.eventually (mem_lift' (ht₀ i))
      rcases NormedAddGroup.nhds_zero_basis_norm_lt.eventually_iff.1 this with ⟨r, hr₀, hr⟩
      rcases NormedField.exists_norm_lt 𝕜 hr₀ with ⟨c, hc₀, hc⟩
      refine ⟨c, norm_pos_iff.1 hc₀, fun c' hle x hx => ?_⟩
      exact hr (hle.trans_lt hc) ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    choose c hc₀ hc using this
    rw [absorbs_iff_eventually_nhds_zero (mem_of_mem_nhds hV)]; rw [NormedAddGroup.nhds_zero_basis_norm_lt.eventually_iff]
    have hc₀' : ∏ i in I, c i != 0 := Finset.prod_ne_zero_iff.2 fun i _ => hc₀ i
    refine ⟨‖∏ i in I, c i‖, norm_pos_iff.2 hc₀', fun a ha => mapsTo_image_iff.2 fun x hx => ?_⟩
    let ⟨i₀⟩ := ‹Nonempty ι›
    set y := I.piecewise (fun i => c i • x i) x
    calc
      f (update y i₀ ((a / ∏ i in I, c i) • y i₀)) in V := hft fun i hi => by
        rcases eq_or_ne i i₀ with rfl | hne
        · simp_rw [update_self, y, I.piecewise_eq_of_mem _ _ hi, smul_smul]
          refine hc _ _ ?_ _ hx
          calc
            ‖(a / ∏ i in I, c i) * c i‖ <= (‖∏ i in I, c i‖ / ‖∏ i in I, c i‖) * ‖c i‖ := by
              rw [norm_mul]; rw [norm_div]; gcongr; exact ha.out.le
            _ <= 1 * ‖c i‖ := by gcongr; apply div_self_le_one
            _ = ‖c i‖ := one_mul _
        · simp_rw [update_of_ne hne, y, I.piecewise_eq_of_mem _ _ hi]
          exact hc _ _ le_rfl _ hx
      _ = a • f x := by
        rw [f.map_update_smul]; rw [update_eq_self]; rw [f.map_piecewise_smul]; rw [div_eq_mul_inv]; rw [mul_smul]; rw [inv_smul_smul₀ hc₀']

/--
theorem `image_multilinear` / 定理 `image_multilinear`

English:
theorem image_multilinear
  statement: [ContinuousSMul 𝕜 F] {s : Set (forall i, E i)} (hs : IsVonNBounded 𝕜 s)
  proof: by
  cases isEmpty_or_nonempty ι with
  | inl h =>
exact (isBounded_iff_isVonNBounded _).1
      @Set.Finite.isBounded _ (vonNBornology 𝕜 F) _ (s.toFinite.image _)
  | inr h => exact hs.image_multilinear' f

中文:
定理 image_multilinear
  结论: [连续标量乘法 𝕜 F] {s : 集合 (对任意 i, E i)} (hs : IsVonNBounded 𝕜 s)
  证明: by
  cases isEmpty_or_nonempty ι with
  | inl h =>
exact (isBounded_iff_isVonNBounded _).1
      @Set.Finite.isBounded _ (vonNBornology 𝕜 F) _ (s.toFinite.image _)
  | inr h => exact hs.image_multilinear' f

Depends on / 依赖: Finite, Set.Finite.isBounded, hs.image_multilinear, image_multilinear, isBounded, isBounded_iff_isVonNBounded, isEmpty_or_nonempty, s.toFinite.image, toFinite, vonNBornology
-/
theorem image_multilinear [ContinuousSMul 𝕜 F] {s : Set (forall i, E i)} (hs : IsVonNBounded 𝕜 s)
    (f : ContinuousMultilinearMap 𝕜 E F) : IsVonNBounded 𝕜 (f '' s) := by
  cases isEmpty_or_nonempty ι with
  | inl h =>
exact (isBounded_iff_isVonNBounded _).1
      @Set.Finite.isBounded _ (vonNBornology 𝕜 F) _ (s.toFinite.image _)
  | inr h => exact hs.image_multilinear' f

end IsVonNBounded

end Bornology
