/-
Copyright (c) 2025 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll, Patrick Massot, Anatole Dedecker
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Order.Filter.IsBounded
public import Mathlib.Topology.Algebra.UniformField

/-!
# A normed field is a completable topological field
-/

public section

open SeminormedAddGroup IsUniformAddGroup Filter

variable {F : Type*} [NormedField F]

/--
Instance `NormedField.instCompletableTopField` / 实例 `NormedField.instCompletableTopField`

English:
instance NormedField.instCompletableTopField
  signature: : CompletableTopField F where
  body: by
obtain ⟨δ, δ_pos, hδ⟩ := (disjoint_nhds_zero ..).mp disjoint_iff.mpr hn
    have f_bdd : f.IsBoundedUnder (· <= ·) (‖·⁻¹‖) :=
      ⟨δ⁻¹, hδ.mono fun y hy => le_inv_of_le_inv₀ δ_pos (by simpa using hy)⟩
    have h₀ : forallᶠ y in f, y != 0 := hδ.mono fun y hy => by simpa using δ_pos.trans_le hy
 

中文:
实例 NormedField.instCompletableTopField
  签名: : CompletableTopField F where
  定义体: by
obtain ⟨δ, δ_pos, hδ⟩ := (disjoint_nhds_zero ..).mp disjoint_iff.mpr hn
    have f_bdd : f.IsBoundedUnder (· <= ·) (‖·⁻¹‖) :=
      ⟨δ⁻¹, hδ.mono fun y hy => le_inv_of_le_inv₀ δ_pos (by simpa using hy)⟩
    have h₀ : forallᶠ y in f, y != 0 := hδ.mono fun y hy => by simpa using δ_pos.trans_le hy
 

Depends on / 依赖: IsBoundedUnder, _pos.trans_le, cauchy_iff_tendsto_swapped, cauchy_map_iff_tends, disjoint_iff, disjoint_iff.mpr, disjoint_nhds_zero, f.IsBoundedUnder, f_bdd, mul_sub, prod_mk, sub_mul, trans_le
-/
instance NormedField.instCompletableTopField : CompletableTopField F where
  nice f hc hn := by
obtain ⟨δ, δ_pos, hδ⟩ := (disjoint_nhds_zero ..).mp disjoint_iff.mpr hn
    have f_bdd : f.IsBoundedUnder (· <= ·) (‖·⁻¹‖) :=
      ⟨δ⁻¹, hδ.mono fun y hy => le_inv_of_le_inv₀ δ_pos (by simpa using hy)⟩
    have h₀ : forallᶠ y in f, y != 0 := hδ.mono fun y hy => by simpa using δ_pos.trans_le hy
    have : forallᶠ p in f ×ˢ f, p.1⁻¹ - p.2⁻¹ = p.1⁻¹ * (p.2 - p.1) * p.2⁻¹ :=
.mono fun ⟨x, y⟩ ⟨hx, hy⟩ => by simp [mul_sub, sub_mul, hx, hy] h₀.prod_mk h₀
    rw [cauchy_iff_tendsto_swapped] at hc
    rw [cauchy_map_iff_tendsto]; rw [tendsto_congr' this]
refine ⟨hc.1, .zero_mul_isBoundedUnder_le ?_ tendsto_snd.isBoundedUnder_comp f_bdd⟩
    exact isBoundedUnder_le_mul_tendsto_zero (tendsto_fst.isBoundedUnder_comp f_bdd) hc.2
