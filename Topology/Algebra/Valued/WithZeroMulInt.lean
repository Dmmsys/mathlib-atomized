/-
Copyright (c) 2025 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.GroupTheory.ArchimedeanDensely
public import Mathlib.Topology.Algebra.Valued.ValuationTopology

/-!
# Topological results for integer-valued rings

This file contains topological results for valuation rings taking values in the
multiplicative integers with zero adjoined. These are useful for cases where there
is a `Valued R ℤₘ₀` instance but no canonical base with which to embed this into
`NNReal`.
-/

public section

open Filter WithZero Set
open scoped Topology

namespace Valued
variable {R Γ₀ : Type*} [Ring R] [LinearOrderedCommGroupWithZero Γ₀]

-- TODO: use ValuativeRel after https://github.com/leanprover-community/mathlib4/issues/26833
/--
lemma `tendsto_zero_pow_of_v_lt_one` / 引理 `tendsto_zero_pow_of_v_lt_one`

English:
lemma tendsto_zero_pow_of_v_lt_one
  given: [MulArchimedean Γ₀] [Valued R Γ₀] {x : R} (hx : v x < 1)
  proof: by
  simp only [(hasBasis_nhds_zero _ _).tendsto_right_iff, mem_ofPred_eq, map_pow, eventually_atTop,
    forall_const]
  intro y
  let v : Valuation R Γ₀ := Valued.v
  obtain ⟨n, hn⟩ := exists_pow_lt₀ hx
    (Units.map (MonoidWithZeroHom.ValueGroup₀.embedding (f := (.ofClass v))) y)
  refine ⟨n, fu

中文:
引理 tendsto_zero_pow_of_v_lt_one
  条件: [MulArchimedean Γ₀] [Valued R Γ₀] {x : R} (hx : v x < 1)
  证明: by
  simp only [(hasBasis_nhds_zero _ _).tendsto_right_iff, mem_ofPred_eq, map_pow, eventually_atTop,
    forall_const]
  intro y
  let v : Valuation R Γ₀ := Valued.v
  obtain ⟨n, hn⟩ := exists_pow_lt₀ hx
    (Units.map (MonoidWithZeroHom.ValueGroup₀.embedding (f := (.ofClass v))) y)
  refine ⟨n, fu

Depends on / 依赖: MonoidWithZeroHom, MonoidWithZeroHom.ValueGroup, Units.map, Valuation, Valuation.restrict_lt_iff_lt_embedding, Valued, Valued.v, embedding, eventually_atTop, forall_const, hasBasis_nhds_zero, hn.trans_le, hx.le, map_pow, mem_ofPred_eq, ofClass, pow_le_pow_right_of_le_one, restrict_lt_iff_lt_embedding, tendsto_right_iff, trans_le
-/
lemma tendsto_zero_pow_of_v_lt_one [MulArchimedean Γ₀] [Valued R Γ₀] {x : R} (hx : v x < 1) :
    Tendsto (fun n : Nat => x ^ n) atTop (𝓝 0) := by
  simp only [(hasBasis_nhds_zero _ _).tendsto_right_iff, mem_ofPred_eq, map_pow, eventually_atTop,
    forall_const]
  intro y
  let v : Valuation R Γ₀ := Valued.v
  obtain ⟨n, hn⟩ := exists_pow_lt₀ hx
    (Units.map (MonoidWithZeroHom.ValueGroup₀.embedding (f := (.ofClass v))) y)
  refine ⟨n, fun m hm => ?_⟩
  rw [← map_pow]; rw [Valuation.restrict_lt_iff_lt_embedding]
  refine hn.trans_le' ?_
  rw [map_pow]
  exact pow_le_pow_right_of_le_one' hx.le hm

/--
lemma `tendsto_zero_pow_of_le_exp_neg_one` / 引理 `tendsto_zero_pow_of_le_exp_neg_one`

English:
lemma tendsto_zero_pow_of_le_exp_neg_one
  given: [Valued R Intᵐ⁰] {x : R} (hx : v x <= exp (-1))
  proof: by
  refine tendsto_zero_pow_of_v_lt_one (hx.trans_lt ?_)
  rw [← exp_zero]; rw [exp_lt_exp]
  simp

中文:
引理 tendsto_zero_pow_of_le_exp_neg_one
  条件: [Valued R 整数ᵐ⁰] {x : R} (hx : v x <= exp (-1))
  证明: by
  refine tendsto_zero_pow_of_v_lt_one (hx.trans_lt ?_)
  rw [← exp_zero]; rw [exp_lt_exp]
  simp

Depends on / 依赖: exp_lt_exp, exp_zero, hx.trans_lt, tendsto_zero_pow_of_v_lt_one, trans_lt
-/
lemma tendsto_zero_pow_of_le_exp_neg_one [Valued R Intᵐ⁰] {x : R} (hx : v x <= exp (-1)) :
    Tendsto (fun n : Nat => x ^ n) atTop (𝓝 0) := by
  refine tendsto_zero_pow_of_v_lt_one (hx.trans_lt ?_)
  rw [← exp_zero]; rw [exp_lt_exp]
  simp

/--
lemma `exists_pow_lt_of_le_exp_neg_one` / 引理 `exists_pow_lt_of_le_exp_neg_one`

English:
lemma exists_pow_lt_of_le_exp_neg_one
  given: [Valued R Intᵐ⁰] {x : R} (hx : v x <= exp (-1)) (γ : Intᵐ⁰ˣ)
  proof: by
  refine exists_pow_lt₀ (hx.trans_lt ?_) _
  rw [← exp_zero]; rw [exp_lt_exp]
  simp

中文:
引理 exists_pow_lt_of_le_exp_neg_one
  条件: [Valued R 整数ᵐ⁰] {x : R} (hx : v x <= exp (-1)) (γ : 整数ᵐ⁰ˣ)
  证明: by
  refine exists_pow_lt₀ (hx.trans_lt ?_) _
  rw [← exp_zero]; rw [exp_lt_exp]
  simp

Depends on / 依赖: exp_lt_exp, exp_zero, hx.trans_lt, trans_lt
-/
lemma exists_pow_lt_of_le_exp_neg_one [Valued R Intᵐ⁰] {x : R} (hx : v x <= exp (-1)) (γ : Intᵐ⁰ˣ) :
    exists n, v x ^ n < γ := by
  refine exists_pow_lt₀ (hx.trans_lt ?_) _
  rw [← exp_zero]; rw [exp_lt_exp]
  simp

end Valued
