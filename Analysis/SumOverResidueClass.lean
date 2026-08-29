/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Sums over residue classes

We consider infinite sums over functions `f` on `ℕ`, restricted to a residue class mod `m`.

The main result is `summable_indicator_mod_iff`, which states that when `f : ℕ → ℝ` is
decreasing, then the sum over `f` restricted to any residue class
mod `m ≠ 0` converges if and only if the sum over all of `ℕ` converges.
-/

public section


/--
lemma `Finset.sum_indicator_mod` / 引理 `Finset.sum_indicator_mod`

English:
lemma Finset.sum_indicator_mod
  given: {R : Type*} [AddCommMonoid R] (m : Nat) [NeZero m] (f : Nat -> R)
  proof: by
  ext n
  simp only [Finset.sum_apply, Set.indicator_apply, Set.mem_ofPred_eq, Finset.sum_ite_eq,
    Finset.mem_univ, ↓reduceIte]

中文:
引理 有限集.sum_indicator_mod
  条件: {R : 类型} [加法交换幺半群 R] (m : 自然数) [NeZero m] (f : 自然数 -> R)
  证明: by
  ext n
  simp only [Finset.sum_apply, Set.indicator_apply, Set.mem_ofPred_eq, Finset.sum_ite_eq,
    Finset.mem_univ, ↓reduceIte]

Depends on / 依赖: Finset, Finset.mem_univ, Finset.sum_apply, Finset.sum_ite_eq, Preorder, Set.indicator_apply, Set.mem_ofPred_eq, indicator_apply, isCofiltered_of_directed_ge_nonempty, mem_ofPred_eq, mem_univ, reduceIte, sum_apply, sum_ite_eq
-/
lemma Finset.sum_indicator_mod {R : Type*} [AddCommMonoid R] (m : Nat) [NeZero m] (f : Nat -> R) :
    f = ∑ a : ZMod m, {n : Nat | (n : ZMod m) = a}.indicator f := by
  ext n
  simp only [Finset.sum_apply, Set.indicator_apply, Set.mem_ofPred_eq, Finset.sum_ite_eq,
    Finset.mem_univ, ↓reduceIte]

set_option backward.isDefEq.respectTransparency false in
open Set in
/--
lemma `summable_indicator_mod_iff_summable` / 引理 `summable_indicator_mod_iff_summable`

English:
lemma summable_indicator_mod_iff_summable
  statement: {R : Type*} [AddCommGroup R] [TopologicalSpace R]
  proof: by
  trans Summable ({n : Nat | (n : ZMod m) = k ∧ k <= n}.indicator f)
  · rw [← (finite_lt_nat k).summable_compl_iff (f := {n : Nat | (n : ZMod m) = k}.indicator f)]
    simp only [summable_subtype_iff_indicator, indicator_indicator, inter_comm, ofPred_and,
      compl_ofPred, not_lt]
  · let g : 

中文:
引理 summable_indicator_mod_iff_summable
  结论: {R : 类型} [加法交换群 R] [拓扑空间 R]
  证明: by
  trans Summable ({n : Nat | (n : ZMod m) = k ∧ k <= n}.indicator f)
  · rw [← (finite_lt_nat k).summable_compl_iff (f := {n : Nat | (n : ZMod m) = k}.indicator f)]
    simp only [summable_subtype_iff_indicator, indicator_indicator, inter_comm, ofPred_and,
      compl_ofPred, not_lt]
  · let g : 

Depends on / 依赖: Function, Function.Injective, Injective, Summable, compl_ofPred, finite_lt_nat, hm.ne, indicator, indicator_indicator, inter_comm, not_lt, ofPred_and, summable_compl_iff, summable_subtype_iff_indicator
-/
lemma summable_indicator_mod_iff_summable {R : Type*} [AddCommGroup R] [TopologicalSpace R]
    [IsTopologicalAddGroup R] (m : Nat) [hm : NeZero m] (k : Nat) (f : Nat -> R) :
    Summable ({n : Nat | (n : ZMod m) = k}.indicator f) ↔ Summable fun n => f (m * n + k) := by
  trans Summable ({n : Nat | (n : ZMod m) = k ∧ k <= n}.indicator f)
  · rw [← (finite_lt_nat k).summable_compl_iff (f := {n : Nat | (n : ZMod m) = k}.indicator f)]
    simp only [summable_subtype_iff_indicator, indicator_indicator, inter_comm, ofPred_and,
      compl_ofPred, not_lt]
  · let g : Nat -> Nat := fun n => m * n + k
    have hg : Function.Injective g := fun m n hmn => by simpa [g, hm.ne] using hmn
    have hg' : forall n ∉ range g, {n : Nat | (n : ZMod m) = k ∧ k <= n}.indicator f n = 0 := by
      intro n hn
      contrapose! hn
      exact (Nat.range_mul_add m k).symm ▸ mem_of_indicator_ne_zero hn
    convert (Function.Injective.summable_iff hg hg').symm
    simp only [Function.comp_apply, mem_ofPred_eq, Nat.cast_add, Nat.cast_mul, CharP.cast_eq_zero,
      zero_mul, zero_add, le_add_iff_nonneg_left, zero_le, and_self, indicator_of_mem, g]

/--
lemma `not_summable_of_antitone_of_neg` / 引理 `not_summable_of_antitone_of_neg`

English:
lemma not_summable_of_antitone_of_neg
  given: {f : Nat -> Real} (hf : Antitone f) {n : Nat} (hn : f n < 0)
  proof: by
  intro hs
  have := hs.tendsto_atTop_zero
  simp only [Metric.tendsto_atTop, dist_zero_right, Real.norm_eq_abs] at this
  obtain ⟨N, hN⟩ := this (|f n|) (abs_pos_of_neg hn)
  specialize hN (max n N) (n.le_max_right N)
  contrapose! hN; clear hN
  have H : f (max n N) <= f n := hf (n.le_max_left 

中文:
引理 not_summable_of_antitone_of_neg
  条件: {f : 自然数 -> 实数} (hf : 递减 f) {n : 自然数} (hn : f n < 0)
  证明: by
  intro hs
  have := hs.tendsto_atTop_zero
  simp only [Metric.tendsto_atTop, dist_zero_right, Real.norm_eq_abs] at this
  obtain ⟨N, hN⟩ := this (|f n|) (abs_pos_of_neg hn)
  specialize hN (max n N) (n.le_max_right N)
  contrapose! hN; clear hN
  have H : f (max n N) <= f n := hf (n.le_max_left 

Depends on / 依赖: H.trans_lt, Metric, Metric.tendsto_atTop, Real.norm_eq_abs, abs_of_neg, abs_pos_of_neg, contrapose, dist_zero_right, hs.tendsto_atTop_zero, le_max_left, le_max_right, n.le_max_left, n.le_max_right, neg_le_neg_iff, norm_eq_abs, specialize, tendsto_atTop, tendsto_atTop_zero, trans_lt
-/
lemma not_summable_of_antitone_of_neg {f : Nat -> Real} (hf : Antitone f) {n : Nat} (hn : f n < 0) :
    ¬ Summable f := by
  intro hs
  have := hs.tendsto_atTop_zero
  simp only [Metric.tendsto_atTop, dist_zero_right, Real.norm_eq_abs] at this
  obtain ⟨N, hN⟩ := this (|f n|) (abs_pos_of_neg hn)
  specialize hN (max n N) (n.le_max_right N)
  contrapose! hN; clear hN
  have H : f (max n N) <= f n := hf (n.le_max_left N)
  rwa [abs_of_neg hn, abs_of_neg (H.trans_lt hn), neg_le_neg_iff]

/--
lemma `not_summable_indicator_mod_of_antitone_of_neg` / 引理 `not_summable_indicator_mod_of_antitone_of_neg`

English:
lemma not_summable_indicator_mod_of_antitone_of_neg
  statement: {m : Nat} [hm : NeZero m] {f : Nat -> Real}
  proof: by
  rw [← ZMod.natCast_zmod_val k]; rw [summable_indicator_mod_iff_summable]
  exact not_summable_of_antitone_of_neg
(hf.comp_monotone <| (Covariant.monotone_of_const m).add_const k.val)
    (hf <| (Nat.le_mul_of_pos_left n Fin.pos').trans <| Nat.le_add_right ..).trans_lt hn

中文:
引理 not_summable_indicator_mod_of_antitone_of_neg
  结论: {m : 自然数} [hm : NeZero m] {f : 自然数 -> 实数}
  证明: by
  rw [← ZMod.natCast_zmod_val k]; rw [summable_indicator_mod_iff_summable]
  exact not_summable_of_antitone_of_neg
(hf.comp_monotone <| (Covariant.monotone_of_const m).add_const k.val)
    (hf <| (Nat.le_mul_of_pos_left n Fin.pos').trans <| Nat.le_add_right ..).trans_lt hn

Depends on / 依赖: Covariant, Covariant.monotone_of_const, Fin.pos, Nat.le_add_right, Nat.le_mul_of_pos_left, ZMod.natCast_zmod_val, add_const, comp_monotone, hf.comp_monotone, k.val, le_add_right, le_mul_of_pos_left, monotone_of_const, natCast_zmod_val, not_summable_of_antitone_of_neg, summable_indicator_mod_iff_summable, trans_lt
-/
lemma not_summable_indicator_mod_of_antitone_of_neg {m : Nat} [hm : NeZero m] {f : Nat -> Real}
    (hf : Antitone f) {n : Nat} (hn : f n < 0) (k : ZMod m) :
    ¬ Summable ({n : Nat | (n : ZMod m) = k}.indicator f) := by
  rw [← ZMod.natCast_zmod_val k]; rw [summable_indicator_mod_iff_summable]
  exact not_summable_of_antitone_of_neg
(hf.comp_monotone <| (Covariant.monotone_of_const m).add_const k.val)
    (hf <| (Nat.le_mul_of_pos_left n Fin.pos').trans <| Nat.le_add_right ..).trans_lt hn

/--
lemma `summable_indicator_mod_iff_summable_indicator_mod` / 引理 `summable_indicator_mod_iff_summable_indicator_mod`

English:
lemma summable_indicator_mod_iff_summable_indicator_mod
  statement: {m : Nat} [NeZero m] {f : Nat -> Real}
  proof: by
  by_cases! hf₀ : forall n, 0 <= f n -- the interesting case
  · rw [← ZMod.natCast_zmod_val k, summable_indicator_mod_iff_summable] at hs
    have hl : (l.val + m : ZMod m) = l := by
      simp only [ZMod.natCast_val, ZMod.cast_id', id_eq, CharP.cast_eq_zero, add_zero]
    rw [← hl]; rw [← Nat.c

中文:
引理 summable_indicator_mod_iff_summable_indicator_mod
  结论: {m : 自然数} [NeZero m] {f : 自然数 -> 实数}
  证明: by
  by_cases! hf₀ : forall n, 0 <= f n -- the interesting case
  · rw [← ZMod.natCast_zmod_val k, summable_indicator_mod_iff_summable] at hs
    have hl : (l.val + m : ZMod m) = l := by
      simp only [ZMod.natCast_val, ZMod.cast_id', id_eq, CharP.cast_eq_zero, add_zero]
    rw [← hl]; rw [← Nat.c

Depends on / 依赖: CharP.cast_eq_zero, Nat.add_le_add, Nat.cast_add, Nat.le.refl, ZMod.cast_id, ZMod.natCast_val, ZMod.natCast_zmod_val, add_le_add, add_zero, cast_add, cast_eq_zero, cast_id, hs.of_nonneg_of_le, id_eq, interesting, k.val_lt.trans_le, l.val, le_add_left, m.le_add_left, natCast_val
-/
lemma summable_indicator_mod_iff_summable_indicator_mod {m : Nat} [NeZero m] {f : Nat -> Real}
    (hf : Antitone f) {k : ZMod m} (l : ZMod m)
    (hs : Summable ({n : Nat | (n : ZMod m) = k}.indicator f)) :
    Summable ({n : Nat | (n : ZMod m) = l}.indicator f) := by
  by_cases! hf₀ : forall n, 0 <= f n -- the interesting case
  · rw [← ZMod.natCast_zmod_val k, summable_indicator_mod_iff_summable] at hs
    have hl : (l.val + m : ZMod m) = l := by
      simp only [ZMod.natCast_val, ZMod.cast_id', id_eq, CharP.cast_eq_zero, add_zero]
    rw [← hl]; rw [← Nat.cast_add]; rw [summable_indicator_mod_iff_summable]
    exact hs.of_nonneg_of_le (fun _ => hf₀ _)
fun _ => hf Nat.add_le_add Nat.le.refl (k.val_lt.trans_le <| m.le_add_left l.val).le
  · obtain ⟨n, hn⟩ := hf₀
    exact (not_summable_indicator_mod_of_antitone_of_neg hf hn k hs).elim

/--
lemma `summable_indicator_mod_iff` / 引理 `summable_indicator_mod_iff`

English:
lemma summable_indicator_mod_iff
  given: {m : Nat} [NeZero m] {f : Nat -> Real} (hf : Antitone f) (k : ZMod m)
  proof: by
  refine ⟨fun H => ?_, fun H => Summable.indicator H _⟩
  rw [Finset.sum_indicator_mod m f]
  convert!
    summable_sum (s := Finset.univ) fun a _ =>
      summable_indicator_mod_iff_summable_indicator_mod hf a H
  simp only [Finset.sum_apply]

中文:
引理 summable_indicator_mod_iff
  条件: {m : 自然数} [NeZero m] {f : 自然数 -> 实数} (hf : 递减 f) (k : ZMod m)
  证明: by
  refine ⟨fun H => ?_, fun H => Summable.indicator H _⟩
  rw [Finset.sum_indicator_mod m f]
  convert!
    summable_sum (s := Finset.univ) fun a _ =>
      summable_indicator_mod_iff_summable_indicator_mod hf a H
  simp only [Finset.sum_apply]

Depends on / 依赖: Finset, Finset.sum_apply, Finset.sum_indicator_mod, Finset.univ, Summable, Summable.indicator, convert, indicator, sum_apply, sum_indicator_mod, summable_indicator_mod_iff_summable_indicator_mod, summable_sum
-/
lemma summable_indicator_mod_iff {m : Nat} [NeZero m] {f : Nat -> Real} (hf : Antitone f) (k : ZMod m) :
    Summable ({n : Nat | (n : ZMod m) = k}.indicator f) ↔ Summable f := by
  refine ⟨fun H => ?_, fun H => Summable.indicator H _⟩
  rw [Finset.sum_indicator_mod m f]
  convert!
    summable_sum (s := Finset.univ) fun a _ =>
      summable_indicator_mod_iff_summable_indicator_mod hf a H
  simp only [Finset.sum_apply]

open ZMod

set_option backward.isDefEq.respectTransparency false in
/--
lemma `Nat.sumByResidueClasses` / 引理 `Nat.sumByResidueClasses`

English:
lemma Nat.sumByResidueClasses
  statement: {R : Type*} [AddCommGroup R] [UniformSpace R] [IsUniformAddGroup R]
  proof: by
  rw [← (residueClassesEquiv N).symm.tsum_eq f]; rw [Summable.tsum_prod]; rw [tsum_fintype]; rw [residueClassesEquiv]; rw [Equiv.coe_fn_symm_mk]
  exact hf.comp_injective (residueClassesEquiv N).symm.injective

中文:
引理 自然数.sumByResidueClasses
  结论: {R : 类型} [加法交换群 R] [一致空间 R] [是UniformAdd群 R]
  证明: by
  rw [← (residueClassesEquiv N).symm.tsum_eq f]; rw [Summable.tsum_prod]; rw [tsum_fintype]; rw [residueClassesEquiv]; rw [Equiv.coe_fn_symm_mk]
  exact hf.comp_injective (residueClassesEquiv N).symm.injective

Depends on / 依赖: Equiv.coe_fn_symm_mk, Summable, Summable.tsum_prod, coe_fn_symm_mk, comp_injective, hf.comp_injective, injective, residueClassesEquiv, symm.injective, symm.tsum_eq, tsum_eq, tsum_fintype, tsum_prod
-/
lemma Nat.sumByResidueClasses {R : Type*} [AddCommGroup R] [UniformSpace R] [IsUniformAddGroup R]
    [CompleteSpace R] [T0Space R] {f : Nat -> R} (hf : Summable f) (N : Nat) [NeZero N] :
    ∑' n, f n = ∑ j : ZMod N, ∑' m, f (j.val + N * m) := by
  rw [← (residueClassesEquiv N).symm.tsum_eq f]; rw [Summable.tsum_prod]; rw [tsum_fintype]; rw [residueClassesEquiv]; rw [Equiv.coe_fn_symm_mk]
  exact hf.comp_injective (residueClassesEquiv N).symm.injective
