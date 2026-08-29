/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Algebra.Field.Periodic
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Topology.Algebra.Order.Archimedean
public import Mathlib.Topology.Algebra.Ring.Real

import Mathlib.Algebra.Order.Monoid.Canonical.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Topological properties of ℝ
-/

public section

assert_not_exists UniformOnFun

noncomputable section

open Filter Int Metric Set TopologicalSpace Bornology
open scoped Topology Uniformity Interval

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

/--
theorem `Real.isTopologicalBasis_Ioo_rat` / 定理 `Real.isTopologicalBasis_Ioo_rat`

English:
theorem Real.isTopologicalBasis_Ioo_rat
  proof: isTopologicalBasis_of_isOpen_of_nhds (by simp +contextual [isOpen_Ioo])
    fun a _ hav hv =>
    let ⟨_, _, ⟨hl, hu⟩, h⟩ := mem_nhds_iff_exists_Ioo_subset.mp (IsOpen.mem_nhds hv hav)
    let ⟨q, hlq, hqa⟩ := exists_rat_btwn hl
    let ⟨p, hap, hpu⟩ := exists_rat_btwn hu
    ⟨Ioo q p, by
      simp 

中文:
定理 Real.isTopologicalBasis_Ioo_rat
  证明: isTopologicalBasis_of_isOpen_of_nhds (by simp +contextual [isOpen_Ioo])
    fun a _ hav hv =>
    let ⟨_, _, ⟨hl, hu⟩, h⟩ := mem_nhds_iff_exists_Ioo_subset.mp (IsOpen.mem_nhds hv hav)
    let ⟨q, hlq, hqa⟩ := exists_rat_btwn hl
    let ⟨p, hap, hpu⟩ := exists_rat_btwn hu
    ⟨Ioo q p, by
      simp 

Depends on / 依赖: IsOpen, IsOpen.mem_nhds, Rat.cast_lt, cast_lt, contextual, exists_rat_btwn, hlq.trans, hqa.trans, isOpen_Ioo, isTopologicalBasis_of_isOpen_of_nhds, mem_iUnion, mem_nhds, mem_nhds_iff_exists_Ioo_subset, mem_nhds_iff_exists_Ioo_subset.mp, p.trans
-/
theorem Real.isTopologicalBasis_Ioo_rat :
    @IsTopologicalBasis Real _ (⋃ (a : Rat) (b : Rat) (_ : a < b), {Ioo (a : Real) b}) :=
  isTopologicalBasis_of_isOpen_of_nhds (by simp +contextual [isOpen_Ioo])
    fun a _ hav hv =>
    let ⟨_, _, ⟨hl, hu⟩, h⟩ := mem_nhds_iff_exists_Ioo_subset.mp (IsOpen.mem_nhds hv hav)
    let ⟨q, hlq, hqa⟩ := exists_rat_btwn hl
    let ⟨p, hap, hpu⟩ := exists_rat_btwn hu
    ⟨Ioo q p, by
      simp only [mem_iUnion]
exact ⟨q, p, Rat.cast_lt.1 hqa.trans hap, rfl⟩, ⟨hqa, hap⟩, fun _ ⟨hqa', ha'p⟩ =>
      h ⟨hlq.trans hqa', ha'p.trans hpu⟩⟩

/--
theorem `Real.mem_closure_iff` / 定理 `Real.mem_closure_iff`

English:
theorem Real.mem_closure_iff
  given: {s : Set Real} {x : Real}
  proof: by
  simp [mem_closure_iff_nhds_basis nhds_basis_ball, Real.dist_eq]

中文:
定理 Real.mem_closure_iff
  条件: {s : Set 实数} {x : 实数}
  证明: by
  simp [mem_closure_iff_nhds_basis nhds_basis_ball, Real.dist_eq]

Depends on / 依赖: Real.dist_eq, dist_eq, mem_closure_iff_nhds_basis, nhds_basis_ball
-/
theorem Real.mem_closure_iff {s : Set Real} {x : Real} :
    x in closure s ↔ forall ε > 0, exists y in s, |y - x| < ε := by
  simp [mem_closure_iff_nhds_basis nhds_basis_ball, Real.dist_eq]

/--
theorem `Real.uniformContinuous_inv` / 定理 `Real.uniformContinuous_inv`

English:
theorem Real.uniformContinuous_inv
  given: (s : Set Real) {r : Real} (r0 : 0 < r) (H : forall x in s, r <= |x|)
  proof: Metric.uniformContinuous_iff.2 fun _ε ε0 =>
    let ⟨δ, δ0, Hδ⟩ := rat_inv_continuous_lemma abs ε0 r0
    ⟨δ, δ0, fun {a b} h => Hδ (H _ a.2) (H _ b.2) h⟩

中文:
定理 Real.uniformContinuous_inv
  条件: (s : Set 实数) {r : 实数} (r0 : 0 < r) (H : 对任意 x in s, r <= |x|)
  证明: Metric.uniformContinuous_iff.2 fun _ε ε0 =>
    let ⟨δ, δ0, Hδ⟩ := rat_inv_continuous_lemma abs ε0 r0
    ⟨δ, δ0, fun {a b} h => Hδ (H _ a.2) (H _ b.2) h⟩

Depends on / 依赖: Metric, Metric.uniformContinuous_iff, rat_inv_continuous_lemma, uniformContinuous_iff
-/
theorem Real.uniformContinuous_inv (s : Set Real) {r : Real} (r0 : 0 < r) (H : forall x in s, r <= |x|) :
    UniformContinuous fun p : s => p.1⁻¹ :=
  Metric.uniformContinuous_iff.2 fun _ε ε0 =>
    let ⟨δ, δ0, Hδ⟩ := rat_inv_continuous_lemma abs ε0 r0
    ⟨δ, δ0, fun {a b} h => Hδ (H _ a.2) (H _ b.2) h⟩

/--
theorem `Real.uniformContinuous_abs` / 定理 `Real.uniformContinuous_abs`

English:
theorem Real.uniformContinuous_abs
  statement: UniformContinuous (abs : Real -> Real)
  proof: Metric.uniformContinuous_iff.2 fun ε ε0 =>
    ⟨ε, ε0, fun _ _ => lt_of_le_of_lt (abs_abs_sub_abs_le_abs_sub _ _)⟩

中文:
定理 Real.uniformContinuous_abs
  结论: UniformContinuous (abs : 实数 -> 实数)
  证明: Metric.uniformContinuous_iff.2 fun ε ε0 =>
    ⟨ε, ε0, fun _ _ => lt_of_le_of_lt (abs_abs_sub_abs_le_abs_sub _ _)⟩

Depends on / 依赖: Metric, Metric.uniformContinuous_iff, abs_abs_sub_abs_le_abs_sub, lt_of_le_of_lt, uniformContinuous_iff
-/
theorem Real.uniformContinuous_abs : UniformContinuous (abs : Real -> Real) :=
  Metric.uniformContinuous_iff.2 fun ε ε0 =>
    ⟨ε, ε0, fun _ _ => lt_of_le_of_lt (abs_abs_sub_abs_le_abs_sub _ _)⟩

/--
theorem `Real.continuous_inv` / 定理 `Real.continuous_inv`

English:
theorem Real.continuous_inv
  statement: Continuous fun a : { r : Real // r != 0 } => a.val⁻¹
  proof: continuousOn_inv₀.domRestrict

中文:
定理 Real.continuous_inv
  结论: Continuous fun a : { r : 实数 // r != 0 } => a.val⁻¹
  证明: continuousOn_inv₀.domRestrict

Depends on / 依赖: domRestrict
-/
theorem Real.continuous_inv : Continuous fun a : { r : Real // r != 0 } => a.val⁻¹ :=
  continuousOn_inv₀.domRestrict

/--
theorem `Real.uniformContinuous_mul` / 定理 `Real.uniformContinuous_mul`

English:
theorem Real.uniformContinuous_mul
  statement: (s : Set (Real × Real)) {r₁ r₂ : Real}
  proof: Metric.uniformContinuous_iff.2 fun _ε ε0 =>
    let ⟨δ, δ0, Hδ⟩ := rat_mul_continuous_lemma abs ε0
    ⟨δ, δ0, fun {a b} h =>
      let ⟨h₁, h₂⟩ := max_lt_iff.1 h
      Hδ (H _ a.2).1 (H _ b.2).2 h₁ h₂⟩

中文:
定理 Real.uniformContinuous_mul
  结论: (s : Set (实数 × 实数)) {r₁ r₂ : 实数}
  证明: Metric.uniformContinuous_iff.2 fun _ε ε0 =>
    let ⟨δ, δ0, Hδ⟩ := rat_mul_continuous_lemma abs ε0
    ⟨δ, δ0, fun {a b} h =>
      let ⟨h₁, h₂⟩ := max_lt_iff.1 h
      Hδ (H _ a.2).1 (H _ b.2).2 h₁ h₂⟩

Depends on / 依赖: Metric, Metric.uniformContinuous_iff, max_lt_iff, rat_mul_continuous_lemma, uniformContinuous_iff
-/
theorem Real.uniformContinuous_mul (s : Set (Real × Real)) {r₁ r₂ : Real}
    (H : forall x in s, |(x : Real × Real).1| < r₁ ∧ |x.2| < r₂) :
    UniformContinuous fun p : s => p.1.1 * p.1.2 :=
  Metric.uniformContinuous_iff.2 fun _ε ε0 =>
    let ⟨δ, δ0, Hδ⟩ := rat_mul_continuous_lemma abs ε0
    ⟨δ, δ0, fun {a b} h =>
      let ⟨h₁, h₂⟩ := max_lt_iff.1 h
      Hδ (H _ a.2).1 (H _ b.2).2 h₁ h₂⟩

/--
theorem `Real.totallyBounded_ball` / 定理 `Real.totallyBounded_ball`

English:
theorem Real.totallyBounded_ball
  given: (x ε : Real)
  statement: TotallyBounded (ball x ε)
  proof: by
  rw [Real.ball_eq_Ioo]; apply totallyBounded_Ioo

中文:
定理 Real.totallyBounded_ball
  条件: (x ε : 实数)
  结论: TotallyBounded (ball x ε)
  证明: by
  rw [Real.ball_eq_Ioo]; apply totallyBounded_Ioo

Depends on / 依赖: Real.ball_eq_Ioo, ball_eq_Ioo, totallyBounded_Ioo
-/
theorem Real.totallyBounded_ball (x ε : Real) : TotallyBounded (ball x ε) := by
  rw [Real.ball_eq_Ioo]; apply totallyBounded_Ioo

/--
theorem `Real.subfield_eq_of_closed` / 定理 `Real.subfield_eq_of_closed`

English:
theorem Real.subfield_eq_of_closed
  given: {K : Subfield Real} (hc : IsClosed (K : Set Real))
  statement: K = ⊤
  proof: by
  rw [SetLike.ext'_iff]; rw [Subfield.coe_top]; rw [← hc.closure_eq]
.closure_eq refine Rat.denseRange_cast.mono ?_
  rintro - ⟨_, rfl⟩
  exact SubfieldClass.ratCast_mem K _

中文:
定理 Real.subfield_eq_of_closed
  条件: {K : Subfield 实数} (hc : IsClosed (K : Set 实数))
  结论: K = ⊤
  证明: by
  rw [SetLike.ext'_iff]; rw [Subfield.coe_top]; rw [← hc.closure_eq]
.closure_eq refine Rat.denseRange_cast.mono ?_
  rintro - ⟨_, rfl⟩
  exact SubfieldClass.ratCast_mem K _

Depends on / 依赖: Rat.denseRange_cast.mono, SetLike, SetLike.ext, Subfield, Subfield.coe_top, SubfieldClass, SubfieldClass.ratCast_mem, _iff, closure_eq, coe_top, denseRange_cast, hc.closure_eq, ratCast_mem
-/
theorem Real.subfield_eq_of_closed {K : Subfield Real} (hc : IsClosed (K : Set Real)) : K = ⊤ := by
  rw [SetLike.ext'_iff]; rw [Subfield.coe_top]; rw [← hc.closure_eq]
.closure_eq refine Rat.denseRange_cast.mono ?_
  rintro - ⟨_, rfl⟩
  exact SubfieldClass.ratCast_mem K _

/--
theorem `Real.exists_seq_rat_strictMono_tendsto` / 定理 `Real.exists_seq_rat_strictMono_tendsto`

English:
theorem Real.exists_seq_rat_strictMono_tendsto
  given: (x : Real)
  proof: Rat.denseRange_cast.exists_seq_strictMono_tendsto Rat.cast_strictMono.monotone x

中文:
定理 Real.exists_seq_rat_strictMono_tendsto
  条件: (x : 实数)
  证明: Rat.denseRange_cast.exists_seq_strictMono_tendsto Rat.cast_strictMono.monotone x

Depends on / 依赖: Rat.cast_strictMono.monotone, Rat.denseRange_cast.exists_seq_strictMono_tendsto, cast_strictMono, denseRange_cast, exists_seq_strictMono_tendsto, monotone
-/
theorem Real.exists_seq_rat_strictMono_tendsto (x : Real) :
    exists u : Nat -> Rat, StrictMono u ∧ (forall n, u n < x) ∧ Tendsto (u · : Nat -> Real) atTop (𝓝 x) :=
  Rat.denseRange_cast.exists_seq_strictMono_tendsto Rat.cast_strictMono.monotone x

/--
theorem `Real.exists_seq_rat_strictAnti_tendsto` / 定理 `Real.exists_seq_rat_strictAnti_tendsto`

English:
theorem Real.exists_seq_rat_strictAnti_tendsto
  given: (x : Real)
  proof: Rat.denseRange_cast.exists_seq_strictAnti_tendsto Rat.cast_strictMono.monotone x

中文:
定理 Real.exists_seq_rat_strictAnti_tendsto
  条件: (x : 实数)
  证明: Rat.denseRange_cast.exists_seq_strictAnti_tendsto Rat.cast_strictMono.monotone x

Depends on / 依赖: Rat.cast_strictMono.monotone, Rat.denseRange_cast.exists_seq_strictAnti_tendsto, cast_strictMono, denseRange_cast, exists_seq_strictAnti_tendsto, monotone
-/
theorem Real.exists_seq_rat_strictAnti_tendsto (x : Real) :
    exists u : Nat -> Rat, StrictAnti u ∧ (forall n, x < u n) ∧ Tendsto (u · : Nat -> Real) atTop (𝓝 x) :=
  Rat.denseRange_cast.exists_seq_strictAnti_tendsto Rat.cast_strictMono.monotone x

section

/--
theorem `closure_ordConnected_inter_rat` / 定理 `closure_ordConnected_inter_rat`

English:
theorem closure_ordConnected_inter_rat
  given: {s : Set Real} (conn : s.OrdConnected) (nt : s.Nontrivial)
  proof: (closure_mono inter_subset_left).antisymm isClosed_closure.closure_subset_iff.mpr fun x hx =>
    Real.mem_closure_iff.mpr fun ε ε_pos => by
      have ⟨z, hz, ne⟩ := nt.exists_ne x
      refine ne.lt_or_gt.elim (fun lt => ?_) fun lt => ?_
      · have ⟨q, h₁, h₂⟩ := exists_rat_btwn (max_lt lt (sub_

中文:
定理 closure_ordConnected_inter_rat
  条件: {s : Set 实数} (conn : s.OrdConnected) (nt : s.Nontrivial)
  证明: (closure_mono inter_subset_left).antisymm isClosed_closure.closure_subset_iff.mpr fun x hx =>
    Real.mem_closure_iff.mpr fun ε ε_pos => by
      have ⟨z, hz, ne⟩ := nt.exists_ne x
      refine ne.lt_or_gt.elim (fun lt => ?_) fun lt => ?_
      · have ⟨q, h₁, h₂⟩ := exists_rat_btwn (max_lt lt (sub_

Depends on / 依赖: Real.mem_closure_iff.mpr, abs_of_pos, abs_sub_comm, antisymm, closure_mono, closure_subset_iff, conn.out, exists_ne, exists_rat_btwn, inter_subset_left, isClosed_closure, isClosed_closure.closure_subset_iff.mpr, lt_min, lt_or_gt, max_lt, max_lt_iff, mem_closure_iff, ne.lt_or_gt.elim, nt.exists_ne, sub_lt_comm
-/
theorem closure_ordConnected_inter_rat {s : Set Real} (conn : s.OrdConnected) (nt : s.Nontrivial) :
    closure (s inter .range Rat.cast) = closure s :=
(closure_mono inter_subset_left).antisymm isClosed_closure.closure_subset_iff.mpr fun x hx =>
    Real.mem_closure_iff.mpr fun ε ε_pos => by
      have ⟨z, hz, ne⟩ := nt.exists_ne x
      refine ne.lt_or_gt.elim (fun lt => ?_) fun lt => ?_
      · have ⟨q, h₁, h₂⟩ := exists_rat_btwn (max_lt lt (sub_lt_self x ε_pos))
        rw [max_lt_iff] at h₁
        refine ⟨q, ⟨conn.out hz hx ⟨h₁.1.le, h₂.le⟩, q, rfl⟩, ?_⟩
        simpa only [abs_sub_comm, abs_of_pos (sub_pos.mpr h₂), sub_lt_comm] using h₁.2
      · have ⟨q, h₁, h₂⟩ := exists_rat_btwn (lt_min lt (lt_add_of_pos_right x ε_pos))
        rw [lt_min_iff] at h₂
        refine ⟨q, ⟨conn.out hx hz ⟨h₁.le, h₂.1.le⟩, q, rfl⟩, ?_⟩
        simpa only [abs_of_pos (sub_pos.2 h₁), sub_lt_iff_lt_add'] using h₂.2

/--
theorem `closure_of_rat_image_lt` / 定理 `closure_of_rat_image_lt`

English:
theorem closure_of_rat_image_lt
  given: {q : Rat}
  proof: by
  convert! closure_ordConnected_inter_rat (ordConnected_Ioi (a := (q : Real))) _ using 1
  · congr!; aesop
  · exact (closure_Ioi _).symm
  · exact ⟨q + 1, show (q : Real) < _ by linarith, q + 2, show (q : Real) < _ by linarith, by simp⟩

@[deprecated (since := "2026-04-07")]
alias Real.cobounded

中文:
定理 closure_of_rat_image_lt
  条件: {q : Rat}
  证明: by
  convert! closure_ordConnected_inter_rat (ordConnected_Ioi (a := (q : Real))) _ using 1
  · congr!; aesop
  · exact (closure_Ioi _).symm
  · exact ⟨q + 1, show (q : Real) < _ by linarith, q + 2, show (q : Real) < _ by linarith, by simp⟩

@[deprecated (since := "2026-04-07")]
alias Real.cobounded

Depends on / 依赖: closure_Ioi, closure_ordConnected_inter_rat, convert, ordConnected_Ioi
-/
theorem closure_of_rat_image_lt {q : Rat} :
    closure (((↑) : Rat -> Real) '' { x | q < x }) = { r | ↑q <= r } := by
  convert! closure_ordConnected_inter_rat (ordConnected_Ioi (a := (q : Real))) _ using 1
  · congr!; aesop
  · exact (closure_Ioi _).symm
  · exact ⟨q + 1, show (q : Real) < _ by linarith, q + 2, show (q : Real) < _ by linarith, by simp⟩

@[deprecated (since := "2026-04-07")]
alias Real.cobounded_eq := IsOrderBornology.cobounded_eq

/- TODO(Mario): Put these back only if needed later
lemma closure_of_rat_image_le_eq {q : ℚ} : closure ((coe : ℚ → ℝ) '' {x | q ≤ x}) = {r | ↑q ≤ r} :=
  _

lemma closure_of_rat_image_le_le_eq {a b : ℚ} (hab : a ≤ b) :
    closure (of_rat '' {q:ℚ | a ≤ q ∧ q ≤ b}) = {r:ℝ | of_rat a ≤ r ∧ r ≤ of_rat b} :=
  _
-/

end

section Periodic

namespace Function

/--
theorem `Periodic.compact_of_continuous` / 定理 `Periodic.compact_of_continuous`

English:
theorem Periodic.compact_of_continuous
  statement: [TopologicalSpace α] {f : Real -> α} {c : Real} (hp : Periodic f c)
  proof: by
  rw [← hp.image_uIcc hc 0]
  exact isCompact_uIcc.image hf

中文:
定理 Periodic.compact_of_continuous
  结论: [TopologicalSpace α] {f : 实数 -> α} {c : 实数} (hp : Periodic f c)
  证明: by
  rw [← hp.image_uIcc hc 0]
  exact isCompact_uIcc.image hf

Depends on / 依赖: hp.image_uIcc, image_uIcc, isCompact_uIcc, isCompact_uIcc.image
-/
theorem Periodic.compact_of_continuous [TopologicalSpace α] {f : Real -> α} {c : Real} (hp : Periodic f c)
    (hc : c != 0) (hf : Continuous f) : IsCompact (range f) := by
  rw [← hp.image_uIcc hc 0]
  exact isCompact_uIcc.image hf

/--
theorem `Periodic.isBounded_of_continuous` / 定理 `Periodic.isBounded_of_continuous`

English:
theorem Periodic.isBounded_of_continuous
  statement: [PseudoMetricSpace α] {f : Real -> α} {c : Real}
  proof: (hp.compact_of_continuous hc hf).isBounded

中文:
定理 Periodic.isBounded_of_continuous
  结论: [PseudoMetricSpace α] {f : 实数 -> α} {c : 实数}
  证明: (hp.compact_of_continuous hc hf).isBounded

Depends on / 依赖: compact_of_continuous, hp.compact_of_continuous, isBounded
-/
theorem Periodic.isBounded_of_continuous [PseudoMetricSpace α] {f : Real -> α} {c : Real}
    (hp : Periodic f c) (hc : c != 0) (hf : Continuous f) : IsBounded (range f) :=
  (hp.compact_of_continuous hc hf).isBounded

end Function

end Periodic

section Monotone

variable {ι : Type*} [Preorder ι] [Nonempty ι]

/--
theorem `Real.tendsto_atTop_csSup_of_monotoneOn_bddAbove_nat_Ici` / 定理 `Real.tendsto_atTop_csSup_of_monotoneOn_bddAbove_nat_Ici`

English:
theorem Real.tendsto_atTop_csSup_of_monotoneOn_bddAbove_nat_Ici
  statement: {f : Nat -> Real} {k : Nat}
  proof: by
  rw [← range_add_eq_image_Ici] at h_bdd
  rw [Ici]; rw [← monotone_add_nat_iff_monotoneOn_nat_Ici] at h_mon
  rw [← tendsto_add_atTop_iff_nat k]; rw [← range_add_eq_image_Ici]; rw [sSup_range]
  exact tendsto_atTop_ciSup h_mon h_bdd

中文:
定理 Real.tendsto_atTop_csSup_of_monotoneOn_bddAbove_nat_Ici
  结论: {f : 自然数 -> 实数} {k : 自然数}
  证明: by
  rw [← range_add_eq_image_Ici] at h_bdd
  rw [Ici]; rw [← monotone_add_nat_iff_monotoneOn_nat_Ici] at h_mon
  rw [← tendsto_add_atTop_iff_nat k]; rw [← range_add_eq_image_Ici]; rw [sSup_range]
  exact tendsto_atTop_ciSup h_mon h_bdd

Depends on / 依赖: h_bdd, h_mon, monotone_add_nat_iff_monotoneOn_nat_Ici, range_add_eq_image_Ici, sSup_range, tendsto_add_atTop_iff_nat, tendsto_atTop_ciSup
-/
theorem Real.tendsto_atTop_csSup_of_monotoneOn_bddAbove_nat_Ici {f : Nat -> Real} {k : Nat}
    (h_mon : MonotoneOn f (Ici k)) (h_bdd : BddAbove (f '' Ici k)) :
    Tendsto f atTop (𝓝 (sSup (f '' Ici k))) := by
  rw [← range_add_eq_image_Ici] at h_bdd
  rw [Ici]; rw [← monotone_add_nat_iff_monotoneOn_nat_Ici] at h_mon
  rw [← tendsto_add_atTop_iff_nat k]; rw [← range_add_eq_image_Ici]; rw [sSup_range]
  exact tendsto_atTop_ciSup h_mon h_bdd

/--
theorem `Real.tendsto_atTop_csInf_of_antitoneOn_bddBelow_nat_Ici` / 定理 `Real.tendsto_atTop_csInf_of_antitoneOn_bddBelow_nat_Ici`

English:
theorem Real.tendsto_atTop_csInf_of_antitoneOn_bddBelow_nat_Ici
  statement: {f : Nat -> Real} {k : Nat}
  proof: by
  rw [← range_add_eq_image_Ici] at h_bdd
  rw [Ici]; rw [← antitone_add_nat_iff_antitoneOn_nat_Ici] at h_ant
  rw [← tendsto_add_atTop_iff_nat k]; rw [← range_add_eq_image_Ici]; rw [sInf_range]
  exact tendsto_atTop_ciInf h_ant h_bdd

中文:
定理 Real.tendsto_atTop_csInf_of_antitoneOn_bddBelow_nat_Ici
  结论: {f : 自然数 -> 实数} {k : 自然数}
  证明: by
  rw [← range_add_eq_image_Ici] at h_bdd
  rw [Ici]; rw [← antitone_add_nat_iff_antitoneOn_nat_Ici] at h_ant
  rw [← tendsto_add_atTop_iff_nat k]; rw [← range_add_eq_image_Ici]; rw [sInf_range]
  exact tendsto_atTop_ciInf h_ant h_bdd

Depends on / 依赖: antitone_add_nat_iff_antitoneOn_nat_Ici, h_ant, h_bdd, range_add_eq_image_Ici, sInf_range, tendsto_add_atTop_iff_nat, tendsto_atTop_ciInf
-/
theorem Real.tendsto_atTop_csInf_of_antitoneOn_bddBelow_nat_Ici {f : Nat -> Real} {k : Nat}
    (h_ant : AntitoneOn f (Ici k)) (h_bdd : BddBelow (f '' Ici k)) :
    Tendsto f atTop (𝓝 (sInf (f '' Ici k))) := by
  rw [← range_add_eq_image_Ici] at h_bdd
  rw [Ici]; rw [← antitone_add_nat_iff_antitoneOn_nat_Ici] at h_ant
  rw [← tendsto_add_atTop_iff_nat k]; rw [← range_add_eq_image_Ici]; rw [sInf_range]
  exact tendsto_atTop_ciInf h_ant h_bdd

variable [IsDirected ι (· <= ·)]

/--
theorem `Real.isLUB_of_tendsto_monotone_bddAbove` / 定理 `Real.isLUB_of_tendsto_monotone_bddAbove`

English:
theorem Real.isLUB_of_tendsto_monotone_bddAbove
  statement: {f : ι -> Real}
  proof: by
  rw [tendsto_nhds_unique h_tto (tendsto_atTop_ciSup h_mon h_bdd)]
  exact isLUB_ciSup h_bdd

中文:
定理 Real.isLUB_of_tendsto_monotone_bddAbove
  结论: {f : ι -> 实数}
  证明: by
  rw [tendsto_nhds_unique h_tto (tendsto_atTop_ciSup h_mon h_bdd)]
  exact isLUB_ciSup h_bdd

Depends on / 依赖: h_bdd, h_mon, h_tto, isLUB_ciSup, tendsto_atTop_ciSup, tendsto_nhds_unique
-/
theorem Real.isLUB_of_tendsto_monotone_bddAbove {f : ι -> Real}
    {x : Real} (h_tto : Tendsto f atTop (𝓝 x))
    (h_mon : Monotone f) (h_bdd : BddAbove (range f)) : IsLUB (range f) x := by
  rw [tendsto_nhds_unique h_tto (tendsto_atTop_ciSup h_mon h_bdd)]
  exact isLUB_ciSup h_bdd

/--
theorem `Real.isGLB_of_tendsto_antitone_bddBelow` / 定理 `Real.isGLB_of_tendsto_antitone_bddBelow`

English:
theorem Real.isGLB_of_tendsto_antitone_bddBelow
  statement: {f : ι -> Real}
  proof: by
  rw [tendsto_nhds_unique h_tto (tendsto_atTop_ciInf h_ant h_bdd)]
  exact isGLB_ciInf h_bdd

中文:
定理 Real.isGLB_of_tendsto_antitone_bddBelow
  结论: {f : ι -> 实数}
  证明: by
  rw [tendsto_nhds_unique h_tto (tendsto_atTop_ciInf h_ant h_bdd)]
  exact isGLB_ciInf h_bdd

Depends on / 依赖: h_ant, h_bdd, h_tto, isGLB_ciInf, tendsto_atTop_ciInf, tendsto_nhds_unique
-/
theorem Real.isGLB_of_tendsto_antitone_bddBelow {f : ι -> Real}
    {x : Real} (h_tto : Tendsto f atTop (𝓝 x))
    (h_ant : Antitone f) (h_bdd : BddBelow (range f)) : IsGLB (range f) x := by
  rw [tendsto_nhds_unique h_tto (tendsto_atTop_ciInf h_ant h_bdd)]
  exact isGLB_ciInf h_bdd

/--
theorem `Real.isLUB_of_tendsto_monotoneOn_bddAbove_nat_Ici` / 定理 `Real.isLUB_of_tendsto_monotoneOn_bddAbove_nat_Ici`

English:
theorem Real.isLUB_of_tendsto_monotoneOn_bddAbove_nat_Ici
  statement: {f : Nat -> Real} {k : Nat}
  proof: by
  rw [tendsto_nhds_unique h_tto
    (Real.tendsto_atTop_csSup_of_monotoneOn_bddAbove_nat_Ici h_mon h_bdd)]
  exact isLUB_csSup (image_nonempty.mpr nonempty_Ici) h_bdd

中文:
定理 Real.isLUB_of_tendsto_monotoneOn_bddAbove_nat_Ici
  结论: {f : 自然数 -> 实数} {k : 自然数}
  证明: by
  rw [tendsto_nhds_unique h_tto
    (Real.tendsto_atTop_csSup_of_monotoneOn_bddAbove_nat_Ici h_mon h_bdd)]
  exact isLUB_csSup (image_nonempty.mpr nonempty_Ici) h_bdd

Depends on / 依赖: Real.tendsto_atTop_csSup_of_monotoneOn_bddAbove_nat_Ici, h_bdd, h_mon, h_tto, image_nonempty, image_nonempty.mpr, isLUB_csSup, nonempty_Ici, tendsto_atTop_csSup_of_monotoneOn_bddAbove_nat_Ici, tendsto_nhds_unique
-/
theorem Real.isLUB_of_tendsto_monotoneOn_bddAbove_nat_Ici {f : Nat -> Real} {k : Nat}
    {x : Real} (h_tto : Tendsto f atTop (𝓝 x))
    (h_mon : MonotoneOn f (Ici k)) (h_bdd : BddAbove (f '' Ici k)) : IsLUB (f '' Ici k) x := by
  rw [tendsto_nhds_unique h_tto
    (Real.tendsto_atTop_csSup_of_monotoneOn_bddAbove_nat_Ici h_mon h_bdd)]
  exact isLUB_csSup (image_nonempty.mpr nonempty_Ici) h_bdd

/--
theorem `Real.isGLB_of_tendsto_antitoneOn_bddBelow_nat_Ici` / 定理 `Real.isGLB_of_tendsto_antitoneOn_bddBelow_nat_Ici`

English:
theorem Real.isGLB_of_tendsto_antitoneOn_bddBelow_nat_Ici
  statement: {f : Nat -> Real} {k : Nat}
  proof: by
  rw [tendsto_nhds_unique h_tto
    (Real.tendsto_atTop_csInf_of_antitoneOn_bddBelow_nat_Ici h_ant h_bdd)]
  exact isGLB_csInf (image_nonempty.mpr nonempty_Ici) h_bdd

中文:
定理 Real.isGLB_of_tendsto_antitoneOn_bddBelow_nat_Ici
  结论: {f : 自然数 -> 实数} {k : 自然数}
  证明: by
  rw [tendsto_nhds_unique h_tto
    (Real.tendsto_atTop_csInf_of_antitoneOn_bddBelow_nat_Ici h_ant h_bdd)]
  exact isGLB_csInf (image_nonempty.mpr nonempty_Ici) h_bdd

Depends on / 依赖: Real.tendsto_atTop_csInf_of_antitoneOn_bddBelow_nat_Ici, h_ant, h_bdd, h_tto, image_nonempty, image_nonempty.mpr, isGLB_csInf, nonempty_Ici, tendsto_atTop_csInf_of_antitoneOn_bddBelow_nat_Ici, tendsto_nhds_unique
-/
theorem Real.isGLB_of_tendsto_antitoneOn_bddBelow_nat_Ici {f : Nat -> Real} {k : Nat}
    {x : Real} (h_tto : Tendsto f atTop (𝓝 x))
    (h_ant : AntitoneOn f (Ici k)) (h_bdd : BddBelow (f '' Ici k)) : IsGLB (f '' Ici k) x := by
  rw [tendsto_nhds_unique h_tto
    (Real.tendsto_atTop_csInf_of_antitoneOn_bddBelow_nat_Ici h_ant h_bdd)]
  exact isGLB_csInf (image_nonempty.mpr nonempty_Ici) h_bdd

end Monotone
