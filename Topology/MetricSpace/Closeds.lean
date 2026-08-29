/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Topology.UniformSpace.Closeds

/-!
# Closed subsets

This file defines the metric and emetric space structure on the types of closed subsets and nonempty
compact subsets of a metric or emetric space.

The Hausdorff distance induces an emetric space structure on the type of closed subsets
of an emetric space, called `Closeds`. Its completeness, resp. compactness, resp.
second-countability, follow from the corresponding properties of the original space.

In a metric space, the type of nonempty compact subsets (called `NonemptyCompacts`) also
inherits a metric space structure from the Hausdorff distance, as the Hausdorff edistance is
always finite in this context.
-/

public section

noncomputable section

open Set Function TopologicalSpace Filter Topology ENNReal

namespace Metric

variable {α : Type*} [PseudoEMetricSpace α]

/--
theorem `mem_hausdorffEntourage_of_hausdorffEDist_lt` / 定理 `mem_hausdorffEntourage_of_hausdorffEDist_lt`

English:
theorem mem_hausdorffEntourage_of_hausdorffEDist_lt
  statement: {s t : Set α} {δ : Real>=0∞}
  proof: by
  rw [hausdorffEDist]; rw [max_lt_iff] at h
  rw [hausdorffEntourage]; rw [Set.mem_ofPred]
  conv => enter [2, 2, 1, 1, _]; rw [edist_comm]
  have {s t : Set α} (h : ⨆ x in s, infEDist x t < δ) :
      s subseteq SetRel.preimage {p | edist p.1 p.2 < δ} t := by
    intro x hx
    simpa only [infEDist, iInf_lt_iff, exists_prop] using! (le_iSup₂ x hx).trans_lt h
  exact ⟨this h.1, this h.2⟩

中文:
定理 mem_hausdorffEntourage_of_hausdorffEDist_lt
  结论: {s t : 集合 α} {δ : 实数>=0∞}
  证明: by
  rw [hausdorffEDist]; rw [max_lt_iff] at h
  rw [hausdorffEntourage]; rw [Set.mem_ofPred]
  conv => enter [2, 2, 1, 1, _]; rw [edist_comm]
  have {s t : Set α} (h : ⨆ x in s, infEDist x t < δ) :
      s subseteq SetRel.preimage {p | edist p.1 p.2 < δ} t := by
    intro x hx
    simpa only [infEDist, iInf_lt_iff, exists_prop] using! (le_iSup₂ x hx).trans_lt h
  exact ⟨this h.1, this h.2⟩

Depends on / 依赖: Set.mem_ofPred, SetRel, SetRel.preimage, edist_comm, exists_prop, hausdorffEDist, hausdorffEntourage, iInf_lt_iff, infEDist, max_lt_iff, mem_ofPred, preimage, subseteq, trans_lt
-/
theorem mem_hausdorffEntourage_of_hausdorffEDist_lt {s t : Set α} {δ : Real>=0∞}
    (h : hausdorffEDist s t < δ) : (s, t) in hausdorffEntourage {p | edist p.1 p.2 < δ} := by
  rw [hausdorffEDist]; rw [max_lt_iff] at h
  rw [hausdorffEntourage]; rw [Set.mem_ofPred]
  conv => enter [2, 2, 1, 1, _]; rw [edist_comm]
  have {s t : Set α} (h : ⨆ x in s, infEDist x t < δ) :
      s subseteq SetRel.preimage {p | edist p.1 p.2 < δ} t := by
    intro x hx
    simpa only [infEDist, iInf_lt_iff, exists_prop] using! (le_iSup₂ x hx).trans_lt h
  exact ⟨this h.1, this h.2⟩

/--
theorem `hausdorffEDist_le_of_mem_hausdorffEntourage` / 定理 `hausdorffEDist_le_of_mem_hausdorffEntourage`

English:
theorem hausdorffEDist_le_of_mem_hausdorffEntourage
  statement: {s t : Set α} {δ : Real>=0∞}
  proof: by
  rw [hausdorffEDist]; rw [max_le_iff]
  rw [hausdorffEntourage]; rw [Set.mem_ofPred] at h
  conv at h => enter [2, 2, 1, 1, _]; rw [edist_comm]
  have {s t : Set α} (h : s subseteq SetRel.preimage {p | edist p.1 p.2 <= δ} t) :
      ⨆ x in s, infEDist x t <= δ := by
    rw [iSup₂_le_iff]
    intro x hx
    obtain ⟨y, hy, hxy⟩ := h hx
    exact iInf₂_le_of_le y hy hxy
  exact ⟨this h.1, this h.2⟩

中文:
定理 hausdorffEDist_le_of_mem_hausdorffEntourage
  结论: {s t : 集合 α} {δ : 实数>=0∞}
  证明: by
  rw [hausdorffEDist]; rw [max_le_iff]
  rw [hausdorffEntourage]; rw [Set.mem_ofPred] at h
  conv at h => enter [2, 2, 1, 1, _]; rw [edist_comm]
  have {s t : Set α} (h : s subseteq SetRel.preimage {p | edist p.1 p.2 <= δ} t) :
      ⨆ x in s, infEDist x t <= δ := by
    rw [iSup₂_le_iff]
    intro x hx
    obtain ⟨y, hy, hxy⟩ := h hx
    exact iInf₂_le_of_le y hy hxy
  exact ⟨this h.1, this h.2⟩

Depends on / 依赖: Set.mem_ofPred, SetRel, SetRel.preimage, edist_comm, hausdorffEDist, hausdorffEntourage, infEDist, max_le_iff, mem_ofPred, preimage, subseteq
-/
theorem hausdorffEDist_le_of_mem_hausdorffEntourage {s t : Set α} {δ : Real>=0∞}
    (h : (s, t) in hausdorffEntourage {p | edist p.1 p.2 <= δ}) : hausdorffEDist s t <= δ := by
  rw [hausdorffEDist]; rw [max_le_iff]
  rw [hausdorffEntourage]; rw [Set.mem_ofPred] at h
  conv at h => enter [2, 2, 1, 1, _]; rw [edist_comm]
  have {s t : Set α} (h : s subseteq SetRel.preimage {p | edist p.1 p.2 <= δ} t) :
      ⨆ x in s, infEDist x t <= δ := by
    rw [iSup₂_le_iff]
    intro x hx
    obtain ⟨y, hy, hxy⟩ := h hx
    exact iInf₂_le_of_le y hy hxy
  exact ⟨this h.1, this h.2⟩

/--
Definition of `_root_.PseudoEMetricSpace.hausdorff` / `_root_.PseudoEMetricSpace.hausdorff` 的定义

English:
abbreviation _root_.PseudoEMetricSpace.hausdorff
  signature: : PseudoEMetricSpace (Set α) where
  body: hausdorffEDist s t
  edist_self _ := hausdorffEDist_self
  edist_comm _ _ := hausdorffEDist_comm
  edist_triangle _ _ _ := hausdorffEDist_triangle
  toUniformSpace := .hausdorff α
  uniformity_edist := by
    refine le_antisymm
      (le_iInf₂ fun ε hε => Filter.le_principal_iff.mpr ?_)
      (uniformity_basis_edist.lift' monotone_hausdorffEntourage |>.ge_iff.mpr fun ε hε =>
Filter.mem_iInf_of_mem ε Filter.mem_iInf_of_mem hε fun _ =>
        mem_hausdorffEntourage_of_hausdorffEDist_lt)
    obtain ⟨δ, hδ, hδε⟩ := exists_between hε
    filter_upwards [Filter.mem_lift' (uniformity_basis_edist_le.mem_of_mem hδ)]
with _ h using hδε.trans_le' hausdorffEDist_le_of_mem_hausdorffEntourage h

中文:
缩写 _root_.PseudoEMetric空间.hausdorff
  签名: : PseudoEMetric空间 (集合 α) where
  定义体: hausdorffEDist s t
  edist_self _ := hausdorffEDist_self
  edist_comm _ _ := hausdorffEDist_comm
  edist_triangle _ _ _ := hausdorffEDist_triangle
  toUniformSpace := .hausdorff α
  uniformity_edist := by
    refine le_antisymm
      (le_iInf₂ fun ε hε => Filter.le_principal_iff.mpr ?_)
      (uniformity_basis_edist.lift' monotone_hausdorffEntourage |>.ge_iff.mpr fun ε hε =>
Filter.mem_iInf_of_mem ε Filter.mem_iInf_of_mem hε fun _ =>
        mem_hausdorffEntourage_of_hausdorffEDist_lt)
    obtain ⟨δ, hδ, hδε⟩ := exists_between hε
    filter_upwards [Filter.mem_lift' (uniformity_basis_edist_le.mem_of_mem hδ)]
with _ h using hδε.trans_le' hausdorffEDist_le_of_mem_hausdorffEntourage h
-/
protected abbrev _root_.PseudoEMetricSpace.hausdorff : PseudoEMetricSpace (Set α) where
  edist s t := hausdorffEDist s t
  edist_self _ := hausdorffEDist_self
  edist_comm _ _ := hausdorffEDist_comm
  edist_triangle _ _ _ := hausdorffEDist_triangle
  toUniformSpace := .hausdorff α
  uniformity_edist := by
    refine le_antisymm
      (le_iInf₂ fun ε hε => Filter.le_principal_iff.mpr ?_)
      (uniformity_basis_edist.lift' monotone_hausdorffEntourage |>.ge_iff.mpr fun ε hε =>
Filter.mem_iInf_of_mem ε Filter.mem_iInf_of_mem hε fun _ =>
        mem_hausdorffEntourage_of_hausdorffEDist_lt)
    obtain ⟨δ, hδ, hδε⟩ := exists_between hε
    filter_upwards [Filter.mem_lift' (uniformity_basis_edist_le.mem_of_mem hδ)]
with _ h using hδε.trans_le' hausdorffEDist_le_of_mem_hausdorffEntourage h

end Metric

namespace TopologicalSpace

open Metric

variable {α β : Type*} [EMetricSpace α] [EMetricSpace β] {s : Set α}

namespace Closeds

/--
Instance `instEMetricSpace` / 实例 `instEMetricSpace`

English:
instance instEMetricSpace
  signature: : EMetricSpace (Closeds α) where
  body: PseudoEMetricSpace.hausdorff.induced SetLike.coe
eq_of_edist_eq_zero {s t} h := Closeds.ext (s.isClosed.hausdorffEDist_zero_iff t.isClosed).1 h

中文:
实例 instEMetricSpace
  签名: : 广义度量空间 (Closeds α) where
  定义体: PseudoEMetricSpace.hausdorff.induced SetLike.coe
eq_of_edist_eq_zero {s t} h := Closeds.ext (s.isClosed.hausdorffEDist_zero_iff t.isClosed).1 h

Depends on / 依赖: PseudoEMetricSpace, PseudoEMetricSpace.hausdorff.induced, SetLike, SetLike.coe, hausdorff, induced
-/
instance instEMetricSpace : EMetricSpace (Closeds α) where
  __ := PseudoEMetricSpace.hausdorff.induced SetLike.coe
eq_of_edist_eq_zero {s t} h := Closeds.ext (s.isClosed.hausdorffEDist_zero_iff t.isClosed).1 h

/--
theorem `continuous_infEDist` / 定理 `continuous_infEDist`

English:
theorem continuous_infEDist
  proof: by
  refine continuous_of_le_add_edist 2 (by simp) ?_
  rintro ⟨x, s⟩ ⟨y, t⟩
  calc
    infEDist x s <= infEDist x t + hausdorffEDist (t : Set α) s :=
      infEDist_le_infEDist_add_hausdorffEDist
    _ <= infEDist y t + edist x y + hausdorffEDist (t : Set α) s := by
      gcongr; apply infEDist_le_infEDist_add_edist
    _ = infEDist y t + (edist x y + hausdorffEDist (s : Set α) t) := by
      rw [add_assoc]; rw [hausdorffEDist_comm]
    _ <= infEDist y t + (edist (x, s) (y, t) + edist (x, s) (y, t)) := by
      gcongr <;> apply_rules [le_max_left, le_max_right]
    _ = infEDist y t + 2 * edist (x, s) (y, t) := by rw [← mul_two, mul_comm]

中文:
定理 continuous_infEDist
  证明: by
  refine continuous_of_le_add_edist 2 (by simp) ?_
  rintro ⟨x, s⟩ ⟨y, t⟩
  calc
    infEDist x s <= infEDist x t + hausdorffEDist (t : Set α) s :=
      infEDist_le_infEDist_add_hausdorffEDist
    _ <= infEDist y t + edist x y + hausdorffEDist (t : Set α) s := by
      gcongr; apply infEDist_le_infEDist_add_edist
    _ = infEDist y t + (edist x y + hausdorffEDist (s : Set α) t) := by
      rw [add_assoc]; rw [hausdorffEDist_comm]
    _ <= infEDist y t + (edist (x, s) (y, t) + edist (x, s) (y, t)) := by
      gcongr <;> apply_rules [le_max_left, le_max_right]
    _ = infEDist y t + 2 * edist (x, s) (y, t) := by rw [← mul_two, mul_comm]

Depends on / 依赖: add_assoc, apply_rules, continuous_of_le_add_edist, hausdorffEDist, hausdorffEDist_comm, infEDist, infEDist_le_infEDist_add_edist, infEDist_le_infEDist_add_hausdorffEDist, le_m
-/
theorem continuous_infEDist :
    Continuous fun p : α × Closeds α => infEDist p.1 p.2 := by
  refine continuous_of_le_add_edist 2 (by simp) ?_
  rintro ⟨x, s⟩ ⟨y, t⟩
  calc
    infEDist x s <= infEDist x t + hausdorffEDist (t : Set α) s :=
      infEDist_le_infEDist_add_hausdorffEDist
    _ <= infEDist y t + edist x y + hausdorffEDist (t : Set α) s := by
      gcongr; apply infEDist_le_infEDist_add_edist
    _ = infEDist y t + (edist x y + hausdorffEDist (s : Set α) t) := by
      rw [add_assoc]; rw [hausdorffEDist_comm]
    _ <= infEDist y t + (edist (x, s) (y, t) + edist (x, s) (y, t)) := by
      gcongr <;> apply_rules [le_max_left, le_max_right]
    _ = infEDist y t + 2 * edist (x, s) (y, t) := by rw [← mul_two, mul_comm]

/--
theorem `edist_eq` / 定理 `edist_eq`

English:
theorem edist_eq
  given: {s t : Closeds α}
  statement: edist s t = hausdorffEDist (s : Set α) t
  proof: rfl

中文:
定理 edist_eq
  条件: {s t : Closeds α}
  结论: edist s t = hausdorffEDist (s : 集合 α) t
  证明: rfl
-/
theorem edist_eq {s t : Closeds α} : edist s t = hausdorffEDist (s : Set α) t :=
  rfl

/--
Instance `instCompleteSpace` / 实例 `instCompleteSpace`

English:
instance instCompleteSpace
  signature: [CompleteSpace α]
  body: by
  /- We will show that, if a sequence of sets `s n` satisfies
    `edist (s n) (s (n+1)) < 2^{-n}`, then it converges. This is enough to guarantee
    completeness, by a standard completeness criterion.
    We use the shorthand `B n = 2^{-n}` in ennreal. -/
  let B : Nat -> Real>=0∞ := fun n => 2⁻¹ ^ n
  have B_pos : forall n, (0 : Real>=0∞) < B n := by simp [B, ENNReal.pow_pos]
  have B_ne_top : forall n, B n != ⊤ := by finiteness
  /- Consider a sequence of closed sets `s n` with `edist (s n) (s (n+1)) < B n`.
    We will show that it converges. The limit set is `t0 = ⋂n, closure (⋃m≥n, s m)`.
    We will have to show that a point in `s n` is close to a point in `t0`, and a point
    in `t0` is close to a point in `s n`. The completeness then follows from a
    standard criterion. -/
  refine EMetric.complete_of_convergent_controlled_sequences B B_pos fun s hs => ?_
  let t0 := ⋂ n, closure (⋃ m >= n, s m : Set α)
  let t : Closeds α := ⟨t0, isClosed_iInter fun _ => isClosed_closure⟩
  use t
  -- The inequality is written this way to agree with `edist_le_of_edist_le_geometric_of_tendsto₀`
  have I1 : forall n, forall x in s n, exists y in t0, edist x y <= 2 * B n := by
    /- This is the main difficulty of the proof. Starting from `x ∈ s n`, we want
           to find a point in `t0` which is close to `x`. Define inductively a sequence of
           points `z m` with `z n = x` and `z m ∈ s m` and `edist (z m) (z (m+1)) ≤ B m`. This is
           possible since the Hausdorff distance between `s m` and `s (m+1)` is at most `B m`.
           This sequence is a Cauchy sequence, therefore converging as the space is complete, to
           a limit which satisfies the required properties. -/
    intro n x hx
    obtain ⟨z, hz₀, hz⟩ :
      exists z : forall l, s (n + l), (z 0 : α) = x ∧ forall k, edist (z k : α) (z (k + 1) : α) <= B n / 2 ^ k := by
      -- We prove existence of the sequence by induction.
      have : forall (l) (z : s (n + l)), exists z' : s (n + l + 1), edist (z : α) z' <= B n / 2 ^ l := by
        intro l z
        obtain ⟨z', z'_mem, hz'⟩ : exists z' in s (n + l + 1), edist (z : α) z' < B n / 2 ^ l := by
          refine exists_edist_lt_of_hausdorffEDist_lt (s := s (n + l)) z.2 ?_
          simp only [ENNReal.inv_pow, div_eq_mul_inv]
          rw [← pow_add]
          apply hs <;> simp
        exact ⟨⟨z', z'_mem⟩, le_of_lt hz'⟩
      use fun k => Nat.recOn k ⟨x, hx⟩ fun l z => (this l z).choose
      simp only [Nat.add_zero, Nat.rec_zero, true_and]
      exact fun k => (this k _).choose_spec
    -- it follows from the previous bound that `z` is a Cauchy sequence
    have : CauchySeq fun k => (z k : α) := cauchySeq_of_edist_le_geometric_two (B n) (B_ne_top n) hz
    -- therefore, it converges
    rcases cauchySeq_tendsto_of_complete this with ⟨y, y_lim⟩
    use y
    -- the limit point `y` will be the desired point, in `t0` and close to our initial point `x`.
    -- First, we check it belongs to `t0`.
    have : y in t0 :=
      mem_iInter.2 fun k =>
        mem_closure_of_tendsto y_lim
          (by
            simp only [exists_prop, Set.mem_iUnion, Filter.eventually_atTop]
            exact ⟨k, fun m hm => ⟨n + m, by lia, (z m).2⟩⟩)
    use this
    -- Then, we check that `y` is close to `x = z n`. This follows from the fact that `y`
    -- is the limit of `z k`, and the distance between `z n` and `z k` has already been estimated.
    rw [← hz₀]
    exact edist_le_of_edist_le_geometric_two_of_tendsto₀ (B n) hz y_lim
  have I2 : forall n, forall x in t0, exists y in s n, edist x y <= 2 * B n := by
    /- For the (much easier) reverse inequality, we start from a point `x ∈ t0` and we want
            to find a point `y ∈ s n` which is close to `x`.
            `x` belongs to `t0`, the intersection of the closures. In particular, it is well
            approximated by a point `z` in `⋃m≥n, s m`, say in `s m`. Since `s m` and
            `s n` are close, this point is itself well approximated by a point `y` in `s n`,
            as required. -/
    intro n x xt0
    have : x in closure (⋃ m >= n, s m : Set α) := by apply mem_iInter.1 xt0 n
    obtain ⟨z : α, hz, Dxz : edist x z < B n⟩ := EMetric.mem_closure_iff.1 this (B n) (B_pos n)
    simp only [exists_prop, Set.mem_iUnion] at hz
    obtain ⟨m : Nat, m_ge_n : m >= n, hm : z in (s m : Set α)⟩ := hz
    have : hausdorffEDist (s m : Set α) (s n) < B n := hs n m n m_ge_n (le_refl n)
    obtain ⟨y : α, hy : y in (s n : Set α), Dzy : edist z y < B n⟩ :=
      exists_edist_lt_of_hausdorffEDist_lt hm this
    exact
      ⟨y, hy,
        calc
          edist x y <= edist x z + edist z y := edist_triangle _ _ _
          _ <= B n + B n := by gcongr
          _ = 2 * B n := (two_mul _).symm
          ⟩
  -- Deduce from the above inequalities that the distance between `s n` and `t0` is at most `2 B n`.
  have main : forall n : Nat, edist (s n) t <= 2 * B n := fun n =>
    hausdorffEDist_le_of_mem_edist (I1 n) (I2 n)
  -- from this, the convergence of `s n` to `t0` follows.
  refine EMetric.tendsto_atTop.2 fun ε εpos => ?_
  have : Tendsto (fun n => 2 * B n) atTop (𝓝 (2 * 0)) :=
    ENNReal.Tendsto.const_mul (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one <|
by simp) (Or.inr by simp)
  rw [mul_zero] at this
  obtain ⟨N, hN⟩ : exists N, forall b >= N, ε > 2 * B b :=
    ((tendsto_order.1 this).2 ε εpos).exists_forall_of_atTop
  exact ⟨N, fun n hn => lt_of_le_of_lt (main n) (hN n hn)⟩

中文:
实例 instCompleteSpace
  签名: [完备空间 α]
  定义体: by
  /- We will show that, if a sequence of sets `s n` satisfies
    `edist (s n) (s (n+1)) < 2^{-n}`, then it converges. This is enough to guarantee
    completeness, by a standard completeness criterion.
    We use the shorthand `B n = 2^{-n}` in ennreal. -/
  let B : Nat -> Real>=0∞ := fun n => 2⁻¹ ^ n
  have B_pos : forall n, (0 : Real>=0∞) < B n := by simp [B, ENNReal.pow_pos]
  have B_ne_top : forall n, B n != ⊤ := by finiteness
  /- Consider a sequence of closed sets `s n` with `edist (s n) (s (n+1)) < B n`.
    We will show that it converges. The limit set is `t0 = ⋂n, closure (⋃m≥n, s m)`.
    We will have to show that a point in `s n` is close to a point in `t0`, and a point
    in `t0` is close to a point in `s n`. The completeness then follows from a
    standard criterion. -/
  refine EMetric.complete_of_convergent_controlled_sequences B B_pos fun s hs => ?_
  let t0 := ⋂ n, closure (⋃ m >= n, s m : Set α)
  let t : Closeds α := ⟨t0, isClosed_iInter fun _ => isClosed_closure⟩
  use t
  -- The inequality is written this way to agree with `edist_le_of_edist_le_geometric_of_tendsto₀`
  have I1 : forall n, forall x in s n, exists y in t0, edist x y <= 2 * B n := by
    /- This is the main difficulty of the proof. Starting from `x ∈ s n`, we want
           to find a point in `t0` which is close to `x`. Define inductively a sequence of
           points `z m` with `z n = x` and `z m ∈ s m` and `edist (z m) (z (m+1)) ≤ B m`. This is
           possible since the Hausdorff distance between `s m` and `s (m+1)` is at most `B m`.
           This sequence is a Cauchy sequence, therefore converging as the space is complete, to
           a limit which satisfies the required properties. -/
    intro n x hx
    obtain ⟨z, hz₀, hz⟩ :
      exists z : forall l, s (n + l), (z 0 : α) = x ∧ forall k, edist (z k : α) (z (k + 1) : α) <= B n / 2 ^ k := by
      -- We prove existence of the sequence by induction.
      have : forall (l) (z : s (n + l)), exists z' : s (n + l + 1), edist (z : α) z' <= B n / 2 ^ l := by
        intro l z
        obtain ⟨z', z'_mem, hz'⟩ : exists z' in s (n + l + 1), edist (z : α) z' < B n / 2 ^ l := by
          refine exists_edist_lt_of_hausdorffEDist_lt (s := s (n + l)) z.2 ?_
          simp only [ENNReal.inv_pow, div_eq_mul_inv]
          rw [← pow_add]
          apply hs <;> simp
        exact ⟨⟨z', z'_mem⟩, le_of_lt hz'⟩
      use fun k => Nat.recOn k ⟨x, hx⟩ fun l z => (this l z).choose
      simp only [Nat.add_zero, Nat.rec_zero, true_and]
      exact fun k => (this k _).choose_spec
    -- it follows from the previous bound that `z` is a Cauchy sequence
    have : CauchySeq fun k => (z k : α) := cauchySeq_of_edist_le_geometric_two (B n) (B_ne_top n) hz
    -- therefore, it converges
    rcases cauchySeq_tendsto_of_complete this with ⟨y, y_lim⟩
    use y
    -- the limit point `y` will be the desired point, in `t0` and close to our initial point `x`.
    -- First, we check it belongs to `t0`.
    have : y in t0 :=
      mem_iInter.2 fun k =>
        mem_closure_of_tendsto y_lim
          (by
            simp only [exists_prop, Set.mem_iUnion, Filter.eventually_atTop]
            exact ⟨k, fun m hm => ⟨n + m, by lia, (z m).2⟩⟩)
    use this
    -- Then, we check that `y` is close to `x = z n`. This follows from the fact that `y`
    -- is the limit of `z k`, and the distance between `z n` and `z k` has already been estimated.
    rw [← hz₀]
    exact edist_le_of_edist_le_geometric_two_of_tendsto₀ (B n) hz y_lim
  have I2 : forall n, forall x in t0, exists y in s n, edist x y <= 2 * B n := by
    /- For the (much easier) reverse inequality, we start from a point `x ∈ t0` and we want
            to find a point `y ∈ s n` which is close to `x`.
            `x` belongs to `t0`, the intersection of the closures. In particular, it is well
            approximated by a point `z` in `⋃m≥n, s m`, say in `s m`. Since `s m` and
            `s n` are close, this point is itself well approximated by a point `y` in `s n`,
            as required. -/
    intro n x xt0
    have : x in closure (⋃ m >= n, s m : Set α) := by apply mem_iInter.1 xt0 n
    obtain ⟨z : α, hz, Dxz : edist x z < B n⟩ := EMetric.mem_closure_iff.1 this (B n) (B_pos n)
    simp only [exists_prop, Set.mem_iUnion] at hz
    obtain ⟨m : Nat, m_ge_n : m >= n, hm : z in (s m : Set α)⟩ := hz
    have : hausdorffEDist (s m : Set α) (s n) < B n := hs n m n m_ge_n (le_refl n)
    obtain ⟨y : α, hy : y in (s n : Set α), Dzy : edist z y < B n⟩ :=
      exists_edist_lt_of_hausdorffEDist_lt hm this
    exact
      ⟨y, hy,
        calc
          edist x y <= edist x z + edist z y := edist_triangle _ _ _
          _ <= B n + B n := by gcongr
          _ = 2 * B n := (two_mul _).symm
          ⟩
  -- Deduce from the above inequalities that the distance between `s n` and `t0` is at most `2 B n`.
  have main : forall n : Nat, edist (s n) t <= 2 * B n := fun n =>
    hausdorffEDist_le_of_mem_edist (I1 n) (I2 n)
  -- from this, the convergence of `s n` to `t0` follows.
  refine EMetric.tendsto_atTop.2 fun ε εpos => ?_
  have : Tendsto (fun n => 2 * B n) atTop (𝓝 (2 * 0)) :=
    ENNReal.Tendsto.const_mul (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one <|
by simp) (Or.inr by simp)
  rw [mul_zero] at this
  obtain ⟨N, hN⟩ : exists N, forall b >= N, ε > 2 * B b :=
    ((tendsto_order.1 this).2 ε εpos).exists_forall_of_atTop
  exact ⟨N, fun n hn => lt_of_le_of_lt (main n) (hN n hn)⟩
-/
instance instCompleteSpace [CompleteSpace α] : CompleteSpace (Closeds α) := by
  /- We will show that, if a sequence of sets `s n` satisfies
    `edist (s n) (s (n+1)) < 2^{-n}`, then it converges. This is enough to guarantee
    completeness, by a standard completeness criterion.
    We use the shorthand `B n = 2^{-n}` in ennreal. -/
  let B : Nat -> Real>=0∞ := fun n => 2⁻¹ ^ n
  have B_pos : forall n, (0 : Real>=0∞) < B n := by simp [B, ENNReal.pow_pos]
  have B_ne_top : forall n, B n != ⊤ := by finiteness
  /- Consider a sequence of closed sets `s n` with `edist (s n) (s (n+1)) < B n`.
    We will show that it converges. The limit set is `t0 = ⋂n, closure (⋃m≥n, s m)`.
    We will have to show that a point in `s n` is close to a point in `t0`, and a point
    in `t0` is close to a point in `s n`. The completeness then follows from a
    standard criterion. -/
  refine EMetric.complete_of_convergent_controlled_sequences B B_pos fun s hs => ?_
  let t0 := ⋂ n, closure (⋃ m >= n, s m : Set α)
  let t : Closeds α := ⟨t0, isClosed_iInter fun _ => isClosed_closure⟩
  use t
  -- The inequality is written this way to agree with `edist_le_of_edist_le_geometric_of_tendsto₀`
  have I1 : forall n, forall x in s n, exists y in t0, edist x y <= 2 * B n := by
    /- This is the main difficulty of the proof. Starting from `x ∈ s n`, we want
           to find a point in `t0` which is close to `x`. Define inductively a sequence of
           points `z m` with `z n = x` and `z m ∈ s m` and `edist (z m) (z (m+1)) ≤ B m`. This is
           possible since the Hausdorff distance between `s m` and `s (m+1)` is at most `B m`.
           This sequence is a Cauchy sequence, therefore converging as the space is complete, to
           a limit which satisfies the required properties. -/
    intro n x hx
    obtain ⟨z, hz₀, hz⟩ :
      exists z : forall l, s (n + l), (z 0 : α) = x ∧ forall k, edist (z k : α) (z (k + 1) : α) <= B n / 2 ^ k := by
      -- We prove existence of the sequence by induction.
      have : forall (l) (z : s (n + l)), exists z' : s (n + l + 1), edist (z : α) z' <= B n / 2 ^ l := by
        intro l z
        obtain ⟨z', z'_mem, hz'⟩ : exists z' in s (n + l + 1), edist (z : α) z' < B n / 2 ^ l := by
          refine exists_edist_lt_of_hausdorffEDist_lt (s := s (n + l)) z.2 ?_
          simp only [ENNReal.inv_pow, div_eq_mul_inv]
          rw [← pow_add]
          apply hs <;> simp
        exact ⟨⟨z', z'_mem⟩, le_of_lt hz'⟩
      use fun k => Nat.recOn k ⟨x, hx⟩ fun l z => (this l z).choose
      simp only [Nat.add_zero, Nat.rec_zero, true_and]
      exact fun k => (this k _).choose_spec
    -- it follows from the previous bound that `z` is a Cauchy sequence
    have : CauchySeq fun k => (z k : α) := cauchySeq_of_edist_le_geometric_two (B n) (B_ne_top n) hz
    -- therefore, it converges
    rcases cauchySeq_tendsto_of_complete this with ⟨y, y_lim⟩
    use y
    -- the limit point `y` will be the desired point, in `t0` and close to our initial point `x`.
    -- First, we check it belongs to `t0`.
    have : y in t0 :=
      mem_iInter.2 fun k =>
        mem_closure_of_tendsto y_lim
          (by
            simp only [exists_prop, Set.mem_iUnion, Filter.eventually_atTop]
            exact ⟨k, fun m hm => ⟨n + m, by lia, (z m).2⟩⟩)
    use this
    -- Then, we check that `y` is close to `x = z n`. This follows from the fact that `y`
    -- is the limit of `z k`, and the distance between `z n` and `z k` has already been estimated.
    rw [← hz₀]
    exact edist_le_of_edist_le_geometric_two_of_tendsto₀ (B n) hz y_lim
  have I2 : forall n, forall x in t0, exists y in s n, edist x y <= 2 * B n := by
    /- For the (much easier) reverse inequality, we start from a point `x ∈ t0` and we want
            to find a point `y ∈ s n` which is close to `x`.
            `x` belongs to `t0`, the intersection of the closures. In particular, it is well
            approximated by a point `z` in `⋃m≥n, s m`, say in `s m`. Since `s m` and
            `s n` are close, this point is itself well approximated by a point `y` in `s n`,
            as required. -/
    intro n x xt0
    have : x in closure (⋃ m >= n, s m : Set α) := by apply mem_iInter.1 xt0 n
    obtain ⟨z : α, hz, Dxz : edist x z < B n⟩ := EMetric.mem_closure_iff.1 this (B n) (B_pos n)
    simp only [exists_prop, Set.mem_iUnion] at hz
    obtain ⟨m : Nat, m_ge_n : m >= n, hm : z in (s m : Set α)⟩ := hz
    have : hausdorffEDist (s m : Set α) (s n) < B n := hs n m n m_ge_n (le_refl n)
    obtain ⟨y : α, hy : y in (s n : Set α), Dzy : edist z y < B n⟩ :=
      exists_edist_lt_of_hausdorffEDist_lt hm this
    exact
      ⟨y, hy,
        calc
          edist x y <= edist x z + edist z y := edist_triangle _ _ _
          _ <= B n + B n := by gcongr
          _ = 2 * B n := (two_mul _).symm
          ⟩
  -- Deduce from the above inequalities that the distance between `s n` and `t0` is at most `2 B n`.
  have main : forall n : Nat, edist (s n) t <= 2 * B n := fun n =>
    hausdorffEDist_le_of_mem_edist (I1 n) (I2 n)
  -- from this, the convergence of `s n` to `t0` follows.
  refine EMetric.tendsto_atTop.2 fun ε εpos => ?_
  have : Tendsto (fun n => 2 * B n) atTop (𝓝 (2 * 0)) :=
    ENNReal.Tendsto.const_mul (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one <|
by simp) (Or.inr by simp)
  rw [mul_zero] at this
  obtain ⟨N, hN⟩ : exists N, forall b >= N, ε > 2 * B b :=
    ((tendsto_order.1 this).2 ε εpos).exists_forall_of_atTop
  exact ⟨N, fun n hn => lt_of_le_of_lt (main n) (hN n hn)⟩

/--
theorem `isometry_singleton` / 定理 `isometry_singleton`

English:
theorem isometry_singleton
  statement: Isometry ({·} : α -> Closeds α)
  proof: fun _ _ => hausdorffEDist_singleton

中文:
定理 isometry_singleton
  结论: 等距 ({·} : α -> Closeds α)
  证明: fun _ _ => hausdorffEDist_singleton

Depends on / 依赖: hausdorffEDist_singleton
-/
theorem isometry_singleton : Isometry ({·} : α -> Closeds α) :=
  fun _ _ => hausdorffEDist_singleton

/--
theorem `lipschitz_sup` / 定理 `lipschitz_sup`

English:
theorem lipschitz_sup
  statement: LipschitzWith 1 fun p : Closeds α × Closeds α => p.1 ⊔ p.2
  proof: .of_edist_le fun _ _ => hausdorffEDist_union_le

中文:
定理 lipschitz_sup
  结论: LipschitzWith 1 fun p : Closeds α × Closeds α => p.1 ⊔ p.2
  证明: .of_edist_le fun _ _ => hausdorffEDist_union_le

Depends on / 依赖: hausdorffEDist_union_le, of_edist_le
-/
theorem lipschitz_sup : LipschitzWith 1 fun p : Closeds α × Closeds α => p.1 ⊔ p.2 :=
  .of_edist_le fun _ _ => hausdorffEDist_union_le

/--
theorem `lipschitz_prod` / 定理 `lipschitz_prod`

English:
theorem lipschitz_prod
  statement: LipschitzWith 1 fun p : Closeds α × Closeds β => p.1 ×ˢ p.2
  proof: .of_edist_le fun _ _ => hausdorffEDist_prod_le

中文:
定理 lipschitz_prod
  结论: LipschitzWith 1 fun p : Closeds α × Closeds β => p.1 ×ˢ p.2
  证明: .of_edist_le fun _ _ => hausdorffEDist_prod_le

Depends on / 依赖: hausdorffEDist_prod_le, of_edist_le
-/
theorem lipschitz_prod : LipschitzWith 1 fun p : Closeds α × Closeds β => p.1 ×ˢ p.2 :=
  .of_edist_le fun _ _ => hausdorffEDist_prod_le

end Closeds

namespace Compacts

/--
Instance `instEMetricSpace` / 实例 `instEMetricSpace`

English:
instance instEMetricSpace
  signature: : EMetricSpace (Compacts α) where
  body: (PseudoEMetricSpace.hausdorff.induced SetLike.coe).replaceUniformity by rfl
eq_of_edist_eq_zero {s t} h := Compacts.ext by
    have : closure (s : Set α) = closure t := hausdorffEDist_zero_iff_closure_eq_closure.1 h
    rwa [s.isCompact.isClosed.closure_eq, t.isCompact.isClosed.closure_eq] at this

中文:
实例 instEMetricSpace
  签名: : 广义度量空间 (余mpacts α) where
  定义体: (PseudoEMetricSpace.hausdorff.induced SetLike.coe).replaceUniformity by rfl
eq_of_edist_eq_zero {s t} h := Compacts.ext by
    have : closure (s : Set α) = closure t := hausdorffEDist_zero_iff_closure_eq_closure.1 h
    rwa [s.isCompact.isClosed.closure_eq, t.isCompact.isClosed.closure_eq] at this

Depends on / 依赖: PseudoEMetricSpace, PseudoEMetricSpace.hausdorff.induced, SetLike, SetLike.coe, hausdorff, induced, replaceUniformity
-/
instance instEMetricSpace : EMetricSpace (Compacts α) where
  /- Since the topology on `Compacts` is not defeq to the one induced by
  `UniformSpace.hausdorff`, we replace the uniformity by `Compacts.uniformSpace`, which has
  the right topology. -/
__ := (PseudoEMetricSpace.hausdorff.induced SetLike.coe).replaceUniformity by rfl
eq_of_edist_eq_zero {s t} h := Compacts.ext by
    have : closure (s : Set α) = closure t := hausdorffEDist_zero_iff_closure_eq_closure.1 h
    rwa [s.isCompact.isClosed.closure_eq, t.isCompact.isClosed.closure_eq] at this

/--
theorem `edist_eq` / 定理 `edist_eq`

English:
theorem edist_eq
  given: {s t : Compacts α}
  statement: edist s t = hausdorffEDist (s : Set α) t
  proof: rfl

中文:
定理 edist_eq
  条件: {s t : 余mpacts α}
  结论: edist s t = hausdorffEDist (s : 集合 α) t
  证明: rfl
-/
theorem edist_eq {s t : Compacts α} : edist s t = hausdorffEDist (s : Set α) t :=
  rfl

/--
theorem `isometry_toCloseds` / 定理 `isometry_toCloseds`

English:
theorem isometry_toCloseds
  statement: Isometry (Compacts.toCloseds (α := α))
  proof: fun _ _ => rfl

中文:
定理 isometry_toCloseds
  结论: 等距 (余mpacts.toCloseds (α := α))
  证明: fun _ _ => rfl
-/
theorem isometry_toCloseds : Isometry (Compacts.toCloseds (α := α)) :=
  fun _ _ => rfl

/--
theorem `isometry_singleton` / 定理 `isometry_singleton`

English:
theorem isometry_singleton
  statement: Isometry ({·} : α -> Compacts α)
  proof: fun _ _ => hausdorffEDist_singleton

中文:
定理 isometry_singleton
  结论: 等距 ({·} : α -> 余mpacts α)
  证明: fun _ _ => hausdorffEDist_singleton

Depends on / 依赖: hausdorffEDist_singleton
-/
theorem isometry_singleton : Isometry ({·} : α -> Compacts α) :=
  fun _ _ => hausdorffEDist_singleton

/--
theorem `lipschitz_sup` / 定理 `lipschitz_sup`

English:
theorem lipschitz_sup
  proof: .of_edist_le fun _ _ => hausdorffEDist_union_le

中文:
定理 lipschitz_sup
  证明: .of_edist_le fun _ _ => hausdorffEDist_union_le

Depends on / 依赖: hausdorffEDist_union_le, of_edist_le
-/
theorem lipschitz_sup :
    LipschitzWith 1 fun p : Compacts α × Compacts α => p.1 ⊔ p.2 :=
  .of_edist_le fun _ _ => hausdorffEDist_union_le

/--
theorem `lipschitz_prod` / 定理 `lipschitz_prod`

English:
theorem lipschitz_prod
  proof: .of_edist_le fun _ _ => hausdorffEDist_prod_le

中文:
定理 lipschitz_prod
  证明: .of_edist_le fun _ _ => hausdorffEDist_prod_le

Depends on / 依赖: hausdorffEDist_prod_le, of_edist_le
-/
theorem lipschitz_prod :
    LipschitzWith 1 fun p : Compacts α × Compacts β => p.1 ×ˢ p.2 :=
  .of_edist_le fun _ _ => hausdorffEDist_prod_le

end Compacts

namespace NonemptyCompacts

/--
Instance `instEMetricSpace` / 实例 `instEMetricSpace`

English:
instance instEMetricSpace
  signature: : EMetricSpace (NonemptyCompacts α) where
  body: (PseudoEMetricSpace.hausdorff.induced SetLike.coe).replaceUniformity by rfl
eq_of_edist_eq_zero {s t} h := NonemptyCompacts.ext by
    have : closure (s : Set α) = closure t := hausdorffEDist_zero_iff_closure_eq_closure.1 h
    rwa [s.isCompact.isClosed.closure_eq, t.isCompact.isClosed.closure_eq] at this

中文:
实例 instEMetricSpace
  签名: : 广义度量空间 (NonemptyCompacts α) where
  定义体: (PseudoEMetricSpace.hausdorff.induced SetLike.coe).replaceUniformity by rfl
eq_of_edist_eq_zero {s t} h := NonemptyCompacts.ext by
    have : closure (s : Set α) = closure t := hausdorffEDist_zero_iff_closure_eq_closure.1 h
    rwa [s.isCompact.isClosed.closure_eq, t.isCompact.isClosed.closure_eq] at this

Depends on / 依赖: PseudoEMetricSpace, PseudoEMetricSpace.hausdorff.induced, SetLike, SetLike.coe, hausdorff, induced, replaceUniformity
-/
instance instEMetricSpace : EMetricSpace (NonemptyCompacts α) where
  /- Since the topology on `NonemptyCompacts` is not defeq to the one induced by
  `UniformSpace.hausdorff`, we replace the uniformity by `NonemptyCompacts.uniformSpace`, which has
  the right topology. -/
__ := (PseudoEMetricSpace.hausdorff.induced SetLike.coe).replaceUniformity by rfl
eq_of_edist_eq_zero {s t} h := NonemptyCompacts.ext by
    have : closure (s : Set α) = closure t := hausdorffEDist_zero_iff_closure_eq_closure.1 h
    rwa [s.isCompact.isClosed.closure_eq, t.isCompact.isClosed.closure_eq] at this

/--
theorem `isometry_toCloseds` / 定理 `isometry_toCloseds`

English:
theorem isometry_toCloseds
  statement: Isometry (@NonemptyCompacts.toCloseds α _ _)
  proof: fun _ _ => rfl

中文:
定理 isometry_toCloseds
  结论: 等距 (@NonemptyCompacts.toCloseds α _ _)
  证明: fun _ _ => rfl
-/
theorem isometry_toCloseds : Isometry (@NonemptyCompacts.toCloseds α _ _) :=
  fun _ _ => rfl

/--
theorem `isometry_toCompacts` / 定理 `isometry_toCompacts`

English:
theorem isometry_toCompacts
  statement: Isometry (NonemptyCompacts.toCompacts (α := α))
  proof: fun _ _ => rfl

中文:
定理 isometry_toCompacts
  结论: 等距 (NonemptyCompacts.toCompacts (α := α))
  证明: fun _ _ => rfl
-/
theorem isometry_toCompacts : Isometry (NonemptyCompacts.toCompacts (α := α)) :=
  fun _ _ => rfl

/-- The range of `NonemptyCompacts.toCloseds` is closed in a complete space -/
@[deprecated
  "Use `TopologicalSpace.NonemptyCompacts.isClosedEmbedding_toCloseds.isClosed_range` instead"
  (since := "2026-01-28")]
/--
theorem `isClosed_in_closeds` / 定理 `isClosed_in_closeds`

English:
theorem isClosed_in_closeds
  given: [CompleteSpace α]
  proof: NonemptyCompacts.isClosedEmbedding_toCloseds.isClosed_range

中文:
定理 isClosed_in_closeds
  条件: [完备空间 α]
  证明: NonemptyCompacts.isClosedEmbedding_toCloseds.isClosed_range

Depends on / 依赖: NonemptyCompacts, NonemptyCompacts.isClosedEmbedding_toCloseds.isClosed_range, isClosedEmbedding_toCloseds, isClosed_range
-/
theorem isClosed_in_closeds [CompleteSpace α] :
    IsClosed (range <| @NonemptyCompacts.toCloseds α _ _) :=
  NonemptyCompacts.isClosedEmbedding_toCloseds.isClosed_range

/--
theorem `isometry_singleton` / 定理 `isometry_singleton`

English:
theorem isometry_singleton
  statement: Isometry ({·} : α -> NonemptyCompacts α)
  proof: fun _ _ => hausdorffEDist_singleton

中文:
定理 isometry_singleton
  结论: 等距 ({·} : α -> NonemptyCompacts α)
  证明: fun _ _ => hausdorffEDist_singleton

Depends on / 依赖: hausdorffEDist_singleton
-/
theorem isometry_singleton : Isometry ({·} : α -> NonemptyCompacts α) :=
  fun _ _ => hausdorffEDist_singleton

/--
theorem `lipschitz_sup` / 定理 `lipschitz_sup`

English:
theorem lipschitz_sup
  proof: .of_edist_le fun _ _ => hausdorffEDist_union_le

中文:
定理 lipschitz_sup
  证明: .of_edist_le fun _ _ => hausdorffEDist_union_le

Depends on / 依赖: hausdorffEDist_union_le, of_edist_le
-/
theorem lipschitz_sup :
    LipschitzWith 1 fun p : NonemptyCompacts α × NonemptyCompacts α => p.1 ⊔ p.2 :=
  .of_edist_le fun _ _ => hausdorffEDist_union_le

/--
theorem `lipschitz_prod` / 定理 `lipschitz_prod`

English:
theorem lipschitz_prod
  proof: .of_edist_le fun _ _ => hausdorffEDist_prod_le

中文:
定理 lipschitz_prod
  证明: .of_edist_le fun _ _ => hausdorffEDist_prod_le

Depends on / 依赖: hausdorffEDist_prod_le, of_edist_le
-/
theorem lipschitz_prod :
    LipschitzWith 1 fun p : NonemptyCompacts α × NonemptyCompacts β => p.1 ×ˢ p.2 :=
  .of_edist_le fun _ _ => hausdorffEDist_prod_le

end NonemptyCompacts

end TopologicalSpace

namespace EMetric

open Metric

@[deprecated (since := "2026-01-08")]
alias mem_hausdorffEntourage_of_hausdorffEdist_lt :=
  mem_hausdorffEntourage_of_hausdorffEDist_lt

@[deprecated (since := "2026-01-08")]
alias hausdorffEdist_le_of_mem_hausdorffEntourage := hausdorffEDist_le_of_mem_hausdorffEntourage

@[deprecated (since := "2026-01-08")]
alias continuous_infEdist_hausdorffEdist :=
  TopologicalSpace.Closeds.continuous_infEDist

@[deprecated (since := "2026-01-08")]
alias Closeds.edist_eq := TopologicalSpace.Closeds.edist_eq

@[deprecated (since := "2026-01-08")]
alias Closeds.isometry_singleton := TopologicalSpace.Closeds.isometry_singleton

@[deprecated (since := "2026-01-08")]
alias Closeds.lipschitz_sup := TopologicalSpace.Closeds.lipschitz_sup

@[deprecated (since := "2026-01-08")]
alias NonemptyCompacts.isometry_toCloseds :=
  TopologicalSpace.NonemptyCompacts.isometry_toCloseds

@[deprecated (since := "2026-01-08")]
alias NonemptyCompacts.isClosed_in_closeds :=
  TopologicalSpace.NonemptyCompacts.isClosed_in_closeds

@[deprecated (since := "2026-01-08")]
alias NonemptyCompacts.isometry_singleton :=
  TopologicalSpace.NonemptyCompacts.isometry_singleton

@[deprecated (since := "2026-01-08")]
alias NonemptyCompacts.lipschitz_sup :=
  TopologicalSpace.NonemptyCompacts.lipschitz_sup

@[deprecated (since := "2026-01-08")]
alias NonemptyCompacts.lipschitz_prod :=
  TopologicalSpace.NonemptyCompacts.lipschitz_prod

end EMetric --namespace

namespace Metric

section

variable {α : Type*} [MetricSpace α]

/--
Instance `NonemptyCompacts.instMetricSpace` / 实例 `NonemptyCompacts.instMetricSpace`

English:
instance NonemptyCompacts.instMetricSpace
  signature: : MetricSpace (NonemptyCompacts α)
  body: EMetricSpace.toMetricSpace fun x y =>
    hausdorffEDist_ne_top_of_nonempty_of_bounded x.nonempty y.nonempty x.isCompact.isBounded
      y.isCompact.isBounded

中文:
实例 NonemptyCompacts.instMetricSpace
  签名: : 度量空间 (NonemptyCompacts α)
  定义体: EMetricSpace.toMetricSpace fun x y =>
    hausdorffEDist_ne_top_of_nonempty_of_bounded x.nonempty y.nonempty x.isCompact.isBounded
      y.isCompact.isBounded

Depends on / 依赖: EMetricSpace, EMetricSpace.toMetricSpace, hausdorffEDist_ne_top_of_nonempty_of_bounded, isBounded, isCompact, nonempty, toMetricSpace, x.isCompact.isBounded, x.nonempty, y.isCompact.isBounded, y.nonempty
-/
instance NonemptyCompacts.instMetricSpace : MetricSpace (NonemptyCompacts α) :=
  EMetricSpace.toMetricSpace fun x y =>
    hausdorffEDist_ne_top_of_nonempty_of_bounded x.nonempty y.nonempty x.isCompact.isBounded
      y.isCompact.isBounded

/--
theorem `NonemptyCompacts.dist_eq` / 定理 `NonemptyCompacts.dist_eq`

English:
theorem NonemptyCompacts.dist_eq
  given: {x y : NonemptyCompacts α}
  proof: rfl

中文:
定理 NonemptyCompacts.dist_eq
  条件: {x y : NonemptyCompacts α}
  证明: rfl
-/
theorem NonemptyCompacts.dist_eq {x y : NonemptyCompacts α} :
    dist x y = hausdorffDist (x : Set α) y :=
  rfl

/--
theorem `lipschitz_infDist_set` / 定理 `lipschitz_infDist_set`

English:
theorem lipschitz_infDist_set
  given: (x : α)
  statement: LipschitzWith 1 fun s : NonemptyCompacts α => infDist x s
  proof: LipschitzWith.of_le_add fun s t => by
    rw [dist_comm]
    exact infDist_le_infDist_add_hausdorffDist (edist_ne_top t s)

中文:
定理 lipschitz_infDist_set
  条件: (x : α)
  结论: LipschitzWith 1 fun s : NonemptyCompacts α => infDist x s
  证明: LipschitzWith.of_le_add fun s t => by
    rw [dist_comm]
    exact infDist_le_infDist_add_hausdorffDist (edist_ne_top t s)

Depends on / 依赖: LipschitzWith, LipschitzWith.of_le_add, dist_comm, edist_ne_top, infDist_le_infDist_add_hausdorffDist, of_le_add
-/
theorem lipschitz_infDist_set (x : α) : LipschitzWith 1 fun s : NonemptyCompacts α => infDist x s :=
  LipschitzWith.of_le_add fun s t => by
    rw [dist_comm]
    exact infDist_le_infDist_add_hausdorffDist (edist_ne_top t s)

/--
theorem `lipschitz_infDist` / 定理 `lipschitz_infDist`

English:
theorem lipschitz_infDist
  statement: LipschitzWith 2 fun p : α × NonemptyCompacts α => infDist p.1 p.2
  proof: by
  rw [← one_add_one_eq_two]
  exact LipschitzWith.uncurry
    (fun s : NonemptyCompacts α => lipschitz_infDist_pt (s : Set α)) lipschitz_infDist_set

中文:
定理 lipschitz_infDist
  结论: LipschitzWith 2 fun p : α × NonemptyCompacts α => infDist p.1 p.2
  证明: by
  rw [← one_add_one_eq_two]
  exact LipschitzWith.uncurry
    (fun s : NonemptyCompacts α => lipschitz_infDist_pt (s : Set α)) lipschitz_infDist_set

Depends on / 依赖: LipschitzWith, LipschitzWith.uncurry, NonemptyCompacts, lipschitz_infDist_pt, lipschitz_infDist_set, one_add_one_eq_two, uncurry
-/
theorem lipschitz_infDist : LipschitzWith 2 fun p : α × NonemptyCompacts α => infDist p.1 p.2 := by
  rw [← one_add_one_eq_two]
  exact LipschitzWith.uncurry
    (fun s : NonemptyCompacts α => lipschitz_infDist_pt (s : Set α)) lipschitz_infDist_set

/--
theorem `uniformContinuous_infDist_Hausdorff_dist` / 定理 `uniformContinuous_infDist_Hausdorff_dist`

English:
theorem uniformContinuous_infDist_Hausdorff_dist
  proof: lipschitz_infDist.uniformContinuous

中文:
定理 uniformContinuous_infDist_Hausdorff_dist
  证明: lipschitz_infDist.uniformContinuous

Depends on / 依赖: lipschitz_infDist, lipschitz_infDist.uniformContinuous, uniformContinuous
-/
theorem uniformContinuous_infDist_Hausdorff_dist :
    UniformContinuous fun p : α × NonemptyCompacts α => infDist p.1 p.2 :=
  lipschitz_infDist.uniformContinuous

end --section

end Metric --namespace
