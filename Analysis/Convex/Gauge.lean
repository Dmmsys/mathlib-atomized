/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise
public import Mathlib.Analysis.Seminorm
public import Mathlib.Analysis.LocallyConvex.Bounded
public import Mathlib.Analysis.RCLike.Basic

/-!
# The Minkowski functional

This file defines the Minkowski functional, aka gauge.

The Minkowski functional of a set `s` is the function which associates each point to how much you
need to scale `s` for `x` to be inside it. When `s` is symmetric, convex and absorbent, its gauge is
a seminorm. Reciprocally, any seminorm arises as the gauge of some set, namely its unit ball. This
induces the equivalence of seminorms and locally convex topological vector spaces.

## Main declarations

For a real vector space,
* `gauge`: Aka Minkowski functional. `gauge s x` is the least (actually, an infimum) `r` such
  that `x ∈ r • s`.
* `gaugeSeminorm`: The Minkowski functional as a seminorm, when `s` is symmetric, convex and
  absorbent.

## References

* [H. H. Schaefer, *Topological Vector Spaces*][schaefer1966]

## Tags

Minkowski functional, gauge
-/

@[expose] public section

open NormedField Set
open scoped Pointwise Topology NNReal

noncomputable section

variable {𝕜 E : Type*}

section AddCommGroup

variable [AddCommGroup E] [Module Real E]

/--
Definition of `gauge` / `gauge` 的定义

English:
definition gauge
  signature: (s : Set E) (x : E)
  body: sInf { r : Real | 0 < r ∧ x in r • s }

中文:
定义 gauge
  签名: (s : 集合 E) (x : E)
  定义体: sInf { r : Real | 0 < r ∧ x in r • s }
-/
def gauge (s : Set E) (x : E) : Real :=
  sInf { r : Real | 0 < r ∧ x in r • s }

variable {s t : Set E} {x : E} {a : Real}

/--
theorem `gauge_def` / 定理 `gauge_def`

English:
theorem gauge_def
  statement: gauge s x = sInf ({ r in Set.Ioi (0 : Real) | x in r • s })
  proof: rfl

中文:
定理 gauge_def
  结论: gauge s x = sInf ({ r in 集合.左开右无界区间 (0 : 实数) | x in r • s })
  证明: rfl
-/
theorem gauge_def : gauge s x = sInf ({ r in Set.Ioi (0 : Real) | x in r • s }) :=
  rfl

/--
theorem `gauge_def'` / 定理 `gauge_def'`

English:
theorem gauge_def'
  statement: gauge s x = sInf {r in Set.Ioi (0 : Real) | r⁻¹ • x in s}
  proof: by
  congrm sInf {r | ?_}
  exact and_congr_right fun hr => mem_smul_set_iff_inv_smul_mem₀ hr.ne' _ _

中文:
定理 gauge_def'
  结论: gauge s x = sInf {r in 集合.左开右无界区间 (0 : 实数) | r⁻¹ • x in s}
  证明: by
  congrm sInf {r | ?_}
  exact and_congr_right fun hr => mem_smul_set_iff_inv_smul_mem₀ hr.ne' _ _

Depends on / 依赖: and_congr_right, congrm, hr.ne
-/
theorem gauge_def' : gauge s x = sInf {r in Set.Ioi (0 : Real) | r⁻¹ • x in s} := by
  congrm sInf {r | ?_}
  exact and_congr_right fun hr => mem_smul_set_iff_inv_smul_mem₀ hr.ne' _ _

/--
theorem `bddBelow_gauge_set` / 定理 `bddBelow_gauge_set`

English:
theorem bddBelow_gauge_set
  statement: BddBelow { r : Real | 0 < r ∧ x in r • s }
  proof: ⟨0, fun _ hr => hr.1.le⟩

中文:
定理 bddBelow_gauge_set
  结论: BddBelow { r : 实数 | 0 < r ∧ x in r • s }
  证明: ⟨0, fun _ hr => hr.1.le⟩
-/
private theorem bddBelow_gauge_set : BddBelow { r : Real | 0 < r ∧ x in r • s } :=
  ⟨0, fun _ hr => hr.1.le⟩

/--
theorem `Absorbent.gauge_set_nonempty` / 定理 `Absorbent.gauge_set_nonempty`

English:
theorem Absorbent.gauge_set_nonempty
  given: (absorbs : Absorbent Real s)
  proof: let ⟨r, hr₁, hr₂⟩ := (absorbs x).exists_pos
  ⟨r, hr₁, hr₂ r (Real.norm_of_nonneg hr₁.le).ge rfl⟩

中文:
定理 Absorbent.gauge_set_nonempty
  条件: (absorbs : Absorbent 实数 s)
  证明: let ⟨r, hr₁, hr₂⟩ := (absorbs x).exists_pos
  ⟨r, hr₁, hr₂ r (Real.norm_of_nonneg hr₁.le).ge rfl⟩

Depends on / 依赖: Real.norm_of_nonneg, absorbs, exists_pos, norm_of_nonneg
-/
theorem Absorbent.gauge_set_nonempty (absorbs : Absorbent Real s) :
    { r : Real | 0 < r ∧ x in r • s }.Nonempty :=
  let ⟨r, hr₁, hr₂⟩ := (absorbs x).exists_pos
  ⟨r, hr₁, hr₂ r (Real.norm_of_nonneg hr₁.le).ge rfl⟩

/--
theorem `gauge_mono` / 定理 `gauge_mono`

English:
theorem gauge_mono
  given: (hs : Absorbent Real s) (h : s subseteq t)
  statement: gauge t <= gauge s
  proof: fun _ => by
  unfold gauge
  gcongr; exacts [bddBelow_gauge_set, hs.gauge_set_nonempty]

中文:
定理 gauge_mono
  条件: (hs : Absorbent 实数 s) (h : s subseteq t)
  结论: gauge t <= gauge s
  证明: fun _ => by
  unfold gauge
  gcongr; exacts [bddBelow_gauge_set, hs.gauge_set_nonempty]

Depends on / 依赖: bddBelow_gauge_set, exacts, gauge_set_nonempty, hs.gauge_set_nonempty
-/
theorem gauge_mono (hs : Absorbent Real s) (h : s subseteq t) : gauge t <= gauge s := fun _ => by
  unfold gauge
  gcongr; exacts [bddBelow_gauge_set, hs.gauge_set_nonempty]

/--
theorem `exists_lt_of_gauge_lt` / 定理 `exists_lt_of_gauge_lt`

English:
theorem exists_lt_of_gauge_lt
  given: (absorbs : Absorbent Real s) (h : gauge s x < a)
  proof: by
  obtain ⟨b, ⟨hb, hx⟩, hba⟩ := exists_lt_of_csInf_lt absorbs.gauge_set_nonempty h
  exact ⟨b, hb, hba, hx⟩

中文:
定理 存在_lt_of_gauge_lt
  条件: (absorbs : Absorbent 实数 s) (h : gauge s x < a)
  证明: by
  obtain ⟨b, ⟨hb, hx⟩, hba⟩ := exists_lt_of_csInf_lt absorbs.gauge_set_nonempty h
  exact ⟨b, hb, hba, hx⟩

Depends on / 依赖: absorbs, absorbs.gauge_set_nonempty, exists_lt_of_csInf_lt, gauge_set_nonempty
-/
theorem exists_lt_of_gauge_lt (absorbs : Absorbent Real s) (h : gauge s x < a) :
    exists b, 0 < b ∧ b < a ∧ x in b • s := by
  obtain ⟨b, ⟨hb, hx⟩, hba⟩ := exists_lt_of_csInf_lt absorbs.gauge_set_nonempty h
  exact ⟨b, hb, hba, hx⟩

/-- The gauge evaluated at `0` is always zero (mathematically this requires `0` to be in the set `s`
but, the real infimum of the empty set in Lean being defined as `0`, it holds unconditionally). -/
@[simp]
/--
theorem `gauge_zero` / 定理 `gauge_zero`

English:
theorem gauge_zero
  statement: gauge s 0 = 0
  proof: by
  rw [gauge_def']
  by_cases h : (0 : E) in s
  · simp only [smul_zero, sep_true, h, csInf_Ioi]
  · simp only [smul_zero, sep_false, h, Real.sInf_empty]

@[simp]

中文:
定理 gauge_zero
  结论: gauge s 0 = 0
  证明: by
  rw [gauge_def']
  by_cases h : (0 : E) in s
  · simp only [smul_zero, sep_true, h, csInf_Ioi]
  · simp only [smul_zero, sep_false, h, Real.sInf_empty]

@[simp]

Depends on / 依赖: Real.sInf_empty, csInf_Ioi, gauge_def, sInf_empty, sep_false, sep_true, smul_zero
-/
theorem gauge_zero : gauge s 0 = 0 := by
  rw [gauge_def']
  by_cases h : (0 : E) in s
  · simp only [smul_zero, sep_true, h, csInf_Ioi]
  · simp only [smul_zero, sep_false, h, Real.sInf_empty]

@[simp]
/--
theorem `gauge_zero'` / 定理 `gauge_zero'`

English:
theorem gauge_zero'
  statement: gauge (0 : Set E) = 0
  proof: by
  ext x
  rw [gauge_def']
  obtain rfl | hx := eq_or_ne x 0
  · simp only [csInf_Ioi, mem_zero, Pi.zero_apply, sep_true, smul_zero]
  · simp only [mem_zero, Pi.zero_apply, inv_eq_zero, smul_eq_zero]
    convert! Real.sInf_empty
    exact eq_empty_iff_forall_notMem.2 fun r hr => hr.2.elim (ne_of_g

中文:
定理 gauge_zero'
  结论: gauge (0 : 集合 E) = 0
  证明: by
  ext x
  rw [gauge_def']
  obtain rfl | hx := eq_or_ne x 0
  · simp only [csInf_Ioi, mem_zero, Pi.zero_apply, sep_true, smul_zero]
  · simp only [mem_zero, Pi.zero_apply, inv_eq_zero, smul_eq_zero]
    convert! Real.sInf_empty
    exact eq_empty_iff_forall_notMem.2 fun r hr => hr.2.elim (ne_of_g

Depends on / 依赖: Pi.zero_apply, Real.sInf_empty, convert, csInf_Ioi, eq_empty_iff_forall_notMem, eq_or_ne, gauge_def, inv_eq_zero, mem_zero, ne_of_gt, sInf_empty, sep_true, smul_eq_zero, smul_zero, zero_apply
-/
theorem gauge_zero' : gauge (0 : Set E) = 0 := by
  ext x
  rw [gauge_def']
  obtain rfl | hx := eq_or_ne x 0
  · simp only [csInf_Ioi, mem_zero, Pi.zero_apply, sep_true, smul_zero]
  · simp only [mem_zero, Pi.zero_apply, inv_eq_zero, smul_eq_zero]
    convert! Real.sInf_empty
    exact eq_empty_iff_forall_notMem.2 fun r hr => hr.2.elim (ne_of_gt hr.1) hx

@[simp]
/--
theorem `gauge_empty` / 定理 `gauge_empty`

English:
theorem gauge_empty
  statement: gauge (∅ : Set E) = 0
  proof: by
  ext
  simp only [gauge_def', Real.sInf_empty, mem_empty_iff_false, Pi.zero_apply, sep_false]

中文:
定理 gauge_empty
  结论: gauge (∅ : 集合 E) = 0
  证明: by
  ext
  simp only [gauge_def', Real.sInf_empty, mem_empty_iff_false, Pi.zero_apply, sep_false]

Depends on / 依赖: Pi.zero_apply, Real.sInf_empty, gauge_def, mem_empty_iff_false, sInf_empty, sep_false, zero_apply
-/
theorem gauge_empty : gauge (∅ : Set E) = 0 := by
  ext
  simp only [gauge_def', Real.sInf_empty, mem_empty_iff_false, Pi.zero_apply, sep_false]

/--
theorem `gauge_of_subset_zero` / 定理 `gauge_of_subset_zero`

English:
theorem gauge_of_subset_zero
  given: (h : s subseteq 0)
  statement: gauge s = 0
  proof: by
  obtain rfl | rfl := subset_singleton_iff_eq.1 h
  exacts [gauge_empty, gauge_zero']

中文:
定理 gauge_of_subset_zero
  条件: (h : s subseteq 0)
  结论: gauge s = 0
  证明: by
  obtain rfl | rfl := subset_singleton_iff_eq.1 h
  exacts [gauge_empty, gauge_zero']

Depends on / 依赖: exacts, gauge_empty, gauge_zero, subset_singleton_iff_eq
-/
theorem gauge_of_subset_zero (h : s subseteq 0) : gauge s = 0 := by
  obtain rfl | rfl := subset_singleton_iff_eq.1 h
  exacts [gauge_empty, gauge_zero']

/--
theorem `gauge_nonneg` / 定理 `gauge_nonneg`

English:
theorem gauge_nonneg
  given: (x : E)
  statement: 0 <= gauge s x
  proof: Real.sInf_nonneg fun _ hx => hx.1.le

中文:
定理 gauge_nonneg
  条件: (x : E)
  结论: 0 <= gauge s x
  证明: Real.sInf_nonneg fun _ hx => hx.1.le

Depends on / 依赖: Real.sInf_nonneg, sInf_nonneg
-/
theorem gauge_nonneg (x : E) : 0 <= gauge s x :=
  Real.sInf_nonneg fun _ hx => hx.1.le

/--
theorem `gauge_neg` / 定理 `gauge_neg`

English:
theorem gauge_neg
  given: (symmetric : forall x in s, -x in s) (x : E)
  statement: gauge s (-x) = gauge s x
  proof: by
  have : forall x, -x in s ↔ x in s := fun x => ⟨fun h => by simpa using symmetric _ h, symmetric x⟩
  simp_rw [gauge_def', smul_neg, this]

中文:
定理 gauge_neg
  条件: (symmetric : 对任意 x in s, -x in s) (x : E)
  结论: gauge s (-x) = gauge s x
  证明: by
  have : forall x, -x in s ↔ x in s := fun x => ⟨fun h => by simpa using symmetric _ h, symmetric x⟩
  simp_rw [gauge_def', smul_neg, this]

Depends on / 依赖: gauge_def, simp_rw, smul_neg, symmetric
-/
theorem gauge_neg (symmetric : forall x in s, -x in s) (x : E) : gauge s (-x) = gauge s x := by
  have : forall x, -x in s ↔ x in s := fun x => ⟨fun h => by simpa using symmetric _ h, symmetric x⟩
  simp_rw [gauge_def', smul_neg, this]

/--
theorem `gauge_neg_set_neg` / 定理 `gauge_neg_set_neg`

English:
theorem gauge_neg_set_neg
  given: (x : E)
  statement: gauge (-s) (-x) = gauge s x
  proof: by
  simp_rw [gauge_def', smul_neg, neg_mem_neg]

中文:
定理 gauge_neg_set_neg
  条件: (x : E)
  结论: gauge (-s) (-x) = gauge s x
  证明: by
  simp_rw [gauge_def', smul_neg, neg_mem_neg]

Depends on / 依赖: gauge_def, neg_mem_neg, simp_rw, smul_neg
-/
theorem gauge_neg_set_neg (x : E) : gauge (-s) (-x) = gauge s x := by
  simp_rw [gauge_def', smul_neg, neg_mem_neg]

/--
theorem `gauge_neg_set_eq_gauge_neg` / 定理 `gauge_neg_set_eq_gauge_neg`

English:
theorem gauge_neg_set_eq_gauge_neg
  given: (x : E)
  statement: gauge (-s) x = gauge s (-x)
  proof: by
  rw [← gauge_neg_set_neg]; rw [neg_neg]

中文:
定理 gauge_neg_set_eq_gauge_neg
  条件: (x : E)
  结论: gauge (-s) x = gauge s (-x)
  证明: by
  rw [← gauge_neg_set_neg]; rw [neg_neg]

Depends on / 依赖: gauge_neg_set_neg, neg_neg
-/
theorem gauge_neg_set_eq_gauge_neg (x : E) : gauge (-s) x = gauge s (-x) := by
  rw [← gauge_neg_set_neg]; rw [neg_neg]

/--
theorem `gauge_le_of_mem` / 定理 `gauge_le_of_mem`

English:
theorem gauge_le_of_mem
  given: (ha : 0 <= a) (hx : x in a • s)
  statement: gauge s x <= a
  proof: by
  obtain rfl | ha' := ha.eq_or_lt
  · rw [mem_singleton_iff.1 (zero_smul_set_subset _ hx), gauge_zero]
  · exact csInf_le bddBelow_gauge_set ⟨ha', hx⟩

中文:
定理 gauge_le_of_mem
  条件: (ha : 0 <= a) (hx : x in a • s)
  结论: gauge s x <= a
  证明: by
  obtain rfl | ha' := ha.eq_or_lt
  · rw [mem_singleton_iff.1 (zero_smul_set_subset _ hx), gauge_zero]
  · exact csInf_le bddBelow_gauge_set ⟨ha', hx⟩

Depends on / 依赖: bddBelow_gauge_set, csInf_le, eq_or_lt, gauge_zero, ha.eq_or_lt, mem_singleton_iff, zero_smul_set_subset
-/
theorem gauge_le_of_mem (ha : 0 <= a) (hx : x in a • s) : gauge s x <= a := by
  obtain rfl | ha' := ha.eq_or_lt
  · rw [mem_singleton_iff.1 (zero_smul_set_subset _ hx), gauge_zero]
  · exact csInf_le bddBelow_gauge_set ⟨ha', hx⟩

/--
theorem `setOfPred_gauge_le_eq` / 定理 `setOfPred_gauge_le_eq`

English:
theorem setOfPred_gauge_le_eq
  statement: (hs₁ : Convex Real s) (hs₀ : (0 : E) in s) (hs₂ : Absorbent Real s)
  proof: by
  ext x
  simp_rw [Set.mem_iInter, Set.mem_ofPred_eq]
  refine ⟨fun h r hr => ?_, fun h => le_of_forall_pos_lt_add fun ε hε => ?_⟩
  · have hr' := ha.trans_lt hr
    rw [mem_smul_set_iff_inv_smul_mem₀ hr'.ne']
    obtain ⟨δ, δ_pos, hδr, hδ⟩ := exists_lt_of_gauge_lt hs₂ (h.trans_lt hr)
    suffice

中文:
定理 setOfPred_gauge_le_eq
  结论: (hs₁ : 凸 实数 s) (hs₀ : (0 : E) in s) (hs₂ : Absorbent 实数 s)
  证明: by
  ext x
  simp_rw [Set.mem_iInter, Set.mem_ofPred_eq]
  refine ⟨fun h r hr => ?_, fun h => le_of_forall_pos_lt_add fun ε hε => ?_⟩
  · have hr' := ha.trans_lt hr
    rw [mem_smul_set_iff_inv_smul_mem₀ hr'.ne']
    obtain ⟨δ, δ_pos, hδr, hδ⟩ := exists_lt_of_gauge_lt hs₂ (h.trans_lt hr)
    suffice

Depends on / 依赖: Set.mem_iInter, Set.mem_ofPred_eq, _pos.ne, exists_lt_of_gauge_lt, h.trans_lt, ha.trans_lt, le_of_forall_pos_lt_add, mem_iInter, mem_ofPred_eq, simp_rw, smul_mem_of_zero_mem, smul_smul, trans_lt
-/
theorem setOfPred_gauge_le_eq (hs₁ : Convex Real s) (hs₀ : (0 : E) in s) (hs₂ : Absorbent Real s)
    (ha : 0 <= a) : { x | gauge s x <= a } = ⋂ (r : Real) (_ : a < r), r • s := by
  ext x
  simp_rw [Set.mem_iInter, Set.mem_ofPred_eq]
  refine ⟨fun h r hr => ?_, fun h => le_of_forall_pos_lt_add fun ε hε => ?_⟩
  · have hr' := ha.trans_lt hr
    rw [mem_smul_set_iff_inv_smul_mem₀ hr'.ne']
    obtain ⟨δ, δ_pos, hδr, hδ⟩ := exists_lt_of_gauge_lt hs₂ (h.trans_lt hr)
    suffices (r⁻¹ * δ) • δ⁻¹ • x in s by rwa [smul_smul, mul_inv_cancel_right₀ δ_pos.ne'] at this
    rw [mem_smul_set_iff_inv_smul_mem₀ δ_pos.ne'] at hδ
    refine hs₁.smul_mem_of_zero_mem hs₀ hδ ⟨by positivity, ?_⟩
    rw [inv_mul_le_iff₀ hr']; rw [mul_one]
    exact hδr.le
  · linarith [gauge_le_of_mem (by linarith) <| h (a + ε / 2) (by linarith)]

@[deprecated (since := "2026-07-09")]
alias setOf_gauge_le_eq := setOfPred_gauge_le_eq

@[deprecated (since := "2026-06-17")] alias gauge_le_eq := setOfPred_gauge_le_eq

/--
theorem `setOfPred_gauge_lt_eq'` / 定理 `setOfPred_gauge_lt_eq'`

English:
theorem setOfPred_gauge_lt_eq'
  given: (absorbs : Absorbent Real s) (a : Real)
  proof: by
  ext
  simp_rw [mem_ofPred, mem_iUnion, exists_prop]
  exact
    ⟨exists_lt_of_gauge_lt absorbs, fun ⟨r, hr₀, hr₁, hx⟩ =>
      (gauge_le_of_mem hr₀.le hx).trans_lt hr₁⟩

@[deprecated (since := "2026-07-09")]
alias setOf_gauge_lt_eq' := setOfPred_gauge_lt_eq'

@[deprecated (since := "2026-06-17"

中文:
定理 setOfPred_gauge_lt_eq'
  条件: (absorbs : Absorbent 实数 s) (a : 实数)
  证明: by
  ext
  simp_rw [mem_ofPred, mem_iUnion, exists_prop]
  exact
    ⟨exists_lt_of_gauge_lt absorbs, fun ⟨r, hr₀, hr₁, hx⟩ =>
      (gauge_le_of_mem hr₀.le hx).trans_lt hr₁⟩

@[deprecated (since := "2026-07-09")]
alias setOf_gauge_lt_eq' := setOfPred_gauge_lt_eq'

@[deprecated (since := "2026-06-17"

Depends on / 依赖: absorbs, exists_lt_of_gauge_lt, exists_prop, gauge_le_of_mem, mem_iUnion, mem_ofPred, simp_rw, trans_lt
-/
theorem setOfPred_gauge_lt_eq' (absorbs : Absorbent Real s) (a : Real) :
    { x | gauge s x < a } = ⋃ (r : Real) (_ : 0 < r) (_ : r < a), r • s := by
  ext
  simp_rw [mem_ofPred, mem_iUnion, exists_prop]
  exact
    ⟨exists_lt_of_gauge_lt absorbs, fun ⟨r, hr₀, hr₁, hx⟩ =>
      (gauge_le_of_mem hr₀.le hx).trans_lt hr₁⟩

@[deprecated (since := "2026-07-09")]
alias setOf_gauge_lt_eq' := setOfPred_gauge_lt_eq'

@[deprecated (since := "2026-06-17")] alias gauge_lt_eq' := setOfPred_gauge_lt_eq'

/--
theorem `setOfPred_gauge_lt_eq` / 定理 `setOfPred_gauge_lt_eq`

English:
theorem setOfPred_gauge_lt_eq
  given: (absorbs : Absorbent Real s) (a : Real)
  proof: by
  ext
  simp_rw [mem_ofPred, mem_iUnion, exists_prop, mem_Ioo, and_assoc]
  exact
    ⟨exists_lt_of_gauge_lt absorbs, fun ⟨r, hr₀, hr₁, hx⟩ =>
      (gauge_le_of_mem hr₀.le hx).trans_lt hr₁⟩

@[deprecated (since := "2026-07-09")]
alias setOf_gauge_lt_eq := setOfPred_gauge_lt_eq

@[deprecated (sin

中文:
定理 setOfPred_gauge_lt_eq
  条件: (absorbs : Absorbent 实数 s) (a : 实数)
  证明: by
  ext
  simp_rw [mem_ofPred, mem_iUnion, exists_prop, mem_Ioo, and_assoc]
  exact
    ⟨exists_lt_of_gauge_lt absorbs, fun ⟨r, hr₀, hr₁, hx⟩ =>
      (gauge_le_of_mem hr₀.le hx).trans_lt hr₁⟩

@[deprecated (since := "2026-07-09")]
alias setOf_gauge_lt_eq := setOfPred_gauge_lt_eq

@[deprecated (sin

Depends on / 依赖: absorbs, and_assoc, exists_lt_of_gauge_lt, exists_prop, gauge_le_of_mem, mem_Ioo, mem_iUnion, mem_ofPred, simp_rw, trans_lt
-/
theorem setOfPred_gauge_lt_eq (absorbs : Absorbent Real s) (a : Real) :
    { x | gauge s x < a } = ⋃ r in Set.Ioo 0 (a : Real), r • s := by
  ext
  simp_rw [mem_ofPred, mem_iUnion, exists_prop, mem_Ioo, and_assoc]
  exact
    ⟨exists_lt_of_gauge_lt absorbs, fun ⟨r, hr₀, hr₁, hx⟩ =>
      (gauge_le_of_mem hr₀.le hx).trans_lt hr₁⟩

@[deprecated (since := "2026-07-09")]
alias setOf_gauge_lt_eq := setOfPred_gauge_lt_eq

@[deprecated (since := "2026-06-17")] alias gauge_lt_eq := setOfPred_gauge_lt_eq

/--
theorem `mem_openSegment_of_gauge_lt_one` / 定理 `mem_openSegment_of_gauge_lt_one`

English:
theorem mem_openSegment_of_gauge_lt_one
  given: (absorbs : Absorbent Real s) (hgauge : gauge s x < 1)
  proof: by
  rcases exists_lt_of_gauge_lt absorbs hgauge with ⟨r, hr₀, hr₁, y, hy, rfl⟩
  refine ⟨y, hy, 1 - r, r, ?_⟩
  simp [*]

中文:
定理 mem_openSegment_of_gauge_lt_one
  条件: (absorbs : Absorbent 实数 s) (hgauge : gauge s x < 1)
  证明: by
  rcases exists_lt_of_gauge_lt absorbs hgauge with ⟨r, hr₀, hr₁, y, hy, rfl⟩
  refine ⟨y, hy, 1 - r, r, ?_⟩
  simp [*]

Depends on / 依赖: absorbs, exists_lt_of_gauge_lt, hgauge
-/
theorem mem_openSegment_of_gauge_lt_one (absorbs : Absorbent Real s) (hgauge : gauge s x < 1) :
    exists y in s, x in openSegment Real 0 y := by
  rcases exists_lt_of_gauge_lt absorbs hgauge with ⟨r, hr₀, hr₁, y, hy, rfl⟩
  refine ⟨y, hy, 1 - r, r, ?_⟩
  simp [*]

/--
theorem `setOfPred_gauge_lt_one_subset_self` / 定理 `setOfPred_gauge_lt_one_subset_self`

English:
theorem setOfPred_gauge_lt_one_subset_self
  statement: (hs : Convex Real s) (h₀ : (0 : E) in s)
  proof: fun _x hx =>
  let ⟨_y, hys, hx⟩ := mem_openSegment_of_gauge_lt_one absorbs hx
  hs.openSegment_subset h₀ hys hx

@[deprecated (since := "2026-07-09")]
alias setOf_gauge_lt_one_subset_self := setOfPred_gauge_lt_one_subset_self

@[deprecated (since := "2026-06-17")]
alias gauge_lt_one_subset_self := 

中文:
定理 setOfPred_gauge_lt_one_subset_self
  结论: (hs : 凸 实数 s) (h₀ : (0 : E) in s)
  证明: fun _x hx =>
  let ⟨_y, hys, hx⟩ := mem_openSegment_of_gauge_lt_one absorbs hx
  hs.openSegment_subset h₀ hys hx

@[deprecated (since := "2026-07-09")]
alias setOf_gauge_lt_one_subset_self := setOfPred_gauge_lt_one_subset_self

@[deprecated (since := "2026-06-17")]
alias gauge_lt_one_subset_self := 
-/
theorem setOfPred_gauge_lt_one_subset_self (hs : Convex Real s) (h₀ : (0 : E) in s)
    (absorbs : Absorbent Real s) : { x | gauge s x < 1 } subseteq s := fun _x hx =>
  let ⟨_y, hys, hx⟩ := mem_openSegment_of_gauge_lt_one absorbs hx
  hs.openSegment_subset h₀ hys hx

@[deprecated (since := "2026-07-09")]
alias setOf_gauge_lt_one_subset_self := setOfPred_gauge_lt_one_subset_self

@[deprecated (since := "2026-06-17")]
alias gauge_lt_one_subset_self := setOfPred_gauge_lt_one_subset_self

/--
theorem `gauge_le_one_of_mem` / 定理 `gauge_le_one_of_mem`

English:
theorem gauge_le_one_of_mem
  given: {x : E} (hx : x in s)
  statement: gauge s x <= 1
  proof: gauge_le_of_mem zero_le_one by rwa [one_smul]

中文:
定理 gauge_le_one_of_mem
  条件: {x : E} (hx : x in s)
  结论: gauge s x <= 1
  证明: gauge_le_of_mem zero_le_one by rwa [one_smul]

Depends on / 依赖: gauge_le_of_mem, one_smul, zero_le_one
-/
theorem gauge_le_one_of_mem {x : E} (hx : x in s) : gauge s x <= 1 :=
gauge_le_of_mem zero_le_one by rwa [one_smul]

/--
theorem `gauge_add_le` / 定理 `gauge_add_le`

English:
theorem gauge_add_le
  given: (hs : Convex Real s) (absorbs : Absorbent Real s) (x y : E)
  proof: by
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨a, ha, ha', x, hx, rfl⟩ :=
    exists_lt_of_gauge_lt absorbs (lt_add_of_pos_right (gauge s x) (half_pos hε))
  obtain ⟨b, hb, hb', y, hy, rfl⟩ :=
    exists_lt_of_gauge_lt absorbs (lt_add_of_pos_right (gauge s y) (half_pos hε))
  calc
gaug

中文:
定理 gauge_add_le
  条件: (hs : 凸 实数 s) (absorbs : Absorbent 实数 s) (x y : E)
  证明: by
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨a, ha, ha', x, hx, rfl⟩ :=
    exists_lt_of_gauge_lt absorbs (lt_add_of_pos_right (gauge s x) (half_pos hε))
  obtain ⟨b, hb, hb', y, hy, rfl⟩ :=
    exists_lt_of_gauge_lt absorbs (lt_add_of_pos_right (gauge s y) (half_pos hε))
  calc
gaug

Depends on / 依赖: absorbs, add_mem_add, add_smul, exists_lt_of_gauge_lt, gauge_le_of_mem, ha.le, half_pos, hb.le, hs.add_smul, le_of_forall_pos_lt_add, lt_add_of_pos_right, smul_mem_smul_set
-/
theorem gauge_add_le (hs : Convex Real s) (absorbs : Absorbent Real s) (x y : E) :
    gauge s (x + y) <= gauge s x + gauge s y := by
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨a, ha, ha', x, hx, rfl⟩ :=
    exists_lt_of_gauge_lt absorbs (lt_add_of_pos_right (gauge s x) (half_pos hε))
  obtain ⟨b, hb, hb', y, hy, rfl⟩ :=
    exists_lt_of_gauge_lt absorbs (lt_add_of_pos_right (gauge s y) (half_pos hε))
  calc
gauge s (a • x + b • y) <= a + b := gauge_le_of_mem (by positivity) by
      rw [hs.add_smul ha.le hb.le]
      exact add_mem_add (smul_mem_smul_set hx) (smul_mem_smul_set hy)
    _ < gauge s (a • x) + gauge s (b • y) + ε := by linarith

/--
theorem `gauge_sum_le` / 定理 `gauge_sum_le`

English:
theorem gauge_sum_le
  statement: {ι : Type*} (hs : Convex Real s) (absorbs : Absorbent Real s) (t : Finset ι)
  proof: Finset.le_sum_of_subadditive _ gauge_zero.le (gauge_add_le hs absorbs) _ _

中文:
定理 gauge_sum_le
  结论: {ι : 类型} (hs : 凸 实数 s) (absorbs : Absorbent 实数 s) (t : 有限集 ι)
  证明: Finset.le_sum_of_subadditive _ gauge_zero.le (gauge_add_le hs absorbs) _ _

Depends on / 依赖: Finset, Finset.le_sum_of_subadditive, absorbs, gauge_add_le, gauge_zero, gauge_zero.le, le_sum_of_subadditive
-/
theorem gauge_sum_le {ι : Type*} (hs : Convex Real s) (absorbs : Absorbent Real s) (t : Finset ι)
    (f : ι -> E) : gauge s (∑ i in t, f i) <= ∑ i in t, gauge s (f i) :=
  Finset.le_sum_of_subadditive _ gauge_zero.le (gauge_add_le hs absorbs) _ _

/--
theorem `self_subset_setOfPred_gauge_le_one` / 定理 `self_subset_setOfPred_gauge_le_one`

English:
theorem self_subset_setOfPred_gauge_le_one
  statement: s subseteq { x | gauge s x <= 1 }
  proof: fun _ => gauge_le_one_of_mem

@[deprecated (since := "2026-07-09")]
alias self_subset_setOf_gauge_le_one := self_subset_setOfPred_gauge_le_one

@[deprecated (since := "2026-06-17")]
alias self_subset_gauge_le_one := self_subset_setOfPred_gauge_le_one

中文:
定理 self_subset_setOfPred_gauge_le_one
  结论: s subseteq { x | gauge s x <= 1 }
  证明: fun _ => gauge_le_one_of_mem

@[deprecated (since := "2026-07-09")]
alias self_subset_setOf_gauge_le_one := self_subset_setOfPred_gauge_le_one

@[deprecated (since := "2026-06-17")]
alias self_subset_gauge_le_one := self_subset_setOfPred_gauge_le_one

Depends on / 依赖: gauge_le_one_of_mem
-/
theorem self_subset_setOfPred_gauge_le_one : s subseteq { x | gauge s x <= 1 } :=
  fun _ => gauge_le_one_of_mem

@[deprecated (since := "2026-07-09")]
alias self_subset_setOf_gauge_le_one := self_subset_setOfPred_gauge_le_one

@[deprecated (since := "2026-06-17")]
alias self_subset_gauge_le_one := self_subset_setOfPred_gauge_le_one

/--
theorem `Convex.setOfPred_gauge_le` / 定理 `Convex.setOfPred_gauge_le`

English:
theorem Convex.setOfPred_gauge_le
  statement: (hs : Convex Real s) (h₀ : (0 : E) in s) (absorbs : Absorbent Real s)
  proof: by
  by_cases ha : 0 <= a
  · rw [setOfPred_gauge_le_eq hs h₀ absorbs ha]
    exact convex_iInter fun i => convex_iInter fun _ => hs.smul _
  · convert! convex_empty (𝕜 := Real)
exact eq_empty_iff_forall_notMem.2 fun x hx => ha (gauge_nonneg _).trans hx

@[deprecated (since := "2026-07-09")]
alias C

中文:
定理 凸.setOfPred_gauge_le
  结论: (hs : 凸 实数 s) (h₀ : (0 : E) in s) (absorbs : Absorbent 实数 s)
  证明: by
  by_cases ha : 0 <= a
  · rw [setOfPred_gauge_le_eq hs h₀ absorbs ha]
    exact convex_iInter fun i => convex_iInter fun _ => hs.smul _
  · convert! convex_empty (𝕜 := Real)
exact eq_empty_iff_forall_notMem.2 fun x hx => ha (gauge_nonneg _).trans hx

@[deprecated (since := "2026-07-09")]
alias C

Depends on / 依赖: absorbs, convert, convex_empty, convex_iInter, eq_empty_iff_forall_notMem, gauge_nonneg, hs.smul, setOfPred_gauge_le_eq
-/
theorem Convex.setOfPred_gauge_le (hs : Convex Real s) (h₀ : (0 : E) in s) (absorbs : Absorbent Real s)
    (a : Real) : Convex Real { x | gauge s x <= a } := by
  by_cases ha : 0 <= a
  · rw [setOfPred_gauge_le_eq hs h₀ absorbs ha]
    exact convex_iInter fun i => convex_iInter fun _ => hs.smul _
  · convert! convex_empty (𝕜 := Real)
exact eq_empty_iff_forall_notMem.2 fun x hx => ha (gauge_nonneg _).trans hx

@[deprecated (since := "2026-07-09")]
alias Convex.setOf_gauge_le := Convex.setOfPred_gauge_le

@[deprecated (since := "2026-06-17")] alias Convex.gauge_le := Convex.setOfPred_gauge_le

/--
theorem `le_gauge_of_notMem` / 定理 `le_gauge_of_notMem`

English:
theorem le_gauge_of_notMem
  given: (hs₀ : StarConvex Real 0 s) (hs₂ : Absorbs Real s {x}) (hx : x ∉ a • s)
  proof: by
  rw [starConvex_zero_iff] at hs₀
  obtain ⟨r, hr, h⟩ := hs₂.exists_pos
refine le_csInf ⟨r, hr, singleton_subset_iff.1 h _ (Real.norm_of_nonneg hr.le).ge⟩ ?_
  rintro b ⟨hb, x, hx', rfl⟩
  refine not_lt.1 fun hba => hx ?_
  have ha := hb.trans hba
  refine ⟨(a⁻¹ * b) • x, hs₀ hx' (by positivity) 

中文:
定理 le_gauge_of_notMem
  条件: (hs₀ : StarConvex 实数 0 s) (hs₂ : Absorbs 实数 s {x}) (hx : x ∉ a • s)
  证明: by
  rw [starConvex_zero_iff] at hs₀
  obtain ⟨r, hr, h⟩ := hs₂.exists_pos
refine le_csInf ⟨r, hr, singleton_subset_iff.1 h _ (Real.norm_of_nonneg hr.le).ge⟩ ?_
  rintro b ⟨hb, x, hx', rfl⟩
  refine not_lt.1 fun hba => hx ?_
  have ha := hb.trans hba
  refine ⟨(a⁻¹ * b) • x, hs₀ hx' (by positivity) 

Depends on / 依赖: Real.norm_of_nonneg, div_eq_inv_mul, exists_pos, ha.le, ha.ne, hb.trans, hba.le, hr.le, le_csInf, mul_smul, norm_of_nonneg, not_lt, singleton_subset_iff, starConvex_zero_iff
-/
theorem le_gauge_of_notMem (hs₀ : StarConvex Real 0 s) (hs₂ : Absorbs Real s {x}) (hx : x ∉ a • s) :
    a <= gauge s x := by
  rw [starConvex_zero_iff] at hs₀
  obtain ⟨r, hr, h⟩ := hs₂.exists_pos
refine le_csInf ⟨r, hr, singleton_subset_iff.1 h _ (Real.norm_of_nonneg hr.le).ge⟩ ?_
  rintro b ⟨hb, x, hx', rfl⟩
  refine not_lt.1 fun hba => hx ?_
  have ha := hb.trans hba
  refine ⟨(a⁻¹ * b) • x, hs₀ hx' (by positivity) ?_, ?_⟩
  · rw [← div_eq_inv_mul]
    exact div_le_one_of_le₀ hba.le ha.le
  · dsimp only
    rw [← mul_smul]; rw [mul_inv_cancel_left₀ ha.ne']

/--
theorem `one_le_gauge_of_notMem` / 定理 `one_le_gauge_of_notMem`

English:
theorem one_le_gauge_of_notMem
  given: (hs₁ : StarConvex Real 0 s) (hs₂ : Absorbs Real s {x}) (hx : x ∉ s)
  proof: le_gauge_of_notMem hs₁ hs₂ by rwa [one_smul]

中文:
定理 one_le_gauge_of_notMem
  条件: (hs₁ : StarConvex 实数 0 s) (hs₂ : Absorbs 实数 s {x}) (hx : x ∉ s)
  证明: le_gauge_of_notMem hs₁ hs₂ by rwa [one_smul]

Depends on / 依赖: le_gauge_of_notMem, one_smul
-/
theorem one_le_gauge_of_notMem (hs₁ : StarConvex Real 0 s) (hs₂ : Absorbs Real s {x}) (hx : x ∉ s) :
    1 <= gauge s x :=
le_gauge_of_notMem hs₁ hs₂ by rwa [one_smul]

section LinearOrderedField

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  [MulActionWithZero α Real] [IsStrictOrderedModule α Real]

/--
theorem `gauge_smul_of_nonneg` / 定理 `gauge_smul_of_nonneg`

English:
theorem gauge_smul_of_nonneg
  statement: [MulActionWithZero α E] [IsScalarTower α Real (Set E)] {s : Set E} {a : α}
  proof: by
  obtain rfl | ha' := ha.eq_or_lt
  · rw [zero_smul, gauge_zero, zero_smul]
  rw [gauge_def']; rw [gauge_def']; rw [← Real.sInf_smul_of_nonneg ha]
  congr 1
  ext r
  simp_rw [Set.mem_smul_set, Set.mem_sep_iff]
  constructor
  · rintro ⟨hr, hx⟩
    simp_rw [mem_Ioi] at hr ⊢
    rw [← mem_smul_set

中文:
定理 gauge_smul_of_nonneg
  结论: [带零乘法作用 α E] [标量塔 α 实数 (集合 E)] {s : 集合 E} {a : α}
  证明: by
  obtain rfl | ha' := ha.eq_or_lt
  · rw [zero_smul, gauge_zero, zero_smul]
  rw [gauge_def']; rw [gauge_def']; rw [← Real.sInf_smul_of_nonneg ha]
  congr 1
  ext r
  simp_rw [Set.mem_smul_set, Set.mem_sep_iff]
  constructor
  · rintro ⟨hr, hx⟩
    simp_rw [mem_Ioi] at hr ⊢
    rw [← mem_smul_set

Depends on / 依赖: Real.sInf_smul_of_nonneg, Set.mem_sep_iff, Set.mem_smul_set, eq_or_lt, gauge_def, gauge_zero, ha.eq_or_lt, hr.ne, inv_ne_z, inv_pos, mem_Ioi, mem_sep_iff, mem_smul_set, sInf_smul_of_nonneg, simp_rw, smul_assoc, smul_pos, this.ne, zero_smul
-/
theorem gauge_smul_of_nonneg [MulActionWithZero α E] [IsScalarTower α Real (Set E)] {s : Set E} {a : α}
    (ha : 0 <= a) (x : E) : gauge s (a • x) = a • gauge s x := by
  obtain rfl | ha' := ha.eq_or_lt
  · rw [zero_smul, gauge_zero, zero_smul]
  rw [gauge_def']; rw [gauge_def']; rw [← Real.sInf_smul_of_nonneg ha]
  congr 1
  ext r
  simp_rw [Set.mem_smul_set, Set.mem_sep_iff]
  constructor
  · rintro ⟨hr, hx⟩
    simp_rw [mem_Ioi] at hr ⊢
    rw [← mem_smul_set_iff_inv_smul_mem₀ hr.ne'] at hx
    have := smul_pos (inv_pos.2 ha') hr
    refine ⟨a⁻¹ • r, ⟨this, ?_⟩, smul_inv_smul₀ ha'.ne' _⟩
    rwa [← mem_smul_set_iff_inv_smul_mem₀ this.ne', smul_assoc,
      mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero ha'.ne'), inv_inv]
  · rintro ⟨r, ⟨hr, hx⟩, rfl⟩
    rw [mem_Ioi] at hr ⊢
    rw [← mem_smul_set_iff_inv_smul_mem₀ hr.ne'] at hx
    have := smul_pos ha' hr
    refine ⟨this, ?_⟩
    rw [← mem_smul_set_iff_inv_smul_mem₀ this.ne']; rw [smul_assoc]
    exact smul_mem_smul_set hx

/--
theorem `gauge_smul_left_of_nonneg` / 定理 `gauge_smul_left_of_nonneg`

English:
theorem gauge_smul_left_of_nonneg
  statement: [MulActionWithZero α E] [SMulCommClass α Real Real]
  proof: by
  obtain rfl | ha' := ha.eq_or_lt
  · rw [inv_zero, zero_smul, gauge_of_subset_zero (zero_smul_set_subset _)]
  ext x
  rw [gauge_def']; rw [Pi.smul_apply]; rw [gauge_def']; rw [← Real.sInf_smul_of_nonneg (inv_nonneg.2 ha)]
  congr 1
  ext r
  simp_rw [Set.mem_smul_set, Set.mem_sep_iff]
  constru

中文:
定理 gauge_smul_left_of_nonneg
  结论: [带零乘法作用 α E] [标量交换类 α 实数 实数]
  证明: by
  obtain rfl | ha' := ha.eq_or_lt
  · rw [inv_zero, zero_smul, gauge_of_subset_zero (zero_smul_set_subset _)]
  ext x
  rw [gauge_def']; rw [Pi.smul_apply]; rw [gauge_def']; rw [← Real.sInf_smul_of_nonneg (inv_nonneg.2 ha)]
  congr 1
  ext r
  simp_rw [Set.mem_smul_set, Set.mem_sep_iff]
  constru

Depends on / 依赖: Pi.smul_apply, Real.sInf_smul_of_nonneg, Set.mem_sep_iff, Set.mem_smul_set, eq_or_lt, gauge_def, gauge_of_subset_zero, ha.eq_or_lt, inv_nonneg, inv_zero, mem_Ioi, mem_sep_iff, mem_smul_set, sInf_smul_of_nonneg, simp_rw, smul_apply, smul_assoc, smul_pos, zero_smul, zero_smul_set_subset
-/
theorem gauge_smul_left_of_nonneg [MulActionWithZero α E] [SMulCommClass α Real Real]
    [IsScalarTower α Real Real] [IsScalarTower α Real E] {s : Set E} {a : α} (ha : 0 <= a) :
    gauge (a • s) = a⁻¹ • gauge s := by
  obtain rfl | ha' := ha.eq_or_lt
  · rw [inv_zero, zero_smul, gauge_of_subset_zero (zero_smul_set_subset _)]
  ext x
  rw [gauge_def']; rw [Pi.smul_apply]; rw [gauge_def']; rw [← Real.sInf_smul_of_nonneg (inv_nonneg.2 ha)]
  congr 1
  ext r
  simp_rw [Set.mem_smul_set, Set.mem_sep_iff]
  constructor
  · rintro ⟨hr, y, hy, h⟩
    simp_rw [mem_Ioi] at hr ⊢
    refine ⟨a • r, ⟨smul_pos ha' hr, ?_⟩, inv_smul_smul₀ ha'.ne' _⟩
    rwa [smul_inv₀, smul_assoc, ← h, inv_smul_smul₀ ha'.ne']
  · rintro ⟨r, ⟨hr, hx⟩, rfl⟩
    rw [mem_Ioi] at hr ⊢
    refine ⟨smul_pos (inv_pos.2 ha') hr, r⁻¹ • x, hx, ?_⟩
    rw [smul_inv₀]; rw [smul_assoc]; rw [inv_inv]

/--
theorem `gauge_smul_left` / 定理 `gauge_smul_left`

English:
theorem gauge_smul_left
  statement: [Module α E] [SMulCommClass α Real Real] [IsScalarTower α Real Real]
  proof: by
  rw [← gauge_smul_left_of_nonneg (abs_nonneg a)]
  obtain h | h := abs_choice a
  · rw [h]
  · rw [h, Set.neg_smul_set, ← Set.smul_set_neg]
    congr
    ext y
    refine ⟨symmetric _, fun hy => ?_⟩
    rw [← neg_neg y]
    exact symmetric _ hy

中文:
定理 gauge_smul_left
  结论: [模 α E] [标量交换类 α 实数 实数] [标量塔 α 实数 实数]
  证明: by
  rw [← gauge_smul_left_of_nonneg (abs_nonneg a)]
  obtain h | h := abs_choice a
  · rw [h]
  · rw [h, Set.neg_smul_set, ← Set.smul_set_neg]
    congr
    ext y
    refine ⟨symmetric _, fun hy => ?_⟩
    rw [← neg_neg y]
    exact symmetric _ hy

Depends on / 依赖: Set.neg_smul_set, Set.smul_set_neg, abs_choice, abs_nonneg, gauge_smul_left_of_nonneg, neg_neg, neg_smul_set, smul_set_neg, symmetric
-/
theorem gauge_smul_left [Module α E] [SMulCommClass α Real Real] [IsScalarTower α Real Real]
    [IsScalarTower α Real E] {s : Set E} (symmetric : forall x in s, -x in s) (a : α) :
    gauge (a • s) = |a|⁻¹ • gauge s := by
  rw [← gauge_smul_left_of_nonneg (abs_nonneg a)]
  obtain h | h := abs_choice a
  · rw [h]
  · rw [h, Set.neg_smul_set, ← Set.smul_set_neg]
    congr
    ext y
    refine ⟨symmetric _, fun hy => ?_⟩
    rw [← neg_neg y]
    exact symmetric _ hy

end LinearOrderedField

section RCLike

variable [RCLike 𝕜] [Module 𝕜 E] [IsScalarTower Real 𝕜 E]

/--
theorem `gauge_norm_smul` / 定理 `gauge_norm_smul`

English:
theorem gauge_norm_smul
  given: (hs : Balanced 𝕜 s) (r : 𝕜) (x : E)
  proof: by
  unfold gauge
  congr with θ
  rw [@RCLike.real_smul_eq_coe_smul 𝕜]
  refine and_congr_right fun hθ => (hs.smul _).smul_mem_iff ?_
  rw [RCLike.norm_ofReal]; rw [abs_norm]

中文:
定理 gauge_norm_smul
  条件: (hs : Balanced 𝕜 s) (r : 𝕜) (x : E)
  证明: by
  unfold gauge
  congr with θ
  rw [@RCLike.real_smul_eq_coe_smul 𝕜]
  refine and_congr_right fun hθ => (hs.smul _).smul_mem_iff ?_
  rw [RCLike.norm_ofReal]; rw [abs_norm]

Depends on / 依赖: RCLike, RCLike.norm_ofReal, RCLike.real_smul_eq_coe_smul, abs_norm, and_congr_right, hs.smul, norm_ofReal, real_smul_eq_coe_smul, smul_mem_iff
-/
theorem gauge_norm_smul (hs : Balanced 𝕜 s) (r : 𝕜) (x : E) :
    gauge s (‖r‖ • x) = gauge s (r • x) := by
  unfold gauge
  congr with θ
  rw [@RCLike.real_smul_eq_coe_smul 𝕜]
  refine and_congr_right fun hθ => (hs.smul _).smul_mem_iff ?_
  rw [RCLike.norm_ofReal]; rw [abs_norm]

/--
theorem `gauge_smul` / 定理 `gauge_smul`

English:
theorem gauge_smul
  given: (hs : Balanced 𝕜 s) (r : 𝕜) (x : E)
  statement: gauge s (r • x) = ‖r‖ * gauge s x
  proof: by
  rw [← smul_eq_mul]; rw [← gauge_smul_of_nonneg (norm_nonneg r)]; rw [gauge_norm_smul hs]

中文:
定理 gauge_smul
  条件: (hs : Balanced 𝕜 s) (r : 𝕜) (x : E)
  结论: gauge s (r • x) = ‖r‖ * gauge s x
  证明: by
  rw [← smul_eq_mul]; rw [← gauge_smul_of_nonneg (norm_nonneg r)]; rw [gauge_norm_smul hs]

Depends on / 依赖: gauge_norm_smul, gauge_smul_of_nonneg, norm_nonneg, smul_eq_mul
-/
theorem gauge_smul (hs : Balanced 𝕜 s) (r : 𝕜) (x : E) : gauge s (r • x) = ‖r‖ * gauge s x := by
  rw [← smul_eq_mul]; rw [← gauge_smul_of_nonneg (norm_nonneg r)]; rw [gauge_norm_smul hs]

end RCLike

open Filter

section TopologicalSpace

variable [TopologicalSpace E]

/--
theorem `comap_gauge_nhds_zero_le` / 定理 `comap_gauge_nhds_zero_le`

English:
theorem comap_gauge_nhds_zero_le
  given: (ha : Absorbent Real s) (hb : Bornology.IsVonNBounded Real s)
  proof: fun u hu => by
  rcases (hb hu).exists_pos with ⟨r, hr₀, hr⟩
  filter_upwards [preimage_mem_comap (gt_mem_nhds (inv_pos.2 hr₀))] with x (hx : gauge s x < r⁻¹)
  rcases exists_lt_of_gauge_lt ha hx with ⟨c, hc₀, hcr, y, hy, rfl⟩
  have hrc := (lt_inv_comm₀ hr₀ hc₀).2 hcr
  rcases hr c⁻¹ (hrc.le.trans 

中文:
定理 comap_gauge_nhds_zero_le
  条件: (ha : Absorbent 实数 s) (hb : 有界结构.IsVonNBounded 实数 s)
  证明: fun u hu => by
  rcases (hb hu).exists_pos with ⟨r, hr₀, hr⟩
  filter_upwards [preimage_mem_comap (gt_mem_nhds (inv_pos.2 hr₀))] with x (hx : gauge s x < r⁻¹)
  rcases exists_lt_of_gauge_lt ha hx with ⟨c, hc₀, hcr, y, hy, rfl⟩
  have hrc := (lt_inv_comm₀ hr₀ hc₀).2 hcr
  rcases hr c⁻¹ (hrc.le.trans 

Depends on / 依赖: exists_lt_of_gauge_lt, exists_pos, filter_upwards, gt_mem_nhds, hrc.le.trans, inv_pos, le_abs_self, preimage_mem_comap
-/
theorem comap_gauge_nhds_zero_le (ha : Absorbent Real s) (hb : Bornology.IsVonNBounded Real s) :
    comap (gauge s) (𝓝 0) <= 𝓝 0 := fun u hu => by
  rcases (hb hu).exists_pos with ⟨r, hr₀, hr⟩
  filter_upwards [preimage_mem_comap (gt_mem_nhds (inv_pos.2 hr₀))] with x (hx : gauge s x < r⁻¹)
  rcases exists_lt_of_gauge_lt ha hx with ⟨c, hc₀, hcr, y, hy, rfl⟩
  have hrc := (lt_inv_comm₀ hr₀ hc₀).2 hcr
  rcases hr c⁻¹ (hrc.le.trans (le_abs_self _)) hy with ⟨z, hz, rfl⟩
  simpa only [smul_inv_smul₀ hc₀.ne']

variable [T1Space E]

/--
theorem `gauge_eq_zero` / 定理 `gauge_eq_zero`

English:
theorem gauge_eq_zero
  given: (hs : Absorbent Real s) (hb : Bornology.IsVonNBounded Real s)
  proof: by
  refine ⟨fun h₀ => by_contra fun (hne : x != 0) => ?_, fun h => h.symm ▸ gauge_zero⟩
  have : {x}ᶜ in comap (gauge s) (𝓝 0) :=
    comap_gauge_nhds_zero_le hs hb (isOpen_compl_singleton.mem_nhds hne.symm)
  rcases ((nhds_basis_zero_abs_lt _).comap _).mem_iff.1 this with ⟨r, hr₀, hr⟩
  exact hr (

中文:
定理 gauge_eq_zero
  条件: (hs : Absorbent 实数 s) (hb : 有界结构.IsVonNBounded 实数 s)
  证明: by
  refine ⟨fun h₀ => by_contra fun (hne : x != 0) => ?_, fun h => h.symm ▸ gauge_zero⟩
  have : {x}ᶜ in comap (gauge s) (𝓝 0) :=
    comap_gauge_nhds_zero_le hs hb (isOpen_compl_singleton.mem_nhds hne.symm)
  rcases ((nhds_basis_zero_abs_lt _).comap _).mem_iff.1 this with ⟨r, hr₀, hr⟩
  exact hr (

Depends on / 依赖: comap_gauge_nhds_zero_le, gauge_zero, h.symm, hne.symm, isOpen_compl_singleton, isOpen_compl_singleton.mem_nhds, mem_iff, mem_nhds, nhds_basis_zero_abs_lt
-/
theorem gauge_eq_zero (hs : Absorbent Real s) (hb : Bornology.IsVonNBounded Real s) :
    gauge s x = 0 ↔ x = 0 := by
  refine ⟨fun h₀ => by_contra fun (hne : x != 0) => ?_, fun h => h.symm ▸ gauge_zero⟩
  have : {x}ᶜ in comap (gauge s) (𝓝 0) :=
    comap_gauge_nhds_zero_le hs hb (isOpen_compl_singleton.mem_nhds hne.symm)
  rcases ((nhds_basis_zero_abs_lt _).comap _).mem_iff.1 this with ⟨r, hr₀, hr⟩
  exact hr (by simpa [h₀]) rfl

/--
theorem `gauge_pos` / 定理 `gauge_pos`

English:
theorem gauge_pos
  given: (hs : Absorbent Real s) (hb : Bornology.IsVonNBounded Real s)
  proof: by
  simp only [(gauge_nonneg _).lt_iff_ne', Ne, gauge_eq_zero hs hb]

中文:
定理 gauge_pos
  条件: (hs : Absorbent 实数 s) (hb : 有界结构.IsVonNBounded 实数 s)
  证明: by
  simp only [(gauge_nonneg _).lt_iff_ne', Ne, gauge_eq_zero hs hb]

Depends on / 依赖: gauge_eq_zero, gauge_nonneg, lt_iff_ne
-/
theorem gauge_pos (hs : Absorbent Real s) (hb : Bornology.IsVonNBounded Real s) :
    0 < gauge s x ↔ x != 0 := by
  simp only [(gauge_nonneg _).lt_iff_ne', Ne, gauge_eq_zero hs hb]

end TopologicalSpace

section ContinuousSMul

variable [TopologicalSpace E] [ContinuousSMul Real E]

open Filter in
/--
theorem `interior_subset_gauge_lt_one` / 定理 `interior_subset_gauge_lt_one`

English:
theorem interior_subset_gauge_lt_one
  given: (s : Set E)
  statement: interior s subseteq { x | gauge s x < 1 }
  proof: by
  intro x hx
  have H₁ : Tendsto (fun r : Real => r⁻¹ • x) (𝓝[<] 1) (𝓝 ((1 : Real)⁻¹ • x)) :=
    ((tendsto_id.inv₀ one_ne_zero).smul tendsto_const_nhds).mono_left inf_le_left
  rw [inv_one]; rw [one_smul] at H₁
  have H₂ : forallᶠ r in 𝓝[<] (1 : Real), x in r • s ∧ 0 < r ∧ r < 1 := by
    filter

中文:
定理 interior_subset_gauge_lt_one
  条件: (s : 集合 E)
  结论: interior s subseteq { x | gauge s x < 1 }
  证明: by
  intro x hx
  have H₁ : Tendsto (fun r : Real => r⁻¹ • x) (𝓝[<] 1) (𝓝 ((1 : Real)⁻¹ • x)) :=
    ((tendsto_id.inv₀ one_ne_zero).smul tendsto_const_nhds).mono_left inf_le_left
  rw [inv_one]; rw [one_smul] at H₁
  have H₂ : forallᶠ r in 𝓝[<] (1 : Real), x in r • s ∧ 0 < r ∧ r < 1 := by
    filter

Depends on / 依赖: Ioo_mem_nhdsLT, Tendsto, filter_upwards, gauge_le_of_mem, inf_le_left, inv_one, mem_interior_iff_mem_nhds, mono_left, one_ne_zero, one_pos, one_smul, tendsto_const_nhds, tendsto_id, tendsto_id.inv
-/
theorem interior_subset_gauge_lt_one (s : Set E) : interior s subseteq { x | gauge s x < 1 } := by
  intro x hx
  have H₁ : Tendsto (fun r : Real => r⁻¹ • x) (𝓝[<] 1) (𝓝 ((1 : Real)⁻¹ • x)) :=
    ((tendsto_id.inv₀ one_ne_zero).smul tendsto_const_nhds).mono_left inf_le_left
  rw [inv_one]; rw [one_smul] at H₁
  have H₂ : forallᶠ r in 𝓝[<] (1 : Real), x in r • s ∧ 0 < r ∧ r < 1 := by
    filter_upwards [H₁ (mem_interior_iff_mem_nhds.1 hx), Ioo_mem_nhdsLT one_pos] with r h₁ h₂
    exact ⟨(mem_smul_set_iff_inv_smul_mem₀ h₂.1.ne' _ _).2 h₁, h₂⟩
  rcases H₂.exists with ⟨r, hxr, hr₀, hr₁⟩
  exact (gauge_le_of_mem hr₀.le hxr).trans_lt hr₁

/--
theorem `setOfPred_gauge_lt_one_eq_self_of_isOpen` / 定理 `setOfPred_gauge_lt_one_eq_self_of_isOpen`

English:
theorem setOfPred_gauge_lt_one_eq_self_of_isOpen
  statement: (hs₁ : Convex Real s) (hs₀ : (0 : E) in s)
  proof: by
  refine (setOfPred_gauge_lt_one_subset_self hs₁ ‹_› <| absorbent_nhds_zero <|
    hs₂.mem_nhds hs₀).antisymm ?_
  convert! interior_subset_gauge_lt_one s
  exact hs₂.interior_eq.symm

@[deprecated (since := "2026-07-09")]
alias setOf_gauge_lt_one_eq_self_of_isOpen := setOfPred_gauge_lt_one_eq_se

中文:
定理 setOfPred_gauge_lt_one_eq_self_of_isOpen
  结论: (hs₁ : 凸 实数 s) (hs₀ : (0 : E) in s)
  证明: by
  refine (setOfPred_gauge_lt_one_subset_self hs₁ ‹_› <| absorbent_nhds_zero <|
    hs₂.mem_nhds hs₀).antisymm ?_
  convert! interior_subset_gauge_lt_one s
  exact hs₂.interior_eq.symm

@[deprecated (since := "2026-07-09")]
alias setOf_gauge_lt_one_eq_self_of_isOpen := setOfPred_gauge_lt_one_eq_se

Depends on / 依赖: absorbent_nhds_zero, antisymm, convert, interior_eq, interior_eq.symm, interior_subset_gauge_lt_one, mem_nhds, setOfPred_gauge_lt_one_subset_self
-/
theorem setOfPred_gauge_lt_one_eq_self_of_isOpen (hs₁ : Convex Real s) (hs₀ : (0 : E) in s)
    (hs₂ : IsOpen s) : { x | gauge s x < 1 } = s := by
  refine (setOfPred_gauge_lt_one_subset_self hs₁ ‹_› <| absorbent_nhds_zero <|
    hs₂.mem_nhds hs₀).antisymm ?_
  convert! interior_subset_gauge_lt_one s
  exact hs₂.interior_eq.symm

@[deprecated (since := "2026-07-09")]
alias setOf_gauge_lt_one_eq_self_of_isOpen := setOfPred_gauge_lt_one_eq_self_of_isOpen

@[deprecated (since := "2026-06-17")]
alias gauge_lt_one_eq_self_of_isOpen := setOfPred_gauge_lt_one_eq_self_of_isOpen

/--
theorem `gauge_lt_one_of_mem_of_isOpen` / 定理 `gauge_lt_one_of_mem_of_isOpen`

English:
theorem gauge_lt_one_of_mem_of_isOpen
  given: (hs₂ : IsOpen s) {x : E} (hx : x in s)
  proof: interior_subset_gauge_lt_one s by rwa [hs₂.interior_eq]

中文:
定理 gauge_lt_one_of_mem_of_isOpen
  条件: (hs₂ : 是开集 s) {x : E} (hx : x in s)
  证明: interior_subset_gauge_lt_one s by rwa [hs₂.interior_eq]

Depends on / 依赖: interior_eq, interior_subset_gauge_lt_one
-/
theorem gauge_lt_one_of_mem_of_isOpen (hs₂ : IsOpen s) {x : E} (hx : x in s) :
    gauge s x < 1 :=
interior_subset_gauge_lt_one s by rwa [hs₂.interior_eq]

/--
theorem `gauge_lt_of_mem_smul` / 定理 `gauge_lt_of_mem_smul`

English:
theorem gauge_lt_of_mem_smul
  given: (x : E) (ε : Real) (hε : 0 < ε) (hs₂ : IsOpen s) (hx : x in ε • s)
  proof: by
  have : ε⁻¹ • x in s := by rwa [← mem_smul_set_iff_inv_smul_mem₀ hε.ne']
  have h_gauge_lt := gauge_lt_one_of_mem_of_isOpen hs₂ this
  rwa [gauge_smul_of_nonneg (inv_nonneg.2 hε.le), smul_eq_mul, inv_mul_lt_iff₀ hε, mul_one]
    at h_gauge_lt

中文:
定理 gauge_lt_of_mem_smul
  条件: (x : E) (ε : 实数) (hε : 0 < ε) (hs₂ : 是开集 s) (hx : x in ε • s)
  证明: by
  have : ε⁻¹ • x in s := by rwa [← mem_smul_set_iff_inv_smul_mem₀ hε.ne']
  have h_gauge_lt := gauge_lt_one_of_mem_of_isOpen hs₂ this
  rwa [gauge_smul_of_nonneg (inv_nonneg.2 hε.le), smul_eq_mul, inv_mul_lt_iff₀ hε, mul_one]
    at h_gauge_lt

Depends on / 依赖: gauge_lt_one_of_mem_of_isOpen, gauge_smul_of_nonneg, h_gauge_lt, inv_nonneg, mul_one, smul_eq_mul
-/
theorem gauge_lt_of_mem_smul (x : E) (ε : Real) (hε : 0 < ε) (hs₂ : IsOpen s) (hx : x in ε • s) :
    gauge s x < ε := by
  have : ε⁻¹ • x in s := by rwa [← mem_smul_set_iff_inv_smul_mem₀ hε.ne']
  have h_gauge_lt := gauge_lt_one_of_mem_of_isOpen hs₂ this
  rwa [gauge_smul_of_nonneg (inv_nonneg.2 hε.le), smul_eq_mul, inv_mul_lt_iff₀ hε, mul_one]
    at h_gauge_lt

/--
theorem `mem_closure_of_gauge_le_one` / 定理 `mem_closure_of_gauge_le_one`

English:
theorem mem_closure_of_gauge_le_one
  statement: (hc : Convex Real s) (hs₀ : 0 in s) (ha : Absorbent Real s)
  proof: by
  have : forallᶠ r : Real in 𝓝[<] 1, r • x in s := by
    filter_upwards [Ico_mem_nhdsLT one_pos] with r ⟨hr₀, hr₁⟩
    apply setOfPred_gauge_lt_one_subset_self hc hs₀ ha
    rw [mem_ofPred_eq]; rw [gauge_smul_of_nonneg hr₀]
    exact mul_lt_one_of_nonneg_of_lt_one_left hr₀ hr₁ h
  refine mem_clo

中文:
定理 mem_closure_of_gauge_le_one
  结论: (hc : 凸 实数 s) (hs₀ : 0 in s) (ha : Absorbent 实数 s)
  证明: by
  have : forallᶠ r : Real in 𝓝[<] 1, r • x in s := by
    filter_upwards [Ico_mem_nhdsLT one_pos] with r ⟨hr₀, hr₁⟩
    apply setOfPred_gauge_lt_one_subset_self hc hs₀ ha
    rw [mem_ofPred_eq]; rw [gauge_smul_of_nonneg hr₀]
    exact mul_lt_one_of_nonneg_of_lt_one_left hr₀ hr₁ h
  refine mem_clo

Depends on / 依赖: Continuous, Continuous.tendsto, Filter, Filter.Tendsto.mono_left, Ico_mem_nhdsLT, Tendsto, filter_upwards, fun_prop, gauge_smul_of_nonneg, inf_le_left, mem_closure_of_tendsto, mem_ofPred_eq, mono_left, mul_lt_one_of_nonneg_of_lt_one_left, one_pos, one_smul, setOfPred_gauge_lt_one_subset_self, tendsto
-/
theorem mem_closure_of_gauge_le_one (hc : Convex Real s) (hs₀ : 0 in s) (ha : Absorbent Real s)
    (h : gauge s x <= 1) : x in closure s := by
  have : forallᶠ r : Real in 𝓝[<] 1, r • x in s := by
    filter_upwards [Ico_mem_nhdsLT one_pos] with r ⟨hr₀, hr₁⟩
    apply setOfPred_gauge_lt_one_subset_self hc hs₀ ha
    rw [mem_ofPred_eq]; rw [gauge_smul_of_nonneg hr₀]
    exact mul_lt_one_of_nonneg_of_lt_one_left hr₀ hr₁ h
  refine mem_closure_of_tendsto ?_ this
  exact Filter.Tendsto.mono_left (Continuous.tendsto' (by fun_prop) _ _ (one_smul _ _))
    inf_le_left

/--
theorem `mem_frontier_of_gauge_eq_one` / 定理 `mem_frontier_of_gauge_eq_one`

English:
theorem mem_frontier_of_gauge_eq_one
  statement: (hc : Convex Real s) (hs₀ : 0 in s) (ha : Absorbent Real s)
  proof: ⟨mem_closure_of_gauge_le_one hc hs₀ ha h.le, fun h' =>
    (interior_subset_gauge_lt_one s h').out.ne h⟩

中文:
定理 mem_frontier_of_gauge_eq_one
  结论: (hc : 凸 实数 s) (hs₀ : 0 in s) (ha : Absorbent 实数 s)
  证明: ⟨mem_closure_of_gauge_le_one hc hs₀ ha h.le, fun h' =>
    (interior_subset_gauge_lt_one s h').out.ne h⟩

Depends on / 依赖: h.le, interior_subset_gauge_lt_one, mem_closure_of_gauge_le_one, out.ne
-/
theorem mem_frontier_of_gauge_eq_one (hc : Convex Real s) (hs₀ : 0 in s) (ha : Absorbent Real s)
    (h : gauge s x = 1) : x in frontier s :=
  ⟨mem_closure_of_gauge_le_one hc hs₀ ha h.le, fun h' =>
    (interior_subset_gauge_lt_one s h').out.ne h⟩

/--
theorem `tendsto_gauge_nhds_zero_nhdsGE` / 定理 `tendsto_gauge_nhds_zero_nhdsGE`

English:
theorem tendsto_gauge_nhds_zero_nhdsGE
  given: (hs : s in 𝓝 0)
  statement: Tendsto (gauge s) (𝓝 0) (𝓝[>=] 0)
  proof: by
  refine nhdsGE_basis_Icc.tendsto_right_iff.2 fun ε hε => ?_
  rw [← set_smul_mem_nhds_zero_iff hε.ne'] at hs
  filter_upwards [hs] with x hx
  exact ⟨gauge_nonneg _, gauge_le_of_mem hε.le hx⟩

中文:
定理 tendsto_gauge_nhds_zero_nhdsGE
  条件: (hs : s in 𝓝 0)
  结论: 收敛 (gauge s) (𝓝 0) (𝓝[>=] 0)
  证明: by
  refine nhdsGE_basis_Icc.tendsto_right_iff.2 fun ε hε => ?_
  rw [← set_smul_mem_nhds_zero_iff hε.ne'] at hs
  filter_upwards [hs] with x hx
  exact ⟨gauge_nonneg _, gauge_le_of_mem hε.le hx⟩

Depends on / 依赖: filter_upwards, gauge_le_of_mem, gauge_nonneg, nhdsGE_basis_Icc, nhdsGE_basis_Icc.tendsto_right_iff, set_smul_mem_nhds_zero_iff, tendsto_right_iff
-/
theorem tendsto_gauge_nhds_zero_nhdsGE (hs : s in 𝓝 0) : Tendsto (gauge s) (𝓝 0) (𝓝[>=] 0) := by
  refine nhdsGE_basis_Icc.tendsto_right_iff.2 fun ε hε => ?_
  rw [← set_smul_mem_nhds_zero_iff hε.ne'] at hs
  filter_upwards [hs] with x hx
  exact ⟨gauge_nonneg _, gauge_le_of_mem hε.le hx⟩

/--
theorem `tendsto_gauge_nhds_zero` / 定理 `tendsto_gauge_nhds_zero`

English:
theorem tendsto_gauge_nhds_zero
  given: (hs : s in 𝓝 0)
  statement: Tendsto (gauge s) (𝓝 0) (𝓝 0)
  proof: (tendsto_gauge_nhds_zero_nhdsGE hs).mono_right inf_le_left

中文:
定理 tendsto_gauge_nhds_zero
  条件: (hs : s in 𝓝 0)
  结论: 收敛 (gauge s) (𝓝 0) (𝓝 0)
  证明: (tendsto_gauge_nhds_zero_nhdsGE hs).mono_right inf_le_left

Depends on / 依赖: inf_le_left, mono_right, tendsto_gauge_nhds_zero_nhdsGE
-/
theorem tendsto_gauge_nhds_zero (hs : s in 𝓝 0) : Tendsto (gauge s) (𝓝 0) (𝓝 0) :=
  (tendsto_gauge_nhds_zero_nhdsGE hs).mono_right inf_le_left

/--
theorem `continuousAt_gauge_zero` / 定理 `continuousAt_gauge_zero`

English:
theorem continuousAt_gauge_zero
  given: (hs : s in 𝓝 0)
  statement: ContinuousAt (gauge s) 0
  proof: by
  rw [ContinuousAt]; rw [gauge_zero]
  exact tendsto_gauge_nhds_zero hs

中文:
定理 continuousAt_gauge_zero
  条件: (hs : s in 𝓝 0)
  结论: ContinuousAt (gauge s) 0
  证明: by
  rw [ContinuousAt]; rw [gauge_zero]
  exact tendsto_gauge_nhds_zero hs

Depends on / 依赖: ContinuousAt, gauge_zero, tendsto_gauge_nhds_zero
-/
theorem continuousAt_gauge_zero (hs : s in 𝓝 0) : ContinuousAt (gauge s) 0 := by
  rw [ContinuousAt]; rw [gauge_zero]
  exact tendsto_gauge_nhds_zero hs

/--
theorem `comap_gauge_nhds_zero` / 定理 `comap_gauge_nhds_zero`

English:
theorem comap_gauge_nhds_zero
  given: (hb : Bornology.IsVonNBounded Real s) (h₀ : s in 𝓝 0)
  proof: (comap_gauge_nhds_zero_le (absorbent_nhds_zero h₀) hb).antisymm
    (tendsto_gauge_nhds_zero h₀).le_comap

中文:
定理 comap_gauge_nhds_zero
  条件: (hb : 有界结构.IsVonNBounded 实数 s) (h₀ : s in 𝓝 0)
  证明: (comap_gauge_nhds_zero_le (absorbent_nhds_zero h₀) hb).antisymm
    (tendsto_gauge_nhds_zero h₀).le_comap

Depends on / 依赖: absorbent_nhds_zero, antisymm, comap_gauge_nhds_zero_le, le_comap, tendsto_gauge_nhds_zero
-/
theorem comap_gauge_nhds_zero (hb : Bornology.IsVonNBounded Real s) (h₀ : s in 𝓝 0) :
    comap (gauge s) (𝓝 0) = 𝓝 0 :=
  (comap_gauge_nhds_zero_le (absorbent_nhds_zero h₀) hb).antisymm
    (tendsto_gauge_nhds_zero h₀).le_comap

end ContinuousSMul

section TopologicalVectorSpace

open Filter

variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul Real E]

/--
theorem `continuousAt_gauge` / 定理 `continuousAt_gauge`

English:
theorem continuousAt_gauge
  given: (hc : Convex Real s) (hs₀ : s in 𝓝 0)
  statement: ContinuousAt (gauge s) x
  proof: by
  have ha : Absorbent Real s := absorbent_nhds_zero hs₀
  refine (nhds_basis_Icc_pos _).tendsto_right_iff.2 fun ε hε₀ => ?_
  rw [← map_add_left_nhds_zero]; rw [eventually_map]
  have : ε • s inter -(ε • s) in 𝓝 0 :=
    inter_mem ((set_smul_mem_nhds_zero_iff hε₀.ne').2 hs₀)
      (neg_mem_nhds_z

中文:
定理 continuousAt_gauge
  条件: (hc : 凸 实数 s) (hs₀ : s in 𝓝 0)
  结论: ContinuousAt (gauge s) x
  证明: by
  have ha : Absorbent Real s := absorbent_nhds_zero hs₀
  refine (nhds_basis_Icc_pos _).tendsto_right_iff.2 fun ε hε₀ => ?_
  rw [← map_add_left_nhds_zero]; rw [eventually_map]
  have : ε • s inter -(ε • s) in 𝓝 0 :=
    inter_mem ((set_smul_mem_nhds_zero_iff hε₀.ne').2 hs₀)
      (neg_mem_nhds_z

Depends on / 依赖: Absorbent, absorbent_nhds_zero, eventually_map, filter_upwards, gauge_a, inter_mem, map_add_left_nhds_zero, neg_mem_nhds_zero, nhds_basis_Icc_pos, set_smul_mem_nhds_zero_iff, sub_le_iff_le_add, tendsto_right_iff
-/
theorem continuousAt_gauge (hc : Convex Real s) (hs₀ : s in 𝓝 0) : ContinuousAt (gauge s) x := by
  have ha : Absorbent Real s := absorbent_nhds_zero hs₀
  refine (nhds_basis_Icc_pos _).tendsto_right_iff.2 fun ε hε₀ => ?_
  rw [← map_add_left_nhds_zero]; rw [eventually_map]
  have : ε • s inter -(ε • s) in 𝓝 0 :=
    inter_mem ((set_smul_mem_nhds_zero_iff hε₀.ne').2 hs₀)
      (neg_mem_nhds_zero _ ((set_smul_mem_nhds_zero_iff hε₀.ne').2 hs₀))
  filter_upwards [this] with y hy
  constructor
  · rw [sub_le_iff_le_add]
    calc
      gauge s x = gauge s (x + y + (-y)) := by simp
      _ <= gauge s (x + y) + gauge s (-y) := gauge_add_le hc ha _ _
      _ <= gauge s (x + y) + ε := by grw [gauge_le_of_mem hε₀.le (mem_neg.1 hy.2)]
  · calc
      gauge s (x + y) <= gauge s x + gauge s y := gauge_add_le hc ha _ _
      _ <= gauge s x + ε := by grw [gauge_le_of_mem hε₀.le hy.1]

/-- If `s` is a convex neighborhood of the origin in a topological real vector space, then `gauge s`
is continuous. If the ambient space is a normed space, then `gauge s` is Lipschitz continuous, see
`Convex.lipschitz_gauge`. -/
@[continuity, fun_prop]
/--
theorem `continuous_gauge` / 定理 `continuous_gauge`

English:
theorem continuous_gauge
  given: (hc : Convex Real s) (hs₀ : s in 𝓝 0)
  statement: Continuous (gauge s)
  proof: continuous_iff_continuousAt.2 fun _ => continuousAt_gauge hc hs₀

中文:
定理 continuous_gauge
  条件: (hc : 凸 实数 s) (hs₀ : s in 𝓝 0)
  结论: 连续 (gauge s)
  证明: continuous_iff_continuousAt.2 fun _ => continuousAt_gauge hc hs₀

Depends on / 依赖: continuousAt_gauge, continuous_iff_continuousAt
-/
theorem continuous_gauge (hc : Convex Real s) (hs₀ : s in 𝓝 0) : Continuous (gauge s) :=
  continuous_iff_continuousAt.2 fun _ => continuousAt_gauge hc hs₀

/--
theorem `setOfPred_gauge_lt_one_eq_interior` / 定理 `setOfPred_gauge_lt_one_eq_interior`

English:
theorem setOfPred_gauge_lt_one_eq_interior
  given: (hc : Convex Real s) (hs₀ : s in 𝓝 0)
  proof: by
  refine Subset.antisymm (fun x hx => ?_) (interior_subset_gauge_lt_one s)
  rcases mem_openSegment_of_gauge_lt_one (absorbent_nhds_zero hs₀) hx with ⟨y, hys, hxy⟩
  exact hc.openSegment_interior_self_subset_interior (mem_interior_iff_mem_nhds.2 hs₀) hys hxy

@[deprecated (since := "2026-07-09")]

中文:
定理 setOfPred_gauge_lt_one_eq_interior
  条件: (hc : 凸 实数 s) (hs₀ : s in 𝓝 0)
  证明: by
  refine Subset.antisymm (fun x hx => ?_) (interior_subset_gauge_lt_one s)
  rcases mem_openSegment_of_gauge_lt_one (absorbent_nhds_zero hs₀) hx with ⟨y, hys, hxy⟩
  exact hc.openSegment_interior_self_subset_interior (mem_interior_iff_mem_nhds.2 hs₀) hys hxy

@[deprecated (since := "2026-07-09")]

Depends on / 依赖: Subset, Subset.antisymm, absorbent_nhds_zero, antisymm, hc.openSegment_interior_self_subset_interior, interior_subset_gauge_lt_one, mem_interior_iff_mem_nhds, mem_openSegment_of_gauge_lt_one, openSegment_interior_self_subset_interior
-/
theorem setOfPred_gauge_lt_one_eq_interior (hc : Convex Real s) (hs₀ : s in 𝓝 0) :
    { x | gauge s x < 1 } = interior s := by
  refine Subset.antisymm (fun x hx => ?_) (interior_subset_gauge_lt_one s)
  rcases mem_openSegment_of_gauge_lt_one (absorbent_nhds_zero hs₀) hx with ⟨y, hys, hxy⟩
  exact hc.openSegment_interior_self_subset_interior (mem_interior_iff_mem_nhds.2 hs₀) hys hxy

@[deprecated (since := "2026-07-09")]
alias setOf_gauge_lt_one_eq_interior := setOfPred_gauge_lt_one_eq_interior

@[deprecated (since := "2026-06-17")]
alias gauge_lt_one_eq_interior := setOfPred_gauge_lt_one_eq_interior

/--
theorem `gauge_lt_one_iff_mem_interior` / 定理 `gauge_lt_one_iff_mem_interior`

English:
theorem gauge_lt_one_iff_mem_interior
  given: (hc : Convex Real s) (hs₀ : s in 𝓝 0)
  proof: Set.ext_iff.1 (setOfPred_gauge_lt_one_eq_interior hc hs₀) _

中文:
定理 gauge_lt_one_iff_mem_interior
  条件: (hc : 凸 实数 s) (hs₀ : s in 𝓝 0)
  证明: Set.ext_iff.1 (setOfPred_gauge_lt_one_eq_interior hc hs₀) _

Depends on / 依赖: Set.ext_iff, ext_iff, setOfPred_gauge_lt_one_eq_interior
-/
theorem gauge_lt_one_iff_mem_interior (hc : Convex Real s) (hs₀ : s in 𝓝 0) :
    gauge s x < 1 ↔ x in interior s :=
  Set.ext_iff.1 (setOfPred_gauge_lt_one_eq_interior hc hs₀) _

/--
theorem `gauge_le_one_iff_mem_closure` / 定理 `gauge_le_one_iff_mem_closure`

English:
theorem gauge_le_one_iff_mem_closure
  given: (hc : Convex Real s) (hs₀ : s in 𝓝 0)
  proof: ⟨mem_closure_of_gauge_le_one hc (mem_of_mem_nhds hs₀) (absorbent_nhds_zero hs₀), fun h =>
    le_on_closure (fun _ => gauge_le_one_of_mem) (continuous_gauge hc hs₀).continuousOn
      continuousOn_const h⟩

中文:
定理 gauge_le_one_iff_mem_closure
  条件: (hc : 凸 实数 s) (hs₀ : s in 𝓝 0)
  证明: ⟨mem_closure_of_gauge_le_one hc (mem_of_mem_nhds hs₀) (absorbent_nhds_zero hs₀), fun h =>
    le_on_closure (fun _ => gauge_le_one_of_mem) (continuous_gauge hc hs₀).continuousOn
      continuousOn_const h⟩

Depends on / 依赖: absorbent_nhds_zero, continuousOn, continuousOn_const, continuous_gauge, gauge_le_one_of_mem, le_on_closure, mem_closure_of_gauge_le_one, mem_of_mem_nhds
-/
theorem gauge_le_one_iff_mem_closure (hc : Convex Real s) (hs₀ : s in 𝓝 0) :
    gauge s x <= 1 ↔ x in closure s :=
  ⟨mem_closure_of_gauge_le_one hc (mem_of_mem_nhds hs₀) (absorbent_nhds_zero hs₀), fun h =>
    le_on_closure (fun _ => gauge_le_one_of_mem) (continuous_gauge hc hs₀).continuousOn
      continuousOn_const h⟩

/--
theorem `gauge_eq_one_iff_mem_frontier` / 定理 `gauge_eq_one_iff_mem_frontier`

English:
theorem gauge_eq_one_iff_mem_frontier
  given: (hc : Convex Real s) (hs₀ : s in 𝓝 0)
  proof: by
  rw [eq_iff_le_not_lt]; rw [gauge_le_one_iff_mem_closure hc hs₀]; rw [gauge_lt_one_iff_mem_interior hc hs₀]
  rfl

中文:
定理 gauge_eq_one_iff_mem_frontier
  条件: (hc : 凸 实数 s) (hs₀ : s in 𝓝 0)
  证明: by
  rw [eq_iff_le_not_lt]; rw [gauge_le_one_iff_mem_closure hc hs₀]; rw [gauge_lt_one_iff_mem_interior hc hs₀]
  rfl

Depends on / 依赖: eq_iff_le_not_lt, gauge_le_one_iff_mem_closure, gauge_lt_one_iff_mem_interior
-/
theorem gauge_eq_one_iff_mem_frontier (hc : Convex Real s) (hs₀ : s in 𝓝 0) :
    gauge s x = 1 ↔ x in frontier s := by
  rw [eq_iff_le_not_lt]; rw [gauge_le_one_iff_mem_closure hc hs₀]; rw [gauge_lt_one_iff_mem_interior hc hs₀]
  rfl

end TopologicalVectorSpace

section RCLike

variable [RCLike 𝕜] [Module 𝕜 E] [IsScalarTower Real 𝕜 E]

/-- `gauge s` as a seminorm when `s` is balanced, convex and absorbent. -/
@[simps!]
/--
Definition of `gaugeSeminorm` / `gaugeSeminorm` 的定义

English:
definition gaugeSeminorm
  signature: (hs₀ : Balanced 𝕜 s) (hs₁ : Convex Real s) (hs₂ : Absorbent Real s)
  body: Seminorm.of (gauge s) (gauge_add_le hs₁ hs₂) (gauge_smul hs₀)

中文:
定义 gaugeSeminorm
  签名: (hs₀ : Balanced 𝕜 s) (hs₁ : 凸 实数 s) (hs₂ : Absorbent 实数 s)
  定义体: Seminorm.of (gauge s) (gauge_add_le hs₁ hs₂) (gauge_smul hs₀)

Depends on / 依赖: Seminorm, Seminorm.of, gauge_add_le, gauge_smul
-/
def gaugeSeminorm (hs₀ : Balanced 𝕜 s) (hs₁ : Convex Real s) (hs₂ : Absorbent Real s) : Seminorm 𝕜 E :=
  Seminorm.of (gauge s) (gauge_add_le hs₁ hs₂) (gauge_smul hs₀)

variable {hs₀ : Balanced 𝕜 s} {hs₁ : Convex Real s} {hs₂ : Absorbent Real s} [TopologicalSpace E]
  [ContinuousSMul Real E]

/--
theorem `gaugeSeminorm_lt_one_of_isOpen` / 定理 `gaugeSeminorm_lt_one_of_isOpen`

English:
theorem gaugeSeminorm_lt_one_of_isOpen
  given: (hs : IsOpen s) {x : E} (hx : x in s)
  proof: gauge_lt_one_of_mem_of_isOpen hs hx

中文:
定理 gaugeSeminorm_lt_one_of_isOpen
  条件: (hs : 是开集 s) {x : E} (hx : x in s)
  证明: gauge_lt_one_of_mem_of_isOpen hs hx

Depends on / 依赖: gauge_lt_one_of_mem_of_isOpen
-/
theorem gaugeSeminorm_lt_one_of_isOpen (hs : IsOpen s) {x : E} (hx : x in s) :
    gaugeSeminorm hs₀ hs₁ hs₂ x < 1 :=
  gauge_lt_one_of_mem_of_isOpen hs hx

/--
theorem `gaugeSeminorm_ball_one` / 定理 `gaugeSeminorm_ball_one`

English:
theorem gaugeSeminorm_ball_one
  given: (hs : IsOpen s)
  statement: (gaugeSeminorm hs₀ hs₁ hs₂).ball 0 1 = s
  proof: by
  rw [Seminorm.ball_zero_eq]
  exact setOfPred_gauge_lt_one_eq_self_of_isOpen hs₁ hs₂.zero_mem hs

中文:
定理 gaugeSeminorm_ball_one
  条件: (hs : 是开集 s)
  结论: (gaugeSeminorm hs₀ hs₁ hs₂).ball 0 1 = s
  证明: by
  rw [Seminorm.ball_zero_eq]
  exact setOfPred_gauge_lt_one_eq_self_of_isOpen hs₁ hs₂.zero_mem hs

Depends on / 依赖: Seminorm, Seminorm.ball_zero_eq, ball_zero_eq, setOfPred_gauge_lt_one_eq_self_of_isOpen, zero_mem
-/
theorem gaugeSeminorm_ball_one (hs : IsOpen s) : (gaugeSeminorm hs₀ hs₁ hs₂).ball 0 1 = s := by
  rw [Seminorm.ball_zero_eq]
  exact setOfPred_gauge_lt_one_eq_self_of_isOpen hs₁ hs₂.zero_mem hs

end RCLike

/-- Any seminorm arises as the gauge of its unit ball. -/
@[simp]
/--
theorem `Seminorm.gauge_ball` / 定理 `Seminorm.gauge_ball`

English:
theorem Seminorm.gauge_ball
  given: (p : Seminorm Real E)
  statement: gauge (p.ball 0 1) = p
  proof: by
  ext x
  obtain hp | hp := { r : Real | 0 < r ∧ x in r • p.ball 0 1 }.eq_empty_or_nonempty
  · rw [gauge, hp, Real.sInf_empty]
    by_contra h
    have hpx : 0 < p x := (apply_nonneg _ _).lt_of_ne h
    have hpx₂ : 0 < 2 * p x := mul_pos zero_lt_two hpx
    refine hp.subset ⟨hpx₂, (2 * p x)⁻¹ • 

中文:
定理 半范数.gauge_ball
  条件: (p : 半范数 实数 E)
  结论: gauge (p.ball 0 1) = p
  证明: by
  ext x
  obtain hp | hp := { r : Real | 0 < r ∧ x in r • p.ball 0 1 }.eq_empty_or_nonempty
  · rw [gauge, hp, Real.sInf_empty]
    by_contra h
    have hpx : 0 < p x := (apply_nonneg _ _).lt_of_ne h
    have hpx₂ : 0 < 2 * p x := mul_pos zero_lt_two hpx
    refine hp.subset ⟨hpx₂, (2 * p x)⁻¹ • 
-/
protected theorem Seminorm.gauge_ball (p : Seminorm Real E) : gauge (p.ball 0 1) = p := by
  ext x
  obtain hp | hp := { r : Real | 0 < r ∧ x in r • p.ball 0 1 }.eq_empty_or_nonempty
  · rw [gauge, hp, Real.sInf_empty]
    by_contra h
    have hpx : 0 < p x := (apply_nonneg _ _).lt_of_ne h
    have hpx₂ : 0 < 2 * p x := mul_pos zero_lt_two hpx
    refine hp.subset ⟨hpx₂, (2 * p x)⁻¹ • x, ?_, smul_inv_smul₀ hpx₂.ne' _⟩
    rw [p.mem_ball_zero]; rw [map_smul_eq_mul]; rw [Real.norm_eq_abs]; rw [abs_of_pos (inv_pos.2 hpx₂)]; rw [inv_mul_lt_iff₀ hpx₂]; rw [mul_one]
    exact lt_mul_of_one_lt_left hpx one_lt_two
  refine IsGLB.csInf_eq ⟨fun r => ?_, fun r hr => le_of_forall_pos_le_add fun ε hε => ?_⟩ hp
  · rintro ⟨hr, y, hy, rfl⟩
    rw [p.mem_ball_zero] at hy
    rw [map_smul_eq_mul]; rw [Real.norm_eq_abs]; rw [abs_of_pos hr]
    exact mul_le_of_le_one_right hr.le hy.le
  · have hpε : 0 < p x + ε := by positivity
    refine hr ⟨hpε, (p x + ε)⁻¹ • x, ?_, smul_inv_smul₀ hpε.ne' _⟩
    rw [p.mem_ball_zero]; rw [map_smul_eq_mul]; rw [Real.norm_eq_abs]; rw [abs_of_pos (inv_pos.2 hpε)]; rw [inv_mul_lt_iff₀ hpε]; rw [mul_one]
    exact lt_add_of_pos_right _ hε

/--
theorem `Seminorm.gaugeSeminorm_ball` / 定理 `Seminorm.gaugeSeminorm_ball`

English:
theorem Seminorm.gaugeSeminorm_ball
  given: (p : Seminorm Real E)
  proof: DFunLike.coe_injective p.gauge_ball

中文:
定理 半范数.gaugeSeminorm_ball
  条件: (p : 半范数 实数 E)
  证明: DFunLike.coe_injective p.gauge_ball

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective, gauge_ball, p.gauge_ball
-/
theorem Seminorm.gaugeSeminorm_ball (p : Seminorm Real E) :
    gaugeSeminorm (p.balanced_ball_zero 1) (p.convex_ball 0 1) (p.absorbent_ball_zero zero_lt_one) =
      p :=
  DFunLike.coe_injective p.gauge_ball

end AddCommGroup

section Seminormed

variable [SeminormedAddCommGroup E] [NormedSpace Real E] {s : Set E} {r : Real} {x : E}
open Metric

/--
theorem `gauge_unit_ball` / 定理 `gauge_unit_ball`

English:
theorem gauge_unit_ball
  given: (x : E)
  statement: gauge (ball (0 : E) 1) x = ‖x‖
  proof: by
  rw [← ball_normSeminorm Real]; rw [Seminorm.gauge_ball]; rw [coe_normSeminorm]

中文:
定理 gauge_unit_ball
  条件: (x : E)
  结论: gauge (ball (0 : E) 1) x = ‖x‖
  证明: by
  rw [← ball_normSeminorm Real]; rw [Seminorm.gauge_ball]; rw [coe_normSeminorm]

Depends on / 依赖: Seminorm, Seminorm.gauge_ball, ball_normSeminorm, coe_normSeminorm, gauge_ball
-/
theorem gauge_unit_ball (x : E) : gauge (ball (0 : E) 1) x = ‖x‖ := by
  rw [← ball_normSeminorm Real]; rw [Seminorm.gauge_ball]; rw [coe_normSeminorm]

/--
theorem `gauge_ball` / 定理 `gauge_ball`

English:
theorem gauge_ball
  given: (hr : 0 <= r) (x : E)
  statement: gauge (ball (0 : E) r) x = ‖x‖ / r
  proof: by
  rcases hr.eq_or_lt with rfl | hr
  · simp
  · rw [← smul_unitBall_of_pos hr, gauge_smul_left, Pi.smul_apply, gauge_unit_ball, smul_eq_mul,
    abs_of_nonneg hr.le, div_eq_inv_mul]
    simp_rw [mem_ball_zero_iff, norm_neg]
    exact fun _ => id

@[simp]

中文:
定理 gauge_ball
  条件: (hr : 0 <= r) (x : E)
  结论: gauge (ball (0 : E) r) x = ‖x‖ / r
  证明: by
  rcases hr.eq_or_lt with rfl | hr
  · simp
  · rw [← smul_unitBall_of_pos hr, gauge_smul_left, Pi.smul_apply, gauge_unit_ball, smul_eq_mul,
    abs_of_nonneg hr.le, div_eq_inv_mul]
    simp_rw [mem_ball_zero_iff, norm_neg]
    exact fun _ => id

@[simp]

Depends on / 依赖: Pi.smul_apply, abs_of_nonneg, div_eq_inv_mul, eq_or_lt, gauge_smul_left, gauge_unit_ball, hr.eq_or_lt, hr.le, mem_ball_zero_iff, norm_neg, simp_rw, smul_apply, smul_eq_mul, smul_unitBall_of_pos
-/
theorem gauge_ball (hr : 0 <= r) (x : E) : gauge (ball (0 : E) r) x = ‖x‖ / r := by
  rcases hr.eq_or_lt with rfl | hr
  · simp
  · rw [← smul_unitBall_of_pos hr, gauge_smul_left, Pi.smul_apply, gauge_unit_ball, smul_eq_mul,
    abs_of_nonneg hr.le, div_eq_inv_mul]
    simp_rw [mem_ball_zero_iff, norm_neg]
    exact fun _ => id

@[simp]
/--
theorem `gauge_closure_zero` / 定理 `gauge_closure_zero`

English:
theorem gauge_closure_zero
  statement: gauge (closure (0 : Set E)) = 0
  proof: funext fun x => by
  simp only [← singleton_zero, gauge_def', mem_closure_zero_iff_norm, norm_smul, mul_eq_zero,
    norm_eq_zero, inv_eq_zero]
  rcases (norm_nonneg x).eq_or_lt' with hx | hx
  · convert! csInf_Ioi (a := (0 : Real))
    exact Set.ext fun r => and_iff_left (.inr hx)
  · convert! Real

中文:
定理 gauge_closure_zero
  结论: gauge (closure (0 : 集合 E)) = 0
  证明: funext fun x => by
  simp only [← singleton_zero, gauge_def', mem_closure_zero_iff_norm, norm_smul, mul_eq_zero,
    norm_eq_zero, inv_eq_zero]
  rcases (norm_nonneg x).eq_or_lt' with hx | hx
  · convert! csInf_Ioi (a := (0 : Real))
    exact Set.ext fun r => and_iff_left (.inr hx)
  · convert! Real

Depends on / 依赖: Real.sInf_empty, Set.ext, and_iff_left, convert, csInf_Ioi, eq_empty_of_forall_notMem, eq_or_lt, gauge_def, hr.resolve_left, hx.ne, inv_eq_zero, mem_closure_zero_iff_norm, mul_eq_zero, norm_eq_zero, norm_nonneg, norm_smul, out.ne, resolve_left, sInf_empty, singleton_zero
-/
theorem gauge_closure_zero : gauge (closure (0 : Set E)) = 0 := funext fun x => by
  simp only [← singleton_zero, gauge_def', mem_closure_zero_iff_norm, norm_smul, mul_eq_zero,
    norm_eq_zero, inv_eq_zero]
  rcases (norm_nonneg x).eq_or_lt' with hx | hx
  · convert! csInf_Ioi (a := (0 : Real))
    exact Set.ext fun r => and_iff_left (.inr hx)
  · convert! Real.sInf_empty
exact eq_empty_of_forall_notMem fun r ⟨hr₀, hr⟩ => hx.ne' hr.resolve_left hr₀.out.ne'

@[simp]
/--
theorem `gauge_closedBall` / 定理 `gauge_closedBall`

English:
theorem gauge_closedBall
  given: (hr : 0 <= r) (x : E)
  statement: gauge (closedBall (0 : E) r) x = ‖x‖ / r
  proof: by
  rcases hr.eq_or_lt with rfl | hr'
  · rw [div_zero, closedBall_zero', singleton_zero, gauge_closure_zero]; rfl
  · apply le_antisymm
    · rw [← gauge_ball hr]
      exact gauge_mono (absorbent_ball_zero hr') ball_subset_closedBall x
    · suffices forallᶠ R in 𝓝[>] r, ‖x‖ / R <= gauge (closedB

中文:
定理 gauge_closedBall
  条件: (hr : 0 <= r) (x : E)
  结论: gauge (closedBall (0 : E) r) x = ‖x‖ / r
  证明: by
  rcases hr.eq_or_lt with rfl | hr'
  · rw [div_zero, closedBall_zero', singleton_zero, gauge_closure_zero]; rfl
  · apply le_antisymm
    · rw [← gauge_ball hr]
      exact gauge_mono (absorbent_ball_zero hr') ball_subset_closedBall x
    · suffices forallᶠ R in 𝓝[>] r, ‖x‖ / R <= gauge (closedB

Depends on / 依赖: absorbent_ball_zero, ball_subset_closedBall, closedBall, closedBall_subset_ba, closedBall_zero, div_zero, eq_or_lt, filter_upwards, gauge_ball, gauge_closure_zero, gauge_mono, hR.out.le, hr.eq_or_lt, hr.trans, inf_le_left, le_antisymm, le_of_tendsto, self_mem_nhdsWithin, singleton_zero, tendsto_const_nhds
-/
theorem gauge_closedBall (hr : 0 <= r) (x : E) : gauge (closedBall (0 : E) r) x = ‖x‖ / r := by
  rcases hr.eq_or_lt with rfl | hr'
  · rw [div_zero, closedBall_zero', singleton_zero, gauge_closure_zero]; rfl
  · apply le_antisymm
    · rw [← gauge_ball hr]
      exact gauge_mono (absorbent_ball_zero hr') ball_subset_closedBall x
    · suffices forallᶠ R in 𝓝[>] r, ‖x‖ / R <= gauge (closedBall 0 r) x by
        refine le_of_tendsto ?_ this
        exact tendsto_const_nhds.div inf_le_left hr'.ne'
      filter_upwards [self_mem_nhdsWithin] with R hR
      rw [← gauge_ball (hr.trans hR.out.le)]
      refine gauge_mono ?_ (closedBall_subset_ball hR) _
      exact (absorbent_ball_zero hr').mono ball_subset_closedBall

/--
theorem `mul_gauge_le_norm` / 定理 `mul_gauge_le_norm`

English:
theorem mul_gauge_le_norm
  given: (hs : Metric.ball (0 : E) r subseteq s)
  statement: r * gauge s x <= ‖x‖
  proof: by
  obtain hr | hr := le_or_gt r 0
  · exact (mul_nonpos_of_nonpos_of_nonneg hr <| gauge_nonneg _).trans (norm_nonneg _)
  rw [mul_comm]; rw [← le_div_iff₀ hr]; rw [← gauge_ball hr.le]
  exact gauge_mono (absorbent_ball_zero hr) hs x

中文:
定理 mul_gauge_le_norm
  条件: (hs : Metric.ball (0 : E) r subseteq s)
  结论: r * gauge s x <= ‖x‖
  证明: by
  obtain hr | hr := le_or_gt r 0
  · exact (mul_nonpos_of_nonpos_of_nonneg hr <| gauge_nonneg _).trans (norm_nonneg _)
  rw [mul_comm]; rw [← le_div_iff₀ hr]; rw [← gauge_ball hr.le]
  exact gauge_mono (absorbent_ball_zero hr) hs x

Depends on / 依赖: absorbent_ball_zero, gauge_ball, gauge_mono, gauge_nonneg, hr.le, le_or_gt, mul_comm, mul_nonpos_of_nonpos_of_nonneg, norm_nonneg
-/
theorem mul_gauge_le_norm (hs : Metric.ball (0 : E) r subseteq s) : r * gauge s x <= ‖x‖ := by
  obtain hr | hr := le_or_gt r 0
  · exact (mul_nonpos_of_nonpos_of_nonneg hr <| gauge_nonneg _).trans (norm_nonneg _)
  rw [mul_comm]; rw [← le_div_iff₀ hr]; rw [← gauge_ball hr.le]
  exact gauge_mono (absorbent_ball_zero hr) hs x

/--
theorem `Convex.lipschitzWith_gauge` / 定理 `Convex.lipschitzWith_gauge`

English:
theorem Convex.lipschitzWith_gauge
  statement: {r : Real>=0} (hc : Convex Real s) (hr : 0 < r)
  proof: have : Absorbent Real (Metric.ball (0 : E) r) := absorbent_ball_zero hr
  LipschitzWith.of_le_add_mul _ fun x y =>
    calc
      gauge s x = gauge s (y + (x - y)) := by simp
      _ <= gauge s y + gauge s (x - y) := gauge_add_le hc (this.mono hs) _ _
      _ <= gauge s y + ‖x - y‖ / r := by grw [ga

中文:
定理 凸.lipschitzWith_gauge
  结论: {r : 实数>=0} (hc : 凸 实数 s) (hr : 0 < r)
  证明: have : Absorbent Real (Metric.ball (0 : E) r) := absorbent_ball_zero hr
  LipschitzWith.of_le_add_mul _ fun x y =>
    calc
      gauge s x = gauge s (y + (x - y)) := by simp
      _ <= gauge s y + gauge s (x - y) := gauge_add_le hc (this.mono hs) _ _
      _ <= gauge s y + ‖x - y‖ / r := by grw [ga

Depends on / 依赖: Absorbent, LipschitzWith, LipschitzWith.of_le_add_mul, Metric, Metric.ball, NNReal, NNReal.coe_inv, absorbent_ball_zero, coe_inv, dist_eq_norm, div_eq_inv_mul, gauge_add_le, gauge_ball, gauge_mono, of_le_add_mul, this.mono
-/
theorem Convex.lipschitzWith_gauge {r : Real>=0} (hc : Convex Real s) (hr : 0 < r)
    (hs : Metric.ball (0 : E) r subseteq s) : LipschitzWith r⁻¹ (gauge s) :=
  have : Absorbent Real (Metric.ball (0 : E) r) := absorbent_ball_zero hr
  LipschitzWith.of_le_add_mul _ fun x y =>
    calc
      gauge s x = gauge s (y + (x - y)) := by simp
      _ <= gauge s y + gauge s (x - y) := gauge_add_le hc (this.mono hs) _ _
      _ <= gauge s y + ‖x - y‖ / r := by grw [gauge_mono this hs (x - y), gauge_ball]; positivity
      _ = gauge s y + r⁻¹ * dist x y := by rw [dist_eq_norm, div_eq_inv_mul, NNReal.coe_inv]

/--
theorem `Convex.lipschitz_gauge` / 定理 `Convex.lipschitz_gauge`

English:
theorem Convex.lipschitz_gauge
  given: (hc : Convex Real s) (h₀ : s in 𝓝 (0 : E))
  proof: let ⟨r, hr₀, hr⟩ := Metric.mem_nhds_iff.1 h₀
  ⟨(⟨r, hr₀.le⟩ : Real>=0)⁻¹, hc.lipschitzWith_gauge hr₀ hr⟩

中文:
定理 凸.lipschitz_gauge
  条件: (hc : 凸 实数 s) (h₀ : s in 𝓝 (0 : E))
  证明: let ⟨r, hr₀, hr⟩ := Metric.mem_nhds_iff.1 h₀
  ⟨(⟨r, hr₀.le⟩ : Real>=0)⁻¹, hc.lipschitzWith_gauge hr₀ hr⟩

Depends on / 依赖: Metric, Metric.mem_nhds_iff, hc.lipschitzWith_gauge, lipschitzWith_gauge, mem_nhds_iff
-/
theorem Convex.lipschitz_gauge (hc : Convex Real s) (h₀ : s in 𝓝 (0 : E)) :
    exists K, LipschitzWith K (gauge s) :=
  let ⟨r, hr₀, hr⟩ := Metric.mem_nhds_iff.1 h₀
  ⟨(⟨r, hr₀.le⟩ : Real>=0)⁻¹, hc.lipschitzWith_gauge hr₀ hr⟩

/--
theorem `Convex.uniformContinuous_gauge` / 定理 `Convex.uniformContinuous_gauge`

English:
theorem Convex.uniformContinuous_gauge
  given: (hc : Convex Real s) (h₀ : s in 𝓝 (0 : E))
  proof: let ⟨_K, hK⟩ := hc.lipschitz_gauge h₀; hK.uniformContinuous

中文:
定理 凸.uniformContinuous_gauge
  条件: (hc : 凸 实数 s) (h₀ : s in 𝓝 (0 : E))
  证明: let ⟨_K, hK⟩ := hc.lipschitz_gauge h₀; hK.uniformContinuous

Depends on / 依赖: hK.uniformContinuous, hc.lipschitz_gauge, lipschitz_gauge, uniformContinuous
-/
theorem Convex.uniformContinuous_gauge (hc : Convex Real s) (h₀ : s in 𝓝 (0 : E)) :
    UniformContinuous (gauge s) :=
  let ⟨_K, hK⟩ := hc.lipschitz_gauge h₀; hK.uniformContinuous

end Seminormed

section Normed

variable [NormedAddCommGroup E] [NormedSpace Real E] {s : Set E} {r : Real} {x : E}
open Metric

/--
theorem `le_gauge_of_subset_closedBall` / 定理 `le_gauge_of_subset_closedBall`

English:
theorem le_gauge_of_subset_closedBall
  given: (hs : Absorbent Real s) (hr : 0 <= r) (hsr : s subseteq closedBall 0 r)
  proof: by
  rw [← gauge_closedBall hr]
  exact gauge_mono hs hsr _

中文:
定理 le_gauge_of_subset_closedBall
  条件: (hs : Absorbent 实数 s) (hr : 0 <= r) (hsr : s subseteq closedBall 0 r)
  证明: by
  rw [← gauge_closedBall hr]
  exact gauge_mono hs hsr _

Depends on / 依赖: gauge_closedBall, gauge_mono
-/
theorem le_gauge_of_subset_closedBall (hs : Absorbent Real s) (hr : 0 <= r) (hsr : s subseteq closedBall 0 r) :
    ‖x‖ / r <= gauge s x := by
  rw [← gauge_closedBall hr]
  exact gauge_mono hs hsr _

end Normed
