/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.NumberTheory.Transcendental.Liouville.Basic
public import Mathlib.Topology.Baire.Lemmas
public import Mathlib.Topology.Baire.LocallyCompactRegular
public import Mathlib.Topology.Instances.Irrational

/-!
# Density of Liouville numbers

In this file we prove that the set of Liouville numbers form a dense `Gδ` set. We also prove a
similar statement about irrational numbers.
-/

public section


open scoped Filter

open Filter Set Metric

/--
theorem `setOfPred_liouville_eq_iInter_iUnion` / 定理 `setOfPred_liouville_eq_iInter_iUnion`

English:
theorem setOfPred_liouville_eq_iInter_iUnion
  proof: by
  ext x
  simp only [mem_iInter, mem_iUnion, Liouville, mem_ofPred_eq, exists_prop, Set.mem_sdiff,
    mem_singleton_iff, mem_ball, Real.dist_eq, and_comm]

@[deprecated (since := "2026-07-09")]
alias setOf_liouville_eq_iInter_iUnion := setOfPred_liouville_eq_iInter_iUnion

中文:
定理 setOfPred_liouville_eq_i整数er_iUnion
  证明: by
  ext x
  simp only [mem_iInter, mem_iUnion, Liouville, mem_ofPred_eq, exists_prop, Set.mem_sdiff,
    mem_singleton_iff, mem_ball, Real.dist_eq, and_comm]

@[deprecated (since := "2026-07-09")]
alias setOf_liouville_eq_iInter_iUnion := setOfPred_liouville_eq_iInter_iUnion

Depends on / 依赖: Liouville, Real.dist_eq, Set.mem_sdiff, and_comm, dist_eq, exists_prop, mem_ball, mem_iInter, mem_iUnion, mem_ofPred_eq, mem_sdiff, mem_singleton_iff
-/
theorem setOfPred_liouville_eq_iInter_iUnion :
    { x | Liouville x } =
      ⋂ n : Nat, ⋃ (a : Int) (b : Int) (_ : 1 < b),
      ball ((a : Real) / b) (1 / (b : Real) ^ n) \ {(a : Real) / b} := by
  ext x
  simp only [mem_iInter, mem_iUnion, Liouville, mem_ofPred_eq, exists_prop, Set.mem_sdiff,
    mem_singleton_iff, mem_ball, Real.dist_eq, and_comm]

@[deprecated (since := "2026-07-09")]
alias setOf_liouville_eq_iInter_iUnion := setOfPred_liouville_eq_iInter_iUnion

/--
theorem `IsGδ.setOfPred_liouville` / 定理 `IsGδ.setOfPred_liouville`

English:
theorem IsGδ.setOfPred_liouville
  statement: IsGδ { x | Liouville x }
  proof: by
  rw [setOfPred_liouville_eq_iInter_iUnion]
  refine .iInter fun n => IsOpen.isGδ ?_
  refine isOpen_iUnion fun a => isOpen_iUnion fun b => isOpen_iUnion fun _hb => ?_
  exact isOpen_ball.inter isClosed_singleton.isOpen_compl

@[deprecated (since := "2026-07-09")]
alias IsGδ.setOf_liouville := Is

中文:
定理 IsGδ.setOfPred_liouville
  结论: IsGδ { x | Liouville x }
  证明: by
  rw [setOfPred_liouville_eq_iInter_iUnion]
  refine .iInter fun n => IsOpen.isGδ ?_
  refine isOpen_iUnion fun a => isOpen_iUnion fun b => isOpen_iUnion fun _hb => ?_
  exact isOpen_ball.inter isClosed_singleton.isOpen_compl

@[deprecated (since := "2026-07-09")]
alias IsGδ.setOf_liouville := Is

Depends on / 依赖: IsOpen, IsOpen.isG, iInter, isClosed_singleton, isClosed_singleton.isOpen_compl, isOpen_ball, isOpen_ball.inter, isOpen_compl, isOpen_iUnion, setOfPred_liouville_eq_iInter_iUnion
-/
theorem IsGδ.setOfPred_liouville : IsGδ { x | Liouville x } := by
  rw [setOfPred_liouville_eq_iInter_iUnion]
  refine .iInter fun n => IsOpen.isGδ ?_
  refine isOpen_iUnion fun a => isOpen_iUnion fun b => isOpen_iUnion fun _hb => ?_
  exact isOpen_ball.inter isClosed_singleton.isOpen_compl

@[deprecated (since := "2026-07-09")]
alias IsGδ.setOf_liouville := IsGδ.setOfPred_liouville

/--
theorem `setOfPred_liouville_eq_irrational_inter_iInter_iUnion` / 定理 `setOfPred_liouville_eq_irrational_inter_iInter_iUnion`

English:
theorem setOfPred_liouville_eq_irrational_inter_iInter_iUnion
  proof: by
  refine Subset.antisymm ?_ ?_
  · refine subset_inter (fun x hx => hx.irrational) ?_
    rw [setOfPred_liouville_eq_iInter_iUnion]
    exact iInter_mono fun n => iUnion₂_mono fun a b => iUnion_mono fun _hb => sdiff_subset
  · simp only [inter_iInter, inter_iUnion, setOfPred_liouville_eq_iInter_i

中文:
定理 setOfPred_liouville_eq_irrational_inter_i整数er_iUnion
  证明: by
  refine Subset.antisymm ?_ ?_
  · refine subset_inter (fun x hx => hx.irrational) ?_
    rw [setOfPred_liouville_eq_iInter_iUnion]
    exact iInter_mono fun n => iUnion₂_mono fun a b => iUnion_mono fun _hb => sdiff_subset
  · simp only [inter_iInter, inter_iUnion, setOfPred_liouville_eq_iInter_i

Depends on / 依赖: Subset, Subset.antisymm, Subset.rfl, antisymm, hx.irrational, iInter_mono, iUnion_mono, inter_comm, inter_iInter, inter_iUnion, irrational, sdiff_subset, sdiff_subset_sdiff, setOfPred_liouville_eq_iInter_iUnion, singleton_subset_iff, subset_inter
-/
theorem setOfPred_liouville_eq_irrational_inter_iInter_iUnion :
    { x | Liouville x } =
      { x | Irrational x } inter ⋂ n : Nat, ⋃ (a : Int) (b : Int) (_ : 1 < b),
      ball (a / b) (1 / (b : Real) ^ n) := by
  refine Subset.antisymm ?_ ?_
  · refine subset_inter (fun x hx => hx.irrational) ?_
    rw [setOfPred_liouville_eq_iInter_iUnion]
    exact iInter_mono fun n => iUnion₂_mono fun a b => iUnion_mono fun _hb => sdiff_subset
  · simp only [inter_iInter, inter_iUnion, setOfPred_liouville_eq_iInter_iUnion]
    refine iInter_mono fun n => iUnion₂_mono fun a b => iUnion_mono fun hb => ?_
    rw [inter_comm]
    exact sdiff_subset_sdiff Subset.rfl (singleton_subset_iff.2 ⟨a / b, by norm_cast⟩)

@[deprecated (since := "2026-07-09")]
alias setOf_liouville_eq_irrational_inter_iInter_iUnion :=
  setOfPred_liouville_eq_irrational_inter_iInter_iUnion

/--
theorem `eventually_residual_liouville` / 定理 `eventually_residual_liouville`

English:
theorem eventually_residual_liouville
  statement: forallᶠ x in residual Real, Liouville x
  proof: by
  rw [Filter.Eventually]; rw [setOfPred_liouville_eq_irrational_inter_iInter_iUnion]
  refine eventually_residual_irrational.and ?_
  refine residual_of_dense_Gδ ?_ (Rat.isDenseEmbedding_coe_real.dense.mono ?_)
· exact .iInter fun n => IsOpen.isGδ
          isOpen_iUnion fun a => isOpen_iUnion fu

中文:
定理 eventually_residual_liouville
  结论: 对任意ᶠ x in residual 实数, Liouville x
  证明: by
  rw [Filter.Eventually]; rw [setOfPred_liouville_eq_irrational_inter_iInter_iUnion]
  refine eventually_residual_irrational.and ?_
  refine residual_of_dense_Gδ ?_ (Rat.isDenseEmbedding_coe_real.dense.mono ?_)
· exact .iInter fun n => IsOpen.isGδ
          isOpen_iUnion fun a => isOpen_iUnion fu

Depends on / 依赖: Eventually, Filter, Filter.Eventually, IsOpen, IsOpen.isG, Rat.isDenseEmbedding_coe_real.dense.mono, convert, eventually_residual_irrational, eventually_residual_irrational.and, iInter, isDenseEmbedding_coe_real, isOpen_ball, isOpen_iUnion, mem_ball_self, mem_iInter, mem_iUnion, r.den, r.num, r.pos, setOfPred_liouville_eq_irrational_inter_iInter_iUnion
-/
theorem eventually_residual_liouville : forallᶠ x in residual Real, Liouville x := by
  rw [Filter.Eventually]; rw [setOfPred_liouville_eq_irrational_inter_iInter_iUnion]
  refine eventually_residual_irrational.and ?_
  refine residual_of_dense_Gδ ?_ (Rat.isDenseEmbedding_coe_real.dense.mono ?_)
· exact .iInter fun n => IsOpen.isGδ
          isOpen_iUnion fun a => isOpen_iUnion fun b => isOpen_iUnion fun _hb => isOpen_ball
  · rintro _ ⟨r, rfl⟩
    simp only [mem_iInter, mem_iUnion]
    refine fun n => ⟨r.num * 2, r.den * 2, ?_, ?_⟩
    · have := r.pos; lia
    · convert! @mem_ball_self Real _ (r : Real) _ _
      · push_cast
        -- Workaround for https://github.com/leanprover/lean4/pull/6438; this eliminates an
        -- `Expr.mdata` that would cause `norm_cast` to skip a numeral.
        rw [Eq.refl (2 : Real)]
        norm_cast
        simp [Rat.divInt_mul_right (two_ne_zero)]
      · refine one_div_pos.2 (pow_pos (Int.cast_pos.2 ?_) _)
        exact mul_pos (Int.natCast_pos.2 r.pos) zero_lt_two

/--
theorem `dense_liouville` / 定理 `dense_liouville`

English:
theorem dense_liouville
  statement: Dense { x | Liouville x }
  proof: dense_of_mem_residual eventually_residual_liouville

中文:
定理 dense_liouville
  结论: 稠密 { x | Liouville x }
  证明: dense_of_mem_residual eventually_residual_liouville

Depends on / 依赖: dense_of_mem_residual, eventually_residual_liouville
-/
theorem dense_liouville : Dense { x | Liouville x } :=
  dense_of_mem_residual eventually_residual_liouville
