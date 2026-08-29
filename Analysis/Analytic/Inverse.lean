/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Analytic.Composition
public import Mathlib.Analysis.Analytic.Linear
public import Mathlib.Tactic.Positivity

/-!

# Inverse of analytic functions

We construct the left and right inverse of a formal multilinear series with invertible linear term,
we prove that they coincide and study their properties (notably convergence). We deduce that the
inverse of an analytic open partial homeomorphism is analytic.

## Main statements

* `p.leftInv i x`: the formal left inverse of the formal multilinear series `p`, with constant
  coefficient `x`, for `i : E ≃L[𝕜] F` which coincides with `p₁`.
* `p.rightInv i x`: the formal right inverse of the formal multilinear series `p`, with constant
  coefficient `x`, for `i : E ≃L[𝕜] F` which coincides with `p₁`.
* `p.leftInv_comp` says that `p.leftInv i x` is indeed a left inverse to `p` when `p₁ = i`.
* `p.rightInv_comp` says that `p.rightInv i x` is indeed a right inverse to `p` when `p₁ = i`.
* `p.leftInv_eq_rightInv`: the two inverses coincide.
* `p.radius_rightInv_pos_of_radius_pos`: if a power series has a positive radius of convergence,
  then so does its inverse.

* `OpenPartialHomeomorph.hasFPowerSeriesAt_symm` shows that, if an open partial homeomorph has a
  power series `p` at a point, with invertible linear part, then the inverse also has a power series
  at the image point, given by `p.leftInv`.
-/

@[expose] public section

open scoped Topology ENNReal

open Finset Filter

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

namespace FormalMultilinearSeries

/-! ### The left inverse of a formal multilinear series -/


/--
Definition of `leftInv` / `leftInv` 的定义

English:
definition leftInv
  signature: (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x : E)

中文:
定义 leftInv
  签名: (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x : E)
-/
noncomputable def leftInv (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x : E) :
    FormalMultilinearSeries 𝕜 F E
  | 0 => ContinuousMultilinearMap.uncurry0 𝕜 _ x
  | 1 => (continuousMultilinearCurryFin1 𝕜 F E).symm i.symm
  | n + 2 =>
    -∑ c : { c : Composition (n + 2) // c.length < n + 2 },
        (leftInv p i x (c : Composition (n + 2)).length).compAlongComposition
          (p.compContinuousLinearMap i.symm) c

@[simp]
/--
theorem `leftInv_coeff_zero` / 定理 `leftInv_coeff_zero`

English:
theorem leftInv_coeff_zero
  given: (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x : E)
  proof: by rw [leftInv]

@[simp]

中文:
定理 leftInv_coeff_zero
  条件: (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x : E)
  证明: by rw [leftInv]

@[simp]

Depends on / 依赖: leftInv
-/
theorem leftInv_coeff_zero (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x : E) :
    p.leftInv i x 0 = ContinuousMultilinearMap.uncurry0 𝕜 _ x := by rw [leftInv]

@[simp]
/--
theorem `leftInv_coeff_one` / 定理 `leftInv_coeff_one`

English:
theorem leftInv_coeff_one
  given: (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x : E)
  proof: by rw [leftInv]

中文:
定理 leftInv_coeff_one
  条件: (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x : E)
  证明: by rw [leftInv]

Depends on / 依赖: leftInv
-/
theorem leftInv_coeff_one (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x : E) :
    p.leftInv i x 1 = (continuousMultilinearCurryFin1 𝕜 F E).symm i.symm := by rw [leftInv]

/--
theorem `leftInv_removeZero` / 定理 `leftInv_removeZero`

English:
theorem leftInv_removeZero
  given: (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x : E)
  proof: by
  ext1 n
  induction n using Nat.strong_induction_on with | _ n IH
  match n with
  | 0 => simp -- if one replaces `simp` with `refl`, the proof times out in the kernel.
  | 1 => simp -- TODO: why?
  | n + 2 =>
    simp only [leftInv, neg_inj]
    refine Finset.sum_congr rfl fun c cuniv => ?_
    rcases c with ⟨c, hc⟩
    ext v
    simp [IH _ hc]

中文:
定理 leftInv_removeZero
  条件: (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x : E)
  证明: by
  ext1 n
  induction n using Nat.strong_induction_on with | _ n IH
  match n with
  | 0 => simp -- if one replaces `simp` with `refl`, the proof times out in the kernel.
  | 1 => simp -- TODO: why?
  | n + 2 =>
    simp only [leftInv, neg_inj]
    refine Finset.sum_congr rfl fun c cuniv => ?_
    rcases c with ⟨c, hc⟩
    ext v
    simp [IH _ hc]

Depends on / 依赖: Finset, Finset.sum_congr, Nat.strong_induction_on, kernel, leftInv, neg_inj, replaces, strong_induction_on, sum_congr
-/
theorem leftInv_removeZero (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x : E) :
    p.removeZero.leftInv i x = p.leftInv i x := by
  ext1 n
  induction n using Nat.strong_induction_on with | _ n IH
  match n with
  | 0 => simp -- if one replaces `simp` with `refl`, the proof times out in the kernel.
  | 1 => simp -- TODO: why?
  | n + 2 =>
    simp only [leftInv, neg_inj]
    refine Finset.sum_congr rfl fun c cuniv => ?_
    rcases c with ⟨c, hc⟩
    ext v
    simp [IH _ hc]

/--
theorem `leftInv_comp` / 定理 `leftInv_comp`

English:
theorem leftInv_comp
  statement: (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x : E)
  proof: by
  ext n v
  match n with
  | 0 =>
    simp only [comp_coeff_zero', leftInv_coeff_zero, ContinuousMultilinearMap.uncurry0_apply,
      id_apply_zero]
  | 1 =>
    simp only [leftInv_coeff_one, comp_coeff_one, h, id_apply_one, ContinuousLinearEquiv.coe_apply,
      ContinuousLinearEquiv.symm_apply_apply, continuousMultilinearCurryFin1_symm_apply]
  | n + 2 =>
    have A :
      (Finset.univ : Finset (Composition (n + 2))) =
        {c | Composition.length c < n + 2}.toFinset union {Composition.ones (n + 2)} := by
      refine Subset.antisymm (fun c _ => ?_) (subset_univ _)
      by_cases! h : c.length < n + 2
      · simp [h]
      · simp [Composition.eq_ones_iff_le_length.2 h]
    have B :
      Disjoint ({c | Composition.length c < n + 2} : Set (Composition (n + 2))).toFinset
        {Composition.ones (n + 2)} := by
      simp
    have C :
      ((p.leftInv i x (Composition.ones (n + 2)).length)
          fun j : Fin (Composition.ones n.succ.succ).length =>
          p 1 fun _ => v ((Fin.castLE (Composition.length_le _)) j)) =
        p.leftInv i x (n + 2) fun j : Fin (n + 2) => p 1 fun _ => v j := by
      apply FormalMultilinearSeries.congr _ (Composition.ones_length _) fun j hj1 hj2 => ?_
      exact FormalMultilinearSeries.congr _ rfl fun k _ _ => by congr
    have D :
      (p.leftInv i x (n + 2) fun j : Fin (n + 2) => p 1 fun _ => v j) =
        -∑ c in {c : Composition (n + 2) | c.length < n + 2}.toFinset,
            (p.leftInv i x c.length) (p.applyComposition c v) := by
      simp only [leftInv, _root_.neg_apply, neg_inj, _root_.sum_apply]
      convert!
        (sum_toFinset_eq_subtype (fun c : Composition (n + 2) => c.length < n + 2)
              (fun c : Composition (n + 2) =>
                (ContinuousMultilinearMap.compAlongComposition
                    (p.compContinuousLinearMap (i.symm : F ->L[𝕜] E)) c (p.leftInv i x c.length))
                  fun j : Fin (n + 2) => p 1 fun _ : Fin 1 => v j)).symm.trans
          _
      simp only [compContinuousLinearMap_applyComposition,
        ContinuousMultilinearMap.compAlongComposition_apply]
      congr
      ext c
      congr
      ext k
      simp [h]
    simp [FormalMultilinearSeries.comp, A, Finset.sum_union B,
      applyComposition_ones, C, D, -Set.toFinset_ofPred, -Finset.union_singleton]

中文:
定理 leftInv_comp
  结论: (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x : E)
  证明: by
  ext n v
  match n with
  | 0 =>
    simp only [comp_coeff_zero', leftInv_coeff_zero, ContinuousMultilinearMap.uncurry0_apply,
      id_apply_zero]
  | 1 =>
    simp only [leftInv_coeff_one, comp_coeff_one, h, id_apply_one, ContinuousLinearEquiv.coe_apply,
      ContinuousLinearEquiv.symm_apply_apply, continuousMultilinearCurryFin1_symm_apply]
  | n + 2 =>
    have A :
      (Finset.univ : Finset (Composition (n + 2))) =
        {c | Composition.length c < n + 2}.toFinset union {Composition.ones (n + 2)} := by
      refine Subset.antisymm (fun c _ => ?_) (subset_univ _)
      by_cases! h : c.length < n + 2
      · simp [h]
      · simp [Composition.eq_ones_iff_le_length.2 h]
    have B :
      Disjoint ({c | Composition.length c < n + 2} : Set (Composition (n + 2))).toFinset
        {Composition.ones (n + 2)} := by
      simp
    have C :
      ((p.leftInv i x (Composition.ones (n + 2)).length)
          fun j : Fin (Composition.ones n.succ.succ).length =>
          p 1 fun _ => v ((Fin.castLE (Composition.length_le _)) j)) =
        p.leftInv i x (n + 2) fun j : Fin (n + 2) => p 1 fun _ => v j := by
      apply FormalMultilinearSeries.congr _ (Composition.ones_length _) fun j hj1 hj2 => ?_
      exact FormalMultilinearSeries.congr _ rfl fun k _ _ => by congr
    have D :
      (p.leftInv i x (n + 2) fun j : Fin (n + 2) => p 1 fun _ => v j) =
        -∑ c in {c : Composition (n + 2) | c.length < n + 2}.toFinset,
            (p.leftInv i x c.length) (p.applyComposition c v) := by
      simp only [leftInv, _root_.neg_apply, neg_inj, _root_.sum_apply]
      convert!
        (sum_toFinset_eq_subtype (fun c : Composition (n + 2) => c.length < n + 2)
              (fun c : Composition (n + 2) =>
                (ContinuousMultilinearMap.compAlongComposition
                    (p.compContinuousLinearMap (i.symm : F ->L[𝕜] E)) c (p.leftInv i x c.length))
                  fun j : Fin (n + 2) => p 1 fun _ : Fin 1 => v j)).symm.trans
          _
      simp only [compContinuousLinearMap_applyComposition,
        ContinuousMultilinearMap.compAlongComposition_apply]
      congr
      ext c
      congr
      ext k
      simp [h]
    simp [FormalMultilinearSeries.comp, A, Finset.sum_union B,
      applyComposition_ones, C, D, -Set.toFinset_ofPred, -Finset.union_singleton]

Depends on / 依赖: Composition, Composition.length, Composition.ones, ContinuousLinearEquiv, ContinuousLinearEquiv.coe_apply, ContinuousLinearEquiv.symm_apply_apply, ContinuousMultilinearMap, ContinuousMultilinearMap.uncurry0_apply, Finset, Finset.univ, Subset, Subset.antisymm, antisymm, coe_apply, comp_coeff_one, comp_coeff_zero, continuousMultilinearCurryFin1_symm_apply, id_apply_one, id_apply_zero, leftInv_coeff_one
-/
theorem leftInv_comp (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x : E)
    (h : p 1 = (continuousMultilinearCurryFin1 𝕜 E F).symm i) :
    (leftInv p i x).comp p = id 𝕜 E x := by
  ext n v
  match n with
  | 0 =>
    simp only [comp_coeff_zero', leftInv_coeff_zero, ContinuousMultilinearMap.uncurry0_apply,
      id_apply_zero]
  | 1 =>
    simp only [leftInv_coeff_one, comp_coeff_one, h, id_apply_one, ContinuousLinearEquiv.coe_apply,
      ContinuousLinearEquiv.symm_apply_apply, continuousMultilinearCurryFin1_symm_apply]
  | n + 2 =>
    have A :
      (Finset.univ : Finset (Composition (n + 2))) =
        {c | Composition.length c < n + 2}.toFinset union {Composition.ones (n + 2)} := by
      refine Subset.antisymm (fun c _ => ?_) (subset_univ _)
      by_cases! h : c.length < n + 2
      · simp [h]
      · simp [Composition.eq_ones_iff_le_length.2 h]
    have B :
      Disjoint ({c | Composition.length c < n + 2} : Set (Composition (n + 2))).toFinset
        {Composition.ones (n + 2)} := by
      simp
    have C :
      ((p.leftInv i x (Composition.ones (n + 2)).length)
          fun j : Fin (Composition.ones n.succ.succ).length =>
          p 1 fun _ => v ((Fin.castLE (Composition.length_le _)) j)) =
        p.leftInv i x (n + 2) fun j : Fin (n + 2) => p 1 fun _ => v j := by
      apply FormalMultilinearSeries.congr _ (Composition.ones_length _) fun j hj1 hj2 => ?_
      exact FormalMultilinearSeries.congr _ rfl fun k _ _ => by congr
    have D :
      (p.leftInv i x (n + 2) fun j : Fin (n + 2) => p 1 fun _ => v j) =
        -∑ c in {c : Composition (n + 2) | c.length < n + 2}.toFinset,
            (p.leftInv i x c.length) (p.applyComposition c v) := by
      simp only [leftInv, _root_.neg_apply, neg_inj, _root_.sum_apply]
      convert!
        (sum_toFinset_eq_subtype (fun c : Composition (n + 2) => c.length < n + 2)
              (fun c : Composition (n + 2) =>
                (ContinuousMultilinearMap.compAlongComposition
                    (p.compContinuousLinearMap (i.symm : F ->L[𝕜] E)) c (p.leftInv i x c.length))
                  fun j : Fin (n + 2) => p 1 fun _ : Fin 1 => v j)).symm.trans
          _
      simp only [compContinuousLinearMap_applyComposition,
        ContinuousMultilinearMap.compAlongComposition_apply]
      congr
      ext c
      congr
      ext k
      simp [h]
    simp [FormalMultilinearSeries.comp, A, Finset.sum_union B,
      applyComposition_ones, C, D, -Set.toFinset_ofPred, -Finset.union_singleton]

/-! ### The right inverse of a formal multilinear series -/


/--
Definition of `rightInv` / `rightInv` 的定义

English:
definition rightInv
  signature: (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x : E)
  body: fun k => if k < n + 2 then rightInv p i x k else 0;
    -(i.symm : F ->L[𝕜] E).compContinuousMultilinearMap ((p.comp q) (n + 2))

@[simp]

中文:
定义 rightInv
  签名: (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x : E)
  定义体: fun k => if k < n + 2 then rightInv p i x k else 0;
    -(i.symm : F ->L[𝕜] E).compContinuousMultilinearMap ((p.comp q) (n + 2))

@[simp]

Depends on / 依赖: rightInv
-/
noncomputable def rightInv (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x : E) :
    FormalMultilinearSeries 𝕜 F E
  | 0 => ContinuousMultilinearMap.uncurry0 𝕜 _ x
  | 1 => (continuousMultilinearCurryFin1 𝕜 F E).symm i.symm
  | n + 2 =>
    let q : FormalMultilinearSeries 𝕜 F E := fun k => if k < n + 2 then rightInv p i x k else 0;
    -(i.symm : F ->L[𝕜] E).compContinuousMultilinearMap ((p.comp q) (n + 2))

@[simp]
/--
theorem `rightInv_coeff_zero` / 定理 `rightInv_coeff_zero`

English:
theorem rightInv_coeff_zero
  given: (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x : E)
  proof: by rw [rightInv]

@[simp]

中文:
定理 rightInv_coeff_zero
  条件: (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x : E)
  证明: by rw [rightInv]

@[simp]

Depends on / 依赖: rightInv
-/
theorem rightInv_coeff_zero (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x : E) :
    p.rightInv i x 0 = ContinuousMultilinearMap.uncurry0 𝕜 _ x := by rw [rightInv]

@[simp]
/--
theorem `rightInv_coeff_one` / 定理 `rightInv_coeff_one`

English:
theorem rightInv_coeff_one
  given: (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x : E)
  proof: by rw [rightInv]

中文:
定理 rightInv_coeff_one
  条件: (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x : E)
  证明: by rw [rightInv]

Depends on / 依赖: rightInv
-/
theorem rightInv_coeff_one (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x : E) :
    p.rightInv i x 1 = (continuousMultilinearCurryFin1 𝕜 F E).symm i.symm := by rw [rightInv]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `rightInv_removeZero` / 定理 `rightInv_removeZero`

English:
theorem rightInv_removeZero
  given: (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x : E)
  proof: by
  ext1 n
  induction n using Nat.strong_induction_on with | _ n IH
  match n with
  | 0 => simp only [rightInv_coeff_zero]
  | 1 => simp only [rightInv_coeff_one]
  | n + 2 =>
    simp only [rightInv, neg_inj]
    rw [removeZero_comp_of_pos _ _ (add_pos_of_nonneg_of_pos n.zero_le zero_lt_two)]
    congr (config := { closePost := false }) 2 with k
    by_cases hk : k < n + 2 <;> simp [hk, IH]

中文:
定理 rightInv_removeZero
  条件: (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x : E)
  证明: by
  ext1 n
  induction n using Nat.strong_induction_on with | _ n IH
  match n with
  | 0 => simp only [rightInv_coeff_zero]
  | 1 => simp only [rightInv_coeff_one]
  | n + 2 =>
    simp only [rightInv, neg_inj]
    rw [removeZero_comp_of_pos _ _ (add_pos_of_nonneg_of_pos n.zero_le zero_lt_two)]
    congr (config := { closePost := false }) 2 with k
    by_cases hk : k < n + 2 <;> simp [hk, IH]

Depends on / 依赖: Nat.strong_induction_on, add_pos_of_nonneg_of_pos, closePost, config, n.zero_le, neg_inj, removeZero_comp_of_pos, rightInv, rightInv_coeff_one, rightInv_coeff_zero, strong_induction_on, zero_le, zero_lt_two
-/
theorem rightInv_removeZero (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x : E) :
    p.removeZero.rightInv i x = p.rightInv i x := by
  ext1 n
  induction n using Nat.strong_induction_on with | _ n IH
  match n with
  | 0 => simp only [rightInv_coeff_zero]
  | 1 => simp only [rightInv_coeff_one]
  | n + 2 =>
    simp only [rightInv, neg_inj]
    rw [removeZero_comp_of_pos _ _ (add_pos_of_nonneg_of_pos n.zero_le zero_lt_two)]
    congr (config := { closePost := false }) 2 with k
    by_cases hk : k < n + 2 <;> simp [hk, IH]

/--
theorem `comp_rightInv_aux1` / 定理 `comp_rightInv_aux1`

English:
theorem comp_rightInv_aux1
  statement: {n : Nat} (hn : 0 < n) (p : FormalMultilinearSeries 𝕜 E F)
  proof: by
  have A :
    (Finset.univ : Finset (Composition n)) =
      {c | 1 < Composition.length c}.toFinset union {Composition.single n hn} := by
    refine Subset.antisymm (fun c _ => ?_) (subset_univ _)
    by_cases h : 1 < c.length
    · simp [h]
    · have : c.length = 1 := by
        refine (eq_iff_le_not_lt.2 ⟨?_, h⟩).symm; exact c.length_pos_of_pos hn
      rw [← Composition.eq_single_iff_length hn] at this
      simp [this]
  have B :
    Disjoint ({c | 1 < Composition.length c} : Set (Composition n)).toFinset
      {Composition.single n hn} := by
    simp
  have C :
    p (Composition.single n hn).length (q.applyComposition (Composition.single n hn) v) =
      p 1 fun _ : Fin 1 => q n v := by
    apply p.congr (Composition.single_length hn) fun j hj1 _ => ?_
    simp [applyComposition_single]
  simp [FormalMultilinearSeries.comp, A, Finset.sum_union B, C, -Set.toFinset_ofPred,
    -add_right_inj, -Composition.single_length, -Finset.union_singleton]

中文:
定理 comp_rightInv_aux1
  结论: {n : 自然数} (hn : 0 < n) (p : FormalMultilinearSeries 𝕜 E F)
  证明: by
  have A :
    (Finset.univ : Finset (Composition n)) =
      {c | 1 < Composition.length c}.toFinset union {Composition.single n hn} := by
    refine Subset.antisymm (fun c _ => ?_) (subset_univ _)
    by_cases h : 1 < c.length
    · simp [h]
    · have : c.length = 1 := by
        refine (eq_iff_le_not_lt.2 ⟨?_, h⟩).symm; exact c.length_pos_of_pos hn
      rw [← Composition.eq_single_iff_length hn] at this
      simp [this]
  have B :
    Disjoint ({c | 1 < Composition.length c} : Set (Composition n)).toFinset
      {Composition.single n hn} := by
    simp
  have C :
    p (Composition.single n hn).length (q.applyComposition (Composition.single n hn) v) =
      p 1 fun _ : Fin 1 => q n v := by
    apply p.congr (Composition.single_length hn) fun j hj1 _ => ?_
    simp [applyComposition_single]
  simp [FormalMultilinearSeries.comp, A, Finset.sum_union B, C, -Set.toFinset_ofPred,
    -add_right_inj, -Composition.single_length, -Finset.union_singleton]

Depends on / 依赖: Composition, Composition.eq_single_iff_length, Composition.length, Composition.single, Disjoint, Finset, Finset.univ, Subset, Subset.antisymm, antisymm, c.length, c.length_pos_of_pos, eq_iff_le_not_lt, eq_single_iff_length, length, length_pos_of_pos, single, subset_univ, toFinset
-/
theorem comp_rightInv_aux1 {n : Nat} (hn : 0 < n) (p : FormalMultilinearSeries 𝕜 E F)
    (q : FormalMultilinearSeries 𝕜 F E) (v : Fin n -> F) :
    p.comp q n v =
      ∑ c in {c : Composition n | 1 < c.length}.toFinset,
          p c.length (q.applyComposition c v) + p 1 fun _ => q n v := by
  have A :
    (Finset.univ : Finset (Composition n)) =
      {c | 1 < Composition.length c}.toFinset union {Composition.single n hn} := by
    refine Subset.antisymm (fun c _ => ?_) (subset_univ _)
    by_cases h : 1 < c.length
    · simp [h]
    · have : c.length = 1 := by
        refine (eq_iff_le_not_lt.2 ⟨?_, h⟩).symm; exact c.length_pos_of_pos hn
      rw [← Composition.eq_single_iff_length hn] at this
      simp [this]
  have B :
    Disjoint ({c | 1 < Composition.length c} : Set (Composition n)).toFinset
      {Composition.single n hn} := by
    simp
  have C :
    p (Composition.single n hn).length (q.applyComposition (Composition.single n hn) v) =
      p 1 fun _ : Fin 1 => q n v := by
    apply p.congr (Composition.single_length hn) fun j hj1 _ => ?_
    simp [applyComposition_single]
  simp [FormalMultilinearSeries.comp, A, Finset.sum_union B, C, -Set.toFinset_ofPred,
    -add_right_inj, -Composition.single_length, -Finset.union_singleton]

/--
theorem `comp_rightInv_aux2` / 定理 `comp_rightInv_aux2`

English:
theorem comp_rightInv_aux2
  statement: (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x : E) (n : Nat)
  proof: by
  have N : 0 < n + 2 := by simp
  refine sum_congr rfl fun c hc => p.congr rfl fun j hj1 hj2 => ?_
  have : forall k, c.blocksFun k < n + 2 := by
    simp only [Set.mem_toFinset (s := {c : Composition (n + 2) | 1 < c.length}),
      Set.mem_ofPred_eq] at hc
    simp [← Composition.ne_single_iff N, Composition.eq_single_iff_length, ne_of_gt hc]
  simp [applyComposition, this]

中文:
定理 comp_rightInv_aux2
  结论: (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x : E) (n : 自然数)
  证明: by
  have N : 0 < n + 2 := by simp
  refine sum_congr rfl fun c hc => p.congr rfl fun j hj1 hj2 => ?_
  have : forall k, c.blocksFun k < n + 2 := by
    simp only [Set.mem_toFinset (s := {c : Composition (n + 2) | 1 < c.length}),
      Set.mem_ofPred_eq] at hc
    simp [← Composition.ne_single_iff N, Composition.eq_single_iff_length, ne_of_gt hc]
  simp [applyComposition, this]

Depends on / 依赖: Composition, Composition.eq_single_iff_length, Composition.ne_single_iff, Set.mem_ofPred_eq, Set.mem_toFinset, applyComposition, blocksFun, c.blocksFun, c.length, eq_single_iff_length, length, mem_ofPred_eq, mem_toFinset, ne_of_gt, ne_single_iff, p.congr, sum_congr
-/
theorem comp_rightInv_aux2 (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x : E) (n : Nat)
    (v : Fin (n + 2) -> F) :
    ∑ c in {c : Composition (n + 2) | 1 < c.length}.toFinset,
        p c.length (applyComposition (fun k : Nat => ite (k < n + 2) (p.rightInv i x k) 0) c v) =
      ∑ c in {c : Composition (n + 2) | 1 < c.length}.toFinset,
        p c.length ((p.rightInv i x).applyComposition c v) := by
  have N : 0 < n + 2 := by simp
  refine sum_congr rfl fun c hc => p.congr rfl fun j hj1 hj2 => ?_
  have : forall k, c.blocksFun k < n + 2 := by
    simp only [Set.mem_toFinset (s := {c : Composition (n + 2) | 1 < c.length}),
      Set.mem_ofPred_eq] at hc
    simp [← Composition.ne_single_iff N, Composition.eq_single_iff_length, ne_of_gt hc]
  simp [applyComposition, this]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `comp_rightInv` / 定理 `comp_rightInv`

English:
theorem comp_rightInv
  statement: (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x : E)
  proof: by
  ext (n v)
  match n with
  | 0 =>
    simp only [comp_coeff_zero', Matrix.zero_empty, id_apply_zero]
    congr
    ext i
    exact i.elim0
  | 1 =>
    simp only [comp_coeff_one, h, rightInv_coeff_one, ContinuousLinearEquiv.apply_symm_apply,
      id_apply_one, ContinuousLinearEquiv.coe_apply, continuousMultilinearCurryFin1_symm_apply]
  | n + 2 =>
    have N : 0 < n + 2 := by simp
    simp [comp_rightInv_aux1 N, h, rightInv, comp_rightInv_aux2, -Set.toFinset_ofPred]

中文:
定理 comp_rightInv
  结论: (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x : E)
  证明: by
  ext (n v)
  match n with
  | 0 =>
    simp only [comp_coeff_zero', Matrix.zero_empty, id_apply_zero]
    congr
    ext i
    exact i.elim0
  | 1 =>
    simp only [comp_coeff_one, h, rightInv_coeff_one, ContinuousLinearEquiv.apply_symm_apply,
      id_apply_one, ContinuousLinearEquiv.coe_apply, continuousMultilinearCurryFin1_symm_apply]
  | n + 2 =>
    have N : 0 < n + 2 := by simp
    simp [comp_rightInv_aux1 N, h, rightInv, comp_rightInv_aux2, -Set.toFinset_ofPred]

Depends on / 依赖: ContinuousLinearEquiv, ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.coe_apply, Matrix, Matrix.zero_empty, Set.toFinset_ofPred, apply_symm_apply, coe_apply, comp_coeff_one, comp_coeff_zero, comp_rightInv_aux1, comp_rightInv_aux2, continuousMultilinearCurryFin1_symm_apply, i.elim0, id_apply_one, id_apply_zero, rightInv, rightInv_coeff_one, toFinset_ofPred, zero_empty
-/
theorem comp_rightInv (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x : E)
    (h : p 1 = (continuousMultilinearCurryFin1 𝕜 E F).symm i) :
    p.comp (rightInv p i x) = id 𝕜 F (p 0 0) := by
  ext (n v)
  match n with
  | 0 =>
    simp only [comp_coeff_zero', Matrix.zero_empty, id_apply_zero]
    congr
    ext i
    exact i.elim0
  | 1 =>
    simp only [comp_coeff_one, h, rightInv_coeff_one, ContinuousLinearEquiv.apply_symm_apply,
      id_apply_one, ContinuousLinearEquiv.coe_apply, continuousMultilinearCurryFin1_symm_apply]
  | n + 2 =>
    have N : 0 < n + 2 := by simp
    simp [comp_rightInv_aux1 N, h, rightInv, comp_rightInv_aux2, -Set.toFinset_ofPred]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `rightInv_coeff` / 定理 `rightInv_coeff`

English:
theorem rightInv_coeff
  statement: (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x : E)
  proof: by
  match n with
  | 0 => exact False.elim (zero_lt_two.not_ge hn)
  | 1 => exact False.elim (one_lt_two.not_ge hn)
  | n + 2 =>
    simp only [rightInv, neg_inj]
    congr (config := { closePost := false }) 1
    ext v
    have N : 0 < n + 2 := by simp
    have : ((p 1) fun _ : Fin 1 => 0) = 0 := ContinuousMultilinearMap.map_zero _
    simp [comp_rightInv_aux1 N, this, comp_rightInv_aux2, -Set.toFinset_ofPred]

中文:
定理 rightInv_coeff
  结论: (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x : E)
  证明: by
  match n with
  | 0 => exact False.elim (zero_lt_two.not_ge hn)
  | 1 => exact False.elim (one_lt_two.not_ge hn)
  | n + 2 =>
    simp only [rightInv, neg_inj]
    congr (config := { closePost := false }) 1
    ext v
    have N : 0 < n + 2 := by simp
    have : ((p 1) fun _ : Fin 1 => 0) = 0 := ContinuousMultilinearMap.map_zero _
    simp [comp_rightInv_aux1 N, this, comp_rightInv_aux2, -Set.toFinset_ofPred]

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.map_zero, False.elim, Set.toFinset_ofPred, closePost, comp_rightInv_aux1, comp_rightInv_aux2, config, map_zero, neg_inj, not_ge, one_lt_two, one_lt_two.not_ge, rightInv, toFinset_ofPred, zero_lt_two, zero_lt_two.not_ge
-/
theorem rightInv_coeff (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x : E)
    (n : Nat) (hn : 2 <= n) :
    p.rightInv i x n =
      -(i.symm : F ->L[𝕜] E).compContinuousMultilinearMap
          (∑ c in ({c | 1 < Composition.length c}.toFinset : Finset (Composition n)),
            p.compAlongComposition (p.rightInv i x) c) := by
  match n with
  | 0 => exact False.elim (zero_lt_two.not_ge hn)
  | 1 => exact False.elim (one_lt_two.not_ge hn)
  | n + 2 =>
    simp only [rightInv, neg_inj]
    congr (config := { closePost := false }) 1
    ext v
    have N : 0 < n + 2 := by simp
    have : ((p 1) fun _ : Fin 1 => 0) = 0 := ContinuousMultilinearMap.map_zero _
    simp [comp_rightInv_aux1 N, this, comp_rightInv_aux2, -Set.toFinset_ofPred]



/--
theorem `leftInv_eq_rightInv` / 定理 `leftInv_eq_rightInv`

English:
theorem leftInv_eq_rightInv
  statement: (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x : E)
  proof: calc
    leftInv p i x = (leftInv p i x).comp (id 𝕜 F (p 0 0)) := by simp
    _ = (leftInv p i x).comp (p.comp (rightInv p i x)) := by rw [comp_rightInv p i _ h]
    _ = ((leftInv p i x).comp p).comp (rightInv p i x) := by rw [comp_assoc]
    _ = (id 𝕜 E x).comp (rightInv p i x) := by rw [leftInv_comp p i _ h]
    _ = rightInv p i x := by simp [id_comp' _ _ 0]

中文:
定理 leftInv_eq_rightInv
  结论: (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x : E)
  证明: calc
    leftInv p i x = (leftInv p i x).comp (id 𝕜 F (p 0 0)) := by simp
    _ = (leftInv p i x).comp (p.comp (rightInv p i x)) := by rw [comp_rightInv p i _ h]
    _ = ((leftInv p i x).comp p).comp (rightInv p i x) := by rw [comp_assoc]
    _ = (id 𝕜 E x).comp (rightInv p i x) := by rw [leftInv_comp p i _ h]
    _ = rightInv p i x := by simp [id_comp' _ _ 0]

Depends on / 依赖: comp_assoc, comp_rightInv, id_comp, leftInv, leftInv_comp, p.comp, rightInv
-/
theorem leftInv_eq_rightInv (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x : E)
    (h : p 1 = (continuousMultilinearCurryFin1 𝕜 E F).symm i) :
    leftInv p i x = rightInv p i x :=
  calc
    leftInv p i x = (leftInv p i x).comp (id 𝕜 F (p 0 0)) := by simp
    _ = (leftInv p i x).comp (p.comp (rightInv p i x)) := by rw [comp_rightInv p i _ h]
    _ = ((leftInv p i x).comp p).comp (rightInv p i x) := by rw [comp_assoc]
    _ = (id 𝕜 E x).comp (rightInv p i x) := by rw [leftInv_comp p i _ h]
    _ = rightInv p i x := by simp [id_comp' _ _ 0]

/-!
### Convergence of the inverse of a power series

Assume that `p` is a convergent multilinear series, and let `q` be its (left or right) inverse.
Using the left-inverse formula gives
$$
q_n = - (p_1)^{-n} \sum_{k=0}^{n-1} \sum_{i_1 + \dotsc + i_k = n} q_k (p_{i_1}, \dotsc, p_{i_k}).
$$
Assume for simplicity that we are in dimension `1` and `p₁ = 1`. In the formula for `qₙ`, the term
`q_{n-1}` appears with a multiplicity of `n-1` (choosing the index `i_j` for which `i_j = 2` while
all the other indices are equal to `1`), which indicates that `qₙ` might grow like `n!`. This is
bad for summability properties.

It turns out that the right-inverse formula is better behaved, and should instead be used for this
kind of estimate. It reads
$$
q_n = - (p_1)^{-1} \sum_{k=2}^n \sum_{i_1 + \dotsc + i_k = n} p_k (q_{i_1}, \dotsc, q_{i_k}).
$$
Here, `q_{n-1}` can only appear in the term with `k = 2`, and it only appears twice, so there is
hope this formula can lead to an at most geometric behavior.

Let `Qₙ = ‖qₙ‖`. Bounding `‖pₖ‖` with `C r^k` gives an inequality
$$
Q_n ≤ C' \sum_{k=2}^n r^k \sum_{i_1 + \dotsc + i_k = n} Q_{i_1} \dotsm Q_{i_k}.
$$

This formula is not enough to prove by naive induction on `n` a bound of the form `Qₙ ≤ D R^n`.
However, assuming that the inequality above were an equality, one could get a formula for the
generating series of the `Qₙ`:

$$
\begin{align}
Q(z) & := \sum Q_n z^n = Q_1 z + C' \sum_{2 \leq k \leq n} \sum_{i_1 + \dotsc + i_k = n}
  (r z^{i_1} Q_{i_1}) \dotsm (r z^{i_k} Q_{i_k})
\\ & = Q_1 z + C' \sum_{k = 2}^\infty (\sum_{i_1 \geq 1} r z^{i_1} Q_{i_1})
  \dotsm (\sum_{i_k \geq 1} r z^{i_k} Q_{i_k})
\\ & = Q_1 z + C' \sum_{k = 2}^\infty (r Q(z))^k
= Q_1 z + C' (r Q(z))^2 / (1 - r Q(z)).
\end{align}
$$

One can solve this formula explicitly. The solution is analytic in a neighborhood of `0` in `ℂ`,
hence its coefficients grow at most geometrically (by a contour integral argument), and therefore
the original `Qₙ`, which are bounded by these ones, are also at most geometric.

This classical argument is not really satisfactory, as it requires an a priori bound on a complex
analytic function. Another option would be to compute explicitly its terms (with binomial
coefficients) to obtain an explicit geometric bound, but this would be very painful.

Instead, we will use the above intuition, but in a slightly different form, with finite sums and an
induction. I learnt this trick in [poeschel2017siegelsternberg]. Let
$S_n = \sum_{k=1}^n Q_k a^k$ (where `a` is a positive real parameter to be chosen suitably small).
The above computation but with finite sums shows that

$$
S_n \leq Q_1 a + C' \sum_{k=2}^n (r S_{n-1})^k.
$$

In particular, $S_n \leq Q_1 a + C' (r S_{n-1})^2 / (1- r S_{n-1})$.
Assume that $S_{n-1} \leq K a$, where `K > Q₁` is fixed and `a` is small enough so that
`r K a ≤ 1/2` (to control the denominator). Then this equation gives a bound
$S_n \leq Q_1 a + 2 C' r^2 K^2 a^2$.
If `a` is small enough, this is bounded by `K a` as the second term is quadratic in `a`, and
therefore negligible.

By induction, we deduce `Sₙ ≤ K a` for all `n`, which gives in particular the fact that `aⁿ Qₙ`
remains bounded.
-/


/--
theorem `radius_right_inv_pos_of_radius_pos_aux1` / 定理 `radius_right_inv_pos_of_radius_pos_aux1`

English:
theorem radius_right_inv_pos_of_radius_pos_aux1
  statement: (n : Nat) (p : Nat -> Real) (hp : forall k, 0 <= p k) {r a : Real}
  proof: calc
    ∑ k in Ico 2 (n + 1),
          a ^ k *
            ∑ c in ({c | 1 < Composition.length c}.toFinset : Finset (Composition k)),
              r ^ c.length * ∏ j, p (c.blocksFun j) =
        ∑ k in Ico 2 (n + 1),
          ∑ c in ({c | 1 < Composition.length c}.toFinset : Finset (Composition k)),
            ∏ j, r * (a ^ c.blocksFun j * p (c.blocksFun j)) := by
      simp_rw [mul_sum]
      congr! with k _ c
      rw [prod_mul_distrib]; rw [prod_mul_distrib]; rw [prod_pow_eq_pow_sum]; rw [Composition.sum_blocksFun]; rw [prod_const]; rw [card_fin]
      ring
    _ <=
        ∑ d in compPartialSumTarget 2 (n + 1) n,
          ∏ j : Fin d.2.length, r * (a ^ d.2.blocksFun j * p (d.2.blocksFun j)) := by
      rw [sum_sigma']
      gcongr
      · intro x _ _
        exact prod_nonneg fun j _ => (by positivity [ha, hp (x.snd.blocksFun j)])
      rintro ⟨k, c⟩ hd
      simp only [Set.mem_toFinset (s := {c | 1 < Composition.length c}), mem_Ico, mem_sigma,
        Set.mem_ofPred_eq] at hd
      simp only [mem_compPartialSumTarget_iff]
      refine ⟨hd.2, c.length_le.trans_lt hd.1.2, fun j => ?_⟩
      have : c != Composition.single k (zero_lt_two.trans_le hd.1.1) := by
        simp [Composition.eq_single_iff_length, ne_of_gt hd.2]
      rw [Composition.ne_single_iff] at this
      exact (this j).trans_le (Nat.lt_succ_iff.mp hd.1.2)
    _ = ∑ e in compPartialSumSource 2 (n + 1) n, ∏ j : Fin e.1, r * (a ^ e.2 j * p (e.2 j)) := by
      symm
      apply compChangeOfVariables_sum
      rintro ⟨k, blocksFun⟩ H
      have K : (compChangeOfVariables 2 (n + 1) n ⟨k, blocksFun⟩ H).snd.length = k := by simp
      congr 2 <;> try rw [K]
      rw [Fin.heq_fun_iff K.symm]
      intro j
      rw [compChangeOfVariables_blocksFun]
    _ = ∑ j in Ico 2 (n + 1), r ^ j * (∑ k in Ico 1 n, a ^ k * p k) ^ j := by
      rw [compPartialSumSource]; rw [← sum_sigma' (Ico 2 (n + 1))
          (fun k : Nat => (Fintype.piFinset fun _ : Fin k => Ico 1 n : Finset (Fin k -> Nat)))
          (fun n e => ∏ j : Fin n]; rw [r * (a ^ e j * p (e j)))]
      congr! with j
      simp only [← @MultilinearMap.mkPiAlgebra_apply Real (Fin j) _ Real]
      simp only [←
        MultilinearMap.map_sum_finset (MultilinearMap.mkPiAlgebra Real (Fin j) Real) fun _ (m : Nat) =>
          r * (a ^ m * p m)]
      simp only [MultilinearMap.mkPiAlgebra_apply]
      simp [prod_const, ← mul_sum, mul_pow]

中文:
定理 radius_right_inv_pos_of_radius_pos_aux1
  结论: (n : 自然数) (p : 自然数 -> 实数) (hp : 对任意 k, 0 <= p k) {r a : 实数}
  证明: calc
    ∑ k in Ico 2 (n + 1),
          a ^ k *
            ∑ c in ({c | 1 < Composition.length c}.toFinset : Finset (Composition k)),
              r ^ c.length * ∏ j, p (c.blocksFun j) =
        ∑ k in Ico 2 (n + 1),
          ∑ c in ({c | 1 < Composition.length c}.toFinset : Finset (Composition k)),
            ∏ j, r * (a ^ c.blocksFun j * p (c.blocksFun j)) := by
      simp_rw [mul_sum]
      congr! with k _ c
      rw [prod_mul_distrib]; rw [prod_mul_distrib]; rw [prod_pow_eq_pow_sum]; rw [Composition.sum_blocksFun]; rw [prod_const]; rw [card_fin]
      ring
    _ <=
        ∑ d in compPartialSumTarget 2 (n + 1) n,
          ∏ j : Fin d.2.length, r * (a ^ d.2.blocksFun j * p (d.2.blocksFun j)) := by
      rw [sum_sigma']
      gcongr
      · intro x _ _
        exact prod_nonneg fun j _ => (by positivity [ha, hp (x.snd.blocksFun j)])
      rintro ⟨k, c⟩ hd
      simp only [Set.mem_toFinset (s := {c | 1 < Composition.length c}), mem_Ico, mem_sigma,
        Set.mem_ofPred_eq] at hd
      simp only [mem_compPartialSumTarget_iff]
      refine ⟨hd.2, c.length_le.trans_lt hd.1.2, fun j => ?_⟩
      have : c != Composition.single k (zero_lt_two.trans_le hd.1.1) := by
        simp [Composition.eq_single_iff_length, ne_of_gt hd.2]
      rw [Composition.ne_single_iff] at this
      exact (this j).trans_le (Nat.lt_succ_iff.mp hd.1.2)
    _ = ∑ e in compPartialSumSource 2 (n + 1) n, ∏ j : Fin e.1, r * (a ^ e.2 j * p (e.2 j)) := by
      symm
      apply compChangeOfVariables_sum
      rintro ⟨k, blocksFun⟩ H
      have K : (compChangeOfVariables 2 (n + 1) n ⟨k, blocksFun⟩ H).snd.length = k := by simp
      congr 2 <;> try rw [K]
      rw [Fin.heq_fun_iff K.symm]
      intro j
      rw [compChangeOfVariables_blocksFun]
    _ = ∑ j in Ico 2 (n + 1), r ^ j * (∑ k in Ico 1 n, a ^ k * p k) ^ j := by
      rw [compPartialSumSource]; rw [← sum_sigma' (Ico 2 (n + 1))
          (fun k : Nat => (Fintype.piFinset fun _ : Fin k => Ico 1 n : Finset (Fin k -> Nat)))
          (fun n e => ∏ j : Fin n]; rw [r * (a ^ e j * p (e j)))]
      congr! with j
      simp only [← @MultilinearMap.mkPiAlgebra_apply Real (Fin j) _ Real]
      simp only [←
        MultilinearMap.map_sum_finset (MultilinearMap.mkPiAlgebra Real (Fin j) Real) fun _ (m : Nat) =>
          r * (a ^ m * p m)]
      simp only [MultilinearMap.mkPiAlgebra_apply]
      simp [prod_const, ← mul_sum, mul_pow]

Depends on / 依赖: Composition, Composition.length, Composition.sum_blocksFun, Finset, blocksFun, c.blocksFun, c.length, card_fin, compPartia, length, mul_sum, prod_const, prod_mul_distrib, prod_pow_eq_pow_sum, simp_rw, sum_blocksFun, toFinset
-/
theorem radius_right_inv_pos_of_radius_pos_aux1 (n : Nat) (p : Nat -> Real) (hp : forall k, 0 <= p k) {r a : Real}
    (hr : 0 <= r) (ha : 0 <= a) :
    ∑ k in Ico 2 (n + 1),
        a ^ k *
          ∑ c in ({c | 1 < Composition.length c}.toFinset : Finset (Composition k)),
            r ^ c.length * ∏ j, p (c.blocksFun j) <=
      ∑ j in Ico 2 (n + 1), r ^ j * (∑ k in Ico 1 n, a ^ k * p k) ^ j :=
  calc
    ∑ k in Ico 2 (n + 1),
          a ^ k *
            ∑ c in ({c | 1 < Composition.length c}.toFinset : Finset (Composition k)),
              r ^ c.length * ∏ j, p (c.blocksFun j) =
        ∑ k in Ico 2 (n + 1),
          ∑ c in ({c | 1 < Composition.length c}.toFinset : Finset (Composition k)),
            ∏ j, r * (a ^ c.blocksFun j * p (c.blocksFun j)) := by
      simp_rw [mul_sum]
      congr! with k _ c
      rw [prod_mul_distrib]; rw [prod_mul_distrib]; rw [prod_pow_eq_pow_sum]; rw [Composition.sum_blocksFun]; rw [prod_const]; rw [card_fin]
      ring
    _ <=
        ∑ d in compPartialSumTarget 2 (n + 1) n,
          ∏ j : Fin d.2.length, r * (a ^ d.2.blocksFun j * p (d.2.blocksFun j)) := by
      rw [sum_sigma']
      gcongr
      · intro x _ _
        exact prod_nonneg fun j _ => (by positivity [ha, hp (x.snd.blocksFun j)])
      rintro ⟨k, c⟩ hd
      simp only [Set.mem_toFinset (s := {c | 1 < Composition.length c}), mem_Ico, mem_sigma,
        Set.mem_ofPred_eq] at hd
      simp only [mem_compPartialSumTarget_iff]
      refine ⟨hd.2, c.length_le.trans_lt hd.1.2, fun j => ?_⟩
      have : c != Composition.single k (zero_lt_two.trans_le hd.1.1) := by
        simp [Composition.eq_single_iff_length, ne_of_gt hd.2]
      rw [Composition.ne_single_iff] at this
      exact (this j).trans_le (Nat.lt_succ_iff.mp hd.1.2)
    _ = ∑ e in compPartialSumSource 2 (n + 1) n, ∏ j : Fin e.1, r * (a ^ e.2 j * p (e.2 j)) := by
      symm
      apply compChangeOfVariables_sum
      rintro ⟨k, blocksFun⟩ H
      have K : (compChangeOfVariables 2 (n + 1) n ⟨k, blocksFun⟩ H).snd.length = k := by simp
      congr 2 <;> try rw [K]
      rw [Fin.heq_fun_iff K.symm]
      intro j
      rw [compChangeOfVariables_blocksFun]
    _ = ∑ j in Ico 2 (n + 1), r ^ j * (∑ k in Ico 1 n, a ^ k * p k) ^ j := by
      rw [compPartialSumSource]; rw [← sum_sigma' (Ico 2 (n + 1))
          (fun k : Nat => (Fintype.piFinset fun _ : Fin k => Ico 1 n : Finset (Fin k -> Nat)))
          (fun n e => ∏ j : Fin n]; rw [r * (a ^ e j * p (e j)))]
      congr! with j
      simp only [← @MultilinearMap.mkPiAlgebra_apply Real (Fin j) _ Real]
      simp only [←
        MultilinearMap.map_sum_finset (MultilinearMap.mkPiAlgebra Real (Fin j) Real) fun _ (m : Nat) =>
          r * (a ^ m * p m)]
      simp only [MultilinearMap.mkPiAlgebra_apply]
      simp [prod_const, ← mul_sum, mul_pow]

/--
theorem `radius_rightInv_pos_of_radius_pos_aux2` / 定理 `radius_rightInv_pos_of_radius_pos_aux2`

English:
theorem radius_rightInv_pos_of_radius_pos_aux2
  statement: {x : E} {n : Nat} (hn : 2 <= n + 1)
  proof: let I := ‖(i.symm : F ->L[𝕜] E)‖
  calc
    ∑ k in Ico 1 (n + 1), a ^ k * ‖p.rightInv i x k‖ =
        a * I + ∑ k in Ico 2 (n + 1), a ^ k * ‖p.rightInv i x k‖ := by
      simp only [I, LinearIsometryEquiv.norm_map, pow_one, rightInv_coeff_one,
        show Ico (1 : Nat) 2 = {1} from Nat.Ico_succ_singleton 1,
        sum_singleton, ← sum_Ico_consecutive _ one_le_two hn]
    _ =
        a * I +
          ∑ k in Ico 2 (n + 1),
            a ^ k *
              ‖(i.symm : F ->L[𝕜] E).compContinuousMultilinearMap
                  (∑ c in ({c | 1 < Composition.length c}.toFinset : Finset (Composition k)),
                    p.compAlongComposition (p.rightInv i x) c)‖ := by
      congr! 2 with j hj
      rw [rightInv_coeff _ _ _ _ (mem_Ico.1 hj).1]; rw [norm_neg]
    _ <=
        a * ‖(i.symm : F ->L[𝕜] E)‖ +
          ∑ k in Ico 2 (n + 1),
            a ^ k *
              (I *
                ∑ c in ({c | 1 < Composition.length c}.toFinset : Finset (Composition k)),
                  C * r ^ c.length * ∏ j, ‖p.rightInv i x (c.blocksFun j)‖) := by
      gcongr with j
      apply (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans
      gcongr
      apply (norm_sum_le _ _).trans
      gcongr
      apply (compAlongComposition_norm _ _ _).trans
      gcongr
      apply hp
    _ = I * a + I * C * ∑ k in Ico 2 (n + 1), a ^ k *
          ∑ c in ({c | 1 < Composition.length c}.toFinset : Finset (Composition k)),
            r ^ c.length * ∏ j, ‖p.rightInv i x (c.blocksFun j)‖ := by
      simp_rw [I, mul_assoc C, ← mul_sum, ← mul_assoc, mul_comm _ ‖(i.symm : F ->L[𝕜] E)‖,
        mul_assoc, ← mul_sum, ← mul_assoc, mul_comm _ C, mul_assoc, ← mul_sum]
      ring
    _ <= I * a + I * C *
        ∑ k in Ico 2 (n + 1), (r * ∑ j in Ico 1 n, a ^ j * ‖p.rightInv i x j‖) ^ k := by
      gcongr _ + _ * _ * ?_
      simp_rw [mul_pow]
      apply
        radius_right_inv_pos_of_radius_pos_aux1 n (fun k => ‖p.rightInv i x k‖)
          (fun k => norm_nonneg _) hr ha

中文:
定理 radius_rightInv_pos_of_radius_pos_aux2
  结论: {x : E} {n : 自然数} (hn : 2 <= n + 1)
  证明: let I := ‖(i.symm : F ->L[𝕜] E)‖
  calc
    ∑ k in Ico 1 (n + 1), a ^ k * ‖p.rightInv i x k‖ =
        a * I + ∑ k in Ico 2 (n + 1), a ^ k * ‖p.rightInv i x k‖ := by
      simp only [I, LinearIsometryEquiv.norm_map, pow_one, rightInv_coeff_one,
        show Ico (1 : Nat) 2 = {1} from Nat.Ico_succ_singleton 1,
        sum_singleton, ← sum_Ico_consecutive _ one_le_two hn]
    _ =
        a * I +
          ∑ k in Ico 2 (n + 1),
            a ^ k *
              ‖(i.symm : F ->L[𝕜] E).compContinuousMultilinearMap
                  (∑ c in ({c | 1 < Composition.length c}.toFinset : Finset (Composition k)),
                    p.compAlongComposition (p.rightInv i x) c)‖ := by
      congr! 2 with j hj
      rw [rightInv_coeff _ _ _ _ (mem_Ico.1 hj).1]; rw [norm_neg]
    _ <=
        a * ‖(i.symm : F ->L[𝕜] E)‖ +
          ∑ k in Ico 2 (n + 1),
            a ^ k *
              (I *
                ∑ c in ({c | 1 < Composition.length c}.toFinset : Finset (Composition k)),
                  C * r ^ c.length * ∏ j, ‖p.rightInv i x (c.blocksFun j)‖) := by
      gcongr with j
      apply (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans
      gcongr
      apply (norm_sum_le _ _).trans
      gcongr
      apply (compAlongComposition_norm _ _ _).trans
      gcongr
      apply hp
    _ = I * a + I * C * ∑ k in Ico 2 (n + 1), a ^ k *
          ∑ c in ({c | 1 < Composition.length c}.toFinset : Finset (Composition k)),
            r ^ c.length * ∏ j, ‖p.rightInv i x (c.blocksFun j)‖ := by
      simp_rw [I, mul_assoc C, ← mul_sum, ← mul_assoc, mul_comm _ ‖(i.symm : F ->L[𝕜] E)‖,
        mul_assoc, ← mul_sum, ← mul_assoc, mul_comm _ C, mul_assoc, ← mul_sum]
      ring
    _ <= I * a + I * C *
        ∑ k in Ico 2 (n + 1), (r * ∑ j in Ico 1 n, a ^ j * ‖p.rightInv i x j‖) ^ k := by
      gcongr _ + _ * _ * ?_
      simp_rw [mul_pow]
      apply
        radius_right_inv_pos_of_radius_pos_aux1 n (fun k => ‖p.rightInv i x k‖)
          (fun k => norm_nonneg _) hr ha

Depends on / 依赖: Compositio, Composition, Composition.length, Finset, Ico_succ_singleton, LinearIsometryEquiv, LinearIsometryEquiv.norm_map, Nat.Ico_succ_singleton, compContinuousMultilinearMap, i.symm, length, norm_map, one_le_two, p.rightInv, pow_one, rightInv, rightInv_coeff_one, sum_Ico_consecutive, sum_singleton, toFinset
-/
theorem radius_rightInv_pos_of_radius_pos_aux2 {x : E} {n : Nat} (hn : 2 <= n + 1)
    (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) {r a C : Real} (hr : 0 <= r) (ha : 0 <= a)
    (hC : 0 <= C) (hp : forall n, ‖p n‖ <= C * r ^ n) :
    ∑ k in Ico 1 (n + 1), a ^ k * ‖p.rightInv i x k‖ <=
      ‖(i.symm : F ->L[𝕜] E)‖ * a +
        ‖(i.symm : F ->L[𝕜] E)‖ * C *
          ∑ k in Ico 2 (n + 1), (r * ∑ j in Ico 1 n, a ^ j * ‖p.rightInv i x j‖) ^ k :=
  let I := ‖(i.symm : F ->L[𝕜] E)‖
  calc
    ∑ k in Ico 1 (n + 1), a ^ k * ‖p.rightInv i x k‖ =
        a * I + ∑ k in Ico 2 (n + 1), a ^ k * ‖p.rightInv i x k‖ := by
      simp only [I, LinearIsometryEquiv.norm_map, pow_one, rightInv_coeff_one,
        show Ico (1 : Nat) 2 = {1} from Nat.Ico_succ_singleton 1,
        sum_singleton, ← sum_Ico_consecutive _ one_le_two hn]
    _ =
        a * I +
          ∑ k in Ico 2 (n + 1),
            a ^ k *
              ‖(i.symm : F ->L[𝕜] E).compContinuousMultilinearMap
                  (∑ c in ({c | 1 < Composition.length c}.toFinset : Finset (Composition k)),
                    p.compAlongComposition (p.rightInv i x) c)‖ := by
      congr! 2 with j hj
      rw [rightInv_coeff _ _ _ _ (mem_Ico.1 hj).1]; rw [norm_neg]
    _ <=
        a * ‖(i.symm : F ->L[𝕜] E)‖ +
          ∑ k in Ico 2 (n + 1),
            a ^ k *
              (I *
                ∑ c in ({c | 1 < Composition.length c}.toFinset : Finset (Composition k)),
                  C * r ^ c.length * ∏ j, ‖p.rightInv i x (c.blocksFun j)‖) := by
      gcongr with j
      apply (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans
      gcongr
      apply (norm_sum_le _ _).trans
      gcongr
      apply (compAlongComposition_norm _ _ _).trans
      gcongr
      apply hp
    _ = I * a + I * C * ∑ k in Ico 2 (n + 1), a ^ k *
          ∑ c in ({c | 1 < Composition.length c}.toFinset : Finset (Composition k)),
            r ^ c.length * ∏ j, ‖p.rightInv i x (c.blocksFun j)‖ := by
      simp_rw [I, mul_assoc C, ← mul_sum, ← mul_assoc, mul_comm _ ‖(i.symm : F ->L[𝕜] E)‖,
        mul_assoc, ← mul_sum, ← mul_assoc, mul_comm _ C, mul_assoc, ← mul_sum]
      ring
    _ <= I * a + I * C *
        ∑ k in Ico 2 (n + 1), (r * ∑ j in Ico 1 n, a ^ j * ‖p.rightInv i x j‖) ^ k := by
      gcongr _ + _ * _ * ?_
      simp_rw [mul_pow]
      apply
        radius_right_inv_pos_of_radius_pos_aux1 n (fun k => ‖p.rightInv i x k‖)
          (fun k => norm_nonneg _) hr ha

/--
theorem `radius_rightInv_pos_of_radius_pos` / 定理 `radius_rightInv_pos_of_radius_pos`

English:
theorem radius_rightInv_pos_of_radius_pos
  proof: by
  obtain ⟨C, r, Cpos, rpos, ple⟩ :
    exists (C r : _) (_ : 0 < C) (_ : 0 < r), forall n : Nat, ‖p n‖ <= C * r ^ n :=
    le_mul_pow_of_radius_pos p hp
  let I := ‖(i.symm : F ->L[𝕜] E)‖
  -- choose `a` small enough to make sure that `∑_{k ≤ n} aᵏ Qₖ` will be controllable by
  -- induction
  obtain ⟨a, apos, ha1, ha2⟩ :
    exists (a : _) (apos : 0 < a),
      2 * I * C * r ^ 2 * (I + 1) ^ 2 * a <= 1 ∧ r * (I + 1) * a <= 1 / 2 := by
    have :
      Tendsto (fun a => 2 * I * C * r ^ 2 * (I + 1) ^ 2 * a) (𝓝 0)
        (𝓝 (2 * I * C * r ^ 2 * (I + 1) ^ 2 * 0)) :=
      tendsto_const_nhds.mul tendsto_id
    have A : forallᶠ a in 𝓝 0, 2 * I * C * r ^ 2 * (I + 1) ^ 2 * a < 1 := by
      apply (tendsto_order.1 this).2; simp [zero_lt_one]
    have : Tendsto (fun a => r * (I + 1) * a) (𝓝 0) (𝓝 (r * (I + 1) * 0)) :=
      tendsto_const_nhds.mul tendsto_id
    have B : forallᶠ a in 𝓝 0, r * (I + 1) * a < 1 / 2 := by
      apply (tendsto_order.1 this).2; simp
    have C : forallᶠ a in 𝓝[>] (0 : Real), (0 : Real) < a := by
      filter_upwards [self_mem_nhdsWithin] with _ ha using ha
    rcases (C.and ((A.and B).filter_mono inf_le_left)).exists with ⟨a, ha⟩
    exact ⟨a, ha.1, ha.2.1.le, ha.2.2.le⟩
  -- check by induction that the partial sums are suitably bounded, using the choice of `a` and the
  -- inductive control from Lemma `radius_rightInv_pos_of_radius_pos_aux2`.
  let S n := ∑ k in Ico 1 n, a ^ k * ‖p.rightInv i x k‖
  have IRec : forall n, 1 <= n -> S n <= (I + 1) * a := by
    apply Nat.le_induction
    · simp only [S]
      rw [Ico_eq_empty_of_le (le_refl 1)]; rw [sum_empty]
      positivity
    · intro n one_le_n hn
      have In : 2 <= n + 1 := by lia
      have rSn : r * S n <= 1 / 2 :=
        calc
          r * S n <= r * ((I + 1) * a) := by gcongr
          _ <= 1 / 2 := by rwa [← mul_assoc]
      calc
        S (n + 1) <= I * a + I * C * ∑ k in Ico 2 (n + 1), (r * S n) ^ k :=
          radius_rightInv_pos_of_radius_pos_aux2 In p i rpos.le apos.le Cpos.le ple
        _ = I * a + I * C * (((r * S n) ^ 2 - (r * S n) ^ (n + 1)) / (1 - r * S n)) := by
          rw [geom_sum_Ico' _ In]; exact ne_of_lt (rSn.trans_lt (by norm_num))
        _ <= I * a + I * C * ((r * S n) ^ 2 / (1 / 2)) := by
          gcongr
          · simp only [sub_le_self_iff]
            positivity
          · linarith only [rSn]
        _ = I * a + 2 * I * C * (r * S n) ^ 2 := by ring
        _ <= I * a + 2 * I * C * (r * ((I + 1) * a)) ^ 2 := by gcongr
        _ = (I + 2 * I * C * r ^ 2 * (I + 1) ^ 2 * a) * a := by ring
        _ <= (I + 1) * a := by gcongr
  -- conclude that all coefficients satisfy `aⁿ Qₙ ≤ (I + 1) a`.
  let a' : NNReal := ⟨a, apos.le⟩
  suffices H : (a' : ENNReal) <= (p.rightInv i x).radius by
    apply lt_of_lt_of_le _ H
    -- Prior to https://github.com/leanprover/lean4/pull/2734, this was `exact_mod_cast apos`.
    simpa only [ENNReal.coe_pos]
  apply le_radius_of_eventually_le _ ((I + 1) * a)
  filter_upwards [Ici_mem_atTop 1] with n (hn : 1 <= n)
  calc
    ‖p.rightInv i x n‖ * (a' : Real) ^ n = a ^ n * ‖p.rightInv i x n‖ := mul_comm _ _
    _ <= ∑ k in Ico 1 (n + 1), a ^ k * ‖p.rightInv i x k‖ :=
      (haveI : forall k in Ico 1 (n + 1), 0 <= a ^ k * ‖p.rightInv i x k‖ := fun k _ => by positivity
      single_le_sum this (by simp [hn]))
    _ <= (I + 1) * a := IRec (n + 1) (by simp)

中文:
定理 radius_rightInv_pos_of_radius_pos
  证明: by
  obtain ⟨C, r, Cpos, rpos, ple⟩ :
    exists (C r : _) (_ : 0 < C) (_ : 0 < r), forall n : Nat, ‖p n‖ <= C * r ^ n :=
    le_mul_pow_of_radius_pos p hp
  let I := ‖(i.symm : F ->L[𝕜] E)‖
  -- choose `a` small enough to make sure that `∑_{k ≤ n} aᵏ Qₖ` will be controllable by
  -- induction
  obtain ⟨a, apos, ha1, ha2⟩ :
    exists (a : _) (apos : 0 < a),
      2 * I * C * r ^ 2 * (I + 1) ^ 2 * a <= 1 ∧ r * (I + 1) * a <= 1 / 2 := by
    have :
      Tendsto (fun a => 2 * I * C * r ^ 2 * (I + 1) ^ 2 * a) (𝓝 0)
        (𝓝 (2 * I * C * r ^ 2 * (I + 1) ^ 2 * 0)) :=
      tendsto_const_nhds.mul tendsto_id
    have A : forallᶠ a in 𝓝 0, 2 * I * C * r ^ 2 * (I + 1) ^ 2 * a < 1 := by
      apply (tendsto_order.1 this).2; simp [zero_lt_one]
    have : Tendsto (fun a => r * (I + 1) * a) (𝓝 0) (𝓝 (r * (I + 1) * 0)) :=
      tendsto_const_nhds.mul tendsto_id
    have B : forallᶠ a in 𝓝 0, r * (I + 1) * a < 1 / 2 := by
      apply (tendsto_order.1 this).2; simp
    have C : forallᶠ a in 𝓝[>] (0 : Real), (0 : Real) < a := by
      filter_upwards [self_mem_nhdsWithin] with _ ha using ha
    rcases (C.and ((A.and B).filter_mono inf_le_left)).exists with ⟨a, ha⟩
    exact ⟨a, ha.1, ha.2.1.le, ha.2.2.le⟩
  -- check by induction that the partial sums are suitably bounded, using the choice of `a` and the
  -- inductive control from Lemma `radius_rightInv_pos_of_radius_pos_aux2`.
  let S n := ∑ k in Ico 1 n, a ^ k * ‖p.rightInv i x k‖
  have IRec : forall n, 1 <= n -> S n <= (I + 1) * a := by
    apply Nat.le_induction
    · simp only [S]
      rw [Ico_eq_empty_of_le (le_refl 1)]; rw [sum_empty]
      positivity
    · intro n one_le_n hn
      have In : 2 <= n + 1 := by lia
      have rSn : r * S n <= 1 / 2 :=
        calc
          r * S n <= r * ((I + 1) * a) := by gcongr
          _ <= 1 / 2 := by rwa [← mul_assoc]
      calc
        S (n + 1) <= I * a + I * C * ∑ k in Ico 2 (n + 1), (r * S n) ^ k :=
          radius_rightInv_pos_of_radius_pos_aux2 In p i rpos.le apos.le Cpos.le ple
        _ = I * a + I * C * (((r * S n) ^ 2 - (r * S n) ^ (n + 1)) / (1 - r * S n)) := by
          rw [geom_sum_Ico' _ In]; exact ne_of_lt (rSn.trans_lt (by norm_num))
        _ <= I * a + I * C * ((r * S n) ^ 2 / (1 / 2)) := by
          gcongr
          · simp only [sub_le_self_iff]
            positivity
          · linarith only [rSn]
        _ = I * a + 2 * I * C * (r * S n) ^ 2 := by ring
        _ <= I * a + 2 * I * C * (r * ((I + 1) * a)) ^ 2 := by gcongr
        _ = (I + 2 * I * C * r ^ 2 * (I + 1) ^ 2 * a) * a := by ring
        _ <= (I + 1) * a := by gcongr
  -- conclude that all coefficients satisfy `aⁿ Qₙ ≤ (I + 1) a`.
  let a' : NNReal := ⟨a, apos.le⟩
  suffices H : (a' : ENNReal) <= (p.rightInv i x).radius by
    apply lt_of_lt_of_le _ H
    -- Prior to https://github.com/leanprover/lean4/pull/2734, this was `exact_mod_cast apos`.
    simpa only [ENNReal.coe_pos]
  apply le_radius_of_eventually_le _ ((I + 1) * a)
  filter_upwards [Ici_mem_atTop 1] with n (hn : 1 <= n)
  calc
    ‖p.rightInv i x n‖ * (a' : Real) ^ n = a ^ n * ‖p.rightInv i x n‖ := mul_comm _ _
    _ <= ∑ k in Ico 1 (n + 1), a ^ k * ‖p.rightInv i x k‖ :=
      (haveI : forall k in Ico 1 (n + 1), 0 <= a ^ k * ‖p.rightInv i x k‖ := fun k _ => by positivity
      single_le_sum this (by simp [hn]))
    _ <= (I + 1) * a := IRec (n + 1) (by simp)

Depends on / 依赖: i.symm, le_mul_pow_of_radius_pos
-/
theorem radius_rightInv_pos_of_radius_pos
    {p : FormalMultilinearSeries 𝕜 E F} {i : E ≃L[𝕜] F} {x : E}
    (hp : 0 < p.radius) : 0 < (p.rightInv i x).radius := by
  obtain ⟨C, r, Cpos, rpos, ple⟩ :
    exists (C r : _) (_ : 0 < C) (_ : 0 < r), forall n : Nat, ‖p n‖ <= C * r ^ n :=
    le_mul_pow_of_radius_pos p hp
  let I := ‖(i.symm : F ->L[𝕜] E)‖
  -- choose `a` small enough to make sure that `∑_{k ≤ n} aᵏ Qₖ` will be controllable by
  -- induction
  obtain ⟨a, apos, ha1, ha2⟩ :
    exists (a : _) (apos : 0 < a),
      2 * I * C * r ^ 2 * (I + 1) ^ 2 * a <= 1 ∧ r * (I + 1) * a <= 1 / 2 := by
    have :
      Tendsto (fun a => 2 * I * C * r ^ 2 * (I + 1) ^ 2 * a) (𝓝 0)
        (𝓝 (2 * I * C * r ^ 2 * (I + 1) ^ 2 * 0)) :=
      tendsto_const_nhds.mul tendsto_id
    have A : forallᶠ a in 𝓝 0, 2 * I * C * r ^ 2 * (I + 1) ^ 2 * a < 1 := by
      apply (tendsto_order.1 this).2; simp [zero_lt_one]
    have : Tendsto (fun a => r * (I + 1) * a) (𝓝 0) (𝓝 (r * (I + 1) * 0)) :=
      tendsto_const_nhds.mul tendsto_id
    have B : forallᶠ a in 𝓝 0, r * (I + 1) * a < 1 / 2 := by
      apply (tendsto_order.1 this).2; simp
    have C : forallᶠ a in 𝓝[>] (0 : Real), (0 : Real) < a := by
      filter_upwards [self_mem_nhdsWithin] with _ ha using ha
    rcases (C.and ((A.and B).filter_mono inf_le_left)).exists with ⟨a, ha⟩
    exact ⟨a, ha.1, ha.2.1.le, ha.2.2.le⟩
  -- check by induction that the partial sums are suitably bounded, using the choice of `a` and the
  -- inductive control from Lemma `radius_rightInv_pos_of_radius_pos_aux2`.
  let S n := ∑ k in Ico 1 n, a ^ k * ‖p.rightInv i x k‖
  have IRec : forall n, 1 <= n -> S n <= (I + 1) * a := by
    apply Nat.le_induction
    · simp only [S]
      rw [Ico_eq_empty_of_le (le_refl 1)]; rw [sum_empty]
      positivity
    · intro n one_le_n hn
      have In : 2 <= n + 1 := by lia
      have rSn : r * S n <= 1 / 2 :=
        calc
          r * S n <= r * ((I + 1) * a) := by gcongr
          _ <= 1 / 2 := by rwa [← mul_assoc]
      calc
        S (n + 1) <= I * a + I * C * ∑ k in Ico 2 (n + 1), (r * S n) ^ k :=
          radius_rightInv_pos_of_radius_pos_aux2 In p i rpos.le apos.le Cpos.le ple
        _ = I * a + I * C * (((r * S n) ^ 2 - (r * S n) ^ (n + 1)) / (1 - r * S n)) := by
          rw [geom_sum_Ico' _ In]; exact ne_of_lt (rSn.trans_lt (by norm_num))
        _ <= I * a + I * C * ((r * S n) ^ 2 / (1 / 2)) := by
          gcongr
          · simp only [sub_le_self_iff]
            positivity
          · linarith only [rSn]
        _ = I * a + 2 * I * C * (r * S n) ^ 2 := by ring
        _ <= I * a + 2 * I * C * (r * ((I + 1) * a)) ^ 2 := by gcongr
        _ = (I + 2 * I * C * r ^ 2 * (I + 1) ^ 2 * a) * a := by ring
        _ <= (I + 1) * a := by gcongr
  -- conclude that all coefficients satisfy `aⁿ Qₙ ≤ (I + 1) a`.
  let a' : NNReal := ⟨a, apos.le⟩
  suffices H : (a' : ENNReal) <= (p.rightInv i x).radius by
    apply lt_of_lt_of_le _ H
    -- Prior to https://github.com/leanprover/lean4/pull/2734, this was `exact_mod_cast apos`.
    simpa only [ENNReal.coe_pos]
  apply le_radius_of_eventually_le _ ((I + 1) * a)
  filter_upwards [Ici_mem_atTop 1] with n (hn : 1 <= n)
  calc
    ‖p.rightInv i x n‖ * (a' : Real) ^ n = a ^ n * ‖p.rightInv i x n‖ := mul_comm _ _
    _ <= ∑ k in Ico 1 (n + 1), a ^ k * ‖p.rightInv i x k‖ :=
      (haveI : forall k in Ico 1 (n + 1), 0 <= a ^ k * ‖p.rightInv i x k‖ := fun k _ => by positivity
      single_le_sum this (by simp [hn]))
    _ <= (I + 1) * a := IRec (n + 1) (by simp)

/--
theorem `radius_leftInv_pos_of_radius_pos` / 定理 `radius_leftInv_pos_of_radius_pos`

English:
theorem radius_leftInv_pos_of_radius_pos
  proof: by
  rw [leftInv_eq_rightInv _ _ _ h]
  exact radius_rightInv_pos_of_radius_pos hp

中文:
定理 radius_leftInv_pos_of_radius_pos
  证明: by
  rw [leftInv_eq_rightInv _ _ _ h]
  exact radius_rightInv_pos_of_radius_pos hp

Depends on / 依赖: leftInv_eq_rightInv, radius_rightInv_pos_of_radius_pos
-/
theorem radius_leftInv_pos_of_radius_pos
    {p : FormalMultilinearSeries 𝕜 E F} {i : E ≃L[𝕜] F} {x : E}
    (hp : 0 < p.radius) (h : p 1 = (continuousMultilinearCurryFin1 𝕜 E F).symm i) :
    0 < (p.leftInv i x).radius := by
  rw [leftInv_eq_rightInv _ _ _ h]
  exact radius_rightInv_pos_of_radius_pos hp

end FormalMultilinearSeries

/-!
### The inverse of an analytic open partial homeomorphism is analytic
-/

open FormalMultilinearSeries List

/--
lemma `HasFPowerSeriesAt.tendsto_partialSum_prod_of_comp` / 引理 `HasFPowerSeriesAt.tendsto_partialSum_prod_of_comp`

English:
lemma HasFPowerSeriesAt.tendsto_partialSum_prod_of_comp
  proof: by
  rcases hf with ⟨r0, h0⟩
  rcases q.comp_summable_nnreal p hq hp with ⟨r1, r1_pos : 0 < r1, hr1⟩
  let r : Real>=0∞ := min r0 r1
  have : Metric.eball (0 : E) r in 𝓝 0 :=
    Metric.eball_mem_nhds 0 (lt_min h0.r_pos (by exact_mod_cast r1_pos))
  filter_upwards [this] with y hy
  have hy0 : y in Metric.eball 0 r0 := Metric.eball_subset_eball (min_le_left _ _) hy
  have A : HasSum (fun i : Σ n, Composition n => q.compAlongComposition p i.2 fun _j => y)
      (f (x + y)) := by
    have cau : CauchySeq fun s : Finset (Σ n, Composition n) =>
        ∑ i in s, q.compAlongComposition p i.2 fun _j => y := by
      apply cauchySeq_finset_of_norm_bounded (NNReal.summable_coe.2 hr1) _
      simp only [coe_nnnorm, NNReal.coe_mul, NNReal.coe_pow]
      rintro ⟨n, c⟩
      calc
        ‖(compAlongComposition q p c) fun _j : Fin n => y‖ <=
            ‖compAlongComposition q p c‖ * ∏ _j : Fin n, ‖y‖ := by
          apply ContinuousMultilinearMap.le_opNorm
        _ <= ‖compAlongComposition q p c‖ * (r1 : Real) ^ n := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          rw [Finset.prod_const]; rw [Finset.card_fin]
          gcongr
          rw [Metric.mem_eball]; rw [edist_zero_right] at hy
          have := le_trans (le_of_lt hy) (min_le_right _ _)
          rwa [enorm_le_coe, ← NNReal.coe_le_coe, coe_nnnorm] at this
    apply HasSum.of_sigma (fun b => hasSum_fintype _) ?_ cau
    simpa [FormalMultilinearSeries.comp] using h0.hasSum hy0
  have B : Tendsto (fun (n : Nat × Nat) => ∑ i in compPartialSumTarget 0 n.1 n.2,
      q.compAlongComposition p i.2 fun _j => y) atTop (𝓝 (f (x + y))) := by
    apply Tendsto.comp A compPartialSumTarget_tendsto_prod_atTop
  have C : Tendsto (fun (n : Nat × Nat) => q.partialSum n.1 (∑ a in Finset.Ico 1 n.2, p a fun _b => y))
      atTop (𝓝 (f (x + y))) := by simpa [comp_partialSum] using B
  apply C.congr'
  filter_upwards [Ici_mem_atTop (0, 1)]
  rintro ⟨-, n⟩ ⟨-, (hn : 1 <= n)⟩
  congr
  rw [partialSum]; rw [eq_sub_iff_add_eq']; rw [Finset.range_eq_Ico]; rw [Finset.sum_eq_sum_Ico_succ_bot hn]
  congr with i
  exact i.elim0

中文:
引理 HasFPowerSeriesAt.tendsto_partialSum_prod_of_comp
  证明: by
  rcases hf with ⟨r0, h0⟩
  rcases q.comp_summable_nnreal p hq hp with ⟨r1, r1_pos : 0 < r1, hr1⟩
  let r : Real>=0∞ := min r0 r1
  have : Metric.eball (0 : E) r in 𝓝 0 :=
    Metric.eball_mem_nhds 0 (lt_min h0.r_pos (by exact_mod_cast r1_pos))
  filter_upwards [this] with y hy
  have hy0 : y in Metric.eball 0 r0 := Metric.eball_subset_eball (min_le_left _ _) hy
  have A : HasSum (fun i : Σ n, Composition n => q.compAlongComposition p i.2 fun _j => y)
      (f (x + y)) := by
    have cau : CauchySeq fun s : Finset (Σ n, Composition n) =>
        ∑ i in s, q.compAlongComposition p i.2 fun _j => y := by
      apply cauchySeq_finset_of_norm_bounded (NNReal.summable_coe.2 hr1) _
      simp only [coe_nnnorm, NNReal.coe_mul, NNReal.coe_pow]
      rintro ⟨n, c⟩
      calc
        ‖(compAlongComposition q p c) fun _j : Fin n => y‖ <=
            ‖compAlongComposition q p c‖ * ∏ _j : Fin n, ‖y‖ := by
          apply ContinuousMultilinearMap.le_opNorm
        _ <= ‖compAlongComposition q p c‖ * (r1 : Real) ^ n := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          rw [Finset.prod_const]; rw [Finset.card_fin]
          gcongr
          rw [Metric.mem_eball]; rw [edist_zero_right] at hy
          have := le_trans (le_of_lt hy) (min_le_right _ _)
          rwa [enorm_le_coe, ← NNReal.coe_le_coe, coe_nnnorm] at this
    apply HasSum.of_sigma (fun b => hasSum_fintype _) ?_ cau
    simpa [FormalMultilinearSeries.comp] using h0.hasSum hy0
  have B : Tendsto (fun (n : Nat × Nat) => ∑ i in compPartialSumTarget 0 n.1 n.2,
      q.compAlongComposition p i.2 fun _j => y) atTop (𝓝 (f (x + y))) := by
    apply Tendsto.comp A compPartialSumTarget_tendsto_prod_atTop
  have C : Tendsto (fun (n : Nat × Nat) => q.partialSum n.1 (∑ a in Finset.Ico 1 n.2, p a fun _b => y))
      atTop (𝓝 (f (x + y))) := by simpa [comp_partialSum] using B
  apply C.congr'
  filter_upwards [Ici_mem_atTop (0, 1)]
  rintro ⟨-, n⟩ ⟨-, (hn : 1 <= n)⟩
  congr
  rw [partialSum]; rw [eq_sub_iff_add_eq']; rw [Finset.range_eq_Ico]; rw [Finset.sum_eq_sum_Ico_succ_bot hn]
  congr with i
  exact i.elim0

Depends on / 依赖: CauchySeq, Composition, Finset, HasSum, Metric, Metric.eball, Metric.eball_mem_nhds, Metric.eball_subset_eball, compAlongComposition, comp_summable_nnreal, eball_mem_nhds, eball_subset_eball, filter_upwards, h0.r_pos, lt_min, min_le_left, q.compAlongComposition, q.comp_summable_nnreal, r1_pos, r_pos
-/
lemma HasFPowerSeriesAt.tendsto_partialSum_prod_of_comp
    {f : E -> G} {q : FormalMultilinearSeries 𝕜 F G}
    {p : FormalMultilinearSeries 𝕜 E F} {x : E}
    (hf : HasFPowerSeriesAt f (q.comp p) x) (hq : 0 < q.radius) (hp : 0 < p.radius) :
    forallᶠ y in 𝓝 0, Tendsto (fun (a : Nat × Nat) => q.partialSum a.1 (p.partialSum a.2 y
      - p 0 (fun _ => 0))) atTop (𝓝 (f (x + y))) := by
  rcases hf with ⟨r0, h0⟩
  rcases q.comp_summable_nnreal p hq hp with ⟨r1, r1_pos : 0 < r1, hr1⟩
  let r : Real>=0∞ := min r0 r1
  have : Metric.eball (0 : E) r in 𝓝 0 :=
    Metric.eball_mem_nhds 0 (lt_min h0.r_pos (by exact_mod_cast r1_pos))
  filter_upwards [this] with y hy
  have hy0 : y in Metric.eball 0 r0 := Metric.eball_subset_eball (min_le_left _ _) hy
  have A : HasSum (fun i : Σ n, Composition n => q.compAlongComposition p i.2 fun _j => y)
      (f (x + y)) := by
    have cau : CauchySeq fun s : Finset (Σ n, Composition n) =>
        ∑ i in s, q.compAlongComposition p i.2 fun _j => y := by
      apply cauchySeq_finset_of_norm_bounded (NNReal.summable_coe.2 hr1) _
      simp only [coe_nnnorm, NNReal.coe_mul, NNReal.coe_pow]
      rintro ⟨n, c⟩
      calc
        ‖(compAlongComposition q p c) fun _j : Fin n => y‖ <=
            ‖compAlongComposition q p c‖ * ∏ _j : Fin n, ‖y‖ := by
          apply ContinuousMultilinearMap.le_opNorm
        _ <= ‖compAlongComposition q p c‖ * (r1 : Real) ^ n := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          rw [Finset.prod_const]; rw [Finset.card_fin]
          gcongr
          rw [Metric.mem_eball]; rw [edist_zero_right] at hy
          have := le_trans (le_of_lt hy) (min_le_right _ _)
          rwa [enorm_le_coe, ← NNReal.coe_le_coe, coe_nnnorm] at this
    apply HasSum.of_sigma (fun b => hasSum_fintype _) ?_ cau
    simpa [FormalMultilinearSeries.comp] using h0.hasSum hy0
  have B : Tendsto (fun (n : Nat × Nat) => ∑ i in compPartialSumTarget 0 n.1 n.2,
      q.compAlongComposition p i.2 fun _j => y) atTop (𝓝 (f (x + y))) := by
    apply Tendsto.comp A compPartialSumTarget_tendsto_prod_atTop
  have C : Tendsto (fun (n : Nat × Nat) => q.partialSum n.1 (∑ a in Finset.Ico 1 n.2, p a fun _b => y))
      atTop (𝓝 (f (x + y))) := by simpa [comp_partialSum] using B
  apply C.congr'
  filter_upwards [Ici_mem_atTop (0, 1)]
  rintro ⟨-, n⟩ ⟨-, (hn : 1 <= n)⟩
  congr
  rw [partialSum]; rw [eq_sub_iff_add_eq']; rw [Finset.range_eq_Ico]; rw [Finset.sum_eq_sum_Ico_succ_bot hn]
  congr with i
  exact i.elim0

/--
lemma `HasFPowerSeriesAt.eventually_hasSum_of_comp` / 引理 `HasFPowerSeriesAt.eventually_hasSum_of_comp`

English:
lemma HasFPowerSeriesAt.eventually_hasSum_of_comp
  statement: {f : E -> F} {g : F -> G}
  proof: by
  have : forallᶠ y in 𝓝 (0 : E), f (x + y) - f x in Metric.eball 0 q.radius := by
    have A : ContinuousAt (fun y => f (x + y) - f x) 0 := by
      apply ContinuousAt.sub _ continuousAt_const
      exact hf.continuousAt.comp_of_eq (by fun_prop) (by simp)
    have B : Metric.eball 0 q.radius in 𝓝 (f (x + 0) - f x) := by
      simpa using Metric.eball_mem_nhds _ hq
    exact A.preimage_mem_nhds B
  filter_upwards [hgf.tendsto_partialSum_prod_of_comp hq (hf.radius_pos),
    hf.tendsto_partialSum, this] with y hy h'y h''y
  have L : Tendsto (fun n => q.partialSum n (f (x + y) - f x)) atTop (𝓝 (g (f (x + y)))) := by
    apply (closed_nhds_basis (g (f (x + y)))).tendsto_right_iff.2
    rintro u ⟨hu, u_closed⟩
    simp only [id_eq, eventually_atTop]
    rcases mem_nhds_iff.1 hu with ⟨v, vu, v_open, hv⟩
    obtain ⟨a₀, b₀, hab⟩ : exists a₀ b₀, forall (a b : Nat), a₀ <= a -> b₀ <= b ->
        q.partialSum a (p.partialSum b y - (p 0) fun _ => 0) in v := by
      simpa using hy (v_open.mem_nhds hv)
    refine ⟨a₀, fun a ha => ?_⟩
    have : Tendsto (fun b => q.partialSum a (p.partialSum b y - (p 0) fun _ => 0)) atTop
        (𝓝 (q.partialSum a (f (x + y) - f x))) := by
      have : ContinuousAt (q.partialSum a) (f (x + y) - f x) :=
        (partialSum_continuous q a).continuousAt
      apply this.tendsto.comp
      apply Tendsto.sub h'y
      convert! tendsto_const_nhds
      exact (HasFPowerSeriesAt.coeff_zero hf fun _ => 0).symm
    apply u_closed.mem_of_tendsto this
    filter_upwards [Ici_mem_atTop b₀] with b hb using vu (hab _ _ ha hb)
  have C : CauchySeq (fun (s : Finset Nat) => ∑ n in s, q n fun _ : Fin n => (f (x + y) - f x)) := by
    have Z := q.summable_norm_apply (x := f (x + y) - f x) h''y
    exact cauchySeq_finset_of_norm_bounded Z (fun i => le_rfl)
  exact tendsto_nhds_of_cauchySeq_of_subseq C tendsto_finset_range L

中文:
引理 HasFPowerSeriesAt.eventually_hasSum_of_comp
  结论: {f : E -> F} {g : F -> G}
  证明: by
  have : forallᶠ y in 𝓝 (0 : E), f (x + y) - f x in Metric.eball 0 q.radius := by
    have A : ContinuousAt (fun y => f (x + y) - f x) 0 := by
      apply ContinuousAt.sub _ continuousAt_const
      exact hf.continuousAt.comp_of_eq (by fun_prop) (by simp)
    have B : Metric.eball 0 q.radius in 𝓝 (f (x + 0) - f x) := by
      simpa using Metric.eball_mem_nhds _ hq
    exact A.preimage_mem_nhds B
  filter_upwards [hgf.tendsto_partialSum_prod_of_comp hq (hf.radius_pos),
    hf.tendsto_partialSum, this] with y hy h'y h''y
  have L : Tendsto (fun n => q.partialSum n (f (x + y) - f x)) atTop (𝓝 (g (f (x + y)))) := by
    apply (closed_nhds_basis (g (f (x + y)))).tendsto_right_iff.2
    rintro u ⟨hu, u_closed⟩
    simp only [id_eq, eventually_atTop]
    rcases mem_nhds_iff.1 hu with ⟨v, vu, v_open, hv⟩
    obtain ⟨a₀, b₀, hab⟩ : exists a₀ b₀, forall (a b : Nat), a₀ <= a -> b₀ <= b ->
        q.partialSum a (p.partialSum b y - (p 0) fun _ => 0) in v := by
      simpa using hy (v_open.mem_nhds hv)
    refine ⟨a₀, fun a ha => ?_⟩
    have : Tendsto (fun b => q.partialSum a (p.partialSum b y - (p 0) fun _ => 0)) atTop
        (𝓝 (q.partialSum a (f (x + y) - f x))) := by
      have : ContinuousAt (q.partialSum a) (f (x + y) - f x) :=
        (partialSum_continuous q a).continuousAt
      apply this.tendsto.comp
      apply Tendsto.sub h'y
      convert! tendsto_const_nhds
      exact (HasFPowerSeriesAt.coeff_zero hf fun _ => 0).symm
    apply u_closed.mem_of_tendsto this
    filter_upwards [Ici_mem_atTop b₀] with b hb using vu (hab _ _ ha hb)
  have C : CauchySeq (fun (s : Finset Nat) => ∑ n in s, q n fun _ : Fin n => (f (x + y) - f x)) := by
    have Z := q.summable_norm_apply (x := f (x + y) - f x) h''y
    exact cauchySeq_finset_of_norm_bounded Z (fun i => le_rfl)
  exact tendsto_nhds_of_cauchySeq_of_subseq C tendsto_finset_range L

Depends on / 依赖: A.preimage_mem_nhds, ContinuousAt, ContinuousAt.sub, Metric, Metric.eball, Metric.eball_mem_nhds, comp_of_eq, continuousAt, continuousAt_const, eball_mem_nhds, filter_upwards, fun_prop, hf.continuousAt.comp_of_eq, hf.radius_pos, hf.tendsto_partialSum, hgf.tendsto_partialSum_prod_of_comp, preimage_mem_nhds, q.radius, radius, radius_pos
-/
lemma HasFPowerSeriesAt.eventually_hasSum_of_comp {f : E -> F} {g : F -> G}
    {q : FormalMultilinearSeries 𝕜 F G} {p : FormalMultilinearSeries 𝕜 E F} {x : E}
    (hgf : HasFPowerSeriesAt (g ∘ f) (q.comp p) x) (hf : HasFPowerSeriesAt f p x)
    (hq : 0 < q.radius) :
    forallᶠ y in 𝓝 0, HasSum (fun n : Nat => q n fun _ : Fin n => (f (x + y) - f x)) (g (f (x + y))) := by
  have : forallᶠ y in 𝓝 (0 : E), f (x + y) - f x in Metric.eball 0 q.radius := by
    have A : ContinuousAt (fun y => f (x + y) - f x) 0 := by
      apply ContinuousAt.sub _ continuousAt_const
      exact hf.continuousAt.comp_of_eq (by fun_prop) (by simp)
    have B : Metric.eball 0 q.radius in 𝓝 (f (x + 0) - f x) := by
      simpa using Metric.eball_mem_nhds _ hq
    exact A.preimage_mem_nhds B
  filter_upwards [hgf.tendsto_partialSum_prod_of_comp hq (hf.radius_pos),
    hf.tendsto_partialSum, this] with y hy h'y h''y
  have L : Tendsto (fun n => q.partialSum n (f (x + y) - f x)) atTop (𝓝 (g (f (x + y)))) := by
    apply (closed_nhds_basis (g (f (x + y)))).tendsto_right_iff.2
    rintro u ⟨hu, u_closed⟩
    simp only [id_eq, eventually_atTop]
    rcases mem_nhds_iff.1 hu with ⟨v, vu, v_open, hv⟩
    obtain ⟨a₀, b₀, hab⟩ : exists a₀ b₀, forall (a b : Nat), a₀ <= a -> b₀ <= b ->
        q.partialSum a (p.partialSum b y - (p 0) fun _ => 0) in v := by
      simpa using hy (v_open.mem_nhds hv)
    refine ⟨a₀, fun a ha => ?_⟩
    have : Tendsto (fun b => q.partialSum a (p.partialSum b y - (p 0) fun _ => 0)) atTop
        (𝓝 (q.partialSum a (f (x + y) - f x))) := by
      have : ContinuousAt (q.partialSum a) (f (x + y) - f x) :=
        (partialSum_continuous q a).continuousAt
      apply this.tendsto.comp
      apply Tendsto.sub h'y
      convert! tendsto_const_nhds
      exact (HasFPowerSeriesAt.coeff_zero hf fun _ => 0).symm
    apply u_closed.mem_of_tendsto this
    filter_upwards [Ici_mem_atTop b₀] with b hb using vu (hab _ _ ha hb)
  have C : CauchySeq (fun (s : Finset Nat) => ∑ n in s, q n fun _ : Fin n => (f (x + y) - f x)) := by
    have Z := q.summable_norm_apply (x := f (x + y) - f x) h''y
    exact cauchySeq_finset_of_norm_bounded Z (fun i => le_rfl)
  exact tendsto_nhds_of_cauchySeq_of_subseq C tendsto_finset_range L

/--
theorem `OpenPartialHomeomorph.hasFPowerSeriesAt_symm` / 定理 `OpenPartialHomeomorph.hasFPowerSeriesAt_symm`

English:
theorem OpenPartialHomeomorph.hasFPowerSeriesAt_symm
  statement: (f : OpenPartialHomeomorph E F) {a : E}
  proof: by
  have A : HasFPowerSeriesAt (f.symm ∘ f) ((p.leftInv i a).comp p) a := by
    have : HasFPowerSeriesAt (ContinuousLinearMap.id 𝕜 E) ((p.leftInv i a).comp p) a := by
      rw [leftInv_comp _ _ _ hp]
      exact (ContinuousLinearMap.id 𝕜 E).hasFPowerSeriesAt a
    apply this.congr
    filter_upwards [f.open_source.mem_nhds h0] with x hx using by simp [hx]
  have B : forallᶠ (y : E) in 𝓝 0, HasSum (fun n => (p.leftInv i a n) fun _ => f (a + y) - f a)
      (f.symm (f (a + y))) := by
    simpa using! A.eventually_hasSum_of_comp h (radius_leftInv_pos_of_radius_pos h.radius_pos hp)
  have C : forallᶠ (y : E) in 𝓝 a, HasSum (fun n => (p.leftInv i a n) fun _ => f y - f a)
      (f.symm (f y)) := by
    rw [← sub_eq_zero_of_eq (a := a) rfl] at B
    have : ContinuousAt (fun x => x - a) a := by fun_prop
    simpa using! this.preimage_mem_nhds B
  have D : forallᶠ (y : E) in 𝓝 (f.symm (f a)),
      HasSum (fun n => (p.leftInv i a n) fun _ => f y - f a) y := by
    simp only [h0, OpenPartialHomeomorph.left_inv]
    filter_upwards [C, f.open_source.mem_nhds h0] with x hx h'x
    simpa [h'x] using! hx
  have E : forallᶠ z in 𝓝 (f a), HasSum (fun n => (p.leftInv i a n) fun _ => f (f.symm z) - f a)
      (f.symm z) := by
    have : ContinuousAt f.symm (f a) := f.continuousAt_symm (f.map_source h0)
    exact this D
  have F : forallᶠ z in 𝓝 (f a), HasSum (fun n => (p.leftInv i a n) fun _ => z - f a) (f.symm z) := by
    filter_upwards [f.open_target.mem_nhds (f.map_source h0), E] with z hz h'z
    simpa [hz] using! h'z
  rcases EMetric.mem_nhds_iff.1 F with ⟨r, r_pos, hr⟩
  refine ⟨min r (p.leftInv i a).radius, min_le_right _ _,
    lt_min r_pos (radius_leftInv_pos_of_radius_pos h.radius_pos hp), fun {y} hy => ?_⟩
  have : y + f a in Metric.eball (f a) r := by
    simp only [Metric.mem_eball, edist_eq_enorm_sub, sub_zero, lt_min_iff,
      add_sub_cancel_right] at hy ⊢
    exact hy.1
  simpa [add_comm] using! hr this

中文:
定理 OpenPartialHomeomorph.hasFPowerSeriesAt_symm
  结论: (f : OpenPartialHomeomorph E F) {a : E}
  证明: by
  have A : HasFPowerSeriesAt (f.symm ∘ f) ((p.leftInv i a).comp p) a := by
    have : HasFPowerSeriesAt (ContinuousLinearMap.id 𝕜 E) ((p.leftInv i a).comp p) a := by
      rw [leftInv_comp _ _ _ hp]
      exact (ContinuousLinearMap.id 𝕜 E).hasFPowerSeriesAt a
    apply this.congr
    filter_upwards [f.open_source.mem_nhds h0] with x hx using by simp [hx]
  have B : forallᶠ (y : E) in 𝓝 0, HasSum (fun n => (p.leftInv i a n) fun _ => f (a + y) - f a)
      (f.symm (f (a + y))) := by
    simpa using! A.eventually_hasSum_of_comp h (radius_leftInv_pos_of_radius_pos h.radius_pos hp)
  have C : forallᶠ (y : E) in 𝓝 a, HasSum (fun n => (p.leftInv i a n) fun _ => f y - f a)
      (f.symm (f y)) := by
    rw [← sub_eq_zero_of_eq (a := a) rfl] at B
    have : ContinuousAt (fun x => x - a) a := by fun_prop
    simpa using! this.preimage_mem_nhds B
  have D : forallᶠ (y : E) in 𝓝 (f.symm (f a)),
      HasSum (fun n => (p.leftInv i a n) fun _ => f y - f a) y := by
    simp only [h0, OpenPartialHomeomorph.left_inv]
    filter_upwards [C, f.open_source.mem_nhds h0] with x hx h'x
    simpa [h'x] using! hx
  have E : forallᶠ z in 𝓝 (f a), HasSum (fun n => (p.leftInv i a n) fun _ => f (f.symm z) - f a)
      (f.symm z) := by
    have : ContinuousAt f.symm (f a) := f.continuousAt_symm (f.map_source h0)
    exact this D
  have F : forallᶠ z in 𝓝 (f a), HasSum (fun n => (p.leftInv i a n) fun _ => z - f a) (f.symm z) := by
    filter_upwards [f.open_target.mem_nhds (f.map_source h0), E] with z hz h'z
    simpa [hz] using! h'z
  rcases EMetric.mem_nhds_iff.1 F with ⟨r, r_pos, hr⟩
  refine ⟨min r (p.leftInv i a).radius, min_le_right _ _,
    lt_min r_pos (radius_leftInv_pos_of_radius_pos h.radius_pos hp), fun {y} hy => ?_⟩
  have : y + f a in Metric.eball (f a) r := by
    simp only [Metric.mem_eball, edist_eq_enorm_sub, sub_zero, lt_min_iff,
      add_sub_cancel_right] at hy ⊢
    exact hy.1
  simpa [add_comm] using! hr this

Depends on / 依赖: A.eventually_hasSum_of_comp, ContinuousLinearMap, ContinuousLinearMap.id, HasFPowerSeriesAt, HasSum, eventually_hasSum_of_comp, f.open_source.mem_nhds, f.symm, filter_upwards, hasFPowerSeriesAt, leftInv, leftInv_comp, mem_nhds, open_source, p.leftInv, this.congr
-/
theorem OpenPartialHomeomorph.hasFPowerSeriesAt_symm (f : OpenPartialHomeomorph E F) {a : E}
    {i : E ≃L[𝕜] F} (h0 : a in f.source) {p : FormalMultilinearSeries 𝕜 E F}
    (h : HasFPowerSeriesAt f p a) (hp : p 1 = (continuousMultilinearCurryFin1 𝕜 E F).symm i) :
    HasFPowerSeriesAt f.symm (p.leftInv i a) (f a) := by
  have A : HasFPowerSeriesAt (f.symm ∘ f) ((p.leftInv i a).comp p) a := by
    have : HasFPowerSeriesAt (ContinuousLinearMap.id 𝕜 E) ((p.leftInv i a).comp p) a := by
      rw [leftInv_comp _ _ _ hp]
      exact (ContinuousLinearMap.id 𝕜 E).hasFPowerSeriesAt a
    apply this.congr
    filter_upwards [f.open_source.mem_nhds h0] with x hx using by simp [hx]
  have B : forallᶠ (y : E) in 𝓝 0, HasSum (fun n => (p.leftInv i a n) fun _ => f (a + y) - f a)
      (f.symm (f (a + y))) := by
    simpa using! A.eventually_hasSum_of_comp h (radius_leftInv_pos_of_radius_pos h.radius_pos hp)
  have C : forallᶠ (y : E) in 𝓝 a, HasSum (fun n => (p.leftInv i a n) fun _ => f y - f a)
      (f.symm (f y)) := by
    rw [← sub_eq_zero_of_eq (a := a) rfl] at B
    have : ContinuousAt (fun x => x - a) a := by fun_prop
    simpa using! this.preimage_mem_nhds B
  have D : forallᶠ (y : E) in 𝓝 (f.symm (f a)),
      HasSum (fun n => (p.leftInv i a n) fun _ => f y - f a) y := by
    simp only [h0, OpenPartialHomeomorph.left_inv]
    filter_upwards [C, f.open_source.mem_nhds h0] with x hx h'x
    simpa [h'x] using! hx
  have E : forallᶠ z in 𝓝 (f a), HasSum (fun n => (p.leftInv i a n) fun _ => f (f.symm z) - f a)
      (f.symm z) := by
    have : ContinuousAt f.symm (f a) := f.continuousAt_symm (f.map_source h0)
    exact this D
  have F : forallᶠ z in 𝓝 (f a), HasSum (fun n => (p.leftInv i a n) fun _ => z - f a) (f.symm z) := by
    filter_upwards [f.open_target.mem_nhds (f.map_source h0), E] with z hz h'z
    simpa [hz] using! h'z
  rcases EMetric.mem_nhds_iff.1 F with ⟨r, r_pos, hr⟩
  refine ⟨min r (p.leftInv i a).radius, min_le_right _ _,
    lt_min r_pos (radius_leftInv_pos_of_radius_pos h.radius_pos hp), fun {y} hy => ?_⟩
  have : y + f a in Metric.eball (f a) r := by
    simp only [Metric.mem_eball, edist_eq_enorm_sub, sub_zero, lt_min_iff,
      add_sub_cancel_right] at hy ⊢
    exact hy.1
  simpa [add_comm] using! hr this
