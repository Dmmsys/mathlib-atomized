/-
Copyright (c) 2025 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.Analysis.Calculus.FDeriv.ContinuousAlternatingMap
public import Mathlib.Analysis.Calculus.VectorField

/-!
# Evaluation of the derivative of differential forms on vector fields

In this file we prove the following formula and its corollaries.
If `ω` is a differentiable `k`-form and `V i` are `k + 1` differentiable vector fields, then

$$
  dω(V_0(x), \dots, V_n(x)) = \sum_{i=0}^k (-1)^i •
      D_x\left(ω\big(x; V_0(x), \dots, \widehat{V_i(x)}, \dots, V_k(x)\big)\right)(V_i(x)) +
    \sum_{0 \le i < j\le k} (-1)^{i + j}
        ω\big(x; [V_i, V_j](x), V_0(x), …, \widehat{V_i(x)}, …, \widehat{V_j(x)}, …, V_k(x)\big),
$$
where $[V_i, V_j]$ is the commutator of the vector fields $V_i$ and $V_j$.
As usual, $\widehat{V_i(x)}$ means that this item is removed from the sequence.

There is no convenient way to write the second term in Lean for `k = 0`,
so we only state this theorem for `k = n + 1`,
see `extDerivWithin_apply_vectorField` and `extDeriv_apply_vectorField`.

In this case, we write the second term as a sum over `i j : Fin (n + 1)`, `i ≤ j`,
where the indexes `(i, j)` in our sum correspond to `(i, j + 1)`
(formally, `(Fin.castSucc i, Fin.succ j)`) in the formula above.
For this reason, we have `-` before the sum in our formal statement.
-/

public section

open Filter ContinuousAlternatingMap Finset VectorField
open scoped Topology

variable {𝕜 E F : Type*}
  [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n m k : Nat} {r : WithTop Nat∞}
  {s t : Set E} {x : E}

/--
theorem `extDerivWithin_apply_vectorField` / 定理 `extDerivWithin_apply_vectorField`

English:
theorem extDerivWithin_apply_vectorField
  proof: by
  have H₀ (i : Fin (n + 2)) (j : Fin (n + 1)) :
      DifferentiableWithinAt 𝕜 (fun y => i.removeNth (V · y) j) s x := hV ..
  symm
  simp only [extDerivWithin_apply,
    fderivWithin_continuousAlternatingMap_apply_const_apply,
    fderivWithin_continuousAlternatingMap_apply_apply hω (H₀ _) hsx, *,
    smul_add, sum_add_distrib, add_sub_assoc, add_eq_left, sub_eq_zero, smul_sum]
  rw [Fin.sum_sum_eq_sum_triangle_add]
  refine Fintype.sum_congr _ _ fun i => sum_congr rfl fun j hj => ?_
  rw [mem_Ici] at hj
  simp only [← Fin.insertNth_removeNth, map_insertNth]
  rw [Fin.removeNth_removeNth_eq_swap]
  have H₁ : i.castSucc.succAbove j = j.succ := by simp [Fin.succAbove_of_le_castSucc, hj]
  have H₂ : j.predAbove i.castSucc = i := by simp [Fin.predAbove_of_le_castSucc, hj]
  have H₃ : j.succ.succAbove i = i.castSucc := by simp [Fin.succAbove_of_castSucc_lt, hj]
  simp +unfoldPartialApp [pow_add, lieBracketWithin, mul_smul, smul_comm ((-1) ^ (j : Nat)), smul_sub,
      ← sub_eq_add_neg, H₁, H₂, H₃, Fin.removeNth]

中文:
定理 extDerivWithin_apply_vectorField
  证明: by
  have H₀ (i : Fin (n + 2)) (j : Fin (n + 1)) :
      DifferentiableWithinAt 𝕜 (fun y => i.removeNth (V · y) j) s x := hV ..
  symm
  simp only [extDerivWithin_apply,
    fderivWithin_continuousAlternatingMap_apply_const_apply,
    fderivWithin_continuousAlternatingMap_apply_apply hω (H₀ _) hsx, *,
    smul_add, sum_add_distrib, add_sub_assoc, add_eq_left, sub_eq_zero, smul_sum]
  rw [Fin.sum_sum_eq_sum_triangle_add]
  refine Fintype.sum_congr _ _ fun i => sum_congr rfl fun j hj => ?_
  rw [mem_Ici] at hj
  simp only [← Fin.insertNth_removeNth, map_insertNth]
  rw [Fin.removeNth_removeNth_eq_swap]
  have H₁ : i.castSucc.succAbove j = j.succ := by simp [Fin.succAbove_of_le_castSucc, hj]
  have H₂ : j.predAbove i.castSucc = i := by simp [Fin.predAbove_of_le_castSucc, hj]
  have H₃ : j.succ.succAbove i = i.castSucc := by simp [Fin.succAbove_of_castSucc_lt, hj]
  simp +unfoldPartialApp [pow_add, lieBracketWithin, mul_smul, smul_comm ((-1) ^ (j : Nat)), smul_sub,
      ← sub_eq_add_neg, H₁, H₂, H₃, Fin.removeNth]

Depends on / 依赖: DifferentiableWithinAt, Fin.sum_sum_eq_sum_triangle_add, Fintype, Fintype.sum_congr, add_eq_left, add_sub_assoc, extDerivWithin_apply, fderivWithin_continuousAlternatingMap_apply_apply, fderivWithin_continuousAlternatingMap_apply_const_apply, i.removeNth, mem_Ici, removeNth, smul_add, smul_sum, sub_eq_zero, sum_add_distrib, sum_congr, sum_sum_eq_sum_triangle_add
-/
theorem extDerivWithin_apply_vectorField
    {ω : E -> E [⋀^Fin (n + 1)]->L[𝕜] F} {V : Fin (n + 2) -> E -> E}
    (hω : DifferentiableWithinAt 𝕜 ω s x) (hV : forall i, DifferentiableWithinAt 𝕜 (V i) s x)
    (hsx : UniqueDiffWithinAt 𝕜 s x) :
    extDerivWithin ω s x (V · x) =
      (∑ i, (-1) ^ i.val • fderivWithin 𝕜 (fun x => ω x (i.removeNth (V · x))) s x (V i x)) -
        ∑ i : Fin (n + 1), ∑ j >= i,
          (-1) ^ (i + j : Nat) •
            ω x (Matrix.vecCons (lieBracketWithin 𝕜 (V i.castSucc) (V j.succ) s x)
              (j.removeNth <| i.castSucc.removeNth (V · x))) := by
  have H₀ (i : Fin (n + 2)) (j : Fin (n + 1)) :
      DifferentiableWithinAt 𝕜 (fun y => i.removeNth (V · y) j) s x := hV ..
  symm
  simp only [extDerivWithin_apply,
    fderivWithin_continuousAlternatingMap_apply_const_apply,
    fderivWithin_continuousAlternatingMap_apply_apply hω (H₀ _) hsx, *,
    smul_add, sum_add_distrib, add_sub_assoc, add_eq_left, sub_eq_zero, smul_sum]
  rw [Fin.sum_sum_eq_sum_triangle_add]
  refine Fintype.sum_congr _ _ fun i => sum_congr rfl fun j hj => ?_
  rw [mem_Ici] at hj
  simp only [← Fin.insertNth_removeNth, map_insertNth]
  rw [Fin.removeNth_removeNth_eq_swap]
  have H₁ : i.castSucc.succAbove j = j.succ := by simp [Fin.succAbove_of_le_castSucc, hj]
  have H₂ : j.predAbove i.castSucc = i := by simp [Fin.predAbove_of_le_castSucc, hj]
  have H₃ : j.succ.succAbove i = i.castSucc := by simp [Fin.succAbove_of_castSucc_lt, hj]
  simp +unfoldPartialApp [pow_add, lieBracketWithin, mul_smul, smul_comm ((-1) ^ (j : Nat)), smul_sub,
      ← sub_eq_add_neg, H₁, H₂, H₃, Fin.removeNth]

/--
theorem `extDeriv_apply_vectorField` / 定理 `extDeriv_apply_vectorField`

English:
theorem extDeriv_apply_vectorField
  statement: {ω : E -> E [⋀^Fin (n + 1)]->L[𝕜] F} {V : Fin (n + 2) -> E -> E}
  proof: by
  simp only [← differentiableWithinAt_univ, ← extDerivWithin_univ, ← fderivWithin_univ,
    ← lieBracketWithin_univ] at *
  exact extDerivWithin_apply_vectorField hω hV (by simp)

中文:
定理 extDeriv_apply_vectorField
  结论: {ω : E -> E [⋀^有限集 (n + 1)]->L[𝕜] F} {V : 有限集 (n + 2) -> E -> E}
  证明: by
  simp only [← differentiableWithinAt_univ, ← extDerivWithin_univ, ← fderivWithin_univ,
    ← lieBracketWithin_univ] at *
  exact extDerivWithin_apply_vectorField hω hV (by simp)

Depends on / 依赖: differentiableWithinAt_univ, extDerivWithin_apply_vectorField, extDerivWithin_univ, fderivWithin_univ, lieBracketWithin_univ
-/
theorem extDeriv_apply_vectorField {ω : E -> E [⋀^Fin (n + 1)]->L[𝕜] F} {V : Fin (n + 2) -> E -> E}
    (hω : DifferentiableAt 𝕜 ω x) (hV : forall i, DifferentiableAt 𝕜 (V i) x) :
    extDeriv ω x (V · x) =
      (∑ i, (-1) ^ i.val • fderiv 𝕜 (fun x => ω x (i.removeNth (V · x))) x (V i x)) -
        ∑ i : Fin (n + 1), ∑ j >= i,
          (-1) ^ (i + j : Nat) •
            ω x (Matrix.vecCons (lieBracket 𝕜 (V i.castSucc) (V j.succ) x)
              (j.removeNth <| i.castSucc.removeNth (V · x))) := by
  simp only [← differentiableWithinAt_univ, ← extDerivWithin_univ, ← fderivWithin_univ,
    ← lieBracketWithin_univ] at *
  exact extDerivWithin_apply_vectorField hω hV (by simp)

/--
theorem `extDerivWithin_apply_vectorField_of_pairwise_commute` / 定理 `extDerivWithin_apply_vectorField_of_pairwise_commute`

English:
theorem extDerivWithin_apply_vectorField_of_pairwise_commute
  proof: by
  cases n with
  | zero =>
    simp [extDerivWithin_apply, fderivWithin_continuousAlternatingMap_apply_const_apply,
      fderivWithin_continuousAlternatingMap_apply_apply, *]
  | succ n =>
    rw [extDerivWithin_apply_vectorField hω hV hsx]; rw [sub_eq_self]
    refine Fintype.sum_eq_zero _ fun i => sum_eq_zero fun j hj => ?_
    rw [hcomm (ne_of_lt <| by simpa using hj)]; rw [(ω x).map_coord_zero 0] <;>
      simp

中文:
定理 extDerivWithin_apply_vectorField_of_pairwise_commute
  证明: by
  cases n with
  | zero =>
    simp [extDerivWithin_apply, fderivWithin_continuousAlternatingMap_apply_const_apply,
      fderivWithin_continuousAlternatingMap_apply_apply, *]
  | succ n =>
    rw [extDerivWithin_apply_vectorField hω hV hsx]; rw [sub_eq_self]
    refine Fintype.sum_eq_zero _ fun i => sum_eq_zero fun j hj => ?_
    rw [hcomm (ne_of_lt <| by simpa using hj)]; rw [(ω x).map_coord_zero 0] <;>
      simp

Depends on / 依赖: Fintype, Fintype.sum_eq_zero, extDerivWithin_apply, extDerivWithin_apply_vectorField, fderivWithin_continuousAlternatingMap_apply_apply, fderivWithin_continuousAlternatingMap_apply_const_apply, map_coord_zero, ne_of_lt, sub_eq_self, sum_eq_zero
-/
theorem extDerivWithin_apply_vectorField_of_pairwise_commute
    {ω : E -> E [⋀^Fin n]->L[𝕜] F} {V : Fin (n + 1) -> E -> E}
    (hω : DifferentiableWithinAt 𝕜 ω s x) (hV : forall i, DifferentiableWithinAt 𝕜 (V i) s x)
    (hsx : UniqueDiffWithinAt 𝕜 s x)
    (hcomm : Pairwise fun i j => lieBracketWithin 𝕜 (V i) (V j) s x = 0) :
    extDerivWithin ω s x (V · x) =
      (∑ i, (-1) ^ i.val • fderivWithin 𝕜 (fun x => ω x (i.removeNth (V · x))) s x (V i x)) := by
  cases n with
  | zero =>
    simp [extDerivWithin_apply, fderivWithin_continuousAlternatingMap_apply_const_apply,
      fderivWithin_continuousAlternatingMap_apply_apply, *]
  | succ n =>
    rw [extDerivWithin_apply_vectorField hω hV hsx]; rw [sub_eq_self]
    refine Fintype.sum_eq_zero _ fun i => sum_eq_zero fun j hj => ?_
    rw [hcomm (ne_of_lt <| by simpa using hj)]; rw [(ω x).map_coord_zero 0] <;>
      simp

/--
theorem `extDeriv_apply_vectorField_of_pairwise_commute` / 定理 `extDeriv_apply_vectorField_of_pairwise_commute`

English:
theorem extDeriv_apply_vectorField_of_pairwise_commute
  proof: by
  simp only [← differentiableWithinAt_univ, ← lieBracketWithin_univ, ← extDerivWithin_univ,
    ← fderivWithin_univ] at *
  exact extDerivWithin_apply_vectorField_of_pairwise_commute hω hV (by simp) hcomm

中文:
定理 extDeriv_apply_vectorField_of_pairwise_commute
  证明: by
  simp only [← differentiableWithinAt_univ, ← lieBracketWithin_univ, ← extDerivWithin_univ,
    ← fderivWithin_univ] at *
  exact extDerivWithin_apply_vectorField_of_pairwise_commute hω hV (by simp) hcomm

Depends on / 依赖: differentiableWithinAt_univ, extDerivWithin_apply_vectorField_of_pairwise_commute, extDerivWithin_univ, fderivWithin_univ, lieBracketWithin_univ
-/
theorem extDeriv_apply_vectorField_of_pairwise_commute
    {ω : E -> E [⋀^Fin n]->L[𝕜] F} {V : Fin (n + 1) -> E -> E}
    (hω : DifferentiableAt 𝕜 ω x) (hV : forall i, DifferentiableAt 𝕜 (V i) x)
    (hcomm : Pairwise fun i j => lieBracket 𝕜 (V i) (V j) x = 0) :
    extDeriv ω x (V · x) =
      (∑ i, (-1) ^ i.val • fderiv 𝕜 (fun x => ω x (i.removeNth (V · x))) x (V i x)) := by
  simp only [← differentiableWithinAt_univ, ← lieBracketWithin_univ, ← extDerivWithin_univ,
    ← fderivWithin_univ] at *
  exact extDerivWithin_apply_vectorField_of_pairwise_commute hω hV (by simp) hcomm
