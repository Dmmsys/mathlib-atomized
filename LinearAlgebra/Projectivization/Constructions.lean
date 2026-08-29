/-
Copyright (c) 2024 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.Projectivization.Basic

/-!

# Dot Product and Cross Product on Projective Spaces

This file defines the dot product and cross product on projective spaces.

## Definitions
- `Projectivization.orthogonal v w` is defined as vanishing of the dot product.
- `Projectivization.cross v w` for `v w : ℙ F (Fin 3 → F)` is defined as the cross product of
  `v` and `w` provided that `v ≠ w`. If `v = w`, then the cross product would be zero, so we
  instead define `cross v v = v`.

-/

@[expose] public section

variable {F : Type*} [Field F] {m : Type*} [Fintype m]

namespace Projectivization

open scoped LinearAlgebra.Projectivization

section DotProduct

/--
Definition of `orthogonal` / `orthogonal` 的定义

English:
definition orthogonal
  signature: : ℙ F (m -> F) -> ℙ F (m -> F) -> Prop
  body: Quotient.lift₂ (fun v w => v.1 ⬝ᵥ w.1 = 0) (fun _ _ _ _ ⟨_, h1⟩ ⟨_, h2⟩ => by
    simp_rw [← h1, ← h2, dotProduct_smul, smul_dotProduct, smul_smul,
      smul_eq_zero_iff_eq])

中文:
定义 orthogonal
  签名: : ℙ F (m -> F) -> ℙ F (m -> F) -> 命题
  定义体: Quotient.lift₂ (fun v w => v.1 ⬝ᵥ w.1 = 0) (fun _ _ _ _ ⟨_, h1⟩ ⟨_, h2⟩ => by
    simp_rw [← h1, ← h2, dotProduct_smul, smul_dotProduct, smul_smul,
      smul_eq_zero_iff_eq])

Depends on / 依赖: Quotient, Quotient.lift, dotProduct_smul, simp_rw, smul_dotProduct, smul_eq_zero_iff_eq, smul_smul
-/
def orthogonal : ℙ F (m -> F) -> ℙ F (m -> F) -> Prop :=
  Quotient.lift₂ (fun v w => v.1 ⬝ᵥ w.1 = 0) (fun _ _ _ _ ⟨_, h1⟩ ⟨_, h2⟩ => by
    simp_rw [← h1, ← h2, dotProduct_smul, smul_dotProduct, smul_smul,
      smul_eq_zero_iff_eq])

/--
lemma `orthogonal_mk` / 引理 `orthogonal_mk`

English:
lemma orthogonal_mk
  given: {v w : m -> F} (hv : v != 0) (hw : w != 0)
  proof: Iff.rfl

中文:
引理 orthogonal_mk
  条件: {v w : m -> F} (hv : v != 0) (hw : w != 0)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma orthogonal_mk {v w : m -> F} (hv : v != 0) (hw : w != 0) :
    orthogonal (mk F v hv) (mk F w hw) ↔ v ⬝ᵥ w = 0 :=
  Iff.rfl

/--
lemma `orthogonal_comm` / 引理 `orthogonal_comm`

English:
lemma orthogonal_comm
  given: {v w : ℙ F (m -> F)}
  statement: orthogonal v w ↔ orthogonal w v
  proof: by
  induction v with | h v hv => induction w with | h w hw =>
  rw [orthogonal_mk hv hw]; rw [orthogonal_mk hw hv]; rw [dotProduct_comm]

中文:
引理 orthogonal_comm
  条件: {v w : ℙ F (m -> F)}
  结论: orthogonal v w ↔ orthogonal w v
  证明: by
  induction v with | h v hv => induction w with | h w hw =>
  rw [orthogonal_mk hv hw]; rw [orthogonal_mk hw hv]; rw [dotProduct_comm]

Depends on / 依赖: dotProduct_comm, orthogonal_mk
-/
lemma orthogonal_comm {v w : ℙ F (m -> F)} : orthogonal v w ↔ orthogonal w v := by
  induction v with | h v hv => induction w with | h w hw =>
  rw [orthogonal_mk hv hw]; rw [orthogonal_mk hw hv]; rw [dotProduct_comm]

/--
lemma `exists_not_self_orthogonal` / 引理 `exists_not_self_orthogonal`

English:
lemma exists_not_self_orthogonal
  given: (v : ℙ F (m -> F))
  statement: exists w, ¬ orthogonal v w
  proof: by
  induction v with | h v hv =>
  rw [ne_eq]; rw [← dotProduct_eq_zero_iff]; rw [not_forall] at hv
  obtain ⟨w, hw⟩ := hv
  exact ⟨mk F w fun h => hw (by rw [h, dotProduct_zero]), hw⟩

中文:
引理 存在_not_self_orthogonal
  条件: (v : ℙ F (m -> F))
  结论: 存在 w, ¬ orthogonal v w
  证明: by
  induction v with | h v hv =>
  rw [ne_eq]; rw [← dotProduct_eq_zero_iff]; rw [not_forall] at hv
  obtain ⟨w, hw⟩ := hv
  exact ⟨mk F w fun h => hw (by rw [h, dotProduct_zero]), hw⟩

Depends on / 依赖: dotProduct_eq_zero_iff, dotProduct_zero, ne_eq, not_forall
-/
lemma exists_not_self_orthogonal (v : ℙ F (m -> F)) : exists w, ¬ orthogonal v w := by
  induction v with | h v hv =>
  rw [ne_eq]; rw [← dotProduct_eq_zero_iff]; rw [not_forall] at hv
  obtain ⟨w, hw⟩ := hv
  exact ⟨mk F w fun h => hw (by rw [h, dotProduct_zero]), hw⟩

/--
lemma `exists_not_orthogonal_self` / 引理 `exists_not_orthogonal_self`

English:
lemma exists_not_orthogonal_self
  given: (v : ℙ F (m -> F))
  statement: exists w, ¬ orthogonal w v
  proof: by
  simp only [orthogonal_comm]
  exact exists_not_self_orthogonal v

中文:
引理 存在_not_orthogonal_self
  条件: (v : ℙ F (m -> F))
  结论: 存在 w, ¬ orthogonal w v
  证明: by
  simp only [orthogonal_comm]
  exact exists_not_self_orthogonal v

Depends on / 依赖: exists_not_self_orthogonal, orthogonal_comm
-/
lemma exists_not_orthogonal_self (v : ℙ F (m -> F)) : exists w, ¬ orthogonal w v := by
  simp only [orthogonal_comm]
  exact exists_not_self_orthogonal v

end DotProduct

section CrossProduct

/--
lemma `mk_eq_mk_iff_crossProduct_eq_zero` / 引理 `mk_eq_mk_iff_crossProduct_eq_zero`

English:
lemma mk_eq_mk_iff_crossProduct_eq_zero
  given: {v w : Fin 3 -> F} (hv : v != 0) (hw : w != 0)
  proof: by
  rw [← not_iff_not]; rw [mk_eq_mk_iff']; rw [not_exists]; rw [← LinearIndependent.pair_iff' hw]; rw [← crossProduct_ne_zero_iff_linearIndependent]; rw [← cross_anticomm]; rw [neg_ne_zero]

中文:
引理 mk_eq_mk_iff_crossProduct_eq_zero
  条件: {v w : 有限集 3 -> F} (hv : v != 0) (hw : w != 0)
  证明: by
  rw [← not_iff_not]; rw [mk_eq_mk_iff']; rw [not_exists]; rw [← LinearIndependent.pair_iff' hw]; rw [← crossProduct_ne_zero_iff_linearIndependent]; rw [← cross_anticomm]; rw [neg_ne_zero]

Depends on / 依赖: LinearIndependent, LinearIndependent.pair_iff, crossProduct_ne_zero_iff_linearIndependent, cross_anticomm, mk_eq_mk_iff, neg_ne_zero, not_exists, not_iff_not, pair_iff
-/
lemma mk_eq_mk_iff_crossProduct_eq_zero {v w : Fin 3 -> F} (hv : v != 0) (hw : w != 0) :
    mk F v hv = mk F w hw ↔ crossProduct v w = 0 := by
  rw [← not_iff_not]; rw [mk_eq_mk_iff']; rw [not_exists]; rw [← LinearIndependent.pair_iff' hw]; rw [← crossProduct_ne_zero_iff_linearIndependent]; rw [← cross_anticomm]; rw [neg_ne_zero]

variable [DecidableEq F]

/--
Definition of `cross` / `cross` 的定义

English:
definition cross
  signature: : ℙ F (Fin 3 -> F) -> ℙ F (Fin 3 -> F) -> ℙ F (Fin 3 -> F)
  body: Quotient.map₂ (fun v w => if h : crossProduct v.1 w.1 = 0 then v else ⟨crossProduct v.1 w.1, h⟩)
    (fun _ _ ⟨a, ha⟩ _ _ ⟨b, hb⟩ => by
      simp_rw [← ha, ← hb, LinearMap.map_smul_of_tower, LinearMap.smul_apply, smul_smul,
        mul_comm b a, smul_eq_zero_iff_eq]
      split_ifs
      · use a
      · use a * b)

中文:
定义 cross
  签名: : ℙ F (有限集 3 -> F) -> ℙ F (有限集 3 -> F) -> ℙ F (有限集 3 -> F)
  定义体: Quotient.map₂ (fun v w => if h : crossProduct v.1 w.1 = 0 then v else ⟨crossProduct v.1 w.1, h⟩)
    (fun _ _ ⟨a, ha⟩ _ _ ⟨b, hb⟩ => by
      simp_rw [← ha, ← hb, LinearMap.map_smul_of_tower, LinearMap.smul_apply, smul_smul,
        mul_comm b a, smul_eq_zero_iff_eq]
      split_ifs
      · use a
      · use a * b)

Depends on / 依赖: LinearMap, LinearMap.map_smul_of_tower, LinearMap.smul_apply, Quotient, Quotient.map, crossProduct, map_smul_of_tower, mul_comm, simp_rw, smul_apply, smul_eq_zero_iff_eq, smul_smul, split_ifs
-/
def cross : ℙ F (Fin 3 -> F) -> ℙ F (Fin 3 -> F) -> ℙ F (Fin 3 -> F) :=
  Quotient.map₂ (fun v w => if h : crossProduct v.1 w.1 = 0 then v else ⟨crossProduct v.1 w.1, h⟩)
    (fun _ _ ⟨a, ha⟩ _ _ ⟨b, hb⟩ => by
      simp_rw [← ha, ← hb, LinearMap.map_smul_of_tower, LinearMap.smul_apply, smul_smul,
        mul_comm b a, smul_eq_zero_iff_eq]
      split_ifs
      · use a
      · use a * b)

/--
lemma `cross_mk` / 引理 `cross_mk`

English:
lemma cross_mk
  given: {v w : Fin 3 -> F} (hv : v != 0) (hw : w != 0)
  proof: by
  change Quotient.mk'' _ = _
  split_ifs with h <;> simp only [h] <;> rfl

中文:
引理 cross_mk
  条件: {v w : 有限集 3 -> F} (hv : v != 0) (hw : w != 0)
  证明: by
  change Quotient.mk'' _ = _
  split_ifs with h <;> simp only [h] <;> rfl

Depends on / 依赖: Quotient, Quotient.mk, split_ifs
-/
lemma cross_mk {v w : Fin 3 -> F} (hv : v != 0) (hw : w != 0) :
    cross (mk F v hv) (mk F w hw) =
      if h : crossProduct v w = 0 then mk F v hv else mk F (crossProduct v w) h := by
  change Quotient.mk'' _ = _
  split_ifs with h <;> simp only [h] <;> rfl

/--
lemma `cross_mk_of_cross_eq_zero` / 引理 `cross_mk_of_cross_eq_zero`

English:
lemma cross_mk_of_cross_eq_zero
  statement: {v w : Fin 3 -> F} (hv : v != 0) (hw : w != 0)
  proof: by
  rw [cross_mk]; rw [dif_pos h]

中文:
引理 cross_mk_of_cross_eq_zero
  结论: {v w : 有限集 3 -> F} (hv : v != 0) (hw : w != 0)
  证明: by
  rw [cross_mk]; rw [dif_pos h]

Depends on / 依赖: cross_mk, dif_pos
-/
lemma cross_mk_of_cross_eq_zero {v w : Fin 3 -> F} (hv : v != 0) (hw : w != 0)
    (h : crossProduct v w = 0) :
    cross (mk F v hv) (mk F w hw) = mk F v hv := by
  rw [cross_mk]; rw [dif_pos h]

/--
lemma `cross_mk_of_cross_ne_zero` / 引理 `cross_mk_of_cross_ne_zero`

English:
lemma cross_mk_of_cross_ne_zero
  statement: {v w : Fin 3 -> F} (hv : v != 0) (hw : w != 0)
  proof: by
  rw [cross_mk]; rw [dif_neg h]

中文:
引理 cross_mk_of_cross_ne_zero
  结论: {v w : 有限集 3 -> F} (hv : v != 0) (hw : w != 0)
  证明: by
  rw [cross_mk]; rw [dif_neg h]

Depends on / 依赖: cross_mk, dif_neg
-/
lemma cross_mk_of_cross_ne_zero {v w : Fin 3 -> F} (hv : v != 0) (hw : w != 0)
    (h : crossProduct v w != 0) :
    cross (mk F v hv) (mk F w hw) = mk F (crossProduct v w) h := by
  rw [cross_mk]; rw [dif_neg h]

/--
lemma `cross_self` / 引理 `cross_self`

English:
lemma cross_self
  given: (v : ℙ F (Fin 3 -> F))
  statement: cross v v = v
  proof: by
  induction v with | h v hv =>
  rw [cross_mk_of_cross_eq_zero]
  rw [← mk_eq_mk_iff_crossProduct_eq_zero hv]

中文:
引理 cross_self
  条件: (v : ℙ F (有限集 3 -> F))
  结论: cross v v = v
  证明: by
  induction v with | h v hv =>
  rw [cross_mk_of_cross_eq_zero]
  rw [← mk_eq_mk_iff_crossProduct_eq_zero hv]

Depends on / 依赖: cross_mk_of_cross_eq_zero, mk_eq_mk_iff_crossProduct_eq_zero
-/
lemma cross_self (v : ℙ F (Fin 3 -> F)) : cross v v = v := by
  induction v with | h v hv =>
  rw [cross_mk_of_cross_eq_zero]
  rw [← mk_eq_mk_iff_crossProduct_eq_zero hv]

/--
lemma `cross_mk_of_ne` / 引理 `cross_mk_of_ne`

English:
lemma cross_mk_of_ne
  given: {v w : Fin 3 -> F} (hv : v != 0) (hw : w != 0) (h : mk F v hv != mk F w hw)
  proof: by
  rw [cross_mk_of_cross_ne_zero]

中文:
引理 cross_mk_of_ne
  条件: {v w : 有限集 3 -> F} (hv : v != 0) (hw : w != 0) (h : mk F v hv != mk F w hw)
  证明: by
  rw [cross_mk_of_cross_ne_zero]

Depends on / 依赖: cross_mk_of_cross_ne_zero
-/
lemma cross_mk_of_ne {v w : Fin 3 -> F} (hv : v != 0) (hw : w != 0) (h : mk F v hv != mk F w hw) :
    cross (mk F v hv) (mk F w hw) = mk F (crossProduct v w)
      (mt (mk_eq_mk_iff_crossProduct_eq_zero hv hw).mpr h) := by
  rw [cross_mk_of_cross_ne_zero]

/--
lemma `cross_comm` / 引理 `cross_comm`

English:
lemma cross_comm
  given: (v w : ℙ F (Fin 3 -> F))
  statement: cross v w = cross w v
  proof: by
  rcases eq_or_ne v w with rfl | h
  · rfl
  · induction v with | h v hv =>
    induction w with | h w hw =>
    rw [cross_mk_of_ne hv hw h]; rw [cross_mk_of_ne hw hv h.symm]; rw [mk_eq_mk_iff_crossProduct_eq_zero]; rw [← cross_anticomm v w]; rw [map_neg]; rw [_root_.cross_self]; rw [neg_zero]

中文:
引理 cross_comm
  条件: (v w : ℙ F (有限集 3 -> F))
  结论: cross v w = cross w v
  证明: by
  rcases eq_or_ne v w with rfl | h
  · rfl
  · induction v with | h v hv =>
    induction w with | h w hw =>
    rw [cross_mk_of_ne hv hw h]; rw [cross_mk_of_ne hw hv h.symm]; rw [mk_eq_mk_iff_crossProduct_eq_zero]; rw [← cross_anticomm v w]; rw [map_neg]; rw [_root_.cross_self]; rw [neg_zero]

Depends on / 依赖: _root_, _root_.cross_self, cross_anticomm, cross_mk_of_ne, cross_self, eq_or_ne, h.symm, map_neg, mk_eq_mk_iff_crossProduct_eq_zero, neg_zero
-/
lemma cross_comm (v w : ℙ F (Fin 3 -> F)) : cross v w = cross w v := by
  rcases eq_or_ne v w with rfl | h
  · rfl
  · induction v with | h v hv =>
    induction w with | h w hw =>
    rw [cross_mk_of_ne hv hw h]; rw [cross_mk_of_ne hw hv h.symm]; rw [mk_eq_mk_iff_crossProduct_eq_zero]; rw [← cross_anticomm v w]; rw [map_neg]; rw [_root_.cross_self]; rw [neg_zero]

/--
theorem `cross_orthogonal_left` / 定理 `cross_orthogonal_left`

English:
theorem cross_orthogonal_left
  given: {v w : ℙ F (Fin 3 -> F)} (h : v != w)
  proof: by
  induction v with | h v hv =>
  induction w with | h w hw =>
  rw [cross_mk_of_ne hv hw h]; rw [orthogonal_mk]; rw [dotProduct_comm]; rw [dot_self_cross]

中文:
定理 cross_orthogonal_left
  条件: {v w : ℙ F (有限集 3 -> F)} (h : v != w)
  证明: by
  induction v with | h v hv =>
  induction w with | h w hw =>
  rw [cross_mk_of_ne hv hw h]; rw [orthogonal_mk]; rw [dotProduct_comm]; rw [dot_self_cross]

Depends on / 依赖: cross_mk_of_ne, dotProduct_comm, dot_self_cross, orthogonal_mk
-/
theorem cross_orthogonal_left {v w : ℙ F (Fin 3 -> F)} (h : v != w) :
    (cross v w).orthogonal v := by
  induction v with | h v hv =>
  induction w with | h w hw =>
  rw [cross_mk_of_ne hv hw h]; rw [orthogonal_mk]; rw [dotProduct_comm]; rw [dot_self_cross]

/--
theorem `cross_orthogonal_right` / 定理 `cross_orthogonal_right`

English:
theorem cross_orthogonal_right
  given: {v w : ℙ F (Fin 3 -> F)} (h : v != w)
  proof: by
  rw [cross_comm]
  exact cross_orthogonal_left h.symm

中文:
定理 cross_orthogonal_right
  条件: {v w : ℙ F (有限集 3 -> F)} (h : v != w)
  证明: by
  rw [cross_comm]
  exact cross_orthogonal_left h.symm

Depends on / 依赖: cross_comm, cross_orthogonal_left, h.symm
-/
theorem cross_orthogonal_right {v w : ℙ F (Fin 3 -> F)} (h : v != w) :
    (cross v w).orthogonal w := by
  rw [cross_comm]
  exact cross_orthogonal_left h.symm

/--
theorem `orthogonal_cross_left` / 定理 `orthogonal_cross_left`

English:
theorem orthogonal_cross_left
  given: {v w : ℙ F (Fin 3 -> F)} (h : v != w)
  proof: by
  rw [orthogonal_comm]
  exact cross_orthogonal_left h

中文:
定理 orthogonal_cross_left
  条件: {v w : ℙ F (有限集 3 -> F)} (h : v != w)
  证明: by
  rw [orthogonal_comm]
  exact cross_orthogonal_left h

Depends on / 依赖: cross_orthogonal_left, orthogonal_comm
-/
theorem orthogonal_cross_left {v w : ℙ F (Fin 3 -> F)} (h : v != w) :
    v.orthogonal (cross v w) := by
  rw [orthogonal_comm]
  exact cross_orthogonal_left h

/--
lemma `orthogonal_cross_right` / 引理 `orthogonal_cross_right`

English:
lemma orthogonal_cross_right
  given: {v w : ℙ F (Fin 3 -> F)} (h : v != w)
  proof: by
  rw [orthogonal_comm]
  exact cross_orthogonal_right h

中文:
引理 orthogonal_cross_right
  条件: {v w : ℙ F (有限集 3 -> F)} (h : v != w)
  证明: by
  rw [orthogonal_comm]
  exact cross_orthogonal_right h

Depends on / 依赖: cross_orthogonal_right, orthogonal_comm
-/
lemma orthogonal_cross_right {v w : ℙ F (Fin 3 -> F)} (h : v != w) :
    w.orthogonal (cross v w) := by
  rw [orthogonal_comm]
  exact cross_orthogonal_right h

end CrossProduct

end Projectivization
