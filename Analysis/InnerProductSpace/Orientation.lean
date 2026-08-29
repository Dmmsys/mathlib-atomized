/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Heather Macbeth
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import Mathlib.LinearAlgebra.Orientation

/-!
# Orientations of real inner product spaces.

This file provides definitions and proves lemmas about orientations of real inner product spaces.

## Main definitions

* `OrthonormalBasis.adjustToOrientation` takes an orthonormal basis and an orientation, and
  returns an orthonormal basis with that orientation: either the original orthonormal basis, or one
  constructed by negating a single (arbitrary) basis vector.
* `Orientation.finOrthonormalBasis` is an orthonormal basis, indexed by `Fin n`, with the given
  orientation.
* `Orientation.volumeForm` is a nonvanishing top-dimensional alternating form on an oriented real
  inner product space, uniquely defined by compatibility with the orientation and inner product
  structure.

## Main theorems

* `Orientation.volumeForm_apply_le` states that the result of applying the volume form to a set of
  `n` vectors, where `n` is the dimension the inner product space, is bounded by the product of the
  lengths of the vectors.
* `Orientation.abs_volumeForm_apply_of_pairwise_orthogonal` states that the result of applying the
  volume form to a set of `n` orthogonal vectors, where `n` is the dimension the inner product
  space, is equal up to sign to the product of the lengths of the vectors.

-/

@[expose] public section


noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]

open Module InnerProductSpace

open scoped RealInnerProductSpace

namespace OrthonormalBasis

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (e f : OrthonormalBasis ι Real E)
  (x : Orientation Real E ι)

/--
theorem `det_to_matrix_orthonormalBasis_of_same_orientation` / 定理 `det_to_matrix_orthonormalBasis_of_same_orientation`

English:
theorem det_to_matrix_orthonormalBasis_of_same_orientation
  proof: by
  apply (e.det_to_matrix_orthonormalBasis_real f).resolve_right
  have : 0 < e.toBasis.det f := by
    rw [e.toBasis.orientation_eq_iff_det_pos] at h
    simpa using h
  linarith

中文:
定理 det_to_matrix_orthonormalBasis_of_same_orientation
  证明: by
  apply (e.det_to_matrix_orthonormalBasis_real f).resolve_right
  have : 0 < e.toBasis.det f := by
    rw [e.toBasis.orientation_eq_iff_det_pos] at h
    simpa using h
  linarith

Depends on / 依赖: det_to_matrix_orthonormalBasis_real, e.det_to_matrix_orthonormalBasis_real, e.toBasis.det, e.toBasis.orientation_eq_iff_det_pos, orientation_eq_iff_det_pos, resolve_right, toBasis
-/
theorem det_to_matrix_orthonormalBasis_of_same_orientation
    (h : e.toBasis.orientation = f.toBasis.orientation) : e.toBasis.det f = 1 := by
  apply (e.det_to_matrix_orthonormalBasis_real f).resolve_right
  have : 0 < e.toBasis.det f := by
    rw [e.toBasis.orientation_eq_iff_det_pos] at h
    simpa using h
  linarith

/--
theorem `det_to_matrix_orthonormalBasis_of_opposite_orientation` / 定理 `det_to_matrix_orthonormalBasis_of_opposite_orientation`

English:
theorem det_to_matrix_orthonormalBasis_of_opposite_orientation
  proof: by
  contrapose! h
  simp [e.toBasis.orientation_eq_iff_det_pos,
    (e.det_to_matrix_orthonormalBasis_real f).resolve_right h]

中文:
定理 det_to_matrix_orthonormalBasis_of_opposite_orientation
  证明: by
  contrapose! h
  simp [e.toBasis.orientation_eq_iff_det_pos,
    (e.det_to_matrix_orthonormalBasis_real f).resolve_right h]

Depends on / 依赖: contrapose, det_to_matrix_orthonormalBasis_real, e.det_to_matrix_orthonormalBasis_real, e.toBasis.orientation_eq_iff_det_pos, orientation_eq_iff_det_pos, resolve_right, toBasis
-/
theorem det_to_matrix_orthonormalBasis_of_opposite_orientation
    (h : e.toBasis.orientation != f.toBasis.orientation) : e.toBasis.det f = -1 := by
  contrapose! h
  simp [e.toBasis.orientation_eq_iff_det_pos,
    (e.det_to_matrix_orthonormalBasis_real f).resolve_right h]

variable {e f}

/--
theorem `same_orientation_iff_det_eq_det` / 定理 `same_orientation_iff_det_eq_det`

English:
theorem same_orientation_iff_det_eq_det
  proof: by
  constructor
  · intro h
    dsimp [Basis.orientation]
    congr
  · intro h
    rw [e.toBasis.det.eq_smul_basis_det f.toBasis]
    simp [e.det_to_matrix_orthonormalBasis_of_same_orientation f h]

中文:
定理 same_orientation_iff_det_eq_det
  证明: by
  constructor
  · intro h
    dsimp [Basis.orientation]
    congr
  · intro h
    rw [e.toBasis.det.eq_smul_basis_det f.toBasis]
    simp [e.det_to_matrix_orthonormalBasis_of_same_orientation f h]

Depends on / 依赖: Basis.orientation, det_to_matrix_orthonormalBasis_of_same_orientation, e.det_to_matrix_orthonormalBasis_of_same_orientation, e.toBasis.det.eq_smul_basis_det, eq_smul_basis_det, f.toBasis, orientation, toBasis
-/
theorem same_orientation_iff_det_eq_det :
    e.toBasis.det = f.toBasis.det ↔ e.toBasis.orientation = f.toBasis.orientation := by
  constructor
  · intro h
    dsimp [Basis.orientation]
    congr
  · intro h
    rw [e.toBasis.det.eq_smul_basis_det f.toBasis]
    simp [e.det_to_matrix_orthonormalBasis_of_same_orientation f h]

variable (e f)

/--
theorem `det_eq_neg_det_of_opposite_orientation` / 定理 `det_eq_neg_det_of_opposite_orientation`

English:
theorem det_eq_neg_det_of_opposite_orientation
  given: (h : e.toBasis.orientation != f.toBasis.orientation)
  proof: by
  rw [e.toBasis.det.eq_smul_basis_det f.toBasis]
  simp [e.det_to_matrix_orthonormalBasis_of_opposite_orientation f h]

中文:
定理 det_eq_neg_det_of_opposite_orientation
  条件: (h : e.toBasis.orientation != f.toBasis.orientation)
  证明: by
  rw [e.toBasis.det.eq_smul_basis_det f.toBasis]
  simp [e.det_to_matrix_orthonormalBasis_of_opposite_orientation f h]

Depends on / 依赖: det_to_matrix_orthonormalBasis_of_opposite_orientation, e.det_to_matrix_orthonormalBasis_of_opposite_orientation, e.toBasis.det.eq_smul_basis_det, eq_smul_basis_det, f.toBasis, toBasis
-/
theorem det_eq_neg_det_of_opposite_orientation (h : e.toBasis.orientation != f.toBasis.orientation) :
    e.toBasis.det = -f.toBasis.det := by
  rw [e.toBasis.det.eq_smul_basis_det f.toBasis]
  simp [e.det_to_matrix_orthonormalBasis_of_opposite_orientation f h]

variable [Nonempty ι]

section AdjustToOrientation

/--
theorem `orthonormal_adjustToOrientation` / 定理 `orthonormal_adjustToOrientation`

English:
theorem orthonormal_adjustToOrientation
  statement: Orthonormal Real (e.toBasis.adjustToOrientation x)
  proof: by
  apply e.orthonormal.orthonormal_of_forall_eq_or_eq_neg
  simpa using e.toBasis.adjustToOrientation_apply_eq_or_eq_neg x

中文:
定理 orthonormal_adjustToOrientation
  结论: Orthonormal 实数 (e.toBasis.adjustToOrientation x)
  证明: by
  apply e.orthonormal.orthonormal_of_forall_eq_or_eq_neg
  simpa using e.toBasis.adjustToOrientation_apply_eq_or_eq_neg x

Depends on / 依赖: adjustToOrientation_apply_eq_or_eq_neg, e.orthonormal.orthonormal_of_forall_eq_or_eq_neg, e.toBasis.adjustToOrientation_apply_eq_or_eq_neg, orthonormal, orthonormal_of_forall_eq_or_eq_neg, toBasis
-/
theorem orthonormal_adjustToOrientation : Orthonormal Real (e.toBasis.adjustToOrientation x) := by
  apply e.orthonormal.orthonormal_of_forall_eq_or_eq_neg
  simpa using e.toBasis.adjustToOrientation_apply_eq_or_eq_neg x

/--
Definition of `adjustToOrientation` / `adjustToOrientation` 的定义

English:
definition adjustToOrientation
  signature: : OrthonormalBasis ι Real E
  body: (e.toBasis.adjustToOrientation x).toOrthonormalBasis (e.orthonormal_adjustToOrientation x)

中文:
定义 adjustToOrientation
  签名: : OrthonormalBasis ι 实数 E
  定义体: (e.toBasis.adjustToOrientation x).toOrthonormalBasis (e.orthonormal_adjustToOrientation x)

Depends on / 依赖: adjustToOrientation, e.orthonormal_adjustToOrientation, e.toBasis.adjustToOrientation, orthonormal_adjustToOrientation, toBasis, toOrthonormalBasis
-/
def adjustToOrientation : OrthonormalBasis ι Real E :=
  (e.toBasis.adjustToOrientation x).toOrthonormalBasis (e.orthonormal_adjustToOrientation x)

/--
theorem `toBasis_adjustToOrientation` / 定理 `toBasis_adjustToOrientation`

English:
theorem toBasis_adjustToOrientation
  proof: (e.toBasis.adjustToOrientation x).toBasis_toOrthonormalBasis _

中文:
定理 toBasis_adjustToOrientation
  证明: (e.toBasis.adjustToOrientation x).toBasis_toOrthonormalBasis _

Depends on / 依赖: adjustToOrientation, e.toBasis.adjustToOrientation, toBasis, toBasis_toOrthonormalBasis
-/
theorem toBasis_adjustToOrientation :
    (e.adjustToOrientation x).toBasis = e.toBasis.adjustToOrientation x :=
  (e.toBasis.adjustToOrientation x).toBasis_toOrthonormalBasis _

/-- `adjustToOrientation` gives an orthonormal basis with the required orientation. -/
@[simp]
/--
theorem `orientation_adjustToOrientation` / 定理 `orientation_adjustToOrientation`

English:
theorem orientation_adjustToOrientation
  statement: (e.adjustToOrientation x).toBasis.orientation = x
  proof: by
  rw [e.toBasis_adjustToOrientation]
  exact e.toBasis.orientation_adjustToOrientation x

中文:
定理 orientation_adjustToOrientation
  结论: (e.adjustToOrientation x).toBasis.orientation = x
  证明: by
  rw [e.toBasis_adjustToOrientation]
  exact e.toBasis.orientation_adjustToOrientation x

Depends on / 依赖: e.toBasis.orientation_adjustToOrientation, e.toBasis_adjustToOrientation, orientation_adjustToOrientation, toBasis, toBasis_adjustToOrientation
-/
theorem orientation_adjustToOrientation : (e.adjustToOrientation x).toBasis.orientation = x := by
  rw [e.toBasis_adjustToOrientation]
  exact e.toBasis.orientation_adjustToOrientation x

/--
theorem `adjustToOrientation_apply_eq_or_eq_neg` / 定理 `adjustToOrientation_apply_eq_or_eq_neg`

English:
theorem adjustToOrientation_apply_eq_or_eq_neg
  given: (i : ι)
  proof: by
  simpa [← e.toBasis_adjustToOrientation] using
    e.toBasis.adjustToOrientation_apply_eq_or_eq_neg x i

中文:
定理 adjustToOrientation_apply_eq_or_eq_neg
  条件: (i : ι)
  证明: by
  simpa [← e.toBasis_adjustToOrientation] using
    e.toBasis.adjustToOrientation_apply_eq_or_eq_neg x i

Depends on / 依赖: adjustToOrientation_apply_eq_or_eq_neg, e.toBasis.adjustToOrientation_apply_eq_or_eq_neg, e.toBasis_adjustToOrientation, toBasis, toBasis_adjustToOrientation
-/
theorem adjustToOrientation_apply_eq_or_eq_neg (i : ι) :
    e.adjustToOrientation x i = e i ∨ e.adjustToOrientation x i = -e i := by
  simpa [← e.toBasis_adjustToOrientation] using
    e.toBasis.adjustToOrientation_apply_eq_or_eq_neg x i

/--
theorem `det_adjustToOrientation` / 定理 `det_adjustToOrientation`

English:
theorem det_adjustToOrientation
  proof: by
  simpa using! e.toBasis.det_adjustToOrientation x

中文:
定理 det_adjustToOrientation
  证明: by
  simpa using! e.toBasis.det_adjustToOrientation x

Depends on / 依赖: det_adjustToOrientation, e.toBasis.det_adjustToOrientation, toBasis
-/
theorem det_adjustToOrientation :
    (e.adjustToOrientation x).toBasis.det = e.toBasis.det ∨
      (e.adjustToOrientation x).toBasis.det = -e.toBasis.det := by
  simpa using! e.toBasis.det_adjustToOrientation x

/--
theorem `abs_det_adjustToOrientation` / 定理 `abs_det_adjustToOrientation`

English:
theorem abs_det_adjustToOrientation
  given: (v : ι -> E)
  proof: by
  simp [toBasis_adjustToOrientation]

中文:
定理 abs_det_adjustToOrientation
  条件: (v : ι -> E)
  证明: by
  simp [toBasis_adjustToOrientation]

Depends on / 依赖: toBasis_adjustToOrientation
-/
theorem abs_det_adjustToOrientation (v : ι -> E) :
    |(e.adjustToOrientation x).toBasis.det v| = |e.toBasis.det v| := by
  simp [toBasis_adjustToOrientation]

end AdjustToOrientation

end OrthonormalBasis

namespace Orientation

variable {n : Nat}

open OrthonormalBasis

/--
Definition of `finOrthonormalBasis` / `finOrthonormalBasis` 的定义

English:
definition finOrthonormalBasis
  signature: (hn : 0 < n) (h : finrank Real E = n) (x : Orientation Real E (Fin n))
  body: by
  haveI := Fin.pos_iff_nonempty.1 hn
haveI : FiniteDimensional Real E := .of_finrank_pos h.symm ▸ hn
  exact ((@stdOrthonormalBasis _ _ _ _ _ this).reindex <| finCongr h).adjustToOrientation x

中文:
定义 finOrthonormalBasis
  签名: (hn : 0 < n) (h : finrank 实数 E = n) (x : Orientation 实数 E (Fin n))
  定义体: by
  haveI := Fin.pos_iff_nonempty.1 hn
haveI : FiniteDimensional Real E := .of_finrank_pos h.symm ▸ hn
  exact ((@stdOrthonormalBasis _ _ _ _ _ this).reindex <| finCongr h).adjustToOrientation x
-/
protected def finOrthonormalBasis (hn : 0 < n) (h : finrank Real E = n) (x : Orientation Real E (Fin n)) :
    OrthonormalBasis (Fin n) Real E := by
  haveI := Fin.pos_iff_nonempty.1 hn
haveI : FiniteDimensional Real E := .of_finrank_pos h.symm ▸ hn
  exact ((@stdOrthonormalBasis _ _ _ _ _ this).reindex <| finCongr h).adjustToOrientation x

/-- `Orientation.finOrthonormalBasis` gives a basis with the required orientation. -/
@[simp]
/--
theorem `finOrthonormalBasis_orientation` / 定理 `finOrthonormalBasis_orientation`

English:
theorem finOrthonormalBasis_orientation
  statement: (hn : 0 < n) (h : finrank Real E = n)
  proof: by
  have := Fin.pos_iff_nonempty.1 hn
have : FiniteDimensional Real E := .of_finrank_pos h.symm ▸ hn
  exact ((@stdOrthonormalBasis _ _ _ _ _ this).reindex <|
    finCongr h).orientation_adjustToOrientation x

中文:
定理 finOrthonormalBasis_orientation
  结论: (hn : 0 < n) (h : finrank 实数 E = n)
  证明: by
  have := Fin.pos_iff_nonempty.1 hn
have : FiniteDimensional Real E := .of_finrank_pos h.symm ▸ hn
  exact ((@stdOrthonormalBasis _ _ _ _ _ this).reindex <|
    finCongr h).orientation_adjustToOrientation x

Depends on / 依赖: Fin.pos_iff_nonempty, FiniteDimensional, finCongr, h.symm, of_finrank_pos, orientation_adjustToOrientation, pos_iff_nonempty, reindex, stdOrthonormalBasis
-/
theorem finOrthonormalBasis_orientation (hn : 0 < n) (h : finrank Real E = n)
    (x : Orientation Real E (Fin n)) : (x.finOrthonormalBasis hn h).toBasis.orientation = x := by
  have := Fin.pos_iff_nonempty.1 hn
have : FiniteDimensional Real E := .of_finrank_pos h.symm ▸ hn
  exact ((@stdOrthonormalBasis _ _ _ _ _ this).reindex <|
    finCongr h).orientation_adjustToOrientation x

section VolumeForm

variable [_i : Fact (finrank Real E = n)] (o : Orientation Real E (Fin n))

/-- The volume form on an oriented real inner product space, a nonvanishing top-dimensional
alternating form uniquely defined by compatibility with the orientation and inner product structure.
-/
irreducible_def volumeForm : E [⋀^Fin n]->ₗ[Real] Real := by
  classical
    cases n with
    | zero =>
      let opos : E [⋀^Fin 0]->ₗ[Real] Real := .constOfIsEmpty Real E (Fin 0) (1 : Real)
      exact o.eq_or_eq_neg_of_isEmpty.by_cases (fun _ => opos) fun _ => -opos
    | succ n => exact (o.finOrthonormalBasis n.succ_pos _i.out).toBasis.det

@[simp]
/--
theorem `volumeForm_zero_pos` / 定理 `volumeForm_zero_pos`

English:
theorem volumeForm_zero_pos
  given: [_i : Fact (finrank Real E = 0)]
  proof: by
  simp [volumeForm, Or.by_cases]

中文:
定理 volumeForm_zero_pos
  条件: [_i : Fact (finrank 实数 E = 0)]
  证明: by
  simp [volumeForm, Or.by_cases]

Depends on / 依赖: Or.by_cases, volumeForm
-/
theorem volumeForm_zero_pos [_i : Fact (finrank Real E = 0)] :
    Orientation.volumeForm (positiveOrientation : Orientation Real E (Fin 0)) =
      AlternatingMap.constLinearEquivOfIsEmpty 1 := by
  simp [volumeForm, Or.by_cases]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `volumeForm_zero_neg` / 定理 `volumeForm_zero_neg`

English:
theorem volumeForm_zero_neg
  given: [_i : Fact (finrank Real E = 0)]
  proof: by
  simp_rw [volumeForm, Or.by_cases, positiveOrientation]
  apply if_neg
  simp only [neg_rayOfNeZero]
  rw [ray_eq_iff]; rw [SameRay.sameRay_comm]
  intro h
  simpa using
    congr_arg AlternatingMap.constLinearEquivOfIsEmpty.symm (eq_zero_of_sameRay_self_neg h)

中文:
定理 volumeForm_zero_neg
  条件: [_i : Fact (finrank 实数 E = 0)]
  证明: by
  simp_rw [volumeForm, Or.by_cases, positiveOrientation]
  apply if_neg
  simp only [neg_rayOfNeZero]
  rw [ray_eq_iff]; rw [SameRay.sameRay_comm]
  intro h
  simpa using
    congr_arg AlternatingMap.constLinearEquivOfIsEmpty.symm (eq_zero_of_sameRay_self_neg h)

Depends on / 依赖: AlternatingMap, AlternatingMap.constLinearEquivOfIsEmpty.symm, Or.by_cases, SameRay, SameRay.sameRay_comm, congr_arg, constLinearEquivOfIsEmpty, eq_zero_of_sameRay_self_neg, if_neg, neg_rayOfNeZero, positiveOrientation, ray_eq_iff, sameRay_comm, simp_rw, volumeForm
-/
theorem volumeForm_zero_neg [_i : Fact (finrank Real E = 0)] :
    Orientation.volumeForm (-positiveOrientation : Orientation Real E (Fin 0)) =
      -AlternatingMap.constLinearEquivOfIsEmpty 1 := by
  simp_rw [volumeForm, Or.by_cases, positiveOrientation]
  apply if_neg
  simp only [neg_rayOfNeZero]
  rw [ray_eq_iff]; rw [SameRay.sameRay_comm]
  intro h
  simpa using
    congr_arg AlternatingMap.constLinearEquivOfIsEmpty.symm (eq_zero_of_sameRay_self_neg h)

/--
theorem `volumeForm_robust` / 定理 `volumeForm_robust`

English:
theorem volumeForm_robust
  given: (b : OrthonormalBasis (Fin n) Real E) (hb : b.toBasis.orientation = o)
  proof: by
  cases n
  · classical
      have : o = positiveOrientation := hb.symm.trans b.toBasis.orientation_isEmpty
      simp_rw [volumeForm, Or.by_cases, dif_pos this, Nat.rec_zero, Basis.det_isEmpty]
  · simp_rw [volumeForm]
    rw [same_orientation_iff_det_eq_det]; rw [hb]
    exact o.finOrthonormalB

中文:
定理 volumeForm_robust
  条件: (b : OrthonormalBasis (Fin n) 实数 E) (hb : b.toBasis.orientation = o)
  证明: by
  cases n
  · classical
      have : o = positiveOrientation := hb.symm.trans b.toBasis.orientation_isEmpty
      simp_rw [volumeForm, Or.by_cases, dif_pos this, Nat.rec_zero, Basis.det_isEmpty]
  · simp_rw [volumeForm]
    rw [same_orientation_iff_det_eq_det]; rw [hb]
    exact o.finOrthonormalB

Depends on / 依赖: Basis.det_isEmpty, Nat.rec_zero, Or.by_cases, b.toBasis.orientation_isEmpty, classical, det_isEmpty, dif_pos, finOrthonormalBasis_orientation, hb.symm.trans, o.finOrthonormalBasis_orientation, orientation_isEmpty, positiveOrientation, rec_zero, same_orientation_iff_det_eq_det, simp_rw, toBasis, volumeForm
-/
theorem volumeForm_robust (b : OrthonormalBasis (Fin n) Real E) (hb : b.toBasis.orientation = o) :
    o.volumeForm = b.toBasis.det := by
  cases n
  · classical
      have : o = positiveOrientation := hb.symm.trans b.toBasis.orientation_isEmpty
      simp_rw [volumeForm, Or.by_cases, dif_pos this, Nat.rec_zero, Basis.det_isEmpty]
  · simp_rw [volumeForm]
    rw [same_orientation_iff_det_eq_det]; rw [hb]
    exact o.finOrthonormalBasis_orientation _ _

/--
theorem `volumeForm_robust_neg` / 定理 `volumeForm_robust_neg`

English:
theorem volumeForm_robust_neg
  given: (b : OrthonormalBasis (Fin n) Real E) (hb : b.toBasis.orientation != o)
  proof: by
  rcases n with - | n
  · classical
      have : positiveOrientation != o := by rwa [b.toBasis.orientation_isEmpty] at hb
      simp_rw [volumeForm, Or.by_cases, dif_neg this.symm, Nat.rec_zero, Basis.det_isEmpty]
  let e : OrthonormalBasis (Fin n.succ) Real E := o.finOrthonormalBasis n.succ_pos 

中文:
定理 volumeForm_robust_neg
  条件: (b : OrthonormalBasis (Fin n) 实数 E) (hb : b.toBasis.orientation != o)
  证明: by
  rcases n with - | n
  · classical
      have : positiveOrientation != o := by rwa [b.toBasis.orientation_isEmpty] at hb
      simp_rw [volumeForm, Or.by_cases, dif_neg this.symm, Nat.rec_zero, Basis.det_isEmpty]
  let e : OrthonormalBasis (Fin n.succ) Real E := o.finOrthonormalBasis n.succ_pos 

Depends on / 依赖: Basis.det_isEmpty, Fact.out, Nat.rec_zero, Or.by_cases, OrthonormalBasis, b.toBasis.orientation_isEmpty, classical, convert, det_eq_neg_det_of_opposite_orientation, det_isEmpty, dif_neg, e.det_eq_neg_det_of_opposite_orientation, finOrthonormalBasis, finOrthonormalBasis_orientation, hb.symm, n.succ, n.succ_pos, o.finOrthonormalBasis, o.finOrthonormalBasis_orientation, orientation_isEmpty
-/
theorem volumeForm_robust_neg (b : OrthonormalBasis (Fin n) Real E) (hb : b.toBasis.orientation != o) :
    o.volumeForm = -b.toBasis.det := by
  rcases n with - | n
  · classical
      have : positiveOrientation != o := by rwa [b.toBasis.orientation_isEmpty] at hb
      simp_rw [volumeForm, Or.by_cases, dif_neg this.symm, Nat.rec_zero, Basis.det_isEmpty]
  let e : OrthonormalBasis (Fin n.succ) Real E := o.finOrthonormalBasis n.succ_pos Fact.out
  simp_rw [volumeForm]
  apply e.det_eq_neg_det_of_opposite_orientation b
  convert! hb.symm
  exact o.finOrthonormalBasis_orientation _ _

@[simp]
/--
theorem `volumeForm_neg_orientation` / 定理 `volumeForm_neg_orientation`

English:
theorem volumeForm_neg_orientation
  statement: (-o).volumeForm = -o.volumeForm
  proof: by
  rcases n with - | n
  · refine o.eq_or_eq_neg_of_isEmpty.elim ?_ ?_ <;> rintro rfl
    · simp [volumeForm_zero_neg]
    · simp [volumeForm_zero_neg]
  let e : OrthonormalBasis (Fin n.succ) Real E := o.finOrthonormalBasis n.succ_pos Fact.out
  have h₁ : e.toBasis.orientation = o := o.finOrthonor

中文:
定理 volumeForm_neg_orientation
  结论: (-o).volumeForm = -o.volumeForm
  证明: by
  rcases n with - | n
  · refine o.eq_or_eq_neg_of_isEmpty.elim ?_ ?_ <;> rintro rfl
    · simp [volumeForm_zero_neg]
    · simp [volumeForm_zero_neg]
  let e : OrthonormalBasis (Fin n.succ) Real E := o.finOrthonormalBasis n.succ_pos Fact.out
  have h₁ : e.toBasis.orientation = o := o.finOrthonor

Depends on / 依赖: Fact.out, OrthonormalBasis, e.toBasis.orientation, e.toBasis.orientation_ne_iff_eq_neg, eq_or_eq_neg_of_isEmpty, finOrthonormalBasis, finOrthonormalBasis_orientation, n.succ, n.succ_pos, o.eq_or_eq_neg_of_isEmpty.elim, o.finOrthonormalBasis, o.finOrthonormalBasis_orientation, o.volumeForm_robust, orientation, orientation_ne_iff_eq_neg, succ_pos, toBasis, volumeForm_robust, volumeForm_robust_neg, volumeForm_zero_neg
-/
theorem volumeForm_neg_orientation : (-o).volumeForm = -o.volumeForm := by
  rcases n with - | n
  · refine o.eq_or_eq_neg_of_isEmpty.elim ?_ ?_ <;> rintro rfl
    · simp [volumeForm_zero_neg]
    · simp [volumeForm_zero_neg]
  let e : OrthonormalBasis (Fin n.succ) Real E := o.finOrthonormalBasis n.succ_pos Fact.out
  have h₁ : e.toBasis.orientation = o := o.finOrthonormalBasis_orientation _ _
  have h₂ : e.toBasis.orientation != -o := by
    symm
    rw [e.toBasis.orientation_ne_iff_eq_neg]; rw [h₁]
  rw [o.volumeForm_robust e h₁]; rw [(-o).volumeForm_robust_neg e h₂]

/--
theorem `volumeForm_robust'` / 定理 `volumeForm_robust'`

English:
theorem volumeForm_robust'
  given: (b : OrthonormalBasis (Fin n) Real E) (v : Fin n -> E)
  proof: by
  cases n
  · refine o.eq_or_eq_neg_of_isEmpty.elim ?_ ?_ <;> rintro rfl <;> simp
  · rw [o.volumeForm_robust (b.adjustToOrientation o) (b.orientation_adjustToOrientation o),
      b.abs_det_adjustToOrientation]

中文:
定理 volumeForm_robust'
  条件: (b : OrthonormalBasis (Fin n) 实数 E) (v : Fin n -> E)
  证明: by
  cases n
  · refine o.eq_or_eq_neg_of_isEmpty.elim ?_ ?_ <;> rintro rfl <;> simp
  · rw [o.volumeForm_robust (b.adjustToOrientation o) (b.orientation_adjustToOrientation o),
      b.abs_det_adjustToOrientation]

Depends on / 依赖: abs_det_adjustToOrientation, adjustToOrientation, b.abs_det_adjustToOrientation, b.adjustToOrientation, b.orientation_adjustToOrientation, eq_or_eq_neg_of_isEmpty, o.eq_or_eq_neg_of_isEmpty.elim, o.volumeForm_robust, orientation_adjustToOrientation, volumeForm_robust
-/
theorem volumeForm_robust' (b : OrthonormalBasis (Fin n) Real E) (v : Fin n -> E) :
    |o.volumeForm v| = |b.toBasis.det v| := by
  cases n
  · refine o.eq_or_eq_neg_of_isEmpty.elim ?_ ?_ <;> rintro rfl <;> simp
  · rw [o.volumeForm_robust (b.adjustToOrientation o) (b.orientation_adjustToOrientation o),
      b.abs_det_adjustToOrientation]

/--
theorem `abs_volumeForm_apply_le` / 定理 `abs_volumeForm_apply_le`

English:
theorem abs_volumeForm_apply_le
  given: (v : Fin n -> E)
  statement: |o.volumeForm v| <= ∏ i : Fin n, ‖v i‖
  proof: by
  rcases n with - | n
  · refine o.eq_or_eq_neg_of_isEmpty.elim ?_ ?_ <;> rintro rfl <;> simp
  have : FiniteDimensional Real E := .of_fact_finrank_eq_succ n
  have : finrank Real E = Fintype.card (Fin n.succ) := by simpa using _i.out
  let b : OrthonormalBasis (Fin n.succ) Real E := gramSchmidtO

中文:
定理 abs_volumeForm_apply_le
  条件: (v : Fin n -> E)
  结论: |o.volumeForm v| <= ∏ i : Fin n, ‖v i‖
  证明: by
  rcases n with - | n
  · refine o.eq_or_eq_neg_of_isEmpty.elim ?_ ?_ <;> rintro rfl <;> simp
  have : FiniteDimensional Real E := .of_fact_finrank_eq_succ n
  have : finrank Real E = Fintype.card (Fin n.succ) := by simpa using _i.out
  let b : OrthonormalBasis (Fin n.succ) Real E := gramSchmidtO

Depends on / 依赖: FiniteDimensional, Finset, Finset.abs_prod, Finset.prod_le_prod, Fintype, Fintype.card, OrthonormalBasis, _i.out, abs_prod, b.toBasis.det, eq_or_eq_neg_of_isEmpty, finrank, gramSchmidtOrthonormalBasis, gramSchmidtOrthonormalBasis_det, n.succ, o.eq_or_eq_neg_of_isEmpty.elim, o.volumeForm_robust, of_fact_finrank_eq_succ, prod_le_prod, toBasis
-/
theorem abs_volumeForm_apply_le (v : Fin n -> E) : |o.volumeForm v| <= ∏ i : Fin n, ‖v i‖ := by
  rcases n with - | n
  · refine o.eq_or_eq_neg_of_isEmpty.elim ?_ ?_ <;> rintro rfl <;> simp
  have : FiniteDimensional Real E := .of_fact_finrank_eq_succ n
  have : finrank Real E = Fintype.card (Fin n.succ) := by simpa using _i.out
  let b : OrthonormalBasis (Fin n.succ) Real E := gramSchmidtOrthonormalBasis this v
  have hb : b.toBasis.det v = ∏ i, ⟪b i, v i⟫ := gramSchmidtOrthonormalBasis_det this v
  rw [o.volumeForm_robust' b]; rw [hb]; rw [Finset.abs_prod]
  apply Finset.prod_le_prod
  · intro i _
    positivity
  intro i _
  convert! abs_real_inner_le_norm (b i) (v i)
  simp [b.orthonormal.1 i]

/--
theorem `volumeForm_apply_le` / 定理 `volumeForm_apply_le`

English:
theorem volumeForm_apply_le
  given: (v : Fin n -> E)
  statement: o.volumeForm v <= ∏ i : Fin n, ‖v i‖
  proof: (le_abs_self _).trans (o.abs_volumeForm_apply_le v)

中文:
定理 volumeForm_apply_le
  条件: (v : Fin n -> E)
  结论: o.volumeForm v <= ∏ i : Fin n, ‖v i‖
  证明: (le_abs_self _).trans (o.abs_volumeForm_apply_le v)

Depends on / 依赖: abs_volumeForm_apply_le, le_abs_self, o.abs_volumeForm_apply_le
-/
theorem volumeForm_apply_le (v : Fin n -> E) : o.volumeForm v <= ∏ i : Fin n, ‖v i‖ :=
  (le_abs_self _).trans (o.abs_volumeForm_apply_le v)

/--
theorem `abs_volumeForm_apply_of_pairwise_orthogonal` / 定理 `abs_volumeForm_apply_of_pairwise_orthogonal`

English:
theorem abs_volumeForm_apply_of_pairwise_orthogonal
  statement: {v : Fin n -> E}
  proof: by
  rcases n with - | n
  · refine o.eq_or_eq_neg_of_isEmpty.elim ?_ ?_ <;> rintro rfl <;> simp
  have : FiniteDimensional Real E := .of_fact_finrank_eq_succ n
  have hdim : finrank Real E = Fintype.card (Fin n.succ) := by simpa using _i.out
  let b : OrthonormalBasis (Fin n.succ) Real E := gramSch

中文:
定理 abs_volumeForm_apply_of_pairwise_orthogonal
  结论: {v : Fin n -> E}
  证明: by
  rcases n with - | n
  · refine o.eq_or_eq_neg_of_isEmpty.elim ?_ ?_ <;> rintro rfl <;> simp
  have : FiniteDimensional Real E := .of_fact_finrank_eq_succ n
  have hdim : finrank Real E = Fintype.card (Fin n.succ) := by simpa using _i.out
  let b : OrthonormalBasis (Fin n.succ) Real E := gramSch

Depends on / 依赖: FiniteDimensional, Finset, Finset.abs_prod, Fintype, Fintype.card, OrthonormalBasis, _i.out, abs_prod, b.toBasis.det, eq_or_eq_neg_of_isEmpty, finrank, gramSchmidtOrthonormalBasis, gramSchmidtOrthonormalBasis_det, n.succ, o.eq_or_eq_neg_of_isEmpty.elim, o.volumeForm_robust, of_fact_finrank_eq_succ, toBasis, volumeForm_robust
-/
theorem abs_volumeForm_apply_of_pairwise_orthogonal {v : Fin n -> E}
    (hv : Pairwise fun i j => ⟪v i, v j⟫ = 0) : |o.volumeForm v| = ∏ i : Fin n, ‖v i‖ := by
  rcases n with - | n
  · refine o.eq_or_eq_neg_of_isEmpty.elim ?_ ?_ <;> rintro rfl <;> simp
  have : FiniteDimensional Real E := .of_fact_finrank_eq_succ n
  have hdim : finrank Real E = Fintype.card (Fin n.succ) := by simpa using _i.out
  let b : OrthonormalBasis (Fin n.succ) Real E := gramSchmidtOrthonormalBasis hdim v
  have hb : b.toBasis.det v = ∏ i, ⟪b i, v i⟫ := gramSchmidtOrthonormalBasis_det hdim v
  rw [o.volumeForm_robust' b]; rw [hb]; rw [Finset.abs_prod]
  by_cases! h : exists i, v i = 0
  · obtain ⟨i, hi⟩ := h
    rw [Finset.prod_eq_zero (Finset.mem_univ i)]; rw [Finset.prod_eq_zero (Finset.mem_univ i)] <;>
      simp [hi]
  congr
  ext i
  have hb : b i = ‖v i‖⁻¹ • v i := gramSchmidtOrthonormalBasis_apply_of_orthogonal hdim hv (h i)
  simp only [hb, inner_smul_left, real_inner_self_eq_norm_mul_norm, RCLike.conj_to_real]
  rw [abs_of_nonneg]
  · field
  · positivity

/--
theorem `abs_volumeForm_apply_of_orthonormal` / 定理 `abs_volumeForm_apply_of_orthonormal`

English:
theorem abs_volumeForm_apply_of_orthonormal
  given: (v : OrthonormalBasis (Fin n) Real E)
  proof: by
  simpa [o.volumeForm_robust' v v] using congr_arg abs v.toBasis.det_self

中文:
定理 abs_volumeForm_apply_of_orthonormal
  条件: (v : OrthonormalBasis (Fin n) 实数 E)
  证明: by
  simpa [o.volumeForm_robust' v v] using congr_arg abs v.toBasis.det_self

Depends on / 依赖: congr_arg, det_self, o.volumeForm_robust, toBasis, v.toBasis.det_self, volumeForm_robust
-/
theorem abs_volumeForm_apply_of_orthonormal (v : OrthonormalBasis (Fin n) Real E) :
    |o.volumeForm v| = 1 := by
  simpa [o.volumeForm_robust' v v] using congr_arg abs v.toBasis.det_self

/--
theorem `volumeForm_map` / 定理 `volumeForm_map`

English:
theorem volumeForm_map
  statement: {F : Type*} [NormedAddCommGroup F] [InnerProductSpace Real F]
  proof: by
  rcases n with - | n
  · refine o.eq_or_eq_neg_of_isEmpty.elim ?_ ?_ <;> rintro rfl <;> simp
  let e : OrthonormalBasis (Fin n.succ) Real E := o.finOrthonormalBasis n.succ_pos Fact.out
  have he : e.toBasis.orientation = o :=
    o.finOrthonormalBasis_orientation n.succ_pos Fact.out
  have heφ :

中文:
定理 volumeForm_map
  结论: {F : 类型} [NormedAddCommGroup F] [InnerProductSpace 实数 F]
  证明: by
  rcases n with - | n
  · refine o.eq_or_eq_neg_of_isEmpty.elim ?_ ?_ <;> rintro rfl <;> simp
  let e : OrthonormalBasis (Fin n.succ) Real E := o.finOrthonormalBasis n.succ_pos Fact.out
  have he : e.toBasis.orientation = o :=
    o.finOrthonormalBasis_orientation n.succ_pos Fact.out
  have heφ :

Depends on / 依赖: Fact.out, Orientation, Orientation.map, OrthonormalBasis, e.map, e.toBasis.orientation, e.toBasis.orientation_map, eq_or_eq_neg_of_isEmpty, finOrthonormalBasis, finOrthonormalBasis_orientation, n.succ, n.succ_pos, o.eq_or_eq_neg_of_isEmpty.elim, o.finOrthonormalBasis, o.finOrthonormalBasis_orientation, orientation, orientation_map, succ_pos, toBasis, toBasis.orientation
-/
theorem volumeForm_map {F : Type*} [NormedAddCommGroup F] [InnerProductSpace Real F]
    [Fact (finrank Real F = n)] (φ : E ≃ₗᵢ[Real] F) (x : Fin n -> F) :
    (Orientation.map (Fin n) φ.toLinearEquiv o).volumeForm x = o.volumeForm (φ.symm ∘ x) := by
  rcases n with - | n
  · refine o.eq_or_eq_neg_of_isEmpty.elim ?_ ?_ <;> rintro rfl <;> simp
  let e : OrthonormalBasis (Fin n.succ) Real E := o.finOrthonormalBasis n.succ_pos Fact.out
  have he : e.toBasis.orientation = o :=
    o.finOrthonormalBasis_orientation n.succ_pos Fact.out
  have heφ : (e.map φ).toBasis.orientation = Orientation.map (Fin n.succ) φ.toLinearEquiv o := by
    rw [← he]
    exact e.toBasis.orientation_map φ.toLinearEquiv
  rw [(Orientation.map (Fin n.succ) φ.toLinearEquiv o).volumeForm_robust (e.map φ) heφ]
  rw [o.volumeForm_robust e he]
  simp

/--
theorem `volumeForm_comp_linearIsometryEquiv` / 定理 `volumeForm_comp_linearIsometryEquiv`

English:
theorem volumeForm_comp_linearIsometryEquiv
  statement: (φ : E ≃ₗᵢ[Real] E)
  proof: by
  rcases n with - | n
  · refine o.eq_or_eq_neg_of_isEmpty.elim ?_ ?_ <;> rintro rfl <;> simp
  have : FiniteDimensional Real E := .of_fact_finrank_eq_succ n
  convert! o.volumeForm_map φ (φ ∘ x)
  · symm
    rwa [← o.map_eq_iff_det_pos φ.toLinearEquiv] at hφ
    rw [_i.out]; rw [Fintype.card_fin

中文:
定理 volumeForm_comp_linearIsometryEquiv
  结论: (φ : E ≃ₗᵢ[实数] E)
  证明: by
  rcases n with - | n
  · refine o.eq_or_eq_neg_of_isEmpty.elim ?_ ?_ <;> rintro rfl <;> simp
  have : FiniteDimensional Real E := .of_fact_finrank_eq_succ n
  convert! o.volumeForm_map φ (φ ∘ x)
  · symm
    rwa [← o.map_eq_iff_det_pos φ.toLinearEquiv] at hφ
    rw [_i.out]; rw [Fintype.card_fin

Depends on / 依赖: FiniteDimensional, Fintype, Fintype.card_fin, _i.out, card_fin, convert, eq_or_eq_neg_of_isEmpty, map_eq_iff_det_pos, o.eq_or_eq_neg_of_isEmpty.elim, o.map_eq_iff_det_pos, o.volumeForm_map, of_fact_finrank_eq_succ, toLinearEquiv, volumeForm_map
-/
theorem volumeForm_comp_linearIsometryEquiv (φ : E ≃ₗᵢ[Real] E)
    (hφ : 0 < LinearMap.det (φ.toLinearEquiv : E ->ₗ[Real] E)) (x : Fin n -> E) :
    o.volumeForm (φ ∘ x) = o.volumeForm x := by
  rcases n with - | n
  · refine o.eq_or_eq_neg_of_isEmpty.elim ?_ ?_ <;> rintro rfl <;> simp
  have : FiniteDimensional Real E := .of_fact_finrank_eq_succ n
  convert! o.volumeForm_map φ (φ ∘ x)
  · symm
    rwa [← o.map_eq_iff_det_pos φ.toLinearEquiv] at hφ
    rw [_i.out]; rw [Fintype.card_fin]
  · ext
    simp

end VolumeForm

end Orientation
