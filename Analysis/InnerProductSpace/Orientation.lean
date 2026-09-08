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

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

open Module InnerProductSpace

open scoped RealInnerProductSpace

namespace OrthonormalBasis

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (e f : OrthonormalBasis ι ℝ E)
  (x : Orientation ℝ E ι)

/-- The change-of-basis matrix between two orthonormal bases with the same orientation has
determinant 1. -/
/-
**OrthonormalBasis.det_to_matrix_orthonormalBasis_of_same_orientation** 是 Mathli
b 中的一个定理，位于命名空间 `OrthonormalBasis`。
形式化陈述：det_to_matrix_orthonormalBasis_of_same_orientation (h : e.toBasis.orientat
ion = f.toBasis.orientation) : e.toBasis.det f = 1
参数：h : e.toBasis.orientation = f.toBasis.orientation。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `OrthonormalBasis.det_to_matrix_orthonormalBasis_real`：OrthonormalBasis.d
et_to_matrix_orthonormalBasis_real : a.toBasis.det b = 1 ∨ a.toBasis.det b = -1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.orientation_eq_iff_det_pos`：orientation_eq_iff_det_pos (e₁ 
e₂ : Basis ι R M) : e₁.orientation = e₂.orientation ↔ 0 < e₁.det e₂
· 使用定理 `Not.intro`：∀ {a : Prop}, (a → False) → ¬a
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
（共 41 条，此处仅展示前 30 条）

--- 原说明 ---
The change-of-basis matrix between two orthonormal bases with the same orientati
on has
determinant 1.
-/
theorem det_to_matrix_orthonormalBasis_of_same_orientation
    (h : e.toBasis.orientation = f.toBasis.orientation) : e.toBasis.det f = 1 := by
  apply (e.det_to_matrix_orthonormalBasis_real f).resolve_right
  have : 0 < e.toBasis.det f := by
    rw [e.toBasis.orientation_eq_iff_det_pos] at h
    simpa using h
  linarith

/-- The change-of-basis matrix between two orthonormal bases with the opposite orientations has
determinant -1. -/
/-
**OrthonormalBasis.det_to_matrix_orthonormalBasis_of_opposite_orientation** 是 Ma
thlib 中的一个定理，位于命名空间 `OrthonormalBasis`。
形式化陈述：det_to_matrix_orthonormalBasis_of_opposite_orientation (h : e.toBasis.orie
ntation != f.toBasis.orientation) : e.toBasis.det f = -1
参数：h : e.toBasis.orientation != f.toBasis.orientation。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Module.Basis.orientation_eq_iff_det_pos`：orientation_eq_iff_det_pos (e₁ 
e₂ : Basis ι R M) : e₁.orientation = e₂.orientation ↔ 0 < e₁.det e₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `OrthonormalBasis.det_to_matrix_orthonormalBasis_real`：OrthonormalBasis.d
et_to_matrix_orthonormalBasis_real : a.toBasis.det b = 1 ∨ a.toBasis.det b = -1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α

--- 原说明 ---
The change-of-basis matrix between two orthonormal bases with the opposite orien
tations has
determinant -1.
-/
theorem det_to_matrix_orthonormalBasis_of_opposite_orientation
    (h : e.toBasis.orientation ≠ f.toBasis.orientation) : e.toBasis.det f = -1 := by
  contrapose! h
  simp [e.toBasis.orientation_eq_iff_det_pos,
    (e.det_to_matrix_orthonormalBasis_real f).resolve_right h]

variable {e f}

/-- Two orthonormal bases with the same orientation determine the same "determinant" top-dimensional
form on `E`, and conversely. -/
/-
**OrthonormalBasis.same_orientation_iff_det_eq_det** 是 Mathlib 中的一个定理，位于命名空间 `Or
thonormalBasis`。
形式化陈述：same_orientation_iff_det_eq_det : e.toBasis.det = f.toBasis.det ↔ e.toBasi
s.orientation = f.toBasis.orientation
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlternatingMap.eq_smul_basis_det`：AlternatingMap.eq_smul_basis_det (f : 
M [⋀^ι]->ₗ[R] R) : f = f e • e.det
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `OrthonormalBasis.det_to_matrix_orthonormalBasis_of_same_orientation`：det
_to_matrix_orthonormalBasis_of_same_orientation (h : e.toBasis.orientation = f.t
oBasis.orientation) : e.toBasis.det f = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Two orthonormal bases with the same orientation determine the same "determinant"
 top-dimensional
form on `E`, and conversely.
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

/-- Two orthonormal bases with opposite orientations determine opposite "determinant"
top-dimensional forms on `E`. -/
/-
**OrthonormalBasis.det_eq_neg_det_of_opposite_orientation** 是 Mathlib 中的一个定理，位于命
名空间 `OrthonormalBasis`。
形式化陈述：det_eq_neg_det_of_opposite_orientation (h : e.toBasis.orientation != f.toB
asis.orientation) : e.toBasis.det = -f.toBasis.det
参数：h : e.toBasis.orientation != f.toBasis.orientation。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlternatingMap.eq_smul_basis_det`：AlternatingMap.eq_smul_basis_det (f : 
M [⋀^ι]->ₗ[R] R) : f = f e • e.det
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `OrthonormalBasis.det_to_matrix_orthonormalBasis_of_opposite_orientation`
：det_to_matrix_orthonormalBasis_of_opposite_orientation (h : e.toBasis.orientati
on != f.toBasis.orientation) : e.toBasis.det f = -1
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Two orthonormal bases with opposite orientations determine opposite "determinant
"
top-dimensional forms on `E`.
-/
theorem det_eq_neg_det_of_opposite_orientation (h : e.toBasis.orientation ≠ f.toBasis.orientation) :
    e.toBasis.det = -f.toBasis.det := by
  rw [e.toBasis.det.eq_smul_basis_det f.toBasis]
  simp [e.det_to_matrix_orthonormalBasis_of_opposite_orientation f h]

variable [Nonempty ι]

section AdjustToOrientation

/-- `OrthonormalBasis.adjustToOrientation`, applied to an orthonormal basis, preserves the
property of orthonormality. -/
/-
**OrthonormalBasis.orthonormal_adjustToOrientation** 是 Mathlib 中的一个定理，位于命名空间 `Or
thonormalBasis`。
形式化陈述：orthonormal_adjustToOrientation : Orthonormal Real (e.toBasis.adjustToOrie
ntation x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Orthonormal.orthonormal_of_forall_eq_or_eq_neg`：Orthonormal.orthonormal_
of_forall_eq_or_eq_neg {v w : ι -> E} (hv : Orthonormal 𝕜 v) (hw : forall i, w i
 = v i ∨ w i = -v i) : Orthonormal 𝕜…
· 使用定理 `OrthonormalBasis.orthonormal`：∀ {ι : Type u_1} {𝕜 : Type u_3} [inst : RC
Like 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductS
pace 𝕜 E] [inst_3 …
· 使用定理 `Module.Basis.adjustToOrientation_apply_eq_or_eq_neg`：adjustToOrientation
_apply_eq_or_eq_neg [Nonempty ι] (e : Basis ι R M) (x : Orientation R M ι) (i : 
ι) : e.adjustToOrientation x i = e i ∨ e.…

--- 原说明 ---
`OrthonormalBasis.adjustToOrientation`, applied to an orthonormal basis, preserv
es the
property of orthonormality.
-/
theorem orthonormal_adjustToOrientation : Orthonormal ℝ (e.toBasis.adjustToOrientation x) := by
  apply e.orthonormal.orthonormal_of_forall_eq_or_eq_neg
  simpa using e.toBasis.adjustToOrientation_apply_eq_or_eq_neg x

/-- Given an orthonormal basis and an orientation, return an orthonormal basis giving that
orientation: either the original basis, or one constructed by negating a single (arbitrary) basis
vector. -/
/-
**OrthonormalBasis.adjustToOrientation** 是 Mathlib 中的一个定义，位于命名空间 `OrthonormalBas
is`。
形式化陈述：adjustToOrientation : OrthonormalBasis ι Real E
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `OrthonormalBasis.orthonormal_adjustToOrientation`：orthonormal_adjustToOr
ientation : Orthonormal Real (e.toBasis.adjustToOrientation x)

--- 原说明 ---
Given an orthonormal basis and an orientation, return an orthonormal basis givin
g that
orientation: either the original basis, or one constructed by negating a single 
(arbitrary) basis
vector.
-/
def adjustToOrientation : OrthonormalBasis ι ℝ E :=
  (e.toBasis.adjustToOrientation x).toOrthonormalBasis (e.orthonormal_adjustToOrientation x)
/-
**OrthonormalBasis.toBasis_adjustToOrientation** 是 Mathlib 中的一个定理，位于命名空间 `Orthon
ormalBasis`。
形式化陈述：toBasis_adjustToOrientation : (e.adjustToOrientation x).toBasis = e.toBasi
s.adjustToOrientation x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.toBasis_toOrthonormalBasis`：∀ {ι : Type u_1} {𝕜 : Type u_3}
 [inst : RCLike 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : In
nerProductSpace 𝕜 E] [inst_3 …
· 使用定理 `OrthonormalBasis.orthonormal_adjustToOrientation`：orthonormal_adjustToOr
ientation : Orthonormal Real (e.toBasis.adjustToOrientation x)
-/
theorem toBasis_adjustToOrientation :
    (e.adjustToOrientation x).toBasis = e.toBasis.adjustToOrientation x :=
  (e.toBasis.adjustToOrientation x).toBasis_toOrthonormalBasis _

/-- `adjustToOrientation` gives an orthonormal basis with the required orientation. -/
@[simp]
/-
**OrthonormalBasis.orientation_adjustToOrientation** 是 Mathlib 中的一个定理，位于命名空间 `Or
thonormalBasis`。
形式化陈述：orientation_adjustToOrientation : (e.adjustToOrientation x).toBasis.orient
ation = x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrthonormalBasis.toBasis_adjustToOrientation`：toBasis_adjustToOrientatio
n : (e.adjustToOrientation x).toBasis = e.toBasis.adjustToOrientation x
· 使用定理 `Module.Basis.orientation_adjustToOrientation`：orientation_adjustToOrient
ation [Nonempty ι] (e : Basis ι R M) (x : Orientation R M ι) : (e.adjustToOrient
ation x).orientation = x

--- 原说明 ---
`adjustToOrientation` gives an orthonormal basis with the required orientation.
-/
theorem orientation_adjustToOrientation : (e.adjustToOrientation x).toBasis.orientation = x := by
  rw [e.toBasis_adjustToOrientation]
  exact e.toBasis.orientation_adjustToOrientation x

/-- Every basis vector from `adjustToOrientation` is either that from the original basis or its
negation. -/
/-
**OrthonormalBasis.adjustToOrientation_apply_eq_or_eq_neg** 是 Mathlib 中的一个定理，位于命
名空间 `OrthonormalBasis`。
形式化陈述：adjustToOrientation_apply_eq_or_eq_neg (i : ι) : e.adjustToOrientation x i
 = e i ∨ e.adjustToOrientation x i = -e i
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrthonormalBasis.toBasis_adjustToOrientation`：toBasis_adjustToOrientatio
n : (e.adjustToOrientation x).toBasis = e.toBasis.adjustToOrientation x
· 使用定理 `Module.Basis.adjustToOrientation_apply_eq_or_eq_neg`：adjustToOrientation
_apply_eq_or_eq_neg [Nonempty ι] (e : Basis ι R M) (x : Orientation R M ι) (i : 
ι) : e.adjustToOrientation x i = e i ∨ e.…

--- 原说明 ---
Every basis vector from `adjustToOrientation` is either that from the original b
asis or its
negation.
-/
theorem adjustToOrientation_apply_eq_or_eq_neg (i : ι) :
    e.adjustToOrientation x i = e i ∨ e.adjustToOrientation x i = -e i := by
  simpa [← e.toBasis_adjustToOrientation] using
    e.toBasis.adjustToOrientation_apply_eq_or_eq_neg x i
/-
**OrthonormalBasis.det_adjustToOrientation** 是 Mathlib 中的一个定理，位于命名空间 `Orthonorma
lBasis`。
形式化陈述：det_adjustToOrientation : (e.adjustToOrientation x).toBasis.det = e.toBasi
s.det ∨ (e.adjustToOrientation x).toBasis.det = -e.toBasis.det
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.det_adjustToOrientation`：det_adjustToOrientation [Nonempty 
ι] (e : Basis ι R M) (x : Orientation R M ι) : (e.adjustToOrientation x).det = e
.det ∨ (e.adjustToOrientat…
-/
theorem det_adjustToOrientation :
    (e.adjustToOrientation x).toBasis.det = e.toBasis.det ∨
      (e.adjustToOrientation x).toBasis.det = -e.toBasis.det := by
  simpa using! e.toBasis.det_adjustToOrientation x
/-
**OrthonormalBasis.abs_det_adjustToOrientation** 是 Mathlib 中的一个定理，位于命名空间 `Orthon
ormalBasis`。
形式化陈述：abs_det_adjustToOrientation (v : ι -> E) : |(e.adjustToOrientation x).toBa
sis.det v| = |e.toBasis.det v|
参数：v : ι -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrthonormalBasis.toBasis_adjustToOrientation`：toBasis_adjustToOrientatio
n : (e.adjustToOrientation x).toBasis = e.toBasis.adjustToOrientation x
· 使用定理 `Module.Basis.abs_det_adjustToOrientation`：abs_det_adjustToOrientation [N
onempty ι] (e : Basis ι R M) (x : Orientation R M ι) (v : ι -> M) : |(e.adjustTo
Orientation x).det v| = |e.det…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem abs_det_adjustToOrientation (v : ι → E) :
    |(e.adjustToOrientation x).toBasis.det v| = |e.toBasis.det v| := by
  simp [toBasis_adjustToOrientation]

end AdjustToOrientation

end OrthonormalBasis

namespace Orientation

variable {n : ℕ}

open OrthonormalBasis

/-- An orthonormal basis, indexed by `Fin n`, with the given orientation. -/
/-
**Orientation.finOrthonormalBasis** 是 Mathlib 中的一个定义，位于命名空间 `Orientation`。
形式化陈述：{E : Type u_1} →   [inst : NormedAddCommGroup E] →     [inst_1 : InnerProd
uctSpace ℝ E] →       {n : ℕ} → 0 < n → Module.finrank ℝ E = n → Orientation ℝ E
 (Fin n) → OrthonormalBasis (Fin n) ℝ E
参数：Fin n；Fin n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An orthonormal basis, indexed by `Fin n`, with the given orientation.
-/
protected def finOrthonormalBasis (hn : 0 < n) (h : finrank ℝ E = n) (x : Orientation ℝ E (Fin n)) :
    OrthonormalBasis (Fin n) ℝ E := by
  haveI := Fin.pos_iff_nonempty.1 hn
  haveI : FiniteDimensional ℝ E := .of_finrank_pos <| h.symm ▸ hn
  exact ((@stdOrthonormalBasis _ _ _ _ _ this).reindex <| finCongr h).adjustToOrientation x

/-- `Orientation.finOrthonormalBasis` gives a basis with the required orientation. -/
@[simp]
/-
**Orientation.finOrthonormalBasis_orientation** 是 Mathlib 中的一个定理，位于命名空间 `Orienta
tion`。
形式化陈述：finOrthonormalBasis_orientation (hn : 0 < n) (h : finrank Real E = n) (x :
 Orientation Real E (Fin n)) : (x.finOrthonormalBasis hn h).toBasis.orientation 
= x
参数：hn : 0 < n；h : finrank Real E = n；x : Orientation Real E (Fin n)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Fin.pos_iff_nonempty`：∀ {n : ℕ}, 0 < n ↔ Nonempty (Fin n)
· 使用定理 `FiniteDimensional.of_finrank_pos`：of_finrank_pos (h : 0 < finrank K V) :
 FiniteDimensional K V
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrthonormalBasis.orientation_adjustToOrientation`：orientation_adjustToOr
ientation : (e.adjustToOrientation x).toBasis.orientation = x

--- 原说明 ---
`Orientation.finOrthonormalBasis` gives a basis with the required orientation.
-/
theorem finOrthonormalBasis_orientation (hn : 0 < n) (h : finrank ℝ E = n)
    (x : Orientation ℝ E (Fin n)) : (x.finOrthonormalBasis hn h).toBasis.orientation = x := by
  have := Fin.pos_iff_nonempty.1 hn
  have : FiniteDimensional ℝ E := .of_finrank_pos <| h.symm ▸ hn
  exact ((@stdOrthonormalBasis _ _ _ _ _ this).reindex <|
    finCongr h).orientation_adjustToOrientation x

section VolumeForm

variable [_i : Fact (finrank ℝ E = n)] (o : Orientation ℝ E (Fin n))

/-- The volume form on an oriented real inner product space, a nonvanishing top-dimensional
alternating form uniquely defined by compatibility with the orientation and inner product structure.
-/
irreducible_def volumeForm : E [⋀^Fin n]→ₗ[ℝ] ℝ := by
  classical
    cases n with
    | zero =>
      let opos : E [⋀^Fin 0]→ₗ[ℝ] ℝ := .constOfIsEmpty ℝ E (Fin 0) (1 : ℝ)
      exact o.eq_or_eq_neg_of_isEmpty.by_cases (fun _ => opos) fun _ => -opos
    | succ n => exact (o.finOrthonormalBasis n.succ_pos _i.out).toBasis.det

@[simp]
/-
**Orientation.volumeForm_zero_pos** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：volumeForm_zero_pos [_i : Fact (finrank Real E = 0)] : Orientation.volumeF
orm (positiveOrientation : Orientation Real E (Fin 0)) = AlternatingMap.constLin
earEquivOfIsEmpty 1
参数：finrank Real E = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `Orientation.volumeForm_def`：∀ {E : Type u_2} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] {n : ℕ}   [_i : Fact (Module.finrank ℝ E = n
)] (o : Orientat…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `AlternatingMap.constLinearEquivOfIsEmpty_apply`：∀ {ι : Type u_7} {R' : T
ype u_10} {M'' : Type u_11} {N'' : Type u_13} [inst : CommSemiring R']   [inst_1
 : AddCommMonoid M''] [inst_2 : AddC…
-/
theorem volumeForm_zero_pos [_i : Fact (finrank ℝ E = 0)] :
    Orientation.volumeForm (positiveOrientation : Orientation ℝ E (Fin 0)) =
      AlternatingMap.constLinearEquivOfIsEmpty 1 := by
  simp [volumeForm, Or.by_cases]

set_option backward.isDefEq.respectTransparency.types false in
/-
**Orientation.volumeForm_zero_neg** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：volumeForm_zero_neg [_i : Fact (finrank Real E = 0)] : Orientation.volumeF
orm (-positiveOrientation : Orientation Real E (Fin 0)) = -AlternatingMap.constL
inearEquivOfIsEmpty 1
参数：finrank Real E = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.volumeForm_def`：∀ {E : Type u_2} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] {n : ℕ}   [_i : Fact (Module.finrank ℝ E = n
)] (o : Orientat…
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_ne_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a ≠
 0 ↔ a ≠ 0
· 使用定理 `ray_eq_iff`：ray_eq_iff {v₁ v₂ : M} (hv₁ : v₁ != 0) (hv₂ : v₂ != 0) : ray
OfNeZero R _ hv₁ = rayOfNeZero R _ hv₂ ↔ SameRay R v₁ v₂
· 使用定理 `SameRay.sameRay_comm`：sameRay_comm : SameRay R x y ↔ SameRay R y x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `AlternatingMap.constLinearEquivOfIsEmpty_apply`：∀ {ι : Type u_7} {R' : T
ype u_10} {M'' : Type u_11} {N'' : Type u_13} [inst : CommSemiring R']   [inst_1
 : AddCommMonoid M''] [inst_2 : AddC…
· 使用定理 `AlternatingMap.constLinearEquivOfIsEmpty_symm_apply`：∀ {ι : Type u_7} {R
' : Type u_10} {M'' : Type u_11} {N'' : Type u_13} [inst : CommSemiring R']   [i
nst_1 : AddCommMonoid M''] [inst_2 : AddC…
· 使用定理 `Matrix.zero_empty`：∀ {α : Type u_1} [inst : Zero α], 0 = ![]
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `AlternatingMap.constOfIsEmpty_apply`：∀ (R : Type u_1) [inst : Semiring R
] (M : Type u_2) [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {N : 
Type u_3} [inst_3 : AddCo…
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `eq_zero_of_sameRay_self_neg`：eq_zero_of_sameRay_self_neg [IsDomain R] [I
sTorsionFree R M] (h : SameRay R x (-x)) : x = 0
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
-/
theorem volumeForm_zero_neg [_i : Fact (finrank ℝ E = 0)] :
    Orientation.volumeForm (-positiveOrientation : Orientation ℝ E (Fin 0)) =
      -AlternatingMap.constLinearEquivOfIsEmpty 1 := by
  simp_rw [volumeForm, Or.by_cases, positiveOrientation]
  apply if_neg
  simp only [neg_rayOfNeZero]
  rw [ray_eq_iff, SameRay.sameRay_comm]
  intro h
  simpa using
    congr_arg AlternatingMap.constLinearEquivOfIsEmpty.symm (eq_zero_of_sameRay_self_neg h)

/-- The volume form on an oriented real inner product space can be evaluated as the determinant with
respect to any orthonormal basis of the space compatible with the orientation. -/
/-
**Orientation.volumeForm_robust** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：volumeForm_robust (b : OrthonormalBasis (Fin n) Real E) (hb : b.toBasis.or
ientation = o) : o.volumeForm = b.toBasis.det
参数：b : OrthonormalBasis (Fin n) Real E；hb : b.toBasis.orientation = o。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.orientation_isEmpty`：orientation_isEmpty [IsEmpty ι] (b : B
asis ι R M) : b.orientation = positiveOrientation
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.volumeForm_def`：∀ {E : Type u_2} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] {n : ℕ}   [_i : Fact (Module.finrank ℝ E = n
)] (o : Orientat…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Module.Basis.det_isEmpty`：det_isEmpty [IsEmpty ι] : e.det = AlternatingM
ap.constOfIsEmpty R M ι 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `OrthonormalBasis.same_orientation_iff_det_eq_det`：same_orientation_iff_d
et_eq_det : e.toBasis.det = f.toBasis.det ↔ e.toBasis.orientation = f.toBasis.or
ientation
· 使用定理 `Orientation.finOrthonormalBasis_orientation`：finOrthonormalBasis_orienta
tion (hn : 0 < n) (h : finrank Real E = n) (x : Orientation Real E (Fin n)) : (x
.finOrthonormalBasis hn h).toBasi…

--- 原说明 ---
The volume form on an oriented real inner product space can be evaluated as the 
determinant with
respect to any orthonormal basis of the space compatible with the orientation.
-/
theorem volumeForm_robust (b : OrthonormalBasis (Fin n) ℝ E) (hb : b.toBasis.orientation = o) :
    o.volumeForm = b.toBasis.det := by
  cases n
  · classical
      have : o = positiveOrientation := hb.symm.trans b.toBasis.orientation_isEmpty
      simp_rw [volumeForm, Or.by_cases, dif_pos this, Nat.rec_zero, Basis.det_isEmpty]
  · simp_rw [volumeForm]
    rw [same_orientation_iff_det_eq_det, hb]
    exact o.finOrthonormalBasis_orientation _ _

/-- The volume form on an oriented real inner product space can be evaluated as the determinant with
respect to any orthonormal basis of the space compatible with the orientation. -/
/-
**Orientation.volumeForm_robust_neg** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：volumeForm_robust_neg (b : OrthonormalBasis (Fin n) Real E) (hb : b.toBasi
s.orientation != o) : o.volumeForm = -b.toBasis.det
参数：b : OrthonormalBasis (Fin n) Real E；hb : b.toBasis.orientation != o。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.orientation_isEmpty`：orientation_isEmpty [IsEmpty ι] (b : B
asis ι R M) : b.orientation = positiveOrientation
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Orientation.volumeForm_def`：∀ {E : Type u_2} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] {n : ℕ}   [_i : Fact (Module.finrank ℝ E = n
)] (o : Orientat…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Module.Basis.det_isEmpty`：det_isEmpty [IsEmpty ι] : e.det = AlternatingM
ap.constOfIsEmpty R M ι 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `OrthonormalBasis.det_eq_neg_det_of_opposite_orientation`：det_eq_neg_det_
of_opposite_orientation (h : e.toBasis.orientation != f.toBasis.orientation) : e
.toBasis.det = -f.toBasis.det
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Orientation.finOrthonormalBasis_orientation`：finOrthonormalBasis_orienta
tion (hn : 0 < n) (h : finrank Real E = n) (x : Orientation Real E (Fin n)) : (x
.finOrthonormalBasis hn h).toBasi…

--- 原说明 ---
The volume form on an oriented real inner product space can be evaluated as the 
determinant with
respect to any orthonormal basis of the space compatible with the orientation.
-/
theorem volumeForm_robust_neg (b : OrthonormalBasis (Fin n) ℝ E) (hb : b.toBasis.orientation ≠ o) :
    o.volumeForm = -b.toBasis.det := by
  rcases n with - | n
  · classical
      have : positiveOrientation ≠ o := by rwa [b.toBasis.orientation_isEmpty] at hb
      simp_rw [volumeForm, Or.by_cases, dif_neg this.symm, Nat.rec_zero, Basis.det_isEmpty]
  let e : OrthonormalBasis (Fin n.succ) ℝ E := o.finOrthonormalBasis n.succ_pos Fact.out
  simp_rw [volumeForm]
  apply e.det_eq_neg_det_of_opposite_orientation b
  convert! hb.symm
  exact o.finOrthonormalBasis_orientation _ _

@[simp]
/-
**Orientation.volumeForm_neg_orientation** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`
。
形式化陈述：volumeForm_neg_orientation : (-o).volumeForm = -o.volumeForm
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Orientation.eq_or_eq_neg_of_isEmpty`：eq_or_eq_neg_of_isEmpty [IsEmpty ι]
 (o : Orientation R M ι) : o = positiveOrientation ∨ o = -positiveOrientation
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.volumeForm_zero_neg`：volumeForm_zero_neg [_i : Fact (finrank
 Real E = 0)] : Orientation.volumeForm (-positiveOrientation : Orientation Real 
E (Fin 0)) = -Alterna…
· 使用定理 `AlternatingMap.constLinearEquivOfIsEmpty_apply`：∀ {ι : Type u_7} {R' : T
ype u_10} {M'' : Type u_11} {N'' : Type u_13} [inst : CommSemiring R']   [inst_1
 : AddCommMonoid M''] [inst_2 : AddC…
· 使用定理 `Orientation.volumeForm_zero_pos`：volumeForm_zero_pos [_i : Fact (finrank
 Real E = 0)] : Orientation.volumeForm (positiveOrientation : Orientation Real E
 (Fin 0)) = Alternati…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Orientation.volumeForm.congr_simp`：∀ {E : Type u_2} [inst : NormedAddCom
mGroup E] [inst_1 : InnerProductSpace ℝ E] {n : ℕ}   [_i : Fact (Module.finrank 
ℝ E = n)] (o o_1 : Orie…
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Orientation.finOrthonormalBasis_orientation`：finOrthonormalBasis_orienta
tion (hn : 0 < n) (h : finrank Real E = n) (x : Orientation Real E (Fin n)) : (x
.finOrthonormalBasis hn h).toBasi…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Module.Basis.orientation_ne_iff_eq_neg`：orientation_ne_iff_eq_neg (e : B
asis ι R M) (x : Orientation R M ι) : x != e.orientation ↔ x = -e.orientation
· 使用定理 `Orientation.volumeForm_robust`：volumeForm_robust (b : OrthonormalBasis (
Fin n) Real E) (hb : b.toBasis.orientation = o) : o.volumeForm = b.toBasis.det
· 使用定理 `Orientation.volumeForm_robust_neg`：volumeForm_robust_neg (b : Orthonorma
lBasis (Fin n) Real E) (hb : b.toBasis.orientation != o) : o.volumeForm = -b.toB
asis.det
-/
theorem volumeForm_neg_orientation : (-o).volumeForm = -o.volumeForm := by
  rcases n with - | n
  · refine o.eq_or_eq_neg_of_isEmpty.elim ?_ ?_ <;> rintro rfl
    · simp [volumeForm_zero_neg]
    · simp [volumeForm_zero_neg]
  let e : OrthonormalBasis (Fin n.succ) ℝ E := o.finOrthonormalBasis n.succ_pos Fact.out
  have h₁ : e.toBasis.orientation = o := o.finOrthonormalBasis_orientation _ _
  have h₂ : e.toBasis.orientation ≠ -o := by
    symm
    rw [e.toBasis.orientation_ne_iff_eq_neg, h₁]
  rw [o.volumeForm_robust e h₁, (-o).volumeForm_robust_neg e h₂]
/-
**Orientation.volumeForm_robust'** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：volumeForm_robust' (b : OrthonormalBasis (Fin n) Real E) (v : Fin n -> E) 
: |o.volumeForm v| = |b.toBasis.det v|
参数：b : OrthonormalBasis (Fin n) Real E；v : Fin n -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Orientation.eq_or_eq_neg_of_isEmpty`：eq_or_eq_neg_of_isEmpty [IsEmpty ι]
 (o : Orientation R M ι) : o = positiveOrientation ∨ o = -positiveOrientation
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Orientation.volumeForm_zero_pos`：volumeForm_zero_pos [_i : Fact (finrank
 Real E = 0)] : Orientation.volumeForm (positiveOrientation : Orientation Real E
 (Fin 0)) = Alternati…
· 使用定理 `AlternatingMap.constLinearEquivOfIsEmpty_apply`：∀ {ι : Type u_7} {R' : T
ype u_10} {M'' : Type u_11} {N'' : Type u_13} [inst : CommSemiring R']   [inst_1
 : AddCommMonoid M''] [inst_2 : AddC…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `AlternatingMap.constOfIsEmpty_apply`：∀ (R : Type u_1) [inst : Semiring R
] (M : Type u_2) [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {N : 
Type u_3} [inst_3 : AddCo…
· 使用定理 `abs_one`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] [IsOr
deredRing α], |1| = 1
· 使用定理 `Module.Basis.det_isEmpty`：det_isEmpty [IsEmpty ι] : e.det = AlternatingM
ap.constOfIsEmpty R M ι 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Orientation.volumeForm_neg_orientation`：volumeForm_neg_orientation : (-o
).volumeForm = -o.volumeForm
· 使用定理 `abs_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (a : 
α), |(-a)| = |a|
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Orientation.volumeForm_robust`：volumeForm_robust (b : OrthonormalBasis (
Fin n) Real E) (hb : b.toBasis.orientation = o) : o.volumeForm = b.toBasis.det
· 使用定理 `OrthonormalBasis.orientation_adjustToOrientation`：orientation_adjustToOr
ientation : (e.adjustToOrientation x).toBasis.orientation = x
· 使用定理 `OrthonormalBasis.abs_det_adjustToOrientation`：abs_det_adjustToOrientatio
n (v : ι -> E) : |(e.adjustToOrientation x).toBasis.det v| = |e.toBasis.det v|
-/
theorem volumeForm_robust' (b : OrthonormalBasis (Fin n) ℝ E) (v : Fin n → E) :
    |o.volumeForm v| = |b.toBasis.det v| := by
  cases n
  · refine o.eq_or_eq_neg_of_isEmpty.elim ?_ ?_ <;> rintro rfl <;> simp
  · rw [o.volumeForm_robust (b.adjustToOrientation o) (b.orientation_adjustToOrientation o),
      b.abs_det_adjustToOrientation]

/-- Let `v` be an indexed family of `n` vectors in an oriented `n`-dimensional real inner
product space `E`. The output of the volume form of `E` when evaluated on `v` is bounded in absolute
value by the product of the norms of the vectors `v i`. -/
/-
**Orientation.abs_volumeForm_apply_le** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：abs_volumeForm_apply_le (v : Fin n -> E) : |o.volumeForm v| <= ∏ i : Fin n
, ‖v i‖
参数：v : Fin n -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Orientation.eq_or_eq_neg_of_isEmpty`：eq_or_eq_neg_of_isEmpty [IsEmpty ι]
 (o : Orientation R M ι) : o = positiveOrientation ∨ o = -positiveOrientation
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Orientation.volumeForm_zero_pos`：volumeForm_zero_pos [_i : Fact (finrank
 Real E = 0)] : Orientation.volumeForm (positiveOrientation : Orientation Real E
 (Fin 0)) = Alternati…
· 使用定理 `AlternatingMap.constLinearEquivOfIsEmpty_apply`：∀ {ι : Type u_7} {R' : T
ype u_10} {M'' : Type u_11} {N'' : Type u_13} [inst : CommSemiring R']   [inst_1
 : AddCommMonoid M''] [inst_2 : AddC…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `AlternatingMap.constOfIsEmpty_apply`：∀ (R : Type u_1) [inst : Semiring R
] (M : Type u_2) [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {N : 
Type u_3} [inst_3 : AddCo…
· 使用定理 `abs_one`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] [IsOr
deredRing α], |1| = 1
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.univ_eq_empty`：univ_eq_empty [IsEmpty α] : (univ : Finset α) = ∅
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Orientation.volumeForm_neg_orientation`：volumeForm_neg_orientation : (-o
).volumeForm = -o.volumeForm
· 使用定理 `abs_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (a : 
α), |(-a)| = |a|
· 使用定理 `FiniteDimensional.of_fact_finrank_eq_succ`：of_fact_finrank_eq_succ (n : 
Nat) [hn : Fact (finrank K V = n + 1)] : FiniteDimensional K V
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `IsWellOrder.toIsWellFounded`：∀ {α : Type u} {r : α → α → Prop} [self : I
sWellOrder α r], IsWellFounded α r
· 使用定理 `Fin.Lt.isWellOrder`：∀ (n : ℕ), IsWellOrder (Fin n) fun x1 x2 => x1 < x2
· 使用定理 `InnerProductSpace.gramSchmidtOrthonormalBasis_det`：gramSchmidtOrthonorma
lBasis_det [DecidableEq ι] : (gramSchmidtOrthonormalBasis h f).toBasis.det f = ∏
 i, ⟪gramSchmidtOrthonormalBasis h f i,…
· 使用定理 `Orientation.volumeForm_robust'`：volumeForm_robust' (b : OrthonormalBasis
 (Fin n) Real E) (v : Fin n -> E) : |o.volumeForm v| = |b.toBasis.det v|
· 使用引理 `Finset.abs_prod`：abs_prod [CommRing R] [LinearOrder R] [IsStrictOrderedR
ing R] (s : Finset ι) (f : ι -> R) : |∏ x in s, f x| = ∏ x in s, |f x|
· 使用引理 `Finset.prod_le_prod`：prod_le_prod (h0 : forall i in s, 0 <= f i) (h1 : f
orall i in s, f i <= g i) : ∏ i in s, f i <= ∏ i in s, g i
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
Let `v` be an indexed family of `n` vectors in an oriented `n`-dimensional real 
inner
product space `E`. The output of the volume form of `E` when evaluated on `v` is
 bounded in absolute
value by the product of the norms of the vectors `v i`.
-/
theorem abs_volumeForm_apply_le (v : Fin n → E) : |o.volumeForm v| ≤ ∏ i : Fin n, ‖v i‖ := by
  rcases n with - | n
  · refine o.eq_or_eq_neg_of_isEmpty.elim ?_ ?_ <;> rintro rfl <;> simp
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  have : finrank ℝ E = Fintype.card (Fin n.succ) := by simpa using _i.out
  let b : OrthonormalBasis (Fin n.succ) ℝ E := gramSchmidtOrthonormalBasis this v
  have hb : b.toBasis.det v = ∏ i, ⟪b i, v i⟫ := gramSchmidtOrthonormalBasis_det this v
  rw [o.volumeForm_robust' b, hb, Finset.abs_prod]
  apply Finset.prod_le_prod
  · intro i _
    positivity
  intro i _
  convert! abs_real_inner_le_norm (b i) (v i)
  simp [b.orthonormal.1 i]
/-
**Orientation.volumeForm_apply_le** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：volumeForm_apply_le (v : Fin n -> E) : o.volumeForm v <= ∏ i : Fin n, ‖v i
‖
参数：v : Fin n -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_abs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (
a : α), a ≤ |a|
· 使用定理 `Orientation.abs_volumeForm_apply_le`：abs_volumeForm_apply_le (v : Fin n 
-> E) : |o.volumeForm v| <= ∏ i : Fin n, ‖v i‖
-/
theorem volumeForm_apply_le (v : Fin n → E) : o.volumeForm v ≤ ∏ i : Fin n, ‖v i‖ :=
  (le_abs_self _).trans (o.abs_volumeForm_apply_le v)

/-- Let `v` be an indexed family of `n` orthogonal vectors in an oriented `n`-dimensional
real inner product space `E`. The output of the volume form of `E` when evaluated on `v` is, up to
sign, the product of the norms of the vectors `v i`. -/
/-
**Orientation.abs_volumeForm_apply_of_pairwise_orthogonal** 是 Mathlib 中的一个定理，位于命
名空间 `Orientation`。
形式化陈述：abs_volumeForm_apply_of_pairwise_orthogonal {v : Fin n -> E} (hv : Pairwis
e fun i j => ⟪v i, v j⟫ = 0) : |o.volumeForm v| = ∏ i : Fin n, ‖v i‖
参数：hv : Pairwise fun i j => ⟪v i, v j⟫ = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Orientation.eq_or_eq_neg_of_isEmpty`：eq_or_eq_neg_of_isEmpty [IsEmpty ι]
 (o : Orientation R M ι) : o = positiveOrientation ∨ o = -positiveOrientation
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Orientation.volumeForm_zero_pos`：volumeForm_zero_pos [_i : Fact (finrank
 Real E = 0)] : Orientation.volumeForm (positiveOrientation : Orientation Real E
 (Fin 0)) = Alternati…
· 使用定理 `AlternatingMap.constLinearEquivOfIsEmpty_apply`：∀ {ι : Type u_7} {R' : T
ype u_10} {M'' : Type u_11} {N'' : Type u_13} [inst : CommSemiring R']   [inst_1
 : AddCommMonoid M''] [inst_2 : AddC…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `AlternatingMap.constOfIsEmpty_apply`：∀ (R : Type u_1) [inst : Semiring R
] (M : Type u_2) [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {N : 
Type u_3} [inst_3 : AddCo…
· 使用定理 `abs_one`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] [IsOr
deredRing α], |1| = 1
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.univ_eq_empty`：univ_eq_empty [IsEmpty α] : (univ : Finset α) = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Orientation.volumeForm_neg_orientation`：volumeForm_neg_orientation : (-o
).volumeForm = -o.volumeForm
· 使用定理 `abs_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (a : 
α), |(-a)| = |a|
· 使用定理 `FiniteDimensional.of_fact_finrank_eq_succ`：of_fact_finrank_eq_succ (n : 
Nat) [hn : Fact (finrank K V = n + 1)] : FiniteDimensional K V
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `IsWellOrder.toIsWellFounded`：∀ {α : Type u} {r : α → α → Prop} [self : I
sWellOrder α r], IsWellFounded α r
· 使用定理 `Fin.Lt.isWellOrder`：∀ (n : ℕ), IsWellOrder (Fin n) fun x1 x2 => x1 < x2
· 使用定理 `InnerProductSpace.gramSchmidtOrthonormalBasis_det`：gramSchmidtOrthonorma
lBasis_det [DecidableEq ι] : (gramSchmidtOrthonormalBasis h f).toBasis.det f = ∏
 i, ⟪gramSchmidtOrthonormalBasis h f i,…
· 使用定理 `Orientation.volumeForm_robust'`：volumeForm_robust' (b : OrthonormalBasis
 (Fin n) Real E) (v : Fin n -> E) : |o.volumeForm v| = |b.toBasis.det v|
· 使用引理 `Finset.abs_prod`：abs_prod [CommRing R] [LinearOrder R] [IsStrictOrderedR
ing R] (s : Finset ι) (f : ι -> R) : |∏ x in s, f x| = ∏ x in s, |f x|
· 使用引理 `Finset.prod_eq_zero`：prod_eq_zero (hi : i in s) (h : f i = 0) : ∏ j in s
, f j = 0
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `inner_zero_right`：inner_zero_right (x : E) : ⟪x, 0⟫ = 0
· 使用定理 `abs_zero`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [Add
LeftMono α], |0| = 0
（共 65 条，此处仅展示前 30 条）

--- 原说明 ---
Let `v` be an indexed family of `n` orthogonal vectors in an oriented `n`-dimens
ional
real inner product space `E`. The output of the volume form of `E` when evaluate
d on `v` is, up to
sign, the product of the norms of the vectors `v i`.
-/
theorem abs_volumeForm_apply_of_pairwise_orthogonal {v : Fin n → E}
    (hv : Pairwise fun i j => ⟪v i, v j⟫ = 0) : |o.volumeForm v| = ∏ i : Fin n, ‖v i‖ := by
  rcases n with - | n
  · refine o.eq_or_eq_neg_of_isEmpty.elim ?_ ?_ <;> rintro rfl <;> simp
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  have hdim : finrank ℝ E = Fintype.card (Fin n.succ) := by simpa using _i.out
  let b : OrthonormalBasis (Fin n.succ) ℝ E := gramSchmidtOrthonormalBasis hdim v
  have hb : b.toBasis.det v = ∏ i, ⟪b i, v i⟫ := gramSchmidtOrthonormalBasis_det hdim v
  rw [o.volumeForm_robust' b, hb, Finset.abs_prod]
  by_cases! h : ∃ i, v i = 0
  · obtain ⟨i, hi⟩ := h
    rw [Finset.prod_eq_zero (Finset.mem_univ i), Finset.prod_eq_zero (Finset.mem_univ i)] <;>
      simp [hi]
  congr
  ext i
  have hb : b i = ‖v i‖⁻¹ • v i := gramSchmidtOrthonormalBasis_apply_of_orthogonal hdim hv (h i)
  simp only [hb, inner_smul_left, real_inner_self_eq_norm_mul_norm, RCLike.conj_to_real]
  rw [abs_of_nonneg]
  · field
  · positivity

/-- The output of the volume form of an oriented real inner product space `E` when evaluated on an
orthonormal basis is ±1. -/
/-
**Orientation.abs_volumeForm_apply_of_orthonormal** 是 Mathlib 中的一个定理，位于命名空间 `Ori
entation`。
形式化陈述：abs_volumeForm_apply_of_orthonormal (v : OrthonormalBasis (Fin n) Real E) 
: |o.volumeForm v| = 1
参数：v : OrthonormalBasis (Fin n) Real E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.volumeForm_robust'`：volumeForm_robust' (b : OrthonormalBasis
 (Fin n) Real E) (v : Fin n -> E) : |o.volumeForm v| = |b.toBasis.det v|
· 使用定理 `abs_one`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] [IsOr
deredRing α], |1| = 1
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Module.Basis.det_self`：det_self : e.det e = 1

--- 原说明 ---
The output of the volume form of an oriented real inner product space `E` when e
valuated on an
orthonormal basis is ±1.
-/
theorem abs_volumeForm_apply_of_orthonormal (v : OrthonormalBasis (Fin n) ℝ E) :
    |o.volumeForm v| = 1 := by
  simpa [o.volumeForm_robust' v v] using congr_arg abs v.toBasis.det_self
/-
**Orientation.volumeForm_map** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：volumeForm_map {F : Type*} [NormedAddCommGroup F] [InnerProductSpace Real 
F] [Fact (finrank Real F = n)] (φ : E ≃ₗᵢ[Real] F) (x : Fin n -> F) : (Orientati
on.map (Fin n) φ.toLinearEquiv o).volumeForm x = o.volumeForm (φ.symm ∘ x)
参数：finrank Real F = n；φ : E ≃ₗᵢ[Real] F；x : Fin n -> F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Orientation.eq_or_eq_neg_of_isEmpty`：eq_or_eq_neg_of_isEmpty [IsEmpty ι]
 (o : Orientation R M ι) : o = positiveOrientation ∨ o = -positiveOrientation
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Orientation.volumeForm_zero_pos`：volumeForm_zero_pos [_i : Fact (finrank
 Real E = 0)] : Orientation.volumeForm (positiveOrientation : Orientation Real E
 (Fin 0)) = Alternati…
· 使用定理 `AlternatingMap.constLinearEquivOfIsEmpty_apply`：∀ {ι : Type u_7} {R' : T
ype u_10} {M'' : Type u_11} {N'' : Type u_13} [inst : CommSemiring R']   [inst_1
 : AddCommMonoid M''] [inst_2 : AddC…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `AlternatingMap.constOfIsEmpty_apply`：∀ (R : Type u_1) [inst : Semiring R
] (M : Type u_2) [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {N : 
Type u_3} [inst_3 : AddCo…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Orientation.volumeForm.congr_simp`：∀ {E : Type u_2} [inst : NormedAddCom
mGroup E] [inst_1 : InnerProductSpace ℝ E] {n : ℕ}   [_i : Fact (Module.finrank 
ℝ E = n)] (o o_1 : Orie…
· 使用定理 `Orientation.map_neg`：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : Part
ialOrder R] [inst_2 : IsStrictOrderedRing R] {M : Type u_2}   {N : Type u_3} [in
st_3 : Ad…
· 使用定理 `Orientation.volumeForm_neg_orientation`：volumeForm_neg_orientation : (-o
).volumeForm = -o.volumeForm
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Orientation.finOrthonormalBasis_orientation`：finOrthonormalBasis_orienta
tion (hn : 0 < n) (h : finrank Real E = n) (x : Orientation Real E (Fin n)) : (x
.finOrthonormalBasis hn h).toBasi…
· 使用定理 `Module.Basis.orientation_map`：orientation_map (e : Basis ι R M) (f : M ≃
ₗ[R] N) : (e.map f).orientation = Orientation.map ι f e.orientation
· 使用定理 `Orientation.volumeForm_robust`：volumeForm_robust (b : OrthonormalBasis (
Fin n) Real E) (hb : b.toBasis.orientation = o) : o.volumeForm = b.toBasis.det
· 使用定理 `Module.Basis.det_map`：det_map (b : Basis ι R M) (f : M ≃ₗ[R] M') (v : ι 
-> M') : (b.map f).det v = b.det (f.symm ∘ v)
-/
theorem volumeForm_map {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [Fact (finrank ℝ F = n)] (φ : E ≃ₗᵢ[ℝ] F) (x : Fin n → F) :
    (Orientation.map (Fin n) φ.toLinearEquiv o).volumeForm x = o.volumeForm (φ.symm ∘ x) := by
  rcases n with - | n
  · refine o.eq_or_eq_neg_of_isEmpty.elim ?_ ?_ <;> rintro rfl <;> simp
  let e : OrthonormalBasis (Fin n.succ) ℝ E := o.finOrthonormalBasis n.succ_pos Fact.out
  have he : e.toBasis.orientation = o :=
    o.finOrthonormalBasis_orientation n.succ_pos Fact.out
  have heφ : (e.map φ).toBasis.orientation = Orientation.map (Fin n.succ) φ.toLinearEquiv o := by
    rw [← he]
    exact e.toBasis.orientation_map φ.toLinearEquiv
  rw [(Orientation.map (Fin n.succ) φ.toLinearEquiv o).volumeForm_robust (e.map φ) heφ]
  rw [o.volumeForm_robust e he]
  simp

/-- The volume form is invariant under pullback by a positively-oriented isometric automorphism. -/
/-
**Orientation.volumeForm_comp_linearIsometryEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Ori
entation`。
形式化陈述：volumeForm_comp_linearIsometryEquiv (φ : E ≃ₗᵢ[Real] E) (hφ : 0 < LinearMa
p.det (φ.toLinearEquiv : E ->ₗ[Real] E)) (x : Fin n -> E) : o.volumeForm (φ ∘ x)
 = o.volumeForm x
参数：φ : E ≃ₗᵢ[Real] E；hφ : 0 < LinearMap.det (φ.toLinearEquiv : E ->ₗ[Real] E)；x 
: Fin n -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Orientation.eq_or_eq_neg_of_isEmpty`：eq_or_eq_neg_of_isEmpty [IsEmpty ι]
 (o : Orientation R M ι) : o = positiveOrientation ∨ o = -positiveOrientation
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Orientation.volumeForm_zero_pos`：volumeForm_zero_pos [_i : Fact (finrank
 Real E = 0)] : Orientation.volumeForm (positiveOrientation : Orientation Real E
 (Fin 0)) = Alternati…
· 使用定理 `AlternatingMap.constLinearEquivOfIsEmpty_apply`：∀ {ι : Type u_7} {R' : T
ype u_10} {M'' : Type u_11} {N'' : Type u_13} [inst : CommSemiring R']   [inst_1
 : AddCommMonoid M''] [inst_2 : AddC…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `AlternatingMap.constOfIsEmpty_apply`：∀ (R : Type u_1) [inst : Semiring R
] (M : Type u_2) [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {N : 
Type u_3} [inst_3 : AddCo…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Orientation.volumeForm_neg_orientation`：volumeForm_neg_orientation : (-o
).volumeForm = -o.volumeForm
· 使用定理 `FiniteDimensional.of_fact_finrank_eq_succ`：of_fact_finrank_eq_succ (n : 
Nat) [hn : Fact (finrank K V = n + 1)] : FiniteDimensional K V
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Orientation.map_eq_iff_det_pos`：map_eq_iff_det_pos [FiniteDimensional R 
M] (x : Orientation R M ι) (f : M ≃ₗ[R] M) (h : Fintype.card ι = finrank R M) : 
Orientation.map ι f …
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LinearIsometryEquiv.symm_apply_apply`：symm_apply_apply (x : E) : e.symm 
(e x) = x
· 使用定理 `Orientation.volumeForm_map`：volumeForm_map {F : Type*} [NormedAddCommGro
up F] [InnerProductSpace Real F] [Fact (finrank Real F = n)] (φ : E ≃ₗᵢ[Real] F)
 (x : Fin n -> F…

--- 原说明 ---
The volume form is invariant under pullback by a positively-oriented isometric a
utomorphism.
-/
theorem volumeForm_comp_linearIsometryEquiv (φ : E ≃ₗᵢ[ℝ] E)
    (hφ : 0 < LinearMap.det (φ.toLinearEquiv : E →ₗ[ℝ] E)) (x : Fin n → E) :
    o.volumeForm (φ ∘ x) = o.volumeForm x := by
  rcases n with - | n
  · refine o.eq_or_eq_neg_of_isEmpty.elim ?_ ?_ <;> rintro rfl <;> simp
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  convert! o.volumeForm_map φ (φ ∘ x)
  · symm
    rwa [← o.map_eq_iff_det_pos φ.toLinearEquiv] at hφ
    rw [_i.out, Fintype.card_fin]
  · ext
    simp

end VolumeForm

end Orientation

