/-
Copyright (c) 2026 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov, Edison Xie
-/
module

public import Mathlib.Data.Sign.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

/-!
# Projective general linear group

In this file we define `Matrix.ProjGenLinGroup n R` as the quotient of `GL n R` by its center.
We introduce notation `PGL(n, R)` for this group,
which works if `n` is either a finite type or a natural number.
If `n` is a number, then `PGL(n, R)` is interpreted as `PGL(Fin n, R)`.

## Main definitions

* `Matrix.SpecialLinearGroup.toPGL` is the natural map from `SL(n, R)` to `PGL(n, R)`.

* `Matrix.ProjectiveSpecialLinearGroup.toPGL` is the natural
  inclusion from `PSL(n, R)` to `PGL(n, R)`.

* `Matrix.ProjectiveSpecialLinearGroup.isoPSLOfAlgClosed` is an isomorphism between
  `PGL(n, F)` and `PSL(n, F)` in the case of an algebraically closed field.

-/

open scoped MatrixGroups

@[expose] public section

namespace Matrix

/--
Definition of `ProjGenLinGroup` / `ProjGenLinGroup` 的定义

English:
definition ProjGenLinGroup
  signature: (n : Type*) [Fintype n] [DecidableEq n] (R : Type*) [CommRing R]
  body: GL n R ⧸ Subgroup.center (GL n R)
  deriving Group

@[inherit_doc]
scoped[MatrixGroups] notation "PGL(" n ", " R ")" => Matrix.ProjGenLinGroup n R

@[inherit_doc]
scoped[MatrixGroups] notation "PGL(" n ", " R ")" => Matrix.ProjGenLinGroup (Fin n) R

中文:
定义 ProjGenLinGroup
  签名: (n : 类型) [有限类型 n] [DecidableEq n] (R : 类型) [交换环 R]
  定义体: GL n R ⧸ Subgroup.center (GL n R)
  deriving Group

@[inherit_doc]
scoped[MatrixGroups] notation "PGL(" n ", " R ")" => Matrix.ProjGenLinGroup n R

@[inherit_doc]
scoped[MatrixGroups] notation "PGL(" n ", " R ")" => Matrix.ProjGenLinGroup (Fin n) R

Depends on / 依赖: Subgroup, Subgroup.center, center
-/
def ProjGenLinGroup (n : Type*) [Fintype n] [DecidableEq n] (R : Type*) [CommRing R] : Type _ :=
  GL n R ⧸ Subgroup.center (GL n R)
  deriving Group

@[inherit_doc]
scoped[MatrixGroups] notation "PGL(" n ", " R ")" => Matrix.ProjGenLinGroup n R

@[inherit_doc]
scoped[MatrixGroups] notation "PGL(" n ", " R ")" => Matrix.ProjGenLinGroup (Fin n) R

namespace ProjGenLinGroup
variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: : GL n R ->* PGL(n, R)
  body: QuotientGroup.mk' (Subgroup.center (GL n R))

中文:
定义 mk
  签名: : GL n R ->* PGL(n, R)
  定义体: QuotientGroup.mk' (Subgroup.center (GL n R))

Depends on / 依赖: QuotientGroup, QuotientGroup.mk, Subgroup, Subgroup.center, center
-/
def mk : GL n R ->* PGL(n, R) := QuotientGroup.mk' (Subgroup.center (GL n R))

/--
theorem `mk_surjective` / 定理 `mk_surjective`

English:
theorem mk_surjective
  statement: Function.Surjective (mk : GL n R -> PGL(n, R))
  proof: Quotient.mk_surjective

中文:
定理 mk_surjective
  结论: 函数.满射 (mk : GL n R -> PGL(n, R))
  证明: Quotient.mk_surjective

Depends on / 依赖: Quotient, Quotient.mk_surjective, mk_surjective
-/
theorem mk_surjective : Function.Surjective (mk : GL n R -> PGL(n, R)) :=
  Quotient.mk_surjective

/--
lemma `mk_eq_mk_iff'` / 引理 `mk_eq_mk_iff'`

English:
lemma mk_eq_mk_iff'
  given: {g₁ g₂ : GL n R}
  proof: QuotientGroup.mk'_eq_mk' (Subgroup.center (GL n R))

中文:
引理 mk_eq_mk_iff'
  条件: {g₁ g₂ : GL n R}
  证明: QuotientGroup.mk'_eq_mk' (Subgroup.center (GL n R))

Depends on / 依赖: QuotientGroup, QuotientGroup.mk, Subgroup, Subgroup.center, _eq_mk, center
-/
lemma mk_eq_mk_iff' {g₁ g₂ : GL n R} :
    mk g₁ = mk g₂ ↔ exists z in Subgroup.center (GL n R), g₁ * z = g₂ :=
  QuotientGroup.mk'_eq_mk' (Subgroup.center (GL n R))

/--
lemma `mk_eq_mk_iff` / 引理 `mk_eq_mk_iff`

English:
lemma mk_eq_mk_iff
  given: {g₁ g₂ : GL n R}
  proof: by
  simp [mk_eq_mk_iff', Matrix.GeneralLinearGroup.center_eq_range_scalar]

@[simp]

中文:
引理 mk_eq_mk_iff
  条件: {g₁ g₂ : GL n R}
  证明: by
  simp [mk_eq_mk_iff', Matrix.GeneralLinearGroup.center_eq_range_scalar]

@[simp]

Depends on / 依赖: GeneralLinearGroup, Matrix, Matrix.GeneralLinearGroup.center_eq_range_scalar, center_eq_range_scalar, mk_eq_mk_iff
-/
lemma mk_eq_mk_iff {g₁ g₂ : GL n R} :
    mk g₁ = mk g₂ ↔ exists u : Rˣ, g₁ * .scalar n u = g₂ := by
  simp [mk_eq_mk_iff', Matrix.GeneralLinearGroup.center_eq_range_scalar]

@[simp]
/--
theorem `ker_mk` / 定理 `ker_mk`

English:
theorem ker_mk
  statement: mk.ker = Subgroup.center (GL n R)
  proof: QuotientGroup.ker_mk' _

@[simp]

中文:
定理 ker_mk
  结论: mk.ker = 子群.center (GL n R)
  证明: QuotientGroup.ker_mk' _

@[simp]

Depends on / 依赖: QuotientGroup, QuotientGroup.ker_mk, ker_mk
-/
theorem ker_mk : mk.ker = Subgroup.center (GL n R) := QuotientGroup.ker_mk' _

@[simp]
/--
theorem `mk_eq_one` / 定理 `mk_eq_one`

English:
theorem mk_eq_one
  given: {g : GL n R}
  statement: mk g = 1 ↔ g in Subgroup.center (GL n R)
  proof: by
  rw [← MonoidHom.mem_ker]; rw [ker_mk]

@[simp]

中文:
定理 mk_eq_one
  条件: {g : GL n R}
  结论: mk g = 1 ↔ g in 子群.center (GL n R)
  证明: by
  rw [← MonoidHom.mem_ker]; rw [ker_mk]

@[simp]

Depends on / 依赖: MonoidHom, MonoidHom.mem_ker, ker_mk, mem_ker
-/
theorem mk_eq_one {g : GL n R} : mk g = 1 ↔ g in Subgroup.center (GL n R) := by
  rw [← MonoidHom.mem_ker]; rw [ker_mk]

@[simp]
/--
lemma `mk_one` / 引理 `mk_one`

English:
lemma mk_one
  statement: mk (1 : GL n R) = 1
  proof: rfl

@[simp]

中文:
引理 mk_one
  结论: mk (1 : GL n R) = 1
  证明: rfl

@[simp]
-/
lemma mk_one : mk (1 : GL n R) = 1 := rfl

@[simp]
/--
theorem `mk_scalar` / 定理 `mk_scalar`

English:
theorem mk_scalar
  given: (u : Rˣ)
  statement: mk (.scalar n u) = 1
  proof: by
  rw [← MonoidHom.mem_ker]; rw [ker_mk]; rw [GeneralLinearGroup.center_eq_range_scalar]
  simp

@[elab_as_elim, cases_eliminator]

中文:
定理 mk_scalar
  条件: (u : Rˣ)
  结论: mk (.scalar n u) = 1
  证明: by
  rw [← MonoidHom.mem_ker]; rw [ker_mk]; rw [GeneralLinearGroup.center_eq_range_scalar]
  simp

@[elab_as_elim, cases_eliminator]

Depends on / 依赖: GeneralLinearGroup, GeneralLinearGroup.center_eq_range_scalar, MonoidHom, MonoidHom.mem_ker, center_eq_range_scalar, ker_mk, mem_ker
-/
theorem mk_scalar (u : Rˣ) : mk (.scalar n u) = 1 := by
  rw [← MonoidHom.mem_ker]; rw [ker_mk]; rw [GeneralLinearGroup.center_eq_range_scalar]
  simp

@[elab_as_elim, cases_eliminator]
/--
theorem `induction_on` / 定理 `induction_on`

English:
theorem induction_on
  statement: {motive : PGL(n, R) -> Prop} (g : PGL(n, R))
  proof: Quotient.inductionOn g mk

中文:
定理 induction_on
  结论: {motive : PGL(n, R) -> 命题} (g : PGL(n, R))
  证明: Quotient.inductionOn g mk

Depends on / 依赖: Quotient, Quotient.inductionOn, inductionOn
-/
theorem induction_on {motive : PGL(n, R) -> Prop} (g : PGL(n, R))
    (mk : forall g : GL n R, motive (ProjGenLinGroup.mk g)) : motive g :=
  Quotient.inductionOn g mk

end ProjGenLinGroup

section isoPSL

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

open Matrix.ProjGenLinGroup

namespace SpecialLinearGroup

/--
Definition of `toPGL` / `toPGL` 的定义

English:
abbreviation toPGL
  signature: : SpecialLinearGroup n R ->* PGL(n, R)
  body: mk.comp toGL

中文:
缩写 toPGL
  签名: : SpecialLinearGroup n R ->* PGL(n, R)
  定义体: mk.comp toGL

Depends on / 依赖: mk.comp
-/
abbrev toPGL : SpecialLinearGroup n R ->* PGL(n, R) := mk.comp toGL

/--
lemma `toPGL_ker` / 引理 `toPGL_ker`

English:
lemma toPGL_ker
  statement: toPGL.ker = Subgroup.center (SpecialLinearGroup n R)
  proof: by
  ext; simp [toGL_mem_center_iff]

中文:
引理 toPGL_ker
  结论: toPGL.ker = 子群.center (SpecialLinearGroup n R)
  证明: by
  ext; simp [toGL_mem_center_iff]

Depends on / 依赖: toGL_mem_center_iff
-/
lemma toPGL_ker : toPGL.ker = Subgroup.center (SpecialLinearGroup n R) := by
  ext; simp [toGL_mem_center_iff]

end SpecialLinearGroup

namespace ProjectiveSpecialLinearGroup

open Matrix.SpecialLinearGroup

/--
Definition of `toPGL` / `toPGL` 的定义

English:
definition toPGL
  signature: : ProjectiveSpecialLinearGroup n R ->* PGL(n, R)
  body: QuotientGroup.lift _ SpecialLinearGroup.toPGL le_of_eq toPGL_ker.symm

@[simp]

中文:
定义 toPGL
  签名: : ProjectiveSpecialLinearGroup n R ->* PGL(n, R)
  定义体: QuotientGroup.lift _ SpecialLinearGroup.toPGL le_of_eq toPGL_ker.symm

@[simp]

Depends on / 依赖: QuotientGroup, QuotientGroup.lift, SpecialLinearGroup, SpecialLinearGroup.toPGL, le_of_eq, toPGL_ker, toPGL_ker.symm
-/
def toPGL : ProjectiveSpecialLinearGroup n R ->* PGL(n, R) :=
QuotientGroup.lift _ SpecialLinearGroup.toPGL le_of_eq toPGL_ker.symm

@[simp]
/--
lemma `toPGL_mk` / 引理 `toPGL_mk`

English:
lemma toPGL_mk
  given: (g : SpecialLinearGroup n R)
  proof: rfl

中文:
引理 toPGL_mk
  条件: (g : SpecialLinearGroup n R)
  证明: rfl
-/
lemma toPGL_mk (g : SpecialLinearGroup n R) :
    ProjectiveSpecialLinearGroup.toPGL g = mk (toGL g) := rfl

/--
lemma `toPGL_injective` / 引理 `toPGL_injective`

English:
lemma toPGL_injective
  proof: .2 toPGL_ker.symm QuotientGroup.injective_lift_iff _ _ _

中文:
引理 toPGL_injective
  证明: .2 toPGL_ker.symm QuotientGroup.injective_lift_iff _ _ _
-/
lemma toPGL_injective :
    Function.Injective (ProjectiveSpecialLinearGroup.toPGL (n := n) (R := R)) :=
.2 toPGL_ker.symm QuotientGroup.injective_lift_iff _ _ _

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `toPGL_surj_of_roots` / 引理 `toPGL_surj_of_roots`

English:
lemma toPGL_surj_of_roots
  proof: fun g => by
  induction g using Matrix.ProjGenLinGroup.induction_on with | mk g =>
  obtain ⟨r, hr⟩ : exists r : Rˣ, r ^ Fintype.card n * g.det = 1 := by
    obtain ⟨r, hr⟩ := hR g.det⁻¹
    exact ⟨r, by simpa [mul_eq_one_iff_eq_inv] using hr⟩
  simp only [Units.ext_iff, Units.val_mul, Units.val_pow

中文:
引理 toPGL_surj_of_roots
  证明: fun g => by
  induction g using Matrix.ProjGenLinGroup.induction_on with | mk g =>
  obtain ⟨r, hr⟩ : exists r : Rˣ, r ^ Fintype.card n * g.det = 1 := by
    obtain ⟨r, hr⟩ := hR g.det⁻¹
    exact ⟨r, by simpa [mul_eq_one_iff_eq_inv] using hr⟩
  simp only [Units.ext_iff, Units.val_mul, Units.val_pow

Depends on / 依赖: Fintype, Fintype.card, GeneralLinearGroup, GeneralLinearGroup.val_det_apply, Matrix, Matrix.ProjGenLinGroup.induction_on, Matrix.det_smul, ProjGenLinGroup, ProjectiveSpecialLinearGroup, ProjectiveSpecialLinearGroup.toPGL_mk, QuotientGroup, QuotientGroup.mk, Units.ext_iff, Units.val_mul, Units.val_one, Units.val_pow_eq_pow_val, det_smul, ext_iff, g.det, induction_on
-/
lemma toPGL_surj_of_roots
    (hR : forall r : Rˣ, exists k : Rˣ, k ^ Fintype.card n = r) :
    Function.Surjective (ProjectiveSpecialLinearGroup.toPGL (n := n) (R := R)) := fun g => by
  induction g using Matrix.ProjGenLinGroup.induction_on with | mk g =>
  obtain ⟨r, hr⟩ : exists r : Rˣ, r ^ Fintype.card n * g.det = 1 := by
    obtain ⟨r, hr⟩ := hR g.det⁻¹
    exact ⟨r, by simpa [mul_eq_one_iff_eq_inv] using hr⟩
  simp only [Units.ext_iff, Units.val_mul, Units.val_pow_eq_pow_val,
    GeneralLinearGroup.val_det_apply, ← Matrix.det_smul g.1 r.1, Units.val_one] at hr
  use QuotientGroup.mk ⟨r.1 • g.1, hr⟩
  simp only [ProjectiveSpecialLinearGroup.toPGL_mk, mk_eq_mk_iff]
  refine ⟨r⁻¹, Units.ext ?_⟩
  simp only [Units.val_mul, coe_GL_coe_matrix, GeneralLinearGroup.coe_scalar]
  simp [← Matrix.mul_smul, ← Matrix.diagonal_smul, Pi.smul_def, smul_eq_mul]

/--
lemma `toPGL_surj_iff` / 引理 `toPGL_surj_iff`

English:
lemma toPGL_surj_iff
  given: [Nonempty n]
  proof: by
  refine ⟨fun h r => ?_, ProjectiveSpecialLinearGroup.toPGL_surj_of_roots⟩
  obtain ⟨A, hA⟩ := GeneralLinearGroup.det_surjective (n := n) r
  obtain ⟨X, hX⟩ := h (.mk A)
  induction X using QuotientGroup.induction_on with | H X =>
  obtain ⟨u, hu⟩ : exists u, toGL X * (GeneralLinearGroup.scalar n

中文:
引理 toPGL_surj_iff
  条件: [非空 n]
  证明: by
  refine ⟨fun h r => ?_, ProjectiveSpecialLinearGroup.toPGL_surj_of_roots⟩
  obtain ⟨A, hA⟩ := GeneralLinearGroup.det_surjective (n := n) r
  obtain ⟨X, hX⟩ := h (.mk A)
  induction X using QuotientGroup.induction_on with | H X =>
  obtain ⟨u, hu⟩ : exists u, toGL X * (GeneralLinearGroup.scalar n
-/
lemma toPGL_surj_iff [Nonempty n] :
    Function.Surjective (ProjectiveSpecialLinearGroup.toPGL (n := n) (R := R)) ↔
      forall r : Rˣ, exists k : Rˣ, k ^ Fintype.card n = r := by
  refine ⟨fun h r => ?_, ProjectiveSpecialLinearGroup.toPGL_surj_of_roots⟩
  obtain ⟨A, hA⟩ := GeneralLinearGroup.det_surjective (n := n) r
  obtain ⟨X, hX⟩ := h (.mk A)
  induction X using QuotientGroup.induction_on with | H X =>
  obtain ⟨u, hu⟩ : exists u, toGL X * (GeneralLinearGroup.scalar n) u = A := by
    simpa [mk_eq_mk_iff] using hX
  exact ⟨u, by simpa [hA] using congr(Matrix.GeneralLinearGroup.det $hu)⟩

open Polynomial in
/--
Definition of `isoPSLOfAlgClosedOfNonempty` / `isoPSLOfAlgClosedOfNonempty` 的定义

English:
definition isoPSLOfAlgClosedOfNonempty
  signature: [Nonempty n] {F : Type*} [Field F] [IsAlgClosed F]
  body: MulEquiv.symm (MulEquiv.ofBijective Matrix.ProjectiveSpecialLinearGroup.toPGL
    ⟨Matrix.ProjectiveSpecialLinearGroup.toPGL_injective,
    Matrix.ProjectiveSpecialLinearGroup.toPGL_surj_of_roots fun r => by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (X ^ Fintype.card n - C r.1 : F[X]) (by
    simp

中文:
定义 isoPSLOfAlgClosedOfNonempty
  签名: [非空 n] {F : 类型} [域 F] [是代数闭 F]
  定义体: MulEquiv.symm (MulEquiv.ofBijective Matrix.ProjectiveSpecialLinearGroup.toPGL
    ⟨Matrix.ProjectiveSpecialLinearGroup.toPGL_injective,
    Matrix.ProjectiveSpecialLinearGroup.toPGL_surj_of_roots fun r => by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (X ^ Fintype.card n - C r.1 : F[X]) (by
    simp

Depends on / 依赖: Fintype, Fintype.card, Fintype.card_pos, IsAlgClosed, IsAlgClosed.exists_root, Matrix, Matrix.ProjectiveSpecialLinearGroup.toPGL, Matrix.ProjectiveSpecialLinearGroup.toPGL_injective, Matrix.ProjectiveSpecialLinearGroup.toPGL_surj_of_roots, MulEquiv, MulEquiv.ofBijective, MulEquiv.symm, Polynomial, Polynomial.degree_X_pow_sub_C, ProjectiveSpecialLinearGroup, Units.ext_iff, card_pos, degree_X_pow_sub_C, exists_root, ext_iff
-/
noncomputable def isoPSLOfAlgClosedOfNonempty [Nonempty n] {F : Type*} [Field F] [IsAlgClosed F] :
    PGL(n, F) ≃* ProjectiveSpecialLinearGroup n F :=
  MulEquiv.symm (MulEquiv.ofBijective Matrix.ProjectiveSpecialLinearGroup.toPGL
    ⟨Matrix.ProjectiveSpecialLinearGroup.toPGL_injective,
    Matrix.ProjectiveSpecialLinearGroup.toPGL_surj_of_roots fun r => by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (X ^ Fintype.card n - C r.1 : F[X]) (by
    simp [Polynomial.degree_X_pow_sub_C Fintype.card_pos])
  have hx' : x != 0 := by aesop
  exact ⟨⟨x, x⁻¹, mul_inv_cancel₀ hx', inv_mul_cancel₀ hx'⟩, by
    simpa [Units.ext_iff, sub_eq_zero] using hx⟩⟩)

/--
Definition of `isoPSLOfAlgClosed` / `isoPSLOfAlgClosed` 的定义

English:
definition isoPSLOfAlgClosed
  signature: {F : Type*} [Field F] [IsAlgClosed F]
  body: open scoped Classical in
  if h : Nonempty n then isoPSLOfAlgClosedOfNonempty else
  have : IsEmpty n := by simpa using h
  have : Subsingleton (PGL(n, F)) := mk_surjective.subsingleton
  MulEquiv.symm (MulEquiv.ofBijective Matrix.ProjectiveSpecialLinearGroup.toPGL
    ⟨Matrix.ProjectiveSpecialLinea

中文:
定义 isoPSLOfAlgClosed
  签名: {F : 类型} [域 F] [是代数闭 F]
  定义体: open scoped Classical in
  if h : Nonempty n then isoPSLOfAlgClosedOfNonempty else
  have : IsEmpty n := by simpa using h
  have : Subsingleton (PGL(n, F)) := mk_surjective.subsingleton
  MulEquiv.symm (MulEquiv.ofBijective Matrix.ProjectiveSpecialLinearGroup.toPGL
    ⟨Matrix.ProjectiveSpecialLinea

Depends on / 依赖: Classical, Function, Function.surjective_to_subsingleton, IsEmpty, Matrix, Matrix.ProjectiveSpecialLinearGroup.toPGL, Matrix.ProjectiveSpecialLinearGroup.toPGL_injective, MulEquiv, MulEquiv.ofBijective, MulEquiv.symm, Nonempty, ProjectiveSpecialLinearGroup, Subsingleton, isoPSLOfAlgClosedOfNonempty, mk_surjective, mk_surjective.subsingleton, ofBijective, scoped, subsingleton, surjective_to_subsingleton
-/
noncomputable def isoPSLOfAlgClosed {F : Type*} [Field F] [IsAlgClosed F] :
    PGL(n, F) ≃* ProjectiveSpecialLinearGroup n F :=
  open scoped Classical in
  if h : Nonempty n then isoPSLOfAlgClosedOfNonempty else
  have : IsEmpty n := by simpa using h
  have : Subsingleton (PGL(n, F)) := mk_surjective.subsingleton
  MulEquiv.symm (MulEquiv.ofBijective Matrix.ProjectiveSpecialLinearGroup.toPGL
    ⟨Matrix.ProjectiveSpecialLinearGroup.toPGL_injective, Function.surjective_to_subsingleton _⟩)

end ProjectiveSpecialLinearGroup

end isoPSL

namespace ProjGenLinGroup

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R] {M : Type*} [Monoid M]

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: (f : GL n R ->* M) (hf : f.comp (GeneralLinearGroup.scalar n) = 1)
  body: QuotientGroup.lift _ f by
    rwa [GeneralLinearGroup.center_eq_range_scalar, MonoidHom.range_le_ker_iff]

@[simp]

中文:
定义 lift
  签名: (f : GL n R ->* M) (hf : f.comp (GeneralLinearGroup.scalar n) = 1)
  定义体: QuotientGroup.lift _ f by
    rwa [GeneralLinearGroup.center_eq_range_scalar, MonoidHom.range_le_ker_iff]

@[simp]

Depends on / 依赖: GeneralLinearGroup, GeneralLinearGroup.center_eq_range_scalar, MonoidHom, MonoidHom.range_le_ker_iff, QuotientGroup, QuotientGroup.lift, center_eq_range_scalar, range_le_ker_iff
-/
def lift (f : GL n R ->* M) (hf : f.comp (GeneralLinearGroup.scalar n) = 1) :
    PGL(n, R) ->* M :=
QuotientGroup.lift _ f by
    rwa [GeneralLinearGroup.center_eq_range_scalar, MonoidHom.range_le_ker_iff]

@[simp]
/--
theorem `lift_mk` / 定理 `lift_mk`

English:
theorem lift_mk
  given: {f : GL n R ->* M} (hf) (g : GL n R)
  statement: lift f hf (mk g) = f g
  proof: by
  rfl

@[simp]

中文:
定理 lift_mk
  条件: {f : GL n R ->* M} (hf) (g : GL n R)
  结论: lift f hf (mk g) = f g
  证明: by
  rfl

@[simp]
-/
theorem lift_mk {f : GL n R ->* M} (hf) (g : GL n R) : lift f hf (mk g) = f g := by
  rfl

@[simp]
/--
theorem `lift_comp_mk` / 定理 `lift_comp_mk`

English:
theorem lift_comp_mk
  given: {f : GL n R ->* M} (hf)
  statement: (lift f hf).comp mk = f
  proof: by
  rfl

中文:
定理 lift_comp_mk
  条件: {f : GL n R ->* M} (hf)
  结论: (lift f hf).comp mk = f
  证明: by
  rfl
-/
theorem lift_comp_mk {f : GL n R ->* M} (hf) : (lift f hf).comp mk = f := by
  rfl

/-- Given an action of `GL n R` such that the scalar matrices act trivially,
define an action of `PGL n R`. -/
@[instance_reducible]
/--
Definition of `mulActionOfGL` / `mulActionOfGL` 的定义

English:
definition mulActionOfGL
  signature: {α : Type*} [MulAction (GL n R) α]
  body: .ofEndHom lift MulAction.toEndHom by
    ext u
    funext a -- TODO: should we add an `ext` lemma for `Function.End`?
    exact h u a

中文:
定义 mulActionOfGL
  签名: {α : 类型} [乘法作用 (GL n R) α]
  定义体: .ofEndHom lift MulAction.toEndHom by
    ext u
    funext a -- TODO: should we add an `ext` lemma for `Function.End`?
    exact h u a

Depends on / 依赖: Function, Function.End, MulAction, MulAction.toEndHom, ofEndHom, should, toEndHom
-/
def mulActionOfGL {α : Type*} [MulAction (GL n R) α]
    (h : forall (u : Rˣ) (a : α), GeneralLinearGroup.scalar n u • a = a) :
    MulAction (PGL(n, R)) α :=
.ofEndHom lift MulAction.toEndHom by
    ext u
    funext a -- TODO: should we add an `ext` lemma for `Function.End`?
    exact h u a

/--
theorem `mk_smul` / 定理 `mk_smul`

English:
theorem mk_smul
  given: {α : Type*} [MulAction (GL n R) α] (h) (g : GL n R) (a : α)
  proof: mulActionOfGL h
    mk g • a = g • a := by
  rfl

中文:
定理 mk_smul
  条件: {α : 类型} [乘法作用 (GL n R) α] (h) (g : GL n R) (a : α)
  证明: mulActionOfGL h
    mk g • a = g • a := by
  rfl

Depends on / 依赖: mulActionOfGL
-/
theorem mk_smul {α : Type*} [MulAction (GL n R) α] (h) (g : GL n R) (a : α) :
    letI : MulAction (PGL(n, R)) α := mulActionOfGL h
    mk g • a = g • a := by
  rfl

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: {S : Type*} [CommRing S] (f : R ->+* S)
  body: QuotientGroup.map _ _ (GeneralLinearGroup.map (n := n) f) GeneralLinearGroup.map_center_le f

@[simp]

中文:
定义 map
  签名: {S : 类型} [交换环 S] (f : R ->+* S)
  定义体: QuotientGroup.map _ _ (GeneralLinearGroup.map (n := n) f) GeneralLinearGroup.map_center_le f

@[simp]

Depends on / 依赖: GeneralLinearGroup, GeneralLinearGroup.map, GeneralLinearGroup.map_center_le, QuotientGroup, QuotientGroup.map, map_center_le
-/
def map {S : Type*} [CommRing S] (f : R ->+* S) : PGL(n, R) ->* PGL(n, S) :=
QuotientGroup.map _ _ (GeneralLinearGroup.map (n := n) f) GeneralLinearGroup.map_center_le f

@[simp]
/--
lemma `map_id` / 引理 `map_id`

English:
lemma map_id
  statement: map (RingHom.id R) = MonoidHom.id (PGL(n, R))
  proof: QuotientGroup.map_id _

@[simp]

中文:
引理 map_id
  结论: map (环态射.id R) = 幺半群态射.id (PGL(n, R))
  证明: QuotientGroup.map_id _

@[simp]

Depends on / 依赖: QuotientGroup, QuotientGroup.map_id, map_id
-/
lemma map_id : map (RingHom.id R) = MonoidHom.id (PGL(n, R)) := QuotientGroup.map_id _

@[simp]
/--
lemma `map_mk` / 引理 `map_mk`

English:
lemma map_mk
  given: {S : Type*} [CommRing S] (f : R ->+* S) (g : GL n R)
  proof: rfl

中文:
引理 map_mk
  条件: {S : 类型} [交换环 S] (f : R ->+* S) (g : GL n R)
  证明: rfl
-/
lemma map_mk {S : Type*} [CommRing S] (f : R ->+* S) (g : GL n R) :
    map f (mk g) = mk (GeneralLinearGroup.map f g) := rfl

/--
lemma `map_comp` / 引理 `map_comp`

English:
lemma map_comp
  given: {S T : Type*} [CommRing S] [CommRing T] (f : R ->+* S) (g : S ->+* T)
  proof: by
  ext g
  induction g using Matrix.ProjGenLinGroup.induction_on with | mk g => simp

中文:
引理 map_comp
  条件: {S T : 类型} [交换环 S] [交换环 T] (f : R ->+* S) (g : S ->+* T)
  证明: by
  ext g
  induction g using Matrix.ProjGenLinGroup.induction_on with | mk g => simp

Depends on / 依赖: Matrix, Matrix.ProjGenLinGroup.induction_on, ProjGenLinGroup, g.comp, induction_on
-/
lemma map_comp {S T : Type*} [CommRing S] [CommRing T] (f : R ->+* S) (g : S ->+* T) :
    map (n := n) (g.comp f) = (map g).comp (map f) := by
  ext g
  induction g using Matrix.ProjGenLinGroup.induction_on with | mk g => simp

variable [Fact (Even (Fintype.card n))] [LinearOrder R] [IsStrictOrderedRing R]

/--
Definition of `signDet` / `signDet` 的定义

English:
definition signDet
  signature: : PGL(n, R) ->* SignTypeˣ
  body: lift ((Units.map signHom.toMonoidHom).comp GeneralLinearGroup.det) by
    ext u
    simp [← sign_pow, Even.pow_pos Fact.out]

中文:
定义 signDet
  签名: : PGL(n, R) ->* SignTypeˣ
  定义体: lift ((Units.map signHom.toMonoidHom).comp GeneralLinearGroup.det) by
    ext u
    simp [← sign_pow, Even.pow_pos Fact.out]

Depends on / 依赖: Even.pow_pos, Fact.out, GeneralLinearGroup, GeneralLinearGroup.det, Units.map, pow_pos, signHom, signHom.toMonoidHom, sign_pow, toMonoidHom
-/
def signDet : PGL(n, R) ->* SignTypeˣ :=
lift ((Units.map signHom.toMonoidHom).comp GeneralLinearGroup.det) by
    ext u
    simp [← sign_pow, Even.pow_pos Fact.out]

/--
theorem `signDet_mk` / 定理 `signDet_mk`

English:
theorem signDet_mk
  given: (g : GL n R)
  statement: signDet (mk g) = Units.map signHom.toMonoidHom g.det
  proof: by
  rfl

@[simp]

中文:
定理 signDet_mk
  条件: (g : GL n R)
  结论: signDet (mk g) = 单位群.map signHom.toMonoidHom g.det
  证明: by
  rfl

@[simp]
-/
theorem signDet_mk (g : GL n R) : signDet (mk g) = Units.map signHom.toMonoidHom g.det := by
  rfl

@[simp]
/--
theorem `val_signDet_mk` / 定理 `val_signDet_mk`

English:
theorem val_signDet_mk
  given: (g : GL n R)
  statement: (signDet (mk g) : SignType) = .sign g.det.val
  proof: by
  rfl

中文:
定理 val_signDet_mk
  条件: (g : GL n R)
  结论: (signDet (mk g) : SignType) = .sign g.det.val
  证明: by
  rfl
-/
theorem val_signDet_mk (g : GL n R) : (signDet (mk g) : SignType) = .sign g.det.val := by
  rfl

end ProjGenLinGroup

end Matrix
