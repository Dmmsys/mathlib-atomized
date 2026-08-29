/-
Copyright (c) 2026 Yoh Tanimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoh Tanimoto
-/
module

public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# Standard subspaces of a Hilbert space

This files defines standard subspaces of a complex Hilbert space: a standard subspace `S` of `H` is
a closed real subspace `S` such that `S ⊓ i S = ⊥` and `S ⊔ i S = ⊤`. For a standard subspace, one
can define a closable operator `x + i y ↦ x - i y` and develop an analogue of the Tomita-Takesaki
modular theory for von Neumann algebras. By considering inclusions of standard subspaces, one can
obtain unitary representations of various Lie groups.

## Main definitions and results

* `instance : InnerProductSpace ℝ H` for `InnerProductSpace ℂ H`, by restricting the scalar product
  to its real part

* `StandardSubspace` as a structure with a `ClosedSubmodule` for `InnerProductSpace ℝ H` satisfying
  `IsCyclic` and `IsSeparating`. Actually the interesting cases need `CompleteSpace H`, but the
  definition is given for a general case.

* `symplComp` as a `StandardSubspace` of the symplectic complement of a standard subspace with
  respect to `⟪⬝, ⬝⟫.im`

* `symplComp_symplComp_eq` the double symplectic complement is equal to itself

## References

* [Chap. 2 of Lecture notes by R. Longo](https://www.mat.uniroma2.it/longo/Lecture-Notes_files/LN-Part1.pdf)

* [Oberwolfach report](https://ems.press/content/serial-article-files/48171)

## TODO

Define the Tomita conjugation, prove Tomita's theorem, prove the KMS condition.
-/

@[expose] public section

open Complex ContinuousLinearMap
open scoped ComplexInnerProductSpace

section ScalarSMulCLE

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace Complex H]

/--
Definition of `scalarSMulCLE` / `scalarSMulCLE` 的定义

English:
definition scalarSMulCLE
  signature: (c : Complexˣ)
  body: ContinuousLinearEquiv.smulLeft c

@[simp]

中文:
定义 scalarSMulCLE
  签名: (c : Complexˣ)
  定义体: ContinuousLinearEquiv.smulLeft c

@[simp]

Depends on / 依赖: ContinuousLinearEquiv, ContinuousLinearEquiv.smulLeft, smulLeft
-/
noncomputable def scalarSMulCLE (c : Complexˣ) : H ≃L[Real] H := ContinuousLinearEquiv.smulLeft c

@[simp]
/--
lemma `scalarSMulCLE_apply` / 引理 `scalarSMulCLE_apply`

English:
lemma scalarSMulCLE_apply
  given: (c : Complexˣ) (x : H)
  statement: scalarSMulCLE H c x = c • x
  proof: rfl

@[simp]

中文:
引理 scalarSMulCLE_apply
  条件: (c : Complexˣ) (x : H)
  结论: scalarSMulCLE H c x = c • x
  证明: rfl

@[simp]
-/
lemma scalarSMulCLE_apply (c : Complexˣ) (x : H) : scalarSMulCLE H c x = c • x := rfl

@[simp]
/--
lemma `scalarSMulCLE_symm_apply` / 引理 `scalarSMulCLE_symm_apply`

English:
lemma scalarSMulCLE_symm_apply
  given: (c : Complexˣ) (x : H)
  statement: (scalarSMulCLE H c).symm x = c⁻¹ • x
  proof: rfl

中文:
引理 scalarSMulCLE_symm_apply
  条件: (c : Complexˣ) (x : H)
  结论: (scalarSMulCLE H c).symm x = c⁻¹ • x
  证明: rfl
-/
lemma scalarSMulCLE_symm_apply (c : Complexˣ) (x : H) : (scalarSMulCLE H c).symm x = c⁻¹ • x := rfl

end ScalarSMulCLE

namespace ClosedSubmodule

variable {H : Type*} [NormedAddCommGroup H] [ipc : InnerProductSpace Complex H]

/-- `H` as a real Hilbert space. This instance is declared inside `ClosedSubmodule` namespace. If
one needs this structure (for example when considering standard subspaces), one should just `open
ClosedSubmodule` and not declare another instance. -/
noncomputable scoped instance : InnerProductSpace Real H where
  inner x y := ⟪x, y⟫.re
  norm_sq_eq_re_inner := by simp [RCLike.re_to_real, ipc.norm_sq_eq_re_inner]
  conj_inner_symm x y := by
    simp only [← ipc.conj_inner_symm x y, conj_trivial]
    rfl
  add_left := by simp
  smul_left := by simp

/--
lemma `inner_real_eq_re_inner` / 引理 `inner_real_eq_re_inner`

English:
lemma inner_real_eq_re_inner
  given: (x y : H)
  statement: inner Real x y = ⟪x, y⟫.re
  proof: rfl

中文:
引理 inner_real_eq_re_inner
  条件: (x y : H)
  结论: inner 实数 x y = ⟪x, y⟫.re
  证明: rfl
-/
lemma inner_real_eq_re_inner (x y : H) : inner Real x y = ⟪x, y⟫.re := rfl

/-- The imaginary unit as an invertible element. -/
@[simps val]
/--
Definition of `_root_.Complex.UnitI` / `_root_.Complex.UnitI` 的定义

English:
definition _root_.Complex.UnitI
  signature: : Complexˣ where
  body: I
  inv := -I
  val_inv := by simp
  inv_val := by simp

中文:
定义 _root_.Complex.UnitI
  签名: : Complexˣ where
  定义体: I
  inv := -I
  val_inv := by simp
  inv_val := by simp
-/
def _root_.Complex.UnitI : Complexˣ where
  val := I
  inv := -I
  val_inv := by simp
  inv_val := by simp

/--
Definition of `mulI` / `mulI` 的定义

English:
abbreviation mulI
  signature: (S : ClosedSubmodule Real H)
  body: S.mapEquiv (scalarSMulCLE H UnitI)

中文:
缩写 mulI
  签名: (S : ClosedSubmodule 实数 H)
  定义体: S.mapEquiv (scalarSMulCLE H UnitI)

Depends on / 依赖: S.mapEquiv, mapEquiv, scalarSMulCLE
-/
noncomputable abbrev mulI (S : ClosedSubmodule Real H) := S.mapEquiv (scalarSMulCLE H UnitI)

/--
Definition of `symplComp` / `symplComp` 的定义

English:
abbreviation symplComp
  signature: (S : ClosedSubmodule Real H)
  body: (S.mulI)ᗮ

中文:
缩写 symplComp
  签名: (S : ClosedSubmodule 实数 H)
  定义体: (S.mulI)ᗮ

Depends on / 依赖: S.mulI
-/
noncomputable abbrev symplComp (S : ClosedSubmodule Real H) := (S.mulI)ᗮ

/--
lemma `mem_iff` / 引理 `mem_iff`

English:
lemma mem_iff
  given: (S : ClosedSubmodule Real H) {x : H}
  statement: x in S ↔ x in S.toSubmodule.carrier
  proof: by
  exact Eq.to_iff rfl

中文:
引理 mem_iff
  条件: (S : ClosedSubmodule 实数 H) {x : H}
  结论: x in S ↔ x in S.toSubmodule.carrier
  证明: by
  exact Eq.to_iff rfl

Depends on / 依赖: Eq.to_iff, to_iff
-/
lemma mem_iff (S : ClosedSubmodule Real H) {x : H} : x in S ↔ x in S.toSubmodule.carrier := by
  exact Eq.to_iff rfl

/--
lemma `mem_symplComp_iff` / 引理 `mem_symplComp_iff`

English:
lemma mem_symplComp_iff
  given: {x : H} {S : ClosedSubmodule Real H}
  proof: by
  simp only [mem_orthogonal, mem_mapEquiv_iff, scalarSMulCLE_symm_apply, Units.smul_def,
    Units.val_inv_eq_inv_val, val_UnitI, inv_I, neg_smul]
  constructor
  · intro h y hy
    have hiy := h (I • y)
    simp only [← smul_assoc, smul_eq_mul, I_mul_I, neg_smul, one_smul, neg_neg] at hiy
    si

中文:
引理 mem_symplComp_iff
  条件: {x : H} {S : ClosedSubmodule 实数 H}
  证明: by
  simp only [mem_orthogonal, mem_mapEquiv_iff, scalarSMulCLE_symm_apply, Units.smul_def,
    Units.val_inv_eq_inv_val, val_UnitI, inv_I, neg_smul]
  constructor
  · intro h y hy
    have hiy := h (I • y)
    simp only [← smul_assoc, smul_eq_mul, I_mul_I, neg_smul, one_smul, neg_neg] at hiy
    si

Depends on / 依赖: I_mul_I, Units.smul_def, Units.val_inv_eq_inv_val, inner_real_eq_re_inner, inner_smul_left, inv_I, mem_mapEquiv_iff, mem_orthogonal, neg_neg, neg_smul, one_smul, scalarSMulCLE_symm_apply, smul_assoc, smul_def, smul_eq_mul, val_UnitI, val_inv_eq_inv_val
-/
lemma mem_symplComp_iff {x : H} {S : ClosedSubmodule Real H} :
    x in S.symplComp ↔ forall y in S, ⟪y, x⟫.im = 0 := by
  simp only [mem_orthogonal, mem_mapEquiv_iff, scalarSMulCLE_symm_apply, Units.smul_def,
    Units.val_inv_eq_inv_val, val_UnitI, inv_I, neg_smul]
  constructor
  · intro h y hy
    have hiy := h (I • y)
    simp only [← smul_assoc, smul_eq_mul, I_mul_I, neg_smul, one_smul, neg_neg] at hiy
    simpa [inner_real_eq_re_inner] using! hiy hy
  · intro h _ hy
    have hiy := h _ hy
    simpa [inner_smul_left] using! hiy

/--
lemma `mulI_orthogonal_eq_symplComp` / 引理 `mulI_orthogonal_eq_symplComp`

English:
lemma mulI_orthogonal_eq_symplComp
  given: (S : ClosedSubmodule Real H)
  statement: Sᗮ.mulI = S.symplComp
  proof: by
  ext x
  rw [← mem_iff]; rw [← mem_iff]; rw [mem_symplComp_iff]; rw [mem_mapEquiv_iff]; rw [scalarSMulCLE_symm_apply]; rw [Units.inv_mk]; rw [Units.smul_mk_apply]
  simp [inner_real_eq_re_inner]

中文:
引理 mulI_orthogonal_eq_symplComp
  条件: (S : ClosedSubmodule 实数 H)
  结论: Sᗮ.mulI = S.symplComp
  证明: by
  ext x
  rw [← mem_iff]; rw [← mem_iff]; rw [mem_symplComp_iff]; rw [mem_mapEquiv_iff]; rw [scalarSMulCLE_symm_apply]; rw [Units.inv_mk]; rw [Units.smul_mk_apply]
  simp [inner_real_eq_re_inner]

Depends on / 依赖: Units.inv_mk, Units.smul_mk_apply, inner_real_eq_re_inner, inv_mk, mem_iff, mem_mapEquiv_iff, mem_symplComp_iff, scalarSMulCLE_symm_apply, smul_mk_apply
-/
lemma mulI_orthogonal_eq_symplComp (S : ClosedSubmodule Real H) : Sᗮ.mulI = S.symplComp := by
  ext x
  rw [← mem_iff]; rw [← mem_iff]; rw [mem_symplComp_iff]; rw [mem_mapEquiv_iff]; rw [scalarSMulCLE_symm_apply]; rw [Units.inv_mk]; rw [Units.smul_mk_apply]
  simp [inner_real_eq_re_inner]


/--
lemma `mulI_orthogonal` / 引理 `mulI_orthogonal`

English:
lemma mulI_orthogonal
  given: (S : ClosedSubmodule Real H)
  statement: Sᗮ.mulI = S.mulIᗮ
  proof: by
  rw [mulI_orthogonal_eq_symplComp]

@[simp]

中文:
引理 mulI_orthogonal
  条件: (S : ClosedSubmodule 实数 H)
  结论: Sᗮ.mulI = S.mulIᗮ
  证明: by
  rw [mulI_orthogonal_eq_symplComp]

@[simp]

Depends on / 依赖: mulI_orthogonal_eq_symplComp
-/
lemma mulI_orthogonal (S : ClosedSubmodule Real H) : Sᗮ.mulI = S.mulIᗮ := by
  rw [mulI_orthogonal_eq_symplComp]

@[simp]
/--
lemma `mulI_symplComp` / 引理 `mulI_symplComp`

English:
lemma mulI_symplComp
  given: {S : ClosedSubmodule Real H}
  proof: by
  rw [symplComp]; rw [symplComp]; rw [mulI_orthogonal_eq_symplComp]

@[simp]

中文:
引理 mulI_symplComp
  条件: {S : ClosedSubmodule 实数 H}
  证明: by
  rw [symplComp]; rw [symplComp]; rw [mulI_orthogonal_eq_symplComp]

@[simp]

Depends on / 依赖: mulI_orthogonal_eq_symplComp, symplComp
-/
lemma mulI_symplComp {S : ClosedSubmodule Real H} :
    S.symplComp.mulI = S.mulI.symplComp := by
  rw [symplComp]; rw [symplComp]; rw [mulI_orthogonal_eq_symplComp]

@[simp]
/--
lemma `mulI_mulI_eq` / 引理 `mulI_mulI_eq`

English:
lemma mulI_mulI_eq
  given: (S : ClosedSubmodule Real H)
  statement: S.mulI.mulI = S
  proof: by
  ext x
  simp only [Submodule.carrier_eq_coe, coe_toSubmodule, SetLike.mem_coe]
  constructor
  · intro h
    rw [mem_mapEquiv_iff (scalarSMulCLE H UnitI)]; rw [← SetLike.forall_smul_mem_iff] at h
    simpa [← smul_assoc, Units.smul_def] using (h (-1 : Real))
  · intro h
    rw [← SetLike.forall

中文:
引理 mulI_mulI_eq
  条件: (S : ClosedSubmodule 实数 H)
  结论: S.mulI.mulI = S
  证明: by
  ext x
  simp only [Submodule.carrier_eq_coe, coe_toSubmodule, SetLike.mem_coe]
  constructor
  · intro h
    rw [mem_mapEquiv_iff (scalarSMulCLE H UnitI)]; rw [← SetLike.forall_smul_mem_iff] at h
    simpa [← smul_assoc, Units.smul_def] using (h (-1 : Real))
  · intro h
    rw [← SetLike.forall

Depends on / 依赖: SetLike, SetLike.forall_smul_mem_iff, SetLike.mem_coe, Submodule, Submodule.carrier_eq_coe, Units.smul_def, carrier_eq_coe, coe_toSubmodule, forall_smul_mem_iff, mem_coe, mem_mapEquiv_iff, scalarSMulCLE, smul_assoc, smul_def
-/
lemma mulI_mulI_eq (S : ClosedSubmodule Real H) : S.mulI.mulI = S := by
  ext x
  simp only [Submodule.carrier_eq_coe, coe_toSubmodule, SetLike.mem_coe]
  constructor
  · intro h
    rw [mem_mapEquiv_iff (scalarSMulCLE H UnitI)]; rw [← SetLike.forall_smul_mem_iff] at h
    simpa [← smul_assoc, Units.smul_def] using (h (-1 : Real))
  · intro h
    rw [← SetLike.forall_smul_mem_iff] at h
    simpa [← smul_assoc, Units.smul_def] using (h (-1 : Real))

/--
lemma `involutive_mulI` / 引理 `involutive_mulI`

English:
lemma involutive_mulI
  proof: mulI_mulI_eq

@[simp]

中文:
引理 involutive_mulI
  证明: mulI_mulI_eq

@[simp]

Depends on / 依赖: mulI_mulI_eq
-/
lemma involutive_mulI :
    Function.Involutive (mulI : ClosedSubmodule Real H -> ClosedSubmodule Real H) := mulI_mulI_eq

@[simp]
/--
lemma `symplComp_symplComp_eq` / 引理 `symplComp_symplComp_eq`

English:
lemma symplComp_symplComp_eq
  given: [CompleteSpace H] {S : ClosedSubmodule Real H}
  proof: by simp [symplComp]

中文:
引理 symplComp_symplComp_eq
  条件: [CompleteSpace H] {S : ClosedSubmodule 实数 H}
  证明: by simp [symplComp]

Depends on / 依赖: symplComp
-/
lemma symplComp_symplComp_eq [CompleteSpace H] {S : ClosedSubmodule Real H} :
    S.symplComp.symplComp = S := by simp [symplComp]

/--
lemma `mulI_sup` / 引理 `mulI_sup`

English:
lemma mulI_sup
  given: (S T : ClosedSubmodule Real H)
  proof: by
  rw [mulI]; rw [← mapEquiv_sup_eq]

中文:
引理 mulI_sup
  条件: (S T : ClosedSubmodule 实数 H)
  证明: by
  rw [mulI]; rw [← mapEquiv_sup_eq]

Depends on / 依赖: mapEquiv_sup_eq
-/
lemma mulI_sup (S T : ClosedSubmodule Real H) :
    (S ⊔ T).mulI = S.mulI ⊔ T.mulI := by
  rw [mulI]; rw [← mapEquiv_sup_eq]

/--
lemma `mulI_inf` / 引理 `mulI_inf`

English:
lemma mulI_inf
  given: (S T : ClosedSubmodule Real H)
  proof: by
  rw [mulI]; rw [← mapEquiv_inf_eq]

@[simp]

中文:
引理 mulI_inf
  条件: (S T : ClosedSubmodule 实数 H)
  证明: by
  rw [mulI]; rw [← mapEquiv_inf_eq]

@[simp]

Depends on / 依赖: mapEquiv_inf_eq
-/
lemma mulI_inf (S T : ClosedSubmodule Real H) :
    (S ⊓ T).mulI = S.mulI ⊓ T.mulI := by
  rw [mulI]; rw [← mapEquiv_inf_eq]

@[simp]
/--
lemma `symplComp_sup` / 引理 `symplComp_sup`

English:
lemma symplComp_sup
  given: (S T : ClosedSubmodule Real H)
  proof: by
  rw [symplComp]; rw [symplComp]; rw [symplComp]; rw [mulI_sup]
  exact Eq.symm (inf_orthogonal S.mulI T.mulI)

@[simp]

中文:
引理 symplComp_sup
  条件: (S T : ClosedSubmodule 实数 H)
  证明: by
  rw [symplComp]; rw [symplComp]; rw [symplComp]; rw [mulI_sup]
  exact Eq.symm (inf_orthogonal S.mulI T.mulI)

@[simp]

Depends on / 依赖: Eq.symm, S.mulI, T.mulI, inf_orthogonal, mulI_sup, symplComp
-/
lemma symplComp_sup (S T : ClosedSubmodule Real H) :
    (S ⊔ T).symplComp = S.symplComp ⊓ T.symplComp := by
  rw [symplComp]; rw [symplComp]; rw [symplComp]; rw [mulI_sup]
  exact Eq.symm (inf_orthogonal S.mulI T.mulI)

@[simp]
/--
lemma `symplComp_inf` / 引理 `symplComp_inf`

English:
lemma symplComp_inf
  given: [CompleteSpace H] (S T : ClosedSubmodule Real H)
  proof: by
  rw [symplComp]; rw [symplComp]; rw [symplComp]; rw [mulI_inf]
  exact Eq.symm (sup_orthogonal S.mulI T.mulI)

中文:
引理 symplComp_inf
  条件: [CompleteSpace H] (S T : ClosedSubmodule 实数 H)
  证明: by
  rw [symplComp]; rw [symplComp]; rw [symplComp]; rw [mulI_inf]
  exact Eq.symm (sup_orthogonal S.mulI T.mulI)

Depends on / 依赖: Eq.symm, S.mulI, T.mulI, mulI_inf, sup_orthogonal, symplComp
-/
lemma symplComp_inf [CompleteSpace H] (S T : ClosedSubmodule Real H) :
    (S ⊓ T).symplComp = S.symplComp ⊔ T.symplComp := by
  rw [symplComp]; rw [symplComp]; rw [symplComp]; rw [mulI_inf]
  exact Eq.symm (sup_orthogonal S.mulI T.mulI)

end ClosedSubmodule

section Def

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace Complex H]

/-- A standard subspace `S` of a complex Hilbert space (or just an inner product space) `H` is a
closed real subspace `S` such that `S ⊓ i S = ⊥` and `S ⊔ i S = ⊤`. -/
@[ext]
/--
Definition of `StandardSubspace` / `StandardSubspace` 的定义

English:
structure StandardSubspace
  parameters: where
  axioms and operations (3):
    - toClosedSubmodule : ClosedSubmodule Real H
    - IsSeparating : toClosedSubmodule ⊓ toClosedSubmodule.mulI = ⊥
    - IsCyclic : toClosedSubmodule ⊔ toClosedSubmodule.mulI = ⊤

中文:
结构 StandardSubspace
  参数: where
  公理与运算 (3 个):
    - toClosedSubmodule : ClosedSubmodule 实数 H
    - IsSeparating : toClosedSubmodule ⊓ toClosedSubmodule.mulI = ⊥
    - IsCyclic : toClosedSubmodule ⊔ toClosedSubmodule.mulI = ⊤
-/
structure StandardSubspace where
  /-- A real closed subspace `S`. -/
  toClosedSubmodule : ClosedSubmodule Real H
  /-- `S` is separating, that is, `S ⊓ i S` is the trivial subspace. -/
  IsSeparating : toClosedSubmodule ⊓ toClosedSubmodule.mulI = ⊥
  /-- `S` is cyclic, that is, `S ⊔ i S` is the whole space. -/
  IsCyclic : toClosedSubmodule ⊔ toClosedSubmodule.mulI = ⊤

end Def

namespace StandardSubspace

open ClosedSubmodule

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace Complex H]

@[simp]
/--
lemma `toClosedSubmodule_inj` / 引理 `toClosedSubmodule_inj`

English:
lemma toClosedSubmodule_inj
  given: {S T : StandardSubspace H}
  proof: StandardSubspace.ext_iff.symm

中文:
引理 toClosedSubmodule_inj
  条件: {S T : StandardSubspace H}
  证明: StandardSubspace.ext_iff.symm

Depends on / 依赖: StandardSubspace, StandardSubspace.ext_iff.symm, ext_iff
-/
lemma toClosedSubmodule_inj {S T : StandardSubspace H} :
    S.toClosedSubmodule = T.toClosedSubmodule ↔ S = T :=
  StandardSubspace.ext_iff.symm

/--
lemma `toClosedSubmodule_injective` / 引理 `toClosedSubmodule_injective`

English:
lemma toClosedSubmodule_injective
  statement: Function.Injective (toClosedSubmodule (H := H))
  proof: fun _ _ => toClosedSubmodule_inj.mp

中文:
引理 toClosedSubmodule_injective
  结论: Function.Injective (toClosedSubmodule (H := H))
  证明: fun _ _ => toClosedSubmodule_inj.mp
-/
lemma toClosedSubmodule_injective : Function.Injective (toClosedSubmodule (H := H)) :=
  fun _ _ => toClosedSubmodule_inj.mp

/--
Definition of `mulI` / `mulI` 的定义

English:
definition mulI
  signature: (S : StandardSubspace H)
  body: S.toClosedSubmodule.mulI
  IsSeparating := by simpa [mulI_mulI_eq, inf_comm] using S.IsSeparating
  IsCyclic := by simpa [mulI_mulI_eq, sup_comm] using S.IsCyclic

中文:
定义 mulI
  签名: (S : StandardSubspace H)
  定义体: S.toClosedSubmodule.mulI
  IsSeparating := by simpa [mulI_mulI_eq, inf_comm] using S.IsSeparating
  IsCyclic := by simpa [mulI_mulI_eq, sup_comm] using S.IsCyclic

Depends on / 依赖: S.toClosedSubmodule.mulI, toClosedSubmodule
-/
noncomputable def mulI (S : StandardSubspace H) : StandardSubspace H where
  toClosedSubmodule := S.toClosedSubmodule.mulI
  IsSeparating := by simpa [mulI_mulI_eq, inf_comm] using S.IsSeparating
  IsCyclic := by simpa [mulI_mulI_eq, sup_comm] using S.IsCyclic

/--
Definition of `symplComp` / `symplComp` 的定义

English:
definition symplComp
  signature: [CompleteSpace H] (S : StandardSubspace H)
  body: S.toClosedSubmodule.symplComp
  IsSeparating := by
    simp [mulI_symplComp, ClosedSubmodule.inf_orthogonal, sup_comm, S.IsCyclic]
  IsCyclic := by
    simp [mulI_symplComp, ClosedSubmodule.sup_orthogonal, inf_comm, S.IsSeparating]

@[simp]

中文:
定义 symplComp
  签名: [CompleteSpace H] (S : StandardSubspace H)
  定义体: S.toClosedSubmodule.symplComp
  IsSeparating := by
    simp [mulI_symplComp, ClosedSubmodule.inf_orthogonal, sup_comm, S.IsCyclic]
  IsCyclic := by
    simp [mulI_symplComp, ClosedSubmodule.sup_orthogonal, inf_comm, S.IsSeparating]

@[simp]

Depends on / 依赖: S.toClosedSubmodule.symplComp, symplComp, toClosedSubmodule
-/
noncomputable def symplComp [CompleteSpace H] (S : StandardSubspace H) : StandardSubspace H where
  toClosedSubmodule := S.toClosedSubmodule.symplComp
  IsSeparating := by
    simp [mulI_symplComp, ClosedSubmodule.inf_orthogonal, sup_comm, S.IsCyclic]
  IsCyclic := by
    simp [mulI_symplComp, ClosedSubmodule.sup_orthogonal, inf_comm, S.IsSeparating]

@[simp]
/--
theorem `symplComp_symplComp_eq` / 定理 `symplComp_symplComp_eq`

English:
theorem symplComp_symplComp_eq
  given: [CompleteSpace H] (S : StandardSubspace H)
  proof: toClosedSubmodule_inj.mp ClosedSubmodule.symplComp_symplComp_eq

中文:
定理 symplComp_symplComp_eq
  条件: [CompleteSpace H] (S : StandardSubspace H)
  证明: toClosedSubmodule_inj.mp ClosedSubmodule.symplComp_symplComp_eq

Depends on / 依赖: ClosedSubmodule, ClosedSubmodule.symplComp_symplComp_eq, symplComp_symplComp_eq, toClosedSubmodule_inj, toClosedSubmodule_inj.mp
-/
theorem symplComp_symplComp_eq [CompleteSpace H] (S : StandardSubspace H) :
    S.symplComp.symplComp = S := toClosedSubmodule_inj.mp ClosedSubmodule.symplComp_symplComp_eq

/--
lemma `involutive_symplComp` / 引理 `involutive_symplComp`

English:
lemma involutive_symplComp
  given: [CompleteSpace H]
  proof: symplComp_symplComp_eq

中文:
引理 involutive_symplComp
  条件: [CompleteSpace H]
  证明: symplComp_symplComp_eq

Depends on / 依赖: symplComp_symplComp_eq
-/
lemma involutive_symplComp [CompleteSpace H] :
    Function.Involutive (symplComp : StandardSubspace H -> StandardSubspace H)
  := symplComp_symplComp_eq

end StandardSubspace
