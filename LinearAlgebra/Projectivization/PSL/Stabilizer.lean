/-
Copyright (c) 2026 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie
-/

module

public import Mathlib.LinearAlgebra.Projectivization.Action

/-!
# Stabilizer of a line in PSL(n, F)
This file contains key constructions to prove that `PSL(n, F)` is simple via
showing it has an Iwasawa structure.

## Main definitions

* `Matrix.SpecialLinearGroup.lineStab` : the unipotent radical attached to a subspace `L ⊆ ι → F`
  defined as the subgroup of `SL ι F` consisting of matrices `A` such that `A - 1`
  sends every vector into `L`.

* `PSL.iwasawaT` : the candidate family of subgroups for the Iwasawa structure on
  `PSL ι F` acting on the projective space `ℙ F (ι → F)` from `Matrix.SpecialLinearGroup.lineStab`.

-/

@[expose] public section

variable {F : Type*} [Field F] {ι : Type*} [DecidableEq ι] [Fintype ι]

/--
Definition of `Matrix.SpecialLinearGroup.lineStab` / `Matrix.SpecialLinearGroup.lineStab` 的定义

English:
definition Matrix.SpecialLinearGroup.lineStab
  signature: (L : Submodule F (ι -> F))
  body: {A | forall w : ι -> F, A • w - w in L}
  one_mem' := by simp
  mul_mem' {A B} hA hB := fun w => by
    simp only [Set.mem_ofPred_eq, mul_smul] at hA hB ⊢
    rw [show A • B • w - w = ((A • (B • w) - A • w) - (B • w - w)) +
      (B • w - w) + (A • w - w) by abel]; rw [← smul_sub]
    exact add_mem 

中文:
定义 矩阵.SpecialLinearGroup.lineStab
  签名: (L : 子模 F (ι -> F))
  定义体: {A | forall w : ι -> F, A • w - w in L}
  one_mem' := by simp
  mul_mem' {A B} hA hB := fun w => by
    simp only [Set.mem_ofPred_eq, mul_smul] at hA hB ⊢
    rw [show A • B • w - w = ((A • (B • w) - A • w) - (B • w - w)) +
      (B • w - w) + (A • w - w) by abel]; rw [← smul_sub]
    exact add_mem 
-/
def Matrix.SpecialLinearGroup.lineStab (L : Submodule F (ι -> F)) :
    Subgroup (SpecialLinearGroup ι F) where
  carrier := {A | forall w : ι -> F, A • w - w in L}
  one_mem' := by simp
  mul_mem' {A B} hA hB := fun w => by
    simp only [Set.mem_ofPred_eq, mul_smul] at hA hB ⊢
    rw [show A • B • w - w = ((A • (B • w) - A • w) - (B • w - w)) +
      (B • w - w) + (A • w - w) by abel]; rw [← smul_sub]
    exact add_mem (add_mem (hA _) (hB w)) (hA w)
  inv_mem' {A} hA := fun w => by
    convert neg_mem (hA (A⁻¹ • w)) using 1
    rw [← mul_smul]; rw [mul_inv_cancel]; rw [one_smul]; rw [neg_sub]

@[simp]
/--
lemma `Matrix.SpecialLinearGroup.mem_lineStab_iff` / 引理 `Matrix.SpecialLinearGroup.mem_lineStab_iff`

English:
lemma Matrix.SpecialLinearGroup.mem_lineStab_iff
  statement: (A : SpecialLinearGroup ι F)
  proof: Iff.rfl

中文:
引理 矩阵.SpecialLinearGroup.mem_lineStab_iff
  结论: (A : SpecialLinearGroup ι F)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma Matrix.SpecialLinearGroup.mem_lineStab_iff (A : SpecialLinearGroup ι F)
    (L : Submodule F (ι -> F)) : A in lineStab L ↔ forall w : ι -> F, A • w - w in L :=
  Iff.rfl

open scoped LinearAlgebra.Projectivization

/--
Definition of `PSL.iwasawaT` / `PSL.iwasawaT` 的定义

English:
abbreviation PSL.iwasawaT
  signature: (p : ℙ F (ι -> F))
  body: Subgroup.map (QuotientGroup.mk' _)
    (Matrix.SpecialLinearGroup.lineStab p.submodule)

中文:
缩写 PSL.iwasawaT
  签名: (p : ℙ F (ι -> F))
  定义体: Subgroup.map (QuotientGroup.mk' _)
    (Matrix.SpecialLinearGroup.lineStab p.submodule)

Depends on / 依赖: Matrix, Matrix.SpecialLinearGroup.lineStab, QuotientGroup, QuotientGroup.mk, SpecialLinearGroup, Subgroup, Subgroup.map, lineStab, p.submodule, submodule
-/
noncomputable abbrev PSL.iwasawaT (p : ℙ F (ι -> F)) :
    Subgroup (Matrix.ProjectiveSpecialLinearGroup ι F) :=
  Subgroup.map (QuotientGroup.mk' _)
    (Matrix.SpecialLinearGroup.lineStab p.submodule)

open scoped Pointwise

/--
lemma `PSL.smul_submodule` / 引理 `PSL.smul_submodule`

English:
lemma PSL.smul_submodule
  given: (g : Matrix.SpecialLinearGroup ι F) (p : ℙ F (ι -> F))
  proof: by
  induction p using Projectivization.ind with | _ v hv => ?_
  simp [Submodule.ext_iff, Submodule.pointwise_smul_def, Submodule.mem_span_singleton, smul_comm]

中文:
引理 PSL.smul_submodule
  条件: (g : 矩阵.SpecialLinearGroup ι F) (p : ℙ F (ι -> F))
  证明: by
  induction p using Projectivization.ind with | _ v hv => ?_
  simp [Submodule.ext_iff, Submodule.pointwise_smul_def, Submodule.mem_span_singleton, smul_comm]

Depends on / 依赖: Projectivization, Projectivization.ind, Submodule, Submodule.ext_iff, Submodule.mem_span_singleton, Submodule.pointwise_smul_def, ext_iff, mem_span_singleton, pointwise_smul_def, smul_comm
-/
lemma PSL.smul_submodule (g : Matrix.SpecialLinearGroup ι F) (p : ℙ F (ι -> F)) :
    (g • p).submodule = g • p.submodule:= by
  induction p using Projectivization.ind with | _ v hv => ?_
  simp [Submodule.ext_iff, Submodule.pointwise_smul_def, Submodule.mem_span_singleton, smul_comm]

/--
lemma `Matrix.SpecialLinearGroup.lineStab_smul` / 引理 `Matrix.SpecialLinearGroup.lineStab_smul`

English:
lemma Matrix.SpecialLinearGroup.lineStab_smul
  proof: by
  ext A
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp only [mem_lineStab_iff, Submodule.mem_smul_pointwise_iff_exists, MulAut.smul_def,
    MulAut.inv_apply, MulAut.conj_symm_apply]
  refine ⟨fun hA w => ?_, fun hA w => ⟨g⁻¹ • (A • w - w), ?_, by simp⟩⟩
  · obtain ⟨v, hv, hvw⟩ := hA 

中文:
引理 矩阵.SpecialLinearGroup.lineStab_smul
  证明: by
  ext A
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp only [mem_lineStab_iff, Submodule.mem_smul_pointwise_iff_exists, MulAut.smul_def,
    MulAut.inv_apply, MulAut.conj_symm_apply]
  refine ⟨fun hA w => ?_, fun hA w => ⟨g⁻¹ • (A • w - w), ?_, by simp⟩⟩
  · obtain ⟨v, hv, hvw⟩ := hA 

Depends on / 依赖: MulAut, MulAut.conj_symm_apply, MulAut.inv_apply, MulAut.smul_def, Subgroup, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Submodule, Submodule.mem_smul_pointwise_iff_exists, conj_symm_apply, eq_comm, inv_apply, mem_lineStab_iff, mem_pointwise_smul_iff_inv_smul_mem, mem_smul_pointwise_iff_exists, mul_smul, smul_def, smul_sub, sub_eq_iff_eq_add
-/
lemma Matrix.SpecialLinearGroup.lineStab_smul
    (g : Matrix.SpecialLinearGroup ι F) (L : Submodule F (ι -> F)) :
    Matrix.SpecialLinearGroup.lineStab (g • L) =
      MulAut.conj g • Matrix.SpecialLinearGroup.lineStab L := by
  ext A
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp only [mem_lineStab_iff, Submodule.mem_smul_pointwise_iff_exists, MulAut.smul_def,
    MulAut.inv_apply, MulAut.conj_symm_apply]
  refine ⟨fun hA w => ?_, fun hA w => ⟨g⁻¹ • (A • w - w), ?_, by simp⟩⟩
  · obtain ⟨v, hv, hvw⟩ := hA (g • w)
    simp_all [eq_comm (a := g • v), sub_eq_iff_eq_add, mul_smul]
  · simpa [mul_smul, smul_sub] using hA (g⁻¹ • w)

/--
lemma `PSL.iwasawaT_map_conj` / 引理 `PSL.iwasawaT_map_conj`

English:
lemma PSL.iwasawaT_map_conj
  statement: (g : Matrix.SpecialLinearGroup ι F)
  proof: by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    MulAut.smul_def, MulAut.inv_apply, MulAut.conj_symm_apply, QuotientGroup.mk'_apply]
  exact ⟨fun ⟨a, ha, ha'⟩ => ⟨g⁻¹ * a * g, ha, by simp [ha']⟩,
    fun ⟨a, ha, hx⟩ => ⟨g * a * g⁻¹, by simp [mul_assoc, ha],

中文:
引理 PSL.iwasawaT_map_conj
  结论: (g : 矩阵.SpecialLinearGroup ι F)
  证明: by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    MulAut.smul_def, MulAut.inv_apply, MulAut.conj_symm_apply, QuotientGroup.mk'_apply]
  exact ⟨fun ⟨a, ha, ha'⟩ => ⟨g⁻¹ * a * g, ha, by simp [ha']⟩,
    fun ⟨a, ha, hx⟩ => ⟨g * a * g⁻¹, by simp [mul_assoc, ha],

Depends on / 依赖: MulAut, MulAut.conj_symm_apply, MulAut.inv_apply, MulAut.smul_def, QuotientGroup, QuotientGroup.mk, Subgroup, Subgroup.mem_map, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, _apply, conj_symm_apply, inv_apply, mem_map, mem_pointwise_smul_iff_inv_smul_mem, mul_assoc, smul_def
-/
lemma PSL.iwasawaT_map_conj (g : Matrix.SpecialLinearGroup ι F)
    (H : Subgroup (Matrix.SpecialLinearGroup ι F)) :
    Subgroup.map (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup ι F)))
        (MulAut.conj g • H) =
      MulAut.conj (QuotientGroup.mk g : Matrix.ProjectiveSpecialLinearGroup ι F) •
        Subgroup.map (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup ι F))) H := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    MulAut.smul_def, MulAut.inv_apply, MulAut.conj_symm_apply, QuotientGroup.mk'_apply]
  exact ⟨fun ⟨a, ha, ha'⟩ => ⟨g⁻¹ * a * g, ha, by simp [ha']⟩,
    fun ⟨a, ha, hx⟩ => ⟨g * a * g⁻¹, by simp [mul_assoc, ha], by simp [hx, mul_assoc]⟩⟩

/--
lemma `LinearMap.exists_restrict_span_singleton_eq_smul_id` / 引理 `LinearMap.exists_restrict_span_singleton_eq_smul_id`

English:
lemma LinearMap.exists_restrict_span_singleton_eq_smul_id
  proof: by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hAv
  refine ⟨c, hc.symm, fun w hw => ?_, LinearMap.ext fun ⟨w, hw⟩ => ?_⟩
  <;> obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hw
  · simpa [Submodule.mem_comap, map_smul] using Submodule.smul_mem _ _ hAv
  · simp [Subtype.ext_iff, ← hc, smul

中文:
引理 线性映射.存在_restrict_span_singleton_eq_smul_id
  证明: by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hAv
  refine ⟨c, hc.symm, fun w hw => ?_, LinearMap.ext fun ⟨w, hw⟩ => ?_⟩
  <;> obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hw
  · simpa [Submodule.mem_comap, map_smul] using Submodule.smul_mem _ _ hAv
  · simp [Subtype.ext_iff, ← hc, smul
-/
private lemma LinearMap.exists_restrict_span_singleton_eq_smul_id
    {R V : Type*} [CommSemiring R] [AddCommMonoid V] [Module R V]
    {v : V} {A : V ->ₗ[R] V} (hAv : A v in Submodule.span R {v}) :
    exists c : R, A v = c • v ∧ exists hcomap : Submodule.span R {v} <= (Submodule.span R {v}).comap A,
      A.restrict hcomap = (c • LinearMap.id : Submodule.span R {v} ->ₗ[R] _) := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hAv
  refine ⟨c, hc.symm, fun w hw => ?_, LinearMap.ext fun ⟨w, hw⟩ => ?_⟩
  <;> obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hw
  · simpa [Submodule.mem_comap, map_smul] using Submodule.smul_mem _ _ hAv
  · simp [Subtype.ext_iff, ← hc, smul_comm a c v]

/--
lemma `Matrix.SpecialLinearGroup.lineStab_fix_of_span` / 引理 `Matrix.SpecialLinearGroup.lineStab_fix_of_span`

English:
lemma Matrix.SpecialLinearGroup.lineStab_fix_of_span
  proof: by
  set L : Submodule F (ι -> F) := Submodule.span F {v}
  obtain ⟨c, hcv, hcomap, hres⟩ :=
    LinearMap.exists_restrict_span_singleton_eq_smul_id (A := A.toLin'.toLinearMap)
      (by simpa using! add_mem (hA v) (Submodule.mem_span_singleton_self v))
  have hQ : L.mapQ L A.toLin'.toLinearMap hcom

中文:
引理 矩阵.SpecialLinearGroup.lineStab_fix_of_span
  证明: by
  set L : Submodule F (ι -> F) := Submodule.span F {v}
  obtain ⟨c, hcv, hcomap, hres⟩ :=
    LinearMap.exists_restrict_span_singleton_eq_smul_id (A := A.toLin'.toLinearMap)
      (by simpa using! add_mem (hA v) (Submodule.mem_span_singleton_self v))
  have hQ : L.mapQ L A.toLin'.toLinearMap hcom

Depends on / 依赖: A.toLin, L.mapQ, LinearMap, LinearMap.exists_restrict_span_singleton_eq_smul_id, LinearMap.ext, LinearMap.id, Quotient, Submodule, Submodule.Quotient.eq, Submodule.Quotient.induction_on, Submodule.mem_span_singleton_self, Submodule.span, add_mem, det_eq_det_mul_det, exists_restrict_span_singleton_eq_smul_id, hcomap, induction_on, mem_span_singleton_self, toLinearMap, toLinearMap.det_eq_det_mul_det
-/
lemma Matrix.SpecialLinearGroup.lineStab_fix_of_span
    (v : ι -> F) (hv : v != 0)
    (A : Matrix.SpecialLinearGroup ι F)
    (hA : A in lineStab (Submodule.span F {v})) :
    A • v = v := by
  set L : Submodule F (ι -> F) := Submodule.span F {v}
  obtain ⟨c, hcv, hcomap, hres⟩ :=
    LinearMap.exists_restrict_span_singleton_eq_smul_id (A := A.toLin'.toLinearMap)
      (by simpa using! add_mem (hA v) (Submodule.mem_span_singleton_self v))
  have hQ : L.mapQ L A.toLin'.toLinearMap hcomap = LinearMap.id := LinearMap.ext fun x => by
    induction x using Submodule.Quotient.induction_on with
    | _ w => simpa [Submodule.Quotient.eq] using! hA w
  have hdet := A.toLin'.toLinearMap.det_eq_det_mul_det L hcomap
  rw [show LinearMap.det A.toLin'.toLinearMap = 1 by simp [toLin'_to_linearMap],
      hres, hQ, LinearMap.det_smul, finrank_span_singleton hv, pow_one,
      LinearMap.det_id, LinearMap.det_id, mul_one, mul_one] at hdet
  exact hcv.trans (hdet ▸ one_smul F v)

/--
lemma `Matrix.SpecialLinearGroup.lineStab_isMulCommutative_of_span'` / 引理 `Matrix.SpecialLinearGroup.lineStab_isMulCommutative_of_span'`

English:
lemma Matrix.SpecialLinearGroup.lineStab_isMulCommutative_of_span'
  proof: by
refine Subtype.ext ext_iff_smul.2 fun w => ?_
  obtain ⟨α, hα⟩ := Submodule.mem_span_singleton.mp (hA w)
  obtain ⟨β, hβ⟩ := Submodule.mem_span_singleton.mp (hB w)
  simp only [coe_mul, mul_smul, ← Matrix.SpecialLinearGroup.smul_def]
  rw [← sub_add_cancel (A • w) w]; rw [← hα]; rw [← sub_add_can

中文:
引理 矩阵.SpecialLinearGroup.lineStab_isMulCommutative_of_span'
  证明: by
refine Subtype.ext ext_iff_smul.2 fun w => ?_
  obtain ⟨α, hα⟩ := Submodule.mem_span_singleton.mp (hA w)
  obtain ⟨β, hβ⟩ := Submodule.mem_span_singleton.mp (hB w)
  simp only [coe_mul, mul_smul, ← Matrix.SpecialLinearGroup.smul_def]
  rw [← sub_add_cancel (A • w) w]; rw [← hα]; rw [← sub_add_can

Depends on / 依赖: Matrix, Matrix.SpecialLinearGroup.smul_def, SpecialLinearGroup, Submodule, Submodule.mem_span_singleton.mp, Subtype, Subtype.ext, add_sub, coe_mul, ext_iff_smul, lineStab_fix_of_span, mem_span_singleton, mul_smul, smul_add, smul_comm, smul_def, sub_add_cancel, sub_left_inj
-/
lemma Matrix.SpecialLinearGroup.lineStab_isMulCommutative_of_span'
    (v : ι -> F) (hv : v != 0) (A B : SpecialLinearGroup ι F)
    (hA : A in SpecialLinearGroup.lineStab (Submodule.span F {v}))
    (hB : B in SpecialLinearGroup.lineStab (Submodule.span F {v})) :
    A * B = B * A := by
refine Subtype.ext ext_iff_smul.2 fun w => ?_
  obtain ⟨α, hα⟩ := Submodule.mem_span_singleton.mp (hA w)
  obtain ⟨β, hβ⟩ := Submodule.mem_span_singleton.mp (hB w)
  simp only [coe_mul, mul_smul, ← Matrix.SpecialLinearGroup.smul_def]
  rw [← sub_add_cancel (A • w) w]; rw [← hα]; rw [← sub_add_cancel (B • w) w]; rw [← hβ]; rw [smul_add]; rw [smul_add]; rw [← sub_left_inj (a := w)]; rw [← add_sub]; rw [← hα]; rw [← add_sub]; rw [← hβ]; rw [smul_comm]; rw [lineStab_fix_of_span v hv A hA]; rw [smul_comm]; rw [lineStab_fix_of_span v hv B hB]; rw [add_comm]

/--
lemma `Matrix.SpecialLinearGroup.lineStab_isMulCommutative_of_span` / 引理 `Matrix.SpecialLinearGroup.lineStab_isMulCommutative_of_span`

English:
lemma Matrix.SpecialLinearGroup.lineStab_isMulCommutative_of_span
  proof: ⟨⟨fun ⟨A, hA⟩ ⟨B, hB⟩ => by simpa using lineStab_isMulCommutative_of_span' v hv A B hA hB⟩⟩

中文:
引理 矩阵.SpecialLinearGroup.lineStab_isMulCommutative_of_span
  证明: ⟨⟨fun ⟨A, hA⟩ ⟨B, hB⟩ => by simpa using lineStab_isMulCommutative_of_span' v hv A B hA hB⟩⟩

Depends on / 依赖: lineStab_isMulCommutative_of_span
-/
lemma Matrix.SpecialLinearGroup.lineStab_isMulCommutative_of_span
    (v : ι -> F) (hv : v != 0) : IsMulCommutative (lineStab (Submodule.span F {v})) :=
  ⟨⟨fun ⟨A, hA⟩ ⟨B, hB⟩ => by simpa using lineStab_isMulCommutative_of_span' v hv A B hA hB⟩⟩
