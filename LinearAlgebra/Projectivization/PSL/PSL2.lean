/-
Copyright (c) 2026 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie
-/
module

public import Mathlib.GroupTheory.GroupAction.Iwasawa
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.LinearAlgebra.Projectivization.PSL.Stabilizer

/-!
-/

@[expose] public section

variable {ι F : Type*} [Field F] [DecidableEq ι] [Fintype ι]

open Matrix Matrix.SpecialLinearGroup

open scoped MatrixGroups

namespace SL2Gen

/--
lemma `transvection_mem_lineStab` / 引理 `transvection_mem_lineStab`

English:
lemma transvection_mem_lineStab
  given: {i j : ι} (hij : i != j) (b : F)
  proof: fun w => Submodule.mem_span_singleton.2 ⟨b * w j, by simp [mul_smul,
    Matrix.SpecialLinearGroup.smul_def, transvection_coe, add_smul, Matrix.single_mulVec_eq]⟩

中文:
引理 transvection_mem_lineStab
  条件: {i j : ι} (hij : i != j) (b : F)
  证明: fun w => Submodule.mem_span_singleton.2 ⟨b * w j, by simp [mul_smul,
    Matrix.SpecialLinearGroup.smul_def, transvection_coe, add_smul, Matrix.single_mulVec_eq]⟩

Depends on / 依赖: Matrix, Matrix.SpecialLinearGroup.smul_def, Matrix.single_mulVec_eq, SpecialLinearGroup, Submodule, Submodule.mem_span_singleton, add_smul, mem_span_singleton, mul_smul, single_mulVec_eq, smul_def, transvection_coe
-/
lemma transvection_mem_lineStab {i j : ι} (hij : i != j) (b : F) :
    transvection hij b in lineStab (Submodule.span F {(Pi.single i (1 : F) : ι -> F)}) :=
  fun w => Submodule.mem_span_singleton.2 ⟨b * w j, by simp [mul_smul,
    Matrix.SpecialLinearGroup.smul_def, transvection_coe, add_smul, Matrix.single_mulVec_eq]⟩

/--
lemma `transvection_mem_lineStab_sup` / 引理 `transvection_mem_lineStab_sup`

English:
lemma transvection_mem_lineStab_sup
  given: (t : TransvectionStruct (Fin 2) F)
  proof: by
  obtain ⟨i, j, hij, c⟩ := t
  simp only [Fin.isValue, TransvectionStruct.toSpecialLinearGroup_mk]
  fin_cases i <;> fin_cases j <;> try tauto
· exact Subgroup.mem_sup_left transvection_mem_lineStab zero_ne_one c
· exact Subgroup.mem_sup_right transvection_mem_lineStab one_ne_zero c

中文:
引理 transvection_mem_lineStab_sup
  条件: (t : TransvectionStruct (Fin 2) F)
  证明: by
  obtain ⟨i, j, hij, c⟩ := t
  simp only [Fin.isValue, TransvectionStruct.toSpecialLinearGroup_mk]
  fin_cases i <;> fin_cases j <;> try tauto
· exact Subgroup.mem_sup_left transvection_mem_lineStab zero_ne_one c
· exact Subgroup.mem_sup_right transvection_mem_lineStab one_ne_zero c

Depends on / 依赖: Fin.isValue, Subgroup, Subgroup.mem_sup_left, Subgroup.mem_sup_right, TransvectionStruct, TransvectionStruct.toSpecialLinearGroup_mk, fin_cases, isValue, mem_sup_left, mem_sup_right, one_ne_zero, toSpecialLinearGroup_mk, transvection_mem_lineStab, zero_ne_one
-/
lemma transvection_mem_lineStab_sup (t : TransvectionStruct (Fin 2) F) :
    t.toSpecialLinearGroup in
      lineStab (Submodule.span F {(Pi.single 0 1 : Fin 2 -> F)})
      ⊔ lineStab (Submodule.span F {(Pi.single 1 1 : Fin 2 -> F)}) := by
  obtain ⟨i, j, hij, c⟩ := t
  simp only [Fin.isValue, TransvectionStruct.toSpecialLinearGroup_mk]
  fin_cases i <;> fin_cases j <;> try tauto
· exact Subgroup.mem_sup_left transvection_mem_lineStab zero_ne_one c
· exact Subgroup.mem_sup_right transvection_mem_lineStab one_ne_zero c

/--
lemma `SL_card_two_lineStab_sup_eq_top` / 引理 `SL_card_two_lineStab_sup_eq_top`

English:
lemma SL_card_two_lineStab_sup_eq_top
  proof: le_antisymm le_top fun M _ => SL2.transvection_induction _
      (fun i j hij a => by simpa using transvection_mem_lineStab_sup ⟨i, j, hij, a⟩)
      (fun _ _ => mul_mem) M

中文:
引理 SL_card_two_lineStab_sup_eq_top
  证明: le_antisymm le_top fun M _ => SL2.transvection_induction _
      (fun i j hij a => by simpa using transvection_mem_lineStab_sup ⟨i, j, hij, a⟩)
      (fun _ _ => mul_mem) M

Depends on / 依赖: SL2.transvection_induction, le_antisymm, le_top, mul_mem, transvection_induction, transvection_mem_lineStab_sup
-/
lemma SL_card_two_lineStab_sup_eq_top :
    lineStab (Submodule.span F {(Pi.single 0 1: Fin 2 -> F)}) ⊔
      lineStab (Submodule.span F {(Pi.single 1 1: Fin 2 -> F)}) =
      (⊤ : Subgroup SL(2, F)) :=
  le_antisymm le_top fun M _ => SL2.transvection_induction _
      (fun i j hij a => by simpa using transvection_mem_lineStab_sup ⟨i, j, hij, a⟩)
      (fun _ _ => mul_mem) M

end SL2Gen

open scoped LinearAlgebra.Projectivization

/--
lemma `PSL.iSup_lineStab_eq_top` / 引理 `PSL.iSup_lineStab_eq_top`

English:
lemma PSL.iSup_lineStab_eq_top
  proof: by
  refine le_antisymm le_top (SL2Gen.SL_card_two_lineStab_sup_eq_top (F := F) ▸
    sup_le ?_ ?_)
  <;> rw [← Projectivization.submodule_mk (K := F) _ (Pi.single_ne_zero_iff.2 one_ne_zero)]
  <;> exact le_iSup_iff.2 fun b a => a _

中文:
引理 PSL.iSup_lineStab_eq_top
  证明: by
  refine le_antisymm le_top (SL2Gen.SL_card_two_lineStab_sup_eq_top (F := F) ▸
    sup_le ?_ ?_)
  <;> rw [← Projectivization.submodule_mk (K := F) _ (Pi.single_ne_zero_iff.2 one_ne_zero)]
  <;> exact le_iSup_iff.2 fun b a => a _

Depends on / 依赖: Pi.single_ne_zero_iff, Projectivization, Projectivization.submodule_mk, SL2Gen, SL2Gen.SL_card_two_lineStab_sup_eq_top, SL_card_two_lineStab_sup_eq_top, le_antisymm, le_iSup_iff, le_top, one_ne_zero, single_ne_zero_iff, submodule_mk, sup_le
-/
lemma PSL.iSup_lineStab_eq_top :
    (⨆ p : ℙ F (Fin 2 -> F), lineStab p.submodule) = (⊤ : Subgroup SL(2, F)) := by
  refine le_antisymm le_top (SL2Gen.SL_card_two_lineStab_sup_eq_top (F := F) ▸
    sup_le ?_ ?_)
  <;> rw [← Projectivization.submodule_mk (K := F) _ (Pi.single_ne_zero_iff.2 one_ne_zero)]
  <;> exact le_iSup_iff.2 fun b a => a _

/--
lemma `PSL.iSup_iwasawaT_eq_top` / 引理 `PSL.iSup_iwasawaT_eq_top`

English:
lemma PSL.iSup_iwasawaT_eq_top
  proof: by
  have step1 : iSup (PSL.iwasawaT (F := F) (ι := Fin 2)) =
      Subgroup.map (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)))
        (⨆ p : ℙ F (Fin 2 -> F),
          Matrix.SpecialLinearGroup.lineStab (F := F) (ι := Fin 2) p.submodule) := by
    rw [Subgroup.map_iSu

中文:
引理 PSL.iSup_iwasawaT_eq_top
  证明: by
  have step1 : iSup (PSL.iwasawaT (F := F) (ι := Fin 2)) =
      Subgroup.map (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)))
        (⨆ p : ℙ F (Fin 2 -> F),
          Matrix.SpecialLinearGroup.lineStab (F := F) (ι := Fin 2) p.submodule) := by
    rw [Subgroup.map_iSu

Depends on / 依赖: Matrix, Matrix.SpecialLinearGroup, Matrix.SpecialLinearGroup.lineStab, PSL.iSup_lineStab_eq_top, PSL.iwasawaT, QuotientGroup, QuotientGroup.mk, SpecialLinearGroup, Subgroup, Subgroup.center, Subgroup.map, Subgroup.map_iSup, Subgroup.map_top_of_surjective, _surjective, center, iSup_lineStab_eq_top, iwasawaT, lineStab, map_iSup, map_top_of_surjective
-/
lemma PSL.iSup_iwasawaT_eq_top :
    iSup (PSL.iwasawaT (F := F) (ι := Fin 2)) = ⊤ := by
  have step1 : iSup (PSL.iwasawaT (F := F) (ι := Fin 2)) =
      Subgroup.map (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)))
        (⨆ p : ℙ F (Fin 2 -> F),
          Matrix.SpecialLinearGroup.lineStab (F := F) (ι := Fin 2) p.submodule) := by
    rw [Subgroup.map_iSup]
  rw [step1]; rw [PSL.iSup_lineStab_eq_top]
  exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)

open MulAction

/--
Definition of `PSL2.Iwasawa` / `PSL2.Iwasawa` 的定义

English:
abbreviation PSL2.Iwasawa
  signature: : IwasawaStructure PSL(2, F) (ℙ F (Fin 2 -> F)) where
  body: PSL.iwasawaT
  is_comm p := by
    have hSL : IsMulCommutative (lineStab (F := F) (ι := Fin 2) p.submodule) := by
      rw [← Projectivization.mk_rep p]; rw [Projectivization.submodule_mk]
      exact lineStab_isMulCommutative_of_span p.rep p.rep_nonzero
    exact Subgroup.map_isMulCommutative _ _
 

中文:
缩写 PSL2.Iwasawa
  签名: : IwasawaStructure PSL(2, F) (ℙ F (Fin 2 -> F)) where
  定义体: PSL.iwasawaT
  is_comm p := by
    have hSL : IsMulCommutative (lineStab (F := F) (ι := Fin 2) p.submodule) := by
      rw [← Projectivization.mk_rep p]; rw [Projectivization.submodule_mk]
      exact lineStab_isMulCommutative_of_span p.rep p.rep_nonzero
    exact Subgroup.map_isMulCommutative _ _
 

Depends on / 依赖: PSL.iwasawaT, iwasawaT
-/
noncomputable abbrev PSL2.Iwasawa : IwasawaStructure PSL(2, F) (ℙ F (Fin 2 -> F)) where
  T := PSL.iwasawaT
  is_comm p := by
    have hSL : IsMulCommutative (lineStab (F := F) (ι := Fin 2) p.submodule) := by
      rw [← Projectivization.mk_rep p]; rw [Projectivization.submodule_mk]
      exact lineStab_isMulCommutative_of_span p.rep p.rep_nonzero
    exact Subgroup.map_isMulCommutative _ _
  is_conj g p := by
    obtain ⟨g_SL, rfl⟩ := QuotientGroup.mk_surjective g
    rw [Matrix.ProjectiveSpecialLinearGroup.smul_proj_mk]
    change Subgroup.map _ _ = _
    rw [PSL.smul_submodule]; rw [Matrix.SpecialLinearGroup.lineStab_smul]; rw [PSL.iwasawaT_map_conj]
  is_generator := PSL.iSup_iwasawaT_eq_top

namespace SL2Simple

open Matrix.SpecialLinearGroup

/--
lemma `PSL_commutator_eq_top` / 引理 `PSL_commutator_eq_top`

English:
lemma PSL_commutator_eq_top
  given: (hF : exists a : F, a != 0 ∧ a ^ 2 != 1)
  proof: by
  obtain ⟨a, ha, hasq⟩ := hF
  have : Group.IsPerfect SL(2, F) := ⟨SL2.commutator_eq_top ha hasq⟩
  have : Group.IsPerfect (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := inferInstance
  exact this.commutator_eq_top

中文:
引理 PSL_commutator_eq_top
  条件: (hF : 存在 a : F, a != 0 ∧ a ^ 2 != 1)
  证明: by
  obtain ⟨a, ha, hasq⟩ := hF
  have : Group.IsPerfect SL(2, F) := ⟨SL2.commutator_eq_top ha hasq⟩
  have : Group.IsPerfect (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := inferInstance
  exact this.commutator_eq_top

Depends on / 依赖: Group.IsPerfect, IsPerfect, Matrix, Matrix.ProjectiveSpecialLinearGroup, ProjectiveSpecialLinearGroup, SL2.commutator_eq_top, commutator_eq_top, this.commutator_eq_top
-/
lemma PSL_commutator_eq_top (hF : exists a : F, a != 0 ∧ a ^ 2 != 1) :
    commutator PSL(2, F) = ⊤ := by
  obtain ⟨a, ha, hasq⟩ := hF
  have : Group.IsPerfect SL(2, F) := ⟨SL2.commutator_eq_top ha hasq⟩
  have : Group.IsPerfect (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := inferInstance
  exact this.commutator_eq_top

/--
Instance `PSL_nontrivial` / 实例 `PSL_nontrivial`

English:
instance PSL_nontrivial
  signature: [Nontrivial ι]
  body: by
  obtain ⟨i₁, i₂, hij⟩ := exists_pair_ne ι
  set g : Matrix.SpecialLinearGroup ι F := transvection hij 1
  refine ⟨⟨(QuotientGroup.mk g : Matrix.ProjectiveSpecialLinearGroup ι F),
    1, fun h => one_ne_zero (α := F) ?_⟩⟩
  rwa [QuotientGroup.eq_one_iff, transvection_mem_center_iff] at h

中文:
实例 PSL_nontrivial
  签名: [Nontrivial ι]
  定义体: by
  obtain ⟨i₁, i₂, hij⟩ := exists_pair_ne ι
  set g : Matrix.SpecialLinearGroup ι F := transvection hij 1
  refine ⟨⟨(QuotientGroup.mk g : Matrix.ProjectiveSpecialLinearGroup ι F),
    1, fun h => one_ne_zero (α := F) ?_⟩⟩
  rwa [QuotientGroup.eq_one_iff, transvection_mem_center_iff] at h

Depends on / 依赖: Matrix, Matrix.ProjectiveSpecialLinearGroup, Matrix.SpecialLinearGroup, ProjectiveSpecialLinearGroup, QuotientGroup, QuotientGroup.eq_one_iff, QuotientGroup.mk, SpecialLinearGroup, eq_one_iff, exists_pair_ne, one_ne_zero, transvection, transvection_mem_center_iff
-/
instance PSL_nontrivial [Nontrivial ι] :
    Nontrivial (Matrix.ProjectiveSpecialLinearGroup ι F) := by
  obtain ⟨i₁, i₂, hij⟩ := exists_pair_ne ι
  set g : Matrix.SpecialLinearGroup ι F := transvection hij 1
  refine ⟨⟨(QuotientGroup.mk g : Matrix.ProjectiveSpecialLinearGroup ι F),
    1, fun h => one_ne_zero (α := F) ?_⟩⟩
  rwa [QuotientGroup.eq_one_iff, transvection_mem_center_iff] at h

end SL2Simple

/--
theorem `Matrix.ProjectiveSpecialLinearGroup.rank_two_simple'` / 定理 `Matrix.ProjectiveSpecialLinearGroup.rank_two_simple'`

English:
theorem Matrix.ProjectiveSpecialLinearGroup.rank_two_simple'
  proof: MulAction.IwasawaStructure.isSimpleGroup
    (SL2Simple.PSL_commutator_eq_top hF) PSL2.Iwasawa inferInstance

中文:
定理 Matrix.ProjectiveSpecialLinearGroup.rank_two_simple'
  证明: MulAction.IwasawaStructure.isSimpleGroup
    (SL2Simple.PSL_commutator_eq_top hF) PSL2.Iwasawa inferInstance

Depends on / 依赖: Iwasawa, IwasawaStructure, MulAction, MulAction.IwasawaStructure.isSimpleGroup, PSL2.Iwasawa, PSL_commutator_eq_top, SL2Simple, SL2Simple.PSL_commutator_eq_top, isSimpleGroup
-/
theorem Matrix.ProjectiveSpecialLinearGroup.rank_two_simple'
    (hF : exists a : F, a != 0 ∧ a ^ 2 != 1) :
    IsSimpleGroup PSL(2, F) :=
  MulAction.IwasawaStructure.isSimpleGroup
    (SL2Simple.PSL_commutator_eq_top hF) PSL2.Iwasawa inferInstance

/--
lemma `field_cond_of_four_le_card` / 引理 `field_cond_of_four_le_card`

English:
lemma field_cond_of_four_le_card
  given: (hF : 4 <= Nat.card F)
  proof: by
  have : Finite F := (Nat.card_pos_iff.1 (by omega)).2
  obtain ⟨x, hx⟩ : IsCyclic Fˣ := by infer_instance
  refine ⟨x, Units.ne_zero x, fun h => ?_⟩
  grw [Nat.card_eq_card_units_add_one F, ← orderOf_eq_card_of_forall_mem_zpowers hx,
    orderOf_le_of_pow_eq_one zero_lt_two (Units.ext <| by simp

中文:
引理 field_cond_of_four_le_card
  条件: (hF : 4 <= 自然数.card F)
  证明: by
  have : Finite F := (Nat.card_pos_iff.1 (by omega)).2
  obtain ⟨x, hx⟩ : IsCyclic Fˣ := by infer_instance
  refine ⟨x, Units.ne_zero x, fun h => ?_⟩
  grw [Nat.card_eq_card_units_add_one F, ← orderOf_eq_card_of_forall_mem_zpowers hx,
    orderOf_le_of_pow_eq_one zero_lt_two (Units.ext <| by simp
-/
private lemma field_cond_of_four_le_card (hF : 4 <= Nat.card F) :
    exists a : F, a != 0 ∧ a ^ 2 != 1 := by
  have : Finite F := (Nat.card_pos_iff.1 (by omega)).2
  obtain ⟨x, hx⟩ : IsCyclic Fˣ := by infer_instance
  refine ⟨x, Units.ne_zero x, fun h => ?_⟩
  grw [Nat.card_eq_card_units_add_one F, ← orderOf_eq_card_of_forall_mem_zpowers hx,
    orderOf_le_of_pow_eq_one zero_lt_two (Units.ext <| by simpa using h)] at hF
  omega

/--
theorem `Matrix.ProjectiveSpecialLinearGroup.rank_two_simple` / 定理 `Matrix.ProjectiveSpecialLinearGroup.rank_two_simple`

English:
theorem Matrix.ProjectiveSpecialLinearGroup.rank_two_simple
  given: (hF : 4 <= Nat.card F)
  proof: Matrix.ProjectiveSpecialLinearGroup.rank_two_simple' (field_cond_of_four_le_card hF)

中文:
定理 Matrix.ProjectiveSpecialLinearGroup.rank_two_simple
  条件: (hF : 4 <= 自然数.card F)
  证明: Matrix.ProjectiveSpecialLinearGroup.rank_two_simple' (field_cond_of_four_le_card hF)

Depends on / 依赖: Matrix, Matrix.ProjectiveSpecialLinearGroup.rank_two_simple, ProjectiveSpecialLinearGroup, field_cond_of_four_le_card, rank_two_simple
-/
theorem Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (hF : 4 <= Nat.card F) :
    IsSimpleGroup PSL(2, F) :=
  Matrix.ProjectiveSpecialLinearGroup.rank_two_simple' (field_cond_of_four_le_card hF)
