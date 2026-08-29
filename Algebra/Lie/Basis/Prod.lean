/-
Copyright (c) 2026 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Lie.Basis.Basic
public import Mathlib.Algebra.Lie.Prod
public import Mathlib.Algebra.Lie.Semisimple.Basic

/-!
# Products of bases Lie algebras

Given two finite-dimensional simple Lie algebras, if they admit bases with matching Cartan matrices,
they must be isomorphic. This file provides a proof of this as `LieAlgebra.Basis.equivOfReindex`.

-/

noncomputable section

namespace LieAlgebra.Basis

open Function LieSubalgebra Set Submodule

variable {ι₁ ι₂ L₁ L₂ : Type*} [Finite ι₁] [Finite ι₂] (eι : ι₁ ≃ ι₂) [LieRing L₁] [LieRing L₂]

section CommRing

variable {R : Type*} [CommRing R]
  [LieAlgebra R L₁] {H₁ : LieSubalgebra R L₁} (b₁ : Basis ι₁ H₁)
  [LieAlgebra R L₂] {H₂ : LieSubalgebra R L₂} (b₂ : Basis ι₂ H₂)

/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: :
  body: .lieSpan _ _
    {(b₁.h i, b₂.h (eι i)) | i : ι₁} union
    {(b₁.e i, b₂.e (eι i)) | i : ι₁} union
    {(b₁.f i, b₂.f (eι i)) | i : ι₁}

中文:
定义 乘积
  签名: :
  定义体: .lieSpan _ _
    {(b₁.h i, b₂.h (eι i)) | i : ι₁} union
    {(b₁.e i, b₂.e (eι i)) | i : ι₁} union
    {(b₁.f i, b₂.f (eι i)) | i : ι₁}
-/
protected def prod :
    LieSubalgebra R (L₁ × L₂) :=
.lieSpan _ _
    {(b₁.h i, b₂.h (eι i)) | i : ι₁} union
    {(b₁.e i, b₂.e (eι i)) | i : ι₁} union
    {(b₁.f i, b₂.f (eι i)) | i : ι₁}

/--
Definition of `prodSymmEquiv` / `prodSymmEquiv` 的定义

English:
definition prodSymmEquiv
  signature: : prod eι.symm b₂ b₁ ≃ₗ⁅R⁆ b₁.prod eι b₂
  body: have : (prod eι.symm b₂ b₁).map (LieEquiv.prodComm R L₂ L₁) = b₁.prod eι b₂ := by
    rw [prod]; rw [prod]; rw [map_lieSpan]; congr; ext; aesop
  (LieEquiv.lieSubalgebraMap (prod eι.symm b₂ b₁) (LieEquiv.prodComm _ _ _)).trans
    (LieEquiv.ofEq _ _ <| by simpa)

@[simp]

中文:
定义 prodSymmEquiv
  签名: : 乘积 eι.symm b₂ b₁ ≃ₗ⁅R⁆ b₁.乘积 eι b₂
  定义体: have : (prod eι.symm b₂ b₁).map (LieEquiv.prodComm R L₂ L₁) = b₁.prod eι b₂ := by
    rw [prod]; rw [prod]; rw [map_lieSpan]; congr; ext; aesop
  (LieEquiv.lieSubalgebraMap (prod eι.symm b₂ b₁) (LieEquiv.prodComm _ _ _)).trans
    (LieEquiv.ofEq _ _ <| by simpa)

@[simp]

Depends on / 依赖: LieEquiv, LieEquiv.lieSubalgebraMap, LieEquiv.ofEq, LieEquiv.prodComm, lieSubalgebraMap, map_lieSpan, prodComm
-/
def prodSymmEquiv : prod eι.symm b₂ b₁ ≃ₗ⁅R⁆ b₁.prod eι b₂ :=
  have : (prod eι.symm b₂ b₁).map (LieEquiv.prodComm R L₂ L₁) = b₁.prod eι b₂ := by
    rw [prod]; rw [prod]; rw [map_lieSpan]; congr; ext; aesop
  (LieEquiv.lieSubalgebraMap (prod eι.symm b₂ b₁) (LieEquiv.prodComm _ _ _)).trans
    (LieEquiv.ofEq _ _ <| by simpa)

@[simp]
/--
lemma `prodSymmEquiv_symm_apply` / 引理 `prodSymmEquiv_symm_apply`

English:
lemma prodSymmEquiv_symm_apply
  given: {y : b₁.prod eι b₂}
  proof: rfl

中文:
引理 prodSymmEquiv_symm_apply
  条件: {y : b₁.乘积 eι b₂}
  证明: rfl
-/
lemma prodSymmEquiv_symm_apply {y : b₁.prod eι b₂} :
    (prodSymmEquiv eι b₁ b₂).symm y =
      ⟨((y : L₁ × L₂).snd, (y : L₁ × L₂).fst), ((prodSymmEquiv eι b₁ b₂).symm y).property⟩ :=
  rfl

/--
lemma `h_mem_prod` / 引理 `h_mem_prod`

English:
lemma h_mem_prod
  given: (i : ι₁)
  proof: subset_lieSpan by aesop

中文:
引理 h_mem_prod
  条件: (i : ι₁)
  证明: subset_lieSpan by aesop

Depends on / 依赖: subset_lieSpan
-/
lemma h_mem_prod (i : ι₁) :
    (b₁.h i, b₂.h (eι i)) in b₁.prod eι b₂ :=
subset_lieSpan by aesop

/--
Definition of `prodCartan` / `prodCartan` 的定义

English:
definition prodCartan
  signature: :
  body: .lieSpan _ _ {⟨(b₁.h i, b₂.h (eι i)), h_mem_prod eι b₁ b₂ i⟩ | i : ι₁}

中文:
定义 prodCartan
  签名: :
  定义体: .lieSpan _ _ {⟨(b₁.h i, b₂.h (eι i)), h_mem_prod eι b₁ b₂ i⟩ | i : ι₁}

Depends on / 依赖: h_mem_prod, lieSpan
-/
def prodCartan :
    LieSubalgebra R (prod eι b₁ b₂) :=
  .lieSpan _ _ {⟨(b₁.h i, b₂.h (eι i)), h_mem_prod eι b₁ b₂ i⟩ | i : ι₁}

open Finsupp in
/--
lemma `prodCartanEquiv_aux` / 引理 `prodCartanEquiv_aux`

English:
lemma prodCartanEquiv_aux
  proof: by
  suffices forall y, (exists l : ι₁ ->₀ R,
      (l.linearCombination R fun i => (b₁.h i, b₂.h (eι i))) = (0, y)) -> y = 0 by
    have aux : {(b₁.h i, b₂.h (eι i)) | i : ι₁} = (fun i : ι₁ => (b₁.h i, b₂.h (eι i))) '' univ := by
      ext; simp
    simp_rw [← LinearMap.disjoint_ker_iff_injOn, LinearMap.disjoint_ker, aux,
      mem_span_image_iff_linearCombination]
    aesop
  intro y ⟨f, hf⟩
  suffices linearCombination R b₁.h f = 0 by
    rw [LinearMap.map_eq_zero_iff _ b₁.linInd] at this
    aesop (add simp Prod.ext_iff)
  replace hf := (LinearMap.fst R L₁ L₂).congr_arg hf
  rw [← LinearMap.comp_apply]; rw [← Finsupp.linearCombination_linear_comp] at hf
  aesop

中文:
引理 prodCartanEquiv_aux
  证明: by
  suffices forall y, (exists l : ι₁ ->₀ R,
      (l.linearCombination R fun i => (b₁.h i, b₂.h (eι i))) = (0, y)) -> y = 0 by
    have aux : {(b₁.h i, b₂.h (eι i)) | i : ι₁} = (fun i : ι₁ => (b₁.h i, b₂.h (eι i))) '' univ := by
      ext; simp
    simp_rw [← LinearMap.disjoint_ker_iff_injOn, LinearMap.disjoint_ker, aux,
      mem_span_image_iff_linearCombination]
    aesop
  intro y ⟨f, hf⟩
  suffices linearCombination R b₁.h f = 0 by
    rw [LinearMap.map_eq_zero_iff _ b₁.linInd] at this
    aesop (add simp Prod.ext_iff)
  replace hf := (LinearMap.fst R L₁ L₂).congr_arg hf
  rw [← LinearMap.comp_apply]; rw [← Finsupp.linearCombination_linear_comp] at hf
  aesop

Depends on / 依赖: LinearMap, LinearMap.disjoint_ker, LinearMap.disjoint_ker_iff_injOn, LinearMap.map_eq_zero_iff, Prod.ext_iff, disjoint_ker, disjoint_ker_iff_injOn, ext_iff, l.linearCombination, linInd, linearCombination, map_eq_zero_iff, mem_span_image_iff_linearCombination, replace, simp_rw
-/
lemma prodCartanEquiv_aux :
    InjOn (LinearMap.fst R L₁ L₂) (span R {(b₁.h i, b₂.h (eι i)) | i : ι₁}) := by
  suffices forall y, (exists l : ι₁ ->₀ R,
      (l.linearCombination R fun i => (b₁.h i, b₂.h (eι i))) = (0, y)) -> y = 0 by
    have aux : {(b₁.h i, b₂.h (eι i)) | i : ι₁} = (fun i : ι₁ => (b₁.h i, b₂.h (eι i))) '' univ := by
      ext; simp
    simp_rw [← LinearMap.disjoint_ker_iff_injOn, LinearMap.disjoint_ker, aux,
      mem_span_image_iff_linearCombination]
    aesop
  intro y ⟨f, hf⟩
  suffices linearCombination R b₁.h f = 0 by
    rw [LinearMap.map_eq_zero_iff _ b₁.linInd] at this
    aesop (add simp Prod.ext_iff)
  replace hf := (LinearMap.fst R L₁ L₂).congr_arg hf
  rw [← LinearMap.comp_apply]; rw [← Finsupp.linearCombination_linear_comp] at hf
  aesop

open LinearMap in
/--
Definition of `prodCartanEquiv` / `prodCartanEquiv` 的定义

English:
definition prodCartanEquiv
  signature: :
  body: /- Informally this is obvious since `prodCartan eι b₁ b₂` is the linear span of
  `{(b₁.h i, b₂.h (eι i)) | i : ι₁}` and `H₁` is the linear span of `{b₁.h i | i : ι₁}` (and both
  families are linearly independent) but formally some care is required. -/
  have h₁ : (prodCartan eι b₁ b₂).map (prod eι b₁ b₂).incl =
      (lieSpan R (L₁ × L₂) {(b₁.h i, b₂.h (eι i)) | i : ι₁} : Set (L₁ × L₂)) := by
    rw [prodCartan]; rw [map_lieSpan]; congr; aesop
  have h₂ : (lieSpan R _ {(b₁.h i, b₂.h (eι i)) | i : ι₁}) =
      span R {(b₁.h i, b₂.h (eι i)) | i : ι₁} :=
coe_lieSpan_eq_span_of_forall_lie_eq_zero by simp [b₁.lie_h_h, b₂.lie_h_h]
  have h₃ : (span R {(b₁.h i, b₂.h (eι i)) | i : ι₁}).map (.fst R L₁ L₂) = span R (range b₁.h) := by
    rw [Submodule.map_span]; congr; ext; simp
  have h₄ : lieSpan R L₁ (range b₁.h) = span R (range b₁.h) := by
    rw [← b₁.coe_cartan_eq_span]; rw [toSubmodule_inj]; rw [← b₁.cartan_eq_lieSpan]
  have h₅ : (H₁ : Set L₁) = lieSpan R L₁ (range b₁.h) := by simp [b₁.cartan_eq_lieSpan]
  let e₀ : prodCartan eι b₁ b₂ ≃ₗ[R] (prodCartan eι b₁ b₂).map (prod eι b₁ b₂).incl :=
(prodCartan eι b₁ b₂).equivMapOfInjective (prod eι b₁ b₂).incl by simp
  let e₁ : (prodCartan eι b₁ b₂).map (prod eι b₁ b₂).incl ≃ₗ[R]
      lieSpan R (L₁ × L₂) {(b₁.h i, b₂.h (eι i)) | i : ι₁} := LieEquiv.ofEq _ _ h₁
  let e₂ : lieSpan R (L₁ × L₂) {(b₁.h i, b₂.h (eι i)) | i : ι₁} ≃ₗ[R]
      span R {(b₁.h i, b₂.h (eι i)) | i : ι₁} := LinearEquiv.ofEq _ _ h₂
  let e₃ : span R {(b₁.h i, b₂.h (eι i)) | i : ι₁} ≃ₗ[R] span R (range b₁.h) :=
    (LinearEquiv.ofBijective _ ⟨submoduleMap_injective_of_injOn (prodCartanEquiv_aux eι b₁ b₂),
      submoduleMap_surjective _ _⟩).trans <| .ofEq _ _ h₃
  let e₄ : span R (range b₁.h) ≃ₗ[R] lieSpan R L₁ (range b₁.h) := LinearEquiv.ofEq _ _ h₄.symm
  let e₅ : lieSpan R L₁ (range b₁.h) ≃ₗ[R] H₁ := (LieEquiv.ofEq _ _ h₅).symm
e₀.trans e₁.trans e₂.trans e₃.trans e₄.trans e₅

中文:
定义 prodCartanEquiv
  签名: :
  定义体: /- Informally this is obvious since `prodCartan eι b₁ b₂` is the linear span of
  `{(b₁.h i, b₂.h (eι i)) | i : ι₁}` and `H₁` is the linear span of `{b₁.h i | i : ι₁}` (and both
  families are linearly independent) but formally some care is required. -/
  have h₁ : (prodCartan eι b₁ b₂).map (prod eι b₁ b₂).incl =
      (lieSpan R (L₁ × L₂) {(b₁.h i, b₂.h (eι i)) | i : ι₁} : Set (L₁ × L₂)) := by
    rw [prodCartan]; rw [map_lieSpan]; congr; aesop
  have h₂ : (lieSpan R _ {(b₁.h i, b₂.h (eι i)) | i : ι₁}) =
      span R {(b₁.h i, b₂.h (eι i)) | i : ι₁} :=
coe_lieSpan_eq_span_of_forall_lie_eq_zero by simp [b₁.lie_h_h, b₂.lie_h_h]
  have h₃ : (span R {(b₁.h i, b₂.h (eι i)) | i : ι₁}).map (.fst R L₁ L₂) = span R (range b₁.h) := by
    rw [Submodule.map_span]; congr; ext; simp
  have h₄ : lieSpan R L₁ (range b₁.h) = span R (range b₁.h) := by
    rw [← b₁.coe_cartan_eq_span]; rw [toSubmodule_inj]; rw [← b₁.cartan_eq_lieSpan]
  have h₅ : (H₁ : Set L₁) = lieSpan R L₁ (range b₁.h) := by simp [b₁.cartan_eq_lieSpan]
  let e₀ : prodCartan eι b₁ b₂ ≃ₗ[R] (prodCartan eι b₁ b₂).map (prod eι b₁ b₂).incl :=
(prodCartan eι b₁ b₂).equivMapOfInjective (prod eι b₁ b₂).incl by simp
  let e₁ : (prodCartan eι b₁ b₂).map (prod eι b₁ b₂).incl ≃ₗ[R]
      lieSpan R (L₁ × L₂) {(b₁.h i, b₂.h (eι i)) | i : ι₁} := LieEquiv.ofEq _ _ h₁
  let e₂ : lieSpan R (L₁ × L₂) {(b₁.h i, b₂.h (eι i)) | i : ι₁} ≃ₗ[R]
      span R {(b₁.h i, b₂.h (eι i)) | i : ι₁} := LinearEquiv.ofEq _ _ h₂
  let e₃ : span R {(b₁.h i, b₂.h (eι i)) | i : ι₁} ≃ₗ[R] span R (range b₁.h) :=
    (LinearEquiv.ofBijective _ ⟨submoduleMap_injective_of_injOn (prodCartanEquiv_aux eι b₁ b₂),
      submoduleMap_surjective _ _⟩).trans <| .ofEq _ _ h₃
  let e₄ : span R (range b₁.h) ≃ₗ[R] lieSpan R L₁ (range b₁.h) := LinearEquiv.ofEq _ _ h₄.symm
  let e₅ : lieSpan R L₁ (range b₁.h) ≃ₗ[R] H₁ := (LieEquiv.ofEq _ _ h₅).symm
e₀.trans e₁.trans e₂.trans e₃.trans e₄.trans e₅
-/
def prodCartanEquiv :
    prodCartan eι b₁ b₂ ≃ₗ[R] H₁ :=
  /- Informally this is obvious since `prodCartan eι b₁ b₂` is the linear span of
  `{(b₁.h i, b₂.h (eι i)) | i : ι₁}` and `H₁` is the linear span of `{b₁.h i | i : ι₁}` (and both
  families are linearly independent) but formally some care is required. -/
  have h₁ : (prodCartan eι b₁ b₂).map (prod eι b₁ b₂).incl =
      (lieSpan R (L₁ × L₂) {(b₁.h i, b₂.h (eι i)) | i : ι₁} : Set (L₁ × L₂)) := by
    rw [prodCartan]; rw [map_lieSpan]; congr; aesop
  have h₂ : (lieSpan R _ {(b₁.h i, b₂.h (eι i)) | i : ι₁}) =
      span R {(b₁.h i, b₂.h (eι i)) | i : ι₁} :=
coe_lieSpan_eq_span_of_forall_lie_eq_zero by simp [b₁.lie_h_h, b₂.lie_h_h]
  have h₃ : (span R {(b₁.h i, b₂.h (eι i)) | i : ι₁}).map (.fst R L₁ L₂) = span R (range b₁.h) := by
    rw [Submodule.map_span]; congr; ext; simp
  have h₄ : lieSpan R L₁ (range b₁.h) = span R (range b₁.h) := by
    rw [← b₁.coe_cartan_eq_span]; rw [toSubmodule_inj]; rw [← b₁.cartan_eq_lieSpan]
  have h₅ : (H₁ : Set L₁) = lieSpan R L₁ (range b₁.h) := by simp [b₁.cartan_eq_lieSpan]
  let e₀ : prodCartan eι b₁ b₂ ≃ₗ[R] (prodCartan eι b₁ b₂).map (prod eι b₁ b₂).incl :=
(prodCartan eι b₁ b₂).equivMapOfInjective (prod eι b₁ b₂).incl by simp
  let e₁ : (prodCartan eι b₁ b₂).map (prod eι b₁ b₂).incl ≃ₗ[R]
      lieSpan R (L₁ × L₂) {(b₁.h i, b₂.h (eι i)) | i : ι₁} := LieEquiv.ofEq _ _ h₁
  let e₂ : lieSpan R (L₁ × L₂) {(b₁.h i, b₂.h (eι i)) | i : ι₁} ≃ₗ[R]
      span R {(b₁.h i, b₂.h (eι i)) | i : ι₁} := LinearEquiv.ofEq _ _ h₂
  let e₃ : span R {(b₁.h i, b₂.h (eι i)) | i : ι₁} ≃ₗ[R] span R (range b₁.h) :=
    (LinearEquiv.ofBijective _ ⟨submoduleMap_injective_of_injOn (prodCartanEquiv_aux eι b₁ b₂),
      submoduleMap_surjective _ _⟩).trans <| .ofEq _ _ h₃
  let e₄ : span R (range b₁.h) ≃ₗ[R] lieSpan R L₁ (range b₁.h) := LinearEquiv.ofEq _ _ h₄.symm
  let e₅ : lieSpan R L₁ (range b₁.h) ≃ₗ[R] H₁ := (LieEquiv.ofEq _ _ h₅).symm
e₀.trans e₁.trans e₂.trans e₃.trans e₄.trans e₅

/--
Definition of `prodH` / `prodH` 的定义

English:
abbreviation prodH
  signature: (i : ι₁)
  body: ⟨(b₁.h i, b₂.h (eι i)), subset_lieSpan by aesop⟩

中文:
缩写 prodH
  签名: (i : ι₁)
  定义体: ⟨(b₁.h i, b₂.h (eι i)), subset_lieSpan by aesop⟩
-/
protected abbrev prodH (i : ι₁) : b₁.prod eι b₂ :=
⟨(b₁.h i, b₂.h (eι i)), subset_lieSpan by aesop⟩

/--
Definition of `prodE` / `prodE` 的定义

English:
abbreviation prodE
  signature: (i : ι₁)
  body: ⟨(b₁.e i, b₂.e (eι i)), subset_lieSpan by aesop⟩

中文:
缩写 prodE
  签名: (i : ι₁)
  定义体: ⟨(b₁.e i, b₂.e (eι i)), subset_lieSpan by aesop⟩
-/
protected abbrev prodE (i : ι₁) : b₁.prod eι b₂ :=
⟨(b₁.e i, b₂.e (eι i)), subset_lieSpan by aesop⟩

/--
Definition of `prodF` / `prodF` 的定义

English:
abbreviation prodF
  signature: (i : ι₁)
  body: ⟨(b₁.f i, b₂.f (eι i)), subset_lieSpan by aesop⟩

中文:
缩写 prodF
  签名: (i : ι₁)
  定义体: ⟨(b₁.f i, b₂.f (eι i)), subset_lieSpan by aesop⟩
-/
protected abbrev prodF (i : ι₁) : b₁.prod eι b₂ :=
⟨(b₁.f i, b₂.f (eι i)), subset_lieSpan by aesop⟩

/--
lemma `basisProd_aux` / 引理 `basisProd_aux`

English:
lemma basisProd_aux
  proof: by
  suffices lieSpan R (prod eι b₁ b₂) (range (prodE eι b₁ b₂) union range (prodF eι b₁ b₂)) =
      lieSpan R (prod eι b₁ b₂)
        (range (prodH eι b₁ b₂) union range (prodE eι b₁ b₂) union range (prodF eι b₁ b₂)) by
    have hr : range (prodH eι b₁ b₂) union range (prodE eι b₁ b₂) union range (prodF eι b₁ b₂) =
        Subtype.val ⁻¹' ( {(b₁.h i, b₂.h (eι i)) | i : ι₁} union
                          {(b₁.e i, b₂.e (eι i)) | i : ι₁} union
                          {(b₁.f i, b₂.f (eι i)) | i : ι₁} ) := by
      ext; simp [Subtype.ext_iff]
    rw [this]; rw [hr]
    exact lieSpan_lieSpan_coe_preimage
  simp only [union_assoc]
  refine le_antisymm (lieSpan_mono <| by simp) (lieSpan_le.mpr <| union_subset ?_ subset_lieSpan)
  rintro - ⟨i, rfl⟩
  have hef : prodH eι b₁ b₂ i = ⁅prodE eι b₁ b₂ i, prodF eι b₁ b₂ i⁆ := by
    simp [Subtype.ext_iff, (b₁.sl2 i).lie_e_f, (b₂.sl2 (eι i)).lie_e_f]
  rw [hef]
  apply lie_mem
· exact subset_lieSpan mem_union_left _ mem_range_self i
· exact subset_lieSpan mem_union_right _ mem_range_self i

中文:
引理 basisProd_aux
  证明: by
  suffices lieSpan R (prod eι b₁ b₂) (range (prodE eι b₁ b₂) union range (prodF eι b₁ b₂)) =
      lieSpan R (prod eι b₁ b₂)
        (range (prodH eι b₁ b₂) union range (prodE eι b₁ b₂) union range (prodF eι b₁ b₂)) by
    have hr : range (prodH eι b₁ b₂) union range (prodE eι b₁ b₂) union range (prodF eι b₁ b₂) =
        Subtype.val ⁻¹' ( {(b₁.h i, b₂.h (eι i)) | i : ι₁} union
                          {(b₁.e i, b₂.e (eι i)) | i : ι₁} union
                          {(b₁.f i, b₂.f (eι i)) | i : ι₁} ) := by
      ext; simp [Subtype.ext_iff]
    rw [this]; rw [hr]
    exact lieSpan_lieSpan_coe_preimage
  simp only [union_assoc]
  refine le_antisymm (lieSpan_mono <| by simp) (lieSpan_le.mpr <| union_subset ?_ subset_lieSpan)
  rintro - ⟨i, rfl⟩
  have hef : prodH eι b₁ b₂ i = ⁅prodE eι b₁ b₂ i, prodF eι b₁ b₂ i⁆ := by
    simp [Subtype.ext_iff, (b₁.sl2 i).lie_e_f, (b₂.sl2 (eι i)).lie_e_f]
  rw [hef]
  apply lie_mem
· exact subset_lieSpan mem_union_left _ mem_range_self i
· exact subset_lieSpan mem_union_right _ mem_range_self i

Depends on / 依赖: Subtype, Subtype.ext_iff, Subtype.val, ext_iff, lieSpan, lieSpan_lie
-/
lemma basisProd_aux :
    lieSpan R (prod eι b₁ b₂) (range (prodE eι b₁ b₂) union range (prodF eι b₁ b₂)) = ⊤ := by
  suffices lieSpan R (prod eι b₁ b₂) (range (prodE eι b₁ b₂) union range (prodF eι b₁ b₂)) =
      lieSpan R (prod eι b₁ b₂)
        (range (prodH eι b₁ b₂) union range (prodE eι b₁ b₂) union range (prodF eι b₁ b₂)) by
    have hr : range (prodH eι b₁ b₂) union range (prodE eι b₁ b₂) union range (prodF eι b₁ b₂) =
        Subtype.val ⁻¹' ( {(b₁.h i, b₂.h (eι i)) | i : ι₁} union
                          {(b₁.e i, b₂.e (eι i)) | i : ι₁} union
                          {(b₁.f i, b₂.f (eι i)) | i : ι₁} ) := by
      ext; simp [Subtype.ext_iff]
    rw [this]; rw [hr]
    exact lieSpan_lieSpan_coe_preimage
  simp only [union_assoc]
  refine le_antisymm (lieSpan_mono <| by simp) (lieSpan_le.mpr <| union_subset ?_ subset_lieSpan)
  rintro - ⟨i, rfl⟩
  have hef : prodH eι b₁ b₂ i = ⁅prodE eι b₁ b₂ i, prodF eι b₁ b₂ i⁆ := by
    simp [Subtype.ext_iff, (b₁.sl2 i).lie_e_f, (b₂.sl2 (eι i)).lie_e_f]
  rw [hef]
  apply lie_mem
· exact subset_lieSpan mem_union_left _ mem_range_self i
· exact subset_lieSpan mem_union_right _ mem_range_self i

/--
Definition of `basisProd` / `basisProd` 的定义

English:
definition basisProd
  signature: (hA : b₁.A.reindex eι eι = b₂.A)
  body: b₁.A
  h := prodH eι b₁ b₂
  e := prodE eι b₁ b₂
  f := prodF eι b₁ b₂
  cartan_eq_lieSpan := rfl
  span_ef := b₁.basisProd_aux eι b₂
linInd := .of_comp (prod eι b₁ b₂).subtype .of_comp (LinearMap.fst R L₁ L₂) b₁.linInd
  nondegen := b₁.nondegen
  sl2 i :=
    { h_ne_zero := by simp [Subtype.ext_iff, (b₁.sl2 i).h_ne_zero]
      lie_e_f := by simp [Subtype.ext_iff, (b₁.sl2 i).lie_e_f, (b₂.sl2 (eι i)).lie_e_f]
      lie_h_e_nsmul := by
        simp [Subtype.ext_iff, (b₁.sl2 i).lie_h_e_nsmul, (b₂.sl2 (eι i)).lie_h_e_nsmul]
      lie_h_f_nsmul := by
        simp [Subtype.ext_iff, (b₁.sl2 i).lie_h_f_nsmul, (b₂.sl2 (eι i)).lie_h_f_nsmul] }
  lie_h_h i j := by simp [Subtype.ext_iff, b₁.lie_h_h, b₂.lie_h_h]
  lie_h_e i j := by simp [Subtype.ext_iff, b₁.lie_h_e, b₂.lie_h_e, ← hA]
  lie_h_f i j := by simp [Subtype.ext_iff, b₁.lie_h_f, b₂.lie_h_f, ← hA]
  lie_e_f_ne i j hij := by
    have hij' : eι i != eι j := by aesop
    simp [Subtype.ext_iff, b₁.lie_e_f_ne i j hij, b₂.lie_e_f_ne _ _ hij']

中文:
定义 basisProd
  签名: (hA : b₁.A.reindex eι eι = b₂.A)
  定义体: b₁.A
  h := prodH eι b₁ b₂
  e := prodE eι b₁ b₂
  f := prodF eι b₁ b₂
  cartan_eq_lieSpan := rfl
  span_ef := b₁.basisProd_aux eι b₂
linInd := .of_comp (prod eι b₁ b₂).subtype .of_comp (LinearMap.fst R L₁ L₂) b₁.linInd
  nondegen := b₁.nondegen
  sl2 i :=
    { h_ne_zero := by simp [Subtype.ext_iff, (b₁.sl2 i).h_ne_zero]
      lie_e_f := by simp [Subtype.ext_iff, (b₁.sl2 i).lie_e_f, (b₂.sl2 (eι i)).lie_e_f]
      lie_h_e_nsmul := by
        simp [Subtype.ext_iff, (b₁.sl2 i).lie_h_e_nsmul, (b₂.sl2 (eι i)).lie_h_e_nsmul]
      lie_h_f_nsmul := by
        simp [Subtype.ext_iff, (b₁.sl2 i).lie_h_f_nsmul, (b₂.sl2 (eι i)).lie_h_f_nsmul] }
  lie_h_h i j := by simp [Subtype.ext_iff, b₁.lie_h_h, b₂.lie_h_h]
  lie_h_e i j := by simp [Subtype.ext_iff, b₁.lie_h_e, b₂.lie_h_e, ← hA]
  lie_h_f i j := by simp [Subtype.ext_iff, b₁.lie_h_f, b₂.lie_h_f, ← hA]
  lie_e_f_ne i j hij := by
    have hij' : eι i != eι j := by aesop
    simp [Subtype.ext_iff, b₁.lie_e_f_ne i j hij, b₂.lie_e_f_ne _ _ hij']
-/
def basisProd (hA : b₁.A.reindex eι eι = b₂.A) :
    Basis ι₁ (prodCartan eι b₁ b₂) where
  A := b₁.A
  h := prodH eι b₁ b₂
  e := prodE eι b₁ b₂
  f := prodF eι b₁ b₂
  cartan_eq_lieSpan := rfl
  span_ef := b₁.basisProd_aux eι b₂
linInd := .of_comp (prod eι b₁ b₂).subtype .of_comp (LinearMap.fst R L₁ L₂) b₁.linInd
  nondegen := b₁.nondegen
  sl2 i :=
    { h_ne_zero := by simp [Subtype.ext_iff, (b₁.sl2 i).h_ne_zero]
      lie_e_f := by simp [Subtype.ext_iff, (b₁.sl2 i).lie_e_f, (b₂.sl2 (eι i)).lie_e_f]
      lie_h_e_nsmul := by
        simp [Subtype.ext_iff, (b₁.sl2 i).lie_h_e_nsmul, (b₂.sl2 (eι i)).lie_h_e_nsmul]
      lie_h_f_nsmul := by
        simp [Subtype.ext_iff, (b₁.sl2 i).lie_h_f_nsmul, (b₂.sl2 (eι i)).lie_h_f_nsmul] }
  lie_h_h i j := by simp [Subtype.ext_iff, b₁.lie_h_h, b₂.lie_h_h]
  lie_h_e i j := by simp [Subtype.ext_iff, b₁.lie_h_e, b₂.lie_h_e, ← hA]
  lie_h_f i j := by simp [Subtype.ext_iff, b₁.lie_h_f, b₂.lie_h_f, ← hA]
  lie_e_f_ne i j hij := by
    have hij' : eι i != eι j := by aesop
    simp [Subtype.ext_iff, b₁.lie_e_f_ne i j hij, b₂.lie_e_f_ne _ _ hij']

/--
lemma `surjective_fst_prod` / 引理 `surjective_fst_prod`

English:
lemma surjective_fst_prod
  proof: by
  set L : LieSubalgebra R (L₁ × L₂) := b₁.prod eι b₂
  set p₁ : L ->ₗ⁅R⁆ L₁ := (LieHom.fst R L₁ L₂).comp L.incl
  have h₁ : range b₁.e = range (p₁ ∘ prodE eι b₁ b₂) := rfl
  have h₂ : range b₁.f = range (p₁ ∘ prodF eι b₁ b₂) := rfl
  rw [← LieHom.range_eq_top]; rw [eq_top_iff]; rw [← b₁.span_ef]; rw [map_top]; rw [← b₁.basisProd_aux eι b₂]; rw [map_lieSpan]; rw [image_union]; rw [h₁]; rw [h₂]
  simp [range_comp]

中文:
引理 surjective_fst_prod
  证明: by
  set L : LieSubalgebra R (L₁ × L₂) := b₁.prod eι b₂
  set p₁ : L ->ₗ⁅R⁆ L₁ := (LieHom.fst R L₁ L₂).comp L.incl
  have h₁ : range b₁.e = range (p₁ ∘ prodE eι b₁ b₂) := rfl
  have h₂ : range b₁.f = range (p₁ ∘ prodF eι b₁ b₂) := rfl
  rw [← LieHom.range_eq_top]; rw [eq_top_iff]; rw [← b₁.span_ef]; rw [map_top]; rw [← b₁.basisProd_aux eι b₂]; rw [map_lieSpan]; rw [image_union]; rw [h₁]; rw [h₂]
  simp [range_comp]

Depends on / 依赖: L.incl, LieHom, LieHom.fst, LieHom.range_eq_top, LieSubalgebra, basisProd_aux, eq_top_iff, image_union, map_lieSpan, map_top, range_comp, range_eq_top, span_ef
-/
lemma surjective_fst_prod :
    Surjective ((LieHom.fst R L₁ L₂).comp (prod eι b₁ b₂).incl) := by
  set L : LieSubalgebra R (L₁ × L₂) := b₁.prod eι b₂
  set p₁ : L ->ₗ⁅R⁆ L₁ := (LieHom.fst R L₁ L₂).comp L.incl
  have h₁ : range b₁.e = range (p₁ ∘ prodE eι b₁ b₂) := rfl
  have h₂ : range b₁.f = range (p₁ ∘ prodF eι b₁ b₂) := rfl
  rw [← LieHom.range_eq_top]; rw [eq_top_iff]; rw [← b₁.span_ef]; rw [map_top]; rw [← b₁.basisProd_aux eι b₂]; rw [map_lieSpan]; rw [image_union]; rw [h₁]; rw [h₂]
  simp [range_comp]

/--
lemma `surjective_snd_prod` / 引理 `surjective_snd_prod`

English:
lemma surjective_snd_prod
  proof: by
  set L : LieSubalgebra R (L₁ × L₂) := b₁.prod eι b₂
  set p₂ : L ->ₗ⁅R⁆ L₂ := (LieHom.snd R L₁ L₂).comp L.incl
  have h₁ : range b₂.e = range (p₂ ∘ prodE eι b₁ b₂) := by
    simp [show p₂ ∘ prodE eι b₁ b₂ = b₂.e ∘ eι from rfl]
  have h₂ : range b₂.f = range (p₂ ∘ prodF eι b₁ b₂) := by
    simp [show p₂ ∘ prodF eι b₁ b₂ = b₂.f ∘ eι from rfl]
  rw [← LieHom.range_eq_top]; rw [eq_top_iff]; rw [← b₂.span_ef]; rw [map_top]; rw [← b₁.basisProd_aux eι b₂]; rw [map_lieSpan]; rw [image_union]; rw [h₁]; rw [h₂]
  simp [range_comp]

中文:
引理 surjective_snd_prod
  证明: by
  set L : LieSubalgebra R (L₁ × L₂) := b₁.prod eι b₂
  set p₂ : L ->ₗ⁅R⁆ L₂ := (LieHom.snd R L₁ L₂).comp L.incl
  have h₁ : range b₂.e = range (p₂ ∘ prodE eι b₁ b₂) := by
    simp [show p₂ ∘ prodE eι b₁ b₂ = b₂.e ∘ eι from rfl]
  have h₂ : range b₂.f = range (p₂ ∘ prodF eι b₁ b₂) := by
    simp [show p₂ ∘ prodF eι b₁ b₂ = b₂.f ∘ eι from rfl]
  rw [← LieHom.range_eq_top]; rw [eq_top_iff]; rw [← b₂.span_ef]; rw [map_top]; rw [← b₁.basisProd_aux eι b₂]; rw [map_lieSpan]; rw [image_union]; rw [h₁]; rw [h₂]
  simp [range_comp]

Depends on / 依赖: L.incl, LieHom, LieHom.range_eq_top, LieHom.snd, LieSubalgebra, basisProd_aux, eq_top_iff, image_union, map_lieSpan, map_top, range_eq_top, span_ef
-/
lemma surjective_snd_prod :
    Surjective ((LieHom.snd R L₁ L₂).comp (prod eι b₁ b₂).incl) := by
  set L : LieSubalgebra R (L₁ × L₂) := b₁.prod eι b₂
  set p₂ : L ->ₗ⁅R⁆ L₂ := (LieHom.snd R L₁ L₂).comp L.incl
  have h₁ : range b₂.e = range (p₂ ∘ prodE eι b₁ b₂) := by
    simp [show p₂ ∘ prodE eι b₁ b₂ = b₂.e ∘ eι from rfl]
  have h₂ : range b₂.f = range (p₂ ∘ prodF eι b₁ b₂) := by
    simp [show p₂ ∘ prodF eι b₁ b₂ = b₂.f ∘ eι from rfl]
  rw [← LieHom.range_eq_top]; rw [eq_top_iff]; rw [← b₂.span_ef]; rw [map_top]; rw [← b₁.basisProd_aux eι b₂]; rw [map_lieSpan]; rw [image_union]; rw [h₁]; rw [h₂]
  simp [range_comp]

/--
lemma `lie_fst_eq_zero_of_mem_prodCartan` / 引理 `lie_fst_eq_zero_of_mem_prodCartan`

English:
lemma lie_fst_eq_zero_of_mem_prodCartan
  proof: by
  have := b₁.isLieAbelian_cartan
  induction hy using lieSpan_induction with
  | mem u hu =>
    obtain ⟨i, rfl⟩ := hu
    suffices ⁅b₁.h' i, x⁆ = 0 by simpa [Subtype.ext_iff, Basis.h'] using this
    apply trivial_lie_zero
  | zero => simp
  | add u v hu hv hu' hv' => simp [hu', hv']
  | smul t u hu hu' => simp [hu']
  | lie u v hu hv hu' hv' => simp [hu', hv']

中文:
引理 lie_fst_eq_zero_of_mem_prodCartan
  证明: by
  have := b₁.isLieAbelian_cartan
  induction hy using lieSpan_induction with
  | mem u hu =>
    obtain ⟨i, rfl⟩ := hu
    suffices ⁅b₁.h' i, x⁆ = 0 by simpa [Subtype.ext_iff, Basis.h'] using this
    apply trivial_lie_zero
  | zero => simp
  | add u v hu hv hu' hv' => simp [hu', hv']
  | smul t u hu hu' => simp [hu']
  | lie u v hu hv hu' hv' => simp [hu', hv']

Depends on / 依赖: Basis.h, Subtype, Subtype.ext_iff, ext_iff, isLieAbelian_cartan, lieSpan_induction, trivial_lie_zero
-/
lemma lie_fst_eq_zero_of_mem_prodCartan
    {y : b₁.prod eι b₂} (hy : y in prodCartan eι b₁ b₂) (x : H₁) :
    ⁅(y : L₁ × L₂).fst, (x : L₁)⁆ = 0 := by
  have := b₁.isLieAbelian_cartan
  induction hy using lieSpan_induction with
  | mem u hu =>
    obtain ⟨i, rfl⟩ := hu
    suffices ⁅b₁.h' i, x⁆ = 0 by simpa [Subtype.ext_iff, Basis.h'] using this
    apply trivial_lie_zero
  | zero => simp
  | add u v hu hv hu' hv' => simp [hu', hv']
  | smul t u hu hu' => simp [hu']
  | lie u v hu hv hu' hv' => simp [hu', hv']

/--
lemma `lie_snd_eq_zero_of_mem_prodCartan` / 引理 `lie_snd_eq_zero_of_mem_prodCartan`

English:
lemma lie_snd_eq_zero_of_mem_prodCartan
  proof: by
  suffices (prodSymmEquiv eι b₁ b₂).symm y in prodCartan eι.symm b₂ b₁ from
    lie_fst_eq_zero_of_mem_prodCartan eι.symm b₂ b₁ this x
  replace hy :
      (prodSymmEquiv eι b₁ b₂).symm y in (prodCartan eι b₁ b₂).map (prodSymmEquiv eι b₁ b₂).symm :=
    mem_image_of_mem (prodSymmEquiv eι b₁ b₂).symm hy
  rw [prodCartan]; rw [map_lieSpan] at hy
  rw [prodCartan]
  convert hy
  ext; simp; grind

中文:
引理 lie_snd_eq_zero_of_mem_prodCartan
  证明: by
  suffices (prodSymmEquiv eι b₁ b₂).symm y in prodCartan eι.symm b₂ b₁ from
    lie_fst_eq_zero_of_mem_prodCartan eι.symm b₂ b₁ this x
  replace hy :
      (prodSymmEquiv eι b₁ b₂).symm y in (prodCartan eι b₁ b₂).map (prodSymmEquiv eι b₁ b₂).symm :=
    mem_image_of_mem (prodSymmEquiv eι b₁ b₂).symm hy
  rw [prodCartan]; rw [map_lieSpan] at hy
  rw [prodCartan]
  convert hy
  ext; simp; grind

Depends on / 依赖: convert, lie_fst_eq_zero_of_mem_prodCartan, map_lieSpan, mem_image_of_mem, prodCartan, prodSymmEquiv, replace
-/
lemma lie_snd_eq_zero_of_mem_prodCartan
    {y : b₁.prod eι b₂} (hy : y in prodCartan eι b₁ b₂) (x : H₂) :
    ⁅(y : L₁ × L₂).snd, (x : L₂)⁆ = 0 := by
  suffices (prodSymmEquiv eι b₁ b₂).symm y in prodCartan eι.symm b₂ b₁ from
    lie_fst_eq_zero_of_mem_prodCartan eι.symm b₂ b₁ this x
  replace hy :
      (prodSymmEquiv eι b₁ b₂).symm y in (prodCartan eι b₁ b₂).map (prodSymmEquiv eι b₁ b₂).symm :=
    mem_image_of_mem (prodSymmEquiv eι b₁ b₂).symm hy
  rw [prodCartan]; rw [map_lieSpan] at hy
  rw [prodCartan]
  convert hy
  ext; simp; grind

end CommRing

section Field

variable {K : Type*} [Field K] [CharZero K]
  [LieAlgebra K L₁] [FiniteDimensional K L₁] {H₁ : LieSubalgebra K L₁} (b₁ : Basis ι₁ H₁)
  [LieAlgebra K L₂] [FiniteDimensional K L₂] {H₂ : LieSubalgebra K L₂} (b₂ : Basis ι₂ H₂)
  (hA : b₁.A.reindex eι eι = b₂.A)
include hA

/--
lemma `prod_lt_top` / 引理 `prod_lt_top`

English:
lemma prod_lt_top
  given: [Nontrivial L₂]
  proof: by
  /- This innocent-looking result is the key. The informal literature seems only to contain
  somewhat heavy-weight proofs (e.g., [Chapter IV, Theorem 14.2](humphreys1972) makes an
  inductive argument using highest weights) but in fact it follows very easily from
  `LieAlgebra.Basis.isCartanSubalgebra`. The argument is essentially: if `b₁.prod eι b₂` is not
  proper then it's Cartan subalgebra contains `H₁ × H₂` which is absurd since it
  `LieAlgebra.Basis.prodCartanEquiv` tells us it is equivalent to `H₁`. -/
  have := Fintype.ofFinite ι₁
  have := Fintype.ofFinite ι₂
  have := b₁.isCartanSubalgebra
  have := b₂.isCartanSubalgebra
  have := (basisProd eι b₁ b₂ hA).isCartanSubalgebra
  rw [lt_top_iff_ne_top]
  intro contra
  have (x : H₁ × H₂) (hx) : ⟨(x.1, x.2), hx⟩ in prodCartan eι b₁ b₂ := by
    rw [← mem_toLieSubmodule]; rw [← rootSpace_zero_eq]; rw [LieModule.mem_genWeightSpace]
    refine fun ⟨y, hy⟩ => ⟨1, ?_⟩
    simpa [Subtype.ext_iff] using ⟨lie_fst_eq_zero_of_mem_prodCartan eι b₁ b₂ hy x.fst,
      lie_snd_eq_zero_of_mem_prodCartan eι b₁ b₂ hy x.snd⟩
  let f : H₁ × H₂ ->ₗ[K] prodCartan eι b₁ b₂ :=
    { toFun x := ⟨⟨⟨x.fst, x.snd⟩, by simp [contra]⟩, this x _⟩
      map_add' := by simp
      map_smul' := by simp }
  have f_inj : Injective f := fun x y h => by simpa [Prod.ext_iff, f] using h
  let g : H₁ × H₂ ->ₗ[K] H₁ := (prodCartanEquiv eι b₁ b₂) ∘ₗ f
  have hg₁ : Injective g := by simpa [g]
  obtain ⟨x₂ : H₂, hx₂ : x₂ != 0⟩ := exists_ne (0 : H₂)
  have hg₂ : g (0, x₂) = g (0, 0) := rfl
  aesop

中文:
引理 prod_lt_top
  条件: [非平凡 L₂]
  证明: by
  /- This innocent-looking result is the key. The informal literature seems only to contain
  somewhat heavy-weight proofs (e.g., [Chapter IV, Theorem 14.2](humphreys1972) makes an
  inductive argument using highest weights) but in fact it follows very easily from
  `LieAlgebra.Basis.isCartanSubalgebra`. The argument is essentially: if `b₁.prod eι b₂` is not
  proper then it's Cartan subalgebra contains `H₁ × H₂` which is absurd since it
  `LieAlgebra.Basis.prodCartanEquiv` tells us it is equivalent to `H₁`. -/
  have := Fintype.ofFinite ι₁
  have := Fintype.ofFinite ι₂
  have := b₁.isCartanSubalgebra
  have := b₂.isCartanSubalgebra
  have := (basisProd eι b₁ b₂ hA).isCartanSubalgebra
  rw [lt_top_iff_ne_top]
  intro contra
  have (x : H₁ × H₂) (hx) : ⟨(x.1, x.2), hx⟩ in prodCartan eι b₁ b₂ := by
    rw [← mem_toLieSubmodule]; rw [← rootSpace_zero_eq]; rw [LieModule.mem_genWeightSpace]
    refine fun ⟨y, hy⟩ => ⟨1, ?_⟩
    simpa [Subtype.ext_iff] using ⟨lie_fst_eq_zero_of_mem_prodCartan eι b₁ b₂ hy x.fst,
      lie_snd_eq_zero_of_mem_prodCartan eι b₁ b₂ hy x.snd⟩
  let f : H₁ × H₂ ->ₗ[K] prodCartan eι b₁ b₂ :=
    { toFun x := ⟨⟨⟨x.fst, x.snd⟩, by simp [contra]⟩, this x _⟩
      map_add' := by simp
      map_smul' := by simp }
  have f_inj : Injective f := fun x y h => by simpa [Prod.ext_iff, f] using h
  let g : H₁ × H₂ ->ₗ[K] H₁ := (prodCartanEquiv eι b₁ b₂) ∘ₗ f
  have hg₁ : Injective g := by simpa [g]
  obtain ⟨x₂ : H₂, hx₂ : x₂ != 0⟩ := exists_ne (0 : H₂)
  have hg₂ : g (0, x₂) = g (0, 0) := rfl
  aesop
-/
lemma prod_lt_top [Nontrivial L₂] :
    b₁.prod eι b₂ < ⊤ := by
  /- This innocent-looking result is the key. The informal literature seems only to contain
  somewhat heavy-weight proofs (e.g., [Chapter IV, Theorem 14.2](humphreys1972) makes an
  inductive argument using highest weights) but in fact it follows very easily from
  `LieAlgebra.Basis.isCartanSubalgebra`. The argument is essentially: if `b₁.prod eι b₂` is not
  proper then it's Cartan subalgebra contains `H₁ × H₂` which is absurd since it
  `LieAlgebra.Basis.prodCartanEquiv` tells us it is equivalent to `H₁`. -/
  have := Fintype.ofFinite ι₁
  have := Fintype.ofFinite ι₂
  have := b₁.isCartanSubalgebra
  have := b₂.isCartanSubalgebra
  have := (basisProd eι b₁ b₂ hA).isCartanSubalgebra
  rw [lt_top_iff_ne_top]
  intro contra
  have (x : H₁ × H₂) (hx) : ⟨(x.1, x.2), hx⟩ in prodCartan eι b₁ b₂ := by
    rw [← mem_toLieSubmodule]; rw [← rootSpace_zero_eq]; rw [LieModule.mem_genWeightSpace]
    refine fun ⟨y, hy⟩ => ⟨1, ?_⟩
    simpa [Subtype.ext_iff] using ⟨lie_fst_eq_zero_of_mem_prodCartan eι b₁ b₂ hy x.fst,
      lie_snd_eq_zero_of_mem_prodCartan eι b₁ b₂ hy x.snd⟩
  let f : H₁ × H₂ ->ₗ[K] prodCartan eι b₁ b₂ :=
    { toFun x := ⟨⟨⟨x.fst, x.snd⟩, by simp [contra]⟩, this x _⟩
      map_add' := by simp
      map_smul' := by simp }
  have f_inj : Injective f := fun x y h => by simpa [Prod.ext_iff, f] using h
  let g : H₁ × H₂ ->ₗ[K] H₁ := (prodCartanEquiv eι b₁ b₂) ∘ₗ f
  have hg₁ : Injective g := by simpa [g]
  obtain ⟨x₂ : H₂, hx₂ : x₂ != 0⟩ := exists_ne (0 : H₂)
  have hg₂ : g (0, x₂) = g (0, 0) := rfl
  aesop

variable [IsSimple K L₁] [IsSimple K L₂]

/--
Definition of `prodEquivLeft` / `prodEquivLeft` 的定义

English:
definition prodEquivLeft
  signature: :
  body: let L : LieSubalgebra K (L₁ × L₂) := b₁.prod eι b₂
  let p₁ : L ->ₗ⁅K⁆ L₁ := (LieHom.fst K L₁ L₂).comp L.incl
  have : Injective p₁ := by
    let p₂ : L ->ₗ⁅K⁆ L₂ := (LieHom.snd K L₁ L₂).comp L.incl
    have disj : Disjoint p₁.ker p₂.ker := by
      rw [disjoint_iff]; rw [_root_.eq_bot_iff]
      rintro ⟨⟨x, y⟩, -⟩
      simp [p₁, p₂, Subtype.ext_iff]
    set I₁ : LieIdeal K L₂ := p₁.ker.map p₂
    suffices I₁ != ⊤ by
      replace this := (IsSimple.eq_bot_or_eq_top I₁).resolve_right this
      rw [LieIdeal.map_eq_bot_iff] at this
      rw [← p₁.ker_eq_bot]; rw [disj.eq_bot_of_le this]
    have : Nontrivial L₂ := IsSimple.nontrivial K L₂
    have := (prod_lt_top eι b₁ b₂ hA).ne
    contrapose this
    have hI₁ : (I₁ : Set L₂) = p₂ '' p₁.ker :=
congr_arg SetLike.coe p₁.ker.coe_map_of_surjective (surjective_snd_prod eι b₁ b₂)
    have hL₂ (x₂ : L₂) : (0, x₂) in L := by
      replace this : x₂ in (I₁ : Set L₂) := by simp [this]
      simpa [p₂, p₁, hI₁] using this
    have hL₁ (x₁ : L₁) : (x₁, 0) in L := by
      obtain ⟨⟨⟨-, y⟩, hy⟩, rfl⟩ : x₁ in range p₁ := mem_range.mpr (surjective_fst_prod eι b₁ b₂ x₁)
      simpa [p₁] using sub_mem hy (hL₂ y)
    rw [eq_top_iff]
    rintro ⟨x₁, x₂⟩ -
    simpa using add_mem (hL₁ x₁) (hL₂ x₂)
  .ofBijective p₁ ⟨this, surjective_fst_prod eι b₁ b₂⟩

中文:
定义 prodEquivLeft
  签名: :
  定义体: let L : LieSubalgebra K (L₁ × L₂) := b₁.prod eι b₂
  let p₁ : L ->ₗ⁅K⁆ L₁ := (LieHom.fst K L₁ L₂).comp L.incl
  have : Injective p₁ := by
    let p₂ : L ->ₗ⁅K⁆ L₂ := (LieHom.snd K L₁ L₂).comp L.incl
    have disj : Disjoint p₁.ker p₂.ker := by
      rw [disjoint_iff]; rw [_root_.eq_bot_iff]
      rintro ⟨⟨x, y⟩, -⟩
      simp [p₁, p₂, Subtype.ext_iff]
    set I₁ : LieIdeal K L₂ := p₁.ker.map p₂
    suffices I₁ != ⊤ by
      replace this := (IsSimple.eq_bot_or_eq_top I₁).resolve_right this
      rw [LieIdeal.map_eq_bot_iff] at this
      rw [← p₁.ker_eq_bot]; rw [disj.eq_bot_of_le this]
    have : Nontrivial L₂ := IsSimple.nontrivial K L₂
    have := (prod_lt_top eι b₁ b₂ hA).ne
    contrapose this
    have hI₁ : (I₁ : Set L₂) = p₂ '' p₁.ker :=
congr_arg SetLike.coe p₁.ker.coe_map_of_surjective (surjective_snd_prod eι b₁ b₂)
    have hL₂ (x₂ : L₂) : (0, x₂) in L := by
      replace this : x₂ in (I₁ : Set L₂) := by simp [this]
      simpa [p₂, p₁, hI₁] using this
    have hL₁ (x₁ : L₁) : (x₁, 0) in L := by
      obtain ⟨⟨⟨-, y⟩, hy⟩, rfl⟩ : x₁ in range p₁ := mem_range.mpr (surjective_fst_prod eι b₁ b₂ x₁)
      simpa [p₁] using sub_mem hy (hL₂ y)
    rw [eq_top_iff]
    rintro ⟨x₁, x₂⟩ -
    simpa using add_mem (hL₁ x₁) (hL₂ x₂)
  .ofBijective p₁ ⟨this, surjective_fst_prod eι b₁ b₂⟩

Depends on / 依赖: Disjoint, Injective, IsSimple, IsSimple.eq_bot_or_eq_top, L.incl, LieHom, LieHom.fst, LieHom.snd, LieIdeal, LieIdeal.map_eq_bot_iff, LieSubalgebra, Subtype, Subtype.ext_iff, _root_, _root_.eq_bot_iff, disjoint_iff, eq_bot_iff, eq_bot_or_eq_top, ext_iff, ker.map
-/
def prodEquivLeft :
    b₁.prod eι b₂ ≃ₗ⁅K⁆ L₁ :=
  let L : LieSubalgebra K (L₁ × L₂) := b₁.prod eι b₂
  let p₁ : L ->ₗ⁅K⁆ L₁ := (LieHom.fst K L₁ L₂).comp L.incl
  have : Injective p₁ := by
    let p₂ : L ->ₗ⁅K⁆ L₂ := (LieHom.snd K L₁ L₂).comp L.incl
    have disj : Disjoint p₁.ker p₂.ker := by
      rw [disjoint_iff]; rw [_root_.eq_bot_iff]
      rintro ⟨⟨x, y⟩, -⟩
      simp [p₁, p₂, Subtype.ext_iff]
    set I₁ : LieIdeal K L₂ := p₁.ker.map p₂
    suffices I₁ != ⊤ by
      replace this := (IsSimple.eq_bot_or_eq_top I₁).resolve_right this
      rw [LieIdeal.map_eq_bot_iff] at this
      rw [← p₁.ker_eq_bot]; rw [disj.eq_bot_of_le this]
    have : Nontrivial L₂ := IsSimple.nontrivial K L₂
    have := (prod_lt_top eι b₁ b₂ hA).ne
    contrapose this
    have hI₁ : (I₁ : Set L₂) = p₂ '' p₁.ker :=
congr_arg SetLike.coe p₁.ker.coe_map_of_surjective (surjective_snd_prod eι b₁ b₂)
    have hL₂ (x₂ : L₂) : (0, x₂) in L := by
      replace this : x₂ in (I₁ : Set L₂) := by simp [this]
      simpa [p₂, p₁, hI₁] using this
    have hL₁ (x₁ : L₁) : (x₁, 0) in L := by
      obtain ⟨⟨⟨-, y⟩, hy⟩, rfl⟩ : x₁ in range p₁ := mem_range.mpr (surjective_fst_prod eι b₁ b₂ x₁)
      simpa [p₁] using sub_mem hy (hL₂ y)
    rw [eq_top_iff]
    rintro ⟨x₁, x₂⟩ -
    simpa using add_mem (hL₁ x₁) (hL₂ x₂)
  .ofBijective p₁ ⟨this, surjective_fst_prod eι b₁ b₂⟩

/--
Definition of `prodEquivRight` / `prodEquivRight` 的定义

English:
definition prodEquivRight
  signature: :
  body: (prodSymmEquiv eι b₁ b₂).symm.trans (prodEquivLeft eι.symm b₂ b₁ <| by simp [← hA])

中文:
定义 prodEquivRight
  签名: :
  定义体: (prodSymmEquiv eι b₁ b₂).symm.trans (prodEquivLeft eι.symm b₂ b₁ <| by simp [← hA])

Depends on / 依赖: prodEquivLeft, prodSymmEquiv, symm.trans
-/
def prodEquivRight :
    b₁.prod eι b₂ ≃ₗ⁅K⁆ L₂ :=
  (prodSymmEquiv eι b₁ b₂).symm.trans (prodEquivLeft eι.symm b₂ b₁ <| by simp [← hA])

/-- Simple Lie algebras with equivalent bases are equivalent. -/
public def equivOfReindex :
    L₁ ≃ₗ⁅K⁆ L₂ :=
  (prodEquivLeft eι b₁ b₂ hA).symm.trans (prodEquivRight eι b₁ b₂ hA)

end Field

end LieAlgebra.Basis
