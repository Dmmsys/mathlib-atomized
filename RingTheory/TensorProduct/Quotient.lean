/-
Copyright (c) 2025 Christian Merten, Yi Song, Sihan Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Yi Song, Sihan Su
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Interaction between quotients and tensor products for algebras

This file proves algebra analogs of the isomorphisms in
`Mathlib/LinearAlgebra/TensorProduct/Quotient.lean`.

## Main results

- `Algebra.TensorProduct.quotIdealMapEquivTensorQuot`:
  `B ⧸ (I.map <| algebraMap A B) ≃ₐ[B] B ⊗[A] (A ⧸ I)`
-/

@[expose] public section

open TensorProduct

namespace Algebra.TensorProduct

section

variable {A : Type*} (B : Type*) [CommRing A] [CommRing B] [Algebra A B] (I : Ideal A)

/--
Definition of `quotIdealMapEquivTensorQuotAux` / `quotIdealMapEquivTensorQuotAux` 的定义

English:
definition quotIdealMapEquivTensorQuotAux
  signature: :
  body: AddEquiv.toLinearEquiv (TensorProduct.tensorQuotEquivQuotSMul B I ≪≫ₗ
      Submodule.quotEquivOfEq _ _ (Ideal.smul_top_eq_map I) ≪≫ₗ
      Submodule.Quotient.restrictScalarsEquiv A (I.map <| algebraMap A B)).symm <| by
    intro c x
    obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl

中文:
定义 quotIdealMapEquivTensorQuotAux
  签名: :
  定义体: AddEquiv.toLinearEquiv (TensorProduct.tensorQuotEquivQuotSMul B I ≪≫ₗ
      Submodule.quotEquivOfEq _ _ (Ideal.smul_top_eq_map I) ≪≫ₗ
      Submodule.Quotient.restrictScalarsEquiv A (I.map <| algebraMap A B)).symm <| by
    intro c x
    obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl

Depends on / 依赖: AddEquiv, AddEquiv.toLinearEquiv, I.map, Ideal.Quotient.mk_surjective, Ideal.smul_top_eq_map, Quotient, Submodule, Submodule.Quotient.restrictScalarsEquiv, Submodule.quotEquivOfEq, TensorProduct, TensorProduct.tensorQuotEquivQuotSMul, algebraMap, mk_surjective, quotEquivOfEq, restrictScalarsEquiv, smul_top_eq_map, tensorQuotEquivQuotSMul, toLinearEquiv
-/
noncomputable def quotIdealMapEquivTensorQuotAux :
      (B ⧸ (I.map <| algebraMap A B)) ≃ₗ[B] B otimes[A] (A ⧸ I) :=
  AddEquiv.toLinearEquiv (TensorProduct.tensorQuotEquivQuotSMul B I ≪≫ₗ
      Submodule.quotEquivOfEq _ _ (Ideal.smul_top_eq_map I) ≪≫ₗ
      Submodule.Quotient.restrictScalarsEquiv A (I.map <| algebraMap A B)).symm <| by
    intro c x
    obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl

/--
lemma `quotIdealMapEquivTensorQuotAux_mk` / 引理 `quotIdealMapEquivTensorQuotAux_mk`

English:
lemma quotIdealMapEquivTensorQuotAux_mk
  given: (b : B)
  proof: rfl

中文:
引理 quotIdealMapEquivTensorQuotAux_mk
  条件: (b : B)
  证明: rfl
-/
private lemma quotIdealMapEquivTensorQuotAux_mk (b : B) :
    (quotIdealMapEquivTensorQuotAux B I) b = b otimesₜ[A] 1 :=
  rfl

/--
Definition of `quotIdealMapEquivTensorQuot` / `quotIdealMapEquivTensorQuot` 的定义

English:
definition quotIdealMapEquivTensorQuot
  signature: :
  body: AlgEquiv.ofLinearEquiv (quotIdealMapEquivTensorQuotAux B I) rfl
    (fun x y => by
      obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective y
      simp_rw [← map_mul, quotIdealMapEquivTensorQuotAux_mk]
      simp)

@[simp]

中文:
定义 quotIdealMapEquivTensorQuot
  签名: :
  定义体: AlgEquiv.ofLinearEquiv (quotIdealMapEquivTensorQuotAux B I) rfl
    (fun x y => by
      obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective y
      simp_rw [← map_mul, quotIdealMapEquivTensorQuotAux_mk]
      simp)

@[simp]

Depends on / 依赖: AlgEquiv, AlgEquiv.ofLinearEquiv, Ideal.Quotient.mk_surjective, Quotient, map_mul, mk_surjective, ofLinearEquiv, quotIdealMapEquivTensorQuotAux, quotIdealMapEquivTensorQuotAux_mk, simp_rw
-/
noncomputable def quotIdealMapEquivTensorQuot :
    (B ⧸ (I.map <| algebraMap A B)) ≃ₐ[B] B otimes[A] (A ⧸ I) :=
  AlgEquiv.ofLinearEquiv (quotIdealMapEquivTensorQuotAux B I) rfl
    (fun x y => by
      obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective y
      simp_rw [← map_mul, quotIdealMapEquivTensorQuotAux_mk]
      simp)

@[simp]
/--
lemma `quotIdealMapEquivTensorQuot_mk` / 引理 `quotIdealMapEquivTensorQuot_mk`

English:
lemma quotIdealMapEquivTensorQuot_mk
  given: (b : B)
  proof: rfl

@[simp]

中文:
引理 quotIdealMapEquivTensorQuot_mk
  条件: (b : B)
  证明: rfl

@[simp]
-/
lemma quotIdealMapEquivTensorQuot_mk (b : B) :
    quotIdealMapEquivTensorQuot B I b = b otimesₜ[A] 1 :=
  rfl

@[simp]
/--
lemma `quotIdealMapEquivTensorQuot_symm_tmul` / 引理 `quotIdealMapEquivTensorQuot_symm_tmul`

English:
lemma quotIdealMapEquivTensorQuot_symm_tmul
  given: (b : B) (a : A)
  proof: rfl

中文:
引理 quotIdealMapEquivTensorQuot_symm_tmul
  条件: (b : B) (a : A)
  证明: rfl
-/
lemma quotIdealMapEquivTensorQuot_symm_tmul (b : B) (a : A) :
    (quotIdealMapEquivTensorQuot B I).symm (b otimesₜ[A] a) = Submodule.Quotient.mk (a • b) :=
  rfl

/--
Definition of `quotIdealMapEquivQuotTensor` / `quotIdealMapEquivQuotTensor` 的定义

English:
definition quotIdealMapEquivQuotTensor
  signature: :
  body: AlgEquiv.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
  { __ := (quotIdealMapEquivTensorQuot B I).toRingEquiv.trans
      (Algebra.TensorProduct.comm A B (A ⧸ I)).toRingEquiv
    commutes' x := by
      suffices Algebra.TensorProduct.comm A B (A ⧸ I) (quotIdealMapEquivTensorQuot B I
        (Ideal.Quotient.mk (I.map (algebraMap A B)) (algebraMap A B x))) =
          (algebraMap A (TensorProduct A (A ⧸ I) B)) x by simpa
      rw [quotIdealMapEquivTensorQuot_mk]; rw [tmul_one_eq_one_tmul]
      simp }

@[simp]

中文:
定义 quotIdealMapEquivQuotTensor
  签名: :
  定义体: AlgEquiv.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
  { __ := (quotIdealMapEquivTensorQuot B I).toRingEquiv.trans
      (Algebra.TensorProduct.comm A B (A ⧸ I)).toRingEquiv
    commutes' x := by
      suffices Algebra.TensorProduct.comm A B (A ⧸ I) (quotIdealMapEquivTensorQuot B I
        (Ideal.Quotient.mk (I.map (algebraMap A B)) (algebraMap A B x))) =
          (algebraMap A (TensorProduct A (A ⧸ I) B)) x by simpa
      rw [quotIdealMapEquivTensorQuot_mk]; rw [tmul_one_eq_one_tmul]
      simp }

@[simp]

Depends on / 依赖: AlgEquiv, AlgEquiv.extendScalarsOfSurjective, Algebra, Algebra.TensorProduct.comm, I.map, Ideal.Quotient.mk, Ideal.Quotient.mk_surjective, Quotient, TensorProduct, algebraMap, commutes, extendScalarsOfSurjective, mk_surjective, quotIdealMapEquivTensorQuot, quotIdealMapEquivTensorQuot_mk, tmul_one_eq_one_tmul, toRingEquiv, toRingEquiv.trans
-/
noncomputable def quotIdealMapEquivQuotTensor :
    (B ⧸ (I.map (algebraMap A B))) ≃ₐ[A ⧸ I] (A ⧸ I) otimes[A] B :=
  AlgEquiv.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
  { __ := (quotIdealMapEquivTensorQuot B I).toRingEquiv.trans
      (Algebra.TensorProduct.comm A B (A ⧸ I)).toRingEquiv
    commutes' x := by
      suffices Algebra.TensorProduct.comm A B (A ⧸ I) (quotIdealMapEquivTensorQuot B I
        (Ideal.Quotient.mk (I.map (algebraMap A B)) (algebraMap A B x))) =
          (algebraMap A (TensorProduct A (A ⧸ I) B)) x by simpa
      rw [quotIdealMapEquivTensorQuot_mk]; rw [tmul_one_eq_one_tmul]
      simp }

@[simp]
/--
lemma `quotIdealMapEquivQuotTensor_mk` / 引理 `quotIdealMapEquivQuotTensor_mk`

English:
lemma quotIdealMapEquivQuotTensor_mk
  given: (b : B)
  proof: rfl

中文:
引理 quotIdealMapEquivQuotTensor_mk
  条件: (b : B)
  证明: rfl
-/
lemma quotIdealMapEquivQuotTensor_mk (b : B) :
    quotIdealMapEquivQuotTensor B I b = 1 otimesₜ[A] b :=
  rfl

end

section

variable {R : Type*} (S T A : Type*) [CommRing R] [CommRing S] [Algebra R S]
  [CommRing T] [Algebra R T] [CommRing A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `tensorQuotientEquiv` / `tensorQuotientEquiv` 的定义

English:
definition tensorQuotientEquiv
  signature: (I : Ideal T)
  body: letI g : (A otimes[R] T ⧸ LinearMap.range (AlgebraTensorModule.lTensor S A
      (I.subtype.restrictScalars R))) ≃ₗ[S]
      A otimes[R] T ⧸ (I.map (includeRight (A := A) (R := R))).restrictScalars S :=
    Submodule.quotEquivOfEq _ _ (AlgebraTensorModule.range_lTensor_idealMap _ _ _)
.ofLinearEquiv (AlgebraTensorModule.tensorQuotientEquiv (R := R) S T A I ≪≫ₗ g) rfl by
    refine LinearMap.map_mul_of_map_mul_tmul fun a₁ a₂ b₁ b₂ => ?_
    obtain ⟨b₁, rfl⟩ := Ideal.Quotient.mk_surjective b₁
    obtain ⟨b₂, rfl⟩ := Ideal.Quotient.mk_surjective b₂
    rw [← map_mul]
    simp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply, g,
      AlgebraTensorModule.tensorQuotientEquiv_apply_tmul, ← Ideal.Quotient.mk_eq_mk,
      ← Algebra.TensorProduct.tmul_mul_tmul]
    rfl

@[simp]

中文:
定义 tensorQuotientEquiv
  签名: (I : 理想 T)
  定义体: letI g : (A otimes[R] T ⧸ LinearMap.range (AlgebraTensorModule.lTensor S A
      (I.subtype.restrictScalars R))) ≃ₗ[S]
      A otimes[R] T ⧸ (I.map (includeRight (A := A) (R := R))).restrictScalars S :=
    Submodule.quotEquivOfEq _ _ (AlgebraTensorModule.range_lTensor_idealMap _ _ _)
.ofLinearEquiv (AlgebraTensorModule.tensorQuotientEquiv (R := R) S T A I ≪≫ₗ g) rfl by
    refine LinearMap.map_mul_of_map_mul_tmul fun a₁ a₂ b₁ b₂ => ?_
    obtain ⟨b₁, rfl⟩ := Ideal.Quotient.mk_surjective b₁
    obtain ⟨b₂, rfl⟩ := Ideal.Quotient.mk_surjective b₂
    rw [← map_mul]
    simp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply, g,
      AlgebraTensorModule.tensorQuotientEquiv_apply_tmul, ← Ideal.Quotient.mk_eq_mk,
      ← Algebra.TensorProduct.tmul_mul_tmul]
    rfl

@[simp]
-/
noncomputable def tensorQuotientEquiv (I : Ideal T) :
    A otimes[R] (T ⧸ I) ≃ₐ[S] (A otimes[R] T) ⧸ I.map (includeRight (A := A) (R := R)) :=
  letI g : (A otimes[R] T ⧸ LinearMap.range (AlgebraTensorModule.lTensor S A
      (I.subtype.restrictScalars R))) ≃ₗ[S]
      A otimes[R] T ⧸ (I.map (includeRight (A := A) (R := R))).restrictScalars S :=
    Submodule.quotEquivOfEq _ _ (AlgebraTensorModule.range_lTensor_idealMap _ _ _)
.ofLinearEquiv (AlgebraTensorModule.tensorQuotientEquiv (R := R) S T A I ≪≫ₗ g) rfl by
    refine LinearMap.map_mul_of_map_mul_tmul fun a₁ a₂ b₁ b₂ => ?_
    obtain ⟨b₁, rfl⟩ := Ideal.Quotient.mk_surjective b₁
    obtain ⟨b₂, rfl⟩ := Ideal.Quotient.mk_surjective b₂
    rw [← map_mul]
    simp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply, g,
      AlgebraTensorModule.tensorQuotientEquiv_apply_tmul, ← Ideal.Quotient.mk_eq_mk,
      ← Algebra.TensorProduct.tmul_mul_tmul]
    rfl

@[simp]
/--
lemma `tensorQuotientEquiv_apply_tmul` / 引理 `tensorQuotientEquiv_apply_tmul`

English:
lemma tensorQuotientEquiv_apply_tmul
  given: (I : Ideal T) (a : A) (t : T)
  proof: rfl

@[simp]

中文:
引理 tensorQuotientEquiv_apply_tmul
  条件: (I : 理想 T) (a : A) (t : T)
  证明: rfl

@[simp]
-/
lemma tensorQuotientEquiv_apply_tmul (I : Ideal T) (a : A) (t : T) :
    tensorQuotientEquiv (R := R) S T A I (a otimesₜ t) = a otimesₜ[R] t :=
  rfl

@[simp]
/--
lemma `tensorQuotientEquiv_symm_apply_tmul` / 引理 `tensorQuotientEquiv_symm_apply_tmul`

English:
lemma tensorQuotientEquiv_symm_apply_tmul
  given: (I : Ideal T) (a : A) (t : T)
  proof: rfl

中文:
引理 tensorQuotientEquiv_symm_apply_tmul
  条件: (I : 理想 T) (a : A) (t : T)
  证明: rfl

Depends on / 依赖: Ideal.Quotient.mk, Quotient
-/
lemma tensorQuotientEquiv_symm_apply_tmul (I : Ideal T) (a : A) (t : T) :
    (tensorQuotientEquiv (R := R) S T A I).symm (a otimesₜ[R] t) = a otimesₜ[R] (Ideal.Quotient.mk I t) :=
  rfl

/--
Definition of `quotientTensorEquiv` / `quotientTensorEquiv` 的定义

English:
definition quotientTensorEquiv
  signature: (I : Ideal A)
  body: (TensorProduct.comm R (A ⧸ I) T).toRingEquiv.trans
(tensorQuotientEquiv (R := R) R A T I).toRingEquiv.trans
Ideal.quotientEquiv _ _ (TensorProduct.comm R T A).toRingEquiv (I.map_map _ _).symm
  commutes' _ := rfl

@[simp]

中文:
定义 quotientTensorEquiv
  签名: (I : 理想 A)
  定义体: (TensorProduct.comm R (A ⧸ I) T).toRingEquiv.trans
(tensorQuotientEquiv (R := R) R A T I).toRingEquiv.trans
Ideal.quotientEquiv _ _ (TensorProduct.comm R T A).toRingEquiv (I.map_map _ _).symm
  commutes' _ := rfl

@[simp]

Depends on / 依赖: TensorProduct, TensorProduct.comm, toRingEquiv, toRingEquiv.trans
-/
noncomputable def quotientTensorEquiv (I : Ideal A) :
    (A ⧸ I) otimes[R] T ≃ₐ[S] (A otimes[R] T) ⧸ I.map (algebraMap A (A otimes[R] T)) where
__ := (TensorProduct.comm R (A ⧸ I) T).toRingEquiv.trans
(tensorQuotientEquiv (R := R) R A T I).toRingEquiv.trans
Ideal.quotientEquiv _ _ (TensorProduct.comm R T A).toRingEquiv (I.map_map _ _).symm
  commutes' _ := rfl

@[simp]
/--
lemma `quotientTensorEquiv_apply_tmul` / 引理 `quotientTensorEquiv_apply_tmul`

English:
lemma quotientTensorEquiv_apply_tmul
  given: (I : Ideal A) (a : A) (t : T)
  proof: rfl

@[simp]

中文:
引理 quotientTensorEquiv_apply_tmul
  条件: (I : 理想 A) (a : A) (t : T)
  证明: rfl

@[simp]
-/
lemma quotientTensorEquiv_apply_tmul (I : Ideal A) (a : A) (t : T) :
    quotientTensorEquiv (R := R) S T A I (a otimesₜ t) = a otimesₜ[R] t :=
  rfl

@[simp]
/--
lemma `quotientTensorEquiv_symm_apply_tmul` / 引理 `quotientTensorEquiv_symm_apply_tmul`

English:
lemma quotientTensorEquiv_symm_apply_tmul
  given: (I : Ideal A) (a : A) (t : T)
  proof: rfl

中文:
引理 quotientTensorEquiv_symm_apply_tmul
  条件: (I : 理想 A) (a : A) (t : T)
  证明: rfl

Depends on / 依赖: Ideal.Quotient.mk, Quotient
-/
lemma quotientTensorEquiv_symm_apply_tmul (I : Ideal A) (a : A) (t : T) :
    (quotientTensorEquiv (R := R) S T A I).symm (a otimesₜ[R] t) = Ideal.Quotient.mk _ a otimesₜ[R] t :=
  rfl

end

end Algebra.TensorProduct

/--
lemma `Ideal.subtype_rTensor_range` / 引理 `Ideal.subtype_rTensor_range`

English:
lemma Ideal.subtype_rTensor_range
  statement: {R : Type*} [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]
  proof: by
  rw [← Submodule.ker_mkQ (I • (⊤ : Submodule R M))]; rw [LinearMap.range_comp]; rw [← Submodule.map_symm_eq_iff]; rw [← Submodule.comap_equiv_eq_map_symm]; rw [← LinearMap.ker_comp]; rw [← TensorProduct.quotTensorEquivQuotSMul_comp_mkQ_rTensor]; rw [LinearEquiv.ker_comp]
  exact LinearMap.exact_iff.mp (rTensor_exact M (LinearMap.exact_subtype_mkQ I) I.mkQ_surjective)

中文:
引理 理想.subtype_rTensor_range
  结论: {R : 类型} [交换环 R] (M : 类型) [加法交换群 M] [模 R M]
  证明: by
  rw [← Submodule.ker_mkQ (I • (⊤ : Submodule R M))]; rw [LinearMap.range_comp]; rw [← Submodule.map_symm_eq_iff]; rw [← Submodule.comap_equiv_eq_map_symm]; rw [← LinearMap.ker_comp]; rw [← TensorProduct.quotTensorEquivQuotSMul_comp_mkQ_rTensor]; rw [LinearEquiv.ker_comp]
  exact LinearMap.exact_iff.mp (rTensor_exact M (LinearMap.exact_subtype_mkQ I) I.mkQ_surjective)

Depends on / 依赖: I.mkQ_surjective, LinearEquiv, LinearEquiv.ker_comp, LinearMap, LinearMap.exact_iff.mp, LinearMap.exact_subtype_mkQ, LinearMap.ker_comp, LinearMap.range_comp, Submodule, Submodule.comap_equiv_eq_map_symm, Submodule.ker_mkQ, Submodule.map_symm_eq_iff, TensorProduct, TensorProduct.quotTensorEquivQuotSMul_comp_mkQ_rTensor, comap_equiv_eq_map_symm, exact_iff, exact_subtype_mkQ, ker_comp, ker_mkQ, map_symm_eq_iff
-/
lemma Ideal.subtype_rTensor_range {R : Type*} [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]
    (I : Ideal R) :
    ((TensorProduct.lid R M).comp (I.subtype.rTensor M)).range = I • (⊤ : Submodule R M) := by
  rw [← Submodule.ker_mkQ (I • (⊤ : Submodule R M))]; rw [LinearMap.range_comp]; rw [← Submodule.map_symm_eq_iff]; rw [← Submodule.comap_equiv_eq_map_symm]; rw [← LinearMap.ker_comp]; rw [← TensorProduct.quotTensorEquivQuotSMul_comp_mkQ_rTensor]; rw [LinearEquiv.ker_comp]
  exact LinearMap.exact_iff.mp (rTensor_exact M (LinearMap.exact_subtype_mkQ I) I.mkQ_surjective)

section

variable {R R' R'' S : Type*} [CommRing R] [CommRing R'] [CommRing R''] [CommRing S]
  [Algebra R R'] [Algebra R R''] [Algebra R' R''] [IsScalarTower R R' R''] [Algebra R S]

variable (R'') in
set_option backward.isDefEq.respectTransparency false in
attribute [local ext high] Ideal.Quotient.algHom_ext in
/-- Let `e` be an element of `R' ⊗[R] S`. Then `R'' ⊗[R'] ((R' ⊗[R] S) / e)` is isomorphic to
`(R'' ⊗[R] S) / e` as `R''`-algebras. -/
noncomputable
/--
Definition of `Algebra.tensorQuotientTensorEquiv` / `Algebra.tensorQuotientTensorEquiv` 的定义

English:
definition Algebra.tensorQuotientTensorEquiv
  signature: (e : R' otimes[R] S)
  body: letI φ := Algebra.TensorProduct.rTensor S (Algebra.ofId R' R'')
  letI ψ : R'' otimes[R] S ->ₐ[R''] R'' otimes[R'] (R' otimes[R] S ⧸ Ideal.span {e}) :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _)
      ((Algebra.TensorProduct.includeRight.restrictScalars R).comp
      ((Ideal.Quotient.mkₐ _ _).comp Algebra.TensorProduct.includeRight)) fun _ _ => .all _ _
  haveI hψφ : (ψ.restrictScalars R').comp φ =
      (Algebra.TensorProduct.includeRight.restrictScalars R').comp (Ideal.Quotient.mkₐ _ _) := by
    ext; simp [ψ, φ]
  haveI heψ : Ideal.span {φ e} <= RingHom.ker ψ := by simpa [Ideal.span_le] using congr($hψφ e)
  AlgEquiv.ofAlgHom (Algebra.TensorProduct.lift (Algebra.ofId _ _) (Ideal.quotientMapₐ _ φ
    (Ideal.map_le_iff_le_comap.mp (by simp [Ideal.map_span, φ]))) fun _ _ => .all _ _)
    (Ideal.Quotient.liftₐ _ ψ heψ) (by ext; simp [ψ, φ]) (by ext; simp [φ, ψ])

@[simp]

中文:
定义 代数.tensorQuotientTensorEquiv
  签名: (e : R' otimes[R] S)
  定义体: letI φ := Algebra.TensorProduct.rTensor S (Algebra.ofId R' R'')
  letI ψ : R'' otimes[R] S ->ₐ[R''] R'' otimes[R'] (R' otimes[R] S ⧸ Ideal.span {e}) :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _)
      ((Algebra.TensorProduct.includeRight.restrictScalars R).comp
      ((Ideal.Quotient.mkₐ _ _).comp Algebra.TensorProduct.includeRight)) fun _ _ => .all _ _
  haveI hψφ : (ψ.restrictScalars R').comp φ =
      (Algebra.TensorProduct.includeRight.restrictScalars R').comp (Ideal.Quotient.mkₐ _ _) := by
    ext; simp [ψ, φ]
  haveI heψ : Ideal.span {φ e} <= RingHom.ker ψ := by simpa [Ideal.span_le] using congr($hψφ e)
  AlgEquiv.ofAlgHom (Algebra.TensorProduct.lift (Algebra.ofId _ _) (Ideal.quotientMapₐ _ φ
    (Ideal.map_le_iff_le_comap.mp (by simp [Ideal.map_span, φ]))) fun _ _ => .all _ _)
    (Ideal.Quotient.liftₐ _ ψ heψ) (by ext; simp [ψ, φ]) (by ext; simp [φ, ψ])

@[simp]

Depends on / 依赖: Algebra, Algebra.TensorProduct.includeRight, Algebra.TensorProduct.includeRight.restrictScalars, Algebra.TensorProduct.lift, Algebra.TensorProduct.rTensor, Algebra.ofId, Ideal.Quotient.mk, Ideal.span, Quotient, TensorProduct, includeRight, otimes, rTensor, restrictScalars
-/
def Algebra.tensorQuotientTensorEquiv (e : R' otimes[R] S) :
    R'' otimes[R'] (R' otimes[R] S ⧸ Ideal.span {e}) ≃ₐ[R'']
    (R'' otimes[R] S ⧸ Ideal.span {Algebra.TensorProduct.rTensor S (Algebra.ofId R' R'') e}) :=
  letI φ := Algebra.TensorProduct.rTensor S (Algebra.ofId R' R'')
  letI ψ : R'' otimes[R] S ->ₐ[R''] R'' otimes[R'] (R' otimes[R] S ⧸ Ideal.span {e}) :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _)
      ((Algebra.TensorProduct.includeRight.restrictScalars R).comp
      ((Ideal.Quotient.mkₐ _ _).comp Algebra.TensorProduct.includeRight)) fun _ _ => .all _ _
  haveI hψφ : (ψ.restrictScalars R').comp φ =
      (Algebra.TensorProduct.includeRight.restrictScalars R').comp (Ideal.Quotient.mkₐ _ _) := by
    ext; simp [ψ, φ]
  haveI heψ : Ideal.span {φ e} <= RingHom.ker ψ := by simpa [Ideal.span_le] using congr($hψφ e)
  AlgEquiv.ofAlgHom (Algebra.TensorProduct.lift (Algebra.ofId _ _) (Ideal.quotientMapₐ _ φ
    (Ideal.map_le_iff_le_comap.mp (by simp [Ideal.map_span, φ]))) fun _ _ => .all _ _)
    (Ideal.Quotient.liftₐ _ ψ heψ) (by ext; simp [ψ, φ]) (by ext; simp [φ, ψ])

@[simp]
/--
lemma `Algebra.tensorQuotientTensorEquiv_tmul` / 引理 `Algebra.tensorQuotientTensorEquiv_tmul`

English:
lemma Algebra.tensorQuotientTensorEquiv_tmul
  given: (e : R' otimes[R] S) (a : R'') (b : R') (c : S)
  proof: by
  simp [Algebra.tensorQuotientTensorEquiv, ← Ideal.Quotient.mk_algebraMap, ← map_mul]

中文:
引理 代数.tensorQuotientTensorEquiv_tmul
  条件: (e : R' otimes[R] S) (a : R'') (b : R') (c : S)
  证明: by
  simp [Algebra.tensorQuotientTensorEquiv, ← Ideal.Quotient.mk_algebraMap, ← map_mul]

Depends on / 依赖: Algebra, Algebra.tensorQuotientTensorEquiv, Ideal.Quotient.mk_algebraMap, Quotient, map_mul, mk_algebraMap, tensorQuotientTensorEquiv
-/
lemma Algebra.tensorQuotientTensorEquiv_tmul (e : R' otimes[R] S) (a : R'') (b : R') (c : S) :
    Algebra.tensorQuotientTensorEquiv R'' e (a otimesₜ Ideal.Quotient.mk _ (b otimesₜ c)) =
      Ideal.Quotient.mk _ ((a * algebraMap R' R'' b) otimesₜ c) := by
  simp [Algebra.tensorQuotientTensorEquiv, ← Ideal.Quotient.mk_algebraMap, ← map_mul]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `Algebra.tensorQuotientTensorEquiv_symm_tmul` / 引理 `Algebra.tensorQuotientTensorEquiv_symm_tmul`

English:
lemma Algebra.tensorQuotientTensorEquiv_symm_tmul
  given: (e : R' otimes[R] S) (a : R'') (b : S)
  proof: by
  simp [Algebra.tensorQuotientTensorEquiv]

中文:
引理 代数.tensorQuotientTensorEquiv_symm_tmul
  条件: (e : R' otimes[R] S) (a : R'') (b : S)
  证明: by
  simp [Algebra.tensorQuotientTensorEquiv]

Depends on / 依赖: Algebra, Algebra.tensorQuotientTensorEquiv, tensorQuotientTensorEquiv
-/
lemma Algebra.tensorQuotientTensorEquiv_symm_tmul (e : R' otimes[R] S) (a : R'') (b : S) :
    (Algebra.tensorQuotientTensorEquiv R'' e).symm (Ideal.Quotient.mk _ (a otimesₜ b)) =
      a otimesₜ Ideal.Quotient.mk _ (1 otimesₜ b) := by
  simp [Algebra.tensorQuotientTensorEquiv]

end
