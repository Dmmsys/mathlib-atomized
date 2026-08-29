/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Scott Carnahan
-/
module

public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.LinearAlgebra.DirectSum.TensorProduct

/-! # Decomposition of tensor product

In this file, we describe the properties of decomposition under tensor product. Suppose `ℳ` is a
decomposition of an `R`-module `M` indexed by a type `ι`. Given an `R`-module `N`, the `R`-module
`M ⊗[R] N` has a decomposition into pieces `fun i ↦ (ℳ i) ⊗[R] N`. Given a commutative `R`-algebra
`S`, the `S`-module `S ⊗[R] M` has a decomposition `fun i ↦ (ℳ i).baseChange S`.

-/

public section

open TensorProduct LinearMap

namespace DirectSum

variable {ι R M S : Type*}
  [CommSemiring R] [AddCommMonoid M] [Module R M]
  (ℳ : ι -> Submodule R M)

section BaseChange

variable [DecidableEq ι] [Decomposition ℳ] [CommSemiring S] [Algebra R S]

/--
Instance `Decomposition.baseChange` / 实例 `Decomposition.baseChange`

English:
instance Decomposition.baseChange
  signature: : Decomposition fun i => (ℳ i).baseChange S
  body: by
  refine .ofLinearMap _ (lmap (ℳ · |>.toBaseChange S) ∘ₗ
    (directSumRight R S S fun i => ℳ i).toLinearMap ∘ₗ
    ((decomposeLinearEquiv ℳ).baseChange R S)) ?_ ?_
  · simp_rw [← comp_assoc]
    rw [← LinearEquiv.eq_comp_toLinearMap_symm]
    ext
    simp
  · ext : 1
    rw [← LinearMap.cancel_right ((ℳ _).toBaseChange_surjective S)]
    ext : 3
    simp

中文:
实例 分解.baseChange
  签名: : 分解 fun i => (ℳ i).baseChange S
  定义体: by
  refine .ofLinearMap _ (lmap (ℳ · |>.toBaseChange S) ∘ₗ
    (directSumRight R S S fun i => ℳ i).toLinearMap ∘ₗ
    ((decomposeLinearEquiv ℳ).baseChange R S)) ?_ ?_
  · simp_rw [← comp_assoc]
    rw [← LinearEquiv.eq_comp_toLinearMap_symm]
    ext
    simp
  · ext : 1
    rw [← LinearMap.cancel_right ((ℳ _).toBaseChange_surjective S)]
    ext : 3
    simp

Depends on / 依赖: LinearEquiv, LinearEquiv.eq_comp_toLinearMap_symm, LinearMap, LinearMap.cancel_right, baseChange, cancel_right, comp_assoc, decomposeLinearEquiv, directSumRight, eq_comp_toLinearMap_symm, ofLinearMap, simp_rw, toBaseChange, toBaseChange_surjective, toLinearMap
-/
instance Decomposition.baseChange : Decomposition fun i => (ℳ i).baseChange S := by
  refine .ofLinearMap _ (lmap (ℳ · |>.toBaseChange S) ∘ₗ
    (directSumRight R S S fun i => ℳ i).toLinearMap ∘ₗ
    ((decomposeLinearEquiv ℳ).baseChange R S)) ?_ ?_
  · simp_rw [← comp_assoc]
    rw [← LinearEquiv.eq_comp_toLinearMap_symm]
    ext
    simp
  · ext : 1
    rw [← LinearMap.cancel_right ((ℳ _).toBaseChange_surjective S)]
    ext : 3
    simp

/--
theorem `toBaseChange_injective` / 定理 `toBaseChange_injective`

English:
theorem toBaseChange_injective
  given: (i : ι)
  statement: Function.Injective ((ℳ i).toBaseChange S)
  proof: fun x y h => by
  have := (Function.Bijective.of_comp_iff (lmap (ℳ · |>.toBaseChange S))
    (by rw [← LinearEquiv.coe_trans]; exact LinearEquiv.bijective _)).1
    (decompose (M := S otimes[R] M) fun i => (ℳ i).baseChange S).bijective
refine of_injective (β := fun i => S otimes[R] ℳ i) i this.injective ?_
  simpa using congr(of (fun i => (ℳ i).baseChange S) i $h)

中文:
定理 toBaseChange_injective
  条件: (i : ι)
  结论: 函数.单射 ((ℳ i).toBaseChange S)
  证明: fun x y h => by
  have := (Function.Bijective.of_comp_iff (lmap (ℳ · |>.toBaseChange S))
    (by rw [← LinearEquiv.coe_trans]; exact LinearEquiv.bijective _)).1
    (decompose (M := S otimes[R] M) fun i => (ℳ i).baseChange S).bijective
refine of_injective (β := fun i => S otimes[R] ℳ i) i this.injective ?_
  simpa using congr(of (fun i => (ℳ i).baseChange S) i $h)

Depends on / 依赖: Bijective, Function, Function.Bijective.of_comp_iff, LinearEquiv, LinearEquiv.bijective, LinearEquiv.coe_trans, baseChange, bijective, coe_trans, decompose, injective, of_comp_iff, of_injective, otimes, this.injective, toBaseChange
-/
theorem toBaseChange_injective (i : ι) : Function.Injective ((ℳ i).toBaseChange S) := fun x y h => by
  have := (Function.Bijective.of_comp_iff (lmap (ℳ · |>.toBaseChange S))
    (by rw [← LinearEquiv.coe_trans]; exact LinearEquiv.bijective _)).1
    (decompose (M := S otimes[R] M) fun i => (ℳ i).baseChange S).bijective
refine of_injective (β := fun i => S otimes[R] ℳ i) i this.injective ?_
  simpa using congr(of (fun i => (ℳ i).baseChange S) i $h)

/--
theorem `toBaseChange_bijective` / 定理 `toBaseChange_bijective`

English:
theorem toBaseChange_bijective
  given: (i : ι)
  statement: Function.Bijective ((ℳ i).toBaseChange S)
  proof: ⟨toBaseChange_injective ℳ i, (ℳ i).toBaseChange_surjective S⟩

中文:
定理 toBaseChange_bijective
  条件: (i : ι)
  结论: 函数.双射 ((ℳ i).toBaseChange S)
  证明: ⟨toBaseChange_injective ℳ i, (ℳ i).toBaseChange_surjective S⟩

Depends on / 依赖: toBaseChange_injective, toBaseChange_surjective
-/
theorem toBaseChange_bijective (i : ι) : Function.Bijective ((ℳ i).toBaseChange S) :=
  ⟨toBaseChange_injective ℳ i, (ℳ i).toBaseChange_surjective S⟩

end BaseChange

section TensorModule

variable (N : Type*) [AddCommMonoid N] [Module R N]

/--
Definition of `decomposeTensor` / `decomposeTensor` 的定义

English:
definition decomposeTensor
  signature: (i : ι)
  body: ((ℳ i).subtype.rTensor N).range

中文:
定义 decomposeTensor
  签名: (i : ι)
  定义体: ((ℳ i).subtype.rTensor N).range

Depends on / 依赖: rTensor, subtype, subtype.rTensor
-/
def decomposeTensor (i : ι) : Submodule R (M otimes[R] N) :=
  ((ℳ i).subtype.rTensor N).range

/--
lemma `decomposeTensor_apply` / 引理 `decomposeTensor_apply`

English:
lemma decomposeTensor_apply
  given: {i : ι}
  proof: Submodule.toSubMulAction_inj.mp rfl

中文:
引理 decomposeTensor_apply
  条件: {i : ι}
  证明: Submodule.toSubMulAction_inj.mp rfl

Depends on / 依赖: Submodule, Submodule.toSubMulAction_inj.mp, toSubMulAction_inj
-/
lemma decomposeTensor_apply {i : ι} :
    decomposeTensor ℳ N i = ((ℳ i).subtype.rTensor N).range :=
  Submodule.toSubMulAction_inj.mp rfl

variable [DecidableEq ι] [Decomposition ℳ]

/--
lemma `subtype_rTensor_injective` / 引理 `subtype_rTensor_injective`

English:
lemma subtype_rTensor_injective
  given: (i : ι)
  proof: injective_of_comp_eq_id ((ℳ i).subtype.rTensor N)
    ((component R ι (fun i => ℳ i) i ∘ₗ DirectSum.decomposeLinearEquiv ℳ).rTensor N)
    (by ext; simp)

中文:
引理 subtype_rTensor_injective
  条件: (i : ι)
  证明: injective_of_comp_eq_id ((ℳ i).subtype.rTensor N)
    ((component R ι (fun i => ℳ i) i ∘ₗ DirectSum.decomposeLinearEquiv ℳ).rTensor N)
    (by ext; simp)

Depends on / 依赖: DirectSum, DirectSum.decomposeLinearEquiv, component, decomposeLinearEquiv, injective_of_comp_eq_id, rTensor, subtype, subtype.rTensor
-/
lemma subtype_rTensor_injective (i : ι) :
    Function.Injective ((ℳ i).subtype.rTensor N) :=
  injective_of_comp_eq_id ((ℳ i).subtype.rTensor N)
    ((component R ι (fun i => ℳ i) i ∘ₗ DirectSum.decomposeLinearEquiv ℳ).rTensor N)
    (by ext; simp)

/--
Definition of `decomposeTensorEquiv` / `decomposeTensorEquiv` 的定义

English:
definition decomposeTensorEquiv
  signature: (i : ι)
  body: LinearEquiv.ofInjective ((ℳ i).subtype.rTensor N) (subtype_rTensor_injective ℳ N i)

中文:
定义 decomposeTensorEquiv
  签名: (i : ι)
  定义体: LinearEquiv.ofInjective ((ℳ i).subtype.rTensor N) (subtype_rTensor_injective ℳ N i)

Depends on / 依赖: LinearEquiv, LinearEquiv.ofInjective, ofInjective, rTensor, subtype, subtype.rTensor, subtype_rTensor_injective
-/
noncomputable def decomposeTensorEquiv (i : ι) :
    (ℳ i) otimes[R] N ≃ₗ[R] decomposeTensor ℳ N i :=
  LinearEquiv.ofInjective ((ℳ i).subtype.rTensor N) (subtype_rTensor_injective ℳ N i)

/--
lemma `decomposeTensorEquiv_apply` / 引理 `decomposeTensorEquiv_apply`

English:
lemma decomposeTensorEquiv_apply
  given: {i : ι} (x : (ℳ i) otimes[R] N)
  proof: by
  rfl

@[simp]

中文:
引理 decomposeTensorEquiv_apply
  条件: {i : ι} (x : (ℳ i) otimes[R] N)
  证明: by
  rfl

@[simp]
-/
lemma decomposeTensorEquiv_apply {i : ι} (x : (ℳ i) otimes[R] N) :
    decomposeTensorEquiv ℳ N i x =
      ⟨(ℳ i).subtype.rTensor N x, by convert (decomposeTensorEquiv ℳ N i x).property; rfl⟩ := by
  rfl

@[simp]
/--
lemma `val_decomposeTensorEquiv_apply` / 引理 `val_decomposeTensorEquiv_apply`

English:
lemma val_decomposeTensorEquiv_apply
  given: {i : ι} (x : (ℳ i) otimes[R] N)
  proof: by rfl

中文:
引理 val_decomposeTensorEquiv_apply
  条件: {i : ι} (x : (ℳ i) otimes[R] N)
  证明: by rfl
-/
lemma val_decomposeTensorEquiv_apply {i : ι} (x : (ℳ i) otimes[R] N) :
    decomposeTensorEquiv ℳ N i x = (ℳ i).subtype.rTensor N x := by rfl

/--
lemma `decomposeTensorEquiv_of_apply` / 引理 `decomposeTensorEquiv_of_apply`

English:
lemma decomposeTensorEquiv_of_apply
  given: {i : ι} (x : (ℳ i) otimes[R] N)
  proof: by
  ext; simp [coe_congrLinearEquiv]

中文:
引理 decomposeTensorEquiv_of_apply
  条件: {i : ι} (x : (ℳ i) otimes[R] N)
  证明: by
  ext; simp [coe_congrLinearEquiv]

Depends on / 依赖: coe_congrLinearEquiv
-/
lemma decomposeTensorEquiv_of_apply {i : ι} (x : (ℳ i) otimes[R] N) :
    congrLinearEquiv (fun i => decomposeTensorEquiv ℳ N i) (of (fun i => ↥(ℳ i) otimes[R] N) i x) =
      of (fun i => decomposeTensor ℳ N i) i (decomposeTensorEquiv ℳ N i x) := by
  ext; simp [coe_congrLinearEquiv]

/--
lemma `decomposeLinearEquiv_comp_subtype` / 引理 `decomposeLinearEquiv_comp_subtype`

English:
lemma decomposeLinearEquiv_comp_subtype
  given: {i : ι}
  proof: by
  ext; simp

中文:
引理 decomposeLinearEquiv_comp_subtype
  条件: {i : ι}
  证明: by
  ext; simp
-/
lemma decomposeLinearEquiv_comp_subtype {i : ι} :
    decomposeLinearEquiv ℳ ∘ₗ (ℳ i).subtype = lof R ι (fun i => ℳ i) i := by
  ext; simp

/--
lemma `coe_decomposeTensor_apply` / 引理 `coe_decomposeTensor_apply`

English:
lemma coe_decomposeTensor_apply
  given: (x : (⨁ i, decomposeTensor ℳ N i))
  proof: by
  rw [← LinearEquiv.symm_rTensor]; rw [LinearEquiv.eq_symm_apply]
  induction x using DirectSum.induction_on with
  | zero => simp
  | of i x =>
    obtain ⟨-, y, rfl⟩ := x
    have : (rTensor N (lof R ι (fun i => ℳ i) i)) y =
        (directSumLeft R R (fun i => ℳ i) N).symm ((of (fun i => ℳ i otimes[R] N) i) y) :=
      (TensorProduct.directSumLeft_symm_of R R (M₁ := fun i => ℳ i) y).symm
    rw [coeAddMonoidHom_of]; rw [LinearEquiv.eq_symm_apply]; rw [LinearEquiv.eq_symm_apply]; rw [← (LinearEquiv.rTensor N _).coe_coe]; rw [LinearEquiv.coe_rTensor]; rw [← rTensor_comp_apply]; rw [decomposeLinearEquiv_comp_subtype]; rw [this]; rw [LinearEquiv.apply_symm_apply]; rw [decomposeTensorEquiv_of_apply]; rw [decomposeTensorEquiv_apply]
  | add x y hx hy => simp [hx, hy]

中文:
引理 coe_decomposeTensor_apply
  条件: (x : (⨁ i, decomposeTensor ℳ N i))
  证明: by
  rw [← LinearEquiv.symm_rTensor]; rw [LinearEquiv.eq_symm_apply]
  induction x using DirectSum.induction_on with
  | zero => simp
  | of i x =>
    obtain ⟨-, y, rfl⟩ := x
    have : (rTensor N (lof R ι (fun i => ℳ i) i)) y =
        (directSumLeft R R (fun i => ℳ i) N).symm ((of (fun i => ℳ i otimes[R] N) i) y) :=
      (TensorProduct.directSumLeft_symm_of R R (M₁ := fun i => ℳ i) y).symm
    rw [coeAddMonoidHom_of]; rw [LinearEquiv.eq_symm_apply]; rw [LinearEquiv.eq_symm_apply]; rw [← (LinearEquiv.rTensor N _).coe_coe]; rw [LinearEquiv.coe_rTensor]; rw [← rTensor_comp_apply]; rw [decomposeLinearEquiv_comp_subtype]; rw [this]; rw [LinearEquiv.apply_symm_apply]; rw [decomposeTensorEquiv_of_apply]; rw [decomposeTensorEquiv_apply]
  | add x y hx hy => simp [hx, hy]

Depends on / 依赖: DirectSum, DirectSum.induction_on, LinearEquiv, LinearEquiv.eq_symm_apply, LinearEquiv.rTensor, LinearEquiv.symm_rTensor, TensorProduct, TensorProduct.directSumLeft_symm_of, coeAddMonoidHom_of, coe_coe, directSumLeft, directSumLeft_symm_of, eq_symm_apply, induction_on, otimes, rTensor, symm_rTensor
-/
lemma coe_decomposeTensor_apply (x : (⨁ i, decomposeTensor ℳ N i)) :
    DirectSum.coeAddMonoidHom (decomposeTensor ℳ N) x =
    (DirectSum.decomposeLinearEquiv ℳ).symm.rTensor N
    ((TensorProduct.directSumLeft R R (fun i => ℳ i) N).symm <|
      (DirectSum.congrLinearEquiv <| decomposeTensorEquiv ℳ N).symm x) := by
  rw [← LinearEquiv.symm_rTensor]; rw [LinearEquiv.eq_symm_apply]
  induction x using DirectSum.induction_on with
  | zero => simp
  | of i x =>
    obtain ⟨-, y, rfl⟩ := x
    have : (rTensor N (lof R ι (fun i => ℳ i) i)) y =
        (directSumLeft R R (fun i => ℳ i) N).symm ((of (fun i => ℳ i otimes[R] N) i) y) :=
      (TensorProduct.directSumLeft_symm_of R R (M₁ := fun i => ℳ i) y).symm
    rw [coeAddMonoidHom_of]; rw [LinearEquiv.eq_symm_apply]; rw [LinearEquiv.eq_symm_apply]; rw [← (LinearEquiv.rTensor N _).coe_coe]; rw [LinearEquiv.coe_rTensor]; rw [← rTensor_comp_apply]; rw [decomposeLinearEquiv_comp_subtype]; rw [this]; rw [LinearEquiv.apply_symm_apply]; rw [decomposeTensorEquiv_of_apply]; rw [decomposeTensorEquiv_apply]
  | add x y hx hy => simp [hx, hy]

/-- The decomposition of a tensor product induced by a decomposition of the left module. -/
@[reducible]
/--
Definition of `tensorDecomposition` / `tensorDecomposition` 的定义

English:
definition tensorDecomposition
  signature: (N : Type*) [AddCommGroup N] [Module R N]
  body: (DirectSum.congrLinearEquiv <| decomposeTensorEquiv ℳ N)
    (directSumLeft R R (fun i => ℳ i) N <| (DirectSum.decomposeLinearEquiv ℳ).rTensor N x)
  left_inv x := by simp [coe_decomposeTensor_apply ℳ N _, ← LinearEquiv.symm_rTensor]
  right_inv x := by simp [coe_decomposeTensor_apply ℳ N _, ← LinearEquiv.symm_rTensor]

中文:
定义 tensorDecomposition
  签名: (N : 类型) [加法交换群 N] [模 R N]
  定义体: (DirectSum.congrLinearEquiv <| decomposeTensorEquiv ℳ N)
    (directSumLeft R R (fun i => ℳ i) N <| (DirectSum.decomposeLinearEquiv ℳ).rTensor N x)
  left_inv x := by simp [coe_decomposeTensor_apply ℳ N _, ← LinearEquiv.symm_rTensor]
  right_inv x := by simp [coe_decomposeTensor_apply ℳ N _, ← LinearEquiv.symm_rTensor]

Depends on / 依赖: DirectSum, DirectSum.congrLinearEquiv, congrLinearEquiv, decomposeTensorEquiv
-/
noncomputable def tensorDecomposition (N : Type*) [AddCommGroup N] [Module R N] :
    DirectSum.Decomposition (decomposeTensor ℳ N) where
  decompose' x := (DirectSum.congrLinearEquiv <| decomposeTensorEquiv ℳ N)
    (directSumLeft R R (fun i => ℳ i) N <| (DirectSum.decomposeLinearEquiv ℳ).rTensor N x)
  left_inv x := by simp [coe_decomposeTensor_apply ℳ N _, ← LinearEquiv.symm_rTensor]
  right_inv x := by simp [coe_decomposeTensor_apply ℳ N _, ← LinearEquiv.symm_rTensor]

end TensorModule

namespace IsInternal

variable [DecidableEq ι] [CommSemiring S] [Algebra R S]

/--
theorem `baseChange` / 定理 `baseChange`

English:
theorem baseChange
  given: (hm : IsInternal ℳ)
  statement: IsInternal fun i => (ℳ i).baseChange S
  proof: haveI := hm.chooseDecomposition
  Decomposition.isInternal _

中文:
定理 baseChange
  条件: (hm : Is整数ernal ℳ)
  结论: Is整数ernal fun i => (ℳ i).baseChange S
  证明: haveI := hm.chooseDecomposition
  Decomposition.isInternal _

Depends on / 依赖: Decomposition, Decomposition.isInternal, chooseDecomposition, hm.chooseDecomposition, isInternal
-/
theorem baseChange (hm : IsInternal ℳ) : IsInternal fun i => (ℳ i).baseChange S :=
  haveI := hm.chooseDecomposition
  Decomposition.isInternal _

/--
theorem `toBaseChange_bijective` / 定理 `toBaseChange_bijective`

English:
theorem toBaseChange_bijective
  given: (hm : IsInternal ℳ) (i : ι)
  proof: haveI := hm.chooseDecomposition
  DirectSum.toBaseChange_bijective ℳ i

中文:
定理 toBaseChange_bijective
  条件: (hm : Is整数ernal ℳ) (i : ι)
  证明: haveI := hm.chooseDecomposition
  DirectSum.toBaseChange_bijective ℳ i

Depends on / 依赖: DirectSum, DirectSum.toBaseChange_bijective, chooseDecomposition, hm.chooseDecomposition, toBaseChange_bijective
-/
theorem toBaseChange_bijective (hm : IsInternal ℳ) (i : ι) :
    Function.Bijective ((ℳ i).toBaseChange S) :=
  haveI := hm.chooseDecomposition
  DirectSum.toBaseChange_bijective ℳ i

/--
theorem `toBaseChange_injective` / 定理 `toBaseChange_injective`

English:
theorem toBaseChange_injective
  given: (hm : IsInternal ℳ) (i : ι)
  proof: (toBaseChange_bijective ℳ hm i).injective

中文:
定理 toBaseChange_injective
  条件: (hm : Is整数ernal ℳ) (i : ι)
  证明: (toBaseChange_bijective ℳ hm i).injective

Depends on / 依赖: injective, toBaseChange_bijective
-/
theorem toBaseChange_injective (hm : IsInternal ℳ) (i : ι) :
    Function.Injective ((ℳ i).toBaseChange S) :=
  (toBaseChange_bijective ℳ hm i).injective

end IsInternal

end DirectSum
