/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Antoine Chambert-Loir
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# Base change properties

This file proves that several constructions in linear algebra
commute with base change, as expressed by `IsBaseChange`.

* `IsBaseChange.prodMap`, `IsBaseChange.pi`: binary and finite products.

In particular, localization of modules commutes with binary and finite products.

* `IsBaseChange.directSum`: base change for direct sums

* Homomorphism modules

-/

public section

variable {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]

namespace IsBaseChange

open TensorProduct

/--
lemma `prodMap` / 引理 `prodMap`

English:
lemma prodMap
  statement: {M N M' N' : Type*}
  proof: by
  apply of_equiv (prodRight R _ S M N ≪≫ₗ hf.equiv.prodCongr hg.equiv)
  intro p
  simp [equiv_tmul]

中文:
引理 prodMap
  结论: {M N M' N' : 类型}
  证明: by
  apply of_equiv (prodRight R _ S M N ≪≫ₗ hf.equiv.prodCongr hg.equiv)
  intro p
  simp [equiv_tmul]

Depends on / 依赖: equiv_tmul, hf.equiv.prodCongr, hg.equiv, of_equiv, prodCongr, prodRight
-/
lemma prodMap {M N M' N' : Type*}
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    [AddCommMonoid M'] [AddCommMonoid N'] [Module R M'] [Module R N']
    [Module S M'] [Module S N'] [IsScalarTower R S M'] [IsScalarTower R S N']
    (f : M ->ₗ[R] M') (g : N ->ₗ[R] N') (hf : IsBaseChange S f) (hg : IsBaseChange S g) :
    IsBaseChange S (f.prodMap g) := by
  apply of_equiv (prodRight R _ S M N ≪≫ₗ hf.equiv.prodCongr hg.equiv)
  intro p
  simp [equiv_tmul]

/--
lemma `pi` / 引理 `pi`

English:
lemma pi
  statement: {ι : Type*} [Finite ι]
  proof: by
  classical
  cases nonempty_fintype ι
apply of_equiv piRight R S _ M ≪≫ₗ .piCongrRight fun i => (hf i).equiv
  intro x
  ext i
  simp [equiv_tmul]

中文:
引理 pi
  结论: {ι : 类型} [有限 ι]
  证明: by
  classical
  cases nonempty_fintype ι
apply of_equiv piRight R S _ M ≪≫ₗ .piCongrRight fun i => (hf i).equiv
  intro x
  ext i
  simp [equiv_tmul]

Depends on / 依赖: classical, equiv_tmul, nonempty_fintype, of_equiv, piCongrRight, piRight
-/
lemma pi {ι : Type*} [Finite ι]
    {M M' : ι -> Type*} [forall i, AddCommMonoid (M i)] [forall i, AddCommMonoid (M' i)]
    [forall i, Module R (M i)] [forall i, Module R (M' i)] [forall i, Module S (M' i)]
    [forall i, IsScalarTower R S (M' i)]
    (f : forall i, M i ->ₗ[R] M' i) (hf : forall i, IsBaseChange S (f i)) :
    IsBaseChange S (.pi fun i => f i ∘ₗ .proj i) := by
  classical
  cases nonempty_fintype ι
apply of_equiv piRight R S _ M ≪≫ₗ .piCongrRight fun i => (hf i).equiv
  intro x
  ext i
  simp [equiv_tmul]

/--
theorem `finitePow` / 定理 `finitePow`

English:
theorem finitePow
  statement: (ι : Type*) [Finite ι]
  proof: IsBaseChange.pi (f := fun _ => f) (fun _ => hf)

中文:
定理 finitePow
  结论: (ι : 类型) [有限 ι]
  证明: IsBaseChange.pi (f := fun _ => f) (fun _ => hf)

Depends on / 依赖: IsBaseChange, IsBaseChange.pi
-/
theorem finitePow (ι : Type*) [Finite ι]
    {M M' : Type*} [AddCommMonoid M] [AddCommMonoid M']
    [Module R M] [Module R M'] [Module S M'] [IsScalarTower R S M']
    {f : M ->ₗ[R] M'} (hf : IsBaseChange S f) :
    IsBaseChange S (f.compLeft ι) :=
  IsBaseChange.pi (f := fun _ => f) (fun _ => hf)

end IsBaseChange

namespace IsLocalizedModule

variable (S : Submonoid R)

attribute [local instance] IsLocalizedModule.isScalarTower_module

/--
Instance `prodMap` / 实例 `prodMap`

English:
instance prodMap
  signature: {M N M' N' : Type*}
  body: by
  let : Module (Localization S) M' := IsLocalizedModule.module S f
  let : Module (Localization S) N' := IsLocalizedModule.module S g
  rw [isLocalizedModule_iff_isBaseChange S (Localization S)]
  apply IsBaseChange.prodMap
  · rw [← isLocalizedModule_iff_isBaseChange S]
    infer_instance
  · rw [← isLocalizedModule_iff_isBaseChange S]
    infer_instance

中文:
实例 prodMap
  签名: {M N M' N' : 类型}
  定义体: by
  let : Module (Localization S) M' := IsLocalizedModule.module S f
  let : Module (Localization S) N' := IsLocalizedModule.module S g
  rw [isLocalizedModule_iff_isBaseChange S (Localization S)]
  apply IsBaseChange.prodMap
  · rw [← isLocalizedModule_iff_isBaseChange S]
    infer_instance
  · rw [← isLocalizedModule_iff_isBaseChange S]
    infer_instance

Depends on / 依赖: IsBaseChange, IsBaseChange.prodMap, IsLocalizedModule, IsLocalizedModule.module, Localization, Module, infer_instance, isLocalizedModule_iff_isBaseChange, module, prodMap
-/
instance prodMap {M N M' N' : Type*}
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    [AddCommMonoid M'] [AddCommMonoid N'] [Module R M'] [Module R N']
    (f : M ->ₗ[R] M') (g : N ->ₗ[R] N')
    [IsLocalizedModule S f] [IsLocalizedModule S g] :
    IsLocalizedModule S (f.prodMap g) := by
  let : Module (Localization S) M' := IsLocalizedModule.module S f
  let : Module (Localization S) N' := IsLocalizedModule.module S g
  rw [isLocalizedModule_iff_isBaseChange S (Localization S)]
  apply IsBaseChange.prodMap
  · rw [← isLocalizedModule_iff_isBaseChange S]
    infer_instance
  · rw [← isLocalizedModule_iff_isBaseChange S]
    infer_instance

/--
Instance `pi` / 实例 `pi`

English:
instance pi
  signature: {ι : Type*} [Finite ι]
  body: by
  let (i : ι) : Module (Localization S) (M' i) := IsLocalizedModule.module S (f i)
  rw [isLocalizedModule_iff_isBaseChange S (Localization S)]
  apply IsBaseChange.pi
  intro i
  rw [← isLocalizedModule_iff_isBaseChange S]
  infer_instance

中文:
实例 pi
  签名: {ι : 类型} [有限 ι]
  定义体: by
  let (i : ι) : Module (Localization S) (M' i) := IsLocalizedModule.module S (f i)
  rw [isLocalizedModule_iff_isBaseChange S (Localization S)]
  apply IsBaseChange.pi
  intro i
  rw [← isLocalizedModule_iff_isBaseChange S]
  infer_instance

Depends on / 依赖: IsBaseChange, IsBaseChange.pi, IsLocalizedModule, IsLocalizedModule.module, Localization, Module, infer_instance, isLocalizedModule_iff_isBaseChange, module
-/
instance pi {ι : Type*} [Finite ι]
    {M M' : ι -> Type*} [forall i, AddCommMonoid (M i)] [forall i, AddCommMonoid (M' i)]
    [forall i, Module R (M i)] [forall i, Module R (M' i)]
    (f : forall i, M i ->ₗ[R] M' i) [forall i, IsLocalizedModule S (f i)] :
    IsLocalizedModule S (.pi fun i => f i ∘ₗ .proj i) := by
  let (i : ι) : Module (Localization S) (M' i) := IsLocalizedModule.module S (f i)
  rw [isLocalizedModule_iff_isBaseChange S (Localization S)]
  apply IsBaseChange.pi
  intro i
  rw [← isLocalizedModule_iff_isBaseChange S]
  infer_instance

end IsLocalizedModule

namespace IsBaseChange

section DirectSum

open TensorProduct LinearMap DirectSum

variable {ι : Type*}
    {N : ι -> Type*} [(i : ι) -> AddCommMonoid (N i)] [(i : ι) -> Module R (N i)]
    {P : ι -> Type*} [forall i, AddCommMonoid (P i)] [forall i, Module R (P i)]
    [forall i, Module S (P i)] [forall i, IsScalarTower R S (P i)]
    {ε : (i : ι) -> N i ->ₗ[R] P i}

/--
theorem `directSum` / 定理 `directSum`

English:
theorem directSum
  given: (ibc : forall i, IsBaseChange S (ε i))
  proof: by
  classical
apply of_equiv directSumRight R S S N ≪≫ₗ congrLinearEquiv fun i => (ibc i).equiv
  intros; ext
  simp [coe_directSumRight, coe_congrLinearEquiv, equiv_tmul]

中文:
定理 directSum
  条件: (ibc : 对任意 i, IsBaseChange S (ε i))
  证明: by
  classical
apply of_equiv directSumRight R S S N ≪≫ₗ congrLinearEquiv fun i => (ibc i).equiv
  intros; ext
  simp [coe_directSumRight, coe_congrLinearEquiv, equiv_tmul]

Depends on / 依赖: classical, coe_congrLinearEquiv, coe_directSumRight, congrLinearEquiv, directSumRight, equiv_tmul, intros, of_equiv
-/
theorem directSum (ibc : forall i, IsBaseChange S (ε i)) :
    IsBaseChange S (lmap ε) := by
  classical
apply of_equiv directSumRight R S S N ≪≫ₗ congrLinearEquiv fun i => (ibc i).equiv
  intros; ext
  simp [coe_directSumRight, coe_congrLinearEquiv, equiv_tmul]

variable (ι)
    {M M' : Type*} [AddCommMonoid M] [AddCommMonoid M']
    [Module R M] [Module R M'] [Module S M'] [IsScalarTower R S M']
    {ε : M ->ₗ[R] M'}

/--
theorem `directSumPow` / 定理 `directSumPow`

English:
theorem directSumPow
  given: (ibc : IsBaseChange S ε)
  proof: directSum (fun _ : ι => ibc)

中文:
定理 directSumPow
  条件: (ibc : IsBaseChange S ε)
  证明: directSum (fun _ : ι => ibc)

Depends on / 依赖: directSum
-/
theorem directSumPow (ibc : IsBaseChange S ε) :
    IsBaseChange S (lmap fun _ : ι => ε) :=
  directSum (fun _ : ι => ibc)

/--
theorem `finsuppPow` / 定理 `finsuppPow`

English:
theorem finsuppPow
  given: (ibc : IsBaseChange S ε)
  proof: by
  classical
apply of_equiv
    LinearEquiv.baseChange R S _ _ (finsuppLEquivDirectSum ..) ≪≫ₗ
      (directSum (fun _ => ibc)).equiv ≪≫ₗ (finsuppLEquivDirectSum ..).symm
  intro x
  rw [LinearEquiv.trans_apply]; rw [Finsupp.mapRange.linearMap_apply]; rw [LinearEquiv.symm_apply_eq]
  ext
  simp [LinearEquiv.baseChange_tmul, IsBaseChange.equiv_tmul, lmap_finsuppLEquivDirectSum_eq]

中文:
定理 finsuppPow
  条件: (ibc : IsBaseChange S ε)
  证明: by
  classical
apply of_equiv
    LinearEquiv.baseChange R S _ _ (finsuppLEquivDirectSum ..) ≪≫ₗ
      (directSum (fun _ => ibc)).equiv ≪≫ₗ (finsuppLEquivDirectSum ..).symm
  intro x
  rw [LinearEquiv.trans_apply]; rw [Finsupp.mapRange.linearMap_apply]; rw [LinearEquiv.symm_apply_eq]
  ext
  simp [LinearEquiv.baseChange_tmul, IsBaseChange.equiv_tmul, lmap_finsuppLEquivDirectSum_eq]

Depends on / 依赖: Finsupp, Finsupp.mapRange.linearMap_apply, IsBaseChange, IsBaseChange.equiv_tmul, LinearEquiv, LinearEquiv.baseChange, LinearEquiv.baseChange_tmul, LinearEquiv.symm_apply_eq, LinearEquiv.trans_apply, baseChange, baseChange_tmul, classical, directSum, equiv_tmul, finsuppLEquivDirectSum, linearMap_apply, lmap_finsuppLEquivDirectSum_eq, mapRange, of_equiv, symm_apply_eq
-/
theorem finsuppPow (ibc : IsBaseChange S ε) :
    IsBaseChange S (Finsupp.mapRange.linearMap (α := ι) ε) := by
  classical
apply of_equiv
    LinearEquiv.baseChange R S _ _ (finsuppLEquivDirectSum ..) ≪≫ₗ
      (directSum (fun _ => ibc)).equiv ≪≫ₗ (finsuppLEquivDirectSum ..).symm
  intro x
  rw [LinearEquiv.trans_apply]; rw [Finsupp.mapRange.linearMap_apply]; rw [LinearEquiv.symm_apply_eq]
  ext
  simp [LinearEquiv.baseChange_tmul, IsBaseChange.equiv_tmul, lmap_finsuppLEquivDirectSum_eq]

end DirectSum

end IsBaseChange
