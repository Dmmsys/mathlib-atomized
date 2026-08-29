/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.DirectSum.Finsupp

/-! # Base change of a free module

* `IsBaseChange.basis` : the natural basis of the base change of a module with a basis

* `IsBaseChange.free` : a base change of a free module is free.

-/

@[expose] public section

namespace IsBaseChange

variable {R : Type*} [CommSemiring R]
    {S : Type*} [CommSemiring S] [Algebra R S]
    {V : Type*} [AddCommMonoid V] [Module R V]
    {W : Type*} [AddCommMonoid W] [Module R W] [Module S W] [IsScalarTower R S W]
    {ι : Type*}
    {ε : V ->ₗ[R] W}

variable (b : Module.Basis ι R V) (ibc : IsBaseChange S ε)

/--
Definition of `basis` / `basis` 的定义

English:
definition basis
  signature: :
  body: (ibc.equiv.symm.trans (b.repr.baseChange R S _ _)).trans
      (finsuppPow ι (linearMap R S)).equiv

中文:
定义 basis
  签名: :
  定义体: (ibc.equiv.symm.trans (b.repr.baseChange R S _ _)).trans
      (finsuppPow ι (linearMap R S)).equiv

Depends on / 依赖: b.repr.baseChange, baseChange, ibc.equiv.symm.trans
-/
noncomputable def basis :
    Module.Basis ι S W where
  repr := (ibc.equiv.symm.trans (b.repr.baseChange R S _ _)).trans
      (finsuppPow ι (linearMap R S)).equiv

/--
theorem `basis_apply` / 定理 `basis_apply`

English:
theorem basis_apply
  given: (i)
  statement: ibc.basis b i = ε (b i)
  proof: by
  simp only [basis, LinearEquiv.baseChange, Module.Basis.coe_ofRepr, LinearEquiv.trans_symm,
    LinearEquiv.symm_symm, LinearEquiv.trans_apply]
  generalize_proofs _ _ _ _ ibcRA
  have : ibcRA.equiv.symm (Finsupp.single i 1) = 1 otimesₜ (Finsupp.single i 1) := by
    simp [LinearEquiv.symm_apply_eq, IsBaseChange.equiv_tmul]
  simp [this, IsBaseChange.equiv_tmul]

中文:
定理 basis_apply
  条件: (i)
  结论: ibc.basis b i = ε (b i)
  证明: by
  simp only [basis, LinearEquiv.baseChange, Module.Basis.coe_ofRepr, LinearEquiv.trans_symm,
    LinearEquiv.symm_symm, LinearEquiv.trans_apply]
  generalize_proofs _ _ _ _ ibcRA
  have : ibcRA.equiv.symm (Finsupp.single i 1) = 1 otimesₜ (Finsupp.single i 1) := by
    simp [LinearEquiv.symm_apply_eq, IsBaseChange.equiv_tmul]
  simp [this, IsBaseChange.equiv_tmul]

Depends on / 依赖: Finsupp, Finsupp.single, IsBaseChange, IsBaseChange.equiv_tmul, LinearEquiv, LinearEquiv.baseChange, LinearEquiv.symm_apply_eq, LinearEquiv.symm_symm, LinearEquiv.trans_apply, LinearEquiv.trans_symm, Module, Module.Basis.coe_ofRepr, baseChange, coe_ofRepr, equiv_tmul, generalize_proofs, ibcRA.equiv.symm, single, symm_apply_eq, symm_symm
-/
theorem basis_apply (i) : ibc.basis b i = ε (b i) := by
  simp only [basis, LinearEquiv.baseChange, Module.Basis.coe_ofRepr, LinearEquiv.trans_symm,
    LinearEquiv.symm_symm, LinearEquiv.trans_apply]
  generalize_proofs _ _ _ _ ibcRA
  have : ibcRA.equiv.symm (Finsupp.single i 1) = 1 otimesₜ (Finsupp.single i 1) := by
    simp [LinearEquiv.symm_apply_eq, IsBaseChange.equiv_tmul]
  simp [this, IsBaseChange.equiv_tmul]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `basis_repr_comp_apply` / 定理 `basis_repr_comp_apply`

English:
theorem basis_repr_comp_apply
  given: (v i)
  proof: by
  conv_lhs => rw [← b.linearCombination_repr v, Finsupp.linearCombination_apply,
    map_finsuppSum, map_finsuppSum]
  simp only [map_smul, Finsupp.sum_apply]
  rw [Finsupp.sum_eq_single i]
  · rw [← IsScalarTower.algebraMap_smul S (b.repr v i) (ε (b i)),
      map_smul, ← ibc.basis_apply]
    simp [Finsupp.single_eq_same, Algebra.algebraMap_eq_smul_one]
  · intro i' _ h
    rw [← IsScalarTower.algebraMap_smul S (b.repr v i') (ε (b i'))]; rw [map_smul]; rw [← ibc.basis_apply]
    simp [Finsupp.single_eq_of_ne (Ne.symm h)]
  · simp

中文:
定理 basis_repr_comp_apply
  条件: (v i)
  证明: by
  conv_lhs => rw [← b.linearCombination_repr v, Finsupp.linearCombination_apply,
    map_finsuppSum, map_finsuppSum]
  simp only [map_smul, Finsupp.sum_apply]
  rw [Finsupp.sum_eq_single i]
  · rw [← IsScalarTower.algebraMap_smul S (b.repr v i) (ε (b i)),
      map_smul, ← ibc.basis_apply]
    simp [Finsupp.single_eq_same, Algebra.algebraMap_eq_smul_one]
  · intro i' _ h
    rw [← IsScalarTower.algebraMap_smul S (b.repr v i') (ε (b i'))]; rw [map_smul]; rw [← ibc.basis_apply]
    simp [Finsupp.single_eq_of_ne (Ne.symm h)]
  · simp

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, Finsupp, Finsupp.linearCombination_apply, Finsupp.single_eq_of_ne, Finsupp.single_eq_same, Finsupp.sum_apply, Finsupp.sum_eq_single, IsScalarTower, IsScalarTower.algebraMap_smul, Ne.symm, algebraMap_eq_smul_one, algebraMap_smul, b.linearCombination_repr, b.repr, basis_apply, conv_lhs, ibc.basis_apply, linearCombination_apply, linearCombination_repr
-/
theorem basis_repr_comp_apply (v i) :
    (ibc.basis b).repr (ε v) i = algebraMap R S (b.repr v i) := by
  conv_lhs => rw [← b.linearCombination_repr v, Finsupp.linearCombination_apply,
    map_finsuppSum, map_finsuppSum]
  simp only [map_smul, Finsupp.sum_apply]
  rw [Finsupp.sum_eq_single i]
  · rw [← IsScalarTower.algebraMap_smul S (b.repr v i) (ε (b i)),
      map_smul, ← ibc.basis_apply]
    simp [Finsupp.single_eq_same, Algebra.algebraMap_eq_smul_one]
  · intro i' _ h
    rw [← IsScalarTower.algebraMap_smul S (b.repr v i') (ε (b i'))]; rw [map_smul]; rw [← ibc.basis_apply]
    simp [Finsupp.single_eq_of_ne (Ne.symm h)]
  · simp

/--
theorem `basis_repr_comp` / 定理 `basis_repr_comp`

English:
theorem basis_repr_comp
  given: (v : V)
  proof: by
  ext i
  simp [basis_repr_comp_apply]

include ibc in

中文:
定理 basis_repr_comp
  条件: (v : V)
  证明: by
  ext i
  simp [basis_repr_comp_apply]

include ibc in

Depends on / 依赖: basis_repr_comp_apply
-/
theorem basis_repr_comp (v : V) :
    (ibc.basis b).repr (ε v) =
      Finsupp.mapRange.linearMap (Algebra.linearMap R S) (b.repr v) := by
  ext i
  simp [basis_repr_comp_apply]

include ibc in
/--
theorem `free` / 定理 `free`

English:
theorem free
  given: [Module.Free R V]
  statement: Module.Free S W
  proof: Module.Free.of_basis (ibc.basis (Module.Free.chooseBasis R V))

中文:
定理 free
  条件: [模.自由 R V]
  结论: 模.自由 S W
  证明: Module.Free.of_basis (ibc.basis (Module.Free.chooseBasis R V))

Depends on / 依赖: Module, Module.Free.chooseBasis, Module.Free.of_basis, chooseBasis, ibc.basis, of_basis
-/
theorem free [Module.Free R V] : Module.Free S W :=
  Module.Free.of_basis (ibc.basis (Module.Free.chooseBasis R V))

end IsBaseChange

section underring

namespace IsBaseChange

open TensorProduct

variable {R : Type*} [CommSemiring R]
  {V : Type*} [AddCommMonoid V] [Module R V]
  (A : Type*) [CommSemiring A] [Algebra A R]
  [Module A V] [IsScalarTower A R V]

open TensorProduct

variable {ι : Type*} (b : Module.Basis ι R V)

/--
theorem `of_basis` / 定理 `of_basis`

English:
theorem of_basis
  statement: IsBaseChange R (Finsupp.linearCombination A b)
  proof: by
  classical
  let j := TensorProduct.finsuppScalarRight A R R ι
  refine of_equiv ?_ ?_
  · apply LinearEquiv.ofBijective (Finsupp.linearCombination R b ∘ₗ j)
    rw [LinearMap.coe_comp]; rw [LinearEquiv.coe_toLinearMap]; rw [j.bijective.of_comp_iff]
    simp [Function.Bijective,
        ← span_range_eq_top_iff_surjective_finsuppLinearCombination,
        ← linearIndependent_iff_injective_finsuppLinearCombination,
        Module.Basis.span_eq, b.linearIndependent]
  · intro x
    suffices (j (1 otimesₜ[A] x)) = x.mapRange (algebraMap A R) (by simp) by
      simp [this, Finsupp.linearCombination_apply, Finsupp.sum_mapRange_index]
    ext i
    simp [j, Algebra.algebraMap_eq_smul_one]

include A in

中文:
定理 of_basis
  结论: IsBaseChange R (有限支撑.linearCombination A b)
  证明: by
  classical
  let j := TensorProduct.finsuppScalarRight A R R ι
  refine of_equiv ?_ ?_
  · apply LinearEquiv.ofBijective (Finsupp.linearCombination R b ∘ₗ j)
    rw [LinearMap.coe_comp]; rw [LinearEquiv.coe_toLinearMap]; rw [j.bijective.of_comp_iff]
    simp [Function.Bijective,
        ← span_range_eq_top_iff_surjective_finsuppLinearCombination,
        ← linearIndependent_iff_injective_finsuppLinearCombination,
        Module.Basis.span_eq, b.linearIndependent]
  · intro x
    suffices (j (1 otimesₜ[A] x)) = x.mapRange (algebraMap A R) (by simp) by
      simp [this, Finsupp.linearCombination_apply, Finsupp.sum_mapRange_index]
    ext i
    simp [j, Algebra.algebraMap_eq_smul_one]

include A in

Depends on / 依赖: Bijective, Finsupp, Finsupp.linearCombination, Function, Function.Bijective, LinearEquiv, LinearEquiv.coe_toLinearMap, LinearEquiv.ofBijective, LinearMap, LinearMap.coe_comp, Module, Module.Basis.span_eq, TensorProduct, TensorProduct.finsuppScalarRight, algebraMap, b.linearIndependent, bijective, classical, coe_comp, coe_toLinearMap
-/
theorem of_basis : IsBaseChange R (Finsupp.linearCombination A b) := by
  classical
  let j := TensorProduct.finsuppScalarRight A R R ι
  refine of_equiv ?_ ?_
  · apply LinearEquiv.ofBijective (Finsupp.linearCombination R b ∘ₗ j)
    rw [LinearMap.coe_comp]; rw [LinearEquiv.coe_toLinearMap]; rw [j.bijective.of_comp_iff]
    simp [Function.Bijective,
        ← span_range_eq_top_iff_surjective_finsuppLinearCombination,
        ← linearIndependent_iff_injective_finsuppLinearCombination,
        Module.Basis.span_eq, b.linearIndependent]
  · intro x
    suffices (j (1 otimesₜ[A] x)) = x.mapRange (algebraMap A R) (by simp) by
      simp [this, Finsupp.linearCombination_apply, Finsupp.sum_mapRange_index]
    ext i
    simp [j, Algebra.algebraMap_eq_smul_one]

include A in
/--
theorem `of_fintype_basis` / 定理 `of_fintype_basis`

English:
theorem of_fintype_basis
  given: [Fintype ι]
  proof: by
  have : DecidableEq ι := Classical.typeDecidableEq ι
  let j : R otimes[A] (ι -> A) ≃ₗ[R] ι -> R := piScalarRight A R R ι
  refine of_equiv ?_ ?_
  · apply LinearEquiv.ofBijective (Fintype.linearCombination R b ∘ₗ j)
    rw [LinearMap.coe_comp]; rw [LinearEquiv.coe_toLinearMap]; rw [j.bijective.of_comp_iff]
    simp [Function.Bijective,
        ← span_range_eq_top_iff_surjective_fintypeLinearCombination,
        ← linearIndependent_iff_injective_fintypeLinearCombination,
        Module.Basis.span_eq, b.linearIndependent]
  · intro x
    -- simp? [Fintype.linearCombination_apply] says:
    simp only [LinearEquiv.ofBijective_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
      Function.comp_apply, Fintype.linearCombination_apply]
    congr
    ext i
    rw [TensorProduct.piScalarRight_apply]; rw [TensorProduct.piScalarRightHom_tmul]
    simp

中文:
定理 of_fintype_basis
  条件: [有限类型 ι]
  证明: by
  have : DecidableEq ι := Classical.typeDecidableEq ι
  let j : R otimes[A] (ι -> A) ≃ₗ[R] ι -> R := piScalarRight A R R ι
  refine of_equiv ?_ ?_
  · apply LinearEquiv.ofBijective (Fintype.linearCombination R b ∘ₗ j)
    rw [LinearMap.coe_comp]; rw [LinearEquiv.coe_toLinearMap]; rw [j.bijective.of_comp_iff]
    simp [Function.Bijective,
        ← span_range_eq_top_iff_surjective_fintypeLinearCombination,
        ← linearIndependent_iff_injective_fintypeLinearCombination,
        Module.Basis.span_eq, b.linearIndependent]
  · intro x
    -- simp? [Fintype.linearCombination_apply] says:
    simp only [LinearEquiv.ofBijective_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
      Function.comp_apply, Fintype.linearCombination_apply]
    congr
    ext i
    rw [TensorProduct.piScalarRight_apply]; rw [TensorProduct.piScalarRightHom_tmul]
    simp

Depends on / 依赖: Bijective, Classical, Classical.typeDecidableEq, DecidableEq, Fintype, Fintype.linearCombination, Function, Function.Bijective, LinearEquiv, LinearEquiv.coe_toLinearMap, LinearEquiv.ofBijective, LinearMap, LinearMap.coe_comp, Module, Module.Basis.span_eq, b.linearIndependent, bijective, coe_comp, coe_toLinearMap, j.bijective.of_comp_iff
-/
theorem of_fintype_basis [Fintype ι] :
    IsBaseChange R (Fintype.linearCombination A b) := by
  have : DecidableEq ι := Classical.typeDecidableEq ι
  let j : R otimes[A] (ι -> A) ≃ₗ[R] ι -> R := piScalarRight A R R ι
  refine of_equiv ?_ ?_
  · apply LinearEquiv.ofBijective (Fintype.linearCombination R b ∘ₗ j)
    rw [LinearMap.coe_comp]; rw [LinearEquiv.coe_toLinearMap]; rw [j.bijective.of_comp_iff]
    simp [Function.Bijective,
        ← span_range_eq_top_iff_surjective_fintypeLinearCombination,
        ← linearIndependent_iff_injective_fintypeLinearCombination,
        Module.Basis.span_eq, b.linearIndependent]
  · intro x
    -- simp? [Fintype.linearCombination_apply] says:
    simp only [LinearEquiv.ofBijective_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
      Function.comp_apply, Fintype.linearCombination_apply]
    congr
    ext i
    rw [TensorProduct.piScalarRight_apply]; rw [TensorProduct.piScalarRightHom_tmul]
    simp

variable {A b} in
/--
theorem `of_fintype_basis_eq` / 定理 `of_fintype_basis_eq`

English:
theorem of_fintype_basis_eq
  given: [Fintype ι] {a : ι -> A} {v : V}
  proof: by
  rw [← LinearEquiv.symm_apply_eq]
  rw [Fintype.linearCombination_apply]; rw [b.equivFun_symm_apply]
  simp

中文:
定理 of_fintype_basis_eq
  条件: [有限类型 ι] {a : ι -> A} {v : V}
  证明: by
  rw [← LinearEquiv.symm_apply_eq]
  rw [Fintype.linearCombination_apply]; rw [b.equivFun_symm_apply]
  simp

Depends on / 依赖: Fintype, Fintype.linearCombination_apply, LinearEquiv, LinearEquiv.symm_apply_eq, b.equivFun_symm_apply, equivFun_symm_apply, linearCombination_apply, symm_apply_eq
-/
theorem of_fintype_basis_eq [Fintype ι] {a : ι -> A} {v : V} :
    (Fintype.linearCombination A b) a = v ↔
      algebraMap A R ∘ a = b.equivFun v := by
  rw [← LinearEquiv.symm_apply_eq]
  rw [Fintype.linearCombination_apply]; rw [b.equivFun_symm_apply]
  simp

end IsBaseChange

end underring
