/-
Copyright (c) 2021 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Eric Wieser, Daniel Morrison
-/
module

public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Multilinear.Finsupp

/-!
# Multilinear maps in relation to bases.

This file proves lemmas about the action of multilinear maps on basis vectors and constructs a
basis for multilinear maps given bases on the domain and codomain.

-/

@[expose] public section


open MultilinearMap

variable {ι R : Type*} [CommSemiring R]
  {M : ι -> Type*} [forall i, AddCommMonoid (M i)] [forall i, Module R (M i)]
  {N : Type*} [AddCommMonoid N] [Module R N]

/--
theorem `Module.Basis.ext_multilinear` / 定理 `Module.Basis.ext_multilinear`

English:
theorem Module.Basis.ext_multilinear
  statement: [Finite ι] {f g : MultilinearMap R M N} {ιM : ι -> Type*}
  proof: by
  cases nonempty_fintype ι
  classical
  ext m
  rcases Function.Surjective.piMap (fun i => (e i).repr.symm.surjective) m with ⟨x, rfl⟩
  unfold Pi.map
  simp_rw [(e _).repr_symm_apply, Finsupp.linearCombination_apply, Finsupp.sum,
    map_sum_finset, map_smul_univ, h]

中文:
定理 模.基.ext_multilinear
  结论: [有限 ι] {f g : 多重线性映射 R M N} {ιM : ι -> 类型}
  证明: by
  cases nonempty_fintype ι
  classical
  ext m
  rcases Function.Surjective.piMap (fun i => (e i).repr.symm.surjective) m with ⟨x, rfl⟩
  unfold Pi.map
  simp_rw [(e _).repr_symm_apply, Finsupp.linearCombination_apply, Finsupp.sum,
    map_sum_finset, map_smul_univ, h]

Depends on / 依赖: Finsupp, Finsupp.linearCombination_apply, Finsupp.sum, Function, Function.Surjective.piMap, Pi.map, Surjective, classical, linearCombination_apply, map_smul_univ, map_sum_finset, nonempty_fintype, repr.symm.surjective, repr_symm_apply, simp_rw, surjective
-/
theorem Module.Basis.ext_multilinear [Finite ι] {f g : MultilinearMap R M N} {ιM : ι -> Type*}
    (e : forall i, Basis (ιM i) R (M i))
    (h : forall v : (i : ι) -> ιM i, (f fun i => e i (v i)) = g fun i => e i (v i)) : f = g := by
  cases nonempty_fintype ι
  classical
  ext m
  rcases Function.Surjective.piMap (fun i => (e i).repr.symm.surjective) m with ⟨x, rfl⟩
  unfold Pi.map
  simp_rw [(e _).repr_symm_apply, Finsupp.linearCombination_apply, Finsupp.sum,
    map_sum_finset, map_smul_univ, h]

namespace Basis

open Module

variable {κ : ι -> Type*} (b : (i : ι) -> Basis (κ i) R (M i))
  {ι' N : Type*} [AddCommMonoid N] [Module R N] (b' : Basis ι' R N)

open scoped Classical in
/--
Definition of `multilinearMap` / `multilinearMap` 的定义

English:
definition multilinearMap
  signature: [Finite ι] [forall i, Finite (κ i)]
  body: have : Fintype ι := Fintype.ofFinite _
    have (i : ι) : Fintype (κ i) := Fintype.ofFinite _
    LinearEquiv.multilinearMapCongrLeft (fun i => (b i).repr.symm) ≪≫ₗ
      (b'.repr).multilinearMapCongrRight R ≪≫ₗ freeFinsuppEquiv.symm

中文:
定义 multilinearMap
  签名: [有限 ι] [对任意 i, 有限 (κ i)]
  定义体: have : Fintype ι := Fintype.ofFinite _
    have (i : ι) : Fintype (κ i) := Fintype.ofFinite _
    LinearEquiv.multilinearMapCongrLeft (fun i => (b i).repr.symm) ≪≫ₗ
      (b'.repr).multilinearMapCongrRight R ≪≫ₗ freeFinsuppEquiv.symm

Depends on / 依赖: Fintype, Fintype.ofFinite, LinearEquiv, LinearEquiv.multilinearMapCongrLeft, freeFinsuppEquiv, freeFinsuppEquiv.symm, multilinearMapCongrLeft, multilinearMapCongrRight, ofFinite, repr.symm
-/
noncomputable def multilinearMap [Finite ι] [forall i, Finite (κ i)] :
    Basis ((Π i, κ i) × ι') R (MultilinearMap R M N) where
  repr :=
    have : Fintype ι := Fintype.ofFinite _
    have (i : ι) : Fintype (κ i) := Fintype.ofFinite _
    LinearEquiv.multilinearMapCongrLeft (fun i => (b i).repr.symm) ≪≫ₗ
      (b'.repr).multilinearMapCongrRight R ≪≫ₗ freeFinsuppEquiv.symm

variable [Fintype ι] [forall i, Finite (κ i)]

/--
theorem `multilinearMap_apply` / 定理 `multilinearMap_apply`

English:
theorem multilinearMap_apply
  given: (i : (Π i, κ i) × ι')
  proof: by
  ext x
  simp +instances only [multilinearMap, Basis.coe_ofRepr, LinearEquiv.trans_symm,
    LinearEquiv.symm_symm, LinearEquiv.trans_apply, LinearEquiv.multilinearMapCongrRight_symm_apply,
    Basis.coe_repr_symm, LinearEquiv.multilinearMapCongrLeft_symm_apply, compLinearMap_apply,
    LinearEquiv.coe_coe, LinearMap.compMultilinearMap_apply, freeFinsuppEquiv_single, one_smul,
    Finsupp.linearCombination_single, Basis.coord_apply, mkPiRing_apply, smul_eq_mul, mul_one,
    LinearMap.coe_smulRight, LinearMap.id_coe, id_eq, Subsingleton.elim (Fintype.ofFinite ι)]

中文:
定理 multilinearMap_apply
  条件: (i : (Π i, κ i) × ι')
  证明: by
  ext x
  simp +instances only [multilinearMap, Basis.coe_ofRepr, LinearEquiv.trans_symm,
    LinearEquiv.symm_symm, LinearEquiv.trans_apply, LinearEquiv.multilinearMapCongrRight_symm_apply,
    Basis.coe_repr_symm, LinearEquiv.multilinearMapCongrLeft_symm_apply, compLinearMap_apply,
    LinearEquiv.coe_coe, LinearMap.compMultilinearMap_apply, freeFinsuppEquiv_single, one_smul,
    Finsupp.linearCombination_single, Basis.coord_apply, mkPiRing_apply, smul_eq_mul, mul_one,
    LinearMap.coe_smulRight, LinearMap.id_coe, id_eq, Subsingleton.elim (Fintype.ofFinite ι)]

Depends on / 依赖: compMultilinearMap, smulRight
-/
theorem multilinearMap_apply (i : (Π i, κ i) × ι') :
    Basis.multilinearMap b b' i =
      ((LinearMap.id (M := R)).smulRight (b' i.2)).compMultilinearMap
        (MultilinearMap.mkPiRing R ι 1 |>.compLinearMap fun i' => (b i').coord (i.1 i')) := by
  ext x
  simp +instances only [multilinearMap, Basis.coe_ofRepr, LinearEquiv.trans_symm,
    LinearEquiv.symm_symm, LinearEquiv.trans_apply, LinearEquiv.multilinearMapCongrRight_symm_apply,
    Basis.coe_repr_symm, LinearEquiv.multilinearMapCongrLeft_symm_apply, compLinearMap_apply,
    LinearEquiv.coe_coe, LinearMap.compMultilinearMap_apply, freeFinsuppEquiv_single, one_smul,
    Finsupp.linearCombination_single, Basis.coord_apply, mkPiRing_apply, smul_eq_mul, mul_one,
    LinearMap.coe_smulRight, LinearMap.id_coe, id_eq, Subsingleton.elim (Fintype.ofFinite ι)]

/--
theorem `multilinearMap_apply_apply` / 定理 `multilinearMap_apply_apply`

English:
theorem multilinearMap_apply_apply
  given: (ii : (Π i, κ i) × ι') (v)
  proof: by
  simp [Basis.multilinearMap_apply]

中文:
定理 multilinearMap_apply_apply
  条件: (ii : (Π i, κ i) × ι') (v)
  证明: by
  simp [Basis.multilinearMap_apply]

Depends on / 依赖: Basis.multilinearMap_apply, multilinearMap_apply
-/
theorem multilinearMap_apply_apply (ii : (Π i, κ i) × ι') (v) :
    Basis.multilinearMap b b' ii v = (∏ i, (b i).repr (v i) (ii.1 i)) • b' ii.2 := by
  simp [Basis.multilinearMap_apply]

end Basis
