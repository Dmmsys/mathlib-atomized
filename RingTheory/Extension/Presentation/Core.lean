/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.Extension.Presentation.Submersive

/-!
# Presentations on subrings

In this file we establish the API for realising a presentation over a
subring of `R`. We define a property `HasCoeffs R₀` for a presentation `P` to mean
the (sub)ring `R₀` contains the coefficients of the relations of `P`.
subring `R₀` of `R` that contains the coefficients of the relations
In this case there exists a model of `S` over `R₀`, i.e., there exists an `R₀`-algebra `S₀`
such that `S` is isomorphic to `R ⊗[R₀] S₀`.

If the presentation is finite, `R₀` may be chosen as a Noetherian ring. In this case,
this API can be used to remove Noetherian hypothesis in certain cases.

-/

@[expose] public section

open TensorProduct

variable {R S ι σ : Type*} [CommRing R] [CommRing S] [Algebra R S]

variable {P : Algebra.Presentation R S ι σ}

namespace Algebra.Presentation

variable (P) in
-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/--
Definition of `coeffs` / `coeffs` 的定义

English:
definition coeffs
  signature: : Set R
  body: ⋃ (i : σ), (P.relation i).coeffs

中文:
定义 coeffs
  签名: : 集合 R
  定义体: ⋃ (i : σ), (P.relation i).coeffs

Depends on / 依赖: P.relation, coeffs, relation
-/
noncomputable def coeffs : Set R := ⋃ (i : σ), (P.relation i).coeffs

/--
lemma `coeffs_relation_subset_coeffs` / 引理 `coeffs_relation_subset_coeffs`

English:
lemma coeffs_relation_subset_coeffs
  given: (x : σ)
  proof: Set.subset_iUnion_of_subset x (by simp)

中文:
引理 coeffs_relation_subset_coeffs
  条件: (x : σ)
  证明: Set.subset_iUnion_of_subset x (by simp)

Depends on / 依赖: Set.subset_iUnion_of_subset, subset_iUnion_of_subset
-/
lemma coeffs_relation_subset_coeffs (x : σ) :
    ((P.relation x).coeffs : Set R) subseteq P.coeffs :=
  Set.subset_iUnion_of_subset x (by simp)

/--
lemma `finite_coeffs` / 引理 `finite_coeffs`

English:
lemma finite_coeffs
  given: [Finite σ]
  statement: P.coeffs.Finite
  proof: Set.finite_iUnion fun _ => Finset.finite_toSet _

中文:
引理 finite_coeffs
  条件: [有限 σ]
  结论: P.coeffs.有限
  证明: Set.finite_iUnion fun _ => Finset.finite_toSet _

Depends on / 依赖: Finset, Finset.finite_toSet, Set.finite_iUnion, finite_iUnion, finite_toSet
-/
lemma finite_coeffs [Finite σ] : P.coeffs.Finite :=
  Set.finite_iUnion fun _ => Finset.finite_toSet _

variable (P) in
-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/--
Definition of `core` / `core` 的定义

English:
definition core
  signature: : Subalgebra Int R
  body: Algebra.adjoin _ P.coeffs

中文:
定义 core
  签名: : 子代数 整数 R
  定义体: Algebra.adjoin _ P.coeffs

Depends on / 依赖: Algebra, Algebra.adjoin, P.coeffs, adjoin, coeffs
-/
noncomputable def core : Subalgebra Int R := Algebra.adjoin _ P.coeffs

variable (P) in
/--
lemma `coeffs_subset_core` / 引理 `coeffs_subset_core`

English:
lemma coeffs_subset_core
  statement: P.coeffs subseteq P.core
  proof: Algebra.subset_adjoin

中文:
引理 coeffs_subset_core
  结论: P.coeffs subseteq P.core
  证明: Algebra.subset_adjoin

Depends on / 依赖: Algebra, Algebra.subset_adjoin, subset_adjoin
-/
lemma coeffs_subset_core : P.coeffs subseteq P.core := Algebra.subset_adjoin

/--
lemma `coeffs_relation_subset_core` / 引理 `coeffs_relation_subset_core`

English:
lemma coeffs_relation_subset_core
  given: (x : σ)
  proof: subset_trans (P.coeffs_relation_subset_coeffs x) P.coeffs_subset_core

中文:
引理 coeffs_relation_subset_core
  条件: (x : σ)
  证明: subset_trans (P.coeffs_relation_subset_coeffs x) P.coeffs_subset_core

Depends on / 依赖: P.coeffs_relation_subset_coeffs, P.coeffs_subset_core, coeffs_relation_subset_coeffs, coeffs_subset_core, subset_trans
-/
lemma coeffs_relation_subset_core (x : σ) :
    ((P.relation x).coeffs : Set R) subseteq P.core :=
  subset_trans (P.coeffs_relation_subset_coeffs x) P.coeffs_subset_core

variable (P) in
-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/--
Definition of `Core` / `Core` 的定义

English:
definition Core
  signature: : Type _
  body: P.core

中文:
定义 核
  签名: : 类型 _
  定义体: P.core

Depends on / 依赖: P.core
-/
noncomputable def Core : Type _ := P.core

-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CommRing P.Core
  body: fast_instance% (inferInstanceAs <| CommRing P.core)

中文:
实例 :
  签名: 交换环 P.核
  定义体: fast_instance% (inferInstanceAs <| CommRing P.core)

Depends on / 依赖: CommRing, P.core, fast_instance
-/
noncomputable instance : CommRing P.Core := fast_instance% (inferInstanceAs <| CommRing P.core)
-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Algebra P.Core R
  body: fast_instance% (inferInstanceAs <| Algebra P.core R)

中文:
实例 :
  签名: 代数 P.核 R
  定义体: fast_instance% (inferInstanceAs <| Algebra P.core R)

Depends on / 依赖: Algebra, P.core, fast_instance
-/
noncomputable instance : Algebra P.Core R := fast_instance% (inferInstanceAs <| Algebra P.core R)
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FaithfulSMul P.Core R
  body: inferInstanceAs FaithfulSMul P.core R

中文:
实例 :
  签名: 忠实标量乘法 P.核 R
  定义体: inferInstanceAs FaithfulSMul P.core R

Depends on / 依赖: FaithfulSMul, LiftHom, P.core, liftHomOf, of.map
-/
instance : FaithfulSMul P.Core R := inferInstanceAs FaithfulSMul P.core R
-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Algebra P.Core S
  body: fast_instance% (inferInstanceAs <| Algebra P.core S)

中文:
实例 :
  签名: 代数 P.核 S
  定义体: fast_instance% (inferInstanceAs <| Algebra P.core S)

Depends on / 依赖: Algebra, P.core, fast_instance
-/
noncomputable instance : Algebra P.Core S := fast_instance% (inferInstanceAs <| Algebra P.core S)
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsScalarTower P.Core R S
  body: inferInstanceAs IsScalarTower P.core R S

中文:
实例 :
  签名: 标量塔 P.核 R S
  定义体: inferInstanceAs IsScalarTower P.core R S

Depends on / 依赖: IsScalarTower, P.core
-/
instance : IsScalarTower P.Core R S := inferInstanceAs IsScalarTower P.core R S

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Finite
  signature: σ] : FiniteType Int P.Core
  body: .adjoin_of_finite P.finite_coeffs

中文:
实例 [有限
  签名: σ] : 有限型 整数 P.核
  定义体: .adjoin_of_finite P.finite_coeffs

Depends on / 依赖: P.finite_coeffs, adjoin_of_finite, finite_coeffs
-/
instance [Finite σ] : FiniteType Int P.Core := .adjoin_of_finite P.finite_coeffs

variable (P) in
/--
Definition of `HasCoeffs` / `HasCoeffs` 的定义

English:
class HasCoeffs
  parameters: (R₀ : Type*) [CommRing R₀] [Algebra R₀ R] [Algebra R₀ S]
  axioms and operations (1):
    - coeffs_subset_range : P.coeffs subseteq Set.range (algebraMap R₀ R)

中文:
类 有余effs
  参数: (R₀ : 类型) [交换环 R₀] [代数 R₀ R] [代数 R₀ S]
  公理与运算 (1 个):
    - coeffs_subset_range : P.coeffs subseteq 集合.range (algebraMap R₀ R)
-/
class HasCoeffs (R₀ : Type*) [CommRing R₀] [Algebra R₀ R] [Algebra R₀ S]
    [IsScalarTower R₀ R S] where
  coeffs_subset_range : P.coeffs subseteq Set.range (algebraMap R₀ R)

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: P.HasCoeffs P.Core
  body: by
    refine subset_trans P.coeffs_subset_core ?_
    simp [Core, Subalgebra.algebraMap_eq]

中文:
实例 :
  签名: P.有余effs P.核
  定义体: by
    refine subset_trans P.coeffs_subset_core ?_
    simp [Core, Subalgebra.algebraMap_eq]

Depends on / 依赖: P.coeffs_subset_core, Subalgebra, Subalgebra.algebraMap_eq, algebraMap_eq, coeffs_subset_core, subset_trans
-/
instance : P.HasCoeffs P.Core where
  coeffs_subset_range := by
    refine subset_trans P.coeffs_subset_core ?_
    simp [Core, Subalgebra.algebraMap_eq]

variable (R₀ : Type*) [CommRing R₀] [Algebra R₀ R] [Algebra R₀ S] [IsScalarTower R₀ R S]
  [P.HasCoeffs R₀]

/--
lemma `coeffs_subset_range` / 引理 `coeffs_subset_range`

English:
lemma coeffs_subset_range
  statement: (P.coeffs : Set R) subseteq Set.range (algebraMap R₀ R)
  proof: HasCoeffs.coeffs_subset_range

中文:
引理 coeffs_subset_range
  结论: (P.coeffs : 集合 R) subseteq 集合.range (algebraMap R₀ R)
  证明: HasCoeffs.coeffs_subset_range

Depends on / 依赖: HasCoeffs, HasCoeffs.coeffs_subset_range, coeffs_subset_range
-/
lemma coeffs_subset_range : (P.coeffs : Set R) subseteq Set.range (algebraMap R₀ R) :=
  HasCoeffs.coeffs_subset_range

/--
lemma `HasCoeffs.of_isScalarTower` / 引理 `HasCoeffs.of_isScalarTower`

English:
lemma HasCoeffs.of_isScalarTower
  statement: {R₁ : Type*} [CommRing R₁] [Algebra R₀ R₁] [Algebra R₁ R]
  proof: by
  refine ⟨subset_trans (P.coeffs_subset_range R₀) ?_⟩
  simp [IsScalarTower.algebraMap_eq R₀ R₁ R, RingHom.coe_comp, Set.range_comp]

中文:
引理 有余effs.of_isScalarTower
  结论: {R₁ : 类型} [交换环 R₁] [代数 R₀ R₁] [代数 R₁ R]
  证明: by
  refine ⟨subset_trans (P.coeffs_subset_range R₀) ?_⟩
  simp [IsScalarTower.algebraMap_eq R₀ R₁ R, RingHom.coe_comp, Set.range_comp]

Depends on / 依赖: IsScalarTower, IsScalarTower.algebraMap_eq, P.coeffs_subset_range, RingHom, RingHom.coe_comp, Set.range_comp, algebraMap_eq, coe_comp, coeffs_subset_range, range_comp, subset_trans
-/
lemma HasCoeffs.of_isScalarTower {R₁ : Type*} [CommRing R₁] [Algebra R₀ R₁] [Algebra R₁ R]
    [IsScalarTower R₀ R₁ R] [Algebra R₁ S] [IsScalarTower R₁ R S] :
    P.HasCoeffs R₁ := by
  refine ⟨subset_trans (P.coeffs_subset_range R₀) ?_⟩
  simp [IsScalarTower.algebraMap_eq R₀ R₁ R, RingHom.coe_comp, Set.range_comp]

instance (s : Set R) : P.HasCoeffs (Algebra.adjoin R₀ s) := HasCoeffs.of_isScalarTower R₀

/--
lemma `HasCoeffs.coeffs_relation_mem_range` / 引理 `HasCoeffs.coeffs_relation_mem_range`

English:
lemma HasCoeffs.coeffs_relation_mem_range
  given: (x : σ)
  proof: subset_trans (P.coeffs_relation_subset_coeffs x) HasCoeffs.coeffs_subset_range

中文:
引理 有余effs.coeffs_relation_mem_range
  条件: (x : σ)
  证明: subset_trans (P.coeffs_relation_subset_coeffs x) HasCoeffs.coeffs_subset_range

Depends on / 依赖: HasCoeffs, HasCoeffs.coeffs_subset_range, P.coeffs_relation_subset_coeffs, coeffs_relation_subset_coeffs, coeffs_subset_range, subset_trans
-/
lemma HasCoeffs.coeffs_relation_mem_range (x : σ) :
    ↑(P.relation x).coeffs subseteq Set.range (algebraMap R₀ R) :=
  subset_trans (P.coeffs_relation_subset_coeffs x) HasCoeffs.coeffs_subset_range

/--
lemma `HasCoeffs.relation_mem_range_map` / 引理 `HasCoeffs.relation_mem_range_map`

English:
lemma HasCoeffs.relation_mem_range_map
  given: (x : σ)
  proof: by
  rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
  exact HasCoeffs.coeffs_relation_mem_range R₀ x

中文:
引理 有余effs.relation_mem_range_map
  条件: (x : σ)
  证明: by
  rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
  exact HasCoeffs.coeffs_relation_mem_range R₀ x

Depends on / 依赖: HasCoeffs, HasCoeffs.coeffs_relation_mem_range, MvPolynomial, MvPolynomial.mem_range_map_iff_coeffs_subset, coeffs_relation_mem_range, mem_range_map_iff_coeffs_subset
-/
lemma HasCoeffs.relation_mem_range_map (x : σ) :
    P.relation x in Set.range (MvPolynomial.map (algebraMap R₀ R)) := by
  rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
  exact HasCoeffs.coeffs_relation_mem_range R₀ x

/--
Definition of `relationOfHasCoeffs` / `relationOfHasCoeffs` 的定义

English:
definition relationOfHasCoeffs
  signature: (r : σ)
  body: (HasCoeffs.relation_mem_range_map (P := P) R₀ r).choose

中文:
定义 relationOfHasCoeffs
  签名: (r : σ)
  定义体: (HasCoeffs.relation_mem_range_map (P := P) R₀ r).choose

Depends on / 依赖: HasCoeffs, HasCoeffs.relation_mem_range_map, relation_mem_range_map
-/
noncomputable def relationOfHasCoeffs (r : σ) : MvPolynomial ι R₀ :=
  (HasCoeffs.relation_mem_range_map (P := P) R₀ r).choose

/--
lemma `map_relationOfHasCoeffs` / 引理 `map_relationOfHasCoeffs`

English:
lemma map_relationOfHasCoeffs
  given: (r : σ)
  proof: (HasCoeffs.relation_mem_range_map R₀ r).choose_spec

@[simp]

中文:
引理 map_relationOfHasCoeffs
  条件: (r : σ)
  证明: (HasCoeffs.relation_mem_range_map R₀ r).choose_spec

@[simp]

Depends on / 依赖: HasCoeffs, HasCoeffs.relation_mem_range_map, choose_spec, relation_mem_range_map
-/
lemma map_relationOfHasCoeffs (r : σ) :
    MvPolynomial.map (algebraMap R₀ R) (P.relationOfHasCoeffs R₀ r) = P.relation r :=
  (HasCoeffs.relation_mem_range_map R₀ r).choose_spec

@[simp]
/--
lemma `aeval_val_relationOfHasCoeffs` / 引理 `aeval_val_relationOfHasCoeffs`

English:
lemma aeval_val_relationOfHasCoeffs
  given: (r : σ)
  proof: by
  rw [← MvPolynomial.aeval_map_algebraMap R]; rw [map_relationOfHasCoeffs]; rw [aeval_val_relation]

@[simp]

中文:
引理 aeval_val_relationOfHasCoeffs
  条件: (r : σ)
  证明: by
  rw [← MvPolynomial.aeval_map_algebraMap R]; rw [map_relationOfHasCoeffs]; rw [aeval_val_relation]

@[simp]

Depends on / 依赖: MvPolynomial, MvPolynomial.aeval_map_algebraMap, aeval_map_algebraMap, aeval_val_relation, map_relationOfHasCoeffs
-/
lemma aeval_val_relationOfHasCoeffs (r : σ) :
    MvPolynomial.aeval P.val (P.relationOfHasCoeffs R₀ r) = 0 := by
  rw [← MvPolynomial.aeval_map_algebraMap R]; rw [map_relationOfHasCoeffs]; rw [aeval_val_relation]

@[simp]
/--
lemma `algebraTensorAlgEquiv_symm_relation` / 引理 `algebraTensorAlgEquiv_symm_relation`

English:
lemma algebraTensorAlgEquiv_symm_relation
  given: (r : σ)
  proof: by
  rw [← map_relationOfHasCoeffs R₀]; rw [MvPolynomial.algebraTensorAlgEquiv_symm_map]

中文:
引理 algebraTensorAlgEquiv_symm_relation
  条件: (r : σ)
  证明: by
  rw [← map_relationOfHasCoeffs R₀]; rw [MvPolynomial.algebraTensorAlgEquiv_symm_map]

Depends on / 依赖: MvPolynomial, MvPolynomial.algebraTensorAlgEquiv_symm_map, algebraTensorAlgEquiv_symm_map, map_relationOfHasCoeffs
-/
lemma algebraTensorAlgEquiv_symm_relation (r : σ) :
    (MvPolynomial.algebraTensorAlgEquiv R₀ R).symm (P.relation r) =
      1 otimesₜ P.relationOfHasCoeffs R₀ r := by
  rw [← map_relationOfHasCoeffs R₀]; rw [MvPolynomial.algebraTensorAlgEquiv_symm_map]

/--
Definition of `ModelOfHasCoeffs` / `ModelOfHasCoeffs` 的定义

English:
abbreviation ModelOfHasCoeffs
  signature: : Type _
  body: MvPolynomial ι R₀ ⧸ (Ideal.span <| Set.range (P.relationOfHasCoeffs R₀))

中文:
缩写 ModelOfHasCoeffs
  签名: : 类型 _
  定义体: MvPolynomial ι R₀ ⧸ (Ideal.span <| Set.range (P.relationOfHasCoeffs R₀))

Depends on / 依赖: Ideal.span, MvPolynomial, P.relationOfHasCoeffs, Set.range, relationOfHasCoeffs
-/
abbrev ModelOfHasCoeffs : Type _ :=
  MvPolynomial ι R₀ ⧸ (Ideal.span <| Set.range (P.relationOfHasCoeffs R₀))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Finite
  signature: ι] [Finite σ] : Algebra.FinitePresentation R₀ (P.ModelOfHasCoeffs R₀)
  body: by
  classical
  cases nonempty_fintype σ
  exact .quotient ⟨Finset.image (P.relationOfHasCoeffs R₀) .univ, by simp⟩

中文:
实例 [有限
  签名: ι] [有限 σ] : 代数.有限呈现 R₀ (P.ModelOfHasCoeffs R₀)
  定义体: by
  classical
  cases nonempty_fintype σ
  exact .quotient ⟨Finset.image (P.relationOfHasCoeffs R₀) .univ, by simp⟩

Depends on / 依赖: Finset, Finset.image, P.relationOfHasCoeffs, classical, nonempty_fintype, quotient, relationOfHasCoeffs
-/
instance [Finite ι] [Finite σ] : Algebra.FinitePresentation R₀ (P.ModelOfHasCoeffs R₀) := by
  classical
  cases nonempty_fintype σ
  exact .quotient ⟨Finset.image (P.relationOfHasCoeffs R₀) .univ, by simp⟩

variable (P) in
/--
Definition of `tensorModelOfHasCoeffsHom` / `tensorModelOfHasCoeffsHom` 的定义

English:
definition tensorModelOfHasCoeffsHom
  signature: : R otimes[R₀] P.ModelOfHasCoeffs R₀ ->ₐ[R] S
  body: Algebra.TensorProduct.lift (Algebra.ofId R S)
    (Ideal.Quotient.liftₐ _ (MvPolynomial.aeval P.val) <| by
      simp_rw [← RingHom.mem_ker, ← SetLike.le_def, Ideal.span_le]
      rintro a ⟨i, rfl⟩
      simp)
    fun _ _ => Commute.all _ _

@[simp]

中文:
定义 tensorModelOfHasCoeffsHom
  签名: : R otimes[R₀] P.ModelOfHasCoeffs R₀ ->ₐ[R] S
  定义体: Algebra.TensorProduct.lift (Algebra.ofId R S)
    (Ideal.Quotient.liftₐ _ (MvPolynomial.aeval P.val) <| by
      simp_rw [← RingHom.mem_ker, ← SetLike.le_def, Ideal.span_le]
      rintro a ⟨i, rfl⟩
      simp)
    fun _ _ => Commute.all _ _

@[simp]

Depends on / 依赖: Algebra, Algebra.TensorProduct.lift, Algebra.ofId, Commute, Commute.all, Ideal.Quotient.lift, Ideal.span_le, MvPolynomial, MvPolynomial.aeval, P.val, Quotient, RingHom, RingHom.mem_ker, SetLike, SetLike.le_def, TensorProduct, le_def, mem_ker, simp_rw, span_le
-/
noncomputable def tensorModelOfHasCoeffsHom : R otimes[R₀] P.ModelOfHasCoeffs R₀ ->ₐ[R] S :=
  Algebra.TensorProduct.lift (Algebra.ofId R S)
    (Ideal.Quotient.liftₐ _ (MvPolynomial.aeval P.val) <| by
      simp_rw [← RingHom.mem_ker, ← SetLike.le_def, Ideal.span_le]
      rintro a ⟨i, rfl⟩
      simp)
    fun _ _ => Commute.all _ _

@[simp]
/--
lemma `tensorModelOfHasCoeffsHom_tmul` / 引理 `tensorModelOfHasCoeffsHom_tmul`

English:
lemma tensorModelOfHasCoeffsHom_tmul
  given: (x : R) (y : MvPolynomial ι R₀)
  proof: rfl

中文:
引理 tensorModelOfHasCoeffsHom_tmul
  条件: (x : R) (y : 多元多项式 ι R₀)
  证明: rfl
-/
lemma tensorModelOfHasCoeffsHom_tmul (x : R) (y : MvPolynomial ι R₀) :
    P.tensorModelOfHasCoeffsHom R₀ (x otimesₜ y) = algebraMap R S x * MvPolynomial.aeval P.val y :=
  rfl

variable (P) in
/--
Definition of `tensorModelOfHasCoeffsInv` / `tensorModelOfHasCoeffsInv` 的定义

English:
definition tensorModelOfHasCoeffsInv
  signature: : S ->ₐ[R] R otimes[R₀] P.ModelOfHasCoeffs R₀
  body: (Ideal.Quotient.liftₐ _
    ((Algebra.TensorProduct.map (.id R R) (Ideal.Quotient.mkₐ _ _)).comp
      (MvPolynomial.algebraTensorAlgEquiv R₀ R).symm.toAlgHom) <| by
    simp_rw [← RingHom.mem_ker, ← SetLike.le_def]
    rw [← P.span_range_relation_eq_ker]; rw [Ideal.span_le]
    rintro a ⟨i, rfl⟩
    simp only [SetLike.mem_coe, RingHom.mem_ker, AlgHom.coe_comp,
      AlgEquiv.coe_toAlgHom, Function.comp_apply, algebraTensorAlgEquiv_symm_relation]
    simp only [TensorProduct.map_tmul, AlgHom.coe_id, id_eq, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.mk_span_range, tmul_zero]).comp
    (P.quotientEquiv.restrictScalars R).symm.toAlgHom

中文:
定义 tensorModelOfHasCoeffsInv
  签名: : S ->ₐ[R] R otimes[R₀] P.ModelOfHasCoeffs R₀
  定义体: (Ideal.Quotient.liftₐ _
    ((Algebra.TensorProduct.map (.id R R) (Ideal.Quotient.mkₐ _ _)).comp
      (MvPolynomial.algebraTensorAlgEquiv R₀ R).symm.toAlgHom) <| by
    simp_rw [← RingHom.mem_ker, ← SetLike.le_def]
    rw [← P.span_range_relation_eq_ker]; rw [Ideal.span_le]
    rintro a ⟨i, rfl⟩
    simp only [SetLike.mem_coe, RingHom.mem_ker, AlgHom.coe_comp,
      AlgEquiv.coe_toAlgHom, Function.comp_apply, algebraTensorAlgEquiv_symm_relation]
    simp only [TensorProduct.map_tmul, AlgHom.coe_id, id_eq, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.mk_span_range, tmul_zero]).comp
    (P.quotientEquiv.restrictScalars R).symm.toAlgHom

Depends on / 依赖: AlgEquiv, AlgEquiv.coe_toAlgHom, AlgHom, AlgHom.coe_comp, AlgHom.coe_id, Algebra, Algebra.TensorProduct.map, Function, Function.comp_apply, Ideal.Quotient.lift, Ideal.Quotient.mk, Ideal.span_le, MvPolynomial, MvPolynomial.algebraTensorAlgEquiv, P.span_range_relation_eq_ker, Quotient, RingHom, RingHom.mem_ker, SetLike, SetLike.le_def
-/
noncomputable def tensorModelOfHasCoeffsInv : S ->ₐ[R] R otimes[R₀] P.ModelOfHasCoeffs R₀ :=
  (Ideal.Quotient.liftₐ _
    ((Algebra.TensorProduct.map (.id R R) (Ideal.Quotient.mkₐ _ _)).comp
      (MvPolynomial.algebraTensorAlgEquiv R₀ R).symm.toAlgHom) <| by
    simp_rw [← RingHom.mem_ker, ← SetLike.le_def]
    rw [← P.span_range_relation_eq_ker]; rw [Ideal.span_le]
    rintro a ⟨i, rfl⟩
    simp only [SetLike.mem_coe, RingHom.mem_ker, AlgHom.coe_comp,
      AlgEquiv.coe_toAlgHom, Function.comp_apply, algebraTensorAlgEquiv_symm_relation]
    simp only [TensorProduct.map_tmul, AlgHom.coe_id, id_eq, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.mk_span_range, tmul_zero]).comp
    (P.quotientEquiv.restrictScalars R).symm.toAlgHom

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `tensorModelOfHasCoeffsInv_aeval_val` / 引理 `tensorModelOfHasCoeffsInv_aeval_val`

English:
lemma tensorModelOfHasCoeffsInv_aeval_val
  given: (x : MvPolynomial ι R₀)
  proof: by
  rw [← MvPolynomial.aeval_map_algebraMap R]; rw [← Generators.algebraMap_apply]; rw [← quotientEquiv_mk]
  simp [tensorModelOfHasCoeffsInv, -quotientEquiv_symm, -quotientEquiv_mk]

中文:
引理 tensorModelOfHasCoeffsInv_aeval_val
  条件: (x : 多元多项式 ι R₀)
  证明: by
  rw [← MvPolynomial.aeval_map_algebraMap R]; rw [← Generators.algebraMap_apply]; rw [← quotientEquiv_mk]
  simp [tensorModelOfHasCoeffsInv, -quotientEquiv_symm, -quotientEquiv_mk]

Depends on / 依赖: Generators, Generators.algebraMap_apply, MvPolynomial, MvPolynomial.aeval_map_algebraMap, aeval_map_algebraMap, algebraMap_apply, quotientEquiv_mk, quotientEquiv_symm, tensorModelOfHasCoeffsInv
-/
lemma tensorModelOfHasCoeffsInv_aeval_val (x : MvPolynomial ι R₀) :
    P.tensorModelOfHasCoeffsInv R₀ (MvPolynomial.aeval P.val x) =
      1 otimesₜ[R₀] (Ideal.Quotient.mk _ x) := by
  rw [← MvPolynomial.aeval_map_algebraMap R]; rw [← Generators.algebraMap_apply]; rw [← quotientEquiv_mk]
  simp [tensorModelOfHasCoeffsInv, -quotientEquiv_symm, -quotientEquiv_mk]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `tensorModelOfHasCoeffsHom_comp` / 引理 `tensorModelOfHasCoeffsHom_comp`

English:
lemma tensorModelOfHasCoeffsHom_comp
  proof: by
  have h : Function.Surjective
      ((P.quotientEquiv.restrictScalars R).toAlgHom.comp (Ideal.Quotient.mkₐ _ _)) :=
    (P.quotientEquiv.restrictScalars R).surjective.comp Ideal.Quotient.mk_surjective
  simp only [← AlgHom.cancel_right h, tensorModelOfHasCoeffsInv, AlgHom.id_comp]
  rw [AlgHom.comp_assoc]; rw [AlgHom.comp_assoc]; rw [← AlgHom.comp_assoc _ _ (Ideal.Quotient.mkₐ R P.ker)]; rw [AlgEquiv.symm_comp]; rw [AlgHom.id_comp]
  ext x
  simp

中文:
引理 tensorModelOfHasCoeffsHom_comp
  证明: by
  have h : Function.Surjective
      ((P.quotientEquiv.restrictScalars R).toAlgHom.comp (Ideal.Quotient.mkₐ _ _)) :=
    (P.quotientEquiv.restrictScalars R).surjective.comp Ideal.Quotient.mk_surjective
  simp only [← AlgHom.cancel_right h, tensorModelOfHasCoeffsInv, AlgHom.id_comp]
  rw [AlgHom.comp_assoc]; rw [AlgHom.comp_assoc]; rw [← AlgHom.comp_assoc _ _ (Ideal.Quotient.mkₐ R P.ker)]; rw [AlgEquiv.symm_comp]; rw [AlgHom.id_comp]
  ext x
  simp

Depends on / 依赖: AlgEquiv, AlgEquiv.symm_comp, AlgHom, AlgHom.cancel_right, AlgHom.comp_assoc, AlgHom.id_comp, Function, Function.Surjective, Ideal.Quotient.mk, Ideal.Quotient.mk_surjective, P.ker, P.quotientEquiv.restrictScalars, Quotient, Surjective, cancel_right, comp_assoc, id_comp, mk_surjective, quotientEquiv, restrictScalars
-/
lemma tensorModelOfHasCoeffsHom_comp :
    (P.tensorModelOfHasCoeffsHom R₀).comp (P.tensorModelOfHasCoeffsInv R₀) = AlgHom.id R S := by
  have h : Function.Surjective
      ((P.quotientEquiv.restrictScalars R).toAlgHom.comp (Ideal.Quotient.mkₐ _ _)) :=
    (P.quotientEquiv.restrictScalars R).surjective.comp Ideal.Quotient.mk_surjective
  simp only [← AlgHom.cancel_right h, tensorModelOfHasCoeffsInv, AlgHom.id_comp]
  rw [AlgHom.comp_assoc]; rw [AlgHom.comp_assoc]; rw [← AlgHom.comp_assoc _ _ (Ideal.Quotient.mkₐ R P.ker)]; rw [AlgEquiv.symm_comp]; rw [AlgHom.id_comp]
  ext x
  simp

/--
lemma `tensorModelOfHasCoeffsInv_comp` / 引理 `tensorModelOfHasCoeffsInv_comp`

English:
lemma tensorModelOfHasCoeffsInv_comp
  proof: by
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp

中文:
引理 tensorModelOfHasCoeffsInv_comp
  证明: by
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp

Depends on / 依赖: Ideal.Quotient.mk_surjective, Quotient, mk_surjective
-/
lemma tensorModelOfHasCoeffsInv_comp :
    (P.tensorModelOfHasCoeffsInv R₀).comp (P.tensorModelOfHasCoeffsHom R₀) = AlgHom.id R _ := by
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp

/--
Definition of `tensorModelOfHasCoeffsEquiv` / `tensorModelOfHasCoeffsEquiv` 的定义

English:
definition tensorModelOfHasCoeffsEquiv
  signature: : R otimes[R₀] P.ModelOfHasCoeffs R₀ ≃ₐ[R] S
  body: AlgEquiv.ofAlgHom (P.tensorModelOfHasCoeffsHom R₀) (P.tensorModelOfHasCoeffsInv R₀)
    (P.tensorModelOfHasCoeffsHom_comp R₀) (P.tensorModelOfHasCoeffsInv_comp R₀)

@[simp]

中文:
定义 tensorModelOfHasCoeffsEquiv
  签名: : R otimes[R₀] P.ModelOfHasCoeffs R₀ ≃ₐ[R] S
  定义体: AlgEquiv.ofAlgHom (P.tensorModelOfHasCoeffsHom R₀) (P.tensorModelOfHasCoeffsInv R₀)
    (P.tensorModelOfHasCoeffsHom_comp R₀) (P.tensorModelOfHasCoeffsInv_comp R₀)

@[simp]

Depends on / 依赖: AlgEquiv, AlgEquiv.ofAlgHom, P.tensorModelOfHasCoeffsHom, P.tensorModelOfHasCoeffsHom_comp, P.tensorModelOfHasCoeffsInv, P.tensorModelOfHasCoeffsInv_comp, ofAlgHom, tensorModelOfHasCoeffsHom, tensorModelOfHasCoeffsHom_comp, tensorModelOfHasCoeffsInv, tensorModelOfHasCoeffsInv_comp
-/
noncomputable def tensorModelOfHasCoeffsEquiv : R otimes[R₀] P.ModelOfHasCoeffs R₀ ≃ₐ[R] S :=
  AlgEquiv.ofAlgHom (P.tensorModelOfHasCoeffsHom R₀) (P.tensorModelOfHasCoeffsInv R₀)
    (P.tensorModelOfHasCoeffsHom_comp R₀) (P.tensorModelOfHasCoeffsInv_comp R₀)

@[simp]
/--
lemma `tensorModelOfHasCoeffsEquiv_tmul` / 引理 `tensorModelOfHasCoeffsEquiv_tmul`

English:
lemma tensorModelOfHasCoeffsEquiv_tmul
  given: (x : R) (y : MvPolynomial ι R₀)
  proof: rfl

@[simp]

中文:
引理 tensorModelOfHasCoeffsEquiv_tmul
  条件: (x : R) (y : 多元多项式 ι R₀)
  证明: rfl

@[simp]
-/
lemma tensorModelOfHasCoeffsEquiv_tmul (x : R) (y : MvPolynomial ι R₀) :
    P.tensorModelOfHasCoeffsEquiv R₀ (x otimesₜ y) = algebraMap R S x * MvPolynomial.aeval P.val y :=
  rfl

@[simp]
/--
lemma `tensorModelOfHasCoeffsEquiv_symm_tmul` / 引理 `tensorModelOfHasCoeffsEquiv_symm_tmul`

English:
lemma tensorModelOfHasCoeffsEquiv_symm_tmul
  given: (x : MvPolynomial ι R₀)
  proof: tensorModelOfHasCoeffsInv_aeval_val _ x

中文:
引理 tensorModelOfHasCoeffsEquiv_symm_tmul
  条件: (x : 多元多项式 ι R₀)
  证明: tensorModelOfHasCoeffsInv_aeval_val _ x

Depends on / 依赖: tensorModelOfHasCoeffsInv_aeval_val
-/
lemma tensorModelOfHasCoeffsEquiv_symm_tmul (x : MvPolynomial ι R₀) :
    (P.tensorModelOfHasCoeffsEquiv R₀).symm (MvPolynomial.aeval P.val x) =
      1 otimesₜ[R₀] (Ideal.Quotient.mk _ x) :=
  tensorModelOfHasCoeffsInv_aeval_val _ x

end Algebra.Presentation
namespace Algebra.PreSubmersivePresentation

variable (P : Algebra.PreSubmersivePresentation R S ι σ)
variable (R₀ : Type*) [CommRing R₀] [Algebra R₀ R] [Algebra R₀ S] [IsScalarTower R₀ R S]
  [P.HasCoeffs R₀]

/-- The presubmersive presentation on `P.ModelOfHasCoeffs R₀` provided `P.HasCoeffs R₀`. -/
@[simps!]
/--
Definition of `ofHasCoeffs` / `ofHasCoeffs` 的定义

English:
definition ofHasCoeffs
  signature: :
  body: Algebra.Presentation.naive
  map := P.map
  map_inj := P.map_inj

#adaptation_note /-- As of nightly-2026-04-29, the simpNF linter is failing here.
Assistance investigating this would be appreciated. -/

中文:
定义 ofHasCoeffs
  签名: :
  定义体: Algebra.Presentation.naive
  map := P.map
  map_inj := P.map_inj

#adaptation_note /-- As of nightly-2026-04-29, the simpNF linter is failing here.
Assistance investigating this would be appreciated. -/

Depends on / 依赖: Algebra, Algebra.Presentation.naive, Presentation
-/
noncomputable def ofHasCoeffs :
    Algebra.PreSubmersivePresentation R₀ (P.ModelOfHasCoeffs R₀) ι σ where
  __ := Algebra.Presentation.naive
  map := P.map
  map_inj := P.map_inj

#adaptation_note /-- As of nightly-2026-04-29, the simpNF linter is failing here.
Assistance investigating this would be appreciated. -/
attribute [nolint simpNF]
  _root_.Algebra.PreSubmersivePresentation.ofHasCoeffs_algebra_algebraMap_apply

end Algebra.PreSubmersivePresentation

namespace Algebra.SubmersivePresentation

variable [Finite σ] (P : Algebra.SubmersivePresentation R S ι σ)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `exists_sum_eq_σ_jacobian_mul_σ_jacobian_inv_sub_one` / 引理 `exists_sum_eq_σ_jacobian_mul_σ_jacobian_inv_sub_one`

English:
lemma exists_sum_eq_σ_jacobian_mul_σ_jacobian_inv_sub_one
  proof: by
  have H : P.jacobiMatrix.det * P.σ ↑(P.jacobian_isUnit.unit⁻¹) - 1 in P.ker := by
    simp [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
  rwa [← P.span_range_relation_eq_ker, Ideal.mem_span_range_iff_exists_fun] at H

中文:
引理 存在_sum_eq_σ_jacobian_mul_σ_jacobian_inv_sub_one
  证明: by
  have H : P.jacobiMatrix.det * P.σ ↑(P.jacobian_isUnit.unit⁻¹) - 1 in P.ker := by
    simp [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
  rwa [← P.span_range_relation_eq_ker, Ideal.mem_span_range_iff_exists_fun] at H

Depends on / 依赖: Ideal.mem_span_range_iff_exists_fun, P.jacobiMatrix.det, P.jacobian_isUnit.unit, P.ker, P.span_range_relation_eq_ker, PreSubmersivePresentation, PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, jacobiMatrix, jacobian_eq_jacobiMatrix_det, jacobian_isUnit, mem_span_range_iff_exists_fun, span_range_relation_eq_ker
-/
lemma exists_sum_eq_σ_jacobian_mul_σ_jacobian_inv_sub_one
    [DecidableEq σ] [Fintype σ] :
    exists v : σ -> MvPolynomial ι R, ∑ i, v i * P.relation i =
        P.jacobiMatrix.det * P.σ ↑(P.jacobian_isUnit.unit⁻¹) - 1 := by
  have H : P.jacobiMatrix.det * P.σ ↑(P.jacobian_isUnit.unit⁻¹) - 1 in P.ker := by
    simp [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
  rwa [← P.span_range_relation_eq_ker, Ideal.mem_span_range_iff_exists_fun] at H

/-- An arbitrarily chosen relation exhibiting the fact that `P.jacobian` is invertible. -/
noncomputable
/--
Definition of `jacobianRelations` / `jacobianRelations` 的定义

English:
definition jacobianRelations
  signature: (s : σ)
  body: letI := Fintype.ofFinite σ
  letI := Classical.decEq σ
  P.exists_sum_eq_σ_jacobian_mul_σ_jacobian_inv_sub_one.choose s

中文:
定义 jacobianRelations
  签名: (s : σ)
  定义体: letI := Fintype.ofFinite σ
  letI := Classical.decEq σ
  P.exists_sum_eq_σ_jacobian_mul_σ_jacobian_inv_sub_one.choose s

Depends on / 依赖: Classical, Classical.decEq, Fintype, Fintype.ofFinite, P.exists_sum_eq_, _jacobian_inv_sub_one.choose, ofFinite
-/
def jacobianRelations (s : σ) : MvPolynomial ι R :=
  letI := Fintype.ofFinite σ
  letI := Classical.decEq σ
  P.exists_sum_eq_σ_jacobian_mul_σ_jacobian_inv_sub_one.choose s

/--
lemma `jacobianRelations_spec` / 引理 `jacobianRelations_spec`

English:
lemma jacobianRelations_spec
  given: [DecidableEq σ] [Fintype σ]
  proof: by
  delta jacobianRelations
  convert! P.exists_sum_eq_σ_jacobian_mul_σ_jacobian_inv_sub_one.choose_spec

中文:
引理 jacobianRelations_spec
  条件: [DecidableEq σ] [有限类型 σ]
  证明: by
  delta jacobianRelations
  convert! P.exists_sum_eq_σ_jacobian_mul_σ_jacobian_inv_sub_one.choose_spec

Depends on / 依赖: P.exists_sum_eq_, _jacobian_inv_sub_one.choose_spec, choose_spec, convert, jacobianRelations
-/
lemma jacobianRelations_spec [DecidableEq σ] [Fintype σ] :
    ∑ i, P.jacobianRelations i * P.relation i =
      P.jacobiMatrix.det * P.σ ↑(P.jacobian_isUnit.unit⁻¹) - 1 := by
  delta jacobianRelations
  convert! P.exists_sum_eq_σ_jacobian_mul_σ_jacobian_inv_sub_one.choose_spec

-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/--
Definition of `coeffs` / `coeffs` 的定义

English:
definition coeffs
  signature: : Set R
  body: P.toPresentation.coeffs union (P.σ (P.jacobian_isUnit.unit⁻¹ :)).coeffs union
    ⋃ i, (P.jacobianRelations i).coeffs

中文:
定义 coeffs
  签名: : 集合 R
  定义体: P.toPresentation.coeffs union (P.σ (P.jacobian_isUnit.unit⁻¹ :)).coeffs union
    ⋃ i, (P.jacobianRelations i).coeffs

Depends on / 依赖: P.jacobianRelations, P.jacobian_isUnit.unit, P.toPresentation.coeffs, coeffs, jacobianRelations, jacobian_isUnit, toPresentation
-/
noncomputable def coeffs : Set R :=
  P.toPresentation.coeffs union (P.σ (P.jacobian_isUnit.unit⁻¹ :)).coeffs union
    ⋃ i, (P.jacobianRelations i).coeffs

/--
lemma `finite_coeffs` / 引理 `finite_coeffs`

English:
lemma finite_coeffs
  statement: P.coeffs.Finite
  proof: .union (P.toPresentation.finite_coeffs.union (by simp))
    (.iUnion Set.finite_univ (by simp) (by simp))

中文:
引理 finite_coeffs
  结论: P.coeffs.有限
  证明: .union (P.toPresentation.finite_coeffs.union (by simp))
    (.iUnion Set.finite_univ (by simp) (by simp))

Depends on / 依赖: P.toPresentation.finite_coeffs.union, Set.finite_univ, finite_coeffs, finite_univ, iUnion, toPresentation
-/
lemma finite_coeffs : P.coeffs.Finite :=
  .union (P.toPresentation.finite_coeffs.union (by simp))
    (.iUnion Set.finite_univ (by simp) (by simp))

/--
lemma `coeffs_toPresentation_subset_coeffs` / 引理 `coeffs_toPresentation_subset_coeffs`

English:
lemma coeffs_toPresentation_subset_coeffs
  statement: P.toPresentation.coeffs subseteq P.coeffs
  proof: Set.subset_union_left.trans Set.subset_union_left

中文:
引理 coeffs_toPresentation_subset_coeffs
  结论: P.toPresentation.coeffs subseteq P.coeffs
  证明: Set.subset_union_left.trans Set.subset_union_left

Depends on / 依赖: Set.subset_union_left, Set.subset_union_left.trans, subset_union_left
-/
lemma coeffs_toPresentation_subset_coeffs : P.toPresentation.coeffs subseteq P.coeffs :=
  Set.subset_union_left.trans Set.subset_union_left

/--
Definition of `HasCoeffs` / `HasCoeffs` 的定义

English:
class HasCoeffs
  parameters: (R₀ : Type*) [CommRing R₀] [Algebra R₀ R] [Algebra R₀ S]
  axioms and operations (1):
    - coeffs_subset_range : P.coeffs subseteq ↑(algebraMap R₀ R).range

中文:
类 有余effs
  参数: (R₀ : 类型) [交换环 R₀] [代数 R₀ R] [代数 R₀ S]
  公理与运算 (1 个):
    - coeffs_subset_range : P.coeffs subseteq ↑(algebraMap R₀ R).range
-/
class HasCoeffs (R₀ : Type*) [CommRing R₀] [Algebra R₀ R] [Algebra R₀ S]
    [IsScalarTower R₀ R S] where
  coeffs_subset_range : P.coeffs subseteq ↑(algebraMap R₀ R).range

variable (R₀ : Type*) [CommRing R₀] [Algebra R₀ R] [Algebra R₀ S] [IsScalarTower R₀ R S]
  [P.HasCoeffs R₀]

instance (priority := low) : P.toPresentation.HasCoeffs R₀ where
  coeffs_subset_range := P.coeffs_toPresentation_subset_coeffs.trans HasCoeffs.coeffs_subset_range

/-- The jacobian of a presentation in the smaller coefficient ring, provided `P.HasCoeffs R₀`. -/
noncomputable
/--
Definition of `jacobianOfHasCoeffs` / `jacobianOfHasCoeffs` 的定义

English:
definition jacobianOfHasCoeffs
  signature: : MvPolynomial ι R₀
  body: letI := Classical.decEq σ
  letI := Fintype.ofFinite σ
  (P.toPreSubmersivePresentation.ofHasCoeffs R₀).jacobiMatrix.det

@[simp]

中文:
定义 jacobianOfHasCoeffs
  签名: : 多元多项式 ι R₀
  定义体: letI := Classical.decEq σ
  letI := Fintype.ofFinite σ
  (P.toPreSubmersivePresentation.ofHasCoeffs R₀).jacobiMatrix.det

@[simp]

Depends on / 依赖: Classical, Classical.decEq, Fintype, Fintype.ofFinite, P.toPreSubmersivePresentation.ofHasCoeffs, jacobiMatrix, jacobiMatrix.det, ofFinite, ofHasCoeffs, toPreSubmersivePresentation
-/
def jacobianOfHasCoeffs : MvPolynomial ι R₀ :=
  letI := Classical.decEq σ
  letI := Fintype.ofFinite σ
  (P.toPreSubmersivePresentation.ofHasCoeffs R₀).jacobiMatrix.det

@[simp]
/--
lemma `map_jacobianOfHasCoeffs` / 引理 `map_jacobianOfHasCoeffs`

English:
lemma map_jacobianOfHasCoeffs
  given: [Fintype σ] [DecidableEq σ]
  proof: by
  rw [jacobianOfHasCoeffs]; rw [@RingHom.map_det]
  congr! 1
  ext1 i j
  simp [Presentation.map_relationOfHasCoeffs, ← MvPolynomial.pderiv_map,
    PreSubmersivePresentation.jacobiMatrix_apply]

@[simp]

中文:
引理 map_jacobianOfHasCoeffs
  条件: [有限类型 σ] [DecidableEq σ]
  证明: by
  rw [jacobianOfHasCoeffs]; rw [@RingHom.map_det]
  congr! 1
  ext1 i j
  simp [Presentation.map_relationOfHasCoeffs, ← MvPolynomial.pderiv_map,
    PreSubmersivePresentation.jacobiMatrix_apply]

@[simp]

Depends on / 依赖: MvPolynomial, MvPolynomial.pderiv_map, PreSubmersivePresentation, PreSubmersivePresentation.jacobiMatrix_apply, Presentation, Presentation.map_relationOfHasCoeffs, RingHom, RingHom.map_det, jacobiMatrix_apply, jacobianOfHasCoeffs, map_det, map_relationOfHasCoeffs, pderiv_map
-/
lemma map_jacobianOfHasCoeffs [Fintype σ] [DecidableEq σ] :
    (P.jacobianOfHasCoeffs R₀).map (algebraMap R₀ R) = P.jacobiMatrix.det := by
  rw [jacobianOfHasCoeffs]; rw [@RingHom.map_det]
  congr! 1
  ext1 i j
  simp [Presentation.map_relationOfHasCoeffs, ← MvPolynomial.pderiv_map,
    PreSubmersivePresentation.jacobiMatrix_apply]

@[simp]
/--
lemma `aeval_jacobianOfHasCoeffs` / 引理 `aeval_jacobianOfHasCoeffs`

English:
lemma aeval_jacobianOfHasCoeffs
  proof: by
  classical
  let : Fintype σ := Fintype.ofFinite _
  rw [← MvPolynomial.aeval_map_algebraMap R]; rw [map_jacobianOfHasCoeffs]; rw [P.jacobian_eq_jacobiMatrix_det]; rw [Generators.algebraMap_apply]

中文:
引理 aeval_jacobianOfHasCoeffs
  证明: by
  classical
  let : Fintype σ := Fintype.ofFinite _
  rw [← MvPolynomial.aeval_map_algebraMap R]; rw [map_jacobianOfHasCoeffs]; rw [P.jacobian_eq_jacobiMatrix_det]; rw [Generators.algebraMap_apply]

Depends on / 依赖: Fintype, Fintype.ofFinite, Generators, Generators.algebraMap_apply, MvPolynomial, MvPolynomial.aeval_map_algebraMap, P.jacobian_eq_jacobiMatrix_det, aeval_map_algebraMap, algebraMap_apply, classical, jacobian_eq_jacobiMatrix_det, map_jacobianOfHasCoeffs, ofFinite
-/
lemma aeval_jacobianOfHasCoeffs :
    MvPolynomial.aeval P.val (P.jacobianOfHasCoeffs R₀) = P.jacobian := by
  classical
  let : Fintype σ := Fintype.ofFinite _
  rw [← MvPolynomial.aeval_map_algebraMap R]; rw [map_jacobianOfHasCoeffs]; rw [P.jacobian_eq_jacobiMatrix_det]; rw [Generators.algebraMap_apply]

/-- The inverse jacobian of a presentation in the smaller coefficient ring,
provided `P.HasCoeffs R₀`. -/
noncomputable
/--
Definition of `invJacobianOfHasCoeffs` / `invJacobianOfHasCoeffs` 的定义

English:
definition invJacobianOfHasCoeffs
  signature: : MvPolynomial ι R₀
  body: (MvPolynomial.mem_range_map_iff_coeffs_subset.mpr
    ((Set.subset_union_right.trans Set.subset_union_left).trans
      (HasCoeffs.coeffs_subset_range (P := P)))).choose

@[simp]

中文:
定义 invJacobianOfHasCoeffs
  签名: : 多元多项式 ι R₀
  定义体: (MvPolynomial.mem_range_map_iff_coeffs_subset.mpr
    ((Set.subset_union_right.trans Set.subset_union_left).trans
      (HasCoeffs.coeffs_subset_range (P := P)))).choose

@[simp]

Depends on / 依赖: HasCoeffs, HasCoeffs.coeffs_subset_range, MvPolynomial, MvPolynomial.mem_range_map_iff_coeffs_subset.mpr, Set.subset_union_left, Set.subset_union_right.trans, coeffs_subset_range, mem_range_map_iff_coeffs_subset, subset_union_left, subset_union_right
-/
def invJacobianOfHasCoeffs : MvPolynomial ι R₀ :=
  (MvPolynomial.mem_range_map_iff_coeffs_subset.mpr
    ((Set.subset_union_right.trans Set.subset_union_left).trans
      (HasCoeffs.coeffs_subset_range (P := P)))).choose

@[simp]
/--
lemma `map_invJacobianOfHasCoeffs` / 引理 `map_invJacobianOfHasCoeffs`

English:
lemma map_invJacobianOfHasCoeffs
  proof: (MvPolynomial.mem_range_map_iff_coeffs_subset.mpr
    ((Set.subset_union_right.trans Set.subset_union_left).trans
      (HasCoeffs.coeffs_subset_range (P := P)))).choose_spec

@[simp]

中文:
引理 map_invJacobianOfHasCoeffs
  证明: (MvPolynomial.mem_range_map_iff_coeffs_subset.mpr
    ((Set.subset_union_right.trans Set.subset_union_left).trans
      (HasCoeffs.coeffs_subset_range (P := P)))).choose_spec

@[simp]

Depends on / 依赖: HasCoeffs, HasCoeffs.coeffs_subset_range, MvPolynomial, MvPolynomial.mem_range_map_iff_coeffs_subset.mpr, Set.subset_union_left, Set.subset_union_right.trans, choose_spec, coeffs_subset_range, mem_range_map_iff_coeffs_subset, subset_union_left, subset_union_right
-/
lemma map_invJacobianOfHasCoeffs :
    (P.invJacobianOfHasCoeffs R₀).map (algebraMap R₀ R) = P.σ ↑(P.jacobian_isUnit.unit⁻¹) :=
  (MvPolynomial.mem_range_map_iff_coeffs_subset.mpr
    ((Set.subset_union_right.trans Set.subset_union_left).trans
      (HasCoeffs.coeffs_subset_range (P := P)))).choose_spec

@[simp]
/--
lemma `aeval_invJacobianOfHasCoeffs` / 引理 `aeval_invJacobianOfHasCoeffs`

English:
lemma aeval_invJacobianOfHasCoeffs
  proof: by
  simpa [-map_invJacobianOfHasCoeffs, MvPolynomial.aeval_map_algebraMap] using
    congr(MvPolynomial.aeval P.val $(P.map_invJacobianOfHasCoeffs R₀))

中文:
引理 aeval_invJacobianOfHasCoeffs
  证明: by
  simpa [-map_invJacobianOfHasCoeffs, MvPolynomial.aeval_map_algebraMap] using
    congr(MvPolynomial.aeval P.val $(P.map_invJacobianOfHasCoeffs R₀))

Depends on / 依赖: MvPolynomial, MvPolynomial.aeval, MvPolynomial.aeval_map_algebraMap, P.map_invJacobianOfHasCoeffs, P.val, aeval_map_algebraMap, map_invJacobianOfHasCoeffs
-/
lemma aeval_invJacobianOfHasCoeffs :
    MvPolynomial.aeval P.val (P.invJacobianOfHasCoeffs R₀) = ↑(P.jacobian_isUnit.unit⁻¹) := by
  simpa [-map_invJacobianOfHasCoeffs, MvPolynomial.aeval_map_algebraMap] using
    congr(MvPolynomial.aeval P.val $(P.map_invJacobianOfHasCoeffs R₀))

/-- An arbitrarily chosen relation exhibiting the fact that `P.jacobian` is invertible,
provided `P.HasCoeffs R₀`. -/
noncomputable
/--
Definition of `jacobianRelationsOfHasCoeffs` / `jacobianRelationsOfHasCoeffs` 的定义

English:
definition jacobianRelationsOfHasCoeffs
  signature: (i : σ)
  body: (MvPolynomial.mem_range_map_iff_coeffs_subset.mpr
    ((Set.subset_iUnion _ i).trans (Set.subset_union_right.trans
      (HasCoeffs.coeffs_subset_range (P := P))))).choose

@[simp]

中文:
定义 jacobianRelationsOfHasCoeffs
  签名: (i : σ)
  定义体: (MvPolynomial.mem_range_map_iff_coeffs_subset.mpr
    ((Set.subset_iUnion _ i).trans (Set.subset_union_right.trans
      (HasCoeffs.coeffs_subset_range (P := P))))).choose

@[simp]

Depends on / 依赖: HasCoeffs, HasCoeffs.coeffs_subset_range, MvPolynomial, MvPolynomial.mem_range_map_iff_coeffs_subset.mpr, Set.subset_iUnion, Set.subset_union_right.trans, coeffs_subset_range, mem_range_map_iff_coeffs_subset, subset_iUnion, subset_union_right
-/
def jacobianRelationsOfHasCoeffs (i : σ) : MvPolynomial ι R₀ :=
  (MvPolynomial.mem_range_map_iff_coeffs_subset.mpr
    ((Set.subset_iUnion _ i).trans (Set.subset_union_right.trans
      (HasCoeffs.coeffs_subset_range (P := P))))).choose

@[simp]
/--
lemma `map_jacobianRelationsOfHasCoeffs` / 引理 `map_jacobianRelationsOfHasCoeffs`

English:
lemma map_jacobianRelationsOfHasCoeffs
  given: (i : σ)
  proof: (MvPolynomial.mem_range_map_iff_coeffs_subset.mpr
    ((Set.subset_iUnion _ i).trans (Set.subset_union_right.trans
      (HasCoeffs.coeffs_subset_range (P := P))))).choose_spec

中文:
引理 map_jacobianRelationsOfHasCoeffs
  条件: (i : σ)
  证明: (MvPolynomial.mem_range_map_iff_coeffs_subset.mpr
    ((Set.subset_iUnion _ i).trans (Set.subset_union_right.trans
      (HasCoeffs.coeffs_subset_range (P := P))))).choose_spec

Depends on / 依赖: HasCoeffs, HasCoeffs.coeffs_subset_range, MvPolynomial, MvPolynomial.mem_range_map_iff_coeffs_subset.mpr, Set.subset_iUnion, Set.subset_union_right.trans, choose_spec, coeffs_subset_range, mem_range_map_iff_coeffs_subset, subset_iUnion, subset_union_right
-/
lemma map_jacobianRelationsOfHasCoeffs (i : σ) :
    (P.jacobianRelationsOfHasCoeffs R₀ i).map (algebraMap R₀ R) = P.jacobianRelations i :=
  (MvPolynomial.mem_range_map_iff_coeffs_subset.mpr
    ((Set.subset_iUnion _ i).trans (Set.subset_union_right.trans
      (HasCoeffs.coeffs_subset_range (P := P))))).choose_spec

/--
lemma `sum_jacobianRelationsOfHasCoeffs_mul_relationOfHasCoeffs` / 引理 `sum_jacobianRelationsOfHasCoeffs_mul_relationOfHasCoeffs`

English:
lemma sum_jacobianRelationsOfHasCoeffs_mul_relationOfHasCoeffs
  given: [FaithfulSMul R₀ R] [Fintype σ]
  proof: by
  classical
  apply MvPolynomial.map_injective _ (FaithfulSMul.algebraMap_injective R₀ R)
  simp [P.map_relationOfHasCoeffs, jacobianRelations_spec]

中文:
引理 sum_jacobianRelationsOfHasCoeffs_mul_relationOfHasCoeffs
  条件: [忠实标量乘法 R₀ R] [有限类型 σ]
  证明: by
  classical
  apply MvPolynomial.map_injective _ (FaithfulSMul.algebraMap_injective R₀ R)
  simp [P.map_relationOfHasCoeffs, jacobianRelations_spec]

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, MvPolynomial, MvPolynomial.map_injective, P.map_relationOfHasCoeffs, algebraMap_injective, classical, jacobianRelations_spec, map_injective, map_relationOfHasCoeffs
-/
lemma sum_jacobianRelationsOfHasCoeffs_mul_relationOfHasCoeffs [FaithfulSMul R₀ R] [Fintype σ] :
    ∑ i, P.jacobianRelationsOfHasCoeffs R₀ i * P.relationOfHasCoeffs R₀ i =
      P.jacobianOfHasCoeffs R₀ * P.invJacobianOfHasCoeffs R₀ - 1 := by
  classical
  apply MvPolynomial.map_injective _ (FaithfulSMul.algebraMap_injective R₀ R)
  simp [P.map_relationOfHasCoeffs, jacobianRelations_spec]

set_option backward.isDefEq.respectTransparency false in
/-- The submersive presentation on `P.ModelOfHasCoeffs R₀` provided `P.HasCoeffs R₀`. -/
noncomputable
/--
Definition of `ofHasCoeffs` / `ofHasCoeffs` 的定义

English:
definition ofHasCoeffs
  signature: [FaithfulSMul R₀ R]
  body: P.toPreSubmersivePresentation.ofHasCoeffs R₀
  jacobian_isUnit := by
    classical
    let : Fintype σ := Fintype.ofFinite _
    have := congr((Ideal.Quotient.mk _ : _ ->+* P.ModelOfHasCoeffs R₀)
 (P.sum_jacobianRelationsOfHasCoeffs_mul_relationOfHasCoeffs R₀))
    simp only [map_sum, map_mul, Ideal.Quotient.mk_span_range, mul_zero, Finset.sum_const_zero,
      map_sub, map_one, @eq_comm (P.ModelOfHasCoeffs R₀) 0, sub_eq_zero] at this
    convert! IsUnit.of_mul_eq_one _ this
    rw [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
    simp [jacobianOfHasCoeffs]

中文:
定义 ofHasCoeffs
  签名: [忠实标量乘法 R₀ R]
  定义体: P.toPreSubmersivePresentation.ofHasCoeffs R₀
  jacobian_isUnit := by
    classical
    let : Fintype σ := Fintype.ofFinite _
    have := congr((Ideal.Quotient.mk _ : _ ->+* P.ModelOfHasCoeffs R₀)
 (P.sum_jacobianRelationsOfHasCoeffs_mul_relationOfHasCoeffs R₀))
    simp only [map_sum, map_mul, Ideal.Quotient.mk_span_range, mul_zero, Finset.sum_const_zero,
      map_sub, map_one, @eq_comm (P.ModelOfHasCoeffs R₀) 0, sub_eq_zero] at this
    convert! IsUnit.of_mul_eq_one _ this
    rw [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
    simp [jacobianOfHasCoeffs]

Depends on / 依赖: P.toPreSubmersivePresentation.ofHasCoeffs, ofHasCoeffs, toPreSubmersivePresentation
-/
def ofHasCoeffs [FaithfulSMul R₀ R] :
    Algebra.SubmersivePresentation R₀ (P.ModelOfHasCoeffs R₀) ι σ where
  __ := P.toPreSubmersivePresentation.ofHasCoeffs R₀
  jacobian_isUnit := by
    classical
    let : Fintype σ := Fintype.ofFinite _
    have := congr((Ideal.Quotient.mk _ : _ ->+* P.ModelOfHasCoeffs R₀)
 (P.sum_jacobianRelationsOfHasCoeffs_mul_relationOfHasCoeffs R₀))
    simp only [map_sum, map_mul, Ideal.Quotient.mk_span_range, mul_zero, Finset.sum_const_zero,
      map_sub, map_one, @eq_comm (P.ModelOfHasCoeffs R₀) 0, sub_eq_zero] at this
    convert! IsUnit.of_mul_eq_one _ this
    rw [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
    simp [jacobianOfHasCoeffs]

end Algebra.SubmersivePresentation
