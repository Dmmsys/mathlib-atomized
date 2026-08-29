/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# The standard basis

This file defines the standard basis `Pi.basis (s : ∀ j, Basis (ι j) R (M j))`,
which is the `Σ j, ι j`-indexed basis of `Π j, M j`. The basis vectors are given by
`Pi.basis s ⟨j, i⟩ j' = Pi.single j' (s j) i = if j = j' then s i else 0`.

The standard basis on `R^η`, i.e. `η → R` is called `Pi.basisFun`.

To give a concrete example, `Pi.single (i : Fin 3) (1 : R)`
gives the `i`th unit basis vector in `R³`, and `Pi.basisFun R (Fin 3)` proves
this is a basis over `Fin 3 → R`.

## Main definitions

- `Pi.basis s`: given a basis `s i` for each `M i`, the standard basis on `Π i, M i`
- `Pi.basisFun R η`: the standard basis on `R^η`, i.e. `η → R`, given by
  `Pi.basisFun R η i j = Pi.single i 1 j = if i = j then 1 else 0`.
- `Matrix.stdBasis R n m`: the standard basis on `Matrix n m R`, given by
  `Matrix.stdBasis R n m (i, j) i' j' = if (i, j) = (i', j') then 1 else 0`.

-/

@[expose] public section

open Function LinearMap Module Set Submodule

namespace Pi
variable {ι R M : Type*}

section Module

variable {η : Type*} {ιs : η -> Type*} {Ms : η -> Type*}

/--
theorem `linearIndependent_single` / 定理 `linearIndependent_single`

English:
theorem linearIndependent_single
  statement: [Semiring R] [forall i, AddCommMonoid (Ms i)] [forall i, Module R (Ms i)]
  proof: by
  convert! (DFinsupp.linearIndependent_single _ hs).map_injOn _ DFinsupp.injective_pi_lapply.injOn

中文:
定理 linearIndependent_single
  结论: [半环 R] [对任意 i, 加法交换幺半群 (Ms i)] [对任意 i, 模 R (Ms i)]
  证明: by
  convert! (DFinsupp.linearIndependent_single _ hs).map_injOn _ DFinsupp.injective_pi_lapply.injOn

Depends on / 依赖: DFinsupp, DFinsupp.injective_pi_lapply.injOn, DFinsupp.linearIndependent_single, convert, injective_pi_lapply, linearIndependent_single, map_injOn
-/
theorem linearIndependent_single [Semiring R] [forall i, AddCommMonoid (Ms i)] [forall i, Module R (Ms i)]
    [DecidableEq η] (v : forall j, ιs j -> Ms j) (hs : forall i, LinearIndependent R (v i)) :
    LinearIndependent R fun ji : Σ j, ιs j => Pi.single ji.1 (v ji.1 ji.2) := by
  convert! (DFinsupp.linearIndependent_single _ hs).map_injOn _ DFinsupp.injective_pi_lapply.injOn

/--
theorem `linearIndependent_single_one` / 定理 `linearIndependent_single_one`

English:
theorem linearIndependent_single_one
  given: (ι R : Type*) [Semiring R] [DecidableEq ι]
  proof: by
  rw [← linearIndependent_equiv (Equiv.sigmaPUnit ι)]
  exact Pi.linearIndependent_single (fun (_ : ι) (_ : Unit) => (1 : R))
 by simp +contextual [Fintype.linearIndependent_iffₛ]

中文:
定理 linearIndependent_single_one
  条件: (ι R : 类型) [半环 R] [DecidableEq ι]
  证明: by
  rw [← linearIndependent_equiv (Equiv.sigmaPUnit ι)]
  exact Pi.linearIndependent_single (fun (_ : ι) (_ : Unit) => (1 : R))
 by simp +contextual [Fintype.linearIndependent_iffₛ]

Depends on / 依赖: Equiv.sigmaPUnit, Fintype, Fintype.linearIndependent_iff, Pi.linearIndependent_single, contextual, linearIndependent_equiv, linearIndependent_single, sigmaPUnit
-/
theorem linearIndependent_single_one (ι R : Type*) [Semiring R] [DecidableEq ι] :
    LinearIndependent R (fun i : ι => Pi.single i (1 : R)) := by
  rw [← linearIndependent_equiv (Equiv.sigmaPUnit ι)]
  exact Pi.linearIndependent_single (fun (_ : ι) (_ : Unit) => (1 : R))
 by simp +contextual [Fintype.linearIndependent_iffₛ]

/--
lemma `linearIndependent_single_of_ne_zero` / 引理 `linearIndependent_single_of_ne_zero`

English:
lemma linearIndependent_single_of_ne_zero
  statement: [Ring R] [IsDomain R] [AddCommGroup M] [Module R M]
  proof: by
  rw [← linearIndependent_equiv (Equiv.sigmaPUnit ι)]
exact linearIndependent_single (fun i (_ : Unit) => v i) by simp +contextual [hv]

中文:
引理 linearIndependent_single_of_ne_zero
  结论: [环 R] [是整环 R] [加法交换群 M] [模 R M]
  证明: by
  rw [← linearIndependent_equiv (Equiv.sigmaPUnit ι)]
exact linearIndependent_single (fun i (_ : Unit) => v i) by simp +contextual [hv]

Depends on / 依赖: Equiv.sigmaPUnit, contextual, linearIndependent_equiv, linearIndependent_single, sigmaPUnit
-/
lemma linearIndependent_single_of_ne_zero [Ring R] [IsDomain R] [AddCommGroup M] [Module R M]
    [IsTorsionFree R M] [DecidableEq ι] {v : ι -> M} (hv : forall i, v i != 0) :
    LinearIndependent R fun i : ι => Pi.single i (v i) := by
  rw [← linearIndependent_equiv (Equiv.sigmaPUnit ι)]
exact linearIndependent_single (fun i (_ : Unit) => v i) by simp +contextual [hv]

variable [Semiring R] [forall i, AddCommMonoid (Ms i)] [forall i, Module R (Ms i)]

section Fintype

variable [Fintype η]

open LinearEquiv

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def basis (s : forall j, Basis (ιs j) R (Ms j))
  body: Basis.ofRepr
    ((LinearEquiv.piCongrRight fun j => (s j).repr) ≪≫ₗ
      (Finsupp.sigmaFinsuppLEquivPiFinsupp R).symm)

中文:
定义 noncomputable
  签名: def basis (s : 对任意 j, 基 (ιs j) R (Ms j))
  定义体: Basis.ofRepr
    ((LinearEquiv.piCongrRight fun j => (s j).repr) ≪≫ₗ
      (Finsupp.sigmaFinsuppLEquivPiFinsupp R).symm)
-/
protected noncomputable def basis (s : forall j, Basis (ιs j) R (Ms j)) :
    Basis (Σ j, ιs j) R (forall j, Ms j) :=
  Basis.ofRepr
    ((LinearEquiv.piCongrRight fun j => (s j).repr) ≪≫ₗ
      (Finsupp.sigmaFinsuppLEquivPiFinsupp R).symm)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `basis_repr_single` / 定理 `basis_repr_single`

English:
theorem basis_repr_single
  given: [DecidableEq η] (s : forall j, Basis (ιs j) R (Ms j)) (j i)
  proof: by
  classical
  ext ⟨j', i'⟩
  by_cases hj : j = j'
  · subst hj
    simp only [Pi.basis, LinearEquiv.trans_apply,
      LinearEquiv.piCongrRight, Finsupp.sigmaFinsuppLEquivPiFinsupp_symm_apply,
      Basis.repr_symm_apply, LinearEquiv.coe_mk]
    symm
    simp [Finsupp.single_apply]
  simp only [P

中文:
定理 basis_repr_single
  条件: [DecidableEq η] (s : 对任意 j, 基 (ιs j) R (Ms j)) (j i)
  证明: by
  classical
  ext ⟨j', i'⟩
  by_cases hj : j = j'
  · subst hj
    simp only [Pi.basis, LinearEquiv.trans_apply,
      LinearEquiv.piCongrRight, Finsupp.sigmaFinsuppLEquivPiFinsupp_symm_apply,
      Basis.repr_symm_apply, LinearEquiv.coe_mk]
    symm
    simp [Finsupp.single_apply]
  simp only [P

Depends on / 依赖: Basis.repr_symm_apply, Finsupp, Finsupp.sigmaFinsuppLEquivPiFinsupp_symm_apply, Finsupp.single_apply, Finsupp.single_eq_of_ne, Finsupp.zero_apply, LinearEquiv, LinearEquiv.coe_mk, LinearEquiv.piCongrRight, LinearEquiv.trans_apply, Ne.symm, Pi.basis, Pi.single_eq_of_ne, classical, coe_mk, map_zero, piCongrRight, repr_symm_apply, sigmaFinsuppLEquivPiFinsupp_symm_apply, single_apply
-/
theorem basis_repr_single [DecidableEq η] (s : forall j, Basis (ιs j) R (Ms j)) (j i) :
    (Pi.basis s).repr (Pi.single j (s j i)) = Finsupp.single ⟨j, i⟩ 1 := by
  classical
  ext ⟨j', i'⟩
  by_cases hj : j = j'
  · subst hj
    simp only [Pi.basis, LinearEquiv.trans_apply,
      LinearEquiv.piCongrRight, Finsupp.sigmaFinsuppLEquivPiFinsupp_symm_apply,
      Basis.repr_symm_apply, LinearEquiv.coe_mk]
    symm
    simp [Finsupp.single_apply]
  simp only [Pi.basis, LinearEquiv.trans_apply, Finsupp.sigmaFinsuppLEquivPiFinsupp_symm_apply,
    LinearEquiv.piCongrRight]
  dsimp
  rw [Pi.single_eq_of_ne (Ne.symm hj)]; rw [map_zero]; rw [Finsupp.zero_apply]; rw [Finsupp.single_eq_of_ne]
  rintro ⟨⟩
  contradiction

@[simp]
/--
theorem `basis_apply` / 定理 `basis_apply`

English:
theorem basis_apply
  given: [DecidableEq η] (s : forall j, Basis (ιs j) R (Ms j)) (ji)
  proof: Basis.apply_eq_iff.mpr (by simp)

@[simp]

中文:
定理 basis_apply
  条件: [DecidableEq η] (s : 对任意 j, 基 (ιs j) R (Ms j)) (ji)
  证明: Basis.apply_eq_iff.mpr (by simp)

@[simp]

Depends on / 依赖: Basis.apply_eq_iff.mpr, apply_eq_iff
-/
theorem basis_apply [DecidableEq η] (s : forall j, Basis (ιs j) R (Ms j)) (ji) :
    Pi.basis s ji = Pi.single ji.1 (s ji.1 ji.2) :=
  Basis.apply_eq_iff.mpr (by simp)

@[simp]
/--
theorem `basis_repr` / 定理 `basis_repr`

English:
theorem basis_repr
  given: (s : forall j, Basis (ιs j) R (Ms j)) (x) (ji)
  proof: rfl

中文:
定理 basis_repr
  条件: (s : 对任意 j, 基 (ιs j) R (Ms j)) (x) (ji)
  证明: rfl
-/
theorem basis_repr (s : forall j, Basis (ιs j) R (Ms j)) (x) (ji) :
    (Pi.basis s).repr x ji = (s ji.1).repr (x ji.1) ji.2 :=
  rfl

end Fintype

section

variable [Finite η]
variable (R η)

/--
Definition of `basisFun` / `basisFun` 的定义

English:
definition basisFun
  signature: : Basis η R (η -> R)
  body: Basis.ofEquivFun (LinearEquiv.refl _ _)

@[simp]

中文:
定义 basisFun
  签名: : 基 η R (η -> R)
  定义体: Basis.ofEquivFun (LinearEquiv.refl _ _)

@[simp]

Depends on / 依赖: Basis.ofEquivFun, LinearEquiv, LinearEquiv.refl, ofEquivFun
-/
noncomputable def basisFun : Basis η R (η -> R) :=
  Basis.ofEquivFun (LinearEquiv.refl _ _)

@[simp]
/--
theorem `basisFun_apply` / 定理 `basisFun_apply`

English:
theorem basisFun_apply
  given: [DecidableEq η] (i)
  proof: by
  simp only [basisFun, Basis.coe_ofEquivFun, LinearEquiv.refl_symm, LinearEquiv.refl_apply]

@[simp]

中文:
定理 basisFun_apply
  条件: [DecidableEq η] (i)
  证明: by
  simp only [basisFun, Basis.coe_ofEquivFun, LinearEquiv.refl_symm, LinearEquiv.refl_apply]

@[simp]

Depends on / 依赖: Basis.coe_ofEquivFun, LinearEquiv, LinearEquiv.refl_apply, LinearEquiv.refl_symm, basisFun, coe_ofEquivFun, refl_apply, refl_symm
-/
theorem basisFun_apply [DecidableEq η] (i) :
    basisFun R η i = Pi.single i 1 := by
  simp only [basisFun, Basis.coe_ofEquivFun, LinearEquiv.refl_symm, LinearEquiv.refl_apply]

@[simp]
/--
theorem `basisFun_repr` / 定理 `basisFun_repr`

English:
theorem basisFun_repr
  given: (x : η -> R) (i : η)
  statement: (Pi.basisFun R η).repr x i = x i
  proof: by simp [basisFun]

@[simp]

中文:
定理 basisFun_repr
  条件: (x : η -> R) (i : η)
  结论: (依赖函数类型.basisFun R η).repr x i = x i
  证明: by simp [basisFun]

@[simp]

Depends on / 依赖: basisFun
-/
theorem basisFun_repr (x : η -> R) (i : η) : (Pi.basisFun R η).repr x i = x i := by simp [basisFun]

@[simp]
/--
theorem `basisFun_equivFun` / 定理 `basisFun_equivFun`

English:
theorem basisFun_equivFun
  statement: (Pi.basisFun R η).equivFun = LinearEquiv.refl _ _
  proof: Basis.equivFun_ofEquivFun _

中文:
定理 basisFun_equivFun
  结论: (依赖函数类型.basisFun R η).equivFun = 线性等价.refl _ _
  证明: Basis.equivFun_ofEquivFun _

Depends on / 依赖: Basis.equivFun_ofEquivFun, equivFun_ofEquivFun
-/
theorem basisFun_equivFun : (Pi.basisFun R η).equivFun = LinearEquiv.refl _ _ :=
  Basis.equivFun_ofEquivFun _

variable {η}

-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/--
Definition of `spanSubset` / `spanSubset` 的定义

English:
definition spanSubset
  signature: (s : Set η)
  body: .span R (Pi.basisFun R η '' s)

中文:
定义 spanSubset
  签名: (s : 集合 η)
  定义体: .span R (Pi.basisFun R η '' s)

Depends on / 依赖: Pi.basisFun, basisFun
-/
noncomputable def spanSubset (s : Set η) : Submodule R (η -> R) :=
  .span R (Pi.basisFun R η '' s)

variable {R} {s : Set η}

/--
lemma `mem_spanSubset_iff` / 引理 `mem_spanSubset_iff`

English:
lemma mem_spanSubset_iff
  given: {s : Set η} {v : η -> R}
  proof: by
  simp [spanSubset, Module.Basis.mem_span_image, Finsupp.support_subset_iff]

中文:
引理 mem_spanSubset_iff
  条件: {s : 集合 η} {v : η -> R}
  证明: by
  simp [spanSubset, Module.Basis.mem_span_image, Finsupp.support_subset_iff]

Depends on / 依赖: Finsupp, Finsupp.support_subset_iff, Module, Module.Basis.mem_span_image, mem_span_image, spanSubset, support_subset_iff
-/
lemma mem_spanSubset_iff {s : Set η} {v : η -> R} :
    v in spanSubset R s ↔ forall i ∉ s, v i = 0 := by
  simp [spanSubset, Module.Basis.mem_span_image, Finsupp.support_subset_iff]

end

end Module

end Pi

/--
lemma `AlgHom.eq_piEvalAlgHom` / 引理 `AlgHom.eq_piEvalAlgHom`

English:
lemma AlgHom.eq_piEvalAlgHom
  statement: {k G : Type*} [CommSemiring k] [NoZeroDivisors k] [Nontrivial k]
  proof: by
  have h1 := map_one φ
  classical
  have := Fintype.ofFinite G
  simp only [← Finset.univ_sum_single (1 : G -> k), Pi.one_apply, map_sum] at h1
  obtain ⟨s, hs⟩ : exists (s : G), φ (Pi.single s 1) != 0 := by
    by_contra
    simp_all
  have h2 : forall t != s, φ (Pi.single t 1) = 0 := by
    re

中文:
引理 代数态射.eq_piEvalAlgHom
  结论: {k G : 类型} [交换半环 k] [无零因子 k] [非平凡 k]
  证明: by
  have h1 := map_one φ
  classical
  have := Fintype.ofFinite G
  simp only [← Finset.univ_sum_single (1 : G -> k), Pi.one_apply, map_sum] at h1
  obtain ⟨s, hs⟩ : exists (s : G), φ (Pi.single s 1) != 0 := by
    by_contra
    simp_all
  have h2 : forall t != s, φ (Pi.single t 1) = 0 := by
    re

Depends on / 依赖: Finset, Finset.univ_sum_single, Fintype, Fintype.ofFinite, Fintype.sum_eq_single, Pi.one_apply, Pi.single, classical, convert, eq_zero_or_eq_zero_of_mul_eq_zero, map_mul, map_one, map_sum, map_zero, ofFinite, one_apply, resolve_left, single, sum_eq_single, univ_sum_single
-/
lemma AlgHom.eq_piEvalAlgHom {k G : Type*} [CommSemiring k] [NoZeroDivisors k] [Nontrivial k]
    [Finite G] (φ : (G -> k) ->ₐ[k] k) : exists (s : G), φ = Pi.evalAlgHom _ _ s := by
  have h1 := map_one φ
  classical
  have := Fintype.ofFinite G
  simp only [← Finset.univ_sum_single (1 : G -> k), Pi.one_apply, map_sum] at h1
  obtain ⟨s, hs⟩ : exists (s : G), φ (Pi.single s 1) != 0 := by
    by_contra
    simp_all
  have h2 : forall t != s, φ (Pi.single t 1) = 0 := by
    refine fun _ _ => (eq_zero_or_eq_zero_of_mul_eq_zero ?_).resolve_left hs
    rw [← map_mul]
    convert! map_zero φ
    ext u
    by_cases u = s <;> simp_all
  have h3 : φ (Pi.single s 1) = 1 := by
    rwa [Fintype.sum_eq_single s h2] at h1
  use s
  refine AlgHom.toLinearMap_injective ((Pi.basisFun k G).ext fun t => ?_)
  by_cases t = s <;> simp_all

namespace Module

variable (ι R M N : Type*) [Finite ι] [CommSemiring R]
  [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]

/--
Definition of `piEquiv` / `piEquiv` 的定义

English:
definition piEquiv
  signature: : (ι -> M) ≃ₗ[R] ((ι -> R) ->ₗ[R] M)
  body: Basis.constr (Pi.basisFun R ι) R

中文:
定义 piEquiv
  签名: : (ι -> M) ≃ₗ[R] ((ι -> R) ->ₗ[R] M)
  定义体: Basis.constr (Pi.basisFun R ι) R

Depends on / 依赖: Basis.constr, Pi.basisFun, basisFun, constr
-/
noncomputable def piEquiv : (ι -> M) ≃ₗ[R] ((ι -> R) ->ₗ[R] M) := Basis.constr (Pi.basisFun R ι) R

/--
lemma `piEquiv_apply_apply` / 引理 `piEquiv_apply_apply`

English:
lemma piEquiv_apply_apply
  statement: (ι R M : Type*) [Fintype ι] [CommSemiring R]
  proof: by
  simp only [piEquiv, Basis.constr_apply_fintype, Basis.equivFun_apply]
  congr

中文:
引理 piEquiv_apply_apply
  结论: (ι R M : 类型) [有限类型 ι] [交换半环 R]
  证明: by
  simp only [piEquiv, Basis.constr_apply_fintype, Basis.equivFun_apply]
  congr

Depends on / 依赖: Basis.constr_apply_fintype, Basis.equivFun_apply, constr_apply_fintype, equivFun_apply, piEquiv
-/
lemma piEquiv_apply_apply (ι R M : Type*) [Fintype ι] [CommSemiring R]
    [AddCommMonoid M] [Module R M] (v : ι -> M) (w : ι -> R) :
    piEquiv ι R M v w = ∑ i, w i • v i := by
  simp only [piEquiv, Basis.constr_apply_fintype, Basis.equivFun_apply]
  congr

/--
lemma `range_piEquiv` / 引理 `range_piEquiv`

English:
lemma range_piEquiv
  given: (v : ι -> M)
  proof: Basis.constr_range _ _

中文:
引理 range_piEquiv
  条件: (v : ι -> M)
  证明: Basis.constr_range _ _
-/
@[simp] lemma range_piEquiv (v : ι -> M) :
    LinearMap.range (piEquiv ι R M v) = span R (range v) :=
  Basis.constr_range _ _

/--
lemma `surjective_piEquiv_apply_iff` / 引理 `surjective_piEquiv_apply_iff`

English:
lemma surjective_piEquiv_apply_iff
  given: (v : ι -> M)
  proof: by
  rw [← LinearMap.range_eq_top]; rw [range_piEquiv]

中文:
引理 surjective_piEquiv_apply_iff
  条件: (v : ι -> M)
  证明: by
  rw [← LinearMap.range_eq_top]; rw [range_piEquiv]
-/
@[simp] lemma surjective_piEquiv_apply_iff (v : ι -> M) :
    Surjective (piEquiv ι R M v) ↔ span R (range v) = ⊤ := by
  rw [← LinearMap.range_eq_top]; rw [range_piEquiv]

end Module

namespace Module.Free

variable {ι : Type*} (R : Type*) (M : Type*) [Semiring R] [AddCommMonoid M] [Module R M]

/--
Instance `_root_.Module.Free.pi` / 实例 `_root_.Module.Free.pi`

English:
instance _root_.Module.Free.pi
  signature: (M : ι -> Type*) [Finite ι] [forall i : ι, AddCommMonoid (M i)]
  body: let ⟨_⟩ := nonempty_fintype ι
.of_basis Pi.basis fun i => Module.Free.chooseBasis R (M i)

中文:
实例 _root_.模.自由.pi
  签名: (M : ι -> 类型) [有限 ι] [对任意 i : ι, 加法交换幺半群 (M i)]
  定义体: let ⟨_⟩ := nonempty_fintype ι
.of_basis Pi.basis fun i => Module.Free.chooseBasis R (M i)

Depends on / 依赖: Module, Module.Free.chooseBasis, Pi.basis, chooseBasis, nonempty_fintype, of_basis
-/
instance _root_.Module.Free.pi (M : ι -> Type*) [Finite ι] [forall i : ι, AddCommMonoid (M i)]
    [forall i : ι, Module R (M i)] [forall i : ι, Module.Free R (M i)] : Module.Free R (forall i, M i) :=
  let ⟨_⟩ := nonempty_fintype ι
.of_basis Pi.basis fun i => Module.Free.chooseBasis R (M i)

variable (ι) in
/--
Instance `_root_.Module.Free.function` / 实例 `_root_.Module.Free.function`

English:
instance _root_.Module.Free.function
  signature: [Finite ι] [Module.Free R M]
  body: Free.pi _ _

中文:
实例 _root_.模.自由.function
  签名: [有限 ι] [模.自由 R M]
  定义体: Free.pi _ _

Depends on / 依赖: Free.pi
-/
instance _root_.Module.Free.function [Finite ι] [Module.Free R M] : Module.Free R (ι -> M) :=
  Free.pi _ _

end Module.Free
