/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.LinearAlgebra.TensorProduct.Submodule
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.RingTheory.Flat.Basic

/-!

# Linearly disjoint submodules

This file contains basics about linearly disjoint submodules.

## Mathematical background

We adapt the definitions in <https://en.wikipedia.org/wiki/Linearly_disjoint>.
Let `R` be a commutative ring, `S` be an `R`-algebra (not necessarily commutative).
Let `M` and `N` be `R`-submodules in `S` (`Submodule R S`).

- `M` and `N` are linearly disjoint (`Submodule.LinearDisjoint M N` or simply
  `M.LinearDisjoint N`), if the natural `R`-linear map `M ⊗[R] N →ₗ[R] S`
  (`Submodule.mulMap M N`) induced by the multiplication in `S` is injective.

The following is the first equivalent characterization of linear disjointness:

- `Submodule.LinearDisjoint.linearIndependent_left_of_flat`:
  if `M` and `N` are linearly disjoint, if `N` is a flat `R`-module, then for any family of
  `R`-linearly independent elements `{ m_i }` of `M`, they are also `N`-linearly independent,
  in the sense that the `R`-linear map from `ι →₀ N` to `S` which maps `{ n_i }`
  to the sum of `m_i * n_i` (`Submodule.mulLeftMap N m`) is injective.

- `Submodule.LinearDisjoint.of_basis_left`:
  conversely, if `{ m_i }` is an `R`-basis of `M`, which is also `N`-linearly independent,
  then `M` and `N` are linearly disjoint.

Dually, we have:

- `Submodule.LinearDisjoint.linearIndependent_right_of_flat`:
  if `M` and `N` are linearly disjoint, if `M` is a flat `R`-module, then for any family of
  `R`-linearly independent elements `{ n_i }` of `N`, they are also `M`-linearly independent,
  in the sense that the `R`-linear map from `ι →₀ M` to `S` which maps `{ m_i }`
  to the sum of `m_i * n_i` (`Submodule.mulRightMap M n`) is injective.

- `Submodule.LinearDisjoint.of_basis_right`:
  conversely, if `{ n_i }` is an `R`-basis of `N`, which is also `M`-linearly independent,
  then `M` and `N` are linearly disjoint.

The following is the second equivalent characterization of linear disjointness:

- `Submodule.LinearDisjoint.linearIndependent_mul_of_flat`:
  if `M` and `N` are linearly disjoint, if one of `M` and `N` is flat, then for any family of
  `R`-linearly independent elements `{ m_i }` of `M`, and any family of
  `R`-linearly independent elements `{ n_j }` of `N`, the family `{ m_i * n_j }` in `S` is
  also `R`-linearly independent.

- `Submodule.LinearDisjoint.of_basis_mul`:
  conversely, if `{ m_i }` is an `R`-basis of `M`, if `{ n_i }` is an `R`-basis of `N`,
  such that the family `{ m_i * n_j }` in `S` is `R`-linearly independent,
  then `M` and `N` are linearly disjoint.

## Other main results

- `Submodule.LinearDisjoint.symm_of_commute`, `Submodule.linearDisjoint_comm_of_commute`:
  linear disjointness is symmetric under some commutative conditions.

- `Submodule.LinearDisjoint.map`:
  linear disjointness is preserved by injective algebra homomorphisms.

- `Submodule.linearDisjoint_op`:
  linear disjointness is preserved by taking multiplicative opposite.

- `Submodule.LinearDisjoint.of_le_left_of_flat`, `Submodule.LinearDisjoint.of_le_right_of_flat`,
  `Submodule.LinearDisjoint.of_le_of_flat_left`, `Submodule.LinearDisjoint.of_le_of_flat_right`:
  linear disjointness is preserved by taking submodules under some flatness conditions.

- `Submodule.LinearDisjoint.of_linearDisjoint_fg_left`,
  `Submodule.LinearDisjoint.of_linearDisjoint_fg_right`,
  `Submodule.LinearDisjoint.of_linearDisjoint_fg`:
  conversely, if any finitely generated submodules of `M` and `N` are linearly disjoint,
  then `M` and `N` themselves are linearly disjoint.

- `Submodule.LinearDisjoint.bot_left`, `Submodule.LinearDisjoint.bot_right`:
  the zero module is linearly disjoint with any other submodules.

- `Submodule.LinearDisjoint.one_left`, `Submodule.LinearDisjoint.one_right`:
  the image of `R` in `S` is linearly disjoint with any other submodules.

- `Submodule.LinearDisjoint.of_left_le_one_of_flat`,
  `Submodule.LinearDisjoint.of_right_le_one_of_flat`:
  if a submodule is contained in the image of `R` in `S`, then it is linearly disjoint with
  any other submodules, under some flatness conditions.

- `Submodule.LinearDisjoint.not_linearIndependent_pair_of_commute_of_flat`,
  `Submodule.LinearDisjoint.rank_inf_le_one_of_commute_of_flat`:
  if `M` and `N` are linearly disjoint, if one of `M` and `N` is flat, then any two commutative
  elements contained in the intersection of `M` and `N` are not `R`-linearly independent (namely,
  their span is not `R ^ 2`). In particular, if any two elements in the intersection of `M` and `N`
  are commutative, then the rank of the intersection of `M` and `N` is at most one.

  These results are stated using a bundled version (i.e. `a : ↥(M ⊓ N)`). If you want a non-bundled
  version (i.e. `a : S` with `ha : a ∈ M ⊓ N`), you may use `LinearIndependent.of_comp` and
  `FinVec.map_eq` (in `Mathlib/Data/Fin/Tuple/Reflection.lean`),
  see the following code snippet:

  ```
  have h := H.not_linearIndependent_pair_of_commute_of_flat hf ⟨a, ha⟩ ⟨b, hb⟩ hc
  contrapose! h
  refine .of_comp (M ⊓ N).subtype ?_
  convert h
  exact (FinVec.map_eq _ _).symm
  ```

- `Submodule.LinearDisjoint.rank_le_one_of_commute_of_flat_of_self`:
  if `M` and itself are linearly disjoint, if `M` is flat, if any two elements in `M`
  are commutative, then the rank of `M` is at most one.

The results with name containing "`of_commute`" also have corresponding specialized versions
assuming `S` is commutative.

## Tags

linearly disjoint, linearly independent, tensor product

-/

@[expose] public section

open Module
open scoped TensorProduct

noncomputable section

universe u v w

namespace Submodule

variable {R : Type u} {S : Type v}

section Semiring

variable [CommSemiring R] [Semiring S] [Algebra R S]

variable (M N : Submodule R S)

/-- Two submodules `M` and `N` in an algebra `S` over `R` are linearly disjoint if the natural map
`M ⊗[R] N →ₗ[R] S` induced by multiplication in `S` is injective. -/
@[mk_iff]
/--
Definition of `LinearDisjoint` / `LinearDisjoint` 的定义

English:
structure LinearDisjoint
  parameters: : Prop where
  axioms and operations (1):
    - injective : Function.Injective (mulMap M N)

中文:
结构 LinearDisjoint
  参数: : 命题 where
  公理与运算 (1 个):
    - injective : 函数.单射 (mulMap M N)
-/
protected structure LinearDisjoint : Prop where
  injective : Function.Injective (mulMap M N)

variable {M N}

/--
Definition of `LinearDisjoint.mulMap` / `LinearDisjoint.mulMap` 的定义

English:
definition LinearDisjoint.mulMap
  signature: (H : M.LinearDisjoint N)
  body: LinearEquiv.ofInjective (M.mulMap N) H.injective ≪≫ₗ LinearEquiv.ofEq _ _ (mulMap_range M N)

@[simp]

中文:
定义 LinearDisjoint.mulMap
  签名: (H : M.LinearDisjoint N)
  定义体: LinearEquiv.ofInjective (M.mulMap N) H.injective ≪≫ₗ LinearEquiv.ofEq _ _ (mulMap_range M N)

@[simp]
-/
protected def LinearDisjoint.mulMap (H : M.LinearDisjoint N) : M otimes[R] N ≃ₗ[R] M * N :=
  LinearEquiv.ofInjective (M.mulMap N) H.injective ≪≫ₗ LinearEquiv.ofEq _ _ (mulMap_range M N)

@[simp]
/--
theorem `LinearDisjoint.val_mulMap_tmul` / 定理 `LinearDisjoint.val_mulMap_tmul`

English:
theorem LinearDisjoint.val_mulMap_tmul
  given: (H : M.LinearDisjoint N) (m : M) (n : N)
  proof: rfl

@[nontriviality]

中文:
定理 LinearDisjoint.val_mulMap_tmul
  条件: (H : M.LinearDisjoint N) (m : M) (n : N)
  证明: rfl

@[nontriviality]
-/
theorem LinearDisjoint.val_mulMap_tmul (H : M.LinearDisjoint N) (m : M) (n : N) :
    (H.mulMap (m otimesₜ[R] n) : S) = m.1 * n.1 := rfl

@[nontriviality]
/--
theorem `LinearDisjoint.of_subsingleton` / 定理 `LinearDisjoint.of_subsingleton`

English:
theorem LinearDisjoint.of_subsingleton
  given: [Subsingleton R]
  statement: M.LinearDisjoint N
  proof: haveI : Subsingleton S := Module.subsingleton R S
  ⟨Function.injective_of_subsingleton _⟩

@[nontriviality]

中文:
定理 LinearDisjoint.of_subsingleton
  条件: [子单例 R]
  结论: M.LinearDisjoint N
  证明: haveI : Subsingleton S := Module.subsingleton R S
  ⟨Function.injective_of_subsingleton _⟩

@[nontriviality]

Depends on / 依赖: Function, Function.injective_of_subsingleton, Module, Module.subsingleton, Subsingleton, injective_of_subsingleton, subsingleton
-/
theorem LinearDisjoint.of_subsingleton [Subsingleton R] : M.LinearDisjoint N :=
  haveI : Subsingleton S := Module.subsingleton R S
  ⟨Function.injective_of_subsingleton _⟩

@[nontriviality]
/--
theorem `LinearDisjoint.of_subsingleton_top` / 定理 `LinearDisjoint.of_subsingleton_top`

English:
theorem LinearDisjoint.of_subsingleton_top
  given: [Subsingleton S]
  statement: M.LinearDisjoint N
  proof: ⟨Function.injective_of_subsingleton _⟩

中文:
定理 LinearDisjoint.of_subsingleton_top
  条件: [子单例 S]
  结论: M.LinearDisjoint N
  证明: ⟨Function.injective_of_subsingleton _⟩

Depends on / 依赖: Function, Function.injective_of_subsingleton, injective_of_subsingleton
-/
theorem LinearDisjoint.of_subsingleton_top [Subsingleton S] : M.LinearDisjoint N :=
  ⟨Function.injective_of_subsingleton _⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `linearDisjoint_op` / 定理 `linearDisjoint_op`

English:
theorem linearDisjoint_op
  proof: by
  simp only [linearDisjoint_iff, mulMap_op, LinearMap.coe_comp,
    LinearEquiv.coe_coe, EquivLike.comp_injective, EquivLike.injective_comp]

alias ⟨LinearDisjoint.op, LinearDisjoint.of_op⟩ := linearDisjoint_op

中文:
定理 linearDisjoint_op
  证明: by
  simp only [linearDisjoint_iff, mulMap_op, LinearMap.coe_comp,
    LinearEquiv.coe_coe, EquivLike.comp_injective, EquivLike.injective_comp]

alias ⟨LinearDisjoint.op, LinearDisjoint.of_op⟩ := linearDisjoint_op

Depends on / 依赖: EquivLike, EquivLike.comp_injective, EquivLike.injective_comp, LinearEquiv, LinearEquiv.coe_coe, LinearMap, LinearMap.coe_comp, coe_coe, coe_comp, comp_injective, injective_comp, linearDisjoint_iff, mulMap_op
-/
theorem linearDisjoint_op :
    M.LinearDisjoint N ↔ (equivOpposite.symm (MulOpposite.op N)).LinearDisjoint
      (equivOpposite.symm (MulOpposite.op M)) := by
  simp only [linearDisjoint_iff, mulMap_op, LinearMap.coe_comp,
    LinearEquiv.coe_coe, EquivLike.comp_injective, EquivLike.injective_comp]

alias ⟨LinearDisjoint.op, LinearDisjoint.of_op⟩ := linearDisjoint_op

/--
theorem `LinearDisjoint.symm_of_commute` / 定理 `LinearDisjoint.symm_of_commute`

English:
theorem LinearDisjoint.symm_of_commute
  statement: (H : M.LinearDisjoint N)
  proof: by
  rw [linearDisjoint_iff]; rw [mulMap_comm_of_commute M N hc]
  exact ((TensorProduct.comm R N M).toEquiv.injective_comp _).2 H.injective

中文:
定理 LinearDisjoint.symm_of_commute
  结论: (H : M.LinearDisjoint N)
  证明: by
  rw [linearDisjoint_iff]; rw [mulMap_comm_of_commute M N hc]
  exact ((TensorProduct.comm R N M).toEquiv.injective_comp _).2 H.injective

Depends on / 依赖: H.injective, TensorProduct, TensorProduct.comm, injective, injective_comp, linearDisjoint_iff, mulMap_comm_of_commute, toEquiv, toEquiv.injective_comp
-/
theorem LinearDisjoint.symm_of_commute (H : M.LinearDisjoint N)
    (hc : forall (m : M) (n : N), Commute m.1 n.1) : N.LinearDisjoint M := by
  rw [linearDisjoint_iff]; rw [mulMap_comm_of_commute M N hc]
  exact ((TensorProduct.comm R N M).toEquiv.injective_comp _).2 H.injective

/--
theorem `linearDisjoint_comm_of_commute` / 定理 `linearDisjoint_comm_of_commute`

English:
theorem linearDisjoint_comm_of_commute
  proof: ⟨fun H => H.symm_of_commute hc, fun H => H.symm_of_commute fun _ _ => (hc _ _).symm⟩

中文:
定理 linearDisjoint_comm_of_commute
  证明: ⟨fun H => H.symm_of_commute hc, fun H => H.symm_of_commute fun _ _ => (hc _ _).symm⟩

Depends on / 依赖: H.symm_of_commute, symm_of_commute
-/
theorem linearDisjoint_comm_of_commute
    (hc : forall (m : M) (n : N), Commute m.1 n.1) : M.LinearDisjoint N ↔ N.LinearDisjoint M :=
  ⟨fun H => H.symm_of_commute hc, fun H => H.symm_of_commute fun _ _ => (hc _ _).symm⟩

namespace LinearDisjoint

/--
theorem `map` / 定理 `map`

English:
theorem map
  statement: (H : M.LinearDisjoint N) {T : Type w} [Semiring T] [Algebra R T]
  proof: by
  rw [linearDisjoint_iff] at H ⊢
  have := hf.comp H
  rw [← coe_mulMap_comp_eq] at this
  refine this.of_comp_right ?_
  apply TensorProduct.map_surjective <;> exact LinearMap.submoduleMap_surjective _ _

中文:
定理 map
  结论: (H : M.LinearDisjoint N) {T : 类型 w} [半环 T] [代数 R T]
  证明: by
  rw [linearDisjoint_iff] at H ⊢
  have := hf.comp H
  rw [← coe_mulMap_comp_eq] at this
  refine this.of_comp_right ?_
  apply TensorProduct.map_surjective <;> exact LinearMap.submoduleMap_surjective _ _

Depends on / 依赖: LinearMap, LinearMap.submoduleMap_surjective, TensorProduct, TensorProduct.map_surjective, coe_mulMap_comp_eq, hf.comp, linearDisjoint_iff, map_surjective, of_comp_right, submoduleMap_surjective, this.of_comp_right
-/
theorem map (H : M.LinearDisjoint N) {T : Type w} [Semiring T] [Algebra R T]
    (f : S ->ₐ[R] T) (hf : Function.Injective f) :
    (M.map (f : S ->ₗ[R] T)).LinearDisjoint (N.map (f : S ->ₗ[R] T)) := by
  rw [linearDisjoint_iff] at H ⊢
  have := hf.comp H
  rw [← coe_mulMap_comp_eq] at this
  refine this.of_comp_right ?_
  apply TensorProduct.map_surjective <;> exact LinearMap.submoduleMap_surjective _ _

variable (M N)

/--
theorem `of_basis_left'` / 定理 `of_basis_left'`

English:
theorem of_basis_left'
  statement: {ι : Type*} (m : Basis ι R M)
  proof: by
  classical simp_rw [mulLeftMap_eq_mulMap_comp, ← Basis.coe_repr_symm,
    ← LinearEquiv.coe_rTensor, LinearEquiv.comp_coe, LinearMap.coe_comp,
    LinearEquiv.coe_coe, EquivLike.injective_comp] at H
  exact ⟨H⟩

中文:
定理 of_basis_left'
  结论: {ι : 类型} (m : 基 ι R M)
  证明: by
  classical simp_rw [mulLeftMap_eq_mulMap_comp, ← Basis.coe_repr_symm,
    ← LinearEquiv.coe_rTensor, LinearEquiv.comp_coe, LinearMap.coe_comp,
    LinearEquiv.coe_coe, EquivLike.injective_comp] at H
  exact ⟨H⟩

Depends on / 依赖: Basis.coe_repr_symm, EquivLike, EquivLike.injective_comp, LinearEquiv, LinearEquiv.coe_coe, LinearEquiv.coe_rTensor, LinearEquiv.comp_coe, LinearMap, LinearMap.coe_comp, classical, coe_coe, coe_comp, coe_rTensor, coe_repr_symm, comp_coe, injective_comp, mulLeftMap_eq_mulMap_comp, simp_rw
-/
theorem of_basis_left' {ι : Type*} (m : Basis ι R M)
    (H : Function.Injective (mulLeftMap N m)) : M.LinearDisjoint N := by
  classical simp_rw [mulLeftMap_eq_mulMap_comp, ← Basis.coe_repr_symm,
    ← LinearEquiv.coe_rTensor, LinearEquiv.comp_coe, LinearMap.coe_comp,
    LinearEquiv.coe_coe, EquivLike.injective_comp] at H
  exact ⟨H⟩

/--
theorem `of_basis_right'` / 定理 `of_basis_right'`

English:
theorem of_basis_right'
  statement: {ι : Type*} (n : Basis ι R N)
  proof: by
  classical simp_rw [mulRightMap_eq_mulMap_comp, ← Basis.coe_repr_symm,
    ← LinearEquiv.coe_lTensor, LinearEquiv.comp_coe, LinearMap.coe_comp,
    LinearEquiv.coe_coe, EquivLike.injective_comp] at H
  exact ⟨H⟩

中文:
定理 of_basis_right'
  结论: {ι : 类型} (n : 基 ι R N)
  证明: by
  classical simp_rw [mulRightMap_eq_mulMap_comp, ← Basis.coe_repr_symm,
    ← LinearEquiv.coe_lTensor, LinearEquiv.comp_coe, LinearMap.coe_comp,
    LinearEquiv.coe_coe, EquivLike.injective_comp] at H
  exact ⟨H⟩

Depends on / 依赖: Basis.coe_repr_symm, EquivLike, EquivLike.injective_comp, LinearEquiv, LinearEquiv.coe_coe, LinearEquiv.coe_lTensor, LinearEquiv.comp_coe, LinearMap, LinearMap.coe_comp, classical, coe_coe, coe_comp, coe_lTensor, coe_repr_symm, comp_coe, injective_comp, mulRightMap_eq_mulMap_comp, simp_rw
-/
theorem of_basis_right' {ι : Type*} (n : Basis ι R N)
    (H : Function.Injective (mulRightMap M n)) : M.LinearDisjoint N := by
  classical simp_rw [mulRightMap_eq_mulMap_comp, ← Basis.coe_repr_symm,
    ← LinearEquiv.coe_lTensor, LinearEquiv.comp_coe, LinearMap.coe_comp,
    LinearEquiv.coe_coe, EquivLike.injective_comp] at H
  exact ⟨H⟩

/--
theorem `of_basis_mul'` / 定理 `of_basis_mul'`

English:
theorem of_basis_mul'
  statement: {κ ι : Type*} (m : Basis κ R M) (n : Basis ι R N)
  proof: by
  let i0 := (finsuppTensorFinsupp' R κ ι).symm
  let i1 := TensorProduct.congr m.repr n.repr
  let i := mulMap M N ∘ₗ (i0.trans i1.symm).toLinearMap
  have : i = Finsupp.linearCombination R fun i : κ × ι => (m i.1 * n i.2 : S) := by
    ext x
    simp [i, i0, i1, finsuppTensorFinsupp'_symm_single

中文:
定理 of_basis_mul'
  结论: {κ ι : 类型} (m : 基 κ R M) (n : 基 ι R N)
  证明: by
  let i0 := (finsuppTensorFinsupp' R κ ι).symm
  let i1 := TensorProduct.congr m.repr n.repr
  let i := mulMap M N ∘ₗ (i0.trans i1.symm).toLinearMap
  have : i = Finsupp.linearCombination R fun i : κ × ι => (m i.1 * n i.2 : S) := by
    ext x
    simp [i, i0, i1, finsuppTensorFinsupp'_symm_single

Depends on / 依赖: EquivLike, EquivLike.injective_comp, Finsupp, Finsupp.linearCombination, LinearEquiv, LinearEquiv.coe_coe, LinearMap, LinearMap.coe_comp, TensorProduct, TensorProduct.congr, _symm_single_eq_single_one_tmul, coe_coe, coe_comp, finsuppTensorFinsupp, i0.trans, i1.symm, injective_comp, linearCombination, m.repr, mulMap
-/
theorem of_basis_mul' {κ ι : Type*} (m : Basis κ R M) (n : Basis ι R N)
    (H : Function.Injective (Finsupp.linearCombination R fun i : κ × ι => (m i.1 * n i.2 : S))) :
    M.LinearDisjoint N := by
  let i0 := (finsuppTensorFinsupp' R κ ι).symm
  let i1 := TensorProduct.congr m.repr n.repr
  let i := mulMap M N ∘ₗ (i0.trans i1.symm).toLinearMap
  have : i = Finsupp.linearCombination R fun i : κ × ι => (m i.1 * n i.2 : S) := by
    ext x
    simp [i, i0, i1, finsuppTensorFinsupp'_symm_single_eq_single_one_tmul]
  simp_rw [← this, i, LinearMap.coe_comp, LinearEquiv.coe_coe, EquivLike.injective_comp] at H
  exact ⟨H⟩

/--
theorem `bot_left` / 定理 `bot_left`

English:
theorem bot_left
  statement: (⊥ : Submodule R S).LinearDisjoint N
  proof: ⟨Function.injective_of_subsingleton _⟩

中文:
定理 bot_left
  结论: (⊥ : 子模 R S).LinearDisjoint N
  证明: ⟨Function.injective_of_subsingleton _⟩

Depends on / 依赖: Function, Function.injective_of_subsingleton, injective_of_subsingleton
-/
theorem bot_left : (⊥ : Submodule R S).LinearDisjoint N :=
  ⟨Function.injective_of_subsingleton _⟩

/--
theorem `bot_right` / 定理 `bot_right`

English:
theorem bot_right
  statement: M.LinearDisjoint (⊥ : Submodule R S)
  proof: ⟨Function.injective_of_subsingleton _⟩

中文:
定理 bot_right
  结论: M.LinearDisjoint (⊥ : 子模 R S)
  证明: ⟨Function.injective_of_subsingleton _⟩

Depends on / 依赖: Function, Function.injective_of_subsingleton, injective_of_subsingleton
-/
theorem bot_right : M.LinearDisjoint (⊥ : Submodule R S) :=
  ⟨Function.injective_of_subsingleton _⟩

/--
theorem `one_left` / 定理 `one_left`

English:
theorem one_left
  statement: (1 : Submodule R S).LinearDisjoint N
  proof: by
  rw [linearDisjoint_iff]; rw [← Algebra.toSubmodule_bot]; rw [mulMap_one_left_eq]
  exact N.injective_subtype.comp N.lTensorOne.injective

中文:
定理 one_left
  结论: (1 : 子模 R S).LinearDisjoint N
  证明: by
  rw [linearDisjoint_iff]; rw [← Algebra.toSubmodule_bot]; rw [mulMap_one_left_eq]
  exact N.injective_subtype.comp N.lTensorOne.injective

Depends on / 依赖: Algebra, Algebra.toSubmodule_bot, N.injective_subtype.comp, N.lTensorOne.injective, injective, injective_subtype, lTensorOne, linearDisjoint_iff, mulMap_one_left_eq, toSubmodule_bot
-/
theorem one_left : (1 : Submodule R S).LinearDisjoint N := by
  rw [linearDisjoint_iff]; rw [← Algebra.toSubmodule_bot]; rw [mulMap_one_left_eq]
  exact N.injective_subtype.comp N.lTensorOne.injective

/--
theorem `one_right` / 定理 `one_right`

English:
theorem one_right
  statement: M.LinearDisjoint (1 : Submodule R S)
  proof: by
  rw [linearDisjoint_iff]; rw [← Algebra.toSubmodule_bot]; rw [mulMap_one_right_eq]
  exact M.injective_subtype.comp M.rTensorOne.injective

中文:
定理 one_right
  结论: M.LinearDisjoint (1 : 子模 R S)
  证明: by
  rw [linearDisjoint_iff]; rw [← Algebra.toSubmodule_bot]; rw [mulMap_one_right_eq]
  exact M.injective_subtype.comp M.rTensorOne.injective

Depends on / 依赖: Algebra, Algebra.toSubmodule_bot, M.injective_subtype.comp, M.rTensorOne.injective, injective, injective_subtype, linearDisjoint_iff, mulMap_one_right_eq, rTensorOne, toSubmodule_bot
-/
theorem one_right : M.LinearDisjoint (1 : Submodule R S) := by
  rw [linearDisjoint_iff]; rw [← Algebra.toSubmodule_bot]; rw [mulMap_one_right_eq]
  exact M.injective_subtype.comp M.rTensorOne.injective

/--
theorem `of_linearDisjoint_fg_left` / 定理 `of_linearDisjoint_fg_left`

English:
theorem of_linearDisjoint_fg_left
  proof: (linearDisjoint_iff _ _).2 fun x y hxy => by
  obtain ⟨M', hM, hFG, h⟩ :=
    TensorProduct.exists_finite_submodule_left_of_setFinite' {x, y} (Set.toFinite _)
  rw [Module.Finite.iff_fg] at hFG
  obtain ⟨x', hx'⟩ := h (show x in {x, y} by simp)
  obtain ⟨y', hy'⟩ := h (show y in {x, y} by simp)
  rw

中文:
定理 of_linearDisjoint_fg_left
  证明: (linearDisjoint_iff _ _).2 fun x y hxy => by
  obtain ⟨M', hM, hFG, h⟩ :=
    TensorProduct.exists_finite_submodule_left_of_setFinite' {x, y} (Set.toFinite _)
  rw [Module.Finite.iff_fg] at hFG
  obtain ⟨x', hx'⟩ := h (show x in {x, y} by simp)
  obtain ⟨y', hy'⟩ := h (show y in {x, y} by simp)
  rw

Depends on / 依赖: Finite, Module, Module.Finite.iff_fg, Set.toFinite, TensorProduct, TensorProduct.exists_finite_submodule_left_of_setFinite, exists_finite_submodule_left_of_setFinite, iff_fg, injective, linearDisjoint_iff, mulMap_comp_rTensor, toFinite
-/
theorem of_linearDisjoint_fg_left
    (H : forall M' : Submodule R S, M' <= M -> M'.FG -> M'.LinearDisjoint N) :
    M.LinearDisjoint N := (linearDisjoint_iff _ _).2 fun x y hxy => by
  obtain ⟨M', hM, hFG, h⟩ :=
    TensorProduct.exists_finite_submodule_left_of_setFinite' {x, y} (Set.toFinite _)
  rw [Module.Finite.iff_fg] at hFG
  obtain ⟨x', hx'⟩ := h (show x in {x, y} by simp)
  obtain ⟨y', hy'⟩ := h (show y in {x, y} by simp)
  rw [← hx']; rw [← hy']; congr
  exact (H M' hM hFG).injective (by simp [← mulMap_comp_rTensor _ hM, hx', hy', hxy])

/--
theorem `of_linearDisjoint_fg_right` / 定理 `of_linearDisjoint_fg_right`

English:
theorem of_linearDisjoint_fg_right
  proof: (linearDisjoint_iff _ _).2 fun x y hxy => by
  obtain ⟨N', hN, hFG, h⟩ :=
    TensorProduct.exists_finite_submodule_right_of_setFinite' {x, y} (Set.toFinite _)
  rw [Module.Finite.iff_fg] at hFG
  obtain ⟨x', hx'⟩ := h (show x in {x, y} by simp)
  obtain ⟨y', hy'⟩ := h (show y in {x, y} by simp)
  r

中文:
定理 of_linearDisjoint_fg_right
  证明: (linearDisjoint_iff _ _).2 fun x y hxy => by
  obtain ⟨N', hN, hFG, h⟩ :=
    TensorProduct.exists_finite_submodule_right_of_setFinite' {x, y} (Set.toFinite _)
  rw [Module.Finite.iff_fg] at hFG
  obtain ⟨x', hx'⟩ := h (show x in {x, y} by simp)
  obtain ⟨y', hy'⟩ := h (show y in {x, y} by simp)
  r

Depends on / 依赖: Finite, Module, Module.Finite.iff_fg, Set.toFinite, TensorProduct, TensorProduct.exists_finite_submodule_right_of_setFinite, exists_finite_submodule_right_of_setFinite, iff_fg, injective, linearDisjoint_iff, mulMap_comp_lTensor, toFinite
-/
theorem of_linearDisjoint_fg_right
    (H : forall N' : Submodule R S, N' <= N -> N'.FG -> M.LinearDisjoint N') :
    M.LinearDisjoint N := (linearDisjoint_iff _ _).2 fun x y hxy => by
  obtain ⟨N', hN, hFG, h⟩ :=
    TensorProduct.exists_finite_submodule_right_of_setFinite' {x, y} (Set.toFinite _)
  rw [Module.Finite.iff_fg] at hFG
  obtain ⟨x', hx'⟩ := h (show x in {x, y} by simp)
  obtain ⟨y', hy'⟩ := h (show y in {x, y} by simp)
  rw [← hx']; rw [← hy']; congr
  exact (H N' hN hFG).injective (by simp [← mulMap_comp_lTensor _ hN, hx', hy', hxy])

/--
theorem `of_linearDisjoint_fg` / 定理 `of_linearDisjoint_fg`

English:
theorem of_linearDisjoint_fg
  proof: of_linearDisjoint_fg_left _ _ fun _ hM hM' =>
    of_linearDisjoint_fg_right _ _ fun _ hN hN' => H _ _ hM hN hM' hN'

中文:
定理 of_linearDisjoint_fg
  证明: of_linearDisjoint_fg_left _ _ fun _ hM hM' =>
    of_linearDisjoint_fg_right _ _ fun _ hN hN' => H _ _ hM hN hM' hN'

Depends on / 依赖: of_linearDisjoint_fg_left, of_linearDisjoint_fg_right
-/
theorem of_linearDisjoint_fg
    (H : forall (M' N' : Submodule R S), M' <= M -> N' <= N -> M'.FG -> N'.FG -> M'.LinearDisjoint N') :
    M.LinearDisjoint N :=
  of_linearDisjoint_fg_left _ _ fun _ hM hM' =>
    of_linearDisjoint_fg_right _ _ fun _ hN hN' => H _ _ hM hN hM' hN'

end LinearDisjoint

end Semiring

section CommSemiring

variable [CommSemiring R] [CommSemiring S] [Algebra R S]

variable {M N : Submodule R S}

/--
theorem `LinearDisjoint.symm` / 定理 `LinearDisjoint.symm`

English:
theorem LinearDisjoint.symm
  given: (H : M.LinearDisjoint N)
  statement: N.LinearDisjoint M
  proof: H.symm_of_commute fun _ _ => mul_comm _ _

中文:
定理 LinearDisjoint.symm
  条件: (H : M.LinearDisjoint N)
  结论: N.LinearDisjoint M
  证明: H.symm_of_commute fun _ _ => mul_comm _ _
-/
theorem LinearDisjoint.symm (H : M.LinearDisjoint N) : N.LinearDisjoint M :=
  H.symm_of_commute fun _ _ => mul_comm _ _

/--
theorem `linearDisjoint_comm` / 定理 `linearDisjoint_comm`

English:
theorem linearDisjoint_comm
  statement: M.LinearDisjoint N ↔ N.LinearDisjoint M
  proof: ⟨LinearDisjoint.symm, LinearDisjoint.symm⟩

中文:
定理 linearDisjoint_comm
  结论: M.LinearDisjoint N ↔ N.LinearDisjoint M
  证明: ⟨LinearDisjoint.symm, LinearDisjoint.symm⟩

Depends on / 依赖: LinearDisjoint, LinearDisjoint.symm
-/
theorem linearDisjoint_comm : M.LinearDisjoint N ↔ N.LinearDisjoint M :=
  ⟨LinearDisjoint.symm, LinearDisjoint.symm⟩

end CommSemiring

section Ring

namespace LinearDisjoint

variable [CommRing R] [Ring S] [Algebra R S]

variable (M N : Submodule R S)

variable {M N} in
/--
theorem `linearIndependent_left_of_flat` / 定理 `linearIndependent_left_of_flat`

English:
theorem linearIndependent_left_of_flat
  statement: (H : M.LinearDisjoint N) [Module.Flat R N]
  proof: by
  refine LinearMap.ker_eq_bot_of_injective ?_
  classical simp_rw [mulLeftMap_eq_mulMap_comp, LinearMap.coe_comp, LinearEquiv.coe_coe,
    ← Function.comp_assoc, EquivLike.injective_comp]
  rw [LinearIndependent] at hm
  exact H.injective.comp (Module.Flat.rTensor_preserves_injective_linearMap (M

中文:
定理 linearIndependent_left_of_flat
  结论: (H : M.LinearDisjoint N) [模.平坦 R N]
  证明: by
  refine LinearMap.ker_eq_bot_of_injective ?_
  classical simp_rw [mulLeftMap_eq_mulMap_comp, LinearMap.coe_comp, LinearEquiv.coe_coe,
    ← Function.comp_assoc, EquivLike.injective_comp]
  rw [LinearIndependent] at hm
  exact H.injective.comp (Module.Flat.rTensor_preserves_injective_linearMap (M

Depends on / 依赖: EquivLike, EquivLike.injective_comp, Function, Function.comp_assoc, H.injective.comp, LinearEquiv, LinearEquiv.coe_coe, LinearIndependent, LinearMap, LinearMap.coe_comp, LinearMap.ker_eq_bot_of_injective, Module, Module.Flat.rTensor_preserves_injective_linearMap, classical, coe_coe, coe_comp, comp_assoc, injective, injective_comp, ker_eq_bot_of_injective
-/
theorem linearIndependent_left_of_flat (H : M.LinearDisjoint N) [Module.Flat R N]
    {ι : Type*} {m : ι -> M} (hm : LinearIndependent R m) : LinearMap.ker (mulLeftMap N m) = ⊥ := by
  refine LinearMap.ker_eq_bot_of_injective ?_
  classical simp_rw [mulLeftMap_eq_mulMap_comp, LinearMap.coe_comp, LinearEquiv.coe_coe,
    ← Function.comp_assoc, EquivLike.injective_comp]
  rw [LinearIndependent] at hm
  exact H.injective.comp (Module.Flat.rTensor_preserves_injective_linearMap (M := N) _ hm)

/--
theorem `of_basis_left` / 定理 `of_basis_left`

English:
theorem of_basis_left
  statement: {ι : Type*} (m : Basis ι R M)
  proof: of_basis_left' M N m (LinearMap.ker_eq_bot.1 H)

中文:
定理 of_basis_left
  结论: {ι : 类型} (m : 基 ι R M)
  证明: of_basis_left' M N m (LinearMap.ker_eq_bot.1 H)

Depends on / 依赖: LinearMap, LinearMap.ker_eq_bot, ker_eq_bot, of_basis_left
-/
theorem of_basis_left {ι : Type*} (m : Basis ι R M)
    (H : LinearMap.ker (mulLeftMap N m) = ⊥) : M.LinearDisjoint N :=
  of_basis_left' M N m (LinearMap.ker_eq_bot.1 H)

variable {M N} in
/--
theorem `linearIndependent_right_of_flat` / 定理 `linearIndependent_right_of_flat`

English:
theorem linearIndependent_right_of_flat
  statement: (H : M.LinearDisjoint N) [Module.Flat R M]
  proof: by
  refine LinearMap.ker_eq_bot_of_injective ?_
  classical simp_rw [mulRightMap_eq_mulMap_comp, LinearMap.coe_comp, LinearEquiv.coe_coe,
    ← Function.comp_assoc, EquivLike.injective_comp]
  rw [LinearIndependent] at hn
  exact H.injective.comp (Module.Flat.lTensor_preserves_injective_linearMap (

中文:
定理 linearIndependent_right_of_flat
  结论: (H : M.LinearDisjoint N) [模.平坦 R M]
  证明: by
  refine LinearMap.ker_eq_bot_of_injective ?_
  classical simp_rw [mulRightMap_eq_mulMap_comp, LinearMap.coe_comp, LinearEquiv.coe_coe,
    ← Function.comp_assoc, EquivLike.injective_comp]
  rw [LinearIndependent] at hn
  exact H.injective.comp (Module.Flat.lTensor_preserves_injective_linearMap (

Depends on / 依赖: EquivLike, EquivLike.injective_comp, Function, Function.comp_assoc, H.injective.comp, LinearEquiv, LinearEquiv.coe_coe, LinearIndependent, LinearMap, LinearMap.coe_comp, LinearMap.ker_eq_bot_of_injective, Module, Module.Flat.lTensor_preserves_injective_linearMap, classical, coe_coe, coe_comp, comp_assoc, injective, injective_comp, ker_eq_bot_of_injective
-/
theorem linearIndependent_right_of_flat (H : M.LinearDisjoint N) [Module.Flat R M]
    {ι : Type*} {n : ι -> N} (hn : LinearIndependent R n) : LinearMap.ker (mulRightMap M n) = ⊥ := by
  refine LinearMap.ker_eq_bot_of_injective ?_
  classical simp_rw [mulRightMap_eq_mulMap_comp, LinearMap.coe_comp, LinearEquiv.coe_coe,
    ← Function.comp_assoc, EquivLike.injective_comp]
  rw [LinearIndependent] at hn
  exact H.injective.comp (Module.Flat.lTensor_preserves_injective_linearMap (M := M) _ hn)

/--
theorem `of_basis_right` / 定理 `of_basis_right`

English:
theorem of_basis_right
  statement: {ι : Type*} (n : Basis ι R N)
  proof: of_basis_right' M N n (LinearMap.ker_eq_bot.1 H)

中文:
定理 of_basis_right
  结论: {ι : 类型} (n : 基 ι R N)
  证明: of_basis_right' M N n (LinearMap.ker_eq_bot.1 H)

Depends on / 依赖: LinearMap, LinearMap.ker_eq_bot, ker_eq_bot, of_basis_right
-/
theorem of_basis_right {ι : Type*} (n : Basis ι R N)
    (H : LinearMap.ker (mulRightMap M n) = ⊥) : M.LinearDisjoint N :=
  of_basis_right' M N n (LinearMap.ker_eq_bot.1 H)

variable {M N} in
/--
theorem `linearIndependent_mul_of_flat_left` / 定理 `linearIndependent_mul_of_flat_left`

English:
theorem linearIndependent_mul_of_flat_left
  statement: (H : M.LinearDisjoint N) [Module.Flat R M]
  proof: by
  rw [LinearIndependent] at hm hn ⊢
  let i0 := (finsuppTensorFinsupp' R κ ι).symm
  let i1 := LinearMap.rTensor (ι ->₀ R) (Finsupp.linearCombination R m)
  let i2 := LinearMap.lTensor M (Finsupp.linearCombination R n)
  let i := mulMap M N ∘ₗ i2 ∘ₗ i1 ∘ₗ i0.toLinearMap
  have h1 : Function.Injec

中文:
定理 linearIndependent_mul_of_flat_left
  结论: (H : M.LinearDisjoint N) [模.平坦 R M]
  证明: by
  rw [LinearIndependent] at hm hn ⊢
  let i0 := (finsuppTensorFinsupp' R κ ι).symm
  let i1 := LinearMap.rTensor (ι ->₀ R) (Finsupp.linearCombination R m)
  let i2 := LinearMap.lTensor M (Finsupp.linearCombination R n)
  let i := mulMap M N ∘ₗ i2 ∘ₗ i1 ∘ₗ i0.toLinearMap
  have h1 : Function.Injec

Depends on / 依赖: Finsupp, Finsupp.linearCombination, Function, Function.Injective, Injective, LinearIndependent, LinearMap, LinearMap.lTensor, LinearMap.rTensor, Module, Module.Flat.lTensor_preserves_injective_linearMap, Module.Flat.rTensor_preserves_injective_linearMap, finsuppTensorFinsupp, i0.injective, i0.toLinearMap, injective, lTensor, lTensor_preserves_injective_linearMap, linearCombination, mulMap
-/
theorem linearIndependent_mul_of_flat_left (H : M.LinearDisjoint N) [Module.Flat R M]
    {κ ι : Type*} {m : κ -> M} {n : ι -> N} (hm : LinearIndependent R m)
    (hn : LinearIndependent R n) : LinearIndependent R fun (i : κ × ι) => (m i.1).1 * (n i.2).1 := by
  rw [LinearIndependent] at hm hn ⊢
  let i0 := (finsuppTensorFinsupp' R κ ι).symm
  let i1 := LinearMap.rTensor (ι ->₀ R) (Finsupp.linearCombination R m)
  let i2 := LinearMap.lTensor M (Finsupp.linearCombination R n)
  let i := mulMap M N ∘ₗ i2 ∘ₗ i1 ∘ₗ i0.toLinearMap
  have h1 : Function.Injective i1 := Module.Flat.rTensor_preserves_injective_linearMap _ hm
  have h2 : Function.Injective i2 := Module.Flat.lTensor_preserves_injective_linearMap _ hn
.comp i0.injective .comp h1 have h : Function.Injective i := H.injective.comp h2
  have : i = Finsupp.linearCombination R fun i => (m i.1).1 * (n i.2).1 := by
    ext x
    simp [i, i0, i1, i2, finsuppTensorFinsupp'_symm_single_eq_single_one_tmul]
  rwa [this] at h

variable {M N} in
/--
theorem `linearIndependent_mul_of_flat_right` / 定理 `linearIndependent_mul_of_flat_right`

English:
theorem linearIndependent_mul_of_flat_right
  statement: (H : M.LinearDisjoint N) [Module.Flat R N]
  proof: by
  rw [LinearIndependent] at hm hn ⊢
  let i0 := (finsuppTensorFinsupp' R κ ι).symm
  let i1 := LinearMap.lTensor (κ ->₀ R) (Finsupp.linearCombination R n)
  let i2 := LinearMap.rTensor N (Finsupp.linearCombination R m)
  let i := mulMap M N ∘ₗ i2 ∘ₗ i1 ∘ₗ i0.toLinearMap
  have h1 : Function.Injec

中文:
定理 linearIndependent_mul_of_flat_right
  结论: (H : M.LinearDisjoint N) [模.平坦 R N]
  证明: by
  rw [LinearIndependent] at hm hn ⊢
  let i0 := (finsuppTensorFinsupp' R κ ι).symm
  let i1 := LinearMap.lTensor (κ ->₀ R) (Finsupp.linearCombination R n)
  let i2 := LinearMap.rTensor N (Finsupp.linearCombination R m)
  let i := mulMap M N ∘ₗ i2 ∘ₗ i1 ∘ₗ i0.toLinearMap
  have h1 : Function.Injec

Depends on / 依赖: Finsupp, Finsupp.linearCombination, Function, Function.Injective, Injective, LinearIndependent, LinearMap, LinearMap.lTensor, LinearMap.rTensor, Module, Module.Flat.lTensor_preserves_injective_linearMap, Module.Flat.rTensor_preserves_injective_linearMap, finsuppTensorFinsupp, i0.injective, i0.toLinearMap, injective, lTensor, lTensor_preserves_injective_linearMap, linearCombination, mulMap
-/
theorem linearIndependent_mul_of_flat_right (H : M.LinearDisjoint N) [Module.Flat R N]
    {κ ι : Type*} {m : κ -> M} {n : ι -> N} (hm : LinearIndependent R m)
    (hn : LinearIndependent R n) : LinearIndependent R fun (i : κ × ι) => (m i.1).1 * (n i.2).1 := by
  rw [LinearIndependent] at hm hn ⊢
  let i0 := (finsuppTensorFinsupp' R κ ι).symm
  let i1 := LinearMap.lTensor (κ ->₀ R) (Finsupp.linearCombination R n)
  let i2 := LinearMap.rTensor N (Finsupp.linearCombination R m)
  let i := mulMap M N ∘ₗ i2 ∘ₗ i1 ∘ₗ i0.toLinearMap
  have h1 : Function.Injective i1 := Module.Flat.lTensor_preserves_injective_linearMap _ hn
  have h2 : Function.Injective i2 := Module.Flat.rTensor_preserves_injective_linearMap _ hm
.comp i0.injective .comp h1 have h : Function.Injective i := H.injective.comp h2
  have : i = Finsupp.linearCombination R fun i => (m i.1).1 * (n i.2).1 := by
    ext x
    simp [i, i0, i1, i2, finsuppTensorFinsupp'_symm_single_eq_single_one_tmul]
  rwa [this] at h

variable {M N} in
/--
theorem `linearIndependent_mul_of_flat` / 定理 `linearIndependent_mul_of_flat`

English:
theorem linearIndependent_mul_of_flat
  statement: (H : M.LinearDisjoint N)
  proof: by
  rcases hf with _ | _
  · exact H.linearIndependent_mul_of_flat_left hm hn
  · exact H.linearIndependent_mul_of_flat_right hm hn

中文:
定理 linearIndependent_mul_of_flat
  结论: (H : M.LinearDisjoint N)
  证明: by
  rcases hf with _ | _
  · exact H.linearIndependent_mul_of_flat_left hm hn
  · exact H.linearIndependent_mul_of_flat_right hm hn

Depends on / 依赖: H.linearIndependent_mul_of_flat_left, H.linearIndependent_mul_of_flat_right, linearIndependent_mul_of_flat_left, linearIndependent_mul_of_flat_right
-/
theorem linearIndependent_mul_of_flat (H : M.LinearDisjoint N)
    (hf : Module.Flat R M ∨ Module.Flat R N)
    {κ ι : Type*} {m : κ -> M} {n : ι -> N} (hm : LinearIndependent R m)
    (hn : LinearIndependent R n) : LinearIndependent R fun (i : κ × ι) => (m i.1).1 * (n i.2).1 := by
  rcases hf with _ | _
  · exact H.linearIndependent_mul_of_flat_left hm hn
  · exact H.linearIndependent_mul_of_flat_right hm hn

/--
theorem `of_basis_mul` / 定理 `of_basis_mul`

English:
theorem of_basis_mul
  statement: {κ ι : Type*} (m : Basis κ R M) (n : Basis ι R N)
  proof: by
  rw [LinearIndependent] at H
  exact of_basis_mul' M N m n H

中文:
定理 of_basis_mul
  结论: {κ ι : 类型} (m : 基 κ R M) (n : 基 ι R N)
  证明: by
  rw [LinearIndependent] at H
  exact of_basis_mul' M N m n H

Depends on / 依赖: LinearIndependent, of_basis_mul
-/
theorem of_basis_mul {κ ι : Type*} (m : Basis κ R M) (n : Basis ι R N)
    (H : LinearIndependent R fun (i : κ × ι) => (m i.1).1 * (n i.2).1) : M.LinearDisjoint N := by
  rw [LinearIndependent] at H
  exact of_basis_mul' M N m n H

variable {M N} in
/--
theorem `of_le_left_of_flat` / 定理 `of_le_left_of_flat`

English:
theorem of_le_left_of_flat
  statement: (H : M.LinearDisjoint N) {M' : Submodule R S}
  proof: by
  let i := mulMap M N ∘ₗ (inclusion h).rTensor N
have hi : Function.Injective i := H.injective.comp
Module.Flat.rTensor_preserves_injective_linearMap _ inclusion_injective h
  have : i = mulMap M' N := by ext; simp [i]
  exact ⟨this ▸ hi⟩

中文:
定理 of_le_left_of_flat
  结论: (H : M.LinearDisjoint N) {M' : 子模 R S}
  证明: by
  let i := mulMap M N ∘ₗ (inclusion h).rTensor N
have hi : Function.Injective i := H.injective.comp
Module.Flat.rTensor_preserves_injective_linearMap _ inclusion_injective h
  have : i = mulMap M' N := by ext; simp [i]
  exact ⟨this ▸ hi⟩

Depends on / 依赖: Function, Function.Injective, H.injective.comp, Injective, Module, Module.Flat.rTensor_preserves_injective_linearMap, inclusion, inclusion_injective, injective, mulMap, rTensor, rTensor_preserves_injective_linearMap
-/
theorem of_le_left_of_flat (H : M.LinearDisjoint N) {M' : Submodule R S}
    (h : M' <= M) [Module.Flat R N] : M'.LinearDisjoint N := by
  let i := mulMap M N ∘ₗ (inclusion h).rTensor N
have hi : Function.Injective i := H.injective.comp
Module.Flat.rTensor_preserves_injective_linearMap _ inclusion_injective h
  have : i = mulMap M' N := by ext; simp [i]
  exact ⟨this ▸ hi⟩

variable {M N} in
/--
theorem `of_le_right_of_flat` / 定理 `of_le_right_of_flat`

English:
theorem of_le_right_of_flat
  statement: (H : M.LinearDisjoint N) {N' : Submodule R S}
  proof: by
  let i := mulMap M N ∘ₗ (inclusion h).lTensor M
have hi : Function.Injective i := H.injective.comp
Module.Flat.lTensor_preserves_injective_linearMap _ inclusion_injective h
  have : i = mulMap M N' := by ext; simp [i]
  exact ⟨this ▸ hi⟩

中文:
定理 of_le_right_of_flat
  结论: (H : M.LinearDisjoint N) {N' : 子模 R S}
  证明: by
  let i := mulMap M N ∘ₗ (inclusion h).lTensor M
have hi : Function.Injective i := H.injective.comp
Module.Flat.lTensor_preserves_injective_linearMap _ inclusion_injective h
  have : i = mulMap M N' := by ext; simp [i]
  exact ⟨this ▸ hi⟩

Depends on / 依赖: Function, Function.Injective, H.injective.comp, Injective, Module, Module.Flat.lTensor_preserves_injective_linearMap, inclusion, inclusion_injective, injective, lTensor, lTensor_preserves_injective_linearMap, mulMap
-/
theorem of_le_right_of_flat (H : M.LinearDisjoint N) {N' : Submodule R S}
    (h : N' <= N) [Module.Flat R M] : M.LinearDisjoint N' := by
  let i := mulMap M N ∘ₗ (inclusion h).lTensor M
have hi : Function.Injective i := H.injective.comp
Module.Flat.lTensor_preserves_injective_linearMap _ inclusion_injective h
  have : i = mulMap M N' := by ext; simp [i]
  exact ⟨this ▸ hi⟩

variable {M N} in
/--
theorem `of_le_of_flat_right` / 定理 `of_le_of_flat_right`

English:
theorem of_le_of_flat_right
  statement: (H : M.LinearDisjoint N) {M' N' : Submodule R S}
  proof: (H.of_le_left_of_flat hm).of_le_right_of_flat hn

中文:
定理 of_le_of_flat_right
  结论: (H : M.LinearDisjoint N) {M' N' : 子模 R S}
  证明: (H.of_le_left_of_flat hm).of_le_right_of_flat hn

Depends on / 依赖: H.of_le_left_of_flat, of_le_left_of_flat, of_le_right_of_flat
-/
theorem of_le_of_flat_right (H : M.LinearDisjoint N) {M' N' : Submodule R S}
    (hm : M' <= M) (hn : N' <= N) [Module.Flat R N] [Module.Flat R M'] :
    M'.LinearDisjoint N' := (H.of_le_left_of_flat hm).of_le_right_of_flat hn

variable {M N} in
/--
theorem `of_le_of_flat_left` / 定理 `of_le_of_flat_left`

English:
theorem of_le_of_flat_left
  statement: (H : M.LinearDisjoint N) {M' N' : Submodule R S}
  proof: (H.of_le_right_of_flat hn).of_le_left_of_flat hm

中文:
定理 of_le_of_flat_left
  结论: (H : M.LinearDisjoint N) {M' N' : 子模 R S}
  证明: (H.of_le_right_of_flat hn).of_le_left_of_flat hm

Depends on / 依赖: H.of_le_right_of_flat, of_le_left_of_flat, of_le_right_of_flat
-/
theorem of_le_of_flat_left (H : M.LinearDisjoint N) {M' N' : Submodule R S}
    (hm : M' <= M) (hn : N' <= N) [Module.Flat R M] [Module.Flat R N'] :
    M'.LinearDisjoint N' := (H.of_le_right_of_flat hn).of_le_left_of_flat hm

/--
theorem `of_left_le_one_of_flat` / 定理 `of_left_le_one_of_flat`

English:
theorem of_left_le_one_of_flat
  given: (h : M <= 1) [Module.Flat R N]
  proof: (one_left N).of_le_left_of_flat h

中文:
定理 of_left_le_one_of_flat
  条件: (h : M <= 1) [模.平坦 R N]
  证明: (one_left N).of_le_left_of_flat h

Depends on / 依赖: of_le_left_of_flat, one_left
-/
theorem of_left_le_one_of_flat (h : M <= 1) [Module.Flat R N] :
    M.LinearDisjoint N := (one_left N).of_le_left_of_flat h

/--
theorem `of_right_le_one_of_flat` / 定理 `of_right_le_one_of_flat`

English:
theorem of_right_le_one_of_flat
  given: (h : N <= 1) [Module.Flat R M]
  proof: (one_right M).of_le_right_of_flat h

中文:
定理 of_right_le_one_of_flat
  条件: (h : N <= 1) [模.平坦 R M]
  证明: (one_right M).of_le_right_of_flat h

Depends on / 依赖: of_le_right_of_flat, one_right
-/
theorem of_right_le_one_of_flat (h : N <= 1) [Module.Flat R M] :
    M.LinearDisjoint N := (one_right M).of_le_right_of_flat h

section not_linearIndependent_pair

variable {M N}

section
variable (H : M.LinearDisjoint N)
include H

section

variable [Nontrivial R]

/--
theorem `not_linearIndependent_pair_of_commute_of_flat_left` / 定理 `not_linearIndependent_pair_of_commute_of_flat_left`

English:
theorem not_linearIndependent_pair_of_commute_of_flat_left
  statement: [Module.Flat R M]
  proof: fun h => by
  let n : Fin 2 -> N := (inclusion inf_le_right) ∘ ![a, b]
  have hn : LinearIndependent R n := h.map' _ (ker_inclusion _ _ _)
  -- need this instance otherwise it only has semigroup structure
  let : AddCommGroup (Fin 2 ->₀ M) := Finsupp.instAddCommGroup
  let m : Fin 2 ->₀ M := .single

中文:
定理 not_linearIndependent_pair_of_commute_of_flat_left
  结论: [模.平坦 R M]
  证明: fun h => by
  let n : Fin 2 -> N := (inclusion inf_le_right) ∘ ![a, b]
  have hn : LinearIndependent R n := h.map' _ (ker_inclusion _ _ _)
  -- need this instance otherwise it only has semigroup structure
  let : AddCommGroup (Fin 2 ->₀ M) := Finsupp.instAddCommGroup
  let m : Fin 2 ->₀ M := .single

Depends on / 依赖: LinearIndependent, h.map, inclusion, inf_le_right, ker_inclusion
-/
theorem not_linearIndependent_pair_of_commute_of_flat_left [Module.Flat R M]
    (a b : ↥(M ⊓ N)) (hc : Commute a.1 b.1) : ¬LinearIndependent R ![a, b] := fun h => by
  let n : Fin 2 -> N := (inclusion inf_le_right) ∘ ![a, b]
  have hn : LinearIndependent R n := h.map' _ (ker_inclusion _ _ _)
  -- need this instance otherwise it only has semigroup structure
  let : AddCommGroup (Fin 2 ->₀ M) := Finsupp.instAddCommGroup
  let m : Fin 2 ->₀ M := .single 0 ⟨b.1, b.2.1⟩ - .single 1 ⟨a.1, a.2.1⟩
  have hm : mulRightMap M n m = 0 := by simp [m, n, show _ * _ = _ * _ from hc]
  rw [← LinearMap.mem_ker]; rw [H.linearIndependent_right_of_flat hn]; rw [mem_bot] at hm
  simp only [Fin.isValue, sub_eq_zero, Finsupp.single_eq_single_iff, zero_ne_one, Subtype.mk.injEq,
    SetLike.coe_eq_coe, false_and, false_or, m] at hm
  repeat rw [AddSubmonoid.mk_eq_zero, ZeroMemClass.coe_eq_zero] at hm
  exact h.ne_zero 0 hm.2

/--
theorem `not_linearIndependent_pair_of_commute_of_flat_right` / 定理 `not_linearIndependent_pair_of_commute_of_flat_right`

English:
theorem not_linearIndependent_pair_of_commute_of_flat_right
  statement: [Module.Flat R N]
  proof: fun h => by
  let m : Fin 2 -> M := (inclusion inf_le_left) ∘ ![a, b]
  have hm : LinearIndependent R m := h.map' _ (ker_inclusion _ _ _)
  -- need this instance otherwise it only has semigroup structure
  let : AddCommGroup (Fin 2 ->₀ N) := Finsupp.instAddCommGroup
  let n : Fin 2 ->₀ N := .single 

中文:
定理 not_linearIndependent_pair_of_commute_of_flat_right
  结论: [模.平坦 R N]
  证明: fun h => by
  let m : Fin 2 -> M := (inclusion inf_le_left) ∘ ![a, b]
  have hm : LinearIndependent R m := h.map' _ (ker_inclusion _ _ _)
  -- need this instance otherwise it only has semigroup structure
  let : AddCommGroup (Fin 2 ->₀ N) := Finsupp.instAddCommGroup
  let n : Fin 2 ->₀ N := .single 

Depends on / 依赖: LinearIndependent, h.map, inclusion, inf_le_left, ker_inclusion
-/
theorem not_linearIndependent_pair_of_commute_of_flat_right [Module.Flat R N]
    (a b : ↥(M ⊓ N)) (hc : Commute a.1 b.1) : ¬LinearIndependent R ![a, b] := fun h => by
  let m : Fin 2 -> M := (inclusion inf_le_left) ∘ ![a, b]
  have hm : LinearIndependent R m := h.map' _ (ker_inclusion _ _ _)
  -- need this instance otherwise it only has semigroup structure
  let : AddCommGroup (Fin 2 ->₀ N) := Finsupp.instAddCommGroup
  let n : Fin 2 ->₀ N := .single 0 ⟨b.1, b.2.2⟩ - .single 1 ⟨a.1, a.2.2⟩
  have hn : mulLeftMap N m n = 0 := by simp [m, n, show _ * _ = _ * _ from hc]
  rw [← LinearMap.mem_ker]; rw [H.linearIndependent_left_of_flat hm]; rw [mem_bot] at hn
  simp only [Fin.isValue, sub_eq_zero, Finsupp.single_eq_single_iff, zero_ne_one, Subtype.mk.injEq,
    SetLike.coe_eq_coe, false_and, false_or, n] at hn
  repeat rw [AddSubmonoid.mk_eq_zero, ZeroMemClass.coe_eq_zero] at hn
  exact h.ne_zero 0 hn.2

/--
theorem `not_linearIndependent_pair_of_commute_of_flat` / 定理 `not_linearIndependent_pair_of_commute_of_flat`

English:
theorem not_linearIndependent_pair_of_commute_of_flat
  statement: (hf : Module.Flat R M ∨ Module.Flat R N)
  proof: by
  rcases hf with _ | _
  · exact H.not_linearIndependent_pair_of_commute_of_flat_left a b hc
  · exact H.not_linearIndependent_pair_of_commute_of_flat_right a b hc

中文:
定理 not_linearIndependent_pair_of_commute_of_flat
  结论: (hf : 模.平坦 R M ∨ 模.平坦 R N)
  证明: by
  rcases hf with _ | _
  · exact H.not_linearIndependent_pair_of_commute_of_flat_left a b hc
  · exact H.not_linearIndependent_pair_of_commute_of_flat_right a b hc

Depends on / 依赖: H.not_linearIndependent_pair_of_commute_of_flat_left, H.not_linearIndependent_pair_of_commute_of_flat_right, not_linearIndependent_pair_of_commute_of_flat_left, not_linearIndependent_pair_of_commute_of_flat_right
-/
theorem not_linearIndependent_pair_of_commute_of_flat (hf : Module.Flat R M ∨ Module.Flat R N)
    (a b : ↥(M ⊓ N)) (hc : Commute a.1 b.1) : ¬LinearIndependent R ![a, b] := by
  rcases hf with _ | _
  · exact H.not_linearIndependent_pair_of_commute_of_flat_left a b hc
  · exact H.not_linearIndependent_pair_of_commute_of_flat_right a b hc

end

/--
theorem `rank_inf_le_one_of_commute_of_flat` / 定理 `rank_inf_le_one_of_commute_of_flat`

English:
theorem rank_inf_le_one_of_commute_of_flat
  statement: (hf : Module.Flat R M ∨ Module.Flat R N)
  proof: by
  nontriviality R
  refine _root_.rank_le fun s h => ?_
  by_contra hs
  rw [not_le]; rw [← Fintype.card_coe]; rw [Fintype.one_lt_card_iff_nontrivial] at hs
  obtain ⟨a, b, hab⟩ := hs.exists_pair_ne
  refine H.not_linearIndependent_pair_of_commute_of_flat hf a.1 b.1 (hc a.1 b.1) ?_
  have := h.co

中文:
定理 rank_inf_le_one_of_commute_of_flat
  结论: (hf : 模.平坦 R M ∨ 模.平坦 R N)
  证明: by
  nontriviality R
  refine _root_.rank_le fun s h => ?_
  by_contra hs
  rw [not_le]; rw [← Fintype.card_coe]; rw [Fintype.one_lt_card_iff_nontrivial] at hs
  obtain ⟨a, b, hab⟩ := hs.exists_pair_ne
  refine H.not_linearIndependent_pair_of_commute_of_flat hf a.1 b.1 (hc a.1 b.1) ?_
  have := h.co

Depends on / 依赖: Fintype, Fintype.card_coe, Fintype.one_lt_card_iff_nontrivial, H.not_linearIndependent_pair_of_commute_of_flat, _root_, _root_.rank_le, card_coe, convert, exists_pair_ne, fin_cases, h.comp, hab.symm, hs.exists_pair_ne, nontriviality, not_le, not_linearIndependent_pair_of_commute_of_flat, one_lt_card_iff_nontrivial, rank_le
-/
theorem rank_inf_le_one_of_commute_of_flat (hf : Module.Flat R M ∨ Module.Flat R N)
    (hc : forall (m n : ↥(M ⊓ N)), Commute m.1 n.1) : Module.rank R ↥(M ⊓ N) <= 1 := by
  nontriviality R
  refine _root_.rank_le fun s h => ?_
  by_contra hs
  rw [not_le]; rw [← Fintype.card_coe]; rw [Fintype.one_lt_card_iff_nontrivial] at hs
  obtain ⟨a, b, hab⟩ := hs.exists_pair_ne
  refine H.not_linearIndependent_pair_of_commute_of_flat hf a.1 b.1 (hc a.1 b.1) ?_
  have := h.comp ![a, b] fun i j hij => by
    fin_cases i <;> fin_cases j
    · rfl
    · simp [hab] at hij
    · simp [hab.symm] at hij
    · rfl
  convert! this
  ext i
  fin_cases i <;> simp

/--
theorem `rank_inf_le_one_of_commute_of_flat_left` / 定理 `rank_inf_le_one_of_commute_of_flat_left`

English:
theorem rank_inf_le_one_of_commute_of_flat_left
  statement: [Module.Flat R M]
  proof: H.rank_inf_le_one_of_commute_of_flat (Or.inl ‹_›) hc

中文:
定理 rank_inf_le_one_of_commute_of_flat_left
  结论: [模.平坦 R M]
  证明: H.rank_inf_le_one_of_commute_of_flat (Or.inl ‹_›) hc

Depends on / 依赖: H.rank_inf_le_one_of_commute_of_flat, Or.inl, rank_inf_le_one_of_commute_of_flat
-/
theorem rank_inf_le_one_of_commute_of_flat_left [Module.Flat R M]
    (hc : forall (m n : ↥(M ⊓ N)), Commute m.1 n.1) : Module.rank R ↥(M ⊓ N) <= 1 :=
  H.rank_inf_le_one_of_commute_of_flat (Or.inl ‹_›) hc

/--
theorem `rank_inf_le_one_of_commute_of_flat_right` / 定理 `rank_inf_le_one_of_commute_of_flat_right`

English:
theorem rank_inf_le_one_of_commute_of_flat_right
  statement: [Module.Flat R N]
  proof: H.rank_inf_le_one_of_commute_of_flat (Or.inr ‹_›) hc

中文:
定理 rank_inf_le_one_of_commute_of_flat_right
  结论: [模.平坦 R N]
  证明: H.rank_inf_le_one_of_commute_of_flat (Or.inr ‹_›) hc

Depends on / 依赖: H.rank_inf_le_one_of_commute_of_flat, Or.inr, rank_inf_le_one_of_commute_of_flat
-/
theorem rank_inf_le_one_of_commute_of_flat_right [Module.Flat R N]
    (hc : forall (m n : ↥(M ⊓ N)), Commute m.1 n.1) : Module.rank R ↥(M ⊓ N) <= 1 :=
  H.rank_inf_le_one_of_commute_of_flat (Or.inr ‹_›) hc

end

/--
theorem `rank_le_one_of_commute_of_flat_of_self` / 定理 `rank_le_one_of_commute_of_flat_of_self`

English:
theorem rank_le_one_of_commute_of_flat_of_self
  statement: (H : M.LinearDisjoint M) [Module.Flat R M]
  proof: by
  rw [← inf_of_le_left (le_refl M)] at hc ⊢
  exact H.rank_inf_le_one_of_commute_of_flat_left hc

中文:
定理 rank_le_one_of_commute_of_flat_of_self
  结论: (H : M.LinearDisjoint M) [模.平坦 R M]
  证明: by
  rw [← inf_of_le_left (le_refl M)] at hc ⊢
  exact H.rank_inf_le_one_of_commute_of_flat_left hc

Depends on / 依赖: H.rank_inf_le_one_of_commute_of_flat_left, inf_of_le_left, le_refl, rank_inf_le_one_of_commute_of_flat_left
-/
theorem rank_le_one_of_commute_of_flat_of_self (H : M.LinearDisjoint M) [Module.Flat R M]
    (hc : forall (m n : M), Commute m.1 n.1) : Module.rank R M <= 1 := by
  rw [← inf_of_le_left (le_refl M)] at hc ⊢
  exact H.rank_inf_le_one_of_commute_of_flat_left hc

end not_linearIndependent_pair

end LinearDisjoint

end Ring

section CommRing

namespace LinearDisjoint

variable [CommRing R] [CommRing S] [Algebra R S]

variable (M N : Submodule R S)

section not_linearIndependent_pair

variable {M N}

section
variable (H : M.LinearDisjoint N)
include H

section

variable [Nontrivial R]

/--
theorem `not_linearIndependent_pair_of_flat_left` / 定理 `not_linearIndependent_pair_of_flat_left`

English:
theorem not_linearIndependent_pair_of_flat_left
  statement: [Module.Flat R M]
  proof: H.not_linearIndependent_pair_of_commute_of_flat_left a b (mul_comm _ _)

中文:
定理 not_linearIndependent_pair_of_flat_left
  结论: [模.平坦 R M]
  证明: H.not_linearIndependent_pair_of_commute_of_flat_left a b (mul_comm _ _)

Depends on / 依赖: H.not_linearIndependent_pair_of_commute_of_flat_left, mul_comm, not_linearIndependent_pair_of_commute_of_flat_left
-/
theorem not_linearIndependent_pair_of_flat_left [Module.Flat R M]
    (a b : ↥(M ⊓ N)) : ¬LinearIndependent R ![a, b] :=
  H.not_linearIndependent_pair_of_commute_of_flat_left a b (mul_comm _ _)

/--
theorem `not_linearIndependent_pair_of_flat_right` / 定理 `not_linearIndependent_pair_of_flat_right`

English:
theorem not_linearIndependent_pair_of_flat_right
  statement: [Module.Flat R N]
  proof: H.not_linearIndependent_pair_of_commute_of_flat_right a b (mul_comm _ _)

中文:
定理 not_linearIndependent_pair_of_flat_right
  结论: [模.平坦 R N]
  证明: H.not_linearIndependent_pair_of_commute_of_flat_right a b (mul_comm _ _)

Depends on / 依赖: H.not_linearIndependent_pair_of_commute_of_flat_right, mul_comm, not_linearIndependent_pair_of_commute_of_flat_right
-/
theorem not_linearIndependent_pair_of_flat_right [Module.Flat R N]
    (a b : ↥(M ⊓ N)) : ¬LinearIndependent R ![a, b] :=
  H.not_linearIndependent_pair_of_commute_of_flat_right a b (mul_comm _ _)

/--
theorem `not_linearIndependent_pair_of_flat` / 定理 `not_linearIndependent_pair_of_flat`

English:
theorem not_linearIndependent_pair_of_flat
  statement: (hf : Module.Flat R M ∨ Module.Flat R N)
  proof: H.not_linearIndependent_pair_of_commute_of_flat hf a b (mul_comm _ _)

中文:
定理 not_linearIndependent_pair_of_flat
  结论: (hf : 模.平坦 R M ∨ 模.平坦 R N)
  证明: H.not_linearIndependent_pair_of_commute_of_flat hf a b (mul_comm _ _)

Depends on / 依赖: H.not_linearIndependent_pair_of_commute_of_flat, mul_comm, not_linearIndependent_pair_of_commute_of_flat
-/
theorem not_linearIndependent_pair_of_flat (hf : Module.Flat R M ∨ Module.Flat R N)
    (a b : ↥(M ⊓ N)) : ¬LinearIndependent R ![a, b] :=
  H.not_linearIndependent_pair_of_commute_of_flat hf a b (mul_comm _ _)

end

/--
theorem `rank_inf_le_one_of_flat` / 定理 `rank_inf_le_one_of_flat`

English:
theorem rank_inf_le_one_of_flat
  given: (hf : Module.Flat R M ∨ Module.Flat R N)
  proof: H.rank_inf_le_one_of_commute_of_flat hf fun _ _ => mul_comm _ _

中文:
定理 rank_inf_le_one_of_flat
  条件: (hf : 模.平坦 R M ∨ 模.平坦 R N)
  证明: H.rank_inf_le_one_of_commute_of_flat hf fun _ _ => mul_comm _ _

Depends on / 依赖: H.rank_inf_le_one_of_commute_of_flat, mul_comm, rank_inf_le_one_of_commute_of_flat
-/
theorem rank_inf_le_one_of_flat (hf : Module.Flat R M ∨ Module.Flat R N) :
    Module.rank R ↥(M ⊓ N) <= 1 :=
  H.rank_inf_le_one_of_commute_of_flat hf fun _ _ => mul_comm _ _

/--
theorem `rank_inf_le_one_of_flat_left` / 定理 `rank_inf_le_one_of_flat_left`

English:
theorem rank_inf_le_one_of_flat_left
  given: [Module.Flat R M]
  statement: Module.rank R ↥(M ⊓ N) <= 1
  proof: H.rank_inf_le_one_of_commute_of_flat_left fun _ _ => mul_comm _ _

中文:
定理 rank_inf_le_one_of_flat_left
  条件: [模.平坦 R M]
  结论: 模.rank R ↥(M ⊓ N) <= 1
  证明: H.rank_inf_le_one_of_commute_of_flat_left fun _ _ => mul_comm _ _

Depends on / 依赖: H.rank_inf_le_one_of_commute_of_flat_left, mul_comm, rank_inf_le_one_of_commute_of_flat_left
-/
theorem rank_inf_le_one_of_flat_left [Module.Flat R M] : Module.rank R ↥(M ⊓ N) <= 1 :=
  H.rank_inf_le_one_of_commute_of_flat_left fun _ _ => mul_comm _ _

/--
theorem `rank_inf_le_one_of_flat_right` / 定理 `rank_inf_le_one_of_flat_right`

English:
theorem rank_inf_le_one_of_flat_right
  given: [Module.Flat R N]
  statement: Module.rank R ↥(M ⊓ N) <= 1
  proof: H.rank_inf_le_one_of_commute_of_flat_right fun _ _ => mul_comm _ _

中文:
定理 rank_inf_le_one_of_flat_right
  条件: [模.平坦 R N]
  结论: 模.rank R ↥(M ⊓ N) <= 1
  证明: H.rank_inf_le_one_of_commute_of_flat_right fun _ _ => mul_comm _ _

Depends on / 依赖: H.rank_inf_le_one_of_commute_of_flat_right, mul_comm, rank_inf_le_one_of_commute_of_flat_right
-/
theorem rank_inf_le_one_of_flat_right [Module.Flat R N] : Module.rank R ↥(M ⊓ N) <= 1 :=
  H.rank_inf_le_one_of_commute_of_flat_right fun _ _ => mul_comm _ _

end

/--
theorem `rank_le_one_of_flat_of_self` / 定理 `rank_le_one_of_flat_of_self`

English:
theorem rank_le_one_of_flat_of_self
  given: (H : M.LinearDisjoint M) [Module.Flat R M]
  proof: H.rank_le_one_of_commute_of_flat_of_self fun _ _ => mul_comm _ _

中文:
定理 rank_le_one_of_flat_of_self
  条件: (H : M.LinearDisjoint M) [模.平坦 R M]
  证明: H.rank_le_one_of_commute_of_flat_of_self fun _ _ => mul_comm _ _

Depends on / 依赖: H.rank_le_one_of_commute_of_flat_of_self, mul_comm, rank_le_one_of_commute_of_flat_of_self
-/
theorem rank_le_one_of_flat_of_self (H : M.LinearDisjoint M) [Module.Flat R M] :
    Module.rank R M <= 1 :=
  H.rank_le_one_of_commute_of_flat_of_self fun _ _ => mul_comm _ _

end not_linearIndependent_pair

end LinearDisjoint

end CommRing

end Submodule
