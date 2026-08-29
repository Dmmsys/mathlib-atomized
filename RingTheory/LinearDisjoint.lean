/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.MulOpposite
public import Mathlib.Algebra.Algebra.Subalgebra.Rank
public import Mathlib.Algebra.Polynomial.Basis
public import Mathlib.LinearAlgebra.LinearDisjoint
public import Mathlib.LinearAlgebra.TensorProduct.Subalgebra
public import Mathlib.RingTheory.Adjoin.Dimension
public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.TensorProduct.Nontrivial
public import Mathlib.RingTheory.Trace.Defs

/-!

# Linearly disjoint subalgebras

This file contains basics about linearly disjoint subalgebras.
We adapt the definitions in <https://en.wikipedia.org/wiki/Linearly_disjoint>.
See the file `Mathlib/LinearAlgebra/LinearDisjoint.lean` for details.

## Main definitions

- `Subalgebra.LinearDisjoint`: two subalgebras are linearly disjoint, if they are
  linearly disjoint as submodules (`Submodule.LinearDisjoint`).

- `Subalgebra.LinearDisjoint.mulMap`: if two subalgebras `A` and `B` of `S / R` are
  linearly disjoint, then there is `A ⊗[R] B ≃ₐ[R] A ⊔ B` induced by multiplication in `S`.

## Main results

### Equivalent characterization of linear disjointness

- `Subalgebra.LinearDisjoint.linearIndependent_left_of_flat`:
  if `A` and `B` are linearly disjoint, and if `B` is a flat `R`-module, then for any family of
  `R`-linearly independent elements of `A`, they are also `B`-linearly independent.

- `Subalgebra.LinearDisjoint.of_basis_left_op`:
  conversely, if a basis of `A` is also `B`-linearly independent, then `A` and `B` are
  linearly disjoint.

- `Subalgebra.LinearDisjoint.linearIndependent_right_of_flat`:
  if `A` and `B` are linearly disjoint, and if `A` is a flat `R`-module, then for any family of
  `R`-linearly independent elements of `B`, they are also `A`-linearly independent.

- `Subalgebra.LinearDisjoint.of_basis_right`:
  conversely, if a basis of `B` is also `A`-linearly independent,
  then `A` and `B` are linearly disjoint.

- `Subalgebra.LinearDisjoint.linearIndependent_mul_of_flat`:
  if `A` and `B` are linearly disjoint, and if one of `A` and `B` is flat, then for any family of
  `R`-linearly independent elements `{ a_i }` of `A`, and any family of
  `R`-linearly independent elements `{ b_j }` of `B`, the family `{ a_i * b_j }` in `S` is
  also `R`-linearly independent.

- `Subalgebra.LinearDisjoint.of_basis_mul`:
  conversely, if `{ a_i }` is an `R`-basis of `A`, if `{ b_j }` is an `R`-basis of `B`,
  such that the family `{ a_i * b_j }` in `S` is `R`-linearly independent,
  then `A` and `B` are linearly disjoint.

### Equivalent characterization by `IsDomain` or `IsField` of tensor product

The following results are related to the equivalent characterizations in
<https://mathoverflow.net/questions/8324>.

- `Subalgebra.LinearDisjoint.isDomain_of_injective`,
  `Subalgebra.LinearDisjoint.exists_field_of_isDomain_of_injective`:
  under some flatness and injectivity conditions, if `A` and `B` are `R`-algebras, then `A ⊗[R] B`
  is a domain if and only if there exists an `R`-algebra which is a field that `A` and `B`
  embed into with linearly disjoint images.

- `Subalgebra.LinearDisjoint.of_isField`, `Subalgebra.LinearDisjoint.of_isField'`:
  if `A ⊗[R] B` is a field, then `A` and `B` are linearly disjoint, moreover, for any
  `R`-algebra `S` and injections of `A` and `B` into `S`, their images are linearly disjoint.

- `Algebra.TensorProduct.not_isField_of_transcendental`,
  `Algebra.TensorProduct.isAlgebraic_of_isField`:
  if `A` and `B` are flat `R`-algebras, both of them are transcendental, then `A ⊗[R] B` cannot
  be a field, equivalently, if `A ⊗[R] B` is a field, then one of them is algebraic.

### Other main results

- `Subalgebra.LinearDisjoint.symm_of_commute`, `Subalgebra.linearDisjoint_comm_of_commute`:
  linear disjointness is symmetric under some commutative conditions.

- `Subalgebra.LinearDisjoint.map`:
  linear disjointness is preserved by injective algebra homomorphisms.

- `Subalgebra.LinearDisjoint.bot_left`, `Subalgebra.LinearDisjoint.bot_right`:
  the image of `R` in `S` is linearly disjoint with any other subalgebras.

- `Subalgebra.LinearDisjoint.sup_free_of_free`: the compositum of two linearly disjoint
  subalgebras is a free module, if two subalgebras are also free modules.

- `Subalgebra.LinearDisjoint.rank_sup_of_free`,
  `Subalgebra.LinearDisjoint.finrank_sup_of_free`:
  if subalgebras `A` and `B` are linearly disjoint and they are
  free modules, then the rank of `A ⊔ B` is equal to the product of the rank of `A` and `B`.

- `Subalgebra.LinearDisjoint.of_finrank_sup_of_free`:
  conversely, if `A` and `B` are subalgebras which are free modules of finite rank,
  such that rank of `A ⊔ B` is equal to the product of the rank of `A` and `B`,
  then `A` and `B` are linearly disjoint.

- `Subalgebra.LinearDisjoint.adjoin_rank_eq_rank_left`:
  `Subalgebra.LinearDisjoint.adjoin_rank_eq_rank_right`:
  if `A` and `B` are linearly disjoint, if `A` is free and `B` is flat (resp. `B` is free and
  `A` is flat), then `[B[A] : B] = [A : R]` (resp. `[A[B] : A] = [B : R]`).
  See also `Subalgebra.adjoin_rank_le`.

- `Subalgebra.LinearDisjoint.of_finrank_coprime_of_free`:
  if the rank of `A` and `B` are coprime, and they satisfy some freeness condition,
  then `A` and `B` are linearly disjoint.

- `Subalgebra.LinearDisjoint.inf_eq_bot_of_commute`, `Subalgebra.LinearDisjoint.inf_eq_bot`:
  if `A` and `B` are linearly disjoint, under suitable technical conditions, they are disjoint.

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

namespace Subalgebra

variable {R : Type u} {S : Type v}

section Semiring

variable [CommSemiring R] [Semiring S] [Algebra R S]

variable (A B : Subalgebra R S)

/--
Definition of `LinearDisjoint` / `LinearDisjoint` 的定义

English:
abbreviation LinearDisjoint
  signature: : Prop
  body: (toSubmodule A).LinearDisjoint (toSubmodule B)

中文:
缩写 LinearDisjoint
  签名: : 命题
  定义体: (toSubmodule A).LinearDisjoint (toSubmodule B)
-/
protected abbrev LinearDisjoint : Prop := (toSubmodule A).LinearDisjoint (toSubmodule B)

/--
theorem `linearDisjoint_iff` / 定理 `linearDisjoint_iff`

English:
theorem linearDisjoint_iff
  statement: A.LinearDisjoint B ↔ (toSubmodule A).LinearDisjoint (toSubmodule B)
  proof: Iff.rfl

中文:
定理 linearDisjoint_iff
  结论: A.LinearDisjoint B ↔ (toSubmodule A).LinearDisjoint (toSubmodule B)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem linearDisjoint_iff : A.LinearDisjoint B ↔ (toSubmodule A).LinearDisjoint (toSubmodule B) :=
  Iff.rfl

variable {A B}

@[nontriviality]
/--
theorem `LinearDisjoint.of_subsingleton` / 定理 `LinearDisjoint.of_subsingleton`

English:
theorem LinearDisjoint.of_subsingleton
  given: [Subsingleton R]
  statement: A.LinearDisjoint B
  proof: Submodule.LinearDisjoint.of_subsingleton

@[nontriviality]

中文:
定理 LinearDisjoint.of_subsingleton
  条件: [Subsingleton R]
  结论: A.LinearDisjoint B
  证明: Submodule.LinearDisjoint.of_subsingleton

@[nontriviality]
-/
theorem LinearDisjoint.of_subsingleton [Subsingleton R] : A.LinearDisjoint B :=
  Submodule.LinearDisjoint.of_subsingleton

@[nontriviality]
/--
theorem `LinearDisjoint.of_subsingleton_top` / 定理 `LinearDisjoint.of_subsingleton_top`

English:
theorem LinearDisjoint.of_subsingleton_top
  given: [Subsingleton S]
  statement: A.LinearDisjoint B
  proof: Submodule.LinearDisjoint.of_subsingleton_top

中文:
定理 LinearDisjoint.of_subsingleton_top
  条件: [Subsingleton S]
  结论: A.LinearDisjoint B
  证明: Submodule.LinearDisjoint.of_subsingleton_top
-/
theorem LinearDisjoint.of_subsingleton_top [Subsingleton S] : A.LinearDisjoint B :=
  Submodule.LinearDisjoint.of_subsingleton_top

/--
theorem `LinearDisjoint.symm_of_commute` / 定理 `LinearDisjoint.symm_of_commute`

English:
theorem LinearDisjoint.symm_of_commute
  statement: (H : A.LinearDisjoint B)
  proof: Submodule.LinearDisjoint.symm_of_commute H hc

中文:
定理 LinearDisjoint.symm_of_commute
  结论: (H : A.LinearDisjoint B)
  证明: Submodule.LinearDisjoint.symm_of_commute H hc
-/
theorem LinearDisjoint.symm_of_commute (H : A.LinearDisjoint B)
    (hc : forall (a : A) (b : B), Commute a.1 b.1) : B.LinearDisjoint A :=
  Submodule.LinearDisjoint.symm_of_commute H hc

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
    (hc : forall (a : A) (b : B), Commute a.1 b.1) : A.LinearDisjoint B ↔ B.LinearDisjoint A :=
  ⟨fun H => H.symm_of_commute hc, fun H => H.symm_of_commute fun _ _ => (hc _ _).symm⟩

namespace LinearDisjoint

/--
theorem `map` / 定理 `map`

English:
theorem map
  statement: (H : A.LinearDisjoint B) {T : Type w} [Semiring T] [Algebra R T]
  proof: Submodule.LinearDisjoint.map H f hf

中文:
定理 map
  结论: (H : A.LinearDisjoint B) {T : Type w} [Semiring T] [Algebra R T]
  证明: Submodule.LinearDisjoint.map H f hf

Depends on / 依赖: LinearDisjoint, Submodule, Submodule.LinearDisjoint.map
-/
theorem map (H : A.LinearDisjoint B) {T : Type w} [Semiring T] [Algebra R T]
    (f : S ->ₐ[R] T) (hf : Function.Injective f) : (A.map f).LinearDisjoint (B.map f) :=
  Submodule.LinearDisjoint.map H f hf

variable (A B)

/--
theorem `bot_left` / 定理 `bot_left`

English:
theorem bot_left
  statement: (⊥ : Subalgebra R S).LinearDisjoint B
  proof: by
  rw [Subalgebra.LinearDisjoint]; rw [Algebra.toSubmodule_bot]
  exact Submodule.LinearDisjoint.one_left _

中文:
定理 bot_left
  结论: (⊥ : Subalgebra R S).LinearDisjoint B
  证明: by
  rw [Subalgebra.LinearDisjoint]; rw [Algebra.toSubmodule_bot]
  exact Submodule.LinearDisjoint.one_left _

Depends on / 依赖: Algebra, Algebra.toSubmodule_bot, LinearDisjoint, Subalgebra, Subalgebra.LinearDisjoint, Submodule, Submodule.LinearDisjoint.one_left, one_left, toSubmodule_bot
-/
theorem bot_left : (⊥ : Subalgebra R S).LinearDisjoint B := by
  rw [Subalgebra.LinearDisjoint]; rw [Algebra.toSubmodule_bot]
  exact Submodule.LinearDisjoint.one_left _

/--
theorem `bot_right` / 定理 `bot_right`

English:
theorem bot_right
  statement: A.LinearDisjoint ⊥
  proof: by
  rw [Subalgebra.LinearDisjoint]; rw [Algebra.toSubmodule_bot]
  exact Submodule.LinearDisjoint.one_right _

中文:
定理 bot_right
  结论: A.LinearDisjoint ⊥
  证明: by
  rw [Subalgebra.LinearDisjoint]; rw [Algebra.toSubmodule_bot]
  exact Submodule.LinearDisjoint.one_right _

Depends on / 依赖: Algebra, Algebra.toSubmodule_bot, LinearDisjoint, Subalgebra, Subalgebra.LinearDisjoint, Submodule, Submodule.LinearDisjoint.one_right, one_right, toSubmodule_bot
-/
theorem bot_right : A.LinearDisjoint ⊥ := by
  rw [Subalgebra.LinearDisjoint]; rw [Algebra.toSubmodule_bot]
  exact Submodule.LinearDisjoint.one_right _

variable (R) in
/--
theorem `include_range` / 定理 `include_range`

English:
theorem include_range
  statement: (A : Type v) [Semiring A] (B : Type w) [Semiring B]
  proof: by
  rw [Subalgebra.LinearDisjoint]; rw [Submodule.linearDisjoint_iff]
change Function.Injective
    Submodule.mulMap (LinearMap.range Algebra.TensorProduct.includeLeft.toLinearMap)
      (LinearMap.range Algebra.TensorProduct.includeRight.toLinearMap)
  rw [← Algebra.TensorProduct.linearEquivInclud

中文:
定理 include_range
  结论: (A : 类型v) [Semiring A] (B : Type w) [Semiring B]
  证明: by
  rw [Subalgebra.LinearDisjoint]; rw [Submodule.linearDisjoint_iff]
change Function.Injective
    Submodule.mulMap (LinearMap.range Algebra.TensorProduct.includeLeft.toLinearMap)
      (LinearMap.range Algebra.TensorProduct.includeRight.toLinearMap)
  rw [← Algebra.TensorProduct.linearEquivInclud

Depends on / 依赖: Algebra, Algebra.TensorProduct.includeLeft.toLinearMap, Algebra.TensorProduct.includeRight.toLinearMap, Algebra.TensorProduct.linearEquivIncludeRange_symm_toLinearMap, Function, Function.Injective, Injective, LinearDisjoint, LinearEquiv, LinearEquiv.injective, LinearMap, LinearMap.range, Subalgebra, Subalgebra.LinearDisjoint, Submodule, Submodule.linearDisjoint_iff, Submodule.mulMap, TensorProduct, includeLeft, includeRight
-/
theorem include_range (A : Type v) [Semiring A] (B : Type w) [Semiring B]
    [Algebra R A] [Algebra R B] :
    (Algebra.TensorProduct.includeLeft : A ->ₐ[R] A otimes[R] B).range.LinearDisjoint
      (Algebra.TensorProduct.includeRight : B ->ₐ[R] A otimes[R] B).range := by
  rw [Subalgebra.LinearDisjoint]; rw [Submodule.linearDisjoint_iff]
change Function.Injective
    Submodule.mulMap (LinearMap.range Algebra.TensorProduct.includeLeft.toLinearMap)
      (LinearMap.range Algebra.TensorProduct.includeRight.toLinearMap)
  rw [← Algebra.TensorProduct.linearEquivIncludeRange_symm_toLinearMap]
  exact LinearEquiv.injective _

end LinearDisjoint

end Semiring

section CommSemiring

variable [CommSemiring R] [CommSemiring S] [Algebra R S]

variable {A B : Subalgebra R S}

/--
theorem `LinearDisjoint.symm` / 定理 `LinearDisjoint.symm`

English:
theorem LinearDisjoint.symm
  given: (H : A.LinearDisjoint B)
  statement: B.LinearDisjoint A
  proof: H.symm_of_commute fun _ _ => mul_comm _ _

中文:
定理 LinearDisjoint.symm
  条件: (H : A.LinearDisjoint B)
  结论: B.LinearDisjoint A
  证明: H.symm_of_commute fun _ _ => mul_comm _ _
-/
theorem LinearDisjoint.symm (H : A.LinearDisjoint B) : B.LinearDisjoint A :=
  H.symm_of_commute fun _ _ => mul_comm _ _

/--
theorem `linearDisjoint_comm` / 定理 `linearDisjoint_comm`

English:
theorem linearDisjoint_comm
  statement: A.LinearDisjoint B ↔ B.LinearDisjoint A
  proof: ⟨LinearDisjoint.symm, LinearDisjoint.symm⟩

中文:
定理 linearDisjoint_comm
  结论: A.LinearDisjoint B ↔ B.LinearDisjoint A
  证明: ⟨LinearDisjoint.symm, LinearDisjoint.symm⟩

Depends on / 依赖: LinearDisjoint, LinearDisjoint.symm
-/
theorem linearDisjoint_comm : A.LinearDisjoint B ↔ B.LinearDisjoint A :=
  ⟨LinearDisjoint.symm, LinearDisjoint.symm⟩

/--
theorem `linearDisjoint_iff_injective` / 定理 `linearDisjoint_iff_injective`

English:
theorem linearDisjoint_iff_injective
  statement: A.LinearDisjoint B ↔ Function.Injective (A.mulMap B)
  proof: by
  rw [linearDisjoint_iff]; rw [Submodule.linearDisjoint_iff]
  rfl

中文:
定理 linearDisjoint_iff_injective
  结论: A.LinearDisjoint B ↔ Function.Injective (A.mulMap B)
  证明: by
  rw [linearDisjoint_iff]; rw [Submodule.linearDisjoint_iff]
  rfl

Depends on / 依赖: Submodule, Submodule.linearDisjoint_iff, linearDisjoint_iff
-/
theorem linearDisjoint_iff_injective : A.LinearDisjoint B ↔ Function.Injective (A.mulMap B) := by
  rw [linearDisjoint_iff]; rw [Submodule.linearDisjoint_iff]
  rfl

namespace LinearDisjoint

variable (H : A.LinearDisjoint B)

/--
Definition of `mulMap` / `mulMap` 的定义

English:
definition mulMap
  body: (AlgEquiv.ofInjective (A.mulMap B) H.injective).trans (equivOfEq _ _ (mulMap_range A B))

@[simp]

中文:
定义 mulMap
  定义体: (AlgEquiv.ofInjective (A.mulMap B) H.injective).trans (equivOfEq _ _ (mulMap_range A B))

@[simp]
-/
protected def mulMap :=
  (AlgEquiv.ofInjective (A.mulMap B) H.injective).trans (equivOfEq _ _ (mulMap_range A B))

@[simp]
/--
theorem `val_mulMap_tmul` / 定理 `val_mulMap_tmul`

English:
theorem val_mulMap_tmul
  given: (a : A) (b : B)
  statement: (H.mulMap (a otimesₜ[R] b) : S) = a.1 * b.1
  proof: rfl

中文:
定理 val_mulMap_tmul
  条件: (a : A) (b : B)
  结论: (H.mulMap (a otimesₜ[R] b) : S) = a.1 * b.1
  证明: rfl
-/
theorem val_mulMap_tmul (a : A) (b : B) : (H.mulMap (a otimesₜ[R] b) : S) = a.1 * b.1 := rfl

/--
Definition of `mulMapLeftOfSupEqTop` / `mulMapLeftOfSupEqTop` 的定义

English:
definition mulMapLeftOfSupEqTop
  signature: (H' : A ⊔ B = ⊤)
  body: (AlgEquiv.ofInjective (Algebra.TensorProduct.productLeftAlgHom
    (Algebra.ofId A S) B.val) H.injective).trans ((Subalgebra.equivOfEq _ _ (by
      apply Subalgebra.restrictScalars_injective R
      rw [restrictScalars_top]; rw [← H']
      exact mulMap_range A B)).trans Subalgebra.topEquiv)

@[sim

中文:
定义 mulMapLeftOfSupEqTop
  签名: (H' : A ⊔ B = ⊤)
  定义体: (AlgEquiv.ofInjective (Algebra.TensorProduct.productLeftAlgHom
    (Algebra.ofId A S) B.val) H.injective).trans ((Subalgebra.equivOfEq _ _ (by
      apply Subalgebra.restrictScalars_injective R
      rw [restrictScalars_top]; rw [← H']
      exact mulMap_range A B)).trans Subalgebra.topEquiv)

@[sim

Depends on / 依赖: AlgEquiv, AlgEquiv.ofInjective, Algebra, Algebra.TensorProduct.productLeftAlgHom, Algebra.ofId, B.val, H.injective, Subalgebra, Subalgebra.equivOfEq, Subalgebra.restrictScalars_injective, Subalgebra.topEquiv, TensorProduct, equivOfEq, injective, mulMap_range, ofInjective, productLeftAlgHom, restrictScalars_injective, restrictScalars_top, topEquiv
-/
noncomputable def mulMapLeftOfSupEqTop (H' : A ⊔ B = ⊤) :
    A otimes[R] B ≃ₐ[A] S :=
  (AlgEquiv.ofInjective (Algebra.TensorProduct.productLeftAlgHom
    (Algebra.ofId A S) B.val) H.injective).trans ((Subalgebra.equivOfEq _ _ (by
      apply Subalgebra.restrictScalars_injective R
      rw [restrictScalars_top]; rw [← H']
      exact mulMap_range A B)).trans Subalgebra.topEquiv)

@[simp]
/--
theorem `mulMapLeftOfSupEqTop_tmul` / 定理 `mulMapLeftOfSupEqTop_tmul`

English:
theorem mulMapLeftOfSupEqTop_tmul
  given: (H' : A ⊔ B = ⊤) (a : A) (b : B)
  proof: rfl

中文:
定理 mulMapLeftOfSupEqTop_tmul
  条件: (H' : A ⊔ B = ⊤) (a : A) (b : B)
  证明: rfl
-/
theorem mulMapLeftOfSupEqTop_tmul (H' : A ⊔ B = ⊤) (a : A) (b : B) :
    H.mulMapLeftOfSupEqTop H' (a otimesₜ[R] b) = (a : S) * (b : S) := rfl

/--
Definition of `basisOfBasisRight` / `basisOfBasisRight` 的定义

English:
definition basisOfBasisRight
  signature: (H' : A ⊔ B = ⊤) {ι : Type*} (b : Basis ι R B)
  body: (b.baseChange A).map (H.mulMapLeftOfSupEqTop H').toLinearEquiv

@[simp]

中文:
定义 basisOfBasisRight
  签名: (H' : A ⊔ B = ⊤) {ι : 类型} (b : Basis ι R B)
  定义体: (b.baseChange A).map (H.mulMapLeftOfSupEqTop H').toLinearEquiv

@[simp]

Depends on / 依赖: H.mulMapLeftOfSupEqTop, b.baseChange, baseChange, mulMapLeftOfSupEqTop, toLinearEquiv
-/
noncomputable def basisOfBasisRight (H' : A ⊔ B = ⊤) {ι : Type*} (b : Basis ι R B) :
    Basis ι A S :=
  (b.baseChange A).map (H.mulMapLeftOfSupEqTop H').toLinearEquiv

@[simp]
/--
theorem `algebraMap_basisOfBasisRight_apply` / 定理 `algebraMap_basisOfBasisRight_apply`

English:
theorem algebraMap_basisOfBasisRight_apply
  given: (H' : A ⊔ B = ⊤) {ι : Type*} (b : Basis ι R B) (i : ι)
  proof: by
  simp [basisOfBasisRight]

@[simp]

中文:
定理 algebraMap_basisOfBasisRight_apply
  条件: (H' : A ⊔ B = ⊤) {ι : 类型} (b : Basis ι R B) (i : ι)
  证明: by
  simp [basisOfBasisRight]

@[simp]

Depends on / 依赖: basisOfBasisRight
-/
theorem algebraMap_basisOfBasisRight_apply (H' : A ⊔ B = ⊤) {ι : Type*} (b : Basis ι R B) (i : ι) :
    H.basisOfBasisRight H' b i = algebraMap B S (b i) := by
  simp [basisOfBasisRight]

@[simp]
/--
theorem `mulMapLeftOfSupEqTop_symm_apply` / 定理 `mulMapLeftOfSupEqTop_symm_apply`

English:
theorem mulMapLeftOfSupEqTop_symm_apply
  given: (H' : A ⊔ B = ⊤) (x : B)
  proof: (H.mulMapLeftOfSupEqTop H').symm_apply_eq.mpr (by simp)

中文:
定理 mulMapLeftOfSupEqTop_symm_apply
  条件: (H' : A ⊔ B = ⊤) (x : B)
  证明: (H.mulMapLeftOfSupEqTop H').symm_apply_eq.mpr (by simp)

Depends on / 依赖: H.mulMapLeftOfSupEqTop, mulMapLeftOfSupEqTop, symm_apply_eq, symm_apply_eq.mpr
-/
theorem mulMapLeftOfSupEqTop_symm_apply (H' : A ⊔ B = ⊤) (x : B) :
    (H.mulMapLeftOfSupEqTop H').symm x = 1 otimesₜ[R] x :=
  (H.mulMapLeftOfSupEqTop H').symm_apply_eq.mpr (by simp)

/--
theorem `algebraMap_basisOfBasisRight_repr_apply` / 定理 `algebraMap_basisOfBasisRight_repr_apply`

English:
theorem algebraMap_basisOfBasisRight_repr_apply
  statement: (H' : A ⊔ B = ⊤) {ι : Type*} (b : Basis ι R B)
  proof: by
  simp [basisOfBasisRight, Algebra.algebraMap_eq_smul_one]

中文:
定理 algebraMap_basisOfBasisRight_repr_apply
  结论: (H' : A ⊔ B = ⊤) {ι : 类型} (b : Basis ι R B)
  证明: by
  simp [basisOfBasisRight, Algebra.algebraMap_eq_smul_one]

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, algebraMap_eq_smul_one, basisOfBasisRight
-/
theorem algebraMap_basisOfBasisRight_repr_apply (H' : A ⊔ B = ⊤) {ι : Type*} (b : Basis ι R B)
    (x : B) (i : ι) :
    algebraMap A S ((H.basisOfBasisRight H' b).repr x i) = algebraMap R S (b.repr x i) := by
  simp [basisOfBasisRight, Algebra.algebraMap_eq_smul_one]

/--
theorem `leftMulMatrix_basisOfBasisRight_algebraMap` / 定理 `leftMulMatrix_basisOfBasisRight_algebraMap`

English:
theorem leftMulMatrix_basisOfBasisRight_algebraMap
  statement: (H' : A ⊔ B = ⊤) {ι : Type*} [Fintype ι]
  proof: by
  ext
  simp [Algebra.leftMulMatrix_eq_repr_mul, ← H.algebraMap_basisOfBasisRight_repr_apply H']

中文:
定理 leftMulMatrix_basisOfBasisRight_algebraMap
  结论: (H' : A ⊔ B = ⊤) {ι : 类型} [Fintype ι]
  证明: by
  ext
  simp [Algebra.leftMulMatrix_eq_repr_mul, ← H.algebraMap_basisOfBasisRight_repr_apply H']

Depends on / 依赖: Algebra, Algebra.leftMulMatrix_eq_repr_mul, H.algebraMap_basisOfBasisRight_repr_apply, algebraMap_basisOfBasisRight_repr_apply, leftMulMatrix_eq_repr_mul
-/
theorem leftMulMatrix_basisOfBasisRight_algebraMap (H' : A ⊔ B = ⊤) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : Basis ι R B) (x : B) :
    Algebra.leftMulMatrix (H.basisOfBasisRight H' b) (algebraMap B S x) =
      RingHom.mapMatrix (algebraMap R A) (Algebra.leftMulMatrix b x) := by
  ext
  simp [Algebra.leftMulMatrix_eq_repr_mul, ← H.algebraMap_basisOfBasisRight_repr_apply H']

/--
Definition of `basisOfBasisLeft` / `basisOfBasisLeft` 的定义

English:
definition basisOfBasisLeft
  signature: (H' : A ⊔ B = ⊤) {ι : Type*} (b : Basis ι R A)
  body: (b.baseChange B).map (H.symm.mulMapLeftOfSupEqTop (by rwa [sup_comm])).toLinearEquiv

@[simp]

中文:
定义 basisOfBasisLeft
  签名: (H' : A ⊔ B = ⊤) {ι : 类型} (b : Basis ι R A)
  定义体: (b.baseChange B).map (H.symm.mulMapLeftOfSupEqTop (by rwa [sup_comm])).toLinearEquiv

@[simp]

Depends on / 依赖: H.symm.mulMapLeftOfSupEqTop, b.baseChange, baseChange, mulMapLeftOfSupEqTop, sup_comm, toLinearEquiv
-/
noncomputable def basisOfBasisLeft (H' : A ⊔ B = ⊤) {ι : Type*} (b : Basis ι R A) :
    Basis ι B S :=
  (b.baseChange B).map (H.symm.mulMapLeftOfSupEqTop (by rwa [sup_comm])).toLinearEquiv

@[simp]
/--
theorem `basisOfBasisLeft_apply` / 定理 `basisOfBasisLeft_apply`

English:
theorem basisOfBasisLeft_apply
  given: (H' : A ⊔ B = ⊤) {ι : Type*} (b : Basis ι R A) (i : ι)
  proof: H.symm.algebraMap_basisOfBasisRight_apply (by rwa [sup_comm]) b i

中文:
定理 basisOfBasisLeft_apply
  条件: (H' : A ⊔ B = ⊤) {ι : 类型} (b : Basis ι R A) (i : ι)
  证明: H.symm.algebraMap_basisOfBasisRight_apply (by rwa [sup_comm]) b i

Depends on / 依赖: H.symm.algebraMap_basisOfBasisRight_apply, algebraMap_basisOfBasisRight_apply, sup_comm
-/
theorem basisOfBasisLeft_apply (H' : A ⊔ B = ⊤) {ι : Type*} (b : Basis ι R A) (i : ι) :
    H.basisOfBasisLeft H' b i = algebraMap A S (b i) :=
  H.symm.algebraMap_basisOfBasisRight_apply (by rwa [sup_comm]) b i

/--
theorem `basisOfBasisLeft_repr_apply` / 定理 `basisOfBasisLeft_repr_apply`

English:
theorem basisOfBasisLeft_repr_apply
  statement: (H' : A ⊔ B = ⊤) {ι : Type*} (b : Basis ι R A)
  proof: H.symm.algebraMap_basisOfBasisRight_repr_apply (by rwa [sup_comm]) b x i

include H in

中文:
定理 basisOfBasisLeft_repr_apply
  结论: (H' : A ⊔ B = ⊤) {ι : 类型} (b : Basis ι R A)
  证明: H.symm.algebraMap_basisOfBasisRight_repr_apply (by rwa [sup_comm]) b x i

include H in

Depends on / 依赖: H.symm.algebraMap_basisOfBasisRight_repr_apply, algebraMap_basisOfBasisRight_repr_apply, sup_comm
-/
theorem basisOfBasisLeft_repr_apply (H' : A ⊔ B = ⊤) {ι : Type*} (b : Basis ι R A)
    (x : A) (i : ι) :
    algebraMap B S ((H.basisOfBasisLeft H' b).repr x i) = algebraMap R S (b.repr x i) :=
  H.symm.algebraMap_basisOfBasisRight_repr_apply (by rwa [sup_comm]) b x i

include H in
/--
theorem `sup_free_of_free` / 定理 `sup_free_of_free`

English:
theorem sup_free_of_free
  given: [Module.Free R A] [Module.Free R B]
  statement: Module.Free R ↥(A ⊔ B)
  proof: Module.Free.of_equiv H.mulMap.toLinearEquiv

include H in

中文:
定理 sup_free_of_free
  条件: [Module.Free R A] [Module.Free R B]
  结论: Module.Free R ↥(A ⊔ B)
  证明: Module.Free.of_equiv H.mulMap.toLinearEquiv

include H in

Depends on / 依赖: H.mulMap.toLinearEquiv, Module, Module.Free.of_equiv, mulMap, of_equiv, toLinearEquiv
-/
theorem sup_free_of_free [Module.Free R A] [Module.Free R B] : Module.Free R ↥(A ⊔ B) :=
  Module.Free.of_equiv H.mulMap.toLinearEquiv

include H in
/--
theorem `isDomain` / 定理 `isDomain`

English:
theorem isDomain
  given: [IsDomain S]
  statement: IsDomain (A otimes[R] B)
  proof: H.injective.isDomain (A.mulMap B).toRingHom

中文:
定理 isDomain
  条件: [IsDomain S]
  结论: IsDomain (A otimes[R] B)
  证明: H.injective.isDomain (A.mulMap B).toRingHom

Depends on / 依赖: A.mulMap, H.injective.isDomain, injective, isDomain, mulMap, toRingHom
-/
theorem isDomain [IsDomain S] : IsDomain (A otimes[R] B) :=
  H.injective.isDomain (A.mulMap B).toRingHom

/--
theorem `isDomain_of_injective` / 定理 `isDomain_of_injective`

English:
theorem isDomain_of_injective
  statement: [IsDomain S] {A B : Type*} [Semiring A] [Semiring B]
  proof: have := H.isDomain
  (Algebra.TensorProduct.congr
    (AlgEquiv.ofInjective fa hfa) (AlgEquiv.ofInjective fb hfb)).toMulEquiv.isDomain

中文:
定理 isDomain_of_injective
  结论: [IsDomain S] {A B : 类型} [Semiring A] [Semiring B]
  证明: have := H.isDomain
  (Algebra.TensorProduct.congr
    (AlgEquiv.ofInjective fa hfa) (AlgEquiv.ofInjective fb hfb)).toMulEquiv.isDomain

Depends on / 依赖: AlgEquiv, AlgEquiv.ofInjective, Algebra, Algebra.TensorProduct.congr, H.isDomain, TensorProduct, isDomain, ofInjective, toMulEquiv, toMulEquiv.isDomain
-/
theorem isDomain_of_injective [IsDomain S] {A B : Type*} [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] {fa : A ->ₐ[R] S} {fb : B ->ₐ[R] S}
    (hfa : Function.Injective fa) (hfb : Function.Injective fb)
    (H : fa.range.LinearDisjoint fb.range) : IsDomain (A otimes[R] B) :=
  have := H.isDomain
  (Algebra.TensorProduct.congr
    (AlgEquiv.ofInjective fa hfa) (AlgEquiv.ofInjective fb hfb)).toMulEquiv.isDomain

end LinearDisjoint

end CommSemiring

section Ring

namespace LinearDisjoint

variable [CommRing R] [Ring S] [Algebra R S]

variable (A B : Subalgebra R S)

/--
lemma `mulLeftMap_ker_eq_bot_iff_linearIndependent_op` / 引理 `mulLeftMap_ker_eq_bot_iff_linearIndependent_op`

English:
lemma mulLeftMap_ker_eq_bot_iff_linearIndependent_op
  given: {ι : Type*} (a : ι -> A)
  proof: by
  simp_rw [LinearIndependent, LinearMap.ker_eq_bot]
  let i : (ι ->₀ B) ->ₗ[R] S := Submodule.mulLeftMap (M := toSubmodule A) (toSubmodule B) a
  let j : (ι ->₀ B) ->ₗ[R] S := (MulOpposite.opLinearEquiv _).symm.toLinearMap ∘ₗ
    (Finsupp.linearCombination B.op (MulOpposite.op ∘ A.val ∘ a)).restr

中文:
引理 mulLeftMap_ker_eq_bot_iff_linearIndependent_op
  条件: {ι : 类型} (a : ι -> A)
  证明: by
  simp_rw [LinearIndependent, LinearMap.ker_eq_bot]
  let i : (ι ->₀ B) ->ₗ[R] S := Submodule.mulLeftMap (M := toSubmodule A) (toSubmodule B) a
  let j : (ι ->₀ B) ->ₗ[R] S := (MulOpposite.opLinearEquiv _).symm.toLinearMap ∘ₗ
    (Finsupp.linearCombination B.op (MulOpposite.op ∘ A.val ∘ a)).restr

Depends on / 依赖: toSubmodule
-/
lemma mulLeftMap_ker_eq_bot_iff_linearIndependent_op {ι : Type*} (a : ι -> A) :
    LinearMap.ker (Submodule.mulLeftMap (M := toSubmodule A) (toSubmodule B) a) = ⊥ ↔
    LinearIndependent B.op (MulOpposite.op ∘ A.val ∘ a) := by
  simp_rw [LinearIndependent, LinearMap.ker_eq_bot]
  let i : (ι ->₀ B) ->ₗ[R] S := Submodule.mulLeftMap (M := toSubmodule A) (toSubmodule B) a
  let j : (ι ->₀ B) ->ₗ[R] S := (MulOpposite.opLinearEquiv _).symm.toLinearMap ∘ₗ
    (Finsupp.linearCombination B.op (MulOpposite.op ∘ A.val ∘ a)).restrictScalars R ∘ₗ
    (Finsupp.mapRange.linearEquiv (linearEquivOp B)).toLinearMap
  suffices i = j by
    change Function.Injective i ↔ _
    simp_rw [this, j, LinearMap.coe_comp, LinearEquiv.coe_coe, EquivLike.comp_injective,
      EquivLike.injective_comp, LinearMap.coe_restrictScalars]
  ext
  simp only [LinearMap.coe_comp, Function.comp_apply, Finsupp.lsingle_apply, coe_val,
    Finsupp.mapRange.linearEquiv_toLinearMap, LinearEquiv.coe_coe,
    MulOpposite.coe_opLinearEquiv_symm, LinearMap.coe_restrictScalars,
    Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single, Finsupp.linearCombination_single,
    MulOpposite.unop_smul, MulOpposite.unop_op, i, j]
  exact Submodule.mulLeftMap_apply_single _ _ _

variable {A B} in
/--
theorem `linearIndependent_left_op_of_flat` / 定理 `linearIndependent_left_op_of_flat`

English:
theorem linearIndependent_left_op_of_flat
  statement: (H : A.LinearDisjoint B) [Module.Flat R B]
  proof: by
  have h := Submodule.LinearDisjoint.linearIndependent_left_of_flat H ha
  rwa [mulLeftMap_ker_eq_bot_iff_linearIndependent_op] at h

中文:
定理 linearIndependent_left_op_of_flat
  结论: (H : A.LinearDisjoint B) [Module.Flat R B]
  证明: by
  have h := Submodule.LinearDisjoint.linearIndependent_left_of_flat H ha
  rwa [mulLeftMap_ker_eq_bot_iff_linearIndependent_op] at h

Depends on / 依赖: LinearDisjoint, Submodule, Submodule.LinearDisjoint.linearIndependent_left_of_flat, linearIndependent_left_of_flat, mulLeftMap_ker_eq_bot_iff_linearIndependent_op
-/
theorem linearIndependent_left_op_of_flat (H : A.LinearDisjoint B) [Module.Flat R B]
    {ι : Type*} {a : ι -> A} (ha : LinearIndependent R a) :
    LinearIndependent B.op (MulOpposite.op ∘ A.val ∘ a) := by
  have h := Submodule.LinearDisjoint.linearIndependent_left_of_flat H ha
  rwa [mulLeftMap_ker_eq_bot_iff_linearIndependent_op] at h

/--
theorem `of_basis_left_op` / 定理 `of_basis_left_op`

English:
theorem of_basis_left_op
  statement: {ι : Type*} (a : Basis ι R A)
  proof: by
  rw [← mulLeftMap_ker_eq_bot_iff_linearIndependent_op] at H
  exact Submodule.LinearDisjoint.of_basis_left _ _ a H

中文:
定理 of_basis_left_op
  结论: {ι : 类型} (a : Basis ι R A)
  证明: by
  rw [← mulLeftMap_ker_eq_bot_iff_linearIndependent_op] at H
  exact Submodule.LinearDisjoint.of_basis_left _ _ a H

Depends on / 依赖: LinearDisjoint, Submodule, Submodule.LinearDisjoint.of_basis_left, mulLeftMap_ker_eq_bot_iff_linearIndependent_op, of_basis_left
-/
theorem of_basis_left_op {ι : Type*} (a : Basis ι R A)
    (H : LinearIndependent B.op (MulOpposite.op ∘ A.val ∘ a)) :
    A.LinearDisjoint B := by
  rw [← mulLeftMap_ker_eq_bot_iff_linearIndependent_op] at H
  exact Submodule.LinearDisjoint.of_basis_left _ _ a H

/--
lemma `mulRightMap_ker_eq_bot_iff_linearIndependent` / 引理 `mulRightMap_ker_eq_bot_iff_linearIndependent`

English:
lemma mulRightMap_ker_eq_bot_iff_linearIndependent
  given: {ι : Type*} (b : ι -> B)
  proof: by
  simp_rw [LinearIndependent, LinearMap.ker_eq_bot]
  let i : (ι ->₀ A) ->ₗ[R] S := Submodule.mulRightMap (toSubmodule A) (N := toSubmodule B) b
  let j : (ι ->₀ A) ->ₗ[R] S := (Finsupp.linearCombination A (B.val ∘ b)).restrictScalars R
  suffices i = j by change Function.Injective i ↔ Function.I

中文:
引理 mulRightMap_ker_eq_bot_iff_linearIndependent
  条件: {ι : 类型} (b : ι -> B)
  证明: by
  simp_rw [LinearIndependent, LinearMap.ker_eq_bot]
  let i : (ι ->₀ A) ->ₗ[R] S := Submodule.mulRightMap (toSubmodule A) (N := toSubmodule B) b
  let j : (ι ->₀ A) ->ₗ[R] S := (Finsupp.linearCombination A (B.val ∘ b)).restrictScalars R
  suffices i = j by change Function.Injective i ↔ Function.I

Depends on / 依赖: toSubmodule
-/
lemma mulRightMap_ker_eq_bot_iff_linearIndependent {ι : Type*} (b : ι -> B) :
    LinearMap.ker (Submodule.mulRightMap (toSubmodule A) (N := toSubmodule B) b) = ⊥ ↔
    LinearIndependent A (B.val ∘ b) := by
  simp_rw [LinearIndependent, LinearMap.ker_eq_bot]
  let i : (ι ->₀ A) ->ₗ[R] S := Submodule.mulRightMap (toSubmodule A) (N := toSubmodule B) b
  let j : (ι ->₀ A) ->ₗ[R] S := (Finsupp.linearCombination A (B.val ∘ b)).restrictScalars R
  suffices i = j by change Function.Injective i ↔ Function.Injective j; rw [this]
  ext
  simp only [LinearMap.coe_comp, Function.comp_apply, Finsupp.lsingle_apply, coe_val,
    LinearMap.coe_restrictScalars, Finsupp.linearCombination_single, i, j]
  exact Submodule.mulRightMap_apply_single _ _ _

variable {A B} in
/--
theorem `linearIndependent_right_of_flat` / 定理 `linearIndependent_right_of_flat`

English:
theorem linearIndependent_right_of_flat
  statement: (H : A.LinearDisjoint B) [Module.Flat R A]
  proof: by
  have h := Submodule.LinearDisjoint.linearIndependent_right_of_flat H hb
  rwa [mulRightMap_ker_eq_bot_iff_linearIndependent] at h

中文:
定理 linearIndependent_right_of_flat
  结论: (H : A.LinearDisjoint B) [Module.Flat R A]
  证明: by
  have h := Submodule.LinearDisjoint.linearIndependent_right_of_flat H hb
  rwa [mulRightMap_ker_eq_bot_iff_linearIndependent] at h

Depends on / 依赖: LinearDisjoint, Submodule, Submodule.LinearDisjoint.linearIndependent_right_of_flat, linearIndependent_right_of_flat, mulRightMap_ker_eq_bot_iff_linearIndependent
-/
theorem linearIndependent_right_of_flat (H : A.LinearDisjoint B) [Module.Flat R A]
    {ι : Type*} {b : ι -> B} (hb : LinearIndependent R b) :
    LinearIndependent A (B.val ∘ b) := by
  have h := Submodule.LinearDisjoint.linearIndependent_right_of_flat H hb
  rwa [mulRightMap_ker_eq_bot_iff_linearIndependent] at h

/--
theorem `of_basis_right` / 定理 `of_basis_right`

English:
theorem of_basis_right
  statement: {ι : Type*} (b : Basis ι R B)
  proof: by
  rw [← mulRightMap_ker_eq_bot_iff_linearIndependent] at H
  exact Submodule.LinearDisjoint.of_basis_right _ _ b H

中文:
定理 of_basis_right
  结论: {ι : 类型} (b : Basis ι R B)
  证明: by
  rw [← mulRightMap_ker_eq_bot_iff_linearIndependent] at H
  exact Submodule.LinearDisjoint.of_basis_right _ _ b H

Depends on / 依赖: LinearDisjoint, Submodule, Submodule.LinearDisjoint.of_basis_right, mulRightMap_ker_eq_bot_iff_linearIndependent, of_basis_right
-/
theorem of_basis_right {ι : Type*} (b : Basis ι R B)
    (H : LinearIndependent A (B.val ∘ b)) : A.LinearDisjoint B := by
  rw [← mulRightMap_ker_eq_bot_iff_linearIndependent] at H
  exact Submodule.LinearDisjoint.of_basis_right _ _ b H

variable {A B} in
/--
theorem `linearIndependent_left_of_flat_of_commute` / 定理 `linearIndependent_left_of_flat_of_commute`

English:
theorem linearIndependent_left_of_flat_of_commute
  statement: (H : A.LinearDisjoint B) [Module.Flat R B]
  proof: (H.symm_of_commute hc).linearIndependent_right_of_flat ha

中文:
定理 linearIndependent_left_of_flat_of_commute
  结论: (H : A.LinearDisjoint B) [Module.Flat R B]
  证明: (H.symm_of_commute hc).linearIndependent_right_of_flat ha

Depends on / 依赖: H.symm_of_commute, linearIndependent_right_of_flat, symm_of_commute
-/
theorem linearIndependent_left_of_flat_of_commute (H : A.LinearDisjoint B) [Module.Flat R B]
    {ι : Type*} {a : ι -> A} (ha : LinearIndependent R a)
    (hc : forall (a : A) (b : B), Commute a.1 b.1) : LinearIndependent B (A.val ∘ a) :=
  (H.symm_of_commute hc).linearIndependent_right_of_flat ha

/--
theorem `of_basis_left_of_commute` / 定理 `of_basis_left_of_commute`

English:
theorem of_basis_left_of_commute
  statement: {ι : Type*} (a : Basis ι R A)
  proof: (of_basis_right B A a H).symm_of_commute fun _ _ => (hc _ _).symm

中文:
定理 of_basis_left_of_commute
  结论: {ι : 类型} (a : Basis ι R A)
  证明: (of_basis_right B A a H).symm_of_commute fun _ _ => (hc _ _).symm

Depends on / 依赖: of_basis_right, symm_of_commute
-/
theorem of_basis_left_of_commute {ι : Type*} (a : Basis ι R A)
    (H : LinearIndependent B (A.val ∘ a)) (hc : forall (a : A) (b : B), Commute a.1 b.1) :
    A.LinearDisjoint B :=
  (of_basis_right B A a H).symm_of_commute fun _ _ => (hc _ _).symm

variable {A B} in
/--
theorem `linearIndependent_mul_of_flat_left` / 定理 `linearIndependent_mul_of_flat_left`

English:
theorem linearIndependent_mul_of_flat_left
  statement: (H : A.LinearDisjoint B) [Module.Flat R A]
  proof: Submodule.LinearDisjoint.linearIndependent_mul_of_flat_left H ha hb

中文:
定理 linearIndependent_mul_of_flat_left
  结论: (H : A.LinearDisjoint B) [Module.Flat R A]
  证明: Submodule.LinearDisjoint.linearIndependent_mul_of_flat_left H ha hb

Depends on / 依赖: LinearDisjoint, Submodule, Submodule.LinearDisjoint.linearIndependent_mul_of_flat_left, linearIndependent_mul_of_flat_left
-/
theorem linearIndependent_mul_of_flat_left (H : A.LinearDisjoint B) [Module.Flat R A]
    {κ ι : Type*} {a : κ -> A} {b : ι -> B} (ha : LinearIndependent R a)
    (hb : LinearIndependent R b) : LinearIndependent R fun (i : κ × ι) => (a i.1).1 * (b i.2).1 :=
  Submodule.LinearDisjoint.linearIndependent_mul_of_flat_left H ha hb

variable {A B} in
/--
theorem `linearIndependent_mul_of_flat_right` / 定理 `linearIndependent_mul_of_flat_right`

English:
theorem linearIndependent_mul_of_flat_right
  statement: (H : A.LinearDisjoint B) [Module.Flat R B]
  proof: Submodule.LinearDisjoint.linearIndependent_mul_of_flat_right H ha hb

中文:
定理 linearIndependent_mul_of_flat_right
  结论: (H : A.LinearDisjoint B) [Module.Flat R B]
  证明: Submodule.LinearDisjoint.linearIndependent_mul_of_flat_right H ha hb

Depends on / 依赖: LinearDisjoint, Submodule, Submodule.LinearDisjoint.linearIndependent_mul_of_flat_right, linearIndependent_mul_of_flat_right
-/
theorem linearIndependent_mul_of_flat_right (H : A.LinearDisjoint B) [Module.Flat R B]
    {κ ι : Type*} {a : κ -> A} {b : ι -> B} (ha : LinearIndependent R a)
    (hb : LinearIndependent R b) : LinearIndependent R fun (i : κ × ι) => (a i.1).1 * (b i.2).1 :=
  Submodule.LinearDisjoint.linearIndependent_mul_of_flat_right H ha hb

variable {A B} in
/--
theorem `linearIndependent_mul_of_flat` / 定理 `linearIndependent_mul_of_flat`

English:
theorem linearIndependent_mul_of_flat
  statement: (H : A.LinearDisjoint B)
  proof: Submodule.LinearDisjoint.linearIndependent_mul_of_flat H hf ha hb

中文:
定理 linearIndependent_mul_of_flat
  结论: (H : A.LinearDisjoint B)
  证明: Submodule.LinearDisjoint.linearIndependent_mul_of_flat H hf ha hb

Depends on / 依赖: LinearDisjoint, Submodule, Submodule.LinearDisjoint.linearIndependent_mul_of_flat, linearIndependent_mul_of_flat
-/
theorem linearIndependent_mul_of_flat (H : A.LinearDisjoint B)
    (hf : Module.Flat R A ∨ Module.Flat R B)
    {κ ι : Type*} {a : κ -> A} {b : ι -> B} (ha : LinearIndependent R a)
    (hb : LinearIndependent R b) : LinearIndependent R fun (i : κ × ι) => (a i.1).1 * (b i.2).1 :=
  Submodule.LinearDisjoint.linearIndependent_mul_of_flat H hf ha hb

/--
theorem `of_basis_mul` / 定理 `of_basis_mul`

English:
theorem of_basis_mul
  statement: {κ ι : Type*} (a : Basis κ R A) (b : Basis ι R B)
  proof: Submodule.LinearDisjoint.of_basis_mul _ _ a b H

中文:
定理 of_basis_mul
  结论: {κ ι : 类型} (a : Basis κ R A) (b : Basis ι R B)
  证明: Submodule.LinearDisjoint.of_basis_mul _ _ a b H

Depends on / 依赖: LinearDisjoint, Submodule, Submodule.LinearDisjoint.of_basis_mul, of_basis_mul
-/
theorem of_basis_mul {κ ι : Type*} (a : Basis κ R A) (b : Basis ι R B)
    (H : LinearIndependent R fun (i : κ × ι) => (a i.1).1 * (b i.2).1) : A.LinearDisjoint B :=
  Submodule.LinearDisjoint.of_basis_mul _ _ a b H

variable {A B}

section

variable (H : A.LinearDisjoint B)
include H

/--
theorem `of_le_left_of_flat` / 定理 `of_le_left_of_flat`

English:
theorem of_le_left_of_flat
  statement: {A' : Subalgebra R S}
  proof: Submodule.LinearDisjoint.of_le_left_of_flat H h

中文:
定理 of_le_left_of_flat
  结论: {A' : Subalgebra R S}
  证明: Submodule.LinearDisjoint.of_le_left_of_flat H h

Depends on / 依赖: LinearDisjoint, Submodule, Submodule.LinearDisjoint.of_le_left_of_flat, of_le_left_of_flat
-/
theorem of_le_left_of_flat {A' : Subalgebra R S}
    (h : A' <= A) [Module.Flat R B] : A'.LinearDisjoint B :=
  Submodule.LinearDisjoint.of_le_left_of_flat H h

/--
theorem `of_le_right_of_flat` / 定理 `of_le_right_of_flat`

English:
theorem of_le_right_of_flat
  statement: {B' : Subalgebra R S}
  proof: Submodule.LinearDisjoint.of_le_right_of_flat H h

中文:
定理 of_le_right_of_flat
  结论: {B' : Subalgebra R S}
  证明: Submodule.LinearDisjoint.of_le_right_of_flat H h

Depends on / 依赖: LinearDisjoint, Submodule, Submodule.LinearDisjoint.of_le_right_of_flat, of_le_right_of_flat
-/
theorem of_le_right_of_flat {B' : Subalgebra R S}
    (h : B' <= B) [Module.Flat R A] : A.LinearDisjoint B' :=
  Submodule.LinearDisjoint.of_le_right_of_flat H h

/--
theorem `of_le_of_flat_right` / 定理 `of_le_of_flat_right`

English:
theorem of_le_of_flat_right
  statement: {A' B' : Subalgebra R S}
  proof: (H.of_le_left_of_flat ha).of_le_right_of_flat hb

中文:
定理 of_le_of_flat_right
  结论: {A' B' : Subalgebra R S}
  证明: (H.of_le_left_of_flat ha).of_le_right_of_flat hb

Depends on / 依赖: H.of_le_left_of_flat, of_le_left_of_flat, of_le_right_of_flat
-/
theorem of_le_of_flat_right {A' B' : Subalgebra R S}
    (ha : A' <= A) (hb : B' <= B) [Module.Flat R B] [Module.Flat R A'] :
    A'.LinearDisjoint B' := (H.of_le_left_of_flat ha).of_le_right_of_flat hb

/--
theorem `of_le_of_flat_left` / 定理 `of_le_of_flat_left`

English:
theorem of_le_of_flat_left
  statement: {A' B' : Subalgebra R S}
  proof: (H.of_le_right_of_flat hb).of_le_left_of_flat ha

中文:
定理 of_le_of_flat_left
  结论: {A' B' : Subalgebra R S}
  证明: (H.of_le_right_of_flat hb).of_le_left_of_flat ha

Depends on / 依赖: H.of_le_right_of_flat, of_le_left_of_flat, of_le_right_of_flat
-/
theorem of_le_of_flat_left {A' B' : Subalgebra R S}
    (ha : A' <= A) (hb : B' <= B) [Module.Flat R A] [Module.Flat R B'] :
    A'.LinearDisjoint B' := (H.of_le_right_of_flat hb).of_le_left_of_flat ha

/--
theorem `rank_inf_eq_one_of_commute_of_flat_of_inj` / 定理 `rank_inf_eq_one_of_commute_of_flat_of_inj`

English:
theorem rank_inf_eq_one_of_commute_of_flat_of_inj
  statement: (hf : Module.Flat R A ∨ Module.Flat R B)
  proof: by
  nontriviality R
  refine le_antisymm (Submodule.LinearDisjoint.rank_inf_le_one_of_commute_of_flat H hf hc) ?_
  have : Cardinal.lift.{u} (Module.rank R (⊥ : Subalgebra R S)) =
      Cardinal.lift.{v} (Module.rank R R) :=
    lift_rank_range_of_injective (Algebra.linearMap R S) hinj
  rw [Module

中文:
定理 rank_inf_eq_one_of_commute_of_flat_of_inj
  结论: (hf : Module.Flat R A ∨ Module.Flat R B)
  证明: by
  nontriviality R
  refine le_antisymm (Submodule.LinearDisjoint.rank_inf_le_one_of_commute_of_flat H hf hc) ?_
  have : Cardinal.lift.{u} (Module.rank R (⊥ : Subalgebra R S)) =
      Cardinal.lift.{v} (Module.rank R R) :=
    lift_rank_range_of_injective (Algebra.linearMap R S) hinj
  rw [Module

Depends on / 依赖: Algebra, Algebra.linearMap, Cardinal, Cardinal.lift, Cardinal.lift_eq_one, Cardinal.lift_one, LinearDisjoint, Module, Module.rank, Module.rank_self, Subalgebra, Submodule, Submodule.LinearDisjoint.rank_inf_le_one_of_commute_of_flat, Submodule.rank_mono, bot_le, le_antisymm, lift_eq_one, lift_one, lift_rank_range_of_injective, linearMap
-/
theorem rank_inf_eq_one_of_commute_of_flat_of_inj (hf : Module.Flat R A ∨ Module.Flat R B)
    (hc : forall (a b : ↥(A ⊓ B)), Commute a.1 b.1)
    (hinj : Function.Injective (algebraMap R S)) : Module.rank R ↥(A ⊓ B) = 1 := by
  nontriviality R
  refine le_antisymm (Submodule.LinearDisjoint.rank_inf_le_one_of_commute_of_flat H hf hc) ?_
  have : Cardinal.lift.{u} (Module.rank R (⊥ : Subalgebra R S)) =
      Cardinal.lift.{v} (Module.rank R R) :=
    lift_rank_range_of_injective (Algebra.linearMap R S) hinj
  rw [Module.rank_self]; rw [Cardinal.lift_one]; rw [Cardinal.lift_eq_one] at this
  rw [← this]
  change Module.rank R (toSubmodule (⊥ : Subalgebra R S)) <=
    Module.rank R (toSubmodule (A ⊓ B))
  exact Submodule.rank_mono (bot_le : (⊥ : Subalgebra R S) <= A ⊓ B)

/--
theorem `rank_inf_eq_one_of_commute_of_flat_left_of_inj` / 定理 `rank_inf_eq_one_of_commute_of_flat_left_of_inj`

English:
theorem rank_inf_eq_one_of_commute_of_flat_left_of_inj
  statement: [Module.Flat R A]
  proof: H.rank_inf_eq_one_of_commute_of_flat_of_inj (Or.inl ‹_›) hc hinj

中文:
定理 rank_inf_eq_one_of_commute_of_flat_left_of_inj
  结论: [Module.Flat R A]
  证明: H.rank_inf_eq_one_of_commute_of_flat_of_inj (Or.inl ‹_›) hc hinj

Depends on / 依赖: H.rank_inf_eq_one_of_commute_of_flat_of_inj, Or.inl, rank_inf_eq_one_of_commute_of_flat_of_inj
-/
theorem rank_inf_eq_one_of_commute_of_flat_left_of_inj [Module.Flat R A]
    (hc : forall (a b : ↥(A ⊓ B)), Commute a.1 b.1)
    (hinj : Function.Injective (algebraMap R S)) : Module.rank R ↥(A ⊓ B) = 1 :=
  H.rank_inf_eq_one_of_commute_of_flat_of_inj (Or.inl ‹_›) hc hinj

/--
theorem `rank_inf_eq_one_of_commute_of_flat_right_of_inj` / 定理 `rank_inf_eq_one_of_commute_of_flat_right_of_inj`

English:
theorem rank_inf_eq_one_of_commute_of_flat_right_of_inj
  statement: [Module.Flat R B]
  proof: H.rank_inf_eq_one_of_commute_of_flat_of_inj (Or.inr ‹_›) hc hinj

中文:
定理 rank_inf_eq_one_of_commute_of_flat_right_of_inj
  结论: [Module.Flat R B]
  证明: H.rank_inf_eq_one_of_commute_of_flat_of_inj (Or.inr ‹_›) hc hinj

Depends on / 依赖: H.rank_inf_eq_one_of_commute_of_flat_of_inj, Or.inr, rank_inf_eq_one_of_commute_of_flat_of_inj
-/
theorem rank_inf_eq_one_of_commute_of_flat_right_of_inj [Module.Flat R B]
    (hc : forall (a b : ↥(A ⊓ B)), Commute a.1 b.1)
    (hinj : Function.Injective (algebraMap R S)) : Module.rank R ↥(A ⊓ B) = 1 :=
  H.rank_inf_eq_one_of_commute_of_flat_of_inj (Or.inr ‹_›) hc hinj

end

/--
theorem `rank_eq_one_of_commute_of_flat_of_self_of_inj` / 定理 `rank_eq_one_of_commute_of_flat_of_self_of_inj`

English:
theorem rank_eq_one_of_commute_of_flat_of_self_of_inj
  statement: (H : A.LinearDisjoint A) [Module.Flat R A]
  proof: by
  rw [← inf_of_le_left (le_refl A)] at hc ⊢
  exact H.rank_inf_eq_one_of_commute_of_flat_left_of_inj hc hinj

中文:
定理 rank_eq_one_of_commute_of_flat_of_self_of_inj
  结论: (H : A.LinearDisjoint A) [Module.Flat R A]
  证明: by
  rw [← inf_of_le_left (le_refl A)] at hc ⊢
  exact H.rank_inf_eq_one_of_commute_of_flat_left_of_inj hc hinj

Depends on / 依赖: H.rank_inf_eq_one_of_commute_of_flat_left_of_inj, inf_of_le_left, le_refl, rank_inf_eq_one_of_commute_of_flat_left_of_inj
-/
theorem rank_eq_one_of_commute_of_flat_of_self_of_inj (H : A.LinearDisjoint A) [Module.Flat R A]
    (hc : forall (a b : A), Commute a.1 b.1)
    (hinj : Function.Injective (algebraMap R S)) : Module.rank R A = 1 := by
  rw [← inf_of_le_left (le_refl A)] at hc ⊢
  exact H.rank_inf_eq_one_of_commute_of_flat_left_of_inj hc hinj

end LinearDisjoint

end Ring

section CommRing

namespace LinearDisjoint

variable [CommRing R] [CommRing S] [Algebra R S]

variable {A B : Subalgebra R S}

/--
theorem `trace_algebraMap` / 定理 `trace_algebraMap`

English:
theorem trace_algebraMap
  statement: (H : A.LinearDisjoint B) (H' : A ⊔ B = ⊤) [Module.Free R B]
  proof: by
  simp_rw [Algebra.trace_eq_matrix_trace (Module.Free.chooseBasis R B),
    Algebra.trace_eq_matrix_trace (H.basisOfBasisRight H' (Module.Free.chooseBasis R B)),
    Matrix.trace, map_sum, leftMulMatrix_basisOfBasisRight_algebraMap, RingHom.mapMatrix_apply,
    Matrix.diag_apply, Matrix.map_apply

中文:
定理 trace_algebraMap
  结论: (H : A.LinearDisjoint B) (H' : A ⊔ B = ⊤) [Module.Free R B]
  证明: by
  simp_rw [Algebra.trace_eq_matrix_trace (Module.Free.chooseBasis R B),
    Algebra.trace_eq_matrix_trace (H.basisOfBasisRight H' (Module.Free.chooseBasis R B)),
    Matrix.trace, map_sum, leftMulMatrix_basisOfBasisRight_algebraMap, RingHom.mapMatrix_apply,
    Matrix.diag_apply, Matrix.map_apply

Depends on / 依赖: Algebra, Algebra.trace_eq_matrix_trace, H.basisOfBasisRight, Matrix, Matrix.diag_apply, Matrix.map_apply, Matrix.trace, Module, Module.Free.chooseBasis, RingHom, RingHom.mapMatrix_apply, basisOfBasisRight, chooseBasis, diag_apply, leftMulMatrix_basisOfBasisRight_algebraMap, mapMatrix_apply, map_apply, map_sum, simp_rw, trace_eq_matrix_trace
-/
theorem trace_algebraMap (H : A.LinearDisjoint B) (H' : A ⊔ B = ⊤) [Module.Free R B]
    [Module.Finite R B] (x : B) :
    Algebra.trace A S (algebraMap B S x) = algebraMap R A (Algebra.trace R B x) := by
  simp_rw [Algebra.trace_eq_matrix_trace (Module.Free.chooseBasis R B),
    Algebra.trace_eq_matrix_trace (H.basisOfBasisRight H' (Module.Free.chooseBasis R B)),
    Matrix.trace, map_sum, leftMulMatrix_basisOfBasisRight_algebraMap, RingHom.mapMatrix_apply,
    Matrix.diag_apply, Matrix.map_apply]

/--
theorem `norm_algebraMap` / 定理 `norm_algebraMap`

English:
theorem norm_algebraMap
  statement: (H : A.LinearDisjoint B) (H' : A ⊔ B = ⊤) [Module.Free R B]
  proof: by
  simp_rw [Algebra.norm_eq_matrix_det (Module.Free.chooseBasis R B),
    Algebra.norm_eq_matrix_det (H.basisOfBasisRight H' (Module.Free.chooseBasis R B)),
    leftMulMatrix_basisOfBasisRight_algebraMap, RingHom.map_det]

中文:
定理 norm_algebraMap
  结论: (H : A.LinearDisjoint B) (H' : A ⊔ B = ⊤) [Module.Free R B]
  证明: by
  simp_rw [Algebra.norm_eq_matrix_det (Module.Free.chooseBasis R B),
    Algebra.norm_eq_matrix_det (H.basisOfBasisRight H' (Module.Free.chooseBasis R B)),
    leftMulMatrix_basisOfBasisRight_algebraMap, RingHom.map_det]

Depends on / 依赖: Algebra, Algebra.norm_eq_matrix_det, H.basisOfBasisRight, Module, Module.Free.chooseBasis, RingHom, RingHom.map_det, basisOfBasisRight, chooseBasis, leftMulMatrix_basisOfBasisRight_algebraMap, map_det, norm_eq_matrix_det, simp_rw
-/
theorem norm_algebraMap (H : A.LinearDisjoint B) (H' : A ⊔ B = ⊤) [Module.Free R B]
    [Module.Finite R B] (x : B) :
    Algebra.norm A (algebraMap B S x) = algebraMap R A (Algebra.norm R x) := by
  simp_rw [Algebra.norm_eq_matrix_det (Module.Free.chooseBasis R B),
    Algebra.norm_eq_matrix_det (H.basisOfBasisRight H' (Module.Free.chooseBasis R B)),
    leftMulMatrix_basisOfBasisRight_algebraMap, RingHom.map_det]

/--
theorem `linearIndependent_left_of_flat` / 定理 `linearIndependent_left_of_flat`

English:
theorem linearIndependent_left_of_flat
  statement: (H : A.LinearDisjoint B) [Module.Flat R B]
  proof: H.linearIndependent_left_of_flat_of_commute ha fun _ _ => mul_comm _ _

中文:
定理 linearIndependent_left_of_flat
  结论: (H : A.LinearDisjoint B) [Module.Flat R B]
  证明: H.linearIndependent_left_of_flat_of_commute ha fun _ _ => mul_comm _ _

Depends on / 依赖: H.linearIndependent_left_of_flat_of_commute, linearIndependent_left_of_flat_of_commute, mul_comm
-/
theorem linearIndependent_left_of_flat (H : A.LinearDisjoint B) [Module.Flat R B]
    {ι : Type*} {a : ι -> A} (ha : LinearIndependent R a) : LinearIndependent B (A.val ∘ a) :=
  H.linearIndependent_left_of_flat_of_commute ha fun _ _ => mul_comm _ _

variable (A B) in
/--
theorem `of_basis_left` / 定理 `of_basis_left`

English:
theorem of_basis_left
  statement: {ι : Type*} (a : Basis ι R A)
  proof: of_basis_left_of_commute A B a H fun _ _ => mul_comm _ _

中文:
定理 of_basis_left
  结论: {ι : 类型} (a : Basis ι R A)
  证明: of_basis_left_of_commute A B a H fun _ _ => mul_comm _ _

Depends on / 依赖: mul_comm, of_basis_left_of_commute
-/
theorem of_basis_left {ι : Type*} (a : Basis ι R A)
    (H : LinearIndependent B (A.val ∘ a)) : A.LinearDisjoint B :=
  of_basis_left_of_commute A B a H fun _ _ => mul_comm _ _

variable (R) in
/--
theorem `exists_field_of_isDomain_of_injective` / 定理 `exists_field_of_isDomain_of_injective`

English:
theorem exists_field_of_isDomain_of_injective
  statement: (A : Type v) [CommRing A] (B : Type w) [CommRing B]
  proof: let K := FractionRing (A otimes[R] B)
  let i := IsScalarTower.toAlgHom R (A otimes[R] B) K
  have hi : Function.Injective i := IsFractionRing.injective (A otimes[R] B) K
  ⟨K, inferInstance, inferInstance,
    i.comp Algebra.TensorProduct.includeLeft,
    i.comp Algebra.TensorProduct.includeRight,


中文:
定理 exists_field_of_isDomain_of_injective
  结论: (A : 类型v) [CommRing A] (B : Type w) [CommRing B]
  证明: let K := FractionRing (A otimes[R] B)
  let i := IsScalarTower.toAlgHom R (A otimes[R] B) K
  have hi : Function.Injective i := IsFractionRing.injective (A otimes[R] B) K
  ⟨K, inferInstance, inferInstance,
    i.comp Algebra.TensorProduct.includeLeft,
    i.comp Algebra.TensorProduct.includeRight,


Depends on / 依赖: AlgHom, AlgHom.range_comp, Algebra, Algebra.TensorProduct.includeLeft, Algebra.TensorProduct.includeLeft_injective, Algebra.TensorProduct.includeRight, Algebra.TensorProduct.includeRight_injective, FractionRing, Function, Function.Injective, Injective, IsFractionRing, IsFractionRing.injective, IsScalarTower, IsScalarTower.toAlgHom, TensorProduct, hi.comp, i.comp, includeLeft, includeLeft_injective
-/
theorem exists_field_of_isDomain_of_injective (A : Type v) [CommRing A] (B : Type w) [CommRing B]
    [Algebra R A] [Algebra R B] [Module.Flat R A] [Module.Flat R B] [IsDomain (A otimes[R] B)]
    (ha : Function.Injective (algebraMap R A)) (hb : Function.Injective (algebraMap R B)) :
    exists (K : Type (max v w)) (_ : Field K) (_ : Algebra R K) (fa : A ->ₐ[R] K) (fb : B ->ₐ[R] K),
    Function.Injective fa ∧ Function.Injective fb ∧ fa.range.LinearDisjoint fb.range :=
  let K := FractionRing (A otimes[R] B)
  let i := IsScalarTower.toAlgHom R (A otimes[R] B) K
  have hi : Function.Injective i := IsFractionRing.injective (A otimes[R] B) K
  ⟨K, inferInstance, inferInstance,
    i.comp Algebra.TensorProduct.includeLeft,
    i.comp Algebra.TensorProduct.includeRight,
    hi.comp (Algebra.TensorProduct.includeLeft_injective hb),
    hi.comp (Algebra.TensorProduct.includeRight_injective ha), by
      simpa only [AlgHom.range_comp] using (include_range R A B).map i hi⟩

/--
theorem `of_isField` / 定理 `of_isField`

English:
theorem of_isField
  given: (H : IsField (A otimes[R] B))
  statement: A.LinearDisjoint B
  proof: by
  nontriviality S
  rw [linearDisjoint_iff_injective]
  let : Field (A otimes[R] B) := H.toField
  -- need this otherwise `RingHom.injective` does not work
  let : NonAssocRing (A otimes[R] B) := Ring.toNonAssocRing
  exact RingHom.injective _

中文:
定理 of_isField
  条件: (H : IsField (A otimes[R] B))
  结论: A.LinearDisjoint B
  证明: by
  nontriviality S
  rw [linearDisjoint_iff_injective]
  let : Field (A otimes[R] B) := H.toField
  -- need this otherwise `RingHom.injective` does not work
  let : NonAssocRing (A otimes[R] B) := Ring.toNonAssocRing
  exact RingHom.injective _

Depends on / 依赖: H.toField, linearDisjoint_iff_injective, nontriviality, otimes, toField
-/
theorem of_isField (H : IsField (A otimes[R] B)) : A.LinearDisjoint B := by
  nontriviality S
  rw [linearDisjoint_iff_injective]
  let : Field (A otimes[R] B) := H.toField
  -- need this otherwise `RingHom.injective` does not work
  let : NonAssocRing (A otimes[R] B) := Ring.toNonAssocRing
  exact RingHom.injective _

/--
theorem `of_isField'` / 定理 `of_isField'`

English:
theorem of_isField'
  statement: {A : Type v} [Ring A] {B : Type w} [Ring B]
  proof: by
  apply of_isField
  exact Algebra.TensorProduct.congr (AlgEquiv.ofInjective fa hfa)
.symm.toMulEquiv.isField H (AlgEquiv.ofInjective fb hfb)

中文:
定理 of_isField'
  结论: {A : 类型v} [Ring A] {B : Type w} [Ring B]
  证明: by
  apply of_isField
  exact Algebra.TensorProduct.congr (AlgEquiv.ofInjective fa hfa)
.symm.toMulEquiv.isField H (AlgEquiv.ofInjective fb hfb)

Depends on / 依赖: AlgEquiv, AlgEquiv.ofInjective, Algebra, Algebra.TensorProduct.congr, TensorProduct, isField, ofInjective, of_isField, symm.toMulEquiv.isField, toMulEquiv
-/
theorem of_isField' {A : Type v} [Ring A] {B : Type w} [Ring B]
    [Algebra R A] [Algebra R B] (H : IsField (A otimes[R] B))
    (fa : A ->ₐ[R] S) (fb : B ->ₐ[R] S) (hfa : Function.Injective fa) (hfb : Function.Injective fb) :
    fa.range.LinearDisjoint fb.range := by
  apply of_isField
  exact Algebra.TensorProduct.congr (AlgEquiv.ofInjective fa hfa)
.symm.toMulEquiv.isField H (AlgEquiv.ofInjective fb hfb)

-- need to be in this file since it uses linearly disjoint
open Cardinal Polynomial in
variable (R) in
/--
theorem `_root_.Algebra.TensorProduct.not_isField_of_transcendental` / 定理 `_root_.Algebra.TensorProduct.not_isField_of_transcendental`

English:
theorem _root_.Algebra.TensorProduct.not_isField_of_transcendental
  proof: fun H => by
  let := H.toField
  obtain ⟨a, hta⟩ := ‹Algebra.Transcendental R A›
  obtain ⟨b, htb⟩ := ‹Algebra.Transcendental R B›
  have ha : Function.Injective (algebraMap R A) := Algebra.injective_of_transcendental
  have hb : Function.Injective (algebraMap R B) := Algebra.injective_of_transcende

中文:
定理 _root_.Algebra.TensorProduct.not_isField_of_transcendental
  证明: fun H => by
  let := H.toField
  obtain ⟨a, hta⟩ := ‹Algebra.Transcendental R A›
  obtain ⟨b, htb⟩ := ‹Algebra.Transcendental R B›
  have ha : Function.Injective (algebraMap R A) := Algebra.injective_of_transcendental
  have hb : Function.Injective (algebraMap R B) := Algebra.injective_of_transcende

Depends on / 依赖: Algebra, Algebra.TensorProduct.includeL, Algebra.TensorProduct.includeLeft, Algebra.TensorProduct.includeRight, Algebra.Transcendental, Algebra.injective_of_transcendental, Function, Function.Injective, H.toField, Injective, TensorProduct, Transcendental, algebraMap, includeL, includeLeft, includeRight, injective_of_transcendental, otimes, toField
-/
theorem _root_.Algebra.TensorProduct.not_isField_of_transcendental
    (A : Type v) [CommRing A] (B : Type w) [CommRing B] [Algebra R A] [Algebra R B]
    [Module.Flat R A] [Module.Flat R B] [Algebra.Transcendental R A] [Algebra.Transcendental R B] :
    ¬IsField (A otimes[R] B) := fun H => by
  let := H.toField
  obtain ⟨a, hta⟩ := ‹Algebra.Transcendental R A›
  obtain ⟨b, htb⟩ := ‹Algebra.Transcendental R B›
  have ha : Function.Injective (algebraMap R A) := Algebra.injective_of_transcendental
  have hb : Function.Injective (algebraMap R B) := Algebra.injective_of_transcendental
  let fa : A ->ₐ[R] A otimes[R] B := Algebra.TensorProduct.includeLeft
  let fb : B ->ₐ[R] A otimes[R] B := Algebra.TensorProduct.includeRight
  have hfa : Function.Injective fa := Algebra.TensorProduct.includeLeft_injective hb
  have hfb : Function.Injective fb := Algebra.TensorProduct.includeRight_injective ha
  have := hfa.isDomain fa.toRingHom
  have := hfb.isDomain fb.toRingHom
  have := ha.isDomain _
  have : Module.Flat R (toSubmodule fa.range) :=
    .of_linearEquiv (AlgEquiv.ofInjective fa hfa).symm.toLinearEquiv
  have key1 : Module.rank R ↥(fa.range ⊓ fb.range) <= 1 :=
    (include_range R A B).rank_inf_le_one_of_flat_left
  let ga : R[X] ->ₐ[R] A := aeval a
  let gb : R[X] ->ₐ[R] B := aeval b
  let gab := fa.comp ga
  replace hta : Function.Injective ga := transcendental_iff_injective.1 hta
  replace htb : Function.Injective gb := transcendental_iff_injective.1 htb
  have htab : Function.Injective gab := hfa.comp hta
  algebraize_only [ga.toRingHom, gb.toRingHom]
  let f := Algebra.TensorProduct.mapOfCompatibleSMul R[X] R R A B
  have := Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain R[X] A B hta htb
  have hf : Function.Injective f := RingHom.injective _
  have key2 : gab.range <= fa.range ⊓ fb.range := by
    simp_rw [gab, ga, ← aeval_algHom]
    rw [Algebra.TensorProduct.includeLeft_apply]; rw [← Algebra.adjoin_singleton_eq_range_aeval]
    simp_rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff, Algebra.coe_inf, Set.mem_inter_iff,
      AlgHom.coe_range, Set.mem_range]
    refine ⟨⟨a, by simp [fa]⟩, ⟨b, hf ?_⟩⟩
    simp_rw [fb, Algebra.TensorProduct.includeRight_apply, f,
      Algebra.TensorProduct.mapOfCompatibleSMul_tmul]
    convert! ← (TensorProduct.smul_tmul (R := R[X]) (R' := R[X]) (M := A) (N := B) X 1 1).symm <;>
      (simp_rw [Algebra.smul_def, mul_one]; exact aeval_X _)
  have key3 := (Subalgebra.inclusion key2).comp (AlgEquiv.ofInjective gab htab).toAlgHom
.toLinearMap.lift_rank_le_of_injective
      ((Subalgebra.inclusion_injective key2).comp (AlgEquiv.injective _))
  have := lift_uzero.{u} _ ▸ (basisMonomials R).mk_eq_rank.symm
  simp only [this, mk_eq_aleph0, lift_aleph0, aleph0_le_lift] at key3
  exact (key3.trans key1).not_gt one_lt_aleph0

variable (R) in
/--
theorem `_root_.Algebra.TensorProduct.isAlgebraic_of_isField` / 定理 `_root_.Algebra.TensorProduct.isAlgebraic_of_isField`

English:
theorem _root_.Algebra.TensorProduct.isAlgebraic_of_isField
  proof: by
  by_contra! h
  simp_rw [← Algebra.transcendental_iff_not_isAlgebraic] at h
  obtain ⟨_, _⟩ := h
  exact Algebra.TensorProduct.not_isField_of_transcendental R A B H

中文:
定理 _root_.Algebra.TensorProduct.isAlgebraic_of_isField
  证明: by
  by_contra! h
  simp_rw [← Algebra.transcendental_iff_not_isAlgebraic] at h
  obtain ⟨_, _⟩ := h
  exact Algebra.TensorProduct.not_isField_of_transcendental R A B H

Depends on / 依赖: Algebra, Algebra.TensorProduct.not_isField_of_transcendental, Algebra.transcendental_iff_not_isAlgebraic, TensorProduct, not_isField_of_transcendental, simp_rw, transcendental_iff_not_isAlgebraic
-/
theorem _root_.Algebra.TensorProduct.isAlgebraic_of_isField
    (A : Type v) [CommRing A] (B : Type w) [CommRing B] [Algebra R A] [Algebra R B]
    [Module.Flat R A] [Module.Flat R B] (H : IsField (A otimes[R] B)) :
    Algebra.IsAlgebraic R A ∨ Algebra.IsAlgebraic R B := by
  by_contra! h
  simp_rw [← Algebra.transcendental_iff_not_isAlgebraic] at h
  obtain ⟨_, _⟩ := h
  exact Algebra.TensorProduct.not_isField_of_transcendental R A B H

variable (H : A.LinearDisjoint B)

include H in
/--
theorem `rank_inf_eq_one_of_flat_of_inj` / 定理 `rank_inf_eq_one_of_flat_of_inj`

English:
theorem rank_inf_eq_one_of_flat_of_inj
  statement: (hf : Module.Flat R A ∨ Module.Flat R B)
  proof: H.rank_inf_eq_one_of_commute_of_flat_of_inj hf (fun _ _ => mul_comm _ _) hinj

include H in

中文:
定理 rank_inf_eq_one_of_flat_of_inj
  结论: (hf : Module.Flat R A ∨ Module.Flat R B)
  证明: H.rank_inf_eq_one_of_commute_of_flat_of_inj hf (fun _ _ => mul_comm _ _) hinj

include H in

Depends on / 依赖: H.rank_inf_eq_one_of_commute_of_flat_of_inj, mul_comm, rank_inf_eq_one_of_commute_of_flat_of_inj
-/
theorem rank_inf_eq_one_of_flat_of_inj (hf : Module.Flat R A ∨ Module.Flat R B)
    (hinj : Function.Injective (algebraMap R S)) : Module.rank R ↥(A ⊓ B) = 1 :=
  H.rank_inf_eq_one_of_commute_of_flat_of_inj hf (fun _ _ => mul_comm _ _) hinj

include H in
/--
theorem `rank_inf_eq_one_of_flat_left_of_inj` / 定理 `rank_inf_eq_one_of_flat_left_of_inj`

English:
theorem rank_inf_eq_one_of_flat_left_of_inj
  statement: [Module.Flat R A]
  proof: H.rank_inf_eq_one_of_commute_of_flat_left_of_inj (fun _ _ => mul_comm _ _) hinj

include H in

中文:
定理 rank_inf_eq_one_of_flat_left_of_inj
  结论: [Module.Flat R A]
  证明: H.rank_inf_eq_one_of_commute_of_flat_left_of_inj (fun _ _ => mul_comm _ _) hinj

include H in

Depends on / 依赖: H.rank_inf_eq_one_of_commute_of_flat_left_of_inj, mul_comm, rank_inf_eq_one_of_commute_of_flat_left_of_inj
-/
theorem rank_inf_eq_one_of_flat_left_of_inj [Module.Flat R A]
    (hinj : Function.Injective (algebraMap R S)) : Module.rank R ↥(A ⊓ B) = 1 :=
  H.rank_inf_eq_one_of_commute_of_flat_left_of_inj (fun _ _ => mul_comm _ _) hinj

include H in
/--
theorem `rank_inf_eq_one_of_flat_right_of_inj` / 定理 `rank_inf_eq_one_of_flat_right_of_inj`

English:
theorem rank_inf_eq_one_of_flat_right_of_inj
  statement: [Module.Flat R B]
  proof: H.rank_inf_eq_one_of_commute_of_flat_right_of_inj (fun _ _ => mul_comm _ _) hinj

中文:
定理 rank_inf_eq_one_of_flat_right_of_inj
  结论: [Module.Flat R B]
  证明: H.rank_inf_eq_one_of_commute_of_flat_right_of_inj (fun _ _ => mul_comm _ _) hinj

Depends on / 依赖: H.rank_inf_eq_one_of_commute_of_flat_right_of_inj, mul_comm, rank_inf_eq_one_of_commute_of_flat_right_of_inj
-/
theorem rank_inf_eq_one_of_flat_right_of_inj [Module.Flat R B]
    (hinj : Function.Injective (algebraMap R S)) : Module.rank R ↥(A ⊓ B) = 1 :=
  H.rank_inf_eq_one_of_commute_of_flat_right_of_inj (fun _ _ => mul_comm _ _) hinj

/--
theorem `rank_eq_one_of_flat_of_self_of_inj` / 定理 `rank_eq_one_of_flat_of_self_of_inj`

English:
theorem rank_eq_one_of_flat_of_self_of_inj
  statement: (H : A.LinearDisjoint A) [Module.Flat R A]
  proof: H.rank_eq_one_of_commute_of_flat_of_self_of_inj (fun _ _ => mul_comm _ _) hinj

include H in

中文:
定理 rank_eq_one_of_flat_of_self_of_inj
  结论: (H : A.LinearDisjoint A) [Module.Flat R A]
  证明: H.rank_eq_one_of_commute_of_flat_of_self_of_inj (fun _ _ => mul_comm _ _) hinj

include H in

Depends on / 依赖: H.rank_eq_one_of_commute_of_flat_of_self_of_inj, mul_comm, rank_eq_one_of_commute_of_flat_of_self_of_inj
-/
theorem rank_eq_one_of_flat_of_self_of_inj (H : A.LinearDisjoint A) [Module.Flat R A]
    (hinj : Function.Injective (algebraMap R S)) : Module.rank R A = 1 :=
  H.rank_eq_one_of_commute_of_flat_of_self_of_inj (fun _ _ => mul_comm _ _) hinj

include H in
/--
theorem `rank_sup_of_free` / 定理 `rank_sup_of_free`

English:
theorem rank_sup_of_free
  given: [Module.Free R A] [Module.Free R B]
  proof: by
  nontriviality R
  rw [← rank_tensorProduct']; rw [H.mulMap.toLinearEquiv.rank_eq]

include H in

中文:
定理 rank_sup_of_free
  条件: [Module.Free R A] [Module.Free R B]
  证明: by
  nontriviality R
  rw [← rank_tensorProduct']; rw [H.mulMap.toLinearEquiv.rank_eq]

include H in

Depends on / 依赖: H.mulMap.toLinearEquiv.rank_eq, mulMap, nontriviality, rank_eq, rank_tensorProduct, toLinearEquiv
-/
theorem rank_sup_of_free [Module.Free R A] [Module.Free R B] :
    Module.rank R ↥(A ⊔ B) = Module.rank R A * Module.rank R B := by
  nontriviality R
  rw [← rank_tensorProduct']; rw [H.mulMap.toLinearEquiv.rank_eq]

include H in
/--
theorem `finrank_sup_of_free` / 定理 `finrank_sup_of_free`

English:
theorem finrank_sup_of_free
  given: [Module.Free R A] [Module.Free R B]
  proof: by
  simpa only [map_mul] using! congr(Cardinal.toNat $(H.rank_sup_of_free))

中文:
定理 finrank_sup_of_free
  条件: [Module.Free R A] [Module.Free R B]
  证明: by
  simpa only [map_mul] using! congr(Cardinal.toNat $(H.rank_sup_of_free))

Depends on / 依赖: Cardinal, Cardinal.toNat, H.rank_sup_of_free, map_mul, rank_sup_of_free
-/
theorem finrank_sup_of_free [Module.Free R A] [Module.Free R B] :
    Module.finrank R ↥(A ⊔ B) = Module.finrank R A * Module.finrank R B := by
  simpa only [map_mul] using! congr(Cardinal.toNat $(H.rank_sup_of_free))

/--
theorem `of_finrank_sup_of_free` / 定理 `of_finrank_sup_of_free`

English:
theorem of_finrank_sup_of_free
  statement: [Module.Free R A] [Module.Free R B]
  proof: by
  nontriviality R
  rw [← Module.finrank_tensorProduct] at H
  obtain ⟨j, hj⟩ := exists_linearIndependent_of_le_finrank H.ge
  rw [LinearIndependent] at hj
  let j' := Finsupp.linearCombination R j ∘ₗ
    (LinearEquiv.ofFinrankEq (A otimes[R] B) _ (by simp)).toLinearMap
  replace hj : Function.In

中文:
定理 of_finrank_sup_of_free
  结论: [Module.Free R A] [Module.Free R B]
  证明: by
  nontriviality R
  rw [← Module.finrank_tensorProduct] at H
  obtain ⟨j, hj⟩ := exists_linearIndependent_of_le_finrank H.ge
  rw [LinearIndependent] at hj
  let j' := Finsupp.linearCombination R j ∘ₗ
    (LinearEquiv.ofFinrankEq (A otimes[R] B) _ (by simp)).toLinearMap
  replace hj : Function.In

Depends on / 依赖: Finsupp, Finsupp.linearCombination, Function, Function.Injective, Function.Surjective, H.ge, Injective, LinearEquiv, LinearEquiv.ofFinrankEq, LinearIndependent, Module, Module.finrank_tensorProduct, Subalgebra, Subalgebra.finite_sup, Submodule, Submodule.linearDisjoint_iff, Subtype, Surjective, _surjective, exists_linearIndependent_of_le_finrank
-/
theorem of_finrank_sup_of_free [Module.Free R A] [Module.Free R B]
    [Module.Finite R A] [Module.Finite R B]
    (H : Module.finrank R ↥(A ⊔ B) = Module.finrank R A * Module.finrank R B) :
    A.LinearDisjoint B := by
  nontriviality R
  rw [← Module.finrank_tensorProduct] at H
  obtain ⟨j, hj⟩ := exists_linearIndependent_of_le_finrank H.ge
  rw [LinearIndependent] at hj
  let j' := Finsupp.linearCombination R j ∘ₗ
    (LinearEquiv.ofFinrankEq (A otimes[R] B) _ (by simp)).toLinearMap
  replace hj : Function.Injective j' := by simpa [j']
  have hf : Function.Surjective (mulMap' A B).toLinearMap := mulMap'_surjective A B
  have := Subalgebra.finite_sup A B
  rw [linearDisjoint_iff]; rw [Submodule.linearDisjoint_iff]
  exact Subtype.val_injective.comp (OrzechProperty.injective_of_surjective_of_injective j' _ hj hf)

include H in
/--
theorem `adjoin_rank_eq_rank_left` / 定理 `adjoin_rank_eq_rank_left`

English:
theorem adjoin_rank_eq_rank_left
  statement: [Module.Free R A] [Module.Flat R B]
  proof: by
  rw [← rank_toSubmodule]; rw [Module.Free.rank_eq_card_chooseBasisIndex R A]; rw [A.adjoin_eq_span_basis B (Module.Free.chooseBasis R A)]
  change Module.rank B (Submodule.span B (Set.range (A.val ∘ Module.Free.chooseBasis R A))) = _
  have := H.linearIndependent_left_of_flat (Module.Free.choose

中文:
定理 adjoin_rank_eq_rank_left
  结论: [Module.Free R A] [Module.Flat R B]
  证明: by
  rw [← rank_toSubmodule]; rw [Module.Free.rank_eq_card_chooseBasisIndex R A]; rw [A.adjoin_eq_span_basis B (Module.Free.chooseBasis R A)]
  change Module.rank B (Submodule.span B (Set.range (A.val ∘ Module.Free.chooseBasis R A))) = _
  have := H.linearIndependent_left_of_flat (Module.Free.choose

Depends on / 依赖: A.adjoin_eq_span_basis, A.val, Cardinal, Cardinal.mk_range_eq, H.linearIndependent_left_of_flat, Module, Module.Free.chooseBasis, Module.Free.rank_eq_card_chooseBasisIndex, Module.rank, Set.range, Submodule, Submodule.span, adjoin_eq_span_basis, chooseBasis, injective, linearIndependent, linearIndependent_left_of_flat, mk_range_eq, rank_eq_card_chooseBasisIndex, rank_span
-/
theorem adjoin_rank_eq_rank_left [Module.Free R A] [Module.Flat R B]
    [Nontrivial R] [Nontrivial S] :
    Module.rank B (Algebra.adjoin B (A : Set S)) = Module.rank R A := by
  rw [← rank_toSubmodule]; rw [Module.Free.rank_eq_card_chooseBasisIndex R A]; rw [A.adjoin_eq_span_basis B (Module.Free.chooseBasis R A)]
  change Module.rank B (Submodule.span B (Set.range (A.val ∘ Module.Free.chooseBasis R A))) = _
  have := H.linearIndependent_left_of_flat (Module.Free.chooseBasis R A).linearIndependent
  rw [rank_span this]; rw [Cardinal.mk_range_eq _ this.injective]

include H in
/--
theorem `adjoin_rank_eq_rank_right` / 定理 `adjoin_rank_eq_rank_right`

English:
theorem adjoin_rank_eq_rank_right
  statement: [Module.Free R B] [Module.Flat R A]
  proof: H.symm.adjoin_rank_eq_rank_left

中文:
定理 adjoin_rank_eq_rank_right
  结论: [Module.Free R B] [Module.Flat R A]
  证明: H.symm.adjoin_rank_eq_rank_left

Depends on / 依赖: H.symm.adjoin_rank_eq_rank_left, adjoin_rank_eq_rank_left
-/
theorem adjoin_rank_eq_rank_right [Module.Free R B] [Module.Flat R A]
    [Nontrivial R] [Nontrivial S] :
    Module.rank A (Algebra.adjoin A (B : Set S)) = Module.rank R B :=
  H.symm.adjoin_rank_eq_rank_left

/--
theorem `of_finrank_coprime_of_free` / 定理 `of_finrank_coprime_of_free`

English:
theorem of_finrank_coprime_of_free
  statement: [Module.Free R A] [Module.Free R B]
  proof: by
  nontriviality R
  by_cases h1 : Module.finrank R A = 0
  · rw [h1, Nat.coprime_zero_left] at H
    rw [eq_bot_of_finrank_one H]
    exact bot_right _
  by_cases h2 : Module.finrank R B = 0
  · rw [h2, Nat.coprime_zero_right] at H
    rw [eq_bot_of_finrank_one H]
    exact bot_left _
  have := M

中文:
定理 of_finrank_coprime_of_free
  结论: [Module.Free R A] [Module.Free R B]
  证明: by
  nontriviality R
  by_cases h1 : Module.finrank R A = 0
  · rw [h1, Nat.coprime_zero_left] at H
    rw [eq_bot_of_finrank_one H]
    exact bot_right _
  by_cases h2 : Module.finrank R B = 0
  · rw [h2, Nat.coprime_zero_right] at H
    rw [eq_bot_of_finrank_one H]
    exact bot_left _
  have := M

Depends on / 依赖: LinearMap, LinearMap.finrank_le_finrank_of_in, Module, Module.finite_of_finrank_pos, Module.finrank, Nat.coprime_zero_left, Nat.coprime_zero_right, Nat.pos_of_ne_zero, bot_left, bot_right, coprime_zero_left, coprime_zero_right, eq_bot_of_finrank_one, finite_of_finrank_pos, finite_sup, finrank, finrank_le_finrank_of_in, nontriviality, pos_of_ne_zero
-/
theorem of_finrank_coprime_of_free [Module.Free R A] [Module.Free R B]
    [Module.Free A (Algebra.adjoin A (B : Set S))] [Module.Free B (Algebra.adjoin B (A : Set S))]
    (H : (Module.finrank R A).Coprime (Module.finrank R B)) : A.LinearDisjoint B := by
  nontriviality R
  by_cases h1 : Module.finrank R A = 0
  · rw [h1, Nat.coprime_zero_left] at H
    rw [eq_bot_of_finrank_one H]
    exact bot_right _
  by_cases h2 : Module.finrank R B = 0
  · rw [h2, Nat.coprime_zero_right] at H
    rw [eq_bot_of_finrank_one H]
    exact bot_left _
  have := Module.finite_of_finrank_pos (Nat.pos_of_ne_zero h1)
  have := Module.finite_of_finrank_pos (Nat.pos_of_ne_zero h2)
  have := finite_sup A B
  have : Module.finrank R A <= Module.finrank R ↥(A ⊔ B) :=
LinearMap.finrank_le_finrank_of_injective
      Submodule.inclusion_injective (show toSubmodule A <= toSubmodule (A ⊔ B) by simp)
exact of_finrank_sup_of_free (finrank_sup_le_of_free A B).antisymm
Nat.le_of_dvd (lt_of_lt_of_le (Nat.pos_of_ne_zero h1) this) H.mul_dvd_of_dvd_of_dvd
      (finrank_left_dvd_finrank_sup_of_free A B) (finrank_right_dvd_finrank_sup_of_free A B)

variable (A B)

/--
theorem `of_linearDisjoint_finite_left` / 定理 `of_linearDisjoint_finite_left`

English:
theorem of_linearDisjoint_finite_left
  statement: [Algebra.IsIntegral R A]
  proof: by
  rw [linearDisjoint_iff]; rw [Submodule.linearDisjoint_iff]
  intro x y hxy
  obtain ⟨M', hM, hf, h⟩ :=
    TensorProduct.exists_finite_submodule_left_of_setFinite' {x, y} (Set.toFinite _)
  obtain ⟨s, hs⟩ : M'.FG := .of_finite
  have hs' : (s : Set S) subseteq A := by rwa [← hs, Submodule.span_

中文:
定理 of_linearDisjoint_finite_left
  结论: [Algebra.Is整数egral R A]
  证明: by
  rw [linearDisjoint_iff]; rw [Submodule.linearDisjoint_iff]
  intro x y hxy
  obtain ⟨M', hM, hf, h⟩ :=
    TensorProduct.exists_finite_submodule_left_of_setFinite' {x, y} (Set.toFinite _)
  obtain ⟨s, hs⟩ : M'.FG := .of_finite
  have hs' : (s : Set S) subseteq A := by rwa [← hs, Submodule.span_

Depends on / 依赖: A.val, Algebra, Algebra.IsIntegral, Algebra.adjoin, IsIntegral, Set.toFinite, Submodule, Submodule.FG, Submodule.linearDisjoint_iff, Submodule.span_le, Subtype, Subtype.val_injective, TensorProduct, TensorProduct.exists_finite_submodule_left_of_setFinite, adjoin, exists_finite_submodule_left_of_setFinite, fg_adjoin_of_finite, finite_toSet, isIntegral_algHom_iff, linearDisjoint_iff
-/
theorem of_linearDisjoint_finite_left [Algebra.IsIntegral R A]
    (H : forall A' : Subalgebra R S, A' <= A -> [Module.Finite R A'] -> A'.LinearDisjoint B) :
    A.LinearDisjoint B := by
  rw [linearDisjoint_iff]; rw [Submodule.linearDisjoint_iff]
  intro x y hxy
  obtain ⟨M', hM, hf, h⟩ :=
    TensorProduct.exists_finite_submodule_left_of_setFinite' {x, y} (Set.toFinite _)
  obtain ⟨s, hs⟩ : M'.FG := .of_finite
  have hs' : (s : Set S) subseteq A := by rwa [← hs, Submodule.span_le] at hM
  let A' := Algebra.adjoin R (s : Set S)
  have hf' : Submodule.FG (toSubmodule A') := fg_adjoin_of_finite s.finite_toSet fun x hx =>
    (isIntegral_algHom_iff A.val Subtype.val_injective).2
      (Algebra.IsIntegral.isIntegral (R := R) (A := A) ⟨x, hs' hx⟩)
  replace hf' : Module.Finite R A' := .of_fg hf'
  have hA : toSubmodule A' <= toSubmodule A := Algebra.adjoin_le_iff.2 hs'
  replace h : {x, y} subseteq (LinearMap.range (LinearMap.rTensor (toSubmodule B)
      (Submodule.inclusion hA)) : Set _) := fun _ hx => by
    have : Submodule.inclusion hM = Submodule.inclusion hA ∘ₗ Submodule.inclusion
      (show M' <= toSubmodule A' by
        rw [← hs]; rw [Submodule.span_le]; exact Algebra.adjoin_le_iff.1 (le_refl _)) := rfl
    rw [this]; rw [LinearMap.rTensor_comp] at h
    exact LinearMap.range_comp_le_range _ _ (h hx)
  obtain ⟨x', hx'⟩ := h (show x in {x, y} by simp)
  obtain ⟨y', hy'⟩ := h (show y in {x, y} by simp)
  rw [← hx']; rw [← hy']; congr
  exact (H A' hA).injective (by simp [← Submodule.mulMap_comp_rTensor _ hA, hx', hy', hxy])

/--
theorem `of_linearDisjoint_finite_right` / 定理 `of_linearDisjoint_finite_right`

English:
theorem of_linearDisjoint_finite_right
  statement: [Algebra.IsIntegral R B]
  proof: (of_linearDisjoint_finite_left B A fun B' hB' _ => (H B' hB').symm).symm

中文:
定理 of_linearDisjoint_finite_right
  结论: [Algebra.Is整数egral R B]
  证明: (of_linearDisjoint_finite_left B A fun B' hB' _ => (H B' hB').symm).symm

Depends on / 依赖: of_linearDisjoint_finite_left
-/
theorem of_linearDisjoint_finite_right [Algebra.IsIntegral R B]
    (H : forall B' : Subalgebra R S, B' <= B -> [Module.Finite R B'] -> A.LinearDisjoint B') :
    A.LinearDisjoint B :=
  (of_linearDisjoint_finite_left B A fun B' hB' _ => (H B' hB').symm).symm

variable {A B}

/--
theorem `of_linearDisjoint_finite` / 定理 `of_linearDisjoint_finite`

English:
theorem of_linearDisjoint_finite
  proof: of_linearDisjoint_finite_left A B fun _ hA' _ =>
    of_linearDisjoint_finite_right _ B fun _ hB' _ => H _ _ hA' hB'

中文:
定理 of_linearDisjoint_finite
  证明: of_linearDisjoint_finite_left A B fun _ hA' _ =>
    of_linearDisjoint_finite_right _ B fun _ hB' _ => H _ _ hA' hB'

Depends on / 依赖: of_linearDisjoint_finite_left, of_linearDisjoint_finite_right
-/
theorem of_linearDisjoint_finite
    [Algebra.IsIntegral R A] [Algebra.IsIntegral R B]
    (H : forall (A' B' : Subalgebra R S), A' <= A -> B' <= B ->
      [Module.Finite R A'] -> [Module.Finite R B'] -> A'.LinearDisjoint B') :
    A.LinearDisjoint B :=
  of_linearDisjoint_finite_left A B fun _ hA' _ =>
    of_linearDisjoint_finite_right _ B fun _ hB' _ => H _ _ hA' hB'

end LinearDisjoint

end CommRing

section FieldAndRing

namespace LinearDisjoint

variable [Field R] [Ring S] [Algebra R S]

variable {A B : Subalgebra R S}

/--
theorem `inf_eq_bot_of_commute` / 定理 `inf_eq_bot_of_commute`

English:
theorem inf_eq_bot_of_commute
  statement: (H : A.LinearDisjoint B)
  proof: eq_bot_of_rank_le_one (Submodule.LinearDisjoint.rank_inf_le_one_of_commute_of_flat_left H hc)

中文:
定理 inf_eq_bot_of_commute
  结论: (H : A.LinearDisjoint B)
  证明: eq_bot_of_rank_le_one (Submodule.LinearDisjoint.rank_inf_le_one_of_commute_of_flat_left H hc)

Depends on / 依赖: LinearDisjoint, Submodule, Submodule.LinearDisjoint.rank_inf_le_one_of_commute_of_flat_left, eq_bot_of_rank_le_one, rank_inf_le_one_of_commute_of_flat_left
-/
theorem inf_eq_bot_of_commute (H : A.LinearDisjoint B)
    (hc : forall (a b : ↥(A ⊓ B)), Commute a.1 b.1) : A ⊓ B = ⊥ :=
  eq_bot_of_rank_le_one (Submodule.LinearDisjoint.rank_inf_le_one_of_commute_of_flat_left H hc)

/--
theorem `eq_bot_of_commute_of_self` / 定理 `eq_bot_of_commute_of_self`

English:
theorem eq_bot_of_commute_of_self
  statement: (H : A.LinearDisjoint A)
  proof: by
  rw [← inf_of_le_left (le_refl A)] at hc ⊢
  exact H.inf_eq_bot_of_commute hc

中文:
定理 eq_bot_of_commute_of_self
  结论: (H : A.LinearDisjoint A)
  证明: by
  rw [← inf_of_le_left (le_refl A)] at hc ⊢
  exact H.inf_eq_bot_of_commute hc

Depends on / 依赖: H.inf_eq_bot_of_commute, inf_eq_bot_of_commute, inf_of_le_left, le_refl
-/
theorem eq_bot_of_commute_of_self (H : A.LinearDisjoint A)
    (hc : forall (a b : A), Commute a.1 b.1) : A = ⊥ := by
  rw [← inf_of_le_left (le_refl A)] at hc ⊢
  exact H.inf_eq_bot_of_commute hc

end LinearDisjoint

end FieldAndRing

section FieldAndCommRing

namespace LinearDisjoint

variable [Field R] [CommRing S] [Algebra R S]

variable {A B : Subalgebra R S}

/--
theorem `inf_eq_bot` / 定理 `inf_eq_bot`

English:
theorem inf_eq_bot
  given: (H : A.LinearDisjoint B)
  statement: A ⊓ B = ⊥
  proof: H.inf_eq_bot_of_commute fun _ _ => mul_comm _ _

中文:
定理 inf_eq_bot
  条件: (H : A.LinearDisjoint B)
  结论: A ⊓ B = ⊥
  证明: H.inf_eq_bot_of_commute fun _ _ => mul_comm _ _

Depends on / 依赖: H.inf_eq_bot_of_commute, inf_eq_bot_of_commute, mul_comm
-/
theorem inf_eq_bot (H : A.LinearDisjoint B) : A ⊓ B = ⊥ :=
  H.inf_eq_bot_of_commute fun _ _ => mul_comm _ _

/--
theorem `eq_bot_of_self` / 定理 `eq_bot_of_self`

English:
theorem eq_bot_of_self
  given: (H : A.LinearDisjoint A)
  statement: A = ⊥
  proof: H.eq_bot_of_commute_of_self fun _ _ => mul_comm _ _

中文:
定理 eq_bot_of_self
  条件: (H : A.LinearDisjoint A)
  结论: A = ⊥
  证明: H.eq_bot_of_commute_of_self fun _ _ => mul_comm _ _

Depends on / 依赖: H.eq_bot_of_commute_of_self, eq_bot_of_commute_of_self, mul_comm
-/
theorem eq_bot_of_self (H : A.LinearDisjoint A) : A = ⊥ :=
  H.eq_bot_of_commute_of_self fun _ _ => mul_comm _ _

end LinearDisjoint

end FieldAndCommRing

end Subalgebra
