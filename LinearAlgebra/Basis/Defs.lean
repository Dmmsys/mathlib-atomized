/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Alexander Bentkamp
-/
module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Bases

This file defines bases in a module or vector space.

It is inspired by Isabelle/HOL's linear algebra, and hence indirectly by HOL Light.

## Main definitions

All definitions are given for families of vectors, i.e. `v : ι → M` where `M` is the module or
vector space and `ι : Type*` is an arbitrary indexing type.

* `Basis ι R M` is the type of `ι`-indexed `R`-bases for a module `M`,
  represented by a linear equiv `M ≃ₗ[R] ι →₀ R`.
* the basis vectors of a basis `b : Basis ι R M` are available as `b i`, where `i : ι`

* `Basis.repr` is the isomorphism sending `x : M` to its coordinates `Basis.repr x : ι →₀ R`.
  The converse, turning this isomorphism into a basis, is called `Basis.ofRepr`.
* If `ι` is finite, there is a variant of `repr` called `Basis.equivFun b : M ≃ₗ[R] ι → R`
  (saving you from having to work with `Finsupp`). The converse, turning this isomorphism into
  a basis, is called `Basis.ofEquivFun`.

* `Basis.reindex` uses an equiv to map a basis to a different indexing set.

* `Basis.map` uses a linear equiv to map a basis to a different module.

* `Basis.constr`: given `b : Basis ι R M` and `f : ι → M`, construct a linear map `g` so that
  `g (b i) = f i`.

* `Basis.coord`: `b.coord i x` is the `i`-th coordinate of a vector `x` with respect to the basis
  `b`.

## Main results

* `Basis.ext` states that two linear maps are equal if they coincide on a basis.
  Similar results are available for linear equivs (if they coincide on the basis vectors),
  elements (if their coordinates coincide) and the functions `b.repr` and `⇑b`.

## Implementation notes

We use families instead of sets because it allows us to say that two identical vectors are linearly
dependent. For bases, this is useful as well because we can easily derive ordered bases by using an
ordered index type `ι`.

## Tags

basis, bases

-/

@[expose] public section

assert_not_exists LinearMap.pi LinearIndependent Cardinal
-- TODO: assert_not_exists Submodule
-- (should be possible after splitting `Mathlib/LinearAlgebra/Finsupp/LinearCombination.lean`)

noncomputable section

universe u

open Function Set Submodule Finsupp

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {K : Type*}
variable {M : Type*} {M' M'' : Type*} {V : Type u} {V' : Type*}

namespace Module

variable [Semiring R]
variable [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']

variable (ι R M) in
/-- A `Basis ι R M` for a module `M` is the type of `ι`-indexed `R`-bases of `M`.

The basis vectors are available as `DFunLike.coe (b : Basis ι R M) : ι → M`.
To turn a linear independent family of vectors spanning `M` into a basis, use `Basis.mk`.
They are internally represented as linear equivs `M ≃ₗ[R] (ι →₀ R)`,
available as `Basis.repr`.
-/
@[wikidata Q189569]
/--
Definition of `Basis` / `Basis` 的定义

English:
structure Basis
  parameters: where
  axioms and operations (1):
    - ofRepr : : repr : M ≃ₗ[R] ι ->₀ R

中文:
结构 基
  参数: where
  公理与运算 (1 个):
    - ofRepr : : repr : M ≃ₗ[R] ι ->₀ R
-/
structure Basis where
  /-- `Basis.ofRepr` constructs a basis given an assignment of coordinates to each vector. -/
  ofRepr ::
    /-- `repr` is the linear equivalence sending a vector `x` to its coordinates:
    the `c`s such that `x = ∑ i, c i`. -/
    repr : M ≃ₗ[R] ι ->₀ R

namespace Basis

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Basis ι R (ι ->₀ R))
  body: ⟨.ofRepr (LinearEquiv.refl _ _)⟩

中文:
实例 :
  签名: 可居 (基 ι R (ι ->₀ R))
  定义体: ⟨.ofRepr (LinearEquiv.refl _ _)⟩

Depends on / 依赖: LinearEquiv, LinearEquiv.refl, ofRepr
-/
instance : Inhabited (Basis ι R (ι ->₀ R)) :=
  ⟨.ofRepr (LinearEquiv.refl _ _)⟩

variable (b b₁ : Basis ι R M) (i : ι) (c : R) (x : M)

section repr

/--
theorem `repr_injective` / 定理 `repr_injective`

English:
theorem repr_injective
  statement: Injective (repr : Basis ι R M -> M ≃ₗ[R] ι ->₀ R)
  proof: fun f g h => by
  cases f; cases g; congr

中文:
定理 repr_injective
  结论: 单射 (repr : 基 ι R M -> M ≃ₗ[R] ι ->₀ R)
  证明: fun f g h => by
  cases f; cases g; congr
-/
theorem repr_injective : Injective (repr : Basis ι R M -> M ≃ₗ[R] ι ->₀ R) := fun f g h => by
  cases f; cases g; congr

/--
Instance `instFunLike` / 实例 `instFunLike`

English:
instance instFunLike
  signature: : FunLike (Basis ι R M) ι M where
  body: b.repr.symm (Finsupp.single i 1)
coe_injective f g h := repr_injective LinearEquiv.symm_bijective.injective
LinearEquiv.toLinearMap_injective by ext; exact congr_fun h _

@[simp]

中文:
实例 instFunLike
  签名: : 函数状 (基 ι R M) ι M where
  定义体: b.repr.symm (Finsupp.single i 1)
coe_injective f g h := repr_injective LinearEquiv.symm_bijective.injective
LinearEquiv.toLinearMap_injective by ext; exact congr_fun h _

@[simp]

Depends on / 依赖: Finsupp, Finsupp.single, b.repr.symm, single
-/
instance instFunLike : FunLike (Basis ι R M) ι M where
  coe b i := b.repr.symm (Finsupp.single i 1)
coe_injective f g h := repr_injective LinearEquiv.symm_bijective.injective
LinearEquiv.toLinearMap_injective by ext; exact congr_fun h _

@[simp]
/--
theorem `coe_ofRepr` / 定理 `coe_ofRepr`

English:
theorem coe_ofRepr
  given: (e : M ≃ₗ[R] ι ->₀ R)
  statement: ⇑(ofRepr e) = fun i => e.symm (Finsupp.single i 1)
  proof: rfl

中文:
定理 coe_ofRepr
  条件: (e : M ≃ₗ[R] ι ->₀ R)
  结论: ⇑(ofRepr e) = fun i => e.symm (有限支撑.single i 1)
  证明: rfl
-/
theorem coe_ofRepr (e : M ≃ₗ[R] ι ->₀ R) : ⇑(ofRepr e) = fun i => e.symm (Finsupp.single i 1) :=
  rfl

/--
theorem `injective` / 定理 `injective`

English:
theorem injective
  given: [Nontrivial R]
  statement: Injective b
  proof: b.repr.symm.injective.comp fun _ _ => (Finsupp.single_left_inj (one_ne_zero : (1 : R) != 0)).mp

中文:
定理 injective
  条件: [非平凡 R]
  结论: 单射 b
  证明: b.repr.symm.injective.comp fun _ _ => (Finsupp.single_left_inj (one_ne_zero : (1 : R) != 0)).mp
-/
protected theorem injective [Nontrivial R] : Injective b :=
  b.repr.symm.injective.comp fun _ _ => (Finsupp.single_left_inj (one_ne_zero : (1 : R) != 0)).mp

/--
theorem `repr_symm_single_one` / 定理 `repr_symm_single_one`

English:
theorem repr_symm_single_one
  statement: b.repr.symm (Finsupp.single i 1) = b i
  proof: rfl

中文:
定理 repr_symm_single_one
  结论: b.repr.symm (有限支撑.single i 1) = b i
  证明: rfl
-/
theorem repr_symm_single_one : b.repr.symm (Finsupp.single i 1) = b i :=
  rfl

/--
theorem `repr_symm_single` / 定理 `repr_symm_single`

English:
theorem repr_symm_single
  statement: b.repr.symm (Finsupp.single i c) = c • b i
  proof: calc
    b.repr.symm (Finsupp.single i c) = b.repr.symm (c • Finsupp.single i (1 : R)) := by
      { rw [Finsupp.smul_single', mul_one] }
    _ = c • b i := by rw [map_smul, repr_symm_single_one]

@[simp]

中文:
定理 repr_symm_single
  结论: b.repr.symm (有限支撑.single i c) = c • b i
  证明: calc
    b.repr.symm (Finsupp.single i c) = b.repr.symm (c • Finsupp.single i (1 : R)) := by
      { rw [Finsupp.smul_single', mul_one] }
    _ = c • b i := by rw [map_smul, repr_symm_single_one]

@[simp]

Depends on / 依赖: Finsupp, Finsupp.single, Finsupp.smul_single, b.repr.symm, map_smul, mul_one, repr_symm_single_one, single, smul_single
-/
theorem repr_symm_single : b.repr.symm (Finsupp.single i c) = c • b i :=
  calc
    b.repr.symm (Finsupp.single i c) = b.repr.symm (c • Finsupp.single i (1 : R)) := by
      { rw [Finsupp.smul_single', mul_one] }
    _ = c • b i := by rw [map_smul, repr_symm_single_one]

@[simp]
/--
theorem `repr_self` / 定理 `repr_self`

English:
theorem repr_self
  statement: b.repr (b i) = Finsupp.single i 1
  proof: LinearEquiv.apply_symm_apply _ _

中文:
定理 repr_self
  结论: b.repr (b i) = 有限支撑.single i 1
  证明: LinearEquiv.apply_symm_apply _ _

Depends on / 依赖: LinearEquiv, LinearEquiv.apply_symm_apply, apply_symm_apply
-/
theorem repr_self : b.repr (b i) = Finsupp.single i 1 :=
  LinearEquiv.apply_symm_apply _ _

/--
theorem `repr_self_apply` / 定理 `repr_self_apply`

English:
theorem repr_self_apply
  given: (j) [Decidable (i = j)]
  statement: b.repr (b i) j = if i = j then 1 else 0
  proof: by
  rw [repr_self]; rw [Finsupp.single_apply]

@[simp]

中文:
定理 repr_self_apply
  条件: (j) [可判定 (i = j)]
  结论: b.repr (b i) j = if i = j then 1 else 0
  证明: by
  rw [repr_self]; rw [Finsupp.single_apply]

@[simp]

Depends on / 依赖: Finsupp, Finsupp.single_apply, repr_self, single_apply
-/
theorem repr_self_apply (j) [Decidable (i = j)] : b.repr (b i) j = if i = j then 1 else 0 := by
  rw [repr_self]; rw [Finsupp.single_apply]

@[simp]
/--
theorem `repr_symm_apply` / 定理 `repr_symm_apply`

English:
theorem repr_symm_apply
  given: (v)
  statement: b.repr.symm v = Finsupp.linearCombination R b v
  proof: calc
    b.repr.symm v = b.repr.symm (v.sum Finsupp.single) := by simp
    _ = v.sum fun i vi => b.repr.symm (Finsupp.single i vi) := map_finsuppSum ..
    _ = Finsupp.linearCombination R b v := by simp only [repr_symm_single,
                                                         Finsupp.linearCombination_apply]

@[simp]

中文:
定理 repr_symm_apply
  条件: (v)
  结论: b.repr.symm v = 有限支撑.linearCombination R b v
  证明: calc
    b.repr.symm v = b.repr.symm (v.sum Finsupp.single) := by simp
    _ = v.sum fun i vi => b.repr.symm (Finsupp.single i vi) := map_finsuppSum ..
    _ = Finsupp.linearCombination R b v := by simp only [repr_symm_single,
                                                         Finsupp.linearCombination_apply]

@[simp]

Depends on / 依赖: Finsupp, Finsupp.linearCombination, Finsupp.linearCombination_apply, Finsupp.single, b.repr.symm, linearCombination, linearCombination_apply, map_finsuppSum, repr_symm_single, single, v.sum
-/
theorem repr_symm_apply (v) : b.repr.symm v = Finsupp.linearCombination R b v :=
  calc
    b.repr.symm v = b.repr.symm (v.sum Finsupp.single) := by simp
    _ = v.sum fun i vi => b.repr.symm (Finsupp.single i vi) := map_finsuppSum ..
    _ = Finsupp.linearCombination R b v := by simp only [repr_symm_single,
                                                         Finsupp.linearCombination_apply]

@[simp]
/--
theorem `coe_repr_symm` / 定理 `coe_repr_symm`

English:
theorem coe_repr_symm
  statement: ↑b.repr.symm = Finsupp.linearCombination R b
  proof: LinearMap.ext fun v => b.repr_symm_apply v

@[simp]

中文:
定理 coe_repr_symm
  结论: ↑b.repr.symm = 有限支撑.linearCombination R b
  证明: LinearMap.ext fun v => b.repr_symm_apply v

@[simp]

Depends on / 依赖: LinearMap, LinearMap.ext, b.repr_symm_apply, repr_symm_apply
-/
theorem coe_repr_symm : ↑b.repr.symm = Finsupp.linearCombination R b :=
  LinearMap.ext fun v => b.repr_symm_apply v

@[simp]
/--
theorem `repr_linearCombination` / 定理 `repr_linearCombination`

English:
theorem repr_linearCombination
  given: (v)
  statement: b.repr (Finsupp.linearCombination _ b v) = v
  proof: by
  rw [← b.coe_repr_symm]
  exact b.repr.apply_symm_apply v

@[simp]

中文:
定理 repr_linearCombination
  条件: (v)
  结论: b.repr (有限支撑.linearCombination _ b v) = v
  证明: by
  rw [← b.coe_repr_symm]
  exact b.repr.apply_symm_apply v

@[simp]

Depends on / 依赖: apply_symm_apply, b.coe_repr_symm, b.repr.apply_symm_apply, coe_repr_symm
-/
theorem repr_linearCombination (v) : b.repr (Finsupp.linearCombination _ b v) = v := by
  rw [← b.coe_repr_symm]
  exact b.repr.apply_symm_apply v

@[simp]
/--
theorem `linearCombination_repr` / 定理 `linearCombination_repr`

English:
theorem linearCombination_repr
  statement: Finsupp.linearCombination _ b (b.repr x) = x
  proof: by
  rw [← b.coe_repr_symm]
  exact b.repr.symm_apply_apply x

中文:
定理 linearCombination_repr
  结论: 有限支撑.linearCombination _ b (b.repr x) = x
  证明: by
  rw [← b.coe_repr_symm]
  exact b.repr.symm_apply_apply x

Depends on / 依赖: b.coe_repr_symm, b.repr.symm_apply_apply, coe_repr_symm, symm_apply_apply
-/
theorem linearCombination_repr : Finsupp.linearCombination _ b (b.repr x) = x := by
  rw [← b.coe_repr_symm]
  exact b.repr.symm_apply_apply x

end repr

section Map

variable (f : M ≃ₗ[R] M')

/-- Apply the linear equivalence `f` to the basis vectors. -/
@[simps]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: : Basis ι R M'
  body: ofRepr (f.symm.trans b.repr)

@[simp]

中文:
定义 map
  签名: : 基 ι R M'
  定义体: ofRepr (f.symm.trans b.repr)

@[simp]
-/
protected def map : Basis ι R M' :=
  ofRepr (f.symm.trans b.repr)

@[simp]
/--
theorem `map_apply` / 定理 `map_apply`

English:
theorem map_apply
  given: (i)
  statement: b.map f i = f (b i)
  proof: rfl

中文:
定理 map_apply
  条件: (i)
  结论: b.map f i = f (b i)
  证明: rfl
-/
theorem map_apply (i) : b.map f i = f (b i) :=
  rfl

/--
theorem `coe_map` / 定理 `coe_map`

English:
theorem coe_map
  statement: (b.map f : ι -> M') = f ∘ b
  proof: rfl

中文:
定理 coe_map
  结论: (b.map f : ι -> M') = f ∘ b
  证明: rfl
-/
theorem coe_map : (b.map f : ι -> M') = f ∘ b :=
  rfl

end Map

section Reindex

variable (b' : Basis ι' R M')
variable (e : ι ≃ ι')

/--
Definition of `reindex` / `reindex` 的定义

English:
definition reindex
  signature: : Basis ι' R M
  body: .ofRepr (b.repr.trans (Finsupp.domLCongr e))

中文:
定义 reindex
  签名: : 基 ι' R M
  定义体: .ofRepr (b.repr.trans (Finsupp.domLCongr e))

Depends on / 依赖: Finsupp, Finsupp.domLCongr, b.repr.trans, domLCongr, ofRepr
-/
def reindex : Basis ι' R M :=
  .ofRepr (b.repr.trans (Finsupp.domLCongr e))

/--
theorem `reindex_apply` / 定理 `reindex_apply`

English:
theorem reindex_apply
  given: (i' : ι')
  statement: b.reindex e i' = b (e.symm i')
  proof: show (b.repr.trans (Finsupp.domLCongr e)).symm (Finsupp.single i' 1) =
    b.repr.symm (Finsupp.single (e.symm i') 1)
  by rw [LinearEquiv.symm_trans_apply, Finsupp.domLCongr_symm, Finsupp.domLCongr_single]

@[simp]

中文:
定理 reindex_apply
  条件: (i' : ι')
  结论: b.reindex e i' = b (e.symm i')
  证明: show (b.repr.trans (Finsupp.domLCongr e)).symm (Finsupp.single i' 1) =
    b.repr.symm (Finsupp.single (e.symm i') 1)
  by rw [LinearEquiv.symm_trans_apply, Finsupp.domLCongr_symm, Finsupp.domLCongr_single]

@[simp]

Depends on / 依赖: Finsupp, Finsupp.domLCongr, Finsupp.domLCongr_single, Finsupp.domLCongr_symm, Finsupp.single, LinearEquiv, LinearEquiv.symm_trans_apply, b.repr.symm, b.repr.trans, domLCongr, domLCongr_single, domLCongr_symm, e.symm, single, symm_trans_apply
-/
theorem reindex_apply (i' : ι') : b.reindex e i' = b (e.symm i') :=
  show (b.repr.trans (Finsupp.domLCongr e)).symm (Finsupp.single i' 1) =
    b.repr.symm (Finsupp.single (e.symm i') 1)
  by rw [LinearEquiv.symm_trans_apply, Finsupp.domLCongr_symm, Finsupp.domLCongr_single]

@[simp]
/--
theorem `coe_reindex` / 定理 `coe_reindex`

English:
theorem coe_reindex
  statement: (b.reindex e : ι' -> M) = b ∘ e.symm
  proof: funext (b.reindex_apply e)

中文:
定理 coe_reindex
  结论: (b.reindex e : ι' -> M) = b ∘ e.symm
  证明: funext (b.reindex_apply e)

Depends on / 依赖: b.reindex_apply, reindex_apply
-/
theorem coe_reindex : (b.reindex e : ι' -> M) = b ∘ e.symm :=
  funext (b.reindex_apply e)

/--
theorem `repr_reindex_apply` / 定理 `repr_reindex_apply`

English:
theorem repr_reindex_apply
  given: (i' : ι')
  statement: (b.reindex e).repr x i' = b.repr x (e.symm i')
  proof: show (Finsupp.domLCongr e : _ ≃ₗ[R] _) (b.repr x) i' = _ by simp

@[simp]

中文:
定理 repr_reindex_apply
  条件: (i' : ι')
  结论: (b.reindex e).repr x i' = b.repr x (e.symm i')
  证明: show (Finsupp.domLCongr e : _ ≃ₗ[R] _) (b.repr x) i' = _ by simp

@[simp]

Depends on / 依赖: Finsupp, Finsupp.domLCongr, b.repr, domLCongr
-/
theorem repr_reindex_apply (i' : ι') : (b.reindex e).repr x i' = b.repr x (e.symm i') :=
  show (Finsupp.domLCongr e : _ ≃ₗ[R] _) (b.repr x) i' = _ by simp

@[simp]
/--
theorem `repr_reindex` / 定理 `repr_reindex`

English:
theorem repr_reindex
  statement: (b.reindex e).repr x = (b.repr x).mapDomain e
  proof: DFunLike.ext _ _ by simp [repr_reindex_apply]

@[simp]

中文:
定理 repr_reindex
  结论: (b.reindex e).repr x = (b.repr x).mapDomain e
  证明: DFunLike.ext _ _ by simp [repr_reindex_apply]

@[simp]

Depends on / 依赖: DFunLike, DFunLike.ext, repr_reindex_apply
-/
theorem repr_reindex : (b.reindex e).repr x = (b.repr x).mapDomain e :=
DFunLike.ext _ _ by simp [repr_reindex_apply]

@[simp]
/--
theorem `reindex_refl` / 定理 `reindex_refl`

English:
theorem reindex_refl
  statement: b.reindex (Equiv.refl ι) = b
  proof: by
  simp [reindex]

中文:
定理 reindex_refl
  结论: b.reindex (等价.refl ι) = b
  证明: by
  simp [reindex]

Depends on / 依赖: reindex
-/
theorem reindex_refl : b.reindex (Equiv.refl ι) = b := by
  simp [reindex]

/--
theorem `range_reindex` / 定理 `range_reindex`

English:
theorem range_reindex
  statement: Set.range (b.reindex e) = Set.range b
  proof: by
  simp [coe_reindex, range_comp]

中文:
定理 range_reindex
  结论: 集合.range (b.reindex e) = 集合.range b
  证明: by
  simp [coe_reindex, range_comp]

Depends on / 依赖: coe_reindex, range_comp
-/
theorem range_reindex : Set.range (b.reindex e) = Set.range b := by
  simp [coe_reindex, range_comp]

end Reindex

end Basis

section Fintype

open Basis

open Fintype

/--
Definition of `Basis.equivFun` / `Basis.equivFun` 的定义

English:
definition Basis.equivFun
  signature: [Finite ι] (b : Basis ι R M)
  body: LinearEquiv.trans b.repr
    ({ Finsupp.equivFunOnFinite with
        toFun := (↑)
        map_add' := Finsupp.coe_add
        map_smul' := Finsupp.coe_smul } :
      (ι ->₀ R) ≃ₗ[R] ι -> R)

中文:
定义 基.equivFun
  签名: [有限 ι] (b : 基 ι R M)
  定义体: LinearEquiv.trans b.repr
    ({ Finsupp.equivFunOnFinite with
        toFun := (↑)
        map_add' := Finsupp.coe_add
        map_smul' := Finsupp.coe_smul } :
      (ι ->₀ R) ≃ₗ[R] ι -> R)

Depends on / 依赖: Finsupp, Finsupp.coe_add, Finsupp.coe_smul, Finsupp.equivFunOnFinite, LinearEquiv, LinearEquiv.trans, b.repr, coe_add, coe_smul, equivFunOnFinite, map_add, map_smul
-/
def Basis.equivFun [Finite ι] (b : Basis ι R M) : M ≃ₗ[R] ι -> R :=
  LinearEquiv.trans b.repr
    ({ Finsupp.equivFunOnFinite with
        toFun := (↑)
        map_add' := Finsupp.coe_add
        map_smul' := Finsupp.coe_smul } :
      (ι ->₀ R) ≃ₗ[R] ι -> R)

/-- A module over a finite ring that admits a finite basis is finite. -/
@[instance_reducible]
/--
Definition of `fintypeOfFintype` / `fintypeOfFintype` 的定义

English:
definition fintypeOfFintype
  signature: [Fintype ι] (b : Basis ι R M) [Fintype R]
  body: haveI := Classical.decEq ι
  Fintype.ofEquiv _ b.equivFun.toEquiv.symm

中文:
定义 fintypeOfFintype
  签名: [有限类型 ι] (b : 基 ι R M) [有限类型 R]
  定义体: haveI := Classical.decEq ι
  Fintype.ofEquiv _ b.equivFun.toEquiv.symm

Depends on / 依赖: Classical, Classical.decEq, Fintype, Fintype.ofEquiv, b.equivFun.toEquiv.symm, equivFun, ofEquiv, toEquiv
-/
def fintypeOfFintype [Fintype ι] (b : Basis ι R M) [Fintype R] : Fintype M :=
  haveI := Classical.decEq ι
  Fintype.ofEquiv _ b.equivFun.toEquiv.symm

set_option backward.isDefEq.respectTransparency false in
/-- Given a basis `v` indexed by `ι`, the canonical linear equivalence between `ι → R` and `M` maps
a function `x : ι → R` to the linear combination `∑_i x i • v i`. -/
@[simp]
/--
theorem `Basis.equivFun_symm_apply` / 定理 `Basis.equivFun_symm_apply`

English:
theorem Basis.equivFun_symm_apply
  given: [Fintype ι] (b : Basis ι R M) (x : ι -> R)
  proof: by
  simp [Basis.equivFun, Finsupp.linearCombination_apply, sum_fintype, equivFunOnFinite]

@[simp]

中文:
定理 基.equivFun_symm_apply
  条件: [有限类型 ι] (b : 基 ι R M) (x : ι -> R)
  证明: by
  simp [Basis.equivFun, Finsupp.linearCombination_apply, sum_fintype, equivFunOnFinite]

@[simp]

Depends on / 依赖: Basis.equivFun, Finsupp, Finsupp.linearCombination_apply, equivFun, equivFunOnFinite, linearCombination_apply, sum_fintype
-/
theorem Basis.equivFun_symm_apply [Fintype ι] (b : Basis ι R M) (x : ι -> R) :
    b.equivFun.symm x = ∑ i, x i • b i := by
  simp [Basis.equivFun, Finsupp.linearCombination_apply, sum_fintype, equivFunOnFinite]

@[simp]
/--
theorem `Basis.equivFun_apply` / 定理 `Basis.equivFun_apply`

English:
theorem Basis.equivFun_apply
  given: [Finite ι] (b : Basis ι R M) (u : M)
  statement: b.equivFun u = b.repr u
  proof: rfl

@[simp]

中文:
定理 基.equivFun_apply
  条件: [有限 ι] (b : 基 ι R M) (u : M)
  结论: b.equivFun u = b.repr u
  证明: rfl

@[simp]
-/
theorem Basis.equivFun_apply [Finite ι] (b : Basis ι R M) (u : M) : b.equivFun u = b.repr u :=
  rfl

@[simp]
/--
theorem `Basis.map_equivFun` / 定理 `Basis.map_equivFun`

English:
theorem Basis.map_equivFun
  given: [Finite ι] (b : Basis ι R M) (f : M ≃ₗ[R] M')
  proof: rfl

中文:
定理 基.map_equivFun
  条件: [有限 ι] (b : 基 ι R M) (f : M ≃ₗ[R] M')
  证明: rfl
-/
theorem Basis.map_equivFun [Finite ι] (b : Basis ι R M) (f : M ≃ₗ[R] M') :
    (b.map f).equivFun = f.symm.trans b.equivFun :=
  rfl

/--
theorem `Basis.sum_equivFun` / 定理 `Basis.sum_equivFun`

English:
theorem Basis.sum_equivFun
  given: [Fintype ι] (b : Basis ι R M) (u : M)
  proof: by
  rw [← b.equivFun_symm_apply]; rw [b.equivFun.symm_apply_apply]

@[simp]

中文:
定理 基.sum_equivFun
  条件: [有限类型 ι] (b : 基 ι R M) (u : M)
  证明: by
  rw [← b.equivFun_symm_apply]; rw [b.equivFun.symm_apply_apply]

@[simp]

Depends on / 依赖: b.equivFun.symm_apply_apply, b.equivFun_symm_apply, equivFun, equivFun_symm_apply, symm_apply_apply
-/
theorem Basis.sum_equivFun [Fintype ι] (b : Basis ι R M) (u : M) :
    ∑ i, b.equivFun u i • b i = u := by
  rw [← b.equivFun_symm_apply]; rw [b.equivFun.symm_apply_apply]

@[simp]
/--
theorem `Basis.sum_repr` / 定理 `Basis.sum_repr`

English:
theorem Basis.sum_repr
  given: [Fintype ι] (b : Basis ι R M) (u : M)
  statement: ∑ i, b.repr u i • b i = u
  proof: b.sum_equivFun u

@[simp]

中文:
定理 基.sum_repr
  条件: [有限类型 ι] (b : 基 ι R M) (u : M)
  结论: ∑ i, b.repr u i • b i = u
  证明: b.sum_equivFun u

@[simp]

Depends on / 依赖: b.sum_equivFun, sum_equivFun
-/
theorem Basis.sum_repr [Fintype ι] (b : Basis ι R M) (u : M) : ∑ i, b.repr u i • b i = u :=
  b.sum_equivFun u

@[simp]
/--
theorem `Basis.equivFun_self` / 定理 `Basis.equivFun_self`

English:
theorem Basis.equivFun_self
  given: [Finite ι] [DecidableEq ι] (b : Basis ι R M) (i j : ι)
  proof: by rw [b.equivFun_apply, b.repr_self_apply]

中文:
定理 基.equivFun_self
  条件: [有限 ι] [DecidableEq ι] (b : 基 ι R M) (i j : ι)
  证明: by rw [b.equivFun_apply, b.repr_self_apply]

Depends on / 依赖: b.equivFun_apply, b.repr_self_apply, equivFun_apply, repr_self_apply
-/
theorem Basis.equivFun_self [Finite ι] [DecidableEq ι] (b : Basis ι R M) (i j : ι) :
    b.equivFun (b i) j = if i = j then 1 else 0 := by rw [b.equivFun_apply, b.repr_self_apply]

/--
theorem `Basis.repr_sum_self` / 定理 `Basis.repr_sum_self`

English:
theorem Basis.repr_sum_self
  given: [Fintype ι] (b : Basis ι R M) (c : ι -> R)
  proof: by
  simp_rw [← b.equivFun_symm_apply, ← b.equivFun_apply, b.equivFun.apply_symm_apply]

中文:
定理 基.repr_sum_self
  条件: [有限类型 ι] (b : 基 ι R M) (c : ι -> R)
  证明: by
  simp_rw [← b.equivFun_symm_apply, ← b.equivFun_apply, b.equivFun.apply_symm_apply]

Depends on / 依赖: apply_symm_apply, b.equivFun.apply_symm_apply, b.equivFun_apply, b.equivFun_symm_apply, equivFun, equivFun_apply, equivFun_symm_apply, simp_rw
-/
theorem Basis.repr_sum_self [Fintype ι] (b : Basis ι R M) (c : ι -> R) :
    b.repr (∑ i, c i • b i) = c := by
  simp_rw [← b.equivFun_symm_apply, ← b.equivFun_apply, b.equivFun.apply_symm_apply]

/--
Definition of `Basis.ofEquivFun` / `Basis.ofEquivFun` 的定义

English:
definition Basis.ofEquivFun
  signature: [Finite ι] (e : M ≃ₗ[R] ι -> R)
  body: .ofRepr e.trans LinearEquiv.symm Finsupp.linearEquivFunOnFinite R R ι

@[simp]

中文:
定义 基.ofEquivFun
  签名: [有限 ι] (e : M ≃ₗ[R] ι -> R)
  定义体: .ofRepr e.trans LinearEquiv.symm Finsupp.linearEquivFunOnFinite R R ι

@[simp]

Depends on / 依赖: Finsupp, Finsupp.linearEquivFunOnFinite, LinearEquiv, LinearEquiv.symm, e.trans, linearEquivFunOnFinite, ofRepr
-/
def Basis.ofEquivFun [Finite ι] (e : M ≃ₗ[R] ι -> R) : Basis ι R M :=
.ofRepr e.trans LinearEquiv.symm Finsupp.linearEquivFunOnFinite R R ι

@[simp]
/--
theorem `Basis.ofEquivFun_repr_apply` / 定理 `Basis.ofEquivFun_repr_apply`

English:
theorem Basis.ofEquivFun_repr_apply
  given: [Finite ι] (e : M ≃ₗ[R] ι -> R) (x : M) (i : ι)
  proof: rfl

@[simp]

中文:
定理 基.ofEquivFun_repr_apply
  条件: [有限 ι] (e : M ≃ₗ[R] ι -> R) (x : M) (i : ι)
  证明: rfl

@[simp]
-/
theorem Basis.ofEquivFun_repr_apply [Finite ι] (e : M ≃ₗ[R] ι -> R) (x : M) (i : ι) :
    (Basis.ofEquivFun e).repr x i = e x i :=
  rfl

@[simp]
/--
theorem `Basis.coe_ofEquivFun` / 定理 `Basis.coe_ofEquivFun`

English:
theorem Basis.coe_ofEquivFun
  given: [Finite ι] [DecidableEq ι] (e : M ≃ₗ[R] ι -> R)
  proof: funext fun i =>
e.injective
      funext fun j => by
        simp [Basis.ofEquivFun, ← Finsupp.single_eq_pi_single]

@[simp]

中文:
定理 基.coe_ofEquivFun
  条件: [有限 ι] [DecidableEq ι] (e : M ≃ₗ[R] ι -> R)
  证明: funext fun i =>
e.injective
      funext fun j => by
        simp [Basis.ofEquivFun, ← Finsupp.single_eq_pi_single]

@[simp]

Depends on / 依赖: Basis.ofEquivFun, Finsupp, Finsupp.single_eq_pi_single, e.injective, injective, ofEquivFun, single_eq_pi_single
-/
theorem Basis.coe_ofEquivFun [Finite ι] [DecidableEq ι] (e : M ≃ₗ[R] ι -> R) :
    (Basis.ofEquivFun e : ι -> M) = fun i => e.symm (Pi.single i 1) :=
  funext fun i =>
e.injective
      funext fun j => by
        simp [Basis.ofEquivFun, ← Finsupp.single_eq_pi_single]

@[simp]
/--
theorem `Basis.ofEquivFun_equivFun` / 定理 `Basis.ofEquivFun_equivFun`

English:
theorem Basis.ofEquivFun_equivFun
  given: [Finite ι] (v : Basis ι R M)
  proof: Basis.repr_injective by ext; rfl

@[simp]

中文:
定理 基.ofEquivFun_equivFun
  条件: [有限 ι] (v : 基 ι R M)
  证明: Basis.repr_injective by ext; rfl

@[simp]

Depends on / 依赖: Basis.repr_injective, repr_injective
-/
theorem Basis.ofEquivFun_equivFun [Finite ι] (v : Basis ι R M) :
    Basis.ofEquivFun v.equivFun = v :=
Basis.repr_injective by ext; rfl

@[simp]
/--
theorem `Basis.equivFun_ofEquivFun` / 定理 `Basis.equivFun_ofEquivFun`

English:
theorem Basis.equivFun_ofEquivFun
  given: [Finite ι] (e : M ≃ₗ[R] ι -> R)
  proof: by
  ext j
  simp_rw [Basis.equivFun_apply, Basis.ofEquivFun_repr_apply]

中文:
定理 基.equivFun_ofEquivFun
  条件: [有限 ι] (e : M ≃ₗ[R] ι -> R)
  证明: by
  ext j
  simp_rw [Basis.equivFun_apply, Basis.ofEquivFun_repr_apply]

Depends on / 依赖: Basis.equivFun_apply, Basis.ofEquivFun_repr_apply, equivFun_apply, ofEquivFun_repr_apply, simp_rw
-/
theorem Basis.equivFun_ofEquivFun [Finite ι] (e : M ≃ₗ[R] ι -> R) :
    (Basis.ofEquivFun e).equivFun = e := by
  ext j
  simp_rw [Basis.equivFun_apply, Basis.ofEquivFun_repr_apply]

end Fintype

variable {ι R M : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M]

namespace Basis

variable (b : Basis ι R M)

section Ext

variable {R₁ : Type*} [Semiring R₁] {σ : R ->+* R₁} {σ' : R₁ ->+* R}
variable [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
variable {M₁ : Type*} [AddCommMonoid M₁] [Module R₁ M₁]

/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f₁ f₂ : M ->ₛₗ[σ] M₁} (h : forall i, f₁ (b i) = f₂ (b i))
  statement: f₁ = f₂
  proof: by
  ext x
  rw [← b.linearCombination_repr x]; rw [Finsupp.linearCombination_apply]; rw [Finsupp.sum]
  simp only [map_sum, map_smulₛₗ, h]

中文:
定理 ext
  条件: {f₁ f₂ : M ->ₛₗ[σ] M₁} (h : 对任意 i, f₁ (b i) = f₂ (b i))
  结论: f₁ = f₂
  证明: by
  ext x
  rw [← b.linearCombination_repr x]; rw [Finsupp.linearCombination_apply]; rw [Finsupp.sum]
  simp only [map_sum, map_smulₛₗ, h]

Depends on / 依赖: Finsupp, Finsupp.linearCombination_apply, Finsupp.sum, b.linearCombination_repr, linearCombination_apply, linearCombination_repr, map_sum
-/
theorem ext {f₁ f₂ : M ->ₛₗ[σ] M₁} (h : forall i, f₁ (b i) = f₂ (b i)) : f₁ = f₂ := by
  ext x
  rw [← b.linearCombination_repr x]; rw [Finsupp.linearCombination_apply]; rw [Finsupp.sum]
  simp only [map_sum, map_smulₛₗ, h]

/--
theorem `ext'` / 定理 `ext'`

English:
theorem ext'
  given: {f₁ f₂ : M ≃ₛₗ[σ] M₁} (h : forall i, f₁ (b i) = f₂ (b i))
  statement: f₁ = f₂
  proof: by
  ext x
  rw [← b.linearCombination_repr x]; rw [Finsupp.linearCombination_apply]; rw [Finsupp.sum]
  simp only [map_sum, map_smulₛₗ, h]

中文:
定理 ext'
  条件: {f₁ f₂ : M ≃ₛₗ[σ] M₁} (h : 对任意 i, f₁ (b i) = f₂ (b i))
  结论: f₁ = f₂
  证明: by
  ext x
  rw [← b.linearCombination_repr x]; rw [Finsupp.linearCombination_apply]; rw [Finsupp.sum]
  simp only [map_sum, map_smulₛₗ, h]

Depends on / 依赖: Finsupp, Finsupp.linearCombination_apply, Finsupp.sum, b.linearCombination_repr, linearCombination_apply, linearCombination_repr, map_sum
-/
theorem ext' {f₁ f₂ : M ≃ₛₗ[σ] M₁} (h : forall i, f₁ (b i) = f₂ (b i)) : f₁ = f₂ := by
  ext x
  rw [← b.linearCombination_repr x]; rw [Finsupp.linearCombination_apply]; rw [Finsupp.sum]
  simp only [map_sum, map_smulₛₗ, h]

/--
theorem `ext_elem_iff` / 定理 `ext_elem_iff`

English:
theorem ext_elem_iff
  given: {x y : M}
  statement: x = y ↔ forall i, b.repr x i = b.repr y i
  proof: by
  simp only [← DFunLike.ext_iff, EmbeddingLike.apply_eq_iff_eq]

alias ⟨_, ext_elem⟩ := ext_elem_iff

中文:
定理 ext_elem_iff
  条件: {x y : M}
  结论: x = y ↔ 对任意 i, b.repr x i = b.repr y i
  证明: by
  simp only [← DFunLike.ext_iff, EmbeddingLike.apply_eq_iff_eq]

alias ⟨_, ext_elem⟩ := ext_elem_iff

Depends on / 依赖: DFunLike, DFunLike.ext_iff, EmbeddingLike, EmbeddingLike.apply_eq_iff_eq, apply_eq_iff_eq, ext_iff
-/
theorem ext_elem_iff {x y : M} : x = y ↔ forall i, b.repr x i = b.repr y i := by
  simp only [← DFunLike.ext_iff, EmbeddingLike.apply_eq_iff_eq]

alias ⟨_, ext_elem⟩ := ext_elem_iff

/--
theorem `repr_eq_iff` / 定理 `repr_eq_iff`

English:
theorem repr_eq_iff
  given: {b : Basis ι R M} {f : M ->ₗ[R] ι ->₀ R}
  proof: ⟨fun h i => h ▸ b.repr_self i, fun h => b.ext fun i => (b.repr_self i).trans (h i).symm⟩

中文:
定理 repr_eq_iff
  条件: {b : 基 ι R M} {f : M ->ₗ[R] ι ->₀ R}
  证明: ⟨fun h i => h ▸ b.repr_self i, fun h => b.ext fun i => (b.repr_self i).trans (h i).symm⟩

Depends on / 依赖: b.ext, b.repr_self, repr_self
-/
theorem repr_eq_iff {b : Basis ι R M} {f : M ->ₗ[R] ι ->₀ R} :
    ↑b.repr = f ↔ forall i, f (b i) = Finsupp.single i 1 :=
  ⟨fun h i => h ▸ b.repr_self i, fun h => b.ext fun i => (b.repr_self i).trans (h i).symm⟩

/--
theorem `repr_eq_iff'` / 定理 `repr_eq_iff'`

English:
theorem repr_eq_iff'
  given: {b : Basis ι R M} {f : M ≃ₗ[R] ι ->₀ R}
  proof: ⟨fun h i => h ▸ b.repr_self i, fun h => b.ext' fun i => (b.repr_self i).trans (h i).symm⟩

中文:
定理 repr_eq_iff'
  条件: {b : 基 ι R M} {f : M ≃ₗ[R] ι ->₀ R}
  证明: ⟨fun h i => h ▸ b.repr_self i, fun h => b.ext' fun i => (b.repr_self i).trans (h i).symm⟩

Depends on / 依赖: b.ext, b.repr_self, repr_self
-/
theorem repr_eq_iff' {b : Basis ι R M} {f : M ≃ₗ[R] ι ->₀ R} :
    b.repr = f ↔ forall i, f (b i) = Finsupp.single i 1 :=
  ⟨fun h i => h ▸ b.repr_self i, fun h => b.ext' fun i => (b.repr_self i).trans (h i).symm⟩

/--
theorem `apply_eq_iff` / 定理 `apply_eq_iff`

English:
theorem apply_eq_iff
  given: {b : Basis ι R M} {x : M} {i : ι}
  statement: b i = x ↔ b.repr x = Finsupp.single i 1
  proof: ⟨fun h => h ▸ b.repr_self i, fun h => b.repr.injective ((b.repr_self i).trans h.symm)⟩

中文:
定理 apply_eq_iff
  条件: {b : 基 ι R M} {x : M} {i : ι}
  结论: b i = x ↔ b.repr x = 有限支撑.single i 1
  证明: ⟨fun h => h ▸ b.repr_self i, fun h => b.repr.injective ((b.repr_self i).trans h.symm)⟩

Depends on / 依赖: HasBesicovitchCovering, b.repr.injective, b.repr_self, h.symm, injective, instHasBesicovitchCovering, repr_self
-/
theorem apply_eq_iff {b : Basis ι R M} {x : M} {i : ι} : b i = x ↔ b.repr x = Finsupp.single i 1 :=
  ⟨fun h => h ▸ b.repr_self i, fun h => b.repr.injective ((b.repr_self i).trans h.symm)⟩

/--
theorem `repr_apply_eq` / 定理 `repr_apply_eq`

English:
theorem repr_apply_eq
  statement: (f : M -> ι -> R) (hadd : forall x y, f (x + y) = f x + f y)
  proof: by
  let f_i : M ->ₗ[R] R :=
    { toFun x := f x i
      map_add' _ _ := by rw [hadd, Pi.add_apply]
      map_smul' _ _ := by simp [hsmul, Pi.smul_apply] }
  have : Finsupp.lapply i ∘ₗ ↑b.repr = f_i := by
    refine b.ext fun j => ?_
    change b.repr (b j) i = f (b j) i
    rw [b.repr_self]; rw [f_eq]
  calc
    b.repr x i = f_i x := by
      { rw [← this]
        rfl }
    _ = f x i := rfl

中文:
定理 repr_apply_eq
  结论: (f : M -> ι -> R) (hadd : 对任意 x y, f (x + y) = f x + f y)
  证明: by
  let f_i : M ->ₗ[R] R :=
    { toFun x := f x i
      map_add' _ _ := by rw [hadd, Pi.add_apply]
      map_smul' _ _ := by simp [hsmul, Pi.smul_apply] }
  have : Finsupp.lapply i ∘ₗ ↑b.repr = f_i := by
    refine b.ext fun j => ?_
    change b.repr (b j) i = f (b j) i
    rw [b.repr_self]; rw [f_eq]
  calc
    b.repr x i = f_i x := by
      { rw [← this]
        rfl }
    _ = f x i := rfl

Depends on / 依赖: Finsupp, Finsupp.lapply, Pi.add_apply, Pi.smul_apply, add_apply, b.ext, b.repr, b.repr_self, f_eq, lapply, map_add, map_smul, repr_self, smul_apply
-/
theorem repr_apply_eq (f : M -> ι -> R) (hadd : forall x y, f (x + y) = f x + f y)
    (hsmul : forall (c : R) (x : M), f (c • x) = c • f x) (f_eq : forall i, f (b i) = Finsupp.single i 1)
    (x : M) (i : ι) : b.repr x i = f x i := by
  let f_i : M ->ₗ[R] R :=
    { toFun x := f x i
      map_add' _ _ := by rw [hadd, Pi.add_apply]
      map_smul' _ _ := by simp [hsmul, Pi.smul_apply] }
  have : Finsupp.lapply i ∘ₗ ↑b.repr = f_i := by
    refine b.ext fun j => ?_
    change b.repr (b j) i = f (b j) i
    rw [b.repr_self]; rw [f_eq]
  calc
    b.repr x i = f_i x := by
      { rw [← this]
        rfl }
    _ = f x i := rfl

/--
theorem `eq_ofRepr_eq_repr` / 定理 `eq_ofRepr_eq_repr`

English:
theorem eq_ofRepr_eq_repr
  given: {b₁ b₂ : Basis ι R M} (h : forall x i, b₁.repr x i = b₂.repr x i)
  statement: b₁ = b₂
  proof: repr_injective by ext; apply h

中文:
定理 eq_ofRepr_eq_repr
  条件: {b₁ b₂ : 基 ι R M} (h : 对任意 x i, b₁.repr x i = b₂.repr x i)
  结论: b₁ = b₂
  证明: repr_injective by ext; apply h

Depends on / 依赖: repr_injective
-/
theorem eq_ofRepr_eq_repr {b₁ b₂ : Basis ι R M} (h : forall x i, b₁.repr x i = b₂.repr x i) : b₁ = b₂ :=
repr_injective by ext; apply h

/-- Two bases are equal if their basis vectors are the same. -/
@[ext]
/--
theorem `eq_of_apply_eq` / 定理 `eq_of_apply_eq`

English:
theorem eq_of_apply_eq
  given: {b₁ b₂ : Basis ι R M}
  statement: (forall i, b₁ i = b₂ i) -> b₁ = b₂
  proof: DFunLike.ext _ _

中文:
定理 eq_of_apply_eq
  条件: {b₁ b₂ : 基 ι R M}
  结论: (对任意 i, b₁ i = b₂ i) -> b₁ = b₂
  证明: DFunLike.ext _ _

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem eq_of_apply_eq {b₁ b₂ : Basis ι R M} : (forall i, b₁ i = b₂ i) -> b₁ = b₂ :=
  DFunLike.ext _ _

end Ext

section MapCoeffs

variable {R' : Type*} [Semiring R'] [Module R' M] (f : R ≃+* R')

attribute [local instance] SMul.comp.isScalarTower

set_option backward.isDefEq.respectTransparency false in
/-- If `R` and `R'` are isomorphic rings that act identically on a module `M`,
then a basis for `M` as `R`-module is also a basis for `M` as `R'`-module.

See also `Basis.algebraMapCoeffs` for the case where `f` is equal to `algebraMap`.
-/
@[simps +simpRhs]
/--
Definition of `mapCoeffs` / `mapCoeffs` 的定义

English:
definition mapCoeffs
  signature: (h : forall (c) (x : M), f c • x = c • x)
  body: by
  letI : Module R' R := Module.compHom R (↑f.symm : R' ->+* R)
  haveI : IsScalarTower R' R M :=
    { smul_assoc := fun x y z => by
        change (f.symm x * y) • z = x • (y • z)
        rw [mul_smul]; rw [← h]; rw [f.apply_symm_apply] }
exact ofRepr (b.repr.restrictScalars R').trans
    Finsupp.mapRange.linearEquiv (Module.compHom.toLinearEquiv f.symm).symm

中文:
定义 mapCoeffs
  签名: (h : 对任意 (c) (x : M), f c • x = c • x)
  定义体: by
  letI : Module R' R := Module.compHom R (↑f.symm : R' ->+* R)
  haveI : IsScalarTower R' R M :=
    { smul_assoc := fun x y z => by
        change (f.symm x * y) • z = x • (y • z)
        rw [mul_smul]; rw [← h]; rw [f.apply_symm_apply] }
exact ofRepr (b.repr.restrictScalars R').trans
    Finsupp.mapRange.linearEquiv (Module.compHom.toLinearEquiv f.symm).symm

Depends on / 依赖: Finsupp, Finsupp.mapRange.linearEquiv, IsScalarTower, Module, Module.compHom, Module.compHom.toLinearEquiv, apply_symm_apply, b.repr.restrictScalars, compHom, f.apply_symm_apply, f.symm, linearEquiv, mapRange, mul_smul, ofRepr, restrictScalars, smul_assoc, toLinearEquiv
-/
def mapCoeffs (h : forall (c) (x : M), f c • x = c • x) : Basis ι R' M := by
  letI : Module R' R := Module.compHom R (↑f.symm : R' ->+* R)
  haveI : IsScalarTower R' R M :=
    { smul_assoc := fun x y z => by
        change (f.symm x * y) • z = x • (y • z)
        rw [mul_smul]; rw [← h]; rw [f.apply_symm_apply] }
exact ofRepr (b.repr.restrictScalars R').trans
    Finsupp.mapRange.linearEquiv (Module.compHom.toLinearEquiv f.symm).symm

variable (h : forall (c) (x : M), f c • x = c • x)

/--
theorem `mapCoeffs_apply` / 定理 `mapCoeffs_apply`

English:
theorem mapCoeffs_apply
  given: (i : ι)
  statement: b.mapCoeffs f h i = b i
  proof: apply_eq_iff.mpr by simp

@[simp]

中文:
定理 mapCoeffs_apply
  条件: (i : ι)
  结论: b.mapCoeffs f h i = b i
  证明: apply_eq_iff.mpr by simp

@[simp]

Depends on / 依赖: apply_eq_iff, apply_eq_iff.mpr
-/
theorem mapCoeffs_apply (i : ι) : b.mapCoeffs f h i = b i :=
apply_eq_iff.mpr by simp

@[simp]
/--
theorem `coe_mapCoeffs` / 定理 `coe_mapCoeffs`

English:
theorem coe_mapCoeffs
  statement: (b.mapCoeffs f h : ι -> M) = b
  proof: funext b.mapCoeffs_apply f h

中文:
定理 coe_mapCoeffs
  结论: (b.mapCoeffs f h : ι -> M) = b
  证明: funext b.mapCoeffs_apply f h

Depends on / 依赖: b.mapCoeffs_apply, mapCoeffs_apply
-/
theorem coe_mapCoeffs : (b.mapCoeffs f h : ι -> M) = b :=
funext b.mapCoeffs_apply f h

end MapCoeffs

section ReindexRange

/--
Definition of `reindexRange` / `reindexRange` 的定义

English:
definition reindexRange
  signature: : Basis (range b) R M
  body: haveI := Classical.dec (Nontrivial R)
  if h : Nontrivial R then
    b.reindex (Equiv.ofInjective b (Basis.injective b))
  else
    letI : Subsingleton R := not_nontrivial_iff_subsingleton.mp h
    .ofRepr (Module.subsingletonEquiv R M (range b))

中文:
定义 reindexRange
  签名: : 基 (range b) R M
  定义体: haveI := Classical.dec (Nontrivial R)
  if h : Nontrivial R then
    b.reindex (Equiv.ofInjective b (Basis.injective b))
  else
    letI : Subsingleton R := not_nontrivial_iff_subsingleton.mp h
    .ofRepr (Module.subsingletonEquiv R M (range b))

Depends on / 依赖: Basis.injective, Classical, Classical.dec, Equiv.ofInjective, Module, Module.subsingletonEquiv, Nontrivial, Subsingleton, b.reindex, injective, not_nontrivial_iff_subsingleton, not_nontrivial_iff_subsingleton.mp, ofInjective, ofRepr, reindex, subsingletonEquiv
-/
def reindexRange : Basis (range b) R M :=
  haveI := Classical.dec (Nontrivial R)
  if h : Nontrivial R then
    b.reindex (Equiv.ofInjective b (Basis.injective b))
  else
    letI : Subsingleton R := not_nontrivial_iff_subsingleton.mp h
    .ofRepr (Module.subsingletonEquiv R M (range b))

/--
theorem `reindexRange_self` / 定理 `reindexRange_self`

English:
theorem reindexRange_self
  given: (i : ι) (h := Set.mem_range_self i)
  statement: b.reindexRange ⟨b i, h⟩ = b i
  proof: by
  cases subsingleton_or_nontrivial R
  · let := Module.subsingleton R M
    simp [reindexRange, eq_iff_true_of_subsingleton]
  · simp [*, reindexRange, reindex_apply]

中文:
定理 reindexRange_self
  条件: (i : ι) (h := 集合.mem_range_self i)
  结论: b.reindexRange ⟨b i, h⟩ = b i
  证明: by
  cases subsingleton_or_nontrivial R
  · let := Module.subsingleton R M
    simp [reindexRange, eq_iff_true_of_subsingleton]
  · simp [*, reindexRange, reindex_apply]

Depends on / 依赖: Module, Module.subsingleton, Set.mem_range_self, b.reindexRange, eq_iff_true_of_subsingleton, mem_range_self, reindexRange, reindex_apply, subsingleton, subsingleton_or_nontrivial
-/
theorem reindexRange_self (i : ι) (h := Set.mem_range_self i) : b.reindexRange ⟨b i, h⟩ = b i := by
  cases subsingleton_or_nontrivial R
  · let := Module.subsingleton R M
    simp [reindexRange, eq_iff_true_of_subsingleton]
  · simp [*, reindexRange, reindex_apply]

/--
theorem `reindexRange_repr_self` / 定理 `reindexRange_repr_self`

English:
theorem reindexRange_repr_self
  given: (i : ι)
  proof: calc
    b.reindexRange.repr (b i) = b.reindexRange.repr (b.reindexRange ⟨b i, mem_range_self i⟩) :=
      congr_arg _ (b.reindexRange_self _ _).symm
    _ = Finsupp.single ⟨b i, mem_range_self i⟩ 1 := b.reindexRange.repr_self _

@[simp]

中文:
定理 reindexRange_repr_self
  条件: (i : ι)
  证明: calc
    b.reindexRange.repr (b i) = b.reindexRange.repr (b.reindexRange ⟨b i, mem_range_self i⟩) :=
      congr_arg _ (b.reindexRange_self _ _).symm
    _ = Finsupp.single ⟨b i, mem_range_self i⟩ 1 := b.reindexRange.repr_self _

@[simp]

Depends on / 依赖: Finsupp, Finsupp.single, b.reindexRange, b.reindexRange.repr, b.reindexRange.repr_self, b.reindexRange_self, congr_arg, mem_range_self, reindexRange, reindexRange_self, repr_self, single
-/
theorem reindexRange_repr_self (i : ι) :
    b.reindexRange.repr (b i) = Finsupp.single ⟨b i, mem_range_self i⟩ 1 :=
  calc
    b.reindexRange.repr (b i) = b.reindexRange.repr (b.reindexRange ⟨b i, mem_range_self i⟩) :=
      congr_arg _ (b.reindexRange_self _ _).symm
    _ = Finsupp.single ⟨b i, mem_range_self i⟩ 1 := b.reindexRange.repr_self _

@[simp]
/--
theorem `reindexRange_apply` / 定理 `reindexRange_apply`

English:
theorem reindexRange_apply
  given: (x : range b)
  statement: b.reindexRange x = x
  proof: by
  rcases x with ⟨bi, ⟨i, rfl⟩⟩
  exact b.reindexRange_self i

中文:
定理 reindexRange_apply
  条件: (x : range b)
  结论: b.reindexRange x = x
  证明: by
  rcases x with ⟨bi, ⟨i, rfl⟩⟩
  exact b.reindexRange_self i

Depends on / 依赖: b.reindexRange_self, reindexRange_self
-/
theorem reindexRange_apply (x : range b) : b.reindexRange x = x := by
  rcases x with ⟨bi, ⟨i, rfl⟩⟩
  exact b.reindexRange_self i

set_option backward.isDefEq.respectTransparency false in
/--
theorem `reindexRange_repr'` / 定理 `reindexRange_repr'`

English:
theorem reindexRange_repr'
  given: (x : M) {bi : M} {i : ι} (h : b i = bi)
  proof: by
  nontriviality
  subst h
  apply (b.repr_apply_eq (fun x i => b.reindexRange.repr x ⟨b i, _⟩) _ _ _ x i).symm
  · intro x y
    ext i
    simp only [Pi.add_apply, map_add, Finsupp.coe_add]
  · intro c x
    ext i
    simp
  · intro i
    ext j
    simp only [reindexRange_repr_self]
    apply Finsupp.single_apply_left (f := fun i => (⟨b i, _⟩ : Set.range b))
    exact fun i j h => b.injective (Subtype.mk.inj h)

@[simp]

中文:
定理 reindexRange_repr'
  条件: (x : M) {bi : M} {i : ι} (h : b i = bi)
  证明: by
  nontriviality
  subst h
  apply (b.repr_apply_eq (fun x i => b.reindexRange.repr x ⟨b i, _⟩) _ _ _ x i).symm
  · intro x y
    ext i
    simp only [Pi.add_apply, map_add, Finsupp.coe_add]
  · intro c x
    ext i
    simp
  · intro i
    ext j
    simp only [reindexRange_repr_self]
    apply Finsupp.single_apply_left (f := fun i => (⟨b i, _⟩ : Set.range b))
    exact fun i j h => b.injective (Subtype.mk.inj h)

@[simp]

Depends on / 依赖: Finsupp, Finsupp.coe_add, Finsupp.single_apply_left, Pi.add_apply, Set.range, Subtype, Subtype.mk.inj, add_apply, b.injective, b.reindexRange.repr, b.repr_apply_eq, coe_add, injective, map_add, nontriviality, reindexRange, reindexRange_repr_self, repr_apply_eq, single_apply_left
-/
theorem reindexRange_repr' (x : M) {bi : M} {i : ι} (h : b i = bi) :
    b.reindexRange.repr x ⟨bi, ⟨i, h⟩⟩ = b.repr x i := by
  nontriviality
  subst h
  apply (b.repr_apply_eq (fun x i => b.reindexRange.repr x ⟨b i, _⟩) _ _ _ x i).symm
  · intro x y
    ext i
    simp only [Pi.add_apply, map_add, Finsupp.coe_add]
  · intro c x
    ext i
    simp
  · intro i
    ext j
    simp only [reindexRange_repr_self]
    apply Finsupp.single_apply_left (f := fun i => (⟨b i, _⟩ : Set.range b))
    exact fun i j h => b.injective (Subtype.mk.inj h)

@[simp]
/--
theorem `reindexRange_repr` / 定理 `reindexRange_repr`

English:
theorem reindexRange_repr
  given: (x : M) (i : ι) (h := Set.mem_range_self i)
  proof: b.reindexRange_repr' _ rfl

中文:
定理 reindexRange_repr
  条件: (x : M) (i : ι) (h := 集合.mem_range_self i)
  证明: b.reindexRange_repr' _ rfl

Depends on / 依赖: Set.mem_range_self, mem_range_self
-/
theorem reindexRange_repr (x : M) (i : ι) (h := Set.mem_range_self i) :
    b.reindexRange.repr x ⟨b i, h⟩ = b.repr x i :=
  b.reindexRange_repr' _ rfl

section Fintype

variable [Fintype ι] [DecidableEq M]

/--
Definition of `reindexFinsetRange` / `reindexFinsetRange` 的定义

English:
definition reindexFinsetRange
  signature: : Basis (Finset.univ.image b) R M
  body: b.reindexRange.reindex ((Equiv.refl M).subtypeEquiv (by simp))

中文:
定义 reindexFinsetRange
  签名: : 基 (有限集.univ.像 b) R M
  定义体: b.reindexRange.reindex ((Equiv.refl M).subtypeEquiv (by simp))

Depends on / 依赖: Equiv.refl, b.reindexRange.reindex, reindex, reindexRange, subtypeEquiv
-/
def reindexFinsetRange : Basis (Finset.univ.image b) R M :=
  b.reindexRange.reindex ((Equiv.refl M).subtypeEquiv (by simp))

/--
theorem `reindexFinsetRange_self` / 定理 `reindexFinsetRange_self`

English:
theorem reindexFinsetRange_self
  given: (i : ι) (h := Finset.mem_image_of_mem b (Finset.mem_univ i))
  proof: by
  rw [reindexFinsetRange]; rw [reindex_apply]; rw [reindexRange_apply]
  rfl

@[simp]

中文:
定理 reindexFinsetRange_self
  条件: (i : ι) (h := 有限集.mem_image_of_mem b (有限集.mem_univ i))
  证明: by
  rw [reindexFinsetRange]; rw [reindex_apply]; rw [reindexRange_apply]
  rfl

@[simp]

Depends on / 依赖: Finset, Finset.mem_image_of_mem, Finset.mem_univ, mem_image_of_mem, mem_univ
-/
theorem reindexFinsetRange_self (i : ι) (h := Finset.mem_image_of_mem b (Finset.mem_univ i)) :
    b.reindexFinsetRange ⟨b i, h⟩ = b i := by
  rw [reindexFinsetRange]; rw [reindex_apply]; rw [reindexRange_apply]
  rfl

@[simp]
/--
theorem `reindexFinsetRange_apply` / 定理 `reindexFinsetRange_apply`

English:
theorem reindexFinsetRange_apply
  given: (x : Finset.univ.image b)
  statement: b.reindexFinsetRange x = x
  proof: by
  rcases x with ⟨bi, hbi⟩
  rcases Finset.mem_image.mp hbi with ⟨i, -, rfl⟩
  exact b.reindexFinsetRange_self i

中文:
定理 reindexFinsetRange_apply
  条件: (x : 有限集.univ.像 b)
  结论: b.reindexFinsetRange x = x
  证明: by
  rcases x with ⟨bi, hbi⟩
  rcases Finset.mem_image.mp hbi with ⟨i, -, rfl⟩
  exact b.reindexFinsetRange_self i

Depends on / 依赖: Finset, Finset.mem_image.mp, b.reindexFinsetRange_self, mem_image, reindexFinsetRange_self
-/
theorem reindexFinsetRange_apply (x : Finset.univ.image b) : b.reindexFinsetRange x = x := by
  rcases x with ⟨bi, hbi⟩
  rcases Finset.mem_image.mp hbi with ⟨i, -, rfl⟩
  exact b.reindexFinsetRange_self i

/--
theorem `reindexFinsetRange_repr_self` / 定理 `reindexFinsetRange_repr_self`

English:
theorem reindexFinsetRange_repr_self
  given: (i : ι)
  proof: by
  ext ⟨bi, hbi⟩
  rw [reindexFinsetRange]; rw [repr_reindex]; rw [Finsupp.mapDomain_equiv_apply]; rw [reindexRange_repr_self]
  simp [Finsupp.single_apply]

@[simp]

中文:
定理 reindexFinsetRange_repr_self
  条件: (i : ι)
  证明: by
  ext ⟨bi, hbi⟩
  rw [reindexFinsetRange]; rw [repr_reindex]; rw [Finsupp.mapDomain_equiv_apply]; rw [reindexRange_repr_self]
  simp [Finsupp.single_apply]

@[simp]

Depends on / 依赖: Finsupp, Finsupp.mapDomain_equiv_apply, Finsupp.single_apply, mapDomain_equiv_apply, reindexFinsetRange, reindexRange_repr_self, repr_reindex, single_apply
-/
theorem reindexFinsetRange_repr_self (i : ι) :
    b.reindexFinsetRange.repr (b i) =
      Finsupp.single ⟨b i, Finset.mem_image_of_mem b (Finset.mem_univ i)⟩ 1 := by
  ext ⟨bi, hbi⟩
  rw [reindexFinsetRange]; rw [repr_reindex]; rw [Finsupp.mapDomain_equiv_apply]; rw [reindexRange_repr_self]
  simp [Finsupp.single_apply]

@[simp]
/--
theorem `reindexFinsetRange_repr` / 定理 `reindexFinsetRange_repr`

English:
theorem reindexFinsetRange_repr
  statement: (x : M) (i : ι)
  proof: by simp [reindexFinsetRange]

中文:
定理 reindexFinsetRange_repr
  结论: (x : M) (i : ι)
  证明: by simp [reindexFinsetRange]

Depends on / 依赖: Finset, Finset.mem_image_of_mem, Finset.mem_univ, mem_image_of_mem, mem_univ
-/
theorem reindexFinsetRange_repr (x : M) (i : ι)
    (h := Finset.mem_image_of_mem b (Finset.mem_univ i)) :
    b.reindexFinsetRange.repr x ⟨b i, h⟩ = b.repr x i := by simp [reindexFinsetRange]

end Fintype

end ReindexRange

variable [Module R M']

section Constr

variable (S : Type*) [Semiring S] [Module S M']
variable [SMulCommClass R S M']

/--
Definition of `constr` / `constr` 的定义

English:
definition constr
  signature: : (ι -> M') ≃ₗ[S] M ->ₗ[R] M' where
  body: (Finsupp.linearCombination R id).comp Finsupp.lmapDomain R R f ∘ₗ ↑b.repr
  invFun f i := f (b i)
  left_inv f := by
    ext
    simp
  right_inv f := by
    refine b.ext fun i => ?_
    simp
  map_add' f g := by
    refine b.ext fun i => ?_
    simp
  map_smul' c f := by
    refine b.ext fun i => ?_
    simp

中文:
定义 constr
  签名: : (ι -> M') ≃ₗ[S] M ->ₗ[R] M' where
  定义体: (Finsupp.linearCombination R id).comp Finsupp.lmapDomain R R f ∘ₗ ↑b.repr
  invFun f i := f (b i)
  left_inv f := by
    ext
    simp
  right_inv f := by
    refine b.ext fun i => ?_
    simp
  map_add' f g := by
    refine b.ext fun i => ?_
    simp
  map_smul' c f := by
    refine b.ext fun i => ?_
    simp

Depends on / 依赖: Finsupp, Finsupp.linearCombination, Finsupp.lmapDomain, b.repr, linearCombination, lmapDomain
-/
def constr : (ι -> M') ≃ₗ[S] M ->ₗ[R] M' where
toFun f := (Finsupp.linearCombination R id).comp Finsupp.lmapDomain R R f ∘ₗ ↑b.repr
  invFun f i := f (b i)
  left_inv f := by
    ext
    simp
  right_inv f := by
    refine b.ext fun i => ?_
    simp
  map_add' f g := by
    refine b.ext fun i => ?_
    simp
  map_smul' c f := by
    refine b.ext fun i => ?_
    simp

/--
theorem `constr_def` / 定理 `constr_def`

English:
theorem constr_def
  given: (f : ι -> M')
  proof: rfl

中文:
定理 constr_def
  条件: (f : ι -> M')
  证明: rfl

Depends on / 依赖: Finsupp, Finsupp.lmapDomain, b.repr, linearCombination, lmapDomain
-/
theorem constr_def (f : ι -> M') :
    constr (M' := M') b S f = linearCombination R id ∘ₗ Finsupp.lmapDomain R R f ∘ₗ ↑b.repr :=
  rfl

/--
theorem `constr_apply` / 定理 `constr_apply`

English:
theorem constr_apply
  given: (f : ι -> M') (x : M)
  proof: by
  simp only [constr_def, LinearMap.comp_apply, lmapDomain_apply, linearCombination_apply]
  rw [Finsupp.sum_mapDomain_index] <;> simp [add_smul]

中文:
定理 constr_apply
  条件: (f : ι -> M') (x : M)
  证明: by
  simp only [constr_def, LinearMap.comp_apply, lmapDomain_apply, linearCombination_apply]
  rw [Finsupp.sum_mapDomain_index] <;> simp [add_smul]

Depends on / 依赖: Finsupp, Finsupp.sum_mapDomain_index, LinearMap, LinearMap.comp_apply, add_smul, b.repr, comp_apply, constr_def, linearCombination_apply, lmapDomain_apply, sum_mapDomain_index
-/
theorem constr_apply (f : ι -> M') (x : M) :
    constr (M' := M') b S f x = (b.repr x).sum fun b a => a • f b := by
  simp only [constr_def, LinearMap.comp_apply, lmapDomain_apply, linearCombination_apply]
  rw [Finsupp.sum_mapDomain_index] <;> simp [add_smul]

/--
theorem `constr_symm_apply` / 定理 `constr_symm_apply`

English:
theorem constr_symm_apply
  given: (f : M ->ₗ[R] M') (i)
  proof: by
  rfl

@[simp]

中文:
定理 constr_symm_apply
  条件: (f : M ->ₗ[R] M') (i)
  证明: by
  rfl

@[simp]
-/
@[simp] theorem constr_symm_apply (f : M ->ₗ[R] M') (i) :
    (b.constr S).symm f i = f (b i) := by
  rfl

@[simp]
/--
theorem `constr_basis` / 定理 `constr_basis`

English:
theorem constr_basis
  given: (f : ι -> M') (i : ι)
  statement: (constr (M' := M') b S f : M -> M') (b i) = f i
  proof: by
  simp [Basis.constr_apply, b.repr_self]

中文:
定理 constr_basis
  条件: (f : ι -> M') (i : ι)
  结论: (constr (M' := M') b S f : M -> M') (b i) = f i
  证明: by
  simp [Basis.constr_apply, b.repr_self]

Depends on / 依赖: Basis.constr_apply, b.repr_self, constr_apply, repr_self
-/
theorem constr_basis (f : ι -> M') (i : ι) : (constr (M' := M') b S f : M -> M') (b i) = f i := by
  simp [Basis.constr_apply, b.repr_self]

/--
theorem `constr_eq` / 定理 `constr_eq`

English:
theorem constr_eq
  given: {g : ι -> M'} {f : M ->ₗ[R] M'} (h : forall i, g i = f (b i))
  proof: b.ext fun i => (b.constr_basis S g i).trans (h i)

中文:
定理 constr_eq
  条件: {g : ι -> M'} {f : M ->ₗ[R] M'} (h : 对任意 i, g i = f (b i))
  证明: b.ext fun i => (b.constr_basis S g i).trans (h i)
-/
theorem constr_eq {g : ι -> M'} {f : M ->ₗ[R] M'} (h : forall i, g i = f (b i)) :
    constr (M' := M') b S g = f :=
  b.ext fun i => (b.constr_basis S g i).trans (h i)

/--
theorem `constr_self` / 定理 `constr_self`

English:
theorem constr_self
  given: (f : M ->ₗ[R] M')
  statement: (constr (M' := M') b S fun i => f (b i)) = f
  proof: b.constr_eq S fun _ => rfl

中文:
定理 constr_self
  条件: (f : M ->ₗ[R] M')
  结论: (constr (M' := M') b S fun i => f (b i)) = f
  证明: b.constr_eq S fun _ => rfl
-/
theorem constr_self (f : M ->ₗ[R] M') : (constr (M' := M') b S fun i => f (b i)) = f :=
  b.constr_eq S fun _ => rfl

/--
theorem `constr_range` / 定理 `constr_range`

English:
theorem constr_range
  given: {f : ι -> M'}
  proof: by
  rw [b.constr_def S f]; rw [LinearMap.range_comp]; rw [LinearMap.range_comp]; rw [LinearEquiv.range]; rw [←
    Finsupp.supported_univ]; rw [Finsupp.lmapDomain_supported]; rw [← Set.image_univ]; rw [←
    Finsupp.span_image_eq_map_linearCombination]; rw [Set.image_id]

@[simp]

中文:
定理 constr_range
  条件: {f : ι -> M'}
  证明: by
  rw [b.constr_def S f]; rw [LinearMap.range_comp]; rw [LinearMap.range_comp]; rw [LinearEquiv.range]; rw [←
    Finsupp.supported_univ]; rw [Finsupp.lmapDomain_supported]; rw [← Set.image_univ]; rw [←
    Finsupp.span_image_eq_map_linearCombination]; rw [Set.image_id]

@[simp]

Depends on / 依赖: Finsupp, Finsupp.lmapDomain_supported, Finsupp.span_image_eq_map_linearCombination, Finsupp.supported_univ, LinearEquiv, LinearEquiv.range, LinearMap, LinearMap.range_comp, Set.image_id, Set.image_univ, b.constr_def, constr_def, image_id, image_univ, lmapDomain_supported, range_comp, span_image_eq_map_linearCombination, supported_univ
-/
theorem constr_range {f : ι -> M'} :
    LinearMap.range (constr (M' := M') b S f) = span R (range f) := by
  rw [b.constr_def S f]; rw [LinearMap.range_comp]; rw [LinearMap.range_comp]; rw [LinearEquiv.range]; rw [←
    Finsupp.supported_univ]; rw [Finsupp.lmapDomain_supported]; rw [← Set.image_univ]; rw [←
    Finsupp.span_image_eq_map_linearCombination]; rw [Set.image_id]

@[simp]
/--
theorem `constr_comp` / 定理 `constr_comp`

English:
theorem constr_comp
  given: (f : M' ->ₗ[R] M') (v : ι -> M')
  proof: b.ext fun i => by simp only [Basis.constr_basis, LinearMap.comp_apply, Function.comp]

中文:
定理 constr_comp
  条件: (f : M' ->ₗ[R] M') (v : ι -> M')
  证明: b.ext fun i => by simp only [Basis.constr_basis, LinearMap.comp_apply, Function.comp]

Depends on / 依赖: constr, f.comp
-/
theorem constr_comp (f : M' ->ₗ[R] M') (v : ι -> M') :
    constr (M' := M') b S (f ∘ v) = f.comp (constr (M' := M') b S v) :=
  b.ext fun i => by simp only [Basis.constr_basis, LinearMap.comp_apply, Function.comp]

variable (S : Type*) [Semiring S] [Module S M']
variable [SMulCommClass R S M']

@[simp]
/--
theorem `constr_apply_fintype` / 定理 `constr_apply_fintype`

English:
theorem constr_apply_fintype
  given: [Fintype ι] (b : Basis ι R M) (f : ι -> M') (x : M)
  proof: by
  simp [b.constr_apply, b.equivFun_apply, Finsupp.sum_fintype]

中文:
定理 constr_apply_fintype
  条件: [有限类型 ι] (b : 基 ι R M) (f : ι -> M') (x : M)
  证明: by
  simp [b.constr_apply, b.equivFun_apply, Finsupp.sum_fintype]

Depends on / 依赖: Finsupp, Finsupp.sum_fintype, b.constr_apply, b.equivFun, b.equivFun_apply, constr_apply, equivFun, equivFun_apply, sum_fintype
-/
theorem constr_apply_fintype [Fintype ι] (b : Basis ι R M) (f : ι -> M') (x : M) :
    (constr (M' := M') b S f : M -> M') x = ∑ i, b.equivFun x i • f i := by
  simp [b.constr_apply, b.equivFun_apply, Finsupp.sum_fintype]

end Constr

section Equiv

variable (i : ι)
variable {M'' : Type*} (b' : Basis ι' R M') (e : ι ≃ ι')
variable [AddCommMonoid M''] [Module R M'']

/--
Definition of `equiv` / `equiv` 的定义

English:
definition equiv
  signature: : M ≃ₗ[R] M'
  body: b.repr.trans (b'.reindex e.symm).repr.symm

@[simp]

中文:
定义 equiv
  签名: : M ≃ₗ[R] M'
  定义体: b.repr.trans (b'.reindex e.symm).repr.symm

@[simp]
-/
protected def equiv : M ≃ₗ[R] M' :=
  b.repr.trans (b'.reindex e.symm).repr.symm

@[simp]
/--
theorem `equiv_apply` / 定理 `equiv_apply`

English:
theorem equiv_apply
  statement: b.equiv b' e (b i) = b' (e i)
  proof: by simp [Basis.equiv]

@[simp]

中文:
定理 equiv_apply
  结论: b.equiv b' e (b i) = b' (e i)
  证明: by simp [Basis.equiv]

@[simp]

Depends on / 依赖: Basis.equiv
-/
theorem equiv_apply : b.equiv b' e (b i) = b' (e i) := by simp [Basis.equiv]

@[simp]
/--
theorem `equiv_refl` / 定理 `equiv_refl`

English:
theorem equiv_refl
  statement: b.equiv b (Equiv.refl ι) = LinearEquiv.refl R M
  proof: b.ext' fun i => by simp

@[simp]

中文:
定理 equiv_refl
  结论: b.equiv b (等价.refl ι) = 线性等价.refl R M
  证明: b.ext' fun i => by simp

@[simp]

Depends on / 依赖: b.ext
-/
theorem equiv_refl : b.equiv b (Equiv.refl ι) = LinearEquiv.refl R M :=
  b.ext' fun i => by simp

@[simp]
/--
theorem `equiv_symm` / 定理 `equiv_symm`

English:
theorem equiv_symm
  statement: (b.equiv b' e).symm = b'.equiv b e.symm
  proof: b'.ext' fun i => (b.equiv b' e).injective (by simp)

@[simp]

中文:
定理 equiv_symm
  结论: (b.equiv b' e).symm = b'.equiv b e.symm
  证明: b'.ext' fun i => (b.equiv b' e).injective (by simp)

@[simp]

Depends on / 依赖: b.equiv, injective
-/
theorem equiv_symm : (b.equiv b' e).symm = b'.equiv b e.symm :=
  b'.ext' fun i => (b.equiv b' e).injective (by simp)

@[simp]
/--
theorem `equiv_trans` / 定理 `equiv_trans`

English:
theorem equiv_trans
  given: {ι'' : Type*} (b'' : Basis ι'' R M'') (e : ι ≃ ι') (e' : ι' ≃ ι'')
  proof: b.ext' fun i => by simp

@[simp]

中文:
定理 equiv_trans
  条件: {ι'' : 类型} (b'' : 基 ι'' R M'') (e : ι ≃ ι') (e' : ι' ≃ ι'')
  证明: b.ext' fun i => by simp

@[simp]

Depends on / 依赖: b.ext
-/
theorem equiv_trans {ι'' : Type*} (b'' : Basis ι'' R M'') (e : ι ≃ ι') (e' : ι' ≃ ι'') :
    (b.equiv b' e).trans (b'.equiv b'' e') = b.equiv b'' (e.trans e') :=
  b.ext' fun i => by simp

@[simp]
/--
theorem `map_equiv` / 定理 `map_equiv`

English:
theorem map_equiv
  given: (b : Basis ι R M) (b' : Basis ι' R M') (e : ι ≃ ι')
  proof: by
  ext i
  simp

中文:
定理 map_equiv
  条件: (b : 基 ι R M) (b' : 基 ι' R M') (e : ι ≃ ι')
  证明: by
  ext i
  simp
-/
theorem map_equiv (b : Basis ι R M) (b' : Basis ι' R M') (e : ι ≃ ι') :
    b.map (b.equiv b' e) = b'.reindex e.symm := by
  ext i
  simp

section CommSemiring

variable {R M M' : Type*} [CommSemiring R]
variable [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
variable (b : Basis ι R M) (b' : Basis ι' R M')
variable [SMulCommClass R R M']

/--
Definition of `equiv'` / `equiv'` 的定义

English:
definition equiv'
  signature: (f : M -> M') (g : M' -> M) (hf : forall i, f (b i) in range b') (hg : forall i, g (b' i) in range b)
  body: { constr (M' := M') b R (f ∘ b) with
    invFun := constr (M' := M) b' R (g ∘ b')
    left_inv :=
      have : (constr (M' := M) b' R (g ∘ b')).comp (constr (M' := M') b R (f ∘ b)) = LinearMap.id :=
        b.ext fun i =>
          Exists.elim (hf i) fun i' hi' => by
            rw [LinearMap.comp_apply]; rw [b.constr_basis]; rw [Function.comp_apply]; rw [← hi']; rw [b'.constr_basis]; rw [Function.comp_apply]; rw [hi']; rw [hgf]; rw [LinearMap.id_apply]
      fun x => congr_arg (fun h : M ->ₗ[R] M => h x) this
    right_inv :=
      have : (constr (M' := M') b R (f ∘ b)).comp (constr (M' := M) b' R (g ∘ b')) = LinearMap.id :=
        b'.ext fun i =>
          Exists.elim (hg i) fun i' hi' => by
            rw [LinearMap.comp_apply]; rw [b'.constr_basis]; rw [Function.comp_apply]; rw [← hi']; rw [b.constr_basis]; rw [Function.comp_apply]; rw [hi']; rw [hfg]; rw [LinearMap.id_apply]
      fun x => congr_arg (fun h : M' ->ₗ[R] M' => h x) this }

@[simp]

中文:
定义 equiv'
  签名: (f : M -> M') (g : M' -> M) (hf : 对任意 i, f (b i) in range b') (hg : 对任意 i, g (b' i) in range b)
  定义体: { constr (M' := M') b R (f ∘ b) with
    invFun := constr (M' := M) b' R (g ∘ b')
    left_inv :=
      have : (constr (M' := M) b' R (g ∘ b')).comp (constr (M' := M') b R (f ∘ b)) = LinearMap.id :=
        b.ext fun i =>
          Exists.elim (hf i) fun i' hi' => by
            rw [LinearMap.comp_apply]; rw [b.constr_basis]; rw [Function.comp_apply]; rw [← hi']; rw [b'.constr_basis]; rw [Function.comp_apply]; rw [hi']; rw [hgf]; rw [LinearMap.id_apply]
      fun x => congr_arg (fun h : M ->ₗ[R] M => h x) this
    right_inv :=
      have : (constr (M' := M') b R (f ∘ b)).comp (constr (M' := M) b' R (g ∘ b')) = LinearMap.id :=
        b'.ext fun i =>
          Exists.elim (hg i) fun i' hi' => by
            rw [LinearMap.comp_apply]; rw [b'.constr_basis]; rw [Function.comp_apply]; rw [← hi']; rw [b.constr_basis]; rw [Function.comp_apply]; rw [hi']; rw [hfg]; rw [LinearMap.id_apply]
      fun x => congr_arg (fun h : M' ->ₗ[R] M' => h x) this }

@[simp]

Depends on / 依赖: Exists, Exists.elim, Function, Function.comp_apply, LinearMap, LinearMap.comp_apply, LinearMap.id, LinearMap.id_apply, b.constr_basis, b.ext, comp_apply, congr_arg, constr, constr_basis, id_apply, invFun, left_inv, right_inv
-/
def equiv' (f : M -> M') (g : M' -> M) (hf : forall i, f (b i) in range b') (hg : forall i, g (b' i) in range b)
    (hgf : forall i, g (f (b i)) = b i) (hfg : forall i, f (g (b' i)) = b' i) : M ≃ₗ[R] M' :=
  { constr (M' := M') b R (f ∘ b) with
    invFun := constr (M' := M) b' R (g ∘ b')
    left_inv :=
      have : (constr (M' := M) b' R (g ∘ b')).comp (constr (M' := M') b R (f ∘ b)) = LinearMap.id :=
        b.ext fun i =>
          Exists.elim (hf i) fun i' hi' => by
            rw [LinearMap.comp_apply]; rw [b.constr_basis]; rw [Function.comp_apply]; rw [← hi']; rw [b'.constr_basis]; rw [Function.comp_apply]; rw [hi']; rw [hgf]; rw [LinearMap.id_apply]
      fun x => congr_arg (fun h : M ->ₗ[R] M => h x) this
    right_inv :=
      have : (constr (M' := M') b R (f ∘ b)).comp (constr (M' := M) b' R (g ∘ b')) = LinearMap.id :=
        b'.ext fun i =>
          Exists.elim (hg i) fun i' hi' => by
            rw [LinearMap.comp_apply]; rw [b'.constr_basis]; rw [Function.comp_apply]; rw [← hi']; rw [b.constr_basis]; rw [Function.comp_apply]; rw [hi']; rw [hfg]; rw [LinearMap.id_apply]
      fun x => congr_arg (fun h : M' ->ₗ[R] M' => h x) this }

@[simp]
/--
theorem `equiv'_apply` / 定理 `equiv'_apply`

English:
theorem equiv'_apply
  given: (f : M -> M') (g : M' -> M) (hf hg hgf hfg) (i : ι)
  proof: b.constr_basis R _ _

@[simp]

中文:
定理 equiv'_apply
  条件: (f : M -> M') (g : M' -> M) (hf hg hgf hfg) (i : ι)
  证明: b.constr_basis R _ _

@[simp]
-/
theorem equiv'_apply (f : M -> M') (g : M' -> M) (hf hg hgf hfg) (i : ι) :
    b.equiv' b' f g hf hg hgf hfg (b i) = f (b i) :=
  b.constr_basis R _ _

@[simp]
/--
theorem `equiv'_symm_apply` / 定理 `equiv'_symm_apply`

English:
theorem equiv'_symm_apply
  given: (f : M -> M') (g : M' -> M) (hf hg hgf hfg) (i : ι')
  proof: b'.constr_basis R _ _

中文:
定理 equiv'_symm_apply
  条件: (f : M -> M') (g : M' -> M) (hf hg hgf hfg) (i : ι')
  证明: b'.constr_basis R _ _
-/
theorem equiv'_symm_apply (f : M -> M') (g : M' -> M) (hf hg hgf hfg) (i : ι') :
    (b.equiv' b' f g hf hg hgf hfg).symm (b' i) = g (b' i) :=
  b'.constr_basis R _ _

set_option backward.isDefEq.respectTransparency false in
/--
theorem `sum_repr_mul_repr` / 定理 `sum_repr_mul_repr`

English:
theorem sum_repr_mul_repr
  given: {ι'} [Fintype ι'] (b' : Basis ι' R M) (x : M) (i : ι)
  proof: by
  conv_rhs => rw [← b'.sum_repr x]
  simp_rw [map_sum, map_smul, Finset.sum_apply']
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finsupp.smul_apply]; rw [smul_eq_mul]; rw [mul_comm]

中文:
定理 sum_repr_mul_repr
  条件: {ι'} [有限类型 ι'] (b' : 基 ι' R M) (x : M) (i : ι)
  证明: by
  conv_rhs => rw [← b'.sum_repr x]
  simp_rw [map_sum, map_smul, Finset.sum_apply']
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finsupp.smul_apply]; rw [smul_eq_mul]; rw [mul_comm]

Depends on / 依赖: Finset, Finset.sum_apply, Finset.sum_congr, Finsupp, Finsupp.smul_apply, conv_rhs, map_smul, map_sum, mul_comm, simp_rw, smul_apply, smul_eq_mul, sum_apply, sum_congr, sum_repr
-/
theorem sum_repr_mul_repr {ι'} [Fintype ι'] (b' : Basis ι' R M) (x : M) (i : ι) :
    (∑ j : ι', b.repr (b' j) i * b'.repr x j) = b.repr x i := by
  conv_rhs => rw [← b'.sum_repr x]
  simp_rw [map_sum, map_smul, Finset.sum_apply']
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finsupp.smul_apply]; rw [smul_eq_mul]; rw [mul_comm]

end CommSemiring

end Equiv

section Coord

variable (i : ι)

/-- `b.coord i` is the linear function giving the `i`-th coordinate of a vector
with respect to the basis `b`.

`b.coord i` is an element of the dual space. In particular, for
finite-dimensional spaces it is the `ι`th basis vector of the dual space.
-/
@[simps!]
/--
Definition of `coord` / `coord` 的定义

English:
definition coord
  signature: : M ->ₗ[R] R
  body: Finsupp.lapply i ∘ₗ ↑b.repr

中文:
定义 coord
  签名: : M ->ₗ[R] R
  定义体: Finsupp.lapply i ∘ₗ ↑b.repr

Depends on / 依赖: Finsupp, Finsupp.lapply, b.repr, lapply
-/
def coord : M ->ₗ[R] R :=
  Finsupp.lapply i ∘ₗ ↑b.repr

/--
theorem `forall_coord_eq_zero_iff` / 定理 `forall_coord_eq_zero_iff`

English:
theorem forall_coord_eq_zero_iff
  given: {x : M}
  statement: (forall i, b.coord i x = 0) ↔ x = 0
  proof: Iff.trans (by simp only [b.coord_apply, DFunLike.ext_iff, Finsupp.zero_apply])
    b.repr.map_eq_zero_iff

中文:
定理 对任意_coord_eq_zero_iff
  条件: {x : M}
  结论: (对任意 i, b.coord i x = 0) ↔ x = 0
  证明: Iff.trans (by simp only [b.coord_apply, DFunLike.ext_iff, Finsupp.zero_apply])
    b.repr.map_eq_zero_iff

Depends on / 依赖: DFunLike, DFunLike.ext_iff, Finsupp, Finsupp.zero_apply, Iff.trans, b.coord_apply, b.repr.map_eq_zero_iff, coord_apply, ext_iff, map_eq_zero_iff, zero_apply
-/
theorem forall_coord_eq_zero_iff {x : M} : (forall i, b.coord i x = 0) ↔ x = 0 :=
  Iff.trans (by simp only [b.coord_apply, DFunLike.ext_iff, Finsupp.zero_apply])
    b.repr.map_eq_zero_iff

/--
Definition of `sumCoords` / `sumCoords` 的定义

English:
definition sumCoords
  signature: : M ->ₗ[R] R
  body: (Finsupp.lsum Nat fun _ => LinearMap.id) ∘ₗ (b.repr : M ->ₗ[R] ι ->₀ R)

@[simp]

中文:
定义 sumCoords
  签名: : M ->ₗ[R] R
  定义体: (Finsupp.lsum Nat fun _ => LinearMap.id) ∘ₗ (b.repr : M ->ₗ[R] ι ->₀ R)

@[simp]

Depends on / 依赖: Finsupp, Finsupp.lsum, LinearMap, LinearMap.id, b.repr
-/
noncomputable def sumCoords : M ->ₗ[R] R :=
  (Finsupp.lsum Nat fun _ => LinearMap.id) ∘ₗ (b.repr : M ->ₗ[R] ι ->₀ R)

@[simp]
/--
theorem `coe_sumCoords` / 定理 `coe_sumCoords`

English:
theorem coe_sumCoords
  statement: (b.sumCoords : M -> R) = fun m => (b.repr m).sum fun _ => id
  proof: rfl

@[simp high]

中文:
定理 coe_sumCoords
  结论: (b.sumCoords : M -> R) = fun m => (b.repr m).求和 fun _ => id
  证明: rfl

@[simp high]
-/
theorem coe_sumCoords : (b.sumCoords : M -> R) = fun m => (b.repr m).sum fun _ => id :=
  rfl

@[simp high]
/--
theorem `coe_sumCoords_of_fintype` / 定理 `coe_sumCoords_of_fintype`

English:
theorem coe_sumCoords_of_fintype
  given: [Fintype ι]
  statement: (b.sumCoords : M -> R) = ∑ i, b.coord i
  proof: by
  ext m
  simp only [sumCoords, Finsupp.sum_fintype, LinearMap.id_coe, LinearEquiv.coe_coe, coord_apply,
    id, Fintype.sum_apply, imp_true_iff, Finsupp.coe_lsum, LinearMap.coe_comp, comp_apply,
    LinearMap.coe_sum]

@[simp]

中文:
定理 coe_sumCoords_of_fintype
  条件: [有限类型 ι]
  结论: (b.sumCoords : M -> R) = ∑ i, b.coord i
  证明: by
  ext m
  simp only [sumCoords, Finsupp.sum_fintype, LinearMap.id_coe, LinearEquiv.coe_coe, coord_apply,
    id, Fintype.sum_apply, imp_true_iff, Finsupp.coe_lsum, LinearMap.coe_comp, comp_apply,
    LinearMap.coe_sum]

@[simp]

Depends on / 依赖: Finsupp, Finsupp.coe_lsum, Finsupp.sum_fintype, Fintype, Fintype.sum_apply, LinearEquiv, LinearEquiv.coe_coe, LinearMap, LinearMap.coe_comp, LinearMap.coe_sum, LinearMap.id_coe, coe_coe, coe_comp, coe_lsum, coe_sum, comp_apply, coord_apply, id_coe, imp_true_iff, sumCoords
-/
theorem coe_sumCoords_of_fintype [Fintype ι] : (b.sumCoords : M -> R) = ∑ i, b.coord i := by
  ext m
  simp only [sumCoords, Finsupp.sum_fintype, LinearMap.id_coe, LinearEquiv.coe_coe, coord_apply,
    id, Fintype.sum_apply, imp_true_iff, Finsupp.coe_lsum, LinearMap.coe_comp, comp_apply,
    LinearMap.coe_sum]

@[simp]
/--
theorem `sumCoords_self_apply` / 定理 `sumCoords_self_apply`

English:
theorem sumCoords_self_apply
  statement: b.sumCoords (b i) = 1
  proof: by
  simp only [Basis.sumCoords, LinearMap.id_coe, LinearEquiv.coe_coe, id, Basis.repr_self,
    Function.comp_apply, Finsupp.coe_lsum, LinearMap.coe_comp, Finsupp.sum_single_index]

中文:
定理 sumCoords_self_apply
  结论: b.sumCoords (b i) = 1
  证明: by
  simp only [Basis.sumCoords, LinearMap.id_coe, LinearEquiv.coe_coe, id, Basis.repr_self,
    Function.comp_apply, Finsupp.coe_lsum, LinearMap.coe_comp, Finsupp.sum_single_index]

Depends on / 依赖: Basis.repr_self, Basis.sumCoords, Finsupp, Finsupp.coe_lsum, Finsupp.sum_single_index, Function, Function.comp_apply, LinearEquiv, LinearEquiv.coe_coe, LinearMap, LinearMap.coe_comp, LinearMap.id_coe, coe_coe, coe_comp, coe_lsum, comp_apply, id_coe, repr_self, sumCoords, sum_single_index
-/
theorem sumCoords_self_apply : b.sumCoords (b i) = 1 := by
  simp only [Basis.sumCoords, LinearMap.id_coe, LinearEquiv.coe_coe, id, Basis.repr_self,
    Function.comp_apply, Finsupp.coe_lsum, LinearMap.coe_comp, Finsupp.sum_single_index]

/--
theorem `dvd_coord_smul` / 定理 `dvd_coord_smul`

English:
theorem dvd_coord_smul
  given: (i : ι) (m : M) (r : R)
  statement: r ∣ b.coord i (r • m)
  proof: ⟨b.coord i m, by simp⟩

中文:
定理 dvd_coord_smul
  条件: (i : ι) (m : M) (r : R)
  结论: r ∣ b.coord i (r • m)
  证明: ⟨b.coord i m, by simp⟩

Depends on / 依赖: b.coord
-/
theorem dvd_coord_smul (i : ι) (m : M) (r : R) : r ∣ b.coord i (r • m) :=
  ⟨b.coord i m, by simp⟩

/--
theorem `coord_repr_symm` / 定理 `coord_repr_symm`

English:
theorem coord_repr_symm
  given: (b : Basis ι R M) (i : ι) (f : ι ->₀ R)
  proof: by
  simp only [repr_symm_apply, coord_apply, repr_linearCombination]

中文:
定理 coord_repr_symm
  条件: (b : 基 ι R M) (i : ι) (f : ι ->₀ R)
  证明: by
  simp only [repr_symm_apply, coord_apply, repr_linearCombination]

Depends on / 依赖: coord_apply, repr_linearCombination, repr_symm_apply
-/
theorem coord_repr_symm (b : Basis ι R M) (i : ι) (f : ι ->₀ R) :
    b.coord i (b.repr.symm f) = f i := by
  simp only [repr_symm_apply, coord_apply, repr_linearCombination]

/--
theorem `coe_sumCoords_eq_finsum` / 定理 `coe_sumCoords_eq_finsum`

English:
theorem coe_sumCoords_eq_finsum
  statement: (b.sumCoords : M -> R) = fun m => ∑ᶠ i, b.coord i m
  proof: by
  ext m
  simp only [Basis.sumCoords, Basis.coord, Finsupp.lapply_apply, LinearMap.id_coe,
    LinearEquiv.coe_coe, Function.comp_apply, Finsupp.coe_lsum, LinearMap.coe_comp,
    finsum_eq_sum _ (b.repr m).hasFiniteSupport, Finsupp.sum, Finset.finite_toSet_toFinset, id,
    Finsupp.fun_support_eq]

中文:
定理 coe_sumCoords_eq_finsum
  结论: (b.sumCoords : M -> R) = fun m => ∑ᶠ i, b.coord i m
  证明: by
  ext m
  simp only [Basis.sumCoords, Basis.coord, Finsupp.lapply_apply, LinearMap.id_coe,
    LinearEquiv.coe_coe, Function.comp_apply, Finsupp.coe_lsum, LinearMap.coe_comp,
    finsum_eq_sum _ (b.repr m).hasFiniteSupport, Finsupp.sum, Finset.finite_toSet_toFinset, id,
    Finsupp.fun_support_eq]

Depends on / 依赖: Basis.coord, Basis.sumCoords, Finset, Finset.finite_toSet_toFinset, Finsupp, Finsupp.coe_lsum, Finsupp.fun_support_eq, Finsupp.lapply_apply, Finsupp.sum, Function, Function.comp_apply, LinearEquiv, LinearEquiv.coe_coe, LinearMap, LinearMap.coe_comp, LinearMap.id_coe, b.repr, coe_coe, coe_comp, coe_lsum
-/
theorem coe_sumCoords_eq_finsum : (b.sumCoords : M -> R) = fun m => ∑ᶠ i, b.coord i m := by
  ext m
  simp only [Basis.sumCoords, Basis.coord, Finsupp.lapply_apply, LinearMap.id_coe,
    LinearEquiv.coe_coe, Function.comp_apply, Finsupp.coe_lsum, LinearMap.coe_comp,
    finsum_eq_sum _ (b.repr m).hasFiniteSupport, Finsupp.sum, Finset.finite_toSet_toFinset, id,
    Finsupp.fun_support_eq]

variable (e : ι ≃ ι')

@[simp]
/--
theorem `sumCoords_reindex` / 定理 `sumCoords_reindex`

English:
theorem sumCoords_reindex
  statement: (b.reindex e).sumCoords = b.sumCoords
  proof: by
  ext x
  simp only [coe_sumCoords, repr_reindex]
  exact Finsupp.sum_mapDomain_index (fun _ => rfl) fun _ _ _ => rfl

中文:
定理 sumCoords_reindex
  结论: (b.reindex e).sumCoords = b.sumCoords
  证明: by
  ext x
  simp only [coe_sumCoords, repr_reindex]
  exact Finsupp.sum_mapDomain_index (fun _ => rfl) fun _ _ _ => rfl

Depends on / 依赖: Finsupp, Finsupp.sum_mapDomain_index, coe_sumCoords, repr_reindex, sum_mapDomain_index
-/
theorem sumCoords_reindex : (b.reindex e).sumCoords = b.sumCoords := by
  ext x
  simp only [coe_sumCoords, repr_reindex]
  exact Finsupp.sum_mapDomain_index (fun _ => rfl) fun _ _ _ => rfl

variable (S : Type*) [Semiring S] [Module S M']
variable [SMulCommClass R S M']

/--
theorem `coord_equivFun_symm` / 定理 `coord_equivFun_symm`

English:
theorem coord_equivFun_symm
  given: [Finite ι] (b : Basis ι R M) (i : ι) (f : ι -> R)
  proof: b.coord_repr_symm i (Finsupp.equivFunOnFinite.symm f)

中文:
定理 coord_equivFun_symm
  条件: [有限 ι] (b : 基 ι R M) (i : ι) (f : ι -> R)
  证明: b.coord_repr_symm i (Finsupp.equivFunOnFinite.symm f)

Depends on / 依赖: Finsupp, Finsupp.equivFunOnFinite.symm, b.coord_repr_symm, coord_repr_symm, equivFunOnFinite
-/
theorem coord_equivFun_symm [Finite ι] (b : Basis ι R M) (i : ι) (f : ι -> R) :
    b.coord i (b.equivFun.symm f) = f i :=
  b.coord_repr_symm i (Finsupp.equivFunOnFinite.symm f)

end Coord

end Basis

end Module
