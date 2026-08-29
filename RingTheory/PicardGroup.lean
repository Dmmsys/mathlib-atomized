/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.CategoryTheory.Monoidal.Skeleton
public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.LinearDisjoint
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.UniqueFactorizationDomain.ClassGroup

/-!
# The Picard group of a commutative ring

This file defines the Picard group `CommRing.Pic R` of a commutative ring `R` as the type of
invertible `R`-modules (in the sense that `M` is invertible if there exists another `R`-module
`N` such that `M ⊗[R] N ≃ₗ[R] R`) up to isomorphism, equipped with tensor product as multiplication.

## Main definition

- `Module.Invertible R M` says that the canonical map `Mᵛ ⊗[R] M → R` is an isomorphism.
  To show that `M` is invertible, it suffices to provide an arbitrary `R`-module `N`
  and an isomorphism `N ⊗[R] M ≃ₗ[R] R`, see `Module.Invertible.right`.

- `ClassGroup.equivPic`: the class group of a domain is isomorphic to the Picard group.

## Main results

- An invertible module is finite and projective (provided as instances).

- `Module.Invertible.free_iff_linearEquiv`: an invertible module is free iff it is isomorphic to
  the ring, i.e. its class is trivial in the Picard group.

- `Submodule.ker_unitsToPic`, `Submodule.range_unitsToPic`: exactness of the sequence
  `1 → Rˣ → Aˣ → (Submodule R A)ˣ → Pic R → Pic A` at the last two spots.
  See Theorem 2.4 in [RobertsSingh1993] or Exercise I.3.7(iv) and Proposition I.3.5 in [Weibel2013].

## References

- https://qchu.wordpress.com/2014/10/19/the-picard-groups/
- https://mathoverflow.net/questions/13768/what-is-the-right-definition-of-the-picard-group-of-a-commutative-ring
- https://mathoverflow.net/questions/375725/picard-group-vs-class-group
- [Weibel2013], https://sites.math.rutgers.edu/~weibel/Kbook/Kbook.I.pdf
- [Stacks: Picard groups of rings](https://stacks.math.columbia.edu/tag/0AFW)

## TODO

Show:
- Invertible modules over a commutative ring have the same cardinality as the ring.

- Establish other characterizations of invertible modules, e.g. they are modules that
  become free of rank one when localized at every prime ideal.
  See [Stacks: Finite projective modules](https://stacks.math.columbia.edu/tag/00NX).
- Connect to invertible sheaves on `Spec R`. More generally, connect projective `R`-modules of
  constant finite rank to locally free sheaves on `Spec R`.
- Exhibit isomorphism with sheaf cohomology `H¹(Spec R, 𝓞ˣ)`.
-/

@[expose] public section

open TensorProduct

universe u v

variable (R : Type u) (M : Type v) (N P Q A : Type*) [CommSemiring R]
variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] [AddCommMonoid Q]
variable [Module R M] [Module R N] [Module R P] [Module R Q]

namespace Module

/--
Definition of `Invertible` / `Invertible` 的定义

English:
class Invertible
  parameters: : Prop where
  axioms and operations (1):
    - bijective : Function.Bijective (contractLeft R M)

中文:
类 可逆
  参数: : 命题 where
  公理与运算 (1 个):
    - bijective : 函数.双射 (contractLeft R M)
-/
protected class Invertible : Prop where
  bijective : Function.Bijective (contractLeft R M)

namespace Invertible

/--
Definition of `linearEquiv` / `linearEquiv` 的定义

English:
definition linearEquiv
  signature: [Module.Invertible R M]
  body: .ofBijective _ Invertible.bijective

中文:
定义 linearEquiv
  签名: [模.可逆 R M]
  定义体: .ofBijective _ Invertible.bijective

Depends on / 依赖: Invertible, Invertible.bijective, bijective, ofBijective
-/
noncomputable def linearEquiv [Module.Invertible R M] : Module.Dual R M otimes[R] M ≃ₗ[R] R :=
  .ofBijective _ Invertible.bijective

variable {R M N}

section LinearEquiv

variable (e : M otimes[R] N ≃ₗ[R] R)

/--
Definition of `leftCancelEquiv` / `leftCancelEquiv` 的定义

English:
abbreviation leftCancelEquiv
  signature: : M otimes[R] (N otimes[R] P) ≃ₗ[R] P
  body: (TensorProduct.assoc R M N P).symm ≪≫ₗ e.rTensor P ≪≫ₗ TensorProduct.lid R P

中文:
缩写 leftCancelEquiv
  签名: : M otimes[R] (N otimes[R] P) ≃ₗ[R] P
  定义体: (TensorProduct.assoc R M N P).symm ≪≫ₗ e.rTensor P ≪≫ₗ TensorProduct.lid R P

Depends on / 依赖: TensorProduct, TensorProduct.assoc, TensorProduct.lid, e.rTensor, rTensor
-/
noncomputable abbrev leftCancelEquiv : M otimes[R] (N otimes[R] P) ≃ₗ[R] P :=
  (TensorProduct.assoc R M N P).symm ≪≫ₗ e.rTensor P ≪≫ₗ TensorProduct.lid R P

/--
Definition of `rightCancelEquiv` / `rightCancelEquiv` 的定义

English:
abbreviation rightCancelEquiv
  signature: : (P otimes[R] M) otimes[R] N ≃ₗ[R] P
  body: TensorProduct.assoc R P M N ≪≫ₗ e.lTensor P ≪≫ₗ TensorProduct.rid R P

中文:
缩写 rightCancelEquiv
  签名: : (P otimes[R] M) otimes[R] N ≃ₗ[R] P
  定义体: TensorProduct.assoc R P M N ≪≫ₗ e.lTensor P ≪≫ₗ TensorProduct.rid R P

Depends on / 依赖: TensorProduct, TensorProduct.assoc, TensorProduct.rid, e.lTensor, lTensor
-/
noncomputable abbrev rightCancelEquiv : (P otimes[R] M) otimes[R] N ≃ₗ[R] P :=
  TensorProduct.assoc R P M N ≪≫ₗ e.lTensor P ≪≫ₗ TensorProduct.rid R P

variable {P Q} in
/--
theorem `leftCancelEquiv_comp_lTensor_comp_symm` / 定理 `leftCancelEquiv_comp_lTensor_comp_symm`

English:
theorem leftCancelEquiv_comp_lTensor_comp_symm
  given: (f : P ->ₗ[R] Q)
  proof: by
  rw [← LinearMap.comp_assoc]; rw [LinearEquiv.comp_toLinearMap_symm_eq]; ext; simp

中文:
定理 leftCancelEquiv_comp_lTensor_comp_symm
  条件: (f : P ->ₗ[R] Q)
  证明: by
  rw [← LinearMap.comp_assoc]; rw [LinearEquiv.comp_toLinearMap_symm_eq]; ext; simp

Depends on / 依赖: LinearEquiv, LinearEquiv.comp_toLinearMap_symm_eq, LinearMap, LinearMap.comp_assoc, comp_assoc, comp_toLinearMap_symm_eq
-/
theorem leftCancelEquiv_comp_lTensor_comp_symm (f : P ->ₗ[R] Q) :
    leftCancelEquiv Q e ∘ₗ (f.lTensor N).lTensor M ∘ₗ (leftCancelEquiv P e).symm = f := by
  rw [← LinearMap.comp_assoc]; rw [LinearEquiv.comp_toLinearMap_symm_eq]; ext; simp

variable {P Q} in
/--
theorem `rightCancelEquiv_comp_rTensor_comp_symm` / 定理 `rightCancelEquiv_comp_rTensor_comp_symm`

English:
theorem rightCancelEquiv_comp_rTensor_comp_symm
  given: (f : P ->ₗ[R] Q)
  proof: by
  rw [← LinearMap.comp_assoc]; rw [LinearEquiv.comp_toLinearMap_symm_eq]; ext; simp

中文:
定理 rightCancelEquiv_comp_rTensor_comp_symm
  条件: (f : P ->ₗ[R] Q)
  证明: by
  rw [← LinearMap.comp_assoc]; rw [LinearEquiv.comp_toLinearMap_symm_eq]; ext; simp

Depends on / 依赖: LinearEquiv, LinearEquiv.comp_toLinearMap_symm_eq, LinearMap, LinearMap.comp_assoc, comp_assoc, comp_toLinearMap_symm_eq
-/
theorem rightCancelEquiv_comp_rTensor_comp_symm (f : P ->ₗ[R] Q) :
    rightCancelEquiv Q e ∘ₗ (f.rTensor M).rTensor N ∘ₗ (rightCancelEquiv P e).symm = f := by
  rw [← LinearMap.comp_assoc]; rw [LinearEquiv.comp_toLinearMap_symm_eq]; ext; simp

/--
Definition of `rTensorInv` / `rTensorInv` 的定义

English:
definition rTensorInv
  signature: : (P otimes[R] M ->ₗ[R] Q otimes[R] M) ->ₗ[R] (P ->ₗ[R] Q)
  body: ((rightCancelEquiv Q e).congrRight ≪≫ₗ (rightCancelEquiv P e).congrLeft _ R) ∘ₗ
    LinearMap.rTensorHom N

中文:
定义 rTensorInv
  签名: : (P otimes[R] M ->ₗ[R] Q otimes[R] M) ->ₗ[R] (P ->ₗ[R] Q)
  定义体: ((rightCancelEquiv Q e).congrRight ≪≫ₗ (rightCancelEquiv P e).congrLeft _ R) ∘ₗ
    LinearMap.rTensorHom N

Depends on / 依赖: LinearMap, LinearMap.rTensorHom, congrLeft, congrRight, rTensorHom, rightCancelEquiv
-/
noncomputable def rTensorInv : (P otimes[R] M ->ₗ[R] Q otimes[R] M) ->ₗ[R] (P ->ₗ[R] Q) :=
  ((rightCancelEquiv Q e).congrRight ≪≫ₗ (rightCancelEquiv P e).congrLeft _ R) ∘ₗ
    LinearMap.rTensorHom N

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `rTensorInv_leftInverse` / 定理 `rTensorInv_leftInverse`

English:
theorem rTensorInv_leftInverse
  statement: Function.LeftInverse (rTensorInv P Q e) (.rTensorHom M)
  proof: fun _ => by
    simp_rw [rTensorInv, LinearEquiv.coe_trans, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
    rw [← LinearEquiv.eq_symm_apply]
    ext; simp [LinearEquiv.congrLeft, LinearEquiv.congrRight, LinearEquiv.arrowCongrAddEquiv]

中文:
定理 rTensorInv_leftInverse
  结论: 函数.左逆 (rTensorInv P Q e) (.rTensorHom M)
  证明: fun _ => by
    simp_rw [rTensorInv, LinearEquiv.coe_trans, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
    rw [← LinearEquiv.eq_symm_apply]
    ext; simp [LinearEquiv.congrLeft, LinearEquiv.congrRight, LinearEquiv.arrowCongrAddEquiv]

Depends on / 依赖: LinearEquiv, LinearEquiv.arrowCongrAddEquiv, LinearEquiv.coe_toLinearMap, LinearEquiv.coe_trans, LinearEquiv.congrLeft, LinearEquiv.congrRight, LinearEquiv.eq_symm_apply, LinearMap, LinearMap.comp_apply, arrowCongrAddEquiv, coe_toLinearMap, coe_trans, comp_apply, congrLeft, congrRight, eq_symm_apply, rTensorInv, simp_rw
-/
theorem rTensorInv_leftInverse : Function.LeftInverse (rTensorInv P Q e) (.rTensorHom M) :=
  fun _ => by
    simp_rw [rTensorInv, LinearEquiv.coe_trans, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
    rw [← LinearEquiv.eq_symm_apply]
    ext; simp [LinearEquiv.congrLeft, LinearEquiv.congrRight, LinearEquiv.arrowCongrAddEquiv]

/--
theorem `rTensorInv_injective` / 定理 `rTensorInv_injective`

English:
theorem rTensorInv_injective
  statement: Function.Injective (rTensorInv P Q e)
  proof: by
  simpa [rTensorInv] using (rTensorInv_leftInverse _ _ <| TensorProduct.comm R N M ≪≫ₗ e).injective

中文:
定理 rTensorInv_injective
  结论: 函数.单射 (rTensorInv P Q e)
  证明: by
  simpa [rTensorInv] using (rTensorInv_leftInverse _ _ <| TensorProduct.comm R N M ≪≫ₗ e).injective

Depends on / 依赖: TensorProduct, TensorProduct.comm, injective, rTensorInv, rTensorInv_leftInverse
-/
theorem rTensorInv_injective : Function.Injective (rTensorInv P Q e) := by
  simpa [rTensorInv] using (rTensorInv_leftInverse _ _ <| TensorProduct.comm R N M ≪≫ₗ e).injective

/--
Definition of `rTensorEquiv` / `rTensorEquiv` 的定义

English:
definition rTensorEquiv
  signature: : (P ->ₗ[R] Q) ≃ₗ[R] (P otimes[R] M ->ₗ[R] Q otimes[R] M) where
  body: LinearMap.rTensorHom M
  invFun := rTensorInv P Q e
  left_inv := rTensorInv_leftInverse P Q e
  right_inv _ := rTensorInv_injective P Q e (by rw [LinearMap.toFun_eq_coe, rTensorInv_leftInverse])

中文:
定义 rTensorEquiv
  签名: : (P ->ₗ[R] Q) ≃ₗ[R] (P otimes[R] M ->ₗ[R] Q otimes[R] M) where
  定义体: LinearMap.rTensorHom M
  invFun := rTensorInv P Q e
  left_inv := rTensorInv_leftInverse P Q e
  right_inv _ := rTensorInv_injective P Q e (by rw [LinearMap.toFun_eq_coe, rTensorInv_leftInverse])
-/
@[simps!] noncomputable def rTensorEquiv : (P ->ₗ[R] Q) ≃ₗ[R] (P otimes[R] M ->ₗ[R] Q otimes[R] M) where
  __ := LinearMap.rTensorHom M
  invFun := rTensorInv P Q e
  left_inv := rTensorInv_leftInverse P Q e
  right_inv _ := rTensorInv_injective P Q e (by rw [LinearMap.toFun_eq_coe, rTensorInv_leftInverse])

set_option backward.isDefEq.respectTransparency.types false in
open LinearMap in
/--
theorem `bijective_curry` / 定理 `bijective_curry`

English:
theorem bijective_curry
  statement: Function.Bijective (curry e.toLinearMap)
  proof: by
  have : curry e.toLinearMap = ((TensorProduct.lid R N).congrLeft _ R ≪≫ₗ e.congrRight) ∘ₗ
      rTensorHom N ∘ₗ (ringLmapEquivSelf R R M).symm.toLinearMap := by
    rw [← LinearEquiv.toLinearMap_symm_comp_eq]; ext
    simp [LinearEquiv.congrLeft, LinearEquiv.congrRight, LinearEquiv.arrowCongrAddEquiv]
  simpa [this] using! (rTensorEquiv R M <| TensorProduct.comm R N M ≪≫ₗ e).bijective

中文:
定理 bijective_curry
  结论: 函数.双射 (curry e.toLinearMap)
  证明: by
  have : curry e.toLinearMap = ((TensorProduct.lid R N).congrLeft _ R ≪≫ₗ e.congrRight) ∘ₗ
      rTensorHom N ∘ₗ (ringLmapEquivSelf R R M).symm.toLinearMap := by
    rw [← LinearEquiv.toLinearMap_symm_comp_eq]; ext
    simp [LinearEquiv.congrLeft, LinearEquiv.congrRight, LinearEquiv.arrowCongrAddEquiv]
  simpa [this] using! (rTensorEquiv R M <| TensorProduct.comm R N M ≪≫ₗ e).bijective

Depends on / 依赖: LinearEquiv, LinearEquiv.arrowCongrAddEquiv, LinearEquiv.congrLeft, LinearEquiv.congrRight, LinearEquiv.toLinearMap_symm_comp_eq, TensorProduct, TensorProduct.comm, TensorProduct.lid, arrowCongrAddEquiv, bijective, congrLeft, congrRight, e.congrRight, e.toLinearMap, rTensorEquiv, rTensorHom, ringLmapEquivSelf, symm.toLinearMap, toLinearMap, toLinearMap_symm_comp_eq
-/
theorem bijective_curry : Function.Bijective (curry e.toLinearMap) := by
  have : curry e.toLinearMap = ((TensorProduct.lid R N).congrLeft _ R ≪≫ₗ e.congrRight) ∘ₗ
      rTensorHom N ∘ₗ (ringLmapEquivSelf R R M).symm.toLinearMap := by
    rw [← LinearEquiv.toLinearMap_symm_comp_eq]; ext
    simp [LinearEquiv.congrLeft, LinearEquiv.congrRight, LinearEquiv.arrowCongrAddEquiv]
  simpa [this] using! (rTensorEquiv R M <| TensorProduct.comm R N M ≪≫ₗ e).bijective

/--
Definition of `linearEquivDual` / `linearEquivDual` 的定义

English:
definition linearEquivDual
  signature: : M ≃ₗ[R] Dual R N
  body: .ofBijective _ (bijective_curry e)

include e

中文:
定义 linearEquivDual
  签名: : M ≃ₗ[R] 对偶 R N
  定义体: .ofBijective _ (bijective_curry e)

include e

Depends on / 依赖: bijective_curry, ofBijective
-/
noncomputable def linearEquivDual : M ≃ₗ[R] Dual R N := .ofBijective _ (bijective_curry e)

include e

/--
theorem `right` / 定理 `right`

English:
theorem right
  statement: Module.Invertible R N where
  proof: by
    rw [show contractLeft R N = ((linearEquivDual e).rTensor N).symm ≪≫ₗ e by
      rw [LinearEquiv.coe_trans]; rw [LinearEquiv.eq_comp_toLinearMap_symm]; ext; rfl]
    apply LinearEquiv.bijective

中文:
定理 right
  结论: 模.可逆 R N where
  证明: by
    rw [show contractLeft R N = ((linearEquivDual e).rTensor N).symm ≪≫ₗ e by
      rw [LinearEquiv.coe_trans]; rw [LinearEquiv.eq_comp_toLinearMap_symm]; ext; rfl]
    apply LinearEquiv.bijective
-/
protected theorem right : Module.Invertible R N where
  bijective := by
    rw [show contractLeft R N = ((linearEquivDual e).rTensor N).symm ≪≫ₗ e by
      rw [LinearEquiv.coe_trans]; rw [LinearEquiv.eq_comp_toLinearMap_symm]; ext; rfl]
    apply LinearEquiv.bijective

/--
theorem `left` / 定理 `left`

English:
theorem left
  statement: Module.Invertible R M
  proof: .right (TensorProduct.comm R N M ≪≫ₗ e)

中文:
定理 left
  结论: 模.可逆 R M
  证明: .right (TensorProduct.comm R N M ≪≫ₗ e)
-/
protected theorem left : Module.Invertible R M := .right (TensorProduct.comm R N M ≪≫ₗ e)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module.Invertible R R
  body: .left (TensorProduct.lid R R)

中文:
实例 :
  签名: 模.可逆 R R
  定义体: .left (TensorProduct.lid R R)

Depends on / 依赖: TensorProduct, TensorProduct.lid
-/
instance : Module.Invertible R R := .left (TensorProduct.lid R R)

end LinearEquiv

variable [Module.Invertible R M]

/--
theorem `congr` / 定理 `congr`

English:
theorem congr
  given: (e : M ≃ₗ[R] N)
  statement: Module.Invertible R N
  proof: .right (e.symm.lTensor _ ≪≫ₗ linearEquiv R M)

中文:
定理 congr
  条件: (e : M ≃ₗ[R] N)
  结论: 模.可逆 R N
  证明: .right (e.symm.lTensor _ ≪≫ₗ linearEquiv R M)
-/
protected theorem congr (e : M ≃ₗ[R] N) : Module.Invertible R N :=
  .right (e.symm.lTensor _ ≪≫ₗ linearEquiv R M)

variable (R M N)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module.Invertible R (Dual R M)
  body: .left (linearEquiv R M)

中文:
实例 :
  签名: 模.可逆 R (对偶 R M)
  定义体: .left (linearEquiv R M)

Depends on / 依赖: linearEquiv
-/
instance : Module.Invertible R (Dual R M) := .left (linearEquiv R M)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Module.Invertible
  signature: R N] : Module.Invertible R (M otimes[R] N)
  body: .right (M := Dual R M otimes[R] Dual R N) tensorTensorTensorComm .. ≪≫ₗ
    congr (linearEquiv R M) (linearEquiv R N) ≪≫ₗ TensorProduct.lid R R

中文:
实例 [模.可逆
  签名: R N] : 模.可逆 R (M otimes[R] N)
  定义体: .right (M := Dual R M otimes[R] Dual R N) tensorTensorTensorComm .. ≪≫ₗ
    congr (linearEquiv R M) (linearEquiv R N) ≪≫ₗ TensorProduct.lid R R

Depends on / 依赖: TensorProduct, TensorProduct.lid, linearEquiv, otimes, tensorTensorTensorComm
-/
instance [Module.Invertible R N] : Module.Invertible R (M otimes[R] N) :=
.right (M := Dual R M otimes[R] Dual R N) tensorTensorTensorComm .. ≪≫ₗ
    congr (linearEquiv R M) (linearEquiv R N) ≪≫ₗ TensorProduct.lid R R

/--
theorem `finite_projective` / 定理 `finite_projective`

English:
theorem finite_projective
  statement: Module.Finite R M ∧ Projective R M
  proof: by
  let N := Dual R M
  let e : M otimes[R] N ≃ₗ[R] R := TensorProduct.comm .. ≪≫ₗ linearEquiv R M
  have ⟨S, hS⟩ := TensorProduct.exists_finset (e.symm 1)
  let f : (S ->₀ N) ->ₗ[R] R := Finsupp.lsum R fun i => e.toLinearMap ∘ₗ TensorProduct.mk R M N i.1.1
  have : Function.Surjective f := by
    rw [← LinearMap.range_eq_top]; rw [Ideal.eq_top_iff_one]
    use Finsupp.equivFunOnFinite.symm fun i => i.1.2
    simp_rw [f, Finsupp.coe_lsum]
    rw [Finsupp.sum_fintype _ _ fun _ => map_zero _]
    rwa [e.symm_apply_eq, map_sum, ← Finset.sum_coe_sort, eq_comm] at hS
  have ⟨g, hg⟩ := projective_lifting_property f .id this
  classical
  let aux := finsuppRight R _ M N S ≪≫ₗ Finsupp.mapRange.linearEquiv e
  let f' : (S ->₀ R) ->ₗ[R] M := TensorProduct.rid R M ∘ₗ f.lTensor M ∘ₗ aux.symm
  let g' : M ->ₗ[R] S ->₀ R := aux ∘ₗ g.lTensor M ∘ₗ (TensorProduct.rid R M).symm
  have : Function.Surjective f' := by simpa [f'] using LinearMap.lTensor_surjective _ this
refine ⟨.of_surjective f' this, .of_split g' f' LinearMap.ext fun m => ?_⟩
  simp [f', g', show f (g 1) = 1 from DFunLike.congr_fun hg 1]

中文:
定理 finite_projective
  结论: 模.有限 R M ∧ 投射 R M
  证明: by
  let N := Dual R M
  let e : M otimes[R] N ≃ₗ[R] R := TensorProduct.comm .. ≪≫ₗ linearEquiv R M
  have ⟨S, hS⟩ := TensorProduct.exists_finset (e.symm 1)
  let f : (S ->₀ N) ->ₗ[R] R := Finsupp.lsum R fun i => e.toLinearMap ∘ₗ TensorProduct.mk R M N i.1.1
  have : Function.Surjective f := by
    rw [← LinearMap.range_eq_top]; rw [Ideal.eq_top_iff_one]
    use Finsupp.equivFunOnFinite.symm fun i => i.1.2
    simp_rw [f, Finsupp.coe_lsum]
    rw [Finsupp.sum_fintype _ _ fun _ => map_zero _]
    rwa [e.symm_apply_eq, map_sum, ← Finset.sum_coe_sort, eq_comm] at hS
  have ⟨g, hg⟩ := projective_lifting_property f .id this
  classical
  let aux := finsuppRight R _ M N S ≪≫ₗ Finsupp.mapRange.linearEquiv e
  let f' : (S ->₀ R) ->ₗ[R] M := TensorProduct.rid R M ∘ₗ f.lTensor M ∘ₗ aux.symm
  let g' : M ->ₗ[R] S ->₀ R := aux ∘ₗ g.lTensor M ∘ₗ (TensorProduct.rid R M).symm
  have : Function.Surjective f' := by simpa [f'] using LinearMap.lTensor_surjective _ this
refine ⟨.of_surjective f' this, .of_split g' f' LinearMap.ext fun m => ?_⟩
  simp [f', g', show f (g 1) = 1 from DFunLike.congr_fun hg 1]
-/
private theorem finite_projective : Module.Finite R M ∧ Projective R M := by
  let N := Dual R M
  let e : M otimes[R] N ≃ₗ[R] R := TensorProduct.comm .. ≪≫ₗ linearEquiv R M
  have ⟨S, hS⟩ := TensorProduct.exists_finset (e.symm 1)
  let f : (S ->₀ N) ->ₗ[R] R := Finsupp.lsum R fun i => e.toLinearMap ∘ₗ TensorProduct.mk R M N i.1.1
  have : Function.Surjective f := by
    rw [← LinearMap.range_eq_top]; rw [Ideal.eq_top_iff_one]
    use Finsupp.equivFunOnFinite.symm fun i => i.1.2
    simp_rw [f, Finsupp.coe_lsum]
    rw [Finsupp.sum_fintype _ _ fun _ => map_zero _]
    rwa [e.symm_apply_eq, map_sum, ← Finset.sum_coe_sort, eq_comm] at hS
  have ⟨g, hg⟩ := projective_lifting_property f .id this
  classical
  let aux := finsuppRight R _ M N S ≪≫ₗ Finsupp.mapRange.linearEquiv e
  let f' : (S ->₀ R) ->ₗ[R] M := TensorProduct.rid R M ∘ₗ f.lTensor M ∘ₗ aux.symm
  let g' : M ->ₗ[R] S ->₀ R := aux ∘ₗ g.lTensor M ∘ₗ (TensorProduct.rid R M).symm
  have : Function.Surjective f' := by simpa [f'] using LinearMap.lTensor_surjective _ this
refine ⟨.of_surjective f' this, .of_split g' f' LinearMap.ext fun m => ?_⟩
  simp [f', g', show f (g 1) = 1 from DFunLike.congr_fun hg 1]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module.Finite R M
  body: (finite_projective R M).1

中文:
实例 :
  签名: 模.有限 R M
  定义体: (finite_projective R M).1

Depends on / 依赖: finite_projective
-/
instance : Module.Finite R M := (finite_projective R M).1
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Projective R M
  body: (finite_projective R M).2
example : IsReflexive R M := inferInstance

中文:
实例 :
  签名: 投射 R M
  定义体: (finite_projective R M).2
example : IsReflexive R M := inferInstance

Depends on / 依赖: finite_projective
-/
instance : Projective R M := (finite_projective R M).2
example : IsReflexive R M := inferInstance

section inj_surj_bij

variable {R N P}

/--
theorem `lTensor_injective_iff` / 定理 `lTensor_injective_iff`

English:
theorem lTensor_injective_iff
  given: {f : N ->ₗ[R] P}
  proof: by
  refine ⟨fun h => ?_, Flat.lTensor_preserves_injective_linearMap _⟩
  rw [← leftCancelEquiv_comp_lTensor_comp_symm (linearEquiv R M) f]
  simpa using Flat.lTensor_preserves_injective_linearMap _ h

中文:
定理 lTensor_injective_iff
  条件: {f : N ->ₗ[R] P}
  证明: by
  refine ⟨fun h => ?_, Flat.lTensor_preserves_injective_linearMap _⟩
  rw [← leftCancelEquiv_comp_lTensor_comp_symm (linearEquiv R M) f]
  simpa using Flat.lTensor_preserves_injective_linearMap _ h

Depends on / 依赖: Flat.lTensor_preserves_injective_linearMap, lTensor_preserves_injective_linearMap, leftCancelEquiv_comp_lTensor_comp_symm, linearEquiv
-/
theorem lTensor_injective_iff {f : N ->ₗ[R] P} :
    Function.Injective (f.lTensor M) ↔ Function.Injective f := by
  refine ⟨fun h => ?_, Flat.lTensor_preserves_injective_linearMap _⟩
  rw [← leftCancelEquiv_comp_lTensor_comp_symm (linearEquiv R M) f]
  simpa using Flat.lTensor_preserves_injective_linearMap _ h

/--
theorem `rTensor_injective_iff` / 定理 `rTensor_injective_iff`

English:
theorem rTensor_injective_iff
  given: {f : N ->ₗ[R] P}
  proof: by
  rw [← LinearMap.lTensor_inj_iff_rTensor_inj]; rw [lTensor_injective_iff]

中文:
定理 rTensor_injective_iff
  条件: {f : N ->ₗ[R] P}
  证明: by
  rw [← LinearMap.lTensor_inj_iff_rTensor_inj]; rw [lTensor_injective_iff]

Depends on / 依赖: LinearMap, LinearMap.lTensor_inj_iff_rTensor_inj, lTensor_inj_iff_rTensor_inj, lTensor_injective_iff
-/
theorem rTensor_injective_iff {f : N ->ₗ[R] P} :
    Function.Injective (f.rTensor M) ↔ Function.Injective f := by
  rw [← LinearMap.lTensor_inj_iff_rTensor_inj]; rw [lTensor_injective_iff]

/--
theorem `lTensor_surjective_iff` / 定理 `lTensor_surjective_iff`

English:
theorem lTensor_surjective_iff
  given: {f : N ->ₗ[R] P}
  proof: by
  refine ⟨fun h => ?_, LinearMap.lTensor_surjective _⟩
  rw [← leftCancelEquiv_comp_lTensor_comp_symm (linearEquiv R M) f]
  simpa using LinearMap.lTensor_surjective _ h

中文:
定理 lTensor_surjective_iff
  条件: {f : N ->ₗ[R] P}
  证明: by
  refine ⟨fun h => ?_, LinearMap.lTensor_surjective _⟩
  rw [← leftCancelEquiv_comp_lTensor_comp_symm (linearEquiv R M) f]
  simpa using LinearMap.lTensor_surjective _ h

Depends on / 依赖: LinearMap, LinearMap.lTensor_surjective, lTensor_surjective, leftCancelEquiv_comp_lTensor_comp_symm, linearEquiv
-/
theorem lTensor_surjective_iff {f : N ->ₗ[R] P} :
    Function.Surjective (f.lTensor M) ↔ Function.Surjective f := by
  refine ⟨fun h => ?_, LinearMap.lTensor_surjective _⟩
  rw [← leftCancelEquiv_comp_lTensor_comp_symm (linearEquiv R M) f]
  simpa using LinearMap.lTensor_surjective _ h

/--
theorem `rTensor_surjective_iff` / 定理 `rTensor_surjective_iff`

English:
theorem rTensor_surjective_iff
  given: {f : N ->ₗ[R] P}
  proof: by
  rw [← LinearMap.lTensor_surj_iff_rTensor_surj]; rw [lTensor_surjective_iff]

中文:
定理 rTensor_surjective_iff
  条件: {f : N ->ₗ[R] P}
  证明: by
  rw [← LinearMap.lTensor_surj_iff_rTensor_surj]; rw [lTensor_surjective_iff]

Depends on / 依赖: LinearMap, LinearMap.lTensor_surj_iff_rTensor_surj, lTensor_surj_iff_rTensor_surj, lTensor_surjective_iff
-/
theorem rTensor_surjective_iff {f : N ->ₗ[R] P} :
    Function.Surjective (f.rTensor M) ↔ Function.Surjective f := by
  rw [← LinearMap.lTensor_surj_iff_rTensor_surj]; rw [lTensor_surjective_iff]

/--
theorem `lTensor_bijective_iff` / 定理 `lTensor_bijective_iff`

English:
theorem lTensor_bijective_iff
  given: {f : N ->ₗ[R] P}
  proof: by
  simp_rw [Function.Bijective, lTensor_injective_iff, lTensor_surjective_iff]

中文:
定理 lTensor_bijective_iff
  条件: {f : N ->ₗ[R] P}
  证明: by
  simp_rw [Function.Bijective, lTensor_injective_iff, lTensor_surjective_iff]

Depends on / 依赖: Bijective, Function, Function.Bijective, lTensor_injective_iff, lTensor_surjective_iff, simp_rw
-/
theorem lTensor_bijective_iff {f : N ->ₗ[R] P} :
    Function.Bijective (f.lTensor M) ↔ Function.Bijective f := by
  simp_rw [Function.Bijective, lTensor_injective_iff, lTensor_surjective_iff]

/--
theorem `rTensor_bijective_iff` / 定理 `rTensor_bijective_iff`

English:
theorem rTensor_bijective_iff
  given: {f : N ->ₗ[R] P}
  proof: by
  simp_rw [Function.Bijective, rTensor_injective_iff, rTensor_surjective_iff]

中文:
定理 rTensor_bijective_iff
  条件: {f : N ->ₗ[R] P}
  证明: by
  simp_rw [Function.Bijective, rTensor_injective_iff, rTensor_surjective_iff]

Depends on / 依赖: Bijective, Function, Function.Bijective, rTensor_injective_iff, rTensor_surjective_iff, simp_rw
-/
theorem rTensor_bijective_iff {f : N ->ₗ[R] P} :
    Function.Bijective (f.rTensor M) ↔ Function.Bijective f := by
  simp_rw [Function.Bijective, rTensor_injective_iff, rTensor_surjective_iff]

end inj_surj_bij

open Finsupp in
variable {R M} in
/--
theorem `free_iff_linearEquiv` / 定理 `free_iff_linearEquiv`

English:
theorem free_iff_linearEquiv
  statement: Free R M ↔ Nonempty (M ≃ₗ[R] R)
  proof: by
  refine ⟨fun _ => ?_, fun ⟨e⟩ => .of_equiv e.symm⟩
  nontriviality R
  have e := (Free.chooseBasis R M).repr
have := card_eq_of_linearEquiv R
    (finsuppTensorFinsupp' .. ≪≫ₗ linearEquivFunOnFinite R R _).symm ≪≫ₗ TensorProduct.congr
      (linearEquivFunOnFinite R R _ ≪≫ₗ llift R R R _ ≪≫ₗ e.dualMap)
      e.symm ≪≫ₗ linearEquiv R M ≪≫ₗ (.symm <| .funUnique Unit R R)
  have : Unique (Free.ChooseBasisIndex R M) :=
    (Fintype.card_eq_one_iff_nonempty_unique.mp (by simpa using this)).some
  exact ⟨e ≪≫ₗ uniqueLinearEquiv R R default⟩

中文:
定理 free_iff_linearEquiv
  结论: 自由 R M ↔ 非空 (M ≃ₗ[R] R)
  证明: by
  refine ⟨fun _ => ?_, fun ⟨e⟩ => .of_equiv e.symm⟩
  nontriviality R
  have e := (Free.chooseBasis R M).repr
have := card_eq_of_linearEquiv R
    (finsuppTensorFinsupp' .. ≪≫ₗ linearEquivFunOnFinite R R _).symm ≪≫ₗ TensorProduct.congr
      (linearEquivFunOnFinite R R _ ≪≫ₗ llift R R R _ ≪≫ₗ e.dualMap)
      e.symm ≪≫ₗ linearEquiv R M ≪≫ₗ (.symm <| .funUnique Unit R R)
  have : Unique (Free.ChooseBasisIndex R M) :=
    (Fintype.card_eq_one_iff_nonempty_unique.mp (by simpa using this)).some
  exact ⟨e ≪≫ₗ uniqueLinearEquiv R R default⟩

Depends on / 依赖: ChooseBasisIndex, Fintype, Fintype.card_eq_one_iff_nonempty_unique.mp, Free.ChooseBasisIndex, Free.chooseBasis, TensorProduct, TensorProduct.congr, Unique, card_eq_of_linearEquiv, card_eq_one_iff_nonempty_unique, chooseBasis, dualMap, e.dualMap, e.symm, finsuppTensorFinsupp, funUnique, linearEquiv, linearEquivFunOnFinite, nontriviality, of_equiv
-/
theorem free_iff_linearEquiv : Free R M ↔ Nonempty (M ≃ₗ[R] R) := by
  refine ⟨fun _ => ?_, fun ⟨e⟩ => .of_equiv e.symm⟩
  nontriviality R
  have e := (Free.chooseBasis R M).repr
have := card_eq_of_linearEquiv R
    (finsuppTensorFinsupp' .. ≪≫ₗ linearEquivFunOnFinite R R _).symm ≪≫ₗ TensorProduct.congr
      (linearEquivFunOnFinite R R _ ≪≫ₗ llift R R R _ ≪≫ₗ e.dualMap)
      e.symm ≪≫ₗ linearEquiv R M ≪≫ₗ (.symm <| .funUnique Unit R R)
  have : Unique (Free.ChooseBasisIndex R M) :=
    (Fintype.card_eq_one_iff_nonempty_unique.mp (by simpa using this)).some
  exact ⟨e ≪≫ₗ uniqueLinearEquiv R R default⟩

/--
theorem `finrank_eq_one` / 定理 `finrank_eq_one`

English:
theorem finrank_eq_one
  given: [Free R M]
  statement: finrank R M = 1
  proof: by
  rw [(free_iff_linearEquiv.mp ‹_›).some.finrank_eq]; rw [CommSemiring.finrank_self]

中文:
定理 finrank_eq_one
  条件: [自由 R M]
  结论: finrank R M = 1
  证明: by
  rw [(free_iff_linearEquiv.mp ‹_›).some.finrank_eq]; rw [CommSemiring.finrank_self]
-/
protected theorem finrank_eq_one [Free R M] : finrank R M = 1 := by
  rw [(free_iff_linearEquiv.mp ‹_›).some.finrank_eq]; rw [CommSemiring.finrank_self]

/--
theorem `rank_eq_one` / 定理 `rank_eq_one`

English:
theorem rank_eq_one
  given: [Free R M]
  statement: Module.rank R M = 1
  proof: rank_eq_one_iff_finrank_eq_one.mpr (Invertible.finrank_eq_one R M)

中文:
定理 rank_eq_one
  条件: [自由 R M]
  结论: 模.rank R M = 1
  证明: rank_eq_one_iff_finrank_eq_one.mpr (Invertible.finrank_eq_one R M)

Depends on / 依赖: Invertible, Invertible.finrank_eq_one, finrank_eq_one, rank_eq_one_iff_finrank_eq_one, rank_eq_one_iff_finrank_eq_one.mpr
-/
theorem rank_eq_one [Free R M] : Module.rank R M = 1 :=
  rank_eq_one_iff_finrank_eq_one.mpr (Invertible.finrank_eq_one R M)

open TensorProduct (comm lid) in
/--
theorem `toModuleEnd_bijective` / 定理 `toModuleEnd_bijective`

English:
theorem toModuleEnd_bijective
  statement: Function.Bijective (toModuleEnd R (S := R) M)
  proof: by
  have : toModuleEnd R (S := R) M = (lid R M).conj ∘ rTensorEquiv R R
      (comm .. ≪≫ₗ linearEquiv R M) ∘ RingEquiv.moduleEndSelf R ∘ MulOpposite.opEquiv := by
    ext; simp [LinearEquiv.conj, liftAux]
  simpa [this] using MulOpposite.opEquiv.bijective

中文:
定理 toModuleEnd_bijective
  结论: 函数.双射 (toModuleEnd R (S := R) M)
  证明: by
  have : toModuleEnd R (S := R) M = (lid R M).conj ∘ rTensorEquiv R R
      (comm .. ≪≫ₗ linearEquiv R M) ∘ RingEquiv.moduleEndSelf R ∘ MulOpposite.opEquiv := by
    ext; simp [LinearEquiv.conj, liftAux]
  simpa [this] using MulOpposite.opEquiv.bijective

Depends on / 依赖: LinearEquiv, LinearEquiv.conj, MulOpposite, MulOpposite.opEquiv, MulOpposite.opEquiv.bijective, RingEquiv, RingEquiv.moduleEndSelf, bijective, liftAux, linearEquiv, moduleEndSelf, opEquiv, rTensorEquiv, toModuleEnd
-/
theorem toModuleEnd_bijective : Function.Bijective (toModuleEnd R (S := R) M) := by
  have : toModuleEnd R (S := R) M = (lid R M).conj ∘ rTensorEquiv R R
      (comm .. ≪≫ₗ linearEquiv R M) ∘ RingEquiv.moduleEndSelf R ∘ MulOpposite.opEquiv := by
    ext; simp [LinearEquiv.conj, liftAux]
  simpa [this] using MulOpposite.opEquiv.bijective

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FaithfulSMul R M
  body: (toModuleEnd_bijective R M).injective LinearMap.ext h

中文:
实例 :
  签名: 忠实标量乘法 R M
  定义体: (toModuleEnd_bijective R M).injective LinearMap.ext h

Depends on / 依赖: LinearMap, LinearMap.ext, injective, toModuleEnd_bijective
-/
instance : FaithfulSMul R M where
eq_of_smul_eq_smul {_ _} h := (toModuleEnd_bijective R M).injective LinearMap.ext h

variable {R M N} in
/--
theorem `bijective_self_of_surjective` / 定理 `bijective_self_of_surjective`

English:
theorem bijective_self_of_surjective
  given: (f : R ->ₗ[R] M) (hf : Function.Surjective f)
  proof: smul_left_injective' (α := M) funext fun m => by
    obtain ⟨r, rfl⟩ := hf m
    simp_rw [← map_smul, smul_eq_mul, mul_comm _ r, ← smul_eq_mul, map_smul, eq]
  right := hf

中文:
定理 bijective_self_of_surjective
  条件: (f : R ->ₗ[R] M) (hf : 函数.满射 f)
  证明: smul_left_injective' (α := M) funext fun m => by
    obtain ⟨r, rfl⟩ := hf m
    simp_rw [← map_smul, smul_eq_mul, mul_comm _ r, ← smul_eq_mul, map_smul, eq]
  right := hf
-/
private theorem bijective_self_of_surjective (f : R ->ₗ[R] M) (hf : Function.Surjective f) :
    Function.Bijective f where
left {r₁ r₂} eq := smul_left_injective' (α := M) funext fun m => by
    obtain ⟨r, rfl⟩ := hf m
    simp_rw [← map_smul, smul_eq_mul, mul_comm _ r, ← smul_eq_mul, map_smul, eq]
  right := hf

variable {R M N} in
/--
theorem `bijective_of_surjective` / 定理 `bijective_of_surjective`

English:
theorem bijective_of_surjective
  statement: [Module.Invertible R N] {f : M ->ₗ[R] N}
  proof: by
  simpa [lTensor_bijective_iff] using bijective_self_of_surjective
    (f.lTensor _ ∘ₗ (linearEquiv R M).symm.toLinearMap) (by simpa [lTensor_surjective_iff] using hf)

中文:
定理 bijective_of_surjective
  结论: [模.可逆 R N] {f : M ->ₗ[R] N}
  证明: by
  simpa [lTensor_bijective_iff] using bijective_self_of_surjective
    (f.lTensor _ ∘ₗ (linearEquiv R M).symm.toLinearMap) (by simpa [lTensor_surjective_iff] using hf)

Depends on / 依赖: bijective_self_of_surjective, f.lTensor, lTensor, lTensor_bijective_iff, lTensor_surjective_iff, linearEquiv, symm.toLinearMap, toLinearMap
-/
theorem bijective_of_surjective [Module.Invertible R N] {f : M ->ₗ[R] N}
    (hf : Function.Surjective f) : Function.Bijective f := by
  simpa [lTensor_bijective_iff] using bijective_self_of_surjective
    (f.lTensor _ ∘ₗ (linearEquiv R M).symm.toLinearMap) (by simpa [lTensor_surjective_iff] using hf)

section LinearEquiv
variable {R M N} [Module.Invertible R N] {f : M ->ₗ[R] N} {g : N ->ₗ[R] M}

/--
theorem `rightInverse_of_leftInverse` / 定理 `rightInverse_of_leftInverse`

English:
theorem rightInverse_of_leftInverse
  given: (hfg : Function.LeftInverse f g)
  proof: Function.rightInverse_of_injective_of_leftInverse
    (bijective_of_surjective hfg.surjective).injective hfg

中文:
定理 rightInverse_of_leftInverse
  条件: (hfg : 函数.左逆 f g)
  证明: Function.rightInverse_of_injective_of_leftInverse
    (bijective_of_surjective hfg.surjective).injective hfg

Depends on / 依赖: Function, Function.rightInverse_of_injective_of_leftInverse, bijective_of_surjective, hfg.surjective, injective, rightInverse_of_injective_of_leftInverse, surjective
-/
theorem rightInverse_of_leftInverse (hfg : Function.LeftInverse f g) :
    Function.RightInverse f g :=
  Function.rightInverse_of_injective_of_leftInverse
    (bijective_of_surjective hfg.surjective).injective hfg

/--
theorem `leftInverse_of_rightInverse` / 定理 `leftInverse_of_rightInverse`

English:
theorem leftInverse_of_rightInverse
  given: (hfg : Function.RightInverse f g)
  proof: rightInverse_of_leftInverse hfg

中文:
定理 leftInverse_of_rightInverse
  条件: (hfg : 函数.右逆 f g)
  证明: rightInverse_of_leftInverse hfg

Depends on / 依赖: rightInverse_of_leftInverse
-/
theorem leftInverse_of_rightInverse (hfg : Function.RightInverse f g) :
    Function.LeftInverse f g :=
  rightInverse_of_leftInverse hfg

variable (f g) in
/--
theorem `leftInverse_iff_rightInverse` / 定理 `leftInverse_iff_rightInverse`

English:
theorem leftInverse_iff_rightInverse
  proof: ⟨rightInverse_of_leftInverse, leftInverse_of_rightInverse⟩

中文:
定理 leftInverse_iff_rightInverse
  证明: ⟨rightInverse_of_leftInverse, leftInverse_of_rightInverse⟩

Depends on / 依赖: leftInverse_of_rightInverse, rightInverse_of_leftInverse
-/
theorem leftInverse_iff_rightInverse :
    Function.LeftInverse f g ↔ Function.RightInverse f g :=
  ⟨rightInverse_of_leftInverse, leftInverse_of_rightInverse⟩

/--
Definition of `linearEquivOfLeftInverse` / `linearEquivOfLeftInverse` 的定义

English:
definition linearEquivOfLeftInverse
  signature: (hfg : Function.LeftInverse f g)
  body: .ofLinearMap f g (LinearMap.ext hfg) (LinearMap.ext <| rightInverse_of_leftInverse hfg)

中文:
定义 linearEquivOfLeftInverse
  签名: (hfg : 函数.左逆 f g)
  定义体: .ofLinearMap f g (LinearMap.ext hfg) (LinearMap.ext <| rightInverse_of_leftInverse hfg)

Depends on / 依赖: LinearMap, LinearMap.ext, ofLinearMap, rightInverse_of_leftInverse
-/
def linearEquivOfLeftInverse (hfg : Function.LeftInverse f g) : M ≃ₗ[R] N :=
  .ofLinearMap f g (LinearMap.ext hfg) (LinearMap.ext <| rightInverse_of_leftInverse hfg)

/--
lemma `linearEquivOfLeftInverse_apply` / 引理 `linearEquivOfLeftInverse_apply`

English:
lemma linearEquivOfLeftInverse_apply
  given: (hfg : Function.LeftInverse f g) (x : M)
  proof: rfl

中文:
引理 linearEquivOfLeftInverse_apply
  条件: (hfg : 函数.左逆 f g) (x : M)
  证明: rfl
-/
@[simp] lemma linearEquivOfLeftInverse_apply (hfg : Function.LeftInverse f g) (x : M) :
    linearEquivOfLeftInverse hfg x = f x := rfl

/--
lemma `linearEquivOfLeftInverse_symm_apply` / 引理 `linearEquivOfLeftInverse_symm_apply`

English:
lemma linearEquivOfLeftInverse_symm_apply
  given: (hfg : Function.LeftInverse f g) (x : N)
  proof: rfl

中文:
引理 linearEquivOfLeftInverse_symm_apply
  条件: (hfg : 函数.左逆 f g) (x : N)
  证明: rfl
-/
@[simp] lemma linearEquivOfLeftInverse_symm_apply (hfg : Function.LeftInverse f g) (x : N) :
    (linearEquivOfLeftInverse hfg).symm x = g x := rfl

/--
Definition of `linearEquivOfRightInverse` / `linearEquivOfRightInverse` 的定义

English:
definition linearEquivOfRightInverse
  signature: (hfg : Function.RightInverse f g)
  body: .ofLinearMap f g (LinearMap.ext <| leftInverse_of_rightInverse hfg) (LinearMap.ext hfg)

中文:
定义 linearEquivOfRightInverse
  签名: (hfg : 函数.右逆 f g)
  定义体: .ofLinearMap f g (LinearMap.ext <| leftInverse_of_rightInverse hfg) (LinearMap.ext hfg)

Depends on / 依赖: LinearMap, LinearMap.ext, leftInverse_of_rightInverse, ofLinearMap
-/
def linearEquivOfRightInverse (hfg : Function.RightInverse f g) : M ≃ₗ[R] N :=
  .ofLinearMap f g (LinearMap.ext <| leftInverse_of_rightInverse hfg) (LinearMap.ext hfg)

/--
lemma `linearEquivOfRightInverse_apply` / 引理 `linearEquivOfRightInverse_apply`

English:
lemma linearEquivOfRightInverse_apply
  given: (hfg : Function.RightInverse f g) (x : M)
  proof: rfl

中文:
引理 linearEquivOfRightInverse_apply
  条件: (hfg : 函数.右逆 f g) (x : M)
  证明: rfl
-/
@[simp] lemma linearEquivOfRightInverse_apply (hfg : Function.RightInverse f g) (x : M) :
    linearEquivOfRightInverse hfg x = f x := rfl

/--
lemma `linearEquivOfRightInverse_symm_apply` / 引理 `linearEquivOfRightInverse_symm_apply`

English:
lemma linearEquivOfRightInverse_symm_apply
  given: (hfg : Function.RightInverse f g) (x : N)
  proof: rfl

中文:
引理 linearEquivOfRightInverse_symm_apply
  条件: (hfg : 函数.右逆 f g) (x : N)
  证明: rfl
-/
@[simp] lemma linearEquivOfRightInverse_symm_apply (hfg : Function.RightInverse f g) (x : N) :
    (linearEquivOfRightInverse hfg).symm x = g x := rfl

end LinearEquiv

section Algebra

section algEquivOfRing

variable [Semiring A] [Algebra R A] [Module.Invertible R A]

/--
Definition of `algEquivOfRing` / `algEquivOfRing` 的定义

English:
definition algEquivOfRing
  signature: : R ≃ₐ[R] A
  body: let inv : A ->ₗ[R] R :=
    linearEquiv R A ∘ₗ
      (LinearMap.mul' R A).lTensor (Dual R A) ∘ₗ
      (leftCancelEquiv A (linearEquiv R A)).symm
  have right : inv ∘ₗ Algebra.linearMap R A = LinearMap.id :=
    let ⟨s, hs⟩ := exists_finset ((linearEquiv R A).symm 1)
LinearMap.ext_ring by simp [inv, hs, sum_tmul, map_sum, ← (LinearEquiv.symm_apply_eq _).1 hs]
  { linearEquivOfRightInverse (f := Algebra.linearMap R A) (g := inv) (LinearMap.ext_iff.1 right),
    Algebra.ofId R A with }

中文:
定义 algEquivOfRing
  签名: : R ≃ₐ[R] A
  定义体: let inv : A ->ₗ[R] R :=
    linearEquiv R A ∘ₗ
      (LinearMap.mul' R A).lTensor (Dual R A) ∘ₗ
      (leftCancelEquiv A (linearEquiv R A)).symm
  have right : inv ∘ₗ Algebra.linearMap R A = LinearMap.id :=
    let ⟨s, hs⟩ := exists_finset ((linearEquiv R A).symm 1)
LinearMap.ext_ring by simp [inv, hs, sum_tmul, map_sum, ← (LinearEquiv.symm_apply_eq _).1 hs]
  { linearEquivOfRightInverse (f := Algebra.linearMap R A) (g := inv) (LinearMap.ext_iff.1 right),
    Algebra.ofId R A with }

Depends on / 依赖: Algebra, Algebra.linearMap, Algebra.ofId, LinearEquiv, LinearEquiv.symm_apply_eq, LinearMap, LinearMap.ext_iff, LinearMap.ext_ring, LinearMap.id, LinearMap.mul, exists_finset, ext_iff, ext_ring, lTensor, leftCancelEquiv, linearEquiv, linearEquivOfRightInverse, linearMap, map_sum, sum_tmul
-/
noncomputable def algEquivOfRing : R ≃ₐ[R] A :=
  let inv : A ->ₗ[R] R :=
    linearEquiv R A ∘ₗ
      (LinearMap.mul' R A).lTensor (Dual R A) ∘ₗ
      (leftCancelEquiv A (linearEquiv R A)).symm
  have right : inv ∘ₗ Algebra.linearMap R A = LinearMap.id :=
    let ⟨s, hs⟩ := exists_finset ((linearEquiv R A).symm 1)
LinearMap.ext_ring by simp [inv, hs, sum_tmul, map_sum, ← (LinearEquiv.symm_apply_eq _).1 hs]
  { linearEquivOfRightInverse (f := Algebra.linearMap R A) (g := inv) (LinearMap.ext_iff.1 right),
    Algebra.ofId R A with }

variable {A} in
/--
lemma `algEquivOfRing_apply` / 引理 `algEquivOfRing_apply`

English:
lemma algEquivOfRing_apply
  given: (x : R)
  statement: algEquivOfRing R A x = algebraMap R A x
  proof: rfl

中文:
引理 algEquivOfRing_apply
  条件: (x : R)
  结论: algEquivOfRing R A x = algebraMap R A x
  证明: rfl
-/
@[simp] lemma algEquivOfRing_apply (x : R) : algEquivOfRing R A x = algebraMap R A x := rfl

end algEquivOfRing

section CommSemiring

variable [CommSemiring A] [Algebra R A]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module.Invertible A (A otimes[R] M)
  body: .right (M := A otimes[R] Dual R M) (AlgebraTensorModule.distribBaseChange ..).symm ≪≫ₗ
    AlgebraTensorModule.congr (.refl A A) (linearEquiv R M) ≪≫ₗ AlgebraTensorModule.rid ..

中文:
实例 :
  签名: 模.可逆 A (A otimes[R] M)
  定义体: .right (M := A otimes[R] Dual R M) (AlgebraTensorModule.distribBaseChange ..).symm ≪≫ₗ
    AlgebraTensorModule.congr (.refl A A) (linearEquiv R M) ≪≫ₗ AlgebraTensorModule.rid ..

Depends on / 依赖: AlgebraTensorModule, AlgebraTensorModule.congr, AlgebraTensorModule.distribBaseChange, AlgebraTensorModule.rid, distribBaseChange, linearEquiv, otimes
-/
instance : Module.Invertible A (A otimes[R] M) :=
.right (M := A otimes[R] Dual R M) (AlgebraTensorModule.distribBaseChange ..).symm ≪≫ₗ
    AlgebraTensorModule.congr (.refl A A) (linearEquiv R M) ≪≫ₗ AlgebraTensorModule.rid ..

variable {R M N A} in
/--
theorem `of_isLocalization` / 定理 `of_isLocalization`

English:
theorem of_isLocalization
  statement: (S : Submonoid R) [IsLocalization S A]
  proof: .congr (IsLocalizedModule.isBaseChange S A f).equiv

中文:
定理 of_isLocalization
  结论: (S : 子幺半群 R) [是Localization S A]
  证明: .congr (IsLocalizedModule.isBaseChange S A f).equiv

Depends on / 依赖: IsLocalizedModule, IsLocalizedModule.isBaseChange, isBaseChange
-/
theorem of_isLocalization (S : Submonoid R) [IsLocalization S A]
    (f : M ->ₗ[R] N) [IsLocalizedModule S f] [Module A N] [IsScalarTower R A N] :
    Module.Invertible A N :=
  .congr (IsLocalizedModule.isBaseChange S A f).equiv

instance (S : Submonoid R) : Module.Invertible (Localization S) (LocalizedModule S M) :=
  of_isLocalization S (LocalizedModule.mkLinearMap S M)

instance (L) [AddCommMonoid L] [Module R L] [Module A L] [IsScalarTower R A L]
    [Module.Invertible A L] : Module.Invertible A (L otimes[R] M) :=
  .congr (AlgebraTensorModule.cancelBaseChange R A A L M)

/--
theorem `exists_finset_free_localization` / 定理 `exists_finset_free_localization`

English:
theorem exists_finset_free_localization
  proof: by
  classical
  -- write 1 = ∑ᵢ fᵢ(mᵢ) with `mᵢ : M` and `fᵢ : Dual R M`
  obtain ⟨S, hS⟩ := ((linearEquiv R M).symm 1).exists_finset
  refine ⟨S.image fun i => i.1 i.2, ?_, fun r hr => ?_⟩
  -- Part 1: The evaluations fᵢ(mᵢ) generate the unit ideal
  · simpa [Ideal.eq_top_iff_one, (LinearEquiv.symm_apply_eq _).mp hS, linearEquiv]
      using Ideal.sum_mem _ fun i hi => Ideal.subset_span (Finset.mem_image_of_mem _ hi)
  -- Part 2: After localizing at any f(m), the module becomes free
  obtain ⟨⟨f, m⟩, _, rfl⟩ := Finset.mem_image.mp hr
  -- Extend f to a R_{f(m)}-linear functional f' on the localized module
  let f' : Dual (Localization.Away (f m)) (LocalizedModule.Away (f m) M) :=
.extendScalarsOfIsLocalization (.powers (f m)) _ IsLocalizedModule.map
      (.powers (f m)) (LocalizedModule.mkLinearMap _ M) (Algebra.linearMap R _) f
  -- f'(m/1) = f(m)/1 is a unit in R_{f(m)}, so f' is surjective and therefore bijective
have surj : Function.Surjective f' := LinearMap.range_eq_top.mp Ideal.eq_top_of_isUnit_mem
    _ ⟨_, IsLocalizedModule.map_apply ..⟩ (IsLocalization.Away.algebraMap_isUnit (f m))
exact .of_equiv .symm .ofBijective f' (bijective_of_surjective surj)

中文:
定理 存在_finset_free_localization
  证明: by
  classical
  -- write 1 = ∑ᵢ fᵢ(mᵢ) with `mᵢ : M` and `fᵢ : Dual R M`
  obtain ⟨S, hS⟩ := ((linearEquiv R M).symm 1).exists_finset
  refine ⟨S.image fun i => i.1 i.2, ?_, fun r hr => ?_⟩
  -- Part 1: The evaluations fᵢ(mᵢ) generate the unit ideal
  · simpa [Ideal.eq_top_iff_one, (LinearEquiv.symm_apply_eq _).mp hS, linearEquiv]
      using Ideal.sum_mem _ fun i hi => Ideal.subset_span (Finset.mem_image_of_mem _ hi)
  -- Part 2: After localizing at any f(m), the module becomes free
  obtain ⟨⟨f, m⟩, _, rfl⟩ := Finset.mem_image.mp hr
  -- Extend f to a R_{f(m)}-linear functional f' on the localized module
  let f' : Dual (Localization.Away (f m)) (LocalizedModule.Away (f m) M) :=
.extendScalarsOfIsLocalization (.powers (f m)) _ IsLocalizedModule.map
      (.powers (f m)) (LocalizedModule.mkLinearMap _ M) (Algebra.linearMap R _) f
  -- f'(m/1) = f(m)/1 is a unit in R_{f(m)}, so f' is surjective and therefore bijective
have surj : Function.Surjective f' := LinearMap.range_eq_top.mp Ideal.eq_top_of_isUnit_mem
    _ ⟨_, IsLocalizedModule.map_apply ..⟩ (IsLocalization.Away.algebraMap_isUnit (f m))
exact .of_equiv .symm .ofBijective f' (bijective_of_surjective surj)

Depends on / 依赖: classical
-/
theorem exists_finset_free_localization :
    exists s : Finset R, Ideal.span (s : Set R) = ⊤ ∧
      forall r in s, Free (Localization.Away r) (LocalizedModule.Away r M) := by
  classical
  -- write 1 = ∑ᵢ fᵢ(mᵢ) with `mᵢ : M` and `fᵢ : Dual R M`
  obtain ⟨S, hS⟩ := ((linearEquiv R M).symm 1).exists_finset
  refine ⟨S.image fun i => i.1 i.2, ?_, fun r hr => ?_⟩
  -- Part 1: The evaluations fᵢ(mᵢ) generate the unit ideal
  · simpa [Ideal.eq_top_iff_one, (LinearEquiv.symm_apply_eq _).mp hS, linearEquiv]
      using Ideal.sum_mem _ fun i hi => Ideal.subset_span (Finset.mem_image_of_mem _ hi)
  -- Part 2: After localizing at any f(m), the module becomes free
  obtain ⟨⟨f, m⟩, _, rfl⟩ := Finset.mem_image.mp hr
  -- Extend f to a R_{f(m)}-linear functional f' on the localized module
  let f' : Dual (Localization.Away (f m)) (LocalizedModule.Away (f m) M) :=
.extendScalarsOfIsLocalization (.powers (f m)) _ IsLocalizedModule.map
      (.powers (f m)) (LocalizedModule.mkLinearMap _ M) (Algebra.linearMap R _) f
  -- f'(m/1) = f(m)/1 is a unit in R_{f(m)}, so f' is surjective and therefore bijective
have surj : Function.Surjective f' := LinearMap.range_eq_top.mp Ideal.eq_top_of_isUnit_mem
    _ ⟨_, IsLocalizedModule.map_apply ..⟩ (IsLocalization.Away.algebraMap_isUnit (f m))
exact .of_equiv .symm .ofBijective f' (bijective_of_surjective surj)

end CommSemiring

end Algebra

end Invertible

end Module

section PicardGroup

open CategoryTheory Module

instance (M : (Skeleton <| SemimoduleCat.{u} R)ˣ) : Module.Invertible R M :=
  .right (Quotient.eq.mp M.inv_mul).some.toLinearEquivₛ

instance (R : Type u) [CommRing R] (M : (Skeleton <| ModuleCat.{u} R)ˣ) : Module.Invertible R M :=
  .right (Quotient.eq.mp M.inv_mul).some.toLinearEquiv

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Small.{u} (Skeleton <| SemimoduleCat.{u} R)ˣ
  body: let sf := Σ n, ModuleCon R (Fin n -> R)
  have {c₁ c₂ : sf} : c₁ = c₂ -> c₁.2.Quotient ≃ₗ[R] c₂.2.Quotient := by rintro rfl; exact .refl ..
  let f (M : (Skeleton <| SemimoduleCat.{u} R)ˣ) : sf := ⟨_, Finite.kerReprₛ R M⟩
small_of_injective (f := f) fun M N eq => Units.ext Quotient.out_equiv_out.mp
    ⟨((Finite.reprEquivₛ R M).symm ≪≫ₗ this eq ≪≫ₗ Finite.reprEquivₛ R N).toModuleIsoₛ⟩

中文:
实例 :
  签名: Small.{u} (Skeleton <| Semimodule范畴.{u} R)ˣ
  定义体: let sf := Σ n, ModuleCon R (Fin n -> R)
  have {c₁ c₂ : sf} : c₁ = c₂ -> c₁.2.Quotient ≃ₗ[R] c₂.2.Quotient := by rintro rfl; exact .refl ..
  let f (M : (Skeleton <| SemimoduleCat.{u} R)ˣ) : sf := ⟨_, Finite.kerReprₛ R M⟩
small_of_injective (f := f) fun M N eq => Units.ext Quotient.out_equiv_out.mp
    ⟨((Finite.reprEquivₛ R M).symm ≪≫ₗ this eq ≪≫ₗ Finite.reprEquivₛ R N).toModuleIsoₛ⟩

Depends on / 依赖: Finite, Finite.kerRepr, Finite.reprEquiv, ModuleCon, Quotient, Quotient.out_equiv_out.mp, SemimoduleCat, Skeleton, Units.ext, out_equiv_out, small_of_injective
-/
instance : Small.{u} (Skeleton <| SemimoduleCat.{u} R)ˣ :=
  let sf := Σ n, ModuleCon R (Fin n -> R)
  have {c₁ c₂ : sf} : c₁ = c₂ -> c₁.2.Quotient ≃ₗ[R] c₂.2.Quotient := by rintro rfl; exact .refl ..
  let f (M : (Skeleton <| SemimoduleCat.{u} R)ˣ) : sf := ⟨_, Finite.kerReprₛ R M⟩
small_of_injective (f := f) fun M N eq => Units.ext Quotient.out_equiv_out.mp
    ⟨((Finite.reprEquivₛ R M).symm ≪≫ₗ this eq ≪≫ₗ Finite.reprEquivₛ R N).toModuleIsoₛ⟩

instance (R : Type u) [CommRing R] : Small.{u} (Skeleton <| ModuleCat.{u} R)ˣ :=
  small_map (Units.mapEquiv <| Skeleton.mulEquiv ModuleCat.equivalenceSemimoduleCat).toEquiv

/--
Definition of `CommRing.Pic` / `CommRing.Pic` 的定义

English:
definition CommRing.Pic
  signature: (R : Type u) [CommSemiring R]
  body: Shrink (Skeleton <| SemimoduleCat.{u} R)ˣ

中文:
定义 交换环.Pic
  签名: (R : 类型u) [交换半环 R]
  定义体: Shrink (Skeleton <| SemimoduleCat.{u} R)ˣ

Depends on / 依赖: SemimoduleCat, Shrink, Skeleton
-/
def CommRing.Pic (R : Type u) [CommSemiring R] : Type u :=
  Shrink (Skeleton <| SemimoduleCat.{u} R)ˣ

open CommRing (Pic)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CommGroup (Pic R)
  body: fast_instance% (equivShrink _).symm.commGroup

中文:
实例 :
  签名: 交换群 (Pic R)
  定义体: fast_instance% (equivShrink _).symm.commGroup

Depends on / 依赖: commGroup, equivShrink, fast_instance, symm.commGroup
-/
noncomputable instance : CommGroup (Pic R) := fast_instance% (equivShrink _).symm.commGroup

variable [Module.Invertible R M] [Module.Invertible R N]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module.Invertible R (Finite.reprₛ R M)
  body: .congr (Finite.reprEquivₛ R M).symm

中文:
实例 :
  签名: 模.可逆 R (有限.reprₛ R M)
  定义体: .congr (Finite.reprEquivₛ R M).symm

Depends on / 依赖: Finite, Finite.reprEquiv
-/
instance : Module.Invertible R (Finite.reprₛ R M) := .congr (Finite.reprEquivₛ R M).symm

namespace CommRing.Pic

variable {R} in
/--
Definition of `AsModule` / `AsModule` 的定义

English:
abbreviation AsModule
  signature: (M : Pic R)
  body: ((equivShrink _).symm M).val

中文:
缩写 AsModule
  签名: (M : Pic R)
  定义体: ((equivShrink _).symm M).val

Depends on / 依赖: equivShrink
-/
abbrev AsModule (M : Pic R) : Type u := ((equivShrink _).symm M).val

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort (Pic R) (Type u)
  body: ⟨AsModule⟩

中文:
实例 :
  签名: CoeSort (Pic R) (类型u)
  定义体: ⟨AsModule⟩

Depends on / 依赖: AsModule
-/
noncomputable instance : CoeSort (Pic R) (Type u) := ⟨AsModule⟩

noncomputable instance (R) [CommRing R] (M : Pic R) : AddCommGroup M :=
  Module.addCommMonoidToAddCommGroup R

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.privateInPublic true in
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def equivShrinkLinearEquiv (M : (Skeleton <| SemimoduleCat.{u} R)ˣ)
  body: have {M N : Skeleton (SemimoduleCat.{u} R)} : M = N -> M ≃ₗ[R] N := by rintro rfl; exact .refl ..
  this (by simp)

中文:
定义 noncomputable
  签名: def equivShrinkLinearEquiv (M : (Skeleton <| Semimodule范畴.{u} R)ˣ)
  定义体: have {M N : Skeleton (SemimoduleCat.{u} R)} : M = N -> M ≃ₗ[R] N := by rintro rfl; exact .refl ..
  this (by simp)
-/
private noncomputable def equivShrinkLinearEquiv (M : (Skeleton <| SemimoduleCat.{u} R)ˣ) :
    (id <| equivShrink _ M : Pic R) ≃ₗ[R] M :=
  have {M N : Skeleton (SemimoduleCat.{u} R)} : M = N -> M ≃ₗ[R] N := by rintro rfl; exact .refl ..
  this (by simp)

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def mk
  body: equivShrink _
  letI M' := Finite.reprₛ R M
.mkOfMulEqOne ⟦.of R M'⟧ ⟦.of R (Dual R M')⟧ by
    rw [← toSkeleton]; rw [← toSkeleton]; rw [mul_comm]; rw [← Skeleton.toSkeleton_tensorObj]
    exact Quotient.sound ⟨(Invertible.linearEquiv R _).toModuleIsoₛ⟩

中文:
定义 noncomputable
  签名: def mk
  定义体: equivShrink _
  letI M' := Finite.reprₛ R M
.mkOfMulEqOne ⟦.of R M'⟧ ⟦.of R (Dual R M')⟧ by
    rw [← toSkeleton]; rw [← toSkeleton]; rw [mul_comm]; rw [← Skeleton.toSkeleton_tensorObj]
    exact Quotient.sound ⟨(Invertible.linearEquiv R _).toModuleIsoₛ⟩
-/
protected noncomputable def mk : Pic R := equivShrink _
  letI M' := Finite.reprₛ R M
.mkOfMulEqOne ⟦.of R M'⟧ ⟦.of R (Dual R M')⟧ by
    rw [← toSkeleton]; rw [← toSkeleton]; rw [mul_comm]; rw [← Skeleton.toSkeleton_tensorObj]
    exact Quotient.sound ⟨(Invertible.linearEquiv R _).toModuleIsoₛ⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Definition of `mk.linearEquiv` / `mk.linearEquiv` 的定义

English:
definition mk.linearEquiv
  signature: : Pic.mk R M ≃ₗ[R] M
  body: equivShrinkLinearEquiv R _ ≪≫ₗ (Quotient.mk_out (s := isIsomorphicSetoid _)
    (SemimoduleCat.of R (Finite.reprₛ R M))).some.toLinearEquivₛ ≪≫ₗ Finite.reprEquivₛ R M

中文:
定义 mk.linearEquiv
  签名: : Pic.mk R M ≃ₗ[R] M
  定义体: equivShrinkLinearEquiv R _ ≪≫ₗ (Quotient.mk_out (s := isIsomorphicSetoid _)
    (SemimoduleCat.of R (Finite.reprₛ R M))).some.toLinearEquivₛ ≪≫ₗ Finite.reprEquivₛ R M

Depends on / 依赖: Finite, Finite.repr, Finite.reprEquiv, Quotient, Quotient.mk_out, SemimoduleCat, SemimoduleCat.of, equivShrinkLinearEquiv, isIsomorphicSetoid, mk_out, some.toLinearEquiv
-/
noncomputable def mk.linearEquiv : Pic.mk R M ≃ₗ[R] M :=
  equivShrinkLinearEquiv R _ ≪≫ₗ (Quotient.mk_out (s := isIsomorphicSetoid _)
    (SemimoduleCat.of R (Finite.reprₛ R M))).some.toLinearEquivₛ ≪≫ₗ Finite.reprEquivₛ R M

variable {R M N}

/--
theorem `mk_eq_iff` / 定理 `mk_eq_iff`

English:
theorem mk_eq_iff
  given: {N : Pic R}
  statement: Pic.mk R M = N ↔ Nonempty (M ≃ₗ[R] N) where
  proof: (· ▸ ⟨(mk.linearEquiv R M).symm⟩)
mpr := fun ⟨e⟩ => ((equivShrink _).eq_symm_apply).mp
Units.ext Quotient.mk_eq_iff_out.mpr ⟨(Finite.reprEquivₛ R M ≪≫ₗ e).toModuleIsoₛ⟩

中文:
定理 mk_eq_iff
  条件: {N : Pic R}
  结论: Pic.mk R M = N ↔ 非空 (M ≃ₗ[R] N) where
  证明: (· ▸ ⟨(mk.linearEquiv R M).symm⟩)
mpr := fun ⟨e⟩ => ((equivShrink _).eq_symm_apply).mp
Units.ext Quotient.mk_eq_iff_out.mpr ⟨(Finite.reprEquivₛ R M ≪≫ₗ e).toModuleIsoₛ⟩

Depends on / 依赖: linearEquiv, mk.linearEquiv
-/
theorem mk_eq_iff {N : Pic R} : Pic.mk R M = N ↔ Nonempty (M ≃ₗ[R] N) where
  mp := (· ▸ ⟨(mk.linearEquiv R M).symm⟩)
mpr := fun ⟨e⟩ => ((equivShrink _).eq_symm_apply).mp
Units.ext Quotient.mk_eq_iff_out.mpr ⟨(Finite.reprEquivₛ R M ≪≫ₗ e).toModuleIsoₛ⟩

/--
theorem `mk_eq_self` / 定理 `mk_eq_self`

English:
theorem mk_eq_self
  given: {M : Pic R}
  statement: Pic.mk R M = M
  proof: mk_eq_iff.mpr ⟨.refl ..⟩

中文:
定理 mk_eq_self
  条件: {M : Pic R}
  结论: Pic.mk R M = M
  证明: mk_eq_iff.mpr ⟨.refl ..⟩

Depends on / 依赖: mk_eq_iff, mk_eq_iff.mpr
-/
theorem mk_eq_self {M : Pic R} : Pic.mk R M = M := mk_eq_iff.mpr ⟨.refl ..⟩

/--
theorem `ext_iff` / 定理 `ext_iff`

English:
theorem ext_iff
  given: {M N : Pic R}
  statement: M = N ↔ Nonempty (M ≃ₗ[R] N)
  proof: by
  rw [← mk_eq_iff]; rw [mk_eq_self]

中文:
定理 ext_iff
  条件: {M N : Pic R}
  结论: M = N ↔ 非空 (M ≃ₗ[R] N)
  证明: by
  rw [← mk_eq_iff]; rw [mk_eq_self]

Depends on / 依赖: mk_eq_iff, mk_eq_self
-/
theorem ext_iff {M N : Pic R} : M = N ↔ Nonempty (M ≃ₗ[R] N) := by
  rw [← mk_eq_iff]; rw [mk_eq_self]

/--
theorem `mk_eq_mk_iff` / 定理 `mk_eq_mk_iff`

English:
theorem mk_eq_mk_iff
  statement: Pic.mk R M = Pic.mk R N ↔ Nonempty (M ≃ₗ[R] N)
  proof: let eN := mk.linearEquiv R N
  mk_eq_iff.trans ⟨fun ⟨e⟩ => ⟨e ≪≫ₗ eN⟩, fun ⟨e⟩ => ⟨e ≪≫ₗ eN.symm⟩⟩

中文:
定理 mk_eq_mk_iff
  结论: Pic.mk R M = Pic.mk R N ↔ 非空 (M ≃ₗ[R] N)
  证明: let eN := mk.linearEquiv R N
  mk_eq_iff.trans ⟨fun ⟨e⟩ => ⟨e ≪≫ₗ eN⟩, fun ⟨e⟩ => ⟨e ≪≫ₗ eN.symm⟩⟩

Depends on / 依赖: eN.symm, linearEquiv, mk.linearEquiv, mk_eq_iff, mk_eq_iff.trans
-/
theorem mk_eq_mk_iff : Pic.mk R M = Pic.mk R N ↔ Nonempty (M ≃ₗ[R] N) :=
  let eN := mk.linearEquiv R N
  mk_eq_iff.trans ⟨fun ⟨e⟩ => ⟨e ≪≫ₗ eN⟩, fun ⟨e⟩ => ⟨e ≪≫ₗ eN.symm⟩⟩

/--
theorem `mk_self` / 定理 `mk_self`

English:
theorem mk_self
  statement: Pic.mk R R = 1
  proof: congr_arg (equivShrink _) Units.ext Quotient.sound ⟨(Finite.reprEquivₛ R R).toModuleIsoₛ⟩

中文:
定理 mk_self
  结论: Pic.mk R R = 1
  证明: congr_arg (equivShrink _) Units.ext Quotient.sound ⟨(Finite.reprEquivₛ R R).toModuleIsoₛ⟩

Depends on / 依赖: Finite, Finite.reprEquiv, Quotient, Quotient.sound, Units.ext, congr_arg, equivShrink
-/
theorem mk_self : Pic.mk R R = 1 :=
congr_arg (equivShrink _) Units.ext Quotient.sound ⟨(Finite.reprEquivₛ R R).toModuleIsoₛ⟩

/--
theorem `mk_eq_one_iff` / 定理 `mk_eq_one_iff`

English:
theorem mk_eq_one_iff
  statement: Pic.mk R M = 1 ↔ Nonempty (M ≃ₗ[R] R)
  proof: by
  rw [← mk_self]; rw [mk_eq_mk_iff]

中文:
定理 mk_eq_one_iff
  结论: Pic.mk R M = 1 ↔ 非空 (M ≃ₗ[R] R)
  证明: by
  rw [← mk_self]; rw [mk_eq_mk_iff]

Depends on / 依赖: mk_eq_mk_iff, mk_self
-/
theorem mk_eq_one_iff : Pic.mk R M = 1 ↔ Nonempty (M ≃ₗ[R] R) := by
  rw [← mk_self]; rw [mk_eq_mk_iff]

/--
theorem `mk_eq_one_iff_free` / 定理 `mk_eq_one_iff_free`

English:
theorem mk_eq_one_iff_free
  statement: Pic.mk R M = 1 ↔ Free R M
  proof: mk_eq_one_iff.trans Invertible.free_iff_linearEquiv.symm

中文:
定理 mk_eq_one_iff_free
  结论: Pic.mk R M = 1 ↔ 自由 R M
  证明: mk_eq_one_iff.trans Invertible.free_iff_linearEquiv.symm

Depends on / 依赖: Invertible, Invertible.free_iff_linearEquiv.symm, free_iff_linearEquiv, mk_eq_one_iff, mk_eq_one_iff.trans
-/
theorem mk_eq_one_iff_free : Pic.mk R M = 1 ↔ Free R M :=
  mk_eq_one_iff.trans Invertible.free_iff_linearEquiv.symm

variable (R M) in
/--
theorem `mk_eq_one` / 定理 `mk_eq_one`

English:
theorem mk_eq_one
  given: [Free R M]
  statement: Pic.mk R M = 1
  proof: mk_eq_one_iff_free.mpr ‹_›

中文:
定理 mk_eq_one
  条件: [自由 R M]
  结论: Pic.mk R M = 1
  证明: mk_eq_one_iff_free.mpr ‹_›

Depends on / 依赖: mk_eq_one_iff_free, mk_eq_one_iff_free.mpr
-/
theorem mk_eq_one [Free R M] : Pic.mk R M = 1 := mk_eq_one_iff_free.mpr ‹_›

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Free R (1 : Pic R)
  body: mk_eq_one_iff_free.mp mk_eq_self

中文:
实例 :
  签名: 自由 R (1 : Pic R)
  定义体: mk_eq_one_iff_free.mp mk_eq_self

Depends on / 依赖: mk_eq_one_iff_free, mk_eq_one_iff_free.mp, mk_eq_self
-/
instance : Free R (1 : Pic R) := mk_eq_one_iff_free.mp mk_eq_self

/--
theorem `mk_tensor` / 定理 `mk_tensor`

English:
theorem mk_tensor
  statement: Pic.mk R (M otimes[R] N) = Pic.mk R M * Pic.mk R N
  proof: congr_arg (equivShrink _) Units.ext by
    simp_rw [Pic.mk, Equiv.toFun_as_coe, Equiv.symm_apply_apply]
    refine (Quotient.sound ?_).trans (Skeleton.toSkeleton_tensorObj ..)
    exact ⟨(Finite.reprEquivₛ R _ ≪≫ₗ TensorProduct.congr
      (Finite.reprEquivₛ R M).symm (Finite.reprEquivₛ R N).symm).toModuleIsoₛ⟩

中文:
定理 mk_tensor
  结论: Pic.mk R (M otimes[R] N) = Pic.mk R M * Pic.mk R N
  证明: congr_arg (equivShrink _) Units.ext by
    simp_rw [Pic.mk, Equiv.toFun_as_coe, Equiv.symm_apply_apply]
    refine (Quotient.sound ?_).trans (Skeleton.toSkeleton_tensorObj ..)
    exact ⟨(Finite.reprEquivₛ R _ ≪≫ₗ TensorProduct.congr
      (Finite.reprEquivₛ R M).symm (Finite.reprEquivₛ R N).symm).toModuleIsoₛ⟩

Depends on / 依赖: Equiv.symm_apply_apply, Equiv.toFun_as_coe, Finite, Finite.reprEquiv, Pic.mk, Quotient, Quotient.sound, Skeleton, Skeleton.toSkeleton_tensorObj, TensorProduct, TensorProduct.congr, Units.ext, congr_arg, equivShrink, simp_rw, symm_apply_apply, toFun_as_coe, toSkeleton_tensorObj
-/
theorem mk_tensor : Pic.mk R (M otimes[R] N) = Pic.mk R M * Pic.mk R N :=
congr_arg (equivShrink _) Units.ext by
    simp_rw [Pic.mk, Equiv.toFun_as_coe, Equiv.symm_apply_apply]
    refine (Quotient.sound ?_).trans (Skeleton.toSkeleton_tensorObj ..)
    exact ⟨(Finite.reprEquivₛ R _ ≪≫ₗ TensorProduct.congr
      (Finite.reprEquivₛ R M).symm (Finite.reprEquivₛ R N).symm).toModuleIsoₛ⟩

/--
theorem `mk_dual` / 定理 `mk_dual`

English:
theorem mk_dual
  statement: Pic.mk R (Dual R M) = (Pic.mk R M)⁻¹
  proof: congr_arg (equivShrink _) Units.ext by
    rw [Pic.mk]; rw [Equiv.toFun_as_coe]; rw [Equiv.symm_apply_apply]
    exact Quotient.sound ⟨(Finite.reprEquivₛ R _ ≪≫ₗ (Finite.reprEquivₛ R _).dualMap).toModuleIsoₛ⟩

中文:
定理 mk_dual
  结论: Pic.mk R (对偶 R M) = (Pic.mk R M)⁻¹
  证明: congr_arg (equivShrink _) Units.ext by
    rw [Pic.mk]; rw [Equiv.toFun_as_coe]; rw [Equiv.symm_apply_apply]
    exact Quotient.sound ⟨(Finite.reprEquivₛ R _ ≪≫ₗ (Finite.reprEquivₛ R _).dualMap).toModuleIsoₛ⟩

Depends on / 依赖: Equiv.symm_apply_apply, Equiv.toFun_as_coe, Finite, Finite.reprEquiv, Pic.mk, Quotient, Quotient.sound, Units.ext, congr_arg, dualMap, equivShrink, symm_apply_apply, toFun_as_coe
-/
theorem mk_dual : Pic.mk R (Dual R M) = (Pic.mk R M)⁻¹ :=
congr_arg (equivShrink _) Units.ext by
    rw [Pic.mk]; rw [Equiv.toFun_as_coe]; rw [Equiv.symm_apply_apply]
    exact Quotient.sound ⟨(Finite.reprEquivₛ R _ ≪≫ₗ (Finite.reprEquivₛ R _).dualMap).toModuleIsoₛ⟩

/--
theorem `inv_eq_dual` / 定理 `inv_eq_dual`

English:
theorem inv_eq_dual
  given: (M : Pic R)
  statement: M⁻¹ = Pic.mk R (Dual R M)
  proof: by
  rw [mk_dual]; rw [mk_eq_self]

中文:
定理 inv_eq_dual
  条件: (M : Pic R)
  结论: M⁻¹ = Pic.mk R (对偶 R M)
  证明: by
  rw [mk_dual]; rw [mk_eq_self]

Depends on / 依赖: mk_dual, mk_eq_self
-/
theorem inv_eq_dual (M : Pic R) : M⁻¹ = Pic.mk R (Dual R M) := by
  rw [mk_dual]; rw [mk_eq_self]

/--
theorem `mul_eq_tensor` / 定理 `mul_eq_tensor`

English:
theorem mul_eq_tensor
  given: (M N : Pic R)
  statement: M * N = Pic.mk R (M otimes[R] N)
  proof: by
  rw [mk_tensor]; rw [mk_eq_self]; rw [mk_eq_self]

中文:
定理 mul_eq_tensor
  条件: (M N : Pic R)
  结论: M * N = Pic.mk R (M otimes[R] N)
  证明: by
  rw [mk_tensor]; rw [mk_eq_self]; rw [mk_eq_self]

Depends on / 依赖: mk_eq_self, mk_tensor
-/
theorem mul_eq_tensor (M N : Pic R) : M * N = Pic.mk R (M otimes[R] N) := by
  rw [mk_tensor]; rw [mk_eq_self]; rw [mk_eq_self]

/--
theorem `subsingleton_iffₛ` / 定理 `subsingleton_iffₛ`

English:
theorem subsingleton_iffₛ
  statement: Subsingleton (Pic R) ↔
  proof: .trans ⟨fun _ M _ _ _ => Subsingleton.elim ..,
fun h => ⟨fun M N => by rw [← mk_eq_self (M := M), ← mk_eq_self (M := N), h, h]⟩⟩
    forall₄_congr fun _ _ _ _ => mk_eq_one_iff_free

中文:
定理 subsingleton_iffₛ
  结论: 子单例 (Pic R) ↔
  证明: .trans ⟨fun _ M _ _ _ => Subsingleton.elim ..,
fun h => ⟨fun M N => by rw [← mk_eq_self (M := M), ← mk_eq_self (M := N), h, h]⟩⟩
    forall₄_congr fun _ _ _ _ => mk_eq_one_iff_free

Depends on / 依赖: Subsingleton, Subsingleton.elim, mk_eq_one_iff_free, mk_eq_self
-/
theorem subsingleton_iffₛ : Subsingleton (Pic R) ↔
    forall (M : Type u) [AddCommMonoid M] [Module R M], Module.Invertible R M -> Free R M :=
  .trans ⟨fun _ M _ _ _ => Subsingleton.elim ..,
fun h => ⟨fun M N => by rw [← mk_eq_self (M := M), ← mk_eq_self (M := N), h, h]⟩⟩
    forall₄_congr fun _ _ _ _ => mk_eq_one_iff_free

/--
theorem `subsingleton_iff` / 定理 `subsingleton_iff`

English:
theorem subsingleton_iff
  given: {R : Type u} [CommRing R]
  statement: Subsingleton (Pic R) ↔
  proof: subsingleton_iffₛ.trans
    ⟨fun h M => h M, fun h M => let _ := @Module.addCommMonoidToAddCommGroup R; h M⟩

中文:
定理 subsingleton_iff
  条件: {R : 类型u} [交换环 R]
  结论: 子单例 (Pic R) ↔
  证明: subsingleton_iffₛ.trans
    ⟨fun h M => h M, fun h M => let _ := @Module.addCommMonoidToAddCommGroup R; h M⟩

Depends on / 依赖: Module, Module.addCommMonoidToAddCommGroup, addCommMonoidToAddCommGroup
-/
theorem subsingleton_iff {R : Type u} [CommRing R] : Subsingleton (Pic R) ↔
    forall (M : Type u) [AddCommGroup M] [Module R M], Module.Invertible R M -> Free R M :=
  subsingleton_iffₛ.trans
    ⟨fun h M => h M, fun h M => let _ := @Module.addCommMonoidToAddCommGroup R; h M⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Subsingleton
  signature: (Pic R)] : Free R M
  body: have := subsingleton_iffₛ.mp ‹_› (Finite.reprₛ R M) inferInstance
  .of_equiv (Finite.reprEquivₛ R M)

中文:
实例 [子单例
  签名: (Pic R)] : 自由 R M
  定义体: have := subsingleton_iffₛ.mp ‹_› (Finite.reprₛ R M) inferInstance
  .of_equiv (Finite.reprEquivₛ R M)

Depends on / 依赖: Finite, Finite.repr, Finite.reprEquiv, of_equiv
-/
instance [Subsingleton (Pic R)] : Free R M :=
  have := subsingleton_iffₛ.mp ‹_› (Finite.reprₛ R M) inferInstance
  .of_equiv (Finite.reprEquivₛ R M)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsLocalRing
  signature: R] : Subsingleton (Pic R)
  body: subsingleton_iffₛ.mpr fun M _ _ _ => by
  obtain ⟨S, hS⟩ := ((Invertible.linearEquiv R M).symm 1).exists_finset
  replace hS : 1 = ∑ i in S, i.1 i.2 := by
    simpa [LinearEquiv.symm_apply_eq, Invertible.linearEquiv] using hS
  obtain ⟨⟨f, m⟩, mem, hfm⟩ := IsLocalRing.exists_of_isUnit_sum (hS ▸ isUnit_one)
exact .of_equiv .symm .ofBijective f (Invertible.bijective_of_surjective <|
LinearMap.range_eq_top.mp Ideal.eq_top_of_isUnit_mem _ ⟨m, rfl⟩ hfm)

中文:
实例 [是局部环
  签名: R] : 子单例 (Pic R)
  定义体: subsingleton_iffₛ.mpr fun M _ _ _ => by
  obtain ⟨S, hS⟩ := ((Invertible.linearEquiv R M).symm 1).exists_finset
  replace hS : 1 = ∑ i in S, i.1 i.2 := by
    simpa [LinearEquiv.symm_apply_eq, Invertible.linearEquiv] using hS
  obtain ⟨⟨f, m⟩, mem, hfm⟩ := IsLocalRing.exists_of_isUnit_sum (hS ▸ isUnit_one)
exact .of_equiv .symm .ofBijective f (Invertible.bijective_of_surjective <|
LinearMap.range_eq_top.mp Ideal.eq_top_of_isUnit_mem _ ⟨m, rfl⟩ hfm)

Depends on / 依赖: Ideal.eq_top_of_isUnit_mem, Invertible, Invertible.bijective_of_surjective, Invertible.linearEquiv, IsLocalRing, IsLocalRing.exists_of_isUnit_sum, LinearEquiv, LinearEquiv.symm_apply_eq, LinearMap, LinearMap.range_eq_top.mp, bijective_of_surjective, eq_top_of_isUnit_mem, exists_finset, exists_of_isUnit_sum, isUnit_one, linearEquiv, ofBijective, of_equiv, range_eq_top, replace
-/
instance [IsLocalRing R] : Subsingleton (Pic R) := subsingleton_iffₛ.mpr fun M _ _ _ => by
  obtain ⟨S, hS⟩ := ((Invertible.linearEquiv R M).symm 1).exists_finset
  replace hS : 1 = ∑ i in S, i.1 i.2 := by
    simpa [LinearEquiv.symm_apply_eq, Invertible.linearEquiv] using hS
  obtain ⟨⟨f, m⟩, mem, hfm⟩ := IsLocalRing.exists_of_isUnit_sum (hS ▸ isUnit_one)
exact .of_equiv .symm .ofBijective f (Invertible.bijective_of_surjective <|
LinearMap.range_eq_top.mp Ideal.eq_top_of_isUnit_mem _ ⟨m, rfl⟩ hfm)

/-- The Picard group of a semilocal ring is trivial. -/
instance (R) [CommRing R] [Finite (MaximalSpectrum R)] : Subsingleton (Pic R) :=
  subsingleton_iff.mpr fun _ _ _ _ => free_of_flat_of_finrank_eq _ _ 1
    fun _ => let _ := @Ideal.Quotient.field; Invertible.finrank_eq_one ..

variable (R) (A B : Type*) [CommSemiring A] [CommSemiring B] [Algebra R A]

open AlgebraTensorModule in
/--
Definition of `mapAlgebra` / `mapAlgebra` 的定义

English:
definition mapAlgebra
  signature: : Pic R ->* Pic A where
  body: .mk A (A otimes[R] M)
  map_one' := mk_eq_one_iff.mpr (Invertible.free_iff_linearEquiv.mp inferInstance)
  map_mul' _ _ := by
    rw [← mk_tensor]; rw [mk_eq_mk_iff]
    refine ⟨congr (.refl ..) (.symm (mk_eq_iff.mp ?_).some) ≪≫ₗ distribBaseChange R A ..⟩
    simp_rw [mk_tensor, mk_eq_self]

中文:
定义 mapAlgebra
  签名: : Pic R ->* Pic A where
  定义体: .mk A (A otimes[R] M)
  map_one' := mk_eq_one_iff.mpr (Invertible.free_iff_linearEquiv.mp inferInstance)
  map_mul' _ _ := by
    rw [← mk_tensor]; rw [mk_eq_mk_iff]
    refine ⟨congr (.refl ..) (.symm (mk_eq_iff.mp ?_).some) ≪≫ₗ distribBaseChange R A ..⟩
    simp_rw [mk_tensor, mk_eq_self]
-/
@[simps] noncomputable def mapAlgebra : Pic R ->* Pic A where
  toFun M := .mk A (A otimes[R] M)
  map_one' := mk_eq_one_iff.mpr (Invertible.free_iff_linearEquiv.mp inferInstance)
  map_mul' _ _ := by
    rw [← mk_tensor]; rw [mk_eq_mk_iff]
    refine ⟨congr (.refl ..) (.symm (mk_eq_iff.mp ?_).some) ≪≫ₗ distribBaseChange R A ..⟩
    simp_rw [mk_tensor, mk_eq_self]

variable {R A B} [Algebra R B] [Algebra A B] [IsScalarTower R A B]

/--
theorem `mapAlgebra_mapAlgebra` / 定理 `mapAlgebra_mapAlgebra`

English:
theorem mapAlgebra_mapAlgebra
  given: {M : Pic R}
  statement: mapAlgebra A B (mapAlgebra R A M) = mapAlgebra R B M
  proof: mk_eq_mk_iff.mpr ⟨AlgebraTensorModule.congr (.refl ..) (mk.linearEquiv ..) ≪≫ₗ
    AlgebraTensorModule.cancelBaseChange ..⟩

中文:
定理 mapAlgebra_mapAlgebra
  条件: {M : Pic R}
  结论: mapAlgebra A B (mapAlgebra R A M) = mapAlgebra R B M
  证明: mk_eq_mk_iff.mpr ⟨AlgebraTensorModule.congr (.refl ..) (mk.linearEquiv ..) ≪≫ₗ
    AlgebraTensorModule.cancelBaseChange ..⟩

Depends on / 依赖: AlgebraTensorModule, AlgebraTensorModule.cancelBaseChange, AlgebraTensorModule.congr, cancelBaseChange, linearEquiv, mk.linearEquiv, mk_eq_mk_iff, mk_eq_mk_iff.mpr
-/
theorem mapAlgebra_mapAlgebra {M : Pic R} : mapAlgebra A B (mapAlgebra R A M) = mapAlgebra R B M :=
  mk_eq_mk_iff.mpr ⟨AlgebraTensorModule.congr (.refl ..) (mk.linearEquiv ..) ≪≫ₗ
    AlgebraTensorModule.cancelBaseChange ..⟩

/--
theorem `mapAlgebra_comp_mapAlgebra` / 定理 `mapAlgebra_comp_mapAlgebra`

English:
theorem mapAlgebra_comp_mapAlgebra
  statement: (mapAlgebra A B).comp (mapAlgebra R A) = mapAlgebra R B
  proof: by
  ext; rw [MonoidHom.comp_apply, mapAlgebra_mapAlgebra]

中文:
定理 mapAlgebra_comp_mapAlgebra
  结论: (mapAlgebra A B).comp (mapAlgebra R A) = mapAlgebra R B
  证明: by
  ext; rw [MonoidHom.comp_apply, mapAlgebra_mapAlgebra]

Depends on / 依赖: MonoidHom, MonoidHom.comp_apply, comp_apply, mapAlgebra_mapAlgebra
-/
theorem mapAlgebra_comp_mapAlgebra : (mapAlgebra A B).comp (mapAlgebra R A) = mapAlgebra R B := by
  ext; rw [MonoidHom.comp_apply, mapAlgebra_mapAlgebra]

/--
theorem `mapAlgebra_self_apply` / 定理 `mapAlgebra_self_apply`

English:
theorem mapAlgebra_self_apply
  given: {M : Pic R}
  statement: mapAlgebra R R M = M
  proof: mk_eq_iff.mpr ⟨TensorProduct.lid ..⟩

中文:
定理 mapAlgebra_self_apply
  条件: {M : Pic R}
  结论: mapAlgebra R R M = M
  证明: mk_eq_iff.mpr ⟨TensorProduct.lid ..⟩

Depends on / 依赖: TensorProduct, TensorProduct.lid, mk_eq_iff, mk_eq_iff.mpr
-/
theorem mapAlgebra_self_apply {M : Pic R} : mapAlgebra R R M = M :=
  mk_eq_iff.mpr ⟨TensorProduct.lid ..⟩

/--
theorem `mapAlgebra_self` / 定理 `mapAlgebra_self`

English:
theorem mapAlgebra_self
  statement: mapAlgebra R R = .id _
  proof: by ext; exact mapAlgebra_self_apply

中文:
定理 mapAlgebra_self
  结论: mapAlgebra R R = .id _
  证明: by ext; exact mapAlgebra_self_apply

Depends on / 依赖: mapAlgebra_self_apply
-/
theorem mapAlgebra_self : mapAlgebra R R = .id _ := by ext; exact mapAlgebra_self_apply

variable {S T : Type*} [CommSemiring S] [CommSemiring T] (f : R ->+* S) (g : S ->+* T)

/--
Definition of `mapRingHom` / `mapRingHom` 的定义

English:
definition mapRingHom
  signature: : Pic R ->* Pic S
  body: let := f.toAlgebra; mapAlgebra R S

中文:
定义 mapRingHom
  签名: : Pic R ->* Pic S
  定义体: let := f.toAlgebra; mapAlgebra R S

Depends on / 依赖: f.toAlgebra, mapAlgebra, toAlgebra
-/
noncomputable def mapRingHom : Pic R ->* Pic S :=
  let := f.toAlgebra; mapAlgebra R S

/--
theorem `mapRingHom_algebraMap` / 定理 `mapRingHom_algebraMap`

English:
theorem mapRingHom_algebraMap
  statement: mapRingHom (algebraMap R A) = mapAlgebra R A
  proof: by
  rw [mapRingHom]; rw [toAlgebra_algebraMap]

中文:
定理 mapRingHom_algebraMap
  结论: mapRingHom (algebraMap R A) = mapAlgebra R A
  证明: by
  rw [mapRingHom]; rw [toAlgebra_algebraMap]

Depends on / 依赖: mapRingHom, toAlgebra_algebraMap
-/
theorem mapRingHom_algebraMap : mapRingHom (algebraMap R A) = mapAlgebra R A := by
  rw [mapRingHom]; rw [toAlgebra_algebraMap]

variable {f g}

/--
theorem `mapRingHom_comp_mapRingHom` / 定理 `mapRingHom_comp_mapRingHom`

English:
theorem mapRingHom_comp_mapRingHom
  proof: by
  algebraize [f, g, g.comp f]
  simp_rw [mapRingHom, mapAlgebra_comp_mapAlgebra]

中文:
定理 mapRingHom_comp_mapRingHom
  证明: by
  algebraize [f, g, g.comp f]
  simp_rw [mapRingHom, mapAlgebra_comp_mapAlgebra]

Depends on / 依赖: algebraize, g.comp, mapAlgebra_comp_mapAlgebra, mapRingHom, simp_rw
-/
theorem mapRingHom_comp_mapRingHom :
    (mapRingHom g).comp (mapRingHom f) = mapRingHom (g.comp f) := by
  algebraize [f, g, g.comp f]
  simp_rw [mapRingHom, mapAlgebra_comp_mapAlgebra]

/--
theorem `mapRingHom_mapRingHom` / 定理 `mapRingHom_mapRingHom`

English:
theorem mapRingHom_mapRingHom
  given: {M : Pic R}
  proof: congr($mapRingHom_comp_mapRingHom M)

中文:
定理 mapRingHom_mapRingHom
  条件: {M : Pic R}
  证明: congr($mapRingHom_comp_mapRingHom M)

Depends on / 依赖: mapRingHom_comp_mapRingHom
-/
theorem mapRingHom_mapRingHom {M : Pic R} :
    mapRingHom g (mapRingHom f M) = mapRingHom (g.comp f) M :=
  congr($mapRingHom_comp_mapRingHom M)

/--
theorem `mapRingHom_id` / 定理 `mapRingHom_id`

English:
theorem mapRingHom_id
  statement: mapRingHom (.id R) = .id _
  proof: by
  rw [mapRingHom]; rw [mapAlgebra_self]

中文:
定理 mapRingHom_id
  结论: mapRingHom (.id R) = .id _
  证明: by
  rw [mapRingHom]; rw [mapAlgebra_self]

Depends on / 依赖: mapAlgebra_self, mapRingHom
-/
theorem mapRingHom_id : mapRingHom (.id R) = .id _ := by
  rw [mapRingHom]; rw [mapAlgebra_self]

/--
theorem `mapRingHom_id_apply` / 定理 `mapRingHom_id_apply`

English:
theorem mapRingHom_id_apply
  given: {M : Pic R}
  statement: mapRingHom (.id R) M = M
  proof: congr($mapRingHom_id M)

中文:
定理 mapRingHom_id_apply
  条件: {M : Pic R}
  结论: mapRingHom (.id R) M = M
  证明: congr($mapRingHom_id M)

Depends on / 依赖: mapRingHom_id
-/
theorem mapRingHom_id_apply {M : Pic R} : mapRingHom (.id R) M = M :=
  congr($mapRingHom_id M)

/--
Definition of `functor` / `functor` 的定义

English:
definition functor
  signature: : CommSemiRingCat.{u} ⥤ CommGrpCat.{u} where
  body: .of (Pic R)
  map f := CommGrpCat.ofHom (mapRingHom f.hom)
  map_id _ := CommGrpCat.Hom.ext mapRingHom_id
  map_comp _ _ := CommGrpCat.Hom.ext mapRingHom_comp_mapRingHom.symm

中文:
定义 functor
  签名: : 交换Semi环范畴.{u} ⥤ 交换群范畴.{u} where
  定义体: .of (Pic R)
  map f := CommGrpCat.ofHom (mapRingHom f.hom)
  map_id _ := CommGrpCat.Hom.ext mapRingHom_id
  map_comp _ _ := CommGrpCat.Hom.ext mapRingHom_comp_mapRingHom.symm
-/
noncomputable def functor : CommSemiRingCat.{u} ⥤ CommGrpCat.{u} where
  obj R := .of (Pic R)
  map f := CommGrpCat.ofHom (mapRingHom f.hom)
  map_id _ := CommGrpCat.Hom.ext mapRingHom_id
  map_comp _ _ := CommGrpCat.Hom.ext mapRingHom_comp_mapRingHom.symm

end Pic

variable (A : Type*) [CommSemiring A] [Algebra R A]

/--
Definition of `relPic` / `relPic` 的定义

English:
definition relPic
  signature: : Subgroup (Pic R)
  body: (Pic.mapAlgebra R A).ker

中文:
定义 relPic
  签名: : 子群 (Pic R)
  定义体: (Pic.mapAlgebra R A).ker

Depends on / 依赖: Pic.mapAlgebra, mapAlgebra
-/
noncomputable def relPic : Subgroup (Pic R) := (Pic.mapAlgebra R A).ker

/--
theorem `relPic_eq_top` / 定理 `relPic_eq_top`

English:
theorem relPic_eq_top
  given: [Subsingleton (Pic A)]
  statement: relPic R A = ⊤
  proof: top_unique fun _ _ => Subsingleton.elim ..

中文:
定理 relPic_eq_top
  条件: [子单例 (Pic A)]
  结论: relPic R A = ⊤
  证明: top_unique fun _ _ => Subsingleton.elim ..

Depends on / 依赖: Subsingleton, Subsingleton.elim, top_unique
-/
theorem relPic_eq_top [Subsingleton (Pic A)] : relPic R A = ⊤ :=
  top_unique fun _ _ => Subsingleton.elim ..

end CommRing

end PicardGroup

namespace Module.Invertible

variable [Module.Invertible R M]

/--
theorem `tensorProductComm_eq_refl` / 定理 `tensorProductComm_eq_refl`

English:
theorem tensorProductComm_eq_refl
  statement: TensorProduct.comm R M M = .refl ..
  proof: by
  let f (P : Ideal R) [P.IsMaximal] := LocalizedModule.mkLinearMap P.primeCompl M
  let ff (P : Ideal R) [P.IsMaximal] := TensorProduct.map (f P) (f P)
refine LinearEquiv.toLinearMap_injective LinearMap.eq_of_localization_maximal _ ff _ ff _ _
    fun P _ => .trans (b := (TensorProduct.comm ..).toLinearMap) ?_ ?_
  · apply IsLocalizedModule.linearMap_ext P.primeCompl (ff P) (ff P)
    ext; exact IsLocalizedModule.map_apply _ (ff P) ..
  let Rp := Localization P.primeCompl
  have ⟨e⟩ := free_iff_linearEquiv.mp (inferInstance : Free Rp (LocalizedModule P.primeCompl M))
  have e := e.restrictScalars R
  ext x y
  refine (congr e e ≪≫ₗ equivOfCompatibleSMul Rp ..).injective ?_
  suffices e y otimesₜ[Rp] e x = e x otimesₜ e y by simpa [equivOfCompatibleSMul]
  conv_lhs => rw [← mul_one (e y), ← smul_eq_mul, smul_tmul, smul_eq_mul,
    mul_comm, ← smul_eq_mul, ← smul_tmul, smul_eq_mul, mul_one]

中文:
定理 tensorProductComm_eq_refl
  结论: 张量积.comm R M M = .refl ..
  证明: by
  let f (P : Ideal R) [P.IsMaximal] := LocalizedModule.mkLinearMap P.primeCompl M
  let ff (P : Ideal R) [P.IsMaximal] := TensorProduct.map (f P) (f P)
refine LinearEquiv.toLinearMap_injective LinearMap.eq_of_localization_maximal _ ff _ ff _ _
    fun P _ => .trans (b := (TensorProduct.comm ..).toLinearMap) ?_ ?_
  · apply IsLocalizedModule.linearMap_ext P.primeCompl (ff P) (ff P)
    ext; exact IsLocalizedModule.map_apply _ (ff P) ..
  let Rp := Localization P.primeCompl
  have ⟨e⟩ := free_iff_linearEquiv.mp (inferInstance : Free Rp (LocalizedModule P.primeCompl M))
  have e := e.restrictScalars R
  ext x y
  refine (congr e e ≪≫ₗ equivOfCompatibleSMul Rp ..).injective ?_
  suffices e y otimesₜ[Rp] e x = e x otimesₜ e y by simpa [equivOfCompatibleSMul]
  conv_lhs => rw [← mul_one (e y), ← smul_eq_mul, smul_tmul, smul_eq_mul,
    mul_comm, ← smul_eq_mul, ← smul_tmul, smul_eq_mul, mul_one]

Depends on / 依赖: IsLocalizedModule, IsLocalizedModule.linearMap_ext, IsLocalizedModule.map_apply, IsMaximal, LinearEquiv, LinearEquiv.toLinearMap_injective, LinearMap, LinearMap.eq_of_localization_maximal, Localization, LocalizedModule, LocalizedModule.mkLinearMap, P.IsMaximal, P.primeCompl, TensorProduct, TensorProduct.comm, TensorProduct.map, eq_of_localization_maximal, free_iff_linearEquiv, free_iff_linearEquiv.mp, linearMap_ext
-/
theorem tensorProductComm_eq_refl : TensorProduct.comm R M M = .refl .. := by
  let f (P : Ideal R) [P.IsMaximal] := LocalizedModule.mkLinearMap P.primeCompl M
  let ff (P : Ideal R) [P.IsMaximal] := TensorProduct.map (f P) (f P)
refine LinearEquiv.toLinearMap_injective LinearMap.eq_of_localization_maximal _ ff _ ff _ _
    fun P _ => .trans (b := (TensorProduct.comm ..).toLinearMap) ?_ ?_
  · apply IsLocalizedModule.linearMap_ext P.primeCompl (ff P) (ff P)
    ext; exact IsLocalizedModule.map_apply _ (ff P) ..
  let Rp := Localization P.primeCompl
  have ⟨e⟩ := free_iff_linearEquiv.mp (inferInstance : Free Rp (LocalizedModule P.primeCompl M))
  have e := e.restrictScalars R
  ext x y
  refine (congr e e ≪≫ₗ equivOfCompatibleSMul Rp ..).injective ?_
  suffices e y otimesₜ[Rp] e x = e x otimesₜ e y by simpa [equivOfCompatibleSMul]
  conv_lhs => rw [← mul_one (e y), ← smul_eq_mul, smul_tmul, smul_eq_mul,
    mul_comm, ← smul_eq_mul, ← smul_tmul, smul_eq_mul, mul_one]

variable {R M} in
/--
theorem `tmul_comm` / 定理 `tmul_comm`

English:
theorem tmul_comm
  given: {m₁ m₂ : M}
  statement: m₁ otimesₜ[R] m₂ = m₂ otimesₜ m₁
  proof: DFunLike.congr_fun (tensorProductComm_eq_refl ..) (m₂ otimesₜ m₁)

中文:
定理 tmul_comm
  条件: {m₁ m₂ : M}
  结论: m₁ otimesₜ[R] m₂ = m₂ otimesₜ m₁
  证明: DFunLike.congr_fun (tensorProductComm_eq_refl ..) (m₂ otimesₜ m₁)

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun, tensorProductComm_eq_refl
-/
theorem tmul_comm {m₁ m₂ : M} : m₁ otimesₜ[R] m₂ = m₂ otimesₜ m₁ :=
  DFunLike.congr_fun (tensorProductComm_eq_refl ..) (m₂ otimesₜ m₁)

end Module.Invertible

namespace Submodule

open Module Invertible

variable {R M A}

section Semiring

variable [Semiring A] [Algebra R A] [FaithfulSMul R A]

open LinearMap in
set_option backward.privateInPublic true in
/--
theorem `projective_units_and_mul'_comp_lTensor_bijective` / 定理 `projective_units_and_mul'_comp_lTensor_bijective`

English:
theorem projective_units_and_mul'_comp_lTensor_bijective
  given: (I : (Submodule R A)ˣ)
  proof: by
  obtain ⟨T, T', hT, hT', one_mem⟩ := mem_span_mul_finite_of_mem_mul (I.inv_mul ▸ one_le.mp le_rfl)
  classical
  rw [← Set.image2_mul]; rw [← Finset.coe_image₂]; rw [mem_span_finset] at one_mem
  set S := T.image₂ (· * ·) T'
  obtain ⟨r, hr⟩ := one_mem
  choose a ha b hb eq using fun i : S => Finset.mem_image₂.mp i.2
  let f : I ->ₗ[R] S -> R := .pi fun i => (LinearEquiv.ofInjective
      (Algebra.linearMap R A) (FaithfulSMul.algebraMap_injective R A)).symm.comp <|
    restrict (mulRight R (r i • a i)) fun x hx => by
      rw [← one_eq_range]; rw [← I.mul_inv]; exact mul_mem_mul hx (I⁻¹.1.smul_mem _ <| hT <| ha i)
  have hf (x : I.1) (i : S) : algebraMap R A (f x i) = x * r i • a i := by
    dsimp [f, ← Algebra.linearMap_apply]
    exact LinearEquiv.ofInjective_symm_apply ..
let g : (S -> R) ->ₗ[R] I := .lsum _ _ Nat fun i => .toSpanSingleton _ _ ⟨b i, hT' hb i⟩
have hgf : g ∘ₗ f = .id := LinearMap.ext fun x => Subtype.ext by
    simp only [g, lsum_apply, comp_apply, LinearMap.sum_apply, toSpanSingleton_apply, proj_apply]
    simp_rw [coe_sum, coe_smul, Algebra.smul_def, hf, mul_assoc, ← Finset.mul_sum,
      Algebra.smul_mul_assoc, eq, (Finset.sum_coe_sort ..).trans hr.2, mul_one, id_apply]
  set m := mul' R A ∘ₗ I.1.subtype.lTensor A
  have eq : (piScalarRight R R A S).toLinearMap ∘ₗ f.lTensor A =
      (.pi fun i : S => mulRight R (r i • a i)) ∘ₗ m := by
    ext; simp [(Algebra.smul_def ..).trans (Algebra.commutes ..), hf, m, mul_assoc]
have := (piScalarRight R R A S).injective.comp injective_of_comp_eq_id
(f.lTensor A) (g.lTensor A) by rw [← lTensor_comp, hgf, lTensor_id]
  rw [← LinearEquiv.coe_toLinearMap]; rw [← coe_comp]; rw [eq]; rw [coe_comp] at this
  refine ⟨.of_split f g hgf, .of_comp this, range_eq_top.mp ?_⟩
  rw [show m = mulMap ⊤ I ∘ₗ (topEquiv.symm.rTensor I.1).toLinearMap by ext; rfl]; rw [range_comp]; rw [LinearEquiv.range]; rw [map_top]; rw [mulMap_range]; rw [top_mul_eq_top_of_mul_eq_one I.inv_mul]

中文:
定理 projective_units_and_mul'_comp_lTensor_bijective
  条件: (I : (子模 R A)ˣ)
  证明: by
  obtain ⟨T, T', hT, hT', one_mem⟩ := mem_span_mul_finite_of_mem_mul (I.inv_mul ▸ one_le.mp le_rfl)
  classical
  rw [← Set.image2_mul]; rw [← Finset.coe_image₂]; rw [mem_span_finset] at one_mem
  set S := T.image₂ (· * ·) T'
  obtain ⟨r, hr⟩ := one_mem
  choose a ha b hb eq using fun i : S => Finset.mem_image₂.mp i.2
  let f : I ->ₗ[R] S -> R := .pi fun i => (LinearEquiv.ofInjective
      (Algebra.linearMap R A) (FaithfulSMul.algebraMap_injective R A)).symm.comp <|
    restrict (mulRight R (r i • a i)) fun x hx => by
      rw [← one_eq_range]; rw [← I.mul_inv]; exact mul_mem_mul hx (I⁻¹.1.smul_mem _ <| hT <| ha i)
  have hf (x : I.1) (i : S) : algebraMap R A (f x i) = x * r i • a i := by
    dsimp [f, ← Algebra.linearMap_apply]
    exact LinearEquiv.ofInjective_symm_apply ..
let g : (S -> R) ->ₗ[R] I := .lsum _ _ Nat fun i => .toSpanSingleton _ _ ⟨b i, hT' hb i⟩
have hgf : g ∘ₗ f = .id := LinearMap.ext fun x => Subtype.ext by
    simp only [g, lsum_apply, comp_apply, LinearMap.sum_apply, toSpanSingleton_apply, proj_apply]
    simp_rw [coe_sum, coe_smul, Algebra.smul_def, hf, mul_assoc, ← Finset.mul_sum,
      Algebra.smul_mul_assoc, eq, (Finset.sum_coe_sort ..).trans hr.2, mul_one, id_apply]
  set m := mul' R A ∘ₗ I.1.subtype.lTensor A
  have eq : (piScalarRight R R A S).toLinearMap ∘ₗ f.lTensor A =
      (.pi fun i : S => mulRight R (r i • a i)) ∘ₗ m := by
    ext; simp [(Algebra.smul_def ..).trans (Algebra.commutes ..), hf, m, mul_assoc]
have := (piScalarRight R R A S).injective.comp injective_of_comp_eq_id
(f.lTensor A) (g.lTensor A) by rw [← lTensor_comp, hgf, lTensor_id]
  rw [← LinearEquiv.coe_toLinearMap]; rw [← coe_comp]; rw [eq]; rw [coe_comp] at this
  refine ⟨.of_split f g hgf, .of_comp this, range_eq_top.mp ?_⟩
  rw [show m = mulMap ⊤ I ∘ₗ (topEquiv.symm.rTensor I.1).toLinearMap by ext; rfl]; rw [range_comp]; rw [LinearEquiv.range]; rw [map_top]; rw [mulMap_range]; rw [top_mul_eq_top_of_mul_eq_one I.inv_mul]
-/
private theorem projective_units_and_mul'_comp_lTensor_bijective (I : (Submodule R A)ˣ) :
    Projective R I ∧ Function.Bijective (mul' R A ∘ₗ I.1.subtype.lTensor A) := by
  obtain ⟨T, T', hT, hT', one_mem⟩ := mem_span_mul_finite_of_mem_mul (I.inv_mul ▸ one_le.mp le_rfl)
  classical
  rw [← Set.image2_mul]; rw [← Finset.coe_image₂]; rw [mem_span_finset] at one_mem
  set S := T.image₂ (· * ·) T'
  obtain ⟨r, hr⟩ := one_mem
  choose a ha b hb eq using fun i : S => Finset.mem_image₂.mp i.2
  let f : I ->ₗ[R] S -> R := .pi fun i => (LinearEquiv.ofInjective
      (Algebra.linearMap R A) (FaithfulSMul.algebraMap_injective R A)).symm.comp <|
    restrict (mulRight R (r i • a i)) fun x hx => by
      rw [← one_eq_range]; rw [← I.mul_inv]; exact mul_mem_mul hx (I⁻¹.1.smul_mem _ <| hT <| ha i)
  have hf (x : I.1) (i : S) : algebraMap R A (f x i) = x * r i • a i := by
    dsimp [f, ← Algebra.linearMap_apply]
    exact LinearEquiv.ofInjective_symm_apply ..
let g : (S -> R) ->ₗ[R] I := .lsum _ _ Nat fun i => .toSpanSingleton _ _ ⟨b i, hT' hb i⟩
have hgf : g ∘ₗ f = .id := LinearMap.ext fun x => Subtype.ext by
    simp only [g, lsum_apply, comp_apply, LinearMap.sum_apply, toSpanSingleton_apply, proj_apply]
    simp_rw [coe_sum, coe_smul, Algebra.smul_def, hf, mul_assoc, ← Finset.mul_sum,
      Algebra.smul_mul_assoc, eq, (Finset.sum_coe_sort ..).trans hr.2, mul_one, id_apply]
  set m := mul' R A ∘ₗ I.1.subtype.lTensor A
  have eq : (piScalarRight R R A S).toLinearMap ∘ₗ f.lTensor A =
      (.pi fun i : S => mulRight R (r i • a i)) ∘ₗ m := by
    ext; simp [(Algebra.smul_def ..).trans (Algebra.commutes ..), hf, m, mul_assoc]
have := (piScalarRight R R A S).injective.comp injective_of_comp_eq_id
(f.lTensor A) (g.lTensor A) by rw [← lTensor_comp, hgf, lTensor_id]
  rw [← LinearEquiv.coe_toLinearMap]; rw [← coe_comp]; rw [eq]; rw [coe_comp] at this
  refine ⟨.of_split f g hgf, .of_comp this, range_eq_top.mp ?_⟩
  rw [show m = mulMap ⊤ I ∘ₗ (topEquiv.symm.rTensor I.1).toLinearMap by ext; rfl]; rw [range_comp]; rw [LinearEquiv.range]; rw [map_top]; rw [mulMap_range]; rw [top_mul_eq_top_of_mul_eq_one I.inv_mul]

open LinearMap in
/--
Instance `projective_units` / 实例 `projective_units`

English:
instance projective_units
  signature: (I : (Submodule R A)ˣ)
  body: (projective_units_and_mul'_comp_lTensor_bijective I).1

中文:
实例 projective_units
  签名: (I : (子模 R A)ˣ)
  定义体: (projective_units_and_mul'_comp_lTensor_bijective I).1

Depends on / 依赖: _comp_lTensor_bijective, projective_units_and_mul
-/
instance projective_units (I : (Submodule R A)ˣ) : Projective R I :=
  (projective_units_and_mul'_comp_lTensor_bijective I).1

/--
theorem `projective_of_isUnit` / 定理 `projective_of_isUnit`

English:
theorem projective_of_isUnit
  given: {I : Submodule R A} (hI : IsUnit I)
  statement: Projective R I
  proof: projective_units hI.unit

中文:
定理 projective_of_isUnit
  条件: {I : 子模 R A} (hI : 是单位 I)
  结论: 投射 R I
  证明: projective_units hI.unit

Depends on / 依赖: hI.unit, projective_units
-/
theorem projective_of_isUnit {I : Submodule R A} (hI : IsUnit I) : Projective R I :=
  projective_units hI.unit

variable (I J : (Submodule R A)ˣ)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Definition of `tensorEquivMul` / `tensorEquivMul` 的定义

English:
definition tensorEquivMul
  signature: : I otimes[R] J ≃ₗ[R] I * J
  body: by
  refine .ofBijective _ ⟨.of_comp (f := Submodule.subtype _) ?_, mulMap'_surjective _ _⟩
  convert!
    (projective_units_and_mul'_comp_lTensor_bijective J).2.1.comp
      (Flat.rTensor_preserves_injective_linearMap _ I.1.subtype_injective)
  simp_rw [← LinearMap.coe_comp]
  congr 1; ext; rfl

中文:
定义 tensorEquivMul
  签名: : I otimes[R] J ≃ₗ[R] I * J
  定义体: by
  refine .ofBijective _ ⟨.of_comp (f := Submodule.subtype _) ?_, mulMap'_surjective _ _⟩
  convert!
    (projective_units_and_mul'_comp_lTensor_bijective J).2.1.comp
      (Flat.rTensor_preserves_injective_linearMap _ I.1.subtype_injective)
  simp_rw [← LinearMap.coe_comp]
  congr 1; ext; rfl

Depends on / 依赖: Flat.rTensor_preserves_injective_linearMap, LinearMap, LinearMap.coe_comp, Submodule, Submodule.subtype, _comp_lTensor_bijective, _surjective, coe_comp, convert, mulMap, ofBijective, of_comp, projective_units_and_mul, rTensor_preserves_injective_linearMap, simp_rw, subtype, subtype_injective
-/
noncomputable def tensorEquivMul : I otimes[R] J ≃ₗ[R] I * J := by
  refine .ofBijective _ ⟨.of_comp (f := Submodule.subtype _) ?_, mulMap'_surjective _ _⟩
  convert!
    (projective_units_and_mul'_comp_lTensor_bijective J).2.1.comp
      (Flat.rTensor_preserves_injective_linearMap _ I.1.subtype_injective)
  simp_rw [← LinearMap.coe_comp]
  congr 1; ext; rfl

/--
Definition of `tensorInvEquiv` / `tensorInvEquiv` 的定义

English:
definition tensorInvEquiv
  signature: : I otimes[R] ↑I⁻¹ ≃ₗ[R] R
  body: tensorEquivMul I _ ≪≫ₗ .ofEq _ _ (I.mul_inv.trans one_eq_range) ≪≫ₗ
    .symm (.ofInjective _ (FaithfulSMul.algebraMap_injective R A))

中文:
定义 tensorInvEquiv
  签名: : I otimes[R] ↑I⁻¹ ≃ₗ[R] R
  定义体: tensorEquivMul I _ ≪≫ₗ .ofEq _ _ (I.mul_inv.trans one_eq_range) ≪≫ₗ
    .symm (.ofInjective _ (FaithfulSMul.algebraMap_injective R A))

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, I.mul_inv.trans, algebraMap_injective, mul_inv, ofInjective, one_eq_range, tensorEquivMul
-/
noncomputable def tensorInvEquiv : I otimes[R] ↑I⁻¹ ≃ₗ[R] R :=
  tensorEquivMul I _ ≪≫ₗ .ofEq _ _ (I.mul_inv.trans one_eq_range) ≪≫ₗ
    .symm (.ofInjective _ (FaithfulSMul.algebraMap_injective R A))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module.Invertible R I
  body: .left (tensorInvEquiv I)

中文:
实例 :
  签名: 模.可逆 R I
  定义体: .left (tensorInvEquiv I)

Depends on / 依赖: tensorInvEquiv
-/
instance : Module.Invertible R I := .left (tensorInvEquiv I)

open CommRing Pic

variable (R A) in
/--
Definition of `unitsToPic` / `unitsToPic` 的定义

English:
definition unitsToPic
  signature: : (Submodule R A)ˣ ->* Pic R where
  body: Pic.mk R I
  map_one' := mk_eq_one_iff.mpr
    ⟨.ofEq _ _ one_eq_range ≪≫ₗ .symm (.ofInjective _ (FaithfulSMul.algebraMap_injective R A))⟩
  map_mul' I J := by rw [← mk_tensor, mk_eq_mk_iff]; exact ⟨(tensorEquivMul I J).symm⟩

中文:
定义 unitsToPic
  签名: : (子模 R A)ˣ ->* Pic R where
  定义体: Pic.mk R I
  map_one' := mk_eq_one_iff.mpr
    ⟨.ofEq _ _ one_eq_range ≪≫ₗ .symm (.ofInjective _ (FaithfulSMul.algebraMap_injective R A))⟩
  map_mul' I J := by rw [← mk_tensor, mk_eq_mk_iff]; exact ⟨(tensorEquivMul I J).symm⟩
-/
@[simps] noncomputable def unitsToPic : (Submodule R A)ˣ ->* Pic R where
  toFun I := Pic.mk R I
  map_one' := mk_eq_one_iff.mpr
    ⟨.ofEq _ _ one_eq_range ≪≫ₗ .symm (.ofInjective _ (FaithfulSMul.algebraMap_injective R A))⟩
  map_mul' I J := by rw [← mk_tensor, mk_eq_mk_iff]; exact ⟨(tensorEquivMul I J).symm⟩

/--
Definition of `unitsToPicEquiv` / `unitsToPicEquiv` 的定义

English:
definition unitsToPicEquiv
  signature: (I : (Submodule R A)ˣ)
  body: (mk_eq_iff.mp rfl).some.symm

中文:
定义 unitsToPicEquiv
  签名: (I : (子模 R A)ˣ)
  定义体: (mk_eq_iff.mp rfl).some.symm

Depends on / 依赖: mk_eq_iff, mk_eq_iff.mp, some.symm
-/
noncomputable def unitsToPicEquiv (I : (Submodule R A)ˣ) : unitsToPic R A I ≃ₗ[R] I :=
  (mk_eq_iff.mp rfl).some.symm

variable (R A)

/--
theorem `ker_unitsToPic` / 定理 `ker_unitsToPic`

English:
theorem ker_unitsToPic
  proof: by
  ext I; constructor <;> intro h
  · have e := (mk_eq_one_iff.mp h).some.symm
    have e' := (mk_eq_one_iff.mp (inv_mem h)).some.symm
    have h := eq_span_singleton_of_surjective e.surjective
    have h' := eq_span_singleton_of_surjective e'.surjective
    refine ⟨(isUnit_iff_exists_and_exists.mpr ⟨?_, ?_⟩).unit, Units.ext h.symm⟩
    · have : span R {(e 1).1 * e' 1} = 1 := by simpa [span_mul_span] using congr($h * $h').symm
      have ⟨r, hr⟩ := span_singleton_eq_one_iff.mp this
      exact ⟨e' 1 * algebraMap R A r.inv, by simp [← mul_assoc, hr, ← map_mul]⟩
    · have : span R {(e' 1).1 * e 1} = 1 := by simpa [span_mul_span] using congr($h' * $h).symm
      have ⟨r, hr⟩ := span_singleton_eq_one_iff.mp this
      exact ⟨algebraMap R A r.inv * e' 1, by simp [mul_assoc, hr, ← map_mul]⟩
  · obtain ⟨x, rfl⟩ := h
exact mk_eq_one_iff.mpr ⟨.symm (.ofInjective (LinearMap.toSpanSingleton R A x) fun _ _ eq =>
(faithfulSMul_iff_injective_smul_one R A).mp ‹_› by simpa using congr($eq * x.inv)) ≪≫ₗ
      .ofEq _ _ (by ext; simp [mem_span_singleton])⟩

中文:
定理 ker_unitsToPic
  证明: by
  ext I; constructor <;> intro h
  · have e := (mk_eq_one_iff.mp h).some.symm
    have e' := (mk_eq_one_iff.mp (inv_mem h)).some.symm
    have h := eq_span_singleton_of_surjective e.surjective
    have h' := eq_span_singleton_of_surjective e'.surjective
    refine ⟨(isUnit_iff_exists_and_exists.mpr ⟨?_, ?_⟩).unit, Units.ext h.symm⟩
    · have : span R {(e 1).1 * e' 1} = 1 := by simpa [span_mul_span] using congr($h * $h').symm
      have ⟨r, hr⟩ := span_singleton_eq_one_iff.mp this
      exact ⟨e' 1 * algebraMap R A r.inv, by simp [← mul_assoc, hr, ← map_mul]⟩
    · have : span R {(e' 1).1 * e 1} = 1 := by simpa [span_mul_span] using congr($h' * $h).symm
      have ⟨r, hr⟩ := span_singleton_eq_one_iff.mp this
      exact ⟨algebraMap R A r.inv * e' 1, by simp [mul_assoc, hr, ← map_mul]⟩
  · obtain ⟨x, rfl⟩ := h
exact mk_eq_one_iff.mpr ⟨.symm (.ofInjective (LinearMap.toSpanSingleton R A x) fun _ _ eq =>
(faithfulSMul_iff_injective_smul_one R A).mp ‹_› by simpa using congr($eq * x.inv)) ≪≫ₗ
      .ofEq _ _ (by ext; simp [mem_span_singleton])⟩

Depends on / 依赖: Units.ext, algebraMap, e.surjective, eq_span_singleton_of_surjective, h.symm, inv_mem, isUnit_iff_exists_and_exists, isUnit_iff_exists_and_exists.mpr, mk_eq_one_iff, mk_eq_one_iff.mp, r.inv, some.symm, span_mul_span, span_singleton_eq_one_iff, span_singleton_eq_one_iff.mp, surjective
-/
theorem ker_unitsToPic :
    (unitsToPic R A).ker = (Units.map (spanSingleton R).toMonoidHom).range := by
  ext I; constructor <;> intro h
  · have e := (mk_eq_one_iff.mp h).some.symm
    have e' := (mk_eq_one_iff.mp (inv_mem h)).some.symm
    have h := eq_span_singleton_of_surjective e.surjective
    have h' := eq_span_singleton_of_surjective e'.surjective
    refine ⟨(isUnit_iff_exists_and_exists.mpr ⟨?_, ?_⟩).unit, Units.ext h.symm⟩
    · have : span R {(e 1).1 * e' 1} = 1 := by simpa [span_mul_span] using congr($h * $h').symm
      have ⟨r, hr⟩ := span_singleton_eq_one_iff.mp this
      exact ⟨e' 1 * algebraMap R A r.inv, by simp [← mul_assoc, hr, ← map_mul]⟩
    · have : span R {(e' 1).1 * e 1} = 1 := by simpa [span_mul_span] using congr($h' * $h).symm
      have ⟨r, hr⟩ := span_singleton_eq_one_iff.mp this
      exact ⟨algebraMap R A r.inv * e' 1, by simp [mul_assoc, hr, ← map_mul]⟩
  · obtain ⟨x, rfl⟩ := h
exact mk_eq_one_iff.mpr ⟨.symm (.ofInjective (LinearMap.toSpanSingleton R A x) fun _ _ eq =>
(faithfulSMul_iff_injective_smul_one R A).mp ‹_› by simpa using congr($eq * x.inv)) ≪≫ₗ
      .ofEq _ _ (by ext; simp [mem_span_singleton])⟩

/--
theorem `mulExact_unitsMap_spanSingleton_unitsToPic` / 定理 `mulExact_unitsMap_spanSingleton_unitsToPic`

English:
theorem mulExact_unitsMap_spanSingleton_unitsToPic
  proof: MonoidHom.mulExact_iff.mpr (ker_unitsToPic R A)

中文:
定理 mulExact_unitsMap_spanSingleton_unitsToPic
  证明: MonoidHom.mulExact_iff.mpr (ker_unitsToPic R A)

Depends on / 依赖: MonoidHom, MonoidHom.mulExact_iff.mpr, ker_unitsToPic, mulExact_iff
-/
theorem mulExact_unitsMap_spanSingleton_unitsToPic :
    Function.MulExact (Units.map (spanSingleton R).toMonoidHom) (unitsToPic R A) :=
  MonoidHom.mulExact_iff.mpr (ker_unitsToPic R A)

end Semiring

end Submodule

namespace Module.Flat

variable {R M A} [Semiring A] [Algebra R A] (e : A otimes[R] M ≃ₗ[A] A)

/--
Definition of `toAlgebra` / `toAlgebra` 的定义

English:
definition toAlgebra
  signature: : M ->ₗ[R] A
  body: e.restrictScalars R ∘ₗ (Algebra.ofId R A).toLinearMap.rTensor M ∘ₗ (TensorProduct.lid R M).symm

中文:
定义 toAlgebra
  签名: : M ->ₗ[R] A
  定义体: e.restrictScalars R ∘ₗ (Algebra.ofId R A).toLinearMap.rTensor M ∘ₗ (TensorProduct.lid R M).symm

Depends on / 依赖: Algebra, Algebra.ofId, TensorProduct, TensorProduct.lid, e.restrictScalars, rTensor, restrictScalars, toLinearMap, toLinearMap.rTensor
-/
noncomputable def toAlgebra : M ->ₗ[R] A :=
  e.restrictScalars R ∘ₗ (Algebra.ofId R A).toLinearMap.rTensor M ∘ₗ (TensorProduct.lid R M).symm

variable [Flat R M] [FaithfulSMul R A]

/--
theorem `toAlgebra_injective` / 定理 `toAlgebra_injective`

English:
theorem toAlgebra_injective
  statement: Function.Injective (toAlgebra e)
  proof: by
  simpa [toAlgebra] using
    Flat.rTensor_preserves_injective_linearMap _ (FaithfulSMul.algebraMap_injective R A)

中文:
定理 toAlgebra_injective
  结论: 函数.单射 (toAlgebra e)
  证明: by
  simpa [toAlgebra] using
    Flat.rTensor_preserves_injective_linearMap _ (FaithfulSMul.algebraMap_injective R A)

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, Flat.rTensor_preserves_injective_linearMap, algebraMap_injective, rTensor_preserves_injective_linearMap, toAlgebra
-/
theorem toAlgebra_injective : Function.Injective (toAlgebra e) := by
  simpa [toAlgebra] using
    Flat.rTensor_preserves_injective_linearMap _ (FaithfulSMul.algebraMap_injective R A)

/--
Definition of `submoduleAlgebra` / `submoduleAlgebra` 的定义

English:
abbreviation submoduleAlgebra
  signature: : Submodule R A
  body: LinearMap.range (toAlgebra e)

中文:
缩写 submoduleAlgebra
  签名: : 子模 R A
  定义体: LinearMap.range (toAlgebra e)

Depends on / 依赖: LinearMap, LinearMap.range, toAlgebra
-/
noncomputable abbrev submoduleAlgebra : Submodule R A := LinearMap.range (toAlgebra e)

/--
Definition of `submoduleAlgebraEquiv` / `submoduleAlgebraEquiv` 的定义

English:
definition submoduleAlgebraEquiv
  signature: : submoduleAlgebra e ≃ₗ[R] M
  body: .symm .ofInjective _ (toAlgebra_injective e)

中文:
定义 submoduleAlgebraEquiv
  签名: : submoduleAlgebra e ≃ₗ[R] M
  定义体: .symm .ofInjective _ (toAlgebra_injective e)

Depends on / 依赖: ofInjective, toAlgebra_injective
-/
noncomputable def submoduleAlgebraEquiv : submoduleAlgebra e ≃ₗ[R] M :=
.symm .ofInjective _ (toAlgebra_injective e)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Flat R (submoduleAlgebra e)
  body: .of_linearEquiv (submoduleAlgebraEquiv e)

中文:
实例 :
  签名: 平坦 R (submoduleAlgebra e)
  定义体: .of_linearEquiv (submoduleAlgebraEquiv e)

Depends on / 依赖: of_linearEquiv, submoduleAlgebraEquiv
-/
instance : Flat R (submoduleAlgebra e) := .of_linearEquiv (submoduleAlgebraEquiv e)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Module.Invertible
  signature: R M] : Module.Invertible R (submoduleAlgebra e)
  body: .congr (submoduleAlgebraEquiv e).symm

中文:
实例 [模.可逆
  签名: R M] : 模.可逆 R (submoduleAlgebra e)
  定义体: .congr (submoduleAlgebraEquiv e).symm

Depends on / 依赖: submoduleAlgebraEquiv
-/
instance [Module.Invertible R M] : Module.Invertible R (submoduleAlgebra e) :=
  .congr (submoduleAlgebraEquiv e).symm

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `tensorSubmoduleAlgebraEquiv` / `tensorSubmoduleAlgebraEquiv` 的定义

English:
definition tensorSubmoduleAlgebraEquiv
  signature: : A otimes[R] submoduleAlgebra e ≃ₗ[A] A
  body: .ofBijective (.mul'' R A ∘ₗ AlgebraTensorModule.lTensor A A (Submodule.subtype _)) by
    convert! (AlgebraTensorModule.congr (.refl ..) (submoduleAlgebraEquiv e) ≪≫ₗ e).bijective
    ext x
    refine x.induction_on (by simp) ?_ (by simp +contextual)
    intro a x
    obtain ⟨m, rfl⟩ := (submoduleAlgebraEquiv e).symm.surjective x
    suffices a * toAlgebra e m = e (a otimesₜ[R] m) by simpa using! this
    dsimp [toAlgebra]
    rw [map_one]; rw [← smul_eq_mul]; rw [← map_smul]; rw [smul_tmul']; rw [smul_eq_mul]; rw [mul_one]

中文:
定义 tensorSubmoduleAlgebraEquiv
  签名: : A otimes[R] submoduleAlgebra e ≃ₗ[A] A
  定义体: .ofBijective (.mul'' R A ∘ₗ AlgebraTensorModule.lTensor A A (Submodule.subtype _)) by
    convert! (AlgebraTensorModule.congr (.refl ..) (submoduleAlgebraEquiv e) ≪≫ₗ e).bijective
    ext x
    refine x.induction_on (by simp) ?_ (by simp +contextual)
    intro a x
    obtain ⟨m, rfl⟩ := (submoduleAlgebraEquiv e).symm.surjective x
    suffices a * toAlgebra e m = e (a otimesₜ[R] m) by simpa using! this
    dsimp [toAlgebra]
    rw [map_one]; rw [← smul_eq_mul]; rw [← map_smul]; rw [smul_tmul']; rw [smul_eq_mul]; rw [mul_one]

Depends on / 依赖: AlgebraTensorModule, AlgebraTensorModule.congr, AlgebraTensorModule.lTensor, Submodule, Submodule.subtype, bijective, contextual, convert, induction_on, lTensor, map_one, map_smul, mul_one, ofBijective, smul_eq_mul, smul_tmul, submoduleAlgebraEquiv, subtype, surjective, symm.surjective
-/
noncomputable def tensorSubmoduleAlgebraEquiv : A otimes[R] submoduleAlgebra e ≃ₗ[A] A :=
.ofBijective (.mul'' R A ∘ₗ AlgebraTensorModule.lTensor A A (Submodule.subtype _)) by
    convert! (AlgebraTensorModule.congr (.refl ..) (submoduleAlgebraEquiv e) ≪≫ₗ e).bijective
    ext x
    refine x.induction_on (by simp) ?_ (by simp +contextual)
    intro a x
    obtain ⟨m, rfl⟩ := (submoduleAlgebraEquiv e).symm.surjective x
    suffices a * toAlgebra e m = e (a otimesₜ[R] m) by simpa using! this
    dsimp [toAlgebra]
    rw [map_one]; rw [← smul_eq_mul]; rw [← map_smul]; rw [smul_tmul']; rw [smul_eq_mul]; rw [mul_one]

/--
theorem `top_mul_submoduleAlgebra` / 定理 `top_mul_submoduleAlgebra`

English:
theorem top_mul_submoduleAlgebra
  statement: ⊤ * submoduleAlgebra e = ⊤
  proof: by
  rw [← Submodule.mulMap_range]
  convert!
    (Submodule.topEquiv.rTensor _ ≪≫ₗ (tensorSubmoduleAlgebraEquiv e).restrictScalars R).range
  ext; rfl

中文:
定理 top_mul_submoduleAlgebra
  结论: ⊤ * submoduleAlgebra e = ⊤
  证明: by
  rw [← Submodule.mulMap_range]
  convert!
    (Submodule.topEquiv.rTensor _ ≪≫ₗ (tensorSubmoduleAlgebraEquiv e).restrictScalars R).range
  ext; rfl

Depends on / 依赖: Submodule, Submodule.mulMap_range, Submodule.topEquiv.rTensor, convert, mulMap_range, rTensor, restrictScalars, tensorSubmoduleAlgebraEquiv, topEquiv
-/
theorem top_mul_submoduleAlgebra : ⊤ * submoduleAlgebra e = ⊤ := by
  rw [← Submodule.mulMap_range]
  convert!
    (Submodule.topEquiv.rTensor _ ≪≫ₗ (tensorSubmoduleAlgebraEquiv e).restrictScalars R).range
  ext; rfl

/--
Definition of `tensorSubmoduleAlgebraEquivMul` / `tensorSubmoduleAlgebraEquivMul` 的定义

English:
definition tensorSubmoduleAlgebraEquivMul
  signature: (I : Submodule R A)
  body: by
  refine .ofBijective _ ⟨.of_comp (f := Submodule.subtype _) ?_, Submodule.mulMap'_surjective _ _⟩
  convert!
    ((tensorSubmoduleAlgebraEquiv e).restrictScalars R).injective.comp
      (Flat.rTensor_preserves_injective_linearMap _ I.subtype_injective)
  simp_rw [← LinearEquiv.coe_toLinearMap, ← LinearMap.coe_comp]
  congr 1; ext; rfl

中文:
定义 tensorSubmoduleAlgebraEquivMul
  签名: (I : 子模 R A)
  定义体: by
  refine .ofBijective _ ⟨.of_comp (f := Submodule.subtype _) ?_, Submodule.mulMap'_surjective _ _⟩
  convert!
    ((tensorSubmoduleAlgebraEquiv e).restrictScalars R).injective.comp
      (Flat.rTensor_preserves_injective_linearMap _ I.subtype_injective)
  simp_rw [← LinearEquiv.coe_toLinearMap, ← LinearMap.coe_comp]
  congr 1; ext; rfl

Depends on / 依赖: Flat.rTensor_preserves_injective_linearMap, I.subtype_injective, LinearEquiv, LinearEquiv.coe_toLinearMap, LinearMap, LinearMap.coe_comp, Submodule, Submodule.mulMap, Submodule.subtype, _surjective, coe_comp, coe_toLinearMap, convert, injective, injective.comp, mulMap, ofBijective, of_comp, rTensor_preserves_injective_linearMap, restrictScalars
-/
noncomputable def tensorSubmoduleAlgebraEquivMul (I : Submodule R A) :
    I otimes[R] submoduleAlgebra e ≃ₗ[R] I * submoduleAlgebra e := by
  refine .ofBijective _ ⟨.of_comp (f := Submodule.subtype _) ?_, Submodule.mulMap'_surjective _ _⟩
  convert!
    ((tensorSubmoduleAlgebraEquiv e).restrictScalars R).injective.comp
      (Flat.rTensor_preserves_injective_linearMap _ I.subtype_injective)
  simp_rw [← LinearEquiv.coe_toLinearMap, ← LinearMap.coe_comp]
  congr 1; ext; rfl

end Module.Flat

section PicardGroup

variable [CommSemiring A] [Algebra R A] [FaithfulSMul R A]

open CommRing Pic LinearMap Module.Flat

/--
theorem `Submodule.range_unitsToPic` / 定理 `Submodule.range_unitsToPic`

English:
theorem Submodule.range_unitsToPic
  statement: (unitsToPic R A).range = relPic R A
  proof: by
  ext M; constructor <;> intro h
  · obtain ⟨I, rfl⟩ := h
    exact mk_eq_one_iff.mpr ⟨AlgebraTensorModule.congr (.refl ..) (unitsToPicEquiv I) ≪≫ₗ
      .ofBijective ((Algebra.TensorProduct.lmul'' R).toLinearMap ∘ₗ AlgebraTensorModule.lTensor A A
        I.1.subtype) (projective_units_and_mul'_comp_lTensor_bijective I).2⟩
  have e := (mk_eq_one_iff.mp h).some
  have f := (mk_eq_one_iff.mp (inv_mem h)).some
  refine ⟨(isUnit_of_mul_isUnit_left (x := submoduleAlgebra e) (y := submoduleAlgebra f) ?_).unit,
    mk_eq_iff.mpr ⟨submoduleAlgebraEquiv e⟩⟩
have := eq_span_singleton_of_surjective LinearEquiv.surjective
    (congr (submoduleAlgebraEquiv e) (submoduleAlgebraEquiv f) ≪≫ₗ
    (mk_eq_one_iff.mp <| by simp_rw [mk_tensor, mk_eq_self, mul_inv_cancel]).some).symm ≪≫ₗ
    tensorSubmoduleAlgebraEquivMul f (submoduleAlgebra e)
  rw [this]
  apply_fun (⊤ * ·) at this
  simp_rw [← mul_assoc, top_mul_submoduleAlgebra] at this
  obtain ⟨a, -, eq⟩ := mem_mul_span_singleton.mp (this ▸ mem_top (x := 1))
  exact .map (spanSingleton R).toMonoidHom (.of_mul_eq_one_right _ eq)

中文:
定理 子模.range_unitsToPic
  结论: (unitsToPic R A).range = relPic R A
  证明: by
  ext M; constructor <;> intro h
  · obtain ⟨I, rfl⟩ := h
    exact mk_eq_one_iff.mpr ⟨AlgebraTensorModule.congr (.refl ..) (unitsToPicEquiv I) ≪≫ₗ
      .ofBijective ((Algebra.TensorProduct.lmul'' R).toLinearMap ∘ₗ AlgebraTensorModule.lTensor A A
        I.1.subtype) (projective_units_and_mul'_comp_lTensor_bijective I).2⟩
  have e := (mk_eq_one_iff.mp h).some
  have f := (mk_eq_one_iff.mp (inv_mem h)).some
  refine ⟨(isUnit_of_mul_isUnit_left (x := submoduleAlgebra e) (y := submoduleAlgebra f) ?_).unit,
    mk_eq_iff.mpr ⟨submoduleAlgebraEquiv e⟩⟩
have := eq_span_singleton_of_surjective LinearEquiv.surjective
    (congr (submoduleAlgebraEquiv e) (submoduleAlgebraEquiv f) ≪≫ₗ
    (mk_eq_one_iff.mp <| by simp_rw [mk_tensor, mk_eq_self, mul_inv_cancel]).some).symm ≪≫ₗ
    tensorSubmoduleAlgebraEquivMul f (submoduleAlgebra e)
  rw [this]
  apply_fun (⊤ * ·) at this
  simp_rw [← mul_assoc, top_mul_submoduleAlgebra] at this
  obtain ⟨a, -, eq⟩ := mem_mul_span_singleton.mp (this ▸ mem_top (x := 1))
  exact .map (spanSingleton R).toMonoidHom (.of_mul_eq_one_right _ eq)

Depends on / 依赖: Algebra, Algebra.TensorProduct.lmul, AlgebraTensorModule, AlgebraTensorModule.congr, AlgebraTensorModule.lTensor, TensorProduct, _comp_lTensor_bijective, inv_mem, isUnit_of_mul_isUnit_left, lTensor, mk_eq_iff, mk_eq_iff.mpr, mk_eq_one_iff, mk_eq_one_iff.mp, mk_eq_one_iff.mpr, ofBijective, projective_units_and_mul, submoduleAlgebra, subtype, toLinearMap
-/
theorem Submodule.range_unitsToPic : (unitsToPic R A).range = relPic R A := by
  ext M; constructor <;> intro h
  · obtain ⟨I, rfl⟩ := h
    exact mk_eq_one_iff.mpr ⟨AlgebraTensorModule.congr (.refl ..) (unitsToPicEquiv I) ≪≫ₗ
      .ofBijective ((Algebra.TensorProduct.lmul'' R).toLinearMap ∘ₗ AlgebraTensorModule.lTensor A A
        I.1.subtype) (projective_units_and_mul'_comp_lTensor_bijective I).2⟩
  have e := (mk_eq_one_iff.mp h).some
  have f := (mk_eq_one_iff.mp (inv_mem h)).some
  refine ⟨(isUnit_of_mul_isUnit_left (x := submoduleAlgebra e) (y := submoduleAlgebra f) ?_).unit,
    mk_eq_iff.mpr ⟨submoduleAlgebraEquiv e⟩⟩
have := eq_span_singleton_of_surjective LinearEquiv.surjective
    (congr (submoduleAlgebraEquiv e) (submoduleAlgebraEquiv f) ≪≫ₗ
    (mk_eq_one_iff.mp <| by simp_rw [mk_tensor, mk_eq_self, mul_inv_cancel]).some).symm ≪≫ₗ
    tensorSubmoduleAlgebraEquivMul f (submoduleAlgebra e)
  rw [this]
  apply_fun (⊤ * ·) at this
  simp_rw [← mul_assoc, top_mul_submoduleAlgebra] at this
  obtain ⟨a, -, eq⟩ := mem_mul_span_singleton.mp (this ▸ mem_top (x := 1))
  exact .map (spanSingleton R).toMonoidHom (.of_mul_eq_one_right _ eq)

/--
theorem `Submodule.mulExact_unitsToPic_mapAlgebra` / 定理 `Submodule.mulExact_unitsToPic_mapAlgebra`

English:
theorem Submodule.mulExact_unitsToPic_mapAlgebra
  proof: MonoidHom.mulExact_iff.mpr (range_unitsToPic R A).symm

#adaptation_note

中文:
定理 子模.mulExact_unitsToPic_mapAlgebra
  证明: MonoidHom.mulExact_iff.mpr (range_unitsToPic R A).symm

#adaptation_note

Depends on / 依赖: MonoidHom, MonoidHom.mulExact_iff.mpr, mulExact_iff, range_unitsToPic
-/
theorem Submodule.mulExact_unitsToPic_mapAlgebra :
    Function.MulExact (unitsToPic R A) (mapAlgebra R A) :=
  MonoidHom.mulExact_iff.mpr (range_unitsToPic R A).symm

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
open QuotientGroup in
/--
Definition of `Submodule.unitsQuotEquivRelPic` / `Submodule.unitsQuotEquivRelPic` 的定义

English:
definition Submodule.unitsQuotEquivRelPic
  signature: :
  body: (QuotientGroup.congr _ _ (.refl _) ((Subgroup.map_id _).trans (ker_unitsToPic R A).symm)).trans
(quotientKerEquivRange _).trans .subgroupCongr (range_unitsToPic R A)

#adaptation_note

中文:
定义 子模.unitsQuotEquivRelPic
  签名: :
  定义体: (QuotientGroup.congr _ _ (.refl _) ((Subgroup.map_id _).trans (ker_unitsToPic R A).symm)).trans
(quotientKerEquivRange _).trans .subgroupCongr (range_unitsToPic R A)

#adaptation_note
-/
@[simps!] noncomputable def Submodule.unitsQuotEquivRelPic :
    (Submodule R A)ˣ ⧸ (Units.map (spanSingleton R).toMonoidHom).range ≃* relPic R A :=
(QuotientGroup.congr _ _ (.refl _) ((Subgroup.map_id _).trans (ker_unitsToPic R A).symm)).trans
(quotientKerEquivRange _).trans .subgroupCongr (range_unitsToPic R A)

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `ClassGroup.equivPic` / `ClassGroup.equivPic` 的定义

English:
definition ClassGroup.equivPic
  signature: (R) [CommRing R] [IsDomain R]
  body: (mulEquivUnitsSubmoduleQuotRange R).trans .trans (Submodule.unitsQuotEquivRelPic R _)
    .trans (.subgroupCongr <| relPic_eq_top R _) Subgroup.topEquiv

中文:
定义 ClassGroup.equivPic
  签名: (R) [交换环 R] [是整环 R]
  定义体: (mulEquivUnitsSubmoduleQuotRange R).trans .trans (Submodule.unitsQuotEquivRelPic R _)
    .trans (.subgroupCongr <| relPic_eq_top R _) Subgroup.topEquiv
-/
@[simps!] noncomputable def ClassGroup.equivPic (R) [CommRing R] [IsDomain R] :
    ClassGroup R ≃* Pic R :=
(mulEquivUnitsSubmoduleQuotRange R).trans .trans (Submodule.unitsQuotEquivRelPic R _)
    .trans (.subgroupCongr <| relPic_eq_top R _) Subgroup.topEquiv

/-- The Picard group of a domain with normalizable gcd is trivial.
This includes unique factorization domains. -/
@[stacks 0BCH]
instance (R) [CommRing R] [IsDomain R] [IsGCDMonoid R] : Subsingleton (Pic R) :=
  Equiv.subsingleton (ClassGroup.equivPic R).toEquiv.symm

end PicardGroup

open CommRing Pic

section Ideal

variable (R M N : Type*) [CommRing R]
variable [AddCommGroup M] [Module R M] [Module.Invertible R M]
variable [AddCommGroup N] [Module R N] [Module.Invertible R N]

/--
theorem `Module.Invertible.exists_linearEquiv_ideal` / 定理 `Module.Invertible.exists_linearEquiv_ideal`

English:
theorem Module.Invertible.exists_linearEquiv_ideal
  given: [Subsingleton (Pic (FractionRing R))]
  proof: have : Pic.mk R M in relPic R (FractionRing R) := Subsingleton.elim ..
  have ⟨I, eq⟩ := Submodule.range_unitsToPic R (FractionRing R) ▸ this
  have ⟨e⟩ := mk_eq_mk_iff.mp eq.symm
  ⟨_, ⟨e ≪≫ₗ FractionalIdeal.equivNumOfIsLocalization
    ⟨_, I.submodule_isFractional (S := nonZeroDivisors R)⟩⟩⟩

中文:
定理 模.可逆.存在_linearEquiv_ideal
  条件: [子单例 (Pic (FractionRing R))]
  证明: have : Pic.mk R M in relPic R (FractionRing R) := Subsingleton.elim ..
  have ⟨I, eq⟩ := Submodule.range_unitsToPic R (FractionRing R) ▸ this
  have ⟨e⟩ := mk_eq_mk_iff.mp eq.symm
  ⟨_, ⟨e ≪≫ₗ FractionalIdeal.equivNumOfIsLocalization
    ⟨_, I.submodule_isFractional (S := nonZeroDivisors R)⟩⟩⟩

Depends on / 依赖: FractionRing, FractionalIdeal, FractionalIdeal.equivNumOfIsLocalization, I.submodule_isFractional, Pic.mk, Submodule, Submodule.range_unitsToPic, Subsingleton, Subsingleton.elim, eq.symm, equivNumOfIsLocalization, mk_eq_mk_iff, mk_eq_mk_iff.mp, nonZeroDivisors, range_unitsToPic, relPic, submodule_isFractional
-/
theorem Module.Invertible.exists_linearEquiv_ideal [Subsingleton (Pic (FractionRing R))] :
    exists I : Ideal R, Nonempty (M ≃ₗ[R] I) :=
  have : Pic.mk R M in relPic R (FractionRing R) := Subsingleton.elim ..
  have ⟨I, eq⟩ := Submodule.range_unitsToPic R (FractionRing R) ▸ this
  have ⟨e⟩ := mk_eq_mk_iff.mp eq.symm
  ⟨_, ⟨e ≪≫ₗ FractionalIdeal.equivNumOfIsLocalization
    ⟨_, I.submodule_isFractional (S := nonZeroDivisors R)⟩⟩⟩

/-- Every invertible module over a domain is isomorphic to an ideal. -/
example [IsDomain R] : exists I : Ideal R, Nonempty (M ≃ₗ[R] I) :=
  Module.Invertible.exists_linearEquiv_ideal R M

/-- Every invertible module over a Noetherian ring is isomorphic to an ideal.
See https://mathoverflow.net/a/499611. -/
example [IsNoetherianRing R] : exists I : Ideal R, Nonempty (M ≃ₗ[R] I) :=
  Module.Invertible.exists_linearEquiv_ideal R M

variable {R} in
/--
theorem `Ideal.eq_top_of_mk_tensor_eq_one` / 定理 `Ideal.eq_top_of_mk_tensor_eq_one`

English:
theorem Ideal.eq_top_of_mk_tensor_eq_one
  statement: [IsFractionRing R R] (I J : Ideal R)
  proof: by
  have ⟨e⟩ := mk_eq_one_iff.mp h
  have e := e.symm ≪≫ₗ Submodule.LinearDisjoint.mulMap
    (.of_left_le_one_of_flat I J <| le_top.trans one_eq_top.ge)
have : IsUnit (e 1 : R) := IsFractionRing.self_iff_nonZeroDivisors_le_isUnit.mp ‹_›
IsRegular.mem_nonZeroDivisors isRightRegular_iff_isRegular.mp by
    rw [IsRightRegular]
    convert! Subtype.val_injective.comp e.injective using 2
    rw [← smul_eq_mul]; rw [← Submodule.coe_smul]; rw [← map_smul]; rw [smul_eq_mul]; rw [mul_one]; rw [Function.comp_apply]
  constructor <;> refine eq_top_of_isUnit_mem _ ?_ this
  exacts [mul_le_left (e 1).2, mul_le_right (e 1).2]

中文:
定理 理想.eq_top_of_mk_tensor_eq_one
  结论: [IsFractionRing R R] (I J : 理想 R)
  证明: by
  have ⟨e⟩ := mk_eq_one_iff.mp h
  have e := e.symm ≪≫ₗ Submodule.LinearDisjoint.mulMap
    (.of_left_le_one_of_flat I J <| le_top.trans one_eq_top.ge)
have : IsUnit (e 1 : R) := IsFractionRing.self_iff_nonZeroDivisors_le_isUnit.mp ‹_›
IsRegular.mem_nonZeroDivisors isRightRegular_iff_isRegular.mp by
    rw [IsRightRegular]
    convert! Subtype.val_injective.comp e.injective using 2
    rw [← smul_eq_mul]; rw [← Submodule.coe_smul]; rw [← map_smul]; rw [smul_eq_mul]; rw [mul_one]; rw [Function.comp_apply]
  constructor <;> refine eq_top_of_isUnit_mem _ ?_ this
  exacts [mul_le_left (e 1).2, mul_le_right (e 1).2]

Depends on / 依赖: Function, Function.comp_apply, IsFractionRing, IsFractionRing.self_iff_nonZeroDivisors_le_isUnit.mp, IsRegular, IsRegular.mem_nonZeroDivisors, IsRightRegular, IsUnit, LinearDisjoint, Submodule, Submodule.LinearDisjoint.mulMap, Submodule.coe_smul, Subtype, Subtype.val_injective.comp, coe_smul, comp_apply, constru, convert, e.injective, e.symm
-/
theorem Ideal.eq_top_of_mk_tensor_eq_one [IsFractionRing R R] (I J : Ideal R)
    [Module.Invertible R I] [Module.Invertible R J] (h : Pic.mk R (I otimes[R] J) = 1) :
    I = ⊤ ∧ J = ⊤ := by
  have ⟨e⟩ := mk_eq_one_iff.mp h
  have e := e.symm ≪≫ₗ Submodule.LinearDisjoint.mulMap
    (.of_left_le_one_of_flat I J <| le_top.trans one_eq_top.ge)
have : IsUnit (e 1 : R) := IsFractionRing.self_iff_nonZeroDivisors_le_isUnit.mp ‹_›
IsRegular.mem_nonZeroDivisors isRightRegular_iff_isRegular.mp by
    rw [IsRightRegular]
    convert! Subtype.val_injective.comp e.injective using 2
    rw [← smul_eq_mul]; rw [← Submodule.coe_smul]; rw [← map_smul]; rw [smul_eq_mul]; rw [mul_one]; rw [Function.comp_apply]
  constructor <;> refine eq_top_of_isUnit_mem _ ?_ this
  exacts [mul_le_left (e 1).2, mul_le_right (e 1).2]

end Ideal
