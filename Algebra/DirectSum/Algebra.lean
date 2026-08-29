/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.DirectSum.Ring

/-! # Additively-graded algebra structures on `⨁ i, A i`

This file provides `R`-algebra structures on external direct sums of `R`-modules.

Recall that if `A i` are a family of `AddCommMonoid`s indexed by an `AddMonoid`, then an instance
of `DirectSum.GMonoid A` is a multiplication `A i → A j → A (i + j)` giving `⨁ i, A i` the
structure of a semiring. In this file, we introduce the `DirectSum.GAlgebra R A` class for the case
where all `A i` are `R`-modules. This is the extra structure needed to promote `⨁ i, A i` to an
`R`-algebra.

## Main definitions

* `DirectSum.GAlgebra R A`, the typeclass.
* `DirectSum.toAlgebra` extends `DirectSum.toSemiring` to produce an `AlgHom`.

-/

@[expose] public section


universe uι uR uA uB

variable {ι : Type uι}

namespace DirectSum

open DirectSum

variable (R : Type uR) (A : ι -> Type uA) {B : Type uB}
variable [CommSemiring R] [forall i, AddCommMonoid (A i)] [forall i, Module R (A i)]
variable [AddMonoid ι] [GSemiring A]

section

/--
Definition of `GAlgebra` / `GAlgebra` 的定义

English:
class GAlgebra
  parameters: where
  axioms and operations (5):
    - toFun : R ->+ A 0
    - map_one : toFun 1 = GradedMonoid.GOne.one
    - map_mul : forall r s, GradedMonoid.mk _ (toFun (r * s)) = .mk _ (GradedMonoid.GMul.mul (toFun r) (toFun s))
    - commutes : forall (r) (x : GradedMonoid A), .mk _ (toFun r) * x = x * .mk _ (toFun r)
    - smul_def : forall (r) (x : GradedMonoid A), r • x = .mk _ (toFun r) * x

中文:
类 G代数
  参数: where
  公理与运算 (5 个):
    - toFun : R ->+ A 0
    - map_one : toFun 1 = 分次幺半群.GOne.one
    - map_mul : 对任意 r s, 分次幺半群.mk _ (toFun (r * s)) = .mk _ (分次幺半群.GMul.mul (toFun r) (toFun s))
    - commutes : 对任意 (r) (x : 分次幺半群 A), .mk _ (toFun r) * x = x * .mk _ (toFun r)
    - smul_def : 对任意 (r) (x : 分次幺半群 A), r • x = .mk _ (toFun r) * x
-/
class GAlgebra where
  toFun : R ->+ A 0
  map_one : toFun 1 = GradedMonoid.GOne.one
  map_mul :
    forall r s, GradedMonoid.mk _ (toFun (r * s)) = .mk _ (GradedMonoid.GMul.mul (toFun r) (toFun s))
  commutes : forall (r) (x : GradedMonoid A), .mk _ (toFun r) * x = x * .mk _ (toFun r)
  smul_def : forall (r) (x : GradedMonoid A), r • x = .mk _ (toFun r) * x

end

variable [Semiring B] [GAlgebra R A] [Algebra R B]

/--
Instance `_root_.GradedMonoid.smulCommClass_right` / 实例 `_root_.GradedMonoid.smulCommClass_right`

English:
instance _root_.GradedMonoid.smulCommClass_right
  signature: :
  body: by
    dsimp
    rw [GAlgebra.smul_def]; rw [GAlgebra.smul_def]; rw [← mul_assoc]; rw [GAlgebra.commutes]; rw [mul_assoc]

中文:
实例 _root_.分次幺半群.smulCommClass_right
  签名: :
  定义体: by
    dsimp
    rw [GAlgebra.smul_def]; rw [GAlgebra.smul_def]; rw [← mul_assoc]; rw [GAlgebra.commutes]; rw [mul_assoc]

Depends on / 依赖: GAlgebra, GAlgebra.commutes, GAlgebra.smul_def, commutes, mul_assoc, smul_def
-/
instance _root_.GradedMonoid.smulCommClass_right :
    SMulCommClass R (GradedMonoid A) (GradedMonoid A) where
  smul_comm s x y := by
    dsimp
    rw [GAlgebra.smul_def]; rw [GAlgebra.smul_def]; rw [← mul_assoc]; rw [GAlgebra.commutes]; rw [mul_assoc]

/--
Instance `_root_.GradedMonoid.isScalarTower_right` / 实例 `_root_.GradedMonoid.isScalarTower_right`

English:
instance _root_.GradedMonoid.isScalarTower_right
  signature: :
  body: by
    dsimp
    rw [GAlgebra.smul_def]; rw [GAlgebra.smul_def]; rw [← mul_assoc]

中文:
实例 _root_.分次幺半群.isScalarTower_right
  签名: :
  定义体: by
    dsimp
    rw [GAlgebra.smul_def]; rw [GAlgebra.smul_def]; rw [← mul_assoc]

Depends on / 依赖: GAlgebra, GAlgebra.smul_def, mul_assoc, smul_def
-/
instance _root_.GradedMonoid.isScalarTower_right :
    IsScalarTower R (GradedMonoid A) (GradedMonoid A) where
  smul_assoc s x y := by
    dsimp
    rw [GAlgebra.smul_def]; rw [GAlgebra.smul_def]; rw [← mul_assoc]

variable [DecidableEq ι]

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Algebra R (⨁ i, A i)
  body: { toFun := (DirectSum.of A 0).comp GAlgebra.toFun
    map_zero' := map_zero _
    map_add' := map_add _
    map_one' := DFunLike.congr_arg (DirectSum.of A 0) GAlgebra.map_one
    map_mul' a b := by
      simp only [AddMonoidHom.comp_apply]
      rw [of_mul_of]
      apply DFinsupp.single_eq_of_sigma_eq (GAlgebra.map_mul a b) }
  commutes' r x := by
    change AddMonoidHom.mul (DirectSum.of _ _ _) x = AddMonoidHom.mul.flip (DirectSum.of _ _ _) x
    apply DFunLike.congr_fun _ x
    ext i xi : 2
    dsimp only [AddMonoidHom.comp_apply, AddMonoidHom.mul_apply, AddMonoidHom.flip_apply]
    rw [of_mul_of]; rw [of_mul_of]
    apply DFinsupp.single_eq_of_sigma_eq (GAlgebra.commutes r ⟨i, xi⟩)
  smul_def' r x := by
    change DistribSMul.toAddMonoidHom _ r x = AddMonoidHom.mul (DirectSum.of _ _ _) x
    apply DFunLike.congr_fun _ x
    ext i xi : 2
    dsimp only [AddMonoidHom.comp_apply, DistribSMul.toAddMonoidHom_apply,
      AddMonoidHom.mul_apply]
    rw [DirectSum.of_mul_of]; rw [← of_smul]
    apply DFinsupp.single_eq_of_sigma_eq (GAlgebra.smul_def r ⟨i, xi⟩)

中文:
实例 :
  签名: 代数 R (⨁ i, A i)
  定义体: { toFun := (DirectSum.of A 0).comp GAlgebra.toFun
    map_zero' := map_zero _
    map_add' := map_add _
    map_one' := DFunLike.congr_arg (DirectSum.of A 0) GAlgebra.map_one
    map_mul' a b := by
      simp only [AddMonoidHom.comp_apply]
      rw [of_mul_of]
      apply DFinsupp.single_eq_of_sigma_eq (GAlgebra.map_mul a b) }
  commutes' r x := by
    change AddMonoidHom.mul (DirectSum.of _ _ _) x = AddMonoidHom.mul.flip (DirectSum.of _ _ _) x
    apply DFunLike.congr_fun _ x
    ext i xi : 2
    dsimp only [AddMonoidHom.comp_apply, AddMonoidHom.mul_apply, AddMonoidHom.flip_apply]
    rw [of_mul_of]; rw [of_mul_of]
    apply DFinsupp.single_eq_of_sigma_eq (GAlgebra.commutes r ⟨i, xi⟩)
  smul_def' r x := by
    change DistribSMul.toAddMonoidHom _ r x = AddMonoidHom.mul (DirectSum.of _ _ _) x
    apply DFunLike.congr_fun _ x
    ext i xi : 2
    dsimp only [AddMonoidHom.comp_apply, DistribSMul.toAddMonoidHom_apply,
      AddMonoidHom.mul_apply]
    rw [DirectSum.of_mul_of]; rw [← of_smul]
    apply DFinsupp.single_eq_of_sigma_eq (GAlgebra.smul_def r ⟨i, xi⟩)

Depends on / 依赖: AddMonoidHom, AddMonoidHom.comp_apply, AddMonoidHom.mul, AddMonoidHom.mul.flip, DFinsupp, DFinsupp.single_eq_of_sigma_eq, DFunLike, DFunLike.congr_arg, DFunLike.congr_fun, DirectSum, DirectSum.of, GAlgebra, GAlgebra.map_mul, GAlgebra.map_one, GAlgebra.toFun, commutes, comp_apply, congr_arg, congr_fun, map_add
-/
instance : Algebra R (⨁ i, A i) where
  algebraMap :=
  { toFun := (DirectSum.of A 0).comp GAlgebra.toFun
    map_zero' := map_zero _
    map_add' := map_add _
    map_one' := DFunLike.congr_arg (DirectSum.of A 0) GAlgebra.map_one
    map_mul' a b := by
      simp only [AddMonoidHom.comp_apply]
      rw [of_mul_of]
      apply DFinsupp.single_eq_of_sigma_eq (GAlgebra.map_mul a b) }
  commutes' r x := by
    change AddMonoidHom.mul (DirectSum.of _ _ _) x = AddMonoidHom.mul.flip (DirectSum.of _ _ _) x
    apply DFunLike.congr_fun _ x
    ext i xi : 2
    dsimp only [AddMonoidHom.comp_apply, AddMonoidHom.mul_apply, AddMonoidHom.flip_apply]
    rw [of_mul_of]; rw [of_mul_of]
    apply DFinsupp.single_eq_of_sigma_eq (GAlgebra.commutes r ⟨i, xi⟩)
  smul_def' r x := by
    change DistribSMul.toAddMonoidHom _ r x = AddMonoidHom.mul (DirectSum.of _ _ _) x
    apply DFunLike.congr_fun _ x
    ext i xi : 2
    dsimp only [AddMonoidHom.comp_apply, DistribSMul.toAddMonoidHom_apply,
      AddMonoidHom.mul_apply]
    rw [DirectSum.of_mul_of]; rw [← of_smul]
    apply DFinsupp.single_eq_of_sigma_eq (GAlgebra.smul_def r ⟨i, xi⟩)

/--
theorem `algebraMap_apply` / 定理 `algebraMap_apply`

English:
theorem algebraMap_apply
  given: (r : R)
  proof: rfl

中文:
定理 algebraMap_apply
  条件: (r : R)
  证明: rfl
-/
theorem algebraMap_apply (r : R) :
    algebraMap R (⨁ i, A i) r = DirectSum.of A 0 (GAlgebra.toFun r) :=
  rfl

/--
theorem `algebraMap_toAddMonoid_hom` / 定理 `algebraMap_toAddMonoid_hom`

English:
theorem algebraMap_toAddMonoid_hom
  proof: rfl

中文:
定理 algebraMap_toAddMonoid_hom
  证明: rfl
-/
theorem algebraMap_toAddMonoid_hom :
    ↑(algebraMap R (⨁ i, A i)) = (DirectSum.of A 0).comp (GAlgebra.toFun : R ->+ A 0) :=
  rfl

/-- A family of `LinearMap`s preserving `DirectSum.GOne.one` and `DirectSum.GMul.mul`
describes an `AlgHom` on `⨁ i, A i`. This is a stronger version of `DirectSum.toSemiring`.

Of particular interest is the case when `A i` are bundled subobjects, `f` is the family of
coercions such as `Submodule.subtype (A i)`, and the `[GMonoid A]` structure originates from
`DirectSum.GMonoid.ofAddSubmodules`, in which case the proofs about `GOne` and `GMul`
can be discharged by `rfl`. -/
@[simps]
/--
Definition of `toAlgebra` / `toAlgebra` 的定义

English:
definition toAlgebra
  signature: (f : forall i, A i ->ₗ[R] B) (hone : f _ GradedMonoid.GOne.one = 1)
  body: { toSemiring (fun i => (f i).toAddMonoidHom) hone @hmul with
    toFun := toSemiring (fun i => (f i).toAddMonoidHom) hone @hmul
    commutes' := fun r => by
      change toModule R _ _ f (algebraMap R _ r) = _
      rw [Algebra.algebraMap_eq_smul_one]; rw [Algebra.algebraMap_eq_smul_one]; rw [map_smul]; rw [one_def]; rw [← lof_eq_of R]; rw [toModule_lof]; rw [hone] }

中文:
定义 toAlgebra
  签名: (f : 对任意 i, A i ->ₗ[R] B) (hone : f _ 分次幺半群.GOne.one = 1)
  定义体: { toSemiring (fun i => (f i).toAddMonoidHom) hone @hmul with
    toFun := toSemiring (fun i => (f i).toAddMonoidHom) hone @hmul
    commutes' := fun r => by
      change toModule R _ _ f (algebraMap R _ r) = _
      rw [Algebra.algebraMap_eq_smul_one]; rw [Algebra.algebraMap_eq_smul_one]; rw [map_smul]; rw [one_def]; rw [← lof_eq_of R]; rw [toModule_lof]; rw [hone] }

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, algebraMap, algebraMap_eq_smul_one, commutes, lof_eq_of, map_smul, one_def, toAddMonoidHom, toModule, toModule_lof, toSemiring
-/
def toAlgebra (f : forall i, A i ->ₗ[R] B) (hone : f _ GradedMonoid.GOne.one = 1)
    (hmul : forall {i j} (ai : A i) (aj : A j), f _ (GradedMonoid.GMul.mul ai aj) = f _ ai * f _ aj) :
    (⨁ i, A i) ->ₐ[R] B :=
  { toSemiring (fun i => (f i).toAddMonoidHom) hone @hmul with
    toFun := toSemiring (fun i => (f i).toAddMonoidHom) hone @hmul
    commutes' := fun r => by
      change toModule R _ _ f (algebraMap R _ r) = _
      rw [Algebra.algebraMap_eq_smul_one]; rw [Algebra.algebraMap_eq_smul_one]; rw [map_smul]; rw [one_def]; rw [← lof_eq_of R]; rw [toModule_lof]; rw [hone] }

/-- Two `AlgHom`s out of a direct sum are equal if they agree on the generators.

See note [partially-applied ext lemmas]. -/
@[ext]
/--
theorem `algHom_ext'` / 定理 `algHom_ext'`

English:
theorem algHom_ext'
  given: ⦃f g
  statement: (⨁ i, A i) ->ₐ[R] B⦄
  proof: AlgHom.toLinearMap_injective DirectSum.linearMap_ext _ h

中文:
定理 algHom_ext'
  条件: ⦃f g
  结论: (⨁ i, A i) ->ₐ[R] B⦄
  证明: AlgHom.toLinearMap_injective DirectSum.linearMap_ext _ h

Depends on / 依赖: AlgHom, AlgHom.toLinearMap_injective, DirectSum, DirectSum.linearMap_ext, linearMap_ext, toLinearMap_injective
-/
theorem algHom_ext' ⦃f g : (⨁ i, A i) ->ₐ[R] B⦄
    (h : forall i, f.toLinearMap.comp (lof _ _ A i) = g.toLinearMap.comp (lof _ _ A i)) : f = g :=
AlgHom.toLinearMap_injective DirectSum.linearMap_ext _ h

/--
theorem `algHom_ext` / 定理 `algHom_ext`

English:
theorem algHom_ext
  given: ⦃f g
  statement: (⨁ i, A i) ->ₐ[R] B⦄ (h : forall i x, f (of A i x) = g (of A i x)) : f = g
  proof: algHom_ext' R A fun i => LinearMap.ext h i

中文:
定理 algHom_ext
  条件: ⦃f g
  结论: (⨁ i, A i) ->ₐ[R] B⦄ (h : 对任意 i x, f (of A i x) = g (of A i x)) : f = g
  证明: algHom_ext' R A fun i => LinearMap.ext h i

Depends on / 依赖: LinearMap, LinearMap.ext, algHom_ext
-/
theorem algHom_ext ⦃f g : (⨁ i, A i) ->ₐ[R] B⦄ (h : forall i x, f (of A i x) = g (of A i x)) : f = g :=
algHom_ext' R A fun i => LinearMap.ext h i

/-- The piecewise multiplication from the `Mul` instance, as a bundled linear map.

This is the graded version of `LinearMap.mul`, and the linear version of `DirectSum.gMulHom` -/
@[simps]
/--
Definition of `gMulLHom` / `gMulLHom` 的定义

English:
definition gMulLHom
  signature: {i j}
  body: { toFun := fun b => GradedMonoid.GMul.mul a b
      map_smul' := fun r x => by
        injection (smul_comm r (GradedMonoid.mk _ a) (GradedMonoid.mk _ x)).symm
      map_add' := GNonUnitalNonAssocSemiring.mul_add _ }
  map_smul' r x := LinearMap.ext fun y => by
    injection smul_assoc r (GradedMonoid.mk _ x) (GradedMonoid.mk _ y)
  map_add' _ _ := LinearMap.ext fun _ => GNonUnitalNonAssocSemiring.add_mul _ _ _

中文:
定义 gMulLHom
  签名: {i j}
  定义体: { toFun := fun b => GradedMonoid.GMul.mul a b
      map_smul' := fun r x => by
        injection (smul_comm r (GradedMonoid.mk _ a) (GradedMonoid.mk _ x)).symm
      map_add' := GNonUnitalNonAssocSemiring.mul_add _ }
  map_smul' r x := LinearMap.ext fun y => by
    injection smul_assoc r (GradedMonoid.mk _ x) (GradedMonoid.mk _ y)
  map_add' _ _ := LinearMap.ext fun _ => GNonUnitalNonAssocSemiring.add_mul _ _ _

Depends on / 依赖: GNonUnitalNonAssocSemiring, GNonUnitalNonAssocSemiring.add_mul, GNonUnitalNonAssocSemiring.mul_add, GradedMonoid, GradedMonoid.GMul.mul, GradedMonoid.mk, LinearMap, LinearMap.ext, add_mul, injection, map_add, map_smul, mul_add, smul_assoc, smul_comm
-/
def gMulLHom {i j} : A i ->ₗ[R] A j ->ₗ[R] A (i + j) where
  toFun a :=
    { toFun := fun b => GradedMonoid.GMul.mul a b
      map_smul' := fun r x => by
        injection (smul_comm r (GradedMonoid.mk _ a) (GradedMonoid.mk _ x)).symm
      map_add' := GNonUnitalNonAssocSemiring.mul_add _ }
  map_smul' r x := LinearMap.ext fun y => by
    injection smul_assoc r (GradedMonoid.mk _ x) (GradedMonoid.mk _ y)
  map_add' _ _ := LinearMap.ext fun _ => GNonUnitalNonAssocSemiring.add_mul _ _ _

end DirectSum

/-! ### Concrete instances -/


/-- A direct sum of copies of an `Algebra` inherits the algebra structure. -/
@[simps]
/--
Instance `Algebra.directSumGAlgebra` / 实例 `Algebra.directSumGAlgebra`

English:
instance Algebra.directSumGAlgebra
  signature: {R A : Type*} [AddMonoid ι] [CommSemiring R]
  body: (algebraMap R A).toAddMonoidHom
  map_one := (algebraMap R A).map_one
  map_mul a b := Sigma.ext (zero_add _).symm (heq_of_eq <| (algebraMap R A).map_mul a b)
  commutes := fun _ ⟨_, _⟩ =>
    Sigma.ext ((zero_add _).trans (add_zero _).symm) (heq_of_eq <| Algebra.commutes _ _)
  smul_def := fun _ ⟨_, _⟩ => Sigma.ext (zero_add _).symm (heq_of_eq <| Algebra.smul_def _ _)

中文:
实例 代数.directSumGAlgebra
  签名: {R A : 类型} [加法幺半群 ι] [交换半环 R]
  定义体: (algebraMap R A).toAddMonoidHom
  map_one := (algebraMap R A).map_one
  map_mul a b := Sigma.ext (zero_add _).symm (heq_of_eq <| (algebraMap R A).map_mul a b)
  commutes := fun _ ⟨_, _⟩ =>
    Sigma.ext ((zero_add _).trans (add_zero _).symm) (heq_of_eq <| Algebra.commutes _ _)
  smul_def := fun _ ⟨_, _⟩ => Sigma.ext (zero_add _).symm (heq_of_eq <| Algebra.smul_def _ _)

Depends on / 依赖: algebraMap, toAddMonoidHom
-/
instance Algebra.directSumGAlgebra {R A : Type*} [AddMonoid ι] [CommSemiring R]
    [Semiring A] [Algebra R A] : DirectSum.GAlgebra R fun _ : ι => A where
  toFun := (algebraMap R A).toAddMonoidHom
  map_one := (algebraMap R A).map_one
  map_mul a b := Sigma.ext (zero_add _).symm (heq_of_eq <| (algebraMap R A).map_mul a b)
  commutes := fun _ ⟨_, _⟩ =>
    Sigma.ext ((zero_add _).trans (add_zero _).symm) (heq_of_eq <| Algebra.commutes _ _)
  smul_def := fun _ ⟨_, _⟩ => Sigma.ext (zero_add _).symm (heq_of_eq <| Algebra.smul_def _ _)
