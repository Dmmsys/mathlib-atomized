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

variable (R : Type uR) (A : ι → Type uA) {B : Type uB}
variable [CommSemiring R] [∀ i, AddCommMonoid (A i)] [∀ i, Module R (A i)]
variable [AddMonoid ι] [GSemiring A]

section

/-- A graded version of `Algebra`. An instance of `DirectSum.GAlgebra R A` endows `(⨁ i, A i)`
with an `R`-algebra structure. -/
/-
**DirectSum.GAlgebra** 是 Mathlib 中的一个归纳类型，位于命名空间 `DirectSum`。
形式化陈述：{ι : Type uι} →   (R : Type uR) →     (A : ι → Type uA) →       [inst : Co
mmSemiring R] →         [inst_1 : (i : ι) → AddCommMonoid (A i)] →           [(i
 : ι) → _root_.Module R (A i)] → [inst : AddMonoid ι] → [DirectSum.GSemiring A] 
→ Type (max uA uR)
参数：R : Type uR；A : ι → Type uA；i : ι；A i；i : ι；A i；max uA uR。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A graded version of `Algebra`. An instance of `DirectSum.GAlgebra R A` endows `(
⨁ i, A i)`
with an `R`-algebra structure.
-/
class GAlgebra where
  toFun : R →+ A 0
  map_one : toFun 1 = GradedMonoid.GOne.one
  map_mul :
    ∀ r s, GradedMonoid.mk _ (toFun (r * s)) = .mk _ (GradedMonoid.GMul.mul (toFun r) (toFun s))
  commutes : ∀ (r) (x : GradedMonoid A), .mk _ (toFun r) * x = x * .mk _ (toFun r)
  smul_def : ∀ (r) (x : GradedMonoid A), r • x = .mk _ (toFun r) * x

end

variable [Semiring B] [GAlgebra R A] [Algebra R B]

/-
**DirectSum._root_.GradedMonoid.smulCommClass_right** 是 Mathlib 中的一个实例，位于命名空间 `D
irectSum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.GradedMonoid.smulCommClass_right :
    SMulCommClass R (GradedMonoid A) (GradedMonoid A) where
  smul_comm s x y := by
    dsimp
    rw [GAlgebra.smul_def, GAlgebra.smul_def, ← mul_assoc, GAlgebra.commutes, mul_assoc]
/-
**DirectSum._root_.GradedMonoid.isScalarTower_right** 是 Mathlib 中的一个实例，位于命名空间 `D
irectSum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.GradedMonoid.isScalarTower_right :
    IsScalarTower R (GradedMonoid A) (GradedMonoid A) where
  smul_assoc s x y := by
    dsimp
    rw [GAlgebra.smul_def, GAlgebra.smul_def, ← mul_assoc]

variable [DecidableEq ι]

set_option backward.defeqAttrib.useBackward true in
/-
**DirectSum.** 是 Mathlib 中的一个实例，位于命名空间 `DirectSum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
    rw [of_mul_of, of_mul_of]
    apply DFinsupp.single_eq_of_sigma_eq (GAlgebra.commutes r ⟨i, xi⟩)
  smul_def' r x := by
    change DistribSMul.toAddMonoidHom _ r x = AddMonoidHom.mul (DirectSum.of _ _ _) x
    apply DFunLike.congr_fun _ x
    ext i xi : 2
    dsimp only [AddMonoidHom.comp_apply, DistribSMul.toAddMonoidHom_apply,
      AddMonoidHom.mul_apply]
    rw [DirectSum.of_mul_of, ← of_smul]
    apply DFinsupp.single_eq_of_sigma_eq (GAlgebra.smul_def r ⟨i, xi⟩)
/-
**DirectSum.algebraMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：algebraMap_apply (r : R) : algebraMap R (⨁ i, A i) r = DirectSum.of A 0 (G
Algebra.toFun r)
参数：r : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algebraMap_apply (r : R) :
    algebraMap R (⨁ i, A i) r = DirectSum.of A 0 (GAlgebra.toFun r) :=
  rfl
/-
**DirectSum.algebraMap_toAddMonoid_hom** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：algebraMap_toAddMonoid_hom : ↑(algebraMap R (⨁ i, A i)) = (DirectSum.of A 
0).comp (GAlgebra.toFun : R ->+ A 0)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
-/
theorem algebraMap_toAddMonoid_hom :
    ↑(algebraMap R (⨁ i, A i)) = (DirectSum.of A 0).comp (GAlgebra.toFun : R →+ A 0) :=
  rfl

/-- A family of `LinearMap`s preserving `DirectSum.GOne.one` and `DirectSum.GMul.mul`
describes an `AlgHom` on `⨁ i, A i`. This is a stronger version of `DirectSum.toSemiring`.

Of particular interest is the case when `A i` are bundled subobjects, `f` is the family of
coercions such as `Submodule.subtype (A i)`, and the `[GMonoid A]` structure originates from
`DirectSum.GMonoid.ofAddSubmodules`, in which case the proofs about `GOne` and `GMul`
can be discharged by `rfl`. -/
@[simps]
/-
**DirectSum.toAlgebra** 是 Mathlib 中的一个定义，位于命名空间 `DirectSum`。
形式化陈述：toAlgebra (f : forall i, A i ->ₗ[R] B) (hone : f _ GradedMonoid.GOne.one =
 1) (hmul : forall {i j} (ai : A i) (aj : A j), f _ (GradedMonoid.GMul.mul ai aj
) = f _ ai * f _ aj) : (⨁ i, A i) ->ₐ[R] B
参数：f : forall i, A i ->ₗ[R] B；hone : f _ GradedMonoid.GOne.one = 1；hmul : forall
 {i j} (ai : A i) (aj : A j), f _ (GradedMonoid.GMul.mul ai aj) = f _ ai * f _ a
j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family of `LinearMap`s preserving `DirectSum.GOne.one` and `DirectSum.GMul.mul
`
describes an `AlgHom` on `⨁ i, A i`. This is a stronger version of `DirectSum.to
Semiring`.

Of particular interest is the case when `A i` are bundled subobjects, `f` is the
 family of
coercions such as `Submodule.subtype (A i)`, and the `[GMonoid A]` structure ori
ginates from
`DirectSum.GMonoid.ofAddSubmodules`, in which case the proofs about `GOne` and `
GMul`
can be discharged by `rfl`.
-/
def toAlgebra (f : ∀ i, A i →ₗ[R] B) (hone : f _ GradedMonoid.GOne.one = 1)
    (hmul : ∀ {i j} (ai : A i) (aj : A j), f _ (GradedMonoid.GMul.mul ai aj) = f _ ai * f _ aj) :
    (⨁ i, A i) →ₐ[R] B :=
  { toSemiring (fun i => (f i).toAddMonoidHom) hone @hmul with
    toFun := toSemiring (fun i => (f i).toAddMonoidHom) hone @hmul
    commutes' := fun r => by
      change toModule R _ _ f (algebraMap R _ r) = _
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, map_smul, one_def,
        ← lof_eq_of R, toModule_lof, hone] }

/-- Two `AlgHom`s out of a direct sum are equal if they agree on the generators.

See note [partially-applied ext lemmas]. -/
@[ext]
/-
**DirectSum.algHom_ext'** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：algHom_ext' ⦃f g : (⨁ i, A i) ->ₐ[R] B⦄ (h : forall i, f.toLinearMap.comp 
(lof _ _ A i) = g.toLinearMap.comp (lof _ _ A i)) : f = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.toLinearMap_injective`：toLinearMap_injective : Function.Injective
 (toLinearMap : _ -> A ->ₗ[R] B)
· 使用定理 `DirectSum.linearMap_ext`：linearMap_ext ⦃ψ ψ' : (⨁ i, M i) ->ₗ[R] N⦄ (H :
 forall i, ψ.comp (lof R ι M i) = ψ'.comp (lof R ι M i)) : ψ = ψ'

--- 原说明 ---
Two `AlgHom`s out of a direct sum are equal if they agree on the generators.

See note [partially-applied ext lemmas].
-/
theorem algHom_ext' ⦃f g : (⨁ i, A i) →ₐ[R] B⦄
    (h : ∀ i, f.toLinearMap.comp (lof _ _ A i) = g.toLinearMap.comp (lof _ _ A i)) : f = g :=
  AlgHom.toLinearMap_injective <| DirectSum.linearMap_ext _ h
/-
**DirectSum.algHom_ext** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：algHom_ext ⦃f g : (⨁ i, A i) ->ₐ[R] B⦄ (h : forall i x, f (of A i x) = g (
of A i x)) : f = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectSum.algHom_ext'`：algHom_ext' ⦃f g : (⨁ i, A i) ->ₐ[R] B⦄ (h : fora
ll i, f.toLinearMap.comp (lof _ _ A i) = g.toLinearMap.comp (lof _ _ A i)) : f =
 g
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
-/
theorem algHom_ext ⦃f g : (⨁ i, A i) →ₐ[R] B⦄ (h : ∀ i x, f (of A i x) = g (of A i x)) : f = g :=
  algHom_ext' R A fun i => LinearMap.ext <| h i

/-- The piecewise multiplication from the `Mul` instance, as a bundled linear map.

This is the graded version of `LinearMap.mul`, and the linear version of `DirectSum.gMulHom` -/
@[simps]
/-
**DirectSum.gMulLHom** 是 Mathlib 中的一个定义，位于命名空间 `DirectSum`。
形式化陈述：gMulLHom {i j} : A i ->ₗ[R] A j ->ₗ[R] A (i + j) where toFun a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The piecewise multiplication from the `Mul` instance, as a bundled linear map.

This is the graded version of `LinearMap.mul`, and the linear version of `Direct
Sum.gMulHom`
-/
def gMulLHom {i j} : A i →ₗ[R] A j →ₗ[R] A (i + j) where
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
/-
**Algebra.directSumGAlgebra** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Algebra.directSumGAlgebra {R A : Type*} [AddMonoid ι] [CommSemiring R] [Se
miring A] [Algebra R A] : DirectSum.GAlgebra R fun _ : ι => A where toFun
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A direct sum of copies of an `Algebra` inherits the algebra structure.
-/
instance Algebra.directSumGAlgebra {R A : Type*} [AddMonoid ι] [CommSemiring R]
    [Semiring A] [Algebra R A] : DirectSum.GAlgebra R fun _ : ι => A where
  toFun := (algebraMap R A).toAddMonoidHom
  map_one := (algebraMap R A).map_one
  map_mul a b := Sigma.ext (zero_add _).symm (heq_of_eq <| (algebraMap R A).map_mul a b)
  commutes := fun _ ⟨_, _⟩ =>
    Sigma.ext ((zero_add _).trans (add_zero _).symm) (heq_of_eq <| Algebra.commutes _ _)
  smul_def := fun _ ⟨_, _⟩ => Sigma.ext (zero_add _).symm (heq_of_eq <| Algebra.smul_def _ _)
