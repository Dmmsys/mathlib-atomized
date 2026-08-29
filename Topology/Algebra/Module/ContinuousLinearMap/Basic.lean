/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo, Yury Kudryashov, Frédéric Dupuis,
  Heather Macbeth
-/
module

public import Mathlib.Algebra.Module.LinearMap.DivisionRing
public import Mathlib.Algebra.Module.Submodule.EqLocus
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Data.FunLike.Module
public import Mathlib.Data.FunLike.Ring

/-!
# Continuous linear maps

In this file we define the type of continuous (semi)linear maps between topological
modules that are continuous, and endow it with its algebraic structure.

Later files endow it with a topological structure, see the docstring of
`Mathlib/Topology/Algebra/Module/Spaces/ContinuousLinearMap.lean`.

## Main definitions

* `ContinuousLinearMap` is the type of (semi)linear maps between two topological modules that are
  continuous. It is denoted by `M →L[R] N` in the `R`-linear case, `M →SL[σ] N` in the
  `σ`-semilinear case, and `M →L⋆[R] N` in the conjugate-linear (antilinear) case.
* `StrongDual R M` is an abbreviation for `M →L[R] R`, the type of continuous `R`-linear forms on
  `M`. As a vector space, it is often called the "topological dual of `M`". We use the name "strong
  dual" because it will (in later files) be endowed with the strong-dual topology, namely the
  topology of uniform convergence on bounded subsets.
* `ContinuousLinearMap.addCommMonoid`, `ContinuousLinearMap.module`,... : the algebraic structures
  on `M →SL[σ] N`.

## Notation

* `M →L[R] N`: the type of `R`-linear continuous maps from `M` to `N`;
* `M →SL[σ] N`: the type of `σ`-semilinear continuous maps from `M` to `N`;
* `M →L⋆[σ] N`: the type of conjugate-linear (antilinear) continuous maps from `M` to `N`;
* `f ∘L g`: the composition of two continuous linear maps;
* `f ∘SL g`: the composition of two continuous semilinear maps.

-/

@[expose] public section

assert_not_exists TrivialStar

open LinearMap (ker range)
open Topology Filter Pointwise

universe u v w u'

/--
Definition of `ContinuousLinearMap` / `ContinuousLinearMap` 的定义

English:
structure ContinuousLinearMap
  parameters: {R : Type*} {S : Type*} [Semiring R] [Semiring S] (σ : R ->+* S)
  extends: M ->ₛₗ[σ] M₂
  axioms and operations (1):
    - cont : Continuous toFun  [default: by first | fun_prop | eta_expand; dsimp; fun_prop | skip]

中文:
结构 ContinuousLinearMap
  参数: {R : 类型} {S : 类型} [Semiring R] [Semiring S] (σ : R ->+* S)
  继承: M ->ₛₗ[σ] M₂
  公理与运算 (1 个):
    - cont : Continuous toFun  [默认: by first | fun_prop | eta_expand; dsimp; fun_prop | skip]

Depends on / 依赖: eta_expand, fun_prop
-/
structure ContinuousLinearMap {R : Type*} {S : Type*} [Semiring R] [Semiring S] (σ : R ->+* S)
    (M : Type*) [TopologicalSpace M] [AddCommMonoid M] (M₂ : Type*) [TopologicalSpace M₂]
    [AddCommMonoid M₂] [Module R M] [Module S M₂] extends M ->ₛₗ[σ] M₂ where
  cont : Continuous toFun := by
    first | fun_prop | eta_expand; dsimp; fun_prop | skip

attribute [inherit_doc ContinuousLinearMap] ContinuousLinearMap.cont

@[inherit_doc]
notation:25 M " ->SL[" σ "] " M₂ => ContinuousLinearMap σ M M₂

@[inherit_doc]
notation:25 M " ->L[" R "] " M₂ => ContinuousLinearMap (RingHom.id R) M M₂

/--
Definition of `ContinuousSemilinearMapClass` / `ContinuousSemilinearMapClass` 的定义

English:
class ContinuousSemilinearMapClass
  parameters: (F : Type*) {R S : outParam Type*} [Semiring R] [Semiring S]
  extends: SemilinearMapClass F σ M M₂, ContinuousMapClass F M M₂
  (no additional axioms)

中文:
类 ContinuousSemilinearMapClass
  参数: (F : 类型) {R S : outParam 类型} [Semiring R] [Semiring S]
  继承: SemilinearMapClass F σ M M₂, ContinuousMapClass F M M₂
  (无附加公理)
-/
class ContinuousSemilinearMapClass (F : Type*) {R S : outParam Type*} [Semiring R] [Semiring S]
    (σ : outParam <| R ->+* S) (M : outParam Type*) [TopologicalSpace M] [AddCommMonoid M]
    (M₂ : outParam Type*) [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M]
    [Module S M₂] [FunLike F M M₂] : Prop
    extends SemilinearMapClass F σ M M₂, ContinuousMapClass F M M₂

/--
Definition of `ContinuousLinearMapClass` / `ContinuousLinearMapClass` 的定义

English:
abbreviation ContinuousLinearMapClass
  signature: (F : Type*) (R : outParam Type*) [Semiring R]
  body: ContinuousSemilinearMapClass F (RingHom.id R) M M₂

中文:
缩写 ContinuousLinearMapClass
  签名: (F : 类型) (R : outParam 类型) [Semiring R]
  定义体: ContinuousSemilinearMapClass F (RingHom.id R) M M₂

Depends on / 依赖: ContinuousSemilinearMapClass, RingHom, RingHom.id
-/
abbrev ContinuousLinearMapClass (F : Type*) (R : outParam Type*) [Semiring R]
    (M : outParam Type*) [TopologicalSpace M] [AddCommMonoid M] (M₂ : outParam Type*)
    [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M] [Module R M₂] [FunLike F M M₂] :=
  ContinuousSemilinearMapClass F (RingHom.id R) M M₂

/--
Definition of `StrongDual` / `StrongDual` 的定义

English:
abbreviation StrongDual
  signature: (R : Type*) [Semiring R] [TopologicalSpace R]
  body: M ->L[R] R

中文:
缩写 StrongDual
  签名: (R : 类型) [Semiring R] [TopologicalSpace R]
  定义体: M ->L[R] R
-/
abbrev StrongDual (R : Type*) [Semiring R] [TopologicalSpace R]
  (M : Type*) [TopologicalSpace M] [AddCommMonoid M] [Module R M] : Type _ := M ->L[R] R

namespace ContinuousLinearMap

section Semiring

/-!
### Properties that hold for non-necessarily commutative semirings.
-/

variable {R₁ : Type*} {R₂ : Type*} {R₃ : Type*} [Semiring R₁] [Semiring R₂] [Semiring R₃]
  {σ₁₂ : R₁ ->+* R₂} {σ₂₃ : R₂ ->+* R₃} {σ₁₃ : R₁ ->+* R₃} {M₁ : Type*} [TopologicalSpace M₁]
  [AddCommMonoid M₁] {M'₁ : Type*} [TopologicalSpace M'₁] [AddCommMonoid M'₁] {M₂ : Type*}
  [TopologicalSpace M₂] [AddCommMonoid M₂] {M₃ : Type*} [TopologicalSpace M₃] [AddCommMonoid M₃]
  {M₄ : Type*} [TopologicalSpace M₄] [AddCommMonoid M₄] [Module R₁ M₁] [Module R₁ M'₁]
  [Module R₂ M₂] [Module R₃ M₃]

attribute [coe] ContinuousLinearMap.toLinearMap
/--
Instance `LinearMap.coe` / 实例 `LinearMap.coe`

English:
instance LinearMap.coe
  signature: : Coe (M₁ ->SL[σ₁₂] M₂) (M₁ ->ₛₗ[σ₁₂] M₂)
  body: ⟨toLinearMap⟩

中文:
实例 LinearMap.coe
  签名: : Coe (M₁ ->SL[σ₁₂] M₂) (M₁ ->ₛₗ[σ₁₂] M₂)
  定义体: ⟨toLinearMap⟩

Depends on / 依赖: toLinearMap
-/
instance LinearMap.coe : Coe (M₁ ->SL[σ₁₂] M₂) (M₁ ->ₛₗ[σ₁₂] M₂) := ⟨toLinearMap⟩

/--
theorem `coe_injective` / 定理 `coe_injective`

English:
theorem coe_injective
  statement: Function.Injective ((↑) : (M₁ ->SL[σ₁₂] M₂) -> M₁ ->ₛₗ[σ₁₂] M₂)
  proof: by
  intro f g H
  cases f
  cases g
  congr

中文:
定理 coe_injective
  结论: Function.Injective ((↑) : (M₁ ->SL[σ₁₂] M₂) -> M₁ ->ₛₗ[σ₁₂] M₂)
  证明: by
  intro f g H
  cases f
  cases g
  congr
-/
theorem coe_injective : Function.Injective ((↑) : (M₁ ->SL[σ₁₂] M₂) -> M₁ ->ₛₗ[σ₁₂] M₂) := by
  intro f g H
  cases f
  cases g
  congr

/--
Instance `funLike` / 实例 `funLike`

English:
instance funLike
  signature: : FunLike (M₁ ->SL[σ₁₂] M₂) M₁ M₂ where
  body: f.toLinearMap
  coe_injective _ _ h := coe_injective (DFunLike.coe_injective h)

中文:
实例 funLike
  签名: : FunLike (M₁ ->SL[σ₁₂] M₂) M₁ M₂ where
  定义体: f.toLinearMap
  coe_injective _ _ h := coe_injective (DFunLike.coe_injective h)

Depends on / 依赖: f.toLinearMap, toLinearMap
-/
instance funLike : FunLike (M₁ ->SL[σ₁₂] M₂) M₁ M₂ where
  coe f := f.toLinearMap
  coe_injective _ _ h := coe_injective (DFunLike.coe_injective h)

/--
Instance `continuousSemilinearMapClass` / 实例 `continuousSemilinearMapClass`

English:
instance continuousSemilinearMapClass
  signature: :
  body: map_add f.toLinearMap
  map_continuous f := f.2
  map_smulₛₗ f := f.toLinearMap.map_smul'

中文:
实例 continuousSemilinearMapClass
  签名: :
  定义体: map_add f.toLinearMap
  map_continuous f := f.2
  map_smulₛₗ f := f.toLinearMap.map_smul'

Depends on / 依赖: f.toLinearMap, map_add, toLinearMap
-/
instance continuousSemilinearMapClass :
    ContinuousSemilinearMapClass (M₁ ->SL[σ₁₂] M₂) σ₁₂ M₁ M₂ where
  map_add f := map_add f.toLinearMap
  map_continuous f := f.2
  map_smulₛₗ f := f.toLinearMap.map_smul'

/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (f : M₁ ->ₛₗ[σ₁₂] M₂) (h)
  statement: (mk f h : M₁ ->ₛₗ[σ₁₂] M₂) = f
  proof: rfl

@[simp]

中文:
定理 coe_mk
  条件: (f : M₁ ->ₛₗ[σ₁₂] M₂) (h)
  结论: (mk f h : M₁ ->ₛₗ[σ₁₂] M₂) = f
  证明: rfl

@[simp]
-/
theorem coe_mk (f : M₁ ->ₛₗ[σ₁₂] M₂) (h) : (mk f h : M₁ ->ₛₗ[σ₁₂] M₂) = f :=
  rfl

@[simp]
/--
theorem `coe_mk'` / 定理 `coe_mk'`

English:
theorem coe_mk'
  given: (f : M₁ ->ₛₗ[σ₁₂] M₂) (h)
  statement: (mk f h : M₁ -> M₂) = f
  proof: rfl

@[continuity, fun_prop]

中文:
定理 coe_mk'
  条件: (f : M₁ ->ₛₗ[σ₁₂] M₂) (h)
  结论: (mk f h : M₁ -> M₂) = f
  证明: rfl

@[continuity, fun_prop]
-/
theorem coe_mk' (f : M₁ ->ₛₗ[σ₁₂] M₂) (h) : (mk f h : M₁ -> M₂) = f :=
  rfl

@[continuity, fun_prop]
/--
theorem `continuous` / 定理 `continuous`

English:
theorem continuous
  given: (f : M₁ ->SL[σ₁₂] M₂)
  statement: Continuous f
  proof: f.2

@[continuity, fun_prop]

中文:
定理 continuous
  条件: (f : M₁ ->SL[σ₁₂] M₂)
  结论: Continuous f
  证明: f.2

@[continuity, fun_prop]
-/
protected theorem continuous (f : M₁ ->SL[σ₁₂] M₂) : Continuous f :=
  f.2

@[continuity, fun_prop]
/--
theorem `continuous_toLinearMap` / 定理 `continuous_toLinearMap`

English:
theorem continuous_toLinearMap
  given: (f : M₁ ->SL[σ₁₂] M₂)
  statement: Continuous f.toLinearMap
  proof: f.2

@[simp]

中文:
定理 continuous_toLinearMap
  条件: (f : M₁ ->SL[σ₁₂] M₂)
  结论: Continuous f.toLinearMap
  证明: f.2

@[simp]
-/
protected theorem continuous_toLinearMap (f : M₁ ->SL[σ₁₂] M₂) : Continuous f.toLinearMap :=
  f.2

@[simp]
/--
theorem `uniformContinuous` / 定理 `uniformContinuous`

English:
theorem uniformContinuous
  statement: {E₁ E₂ : Type*} [UniformSpace E₁] [UniformSpace E₂]
  proof: uniformContinuous_addMonoidHom_of_continuous f.continuous

@[simp, norm_cast]

中文:
定理 uniformContinuous
  结论: {E₁ E₂ : 类型} [UniformSpace E₁] [UniformSpace E₂]
  证明: uniformContinuous_addMonoidHom_of_continuous f.continuous

@[simp, norm_cast]
-/
protected theorem uniformContinuous {E₁ E₂ : Type*} [UniformSpace E₁] [UniformSpace E₂]
    [AddCommGroup E₁] [AddCommGroup E₂] [Module R₁ E₁] [Module R₂ E₂] [IsUniformAddGroup E₁]
    [IsUniformAddGroup E₂] (f : E₁ ->SL[σ₁₂] E₂) : UniformContinuous f :=
  uniformContinuous_addMonoidHom_of_continuous f.continuous

@[simp, norm_cast]
/--
theorem `coe_inj` / 定理 `coe_inj`

English:
theorem coe_inj
  given: {f g : M₁ ->SL[σ₁₂] M₂}
  statement: (f : M₁ ->ₛₗ[σ₁₂] M₂) = g ↔ f = g
  proof: coe_injective.eq_iff

中文:
定理 coe_inj
  条件: {f g : M₁ ->SL[σ₁₂] M₂}
  结论: (f : M₁ ->ₛₗ[σ₁₂] M₂) = g ↔ f = g
  证明: coe_injective.eq_iff

Depends on / 依赖: coe_injective, coe_injective.eq_iff, eq_iff
-/
theorem coe_inj {f g : M₁ ->SL[σ₁₂] M₂} : (f : M₁ ->ₛₗ[σ₁₂] M₂) = g ↔ f = g :=
  coe_injective.eq_iff

/--
theorem `coeFn_injective` / 定理 `coeFn_injective`

English:
theorem coeFn_injective
  statement: @Function.Injective (M₁ ->SL[σ₁₂] M₂) (M₁ -> M₂) (↑)
  proof: DFunLike.coe_injective

中文:
定理 coeFn_injective
  结论: @Function.Injective (M₁ ->SL[σ₁₂] M₂) (M₁ -> M₂) (↑)
  证明: DFunLike.coe_injective

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective
-/
theorem coeFn_injective : @Function.Injective (M₁ ->SL[σ₁₂] M₂) (M₁ -> M₂) (↑) :=
  DFunLike.coe_injective

/--
theorem `toContinuousAddMonoidHom_injective` / 定理 `toContinuousAddMonoidHom_injective`

English:
theorem toContinuousAddMonoidHom_injective
  proof: (DFunLike.coe_injective.of_comp_iff _).1 DFunLike.coe_injective

@[simp, norm_cast]

中文:
定理 toContinuousAddMonoidHom_injective
  证明: (DFunLike.coe_injective.of_comp_iff _).1 DFunLike.coe_injective

@[simp, norm_cast]

Depends on / 依赖: DFunLike, DFunLike.coe_injective, DFunLike.coe_injective.of_comp_iff, coe_injective, of_comp_iff
-/
theorem toContinuousAddMonoidHom_injective :
    Function.Injective ((↑) : (M₁ ->SL[σ₁₂] M₂) -> ContinuousAddMonoidHom M₁ M₂) :=
  (DFunLike.coe_injective.of_comp_iff _).1 DFunLike.coe_injective

@[simp, norm_cast]
/--
theorem `toContinuousAddMonoidHom_inj` / 定理 `toContinuousAddMonoidHom_inj`

English:
theorem toContinuousAddMonoidHom_inj
  given: {f g : M₁ ->SL[σ₁₂] M₂}
  proof: toContinuousAddMonoidHom_injective.eq_iff

中文:
定理 toContinuousAddMonoidHom_inj
  条件: {f g : M₁ ->SL[σ₁₂] M₂}
  证明: toContinuousAddMonoidHom_injective.eq_iff

Depends on / 依赖: eq_iff, toContinuousAddMonoidHom_injective, toContinuousAddMonoidHom_injective.eq_iff
-/
theorem toContinuousAddMonoidHom_inj {f g : M₁ ->SL[σ₁₂] M₂} :
    (f : ContinuousAddMonoidHom M₁ M₂) = g ↔ f = g :=
  toContinuousAddMonoidHom_injective.eq_iff

/--
Definition of `Simps.apply` / `Simps.apply` 的定义

English:
definition Simps.apply
  signature: (h : M₁ ->SL[σ₁₂] M₂)
  body: h

中文:
定义 Simps.apply
  签名: (h : M₁ ->SL[σ₁₂] M₂)
  定义体: h
-/
def Simps.apply (h : M₁ ->SL[σ₁₂] M₂) : M₁ -> M₂ :=
  h

/--
Definition of `Simps.coe` / `Simps.coe` 的定义

English:
definition Simps.coe
  signature: (h : M₁ ->SL[σ₁₂] M₂)
  body: h

initialize_simps_projections ContinuousLinearMap (toFun -> apply, toLinearMap -> coe, as_prefix coe)

@[ext]

中文:
定义 Simps.coe
  签名: (h : M₁ ->SL[σ₁₂] M₂)
  定义体: h

initialize_simps_projections ContinuousLinearMap (toFun -> apply, toLinearMap -> coe, as_prefix coe)

@[ext]
-/
def Simps.coe (h : M₁ ->SL[σ₁₂] M₂) : M₁ ->ₛₗ[σ₁₂] M₂ :=
  h

initialize_simps_projections ContinuousLinearMap (toFun -> apply, toLinearMap -> coe, as_prefix coe)

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x = g x)
  statement: f = g
  proof: DFunLike.ext f g h

@[simp, norm_cast]

中文:
定理 ext
  条件: {f g : M₁ ->SL[σ₁₂] M₂} (h : 对任意 x, f x = g x)
  结论: f = g
  证明: DFunLike.ext f g h

@[simp, norm_cast]

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x = g x) : f = g :=
  DFunLike.ext f g h

@[simp, norm_cast]
/--
theorem `coe_coe` / 定理 `coe_coe`

English:
theorem coe_coe
  given: (f : M₁ ->SL[σ₁₂] M₂)
  statement: ⇑(f : M₁ ->ₛₗ[σ₁₂] M₂) = f
  proof: rfl

中文:
定理 coe_coe
  条件: (f : M₁ ->SL[σ₁₂] M₂)
  结论: ⇑(f : M₁ ->ₛₗ[σ₁₂] M₂) = f
  证明: rfl
-/
theorem coe_coe (f : M₁ ->SL[σ₁₂] M₂) : ⇑(f : M₁ ->ₛₗ[σ₁₂] M₂) = f :=
  rfl

/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (f : M₁ ->SL[σ₁₂] M₂) (f' : M₁ -> M₂) (h : f' = ⇑f)
  body: f.toLinearMap.copy f' h
  cont := show Continuous f' from h.symm ▸ f.continuous

@[simp]

中文:
定义 copy
  签名: (f : M₁ ->SL[σ₁₂] M₂) (f' : M₁ -> M₂) (h : f' = ⇑f)
  定义体: f.toLinearMap.copy f' h
  cont := show Continuous f' from h.symm ▸ f.continuous

@[simp]
-/
protected def copy (f : M₁ ->SL[σ₁₂] M₂) (f' : M₁ -> M₂) (h : f' = ⇑f) : M₁ ->SL[σ₁₂] M₂ where
  toLinearMap := f.toLinearMap.copy f' h
  cont := show Continuous f' from h.symm ▸ f.continuous

@[simp]
/--
theorem `coe_copy` / 定理 `coe_copy`

English:
theorem coe_copy
  given: (f : M₁ ->SL[σ₁₂] M₂) (f' : M₁ -> M₂) (h : f' = ⇑f)
  statement: ⇑(f.copy f' h) = f'
  proof: rfl

中文:
定理 coe_copy
  条件: (f : M₁ ->SL[σ₁₂] M₂) (f' : M₁ -> M₂) (h : f' = ⇑f)
  结论: ⇑(f.copy f' h) = f'
  证明: rfl
-/
theorem coe_copy (f : M₁ ->SL[σ₁₂] M₂) (f' : M₁ -> M₂) (h : f' = ⇑f) : ⇑(f.copy f' h) = f' :=
  rfl

/--
theorem `copy_eq` / 定理 `copy_eq`

English:
theorem copy_eq
  given: (f : M₁ ->SL[σ₁₂] M₂) (f' : M₁ -> M₂) (h : f' = ⇑f)
  statement: f.copy f' h = f
  proof: DFunLike.ext' h

中文:
定理 copy_eq
  条件: (f : M₁ ->SL[σ₁₂] M₂) (f' : M₁ -> M₂) (h : f' = ⇑f)
  结论: f.copy f' h = f
  证明: DFunLike.ext' h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem copy_eq (f : M₁ ->SL[σ₁₂] M₂) (f' : M₁ -> M₂) (h : f' = ⇑f) : f.copy f' h = f :=
  DFunLike.ext' h

/--
theorem `range_coeFn_eq` / 定理 `range_coeFn_eq`

English:
theorem range_coeFn_eq
  proof: by
  ext f
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨f.continuous, f, rfl⟩
  · rintro ⟨hfc, f, rfl⟩
    exact ⟨⟨f, hfc⟩, rfl⟩

中文:
定理 range_coeFn_eq
  证明: by
  ext f
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨f.continuous, f, rfl⟩
  · rintro ⟨hfc, f, rfl⟩
    exact ⟨⟨f, hfc⟩, rfl⟩

Depends on / 依赖: continuous, f.continuous
-/
theorem range_coeFn_eq :
    Set.range ((⇑) : (M₁ ->SL[σ₁₂] M₂) -> (M₁ -> M₂)) =
      {f | Continuous f} inter Set.range ((⇑) : (M₁ ->ₛₗ[σ₁₂] M₂) -> (M₁ -> M₂)) := by
  ext f
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨f.continuous, f, rfl⟩
  · rintro ⟨hfc, f, rfl⟩
    exact ⟨⟨f, hfc⟩, rfl⟩

/--
lemma `range_toLinearMap` / 引理 `range_toLinearMap`

English:
lemma range_toLinearMap
  given: (f : M₁ ->SL[σ₁₂] M₂)
  statement: Set.range f.toLinearMap = Set.range f
  proof: by simp

中文:
引理 range_toLinearMap
  条件: (f : M₁ ->SL[σ₁₂] M₂)
  结论: Set.range f.toLinearMap = Set.range f
  证明: by simp
-/
lemma range_toLinearMap (f : M₁ ->SL[σ₁₂] M₂) : Set.range f.toLinearMap = Set.range f := by simp

-- make some straightforward lemmas available to `simp`.
/--
theorem `map_zero` / 定理 `map_zero`

English:
theorem map_zero
  given: (f : M₁ ->SL[σ₁₂] M₂)
  statement: f (0 : M₁) = 0
  proof: map_zero f

中文:
定理 map_zero
  条件: (f : M₁ ->SL[σ₁₂] M₂)
  结论: f (0 : M₁) = 0
  证明: map_zero f
-/
protected theorem map_zero (f : M₁ ->SL[σ₁₂] M₂) : f (0 : M₁) = 0 :=
  map_zero f

/--
theorem `map_add` / 定理 `map_add`

English:
theorem map_add
  given: (f : M₁ ->SL[σ₁₂] M₂) (x y : M₁)
  statement: f (x + y) = f x + f y
  proof: map_add f x y

@[simp]

中文:
定理 map_add
  条件: (f : M₁ ->SL[σ₁₂] M₂) (x y : M₁)
  结论: f (x + y) = f x + f y
  证明: map_add f x y

@[simp]
-/
protected theorem map_add (f : M₁ ->SL[σ₁₂] M₂) (x y : M₁) : f (x + y) = f x + f y :=
  map_add f x y

@[simp]
/--
theorem `map_smulₛₗ` / 定理 `map_smulₛₗ`

English:
theorem map_smulₛₗ
  given: (f : M₁ ->SL[σ₁₂] M₂) (c : R₁) (x : M₁)
  statement: f (c • x) = σ₁₂ c • f x
  proof: (toLinearMap _).map_smulₛₗ _ _

中文:
定理 map_smulₛₗ
  条件: (f : M₁ ->SL[σ₁₂] M₂) (c : R₁) (x : M₁)
  结论: f (c • x) = σ₁₂ c • f x
  证明: (toLinearMap _).map_smulₛₗ _ _
-/
protected theorem map_smulₛₗ (f : M₁ ->SL[σ₁₂] M₂) (c : R₁) (x : M₁) : f (c • x) = σ₁₂ c • f x :=
  (toLinearMap _).map_smulₛₗ _ _

/--
theorem `map_smul` / 定理 `map_smul`

English:
theorem map_smul
  given: [Module R₁ M₂] (f : M₁ ->L[R₁] M₂) (c : R₁) (x : M₁)
  proof: by simp only [RingHom.id_apply, map_smulₛₗ]

@[simp]

中文:
定理 map_smul
  条件: [Module R₁ M₂] (f : M₁ ->L[R₁] M₂) (c : R₁) (x : M₁)
  证明: by simp only [RingHom.id_apply, map_smulₛₗ]

@[simp]
-/
protected theorem map_smul [Module R₁ M₂] (f : M₁ ->L[R₁] M₂) (c : R₁) (x : M₁) :
    f (c • x) = c • f x := by simp only [RingHom.id_apply, map_smulₛₗ]

@[simp]
/--
theorem `map_smul_of_tower` / 定理 `map_smul_of_tower`

English:
theorem map_smul_of_tower
  statement: {R S : Type*} [Semiring S] [SMul R M₁] [Module S M₁] [SMul R M₂]
  proof: LinearMap.CompatibleSMul.map_smul (f : M₁ ->ₗ[S] M₂) c x

@[ext]

中文:
定理 map_smul_of_tower
  结论: {R S : 类型} [Semiring S] [SMul R M₁] [Module S M₁] [SMul R M₂]
  证明: LinearMap.CompatibleSMul.map_smul (f : M₁ ->ₗ[S] M₂) c x

@[ext]

Depends on / 依赖: CompatibleSMul, LinearMap, LinearMap.CompatibleSMul.map_smul, map_smul
-/
theorem map_smul_of_tower {R S : Type*} [Semiring S] [SMul R M₁] [Module S M₁] [SMul R M₂]
    [Module S M₂] [LinearMap.CompatibleSMul M₁ M₂ R S] (f : M₁ ->L[S] M₂) (c : R) (x : M₁) :
    f (c • x) = c • f x :=
  LinearMap.CompatibleSMul.map_smul (f : M₁ ->ₗ[S] M₂) c x

@[ext]
/--
theorem `ext_ring` / 定理 `ext_ring`

English:
theorem ext_ring
  given: [TopologicalSpace R₁] {f g : R₁ ->L[R₁] M₁} (h : f 1 = g 1)
  statement: f = g
  proof: coe_inj.1 LinearMap.ext_ring h

@[simp]

中文:
定理 ext_ring
  条件: [TopologicalSpace R₁] {f g : R₁ ->L[R₁] M₁} (h : f 1 = g 1)
  结论: f = g
  证明: coe_inj.1 LinearMap.ext_ring h

@[simp]

Depends on / 依赖: LinearMap, LinearMap.ext_ring, coe_inj, ext_ring
-/
theorem ext_ring [TopologicalSpace R₁] {f g : R₁ ->L[R₁] M₁} (h : f 1 = g 1) : f = g :=
coe_inj.1 LinearMap.ext_ring h

@[simp]
/--
theorem `apply_val_ker` / 定理 `apply_val_ker`

English:
theorem apply_val_ker
  given: (f : M₁ ->SL[σ₁₂] M₂) (x : f.ker)
  statement: f x = 0
  proof: x.2

中文:
定理 apply_val_ker
  条件: (f : M₁ ->SL[σ₁₂] M₂) (x : f.ker)
  结论: f x = 0
  证明: x.2
-/
theorem apply_val_ker (f : M₁ ->SL[σ₁₂] M₂) (x : f.ker) : f x = 0 := x.2

/--
theorem `eqOn_closure_span` / 定理 `eqOn_closure_span`

English:
theorem eqOn_closure_span
  given: [T2Space M₂] {s : Set M₁} {f g : M₁ ->SL[σ₁₂] M₂} (h : Set.EqOn f g s)
  proof: (LinearMap.eqOn_span' h).closure f.continuous g.continuous

中文:
定理 eqOn_closure_span
  条件: [T2Space M₂] {s : Set M₁} {f g : M₁ ->SL[σ₁₂] M₂} (h : Set.EqOn f g s)
  证明: (LinearMap.eqOn_span' h).closure f.continuous g.continuous

Depends on / 依赖: LinearMap, LinearMap.eqOn_span, closure, continuous, eqOn_span, f.continuous, g.continuous
-/
theorem eqOn_closure_span [T2Space M₂] {s : Set M₁} {f g : M₁ ->SL[σ₁₂] M₂} (h : Set.EqOn f g s) :
    Set.EqOn f g (closure (Submodule.span R₁ s : Set M₁)) :=
  (LinearMap.eqOn_span' h).closure f.continuous g.continuous

/--
theorem `ext_on` / 定理 `ext_on`

English:
theorem ext_on
  statement: [T2Space M₂] {s : Set M₁} (hs : Dense (Submodule.span R₁ s : Set M₁))
  proof: ext fun x => eqOn_closure_span h (hs x)

中文:
定理 ext_on
  结论: [T2Space M₂] {s : Set M₁} (hs : Dense (Submodule.span R₁ s : Set M₁))
  证明: ext fun x => eqOn_closure_span h (hs x)

Depends on / 依赖: eqOn_closure_span
-/
theorem ext_on [T2Space M₂] {s : Set M₁} (hs : Dense (Submodule.span R₁ s : Set M₁))
    {f g : M₁ ->SL[σ₁₂] M₂} (h : Set.EqOn f g s) : f = g :=
  ext fun x => eqOn_closure_span h (hs x)

/--
theorem `_root_.Submodule.topologicalClosure_map` / 定理 `_root_.Submodule.topologicalClosure_map`

English:
theorem _root_.Submodule.topologicalClosure_map
  statement: [RingHomSurjective σ₁₂] [TopologicalSpace R₁]
  proof: image_closure_subset_closure_image f.continuous

中文:
定理 _root_.Submodule.topologicalClosure_map
  结论: [RingHomSurjective σ₁₂] [TopologicalSpace R₁]
  证明: image_closure_subset_closure_image f.continuous

Depends on / 依赖: continuous, f.continuous, image_closure_subset_closure_image
-/
theorem _root_.Submodule.topologicalClosure_map [RingHomSurjective σ₁₂] [TopologicalSpace R₁]
    [TopologicalSpace R₂] [ContinuousSMul R₁ M₁] [ContinuousAdd M₁] [ContinuousSMul R₂ M₂]
    [ContinuousAdd M₂] (f : M₁ ->SL[σ₁₂] M₂) (s : Submodule R₁ M₁) :
    s.topologicalClosure.map (f : M₁ ->ₛₗ[σ₁₂] M₂) <=
      (s.map (f : M₁ ->ₛₗ[σ₁₂] M₂)).topologicalClosure :=
  image_closure_subset_closure_image f.continuous

/--
theorem `_root_.Submodule.topologicalClosure_mem_invtSubmodule` / 定理 `_root_.Submodule.topologicalClosure_mem_invtSubmodule`

English:
theorem _root_.Submodule.topologicalClosure_mem_invtSubmodule
  statement: [TopologicalSpace R₁]
  proof: by
  rw [Module.End.mem_invtSubmodule_iff_map_le] at hs ⊢
  exact (s.topologicalClosure_map f).trans (Submodule.topologicalClosure_mono hs)

中文:
定理 _root_.Submodule.topologicalClosure_mem_invtSubmodule
  结论: [TopologicalSpace R₁]
  证明: by
  rw [Module.End.mem_invtSubmodule_iff_map_le] at hs ⊢
  exact (s.topologicalClosure_map f).trans (Submodule.topologicalClosure_mono hs)

Depends on / 依赖: Module, Module.End.mem_invtSubmodule_iff_map_le, Submodule, Submodule.topologicalClosure_mono, mem_invtSubmodule_iff_map_le, s.topologicalClosure_map, topologicalClosure_map, topologicalClosure_mono
-/
theorem _root_.Submodule.topologicalClosure_mem_invtSubmodule [TopologicalSpace R₁]
    [ContinuousSMul R₁ M₁] [ContinuousAdd M₁] {f : M₁ ->L[R₁] M₁} {s : Submodule R₁ M₁}
    (hs : s in Module.End.invtSubmodule f) :
    s.topologicalClosure in Module.End.invtSubmodule f := by
  rw [Module.End.mem_invtSubmodule_iff_map_le] at hs ⊢
  exact (s.topologicalClosure_map f).trans (Submodule.topologicalClosure_mono hs)

/--
theorem `_root_.DenseRange.topologicalClosure_map_submodule` / 定理 `_root_.DenseRange.topologicalClosure_map_submodule`

English:
theorem _root_.DenseRange.topologicalClosure_map_submodule
  statement: [RingHomSurjective σ₁₂]
  proof: by
  rw [SetLike.ext'_iff] at hs ⊢
  simp only [Submodule.topologicalClosure_coe, Submodule.top_coe, ← dense_iff_closure_eq] at hs ⊢
  exact hf'.dense_image f.continuous hs

中文:
定理 _root_.DenseRange.topologicalClosure_map_submodule
  结论: [RingHomSurjective σ₁₂]
  证明: by
  rw [SetLike.ext'_iff] at hs ⊢
  simp only [Submodule.topologicalClosure_coe, Submodule.top_coe, ← dense_iff_closure_eq] at hs ⊢
  exact hf'.dense_image f.continuous hs

Depends on / 依赖: SetLike, SetLike.ext, Submodule, Submodule.top_coe, Submodule.topologicalClosure_coe, _iff, continuous, dense_iff_closure_eq, dense_image, f.continuous, top_coe, topologicalClosure_coe
-/
theorem _root_.DenseRange.topologicalClosure_map_submodule [RingHomSurjective σ₁₂]
    [TopologicalSpace R₁] [TopologicalSpace R₂] [ContinuousSMul R₁ M₁] [ContinuousAdd M₁]
    [ContinuousSMul R₂ M₂] [ContinuousAdd M₂] {f : M₁ ->SL[σ₁₂] M₂} (hf' : DenseRange f)
    {s : Submodule R₁ M₁} (hs : s.topologicalClosure = ⊤) :
    (s.map (f : M₁ ->ₛₗ[σ₁₂] M₂)).topologicalClosure = ⊤ := by
  rw [SetLike.ext'_iff] at hs ⊢
  simp only [Submodule.topologicalClosure_coe, Submodule.top_coe, ← dense_iff_closure_eq] at hs ⊢
  exact hf'.dense_image f.continuous hs

section SMul

variable {S₂ T₂ : Type*}
variable [DistribSMul S₂ M₂] [SMulCommClass R₂ S₂ M₂] [ContinuousConstSMul S₂ M₂]
variable [DistribSMul T₂ M₂] [SMulCommClass R₂ T₂ M₂] [ContinuousConstSMul T₂ M₂]

/--
Instance `instSMul` / 实例 `instSMul`

English:
instance instSMul
  signature: : SMul S₂ (M₁ ->SL[σ₁₂] M₂) where
  body: ⟨c • (f : M₁ ->ₛₗ[σ₁₂] M₂), (f.2.const_smul _ : Continuous fun x => c • f x)⟩

中文:
实例 instSMul
  签名: : SMul S₂ (M₁ ->SL[σ₁₂] M₂) where
  定义体: ⟨c • (f : M₁ ->ₛₗ[σ₁₂] M₂), (f.2.const_smul _ : Continuous fun x => c • f x)⟩

Depends on / 依赖: Continuous, const_smul
-/
instance instSMul : SMul S₂ (M₁ ->SL[σ₁₂] M₂) where
  smul c f := ⟨c • (f : M₁ ->ₛₗ[σ₁₂] M₂), (f.2.const_smul _ : Continuous fun x => c • f x)⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsSMulApply S₂ (M₁ ->SL[σ₁₂] M₂) M₁ M₂
  body: rfl

@[simp, norm_cast]

中文:
实例 :
  签名: IsSMulApply S₂ (M₁ ->SL[σ₁₂] M₂) M₁ M₂
  定义体: rfl

@[simp, norm_cast]
-/
instance : IsSMulApply S₂ (M₁ ->SL[σ₁₂] M₂) M₁ M₂ where
  smul_apply _ _ _ := rfl

@[simp, norm_cast]
/--
theorem `toLinearMap_smul` / 定理 `toLinearMap_smul`

English:
theorem toLinearMap_smul
  given: (c : S₂) (f : M₁ ->SL[σ₁₂] M₂)
  proof: rfl

@[deprecated (since := "2026-05-20")] protected alias smul_apply := _root_.smul_apply

@[deprecated (since := "2026-05-20")] protected alias coe_smul := toLinearMap_smul

@[deprecated (since := "2026-05-20")] alias coe_smul' := FunLike.coe_smul

中文:
定理 toLinearMap_smul
  条件: (c : S₂) (f : M₁ ->SL[σ₁₂] M₂)
  证明: rfl

@[deprecated (since := "2026-05-20")] protected alias smul_apply := _root_.smul_apply

@[deprecated (since := "2026-05-20")] protected alias coe_smul := toLinearMap_smul

@[deprecated (since := "2026-05-20")] alias coe_smul' := FunLike.coe_smul
-/
theorem toLinearMap_smul (c : S₂) (f : M₁ ->SL[σ₁₂] M₂) :
    ↑(c • f) = c • (f : M₁ ->ₛₗ[σ₁₂] M₂) :=
  rfl

@[deprecated (since := "2026-05-20")] protected alias smul_apply := _root_.smul_apply

@[deprecated (since := "2026-05-20")] protected alias coe_smul := toLinearMap_smul

@[deprecated (since := "2026-05-20")] alias coe_smul' := FunLike.coe_smul

/--
Instance `isScalarTower` / 实例 `isScalarTower`

English:
instance isScalarTower
  signature: [SMul S₂ T₂] [IsScalarTower S₂ T₂ M₂]
  body: FunLike.isScalarTower

中文:
实例 isScalarTower
  签名: [SMul S₂ T₂] [IsScalarTower S₂ T₂ M₂]
  定义体: FunLike.isScalarTower

Depends on / 依赖: FunLike, FunLike.isScalarTower, isScalarTower
-/
instance isScalarTower [SMul S₂ T₂] [IsScalarTower S₂ T₂ M₂] :
    IsScalarTower S₂ T₂ (M₁ ->SL[σ₁₂] M₂) := FunLike.isScalarTower

/--
Instance `smulCommClass` / 实例 `smulCommClass`

English:
instance smulCommClass
  signature: [SMulCommClass S₂ T₂ M₂]
  body: FunLike.smulCommClass

中文:
实例 smulCommClass
  签名: [SMulCommClass S₂ T₂ M₂]
  定义体: FunLike.smulCommClass

Depends on / 依赖: FunLike, FunLike.smulCommClass, smulCommClass
-/
instance smulCommClass [SMulCommClass S₂ T₂ M₂] : SMulCommClass S₂ T₂ (M₁ ->SL[σ₁₂] M₂) :=
  FunLike.smulCommClass

end SMul

section SMulMonoid

variable {S₂ : Type*} [Monoid S₂]
variable [DistribMulAction S₂ M₂] [SMulCommClass R₂ S₂ M₂] [ContinuousConstSMul S₂ M₂]

/--
Instance `mulAction` / 实例 `mulAction`

English:
instance mulAction
  signature: : MulAction S₂ (M₁ ->SL[σ₁₂] M₂)
  body: fast_instance% FunLike.mulAction

中文:
实例 mulAction
  签名: : MulAction S₂ (M₁ ->SL[σ₁₂] M₂)
  定义体: fast_instance% FunLike.mulAction

Depends on / 依赖: FunLike, FunLike.mulAction, fast_instance, mulAction
-/
instance mulAction : MulAction S₂ (M₁ ->SL[σ₁₂] M₂) := fast_instance% FunLike.mulAction

end SMulMonoid

/--
Instance `zero` / 实例 `zero`

English:
instance zero
  signature: : Zero (M₁ ->SL[σ₁₂] M₂)
  body: ⟨⟨0, continuous_zero⟩⟩

中文:
实例 zero
  签名: : Zero (M₁ ->SL[σ₁₂] M₂)
  定义体: ⟨⟨0, continuous_zero⟩⟩

Depends on / 依赖: continuous_zero
-/
instance zero : Zero (M₁ ->SL[σ₁₂] M₂) :=
  ⟨⟨0, continuous_zero⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsZeroApply (M₁ ->SL[σ₁₂] M₂) M₁ M₂
  body: rfl

中文:
实例 :
  签名: IsZeroApply (M₁ ->SL[σ₁₂] M₂) M₁ M₂
  定义体: rfl
-/
instance : IsZeroApply (M₁ ->SL[σ₁₂] M₂) M₁ M₂ where
  zero_apply _ := rfl

/--
Instance `inhabited` / 实例 `inhabited`

English:
instance inhabited
  signature: : Inhabited (M₁ ->SL[σ₁₂] M₂)
  body: ⟨0⟩

@[simp]

中文:
实例 inhabited
  签名: : Inhabited (M₁ ->SL[σ₁₂] M₂)
  定义体: ⟨0⟩

@[simp]
-/
instance inhabited : Inhabited (M₁ ->SL[σ₁₂] M₂) :=
  ⟨0⟩

@[simp]
/--
theorem `default_def` / 定理 `default_def`

English:
theorem default_def
  statement: (default : M₁ ->SL[σ₁₂] M₂) = 0
  proof: rfl

@[simp, norm_cast]

中文:
定理 default_def
  结论: (default : M₁ ->SL[σ₁₂] M₂) = 0
  证明: rfl

@[simp, norm_cast]
-/
theorem default_def : (default : M₁ ->SL[σ₁₂] M₂) = 0 :=
  rfl

@[simp, norm_cast]
/--
theorem `toLinearMap_zero` / 定理 `toLinearMap_zero`

English:
theorem toLinearMap_zero
  statement: ((0 : M₁ ->SL[σ₁₂] M₂) : M₁ ->ₛₗ[σ₁₂] M₂) = 0
  proof: rfl

@[deprecated (since := "2026-05-20")] protected alias zero_apply := _root_.zero_apply

@[deprecated (since := "2026-05-20")] protected alias coe_zero := toLinearMap_zero

@[deprecated (since := "2026-05-20")] alias coe_zero' := FunLike.coe_zero

@[simp, norm_cast]

中文:
定理 toLinearMap_zero
  结论: ((0 : M₁ ->SL[σ₁₂] M₂) : M₁ ->ₛₗ[σ₁₂] M₂) = 0
  证明: rfl

@[deprecated (since := "2026-05-20")] protected alias zero_apply := _root_.zero_apply

@[deprecated (since := "2026-05-20")] protected alias coe_zero := toLinearMap_zero

@[deprecated (since := "2026-05-20")] alias coe_zero' := FunLike.coe_zero

@[simp, norm_cast]
-/
theorem toLinearMap_zero : ((0 : M₁ ->SL[σ₁₂] M₂) : M₁ ->ₛₗ[σ₁₂] M₂) = 0 :=
  rfl

@[deprecated (since := "2026-05-20")] protected alias zero_apply := _root_.zero_apply

@[deprecated (since := "2026-05-20")] protected alias coe_zero := toLinearMap_zero

@[deprecated (since := "2026-05-20")] alias coe_zero' := FunLike.coe_zero

@[simp, norm_cast]
/--
theorem `toContinuousAddMonoidHom_zero` / 定理 `toContinuousAddMonoidHom_zero`

English:
theorem toContinuousAddMonoidHom_zero
  proof: rfl

中文:
定理 toContinuousAddMonoidHom_zero
  证明: rfl
-/
theorem toContinuousAddMonoidHom_zero :
    ((0 : M₁ ->SL[σ₁₂] M₂) : ContinuousAddMonoidHom M₁ M₂) = 0 := rfl

/--
Instance `uniqueOfLeft` / 实例 `uniqueOfLeft`

English:
instance uniqueOfLeft
  signature: [Subsingleton M₁]
  body: coe_injective.unique

中文:
实例 uniqueOfLeft
  签名: [Subsingleton M₁]
  定义体: coe_injective.unique

Depends on / 依赖: coe_injective, coe_injective.unique, unique
-/
instance uniqueOfLeft [Subsingleton M₁] : Unique (M₁ ->SL[σ₁₂] M₂) :=
  coe_injective.unique

/--
Instance `uniqueOfRight` / 实例 `uniqueOfRight`

English:
instance uniqueOfRight
  signature: [Subsingleton M₂]
  body: coe_injective.unique

中文:
实例 uniqueOfRight
  签名: [Subsingleton M₂]
  定义体: coe_injective.unique

Depends on / 依赖: coe_injective, coe_injective.unique, unique
-/
instance uniqueOfRight [Subsingleton M₂] : Unique (M₁ ->SL[σ₁₂] M₂) :=
  coe_injective.unique

/--
theorem `exists_ne_zero` / 定理 `exists_ne_zero`

English:
theorem exists_ne_zero
  given: {f : M₁ ->SL[σ₁₂] M₂} (hf : f != 0)
  statement: exists x, f x != 0
  proof: by
  by_contra! h
  exact hf (ContinuousLinearMap.ext h)

中文:
定理 exists_ne_zero
  条件: {f : M₁ ->SL[σ₁₂] M₂} (hf : f != 0)
  结论: 存在 x, f x != 0
  证明: by
  by_contra! h
  exact hf (ContinuousLinearMap.ext h)

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.ext
-/
theorem exists_ne_zero {f : M₁ ->SL[σ₁₂] M₂} (hf : f != 0) : exists x, f x != 0 := by
  by_contra! h
  exact hf (ContinuousLinearMap.ext h)

section

variable (R₁ M₁)

/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : M₁ ->L[R₁] M₁
  body: ⟨LinearMap.id, continuous_id⟩

中文:
定义 id
  签名: : M₁ ->L[R₁] M₁
  定义体: ⟨LinearMap.id, continuous_id⟩
-/
protected def id : M₁ ->L[R₁] M₁ :=
  ⟨LinearMap.id, continuous_id⟩

end

/--
Instance `one` / 实例 `one`

English:
instance one
  signature: : One (M₁ ->L[R₁] M₁)
  body: ⟨.id R₁ M₁⟩

中文:
实例 one
  签名: : One (M₁ ->L[R₁] M₁)
  定义体: ⟨.id R₁ M₁⟩
-/
instance one : One (M₁ ->L[R₁] M₁) :=
  ⟨.id R₁ M₁⟩

/--
theorem `one_def` / 定理 `one_def`

English:
theorem one_def
  statement: (1 : M₁ ->L[R₁] M₁) = .id R₁ M₁
  proof: rfl

中文:
定理 one_def
  结论: (1 : M₁ ->L[R₁] M₁) = .id R₁ M₁
  证明: rfl
-/
theorem one_def : (1 : M₁ ->L[R₁] M₁) = .id R₁ M₁ := rfl

/--
Instance `instIsOneApply` / 实例 `instIsOneApply`

English:
instance instIsOneApply
  signature: : IsOneApplyEqSelf (M₁ ->L[R₁] M₁) M₁ where
  body: rfl

@[simp]

中文:
实例 instIsOneApply
  签名: : IsOneApplyEqSelf (M₁ ->L[R₁] M₁) M₁ where
  定义体: rfl

@[simp]
-/
instance instIsOneApply : IsOneApplyEqSelf (M₁ ->L[R₁] M₁) M₁ where
  one_apply_eq_self _ := rfl

@[simp]
/--
theorem `id_apply` / 定理 `id_apply`

English:
theorem id_apply
  given: (x : M₁)
  statement: ContinuousLinearMap.id R₁ M₁ x = x
  proof: rfl

@[simp, norm_cast]

中文:
定理 id_apply
  条件: (x : M₁)
  结论: ContinuousLinearMap.id R₁ M₁ x = x
  证明: rfl

@[simp, norm_cast]
-/
theorem id_apply (x : M₁) : ContinuousLinearMap.id R₁ M₁ x = x := rfl

@[simp, norm_cast]
/--
theorem `coe_id` / 定理 `coe_id`

English:
theorem coe_id
  statement: (ContinuousLinearMap.id R₁ M₁ : M₁ ->ₗ[R₁] M₁) = LinearMap.id
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_id
  结论: (ContinuousLinearMap.id R₁ M₁ : M₁ ->ₗ[R₁] M₁) = LinearMap.id
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_id : (ContinuousLinearMap.id R₁ M₁ : M₁ ->ₗ[R₁] M₁) = LinearMap.id :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_id'` / 定理 `coe_id'`

English:
theorem coe_id'
  statement: ⇑(ContinuousLinearMap.id R₁ M₁) = id
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_id'
  结论: ⇑(ContinuousLinearMap.id R₁ M₁) = id
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_id' : ⇑(ContinuousLinearMap.id R₁ M₁) = id :=
  rfl

@[simp, norm_cast]
/--
theorem `toLinearMap_one` / 定理 `toLinearMap_one`

English:
theorem toLinearMap_one
  statement: ((1 : M₁ ->L[R₁] M₁) : M₁ ->ₗ[R₁] M₁) = 1
  proof: rfl

@[deprecated (since := "2026-05-20")] protected alias coe_one := toLinearMap_one

中文:
定理 toLinearMap_one
  结论: ((1 : M₁ ->L[R₁] M₁) : M₁ ->ₗ[R₁] M₁) = 1
  证明: rfl

@[deprecated (since := "2026-05-20")] protected alias coe_one := toLinearMap_one
-/
theorem toLinearMap_one : ((1 : M₁ ->L[R₁] M₁) : M₁ ->ₗ[R₁] M₁) = 1 :=
  rfl

@[deprecated (since := "2026-05-20")] protected alias coe_one := toLinearMap_one

/--
lemma `mk_id` / 引理 `mk_id`

English:
lemma mk_id
  statement: mk (.id : M₁ ->ₗ[R₁] M₁) continuous_id = .id _ _
  proof: rfl

中文:
引理 mk_id
  结论: mk (.id : M₁ ->ₗ[R₁] M₁) continuous_id = .id _ _
  证明: rfl
-/
@[simp] lemma mk_id : mk (.id : M₁ ->ₗ[R₁] M₁) continuous_id = .id _ _ := rfl
/--
lemma `mk_one` / 引理 `mk_one`

English:
lemma mk_one
  statement: mk (1 : M₁ ->ₗ[R₁] M₁) continuous_id = 1
  proof: rfl

@[simp, norm_cast]

中文:
引理 mk_one
  结论: mk (1 : M₁ ->ₗ[R₁] M₁) continuous_id = 1
  证明: rfl

@[simp, norm_cast]
-/
@[simp] lemma mk_one : mk (1 : M₁ ->ₗ[R₁] M₁) continuous_id = 1 := rfl

@[simp, norm_cast]
/--
theorem `toContinuousAddMonoidHom_id` / 定理 `toContinuousAddMonoidHom_id`

English:
theorem toContinuousAddMonoidHom_id
  proof: rfl

@[simp, norm_cast]

中文:
定理 toContinuousAddMonoidHom_id
  证明: rfl

@[simp, norm_cast]
-/
theorem toContinuousAddMonoidHom_id :
    (ContinuousLinearMap.id R₁ M₁ : ContinuousAddMonoidHom M₁ M₁) = .id _ := rfl

@[simp, norm_cast]
/--
theorem `coe_eq_id` / 定理 `coe_eq_id`

English:
theorem coe_eq_id
  given: {f : M₁ ->L[R₁] M₁}
  statement: (f : M₁ ->ₗ[R₁] M₁) = LinearMap.id ↔ f = .id _ _
  proof: by
  rw [← coe_id]; rw [coe_inj]

@[deprecated (since := "2026-05-20")] protected alias one_apply := one_apply_eq_self

中文:
定理 coe_eq_id
  条件: {f : M₁ ->L[R₁] M₁}
  结论: (f : M₁ ->ₗ[R₁] M₁) = LinearMap.id ↔ f = .id _ _
  证明: by
  rw [← coe_id]; rw [coe_inj]

@[deprecated (since := "2026-05-20")] protected alias one_apply := one_apply_eq_self

Depends on / 依赖: coe_id, coe_inj
-/
theorem coe_eq_id {f : M₁ ->L[R₁] M₁} : (f : M₁ ->ₗ[R₁] M₁) = LinearMap.id ↔ f = .id _ _ := by
  rw [← coe_id]; rw [coe_inj]

@[deprecated (since := "2026-05-20")] protected alias one_apply := one_apply_eq_self

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nontrivial
  signature: M₁] : Nontrivial (M₁ ->L[R₁] M₁)
  body: ⟨0, 1, fun e =>
    have ⟨x, hx⟩ := exists_ne (0 : M₁); hx (by simpa using DFunLike.congr_fun e.symm x)⟩

中文:
实例 [Nontrivial
  签名: M₁] : Nontrivial (M₁ ->L[R₁] M₁)
  定义体: ⟨0, 1, fun e =>
    have ⟨x, hx⟩ := exists_ne (0 : M₁); hx (by simpa using DFunLike.congr_fun e.symm x)⟩

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun, e.symm, exists_ne
-/
instance [Nontrivial M₁] : Nontrivial (M₁ ->L[R₁] M₁) :=
  ⟨0, 1, fun e =>
    have ⟨x, hx⟩ := exists_ne (0 : M₁); hx (by simpa using DFunLike.congr_fun e.symm x)⟩

section Add

variable [ContinuousAdd M₂]

/--
Instance `add` / 实例 `add`

English:
instance add
  signature: : Add (M₁ ->SL[σ₁₂] M₂)
  body: ⟨fun f g => ⟨f + g, f.2.add g.2⟩⟩

中文:
实例 add
  签名: : Add (M₁ ->SL[σ₁₂] M₂)
  定义体: ⟨fun f g => ⟨f + g, f.2.add g.2⟩⟩
-/
instance add : Add (M₁ ->SL[σ₁₂] M₂) :=
  ⟨fun f g => ⟨f + g, f.2.add g.2⟩⟩

/--
Instance `instIsAddApply` / 实例 `instIsAddApply`

English:
instance instIsAddApply
  signature: : IsAddApply (M₁ ->SL[σ₁₂] M₂) M₁ M₂ where
  body: rfl

@[simp, norm_cast]

中文:
实例 instIsAddApply
  签名: : IsAddApply (M₁ ->SL[σ₁₂] M₂) M₁ M₂ where
  定义体: rfl

@[simp, norm_cast]
-/
instance instIsAddApply : IsAddApply (M₁ ->SL[σ₁₂] M₂) M₁ M₂ where
  add_apply _ _ _ := rfl

@[simp, norm_cast]
/--
theorem `toLinearMap_add` / 定理 `toLinearMap_add`

English:
theorem toLinearMap_add
  given: (f g : M₁ ->SL[σ₁₂] M₂)
  statement: (↑(f + g) : M₁ ->ₛₗ[σ₁₂] M₂) = f + g
  proof: rfl

@[deprecated (since := "2026-05-20")] protected alias add_apply := _root_.add_apply

@[deprecated (since := "2026-05-20")] protected alias coe_add := toLinearMap_add

@[deprecated (since := "2026-05-20")] alias coe_add' := FunLike.coe_add

@[simp, norm_cast]

中文:
定理 toLinearMap_add
  条件: (f g : M₁ ->SL[σ₁₂] M₂)
  结论: (↑(f + g) : M₁ ->ₛₗ[σ₁₂] M₂) = f + g
  证明: rfl

@[deprecated (since := "2026-05-20")] protected alias add_apply := _root_.add_apply

@[deprecated (since := "2026-05-20")] protected alias coe_add := toLinearMap_add

@[deprecated (since := "2026-05-20")] alias coe_add' := FunLike.coe_add

@[simp, norm_cast]
-/
theorem toLinearMap_add (f g : M₁ ->SL[σ₁₂] M₂) : (↑(f + g) : M₁ ->ₛₗ[σ₁₂] M₂) = f + g :=
  rfl

@[deprecated (since := "2026-05-20")] protected alias add_apply := _root_.add_apply

@[deprecated (since := "2026-05-20")] protected alias coe_add := toLinearMap_add

@[deprecated (since := "2026-05-20")] alias coe_add' := FunLike.coe_add

@[simp, norm_cast]
/--
theorem `toContinuousAddMonoidHom_add` / 定理 `toContinuousAddMonoidHom_add`

English:
theorem toContinuousAddMonoidHom_add
  given: (f g : M₁ ->SL[σ₁₂] M₂)
  proof: rfl

中文:
定理 toContinuousAddMonoidHom_add
  条件: (f g : M₁ ->SL[σ₁₂] M₂)
  证明: rfl
-/
theorem toContinuousAddMonoidHom_add (f g : M₁ ->SL[σ₁₂] M₂) :
    ↑(f + g) = (f + g : ContinuousAddMonoidHom M₁ M₂) := rfl

-- The `AddMonoid` instance exists to help speedup unification
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddMonoid (M₁ ->SL[σ₁₂] M₂)
  body: fast_instance% FunLike.addMonoid

中文:
实例 :
  签名: AddMonoid (M₁ ->SL[σ₁₂] M₂)
  定义体: fast_instance% FunLike.addMonoid

Depends on / 依赖: FunLike, FunLike.addMonoid, addMonoid, fast_instance
-/
instance : AddMonoid (M₁ ->SL[σ₁₂] M₂) := fast_instance% FunLike.addMonoid

/--
Instance `addCommMonoid` / 实例 `addCommMonoid`

English:
instance addCommMonoid
  signature: : AddCommMonoid (M₁ ->SL[σ₁₂] M₂)
  body: fast_instance% FunLike.addCommMonoid

@[simp, norm_cast]

中文:
实例 addCommMonoid
  签名: : AddCommMonoid (M₁ ->SL[σ₁₂] M₂)
  定义体: fast_instance% FunLike.addCommMonoid

@[simp, norm_cast]

Depends on / 依赖: FunLike, FunLike.addCommMonoid, addCommMonoid, fast_instance
-/
instance addCommMonoid : AddCommMonoid (M₁ ->SL[σ₁₂] M₂) := fast_instance% FunLike.addCommMonoid

@[simp, norm_cast]
/--
theorem `toLinearMap_sum` / 定理 `toLinearMap_sum`

English:
theorem toLinearMap_sum
  given: {ι : Type*} (t : Finset ι) (f : ι -> M₁ ->SL[σ₁₂] M₂)
  proof: map_sum (AddMonoidHom.mk ⟨((↑) : (M₁ ->SL[σ₁₂] M₂) -> M₁ ->ₛₗ[σ₁₂] M₂), rfl⟩ fun _ _ => rfl) _ _

@[deprecated (since := "2026-05-20")] protected alias sum_apply := _root_.sum_apply

@[deprecated (since := "2026-05-20")] protected alias coe_sum := toLinearMap_sum

@[deprecated (since := "2026-05-20"

中文:
定理 toLinearMap_sum
  条件: {ι : 类型} (t : Finset ι) (f : ι -> M₁ ->SL[σ₁₂] M₂)
  证明: map_sum (AddMonoidHom.mk ⟨((↑) : (M₁ ->SL[σ₁₂] M₂) -> M₁ ->ₛₗ[σ₁₂] M₂), rfl⟩ fun _ _ => rfl) _ _

@[deprecated (since := "2026-05-20")] protected alias sum_apply := _root_.sum_apply

@[deprecated (since := "2026-05-20")] protected alias coe_sum := toLinearMap_sum

@[deprecated (since := "2026-05-20"

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mk, map_sum
-/
theorem toLinearMap_sum {ι : Type*} (t : Finset ι) (f : ι -> M₁ ->SL[σ₁₂] M₂) :
    ↑(∑ d in t, f d) = (∑ d in t, f d : M₁ ->ₛₗ[σ₁₂] M₂) :=
  map_sum (AddMonoidHom.mk ⟨((↑) : (M₁ ->SL[σ₁₂] M₂) -> M₁ ->ₛₗ[σ₁₂] M₂), rfl⟩ fun _ _ => rfl) _ _

@[deprecated (since := "2026-05-20")] protected alias sum_apply := _root_.sum_apply

@[deprecated (since := "2026-05-20")] protected alias coe_sum := toLinearMap_sum

@[deprecated (since := "2026-05-20")] alias coe_sum' := FunLike.coe_sum

end Add

variable [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (g : M₂ ->SL[σ₂₃] M₃) (f : M₁ ->SL[σ₁₂] M₂)
  body: ⟨(g : M₂ ->ₛₗ[σ₂₃] M₃).comp (f : M₁ ->ₛₗ[σ₁₂] M₂), g.2.comp f.2⟩

@[inherit_doc comp]
infixr:80 " ∘L " =>
  @ContinuousLinearMap.comp _ _ _ _ _ _ (RingHom.id _) (RingHom.id _) (RingHom.id _) _ _ _ _ _ _ _ _
    _ _ _ _ RingHomCompTriple.ids

@[inherit_doc comp]
infixr:90 " ∘SL " =>
  ContinuousLinea

中文:
定义 comp
  签名: (g : M₂ ->SL[σ₂₃] M₃) (f : M₁ ->SL[σ₁₂] M₂)
  定义体: ⟨(g : M₂ ->ₛₗ[σ₂₃] M₃).comp (f : M₁ ->ₛₗ[σ₁₂] M₂), g.2.comp f.2⟩

@[inherit_doc comp]
infixr:80 " ∘L " =>
  @ContinuousLinearMap.comp _ _ _ _ _ _ (RingHom.id _) (RingHom.id _) (RingHom.id _) _ _ _ _ _ _ _ _
    _ _ _ _ RingHomCompTriple.ids

@[inherit_doc comp]
infixr:90 " ∘SL " =>
  ContinuousLinea
-/
def comp (g : M₂ ->SL[σ₂₃] M₃) (f : M₁ ->SL[σ₁₂] M₂) : M₁ ->SL[σ₁₃] M₃ :=
  ⟨(g : M₂ ->ₛₗ[σ₂₃] M₃).comp (f : M₁ ->ₛₗ[σ₁₂] M₂), g.2.comp f.2⟩

@[inherit_doc comp]
infixr:80 " ∘L " =>
  @ContinuousLinearMap.comp _ _ _ _ _ _ (RingHom.id _) (RingHom.id _) (RingHom.id _) _ _ _ _ _ _ _ _
    _ _ _ _ RingHomCompTriple.ids

@[inherit_doc comp]
infixr:90 " ∘SL " =>
  ContinuousLinearMap.comp

@[simp, norm_cast]
/--
theorem `toLinearMap_comp` / 定理 `toLinearMap_comp`

English:
theorem toLinearMap_comp
  given: (h : M₂ ->SL[σ₂₃] M₃) (f : M₁ ->SL[σ₁₂] M₂)
  proof: rfl

@[norm_cast]

中文:
定理 toLinearMap_comp
  条件: (h : M₂ ->SL[σ₂₃] M₃) (f : M₁ ->SL[σ₁₂] M₂)
  证明: rfl

@[norm_cast]
-/
theorem toLinearMap_comp (h : M₂ ->SL[σ₂₃] M₃) (f : M₁ ->SL[σ₁₂] M₂) :
    (h ∘SL f : M₁ ->ₛₗ[σ₁₃] M₃) = (h : M₂ ->ₛₗ[σ₂₃] M₃) ∘ₛₗ (f : M₁ ->ₛₗ[σ₁₂] M₂) :=
  rfl

@[norm_cast]
/--
theorem `coe_comp` / 定理 `coe_comp`

English:
theorem coe_comp
  given: (h : M₂ ->SL[σ₂₃] M₃) (f : M₁ ->SL[σ₁₂] M₂)
  statement: ⇑(h ∘SL f) = h ∘ f
  proof: rfl

@[deprecated (since := "2026-05-20")] alias coe_comp' := coe_comp

@[simp, norm_cast]

中文:
定理 coe_comp
  条件: (h : M₂ ->SL[σ₂₃] M₃) (f : M₁ ->SL[σ₁₂] M₂)
  结论: ⇑(h ∘SL f) = h ∘ f
  证明: rfl

@[deprecated (since := "2026-05-20")] alias coe_comp' := coe_comp

@[simp, norm_cast]
-/
theorem coe_comp (h : M₂ ->SL[σ₂₃] M₃) (f : M₁ ->SL[σ₁₂] M₂) : ⇑(h ∘SL f) = h ∘ f :=
  rfl

@[deprecated (since := "2026-05-20")] alias coe_comp' := coe_comp

@[simp, norm_cast]
/--
theorem `toContinuousAddMonoidHom_comp` / 定理 `toContinuousAddMonoidHom_comp`

English:
theorem toContinuousAddMonoidHom_comp
  given: (h : M₂ ->SL[σ₂₃] M₃) (f : M₁ ->SL[σ₁₂] M₂)
  proof: rfl

@[simp, grind =]

中文:
定理 toContinuousAddMonoidHom_comp
  条件: (h : M₂ ->SL[σ₂₃] M₃) (f : M₁ ->SL[σ₁₂] M₂)
  证明: rfl

@[simp, grind =]
-/
theorem toContinuousAddMonoidHom_comp (h : M₂ ->SL[σ₂₃] M₃) (f : M₁ ->SL[σ₁₂] M₂) :
    (↑(h ∘SL f) : ContinuousAddMonoidHom M₁ M₃) = (h : ContinuousAddMonoidHom M₂ M₃).comp f := rfl

@[simp, grind =]
/--
theorem `comp_apply` / 定理 `comp_apply`

English:
theorem comp_apply
  given: (g : M₂ ->SL[σ₂₃] M₃) (f : M₁ ->SL[σ₁₂] M₂) (x : M₁)
  statement: (g ∘SL f) x = g (f x)
  proof: rfl

@[simp]

中文:
定理 comp_apply
  条件: (g : M₂ ->SL[σ₂₃] M₃) (f : M₁ ->SL[σ₁₂] M₂) (x : M₁)
  结论: (g ∘SL f) x = g (f x)
  证明: rfl

@[simp]
-/
theorem comp_apply (g : M₂ ->SL[σ₂₃] M₃) (f : M₁ ->SL[σ₁₂] M₂) (x : M₁) : (g ∘SL f) x = g (f x) :=
  rfl

@[simp]
/--
theorem `comp_id` / 定理 `comp_id`

English:
theorem comp_id
  given: (f : M₁ ->SL[σ₁₂] M₂)
  statement: f ∘SL .id R₁ M₁ = f
  proof: ext fun _x => rfl

@[simp]

中文:
定理 comp_id
  条件: (f : M₁ ->SL[σ₁₂] M₂)
  结论: f ∘SL .id R₁ M₁ = f
  证明: ext fun _x => rfl

@[simp]
-/
theorem comp_id (f : M₁ ->SL[σ₁₂] M₂) : f ∘SL .id R₁ M₁ = f :=
  ext fun _x => rfl

@[simp]
/--
theorem `id_comp` / 定理 `id_comp`

English:
theorem id_comp
  given: (f : M₁ ->SL[σ₁₂] M₂)
  statement: .id R₂ M₂ ∘SL f = f
  proof: ext fun _x => rfl

中文:
定理 id_comp
  条件: (f : M₁ ->SL[σ₁₂] M₂)
  结论: .id R₂ M₂ ∘SL f = f
  证明: ext fun _x => rfl
-/
theorem id_comp (f : M₁ ->SL[σ₁₂] M₂) : .id R₂ M₂ ∘SL f = f :=
  ext fun _x => rfl

section

variable {R E F : Type*} [Semiring R]
  [TopologicalSpace E] [AddCommMonoid E] [Module R E]
  [TopologicalSpace F] [AddCommMonoid F] [Module R F]

/--
lemma `leftInverse_of_comp` / 引理 `leftInverse_of_comp`

English:
lemma leftInverse_of_comp
  statement: {f : E ->L[R] F} {g : F ->L[R] E}
  proof: by
  simpa [coe_comp, ← Function.leftInverse_iff_comp] using congr(⇑$hinv)

中文:
引理 leftInverse_of_comp
  结论: {f : E ->L[R] F} {g : F ->L[R] E}
  证明: by
  simpa [coe_comp, ← Function.leftInverse_iff_comp] using congr(⇑$hinv)

Depends on / 依赖: Function, Function.leftInverse_iff_comp, coe_comp, leftInverse_iff_comp
-/
lemma leftInverse_of_comp {f : E ->L[R] F} {g : F ->L[R] E}
    (hinv : g ∘L f = .id R E) : Function.LeftInverse g f := by
  simpa [coe_comp, ← Function.leftInverse_iff_comp] using congr(⇑$hinv)

/--
lemma `rightInverse_of_comp` / 引理 `rightInverse_of_comp`

English:
lemma rightInverse_of_comp
  statement: {f : E ->L[R] F} {g : F ->L[R] E}
  proof: leftInverse_of_comp hinv

中文:
引理 rightInverse_of_comp
  结论: {f : E ->L[R] F} {g : F ->L[R] E}
  证明: leftInverse_of_comp hinv

Depends on / 依赖: leftInverse_of_comp
-/
lemma rightInverse_of_comp {f : E ->L[R] F} {g : F ->L[R] E}
    (hinv : f ∘L g = .id R F) : Function.RightInverse g f :=
  leftInverse_of_comp hinv

end

@[simp]
/--
theorem `comp_zero` / 定理 `comp_zero`

English:
theorem comp_zero
  given: (g : M₂ ->SL[σ₂₃] M₃)
  statement: g ∘SL (0 : M₁ ->SL[σ₁₂] M₂) = 0
  proof: by
  ext
  simp

@[simp]

中文:
定理 comp_zero
  条件: (g : M₂ ->SL[σ₂₃] M₃)
  结论: g ∘SL (0 : M₁ ->SL[σ₁₂] M₂) = 0
  证明: by
  ext
  simp

@[simp]
-/
theorem comp_zero (g : M₂ ->SL[σ₂₃] M₃) : g ∘SL (0 : M₁ ->SL[σ₁₂] M₂) = 0 := by
  ext
  simp

@[simp]
/--
theorem `zero_comp` / 定理 `zero_comp`

English:
theorem zero_comp
  given: (f : M₁ ->SL[σ₁₂] M₂)
  statement: (0 : M₂ ->SL[σ₂₃] M₃) ∘SL f = 0
  proof: by
  ext
  simp

@[simp]

中文:
定理 zero_comp
  条件: (f : M₁ ->SL[σ₁₂] M₂)
  结论: (0 : M₂ ->SL[σ₂₃] M₃) ∘SL f = 0
  证明: by
  ext
  simp

@[simp]
-/
theorem zero_comp (f : M₁ ->SL[σ₁₂] M₂) : (0 : M₂ ->SL[σ₂₃] M₃) ∘SL f = 0 := by
  ext
  simp

@[simp]
/--
theorem `comp_add` / 定理 `comp_add`

English:
theorem comp_add
  statement: [ContinuousAdd M₂] [ContinuousAdd M₃] (g : M₂ ->SL[σ₂₃] M₃)
  proof: by
  ext
  simp

@[simp]

中文:
定理 comp_add
  结论: [ContinuousAdd M₂] [ContinuousAdd M₃] (g : M₂ ->SL[σ₂₃] M₃)
  证明: by
  ext
  simp

@[simp]
-/
theorem comp_add [ContinuousAdd M₂] [ContinuousAdd M₃] (g : M₂ ->SL[σ₂₃] M₃)
    (f₁ f₂ : M₁ ->SL[σ₁₂] M₂) : g ∘SL (f₁ + f₂) = g ∘SL f₁ + g ∘SL f₂ := by
  ext
  simp

@[simp]
/--
theorem `add_comp` / 定理 `add_comp`

English:
theorem add_comp
  given: [ContinuousAdd M₃] (g₁ g₂ : M₂ ->SL[σ₂₃] M₃) (f : M₁ ->SL[σ₁₂] M₂)
  proof: by
  ext
  simp

中文:
定理 add_comp
  条件: [ContinuousAdd M₃] (g₁ g₂ : M₂ ->SL[σ₂₃] M₃) (f : M₁ ->SL[σ₁₂] M₂)
  证明: by
  ext
  simp
-/
theorem add_comp [ContinuousAdd M₃] (g₁ g₂ : M₂ ->SL[σ₂₃] M₃) (f : M₁ ->SL[σ₁₂] M₂) :
    (g₁ + g₂) ∘SL f = g₁ ∘SL f + g₂ ∘SL f := by
  ext
  simp

/--
theorem `comp_finsetSum` / 定理 `comp_finsetSum`

English:
theorem comp_finsetSum
  statement: {ι : Type*} {s : Finset ι}
  proof: by
  ext
  simp

@[deprecated (since := "2026-04-08")] alias comp_finset_sum := comp_finsetSum

中文:
定理 comp_finsetSum
  结论: {ι : 类型} {s : Finset ι}
  证明: by
  ext
  simp

@[deprecated (since := "2026-04-08")] alias comp_finset_sum := comp_finsetSum
-/
theorem comp_finsetSum {ι : Type*} {s : Finset ι}
    [ContinuousAdd M₂] [ContinuousAdd M₃] (g : M₂ ->SL[σ₂₃] M₃)
    (f : ι -> M₁ ->SL[σ₁₂] M₂) : g ∘SL (∑ i in s, f i) = ∑ i in s, g ∘SL (f i) := by
  ext
  simp

@[deprecated (since := "2026-04-08")] alias comp_finset_sum := comp_finsetSum

/--
theorem `finsetSum_comp` / 定理 `finsetSum_comp`

English:
theorem finsetSum_comp
  statement: {ι : Type*} {s : Finset ι}
  proof: by
  ext
  simp only [comp_apply, sum_apply]

@[deprecated (since := "2026-04-08")] alias finset_sum_comp := finsetSum_comp

中文:
定理 finsetSum_comp
  结论: {ι : 类型} {s : Finset ι}
  证明: by
  ext
  simp only [comp_apply, sum_apply]

@[deprecated (since := "2026-04-08")] alias finset_sum_comp := finsetSum_comp

Depends on / 依赖: comp_apply, sum_apply
-/
theorem finsetSum_comp {ι : Type*} {s : Finset ι}
    [ContinuousAdd M₃] (g : ι -> M₂ ->SL[σ₂₃] M₃)
    (f : M₁ ->SL[σ₁₂] M₂) : (∑ i in s, g i) ∘SL f = ∑ i in s, (g i) ∘SL f := by
  ext
  simp only [comp_apply, sum_apply]

@[deprecated (since := "2026-04-08")] alias finset_sum_comp := finsetSum_comp

/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  statement: {R₄ : Type*} [Semiring R₄] [Module R₄ M₄] {σ₁₄ : R₁ ->+* R₄} {σ₂₄ : R₂ ->+* R₄}
  proof: rfl

中文:
定理 comp_assoc
  结论: {R₄ : 类型} [Semiring R₄] [Module R₄ M₄] {σ₁₄ : R₁ ->+* R₄} {σ₂₄ : R₂ ->+* R₄}
  证明: rfl
-/
theorem comp_assoc {R₄ : Type*} [Semiring R₄] [Module R₄ M₄] {σ₁₄ : R₁ ->+* R₄} {σ₂₄ : R₂ ->+* R₄}
    {σ₃₄ : R₃ ->+* R₄} [RingHomCompTriple σ₁₃ σ₃₄ σ₁₄] [RingHomCompTriple σ₂₃ σ₃₄ σ₂₄]
    [RingHomCompTriple σ₁₂ σ₂₄ σ₁₄] (h : M₃ ->SL[σ₃₄] M₄) (g : M₂ ->SL[σ₂₃] M₃) (f : M₁ ->SL[σ₁₂] M₂) :
    (h ∘SL g) ∘SL f = h ∘SL (g ∘SL f) :=
  rfl

/--
theorem `cancel_left` / 定理 `cancel_left`

English:
theorem cancel_left
  statement: {g : M₂ ->SL[σ₂₃] M₃} {f₁ f₂ : M₁ ->SL[σ₁₂] M₂} (hg : Function.Injective g)
  proof: by
  ext x
  exact hg congr($h x)

中文:
定理 cancel_left
  结论: {g : M₂ ->SL[σ₂₃] M₃} {f₁ f₂ : M₁ ->SL[σ₁₂] M₂} (hg : Function.Injective g)
  证明: by
  ext x
  exact hg congr($h x)
-/
theorem cancel_left {g : M₂ ->SL[σ₂₃] M₃} {f₁ f₂ : M₁ ->SL[σ₁₂] M₂} (hg : Function.Injective g)
    (h : g ∘SL f₁ = g ∘SL f₂) : f₁ = f₂ := by
  ext x
  exact hg congr($h x)

/--
lemma `cancel_left'` / 引理 `cancel_left'`

English:
lemma cancel_left'
  given: {g : M₂ ->SL[σ₂₃] M₃} {f₁ f₂ : M₁ ->SL[σ₁₂] M₂} (hg : Function.Injective g)
  proof: ⟨cancel_left hg, congr_arg (fun f => g ∘SL f)⟩

中文:
引理 cancel_left'
  条件: {g : M₂ ->SL[σ₂₃] M₃} {f₁ f₂ : M₁ ->SL[σ₁₂] M₂} (hg : Function.Injective g)
  证明: ⟨cancel_left hg, congr_arg (fun f => g ∘SL f)⟩

Depends on / 依赖: cancel_left, congr_arg
-/
lemma cancel_left' {g : M₂ ->SL[σ₂₃] M₃} {f₁ f₂ : M₁ ->SL[σ₁₂] M₂} (hg : Function.Injective g) :
    g ∘SL f₁ = g ∘SL f₂ ↔ f₁ = f₂ :=
  ⟨cancel_left hg, congr_arg (fun f => g ∘SL f)⟩

/--
Instance `instMul` / 实例 `instMul`

English:
instance instMul
  signature: : Mul (M₁ ->L[R₁] M₁)
  body: ⟨comp⟩

中文:
实例 instMul
  签名: : Mul (M₁ ->L[R₁] M₁)
  定义体: ⟨comp⟩
-/
instance instMul : Mul (M₁ ->L[R₁] M₁) :=
  ⟨comp⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsMulApplyEqComp (M₁ ->L[R₁] M₁) M₁
  body: rfl

中文:
实例 :
  签名: IsMulApplyEqComp (M₁ ->L[R₁] M₁) M₁
  定义体: rfl
-/
instance : IsMulApplyEqComp (M₁ ->L[R₁] M₁) M₁ where
  mul_apply_eq_comp _ _ _ := rfl

/--
theorem `mul_def` / 定理 `mul_def`

English:
theorem mul_def
  given: (f g : M₁ ->L[R₁] M₁)
  statement: f * g = f ∘L g
  proof: rfl

@[simp, norm_cast]

中文:
定理 mul_def
  条件: (f g : M₁ ->L[R₁] M₁)
  结论: f * g = f ∘L g
  证明: rfl

@[simp, norm_cast]
-/
theorem mul_def (f g : M₁ ->L[R₁] M₁) : f * g = f ∘L g :=
  rfl

@[simp, norm_cast]
/--
theorem `toLinearMap_mul` / 定理 `toLinearMap_mul`

English:
theorem toLinearMap_mul
  given: (f g : M₁ ->L[R₁] M₁)
  statement: (↑(f * g) : M₁ ->ₗ[R₁] M₁) = f * g
  proof: rfl

@[deprecated (since := "2026-05-20")] alias coe_mul := toLinearMap_mul

@[deprecated (since := "2026-05-20")] protected alias coe_mul' := FunLike.coe_mul

@[deprecated (since := "2026-05-20")] protected alias mul_apply := mul_apply_eq_comp

中文:
定理 toLinearMap_mul
  条件: (f g : M₁ ->L[R₁] M₁)
  结论: (↑(f * g) : M₁ ->ₗ[R₁] M₁) = f * g
  证明: rfl

@[deprecated (since := "2026-05-20")] alias coe_mul := toLinearMap_mul

@[deprecated (since := "2026-05-20")] protected alias coe_mul' := FunLike.coe_mul

@[deprecated (since := "2026-05-20")] protected alias mul_apply := mul_apply_eq_comp
-/
theorem toLinearMap_mul (f g : M₁ ->L[R₁] M₁) : (↑(f * g) : M₁ ->ₗ[R₁] M₁) = f * g :=
  rfl

@[deprecated (since := "2026-05-20")] alias coe_mul := toLinearMap_mul

@[deprecated (since := "2026-05-20")] protected alias coe_mul' := FunLike.coe_mul

@[deprecated (since := "2026-05-20")] protected alias mul_apply := mul_apply_eq_comp

/--
Instance `monoidWithZero` / 实例 `monoidWithZero`

English:
instance monoidWithZero
  signature: : MonoidWithZero (M₁ ->L[R₁] M₁)
  body: fast_instance% FunLike.monoidWithZero

@[deprecated (since := "2026-07-23")] alias coe_pow' := FunLike.coe_pow_eq_iterate

@[simp, norm_cast]

中文:
实例 monoidWithZero
  签名: : MonoidWithZero (M₁ ->L[R₁] M₁)
  定义体: fast_instance% FunLike.monoidWithZero

@[deprecated (since := "2026-07-23")] alias coe_pow' := FunLike.coe_pow_eq_iterate

@[simp, norm_cast]

Depends on / 依赖: FunLike, FunLike.monoidWithZero, fast_instance, monoidWithZero
-/
instance monoidWithZero : MonoidWithZero (M₁ ->L[R₁] M₁) :=
  fast_instance% FunLike.monoidWithZero

@[deprecated (since := "2026-07-23")] alias coe_pow' := FunLike.coe_pow_eq_iterate

@[simp, norm_cast]
/--
theorem `toLinearMap_pow` / 定理 `toLinearMap_pow`

English:
theorem toLinearMap_pow
  given: (f : M₁ ->L[R₁] M₁) (n : Nat)
  statement: (↑(f ^ n) : M₁ ->ₗ[R₁] M₁) = f ^ n
  proof: DFunLike.ext' (FunLike.coe_pow_eq_iterate f n).trans
 .symm hom_coe_pow _ rfl (fun _ _ => rfl) _ _

@[deprecated (since := "2026-07-24")] protected alias coe_pow := toLinearMap_pow

中文:
定理 toLinearMap_pow
  条件: (f : M₁ ->L[R₁] M₁) (n : 自然数)
  结论: (↑(f ^ n) : M₁ ->ₗ[R₁] M₁) = f ^ n
  证明: DFunLike.ext' (FunLike.coe_pow_eq_iterate f n).trans
 .symm hom_coe_pow _ rfl (fun _ _ => rfl) _ _

@[deprecated (since := "2026-07-24")] protected alias coe_pow := toLinearMap_pow

Depends on / 依赖: DFunLike, DFunLike.ext, FunLike, FunLike.coe_pow_eq_iterate, coe_pow_eq_iterate, hom_coe_pow
-/
theorem toLinearMap_pow (f : M₁ ->L[R₁] M₁) (n : Nat) : (↑(f ^ n) : M₁ ->ₗ[R₁] M₁) = f ^ n :=
DFunLike.ext' (FunLike.coe_pow_eq_iterate f n).trans
 .symm hom_coe_pow _ rfl (fun _ _ => rfl) _ _

@[deprecated (since := "2026-07-24")] protected alias coe_pow := toLinearMap_pow

/--
Instance `instNatCast` / 实例 `instNatCast`

English:
instance instNatCast
  signature: [ContinuousAdd M₁]
  body: n • (1 : M₁ ->L[R₁] M₁)

中文:
实例 instNatCast
  签名: [ContinuousAdd M₁]
  定义体: n • (1 : M₁ ->L[R₁] M₁)
-/
instance instNatCast [ContinuousAdd M₁] : NatCast (M₁ ->L[R₁] M₁) where
  natCast n := n • (1 : M₁ ->L[R₁] M₁)

/--
Instance `instIsNatCastApply` / 实例 `instIsNatCastApply`

English:
instance instIsNatCastApply
  signature: [ContinuousAdd M₁]
  body: rfl

中文:
实例 instIsNatCastApply
  签名: [ContinuousAdd M₁]
  定义体: rfl
-/
instance instIsNatCastApply [ContinuousAdd M₁] : IsNatCastApply (M₁ ->L[R₁] M₁) M₁ where
  natCast_apply _ _ := rfl

/--
Instance `semiring` / 实例 `semiring`

English:
instance semiring
  signature: [ContinuousAdd M₁]
  body: fast_instance% FunLike.semiring

中文:
实例 semiring
  签名: [ContinuousAdd M₁]
  定义体: fast_instance% FunLike.semiring

Depends on / 依赖: FunLike, FunLike.semiring, fast_instance, semiring
-/
instance semiring [ContinuousAdd M₁] : Semiring (M₁ ->L[R₁] M₁) :=
  fast_instance% FunLike.semiring

/-- `ContinuousLinearMap.toLinearMap` as a `RingHom`. -/
@[simps]
/--
Definition of `toLinearMapRingHom` / `toLinearMapRingHom` 的定义

English:
definition toLinearMapRingHom
  signature: [ContinuousAdd M₁]
  body: toLinearMap
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

@[simp]

中文:
定义 toLinearMapRingHom
  签名: [ContinuousAdd M₁]
  定义体: toLinearMap
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

@[simp]

Depends on / 依赖: toLinearMap
-/
def toLinearMapRingHom [ContinuousAdd M₁] : (M₁ ->L[R₁] M₁) ->+* M₁ ->ₗ[R₁] M₁ where
  toFun := toLinearMap
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

@[simp]
/--
theorem `natCast_apply` / 定理 `natCast_apply`

English:
theorem natCast_apply
  given: [ContinuousAdd M₁] (n : Nat) (m : M₁)
  statement: (↑n : M₁ ->L[R₁] M₁) m = n • m
  proof: rfl

@[simp]

中文:
定理 natCast_apply
  条件: [ContinuousAdd M₁] (n : 自然数) (m : M₁)
  结论: (↑n : M₁ ->L[R₁] M₁) m = n • m
  证明: rfl

@[simp]
-/
theorem natCast_apply [ContinuousAdd M₁] (n : Nat) (m : M₁) : (↑n : M₁ ->L[R₁] M₁) m = n • m :=
  rfl

@[simp]
/--
theorem `ofNat_apply` / 定理 `ofNat_apply`

English:
theorem ofNat_apply
  given: [ContinuousAdd M₁] (n : Nat) [n.AtLeastTwo] (m : M₁)
  proof: rfl

中文:
定理 ofNat_apply
  条件: [ContinuousAdd M₁] (n : 自然数) [n.AtLeastTwo] (m : M₁)
  证明: rfl
-/
theorem ofNat_apply [ContinuousAdd M₁] (n : Nat) [n.AtLeastTwo] (m : M₁) :
    (ofNat(n) : M₁ ->L[R₁] M₁) m = OfNat.ofNat n • m :=
  rfl

/-- Construct a homeomorphism from an invertible continuous linear map. -/
@[simps]
/--
Definition of `homeomorphOfUnit` / `homeomorphOfUnit` 的定义

English:
definition homeomorphOfUnit
  signature: (T : (M₁ ->L[R₁] M₁)ˣ)
  body: T.1
  invFun := T⁻¹.1
  left_inv x := by rw [← mul_apply_eq_comp, Units.inv_mul, one_apply_eq_self]
  right_inv x := by rw [← mul_apply_eq_comp, Units.mul_inv, one_apply_eq_self]

中文:
定义 homeomorphOfUnit
  签名: (T : (M₁ ->L[R₁] M₁)ˣ)
  定义体: T.1
  invFun := T⁻¹.1
  left_inv x := by rw [← mul_apply_eq_comp, Units.inv_mul, one_apply_eq_self]
  right_inv x := by rw [← mul_apply_eq_comp, Units.mul_inv, one_apply_eq_self]
-/
def homeomorphOfUnit (T : (M₁ ->L[R₁] M₁)ˣ) : M₁ ≃ₜ M₁ where
  toFun := T.1
  invFun := T⁻¹.1
  left_inv x := by rw [← mul_apply_eq_comp, Units.inv_mul, one_apply_eq_self]
  right_inv x := by rw [← mul_apply_eq_comp, Units.mul_inv, one_apply_eq_self]

/--
theorem `isHomeomorph_of_isUnit` / 定理 `isHomeomorph_of_isUnit`

English:
theorem isHomeomorph_of_isUnit
  given: {T : M₁ ->L[R₁] M₁} (hT : IsUnit T)
  statement: IsHomeomorph T
  proof: by
  obtain ⟨T, rfl⟩ := hT
  exact (homeomorphOfUnit T).isHomeomorph

中文:
定理 isHomeomorph_of_isUnit
  条件: {T : M₁ ->L[R₁] M₁} (hT : IsUnit T)
  结论: IsHomeomorph T
  证明: by
  obtain ⟨T, rfl⟩ := hT
  exact (homeomorphOfUnit T).isHomeomorph

Depends on / 依赖: homeomorphOfUnit, isHomeomorph
-/
theorem isHomeomorph_of_isUnit {T : M₁ ->L[R₁] M₁} (hT : IsUnit T) : IsHomeomorph T := by
  obtain ⟨T, rfl⟩ := hT
  exact (homeomorphOfUnit T).isHomeomorph

section ApplyAction

variable [ContinuousAdd M₁]

/--
Instance `applyModule` / 实例 `applyModule`

English:
instance applyModule
  signature: : Module (M₁ ->L[R₁] M₁) M₁
  body: Module.compHom _ toLinearMapRingHom

@[simp]

中文:
实例 applyModule
  签名: : Module (M₁ ->L[R₁] M₁) M₁
  定义体: Module.compHom _ toLinearMapRingHom

@[simp]

Depends on / 依赖: Module, Module.compHom, compHom, toLinearMapRingHom
-/
instance applyModule : Module (M₁ ->L[R₁] M₁) M₁ :=
  Module.compHom _ toLinearMapRingHom

@[simp]
/--
theorem `smul_def` / 定理 `smul_def`

English:
theorem smul_def
  given: (f : M₁ ->L[R₁] M₁) (a : M₁)
  statement: f • a = f a
  proof: rfl

中文:
定理 smul_def
  条件: (f : M₁ ->L[R₁] M₁) (a : M₁)
  结论: f • a = f a
  证明: rfl
-/
protected theorem smul_def (f : M₁ ->L[R₁] M₁) (a : M₁) : f • a = f a :=
  rfl

/--
Instance `applyFaithfulSMul` / 实例 `applyFaithfulSMul`

English:
instance applyFaithfulSMul
  signature: : FaithfulSMul (M₁ ->L[R₁] M₁) M₁
  body: ⟨fun {_ _} => ContinuousLinearMap.ext⟩

中文:
实例 applyFaithfulSMul
  签名: : FaithfulSMul (M₁ ->L[R₁] M₁) M₁
  定义体: ⟨fun {_ _} => ContinuousLinearMap.ext⟩

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.ext
-/
instance applyFaithfulSMul : FaithfulSMul (M₁ ->L[R₁] M₁) M₁ :=
  ⟨fun {_ _} => ContinuousLinearMap.ext⟩

/--
Instance `applySMulCommClass` / 实例 `applySMulCommClass`

English:
instance applySMulCommClass
  signature: : SMulCommClass R₁ (M₁ ->L[R₁] M₁) M₁ where
  body: (e.map_smul r m).symm

中文:
实例 applySMulCommClass
  签名: : SMulCommClass R₁ (M₁ ->L[R₁] M₁) M₁ where
  定义体: (e.map_smul r m).symm

Depends on / 依赖: e.map_smul, map_smul
-/
instance applySMulCommClass : SMulCommClass R₁ (M₁ ->L[R₁] M₁) M₁ where
  smul_comm r e m := (e.map_smul r m).symm

/--
Instance `applySMulCommClass'` / 实例 `applySMulCommClass'`

English:
instance applySMulCommClass'
  signature: : SMulCommClass (M₁ ->L[R₁] M₁) R₁ M₁ where
  body: map_smul

中文:
实例 applySMulCommClass'
  签名: : SMulCommClass (M₁ ->L[R₁] M₁) R₁ M₁ where
  定义体: map_smul

Depends on / 依赖: map_smul
-/
instance applySMulCommClass' : SMulCommClass (M₁ ->L[R₁] M₁) R₁ M₁ where
  smul_comm := map_smul

/--
Instance `continuousConstSMul_apply` / 实例 `continuousConstSMul_apply`

English:
instance continuousConstSMul_apply
  signature: : ContinuousConstSMul (M₁ ->L[R₁] M₁) M₁
  body: ⟨ContinuousLinearMap.continuous⟩

中文:
实例 continuousConstSMul_apply
  签名: : ContinuousConstSMul (M₁ ->L[R₁] M₁) M₁
  定义体: ⟨ContinuousLinearMap.continuous⟩

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.continuous, continuous
-/
instance continuousConstSMul_apply : ContinuousConstSMul (M₁ ->L[R₁] M₁) M₁ :=
  ⟨ContinuousLinearMap.continuous⟩

end ApplyAction

/--
theorem `isClosed_ker` / 定理 `isClosed_ker`

English:
theorem isClosed_ker
  given: [T1Space M₂] (f : M₁ ->SL[σ₁₂] M₂)
  proof: isClosed_singleton.preimage f.continuous

中文:
定理 isClosed_ker
  条件: [T1Space M₂] (f : M₁ ->SL[σ₁₂] M₂)
  证明: isClosed_singleton.preimage f.continuous

Depends on / 依赖: continuous, f.continuous, isClosed_singleton, isClosed_singleton.preimage, preimage
-/
theorem isClosed_ker [T1Space M₂] (f : M₁ ->SL[σ₁₂] M₂) :
    IsClosed (f.ker : Set M₁) :=
  isClosed_singleton.preimage f.continuous

/--
theorem `isClosed_eqLocus` / 定理 `isClosed_eqLocus`

English:
theorem isClosed_eqLocus
  given: [T2Space M₂] (f g : M₁ ->SL[σ₁₂] M₂)
  proof: isClosed_eq f.continuous g.continuous

中文:
定理 isClosed_eqLocus
  条件: [T2Space M₂] (f g : M₁ ->SL[σ₁₂] M₂)
  证明: isClosed_eq f.continuous g.continuous

Depends on / 依赖: continuous, f.continuous, g.continuous, isClosed_eq
-/
theorem isClosed_eqLocus [T2Space M₂] (f g : M₁ ->SL[σ₁₂] M₂) :
    IsClosed (f.eqLocus g : Set M₁) :=
  isClosed_eq f.continuous g.continuous

/--
theorem `isComplete_ker` / 定理 `isComplete_ker`

English:
theorem isComplete_ker
  statement: {M' : Type*} [UniformSpace M'] [CompleteSpace M'] [AddCommMonoid M']
  proof: (isClosed_ker f).isComplete

中文:
定理 isComplete_ker
  结论: {M' : 类型} [UniformSpace M'] [CompleteSpace M'] [AddCommMonoid M']
  证明: (isClosed_ker f).isComplete

Depends on / 依赖: isClosed_ker, isComplete
-/
theorem isComplete_ker {M' : Type*} [UniformSpace M'] [CompleteSpace M'] [AddCommMonoid M']
    [Module R₁ M'] [T1Space M₂] (f : M' ->SL[σ₁₂] M₂) :
    IsComplete (f.ker : Set M') :=
  (isClosed_ker f).isComplete

/--
theorem `isComplete_eqLocus` / 定理 `isComplete_eqLocus`

English:
theorem isComplete_eqLocus
  statement: {M' : Type*} [UniformSpace M'] [CompleteSpace M'] [AddCommMonoid M']
  proof: (isClosed_eqLocus f g).isComplete

中文:
定理 isComplete_eqLocus
  结论: {M' : 类型} [UniformSpace M'] [CompleteSpace M'] [AddCommMonoid M']
  证明: (isClosed_eqLocus f g).isComplete

Depends on / 依赖: isClosed_eqLocus, isComplete
-/
theorem isComplete_eqLocus {M' : Type*} [UniformSpace M'] [CompleteSpace M'] [AddCommMonoid M']
    [Module R₁ M'] [T2Space M₂] (f g : M' ->SL[σ₁₂] M₂) :
    IsComplete (f.eqLocus g : Set M') :=
  (isClosed_eqLocus f g).isComplete

/--
Instance `completeSpace_ker` / 实例 `completeSpace_ker`

English:
instance completeSpace_ker
  signature: {M' : Type*} [UniformSpace M'] [CompleteSpace M']
  body: (isComplete_ker f).completeSpace_coe

中文:
实例 completeSpace_ker
  签名: {M' : 类型} [UniformSpace M'] [CompleteSpace M']
  定义体: (isComplete_ker f).completeSpace_coe

Depends on / 依赖: completeSpace_coe, isComplete_ker
-/
instance completeSpace_ker {M' : Type*} [UniformSpace M'] [CompleteSpace M']
    [AddCommMonoid M'] [Module R₁ M'] [T1Space M₂]
    (f : M' ->SL[σ₁₂] M₂) : CompleteSpace f.ker :=
  (isComplete_ker f).completeSpace_coe

/--
Instance `completeSpace_eqLocus` / 实例 `completeSpace_eqLocus`

English:
instance completeSpace_eqLocus
  signature: {M' : Type*} [UniformSpace M'] [CompleteSpace M']
  body: (isComplete_eqLocus f g).completeSpace_coe

中文:
实例 completeSpace_eqLocus
  签名: {M' : 类型} [UniformSpace M'] [CompleteSpace M']
  定义体: (isComplete_eqLocus f g).completeSpace_coe

Depends on / 依赖: completeSpace_coe, isComplete_eqLocus
-/
instance completeSpace_eqLocus {M' : Type*} [UniformSpace M'] [CompleteSpace M']
    [AddCommMonoid M'] [Module R₁ M'] [T2Space M₂]
    (f g : M' ->SL[σ₁₂] M₂) : CompleteSpace (f.toLinearMap.eqLocus g.toLinearMap) :=
  (isComplete_eqLocus f g).completeSpace_coe

section

variable {R S : Type*} [Semiring R] [Semiring S] [Module R M₁] [Module R M₂] [Module R S]
  [Module S M₂] [IsScalarTower R S M₂] [TopologicalSpace S] [ContinuousSMul S M₂]

/-- The linear map `fun x => c x • f`. Associates to a scalar-valued linear map and an element of
`M₂` the `M₂`-valued linear map obtained by multiplying the two (a.k.a. tensoring by `M₂`).
See also `ContinuousLinearMap.smulRightₗ` and `ContinuousLinearMap.smulRightL`. -/
@[simps coe]
/--
Definition of `smulRight` / `smulRight` 的定义

English:
definition smulRight
  signature: (c : M₁ ->L[R] S) (f : M₂)
  body: c.toLinearMap.smulRight f

@[simp]

中文:
定义 smulRight
  签名: (c : M₁ ->L[R] S) (f : M₂)
  定义体: c.toLinearMap.smulRight f

@[simp]

Depends on / 依赖: c.toLinearMap.smulRight, smulRight, toLinearMap
-/
def smulRight (c : M₁ ->L[R] S) (f : M₂) : M₁ ->L[R] M₂ where
  toLinearMap := c.toLinearMap.smulRight f

@[simp]
/--
theorem `smulRight_apply` / 定理 `smulRight_apply`

English:
theorem smulRight_apply
  given: {c : M₁ ->L[R] S} {f : M₂} {x : M₁}
  proof: rfl

@[simp]

中文:
定理 smulRight_apply
  条件: {c : M₁ ->L[R] S} {f : M₂} {x : M₁}
  证明: rfl

@[simp]
-/
theorem smulRight_apply {c : M₁ ->L[R] S} {f : M₂} {x : M₁} :
    (smulRight c f : M₁ -> M₂) x = c x • f :=
  rfl

@[simp]
/--
lemma `smulRight_zero` / 引理 `smulRight_zero`

English:
lemma smulRight_zero
  given: (f : M₁ ->L[R] S)
  statement: f.smulRight (0 : M₂) = 0
  proof: by ext; simp

@[simp]

中文:
引理 smulRight_zero
  条件: (f : M₁ ->L[R] S)
  结论: f.smulRight (0 : M₂) = 0
  证明: by ext; simp

@[simp]
-/
lemma smulRight_zero (f : M₁ ->L[R] S) : f.smulRight (0 : M₂) = 0 := by ext; simp

@[simp]
/--
theorem `zero_smulRight` / 定理 `zero_smulRight`

English:
theorem zero_smulRight
  given: {x : M₂}
  statement: (0 : M₁ ->L[R] S).smulRight x = 0
  proof: by ext; simp

中文:
定理 zero_smulRight
  条件: {x : M₂}
  结论: (0 : M₁ ->L[R] S).smulRight x = 0
  证明: by ext; simp
-/
theorem zero_smulRight {x : M₂} : (0 : M₁ ->L[R] S).smulRight x = 0 := by ext; simp

end

variable [Module R₁ M₂] [TopologicalSpace R₁] [ContinuousSMul R₁ M₂]

/--
theorem `smulRight_comp_smulRight` / 定理 `smulRight_comp_smulRight`

English:
theorem smulRight_comp_smulRight
  statement: {M₃ : Type*} [AddCommMonoid M₃] [Module R₁ M₃]
  proof: by
  ext
  simp

中文:
定理 smulRight_comp_smulRight
  结论: {M₃ : 类型} [AddCommMonoid M₃] [Module R₁ M₃]
  证明: by
  ext
  simp
-/
theorem smulRight_comp_smulRight {M₃ : Type*} [AddCommMonoid M₃] [Module R₁ M₃]
    [TopologicalSpace M₃] [ContinuousSMul R₁ M₃] (f : M₃ ->L[R₁] R₁) (g : M₁ ->L[R₁] R₁) {x : M₂}
    {y : M₃} : (smulRight f x) ∘L (smulRight g y) = smulRight g (f y • x) := by
  ext
  simp

/--
theorem `range_smulRight_apply` / 定理 `range_smulRight_apply`

English:
theorem range_smulRight_apply
  statement: {R : Type*} [DivisionSemiring R] [Module R M₁] [Module R M₂]
  proof: LinearMap.range_smulRight_apply (by simpa [coe_inj, ← toLinearMap_zero] using hf) x

中文:
定理 range_smulRight_apply
  结论: {R : 类型} [DivisionSemiring R] [Module R M₁] [Module R M₂]
  证明: LinearMap.range_smulRight_apply (by simpa [coe_inj, ← toLinearMap_zero] using hf) x

Depends on / 依赖: LinearMap, LinearMap.range_smulRight_apply, coe_inj, range_smulRight_apply, toLinearMap_zero
-/
theorem range_smulRight_apply {R : Type*} [DivisionSemiring R] [Module R M₁] [Module R M₂]
    [TopologicalSpace R] [ContinuousSMul R M₂] {f : M₁ ->L[R] R} (hf : f != 0) (x : M₂) :
    range (f.smulRight x : M₁ ->ₗ[R] M₂) = Submodule.span R {x} :=
  LinearMap.range_smulRight_apply (by simpa [coe_inj, ← toLinearMap_zero] using hf) x

section ToSpanSingleton

variable (R₁)
variable [ContinuousSMul R₁ M₁]

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `toSpanSingleton` / `toSpanSingleton` 的定义

English:
definition toSpanSingleton
  signature: (x : M₁)
  body: LinearMap.toSpanSingleton R₁ M₁ x

@[simp]

中文:
定义 toSpanSingleton
  签名: (x : M₁)
  定义体: LinearMap.toSpanSingleton R₁ M₁ x

@[simp]

Depends on / 依赖: LinearMap, LinearMap.toSpanSingleton, toSpanSingleton
-/
def toSpanSingleton (x : M₁) : R₁ ->L[R₁] M₁ where
  toLinearMap := LinearMap.toSpanSingleton R₁ M₁ x

@[simp]
/--
theorem `toSpanSingleton_apply` / 定理 `toSpanSingleton_apply`

English:
theorem toSpanSingleton_apply
  given: (x : M₁) (r : R₁)
  statement: toSpanSingleton R₁ x r = r • x
  proof: rfl

@[simp]

中文:
定理 toSpanSingleton_apply
  条件: (x : M₁) (r : R₁)
  结论: toSpanSingleton R₁ x r = r • x
  证明: rfl

@[simp]
-/
theorem toSpanSingleton_apply (x : M₁) (r : R₁) : toSpanSingleton R₁ x r = r • x :=
  rfl

@[simp]
/--
theorem `toSpanSingleton_zero` / 定理 `toSpanSingleton_zero`

English:
theorem toSpanSingleton_zero
  statement: toSpanSingleton R₁ (0 : M₁) = 0
  proof: by ext; simp

中文:
定理 toSpanSingleton_zero
  结论: toSpanSingleton R₁ (0 : M₁) = 0
  证明: by ext; simp
-/
theorem toSpanSingleton_zero : toSpanSingleton R₁ (0 : M₁) = 0 := by ext; simp

/--
theorem `toSpanSingleton_apply_one` / 定理 `toSpanSingleton_apply_one`

English:
theorem toSpanSingleton_apply_one
  given: (x : M₁)
  statement: toSpanSingleton R₁ x 1 = x
  proof: one_smul _ _

中文:
定理 toSpanSingleton_apply_one
  条件: (x : M₁)
  结论: toSpanSingleton R₁ x 1 = x
  证明: one_smul _ _

Depends on / 依赖: one_smul
-/
theorem toSpanSingleton_apply_one (x : M₁) : toSpanSingleton R₁ x 1 = x :=
  one_smul _ _

/--
theorem `toSpanSingleton_apply_map_one` / 定理 `toSpanSingleton_apply_map_one`

English:
theorem toSpanSingleton_apply_map_one
  given: (c : R₁ ->L[R₁] M₂)
  proof: by
  ext
  simp [← ContinuousLinearMap.map_smul_of_tower]

中文:
定理 toSpanSingleton_apply_map_one
  条件: (c : R₁ ->L[R₁] M₂)
  证明: by
  ext
  simp [← ContinuousLinearMap.map_smul_of_tower]
-/
@[simp] theorem toSpanSingleton_apply_map_one (c : R₁ ->L[R₁] M₂) :
    toSpanSingleton R₁ (c 1) = c := by
  ext
  simp [← ContinuousLinearMap.map_smul_of_tower]

/--
theorem `toSpanSingleton_add` / 定理 `toSpanSingleton_add`

English:
theorem toSpanSingleton_add
  given: [ContinuousAdd M₁] (x y : M₁)
  proof: coe_inj.mp LinearMap.toSpanSingleton_add _ _

中文:
定理 toSpanSingleton_add
  条件: [ContinuousAdd M₁] (x y : M₁)
  证明: coe_inj.mp LinearMap.toSpanSingleton_add _ _

Depends on / 依赖: LinearMap, LinearMap.toSpanSingleton_add, coe_inj, coe_inj.mp, toSpanSingleton_add
-/
theorem toSpanSingleton_add [ContinuousAdd M₁] (x y : M₁) :
    toSpanSingleton R₁ (x + y) = toSpanSingleton R₁ x + toSpanSingleton R₁ y :=
coe_inj.mp LinearMap.toSpanSingleton_add _ _

/--
theorem `toSpanSingleton_smul` / 定理 `toSpanSingleton_smul`

English:
theorem toSpanSingleton_smul
  statement: {α} [Monoid α] [DistribMulAction α M₁] [ContinuousConstSMul α M₁]
  proof: coe_inj.mp LinearMap.toSpanSingleton_smul _ _

中文:
定理 toSpanSingleton_smul
  结论: {α} [Monoid α] [DistribMulAction α M₁] [ContinuousConstSMul α M₁]
  证明: coe_inj.mp LinearMap.toSpanSingleton_smul _ _

Depends on / 依赖: LinearMap, LinearMap.toSpanSingleton_smul, coe_inj, coe_inj.mp, toSpanSingleton_smul
-/
theorem toSpanSingleton_smul {α} [Monoid α] [DistribMulAction α M₁] [ContinuousConstSMul α M₁]
    [SMulCommClass R₁ α M₁] (c : α) (x : M₁) :
    toSpanSingleton R₁ (c • x) = c • toSpanSingleton R₁ x :=
coe_inj.mp LinearMap.toSpanSingleton_smul _ _

/--
theorem `smulRight_id` / 定理 `smulRight_id`

English:
theorem smulRight_id
  statement: smulRight (.id R₁ R₁) = toSpanSingleton R₁ (M₁ := M₁)
  proof: rfl

中文:
定理 smulRight_id
  结论: smulRight (.id R₁ R₁) = toSpanSingleton R₁ (M₁ := M₁)
  证明: rfl
-/
theorem smulRight_id : smulRight (.id R₁ R₁) = toSpanSingleton R₁ (M₁ := M₁) := rfl

/--
theorem `smulRight_one_eq_toSpanSingleton` / 定理 `smulRight_one_eq_toSpanSingleton`

English:
theorem smulRight_one_eq_toSpanSingleton
  given: (x : M₁)
  proof: rfl

@[simp]

中文:
定理 smulRight_one_eq_toSpanSingleton
  条件: (x : M₁)
  证明: rfl

@[simp]
-/
theorem smulRight_one_eq_toSpanSingleton (x : M₁) :
    (1 : R₁ ->L[R₁] R₁).smulRight x = toSpanSingleton R₁ x :=
  rfl

@[simp]
/--
theorem `toLinearMap_toSpanSingleton` / 定理 `toLinearMap_toSpanSingleton`

English:
theorem toLinearMap_toSpanSingleton
  given: (x : M₁)
  proof: rfl

中文:
定理 toLinearMap_toSpanSingleton
  条件: (x : M₁)
  证明: rfl
-/
theorem toLinearMap_toSpanSingleton (x : M₁) :
    (toSpanSingleton R₁ x).toLinearMap = LinearMap.toSpanSingleton R₁ M₁ x := rfl

variable {R₁}

/--
theorem `comp_toSpanSingleton` / 定理 `comp_toSpanSingleton`

English:
theorem comp_toSpanSingleton
  given: (f : M₁ ->L[R₁] M₂) (x : M₁)
  proof: coe_inj.mp LinearMap.comp_toSpanSingleton _ _

omit [ContinuousSMul R₁ M₁] in

中文:
定理 comp_toSpanSingleton
  条件: (f : M₁ ->L[R₁] M₂) (x : M₁)
  证明: coe_inj.mp LinearMap.comp_toSpanSingleton _ _

omit [ContinuousSMul R₁ M₁] in

Depends on / 依赖: LinearMap, LinearMap.comp_toSpanSingleton, coe_inj, coe_inj.mp, comp_toSpanSingleton
-/
theorem comp_toSpanSingleton (f : M₁ ->L[R₁] M₂) (x : M₁) :
    f ∘L toSpanSingleton R₁ x = toSpanSingleton R₁ (f x) :=
coe_inj.mp LinearMap.comp_toSpanSingleton _ _

omit [ContinuousSMul R₁ M₁] in
/--
theorem `toSpanSingleton_comp` / 定理 `toSpanSingleton_comp`

English:
theorem toSpanSingleton_comp
  given: (f : M₁ ->L[R₁] R₁) (g : M₂)
  proof: rfl

中文:
定理 toSpanSingleton_comp
  条件: (f : M₁ ->L[R₁] R₁) (g : M₂)
  证明: rfl
-/
theorem toSpanSingleton_comp (f : M₁ ->L[R₁] R₁) (g : M₂) :
    toSpanSingleton R₁ g ∘L f = f.smulRight g := rfl

/--
theorem `toSpanSingleton_inj` / 定理 `toSpanSingleton_inj`

English:
theorem toSpanSingleton_inj
  given: {f f' : M₂}
  proof: by
  simp [ContinuousLinearMap.ext_ring_iff]

中文:
定理 toSpanSingleton_inj
  条件: {f f' : M₂}
  证明: by
  simp [ContinuousLinearMap.ext_ring_iff]
-/
@[simp] theorem toSpanSingleton_inj {f f' : M₂} :
    toSpanSingleton R₁ f = toSpanSingleton R₁ f' ↔ f = f' := by
  simp [ContinuousLinearMap.ext_ring_iff]

/--
theorem `toSpanSingleton_comp_toSpanSingleton` / 定理 `toSpanSingleton_comp_toSpanSingleton`

English:
theorem toSpanSingleton_comp_toSpanSingleton
  given: [ContinuousMul R₁] {x : M₂} {c : R₁}
  proof: smulRight_comp_smulRight 1 1

中文:
定理 toSpanSingleton_comp_toSpanSingleton
  条件: [ContinuousMul R₁] {x : M₂} {c : R₁}
  证明: smulRight_comp_smulRight 1 1

Depends on / 依赖: smulRight_comp_smulRight
-/
theorem toSpanSingleton_comp_toSpanSingleton [ContinuousMul R₁] {x : M₂} {c : R₁} :
    (toSpanSingleton R₁ x) ∘L (toSpanSingleton R₁ c) =
      toSpanSingleton R₁ (c • x) := smulRight_comp_smulRight 1 1

end ToSpanSingleton

end Semiring

section Ring

variable {R : Type*} [Ring R] {R₂ : Type*} [Ring R₂] {R₃ : Type*} [Ring R₃] {M : Type*}
  [TopologicalSpace M] [AddCommGroup M] {M₂ : Type*} [TopologicalSpace M₂] [AddCommGroup M₂]
  {M₃ : Type*} [TopologicalSpace M₃] [AddCommGroup M₃] {M₄ : Type*} [TopologicalSpace M₄]
  [AddCommGroup M₄] [Module R M] [Module R₂ M₂] [Module R₃ M₃] {σ₁₂ : R ->+* R₂} {σ₂₃ : R₂ ->+* R₃}
  {σ₁₃ : R ->+* R₃}

section

/--
theorem `map_neg` / 定理 `map_neg`

English:
theorem map_neg
  given: (f : M ->SL[σ₁₂] M₂) (x : M)
  statement: f (-x) = -f x
  proof: by
  exact map_neg f x

中文:
定理 map_neg
  条件: (f : M ->SL[σ₁₂] M₂) (x : M)
  结论: f (-x) = -f x
  证明: by
  exact map_neg f x
-/
protected theorem map_neg (f : M ->SL[σ₁₂] M₂) (x : M) : f (-x) = -f x := by
  exact map_neg f x

/--
theorem `map_sub` / 定理 `map_sub`

English:
theorem map_sub
  given: (f : M ->SL[σ₁₂] M₂) (x y : M)
  statement: f (x - y) = f x - f y
  proof: by
  exact map_sub f x y

@[simp]

中文:
定理 map_sub
  条件: (f : M ->SL[σ₁₂] M₂) (x y : M)
  结论: f (x - y) = f x - f y
  证明: by
  exact map_sub f x y

@[simp]
-/
protected theorem map_sub (f : M ->SL[σ₁₂] M₂) (x y : M) : f (x - y) = f x - f y := by
  exact map_sub f x y

@[simp]
/--
theorem `sub_apply'` / 定理 `sub_apply'`

English:
theorem sub_apply'
  given: (f g : M ->SL[σ₁₂] M₂) (x : M)
  statement: ((f : M ->ₛₗ[σ₁₂] M₂) - g) x = f x - g x
  proof: rfl

中文:
定理 sub_apply'
  条件: (f g : M ->SL[σ₁₂] M₂) (x : M)
  结论: ((f : M ->ₛₗ[σ₁₂] M₂) - g) x = f x - g x
  证明: rfl
-/
theorem sub_apply' (f g : M ->SL[σ₁₂] M₂) (x : M) : ((f : M ->ₛₗ[σ₁₂] M₂) - g) x = f x - g x :=
  rfl

end

section

variable [IsTopologicalAddGroup M₂]

/--
Instance `neg` / 实例 `neg`

English:
instance neg
  signature: : Neg (M ->SL[σ₁₂] M₂)
  body: ⟨fun f => ⟨-f, f.2.neg⟩⟩

中文:
实例 neg
  签名: : Neg (M ->SL[σ₁₂] M₂)
  定义体: ⟨fun f => ⟨-f, f.2.neg⟩⟩
-/
instance neg : Neg (M ->SL[σ₁₂] M₂) :=
  ⟨fun f => ⟨-f, f.2.neg⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsNegApply (M ->SL[σ₁₂] M₂) M M₂
  body: rfl

@[simp, norm_cast]

中文:
实例 :
  签名: IsNegApply (M ->SL[σ₁₂] M₂) M M₂
  定义体: rfl

@[simp, norm_cast]
-/
instance : IsNegApply (M ->SL[σ₁₂] M₂) M M₂ where
  neg_apply _ _ := rfl

@[simp, norm_cast]
/--
theorem `toLinearMap_neg` / 定理 `toLinearMap_neg`

English:
theorem toLinearMap_neg
  given: (f : M ->SL[σ₁₂] M₂)
  statement: (↑(-f) : M ->ₛₗ[σ₁₂] M₂) = -f
  proof: rfl

@[deprecated (since := "2026-05-20")] protected alias neg_apply := _root_.neg_apply

@[deprecated (since := "2026-05-20")] protected alias coe_neg := toLinearMap_neg

@[deprecated (since := "2026-05-20")] alias coe_neg' := FunLike.coe_neg

@[simp, norm_cast]

中文:
定理 toLinearMap_neg
  条件: (f : M ->SL[σ₁₂] M₂)
  结论: (↑(-f) : M ->ₛₗ[σ₁₂] M₂) = -f
  证明: rfl

@[deprecated (since := "2026-05-20")] protected alias neg_apply := _root_.neg_apply

@[deprecated (since := "2026-05-20")] protected alias coe_neg := toLinearMap_neg

@[deprecated (since := "2026-05-20")] alias coe_neg' := FunLike.coe_neg

@[simp, norm_cast]
-/
theorem toLinearMap_neg (f : M ->SL[σ₁₂] M₂) : (↑(-f) : M ->ₛₗ[σ₁₂] M₂) = -f :=
  rfl

@[deprecated (since := "2026-05-20")] protected alias neg_apply := _root_.neg_apply

@[deprecated (since := "2026-05-20")] protected alias coe_neg := toLinearMap_neg

@[deprecated (since := "2026-05-20")] alias coe_neg' := FunLike.coe_neg

@[simp, norm_cast]
/--
theorem `toContinuousAddMonoidHom_neg` / 定理 `toContinuousAddMonoidHom_neg`

English:
theorem toContinuousAddMonoidHom_neg
  given: (f : M ->SL[σ₁₂] M₂)
  proof: rfl

中文:
定理 toContinuousAddMonoidHom_neg
  条件: (f : M ->SL[σ₁₂] M₂)
  证明: rfl
-/
theorem toContinuousAddMonoidHom_neg (f : M ->SL[σ₁₂] M₂) :
    ↑(-f) = -(f : ContinuousAddMonoidHom M M₂) := rfl

/--
Instance `sub` / 实例 `sub`

English:
instance sub
  signature: : Sub (M ->SL[σ₁₂] M₂)
  body: ⟨fun f g => ⟨f - g, f.2.sub g.2⟩⟩

中文:
实例 sub
  签名: : Sub (M ->SL[σ₁₂] M₂)
  定义体: ⟨fun f g => ⟨f - g, f.2.sub g.2⟩⟩
-/
instance sub : Sub (M ->SL[σ₁₂] M₂) :=
  ⟨fun f g => ⟨f - g, f.2.sub g.2⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsSubApply (M ->SL[σ₁₂] M₂) M M₂
  body: rfl

中文:
实例 :
  签名: IsSubApply (M ->SL[σ₁₂] M₂) M M₂
  定义体: rfl
-/
instance : IsSubApply (M ->SL[σ₁₂] M₂) M M₂ where
  sub_apply _ _ _ := rfl

/--
Instance `addCommGroup` / 实例 `addCommGroup`

English:
instance addCommGroup
  signature: : AddCommGroup (M ->SL[σ₁₂] M₂)
  body: fast_instance% FunLike.addCommGroup

@[simp, norm_cast]

中文:
实例 addCommGroup
  签名: : AddCommGroup (M ->SL[σ₁₂] M₂)
  定义体: fast_instance% FunLike.addCommGroup

@[simp, norm_cast]

Depends on / 依赖: FunLike, FunLike.addCommGroup, addCommGroup, fast_instance
-/
instance addCommGroup : AddCommGroup (M ->SL[σ₁₂] M₂) := fast_instance% FunLike.addCommGroup

@[simp, norm_cast]
/--
theorem `toLinearMap_sub` / 定理 `toLinearMap_sub`

English:
theorem toLinearMap_sub
  given: (f g : M ->SL[σ₁₂] M₂)
  statement: (↑(f - g) : M ->ₛₗ[σ₁₂] M₂) = f - g
  proof: rfl

@[deprecated (since := "2026-05-20")] protected alias sub_apply := _root_.sub_apply

@[deprecated (since := "2026-05-20")] protected alias coe_sub := toLinearMap_sub

@[deprecated (since := "2026-05-20")] alias coe_sub' := FunLike.coe_sub

@[simp, norm_cast]

中文:
定理 toLinearMap_sub
  条件: (f g : M ->SL[σ₁₂] M₂)
  结论: (↑(f - g) : M ->ₛₗ[σ₁₂] M₂) = f - g
  证明: rfl

@[deprecated (since := "2026-05-20")] protected alias sub_apply := _root_.sub_apply

@[deprecated (since := "2026-05-20")] protected alias coe_sub := toLinearMap_sub

@[deprecated (since := "2026-05-20")] alias coe_sub' := FunLike.coe_sub

@[simp, norm_cast]
-/
theorem toLinearMap_sub (f g : M ->SL[σ₁₂] M₂) : (↑(f - g) : M ->ₛₗ[σ₁₂] M₂) = f - g :=
  rfl

@[deprecated (since := "2026-05-20")] protected alias sub_apply := _root_.sub_apply

@[deprecated (since := "2026-05-20")] protected alias coe_sub := toLinearMap_sub

@[deprecated (since := "2026-05-20")] alias coe_sub' := FunLike.coe_sub

@[simp, norm_cast]
/--
theorem `toContinuousAddMonoidHom_sub` / 定理 `toContinuousAddMonoidHom_sub`

English:
theorem toContinuousAddMonoidHom_sub
  given: (f g : M ->SL[σ₁₂] M₂)
  proof: rfl

中文:
定理 toContinuousAddMonoidHom_sub
  条件: (f g : M ->SL[σ₁₂] M₂)
  证明: rfl
-/
theorem toContinuousAddMonoidHom_sub (f g : M ->SL[σ₁₂] M₂) :
    ↑(f - g) = (f - g : ContinuousAddMonoidHom M M₂) := rfl

end

@[simp]
/--
theorem `comp_neg` / 定理 `comp_neg`

English:
theorem comp_neg
  statement: [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [IsTopologicalAddGroup M₂]
  proof: by
  ext x
  simp

@[simp]

中文:
定理 comp_neg
  结论: [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [IsTopologicalAddGroup M₂]
  证明: by
  ext x
  simp

@[simp]
-/
theorem comp_neg [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [IsTopologicalAddGroup M₂]
    [IsTopologicalAddGroup M₃] (g : M₂ ->SL[σ₂₃] M₃) (f : M ->SL[σ₁₂] M₂) :
    g ∘SL (-f) = -g ∘SL f := by
  ext x
  simp

@[simp]
/--
theorem `neg_comp` / 定理 `neg_comp`

English:
theorem neg_comp
  statement: [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [IsTopologicalAddGroup M₃] (g : M₂ ->SL[σ₂₃] M₃)
  proof: by
  ext
  simp

@[simp]

中文:
定理 neg_comp
  结论: [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [IsTopologicalAddGroup M₃] (g : M₂ ->SL[σ₂₃] M₃)
  证明: by
  ext
  simp

@[simp]
-/
theorem neg_comp [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [IsTopologicalAddGroup M₃] (g : M₂ ->SL[σ₂₃] M₃)
    (f : M ->SL[σ₁₂] M₂) : (-g) ∘SL f = -g ∘SL f := by
  ext
  simp

@[simp]
/--
theorem `comp_sub` / 定理 `comp_sub`

English:
theorem comp_sub
  statement: [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [IsTopologicalAddGroup M₂]
  proof: by
  ext
  simp

@[simp]

中文:
定理 comp_sub
  结论: [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [IsTopologicalAddGroup M₂]
  证明: by
  ext
  simp

@[simp]
-/
theorem comp_sub [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [IsTopologicalAddGroup M₂]
    [IsTopologicalAddGroup M₃] (g : M₂ ->SL[σ₂₃] M₃) (f₁ f₂ : M ->SL[σ₁₂] M₂) :
    g ∘SL (f₁ - f₂) = g ∘SL f₁ - g ∘SL f₂ := by
  ext
  simp

@[simp]
/--
theorem `sub_comp` / 定理 `sub_comp`

English:
theorem sub_comp
  statement: [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [IsTopologicalAddGroup M₃] (g₁ g₂ : M₂ ->SL[σ₂₃] M₃)
  proof: by
  ext
  simp

中文:
定理 sub_comp
  结论: [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [IsTopologicalAddGroup M₃] (g₁ g₂ : M₂ ->SL[σ₂₃] M₃)
  证明: by
  ext
  simp
-/
theorem sub_comp [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [IsTopologicalAddGroup M₃] (g₁ g₂ : M₂ ->SL[σ₂₃] M₃)
    (f : M ->SL[σ₁₂] M₂) : (g₁ - g₂) ∘SL f = g₁ ∘SL f - g₂ ∘SL f := by
  ext
  simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsTopologicalAddGroup
  signature: M] : IntCast (M ->L[R] M) where
  body: z • (1 : M ->L[R] M)

中文:
实例 [IsTopologicalAddGroup
  签名: M] : 整数Cast (M ->L[R] M) where
  定义体: z • (1 : M ->L[R] M)
-/
instance [IsTopologicalAddGroup M] : IntCast (M ->L[R] M) where
  intCast z := z • (1 : M ->L[R] M)

/--
Instance `instIsIntCastApply` / 实例 `instIsIntCastApply`

English:
instance instIsIntCastApply
  signature: [IsTopologicalAddGroup M]
  body: rfl

@[deprecated (since := "2026-05-20")] alias intCast_apply := _root_.intCast_apply

中文:
实例 instIsIntCastApply
  签名: [IsTopologicalAddGroup M]
  定义体: rfl

@[deprecated (since := "2026-05-20")] alias intCast_apply := _root_.intCast_apply
-/
instance instIsIntCastApply [IsTopologicalAddGroup M] : IsIntCastApply (M ->L[R] M) M where
  intCast_apply _ _ := rfl

@[deprecated (since := "2026-05-20")] alias intCast_apply := _root_.intCast_apply

/--
Instance `ring` / 实例 `ring`

English:
instance ring
  signature: [IsTopologicalAddGroup M]
  body: fast_instance% FunLike.ring

中文:
实例 ring
  签名: [IsTopologicalAddGroup M]
  定义体: fast_instance% FunLike.ring

Depends on / 依赖: FunLike, FunLike.ring, fast_instance
-/
instance ring [IsTopologicalAddGroup M] : Ring (M ->L[R] M) := fast_instance% FunLike.ring

/--
theorem `toSpanSingleton_pow` / 定理 `toSpanSingleton_pow`

English:
theorem toSpanSingleton_pow
  given: [TopologicalSpace R] [IsTopologicalRing R] (c : R) (n : Nat)
  proof: by
  induction n with
  | zero => ext; simp
  | succ n ihn =>
    rw [pow_succ]; rw [ihn]; rw [mul_def]; rw [toSpanSingleton_comp_toSpanSingleton]; rw [smul_eq_mul]; rw [pow_succ']

中文:
定理 toSpanSingleton_pow
  条件: [TopologicalSpace R] [IsTopologicalRing R] (c : R) (n : 自然数)
  证明: by
  induction n with
  | zero => ext; simp
  | succ n ihn =>
    rw [pow_succ]; rw [ihn]; rw [mul_def]; rw [toSpanSingleton_comp_toSpanSingleton]; rw [smul_eq_mul]; rw [pow_succ']

Depends on / 依赖: mul_def, pow_succ, smul_eq_mul, toSpanSingleton_comp_toSpanSingleton
-/
theorem toSpanSingleton_pow [TopologicalSpace R] [IsTopologicalRing R] (c : R) (n : Nat) :
    toSpanSingleton R c ^ n = toSpanSingleton R (c ^ n) := by
  induction n with
  | zero => ext; simp
  | succ n ihn =>
    rw [pow_succ]; rw [ihn]; rw [mul_def]; rw [toSpanSingleton_comp_toSpanSingleton]; rw [smul_eq_mul]; rw [pow_succ']

end Ring

section DivisionRing

variable {R M : Type*}

/--
theorem `isOpenMap_of_ne_zero` / 定理 `isOpenMap_of_ne_zero`

English:
theorem isOpenMap_of_ne_zero
  statement: [TopologicalSpace R] [DivisionRing R] [ContinuousSub R]
  proof: let ⟨x, hx⟩ := exists_ne_zero hf
  IsOpenMap.of_sections fun y =>
⟨fun a => y + (a - f y) • (f x)⁻¹ • x, Continuous.continuousAt by fun_prop, by simp,
      fun a => by simp [hx]⟩

中文:
定理 isOpenMap_of_ne_zero
  结论: [TopologicalSpace R] [DivisionRing R] [ContinuousSub R]
  证明: let ⟨x, hx⟩ := exists_ne_zero hf
  IsOpenMap.of_sections fun y =>
⟨fun a => y + (a - f y) • (f x)⁻¹ • x, Continuous.continuousAt by fun_prop, by simp,
      fun a => by simp [hx]⟩
-/
protected theorem isOpenMap_of_ne_zero [TopologicalSpace R] [DivisionRing R] [ContinuousSub R]
    [AddCommGroup M] [TopologicalSpace M] [ContinuousAdd M] [Module R M] [ContinuousSMul R M]
    (f : StrongDual R M) (hf : f != 0) : IsOpenMap f :=
  let ⟨x, hx⟩ := exists_ne_zero hf
  IsOpenMap.of_sections fun y =>
⟨fun a => y + (a - f y) • (f x)⁻¹ • x, Continuous.continuousAt by fun_prop, by simp,
      fun a => by simp [hx]⟩

end DivisionRing

section SMulMonoid

-- The M's are used for semilinear maps, and the N's for plain linear maps
variable {R R₂ R₃ S S₃ : Type*} [Semiring R] [Semiring R₂] [Semiring R₃] [Monoid S] [Monoid S₃]
  {M : Type*} [TopologicalSpace M] [AddCommMonoid M] [Module R M] {M₂ : Type*}
  [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R₂ M₂] {M₃ : Type*} [TopologicalSpace M₃]
  [AddCommMonoid M₃] [Module R₃ M₃] {N₂ : Type*} [TopologicalSpace N₂] [AddCommMonoid N₂]
  [Module R N₂] {N₃ : Type*} [TopologicalSpace N₃] [AddCommMonoid N₃] [Module R N₃]
  [DistribMulAction S₃ M₃] [SMulCommClass R₃ S₃ M₃] [ContinuousConstSMul S₃ M₃]
  [DistribMulAction S N₃] [SMulCommClass R S N₃] [ContinuousConstSMul S N₃] {σ₁₂ : R ->+* R₂}
  {σ₂₃ : R₂ ->+* R₃} {σ₁₃ : R ->+* R₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

@[simp]
/--
theorem `smul_comp` / 定理 `smul_comp`

English:
theorem smul_comp
  given: (c : S₃) (h : M₂ ->SL[σ₂₃] M₃) (f : M ->SL[σ₁₂] M₂)
  proof: rfl

中文:
定理 smul_comp
  条件: (c : S₃) (h : M₂ ->SL[σ₂₃] M₃) (f : M ->SL[σ₁₂] M₂)
  证明: rfl
-/
theorem smul_comp (c : S₃) (h : M₂ ->SL[σ₂₃] M₃) (f : M ->SL[σ₁₂] M₂) :
    (c • h) ∘SL f = c • h ∘SL f :=
  rfl

variable [DistribMulAction S₃ M₂] [ContinuousConstSMul S₃ M₂] [SMulCommClass R₂ S₃ M₂]
variable [DistribMulAction S N₂] [ContinuousConstSMul S N₂] [SMulCommClass R S N₂]

@[simp]
/--
theorem `comp_smul` / 定理 `comp_smul`

English:
theorem comp_smul
  statement: [LinearMap.CompatibleSMul N₂ N₃ S R] (hₗ : N₂ ->L[R] N₃) (c : S)
  proof: by
  ext x
  exact hₗ.map_smul_of_tower c (fₗ x)

@[simp]

中文:
定理 comp_smul
  结论: [LinearMap.CompatibleSMul N₂ N₃ S R] (hₗ : N₂ ->L[R] N₃) (c : S)
  证明: by
  ext x
  exact hₗ.map_smul_of_tower c (fₗ x)

@[simp]

Depends on / 依赖: map_smul_of_tower
-/
theorem comp_smul [LinearMap.CompatibleSMul N₂ N₃ S R] (hₗ : N₂ ->L[R] N₃) (c : S)
    (fₗ : M ->L[R] N₂) : hₗ ∘L (c • fₗ) = c • hₗ ∘L fₗ := by
  ext x
  exact hₗ.map_smul_of_tower c (fₗ x)

@[simp]
/--
theorem `comp_smulₛₗ` / 定理 `comp_smulₛₗ`

English:
theorem comp_smulₛₗ
  statement: [SMulCommClass R₂ R₂ M₂] [SMulCommClass R₃ R₃ M₃] [ContinuousConstSMul R₂ M₂]
  proof: by
  ext x
  simp

中文:
定理 comp_smulₛₗ
  结论: [SMulCommClass R₂ R₂ M₂] [SMulCommClass R₃ R₃ M₃] [ContinuousConstSMul R₂ M₂]
  证明: by
  ext x
  simp
-/
theorem comp_smulₛₗ [SMulCommClass R₂ R₂ M₂] [SMulCommClass R₃ R₃ M₃] [ContinuousConstSMul R₂ M₂]
    [ContinuousConstSMul R₃ M₃] (h : M₂ ->SL[σ₂₃] M₃) (c : R₂) (f : M ->SL[σ₁₂] M₂) :
    h ∘SL (c • f) = σ₂₃ c • h ∘SL f := by
  ext x
  simp

/--
Instance `distribMulAction` / 实例 `distribMulAction`

English:
instance distribMulAction
  signature: [ContinuousAdd M₂]
  body: fast_instance% FunLike.distribMulAction

中文:
实例 distribMulAction
  签名: [ContinuousAdd M₂]
  定义体: fast_instance% FunLike.distribMulAction

Depends on / 依赖: FunLike, FunLike.distribMulAction, distribMulAction, fast_instance
-/
instance distribMulAction [ContinuousAdd M₂] : DistribMulAction S₃ (M ->SL[σ₁₂] M₂) :=
  fast_instance% FunLike.distribMulAction

end SMulMonoid

section SMul

-- The M's are used for semilinear maps, and the N's for plain linear maps
variable {R R₂ R₃ S S₃ : Type*} [Semiring R] [Semiring R₂] [Semiring R₃] [Semiring S] [Semiring S₃]
  {M : Type*} [TopologicalSpace M] [AddCommMonoid M] [Module R M] {M₂ : Type*}
  [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R₂ M₂] {M₃ : Type*} [TopologicalSpace M₃]
  [AddCommMonoid M₃] [Module R₃ M₃] {N₂ : Type*} [TopologicalSpace N₂] [AddCommMonoid N₂]
  [Module R N₂] {N₃ : Type*} [TopologicalSpace N₃] [AddCommMonoid N₃] [Module R N₃] [Module S₃ M₃]
  [SMulCommClass R₃ S₃ M₃] [ContinuousConstSMul S₃ M₃] [Module S N₂] [ContinuousConstSMul S N₂]
  [SMulCommClass R S N₂] [Module S N₃] [SMulCommClass R S N₃] [ContinuousConstSMul S N₃]
  {σ₁₂ : R ->+* R₂} {σ₂₃ : R₂ ->+* R₃} {σ₁₃ : R ->+* R₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] (c : S)
  (h : M₂ ->SL[σ₂₃] M₃) (f : M ->SL[σ₁₂] M₂)

variable [ContinuousAdd M₂] [ContinuousAdd M₃] [ContinuousAdd N₂]

/--
Instance `module` / 实例 `module`

English:
instance module
  signature: : Module S₃ (M ->SL[σ₁₃] M₃)
  body: fast_instance% FunLike.module

中文:
实例 module
  签名: : Module S₃ (M ->SL[σ₁₃] M₃)
  定义体: fast_instance% FunLike.module

Depends on / 依赖: FunLike, FunLike.module, fast_instance, module
-/
instance module : Module S₃ (M ->SL[σ₁₃] M₃) := fast_instance% FunLike.module

/--
Instance `isCentralScalar` / 实例 `isCentralScalar`

English:
instance isCentralScalar
  signature: [Module S₃ᵐᵒᵖ M₃] [IsCentralScalar S₃ M₃]
  body: FunLike.isCentralScalar

中文:
实例 isCentralScalar
  签名: [Module S₃ᵐᵒᵖ M₃] [IsCentralScalar S₃ M₃]
  定义体: FunLike.isCentralScalar

Depends on / 依赖: FunLike, FunLike.isCentralScalar, isCentralScalar
-/
instance isCentralScalar [Module S₃ᵐᵒᵖ M₃] [IsCentralScalar S₃ M₃] :
    IsCentralScalar S₃ (M ->SL[σ₁₃] M₃) := FunLike.isCentralScalar

variable (S) [ContinuousAdd N₃]

/-- The coercion from `M →L[R] M₂` to `M →ₗ[R] M₂`, as a linear map. -/
@[simps]
/--
Definition of `coeLM` / `coeLM` 的定义

English:
definition coeLM
  signature: : (M ->L[R] N₃) ->ₗ[S] M ->ₗ[R] N₃ where
  body: (↑)
  map_add' f g := toLinearMap_add f g
  map_smul' c f := toLinearMap_smul c f

中文:
定义 coeLM
  签名: : (M ->L[R] N₃) ->ₗ[S] M ->ₗ[R] N₃ where
  定义体: (↑)
  map_add' f g := toLinearMap_add f g
  map_smul' c f := toLinearMap_smul c f
-/
def coeLM : (M ->L[R] N₃) ->ₗ[S] M ->ₗ[R] N₃ where
  toFun := (↑)
  map_add' f g := toLinearMap_add f g
  map_smul' c f := toLinearMap_smul c f

variable {S} (σ₁₃)

/-- The coercion from `M →SL[σ] M₂` to `M →ₛₗ[σ] M₂`, as a linear map. -/
@[simps]
/--
Definition of `coeLMₛₗ` / `coeLMₛₗ` 的定义

English:
definition coeLMₛₗ
  signature: : (M ->SL[σ₁₃] M₃) ->ₗ[S₃] M ->ₛₗ[σ₁₃] M₃ where
  body: (↑)
  map_add' f g := toLinearMap_add f g
  map_smul' c f := toLinearMap_smul c f

中文:
定义 coeLMₛₗ
  签名: : (M ->SL[σ₁₃] M₃) ->ₗ[S₃] M ->ₛₗ[σ₁₃] M₃ where
  定义体: (↑)
  map_add' f g := toLinearMap_add f g
  map_smul' c f := toLinearMap_smul c f
-/
def coeLMₛₗ : (M ->SL[σ₁₃] M₃) ->ₗ[S₃] M ->ₛₗ[σ₁₃] M₃ where
  toFun := (↑)
  map_add' f g := toLinearMap_add f g
  map_smul' c f := toLinearMap_smul c f

end SMul

section lcomp

variable {R U V : Type*} (W : Type*) [CommSemiring R]
    [AddCommMonoid U] [Module R U] [TopologicalSpace U]
    [AddCommMonoid V] [Module R V] [TopologicalSpace V]
    [AddCommMonoid W] [Module R W] [TopologicalSpace W]
    [ContinuousAdd W] [ContinuousConstSMul R W]

/-- Composition of continuous linear maps, as a linear map. Compare `LinearMap.lcomp`. -/
@[simps]
/--
Definition of `lcomp` / `lcomp` 的定义

English:
definition lcomp
  signature: (f : U ->L[R] V)
  body: l ∘L f
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

中文:
定义 lcomp
  签名: (f : U ->L[R] V)
  定义体: l ∘L f
  map_add' _ _ := by simp
  map_smul' _ _ := by simp
-/
def lcomp (f : U ->L[R] V) : (V ->L[R] W) ->ₗ[R] (U ->L[R] W) where
  toFun l := l ∘L f
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

end lcomp

section llcomp

variable (R U V W : Type*) [CommSemiring R]
  [AddCommMonoid U] [Module R U] [TopologicalSpace U]
  [AddCommMonoid V] [Module R V] [TopologicalSpace V]
  [ContinuousAdd V] [ContinuousConstSMul R V]
  [AddCommMonoid W] [Module R W] [TopologicalSpace W]
  [ContinuousAdd W] [ContinuousConstSMul R W]

/-- Composition of continuous linear maps, as a bilinear map. Compare `LinearMap.llcomp`. -/
@[simps]
/--
Definition of `llcomp` / `llcomp` 的定义

English:
definition llcomp
  signature: : (U ->L[R] V) ->ₗ[R] (V ->L[R] W) ->ₗ[R] (U ->L[R] W) where
  body: l.lcomp W
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

中文:
定义 llcomp
  签名: : (U ->L[R] V) ->ₗ[R] (V ->L[R] W) ->ₗ[R] (U ->L[R] W) where
  定义体: l.lcomp W
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

Depends on / 依赖: l.lcomp
-/
def llcomp : (U ->L[R] V) ->ₗ[R] (V ->L[R] W) ->ₗ[R] (U ->L[R] W) where
  toFun l := l.lcomp W
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

end llcomp

section toSpanSingletonLE

variable (R S M : Type*) [Semiring R] [Semiring S] [AddCommMonoid M] [Module R M] [Module S M]
  [SMulCommClass R S M] [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul S M]
  [TopologicalSpace R] [ContinuousSMul R M]

/-- `ContinuousLinearMap.toSpanSingleton` as a linear equivalence. See
`ContinuousLinearMap.toSpanSingletonLIE` for the isometric version
and `ContinuousLinearMap.toSpanSingletonCLE` for the continuous version. -/
@[simps -fullyApplied]
/--
Definition of `toSpanSingletonLE` / `toSpanSingletonLE` 的定义

English:
definition toSpanSingletonLE
  signature: : M ≃ₗ[S] (R ->L[R] M) where
  body: toSpanSingleton R
  invFun f := f 1
  map_add' := toSpanSingleton_add R
  map_smul' := toSpanSingleton_smul R
  left_inv x := by simp
  right_inv f := by ext; simp

中文:
定义 toSpanSingletonLE
  签名: : M ≃ₗ[S] (R ->L[R] M) where
  定义体: toSpanSingleton R
  invFun f := f 1
  map_add' := toSpanSingleton_add R
  map_smul' := toSpanSingleton_smul R
  left_inv x := by simp
  right_inv f := by ext; simp

Depends on / 依赖: toSpanSingleton
-/
def toSpanSingletonLE : M ≃ₗ[S] (R ->L[R] M) where
  toFun := toSpanSingleton R
  invFun f := f 1
  map_add' := toSpanSingleton_add R
  map_smul' := toSpanSingleton_smul R
  left_inv x := by simp
  right_inv f := by ext; simp

end toSpanSingletonLE

section SMulRightₗ

variable {R S T M M₂ : Type*} [Semiring R] [Semiring S] [Semiring T] [Module R S]
  [AddCommMonoid M₂] [Module R M₂] [Module S M₂] [IsScalarTower R S M₂] [TopologicalSpace S]
  [TopologicalSpace M₂] [ContinuousSMul S M₂] [TopologicalSpace M] [AddCommMonoid M] [Module R M]
  [ContinuousAdd M₂] [Module T M₂] [ContinuousConstSMul T M₂] [SMulCommClass R T M₂]
  [SMulCommClass S T M₂]

/--
Definition of `smulRightₗ` / `smulRightₗ` 的定义

English:
definition smulRightₗ
  signature: (c : M ->L[R] S)
  body: c.smulRight
  map_add' x y := by
    ext e
    apply smul_add (c e)
  map_smul' a x := by
    ext e
    dsimp
    apply smul_comm

@[simp]

中文:
定义 smulRightₗ
  签名: (c : M ->L[R] S)
  定义体: c.smulRight
  map_add' x y := by
    ext e
    apply smul_add (c e)
  map_smul' a x := by
    ext e
    dsimp
    apply smul_comm

@[simp]

Depends on / 依赖: c.smulRight, smulRight
-/
def smulRightₗ (c : M ->L[R] S) : M₂ ->ₗ[T] M ->L[R] M₂ where
  toFun := c.smulRight
  map_add' x y := by
    ext e
    apply smul_add (c e)
  map_smul' a x := by
    ext e
    dsimp
    apply smul_comm

@[simp]
/--
theorem `coe_smulRightₗ` / 定理 `coe_smulRightₗ`

English:
theorem coe_smulRightₗ
  given: (c : M ->L[R] S)
  statement: ⇑(smulRightₗ c : M₂ ->ₗ[T] M ->L[R] M₂) = c.smulRight
  proof: rfl

中文:
定理 coe_smulRightₗ
  条件: (c : M ->L[R] S)
  结论: ⇑(smulRightₗ c : M₂ ->ₗ[T] M ->L[R] M₂) = c.smulRight
  证明: rfl
-/
theorem coe_smulRightₗ (c : M ->L[R] S) : ⇑(smulRightₗ c : M₂ ->ₗ[T] M ->L[R] M₂) = c.smulRight :=
  rfl

end SMulRightₗ

section Semiring
variable {R S M : Type*} [Semiring R] [TopologicalSpace M] [AddCommGroup M] [Module R M]
  [CommSemiring S] [Module S M] [SMulCommClass R S M] [SMul S R] [IsScalarTower S R M]
  [ContinuousConstSMul S M] [IsTopologicalAddGroup M]

/--
Instance `algebra` / 实例 `algebra`

English:
instance algebra
  signature: : Algebra S (M ->L[R] M)
  body: Algebra.ofModule smul_comp fun _ _ _ => comp_smul _ _ _

中文:
实例 algebra
  签名: : Algebra S (M ->L[R] M)
  定义体: Algebra.ofModule smul_comp fun _ _ _ => comp_smul _ _ _

Depends on / 依赖: Algebra, Algebra.ofModule, comp_smul, ofModule, smul_comp
-/
instance algebra : Algebra S (M ->L[R] M) :=
  Algebra.ofModule smul_comp fun _ _ _ => comp_smul _ _ _

/--
theorem `algebraMap_apply` / 定理 `algebraMap_apply`

English:
theorem algebraMap_apply
  given: (r : S) (m : M)
  statement: algebraMap S (M ->L[R] M) r m = r • m
  proof: rfl

中文:
定理 algebraMap_apply
  条件: (r : S) (m : M)
  结论: algebraMap S (M ->L[R] M) r m = r • m
  证明: rfl
-/
@[simp] theorem algebraMap_apply (r : S) (m : M) : algebraMap S (M ->L[R] M) r m = r • m := rfl

end Semiring

end ContinuousLinearMap

section topDualPairing

variable {𝕜 E : Type*} [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜] [AddCommMonoid E]
  [Module 𝕜 E] [TopologicalSpace E] [ContinuousConstSMul 𝕜 𝕜]

variable (𝕜 E) in
/--
Definition of `topDualPairing` / `topDualPairing` 的定义

English:
definition topDualPairing
  signature: : (E ->L[𝕜] 𝕜) ->ₗ[𝕜] E ->ₗ[𝕜] 𝕜
  body: ContinuousLinearMap.coeLM 𝕜

@[simp]

中文:
定义 topDualPairing
  签名: : (E ->L[𝕜] 𝕜) ->ₗ[𝕜] E ->ₗ[𝕜] 𝕜
  定义体: ContinuousLinearMap.coeLM 𝕜

@[simp]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.coeLM
-/
def topDualPairing : (E ->L[𝕜] 𝕜) ->ₗ[𝕜] E ->ₗ[𝕜] 𝕜 :=
  ContinuousLinearMap.coeLM 𝕜

@[simp]
/--
theorem `topDualPairing_apply` / 定理 `topDualPairing_apply`

English:
theorem topDualPairing_apply
  statement: (v : E ->L[𝕜] 𝕜)
  proof: rfl

中文:
定理 topDualPairing_apply
  结论: (v : E ->L[𝕜] 𝕜)
  证明: rfl
-/
theorem topDualPairing_apply (v : E ->L[𝕜] 𝕜)
    (x : E) : topDualPairing 𝕜 E v x = v x :=
  rfl

end topDualPairing
