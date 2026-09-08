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

/-- Continuous linear maps between modules. We only put the type classes that are necessary for the
definition, although in applications `M` and `M₂` will be topological modules over the topological
ring `R`. -/
/-
**ContinuousLinearMap** 是 Mathlib 中的一个结构，位于命名空间 ``。
形式化陈述：ContinuousLinearMap {R : Type*} {S : Type*} [Semiring R] [Semiring S] (σ :
 R ->+* S) (M : Type*) [TopologicalSpace M] [AddCommMonoid M] (M₂ : Type*) [Topo
logicalSpace M₂] [AddCommMonoid M₂] [Module R M] [Module S M₂] extends M ->ₛₗ[σ]
 M₂ where cont : Continuous toFun
参数：σ : R ->+* S；M : Type*；M₂ : Type*。
继承自：M ->ₛₗ[σ] M₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Continuous linear maps between modules. We only put the type classes that are ne
cessary for the
definition, although in applications `M` and `M₂` will be topological modules ov
er the topological
ring `R`.
-/
structure ContinuousLinearMap {R : Type*} {S : Type*} [Semiring R] [Semiring S] (σ : R →+* S)
    (M : Type*) [TopologicalSpace M] [AddCommMonoid M] (M₂ : Type*) [TopologicalSpace M₂]
    [AddCommMonoid M₂] [Module R M] [Module S M₂] extends M →ₛₗ[σ] M₂ where
  cont : Continuous toFun := by
    first | fun_prop | eta_expand; dsimp; fun_prop | skip

attribute [inherit_doc ContinuousLinearMap] ContinuousLinearMap.cont

@[inherit_doc]
notation:25 M " →SL[" σ "] " M₂ => ContinuousLinearMap σ M M₂

@[inherit_doc]
notation:25 M " →L[" R "] " M₂ => ContinuousLinearMap (RingHom.id R) M M₂

/-- `ContinuousSemilinearMapClass F σ M M₂` asserts `F` is a type of bundled continuous
`σ`-semilinear maps `M → M₂`.  See also `ContinuousLinearMapClass F R M M₂` for the case where
`σ` is the identity map on `R`.  A map `f` between an `R`-module and an `S`-module over a ring
homomorphism `σ : R →+* S` is semilinear if it satisfies the two properties `f (x + y) = f x + f y`
and `f (c • x) = (σ c) • f x`. -/
/-
**ContinuousSemilinearMapClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_1) →   {R : outParam (Type u_2)} →     {S : outParam (Type u_3
)} →       [inst : Semiring R] →         [inst_1 : Semiring S] →           outPa
ram (R →+* S) →             (M : outParam (Type u_4)) →               [Topologic
alSpace M] →                 [inst_3 : AddCommMonoid M] →                   (M₂ 
: outParam (Type u_5)) →                     [TopologicalSpace M₂] →            
           [inst_5 : AddCommMonoid M₂] → [_root_.Module R M] → [_root_.Module S 
M₂] → [FunLike F M M₂] → Prop
参数：Type u_4；Type u_5。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ContinuousSemilinearMapClass F σ M M₂` asserts `F` is a type of bundled continu
ous
`σ`-semilinear maps `M → M₂`.  See also `ContinuousLinearMapClass F R M M₂` for 
the case where
`σ` is the identity map on `R`.  A map `f` between an `R`-module and an `S`-modu
le over a ring
homomorphism `σ : R →+* S` is semilinear if it satisfies the two properties `f (
x + y) = f x + f y`
and `f (c • x) = (σ c) • f x`.
-/
class ContinuousSemilinearMapClass (F : Type*) {R S : outParam Type*} [Semiring R] [Semiring S]
    (σ : outParam <| R →+* S) (M : outParam Type*) [TopologicalSpace M] [AddCommMonoid M]
    (M₂ : outParam Type*) [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M]
    [Module S M₂] [FunLike F M M₂] : Prop
    extends SemilinearMapClass F σ M M₂, ContinuousMapClass F M M₂

/-- `ContinuousLinearMapClass F R M M₂` asserts `F` is a type of bundled continuous
`R`-linear maps `M → M₂`.  This is an abbreviation for
`ContinuousSemilinearMapClass F (RingHom.id R) M M₂`. -/
/-
**ContinuousLinearMapClass** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：ContinuousLinearMapClass (F : Type*) (R : outParam Type*) [Semiring R] (M 
: outParam Type*) [TopologicalSpace M] [AddCommMonoid M] (M₂ : outParam Type*) [
TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M] [Module R M₂] [FunLike F M 
M₂]
参数：F : Type*；R : outParam Type*；M : outParam Type*；M₂ : outParam Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ContinuousLinearMapClass F R M M₂` asserts `F` is a type of bundled continuous
`R`-linear maps `M → M₂`.  This is an abbreviation for
`ContinuousSemilinearMapClass F (RingHom.id R) M M₂`.
-/
abbrev ContinuousLinearMapClass (F : Type*) (R : outParam Type*) [Semiring R]
    (M : outParam Type*) [TopologicalSpace M] [AddCommMonoid M] (M₂ : outParam Type*)
    [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M] [Module R M₂] [FunLike F M M₂] :=
  ContinuousSemilinearMapClass F (RingHom.id R) M M₂

/-- The *strong dual* of a topological vector space `M` over a ring `R`. This is the space of
continuous linear functionals and is equipped with the topology of uniform convergence
on bounded subsets. `StrongDual R M` is an abbreviation for `M →L[R] R`. -/
/-
**StrongDual** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：StrongDual (R : Type*) [Semiring R] [TopologicalSpace R] (M : Type*) [Topo
logicalSpace M] [AddCommMonoid M] [Module R M] : Type _
参数：R : Type*；M : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The *strong dual* of a topological vector space `M` over a ring `R`. This is the
 space of
continuous linear functionals and is equipped with the topology of uniform conve
rgence
on bounded subsets. `StrongDual R M` is an abbreviation for `M →L[R] R`.
-/
abbrev StrongDual (R : Type*) [Semiring R] [TopologicalSpace R]
  (M : Type*) [TopologicalSpace M] [AddCommMonoid M] [Module R M] : Type _ := M →L[R] R

namespace ContinuousLinearMap

section Semiring

/-!
### Properties that hold for non-necessarily commutative semirings.
-/

variable {R₁ : Type*} {R₂ : Type*} {R₃ : Type*} [Semiring R₁] [Semiring R₂] [Semiring R₃]
  {σ₁₂ : R₁ →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R₁ →+* R₃} {M₁ : Type*} [TopologicalSpace M₁]
  [AddCommMonoid M₁] {M'₁ : Type*} [TopologicalSpace M'₁] [AddCommMonoid M'₁] {M₂ : Type*}
  [TopologicalSpace M₂] [AddCommMonoid M₂] {M₃ : Type*} [TopologicalSpace M₃] [AddCommMonoid M₃]
  {M₄ : Type*} [TopologicalSpace M₄] [AddCommMonoid M₄] [Module R₁ M₁] [Module R₁ M'₁]
  [Module R₂ M₂] [Module R₃ M₃]

attribute [coe] ContinuousLinearMap.toLinearMap
/-- Coerce continuous linear maps to linear maps. -/
/-
**ContinuousLinearMap.LinearMap.coe** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearM
ap.LinearMap`。
形式化陈述：{R₁ : Type u_1} →   {R₂ : Type u_2} →     [inst : Semiring R₁] →       [in
st_1 : Semiring R₂] →         {σ₁₂ : R₁ →+* R₂} →           {M₁ : Type u_4} →   
          [inst_2 : TopologicalSpace M₁] →               [inst_3 : AddCommMonoid
 M₁] →                 {M₂ : Type u_6} →                   [inst_4 : Topological
Space M₂] →                     [inst_5 : AddCommMonoid M₂] →                   
    [inst_6 : _root_.Module R₁ M₁] →                         [inst_7 : _root_.Mo
dule R₂ M₂] → Coe (M₁ →SL[σ₁₂] M₂) (M₁ →ₛₗ[σ₁₂] M₂)
参数：M₁ →SL[σ₁₂] M₂；M₁ →ₛₗ[σ₁₂] M₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coerce continuous linear maps to linear maps.
-/
instance LinearMap.coe : Coe (M₁ →SL[σ₁₂] M₂) (M₁ →ₛₗ[σ₁₂] M₂) := ⟨toLinearMap⟩
/-
**ContinuousLinearMap.coe_injective** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearM
ap`。
形式化陈述：coe_injective : Function.Injective ((↑) : (M₁ ->SL[σ₁₂] M₂) -> M₁ ->ₛₗ[σ₁₂
] M₂)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem coe_injective : Function.Injective ((↑) : (M₁ →SL[σ₁₂] M₂) → M₁ →ₛₗ[σ₁₂] M₂) := by
  intro f g H
  cases f
  cases g
  congr
/-
**ContinuousLinearMap.funLike** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLinearMap`。
形式化陈述：funLike : FunLike (M₁ ->SL[σ₁₂] M₂) M₁ M₂ where coe f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance funLike : FunLike (M₁ →SL[σ₁₂] M₂) M₁ M₂ where
  coe f := f.toLinearMap
  coe_injective _ _ h := coe_injective (DFunLike.coe_injective h)
/-
**ContinuousLinearMap.continuousSemilinearMapClass** 是 Mathlib 中的一个实例，位于命名空间 `Co
ntinuousLinearMap`。
形式化陈述：continuousSemilinearMapClass : ContinuousSemilinearMapClass (M₁ ->SL[σ₁₂] 
M₂) σ₁₂ M₁ M₂ where map_add f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `LinearMap.map_smul'`：∀ {R : Type u_14} {S : Type u_15} [inst : Semiring 
R] [inst_1 : Semiring S] {σ : R →+* S} {M : Type u_16}   {M₂ : Type u_17} [inst_
2 : AddCo…
· 使用定理 `ContinuousLinearMap.cont`：∀ {R : Type u_1} {S : Type u_2} [inst : Semiri
ng R] [inst_1 : Semiring S] {σ : R →+* S} {M : Type u_3}   [inst_2 : Topological
Space M] [inst…
-/
instance continuousSemilinearMapClass :
    ContinuousSemilinearMapClass (M₁ →SL[σ₁₂] M₂) σ₁₂ M₁ M₂ where
  map_add f := map_add f.toLinearMap
  map_continuous f := f.2
  map_smulₛₗ f := f.toLinearMap.map_smul'
/-
**ContinuousLinearMap.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：coe_mk (f : M₁ ->ₛₗ[σ₁₂] M₂) (h) : (mk f h : M₁ ->ₛₗ[σ₁₂] M₂) = f
参数：f : M₁ ->ₛₗ[σ₁₂] M₂；h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (f : M₁ →ₛₗ[σ₁₂] M₂) (h) : (mk f h : M₁ →ₛₗ[σ₁₂] M₂) = f :=
  rfl

@[simp]
/-
**ContinuousLinearMap.coe_mk'** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：coe_mk' (f : M₁ ->ₛₗ[σ₁₂] M₂) (h) : (mk f h : M₁ -> M₂) = f
参数：f : M₁ ->ₛₗ[σ₁₂] M₂；h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk' (f : M₁ →ₛₗ[σ₁₂] M₂) (h) : (mk f h : M₁ → M₂) = f :=
  rfl

@[continuity, fun_prop]
/-
**ContinuousLinearMap.continuous** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`
。
形式化陈述：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Semiring R₁] [inst_1 : Semiring 
R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_2 : TopologicalSpace M₁] [inst_3 :
 AddCommMonoid M₁] {M₂ : Type u_6} [inst_4 : TopologicalSpace M₂]   [inst_5 : Ad
dCommMonoid M₂] [inst_6 : _root_.Module R₁ M₁] [inst_7 : _root_.Module R₂ M₂] (f
 : M₁ →SL[σ₁₂] M₂),   Continuous ⇑f
参数：f : M₁ →SL[σ₁₂] M₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.cont`：∀ {R : Type u_1} {S : Type u_2} [inst : Semiri
ng R] [inst_1 : Semiring S] {σ : R →+* S} {M : Type u_3}   [inst_2 : Topological
Space M] [inst…
-/
protected theorem continuous (f : M₁ →SL[σ₁₂] M₂) : Continuous f :=
  f.2

@[continuity, fun_prop]
/-
**ContinuousLinearMap.continuous_toLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `Continuo
usLinearMap`。
形式化陈述：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Semiring R₁] [inst_1 : Semiring 
R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_2 : TopologicalSpace M₁] [inst_3 :
 AddCommMonoid M₁] {M₂ : Type u_6} [inst_4 : TopologicalSpace M₂]   [inst_5 : Ad
dCommMonoid M₂] [inst_6 : _root_.Module R₁ M₁] [inst_7 : _root_.Module R₂ M₂] (f
 : M₁ →SL[σ₁₂] M₂),   Continuous ⇑↑f
参数：f : M₁ →SL[σ₁₂] M₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.cont`：∀ {R : Type u_1} {S : Type u_2} [inst : Semiri
ng R] [inst_1 : Semiring S] {σ : R →+* S} {M : Type u_3}   [inst_2 : Topological
Space M] [inst…
-/
protected theorem continuous_toLinearMap (f : M₁ →SL[σ₁₂] M₂) : Continuous f.toLinearMap :=
  f.2

@[simp]
/-
**ContinuousLinearMap.uniformContinuous** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLin
earMap`。
形式化陈述：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Semiring R₁] [inst_1 : Semiring 
R₂] {σ₁₂ : R₁ →+* R₂} {E₁ : Type u_9}   {E₂ : Type u_10} [inst_2 : UniformSpace 
E₁] [inst_3 : UniformSpace E₂] [inst_4 : AddCommGroup E₁]   [inst_5 : AddCommGro
up E₂] [inst_6 : _root_.Module R₁ E₁] [inst_7 : _root_.Module R₂ E₂] [IsUniformA
ddGroup E₁]   [IsUniformAddGroup E₂] (f : E₁ →SL[σ₁₂] E₂), UniformContinuous ⇑f
参数：f : E₁ →SL[σ₁₂] E₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `uniformContinuous_addMonoidHom_of_continuous`：∀ {α : Type u_1} {β : Type
 u_2} [inst : UniformSpace α] [inst_1 : AddGroup α] [IsUniformAddGroup α] {hom :
 Type u_3}   [inst_3 : UniformSpac…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
-/
protected theorem uniformContinuous {E₁ E₂ : Type*} [UniformSpace E₁] [UniformSpace E₂]
    [AddCommGroup E₁] [AddCommGroup E₂] [Module R₁ E₁] [Module R₂ E₂] [IsUniformAddGroup E₁]
    [IsUniformAddGroup E₂] (f : E₁ →SL[σ₁₂] E₂) : UniformContinuous f :=
  uniformContinuous_addMonoidHom_of_continuous f.continuous

@[simp, norm_cast]
/-
**ContinuousLinearMap.coe_inj** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：coe_inj {f g : M₁ ->SL[σ₁₂] M₂} : (f : M₁ ->ₛₗ[σ₁₂] M₂) = g ↔ f = g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `ContinuousLinearMap.coe_injective`：coe_injective : Function.Injective ((
↑) : (M₁ ->SL[σ₁₂] M₂) -> M₁ ->ₛₗ[σ₁₂] M₂)
-/
theorem coe_inj {f g : M₁ →SL[σ₁₂] M₂} : (f : M₁ →ₛₗ[σ₁₂] M₂) = g ↔ f = g :=
  coe_injective.eq_iff
/-
**ContinuousLinearMap.coeFn_injective** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinea
rMap`。
形式化陈述：coeFn_injective : @Function.Injective (M₁ ->SL[σ₁₂] M₂) (M₁ -> M₂) (↑)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
theorem coeFn_injective : @Function.Injective (M₁ →SL[σ₁₂] M₂) (M₁ → M₂) (↑) :=
  DFunLike.coe_injective
/-
**ContinuousLinearMap.toContinuousAddMonoidHom_injective** 是 Mathlib 中的一个定理，位于命名
空间 `ContinuousLinearMap`。
形式化陈述：toContinuousAddMonoidHom_injective : Function.Injective ((↑) : (M₁ ->SL[σ₁
₂] M₂) -> ContinuousAddMonoidHom M₁ M₂)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `ContinuousSemilinearMapClass.toContinuousMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `Function.Injective.of_comp_iff`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sor
t u_3} {f : α → β},   Function.Injective f → ∀ (g : γ → α), Function.Injective (
f ∘ g) ↔ Function.In…
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
theorem toContinuousAddMonoidHom_injective :
    Function.Injective ((↑) : (M₁ →SL[σ₁₂] M₂) → ContinuousAddMonoidHom M₁ M₂) :=
  (DFunLike.coe_injective.of_comp_iff _).1 DFunLike.coe_injective

@[simp, norm_cast]
/-
**ContinuousLinearMap.toContinuousAddMonoidHom_inj** 是 Mathlib 中的一个定理，位于命名空间 `Co
ntinuousLinearMap`。
形式化陈述：toContinuousAddMonoidHom_inj {f g : M₁ ->SL[σ₁₂] M₂} : (f : ContinuousAddM
onoidHom M₁ M₂) = g ↔ f = g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `ContinuousSemilinearMapClass.toContinuousMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `ContinuousLinearMap.toContinuousAddMonoidHom_injective`：toContinuousAddM
onoidHom_injective : Function.Injective ((↑) : (M₁ ->SL[σ₁₂] M₂) -> ContinuousAd
dMonoidHom M₁ M₂)
-/
theorem toContinuousAddMonoidHom_inj {f g : M₁ →SL[σ₁₂] M₂} :
    (f : ContinuousAddMonoidHom M₁ M₂) = g ↔ f = g :=
  toContinuousAddMonoidHom_injective.eq_iff

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
/-
**ContinuousLinearMap.Simps.apply** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap
.Simps`。
形式化陈述：{R₁ : Type u_1} →   {R₂ : Type u_2} →     [inst : Semiring R₁] →       [in
st_1 : Semiring R₂] →         {σ₁₂ : R₁ →+* R₂} →           {M₁ : Type u_4} →   
          [inst_2 : TopologicalSpace M₁] →               [inst_3 : AddCommMonoid
 M₁] →                 {M₂ : Type u_6} →                   [inst_4 : Topological
Space M₂] →                     [inst_5 : AddCommMonoid M₂] →                   
    [inst_6 : _root_.Module R₁ M₁] → [inst_7 : _root_.Module R₂ M₂] → (M₁ →SL[σ₁
₂] M₂) → M₁ → M₂
参数：M₁ →SL[σ₁₂] M₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection]. We need to specify this projection explicitl
y in this case,
  because it is a composition of multiple projections.
-/
def Simps.apply (h : M₁ →SL[σ₁₂] M₂) : M₁ → M₂ :=
  h

/-- See Note [custom simps projection]. -/
/-
**ContinuousLinearMap.Simps.coe** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap.S
imps`。
形式化陈述：{R₁ : Type u_1} →   {R₂ : Type u_2} →     [inst : Semiring R₁] →       [in
st_1 : Semiring R₂] →         {σ₁₂ : R₁ →+* R₂} →           {M₁ : Type u_4} →   
          [inst_2 : TopologicalSpace M₁] →               [inst_3 : AddCommMonoid
 M₁] →                 {M₂ : Type u_6} →                   [inst_4 : Topological
Space M₂] →                     [inst_5 : AddCommMonoid M₂] →                   
    [inst_6 : _root_.Module R₁ M₁] →                         [inst_7 : _root_.Mo
dule R₂ M₂] → (M₁ →SL[σ₁₂] M₂) → M₁ →ₛₗ[σ₁₂] M₂
参数：M₁ →SL[σ₁₂] M₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection].
-/
def Simps.coe (h : M₁ →SL[σ₁₂] M₂) : M₁ →ₛₗ[σ₁₂] M₂ :=
  h

initialize_simps_projections ContinuousLinearMap (toFun → apply, toLinearMap → coe, as_prefix coe)

@[ext]
/-
**ContinuousLinearMap.ext** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x = g x) : f = g
参数：h : forall x, f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {f g : M₁ →SL[σ₁₂] M₂} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

@[simp, norm_cast]
/-
**ContinuousLinearMap.coe_coe** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：coe_coe (f : M₁ ->SL[σ₁₂] M₂) : ⇑(f : M₁ ->ₛₗ[σ₁₂] M₂) = f
参数：f : M₁ ->SL[σ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_coe (f : M₁ →SL[σ₁₂] M₂) : ⇑(f : M₁ →ₛₗ[σ₁₂] M₂) = f :=
  rfl

/-- Copy of a `ContinuousLinearMap` with a new `toFun` equal to the old one. Useful to fix
definitional equalities. -/
/-
**ContinuousLinearMap.copy** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap`。
形式化陈述：{R₁ : Type u_1} →   {R₂ : Type u_2} →     [inst : Semiring R₁] →       [in
st_1 : Semiring R₂] →         {σ₁₂ : R₁ →+* R₂} →           {M₁ : Type u_4} →   
          [inst_2 : TopologicalSpace M₁] →               [inst_3 : AddCommMonoid
 M₁] →                 {M₂ : Type u_6} →                   [inst_4 : Topological
Space M₂] →                     [inst_5 : AddCommMonoid M₂] →                   
    [inst_6 : _root_.Module R₁ M₁] →                         [inst_7 : _root_.Mo
dule R₂ M₂] →                           (f : M₁ →SL[σ₁₂] M₂) → (f' : M₁ → M₂) → 
f' = ⇑f → M₁ →SL[σ₁₂] M₂
参数：f : M₁ →SL[σ₁₂] M₂；f' : M₁ → M₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of a `ContinuousLinearMap` with a new `toFun` equal to the old one. Useful 
to fix
definitional equalities.
-/
protected def copy (f : M₁ →SL[σ₁₂] M₂) (f' : M₁ → M₂) (h : f' = ⇑f) : M₁ →SL[σ₁₂] M₂ where
  toLinearMap := f.toLinearMap.copy f' h
  cont := show Continuous f' from h.symm ▸ f.continuous

@[simp]
/-
**ContinuousLinearMap.coe_copy** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：coe_copy (f : M₁ ->SL[σ₁₂] M₂) (f' : M₁ -> M₂) (h : f' = ⇑f) : ⇑(f.copy f'
 h) = f'
参数：f : M₁ ->SL[σ₁₂] M₂；f' : M₁ -> M₂；h : f' = ⇑f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_copy (f : M₁ →SL[σ₁₂] M₂) (f' : M₁ → M₂) (h : f' = ⇑f) : ⇑(f.copy f' h) = f' :=
  rfl
/-
**ContinuousLinearMap.copy_eq** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：copy_eq (f : M₁ ->SL[σ₁₂] M₂) (f' : M₁ -> M₂) (h : f' = ⇑f) : f.copy f' h 
= f
参数：f : M₁ ->SL[σ₁₂] M₂；f' : M₁ -> M₂；h : f' = ⇑f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext'`：ext' {f g : F} (h : (f : forall a : α, β a) = (g : forall
 a : α, β a)) : f = g
-/
theorem copy_eq (f : M₁ →SL[σ₁₂] M₂) (f' : M₁ → M₂) (h : f' = ⇑f) : f.copy f' h = f :=
  DFunLike.ext' h
/-
**ContinuousLinearMap.range_coeFn_eq** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinear
Map`。
形式化陈述：range_coeFn_eq : Set.range ((⇑) : (M₁ ->SL[σ₁₂] M₂) -> (M₁ -> M₂)) = {f | 
Continuous f} inter Set.range ((⇑) : (M₁ ->ₛₗ[σ₁₂] M₂) -> (M₁ -> M₂))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
-/
theorem range_coeFn_eq :
    Set.range ((⇑) : (M₁ →SL[σ₁₂] M₂) → (M₁ → M₂)) =
      {f | Continuous f} ∩ Set.range ((⇑) : (M₁ →ₛₗ[σ₁₂] M₂) → (M₁ → M₂)) := by
  ext f
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨f.continuous, f, rfl⟩
  · rintro ⟨hfc, f, rfl⟩
    exact ⟨⟨f, hfc⟩, rfl⟩
/-
**ContinuousLinearMap.range_toLinearMap** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLin
earMap`。
形式化陈述：range_toLinearMap (f : M₁ ->SL[σ₁₂] M₂) : Set.range f.toLinearMap = Set.ra
nge f
参数：f : M₁ ->SL[σ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma range_toLinearMap (f : M₁ →SL[σ₁₂] M₂) : Set.range f.toLinearMap = Set.range f := by simp

-- make some straightforward lemmas available to `simp`.
/-
**ContinuousLinearMap.map_zero** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Semiring R₁] [inst_1 : Semiring 
R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_2 : TopologicalSpace M₁] [inst_3 :
 AddCommMonoid M₁] {M₂ : Type u_6} [inst_4 : TopologicalSpace M₂]   [inst_5 : Ad
dCommMonoid M₂] [inst_6 : _root_.Module R₁ M₁] [inst_7 : _root_.Module R₂ M₂] (f
 : M₁ →SL[σ₁₂] M₂),   f 0 = 0
参数：f : M₁ →SL[σ₁₂] M₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
-/
protected theorem map_zero (f : M₁ →SL[σ₁₂] M₂) : f (0 : M₁) = 0 :=
  map_zero f
/-
**ContinuousLinearMap.map_add** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Semiring R₁] [inst_1 : Semiring 
R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_2 : TopologicalSpace M₁] [inst_3 :
 AddCommMonoid M₁] {M₂ : Type u_6} [inst_4 : TopologicalSpace M₂]   [inst_5 : Ad
dCommMonoid M₂] [inst_6 : _root_.Module R₁ M₁] [inst_7 : _root_.Module R₂ M₂] (f
 : M₁ →SL[σ₁₂] M₂)   (x y : M₁), f (x + y) = f x + f y
参数：f : M₁ →SL[σ₁₂] M₂；x y : M₁；x + y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
-/
protected theorem map_add (f : M₁ →SL[σ₁₂] M₂) (x y : M₁) : f (x + y) = f x + f y :=
  map_add f x y

@[simp]
/-
**ContinuousLinearMap.map_smul** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：∀ {R₁ : Type u_1} [inst : Semiring R₁] {M₁ : Type u_4} [inst_1 : Topologic
alSpace M₁] [inst_2 : AddCommMonoid M₁]   {M₂ : Type u_6} [inst_3 : TopologicalS
pace M₂] [inst_4 : AddCommMonoid M₂] [inst_5 : _root_.Module R₁ M₁]   [inst_6 : 
_root_.Module R₁ M₂] (f : M₁ →L[R₁] M₂) (c : R₁) (x : M₁), f (c • x) = c • f x
参数：f : M₁ →L[R₁] M₂；c : R₁；x : M₁；c • x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulActionSemiHomClass.map_smulₛₗ`：∀ {F : Type u_8} {M : outParam (Type u
_9)} {N : outParam (Type u_10)} {φ : outParam (M → N)} {X : outParam (Type u_11)
}   {Y : outParam (Typ…
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem map_smulₛₗ (f : M₁ →SL[σ₁₂] M₂) (c : R₁) (x : M₁) : f (c • x) = σ₁₂ c • f x :=
  (toLinearMap _).map_smulₛₗ _ _
/-
**ContinuousLinearMap.map_smul** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：∀ {R₁ : Type u_1} [inst : Semiring R₁] {M₁ : Type u_4} [inst_1 : Topologic
alSpace M₁] [inst_2 : AddCommMonoid M₁]   {M₂ : Type u_6} [inst_3 : TopologicalS
pace M₂] [inst_4 : AddCommMonoid M₂] [inst_5 : _root_.Module R₁ M₁]   [inst_6 : 
_root_.Module R₁ M₂] (f : M₁ →L[R₁] M₂) (c : R₁) (x : M₁), f (c • x) = c • f x
参数：f : M₁ →L[R₁] M₂；c : R₁；x : M₁；c • x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulActionSemiHomClass.map_smulₛₗ`：∀ {F : Type u_8} {M : outParam (Type u
_9)} {N : outParam (Type u_10)} {φ : outParam (M → N)} {X : outParam (Type u_11)
}   {Y : outParam (Typ…
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem map_smul [Module R₁ M₂] (f : M₁ →L[R₁] M₂) (c : R₁) (x : M₁) :
    f (c • x) = c • f x := by simp only [RingHom.id_apply, map_smulₛₗ]

@[simp]
/-
**ContinuousLinearMap.map_smul_of_tower** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLin
earMap`。
形式化陈述：map_smul_of_tower {R S : Type*} [Semiring S] [SMul R M₁] [Module S M₁] [SM
ul R M₂] [Module S M₂] [LinearMap.CompatibleSMul M₁ M₂ R S] (f : M₁ ->L[S] M₂) (
c : R) (x : M₁) : f (c • x) = c • f x
参数：f : M₁ ->L[S] M₂；c : R；x : M₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.CompatibleSMul.map_smul`：∀ {M : Type u_8} {M₂ : Type u_10} {in
st : AddCommMonoid M} {inst_1 : AddCommMonoid M₂} {R : Type u_14} {S : Type u_15
}   {inst_2 : Semiring …
-/
theorem map_smul_of_tower {R S : Type*} [Semiring S] [SMul R M₁] [Module S M₁] [SMul R M₂]
    [Module S M₂] [LinearMap.CompatibleSMul M₁ M₂ R S] (f : M₁ →L[S] M₂) (c : R) (x : M₁) :
    f (c • x) = c • f x :=
  LinearMap.CompatibleSMul.map_smul (f : M₁ →ₗ[S] M₂) c x

@[ext]
/-
**ContinuousLinearMap.ext_ring** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：ext_ring [TopologicalSpace R₁] {f g : R₁ ->L[R₁] M₁} (h : f 1 = g 1) : f =
 g
参数：h : f 1 = g 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ContinuousLinearMap.coe_inj`：coe_inj {f g : M₁ ->SL[σ₁₂] M₂} : (f : M₁ -
>ₛₗ[σ₁₂] M₂) = g ↔ f = g
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
-/
theorem ext_ring [TopologicalSpace R₁] {f g : R₁ →L[R₁] M₁} (h : f 1 = g 1) : f = g :=
  coe_inj.1 <| LinearMap.ext_ring h

@[simp]
/-
**ContinuousLinearMap.apply_val_ker** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearM
ap`。
形式化陈述：apply_val_ker (f : M₁ ->SL[σ₁₂] M₂) (x : f.ker) : f x = 0
参数：f : M₁ ->SL[σ₁₂] M₂；x : f.ker。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem apply_val_ker (f : M₁ →SL[σ₁₂] M₂) (x : f.ker) : f x = 0 := x.2

/-- If two continuous linear maps are equal on a set `s`, then they are equal on the closure
of the `Submodule.span` of this set. -/
/-
**ContinuousLinearMap.eqOn_closure_span** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLin
earMap`。
形式化陈述：eqOn_closure_span [T2Space M₂] {s : Set M₁} {f g : M₁ ->SL[σ₁₂] M₂} (h : S
et.EqOn f g s) : Set.EqOn f g (closure (Submodule.span R₁ s : Set M₁))
参数：h : Set.EqOn f g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.EqOn.closure`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpa
ce X] [inst_1 : TopologicalSpace Y] [T2Space X] {s : Set Y}   {f g : Y → X}, Set
.EqOn …
· 使用定理 `LinearMap.eqOn_span'`：eqOn_span' {s : Set M} {f g : M ->ₛₗ[σ₁₂] M₂} (H :
 Set.EqOn f g s) : Set.EqOn f g (span R s : Set M)
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…

--- 原说明 ---
If two continuous linear maps are equal on a set `s`, then they are equal on the
 closure
of the `Submodule.span` of this set.
-/
theorem eqOn_closure_span [T2Space M₂] {s : Set M₁} {f g : M₁ →SL[σ₁₂] M₂} (h : Set.EqOn f g s) :
    Set.EqOn f g (closure (Submodule.span R₁ s : Set M₁)) :=
  (LinearMap.eqOn_span' h).closure f.continuous g.continuous

/-- If the submodule generated by a set `s` is dense in the ambient module, then two continuous
linear maps equal on `s` are equal. -/
/-
**ContinuousLinearMap.ext_on** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：ext_on [T2Space M₂] {s : Set M₁} (hs : Dense (Submodule.span R₁ s : Set M₁
)) {f g : M₁ ->SL[σ₁₂] M₂} (h : Set.EqOn f g s) : f = g
参数：hs : Dense (Submodule.span R₁ s : Set M₁)；h : Set.EqOn f g s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `ContinuousLinearMap.eqOn_closure_span`：eqOn_closure_span [T2Space M₂] {s
 : Set M₁} {f g : M₁ ->SL[σ₁₂] M₂} (h : Set.EqOn f g s) : Set.EqOn f g (closure 
(Submodule.span R₁ s : Set …

--- 原说明 ---
If the submodule generated by a set `s` is dense in the ambient module, then two
 continuous
linear maps equal on `s` are equal.
-/
theorem ext_on [T2Space M₂] {s : Set M₁} (hs : Dense (Submodule.span R₁ s : Set M₁))
    {f g : M₁ →SL[σ₁₂] M₂} (h : Set.EqOn f g s) : f = g :=
  ext fun x => eqOn_closure_span h (hs x)

/-- Under a continuous linear map, the image of the `TopologicalClosure` of a submodule is
contained in the `TopologicalClosure` of its image. -/
/-
**ContinuousLinearMap._root_.Submodule.topologicalClosure_map** 是 Mathlib 中的一个定理
，位于命名空间 `ContinuousLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Under a continuous linear map, the image of the `TopologicalClosure` of a submod
ule is
contained in the `TopologicalClosure` of its image.
-/
theorem _root_.Submodule.topologicalClosure_map [RingHomSurjective σ₁₂] [TopologicalSpace R₁]
    [TopologicalSpace R₂] [ContinuousSMul R₁ M₁] [ContinuousAdd M₁] [ContinuousSMul R₂ M₂]
    [ContinuousAdd M₂] (f : M₁ →SL[σ₁₂] M₂) (s : Submodule R₁ M₁) :
    s.topologicalClosure.map (f : M₁ →ₛₗ[σ₁₂] M₂) ≤
      (s.map (f : M₁ →ₛₗ[σ₁₂] M₂)).topologicalClosure :=
  image_closure_subset_closure_image f.continuous

/-- If a continuous linear map stabilizes a submodule, then it stabilizes its topological
closure. -/
/-
**ContinuousLinearMap._root_.Submodule.topologicalClosure_mem_invtSubmodule** 是 
Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a continuous linear map stabilizes a submodule, then it stabilizes its topolo
gical
closure.
-/
theorem _root_.Submodule.topologicalClosure_mem_invtSubmodule [TopologicalSpace R₁]
    [ContinuousSMul R₁ M₁] [ContinuousAdd M₁] {f : M₁ →L[R₁] M₁} {s : Submodule R₁ M₁}
    (hs : s ∈ Module.End.invtSubmodule f) :
    s.topologicalClosure ∈ Module.End.invtSubmodule f := by
  rw [Module.End.mem_invtSubmodule_iff_map_le] at hs ⊢
  exact (s.topologicalClosure_map f).trans (Submodule.topologicalClosure_mono hs)

/-- Under a dense continuous linear map, a submodule whose `TopologicalClosure` is `⊤` is sent to
another such submodule.  That is, the image of a dense set under a map with dense range is dense.
-/
/-
**ContinuousLinearMap._root_.DenseRange.topologicalClosure_map_submodule** 是 Mat
hlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Under a dense continuous linear map, a submodule whose `TopologicalClosure` is `
⊤` is sent to
another such submodule.  That is, the image of a dense set under a map with dens
e range is dense.
-/
theorem _root_.DenseRange.topologicalClosure_map_submodule [RingHomSurjective σ₁₂]
    [TopologicalSpace R₁] [TopologicalSpace R₂] [ContinuousSMul R₁ M₁] [ContinuousAdd M₁]
    [ContinuousSMul R₂ M₂] [ContinuousAdd M₂] {f : M₁ →SL[σ₁₂] M₂} (hf' : DenseRange f)
    {s : Submodule R₁ M₁} (hs : s.topologicalClosure = ⊤) :
    (s.map (f : M₁ →ₛₗ[σ₁₂] M₂)).topologicalClosure = ⊤ := by
  rw [SetLike.ext'_iff] at hs ⊢
  simp only [Submodule.topologicalClosure_coe, Submodule.top_coe, ← dense_iff_closure_eq] at hs ⊢
  exact hf'.dense_image f.continuous hs

section SMul

variable {S₂ T₂ : Type*}
variable [DistribSMul S₂ M₂] [SMulCommClass R₂ S₂ M₂] [ContinuousConstSMul S₂ M₂]
variable [DistribSMul T₂ M₂] [SMulCommClass R₂ T₂ M₂] [ContinuousConstSMul T₂ M₂]

/-
**ContinuousLinearMap.instSMul** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLinearMap`。
形式化陈述：instSMul : SMul S₂ (M₁ ->SL[σ₁₂] M₂) where smul c f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSMul : SMul S₂ (M₁ →SL[σ₁₂] M₂) where
  smul c f := ⟨c • (f : M₁ →ₛₗ[σ₁₂] M₂), (f.2.const_smul _ : Continuous fun x => c • f x)⟩
/-
**ContinuousLinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsSMulApply S₂ (M₁ →SL[σ₁₂] M₂) M₁ M₂ where
  smul_apply _ _ _ := rfl

@[simp, norm_cast]
/-
**ContinuousLinearMap.toLinearMap_smul** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLine
arMap`。
形式化陈述：toLinearMap_smul (c : S₂) (f : M₁ ->SL[σ₁₂] M₂) : ↑(c • f) = c • (f : M₁ -
>ₛₗ[σ₁₂] M₂)
参数：c : S₂；f : M₁ ->SL[σ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLinearMap_smul (c : S₂) (f : M₁ →SL[σ₁₂] M₂) :
    ↑(c • f) = c • (f : M₁ →ₛₗ[σ₁₂] M₂) :=
  rfl

@[deprecated (since := "2026-05-20")] protected alias smul_apply := _root_.smul_apply

@[deprecated (since := "2026-05-20")] protected alias coe_smul := toLinearMap_smul

@[deprecated (since := "2026-05-20")] alias coe_smul' := FunLike.coe_smul
/-
**ContinuousLinearMap.isScalarTower** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLinearM
ap`。
形式化陈述：isScalarTower [SMul S₂ T₂] [IsScalarTower S₂ T₂ M₂] : IsScalarTower S₂ T₂ 
(M₁ ->SL[σ₁₂] M₂)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `FunLike.isScalarTower`：∀ {M : Type u_1} {M' : Type u_2} {F : Type u_3} {
α : Type u_4} {β : Type u_5} [i : FunLike F α β] [inst : SMul M β]   [inst_1 : S
Mul M' β] […
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
-/
instance isScalarTower [SMul S₂ T₂] [IsScalarTower S₂ T₂ M₂] :
    IsScalarTower S₂ T₂ (M₁ →SL[σ₁₂] M₂) := FunLike.isScalarTower
/-
**ContinuousLinearMap.smulCommClass** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLinearM
ap`。
形式化陈述：smulCommClass [SMulCommClass S₂ T₂ M₂] : SMulCommClass S₂ T₂ (M₁ ->SL[σ₁₂]
 M₂)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `FunLike.smulCommClass`：∀ {M : Type u_1} {M' : Type u_2} {F : Type u_3} {
α : Type u_4} {β : Type u_5} [i : FunLike F α β] [inst : SMul M β]   [inst_1 : S
Mul M' β] […
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
-/
instance smulCommClass [SMulCommClass S₂ T₂ M₂] : SMulCommClass S₂ T₂ (M₁ →SL[σ₁₂] M₂) :=
  FunLike.smulCommClass

end SMul

section SMulMonoid

variable {S₂ : Type*} [Monoid S₂]
variable [DistribMulAction S₂ M₂] [SMulCommClass R₂ S₂ M₂] [ContinuousConstSMul S₂ M₂]

/-
**ContinuousLinearMap.mulAction** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLinearMap`。
形式化陈述：mulAction : MulAction S₂ (M₁ ->SL[σ₁₂] M₂)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance mulAction : MulAction S₂ (M₁ →SL[σ₁₂] M₂) := fast_instance% FunLike.mulAction

end SMulMonoid

/-- The continuous map that is constantly zero. -/
/-
**ContinuousLinearMap.zero** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLinearMap`。
形式化陈述：zero : Zero (M₁ ->SL[σ₁₂] M₂)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The continuous map that is constantly zero.
-/
instance zero : Zero (M₁ →SL[σ₁₂] M₂) :=
  ⟨⟨0, continuous_zero⟩⟩
/-
**ContinuousLinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsZeroApply (M₁ →SL[σ₁₂] M₂) M₁ M₂ where
  zero_apply _ := rfl
/-
**ContinuousLinearMap.inhabited** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLinearMap`。
形式化陈述：inhabited : Inhabited (M₁ ->SL[σ₁₂] M₂)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inhabited : Inhabited (M₁ →SL[σ₁₂] M₂) :=
  ⟨0⟩

@[simp]
/-
**ContinuousLinearMap.default_def** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap
`。
形式化陈述：default_def : (default : M₁ ->SL[σ₁₂] M₂) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem default_def : (default : M₁ →SL[σ₁₂] M₂) = 0 :=
  rfl

@[simp, norm_cast]
/-
**ContinuousLinearMap.toLinearMap_zero** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLine
arMap`。
形式化陈述：toLinearMap_zero : ((0 : M₁ ->SL[σ₁₂] M₂) : M₁ ->ₛₗ[σ₁₂] M₂) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLinearMap_zero : ((0 : M₁ →SL[σ₁₂] M₂) : M₁ →ₛₗ[σ₁₂] M₂) = 0 :=
  rfl

@[deprecated (since := "2026-05-20")] protected alias zero_apply := _root_.zero_apply

@[deprecated (since := "2026-05-20")] protected alias coe_zero := toLinearMap_zero

@[deprecated (since := "2026-05-20")] alias coe_zero' := FunLike.coe_zero

@[simp, norm_cast]
/-
**ContinuousLinearMap.toContinuousAddMonoidHom_zero** 是 Mathlib 中的一个定理，位于命名空间 `C
ontinuousLinearMap`。
形式化陈述：toContinuousAddMonoidHom_zero : ((0 : M₁ ->SL[σ₁₂] M₂) : ContinuousAddMono
idHom M₁ M₂) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `ContinuousSemilinearMapClass.toContinuousMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
-/
theorem toContinuousAddMonoidHom_zero :
    ((0 : M₁ →SL[σ₁₂] M₂) : ContinuousAddMonoidHom M₁ M₂) = 0 := rfl
/-
**ContinuousLinearMap.uniqueOfLeft** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLinearMa
p`。
形式化陈述：uniqueOfLeft [Subsingleton M₁] : Unique (M₁ ->SL[σ₁₂] M₂)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.coe_injective`：coe_injective : Function.Injective ((
↑) : (M₁ ->SL[σ₁₂] M₂) -> M₁ ->ₛₗ[σ₁₂] M₂)
-/
instance uniqueOfLeft [Subsingleton M₁] : Unique (M₁ →SL[σ₁₂] M₂) :=
  coe_injective.unique
/-
**ContinuousLinearMap.uniqueOfRight** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLinearM
ap`。
形式化陈述：uniqueOfRight [Subsingleton M₂] : Unique (M₁ ->SL[σ₁₂] M₂)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.coe_injective`：coe_injective : Function.Injective ((
↑) : (M₁ ->SL[σ₁₂] M₂) -> M₁ ->ₛₗ[σ₁₂] M₂)
-/
instance uniqueOfRight [Subsingleton M₂] : Unique (M₁ →SL[σ₁₂] M₂) :=
  coe_injective.unique
/-
**ContinuousLinearMap.exists_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinear
Map`。
形式化陈述：exists_ne_zero {f : M₁ ->SL[σ₁₂] M₂} (hf : f != 0) : exists x, f x != 0
参数：hf : f != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
theorem exists_ne_zero {f : M₁ →SL[σ₁₂] M₂} (hf : f ≠ 0) : ∃ x, f x ≠ 0 := by
  by_contra! h
  exact hf (ContinuousLinearMap.ext h)

section

variable (R₁ M₁)

/-- the identity map as a continuous linear map. -/
/-
**ContinuousLinearMap.id** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap`。
形式化陈述：(R₁ : Type u_1) →   [inst : Semiring R₁] →     (M₁ : Type u_4) →       [in
st_1 : TopologicalSpace M₁] → [inst_2 : AddCommMonoid M₁] → [inst_3 : _root_.Mod
ule R₁ M₁] → M₁ →L[R₁] M₁
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)

--- 原说明 ---
the identity map as a continuous linear map.
-/
protected def id : M₁ →L[R₁] M₁ :=
  ⟨LinearMap.id, continuous_id⟩

end

/-
**ContinuousLinearMap.one** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLinearMap`。
形式化陈述：one : One (M₁ ->L[R₁] M₁)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance one : One (M₁ →L[R₁] M₁) :=
  ⟨.id R₁ M₁⟩
/-
**ContinuousLinearMap.one_def** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：one_def : (1 : M₁ ->L[R₁] M₁) = .id R₁ M₁
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_def : (1 : M₁ →L[R₁] M₁) = .id R₁ M₁ := rfl
/-
**ContinuousLinearMap.instIsOneApply** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLinear
Map`。
形式化陈述：instIsOneApply : IsOneApplyEqSelf (M₁ ->L[R₁] M₁) M₁ where one_apply_eq_se
lf _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instIsOneApply : IsOneApplyEqSelf (M₁ →L[R₁] M₁) M₁ where
  one_apply_eq_self _ := rfl

@[simp]
/-
**ContinuousLinearMap.id_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：id_apply (x : M₁) : ContinuousLinearMap.id R₁ M₁ x = x
参数：x : M₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_apply (x : M₁) : ContinuousLinearMap.id R₁ M₁ x = x := rfl

@[simp, norm_cast]
/-
**ContinuousLinearMap.coe_id** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：coe_id : (ContinuousLinearMap.id R₁ M₁ : M₁ ->ₗ[R₁] M₁) = LinearMap.id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_id : (ContinuousLinearMap.id R₁ M₁ : M₁ →ₗ[R₁] M₁) = LinearMap.id :=
  rfl

@[simp, norm_cast]
/-
**ContinuousLinearMap.coe_id'** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：coe_id' : ⇑(ContinuousLinearMap.id R₁ M₁) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_id' : ⇑(ContinuousLinearMap.id R₁ M₁) = id :=
  rfl

@[simp, norm_cast]
/-
**ContinuousLinearMap.toLinearMap_one** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinea
rMap`。
形式化陈述：toLinearMap_one : ((1 : M₁ ->L[R₁] M₁) : M₁ ->ₗ[R₁] M₁) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLinearMap_one : ((1 : M₁ →L[R₁] M₁) : M₁ →ₗ[R₁] M₁) = 1 :=
  rfl

@[deprecated (since := "2026-05-20")] protected alias coe_one := toLinearMap_one
/-
**ContinuousLinearMap.mk_id** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：∀ {R₁ : Type u_1} [inst : Semiring R₁] {M₁ : Type u_4} [inst_1 : Topologic
alSpace M₁] [inst_2 : AddCommMonoid M₁]   [inst_3 : _root_.Module R₁ M₁], { toLi
nearMap := LinearMap.id, cont := ⋯ } = ContinuousLinearMap.id R₁ M₁
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
-/
@[simp] lemma mk_id : mk (.id : M₁ →ₗ[R₁] M₁) continuous_id = .id _ _ := rfl
/-
**ContinuousLinearMap.mk_one** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：∀ {R₁ : Type u_1} [inst : Semiring R₁] {M₁ : Type u_4} [inst_1 : Topologic
alSpace M₁] [inst_2 : AddCommMonoid M₁]   [inst_3 : _root_.Module R₁ M₁], { toLi
nearMap := 1, cont := ⋯ } = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
-/
@[simp] lemma mk_one : mk (1 : M₁ →ₗ[R₁] M₁) continuous_id = 1 := rfl

@[simp, norm_cast]
/-
**ContinuousLinearMap.toContinuousAddMonoidHom_id** 是 Mathlib 中的一个定理，位于命名空间 `Con
tinuousLinearMap`。
形式化陈述：toContinuousAddMonoidHom_id : (ContinuousLinearMap.id R₁ M₁ : ContinuousAd
dMonoidHom M₁ M₁) = .id _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `ContinuousSemilinearMapClass.toContinuousMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
-/
theorem toContinuousAddMonoidHom_id :
    (ContinuousLinearMap.id R₁ M₁ : ContinuousAddMonoidHom M₁ M₁) = .id _ := rfl

@[simp, norm_cast]
/-
**ContinuousLinearMap.coe_eq_id** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：coe_eq_id {f : M₁ ->L[R₁] M₁} : (f : M₁ ->ₗ[R₁] M₁) = LinearMap.id ↔ f = .
id _ _
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearMap.coe_id`：coe_id : (ContinuousLinearMap.id R₁ M₁ : M₁ 
->ₗ[R₁] M₁) = LinearMap.id
· 使用定理 `ContinuousLinearMap.coe_inj`：coe_inj {f g : M₁ ->SL[σ₁₂] M₂} : (f : M₁ -
>ₛₗ[σ₁₂] M₂) = g ↔ f = g
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coe_eq_id {f : M₁ →L[R₁] M₁} : (f : M₁ →ₗ[R₁] M₁) = LinearMap.id ↔ f = .id _ _ := by
  rw [← coe_id, coe_inj]

@[deprecated (since := "2026-05-20")] protected alias one_apply := one_apply_eq_self
/-
**ContinuousLinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nontrivial M₁] : Nontrivial (M₁ →L[R₁] M₁) :=
  ⟨0, 1, fun e ↦
    have ⟨x, hx⟩ := exists_ne (0 : M₁); hx (by simpa using DFunLike.congr_fun e.symm x)⟩

section Add

variable [ContinuousAdd M₂]

/-
**ContinuousLinearMap.add** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLinearMap`。
形式化陈述：add : Add (M₁ ->SL[σ₁₂] M₂)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance add : Add (M₁ →SL[σ₁₂] M₂) :=
  ⟨fun f g => ⟨f + g, f.2.add g.2⟩⟩
/-
**ContinuousLinearMap.instIsAddApply** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLinear
Map`。
形式化陈述：instIsAddApply : IsAddApply (M₁ ->SL[σ₁₂] M₂) M₁ M₂ where add_apply _ _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instIsAddApply : IsAddApply (M₁ →SL[σ₁₂] M₂) M₁ M₂ where
  add_apply _ _ _ := rfl

@[simp, norm_cast]
/-
**ContinuousLinearMap.toLinearMap_add** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinea
rMap`。
形式化陈述：toLinearMap_add (f g : M₁ ->SL[σ₁₂] M₂) : (↑(f + g) : M₁ ->ₛₗ[σ₁₂] M₂) = f
 + g
参数：f g : M₁ ->SL[σ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLinearMap_add (f g : M₁ →SL[σ₁₂] M₂) : (↑(f + g) : M₁ →ₛₗ[σ₁₂] M₂) = f + g :=
  rfl

@[deprecated (since := "2026-05-20")] protected alias add_apply := _root_.add_apply

@[deprecated (since := "2026-05-20")] protected alias coe_add := toLinearMap_add

@[deprecated (since := "2026-05-20")] alias coe_add' := FunLike.coe_add

@[simp, norm_cast]
/-
**ContinuousLinearMap.toContinuousAddMonoidHom_add** 是 Mathlib 中的一个定理，位于命名空间 `Co
ntinuousLinearMap`。
形式化陈述：toContinuousAddMonoidHom_add (f g : M₁ ->SL[σ₁₂] M₂) : ↑(f + g) = (f + g :
 ContinuousAddMonoidHom M₁ M₂)
参数：f g : M₁ ->SL[σ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `ContinuousSemilinearMapClass.toContinuousMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
-/
theorem toContinuousAddMonoidHom_add (f g : M₁ →SL[σ₁₂] M₂) :
    ↑(f + g) = (f + g : ContinuousAddMonoidHom M₁ M₂) := rfl

-- The `AddMonoid` instance exists to help speedup unification
/-
**ContinuousLinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddMonoid (M₁ →SL[σ₁₂] M₂) := fast_instance% FunLike.addMonoid
/-
**ContinuousLinearMap.addCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLinearM
ap`。
形式化陈述：addCommMonoid : AddCommMonoid (M₁ ->SL[σ₁₂] M₂)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addCommMonoid : AddCommMonoid (M₁ →SL[σ₁₂] M₂) := fast_instance% FunLike.addCommMonoid

@[simp, norm_cast]
/-
**ContinuousLinearMap.toLinearMap_sum** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinea
rMap`。
形式化陈述：toLinearMap_sum {ι : Type*} (t : Finset ι) (f : ι -> M₁ ->SL[σ₁₂] M₂) : ↑(
∑ d in t, f d) = (∑ d in t, f d : M₁ ->ₛₗ[σ₁₂] M₂)
参数：t : Finset ι；f : ι -> M₁ ->SL[σ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem toLinearMap_sum {ι : Type*} (t : Finset ι) (f : ι → M₁ →SL[σ₁₂] M₂) :
    ↑(∑ d ∈ t, f d) = (∑ d ∈ t, f d : M₁ →ₛₗ[σ₁₂] M₂) :=
  map_sum (AddMonoidHom.mk ⟨((↑) : (M₁ →SL[σ₁₂] M₂) → M₁ →ₛₗ[σ₁₂] M₂), rfl⟩ fun _ _ => rfl) _ _

@[deprecated (since := "2026-05-20")] protected alias sum_apply := _root_.sum_apply

@[deprecated (since := "2026-05-20")] protected alias coe_sum := toLinearMap_sum

@[deprecated (since := "2026-05-20")] alias coe_sum' := FunLike.coe_sum

end Add

variable [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

/-- Composition of continuous linear maps. -/
/-
**ContinuousLinearMap.comp** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap`。
形式化陈述：comp (g : M₂ ->SL[σ₂₃] M₃) (f : M₁ ->SL[σ₁₂] M₂) : M₁ ->SL[σ₁₃] M₃
参数：g : M₂ ->SL[σ₂₃] M₃；f : M₁ ->SL[σ₁₂] M₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of continuous linear maps.
-/
def comp (g : M₂ →SL[σ₂₃] M₃) (f : M₁ →SL[σ₁₂] M₂) : M₁ →SL[σ₁₃] M₃ :=
  ⟨(g : M₂ →ₛₗ[σ₂₃] M₃).comp (f : M₁ →ₛₗ[σ₁₂] M₂), g.2.comp f.2⟩

@[inherit_doc comp]
infixr:80 " ∘L " =>
  @ContinuousLinearMap.comp _ _ _ _ _ _ (RingHom.id _) (RingHom.id _) (RingHom.id _) _ _ _ _ _ _ _ _
    _ _ _ _ RingHomCompTriple.ids

@[inherit_doc comp]
infixr:90 " ∘SL " =>
  ContinuousLinearMap.comp

@[simp, norm_cast]
/-
**ContinuousLinearMap.toLinearMap_comp** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLine
arMap`。
形式化陈述：toLinearMap_comp (h : M₂ ->SL[σ₂₃] M₃) (f : M₁ ->SL[σ₁₂] M₂) : (h ∘SL f : 
M₁ ->ₛₗ[σ₁₃] M₃) = (h : M₂ ->ₛₗ[σ₂₃] M₃) ∘ₛₗ (f : M₁ ->ₛₗ[σ₁₂] M₂)
参数：h : M₂ ->SL[σ₂₃] M₃；f : M₁ ->SL[σ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLinearMap_comp (h : M₂ →SL[σ₂₃] M₃) (f : M₁ →SL[σ₁₂] M₂) :
    (h ∘SL f : M₁ →ₛₗ[σ₁₃] M₃) = (h : M₂ →ₛₗ[σ₂₃] M₃) ∘ₛₗ (f : M₁ →ₛₗ[σ₁₂] M₂) :=
  rfl

@[norm_cast]
/-
**ContinuousLinearMap.coe_comp** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：coe_comp (h : M₂ ->SL[σ₂₃] M₃) (f : M₁ ->SL[σ₁₂] M₂) : ⇑(h ∘SL f) = h ∘ f
参数：h : M₂ ->SL[σ₂₃] M₃；f : M₁ ->SL[σ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comp (h : M₂ →SL[σ₂₃] M₃) (f : M₁ →SL[σ₁₂] M₂) : ⇑(h ∘SL f) = h ∘ f :=
  rfl

@[deprecated (since := "2026-05-20")] alias coe_comp' := coe_comp

@[simp, norm_cast]
/-
**ContinuousLinearMap.toContinuousAddMonoidHom_comp** 是 Mathlib 中的一个定理，位于命名空间 `C
ontinuousLinearMap`。
形式化陈述：toContinuousAddMonoidHom_comp (h : M₂ ->SL[σ₂₃] M₃) (f : M₁ ->SL[σ₁₂] M₂) 
: (↑(h ∘SL f) : ContinuousAddMonoidHom M₁ M₃) = (h : ContinuousAddMonoidHom M₂ M
₃).comp f
参数：h : M₂ ->SL[σ₂₃] M₃；f : M₁ ->SL[σ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `ContinuousSemilinearMapClass.toContinuousMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
-/
theorem toContinuousAddMonoidHom_comp (h : M₂ →SL[σ₂₃] M₃) (f : M₁ →SL[σ₁₂] M₂) :
    (↑(h ∘SL f) : ContinuousAddMonoidHom M₁ M₃) = (h : ContinuousAddMonoidHom M₂ M₃).comp f := rfl

@[simp, grind =]
/-
**ContinuousLinearMap.comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`
。
形式化陈述：comp_apply (g : M₂ ->SL[σ₂₃] M₃) (f : M₁ ->SL[σ₁₂] M₂) (x : M₁) : (g ∘SL f
) x = g (f x)
参数：g : M₂ ->SL[σ₂₃] M₃；f : M₁ ->SL[σ₁₂] M₂；x : M₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_apply (g : M₂ →SL[σ₂₃] M₃) (f : M₁ →SL[σ₁₂] M₂) (x : M₁) : (g ∘SL f) x = g (f x) :=
  rfl

@[simp]
/-
**ContinuousLinearMap.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：comp_id (f : M₁ ->SL[σ₁₂] M₂) : f ∘SL .id R₁ M₁ = f
参数：f : M₁ ->SL[σ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
-/
theorem comp_id (f : M₁ →SL[σ₁₂] M₂) : f ∘SL .id R₁ M₁ = f :=
  ext fun _x => rfl

@[simp]
/-
**ContinuousLinearMap.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：id_comp (f : M₁ ->SL[σ₁₂] M₂) : .id R₂ M₂ ∘SL f = f
参数：f : M₁ ->SL[σ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
-/
theorem id_comp (f : M₁ →SL[σ₁₂] M₂) : .id R₂ M₂ ∘SL f = f :=
  ext fun _x => rfl

section

variable {R E F : Type*} [Semiring R]
  [TopologicalSpace E] [AddCommMonoid E] [Module R E]
  [TopologicalSpace F] [AddCommMonoid F] [Module R F]

/-- `g ∘ f = id` as `ContinuousLinearMap`s implies `g ∘ f = id` as functions. -/
/-
**ContinuousLinearMap.leftInverse_of_comp** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousL
inearMap`。
形式化陈述：leftInverse_of_comp {f : E ->L[R] F} {g : F ->L[R] E} (hinv : g ∘L f = .id
 R E) : Function.LeftInverse g f
参数：hinv : g ∘L f = .id R E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
`g ∘ f = id` as `ContinuousLinearMap`s implies `g ∘ f = id` as functions.
-/
lemma leftInverse_of_comp {f : E →L[R] F} {g : F →L[R] E}
    (hinv : g ∘L f = .id R E) : Function.LeftInverse g f := by
  simpa [coe_comp, ← Function.leftInverse_iff_comp] using congr(⇑$hinv)

/-- `f ∘ g = id` as `ContinuousLinearMap`s implies `f ∘ g = id` as functions. -/
/-
**ContinuousLinearMap.rightInverse_of_comp** 是 Mathlib 中的一个引理，位于命名空间 `Continuous
LinearMap`。
形式化陈述：rightInverse_of_comp {f : E ->L[R] F} {g : F ->L[R] E} (hinv : f ∘L g = .i
d R F) : Function.RightInverse g f
参数：hinv : f ∘L g = .id R F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousLinearMap.leftInverse_of_comp`：leftInverse_of_comp {f : E ->L[
R] F} {g : F ->L[R] E} (hinv : g ∘L f = .id R E) : Function.LeftInverse g f

--- 原说明 ---
`f ∘ g = id` as `ContinuousLinearMap`s implies `f ∘ g = id` as functions.
-/
lemma rightInverse_of_comp {f : E →L[R] F} {g : F →L[R] E}
    (hinv : f ∘L g = .id R F) : Function.RightInverse g f :=
  leftInverse_of_comp hinv

end

@[simp]
/-
**ContinuousLinearMap.comp_zero** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：comp_zero (g : M₂ ->SL[σ₂₃] M₃) : g ∘SL (0 : M₁ ->SL[σ₁₂] M₂) = 0
参数：g : M₂ ->SL[σ₂₃] M₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comp_zero (g : M₂ →SL[σ₂₃] M₃) : g ∘SL (0 : M₁ →SL[σ₁₂] M₂) = 0 := by
  ext
  simp

@[simp]
/-
**ContinuousLinearMap.zero_comp** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：zero_comp (f : M₁ ->SL[σ₁₂] M₂) : (0 : M₂ ->SL[σ₂₃] M₃) ∘SL f = 0
参数：f : M₁ ->SL[σ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem zero_comp (f : M₁ →SL[σ₁₂] M₂) : (0 : M₂ →SL[σ₂₃] M₃) ∘SL f = 0 := by
  ext
  simp

@[simp]
/-
**ContinuousLinearMap.comp_add** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：comp_add [ContinuousAdd M₂] [ContinuousAdd M₃] (g : M₂ ->SL[σ₂₃] M₃) (f₁ f
₂ : M₁ ->SL[σ₁₂] M₂) : g ∘SL (f₁ + f₂) = g ∘SL f₁ + g ∘SL f₂
参数：g : M₂ ->SL[σ₂₃] M₃；f₁ f₂ : M₁ ->SL[σ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comp_add [ContinuousAdd M₂] [ContinuousAdd M₃] (g : M₂ →SL[σ₂₃] M₃)
    (f₁ f₂ : M₁ →SL[σ₁₂] M₂) : g ∘SL (f₁ + f₂) = g ∘SL f₁ + g ∘SL f₂ := by
  ext
  simp

@[simp]
/-
**ContinuousLinearMap.add_comp** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：add_comp [ContinuousAdd M₃] (g₁ g₂ : M₂ ->SL[σ₂₃] M₃) (f : M₁ ->SL[σ₁₂] M₂
) : (g₁ + g₂) ∘SL f = g₁ ∘SL f + g₂ ∘SL f
参数：g₁ g₂ : M₂ ->SL[σ₂₃] M₃；f : M₁ ->SL[σ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem add_comp [ContinuousAdd M₃] (g₁ g₂ : M₂ →SL[σ₂₃] M₃) (f : M₁ →SL[σ₁₂] M₂) :
    (g₁ + g₂) ∘SL f = g₁ ∘SL f + g₂ ∘SL f := by
  ext
  simp
/-
**ContinuousLinearMap.comp_finsetSum** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinear
Map`。
形式化陈述：comp_finsetSum {ι : Type*} {s : Finset ι} [ContinuousAdd M₂] [ContinuousAd
d M₃] (g : M₂ ->SL[σ₂₃] M₃) (f : ι -> M₁ ->SL[σ₁₂] M₂) : g ∘SL (∑ i in s, f i) =
 ∑ i in s, g ∘SL (f i)
参数：g : M₂ ->SL[σ₂₃] M₃；f : ι -> M₁ ->SL[σ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sum_apply`：∀ {F : Type u_8} {α : Type u_9} {β : Type u_10} {ι : Type u_1
1} [inst : FunLike F α β] [inst_1 : AddCommMonoid β]   [inst_2 : AddCommMonoid …
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comp_finsetSum {ι : Type*} {s : Finset ι}
    [ContinuousAdd M₂] [ContinuousAdd M₃] (g : M₂ →SL[σ₂₃] M₃)
    (f : ι → M₁ →SL[σ₁₂] M₂) : g ∘SL (∑ i ∈ s, f i) = ∑ i ∈ s, g ∘SL (f i) := by
  ext
  simp

@[deprecated (since := "2026-04-08")] alias comp_finset_sum := comp_finsetSum
/-
**ContinuousLinearMap.finsetSum_comp** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinear
Map`。
形式化陈述：finsetSum_comp {ι : Type*} {s : Finset ι} [ContinuousAdd M₃] (g : ι -> M₂ 
->SL[σ₂₃] M₃) (f : M₁ ->SL[σ₁₂] M₂) : (∑ i in s, g i) ∘SL f = ∑ i in s, (g i) ∘S
L f
参数：g : ι -> M₂ ->SL[σ₂₃] M₃；f : M₁ ->SL[σ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sum_apply`：∀ {F : Type u_8} {α : Type u_9} {β : Type u_10} {ι : Type u_1
1} [inst : FunLike F α β] [inst_1 : AddCommMonoid β]   [inst_2 : AddCommMonoid …
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finsetSum_comp {ι : Type*} {s : Finset ι}
    [ContinuousAdd M₃] (g : ι → M₂ →SL[σ₂₃] M₃)
    (f : M₁ →SL[σ₁₂] M₂) : (∑ i ∈ s, g i) ∘SL f = ∑ i ∈ s, (g i) ∘SL f := by
  ext
  simp only [comp_apply, sum_apply]

@[deprecated (since := "2026-04-08")] alias finset_sum_comp := finsetSum_comp
/-
**ContinuousLinearMap.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`
。
形式化陈述：comp_assoc {R₄ : Type*} [Semiring R₄] [Module R₄ M₄] {σ₁₄ : R₁ ->+* R₄} {σ
₂₄ : R₂ ->+* R₄} {σ₃₄ : R₃ ->+* R₄} [RingHomCompTriple σ₁₃ σ₃₄ σ₁₄] [RingHomComp
Triple σ₂₃ σ₃₄ σ₂₄] [RingHomCompTriple σ₁₂ σ₂₄ σ₁₄] (h : M₃ ->SL[σ₃₄] M₄) (g : M
₂ ->SL[σ₂₃] M₃) (f : M₁ ->SL[σ₁₂] M₂) : (h ∘SL g) ∘SL f = h ∘SL (g ∘SL f)
参数：h : M₃ ->SL[σ₃₄] M₄；g : M₂ ->SL[σ₂₃] M₃；f : M₁ ->SL[σ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_assoc {R₄ : Type*} [Semiring R₄] [Module R₄ M₄] {σ₁₄ : R₁ →+* R₄} {σ₂₄ : R₂ →+* R₄}
    {σ₃₄ : R₃ →+* R₄} [RingHomCompTriple σ₁₃ σ₃₄ σ₁₄] [RingHomCompTriple σ₂₃ σ₃₄ σ₂₄]
    [RingHomCompTriple σ₁₂ σ₂₄ σ₁₄] (h : M₃ →SL[σ₃₄] M₄) (g : M₂ →SL[σ₂₃] M₃) (f : M₁ →SL[σ₁₂] M₂) :
    (h ∘SL g) ∘SL f = h ∘SL (g ∘SL f) :=
  rfl
/-
**ContinuousLinearMap.cancel_left** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap
`。
形式化陈述：cancel_left {g : M₂ ->SL[σ₂₃] M₃} {f₁ f₂ : M₁ ->SL[σ₁₂] M₂} (hg : Function
.Injective g) (h : g ∘SL f₁ = g ∘SL f₂) : f₁ = f₂
参数：hg : Function.Injective g；h : g ∘SL f₁ = g ∘SL f₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem cancel_left {g : M₂ →SL[σ₂₃] M₃} {f₁ f₂ : M₁ →SL[σ₁₂] M₂} (hg : Function.Injective g)
    (h : g ∘SL f₁ = g ∘SL f₂) : f₁ = f₂ := by
  ext x
  exact hg congr($h x)
/-
**ContinuousLinearMap.cancel_left'** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLinearMa
p`。
形式化陈述：cancel_left' {g : M₂ ->SL[σ₂₃] M₃} {f₁ f₂ : M₁ ->SL[σ₁₂] M₂} (hg : Functio
n.Injective g) : g ∘SL f₁ = g ∘SL f₂ ↔ f₁ = f₂
参数：hg : Function.Injective g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.cancel_left`：cancel_left {g : M₂ ->SL[σ₂₃] M₃} {f₁ f
₂ : M₁ ->SL[σ₁₂] M₂} (hg : Function.Injective g) (h : g ∘SL f₁ = g ∘SL f₂) : f₁ 
= f₂
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
lemma cancel_left' {g : M₂ →SL[σ₂₃] M₃} {f₁ f₂ : M₁ →SL[σ₁₂] M₂} (hg : Function.Injective g) :
    g ∘SL f₁ = g ∘SL f₂ ↔ f₁ = f₂ :=
  ⟨cancel_left hg, congr_arg (fun f => g ∘SL f)⟩
/-
**ContinuousLinearMap.instMul** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLinearMap`。
形式化陈述：instMul : Mul (M₁ ->L[R₁] M₁)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMul : Mul (M₁ →L[R₁] M₁) :=
  ⟨comp⟩
/-
**ContinuousLinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsMulApplyEqComp (M₁ →L[R₁] M₁) M₁ where
  mul_apply_eq_comp _ _ _ := rfl
/-
**ContinuousLinearMap.mul_def** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：mul_def (f g : M₁ ->L[R₁] M₁) : f * g = f ∘L g
参数：f g : M₁ ->L[R₁] M₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_def (f g : M₁ →L[R₁] M₁) : f * g = f ∘L g :=
  rfl

@[simp, norm_cast]
/-
**ContinuousLinearMap.toLinearMap_mul** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinea
rMap`。
形式化陈述：toLinearMap_mul (f g : M₁ ->L[R₁] M₁) : (↑(f * g) : M₁ ->ₗ[R₁] M₁) = f * g
参数：f g : M₁ ->L[R₁] M₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLinearMap_mul (f g : M₁ →L[R₁] M₁) : (↑(f * g) : M₁ →ₗ[R₁] M₁) = f * g :=
  rfl

@[deprecated (since := "2026-05-20")] alias coe_mul := toLinearMap_mul

@[deprecated (since := "2026-05-20")] protected alias coe_mul' := FunLike.coe_mul

@[deprecated (since := "2026-05-20")] protected alias mul_apply := mul_apply_eq_comp
/-
**ContinuousLinearMap.monoidWithZero** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLinear
Map`。
形式化陈述：monoidWithZero : MonoidWithZero (M₁ ->L[R₁] M₁)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance monoidWithZero : MonoidWithZero (M₁ →L[R₁] M₁) :=
  fast_instance% FunLike.monoidWithZero

@[deprecated (since := "2026-07-23")] alias coe_pow' := FunLike.coe_pow_eq_iterate

@[simp, norm_cast]
/-
**ContinuousLinearMap.toLinearMap_pow** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinea
rMap`。
形式化陈述：toLinearMap_pow (f : M₁ ->L[R₁] M₁) (n : Nat) : (↑(f ^ n) : M₁ ->ₗ[R₁] M₁)
 = f ^ n
参数：f : M₁ ->L[R₁] M₁；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext'`：ext' {f g : F} (h : (f : forall a : α, β a) = (g : forall
 a : α, β a)) : f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `FunLike.coe_pow_eq_iterate`：coe_pow_eq_iterate [Monoid F'] [IsMulApplyEq
Comp F' α] [IsOneApplyEqSelf F' α] (f : F') (n : Nat) : ⇑(f ^ n) = f^[n]
· 使用定理 `ContinuousLinearMap.instIsMulApplyEqCompId`：∀ {R₁ : Type u_1} [inst : Se
miring R₁] {M₁ : Type u_4} [inst_1 : TopologicalSpace M₁] [inst_2 : AddCommMonoi
d M₁]   [inst_3 : _root_.Module …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `hom_coe_pow`：∀ {M : Type u_4} {F : Type u_5} [inst : Monoid F] (c : F → 
M → M),   c 1 = id → (∀ (f g : F), c (f * g) = c f ∘ c g) → ∀ (f : F) (n : ℕ), c
 …
-/
theorem toLinearMap_pow (f : M₁ →L[R₁] M₁) (n : ℕ) : (↑(f ^ n) : M₁ →ₗ[R₁] M₁) = f ^ n :=
  DFunLike.ext' <| (FunLike.coe_pow_eq_iterate f n).trans
    <| .symm <| hom_coe_pow _ rfl (fun _ _ ↦ rfl) _ _

@[deprecated (since := "2026-07-24")] protected alias coe_pow := toLinearMap_pow
/-
**ContinuousLinearMap.instNatCast** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLinearMap
`。
形式化陈述：instNatCast [ContinuousAdd M₁] : NatCast (M₁ ->L[R₁] M₁) where natCast n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNatCast [ContinuousAdd M₁] : NatCast (M₁ →L[R₁] M₁) where
  natCast n := n • (1 : M₁ →L[R₁] M₁)
/-
**ContinuousLinearMap.instIsNatCastApply** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLi
nearMap`。
形式化陈述：instIsNatCastApply [ContinuousAdd M₁] : IsNatCastApply (M₁ ->L[R₁] M₁) M₁ 
where natCast_apply _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instIsNatCastApply [ContinuousAdd M₁] : IsNatCastApply (M₁ →L[R₁] M₁) M₁ where
  natCast_apply _ _ := rfl
/-
**ContinuousLinearMap.semiring** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLinearMap`。
形式化陈述：semiring [ContinuousAdd M₁] : Semiring (M₁ ->L[R₁] M₁)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance semiring [ContinuousAdd M₁] : Semiring (M₁ →L[R₁] M₁) :=
  fast_instance% FunLike.semiring

/-- `ContinuousLinearMap.toLinearMap` as a `RingHom`. -/
@[simps]
/-
**ContinuousLinearMap.toLinearMapRingHom** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLi
nearMap`。
形式化陈述：toLinearMapRingHom [ContinuousAdd M₁] : (M₁ ->L[R₁] M₁) ->+* M₁ ->ₗ[R₁] M₁
 where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ContinuousLinearMap.toLinearMap` as a `RingHom`.
-/
def toLinearMapRingHom [ContinuousAdd M₁] : (M₁ →L[R₁] M₁) →+* M₁ →ₗ[R₁] M₁ where
  toFun := toLinearMap
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

@[simp]
/-
**ContinuousLinearMap.natCast_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearM
ap`。
形式化陈述：natCast_apply [ContinuousAdd M₁] (n : Nat) (m : M₁) : (↑n : M₁ ->L[R₁] M₁)
 m = n • m
参数：n : Nat；m : M₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem natCast_apply [ContinuousAdd M₁] (n : ℕ) (m : M₁) : (↑n : M₁ →L[R₁] M₁) m = n • m :=
  rfl

@[simp]
/-
**ContinuousLinearMap.ofNat_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap
`。
形式化陈述：ofNat_apply [ContinuousAdd M₁] (n : Nat) [n.AtLeastTwo] (m : M₁) : (ofNat(
n) : M₁ ->L[R₁] M₁) m = OfNat.ofNat n • m
参数：n : Nat；m : M₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofNat_apply [ContinuousAdd M₁] (n : ℕ) [n.AtLeastTwo] (m : M₁) :
    (ofNat(n) : M₁ →L[R₁] M₁) m = OfNat.ofNat n • m :=
  rfl

/-- Construct a homeomorphism from an invertible continuous linear map. -/
@[simps]
/-
**ContinuousLinearMap.homeomorphOfUnit** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLine
arMap`。
形式化陈述：homeomorphOfUnit (T : (M₁ ->L[R₁] M₁)ˣ) : M₁ ≃ₜ M₁ where toFun
参数：T : (M₁ ->L[R₁] M₁)ˣ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a homeomorphism from an invertible continuous linear map.
-/
def homeomorphOfUnit (T : (M₁ →L[R₁] M₁)ˣ) : M₁ ≃ₜ M₁ where
  toFun := T.1
  invFun := T⁻¹.1
  left_inv x := by rw [← mul_apply_eq_comp, Units.inv_mul, one_apply_eq_self]
  right_inv x := by rw [← mul_apply_eq_comp, Units.mul_inv, one_apply_eq_self]
/-
**ContinuousLinearMap.isHomeomorph_of_isUnit** 是 Mathlib 中的一个定理，位于命名空间 `Continuo
usLinearMap`。
形式化陈述：isHomeomorph_of_isUnit {T : M₁ ->L[R₁] M₁} (hT : IsUnit T) : IsHomeomorph 
T
参数：hT : IsUnit T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.isHomeomorph`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), IsHomeomorph ⇑h
-/
theorem isHomeomorph_of_isUnit {T : M₁ →L[R₁] M₁} (hT : IsUnit T) : IsHomeomorph T := by
  obtain ⟨T, rfl⟩ := hT
  exact (homeomorphOfUnit T).isHomeomorph

section ApplyAction

variable [ContinuousAdd M₁]

/-- The tautological action by `M₁ →L[R₁] M₁` on `M`.

This generalizes `Function.End.applyMulAction`. -/
/-
**ContinuousLinearMap.applyModule** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLinearMap
`。
形式化陈述：applyModule : Module (M₁ ->L[R₁] M₁) M₁
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tautological action by `M₁ →L[R₁] M₁` on `M`.

This generalizes `Function.End.applyMulAction`.
-/
instance applyModule : Module (M₁ →L[R₁] M₁) M₁ :=
  Module.compHom _ toLinearMapRingHom

@[simp]
/-
**ContinuousLinearMap.smul_def** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：∀ {R₁ : Type u_1} [inst : Semiring R₁] {M₁ : Type u_4} [inst_1 : Topologic
alSpace M₁] [inst_2 : AddCommMonoid M₁]   [inst_3 : _root_.Module R₁ M₁] [inst_4
 : ContinuousAdd M₁] (f : M₁ →L[R₁] M₁) (a : M₁), f • a = f a
参数：f : M₁ →L[R₁] M₁；a : M₁。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem smul_def (f : M₁ →L[R₁] M₁) (a : M₁) : f • a = f a :=
  rfl

/-- `ContinuousLinearMap.applyModule` is faithful. -/
/-
**ContinuousLinearMap.applyFaithfulSMul** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLin
earMap`。
形式化陈述：applyFaithfulSMul : FaithfulSMul (M₁ ->L[R₁] M₁) M₁
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g

--- 原说明 ---
`ContinuousLinearMap.applyModule` is faithful.
-/
instance applyFaithfulSMul : FaithfulSMul (M₁ →L[R₁] M₁) M₁ :=
  ⟨fun {_ _} => ContinuousLinearMap.ext⟩
/-
**ContinuousLinearMap.applySMulCommClass** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLi
nearMap`。
形式化陈述：applySMulCommClass : SMulCommClass R₁ (M₁ ->L[R₁] M₁) M₁ where smul_comm r
 e m
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearMap.map_smul`：∀ {R₁ : Type u_1} [inst : Semiring R₁] {M₁
 : Type u_4} [inst_1 : TopologicalSpace M₁] [inst_2 : AddCommMonoid M₁]   {M₂ : 
Type u_6} [inst_3 …
-/
instance applySMulCommClass : SMulCommClass R₁ (M₁ →L[R₁] M₁) M₁ where
  smul_comm r e m := (e.map_smul r m).symm
/-
**ContinuousLinearMap.applySMulCommClass'** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousL
inearMap`。
形式化陈述：applySMulCommClass' : SMulCommClass (M₁ ->L[R₁] M₁) R₁ M₁ where smul_comm
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
-/
instance applySMulCommClass' : SMulCommClass (M₁ →L[R₁] M₁) R₁ M₁ where
  smul_comm := map_smul
/-
**ContinuousLinearMap.continuousConstSMul_apply** 是 Mathlib 中的一个实例，位于命名空间 `Conti
nuousLinearMap`。
形式化陈述：continuousConstSMul_apply : ContinuousConstSMul (M₁ ->L[R₁] M₁) M₁
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
-/
instance continuousConstSMul_apply : ContinuousConstSMul (M₁ →L[R₁] M₁) M₁ :=
  ⟨ContinuousLinearMap.continuous⟩

end ApplyAction

/-
**ContinuousLinearMap.isClosed_ker** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMa
p`。
形式化陈述：isClosed_ker [T1Space M₂] (f : M₁ ->SL[σ₁₂] M₂) : IsClosed (f.ker : Set M₁
)
参数：f : M₁ ->SL[σ₁₂] M₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
· 使用定理 `isClosed_singleton`：isClosed_singleton [T1Space X] {x : X} : IsClosed ({
x} : Set X)
-/
theorem isClosed_ker [T1Space M₂] (f : M₁ →SL[σ₁₂] M₂) :
    IsClosed (f.ker : Set M₁) :=
  isClosed_singleton.preimage f.continuous
/-
**ContinuousLinearMap.isClosed_eqLocus** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLine
arMap`。
形式化陈述：isClosed_eqLocus [T2Space M₂] (f g : M₁ ->SL[σ₁₂] M₂) : IsClosed (f.eqLocu
s g : Set M₁)
参数：f g : M₁ ->SL[σ₁₂] M₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_eq`：isClosed_eq [T2Space X] {f g : Y -> X} (hf : Continuous f) 
(hg : Continuous g) : IsClosed { y : Y | f y = g y }
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
-/
theorem isClosed_eqLocus [T2Space M₂] (f g : M₁ →SL[σ₁₂] M₂) :
    IsClosed (f.eqLocus g : Set M₁) :=
  isClosed_eq f.continuous g.continuous
/-
**ContinuousLinearMap.isComplete_ker** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinear
Map`。
形式化陈述：isComplete_ker {M' : Type*} [UniformSpace M'] [CompleteSpace M'] [AddCommM
onoid M'] [Module R₁ M'] [T1Space M₂] (f : M' ->SL[σ₁₂] M₂) : IsComplete (f.ker 
: Set M')
参数：f : M' ->SL[σ₁₂] M₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.isComplete`：IsClosed.isComplete [CompleteSpace α] {s : Set α} (
h : IsClosed s) : IsComplete s
· 使用定理 `ContinuousLinearMap.isClosed_ker`：isClosed_ker [T1Space M₂] (f : M₁ ->SL
[σ₁₂] M₂) : IsClosed (f.ker : Set M₁)
-/
theorem isComplete_ker {M' : Type*} [UniformSpace M'] [CompleteSpace M'] [AddCommMonoid M']
    [Module R₁ M'] [T1Space M₂] (f : M' →SL[σ₁₂] M₂) :
    IsComplete (f.ker : Set M') :=
  (isClosed_ker f).isComplete
/-
**ContinuousLinearMap.isComplete_eqLocus** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLi
nearMap`。
形式化陈述：isComplete_eqLocus {M' : Type*} [UniformSpace M'] [CompleteSpace M'] [AddC
ommMonoid M'] [Module R₁ M'] [T2Space M₂] (f g : M' ->SL[σ₁₂] M₂) : IsComplete (
f.eqLocus g : Set M')
参数：f g : M' ->SL[σ₁₂] M₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.isComplete`：IsClosed.isComplete [CompleteSpace α] {s : Set α} (
h : IsClosed s) : IsComplete s
· 使用定理 `ContinuousLinearMap.isClosed_eqLocus`：isClosed_eqLocus [T2Space M₂] (f g
 : M₁ ->SL[σ₁₂] M₂) : IsClosed (f.eqLocus g : Set M₁)
-/
theorem isComplete_eqLocus {M' : Type*} [UniformSpace M'] [CompleteSpace M'] [AddCommMonoid M']
    [Module R₁ M'] [T2Space M₂] (f g : M' →SL[σ₁₂] M₂) :
    IsComplete (f.eqLocus g : Set M') :=
  (isClosed_eqLocus f g).isComplete
/-
**ContinuousLinearMap.completeSpace_ker** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLin
earMap`。
形式化陈述：completeSpace_ker {M' : Type*} [UniformSpace M'] [CompleteSpace M'] [AddCo
mmMonoid M'] [Module R₁ M'] [T1Space M₂] (f : M' ->SL[σ₁₂] M₂) : CompleteSpace f
.ker
参数：f : M' ->SL[σ₁₂] M₂。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsComplete.completeSpace_coe`：∀ {α : Type u} [inst : UniformSpace α] {s 
: Set α}, IsComplete s → CompleteSpace ↑s
· 使用定理 `ContinuousLinearMap.isComplete_ker`：isComplete_ker {M' : Type*} [Uniform
Space M'] [CompleteSpace M'] [AddCommMonoid M'] [Module R₁ M'] [T1Space M₂] (f :
 M' ->SL[σ₁₂] M₂) : IsCo…
-/
instance completeSpace_ker {M' : Type*} [UniformSpace M'] [CompleteSpace M']
    [AddCommMonoid M'] [Module R₁ M'] [T1Space M₂]
    (f : M' →SL[σ₁₂] M₂) : CompleteSpace f.ker :=
  (isComplete_ker f).completeSpace_coe
/-
**ContinuousLinearMap.completeSpace_eqLocus** 是 Mathlib 中的一个实例，位于命名空间 `Continuou
sLinearMap`。
形式化陈述：completeSpace_eqLocus {M' : Type*} [UniformSpace M'] [CompleteSpace M'] [A
ddCommMonoid M'] [Module R₁ M'] [T2Space M₂] (f g : M' ->SL[σ₁₂] M₂) : CompleteS
pace (f.toLinearMap.eqLocus g.toLinearMap)
参数：f g : M' ->SL[σ₁₂] M₂。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsComplete.completeSpace_coe`：∀ {α : Type u} [inst : UniformSpace α] {s 
: Set α}, IsComplete s → CompleteSpace ↑s
· 使用定理 `ContinuousLinearMap.isComplete_eqLocus`：isComplete_eqLocus {M' : Type*} 
[UniformSpace M'] [CompleteSpace M'] [AddCommMonoid M'] [Module R₁ M'] [T2Space 
M₂] (f g : M' ->SL[σ₁₂] M₂) …
-/
instance completeSpace_eqLocus {M' : Type*} [UniformSpace M'] [CompleteSpace M']
    [AddCommMonoid M'] [Module R₁ M'] [T2Space M₂]
    (f g : M' →SL[σ₁₂] M₂) : CompleteSpace (f.toLinearMap.eqLocus g.toLinearMap) :=
  (isComplete_eqLocus f g).completeSpace_coe

section

variable {R S : Type*} [Semiring R] [Semiring S] [Module R M₁] [Module R M₂] [Module R S]
  [Module S M₂] [IsScalarTower R S M₂] [TopologicalSpace S] [ContinuousSMul S M₂]

/-- The linear map `fun x => c x • f`.  Associates to a scalar-valued linear map and an element of
`M₂` the `M₂`-valued linear map obtained by multiplying the two (a.k.a. tensoring by `M₂`).
See also `ContinuousLinearMap.smulRightₗ` and `ContinuousLinearMap.smulRightL`. -/
@[simps coe]
/-
**ContinuousLinearMap.smulRight** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap`。
形式化陈述：smulRight (c : M₁ ->L[R] S) (f : M₂) : M₁ ->L[R] M₂ where toLinearMap
参数：c : M₁ ->L[R] S；f : M₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The linear map `fun x => c x • f`.  Associates to a scalar-valued linear map and
 an element of
`M₂` the `M₂`-valued linear map obtained by multiplying the two (a.k.a. tensorin
g by `M₂`).
See also `ContinuousLinearMap.smulRightₗ` and `ContinuousLinearMap.smulRightL`.
-/
def smulRight (c : M₁ →L[R] S) (f : M₂) : M₁ →L[R] M₂ where
  toLinearMap := c.toLinearMap.smulRight f

@[simp]
/-
**ContinuousLinearMap.smulRight_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinea
rMap`。
形式化陈述：smulRight_apply {c : M₁ ->L[R] S} {f : M₂} {x : M₁} : (smulRight c f : M₁ 
-> M₂) x = c x • f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smulRight_apply {c : M₁ →L[R] S} {f : M₂} {x : M₁} :
    (smulRight c f : M₁ → M₂) x = c x • f :=
  rfl

@[simp]
/-
**ContinuousLinearMap.smulRight_zero** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLinear
Map`。
形式化陈述：smulRight_zero (f : M₁ ->L[R] S) : f.smulRight (0 : M₂) = 0
参数：f : M₁ ->L[R] S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma smulRight_zero (f : M₁ →L[R] S) : f.smulRight (0 : M₂) = 0 := by ext; simp

@[simp]
/-
**ContinuousLinearMap.zero_smulRight** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinear
Map`。
形式化陈述：zero_smulRight {x : M₂} : (0 : M₁ ->L[R] S).smulRight x = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem zero_smulRight {x : M₂} : (0 : M₁ →L[R] S).smulRight x = 0 := by ext; simp

end

variable [Module R₁ M₂] [TopologicalSpace R₁] [ContinuousSMul R₁ M₂]

/-
**ContinuousLinearMap.smulRight_comp_smulRight** 是 Mathlib 中的一个定理，位于命名空间 `Contin
uousLinearMap`。
形式化陈述：smulRight_comp_smulRight {M₃ : Type*} [AddCommMonoid M₃] [Module R₁ M₃] [T
opologicalSpace M₃] [ContinuousSMul R₁ M₃] (f : M₃ ->L[R₁] R₁) (g : M₁ ->L[R₁] R
₁) {x : M₂} {y : M₃} : (smulRight f x) ∘L (smulRight g y) = smulRight g (f y • x
)
参数：f : M₃ ->L[R₁] R₁；g : M₁ ->L[R₁] R₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smulRight_comp_smulRight {M₃ : Type*} [AddCommMonoid M₃] [Module R₁ M₃]
    [TopologicalSpace M₃] [ContinuousSMul R₁ M₃] (f : M₃ →L[R₁] R₁) (g : M₁ →L[R₁] R₁) {x : M₂}
    {y : M₃} : (smulRight f x) ∘L (smulRight g y) = smulRight g (f y • x) := by
  ext
  simp
/-
**ContinuousLinearMap.range_smulRight_apply** 是 Mathlib 中的一个定理，位于命名空间 `Continuou
sLinearMap`。
形式化陈述：range_smulRight_apply {R : Type*} [DivisionSemiring R] [Module R M₁] [Modu
le R M₂] [TopologicalSpace R] [ContinuousSMul R M₂] {f : M₁ ->L[R] R} (hf : f !=
 0) (x : M₂) : range (f.smulRight x : M₁ ->ₗ[R] M₂) = Submodule.span R {x}
参数：hf : f != 0；x : M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.range_smulRight_apply`：range_smulRight_apply [DivisionSemiring
 R] [Module R M] [Module R M₁] {f : M ->ₗ[R] R} (hf : f != 0) (x : M₁) : range (
f.smulRight x) = Subm…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem range_smulRight_apply {R : Type*} [DivisionSemiring R] [Module R M₁] [Module R M₂]
    [TopologicalSpace R] [ContinuousSMul R M₂] {f : M₁ →L[R] R} (hf : f ≠ 0) (x : M₂) :
    range (f.smulRight x : M₁ →ₗ[R] M₂) = Submodule.span R {x} :=
  LinearMap.range_smulRight_apply (by simpa [coe_inj, ← toLinearMap_zero] using hf) x

section ToSpanSingleton

variable (R₁)
variable [ContinuousSMul R₁ M₁]

set_option backward.defeqAttrib.useBackward true in
/-- Given an element `x` of a topological space `M` over a semiring `R`, the natural continuous
linear map from `R` to `M` by taking multiples of `x`. -/
/-
**ContinuousLinearMap.toSpanSingleton** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinea
rMap`。
形式化陈述：toSpanSingleton (x : M₁) : R₁ ->L[R₁] M₁ where toLinearMap
参数：x : M₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an element `x` of a topological space `M` over a semiring `R`, the natural
 continuous
linear map from `R` to `M` by taking multiples of `x`.
-/
def toSpanSingleton (x : M₁) : R₁ →L[R₁] M₁ where
  toLinearMap := LinearMap.toSpanSingleton R₁ M₁ x

@[simp]
/-
**ContinuousLinearMap.toSpanSingleton_apply** 是 Mathlib 中的一个定理，位于命名空间 `Continuou
sLinearMap`。
形式化陈述：toSpanSingleton_apply (x : M₁) (r : R₁) : toSpanSingleton R₁ x r = r • x
参数：x : M₁；r : R₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toSpanSingleton_apply (x : M₁) (r : R₁) : toSpanSingleton R₁ x r = r • x :=
  rfl

@[simp]
/-
**ContinuousLinearMap.toSpanSingleton_zero** 是 Mathlib 中的一个定理，位于命名空间 `Continuous
LinearMap`。
形式化陈述：toSpanSingleton_zero : toSpanSingleton R₁ (0 : M₁) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext_ring`：ext_ring [TopologicalSpace R₁] {f g : R₁ -
>L[R₁] M₁} (h : f 1 = g 1) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toSpanSingleton_zero : toSpanSingleton R₁ (0 : M₁) = 0 := by ext; simp
/-
**ContinuousLinearMap.toSpanSingleton_apply_one** 是 Mathlib 中的一个定理，位于命名空间 `Conti
nuousLinearMap`。
形式化陈述：toSpanSingleton_apply_one (x : M₁) : toSpanSingleton R₁ x 1 = x
参数：x : M₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem toSpanSingleton_apply_one (x : M₁) : toSpanSingleton R₁ x 1 = x :=
  one_smul _ _
/-
**ContinuousLinearMap.toSpanSingleton_apply_map_one** 是 Mathlib 中的一个定理，位于命名空间 `C
ontinuousLinearMap`。
形式化陈述：∀ (R₁ : Type u_1) [inst : Semiring R₁] {M₂ : Type u_6} [inst_1 : Topologic
alSpace M₂] [inst_2 : AddCommMonoid M₂]   [inst_3 : _root_.Module R₁ M₂] [inst_4
 : TopologicalSpace R₁] [inst_5 : ContinuousSMul R₁ M₂] (c : R₁ →L[R₁] M₂),   Co
ntinuousLinearMap.toSpanSingleton R₁ (c 1) = c
参数：R₁ : Type u_1；c : R₁ →L[R₁] M₂；c 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext_ring`：ext_ring [TopologicalSpace R₁] {f g : R₁ -
>L[R₁] M₁} (h : f 1 = g 1) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul'`：∀ {M : Type u_8} [inst : AddCom
mMonoid M] {R : Type u_14} {S : Type u_15} [inst_1 : Semiring S] [inst_2 : SMul 
R M]   [inst_3 : _root_.Modul…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem toSpanSingleton_apply_map_one (c : R₁ →L[R₁] M₂) :
    toSpanSingleton R₁ (c 1) = c := by
  ext
  simp [← ContinuousLinearMap.map_smul_of_tower]
/-
**ContinuousLinearMap.toSpanSingleton_add** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousL
inearMap`。
形式化陈述：toSpanSingleton_add [ContinuousAdd M₁] (x y : M₁) : toSpanSingleton R₁ (x 
+ y) = toSpanSingleton R₁ x + toSpanSingleton R₁ y
参数：x y : M₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ContinuousLinearMap.coe_inj`：coe_inj {f g : M₁ ->SL[σ₁₂] M₂} : (f : M₁ -
>ₛₗ[σ₁₂] M₂) = g ↔ f = g
· 使用引理 `LinearMap.toSpanSingleton_add`：toSpanSingleton_add (x y : M) : toSpanSin
gleton R M (x + y) = toSpanSingleton R M x + toSpanSingleton R M y
-/
theorem toSpanSingleton_add [ContinuousAdd M₁] (x y : M₁) :
    toSpanSingleton R₁ (x + y) = toSpanSingleton R₁ x + toSpanSingleton R₁ y :=
  coe_inj.mp <| LinearMap.toSpanSingleton_add _ _
/-
**ContinuousLinearMap.toSpanSingleton_smul** 是 Mathlib 中的一个定理，位于命名空间 `Continuous
LinearMap`。
形式化陈述：toSpanSingleton_smul {α} [Monoid α] [DistribMulAction α M₁] [ContinuousCon
stSMul α M₁] [SMulCommClass R₁ α M₁] (c : α) (x : M₁) : toSpanSingleton R₁ (c • 
x) = c • toSpanSingleton R₁ x
参数：c : α；x : M₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ContinuousLinearMap.coe_inj`：coe_inj {f g : M₁ ->SL[σ₁₂] M₂} : (f : M₁ -
>ₛₗ[σ₁₂] M₂) = g ↔ f = g
· 使用定理 `LinearMap.toSpanSingleton_smul`：toSpanSingleton_smul {S : Type*} [Monoid
 S] [DistribMulAction S M] [SMulCommClass R S M] (r : S) (x : M) : toSpanSinglet
on R M (r • x) = r •…
-/
theorem toSpanSingleton_smul {α} [Monoid α] [DistribMulAction α M₁] [ContinuousConstSMul α M₁]
    [SMulCommClass R₁ α M₁] (c : α) (x : M₁) :
    toSpanSingleton R₁ (c • x) = c • toSpanSingleton R₁ x :=
  coe_inj.mp <| LinearMap.toSpanSingleton_smul _ _
/-
**ContinuousLinearMap.smulRight_id** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMa
p`。
形式化陈述：smulRight_id : smulRight (.id R₁ R₁) = toSpanSingleton R₁ (M₁
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smulRight_id : smulRight (.id R₁ R₁) = toSpanSingleton R₁ (M₁ := M₁) := rfl
/-
**ContinuousLinearMap.smulRight_one_eq_toSpanSingleton** 是 Mathlib 中的一个定理，位于命名空间
 `ContinuousLinearMap`。
形式化陈述：smulRight_one_eq_toSpanSingleton (x : M₁) : (1 : R₁ ->L[R₁] R₁).smulRight 
x = toSpanSingleton R₁ x
参数：x : M₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smulRight_one_eq_toSpanSingleton (x : M₁) :
    (1 : R₁ →L[R₁] R₁).smulRight x = toSpanSingleton R₁ x :=
  rfl

@[simp]
/-
**ContinuousLinearMap.toLinearMap_toSpanSingleton** 是 Mathlib 中的一个定理，位于命名空间 `Con
tinuousLinearMap`。
形式化陈述：toLinearMap_toSpanSingleton (x : M₁) : (toSpanSingleton R₁ x).toLinearMap 
= LinearMap.toSpanSingleton R₁ M₁ x
参数：x : M₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLinearMap_toSpanSingleton (x : M₁) :
    (toSpanSingleton R₁ x).toLinearMap = LinearMap.toSpanSingleton R₁ M₁ x := rfl

variable {R₁}
/-
**ContinuousLinearMap.comp_toSpanSingleton** 是 Mathlib 中的一个定理，位于命名空间 `Continuous
LinearMap`。
形式化陈述：comp_toSpanSingleton (f : M₁ ->L[R₁] M₂) (x : M₁) : f ∘L toSpanSingleton R
₁ x = toSpanSingleton R₁ (f x)
参数：f : M₁ ->L[R₁] M₂；x : M₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ContinuousLinearMap.coe_inj`：coe_inj {f g : M₁ ->SL[σ₁₂] M₂} : (f : M₁ -
>ₛₗ[σ₁₂] M₂) = g ↔ f = g
· 使用定理 `LinearMap.comp_toSpanSingleton`：comp_toSpanSingleton [AddCommMonoid M₂] 
[Module R M₂] (f : M ->ₗ[R] M₂) (x : M) : f ∘ₗ toSpanSingleton R M x = toSpanSin
gleton R M₂ (f x)
-/
theorem comp_toSpanSingleton (f : M₁ →L[R₁] M₂) (x : M₁) :
    f ∘L toSpanSingleton R₁ x = toSpanSingleton R₁ (f x) :=
  coe_inj.mp <| LinearMap.comp_toSpanSingleton _ _

omit [ContinuousSMul R₁ M₁] in
/-
**ContinuousLinearMap.toSpanSingleton_comp** 是 Mathlib 中的一个定理，位于命名空间 `Continuous
LinearMap`。
形式化陈述：toSpanSingleton_comp (f : M₁ ->L[R₁] R₁) (g : M₂) : toSpanSingleton R₁ g ∘
L f = f.smulRight g
参数：f : M₁ ->L[R₁] R₁；g : M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toSpanSingleton_comp (f : M₁ →L[R₁] R₁) (g : M₂) :
    toSpanSingleton R₁ g ∘L f = f.smulRight g := rfl
/-
**ContinuousLinearMap.toSpanSingleton_inj** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousL
inearMap`。
形式化陈述：∀ {R₁ : Type u_1} [inst : Semiring R₁] {M₂ : Type u_6} [inst_1 : Topologic
alSpace M₂] [inst_2 : AddCommMonoid M₂]   [inst_3 : _root_.Module R₁ M₂] [inst_4
 : TopologicalSpace R₁] [inst_5 : ContinuousSMul R₁ M₂] {f f' : M₂},   Continuou
sLinearMap.toSpanSingleton R₁ f = ContinuousLinearMap.toSpanSingleton R₁ f' ↔ f 
= f'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] theorem toSpanSingleton_inj {f f' : M₂} :
    toSpanSingleton R₁ f = toSpanSingleton R₁ f' ↔ f = f' := by
  simp [ContinuousLinearMap.ext_ring_iff]
/-
**ContinuousLinearMap.toSpanSingleton_comp_toSpanSingleton** 是 Mathlib 中的一个定理，位于
命名空间 `ContinuousLinearMap`。
形式化陈述：toSpanSingleton_comp_toSpanSingleton [ContinuousMul R₁] {x : M₂} {c : R₁} 
: (toSpanSingleton R₁ x) ∘L (toSpanSingleton R₁ c) = toSpanSingleton R₁ (c • x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.smulRight_comp_smulRight`：smulRight_comp_smulRight {
M₃ : Type*} [AddCommMonoid M₃] [Module R₁ M₃] [TopologicalSpace M₃] [ContinuousS
Mul R₁ M₃] (f : M₃ ->L[R₁] R₁) (g …
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
  [AddCommGroup M₄] [Module R M] [Module R₂ M₂] [Module R₃ M₃] {σ₁₂ : R →+* R₂} {σ₂₃ : R₂ →+* R₃}
  {σ₁₃ : R →+* R₃}

section

/-
**ContinuousLinearMap.map_neg** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] {R₂ : Type u_2} [inst_1 : Ring R₂] {M : T
ype u_4} [inst_2 : TopologicalSpace M]   [inst_3 : AddCommGroup M] {M₂ : Type u_
5} [inst_4 : TopologicalSpace M₂] [inst_5 : AddCommGroup M₂]   [inst_6 : _root_.
Module R M] [inst_7 : _root_.Module R₂ M₂] {σ₁₂ : R →+* R₂} (f : M →SL[σ₁₂] M₂) 
(x : M),   f (-x) = -f x
参数：f : M →SL[σ₁₂] M₂；x : M；-x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
-/
protected theorem map_neg (f : M →SL[σ₁₂] M₂) (x : M) : f (-x) = -f x := by
  exact map_neg f x
/-
**ContinuousLinearMap.map_sub** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] {R₂ : Type u_2} [inst_1 : Ring R₂] {M : T
ype u_4} [inst_2 : TopologicalSpace M]   [inst_3 : AddCommGroup M] {M₂ : Type u_
5} [inst_4 : TopologicalSpace M₂] [inst_5 : AddCommGroup M₂]   [inst_6 : _root_.
Module R M] [inst_7 : _root_.Module R₂ M₂] {σ₁₂ : R →+* R₂} (f : M →SL[σ₁₂] M₂) 
(x y : M),   f (x - y) = f x - f y
参数：f : M →SL[σ₁₂] M₂；x y : M；x - y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
-/
protected theorem map_sub (f : M →SL[σ₁₂] M₂) (x y : M) : f (x - y) = f x - f y := by
  exact map_sub f x y

@[simp]
/-
**ContinuousLinearMap.sub_apply'** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`
。
形式化陈述：sub_apply' (f g : M ->SL[σ₁₂] M₂) (x : M) : ((f : M ->ₛₗ[σ₁₂] M₂) - g) x =
 f x - g x
参数：f g : M ->SL[σ₁₂] M₂；x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sub_apply' (f g : M →SL[σ₁₂] M₂) (x : M) : ((f : M →ₛₗ[σ₁₂] M₂) - g) x = f x - g x :=
  rfl

end

section

variable [IsTopologicalAddGroup M₂]

/-
**ContinuousLinearMap.neg** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLinearMap`。
形式化陈述：neg : Neg (M ->SL[σ₁₂] M₂)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance neg : Neg (M →SL[σ₁₂] M₂) :=
  ⟨fun f => ⟨-f, f.2.neg⟩⟩
/-
**ContinuousLinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsNegApply (M →SL[σ₁₂] M₂) M M₂ where
  neg_apply _ _ := rfl

@[simp, norm_cast]
/-
**ContinuousLinearMap.toLinearMap_neg** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinea
rMap`。
形式化陈述：toLinearMap_neg (f : M ->SL[σ₁₂] M₂) : (↑(-f) : M ->ₛₗ[σ₁₂] M₂) = -f
参数：f : M ->SL[σ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLinearMap_neg (f : M →SL[σ₁₂] M₂) : (↑(-f) : M →ₛₗ[σ₁₂] M₂) = -f :=
  rfl

@[deprecated (since := "2026-05-20")] protected alias neg_apply := _root_.neg_apply

@[deprecated (since := "2026-05-20")] protected alias coe_neg := toLinearMap_neg

@[deprecated (since := "2026-05-20")] alias coe_neg' := FunLike.coe_neg

@[simp, norm_cast]
/-
**ContinuousLinearMap.toContinuousAddMonoidHom_neg** 是 Mathlib 中的一个定理，位于命名空间 `Co
ntinuousLinearMap`。
形式化陈述：toContinuousAddMonoidHom_neg (f : M ->SL[σ₁₂] M₂) : ↑(-f) = -(f : Continuo
usAddMonoidHom M M₂)
参数：f : M ->SL[σ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `ContinuousSemilinearMapClass.toContinuousMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
-/
theorem toContinuousAddMonoidHom_neg (f : M →SL[σ₁₂] M₂) :
    ↑(-f) = -(f : ContinuousAddMonoidHom M M₂) := rfl
/-
**ContinuousLinearMap.sub** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLinearMap`。
形式化陈述：sub : Sub (M ->SL[σ₁₂] M₂)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance sub : Sub (M →SL[σ₁₂] M₂) :=
  ⟨fun f g => ⟨f - g, f.2.sub g.2⟩⟩
/-
**ContinuousLinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsSubApply (M →SL[σ₁₂] M₂) M M₂ where
  sub_apply _ _ _ := rfl
/-
**ContinuousLinearMap.addCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLinearMa
p`。
形式化陈述：addCommGroup : AddCommGroup (M ->SL[σ₁₂] M₂)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addCommGroup : AddCommGroup (M →SL[σ₁₂] M₂) := fast_instance% FunLike.addCommGroup

@[simp, norm_cast]
/-
**ContinuousLinearMap.toLinearMap_sub** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinea
rMap`。
形式化陈述：toLinearMap_sub (f g : M ->SL[σ₁₂] M₂) : (↑(f - g) : M ->ₛₗ[σ₁₂] M₂) = f -
 g
参数：f g : M ->SL[σ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLinearMap_sub (f g : M →SL[σ₁₂] M₂) : (↑(f - g) : M →ₛₗ[σ₁₂] M₂) = f - g :=
  rfl

@[deprecated (since := "2026-05-20")] protected alias sub_apply := _root_.sub_apply

@[deprecated (since := "2026-05-20")] protected alias coe_sub := toLinearMap_sub

@[deprecated (since := "2026-05-20")] alias coe_sub' := FunLike.coe_sub

@[simp, norm_cast]
/-
**ContinuousLinearMap.toContinuousAddMonoidHom_sub** 是 Mathlib 中的一个定理，位于命名空间 `Co
ntinuousLinearMap`。
形式化陈述：toContinuousAddMonoidHom_sub (f g : M ->SL[σ₁₂] M₂) : ↑(f - g) = (f - g : 
ContinuousAddMonoidHom M M₂)
参数：f g : M ->SL[σ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `ContinuousSemilinearMapClass.toContinuousMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
-/
theorem toContinuousAddMonoidHom_sub (f g : M →SL[σ₁₂] M₂) :
    ↑(f - g) = (f - g : ContinuousAddMonoidHom M M₂) := rfl

end

@[simp]
/-
**ContinuousLinearMap.comp_neg** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：comp_neg [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [IsTopologicalAddGroup M₂] [IsTop
ologicalAddGroup M₃] (g : M₂ ->SL[σ₂₃] M₃) (f : M ->SL[σ₁₂] M₂) : g ∘SL (-f) = -
g ∘SL f
参数：g : M₂ ->SL[σ₂₃] M₃；f : M ->SL[σ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Neg β}   {inst_2 : Neg F} [self : IsNe…
· 使用定理 `ContinuousLinearMap.instIsNegApply`：∀ {R : Type u_1} [inst : Ring R] {R₂
 : Type u_2} [inst_1 : Ring R₂] {M : Type u_4} [inst_2 : TopologicalSpace M]   [
inst_3 : AddCommGroup M]…
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comp_neg [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [IsTopologicalAddGroup M₂]
    [IsTopologicalAddGroup M₃] (g : M₂ →SL[σ₂₃] M₃) (f : M →SL[σ₁₂] M₂) :
    g ∘SL (-f) = -g ∘SL f := by
  ext x
  simp

@[simp]
/-
**ContinuousLinearMap.neg_comp** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：neg_comp [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [IsTopologicalAddGroup M₃] (g : M
₂ ->SL[σ₂₃] M₃) (f : M ->SL[σ₁₂] M₂) : (-g) ∘SL f = -g ∘SL f
参数：g : M₂ ->SL[σ₂₃] M₃；f : M ->SL[σ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Neg β}   {inst_2 : Neg F} [self : IsNe…
· 使用定理 `ContinuousLinearMap.instIsNegApply`：∀ {R : Type u_1} [inst : Ring R] {R₂
 : Type u_2} [inst_1 : Ring R₂] {M : Type u_4} [inst_2 : TopologicalSpace M]   [
inst_3 : AddCommGroup M]…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem neg_comp [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [IsTopologicalAddGroup M₃] (g : M₂ →SL[σ₂₃] M₃)
    (f : M →SL[σ₁₂] M₂) : (-g) ∘SL f = -g ∘SL f := by
  ext
  simp

@[simp]
/-
**ContinuousLinearMap.comp_sub** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：comp_sub [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [IsTopologicalAddGroup M₂] [IsTop
ologicalAddGroup M₃] (g : M₂ ->SL[σ₂₃] M₃) (f₁ f₂ : M ->SL[σ₁₂] M₂) : g ∘SL (f₁ 
- f₂) = g ∘SL f₁ - g ∘SL f₂
参数：g : M₂ ->SL[σ₂₃] M₃；f₁ f₂ : M ->SL[σ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Sub β}   {inst_2 : Sub F} [self : IsSu…
· 使用定理 `ContinuousLinearMap.instIsSubApply`：∀ {R : Type u_1} [inst : Ring R] {R₂
 : Type u_2} [inst_1 : Ring R₂] {M : Type u_4} [inst_2 : TopologicalSpace M]   [
inst_3 : AddCommGroup M]…
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comp_sub [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [IsTopologicalAddGroup M₂]
    [IsTopologicalAddGroup M₃] (g : M₂ →SL[σ₂₃] M₃) (f₁ f₂ : M →SL[σ₁₂] M₂) :
    g ∘SL (f₁ - f₂) = g ∘SL f₁ - g ∘SL f₂ := by
  ext
  simp

@[simp]
/-
**ContinuousLinearMap.sub_comp** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：sub_comp [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [IsTopologicalAddGroup M₃] (g₁ g₂
 : M₂ ->SL[σ₂₃] M₃) (f : M ->SL[σ₁₂] M₂) : (g₁ - g₂) ∘SL f = g₁ ∘SL f - g₂ ∘SL f
参数：g₁ g₂ : M₂ ->SL[σ₂₃] M₃；f : M ->SL[σ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Sub β}   {inst_2 : Sub F} [self : IsSu…
· 使用定理 `ContinuousLinearMap.instIsSubApply`：∀ {R : Type u_1} [inst : Ring R] {R₂
 : Type u_2} [inst_1 : Ring R₂] {M : Type u_4} [inst_2 : TopologicalSpace M]   [
inst_3 : AddCommGroup M]…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sub_comp [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [IsTopologicalAddGroup M₃] (g₁ g₂ : M₂ →SL[σ₂₃] M₃)
    (f : M →SL[σ₁₂] M₂) : (g₁ - g₂) ∘SL f = g₁ ∘SL f - g₂ ∘SL f := by
  ext
  simp
/-
**ContinuousLinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsTopologicalAddGroup M] : IntCast (M →L[R] M) where
  intCast z := z • (1 : M →L[R] M)
/-
**ContinuousLinearMap.instIsIntCastApply** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLi
nearMap`。
形式化陈述：instIsIntCastApply [IsTopologicalAddGroup M] : IsIntCastApply (M ->L[R] M)
 M where intCast_apply _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instIsIntCastApply [IsTopologicalAddGroup M] : IsIntCastApply (M →L[R] M) M where
  intCast_apply _ _ := rfl

@[deprecated (since := "2026-05-20")] alias intCast_apply := _root_.intCast_apply
/-
**ContinuousLinearMap.ring** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLinearMap`。
形式化陈述：ring [IsTopologicalAddGroup M] : Ring (M ->L[R] M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance ring [IsTopologicalAddGroup M] : Ring (M →L[R] M) := fast_instance% FunLike.ring
/-
**ContinuousLinearMap.toSpanSingleton_pow** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousL
inearMap`。
形式化陈述：toSpanSingleton_pow [TopologicalSpace R] [IsTopologicalRing R] (c : R) (n 
: Nat) : toSpanSingleton R c ^ n = toSpanSingleton R (c ^ n)
参数：c : R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `ContinuousLinearMap.ext_ring`：ext_ring [TopologicalSpace R₁] {f g : R₁ -
>L[R₁] M₁} (h : f 1 = g 1) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_apply_eq_self`：∀ {F : Type u_1} {α : outParam (Type u_2)} {inst : Fu
nLike F α α} {inst_1 : One F} [self : IsOneApplyEqSelf F α]   (x : α), 1 x = x
· 使用定理 `ContinuousLinearMap.toSpanSingleton.congr_simp`：∀ (R₁ : Type u_1) [inst 
: Semiring R₁] {M₁ : Type u_4} [inst_1 : TopologicalSpace M₁] [inst_2 : AddCommM
onoid M₁]   [inst_3 : _root_.Module …
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `ContinuousLinearMap.mul_def`：mul_def (f g : M₁ ->L[R₁] M₁) : f * g = f ∘
L g
· 使用定理 `ContinuousLinearMap.toSpanSingleton_comp_toSpanSingleton`：toSpanSingleto
n_comp_toSpanSingleton [ContinuousMul R₁] {x : M₂} {c : R₁} : (toSpanSingleton R
₁ x) ∘L (toSpanSingleton R₁ c) = toSpanSinglet…
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
-/
theorem toSpanSingleton_pow [TopologicalSpace R] [IsTopologicalRing R] (c : R) (n : ℕ) :
    toSpanSingleton R c ^ n = toSpanSingleton R (c ^ n) := by
  induction n with
  | zero => ext; simp
  | succ n ihn =>
    rw [pow_succ, ihn, mul_def, toSpanSingleton_comp_toSpanSingleton, smul_eq_mul, pow_succ']

end Ring

section DivisionRing

variable {R M : Type*}

/-- A nonzero continuous linear functional is open. -/
/-
**ContinuousLinearMap.isOpenMap_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Continuous
LinearMap`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : TopologicalSpace R] [inst_1 : Divi
sionRing R] [ContinuousSub R]   [inst_3 : AddCommGroup M] [inst_4 : TopologicalS
pace M] [ContinuousAdd M] [inst_6 : _root_.Module R M]   [ContinuousSMul R M] (f
 : StrongDual R M), f ≠ 0 → IsOpenMap ⇑f
参数：f : StrongDual R M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.exists_ne_zero`：exists_ne_zero {f : M₁ ->SL[σ₁₂] M₂}
 (hf : f != 0) : exists x, f x != 0
· 使用定理 `IsOpenMap.of_sections`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   (∀ (x : X), ∃ g, Continu
ousAt g (f …
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `Continuous.const_add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst
_1 : Add M] [SeparatelyContinuousAdd M] {X : Type u_2}   [inst_3 : TopologicalSp
ace X] {f …
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `Continuous.fun_smul`：∀ {M : Type u_1} {X : Type u_2} {Y : Type u_3} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X]   [inst_2 : TopologicalSpa
ce Y] [in…
· 使用定理 `Continuous.fun_sub`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f g 
: X → G}…
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b

--- 原说明 ---
A nonzero continuous linear functional is open.
-/
protected theorem isOpenMap_of_ne_zero [TopologicalSpace R] [DivisionRing R] [ContinuousSub R]
    [AddCommGroup M] [TopologicalSpace M] [ContinuousAdd M] [Module R M] [ContinuousSMul R M]
    (f : StrongDual R M) (hf : f ≠ 0) : IsOpenMap f :=
  let ⟨x, hx⟩ := exists_ne_zero hf
  IsOpenMap.of_sections fun y =>
    ⟨fun a => y + (a - f y) • (f x)⁻¹ • x, Continuous.continuousAt <| by fun_prop, by simp,
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
  [DistribMulAction S N₃] [SMulCommClass R S N₃] [ContinuousConstSMul S N₃] {σ₁₂ : R →+* R₂}
  {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

@[simp]
/-
**ContinuousLinearMap.smul_comp** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：smul_comp (c : S₃) (h : M₂ ->SL[σ₂₃] M₃) (f : M ->SL[σ₁₂] M₂) : (c • h) ∘S
L f = c • h ∘SL f
参数：c : S₃；h : M₂ ->SL[σ₂₃] M₃；f : M ->SL[σ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_comp (c : S₃) (h : M₂ →SL[σ₂₃] M₃) (f : M →SL[σ₁₂] M₂) :
    (c • h) ∘SL f = c • h ∘SL f :=
  rfl

variable [DistribMulAction S₃ M₂] [ContinuousConstSMul S₃ M₂] [SMulCommClass R₂ S₃ M₂]
variable [DistribMulAction S N₂] [ContinuousConstSMul S N₂] [SMulCommClass R S N₂]

@[simp]
/-
**ContinuousLinearMap.comp_smul** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：comp_smul [LinearMap.CompatibleSMul N₂ N₃ S R] (hₗ : N₂ ->L[R] N₃) (c : S)
 (fₗ : M ->L[R] N₂) : hₗ ∘L (c • fₗ) = c • hₗ ∘L fₗ
参数：hₗ : N₂ ->L[R] N₃；c : S；fₗ : M ->L[R] N₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `ContinuousLinearMap.map_smul_of_tower`：map_smul_of_tower {R S : Type*} [
Semiring S] [SMul R M₁] [Module S M₁] [SMul R M₂] [Module S M₂] [LinearMap.Compa
tibleSMul M₁ M₂ R S] (f : M…
-/
theorem comp_smul [LinearMap.CompatibleSMul N₂ N₃ S R] (hₗ : N₂ →L[R] N₃) (c : S)
    (fₗ : M →L[R] N₂) : hₗ ∘L (c • fₗ) = c • hₗ ∘L fₗ := by
  ext x
  exact hₗ.map_smul_of_tower c (fₗ x)

@[simp]
/-
**ContinuousLinearMap.comp_smul** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：comp_smul [LinearMap.CompatibleSMul N₂ N₃ S R] (hₗ : N₂ ->L[R] N₃) (c : S)
 (fₗ : M ->L[R] N₂) : hₗ ∘L (c • fₗ) = c • hₗ ∘L fₗ
参数：hₗ : N₂ ->L[R] N₃；c : S；fₗ : M ->L[R] N₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `ContinuousLinearMap.map_smul_of_tower`：map_smul_of_tower {R S : Type*} [
Semiring S] [SMul R M₁] [Module S M₁] [SMul R M₂] [Module S M₂] [LinearMap.Compa
tibleSMul M₁ M₂ R S] (f : M…
-/
theorem comp_smulₛₗ [SMulCommClass R₂ R₂ M₂] [SMulCommClass R₃ R₃ M₃] [ContinuousConstSMul R₂ M₂]
    [ContinuousConstSMul R₃ M₃] (h : M₂ →SL[σ₂₃] M₃) (c : R₂) (f : M →SL[σ₁₂] M₂) :
    h ∘SL (c • f) = σ₂₃ c • h ∘SL f := by
  ext x
  simp
/-
**ContinuousLinearMap.distribMulAction** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLine
arMap`。
形式化陈述：distribMulAction [ContinuousAdd M₂] : DistribMulAction S₃ (M ->SL[σ₁₂] M₂)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance distribMulAction [ContinuousAdd M₂] : DistribMulAction S₃ (M →SL[σ₁₂] M₂) :=
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
  {σ₁₂ : R →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] (c : S)
  (h : M₂ →SL[σ₂₃] M₃) (f : M →SL[σ₁₂] M₂)

variable [ContinuousAdd M₂] [ContinuousAdd M₃] [ContinuousAdd N₂]

/-
**ContinuousLinearMap.module** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLinearMap`。
形式化陈述：module : Module S₃ (M ->SL[σ₁₃] M₃)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance module : Module S₃ (M →SL[σ₁₃] M₃) := fast_instance% FunLike.module
/-
**ContinuousLinearMap.isCentralScalar** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLinea
rMap`。
形式化陈述：isCentralScalar [Module S₃ᵐᵒᵖ M₃] [IsCentralScalar S₃ M₃] : IsCentralScala
r S₃ (M ->SL[σ₁₃] M₃)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `FunLike.isCentralScalar`：∀ {M : Type u_1} {F : Type u_3} {α : Type u_4} 
{β : Type u_5} [i : FunLike F α β] [inst : SMul M F]   [inst_1 : SMul Mᵐᵒᵖ F] [i
nst_2 : SMul …
· 使用定理 `SMulCommClass.op_right`：∀ {M : Type u_1} {N : Type u_2} {α : Type u_5} [
inst : SMul M α] [inst_1 : SMul N α] [inst_2 : SMul Nᵐᵒᵖ α]   [IsCentralScalar N
 α] [SMulCom…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
-/
instance isCentralScalar [Module S₃ᵐᵒᵖ M₃] [IsCentralScalar S₃ M₃] :
    IsCentralScalar S₃ (M →SL[σ₁₃] M₃) := FunLike.isCentralScalar

variable (S) [ContinuousAdd N₃]

/-- The coercion from `M →L[R] M₂` to `M →ₗ[R] M₂`, as a linear map. -/
@[simps]
/-
**ContinuousLinearMap.coeLM** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap`。
形式化陈述：coeLM : (M ->L[R] N₃) ->ₗ[S] M ->ₗ[R] N₃ where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The coercion from `M →L[R] M₂` to `M →ₗ[R] M₂`, as a linear map.
-/
def coeLM : (M →L[R] N₃) →ₗ[S] M →ₗ[R] N₃ where
  toFun := (↑)
  map_add' f g := toLinearMap_add f g
  map_smul' c f := toLinearMap_smul c f

variable {S} (σ₁₃)

/-- The coercion from `M →SL[σ] M₂` to `M →ₛₗ[σ] M₂`, as a linear map. -/
@[simps]
/-
**ContinuousLinearMap.coeLM** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap`。
形式化陈述：coeLM : (M ->L[R] N₃) ->ₗ[S] M ->ₗ[R] N₃ where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The coercion from `M →SL[σ] M₂` to `M →ₛₗ[σ] M₂`, as a linear map.
-/
def coeLMₛₗ : (M →SL[σ₁₃] M₃) →ₗ[S₃] M →ₛₗ[σ₁₃] M₃ where
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
/-
**ContinuousLinearMap.lcomp** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap`。
形式化陈述：lcomp (f : U ->L[R] V) : (V ->L[R] W) ->ₗ[R] (U ->L[R] W) where toFun l
参数：f : U ->L[R] V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of continuous linear maps, as a linear map. Compare `LinearMap.lcomp
`.
-/
def lcomp (f : U →L[R] V) : (V →L[R] W) →ₗ[R] (U →L[R] W) where
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
/-
**ContinuousLinearMap.llcomp** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap`。
形式化陈述：llcomp : (U ->L[R] V) ->ₗ[R] (V ->L[R] W) ->ₗ[R] (U ->L[R] W) where toFun 
l
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of continuous linear maps, as a bilinear map. Compare `LinearMap.llc
omp`.
-/
def llcomp : (U →L[R] V) →ₗ[R] (V →L[R] W) →ₗ[R] (U →L[R] W) where
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
/-
**ContinuousLinearMap.toSpanSingletonLE** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLin
earMap`。
形式化陈述：toSpanSingletonLE : M ≃ₗ[S] (R ->L[R] M) where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.toSpanSingleton_add`：toSpanSingleton_add [Continuous
Add M₁] (x y : M₁) : toSpanSingleton R₁ (x + y) = toSpanSingleton R₁ x + toSpanS
ingleton R₁ y

--- 原说明 ---
`ContinuousLinearMap.toSpanSingleton` as a linear equivalence. See
`ContinuousLinearMap.toSpanSingletonLIE` for the isometric version
and `ContinuousLinearMap.toSpanSingletonCLE` for the continuous version.
-/
def toSpanSingletonLE : M ≃ₗ[S] (R →L[R] M) where
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

/-- Given `c : E →L[R] S`, `c.smulRightₗ` is the linear map from `F` to `E →L[R] F`
sending `f` to `fun e => c e • f`. See also `ContinuousLinearMap.smulRightL`. -/
/-
**ContinuousLinearMap.smulRight** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap`。
形式化陈述：smulRight (c : M₁ ->L[R] S) (f : M₂) : M₁ ->L[R] M₂ where toLinearMap
参数：c : M₁ ->L[R] S；f : M₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `c : E →L[R] S`, `c.smulRightₗ` is the linear map from `F` to `E →L[R] F`
sending `f` to `fun e => c e • f`. See also `ContinuousLinearMap.smulRightL`.
-/
def smulRightₗ (c : M →L[R] S) : M₂ →ₗ[T] M →L[R] M₂ where
  toFun := c.smulRight
  map_add' x y := by
    ext e
    apply smul_add (c e)
  map_smul' a x := by
    ext e
    dsimp
    apply smul_comm

@[simp]
/-
**ContinuousLinearMap.coe_smulRight** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearM
ap`。
形式化陈述：∀ {M₁ : Type u_4} [inst : TopologicalSpace M₁] [inst_1 : AddCommMonoid M₁]
 {M₂ : Type u_6}   [inst_2 : TopologicalSpace M₂] [inst_3 : AddCommMonoid M₂] {R
 : Type u_9} {S : Type u_10} [inst_4 : Semiring R]   [inst_5 : Semiring S] [inst
_6 : _root_.Module R M₁] [inst_7 : _root_.Module R M₂] [inst_8 : _root_.Module R
 S]   [inst_9 : _root_.Module S M₂] [inst_10 : IsScalarTower R S M₂] [inst_11 : 
TopologicalSpace S]   [inst_12 : ContinuousSMul S M₂] (c : M₁ →L[R] S) (f : M₂),
 ↑(c.smulRight f) = (↑c).smulRight f
参数：c : M₁ →L[R] S；f : M₂；c.smulRight f；↑c。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_smulRightₗ (c : M →L[R] S) : ⇑(smulRightₗ c : M₂ →ₗ[T] M →L[R] M₂) = c.smulRight :=
  rfl

end SMulRightₗ

section Semiring
variable {R S M : Type*} [Semiring R] [TopologicalSpace M] [AddCommGroup M] [Module R M]
  [CommSemiring S] [Module S M] [SMulCommClass R S M] [SMul S R] [IsScalarTower S R M]
  [ContinuousConstSMul S M] [IsTopologicalAddGroup M]

/-
**ContinuousLinearMap.algebra** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLinearMap`。
形式化陈述：algebra : Algebra S (M ->L[R] M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance algebra : Algebra S (M →L[R] M) :=
  Algebra.ofModule smul_comp fun _ _ _ => comp_smul _ _ _
/-
**ContinuousLinearMap.algebraMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLine
arMap`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} {M : Type u_3} [inst : Semiring R] [inst_1
 : TopologicalSpace M]   [inst_2 : AddCommGroup M] [inst_3 : _root_.Module R M] 
[inst_4 : CommSemiring S] [inst_5 : _root_.Module S M]   [inst_6 : SMulCommClass
 R S M] [inst_7 : SMul S R] [inst_8 : IsScalarTower S R M] [inst_9 : ContinuousC
onstSMul S M]   [inst_10 : IsTopologicalAddGroup M] (r : S) (m : M), ((algebraMa
p S (M →L[R] M)) r) m = r • m
参数：r : S；m : M；(algebraMap S (M →L[R] M)) r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
-/
@[simp] theorem algebraMap_apply (r : S) (m : M) : algebraMap S (M →L[R] M) r m = r • m := rfl

end Semiring

end ContinuousLinearMap

section topDualPairing

variable {𝕜 E : Type*} [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜] [AddCommMonoid E]
  [Module 𝕜 E] [TopologicalSpace E] [ContinuousConstSMul 𝕜 𝕜]

variable (𝕜 E) in
/-- The canonical pairing of a vector space and its topological dual. -/
/-
**topDualPairing** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：topDualPairing : (E ->L[𝕜] 𝕜) ->ₗ[𝕜] E ->ₗ[𝕜] 𝕜
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical pairing of a vector space and its topological dual.
-/
def topDualPairing : (E →L[𝕜] 𝕜) →ₗ[𝕜] E →ₗ[𝕜] 𝕜 :=
  ContinuousLinearMap.coeLM 𝕜

@[simp]
/-
**topDualPairing_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：topDualPairing_apply (v : E ->L[𝕜] 𝕜) (x : E) : topDualPairing 𝕜 E v x = v
 x
参数：v : E ->L[𝕜] 𝕜；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem topDualPairing_apply (v : E →L[𝕜] 𝕜)
    (x : E) : topDualPairing 𝕜 E v x = v x :=
  rfl

end topDualPairing

