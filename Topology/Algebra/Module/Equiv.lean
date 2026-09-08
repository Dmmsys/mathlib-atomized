/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo, Yury Kudryashov, Frédéric Dupuis,
  Heather Macbeth
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict

/-!
# Continuous linear equivalences

## Notation
Continuous semilinear / linear / star-linear equivalences between topological modules are denoted
by `M ≃SL[σ] M₂`, `M ≃L[R] M₂` and `M ≃L⋆[R] M₂`.

## Main Definitions
* `toHomeomorph` is the homeomorphism induced by a continuous (semi)linear equivalence.
* `symm` is the inverse of a continuous linear equivalence as a continuous linear equivalence.
* `equivOfInverse` creates a `ContinuousLinearEquiv` from two `ContinuousLinearMap`s that are
  inverse of each other (as functions). See also `equivOfInverse'` when they're inverse to each
  other as continuous linear maps.
* `ofUnit` is the `ContinuousLinearEquiv` corresponding to a unit in the ring of continuous
  endomorphisms. See `toUnit` for the inverse direction.
* `IsInvertible`: a continuous linear map is invertible if it is the forward direction of a
  continuous linear equivalence.
* `ofIsHomeomorph`: a linear equivalence that is a homeomorphism is a continuous linear equivalence.

## Main Results
* `prodComm`: the product of topological modules is commutative up to continuous linear isomorphism.
* `LinearEquiv.isHomeomorph_iff`: A linear equivalence between topological modules is a
  homeomorphism if and only if it is continuous in both directions.
-/

@[expose] public section

assert_not_exists TrivialStar

open LinearMap (ker range)
open Topology Filter Pointwise
open scoped Ring

universe u v w u'

/-- Continuous linear equivalences between modules. We only put the type classes that are necessary
for the definition, although in applications `M` and `M₂` will be topological modules over the
topological semiring `R`. -/
/-
**ContinuousLinearEquiv** 是 Mathlib 中的一个结构，位于命名空间 ``。
形式化陈述：ContinuousLinearEquiv {R : Type*} {S : Type*} [Semiring R] [Semiring S] (σ
 : R ->+* S) {σ' : S ->+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (M : Ty
pe*) [TopologicalSpace M] [AddCommMonoid M] (M₂ : Type*) [TopologicalSpace M₂] [
AddCommMonoid M₂] [Module R M] [Module S M₂] extends M ≃ₛₗ[σ] M₂ where continuou
s_toFun : Continuous toFun
参数：σ : R ->+* S；M : Type*；M₂ : Type*。
继承自：M ≃ₛₗ[σ] M₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Continuous linear equivalences between modules. We only put the type classes tha
t are necessary
for the definition, although in applications `M` and `M₂` will be topological mo
dules over the
topological semiring `R`.
-/
structure ContinuousLinearEquiv {R : Type*} {S : Type*} [Semiring R] [Semiring S] (σ : R →+* S)
    {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (M : Type*) [TopologicalSpace M]
    [AddCommMonoid M] (M₂ : Type*) [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M]
    [Module S M₂] extends M ≃ₛₗ[σ] M₂ where
  continuous_toFun : Continuous toFun := by first | fun_prop | eta_expand; dsimp; fun_prop | skip
  continuous_invFun : Continuous invFun := by first | fun_prop | eta_expand; dsimp; fun_prop | skip

attribute [inherit_doc ContinuousLinearEquiv] ContinuousLinearEquiv.continuous_toFun
ContinuousLinearEquiv.continuous_invFun

@[inherit_doc]
notation:50 M " ≃SL[" σ "] " M₂ => ContinuousLinearEquiv σ M M₂

@[inherit_doc]
notation:50 M " ≃L[" R "] " M₂ => ContinuousLinearEquiv (RingHom.id R) M M₂

/-- `ContinuousSemilinearEquivClass F σ M M₂` asserts `F` is a type of bundled continuous
`σ`-semilinear equivs `M → M₂`.  See also `ContinuousLinearEquivClass F R M M₂` for the case
where `σ` is the identity map on `R`.  A map `f` between an `R`-module and an `S`-module over a ring
homomorphism `σ : R →+* S` is semilinear if it satisfies the two properties `f (x + y) = f x + f y`
and `f (c • x) = (σ c) • f x`. -/
/-
**ContinuousSemilinearEquivClass** 是 Mathlib 中的一个类，位于命名空间 ``。
形式化陈述：ContinuousSemilinearEquivClass (F : Type*) {R : outParam Type*} {S : outPa
ram Type*} [Semiring R] [Semiring S] (σ : outParam <| R ->+* S) {σ' : outParam <
| S ->+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (M : outParam Type*) [To
pologicalSpace M] [AddCommMonoid M] (M₂ : outParam Type*) [TopologicalSpace M₂] 
[AddCommMonoid M₂] [Module R M] [Module S M₂] [EquivLike F M M₂] : Prop extends 
SemilinearEquivClass F σ M M₂ where map_continuous : forall f : F, Continuous f
参数：F : Type*；σ : outParam <| R ->+* S；M : outParam Type*；M₂ : outParam Type*。
继承自：SemilinearEquivClass F σ M M₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ContinuousSemilinearEquivClass F σ M M₂` asserts `F` is a type of bundled conti
nuous
`σ`-semilinear equivs `M → M₂`.  See also `ContinuousLinearEquivClass F R M M₂` 
for the case
where `σ` is the identity map on `R`.  A map `f` between an `R`-module and an `S
`-module over a ring
homomorphism `σ : R →+* S` is semilinear if it satisfies the two properties `f (
x + y) = f x + f y`
and `f (c • x) = (σ c) • f x`.
-/
class ContinuousSemilinearEquivClass (F : Type*) {R : outParam Type*} {S : outParam Type*}
    [Semiring R] [Semiring S] (σ : outParam <| R →+* S) {σ' : outParam <| S →+* R}
    [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (M : outParam Type*) [TopologicalSpace M]
    [AddCommMonoid M] (M₂ : outParam Type*) [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M]
    [Module S M₂] [EquivLike F M M₂] : Prop extends SemilinearEquivClass F σ M M₂ where
  map_continuous : ∀ f : F, Continuous f := by first | fun_prop | dsimp; fun_prop
  inv_continuous : ∀ f : F, Continuous (EquivLike.inv f) := by first | fun_prop | dsimp; fun_prop

attribute [inherit_doc ContinuousSemilinearEquivClass]
ContinuousSemilinearEquivClass.map_continuous
ContinuousSemilinearEquivClass.inv_continuous

/-- `ContinuousLinearEquivClass F σ M M₂` asserts `F` is a type of bundled continuous
`R`-linear equivs `M → M₂`. This is an abbreviation for
`ContinuousSemilinearEquivClass F (RingHom.id R) M M₂`. -/
/-
**ContinuousLinearEquivClass** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：ContinuousLinearEquivClass (F : Type*) (R : outParam Type*) [Semiring R] (
M : outParam Type*) [TopologicalSpace M] [AddCommMonoid M] (M₂ : outParam Type*)
 [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M] [Module R M₂] [EquivLike 
F M M₂]
参数：F : Type*；R : outParam Type*；M : outParam Type*；M₂ : outParam Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ContinuousLinearEquivClass F σ M M₂` asserts `F` is a type of bundled continuou
s
`R`-linear equivs `M → M₂`. This is an abbreviation for
`ContinuousSemilinearEquivClass F (RingHom.id R) M M₂`.
-/
abbrev ContinuousLinearEquivClass (F : Type*) (R : outParam Type*) [Semiring R]
    (M : outParam Type*) [TopologicalSpace M] [AddCommMonoid M] (M₂ : outParam Type*)
    [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M] [Module R M₂] [EquivLike F M M₂] :=
  ContinuousSemilinearEquivClass F (RingHom.id R) M M₂

namespace ContinuousSemilinearEquivClass

variable (F : Type*) {R : Type*} {S : Type*} [Semiring R] [Semiring S] (σ : R →+* S)
  {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
  (M : Type*) [TopologicalSpace M] [AddCommMonoid M]
  (M₂ : Type*) [TopologicalSpace M₂] [AddCommMonoid M₂]
  [Module R M] [Module S M₂]

-- `σ'` becomes a metavariable, but it's OK since it's an outparam
/-
**ContinuousSemilinearEquivClass.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousSemilinea
rEquivClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) continuousSemilinearMapClass [EquivLike F M M₂]
    [s : ContinuousSemilinearEquivClass F σ M M₂] : ContinuousSemilinearMapClass F σ M M₂ :=
  { s with }
/-
**ContinuousSemilinearEquivClass.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousSemilinea
rEquivClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) [EquivLike F M M₂]
    [s : ContinuousSemilinearEquivClass F σ M M₂] : HomeomorphClass F M M₂ :=
  { s with }

end ContinuousSemilinearEquivClass

namespace ContinuousLinearMap

section Pi

variable {R : Type*} [Semiring R] {M : Type*} [TopologicalSpace M] [AddCommMonoid M] [Module R M]
  {M₂ : Type*} [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M₂] {ι : Type*} {φ : ι → Type*}
  [∀ i, TopologicalSpace (φ i)] [∀ i, AddCommMonoid (φ i)] [∀ i, Module R (φ i)]

variable (R φ)

/-- If `I` and `J` are complementary index sets, the product of the kernels of the `J`th projections
of `φ` is linearly equivalent to the product over `I`. -/
/-
**ContinuousLinearMap.iInfKerProjEquiv** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLine
arMap`。
形式化陈述：iInfKerProjEquiv {I J : Set ι} [DecidablePred fun i => i in I] (hd : Disjo
int I J) (hu : Set.univ subseteq I union J) : (⨅ i in J, (proj i : (forall i, φ 
i) ->L[R] φ i).ker : Submodule R (forall i, φ i)) ≃L[R] forall i : I, φ i where 
toLinearEquiv
参数：hd : Disjoint I J；hu : Set.univ subseteq I union J。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `I` and `J` are complementary index sets, the product of the kernels of the `
J`th projections
of `φ` is linearly equivalent to the product over `I`.
-/
def iInfKerProjEquiv {I J : Set ι} [DecidablePred fun i => i ∈ I] (hd : Disjoint I J)
    (hu : Set.univ ⊆ I ∪ J) :
    (⨅ i ∈ J, (proj i : (∀ i, φ i) →L[R] φ i).ker : Submodule R (∀ i, φ i)) ≃L[R] ∀ i : I, φ i where
  toLinearEquiv := LinearMap.iInfKerProjEquiv R φ hd hu
  continuous_toFun :=
    continuous_pi fun i =>
      Continuous.comp (continuous_apply (A := φ) i) <| continuous_subtype_val
  continuous_invFun :=
    Continuous.subtype_mk
      (continuous_pi fun i => by
        dsimp
        split_ifs <;> [apply continuous_apply; exact continuous_zero])
      _

end Pi

end ContinuousLinearMap

namespace ContinuousLinearEquiv

section AddCommMonoid

variable {R₁ : Type*} {R₂ : Type*} {R₃ : Type*} [Semiring R₁] [Semiring R₂] [Semiring R₃]
  {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
  {σ₂₃ : R₂ →+* R₃} {σ₃₂ : R₃ →+* R₂} [RingHomInvPair σ₂₃ σ₃₂] [RingHomInvPair σ₃₂ σ₂₃]
  {σ₁₃ : R₁ →+* R₃} {σ₃₁ : R₃ →+* R₁} [RingHomInvPair σ₁₃ σ₃₁] [RingHomInvPair σ₃₁ σ₁₃]
  [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomCompTriple σ₃₂ σ₂₁ σ₃₁] {M₁ : Type*}
  [TopologicalSpace M₁] [AddCommMonoid M₁]
  {M₂ : Type*} [TopologicalSpace M₂] [AddCommMonoid M₂] {M₃ : Type*} [TopologicalSpace M₃]
  [AddCommMonoid M₃] {M₄ : Type*} [TopologicalSpace M₄] [AddCommMonoid M₄] [Module R₁ M₁]
  [Module R₂ M₂] [Module R₃ M₃]

/-- A continuous linear equivalence induces a continuous linear map. -/
@[coe]
/-
**ContinuousLinearEquiv.toContinuousLinearMap** 是 Mathlib 中的一个定义，位于命名空间 `Continu
ousLinearEquiv`。
形式化陈述：toContinuousLinearMap (e : M₁ ≃SL[σ₁₂] M₂) : M₁ ->SL[σ₁₂] M₂
参数：e : M₁ ≃SL[σ₁₂] M₂。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearEquiv.continuous_toFun`：∀ {R : Type u_1} {S : Type u_2} 
[inst : Semiring R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2
 : RingHomInvPair σ σ'] [ins…

--- 原说明 ---
A continuous linear equivalence induces a continuous linear map.
-/
def toContinuousLinearMap (e : M₁ ≃SL[σ₁₂] M₂) : M₁ →SL[σ₁₂] M₂ :=
  { e.toLinearEquiv.toLinearMap with cont := e.continuous_toFun }

attribute [coe] toLinearEquiv

/-- Coerce continuous linear equivs to continuous linear maps. -/
/-
**ContinuousLinearEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLinearEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coerce continuous linear equivs to continuous linear maps.
-/
instance : Coe (M₁ ≃SL[σ₁₂] M₂) (M₁ →SL[σ₁₂] M₂) where coe := toContinuousLinearMap
/-
**ContinuousLinearEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLinearEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Coe (M₁ ≃SL[σ₁₂] M₂) (M₁ ≃ₛₗ[σ₁₂] M₂) where coe := toLinearEquiv
/-
**ContinuousLinearEquiv.toLinearMap_toContinuousLinearMap** 是 Mathlib 中的一个定理，位于命
名空间 `ContinuousLinearEquiv`。
形式化陈述：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Semiring R₁] [inst_1 : Semiring 
R₂] {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁}   [inst_2 : RingHomInvPair σ₁₂ σ₂₁] [ins
t_3 : RingHomInvPair σ₂₁ σ₁₂] {M₁ : Type u_4} [inst_4 : TopologicalSpace M₁]   [
inst_5 : AddCommMonoid M₁] {M₂ : Type u_5} [inst_6 : TopologicalSpace M₂] [inst_
7 : AddCommMonoid M₂]   [inst_8 : _root_.Module R₁ M₁] [inst_9 : _root_.Module R
₂ M₂] (e : M₁ ≃SL[σ₁₂] M₂), ↑↑e = ↑↑e
参数：e : M₁ ≃SL[σ₁₂] M₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toLinearMap_toContinuousLinearMap (e : M₁ ≃SL[σ₁₂] M₂) :
    e.toContinuousLinearMap.toLinearMap = e.toLinearEquiv.toLinearMap := rfl
/-
**ContinuousLinearEquiv.equivLike** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLinearEqu
iv`。
形式化陈述：equivLike : EquivLike (M₁ ≃SL[σ₁₂] M₂) M₁ M₂ where coe f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance equivLike :
    EquivLike (M₁ ≃SL[σ₁₂] M₂) M₁ M₂ where
  coe f := f.toFun
  inv f := f.invFun
  coe_injective' f g h₁ h₂ := by
    obtain ⟨f', _⟩ := f
    obtain ⟨g', _⟩ := g
    rcases f' with ⟨⟨⟨_, _⟩, _⟩, _⟩
    rcases g' with ⟨⟨⟨_, _⟩, _⟩, _⟩
    congr
  left_inv f := f.left_inv
  right_inv f := f.right_inv
/-
**ContinuousLinearEquiv.continuousSemilinearEquivClass** 是 Mathlib 中的一个实例，位于命名空间
 `ContinuousLinearEquiv`。
形式化陈述：continuousSemilinearEquivClass : ContinuousSemilinearEquivClass (M₁ ≃SL[σ₁
₂] M₂) σ₁₂ M₁ M₂ where map_add f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AddHom.map_add'`：∀ {M : Type u_10} {N : Type u_11} [inst : Add M] [inst_
1 : Add N] (self : M →ₙ+ N) (x y : M),   self.toFun (x + y) = self.toFun x + sel
f.toF…
· 使用定理 `LinearMap.map_smul'`：∀ {R : Type u_14} {S : Type u_15} [inst : Semiring 
R] [inst_1 : Semiring S] {σ : R →+* S} {M : Type u_16}   {M₂ : Type u_17} [inst_
2 : AddCo…
· 使用定理 `ContinuousLinearEquiv.continuous_toFun`：∀ {R : Type u_1} {S : Type u_2} 
[inst : Semiring R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2
 : RingHomInvPair σ σ'] [ins…
· 使用定理 `ContinuousLinearEquiv.continuous_invFun`：∀ {R : Type u_1} {S : Type u_2}
 [inst : Semiring R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_
2 : RingHomInvPair σ σ'] [ins…
-/
instance continuousSemilinearEquivClass :
    ContinuousSemilinearEquivClass (M₁ ≃SL[σ₁₂] M₂) σ₁₂ M₁ M₂ where
  map_add f := f.map_add'
  map_smulₛₗ f := f.map_smul'
  map_continuous := continuous_toFun
  inv_continuous := continuous_invFun

@[simp]
/-
**ContinuousLinearEquiv.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearEquiv`
。
形式化陈述：coe_mk (e : M₁ ≃ₛₗ[σ₁₂] M₂) (a b) : ⇑(ContinuousLinearEquiv.mk e a b) = e
参数：e : M₁ ≃ₛₗ[σ₁₂] M₂；a b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (e : M₁ ≃ₛₗ[σ₁₂] M₂) (a b) : ⇑(ContinuousLinearEquiv.mk e a b) = e := rfl
/-
**ContinuousLinearEquiv.coe_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearEqu
iv`。
形式化陈述：coe_apply (e : M₁ ≃SL[σ₁₂] M₂) (b : M₁) : (e : M₁ ->SL[σ₁₂] M₂) b = e b
参数：e : M₁ ≃SL[σ₁₂] M₂；b : M₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_apply (e : M₁ ≃SL[σ₁₂] M₂) (b : M₁) : (e : M₁ →SL[σ₁₂] M₂) b = e b :=
  rfl

@[simp]
/-
**ContinuousLinearEquiv.coe_toLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousL
inearEquiv`。
形式化陈述：coe_toLinearEquiv (f : M₁ ≃SL[σ₁₂] M₂) : ⇑f.toLinearEquiv = f
参数：f : M₁ ≃SL[σ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toLinearEquiv (f : M₁ ≃SL[σ₁₂] M₂) : ⇑f.toLinearEquiv = f :=
  rfl

@[simp, norm_cast]
/-
**ContinuousLinearEquiv.coe_coe** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearEquiv
`。
形式化陈述：coe_coe (e : M₁ ≃SL[σ₁₂] M₂) : ⇑(e : M₁ ->SL[σ₁₂] M₂) = e
参数：e : M₁ ≃SL[σ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_coe (e : M₁ ≃SL[σ₁₂] M₂) : ⇑(e : M₁ →SL[σ₁₂] M₂) = e :=
  rfl
/-
**ContinuousLinearEquiv.toLinearEquiv_injective** 是 Mathlib 中的一个定理，位于命名空间 `Conti
nuousLinearEquiv`。
形式化陈述：toLinearEquiv_injective : Function.Injective (toLinearEquiv : (M₁ ≃SL[σ₁₂]
 M₂) -> M₁ ≃ₛₗ[σ₁₂] M₂)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLinearEquiv_injective :
    Function.Injective (toLinearEquiv : (M₁ ≃SL[σ₁₂] M₂) → M₁ ≃ₛₗ[σ₁₂] M₂) := by
  rintro ⟨e, _, _⟩ ⟨e', _, _⟩ rfl
  rfl

@[ext]
/-
**ContinuousLinearEquiv.ext** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearEquiv`。
形式化陈述：ext {f g : M₁ ≃SL[σ₁₂] M₂} (h : (f : M₁ -> M₂) = g) : f = g
参数：h : (f : M₁ -> M₂) = g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearEquiv.toLinearEquiv_injective`：toLinearEquiv_injective :
 Function.Injective (toLinearEquiv : (M₁ ≃SL[σ₁₂] M₂) -> M₁ ≃ₛₗ[σ₁₂] M₂)
· 使用定理 `LinearEquiv.ext`：ext (h : forall x, e x = e' x) : e = e'
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
-/
theorem ext {f g : M₁ ≃SL[σ₁₂] M₂} (h : (f : M₁ → M₂) = g) : f = g :=
  toLinearEquiv_injective <| LinearEquiv.ext <| congr_fun h
/-
**ContinuousLinearEquiv.coe_injective** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinea
rEquiv`。
形式化陈述：coe_injective : Function.Injective ((↑) : (M₁ ≃SL[σ₁₂] M₂) -> M₁ ->SL[σ₁₂]
 M₂)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearEquiv.ext`：ext {f g : M₁ ≃SL[σ₁₂] M₂} (h : (f : M₁ -> M₂
) = g) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ContinuousLinearMap.ext_iff`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : S
emiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_2 :
 TopologicalSpace…
-/
theorem coe_injective : Function.Injective ((↑) : (M₁ ≃SL[σ₁₂] M₂) → M₁ →SL[σ₁₂] M₂) :=
  fun _e _e' h => ext <| funext <| ContinuousLinearMap.ext_iff.1 h

@[simp, norm_cast]
/-
**ContinuousLinearEquiv.coe_inj** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearEquiv
`。
形式化陈述：coe_inj {e e' : M₁ ≃SL[σ₁₂] M₂} : (e : M₁ ->SL[σ₁₂] M₂) = e' ↔ e = e'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `ContinuousLinearEquiv.coe_injective`：coe_injective : Function.Injective 
((↑) : (M₁ ≃SL[σ₁₂] M₂) -> M₁ ->SL[σ₁₂] M₂)
-/
theorem coe_inj {e e' : M₁ ≃SL[σ₁₂] M₂} : (e : M₁ →SL[σ₁₂] M₂) = e' ↔ e = e' :=
  coe_injective.eq_iff

/-- A continuous linear equivalence induces a homeomorphism. -/
/-
**ContinuousLinearEquiv.toHomeomorph** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinear
Equiv`。
形式化陈述：toHomeomorph (e : M₁ ≃SL[σ₁₂] M₂) : M₁ ≃ₜ M₂
参数：e : M₁ ≃SL[σ₁₂] M₂。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearEquiv.continuous_toFun`：∀ {R : Type u_1} {S : Type u_2} 
[inst : Semiring R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2
 : RingHomInvPair σ σ'] [ins…
· 使用定理 `ContinuousLinearEquiv.continuous_invFun`：∀ {R : Type u_1} {S : Type u_2}
 [inst : Semiring R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_
2 : RingHomInvPair σ σ'] [ins…

--- 原说明 ---
A continuous linear equivalence induces a homeomorphism.
-/
def toHomeomorph (e : M₁ ≃SL[σ₁₂] M₂) : M₁ ≃ₜ M₂ :=
  { e with toEquiv := e.toLinearEquiv.toEquiv }

@[simp]
/-
**ContinuousLinearEquiv.coe_toHomeomorph** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLi
nearEquiv`。
形式化陈述：coe_toHomeomorph (e : M₁ ≃SL[σ₁₂] M₂) : ⇑e.toHomeomorph = e
参数：e : M₁ ≃SL[σ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toHomeomorph (e : M₁ ≃SL[σ₁₂] M₂) : ⇑e.toHomeomorph = e :=
  rfl
/-
**ContinuousLinearEquiv.isOpenMap** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearEqu
iv`。
形式化陈述：isOpenMap (e : M₁ ≃SL[σ₁₂] M₂) : IsOpenMap e
参数：e : M₁ ≃SL[σ₁₂] M₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.isOpenMap`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), IsOpenMap ⇑h
-/
theorem isOpenMap (e : M₁ ≃SL[σ₁₂] M₂) : IsOpenMap e :=
  (ContinuousLinearEquiv.toHomeomorph e).isOpenMap
/-
**ContinuousLinearEquiv.image_closure** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinea
rEquiv`。
形式化陈述：image_closure (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₁) : e '' closure s = closure
 (e '' s)
参数：e : M₁ ≃SL[σ₁₂] M₂；s : Set M₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.image_closure`：image_closure (h : X ≃ₜ Y) (s : Set X) : h '' 
closure s = closure (h '' s)
-/
theorem image_closure (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₁) : e '' closure s = closure (e '' s) :=
  e.toHomeomorph.image_closure s
/-
**ContinuousLinearEquiv.preimage_closure** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLi
nearEquiv`。
形式化陈述：preimage_closure (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₂) : e ⁻¹' closure s = clo
sure (e ⁻¹' s)
参数：e : M₁ ≃SL[σ₁₂] M₂；s : Set M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.preimage_closure`：preimage_closure (h : X ≃ₜ Y) (s : Set Y) :
 h ⁻¹' closure s = closure (h ⁻¹' s)
-/
theorem preimage_closure (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₂) : e ⁻¹' closure s = closure (e ⁻¹' s) :=
  e.toHomeomorph.preimage_closure s

@[simp]
/-
**ContinuousLinearEquiv.isClosed_image** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLine
arEquiv`。
形式化陈述：isClosed_image (e : M₁ ≃SL[σ₁₂] M₂) {s : Set M₁} : IsClosed (e '' s) ↔ IsC
losed s
参数：e : M₁ ≃SL[σ₁₂] M₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.isClosed_image`：isClosed_image (h : X ≃ₜ Y) {s : Set X} : IsC
losed (h '' s) ↔ IsClosed s
-/
theorem isClosed_image (e : M₁ ≃SL[σ₁₂] M₂) {s : Set M₁} : IsClosed (e '' s) ↔ IsClosed s :=
  e.toHomeomorph.isClosed_image
/-
**ContinuousLinearEquiv.map_nhds_eq** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearE
quiv`。
形式化陈述：map_nhds_eq (e : M₁ ≃SL[σ₁₂] M₂) (x : M₁) : map e (𝓝 x) = 𝓝 (e x)
参数：e : M₁ ≃SL[σ₁₂] M₂；x : M₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.map_nhds_eq`：map_nhds_eq (h : X ≃ₜ Y) (x : X) : map h (𝓝 x) =
 𝓝 (h x)
-/
theorem map_nhds_eq (e : M₁ ≃SL[σ₁₂] M₂) (x : M₁) : map e (𝓝 x) = 𝓝 (e x) :=
  e.toHomeomorph.map_nhds_eq x
/-
**ContinuousLinearEquiv.map_zero** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearEqui
v`。
形式化陈述：map_zero (e : M₁ ≃SL[σ₁₂] M₂) : e (0 : M₁) = 0
参数：e : M₁ ≃SL[σ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.map_zero`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : 
Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_2 
: TopologicalSpace…
-/
theorem map_zero (e : M₁ ≃SL[σ₁₂] M₂) : e (0 : M₁) = 0 :=
  (e : M₁ →SL[σ₁₂] M₂).map_zero
/-
**ContinuousLinearEquiv.map_add** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearEquiv
`。
形式化陈述：map_add (e : M₁ ≃SL[σ₁₂] M₂) (x y : M₁) : e (x + y) = e x + e y
参数：e : M₁ ≃SL[σ₁₂] M₂；x y : M₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.map_add`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : S
emiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_2 :
 TopologicalSpace…
-/
theorem map_add (e : M₁ ≃SL[σ₁₂] M₂) (x y : M₁) : e (x + y) = e x + e y :=
  (e : M₁ →SL[σ₁₂] M₂).map_add x y

@[simp]
/-
**ContinuousLinearEquiv.map_smul** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearEqui
v`。
形式化陈述：map_smul [Module R₁ M₂] (e : M₁ ≃L[R₁] M₂) (c : R₁) (x : M₁) : e (c • x) =
 c • e x
参数：e : M₁ ≃L[R₁] M₂；c : R₁；x : M₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.map_smul`：∀ {R₁ : Type u_1} [inst : Semiring R₁] {M₁
 : Type u_4} [inst_1 : TopologicalSpace M₁] [inst_2 : AddCommMonoid M₁]   {M₂ : 
Type u_6} [inst_3 …
-/
theorem map_smulₛₗ (e : M₁ ≃SL[σ₁₂] M₂) (c : R₁) (x : M₁) : e (c • x) = σ₁₂ c • e x :=
  (e : M₁ →SL[σ₁₂] M₂).map_smulₛₗ c x
/-
**ContinuousLinearEquiv.map_smul** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearEqui
v`。
形式化陈述：map_smul [Module R₁ M₂] (e : M₁ ≃L[R₁] M₂) (c : R₁) (x : M₁) : e (c • x) =
 c • e x
参数：e : M₁ ≃L[R₁] M₂；c : R₁；x : M₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.map_smul`：∀ {R₁ : Type u_1} [inst : Semiring R₁] {M₁
 : Type u_4} [inst_1 : TopologicalSpace M₁] [inst_2 : AddCommMonoid M₁]   {M₂ : 
Type u_6} [inst_3 …
-/
theorem map_smul [Module R₁ M₂] (e : M₁ ≃L[R₁] M₂) (c : R₁) (x : M₁) : e (c • x) = c • e x :=
  (e : M₁ →L[R₁] M₂).map_smul c x
/-
**ContinuousLinearEquiv.map_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLin
earEquiv`。
形式化陈述：map_eq_zero_iff (e : M₁ ≃SL[σ₁₂] M₂) {x : M₁} : e x = 0 ↔ x = 0
参数：e : M₁ ≃SL[σ₁₂] M₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.map_eq_zero_iff`：map_eq_zero_iff {x : M} : e x = 0 ↔ x = 0
-/
theorem map_eq_zero_iff (e : M₁ ≃SL[σ₁₂] M₂) {x : M₁} : e x = 0 ↔ x = 0 :=
  e.toLinearEquiv.map_eq_zero_iff

attribute [continuity]
  ContinuousLinearEquiv.continuous_toFun ContinuousLinearEquiv.continuous_invFun

@[continuity]
/-
**ContinuousLinearEquiv.continuous** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearEq
uiv`。
形式化陈述：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Semiring R₁] [inst_1 : Semiring 
R₂] {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁}   [inst_2 : RingHomInvPair σ₁₂ σ₂₁] [ins
t_3 : RingHomInvPair σ₂₁ σ₁₂] {M₁ : Type u_4} [inst_4 : TopologicalSpace M₁]   [
inst_5 : AddCommMonoid M₁] {M₂ : Type u_5} [inst_6 : TopologicalSpace M₂] [inst_
7 : AddCommMonoid M₂]   [inst_8 : _root_.Module R₁ M₁] [inst_9 : _root_.Module R
₂ M₂] (e : M₁ ≃SL[σ₁₂] M₂), Continuous ⇑e
参数：e : M₁ ≃SL[σ₁₂] M₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearEquiv.continuous_toFun`：∀ {R : Type u_1} {S : Type u_2} 
[inst : Semiring R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2
 : RingHomInvPair σ σ'] [ins…
-/
protected theorem continuous (e : M₁ ≃SL[σ₁₂] M₂) : Continuous (e : M₁ → M₂) :=
  e.continuous_toFun
/-
**ContinuousLinearEquiv.continuousOn** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinear
Equiv`。
形式化陈述：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Semiring R₁] [inst_1 : Semiring 
R₂] {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁}   [inst_2 : RingHomInvPair σ₁₂ σ₂₁] [ins
t_3 : RingHomInvPair σ₂₁ σ₁₂] {M₁ : Type u_4} [inst_4 : TopologicalSpace M₁]   [
inst_5 : AddCommMonoid M₁] {M₂ : Type u_5} [inst_6 : TopologicalSpace M₂] [inst_
7 : AddCommMonoid M₂]   [inst_8 : _root_.Module R₁ M₁] [inst_9 : _root_.Module R
₂ M₂] (e : M₁ ≃SL[σ₁₂] M₂) {s : Set M₁}, ContinuousOn (⇑e) s
参数：e : M₁ ≃SL[σ₁₂] M₂；⇑e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `ContinuousLinearEquiv.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [ins
t : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁}   [i
nst_2 : RingHomInvPair…
-/
protected theorem continuousOn (e : M₁ ≃SL[σ₁₂] M₂) {s : Set M₁} : ContinuousOn (e : M₁ → M₂) s :=
  e.continuous.continuousOn
/-
**ContinuousLinearEquiv.continuousAt** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinear
Equiv`。
形式化陈述：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Semiring R₁] [inst_1 : Semiring 
R₂] {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁}   [inst_2 : RingHomInvPair σ₁₂ σ₂₁] [ins
t_3 : RingHomInvPair σ₂₁ σ₁₂] {M₁ : Type u_4} [inst_4 : TopologicalSpace M₁]   [
inst_5 : AddCommMonoid M₁] {M₂ : Type u_5} [inst_6 : TopologicalSpace M₂] [inst_
7 : AddCommMonoid M₂]   [inst_8 : _root_.Module R₁ M₁] [inst_9 : _root_.Module R
₂ M₂] (e : M₁ ≃SL[σ₁₂] M₂) {x : M₁}, ContinuousAt (⇑e) x
参数：e : M₁ ≃SL[σ₁₂] M₂；⇑e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `ContinuousLinearEquiv.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [ins
t : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁}   [i
nst_2 : RingHomInvPair…
-/
protected theorem continuousAt (e : M₁ ≃SL[σ₁₂] M₂) {x : M₁} : ContinuousAt (e : M₁ → M₂) x :=
  e.continuous.continuousAt
/-
**ContinuousLinearEquiv.continuousWithinAt** 是 Mathlib 中的一个定理，位于命名空间 `Continuous
LinearEquiv`。
形式化陈述：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Semiring R₁] [inst_1 : Semiring 
R₂] {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁}   [inst_2 : RingHomInvPair σ₁₂ σ₂₁] [ins
t_3 : RingHomInvPair σ₂₁ σ₁₂] {M₁ : Type u_4} [inst_4 : TopologicalSpace M₁]   [
inst_5 : AddCommMonoid M₁] {M₂ : Type u_5} [inst_6 : TopologicalSpace M₂] [inst_
7 : AddCommMonoid M₂]   [inst_8 : _root_.Module R₁ M₁] [inst_9 : _root_.Module R
₂ M₂] (e : M₁ ≃SL[σ₁₂] M₂) {s : Set M₁} {x : M₁},   ContinuousWithinAt (⇑e) s x
参数：e : M₁ ≃SL[σ₁₂] M₂；⇑e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.continuousWithinAt`：Continuous.continuousWithinAt (h : Contin
uous f) : ContinuousWithinAt f s x
· 使用定理 `ContinuousLinearEquiv.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [ins
t : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁}   [i
nst_2 : RingHomInvPair…
-/
protected theorem continuousWithinAt (e : M₁ ≃SL[σ₁₂] M₂) {s : Set M₁} {x : M₁} :
    ContinuousWithinAt (e : M₁ → M₂) s x :=
  e.continuous.continuousWithinAt
/-
**ContinuousLinearEquiv.comp_continuousOn_iff** 是 Mathlib 中的一个定理，位于命名空间 `Continu
ousLinearEquiv`。
形式化陈述：comp_continuousOn_iff {α : Type*} [TopologicalSpace α] (e : M₁ ≃SL[σ₁₂] M₂
) {f : α -> M₁} {s : Set α} : ContinuousOn (e ∘ f) s ↔ ContinuousOn f s
参数：e : M₁ ≃SL[σ₁₂] M₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.comp_continuousOn_iff`：comp_continuousOn_iff (h : X ≃ₜ Y) (f 
: Z -> X) (s : Set Z) : ContinuousOn (h ∘ f) s ↔ ContinuousOn f s
-/
theorem comp_continuousOn_iff {α : Type*} [TopologicalSpace α] (e : M₁ ≃SL[σ₁₂] M₂) {f : α → M₁}
    {s : Set α} : ContinuousOn (e ∘ f) s ↔ ContinuousOn f s :=
  e.toHomeomorph.comp_continuousOn_iff _ _
/-
**ContinuousLinearEquiv.comp_continuous_iff** 是 Mathlib 中的一个定理，位于命名空间 `Continuou
sLinearEquiv`。
形式化陈述：comp_continuous_iff {α : Type*} [TopologicalSpace α] (e : M₁ ≃SL[σ₁₂] M₂) 
{f : α -> M₁} : Continuous (e ∘ f) ↔ Continuous f
参数：e : M₁ ≃SL[σ₁₂] M₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.comp_continuous_iff`：comp_continuous_iff (h : X ≃ₜ Y) {f : Z 
-> X} : Continuous (h ∘ f) ↔ Continuous f
-/
theorem comp_continuous_iff {α : Type*} [TopologicalSpace α] (e : M₁ ≃SL[σ₁₂] M₂) {f : α → M₁} :
    Continuous (e ∘ f) ↔ Continuous f :=
  e.toHomeomorph.comp_continuous_iff

/-- An extensionality lemma for `R ≃L[R] M`. -/
/-
**ContinuousLinearEquiv.ext** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearEquiv`。
形式化陈述：ext {f g : M₁ ≃SL[σ₁₂] M₂} (h : (f : M₁ -> M₂) = g) : f = g
参数：h : (f : M₁ -> M₂) = g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearEquiv.toLinearEquiv_injective`：toLinearEquiv_injective :
 Function.Injective (toLinearEquiv : (M₁ ≃SL[σ₁₂] M₂) -> M₁ ≃ₛₗ[σ₁₂] M₂)
· 使用定理 `LinearEquiv.ext`：ext (h : forall x, e x = e' x) : e = e'
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a

--- 原说明 ---
An extensionality lemma for `R ≃L[R] M`.
-/
theorem ext₁ [TopologicalSpace R₁] {f g : R₁ ≃L[R₁] M₁} (h : f 1 = g 1) : f = g :=
  ext <| funext fun x => mul_one x ▸ by rw [← smul_eq_mul, map_smul, h, map_smul]

section

variable {M : Type*} [TopologicalSpace M] [AddCommMonoid M] [Module R₁ M]

/-- A continuous linear equivalence seen as a `ContinuousAddEquiv`. -/
/-
**ContinuousLinearEquiv.toContinuousAddEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Continuo
usLinearEquiv`。
形式化陈述：toContinuousAddEquiv (e : M₁ ≃L[R₁] M) : M₁ ≃ₜ+ M
参数：e : M₁ ≃L[R₁] M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A continuous linear equivalence seen as a `ContinuousAddEquiv`.
-/
def toContinuousAddEquiv (e : M₁ ≃L[R₁] M) : M₁ ≃ₜ+ M :=
  e.toAddEquiv.toContinuousAddEquiv fun _ ↦ e.toHomeomorph.isOpen_preimage

@[simp]
/-
**ContinuousLinearEquiv.toContinuousAddEquiv_coe** 是 Mathlib 中的一个引理，位于命名空间 `Cont
inuousLinearEquiv`。
形式化陈述：toContinuousAddEquiv_coe (e : M₁ ≃L[R₁] M) : ⇑e.toContinuousAddEquiv = e
参数：e : M₁ ≃L[R₁] M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toContinuousAddEquiv_coe (e : M₁ ≃L[R₁] M) : ⇑e.toContinuousAddEquiv = e := rfl

variable (R₁ M₁)

/-- The identity map as a continuous linear equivalence. -/
@[refl]
/-
**ContinuousLinearEquiv.refl** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearEquiv`。
形式化陈述：(R₁ : Type u_1) →   [inst : Semiring R₁] →     (M₁ : Type u_4) →       [in
st_1 : TopologicalSpace M₁] → [inst_2 : AddCommMonoid M₁] → [inst_3 : _root_.Mod
ule R₁ M₁] → M₁ ≃L[R₁] M₁
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity map as a continuous linear equivalence.
-/
protected def refl : M₁ ≃L[R₁] M₁ where
  __ := LinearEquiv.refl R₁ M₁

@[simp]
/-
**ContinuousLinearEquiv.refl_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearEq
uiv`。
形式化陈述：refl_apply (x : M₁) : ContinuousLinearEquiv.refl R₁ M₁ x = x
参数：x : M₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem refl_apply (x : M₁) :
    ContinuousLinearEquiv.refl R₁ M₁ x = x := rfl

end

@[simp, norm_cast]
/-
**ContinuousLinearEquiv.coe_refl** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearEqui
v`。
形式化陈述：coe_refl : ↑(ContinuousLinearEquiv.refl R₁ M₁) = ContinuousLinearMap.id R₁
 M₁
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_refl : ↑(ContinuousLinearEquiv.refl R₁ M₁) = ContinuousLinearMap.id R₁ M₁ :=
  rfl

@[simp, norm_cast]
/-
**ContinuousLinearEquiv.coe_refl'** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearEqu
iv`。
形式化陈述：coe_refl' : ⇑(ContinuousLinearEquiv.refl R₁ M₁) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_refl' : ⇑(ContinuousLinearEquiv.refl R₁ M₁) = id :=
  rfl

/-- The inverse of a continuous linear equivalence as a continuous linear equivalence -/
@[symm]
/-
**ContinuousLinearEquiv.symm** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearEquiv`。
形式化陈述：{R₁ : Type u_1} →   {R₂ : Type u_2} →     [inst : Semiring R₁] →       [in
st_1 : Semiring R₂] →         {σ₁₂ : R₁ →+* R₂} →           {σ₂₁ : R₂ →+* R₁} → 
            [inst_2 : RingHomInvPair σ₁₂ σ₂₁] →               [inst_3 : RingHomI
nvPair σ₂₁ σ₁₂] →                 {M₁ : Type u_4} →                   [inst_4 : 
TopologicalSpace M₁] →                     [inst_5 : AddCommMonoid M₁] →        
               {M₂ : Type u_5} →                         [inst_6 : TopologicalSp
ace M₂] →                           [inst_7 : AddCommMonoid M₂] →               
              [inst_8 : _root_.Module R₁ M₁] →                               [in
st_9 : _root_.Module R₂ M₂] → (M₁ ≃SL[σ₁₂] M₂) → M₂ ≃SL[σ₂₁] M₁
参数：M₁ ≃SL[σ₁₂] M₂。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearEquiv.continuous_invFun`：∀ {R : Type u_1} {S : Type u_2}
 [inst : Semiring R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_
2 : RingHomInvPair σ σ'] [ins…
· 使用定理 `ContinuousLinearEquiv.continuous_toFun`：∀ {R : Type u_1} {S : Type u_2} 
[inst : Semiring R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2
 : RingHomInvPair σ σ'] [ins…

--- 原说明 ---
The inverse of a continuous linear equivalence as a continuous linear equivalenc
e
-/
protected def symm (e : M₁ ≃SL[σ₁₂] M₂) : M₂ ≃SL[σ₂₁] M₁ :=
  { e.toLinearEquiv.symm with
    continuous_toFun := e.continuous_invFun
    continuous_invFun := e.continuous_toFun }

@[simp]
/-
**ContinuousLinearEquiv.toLinearEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `Continuous
LinearEquiv`。
形式化陈述：toLinearEquiv_symm (e : M₁ ≃SL[σ₁₂] M₂) : e.symm.toLinearEquiv = e.toLinea
rEquiv.symm
参数：e : M₁ ≃SL[σ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLinearEquiv_symm (e : M₁ ≃SL[σ₁₂] M₂) : e.symm.toLinearEquiv = e.toLinearEquiv.symm :=
  rfl

@[simp]
/-
**ContinuousLinearEquiv.coe_symm_toLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Contin
uousLinearEquiv`。
形式化陈述：coe_symm_toLinearEquiv (e : M₁ ≃SL[σ₁₂] M₂) : ⇑e.toLinearEquiv.symm = e.sy
mm
参数：e : M₁ ≃SL[σ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_symm_toLinearEquiv (e : M₁ ≃SL[σ₁₂] M₂) : ⇑e.toLinearEquiv.symm = e.symm :=
  rfl

@[simp]
/-
**ContinuousLinearEquiv.toHomeomorph_symm** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousL
inearEquiv`。
形式化陈述：toHomeomorph_symm (e : M₁ ≃SL[σ₁₂] M₂) : e.symm.toHomeomorph = e.toHomeomo
rph.symm
参数：e : M₁ ≃SL[σ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toHomeomorph_symm (e : M₁ ≃SL[σ₁₂] M₂) : e.symm.toHomeomorph = e.toHomeomorph.symm :=
  rfl

@[simp]
/-
**ContinuousLinearEquiv.coe_symm_toHomeomorph** 是 Mathlib 中的一个定理，位于命名空间 `Continu
ousLinearEquiv`。
形式化陈述：coe_symm_toHomeomorph (e : M₁ ≃SL[σ₁₂] M₂) : ⇑e.toHomeomorph.symm = e.symm
参数：e : M₁ ≃SL[σ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_symm_toHomeomorph (e : M₁ ≃SL[σ₁₂] M₂) : ⇑e.toHomeomorph.symm = e.symm :=
  rfl

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
/-
**ContinuousLinearEquiv.Simps.apply** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearE
quiv.Simps`。
形式化陈述：{R₁ : Type u_1} →   {R₂ : Type u_2} →     [inst : Semiring R₁] →       [in
st_1 : Semiring R₂] →         {σ₁₂ : R₁ →+* R₂} →           {σ₂₁ : R₂ →+* R₁} → 
            [inst_2 : RingHomInvPair σ₁₂ σ₂₁] →               [inst_3 : RingHomI
nvPair σ₂₁ σ₁₂] →                 {M₁ : Type u_4} →                   [inst_4 : 
TopologicalSpace M₁] →                     [inst_5 : AddCommMonoid M₁] →        
               {M₂ : Type u_5} →                         [inst_6 : TopologicalSp
ace M₂] →                           [inst_7 : AddCommMonoid M₂] →               
              [inst_8 : _root_.Module R₁ M₁] → [inst_9 : _root_.Module R₂ M₂] → 
(M₁ ≃SL[σ₁₂] M₂) → M₁ → M₂
参数：M₁ ≃SL[σ₁₂] M₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection]. We need to specify this projection explicitl
y in this case,
  because it is a composition of multiple projections.
-/
def Simps.apply (h : M₁ ≃SL[σ₁₂] M₂) : M₁ → M₂ :=
  h

/-- See Note [custom simps projection] -/
/-
**ContinuousLinearEquiv.Simps.symm_apply** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLi
nearEquiv.Simps`。
形式化陈述：{R₁ : Type u_1} →   {R₂ : Type u_2} →     [inst : Semiring R₁] →       [in
st_1 : Semiring R₂] →         {σ₁₂ : R₁ →+* R₂} →           {σ₂₁ : R₂ →+* R₁} → 
            [inst_2 : RingHomInvPair σ₁₂ σ₂₁] →               [inst_3 : RingHomI
nvPair σ₂₁ σ₁₂] →                 {M₁ : Type u_4} →                   [inst_4 : 
TopologicalSpace M₁] →                     [inst_5 : AddCommMonoid M₁] →        
               {M₂ : Type u_5} →                         [inst_6 : TopologicalSp
ace M₂] →                           [inst_7 : AddCommMonoid M₂] →               
              [inst_8 : _root_.Module R₁ M₁] → [inst_9 : _root_.Module R₂ M₂] → 
(M₁ ≃SL[σ₁₂] M₂) → M₂ → M₁
参数：M₁ ≃SL[σ₁₂] M₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection]
-/
def Simps.symm_apply (h : M₁ ≃SL[σ₁₂] M₂) : M₂ → M₁ :=
  h.symm

initialize_simps_projections ContinuousLinearEquiv (toFun → apply, invFun → symm_apply)
/-
**ContinuousLinearEquiv.symm_map_nhds_eq** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLi
nearEquiv`。
形式化陈述：symm_map_nhds_eq (e : M₁ ≃SL[σ₁₂] M₂) (x : M₁) : map e.symm (𝓝 (e x)) = 𝓝 
x
参数：e : M₁ ≃SL[σ₁₂] M₂；x : M₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.symm_map_nhds_eq`：symm_map_nhds_eq (h : X ≃ₜ Y) (x : X) : map
 h.symm (𝓝 (h x)) = 𝓝 x
-/
theorem symm_map_nhds_eq (e : M₁ ≃SL[σ₁₂] M₂) (x : M₁) : map e.symm (𝓝 (e x)) = 𝓝 x :=
  e.toHomeomorph.symm_map_nhds_eq x

/-- The composition of two continuous linear equivalences as a continuous linear equivalence. -/
@[trans]
/-
**ContinuousLinearEquiv.trans** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearEquiv`。
形式化陈述：{R₁ : Type u_1} →   {R₂ : Type u_2} →     {R₃ : Type u_3} →       [inst : 
Semiring R₁] →         [inst_1 : Semiring R₂] →           [inst_2 : Semiring R₃]
 →             {σ₁₂ : R₁ →+* R₂} →               {σ₂₁ : R₂ →+* R₁} →            
     [inst_3 : RingHomInvPair σ₁₂ σ₂₁] →                   [inst_4 : RingHomInvP
air σ₂₁ σ₁₂] →                     {σ₂₃ : R₂ →+* R₃} →                       {σ₃
₂ : R₃ →+* R₂} →                         [inst_5 : RingHomInvPair σ₂₃ σ₃₂] →    
                       [inst_6 : RingHomInvPair σ₃₂ σ₂₃] →                      
       {σ₁₃ : R₁ →+* R₃} →                               {σ₃₁ : R₃ →+* R₁} →    
                             [inst_7 : RingHomInvPair σ₁₃ σ₃₁] →                
                   [inst_8 : RingHomInvPair σ₃₁ σ₁₃] →                          
           [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] →                                    
   [RingHomCompTriple σ₃₂ σ₂₁ σ₃₁] →                                         {M₁
 : Type u_4} →                                           [inst_11 : TopologicalS
pace M₁] →                                             [inst_12 : AddCommMonoid 
M₁] →                                               {M₂ : Type u_5} →           
                                      [inst_13 : TopologicalSpace M₂] →         
                                          [inst_14 : AddCommMonoid M₂] →        
                                             {M₃ : Type u_6} →                  
                                     [inst_15 : TopologicalSpace M₃] →          
                                               [inst_16 : AddCommMonoid M₃] →   
                                                        [inst_17 : _root_.Module
 R₁ M₁] →                                                             [inst_18 :
 _root_.Module R₂ M₂] →                                                         
      [inst_19 : _root_.Module R₃ M₃] →                                         
                        (M₁ ≃SL[σ₁₂] M₂) → (M₂ ≃SL[σ₂₃] M₃) → M₁ ≃SL[σ₁₃] M₃
参数：M₁ ≃SL[σ₁₂] M₂；M₂ ≃SL[σ₂₃] M₃。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of two continuous linear equivalences as a continuous linear equ
ivalence.
-/
protected def trans (e₁ : M₁ ≃SL[σ₁₂] M₂) (e₂ : M₂ ≃SL[σ₂₃] M₃) : M₁ ≃SL[σ₁₃] M₃ where
  __ := e₁.toLinearEquiv.trans e₂.toLinearEquiv

@[simp]
/-
**ContinuousLinearEquiv.trans_toLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Continuou
sLinearEquiv`。
形式化陈述：trans_toLinearEquiv (e₁ : M₁ ≃SL[σ₁₂] M₂) (e₂ : M₂ ≃SL[σ₂₃] M₃) : (e₁.tran
s e₂).toLinearEquiv = e₁.toLinearEquiv.trans e₂.toLinearEquiv
参数：e₁ : M₁ ≃SL[σ₁₂] M₂；e₂ : M₂ ≃SL[σ₂₃] M₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.ext`：ext (h : forall x, e x = e' x) : e = e'
-/
theorem trans_toLinearEquiv (e₁ : M₁ ≃SL[σ₁₂] M₂) (e₂ : M₂ ≃SL[σ₂₃] M₃) :
    (e₁.trans e₂).toLinearEquiv = e₁.toLinearEquiv.trans e₂.toLinearEquiv := by
  ext
  rfl

/-- Product of two continuous linear equivalences. The map comes from `Equiv.prodCongr`. -/
/-
**ContinuousLinearEquiv.prodCongr** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearEqu
iv`。
形式化陈述：prodCongr [Module R₁ M₂] [Module R₁ M₃] [Module R₁ M₄] (e : M₁ ≃L[R₁] M₂) 
(e' : M₃ ≃L[R₁] M₄) : (M₁ × M₃) ≃L[R₁] M₂ × M₄ where __
参数：e : M₁ ≃L[R₁] M₂；e' : M₃ ≃L[R₁] M₄。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Product of two continuous linear equivalences. The map comes from `Equiv.prodCon
gr`.
-/
def prodCongr [Module R₁ M₂] [Module R₁ M₃] [Module R₁ M₄] (e : M₁ ≃L[R₁] M₂) (e' : M₃ ≃L[R₁] M₄) :
    (M₁ × M₃) ≃L[R₁] M₂ × M₄ where
  __ := e.toLinearEquiv.prodCongr e'.toLinearEquiv

@[simp, norm_cast]
/-
**ContinuousLinearEquiv.prodCongr_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLin
earEquiv`。
形式化陈述：prodCongr_apply [Module R₁ M₂] [Module R₁ M₃] [Module R₁ M₄] (e : M₁ ≃L[R₁
] M₂) (e' : M₃ ≃L[R₁] M₄) (x) : e.prodCongr e' x = (e x.1, e' x.2)
参数：e : M₁ ≃L[R₁] M₂；e' : M₃ ≃L[R₁] M₄；x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prodCongr_apply [Module R₁ M₂] [Module R₁ M₃] [Module R₁ M₄] (e : M₁ ≃L[R₁] M₂)
    (e' : M₃ ≃L[R₁] M₄) (x) : e.prodCongr e' x = (e x.1, e' x.2) :=
  rfl

@[simp, norm_cast]
/-
**ContinuousLinearEquiv.coe_prodCongr** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinea
rEquiv`。
形式化陈述：coe_prodCongr [Module R₁ M₂] [Module R₁ M₃] [Module R₁ M₄] (e : M₁ ≃L[R₁] 
M₂) (e' : M₃ ≃L[R₁] M₄) : (e.prodCongr e' : M₁ × M₃ ->L[R₁] M₂ × M₄) = (e : M₁ -
>L[R₁] M₂).prodMap (e' : M₃ ->L[R₁] M₄)
参数：e : M₁ ≃L[R₁] M₂；e' : M₃ ≃L[R₁] M₄。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_prodCongr [Module R₁ M₂] [Module R₁ M₃] [Module R₁ M₄] (e : M₁ ≃L[R₁] M₂)
    (e' : M₃ ≃L[R₁] M₄) :
    (e.prodCongr e' : M₁ × M₃ →L[R₁] M₂ × M₄) = (e : M₁ →L[R₁] M₂).prodMap (e' : M₃ →L[R₁] M₄) :=
  rfl

@[simp]
/-
**ContinuousLinearEquiv.prodCongr_symm** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLine
arEquiv`。
形式化陈述：prodCongr_symm [Module R₁ M₂] [Module R₁ M₃] [Module R₁ M₄] (e : M₁ ≃L[R₁]
 M₂) (e' : M₃ ≃L[R₁] M₄) : (e.prodCongr e').symm = e.symm.prodCongr e'.symm
参数：e : M₁ ≃L[R₁] M₂；e' : M₃ ≃L[R₁] M₄。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prodCongr_symm [Module R₁ M₂] [Module R₁ M₃] [Module R₁ M₄] (e : M₁ ≃L[R₁] M₂)
    (e' : M₃ ≃L[R₁] M₄) : (e.prodCongr e').symm = e.symm.prodCongr e'.symm :=
  rfl

variable (R₁ M₁ M₂)

set_option backward.defeqAttrib.useBackward true in
/-- Product of topological modules is commutative up to continuous linear isomorphism. -/
@[simps! apply toLinearEquiv]
/-
**ContinuousLinearEquiv.prodComm** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearEqui
v`。
形式化陈述：prodComm [Module R₁ M₂] : (M₁ × M₂) ≃L[R₁] M₂ × M₁ where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Product of topological modules is commutative up to continuous linear isomorphis
m.
-/
def prodComm [Module R₁ M₂] : (M₁ × M₂) ≃L[R₁] M₂ × M₁ where
  __ := LinearEquiv.prodComm R₁ M₁ M₂
/-
**ContinuousLinearEquiv.prodComm_symm** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinea
rEquiv`。
形式化陈述：∀ (R₁ : Type u_1) [inst : Semiring R₁] (M₁ : Type u_4) [inst_1 : Topologic
alSpace M₁] [inst_2 : AddCommMonoid M₁]   (M₂ : Type u_5) [inst_3 : TopologicalS
pace M₂] [inst_4 : AddCommMonoid M₂] [inst_5 : _root_.Module R₁ M₁]   [inst_6 : 
_root_.Module R₁ M₂],   (ContinuousLinearEquiv.prodComm R₁ M₁ M₂).symm = Continu
ousLinearEquiv.prodComm R₁ M₂ M₁
参数：R₁ : Type u_1；M₁ : Type u_4；M₂ : Type u_5；ContinuousLinearEquiv.prodComm R₁ M
₁ M₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma prodComm_symm [Module R₁ M₂] : (prodComm R₁ M₁ M₂).symm = prodComm R₁ M₂ M₁ := rfl

section prodAssoc

variable (R M₁ M₂ M₃ : Type*) [Semiring R]
  [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃] [Module R M₁] [Module R M₂] [Module R M₃]
  [TopologicalSpace M₁] [TopologicalSpace M₂] [TopologicalSpace M₃]

/-- The product of topological modules is associative up to continuous linear isomorphism.
This is `LinearEquiv.prodAssoc` prodAssoc as a continuous linear equivalence. -/
/-
**ContinuousLinearEquiv.prodAssoc** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearEqu
iv`。
形式化陈述：prodAssoc : ((M₁ × M₂) × M₃) ≃L[R] M₁ × M₂ × M₃ where toLinearEquiv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of topological modules is associative up to continuous linear isomor
phism.
This is `LinearEquiv.prodAssoc` prodAssoc as a continuous linear equivalence.
-/
def prodAssoc : ((M₁ × M₂) × M₃) ≃L[R] M₁ × M₂ × M₃ where
  toLinearEquiv := LinearEquiv.prodAssoc R M₁ M₂ M₃
  continuous_toFun := (continuous_fst.comp continuous_fst).prodMk
    ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
  continuous_invFun := (continuous_fst.prodMk (continuous_fst.comp continuous_snd)).prodMk
    (continuous_snd.comp continuous_snd)

@[simp]
/-
**ContinuousLinearEquiv.prodAssoc_toLinearEquiv** 是 Mathlib 中的一个引理，位于命名空间 `Conti
nuousLinearEquiv`。
形式化陈述：prodAssoc_toLinearEquiv : (prodAssoc R M₁ M₂ M₃).toLinearEquiv = LinearEqu
iv.prodAssoc R M₁ M₂ M₃
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma prodAssoc_toLinearEquiv :
    (prodAssoc R M₁ M₂ M₃).toLinearEquiv = LinearEquiv.prodAssoc R M₁ M₂ M₃ := rfl

@[simp]
/-
**ContinuousLinearEquiv.coe_prodAssoc** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLinea
rEquiv`。
形式化陈述：coe_prodAssoc : (prodAssoc R M₁ M₂ M₃ : (M₁ × M₂) × M₃ -> M₁ × M₂ × M₃) = 
Equiv.prodAssoc M₁ M₂ M₃
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_prodAssoc :
    (prodAssoc R M₁ M₂ M₃ : (M₁ × M₂) × M₃ → M₁ × M₂ × M₃) = Equiv.prodAssoc M₁ M₂ M₃ := rfl

@[simp]
/-
**ContinuousLinearEquiv.prodAssoc_apply** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLin
earEquiv`。
形式化陈述：prodAssoc_apply (p₁ : M₁) (p₂ : M₂) (p₃ : M₃) : prodAssoc R M₁ M₂ M₃ ((p₁,
 p₂), p₃) = (p₁, (p₂, p₃))
参数：p₁ : M₁；p₂ : M₂；p₃ : M₃。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma prodAssoc_apply (p₁ : M₁) (p₂ : M₂) (p₃ : M₃) :
    prodAssoc R M₁ M₂ M₃ ((p₁, p₂), p₃) = (p₁, (p₂, p₃)) := rfl

@[simp]
/-
**ContinuousLinearEquiv.prodAssoc_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `Continuo
usLinearEquiv`。
形式化陈述：prodAssoc_symm_apply (p₁ : M₁) (p₂ : M₂) (p₃ : M₃) : (prodAssoc R M₁ M₂ M₃
).symm (p₁, (p₂, p₃)) = ((p₁, p₂), p₃)
参数：p₁ : M₁；p₂ : M₂；p₃ : M₃。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma prodAssoc_symm_apply (p₁ : M₁) (p₂ : M₂) (p₃ : M₃) :
    (prodAssoc R M₁ M₂ M₃).symm (p₁, (p₂, p₃)) = ((p₁, p₂), p₃) := rfl

end prodAssoc

section prodProdProdComm

variable (R M₁ M₂ M₃ M₄ : Type*) [Semiring R]
  [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃] [AddCommMonoid M₄]
  [Module R M₁] [Module R M₂] [Module R M₃] [Module R M₄]
  [TopologicalSpace M₁] [TopologicalSpace M₂] [TopologicalSpace M₃] [TopologicalSpace M₄]

/-- The product of topological modules is four-way commutative up to continuous linear isomorphism.
This is `LinearEquiv.prodProdProdComm` prodAssoc as a continuous linear equivalence. -/
/-
**ContinuousLinearEquiv.prodProdProdComm** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLi
nearEquiv`。
形式化陈述：prodProdProdComm : ((M₁ × M₂) × M₃ × M₄) ≃L[R] (M₁ × M₃) × M₂ × M₄ where t
oLinearEquiv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of topological modules is four-way commutative up to continuous line
ar isomorphism.
This is `LinearEquiv.prodProdProdComm` prodAssoc as a continuous linear equivale
nce.
-/
def prodProdProdComm : ((M₁ × M₂) × M₃ × M₄) ≃L[R] (M₁ × M₃) × M₂ × M₄ where
  toLinearEquiv := LinearEquiv.prodProdProdComm R M₁ M₂ M₃ M₄

@[simp]
/-
**ContinuousLinearEquiv.prodProdProdComm_symm** 是 Mathlib 中的一个定理，位于命名空间 `Continu
ousLinearEquiv`。
形式化陈述：prodProdProdComm_symm : (prodProdProdComm R M₁ M₂ M₃ M₄).symm = prodProdPr
odComm R M₁ M₃ M₂ M₄
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prodProdProdComm_symm :
    (prodProdProdComm R M₁ M₂ M₃ M₄).symm = prodProdProdComm R M₁ M₃ M₂ M₄ :=
  rfl

@[simp]
/-
**ContinuousLinearEquiv.prodProdProdComm_toLinearEquiv** 是 Mathlib 中的一个引理，位于命名空间
 `ContinuousLinearEquiv`。
形式化陈述：prodProdProdComm_toLinearEquiv : (prodProdProdComm R M₁ M₂ M₃ M₄).toLinear
Equiv = LinearEquiv.prodProdProdComm R M₁ M₂ M₃ M₄
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma prodProdProdComm_toLinearEquiv :
    (prodProdProdComm R M₁ M₂ M₃ M₄).toLinearEquiv = LinearEquiv.prodProdProdComm R M₁ M₂ M₃ M₄ :=
  rfl

@[simp]
/-
**ContinuousLinearEquiv.coe_prodProdProdComm** 是 Mathlib 中的一个引理，位于命名空间 `Continuo
usLinearEquiv`。
形式化陈述：coe_prodProdProdComm : (prodProdProdComm R M₁ M₂ M₃ M₄ : (M₁ × M₂) × M₃ × 
M₄ -> (M₁ × M₃) × M₂ × M₄) = Equiv.prodProdProdComm M₁ M₂ M₃ M₄
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_prodProdProdComm :
    (prodProdProdComm R M₁ M₂ M₃ M₄ : (M₁ × M₂) × M₃ × M₄ → (M₁ × M₃) × M₂ × M₄) =
      Equiv.prodProdProdComm M₁ M₂ M₃ M₄ := rfl

@[simp]
/-
**ContinuousLinearEquiv.prodProdProdComm_apply** 是 Mathlib 中的一个引理，位于命名空间 `Contin
uousLinearEquiv`。
形式化陈述：prodProdProdComm_apply (p₁ : M₁) (p₂ : M₂) (p₃ : M₃) (p₄ : M₄) : prodProdP
rodComm R M₁ M₂ M₃ M₄ ((p₁, p₂), p₃, p₄) = ((p₁, p₃), p₂, p₄)
参数：p₁ : M₁；p₂ : M₂；p₃ : M₃；p₄ : M₄。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma prodProdProdComm_apply (p₁ : M₁) (p₂ : M₂) (p₃ : M₃) (p₄ : M₄) :
    prodProdProdComm R M₁ M₂ M₃ M₄ ((p₁, p₂), p₃, p₄) = ((p₁, p₃), p₂, p₄) := rfl

end prodProdProdComm

section prodUnique

variable (R M N : Type*) [Semiring R]
  [TopologicalSpace M] [AddCommMonoid M] [TopologicalSpace N] [AddCommMonoid N]
  [Unique N] [Module R M] [Module R N]

set_option backward.defeqAttrib.useBackward true in
/-- The natural equivalence `M × N ≃L[R] M` for any `Unique` type `N`.
This is `Equiv.prodUnique` as a continuous linear equivalence. -/
/-
**ContinuousLinearEquiv.prodUnique** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearEq
uiv`。
形式化陈述：prodUnique : (M × N) ≃L[R] M where toLinearEquiv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural equivalence `M × N ≃L[R] M` for any `Unique` type `N`.
This is `Equiv.prodUnique` as a continuous linear equivalence.
-/
def prodUnique : (M × N) ≃L[R] M where
  toLinearEquiv := LinearEquiv.prodUnique

@[simp]
/-
**ContinuousLinearEquiv.coe_prodUnique** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLine
arEquiv`。
形式化陈述：coe_prodUnique : (prodUnique R M N).toEquiv = Equiv.prodUnique M N
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_prodUnique : (prodUnique R M N).toEquiv = Equiv.prodUnique M N := rfl

@[simp]
/-
**ContinuousLinearEquiv.prodUnique_apply** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLi
nearEquiv`。
形式化陈述：prodUnique_apply (x : M × N) : prodUnique R M N x = x.1
参数：x : M × N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma prodUnique_apply (x : M × N) : prodUnique R M N x = x.1 := rfl

@[simp]
/-
**ContinuousLinearEquiv.prodUnique_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `Continu
ousLinearEquiv`。
形式化陈述：prodUnique_symm_apply (x : M) : (prodUnique R M N).symm x = (x, default)
参数：x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma prodUnique_symm_apply (x : M) : (prodUnique R M N).symm x = (x, default) := rfl

set_option backward.defeqAttrib.useBackward true in
/-- The natural equivalence `N × M ≃L[R] M` for any `Unique` type `N`.
This is `Equiv.uniqueProd` as a continuous linear equivalence. -/
/-
**ContinuousLinearEquiv.uniqueProd** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearEq
uiv`。
形式化陈述：uniqueProd : (N × M) ≃L[R] M where toLinearEquiv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural equivalence `N × M ≃L[R] M` for any `Unique` type `N`.
This is `Equiv.uniqueProd` as a continuous linear equivalence.
-/
def uniqueProd : (N × M) ≃L[R] M where
  toLinearEquiv := LinearEquiv.uniqueProd

@[simp]
/-
**ContinuousLinearEquiv.coe_uniqueProd** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLine
arEquiv`。
形式化陈述：coe_uniqueProd : (uniqueProd R M N).toEquiv = Equiv.uniqueProd M N
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_uniqueProd : (uniqueProd R M N).toEquiv = Equiv.uniqueProd M N := rfl

@[simp]
/-
**ContinuousLinearEquiv.uniqueProd_apply** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLi
nearEquiv`。
形式化陈述：uniqueProd_apply (x : N × M) : uniqueProd R M N x = x.2
参数：x : N × M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma uniqueProd_apply (x : N × M) : uniqueProd R M N x = x.2 := rfl

@[simp]
/-
**ContinuousLinearEquiv.uniqueProd_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `Continu
ousLinearEquiv`。
形式化陈述：uniqueProd_symm_apply (x : M) : (uniqueProd R M N).symm x = (default, x)
参数：x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma uniqueProd_symm_apply (x : M) : (uniqueProd R M N).symm x = (default, x) := rfl

end prodUnique

variable {R₁ M₁ M₂}

/-
**ContinuousLinearEquiv.bijective** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearEqu
iv`。
形式化陈述：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Semiring R₁] [inst_1 : Semiring 
R₂] {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁}   [inst_2 : RingHomInvPair σ₁₂ σ₂₁] [ins
t_3 : RingHomInvPair σ₂₁ σ₁₂] {M₁ : Type u_4} [inst_4 : TopologicalSpace M₁]   [
inst_5 : AddCommMonoid M₁] {M₂ : Type u_5} [inst_6 : TopologicalSpace M₂] [inst_
7 : AddCommMonoid M₂]   [inst_8 : _root_.Module R₁ M₁] [inst_9 : _root_.Module R
₂ M₂] (e : M₁ ≃SL[σ₁₂] M₂), Function.Bijective ⇑e
参数：e : M₁ ≃SL[σ₁₂] M₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
-/
protected theorem bijective (e : M₁ ≃SL[σ₁₂] M₂) : Function.Bijective e :=
  e.toLinearEquiv.toEquiv.bijective
/-
**ContinuousLinearEquiv.injective** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearEqu
iv`。
形式化陈述：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Semiring R₁] [inst_1 : Semiring 
R₂] {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁}   [inst_2 : RingHomInvPair σ₁₂ σ₂₁] [ins
t_3 : RingHomInvPair σ₂₁ σ₁₂] {M₁ : Type u_4} [inst_4 : TopologicalSpace M₁]   [
inst_5 : AddCommMonoid M₁] {M₂ : Type u_5} [inst_6 : TopologicalSpace M₂] [inst_
7 : AddCommMonoid M₂]   [inst_8 : _root_.Module R₁ M₁] [inst_9 : _root_.Module R
₂ M₂] (e : M₁ ≃SL[σ₁₂] M₂), Function.Injective ⇑e
参数：e : M₁ ≃SL[σ₁₂] M₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
protected theorem injective (e : M₁ ≃SL[σ₁₂] M₂) : Function.Injective e :=
  e.toLinearEquiv.toEquiv.injective
/-
**ContinuousLinearEquiv.surjective** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearEq
uiv`。
形式化陈述：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Semiring R₁] [inst_1 : Semiring 
R₂] {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁}   [inst_2 : RingHomInvPair σ₁₂ σ₂₁] [ins
t_3 : RingHomInvPair σ₂₁ σ₁₂] {M₁ : Type u_4} [inst_4 : TopologicalSpace M₁]   [
inst_5 : AddCommMonoid M₁] {M₂ : Type u_5} [inst_6 : TopologicalSpace M₂] [inst_
7 : AddCommMonoid M₂]   [inst_8 : _root_.Module R₁ M₁] [inst_9 : _root_.Module R
₂ M₂] (e : M₁ ≃SL[σ₁₂] M₂), Function.Surjective ⇑e
参数：e : M₁ ≃SL[σ₁₂] M₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
-/
protected theorem surjective (e : M₁ ≃SL[σ₁₂] M₂) : Function.Surjective e :=
  e.toLinearEquiv.toEquiv.surjective

@[simp]
/-
**ContinuousLinearEquiv.trans_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearE
quiv`。
形式化陈述：trans_apply (e₁ : M₁ ≃SL[σ₁₂] M₂) (e₂ : M₂ ≃SL[σ₂₃] M₃) (c : M₁) : (e₁.tra
ns e₂) c = e₂ (e₁ c)
参数：e₁ : M₁ ≃SL[σ₁₂] M₂；e₂ : M₂ ≃SL[σ₂₃] M₃；c : M₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trans_apply (e₁ : M₁ ≃SL[σ₁₂] M₂) (e₂ : M₂ ≃SL[σ₂₃] M₃) (c : M₁) :
    (e₁.trans e₂) c = e₂ (e₁ c) :=
  rfl

@[simp]
/-
**ContinuousLinearEquiv.apply_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLi
nearEquiv`。
形式化陈述：apply_symm_apply (e : M₁ ≃SL[σ₁₂] M₂) (c : M₂) : e (e.symm c) = c
参数：e : M₁ ≃SL[σ₁₂] M₂；c : M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.right_inv`：∀ {R : Type u_14} {S : Type u_15} [inst : Semirin
g R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2 : RingHomInvPa
ir σ σ'] [i…
-/
theorem apply_symm_apply (e : M₁ ≃SL[σ₁₂] M₂) (c : M₂) : e (e.symm c) = c :=
  e.1.right_inv c

@[simp]
/-
**ContinuousLinearEquiv.symm_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLi
nearEquiv`。
形式化陈述：symm_apply_apply (e : M₁ ≃SL[σ₁₂] M₂) (b : M₁) : e.symm (e b) = b
参数：e : M₁ ≃SL[σ₁₂] M₂；b : M₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.left_inv`：∀ {R : Type u_14} {S : Type u_15} [inst : Semiring
 R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2 : RingHomInvPai
r σ σ'] [i…
-/
theorem symm_apply_apply (e : M₁ ≃SL[σ₁₂] M₂) (b : M₁) : e.symm (e b) = b :=
  e.1.left_inv b
/-
**ContinuousLinearEquiv.symm_trans_self** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLin
earEquiv`。
形式化陈述：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Semiring R₁] [inst_1 : Semiring 
R₂] {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁}   [inst_2 : RingHomInvPair σ₁₂ σ₂₁] [ins
t_3 : RingHomInvPair σ₂₁ σ₁₂] {M₁ : Type u_4} [inst_4 : TopologicalSpace M₁]   [
inst_5 : AddCommMonoid M₁] {M₂ : Type u_5} [inst_6 : TopologicalSpace M₂] [inst_
7 : AddCommMonoid M₂]   [inst_8 : _root_.Module R₁ M₁] [inst_9 : _root_.Module R
₂ M₂] (e : M₁ ≃SL[σ₁₂] M₂),   e.symm.trans e = ContinuousLinearEquiv.refl R₂ M₂
参数：e : M₁ ≃SL[σ₁₂] M₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearEquiv.ext`：ext {f g : M₁ ≃SL[σ₁₂] M₂} (h : (f : M₁ -> M₂
) = g) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousLinearEquiv.apply_symm_apply`：apply_symm_apply (e : M₁ ≃SL[σ₁₂
] M₂) (c : M₂) : e (e.symm c) = c
-/
@[simp] theorem symm_trans_self (e : M₁ ≃SL[σ₁₂] M₂) : e.symm.trans e = .refl R₂ M₂ :=
  ext <| funext fun _ ↦ apply_symm_apply _ _
/-
**ContinuousLinearEquiv.self_trans_symm** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLin
earEquiv`。
形式化陈述：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Semiring R₁] [inst_1 : Semiring 
R₂] {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁}   [inst_2 : RingHomInvPair σ₁₂ σ₂₁] [ins
t_3 : RingHomInvPair σ₂₁ σ₁₂] {M₁ : Type u_4} [inst_4 : TopologicalSpace M₁]   [
inst_5 : AddCommMonoid M₁] {M₂ : Type u_5} [inst_6 : TopologicalSpace M₂] [inst_
7 : AddCommMonoid M₂]   [inst_8 : _root_.Module R₁ M₁] [inst_9 : _root_.Module R
₂ M₂] (e : M₁ ≃SL[σ₁₂] M₂),   e.trans e.symm = ContinuousLinearEquiv.refl R₁ M₁
参数：e : M₁ ≃SL[σ₁₂] M₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearEquiv.ext`：ext {f g : M₁ ≃SL[σ₁₂] M₂} (h : (f : M₁ -> M₂
) = g) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousLinearEquiv.symm_apply_apply`：symm_apply_apply (e : M₁ ≃SL[σ₁₂
] M₂) (b : M₁) : e.symm (e b) = b
-/
@[simp] theorem self_trans_symm (e : M₁ ≃SL[σ₁₂] M₂) : e.trans e.symm = .refl R₁ M₁ :=
  ext <| funext fun _ ↦ symm_apply_apply _ _

@[simp]
/-
**ContinuousLinearEquiv.symm_trans_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLi
nearEquiv`。
形式化陈述：symm_trans_apply (e₁ : M₂ ≃SL[σ₂₁] M₁) (e₂ : M₃ ≃SL[σ₃₂] M₂) (c : M₁) : (e
₂.trans e₁).symm c = e₂.symm (e₁.symm c)
参数：e₁ : M₂ ≃SL[σ₂₁] M₁；e₂ : M₃ ≃SL[σ₃₂] M₂；c : M₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_trans_apply (e₁ : M₂ ≃SL[σ₂₁] M₁) (e₂ : M₃ ≃SL[σ₃₂] M₂) (c : M₁) :
    (e₂.trans e₁).symm c = e₂.symm (e₁.symm c) :=
  rfl

@[simp]
/-
**ContinuousLinearEquiv.symm_image_image** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLi
nearEquiv`。
形式化陈述：symm_image_image (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₁) : e.symm '' e '' s = s
参数：e : M₁ ≃SL[σ₁₂] M₂；s : Set M₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm_image_image`：symm_image_image {α β} (e : α ≃ β) (s : Set α) :
 e.symm '' e '' s = s
-/
theorem symm_image_image (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₁) : e.symm '' e '' s = s :=
  e.toLinearEquiv.toEquiv.symm_image_image s

@[simp]
/-
**ContinuousLinearEquiv.image_symm_image** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLi
nearEquiv`。
形式化陈述：image_symm_image (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₂) : e '' e.symm '' s = s
参数：e : M₁ ≃SL[σ₁₂] M₂；s : Set M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearEquiv.symm_image_image`：symm_image_image (e : M₁ ≃SL[σ₁₂
] M₂) (s : Set M₁) : e.symm '' e '' s = s
-/
theorem image_symm_image (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₂) : e '' e.symm '' s = s :=
  e.symm.symm_image_image s

@[simp, norm_cast]
/-
**ContinuousLinearEquiv.comp_coe** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearEqui
v`。
形式化陈述：comp_coe (f : M₁ ≃SL[σ₁₂] M₂) (f' : M₂ ≃SL[σ₂₃] M₃) : (f' : M₂ ->SL[σ₂₃] M
₃).comp (f : M₁ ->SL[σ₁₂] M₂) = (f.trans f' : M₁ ->SL[σ₁₃] M₃)
参数：f : M₁ ≃SL[σ₁₂] M₂；f' : M₂ ≃SL[σ₂₃] M₃。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_coe (f : M₁ ≃SL[σ₁₂] M₂) (f' : M₂ ≃SL[σ₂₃] M₃) :
    (f' : M₂ →SL[σ₂₃] M₃).comp (f : M₁ →SL[σ₁₂] M₂) = (f.trans f' : M₁ →SL[σ₁₃] M₃) :=
  rfl

-- The priority should be higher than `comp_coe`.
@[simp high]
/-
**ContinuousLinearEquiv.coe_comp_coe_symm** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousL
inearEquiv`。
形式化陈述：coe_comp_coe_symm (e : M₁ ≃SL[σ₁₂] M₂) : (e : M₁ ->SL[σ₁₂] M₂).comp (e.sym
m : M₂ ->SL[σ₂₁] M₁) = ContinuousLinearMap.id R₂ M₂
参数：e : M₁ ≃SL[σ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `ContinuousLinearEquiv.apply_symm_apply`：apply_symm_apply (e : M₁ ≃SL[σ₁₂
] M₂) (c : M₂) : e (e.symm c) = c
-/
theorem coe_comp_coe_symm (e : M₁ ≃SL[σ₁₂] M₂) :
    (e : M₁ →SL[σ₁₂] M₂).comp (e.symm : M₂ →SL[σ₂₁] M₁) = ContinuousLinearMap.id R₂ M₂ :=
  ContinuousLinearMap.ext e.apply_symm_apply

-- The priority should be higher than `comp_coe`.
@[simp high]
/-
**ContinuousLinearEquiv.coe_symm_comp_coe** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousL
inearEquiv`。
形式化陈述：coe_symm_comp_coe (e : M₁ ≃SL[σ₁₂] M₂) : (e.symm : M₂ ->SL[σ₂₁] M₁).comp (
e : M₁ ->SL[σ₁₂] M₂) = ContinuousLinearMap.id R₁ M₁
参数：e : M₁ ≃SL[σ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `ContinuousLinearEquiv.symm_apply_apply`：symm_apply_apply (e : M₁ ≃SL[σ₁₂
] M₂) (b : M₁) : e.symm (e b) = b
-/
theorem coe_symm_comp_coe (e : M₁ ≃SL[σ₁₂] M₂) :
    (e.symm : M₂ →SL[σ₂₁] M₁).comp (e : M₁ →SL[σ₁₂] M₂) = ContinuousLinearMap.id R₁ M₁ :=
  ContinuousLinearMap.ext e.symm_apply_apply

@[simp]
/-
**ContinuousLinearEquiv.symm_comp_self** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLine
arEquiv`。
形式化陈述：symm_comp_self (e : M₁ ≃SL[σ₁₂] M₂) : (e.symm : M₂ -> M₁) ∘ (e : M₁ -> M₂)
 = id
参数：e : M₁ ≃SL[σ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousLinearEquiv.symm_apply_apply`：symm_apply_apply (e : M₁ ≃SL[σ₁₂
] M₂) (b : M₁) : e.symm (e b) = b
-/
theorem symm_comp_self (e : M₁ ≃SL[σ₁₂] M₂) : (e.symm : M₂ → M₁) ∘ (e : M₁ → M₂) = id := by
  ext x
  exact symm_apply_apply e x

@[simp]
/-
**ContinuousLinearEquiv.self_comp_symm** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLine
arEquiv`。
形式化陈述：self_comp_symm (e : M₁ ≃SL[σ₁₂] M₂) : (e : M₁ -> M₂) ∘ (e.symm : M₂ -> M₁)
 = id
参数：e : M₁ ≃SL[σ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousLinearEquiv.apply_symm_apply`：apply_symm_apply (e : M₁ ≃SL[σ₁₂
] M₂) (c : M₂) : e (e.symm c) = c
-/
theorem self_comp_symm (e : M₁ ≃SL[σ₁₂] M₂) : (e : M₁ → M₂) ∘ (e.symm : M₂ → M₁) = id := by
  ext x
  exact apply_symm_apply e x

@[simp]
/-
**ContinuousLinearEquiv.symm_symm** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearEqu
iv`。
形式化陈述：symm_symm (e : M₁ ≃SL[σ₁₂] M₂) : e.symm.symm = e
参数：e : M₁ ≃SL[σ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_symm (e : M₁ ≃SL[σ₁₂] M₂) : e.symm.symm = e := rfl
/-
**ContinuousLinearEquiv.symm_bijective** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLine
arEquiv`。
形式化陈述：symm_bijective : Function.Bijective (ContinuousLinearEquiv.symm : (M₁ ≃SL[
σ₁₂] M₂) -> _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.bijective_iff_has_inverse`：bijective_iff_has_inverse : Bijectiv
e f ↔ exists g, LeftInverse g f ∧ RightInverse g f
· 使用定理 `ContinuousLinearEquiv.symm_symm`：symm_symm (e : M₁ ≃SL[σ₁₂] M₂) : e.symm
.symm = e
-/
theorem symm_bijective : Function.Bijective (ContinuousLinearEquiv.symm : (M₁ ≃SL[σ₁₂] M₂) → _) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]
/-
**ContinuousLinearEquiv.refl_symm** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearEqu
iv`。
形式化陈述：refl_symm : (ContinuousLinearEquiv.refl R₁ M₁).symm = ContinuousLinearEqui
v.refl R₁ M₁
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem refl_symm : (ContinuousLinearEquiv.refl R₁ M₁).symm = ContinuousLinearEquiv.refl R₁ M₁ :=
  rfl
/-
**ContinuousLinearEquiv.symm_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLin
earEquiv`。
形式化陈述：symm_symm_apply (e : M₁ ≃SL[σ₁₂] M₂) (x : M₁) : e.symm.symm x = e x
参数：e : M₁ ≃SL[σ₁₂] M₂；x : M₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_symm_apply (e : M₁ ≃SL[σ₁₂] M₂) (x : M₁) : e.symm.symm x = e x :=
  rfl
/-
**ContinuousLinearEquiv.symm_apply_eq** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinea
rEquiv`。
形式化陈述：symm_apply_eq (e : M₁ ≃SL[σ₁₂] M₂) {x y} : e.symm x = y ↔ x = e y
参数：e : M₁ ≃SL[σ₁₂] M₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.symm_apply_eq`：symm_apply_eq {x y} : e.symm x = y ↔ x = e y
-/
theorem symm_apply_eq (e : M₁ ≃SL[σ₁₂] M₂) {x y} : e.symm x = y ↔ x = e y :=
  e.toLinearEquiv.symm_apply_eq
/-
**ContinuousLinearEquiv.eq_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinea
rEquiv`。
形式化陈述：eq_symm_apply (e : M₁ ≃SL[σ₁₂] M₂) {x y} : y = e.symm x ↔ e y = x
参数：e : M₁ ≃SL[σ₁₂] M₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.eq_symm_apply`：eq_symm_apply {x y} : y = e.symm x ↔ e y = x
-/
theorem eq_symm_apply (e : M₁ ≃SL[σ₁₂] M₂) {x y} : y = e.symm x ↔ e y = x :=
  e.toLinearEquiv.eq_symm_apply
/-
**ContinuousLinearEquiv.image_eq_preimage_symm** 是 Mathlib 中的一个定理，位于命名空间 `Contin
uousLinearEquiv`。
形式化陈述：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Semiring R₁] [inst_1 : Semiring 
R₂] {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁}   [inst_2 : RingHomInvPair σ₁₂ σ₂₁] [ins
t_3 : RingHomInvPair σ₂₁ σ₁₂] {M₁ : Type u_4} [inst_4 : TopologicalSpace M₁]   [
inst_5 : AddCommMonoid M₁] {M₂ : Type u_5} [inst_6 : TopologicalSpace M₂] [inst_
7 : AddCommMonoid M₂]   [inst_8 : _root_.Module R₁ M₁] [inst_9 : _root_.Module R
₂ M₂] (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₁),   ⇑e '' s = ⇑e.symm ⁻¹' s
参数：e : M₁ ≃SL[σ₁₂] M₂；s : Set M₁。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Equiv.image_eq_preimage_symm`：image_eq_preimage_symm (e : α ≃ β) (s : Se
t α) : e '' s = e.symm ⁻¹' s
-/
protected lemma image_eq_preimage_symm (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₁) : e '' s = e.symm ⁻¹' s :=
  e.toLinearEquiv.toEquiv.image_eq_preimage_symm s
/-
**ContinuousLinearEquiv.image_symm_eq_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Contin
uousLinearEquiv`。
形式化陈述：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Semiring R₁] [inst_1 : Semiring 
R₂] {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁}   [inst_2 : RingHomInvPair σ₁₂ σ₂₁] [ins
t_3 : RingHomInvPair σ₂₁ σ₁₂] {M₁ : Type u_4} [inst_4 : TopologicalSpace M₁]   [
inst_5 : AddCommMonoid M₁] {M₂ : Type u_5} [inst_6 : TopologicalSpace M₂] [inst_
7 : AddCommMonoid M₂]   [inst_8 : _root_.Module R₁ M₁] [inst_9 : _root_.Module R
₂ M₂] (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₂),   ⇑e.symm '' s = ⇑e ⁻¹' s
参数：e : M₁ ≃SL[σ₁₂] M₂；s : Set M₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearEquiv.image_eq_preimage_symm`：∀ {R₁ : Type u_1} {R₂ : Ty
pe u_2} [inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ 
→+* R₁}   [inst_2 : RingHomInvPair…
· 使用定理 `ContinuousLinearEquiv.symm_symm`：symm_symm (e : M₁ ≃SL[σ₁₂] M₂) : e.symm
.symm = e
-/
protected theorem image_symm_eq_preimage (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₂) :
    e.symm '' s = e ⁻¹' s := by rw [e.symm.image_eq_preimage_symm, e.symm_symm]

@[simp]
/-
**ContinuousLinearEquiv.symm_preimage_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Contin
uousLinearEquiv`。
形式化陈述：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Semiring R₁] [inst_1 : Semiring 
R₂] {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁}   [inst_2 : RingHomInvPair σ₁₂ σ₂₁] [ins
t_3 : RingHomInvPair σ₂₁ σ₁₂] {M₁ : Type u_4} [inst_4 : TopologicalSpace M₁]   [
inst_5 : AddCommMonoid M₁] {M₂ : Type u_5} [inst_6 : TopologicalSpace M₂] [inst_
7 : AddCommMonoid M₂]   [inst_8 : _root_.Module R₁ M₁] [inst_9 : _root_.Module R
₂ M₂] (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₂),   ⇑e.symm ⁻¹' ⇑e ⁻¹' s = s
参数：e : M₁ ≃SL[σ₁₂] M₂；s : Set M₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm_preimage_preimage`：symm_preimage_preimage {α β} (e : α ≃ β) (
s : Set β) : e.symm ⁻¹' e ⁻¹' s = s
-/
protected theorem symm_preimage_preimage (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₂) :
    e.symm ⁻¹' e ⁻¹' s = s :=
  e.toLinearEquiv.toEquiv.symm_preimage_preimage s

@[simp]
/-
**ContinuousLinearEquiv.preimage_symm_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Contin
uousLinearEquiv`。
形式化陈述：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Semiring R₁] [inst_1 : Semiring 
R₂] {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁}   [inst_2 : RingHomInvPair σ₁₂ σ₂₁] [ins
t_3 : RingHomInvPair σ₂₁ σ₁₂] {M₁ : Type u_4} [inst_4 : TopologicalSpace M₁]   [
inst_5 : AddCommMonoid M₁] {M₂ : Type u_5} [inst_6 : TopologicalSpace M₂] [inst_
7 : AddCommMonoid M₂]   [inst_8 : _root_.Module R₁ M₁] [inst_9 : _root_.Module R
₂ M₂] (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₁),   ⇑e ⁻¹' ⇑e.symm ⁻¹' s = s
参数：e : M₁ ≃SL[σ₁₂] M₂；s : Set M₁。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearEquiv.symm_preimage_preimage`：∀ {R₁ : Type u_1} {R₂ : Ty
pe u_2} [inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ 
→+* R₁}   [inst_2 : RingHomInvPair…
-/
protected theorem preimage_symm_preimage (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₁) :
    e ⁻¹' e.symm ⁻¹' s = s :=
  e.symm.symm_preimage_preimage s
/-
**ContinuousLinearEquiv.isUniformEmbedding** 是 Mathlib 中的一个引理，位于命名空间 `Continuous
LinearEquiv`。
形式化陈述：isUniformEmbedding {E₁ E₂ : Type*} [UniformSpace E₁] [UniformSpace E₂] [Ad
dCommGroup E₁] [AddCommGroup E₂] [Module R₁ E₁] [Module R₂ E₂] [IsUniformAddGrou
p E₁] [IsUniformAddGroup E₂] (e : E₁ ≃SL[σ₁₂] E₂) : IsUniformEmbedding e
参数：e : E₁ ≃SL[σ₁₂] E₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.isUniformEmbedding`：Equiv.isUniformEmbedding {α β : Type*} [Unifor
mSpace α] [UniformSpace β] (f : α ≃ β) (h₁ : UniformContinuous f) (h₂ : UniformC
ontinuous f.sy…
· 使用定理 `ContinuousLinearMap.uniformContinuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2}
 [inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {E₁ : Type u_9}  
 {E₂ : Type u_10} [inst_2 :…
-/
lemma isUniformEmbedding {E₁ E₂ : Type*} [UniformSpace E₁] [UniformSpace E₂]
    [AddCommGroup E₁] [AddCommGroup E₂] [Module R₁ E₁] [Module R₂ E₂] [IsUniformAddGroup E₁]
    [IsUniformAddGroup E₂] (e : E₁ ≃SL[σ₁₂] E₂) : IsUniformEmbedding e :=
  e.toLinearEquiv.toEquiv.isUniformEmbedding e.toContinuousLinearMap.uniformContinuous
    e.symm.toContinuousLinearMap.uniformContinuous
/-
**ContinuousLinearEquiv._root_.LinearEquiv.isUniformEmbedding** 是 Mathlib 中的一个定理
，位于命名空间 `ContinuousLinearEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem _root_.LinearEquiv.isUniformEmbedding {E₁ E₂ : Type*} [UniformSpace E₁]
    [UniformSpace E₂] [AddCommGroup E₁] [AddCommGroup E₂] [Module R₁ E₁] [Module R₂ E₂]
    [IsUniformAddGroup E₁] [IsUniformAddGroup E₂] (e : E₁ ≃ₛₗ[σ₁₂] E₂)
    (h₁ : Continuous e) (h₂ : Continuous e.symm) : IsUniformEmbedding e :=
  ContinuousLinearEquiv.isUniformEmbedding
    ({ e with
        continuous_toFun := h₁
        continuous_invFun := h₂ } :
      E₁ ≃SL[σ₁₂] E₂)

/-- Create a `ContinuousLinearEquiv` from two `ContinuousLinearMap`s that are
inverse of each other. See also `equivOfInverse'`.
*ToDo*: Improve the naiming to make it match `LinearMap.ofLinear`. -/
/-
**ContinuousLinearEquiv.equivOfInverse** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLine
arEquiv`。
形式化陈述：equivOfInverse (f₁ : M₁ ->SL[σ₁₂] M₂) (f₂ : M₂ ->SL[σ₂₁] M₁) (h₁ : Functio
n.LeftInverse f₂ f₁) (h₂ : Function.RightInverse f₂ f₁) : M₁ ≃SL[σ₁₂] M₂
参数：f₁ : M₁ ->SL[σ₁₂] M₂；f₂ : M₂ ->SL[σ₂₁] M₁；h₁ : Function.LeftInverse f₂ f₁；h₂ 
: Function.RightInverse f₂ f₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Create a `ContinuousLinearEquiv` from two `ContinuousLinearMap`s that are
inverse of each other. See also `equivOfInverse'`.
*ToDo*: Improve the naiming to make it match `LinearMap.ofLinear`.
-/
def equivOfInverse (f₁ : M₁ →SL[σ₁₂] M₂) (f₂ : M₂ →SL[σ₂₁] M₁) (h₁ : Function.LeftInverse f₂ f₁)
    (h₂ : Function.RightInverse f₂ f₁) : M₁ ≃SL[σ₁₂] M₂ :=
  { f₁ with
    invFun := f₂
    left_inv := h₁
    right_inv := h₂ }

@[simp]
/-
**ContinuousLinearEquiv.equivOfInverse_apply** 是 Mathlib 中的一个定理，位于命名空间 `Continuo
usLinearEquiv`。
形式化陈述：equivOfInverse_apply (f₁ : M₁ ->SL[σ₁₂] M₂) (f₂ h₁ h₂ x) : equivOfInverse 
f₁ f₂ h₁ h₂ x = f₁ x
参数：f₁ : M₁ ->SL[σ₁₂] M₂；f₂ h₁ h₂ x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem equivOfInverse_apply (f₁ : M₁ →SL[σ₁₂] M₂) (f₂ h₁ h₂ x) :
    equivOfInverse f₁ f₂ h₁ h₂ x = f₁ x :=
  rfl

@[simp]
/-
**ContinuousLinearEquiv.symm_equivOfInverse** 是 Mathlib 中的一个定理，位于命名空间 `Continuou
sLinearEquiv`。
形式化陈述：symm_equivOfInverse (f₁ : M₁ ->SL[σ₁₂] M₂) (f₂ h₁ h₂) : (equivOfInverse f₁
 f₂ h₁ h₂).symm = equivOfInverse f₂ f₁ h₂ h₁
参数：f₁ : M₁ ->SL[σ₁₂] M₂；f₂ h₁ h₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_equivOfInverse (f₁ : M₁ →SL[σ₁₂] M₂) (f₂ h₁ h₂) :
    (equivOfInverse f₁ f₂ h₁ h₂).symm = equivOfInverse f₂ f₁ h₂ h₁ :=
  rfl

/-- Create a `ContinuousLinearEquiv` from two `ContinuousLinearMap`s that are
inverse of each other, in the `ContinuousLinearMap.comp` sense. See also `equivOfInverse`.
*ToDo*: Improve the naiming to make it match `LinearMap.ofLinear` -/
/-
**ContinuousLinearEquiv.equivOfInverse'** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLin
earEquiv`。
形式化陈述：equivOfInverse' (f₁ : M₁ ->SL[σ₁₂] M₂) (f₂ : M₂ ->SL[σ₂₁] M₁) (h₁ : f₁.com
p f₂ = .id R₂ M₂) (h₂ : f₂.comp f₁ = .id R₁ M₁) : M₁ ≃SL[σ₁₂] M₂
参数：f₁ : M₁ ->SL[σ₁₂] M₂；f₂ : M₂ ->SL[σ₂₁] M₁；h₁ : f₁.comp f₂ = .id R₂ M₂；h₂ : f₂
.comp f₁ = .id R₁ M₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Create a `ContinuousLinearEquiv` from two `ContinuousLinearMap`s that are
inverse of each other, in the `ContinuousLinearMap.comp` sense. See also `equivO
fInverse`.
*ToDo*: Improve the naiming to make it match `LinearMap.ofLinear`
-/
def equivOfInverse' (f₁ : M₁ →SL[σ₁₂] M₂) (f₂ : M₂ →SL[σ₂₁] M₁)
    (h₁ : f₁.comp f₂ = .id R₂ M₂) (h₂ : f₂.comp f₁ = .id R₁ M₁) : M₁ ≃SL[σ₁₂] M₂ :=
  equivOfInverse f₁ f₂
    (fun x ↦ by simpa using congr($(h₂) x)) (fun x ↦ by simpa using congr($(h₁) x))

@[simp]
/-
**ContinuousLinearEquiv.equivOfInverse'_apply** 是 Mathlib 中的一个定理，位于命名空间 `Continu
ousLinearEquiv`。
形式化陈述：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Semiring R₁] [inst_1 : Semiring 
R₂] {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁}   [inst_2 : RingHomInvPair σ₁₂ σ₂₁] [ins
t_3 : RingHomInvPair σ₂₁ σ₁₂] {M₁ : Type u_4} [inst_4 : TopologicalSpace M₁]   [
inst_5 : AddCommMonoid M₁] {M₂ : Type u_5} [inst_6 : TopologicalSpace M₂] [inst_
7 : AddCommMonoid M₂]   [inst_8 : _root_.Module R₁ M₁] [inst_9 : _root_.Module R
₂ M₂] (f₁ : M₁ →SL[σ₁₂] M₂) (f₂ : M₂ →SL[σ₂₁] M₁)   (h₁ : f₁ ∘SL f₂ = Continuous
LinearMap.id R₂ M₂) (h₂ : f₂ ∘SL f₁ = ContinuousLinearMap.id R₁ M₁) (x : M₁),   
(ContinuousLinearEquiv.equivOfInverse' f₁ f₂ h₁ h₂) x = f₁ x
参数：f₁ : M₁ →SL[σ₁₂] M₂；f₂ : M₂ →SL[σ₂₁] M₁；h₁ : f₁ ∘SL f₂ = ContinuousLinearMap.
id R₂ M₂；h₂ : f₂ ∘SL f₁ = ContinuousLinearMap.id R₁ M₁；x : M₁；ContinuousLinearEq
uiv.equivOfInverse' f₁ f₂ h₁ h₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem equivOfInverse'_apply (f₁ : M₁ →SL[σ₁₂] M₂) (f₂ h₁ h₂ x) :
    equivOfInverse' f₁ f₂ h₁ h₂ x = f₁ x :=
  rfl

/-- The inverse of `equivOfInverse'` is obtained by swapping the order of its parameters. -/
@[simp]
/-
**ContinuousLinearEquiv.symm_equivOfInverse'** 是 Mathlib 中的一个定理，位于命名空间 `Continuo
usLinearEquiv`。
形式化陈述：symm_equivOfInverse' (f₁ : M₁ ->SL[σ₁₂] M₂) (f₂ h₁ h₂) : (equivOfInverse' 
f₁ f₂ h₁ h₂).symm = equivOfInverse' f₂ f₁ h₂ h₁
参数：f₁ : M₁ ->SL[σ₁₂] M₂；f₂ h₁ h₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse of `equivOfInverse'` is obtained by swapping the order of its parame
ters.
-/
theorem symm_equivOfInverse' (f₁ : M₁ →SL[σ₁₂] M₂) (f₂ h₁ h₂) :
    (equivOfInverse' f₁ f₂ h₁ h₂).symm = equivOfInverse' f₂ f₁ h₂ h₁ :=
  rfl
/-
**ContinuousLinearEquiv.eq_comp_toContinuousLinearMap_symm** 是 Mathlib 中的一个定理，位于
命名空间 `ContinuousLinearEquiv`。
形式化陈述：eq_comp_toContinuousLinearMap_symm (e₁₂ : M₁ ≃SL[σ₁₂] M₂) [RingHomCompTrip
le σ₂₁ σ₁₃ σ₂₃] (f : M₂ ->SL[σ₂₃] M₃) (g : M₁ ->SL[σ₁₃] M₃) : f = g.comp e₁₂.sym
m.toContinuousLinearMap ↔ f.comp e₁₂.toContinuousLinearMap = g
参数：e₁₂ : M₁ ≃SL[σ₁₂] M₂；f : M₂ ->SL[σ₂₃] M₃；g : M₁ ->SL[σ₁₃] M₃。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearEquiv.symm_apply_apply`：symm_apply_apply (e : M₁ ≃SL[σ₁₂
] M₂) (b : M₁) : e.symm (e b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearEquiv.apply_symm_apply`：apply_symm_apply (e : M₁ ≃SL[σ₁₂
] M₂) (c : M₂) : e (e.symm c) = c
-/
theorem eq_comp_toContinuousLinearMap_symm (e₁₂ : M₁ ≃SL[σ₁₂] M₂) [RingHomCompTriple σ₂₁ σ₁₃ σ₂₃]
    (f : M₂ →SL[σ₂₃] M₃) (g : M₁ →SL[σ₁₃] M₃) :
    f = g.comp e₁₂.symm.toContinuousLinearMap ↔ f.comp e₁₂.toContinuousLinearMap = g := by
  aesop
/-
**ContinuousLinearEquiv.eq_toContinuousLinearMap_symm_comp** 是 Mathlib 中的一个定理，位于
命名空间 `ContinuousLinearEquiv`。
形式化陈述：eq_toContinuousLinearMap_symm_comp {e₁₂ : M₁ ≃SL[σ₁₂] M₂} [RingHomCompTrip
le σ₃₁ σ₁₂ σ₃₂] (f : M₃ ->SL[σ₃₁] M₁) (g : M₃ ->SL[σ₃₂] M₂) : f = e₁₂.symm.toCon
tinuousLinearMap.comp g ↔ e₁₂.toContinuousLinearMap.comp f = g
参数：f : M₃ ->SL[σ₃₁] M₁；g : M₃ ->SL[σ₃₂] M₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearEquiv.apply_symm_apply`：apply_symm_apply (e : M₁ ≃SL[σ₁₂
] M₂) (c : M₂) : e (e.symm c) = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearEquiv.symm_apply_apply`：symm_apply_apply (e : M₁ ≃SL[σ₁₂
] M₂) (b : M₁) : e.symm (e b) = b
-/
theorem eq_toContinuousLinearMap_symm_comp {e₁₂ : M₁ ≃SL[σ₁₂] M₂} [RingHomCompTriple σ₃₁ σ₁₂ σ₃₂]
    (f : M₃ →SL[σ₃₁] M₁) (g : M₃ →SL[σ₃₂] M₂) :
    f = e₁₂.symm.toContinuousLinearMap.comp g ↔ e₁₂.toContinuousLinearMap.comp f = g := by
  aesop

variable (M₁)

/-- The continuous linear equivalences from `M` to itself form a group under composition. -/
/-
**ContinuousLinearEquiv.automorphismGroup** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousL
inearEquiv`。
形式化陈述：automorphismGroup : Group (M₁ ≃L[R₁] M₁) where mul f g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The continuous linear equivalences from `M` to itself form a group under composi
tion.
-/
instance automorphismGroup : Group (M₁ ≃L[R₁] M₁) where
  mul f g := g.trans f
  one := ContinuousLinearEquiv.refl R₁ M₁
  inv f := f.symm
  mul_assoc f g h := rfl
  mul_one f := rfl
  one_mul f := rfl
  inv_mul_cancel f := ext <| funext fun _ ↦ f.left_inv _
/-
**ContinuousLinearEquiv.toContinuousLinearMap_one** 是 Mathlib 中的一个定理，位于命名空间 `Con
tinuousLinearEquiv`。
形式化陈述：∀ {R₁ : Type u_1} [inst : Semiring R₁] (M₁ : Type u_4) [inst_1 : Topologic
alSpace M₁] [inst_2 : AddCommMonoid M₁]   [inst_3 : _root_.Module R₁ M₁], ↑1 = 1
参数：M₁ : Type u_4。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toContinuousLinearMap_one : toContinuousLinearMap (1 : M₁ ≃L[R₁] M₁) = 1 := rfl
/-
**ContinuousLinearEquiv.toContinuousLinearMap_mul** 是 Mathlib 中的一个定理，位于命名空间 `Con
tinuousLinearEquiv`。
形式化陈述：∀ {R₁ : Type u_1} [inst : Semiring R₁] (M₁ : Type u_4) [inst_1 : Topologic
alSpace M₁] [inst_2 : AddCommMonoid M₁]   [inst_3 : _root_.Module R₁ M₁] (e e' :
 M₁ ≃L[R₁] M₁), ↑(e * e') = ↑e * ↑e'
参数：M₁ : Type u_4；e e' : M₁ ≃L[R₁] M₁；e * e'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toContinuousLinearMap_mul (e e' : M₁ ≃L[R₁] M₁) :
    toContinuousLinearMap (e * e') = e.toContinuousLinearMap * e'.toContinuousLinearMap := rfl

variable {M₁} {R₄ : Type*} [Semiring R₄] [Module R₄ M₄] {σ₃₄ : R₃ →+* R₄} {σ₄₃ : R₄ →+* R₃}
  [RingHomInvPair σ₃₄ σ₄₃] [RingHomInvPair σ₄₃ σ₃₄] {σ₂₄ : R₂ →+* R₄} {σ₁₄ : R₁ →+* R₄}
  [RingHomCompTriple σ₂₁ σ₁₄ σ₂₄] [RingHomCompTriple σ₂₄ σ₄₃ σ₂₃] [RingHomCompTriple σ₁₃ σ₃₄ σ₁₄]

/-- The continuous linear equivalence between `ULift M₁` and `M₁`.

This is a continuous version of `ULift.moduleEquiv`. -/
/-
**ContinuousLinearEquiv.ulift** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearEquiv`。
形式化陈述：ulift : ULift M₁ ≃L[R₁] M₁ where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The continuous linear equivalence between `ULift M₁` and `M₁`.

This is a continuous version of `ULift.moduleEquiv`.
-/
def ulift : ULift M₁ ≃L[R₁] M₁ where
  __ := ULift.moduleEquiv

/-- A pair of continuous (semi)linear equivalences generates an equivalence between the spaces of
continuous linear maps. See also `ContinuousLinearEquiv.arrowCongr`. -/
@[simps]
/-
**ContinuousLinearEquiv.arrowCongrEquiv** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLin
earEquiv`。
形式化陈述：arrowCongrEquiv (e₁₂ : M₁ ≃SL[σ₁₂] M₂) (e₄₃ : M₄ ≃SL[σ₄₃] M₃) : (M₁ ->SL[σ
₁₄] M₄) ≃ (M₂ ->SL[σ₂₃] M₃) where toFun f
参数：e₁₂ : M₁ ≃SL[σ₁₂] M₂；e₄₃ : M₄ ≃SL[σ₄₃] M₃。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A pair of continuous (semi)linear equivalences generates an equivalence between 
the spaces of
continuous linear maps. See also `ContinuousLinearEquiv.arrowCongr`.
-/
def arrowCongrEquiv (e₁₂ : M₁ ≃SL[σ₁₂] M₂) (e₄₃ : M₄ ≃SL[σ₄₃] M₃) :
    (M₁ →SL[σ₁₄] M₄) ≃ (M₂ →SL[σ₂₃] M₃) where
  toFun f := (e₄₃ : M₄ →SL[σ₄₃] M₃).comp (f.comp (e₁₂.symm : M₂ →SL[σ₂₁] M₁))
  invFun f := (e₄₃.symm : M₃ →SL[σ₃₄] M₄).comp (f.comp (e₁₂ : M₁ →SL[σ₁₂] M₂))
  left_inv f :=
    ContinuousLinearMap.ext fun x => by
      simp only [ContinuousLinearMap.comp_apply, symm_apply_apply, coe_coe]
  right_inv f :=
    ContinuousLinearMap.ext fun x => by
      simp only [ContinuousLinearMap.comp_apply, apply_symm_apply, coe_coe]

/-- A pair of continuous (semi)linear equivalences generates a linear equivalence between the spaces
of continuous linear maps. See also `ContinuousLinearEquiv.arrowCongr`. -/
@[simps]
/-
**ContinuousLinearEquiv.arrowCongrEquiv** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLin
earEquiv`。
形式化陈述：arrowCongrEquiv (e₁₂ : M₁ ≃SL[σ₁₂] M₂) (e₄₃ : M₄ ≃SL[σ₄₃] M₃) : (M₁ ->SL[σ
₁₄] M₄) ≃ (M₂ ->SL[σ₂₃] M₃) where toFun f
参数：e₁₂ : M₁ ≃SL[σ₁₂] M₂；e₄₃ : M₄ ≃SL[σ₄₃] M₃。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A pair of continuous (semi)linear equivalences generates a linear equivalence be
tween the spaces
of continuous linear maps. See also `ContinuousLinearEquiv.arrowCongr`.
-/
def arrowCongrEquivₛₗ [SMulCommClass R₃ R₃ M₃] [SMulCommClass R₄ R₄ M₄]
    [ContinuousAdd M₃] [ContinuousConstSMul R₃ M₃] [ContinuousAdd M₄] [ContinuousConstSMul R₄ M₄]
    (e₁₂ : M₁ ≃SL[σ₁₂] M₂) (e₄₃ : M₄ ≃SL[σ₄₃] M₃) :
    (M₁ →SL[σ₁₄] M₄) ≃ₛₗ[σ₄₃] (M₂ →SL[σ₂₃] M₃) where
  toEquiv := arrowCongrEquiv e₁₂ e₄₃
  map_add' := by simp
  map_smul' := by simp

section Pi

/-- Combine a family of linear equivalences into a linear equivalence of `pi`-types.
This is `Equiv.piCongrLeft` as a `ContinuousLinearEquiv`.
-/
/-
**ContinuousLinearEquiv.piCongrLeft** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearE
quiv`。
形式化陈述：piCongrLeft (R : Type*) [Semiring R] {ι ι' : Type*} (φ : ι -> Type*) [fora
ll i, AddCommMonoid (φ i)] [forall i, Module R (φ i)] [forall i, TopologicalSpac
e (φ i)] (e : ι' ≃ ι) : ((i' : ι') -> φ (e i')) ≃L[R] (i : ι) -> φ i where __
参数：R : Type*；φ : ι -> Type*；φ i；φ i；φ i；e : ι' ≃ ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Combine a family of linear equivalences into a linear equivalence of `pi`-types.
This is `Equiv.piCongrLeft` as a `ContinuousLinearEquiv`.
-/
def piCongrLeft (R : Type*) [Semiring R] {ι ι' : Type*}
    (φ : ι → Type*) [∀ i, AddCommMonoid (φ i)] [∀ i, Module R (φ i)]
    [∀ i, TopologicalSpace (φ i)]
    (e : ι' ≃ ι) : ((i' : ι') → φ (e i')) ≃L[R] (i : ι) → φ i where
  __ := Homeomorph.piCongrLeft e
  __ := LinearEquiv.piCongrLeft R φ e

/-- The product over `S ⊕ T` of a family of topological modules
is isomorphic (topologically and algebraically) to the product of
(the product over `S`) and (the product over `T`).

This is `Equiv.sumPiEquivProdPi` as a `ContinuousLinearEquiv`.
-/
/-
**ContinuousLinearEquiv.sumPiEquivProdPi** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLi
nearEquiv`。
形式化陈述：sumPiEquivProdPi (R : Type*) [Semiring R] (S T : Type*) (A : S oplus T -> 
Type*) [forall st, AddCommMonoid (A st)] [forall st, Module R (A st)] [forall st
, TopologicalSpace (A st)] : ((st : S oplus T) -> A st) ≃L[R] ((s : S) -> A (Sum
.inl s)) × ((t : T) -> A (Sum.inr t)) where __
参数：R : Type*；S T : Type*；A : S oplus T -> Type*；A st；A st；A st。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product over `S ⊕ T` of a family of topological modules
is isomorphic (topologically and algebraically) to the product of
(the product over `S`) and (the product over `T`).

This is `Equiv.sumPiEquivProdPi` as a `ContinuousLinearEquiv`.
-/
def sumPiEquivProdPi (R : Type*) [Semiring R] (S T : Type*)
    (A : S ⊕ T → Type*) [∀ st, AddCommMonoid (A st)] [∀ st, Module R (A st)]
    [∀ st, TopologicalSpace (A st)] :
    ((st : S ⊕ T) → A st) ≃L[R] ((s : S) → A (Sum.inl s)) × ((t : T) → A (Sum.inr t)) where
  __ := LinearEquiv.sumPiEquivProdPi R S T A
  __ := Homeomorph.sumPiEquivProdPi S T A

/-- The product `Π t : α, f t` of a family of topological modules is isomorphic
(both topologically and algebraically) to the space `f ⬝` when `α` only contains `⬝`.

This is `Equiv.piUnique` as a `ContinuousLinearEquiv`.
-/
@[simps! -fullyApplied]
/-
**ContinuousLinearEquiv.piUnique** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearEqui
v`。
形式化陈述：piUnique {α : Type*} [Unique α] (R : Type*) [Semiring R] (f : α -> Type*) 
[forall x, AddCommMonoid (f x)] [forall x, Module R (f x)] [forall x, Topologica
lSpace (f x)] : (Π t, f t) ≃L[R] f default where __
参数：R : Type*；f : α -> Type*；f x；f x；f x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product `Π t : α, f t` of a family of topological modules is isomorphic
(both topologically and algebraically) to the space `f ⬝` when `α` only contains
 `⬝`.

This is `Equiv.piUnique` as a `ContinuousLinearEquiv`.
-/
def piUnique {α : Type*} [Unique α] (R : Type*) [Semiring R] (f : α → Type*)
    [∀ x, AddCommMonoid (f x)] [∀ x, Module R (f x)] [∀ x, TopologicalSpace (f x)] :
    (Π t, f t) ≃L[R] f default where
  __ := LinearEquiv.piUnique R f
  __ := Homeomorph.piUnique f

end Pi

section piCongrRight

variable {ι : Type*} {M : ι → Type*} [∀ i, TopologicalSpace (M i)] [∀ i, AddCommMonoid (M i)]
  [∀ i, Module R₁ (M i)] {N : ι → Type*} [∀ i, TopologicalSpace (N i)] [∀ i, AddCommMonoid (N i)]
  [∀ i, Module R₁ (N i)] (f : (i : ι) → M i ≃L[R₁] N i)

/-- Combine a family of continuous linear equivalences into a continuous linear equivalence of
pi-types. -/
/-
**ContinuousLinearEquiv.piCongrRight** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinear
Equiv`。
形式化陈述：piCongrRight : ((i : ι) -> M i) ≃L[R₁] (i : ι) -> N i where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Combine a family of continuous linear equivalences into a continuous linear equi
valence of
pi-types.
-/
def piCongrRight : ((i : ι) → M i) ≃L[R₁] (i : ι) → N i where
  __ := LinearEquiv.piCongrRight fun i ↦ (f i).toLinearEquiv

@[simp]
/-
**ContinuousLinearEquiv.piCongrRight_apply** 是 Mathlib 中的一个定理，位于命名空间 `Continuous
LinearEquiv`。
形式化陈述：piCongrRight_apply (m : (i : ι) -> M i) (i : ι) : piCongrRight f m i = (f 
i) (m i)
参数：m : (i : ι) -> M i；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem piCongrRight_apply (m : (i : ι) → M i) (i : ι) :
    piCongrRight f m i = (f i) (m i) := rfl

@[simp]
/-
**ContinuousLinearEquiv.piCongrRight_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Conti
nuousLinearEquiv`。
形式化陈述：piCongrRight_symm_apply (n : (i : ι) -> N i) (i : ι) : (piCongrRight f).sy
mm n i = (f i).symm (n i)
参数：n : (i : ι) -> N i；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem piCongrRight_symm_apply (n : (i : ι) → N i) (i : ι) :
    (piCongrRight f).symm n i = (f i).symm (n i) := rfl

end piCongrRight

section DistribMulAction

variable {G : Type*} [Group G] [DistribMulAction G M₁] [ContinuousConstSMul G M₁]
  [SMulCommClass G R₁ M₁]

/-- Scalar multiplication by a group element as a continuous linear equivalence. -/
@[simps! apply_toLinearEquiv apply_apply]
/-
**ContinuousLinearEquiv.smulLeft** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearEqui
v`。
形式化陈述：smulLeft : G ->* M₁ ≃L[R₁] M₁ where toFun g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Scalar multiplication by a group element as a continuous linear equivalence.
-/
def smulLeft : G →* M₁ ≃L[R₁] M₁ where
  toFun g := ⟨DistribMulAction.toModuleAut _ _ g, continuous_const_smul _, continuous_const_smul _⟩
  map_mul' _ _ := toLinearEquiv_injective <| map_mul (DistribMulAction.toModuleAut _ _) _ _
  map_one' := toLinearEquiv_injective <| map_one <| DistribMulAction.toModuleAut _ _

end DistribMulAction

end AddCommMonoid

section Aut

/-!
### Automorphisms as continuous linear equivalences and as units of the ring of endomorphisms

The next theorems cover the identification between `M ≃L[R] M` and the group of units of the ring
`M →L[R] M`.
-/

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [TopologicalSpace M]

/-- An invertible continuous linear map `f` determines a continuous equivalence from `M` to itself.
-/
/-
**ContinuousLinearEquiv.ofUnit** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearEquiv`
。
形式化陈述：ofUnit (f : (M ->L[R] M)ˣ) : M ≃L[R] M where toLinearEquiv
参数：f : (M ->L[R] M)ˣ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An invertible continuous linear map `f` determines a continuous equivalence from
 `M` to itself.
-/
def ofUnit (f : (M →L[R] M)ˣ) : M ≃L[R] M where
  toLinearEquiv :=
    { toFun := f.val
      map_add' := by simp
      map_smul' := by simp
      invFun := f.inv
      left_inv := fun x =>
        show (f.inv * f.val) x = x by
          rw [f.inv_val]
          simp
      right_inv := fun x =>
        show (f.val * f.inv) x = x by
          rw [f.val_inv]
          simp }

/-- A continuous equivalence from `M` to itself determines an invertible continuous linear map. -/
/-
**ContinuousLinearEquiv.toUnit** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearEquiv`
。
形式化陈述：toUnit (f : M ≃L[R] M) : (M ->L[R] M)ˣ where val
参数：f : M ≃L[R] M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A continuous equivalence from `M` to itself determines an invertible continuous 
linear map.
-/
def toUnit (f : M ≃L[R] M) : (M →L[R] M)ˣ where
  val := f
  inv := f.symm
  val_inv := by
    ext
    simp
  inv_val := by
    ext
    simp

variable (R M)

/-- The units of the algebra of continuous `R`-linear endomorphisms of `M` is multiplicatively
equivalent to the type of continuous linear equivalences between `M` and itself. -/
/-
**ContinuousLinearEquiv.unitsEquiv** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearEq
uiv`。
形式化陈述：unitsEquiv : (M ->L[R] M)ˣ ≃* M ≃L[R] M where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The units of the algebra of continuous `R`-linear endomorphisms of `M` is multip
licatively
equivalent to the type of continuous linear equivalences between `M` and itself.
-/
def unitsEquiv : (M →L[R] M)ˣ ≃* M ≃L[R] M where
  toFun := ofUnit
  invFun := toUnit
  map_mul' x y := by
    ext
    rfl

@[simp]
/-
**ContinuousLinearEquiv.unitsEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLi
nearEquiv`。
形式化陈述：unitsEquiv_apply (f : (M ->L[R] M)ˣ) (x : M) : unitsEquiv R M f x = (f : M
 ->L[R] M) x
参数：f : (M ->L[R] M)ˣ；x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unitsEquiv_apply (f : (M →L[R] M)ˣ) (x : M) : unitsEquiv R M f x = (f : M →L[R] M) x :=
  rfl

end Aut

section AutRing

/-!
### Units of a ring as linear automorphisms
-/

variable (R : Type*) [Semiring R] [TopologicalSpace R] [ContinuousMul R]

set_option backward.isDefEq.respectTransparency false in
/-- Continuous linear equivalences `R ≃L[R] R` are enumerated by `Rˣ`. -/
/-
**ContinuousLinearEquiv.unitsEquivAut** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinea
rEquiv`。
形式化陈述：unitsEquivAut : Rˣ ≃ R ≃L[R] R where toFun u
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Continuous linear equivalences `R ≃L[R] R` are enumerated by `Rˣ`.
-/
def unitsEquivAut : Rˣ ≃ R ≃L[R] R where
  toFun u :=
    equivOfInverse (ContinuousLinearMap.smulRight (1 : R →L[R] R) ↑u)
      (ContinuousLinearMap.smulRight (1 : R →L[R] R) ↑u⁻¹) (fun x => by simp) fun x => by simp
  invFun e :=
    ⟨e 1, e.symm 1, by rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one, symm_apply_apply], by
      rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one, apply_symm_apply]⟩
  left_inv u := Units.ext <| by simp
  right_inv e := ext₁ <| by simp

variable {R}

@[simp]
/-
**ContinuousLinearEquiv.unitsEquivAut_apply** 是 Mathlib 中的一个定理，位于命名空间 `Continuou
sLinearEquiv`。
形式化陈述：unitsEquivAut_apply (u : Rˣ) (x : R) : unitsEquivAut R u x = x * u
参数：u : Rˣ；x : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unitsEquivAut_apply (u : Rˣ) (x : R) : unitsEquivAut R u x = x * u :=
  rfl

@[simp]
/-
**ContinuousLinearEquiv.unitsEquivAut_apply_symm** 是 Mathlib 中的一个定理，位于命名空间 `Cont
inuousLinearEquiv`。
形式化陈述：unitsEquivAut_apply_symm (u : Rˣ) (x : R) : (unitsEquivAut R u).symm x = x
 * ↑u⁻¹
参数：u : Rˣ；x : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unitsEquivAut_apply_symm (u : Rˣ) (x : R) : (unitsEquivAut R u).symm x = x * ↑u⁻¹ :=
  rfl

@[simp]
/-
**ContinuousLinearEquiv.unitsEquivAut_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Cont
inuousLinearEquiv`。
形式化陈述：unitsEquivAut_symm_apply (e : R ≃L[R] R) : ↑((unitsEquivAut R).symm e) = e
 1
参数：e : R ≃L[R] R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem unitsEquivAut_symm_apply (e : R ≃L[R] R) : ↑((unitsEquivAut R).symm e) = e 1 :=
  rfl

end AutRing

section Pi

variable (ι R M : Type*) [Unique ι] [Semiring R] [AddCommMonoid M] [Module R M]
  [TopologicalSpace M]

/-- If `ι` has a unique element, then `ι → M` is continuously linear equivalent to `M`. -/
/-
**ContinuousLinearEquiv.funUnique** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearEqu
iv`。
形式化陈述：funUnique : (ι -> M) ≃L[R] M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `ι` has a unique element, then `ι → M` is continuously linear equivalent to `
M`.
-/
def funUnique : (ι → M) ≃L[R] M :=
  { Homeomorph.funUnique ι M with toLinearEquiv := LinearEquiv.funUnique ι R M }

variable {ι R M}

@[simp]
/-
**ContinuousLinearEquiv.coe_funUnique** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinea
rEquiv`。
形式化陈述：coe_funUnique : ⇑(funUnique ι R M) = Function.eval default
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_funUnique : ⇑(funUnique ι R M) = Function.eval default :=
  rfl

@[simp]
/-
**ContinuousLinearEquiv.coe_funUnique_symm** 是 Mathlib 中的一个定理，位于命名空间 `Continuous
LinearEquiv`。
形式化陈述：coe_funUnique_symm : ⇑(funUnique ι R M).symm = Function.const ι
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_funUnique_symm : ⇑(funUnique ι R M).symm = Function.const ι :=
  rfl

variable (R M)

/-- Continuous linear equivalence between dependent functions `(i : Fin 2) → M i` and `M 0 × M 1`.
-/
@[simps! -fullyApplied apply symm_apply]
/-
**ContinuousLinearEquiv.piFinTwo** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearEqui
v`。
形式化陈述：piFinTwo (M : Fin 2 -> Type*) [forall i, AddCommMonoid (M i)] [forall i, M
odule R (M i)] [forall i, TopologicalSpace (M i)] : ((i : _) -> M i) ≃L[R] M 0 ×
 M 1
参数：M : Fin 2 -> Type*；M i；M i；M i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Continuous linear equivalence between dependent functions `(i : Fin 2) → M i` an
d `M 0 × M 1`.
-/
def piFinTwo (M : Fin 2 → Type*) [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    [∀ i, TopologicalSpace (M i)] : ((i : _) → M i) ≃L[R] M 0 × M 1 :=
  { Homeomorph.piFinTwo M with toLinearEquiv := LinearEquiv.piFinTwo R M }

/-- Continuous linear equivalence between vectors in `M² = Fin 2 → M` and `M × M`. -/
@[simps! -fullyApplied apply symm_apply]
/-
**ContinuousLinearEquiv.finTwoArrow** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearE
quiv`。
形式化陈述：finTwoArrow : (Fin 2 -> M) ≃L[R] M × M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Continuous linear equivalence between vectors in `M² = Fin 2 → M` and `M × M`.
-/
def finTwoArrow : (Fin 2 → M) ≃L[R] M × M :=
  { piFinTwo R fun _ => M with toLinearEquiv := LinearEquiv.finTwoArrow R M }

section
variable {n : ℕ} {R : Type*} {M : Fin n.succ → Type*} {N : Type*}
variable [Semiring R]
variable [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] [∀ i, TopologicalSpace (M i)]

set_option backward.defeqAttrib.useBackward true in
variable (R M) in
/-- `Fin.consEquiv` as a continuous linear equivalence. -/
@[simps!]
/-
**ContinuousLinearEquiv._root_.Fin.consEquivL** 是 Mathlib 中的一个定义，位于命名空间 `Continu
ousLinearEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Fin.consEquiv` as a continuous linear equivalence.
-/
def _root_.Fin.consEquivL : (M 0 × Π i, M (Fin.succ i)) ≃L[R] (Π i, M i) where
  __ := Fin.consLinearEquiv R M

/-- `Fin.cons` in the codomain of continuous linear maps. -/
/-
**ContinuousLinearEquiv._root_.ContinuousLinearMap.finCons** 是 Mathlib 中的一个缩写定义，
位于命名空间 `ContinuousLinearEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Fin.cons` in the codomain of continuous linear maps.
-/
abbrev _root_.ContinuousLinearMap.finCons
    [AddCommMonoid N] [Module R N] [TopologicalSpace N]
    (f : N →L[R] M 0) (fs : N →L[R] Π i, M (Fin.succ i)) :
    N →L[R] Π i, M i :=
  Fin.consEquivL R M ∘L f.prod fs

end

end Pi

section AddCommGroup

variable {R : Type*} [Semiring R] {M : Type*} [TopologicalSpace M] [AddCommGroup M] {M₂ : Type*}
  [TopologicalSpace M₂] [AddCommGroup M₂] {M₃ : Type*} [TopologicalSpace M₃] [AddCommGroup M₃]
  {M₄ : Type*} [TopologicalSpace M₄] [AddCommGroup M₄] [Module R M] [Module R M₂] [Module R M₃]
  [Module R M₄]

variable [IsTopologicalAddGroup M₄]

/-- Equivalence given by a block lower diagonal matrix. `e` and `e'` are diagonal square blocks,
  and `f` is a rectangular block below the diagonal. -/
/-
**ContinuousLinearEquiv.skewProd** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearEqui
v`。
形式化陈述：skewProd (e : M ≃L[R] M₂) (e' : M₃ ≃L[R] M₄) (f : M ->L[R] M₄) : (M × M₃) 
≃L[R] M₂ × M₄ where __
参数：e : M ≃L[R] M₂；e' : M₃ ≃L[R] M₄；f : M ->L[R] M₄。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equivalence given by a block lower diagonal matrix. `e` and `e'` are diagonal sq
uare blocks,
  and `f` is a rectangular block below the diagonal.
-/
def skewProd (e : M ≃L[R] M₂) (e' : M₃ ≃L[R] M₄) (f : M →L[R] M₄) : (M × M₃) ≃L[R] M₂ × M₄ where
  __ := e.toLinearEquiv.skewProd e'.toLinearEquiv ↑f

@[simp]
/-
**ContinuousLinearEquiv.skewProd_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLine
arEquiv`。
形式化陈述：skewProd_apply (e : M ≃L[R] M₂) (e' : M₃ ≃L[R] M₄) (f : M ->L[R] M₄) (x) :
 e.skewProd e' f x = (e x.1, e' x.2 + f x.1)
参数：e : M ≃L[R] M₂；e' : M₃ ≃L[R] M₄；f : M ->L[R] M₄；x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem skewProd_apply (e : M ≃L[R] M₂) (e' : M₃ ≃L[R] M₄) (f : M →L[R] M₄) (x) :
    e.skewProd e' f x = (e x.1, e' x.2 + f x.1) :=
  rfl

@[simp]
/-
**ContinuousLinearEquiv.skewProd_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Continuou
sLinearEquiv`。
形式化陈述：skewProd_symm_apply (e : M ≃L[R] M₂) (e' : M₃ ≃L[R] M₄) (f : M ->L[R] M₄) 
(x) : (e.skewProd e' f).symm x = (e.symm x.1, e'.symm (x.2 - f (e.symm x.1)))
参数：e : M ≃L[R] M₂；e' : M₃ ≃L[R] M₄；f : M ->L[R] M₄；x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem skewProd_symm_apply (e : M ≃L[R] M₂) (e' : M₃ ≃L[R] M₄) (f : M →L[R] M₄) (x) :
    (e.skewProd e' f).symm x = (e.symm x.1, e'.symm (x.2 - f (e.symm x.1))) :=
  rfl

variable (R) in
/-- The negation map as a continuous linear equivalence. -/
/-
**ContinuousLinearEquiv.neg** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearEquiv`。
形式化陈述：neg [ContinuousNeg M] : M ≃L[R] M where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The negation map as a continuous linear equivalence.
-/
def neg [ContinuousNeg M] :
    M ≃L[R] M where
  __ := LinearEquiv.neg R

@[simp]
/-
**ContinuousLinearEquiv.coe_neg** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearEquiv
`。
形式化陈述：coe_neg [ContinuousNeg M] : (neg R : M -> M) = -id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_neg [ContinuousNeg M] :
    (neg R : M → M) = -id := rfl

@[simp]
/-
**ContinuousLinearEquiv.neg_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearEqu
iv`。
形式化陈述：neg_apply [ContinuousNeg M] (x : M) : neg R x = -x
参数：x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem neg_apply [ContinuousNeg M] (x : M) :
    neg R x = -x := by simp

@[simp]
/-
**ContinuousLinearEquiv.symm_neg** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearEqui
v`。
形式化陈述：symm_neg [ContinuousNeg M] : (neg R : M ≃L[R] M).symm = neg R
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_neg [ContinuousNeg M] :
    (neg R : M ≃L[R] M).symm = neg R := rfl

end AddCommGroup

section Ring

variable {R : Type*} [Ring R] {R₂ : Type*} [Ring R₂] {M : Type*} [TopologicalSpace M]
  [AddCommGroup M] [Module R M] {M₂ : Type*} [TopologicalSpace M₂] [AddCommGroup M₂] [Module R₂ M₂]

variable {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]

/-
**ContinuousLinearEquiv.map_sub** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearEquiv
`。
形式化陈述：map_sub (e : M ≃SL[σ₁₂] M₂) (x y : M) : e (x - y) = e x - e y
参数：e : M ≃SL[σ₁₂] M₂；x y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.map_sub`：∀ {R : Type u_1} [inst : Ring R] {R₂ : Type
 u_2} [inst_1 : Ring R₂] {M : Type u_4} [inst_2 : TopologicalSpace M]   [inst_3 
: AddCommGroup M]…
-/
theorem map_sub (e : M ≃SL[σ₁₂] M₂) (x y : M) : e (x - y) = e x - e y :=
  (e : M →SL[σ₁₂] M₂).map_sub x y
/-
**ContinuousLinearEquiv.map_neg** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearEquiv
`。
形式化陈述：map_neg (e : M ≃SL[σ₁₂] M₂) (x : M) : e (-x) = -e x
参数：e : M ≃SL[σ₁₂] M₂；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.map_neg`：∀ {R : Type u_1} [inst : Ring R] {R₂ : Type
 u_2} [inst_1 : Ring R₂] {M : Type u_4} [inst_2 : TopologicalSpace M]   [inst_3 
: AddCommGroup M]…
-/
theorem map_neg (e : M ≃SL[σ₁₂] M₂) (x : M) : e (-x) = -e x :=
  (e : M →SL[σ₁₂] M₂).map_neg x

variable [Module R M₂] [IsTopologicalAddGroup M]

/-- A pair of continuous linear maps such that `f₁ ∘ f₂ = id` generates a continuous
linear equivalence `e` between `M` and `M₂ × f₁.ker` such that `(e x).2 = x` for `x ∈ f₁.ker`,
`(e x).1 = f₁ x`, and `(e (f₂ y)).2 = 0`. The map is given by `e x = (f₁ x, x - f₂ (f₁ x))`. -/
/-
**ContinuousLinearEquiv.equivOfRightInverse** 是 Mathlib 中的一个定义，位于命名空间 `Continuou
sLinearEquiv`。
形式化陈述：equivOfRightInverse (f₁ : M ->L[R] M₂) (f₂ : M₂ ->L[R] M) (h : Function.Ri
ghtInverse f₂ f₁) : M ≃L[R] M₂ × f₁.ker
参数：f₁ : M ->L[R] M₂；f₂ : M₂ ->L[R] M；h : Function.RightInverse f₂ f₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A pair of continuous linear maps such that `f₁ ∘ f₂ = id` generates a continuous
linear equivalence `e` between `M` and `M₂ × f₁.ker` such that `(e x).2 = x` for
 `x ∈ f₁.ker`,
`(e x).1 = f₁ x`, and `(e (f₂ y)).2 = 0`. The map is given by `e x = (f₁ x, x - 
f₂ (f₁ x))`.
-/
def equivOfRightInverse (f₁ : M →L[R] M₂) (f₂ : M₂ →L[R] M) (h : Function.RightInverse f₂ f₁) :
    M ≃L[R] M₂ × f₁.ker :=
  equivOfInverse (f₁.prod (f₁.projKerOfRightInverse f₂ h)) (f₂.coprod f₁.ker.subtypeL)
    (fun x => by simp) fun ⟨x, y⟩ => by simp [h x]

@[simp]
/-
**ContinuousLinearEquiv.fst_equivOfRightInverse** 是 Mathlib 中的一个定理，位于命名空间 `Conti
nuousLinearEquiv`。
形式化陈述：fst_equivOfRightInverse (f₁ : M ->L[R] M₂) (f₂ : M₂ ->L[R] M) (h : Functio
n.RightInverse f₂ f₁) (x : M) : (equivOfRightInverse f₁ f₂ h x).1 = f₁ x
参数：f₁ : M ->L[R] M₂；f₂ : M₂ ->L[R] M；h : Function.RightInverse f₂ f₁；x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_equivOfRightInverse (f₁ : M →L[R] M₂) (f₂ : M₂ →L[R] M)
    (h : Function.RightInverse f₂ f₁) (x : M) : (equivOfRightInverse f₁ f₂ h x).1 = f₁ x :=
  rfl

@[simp]
/-
**ContinuousLinearEquiv.snd_equivOfRightInverse** 是 Mathlib 中的一个定理，位于命名空间 `Conti
nuousLinearEquiv`。
形式化陈述：snd_equivOfRightInverse (f₁ : M ->L[R] M₂) (f₂ : M₂ ->L[R] M) (h : Functio
n.RightInverse f₂ f₁) (x : M) : ((equivOfRightInverse f₁ f₂ h x).2 : M) = x - f₂
 (f₁ x)
参数：f₁ : M ->L[R] M₂；f₂ : M₂ ->L[R] M；h : Function.RightInverse f₂ f₁；x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snd_equivOfRightInverse (f₁ : M →L[R] M₂) (f₂ : M₂ →L[R] M)
    (h : Function.RightInverse f₂ f₁) (x : M) :
    ((equivOfRightInverse f₁ f₂ h x).2 : M) = x - f₂ (f₁ x) :=
  rfl

@[simp]
/-
**ContinuousLinearEquiv.equivOfRightInverse_symm_apply** 是 Mathlib 中的一个定理，位于命名空间
 `ContinuousLinearEquiv`。
形式化陈述：equivOfRightInverse_symm_apply (f₁ : M ->L[R] M₂) (f₂ : M₂ ->L[R] M) (h : 
Function.RightInverse f₂ f₁) (y : M₂ × f₁.ker) : (equivOfRightInverse f₁ f₂ h).s
ymm y = f₂ y.1 + y.2
参数：f₁ : M ->L[R] M₂；f₂ : M₂ ->L[R] M；h : Function.RightInverse f₂ f₁；y : M₂ × f₁
.ker。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem equivOfRightInverse_symm_apply (f₁ : M →L[R] M₂) (f₂ : M₂ →L[R] M)
    (h : Function.RightInverse f₂ f₁) (y : M₂ × f₁.ker) :
    (equivOfRightInverse f₁ f₂ h).symm y = f₂ y.1 + y.2 :=
  rfl

end Ring

section RestrictScalars

set_option backward.defeqAttrib.useBackward true in
/-- If M is an `R`-module and `S`-module and `R`-module structure is defined by an action of `R` on
`S` (formally, we have two scalar towers), then any `S`-linear equivalence on `M` is an `R`-linear
equivalence. -/
@[simps! toLinearEquiv apply symm_apply]
/-
**ContinuousLinearEquiv.restrictScalars** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLin
earEquiv`。
形式化陈述：restrictScalars (R : Type*) {S : Type*} {M : Type*} [Semiring R] [Semiring
 S] [AddCommMonoid M] [Module R M] [Module S M] [TopologicalSpace M] [LinearMap.
CompatibleSMul M M R S] (f : M ≃L[S] M) : M ≃L[R] M where toLinearEquiv
参数：R : Type*；f : M ≃L[S] M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If M is an `R`-module and `S`-module and `R`-module structure is defined by an a
ction of `R` on
`S` (formally, we have two scalar towers), then any `S`-linear equivalence on `M
` is an `R`-linear
equivalence.
-/
def restrictScalars (R : Type*) {S : Type*} {M : Type*}
    [Semiring R] [Semiring S] [AddCommMonoid M] [Module R M] [Module S M] [TopologicalSpace M]
    [LinearMap.CompatibleSMul M M R S] (f : M ≃L[S] M) : M ≃L[R] M where
  toLinearEquiv := f.toLinearEquiv.restrictScalars R

end RestrictScalars

end ContinuousLinearEquiv

namespace ContinuousLinearMap

variable {R : Type*} {M M₂ M₃ : Type*}
  [TopologicalSpace M] [TopologicalSpace M₂] [TopologicalSpace M₃]

variable [Semiring R]
  [AddCommMonoid M] [Module R M]
  [AddCommMonoid M₂] [Module R M₂]
  [AddCommMonoid M₃] [Module R M₃]

/-- A continuous linear map is invertible if it is the forward direction of a continuous linear
equivalence. -/
/-
**ContinuousLinearMap.IsInvertible** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMa
p`。
形式化陈述：IsInvertible (f : M ->L[R] M₂) : Prop
参数：f : M ->L[R] M₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A continuous linear map is invertible if it is the forward direction of a contin
uous linear
equivalence.
-/
def IsInvertible (f : M →L[R] M₂) : Prop :=
  ∃ (A : M ≃L[R] M₂), A = f

open scoped Classical in
/-- Introduce a function `inverse` from `M →L[R] M₂` to `M₂ →L[R] M`, which sends `f` to `f.symm` if
`f` is a continuous linear equivalence and to `0` otherwise.  This definition is somewhat ad hoc,
but one needs a fully (rather than partially) defined inverse function for some purposes, including
for calculus. -/
/-
**ContinuousLinearMap.inverse** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap`。
形式化陈述：inverse : (M ->L[R] M₂) -> M₂ ->L[R] M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Introduce a function `inverse` from `M →L[R] M₂` to `M₂ →L[R] M`, which sends `f
` to `f.symm` if
`f` is a continuous linear equivalence and to `0` otherwise.  This definition is
 somewhat ad hoc,
but one needs a fully (rather than partially) defined inverse function for some 
purposes, including
for calculus.
-/
noncomputable def inverse : (M →L[R] M₂) → M₂ →L[R] M := fun f =>
  if h : f.IsInvertible then ((Classical.choose h).symm : M₂ →L[R] M) else 0
/-
**ContinuousLinearMap.isInvertible_equiv** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLi
nearMap`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} {M₂ : Type u_3} [inst : TopologicalSpace M
] [inst_1 : TopologicalSpace M₂]   [inst_2 : Semiring R] [inst_3 : AddCommMonoid
 M] [inst_4 : _root_.Module R M] [inst_5 : AddCommMonoid M₂]   [inst_6 : _root_.
Module R M₂] {f : M ≃L[R] M₂}, (↑f).IsInvertible
参数：↑f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma isInvertible_equiv {f : M ≃L[R] M₂} : IsInvertible (f : M →L[R] M₂) := ⟨f, rfl⟩

/-- By definition, if `f` is invertible then `inverse f = f.symm`. -/
@[simp]
/-
**ContinuousLinearMap.inverse_equiv** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearM
ap`。
形式化陈述：inverse_equiv (e : M ≃L[R] M₂) : inverse (e : M ->L[R] M₂) = e.symm
参数：e : M ≃L[R] M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Classical.choose.congr_simp`：∀ {α : Sort u} {p p_1 : α → Prop} (e_p : p 
= p_1) (h : ∃ x, p x), Classical.choose h = Classical.choose ⋯
· 使用定理 `Classical.choose_eq`：∀ {α : Sort u_1} (a : α), ⋯.choose = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
By definition, if `f` is invertible then `inverse f = f.symm`.
-/
theorem inverse_equiv (e : M ≃L[R] M₂) : inverse (e : M →L[R] M₂) = e.symm := by
  simp [inverse]

/-- By definition, if `f` is not invertible then `inverse f = 0`. -/
/-
**ContinuousLinearMap.inverse_of_not_isInvertible** 是 Mathlib 中的一个定理，位于命名空间 `Con
tinuousLinearMap`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} {M₂ : Type u_3} [inst : TopologicalSpace M
] [inst_1 : TopologicalSpace M₂]   [inst_2 : Semiring R] [inst_3 : AddCommMonoid
 M] [inst_4 : _root_.Module R M] [inst_5 : AddCommMonoid M₂]   [inst_6 : _root_.
Module R M₂] {f : M →L[R] M₂}, ¬f.IsInvertible → f.inverse = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc

--- 原说明 ---
By definition, if `f` is not invertible then `inverse f = 0`.
-/
@[simp] lemma inverse_of_not_isInvertible
    {f : M →L[R] M₂} (hf : ¬ f.IsInvertible) : f.inverse = 0 :=
  dif_neg hf

@[simp]
/-
**ContinuousLinearMap.isInvertible_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Continuou
sLinearMap`。
形式化陈述：isInvertible_zero_iff : IsInvertible (0 : M ->L[R] M₂) ↔ Subsingleton M ∧ 
Subsingleton M₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearEquiv.injective`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst
 : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁}   [in
st_2 : RingHomInvPair…
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Equiv.subsingleton`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) [Subsingleto
n β], Subsingleton α
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `continuous_zero`：∀ {M : Type u_3} {X : Type u_5} [inst : TopologicalSpac
e X] [inst_1 : TopologicalSpace M] [inst_2 : Zero M],   Continuous 0
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
-/
theorem isInvertible_zero_iff :
    IsInvertible (0 : M →L[R] M₂) ↔ Subsingleton M ∧ Subsingleton M₂ := by
  refine ⟨fun ⟨e, he⟩ ↦ ?_, ?_⟩
  · have A : Subsingleton M := by
      refine ⟨fun x y ↦ e.injective ?_⟩
      simp [he, ← ContinuousLinearEquiv.coe_coe]
    exact ⟨A, e.toEquiv.symm.subsingleton⟩
  · rintro ⟨hM, hM₂⟩
    let e : M ≃L[R] M₂ :=
    { toFun := 0
      invFun := 0
      left_inv x := Subsingleton.elim _ _
      right_inv x := Subsingleton.elim _ _
      map_add' x y := Subsingleton.elim _ _
      map_smul' c x := Subsingleton.elim _ _ }
    refine ⟨e, ?_⟩
    ext x
    exact Subsingleton.elim _ _
/-
**ContinuousLinearMap.inverse_zero** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMa
p`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} {M₂ : Type u_3} [inst : TopologicalSpace M
] [inst_1 : TopologicalSpace M₂]   [inst_2 : Semiring R] [inst_3 : AddCommMonoid
 M] [inst_4 : _root_.Module R M] [inst_5 : AddCommMonoid M₂]   [inst_6 : _root_.
Module R M₂], ContinuousLinearMap.inverse 0 = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ContinuousLinearMap.isInvertible_zero_iff`：isInvertible_zero_iff : IsInv
ertible (0 : M ->L[R] M₂) ↔ Subsingleton M ∧ Subsingleton M₂
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `ContinuousLinearMap.inverse_of_not_isInvertible`：∀ {R : Type u_1} {M : T
ype u_2} {M₂ : Type u_3} [inst : TopologicalSpace M] [inst_1 : TopologicalSpace 
M₂]   [inst_2 : Semiring R] [inst_3 :…
-/
@[simp] theorem inverse_zero : inverse (0 : M →L[R] M₂) = 0 := by
  by_cases h : IsInvertible (0 : M →L[R] M₂)
  · rcases isInvertible_zero_iff.1 h with ⟨hM, hM₂⟩
    ext x
    exact Subsingleton.elim _ _
  · exact inverse_of_not_isInvertible h
/-
**ContinuousLinearMap.IsInvertible.comp** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLin
earMap.IsInvertible`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} {M₂ : Type u_3} {M₃ : Type u_4} [inst : To
pologicalSpace M]   [inst_1 : TopologicalSpace M₂] [inst_2 : TopologicalSpace M₃
] [inst_3 : Semiring R] [inst_4 : AddCommMonoid M]   [inst_5 : _root_.Module R M
] [inst_6 : AddCommMonoid M₂] [inst_7 : _root_.Module R M₂] [inst_8 : AddCommMon
oid M₃]   [inst_9 : _root_.Module R M₃] {g : M₂ →L[R] M₃} {f : M →L[R] M₂},   g.
IsInvertible → f.IsInvertible → (g ∘SL f).IsInvertible
参数：g ∘SL f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsInvertible.comp {g : M₂ →L[R] M₃} {f : M →L[R] M₂}
    (hg : g.IsInvertible) (hf : f.IsInvertible) : (g ∘L f).IsInvertible := by
  rcases hg with ⟨N, rfl⟩
  rcases hf with ⟨M, rfl⟩
  exact ⟨M.trans N, rfl⟩
/-
**ContinuousLinearMap.IsInvertible.of_inverse** 是 Mathlib 中的一个定理，位于命名空间 `Continu
ousLinearMap.IsInvertible`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} {M₂ : Type u_3} [inst : TopologicalSpace M
] [inst_1 : TopologicalSpace M₂]   [inst_2 : Semiring R] [inst_3 : AddCommMonoid
 M] [inst_4 : _root_.Module R M] [inst_5 : AddCommMonoid M₂]   [inst_6 : _root_.
Module R M₂] {f : M →L[R] M₂} {g : M₂ →L[R] M},   f ∘SL g = ContinuousLinearMap.
id R M₂ → g ∘SL f = ContinuousLinearMap.id R M → f.IsInvertible
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsInvertible.of_inverse {f : M →L[R] M₂} {g : M₂ →L[R] M}
    (hf : f ∘L g = .id R M₂) (hg : g ∘L f = .id R M) :
    f.IsInvertible :=
  ⟨ContinuousLinearEquiv.equivOfInverse' _ _ hf hg, rfl⟩
/-
**ContinuousLinearMap.inverse_eq** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLinearMap`
。
形式化陈述：inverse_eq {f : M ->L[R] M₂} {g : M₂ ->L[R] M} (hf : f ∘L g = .id R M₂) (h
g : g ∘L f = .id R M) : f.inverse = g
参数：hf : f ∘L g = .id R M₂；hg : g ∘L f = .id R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.inverse_equiv`：inverse_equiv (e : M ≃L[R] M₂) : inve
rse (e : M ->L[R] M₂) = e.symm
-/
lemma inverse_eq {f : M →L[R] M₂} {g : M₂ →L[R] M}
    (hf : f ∘L g = .id R M₂) (hg : g ∘L f = .id R M) :
    f.inverse = g := by
  have : f = ContinuousLinearEquiv.equivOfInverse' f g hf hg := rfl
  rw [this, inverse_equiv]
  rfl
/-
**ContinuousLinearMap.IsInvertible.inverse_apply_eq** 是 Mathlib 中的一个定理，位于命名空间 `C
ontinuousLinearMap.IsInvertible`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} {M₂ : Type u_3} [inst : TopologicalSpace M
] [inst_1 : TopologicalSpace M₂]   [inst_2 : Semiring R] [inst_3 : AddCommMonoid
 M] [inst_4 : _root_.Module R M] [inst_5 : AddCommMonoid M₂]   [inst_6 : _root_.
Module R M₂] {f : M →L[R] M₂} {x : M} {y : M₂}, f.IsInvertible → (f.inverse y = 
x ↔ y = f x)
参数：f.inverse y = x ↔ y = f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.inverse_equiv`：inverse_equiv (e : M ≃L[R] M₂) : inve
rse (e : M ->L[R] M₂) = e.symm
· 使用定理 `ContinuousLinearEquiv.symm_apply_eq`：symm_apply_eq (e : M₁ ≃SL[σ₁₂] M₂) 
{x y} : e.symm x = y ↔ x = e y
-/
lemma IsInvertible.inverse_apply_eq {f : M →L[R] M₂} {x : M} {y : M₂} (hf : f.IsInvertible) :
    f.inverse y = x ↔ y = f x := by
  rcases hf with ⟨M, rfl⟩
  simp only [inverse_equiv, ContinuousLinearEquiv.coe_coe]
  exact ContinuousLinearEquiv.symm_apply_eq M
/-
**ContinuousLinearMap.isInvertible_equiv_comp** 是 Mathlib 中的一个定理，位于命名空间 `Continu
ousLinearMap`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} {M₂ : Type u_3} {M₃ : Type u_4} [inst : To
pologicalSpace M]   [inst_1 : TopologicalSpace M₂] [inst_2 : TopologicalSpace M₃
] [inst_3 : Semiring R] [inst_4 : AddCommMonoid M]   [inst_5 : _root_.Module R M
] [inst_6 : AddCommMonoid M₂] [inst_7 : _root_.Module R M₂] [inst_8 : AddCommMon
oid M₃]   [inst_9 : _root_.Module R M₃] {e : M₂ ≃L[R] M₃} {f : M →L[R] M₂}, (↑e 
∘SL f).IsInvertible ↔ f.IsInvertible
参数：↑e ∘SL f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearEquiv.symm_apply_apply`：symm_apply_apply (e : M₁ ≃SL[σ₁₂
] M₂) (b : M₁) : e.symm (e b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[simp] lemma isInvertible_equiv_comp {e : M₂ ≃L[R] M₃} {f : M →L[R] M₂} :
    ((e : M₂ →L[R] M₃) ∘L f).IsInvertible ↔ f.IsInvertible := by
  constructor
  · rintro ⟨A, hA⟩
    have : f = e.symm ∘L ((e : M₂ →L[R] M₃) ∘L f) := by ext; simp
    rw [this, ← hA]
    simp
  · rintro ⟨M, rfl⟩
    simp
/-
**ContinuousLinearMap.isInvertible_comp_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Continu
ousLinearMap`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} {M₂ : Type u_3} {M₃ : Type u_4} [inst : To
pologicalSpace M]   [inst_1 : TopologicalSpace M₂] [inst_2 : TopologicalSpace M₃
] [inst_3 : Semiring R] [inst_4 : AddCommMonoid M]   [inst_5 : _root_.Module R M
] [inst_6 : AddCommMonoid M₂] [inst_7 : _root_.Module R M₂] [inst_8 : AddCommMon
oid M₃]   [inst_9 : _root_.Module R M₃] {e : M₃ ≃L[R] M} {f : M →L[R] M₂}, (f ∘S
L ↑e).IsInvertible ↔ f.IsInvertible
参数：f ∘SL ↑e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearEquiv.apply_symm_apply`：apply_symm_apply (e : M₁ ≃SL[σ₁₂
] M₂) (c : M₂) : e (e.symm c) = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[simp] lemma isInvertible_comp_equiv {e : M₃ ≃L[R] M} {f : M →L[R] M₂} :
    (f ∘L (e : M₃ →L[R] M)).IsInvertible ↔ f.IsInvertible := by
  constructor
  · rintro ⟨A, hA⟩
    have : f = (f ∘L (e : M₃ →L[R] M)) ∘L e.symm := by ext; simp
    rw [this, ← hA]
    simp
  · rintro ⟨M, rfl⟩
    simp
/-
**ContinuousLinearMap.inverse_equiv_comp** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLi
nearMap`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} {M₂ : Type u_3} {M₃ : Type u_4} [inst : To
pologicalSpace M]   [inst_1 : TopologicalSpace M₂] [inst_2 : TopologicalSpace M₃
] [inst_3 : Semiring R] [inst_4 : AddCommMonoid M]   [inst_5 : _root_.Module R M
] [inst_6 : AddCommMonoid M₂] [inst_7 : _root_.Module R M₂] [inst_8 : AddCommMon
oid M₃]   [inst_9 : _root_.Module R M₃] {e : M₂ ≃L[R] M₃} {f : M →L[R] M₂}, (↑e 
∘SL f).inverse = f.inverse ∘SL ↑e.symm
参数：↑e ∘SL f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.inverse_equiv`：inverse_equiv (e : M ≃L[R] M₂) : inve
rse (e : M ->L[R] M₂) = e.symm
· 使用定理 `ContinuousLinearMap.comp.congr_simp`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {
R₃ : Type u_3} [inst : Semiring R₁] [inst_1 : Semiring R₂] [inst_2 : Semiring R₃
]   {σ₁₂ : R₁ →+* R₂} {σ₂…
· 使用定理 `ContinuousLinearMap.inverse_of_not_isInvertible`：∀ {R : Type u_1} {M : T
ype u_2} {M₂ : Type u_3} [inst : TopologicalSpace M] [inst_1 : TopologicalSpace 
M₂]   [inst_2 : Semiring R] [inst_3 :…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ContinuousLinearMap.zero_comp`：zero_comp (f : M₁ ->SL[σ₁₂] M₂) : (0 : M₂
 ->SL[σ₂₃] M₃) ∘SL f = 0
-/
@[simp] lemma inverse_equiv_comp {e : M₂ ≃L[R] M₃} {f : M →L[R] M₂} :
    (e ∘L f).inverse = f.inverse ∘L (e.symm : M₃ →L[R] M₂) := by
  by_cases hf : f.IsInvertible
  · rcases hf with ⟨A, rfl⟩
    simp only [ContinuousLinearEquiv.comp_coe, inverse_equiv, ContinuousLinearEquiv.coe_inj]
    rfl
  · rw [inverse_of_not_isInvertible (by simp [hf]), inverse_of_not_isInvertible hf, zero_comp]
/-
**ContinuousLinearMap.inverse_comp_equiv** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLi
nearMap`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} {M₂ : Type u_3} {M₃ : Type u_4} [inst : To
pologicalSpace M]   [inst_1 : TopologicalSpace M₂] [inst_2 : TopologicalSpace M₃
] [inst_3 : Semiring R] [inst_4 : AddCommMonoid M]   [inst_5 : _root_.Module R M
] [inst_6 : AddCommMonoid M₂] [inst_7 : _root_.Module R M₂] [inst_8 : AddCommMon
oid M₃]   [inst_9 : _root_.Module R M₃] {e : M₃ ≃L[R] M} {f : M →L[R] M₂}, (f ∘S
L ↑e).inverse = ↑e.symm ∘SL f.inverse
参数：f ∘SL ↑e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.inverse_equiv`：inverse_equiv (e : M ≃L[R] M₂) : inve
rse (e : M ->L[R] M₂) = e.symm
· 使用定理 `ContinuousLinearMap.comp.congr_simp`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {
R₃ : Type u_3} [inst : Semiring R₁] [inst_1 : Semiring R₂] [inst_2 : Semiring R₃
]   {σ₁₂ : R₁ →+* R₂} {σ₂…
· 使用定理 `ContinuousLinearMap.inverse_of_not_isInvertible`：∀ {R : Type u_1} {M : T
ype u_2} {M₂ : Type u_3} [inst : TopologicalSpace M] [inst_1 : TopologicalSpace 
M₂]   [inst_2 : Semiring R] [inst_3 :…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ContinuousLinearMap.comp_zero`：comp_zero (g : M₂ ->SL[σ₂₃] M₃) : g ∘SL (
0 : M₁ ->SL[σ₁₂] M₂) = 0
-/
@[simp] lemma inverse_comp_equiv {e : M₃ ≃L[R] M} {f : M →L[R] M₂} :
    (f ∘L e).inverse = (e.symm : M →L[R] M₃) ∘L f.inverse := by
  by_cases hf : f.IsInvertible
  · rcases hf with ⟨A, rfl⟩
    simp only [ContinuousLinearEquiv.comp_coe, inverse_equiv, ContinuousLinearEquiv.coe_inj]
    rfl
  · rw [inverse_of_not_isInvertible (by simp [hf]), inverse_of_not_isInvertible hf, comp_zero]
/-
**ContinuousLinearMap.IsInvertible.inverse_comp_of_left** 是 Mathlib 中的一个定理，位于命名空
间 `ContinuousLinearMap.IsInvertible`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} {M₂ : Type u_3} {M₃ : Type u_4} [inst : To
pologicalSpace M]   [inst_1 : TopologicalSpace M₂] [inst_2 : TopologicalSpace M₃
] [inst_3 : Semiring R] [inst_4 : AddCommMonoid M]   [inst_5 : _root_.Module R M
] [inst_6 : AddCommMonoid M₂] [inst_7 : _root_.Module R M₂] [inst_8 : AddCommMon
oid M₃]   [inst_9 : _root_.Module R M₃] {g : M₂ →L[R] M₃} {f : M →L[R] M₂},   g.
IsInvertible → (g ∘SL f).inverse = f.inverse ∘SL g.inverse
参数：g ∘SL f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.inverse_equiv_comp`：∀ {R : Type u_1} {M : Type u_2} 
{M₂ : Type u_3} {M₃ : Type u_4} [inst : TopologicalSpace M]   [inst_1 : Topologi
calSpace M₂] [inst_2 : Topol…
· 使用定理 `ContinuousLinearMap.comp.congr_simp`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {
R₃ : Type u_3} [inst : Semiring R₁] [inst_1 : Semiring R₂] [inst_2 : Semiring R₃
]   {σ₁₂ : R₁ →+* R₂} {σ₂…
· 使用定理 `ContinuousLinearMap.inverse_equiv`：inverse_equiv (e : M ≃L[R] M₂) : inve
rse (e : M ->L[R] M₂) = e.symm
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsInvertible.inverse_comp_of_left {g : M₂ →L[R] M₃} {f : M →L[R] M₂}
    (hg : g.IsInvertible) : (g ∘L f).inverse = f.inverse ∘L g.inverse := by
  rcases hg with ⟨N, rfl⟩
  simp
/-
**ContinuousLinearMap.IsInvertible.inverse_comp_apply_of_left** 是 Mathlib 中的一个定理
，位于命名空间 `ContinuousLinearMap.IsInvertible`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} {M₂ : Type u_3} {M₃ : Type u_4} [inst : To
pologicalSpace M]   [inst_1 : TopologicalSpace M₂] [inst_2 : TopologicalSpace M₃
] [inst_3 : Semiring R] [inst_4 : AddCommMonoid M]   [inst_5 : _root_.Module R M
] [inst_6 : AddCommMonoid M₂] [inst_7 : _root_.Module R M₂] [inst_8 : AddCommMon
oid M₃]   [inst_9 : _root_.Module R M₃] {g : M₂ →L[R] M₃} {f : M →L[R] M₂} {v : 
M₃},   g.IsInvertible → (g ∘SL f).inverse v = f.inverse (g.inverse v)
参数：g ∘SL f；g.inverse v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.IsInvertible.inverse_comp_of_left`：∀ {R : Type u_1} 
{M : Type u_2} {M₂ : Type u_3} {M₃ : Type u_4} [inst : TopologicalSpace M]   [in
st_1 : TopologicalSpace M₂] [inst_2 : Topol…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsInvertible.inverse_comp_apply_of_left {g : M₂ →L[R] M₃} {f : M →L[R] M₂} {v : M₃}
    (hg : g.IsInvertible) : (g ∘L f).inverse v = f.inverse (g.inverse v) := by
  simp only [hg.inverse_comp_of_left, comp_apply]
/-
**ContinuousLinearMap.IsInvertible.inverse_comp_of_right** 是 Mathlib 中的一个定理，位于命名
空间 `ContinuousLinearMap.IsInvertible`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} {M₂ : Type u_3} {M₃ : Type u_4} [inst : To
pologicalSpace M]   [inst_1 : TopologicalSpace M₂] [inst_2 : TopologicalSpace M₃
] [inst_3 : Semiring R] [inst_4 : AddCommMonoid M]   [inst_5 : _root_.Module R M
] [inst_6 : AddCommMonoid M₂] [inst_7 : _root_.Module R M₂] [inst_8 : AddCommMon
oid M₃]   [inst_9 : _root_.Module R M₃] {g : M₂ →L[R] M₃} {f : M →L[R] M₂},   f.
IsInvertible → (g ∘SL f).inverse = f.inverse ∘SL g.inverse
参数：g ∘SL f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.inverse_comp_equiv`：∀ {R : Type u_1} {M : Type u_2} 
{M₂ : Type u_3} {M₃ : Type u_4} [inst : TopologicalSpace M]   [inst_1 : Topologi
calSpace M₂] [inst_2 : Topol…
· 使用定理 `ContinuousLinearMap.comp.congr_simp`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {
R₃ : Type u_3} [inst : Semiring R₁] [inst_1 : Semiring R₂] [inst_2 : Semiring R₃
]   {σ₁₂ : R₁ →+* R₂} {σ₂…
· 使用定理 `ContinuousLinearMap.inverse_equiv`：inverse_equiv (e : M ≃L[R] M₂) : inve
rse (e : M ->L[R] M₂) = e.symm
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsInvertible.inverse_comp_of_right {g : M₂ →L[R] M₃} {f : M →L[R] M₂}
    (hf : f.IsInvertible) : (g ∘L f).inverse = f.inverse ∘L g.inverse := by
  rcases hf with ⟨M, rfl⟩
  simp
/-
**ContinuousLinearMap.IsInvertible.inverse_comp_apply_of_right** 是 Mathlib 中的一个定
理，位于命名空间 `ContinuousLinearMap.IsInvertible`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} {M₂ : Type u_3} {M₃ : Type u_4} [inst : To
pologicalSpace M]   [inst_1 : TopologicalSpace M₂] [inst_2 : TopologicalSpace M₃
] [inst_3 : Semiring R] [inst_4 : AddCommMonoid M]   [inst_5 : _root_.Module R M
] [inst_6 : AddCommMonoid M₂] [inst_7 : _root_.Module R M₂] [inst_8 : AddCommMon
oid M₃]   [inst_9 : _root_.Module R M₃] {g : M₂ →L[R] M₃} {f : M →L[R] M₂} {v : 
M₃},   f.IsInvertible → (g ∘SL f).inverse v = f.inverse (g.inverse v)
参数：g ∘SL f；g.inverse v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.IsInvertible.inverse_comp_of_right`：∀ {R : Type u_1}
 {M : Type u_2} {M₂ : Type u_3} {M₃ : Type u_4} [inst : TopologicalSpace M]   [i
nst_1 : TopologicalSpace M₂] [inst_2 : Topol…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsInvertible.inverse_comp_apply_of_right {g : M₂ →L[R] M₃} {f : M →L[R] M₂} {v : M₃}
    (hf : f.IsInvertible) : (g ∘L f).inverse v = f.inverse (g.inverse v) := by
  simp only [hf.inverse_comp_of_right, comp_apply]

@[simp]
/-
**ContinuousLinearMap.ringInverse_equiv** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLin
earMap`。
形式化陈述：ringInverse_equiv (e : M ≃L[R] M) : (↑e)⁻¹ʳ = inverse (e : M ->L[R] M)
参数：e : M ≃L[R] M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ring.inverse_invertible`：Ring.inverse_invertible (x : α) [Invertible x] 
: x⁻¹ʳ = ⅟x
· 使用定理 `invOf_units`：invOf_units [Monoid α] (u : αˣ) [Invertible (u : α)] : ⅟(u 
: α) = ↑u⁻¹
· 使用定理 `ContinuousLinearMap.inverse_equiv`：inverse_equiv (e : M ≃L[R] M₂) : inve
rse (e : M ->L[R] M₂) = e.symm
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem ringInverse_equiv (e : M ≃L[R] M) : (↑e)⁻¹ʳ = inverse (e : M →L[R] M) := by
  suffices ((ContinuousLinearEquiv.unitsEquiv _ _).symm e : M →L[R] M)⁻¹ʳ = inverse ↑e by
    convert! this
  simp
  rfl

/-- The function `ContinuousLinearEquiv.inverse` can be written in terms of `Ring.inverse` for the
ring of self-maps of the domain. -/
/-
**ContinuousLinearMap.inverse_eq_ringInverse** 是 Mathlib 中的一个定理，位于命名空间 `Continuo
usLinearMap`。
形式化陈述：inverse_eq_ringInverse (e : M ≃L[R] M₂) (f : M ->L[R] M₂) : inverse f = ((
e.symm : M₂ ->L[R] M).comp f)⁻¹ʳ ∘L e.symm
参数：e : M ≃L[R] M₂；f : M ->L[R] M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ContinuousLinearMap.inverse_equiv`：inverse_equiv (e : M ≃L[R] M₂) : inve
rse (e : M ->L[R] M₂) = e.symm
· 使用定理 `ContinuousLinearMap.comp.congr_simp`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {
R₃ : Type u_3} [inst : Semiring R₁] [inst_1 : Semiring R₂] [inst_2 : Semiring R₃
]   {σ₁₂ : R₁ →+* R₂} {σ₂…
· 使用定理 `ContinuousLinearMap.ringInverse_equiv`：ringInverse_equiv (e : M ≃L[R] M)
 : (↑e)⁻¹ʳ = inverse (e : M ->L[R] M)
· 使用定理 `ContinuousLinearEquiv.apply_symm_apply`：apply_symm_apply (e : M₁ ≃SL[σ₁₂
] M₂) (c : M₂) : e (e.symm c) = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `ContinuousLinearMap.inverse_of_not_isInvertible`：∀ {R : Type u_1} {M : T
ype u_2} {M₂ : Type u_3} [inst : TopologicalSpace M] [inst_1 : TopologicalSpace 
M₂]   [inst_2 : Semiring R] [inst_3 :…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Ring.inverse_non_unit`：inverse_non_unit (x : M₀) (h : ¬IsUnit x) : x⁻¹ʳ 
= 0
· 使用定理 `ContinuousLinearMap.zero_comp`：zero_comp (f : M₁ ->SL[σ₁₂] M₂) : (0 : M₂
 ->SL[σ₂₃] M₃) ∘SL f = 0

--- 原说明 ---
The function `ContinuousLinearEquiv.inverse` can be written in terms of `Ring.in
verse` for the
ring of self-maps of the domain.
-/
theorem inverse_eq_ringInverse (e : M ≃L[R] M₂) (f : M →L[R] M₂) :
    inverse f = ((e.symm : M₂ →L[R] M).comp f)⁻¹ʳ ∘L e.symm := by
  by_cases h₁ : f.IsInvertible
  · obtain ⟨e', he'⟩ := h₁
    rw [← he']
    change _ = (e'.trans e.symm : M →L[R] M)⁻¹ʳ ∘L (e.symm : M₂ →L[R] M)
    ext
    simp
  · suffices ¬IsUnit ((e.symm : M₂ →L[R] M).comp f) by simp [this, h₁]
    contrapose h₁
    rcases h₁ with ⟨F, hF⟩
    use (ContinuousLinearEquiv.unitsEquiv _ _ F).trans e
    ext
    dsimp
    rw [hF]
    simp
/-
**ContinuousLinearMap.ringInverse_eq_inverse** 是 Mathlib 中的一个定理，位于命名空间 `Continuo
usLinearMap`。
形式化陈述：ringInverse_eq_inverse : Ring.inverse = inverse (R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ContinuousLinearMap.inverse_eq_ringInverse`：inverse_eq_ringInverse (e : 
M ≃L[R] M₂) (f : M ->L[R] M₂) : inverse f = ((e.symm : M₂ ->L[R] M).comp f)⁻¹ʳ ∘
L e.symm
· 使用定理 `ContinuousLinearMap.comp.congr_simp`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {
R₃ : Type u_3} [inst : Semiring R₁] [inst_1 : Semiring R₂] [inst_2 : Semiring R₃
]   {σ₁₂ : R₁ →+* R₂} {σ₂…
· 使用定理 `ContinuousLinearMap.id_comp`：id_comp (f : M₁ ->SL[σ₁₂] M₂) : .id R₂ M₂ ∘
SL f = f
· 使用定理 `ContinuousLinearMap.comp_id`：comp_id (f : M₁ ->SL[σ₁₂] M₂) : f ∘SL .id R
₁ M₁ = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ringInverse_eq_inverse : Ring.inverse = inverse (R := R) (M := M) := by
  ext
  simp [inverse_eq_ringInverse (ContinuousLinearEquiv.refl R M)]
/-
**ContinuousLinearMap.inverse_id** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`
。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : TopologicalSpace M] [inst_1 : Semi
ring R] [inst_2 : AddCommMonoid M]   [inst_3 : _root_.Module R M], (ContinuousLi
nearMap.id R M).inverse = ContinuousLinearMap.id R M
参数：ContinuousLinearMap.id R M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearMap.ringInverse_eq_inverse`：ringInverse_eq_inverse : Rin
g.inverse = inverse (R
· 使用定理 `Ring.inverse_one`：inverse_one : (1 : M₀)⁻¹ʳ = 1
-/
@[simp] theorem inverse_id : (ContinuousLinearMap.id R M).inverse = .id R M := by
  rw [← ringInverse_eq_inverse]
  exact Ring.inverse_one _

namespace IsInvertible

variable {f : M →L[R] M₂}

@[simp]
/-
**ContinuousLinearMap.IsInvertible.self_comp_inverse** 是 Mathlib 中的一个定理，位于命名空间 `
ContinuousLinearMap.IsInvertible`。
形式化陈述：self_comp_inverse (hf : f.IsInvertible) : f ∘L f.inverse = .id _ _
参数：hf : f.IsInvertible。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.comp.congr_simp`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {
R₃ : Type u_3} [inst : Semiring R₁] [inst_1 : Semiring R₂] [inst_2 : Semiring R₃
]   {σ₁₂ : R₁ →+* R₂} {σ₂…
· 使用定理 `ContinuousLinearMap.inverse_equiv`：inverse_equiv (e : M ≃L[R] M₂) : inve
rse (e : M ->L[R] M₂) = e.symm
· 使用定理 `ContinuousLinearEquiv.coe_comp_coe_symm`：coe_comp_coe_symm (e : M₁ ≃SL[σ
₁₂] M₂) : (e : M₁ ->SL[σ₁₂] M₂).comp (e.symm : M₂ ->SL[σ₂₁] M₁) = ContinuousLine
arMap.id R₂ M₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem self_comp_inverse (hf : f.IsInvertible) : f ∘L f.inverse = .id _ _ := by
  rcases hf with ⟨e, rfl⟩
  simp

@[simp]
/-
**ContinuousLinearMap.IsInvertible.self_apply_inverse** 是 Mathlib 中的一个定理，位于命名空间 
`ContinuousLinearMap.IsInvertible`。
形式化陈述：self_apply_inverse (hf : f.IsInvertible) (y : M₂) : f (f.inverse y) = y
参数：hf : f.IsInvertible；y : M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.inverse_equiv`：inverse_equiv (e : M ≃L[R] M₂) : inve
rse (e : M ->L[R] M₂) = e.symm
· 使用定理 `ContinuousLinearEquiv.apply_symm_apply`：apply_symm_apply (e : M₁ ≃SL[σ₁₂
] M₂) (c : M₂) : e (e.symm c) = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem self_apply_inverse (hf : f.IsInvertible) (y : M₂) : f (f.inverse y) = y := by
  rcases hf with ⟨e, rfl⟩
  simp

@[simp]
/-
**ContinuousLinearMap.IsInvertible.inverse_comp_self** 是 Mathlib 中的一个定理，位于命名空间 `
ContinuousLinearMap.IsInvertible`。
形式化陈述：inverse_comp_self (hf : f.IsInvertible) : f.inverse ∘L f = .id _ _
参数：hf : f.IsInvertible。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.comp.congr_simp`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {
R₃ : Type u_3} [inst : Semiring R₁] [inst_1 : Semiring R₂] [inst_2 : Semiring R₃
]   {σ₁₂ : R₁ →+* R₂} {σ₂…
· 使用定理 `ContinuousLinearMap.inverse_equiv`：inverse_equiv (e : M ≃L[R] M₂) : inve
rse (e : M ->L[R] M₂) = e.symm
· 使用定理 `ContinuousLinearEquiv.coe_symm_comp_coe`：coe_symm_comp_coe (e : M₁ ≃SL[σ
₁₂] M₂) : (e.symm : M₂ ->SL[σ₂₁] M₁).comp (e : M₁ ->SL[σ₁₂] M₂) = ContinuousLine
arMap.id R₁ M₁
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inverse_comp_self (hf : f.IsInvertible) : f.inverse ∘L f = .id _ _ := by
  rcases hf with ⟨e, rfl⟩
  simp

@[simp]
/-
**ContinuousLinearMap.IsInvertible.inverse_apply_self** 是 Mathlib 中的一个定理，位于命名空间 
`ContinuousLinearMap.IsInvertible`。
形式化陈述：inverse_apply_self (hf : f.IsInvertible) (y : M) : f.inverse (f y) = y
参数：hf : f.IsInvertible；y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.inverse_equiv`：inverse_equiv (e : M ≃L[R] M₂) : inve
rse (e : M ->L[R] M₂) = e.symm
· 使用定理 `ContinuousLinearEquiv.symm_apply_apply`：symm_apply_apply (e : M₁ ≃SL[σ₁₂
] M₂) (b : M₁) : e.symm (e b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inverse_apply_self (hf : f.IsInvertible) (y : M) : f.inverse (f y) = y := by
  rcases hf with ⟨e, rfl⟩
  simp
/-
**ContinuousLinearMap.IsInvertible.bijective** 是 Mathlib 中的一个定理，位于命名空间 `Continuo
usLinearMap.IsInvertible`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} {M₂ : Type u_3} [inst : TopologicalSpace M
] [inst_1 : TopologicalSpace M₂]   [inst_2 : Semiring R] [inst_3 : AddCommMonoid
 M] [inst_4 : _root_.Module R M] [inst_5 : AddCommMonoid M₂]   [inst_6 : _root_.
Module R M₂] {f : M →L[R] M₂}, f.IsInvertible → Function.Bijective ⇑f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
protected theorem bijective (hf : f.IsInvertible) : Function.Bijective f := by
  rcases hf with ⟨e, rfl⟩
  simp [ContinuousLinearEquiv.bijective]
/-
**ContinuousLinearMap.IsInvertible.injective** 是 Mathlib 中的一个定理，位于命名空间 `Continuo
usLinearMap.IsInvertible`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} {M₂ : Type u_3} [inst : TopologicalSpace M
] [inst_1 : TopologicalSpace M₂]   [inst_2 : Semiring R] [inst_3 : AddCommMonoid
 M] [inst_4 : _root_.Module R M] [inst_5 : AddCommMonoid M₂]   [inst_6 : _root_.
Module R M₂] {f : M →L[R] M₂}, f.IsInvertible → Function.Injective ⇑f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用定理 `ContinuousLinearMap.IsInvertible.bijective`：∀ {R : Type u_1} {M : Type u
_2} {M₂ : Type u_3} [inst : TopologicalSpace M] [inst_1 : TopologicalSpace M₂]  
 [inst_2 : Semiring R] [inst_3 :…
-/
protected theorem injective (hf : f.IsInvertible) : Function.Injective f :=
  hf.bijective.injective
/-
**ContinuousLinearMap.IsInvertible.surjective** 是 Mathlib 中的一个定理，位于命名空间 `Continu
ousLinearMap.IsInvertible`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} {M₂ : Type u_3} [inst : TopologicalSpace M
] [inst_1 : TopologicalSpace M₂]   [inst_2 : Semiring R] [inst_3 : AddCommMonoid
 M] [inst_4 : _root_.Module R M] [inst_5 : AddCommMonoid M₂]   [inst_6 : _root_.
Module R M₂] {f : M →L[R] M₂}, f.IsInvertible → Function.Surjective ⇑f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
· 使用定理 `ContinuousLinearMap.IsInvertible.bijective`：∀ {R : Type u_1} {M : Type u
_2} {M₂ : Type u_3} [inst : TopologicalSpace M] [inst_1 : TopologicalSpace M₂]  
 [inst_2 : Semiring R] [inst_3 :…
-/
protected theorem surjective (hf : f.IsInvertible) : Function.Surjective f :=
  hf.bijective.surjective
/-
**ContinuousLinearMap.IsInvertible.inverse** 是 Mathlib 中的一个定理，位于命名空间 `Continuous
LinearMap.IsInvertible`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} {M₂ : Type u_3} [inst : TopologicalSpace M
] [inst_1 : TopologicalSpace M₂]   [inst_2 : Semiring R] [inst_3 : AddCommMonoid
 M] [inst_4 : _root_.Module R M] [inst_5 : AddCommMonoid M₂]   [inst_6 : _root_.
Module R M₂] {f : M →L[R] M₂}, f.IsInvertible → f.inverse.IsInvertible
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.inverse_equiv`：inverse_equiv (e : M ≃L[R] M₂) : inve
rse (e : M ->L[R] M₂) = e.symm
-/
protected theorem inverse (hf : f.IsInvertible) : f.inverse.IsInvertible := by
  rcases hf with ⟨e, rfl⟩
  simp

@[simp]
/-
**ContinuousLinearMap.IsInvertible.inverse_inverse** 是 Mathlib 中的一个定理，位于命名空间 `Co
ntinuousLinearMap.IsInvertible`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} {M₂ : Type u_3} [inst : TopologicalSpace M
] [inst_1 : TopologicalSpace M₂]   [inst_2 : Semiring R] [inst_3 : AddCommMonoid
 M] [inst_4 : _root_.Module R M] [inst_5 : AddCommMonoid M₂]   [inst_6 : _root_.
Module R M₂] {f : M →L[R] M₂}, f.IsInvertible → f.inverse.inverse = f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.inverse_equiv`：inverse_equiv (e : M ≃L[R] M₂) : inve
rse (e : M ->L[R] M₂) = e.symm
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem inverse_inverse (hf : f.IsInvertible) : f.inverse.inverse = f := by
  rcases hf with ⟨e, rfl⟩
  simp
/-
**ContinuousLinearMap.IsInvertible.of_isInvertible_inverse** 是 Mathlib 中的一个定理，位于
命名空间 `ContinuousLinearMap.IsInvertible`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} {M₂ : Type u_3} [inst : TopologicalSpace M
] [inst_1 : TopologicalSpace M₂]   [inst_2 : Semiring R] [inst_3 : AddCommMonoid
 M] [inst_4 : _root_.Module R M] [inst_5 : AddCommMonoid M₂]   [inst_6 : _root_.
Module R M₂] {f : M →L[R] M₂}, f.inverse.IsInvertible → f.IsInvertible
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `not_true_eq_false`：(¬True) = False
-/
protected theorem of_isInvertible_inverse (hf : f.inverse.IsInvertible) : f.IsInvertible := by
  by_contra H
  obtain ⟨_, _⟩ : Subsingleton M₂ ∧ Subsingleton M := by simpa [inverse, H] using hf
  simp_all [Subsingleton.elim f 0]

@[simp]
/-
**ContinuousLinearMap.IsInvertible._root_.ContinuousLinearMap.isInvertible_inver
se_iff** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap.IsInvertible`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.ContinuousLinearMap.isInvertible_inverse_iff :
    f.inverse.IsInvertible ↔ f.IsInvertible :=
  ⟨.of_isInvertible_inverse, .inverse⟩

end IsInvertible

/-- Composition of a map on a product with the exchange of the product factors -/
/-
**ContinuousLinearMap.coprod_comp_prodComm** 是 Mathlib 中的一个定理，位于命名空间 `Continuous
LinearMap`。
形式化陈述：coprod_comp_prodComm [ContinuousAdd M] (f : M₂ ->L[R] M) (g : M₃ ->L[R] M)
 : f.coprod g ∘L ContinuousLinearEquiv.prodComm R M₃ M₂ = g.coprod f
参数：f : M₂ ->L[R] M；g : M₃ ->L[R] M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.prod_ext`：prod_ext {f g : M × M₂ ->L[R] M₃} (hl : f.
comp (inl _ _ _) = g.comp (inl _ _ _)) (hr : f.comp (inr _ _ _) = g.comp (inr _ 
_ _)) : f = g
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearEquiv.prodComm_apply`：∀ (R₁ : Type u_1) [inst : Semiring
 R₁] (M₁ : Type u_4) [inst_1 : TopologicalSpace M₁] [inst_2 : AddCommMonoid M₁] 
  (M₂ : Type u_5) [inst_3 …
· 使用定理 `ContinuousLinearMap.coprod_apply`：∀ {R : Type u_1} {M : Type u_3} {M₁ : 
Type u_5} {M₂ : Type u_6} [inst : Semiring R] [inst_1 : TopologicalSpace M]   [i
nst_2 : TopologicalSpa…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
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
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `ContinuousLinearMap.coprod_comp_inl`：∀ {R : Type u_1} {M : Type u_3} {M₁
 : Type u_5} {M₂ : Type u_6} [inst : Semiring R] [inst_1 : TopologicalSpace M]  
 [inst_2 : TopologicalSpa…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `ContinuousLinearMap.coprod_comp_inr`：∀ {R : Type u_1} {M : Type u_3} {M₁
 : Type u_5} {M₂ : Type u_6} [inst : Semiring R] [inst_1 : TopologicalSpace M]  
 [inst_2 : TopologicalSpa…

--- 原说明 ---
Composition of a map on a product with the exchange of the product factors
-/
theorem coprod_comp_prodComm [ContinuousAdd M] (f : M₂ →L[R] M) (g : M₃ →L[R] M) :
    f.coprod g ∘L ContinuousLinearEquiv.prodComm R M₃ M₂ = g.coprod f := by
  ext <;> simp

end ContinuousLinearMap

-- Restricting a continuous linear equivalence to a map between submodules.
section map

namespace ContinuousLinearEquiv

variable {R R₂ M M₂ : Type*} [Semiring R] [Semiring R₂] [AddCommMonoid M] [TopologicalSpace M]
  [AddCommMonoid M₂] [TopologicalSpace M₂]
  {module_M : Module R M} {module_M₂ : Module R₂ M₂} {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R}
  {re₁₂ : RingHomInvPair σ₁₂ σ₂₁} {re₂₁ : RingHomInvPair σ₂₁ σ₁₂}

/-- Continuous linear equivalence between two equal submodules:
this is `LinearEquiv.ofEq` as a continuous linear equivalence -/
/-
**ContinuousLinearEquiv.ofEq** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearEquiv`。
形式化陈述：ofEq (p q : Submodule R M) (h : p = q) : p ≃L[R] q where toLinearEquiv
参数：p q : Submodule R M；h : p = q。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Continuous linear equivalence between two equal submodules:
this is `LinearEquiv.ofEq` as a continuous linear equivalence
-/
def ofEq (p q : Submodule R M) (h : p = q) : p ≃L[R] q where
  toLinearEquiv := LinearEquiv.ofEq _ _ h
  continuous_toFun := by
    have h' : (fun x ↦ x ∈ p) = (fun x ↦ x ∈ q) := by simp [h]
    exact (Homeomorph.ofEqSubtypes h').continuous
  continuous_invFun := by
    have h' : (fun x ↦ x ∈ p) = (fun x ↦ x ∈ q) := by simp [h]
    exact (Homeomorph.ofEqSubtypes h').symm.continuous

/--
A continuous linear equivalence of two modules restricts to a continuous linear equivalence
from any submodule `p` of the domain onto the image of that submodule.

This is the continuous linear version of `LinearEquiv.submoduleMap`.
This is `ContinuousLinearEquiv.ofSubmodule'` but with map on the right instead of comap on the left.
-/
/-
**ContinuousLinearEquiv.submoduleMap** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinear
Equiv`。
形式化陈述：submoduleMap (e : M ≃SL[σ₁₂] M₂) (p : Submodule R M) : p ≃SL[σ₁₂] Submodul
e.map (e : M ->ₛₗ[σ₁₂] M₂) p where __
参数：e : M ≃SL[σ₁₂] M₂；p : Submodule R M。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…

--- 原说明 ---
A continuous linear equivalence of two modules restricts to a continuous linear 
equivalence
from any submodule `p` of the domain onto the image of that submodule.

This is the continuous linear version of `LinearEquiv.submoduleMap`.
This is `ContinuousLinearEquiv.ofSubmodule'` but with map on the right instead o
f comap on the left.
-/
def submoduleMap (e : M ≃SL[σ₁₂] M₂) (p : Submodule R M) :
    p ≃SL[σ₁₂] Submodule.map (e : M →ₛₗ[σ₁₂] M₂) p where
  __ := LinearEquiv.submoduleMap e.toLinearEquiv p
  continuous_toFun := map_continuous ((e.toContinuousLinearMap.comp p.subtypeL).codRestrict _ _)
  continuous_invFun := (map_continuous e.symm).restrict fun x hx ↦
    ((LinearEquiv.submoduleMap e.toLinearEquiv p).symm ⟨x, hx⟩).2

@[simp]
/-
**ContinuousLinearEquiv.submoduleMap_apply** 是 Mathlib 中的一个引理，位于命名空间 `Continuous
LinearEquiv`。
形式化陈述：submoduleMap_apply (e : M ≃SL[σ₁₂] M₂) (p : Submodule R M) (x : p) : e.sub
moduleMap p x = e x
参数：e : M ≃SL[σ₁₂] M₂；p : Submodule R M；x : p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
-/
lemma submoduleMap_apply (e : M ≃SL[σ₁₂] M₂) (p : Submodule R M) (x : p) :
    e.submoduleMap p x = e x := by
  rfl

@[simp]
/-
**ContinuousLinearEquiv.submoduleMap_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `Conti
nuousLinearEquiv`。
形式化陈述：submoduleMap_symm_apply (e : M ≃SL[σ₁₂] M₂) (p : Submodule R M) (x : p.map
 (e : M ->ₛₗ[σ₁₂] M₂)) : (e.submoduleMap p).symm x = e.symm x
参数：e : M ≃SL[σ₁₂] M₂；p : Submodule R M；x : p.map (e : M ->ₛₗ[σ₁₂] M₂)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
-/
lemma submoduleMap_symm_apply (e : M ≃SL[σ₁₂] M₂) (p : Submodule R M)
    (x : p.map (e : M →ₛₗ[σ₁₂] M₂)) :
    (e.submoduleMap p).symm x = e.symm x := by
  rfl

/-- A continuous linear equivalence which maps a submodule of one module onto another,
restricts to a continuous linear equivalence of the two submodules.
This is `LinearEquiv.ofSubmodules` as a continuous linear equivalence. -/
/-
**ContinuousLinearEquiv.ofSubmodules** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinear
Equiv`。
形式化陈述：ofSubmodules (e : M ≃SL[σ₁₂] M₂) (p : Submodule R M) (q : Submodule R₂ M₂)
 (h : p.map (e : M ->ₛₗ[σ₁₂] M₂) = q) : p ≃SL[σ₁₂] q
参数：e : M ≃SL[σ₁₂] M₂；p : Submodule R M；q : Submodule R₂ M₂；h : p.map (e : M ->ₛₗ
[σ₁₂] M₂) = q。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…

--- 原说明 ---
A continuous linear equivalence which maps a submodule of one module onto anothe
r,
restricts to a continuous linear equivalence of the two submodules.
This is `LinearEquiv.ofSubmodules` as a continuous linear equivalence.
-/
def ofSubmodules (e : M ≃SL[σ₁₂] M₂)
    (p : Submodule R M) (q : Submodule R₂ M₂) (h : p.map (e : M →ₛₗ[σ₁₂] M₂) = q) : p ≃SL[σ₁₂] q :=
  (e.submoduleMap p).trans (.ofEq _ _ h)

@[simp]
/-
**ContinuousLinearEquiv.ofSubmodules_apply** 是 Mathlib 中的一个定理，位于命名空间 `Continuous
LinearEquiv`。
形式化陈述：ofSubmodules_apply (e : M ≃SL[σ₁₂] M₂) {p : Submodule R M} {q : Submodule 
R₂ M₂} (h : p.map (e : M ->ₛₗ[σ₁₂] M₂) = q) (x : p) : e.ofSubmodules p q h x = e
 x
参数：e : M ≃SL[σ₁₂] M₂；h : p.map (e : M ->ₛₗ[σ₁₂] M₂) = q；x : p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
-/
theorem ofSubmodules_apply (e : M ≃SL[σ₁₂] M₂) {p : Submodule R M} {q : Submodule R₂ M₂}
    (h : p.map (e : M →ₛₗ[σ₁₂] M₂) = q) (x : p) :
    e.ofSubmodules p q h x = e x :=
  rfl

@[simp]
/-
**ContinuousLinearEquiv.ofSubmodules_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Conti
nuousLinearEquiv`。
形式化陈述：ofSubmodules_symm_apply (e : M ≃SL[σ₁₂] M₂) {p : Submodule R M} {q : Submo
dule R₂ M₂} (h : p.map (e : M ->ₛₗ[σ₁₂] M₂) = q) (x : q) : (e.ofSubmodules p q h
).symm x = e.symm x
参数：e : M ≃SL[σ₁₂] M₂；h : p.map (e : M ->ₛₗ[σ₁₂] M₂) = q；x : q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
-/
theorem ofSubmodules_symm_apply (e : M ≃SL[σ₁₂] M₂) {p : Submodule R M} {q : Submodule R₂ M₂}
    (h : p.map (e : M →ₛₗ[σ₁₂] M₂) = q) (x : q) : (e.ofSubmodules p q h).symm x = e.symm x :=
  rfl

/-- A continuous linear equivalence of two modules restricts to a continuous linear equivalence
from the preimage of any submodule to that submodule.
This is `ContinuousLinearEquiv.ofSubmodule` but with `comap` on the left
instead of `map` on the right. -/
/-
**ContinuousLinearEquiv.ofSubmodule'** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinear
Equiv`。
形式化陈述：ofSubmodule' (f : M ≃SL[σ₁₂] M₂) (U : Submodule R₂ M₂) : U.comap (f : M ->
ₛₗ[σ₁₂] M₂) ≃SL[σ₁₂] U
参数：f : M ≃SL[σ₁₂] M₂；U : Submodule R₂ M₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A continuous linear equivalence of two modules restricts to a continuous linear 
equivalence
from the preimage of any submodule to that submodule.
This is `ContinuousLinearEquiv.ofSubmodule` but with `comap` on the left
instead of `map` on the right.
-/
def ofSubmodule' (f : M ≃SL[σ₁₂] M₂) (U : Submodule R₂ M₂) :
    U.comap (f : M →ₛₗ[σ₁₂] M₂) ≃SL[σ₁₂] U :=
  f.symm.ofSubmodules _ _ (U.map_equiv_eq_comap_symm f.toLinearEquiv.symm) |>.symm
/-
**ContinuousLinearEquiv.ofSubmodule'_toContinuousLinearMap** 是 Mathlib 中的一个定理，位于
命名空间 `ContinuousLinearEquiv`。
形式化陈述：∀ {R : Type u_1} {R₂ : Type u_2} {M : Type u_3} {M₂ : Type u_4} [inst : Se
miring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMonoid M] [inst_3 : Topologi
calSpace M] [inst_4 : AddCommMonoid M₂] [inst_5 : TopologicalSpace M₂]   {module
_M : _root_.Module R M} {module_M₂ : _root_.Module R₂ M₂} {σ₁₂ : R →+* R₂} {σ₂₁ 
: R₂ →+* R}   {re₁₂ : RingHomInvPair σ₁₂ σ₂₁} {re₂₁ : RingHomInvPair σ₂₁ σ₁₂} (f
 : M ≃SL[σ₁₂] M₂) (U : Submodule R₂ M₂),   ↑(f.ofSubmodule' U) = (↑f ∘SL (Submod
ule.comap (↑↑f) U).subtypeL).codRestrict U ⋯
参数：f : M ≃SL[σ₁₂] M₂；U : Submodule R₂ M₂；f.ofSubmodule' U；↑f ∘SL (Submodule.coma
p (↑↑f) U).subtypeL。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofSubmodule'_toContinuousLinearMap (f : M ≃SL[σ₁₂] M₂) (U : Submodule R₂ M₂) :
    (f.ofSubmodule' U).toContinuousLinearMap =
      (f.toContinuousLinearMap.comp ((U.comap f.toLinearMap).subtypeL)).codRestrict U
        ((fun ⟨x, hx⟩ ↦ by simpa [Submodule.mem_comap])) := by
  rfl

@[simp]
/-
**ContinuousLinearEquiv.ofSubmodule'_apply** 是 Mathlib 中的一个定理，位于命名空间 `Continuous
LinearEquiv`。
形式化陈述：∀ {R : Type u_1} {R₂ : Type u_2} {M : Type u_3} {M₂ : Type u_4} [inst : Se
miring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMonoid M] [inst_3 : Topologi
calSpace M] [inst_4 : AddCommMonoid M₂] [inst_5 : TopologicalSpace M₂]   {module
_M : _root_.Module R M} {module_M₂ : _root_.Module R₂ M₂} {σ₁₂ : R →+* R₂} {σ₂₁ 
: R₂ →+* R}   {re₁₂ : RingHomInvPair σ₁₂ σ₂₁} {re₂₁ : RingHomInvPair σ₂₁ σ₁₂} (f
 : M ≃SL[σ₁₂] M₂) (U : Submodule R₂ M₂)   (x : ↥(Submodule.comap (↑↑f) U)), ↑((f
.ofSubmodule' U) x) = f ↑x
参数：f : M ≃SL[σ₁₂] M₂；U : Submodule R₂ M₂；x : ↥(Submodule.comap (↑↑f) U)；(f.ofSub
module' U) x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofSubmodule'_apply (f : M ≃SL[σ₁₂] M₂) (U : Submodule R₂ M₂)
    (x : U.comap (f : M →ₛₗ[σ₁₂] M₂)) :
    (f.ofSubmodule' U x : M₂) = f (x : M) :=
  rfl

@[simp]
/-
**ContinuousLinearEquiv.ofSubmodule'_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Conti
nuousLinearEquiv`。
形式化陈述：∀ {R : Type u_1} {R₂ : Type u_2} {M : Type u_3} {M₂ : Type u_4} [inst : Se
miring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMonoid M] [inst_3 : Topologi
calSpace M] [inst_4 : AddCommMonoid M₂] [inst_5 : TopologicalSpace M₂]   {module
_M : _root_.Module R M} {module_M₂ : _root_.Module R₂ M₂} {σ₁₂ : R →+* R₂} {σ₂₁ 
: R₂ →+* R}   {re₁₂ : RingHomInvPair σ₁₂ σ₂₁} {re₂₁ : RingHomInvPair σ₂₁ σ₁₂} (f
 : M ≃SL[σ₁₂] M₂) (U : Submodule R₂ M₂) (x : ↥U),   ↑((f.ofSubmodule' U).symm x)
 = f.symm ↑x
参数：f : M ≃SL[σ₁₂] M₂；U : Submodule R₂ M₂；x : ↥U；(f.ofSubmodule' U).symm x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofSubmodule'_symm_apply (f : M ≃SL[σ₁₂] M₂) (U : Submodule R₂ M₂) (x : U) :
    ((f.ofSubmodule' U).symm x : M) = f.symm (x : M₂) := rfl

end ContinuousLinearEquiv

/-- The top submodule is continuous linearly equivalent to the module.
This is the continuous version of `Submodule.topEquiv`. -/
/-
**_root_.Submodule.topContEquiv** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：_root_.Submodule.topContEquiv {R M : Type*} [Semiring R] [AddCommMonoid M]
 [Module R M] [TopologicalSpace M] : (⊤ : Submodule R M) ≃L[R] M where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The top submodule is continuous linearly equivalent to the module.
This is the continuous version of `Submodule.topEquiv`.
-/
abbrev _root_.Submodule.topContEquiv {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [TopologicalSpace M] : (⊤ : Submodule R M) ≃L[R] M where
  __ := Submodule.topEquiv

end map

namespace MulOpposite

variable (R : Type*) [Semiring R] [τR : TopologicalSpace R] [IsTopologicalSemiring R]
  {M : Type*} [AddCommMonoid M] [Module R M] [TopologicalSpace M] [ContinuousSMul R M]

/-- The function `op` is a continuous linear equivalence. -/
@[simps!]
/-
**MulOpposite.opContinuousLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MulOpposite`。
形式化陈述：opContinuousLinearEquiv : M ≃L[R] Mᵐᵒᵖ where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The function `op` is a continuous linear equivalence.
-/
def opContinuousLinearEquiv : M ≃L[R] Mᵐᵒᵖ where
  __ := MulOpposite.opLinearEquiv R

end MulOpposite

namespace ContinuousLinearEquiv
variable {S R V W G : Type*} [Semiring R] [Semiring S]
  [AddCommMonoid V] [Module R V] [TopologicalSpace V] [Module S V] [ContinuousConstSMul S V]
  [AddCommMonoid W] [Module R W] [TopologicalSpace W] [Module S W] [ContinuousConstSMul S W]
  [AddCommMonoid G] [Module R G] [TopologicalSpace G] [Module S G] [ContinuousConstSMul S G]
  [SMulCommClass R S W] [SMul S R] [IsScalarTower S R V] [IsScalarTower S R W]

/-- Left scalar multiplication of a unit and a continuous linear equivalence,
as a continuous linear equivalence. -/
/-
**ContinuousLinearEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLinearEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Left scalar multiplication of a unit and a continuous linear equivalence,
as a continuous linear equivalence.
-/
instance : SMul Sˣ (V ≃L[R] W) where smul α e :=
  { __ := α • e.toLinearEquiv
    continuous_toFun := α.isUnit.continuous_const_smul_iff.mpr e.continuous
    continuous_invFun := α⁻¹.isUnit.continuous_const_smul_iff.mpr e.symm.continuous }
/-
**ContinuousLinearEquiv.smul_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearEq
uiv`。
形式化陈述：∀ {S : Type u_1} {R : Type u_2} {V : Type u_3} {W : Type u_4} [inst : Semi
ring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid V] [inst_3 : _root_.Modu
le R V] [inst_4 : TopologicalSpace V] [inst_5 : _root_.Module S V]   [inst_6 : C
ontinuousConstSMul S V] [inst_7 : AddCommMonoid W] [inst_8 : _root_.Module R W] 
  [inst_9 : TopologicalSpace W] [inst_10 : _root_.Module S W] [inst_11 : Continu
ousConstSMul S W]   [inst_12 : SMulCommClass R S W] [inst_13 : SMul S R] [inst_1
4 : IsScalarTower S R V] [inst_15 : IsScalarTower S R W]   (α : Sˣ) (e : V ≃L[R]
 W) (x : V), (α • e) x = ↑α • e x
参数：α : Sˣ；e : V ≃L[R] W；x : V；α • e。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem smul_apply (α : Sˣ) (e : V ≃L[R] W) (x : V) : (α • e) x = (α : S) • e x := rfl
/-
**ContinuousLinearEquiv.symm_smul_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLin
earEquiv`。
形式化陈述：symm_smul_apply (e : V ≃L[R] W) (α : Sˣ) (x : W) : (α • e).symm x = (↑α⁻¹ 
: S) • e.symm x
参数：e : V ≃L[R] W；α : Sˣ；x : W。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_smul_apply (e : V ≃L[R] W) (α : Sˣ) (x : W) :
    (α • e).symm x = (↑α⁻¹ : S) • e.symm x := rfl
/-
**ContinuousLinearEquiv.symm_smul** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearEqu
iv`。
形式化陈述：∀ {S : Type u_1} {R : Type u_2} {V : Type u_3} {W : Type u_4} [inst : Semi
ring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid V] [inst_3 : _root_.Modu
le R V] [inst_4 : TopologicalSpace V] [inst_5 : _root_.Module S V]   [inst_6 : C
ontinuousConstSMul S V] [inst_7 : AddCommMonoid W] [inst_8 : _root_.Module R W] 
  [inst_9 : TopologicalSpace W] [inst_10 : _root_.Module S W] [inst_11 : Continu
ousConstSMul S W]   [inst_12 : SMulCommClass R S W] [inst_13 : SMul S R] [inst_1
4 : IsScalarTower S R V] [inst_15 : IsScalarTower S R W]   [inst_16 : SMulCommCl
ass R S V] (e : V ≃L[R] W) (α : Sˣ), (α • e).symm = α⁻¹ • e.symm
参数：e : V ≃L[R] W；α : Sˣ；α • e。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem symm_smul [SMulCommClass R S V]
    (e : V ≃L[R] W) (α : Sˣ) : (α • e).symm = α⁻¹ • e.symm := rfl
/-
**ContinuousLinearEquiv.toLinearEquiv_smul** 是 Mathlib 中的一个定理，位于命名空间 `Continuous
LinearEquiv`。
形式化陈述：∀ {S : Type u_1} {R : Type u_2} {V : Type u_3} {W : Type u_4} [inst : Semi
ring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid V] [inst_3 : _root_.Modu
le R V] [inst_4 : TopologicalSpace V] [inst_5 : _root_.Module S V]   [inst_6 : C
ontinuousConstSMul S V] [inst_7 : AddCommMonoid W] [inst_8 : _root_.Module R W] 
  [inst_9 : TopologicalSpace W] [inst_10 : _root_.Module S W] [inst_11 : Continu
ousConstSMul S W]   [inst_12 : SMulCommClass R S W] [inst_13 : SMul S R] [inst_1
4 : IsScalarTower S R V] [inst_15 : IsScalarTower S R W]   (e : V ≃L[R] W) (α : 
Sˣ), ↑(α • e) = α • ↑e
参数：e : V ≃L[R] W；α : Sˣ；α • e。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem toLinearEquiv_smul (e : V ≃L[R] W) (α : Sˣ) :
    (α • e).toLinearEquiv = α • e.toLinearEquiv := rfl
/-
**ContinuousLinearEquiv.smul_trans** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearEq
uiv`。
形式化陈述：smul_trans [SMulCommClass R S V] [IsScalarTower S R G] (α : Sˣ) (e : G ≃L[
R] V) (f : V ≃L[R] W) : (α • e).trans f = α • (e.trans f)
参数：α : Sˣ；e : G ≃L[R] V；f : V ≃L[R] W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearEquiv.ext`：ext {f g : M₁ ≃SL[σ₁₂] M₂} (h : (f : M₁ -> M₂
) = g) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMapClass.map_smul_of_tower`：∀ {M : Type u_8} {M₂ : Type u_10} [ins
t : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type u_15}
   [inst_2 : Semiring …
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `ContinuousSemilinearEquivClass.continuousSemilinearMapClass`：∀ (F : Type
 u_1) {R : Type u_2} {S : Type u_3} [inst : Semiring R] [inst_1 : Semiring S] (σ
 : R →+* S) {σ' : S →+* R}   [inst_2 : RingHomInv…
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smul_trans [SMulCommClass R S V] [IsScalarTower S R G] (α : Sˣ) (e : G ≃L[R] V)
    (f : V ≃L[R] W) : (α • e).trans f = α • (e.trans f) := by
  ext; simp [LinearMapClass.map_smul_of_tower f]
/-
**ContinuousLinearEquiv.trans_smul** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearEq
uiv`。
形式化陈述：trans_smul [IsScalarTower S R G] (α : Sˣ) (e : G ≃L[R] V) (f : V ≃L[R] W) 
: e.trans (α • f) = α • (e.trans f)
参数：α : Sˣ；e : G ≃L[R] V；f : V ≃L[R] W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearEquiv.ext`：ext {f g : M₁ ≃SL[σ₁₂] M₂} (h : (f : M₁ -> M₂
) = g) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem trans_smul [IsScalarTower S R G] (α : Sˣ) (e : G ≃L[R] V) (f : V ≃L[R] W) :
    e.trans (α • f) = α • (e.trans f) := by ext; simp

section IsHomeomorph

variable {S₁ M M₁ : Type*} [Semiring S₁] {σ : S →+* S₁} {σ' : S₁ →+* S}
  [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] [TopologicalSpace M] [AddCommMonoid M] [Module S M]
  [TopologicalSpace M₁] [AddCommMonoid M₁] [Module S₁ M₁]

/-- A linear equivalence that is a homeomorphism is a continuous linear equivalence. -/
/-
**ContinuousLinearEquiv.ofIsHomeomorph** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLine
arEquiv`。
形式化陈述：ofIsHomeomorph (f : M ≃ₛₗ[σ] M₁) (hf : IsHomeomorph f) : M ≃SL[σ] M₁ where
 __
参数：f : M ≃ₛₗ[σ] M₁；hf : IsHomeomorph f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A linear equivalence that is a homeomorphism is a continuous linear equivalence.
-/
def ofIsHomeomorph (f : M ≃ₛₗ[σ] M₁) (hf : IsHomeomorph f) : M ≃SL[σ] M₁ where
  __ := f
  continuous_toFun := hf.continuous
  continuous_invFun := (f.isHomeomorph_iff.mp hf).2
/-
**ContinuousLinearEquiv.isHomeomorph** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinear
Equiv`。
形式化陈述：isHomeomorph (f : M ≃SL[σ] M₁) : IsHomeomorph f
参数：f : M ≃SL[σ] M₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearEquiv.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [ins
t : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁}   [i
nst_2 : RingHomInvPair…
· 使用定理 `ContinuousLinearEquiv.isOpenMap`：isOpenMap (e : M₁ ≃SL[σ₁₂] M₂) : IsOpen
Map e
· 使用定理 `ContinuousLinearEquiv.bijective`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst
 : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁}   [in
st_2 : RingHomInvPair…
-/
theorem isHomeomorph (f : M ≃SL[σ] M₁) : IsHomeomorph f := ⟨f.continuous, isOpenMap f, f.bijective⟩

variable {f : M ≃ₛₗ[σ] M₁} (hf : IsHomeomorph f)

@[simp]
/-
**ContinuousLinearEquiv.toLinearquiv_ofIsHomeomorph** 是 Mathlib 中的一个引理，位于命名空间 `C
ontinuousLinearEquiv`。
形式化陈述：toLinearquiv_ofIsHomeomorph : (ofIsHomeomorph f hf).toLinearEquiv = f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toLinearquiv_ofIsHomeomorph : (ofIsHomeomorph f hf).toLinearEquiv = f := by
  dsimp only [ofIsHomeomorph]

@[simp]
/-
**ContinuousLinearEquiv.coe_ofIsHomeomorph** 是 Mathlib 中的一个引理，位于命名空间 `Continuous
LinearEquiv`。
形式化陈述：coe_ofIsHomeomorph : (ofIsHomeomorph f hf : M -> M₁) = f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_ofIsHomeomorph : (ofIsHomeomorph f hf : M → M₁) = f := by dsimp [ofIsHomeomorph]

/-- A linear equivalence between topological modules is a homeomorphism if and only if it is
continuous in both directions. -/
/-
**ContinuousLinearEquiv._root_.LinearEquiv.isHomeomorph_iff** 是 Mathlib 中的一个定理，位
于命名空间 `ContinuousLinearEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A linear equivalence between topological modules is a homeomorphism if and only 
if it is
continuous in both directions.
-/
theorem _root_.LinearEquiv.isHomeomorph_iff (e : M ≃ₛₗ[σ] M₁) :
    IsHomeomorph e ↔ Continuous e ∧ Continuous e.symm := e.toEquiv.isHomeomorph_iff

end IsHomeomorph

end ContinuousLinearEquiv

