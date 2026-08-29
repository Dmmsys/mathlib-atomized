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

/--
Definition of `ContinuousLinearEquiv` / `ContinuousLinearEquiv` 的定义

English:
structure ContinuousLinearEquiv
  parameters: {R : Type*} {S : Type*} [Semiring R] [Semiring S] (σ : R ->+* S)
  extends: M ≃ₛₗ[σ] M₂
  axioms and operations (2):
    - continuous_toFun : Continuous toFun  [default: by first | fun_prop | eta_expand; dsimp; fun_prop | skip]
    - continuous_invFun : Continuous invFun  [default: by first | fun_prop | eta_expand; dsimp; fun_prop | skip]

中文:
结构 连续线性等价
  参数: {R : 类型} {S : 类型} [半环 R] [半环 S] (σ : R ->+* S)
  继承: M ≃ₛₗ[σ] M₂
  公理与运算 (2 个):
    - continuous_toFun : 连续 toFun  [默认: by first | fun_prop | eta_expand; dsimp; fun_prop | skip]
    - continuous_invFun : 连续 invFun  [默认: by first | fun_prop | eta_expand; dsimp; fun_prop | skip]

Depends on / 依赖: Continuous, continuous_invFun, eta_expand, fun_prop, invFun
-/
structure ContinuousLinearEquiv {R : Type*} {S : Type*} [Semiring R] [Semiring S] (σ : R ->+* S)
    {σ' : S ->+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (M : Type*) [TopologicalSpace M]
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

/--
Definition of `ContinuousSemilinearEquivClass` / `ContinuousSemilinearEquivClass` 的定义

English:
class ContinuousSemilinearEquivClass
  parameters: (F : Type*) {R : outParam Type*} {S : outParam Type*}
  extends: SemilinearEquivClass F σ M M₂
  axioms and operations (2):
    - map_continuous : forall f : F, Continuous f  [default: by first | fun_prop | dsimp; fun_prop]
    - inv_continuous : forall f : F, Continuous (EquivLike.inv f)  [default: by first | fun_prop | dsimp; fun_prop]

中文:
类 余ntinuousSemilinear等价类
  参数: (F : 类型) {R : outParam 类型} {S : outParam 类型}
  继承: 半线性等价类 F σ M M₂
  公理与运算 (2 个):
    - map_continuous : 对任意 f : F, 连续 f  [默认: by first | fun_prop | dsimp; fun_prop]
    - inv_continuous : 对任意 f : F, 连续 (等价状.inv f)  [默认: by first | fun_prop | dsimp; fun_prop]

Depends on / 依赖: Continuous, EquivLike, EquivLike.inv, fun_prop, inv_continuous
-/
class ContinuousSemilinearEquivClass (F : Type*) {R : outParam Type*} {S : outParam Type*}
    [Semiring R] [Semiring S] (σ : outParam <| R ->+* S) {σ' : outParam <| S ->+* R}
    [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (M : outParam Type*) [TopologicalSpace M]
    [AddCommMonoid M] (M₂ : outParam Type*) [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M]
    [Module S M₂] [EquivLike F M M₂] : Prop extends SemilinearEquivClass F σ M M₂ where
  map_continuous : forall f : F, Continuous f := by first | fun_prop | dsimp; fun_prop
  inv_continuous : forall f : F, Continuous (EquivLike.inv f) := by first | fun_prop | dsimp; fun_prop

attribute [inherit_doc ContinuousSemilinearEquivClass]
ContinuousSemilinearEquivClass.map_continuous
ContinuousSemilinearEquivClass.inv_continuous

/--
Definition of `ContinuousLinearEquivClass` / `ContinuousLinearEquivClass` 的定义

English:
abbreviation ContinuousLinearEquivClass
  signature: (F : Type*) (R : outParam Type*) [Semiring R]
  body: ContinuousSemilinearEquivClass F (RingHom.id R) M M₂

中文:
缩写 ContinuousLinearEquivClass
  签名: (F : 类型) (R : outParam 类型) [半环 R]
  定义体: ContinuousSemilinearEquivClass F (RingHom.id R) M M₂

Depends on / 依赖: ContinuousSemilinearEquivClass, RingHom, RingHom.id
-/
abbrev ContinuousLinearEquivClass (F : Type*) (R : outParam Type*) [Semiring R]
    (M : outParam Type*) [TopologicalSpace M] [AddCommMonoid M] (M₂ : outParam Type*)
    [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M] [Module R M₂] [EquivLike F M M₂] :=
  ContinuousSemilinearEquivClass F (RingHom.id R) M M₂

namespace ContinuousSemilinearEquivClass

variable (F : Type*) {R : Type*} {S : Type*} [Semiring R] [Semiring S] (σ : R ->+* S)
  {σ' : S ->+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
  (M : Type*) [TopologicalSpace M] [AddCommMonoid M]
  (M₂ : Type*) [TopologicalSpace M₂] [AddCommMonoid M₂]
  [Module R M] [Module S M₂]

-- `σ'` becomes a metavariable, but it's OK since it's an outparam
instance (priority := 100) continuousSemilinearMapClass [EquivLike F M M₂]
    [s : ContinuousSemilinearEquivClass F σ M M₂] : ContinuousSemilinearMapClass F σ M M₂ :=
  { s with }

instance (priority := 100) [EquivLike F M M₂]
    [s : ContinuousSemilinearEquivClass F σ M M₂] : HomeomorphClass F M M₂ :=
  { s with }

end ContinuousSemilinearEquivClass

namespace ContinuousLinearMap

section Pi

variable {R : Type*} [Semiring R] {M : Type*} [TopologicalSpace M] [AddCommMonoid M] [Module R M]
  {M₂ : Type*} [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M₂] {ι : Type*} {φ : ι -> Type*}
  [forall i, TopologicalSpace (φ i)] [forall i, AddCommMonoid (φ i)] [forall i, Module R (φ i)]

variable (R φ)

/--
Definition of `iInfKerProjEquiv` / `iInfKerProjEquiv` 的定义

English:
definition iInfKerProjEquiv
  signature: {I J : Set ι} [DecidablePred fun i => i in I] (hd : Disjoint I J)
  body: LinearMap.iInfKerProjEquiv R φ hd hu
  continuous_toFun :=
    continuous_pi fun i =>
Continuous.comp (continuous_apply (A := φ) i) continuous_subtype_val
  continuous_invFun :=
    Continuous.subtype_mk
      (continuous_pi fun i => by
        dsimp
        split_ifs <;> [apply continuous_apply; exact continuous_zero])
      _

中文:
定义 iInfKerProjEquiv
  签名: {I J : 集合 ι} [DecidablePred fun i => i in I] (hd : Disjoint I J)
  定义体: LinearMap.iInfKerProjEquiv R φ hd hu
  continuous_toFun :=
    continuous_pi fun i =>
Continuous.comp (continuous_apply (A := φ) i) continuous_subtype_val
  continuous_invFun :=
    Continuous.subtype_mk
      (continuous_pi fun i => by
        dsimp
        split_ifs <;> [apply continuous_apply; exact continuous_zero])
      _

Depends on / 依赖: LinearMap, LinearMap.iInfKerProjEquiv, iInfKerProjEquiv
-/
def iInfKerProjEquiv {I J : Set ι} [DecidablePred fun i => i in I] (hd : Disjoint I J)
    (hu : Set.univ subseteq I union J) :
    (⨅ i in J, (proj i : (forall i, φ i) ->L[R] φ i).ker : Submodule R (forall i, φ i)) ≃L[R] forall i : I, φ i where
  toLinearEquiv := LinearMap.iInfKerProjEquiv R φ hd hu
  continuous_toFun :=
    continuous_pi fun i =>
Continuous.comp (continuous_apply (A := φ) i) continuous_subtype_val
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
  {σ₁₂ : R₁ ->+* R₂} {σ₂₁ : R₂ ->+* R₁} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
  {σ₂₃ : R₂ ->+* R₃} {σ₃₂ : R₃ ->+* R₂} [RingHomInvPair σ₂₃ σ₃₂] [RingHomInvPair σ₃₂ σ₂₃]
  {σ₁₃ : R₁ ->+* R₃} {σ₃₁ : R₃ ->+* R₁} [RingHomInvPair σ₁₃ σ₃₁] [RingHomInvPair σ₃₁ σ₁₃]
  [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomCompTriple σ₃₂ σ₂₁ σ₃₁] {M₁ : Type*}
  [TopologicalSpace M₁] [AddCommMonoid M₁]
  {M₂ : Type*} [TopologicalSpace M₂] [AddCommMonoid M₂] {M₃ : Type*} [TopologicalSpace M₃]
  [AddCommMonoid M₃] {M₄ : Type*} [TopologicalSpace M₄] [AddCommMonoid M₄] [Module R₁ M₁]
  [Module R₂ M₂] [Module R₃ M₃]

/-- A continuous linear equivalence induces a continuous linear map. -/
@[coe]
/--
Definition of `toContinuousLinearMap` / `toContinuousLinearMap` 的定义

English:
definition toContinuousLinearMap
  signature: (e : M₁ ≃SL[σ₁₂] M₂)
  body: { e.toLinearEquiv.toLinearMap with cont := e.continuous_toFun }

中文:
定义 toContinuousLinearMap
  签名: (e : M₁ ≃SL[σ₁₂] M₂)
  定义体: { e.toLinearEquiv.toLinearMap with cont := e.continuous_toFun }

Depends on / 依赖: continuous_toFun, e.continuous_toFun, e.toLinearEquiv.toLinearMap, toLinearEquiv, toLinearMap
-/
def toContinuousLinearMap (e : M₁ ≃SL[σ₁₂] M₂) : M₁ ->SL[σ₁₂] M₂ :=
  { e.toLinearEquiv.toLinearMap with cont := e.continuous_toFun }

attribute [coe] toLinearEquiv

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe (M₁ ≃SL[σ₁₂] M₂) (M₁ ->SL[σ₁₂] M₂)
  body: toContinuousLinearMap

中文:
实例 :
  签名: Coe (M₁ ≃SL[σ₁₂] M₂) (M₁ ->SL[σ₁₂] M₂)
  定义体: toContinuousLinearMap

Depends on / 依赖: toContinuousLinearMap
-/
instance : Coe (M₁ ≃SL[σ₁₂] M₂) (M₁ ->SL[σ₁₂] M₂) where coe := toContinuousLinearMap
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe (M₁ ≃SL[σ₁₂] M₂) (M₁ ≃ₛₗ[σ₁₂] M₂)
  body: toLinearEquiv

中文:
实例 :
  签名: Coe (M₁ ≃SL[σ₁₂] M₂) (M₁ ≃ₛₗ[σ₁₂] M₂)
  定义体: toLinearEquiv

Depends on / 依赖: toLinearEquiv
-/
instance : Coe (M₁ ≃SL[σ₁₂] M₂) (M₁ ≃ₛₗ[σ₁₂] M₂) where coe := toLinearEquiv

/--
lemma `toLinearMap_toContinuousLinearMap` / 引理 `toLinearMap_toContinuousLinearMap`

English:
lemma toLinearMap_toContinuousLinearMap
  given: (e : M₁ ≃SL[σ₁₂] M₂)
  proof: rfl

中文:
引理 toLinearMap_toContinuousLinearMap
  条件: (e : M₁ ≃SL[σ₁₂] M₂)
  证明: rfl
-/
@[simp] lemma toLinearMap_toContinuousLinearMap (e : M₁ ≃SL[σ₁₂] M₂) :
    e.toContinuousLinearMap.toLinearMap = e.toLinearEquiv.toLinearMap := rfl

/--
Instance `equivLike` / 实例 `equivLike`

English:
instance equivLike
  signature: :
  body: f.toFun
  inv f := f.invFun
  coe_injective' f g h₁ h₂ := by
    obtain ⟨f', _⟩ := f
    obtain ⟨g', _⟩ := g
    rcases f' with ⟨⟨⟨_, _⟩, _⟩, _⟩
    rcases g' with ⟨⟨⟨_, _⟩, _⟩, _⟩
    congr
  left_inv f := f.left_inv
  right_inv f := f.right_inv

中文:
实例 equivLike
  签名: :
  定义体: f.toFun
  inv f := f.invFun
  coe_injective' f g h₁ h₂ := by
    obtain ⟨f', _⟩ := f
    obtain ⟨g', _⟩ := g
    rcases f' with ⟨⟨⟨_, _⟩, _⟩, _⟩
    rcases g' with ⟨⟨⟨_, _⟩, _⟩, _⟩
    congr
  left_inv f := f.left_inv
  right_inv f := f.right_inv

Depends on / 依赖: f.toFun
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

/--
Instance `continuousSemilinearEquivClass` / 实例 `continuousSemilinearEquivClass`

English:
instance continuousSemilinearEquivClass
  signature: :
  body: f.map_add'
  map_smulₛₗ f := f.map_smul'
  map_continuous := continuous_toFun
  inv_continuous := continuous_invFun

@[simp]

中文:
实例 continuousSemilinearEquivClass
  签名: :
  定义体: f.map_add'
  map_smulₛₗ f := f.map_smul'
  map_continuous := continuous_toFun
  inv_continuous := continuous_invFun

@[simp]

Depends on / 依赖: f.map_add, map_add
-/
instance continuousSemilinearEquivClass :
    ContinuousSemilinearEquivClass (M₁ ≃SL[σ₁₂] M₂) σ₁₂ M₁ M₂ where
  map_add f := f.map_add'
  map_smulₛₗ f := f.map_smul'
  map_continuous := continuous_toFun
  inv_continuous := continuous_invFun

@[simp]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (e : M₁ ≃ₛₗ[σ₁₂] M₂) (a b)
  statement: ⇑(ContinuousLinearEquiv.mk e a b) = e
  proof: rfl

中文:
定理 coe_mk
  条件: (e : M₁ ≃ₛₗ[σ₁₂] M₂) (a b)
  结论: ⇑(连续线性等价.mk e a b) = e
  证明: rfl
-/
theorem coe_mk (e : M₁ ≃ₛₗ[σ₁₂] M₂) (a b) : ⇑(ContinuousLinearEquiv.mk e a b) = e := rfl

/--
theorem `coe_apply` / 定理 `coe_apply`

English:
theorem coe_apply
  given: (e : M₁ ≃SL[σ₁₂] M₂) (b : M₁)
  statement: (e : M₁ ->SL[σ₁₂] M₂) b = e b
  proof: rfl

@[simp]

中文:
定理 coe_apply
  条件: (e : M₁ ≃SL[σ₁₂] M₂) (b : M₁)
  结论: (e : M₁ ->SL[σ₁₂] M₂) b = e b
  证明: rfl

@[simp]
-/
theorem coe_apply (e : M₁ ≃SL[σ₁₂] M₂) (b : M₁) : (e : M₁ ->SL[σ₁₂] M₂) b = e b :=
  rfl

@[simp]
/--
theorem `coe_toLinearEquiv` / 定理 `coe_toLinearEquiv`

English:
theorem coe_toLinearEquiv
  given: (f : M₁ ≃SL[σ₁₂] M₂)
  statement: ⇑f.toLinearEquiv = f
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_toLinearEquiv
  条件: (f : M₁ ≃SL[σ₁₂] M₂)
  结论: ⇑f.toLinearEquiv = f
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_toLinearEquiv (f : M₁ ≃SL[σ₁₂] M₂) : ⇑f.toLinearEquiv = f :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_coe` / 定理 `coe_coe`

English:
theorem coe_coe
  given: (e : M₁ ≃SL[σ₁₂] M₂)
  statement: ⇑(e : M₁ ->SL[σ₁₂] M₂) = e
  proof: rfl

中文:
定理 coe_coe
  条件: (e : M₁ ≃SL[σ₁₂] M₂)
  结论: ⇑(e : M₁ ->SL[σ₁₂] M₂) = e
  证明: rfl
-/
theorem coe_coe (e : M₁ ≃SL[σ₁₂] M₂) : ⇑(e : M₁ ->SL[σ₁₂] M₂) = e :=
  rfl

/--
theorem `toLinearEquiv_injective` / 定理 `toLinearEquiv_injective`

English:
theorem toLinearEquiv_injective
  proof: by
  rintro ⟨e, _, _⟩ ⟨e', _, _⟩ rfl
  rfl

@[ext]

中文:
定理 toLinearEquiv_injective
  证明: by
  rintro ⟨e, _, _⟩ ⟨e', _, _⟩ rfl
  rfl

@[ext]
-/
theorem toLinearEquiv_injective :
    Function.Injective (toLinearEquiv : (M₁ ≃SL[σ₁₂] M₂) -> M₁ ≃ₛₗ[σ₁₂] M₂) := by
  rintro ⟨e, _, _⟩ ⟨e', _, _⟩ rfl
  rfl

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : M₁ ≃SL[σ₁₂] M₂} (h : (f : M₁ -> M₂) = g)
  statement: f = g
  proof: toLinearEquiv_injective LinearEquiv.ext congr_fun h

中文:
定理 ext
  条件: {f g : M₁ ≃SL[σ₁₂] M₂} (h : (f : M₁ -> M₂) = g)
  结论: f = g
  证明: toLinearEquiv_injective LinearEquiv.ext congr_fun h

Depends on / 依赖: LinearEquiv, LinearEquiv.ext, congr_fun, toLinearEquiv_injective
-/
theorem ext {f g : M₁ ≃SL[σ₁₂] M₂} (h : (f : M₁ -> M₂) = g) : f = g :=
toLinearEquiv_injective LinearEquiv.ext congr_fun h

/--
theorem `coe_injective` / 定理 `coe_injective`

English:
theorem coe_injective
  statement: Function.Injective ((↑) : (M₁ ≃SL[σ₁₂] M₂) -> M₁ ->SL[σ₁₂] M₂)
  proof: fun _e _e' h => ext funext ContinuousLinearMap.ext_iff.1 h

@[simp, norm_cast]

中文:
定理 coe_injective
  结论: 函数.单射 ((↑) : (M₁ ≃SL[σ₁₂] M₂) -> M₁ ->SL[σ₁₂] M₂)
  证明: fun _e _e' h => ext funext ContinuousLinearMap.ext_iff.1 h

@[simp, norm_cast]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.ext_iff, ext_iff
-/
theorem coe_injective : Function.Injective ((↑) : (M₁ ≃SL[σ₁₂] M₂) -> M₁ ->SL[σ₁₂] M₂) :=
fun _e _e' h => ext funext ContinuousLinearMap.ext_iff.1 h

@[simp, norm_cast]
/--
theorem `coe_inj` / 定理 `coe_inj`

English:
theorem coe_inj
  given: {e e' : M₁ ≃SL[σ₁₂] M₂}
  statement: (e : M₁ ->SL[σ₁₂] M₂) = e' ↔ e = e'
  proof: coe_injective.eq_iff

中文:
定理 coe_inj
  条件: {e e' : M₁ ≃SL[σ₁₂] M₂}
  结论: (e : M₁ ->SL[σ₁₂] M₂) = e' ↔ e = e'
  证明: coe_injective.eq_iff

Depends on / 依赖: coe_injective, coe_injective.eq_iff, eq_iff
-/
theorem coe_inj {e e' : M₁ ≃SL[σ₁₂] M₂} : (e : M₁ ->SL[σ₁₂] M₂) = e' ↔ e = e' :=
  coe_injective.eq_iff

/--
Definition of `toHomeomorph` / `toHomeomorph` 的定义

English:
definition toHomeomorph
  signature: (e : M₁ ≃SL[σ₁₂] M₂)
  body: { e with toEquiv := e.toLinearEquiv.toEquiv }

@[simp]

中文:
定义 toHomeomorph
  签名: (e : M₁ ≃SL[σ₁₂] M₂)
  定义体: { e with toEquiv := e.toLinearEquiv.toEquiv }

@[simp]

Depends on / 依赖: e.toLinearEquiv.toEquiv, toEquiv, toLinearEquiv
-/
def toHomeomorph (e : M₁ ≃SL[σ₁₂] M₂) : M₁ ≃ₜ M₂ :=
  { e with toEquiv := e.toLinearEquiv.toEquiv }

@[simp]
/--
theorem `coe_toHomeomorph` / 定理 `coe_toHomeomorph`

English:
theorem coe_toHomeomorph
  given: (e : M₁ ≃SL[σ₁₂] M₂)
  statement: ⇑e.toHomeomorph = e
  proof: rfl

中文:
定理 coe_toHomeomorph
  条件: (e : M₁ ≃SL[σ₁₂] M₂)
  结论: ⇑e.toHomeomorph = e
  证明: rfl
-/
theorem coe_toHomeomorph (e : M₁ ≃SL[σ₁₂] M₂) : ⇑e.toHomeomorph = e :=
  rfl

/--
theorem `isOpenMap` / 定理 `isOpenMap`

English:
theorem isOpenMap
  given: (e : M₁ ≃SL[σ₁₂] M₂)
  statement: IsOpenMap e
  proof: (ContinuousLinearEquiv.toHomeomorph e).isOpenMap

中文:
定理 isOpenMap
  条件: (e : M₁ ≃SL[σ₁₂] M₂)
  结论: 是开映射 e
  证明: (ContinuousLinearEquiv.toHomeomorph e).isOpenMap

Depends on / 依赖: ContinuousLinearEquiv, ContinuousLinearEquiv.toHomeomorph, isOpenMap, toHomeomorph
-/
theorem isOpenMap (e : M₁ ≃SL[σ₁₂] M₂) : IsOpenMap e :=
  (ContinuousLinearEquiv.toHomeomorph e).isOpenMap

/--
theorem `image_closure` / 定理 `image_closure`

English:
theorem image_closure
  given: (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₁)
  statement: e '' closure s = closure (e '' s)
  proof: e.toHomeomorph.image_closure s

中文:
定理 image_closure
  条件: (e : M₁ ≃SL[σ₁₂] M₂) (s : 集合 M₁)
  结论: e '' closure s = closure (e '' s)
  证明: e.toHomeomorph.image_closure s

Depends on / 依赖: e.toHomeomorph.image_closure, image_closure, toHomeomorph
-/
theorem image_closure (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₁) : e '' closure s = closure (e '' s) :=
  e.toHomeomorph.image_closure s

/--
theorem `preimage_closure` / 定理 `preimage_closure`

English:
theorem preimage_closure
  given: (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₂)
  statement: e ⁻¹' closure s = closure (e ⁻¹' s)
  proof: e.toHomeomorph.preimage_closure s

@[simp]

中文:
定理 preimage_closure
  条件: (e : M₁ ≃SL[σ₁₂] M₂) (s : 集合 M₂)
  结论: e ⁻¹' closure s = closure (e ⁻¹' s)
  证明: e.toHomeomorph.preimage_closure s

@[simp]

Depends on / 依赖: e.toHomeomorph.preimage_closure, preimage_closure, toHomeomorph
-/
theorem preimage_closure (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₂) : e ⁻¹' closure s = closure (e ⁻¹' s) :=
  e.toHomeomorph.preimage_closure s

@[simp]
/--
theorem `isClosed_image` / 定理 `isClosed_image`

English:
theorem isClosed_image
  given: (e : M₁ ≃SL[σ₁₂] M₂) {s : Set M₁}
  statement: IsClosed (e '' s) ↔ IsClosed s
  proof: e.toHomeomorph.isClosed_image

中文:
定理 isClosed_image
  条件: (e : M₁ ≃SL[σ₁₂] M₂) {s : 集合 M₁}
  结论: 是闭集 (e '' s) ↔ 是闭集 s
  证明: e.toHomeomorph.isClosed_image

Depends on / 依赖: e.toHomeomorph.isClosed_image, isClosed_image, toHomeomorph
-/
theorem isClosed_image (e : M₁ ≃SL[σ₁₂] M₂) {s : Set M₁} : IsClosed (e '' s) ↔ IsClosed s :=
  e.toHomeomorph.isClosed_image

/--
theorem `map_nhds_eq` / 定理 `map_nhds_eq`

English:
theorem map_nhds_eq
  given: (e : M₁ ≃SL[σ₁₂] M₂) (x : M₁)
  statement: map e (𝓝 x) = 𝓝 (e x)
  proof: e.toHomeomorph.map_nhds_eq x

中文:
定理 map_nhds_eq
  条件: (e : M₁ ≃SL[σ₁₂] M₂) (x : M₁)
  结论: map e (𝓝 x) = 𝓝 (e x)
  证明: e.toHomeomorph.map_nhds_eq x

Depends on / 依赖: e.toHomeomorph.map_nhds_eq, map_nhds_eq, toHomeomorph
-/
theorem map_nhds_eq (e : M₁ ≃SL[σ₁₂] M₂) (x : M₁) : map e (𝓝 x) = 𝓝 (e x) :=
  e.toHomeomorph.map_nhds_eq x

/--
theorem `map_zero` / 定理 `map_zero`

English:
theorem map_zero
  given: (e : M₁ ≃SL[σ₁₂] M₂)
  statement: e (0 : M₁) = 0
  proof: (e : M₁ ->SL[σ₁₂] M₂).map_zero

中文:
定理 map_zero
  条件: (e : M₁ ≃SL[σ₁₂] M₂)
  结论: e (0 : M₁) = 0
  证明: (e : M₁ ->SL[σ₁₂] M₂).map_zero

Depends on / 依赖: map_zero
-/
theorem map_zero (e : M₁ ≃SL[σ₁₂] M₂) : e (0 : M₁) = 0 :=
  (e : M₁ ->SL[σ₁₂] M₂).map_zero

/--
theorem `map_add` / 定理 `map_add`

English:
theorem map_add
  given: (e : M₁ ≃SL[σ₁₂] M₂) (x y : M₁)
  statement: e (x + y) = e x + e y
  proof: (e : M₁ ->SL[σ₁₂] M₂).map_add x y

@[simp]

中文:
定理 map_add
  条件: (e : M₁ ≃SL[σ₁₂] M₂) (x y : M₁)
  结论: e (x + y) = e x + e y
  证明: (e : M₁ ->SL[σ₁₂] M₂).map_add x y

@[simp]

Depends on / 依赖: map_add
-/
theorem map_add (e : M₁ ≃SL[σ₁₂] M₂) (x y : M₁) : e (x + y) = e x + e y :=
  (e : M₁ ->SL[σ₁₂] M₂).map_add x y

@[simp]
/--
theorem `map_smulₛₗ` / 定理 `map_smulₛₗ`

English:
theorem map_smulₛₗ
  given: (e : M₁ ≃SL[σ₁₂] M₂) (c : R₁) (x : M₁)
  statement: e (c • x) = σ₁₂ c • e x
  proof: (e : M₁ ->SL[σ₁₂] M₂).map_smulₛₗ c x

中文:
定理 map_smulₛₗ
  条件: (e : M₁ ≃SL[σ₁₂] M₂) (c : R₁) (x : M₁)
  结论: e (c • x) = σ₁₂ c • e x
  证明: (e : M₁ ->SL[σ₁₂] M₂).map_smulₛₗ c x
-/
theorem map_smulₛₗ (e : M₁ ≃SL[σ₁₂] M₂) (c : R₁) (x : M₁) : e (c • x) = σ₁₂ c • e x :=
  (e : M₁ ->SL[σ₁₂] M₂).map_smulₛₗ c x

/--
theorem `map_smul` / 定理 `map_smul`

English:
theorem map_smul
  given: [Module R₁ M₂] (e : M₁ ≃L[R₁] M₂) (c : R₁) (x : M₁)
  statement: e (c • x) = c • e x
  proof: (e : M₁ ->L[R₁] M₂).map_smul c x

中文:
定理 map_smul
  条件: [模 R₁ M₂] (e : M₁ ≃L[R₁] M₂) (c : R₁) (x : M₁)
  结论: e (c • x) = c • e x
  证明: (e : M₁ ->L[R₁] M₂).map_smul c x

Depends on / 依赖: map_smul
-/
theorem map_smul [Module R₁ M₂] (e : M₁ ≃L[R₁] M₂) (c : R₁) (x : M₁) : e (c • x) = c • e x :=
  (e : M₁ ->L[R₁] M₂).map_smul c x

/--
theorem `map_eq_zero_iff` / 定理 `map_eq_zero_iff`

English:
theorem map_eq_zero_iff
  given: (e : M₁ ≃SL[σ₁₂] M₂) {x : M₁}
  statement: e x = 0 ↔ x = 0
  proof: e.toLinearEquiv.map_eq_zero_iff

中文:
定理 map_eq_zero_iff
  条件: (e : M₁ ≃SL[σ₁₂] M₂) {x : M₁}
  结论: e x = 0 ↔ x = 0
  证明: e.toLinearEquiv.map_eq_zero_iff

Depends on / 依赖: e.toLinearEquiv.map_eq_zero_iff, map_eq_zero_iff, toLinearEquiv
-/
theorem map_eq_zero_iff (e : M₁ ≃SL[σ₁₂] M₂) {x : M₁} : e x = 0 ↔ x = 0 :=
  e.toLinearEquiv.map_eq_zero_iff

attribute [continuity]
  ContinuousLinearEquiv.continuous_toFun ContinuousLinearEquiv.continuous_invFun

@[continuity]
/--
theorem `continuous` / 定理 `continuous`

English:
theorem continuous
  given: (e : M₁ ≃SL[σ₁₂] M₂)
  statement: Continuous (e : M₁ -> M₂)
  proof: e.continuous_toFun

中文:
定理 continuous
  条件: (e : M₁ ≃SL[σ₁₂] M₂)
  结论: 连续 (e : M₁ -> M₂)
  证明: e.continuous_toFun
-/
protected theorem continuous (e : M₁ ≃SL[σ₁₂] M₂) : Continuous (e : M₁ -> M₂) :=
  e.continuous_toFun

/--
theorem `continuousOn` / 定理 `continuousOn`

English:
theorem continuousOn
  given: (e : M₁ ≃SL[σ₁₂] M₂) {s : Set M₁}
  statement: ContinuousOn (e : M₁ -> M₂) s
  proof: e.continuous.continuousOn

中文:
定理 continuousOn
  条件: (e : M₁ ≃SL[σ₁₂] M₂) {s : 集合 M₁}
  结论: ContinuousOn (e : M₁ -> M₂) s
  证明: e.continuous.continuousOn
-/
protected theorem continuousOn (e : M₁ ≃SL[σ₁₂] M₂) {s : Set M₁} : ContinuousOn (e : M₁ -> M₂) s :=
  e.continuous.continuousOn

/--
theorem `continuousAt` / 定理 `continuousAt`

English:
theorem continuousAt
  given: (e : M₁ ≃SL[σ₁₂] M₂) {x : M₁}
  statement: ContinuousAt (e : M₁ -> M₂) x
  proof: e.continuous.continuousAt

中文:
定理 continuousAt
  条件: (e : M₁ ≃SL[σ₁₂] M₂) {x : M₁}
  结论: ContinuousAt (e : M₁ -> M₂) x
  证明: e.continuous.continuousAt
-/
protected theorem continuousAt (e : M₁ ≃SL[σ₁₂] M₂) {x : M₁} : ContinuousAt (e : M₁ -> M₂) x :=
  e.continuous.continuousAt

/--
theorem `continuousWithinAt` / 定理 `continuousWithinAt`

English:
theorem continuousWithinAt
  given: (e : M₁ ≃SL[σ₁₂] M₂) {s : Set M₁} {x : M₁}
  proof: e.continuous.continuousWithinAt

中文:
定理 continuousWithinAt
  条件: (e : M₁ ≃SL[σ₁₂] M₂) {s : 集合 M₁} {x : M₁}
  证明: e.continuous.continuousWithinAt
-/
protected theorem continuousWithinAt (e : M₁ ≃SL[σ₁₂] M₂) {s : Set M₁} {x : M₁} :
    ContinuousWithinAt (e : M₁ -> M₂) s x :=
  e.continuous.continuousWithinAt

/--
theorem `comp_continuousOn_iff` / 定理 `comp_continuousOn_iff`

English:
theorem comp_continuousOn_iff
  statement: {α : Type*} [TopologicalSpace α] (e : M₁ ≃SL[σ₁₂] M₂) {f : α -> M₁}
  proof: e.toHomeomorph.comp_continuousOn_iff _ _

中文:
定理 comp_continuousOn_iff
  结论: {α : 类型} [拓扑空间 α] (e : M₁ ≃SL[σ₁₂] M₂) {f : α -> M₁}
  证明: e.toHomeomorph.comp_continuousOn_iff _ _

Depends on / 依赖: comp_continuousOn_iff, e.toHomeomorph.comp_continuousOn_iff, toHomeomorph
-/
theorem comp_continuousOn_iff {α : Type*} [TopologicalSpace α] (e : M₁ ≃SL[σ₁₂] M₂) {f : α -> M₁}
    {s : Set α} : ContinuousOn (e ∘ f) s ↔ ContinuousOn f s :=
  e.toHomeomorph.comp_continuousOn_iff _ _

/--
theorem `comp_continuous_iff` / 定理 `comp_continuous_iff`

English:
theorem comp_continuous_iff
  given: {α : Type*} [TopologicalSpace α] (e : M₁ ≃SL[σ₁₂] M₂) {f : α -> M₁}
  proof: e.toHomeomorph.comp_continuous_iff

中文:
定理 comp_continuous_iff
  条件: {α : 类型} [拓扑空间 α] (e : M₁ ≃SL[σ₁₂] M₂) {f : α -> M₁}
  证明: e.toHomeomorph.comp_continuous_iff

Depends on / 依赖: comp_continuous_iff, e.toHomeomorph.comp_continuous_iff, toHomeomorph
-/
theorem comp_continuous_iff {α : Type*} [TopologicalSpace α] (e : M₁ ≃SL[σ₁₂] M₂) {f : α -> M₁} :
    Continuous (e ∘ f) ↔ Continuous f :=
  e.toHomeomorph.comp_continuous_iff

/--
theorem `ext₁` / 定理 `ext₁`

English:
theorem ext₁
  given: [TopologicalSpace R₁] {f g : R₁ ≃L[R₁] M₁} (h : f 1 = g 1)
  statement: f = g
  proof: ext funext fun x => mul_one x ▸ by rw [← smul_eq_mul, map_smul, h, map_smul]

中文:
定理 ext₁
  条件: [拓扑空间 R₁] {f g : R₁ ≃L[R₁] M₁} (h : f 1 = g 1)
  结论: f = g
  证明: ext funext fun x => mul_one x ▸ by rw [← smul_eq_mul, map_smul, h, map_smul]

Depends on / 依赖: map_smul, mul_one, smul_eq_mul
-/
theorem ext₁ [TopologicalSpace R₁] {f g : R₁ ≃L[R₁] M₁} (h : f 1 = g 1) : f = g :=
ext funext fun x => mul_one x ▸ by rw [← smul_eq_mul, map_smul, h, map_smul]

section

variable {M : Type*} [TopologicalSpace M] [AddCommMonoid M] [Module R₁ M]

/--
Definition of `toContinuousAddEquiv` / `toContinuousAddEquiv` 的定义

English:
definition toContinuousAddEquiv
  signature: (e : M₁ ≃L[R₁] M)
  body: e.toAddEquiv.toContinuousAddEquiv fun _ => e.toHomeomorph.isOpen_preimage

@[simp]

中文:
定义 toContinuousAddEquiv
  签名: (e : M₁ ≃L[R₁] M)
  定义体: e.toAddEquiv.toContinuousAddEquiv fun _ => e.toHomeomorph.isOpen_preimage

@[simp]

Depends on / 依赖: e.toAddEquiv.toContinuousAddEquiv, e.toHomeomorph.isOpen_preimage, isOpen_preimage, toAddEquiv, toContinuousAddEquiv, toHomeomorph
-/
def toContinuousAddEquiv (e : M₁ ≃L[R₁] M) : M₁ ≃ₜ+ M :=
  e.toAddEquiv.toContinuousAddEquiv fun _ => e.toHomeomorph.isOpen_preimage

@[simp]
/--
lemma `toContinuousAddEquiv_coe` / 引理 `toContinuousAddEquiv_coe`

English:
lemma toContinuousAddEquiv_coe
  given: (e : M₁ ≃L[R₁] M)
  statement: ⇑e.toContinuousAddEquiv = e
  proof: rfl

中文:
引理 toContinuousAddEquiv_coe
  条件: (e : M₁ ≃L[R₁] M)
  结论: ⇑e.toContinuousAddEquiv = e
  证明: rfl
-/
lemma toContinuousAddEquiv_coe (e : M₁ ≃L[R₁] M) : ⇑e.toContinuousAddEquiv = e := rfl

variable (R₁ M₁)

/-- The identity map as a continuous linear equivalence. -/
@[refl]
/--
Definition of `refl` / `refl` 的定义

English:
definition refl
  signature: : M₁ ≃L[R₁] M₁ where
  body: LinearEquiv.refl R₁ M₁

@[simp]

中文:
定义 refl
  签名: : M₁ ≃L[R₁] M₁ where
  定义体: LinearEquiv.refl R₁ M₁

@[simp]
-/
protected def refl : M₁ ≃L[R₁] M₁ where
  __ := LinearEquiv.refl R₁ M₁

@[simp]
/--
theorem `refl_apply` / 定理 `refl_apply`

English:
theorem refl_apply
  given: (x : M₁)
  proof: rfl

中文:
定理 refl_apply
  条件: (x : M₁)
  证明: rfl
-/
theorem refl_apply (x : M₁) :
    ContinuousLinearEquiv.refl R₁ M₁ x = x := rfl

end

@[simp, norm_cast]
/--
theorem `coe_refl` / 定理 `coe_refl`

English:
theorem coe_refl
  statement: ↑(ContinuousLinearEquiv.refl R₁ M₁) = ContinuousLinearMap.id R₁ M₁
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_refl
  结论: ↑(连续线性等价.refl R₁ M₁) = 连续线性映射.id R₁ M₁
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_refl : ↑(ContinuousLinearEquiv.refl R₁ M₁) = ContinuousLinearMap.id R₁ M₁ :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_refl'` / 定理 `coe_refl'`

English:
theorem coe_refl'
  statement: ⇑(ContinuousLinearEquiv.refl R₁ M₁) = id
  proof: rfl

中文:
定理 coe_refl'
  结论: ⇑(连续线性等价.refl R₁ M₁) = id
  证明: rfl
-/
theorem coe_refl' : ⇑(ContinuousLinearEquiv.refl R₁ M₁) = id :=
  rfl

/-- The inverse of a continuous linear equivalence as a continuous linear equivalence -/
@[symm]
/--
Definition of `symm` / `symm` 的定义

English:
definition symm
  signature: (e : M₁ ≃SL[σ₁₂] M₂)
  body: { e.toLinearEquiv.symm with
    continuous_toFun := e.continuous_invFun
    continuous_invFun := e.continuous_toFun }

@[simp]

中文:
定义 symm
  签名: (e : M₁ ≃SL[σ₁₂] M₂)
  定义体: { e.toLinearEquiv.symm with
    continuous_toFun := e.continuous_invFun
    continuous_invFun := e.continuous_toFun }

@[simp]
-/
protected def symm (e : M₁ ≃SL[σ₁₂] M₂) : M₂ ≃SL[σ₂₁] M₁ :=
  { e.toLinearEquiv.symm with
    continuous_toFun := e.continuous_invFun
    continuous_invFun := e.continuous_toFun }

@[simp]
/--
theorem `toLinearEquiv_symm` / 定理 `toLinearEquiv_symm`

English:
theorem toLinearEquiv_symm
  given: (e : M₁ ≃SL[σ₁₂] M₂)
  statement: e.symm.toLinearEquiv = e.toLinearEquiv.symm
  proof: rfl

@[simp]

中文:
定理 toLinearEquiv_symm
  条件: (e : M₁ ≃SL[σ₁₂] M₂)
  结论: e.symm.toLinearEquiv = e.toLinearEquiv.symm
  证明: rfl

@[simp]
-/
theorem toLinearEquiv_symm (e : M₁ ≃SL[σ₁₂] M₂) : e.symm.toLinearEquiv = e.toLinearEquiv.symm :=
  rfl

@[simp]
/--
theorem `coe_symm_toLinearEquiv` / 定理 `coe_symm_toLinearEquiv`

English:
theorem coe_symm_toLinearEquiv
  given: (e : M₁ ≃SL[σ₁₂] M₂)
  statement: ⇑e.toLinearEquiv.symm = e.symm
  proof: rfl

@[simp]

中文:
定理 coe_symm_toLinearEquiv
  条件: (e : M₁ ≃SL[σ₁₂] M₂)
  结论: ⇑e.toLinearEquiv.symm = e.symm
  证明: rfl

@[simp]
-/
theorem coe_symm_toLinearEquiv (e : M₁ ≃SL[σ₁₂] M₂) : ⇑e.toLinearEquiv.symm = e.symm :=
  rfl

@[simp]
/--
theorem `toHomeomorph_symm` / 定理 `toHomeomorph_symm`

English:
theorem toHomeomorph_symm
  given: (e : M₁ ≃SL[σ₁₂] M₂)
  statement: e.symm.toHomeomorph = e.toHomeomorph.symm
  proof: rfl

@[simp]

中文:
定理 toHomeomorph_symm
  条件: (e : M₁ ≃SL[σ₁₂] M₂)
  结论: e.symm.toHomeomorph = e.toHomeomorph.symm
  证明: rfl

@[simp]
-/
theorem toHomeomorph_symm (e : M₁ ≃SL[σ₁₂] M₂) : e.symm.toHomeomorph = e.toHomeomorph.symm :=
  rfl

@[simp]
/--
theorem `coe_symm_toHomeomorph` / 定理 `coe_symm_toHomeomorph`

English:
theorem coe_symm_toHomeomorph
  given: (e : M₁ ≃SL[σ₁₂] M₂)
  statement: ⇑e.toHomeomorph.symm = e.symm
  proof: rfl

中文:
定理 coe_symm_toHomeomorph
  条件: (e : M₁ ≃SL[σ₁₂] M₂)
  结论: ⇑e.toHomeomorph.symm = e.symm
  证明: rfl
-/
theorem coe_symm_toHomeomorph (e : M₁ ≃SL[σ₁₂] M₂) : ⇑e.toHomeomorph.symm = e.symm :=
  rfl

/--
Definition of `Simps.apply` / `Simps.apply` 的定义

English:
definition Simps.apply
  signature: (h : M₁ ≃SL[σ₁₂] M₂)
  body: h

中文:
定义 Simps.apply
  签名: (h : M₁ ≃SL[σ₁₂] M₂)
  定义体: h
-/
def Simps.apply (h : M₁ ≃SL[σ₁₂] M₂) : M₁ -> M₂ :=
  h

/--
Definition of `Simps.symm_apply` / `Simps.symm_apply` 的定义

English:
definition Simps.symm_apply
  signature: (h : M₁ ≃SL[σ₁₂] M₂)
  body: h.symm

initialize_simps_projections ContinuousLinearEquiv (toFun -> apply, invFun -> symm_apply)

中文:
定义 Simps.symm_apply
  签名: (h : M₁ ≃SL[σ₁₂] M₂)
  定义体: h.symm

initialize_simps_projections ContinuousLinearEquiv (toFun -> apply, invFun -> symm_apply)
-/
def Simps.symm_apply (h : M₁ ≃SL[σ₁₂] M₂) : M₂ -> M₁ :=
  h.symm

initialize_simps_projections ContinuousLinearEquiv (toFun -> apply, invFun -> symm_apply)

/--
theorem `symm_map_nhds_eq` / 定理 `symm_map_nhds_eq`

English:
theorem symm_map_nhds_eq
  given: (e : M₁ ≃SL[σ₁₂] M₂) (x : M₁)
  statement: map e.symm (𝓝 (e x)) = 𝓝 x
  proof: e.toHomeomorph.symm_map_nhds_eq x

中文:
定理 symm_map_nhds_eq
  条件: (e : M₁ ≃SL[σ₁₂] M₂) (x : M₁)
  结论: map e.symm (𝓝 (e x)) = 𝓝 x
  证明: e.toHomeomorph.symm_map_nhds_eq x

Depends on / 依赖: e.toHomeomorph.symm_map_nhds_eq, symm_map_nhds_eq, toHomeomorph
-/
theorem symm_map_nhds_eq (e : M₁ ≃SL[σ₁₂] M₂) (x : M₁) : map e.symm (𝓝 (e x)) = 𝓝 x :=
  e.toHomeomorph.symm_map_nhds_eq x

/-- The composition of two continuous linear equivalences as a continuous linear equivalence. -/
@[trans]
/--
Definition of `trans` / `trans` 的定义

English:
definition trans
  signature: (e₁ : M₁ ≃SL[σ₁₂] M₂) (e₂ : M₂ ≃SL[σ₂₃] M₃)
  body: e₁.toLinearEquiv.trans e₂.toLinearEquiv

@[simp]

中文:
定义 trans
  签名: (e₁ : M₁ ≃SL[σ₁₂] M₂) (e₂ : M₂ ≃SL[σ₂₃] M₃)
  定义体: e₁.toLinearEquiv.trans e₂.toLinearEquiv

@[simp]
-/
protected def trans (e₁ : M₁ ≃SL[σ₁₂] M₂) (e₂ : M₂ ≃SL[σ₂₃] M₃) : M₁ ≃SL[σ₁₃] M₃ where
  __ := e₁.toLinearEquiv.trans e₂.toLinearEquiv

@[simp]
/--
theorem `trans_toLinearEquiv` / 定理 `trans_toLinearEquiv`

English:
theorem trans_toLinearEquiv
  given: (e₁ : M₁ ≃SL[σ₁₂] M₂) (e₂ : M₂ ≃SL[σ₂₃] M₃)
  proof: by
  ext
  rfl

中文:
定理 trans_toLinearEquiv
  条件: (e₁ : M₁ ≃SL[σ₁₂] M₂) (e₂ : M₂ ≃SL[σ₂₃] M₃)
  证明: by
  ext
  rfl
-/
theorem trans_toLinearEquiv (e₁ : M₁ ≃SL[σ₁₂] M₂) (e₂ : M₂ ≃SL[σ₂₃] M₃) :
    (e₁.trans e₂).toLinearEquiv = e₁.toLinearEquiv.trans e₂.toLinearEquiv := by
  ext
  rfl

/--
Definition of `prodCongr` / `prodCongr` 的定义

English:
definition prodCongr
  signature: [Module R₁ M₂] [Module R₁ M₃] [Module R₁ M₄] (e : M₁ ≃L[R₁] M₂) (e' : M₃ ≃L[R₁] M₄)
  body: e.toLinearEquiv.prodCongr e'.toLinearEquiv

@[simp, norm_cast]

中文:
定义 prodCongr
  签名: [模 R₁ M₂] [模 R₁ M₃] [模 R₁ M₄] (e : M₁ ≃L[R₁] M₂) (e' : M₃ ≃L[R₁] M₄)
  定义体: e.toLinearEquiv.prodCongr e'.toLinearEquiv

@[simp, norm_cast]

Depends on / 依赖: e.toLinearEquiv.prodCongr, prodCongr, toLinearEquiv
-/
def prodCongr [Module R₁ M₂] [Module R₁ M₃] [Module R₁ M₄] (e : M₁ ≃L[R₁] M₂) (e' : M₃ ≃L[R₁] M₄) :
    (M₁ × M₃) ≃L[R₁] M₂ × M₄ where
  __ := e.toLinearEquiv.prodCongr e'.toLinearEquiv

@[simp, norm_cast]
/--
theorem `prodCongr_apply` / 定理 `prodCongr_apply`

English:
theorem prodCongr_apply
  statement: [Module R₁ M₂] [Module R₁ M₃] [Module R₁ M₄] (e : M₁ ≃L[R₁] M₂)
  proof: rfl

@[simp, norm_cast]

中文:
定理 prodCongr_apply
  结论: [模 R₁ M₂] [模 R₁ M₃] [模 R₁ M₄] (e : M₁ ≃L[R₁] M₂)
  证明: rfl

@[simp, norm_cast]
-/
theorem prodCongr_apply [Module R₁ M₂] [Module R₁ M₃] [Module R₁ M₄] (e : M₁ ≃L[R₁] M₂)
    (e' : M₃ ≃L[R₁] M₄) (x) : e.prodCongr e' x = (e x.1, e' x.2) :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_prodCongr` / 定理 `coe_prodCongr`

English:
theorem coe_prodCongr
  statement: [Module R₁ M₂] [Module R₁ M₃] [Module R₁ M₄] (e : M₁ ≃L[R₁] M₂)
  proof: rfl

@[simp]

中文:
定理 coe_prodCongr
  结论: [模 R₁ M₂] [模 R₁ M₃] [模 R₁ M₄] (e : M₁ ≃L[R₁] M₂)
  证明: rfl

@[simp]
-/
theorem coe_prodCongr [Module R₁ M₂] [Module R₁ M₃] [Module R₁ M₄] (e : M₁ ≃L[R₁] M₂)
    (e' : M₃ ≃L[R₁] M₄) :
    (e.prodCongr e' : M₁ × M₃ ->L[R₁] M₂ × M₄) = (e : M₁ ->L[R₁] M₂).prodMap (e' : M₃ ->L[R₁] M₄) :=
  rfl

@[simp]
/--
theorem `prodCongr_symm` / 定理 `prodCongr_symm`

English:
theorem prodCongr_symm
  statement: [Module R₁ M₂] [Module R₁ M₃] [Module R₁ M₄] (e : M₁ ≃L[R₁] M₂)
  proof: rfl

中文:
定理 prodCongr_symm
  结论: [模 R₁ M₂] [模 R₁ M₃] [模 R₁ M₄] (e : M₁ ≃L[R₁] M₂)
  证明: rfl
-/
theorem prodCongr_symm [Module R₁ M₂] [Module R₁ M₃] [Module R₁ M₄] (e : M₁ ≃L[R₁] M₂)
    (e' : M₃ ≃L[R₁] M₄) : (e.prodCongr e').symm = e.symm.prodCongr e'.symm :=
  rfl

variable (R₁ M₁ M₂)

set_option backward.defeqAttrib.useBackward true in
/-- Product of topological modules is commutative up to continuous linear isomorphism. -/
@[simps! apply toLinearEquiv]
/--
Definition of `prodComm` / `prodComm` 的定义

English:
definition prodComm
  signature: [Module R₁ M₂]
  body: LinearEquiv.prodComm R₁ M₁ M₂

中文:
定义 prodComm
  签名: [模 R₁ M₂]
  定义体: LinearEquiv.prodComm R₁ M₁ M₂

Depends on / 依赖: LinearEquiv, LinearEquiv.prodComm, prodComm
-/
def prodComm [Module R₁ M₂] : (M₁ × M₂) ≃L[R₁] M₂ × M₁ where
  __ := LinearEquiv.prodComm R₁ M₁ M₂

/--
lemma `prodComm_symm` / 引理 `prodComm_symm`

English:
lemma prodComm_symm
  given: [Module R₁ M₂]
  statement: (prodComm R₁ M₁ M₂).symm = prodComm R₁ M₂ M₁
  proof: rfl

中文:
引理 prodComm_symm
  条件: [模 R₁ M₂]
  结论: (prodComm R₁ M₁ M₂).symm = prodComm R₁ M₂ M₁
  证明: rfl
-/
@[simp] lemma prodComm_symm [Module R₁ M₂] : (prodComm R₁ M₁ M₂).symm = prodComm R₁ M₂ M₁ := rfl

section prodAssoc

variable (R M₁ M₂ M₃ : Type*) [Semiring R]
  [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃] [Module R M₁] [Module R M₂] [Module R M₃]
  [TopologicalSpace M₁] [TopologicalSpace M₂] [TopologicalSpace M₃]

/--
Definition of `prodAssoc` / `prodAssoc` 的定义

English:
definition prodAssoc
  signature: : ((M₁ × M₂) × M₃) ≃L[R] M₁ × M₂ × M₃ where
  body: LinearEquiv.prodAssoc R M₁ M₂ M₃
  continuous_toFun := (continuous_fst.comp continuous_fst).prodMk
    ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
  continuous_invFun := (continuous_fst.prodMk (continuous_fst.comp continuous_snd)).prodMk
    (continuous_snd.comp continuous_snd)

@[simp]

中文:
定义 prodAssoc
  签名: : ((M₁ × M₂) × M₃) ≃L[R] M₁ × M₂ × M₃ where
  定义体: LinearEquiv.prodAssoc R M₁ M₂ M₃
  continuous_toFun := (continuous_fst.comp continuous_fst).prodMk
    ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
  continuous_invFun := (continuous_fst.prodMk (continuous_fst.comp continuous_snd)).prodMk
    (continuous_snd.comp continuous_snd)

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.prodAssoc, prodAssoc
-/
def prodAssoc : ((M₁ × M₂) × M₃) ≃L[R] M₁ × M₂ × M₃ where
  toLinearEquiv := LinearEquiv.prodAssoc R M₁ M₂ M₃
  continuous_toFun := (continuous_fst.comp continuous_fst).prodMk
    ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
  continuous_invFun := (continuous_fst.prodMk (continuous_fst.comp continuous_snd)).prodMk
    (continuous_snd.comp continuous_snd)

@[simp]
/--
lemma `prodAssoc_toLinearEquiv` / 引理 `prodAssoc_toLinearEquiv`

English:
lemma prodAssoc_toLinearEquiv
  proof: rfl

@[simp]

中文:
引理 prodAssoc_toLinearEquiv
  证明: rfl

@[simp]
-/
lemma prodAssoc_toLinearEquiv :
    (prodAssoc R M₁ M₂ M₃).toLinearEquiv = LinearEquiv.prodAssoc R M₁ M₂ M₃ := rfl

@[simp]
/--
lemma `coe_prodAssoc` / 引理 `coe_prodAssoc`

English:
lemma coe_prodAssoc
  proof: rfl

@[simp]

中文:
引理 coe_prodAssoc
  证明: rfl

@[simp]
-/
lemma coe_prodAssoc :
    (prodAssoc R M₁ M₂ M₃ : (M₁ × M₂) × M₃ -> M₁ × M₂ × M₃) = Equiv.prodAssoc M₁ M₂ M₃ := rfl

@[simp]
/--
lemma `prodAssoc_apply` / 引理 `prodAssoc_apply`

English:
lemma prodAssoc_apply
  given: (p₁ : M₁) (p₂ : M₂) (p₃ : M₃)
  proof: rfl

@[simp]

中文:
引理 prodAssoc_apply
  条件: (p₁ : M₁) (p₂ : M₂) (p₃ : M₃)
  证明: rfl

@[simp]
-/
lemma prodAssoc_apply (p₁ : M₁) (p₂ : M₂) (p₃ : M₃) :
    prodAssoc R M₁ M₂ M₃ ((p₁, p₂), p₃) = (p₁, (p₂, p₃)) := rfl

@[simp]
/--
lemma `prodAssoc_symm_apply` / 引理 `prodAssoc_symm_apply`

English:
lemma prodAssoc_symm_apply
  given: (p₁ : M₁) (p₂ : M₂) (p₃ : M₃)
  proof: rfl

中文:
引理 prodAssoc_symm_apply
  条件: (p₁ : M₁) (p₂ : M₂) (p₃ : M₃)
  证明: rfl
-/
lemma prodAssoc_symm_apply (p₁ : M₁) (p₂ : M₂) (p₃ : M₃) :
    (prodAssoc R M₁ M₂ M₃).symm (p₁, (p₂, p₃)) = ((p₁, p₂), p₃) := rfl

end prodAssoc

section prodProdProdComm

variable (R M₁ M₂ M₃ M₄ : Type*) [Semiring R]
  [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃] [AddCommMonoid M₄]
  [Module R M₁] [Module R M₂] [Module R M₃] [Module R M₄]
  [TopologicalSpace M₁] [TopologicalSpace M₂] [TopologicalSpace M₃] [TopologicalSpace M₄]

/--
Definition of `prodProdProdComm` / `prodProdProdComm` 的定义

English:
definition prodProdProdComm
  signature: : ((M₁ × M₂) × M₃ × M₄) ≃L[R] (M₁ × M₃) × M₂ × M₄ where
  body: LinearEquiv.prodProdProdComm R M₁ M₂ M₃ M₄

@[simp]

中文:
定义 prodProdProdComm
  签名: : ((M₁ × M₂) × M₃ × M₄) ≃L[R] (M₁ × M₃) × M₂ × M₄ where
  定义体: LinearEquiv.prodProdProdComm R M₁ M₂ M₃ M₄

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.prodProdProdComm, prodProdProdComm
-/
def prodProdProdComm : ((M₁ × M₂) × M₃ × M₄) ≃L[R] (M₁ × M₃) × M₂ × M₄ where
  toLinearEquiv := LinearEquiv.prodProdProdComm R M₁ M₂ M₃ M₄

@[simp]
/--
theorem `prodProdProdComm_symm` / 定理 `prodProdProdComm_symm`

English:
theorem prodProdProdComm_symm
  proof: rfl

@[simp]

中文:
定理 prodProdProdComm_symm
  证明: rfl

@[simp]
-/
theorem prodProdProdComm_symm :
    (prodProdProdComm R M₁ M₂ M₃ M₄).symm = prodProdProdComm R M₁ M₃ M₂ M₄ :=
  rfl

@[simp]
/--
lemma `prodProdProdComm_toLinearEquiv` / 引理 `prodProdProdComm_toLinearEquiv`

English:
lemma prodProdProdComm_toLinearEquiv
  proof: rfl

@[simp]

中文:
引理 prodProdProdComm_toLinearEquiv
  证明: rfl

@[simp]
-/
lemma prodProdProdComm_toLinearEquiv :
    (prodProdProdComm R M₁ M₂ M₃ M₄).toLinearEquiv = LinearEquiv.prodProdProdComm R M₁ M₂ M₃ M₄ :=
  rfl

@[simp]
/--
lemma `coe_prodProdProdComm` / 引理 `coe_prodProdProdComm`

English:
lemma coe_prodProdProdComm
  proof: rfl

@[simp]

中文:
引理 coe_prodProdProdComm
  证明: rfl

@[simp]
-/
lemma coe_prodProdProdComm :
    (prodProdProdComm R M₁ M₂ M₃ M₄ : (M₁ × M₂) × M₃ × M₄ -> (M₁ × M₃) × M₂ × M₄) =
      Equiv.prodProdProdComm M₁ M₂ M₃ M₄ := rfl

@[simp]
/--
lemma `prodProdProdComm_apply` / 引理 `prodProdProdComm_apply`

English:
lemma prodProdProdComm_apply
  given: (p₁ : M₁) (p₂ : M₂) (p₃ : M₃) (p₄ : M₄)
  proof: rfl

中文:
引理 prodProdProdComm_apply
  条件: (p₁ : M₁) (p₂ : M₂) (p₃ : M₃) (p₄ : M₄)
  证明: rfl
-/
lemma prodProdProdComm_apply (p₁ : M₁) (p₂ : M₂) (p₃ : M₃) (p₄ : M₄) :
    prodProdProdComm R M₁ M₂ M₃ M₄ ((p₁, p₂), p₃, p₄) = ((p₁, p₃), p₂, p₄) := rfl

end prodProdProdComm

section prodUnique

variable (R M N : Type*) [Semiring R]
  [TopologicalSpace M] [AddCommMonoid M] [TopologicalSpace N] [AddCommMonoid N]
  [Unique N] [Module R M] [Module R N]

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `prodUnique` / `prodUnique` 的定义

English:
definition prodUnique
  signature: : (M × N) ≃L[R] M where
  body: LinearEquiv.prodUnique

@[simp]

中文:
定义 prodUnique
  签名: : (M × N) ≃L[R] M where
  定义体: LinearEquiv.prodUnique

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.prodUnique, prodUnique
-/
def prodUnique : (M × N) ≃L[R] M where
  toLinearEquiv := LinearEquiv.prodUnique

@[simp]
/--
lemma `coe_prodUnique` / 引理 `coe_prodUnique`

English:
lemma coe_prodUnique
  statement: (prodUnique R M N).toEquiv = Equiv.prodUnique M N
  proof: rfl

@[simp]

中文:
引理 coe_prodUnique
  结论: (prodUnique R M N).toEquiv = 等价.prodUnique M N
  证明: rfl

@[simp]
-/
lemma coe_prodUnique : (prodUnique R M N).toEquiv = Equiv.prodUnique M N := rfl

@[simp]
/--
lemma `prodUnique_apply` / 引理 `prodUnique_apply`

English:
lemma prodUnique_apply
  given: (x : M × N)
  statement: prodUnique R M N x = x.1
  proof: rfl

@[simp]

中文:
引理 prodUnique_apply
  条件: (x : M × N)
  结论: prodUnique R M N x = x.1
  证明: rfl

@[simp]
-/
lemma prodUnique_apply (x : M × N) : prodUnique R M N x = x.1 := rfl

@[simp]
/--
lemma `prodUnique_symm_apply` / 引理 `prodUnique_symm_apply`

English:
lemma prodUnique_symm_apply
  given: (x : M)
  statement: (prodUnique R M N).symm x = (x, default)
  proof: rfl

中文:
引理 prodUnique_symm_apply
  条件: (x : M)
  结论: (prodUnique R M N).symm x = (x, default)
  证明: rfl
-/
lemma prodUnique_symm_apply (x : M) : (prodUnique R M N).symm x = (x, default) := rfl

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `uniqueProd` / `uniqueProd` 的定义

English:
definition uniqueProd
  signature: : (N × M) ≃L[R] M where
  body: LinearEquiv.uniqueProd

@[simp]

中文:
定义 uniqueProd
  签名: : (N × M) ≃L[R] M where
  定义体: LinearEquiv.uniqueProd

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.uniqueProd, uniqueProd
-/
def uniqueProd : (N × M) ≃L[R] M where
  toLinearEquiv := LinearEquiv.uniqueProd

@[simp]
/--
lemma `coe_uniqueProd` / 引理 `coe_uniqueProd`

English:
lemma coe_uniqueProd
  statement: (uniqueProd R M N).toEquiv = Equiv.uniqueProd M N
  proof: rfl

@[simp]

中文:
引理 coe_uniqueProd
  结论: (uniqueProd R M N).toEquiv = 等价.uniqueProd M N
  证明: rfl

@[simp]
-/
lemma coe_uniqueProd : (uniqueProd R M N).toEquiv = Equiv.uniqueProd M N := rfl

@[simp]
/--
lemma `uniqueProd_apply` / 引理 `uniqueProd_apply`

English:
lemma uniqueProd_apply
  given: (x : N × M)
  statement: uniqueProd R M N x = x.2
  proof: rfl

@[simp]

中文:
引理 uniqueProd_apply
  条件: (x : N × M)
  结论: uniqueProd R M N x = x.2
  证明: rfl

@[simp]
-/
lemma uniqueProd_apply (x : N × M) : uniqueProd R M N x = x.2 := rfl

@[simp]
/--
lemma `uniqueProd_symm_apply` / 引理 `uniqueProd_symm_apply`

English:
lemma uniqueProd_symm_apply
  given: (x : M)
  statement: (uniqueProd R M N).symm x = (default, x)
  proof: rfl

中文:
引理 uniqueProd_symm_apply
  条件: (x : M)
  结论: (uniqueProd R M N).symm x = (default, x)
  证明: rfl
-/
lemma uniqueProd_symm_apply (x : M) : (uniqueProd R M N).symm x = (default, x) := rfl

end prodUnique

variable {R₁ M₁ M₂}

/--
theorem `bijective` / 定理 `bijective`

English:
theorem bijective
  given: (e : M₁ ≃SL[σ₁₂] M₂)
  statement: Function.Bijective e
  proof: e.toLinearEquiv.toEquiv.bijective

中文:
定理 bijective
  条件: (e : M₁ ≃SL[σ₁₂] M₂)
  结论: 函数.双射 e
  证明: e.toLinearEquiv.toEquiv.bijective
-/
protected theorem bijective (e : M₁ ≃SL[σ₁₂] M₂) : Function.Bijective e :=
  e.toLinearEquiv.toEquiv.bijective

/--
theorem `injective` / 定理 `injective`

English:
theorem injective
  given: (e : M₁ ≃SL[σ₁₂] M₂)
  statement: Function.Injective e
  proof: e.toLinearEquiv.toEquiv.injective

中文:
定理 injective
  条件: (e : M₁ ≃SL[σ₁₂] M₂)
  结论: 函数.单射 e
  证明: e.toLinearEquiv.toEquiv.injective
-/
protected theorem injective (e : M₁ ≃SL[σ₁₂] M₂) : Function.Injective e :=
  e.toLinearEquiv.toEquiv.injective

/--
theorem `surjective` / 定理 `surjective`

English:
theorem surjective
  given: (e : M₁ ≃SL[σ₁₂] M₂)
  statement: Function.Surjective e
  proof: e.toLinearEquiv.toEquiv.surjective

@[simp]

中文:
定理 surjective
  条件: (e : M₁ ≃SL[σ₁₂] M₂)
  结论: 函数.满射 e
  证明: e.toLinearEquiv.toEquiv.surjective

@[simp]
-/
protected theorem surjective (e : M₁ ≃SL[σ₁₂] M₂) : Function.Surjective e :=
  e.toLinearEquiv.toEquiv.surjective

@[simp]
/--
theorem `trans_apply` / 定理 `trans_apply`

English:
theorem trans_apply
  given: (e₁ : M₁ ≃SL[σ₁₂] M₂) (e₂ : M₂ ≃SL[σ₂₃] M₃) (c : M₁)
  proof: rfl

@[simp]

中文:
定理 trans_apply
  条件: (e₁ : M₁ ≃SL[σ₁₂] M₂) (e₂ : M₂ ≃SL[σ₂₃] M₃) (c : M₁)
  证明: rfl

@[simp]
-/
theorem trans_apply (e₁ : M₁ ≃SL[σ₁₂] M₂) (e₂ : M₂ ≃SL[σ₂₃] M₃) (c : M₁) :
    (e₁.trans e₂) c = e₂ (e₁ c) :=
  rfl

@[simp]
/--
theorem `apply_symm_apply` / 定理 `apply_symm_apply`

English:
theorem apply_symm_apply
  given: (e : M₁ ≃SL[σ₁₂] M₂) (c : M₂)
  statement: e (e.symm c) = c
  proof: e.1.right_inv c

@[simp]

中文:
定理 apply_symm_apply
  条件: (e : M₁ ≃SL[σ₁₂] M₂) (c : M₂)
  结论: e (e.symm c) = c
  证明: e.1.right_inv c

@[simp]

Depends on / 依赖: right_inv
-/
theorem apply_symm_apply (e : M₁ ≃SL[σ₁₂] M₂) (c : M₂) : e (e.symm c) = c :=
  e.1.right_inv c

@[simp]
/--
theorem `symm_apply_apply` / 定理 `symm_apply_apply`

English:
theorem symm_apply_apply
  given: (e : M₁ ≃SL[σ₁₂] M₂) (b : M₁)
  statement: e.symm (e b) = b
  proof: e.1.left_inv b

中文:
定理 symm_apply_apply
  条件: (e : M₁ ≃SL[σ₁₂] M₂) (b : M₁)
  结论: e.symm (e b) = b
  证明: e.1.left_inv b

Depends on / 依赖: left_inv
-/
theorem symm_apply_apply (e : M₁ ≃SL[σ₁₂] M₂) (b : M₁) : e.symm (e b) = b :=
  e.1.left_inv b

/--
theorem `symm_trans_self` / 定理 `symm_trans_self`

English:
theorem symm_trans_self
  given: (e : M₁ ≃SL[σ₁₂] M₂)
  statement: e.symm.trans e = .refl R₂ M₂
  proof: ext funext fun _ => apply_symm_apply _ _

中文:
定理 symm_trans_self
  条件: (e : M₁ ≃SL[σ₁₂] M₂)
  结论: e.symm.trans e = .refl R₂ M₂
  证明: ext funext fun _ => apply_symm_apply _ _
-/
@[simp] theorem symm_trans_self (e : M₁ ≃SL[σ₁₂] M₂) : e.symm.trans e = .refl R₂ M₂ :=
ext funext fun _ => apply_symm_apply _ _

/--
theorem `self_trans_symm` / 定理 `self_trans_symm`

English:
theorem self_trans_symm
  given: (e : M₁ ≃SL[σ₁₂] M₂)
  statement: e.trans e.symm = .refl R₁ M₁
  proof: ext funext fun _ => symm_apply_apply _ _

@[simp]

中文:
定理 self_trans_symm
  条件: (e : M₁ ≃SL[σ₁₂] M₂)
  结论: e.trans e.symm = .refl R₁ M₁
  证明: ext funext fun _ => symm_apply_apply _ _

@[simp]
-/
@[simp] theorem self_trans_symm (e : M₁ ≃SL[σ₁₂] M₂) : e.trans e.symm = .refl R₁ M₁ :=
ext funext fun _ => symm_apply_apply _ _

@[simp]
/--
theorem `symm_trans_apply` / 定理 `symm_trans_apply`

English:
theorem symm_trans_apply
  given: (e₁ : M₂ ≃SL[σ₂₁] M₁) (e₂ : M₃ ≃SL[σ₃₂] M₂) (c : M₁)
  proof: rfl

@[simp]

中文:
定理 symm_trans_apply
  条件: (e₁ : M₂ ≃SL[σ₂₁] M₁) (e₂ : M₃ ≃SL[σ₃₂] M₂) (c : M₁)
  证明: rfl

@[simp]
-/
theorem symm_trans_apply (e₁ : M₂ ≃SL[σ₂₁] M₁) (e₂ : M₃ ≃SL[σ₃₂] M₂) (c : M₁) :
    (e₂.trans e₁).symm c = e₂.symm (e₁.symm c) :=
  rfl

@[simp]
/--
theorem `symm_image_image` / 定理 `symm_image_image`

English:
theorem symm_image_image
  given: (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₁)
  statement: e.symm '' e '' s = s
  proof: e.toLinearEquiv.toEquiv.symm_image_image s

@[simp]

中文:
定理 symm_image_image
  条件: (e : M₁ ≃SL[σ₁₂] M₂) (s : 集合 M₁)
  结论: e.symm '' e '' s = s
  证明: e.toLinearEquiv.toEquiv.symm_image_image s

@[simp]

Depends on / 依赖: e.toLinearEquiv.toEquiv.symm_image_image, symm_image_image, toEquiv, toLinearEquiv
-/
theorem symm_image_image (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₁) : e.symm '' e '' s = s :=
  e.toLinearEquiv.toEquiv.symm_image_image s

@[simp]
/--
theorem `image_symm_image` / 定理 `image_symm_image`

English:
theorem image_symm_image
  given: (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₂)
  statement: e '' e.symm '' s = s
  proof: e.symm.symm_image_image s

@[simp, norm_cast]

中文:
定理 image_symm_image
  条件: (e : M₁ ≃SL[σ₁₂] M₂) (s : 集合 M₂)
  结论: e '' e.symm '' s = s
  证明: e.symm.symm_image_image s

@[simp, norm_cast]

Depends on / 依赖: e.symm.symm_image_image, symm_image_image
-/
theorem image_symm_image (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₂) : e '' e.symm '' s = s :=
  e.symm.symm_image_image s

@[simp, norm_cast]
/--
theorem `comp_coe` / 定理 `comp_coe`

English:
theorem comp_coe
  given: (f : M₁ ≃SL[σ₁₂] M₂) (f' : M₂ ≃SL[σ₂₃] M₃)
  proof: rfl

中文:
定理 comp_coe
  条件: (f : M₁ ≃SL[σ₁₂] M₂) (f' : M₂ ≃SL[σ₂₃] M₃)
  证明: rfl
-/
theorem comp_coe (f : M₁ ≃SL[σ₁₂] M₂) (f' : M₂ ≃SL[σ₂₃] M₃) :
    (f' : M₂ ->SL[σ₂₃] M₃).comp (f : M₁ ->SL[σ₁₂] M₂) = (f.trans f' : M₁ ->SL[σ₁₃] M₃) :=
  rfl

-- The priority should be higher than `comp_coe`.
@[simp high]
/--
theorem `coe_comp_coe_symm` / 定理 `coe_comp_coe_symm`

English:
theorem coe_comp_coe_symm
  given: (e : M₁ ≃SL[σ₁₂] M₂)
  proof: ContinuousLinearMap.ext e.apply_symm_apply

中文:
定理 coe_comp_coe_symm
  条件: (e : M₁ ≃SL[σ₁₂] M₂)
  证明: ContinuousLinearMap.ext e.apply_symm_apply

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.ext, apply_symm_apply, e.apply_symm_apply
-/
theorem coe_comp_coe_symm (e : M₁ ≃SL[σ₁₂] M₂) :
    (e : M₁ ->SL[σ₁₂] M₂).comp (e.symm : M₂ ->SL[σ₂₁] M₁) = ContinuousLinearMap.id R₂ M₂ :=
  ContinuousLinearMap.ext e.apply_symm_apply

-- The priority should be higher than `comp_coe`.
@[simp high]
/--
theorem `coe_symm_comp_coe` / 定理 `coe_symm_comp_coe`

English:
theorem coe_symm_comp_coe
  given: (e : M₁ ≃SL[σ₁₂] M₂)
  proof: ContinuousLinearMap.ext e.symm_apply_apply

@[simp]

中文:
定理 coe_symm_comp_coe
  条件: (e : M₁ ≃SL[σ₁₂] M₂)
  证明: ContinuousLinearMap.ext e.symm_apply_apply

@[simp]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.ext, e.symm_apply_apply, symm_apply_apply
-/
theorem coe_symm_comp_coe (e : M₁ ≃SL[σ₁₂] M₂) :
    (e.symm : M₂ ->SL[σ₂₁] M₁).comp (e : M₁ ->SL[σ₁₂] M₂) = ContinuousLinearMap.id R₁ M₁ :=
  ContinuousLinearMap.ext e.symm_apply_apply

@[simp]
/--
theorem `symm_comp_self` / 定理 `symm_comp_self`

English:
theorem symm_comp_self
  given: (e : M₁ ≃SL[σ₁₂] M₂)
  statement: (e.symm : M₂ -> M₁) ∘ (e : M₁ -> M₂) = id
  proof: by
  ext x
  exact symm_apply_apply e x

@[simp]

中文:
定理 symm_comp_self
  条件: (e : M₁ ≃SL[σ₁₂] M₂)
  结论: (e.symm : M₂ -> M₁) ∘ (e : M₁ -> M₂) = id
  证明: by
  ext x
  exact symm_apply_apply e x

@[simp]

Depends on / 依赖: symm_apply_apply
-/
theorem symm_comp_self (e : M₁ ≃SL[σ₁₂] M₂) : (e.symm : M₂ -> M₁) ∘ (e : M₁ -> M₂) = id := by
  ext x
  exact symm_apply_apply e x

@[simp]
/--
theorem `self_comp_symm` / 定理 `self_comp_symm`

English:
theorem self_comp_symm
  given: (e : M₁ ≃SL[σ₁₂] M₂)
  statement: (e : M₁ -> M₂) ∘ (e.symm : M₂ -> M₁) = id
  proof: by
  ext x
  exact apply_symm_apply e x

@[simp]

中文:
定理 self_comp_symm
  条件: (e : M₁ ≃SL[σ₁₂] M₂)
  结论: (e : M₁ -> M₂) ∘ (e.symm : M₂ -> M₁) = id
  证明: by
  ext x
  exact apply_symm_apply e x

@[simp]

Depends on / 依赖: apply_symm_apply
-/
theorem self_comp_symm (e : M₁ ≃SL[σ₁₂] M₂) : (e : M₁ -> M₂) ∘ (e.symm : M₂ -> M₁) = id := by
  ext x
  exact apply_symm_apply e x

@[simp]
/--
theorem `symm_symm` / 定理 `symm_symm`

English:
theorem symm_symm
  given: (e : M₁ ≃SL[σ₁₂] M₂)
  statement: e.symm.symm = e
  proof: rfl

中文:
定理 symm_symm
  条件: (e : M₁ ≃SL[σ₁₂] M₂)
  结论: e.symm.symm = e
  证明: rfl
-/
theorem symm_symm (e : M₁ ≃SL[σ₁₂] M₂) : e.symm.symm = e := rfl

/--
theorem `symm_bijective` / 定理 `symm_bijective`

English:
theorem symm_bijective
  statement: Function.Bijective (ContinuousLinearEquiv.symm : (M₁ ≃SL[σ₁₂] M₂) -> _)
  proof: Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]

中文:
定理 symm_bijective
  结论: 函数.双射 (连续线性等价.symm : (M₁ ≃SL[σ₁₂] M₂) -> _)
  证明: Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]

Depends on / 依赖: Function, Function.bijective_iff_has_inverse.mpr, bijective_iff_has_inverse, symm_symm
-/
theorem symm_bijective : Function.Bijective (ContinuousLinearEquiv.symm : (M₁ ≃SL[σ₁₂] M₂) -> _) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]
/--
theorem `refl_symm` / 定理 `refl_symm`

English:
theorem refl_symm
  statement: (ContinuousLinearEquiv.refl R₁ M₁).symm = ContinuousLinearEquiv.refl R₁ M₁
  proof: rfl

中文:
定理 refl_symm
  结论: (连续线性等价.refl R₁ M₁).symm = 连续线性等价.refl R₁ M₁
  证明: rfl
-/
theorem refl_symm : (ContinuousLinearEquiv.refl R₁ M₁).symm = ContinuousLinearEquiv.refl R₁ M₁ :=
  rfl

/--
theorem `symm_symm_apply` / 定理 `symm_symm_apply`

English:
theorem symm_symm_apply
  given: (e : M₁ ≃SL[σ₁₂] M₂) (x : M₁)
  statement: e.symm.symm x = e x
  proof: rfl

中文:
定理 symm_symm_apply
  条件: (e : M₁ ≃SL[σ₁₂] M₂) (x : M₁)
  结论: e.symm.symm x = e x
  证明: rfl
-/
theorem symm_symm_apply (e : M₁ ≃SL[σ₁₂] M₂) (x : M₁) : e.symm.symm x = e x :=
  rfl

/--
theorem `symm_apply_eq` / 定理 `symm_apply_eq`

English:
theorem symm_apply_eq
  given: (e : M₁ ≃SL[σ₁₂] M₂) {x y}
  statement: e.symm x = y ↔ x = e y
  proof: e.toLinearEquiv.symm_apply_eq

中文:
定理 symm_apply_eq
  条件: (e : M₁ ≃SL[σ₁₂] M₂) {x y}
  结论: e.symm x = y ↔ x = e y
  证明: e.toLinearEquiv.symm_apply_eq

Depends on / 依赖: e.toLinearEquiv.symm_apply_eq, symm_apply_eq, toLinearEquiv
-/
theorem symm_apply_eq (e : M₁ ≃SL[σ₁₂] M₂) {x y} : e.symm x = y ↔ x = e y :=
  e.toLinearEquiv.symm_apply_eq

/--
theorem `eq_symm_apply` / 定理 `eq_symm_apply`

English:
theorem eq_symm_apply
  given: (e : M₁ ≃SL[σ₁₂] M₂) {x y}
  statement: y = e.symm x ↔ e y = x
  proof: e.toLinearEquiv.eq_symm_apply

中文:
定理 eq_symm_apply
  条件: (e : M₁ ≃SL[σ₁₂] M₂) {x y}
  结论: y = e.symm x ↔ e y = x
  证明: e.toLinearEquiv.eq_symm_apply

Depends on / 依赖: e.toLinearEquiv.eq_symm_apply, eq_symm_apply, toLinearEquiv
-/
theorem eq_symm_apply (e : M₁ ≃SL[σ₁₂] M₂) {x y} : y = e.symm x ↔ e y = x :=
  e.toLinearEquiv.eq_symm_apply

/--
lemma `image_eq_preimage_symm` / 引理 `image_eq_preimage_symm`

English:
lemma image_eq_preimage_symm
  given: (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₁)
  statement: e '' s = e.symm ⁻¹' s
  proof: e.toLinearEquiv.toEquiv.image_eq_preimage_symm s

中文:
引理 image_eq_preimage_symm
  条件: (e : M₁ ≃SL[σ₁₂] M₂) (s : 集合 M₁)
  结论: e '' s = e.symm ⁻¹' s
  证明: e.toLinearEquiv.toEquiv.image_eq_preimage_symm s
-/
protected lemma image_eq_preimage_symm (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₁) : e '' s = e.symm ⁻¹' s :=
  e.toLinearEquiv.toEquiv.image_eq_preimage_symm s

/--
theorem `image_symm_eq_preimage` / 定理 `image_symm_eq_preimage`

English:
theorem image_symm_eq_preimage
  given: (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₂)
  proof: by rw [e.symm.image_eq_preimage_symm, e.symm_symm]

@[simp]

中文:
定理 image_symm_eq_preimage
  条件: (e : M₁ ≃SL[σ₁₂] M₂) (s : 集合 M₂)
  证明: by rw [e.symm.image_eq_preimage_symm, e.symm_symm]

@[simp]
-/
protected theorem image_symm_eq_preimage (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₂) :
    e.symm '' s = e ⁻¹' s := by rw [e.symm.image_eq_preimage_symm, e.symm_symm]

@[simp]
/--
theorem `symm_preimage_preimage` / 定理 `symm_preimage_preimage`

English:
theorem symm_preimage_preimage
  given: (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₂)
  proof: e.toLinearEquiv.toEquiv.symm_preimage_preimage s

@[simp]

中文:
定理 symm_preimage_preimage
  条件: (e : M₁ ≃SL[σ₁₂] M₂) (s : 集合 M₂)
  证明: e.toLinearEquiv.toEquiv.symm_preimage_preimage s

@[simp]
-/
protected theorem symm_preimage_preimage (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₂) :
    e.symm ⁻¹' e ⁻¹' s = s :=
  e.toLinearEquiv.toEquiv.symm_preimage_preimage s

@[simp]
/--
theorem `preimage_symm_preimage` / 定理 `preimage_symm_preimage`

English:
theorem preimage_symm_preimage
  given: (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₁)
  proof: e.symm.symm_preimage_preimage s

中文:
定理 preimage_symm_preimage
  条件: (e : M₁ ≃SL[σ₁₂] M₂) (s : 集合 M₁)
  证明: e.symm.symm_preimage_preimage s
-/
protected theorem preimage_symm_preimage (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₁) :
    e ⁻¹' e.symm ⁻¹' s = s :=
  e.symm.symm_preimage_preimage s

/--
lemma `isUniformEmbedding` / 引理 `isUniformEmbedding`

English:
lemma isUniformEmbedding
  statement: {E₁ E₂ : Type*} [UniformSpace E₁] [UniformSpace E₂]
  proof: e.toLinearEquiv.toEquiv.isUniformEmbedding e.toContinuousLinearMap.uniformContinuous
    e.symm.toContinuousLinearMap.uniformContinuous

中文:
引理 isUniformEmbedding
  结论: {E₁ E₂ : 类型} [一致空间 E₁] [一致空间 E₂]
  证明: e.toLinearEquiv.toEquiv.isUniformEmbedding e.toContinuousLinearMap.uniformContinuous
    e.symm.toContinuousLinearMap.uniformContinuous

Depends on / 依赖: e.symm.toContinuousLinearMap.uniformContinuous, e.toContinuousLinearMap.uniformContinuous, e.toLinearEquiv.toEquiv.isUniformEmbedding, isUniformEmbedding, toContinuousLinearMap, toEquiv, toLinearEquiv, uniformContinuous
-/
lemma isUniformEmbedding {E₁ E₂ : Type*} [UniformSpace E₁] [UniformSpace E₂]
    [AddCommGroup E₁] [AddCommGroup E₂] [Module R₁ E₁] [Module R₂ E₂] [IsUniformAddGroup E₁]
    [IsUniformAddGroup E₂] (e : E₁ ≃SL[σ₁₂] E₂) : IsUniformEmbedding e :=
  e.toLinearEquiv.toEquiv.isUniformEmbedding e.toContinuousLinearMap.uniformContinuous
    e.symm.toContinuousLinearMap.uniformContinuous

/--
theorem `_root_.LinearEquiv.isUniformEmbedding` / 定理 `_root_.LinearEquiv.isUniformEmbedding`

English:
theorem _root_.LinearEquiv.isUniformEmbedding
  statement: {E₁ E₂ : Type*} [UniformSpace E₁]
  proof: ContinuousLinearEquiv.isUniformEmbedding
    ({ e with
        continuous_toFun := h₁
        continuous_invFun := h₂ } :
      E₁ ≃SL[σ₁₂] E₂)

中文:
定理 _root_.线性等价.isUniformEmbedding
  结论: {E₁ E₂ : 类型} [一致空间 E₁]
  证明: ContinuousLinearEquiv.isUniformEmbedding
    ({ e with
        continuous_toFun := h₁
        continuous_invFun := h₂ } :
      E₁ ≃SL[σ₁₂] E₂)
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

/--
Definition of `equivOfInverse` / `equivOfInverse` 的定义

English:
definition equivOfInverse
  signature: (f₁ : M₁ ->SL[σ₁₂] M₂) (f₂ : M₂ ->SL[σ₂₁] M₁) (h₁ : Function.LeftInverse f₂ f₁)
  body: { f₁ with
    invFun := f₂
    left_inv := h₁
    right_inv := h₂ }

@[simp]

中文:
定义 equivOfInverse
  签名: (f₁ : M₁ ->SL[σ₁₂] M₂) (f₂ : M₂ ->SL[σ₂₁] M₁) (h₁ : 函数.左逆 f₂ f₁)
  定义体: { f₁ with
    invFun := f₂
    left_inv := h₁
    right_inv := h₂ }

@[simp]

Depends on / 依赖: invFun, left_inv, right_inv
-/
def equivOfInverse (f₁ : M₁ ->SL[σ₁₂] M₂) (f₂ : M₂ ->SL[σ₂₁] M₁) (h₁ : Function.LeftInverse f₂ f₁)
    (h₂ : Function.RightInverse f₂ f₁) : M₁ ≃SL[σ₁₂] M₂ :=
  { f₁ with
    invFun := f₂
    left_inv := h₁
    right_inv := h₂ }

@[simp]
/--
theorem `equivOfInverse_apply` / 定理 `equivOfInverse_apply`

English:
theorem equivOfInverse_apply
  given: (f₁ : M₁ ->SL[σ₁₂] M₂) (f₂ h₁ h₂ x)
  proof: rfl

@[simp]

中文:
定理 equivOfInverse_apply
  条件: (f₁ : M₁ ->SL[σ₁₂] M₂) (f₂ h₁ h₂ x)
  证明: rfl

@[simp]
-/
theorem equivOfInverse_apply (f₁ : M₁ ->SL[σ₁₂] M₂) (f₂ h₁ h₂ x) :
    equivOfInverse f₁ f₂ h₁ h₂ x = f₁ x :=
  rfl

@[simp]
/--
theorem `symm_equivOfInverse` / 定理 `symm_equivOfInverse`

English:
theorem symm_equivOfInverse
  given: (f₁ : M₁ ->SL[σ₁₂] M₂) (f₂ h₁ h₂)
  proof: rfl

中文:
定理 symm_equivOfInverse
  条件: (f₁ : M₁ ->SL[σ₁₂] M₂) (f₂ h₁ h₂)
  证明: rfl
-/
theorem symm_equivOfInverse (f₁ : M₁ ->SL[σ₁₂] M₂) (f₂ h₁ h₂) :
    (equivOfInverse f₁ f₂ h₁ h₂).symm = equivOfInverse f₂ f₁ h₂ h₁ :=
  rfl

/--
Definition of `equivOfInverse'` / `equivOfInverse'` 的定义

English:
definition equivOfInverse'
  signature: (f₁ : M₁ ->SL[σ₁₂] M₂) (f₂ : M₂ ->SL[σ₂₁] M₁)
  body: equivOfInverse f₁ f₂
    (fun x => by simpa using congr($(h₂) x)) (fun x => by simpa using congr($(h₁) x))

@[simp]

中文:
定义 equivOfInverse'
  签名: (f₁ : M₁ ->SL[σ₁₂] M₂) (f₂ : M₂ ->SL[σ₂₁] M₁)
  定义体: equivOfInverse f₁ f₂
    (fun x => by simpa using congr($(h₂) x)) (fun x => by simpa using congr($(h₁) x))

@[simp]

Depends on / 依赖: equivOfInverse
-/
def equivOfInverse' (f₁ : M₁ ->SL[σ₁₂] M₂) (f₂ : M₂ ->SL[σ₂₁] M₁)
    (h₁ : f₁.comp f₂ = .id R₂ M₂) (h₂ : f₂.comp f₁ = .id R₁ M₁) : M₁ ≃SL[σ₁₂] M₂ :=
  equivOfInverse f₁ f₂
    (fun x => by simpa using congr($(h₂) x)) (fun x => by simpa using congr($(h₁) x))

@[simp]
/--
theorem `equivOfInverse'_apply` / 定理 `equivOfInverse'_apply`

English:
theorem equivOfInverse'_apply
  given: (f₁ : M₁ ->SL[σ₁₂] M₂) (f₂ h₁ h₂ x)
  proof: rfl

中文:
定理 equivOfInverse'_apply
  条件: (f₁ : M₁ ->SL[σ₁₂] M₂) (f₂ h₁ h₂ x)
  证明: rfl
-/
theorem equivOfInverse'_apply (f₁ : M₁ ->SL[σ₁₂] M₂) (f₂ h₁ h₂ x) :
    equivOfInverse' f₁ f₂ h₁ h₂ x = f₁ x :=
  rfl

/-- The inverse of `equivOfInverse'` is obtained by swapping the order of its parameters. -/
@[simp]
/--
theorem `symm_equivOfInverse'` / 定理 `symm_equivOfInverse'`

English:
theorem symm_equivOfInverse'
  given: (f₁ : M₁ ->SL[σ₁₂] M₂) (f₂ h₁ h₂)
  proof: rfl

中文:
定理 symm_equivOfInverse'
  条件: (f₁ : M₁ ->SL[σ₁₂] M₂) (f₂ h₁ h₂)
  证明: rfl
-/
theorem symm_equivOfInverse' (f₁ : M₁ ->SL[σ₁₂] M₂) (f₂ h₁ h₂) :
    (equivOfInverse' f₁ f₂ h₁ h₂).symm = equivOfInverse' f₂ f₁ h₂ h₁ :=
  rfl

/--
theorem `eq_comp_toContinuousLinearMap_symm` / 定理 `eq_comp_toContinuousLinearMap_symm`

English:
theorem eq_comp_toContinuousLinearMap_symm
  statement: (e₁₂ : M₁ ≃SL[σ₁₂] M₂) [RingHomCompTriple σ₂₁ σ₁₃ σ₂₃]
  proof: by
  aesop

中文:
定理 eq_comp_toContinuousLinearMap_symm
  结论: (e₁₂ : M₁ ≃SL[σ₁₂] M₂) [RingHomCompTriple σ₂₁ σ₁₃ σ₂₃]
  证明: by
  aesop
-/
theorem eq_comp_toContinuousLinearMap_symm (e₁₂ : M₁ ≃SL[σ₁₂] M₂) [RingHomCompTriple σ₂₁ σ₁₃ σ₂₃]
    (f : M₂ ->SL[σ₂₃] M₃) (g : M₁ ->SL[σ₁₃] M₃) :
    f = g.comp e₁₂.symm.toContinuousLinearMap ↔ f.comp e₁₂.toContinuousLinearMap = g := by
  aesop

/--
theorem `eq_toContinuousLinearMap_symm_comp` / 定理 `eq_toContinuousLinearMap_symm_comp`

English:
theorem eq_toContinuousLinearMap_symm_comp
  statement: {e₁₂ : M₁ ≃SL[σ₁₂] M₂} [RingHomCompTriple σ₃₁ σ₁₂ σ₃₂]
  proof: by
  aesop

中文:
定理 eq_toContinuousLinearMap_symm_comp
  结论: {e₁₂ : M₁ ≃SL[σ₁₂] M₂} [RingHomCompTriple σ₃₁ σ₁₂ σ₃₂]
  证明: by
  aesop
-/
theorem eq_toContinuousLinearMap_symm_comp {e₁₂ : M₁ ≃SL[σ₁₂] M₂} [RingHomCompTriple σ₃₁ σ₁₂ σ₃₂]
    (f : M₃ ->SL[σ₃₁] M₁) (g : M₃ ->SL[σ₃₂] M₂) :
    f = e₁₂.symm.toContinuousLinearMap.comp g ↔ e₁₂.toContinuousLinearMap.comp f = g := by
  aesop

variable (M₁)

/--
Instance `automorphismGroup` / 实例 `automorphismGroup`

English:
instance automorphismGroup
  signature: : Group (M₁ ≃L[R₁] M₁) where
  body: g.trans f
  one := ContinuousLinearEquiv.refl R₁ M₁
  inv f := f.symm
  mul_assoc f g h := rfl
  mul_one f := rfl
  one_mul f := rfl
inv_mul_cancel f := ext funext fun _ => f.left_inv _

中文:
实例 automorphismGroup
  签名: : 群 (M₁ ≃L[R₁] M₁) where
  定义体: g.trans f
  one := ContinuousLinearEquiv.refl R₁ M₁
  inv f := f.symm
  mul_assoc f g h := rfl
  mul_one f := rfl
  one_mul f := rfl
inv_mul_cancel f := ext funext fun _ => f.left_inv _

Depends on / 依赖: g.trans
-/
instance automorphismGroup : Group (M₁ ≃L[R₁] M₁) where
  mul f g := g.trans f
  one := ContinuousLinearEquiv.refl R₁ M₁
  inv f := f.symm
  mul_assoc f g h := rfl
  mul_one f := rfl
  one_mul f := rfl
inv_mul_cancel f := ext funext fun _ => f.left_inv _

/--
lemma `toContinuousLinearMap_one` / 引理 `toContinuousLinearMap_one`

English:
lemma toContinuousLinearMap_one
  statement: toContinuousLinearMap (1 : M₁ ≃L[R₁] M₁) = 1
  proof: rfl

中文:
引理 toContinuousLinearMap_one
  结论: toContinuousLinearMap (1 : M₁ ≃L[R₁] M₁) = 1
  证明: rfl
-/
@[simp] lemma toContinuousLinearMap_one : toContinuousLinearMap (1 : M₁ ≃L[R₁] M₁) = 1 := rfl

/--
lemma `toContinuousLinearMap_mul` / 引理 `toContinuousLinearMap_mul`

English:
lemma toContinuousLinearMap_mul
  given: (e e' : M₁ ≃L[R₁] M₁)
  proof: rfl

中文:
引理 toContinuousLinearMap_mul
  条件: (e e' : M₁ ≃L[R₁] M₁)
  证明: rfl
-/
@[simp] lemma toContinuousLinearMap_mul (e e' : M₁ ≃L[R₁] M₁) :
    toContinuousLinearMap (e * e') = e.toContinuousLinearMap * e'.toContinuousLinearMap := rfl

variable {M₁} {R₄ : Type*} [Semiring R₄] [Module R₄ M₄] {σ₃₄ : R₃ ->+* R₄} {σ₄₃ : R₄ ->+* R₃}
  [RingHomInvPair σ₃₄ σ₄₃] [RingHomInvPair σ₄₃ σ₃₄] {σ₂₄ : R₂ ->+* R₄} {σ₁₄ : R₁ ->+* R₄}
  [RingHomCompTriple σ₂₁ σ₁₄ σ₂₄] [RingHomCompTriple σ₂₄ σ₄₃ σ₂₃] [RingHomCompTriple σ₁₃ σ₃₄ σ₁₄]

/--
Definition of `ulift` / `ulift` 的定义

English:
definition ulift
  signature: : ULift M₁ ≃L[R₁] M₁ where
  body: ULift.moduleEquiv

中文:
定义 ulift
  签名: : 类型层提升 M₁ ≃L[R₁] M₁ where
  定义体: ULift.moduleEquiv

Depends on / 依赖: ULift.moduleEquiv, moduleEquiv
-/
def ulift : ULift M₁ ≃L[R₁] M₁ where
  __ := ULift.moduleEquiv

/-- A pair of continuous (semi)linear equivalences generates an equivalence between the spaces of
continuous linear maps. See also `ContinuousLinearEquiv.arrowCongr`. -/
@[simps]
/--
Definition of `arrowCongrEquiv` / `arrowCongrEquiv` 的定义

English:
definition arrowCongrEquiv
  signature: (e₁₂ : M₁ ≃SL[σ₁₂] M₂) (e₄₃ : M₄ ≃SL[σ₄₃] M₃)
  body: (e₄₃ : M₄ ->SL[σ₄₃] M₃).comp (f.comp (e₁₂.symm : M₂ ->SL[σ₂₁] M₁))
  invFun f := (e₄₃.symm : M₃ ->SL[σ₃₄] M₄).comp (f.comp (e₁₂ : M₁ ->SL[σ₁₂] M₂))
  left_inv f :=
    ContinuousLinearMap.ext fun x => by
      simp only [ContinuousLinearMap.comp_apply, symm_apply_apply, coe_coe]
  right_inv f :=
    ContinuousLinearMap.ext fun x => by
      simp only [ContinuousLinearMap.comp_apply, apply_symm_apply, coe_coe]

中文:
定义 arrowCongrEquiv
  签名: (e₁₂ : M₁ ≃SL[σ₁₂] M₂) (e₄₃ : M₄ ≃SL[σ₄₃] M₃)
  定义体: (e₄₃ : M₄ ->SL[σ₄₃] M₃).comp (f.comp (e₁₂.symm : M₂ ->SL[σ₂₁] M₁))
  invFun f := (e₄₃.symm : M₃ ->SL[σ₃₄] M₄).comp (f.comp (e₁₂ : M₁ ->SL[σ₁₂] M₂))
  left_inv f :=
    ContinuousLinearMap.ext fun x => by
      simp only [ContinuousLinearMap.comp_apply, symm_apply_apply, coe_coe]
  right_inv f :=
    ContinuousLinearMap.ext fun x => by
      simp only [ContinuousLinearMap.comp_apply, apply_symm_apply, coe_coe]

Depends on / 依赖: f.comp
-/
def arrowCongrEquiv (e₁₂ : M₁ ≃SL[σ₁₂] M₂) (e₄₃ : M₄ ≃SL[σ₄₃] M₃) :
    (M₁ ->SL[σ₁₄] M₄) ≃ (M₂ ->SL[σ₂₃] M₃) where
  toFun f := (e₄₃ : M₄ ->SL[σ₄₃] M₃).comp (f.comp (e₁₂.symm : M₂ ->SL[σ₂₁] M₁))
  invFun f := (e₄₃.symm : M₃ ->SL[σ₃₄] M₄).comp (f.comp (e₁₂ : M₁ ->SL[σ₁₂] M₂))
  left_inv f :=
    ContinuousLinearMap.ext fun x => by
      simp only [ContinuousLinearMap.comp_apply, symm_apply_apply, coe_coe]
  right_inv f :=
    ContinuousLinearMap.ext fun x => by
      simp only [ContinuousLinearMap.comp_apply, apply_symm_apply, coe_coe]

/-- A pair of continuous (semi)linear equivalences generates a linear equivalence between the spaces
of continuous linear maps. See also `ContinuousLinearEquiv.arrowCongr`. -/
@[simps]
/--
Definition of `arrowCongrEquivₛₗ` / `arrowCongrEquivₛₗ` 的定义

English:
definition arrowCongrEquivₛₗ
  signature: [SMulCommClass R₃ R₃ M₃] [SMulCommClass R₄ R₄ M₄]
  body: arrowCongrEquiv e₁₂ e₄₃
  map_add' := by simp
  map_smul' := by simp

中文:
定义 arrowCongrEquivₛₗ
  签名: [标量交换类 R₃ R₃ M₃] [标量交换类 R₄ R₄ M₄]
  定义体: arrowCongrEquiv e₁₂ e₄₃
  map_add' := by simp
  map_smul' := by simp

Depends on / 依赖: arrowCongrEquiv
-/
def arrowCongrEquivₛₗ [SMulCommClass R₃ R₃ M₃] [SMulCommClass R₄ R₄ M₄]
    [ContinuousAdd M₃] [ContinuousConstSMul R₃ M₃] [ContinuousAdd M₄] [ContinuousConstSMul R₄ M₄]
    (e₁₂ : M₁ ≃SL[σ₁₂] M₂) (e₄₃ : M₄ ≃SL[σ₄₃] M₃) :
    (M₁ ->SL[σ₁₄] M₄) ≃ₛₗ[σ₄₃] (M₂ ->SL[σ₂₃] M₃) where
  toEquiv := arrowCongrEquiv e₁₂ e₄₃
  map_add' := by simp
  map_smul' := by simp

section Pi

/--
Definition of `piCongrLeft` / `piCongrLeft` 的定义

English:
definition piCongrLeft
  signature: (R : Type*) [Semiring R] {ι ι' : Type*}
  body: Homeomorph.piCongrLeft e
  __ := LinearEquiv.piCongrLeft R φ e

中文:
定义 piCongrLeft
  签名: (R : 类型) [半环 R] {ι ι' : 类型}
  定义体: Homeomorph.piCongrLeft e
  __ := LinearEquiv.piCongrLeft R φ e

Depends on / 依赖: Homeomorph, Homeomorph.piCongrLeft, piCongrLeft
-/
def piCongrLeft (R : Type*) [Semiring R] {ι ι' : Type*}
    (φ : ι -> Type*) [forall i, AddCommMonoid (φ i)] [forall i, Module R (φ i)]
    [forall i, TopologicalSpace (φ i)]
    (e : ι' ≃ ι) : ((i' : ι') -> φ (e i')) ≃L[R] (i : ι) -> φ i where
  __ := Homeomorph.piCongrLeft e
  __ := LinearEquiv.piCongrLeft R φ e

/--
Definition of `sumPiEquivProdPi` / `sumPiEquivProdPi` 的定义

English:
definition sumPiEquivProdPi
  signature: (R : Type*) [Semiring R] (S T : Type*)
  body: LinearEquiv.sumPiEquivProdPi R S T A
  __ := Homeomorph.sumPiEquivProdPi S T A

中文:
定义 sumPiEquivProdPi
  签名: (R : 类型) [半环 R] (S T : 类型)
  定义体: LinearEquiv.sumPiEquivProdPi R S T A
  __ := Homeomorph.sumPiEquivProdPi S T A

Depends on / 依赖: LinearEquiv, LinearEquiv.sumPiEquivProdPi, sumPiEquivProdPi
-/
def sumPiEquivProdPi (R : Type*) [Semiring R] (S T : Type*)
    (A : S oplus T -> Type*) [forall st, AddCommMonoid (A st)] [forall st, Module R (A st)]
    [forall st, TopologicalSpace (A st)] :
    ((st : S oplus T) -> A st) ≃L[R] ((s : S) -> A (Sum.inl s)) × ((t : T) -> A (Sum.inr t)) where
  __ := LinearEquiv.sumPiEquivProdPi R S T A
  __ := Homeomorph.sumPiEquivProdPi S T A

/-- The product `Π t : α, f t` of a family of topological modules is isomorphic
(both topologically and algebraically) to the space `f ⬝` when `α` only contains `⬝`.

This is `Equiv.piUnique` as a `ContinuousLinearEquiv`.
-/
@[simps! -fullyApplied]
/--
Definition of `piUnique` / `piUnique` 的定义

English:
definition piUnique
  signature: {α : Type*} [Unique α] (R : Type*) [Semiring R] (f : α -> Type*)
  body: LinearEquiv.piUnique R f
  __ := Homeomorph.piUnique f

中文:
定义 piUnique
  签名: {α : 类型} [唯一 α] (R : 类型) [半环 R] (f : α -> 类型)
  定义体: LinearEquiv.piUnique R f
  __ := Homeomorph.piUnique f

Depends on / 依赖: LinearEquiv, LinearEquiv.piUnique, piUnique
-/
def piUnique {α : Type*} [Unique α] (R : Type*) [Semiring R] (f : α -> Type*)
    [forall x, AddCommMonoid (f x)] [forall x, Module R (f x)] [forall x, TopologicalSpace (f x)] :
    (Π t, f t) ≃L[R] f default where
  __ := LinearEquiv.piUnique R f
  __ := Homeomorph.piUnique f

end Pi

section piCongrRight

variable {ι : Type*} {M : ι -> Type*} [forall i, TopologicalSpace (M i)] [forall i, AddCommMonoid (M i)]
  [forall i, Module R₁ (M i)] {N : ι -> Type*} [forall i, TopologicalSpace (N i)] [forall i, AddCommMonoid (N i)]
  [forall i, Module R₁ (N i)] (f : (i : ι) -> M i ≃L[R₁] N i)

/--
Definition of `piCongrRight` / `piCongrRight` 的定义

English:
definition piCongrRight
  signature: : ((i : ι) -> M i) ≃L[R₁] (i : ι) -> N i where
  body: LinearEquiv.piCongrRight fun i => (f i).toLinearEquiv

@[simp]

中文:
定义 piCongrRight
  签名: : ((i : ι) -> M i) ≃L[R₁] (i : ι) -> N i where
  定义体: LinearEquiv.piCongrRight fun i => (f i).toLinearEquiv

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.piCongrRight, piCongrRight, toLinearEquiv
-/
def piCongrRight : ((i : ι) -> M i) ≃L[R₁] (i : ι) -> N i where
  __ := LinearEquiv.piCongrRight fun i => (f i).toLinearEquiv

@[simp]
/--
theorem `piCongrRight_apply` / 定理 `piCongrRight_apply`

English:
theorem piCongrRight_apply
  given: (m : (i : ι) -> M i) (i : ι)
  proof: rfl

@[simp]

中文:
定理 piCongrRight_apply
  条件: (m : (i : ι) -> M i) (i : ι)
  证明: rfl

@[simp]
-/
theorem piCongrRight_apply (m : (i : ι) -> M i) (i : ι) :
    piCongrRight f m i = (f i) (m i) := rfl

@[simp]
/--
theorem `piCongrRight_symm_apply` / 定理 `piCongrRight_symm_apply`

English:
theorem piCongrRight_symm_apply
  given: (n : (i : ι) -> N i) (i : ι)
  proof: rfl

中文:
定理 piCongrRight_symm_apply
  条件: (n : (i : ι) -> N i) (i : ι)
  证明: rfl
-/
theorem piCongrRight_symm_apply (n : (i : ι) -> N i) (i : ι) :
    (piCongrRight f).symm n i = (f i).symm (n i) := rfl

end piCongrRight

section DistribMulAction

variable {G : Type*} [Group G] [DistribMulAction G M₁] [ContinuousConstSMul G M₁]
  [SMulCommClass G R₁ M₁]

/-- Scalar multiplication by a group element as a continuous linear equivalence. -/
@[simps! apply_toLinearEquiv apply_apply]
/--
Definition of `smulLeft` / `smulLeft` 的定义

English:
definition smulLeft
  signature: : G ->* M₁ ≃L[R₁] M₁ where
  body: ⟨DistribMulAction.toModuleAut _ _ g, continuous_const_smul _, continuous_const_smul _⟩
map_mul' _ _ := toLinearEquiv_injective map_mul (DistribMulAction.toModuleAut _ _) _ _
map_one' := toLinearEquiv_injective map_one DistribMulAction.toModuleAut _ _

中文:
定义 smulLeft
  签名: : G ->* M₁ ≃L[R₁] M₁ where
  定义体: ⟨DistribMulAction.toModuleAut _ _ g, continuous_const_smul _, continuous_const_smul _⟩
map_mul' _ _ := toLinearEquiv_injective map_mul (DistribMulAction.toModuleAut _ _) _ _
map_one' := toLinearEquiv_injective map_one DistribMulAction.toModuleAut _ _

Depends on / 依赖: DistribMulAction, DistribMulAction.toModuleAut, continuous_const_smul, toModuleAut
-/
def smulLeft : G ->* M₁ ≃L[R₁] M₁ where
  toFun g := ⟨DistribMulAction.toModuleAut _ _ g, continuous_const_smul _, continuous_const_smul _⟩
map_mul' _ _ := toLinearEquiv_injective map_mul (DistribMulAction.toModuleAut _ _) _ _
map_one' := toLinearEquiv_injective map_one DistribMulAction.toModuleAut _ _

end DistribMulAction

end AddCommMonoid

section Aut

/-!
### Automorphisms as continuous linear equivalences and as units of the ring of endomorphisms

The next theorems cover the identification between `M ≃L[R] M` and the group of units of the ring
`M →L[R] M`.
-/

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [TopologicalSpace M]

/--
Definition of `ofUnit` / `ofUnit` 的定义

English:
definition ofUnit
  signature: (f : (M ->L[R] M)ˣ)
  body: { toFun := f.val
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

中文:
定义 ofUnit
  签名: (f : (M ->L[R] M)ˣ)
  定义体: { toFun := f.val
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

Depends on / 依赖: f.inv, f.inv_val, f.val, f.val_inv, invFun, inv_val, left_inv, map_add, map_smul, right_inv, val_inv
-/
def ofUnit (f : (M ->L[R] M)ˣ) : M ≃L[R] M where
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

/--
Definition of `toUnit` / `toUnit` 的定义

English:
definition toUnit
  signature: (f : M ≃L[R] M)
  body: f
  inv := f.symm
  val_inv := by
    ext
    simp
  inv_val := by
    ext
    simp

中文:
定义 toUnit
  签名: (f : M ≃L[R] M)
  定义体: f
  inv := f.symm
  val_inv := by
    ext
    simp
  inv_val := by
    ext
    simp
-/
def toUnit (f : M ≃L[R] M) : (M ->L[R] M)ˣ where
  val := f
  inv := f.symm
  val_inv := by
    ext
    simp
  inv_val := by
    ext
    simp

variable (R M)

/--
Definition of `unitsEquiv` / `unitsEquiv` 的定义

English:
definition unitsEquiv
  signature: : (M ->L[R] M)ˣ ≃* M ≃L[R] M where
  body: ofUnit
  invFun := toUnit
  map_mul' x y := by
    ext
    rfl

@[simp]

中文:
定义 unitsEquiv
  签名: : (M ->L[R] M)ˣ ≃* M ≃L[R] M where
  定义体: ofUnit
  invFun := toUnit
  map_mul' x y := by
    ext
    rfl

@[simp]

Depends on / 依赖: ofUnit
-/
def unitsEquiv : (M ->L[R] M)ˣ ≃* M ≃L[R] M where
  toFun := ofUnit
  invFun := toUnit
  map_mul' x y := by
    ext
    rfl

@[simp]
/--
theorem `unitsEquiv_apply` / 定理 `unitsEquiv_apply`

English:
theorem unitsEquiv_apply
  given: (f : (M ->L[R] M)ˣ) (x : M)
  statement: unitsEquiv R M f x = (f : M ->L[R] M) x
  proof: rfl

中文:
定理 unitsEquiv_apply
  条件: (f : (M ->L[R] M)ˣ) (x : M)
  结论: unitsEquiv R M f x = (f : M ->L[R] M) x
  证明: rfl
-/
theorem unitsEquiv_apply (f : (M ->L[R] M)ˣ) (x : M) : unitsEquiv R M f x = (f : M ->L[R] M) x :=
  rfl

end Aut

section AutRing

/-!
### Units of a ring as linear automorphisms
-/

variable (R : Type*) [Semiring R] [TopologicalSpace R] [ContinuousMul R]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `unitsEquivAut` / `unitsEquivAut` 的定义

English:
definition unitsEquivAut
  signature: : Rˣ ≃ R ≃L[R] R where
  body: equivOfInverse (ContinuousLinearMap.smulRight (1 : R ->L[R] R) ↑u)
      (ContinuousLinearMap.smulRight (1 : R ->L[R] R) ↑u⁻¹) (fun x => by simp) fun x => by simp
  invFun e :=
    ⟨e 1, e.symm 1, by rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one, symm_apply_apply], by
      rw [← smul_eq_mul]; rw [← map_smul]; rw [smul_eq_mul]; rw [mul_one]; rw [apply_symm_apply]⟩
left_inv u := Units.ext by simp
right_inv e := ext₁ by simp

中文:
定义 unitsEquivAut
  签名: : Rˣ ≃ R ≃L[R] R where
  定义体: equivOfInverse (ContinuousLinearMap.smulRight (1 : R ->L[R] R) ↑u)
      (ContinuousLinearMap.smulRight (1 : R ->L[R] R) ↑u⁻¹) (fun x => by simp) fun x => by simp
  invFun e :=
    ⟨e 1, e.symm 1, by rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one, symm_apply_apply], by
      rw [← smul_eq_mul]; rw [← map_smul]; rw [smul_eq_mul]; rw [mul_one]; rw [apply_symm_apply]⟩
left_inv u := Units.ext by simp
right_inv e := ext₁ by simp

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.smulRight, Units.ext, apply_symm_apply, e.symm, equivOfInverse, invFun, left_inv, map_smul, mul_one, right_inv, smulRight, smul_eq_mul, symm_apply_apply
-/
def unitsEquivAut : Rˣ ≃ R ≃L[R] R where
  toFun u :=
    equivOfInverse (ContinuousLinearMap.smulRight (1 : R ->L[R] R) ↑u)
      (ContinuousLinearMap.smulRight (1 : R ->L[R] R) ↑u⁻¹) (fun x => by simp) fun x => by simp
  invFun e :=
    ⟨e 1, e.symm 1, by rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one, symm_apply_apply], by
      rw [← smul_eq_mul]; rw [← map_smul]; rw [smul_eq_mul]; rw [mul_one]; rw [apply_symm_apply]⟩
left_inv u := Units.ext by simp
right_inv e := ext₁ by simp

variable {R}

@[simp]
/--
theorem `unitsEquivAut_apply` / 定理 `unitsEquivAut_apply`

English:
theorem unitsEquivAut_apply
  given: (u : Rˣ) (x : R)
  statement: unitsEquivAut R u x = x * u
  proof: rfl

@[simp]

中文:
定理 unitsEquivAut_apply
  条件: (u : Rˣ) (x : R)
  结论: unitsEquivAut R u x = x * u
  证明: rfl

@[simp]
-/
theorem unitsEquivAut_apply (u : Rˣ) (x : R) : unitsEquivAut R u x = x * u :=
  rfl

@[simp]
/--
theorem `unitsEquivAut_apply_symm` / 定理 `unitsEquivAut_apply_symm`

English:
theorem unitsEquivAut_apply_symm
  given: (u : Rˣ) (x : R)
  statement: (unitsEquivAut R u).symm x = x * ↑u⁻¹
  proof: rfl

@[simp]

中文:
定理 unitsEquivAut_apply_symm
  条件: (u : Rˣ) (x : R)
  结论: (unitsEquivAut R u).symm x = x * ↑u⁻¹
  证明: rfl

@[simp]
-/
theorem unitsEquivAut_apply_symm (u : Rˣ) (x : R) : (unitsEquivAut R u).symm x = x * ↑u⁻¹ :=
  rfl

@[simp]
/--
theorem `unitsEquivAut_symm_apply` / 定理 `unitsEquivAut_symm_apply`

English:
theorem unitsEquivAut_symm_apply
  given: (e : R ≃L[R] R)
  statement: ↑((unitsEquivAut R).symm e) = e 1
  proof: rfl

中文:
定理 unitsEquivAut_symm_apply
  条件: (e : R ≃L[R] R)
  结论: ↑((unitsEquivAut R).symm e) = e 1
  证明: rfl
-/
theorem unitsEquivAut_symm_apply (e : R ≃L[R] R) : ↑((unitsEquivAut R).symm e) = e 1 :=
  rfl

end AutRing

section Pi

variable (ι R M : Type*) [Unique ι] [Semiring R] [AddCommMonoid M] [Module R M]
  [TopologicalSpace M]

/--
Definition of `funUnique` / `funUnique` 的定义

English:
definition funUnique
  signature: : (ι -> M) ≃L[R] M
  body: { Homeomorph.funUnique ι M with toLinearEquiv := LinearEquiv.funUnique ι R M }

中文:
定义 funUnique
  签名: : (ι -> M) ≃L[R] M
  定义体: { Homeomorph.funUnique ι M with toLinearEquiv := LinearEquiv.funUnique ι R M }

Depends on / 依赖: Homeomorph, Homeomorph.funUnique, LinearEquiv, LinearEquiv.funUnique, funUnique, toLinearEquiv
-/
def funUnique : (ι -> M) ≃L[R] M :=
  { Homeomorph.funUnique ι M with toLinearEquiv := LinearEquiv.funUnique ι R M }

variable {ι R M}

@[simp]
/--
theorem `coe_funUnique` / 定理 `coe_funUnique`

English:
theorem coe_funUnique
  statement: ⇑(funUnique ι R M) = Function.eval default
  proof: rfl

@[simp]

中文:
定理 coe_funUnique
  结论: ⇑(funUnique ι R M) = 函数.eval default
  证明: rfl

@[simp]
-/
theorem coe_funUnique : ⇑(funUnique ι R M) = Function.eval default :=
  rfl

@[simp]
/--
theorem `coe_funUnique_symm` / 定理 `coe_funUnique_symm`

English:
theorem coe_funUnique_symm
  statement: ⇑(funUnique ι R M).symm = Function.const ι
  proof: rfl

中文:
定理 coe_funUnique_symm
  结论: ⇑(funUnique ι R M).symm = 函数.const ι
  证明: rfl
-/
theorem coe_funUnique_symm : ⇑(funUnique ι R M).symm = Function.const ι :=
  rfl

variable (R M)

/-- Continuous linear equivalence between dependent functions `(i : Fin 2) → M i` and `M 0 × M 1`.
-/
@[simps! -fullyApplied apply symm_apply]
/--
Definition of `piFinTwo` / `piFinTwo` 的定义

English:
definition piFinTwo
  signature: (M : Fin 2 -> Type*) [forall i, AddCommMonoid (M i)] [forall i, Module R (M i)]
  body: { Homeomorph.piFinTwo M with toLinearEquiv := LinearEquiv.piFinTwo R M }

中文:
定义 piFinTwo
  签名: (M : 有限集 2 -> 类型) [对任意 i, 加法交换幺半群 (M i)] [对任意 i, 模 R (M i)]
  定义体: { Homeomorph.piFinTwo M with toLinearEquiv := LinearEquiv.piFinTwo R M }

Depends on / 依赖: Homeomorph, Homeomorph.piFinTwo, LinearEquiv, LinearEquiv.piFinTwo, piFinTwo, toLinearEquiv
-/
def piFinTwo (M : Fin 2 -> Type*) [forall i, AddCommMonoid (M i)] [forall i, Module R (M i)]
    [forall i, TopologicalSpace (M i)] : ((i : _) -> M i) ≃L[R] M 0 × M 1 :=
  { Homeomorph.piFinTwo M with toLinearEquiv := LinearEquiv.piFinTwo R M }

/-- Continuous linear equivalence between vectors in `M² = Fin 2 → M` and `M × M`. -/
@[simps! -fullyApplied apply symm_apply]
/--
Definition of `finTwoArrow` / `finTwoArrow` 的定义

English:
definition finTwoArrow
  signature: : (Fin 2 -> M) ≃L[R] M × M
  body: { piFinTwo R fun _ => M with toLinearEquiv := LinearEquiv.finTwoArrow R M }

中文:
定义 finTwoArrow
  签名: : (有限集 2 -> M) ≃L[R] M × M
  定义体: { piFinTwo R fun _ => M with toLinearEquiv := LinearEquiv.finTwoArrow R M }

Depends on / 依赖: LinearEquiv, LinearEquiv.finTwoArrow, finTwoArrow, piFinTwo, toLinearEquiv
-/
def finTwoArrow : (Fin 2 -> M) ≃L[R] M × M :=
  { piFinTwo R fun _ => M with toLinearEquiv := LinearEquiv.finTwoArrow R M }

section
variable {n : Nat} {R : Type*} {M : Fin n.succ -> Type*} {N : Type*}
variable [Semiring R]
variable [forall i, AddCommMonoid (M i)] [forall i, Module R (M i)] [forall i, TopologicalSpace (M i)]

set_option backward.defeqAttrib.useBackward true in
variable (R M) in
/-- `Fin.consEquiv` as a continuous linear equivalence. -/
@[simps!]
/--
Definition of `_root_.Fin.consEquivL` / `_root_.Fin.consEquivL` 的定义

English:
definition _root_.Fin.consEquivL
  signature: : (M 0 × Π i, M (Fin.succ i)) ≃L[R] (Π i, M i) where
  body: Fin.consLinearEquiv R M

中文:
定义 _root_.有限集.consEquivL
  签名: : (M 0 × Π i, M (有限集.succ i)) ≃L[R] (Π i, M i) where
  定义体: Fin.consLinearEquiv R M

Depends on / 依赖: Fin.consLinearEquiv, consLinearEquiv
-/
def _root_.Fin.consEquivL : (M 0 × Π i, M (Fin.succ i)) ≃L[R] (Π i, M i) where
  __ := Fin.consLinearEquiv R M

/--
Definition of `_root_.ContinuousLinearMap.finCons` / `_root_.ContinuousLinearMap.finCons` 的定义

English:
abbreviation _root_.ContinuousLinearMap.finCons
  body: Fin.consEquivL R M ∘L f.prod fs

中文:
缩写 _root_.连续线性映射.finCons
  定义体: Fin.consEquivL R M ∘L f.prod fs

Depends on / 依赖: Fin.consEquivL, consEquivL, f.prod
-/
abbrev _root_.ContinuousLinearMap.finCons
    [AddCommMonoid N] [Module R N] [TopologicalSpace N]
    (f : N ->L[R] M 0) (fs : N ->L[R] Π i, M (Fin.succ i)) :
    N ->L[R] Π i, M i :=
  Fin.consEquivL R M ∘L f.prod fs

end

end Pi

section AddCommGroup

variable {R : Type*} [Semiring R] {M : Type*} [TopologicalSpace M] [AddCommGroup M] {M₂ : Type*}
  [TopologicalSpace M₂] [AddCommGroup M₂] {M₃ : Type*} [TopologicalSpace M₃] [AddCommGroup M₃]
  {M₄ : Type*} [TopologicalSpace M₄] [AddCommGroup M₄] [Module R M] [Module R M₂] [Module R M₃]
  [Module R M₄]

variable [IsTopologicalAddGroup M₄]

/--
Definition of `skewProd` / `skewProd` 的定义

English:
definition skewProd
  signature: (e : M ≃L[R] M₂) (e' : M₃ ≃L[R] M₄) (f : M ->L[R] M₄)
  body: e.toLinearEquiv.skewProd e'.toLinearEquiv ↑f

@[simp]

中文:
定义 skewProd
  签名: (e : M ≃L[R] M₂) (e' : M₃ ≃L[R] M₄) (f : M ->L[R] M₄)
  定义体: e.toLinearEquiv.skewProd e'.toLinearEquiv ↑f

@[simp]

Depends on / 依赖: e.toLinearEquiv.skewProd, skewProd, toLinearEquiv
-/
def skewProd (e : M ≃L[R] M₂) (e' : M₃ ≃L[R] M₄) (f : M ->L[R] M₄) : (M × M₃) ≃L[R] M₂ × M₄ where
  __ := e.toLinearEquiv.skewProd e'.toLinearEquiv ↑f

@[simp]
/--
theorem `skewProd_apply` / 定理 `skewProd_apply`

English:
theorem skewProd_apply
  given: (e : M ≃L[R] M₂) (e' : M₃ ≃L[R] M₄) (f : M ->L[R] M₄) (x)
  proof: rfl

@[simp]

中文:
定理 skewProd_apply
  条件: (e : M ≃L[R] M₂) (e' : M₃ ≃L[R] M₄) (f : M ->L[R] M₄) (x)
  证明: rfl

@[simp]
-/
theorem skewProd_apply (e : M ≃L[R] M₂) (e' : M₃ ≃L[R] M₄) (f : M ->L[R] M₄) (x) :
    e.skewProd e' f x = (e x.1, e' x.2 + f x.1) :=
  rfl

@[simp]
/--
theorem `skewProd_symm_apply` / 定理 `skewProd_symm_apply`

English:
theorem skewProd_symm_apply
  given: (e : M ≃L[R] M₂) (e' : M₃ ≃L[R] M₄) (f : M ->L[R] M₄) (x)
  proof: rfl

中文:
定理 skewProd_symm_apply
  条件: (e : M ≃L[R] M₂) (e' : M₃ ≃L[R] M₄) (f : M ->L[R] M₄) (x)
  证明: rfl
-/
theorem skewProd_symm_apply (e : M ≃L[R] M₂) (e' : M₃ ≃L[R] M₄) (f : M ->L[R] M₄) (x) :
    (e.skewProd e' f).symm x = (e.symm x.1, e'.symm (x.2 - f (e.symm x.1))) :=
  rfl

variable (R) in
/--
Definition of `neg` / `neg` 的定义

English:
definition neg
  signature: [ContinuousNeg M]
  body: LinearEquiv.neg R

@[simp]

中文:
定义 neg
  签名: [连续取负 M]
  定义体: LinearEquiv.neg R

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.neg
-/
def neg [ContinuousNeg M] :
    M ≃L[R] M where
  __ := LinearEquiv.neg R

@[simp]
/--
theorem `coe_neg` / 定理 `coe_neg`

English:
theorem coe_neg
  given: [ContinuousNeg M]
  proof: rfl

@[simp]

中文:
定理 coe_neg
  条件: [连续取负 M]
  证明: rfl

@[simp]
-/
theorem coe_neg [ContinuousNeg M] :
    (neg R : M -> M) = -id := rfl

@[simp]
/--
theorem `neg_apply` / 定理 `neg_apply`

English:
theorem neg_apply
  given: [ContinuousNeg M] (x : M)
  proof: by simp

@[simp]

中文:
定理 neg_apply
  条件: [连续取负 M] (x : M)
  证明: by simp

@[simp]
-/
theorem neg_apply [ContinuousNeg M] (x : M) :
    neg R x = -x := by simp

@[simp]
/--
theorem `symm_neg` / 定理 `symm_neg`

English:
theorem symm_neg
  given: [ContinuousNeg M]
  proof: rfl

中文:
定理 symm_neg
  条件: [连续取负 M]
  证明: rfl
-/
theorem symm_neg [ContinuousNeg M] :
    (neg R : M ≃L[R] M).symm = neg R := rfl

end AddCommGroup

section Ring

variable {R : Type*} [Ring R] {R₂ : Type*} [Ring R₂] {M : Type*} [TopologicalSpace M]
  [AddCommGroup M] [Module R M] {M₂ : Type*} [TopologicalSpace M₂] [AddCommGroup M₂] [Module R₂ M₂]

variable {σ₁₂ : R ->+* R₂} {σ₂₁ : R₂ ->+* R} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]

/--
theorem `map_sub` / 定理 `map_sub`

English:
theorem map_sub
  given: (e : M ≃SL[σ₁₂] M₂) (x y : M)
  statement: e (x - y) = e x - e y
  proof: (e : M ->SL[σ₁₂] M₂).map_sub x y

中文:
定理 map_sub
  条件: (e : M ≃SL[σ₁₂] M₂) (x y : M)
  结论: e (x - y) = e x - e y
  证明: (e : M ->SL[σ₁₂] M₂).map_sub x y

Depends on / 依赖: map_sub
-/
theorem map_sub (e : M ≃SL[σ₁₂] M₂) (x y : M) : e (x - y) = e x - e y :=
  (e : M ->SL[σ₁₂] M₂).map_sub x y

/--
theorem `map_neg` / 定理 `map_neg`

English:
theorem map_neg
  given: (e : M ≃SL[σ₁₂] M₂) (x : M)
  statement: e (-x) = -e x
  proof: (e : M ->SL[σ₁₂] M₂).map_neg x

中文:
定理 map_neg
  条件: (e : M ≃SL[σ₁₂] M₂) (x : M)
  结论: e (-x) = -e x
  证明: (e : M ->SL[σ₁₂] M₂).map_neg x

Depends on / 依赖: map_neg
-/
theorem map_neg (e : M ≃SL[σ₁₂] M₂) (x : M) : e (-x) = -e x :=
  (e : M ->SL[σ₁₂] M₂).map_neg x

variable [Module R M₂] [IsTopologicalAddGroup M]

/--
Definition of `equivOfRightInverse` / `equivOfRightInverse` 的定义

English:
definition equivOfRightInverse
  signature: (f₁ : M ->L[R] M₂) (f₂ : M₂ ->L[R] M) (h : Function.RightInverse f₂ f₁)
  body: equivOfInverse (f₁.prod (f₁.projKerOfRightInverse f₂ h)) (f₂.coprod f₁.ker.subtypeL)
    (fun x => by simp) fun ⟨x, y⟩ => by simp [h x]

@[simp]

中文:
定义 equivOfRightInverse
  签名: (f₁ : M ->L[R] M₂) (f₂ : M₂ ->L[R] M) (h : 函数.右逆 f₂ f₁)
  定义体: equivOfInverse (f₁.prod (f₁.projKerOfRightInverse f₂ h)) (f₂.coprod f₁.ker.subtypeL)
    (fun x => by simp) fun ⟨x, y⟩ => by simp [h x]

@[simp]

Depends on / 依赖: coprod, equivOfInverse, ker.subtypeL, projKerOfRightInverse, subtypeL
-/
def equivOfRightInverse (f₁ : M ->L[R] M₂) (f₂ : M₂ ->L[R] M) (h : Function.RightInverse f₂ f₁) :
    M ≃L[R] M₂ × f₁.ker :=
  equivOfInverse (f₁.prod (f₁.projKerOfRightInverse f₂ h)) (f₂.coprod f₁.ker.subtypeL)
    (fun x => by simp) fun ⟨x, y⟩ => by simp [h x]

@[simp]
/--
theorem `fst_equivOfRightInverse` / 定理 `fst_equivOfRightInverse`

English:
theorem fst_equivOfRightInverse
  statement: (f₁ : M ->L[R] M₂) (f₂ : M₂ ->L[R] M)
  proof: rfl

@[simp]

中文:
定理 fst_equivOfRightInverse
  结论: (f₁ : M ->L[R] M₂) (f₂ : M₂ ->L[R] M)
  证明: rfl

@[simp]
-/
theorem fst_equivOfRightInverse (f₁ : M ->L[R] M₂) (f₂ : M₂ ->L[R] M)
    (h : Function.RightInverse f₂ f₁) (x : M) : (equivOfRightInverse f₁ f₂ h x).1 = f₁ x :=
  rfl

@[simp]
/--
theorem `snd_equivOfRightInverse` / 定理 `snd_equivOfRightInverse`

English:
theorem snd_equivOfRightInverse
  statement: (f₁ : M ->L[R] M₂) (f₂ : M₂ ->L[R] M)
  proof: rfl

@[simp]

中文:
定理 snd_equivOfRightInverse
  结论: (f₁ : M ->L[R] M₂) (f₂ : M₂ ->L[R] M)
  证明: rfl

@[simp]
-/
theorem snd_equivOfRightInverse (f₁ : M ->L[R] M₂) (f₂ : M₂ ->L[R] M)
    (h : Function.RightInverse f₂ f₁) (x : M) :
    ((equivOfRightInverse f₁ f₂ h x).2 : M) = x - f₂ (f₁ x) :=
  rfl

@[simp]
/--
theorem `equivOfRightInverse_symm_apply` / 定理 `equivOfRightInverse_symm_apply`

English:
theorem equivOfRightInverse_symm_apply
  statement: (f₁ : M ->L[R] M₂) (f₂ : M₂ ->L[R] M)
  proof: rfl

中文:
定理 equivOfRightInverse_symm_apply
  结论: (f₁ : M ->L[R] M₂) (f₂ : M₂ ->L[R] M)
  证明: rfl
-/
theorem equivOfRightInverse_symm_apply (f₁ : M ->L[R] M₂) (f₂ : M₂ ->L[R] M)
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
/--
Definition of `restrictScalars` / `restrictScalars` 的定义

English:
definition restrictScalars
  signature: (R : Type*) {S : Type*} {M : Type*}
  body: f.toLinearEquiv.restrictScalars R

中文:
定义 restrictScalars
  签名: (R : 类型) {S : 类型} {M : 类型}
  定义体: f.toLinearEquiv.restrictScalars R

Depends on / 依赖: f.toLinearEquiv.restrictScalars, restrictScalars, toLinearEquiv
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

/--
Definition of `IsInvertible` / `IsInvertible` 的定义

English:
definition IsInvertible
  signature: (f : M ->L[R] M₂)
  body: exists (A : M ≃L[R] M₂), A = f

中文:
定义 IsInvertible
  签名: (f : M ->L[R] M₂)
  定义体: exists (A : M ≃L[R] M₂), A = f
-/
def IsInvertible (f : M ->L[R] M₂) : Prop :=
  exists (A : M ≃L[R] M₂), A = f

open scoped Classical in
/--
Definition of `inverse` / `inverse` 的定义

English:
definition inverse
  signature: : (M ->L[R] M₂) -> M₂ ->L[R] M
  body: fun f =>
  if h : f.IsInvertible then ((Classical.choose h).symm : M₂ ->L[R] M) else 0

中文:
定义 inverse
  签名: : (M ->L[R] M₂) -> M₂ ->L[R] M
  定义体: fun f =>
  if h : f.IsInvertible then ((Classical.choose h).symm : M₂ ->L[R] M) else 0
-/
noncomputable def inverse : (M ->L[R] M₂) -> M₂ ->L[R] M := fun f =>
  if h : f.IsInvertible then ((Classical.choose h).symm : M₂ ->L[R] M) else 0

/--
lemma `isInvertible_equiv` / 引理 `isInvertible_equiv`

English:
lemma isInvertible_equiv
  given: {f : M ≃L[R] M₂}
  statement: IsInvertible (f : M ->L[R] M₂)
  proof: ⟨f, rfl⟩

中文:
引理 isInvertible_equiv
  条件: {f : M ≃L[R] M₂}
  结论: IsInvertible (f : M ->L[R] M₂)
  证明: ⟨f, rfl⟩
-/
@[simp] lemma isInvertible_equiv {f : M ≃L[R] M₂} : IsInvertible (f : M ->L[R] M₂) := ⟨f, rfl⟩

/-- By definition, if `f` is invertible then `inverse f = f.symm`. -/
@[simp]
/--
theorem `inverse_equiv` / 定理 `inverse_equiv`

English:
theorem inverse_equiv
  given: (e : M ≃L[R] M₂)
  statement: inverse (e : M ->L[R] M₂) = e.symm
  proof: by
  simp [inverse]

中文:
定理 inverse_equiv
  条件: (e : M ≃L[R] M₂)
  结论: inverse (e : M ->L[R] M₂) = e.symm
  证明: by
  simp [inverse]

Depends on / 依赖: inverse
-/
theorem inverse_equiv (e : M ≃L[R] M₂) : inverse (e : M ->L[R] M₂) = e.symm := by
  simp [inverse]

/--
lemma `inverse_of_not_isInvertible` / 引理 `inverse_of_not_isInvertible`

English:
lemma inverse_of_not_isInvertible
  proof: dif_neg hf

@[simp]

中文:
引理 inverse_of_not_isInvertible
  证明: dif_neg hf

@[simp]
-/
@[simp] lemma inverse_of_not_isInvertible
    {f : M ->L[R] M₂} (hf : ¬ f.IsInvertible) : f.inverse = 0 :=
  dif_neg hf

@[simp]
/--
theorem `isInvertible_zero_iff` / 定理 `isInvertible_zero_iff`

English:
theorem isInvertible_zero_iff
  proof: by
  refine ⟨fun ⟨e, he⟩ => ?_, ?_⟩
  · have A : Subsingleton M := by
      refine ⟨fun x y => e.injective ?_⟩
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

中文:
定理 isInvertible_zero_iff
  证明: by
  refine ⟨fun ⟨e, he⟩ => ?_, ?_⟩
  · have A : Subsingleton M := by
      refine ⟨fun x y => e.injective ?_⟩
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

Depends on / 依赖: ContinuousLinearEquiv, ContinuousLinearEquiv.coe_coe, Subsingleton, Subsingleton.elim, coe_coe, e.injective, e.toEquiv.symm.subsingleton, injective, invFun, left_inv, map_add, map_smul, right_inv, subsingleton, toEquiv
-/
theorem isInvertible_zero_iff :
    IsInvertible (0 : M ->L[R] M₂) ↔ Subsingleton M ∧ Subsingleton M₂ := by
  refine ⟨fun ⟨e, he⟩ => ?_, ?_⟩
  · have A : Subsingleton M := by
      refine ⟨fun x y => e.injective ?_⟩
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

/--
theorem `inverse_zero` / 定理 `inverse_zero`

English:
theorem inverse_zero
  statement: inverse (0 : M ->L[R] M₂) = 0
  proof: by
  by_cases h : IsInvertible (0 : M ->L[R] M₂)
  · rcases isInvertible_zero_iff.1 h with ⟨hM, hM₂⟩
    ext x
    exact Subsingleton.elim _ _
  · exact inverse_of_not_isInvertible h

中文:
定理 inverse_zero
  结论: inverse (0 : M ->L[R] M₂) = 0
  证明: by
  by_cases h : IsInvertible (0 : M ->L[R] M₂)
  · rcases isInvertible_zero_iff.1 h with ⟨hM, hM₂⟩
    ext x
    exact Subsingleton.elim _ _
  · exact inverse_of_not_isInvertible h
-/
@[simp] theorem inverse_zero : inverse (0 : M ->L[R] M₂) = 0 := by
  by_cases h : IsInvertible (0 : M ->L[R] M₂)
  · rcases isInvertible_zero_iff.1 h with ⟨hM, hM₂⟩
    ext x
    exact Subsingleton.elim _ _
  · exact inverse_of_not_isInvertible h

/--
lemma `IsInvertible.comp` / 引理 `IsInvertible.comp`

English:
lemma IsInvertible.comp
  statement: {g : M₂ ->L[R] M₃} {f : M ->L[R] M₂}
  proof: by
  rcases hg with ⟨N, rfl⟩
  rcases hf with ⟨M, rfl⟩
  exact ⟨M.trans N, rfl⟩

中文:
引理 IsInvertible.comp
  结论: {g : M₂ ->L[R] M₃} {f : M ->L[R] M₂}
  证明: by
  rcases hg with ⟨N, rfl⟩
  rcases hf with ⟨M, rfl⟩
  exact ⟨M.trans N, rfl⟩

Depends on / 依赖: M.trans
-/
lemma IsInvertible.comp {g : M₂ ->L[R] M₃} {f : M ->L[R] M₂}
    (hg : g.IsInvertible) (hf : f.IsInvertible) : (g ∘L f).IsInvertible := by
  rcases hg with ⟨N, rfl⟩
  rcases hf with ⟨M, rfl⟩
  exact ⟨M.trans N, rfl⟩

/--
lemma `IsInvertible.of_inverse` / 引理 `IsInvertible.of_inverse`

English:
lemma IsInvertible.of_inverse
  statement: {f : M ->L[R] M₂} {g : M₂ ->L[R] M}
  proof: ⟨ContinuousLinearEquiv.equivOfInverse' _ _ hf hg, rfl⟩

中文:
引理 IsInvertible.of_inverse
  结论: {f : M ->L[R] M₂} {g : M₂ ->L[R] M}
  证明: ⟨ContinuousLinearEquiv.equivOfInverse' _ _ hf hg, rfl⟩

Depends on / 依赖: ContinuousLinearEquiv, ContinuousLinearEquiv.equivOfInverse, equivOfInverse
-/
lemma IsInvertible.of_inverse {f : M ->L[R] M₂} {g : M₂ ->L[R] M}
    (hf : f ∘L g = .id R M₂) (hg : g ∘L f = .id R M) :
    f.IsInvertible :=
  ⟨ContinuousLinearEquiv.equivOfInverse' _ _ hf hg, rfl⟩

/--
lemma `inverse_eq` / 引理 `inverse_eq`

English:
lemma inverse_eq
  statement: {f : M ->L[R] M₂} {g : M₂ ->L[R] M}
  proof: by
  have : f = ContinuousLinearEquiv.equivOfInverse' f g hf hg := rfl
  rw [this]; rw [inverse_equiv]
  rfl

中文:
引理 inverse_eq
  结论: {f : M ->L[R] M₂} {g : M₂ ->L[R] M}
  证明: by
  have : f = ContinuousLinearEquiv.equivOfInverse' f g hf hg := rfl
  rw [this]; rw [inverse_equiv]
  rfl

Depends on / 依赖: ContinuousLinearEquiv, ContinuousLinearEquiv.equivOfInverse, equivOfInverse, inverse_equiv
-/
lemma inverse_eq {f : M ->L[R] M₂} {g : M₂ ->L[R] M}
    (hf : f ∘L g = .id R M₂) (hg : g ∘L f = .id R M) :
    f.inverse = g := by
  have : f = ContinuousLinearEquiv.equivOfInverse' f g hf hg := rfl
  rw [this]; rw [inverse_equiv]
  rfl

/--
lemma `IsInvertible.inverse_apply_eq` / 引理 `IsInvertible.inverse_apply_eq`

English:
lemma IsInvertible.inverse_apply_eq
  given: {f : M ->L[R] M₂} {x : M} {y : M₂} (hf : f.IsInvertible)
  proof: by
  rcases hf with ⟨M, rfl⟩
  simp only [inverse_equiv, ContinuousLinearEquiv.coe_coe]
  exact ContinuousLinearEquiv.symm_apply_eq M

中文:
引理 IsInvertible.inverse_apply_eq
  条件: {f : M ->L[R] M₂} {x : M} {y : M₂} (hf : f.IsInvertible)
  证明: by
  rcases hf with ⟨M, rfl⟩
  simp only [inverse_equiv, ContinuousLinearEquiv.coe_coe]
  exact ContinuousLinearEquiv.symm_apply_eq M

Depends on / 依赖: ContinuousLinearEquiv, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_eq, coe_coe, inverse_equiv, symm_apply_eq
-/
lemma IsInvertible.inverse_apply_eq {f : M ->L[R] M₂} {x : M} {y : M₂} (hf : f.IsInvertible) :
    f.inverse y = x ↔ y = f x := by
  rcases hf with ⟨M, rfl⟩
  simp only [inverse_equiv, ContinuousLinearEquiv.coe_coe]
  exact ContinuousLinearEquiv.symm_apply_eq M

/--
lemma `isInvertible_equiv_comp` / 引理 `isInvertible_equiv_comp`

English:
lemma isInvertible_equiv_comp
  given: {e : M₂ ≃L[R] M₃} {f : M ->L[R] M₂}
  proof: by
  constructor
  · rintro ⟨A, hA⟩
    have : f = e.symm ∘L ((e : M₂ ->L[R] M₃) ∘L f) := by ext; simp
    rw [this]; rw [← hA]
    simp
  · rintro ⟨M, rfl⟩
    simp

中文:
引理 isInvertible_equiv_comp
  条件: {e : M₂ ≃L[R] M₃} {f : M ->L[R] M₂}
  证明: by
  constructor
  · rintro ⟨A, hA⟩
    have : f = e.symm ∘L ((e : M₂ ->L[R] M₃) ∘L f) := by ext; simp
    rw [this]; rw [← hA]
    simp
  · rintro ⟨M, rfl⟩
    simp
-/
@[simp] lemma isInvertible_equiv_comp {e : M₂ ≃L[R] M₃} {f : M ->L[R] M₂} :
    ((e : M₂ ->L[R] M₃) ∘L f).IsInvertible ↔ f.IsInvertible := by
  constructor
  · rintro ⟨A, hA⟩
    have : f = e.symm ∘L ((e : M₂ ->L[R] M₃) ∘L f) := by ext; simp
    rw [this]; rw [← hA]
    simp
  · rintro ⟨M, rfl⟩
    simp

/--
lemma `isInvertible_comp_equiv` / 引理 `isInvertible_comp_equiv`

English:
lemma isInvertible_comp_equiv
  given: {e : M₃ ≃L[R] M} {f : M ->L[R] M₂}
  proof: by
  constructor
  · rintro ⟨A, hA⟩
    have : f = (f ∘L (e : M₃ ->L[R] M)) ∘L e.symm := by ext; simp
    rw [this]; rw [← hA]
    simp
  · rintro ⟨M, rfl⟩
    simp

中文:
引理 isInvertible_comp_equiv
  条件: {e : M₃ ≃L[R] M} {f : M ->L[R] M₂}
  证明: by
  constructor
  · rintro ⟨A, hA⟩
    have : f = (f ∘L (e : M₃ ->L[R] M)) ∘L e.symm := by ext; simp
    rw [this]; rw [← hA]
    simp
  · rintro ⟨M, rfl⟩
    simp
-/
@[simp] lemma isInvertible_comp_equiv {e : M₃ ≃L[R] M} {f : M ->L[R] M₂} :
    (f ∘L (e : M₃ ->L[R] M)).IsInvertible ↔ f.IsInvertible := by
  constructor
  · rintro ⟨A, hA⟩
    have : f = (f ∘L (e : M₃ ->L[R] M)) ∘L e.symm := by ext; simp
    rw [this]; rw [← hA]
    simp
  · rintro ⟨M, rfl⟩
    simp

/--
lemma `inverse_equiv_comp` / 引理 `inverse_equiv_comp`

English:
lemma inverse_equiv_comp
  given: {e : M₂ ≃L[R] M₃} {f : M ->L[R] M₂}
  proof: by
  by_cases hf : f.IsInvertible
  · rcases hf with ⟨A, rfl⟩
    simp only [ContinuousLinearEquiv.comp_coe, inverse_equiv, ContinuousLinearEquiv.coe_inj]
    rfl
  · rw [inverse_of_not_isInvertible (by simp [hf]), inverse_of_not_isInvertible hf, zero_comp]

中文:
引理 inverse_equiv_comp
  条件: {e : M₂ ≃L[R] M₃} {f : M ->L[R] M₂}
  证明: by
  by_cases hf : f.IsInvertible
  · rcases hf with ⟨A, rfl⟩
    simp only [ContinuousLinearEquiv.comp_coe, inverse_equiv, ContinuousLinearEquiv.coe_inj]
    rfl
  · rw [inverse_of_not_isInvertible (by simp [hf]), inverse_of_not_isInvertible hf, zero_comp]
-/
@[simp] lemma inverse_equiv_comp {e : M₂ ≃L[R] M₃} {f : M ->L[R] M₂} :
    (e ∘L f).inverse = f.inverse ∘L (e.symm : M₃ ->L[R] M₂) := by
  by_cases hf : f.IsInvertible
  · rcases hf with ⟨A, rfl⟩
    simp only [ContinuousLinearEquiv.comp_coe, inverse_equiv, ContinuousLinearEquiv.coe_inj]
    rfl
  · rw [inverse_of_not_isInvertible (by simp [hf]), inverse_of_not_isInvertible hf, zero_comp]

/--
lemma `inverse_comp_equiv` / 引理 `inverse_comp_equiv`

English:
lemma inverse_comp_equiv
  given: {e : M₃ ≃L[R] M} {f : M ->L[R] M₂}
  proof: by
  by_cases hf : f.IsInvertible
  · rcases hf with ⟨A, rfl⟩
    simp only [ContinuousLinearEquiv.comp_coe, inverse_equiv, ContinuousLinearEquiv.coe_inj]
    rfl
  · rw [inverse_of_not_isInvertible (by simp [hf]), inverse_of_not_isInvertible hf, comp_zero]

中文:
引理 inverse_comp_equiv
  条件: {e : M₃ ≃L[R] M} {f : M ->L[R] M₂}
  证明: by
  by_cases hf : f.IsInvertible
  · rcases hf with ⟨A, rfl⟩
    simp only [ContinuousLinearEquiv.comp_coe, inverse_equiv, ContinuousLinearEquiv.coe_inj]
    rfl
  · rw [inverse_of_not_isInvertible (by simp [hf]), inverse_of_not_isInvertible hf, comp_zero]
-/
@[simp] lemma inverse_comp_equiv {e : M₃ ≃L[R] M} {f : M ->L[R] M₂} :
    (f ∘L e).inverse = (e.symm : M ->L[R] M₃) ∘L f.inverse := by
  by_cases hf : f.IsInvertible
  · rcases hf with ⟨A, rfl⟩
    simp only [ContinuousLinearEquiv.comp_coe, inverse_equiv, ContinuousLinearEquiv.coe_inj]
    rfl
  · rw [inverse_of_not_isInvertible (by simp [hf]), inverse_of_not_isInvertible hf, comp_zero]

/--
lemma `IsInvertible.inverse_comp_of_left` / 引理 `IsInvertible.inverse_comp_of_left`

English:
lemma IsInvertible.inverse_comp_of_left
  statement: {g : M₂ ->L[R] M₃} {f : M ->L[R] M₂}
  proof: by
  rcases hg with ⟨N, rfl⟩
  simp

中文:
引理 IsInvertible.inverse_comp_of_left
  结论: {g : M₂ ->L[R] M₃} {f : M ->L[R] M₂}
  证明: by
  rcases hg with ⟨N, rfl⟩
  simp
-/
lemma IsInvertible.inverse_comp_of_left {g : M₂ ->L[R] M₃} {f : M ->L[R] M₂}
    (hg : g.IsInvertible) : (g ∘L f).inverse = f.inverse ∘L g.inverse := by
  rcases hg with ⟨N, rfl⟩
  simp

/--
lemma `IsInvertible.inverse_comp_apply_of_left` / 引理 `IsInvertible.inverse_comp_apply_of_left`

English:
lemma IsInvertible.inverse_comp_apply_of_left
  statement: {g : M₂ ->L[R] M₃} {f : M ->L[R] M₂} {v : M₃}
  proof: by
  simp only [hg.inverse_comp_of_left, comp_apply]

中文:
引理 IsInvertible.inverse_comp_apply_of_left
  结论: {g : M₂ ->L[R] M₃} {f : M ->L[R] M₂} {v : M₃}
  证明: by
  simp only [hg.inverse_comp_of_left, comp_apply]

Depends on / 依赖: comp_apply, hg.inverse_comp_of_left, inverse_comp_of_left
-/
lemma IsInvertible.inverse_comp_apply_of_left {g : M₂ ->L[R] M₃} {f : M ->L[R] M₂} {v : M₃}
    (hg : g.IsInvertible) : (g ∘L f).inverse v = f.inverse (g.inverse v) := by
  simp only [hg.inverse_comp_of_left, comp_apply]

/--
lemma `IsInvertible.inverse_comp_of_right` / 引理 `IsInvertible.inverse_comp_of_right`

English:
lemma IsInvertible.inverse_comp_of_right
  statement: {g : M₂ ->L[R] M₃} {f : M ->L[R] M₂}
  proof: by
  rcases hf with ⟨M, rfl⟩
  simp

中文:
引理 IsInvertible.inverse_comp_of_right
  结论: {g : M₂ ->L[R] M₃} {f : M ->L[R] M₂}
  证明: by
  rcases hf with ⟨M, rfl⟩
  simp
-/
lemma IsInvertible.inverse_comp_of_right {g : M₂ ->L[R] M₃} {f : M ->L[R] M₂}
    (hf : f.IsInvertible) : (g ∘L f).inverse = f.inverse ∘L g.inverse := by
  rcases hf with ⟨M, rfl⟩
  simp

/--
lemma `IsInvertible.inverse_comp_apply_of_right` / 引理 `IsInvertible.inverse_comp_apply_of_right`

English:
lemma IsInvertible.inverse_comp_apply_of_right
  statement: {g : M₂ ->L[R] M₃} {f : M ->L[R] M₂} {v : M₃}
  proof: by
  simp only [hf.inverse_comp_of_right, comp_apply]

@[simp]

中文:
引理 IsInvertible.inverse_comp_apply_of_right
  结论: {g : M₂ ->L[R] M₃} {f : M ->L[R] M₂} {v : M₃}
  证明: by
  simp only [hf.inverse_comp_of_right, comp_apply]

@[simp]

Depends on / 依赖: comp_apply, hf.inverse_comp_of_right, inverse_comp_of_right
-/
lemma IsInvertible.inverse_comp_apply_of_right {g : M₂ ->L[R] M₃} {f : M ->L[R] M₂} {v : M₃}
    (hf : f.IsInvertible) : (g ∘L f).inverse v = f.inverse (g.inverse v) := by
  simp only [hf.inverse_comp_of_right, comp_apply]

@[simp]
/--
theorem `ringInverse_equiv` / 定理 `ringInverse_equiv`

English:
theorem ringInverse_equiv
  given: (e : M ≃L[R] M)
  statement: (↑e)⁻¹ʳ = inverse (e : M ->L[R] M)
  proof: by
  suffices ((ContinuousLinearEquiv.unitsEquiv _ _).symm e : M ->L[R] M)⁻¹ʳ = inverse ↑e by
    convert! this
  simp
  rfl

中文:
定理 ringInverse_equiv
  条件: (e : M ≃L[R] M)
  结论: (↑e)⁻¹ʳ = inverse (e : M ->L[R] M)
  证明: by
  suffices ((ContinuousLinearEquiv.unitsEquiv _ _).symm e : M ->L[R] M)⁻¹ʳ = inverse ↑e by
    convert! this
  simp
  rfl

Depends on / 依赖: ContinuousLinearEquiv, ContinuousLinearEquiv.unitsEquiv, convert, inverse, unitsEquiv
-/
theorem ringInverse_equiv (e : M ≃L[R] M) : (↑e)⁻¹ʳ = inverse (e : M ->L[R] M) := by
  suffices ((ContinuousLinearEquiv.unitsEquiv _ _).symm e : M ->L[R] M)⁻¹ʳ = inverse ↑e by
    convert! this
  simp
  rfl

/--
theorem `inverse_eq_ringInverse` / 定理 `inverse_eq_ringInverse`

English:
theorem inverse_eq_ringInverse
  given: (e : M ≃L[R] M₂) (f : M ->L[R] M₂)
  proof: by
  by_cases h₁ : f.IsInvertible
  · obtain ⟨e', he'⟩ := h₁
    rw [← he']
    change _ = (e'.trans e.symm : M ->L[R] M)⁻¹ʳ ∘L (e.symm : M₂ ->L[R] M)
    ext
    simp
  · suffices ¬IsUnit ((e.symm : M₂ ->L[R] M).comp f) by simp [this, h₁]
    contrapose h₁
    rcases h₁ with ⟨F, hF⟩
    use (ContinuousLinearEquiv.unitsEquiv _ _ F).trans e
    ext
    dsimp
    rw [hF]
    simp

中文:
定理 inverse_eq_ringInverse
  条件: (e : M ≃L[R] M₂) (f : M ->L[R] M₂)
  证明: by
  by_cases h₁ : f.IsInvertible
  · obtain ⟨e', he'⟩ := h₁
    rw [← he']
    change _ = (e'.trans e.symm : M ->L[R] M)⁻¹ʳ ∘L (e.symm : M₂ ->L[R] M)
    ext
    simp
  · suffices ¬IsUnit ((e.symm : M₂ ->L[R] M).comp f) by simp [this, h₁]
    contrapose h₁
    rcases h₁ with ⟨F, hF⟩
    use (ContinuousLinearEquiv.unitsEquiv _ _ F).trans e
    ext
    dsimp
    rw [hF]
    simp

Depends on / 依赖: ContinuousLinearEquiv, ContinuousLinearEquiv.unitsEquiv, IsInvertible, IsUnit, contrapose, e.symm, f.IsInvertible, unitsEquiv
-/
theorem inverse_eq_ringInverse (e : M ≃L[R] M₂) (f : M ->L[R] M₂) :
    inverse f = ((e.symm : M₂ ->L[R] M).comp f)⁻¹ʳ ∘L e.symm := by
  by_cases h₁ : f.IsInvertible
  · obtain ⟨e', he'⟩ := h₁
    rw [← he']
    change _ = (e'.trans e.symm : M ->L[R] M)⁻¹ʳ ∘L (e.symm : M₂ ->L[R] M)
    ext
    simp
  · suffices ¬IsUnit ((e.symm : M₂ ->L[R] M).comp f) by simp [this, h₁]
    contrapose h₁
    rcases h₁ with ⟨F, hF⟩
    use (ContinuousLinearEquiv.unitsEquiv _ _ F).trans e
    ext
    dsimp
    rw [hF]
    simp

/--
theorem `ringInverse_eq_inverse` / 定理 `ringInverse_eq_inverse`

English:
theorem ringInverse_eq_inverse
  statement: Ring.inverse = inverse (R := R) (M := M)
  proof: by
  ext
  simp [inverse_eq_ringInverse (ContinuousLinearEquiv.refl R M)]

中文:
定理 ringInverse_eq_inverse
  结论: 环.inverse = inverse (R := R) (M := M)
  证明: by
  ext
  simp [inverse_eq_ringInverse (ContinuousLinearEquiv.refl R M)]

Depends on / 依赖: ContinuousLinearEquiv, ContinuousLinearEquiv.refl, inverse_eq_ringInverse
-/
theorem ringInverse_eq_inverse : Ring.inverse = inverse (R := R) (M := M) := by
  ext
  simp [inverse_eq_ringInverse (ContinuousLinearEquiv.refl R M)]

/--
theorem `inverse_id` / 定理 `inverse_id`

English:
theorem inverse_id
  statement: (ContinuousLinearMap.id R M).inverse = .id R M
  proof: by
  rw [← ringInverse_eq_inverse]
  exact Ring.inverse_one _

中文:
定理 inverse_id
  结论: (连续线性映射.id R M).inverse = .id R M
  证明: by
  rw [← ringInverse_eq_inverse]
  exact Ring.inverse_one _
-/
@[simp] theorem inverse_id : (ContinuousLinearMap.id R M).inverse = .id R M := by
  rw [← ringInverse_eq_inverse]
  exact Ring.inverse_one _

namespace IsInvertible

variable {f : M ->L[R] M₂}

@[simp]
/--
theorem `self_comp_inverse` / 定理 `self_comp_inverse`

English:
theorem self_comp_inverse
  given: (hf : f.IsInvertible)
  statement: f ∘L f.inverse = .id _ _
  proof: by
  rcases hf with ⟨e, rfl⟩
  simp

@[simp]

中文:
定理 self_comp_inverse
  条件: (hf : f.IsInvertible)
  结论: f ∘L f.inverse = .id _ _
  证明: by
  rcases hf with ⟨e, rfl⟩
  simp

@[simp]
-/
theorem self_comp_inverse (hf : f.IsInvertible) : f ∘L f.inverse = .id _ _ := by
  rcases hf with ⟨e, rfl⟩
  simp

@[simp]
/--
theorem `self_apply_inverse` / 定理 `self_apply_inverse`

English:
theorem self_apply_inverse
  given: (hf : f.IsInvertible) (y : M₂)
  statement: f (f.inverse y) = y
  proof: by
  rcases hf with ⟨e, rfl⟩
  simp

@[simp]

中文:
定理 self_apply_inverse
  条件: (hf : f.IsInvertible) (y : M₂)
  结论: f (f.inverse y) = y
  证明: by
  rcases hf with ⟨e, rfl⟩
  simp

@[simp]
-/
theorem self_apply_inverse (hf : f.IsInvertible) (y : M₂) : f (f.inverse y) = y := by
  rcases hf with ⟨e, rfl⟩
  simp

@[simp]
/--
theorem `inverse_comp_self` / 定理 `inverse_comp_self`

English:
theorem inverse_comp_self
  given: (hf : f.IsInvertible)
  statement: f.inverse ∘L f = .id _ _
  proof: by
  rcases hf with ⟨e, rfl⟩
  simp

@[simp]

中文:
定理 inverse_comp_self
  条件: (hf : f.IsInvertible)
  结论: f.inverse ∘L f = .id _ _
  证明: by
  rcases hf with ⟨e, rfl⟩
  simp

@[simp]
-/
theorem inverse_comp_self (hf : f.IsInvertible) : f.inverse ∘L f = .id _ _ := by
  rcases hf with ⟨e, rfl⟩
  simp

@[simp]
/--
theorem `inverse_apply_self` / 定理 `inverse_apply_self`

English:
theorem inverse_apply_self
  given: (hf : f.IsInvertible) (y : M)
  statement: f.inverse (f y) = y
  proof: by
  rcases hf with ⟨e, rfl⟩
  simp

中文:
定理 inverse_apply_self
  条件: (hf : f.IsInvertible) (y : M)
  结论: f.inverse (f y) = y
  证明: by
  rcases hf with ⟨e, rfl⟩
  simp
-/
theorem inverse_apply_self (hf : f.IsInvertible) (y : M) : f.inverse (f y) = y := by
  rcases hf with ⟨e, rfl⟩
  simp

/--
theorem `bijective` / 定理 `bijective`

English:
theorem bijective
  given: (hf : f.IsInvertible)
  statement: Function.Bijective f
  proof: by
  rcases hf with ⟨e, rfl⟩
  simp [ContinuousLinearEquiv.bijective]

中文:
定理 bijective
  条件: (hf : f.IsInvertible)
  结论: 函数.双射 f
  证明: by
  rcases hf with ⟨e, rfl⟩
  simp [ContinuousLinearEquiv.bijective]
-/
protected theorem bijective (hf : f.IsInvertible) : Function.Bijective f := by
  rcases hf with ⟨e, rfl⟩
  simp [ContinuousLinearEquiv.bijective]

/--
theorem `injective` / 定理 `injective`

English:
theorem injective
  given: (hf : f.IsInvertible)
  statement: Function.Injective f
  proof: hf.bijective.injective

中文:
定理 injective
  条件: (hf : f.IsInvertible)
  结论: 函数.单射 f
  证明: hf.bijective.injective
-/
protected theorem injective (hf : f.IsInvertible) : Function.Injective f :=
  hf.bijective.injective

/--
theorem `surjective` / 定理 `surjective`

English:
theorem surjective
  given: (hf : f.IsInvertible)
  statement: Function.Surjective f
  proof: hf.bijective.surjective

中文:
定理 surjective
  条件: (hf : f.IsInvertible)
  结论: 函数.满射 f
  证明: hf.bijective.surjective
-/
protected theorem surjective (hf : f.IsInvertible) : Function.Surjective f :=
  hf.bijective.surjective

/--
theorem `inverse` / 定理 `inverse`

English:
theorem inverse
  given: (hf : f.IsInvertible)
  statement: f.inverse.IsInvertible
  proof: by
  rcases hf with ⟨e, rfl⟩
  simp

@[simp]

中文:
定理 inverse
  条件: (hf : f.IsInvertible)
  结论: f.inverse.IsInvertible
  证明: by
  rcases hf with ⟨e, rfl⟩
  simp

@[simp]
-/
protected theorem inverse (hf : f.IsInvertible) : f.inverse.IsInvertible := by
  rcases hf with ⟨e, rfl⟩
  simp

@[simp]
/--
theorem `inverse_inverse` / 定理 `inverse_inverse`

English:
theorem inverse_inverse
  given: (hf : f.IsInvertible)
  statement: f.inverse.inverse = f
  proof: by
  rcases hf with ⟨e, rfl⟩
  simp

中文:
定理 inverse_inverse
  条件: (hf : f.IsInvertible)
  结论: f.inverse.inverse = f
  证明: by
  rcases hf with ⟨e, rfl⟩
  simp
-/
protected theorem inverse_inverse (hf : f.IsInvertible) : f.inverse.inverse = f := by
  rcases hf with ⟨e, rfl⟩
  simp

/--
theorem `of_isInvertible_inverse` / 定理 `of_isInvertible_inverse`

English:
theorem of_isInvertible_inverse
  given: (hf : f.inverse.IsInvertible)
  statement: f.IsInvertible
  proof: by
  by_contra H
  obtain ⟨_, _⟩ : Subsingleton M₂ ∧ Subsingleton M := by simpa [inverse, H] using hf
  simp_all [Subsingleton.elim f 0]

@[simp]

中文:
定理 of_isInvertible_inverse
  条件: (hf : f.inverse.IsInvertible)
  结论: f.IsInvertible
  证明: by
  by_contra H
  obtain ⟨_, _⟩ : Subsingleton M₂ ∧ Subsingleton M := by simpa [inverse, H] using hf
  simp_all [Subsingleton.elim f 0]

@[simp]
-/
protected theorem of_isInvertible_inverse (hf : f.inverse.IsInvertible) : f.IsInvertible := by
  by_contra H
  obtain ⟨_, _⟩ : Subsingleton M₂ ∧ Subsingleton M := by simpa [inverse, H] using hf
  simp_all [Subsingleton.elim f 0]

@[simp]
/--
theorem `_root_.ContinuousLinearMap.isInvertible_inverse_iff` / 定理 `_root_.ContinuousLinearMap.isInvertible_inverse_iff`

English:
theorem _root_.ContinuousLinearMap.isInvertible_inverse_iff
  proof: ⟨.of_isInvertible_inverse, .inverse⟩

中文:
定理 _root_.连续线性映射.isInvertible_inverse_iff
  证明: ⟨.of_isInvertible_inverse, .inverse⟩

Depends on / 依赖: inverse, of_isInvertible_inverse
-/
theorem _root_.ContinuousLinearMap.isInvertible_inverse_iff :
    f.inverse.IsInvertible ↔ f.IsInvertible :=
  ⟨.of_isInvertible_inverse, .inverse⟩

end IsInvertible

/--
theorem `coprod_comp_prodComm` / 定理 `coprod_comp_prodComm`

English:
theorem coprod_comp_prodComm
  given: [ContinuousAdd M] (f : M₂ ->L[R] M) (g : M₃ ->L[R] M)
  proof: by
  ext <;> simp

中文:
定理 coprod_comp_prodComm
  条件: [连续加法 M] (f : M₂ ->L[R] M) (g : M₃ ->L[R] M)
  证明: by
  ext <;> simp
-/
theorem coprod_comp_prodComm [ContinuousAdd M] (f : M₂ ->L[R] M) (g : M₃ ->L[R] M) :
    f.coprod g ∘L ContinuousLinearEquiv.prodComm R M₃ M₂ = g.coprod f := by
  ext <;> simp

end ContinuousLinearMap

-- Restricting a continuous linear equivalence to a map between submodules.
section map

namespace ContinuousLinearEquiv

variable {R R₂ M M₂ : Type*} [Semiring R] [Semiring R₂] [AddCommMonoid M] [TopologicalSpace M]
  [AddCommMonoid M₂] [TopologicalSpace M₂]
  {module_M : Module R M} {module_M₂ : Module R₂ M₂} {σ₁₂ : R ->+* R₂} {σ₂₁ : R₂ ->+* R}
  {re₁₂ : RingHomInvPair σ₁₂ σ₂₁} {re₂₁ : RingHomInvPair σ₂₁ σ₁₂}

/--
Definition of `ofEq` / `ofEq` 的定义

English:
definition ofEq
  signature: (p q : Submodule R M) (h : p = q)
  body: LinearEquiv.ofEq _ _ h
  continuous_toFun := by
    have h' : (fun x => x in p) = (fun x => x in q) := by simp [h]
    exact (Homeomorph.ofEqSubtypes h').continuous
  continuous_invFun := by
    have h' : (fun x => x in p) = (fun x => x in q) := by simp [h]
    exact (Homeomorph.ofEqSubtypes h').symm.continuous

中文:
定义 ofEq
  签名: (p q : 子模 R M) (h : p = q)
  定义体: LinearEquiv.ofEq _ _ h
  continuous_toFun := by
    have h' : (fun x => x in p) = (fun x => x in q) := by simp [h]
    exact (Homeomorph.ofEqSubtypes h').continuous
  continuous_invFun := by
    have h' : (fun x => x in p) = (fun x => x in q) := by simp [h]
    exact (Homeomorph.ofEqSubtypes h').symm.continuous

Depends on / 依赖: LinearEquiv, LinearEquiv.ofEq
-/
def ofEq (p q : Submodule R M) (h : p = q) : p ≃L[R] q where
  toLinearEquiv := LinearEquiv.ofEq _ _ h
  continuous_toFun := by
    have h' : (fun x => x in p) = (fun x => x in q) := by simp [h]
    exact (Homeomorph.ofEqSubtypes h').continuous
  continuous_invFun := by
    have h' : (fun x => x in p) = (fun x => x in q) := by simp [h]
    exact (Homeomorph.ofEqSubtypes h').symm.continuous

/--
Definition of `submoduleMap` / `submoduleMap` 的定义

English:
definition submoduleMap
  signature: (e : M ≃SL[σ₁₂] M₂) (p : Submodule R M)
  body: LinearEquiv.submoduleMap e.toLinearEquiv p
  continuous_toFun := map_continuous ((e.toContinuousLinearMap.comp p.subtypeL).codRestrict _ _)
  continuous_invFun := (map_continuous e.symm).restrict fun x hx =>
    ((LinearEquiv.submoduleMap e.toLinearEquiv p).symm ⟨x, hx⟩).2

@[simp]

中文:
定义 submoduleMap
  签名: (e : M ≃SL[σ₁₂] M₂) (p : 子模 R M)
  定义体: LinearEquiv.submoduleMap e.toLinearEquiv p
  continuous_toFun := map_continuous ((e.toContinuousLinearMap.comp p.subtypeL).codRestrict _ _)
  continuous_invFun := (map_continuous e.symm).restrict fun x hx =>
    ((LinearEquiv.submoduleMap e.toLinearEquiv p).symm ⟨x, hx⟩).2

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.submoduleMap, e.toLinearEquiv, submoduleMap, toLinearEquiv
-/
def submoduleMap (e : M ≃SL[σ₁₂] M₂) (p : Submodule R M) :
    p ≃SL[σ₁₂] Submodule.map (e : M ->ₛₗ[σ₁₂] M₂) p where
  __ := LinearEquiv.submoduleMap e.toLinearEquiv p
  continuous_toFun := map_continuous ((e.toContinuousLinearMap.comp p.subtypeL).codRestrict _ _)
  continuous_invFun := (map_continuous e.symm).restrict fun x hx =>
    ((LinearEquiv.submoduleMap e.toLinearEquiv p).symm ⟨x, hx⟩).2

@[simp]
/--
lemma `submoduleMap_apply` / 引理 `submoduleMap_apply`

English:
lemma submoduleMap_apply
  given: (e : M ≃SL[σ₁₂] M₂) (p : Submodule R M) (x : p)
  proof: by
  rfl

@[simp]

中文:
引理 submoduleMap_apply
  条件: (e : M ≃SL[σ₁₂] M₂) (p : 子模 R M) (x : p)
  证明: by
  rfl

@[simp]
-/
lemma submoduleMap_apply (e : M ≃SL[σ₁₂] M₂) (p : Submodule R M) (x : p) :
    e.submoduleMap p x = e x := by
  rfl

@[simp]
/--
lemma `submoduleMap_symm_apply` / 引理 `submoduleMap_symm_apply`

English:
lemma submoduleMap_symm_apply
  statement: (e : M ≃SL[σ₁₂] M₂) (p : Submodule R M)
  proof: by
  rfl

中文:
引理 submoduleMap_symm_apply
  结论: (e : M ≃SL[σ₁₂] M₂) (p : 子模 R M)
  证明: by
  rfl
-/
lemma submoduleMap_symm_apply (e : M ≃SL[σ₁₂] M₂) (p : Submodule R M)
    (x : p.map (e : M ->ₛₗ[σ₁₂] M₂)) :
    (e.submoduleMap p).symm x = e.symm x := by
  rfl

/--
Definition of `ofSubmodules` / `ofSubmodules` 的定义

English:
definition ofSubmodules
  signature: (e : M ≃SL[σ₁₂] M₂)
  body: (e.submoduleMap p).trans (.ofEq _ _ h)

@[simp]

中文:
定义 ofSubmodules
  签名: (e : M ≃SL[σ₁₂] M₂)
  定义体: (e.submoduleMap p).trans (.ofEq _ _ h)

@[simp]

Depends on / 依赖: e.submoduleMap, submoduleMap
-/
def ofSubmodules (e : M ≃SL[σ₁₂] M₂)
    (p : Submodule R M) (q : Submodule R₂ M₂) (h : p.map (e : M ->ₛₗ[σ₁₂] M₂) = q) : p ≃SL[σ₁₂] q :=
  (e.submoduleMap p).trans (.ofEq _ _ h)

@[simp]
/--
theorem `ofSubmodules_apply` / 定理 `ofSubmodules_apply`

English:
theorem ofSubmodules_apply
  statement: (e : M ≃SL[σ₁₂] M₂) {p : Submodule R M} {q : Submodule R₂ M₂}
  proof: rfl

@[simp]

中文:
定理 ofSubmodules_apply
  结论: (e : M ≃SL[σ₁₂] M₂) {p : 子模 R M} {q : 子模 R₂ M₂}
  证明: rfl

@[simp]
-/
theorem ofSubmodules_apply (e : M ≃SL[σ₁₂] M₂) {p : Submodule R M} {q : Submodule R₂ M₂}
    (h : p.map (e : M ->ₛₗ[σ₁₂] M₂) = q) (x : p) :
    e.ofSubmodules p q h x = e x :=
  rfl

@[simp]
/--
theorem `ofSubmodules_symm_apply` / 定理 `ofSubmodules_symm_apply`

English:
theorem ofSubmodules_symm_apply
  statement: (e : M ≃SL[σ₁₂] M₂) {p : Submodule R M} {q : Submodule R₂ M₂}
  proof: rfl

中文:
定理 ofSubmodules_symm_apply
  结论: (e : M ≃SL[σ₁₂] M₂) {p : 子模 R M} {q : 子模 R₂ M₂}
  证明: rfl
-/
theorem ofSubmodules_symm_apply (e : M ≃SL[σ₁₂] M₂) {p : Submodule R M} {q : Submodule R₂ M₂}
    (h : p.map (e : M ->ₛₗ[σ₁₂] M₂) = q) (x : q) : (e.ofSubmodules p q h).symm x = e.symm x :=
  rfl

/--
Definition of `ofSubmodule'` / `ofSubmodule'` 的定义

English:
definition ofSubmodule'
  signature: (f : M ≃SL[σ₁₂] M₂) (U : Submodule R₂ M₂)
  body: .symm f.symm.ofSubmodules _ _ (U.map_equiv_eq_comap_symm f.toLinearEquiv.symm)

中文:
定义 ofSubmodule'
  签名: (f : M ≃SL[σ₁₂] M₂) (U : 子模 R₂ M₂)
  定义体: .symm f.symm.ofSubmodules _ _ (U.map_equiv_eq_comap_symm f.toLinearEquiv.symm)

Depends on / 依赖: U.map_equiv_eq_comap_symm, f.symm.ofSubmodules, f.toLinearEquiv.symm, map_equiv_eq_comap_symm, ofSubmodules, toLinearEquiv
-/
def ofSubmodule' (f : M ≃SL[σ₁₂] M₂) (U : Submodule R₂ M₂) :
    U.comap (f : M ->ₛₗ[σ₁₂] M₂) ≃SL[σ₁₂] U :=
.symm f.symm.ofSubmodules _ _ (U.map_equiv_eq_comap_symm f.toLinearEquiv.symm)

/--
theorem `ofSubmodule'_toContinuousLinearMap` / 定理 `ofSubmodule'_toContinuousLinearMap`

English:
theorem ofSubmodule'_toContinuousLinearMap
  given: (f : M ≃SL[σ₁₂] M₂) (U : Submodule R₂ M₂)
  proof: by
  rfl

@[simp]

中文:
定理 ofSubmodule'_toContinuousLinearMap
  条件: (f : M ≃SL[σ₁₂] M₂) (U : 子模 R₂ M₂)
  证明: by
  rfl

@[simp]
-/
theorem ofSubmodule'_toContinuousLinearMap (f : M ≃SL[σ₁₂] M₂) (U : Submodule R₂ M₂) :
    (f.ofSubmodule' U).toContinuousLinearMap =
      (f.toContinuousLinearMap.comp ((U.comap f.toLinearMap).subtypeL)).codRestrict U
        ((fun ⟨x, hx⟩ => by simpa [Submodule.mem_comap])) := by
  rfl

@[simp]
/--
theorem `ofSubmodule'_apply` / 定理 `ofSubmodule'_apply`

English:
theorem ofSubmodule'_apply
  statement: (f : M ≃SL[σ₁₂] M₂) (U : Submodule R₂ M₂)
  proof: rfl

@[simp]

中文:
定理 ofSubmodule'_apply
  结论: (f : M ≃SL[σ₁₂] M₂) (U : 子模 R₂ M₂)
  证明: rfl

@[simp]
-/
theorem ofSubmodule'_apply (f : M ≃SL[σ₁₂] M₂) (U : Submodule R₂ M₂)
    (x : U.comap (f : M ->ₛₗ[σ₁₂] M₂)) :
    (f.ofSubmodule' U x : M₂) = f (x : M) :=
  rfl

@[simp]
/--
theorem `ofSubmodule'_symm_apply` / 定理 `ofSubmodule'_symm_apply`

English:
theorem ofSubmodule'_symm_apply
  given: (f : M ≃SL[σ₁₂] M₂) (U : Submodule R₂ M₂) (x : U)
  proof: rfl

中文:
定理 ofSubmodule'_symm_apply
  条件: (f : M ≃SL[σ₁₂] M₂) (U : 子模 R₂ M₂) (x : U)
  证明: rfl
-/
theorem ofSubmodule'_symm_apply (f : M ≃SL[σ₁₂] M₂) (U : Submodule R₂ M₂) (x : U) :
    ((f.ofSubmodule' U).symm x : M) = f.symm (x : M₂) := rfl

end ContinuousLinearEquiv

/--
Definition of `_root_.Submodule.topContEquiv` / `_root_.Submodule.topContEquiv` 的定义

English:
abbreviation _root_.Submodule.topContEquiv
  signature: {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  body: Submodule.topEquiv

中文:
缩写 _root_.子模.topContEquiv
  签名: {R M : 类型} [半环 R] [加法交换幺半群 M] [模 R M]
  定义体: Submodule.topEquiv

Depends on / 依赖: Submodule, Submodule.topEquiv, topEquiv
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
/--
Definition of `opContinuousLinearEquiv` / `opContinuousLinearEquiv` 的定义

English:
definition opContinuousLinearEquiv
  signature: : M ≃L[R] Mᵐᵒᵖ where
  body: MulOpposite.opLinearEquiv R

中文:
定义 opContinuousLinearEquiv
  签名: : M ≃L[R] Mᵐᵒᵖ where
  定义体: MulOpposite.opLinearEquiv R

Depends on / 依赖: MulOpposite, MulOpposite.opLinearEquiv, opLinearEquiv
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

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul Sˣ (V ≃L[R] W)
  body: { __ := α • e.toLinearEquiv
    continuous_toFun := α.isUnit.continuous_const_smul_iff.mpr e.continuous
    continuous_invFun := α⁻¹.isUnit.continuous_const_smul_iff.mpr e.symm.continuous }

中文:
实例 :
  签名: 标量乘法 Sˣ (V ≃L[R] W)
  定义体: { __ := α • e.toLinearEquiv
    continuous_toFun := α.isUnit.continuous_const_smul_iff.mpr e.continuous
    continuous_invFun := α⁻¹.isUnit.continuous_const_smul_iff.mpr e.symm.continuous }

Depends on / 依赖: continuous, continuous_const_smul_iff, continuous_invFun, continuous_toFun, e.continuous, e.symm.continuous, e.toLinearEquiv, isUnit, isUnit.continuous_const_smul_iff.mpr, toLinearEquiv
-/
instance : SMul Sˣ (V ≃L[R] W) where smul α e :=
  { __ := α • e.toLinearEquiv
    continuous_toFun := α.isUnit.continuous_const_smul_iff.mpr e.continuous
    continuous_invFun := α⁻¹.isUnit.continuous_const_smul_iff.mpr e.symm.continuous }

/--
theorem `smul_apply` / 定理 `smul_apply`

English:
theorem smul_apply
  given: (α : Sˣ) (e : V ≃L[R] W) (x : V)
  statement: (α • e) x = (α : S) • e x
  proof: rfl

中文:
定理 smul_apply
  条件: (α : Sˣ) (e : V ≃L[R] W) (x : V)
  结论: (α • e) x = (α : S) • e x
  证明: rfl
-/
@[simp] theorem smul_apply (α : Sˣ) (e : V ≃L[R] W) (x : V) : (α • e) x = (α : S) • e x := rfl

/--
theorem `symm_smul_apply` / 定理 `symm_smul_apply`

English:
theorem symm_smul_apply
  given: (e : V ≃L[R] W) (α : Sˣ) (x : W)
  proof: rfl

中文:
定理 symm_smul_apply
  条件: (e : V ≃L[R] W) (α : Sˣ) (x : W)
  证明: rfl
-/
theorem symm_smul_apply (e : V ≃L[R] W) (α : Sˣ) (x : W) :
    (α • e).symm x = (↑α⁻¹ : S) • e.symm x := rfl

/--
theorem `symm_smul` / 定理 `symm_smul`

English:
theorem symm_smul
  statement: [SMulCommClass R S V]
  proof: rfl

中文:
定理 symm_smul
  结论: [标量交换类 R S V]
  证明: rfl
-/
@[simp] theorem symm_smul [SMulCommClass R S V]
    (e : V ≃L[R] W) (α : Sˣ) : (α • e).symm = α⁻¹ • e.symm := rfl

/--
theorem `toLinearEquiv_smul` / 定理 `toLinearEquiv_smul`

English:
theorem toLinearEquiv_smul
  given: (e : V ≃L[R] W) (α : Sˣ)
  proof: rfl

中文:
定理 toLinearEquiv_smul
  条件: (e : V ≃L[R] W) (α : Sˣ)
  证明: rfl
-/
@[simp] theorem toLinearEquiv_smul (e : V ≃L[R] W) (α : Sˣ) :
    (α • e).toLinearEquiv = α • e.toLinearEquiv := rfl

/--
theorem `smul_trans` / 定理 `smul_trans`

English:
theorem smul_trans
  statement: [SMulCommClass R S V] [IsScalarTower S R G] (α : Sˣ) (e : G ≃L[R] V)
  proof: by
  ext; simp [LinearMapClass.map_smul_of_tower f]

中文:
定理 smul_trans
  结论: [标量交换类 R S V] [标量塔 S R G] (α : Sˣ) (e : G ≃L[R] V)
  证明: by
  ext; simp [LinearMapClass.map_smul_of_tower f]

Depends on / 依赖: LinearMapClass, LinearMapClass.map_smul_of_tower, map_smul_of_tower
-/
theorem smul_trans [SMulCommClass R S V] [IsScalarTower S R G] (α : Sˣ) (e : G ≃L[R] V)
    (f : V ≃L[R] W) : (α • e).trans f = α • (e.trans f) := by
  ext; simp [LinearMapClass.map_smul_of_tower f]

/--
theorem `trans_smul` / 定理 `trans_smul`

English:
theorem trans_smul
  given: [IsScalarTower S R G] (α : Sˣ) (e : G ≃L[R] V) (f : V ≃L[R] W)
  proof: by ext; simp

中文:
定理 trans_smul
  条件: [标量塔 S R G] (α : Sˣ) (e : G ≃L[R] V) (f : V ≃L[R] W)
  证明: by ext; simp
-/
theorem trans_smul [IsScalarTower S R G] (α : Sˣ) (e : G ≃L[R] V) (f : V ≃L[R] W) :
    e.trans (α • f) = α • (e.trans f) := by ext; simp

section IsHomeomorph

variable {S₁ M M₁ : Type*} [Semiring S₁] {σ : S ->+* S₁} {σ' : S₁ ->+* S}
  [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] [TopologicalSpace M] [AddCommMonoid M] [Module S M]
  [TopologicalSpace M₁] [AddCommMonoid M₁] [Module S₁ M₁]

/--
Definition of `ofIsHomeomorph` / `ofIsHomeomorph` 的定义

English:
definition ofIsHomeomorph
  signature: (f : M ≃ₛₗ[σ] M₁) (hf : IsHomeomorph f)
  body: f
  continuous_toFun := hf.continuous
  continuous_invFun := (f.isHomeomorph_iff.mp hf).2

中文:
定义 ofIsHomeomorph
  签名: (f : M ≃ₛₗ[σ] M₁) (hf : 是同胚 f)
  定义体: f
  continuous_toFun := hf.continuous
  continuous_invFun := (f.isHomeomorph_iff.mp hf).2
-/
def ofIsHomeomorph (f : M ≃ₛₗ[σ] M₁) (hf : IsHomeomorph f) : M ≃SL[σ] M₁ where
  __ := f
  continuous_toFun := hf.continuous
  continuous_invFun := (f.isHomeomorph_iff.mp hf).2

/--
theorem `isHomeomorph` / 定理 `isHomeomorph`

English:
theorem isHomeomorph
  given: (f : M ≃SL[σ] M₁)
  statement: IsHomeomorph f
  proof: ⟨f.continuous, isOpenMap f, f.bijective⟩

中文:
定理 isHomeomorph
  条件: (f : M ≃SL[σ] M₁)
  结论: 是同胚 f
  证明: ⟨f.continuous, isOpenMap f, f.bijective⟩

Depends on / 依赖: bijective, continuous, f.bijective, f.continuous, isOpenMap
-/
theorem isHomeomorph (f : M ≃SL[σ] M₁) : IsHomeomorph f := ⟨f.continuous, isOpenMap f, f.bijective⟩

variable {f : M ≃ₛₗ[σ] M₁} (hf : IsHomeomorph f)

@[simp]
/--
lemma `toLinearquiv_ofIsHomeomorph` / 引理 `toLinearquiv_ofIsHomeomorph`

English:
lemma toLinearquiv_ofIsHomeomorph
  statement: (ofIsHomeomorph f hf).toLinearEquiv = f
  proof: by
  dsimp only [ofIsHomeomorph]

@[simp]

中文:
引理 toLinearquiv_ofIsHomeomorph
  结论: (ofIsHomeomorph f hf).toLinearEquiv = f
  证明: by
  dsimp only [ofIsHomeomorph]

@[simp]

Depends on / 依赖: ofIsHomeomorph
-/
lemma toLinearquiv_ofIsHomeomorph : (ofIsHomeomorph f hf).toLinearEquiv = f := by
  dsimp only [ofIsHomeomorph]

@[simp]
/--
lemma `coe_ofIsHomeomorph` / 引理 `coe_ofIsHomeomorph`

English:
lemma coe_ofIsHomeomorph
  statement: (ofIsHomeomorph f hf : M -> M₁) = f
  proof: by dsimp [ofIsHomeomorph]

中文:
引理 coe_ofIsHomeomorph
  结论: (ofIsHomeomorph f hf : M -> M₁) = f
  证明: by dsimp [ofIsHomeomorph]

Depends on / 依赖: ofIsHomeomorph
-/
lemma coe_ofIsHomeomorph : (ofIsHomeomorph f hf : M -> M₁) = f := by dsimp [ofIsHomeomorph]

/--
theorem `_root_.LinearEquiv.isHomeomorph_iff` / 定理 `_root_.LinearEquiv.isHomeomorph_iff`

English:
theorem _root_.LinearEquiv.isHomeomorph_iff
  given: (e : M ≃ₛₗ[σ] M₁)
  proof: e.toEquiv.isHomeomorph_iff

中文:
定理 _root_.线性等价.isHomeomorph_iff
  条件: (e : M ≃ₛₗ[σ] M₁)
  证明: e.toEquiv.isHomeomorph_iff

Depends on / 依赖: e.toEquiv.isHomeomorph_iff, isHomeomorph_iff, toEquiv
-/
theorem _root_.LinearEquiv.isHomeomorph_iff (e : M ≃ₛₗ[σ] M₁) :
    IsHomeomorph e ↔ Continuous e ∧ Continuous e.symm := e.toEquiv.isHomeomorph_iff

end IsHomeomorph

end ContinuousLinearEquiv
