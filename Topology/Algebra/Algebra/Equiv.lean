/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.Topology.Algebra.Algebra
public import Mathlib.Topology.Algebra.Module.Equiv

/-!
# Isomorphisms of topological algebras

This file contains an API for `ContinuousAlgEquiv R A B`, the type of
continuous `R`-algebra isomorphisms with continuous inverses. Here `R` is a
commutative (semi)ring, and `A` and `B` are `R`-algebras with topologies.

## Main definitions

Let `R` be a commutative semiring and let `A` and `B` be `R`-algebras which
are also topological spaces.

* `ContinuousAlgEquiv R A B`: the type of continuous `R`-algebra isomorphisms
  from `A` to `B` with continuous inverses.

## Notation

`A ≃A[R] B` : notation for `ContinuousAlgEquiv R A B`.

## Tags

* continuous, isomorphism, algebra
-/

@[expose] public section

open scoped Topology


/--
Definition of `ContinuousAlgEquiv` / `ContinuousAlgEquiv` 的定义

English:
structure ContinuousAlgEquiv
  parameters: (R A B : Type*) [CommSemiring R]
  extends: A ≃ₐ[R] B, A ≃ₜ B
  (no additional axioms)

中文:
结构 余ntinuousAlg等价
  参数: (R A B : 类型) [交换半环 R]
  继承: A ≃ₐ[R] B, A ≃ₜ B
  (无附加公理)
-/
structure ContinuousAlgEquiv (R A B : Type*) [CommSemiring R]
    [Semiring A] [TopologicalSpace A] [Semiring B] [TopologicalSpace B] [Algebra R A]
    [Algebra R B] extends A ≃ₐ[R] B, A ≃ₜ B

@[inherit_doc]
notation:50 A " ≃A[" R "] " B => ContinuousAlgEquiv R A B

attribute [nolint docBlame] ContinuousAlgEquiv.toHomeomorph

/--
Definition of `ContinuousAlgEquivClass` / `ContinuousAlgEquivClass` 的定义

English:
class ContinuousAlgEquivClass
  parameters: (F : Type*) (R A B : outParam Type*) [CommSemiring R]
  extends: AlgEquivClass F R A B, HomeomorphClass F A B
  (no additional axioms)

中文:
类 余ntinuousAlg等价类
  参数: (F : 类型) (R A B : outParam 类型) [交换半环 R]
  继承: 代数等价类 F R A B, 同胚类 F A B
  (无附加公理)
-/
class ContinuousAlgEquivClass (F : Type*) (R A B : outParam Type*) [CommSemiring R]
    [Semiring A] [TopologicalSpace A] [Semiring B] [TopologicalSpace B]
    [Algebra R A] [Algebra R B] [EquivLike F A B] : Prop
    extends AlgEquivClass F R A B, HomeomorphClass F A B

namespace ContinuousAlgEquiv

variable {R A B C : Type*}
  [CommSemiring R] [Semiring A] [TopologicalSpace A] [Semiring B]
  [TopologicalSpace B] [Semiring C] [TopologicalSpace C] [Algebra R A] [Algebra R B]
  [Algebra R C]

/-- The natural coercion from a continuous algebra isomorphism to a continuous
algebra morphism. -/
@[coe]
/--
Definition of `toContinuousAlgHom` / `toContinuousAlgHom` 的定义

English:
definition toContinuousAlgHom
  signature: (e : A ≃A[R] B)
  body: e.toAlgHom
  cont := e.continuous_toFun

中文:
定义 toContinuousAlgHom
  签名: (e : A ≃A[R] B)
  定义体: e.toAlgHom
  cont := e.continuous_toFun

Depends on / 依赖: e.toAlgHom, toAlgHom
-/
def toContinuousAlgHom (e : A ≃A[R] B) : A ->A[R] B where
  __ := e.toAlgHom
  cont := e.continuous_toFun

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeOut (A ≃A[R] B) (A ->A[R] B)
  body: toContinuousAlgHom

中文:
实例 :
  签名: CoeOut (A ≃A[R] B) (A ->A[R] B)
  定义体: toContinuousAlgHom

Depends on / 依赖: toContinuousAlgHom
-/
instance : CoeOut (A ≃A[R] B) (A ->A[R] B) where coe := toContinuousAlgHom
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeOut (A ≃A[R] B) (A ≃ₐ[R] B)
  body: toAlgEquiv

中文:
实例 :
  签名: CoeOut (A ≃A[R] B) (A ≃ₐ[R] B)
  定义体: toAlgEquiv

Depends on / 依赖: toAlgEquiv
-/
instance : CoeOut (A ≃A[R] B) (A ≃ₐ[R] B) where coe := toAlgEquiv

/--
Instance `equivLike` / 实例 `equivLike`

English:
instance equivLike
  signature: : EquivLike (A ≃A[R] B) A B where
  body: f.toFun
  inv f := f.invFun
  coe_injective' f g h₁ h₂ := by
    obtain ⟨f', _⟩ := f
    obtain ⟨g', _⟩ := g
    rcases f' with ⟨⟨_, _⟩, _⟩
    rcases g' with ⟨⟨_, _⟩, _⟩
    congr
  left_inv f := f.left_inv
  right_inv f := f.right_inv

中文:
实例 equivLike
  签名: : 等价状 (A ≃A[R] B) A B where
  定义体: f.toFun
  inv f := f.invFun
  coe_injective' f g h₁ h₂ := by
    obtain ⟨f', _⟩ := f
    obtain ⟨g', _⟩ := g
    rcases f' with ⟨⟨_, _⟩, _⟩
    rcases g' with ⟨⟨_, _⟩, _⟩
    congr
  left_inv f := f.left_inv
  right_inv f := f.right_inv

Depends on / 依赖: f.toFun
-/
instance equivLike : EquivLike (A ≃A[R] B) A B where
  coe f := f.toFun
  inv f := f.invFun
  coe_injective' f g h₁ h₂ := by
    obtain ⟨f', _⟩ := f
    obtain ⟨g', _⟩ := g
    rcases f' with ⟨⟨_, _⟩, _⟩
    rcases g' with ⟨⟨_, _⟩, _⟩
    congr
  left_inv f := f.left_inv
  right_inv f := f.right_inv

/--
Instance `continuousAlgEquivClass` / 实例 `continuousAlgEquivClass`

English:
instance continuousAlgEquivClass
  signature: : ContinuousAlgEquivClass (A ≃A[R] B) R A B where
  body: f.map_add'
  map_mul f := f.map_mul'
  commutes f := f.commutes'
  map_continuous := continuous_toFun
  inv_continuous := continuous_invFun

中文:
实例 continuousAlgEquivClass
  签名: : 余ntinuousAlg等价类 (A ≃A[R] B) R A B where
  定义体: f.map_add'
  map_mul f := f.map_mul'
  commutes f := f.commutes'
  map_continuous := continuous_toFun
  inv_continuous := continuous_invFun

Depends on / 依赖: f.map_add, map_add
-/
instance continuousAlgEquivClass : ContinuousAlgEquivClass (A ≃A[R] B) R A B where
  map_add f := f.map_add'
  map_mul f := f.map_mul'
  commutes f := f.commutes'
  map_continuous := continuous_toFun
  inv_continuous := continuous_invFun

/--
theorem `coe_apply` / 定理 `coe_apply`

English:
theorem coe_apply
  given: (e : A ≃A[R] B) (a : A)
  statement: (e : A ->A[R] B) a = e a
  proof: rfl

中文:
定理 coe_apply
  条件: (e : A ≃A[R] B) (a : A)
  结论: (e : A ->A[R] B) a = e a
  证明: rfl
-/
theorem coe_apply (e : A ≃A[R] B) (a : A) : (e : A ->A[R] B) a = e a := rfl

/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (e : A ≃ₐ[R] B) (he he')
  statement: ⇑(mk e he he') = e
  proof: rfl

@[simp]

中文:
定理 coe_mk
  条件: (e : A ≃ₐ[R] B) (he he')
  结论: ⇑(mk e he he') = e
  证明: rfl

@[simp]
-/
@[simp] theorem coe_mk (e : A ≃ₐ[R] B) (he he') : ⇑(mk e he he') = e := rfl

@[simp]
/--
theorem `coe_coe` / 定理 `coe_coe`

English:
theorem coe_coe
  given: (e : A ≃A[R] B)
  statement: ⇑(e : A ->A[R] B) = e
  proof: rfl

中文:
定理 coe_coe
  条件: (e : A ≃A[R] B)
  结论: ⇑(e : A ->A[R] B) = e
  证明: rfl
-/
theorem coe_coe (e : A ≃A[R] B) : ⇑(e : A ->A[R] B) = e := rfl

/--
theorem `toAlgEquiv_injective` / 定理 `toAlgEquiv_injective`

English:
theorem toAlgEquiv_injective
  statement: Function.Injective (toAlgEquiv : (A ≃A[R] B) -> A ≃ₐ[R] B)
  proof: by
  rintro ⟨e, _, _⟩ ⟨e', _, _⟩ rfl
  rfl

@[ext]

中文:
定理 toAlgEquiv_injective
  结论: 函数.单射 (toAlgEquiv : (A ≃A[R] B) -> A ≃ₐ[R] B)
  证明: by
  rintro ⟨e, _, _⟩ ⟨e', _, _⟩ rfl
  rfl

@[ext]
-/
theorem toAlgEquiv_injective : Function.Injective (toAlgEquiv : (A ≃A[R] B) -> A ≃ₐ[R] B) := by
  rintro ⟨e, _, _⟩ ⟨e', _, _⟩ rfl
  rfl

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : A ≃A[R] B} (h : ⇑f = ⇑g)
  statement: f = g
  proof: toAlgEquiv_injective AlgEquiv.ext congr_fun h

中文:
定理 ext
  条件: {f g : A ≃A[R] B} (h : ⇑f = ⇑g)
  结论: f = g
  证明: toAlgEquiv_injective AlgEquiv.ext congr_fun h

Depends on / 依赖: AlgEquiv, AlgEquiv.ext, congr_fun, toAlgEquiv_injective
-/
theorem ext {f g : A ≃A[R] B} (h : ⇑f = ⇑g) : f = g :=
toAlgEquiv_injective AlgEquiv.ext congr_fun h

/--
theorem `coe_injective` / 定理 `coe_injective`

English:
theorem coe_injective
  statement: Function.Injective ((↑) : (A ≃A[R] B) -> A ->A[R] B)
  proof: fun _ _ h => ext funext ContinuousAlgHom.ext_iff.1 h

@[simp]

中文:
定理 coe_injective
  结论: 函数.单射 ((↑) : (A ≃A[R] B) -> A ->A[R] B)
  证明: fun _ _ h => ext funext ContinuousAlgHom.ext_iff.1 h

@[simp]

Depends on / 依赖: ContinuousAlgHom, ContinuousAlgHom.ext_iff, ext_iff
-/
theorem coe_injective : Function.Injective ((↑) : (A ≃A[R] B) -> A ->A[R] B) :=
fun _ _ h => ext funext ContinuousAlgHom.ext_iff.1 h

@[simp]
/--
theorem `coe_inj` / 定理 `coe_inj`

English:
theorem coe_inj
  given: {f g : A ≃A[R] B}
  statement: (f : A ->A[R] B) = g ↔ f = g
  proof: coe_injective.eq_iff

@[simp]

中文:
定理 coe_inj
  条件: {f g : A ≃A[R] B}
  结论: (f : A ->A[R] B) = g ↔ f = g
  证明: coe_injective.eq_iff

@[simp]

Depends on / 依赖: coe_injective, coe_injective.eq_iff, eq_iff
-/
theorem coe_inj {f g : A ≃A[R] B} : (f : A ->A[R] B) = g ↔ f = g :=
  coe_injective.eq_iff

@[simp]
/--
theorem `coe_toAlgEquiv` / 定理 `coe_toAlgEquiv`

English:
theorem coe_toAlgEquiv
  given: (e : A ≃A[R] B)
  statement: ⇑e.toAlgEquiv = e
  proof: rfl

中文:
定理 coe_toAlgEquiv
  条件: (e : A ≃A[R] B)
  结论: ⇑e.toAlgEquiv = e
  证明: rfl
-/
theorem coe_toAlgEquiv (e : A ≃A[R] B) : ⇑e.toAlgEquiv = e := rfl

/-- The natural coercion from a continuous algebra isomorphism
to a continuous linear isomorphism. -/
@[coe]
/--
Definition of `toContinuousLinearEquiv` / `toContinuousLinearEquiv` 的定义

English:
definition toContinuousLinearEquiv
  signature: (e : A ≃A[R] B)
  body: { e with __ := e.toLinearEquiv }

中文:
定义 toContinuousLinearEquiv
  签名: (e : A ≃A[R] B)
  定义体: { e with __ := e.toLinearEquiv }

Depends on / 依赖: e.toLinearEquiv, toLinearEquiv
-/
def toContinuousLinearEquiv (e : A ≃A[R] B) : A ≃L[R] B :=
  { e with __ := e.toLinearEquiv }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe (A ≃A[R] B) (A ≃L[R] B)
  body: ⟨toContinuousLinearEquiv⟩

中文:
实例 :
  签名: Coe (A ≃A[R] B) (A ≃L[R] B)
  定义体: ⟨toContinuousLinearEquiv⟩

Depends on / 依赖: toContinuousLinearEquiv
-/
instance : Coe (A ≃A[R] B) (A ≃L[R] B) := ⟨toContinuousLinearEquiv⟩

/--
theorem `coeCLE_apply` / 定理 `coeCLE_apply`

English:
theorem coeCLE_apply
  given: (e : A ≃A[R] B) (a : A)
  statement: (e : A ≃L[R] B) a = e a
  proof: rfl

中文:
定理 coeCLE_apply
  条件: (e : A ≃A[R] B) (a : A)
  结论: (e : A ≃L[R] B) a = e a
  证明: rfl
-/
@[simp] theorem coeCLE_apply (e : A ≃A[R] B) (a : A) : (e : A ≃L[R] B) a = e a := rfl

/--
theorem `coe_coeCLE` / 定理 `coe_coeCLE`

English:
theorem coe_coeCLE
  given: (e : A ≃A[R] B)
  statement: ⇑(e : A ≃L[R] B) = e
  proof: rfl

@[simp]

中文:
定理 coe_coeCLE
  条件: (e : A ≃A[R] B)
  结论: ⇑(e : A ≃L[R] B) = e
  证明: rfl

@[simp]
-/
@[simp] theorem coe_coeCLE (e : A ≃A[R] B) : ⇑(e : A ≃L[R] B) = e := rfl

@[simp]
/--
theorem `toContinuousLinearEquiv_apply` / 定理 `toContinuousLinearEquiv_apply`

English:
theorem toContinuousLinearEquiv_apply
  given: (e : A ≃A[R] B) (a : A)
  proof: rfl

中文:
定理 toContinuousLinearEquiv_apply
  条件: (e : A ≃A[R] B) (a : A)
  证明: rfl

Depends on / 依赖: UniformSpace
-/
theorem toContinuousLinearEquiv_apply (e : A ≃A[R] B) (a : A) :
    e.toContinuousLinearEquiv a = e a := rfl

/--
theorem `toContinuousLinearMap_toContinuousLinearEquiv_eq` / 定理 `toContinuousLinearMap_toContinuousLinearEquiv_eq`

English:
theorem toContinuousLinearMap_toContinuousLinearEquiv_eq
  given: (e : A ≃A[R] B)
  proof: rfl

中文:
定理 toContinuousLinearMap_toContinuousLinearEquiv_eq
  条件: (e : A ≃A[R] B)
  证明: rfl
-/
theorem toContinuousLinearMap_toContinuousLinearEquiv_eq (e : A ≃A[R] B) :
    e.toContinuousLinearEquiv.toContinuousLinearMap
    = e.toContinuousAlgHom.toContinuousLinearMap := rfl

/--
theorem `toContinuousLinearEquiv_toLinearEquiv_eq` / 定理 `toContinuousLinearEquiv_toLinearEquiv_eq`

English:
theorem toContinuousLinearEquiv_toLinearEquiv_eq
  given: (e : A ≃A[R] B)
  proof: rfl

中文:
定理 toContinuousLinearEquiv_toLinearEquiv_eq
  条件: (e : A ≃A[R] B)
  证明: rfl
-/
theorem toContinuousLinearEquiv_toLinearEquiv_eq (e : A ≃A[R] B) :
    e.toContinuousLinearEquiv.toLinearEquiv
    = e.toAlgEquiv.toLinearEquiv := rfl

/--
theorem `isOpenMap` / 定理 `isOpenMap`

English:
theorem isOpenMap
  given: (e : A ≃A[R] B)
  statement: IsOpenMap e
  proof: e.toHomeomorph.isOpenMap

中文:
定理 isOpenMap
  条件: (e : A ≃A[R] B)
  结论: 是开映射 e
  证明: e.toHomeomorph.isOpenMap

Depends on / 依赖: e.toHomeomorph.isOpenMap, isOpenMap, toHomeomorph
-/
theorem isOpenMap (e : A ≃A[R] B) : IsOpenMap e :=
  e.toHomeomorph.isOpenMap

/--
theorem `image_closure` / 定理 `image_closure`

English:
theorem image_closure
  given: (e : A ≃A[R] B) (S : Set A)
  statement: e '' closure S = closure (e '' S)
  proof: e.toHomeomorph.image_closure S

中文:
定理 image_closure
  条件: (e : A ≃A[R] B) (S : 集合 A)
  结论: e '' closure S = closure (e '' S)
  证明: e.toHomeomorph.image_closure S

Depends on / 依赖: e.toHomeomorph.image_closure, image_closure, toHomeomorph
-/
theorem image_closure (e : A ≃A[R] B) (S : Set A) : e '' closure S = closure (e '' S) :=
  e.toHomeomorph.image_closure S

/--
theorem `preimage_closure` / 定理 `preimage_closure`

English:
theorem preimage_closure
  given: (e : A ≃A[R] B) (S : Set B)
  statement: e ⁻¹' closure S = closure (e ⁻¹' S)
  proof: e.toHomeomorph.preimage_closure S

@[simp]

中文:
定理 preimage_closure
  条件: (e : A ≃A[R] B) (S : 集合 B)
  结论: e ⁻¹' closure S = closure (e ⁻¹' S)
  证明: e.toHomeomorph.preimage_closure S

@[simp]

Depends on / 依赖: e.toHomeomorph.preimage_closure, preimage_closure, toHomeomorph
-/
theorem preimage_closure (e : A ≃A[R] B) (S : Set B) : e ⁻¹' closure S = closure (e ⁻¹' S) :=
  e.toHomeomorph.preimage_closure S

@[simp]
/--
theorem `isClosed_image` / 定理 `isClosed_image`

English:
theorem isClosed_image
  given: (e : A ≃A[R] B) {S : Set A}
  statement: IsClosed (e '' S) ↔ IsClosed S
  proof: e.toHomeomorph.isClosed_image

中文:
定理 isClosed_image
  条件: (e : A ≃A[R] B) {S : 集合 A}
  结论: 是闭集 (e '' S) ↔ 是闭集 S
  证明: e.toHomeomorph.isClosed_image

Depends on / 依赖: e.toHomeomorph.isClosed_image, isClosed_image, toHomeomorph
-/
theorem isClosed_image (e : A ≃A[R] B) {S : Set A} : IsClosed (e '' S) ↔ IsClosed S :=
  e.toHomeomorph.isClosed_image

/--
theorem `map_nhds_eq` / 定理 `map_nhds_eq`

English:
theorem map_nhds_eq
  given: (e : A ≃A[R] B) (a : A)
  statement: Filter.map e (𝓝 a) = 𝓝 (e a)
  proof: e.toHomeomorph.map_nhds_eq a

中文:
定理 map_nhds_eq
  条件: (e : A ≃A[R] B) (a : A)
  结论: 滤子.map e (𝓝 a) = 𝓝 (e a)
  证明: e.toHomeomorph.map_nhds_eq a

Depends on / 依赖: e.toHomeomorph.map_nhds_eq, map_nhds_eq, toHomeomorph
-/
theorem map_nhds_eq (e : A ≃A[R] B) (a : A) : Filter.map e (𝓝 a) = 𝓝 (e a) :=
  e.toHomeomorph.map_nhds_eq a

/--
theorem `map_eq_zero_iff` / 定理 `map_eq_zero_iff`

English:
theorem map_eq_zero_iff
  given: (e : A ≃A[R] B) {a : A}
  statement: e a = 0 ↔ a = 0
  proof: e.toAlgEquiv.toLinearEquiv.map_eq_zero_iff

中文:
定理 map_eq_zero_iff
  条件: (e : A ≃A[R] B) {a : A}
  结论: e a = 0 ↔ a = 0
  证明: e.toAlgEquiv.toLinearEquiv.map_eq_zero_iff

Depends on / 依赖: e.toAlgEquiv.toLinearEquiv.map_eq_zero_iff, map_eq_zero_iff, toAlgEquiv, toLinearEquiv
-/
theorem map_eq_zero_iff (e : A ≃A[R] B) {a : A} : e a = 0 ↔ a = 0 :=
  e.toAlgEquiv.toLinearEquiv.map_eq_zero_iff

attribute [continuity]
  ContinuousAlgEquiv.continuous_invFun ContinuousAlgEquiv.continuous_toFun

@[fun_prop]
/--
theorem `continuous` / 定理 `continuous`

English:
theorem continuous
  given: (e : A ≃A[R] B)
  statement: Continuous e
  proof: e.continuous_toFun

中文:
定理 continuous
  条件: (e : A ≃A[R] B)
  结论: 连续 e
  证明: e.continuous_toFun

Depends on / 依赖: continuous_toFun, e.continuous_toFun
-/
theorem continuous (e : A ≃A[R] B) : Continuous e := e.continuous_toFun

/--
theorem `continuousOn` / 定理 `continuousOn`

English:
theorem continuousOn
  given: (e : A ≃A[R] B) {S : Set A}
  statement: ContinuousOn e S
  proof: e.continuous.continuousOn

中文:
定理 continuousOn
  条件: (e : A ≃A[R] B) {S : 集合 A}
  结论: ContinuousOn e S
  证明: e.continuous.continuousOn

Depends on / 依赖: continuous, continuousOn, e.continuous.continuousOn
-/
theorem continuousOn (e : A ≃A[R] B) {S : Set A} : ContinuousOn e S :=
  e.continuous.continuousOn

/--
theorem `continuousAt` / 定理 `continuousAt`

English:
theorem continuousAt
  given: (e : A ≃A[R] B) {a : A}
  statement: ContinuousAt e a
  proof: e.continuous.continuousAt

中文:
定理 continuousAt
  条件: (e : A ≃A[R] B) {a : A}
  结论: ContinuousAt e a
  证明: e.continuous.continuousAt

Depends on / 依赖: continuous, continuousAt, e.continuous.continuousAt
-/
theorem continuousAt (e : A ≃A[R] B) {a : A} : ContinuousAt e a :=
  e.continuous.continuousAt

/--
theorem `continuousWithinAt` / 定理 `continuousWithinAt`

English:
theorem continuousWithinAt
  given: (e : A ≃A[R] B) {S : Set A} {a : A}
  proof: e.continuous.continuousWithinAt

中文:
定理 continuousWithinAt
  条件: (e : A ≃A[R] B) {S : 集合 A} {a : A}
  证明: e.continuous.continuousWithinAt

Depends on / 依赖: continuous, continuousWithinAt, e.continuous.continuousWithinAt
-/
theorem continuousWithinAt (e : A ≃A[R] B) {S : Set A} {a : A} :
    ContinuousWithinAt e S a :=
  e.continuous.continuousWithinAt

/--
theorem `comp_continuous_iff` / 定理 `comp_continuous_iff`

English:
theorem comp_continuous_iff
  given: {α : Type*} [TopologicalSpace α] (e : A ≃A[R] B) {f : α -> A}
  proof: e.toHomeomorph.comp_continuous_iff

中文:
定理 comp_continuous_iff
  条件: {α : 类型} [拓扑空间 α] (e : A ≃A[R] B) {f : α -> A}
  证明: e.toHomeomorph.comp_continuous_iff

Depends on / 依赖: comp_continuous_iff, e.toHomeomorph.comp_continuous_iff, toHomeomorph
-/
theorem comp_continuous_iff {α : Type*} [TopologicalSpace α] (e : A ≃A[R] B) {f : α -> A} :
    Continuous (e ∘ f) ↔ Continuous f :=
  e.toHomeomorph.comp_continuous_iff

/--
theorem `comp_continuous_iff'` / 定理 `comp_continuous_iff'`

English:
theorem comp_continuous_iff'
  given: {β : Type*} [TopologicalSpace β] (e : A ≃A[R] B) {g : B -> β}
  proof: e.toHomeomorph.comp_continuous_iff'

中文:
定理 comp_continuous_iff'
  条件: {β : 类型} [拓扑空间 β] (e : A ≃A[R] B) {g : B -> β}
  证明: e.toHomeomorph.comp_continuous_iff'

Depends on / 依赖: comp_continuous_iff, e.toHomeomorph.comp_continuous_iff, toHomeomorph
-/
theorem comp_continuous_iff' {β : Type*} [TopologicalSpace β] (e : A ≃A[R] B) {g : B -> β} :
    Continuous (g ∘ e) ↔ Continuous g :=
  e.toHomeomorph.comp_continuous_iff'

variable (R A)

/-- The identity isomorphism as a continuous `R`-algebra equivalence. -/
@[refl]
/--
Definition of `refl` / `refl` 的定义

English:
definition refl
  signature: : A ≃A[R] A where
  body: AlgEquiv.refl
  continuous_toFun := continuous_id
  continuous_invFun := continuous_id

@[simp]

中文:
定义 refl
  签名: : A ≃A[R] A where
  定义体: AlgEquiv.refl
  continuous_toFun := continuous_id
  continuous_invFun := continuous_id

@[simp]

Depends on / 依赖: AlgEquiv, AlgEquiv.refl
-/
def refl : A ≃A[R] A where
  __ := AlgEquiv.refl
  continuous_toFun := continuous_id
  continuous_invFun := continuous_id

@[simp]
/--
theorem `refl_apply` / 定理 `refl_apply`

English:
theorem refl_apply
  given: (a : A)
  statement: refl R A a = a
  proof: rfl

@[simp]

中文:
定理 refl_apply
  条件: (a : A)
  结论: refl R A a = a
  证明: rfl

@[simp]
-/
theorem refl_apply (a : A) : refl R A a = a := rfl

@[simp]
/--
theorem `coe_refl` / 定理 `coe_refl`

English:
theorem coe_refl
  statement: refl R A = ContinuousAlgHom.id R A
  proof: rfl

@[simp]

中文:
定理 coe_refl
  结论: refl R A = 余ntinuousAlg态射.id R A
  证明: rfl

@[simp]
-/
theorem coe_refl : refl R A = ContinuousAlgHom.id R A := rfl

@[simp]
/--
theorem `coeCLE_refl` / 定理 `coeCLE_refl`

English:
theorem coeCLE_refl
  statement: (refl R A).toContinuousLinearEquiv = ContinuousLinearEquiv.refl R A
  proof: rfl

@[simp]

中文:
定理 coeCLE_refl
  结论: (refl R A).toContinuousLinearEquiv = 连续线性等价.refl R A
  证明: rfl

@[simp]
-/
theorem coeCLE_refl : (refl R A).toContinuousLinearEquiv = ContinuousLinearEquiv.refl R A := rfl

@[simp]
/--
theorem `coe_refl'` / 定理 `coe_refl'`

English:
theorem coe_refl'
  statement: ⇑(refl R A) = id
  proof: rfl

@[simp]

中文:
定理 coe_refl'
  结论: ⇑(refl R A) = id
  证明: rfl

@[simp]
-/
theorem coe_refl' : ⇑(refl R A) = id := rfl

@[simp]
/--
theorem `refl_toContinuousLinearEquiv` / 定理 `refl_toContinuousLinearEquiv`

English:
theorem refl_toContinuousLinearEquiv
  proof: rfl

中文:
定理 refl_toContinuousLinearEquiv
  证明: rfl
-/
theorem refl_toContinuousLinearEquiv :
    (refl R A).toContinuousLinearEquiv = .refl R A := rfl

variable {R A}

/-- The inverse of a continuous algebra equivalence. -/
@[symm]
/--
Definition of `symm` / `symm` 的定义

English:
definition symm
  signature: (e : A ≃A[R] B)
  body: e.toAlgEquiv.symm
  continuous_toFun := e.continuous_invFun
  continuous_invFun := e.continuous_toFun

@[simp]

中文:
定义 symm
  签名: (e : A ≃A[R] B)
  定义体: e.toAlgEquiv.symm
  continuous_toFun := e.continuous_invFun
  continuous_invFun := e.continuous_toFun

@[simp]

Depends on / 依赖: e.toAlgEquiv.symm, toAlgEquiv
-/
def symm (e : A ≃A[R] B) : B ≃A[R] A where
  __ := e.toAlgEquiv.symm
  continuous_toFun := e.continuous_invFun
  continuous_invFun := e.continuous_toFun

@[simp]
/--
theorem `apply_symm_apply` / 定理 `apply_symm_apply`

English:
theorem apply_symm_apply
  given: (e : A ≃A[R] B) (b : B)
  statement: e (e.symm b) = b
  proof: e.1.right_inv b

@[simp]

中文:
定理 apply_symm_apply
  条件: (e : A ≃A[R] B) (b : B)
  结论: e (e.symm b) = b
  证明: e.1.right_inv b

@[simp]

Depends on / 依赖: right_inv
-/
theorem apply_symm_apply (e : A ≃A[R] B) (b : B) : e (e.symm b) = b :=
  e.1.right_inv b

@[simp]
/--
theorem `symm_apply_apply` / 定理 `symm_apply_apply`

English:
theorem symm_apply_apply
  given: (e : A ≃A[R] B) (a : A)
  statement: e.symm (e a) = a
  proof: e.1.left_inv a

@[simp]

中文:
定理 symm_apply_apply
  条件: (e : A ≃A[R] B) (a : A)
  结论: e.symm (e a) = a
  证明: e.1.left_inv a

@[simp]

Depends on / 依赖: left_inv
-/
theorem symm_apply_apply (e : A ≃A[R] B) (a : A) : e.symm (e a) = a :=
  e.1.left_inv a

@[simp]
/--
theorem `symm_image_image` / 定理 `symm_image_image`

English:
theorem symm_image_image
  given: (e : A ≃A[R] B) (S : Set A)
  statement: e.symm '' e '' S = S
  proof: e.toEquiv.symm_image_image S

@[simp]

中文:
定理 symm_image_image
  条件: (e : A ≃A[R] B) (S : 集合 A)
  结论: e.symm '' e '' S = S
  证明: e.toEquiv.symm_image_image S

@[simp]

Depends on / 依赖: e.toEquiv.symm_image_image, symm_image_image, toEquiv
-/
theorem symm_image_image (e : A ≃A[R] B) (S : Set A) : e.symm '' e '' S = S :=
  e.toEquiv.symm_image_image S

@[simp]
/--
theorem `image_symm_image` / 定理 `image_symm_image`

English:
theorem image_symm_image
  given: (e : A ≃A[R] B) (S : Set B)
  statement: e '' e.symm '' S = S
  proof: e.symm.symm_image_image S

@[simp]

中文:
定理 image_symm_image
  条件: (e : A ≃A[R] B) (S : 集合 B)
  结论: e '' e.symm '' S = S
  证明: e.symm.symm_image_image S

@[simp]

Depends on / 依赖: e.symm.symm_image_image, symm_image_image
-/
theorem image_symm_image (e : A ≃A[R] B) (S : Set B) : e '' e.symm '' S = S :=
  e.symm.symm_image_image S

@[simp]
/--
theorem `symm_toAlgEquiv` / 定理 `symm_toAlgEquiv`

English:
theorem symm_toAlgEquiv
  given: (e : A ≃A[R] B)
  statement: e.symm.toAlgEquiv = e.toAlgEquiv.symm
  proof: rfl

@[simp]

中文:
定理 symm_toAlgEquiv
  条件: (e : A ≃A[R] B)
  结论: e.symm.toAlgEquiv = e.toAlgEquiv.symm
  证明: rfl

@[simp]
-/
theorem symm_toAlgEquiv (e : A ≃A[R] B) : e.symm.toAlgEquiv = e.toAlgEquiv.symm := rfl

@[simp]
/--
theorem `symm_toHomeomorph` / 定理 `symm_toHomeomorph`

English:
theorem symm_toHomeomorph
  given: (e : A ≃A[R] B)
  statement: e.symm.toHomeomorph = e.toHomeomorph.symm
  proof: rfl

@[simp]

中文:
定理 symm_toHomeomorph
  条件: (e : A ≃A[R] B)
  结论: e.symm.toHomeomorph = e.toHomeomorph.symm
  证明: rfl

@[simp]
-/
theorem symm_toHomeomorph (e : A ≃A[R] B) : e.symm.toHomeomorph = e.toHomeomorph.symm := rfl

@[simp]
/--
theorem `toContinuousLinearEquiv_symm` / 定理 `toContinuousLinearEquiv_symm`

English:
theorem toContinuousLinearEquiv_symm
  given: (e : A ≃A[R] B)
  proof: rfl

中文:
定理 toContinuousLinearEquiv_symm
  条件: (e : A ≃A[R] B)
  证明: rfl
-/
theorem toContinuousLinearEquiv_symm (e : A ≃A[R] B) :
    e.symm.toContinuousLinearEquiv = e.toContinuousLinearEquiv.symm := rfl

/--
theorem `symm_map_nhds_eq` / 定理 `symm_map_nhds_eq`

English:
theorem symm_map_nhds_eq
  given: (e : A ≃A[R] B) (a : A)
  statement: Filter.map e.symm (𝓝 (e a)) = 𝓝 a
  proof: e.toHomeomorph.symm_map_nhds_eq a

中文:
定理 symm_map_nhds_eq
  条件: (e : A ≃A[R] B) (a : A)
  结论: 滤子.map e.symm (𝓝 (e a)) = 𝓝 a
  证明: e.toHomeomorph.symm_map_nhds_eq a

Depends on / 依赖: e.toHomeomorph.symm_map_nhds_eq, symm_map_nhds_eq, toHomeomorph
-/
theorem symm_map_nhds_eq (e : A ≃A[R] B) (a : A) : Filter.map e.symm (𝓝 (e a)) = 𝓝 a :=
  e.toHomeomorph.symm_map_nhds_eq a

/-- The composition of two continuous algebra equivalences. -/
@[trans]
/--
Definition of `trans` / `trans` 的定义

English:
definition trans
  signature: (e₁ : A ≃A[R] B) (e₂ : B ≃A[R] C)
  body: e₁.toAlgEquiv.trans e₂.toAlgEquiv
  continuous_toFun := e₂.continuous_toFun.comp e₁.continuous_toFun
  continuous_invFun := e₁.continuous_invFun.comp e₂.continuous_invFun

@[simp]

中文:
定义 trans
  签名: (e₁ : A ≃A[R] B) (e₂ : B ≃A[R] C)
  定义体: e₁.toAlgEquiv.trans e₂.toAlgEquiv
  continuous_toFun := e₂.continuous_toFun.comp e₁.continuous_toFun
  continuous_invFun := e₁.continuous_invFun.comp e₂.continuous_invFun

@[simp]

Depends on / 依赖: toAlgEquiv, toAlgEquiv.trans
-/
def trans (e₁ : A ≃A[R] B) (e₂ : B ≃A[R] C) : A ≃A[R] C where
  __ := e₁.toAlgEquiv.trans e₂.toAlgEquiv
  continuous_toFun := e₂.continuous_toFun.comp e₁.continuous_toFun
  continuous_invFun := e₁.continuous_invFun.comp e₂.continuous_invFun

@[simp]
/--
theorem `trans_toAlgEquiv` / 定理 `trans_toAlgEquiv`

English:
theorem trans_toAlgEquiv
  given: (e₁ : A ≃A[R] B) (e₂ : B ≃A[R] C)
  proof: rfl

@[simp]

中文:
定理 trans_toAlgEquiv
  条件: (e₁ : A ≃A[R] B) (e₂ : B ≃A[R] C)
  证明: rfl

@[simp]
-/
theorem trans_toAlgEquiv (e₁ : A ≃A[R] B) (e₂ : B ≃A[R] C) :
    (e₁.trans e₂).toAlgEquiv = e₁.toAlgEquiv.trans e₂.toAlgEquiv :=
  rfl

@[simp]
/--
theorem `trans_toContinuousLinearEquiv` / 定理 `trans_toContinuousLinearEquiv`

English:
theorem trans_toContinuousLinearEquiv
  given: (e₁ : A ≃A[R] B) (e₂ : B ≃A[R] C)
  proof: rfl

@[simp]

中文:
定理 trans_toContinuousLinearEquiv
  条件: (e₁ : A ≃A[R] B) (e₂ : B ≃A[R] C)
  证明: rfl

@[simp]
-/
theorem trans_toContinuousLinearEquiv (e₁ : A ≃A[R] B) (e₂ : B ≃A[R] C) :
    (e₁.trans e₂).toContinuousLinearEquiv
    = e₁.toContinuousLinearEquiv.trans e₂.toContinuousLinearEquiv := rfl

@[simp]
/--
theorem `trans_apply` / 定理 `trans_apply`

English:
theorem trans_apply
  given: (e₁ : A ≃A[R] B) (e₂ : B ≃A[R] C) (a : A)
  proof: rfl

@[simp]

中文:
定理 trans_apply
  条件: (e₁ : A ≃A[R] B) (e₂ : B ≃A[R] C) (a : A)
  证明: rfl

@[simp]
-/
theorem trans_apply (e₁ : A ≃A[R] B) (e₂ : B ≃A[R] C) (a : A) :
    (e₁.trans e₂) a = e₂ (e₁ a) :=
  rfl

@[simp]
/--
theorem `symm_trans_apply` / 定理 `symm_trans_apply`

English:
theorem symm_trans_apply
  given: (e₁ : B ≃A[R] A) (e₂ : C ≃A[R] B) (a : A)
  proof: rfl

中文:
定理 symm_trans_apply
  条件: (e₁ : B ≃A[R] A) (e₂ : C ≃A[R] B) (a : A)
  证明: rfl
-/
theorem symm_trans_apply (e₁ : B ≃A[R] A) (e₂ : C ≃A[R] B) (a : A) :
    (e₂.trans e₁).symm a = e₂.symm (e₁.symm a) :=
  rfl

/--
theorem `comp_coe` / 定理 `comp_coe`

English:
theorem comp_coe
  given: (e₁ : A ≃A[R] B) (e₂ : B ≃A[R] C)
  proof: by
  rfl

@[simp high]

中文:
定理 comp_coe
  条件: (e₁ : A ≃A[R] B) (e₂ : B ≃A[R] C)
  证明: by
  rfl

@[simp high]
-/
theorem comp_coe (e₁ : A ≃A[R] B) (e₂ : B ≃A[R] C) :
    e₂.toAlgHom.comp e₁.toAlgHom = e₁.trans e₂ := by
  rfl

@[simp high]
/--
theorem `coe_comp_coe_symm` / 定理 `coe_comp_coe_symm`

English:
theorem coe_comp_coe_symm
  given: (e : A ≃A[R] B)
  proof: ContinuousAlgHom.ext e.apply_symm_apply

@[simp high]

中文:
定理 coe_comp_coe_symm
  条件: (e : A ≃A[R] B)
  证明: ContinuousAlgHom.ext e.apply_symm_apply

@[simp high]

Depends on / 依赖: ContinuousAlgHom, ContinuousAlgHom.ext, apply_symm_apply, e.apply_symm_apply
-/
theorem coe_comp_coe_symm (e : A ≃A[R] B) :
    e.toContinuousAlgHom.comp e.symm = ContinuousAlgHom.id R B :=
  ContinuousAlgHom.ext e.apply_symm_apply

@[simp high]
/--
theorem `coe_symm_comp_coe` / 定理 `coe_symm_comp_coe`

English:
theorem coe_symm_comp_coe
  given: (e : A ≃A[R] B)
  proof: ContinuousAlgHom.ext e.symm_apply_apply

@[simp]

中文:
定理 coe_symm_comp_coe
  条件: (e : A ≃A[R] B)
  证明: ContinuousAlgHom.ext e.symm_apply_apply

@[simp]

Depends on / 依赖: ContinuousAlgHom, ContinuousAlgHom.ext, e.symm_apply_apply, symm_apply_apply
-/
theorem coe_symm_comp_coe (e : A ≃A[R] B) :
    e.symm.toContinuousAlgHom.comp e = ContinuousAlgHom.id R A :=
  ContinuousAlgHom.ext e.symm_apply_apply

@[simp]
/--
theorem `symm_comp_self` / 定理 `symm_comp_self`

English:
theorem symm_comp_self
  given: (e : A ≃A[R] B)
  statement: (e.symm : B -> A) ∘ e = id
  proof: by
exact funext e.symm_apply_apply

@[simp]

中文:
定理 symm_comp_self
  条件: (e : A ≃A[R] B)
  结论: (e.symm : B -> A) ∘ e = id
  证明: by
exact funext e.symm_apply_apply

@[simp]

Depends on / 依赖: e.symm_apply_apply, symm_apply_apply
-/
theorem symm_comp_self (e : A ≃A[R] B) : (e.symm : B -> A) ∘ e = id := by
exact funext e.symm_apply_apply

@[simp]
/--
theorem `self_comp_symm` / 定理 `self_comp_symm`

English:
theorem self_comp_symm
  given: (e : A ≃A[R] B)
  statement: (e : A -> B) ∘ e.symm = id
  proof: funext e.apply_symm_apply

@[simp]

中文:
定理 self_comp_symm
  条件: (e : A ≃A[R] B)
  结论: (e : A -> B) ∘ e.symm = id
  证明: funext e.apply_symm_apply

@[simp]

Depends on / 依赖: apply_symm_apply, e.apply_symm_apply
-/
theorem self_comp_symm (e : A ≃A[R] B) : (e : A -> B) ∘ e.symm = id :=
funext e.apply_symm_apply

@[simp]
/--
theorem `symm_symm` / 定理 `symm_symm`

English:
theorem symm_symm
  given: (e : A ≃A[R] B)
  statement: e.symm.symm = e
  proof: rfl

中文:
定理 symm_symm
  条件: (e : A ≃A[R] B)
  结论: e.symm.symm = e
  证明: rfl
-/
theorem symm_symm (e : A ≃A[R] B) : e.symm.symm = e := rfl

/--
theorem `symm_bijective` / 定理 `symm_bijective`

English:
theorem symm_bijective
  statement: Function.Bijective (symm : (A ≃A[R] B) -> _)
  proof: Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]

中文:
定理 symm_bijective
  结论: 函数.双射 (symm : (A ≃A[R] B) -> _)
  证明: Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]

Depends on / 依赖: Function, Function.bijective_iff_has_inverse.mpr, bijective_iff_has_inverse, symm_symm
-/
theorem symm_bijective : Function.Bijective (symm : (A ≃A[R] B) -> _) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]
/--
theorem `refl_symm` / 定理 `refl_symm`

English:
theorem refl_symm
  statement: (refl R A).symm = refl R A
  proof: rfl

中文:
定理 refl_symm
  结论: (refl R A).symm = refl R A
  证明: rfl
-/
theorem refl_symm : (refl R A).symm = refl R A := rfl

/--
theorem `symm_symm_apply` / 定理 `symm_symm_apply`

English:
theorem symm_symm_apply
  given: (e : A ≃A[R] B) (a : A)
  statement: e.symm.symm a = e a
  proof: rfl

中文:
定理 symm_symm_apply
  条件: (e : A ≃A[R] B) (a : A)
  结论: e.symm.symm a = e a
  证明: rfl
-/
theorem symm_symm_apply (e : A ≃A[R] B) (a : A) : e.symm.symm a = e a := rfl

/--
theorem `symm_apply_eq` / 定理 `symm_apply_eq`

English:
theorem symm_apply_eq
  given: (e : A ≃A[R] B) {a : A} {b : B}
  statement: e.symm b = a ↔ b = e a
  proof: e.toEquiv.symm_apply_eq

中文:
定理 symm_apply_eq
  条件: (e : A ≃A[R] B) {a : A} {b : B}
  结论: e.symm b = a ↔ b = e a
  证明: e.toEquiv.symm_apply_eq

Depends on / 依赖: e.toEquiv.symm_apply_eq, symm_apply_eq, toEquiv
-/
theorem symm_apply_eq (e : A ≃A[R] B) {a : A} {b : B} : e.symm b = a ↔ b = e a :=
  e.toEquiv.symm_apply_eq

/--
theorem `eq_symm_apply` / 定理 `eq_symm_apply`

English:
theorem eq_symm_apply
  given: (e : A ≃A[R] B) {a : A} {b : B}
  statement: a = e.symm b ↔ e a = b
  proof: e.toEquiv.eq_symm_apply

中文:
定理 eq_symm_apply
  条件: (e : A ≃A[R] B) {a : A} {b : B}
  结论: a = e.symm b ↔ e a = b
  证明: e.toEquiv.eq_symm_apply

Depends on / 依赖: e.toEquiv.eq_symm_apply, eq_symm_apply, toEquiv
-/
theorem eq_symm_apply (e : A ≃A[R] B) {a : A} {b : B} : a = e.symm b ↔ e a = b :=
  e.toEquiv.eq_symm_apply

/--
theorem `image_eq_preimage_symm` / 定理 `image_eq_preimage_symm`

English:
theorem image_eq_preimage_symm
  given: (e : A ≃A[R] B) (S : Set A)
  statement: e '' S = e.symm ⁻¹' S
  proof: e.toEquiv.image_eq_preimage_symm S

中文:
定理 image_eq_preimage_symm
  条件: (e : A ≃A[R] B) (S : 集合 A)
  结论: e '' S = e.symm ⁻¹' S
  证明: e.toEquiv.image_eq_preimage_symm S

Depends on / 依赖: e.toEquiv.image_eq_preimage_symm, image_eq_preimage_symm, toEquiv
-/
theorem image_eq_preimage_symm (e : A ≃A[R] B) (S : Set A) : e '' S = e.symm ⁻¹' S :=
  e.toEquiv.image_eq_preimage_symm S

/--
theorem `image_symm_eq_preimage` / 定理 `image_symm_eq_preimage`

English:
theorem image_symm_eq_preimage
  given: (e : A ≃A[R] B) (S : Set B)
  statement: e.symm '' S = e ⁻¹' S
  proof: by
  rw [e.symm.image_eq_preimage_symm]; rw [e.symm_symm]

@[simp]

中文:
定理 image_symm_eq_preimage
  条件: (e : A ≃A[R] B) (S : 集合 B)
  结论: e.symm '' S = e ⁻¹' S
  证明: by
  rw [e.symm.image_eq_preimage_symm]; rw [e.symm_symm]

@[simp]

Depends on / 依赖: e.symm.image_eq_preimage_symm, e.symm_symm, image_eq_preimage_symm, symm_symm
-/
theorem image_symm_eq_preimage (e : A ≃A[R] B) (S : Set B) : e.symm '' S = e ⁻¹' S := by
  rw [e.symm.image_eq_preimage_symm]; rw [e.symm_symm]

@[simp]
/--
theorem `symm_preimage_preimage` / 定理 `symm_preimage_preimage`

English:
theorem symm_preimage_preimage
  given: (e : A ≃A[R] B) (S : Set B)
  statement: e.symm ⁻¹' e ⁻¹' S = S
  proof: e.toEquiv.symm_preimage_preimage S

@[simp]

中文:
定理 symm_preimage_preimage
  条件: (e : A ≃A[R] B) (S : 集合 B)
  结论: e.symm ⁻¹' e ⁻¹' S = S
  证明: e.toEquiv.symm_preimage_preimage S

@[simp]

Depends on / 依赖: e.toEquiv.symm_preimage_preimage, symm_preimage_preimage, toEquiv
-/
theorem symm_preimage_preimage (e : A ≃A[R] B) (S : Set B) : e.symm ⁻¹' e ⁻¹' S = S :=
  e.toEquiv.symm_preimage_preimage S

@[simp]
/--
theorem `preimage_symm_preimage` / 定理 `preimage_symm_preimage`

English:
theorem preimage_symm_preimage
  given: (e : A ≃A[R] B) (S : Set A)
  statement: e ⁻¹' e.symm ⁻¹' S = S
  proof: e.symm.symm_preimage_preimage S

中文:
定理 preimage_symm_preimage
  条件: (e : A ≃A[R] B) (S : 集合 A)
  结论: e ⁻¹' e.symm ⁻¹' S = S
  证明: e.symm.symm_preimage_preimage S

Depends on / 依赖: e.symm.symm_preimage_preimage, symm_preimage_preimage
-/
theorem preimage_symm_preimage (e : A ≃A[R] B) (S : Set A) : e ⁻¹' e.symm ⁻¹' S = S :=
  e.symm.symm_preimage_preimage S

/--
theorem `isUniformEmbedding` / 定理 `isUniformEmbedding`

English:
theorem isUniformEmbedding
  statement: {E₁ E₂ : Type*} [UniformSpace E₁] [UniformSpace E₂] [Ring E₁]
  proof: e.toAlgEquiv.isUniformEmbedding e.toContinuousAlgHom.uniformContinuous
    e.symm.toContinuousAlgHom.uniformContinuous

中文:
定理 isUniformEmbedding
  结论: {E₁ E₂ : 类型} [一致空间 E₁] [一致空间 E₂] [环 E₁]
  证明: e.toAlgEquiv.isUniformEmbedding e.toContinuousAlgHom.uniformContinuous
    e.symm.toContinuousAlgHom.uniformContinuous

Depends on / 依赖: e.symm.toContinuousAlgHom.uniformContinuous, e.toAlgEquiv.isUniformEmbedding, e.toContinuousAlgHom.uniformContinuous, isUniformEmbedding, toAlgEquiv, toContinuousAlgHom, uniformContinuous
-/
theorem isUniformEmbedding {E₁ E₂ : Type*} [UniformSpace E₁] [UniformSpace E₂] [Ring E₁]
    [IsUniformAddGroup E₁] [Algebra R E₁] [Ring E₂] [IsUniformAddGroup E₂] [Algebra R E₂]
    (e : E₁ ≃A[R] E₂) : IsUniformEmbedding e :=
  e.toAlgEquiv.isUniformEmbedding e.toContinuousAlgHom.uniformContinuous
    e.symm.toContinuousAlgHom.uniformContinuous

/--
theorem `_root_.AlgEquiv.isUniformEmbedding` / 定理 `_root_.AlgEquiv.isUniformEmbedding`

English:
theorem _root_.AlgEquiv.isUniformEmbedding
  statement: {E₁ E₂ : Type*} [UniformSpace E₁] [UniformSpace E₂]
  proof: ContinuousAlgEquiv.isUniformEmbedding { e with
    continuous_toFun := h₁
    continuous_invFun := by dsimp; fun_prop }

中文:
定理 _root_.代数等价.isUniformEmbedding
  结论: {E₁ E₂ : 类型} [一致空间 E₁] [一致空间 E₂]
  证明: ContinuousAlgEquiv.isUniformEmbedding { e with
    continuous_toFun := h₁
    continuous_invFun := by dsimp; fun_prop }

Depends on / 依赖: ContinuousAlgEquiv, ContinuousAlgEquiv.isUniformEmbedding, continuous_invFun, continuous_toFun, fun_prop, isUniformEmbedding
-/
theorem _root_.AlgEquiv.isUniformEmbedding {E₁ E₂ : Type*} [UniformSpace E₁] [UniformSpace E₂]
    [Ring E₁] [IsUniformAddGroup E₁] [Algebra R E₁] [Ring E₂] [IsUniformAddGroup E₂] [Algebra R E₂]
    (e : E₁ ≃ₐ[R] E₂) (h₁ : Continuous e) (h₂ : Continuous e.symm) :
    IsUniformEmbedding e :=
  ContinuousAlgEquiv.isUniformEmbedding { e with
    continuous_toFun := h₁
    continuous_invFun := by dsimp; fun_prop }

/--
theorem `surjective` / 定理 `surjective`

English:
theorem surjective
  given: (e : A ≃A[R] B)
  statement: Function.Surjective e
  proof: e.toAlgEquiv.surjective

中文:
定理 surjective
  条件: (e : A ≃A[R] B)
  结论: 函数.满射 e
  证明: e.toAlgEquiv.surjective

Depends on / 依赖: e.toAlgEquiv.surjective, surjective, toAlgEquiv
-/
theorem surjective (e : A ≃A[R] B) : Function.Surjective e := e.toAlgEquiv.surjective

/--
Definition of `cast` / `cast` 的定义

English:
definition cast
  signature: {ι : Type*} {A : ι -> Type*} [(i : ι) -> Semiring (A i)] [(i : ι) -> Algebra R (A i)]
  body: AlgEquiv.cast h
  continuous_toFun := by cases h; exact continuous_id
  continuous_invFun := by cases h; exact continuous_id

@[simp]

中文:
定义 cast
  签名: {ι : 类型} {A : ι -> 类型} [(i : ι) -> 半环 (A i)] [(i : ι) -> 代数 R (A i)]
  定义体: AlgEquiv.cast h
  continuous_toFun := by cases h; exact continuous_id
  continuous_invFun := by cases h; exact continuous_id

@[simp]

Depends on / 依赖: AlgEquiv, AlgEquiv.cast
-/
def cast {ι : Type*} {A : ι -> Type*} [(i : ι) -> Semiring (A i)] [(i : ι) -> Algebra R (A i)]
    [(i : ι) -> TopologicalSpace (A i)] {i j : ι} (h : i = j) :
    A i ≃A[R] A j where
  __ := AlgEquiv.cast h
  continuous_toFun := by cases h; exact continuous_id
  continuous_invFun := by cases h; exact continuous_id

@[simp]
/--
theorem `cast_apply` / 定理 `cast_apply`

English:
theorem cast_apply
  statement: {ι : Type*} {A : ι -> Type*} [(i : ι) -> Semiring (A i)]
  proof: rfl

@[simp]

中文:
定理 cast_apply
  结论: {ι : 类型} {A : ι -> 类型} [(i : ι) -> 半环 (A i)]
  证明: rfl

@[simp]

Depends on / 依赖: Equiv.cast
-/
theorem cast_apply {ι : Type*} {A : ι -> Type*} [(i : ι) -> Semiring (A i)]
    [(i : ι) -> Algebra R (A i)] [(i : ι) -> TopologicalSpace (A i)] {i j : ι} (h : i = j) (x : A i) :
    cast (R := R) h x = Equiv.cast (congrArg A h) x := rfl

@[simp]
/--
theorem `cast_symm_apply` / 定理 `cast_symm_apply`

English:
theorem cast_symm_apply
  statement: {ι : Type*} {A : ι -> Type*} [(i : ι) -> Semiring (A i)]
  proof: rfl

中文:
定理 cast_symm_apply
  结论: {ι : 类型} {A : ι -> 类型} [(i : ι) -> 半环 (A i)]
  证明: rfl

Depends on / 依赖: Equiv.cast, h.symm
-/
theorem cast_symm_apply {ι : Type*} {A : ι -> Type*} [(i : ι) -> Semiring (A i)]
    [(i : ι) -> Algebra R (A i)] [(i : ι) -> TopologicalSpace (A i)] {i j : ι} (h : i = j)
    (x : A j) : (cast (R := R) h).symm x = Equiv.cast (congrArg A h.symm) x := rfl

end ContinuousAlgEquiv
