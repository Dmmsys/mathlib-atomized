/-
Copyright (c) 2021 Shing Tak Lam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam
-/
module

public import Mathlib.Topology.Order.ProjIcc
public import Mathlib.Topology.ContinuousMap.Ordered
public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.UnitInterval

/-!
# Homotopy between functions

In this file, we define a homotopy between two functions `f₀` and `f₁`. First we define
`ContinuousMap.Homotopy` between the two functions, with no restrictions on the intermediate
maps. Then, as in the formalisation in HOL-Analysis, we define
`ContinuousMap.HomotopyWith f₀ f₁ P`, for homotopies between `f₀` and `f₁`, where the
intermediate maps satisfy the predicate `P`. Finally, we define
`ContinuousMap.HomotopyRel f₀ f₁ S`, for homotopies between `f₀` and `f₁` which are fixed
on `S`.

## Definitions

* `ContinuousMap.Homotopy f₀ f₁` is the type of homotopies between `f₀` and `f₁`.
* `ContinuousMap.HomotopyWith f₀ f₁ P` is the type of homotopies between `f₀` and `f₁`, where
  the intermediate maps satisfy the predicate `P`.
* `ContinuousMap.HomotopyRel f₀ f₁ S` is the type of homotopies between `f₀` and `f₁` which
  are fixed on `S`.

For each of the above, we have

* `refl f`, which is the constant homotopy from `f` to `f`.
* `symm F`, which reverses the homotopy `F`. For example, if `F : ContinuousMap.Homotopy f₀ f₁`,
  then `F.symm : ContinuousMap.Homotopy f₁ f₀`.
* `trans F G`, which concatenates the homotopies `F` and `G`. For example, if
  `F : ContinuousMap.Homotopy f₀ f₁` and `G : ContinuousMap.Homotopy f₁ f₂`, then
  `F.trans G : ContinuousMap.Homotopy f₀ f₂`.

We also define the relations

* `ContinuousMap.Homotopic f₀ f₁` is defined to be `Nonempty (ContinuousMap.Homotopy f₀ f₁)`
* `ContinuousMap.HomotopicWith f₀ f₁ P` is defined to be
  `Nonempty (ContinuousMap.HomotopyWith f₀ f₁ P)`
* `ContinuousMap.HomotopicRel f₀ f₁ P` is defined to be
  `Nonempty (ContinuousMap.HomotopyRel f₀ f₁ P)`

and for `ContinuousMap.homotopic` and `ContinuousMap.homotopic_rel`, we also define the
`setoid` and `quotient` in `C(X, Y)` by these relations.

## References

- [HOL-Analysis formalisation](https://isabelle.in.tum.de/library/HOL/HOL-Analysis/Homotopy.html)
-/

@[expose] public section

noncomputable section

universe u v w x

variable {F : Type*} {X : Type u} {Y : Type v} {Z : Type w} {Z' : Type x} {ι : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace Z']

open unitInterval

namespace ContinuousMap

/-- `ContinuousMap.Homotopy f₀ f₁` is the type of homotopies from `f₀` to `f₁`.

When possible, instead of parametrizing results over `(f : ContinuousMap.Homotopy f₀ f₁)`,
you should parametrize over `{F : Type*} [HomotopyLike F f₀ f₁] (f : F)`.

When you extend this structure, make sure to extend `ContinuousMap.HomotopyLike`. -/
@[wikidata Q746083]
/--
Definition of `Homotopy` / `Homotopy` 的定义

English:
structure Homotopy
  parameters: (f₀ f₁ : C(X, Y))
  extends: C(I × X, Y)
  axioms and operations (2):
    - map_zero_left : forall x, toFun (0, x) = f₀ x
    - map_one_left : forall x, toFun (1, x) = f₁ x

中文:
结构 同伦
  参数: (f₀ f₁ : C(X, Y))
  继承: C(I × X, Y)
  公理与运算 (2 个):
    - map_zero_left : 对任意 x, toFun (0, x) = f₀ x
    - map_one_left : 对任意 x, toFun (1, x) = f₁ x
-/
structure Homotopy (f₀ f₁ : C(X, Y)) extends C(I × X, Y) where
  /-- value of the homotopy at 0 -/
  map_zero_left : forall x, toFun (0, x) = f₀ x
  /-- value of the homotopy at 1 -/
  map_one_left : forall x, toFun (1, x) = f₁ x

section

/--
Definition of `HomotopyLike` / `HomotopyLike` 的定义

English:
class HomotopyLike
  parameters: {X Y : outParam Type*} [TopologicalSpace X] [TopologicalSpace Y]
  extends: ContinuousMapClass F (I × X) Y
  axioms and operations (2):
    - map_zero_left((f : F)) : forall x, f (0, x) = f₀ x
    - map_one_left((f : F)) : forall x, f (1, x) = f₁ x

中文:
类 HomotopyLike
  参数: {X Y : outParam 类型} [拓扑空间 X] [拓扑空间 Y]
  继承: 连续映射类 F (I × X) Y
  公理与运算 (2 个):
    - map_zero_left((f : F)) : 对任意 x, f (0, x) = f₀ x
    - map_one_left((f : F)) : 对任意 x, f (1, x) = f₁ x
-/
class HomotopyLike {X Y : outParam Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (F : Type*) (f₀ f₁ : outParam <| C(X, Y)) [FunLike F (I × X) Y] : Prop
    extends ContinuousMapClass F (I × X) Y where
  /-- value of the homotopy at 0 -/
  map_zero_left (f : F) : forall x, f (0, x) = f₀ x
  /-- value of the homotopy at 1 -/
  map_one_left (f : F) : forall x, f (1, x) = f₁ x

end

namespace Homotopy

section

variable {f₀ f₁ : C(X, Y)}

/--
Instance `instFunLike` / 实例 `instFunLike`

English:
instance instFunLike
  signature: : FunLike (Homotopy f₀ f₁) (I × X) Y where
  body: f.toFun
  coe_injective f g h := by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr

中文:
实例 instFunLike
  签名: : 函数状 (同伦 f₀ f₁) (I × X) Y where
  定义体: f.toFun
  coe_injective f g h := by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr

Depends on / 依赖: f.toFun
-/
instance instFunLike : FunLike (Homotopy f₀ f₁) (I × X) Y where
  coe f := f.toFun
  coe_injective f g h := by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HomotopyLike (Homotopy f₀ f₁) f₀ f₁
  body: f.continuous_toFun
  map_zero_left f := f.map_zero_left
  map_one_left f := f.map_one_left

@[ext]

中文:
实例 :
  签名: HomotopyLike (同伦 f₀ f₁) f₀ f₁
  定义体: f.continuous_toFun
  map_zero_left f := f.map_zero_left
  map_one_left f := f.map_one_left

@[ext]

Depends on / 依赖: continuous_toFun, f.continuous_toFun
-/
instance : HomotopyLike (Homotopy f₀ f₁) f₀ f₁ where
  map_continuous f := f.continuous_toFun
  map_zero_left f := f.map_zero_left
  map_one_left f := f.map_one_left

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {F G : Homotopy f₀ f₁} (h : forall x, F x = G x)
  statement: F = G
  proof: DFunLike.ext _ _ h

中文:
定理 ext
  条件: {F G : 同伦 f₀ f₁} (h : 对任意 x, F x = G x)
  结论: F = G
  证明: DFunLike.ext _ _ h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {F G : Homotopy f₀ f₁} (h : forall x, F x = G x) : F = G :=
  DFunLike.ext _ _ h

/--
Definition of `Simps.apply` / `Simps.apply` 的定义

English:
definition Simps.apply
  signature: (F : Homotopy f₀ f₁)
  body: F

initialize_simps_projections Homotopy (toFun -> apply, -toContinuousMap)

中文:
定义 Simps.apply
  签名: (F : 同伦 f₀ f₁)
  定义体: F

initialize_simps_projections Homotopy (toFun -> apply, -toContinuousMap)
-/
def Simps.apply (F : Homotopy f₀ f₁) : I × X -> Y :=
  F

initialize_simps_projections Homotopy (toFun -> apply, -toContinuousMap)

/--
theorem `continuous` / 定理 `continuous`

English:
theorem continuous
  given: (F : Homotopy f₀ f₁)
  statement: Continuous F
  proof: F.continuous_toFun

@[simp]

中文:
定理 continuous
  条件: (F : 同伦 f₀ f₁)
  结论: 连续 F
  证明: F.continuous_toFun

@[simp]
-/
protected theorem continuous (F : Homotopy f₀ f₁) : Continuous F :=
  F.continuous_toFun

@[simp]
/--
theorem `apply_zero` / 定理 `apply_zero`

English:
theorem apply_zero
  given: (F : Homotopy f₀ f₁) (x : X)
  statement: F (0, x) = f₀ x
  proof: F.map_zero_left x

@[simp]

中文:
定理 apply_zero
  条件: (F : 同伦 f₀ f₁) (x : X)
  结论: F (0, x) = f₀ x
  证明: F.map_zero_left x

@[simp]

Depends on / 依赖: F.map_zero_left, map_zero_left
-/
theorem apply_zero (F : Homotopy f₀ f₁) (x : X) : F (0, x) = f₀ x :=
  F.map_zero_left x

@[simp]
/--
theorem `apply_one` / 定理 `apply_one`

English:
theorem apply_one
  given: (F : Homotopy f₀ f₁) (x : X)
  statement: F (1, x) = f₁ x
  proof: F.map_one_left x

@[simp]

中文:
定理 apply_one
  条件: (F : 同伦 f₀ f₁) (x : X)
  结论: F (1, x) = f₁ x
  证明: F.map_one_left x

@[simp]

Depends on / 依赖: F.map_one_left, map_one_left
-/
theorem apply_one (F : Homotopy f₀ f₁) (x : X) : F (1, x) = f₁ x :=
  F.map_one_left x

@[simp]
/--
theorem `coe_toContinuousMap` / 定理 `coe_toContinuousMap`

English:
theorem coe_toContinuousMap
  given: (F : Homotopy f₀ f₁)
  statement: ⇑F.toContinuousMap = F
  proof: rfl

中文:
定理 coe_toContinuousMap
  条件: (F : 同伦 f₀ f₁)
  结论: ⇑F.toContinuousMap = F
  证明: rfl
-/
theorem coe_toContinuousMap (F : Homotopy f₀ f₁) : ⇑F.toContinuousMap = F :=
  rfl

/--
Definition of `curry` / `curry` 的定义

English:
definition curry
  signature: (F : Homotopy f₀ f₁)
  body: F.toContinuousMap.curry

@[simp]

中文:
定义 curry
  签名: (F : 同伦 f₀ f₁)
  定义体: F.toContinuousMap.curry

@[simp]

Depends on / 依赖: F.toContinuousMap.curry, toContinuousMap
-/
def curry (F : Homotopy f₀ f₁) : C(I, C(X, Y)) :=
  F.toContinuousMap.curry

@[simp]
/--
theorem `curry_apply` / 定理 `curry_apply`

English:
theorem curry_apply
  given: (F : Homotopy f₀ f₁) (t : I) (x : X)
  statement: F.curry t x = F (t, x)
  proof: rfl

中文:
定理 curry_apply
  条件: (F : 同伦 f₀ f₁) (t : I) (x : X)
  结论: F.curry t x = F (t, x)
  证明: rfl
-/
theorem curry_apply (F : Homotopy f₀ f₁) (t : I) (x : X) : F.curry t x = F (t, x) :=
  rfl

/--
theorem `curry_zero` / 定理 `curry_zero`

English:
theorem curry_zero
  given: (F : Homotopy f₀ f₁)
  statement: F.curry 0 = f₀
  proof: by ext; simp

中文:
定理 curry_zero
  条件: (F : 同伦 f₀ f₁)
  结论: F.curry 0 = f₀
  证明: by ext; simp
-/
@[simp] theorem curry_zero (F : Homotopy f₀ f₁) : F.curry 0 = f₀ := by ext; simp
/--
theorem `curry_one` / 定理 `curry_one`

English:
theorem curry_one
  given: (F : Homotopy f₀ f₁)
  statement: F.curry 1 = f₁
  proof: by ext; simp

中文:
定理 curry_one
  条件: (F : 同伦 f₀ f₁)
  结论: F.curry 1 = f₁
  证明: by ext; simp
-/
@[simp] theorem curry_one (F : Homotopy f₀ f₁) : F.curry 1 = f₁ := by ext; simp

/--
Definition of `extend` / `extend` 的定义

English:
definition extend
  signature: (F : Homotopy f₀ f₁)
  body: F.curry.IccExtend zero_le_one

中文:
定义 extend
  签名: (F : 同伦 f₀ f₁)
  定义体: F.curry.IccExtend zero_le_one

Depends on / 依赖: F.curry.IccExtend, IccExtend, zero_le_one
-/
def extend (F : Homotopy f₀ f₁) : C(Real, C(X, Y)) :=
  F.curry.IccExtend zero_le_one

/--
theorem `extend_apply_of_le_zero` / 定理 `extend_apply_of_le_zero`

English:
theorem extend_apply_of_le_zero
  given: (F : Homotopy f₀ f₁) {t : Real} (ht : t <= 0) (x : X)
  proof: by
  rw [← F.apply_zero]
  exact ContinuousMap.congr_fun (Set.IccExtend_of_le_left (zero_le_one' Real) F.curry ht) x

中文:
定理 extend_apply_of_le_zero
  条件: (F : 同伦 f₀ f₁) {t : 实数} (ht : t <= 0) (x : X)
  证明: by
  rw [← F.apply_zero]
  exact ContinuousMap.congr_fun (Set.IccExtend_of_le_left (zero_le_one' Real) F.curry ht) x

Depends on / 依赖: ContinuousMap, ContinuousMap.congr_fun, F.apply_zero, F.curry, IccExtend_of_le_left, Set.IccExtend_of_le_left, apply_zero, congr_fun, zero_le_one
-/
theorem extend_apply_of_le_zero (F : Homotopy f₀ f₁) {t : Real} (ht : t <= 0) (x : X) :
    F.extend t x = f₀ x := by
  rw [← F.apply_zero]
  exact ContinuousMap.congr_fun (Set.IccExtend_of_le_left (zero_le_one' Real) F.curry ht) x

/--
theorem `extend_apply_of_one_le` / 定理 `extend_apply_of_one_le`

English:
theorem extend_apply_of_one_le
  given: (F : Homotopy f₀ f₁) {t : Real} (ht : 1 <= t) (x : X)
  proof: by
  rw [← F.apply_one]
  exact ContinuousMap.congr_fun (Set.IccExtend_of_right_le (zero_le_one' Real) F.curry ht) x

中文:
定理 extend_apply_of_one_le
  条件: (F : 同伦 f₀ f₁) {t : 实数} (ht : 1 <= t) (x : X)
  证明: by
  rw [← F.apply_one]
  exact ContinuousMap.congr_fun (Set.IccExtend_of_right_le (zero_le_one' Real) F.curry ht) x

Depends on / 依赖: ContinuousMap, ContinuousMap.congr_fun, F.apply_one, F.curry, IccExtend_of_right_le, Set.IccExtend_of_right_le, apply_one, congr_fun, zero_le_one
-/
theorem extend_apply_of_one_le (F : Homotopy f₀ f₁) {t : Real} (ht : 1 <= t) (x : X) :
    F.extend t x = f₁ x := by
  rw [← F.apply_one]
  exact ContinuousMap.congr_fun (Set.IccExtend_of_right_le (zero_le_one' Real) F.curry ht) x

/--
theorem `extend_apply_coe` / 定理 `extend_apply_coe`

English:
theorem extend_apply_coe
  given: (F : Homotopy f₀ f₁) (t : I) (x : X)
  statement: F.extend t x = F (t, x)
  proof: ContinuousMap.congr_fun (Set.IccExtend_val (zero_le_one' Real) F.curry t) x

@[simp]

中文:
定理 extend_apply_coe
  条件: (F : 同伦 f₀ f₁) (t : I) (x : X)
  结论: F.extend t x = F (t, x)
  证明: ContinuousMap.congr_fun (Set.IccExtend_val (zero_le_one' Real) F.curry t) x

@[simp]

Depends on / 依赖: ContinuousMap, ContinuousMap.congr_fun, F.curry, IccExtend_val, Set.IccExtend_val, congr_fun, zero_le_one
-/
theorem extend_apply_coe (F : Homotopy f₀ f₁) (t : I) (x : X) : F.extend t x = F (t, x) :=
  ContinuousMap.congr_fun (Set.IccExtend_val (zero_le_one' Real) F.curry t) x

@[simp]
/--
theorem `extend_of_mem_I` / 定理 `extend_of_mem_I`

English:
theorem extend_of_mem_I
  given: (F : Homotopy f₀ f₁) {t : Real} (ht : t in I)
  proof: Set.IccExtend_of_mem (zero_le_one' Real) F.curry ht

中文:
定理 extend_of_mem_I
  条件: (F : 同伦 f₀ f₁) {t : 实数} (ht : t in I)
  证明: Set.IccExtend_of_mem (zero_le_one' Real) F.curry ht

Depends on / 依赖: F.curry, IccExtend_of_mem, Set.IccExtend_of_mem, zero_le_one
-/
theorem extend_of_mem_I (F : Homotopy f₀ f₁) {t : Real} (ht : t in I) :
    F.extend t = F.curry ⟨t, ht⟩ :=
  Set.IccExtend_of_mem (zero_le_one' Real) F.curry ht

/--
theorem `extend_zero` / 定理 `extend_zero`

English:
theorem extend_zero
  given: (F : Homotopy f₀ f₁)
  statement: F.extend 0 = f₀
  proof: by simp

中文:
定理 extend_zero
  条件: (F : 同伦 f₀ f₁)
  结论: F.extend 0 = f₀
  证明: by simp
-/
theorem extend_zero (F : Homotopy f₀ f₁) : F.extend 0 = f₀ := by simp
/--
theorem `extend_one` / 定理 `extend_one`

English:
theorem extend_one
  given: (F : Homotopy f₀ f₁)
  statement: F.extend 1 = f₁
  proof: by simp

中文:
定理 extend_one
  条件: (F : 同伦 f₀ f₁)
  结论: F.extend 1 = f₁
  证明: by simp
-/
theorem extend_one (F : Homotopy f₀ f₁) : F.extend 1 = f₁ := by simp

/--
theorem `extend_apply_of_mem_I` / 定理 `extend_apply_of_mem_I`

English:
theorem extend_apply_of_mem_I
  given: (F : Homotopy f₀ f₁) {t : Real} (ht : t in I) (x : X)
  proof: by
  simp [ht]

中文:
定理 extend_apply_of_mem_I
  条件: (F : 同伦 f₀ f₁) {t : 实数} (ht : t in I) (x : X)
  证明: by
  simp [ht]
-/
theorem extend_apply_of_mem_I (F : Homotopy f₀ f₁) {t : Real} (ht : t in I) (x : X) :
    F.extend t x = F (⟨t, ht⟩, x) := by
  simp [ht]

/--
theorem `congr_fun` / 定理 `congr_fun`

English:
theorem congr_fun
  given: {F G : Homotopy f₀ f₁} (h : F = G) (x : I × X)
  statement: F x = G x
  proof: ContinuousMap.congr_fun (congr_arg _ h) x

中文:
定理 congr_fun
  条件: {F G : 同伦 f₀ f₁} (h : F = G) (x : I × X)
  结论: F x = G x
  证明: ContinuousMap.congr_fun (congr_arg _ h) x
-/
protected theorem congr_fun {F G : Homotopy f₀ f₁} (h : F = G) (x : I × X) : F x = G x :=
  ContinuousMap.congr_fun (congr_arg _ h) x

/--
theorem `congr_arg` / 定理 `congr_arg`

English:
theorem congr_arg
  given: (F : Homotopy f₀ f₁) {x y : I × X} (h : x = y)
  statement: F x = F y
  proof: F.toContinuousMap.congr_arg h

中文:
定理 congr_arg
  条件: (F : 同伦 f₀ f₁) {x y : I × X} (h : x = y)
  结论: F x = F y
  证明: F.toContinuousMap.congr_arg h
-/
protected theorem congr_arg (F : Homotopy f₀ f₁) {x y : I × X} (h : x = y) : F x = F y :=
  F.toContinuousMap.congr_arg h

end

/-- Given a continuous function `f`, we can define a `ContinuousMap.Homotopy f f` by
`F (t, x) = f x`
-/
@[simps]
/--
Definition of `refl` / `refl` 的定义

English:
definition refl
  signature: (f : C(X, Y))
  body: f x.2
  map_zero_left _ := rfl
  map_one_left _ := rfl

中文:
定义 refl
  签名: (f : C(X, Y))
  定义体: f x.2
  map_zero_left _ := rfl
  map_one_left _ := rfl
-/
def refl (f : C(X, Y)) : Homotopy f f where
  toFun x := f x.2
  map_zero_left _ := rfl
  map_one_left _ := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Homotopy (ContinuousMap.id X) (ContinuousMap.id X))
  body: ⟨Homotopy.refl _⟩

中文:
实例 :
  签名: 可居 (同伦 (连续映射.id X) (连续映射.id X))
  定义体: ⟨Homotopy.refl _⟩

Depends on / 依赖: Homotopy, Homotopy.refl
-/
instance : Inhabited (Homotopy (ContinuousMap.id X) (ContinuousMap.id X)) :=
  ⟨Homotopy.refl _⟩

/-- Given a `ContinuousMap.Homotopy f₀ f₁`, we can define a `ContinuousMap.Homotopy f₁ f₀` by
reversing the homotopy.
-/
@[simps]
/--
Definition of `symm` / `symm` 的定义

English:
definition symm
  signature: {f₀ f₁ : C(X, Y)} (F : Homotopy f₀ f₁)
  body: F (σ x.1, x.2)
  map_zero_left := by simp
  map_one_left := by norm_num

@[simp]

中文:
定义 symm
  签名: {f₀ f₁ : C(X, Y)} (F : 同伦 f₀ f₁)
  定义体: F (σ x.1, x.2)
  map_zero_left := by simp
  map_one_left := by norm_num

@[simp]
-/
def symm {f₀ f₁ : C(X, Y)} (F : Homotopy f₀ f₁) : Homotopy f₁ f₀ where
  toFun x := F (σ x.1, x.2)
  map_zero_left := by simp
  map_one_left := by norm_num

@[simp]
/--
theorem `symm_symm` / 定理 `symm_symm`

English:
theorem symm_symm
  given: {f₀ f₁ : C(X, Y)} (F : Homotopy f₀ f₁)
  statement: F.symm.symm = F
  proof: by
  ext
  simp

中文:
定理 symm_symm
  条件: {f₀ f₁ : C(X, Y)} (F : 同伦 f₀ f₁)
  结论: F.symm.symm = F
  证明: by
  ext
  simp
-/
theorem symm_symm {f₀ f₁ : C(X, Y)} (F : Homotopy f₀ f₁) : F.symm.symm = F := by
  ext
  simp

/--
theorem `symm_bijective` / 定理 `symm_bijective`

English:
theorem symm_bijective
  given: {f₀ f₁ : C(X, Y)}
  proof: Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

中文:
定理 symm_bijective
  条件: {f₀ f₁ : C(X, Y)}
  证明: Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

Depends on / 依赖: Function, Function.bijective_iff_has_inverse.mpr, bijective_iff_has_inverse, symm_symm
-/
theorem symm_bijective {f₀ f₁ : C(X, Y)} :
    Function.Bijective (Homotopy.symm : Homotopy f₀ f₁ -> Homotopy f₁ f₀) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

/--
Definition of `trans` / `trans` 的定义

English:
definition trans
  signature: {f₀ f₁ f₂ : C(X, Y)} (F : Homotopy f₀ f₁) (G : Homotopy f₁ f₂)
  body: if (x.1 : Real) <= 1 / 2 then F.extend (2 * x.1) x.2 else G.extend (2 * x.1 - 1) x.2
  continuous_toFun :=
    continuous_if_le (by fun_prop) continuous_const
      (F.continuous.comp (by fun_prop)).continuousOn
      (G.continuous.comp (by fun_prop)).continuousOn (fun x hx => by norm_num [hx])
  ma

中文:
定义 trans
  签名: {f₀ f₁ f₂ : C(X, Y)} (F : 同伦 f₀ f₁) (G : 同伦 f₁ f₂)
  定义体: if (x.1 : Real) <= 1 / 2 then F.extend (2 * x.1) x.2 else G.extend (2 * x.1 - 1) x.2
  continuous_toFun :=
    continuous_if_le (by fun_prop) continuous_const
      (F.continuous.comp (by fun_prop)).continuousOn
      (G.continuous.comp (by fun_prop)).continuousOn (fun x hx => by norm_num [hx])
  ma

Depends on / 依赖: F.extend, G.extend, extend
-/
def trans {f₀ f₁ f₂ : C(X, Y)} (F : Homotopy f₀ f₁) (G : Homotopy f₁ f₂) : Homotopy f₀ f₂ where
  toFun x := if (x.1 : Real) <= 1 / 2 then F.extend (2 * x.1) x.2 else G.extend (2 * x.1 - 1) x.2
  continuous_toFun :=
    continuous_if_le (by fun_prop) continuous_const
      (F.continuous.comp (by fun_prop)).continuousOn
      (G.continuous.comp (by fun_prop)).continuousOn (fun x hx => by norm_num [hx])
  map_zero_left x := by norm_num
  map_one_left x := by norm_num

/--
theorem `trans_apply` / 定理 `trans_apply`

English:
theorem trans_apply
  given: {f₀ f₁ f₂ : C(X, Y)} (F : Homotopy f₀ f₁) (G : Homotopy f₁ f₂) (x : I × X)
  proof: show ite _ _ _ = _ by
    split_ifs <;>
      · rw [extend, ContinuousMap.coe_IccExtend, Set.IccExtend_of_mem]
        rfl

中文:
定理 trans_apply
  条件: {f₀ f₁ f₂ : C(X, Y)} (F : 同伦 f₀ f₁) (G : 同伦 f₁ f₂) (x : I × X)
  证明: show ite _ _ _ = _ by
    split_ifs <;>
      · rw [extend, ContinuousMap.coe_IccExtend, Set.IccExtend_of_mem]
        rfl

Depends on / 依赖: ContinuousMap, ContinuousMap.coe_IccExtend, IccExtend_of_mem, Set.IccExtend_of_mem, coe_IccExtend, extend, split_ifs
-/
theorem trans_apply {f₀ f₁ f₂ : C(X, Y)} (F : Homotopy f₀ f₁) (G : Homotopy f₁ f₂) (x : I × X) :
    (F.trans G) x =
      if h : (x.1 : Real) <= 1 / 2 then
        F (⟨2 * x.1, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨x.1.2.1, h⟩⟩, x.2)
      else
        G (⟨2 * x.1 - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, x.1.2.2⟩⟩, x.2) :=
  show ite _ _ _ = _ by
    split_ifs <;>
      · rw [extend, ContinuousMap.coe_IccExtend, Set.IccExtend_of_mem]
        rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `symm_trans` / 定理 `symm_trans`

English:
theorem symm_trans
  given: {f₀ f₁ f₂ : C(X, Y)} (F : Homotopy f₀ f₁) (G : Homotopy f₁ f₂)
  proof: by
  ext ⟨t, _⟩
  rw [trans_apply]; rw [symm_apply]; rw [trans_apply]
  simp only [coe_symm_eq, symm_apply]
  split_ifs with h₁ h₂ h₂
  · have ht : (t : Real) = 1 / 2 := by linarith
    norm_num [ht]
  · congr 2
    apply Subtype.ext
    simp only [coe_symm_eq]
    linarith
  · congr 2
    apply Sub

中文:
定理 symm_trans
  条件: {f₀ f₁ f₂ : C(X, Y)} (F : 同伦 f₀ f₁) (G : 同伦 f₁ f₂)
  证明: by
  ext ⟨t, _⟩
  rw [trans_apply]; rw [symm_apply]; rw [trans_apply]
  simp only [coe_symm_eq, symm_apply]
  split_ifs with h₁ h₂ h₂
  · have ht : (t : Real) = 1 / 2 := by linarith
    norm_num [ht]
  · congr 2
    apply Subtype.ext
    simp only [coe_symm_eq]
    linarith
  · congr 2
    apply Sub

Depends on / 依赖: Subtype, Subtype.ext, coe_symm_eq, split_ifs, symm_apply, trans_apply
-/
theorem symm_trans {f₀ f₁ f₂ : C(X, Y)} (F : Homotopy f₀ f₁) (G : Homotopy f₁ f₂) :
    (F.trans G).symm = G.symm.trans F.symm := by
  ext ⟨t, _⟩
  rw [trans_apply]; rw [symm_apply]; rw [trans_apply]
  simp only [coe_symm_eq, symm_apply]
  split_ifs with h₁ h₂ h₂
  · have ht : (t : Real) = 1 / 2 := by linarith
    norm_num [ht]
  · congr 2
    apply Subtype.ext
    simp only [coe_symm_eq]
    linarith
  · congr 2
    apply Subtype.ext
    simp only [coe_symm_eq]
    linarith
  · exfalso
    linarith

/-- Casting a `ContinuousMap.Homotopy f₀ f₁` to a `ContinuousMap.Homotopy g₀ g₁` where `f₀ = g₀`
and `f₁ = g₁`.
-/
@[simps]
/--
Definition of `cast` / `cast` 的定义

English:
definition cast
  signature: {f₀ f₁ g₀ g₁ : C(X, Y)} (F : Homotopy f₀ f₁) (h₀ : f₀ = g₀) (h₁ : f₁ = g₁)
  body: F
  map_zero_left := by simp [← h₀]
  map_one_left := by simp [← h₁]

中文:
定义 cast
  签名: {f₀ f₁ g₀ g₁ : C(X, Y)} (F : 同伦 f₀ f₁) (h₀ : f₀ = g₀) (h₁ : f₁ = g₁)
  定义体: F
  map_zero_left := by simp [← h₀]
  map_one_left := by simp [← h₁]
-/
def cast {f₀ f₁ g₀ g₁ : C(X, Y)} (F : Homotopy f₀ f₁) (h₀ : f₀ = g₀) (h₁ : f₁ = g₁) :
    Homotopy g₀ g₁ where
  toFun := F
  map_zero_left := by simp [← h₀]
  map_one_left := by simp [← h₁]

/-- If we have a `ContinuousMap.Homotopy g₀ g₁` and a `ContinuousMap.Homotopy f₀ f₁`, then we can
compose them and get a `ContinuousMap.Homotopy (g₀.comp f₀) (g₁.comp f₁)`.
-/
@[simps]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: {f₀ f₁ : C(X, Y)} {g₀ g₁ : C(Y, Z)} (G : Homotopy g₀ g₁) (F : Homotopy f₀ f₁)
  body: G (x.1, F x)
  map_zero_left := by simp
  map_one_left := by simp

中文:
定义 comp
  签名: {f₀ f₁ : C(X, Y)} {g₀ g₁ : C(Y, Z)} (G : 同伦 g₀ g₁) (F : 同伦 f₀ f₁)
  定义体: G (x.1, F x)
  map_zero_left := by simp
  map_one_left := by simp
-/
def comp {f₀ f₁ : C(X, Y)} {g₀ g₁ : C(Y, Z)} (G : Homotopy g₀ g₁) (F : Homotopy f₀ f₁) :
    Homotopy (g₀.comp f₀) (g₁.comp f₁) where
  toFun x := G (x.1, F x)
  map_zero_left := by simp
  map_one_left := by simp

/-- Composition of a `ContinuousMap.Homotopy g₀ g₁` and `f : C(X, Y)` as a homotopy between
`g₀.comp f` and `g₁.comp f`. -/
@[simps!]
/--
Definition of `compContinuousMap` / `compContinuousMap` 的定义

English:
definition compContinuousMap
  signature: {g₀ g₁ : C(Y, Z)} (G : Homotopy g₀ g₁) (f : C(X, Y))
  body: G.comp (.refl f)

中文:
定义 compContinuousMap
  签名: {g₀ g₁ : C(Y, Z)} (G : 同伦 g₀ g₁) (f : C(X, Y))
  定义体: G.comp (.refl f)

Depends on / 依赖: G.comp
-/
def compContinuousMap {g₀ g₁ : C(Y, Z)} (G : Homotopy g₀ g₁) (f : C(X, Y)) :
    Homotopy (g₀.comp f) (g₁.comp f) :=
  G.comp (.refl f)

/-- Let `F` be a homotopy between `f₀ : C(X, Y)` and `f₁ : C(X, Y)`. Let `G` be a homotopy between
`g₀ : C(X, Z)` and `g₁ : C(X, Z)`. Then `F.prodMk G` is the homotopy between `f₀.prodMk g₀` and
`f₁.prodMk g₁` that sends `p` to `(F p, G p)`. -/
nonrec def prodMk {f₀ f₁ : C(X, Y)} {g₀ g₁ : C(X, Z)} (F : Homotopy f₀ f₁) (G : Homotopy g₀ g₁) :
    Homotopy (f₀.prodMk g₀) (f₁.prodMk g₁) where
  toContinuousMap := F.prodMk G
  map_zero_left _ := Prod.ext (F.map_zero_left _) (G.map_zero_left _)
  map_one_left _ := Prod.ext (F.map_one_left _) (G.map_one_left _)

/--
Definition of `prodMap` / `prodMap` 的定义

English:
definition prodMap
  signature: {f₀ f₁ : C(X, Y)} {g₀ g₁ : C(Z, Z')} (F : Homotopy f₀ f₁) (G : Homotopy g₀ g₁)
  body: .prodMk (F.compContinuousMap .fst) (G.compContinuousMap .snd)

中文:
定义 prodMap
  签名: {f₀ f₁ : C(X, Y)} {g₀ g₁ : C(Z, Z')} (F : 同伦 f₀ f₁) (G : 同伦 g₀ g₁)
  定义体: .prodMk (F.compContinuousMap .fst) (G.compContinuousMap .snd)

Depends on / 依赖: F.compContinuousMap, G.compContinuousMap, compContinuousMap, prodMk
-/
def prodMap {f₀ f₁ : C(X, Y)} {g₀ g₁ : C(Z, Z')} (F : Homotopy f₀ f₁) (G : Homotopy g₀ g₁) :
    Homotopy (f₀.prodMap g₀) (f₁.prodMap g₁) :=
  .prodMk (F.compContinuousMap .fst) (G.compContinuousMap .snd)

/--
Definition of `pi` / `pi` 的定义

English:
definition pi
  signature: {Y : ι -> Type*} [forall i, TopologicalSpace (Y i)] {f₀ f₁ : forall i, C(X, Y i)}
  body: .pi fun i => F i
  map_zero_left x := funext fun i => (F i).map_zero_left x
  map_one_left x := funext fun i => (F i).map_one_left x

中文:
定义 pi
  签名: {Y : ι -> 类型} [对任意 i, 拓扑空间 (Y i)] {f₀ f₁ : 对任意 i, C(X, Y i)}
  定义体: .pi fun i => F i
  map_zero_left x := funext fun i => (F i).map_zero_left x
  map_one_left x := funext fun i => (F i).map_one_left x
-/
protected def pi {Y : ι -> Type*} [forall i, TopologicalSpace (Y i)] {f₀ f₁ : forall i, C(X, Y i)}
    (F : forall i, Homotopy (f₀ i) (f₁ i)) :
    Homotopy (.pi f₀) (.pi f₁) where
  toContinuousMap := .pi fun i => F i
  map_zero_left x := funext fun i => (F i).map_zero_left x
  map_one_left x := funext fun i => (F i).map_one_left x

/--
Definition of `piMap` / `piMap` 的定义

English:
definition piMap
  signature: {X Y : ι -> Type*} [forall i, TopologicalSpace (X i)] [forall i, TopologicalSpace (Y i)]
  body: .pi fun i => (F i).compContinuousMap .eval i

中文:
定义 piMap
  签名: {X Y : ι -> 类型} [对任意 i, 拓扑空间 (X i)] [对任意 i, 拓扑空间 (Y i)]
  定义体: .pi fun i => (F i).compContinuousMap .eval i
-/
protected def piMap {X Y : ι -> Type*} [forall i, TopologicalSpace (X i)] [forall i, TopologicalSpace (Y i)]
    {f₀ f₁ : forall i, C(X i, Y i)} (F : forall i, Homotopy (f₀ i) (f₁ i)) :
    Homotopy (.piMap f₀) (.piMap f₁) :=
.pi fun i => (F i).compContinuousMap .eval i

end Homotopy

/--
Definition of `Homotopic` / `Homotopic` 的定义

English:
definition Homotopic
  signature: (f₀ f₁ : C(X, Y))
  body: Nonempty (Homotopy f₀ f₁)

中文:
定义 同伦
  签名: (f₀ f₁ : C(X, Y))
  定义体: Nonempty (Homotopy f₀ f₁)

Depends on / 依赖: Homotopy, Nonempty
-/
def Homotopic (f₀ f₁ : C(X, Y)) : Prop :=
  Nonempty (Homotopy f₀ f₁)

namespace Homotopic

@[refl]
/--
theorem `refl` / 定理 `refl`

English:
theorem refl
  given: (f : C(X, Y))
  statement: Homotopic f f
  proof: ⟨Homotopy.refl f⟩

@[symm]

中文:
定理 refl
  条件: (f : C(X, Y))
  结论: 同伦 f f
  证明: ⟨Homotopy.refl f⟩

@[symm]

Depends on / 依赖: Homotopy, Homotopy.refl
-/
theorem refl (f : C(X, Y)) : Homotopic f f :=
  ⟨Homotopy.refl f⟩

@[symm]
/--
theorem `symm` / 定理 `symm`

English:
theorem symm
  given: ⦃f g
  statement: C(X, Y)⦄ (h : Homotopic f g) : Homotopic g f
  proof: h.map Homotopy.symm

@[trans]

中文:
定理 symm
  条件: ⦃f g
  结论: C(X, Y)⦄ (h : 同伦 f g) : 同伦 g f
  证明: h.map Homotopy.symm

@[trans]

Depends on / 依赖: Homotopy, Homotopy.symm, h.map
-/
theorem symm ⦃f g : C(X, Y)⦄ (h : Homotopic f g) : Homotopic g f :=
  h.map Homotopy.symm

@[trans]
/--
theorem `trans` / 定理 `trans`

English:
theorem trans
  given: ⦃f g h
  statement: C(X, Y)⦄ (h₀ : Homotopic f g) (h₁ : Homotopic g h) : Homotopic f h
  proof: h₀.map2 Homotopy.trans h₁

中文:
定理 trans
  条件: ⦃f g h
  结论: C(X, Y)⦄ (h₀ : 同伦 f g) (h₁ : 同伦 g h) : 同伦 f h
  证明: h₀.map2 Homotopy.trans h₁

Depends on / 依赖: Homotopy, Homotopy.trans
-/
theorem trans ⦃f g h : C(X, Y)⦄ (h₀ : Homotopic f g) (h₁ : Homotopic g h) : Homotopic f h :=
  h₀.map2 Homotopy.trans h₁

/--
theorem `comp` / 定理 `comp`

English:
theorem comp
  given: {g₀ g₁ : C(Y, Z)} {f₀ f₁ : C(X, Y)} (hg : Homotopic g₀ g₁) (hf : Homotopic f₀ f₁)
  proof: hg.map2 Homotopy.comp hf

中文:
定理 comp
  条件: {g₀ g₁ : C(Y, Z)} {f₀ f₁ : C(X, Y)} (hg : 同伦 g₀ g₁) (hf : 同伦 f₀ f₁)
  证明: hg.map2 Homotopy.comp hf

Depends on / 依赖: Homotopy, Homotopy.comp, hg.map2
-/
theorem comp {g₀ g₁ : C(Y, Z)} {f₀ f₁ : C(X, Y)} (hg : Homotopic g₀ g₁) (hf : Homotopic f₀ f₁) :
    Homotopic (g₀.comp f₀) (g₁.comp f₁) :=
  hg.map2 Homotopy.comp hf

/--
theorem `equivalence` / 定理 `equivalence`

English:
theorem equivalence
  statement: Equivalence (@Homotopic X Y _ _)
  proof: ⟨refl, by apply symm, by apply trans⟩

nonrec theorem prodMk {f₀ f₁ : C(X, Y)} {g₀ g₁ : C(X, Z)} :
    Homotopic f₀ f₁ -> Homotopic g₀ g₁ -> Homotopic (f₀.prodMk g₀) (f₁.prodMk g₁)
  | ⟨F⟩, ⟨G⟩ => ⟨F.prodMk G⟩

nonrec theorem prodMap {f₀ f₁ : C(X, Y)} {g₀ g₁ : C(Z, Z')} :
    Homotopic f₀ f₁ -> Homo

中文:
定理 equivalence
  结论: 等价 (@同伦 X Y _ _)
  证明: ⟨refl, by apply symm, by apply trans⟩

nonrec theorem prodMk {f₀ f₁ : C(X, Y)} {g₀ g₁ : C(X, Z)} :
    Homotopic f₀ f₁ -> Homotopic g₀ g₁ -> Homotopic (f₀.prodMk g₀) (f₁.prodMk g₁)
  | ⟨F⟩, ⟨G⟩ => ⟨F.prodMk G⟩

nonrec theorem prodMap {f₀ f₁ : C(X, Y)} {g₀ g₁ : C(Z, Z')} :
    Homotopic f₀ f₁ -> Homo
-/
theorem equivalence : Equivalence (@Homotopic X Y _ _) :=
  ⟨refl, by apply symm, by apply trans⟩

nonrec theorem prodMk {f₀ f₁ : C(X, Y)} {g₀ g₁ : C(X, Z)} :
    Homotopic f₀ f₁ -> Homotopic g₀ g₁ -> Homotopic (f₀.prodMk g₀) (f₁.prodMk g₁)
  | ⟨F⟩, ⟨G⟩ => ⟨F.prodMk G⟩

nonrec theorem prodMap {f₀ f₁ : C(X, Y)} {g₀ g₁ : C(Z, Z')} :
    Homotopic f₀ f₁ -> Homotopic g₀ g₁ -> Homotopic (f₀.prodMap g₀) (f₁.prodMap g₁)
  | ⟨F⟩, ⟨G⟩ => ⟨F.prodMap G⟩

/--
theorem `pi` / 定理 `pi`

English:
theorem pi
  statement: {Y : ι -> Type*} [forall i, TopologicalSpace (Y i)] {f₀ f₁ : forall i, C(X, Y i)}
  proof: ⟨.pi fun i => (F i).some⟩

中文:
定理 pi
  结论: {Y : ι -> 类型} [对任意 i, 拓扑空间 (Y i)] {f₀ f₁ : 对任意 i, C(X, Y i)}
  证明: ⟨.pi fun i => (F i).some⟩
-/
protected theorem pi {Y : ι -> Type*} [forall i, TopologicalSpace (Y i)] {f₀ f₁ : forall i, C(X, Y i)}
    (F : forall i, Homotopic (f₀ i) (f₁ i)) :
    Homotopic (.pi f₀) (.pi f₁) :=
  ⟨.pi fun i => (F i).some⟩

/--
theorem `piMap` / 定理 `piMap`

English:
theorem piMap
  statement: {X Y : ι -> Type*} [forall i, TopologicalSpace (X i)]
  proof: .pi fun i => .comp (F i) (.refl <| .eval i)

中文:
定理 piMap
  结论: {X Y : ι -> 类型} [对任意 i, 拓扑空间 (X i)]
  证明: .pi fun i => .comp (F i) (.refl <| .eval i)
-/
protected theorem piMap {X Y : ι -> Type*} [forall i, TopologicalSpace (X i)]
    [forall i, TopologicalSpace (Y i)] {f₀ f₁ : forall i, C(X i, Y i)} (F : forall i, Homotopic (f₀ i) (f₁ i)) :
    Homotopic (.piMap f₀) (.piMap f₁) :=
  .pi fun i => .comp (F i) (.refl <| .eval i)

end Homotopic

/--
Definition of `HomotopyWith` / `HomotopyWith` 的定义

English:
structure HomotopyWith
  parameters: (f₀ f₁ : C(X, Y)) (P : C(X, Y) -> Prop)
  extends: Homotopy f₀ f₁
  axioms and operations (1):
    - prop' : forall t, P ⟨fun x => toFun (t, x), continuous_toFun.comp (by fun_prop)⟩

中文:
结构 HomotopyWith
  参数: (f₀ f₁ : C(X, Y)) (P : C(X, Y) -> 命题)
  继承: 同伦 f₀ f₁
  公理与运算 (1 个):
    - prop' : 对任意 t, P ⟨fun x => toFun (t, x), continuous_toFun.comp (by fun_prop)⟩
-/
structure HomotopyWith (f₀ f₁ : C(X, Y)) (P : C(X, Y) -> Prop) extends Homotopy f₀ f₁ where
  -- TODO: use `toHomotopy.curry t`
  /-- the intermediate maps of the homotopy satisfy the property -/
  prop' : forall t, P ⟨fun x => toFun (t, x), continuous_toFun.comp (by fun_prop)⟩

namespace HomotopyWith

section

variable {f₀ f₁ : C(X, Y)} {P : C(X, Y) -> Prop}

/--
Instance `instFunLike` / 实例 `instFunLike`

English:
instance instFunLike
  signature: : FunLike (HomotopyWith f₀ f₁ P) (I × X) Y where
  body: ⇑F.toHomotopy
  coe_injective
  | ⟨⟨⟨_, _⟩, _, _⟩, _⟩, ⟨⟨⟨_, _⟩, _, _⟩, _⟩, rfl => rfl

中文:
实例 instFunLike
  签名: : 函数状 (HomotopyWith f₀ f₁ P) (I × X) Y where
  定义体: ⇑F.toHomotopy
  coe_injective
  | ⟨⟨⟨_, _⟩, _, _⟩, _⟩, ⟨⟨⟨_, _⟩, _, _⟩, _⟩, rfl => rfl

Depends on / 依赖: F.toHomotopy, toHomotopy
-/
instance instFunLike : FunLike (HomotopyWith f₀ f₁ P) (I × X) Y where
  coe F := ⇑F.toHomotopy
  coe_injective
  | ⟨⟨⟨_, _⟩, _, _⟩, _⟩, ⟨⟨⟨_, _⟩, _, _⟩, _⟩, rfl => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HomotopyLike (HomotopyWith f₀ f₁ P) f₀ f₁
  body: F.continuous_toFun
  map_zero_left F := F.map_zero_left
  map_one_left F := F.map_one_left

中文:
实例 :
  签名: HomotopyLike (HomotopyWith f₀ f₁ P) f₀ f₁
  定义体: F.continuous_toFun
  map_zero_left F := F.map_zero_left
  map_one_left F := F.map_one_left

Depends on / 依赖: F.continuous_toFun, continuous_toFun
-/
instance : HomotopyLike (HomotopyWith f₀ f₁ P) f₀ f₁ where
  map_continuous F := F.continuous_toFun
  map_zero_left F := F.map_zero_left
  map_one_left F := F.map_one_left

/--
theorem `coeFn_injective` / 定理 `coeFn_injective`

English:
theorem coeFn_injective
  statement: @Function.Injective (HomotopyWith f₀ f₁ P) (I × X -> Y) (⇑)
  proof: DFunLike.coe_injective

@[ext]

中文:
定理 coeFn_injective
  结论: @函数.单射 (HomotopyWith f₀ f₁ P) (I × X -> Y) (⇑)
  证明: DFunLike.coe_injective

@[ext]

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective
-/
theorem coeFn_injective : @Function.Injective (HomotopyWith f₀ f₁ P) (I × X -> Y) (⇑) :=
  DFunLike.coe_injective

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {F G : HomotopyWith f₀ f₁ P} (h : forall x, F x = G x)
  statement: F = G
  proof: DFunLike.ext F G h

中文:
定理 ext
  条件: {F G : HomotopyWith f₀ f₁ P} (h : 对任意 x, F x = G x)
  结论: F = G
  证明: DFunLike.ext F G h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {F G : HomotopyWith f₀ f₁ P} (h : forall x, F x = G x) : F = G := DFunLike.ext F G h

/--
Definition of `Simps.apply` / `Simps.apply` 的定义

English:
definition Simps.apply
  signature: (F : HomotopyWith f₀ f₁ P)
  body: F

initialize_simps_projections HomotopyWith (toFun -> apply, -toHomotopy_toContinuousMap)

@[continuity]

中文:
定义 Simps.apply
  签名: (F : HomotopyWith f₀ f₁ P)
  定义体: F

initialize_simps_projections HomotopyWith (toFun -> apply, -toHomotopy_toContinuousMap)

@[continuity]
-/
def Simps.apply (F : HomotopyWith f₀ f₁ P) : I × X -> Y := F

initialize_simps_projections HomotopyWith (toFun -> apply, -toHomotopy_toContinuousMap)

@[continuity]
/--
theorem `continuous` / 定理 `continuous`

English:
theorem continuous
  given: (F : HomotopyWith f₀ f₁ P)
  statement: Continuous F
  proof: F.continuous_toFun

@[simp]

中文:
定理 continuous
  条件: (F : HomotopyWith f₀ f₁ P)
  结论: 连续 F
  证明: F.continuous_toFun

@[simp]
-/
protected theorem continuous (F : HomotopyWith f₀ f₁ P) : Continuous F :=
  F.continuous_toFun

@[simp]
/--
theorem `apply_zero` / 定理 `apply_zero`

English:
theorem apply_zero
  given: (F : HomotopyWith f₀ f₁ P) (x : X)
  statement: F (0, x) = f₀ x
  proof: F.map_zero_left x

@[simp]

中文:
定理 apply_zero
  条件: (F : HomotopyWith f₀ f₁ P) (x : X)
  结论: F (0, x) = f₀ x
  证明: F.map_zero_left x

@[simp]

Depends on / 依赖: F.map_zero_left, map_zero_left
-/
theorem apply_zero (F : HomotopyWith f₀ f₁ P) (x : X) : F (0, x) = f₀ x :=
  F.map_zero_left x

@[simp]
/--
theorem `apply_one` / 定理 `apply_one`

English:
theorem apply_one
  given: (F : HomotopyWith f₀ f₁ P) (x : X)
  statement: F (1, x) = f₁ x
  proof: F.map_one_left x

中文:
定理 apply_one
  条件: (F : HomotopyWith f₀ f₁ P) (x : X)
  结论: F (1, x) = f₁ x
  证明: F.map_one_left x

Depends on / 依赖: F.map_one_left, map_one_left
-/
theorem apply_one (F : HomotopyWith f₀ f₁ P) (x : X) : F (1, x) = f₁ x :=
  F.map_one_left x

/--
theorem `coe_toContinuousMap` / 定理 `coe_toContinuousMap`

English:
theorem coe_toContinuousMap
  given: (F : HomotopyWith f₀ f₁ P)
  statement: ⇑F.toContinuousMap = F
  proof: rfl

@[simp]

中文:
定理 coe_toContinuousMap
  条件: (F : HomotopyWith f₀ f₁ P)
  结论: ⇑F.toContinuousMap = F
  证明: rfl

@[simp]
-/
theorem coe_toContinuousMap (F : HomotopyWith f₀ f₁ P) : ⇑F.toContinuousMap = F :=
  rfl

@[simp]
/--
theorem `coe_toHomotopy` / 定理 `coe_toHomotopy`

English:
theorem coe_toHomotopy
  given: (F : HomotopyWith f₀ f₁ P)
  statement: ⇑F.toHomotopy = F
  proof: rfl

中文:
定理 coe_toHomotopy
  条件: (F : HomotopyWith f₀ f₁ P)
  结论: ⇑F.toHomotopy = F
  证明: rfl
-/
theorem coe_toHomotopy (F : HomotopyWith f₀ f₁ P) : ⇑F.toHomotopy = F :=
  rfl

/--
theorem `prop` / 定理 `prop`

English:
theorem prop
  given: (F : HomotopyWith f₀ f₁ P) (t : I)
  statement: P (F.toHomotopy.curry t)
  proof: F.prop' t

中文:
定理 prop
  条件: (F : HomotopyWith f₀ f₁ P) (t : I)
  结论: P (F.toHomotopy.curry t)
  证明: F.prop' t

Depends on / 依赖: F.prop
-/
theorem prop (F : HomotopyWith f₀ f₁ P) (t : I) : P (F.toHomotopy.curry t) := F.prop' t

/--
theorem `extendProp` / 定理 `extendProp`

English:
theorem extendProp
  given: (F : HomotopyWith f₀ f₁ P) (t : Real)
  statement: P (F.toHomotopy.extend t)
  proof: F.prop _

中文:
定理 extendProp
  条件: (F : HomotopyWith f₀ f₁ P) (t : 实数)
  结论: P (F.toHomotopy.extend t)
  证明: F.prop _

Depends on / 依赖: F.prop
-/
theorem extendProp (F : HomotopyWith f₀ f₁ P) (t : Real) : P (F.toHomotopy.extend t) := F.prop _

end

variable {P : C(X, Y) -> Prop}

/-- Given a continuous function `f`, and a proof `h : P f`, we can define a `HomotopyWith f f P` by
`F (t, x) = f x`
-/
@[simps!]
/--
Definition of `refl` / `refl` 的定义

English:
definition refl
  signature: (f : C(X, Y)) (hf : P f)
  body: Homotopy.refl f
  prop' := fun _ => hf

中文:
定义 refl
  签名: (f : C(X, Y)) (hf : P f)
  定义体: Homotopy.refl f
  prop' := fun _ => hf

Depends on / 依赖: Homotopy, Homotopy.refl
-/
def refl (f : C(X, Y)) (hf : P f) : HomotopyWith f f P where
  toHomotopy := Homotopy.refl f
  prop' := fun _ => hf

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (HomotopyWith (ContinuousMap.id X) (ContinuousMap.id X) fun _ => True)
  body: ⟨HomotopyWith.refl _ trivial⟩

中文:
实例 :
  签名: 可居 (HomotopyWith (连续映射.id X) (连续映射.id X) fun _ => 真)
  定义体: ⟨HomotopyWith.refl _ trivial⟩

Depends on / 依赖: HomotopyWith, HomotopyWith.refl
-/
instance : Inhabited (HomotopyWith (ContinuousMap.id X) (ContinuousMap.id X) fun _ => True) :=
  ⟨HomotopyWith.refl _ trivial⟩

/--
Given a `HomotopyWith f₀ f₁ P`, we can define a `HomotopyWith f₁ f₀ P` by reversing the homotopy.
-/
@[simps!]
/--
Definition of `symm` / `symm` 的定义

English:
definition symm
  signature: {f₀ f₁ : C(X, Y)} (F : HomotopyWith f₀ f₁ P)
  body: F.toHomotopy.symm
  prop' := fun t => F.prop (σ t)

@[simp]

中文:
定义 symm
  签名: {f₀ f₁ : C(X, Y)} (F : HomotopyWith f₀ f₁ P)
  定义体: F.toHomotopy.symm
  prop' := fun t => F.prop (σ t)

@[simp]

Depends on / 依赖: F.toHomotopy.symm, toHomotopy
-/
def symm {f₀ f₁ : C(X, Y)} (F : HomotopyWith f₀ f₁ P) : HomotopyWith f₁ f₀ P where
  toHomotopy := F.toHomotopy.symm
  prop' := fun t => F.prop (σ t)

@[simp]
/--
theorem `symm_symm` / 定理 `symm_symm`

English:
theorem symm_symm
  given: {f₀ f₁ : C(X, Y)} (F : HomotopyWith f₀ f₁ P)
  statement: F.symm.symm = F
  proof: ext Homotopy.congr_fun Homotopy.symm_symm _

中文:
定理 symm_symm
  条件: {f₀ f₁ : C(X, Y)} (F : HomotopyWith f₀ f₁ P)
  结论: F.symm.symm = F
  证明: ext Homotopy.congr_fun Homotopy.symm_symm _

Depends on / 依赖: Homotopy, Homotopy.congr_fun, Homotopy.symm_symm, congr_fun, symm_symm
-/
theorem symm_symm {f₀ f₁ : C(X, Y)} (F : HomotopyWith f₀ f₁ P) : F.symm.symm = F :=
ext Homotopy.congr_fun Homotopy.symm_symm _

/--
theorem `symm_bijective` / 定理 `symm_bijective`

English:
theorem symm_bijective
  given: {f₀ f₁ : C(X, Y)}
  proof: Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

中文:
定理 symm_bijective
  条件: {f₀ f₁ : C(X, Y)}
  证明: Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

Depends on / 依赖: Function, Function.bijective_iff_has_inverse.mpr, bijective_iff_has_inverse, symm_symm
-/
theorem symm_bijective {f₀ f₁ : C(X, Y)} :
    Function.Bijective (HomotopyWith.symm : HomotopyWith f₀ f₁ P -> HomotopyWith f₁ f₀ P) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

/--
Definition of `trans` / `trans` 的定义

English:
definition trans
  signature: {f₀ f₁ f₂ : C(X, Y)} (F : HomotopyWith f₀ f₁ P) (G : HomotopyWith f₁ f₂ P)
  body: { F.toHomotopy.trans G.toHomotopy with
    prop' := fun t => by
      simp only [Homotopy.trans]
      change P ⟨fun _ => ite ((t : Real) <= _) _ _, _⟩
      split_ifs
      · exact F.extendProp _
      · exact G.extendProp _ }

中文:
定义 trans
  签名: {f₀ f₁ f₂ : C(X, Y)} (F : HomotopyWith f₀ f₁ P) (G : HomotopyWith f₁ f₂ P)
  定义体: { F.toHomotopy.trans G.toHomotopy with
    prop' := fun t => by
      simp only [Homotopy.trans]
      change P ⟨fun _ => ite ((t : Real) <= _) _ _, _⟩
      split_ifs
      · exact F.extendProp _
      · exact G.extendProp _ }

Depends on / 依赖: F.extendProp, F.toHomotopy.trans, G.extendProp, G.toHomotopy, Homotopy, Homotopy.trans, extendProp, split_ifs, toHomotopy
-/
def trans {f₀ f₁ f₂ : C(X, Y)} (F : HomotopyWith f₀ f₁ P) (G : HomotopyWith f₁ f₂ P) :
    HomotopyWith f₀ f₂ P :=
  { F.toHomotopy.trans G.toHomotopy with
    prop' := fun t => by
      simp only [Homotopy.trans]
      change P ⟨fun _ => ite ((t : Real) <= _) _ _, _⟩
      split_ifs
      · exact F.extendProp _
      · exact G.extendProp _ }

/--
theorem `trans_apply` / 定理 `trans_apply`

English:
theorem trans_apply
  statement: {f₀ f₁ f₂ : C(X, Y)} (F : HomotopyWith f₀ f₁ P) (G : HomotopyWith f₁ f₂ P)
  proof: Homotopy.trans_apply _ _ _

中文:
定理 trans_apply
  结论: {f₀ f₁ f₂ : C(X, Y)} (F : HomotopyWith f₀ f₁ P) (G : HomotopyWith f₁ f₂ P)
  证明: Homotopy.trans_apply _ _ _

Depends on / 依赖: Homotopy, Homotopy.trans_apply, trans_apply
-/
theorem trans_apply {f₀ f₁ f₂ : C(X, Y)} (F : HomotopyWith f₀ f₁ P) (G : HomotopyWith f₁ f₂ P)
    (x : I × X) :
    (F.trans G) x =
      if h : (x.1 : Real) <= 1 / 2 then
        F (⟨2 * x.1, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨x.1.2.1, h⟩⟩, x.2)
      else
        G (⟨2 * x.1 - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, x.1.2.2⟩⟩, x.2) :=
  Homotopy.trans_apply _ _ _

/--
theorem `symm_trans` / 定理 `symm_trans`

English:
theorem symm_trans
  given: {f₀ f₁ f₂ : C(X, Y)} (F : HomotopyWith f₀ f₁ P) (G : HomotopyWith f₁ f₂ P)
  proof: ext Homotopy.congr_fun Homotopy.symm_trans _ _

中文:
定理 symm_trans
  条件: {f₀ f₁ f₂ : C(X, Y)} (F : HomotopyWith f₀ f₁ P) (G : HomotopyWith f₁ f₂ P)
  证明: ext Homotopy.congr_fun Homotopy.symm_trans _ _

Depends on / 依赖: Homotopy, Homotopy.congr_fun, Homotopy.symm_trans, congr_fun, symm_trans
-/
theorem symm_trans {f₀ f₁ f₂ : C(X, Y)} (F : HomotopyWith f₀ f₁ P) (G : HomotopyWith f₁ f₂ P) :
    (F.trans G).symm = G.symm.trans F.symm :=
ext Homotopy.congr_fun Homotopy.symm_trans _ _

/-- Casting a `HomotopyWith f₀ f₁ P` to a `HomotopyWith g₀ g₁ P` where `f₀ = g₀` and `f₁ = g₁`.
-/
@[simps!]
/--
Definition of `cast` / `cast` 的定义

English:
definition cast
  signature: {f₀ f₁ g₀ g₁ : C(X, Y)} (F : HomotopyWith f₀ f₁ P) (h₀ : f₀ = g₀) (h₁ : f₁ = g₁)
  body: F.toHomotopy.cast h₀ h₁
  prop' := F.prop

中文:
定义 cast
  签名: {f₀ f₁ g₀ g₁ : C(X, Y)} (F : HomotopyWith f₀ f₁ P) (h₀ : f₀ = g₀) (h₁ : f₁ = g₁)
  定义体: F.toHomotopy.cast h₀ h₁
  prop' := F.prop

Depends on / 依赖: F.toHomotopy.cast, toHomotopy
-/
def cast {f₀ f₁ g₀ g₁ : C(X, Y)} (F : HomotopyWith f₀ f₁ P) (h₀ : f₀ = g₀) (h₁ : f₁ = g₁) :
    HomotopyWith g₀ g₁ P where
  toHomotopy := F.toHomotopy.cast h₀ h₁
  prop' := F.prop

end HomotopyWith

/--
Definition of `HomotopicWith` / `HomotopicWith` 的定义

English:
definition HomotopicWith
  signature: (f₀ f₁ : C(X, Y)) (P : C(X, Y) -> Prop)
  body: Nonempty (HomotopyWith f₀ f₁ P)

中文:
定义 HomotopicWith
  签名: (f₀ f₁ : C(X, Y)) (P : C(X, Y) -> 命题)
  定义体: Nonempty (HomotopyWith f₀ f₁ P)

Depends on / 依赖: HomotopyWith, Nonempty
-/
def HomotopicWith (f₀ f₁ : C(X, Y)) (P : C(X, Y) -> Prop) : Prop :=
  Nonempty (HomotopyWith f₀ f₁ P)

namespace HomotopicWith

variable {P : C(X, Y) -> Prop}

/--
theorem `refl` / 定理 `refl`

English:
theorem refl
  given: (f : C(X, Y)) (hf : P f)
  statement: HomotopicWith f f P
  proof: ⟨HomotopyWith.refl f hf⟩

@[symm]

中文:
定理 refl
  条件: (f : C(X, Y)) (hf : P f)
  结论: HomotopicWith f f P
  证明: ⟨HomotopyWith.refl f hf⟩

@[symm]

Depends on / 依赖: HomotopyWith, HomotopyWith.refl
-/
theorem refl (f : C(X, Y)) (hf : P f) : HomotopicWith f f P :=
  ⟨HomotopyWith.refl f hf⟩

@[symm]
/--
theorem `symm` / 定理 `symm`

English:
theorem symm
  given: ⦃f g
  statement: C(X, Y)⦄ (h : HomotopicWith f g P) : HomotopicWith g f P
  proof: ⟨h.some.symm⟩

中文:
定理 symm
  条件: ⦃f g
  结论: C(X, Y)⦄ (h : HomotopicWith f g P) : HomotopicWith g f P
  证明: ⟨h.some.symm⟩

Depends on / 依赖: h.some.symm
-/
theorem symm ⦃f g : C(X, Y)⦄ (h : HomotopicWith f g P) : HomotopicWith g f P :=
  ⟨h.some.symm⟩

-- Note: this was formerly tagged with `@[trans]`, and although the `trans` attribute accepted it
-- the `trans` tactic could not use it.
-- An update to the trans tactic coming in https://github.com/leanprover-community/mathlib4/pull/7014 will reject this attribute.
-- It could be restored by changing the argument order to `HomotopicWith P f g`.
@[trans]
/--
theorem `trans` / 定理 `trans`

English:
theorem trans
  given: ⦃f g h
  statement: C(X, Y)⦄ (h₀ : HomotopicWith f g P) (h₁ : HomotopicWith g h P) :
  proof: ⟨h₀.some.trans h₁.some⟩

中文:
定理 trans
  条件: ⦃f g h
  结论: C(X, Y)⦄ (h₀ : HomotopicWith f g P) (h₁ : HomotopicWith g h P) :
  证明: ⟨h₀.some.trans h₁.some⟩

Depends on / 依赖: some.trans
-/
theorem trans ⦃f g h : C(X, Y)⦄ (h₀ : HomotopicWith f g P) (h₁ : HomotopicWith g h P) :
    HomotopicWith f h P :=
  ⟨h₀.some.trans h₁.some⟩

end HomotopicWith

/--
Definition of `HomotopyRel` / `HomotopyRel` 的定义

English:
abbreviation HomotopyRel
  signature: (f₀ f₁ : C(X, Y)) (S : Set X)
  body: HomotopyWith f₀ f₁ fun f => forall x in S, f x = f₀ x

中文:
缩写 HomotopyRel
  签名: (f₀ f₁ : C(X, Y)) (S : 集合 X)
  定义体: HomotopyWith f₀ f₁ fun f => forall x in S, f x = f₀ x

Depends on / 依赖: HomotopyWith
-/
abbrev HomotopyRel (f₀ f₁ : C(X, Y)) (S : Set X) :=
  HomotopyWith f₀ f₁ fun f => forall x in S, f x = f₀ x

namespace HomotopyRel

section

variable {f₀ f₁ : C(X, Y)} {S : Set X}

/--
theorem `eq_fst` / 定理 `eq_fst`

English:
theorem eq_fst
  given: (F : HomotopyRel f₀ f₁ S) (t : I) {x : X} (hx : x in S)
  statement: F (t, x) = f₀ x
  proof: F.prop t x hx

中文:
定理 eq_fst
  条件: (F : HomotopyRel f₀ f₁ S) (t : I) {x : X} (hx : x in S)
  结论: F (t, x) = f₀ x
  证明: F.prop t x hx

Depends on / 依赖: F.prop
-/
theorem eq_fst (F : HomotopyRel f₀ f₁ S) (t : I) {x : X} (hx : x in S) : F (t, x) = f₀ x :=
  F.prop t x hx

/--
theorem `eq_snd` / 定理 `eq_snd`

English:
theorem eq_snd
  given: (F : HomotopyRel f₀ f₁ S) (t : I) {x : X} (hx : x in S)
  statement: F (t, x) = f₁ x
  proof: by
  rw [F.eq_fst t hx]; rw [← F.eq_fst 1 hx]; rw [F.apply_one]

中文:
定理 eq_snd
  条件: (F : HomotopyRel f₀ f₁ S) (t : I) {x : X} (hx : x in S)
  结论: F (t, x) = f₁ x
  证明: by
  rw [F.eq_fst t hx]; rw [← F.eq_fst 1 hx]; rw [F.apply_one]

Depends on / 依赖: F.apply_one, F.eq_fst, apply_one, eq_fst
-/
theorem eq_snd (F : HomotopyRel f₀ f₁ S) (t : I) {x : X} (hx : x in S) : F (t, x) = f₁ x := by
  rw [F.eq_fst t hx]; rw [← F.eq_fst 1 hx]; rw [F.apply_one]

/--
theorem `fst_eq_snd` / 定理 `fst_eq_snd`

English:
theorem fst_eq_snd
  given: (F : HomotopyRel f₀ f₁ S) {x : X} (hx : x in S)
  statement: f₀ x = f₁ x
  proof: F.eq_fst 0 hx ▸ F.eq_snd 0 hx

中文:
定理 fst_eq_snd
  条件: (F : HomotopyRel f₀ f₁ S) {x : X} (hx : x in S)
  结论: f₀ x = f₁ x
  证明: F.eq_fst 0 hx ▸ F.eq_snd 0 hx

Depends on / 依赖: F.eq_fst, F.eq_snd, eq_fst, eq_snd
-/
theorem fst_eq_snd (F : HomotopyRel f₀ f₁ S) {x : X} (hx : x in S) : f₀ x = f₁ x :=
  F.eq_fst 0 hx ▸ F.eq_snd 0 hx

end

variable {f₀ f₁ f₂ : C(X, Y)} {S : Set X}

/-- Given a map `f : C(X, Y)` and a set `S`, we can define a `HomotopyRel f f S` by setting
`F (t, x) = f x` for all `t`. This is defined using `HomotopyWith.refl`, but with the proof
filled in.
-/
@[simps!]
/--
Definition of `refl` / `refl` 的定义

English:
definition refl
  signature: (f : C(X, Y)) (S : Set X)
  body: HomotopyWith.refl f fun _ _ => rfl

中文:
定义 refl
  签名: (f : C(X, Y)) (S : 集合 X)
  定义体: HomotopyWith.refl f fun _ _ => rfl

Depends on / 依赖: HomotopyWith, HomotopyWith.refl
-/
def refl (f : C(X, Y)) (S : Set X) : HomotopyRel f f S :=
  HomotopyWith.refl f fun _ _ => rfl

/--
Given a `HomotopyRel f₀ f₁ S`, we can define a `HomotopyRel f₁ f₀ S` by reversing the homotopy.
-/
@[simps!]
/--
Definition of `symm` / `symm` 的定义

English:
definition symm
  signature: (F : HomotopyRel f₀ f₁ S)
  body: F.toHomotopy.symm
  prop' := fun _ _ hx => F.eq_snd _ hx

@[simp]

中文:
定义 symm
  签名: (F : HomotopyRel f₀ f₁ S)
  定义体: F.toHomotopy.symm
  prop' := fun _ _ hx => F.eq_snd _ hx

@[simp]

Depends on / 依赖: F.toHomotopy.symm, toHomotopy
-/
def symm (F : HomotopyRel f₀ f₁ S) : HomotopyRel f₁ f₀ S where
  toHomotopy := F.toHomotopy.symm
  prop' := fun _ _ hx => F.eq_snd _ hx

@[simp]
/--
theorem `symm_symm` / 定理 `symm_symm`

English:
theorem symm_symm
  given: (F : HomotopyRel f₀ f₁ S)
  statement: F.symm.symm = F
  proof: HomotopyWith.symm_symm F

中文:
定理 symm_symm
  条件: (F : HomotopyRel f₀ f₁ S)
  结论: F.symm.symm = F
  证明: HomotopyWith.symm_symm F

Depends on / 依赖: HomotopyWith, HomotopyWith.symm_symm, symm_symm
-/
theorem symm_symm (F : HomotopyRel f₀ f₁ S) : F.symm.symm = F :=
  HomotopyWith.symm_symm F

/--
theorem `symm_bijective` / 定理 `symm_bijective`

English:
theorem symm_bijective
  proof: Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

中文:
定理 symm_bijective
  证明: Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

Depends on / 依赖: Function, Function.bijective_iff_has_inverse.mpr, bijective_iff_has_inverse, symm_symm
-/
theorem symm_bijective :
    Function.Bijective (HomotopyRel.symm : HomotopyRel f₀ f₁ S -> HomotopyRel f₁ f₀ S) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

/--
Definition of `trans` / `trans` 的定义

English:
definition trans
  signature: (F : HomotopyRel f₀ f₁ S) (G : HomotopyRel f₁ f₂ S)
  body: F.toHomotopy.trans G.toHomotopy
  prop' t x hx := by
    simp only [Homotopy.trans]
    split_ifs
    · simp [HomotopyWith.extendProp F (2 * t) x hx, F.fst_eq_snd hx, G.fst_eq_snd hx]
    · simp [HomotopyWith.extendProp G (2 * t - 1) x hx, F.fst_eq_snd hx, G.fst_eq_snd hx]

中文:
定义 trans
  签名: (F : HomotopyRel f₀ f₁ S) (G : HomotopyRel f₁ f₂ S)
  定义体: F.toHomotopy.trans G.toHomotopy
  prop' t x hx := by
    simp only [Homotopy.trans]
    split_ifs
    · simp [HomotopyWith.extendProp F (2 * t) x hx, F.fst_eq_snd hx, G.fst_eq_snd hx]
    · simp [HomotopyWith.extendProp G (2 * t - 1) x hx, F.fst_eq_snd hx, G.fst_eq_snd hx]

Depends on / 依赖: F.toHomotopy.trans, G.toHomotopy, toHomotopy
-/
def trans (F : HomotopyRel f₀ f₁ S) (G : HomotopyRel f₁ f₂ S) : HomotopyRel f₀ f₂ S where
  toHomotopy := F.toHomotopy.trans G.toHomotopy
  prop' t x hx := by
    simp only [Homotopy.trans]
    split_ifs
    · simp [HomotopyWith.extendProp F (2 * t) x hx, F.fst_eq_snd hx, G.fst_eq_snd hx]
    · simp [HomotopyWith.extendProp G (2 * t - 1) x hx, F.fst_eq_snd hx, G.fst_eq_snd hx]

/--
theorem `trans_apply` / 定理 `trans_apply`

English:
theorem trans_apply
  given: (F : HomotopyRel f₀ f₁ S) (G : HomotopyRel f₁ f₂ S) (x : I × X)
  proof: Homotopy.trans_apply _ _ _

中文:
定理 trans_apply
  条件: (F : HomotopyRel f₀ f₁ S) (G : HomotopyRel f₁ f₂ S) (x : I × X)
  证明: Homotopy.trans_apply _ _ _

Depends on / 依赖: Homotopy, Homotopy.trans_apply, trans_apply
-/
theorem trans_apply (F : HomotopyRel f₀ f₁ S) (G : HomotopyRel f₁ f₂ S) (x : I × X) :
    (F.trans G) x =
      if h : (x.1 : Real) <= 1 / 2 then
        F (⟨2 * x.1, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨x.1.2.1, h⟩⟩, x.2)
      else
        G (⟨2 * x.1 - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, x.1.2.2⟩⟩, x.2) :=
  Homotopy.trans_apply _ _ _

/--
theorem `symm_trans` / 定理 `symm_trans`

English:
theorem symm_trans
  given: (F : HomotopyRel f₀ f₁ S) (G : HomotopyRel f₁ f₂ S)
  proof: HomotopyWith.ext Homotopy.congr_fun Homotopy.symm_trans _ _

中文:
定理 symm_trans
  条件: (F : HomotopyRel f₀ f₁ S) (G : HomotopyRel f₁ f₂ S)
  证明: HomotopyWith.ext Homotopy.congr_fun Homotopy.symm_trans _ _

Depends on / 依赖: Homotopy, Homotopy.congr_fun, Homotopy.symm_trans, HomotopyWith, HomotopyWith.ext, congr_fun, symm_trans
-/
theorem symm_trans (F : HomotopyRel f₀ f₁ S) (G : HomotopyRel f₁ f₂ S) :
    (F.trans G).symm = G.symm.trans F.symm :=
HomotopyWith.ext Homotopy.congr_fun Homotopy.symm_trans _ _

/-- Casting a `HomotopyRel f₀ f₁ S` to a `HomotopyRel g₀ g₁ S` where `f₀ = g₀` and `f₁ = g₁`.
-/
@[simps!]
/--
Definition of `cast` / `cast` 的定义

English:
definition cast
  signature: {f₀ f₁ g₀ g₁ : C(X, Y)} (F : HomotopyRel f₀ f₁ S) (h₀ : f₀ = g₀) (h₁ : f₁ = g₁)
  body: Homotopy.cast F.toHomotopy h₀ h₁
  prop' t x hx := by simpa only [← h₀, ← h₁] using! F.prop t x hx

中文:
定义 cast
  签名: {f₀ f₁ g₀ g₁ : C(X, Y)} (F : HomotopyRel f₀ f₁ S) (h₀ : f₀ = g₀) (h₁ : f₁ = g₁)
  定义体: Homotopy.cast F.toHomotopy h₀ h₁
  prop' t x hx := by simpa only [← h₀, ← h₁] using! F.prop t x hx

Depends on / 依赖: F.toHomotopy, Homotopy, Homotopy.cast, toHomotopy
-/
def cast {f₀ f₁ g₀ g₁ : C(X, Y)} (F : HomotopyRel f₀ f₁ S) (h₀ : f₀ = g₀) (h₁ : f₁ = g₁) :
    HomotopyRel g₀ g₁ S where
  toHomotopy := Homotopy.cast F.toHomotopy h₀ h₁
  prop' t x hx := by simpa only [← h₀, ← h₁] using! F.prop t x hx

/--
Definition of `compContinuousMap` / `compContinuousMap` 的定义

English:
definition compContinuousMap
  signature: {f₀ f₁ : C(X, Y)} (F : f₀.HomotopyRel f₁ S) (g : C(Y, Z))
  body: .comp (.refl g) F.toHomotopy
  prop' t x hx := congr_arg g (F.prop t x hx)

中文:
定义 compContinuousMap
  签名: {f₀ f₁ : C(X, Y)} (F : f₀.HomotopyRel f₁ S) (g : C(Y, Z))
  定义体: .comp (.refl g) F.toHomotopy
  prop' t x hx := congr_arg g (F.prop t x hx)
-/
@[simps!] def compContinuousMap {f₀ f₁ : C(X, Y)} (F : f₀.HomotopyRel f₁ S) (g : C(Y, Z)) :
    (g.comp f₀).HomotopyRel (g.comp f₁) S where
  toHomotopy := .comp (.refl g) F.toHomotopy
  prop' t x hx := congr_arg g (F.prop t x hx)

end HomotopyRel

/--
Definition of `HomotopicRel` / `HomotopicRel` 的定义

English:
definition HomotopicRel
  signature: (f₀ f₁ : C(X, Y)) (S : Set X)
  body: Nonempty (HomotopyRel f₀ f₁ S)

中文:
定义 HomotopicRel
  签名: (f₀ f₁ : C(X, Y)) (S : 集合 X)
  定义体: Nonempty (HomotopyRel f₀ f₁ S)

Depends on / 依赖: HomotopyRel, Nonempty
-/
def HomotopicRel (f₀ f₁ : C(X, Y)) (S : Set X) : Prop :=
  Nonempty (HomotopyRel f₀ f₁ S)

namespace HomotopicRel

variable {S : Set X}

/--
theorem `homotopic` / 定理 `homotopic`

English:
theorem homotopic
  given: {f₀ f₁ : C(X, Y)} (h : HomotopicRel f₀ f₁ S)
  statement: Homotopic f₀ f₁
  proof: h.map fun F => F.1

中文:
定理 homotopic
  条件: {f₀ f₁ : C(X, Y)} (h : HomotopicRel f₀ f₁ S)
  结论: 同伦 f₀ f₁
  证明: h.map fun F => F.1
-/
protected theorem homotopic {f₀ f₁ : C(X, Y)} (h : HomotopicRel f₀ f₁ S) : Homotopic f₀ f₁ :=
  h.map fun F => F.1

/--
theorem `fst_eq_snd` / 定理 `fst_eq_snd`

English:
theorem fst_eq_snd
  given: ⦃f₀ f₁
  statement: C(X, Y)⦄ (h : HomotopicRel f₀ f₁ S) {x : X} (hx : x in S) :
  proof: Nonempty.elim h (HomotopyRel.fst_eq_snd · hx)

中文:
定理 fst_eq_snd
  条件: ⦃f₀ f₁
  结论: C(X, Y)⦄ (h : HomotopicRel f₀ f₁ S) {x : X} (hx : x in S) :
  证明: Nonempty.elim h (HomotopyRel.fst_eq_snd · hx)

Depends on / 依赖: HomotopyRel, HomotopyRel.fst_eq_snd, Nonempty, Nonempty.elim, fst_eq_snd
-/
theorem fst_eq_snd ⦃f₀ f₁ : C(X, Y)⦄ (h : HomotopicRel f₀ f₁ S) {x : X} (hx : x in S) :
    f₀ x = f₁ x :=
  Nonempty.elim h (HomotopyRel.fst_eq_snd · hx)

/--
theorem `refl` / 定理 `refl`

English:
theorem refl
  given: (f : C(X, Y))
  statement: HomotopicRel f f S
  proof: ⟨HomotopyRel.refl f S⟩

@[symm]

中文:
定理 refl
  条件: (f : C(X, Y))
  结论: HomotopicRel f f S
  证明: ⟨HomotopyRel.refl f S⟩

@[symm]

Depends on / 依赖: HomotopyRel, HomotopyRel.refl
-/
theorem refl (f : C(X, Y)) : HomotopicRel f f S :=
  ⟨HomotopyRel.refl f S⟩

@[symm]
/--
theorem `symm` / 定理 `symm`

English:
theorem symm
  given: ⦃f g
  statement: C(X, Y)⦄ (h : HomotopicRel f g S) : HomotopicRel g f S
  proof: h.map HomotopyRel.symm

@[trans]

中文:
定理 symm
  条件: ⦃f g
  结论: C(X, Y)⦄ (h : HomotopicRel f g S) : HomotopicRel g f S
  证明: h.map HomotopyRel.symm

@[trans]

Depends on / 依赖: HomotopyRel, HomotopyRel.symm, h.map
-/
theorem symm ⦃f g : C(X, Y)⦄ (h : HomotopicRel f g S) : HomotopicRel g f S :=
  h.map HomotopyRel.symm

@[trans]
/--
theorem `trans` / 定理 `trans`

English:
theorem trans
  given: ⦃f g h
  statement: C(X, Y)⦄ (h₀ : HomotopicRel f g S) (h₁ : HomotopicRel g h S) :
  proof: h₀.map2 HomotopyRel.trans h₁

中文:
定理 trans
  条件: ⦃f g h
  结论: C(X, Y)⦄ (h₀ : HomotopicRel f g S) (h₁ : HomotopicRel g h S) :
  证明: h₀.map2 HomotopyRel.trans h₁

Depends on / 依赖: HomotopyRel, HomotopyRel.trans
-/
theorem trans ⦃f g h : C(X, Y)⦄ (h₀ : HomotopicRel f g S) (h₁ : HomotopicRel g h S) :
    HomotopicRel f h S :=
  h₀.map2 HomotopyRel.trans h₁

/--
theorem `equivalence` / 定理 `equivalence`

English:
theorem equivalence
  statement: Equivalence fun f g : C(X, Y) => HomotopicRel f g S
  proof: ⟨refl, by apply symm, by apply trans⟩

中文:
定理 equivalence
  结论: 等价 fun f g : C(X, Y) => HomotopicRel f g S
  证明: ⟨refl, by apply symm, by apply trans⟩
-/
theorem equivalence : Equivalence fun f g : C(X, Y) => HomotopicRel f g S :=
  ⟨refl, by apply symm, by apply trans⟩

/--
theorem `comp_continuousMap` / 定理 `comp_continuousMap`

English:
theorem comp_continuousMap
  given: ⦃f₀ f₁
  statement: C(X, Y)⦄ (h : f₀.HomotopicRel f₁ S) (g : C(Y, Z)) :
  proof: h.map (·.compContinuousMap g)

中文:
定理 comp_continuousMap
  条件: ⦃f₀ f₁
  结论: C(X, Y)⦄ (h : f₀.HomotopicRel f₁ S) (g : C(Y, Z)) :
  证明: h.map (·.compContinuousMap g)

Depends on / 依赖: compContinuousMap, h.map
-/
theorem comp_continuousMap ⦃f₀ f₁ : C(X, Y)⦄ (h : f₀.HomotopicRel f₁ S) (g : C(Y, Z)) :
    (g.comp f₀).HomotopicRel (g.comp f₁) S := h.map (·.compContinuousMap g)

end HomotopicRel

/--
theorem `homotopicRel_empty` / 定理 `homotopicRel_empty`

English:
theorem homotopicRel_empty
  given: {f₀ f₁ : C(X, Y)}
  statement: HomotopicRel f₀ f₁ ∅ ↔ Homotopic f₀ f₁
  proof: ⟨fun h => h.homotopic, fun ⟨F⟩ => ⟨⟨F, fun _ _ => False.elim⟩⟩⟩

中文:
定理 homotopicRel_empty
  条件: {f₀ f₁ : C(X, Y)}
  结论: HomotopicRel f₀ f₁ ∅ ↔ 同伦 f₀ f₁
  证明: ⟨fun h => h.homotopic, fun ⟨F⟩ => ⟨⟨F, fun _ _ => False.elim⟩⟩⟩
-/
@[simp] theorem homotopicRel_empty {f₀ f₁ : C(X, Y)} : HomotopicRel f₀ f₁ ∅ ↔ Homotopic f₀ f₁ :=
  ⟨fun h => h.homotopic, fun ⟨F⟩ => ⟨⟨F, fun _ _ => False.elim⟩⟩⟩

end ContinuousMap
