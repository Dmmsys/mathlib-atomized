/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Algebra.Order.Group.Pointwise.Interval
public import Mathlib.Algebra.Order.Module.Defs
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.Tactic.Abel
public import Mathlib.Algebra.Torsor.Basic
public import Mathlib.LinearAlgebra.AffineSpace.Defs
/-!
# Affine maps

This file defines affine maps.

## Main definitions

* `AffineMap` is the type of affine maps between two affine spaces with the same ring `k`. Various
  basic examples of affine maps are defined, including `const`, `id`, `lineMap` and `homothety`.

## Notation

* `P1 →ᵃ[k] P2` is a notation for `AffineMap k P1 P2`;
* `AffineSpace V P`: a localized notation for `AddTorsor V P` defined in
  `LinearAlgebra.AffineSpace.Basic`.

## Implementation notes

`outParam` is used in the definition of `[AddTorsor V P]` to make `V` an implicit argument
(deduced from `P`) in most cases. As for modules, `k` is an explicit argument rather than implied by
`P` or `V`.

This file only provides purely algebraic definitions and results. Those depending on analysis or
topology are defined elsewhere; see `Analysis.Normed.Affine.AddTorsor` and
`Topology.Algebra.Affine`.

## References

* https://en.wikipedia.org/wiki/Affine_space
* https://en.wikipedia.org/wiki/Principal_homogeneous_space
-/

@[expose] public section

open Affine Module

/--
Definition of `AffineMap` / `AffineMap` 的定义

English:
structure AffineMap
  parameters: (k : Type*) {V1 : Type*} (P1 : Type*) {V2 : Type*} (P2 : Type*) [Ring k]
  axioms and operations (3):
    - toFun : P1 -> P2
    - linear : V1 ->ₗ[k] V2
    - map_vadd' : forall (p : P1) (v : V1), toFun (v +ᵥ p) = linear v +ᵥ toFun p

中文:
结构 仿射映射
  参数: (k : 类型) {V1 : 类型} (P1 : 类型) {V2 : 类型} (P2 : 类型) [环 k]
  公理与运算 (3 个):
    - toFun : P1 -> P2
    - linear : V1 ->ₗ[k] V2
    - map_vadd' : 对任意 (p : P1) (v : V1), toFun (v +ᵥ p) = linear v +ᵥ toFun p
-/
structure AffineMap (k : Type*) {V1 : Type*} (P1 : Type*) {V2 : Type*} (P2 : Type*) [Ring k]
  [AddCommGroup V1] [Module k V1] [AffineSpace V1 P1] [AddCommGroup V2] [Module k V2]
  [AffineSpace V2 P2] where
  /-- The underlying function between the affine spaces `P1` and `P2`. -/
  toFun : P1 -> P2
  /-- The linear map between the corresponding vector spaces `V1` and `V2`.
  This represents how the affine map acts on differences of points. -/
  linear : V1 ->ₗ[k] V2
  map_vadd' : forall (p : P1) (v : V1), toFun (v +ᵥ p) = linear v +ᵥ toFun p

/-- An `AffineMap k P1 P2` (notation: `P1 →ᵃ[k] P2`) is a map from `P1` to `P2` that
induces a corresponding linear map from `V1` to `V2`. -/
notation:25 P1 " ->ᵃ[" k:25 "] " P2:0 => AffineMap k P1 P2

/--
Instance `AffineMap.instFunLike` / 实例 `AffineMap.instFunLike`

English:
instance AffineMap.instFunLike
  signature: (k : Type*) {V1 : Type*} (P1 : Type*) {V2 : Type*} (P2 : Type*)
  body: AffineMap.toFun
  coe_injective := fun ⟨f, f_linear, f_add⟩ ⟨g, g_linear, g_add⟩ => fun (h : f = g) => by
    obtain ⟨p⟩ := (AddTorsor.nonempty : Nonempty P1)
    congr with v
    apply vadd_right_cancel (f p)
    rw [← f_add]; rw [h]; rw [← g_add]

中文:
实例 仿射映射.instFunLike
  签名: (k : 类型) {V1 : 类型} (P1 : 类型) {V2 : 类型} (P2 : 类型)
  定义体: AffineMap.toFun
  coe_injective := fun ⟨f, f_linear, f_add⟩ ⟨g, g_linear, g_add⟩ => fun (h : f = g) => by
    obtain ⟨p⟩ := (AddTorsor.nonempty : Nonempty P1)
    congr with v
    apply vadd_right_cancel (f p)
    rw [← f_add]; rw [h]; rw [← g_add]

Depends on / 依赖: AffineMap, AffineMap.toFun
-/
instance AffineMap.instFunLike (k : Type*) {V1 : Type*} (P1 : Type*) {V2 : Type*} (P2 : Type*)
    [Ring k] [AddCommGroup V1] [Module k V1] [AffineSpace V1 P1] [AddCommGroup V2] [Module k V2]
    [AffineSpace V2 P2] : FunLike (P1 ->ᵃ[k] P2) P1 P2 where
  coe := AffineMap.toFun
  coe_injective := fun ⟨f, f_linear, f_add⟩ ⟨g, g_linear, g_add⟩ => fun (h : f = g) => by
    obtain ⟨p⟩ := (AddTorsor.nonempty : Nonempty P1)
    congr with v
    apply vadd_right_cancel (f p)
    rw [← f_add]; rw [h]; rw [← g_add]

namespace LinearMap

variable {k : Type*} {V₁ : Type*} {V₂ : Type*} [Ring k] [AddCommGroup V₁] [Module k V₁]
  [AddCommGroup V₂] [Module k V₂] (f : V₁ ->ₗ[k] V₂)

/--
Definition of `toAffineMap` / `toAffineMap` 的定义

English:
definition toAffineMap
  signature: : V₁ ->ᵃ[k] V₂ where
  body: f
  linear := f
  map_vadd' p v := f.map_add v p

@[simp]

中文:
定义 toAffineMap
  签名: : V₁ ->ᵃ[k] V₂ where
  定义体: f
  linear := f
  map_vadd' p v := f.map_add v p

@[simp]
-/
def toAffineMap : V₁ ->ᵃ[k] V₂ where
  toFun := f
  linear := f
  map_vadd' p v := f.map_add v p

@[simp]
/--
theorem `coe_toAffineMap` / 定理 `coe_toAffineMap`

English:
theorem coe_toAffineMap
  statement: ⇑f.toAffineMap = f
  proof: rfl

@[simp]

中文:
定理 coe_toAffineMap
  结论: ⇑f.toAffineMap = f
  证明: rfl

@[simp]
-/
theorem coe_toAffineMap : ⇑f.toAffineMap = f :=
  rfl

@[simp]
/--
theorem `toAffineMap_linear` / 定理 `toAffineMap_linear`

English:
theorem toAffineMap_linear
  statement: f.toAffineMap.linear = f
  proof: rfl

中文:
定理 toAffineMap_linear
  结论: f.toAffineMap.linear = f
  证明: rfl
-/
theorem toAffineMap_linear : f.toAffineMap.linear = f :=
  rfl

end LinearMap

namespace AffineMap

variable {k : Type*} {V1 : Type*} {P1 : Type*} {V2 : Type*} {P2 : Type*} {V3 : Type*}
  {P3 : Type*} {V4 : Type*} {P4 : Type*} [Ring k] [AddCommGroup V1] [Module k V1]
  [AffineSpace V1 P1] [AddCommGroup V2] [Module k V2] [AffineSpace V2 P2] [AddCommGroup V3]
  [Module k V3] [AffineSpace V3 P3] [AddCommGroup V4] [Module k V4] [AffineSpace V4 P4]

/-- Constructing an affine map and coercing back to a function
produces the same map. -/
@[simp]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (f : P1 -> P2) (linear add)
  statement: ((mk f linear add : P1 ->ᵃ[k] P2) : P1 -> P2) = f
  proof: rfl

中文:
定理 coe_mk
  条件: (f : P1 -> P2) (linear add)
  结论: ((mk f linear add : P1 ->ᵃ[k] P2) : P1 -> P2) = f
  证明: rfl
-/
theorem coe_mk (f : P1 -> P2) (linear add) : ((mk f linear add : P1 ->ᵃ[k] P2) : P1 -> P2) = f :=
  rfl

/-- `toFun` is the same as the result of coercing to a function. -/
@[simp]
/--
theorem `toFun_eq_coe` / 定理 `toFun_eq_coe`

English:
theorem toFun_eq_coe
  given: (f : P1 ->ᵃ[k] P2)
  statement: f.toFun = ⇑f
  proof: rfl

中文:
定理 toFun_eq_coe
  条件: (f : P1 ->ᵃ[k] P2)
  结论: f.toFun = ⇑f
  证明: rfl
-/
theorem toFun_eq_coe (f : P1 ->ᵃ[k] P2) : f.toFun = ⇑f :=
  rfl

/-- An affine map on the result of adding a vector to a point produces
the same result as the linear map applied to that vector, added to the
affine map applied to that point. -/
@[simp]
/--
theorem `map_vadd` / 定理 `map_vadd`

English:
theorem map_vadd
  given: (f : P1 ->ᵃ[k] P2) (p : P1) (v : V1)
  statement: f (v +ᵥ p) = f.linear v +ᵥ f p
  proof: f.map_vadd' p v

中文:
定理 map_vadd
  条件: (f : P1 ->ᵃ[k] P2) (p : P1) (v : V1)
  结论: f (v +ᵥ p) = f.linear v +ᵥ f p
  证明: f.map_vadd' p v

Depends on / 依赖: f.map_vadd, map_vadd
-/
theorem map_vadd (f : P1 ->ᵃ[k] P2) (p : P1) (v : V1) : f (v +ᵥ p) = f.linear v +ᵥ f p :=
  f.map_vadd' p v

/-- The linear map on the result of subtracting two points is the
result of subtracting the result of the affine map on those two
points. -/
@[simp]
/--
theorem `linearMap_vsub` / 定理 `linearMap_vsub`

English:
theorem linearMap_vsub
  given: (f : P1 ->ᵃ[k] P2) (p1 p2 : P1)
  statement: f.linear (p1 -ᵥ p2) = f p1 -ᵥ f p2
  proof: by
  conv_rhs => rw [← vsub_vadd p1 p2, map_vadd, vadd_vsub]

中文:
定理 linearMap_vsub
  条件: (f : P1 ->ᵃ[k] P2) (p1 p2 : P1)
  结论: f.linear (p1 -ᵥ p2) = f p1 -ᵥ f p2
  证明: by
  conv_rhs => rw [← vsub_vadd p1 p2, map_vadd, vadd_vsub]

Depends on / 依赖: conv_rhs, map_vadd, vadd_vsub, vsub_vadd
-/
theorem linearMap_vsub (f : P1 ->ᵃ[k] P2) (p1 p2 : P1) : f.linear (p1 -ᵥ p2) = f p1 -ᵥ f p2 := by
  conv_rhs => rw [← vsub_vadd p1 p2, map_vadd, vadd_vsub]

/-- Two affine maps are equal if they coerce to the same function. -/
@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : P1 ->ᵃ[k] P2} (h : forall p, f p = g p)
  statement: f = g
  proof: DFunLike.ext _ _ h

中文:
定理 ext
  条件: {f g : P1 ->ᵃ[k] P2} (h : 对任意 p, f p = g p)
  结论: f = g
  证明: DFunLike.ext _ _ h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {f g : P1 ->ᵃ[k] P2} (h : forall p, f p = g p) : f = g :=
  DFunLike.ext _ _ h

/--
theorem `coeFn_injective` / 定理 `coeFn_injective`

English:
theorem coeFn_injective
  statement: @Function.Injective (P1 ->ᵃ[k] P2) (P1 -> P2) (⇑)
  proof: DFunLike.coe_injective

中文:
定理 coeFn_injective
  结论: @函数.单射 (P1 ->ᵃ[k] P2) (P1 -> P2) (⇑)
  证明: DFunLike.coe_injective

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective
-/
theorem coeFn_injective : @Function.Injective (P1 ->ᵃ[k] P2) (P1 -> P2) (⇑) :=
  DFunLike.coe_injective

/--
theorem `congr_arg` / 定理 `congr_arg`

English:
theorem congr_arg
  given: (f : P1 ->ᵃ[k] P2) {x y : P1} (h : x = y)
  statement: f x = f y
  proof: congr_arg _ h

中文:
定理 congr_arg
  条件: (f : P1 ->ᵃ[k] P2) {x y : P1} (h : x = y)
  结论: f x = f y
  证明: congr_arg _ h
-/
protected theorem congr_arg (f : P1 ->ᵃ[k] P2) {x y : P1} (h : x = y) : f x = f y :=
  congr_arg _ h

/--
theorem `congr_fun` / 定理 `congr_fun`

English:
theorem congr_fun
  given: {f g : P1 ->ᵃ[k] P2} (h : f = g) (x : P1)
  statement: f x = g x
  proof: h ▸ rfl

中文:
定理 congr_fun
  条件: {f g : P1 ->ᵃ[k] P2} (h : f = g) (x : P1)
  结论: f x = g x
  证明: h ▸ rfl
-/
protected theorem congr_fun {f g : P1 ->ᵃ[k] P2} (h : f = g) (x : P1) : f x = g x :=
  h ▸ rfl

/--
theorem `ext_linear` / 定理 `ext_linear`

English:
theorem ext_linear
  given: {f g : P1 ->ᵃ[k] P2} (h₁ : f.linear = g.linear) {p : P1} (h₂ : f p = g p)
  proof: by
  ext q
  have hgl : g.linear (q -ᵥ p) = toFun g ((q -ᵥ p) +ᵥ q) -ᵥ toFun g q := by simp
  have := f.map_vadd' q (q -ᵥ p)
  rw [h₁]; rw [hgl]; rw [toFun_eq_coe]; rw [map_vadd]; rw [linearMap_vsub]; rw [h₂] at this
  simpa

中文:
定理 ext_linear
  条件: {f g : P1 ->ᵃ[k] P2} (h₁ : f.linear = g.linear) {p : P1} (h₂ : f p = g p)
  证明: by
  ext q
  have hgl : g.linear (q -ᵥ p) = toFun g ((q -ᵥ p) +ᵥ q) -ᵥ toFun g q := by simp
  have := f.map_vadd' q (q -ᵥ p)
  rw [h₁]; rw [hgl]; rw [toFun_eq_coe]; rw [map_vadd]; rw [linearMap_vsub]; rw [h₂] at this
  simpa

Depends on / 依赖: f.map_vadd, g.linear, linear, linearMap_vsub, map_vadd, toFun_eq_coe
-/
theorem ext_linear {f g : P1 ->ᵃ[k] P2} (h₁ : f.linear = g.linear) {p : P1} (h₂ : f p = g p) :
    f = g := by
  ext q
  have hgl : g.linear (q -ᵥ p) = toFun g ((q -ᵥ p) +ᵥ q) -ᵥ toFun g q := by simp
  have := f.map_vadd' q (q -ᵥ p)
  rw [h₁]; rw [hgl]; rw [toFun_eq_coe]; rw [map_vadd]; rw [linearMap_vsub]; rw [h₂] at this
  simpa

/--
theorem `ext_linear_iff` / 定理 `ext_linear_iff`

English:
theorem ext_linear_iff
  given: {f g : P1 ->ᵃ[k] P2}
  statement: f = g ↔ (f.linear = g.linear) ∧ (exists p, f p = g p)
  proof: ⟨fun h => ⟨congrArg _ h, by inhabit P1; exact default, by rw [h]⟩,
  fun h => Exists.casesOn h.2 fun _ hp => ext_linear h.1 hp⟩

中文:
定理 ext_linear_iff
  条件: {f g : P1 ->ᵃ[k] P2}
  结论: f = g ↔ (f.linear = g.linear) ∧ (存在 p, f p = g p)
  证明: ⟨fun h => ⟨congrArg _ h, by inhabit P1; exact default, by rw [h]⟩,
  fun h => Exists.casesOn h.2 fun _ hp => ext_linear h.1 hp⟩

Depends on / 依赖: Exists, Exists.casesOn, casesOn, ext_linear, inhabit
-/
theorem ext_linear_iff {f g : P1 ->ᵃ[k] P2} : f = g ↔ (f.linear = g.linear) ∧ (exists p, f p = g p) :=
  ⟨fun h => ⟨congrArg _ h, by inhabit P1; exact default, by rw [h]⟩,
  fun h => Exists.casesOn h.2 fun _ hp => ext_linear h.1 hp⟩

variable (k P1)

/--
Definition of `const` / `const` 的定义

English:
definition const
  signature: (p : P2)
  body: Function.const P1 p
  linear := 0
  map_vadd' _ _ :=
    letI : AddAction V2 P2 := inferInstance
    by simp

@[simp]

中文:
定义 const
  签名: (p : P2)
  定义体: Function.const P1 p
  linear := 0
  map_vadd' _ _ :=
    letI : AddAction V2 P2 := inferInstance
    by simp

@[simp]

Depends on / 依赖: Function, Function.const
-/
def const (p : P2) : P1 ->ᵃ[k] P2 where
  toFun := Function.const P1 p
  linear := 0
  map_vadd' _ _ :=
    letI : AddAction V2 P2 := inferInstance
    by simp

@[simp]
/--
theorem `coe_const` / 定理 `coe_const`

English:
theorem coe_const
  given: (p : P2)
  statement: ⇑(const k P1 p) = Function.const P1 p
  proof: rfl

@[simp]

中文:
定理 coe_const
  条件: (p : P2)
  结论: ⇑(const k P1 p) = 函数.const P1 p
  证明: rfl

@[simp]
-/
theorem coe_const (p : P2) : ⇑(const k P1 p) = Function.const P1 p :=
  rfl

@[simp]
/--
theorem `const_apply` / 定理 `const_apply`

English:
theorem const_apply
  given: (p : P2) (q : P1)
  statement: (const k P1 p) q = p
  proof: rfl

@[simp]

中文:
定理 const_apply
  条件: (p : P2) (q : P1)
  结论: (const k P1 p) q = p
  证明: rfl

@[simp]
-/
theorem const_apply (p : P2) (q : P1) : (const k P1 p) q = p := rfl

@[simp]
/--
theorem `const_linear` / 定理 `const_linear`

English:
theorem const_linear
  given: (p : P2)
  statement: (const k P1 p).linear = 0
  proof: rfl

中文:
定理 const_linear
  条件: (p : P2)
  结论: (const k P1 p).linear = 0
  证明: rfl
-/
theorem const_linear (p : P2) : (const k P1 p).linear = 0 :=
  rfl

variable {k P1}

/--
theorem `linear_eq_zero_iff_exists_const` / 定理 `linear_eq_zero_iff_exists_const`

English:
theorem linear_eq_zero_iff_exists_const
  given: (f : P1 ->ᵃ[k] P2)
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · use f (Classical.arbitrary P1)
    ext
    rw [coe_const]; rw [Function.const_apply]; rw [← @vsub_eq_zero_iff_eq V2]; rw [← f.linearMap_vsub]; rw [h]; rw [LinearMap.zero_apply]
  · rcases h with ⟨q, rfl⟩
    exact const_linear k P1 q

中文:
定理 linear_eq_zero_iff_存在_const
  条件: (f : P1 ->ᵃ[k] P2)
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · use f (Classical.arbitrary P1)
    ext
    rw [coe_const]; rw [Function.const_apply]; rw [← @vsub_eq_zero_iff_eq V2]; rw [← f.linearMap_vsub]; rw [h]; rw [LinearMap.zero_apply]
  · rcases h with ⟨q, rfl⟩
    exact const_linear k P1 q

Depends on / 依赖: Classical, Classical.arbitrary, Function, Function.const_apply, LinearMap, LinearMap.zero_apply, arbitrary, coe_const, const_apply, const_linear, f.linearMap_vsub, linearMap_vsub, vsub_eq_zero_iff_eq, zero_apply
-/
theorem linear_eq_zero_iff_exists_const (f : P1 ->ᵃ[k] P2) :
    f.linear = 0 ↔ exists q, f = const k P1 q := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · use f (Classical.arbitrary P1)
    ext
    rw [coe_const]; rw [Function.const_apply]; rw [← @vsub_eq_zero_iff_eq V2]; rw [← f.linearMap_vsub]; rw [h]; rw [LinearMap.zero_apply]
  · rcases h with ⟨q, rfl⟩
    exact const_linear k P1 q

/--
Instance `nonempty` / 实例 `nonempty`

English:
instance nonempty
  signature: : Nonempty (P1 ->ᵃ[k] P2)
  body: (AddTorsor.nonempty : Nonempty P2).map const k P1

中文:
实例 nonempty
  签名: : 非空 (P1 ->ᵃ[k] P2)
  定义体: (AddTorsor.nonempty : Nonempty P2).map const k P1

Depends on / 依赖: AddTorsor, AddTorsor.nonempty, Nonempty, nonempty
-/
instance nonempty : Nonempty (P1 ->ᵃ[k] P2) :=
(AddTorsor.nonempty : Nonempty P2).map const k P1

/--
Definition of `mk'` / `mk'` 的定义

English:
definition mk'
  signature: (f : P1 -> P2) (f' : V1 ->ₗ[k] V2) (p : P1) (h : forall p' : P1, f p' = f' (p' -ᵥ p) +ᵥ f p)
  body: f
  linear := f'
  map_vadd' p' v := by rw [h, h p', vadd_vsub_assoc, f'.map_add, vadd_vadd]

@[simp]

中文:
定义 mk'
  签名: (f : P1 -> P2) (f' : V1 ->ₗ[k] V2) (p : P1) (h : 对任意 p' : P1, f p' = f' (p' -ᵥ p) +ᵥ f p)
  定义体: f
  linear := f'
  map_vadd' p' v := by rw [h, h p', vadd_vsub_assoc, f'.map_add, vadd_vadd]

@[simp]
-/
def mk' (f : P1 -> P2) (f' : V1 ->ₗ[k] V2) (p : P1) (h : forall p' : P1, f p' = f' (p' -ᵥ p) +ᵥ f p) :
    P1 ->ᵃ[k] P2 where
  toFun := f
  linear := f'
  map_vadd' p' v := by rw [h, h p', vadd_vsub_assoc, f'.map_add, vadd_vadd]

@[simp]
/--
theorem `coe_mk'` / 定理 `coe_mk'`

English:
theorem coe_mk'
  given: (f : P1 -> P2) (f' : V1 ->ₗ[k] V2) (p h)
  statement: ⇑(mk' f f' p h) = f
  proof: rfl

@[simp]

中文:
定理 coe_mk'
  条件: (f : P1 -> P2) (f' : V1 ->ₗ[k] V2) (p h)
  结论: ⇑(mk' f f' p h) = f
  证明: rfl

@[simp]
-/
theorem coe_mk' (f : P1 -> P2) (f' : V1 ->ₗ[k] V2) (p h) : ⇑(mk' f f' p h) = f :=
  rfl

@[simp]
/--
theorem `mk'_linear` / 定理 `mk'_linear`

English:
theorem mk'_linear
  given: (f : P1 -> P2) (f' : V1 ->ₗ[k] V2) (p h)
  statement: (mk' f f' p h).linear = f'
  proof: rfl

中文:
定理 mk'_linear
  条件: (f : P1 -> P2) (f' : V1 ->ₗ[k] V2) (p h)
  结论: (mk' f f' p h).linear = f'
  证明: rfl
-/
theorem mk'_linear (f : P1 -> P2) (f' : V1 ->ₗ[k] V2) (p h) : (mk' f f' p h).linear = f' :=
  rfl

section SMul

variable {R : Type*} [Monoid R] [DistribMulAction R V2] [SMulCommClass k R V2]
/--
Instance `mulAction` / 实例 `mulAction`

English:
instance mulAction
  signature: : MulAction R (P1 ->ᵃ[k] V2) where
  body: ⟨c • ⇑f, c • f.linear, fun p v => by simp [smul_add]⟩
  one_smul _ := ext fun _ => one_smul _ _
  mul_smul _ _ _ := ext fun _ => mul_smul _ _ _

@[simp, norm_cast]

中文:
实例 mulAction
  签名: : 乘法作用 R (P1 ->ᵃ[k] V2) where
  定义体: ⟨c • ⇑f, c • f.linear, fun p v => by simp [smul_add]⟩
  one_smul _ := ext fun _ => one_smul _ _
  mul_smul _ _ _ := ext fun _ => mul_smul _ _ _

@[simp, norm_cast]

Depends on / 依赖: f.linear, linear, smul_add
-/
instance mulAction : MulAction R (P1 ->ᵃ[k] V2) where
  smul c f := ⟨c • ⇑f, c • f.linear, fun p v => by simp [smul_add]⟩
  one_smul _ := ext fun _ => one_smul _ _
  mul_smul _ _ _ := ext fun _ => mul_smul _ _ _

@[simp, norm_cast]
/--
theorem `coe_smul` / 定理 `coe_smul`

English:
theorem coe_smul
  given: (c : R) (f : P1 ->ᵃ[k] V2)
  statement: ⇑(c • f) = c • ⇑f
  proof: rfl

@[simp]

中文:
定理 coe_smul
  条件: (c : R) (f : P1 ->ᵃ[k] V2)
  结论: ⇑(c • f) = c • ⇑f
  证明: rfl

@[simp]
-/
theorem coe_smul (c : R) (f : P1 ->ᵃ[k] V2) : ⇑(c • f) = c • ⇑f :=
  rfl

@[simp]
/--
theorem `smul_linear` / 定理 `smul_linear`

English:
theorem smul_linear
  given: (t : R) (f : P1 ->ᵃ[k] V2)
  statement: (t • f).linear = t • f.linear
  proof: rfl

中文:
定理 smul_linear
  条件: (t : R) (f : P1 ->ᵃ[k] V2)
  结论: (t • f).linear = t • f.linear
  证明: rfl
-/
theorem smul_linear (t : R) (f : P1 ->ᵃ[k] V2) : (t • f).linear = t • f.linear :=
  rfl

/--
Instance `isCentralScalar` / 实例 `isCentralScalar`

English:
instance isCentralScalar
  signature: [DistribMulAction Rᵐᵒᵖ V2] [IsCentralScalar R V2]
  body: ext fun _ => op_smul_eq_smul _ _

中文:
实例 isCentralScalar
  签名: [分配乘法作用 Rᵐᵒᵖ V2] [中心标量 R V2]
  定义体: ext fun _ => op_smul_eq_smul _ _

Depends on / 依赖: op_smul_eq_smul
-/
instance isCentralScalar [DistribMulAction Rᵐᵒᵖ V2] [IsCentralScalar R V2] :
    IsCentralScalar R (P1 ->ᵃ[k] V2) where
  op_smul_eq_smul _r _x := ext fun _ => op_smul_eq_smul _ _

end SMul

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero (P1 ->ᵃ[k] V2)
  body: ⟨0, 0, fun _ _ => (zero_vadd _ _).symm⟩

中文:
实例 :
  签名: 零 (P1 ->ᵃ[k] V2)
  定义体: ⟨0, 0, fun _ _ => (zero_vadd _ _).symm⟩

Depends on / 依赖: zero_vadd
-/
instance : Zero (P1 ->ᵃ[k] V2) where zero := ⟨0, 0, fun _ _ => (zero_vadd _ _).symm⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add (P1 ->ᵃ[k] V2)
  body: ⟨f + g, f.linear + g.linear, fun p v => by simp [add_add_add_comm]⟩

中文:
实例 :
  签名: 加法 (P1 ->ᵃ[k] V2)
  定义体: ⟨f + g, f.linear + g.linear, fun p v => by simp [add_add_add_comm]⟩

Depends on / 依赖: add_add_add_comm, f.linear, g.linear, linear
-/
instance : Add (P1 ->ᵃ[k] V2) where
  add f g := ⟨f + g, f.linear + g.linear, fun p v => by simp [add_add_add_comm]⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Sub (P1 ->ᵃ[k] V2)
  body: ⟨f - g, f.linear - g.linear, fun p v => by simp [sub_add_sub_comm]⟩

中文:
实例 :
  签名: 减法 (P1 ->ᵃ[k] V2)
  定义体: ⟨f - g, f.linear - g.linear, fun p v => by simp [sub_add_sub_comm]⟩

Depends on / 依赖: f.linear, g.linear, linear, sub_add_sub_comm
-/
instance : Sub (P1 ->ᵃ[k] V2) where
  sub f g := ⟨f - g, f.linear - g.linear, fun p v => by simp [sub_add_sub_comm]⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Neg (P1 ->ᵃ[k] V2)
  body: ⟨-f, -f.linear, fun p v => by simp [add_comm, map_vadd f]⟩

@[simp, norm_cast]

中文:
实例 :
  签名: 取负 (P1 ->ᵃ[k] V2)
  定义体: ⟨-f, -f.linear, fun p v => by simp [add_comm, map_vadd f]⟩

@[simp, norm_cast]

Depends on / 依赖: add_comm, f.linear, linear, map_vadd
-/
instance : Neg (P1 ->ᵃ[k] V2) where
  neg f := ⟨-f, -f.linear, fun p v => by simp [add_comm, map_vadd f]⟩

@[simp, norm_cast]
/--
theorem `coe_zero` / 定理 `coe_zero`

English:
theorem coe_zero
  statement: ⇑(0 : P1 ->ᵃ[k] V2) = 0
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_zero
  结论: ⇑(0 : P1 ->ᵃ[k] V2) = 0
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_zero : ⇑(0 : P1 ->ᵃ[k] V2) = 0 :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_add` / 定理 `coe_add`

English:
theorem coe_add
  given: (f g : P1 ->ᵃ[k] V2)
  statement: ⇑(f + g) = f + g
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_add
  条件: (f g : P1 ->ᵃ[k] V2)
  结论: ⇑(f + g) = f + g
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_add (f g : P1 ->ᵃ[k] V2) : ⇑(f + g) = f + g :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_neg` / 定理 `coe_neg`

English:
theorem coe_neg
  given: (f : P1 ->ᵃ[k] V2)
  statement: ⇑(-f) = -f
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_neg
  条件: (f : P1 ->ᵃ[k] V2)
  结论: ⇑(-f) = -f
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_neg (f : P1 ->ᵃ[k] V2) : ⇑(-f) = -f :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_sub` / 定理 `coe_sub`

English:
theorem coe_sub
  given: (f g : P1 ->ᵃ[k] V2)
  statement: ⇑(f - g) = f - g
  proof: rfl

@[simp]

中文:
定理 coe_sub
  条件: (f g : P1 ->ᵃ[k] V2)
  结论: ⇑(f - g) = f - g
  证明: rfl

@[simp]
-/
theorem coe_sub (f g : P1 ->ᵃ[k] V2) : ⇑(f - g) = f - g :=
  rfl

@[simp]
/--
theorem `zero_linear` / 定理 `zero_linear`

English:
theorem zero_linear
  statement: (0 : P1 ->ᵃ[k] V2).linear = 0
  proof: rfl

@[simp]

中文:
定理 zero_linear
  结论: (0 : P1 ->ᵃ[k] V2).linear = 0
  证明: rfl

@[simp]
-/
theorem zero_linear : (0 : P1 ->ᵃ[k] V2).linear = 0 :=
  rfl

@[simp]
/--
theorem `add_linear` / 定理 `add_linear`

English:
theorem add_linear
  given: (f g : P1 ->ᵃ[k] V2)
  statement: (f + g).linear = f.linear + g.linear
  proof: rfl

@[simp]

中文:
定理 add_linear
  条件: (f g : P1 ->ᵃ[k] V2)
  结论: (f + g).linear = f.linear + g.linear
  证明: rfl

@[simp]
-/
theorem add_linear (f g : P1 ->ᵃ[k] V2) : (f + g).linear = f.linear + g.linear :=
  rfl

@[simp]
/--
theorem `sub_linear` / 定理 `sub_linear`

English:
theorem sub_linear
  given: (f g : P1 ->ᵃ[k] V2)
  statement: (f - g).linear = f.linear - g.linear
  proof: rfl

@[simp]

中文:
定理 sub_linear
  条件: (f g : P1 ->ᵃ[k] V2)
  结论: (f - g).linear = f.linear - g.linear
  证明: rfl

@[simp]
-/
theorem sub_linear (f g : P1 ->ᵃ[k] V2) : (f - g).linear = f.linear - g.linear :=
  rfl

@[simp]
/--
theorem `neg_linear` / 定理 `neg_linear`

English:
theorem neg_linear
  given: (f : P1 ->ᵃ[k] V2)
  statement: (-f).linear = -f.linear
  proof: rfl

中文:
定理 neg_linear
  条件: (f : P1 ->ᵃ[k] V2)
  结论: (-f).linear = -f.linear
  证明: rfl
-/
theorem neg_linear (f : P1 ->ᵃ[k] V2) : (-f).linear = -f.linear :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommGroup (P1 ->ᵃ[k] V2)
  body: coeFn_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => coe_smul _ _)
    fun _ _ => coe_smul _ _

中文:
实例 :
  签名: 加法交换群 (P1 ->ᵃ[k] V2)
  定义体: coeFn_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => coe_smul _ _)
    fun _ _ => coe_smul _ _

Depends on / 依赖: addCommGroup, coeFn_injective, coeFn_injective.addCommGroup, coe_add, coe_neg, coe_smul, coe_sub, coe_zero
-/
instance : AddCommGroup (P1 ->ᵃ[k] V2) :=
  coeFn_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => coe_smul _ _)
    fun _ _ => coe_smul _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AffineSpace (P1 ->ᵃ[k] V2) (P1 ->ᵃ[k] P2)
  body: ⟨fun p => f p +ᵥ g p, f.linear + g.linear,
      fun p v => by simp [vadd_vadd, add_right_comm]⟩
  zero_vadd f := ext fun p => zero_vadd _ (f p)
  add_vadd f₁ f₂ f₃ := ext fun p => add_vadd (f₁ p) (f₂ p) (f₃ p)
  vsub f g :=
    ⟨fun p => f p -ᵥ g p, f.linear - g.linear, fun p v => by
      simp [vs

中文:
实例 :
  签名: 仿射空间 (P1 ->ᵃ[k] V2) (P1 ->ᵃ[k] P2)
  定义体: ⟨fun p => f p +ᵥ g p, f.linear + g.linear,
      fun p v => by simp [vadd_vadd, add_right_comm]⟩
  zero_vadd f := ext fun p => zero_vadd _ (f p)
  add_vadd f₁ f₂ f₃ := ext fun p => add_vadd (f₁ p) (f₂ p) (f₃ p)
  vsub f g :=
    ⟨fun p => f p -ᵥ g p, f.linear - g.linear, fun p v => by
      simp [vs

Depends on / 依赖: add_right_comm, add_vadd, f.linear, g.linear, linear, sub_add_eq_add_sub, vadd_vadd, vadd_vsub, vadd_vsub_assoc, vsub_vadd, vsub_vadd_eq_vsub_sub, zero_vadd
-/
instance : AffineSpace (P1 ->ᵃ[k] V2) (P1 ->ᵃ[k] P2) where
  vadd f g :=
    ⟨fun p => f p +ᵥ g p, f.linear + g.linear,
      fun p v => by simp [vadd_vadd, add_right_comm]⟩
  zero_vadd f := ext fun p => zero_vadd _ (f p)
  add_vadd f₁ f₂ f₃ := ext fun p => add_vadd (f₁ p) (f₂ p) (f₃ p)
  vsub f g :=
    ⟨fun p => f p -ᵥ g p, f.linear - g.linear, fun p v => by
      simp [vsub_vadd_eq_vsub_sub, vadd_vsub_assoc, sub_add_eq_add_sub]⟩
  vsub_vadd' f g := ext fun p => vsub_vadd (f p) (g p)
  vadd_vsub' f g := ext fun p => vadd_vsub (f p) (g p)

@[simp]
/--
theorem `vadd_apply` / 定理 `vadd_apply`

English:
theorem vadd_apply
  given: (f : P1 ->ᵃ[k] V2) (g : P1 ->ᵃ[k] P2) (p : P1)
  statement: (f +ᵥ g) p = f p +ᵥ g p
  proof: rfl

@[simp]

中文:
定理 vadd_apply
  条件: (f : P1 ->ᵃ[k] V2) (g : P1 ->ᵃ[k] P2) (p : P1)
  结论: (f +ᵥ g) p = f p +ᵥ g p
  证明: rfl

@[simp]
-/
theorem vadd_apply (f : P1 ->ᵃ[k] V2) (g : P1 ->ᵃ[k] P2) (p : P1) : (f +ᵥ g) p = f p +ᵥ g p :=
  rfl

@[simp]
/--
theorem `vadd_linear` / 定理 `vadd_linear`

English:
theorem vadd_linear
  given: (f : P1 ->ᵃ[k] V2) (g : P1 ->ᵃ[k] P2)
  statement: (f +ᵥ g).linear = f.linear + g.linear
  proof: rfl

@[simp]

中文:
定理 vadd_linear
  条件: (f : P1 ->ᵃ[k] V2) (g : P1 ->ᵃ[k] P2)
  结论: (f +ᵥ g).linear = f.linear + g.linear
  证明: rfl

@[simp]
-/
theorem vadd_linear (f : P1 ->ᵃ[k] V2) (g : P1 ->ᵃ[k] P2) : (f +ᵥ g).linear = f.linear + g.linear :=
  rfl

@[simp]
/--
theorem `vsub_apply` / 定理 `vsub_apply`

English:
theorem vsub_apply
  given: (f g : P1 ->ᵃ[k] P2) (p : P1)
  statement: (f -ᵥ g : P1 ->ᵃ[k] V2) p = f p -ᵥ g p
  proof: rfl

@[simp]

中文:
定理 vsub_apply
  条件: (f g : P1 ->ᵃ[k] P2) (p : P1)
  结论: (f -ᵥ g : P1 ->ᵃ[k] V2) p = f p -ᵥ g p
  证明: rfl

@[simp]
-/
theorem vsub_apply (f g : P1 ->ᵃ[k] P2) (p : P1) : (f -ᵥ g : P1 ->ᵃ[k] V2) p = f p -ᵥ g p :=
  rfl

@[simp]
/--
theorem `vsub_linear` / 定理 `vsub_linear`

English:
theorem vsub_linear
  given: (f g : P1 ->ᵃ[k] P2)
  statement: (f -ᵥ g).linear = f.linear - g.linear
  proof: rfl

中文:
定理 vsub_linear
  条件: (f g : P1 ->ᵃ[k] P2)
  结论: (f -ᵥ g).linear = f.linear - g.linear
  证明: rfl
-/
theorem vsub_linear (f g : P1 ->ᵃ[k] P2) : (f -ᵥ g).linear = f.linear - g.linear :=
  rfl

/--
Definition of `fst` / `fst` 的定义

English:
definition fst
  signature: : P1 × P2 ->ᵃ[k] P1 where
  body: Prod.fst
  linear := LinearMap.fst k V1 V2
  map_vadd' _ _ := rfl

@[simp]

中文:
定义 fst
  签名: : P1 × P2 ->ᵃ[k] P1 where
  定义体: Prod.fst
  linear := LinearMap.fst k V1 V2
  map_vadd' _ _ := rfl

@[simp]

Depends on / 依赖: Prod.fst
-/
def fst : P1 × P2 ->ᵃ[k] P1 where
  toFun := Prod.fst
  linear := LinearMap.fst k V1 V2
  map_vadd' _ _ := rfl

@[simp]
/--
theorem `coe_fst` / 定理 `coe_fst`

English:
theorem coe_fst
  statement: ⇑(fst : P1 × P2 ->ᵃ[k] P1) = Prod.fst
  proof: rfl

@[simp]

中文:
定理 coe_fst
  结论: ⇑(fst : P1 × P2 ->ᵃ[k] P1) = 积类型.fst
  证明: rfl

@[simp]
-/
theorem coe_fst : ⇑(fst : P1 × P2 ->ᵃ[k] P1) = Prod.fst :=
  rfl

@[simp]
/--
theorem `fst_linear` / 定理 `fst_linear`

English:
theorem fst_linear
  statement: (fst : P1 × P2 ->ᵃ[k] P1).linear = LinearMap.fst k V1 V2
  proof: rfl

中文:
定理 fst_linear
  结论: (fst : P1 × P2 ->ᵃ[k] P1).linear = 线性映射.fst k V1 V2
  证明: rfl
-/
theorem fst_linear : (fst : P1 × P2 ->ᵃ[k] P1).linear = LinearMap.fst k V1 V2 :=
  rfl

/--
Definition of `snd` / `snd` 的定义

English:
definition snd
  signature: : P1 × P2 ->ᵃ[k] P2 where
  body: Prod.snd
  linear := LinearMap.snd k V1 V2
  map_vadd' _ _ := rfl

@[simp]

中文:
定义 snd
  签名: : P1 × P2 ->ᵃ[k] P2 where
  定义体: Prod.snd
  linear := LinearMap.snd k V1 V2
  map_vadd' _ _ := rfl

@[simp]

Depends on / 依赖: Prod.snd
-/
def snd : P1 × P2 ->ᵃ[k] P2 where
  toFun := Prod.snd
  linear := LinearMap.snd k V1 V2
  map_vadd' _ _ := rfl

@[simp]
/--
theorem `coe_snd` / 定理 `coe_snd`

English:
theorem coe_snd
  statement: ⇑(snd : P1 × P2 ->ᵃ[k] P2) = Prod.snd
  proof: rfl

@[simp]

中文:
定理 coe_snd
  结论: ⇑(snd : P1 × P2 ->ᵃ[k] P2) = 积类型.snd
  证明: rfl

@[simp]
-/
theorem coe_snd : ⇑(snd : P1 × P2 ->ᵃ[k] P2) = Prod.snd :=
  rfl

@[simp]
/--
theorem `snd_linear` / 定理 `snd_linear`

English:
theorem snd_linear
  statement: (snd : P1 × P2 ->ᵃ[k] P2).linear = LinearMap.snd k V1 V2
  proof: rfl

中文:
定理 snd_linear
  结论: (snd : P1 × P2 ->ᵃ[k] P2).linear = 线性映射.snd k V1 V2
  证明: rfl
-/
theorem snd_linear : (snd : P1 × P2 ->ᵃ[k] P2).linear = LinearMap.snd k V1 V2 :=
  rfl

variable (k P1)
/-- Identity map as an affine map. -/
nonrec def id : P1 ->ᵃ[k] P1 where
  toFun := id
  linear := LinearMap.id
  map_vadd' _ _ := rfl

/-- The identity affine map acts as the identity. -/
@[simp, norm_cast]
/--
theorem `coe_id` / 定理 `coe_id`

English:
theorem coe_id
  statement: ⇑(id k P1) = _root_.id
  proof: rfl

@[simp]

中文:
定理 coe_id
  结论: ⇑(id k P1) = _root_.id
  证明: rfl

@[simp]
-/
theorem coe_id : ⇑(id k P1) = _root_.id :=
  rfl

@[simp]
/--
theorem `id_linear` / 定理 `id_linear`

English:
theorem id_linear
  statement: (id k P1).linear = LinearMap.id
  proof: rfl

中文:
定理 id_linear
  结论: (id k P1).linear = 线性映射.id
  证明: rfl
-/
theorem id_linear : (id k P1).linear = LinearMap.id :=
  rfl

variable {P1}

/--
theorem `id_apply` / 定理 `id_apply`

English:
theorem id_apply
  given: (p : P1)
  statement: id k P1 p = p
  proof: rfl

中文:
定理 id_apply
  条件: (p : P1)
  结论: id k P1 p = p
  证明: rfl
-/
theorem id_apply (p : P1) : id k P1 p = p :=
  rfl

variable {k}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (P1 ->ᵃ[k] P1)
  body: ⟨id k P1⟩

中文:
实例 :
  签名: 可居 (P1 ->ᵃ[k] P1)
  定义体: ⟨id k P1⟩
-/
instance : Inhabited (P1 ->ᵃ[k] P1) :=
  ⟨id k P1⟩

/-- Composition of affine maps. -/
@[simps linear]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (f : P2 ->ᵃ[k] P3) (g : P1 ->ᵃ[k] P2)
  body: f ∘ g
  linear := f.linear.comp g.linear
  map_vadd' := by
    intro p v
    rw [Function.comp_apply]; rw [g.map_vadd]; rw [f.map_vadd]
    rfl

中文:
定义 comp
  签名: (f : P2 ->ᵃ[k] P3) (g : P1 ->ᵃ[k] P2)
  定义体: f ∘ g
  linear := f.linear.comp g.linear
  map_vadd' := by
    intro p v
    rw [Function.comp_apply]; rw [g.map_vadd]; rw [f.map_vadd]
    rfl
-/
def comp (f : P2 ->ᵃ[k] P3) (g : P1 ->ᵃ[k] P2) : P1 ->ᵃ[k] P3 where
  toFun := f ∘ g
  linear := f.linear.comp g.linear
  map_vadd' := by
    intro p v
    rw [Function.comp_apply]; rw [g.map_vadd]; rw [f.map_vadd]
    rfl

/-- Composition of affine maps acts as applying the two functions. -/
@[simp]
/--
theorem `coe_comp` / 定理 `coe_comp`

English:
theorem coe_comp
  given: (f : P2 ->ᵃ[k] P3) (g : P1 ->ᵃ[k] P2)
  statement: ⇑(f.comp g) = f ∘ g
  proof: rfl

中文:
定理 coe_comp
  条件: (f : P2 ->ᵃ[k] P3) (g : P1 ->ᵃ[k] P2)
  结论: ⇑(f.comp g) = f ∘ g
  证明: rfl
-/
theorem coe_comp (f : P2 ->ᵃ[k] P3) (g : P1 ->ᵃ[k] P2) : ⇑(f.comp g) = f ∘ g :=
  rfl

/--
theorem `comp_apply` / 定理 `comp_apply`

English:
theorem comp_apply
  given: (f : P2 ->ᵃ[k] P3) (g : P1 ->ᵃ[k] P2) (p : P1)
  statement: f.comp g p = f (g p)
  proof: rfl

@[simp]

中文:
定理 comp_apply
  条件: (f : P2 ->ᵃ[k] P3) (g : P1 ->ᵃ[k] P2) (p : P1)
  结论: f.comp g p = f (g p)
  证明: rfl

@[simp]
-/
theorem comp_apply (f : P2 ->ᵃ[k] P3) (g : P1 ->ᵃ[k] P2) (p : P1) : f.comp g p = f (g p) :=
  rfl

@[simp]
/--
theorem `comp_id` / 定理 `comp_id`

English:
theorem comp_id
  given: (f : P1 ->ᵃ[k] P2)
  statement: f.comp (id k P1) = f
  proof: ext fun _ => rfl

@[simp]

中文:
定理 comp_id
  条件: (f : P1 ->ᵃ[k] P2)
  结论: f.comp (id k P1) = f
  证明: ext fun _ => rfl

@[simp]
-/
theorem comp_id (f : P1 ->ᵃ[k] P2) : f.comp (id k P1) = f :=
  ext fun _ => rfl

@[simp]
/--
theorem `id_comp` / 定理 `id_comp`

English:
theorem id_comp
  given: (f : P1 ->ᵃ[k] P2)
  statement: (id k P2).comp f = f
  proof: ext fun _ => rfl

中文:
定理 id_comp
  条件: (f : P1 ->ᵃ[k] P2)
  结论: (id k P2).comp f = f
  证明: ext fun _ => rfl
-/
theorem id_comp (f : P1 ->ᵃ[k] P2) : (id k P2).comp f = f :=
  ext fun _ => rfl

/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  given: (f₃₄ : P3 ->ᵃ[k] P4) (f₂₃ : P2 ->ᵃ[k] P3) (f₁₂ : P1 ->ᵃ[k] P2)
  proof: rfl

中文:
定理 comp_assoc
  条件: (f₃₄ : P3 ->ᵃ[k] P4) (f₂₃ : P2 ->ᵃ[k] P3) (f₁₂ : P1 ->ᵃ[k] P2)
  证明: rfl
-/
theorem comp_assoc (f₃₄ : P3 ->ᵃ[k] P4) (f₂₃ : P2 ->ᵃ[k] P3) (f₁₂ : P1 ->ᵃ[k] P2) :
    (f₃₄.comp f₂₃).comp f₁₂ = f₃₄.comp (f₂₃.comp f₁₂) :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Monoid (P1 ->ᵃ[k] P1)
  body: id k P1
  mul := comp
  one_mul := id_comp
  mul_one := comp_id
  mul_assoc := comp_assoc

@[simp]

中文:
实例 :
  签名: 幺半群 (P1 ->ᵃ[k] P1)
  定义体: id k P1
  mul := comp
  one_mul := id_comp
  mul_one := comp_id
  mul_assoc := comp_assoc

@[simp]
-/
instance : Monoid (P1 ->ᵃ[k] P1) where
  one := id k P1
  mul := comp
  one_mul := id_comp
  mul_one := comp_id
  mul_assoc := comp_assoc

@[simp]
/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  given: (f g : P1 ->ᵃ[k] P1)
  statement: ⇑(f * g) = f ∘ g
  proof: rfl

@[simp]

中文:
定理 coe_mul
  条件: (f g : P1 ->ᵃ[k] P1)
  结论: ⇑(f * g) = f ∘ g
  证明: rfl

@[simp]
-/
theorem coe_mul (f g : P1 ->ᵃ[k] P1) : ⇑(f * g) = f ∘ g :=
  rfl

@[simp]
/--
theorem `coe_one` / 定理 `coe_one`

English:
theorem coe_one
  statement: ⇑(1 : P1 ->ᵃ[k] P1) = _root_.id
  proof: rfl

中文:
定理 coe_one
  结论: ⇑(1 : P1 ->ᵃ[k] P1) = _root_.id
  证明: rfl
-/
theorem coe_one : ⇑(1 : P1 ->ᵃ[k] P1) = _root_.id :=
  rfl

/-- `AffineMap.linear` on endomorphisms is a `MonoidHom`. -/
@[simps]
/--
Definition of `linearHom` / `linearHom` 的定义

English:
definition linearHom
  signature: : (P1 ->ᵃ[k] P1) ->* V1 ->ₗ[k] V1 where
  body: linear
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]

中文:
定义 linearHom
  签名: : (P1 ->ᵃ[k] P1) ->* V1 ->ₗ[k] V1 where
  定义体: linear
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]

Depends on / 依赖: linear
-/
def linearHom : (P1 ->ᵃ[k] P1) ->* V1 ->ₗ[k] V1 where
  toFun := linear
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
/--
theorem `linear_injective_iff` / 定理 `linear_injective_iff`

English:
theorem linear_injective_iff
  given: (f : P1 ->ᵃ[k] P2)
  proof: by
  obtain ⟨p⟩ := (inferInstance : Nonempty P1)
  have h : ⇑f.linear = (Equiv.vaddConst (f p)).symm ∘ f ∘ Equiv.vaddConst p := by
    ext v
    simp [f.map_vadd]
  rw [h]; rw [Equiv.comp_injective]; rw [Equiv.injective_comp]

@[simp]

中文:
定理 linear_injective_iff
  条件: (f : P1 ->ᵃ[k] P2)
  证明: by
  obtain ⟨p⟩ := (inferInstance : Nonempty P1)
  have h : ⇑f.linear = (Equiv.vaddConst (f p)).symm ∘ f ∘ Equiv.vaddConst p := by
    ext v
    simp [f.map_vadd]
  rw [h]; rw [Equiv.comp_injective]; rw [Equiv.injective_comp]

@[simp]

Depends on / 依赖: Equiv.comp_injective, Equiv.injective_comp, Equiv.vaddConst, Nonempty, comp_injective, f.linear, f.map_vadd, injective_comp, linear, map_vadd, vaddConst
-/
theorem linear_injective_iff (f : P1 ->ᵃ[k] P2) :
    Function.Injective f.linear ↔ Function.Injective f := by
  obtain ⟨p⟩ := (inferInstance : Nonempty P1)
  have h : ⇑f.linear = (Equiv.vaddConst (f p)).symm ∘ f ∘ Equiv.vaddConst p := by
    ext v
    simp [f.map_vadd]
  rw [h]; rw [Equiv.comp_injective]; rw [Equiv.injective_comp]

@[simp]
/--
theorem `linear_surjective_iff` / 定理 `linear_surjective_iff`

English:
theorem linear_surjective_iff
  given: (f : P1 ->ᵃ[k] P2)
  proof: by
  obtain ⟨p⟩ := (inferInstance : Nonempty P1)
  have h : ⇑f.linear = (Equiv.vaddConst (f p)).symm ∘ f ∘ Equiv.vaddConst p := by
    ext v
    simp [f.map_vadd]
  rw [h]; rw [Equiv.comp_surjective]; rw [Equiv.surjective_comp]

@[simp]

中文:
定理 linear_surjective_iff
  条件: (f : P1 ->ᵃ[k] P2)
  证明: by
  obtain ⟨p⟩ := (inferInstance : Nonempty P1)
  have h : ⇑f.linear = (Equiv.vaddConst (f p)).symm ∘ f ∘ Equiv.vaddConst p := by
    ext v
    simp [f.map_vadd]
  rw [h]; rw [Equiv.comp_surjective]; rw [Equiv.surjective_comp]

@[simp]

Depends on / 依赖: Equiv.comp_surjective, Equiv.surjective_comp, Equiv.vaddConst, Nonempty, comp_surjective, f.linear, f.map_vadd, linear, map_vadd, surjective_comp, vaddConst
-/
theorem linear_surjective_iff (f : P1 ->ᵃ[k] P2) :
    Function.Surjective f.linear ↔ Function.Surjective f := by
  obtain ⟨p⟩ := (inferInstance : Nonempty P1)
  have h : ⇑f.linear = (Equiv.vaddConst (f p)).symm ∘ f ∘ Equiv.vaddConst p := by
    ext v
    simp [f.map_vadd]
  rw [h]; rw [Equiv.comp_surjective]; rw [Equiv.surjective_comp]

@[simp]
/--
theorem `linear_bijective_iff` / 定理 `linear_bijective_iff`

English:
theorem linear_bijective_iff
  given: (f : P1 ->ᵃ[k] P2)
  proof: and_congr f.linear_injective_iff f.linear_surjective_iff

中文:
定理 linear_bijective_iff
  条件: (f : P1 ->ᵃ[k] P2)
  证明: and_congr f.linear_injective_iff f.linear_surjective_iff

Depends on / 依赖: and_congr, f.linear_injective_iff, f.linear_surjective_iff, linear_injective_iff, linear_surjective_iff
-/
theorem linear_bijective_iff (f : P1 ->ᵃ[k] P2) :
    Function.Bijective f.linear ↔ Function.Bijective f :=
  and_congr f.linear_injective_iff f.linear_surjective_iff

/--
theorem `image_vsub_image` / 定理 `image_vsub_image`

English:
theorem image_vsub_image
  given: {s t : Set P1} (f : P1 ->ᵃ[k] P2)
  proof: by
  ext v
  simp only [Set.mem_vsub, Set.mem_image,
    exists_exists_and_eq_and, ← f.linearMap_vsub]
  grind

中文:
定理 image_vsub_image
  条件: {s t : 集合 P1} (f : P1 ->ᵃ[k] P2)
  证明: by
  ext v
  simp only [Set.mem_vsub, Set.mem_image,
    exists_exists_and_eq_and, ← f.linearMap_vsub]
  grind

Depends on / 依赖: Set.mem_image, Set.mem_vsub, exists_exists_and_eq_and, f.linearMap_vsub, linearMap_vsub, mem_image, mem_vsub
-/
theorem image_vsub_image {s t : Set P1} (f : P1 ->ᵃ[k] P2) :
    f '' s -ᵥ f '' t = f.linear '' (s -ᵥ t) := by
  ext v
  simp only [Set.mem_vsub, Set.mem_image,
    exists_exists_and_eq_and, ← f.linearMap_vsub]
  grind

/-- The product of two affine maps is an affine map. -/
@[simps linear]
/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: (f : P1 ->ᵃ[k] P2) (g : P1 ->ᵃ[k] P3)
  body: Function.prod f g
  linear := f.linear.prod g.linear
  map_vadd' := by simp

中文:
定义 乘积
  签名: (f : P1 ->ᵃ[k] P2) (g : P1 ->ᵃ[k] P3)
  定义体: Function.prod f g
  linear := f.linear.prod g.linear
  map_vadd' := by simp

Depends on / 依赖: Function, Function.prod
-/
def prod (f : P1 ->ᵃ[k] P2) (g : P1 ->ᵃ[k] P3) : P1 ->ᵃ[k] P2 × P3 where
  toFun := Function.prod f g
  linear := f.linear.prod g.linear
  map_vadd' := by simp

/--
theorem `coe_prod` / 定理 `coe_prod`

English:
theorem coe_prod
  given: (f : P1 ->ᵃ[k] P2) (g : P1 ->ᵃ[k] P3)
  statement: prod f g = Function.prod f g
  proof: rfl

@[simp]

中文:
定理 coe_prod
  条件: (f : P1 ->ᵃ[k] P2) (g : P1 ->ᵃ[k] P3)
  结论: 乘积 f g = 函数.乘积 f g
  证明: rfl

@[simp]
-/
theorem coe_prod (f : P1 ->ᵃ[k] P2) (g : P1 ->ᵃ[k] P3) : prod f g = Function.prod f g :=
  rfl

@[simp]
/--
theorem `prod_apply` / 定理 `prod_apply`

English:
theorem prod_apply
  given: (f : P1 ->ᵃ[k] P2) (g : P1 ->ᵃ[k] P3) (p : P1)
  statement: prod f g p = (f p, g p)
  proof: rfl

中文:
定理 prod_apply
  条件: (f : P1 ->ᵃ[k] P2) (g : P1 ->ᵃ[k] P3) (p : P1)
  结论: 乘积 f g p = (f p, g p)
  证明: rfl
-/
theorem prod_apply (f : P1 ->ᵃ[k] P2) (g : P1 ->ᵃ[k] P3) (p : P1) : prod f g p = (f p, g p) :=
  rfl

/-- `Prod.map` of two affine maps. -/
@[simps linear]
/--
Definition of `prodMap` / `prodMap` 的定义

English:
definition prodMap
  signature: (f : P1 ->ᵃ[k] P2) (g : P3 ->ᵃ[k] P4)
  body: Prod.map f g
  linear := f.linear.prodMap g.linear
  map_vadd' := by simp

中文:
定义 prodMap
  签名: (f : P1 ->ᵃ[k] P2) (g : P3 ->ᵃ[k] P4)
  定义体: Prod.map f g
  linear := f.linear.prodMap g.linear
  map_vadd' := by simp

Depends on / 依赖: Prod.map
-/
def prodMap (f : P1 ->ᵃ[k] P2) (g : P3 ->ᵃ[k] P4) : P1 × P3 ->ᵃ[k] P2 × P4 where
  toFun := Prod.map f g
  linear := f.linear.prodMap g.linear
  map_vadd' := by simp

/--
theorem `coe_prodMap` / 定理 `coe_prodMap`

English:
theorem coe_prodMap
  given: (f : P1 ->ᵃ[k] P2) (g : P3 ->ᵃ[k] P4)
  statement: ⇑(f.prodMap g) = Prod.map f g
  proof: rfl

@[simp]

中文:
定理 coe_prodMap
  条件: (f : P1 ->ᵃ[k] P2) (g : P3 ->ᵃ[k] P4)
  结论: ⇑(f.prodMap g) = 积类型.map f g
  证明: rfl

@[simp]
-/
theorem coe_prodMap (f : P1 ->ᵃ[k] P2) (g : P3 ->ᵃ[k] P4) : ⇑(f.prodMap g) = Prod.map f g :=
  rfl

@[simp]
/--
theorem `prodMap_apply` / 定理 `prodMap_apply`

English:
theorem prodMap_apply
  given: (f : P1 ->ᵃ[k] P2) (g : P3 ->ᵃ[k] P4) (x)
  statement: f.prodMap g x = (f x.1, g x.2)
  proof: rfl

中文:
定理 prodMap_apply
  条件: (f : P1 ->ᵃ[k] P2) (g : P3 ->ᵃ[k] P4) (x)
  结论: f.prodMap g x = (f x.1, g x.2)
  证明: rfl
-/
theorem prodMap_apply (f : P1 ->ᵃ[k] P2) (g : P3 ->ᵃ[k] P4) (x) : f.prodMap g x = (f x.1, g x.2) :=
  rfl

/-! ### Definition of `AffineMap.lineMap` and lemmas about it -/

/--
Definition of `lineMap` / `lineMap` 的定义

English:
definition lineMap
  signature: (p₀ p₁ : P1)
  body: ((LinearMap.id : k ->ₗ[k] k).smulRight (p₁ -ᵥ p₀)).toAffineMap +ᵥ const k k p₀

中文:
定义 lineMap
  签名: (p₀ p₁ : P1)
  定义体: ((LinearMap.id : k ->ₗ[k] k).smulRight (p₁ -ᵥ p₀)).toAffineMap +ᵥ const k k p₀

Depends on / 依赖: LinearMap, LinearMap.id, smulRight, toAffineMap
-/
def lineMap (p₀ p₁ : P1) : k ->ᵃ[k] P1 :=
  ((LinearMap.id : k ->ₗ[k] k).smulRight (p₁ -ᵥ p₀)).toAffineMap +ᵥ const k k p₀

set_option backward.isDefEq.respectTransparency false in
/--
theorem `coe_lineMap` / 定理 `coe_lineMap`

English:
theorem coe_lineMap
  given: (p₀ p₁ : P1)
  statement: (lineMap p₀ p₁ : k -> P1) = fun c => c • (p₁ -ᵥ p₀) +ᵥ p₀
  proof: rfl

中文:
定理 coe_lineMap
  条件: (p₀ p₁ : P1)
  结论: (lineMap p₀ p₁ : k -> P1) = fun c => c • (p₁ -ᵥ p₀) +ᵥ p₀
  证明: rfl
-/
theorem coe_lineMap (p₀ p₁ : P1) : (lineMap p₀ p₁ : k -> P1) = fun c => c • (p₁ -ᵥ p₀) +ᵥ p₀ :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `lineMap_apply` / 定理 `lineMap_apply`

English:
theorem lineMap_apply
  given: (p₀ p₁ : P1) (c : k)
  statement: lineMap p₀ p₁ c = c • (p₁ -ᵥ p₀) +ᵥ p₀
  proof: rfl

中文:
定理 lineMap_apply
  条件: (p₀ p₁ : P1) (c : k)
  结论: lineMap p₀ p₁ c = c • (p₁ -ᵥ p₀) +ᵥ p₀
  证明: rfl
-/
theorem lineMap_apply (p₀ p₁ : P1) (c : k) : lineMap p₀ p₁ c = c • (p₁ -ᵥ p₀) +ᵥ p₀ :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `lineMap_apply_module'` / 定理 `lineMap_apply_module'`

English:
theorem lineMap_apply_module'
  given: (p₀ p₁ : V1) (c : k)
  statement: lineMap p₀ p₁ c = c • (p₁ - p₀) + p₀
  proof: rfl

中文:
定理 lineMap_apply_module'
  条件: (p₀ p₁ : V1) (c : k)
  结论: lineMap p₀ p₁ c = c • (p₁ - p₀) + p₀
  证明: rfl
-/
theorem lineMap_apply_module' (p₀ p₁ : V1) (c : k) : lineMap p₀ p₁ c = c • (p₁ - p₀) + p₀ :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `lineMap_apply_module` / 定理 `lineMap_apply_module`

English:
theorem lineMap_apply_module
  given: (p₀ p₁ : V1) (c : k)
  statement: lineMap p₀ p₁ c = (1 - c) • p₀ + c • p₁
  proof: by
  simp [lineMap_apply_module', smul_sub, sub_smul]; abel

中文:
定理 lineMap_apply_module
  条件: (p₀ p₁ : V1) (c : k)
  结论: lineMap p₀ p₁ c = (1 - c) • p₀ + c • p₁
  证明: by
  simp [lineMap_apply_module', smul_sub, sub_smul]; abel

Depends on / 依赖: lineMap_apply_module, smul_sub, sub_smul
-/
theorem lineMap_apply_module (p₀ p₁ : V1) (c : k) : lineMap p₀ p₁ c = (1 - c) • p₀ + c • p₁ := by
  simp [lineMap_apply_module', smul_sub, sub_smul]; abel

set_option backward.isDefEq.respectTransparency false in
/--
theorem `lineMap_apply_ring'` / 定理 `lineMap_apply_ring'`

English:
theorem lineMap_apply_ring'
  given: (a b c : k)
  statement: lineMap a b c = c * (b - a) + a
  proof: rfl

中文:
定理 lineMap_apply_ring'
  条件: (a b c : k)
  结论: lineMap a b c = c * (b - a) + a
  证明: rfl
-/
theorem lineMap_apply_ring' (a b c : k) : lineMap a b c = c * (b - a) + a :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `lineMap_apply_ring` / 定理 `lineMap_apply_ring`

English:
theorem lineMap_apply_ring
  given: (a b c : k)
  statement: lineMap a b c = (1 - c) * a + c * b
  proof: lineMap_apply_module a b c

中文:
定理 lineMap_apply_ring
  条件: (a b c : k)
  结论: lineMap a b c = (1 - c) * a + c * b
  证明: lineMap_apply_module a b c

Depends on / 依赖: lineMap_apply_module
-/
theorem lineMap_apply_ring (a b c : k) : lineMap a b c = (1 - c) * a + c * b :=
  lineMap_apply_module a b c

set_option backward.isDefEq.respectTransparency false in
/--
theorem `lineMap_vadd_apply` / 定理 `lineMap_vadd_apply`

English:
theorem lineMap_vadd_apply
  given: (p : P1) (v : V1) (c : k)
  statement: lineMap p (v +ᵥ p) c = c • v +ᵥ p
  proof: by
  rw [lineMap_apply]; rw [vadd_vsub]

@[simp]

中文:
定理 lineMap_vadd_apply
  条件: (p : P1) (v : V1) (c : k)
  结论: lineMap p (v +ᵥ p) c = c • v +ᵥ p
  证明: by
  rw [lineMap_apply]; rw [vadd_vsub]

@[simp]

Depends on / 依赖: lineMap_apply, vadd_vsub
-/
theorem lineMap_vadd_apply (p : P1) (v : V1) (c : k) : lineMap p (v +ᵥ p) c = c • v +ᵥ p := by
  rw [lineMap_apply]; rw [vadd_vsub]

@[simp]
/--
theorem `lineMap_linear` / 定理 `lineMap_linear`

English:
theorem lineMap_linear
  given: (p₀ p₁ : P1)
  proof: add_zero _

中文:
定理 lineMap_linear
  条件: (p₀ p₁ : P1)
  证明: add_zero _

Depends on / 依赖: add_zero
-/
theorem lineMap_linear (p₀ p₁ : P1) :
    (lineMap p₀ p₁ : k ->ᵃ[k] P1).linear = LinearMap.id.smulRight (p₁ -ᵥ p₀) :=
  add_zero _

set_option backward.isDefEq.respectTransparency false in
/--
theorem `lineMap_same_apply` / 定理 `lineMap_same_apply`

English:
theorem lineMap_same_apply
  given: (p : P1) (c : k)
  statement: lineMap p p c = p
  proof: by
  simp [lineMap_apply]

@[simp]

中文:
定理 lineMap_same_apply
  条件: (p : P1) (c : k)
  结论: lineMap p p c = p
  证明: by
  simp [lineMap_apply]

@[simp]

Depends on / 依赖: lineMap_apply
-/
theorem lineMap_same_apply (p : P1) (c : k) : lineMap p p c = p := by
  simp [lineMap_apply]

@[simp]
/--
theorem `lineMap_same` / 定理 `lineMap_same`

English:
theorem lineMap_same
  given: (p : P1)
  statement: lineMap p p = const k k p
  proof: ext lineMap_same_apply p

中文:
定理 lineMap_same
  条件: (p : P1)
  结论: lineMap p p = const k k p
  证明: ext lineMap_same_apply p

Depends on / 依赖: lineMap_same_apply
-/
theorem lineMap_same (p : P1) : lineMap p p = const k k p :=
ext lineMap_same_apply p

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `lineMap_apply_zero` / 定理 `lineMap_apply_zero`

English:
theorem lineMap_apply_zero
  given: (p₀ p₁ : P1)
  statement: lineMap p₀ p₁ (0 : k) = p₀
  proof: by
  simp [lineMap_apply]

中文:
定理 lineMap_apply_zero
  条件: (p₀ p₁ : P1)
  结论: lineMap p₀ p₁ (0 : k) = p₀
  证明: by
  simp [lineMap_apply]

Depends on / 依赖: lineMap_apply
-/
theorem lineMap_apply_zero (p₀ p₁ : P1) : lineMap p₀ p₁ (0 : k) = p₀ := by
  simp [lineMap_apply]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `lineMap_apply_one` / 定理 `lineMap_apply_one`

English:
theorem lineMap_apply_one
  given: (p₀ p₁ : P1)
  statement: lineMap p₀ p₁ (1 : k) = p₁
  proof: by
  simp [lineMap_apply]

中文:
定理 lineMap_apply_one
  条件: (p₀ p₁ : P1)
  结论: lineMap p₀ p₁ (1 : k) = p₁
  证明: by
  simp [lineMap_apply]

Depends on / 依赖: lineMap_apply
-/
theorem lineMap_apply_one (p₀ p₁ : P1) : lineMap p₀ p₁ (1 : k) = p₁ := by
  simp [lineMap_apply]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `lineMap_eq_lineMap_iff` / 定理 `lineMap_eq_lineMap_iff`

English:
theorem lineMap_eq_lineMap_iff
  given: [IsDomain k] [IsTorsionFree k V1] {p₀ p₁ : P1} {c₁ c₂ : k}
  proof: by
  rw [lineMap_apply]; rw [lineMap_apply]; rw [← @vsub_eq_zero_iff_eq V1]; rw [vadd_vsub_vadd_cancel_right]; rw [←
    sub_smul]; rw [smul_eq_zero]; rw [sub_eq_zero]; rw [vsub_eq_zero_iff_eq]; rw [or_comm]; rw [eq_comm]

中文:
定理 lineMap_eq_lineMap_iff
  条件: [是整环 k] [是无挠 k V1] {p₀ p₁ : P1} {c₁ c₂ : k}
  证明: by
  rw [lineMap_apply]; rw [lineMap_apply]; rw [← @vsub_eq_zero_iff_eq V1]; rw [vadd_vsub_vadd_cancel_right]; rw [←
    sub_smul]; rw [smul_eq_zero]; rw [sub_eq_zero]; rw [vsub_eq_zero_iff_eq]; rw [or_comm]; rw [eq_comm]

Depends on / 依赖: eq_comm, lineMap_apply, or_comm, smul_eq_zero, sub_eq_zero, sub_smul, vadd_vsub_vadd_cancel_right, vsub_eq_zero_iff_eq
-/
theorem lineMap_eq_lineMap_iff [IsDomain k] [IsTorsionFree k V1] {p₀ p₁ : P1} {c₁ c₂ : k} :
    lineMap p₀ p₁ c₁ = lineMap p₀ p₁ c₂ ↔ p₀ = p₁ ∨ c₁ = c₂ := by
  rw [lineMap_apply]; rw [lineMap_apply]; rw [← @vsub_eq_zero_iff_eq V1]; rw [vadd_vsub_vadd_cancel_right]; rw [←
    sub_smul]; rw [smul_eq_zero]; rw [sub_eq_zero]; rw [vsub_eq_zero_iff_eq]; rw [or_comm]; rw [eq_comm]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `lineMap_eq_left_iff` / 定理 `lineMap_eq_left_iff`

English:
theorem lineMap_eq_left_iff
  given: [IsDomain k] [IsTorsionFree k V1] {p₀ p₁ : P1} {c : k}
  proof: by
  rw [← @lineMap_eq_lineMap_iff k V1]; rw [lineMap_apply_zero]

中文:
定理 lineMap_eq_left_iff
  条件: [是整环 k] [是无挠 k V1] {p₀ p₁ : P1} {c : k}
  证明: by
  rw [← @lineMap_eq_lineMap_iff k V1]; rw [lineMap_apply_zero]

Depends on / 依赖: lineMap_apply_zero, lineMap_eq_lineMap_iff
-/
theorem lineMap_eq_left_iff [IsDomain k] [IsTorsionFree k V1] {p₀ p₁ : P1} {c : k} :
    lineMap p₀ p₁ c = p₀ ↔ p₀ = p₁ ∨ c = 0 := by
  rw [← @lineMap_eq_lineMap_iff k V1]; rw [lineMap_apply_zero]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `lineMap_eq_right_iff` / 定理 `lineMap_eq_right_iff`

English:
theorem lineMap_eq_right_iff
  given: [IsDomain k] [IsTorsionFree k V1] {p₀ p₁ : P1} {c : k}
  proof: by
  rw [← @lineMap_eq_lineMap_iff k V1]; rw [lineMap_apply_one]

中文:
定理 lineMap_eq_right_iff
  条件: [是整环 k] [是无挠 k V1] {p₀ p₁ : P1} {c : k}
  证明: by
  rw [← @lineMap_eq_lineMap_iff k V1]; rw [lineMap_apply_one]

Depends on / 依赖: lineMap_apply_one, lineMap_eq_lineMap_iff
-/
theorem lineMap_eq_right_iff [IsDomain k] [IsTorsionFree k V1] {p₀ p₁ : P1} {c : k} :
    lineMap p₀ p₁ c = p₁ ↔ p₀ = p₁ ∨ c = 1 := by
  rw [← @lineMap_eq_lineMap_iff k V1]; rw [lineMap_apply_one]

set_option backward.isDefEq.respectTransparency false in
variable (k) in
/--
theorem `lineMap_injective` / 定理 `lineMap_injective`

English:
theorem lineMap_injective
  given: [IsDomain k] [IsTorsionFree k V1] {p₀ p₁ : P1} (h : p₀ != p₁)
  proof: fun _c₁ _c₂ hc =>
  (lineMap_eq_lineMap_iff.mp hc).resolve_left h

中文:
定理 lineMap_injective
  条件: [是整环 k] [是无挠 k V1] {p₀ p₁ : P1} (h : p₀ != p₁)
  证明: fun _c₁ _c₂ hc =>
  (lineMap_eq_lineMap_iff.mp hc).resolve_left h
-/
theorem lineMap_injective [IsDomain k] [IsTorsionFree k V1] {p₀ p₁ : P1} (h : p₀ != p₁) :
    Function.Injective (lineMap p₀ p₁ : k -> P1) := fun _c₁ _c₂ hc =>
  (lineMap_eq_lineMap_iff.mp hc).resolve_left h

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `apply_lineMap` / 定理 `apply_lineMap`

English:
theorem apply_lineMap
  given: (f : P1 ->ᵃ[k] P2) (p₀ p₁ : P1) (c : k)
  proof: by
  simp [lineMap_apply]

@[simp]

中文:
定理 apply_lineMap
  条件: (f : P1 ->ᵃ[k] P2) (p₀ p₁ : P1) (c : k)
  证明: by
  simp [lineMap_apply]

@[simp]

Depends on / 依赖: lineMap_apply
-/
theorem apply_lineMap (f : P1 ->ᵃ[k] P2) (p₀ p₁ : P1) (c : k) :
    f (lineMap p₀ p₁ c) = lineMap (f p₀) (f p₁) c := by
  simp [lineMap_apply]

@[simp]
/--
theorem `comp_lineMap` / 定理 `comp_lineMap`

English:
theorem comp_lineMap
  given: (f : P1 ->ᵃ[k] P2) (p₀ p₁ : P1)
  proof: ext f.apply_lineMap p₀ p₁

中文:
定理 comp_lineMap
  条件: (f : P1 ->ᵃ[k] P2) (p₀ p₁ : P1)
  证明: ext f.apply_lineMap p₀ p₁

Depends on / 依赖: apply_lineMap, f.apply_lineMap
-/
theorem comp_lineMap (f : P1 ->ᵃ[k] P2) (p₀ p₁ : P1) :
    f.comp (lineMap p₀ p₁) = lineMap (f p₀) (f p₁) :=
ext f.apply_lineMap p₀ p₁

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `fst_lineMap` / 定理 `fst_lineMap`

English:
theorem fst_lineMap
  given: (p₀ p₁ : P1 × P2) (c : k)
  statement: (lineMap p₀ p₁ c).1 = lineMap p₀.1 p₁.1 c
  proof: fst.apply_lineMap p₀ p₁ c

中文:
定理 fst_lineMap
  条件: (p₀ p₁ : P1 × P2) (c : k)
  结论: (lineMap p₀ p₁ c).1 = lineMap p₀.1 p₁.1 c
  证明: fst.apply_lineMap p₀ p₁ c

Depends on / 依赖: apply_lineMap, fst.apply_lineMap
-/
theorem fst_lineMap (p₀ p₁ : P1 × P2) (c : k) : (lineMap p₀ p₁ c).1 = lineMap p₀.1 p₁.1 c :=
  fst.apply_lineMap p₀ p₁ c

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `snd_lineMap` / 定理 `snd_lineMap`

English:
theorem snd_lineMap
  given: (p₀ p₁ : P1 × P2) (c : k)
  statement: (lineMap p₀ p₁ c).2 = lineMap p₀.2 p₁.2 c
  proof: snd.apply_lineMap p₀ p₁ c

中文:
定理 snd_lineMap
  条件: (p₀ p₁ : P1 × P2) (c : k)
  结论: (lineMap p₀ p₁ c).2 = lineMap p₀.2 p₁.2 c
  证明: snd.apply_lineMap p₀ p₁ c

Depends on / 依赖: apply_lineMap, snd.apply_lineMap
-/
theorem snd_lineMap (p₀ p₁ : P1 × P2) (c : k) : (lineMap p₀ p₁ c).2 = lineMap p₀.2 p₁.2 c :=
  snd.apply_lineMap p₀ p₁ c

/--
theorem `lineMap_symm` / 定理 `lineMap_symm`

English:
theorem lineMap_symm
  given: (p₀ p₁ : P1)
  proof: by
  simp

中文:
定理 lineMap_symm
  条件: (p₀ p₁ : P1)
  证明: by
  simp
-/
theorem lineMap_symm (p₀ p₁ : P1) :
    lineMap p₀ p₁ = (lineMap p₁ p₀).comp (lineMap (1 : k) (0 : k)) := by
  simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `lineMap_apply_one_sub` / 定理 `lineMap_apply_one_sub`

English:
theorem lineMap_apply_one_sub
  given: (p₀ p₁ : P1) (c : k)
  statement: lineMap p₀ p₁ (1 - c) = lineMap p₁ p₀ c
  proof: by
  rw [lineMap_symm p₀]; rw [comp_apply]
  congr
  simp [lineMap_apply]

中文:
定理 lineMap_apply_one_sub
  条件: (p₀ p₁ : P1) (c : k)
  结论: lineMap p₀ p₁ (1 - c) = lineMap p₁ p₀ c
  证明: by
  rw [lineMap_symm p₀]; rw [comp_apply]
  congr
  simp [lineMap_apply]

Depends on / 依赖: comp_apply, lineMap_apply, lineMap_symm
-/
theorem lineMap_apply_one_sub (p₀ p₁ : P1) (c : k) : lineMap p₀ p₁ (1 - c) = lineMap p₁ p₀ c := by
  rw [lineMap_symm p₀]; rw [comp_apply]
  congr
  simp [lineMap_apply]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `lineMap_vsub_left` / 定理 `lineMap_vsub_left`

English:
theorem lineMap_vsub_left
  given: (p₀ p₁ : P1) (c : k)
  statement: lineMap p₀ p₁ c -ᵥ p₀ = c • (p₁ -ᵥ p₀)
  proof: vadd_vsub _ _

中文:
定理 lineMap_vsub_left
  条件: (p₀ p₁ : P1) (c : k)
  结论: lineMap p₀ p₁ c -ᵥ p₀ = c • (p₁ -ᵥ p₀)
  证明: vadd_vsub _ _

Depends on / 依赖: vadd_vsub
-/
theorem lineMap_vsub_left (p₀ p₁ : P1) (c : k) : lineMap p₀ p₁ c -ᵥ p₀ = c • (p₁ -ᵥ p₀) :=
  vadd_vsub _ _

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `left_vsub_lineMap` / 定理 `left_vsub_lineMap`

English:
theorem left_vsub_lineMap
  given: (p₀ p₁ : P1) (c : k)
  statement: p₀ -ᵥ lineMap p₀ p₁ c = c • (p₀ -ᵥ p₁)
  proof: by
  rw [← neg_vsub_eq_vsub_rev]; rw [lineMap_vsub_left]; rw [← smul_neg]; rw [neg_vsub_eq_vsub_rev]

中文:
定理 left_vsub_lineMap
  条件: (p₀ p₁ : P1) (c : k)
  结论: p₀ -ᵥ lineMap p₀ p₁ c = c • (p₀ -ᵥ p₁)
  证明: by
  rw [← neg_vsub_eq_vsub_rev]; rw [lineMap_vsub_left]; rw [← smul_neg]; rw [neg_vsub_eq_vsub_rev]

Depends on / 依赖: lineMap_vsub_left, neg_vsub_eq_vsub_rev, smul_neg
-/
theorem left_vsub_lineMap (p₀ p₁ : P1) (c : k) : p₀ -ᵥ lineMap p₀ p₁ c = c • (p₀ -ᵥ p₁) := by
  rw [← neg_vsub_eq_vsub_rev]; rw [lineMap_vsub_left]; rw [← smul_neg]; rw [neg_vsub_eq_vsub_rev]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `lineMap_vsub_right` / 定理 `lineMap_vsub_right`

English:
theorem lineMap_vsub_right
  given: (p₀ p₁ : P1) (c : k)
  statement: lineMap p₀ p₁ c -ᵥ p₁ = (1 - c) • (p₀ -ᵥ p₁)
  proof: by
  rw [← lineMap_apply_one_sub]; rw [lineMap_vsub_left]

中文:
定理 lineMap_vsub_right
  条件: (p₀ p₁ : P1) (c : k)
  结论: lineMap p₀ p₁ c -ᵥ p₁ = (1 - c) • (p₀ -ᵥ p₁)
  证明: by
  rw [← lineMap_apply_one_sub]; rw [lineMap_vsub_left]

Depends on / 依赖: lineMap_apply_one_sub, lineMap_vsub_left
-/
theorem lineMap_vsub_right (p₀ p₁ : P1) (c : k) : lineMap p₀ p₁ c -ᵥ p₁ = (1 - c) • (p₀ -ᵥ p₁) := by
  rw [← lineMap_apply_one_sub]; rw [lineMap_vsub_left]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `right_vsub_lineMap` / 定理 `right_vsub_lineMap`

English:
theorem right_vsub_lineMap
  given: (p₀ p₁ : P1) (c : k)
  statement: p₁ -ᵥ lineMap p₀ p₁ c = (1 - c) • (p₁ -ᵥ p₀)
  proof: by
  rw [← lineMap_apply_one_sub]; rw [left_vsub_lineMap]

中文:
定理 right_vsub_lineMap
  条件: (p₀ p₁ : P1) (c : k)
  结论: p₁ -ᵥ lineMap p₀ p₁ c = (1 - c) • (p₁ -ᵥ p₀)
  证明: by
  rw [← lineMap_apply_one_sub]; rw [left_vsub_lineMap]

Depends on / 依赖: left_vsub_lineMap, lineMap_apply_one_sub
-/
theorem right_vsub_lineMap (p₀ p₁ : P1) (c : k) : p₁ -ᵥ lineMap p₀ p₁ c = (1 - c) • (p₁ -ᵥ p₀) := by
  rw [← lineMap_apply_one_sub]; rw [left_vsub_lineMap]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `lineMap_vadd_lineMap` / 定理 `lineMap_vadd_lineMap`

English:
theorem lineMap_vadd_lineMap
  given: (v₁ v₂ : V1) (p₁ p₂ : P1) (c : k)
  proof: ((fst : V1 × P1 ->ᵃ[k] V1) +ᵥ (snd : V1 × P1 ->ᵃ[k] P1)).apply_lineMap (v₁, p₁) (v₂, p₂) c

中文:
定理 lineMap_vadd_lineMap
  条件: (v₁ v₂ : V1) (p₁ p₂ : P1) (c : k)
  证明: ((fst : V1 × P1 ->ᵃ[k] V1) +ᵥ (snd : V1 × P1 ->ᵃ[k] P1)).apply_lineMap (v₁, p₁) (v₂, p₂) c

Depends on / 依赖: apply_lineMap
-/
theorem lineMap_vadd_lineMap (v₁ v₂ : V1) (p₁ p₂ : P1) (c : k) :
    lineMap v₁ v₂ c +ᵥ lineMap p₁ p₂ c = lineMap (v₁ +ᵥ p₁) (v₂ +ᵥ p₂) c :=
  ((fst : V1 × P1 ->ᵃ[k] V1) +ᵥ (snd : V1 × P1 ->ᵃ[k] P1)).apply_lineMap (v₁, p₁) (v₂, p₂) c

set_option backward.isDefEq.respectTransparency false in
/--
theorem `lineMap_vsub_lineMap` / 定理 `lineMap_vsub_lineMap`

English:
theorem lineMap_vsub_lineMap
  given: (p₁ p₂ p₃ p₄ : P1) (c : k)
  proof: ((fst : P1 × P1 ->ᵃ[k] P1) -ᵥ (snd : P1 × P1 ->ᵃ[k] P1)).apply_lineMap (_, _) (_, _) c

中文:
定理 lineMap_vsub_lineMap
  条件: (p₁ p₂ p₃ p₄ : P1) (c : k)
  证明: ((fst : P1 × P1 ->ᵃ[k] P1) -ᵥ (snd : P1 × P1 ->ᵃ[k] P1)).apply_lineMap (_, _) (_, _) c

Depends on / 依赖: apply_lineMap
-/
theorem lineMap_vsub_lineMap (p₁ p₂ p₃ p₄ : P1) (c : k) :
    lineMap p₁ p₂ c -ᵥ lineMap p₃ p₄ c = lineMap (p₁ -ᵥ p₃) (p₂ -ᵥ p₄) c :=
  ((fst : P1 × P1 ->ᵃ[k] P1) -ᵥ (snd : P1 × P1 ->ᵃ[k] P1)).apply_lineMap (_, _) (_, _) c

set_option backward.isDefEq.respectTransparency false in
/--
lemma `lineMap_lineMap_right` / 引理 `lineMap_lineMap_right`

English:
lemma lineMap_lineMap_right
  given: (p₀ p₁ : P1) (c d : k)
  proof: by simp [lineMap_apply, mul_smul]

中文:
引理 lineMap_lineMap_right
  条件: (p₀ p₁ : P1) (c d : k)
  证明: by simp [lineMap_apply, mul_smul]
-/
@[simp] lemma lineMap_lineMap_right (p₀ p₁ : P1) (c d : k) :
    lineMap p₀ (lineMap p₀ p₁ c) d = lineMap p₀ p₁ (d * c) := by simp [lineMap_apply, mul_smul]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `lineMap_lineMap_left` / 引理 `lineMap_lineMap_left`

English:
lemma lineMap_lineMap_left
  given: (p₀ p₁ : P1) (c d : k)
  proof: by
  simp_rw [lineMap_apply_one_sub, ← lineMap_apply_one_sub p₁, lineMap_lineMap_right]

中文:
引理 lineMap_lineMap_left
  条件: (p₀ p₁ : P1) (c d : k)
  证明: by
  simp_rw [lineMap_apply_one_sub, ← lineMap_apply_one_sub p₁, lineMap_lineMap_right]
-/
@[simp] lemma lineMap_lineMap_left (p₀ p₁ : P1) (c d : k) :
    lineMap (lineMap p₀ p₁ c) p₁ d = lineMap p₀ p₁ (1 - (1 - d) * (1 - c)) := by
  simp_rw [lineMap_apply_one_sub, ← lineMap_apply_one_sub p₁, lineMap_lineMap_right]

/--
lemma `lineMap_mono` / 引理 `lineMap_mono`

English:
lemma lineMap_mono
  statement: [LinearOrder k] [Preorder V1] [AddRightMono V1] [SMulPosMono k V1]
  proof: by
  intro x y hxy
  suffices x • (p₁ - p₀) <= y • (p₁ - p₀) by simpa [lineMap]
  gcongr
  simpa

中文:
引理 lineMap_mono
  结论: [线性序 k] [预序 V1] [AddRightMono V1] [标量乘正递增 k V1]
  证明: by
  intro x y hxy
  suffices x • (p₁ - p₀) <= y • (p₁ - p₀) by simpa [lineMap]
  gcongr
  simpa

Depends on / 依赖: lineMap
-/
lemma lineMap_mono [LinearOrder k] [Preorder V1] [AddRightMono V1] [SMulPosMono k V1]
    {p₀ p₁ : V1} (h : p₀ <= p₁) :
    Monotone (lineMap (k := k) p₀ p₁) := by
  intro x y hxy
  suffices x • (p₁ - p₀) <= y • (p₁ - p₀) by simpa [lineMap]
  gcongr
  simpa

/--
lemma `lineMap_anti` / 引理 `lineMap_anti`

English:
lemma lineMap_anti
  statement: [LinearOrder k] [Preorder V1] [AddLeftMono V1] [SMulPosMono k V1]
  proof: by
  intro x y hxy
  suffices y • (p₁ - p₀) <= x • (p₁ - p₀) by simpa [lineMap]
  rw [← neg_le_neg_iff]; rw [← smul_neg]; rw [← smul_neg]
  gcongr
  simpa

中文:
引理 lineMap_anti
  结论: [线性序 k] [预序 V1] [AddLeftMono V1] [标量乘正递增 k V1]
  证明: by
  intro x y hxy
  suffices y • (p₁ - p₀) <= x • (p₁ - p₀) by simpa [lineMap]
  rw [← neg_le_neg_iff]; rw [← smul_neg]; rw [← smul_neg]
  gcongr
  simpa

Depends on / 依赖: lineMap, neg_le_neg_iff, smul_neg
-/
lemma lineMap_anti [LinearOrder k] [Preorder V1] [AddLeftMono V1] [SMulPosMono k V1]
    {p₀ p₁ : V1} (h : p₁ <= p₀) :
    Antitone (lineMap (k := k) p₀ p₁) := by
  intro x y hxy
  suffices y • (p₁ - p₀) <= x • (p₁ - p₀) by simpa [lineMap]
  rw [← neg_le_neg_iff]; rw [← smul_neg]; rw [← smul_neg]
  gcongr
  simpa

/--
theorem `decomp` / 定理 `decomp`

English:
theorem decomp
  given: (f : V1 ->ᵃ[k] V2)
  statement: (f : V1 -> V2) = ⇑f.linear + fun _ => f 0
  proof: by
  ext x
  calc
    f x = f.linear x +ᵥ f 0 := by rw [← f.map_vadd, vadd_eq_add, add_zero]
    _ = (f.linear + fun _ : V1 => f 0) x := rfl

中文:
定理 decomp
  条件: (f : V1 ->ᵃ[k] V2)
  结论: (f : V1 -> V2) = ⇑f.linear + fun _ => f 0
  证明: by
  ext x
  calc
    f x = f.linear x +ᵥ f 0 := by rw [← f.map_vadd, vadd_eq_add, add_zero]
    _ = (f.linear + fun _ : V1 => f 0) x := rfl

Depends on / 依赖: add_zero, f.linear, f.map_vadd, linear, map_vadd, vadd_eq_add
-/
theorem decomp (f : V1 ->ᵃ[k] V2) : (f : V1 -> V2) = ⇑f.linear + fun _ => f 0 := by
  ext x
  calc
    f x = f.linear x +ᵥ f 0 := by rw [← f.map_vadd, vadd_eq_add, add_zero]
    _ = (f.linear + fun _ : V1 => f 0) x := rfl

/--
theorem `decomp'` / 定理 `decomp'`

English:
theorem decomp'
  given: (f : V1 ->ᵃ[k] V2)
  statement: (f.linear : V1 -> V2) = ⇑f - fun _ => f 0
  proof: by
  rw [decomp]
  simp only [map_zero, Pi.add_apply, add_sub_cancel_right, zero_add]

中文:
定理 decomp'
  条件: (f : V1 ->ᵃ[k] V2)
  结论: (f.linear : V1 -> V2) = ⇑f - fun _ => f 0
  证明: by
  rw [decomp]
  simp only [map_zero, Pi.add_apply, add_sub_cancel_right, zero_add]

Depends on / 依赖: Pi.add_apply, add_apply, add_sub_cancel_right, decomp, map_zero, zero_add
-/
theorem decomp' (f : V1 ->ᵃ[k] V2) : (f.linear : V1 -> V2) = ⇑f - fun _ => f 0 := by
  rw [decomp]
  simp only [map_zero, Pi.add_apply, add_sub_cancel_right, zero_add]

/--
theorem `image_uIcc` / 定理 `image_uIcc`

English:
theorem image_uIcc
  statement: {k : Type*} [Field k] [LinearOrder k] [IsStrictOrderedRing k]
  proof: by
  have : ⇑f = (fun x => x + f 0) ∘ fun x => x * (f 1 - f 0) := by
    ext x
    change f x = x • (f 1 -ᵥ f 0) +ᵥ f 0
    rw [← f.linearMap_vsub]; rw [← f.linear.map_smul]; rw [← f.map_vadd]
    simp only [vsub_eq_sub, add_zero, mul_one, vadd_eq_add, sub_zero, smul_eq_mul]
  rw [this]; rw [Set.ima

中文:
定理 image_uIcc
  结论: {k : 类型} [域 k] [线性序 k] [是StrictOrdered环 k]
  证明: by
  have : ⇑f = (fun x => x + f 0) ∘ fun x => x * (f 1 - f 0) := by
    ext x
    change f x = x • (f 1 -ᵥ f 0) +ᵥ f 0
    rw [← f.linearMap_vsub]; rw [← f.linear.map_smul]; rw [← f.map_vadd]
    simp only [vsub_eq_sub, add_zero, mul_one, vadd_eq_add, sub_zero, smul_eq_mul]
  rw [this]; rw [Set.ima

Depends on / 依赖: Function, Function.comp_apply, Set.image_add_const_uIcc, Set.image_comp, Set.image_mul_const_uIcc, add_zero, comp_apply, f.linear.map_smul, f.linearMap_vsub, f.map_vadd, image_add_const_uIcc, image_comp, image_mul_const_uIcc, linear, linearMap_vsub, map_smul, map_vadd, mul_one, smul_eq_mul, sub_zero
-/
theorem image_uIcc {k : Type*} [Field k] [LinearOrder k] [IsStrictOrderedRing k]
    (f : k ->ᵃ[k] k) (a b : k) :
    f '' Set.uIcc a b = Set.uIcc (f a) (f b) := by
  have : ⇑f = (fun x => x + f 0) ∘ fun x => x * (f 1 - f 0) := by
    ext x
    change f x = x • (f 1 -ᵥ f 0) +ᵥ f 0
    rw [← f.linearMap_vsub]; rw [← f.linear.map_smul]; rw [← f.map_vadd]
    simp only [vsub_eq_sub, add_zero, mul_one, vadd_eq_add, sub_zero, smul_eq_mul]
  rw [this]; rw [Set.image_comp]
  simp only [Set.image_add_const_uIcc, Set.image_mul_const_uIcc, Function.comp_apply]

section

variable {ι : Type*} {V : ι -> Type*} {P : ι -> Type*} [forall i, AddCommGroup (V i)]
  [forall i, Module k (V i)] [forall i, AddTorsor (V i) (P i)]

/--
Definition of `proj` / `proj` 的定义

English:
definition proj
  signature: (i : ι)
  body: f i
  linear := @LinearMap.proj k ι _ V _ _ i
  map_vadd' _ _ := rfl

@[simp]

中文:
定义 proj
  签名: (i : ι)
  定义体: f i
  linear := @LinearMap.proj k ι _ V _ _ i
  map_vadd' _ _ := rfl

@[simp]
-/
def proj (i : ι) : (forall i : ι, P i) ->ᵃ[k] P i where
  toFun f := f i
  linear := @LinearMap.proj k ι _ V _ _ i
  map_vadd' _ _ := rfl

@[simp]
/--
theorem `proj_apply` / 定理 `proj_apply`

English:
theorem proj_apply
  given: (i : ι) (f : forall i, P i)
  statement: @proj k _ ι V P _ _ _ i f = f i
  proof: rfl

@[simp]

中文:
定理 proj_apply
  条件: (i : ι) (f : 对任意 i, P i)
  结论: @proj k _ ι V P _ _ _ i f = f i
  证明: rfl

@[simp]
-/
theorem proj_apply (i : ι) (f : forall i, P i) : @proj k _ ι V P _ _ _ i f = f i :=
  rfl

@[simp]
/--
theorem `proj_linear` / 定理 `proj_linear`

English:
theorem proj_linear
  given: (i : ι)
  statement: (@proj k _ ι V P _ _ _ i).linear = @LinearMap.proj k ι _ V _ _ i
  proof: rfl

中文:
定理 proj_linear
  条件: (i : ι)
  结论: (@proj k _ ι V P _ _ _ i).linear = @线性映射.proj k ι _ V _ _ i
  证明: rfl
-/
theorem proj_linear (i : ι) : (@proj k _ ι V P _ _ _ i).linear = @LinearMap.proj k ι _ V _ _ i :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `pi_lineMap_apply` / 定理 `pi_lineMap_apply`

English:
theorem pi_lineMap_apply
  given: (f g : forall i, P i) (c : k) (i : ι)
  proof: (proj i : (forall i, P i) ->ᵃ[k] P i).apply_lineMap f g c

中文:
定理 pi_lineMap_apply
  条件: (f g : 对任意 i, P i) (c : k) (i : ι)
  证明: (proj i : (forall i, P i) ->ᵃ[k] P i).apply_lineMap f g c

Depends on / 依赖: apply_lineMap
-/
theorem pi_lineMap_apply (f g : forall i, P i) (c : k) (i : ι) :
    lineMap f g c i = lineMap (f i) (g i) c :=
  (proj i : (forall i, P i) ->ᵃ[k] P i).apply_lineMap f g c

end

end AffineMap

namespace AffineMap

variable {R k V1 P1 V2 P2 V3 P3 : Type*}

section Ring

variable [Ring k] [AddCommGroup V1] [AffineSpace V1 P1] [AddCommGroup V2] [AffineSpace V2 P2]
variable [AddCommGroup V3] [AffineSpace V3 P3] [Module k V1] [Module k V2] [Module k V3]

section DistribMulAction

variable [Monoid R] [DistribMulAction R V2] [SMulCommClass k R V2]

/--
Instance `distribMulAction` / 实例 `distribMulAction`

English:
instance distribMulAction
  signature: : DistribMulAction R (P1 ->ᵃ[k] V2) where
  body: ext fun _ => smul_add _ _ _
  smul_zero _ := ext fun _ => smul_zero _

中文:
实例 distribMulAction
  签名: : 分配乘法作用 R (P1 ->ᵃ[k] V2) where
  定义体: ext fun _ => smul_add _ _ _
  smul_zero _ := ext fun _ => smul_zero _

Depends on / 依赖: smul_add
-/
instance distribMulAction : DistribMulAction R (P1 ->ᵃ[k] V2) where
  smul_add _ _ _ := ext fun _ => smul_add _ _ _
  smul_zero _ := ext fun _ => smul_zero _

end DistribMulAction

section Module

variable [Semiring R] [Module R V2] [SMulCommClass k R V2]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module R (P1 ->ᵃ[k] V2)
  body: { AffineMap.distribMulAction with
    add_smul := fun _ _ _ => ext fun _ => add_smul _ _ _
    zero_smul := fun _ => ext fun _ => zero_smul _ _ }

中文:
实例 :
  签名: 模 R (P1 ->ᵃ[k] V2)
  定义体: { AffineMap.distribMulAction with
    add_smul := fun _ _ _ => ext fun _ => add_smul _ _ _
    zero_smul := fun _ => ext fun _ => zero_smul _ _ }

Depends on / 依赖: AffineMap, AffineMap.distribMulAction, add_smul, distribMulAction, zero_smul
-/
instance : Module R (P1 ->ᵃ[k] V2) :=
  { AffineMap.distribMulAction with
    add_smul := fun _ _ _ => ext fun _ => add_smul _ _ _
    zero_smul := fun _ => ext fun _ => zero_smul _ _ }

variable (R)

/-- The space of affine maps between two modules is linearly equivalent to the product of the
domain with the space of linear maps, by taking the value of the affine map at `(0 : V1)` and the
linear part.

See note [bundled maps over different rings] -/
@[simps]
/--
Definition of `toConstProdLinearMap` / `toConstProdLinearMap` 的定义

English:
definition toConstProdLinearMap
  signature: : (V1 ->ᵃ[k] V2) ≃ₗ[R] V2 × (V1 ->ₗ[k] V2) where
  body: ⟨f 0, f.linear⟩
  invFun p := p.2.toAffineMap + const k V1 p.1
  left_inv f := by
    ext
    rw [f.decomp]
    simp
  right_inv := by
    rintro ⟨v, f⟩
    ext <;> simp [const_linear]
  map_add' := by simp
  map_smul' := by simp

中文:
定义 toConstProdLinearMap
  签名: : (V1 ->ᵃ[k] V2) ≃ₗ[R] V2 × (V1 ->ₗ[k] V2) where
  定义体: ⟨f 0, f.linear⟩
  invFun p := p.2.toAffineMap + const k V1 p.1
  left_inv f := by
    ext
    rw [f.decomp]
    simp
  right_inv := by
    rintro ⟨v, f⟩
    ext <;> simp [const_linear]
  map_add' := by simp
  map_smul' := by simp

Depends on / 依赖: f.linear, linear
-/
def toConstProdLinearMap : (V1 ->ᵃ[k] V2) ≃ₗ[R] V2 × (V1 ->ₗ[k] V2) where
  toFun f := ⟨f 0, f.linear⟩
  invFun p := p.2.toAffineMap + const k V1 p.1
  left_inv f := by
    ext
    rw [f.decomp]
    simp
  right_inv := by
    rintro ⟨v, f⟩
    ext <;> simp [const_linear]
  map_add' := by simp
  map_smul' := by simp

end Module

set_option backward.isDefEq.respectTransparency false in
/-- Interpolating between affine maps with `lineMap` commutes with evaluation. -/
@[simp]
/--
lemma `lineMap_apply'` / 引理 `lineMap_apply'`

English:
lemma lineMap_apply'
  statement: [SMulCommClass k k V2] (f g : P1 ->ᵃ[k] P2) (c : k)
  proof: by
  simp [AffineMap.lineMap_apply]

中文:
引理 lineMap_apply'
  结论: [标量交换类 k k V2] (f g : P1 ->ᵃ[k] P2) (c : k)
  证明: by
  simp [AffineMap.lineMap_apply]

Depends on / 依赖: AffineMap, AffineMap.lineMap_apply, lineMap_apply
-/
lemma lineMap_apply' [SMulCommClass k k V2] (f g : P1 ->ᵃ[k] P2) (c : k)
    (p : P1) : lineMap f g c p = lineMap (f p) (g p) c := by
  simp [AffineMap.lineMap_apply]

section Pi

variable {ι : Type*} {φv φp : ι -> Type*} [(i : ι) -> AddCommGroup (φv i)]
  [(i : ι) -> Module k (φv i)] [(i : ι) -> AffineSpace (φv i) (φp i)]
/-- `pi` construction for affine maps. From a family of affine maps it produces an affine
map into a family of affine spaces.

This is the affine version of `LinearMap.pi`.
-/
@[simps linear]
/--
Definition of `pi` / `pi` 的定义

English:
definition pi
  signature: (f : (i : ι) -> (P1 ->ᵃ[k] φp i))
  body: f a m
  linear := LinearMap.pi (fun a => (f a).linear)
  map_vadd' _ _ := funext fun _ => map_vadd _ _ _

中文:
定义 pi
  签名: (f : (i : ι) -> (P1 ->ᵃ[k] φp i))
  定义体: f a m
  linear := LinearMap.pi (fun a => (f a).linear)
  map_vadd' _ _ := funext fun _ => map_vadd _ _ _
-/
def pi (f : (i : ι) -> (P1 ->ᵃ[k] φp i)) : P1 ->ᵃ[k] ((i : ι) -> φp i) where
  toFun m a := f a m
  linear := LinearMap.pi (fun a => (f a).linear)
  map_vadd' _ _ := funext fun _ => map_vadd _ _ _

--fp for when the image is a dependent AffineSpace φp i, fv for when the
--image is a Module φv i, f' for when the image isn't dependent.
variable (fp : (i : ι) -> (P1 ->ᵃ[k] φp i)) (fv : (i : ι) -> (P1 ->ᵃ[k] φv i))
  (f' : ι -> P1 ->ᵃ[k] P2)

@[simp]
/--
theorem `pi_apply` / 定理 `pi_apply`

English:
theorem pi_apply
  given: (c : P1) (i : ι)
  statement: pi fp c i = fp i c
  proof: rfl

中文:
定理 pi_apply
  条件: (c : P1) (i : ι)
  结论: pi fp c i = fp i c
  证明: rfl
-/
theorem pi_apply (c : P1) (i : ι) : pi fp c i = fp i c :=
  rfl

/--
theorem `pi_comp` / 定理 `pi_comp`

English:
theorem pi_comp
  given: (g : P3 ->ᵃ[k] P1)
  statement: (pi fp).comp g = pi (fun i => (fp i).comp g)
  proof: rfl

中文:
定理 pi_comp
  条件: (g : P3 ->ᵃ[k] P1)
  结论: (pi fp).comp g = pi (fun i => (fp i).comp g)
  证明: rfl
-/
theorem pi_comp (g : P3 ->ᵃ[k] P1) : (pi fp).comp g = pi (fun i => (fp i).comp g) :=
  rfl

/--
theorem `pi_eq_zero` / 定理 `pi_eq_zero`

English:
theorem pi_eq_zero
  statement: pi fv = 0 ↔ forall i, fv i = 0
  proof: by
  simp only [AffineMap.ext_iff, funext_iff, pi_apply]
  exact forall_comm

中文:
定理 pi_eq_zero
  结论: pi fv = 0 ↔ 对任意 i, fv i = 0
  证明: by
  simp only [AffineMap.ext_iff, funext_iff, pi_apply]
  exact forall_comm

Depends on / 依赖: AffineMap, AffineMap.ext_iff, ext_iff, forall_comm, funext_iff, pi_apply
-/
theorem pi_eq_zero : pi fv = 0 ↔ forall i, fv i = 0 := by
  simp only [AffineMap.ext_iff, funext_iff, pi_apply]
  exact forall_comm

/--
theorem `pi_zero` / 定理 `pi_zero`

English:
theorem pi_zero
  statement: pi (fun _ => 0 : (i : ι) -> P1 ->ᵃ[k] φv i) = 0
  proof: by
  ext; rfl

中文:
定理 pi_zero
  结论: pi (fun _ => 0 : (i : ι) -> P1 ->ᵃ[k] φv i) = 0
  证明: by
  ext; rfl
-/
theorem pi_zero : pi (fun _ => 0 : (i : ι) -> P1 ->ᵃ[k] φv i) = 0 := by
  ext; rfl

/--
theorem `proj_pi` / 定理 `proj_pi`

English:
theorem proj_pi
  given: (i : ι)
  statement: (proj i).comp (pi fp) = fp i
  proof: ext fun _ => rfl

中文:
定理 proj_pi
  条件: (i : ι)
  结论: (proj i).comp (pi fp) = fp i
  证明: ext fun _ => rfl
-/
theorem proj_pi (i : ι) : (proj i).comp (pi fp) = fp i :=
  ext fun _ => rfl
section Ext

variable [Finite ι] [DecidableEq ι] {f g : ((i : ι) -> φv i) ->ᵃ[k] P2}

/--
theorem `pi_ext_zero` / 定理 `pi_ext_zero`

English:
theorem pi_ext_zero
  given: (h : forall i x, f (Pi.single i x) = g (Pi.single i x)) (h₂ : f 0 = g 0)
  proof: by
  apply ext_linear
  · apply LinearMap.pi_ext
    intro i x
    have s₁ := h i x
    have s₂ := f.map_vadd 0 (Pi.single i x)
    have s₃ := g.map_vadd 0 (Pi.single i x)
    rw [vadd_eq_add]; rw [add_zero] at s₂ s₃
    replace h₂ := h i 0
    simp only [Pi.single_zero] at h₂
    rwa [s₂, s₃, h₂, v

中文:
定理 pi_ext_zero
  条件: (h : 对任意 i x, f (依赖函数类型.single i x) = g (依赖函数类型.single i x)) (h₂ : f 0 = g 0)
  证明: by
  apply ext_linear
  · apply LinearMap.pi_ext
    intro i x
    have s₁ := h i x
    have s₂ := f.map_vadd 0 (Pi.single i x)
    have s₃ := g.map_vadd 0 (Pi.single i x)
    rw [vadd_eq_add]; rw [add_zero] at s₂ s₃
    replace h₂ := h i 0
    simp only [Pi.single_zero] at h₂
    rwa [s₂, s₃, h₂, v

Depends on / 依赖: LinearMap, LinearMap.pi_ext, Pi.single, Pi.single_zero, add_zero, ext_linear, f.map_vadd, g.map_vadd, map_vadd, pi_ext, replace, single, single_zero, vadd_eq_add, vadd_right_cancel_iff
-/
theorem pi_ext_zero (h : forall i x, f (Pi.single i x) = g (Pi.single i x)) (h₂ : f 0 = g 0) :
    f = g := by
  apply ext_linear
  · apply LinearMap.pi_ext
    intro i x
    have s₁ := h i x
    have s₂ := f.map_vadd 0 (Pi.single i x)
    have s₃ := g.map_vadd 0 (Pi.single i x)
    rw [vadd_eq_add]; rw [add_zero] at s₂ s₃
    replace h₂ := h i 0
    simp only [Pi.single_zero] at h₂
    rwa [s₂, s₃, h₂, vadd_right_cancel_iff] at s₁
  · exact h₂

/--
theorem `pi_ext_nonempty` / 定理 `pi_ext_nonempty`

English:
theorem pi_ext_nonempty
  given: [Nonempty ι] (h : forall i x, f (Pi.single i x) = g (Pi.single i x))
  proof: by
  apply pi_ext_zero h
  inhabit ι
  rw [← Pi.single_zero default]
  apply h

中文:
定理 pi_ext_nonempty
  条件: [非空 ι] (h : 对任意 i x, f (依赖函数类型.single i x) = g (依赖函数类型.single i x))
  证明: by
  apply pi_ext_zero h
  inhabit ι
  rw [← Pi.single_zero default]
  apply h

Depends on / 依赖: Pi.single_zero, inhabit, pi_ext_zero, single_zero
-/
theorem pi_ext_nonempty [Nonempty ι] (h : forall i x, f (Pi.single i x) = g (Pi.single i x)) :
    f = g := by
  apply pi_ext_zero h
  inhabit ι
  rw [← Pi.single_zero default]
  apply h

/-- This is used as the ext lemma instead of `AffineMap.pi_ext_nonempty` for reasons explained in
note [partially-applied ext lemmas]. Analogous to `LinearMap.pi_ext'` -/
@[ext (iff := false)]
/--
theorem `pi_ext_nonempty'` / 定理 `pi_ext_nonempty'`

English:
theorem pi_ext_nonempty'
  statement: [Nonempty ι] (h : forall i, f.comp (LinearMap.single _ _ i).toAffineMap =
  proof: by
  refine pi_ext_nonempty fun i x => ?_
  convert! AffineMap.congr_fun (h i) x

中文:
定理 pi_ext_nonempty'
  结论: [非空 ι] (h : 对任意 i, f.comp (线性映射.single _ _ i).toAffineMap =
  证明: by
  refine pi_ext_nonempty fun i x => ?_
  convert! AffineMap.congr_fun (h i) x

Depends on / 依赖: AffineMap, AffineMap.congr_fun, congr_fun, convert, pi_ext_nonempty
-/
theorem pi_ext_nonempty' [Nonempty ι] (h : forall i, f.comp (LinearMap.single _ _ i).toAffineMap =
    g.comp (LinearMap.single _ _ i).toAffineMap) : f = g := by
  refine pi_ext_nonempty fun i x => ?_
  convert! AffineMap.congr_fun (h i) x

end Ext

end Pi

end Ring

section CommRing

variable [CommRing k] [AddCommGroup V1] [AffineSpace V1 P1] [AddCommGroup V2]
variable [Module k V1] [Module k V2]

/--
Definition of `homothety` / `homothety` 的定义

English:
definition homothety
  signature: (c : P1) (r : k)
  body: r • (id k P1 -ᵥ const k P1 c) +ᵥ const k P1 c

中文:
定义 homothety
  签名: (c : P1) (r : k)
  定义体: r • (id k P1 -ᵥ const k P1 c) +ᵥ const k P1 c
-/
def homothety (c : P1) (r : k) : P1 ->ᵃ[k] P1 :=
  r • (id k P1 -ᵥ const k P1 c) +ᵥ const k P1 c

/--
theorem `homothety_def` / 定理 `homothety_def`

English:
theorem homothety_def
  given: (c : P1) (r : k)
  proof: rfl

中文:
定理 homothety_def
  条件: (c : P1) (r : k)
  证明: rfl
-/
theorem homothety_def (c : P1) (r : k) :
    homothety c r = r • (id k P1 -ᵥ const k P1 c) +ᵥ const k P1 c :=
  rfl

/--
theorem `coe_homothety` / 定理 `coe_homothety`

English:
theorem coe_homothety
  given: (c : P1) (r : k)
  statement: homothety c r = fun p => r • (p -ᵥ c) +ᵥ c
  proof: rfl

中文:
定理 coe_homothety
  条件: (c : P1) (r : k)
  结论: homothety c r = fun p => r • (p -ᵥ c) +ᵥ c
  证明: rfl
-/
theorem coe_homothety (c : P1) (r : k) : homothety c r = fun p => r • (p -ᵥ c) +ᵥ c :=
  rfl

/--
theorem `homothety_apply` / 定理 `homothety_apply`

English:
theorem homothety_apply
  given: (c : P1) (r : k) (p : P1)
  statement: homothety c r p = r • (p -ᵥ c : V1) +ᵥ c
  proof: rfl

@[simp]

中文:
定理 homothety_apply
  条件: (c : P1) (r : k) (p : P1)
  结论: homothety c r p = r • (p -ᵥ c : V1) +ᵥ c
  证明: rfl

@[simp]
-/
theorem homothety_apply (c : P1) (r : k) (p : P1) : homothety c r p = r • (p -ᵥ c : V1) +ᵥ c :=
  rfl

@[simp]
/--
theorem `homothety_linear` / 定理 `homothety_linear`

English:
theorem homothety_linear
  given: (c : P1) (r : k)
  statement: (homothety c r).linear = r • LinearMap.id
  proof: by
  simp [homothety]

中文:
定理 homothety_linear
  条件: (c : P1) (r : k)
  结论: (homothety c r).linear = r • 线性映射.id
  证明: by
  simp [homothety]

Depends on / 依赖: homothety
-/
theorem homothety_linear (c : P1) (r : k) : (homothety c r).linear = r • LinearMap.id := by
  simp [homothety]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `homothety_eq_lineMap` / 定理 `homothety_eq_lineMap`

English:
theorem homothety_eq_lineMap
  given: (c : P1) (r : k) (p : P1)
  statement: homothety c r p = lineMap c p r
  proof: rfl

@[simp]

中文:
定理 homothety_eq_lineMap
  条件: (c : P1) (r : k) (p : P1)
  结论: homothety c r p = lineMap c p r
  证明: rfl

@[simp]
-/
theorem homothety_eq_lineMap (c : P1) (r : k) (p : P1) : homothety c r p = lineMap c p r :=
  rfl

@[simp]
/--
theorem `homothety_one` / 定理 `homothety_one`

English:
theorem homothety_one
  given: (c : P1)
  statement: homothety c (1 : k) = id k P1
  proof: by
  ext p
  simp [homothety_apply]

@[simp]

中文:
定理 homothety_one
  条件: (c : P1)
  结论: homothety c (1 : k) = id k P1
  证明: by
  ext p
  simp [homothety_apply]

@[simp]

Depends on / 依赖: homothety_apply
-/
theorem homothety_one (c : P1) : homothety c (1 : k) = id k P1 := by
  ext p
  simp [homothety_apply]

@[simp]
/--
theorem `homothety_apply_same` / 定理 `homothety_apply_same`

English:
theorem homothety_apply_same
  given: (c : P1) (r : k)
  statement: homothety c r c = c
  proof: lineMap_same_apply c r

中文:
定理 homothety_apply_same
  条件: (c : P1) (r : k)
  结论: homothety c r c = c
  证明: lineMap_same_apply c r

Depends on / 依赖: lineMap_same_apply
-/
theorem homothety_apply_same (c : P1) (r : k) : homothety c r c = c :=
  lineMap_same_apply c r

/--
theorem `homothety_mul_apply` / 定理 `homothety_mul_apply`

English:
theorem homothety_mul_apply
  given: (c : P1) (r₁ r₂ : k) (p : P1)
  proof: by
  simp only [homothety_apply, mul_smul, vadd_vsub]

中文:
定理 homothety_mul_apply
  条件: (c : P1) (r₁ r₂ : k) (p : P1)
  证明: by
  simp only [homothety_apply, mul_smul, vadd_vsub]

Depends on / 依赖: homothety_apply, mul_smul, vadd_vsub
-/
theorem homothety_mul_apply (c : P1) (r₁ r₂ : k) (p : P1) :
    homothety c (r₁ * r₂) p = homothety c r₁ (homothety c r₂ p) := by
  simp only [homothety_apply, mul_smul, vadd_vsub]

/--
theorem `homothety_mul` / 定理 `homothety_mul`

English:
theorem homothety_mul
  given: (c : P1) (r₁ r₂ : k)
  proof: ext homothety_mul_apply c r₁ r₂

@[simp]

中文:
定理 homothety_mul
  条件: (c : P1) (r₁ r₂ : k)
  证明: ext homothety_mul_apply c r₁ r₂

@[simp]

Depends on / 依赖: homothety_mul_apply
-/
theorem homothety_mul (c : P1) (r₁ r₂ : k) :
    homothety c (r₁ * r₂) = (homothety c r₁).comp (homothety c r₂) :=
ext homothety_mul_apply c r₁ r₂

@[simp]
/--
theorem `homothety_zero` / 定理 `homothety_zero`

English:
theorem homothety_zero
  given: (c : P1)
  statement: homothety c (0 : k) = const k P1 c
  proof: by
  ext p
  simp [homothety_apply]

@[simp]

中文:
定理 homothety_zero
  条件: (c : P1)
  结论: homothety c (0 : k) = const k P1 c
  证明: by
  ext p
  simp [homothety_apply]

@[simp]

Depends on / 依赖: homothety_apply
-/
theorem homothety_zero (c : P1) : homothety c (0 : k) = const k P1 c := by
  ext p
  simp [homothety_apply]

@[simp]
/--
theorem `homothety_add` / 定理 `homothety_add`

English:
theorem homothety_add
  given: (c : P1) (r₁ r₂ : k)
  proof: by
  simp only [homothety_def, add_smul, vadd_vadd]

中文:
定理 homothety_add
  条件: (c : P1) (r₁ r₂ : k)
  证明: by
  simp only [homothety_def, add_smul, vadd_vadd]

Depends on / 依赖: add_smul, homothety_def, vadd_vadd
-/
theorem homothety_add (c : P1) (r₁ r₂ : k) :
    homothety c (r₁ + r₂) = r₁ • (id k P1 -ᵥ const k P1 c) +ᵥ homothety c r₂ := by
  simp only [homothety_def, add_smul, vadd_vadd]

/--
theorem `homothety_eq_iff_of_mul_eq_one` / 定理 `homothety_eq_iff_of_mul_eq_one`

English:
theorem homothety_eq_iff_of_mul_eq_one
  given: {c p q : P1} {r₁ r₂ : k} (h : r₁ * r₂ = 1)
  proof: by
  obtain h' : r₂ * r₁ = 1 := mul_eq_one_comm.mp h
  refine ⟨fun h1 => ?_, fun h1 => ?_⟩
  all_goals
    rw [← h1]; rw [← homothety_mul_apply]
    simp [h, h']

中文:
定理 homothety_eq_iff_of_mul_eq_one
  条件: {c p q : P1} {r₁ r₂ : k} (h : r₁ * r₂ = 1)
  证明: by
  obtain h' : r₂ * r₁ = 1 := mul_eq_one_comm.mp h
  refine ⟨fun h1 => ?_, fun h1 => ?_⟩
  all_goals
    rw [← h1]; rw [← homothety_mul_apply]
    simp [h, h']

Depends on / 依赖: all_goals, homothety_mul_apply, mul_eq_one_comm, mul_eq_one_comm.mp
-/
theorem homothety_eq_iff_of_mul_eq_one {c p q : P1} {r₁ r₂ : k} (h : r₁ * r₂ = 1) :
    homothety c r₁ p = q ↔ homothety c r₂ q = p := by
  obtain h' : r₂ * r₁ = 1 := mul_eq_one_comm.mp h
  refine ⟨fun h1 => ?_, fun h1 => ?_⟩
  all_goals
    rw [← h1]; rw [← homothety_mul_apply]
    simp [h, h']

/--
theorem `homothety_injective` / 定理 `homothety_injective`

English:
theorem homothety_injective
  statement: [Module.IsTorsionFree k V1] [IsCancelMulZero k] (c : P1) {r : k}
  proof: fun _ _ h => by simpa [homothety_def, hr] using h

@[simp]

中文:
定理 homothety_injective
  结论: [模.是无挠 k V1] [是乘零消去 k] (c : P1) {r : k}
  证明: fun _ _ h => by simpa [homothety_def, hr] using h

@[simp]

Depends on / 依赖: homothety_def
-/
theorem homothety_injective [Module.IsTorsionFree k V1] [IsCancelMulZero k] (c : P1) {r : k}
    (hr : r != 0) :
    Function.Injective (homothety c r) :=
  fun _ _ h => by simpa [homothety_def, hr] using h

@[simp]
/--
theorem `homothety_inj` / 定理 `homothety_inj`

English:
theorem homothety_inj
  statement: [Module.IsTorsionFree k V1] [IsCancelMulZero k] (c : P1) {r : k} (hr : r != 0)
  proof: (homothety_injective c hr).eq_iff

中文:
定理 homothety_inj
  结论: [模.是无挠 k V1] [是乘零消去 k] (c : P1) {r : k} (hr : r != 0)
  证明: (homothety_injective c hr).eq_iff

Depends on / 依赖: eq_iff, homothety_injective
-/
theorem homothety_inj [Module.IsTorsionFree k V1] [IsCancelMulZero k] (c : P1) {r : k} (hr : r != 0)
    {p q : P1} :
    homothety c r p = homothety c r q ↔ p = q :=
  (homothety_injective c hr).eq_iff

/--
Definition of `homothetyHom` / `homothetyHom` 的定义

English:
definition homothetyHom
  signature: (c : P1)
  body: homothety c
  map_one' := homothety_one c
  map_mul' := homothety_mul c

@[simp]

中文:
定义 homothetyHom
  签名: (c : P1)
  定义体: homothety c
  map_one' := homothety_one c
  map_mul' := homothety_mul c

@[simp]

Depends on / 依赖: homothety
-/
def homothetyHom (c : P1) : k ->* P1 ->ᵃ[k] P1 where
  toFun := homothety c
  map_one' := homothety_one c
  map_mul' := homothety_mul c

@[simp]
/--
theorem `coe_homothetyHom` / 定理 `coe_homothetyHom`

English:
theorem coe_homothetyHom
  given: (c : P1)
  statement: ⇑(homothetyHom c : k ->* _) = homothety c
  proof: rfl

中文:
定理 coe_homothetyHom
  条件: (c : P1)
  结论: ⇑(homothetyHom c : k ->* _) = homothety c
  证明: rfl
-/
theorem coe_homothetyHom (c : P1) : ⇑(homothetyHom c : k ->* _) = homothety c :=
  rfl

/--
Definition of `homothetyAffine` / `homothetyAffine` 的定义

English:
definition homothetyAffine
  signature: (c : P1)
  body: ⟨homothety c, (LinearMap.lsmul k _).flip (id k P1 -ᵥ const k P1 c),
    Function.swap (homothety_add c)⟩

@[simp]

中文:
定义 homothetyAffine
  签名: (c : P1)
  定义体: ⟨homothety c, (LinearMap.lsmul k _).flip (id k P1 -ᵥ const k P1 c),
    Function.swap (homothety_add c)⟩

@[simp]

Depends on / 依赖: Function, Function.swap, LinearMap, LinearMap.lsmul, homothety, homothety_add
-/
def homothetyAffine (c : P1) : k ->ᵃ[k] P1 ->ᵃ[k] P1 :=
  ⟨homothety c, (LinearMap.lsmul k _).flip (id k P1 -ᵥ const k P1 c),
    Function.swap (homothety_add c)⟩

@[simp]
/--
theorem `coe_homothetyAffine` / 定理 `coe_homothetyAffine`

English:
theorem coe_homothetyAffine
  given: (c : P1)
  statement: ⇑(homothetyAffine c : k ->ᵃ[k] _) = homothety c
  proof: rfl

中文:
定理 coe_homothetyAffine
  条件: (c : P1)
  结论: ⇑(homothetyAffine c : k ->ᵃ[k] _) = homothety c
  证明: rfl
-/
theorem coe_homothetyAffine (c : P1) : ⇑(homothetyAffine c : k ->ᵃ[k] _) = homothety c :=
  rfl

end CommRing

end AffineMap

section

variable {𝕜 E F : Type*} [Ring 𝕜] [AddCommGroup E] [AddCommGroup F] [Module 𝕜 E] [Module 𝕜 F]

/--
theorem `Convex.combo_affine_apply` / 定理 `Convex.combo_affine_apply`

English:
theorem Convex.combo_affine_apply
  given: {x y : E} {a b : 𝕜} {f : E ->ᵃ[𝕜] F} (h : a + b = 1)
  proof: by
  simp only [Convex.combo_eq_smul_sub_add h, ← vsub_eq_sub]
  exact f.apply_lineMap _ _ _

中文:
定理 凸.combo_affine_apply
  条件: {x y : E} {a b : 𝕜} {f : E ->ᵃ[𝕜] F} (h : a + b = 1)
  证明: by
  simp only [Convex.combo_eq_smul_sub_add h, ← vsub_eq_sub]
  exact f.apply_lineMap _ _ _

Depends on / 依赖: Convex, Convex.combo_eq_smul_sub_add, apply_lineMap, combo_eq_smul_sub_add, f.apply_lineMap, vsub_eq_sub
-/
theorem Convex.combo_affine_apply {x y : E} {a b : 𝕜} {f : E ->ᵃ[𝕜] F} (h : a + b = 1) :
    f (a • x + b • y) = a • f x + b • f y := by
  simp only [Convex.combo_eq_smul_sub_add h, ← vsub_eq_sub]
  exact f.apply_lineMap _ _ _

end
