/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Algebra.Group.Basic

/-!
# Topological monoids - definitions

In this file we define three mixin typeclasses:

- `ContinuousMul M` says that the multiplication on `M` is continuous as a function on `M × M`;
- `ContinuousAdd M` says that the addition on `M` is continuous as a function on `M × M`.
- `SeparatelyContinuousMul M` says that the multiplication on `M` is continuous in each argument
  separately. This is strictly weaker than `ContinuousMul M`, but arises frequently in practice in
  functional analysis where one often considers topologies weaker than the norm topology. In these
  topologies it is frequently the case that the multiplication is not jointly continuous, but is
  continuous in each argument separately.

These classes are `Prop`-valued mixins,
i.e., they take data (`TopologicalSpace`, `Mul`/`Add`) as arguments
instead of extending typeclasses with these fields.

We also provide convenience dot notation lemmas like `Filter.Tendsto.mul` and `ContinuousAt.add`.
-/

public section

open scoped Topology

/--
Definition of `ContinuousAdd` / `ContinuousAdd` 的定义

English:
class ContinuousAdd
  parameters: (M : Type*) [TopologicalSpace M] [Add M]
  axioms and operations (1):
    - continuous_add : Continuous fun p : M × M => p.1 + p.2

中文:
类 连续加法
  参数: (M : 类型) [拓扑空间 M] [加法 M]
  公理与运算 (1 个):
    - continuous_add : 连续 fun p : M × M => p.1 + p.2
-/
class ContinuousAdd (M : Type*) [TopologicalSpace M] [Add M] : Prop where
  continuous_add : Continuous fun p : M × M => p.1 + p.2

/-- Basic hypothesis to talk about a topological monoid or a topological semigroup.
A topological monoid over `M`, for example, is obtained by requiring both the instances `Monoid M`
and `ContinuousMul M`.

Continuity in each argument separately can be stated using `SeparatelyContinuousMul α`. If one wants
only continuity in either the left or right argument, but not both one can use
`ContinuousConstSMul α α`/`ContinuousConstSMul αᵐᵒᵖ α`. -/
@[to_additive]
/--
Definition of `ContinuousMul` / `ContinuousMul` 的定义

English:
class ContinuousMul
  parameters: (M : Type*) [TopologicalSpace M] [Mul M]
  axioms and operations (1):
    - continuous_mul : Continuous fun p : M × M => p.1 * p.2

中文:
类 连续乘法
  参数: (M : 类型) [拓扑空间 M] [乘法 M]
  公理与运算 (1 个):
    - continuous_mul : 连续 fun p : M × M => p.1 * p.2
-/
class ContinuousMul (M : Type*) [TopologicalSpace M] [Mul M] : Prop where
  continuous_mul : Continuous fun p : M × M => p.1 * p.2

/--
Definition of `SeparatelyContinuousAdd` / `SeparatelyContinuousAdd` 的定义

English:
class SeparatelyContinuousAdd
  parameters: (M : Type*) [TopologicalSpace M] [Add M]
  axioms and operations (2):
    - continuous_const_add({a : M}) : Continuous (a + ·)
    - continuous_add_const({a : M}) : Continuous (· + a)

中文:
类 SeparatelyContinuousAdd
  参数: (M : 类型) [拓扑空间 M] [加法 M]
  公理与运算 (2 个):
    - continuous_const_add({a : M}) : 连续 (a + ·)
    - continuous_add_const({a : M}) : 连续 (· + a)
-/
class SeparatelyContinuousAdd (M : Type*) [TopologicalSpace M] [Add M] : Prop where
  continuous_const_add {a : M} : Continuous (a + ·)
  continuous_add_const {a : M} : Continuous (· + a)

/-- A type class encoding that addition is continuous in each argument. This is weaker than
`ContinuousMul`. -/
@[to_additive]
/--
Definition of `SeparatelyContinuousMul` / `SeparatelyContinuousMul` 的定义

English:
class SeparatelyContinuousMul
  parameters: (M : Type*) [TopologicalSpace M] [Mul M]
  axioms and operations (2):
    - continuous_const_mul({a : M}) : Continuous (a * ·)
    - continuous_mul_const({a : M}) : Continuous (· * a)

中文:
类 SeparatelyContinuousMul
  参数: (M : 类型) [拓扑空间 M] [乘法 M]
  公理与运算 (2 个):
    - continuous_const_mul({a : M}) : 连续 (a * ·)
    - continuous_mul_const({a : M}) : 连续 (· * a)
-/
class SeparatelyContinuousMul (M : Type*) [TopologicalSpace M] [Mul M] : Prop where
  continuous_const_mul {a : M} : Continuous (a * ·)
  continuous_mul_const {a : M} : Continuous (· * a)

section ContinuousMul

variable {M : Type*} [TopologicalSpace M] [Mul M] [ContinuousMul M]

@[to_additive (attr := continuity, fun_prop)]
/--
theorem `continuous_mul` / 定理 `continuous_mul`

English:
theorem continuous_mul
  statement: Continuous fun p : M × M => p.1 * p.2
  proof: ContinuousMul.continuous_mul

@[to_additive]

中文:
定理 continuous_mul
  结论: 连续 fun p : M × M => p.1 * p.2
  证明: ContinuousMul.continuous_mul

@[to_additive]

Depends on / 依赖: ContinuousMul, ContinuousMul.continuous_mul, continuous_mul
-/
theorem continuous_mul : Continuous fun p : M × M => p.1 * p.2 :=
  ContinuousMul.continuous_mul

@[to_additive]
/--
theorem `Filter.Tendsto.mul` / 定理 `Filter.Tendsto.mul`

English:
theorem Filter.Tendsto.mul
  statement: {α : Type*} {f g : α -> M} {x : Filter α} {a b : M}
  proof: (continuous_mul.tendsto _).comp (hf.prodMk_nhds hg)

@[to_additive]

中文:
定理 滤子.收敛.mul
  结论: {α : 类型} {f g : α -> M} {x : 滤子 α} {a b : M}
  证明: (continuous_mul.tendsto _).comp (hf.prodMk_nhds hg)

@[to_additive]

Depends on / 依赖: continuous_mul, continuous_mul.tendsto, hf.prodMk_nhds, prodMk_nhds, tendsto
-/
theorem Filter.Tendsto.mul {α : Type*} {f g : α -> M} {x : Filter α} {a b : M}
    (hf : Tendsto f x (𝓝 a)) (hg : Tendsto g x (𝓝 b)) : Tendsto (fun x => f x * g x) x (𝓝 (a * b)) :=
  (continuous_mul.tendsto _).comp (hf.prodMk_nhds hg)

@[to_additive]
/--
lemma `Filter.tendsto_of_div_tendsto_one` / 引理 `Filter.tendsto_of_div_tendsto_one`

English:
lemma Filter.tendsto_of_div_tendsto_one
  statement: {α E : Type*} [CommGroup E] [TopologicalSpace E]
  proof: by
  simpa using Tendsto.mul hf hfg

中文:
引理 滤子.tendsto_of_div_tendsto_one
  结论: {α E : 类型} [交换群 E] [拓扑空间 E]
  证明: by
  simpa using Tendsto.mul hf hfg

Depends on / 依赖: Tendsto, Tendsto.mul
-/
lemma Filter.tendsto_of_div_tendsto_one {α E : Type*} [CommGroup E] [TopologicalSpace E]
    [ContinuousMul E] {f g : α -> E} (m : E) {x : Filter α} (hf : Tendsto f x (𝓝 m))
    (hfg : Tendsto (g / f) x (𝓝 1)) : Tendsto g x (𝓝 m) := by
  simpa using Tendsto.mul hf hfg

variable {X : Type*} [TopologicalSpace X] {f g : X -> M} {s : Set X} {x : X}

@[to_fun (attr := to_additive (attr := continuity, fun_prop))]
/--
theorem `Continuous.mul` / 定理 `Continuous.mul`

English:
theorem Continuous.mul
  given: (hf : Continuous f) (hg : Continuous g)
  proof: continuous_mul.comp₂ hf hg

@[to_fun (attr := to_additive (attr := fun_prop))]

中文:
定理 连续.mul
  条件: (hf : 连续 f) (hg : 连续 g)
  证明: continuous_mul.comp₂ hf hg

@[to_fun (attr := to_additive (attr := fun_prop))]

Depends on / 依赖: continuous_mul, continuous_mul.comp
-/
theorem Continuous.mul (hf : Continuous f) (hg : Continuous g) :
    Continuous (f * g) :=
  continuous_mul.comp₂ hf hg

@[to_fun (attr := to_additive (attr := fun_prop))]
/--
theorem `ContinuousWithinAt.mul` / 定理 `ContinuousWithinAt.mul`

English:
theorem ContinuousWithinAt.mul
  given: (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x)
  proof: Filter.Tendsto.mul hf hg

@[to_fun (attr := to_additive (attr := fun_prop))]

中文:
定理 ContinuousWithinAt.mul
  条件: (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x)
  证明: Filter.Tendsto.mul hf hg

@[to_fun (attr := to_additive (attr := fun_prop))]

Depends on / 依赖: Filter, Filter.Tendsto.mul, Tendsto
-/
theorem ContinuousWithinAt.mul (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x) :
    ContinuousWithinAt (f * g) s x :=
  Filter.Tendsto.mul hf hg

@[to_fun (attr := to_additive (attr := fun_prop))]
/--
theorem `ContinuousAt.mul` / 定理 `ContinuousAt.mul`

English:
theorem ContinuousAt.mul
  given: (hf : ContinuousAt f x) (hg : ContinuousAt g x)
  proof: Filter.Tendsto.mul hf hg

@[to_fun (attr := to_additive (attr := fun_prop))]

中文:
定理 ContinuousAt.mul
  条件: (hf : ContinuousAt f x) (hg : ContinuousAt g x)
  证明: Filter.Tendsto.mul hf hg

@[to_fun (attr := to_additive (attr := fun_prop))]

Depends on / 依赖: Filter, Filter.Tendsto.mul, Tendsto
-/
theorem ContinuousAt.mul (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    ContinuousAt (f * g) x :=
  Filter.Tendsto.mul hf hg

@[to_fun (attr := to_additive (attr := fun_prop))]
/--
theorem `ContinuousOn.mul` / 定理 `ContinuousOn.mul`

English:
theorem ContinuousOn.mul
  given: (hf : ContinuousOn f s) (hg : ContinuousOn g s)
  proof: fun x hx =>
  (hf x hx).mul (hg x hx)

中文:
定理 ContinuousOn.mul
  条件: (hf : ContinuousOn f s) (hg : ContinuousOn g s)
  证明: fun x hx =>
  (hf x hx).mul (hg x hx)
-/
theorem ContinuousOn.mul (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (f * g) s := fun x hx =>
  (hf x hx).mul (hg x hx)

end ContinuousMul

section

variable {M : Type*} [TopologicalSpace M] [Mul M]

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [ContinuousMul
  signature: M] : SeparatelyContinuousMul M where
  body: continuous_const.mul continuous_id
  continuous_mul_const := continuous_id.mul continuous_const

中文:
实例 [连续乘法
  签名: M] : SeparatelyContinuousMul M where
  定义体: continuous_const.mul continuous_id
  continuous_mul_const := continuous_id.mul continuous_const
-/
instance [ContinuousMul M] : SeparatelyContinuousMul M where
  continuous_const_mul := continuous_const.mul continuous_id
  continuous_mul_const := continuous_id.mul continuous_const

variable [SeparatelyContinuousMul M]

@[to_additive (attr := continuity, fun_prop)]
/--
theorem `continuous_const_mul` / 定理 `continuous_const_mul`

English:
theorem continuous_const_mul
  given: (m : M)
  statement: Continuous (m * ·)
  proof: SeparatelyContinuousMul.continuous_const_mul

@[to_additive (attr := continuity, fun_prop)]

中文:
定理 continuous_const_mul
  条件: (m : M)
  结论: 连续 (m * ·)
  证明: SeparatelyContinuousMul.continuous_const_mul

@[to_additive (attr := continuity, fun_prop)]

Depends on / 依赖: SeparatelyContinuousMul, SeparatelyContinuousMul.continuous_const_mul, continuous_const_mul
-/
theorem continuous_const_mul (m : M) : Continuous (m * ·) :=
  SeparatelyContinuousMul.continuous_const_mul

@[to_additive (attr := continuity, fun_prop)]
/--
theorem `continuous_mul_const` / 定理 `continuous_mul_const`

English:
theorem continuous_mul_const
  given: (m : M)
  statement: Continuous (· * m)
  proof: SeparatelyContinuousMul.continuous_mul_const

@[to_additive]

中文:
定理 continuous_mul_const
  条件: (m : M)
  结论: 连续 (· * m)
  证明: SeparatelyContinuousMul.continuous_mul_const

@[to_additive]

Depends on / 依赖: SeparatelyContinuousMul, SeparatelyContinuousMul.continuous_mul_const, continuous_mul_const
-/
theorem continuous_mul_const (m : M) : Continuous (· * m) :=
  SeparatelyContinuousMul.continuous_mul_const

@[to_additive]
/--
theorem `Filter.Tendsto.const_mul` / 定理 `Filter.Tendsto.const_mul`

English:
theorem Filter.Tendsto.const_mul
  statement: {α : Type*} {f : α -> M} {x : Filter α} {a : M}
  proof: .comp hf .tendsto _ continuous_const_mul b

@[to_additive]

中文:
定理 滤子.收敛.const_mul
  结论: {α : 类型} {f : α -> M} {x : 滤子 α} {a : M}
  证明: .comp hf .tendsto _ continuous_const_mul b

@[to_additive]

Depends on / 依赖: continuous_const_mul, tendsto
-/
theorem Filter.Tendsto.const_mul {α : Type*} {f : α -> M} {x : Filter α} {a : M}
    (b : M) (hf : Tendsto f x (𝓝 a)) : Tendsto (b * f ·) x (𝓝 (b * a)) :=
.comp hf .tendsto _ continuous_const_mul b

@[to_additive]
/--
theorem `Filter.Tendsto.mul_const` / 定理 `Filter.Tendsto.mul_const`

English:
theorem Filter.Tendsto.mul_const
  statement: {α : Type*} {f : α -> M} {x : Filter α} {a : M}
  proof: .comp hf .tendsto _ continuous_mul_const b

中文:
定理 滤子.收敛.mul_const
  结论: {α : 类型} {f : α -> M} {x : 滤子 α} {a : M}
  证明: .comp hf .tendsto _ continuous_mul_const b

Depends on / 依赖: continuous_mul_const, tendsto
-/
theorem Filter.Tendsto.mul_const {α : Type*} {f : α -> M} {x : Filter α} {a : M}
    (b : M) (hf : Tendsto f x (𝓝 a)) : Tendsto (f · * b) x (𝓝 (a * b)) :=
.comp hf .tendsto _ continuous_mul_const b

variable {X : Type*} [TopologicalSpace X] {f g : X -> M} {s : Set X} {x : X}

@[to_additive (attr := continuity, fun_prop)]
/--
theorem `Continuous.mul_const` / 定理 `Continuous.mul_const`

English:
theorem Continuous.mul_const
  given: (hf : Continuous f) (b : M)
  statement: Continuous (f · * b)
  proof: .comp hf continuous_mul_const b

@[to_additive (attr := continuity, fun_prop)]

中文:
定理 连续.mul_const
  条件: (hf : 连续 f) (b : M)
  结论: 连续 (f · * b)
  证明: .comp hf continuous_mul_const b

@[to_additive (attr := continuity, fun_prop)]

Depends on / 依赖: continuous_mul_const
-/
theorem Continuous.mul_const (hf : Continuous f) (b : M) : Continuous (f · * b) :=
.comp hf continuous_mul_const b

@[to_additive (attr := continuity, fun_prop)]
/--
theorem `Continuous.const_mul` / 定理 `Continuous.const_mul`

English:
theorem Continuous.const_mul
  given: (hf : Continuous f) (b : M)
  statement: Continuous (b * f ·)
  proof: .comp hf continuous_const_mul b

@[to_additive (attr := fun_prop)]

中文:
定理 连续.const_mul
  条件: (hf : 连续 f) (b : M)
  结论: 连续 (b * f ·)
  证明: .comp hf continuous_const_mul b

@[to_additive (attr := fun_prop)]

Depends on / 依赖: continuous_const_mul
-/
theorem Continuous.const_mul (hf : Continuous f) (b : M) : Continuous (b * f ·) :=
.comp hf continuous_const_mul b

@[to_additive (attr := fun_prop)]
/--
theorem `ContinuousWithinAt.mul_const` / 定理 `ContinuousWithinAt.mul_const`

English:
theorem ContinuousWithinAt.mul_const
  given: (hf : ContinuousWithinAt f s x) (b : M)
  proof: Filter.Tendsto.mul_const b hf

@[to_additive (attr := fun_prop)]

中文:
定理 ContinuousWithinAt.mul_const
  条件: (hf : ContinuousWithinAt f s x) (b : M)
  证明: Filter.Tendsto.mul_const b hf

@[to_additive (attr := fun_prop)]

Depends on / 依赖: Filter, Filter.Tendsto.mul_const, Tendsto, mul_const
-/
theorem ContinuousWithinAt.mul_const (hf : ContinuousWithinAt f s x) (b : M) :
    ContinuousWithinAt (f · * b) s x :=
  Filter.Tendsto.mul_const b hf

@[to_additive (attr := fun_prop)]
/--
theorem `ContinuousWithinAt.const_mul` / 定理 `ContinuousWithinAt.const_mul`

English:
theorem ContinuousWithinAt.const_mul
  given: (hf : ContinuousWithinAt f s x) (b : M)
  proof: Filter.Tendsto.const_mul b hf

@[to_additive (attr := fun_prop)]

中文:
定理 ContinuousWithinAt.const_mul
  条件: (hf : ContinuousWithinAt f s x) (b : M)
  证明: Filter.Tendsto.const_mul b hf

@[to_additive (attr := fun_prop)]

Depends on / 依赖: Filter, Filter.Tendsto.const_mul, Tendsto, const_mul
-/
theorem ContinuousWithinAt.const_mul (hf : ContinuousWithinAt f s x) (b : M) :
    ContinuousWithinAt (b * f ·) s x :=
  Filter.Tendsto.const_mul b hf

@[to_additive (attr := fun_prop)]
/--
theorem `ContinuousAt.mul_const` / 定理 `ContinuousAt.mul_const`

English:
theorem ContinuousAt.mul_const
  given: (hf : ContinuousAt f x) (b : M)
  proof: Filter.Tendsto.mul_const b hf

@[to_additive (attr := fun_prop)]

中文:
定理 ContinuousAt.mul_const
  条件: (hf : ContinuousAt f x) (b : M)
  证明: Filter.Tendsto.mul_const b hf

@[to_additive (attr := fun_prop)]

Depends on / 依赖: Filter, Filter.Tendsto.mul_const, Tendsto, mul_const
-/
theorem ContinuousAt.mul_const (hf : ContinuousAt f x) (b : M) :
    ContinuousAt (f · * b) x :=
  Filter.Tendsto.mul_const b hf

@[to_additive (attr := fun_prop)]
/--
theorem `ContinuousAt.const_mul` / 定理 `ContinuousAt.const_mul`

English:
theorem ContinuousAt.const_mul
  given: (hf : ContinuousAt f x) (b : M)
  proof: Filter.Tendsto.const_mul b hf

@[to_additive (attr := fun_prop)]

中文:
定理 ContinuousAt.const_mul
  条件: (hf : ContinuousAt f x) (b : M)
  证明: Filter.Tendsto.const_mul b hf

@[to_additive (attr := fun_prop)]

Depends on / 依赖: Filter, Filter.Tendsto.const_mul, Tendsto, const_mul
-/
theorem ContinuousAt.const_mul (hf : ContinuousAt f x) (b : M) :
    ContinuousAt (b * f ·) x :=
  Filter.Tendsto.const_mul b hf

@[to_additive (attr := fun_prop)]
/--
theorem `ContinuousOn.mul_const` / 定理 `ContinuousOn.mul_const`

English:
theorem ContinuousOn.mul_const
  given: (hf : ContinuousOn f s) (b : M)
  proof: fun x hx => (hf x hx).mul_const b

@[to_additive (attr := fun_prop)]

中文:
定理 ContinuousOn.mul_const
  条件: (hf : ContinuousOn f s) (b : M)
  证明: fun x hx => (hf x hx).mul_const b

@[to_additive (attr := fun_prop)]

Depends on / 依赖: mul_const
-/
theorem ContinuousOn.mul_const (hf : ContinuousOn f s) (b : M) :
    ContinuousOn (f · * b) s :=
  fun x hx => (hf x hx).mul_const b

@[to_additive (attr := fun_prop)]
/--
theorem `ContinuousOn.const_mul` / 定理 `ContinuousOn.const_mul`

English:
theorem ContinuousOn.const_mul
  given: (hf : ContinuousOn f s) (b : M)
  proof: fun x hx => (hf x hx).const_mul b

中文:
定理 ContinuousOn.const_mul
  条件: (hf : ContinuousOn f s) (b : M)
  证明: fun x hx => (hf x hx).const_mul b

Depends on / 依赖: const_mul
-/
theorem ContinuousOn.const_mul (hf : ContinuousOn f s) (b : M) :
    ContinuousOn (b * f ·) s :=
  fun x hx => (hf x hx).const_mul b
