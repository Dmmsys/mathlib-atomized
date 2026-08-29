/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
module

public import Mathlib.Topology.Algebra.Monoid.Defs

/-!
# Definitions about topological groups

In this file we define mixin classes `ContinuousInv`, `IsTopologicalGroup`, and `ContinuousDiv`,
as well as their additive versions.

These classes say that the corresponding operations are continuous:

- `ContinuousInv G` says that `(·⁻¹)` is continuous on `G`;
- `IsTopologicalGroup G` says that `(· * ·)` is continuous on `G × G`
  and `(·⁻¹)` is continuous on `G`;
- `ContinuousDiv G` says that `(· / ·)` is continuous on `G`.

For groups, `ContinuousDiv G` is equivalent to `IsTopologicalGroup G`,
but we use the additive version `ContinuousSub` for types like `NNReal`,
where subtraction is not given by `a - b = a + (-b)`.

We also provide convenience dot notation lemmas like `ContinuousAt.neg`.
-/

public section

open scoped Topology

universe u

variable {G α X : Type*} [TopologicalSpace X]

/--
Definition of `ContinuousNeg` / `ContinuousNeg` 的定义

English:
class ContinuousNeg
  parameters: (G : Type u) [TopologicalSpace G] [Neg G]
  axioms and operations (1):
    - continuous_neg : Continuous fun a : G => -a

中文:
类 ContinuousNeg
  参数: (G : 类型u) [TopologicalSpace G] [Neg G]
  公理与运算 (1 个):
    - continuous_neg : Continuous fun a : G => -a
-/
class ContinuousNeg (G : Type u) [TopologicalSpace G] [Neg G] : Prop where
  continuous_neg : Continuous fun a : G => -a

attribute [continuity, fun_prop] ContinuousNeg.continuous_neg

/-- Basic hypothesis to talk about a topological group. A topological group over `M`, for example,
is obtained by requiring the instances `Group M` and `ContinuousMul M` and
`ContinuousInv M`. -/
@[to_additive (attr := continuity)]
/--
Definition of `ContinuousInv` / `ContinuousInv` 的定义

English:
class ContinuousInv
  parameters: (G : Type u) [TopologicalSpace G] [Inv G]
  axioms and operations (1):
    - continuous_inv : Continuous fun a : G => a⁻¹

中文:
类 ContinuousInv
  参数: (G : 类型u) [TopologicalSpace G] [Inv G]
  公理与运算 (1 个):
    - continuous_inv : Continuous fun a : G => a⁻¹
-/
class ContinuousInv (G : Type u) [TopologicalSpace G] [Inv G] : Prop where
  continuous_inv : Continuous fun a : G => a⁻¹

attribute [continuity, fun_prop] ContinuousInv.continuous_inv

export ContinuousInv (continuous_inv)
export ContinuousNeg (continuous_neg)

section ContinuousInv

variable [TopologicalSpace G] [Inv G] [ContinuousInv G]

/-- If a function converges to a value in a multiplicative topological group, then its inverse
converges to the inverse of this value.
For the version in topological groups with zero (including topological fields)
assuming additionally that the limit is nonzero, use `Filter.Tendsto.inv₀`. -/
@[to_additive
  /-- If a function converges to a value in an additive topological group, then its
  negation converges to the negation of this value. -/]
/--
theorem `Filter.Tendsto.inv` / 定理 `Filter.Tendsto.inv`

English:
theorem Filter.Tendsto.inv
  given: {f : α -> G} {l : Filter α} {y : G} (h : Tendsto f l (𝓝 y))
  proof: (continuous_inv.tendsto y).comp h

中文:
定理 Filter.Tendsto.inv
  条件: {f : α -> G} {l : Filter α} {y : G} (h : Tendsto f l (𝓝 y))
  证明: (continuous_inv.tendsto y).comp h

Depends on / 依赖: continuous_inv, continuous_inv.tendsto, tendsto
-/
theorem Filter.Tendsto.inv {f : α -> G} {l : Filter α} {y : G} (h : Tendsto f l (𝓝 y)) :
    Tendsto (fun x => (f x)⁻¹) l (𝓝 y⁻¹) :=
  (continuous_inv.tendsto y).comp h

variable {f : X -> G} {s : Set X} {x : X}

@[to_fun (attr := to_additive (attr := continuity, fun_prop))]
/--
theorem `Continuous.inv` / 定理 `Continuous.inv`

English:
theorem Continuous.inv
  given: (hf : Continuous f)
  statement: Continuous f⁻¹
  proof: continuous_inv.comp hf

@[to_fun (attr := to_additive (attr := fun_prop))]
nonrec theorem ContinuousWithinAt.inv (hf : ContinuousWithinAt f s x) :
    ContinuousWithinAt f⁻¹ s x :=
  hf.inv

@[to_fun (attr := to_additive (attr := fun_prop))]
nonrec theorem ContinuousAt.inv (hf : ContinuousAt f x) : 

中文:
定理 Continuous.inv
  条件: (hf : Continuous f)
  结论: Continuous f⁻¹
  证明: continuous_inv.comp hf

@[to_fun (attr := to_additive (attr := fun_prop))]
nonrec theorem ContinuousWithinAt.inv (hf : ContinuousWithinAt f s x) :
    ContinuousWithinAt f⁻¹ s x :=
  hf.inv

@[to_fun (attr := to_additive (attr := fun_prop))]
nonrec theorem ContinuousAt.inv (hf : ContinuousAt f x) : 

Depends on / 依赖: continuous_inv, continuous_inv.comp
-/
theorem Continuous.inv (hf : Continuous f) : Continuous f⁻¹ :=
  continuous_inv.comp hf

@[to_fun (attr := to_additive (attr := fun_prop))]
nonrec theorem ContinuousWithinAt.inv (hf : ContinuousWithinAt f s x) :
    ContinuousWithinAt f⁻¹ s x :=
  hf.inv

@[to_fun (attr := to_additive (attr := fun_prop))]
nonrec theorem ContinuousAt.inv (hf : ContinuousAt f x) : ContinuousAt f⁻¹ x :=
  hf.inv

@[to_fun (attr := to_additive (attr := fun_prop))]
/--
theorem `ContinuousOn.inv` / 定理 `ContinuousOn.inv`

English:
theorem ContinuousOn.inv
  given: (hf : ContinuousOn f s)
  statement: ContinuousOn f⁻¹ s
  proof: fun x hx =>
  (hf x hx).inv

中文:
定理 ContinuousOn.inv
  条件: (hf : ContinuousOn f s)
  结论: ContinuousOn f⁻¹ s
  证明: fun x hx =>
  (hf x hx).inv
-/
theorem ContinuousOn.inv (hf : ContinuousOn f s) : ContinuousOn f⁻¹ s := fun x hx =>
  (hf x hx).inv

end ContinuousInv

/--
Definition of `IsTopologicalAddGroup` / `IsTopologicalAddGroup` 的定义

English:
class IsTopologicalAddGroup
  parameters: (G : Type u) [TopologicalSpace G] [AddGroup G]
  extends: ContinuousAdd G, ContinuousNeg G
  (no additional axioms)

中文:
类 IsTopologicalAddGroup
  参数: (G : 类型u) [TopologicalSpace G] [AddGroup G]
  继承: ContinuousAdd G, ContinuousNeg G
  (无附加公理)
-/
class IsTopologicalAddGroup (G : Type u) [TopologicalSpace G] [AddGroup G] : Prop
    extends ContinuousAdd G, ContinuousNeg G

/-- A topological group is a group in which the multiplication and inversion operations are
continuous.

When you declare an instance that does not already have a `UniformSpace` instance,
you should also provide an instance of `UniformSpace` and `IsUniformGroup` using
`IsTopologicalGroup.rightUniformSpace` and `isUniformGroup_of_commGroup`. -/
@[to_additive]
/--
Definition of `IsTopologicalGroup` / `IsTopologicalGroup` 的定义

English:
class IsTopologicalGroup
  parameters: (G : Type*) [TopologicalSpace G] [Group G]
  extends: ContinuousMul G, ContinuousInv G
  (no additional axioms)

中文:
类 IsTopologicalGroup
  参数: (G : 类型) [TopologicalSpace G] [Group G]
  继承: ContinuousMul G, ContinuousInv G
  (无附加公理)
-/
class IsTopologicalGroup (G : Type*) [TopologicalSpace G] [Group G] : Prop
    extends ContinuousMul G, ContinuousInv G

/--
Definition of `ContinuousSub` / `ContinuousSub` 的定义

English:
class ContinuousSub
  parameters: (G : Type*) [TopologicalSpace G] [Sub G]
  axioms and operations (1):
    - continuous_sub : Continuous fun p : G × G => p.1 - p.2

中文:
类 ContinuousSub
  参数: (G : 类型) [TopologicalSpace G] [Sub G]
  公理与运算 (1 个):
    - continuous_sub : Continuous fun p : G × G => p.1 - p.2
-/
class ContinuousSub (G : Type*) [TopologicalSpace G] [Sub G] : Prop where
  continuous_sub : Continuous fun p : G × G => p.1 - p.2

/-- A typeclass saying that `p : G × G ↦ p.1 / p.2` is a continuous function. This property
automatically holds for topological groups. Lemmas using this class have primes.
The unprimed version is for `GroupWithZero`. -/
@[to_additive existing]
/--
Definition of `ContinuousDiv` / `ContinuousDiv` 的定义

English:
class ContinuousDiv
  parameters: (G : Type*) [TopologicalSpace G] [Div G]
  axioms and operations (1):
    - continuous_div' : Continuous fun p : G × G => p.1 / p.2

中文:
类 ContinuousDiv
  参数: (G : 类型) [TopologicalSpace G] [Div G]
  公理与运算 (1 个):
    - continuous_div' : Continuous fun p : G × G => p.1 / p.2
-/
class ContinuousDiv (G : Type*) [TopologicalSpace G] [Div G] : Prop where
  continuous_div' : Continuous fun p : G × G => p.1 / p.2

-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) IsTopologicalGroup.to_continuousDiv
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] : ContinuousDiv G where
  continuous_div' := by
    simp only [div_eq_mul_inv]
exact continuous_mul.comp₂ continuous_fst continuous_inv.comp continuous_snd

export ContinuousSub (continuous_sub)
export ContinuousDiv (continuous_div')

section ContinuousDiv

variable [TopologicalSpace G] [Div G] [ContinuousDiv G]

@[to_additive sub]
/--
theorem `Filter.Tendsto.div'` / 定理 `Filter.Tendsto.div'`

English:
theorem Filter.Tendsto.div'
  statement: {f g : α -> G} {l : Filter α} {a b : G} (hf : Tendsto f l (𝓝 a))
  proof: (continuous_div'.tendsto (a, b)).comp (hf.prodMk_nhds hg)

中文:
定理 Filter.Tendsto.div'
  结论: {f g : α -> G} {l : Filter α} {a b : G} (hf : Tendsto f l (𝓝 a))
  证明: (continuous_div'.tendsto (a, b)).comp (hf.prodMk_nhds hg)

Depends on / 依赖: continuous_div, hf.prodMk_nhds, prodMk_nhds, tendsto
-/
theorem Filter.Tendsto.div' {f g : α -> G} {l : Filter α} {a b : G} (hf : Tendsto f l (𝓝 a))
    (hg : Tendsto g l (𝓝 b)) : Tendsto (fun x => f x / g x) l (𝓝 (a / b)) :=
  (continuous_div'.tendsto (a, b)).comp (hf.prodMk_nhds hg)

variable {f g : X -> G} {s : Set X} {x : X}

@[to_additive (attr := to_fun (attr := fun_prop)) sub]
nonrec theorem ContinuousAt.div' (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    ContinuousAt (f / g) x :=
  hf.div' hg

@[to_additive (attr := to_fun (attr := fun_prop)) sub]
/--
theorem `ContinuousWithinAt.div'` / 定理 `ContinuousWithinAt.div'`

English:
theorem ContinuousWithinAt.div'
  given: (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x)
  proof: Filter.Tendsto.div' hf hg

@[to_additive (attr := to_fun (attr := fun_prop)) sub]

中文:
定理 ContinuousWithinAt.div'
  条件: (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x)
  证明: Filter.Tendsto.div' hf hg

@[to_additive (attr := to_fun (attr := fun_prop)) sub]

Depends on / 依赖: Filter, Filter.Tendsto.div, Tendsto
-/
theorem ContinuousWithinAt.div' (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x) :
    ContinuousWithinAt (f / g) s x :=
  Filter.Tendsto.div' hf hg

@[to_additive (attr := to_fun (attr := fun_prop)) sub]
/--
theorem `ContinuousOn.div'` / 定理 `ContinuousOn.div'`

English:
theorem ContinuousOn.div'
  given: (hf : ContinuousOn f s) (hg : ContinuousOn g s)
  proof: fun x hx => (hf x hx).div' (hg x hx)

@[to_additive (attr := to_fun (attr := continuity, fun_prop)) sub]

中文:
定理 ContinuousOn.div'
  条件: (hf : ContinuousOn f s) (hg : ContinuousOn g s)
  证明: fun x hx => (hf x hx).div' (hg x hx)

@[to_additive (attr := to_fun (attr := continuity, fun_prop)) sub]
-/
theorem ContinuousOn.div' (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (f / g) s := fun x hx => (hf x hx).div' (hg x hx)

@[to_additive (attr := to_fun (attr := continuity, fun_prop)) sub]
/--
theorem `Continuous.div'` / 定理 `Continuous.div'`

English:
theorem Continuous.div'
  given: (hf : Continuous f) (hg : Continuous g)
  statement: Continuous (f / g)
  proof: continuous_div'.comp₂ hf hg

中文:
定理 Continuous.div'
  条件: (hf : Continuous f) (hg : Continuous g)
  结论: Continuous (f / g)
  证明: continuous_div'.comp₂ hf hg

Depends on / 依赖: continuous_div
-/
theorem Continuous.div' (hf : Continuous f) (hg : Continuous g) : Continuous (f / g) :=
  continuous_div'.comp₂ hf hg

end ContinuousDiv
