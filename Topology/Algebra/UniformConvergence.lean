/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Topology.Algebra.UniformMulAction
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Topology.UniformSpace.UniformConvergenceTopology

/-!
# Algebraic facts about the topology of uniform convergence

This file contains algebraic compatibility results about the uniform structure of uniform
convergence / `𝔖`-convergence. They will mostly be useful for defining strong topologies on the
space of continuous linear maps between two topological vector spaces.

## Main statements

* `UniformFun.uniform_group` : if `G` is a uniform group, then `α →ᵤ G` a uniform group
* `UniformOnFun.uniform_group` : if `G` is a uniform group, then for any `𝔖 : Set (Set α)`,
  `α →ᵤ[𝔖] G` a uniform group.

## Implementation notes

Like in `Mathlib/Topology/UniformSpace/UniformConvergenceTopology.lean`, we use the type aliases
`UniformFun` (denoted `α →ᵤ β`) and `UniformOnFun` (denoted `α →ᵤ[𝔖] β`) for functions from `α`
to `β` endowed with the structures of uniform convergence and `𝔖`-convergence.

## References

* [N. Bourbaki, *General Topology, Chapter X*][bourbaki1966]
* [N. Bourbaki, *Topological Vector Spaces*][bourbaki1987]

## Tags

uniform convergence, strong dual

-/

public section

open Filter

open scoped Topology Pointwise UniformConvergence Uniformity

section AlgebraicInstances

variable {α β ι R : Type*} {𝔖 : Set <| Set α} {x : α}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [One
  signature: β] : One (α ->ᵤ β)
  body: inferInstanceAs One (α -> β)

@[to_additive (attr := simp)]

中文:
实例 [One
  签名: β] : One (α ->ᵤ β)
  定义体: inferInstanceAs One (α -> β)

@[to_additive (attr := simp)]
-/
@[to_additive] instance [One β] : One (α ->ᵤ β) := inferInstanceAs One (α -> β)

@[to_additive (attr := simp)]
/--
lemma `UniformFun.toFun_one` / 引理 `UniformFun.toFun_one`

English:
lemma UniformFun.toFun_one
  given: [One β]
  statement: toFun (1 : α ->ᵤ β) = 1
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 UniformFun.toFun_one
  条件: [One β]
  结论: toFun (1 : α ->ᵤ β) = 1
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma UniformFun.toFun_one [One β] : toFun (1 : α ->ᵤ β) = 1 := rfl

@[to_additive (attr := simp)]
/--
lemma `UniformFun.ofFun_one` / 引理 `UniformFun.ofFun_one`

English:
lemma UniformFun.ofFun_one
  given: [One β]
  statement: ofFun (1 : α -> β) = 1
  proof: rfl

中文:
引理 UniformFun.ofFun_one
  条件: [One β]
  结论: ofFun (1 : α -> β) = 1
  证明: rfl
-/
lemma UniformFun.ofFun_one [One β] : ofFun (1 : α -> β) = 1 := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [One
  signature: β] : One (α ->ᵤ[𝔖] β)
  body: inferInstanceAs One (α -> β)

@[to_additive (attr := simp)]

中文:
实例 [One
  签名: β] : One (α ->ᵤ[𝔖] β)
  定义体: inferInstanceAs One (α -> β)

@[to_additive (attr := simp)]
-/
@[to_additive] instance [One β] : One (α ->ᵤ[𝔖] β) := inferInstanceAs One (α -> β)

@[to_additive (attr := simp)]
/--
lemma `UniformOnFun.toFun_one` / 引理 `UniformOnFun.toFun_one`

English:
lemma UniformOnFun.toFun_one
  given: [One β]
  statement: toFun 𝔖 (1 : α ->ᵤ[𝔖] β) = 1
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 UniformOnFun.toFun_one
  条件: [One β]
  结论: toFun 𝔖 (1 : α ->ᵤ[𝔖] β) = 1
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma UniformOnFun.toFun_one [One β] : toFun 𝔖 (1 : α ->ᵤ[𝔖] β) = 1 := rfl

@[to_additive (attr := simp)]
/--
lemma `UniformOnFun.one_apply` / 引理 `UniformOnFun.one_apply`

English:
lemma UniformOnFun.one_apply
  given: [One β]
  statement: ofFun 𝔖 (1 : α -> β) = 1
  proof: rfl

中文:
引理 UniformOnFun.one_apply
  条件: [One β]
  结论: ofFun 𝔖 (1 : α -> β) = 1
  证明: rfl
-/
lemma UniformOnFun.one_apply [One β] : ofFun 𝔖 (1 : α -> β) = 1 := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mul
  signature: β] : Mul (α ->ᵤ β)
  body: inferInstanceAs Mul (α -> β)

@[to_additive (attr := simp)]

中文:
实例 [Mul
  签名: β] : Mul (α ->ᵤ β)
  定义体: inferInstanceAs Mul (α -> β)

@[to_additive (attr := simp)]
-/
@[to_additive] instance [Mul β] : Mul (α ->ᵤ β) := inferInstanceAs Mul (α -> β)

@[to_additive (attr := simp)]
/--
lemma `UniformFun.toFun_mul` / 引理 `UniformFun.toFun_mul`

English:
lemma UniformFun.toFun_mul
  given: [Mul β] (f g : α ->ᵤ β)
  statement: toFun (f * g) = toFun f * toFun g
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 UniformFun.toFun_mul
  条件: [Mul β] (f g : α ->ᵤ β)
  结论: toFun (f * g) = toFun f * toFun g
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma UniformFun.toFun_mul [Mul β] (f g : α ->ᵤ β) : toFun (f * g) = toFun f * toFun g := rfl

@[to_additive (attr := simp)]
/--
lemma `UniformFun.ofFun_mul` / 引理 `UniformFun.ofFun_mul`

English:
lemma UniformFun.ofFun_mul
  given: [Mul β] (f g : α -> β)
  statement: ofFun (f * g) = ofFun f * ofFun g
  proof: rfl

中文:
引理 UniformFun.ofFun_mul
  条件: [Mul β] (f g : α -> β)
  结论: ofFun (f * g) = ofFun f * ofFun g
  证明: rfl
-/
lemma UniformFun.ofFun_mul [Mul β] (f g : α -> β) : ofFun (f * g) = ofFun f * ofFun g := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mul
  signature: β] : Mul (α ->ᵤ[𝔖] β)
  body: inferInstanceAs Mul (α -> β)

@[to_additive (attr := simp)]

中文:
实例 [Mul
  签名: β] : Mul (α ->ᵤ[𝔖] β)
  定义体: inferInstanceAs Mul (α -> β)

@[to_additive (attr := simp)]
-/
@[to_additive] instance [Mul β] : Mul (α ->ᵤ[𝔖] β) := inferInstanceAs Mul (α -> β)

@[to_additive (attr := simp)]
/--
lemma `UniformOnFun.toFun_mul` / 引理 `UniformOnFun.toFun_mul`

English:
lemma UniformOnFun.toFun_mul
  given: [Mul β] (f g : α ->ᵤ[𝔖] β)
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 UniformOnFun.toFun_mul
  条件: [Mul β] (f g : α ->ᵤ[𝔖] β)
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma UniformOnFun.toFun_mul [Mul β] (f g : α ->ᵤ[𝔖] β) :
    toFun 𝔖 (f * g) = toFun 𝔖 f * toFun 𝔖 g :=
  rfl

@[to_additive (attr := simp)]
/--
lemma `UniformOnFun.ofFun_mul` / 引理 `UniformOnFun.ofFun_mul`

English:
lemma UniformOnFun.ofFun_mul
  given: [Mul β] (f g : α -> β)
  statement: ofFun 𝔖 (f * g) = ofFun 𝔖 f * ofFun 𝔖 g
  proof: rfl

中文:
引理 UniformOnFun.ofFun_mul
  条件: [Mul β] (f g : α -> β)
  结论: ofFun 𝔖 (f * g) = ofFun 𝔖 f * ofFun 𝔖 g
  证明: rfl
-/
lemma UniformOnFun.ofFun_mul [Mul β] (f g : α -> β) : ofFun 𝔖 (f * g) = ofFun 𝔖 f * ofFun 𝔖 g := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inv
  signature: β] : Inv (α ->ᵤ β)
  body: inferInstanceAs Inv (α -> β)

@[to_additive (attr := simp)]

中文:
实例 [Inv
  签名: β] : Inv (α ->ᵤ β)
  定义体: inferInstanceAs Inv (α -> β)

@[to_additive (attr := simp)]
-/
@[to_additive] instance [Inv β] : Inv (α ->ᵤ β) := inferInstanceAs Inv (α -> β)

@[to_additive (attr := simp)]
/--
lemma `UniformFun.toFun_inv` / 引理 `UniformFun.toFun_inv`

English:
lemma UniformFun.toFun_inv
  given: [Inv β] (f : α ->ᵤ β)
  statement: toFun (f⁻¹) = (toFun f)⁻¹
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 UniformFun.toFun_inv
  条件: [Inv β] (f : α ->ᵤ β)
  结论: toFun (f⁻¹) = (toFun f)⁻¹
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma UniformFun.toFun_inv [Inv β] (f : α ->ᵤ β) : toFun (f⁻¹) = (toFun f)⁻¹ := rfl

@[to_additive (attr := simp)]
/--
lemma `UniformFun.ofFun_inv` / 引理 `UniformFun.ofFun_inv`

English:
lemma UniformFun.ofFun_inv
  given: [Inv β] (f : α -> β)
  statement: ofFun (f⁻¹) = (ofFun f)⁻¹
  proof: rfl

中文:
引理 UniformFun.ofFun_inv
  条件: [Inv β] (f : α -> β)
  结论: ofFun (f⁻¹) = (ofFun f)⁻¹
  证明: rfl
-/
lemma UniformFun.ofFun_inv [Inv β] (f : α -> β) : ofFun (f⁻¹) = (ofFun f)⁻¹ := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inv
  signature: β] : Inv (α ->ᵤ[𝔖] β)
  body: inferInstanceAs Inv (α -> β)

@[to_additive (attr := simp)]

中文:
实例 [Inv
  签名: β] : Inv (α ->ᵤ[𝔖] β)
  定义体: inferInstanceAs Inv (α -> β)

@[to_additive (attr := simp)]
-/
@[to_additive] instance [Inv β] : Inv (α ->ᵤ[𝔖] β) := inferInstanceAs Inv (α -> β)

@[to_additive (attr := simp)]
/--
lemma `UniformOnFun.toFun_inv` / 引理 `UniformOnFun.toFun_inv`

English:
lemma UniformOnFun.toFun_inv
  given: [Inv β] (f : α ->ᵤ[𝔖] β)
  statement: toFun 𝔖 (f⁻¹) = (toFun 𝔖 f)⁻¹
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 UniformOnFun.toFun_inv
  条件: [Inv β] (f : α ->ᵤ[𝔖] β)
  结论: toFun 𝔖 (f⁻¹) = (toFun 𝔖 f)⁻¹
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma UniformOnFun.toFun_inv [Inv β] (f : α ->ᵤ[𝔖] β) : toFun 𝔖 (f⁻¹) = (toFun 𝔖 f)⁻¹ := rfl

@[to_additive (attr := simp)]
/--
lemma `UniformOnFun.ofFun_inv` / 引理 `UniformOnFun.ofFun_inv`

English:
lemma UniformOnFun.ofFun_inv
  given: [Inv β] (f : α -> β)
  statement: ofFun 𝔖 (f⁻¹) = (ofFun 𝔖 f)⁻¹
  proof: rfl

中文:
引理 UniformOnFun.ofFun_inv
  条件: [Inv β] (f : α -> β)
  结论: ofFun 𝔖 (f⁻¹) = (ofFun 𝔖 f)⁻¹
  证明: rfl
-/
lemma UniformOnFun.ofFun_inv [Inv β] (f : α -> β) : ofFun 𝔖 (f⁻¹) = (ofFun 𝔖 f)⁻¹ := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Div
  signature: β] : Div (α ->ᵤ β)
  body: inferInstanceAs Div (α -> β)

@[to_additive (attr := simp)]

中文:
实例 [Div
  签名: β] : Div (α ->ᵤ β)
  定义体: inferInstanceAs Div (α -> β)

@[to_additive (attr := simp)]
-/
@[to_additive] instance [Div β] : Div (α ->ᵤ β) := inferInstanceAs Div (α -> β)

@[to_additive (attr := simp)]
/--
lemma `UniformFun.toFun_div` / 引理 `UniformFun.toFun_div`

English:
lemma UniformFun.toFun_div
  given: [Div β] (f g : α ->ᵤ β)
  statement: toFun (f / g) = toFun f / toFun g
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 UniformFun.toFun_div
  条件: [Div β] (f g : α ->ᵤ β)
  结论: toFun (f / g) = toFun f / toFun g
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma UniformFun.toFun_div [Div β] (f g : α ->ᵤ β) : toFun (f / g) = toFun f / toFun g := rfl

@[to_additive (attr := simp)]
/--
lemma `UniformFun.ofFun_div` / 引理 `UniformFun.ofFun_div`

English:
lemma UniformFun.ofFun_div
  given: [Div β] (f g : α -> β)
  statement: ofFun (f / g) = ofFun f / ofFun g
  proof: rfl

中文:
引理 UniformFun.ofFun_div
  条件: [Div β] (f g : α -> β)
  结论: ofFun (f / g) = ofFun f / ofFun g
  证明: rfl
-/
lemma UniformFun.ofFun_div [Div β] (f g : α -> β) : ofFun (f / g) = ofFun f / ofFun g := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Div
  signature: β] : Div (α ->ᵤ[𝔖] β)
  body: inferInstanceAs Div (α -> β)

@[to_additive (attr := simp)]

中文:
实例 [Div
  签名: β] : Div (α ->ᵤ[𝔖] β)
  定义体: inferInstanceAs Div (α -> β)

@[to_additive (attr := simp)]
-/
@[to_additive] instance [Div β] : Div (α ->ᵤ[𝔖] β) := inferInstanceAs Div (α -> β)

@[to_additive (attr := simp)]
/--
lemma `UniformOnFun.toFun_div` / 引理 `UniformOnFun.toFun_div`

English:
lemma UniformOnFun.toFun_div
  given: [Div β] (f g : α ->ᵤ[𝔖] β)
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 UniformOnFun.toFun_div
  条件: [Div β] (f g : α ->ᵤ[𝔖] β)
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma UniformOnFun.toFun_div [Div β] (f g : α ->ᵤ[𝔖] β) :
    toFun 𝔖 (f / g) = toFun 𝔖 f / toFun 𝔖 g :=
  rfl

@[to_additive (attr := simp)]
/--
lemma `UniformOnFun.ofFun_div` / 引理 `UniformOnFun.ofFun_div`

English:
lemma UniformOnFun.ofFun_div
  given: [Div β] (f g : α -> β)
  statement: ofFun 𝔖 (f / g) = ofFun 𝔖 f / ofFun 𝔖 g
  proof: rfl

@[to_additive]

中文:
引理 UniformOnFun.ofFun_div
  条件: [Div β] (f g : α -> β)
  结论: ofFun 𝔖 (f / g) = ofFun 𝔖 f / ofFun 𝔖 g
  证明: rfl

@[to_additive]
-/
lemma UniformOnFun.ofFun_div [Div β] (f g : α -> β) : ofFun 𝔖 (f / g) = ofFun 𝔖 f / ofFun 𝔖 g := rfl

@[to_additive]
instance {M : Type*} [Pow β M] : Pow (α ->ᵤ β) M := inferInstanceAs Pow (α -> β) M

@[to_additive (attr := simp) toFun_smul]
/--
lemma `UniformFun.toFun_pow` / 引理 `UniformFun.toFun_pow`

English:
lemma UniformFun.toFun_pow
  given: {M : Type*} [Pow β M] (c : M) (f : α ->ᵤ β)
  proof: rfl

@[to_additive (attr := simp) ofFun_smul]

中文:
引理 UniformFun.toFun_pow
  条件: {M : 类型} [Pow β M] (c : M) (f : α ->ᵤ β)
  证明: rfl

@[to_additive (attr := simp) ofFun_smul]
-/
lemma UniformFun.toFun_pow {M : Type*} [Pow β M] (c : M) (f : α ->ᵤ β) :
    toFun (f ^ c) = toFun f ^ c :=
  rfl

@[to_additive (attr := simp) ofFun_smul]
/--
lemma `UniformFun.ofFun_pow` / 引理 `UniformFun.ofFun_pow`

English:
lemma UniformFun.ofFun_pow
  given: {M : Type*} [Pow β M] (c : M) (f : α -> β)
  proof: rfl

@[to_additive]

中文:
引理 UniformFun.ofFun_pow
  条件: {M : 类型} [Pow β M] (c : M) (f : α -> β)
  证明: rfl

@[to_additive]
-/
lemma UniformFun.ofFun_pow {M : Type*} [Pow β M] (c : M) (f : α -> β) :
    ofFun (f ^ c) = ofFun f ^ c :=
  rfl

@[to_additive]
instance {M : Type*} [Pow β M] : Pow (α ->ᵤ[𝔖] β) M := inferInstanceAs Pow (α -> β) M

@[to_additive (attr := simp) toFun_smul]
/--
lemma `UniformOnFun.toFun_pow` / 引理 `UniformOnFun.toFun_pow`

English:
lemma UniformOnFun.toFun_pow
  given: {M : Type*} [Pow β M] (c : M) (f : α ->ᵤ[𝔖] β)
  proof: rfl

@[to_additive (attr := simp) ofFun_smul]

中文:
引理 UniformOnFun.toFun_pow
  条件: {M : 类型} [Pow β M] (c : M) (f : α ->ᵤ[𝔖] β)
  证明: rfl

@[to_additive (attr := simp) ofFun_smul]
-/
lemma UniformOnFun.toFun_pow {M : Type*} [Pow β M] (c : M) (f : α ->ᵤ[𝔖] β) :
    toFun 𝔖 (f ^ c) = toFun 𝔖 f ^ c :=
  rfl

@[to_additive (attr := simp) ofFun_smul]
/--
lemma `UniformOnFun.ofFun_pow` / 引理 `UniformOnFun.ofFun_pow`

English:
lemma UniformOnFun.ofFun_pow
  given: {M : Type*} [Pow β M] (c : M) (f : α -> β)
  proof: rfl

@[to_additive]

中文:
引理 UniformOnFun.ofFun_pow
  条件: {M : 类型} [Pow β M] (c : M) (f : α -> β)
  证明: rfl

@[to_additive]
-/
lemma UniformOnFun.ofFun_pow {M : Type*} [Pow β M] (c : M) (f : α -> β) :
    ofFun 𝔖 (f ^ c) = ofFun 𝔖 f ^ c :=
  rfl

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: β] : Monoid (α ->ᵤ β)
  body: inferInstanceAs Monoid (α -> β)

@[to_additive]

中文:
实例 [Monoid
  签名: β] : Monoid (α ->ᵤ β)
  定义体: inferInstanceAs Monoid (α -> β)

@[to_additive]

Depends on / 依赖: Monoid
-/
instance [Monoid β] : Monoid (α ->ᵤ β) := inferInstanceAs Monoid (α -> β)

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: β] : Monoid (α ->ᵤ[𝔖] β)
  body: inferInstanceAs Monoid (α -> β)

@[to_additive]

中文:
实例 [Monoid
  签名: β] : Monoid (α ->ᵤ[𝔖] β)
  定义体: inferInstanceAs Monoid (α -> β)

@[to_additive]

Depends on / 依赖: Monoid
-/
instance [Monoid β] : Monoid (α ->ᵤ[𝔖] β) := inferInstanceAs Monoid (α -> β)

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommMonoid
  signature: β] : CommMonoid (α ->ᵤ β)
  body: inferInstanceAs CommMonoid (α -> β)

@[to_additive]

中文:
实例 [CommMonoid
  签名: β] : CommMonoid (α ->ᵤ β)
  定义体: inferInstanceAs CommMonoid (α -> β)

@[to_additive]

Depends on / 依赖: CommMonoid
-/
instance [CommMonoid β] : CommMonoid (α ->ᵤ β) := inferInstanceAs CommMonoid (α -> β)

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommMonoid
  signature: β] : CommMonoid (α ->ᵤ[𝔖] β)
  body: inferInstanceAs CommMonoid (α -> β)

@[to_additive]

中文:
实例 [CommMonoid
  签名: β] : CommMonoid (α ->ᵤ[𝔖] β)
  定义体: inferInstanceAs CommMonoid (α -> β)

@[to_additive]

Depends on / 依赖: CommMonoid
-/
instance [CommMonoid β] : CommMonoid (α ->ᵤ[𝔖] β) := inferInstanceAs CommMonoid (α -> β)

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Group
  signature: β] : Group (α ->ᵤ β)
  body: inferInstanceAs Group (α -> β)

@[to_additive]

中文:
实例 [Group
  签名: β] : Group (α ->ᵤ β)
  定义体: inferInstanceAs Group (α -> β)

@[to_additive]
-/
instance [Group β] : Group (α ->ᵤ β) := inferInstanceAs Group (α -> β)

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Group
  signature: β] : Group (α ->ᵤ[𝔖] β)
  body: inferInstanceAs Group (α -> β)

@[to_additive]

中文:
实例 [Group
  签名: β] : Group (α ->ᵤ[𝔖] β)
  定义体: inferInstanceAs Group (α -> β)

@[to_additive]
-/
instance [Group β] : Group (α ->ᵤ[𝔖] β) := inferInstanceAs Group (α -> β)

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommGroup
  signature: β] : CommGroup (α ->ᵤ β)
  body: inferInstanceAs CommGroup (α -> β)

@[to_additive]

中文:
实例 [CommGroup
  签名: β] : CommGroup (α ->ᵤ β)
  定义体: inferInstanceAs CommGroup (α -> β)

@[to_additive]

Depends on / 依赖: CommGroup
-/
instance [CommGroup β] : CommGroup (α ->ᵤ β) := inferInstanceAs CommGroup (α -> β)

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommGroup
  signature: β] : CommGroup (α ->ᵤ[𝔖] β)
  body: inferInstanceAs CommGroup (α -> β)

中文:
实例 [CommGroup
  签名: β] : CommGroup (α ->ᵤ[𝔖] β)
  定义体: inferInstanceAs CommGroup (α -> β)

Depends on / 依赖: CommGroup
-/
instance [CommGroup β] : CommGroup (α ->ᵤ[𝔖] β) := inferInstanceAs CommGroup (α -> β)

instance {M N : Type*} [SMul M N] [SMul M β] [SMul N β] [IsScalarTower M N β] :
    IsScalarTower M N (α ->ᵤ β) :=
inferInstanceAs IsScalarTower M N (α -> β)

instance {M N : Type*} [SMul M N] [SMul M β] [SMul N β] [IsScalarTower M N β] :
    IsScalarTower M N (α ->ᵤ[𝔖] β) :=
inferInstanceAs IsScalarTower M N (α -> β)

instance {M N : Type*} [SMul M β] [SMul N β] [SMulCommClass M N β] :
    SMulCommClass M N (α ->ᵤ β) :=
inferInstanceAs SMulCommClass M N (α -> β)

instance {M N : Type*} [SMul M β] [SMul N β] [SMulCommClass M N β] :
    SMulCommClass M N (α ->ᵤ[𝔖] β) :=
inferInstanceAs SMulCommClass M N (α -> β)

instance {M : Type*} [Monoid M] [MulAction M β] : MulAction M (α ->ᵤ β) :=
inferInstanceAs MulAction M (α -> β)

instance {M : Type*} [Monoid M] [MulAction M β] : MulAction M (α ->ᵤ[𝔖] β) :=
inferInstanceAs MulAction M (α -> β)

instance {M : Type*} [Monoid M] [AddMonoid β] [DistribMulAction M β] :
    DistribMulAction M (α ->ᵤ β) :=
inferInstanceAs DistribMulAction M (α -> β)

instance {M : Type*} [Monoid M] [AddMonoid β] [DistribMulAction M β] :
    DistribMulAction M (α ->ᵤ[𝔖] β) :=
inferInstanceAs DistribMulAction M (α -> β)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Semiring
  signature: R] [AddCommMonoid β] [Module R β] : Module R (α ->ᵤ β)
  body: inferInstanceAs Module R (α -> β)

中文:
实例 [Semiring
  签名: R] [AddCommMonoid β] [Module R β] : Module R (α ->ᵤ β)
  定义体: inferInstanceAs Module R (α -> β)

Depends on / 依赖: Module
-/
instance [Semiring R] [AddCommMonoid β] [Module R β] : Module R (α ->ᵤ β) :=
inferInstanceAs Module R (α -> β)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Semiring
  signature: R] [AddCommMonoid β] [Module R β] : Module R (α ->ᵤ[𝔖] β)
  body: inferInstanceAs Module R (α -> β)

中文:
实例 [Semiring
  签名: R] [AddCommMonoid β] [Module R β] : Module R (α ->ᵤ[𝔖] β)
  定义体: inferInstanceAs Module R (α -> β)

Depends on / 依赖: Module
-/
instance [Semiring R] [AddCommMonoid β] [Module R β] : Module R (α ->ᵤ[𝔖] β) :=
inferInstanceAs Module R (α -> β)

end AlgebraicInstances

section Group

variable {α G ι : Type*} [Group G] {𝔖 : Set <| Set α} [UniformSpace G] [IsUniformGroup G]

/-- If `G` is a uniform group, then `α →ᵤ G` is a uniform group as well. -/
@[to_additive /-- If `G` is a uniform additive group,
then `α →ᵤ G` is a uniform additive group as well. -/]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsUniformGroup (α ->ᵤ G)
  body: ⟨(-- Since `(/) : G × G → G` is uniformly continuous,
    -- `UniformFun.postcomp_uniformContinuous` tells us that
    -- `((/) ∘ —) : (α →ᵤ G × G) → (α →ᵤ G)` is uniformly continuous too. By precomposing with
    -- `UniformFun.uniformEquivProdArrow`, this gives that
    -- `(/) : (α →ᵤ G) × (α →ᵤ 

中文:
实例 :
  签名: IsUniformGroup (α ->ᵤ G)
  定义体: ⟨(-- Since `(/) : G × G → G` is uniformly continuous,
    -- `UniformFun.postcomp_uniformContinuous` tells us that
    -- `((/) ∘ —) : (α →ᵤ G × G) → (α →ᵤ G)` is uniformly continuous too. By precomposing with
    -- `UniformFun.uniformEquivProdArrow`, this gives that
    -- `(/) : (α →ᵤ G) × (α →ᵤ 

Depends on / 依赖: continuous, uniformly
-/
instance : IsUniformGroup (α ->ᵤ G) :=
  ⟨(-- Since `(/) : G × G → G` is uniformly continuous,
    -- `UniformFun.postcomp_uniformContinuous` tells us that
    -- `((/) ∘ —) : (α →ᵤ G × G) → (α →ᵤ G)` is uniformly continuous too. By precomposing with
    -- `UniformFun.uniformEquivProdArrow`, this gives that
    -- `(/) : (α →ᵤ G) × (α →ᵤ G) → (α →ᵤ G)` is also uniformly continuous
    UniformFun.postcomp_uniformContinuous uniformContinuous_div).comp
    UniformFun.uniformEquivProdArrow.symm.uniformContinuous⟩

@[to_additive]
/--
theorem `UniformFun.hasBasis_nhds_one_of_basis` / 定理 `UniformFun.hasBasis_nhds_one_of_basis`

English:
theorem UniformFun.hasBasis_nhds_one_of_basis
  statement: {p : ι -> Prop} {b : ι -> Set G}
  proof: by
  convert! UniformFun.hasBasis_nhds_of_basis α _ (1 : α ->ᵤ G) h.uniformity_of_nhds_one
  simp

@[to_additive]

中文:
定理 UniformFun.hasBasis_nhds_one_of_basis
  结论: {p : ι -> 命题} {b : ι -> Set G}
  证明: by
  convert! UniformFun.hasBasis_nhds_of_basis α _ (1 : α ->ᵤ G) h.uniformity_of_nhds_one
  simp

@[to_additive]
-/
protected theorem UniformFun.hasBasis_nhds_one_of_basis {p : ι -> Prop} {b : ι -> Set G}
    (h : (𝓝 1 : Filter G).HasBasis p b) :
    (𝓝 1 : Filter (α ->ᵤ G)).HasBasis p fun i => { f : α ->ᵤ G | forall x, toFun f x in b i } := by
  convert! UniformFun.hasBasis_nhds_of_basis α _ (1 : α ->ᵤ G) h.uniformity_of_nhds_one
  simp

@[to_additive]
/--
theorem `UniformFun.hasBasis_nhds_one` / 定理 `UniformFun.hasBasis_nhds_one`

English:
theorem UniformFun.hasBasis_nhds_one
  proof: UniformFun.hasBasis_nhds_one_of_basis (basis_sets _)

中文:
定理 UniformFun.hasBasis_nhds_one
  证明: UniformFun.hasBasis_nhds_one_of_basis (basis_sets _)
-/
protected theorem UniformFun.hasBasis_nhds_one :
    (𝓝 1 : Filter (α ->ᵤ G)).HasBasis (fun V : Set G => V in (𝓝 1 : Filter G)) fun V =>
      { f : α -> G | forall x, f x in V } :=
  UniformFun.hasBasis_nhds_one_of_basis (basis_sets _)

/-- Let `𝔖 : Set (Set α)`. If `G` is a uniform group, then `α →ᵤ[𝔖] G` is a uniform group as
well. -/
@[to_additive /-- Let `𝔖 : Set (Set α)`. If `G` is a uniform additive group,
then `α →ᵤ[𝔖] G` is a uniform additive group as well. -/]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsUniformGroup (α ->ᵤ[𝔖] G)
  body: ⟨(-- Since `(/) : G × G → G` is uniformly continuous,
    -- `UniformOnFun.postcomp_uniformContinuous` tells us that
    -- `((/) ∘ —) : (α →ᵤ[𝔖] G × G) → (α →ᵤ[𝔖] G)` is uniformly continuous too. By precomposing with
    -- `UniformOnFun.uniformEquivProdArrow`, this gives that
    -- `(/) : (α →ᵤ[𝔖

中文:
实例 :
  签名: IsUniformGroup (α ->ᵤ[𝔖] G)
  定义体: ⟨(-- Since `(/) : G × G → G` is uniformly continuous,
    -- `UniformOnFun.postcomp_uniformContinuous` tells us that
    -- `((/) ∘ —) : (α →ᵤ[𝔖] G × G) → (α →ᵤ[𝔖] G)` is uniformly continuous too. By precomposing with
    -- `UniformOnFun.uniformEquivProdArrow`, this gives that
    -- `(/) : (α →ᵤ[𝔖

Depends on / 依赖: continuous, uniformly
-/
instance : IsUniformGroup (α ->ᵤ[𝔖] G) :=
  ⟨(-- Since `(/) : G × G → G` is uniformly continuous,
    -- `UniformOnFun.postcomp_uniformContinuous` tells us that
    -- `((/) ∘ —) : (α →ᵤ[𝔖] G × G) → (α →ᵤ[𝔖] G)` is uniformly continuous too. By precomposing with
    -- `UniformOnFun.uniformEquivProdArrow`, this gives that
    -- `(/) : (α →ᵤ[𝔖] G) × (α →ᵤ[𝔖] G) → (α →ᵤ[𝔖] G)` is also uniformly continuous
    UniformOnFun.postcomp_uniformContinuous uniformContinuous_div).comp
    UniformOnFun.uniformEquivProdArrow.symm.uniformContinuous⟩

@[to_additive]
/--
theorem `UniformOnFun.hasBasis_nhds_one_of_basis` / 定理 `UniformOnFun.hasBasis_nhds_one_of_basis`

English:
theorem UniformOnFun.hasBasis_nhds_one_of_basis
  statement: (𝔖 : Set <| Set α) (h𝔖₁ : 𝔖.Nonempty)
  proof: by
  convert!
UniformOnFun.hasBasis_nhds_of_basis α _ 𝔖 (1 : α ->ᵤ[𝔖] G) h𝔖₁ h𝔖₂
      h.uniformity_of_nhds_one_swapped
  simp [UniformOnFun.gen]

@[to_additive]

中文:
定理 UniformOnFun.hasBasis_nhds_one_of_basis
  结论: (𝔖 : Set <| Set α) (h𝔖₁ : 𝔖.Nonempty)
  证明: by
  convert!
UniformOnFun.hasBasis_nhds_of_basis α _ 𝔖 (1 : α ->ᵤ[𝔖] G) h𝔖₁ h𝔖₂
      h.uniformity_of_nhds_one_swapped
  simp [UniformOnFun.gen]

@[to_additive]
-/
protected theorem UniformOnFun.hasBasis_nhds_one_of_basis (𝔖 : Set <| Set α) (h𝔖₁ : 𝔖.Nonempty)
    (h𝔖₂ : DirectedOn (· subseteq ·) 𝔖) {p : ι -> Prop} {b : ι -> Set G}
    (h : (𝓝 1 : Filter G).HasBasis p b) :
    (𝓝 1 : Filter (α ->ᵤ[𝔖] G)).HasBasis (fun Si : Set α × ι => Si.1 in 𝔖 ∧ p Si.2) fun Si =>
      { f : α ->ᵤ[𝔖] G | forall x in Si.1, toFun 𝔖 f x in b Si.2 } := by
  convert!
UniformOnFun.hasBasis_nhds_of_basis α _ 𝔖 (1 : α ->ᵤ[𝔖] G) h𝔖₁ h𝔖₂
      h.uniformity_of_nhds_one_swapped
  simp [UniformOnFun.gen]

@[to_additive]
/--
theorem `UniformOnFun.hasBasis_nhds_one` / 定理 `UniformOnFun.hasBasis_nhds_one`

English:
theorem UniformOnFun.hasBasis_nhds_one
  statement: (𝔖 : Set <| Set α) (h𝔖₁ : 𝔖.Nonempty)
  proof: UniformOnFun.hasBasis_nhds_one_of_basis 𝔖 h𝔖₁ h𝔖₂ (basis_sets _)

@[to_additive (attr := simp)]

中文:
定理 UniformOnFun.hasBasis_nhds_one
  结论: (𝔖 : Set <| Set α) (h𝔖₁ : 𝔖.Nonempty)
  证明: UniformOnFun.hasBasis_nhds_one_of_basis 𝔖 h𝔖₁ h𝔖₂ (basis_sets _)

@[to_additive (attr := simp)]
-/
protected theorem UniformOnFun.hasBasis_nhds_one (𝔖 : Set <| Set α) (h𝔖₁ : 𝔖.Nonempty)
    (h𝔖₂ : DirectedOn (· subseteq ·) 𝔖) :
    (𝓝 1 : Filter (α ->ᵤ[𝔖] G)).HasBasis
      (fun SV : Set α × Set G => SV.1 in 𝔖 ∧ SV.2 in (𝓝 1 : Filter G)) fun SV =>
      { f : α ->ᵤ[𝔖] G | forall x in SV.1, f x in SV.2 } :=
  UniformOnFun.hasBasis_nhds_one_of_basis 𝔖 h𝔖₁ h𝔖₂ (basis_sets _)

@[to_additive (attr := simp)]
/--
lemma `UniformOnFun.ofFun_prod` / 引理 `UniformOnFun.ofFun_prod`

English:
lemma UniformOnFun.ofFun_prod
  given: {β : Type*} [CommMonoid β] {f : ι -> α -> β} (I : Finset ι)
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 UniformOnFun.ofFun_prod
  条件: {β : 类型} [CommMonoid β] {f : ι -> α -> β} (I : Finset ι)
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma UniformOnFun.ofFun_prod {β : Type*} [CommMonoid β] {f : ι -> α -> β} (I : Finset ι) :
    ofFun 𝔖 (∏ i in I, f i) = ∏ i in I, ofFun 𝔖 (f i) :=
  rfl

@[to_additive (attr := simp)]
/--
lemma `UniformOnFun.toFun_prod` / 引理 `UniformOnFun.toFun_prod`

English:
lemma UniformOnFun.toFun_prod
  given: {β : Type*} [CommMonoid β] {f : ι -> α -> β} (I : Finset ι)
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 UniformOnFun.toFun_prod
  条件: {β : 类型} [CommMonoid β] {f : ι -> α -> β} (I : Finset ι)
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma UniformOnFun.toFun_prod {β : Type*} [CommMonoid β] {f : ι -> α -> β} (I : Finset ι) :
    toFun 𝔖 (∏ i in I, f i) = ∏ i in I, toFun 𝔖 (f i) :=
  rfl

@[to_additive (attr := simp)]
/--
lemma `UniformFun.ofFun_prod` / 引理 `UniformFun.ofFun_prod`

English:
lemma UniformFun.ofFun_prod
  given: {β : Type*} [CommMonoid β] {f : ι -> α -> β} (I : Finset ι)
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 UniformFun.ofFun_prod
  条件: {β : 类型} [CommMonoid β] {f : ι -> α -> β} (I : Finset ι)
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma UniformFun.ofFun_prod {β : Type*} [CommMonoid β] {f : ι -> α -> β} (I : Finset ι) :
    ofFun (∏ i in I, f i) = ∏ i in I, ofFun (f i) :=
  rfl

@[to_additive (attr := simp)]
/--
lemma `UniformFun.toFun_prod` / 引理 `UniformFun.toFun_prod`

English:
lemma UniformFun.toFun_prod
  given: {β : Type*} [CommMonoid β] {f : ι -> α -> β} (I : Finset ι)
  proof: rfl

中文:
引理 UniformFun.toFun_prod
  条件: {β : 类型} [CommMonoid β] {f : ι -> α -> β} (I : Finset ι)
  证明: rfl
-/
lemma UniformFun.toFun_prod {β : Type*} [CommMonoid β] {f : ι -> α -> β} (I : Finset ι) :
    toFun (∏ i in I, f i) = ∏ i in I, toFun (f i) :=
  rfl

end Group

section ConstSMul

variable (M α X : Type*) [SMul M X] [UniformSpace X] [UniformContinuousConstSMul M X]

/--
Instance `UniformFun.uniformContinuousConstSMul` / 实例 `UniformFun.uniformContinuousConstSMul`

English:
instance UniformFun.uniformContinuousConstSMul
  signature: :
  body: UniformFun.postcomp_uniformContinuous
    uniformContinuous_const_smul c

中文:
实例 UniformFun.uniformContinuousConstSMul
  签名: :
  定义体: UniformFun.postcomp_uniformContinuous
    uniformContinuous_const_smul c

Depends on / 依赖: UniformFun, UniformFun.postcomp_uniformContinuous, postcomp_uniformContinuous
-/
instance UniformFun.uniformContinuousConstSMul :
    UniformContinuousConstSMul M (α ->ᵤ X) where
uniformContinuous_const_smul c := UniformFun.postcomp_uniformContinuous
    uniformContinuous_const_smul c

/--
Instance `UniformFunOn.uniformContinuousConstSMul` / 实例 `UniformFunOn.uniformContinuousConstSMul`

English:
instance UniformFunOn.uniformContinuousConstSMul
  signature: {𝔖 : Set (Set α)}
  body: UniformOnFun.postcomp_uniformContinuous
    uniformContinuous_const_smul c

中文:
实例 UniformFunOn.uniformContinuousConstSMul
  签名: {𝔖 : Set (Set α)}
  定义体: UniformOnFun.postcomp_uniformContinuous
    uniformContinuous_const_smul c

Depends on / 依赖: UniformOnFun, UniformOnFun.postcomp_uniformContinuous, postcomp_uniformContinuous
-/
instance UniformFunOn.uniformContinuousConstSMul {𝔖 : Set (Set α)} :
    UniformContinuousConstSMul M (α ->ᵤ[𝔖] X) where
uniformContinuous_const_smul c := UniformOnFun.postcomp_uniformContinuous
    uniformContinuous_const_smul c

end ConstSMul
