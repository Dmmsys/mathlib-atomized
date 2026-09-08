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

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance [One β] : One (α →ᵤ β) := inferInstanceAs <| One (α → β)

@[to_additive (attr := simp)]
/-
**UniformFun.toFun_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：UniformFun.toFun_one [One β] : toFun (1 : α ->ᵤ β) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma UniformFun.toFun_one [One β] : toFun (1 : α →ᵤ β) = 1 := rfl

@[to_additive (attr := simp)]
/-
**UniformFun.ofFun_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：UniformFun.ofFun_one [One β] : ofFun (1 : α -> β) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma UniformFun.ofFun_one [One β] : ofFun (1 : α → β) = 1 := rfl
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance [One β] : One (α →ᵤ[𝔖] β) := inferInstanceAs <| One (α → β)

@[to_additive (attr := simp)]
/-
**UniformOnFun.toFun_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：UniformOnFun.toFun_one [One β] : toFun 𝔖 (1 : α ->ᵤ[𝔖] β) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma UniformOnFun.toFun_one [One β] : toFun 𝔖 (1 : α →ᵤ[𝔖] β) = 1 := rfl

@[to_additive (attr := simp)]
/-
**UniformOnFun.one_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：UniformOnFun.one_apply [One β] : ofFun 𝔖 (1 : α -> β) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma UniformOnFun.one_apply [One β] : ofFun 𝔖 (1 : α → β) = 1 := rfl
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance [Mul β] : Mul (α →ᵤ β) := inferInstanceAs <| Mul (α → β)

@[to_additive (attr := simp)]
/-
**UniformFun.toFun_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：UniformFun.toFun_mul [Mul β] (f g : α ->ᵤ β) : toFun (f * g) = toFun f * t
oFun g
参数：f g : α ->ᵤ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma UniformFun.toFun_mul [Mul β] (f g : α →ᵤ β) : toFun (f * g) = toFun f * toFun g := rfl

@[to_additive (attr := simp)]
/-
**UniformFun.ofFun_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：UniformFun.ofFun_mul [Mul β] (f g : α -> β) : ofFun (f * g) = ofFun f * of
Fun g
参数：f g : α -> β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma UniformFun.ofFun_mul [Mul β] (f g : α → β) : ofFun (f * g) = ofFun f * ofFun g := rfl
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance [Mul β] : Mul (α →ᵤ[𝔖] β) := inferInstanceAs <| Mul (α → β)

@[to_additive (attr := simp)]
/-
**UniformOnFun.toFun_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：UniformOnFun.toFun_mul [Mul β] (f g : α ->ᵤ[𝔖] β) : toFun 𝔖 (f * g) = toFu
n 𝔖 f * toFun 𝔖 g
参数：f g : α ->ᵤ[𝔖] β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma UniformOnFun.toFun_mul [Mul β] (f g : α →ᵤ[𝔖] β) :
    toFun 𝔖 (f * g) = toFun 𝔖 f * toFun 𝔖 g :=
  rfl

@[to_additive (attr := simp)]
/-
**UniformOnFun.ofFun_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：UniformOnFun.ofFun_mul [Mul β] (f g : α -> β) : ofFun 𝔖 (f * g) = ofFun 𝔖 
f * ofFun 𝔖 g
参数：f g : α -> β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma UniformOnFun.ofFun_mul [Mul β] (f g : α → β) : ofFun 𝔖 (f * g) = ofFun 𝔖 f * ofFun 𝔖 g := rfl
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance [Inv β] : Inv (α →ᵤ β) := inferInstanceAs <| Inv (α → β)

@[to_additive (attr := simp)]
/-
**UniformFun.toFun_inv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：UniformFun.toFun_inv [Inv β] (f : α ->ᵤ β) : toFun (f⁻¹) = (toFun f)⁻¹
参数：f : α ->ᵤ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma UniformFun.toFun_inv [Inv β] (f : α →ᵤ β) : toFun (f⁻¹) = (toFun f)⁻¹ := rfl

@[to_additive (attr := simp)]
/-
**UniformFun.ofFun_inv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：UniformFun.ofFun_inv [Inv β] (f : α -> β) : ofFun (f⁻¹) = (ofFun f)⁻¹
参数：f : α -> β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma UniformFun.ofFun_inv [Inv β] (f : α → β) : ofFun (f⁻¹) = (ofFun f)⁻¹ := rfl
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance [Inv β] : Inv (α →ᵤ[𝔖] β) := inferInstanceAs <| Inv (α → β)

@[to_additive (attr := simp)]
/-
**UniformOnFun.toFun_inv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：UniformOnFun.toFun_inv [Inv β] (f : α ->ᵤ[𝔖] β) : toFun 𝔖 (f⁻¹) = (toFun 𝔖
 f)⁻¹
参数：f : α ->ᵤ[𝔖] β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma UniformOnFun.toFun_inv [Inv β] (f : α →ᵤ[𝔖] β) : toFun 𝔖 (f⁻¹) = (toFun 𝔖 f)⁻¹ := rfl

@[to_additive (attr := simp)]
/-
**UniformOnFun.ofFun_inv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：UniformOnFun.ofFun_inv [Inv β] (f : α -> β) : ofFun 𝔖 (f⁻¹) = (ofFun 𝔖 f)⁻
¹
参数：f : α -> β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma UniformOnFun.ofFun_inv [Inv β] (f : α → β) : ofFun 𝔖 (f⁻¹) = (ofFun 𝔖 f)⁻¹ := rfl
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance [Div β] : Div (α →ᵤ β) := inferInstanceAs <| Div (α → β)

@[to_additive (attr := simp)]
/-
**UniformFun.toFun_div** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：UniformFun.toFun_div [Div β] (f g : α ->ᵤ β) : toFun (f / g) = toFun f / t
oFun g
参数：f g : α ->ᵤ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma UniformFun.toFun_div [Div β] (f g : α →ᵤ β) : toFun (f / g) = toFun f / toFun g := rfl

@[to_additive (attr := simp)]
/-
**UniformFun.ofFun_div** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：UniformFun.ofFun_div [Div β] (f g : α -> β) : ofFun (f / g) = ofFun f / of
Fun g
参数：f g : α -> β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma UniformFun.ofFun_div [Div β] (f g : α → β) : ofFun (f / g) = ofFun f / ofFun g := rfl
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance [Div β] : Div (α →ᵤ[𝔖] β) := inferInstanceAs <| Div (α → β)

@[to_additive (attr := simp)]
/-
**UniformOnFun.toFun_div** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：UniformOnFun.toFun_div [Div β] (f g : α ->ᵤ[𝔖] β) : toFun 𝔖 (f / g) = toFu
n 𝔖 f / toFun 𝔖 g
参数：f g : α ->ᵤ[𝔖] β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma UniformOnFun.toFun_div [Div β] (f g : α →ᵤ[𝔖] β) :
    toFun 𝔖 (f / g) = toFun 𝔖 f / toFun 𝔖 g :=
  rfl

@[to_additive (attr := simp)]
/-
**UniformOnFun.ofFun_div** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：UniformOnFun.ofFun_div [Div β] (f g : α -> β) : ofFun 𝔖 (f / g) = ofFun 𝔖 
f / ofFun 𝔖 g
参数：f g : α -> β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma UniformOnFun.ofFun_div [Div β] (f g : α → β) : ofFun 𝔖 (f / g) = ofFun 𝔖 f / ofFun 𝔖 g := rfl

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {M : Type*} [Pow β M] : Pow (α →ᵤ β) M := inferInstanceAs <| Pow (α → β) M

@[to_additive (attr := simp) toFun_smul]
/-
**UniformFun.toFun_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：UniformFun.toFun_pow {M : Type*} [Pow β M] (c : M) (f : α ->ᵤ β) : toFun (
f ^ c) = toFun f ^ c
参数：c : M；f : α ->ᵤ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma UniformFun.toFun_pow {M : Type*} [Pow β M] (c : M) (f : α →ᵤ β) :
    toFun (f ^ c) = toFun f ^ c :=
  rfl

@[to_additive (attr := simp) ofFun_smul]
/-
**UniformFun.ofFun_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：UniformFun.ofFun_pow {M : Type*} [Pow β M] (c : M) (f : α -> β) : ofFun (f
 ^ c) = ofFun f ^ c
参数：c : M；f : α -> β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma UniformFun.ofFun_pow {M : Type*} [Pow β M] (c : M) (f : α → β) :
    ofFun (f ^ c) = ofFun f ^ c :=
  rfl

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {M : Type*} [Pow β M] : Pow (α →ᵤ[𝔖] β) M := inferInstanceAs <| Pow (α → β) M

@[to_additive (attr := simp) toFun_smul]
/-
**UniformOnFun.toFun_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：UniformOnFun.toFun_pow {M : Type*} [Pow β M] (c : M) (f : α ->ᵤ[𝔖] β) : to
Fun 𝔖 (f ^ c) = toFun 𝔖 f ^ c
参数：c : M；f : α ->ᵤ[𝔖] β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma UniformOnFun.toFun_pow {M : Type*} [Pow β M] (c : M) (f : α →ᵤ[𝔖] β) :
    toFun 𝔖 (f ^ c) = toFun 𝔖 f ^ c :=
  rfl

@[to_additive (attr := simp) ofFun_smul]
/-
**UniformOnFun.ofFun_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：UniformOnFun.ofFun_pow {M : Type*} [Pow β M] (c : M) (f : α -> β) : ofFun 
𝔖 (f ^ c) = ofFun 𝔖 f ^ c
参数：c : M；f : α -> β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma UniformOnFun.ofFun_pow {M : Type*} [Pow β M] (c : M) (f : α → β) :
    ofFun 𝔖 (f ^ c) = ofFun 𝔖 f ^ c :=
  rfl

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Monoid β] : Monoid (α →ᵤ β) := inferInstanceAs <| Monoid (α → β)

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Monoid β] : Monoid (α →ᵤ[𝔖] β) := inferInstanceAs <| Monoid (α → β)

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CommMonoid β] : CommMonoid (α →ᵤ β) := inferInstanceAs <| CommMonoid (α → β)

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CommMonoid β] : CommMonoid (α →ᵤ[𝔖] β) := inferInstanceAs <| CommMonoid (α → β)

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Group β] : Group (α →ᵤ β) := inferInstanceAs <| Group (α → β)

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Group β] : Group (α →ᵤ[𝔖] β) := inferInstanceAs <| Group (α → β)

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CommGroup β] : CommGroup (α →ᵤ β) := inferInstanceAs <| CommGroup (α → β)

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CommGroup β] : CommGroup (α →ᵤ[𝔖] β) := inferInstanceAs <| CommGroup (α → β)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {M N : Type*} [SMul M N] [SMul M β] [SMul N β] [IsScalarTower M N β] :
    IsScalarTower M N (α →ᵤ β) :=
  inferInstanceAs <| IsScalarTower M N (α → β)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {M N : Type*} [SMul M N] [SMul M β] [SMul N β] [IsScalarTower M N β] :
    IsScalarTower M N (α →ᵤ[𝔖] β) :=
  inferInstanceAs <| IsScalarTower M N (α → β)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {M N : Type*} [SMul M β] [SMul N β] [SMulCommClass M N β] :
    SMulCommClass M N (α →ᵤ β) :=
  inferInstanceAs <| SMulCommClass M N (α → β)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {M N : Type*} [SMul M β] [SMul N β] [SMulCommClass M N β] :
    SMulCommClass M N (α →ᵤ[𝔖] β) :=
  inferInstanceAs <| SMulCommClass M N (α → β)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {M : Type*} [Monoid M] [MulAction M β] : MulAction M (α →ᵤ β) :=
  inferInstanceAs <| MulAction M (α → β)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {M : Type*} [Monoid M] [MulAction M β] : MulAction M (α →ᵤ[𝔖] β) :=
  inferInstanceAs <| MulAction M (α → β)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {M : Type*} [Monoid M] [AddMonoid β] [DistribMulAction M β] :
    DistribMulAction M (α →ᵤ β) :=
  inferInstanceAs <| DistribMulAction M (α → β)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {M : Type*} [Monoid M] [AddMonoid β] [DistribMulAction M β] :
    DistribMulAction M (α →ᵤ[𝔖] β) :=
  inferInstanceAs <| DistribMulAction M (α → β)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Semiring R] [AddCommMonoid β] [Module R β] : Module R (α →ᵤ β) :=
  inferInstanceAs <| Module R (α → β)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Semiring R] [AddCommMonoid β] [Module R β] : Module R (α →ᵤ[𝔖] β) :=
  inferInstanceAs <| Module R (α → β)

end AlgebraicInstances

section Group

variable {α G ι : Type*} [Group G] {𝔖 : Set <| Set α} [UniformSpace G] [IsUniformGroup G]

/-- If `G` is a uniform group, then `α →ᵤ G` is a uniform group as well. -/
@[to_additive /-- If `G` is a uniform additive group,
then `α →ᵤ G` is a uniform additive group as well. -/]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsUniformGroup (α →ᵤ G) :=
  ⟨(-- Since `(/) : G × G → G` is uniformly continuous,
    -- `UniformFun.postcomp_uniformContinuous` tells us that
    -- `((/) ∘ —) : (α →ᵤ G × G) → (α →ᵤ G)` is uniformly continuous too. By precomposing with
    -- `UniformFun.uniformEquivProdArrow`, this gives that
    -- `(/) : (α →ᵤ G) × (α →ᵤ G) → (α →ᵤ G)` is also uniformly continuous
    UniformFun.postcomp_uniformContinuous uniformContinuous_div).comp
    UniformFun.uniformEquivProdArrow.symm.uniformContinuous⟩

@[to_additive]
/-
**UniformFun.hasBasis_nhds_one_of_basis** 是 Mathlib 中的一个定理，位于命名空间 `UniformFun`。
形式化陈述：∀ {α : Type u_1} {G : Type u_2} {ι : Type u_3} [inst : Group G] [inst_1 : 
UniformSpace G] [IsUniformGroup G]   {p : ι → Prop} {b : ι → Set G},   (nhds 1).
HasBasis p b → (nhds 1).HasBasis p fun i => {f | ∀ (x : α), UniformFun.toFun f x
 ∈ b i}
参数：nhds 1；nhds 1；x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `UniformFun.hasBasis_nhds_of_basis`：∀ (α : Type u_1) (β : Type u_2) {ι : 
Type u_4} [inst : UniformSpace β] (f : UniformFun α β) {p : ι → Prop}   {s : ι →
 Set (β × β)},   (unifo…
· 使用定理 `Filter.HasBasis.uniformity_of_nhds_one`：Filter.HasBasis.uniformity_of_nh
ds_one {ι} {p : ι -> Prop} {U : ι -> Set α} (h : (𝓝 (1 : α)).HasBasis p U) : (𝓤 
α).HasBasis p fun i => { x :…
-/
protected theorem UniformFun.hasBasis_nhds_one_of_basis {p : ι → Prop} {b : ι → Set G}
    (h : (𝓝 1 : Filter G).HasBasis p b) :
    (𝓝 1 : Filter (α →ᵤ G)).HasBasis p fun i => { f : α →ᵤ G | ∀ x, toFun f x ∈ b i } := by
  convert! UniformFun.hasBasis_nhds_of_basis α _ (1 : α →ᵤ G) h.uniformity_of_nhds_one
  simp

@[to_additive]
/-
**UniformFun.hasBasis_nhds_one** 是 Mathlib 中的一个定理，位于命名空间 `UniformFun`。
形式化陈述：∀ {α : Type u_1} {G : Type u_2} [inst : Group G] [inst_1 : UniformSpace G]
 [IsUniformGroup G],   (nhds 1).HasBasis (fun V => V ∈ nhds 1) fun V => {f | ∀ (
x : α), f x ∈ V}
参数：nhds 1；fun V => V ∈ nhds 1；x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformFun.hasBasis_nhds_one_of_basis`：∀ {α : Type u_1} {G : Type u_2} {
ι : Type u_3} [inst : Group G] [inst_1 : UniformSpace G] [IsUniformGroup G]   {p
 : ι → Prop} {b : ι → Set G…
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
-/
protected theorem UniformFun.hasBasis_nhds_one :
    (𝓝 1 : Filter (α →ᵤ G)).HasBasis (fun V : Set G => V ∈ (𝓝 1 : Filter G)) fun V =>
      { f : α → G | ∀ x, f x ∈ V } :=
  UniformFun.hasBasis_nhds_one_of_basis (basis_sets _)

/-- Let `𝔖 : Set (Set α)`. If `G` is a uniform group, then `α →ᵤ[𝔖] G` is a uniform group as
well. -/
@[to_additive /-- Let `𝔖 : Set (Set α)`. If `G` is a uniform additive group,
then `α →ᵤ[𝔖] G` is a uniform additive group as well. -/]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsUniformGroup (α →ᵤ[𝔖] G) :=
  ⟨(-- Since `(/) : G × G → G` is uniformly continuous,
    -- `UniformOnFun.postcomp_uniformContinuous` tells us that
    -- `((/) ∘ —) : (α →ᵤ[𝔖] G × G) → (α →ᵤ[𝔖] G)` is uniformly continuous too. By precomposing with
    -- `UniformOnFun.uniformEquivProdArrow`, this gives that
    -- `(/) : (α →ᵤ[𝔖] G) × (α →ᵤ[𝔖] G) → (α →ᵤ[𝔖] G)` is also uniformly continuous
    UniformOnFun.postcomp_uniformContinuous uniformContinuous_div).comp
    UniformOnFun.uniformEquivProdArrow.symm.uniformContinuous⟩

@[to_additive]
/-
**UniformOnFun.hasBasis_nhds_one_of_basis** 是 Mathlib 中的一个定理，位于命名空间 `UniformOnFu
n`。
形式化陈述：∀ {α : Type u_1} {G : Type u_2} {ι : Type u_3} [inst : Group G] [inst_1 : 
UniformSpace G] [IsUniformGroup G]   (𝔖 : Set (Set α)),   𝔖.Nonempty →     Direc
tedOn (fun x1 x2 => x1 ⊆ x2) 𝔖 →       ∀ {p : ι → Prop} {b : ι → Set G},        
 (nhds 1).HasBasis p b →           (nhds 1).HasBasis (fun Si => Si.1 ∈ 𝔖 ∧ p Si.
2) fun Si =>             {f | ∀ x ∈ Si.1, (UniformOnFun.toFun 𝔖) f x ∈ b Si.2}
参数：𝔖 : Set (Set α)；fun x1 x2 => x1 ⊆ x2；nhds 1；nhds 1；fun Si => Si.1 ∈ 𝔖 ∧ p Si.
2；UniformOnFun.toFun 𝔖。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `UniformOnFun.hasBasis_nhds_of_basis`：∀ (α : Type u_1) (β : Type u_2) {ι 
: Type u_4} [inst : UniformSpace β] (𝔖 : Set (Set α)) (f : UniformOnFun α β 𝔖), 
  𝔖.Nonempty →     Direct…
· 使用定理 `Filter.HasBasis.uniformity_of_nhds_one_swapped`：Filter.HasBasis.uniformi
ty_of_nhds_one_swapped {ι} {p : ι -> Prop} {U : ι -> Set α} (h : (𝓝 (1 : α)).Has
Basis p U) : (𝓤 α).HasBasis p fun i …
-/
protected theorem UniformOnFun.hasBasis_nhds_one_of_basis (𝔖 : Set <| Set α) (h𝔖₁ : 𝔖.Nonempty)
    (h𝔖₂ : DirectedOn (· ⊆ ·) 𝔖) {p : ι → Prop} {b : ι → Set G}
    (h : (𝓝 1 : Filter G).HasBasis p b) :
    (𝓝 1 : Filter (α →ᵤ[𝔖] G)).HasBasis (fun Si : Set α × ι => Si.1 ∈ 𝔖 ∧ p Si.2) fun Si =>
      { f : α →ᵤ[𝔖] G | ∀ x ∈ Si.1, toFun 𝔖 f x ∈ b Si.2 } := by
  convert!
    UniformOnFun.hasBasis_nhds_of_basis α _ 𝔖 (1 : α →ᵤ[𝔖] G) h𝔖₁ h𝔖₂ <|
      h.uniformity_of_nhds_one_swapped
  simp [UniformOnFun.gen]

@[to_additive]
/-
**UniformOnFun.hasBasis_nhds_one** 是 Mathlib 中的一个定理，位于命名空间 `UniformOnFun`。
形式化陈述：∀ {α : Type u_1} {G : Type u_2} [inst : Group G] [inst_1 : UniformSpace G]
 [IsUniformGroup G] (𝔖 : Set (Set α)),   𝔖.Nonempty →     DirectedOn (fun x1 x2 
=> x1 ⊆ x2) 𝔖 →       (nhds 1).HasBasis (fun SV => SV.1 ∈ 𝔖 ∧ SV.2 ∈ nhds 1) fun
 SV => {f | ∀ x ∈ SV.1, f x ∈ SV.2}
参数：𝔖 : Set (Set α)；fun x1 x2 => x1 ⊆ x2；nhds 1；fun SV => SV.1 ∈ 𝔖 ∧ SV.2 ∈ nhds 
1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformOnFun.hasBasis_nhds_one_of_basis`：∀ {α : Type u_1} {G : Type u_2}
 {ι : Type u_3} [inst : Group G] [inst_1 : UniformSpace G] [IsUniformGroup G]   
(𝔖 : Set (Set α)),   𝔖.Nonemp…
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
-/
protected theorem UniformOnFun.hasBasis_nhds_one (𝔖 : Set <| Set α) (h𝔖₁ : 𝔖.Nonempty)
    (h𝔖₂ : DirectedOn (· ⊆ ·) 𝔖) :
    (𝓝 1 : Filter (α →ᵤ[𝔖] G)).HasBasis
      (fun SV : Set α × Set G => SV.1 ∈ 𝔖 ∧ SV.2 ∈ (𝓝 1 : Filter G)) fun SV =>
      { f : α →ᵤ[𝔖] G | ∀ x ∈ SV.1, f x ∈ SV.2 } :=
  UniformOnFun.hasBasis_nhds_one_of_basis 𝔖 h𝔖₁ h𝔖₂ (basis_sets _)

@[to_additive (attr := simp)]
/-
**UniformOnFun.ofFun_prod** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：UniformOnFun.ofFun_prod {β : Type*} [CommMonoid β] {f : ι -> α -> β} (I : 
Finset ι) : ofFun 𝔖 (∏ i in I, f i) = ∏ i in I, ofFun 𝔖 (f i)
参数：I : Finset ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma UniformOnFun.ofFun_prod {β : Type*} [CommMonoid β] {f : ι → α → β} (I : Finset ι) :
    ofFun 𝔖 (∏ i ∈ I, f i) = ∏ i ∈ I, ofFun 𝔖 (f i) :=
  rfl

@[to_additive (attr := simp)]
/-
**UniformOnFun.toFun_prod** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：UniformOnFun.toFun_prod {β : Type*} [CommMonoid β] {f : ι -> α -> β} (I : 
Finset ι) : toFun 𝔖 (∏ i in I, f i) = ∏ i in I, toFun 𝔖 (f i)
参数：I : Finset ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma UniformOnFun.toFun_prod {β : Type*} [CommMonoid β] {f : ι → α → β} (I : Finset ι) :
    toFun 𝔖 (∏ i ∈ I, f i) = ∏ i ∈ I, toFun 𝔖 (f i) :=
  rfl

@[to_additive (attr := simp)]
/-
**UniformFun.ofFun_prod** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：UniformFun.ofFun_prod {β : Type*} [CommMonoid β] {f : ι -> α -> β} (I : Fi
nset ι) : ofFun (∏ i in I, f i) = ∏ i in I, ofFun (f i)
参数：I : Finset ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma UniformFun.ofFun_prod {β : Type*} [CommMonoid β] {f : ι → α → β} (I : Finset ι) :
    ofFun (∏ i ∈ I, f i) = ∏ i ∈ I, ofFun (f i) :=
  rfl

@[to_additive (attr := simp)]
/-
**UniformFun.toFun_prod** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：UniformFun.toFun_prod {β : Type*} [CommMonoid β] {f : ι -> α -> β} (I : Fi
nset ι) : toFun (∏ i in I, f i) = ∏ i in I, toFun (f i)
参数：I : Finset ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma UniformFun.toFun_prod {β : Type*} [CommMonoid β] {f : ι → α → β} (I : Finset ι) :
    toFun (∏ i ∈ I, f i) = ∏ i ∈ I, toFun (f i) :=
  rfl

end Group

section ConstSMul

variable (M α X : Type*) [SMul M X] [UniformSpace X] [UniformContinuousConstSMul M X]

/-
**UniformFun.uniformContinuousConstSMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：UniformFun.uniformContinuousConstSMul : UniformContinuousConstSMul M (α ->
ᵤ X) where uniformContinuous_const_smul c
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformFun.postcomp_uniformContinuous`：∀ {α : Type u_1} {β : Type u_2} {
γ : Type u_3} [inst : UniformSpace β] [inst_1 : UniformSpace γ] {f : γ → β},   U
niformContinuous f → Unifor…
· 使用定理 `UniformContinuousConstSMul.uniformContinuous_const_smul`：∀ {M : Type v} 
{X : Type x} {inst : UniformSpace X} {inst_1 : SMul M X} [self : UniformContinuo
usConstSMul M X] (c : M),   UniformContinuous…
-/
instance UniformFun.uniformContinuousConstSMul :
    UniformContinuousConstSMul M (α →ᵤ X) where
  uniformContinuous_const_smul c := UniformFun.postcomp_uniformContinuous <|
    uniformContinuous_const_smul c
/-
**UniformFunOn.uniformContinuousConstSMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：UniformFunOn.uniformContinuousConstSMul {𝔖 : Set (Set α)} : UniformContinu
ousConstSMul M (α ->ᵤ[𝔖] X) where uniformContinuous_const_smul c
参数：Set α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformOnFun.postcomp_uniformContinuous`：∀ {α : Type u_1} {β : Type u_2}
 {γ : Type u_3} [inst : UniformSpace β] {𝔖 : Set (Set α)} [inst_1 : UniformSpace
 γ]   {f : γ → β},   UniformC…
· 使用定理 `UniformContinuousConstSMul.uniformContinuous_const_smul`：∀ {M : Type v} 
{X : Type x} {inst : UniformSpace X} {inst_1 : SMul M X} [self : UniformContinuo
usConstSMul M X] (c : M),   UniformContinuous…
-/
instance UniformFunOn.uniformContinuousConstSMul {𝔖 : Set (Set α)} :
    UniformContinuousConstSMul M (α →ᵤ[𝔖] X) where
  uniformContinuous_const_smul c := UniformOnFun.postcomp_uniformContinuous <|
    uniformContinuous_const_smul c

end ConstSMul

