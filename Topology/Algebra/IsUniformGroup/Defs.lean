/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl, Anatole Dedecker
-/
module

public import Mathlib.Topology.UniformSpace.Basic
public import Mathlib.Topology.Algebra.Group.Basic

/-!
# Uniform structure on topological groups

Given a topological group `G`, one can naturally build two uniform structures
(the "left" and "right" ones) on `G` inducing its topology.
This file defines typeclasses for groups equipped with either of these uniform structures, as well
as a separate typeclass for the (very common) case where the given uniform structure
coincides with **both** the left and right uniform structures.

## Main declarations

* `IsRightUniformGroup` and `IsRightUniformAddGroup`: Multiplicative and additive topological groups
  endowed with the associated right uniform structure. This means that two points `x` and `y`
  are close precisely when `y * x⁻¹` is close to `1` / `y + (-x)` close to `0`.
* `IsLeftUniformGroup` and `IsLeftUniformAddGroup`: Multiplicative and additive topological groups
  endowed with the associated left uniform structure. This means that two points `x` and `y`
  are close precisely when `x⁻¹ * y` is close to `1` / `(-x) + y` close to `0`.
* `IsUniformGroup` and `IsUniformAddGroup`: Multiplicative and additive uniform groups,
  i.e., groups with uniformly continuous `(*)` and `(⁻¹)` / `(+)` and `(-)`. This corresponds
  to the conjunction of the two conditions above, although this result is not in Mathlib yet.

## Main results

* `IsTopologicalAddGroup.rightUniformSpace` and `comm_topologicalAddGroup_is_uniform` can be used
  to construct a canonical uniformity for a topological additive group.

See `Mathlib/Topology/Algebra/IsUniformGroup/Basic.lean` for further results.

## Implementation Notes

Since the most frequent use case is `G` being a commutative additive groups, `Mathlib` originally
did essentially all the theory under the assumption `IsUniformGroup G`.
For this reason, you may find results stated under this assumption even though they may hold
under either `IsRightUniformGroup G` or `IsLeftUniformGroup G`.
-/

@[expose] public section

assert_not_exists Cauchy

noncomputable section

open Uniformity Topology Filter Pointwise

section LeftRight

open Filter Set

variable {G Gₗ Gᵣ Hₗ Hᵣ X : Type*}

/-- A **right-uniform additive group** is a topological additive group endowed with the associated
right uniform structure: the uniformity filter `𝓤 G` is the inverse image of `𝓝 0` by the map
`(x, y) ↦ y + (-x)`.

In other words, we declare that two points `x` and `y` are infinitely close
precisely when `y + (-x)` is infinitely close to `0`. -/
/-
**IsRightUniformAddGroup** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(G : Type u_7) → [UniformSpace G] → [AddGroup G] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A **right-uniform additive group** is a topological additive group endowed with 
the associated
right uniform structure: the uniformity filter `𝓤 G` is the inverse image of `𝓝 
0` by the map
`(x, y) ↦ y + (-x)`.

In other words, we declare that two points `x` and `y` are infinitely close
precisely when `y + (-x)` is infinitely close to `0`.
-/
class IsRightUniformAddGroup (G : Type*) [UniformSpace G] [AddGroup G] : Prop
    extends IsTopologicalAddGroup G where
  uniformity_eq :
    𝓤 G = comap (fun x : G × G ↦ x.2 + (-x.1)) (𝓝 0)

/-- A **right-uniform group** is a topological group endowed with the associated
right uniform structure: the uniformity filter `𝓤 G` is the inverse image of `𝓝 1` by the map
`(x, y) ↦ y * x⁻¹`.

In other words, we declare that two points `x` and `y` are infinitely close
precisely when `y * x⁻¹` is infinitely close to `1`. -/
@[to_additive]
/-
**IsRightUniformGroup** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(G : Type u_7) → [UniformSpace G] → [Group G] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A **right-uniform group** is a topological group endowed with the associated
right uniform structure: the uniformity filter `𝓤 G` is the inverse image of `𝓝 
1` by the map
`(x, y) ↦ y * x⁻¹`.

In other words, we declare that two points `x` and `y` are infinitely close
precisely when `y * x⁻¹` is infinitely close to `1`.
-/
class IsRightUniformGroup (G : Type*) [UniformSpace G] [Group G] : Prop
    extends IsTopologicalGroup G where
  uniformity_eq :
    𝓤 G = comap (fun x : G × G ↦ x.2 * x.1⁻¹) (𝓝 1)

/-- A **left-uniform additive group** is a topological additive group endowed with the associated
left uniform structure: the uniformity filter `𝓤 G` is the inverse image of `𝓝 0` by the map
`(x, y) ↦ (-x) + y`.

In other words, we declare that two points `x` and `y` are infinitely close
precisely when `(-x) + y` is infinitely close to `0`. -/
/-
**IsLeftUniformAddGroup** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(G : Type u_7) → [UniformSpace G] → [AddGroup G] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A **left-uniform additive group** is a topological additive group endowed with t
he associated
left uniform structure: the uniformity filter `𝓤 G` is the inverse image of `𝓝 0
` by the map
`(x, y) ↦ (-x) + y`.

In other words, we declare that two points `x` and `y` are infinitely close
precisely when `(-x) + y` is infinitely close to `0`.
-/
class IsLeftUniformAddGroup (G : Type*) [UniformSpace G] [AddGroup G] : Prop
    extends IsTopologicalAddGroup G where
  uniformity_eq :
    𝓤 G = comap (fun x : G × G ↦ (-x.1) + x.2) (𝓝 0)

/-- A **left-uniform group** is a topological group endowed with the associated
left uniform structure: the uniformity filter `𝓤 G` is the inverse image of `𝓝 1` by the map
`(x, y) ↦ x⁻¹ * y`.

In other words, we declare that two points `x` and `y` are infinitely close
precisely when `x⁻¹ * y` is infinitely close to `1`. -/
@[to_additive]
/-
**IsLeftUniformGroup** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(G : Type u_7) → [UniformSpace G] → [Group G] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A **left-uniform group** is a topological group endowed with the associated
left uniform structure: the uniformity filter `𝓤 G` is the inverse image of `𝓝 1
` by the map
`(x, y) ↦ x⁻¹ * y`.

In other words, we declare that two points `x` and `y` are infinitely close
precisely when `x⁻¹ * y` is infinitely close to `1`.
-/
class IsLeftUniformGroup (G : Type*) [UniformSpace G] [Group G] : Prop
    extends IsTopologicalGroup G where
  uniformity_eq :
    𝓤 G = comap (fun x : G × G ↦ x.1⁻¹ * x.2) (𝓝 1)

attribute [instance 10] IsRightUniformAddGroup.toIsTopologicalAddGroup
attribute [instance 10] IsRightUniformGroup.toIsTopologicalGroup
attribute [instance 10] IsLeftUniformAddGroup.toIsTopologicalAddGroup
attribute [instance 10] IsLeftUniformGroup.toIsTopologicalGroup

variable [UniformSpace Gₗ] [UniformSpace Gᵣ] [Group Gₗ] [Group Gᵣ]
variable [UniformSpace Hₗ] [UniformSpace Hᵣ] [Group Hₗ] [Group Hᵣ]
variable [IsLeftUniformGroup Gₗ] [IsRightUniformGroup Gᵣ]
variable [IsLeftUniformGroup Hₗ] [IsRightUniformGroup Hᵣ]
variable [UniformSpace X]

variable (Gₗ Gᵣ)

@[to_additive]
/-
**uniformity_eq_comap_mul_inv_nhds_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：uniformity_eq_comap_mul_inv_nhds_one : 𝓤 Gᵣ = comap (fun x : Gᵣ × Gᵣ => x.
2 * x.1⁻¹) (𝓝 1)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRightUniformGroup.uniformity_eq`：∀ {G : Type u_7} {inst : UniformSpace
 G} {inst_1 : Group G} [self : IsRightUniformGroup G],   uniformity G = Filter.c
omap (fun x => x.2 * x.…
-/
lemma uniformity_eq_comap_mul_inv_nhds_one :
    𝓤 Gᵣ = comap (fun x : Gᵣ × Gᵣ ↦ x.2 * x.1⁻¹) (𝓝 1) :=
  IsRightUniformGroup.uniformity_eq

@[to_additive]
/-
**uniformity_eq_comap_inv_mul_nhds_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：uniformity_eq_comap_inv_mul_nhds_one : 𝓤 Gₗ = comap (fun x : Gₗ × Gₗ => x.
1⁻¹ * x.2) (𝓝 1)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLeftUniformGroup.uniformity_eq`：∀ {G : Type u_7} {inst : UniformSpace 
G} {inst_1 : Group G} [self : IsLeftUniformGroup G],   uniformity G = Filter.com
ap (fun x => x.1⁻¹ * x…
-/
lemma uniformity_eq_comap_inv_mul_nhds_one :
    𝓤 Gₗ = comap (fun x : Gₗ × Gₗ ↦ x.1⁻¹ * x.2) (𝓝 1) :=
  IsLeftUniformGroup.uniformity_eq

@[to_additive]
/-
**uniformity_eq_comap_mul_inv_nhds_one_swapped** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：uniformity_eq_comap_mul_inv_nhds_one_swapped : 𝓤 Gᵣ = comap (fun x : Gᵣ × 
Gᵣ => x.1 * x.2⁻¹) (𝓝 1)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `comap_swap_uniformity`：comap_swap_uniformity : comap (@Prod.swap α α) (𝓤
 α) = 𝓤 α
· 使用引理 `uniformity_eq_comap_mul_inv_nhds_one`：uniformity_eq_comap_mul_inv_nhds_o
ne : 𝓤 Gᵣ = comap (fun x : Gᵣ × Gᵣ => x.2 * x.1⁻¹) (𝓝 1)
· 使用定理 `Filter.comap_comap`：comap_comap {m : γ -> β} {n : β -> α} : comap m (com
ap n f) = comap (n ∘ m) f
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma uniformity_eq_comap_mul_inv_nhds_one_swapped :
    𝓤 Gᵣ = comap (fun x : Gᵣ × Gᵣ ↦ x.1 * x.2⁻¹) (𝓝 1) := by
  rw [← comap_swap_uniformity, uniformity_eq_comap_mul_inv_nhds_one, comap_comap, Function.comp_def]
  simp

@[to_additive]
/-
**uniformity_eq_comap_inv_mul_nhds_one_swapped** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：uniformity_eq_comap_inv_mul_nhds_one_swapped : 𝓤 Gₗ = comap (fun x : Gₗ × 
Gₗ => x.2⁻¹ * x.1) (𝓝 1)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `comap_swap_uniformity`：comap_swap_uniformity : comap (@Prod.swap α α) (𝓤
 α) = 𝓤 α
· 使用引理 `uniformity_eq_comap_inv_mul_nhds_one`：uniformity_eq_comap_inv_mul_nhds_o
ne : 𝓤 Gₗ = comap (fun x : Gₗ × Gₗ => x.1⁻¹ * x.2) (𝓝 1)
· 使用定理 `Filter.comap_comap`：comap_comap {m : γ -> β} {n : β -> α} : comap m (com
ap n f) = comap (n ∘ m) f
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma uniformity_eq_comap_inv_mul_nhds_one_swapped :
    𝓤 Gₗ = comap (fun x : Gₗ × Gₗ ↦ x.2⁻¹ * x.1) (𝓝 1) := by
  rw [← comap_swap_uniformity, uniformity_eq_comap_inv_mul_nhds_one, comap_comap, Function.comp_def]
  simp

@[to_additive]
/-
**uniformity_eq_comap_nhds_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformity_eq_comap_nhds_one : 𝓤 Gᵣ = comap (fun x : Gᵣ × Gᵣ => x.2 / x.1)
 (𝓝 1)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用引理 `uniformity_eq_comap_mul_inv_nhds_one`：uniformity_eq_comap_mul_inv_nhds_o
ne : 𝓤 Gᵣ = comap (fun x : Gᵣ × Gᵣ => x.2 * x.1⁻¹) (𝓝 1)
-/
theorem uniformity_eq_comap_nhds_one : 𝓤 Gᵣ = comap (fun x : Gᵣ × Gᵣ => x.2 / x.1) (𝓝 1) := by
  simp_rw [div_eq_mul_inv]
  exact uniformity_eq_comap_mul_inv_nhds_one Gᵣ

@[to_additive]
/-
**uniformity_eq_comap_nhds_one_swapped** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformity_eq_comap_nhds_one_swapped : 𝓤 Gᵣ = comap (fun x : Gᵣ × Gᵣ => x.
1 / x.2) (𝓝 1)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `comap_swap_uniformity`：comap_swap_uniformity : comap (@Prod.swap α α) (𝓤
 α) = 𝓤 α
· 使用定理 `uniformity_eq_comap_nhds_one`：uniformity_eq_comap_nhds_one : 𝓤 Gᵣ = coma
p (fun x : Gᵣ × Gᵣ => x.2 / x.1) (𝓝 1)
· 使用定理 `Filter.comap_comap`：comap_comap {m : γ -> β} {n : β -> α} : comap m (com
ap n f) = comap (n ∘ m) f
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem uniformity_eq_comap_nhds_one_swapped :
    𝓤 Gᵣ = comap (fun x : Gᵣ × Gᵣ => x.1 / x.2) (𝓝 1) := by
  rw [← comap_swap_uniformity, uniformity_eq_comap_nhds_one, comap_comap, Function.comp_def]
  simp

end LeftRight

section IsUniformGroup

open Filter Set

variable {α : Type*} {β : Type*}

/-- A uniform group is a group in which multiplication and inversion are uniformly continuous.

`IsUniformGroup G` is equivalent to the fact that `G` is a topological group, and the uniformity
coincides with **both** the associated left and right uniformities
(see `IsUniformGroup.isRightUniformGroup`, `IsUniformGroup.isLeftUniformGroup` and
`IsUniformGroup.of_left_right`).

Since there are topological groups where these two uniformities do **not** coincide,
not all topological groups admit a uniform group structure in this sense. This is however the
case for commutative groups, which are the main motivation for the existence of this
typeclass. -/
/-
**IsUniformGroup** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_3) → [UniformSpace α] → [Group α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A uniform group is a group in which multiplication and inversion are uniformly c
ontinuous.

`IsUniformGroup G` is equivalent to the fact that `G` is a topological group, an
d the uniformity
coincides with **both** the associated left and right uniformities
(see `IsUniformGroup.isRightUniformGroup`, `IsUniformGroup.isLeftUniformGroup` a
nd
`IsUniformGroup.of_left_right`).

Since there are topological groups where these two uniformities do **not** coinc
ide,
not all topological groups admit a uniform group structure in this sense. This i
s however the
case for commutative groups, which are the main motivation for the existence of 
this
typeclass.
-/
class IsUniformGroup (α : Type*) [UniformSpace α] [Group α] : Prop where
  uniformContinuous_div : UniformContinuous fun p : α × α => p.1 / p.2

/-- A uniform additive group is an additive group in which addition and negation are
uniformly continuous.

`IsUniformAddGroup G` is equivalent to the fact that `G` is a topological additive group, and the
uniformity coincides with **both** the associated left and right uniformities
(see `IsUniformAddGroup.isRightUniformAddGroup`, `IsUniformAddGroup.isLeftUniformAddGroup` and
`IsUniformAddGroup.of_left_right`).

Since there are topological groups where these two uniformities do **not** coincide,
not all topological groups admit a uniform group structure in this sense. This is however the
case for commutative groups, which are the main motivation for the existence of this
typeclass. -/
/-
**IsUniformAddGroup** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_3) → [UniformSpace α] → [AddGroup α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A uniform additive group is an additive group in which addition and negation are
uniformly continuous.

`IsUniformAddGroup G` is equivalent to the fact that `G` is a topological additi
ve group, and the
uniformity coincides with **both** the associated left and right uniformities
(see `IsUniformAddGroup.isRightUniformAddGroup`, `IsUniformAddGroup.isLeftUnifor
mAddGroup` and
`IsUniformAddGroup.of_left_right`).

Since there are topological groups where these two uniformities do **not** coinc
ide,
not all topological groups admit a uniform group structure in this sense. This i
s however the
case for commutative groups, which are the main motivation for the existence of 
this
typeclass.
-/
class IsUniformAddGroup (α : Type*) [UniformSpace α] [AddGroup α] : Prop where
  uniformContinuous_sub : UniformContinuous fun p : α × α => p.1 - p.2

attribute [to_additive] IsUniformGroup

@[to_additive]
/-
**IsUniformGroup.mk'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUniformGroup.mk' {α} [UniformSpace α] [Group α] (h₁ : UniformContinuous 
fun p : α × α => p.1 * p.2) (h₂ : UniformContinuous fun p : α => p⁻¹) : IsUnifor
mGroup α
参数：h₁ : UniformContinuous fun p : α × α => p.1 * p.2；h₂ : UniformContinuous fun 
p : α => p⁻¹。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `UniformContinuous.comp`：∀ {α : Type ua} {β : Type ub} {γ : Type uc} [ins
t : UniformSpace α] [inst_1 : UniformSpace β] [inst_2 : UniformSpace γ]   {g : β
 → γ} {f : α…
· 使用定理 `UniformContinuous.prodMk`：UniformContinuous.prodMk {f₁ : α -> β} {f₂ : α
 -> γ} (h₁ : UniformContinuous f₁) (h₂ : UniformContinuous f₂) : UniformContinuo
us fun a => (f…
· 使用定理 `uniformContinuous_fst`：uniformContinuous_fst [UniformSpace α] [UniformSp
ace β] : UniformContinuous fun p : α × β => p.1
· 使用定理 `uniformContinuous_snd`：uniformContinuous_snd [UniformSpace α] [UniformSp
ace β] : UniformContinuous fun p : α × β => p.2
-/
theorem IsUniformGroup.mk' {α} [UniformSpace α] [Group α]
    (h₁ : UniformContinuous fun p : α × α => p.1 * p.2) (h₂ : UniformContinuous fun p : α => p⁻¹) :
    IsUniformGroup α :=
  ⟨by simpa only [div_eq_mul_inv] using!
    h₁.comp (uniformContinuous_fst.prodMk (h₂.comp uniformContinuous_snd))⟩

variable [UniformSpace α] [Group α] [IsUniformGroup α]

@[to_additive]
/-
**uniformContinuous_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformContinuous_div : UniformContinuous fun p : α × α => p.1 / p.2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformGroup.uniformContinuous_div`：∀ {α : Type u_3} {inst : UniformSp
ace α} {inst_1 : Group α} [self : IsUniformGroup α],   UniformContinuous fun p =
> p.1 / p.2
-/
theorem uniformContinuous_div : UniformContinuous fun p : α × α => p.1 / p.2 :=
  IsUniformGroup.uniformContinuous_div

@[to_additive (attr := fun_prop)]
/-
**UniformContinuous.div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformContinuous.div [UniformSpace β] {f : β -> α} {g : β -> α} (hf : Uni
formContinuous f) (hg : UniformContinuous g) : UniformContinuous fun x => f x / 
g x
参数：hf : UniformContinuous f；hg : UniformContinuous g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.comp`：∀ {α : Type ua} {β : Type ub} {γ : Type uc} [ins
t : UniformSpace α] [inst_1 : UniformSpace β] [inst_2 : UniformSpace γ]   {g : β
 → γ} {f : α…
· 使用定理 `uniformContinuous_div`：uniformContinuous_div : UniformContinuous fun p :
 α × α => p.1 / p.2
· 使用定理 `UniformContinuous.prodMk`：UniformContinuous.prodMk {f₁ : α -> β} {f₂ : α
 -> γ} (h₁ : UniformContinuous f₁) (h₂ : UniformContinuous f₂) : UniformContinuo
us fun a => (f…
-/
theorem UniformContinuous.div [UniformSpace β] {f : β → α} {g : β → α} (hf : UniformContinuous f)
    (hg : UniformContinuous g) : UniformContinuous fun x => f x / g x :=
  uniformContinuous_div.comp (hf.prodMk hg)

@[to_additive (attr := fun_prop)]
/-
**UniformContinuous.inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformContinuous.inv [UniformSpace β] {f : β -> α} (hf : UniformContinuou
s f) : UniformContinuous fun x => (f x)⁻¹
参数：hf : UniformContinuous f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.div`：UniformContinuous.div [UniformSpace β] {f : β -> 
α} {g : β -> α} (hf : UniformContinuous f) (hg : UniformContinuous g) : UniformC
ontinuous f…
· 使用定理 `uniformContinuous_const`：uniformContinuous_const {b : β} : UniformContin
uous fun _ : α => b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
-/
theorem UniformContinuous.inv [UniformSpace β] {f : β → α} (hf : UniformContinuous f) :
    UniformContinuous fun x => (f x)⁻¹ := by
  have : UniformContinuous fun x => 1 / f x := uniformContinuous_const.div hf
  simp_all

@[to_additive]
/-
**uniformContinuous_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformContinuous_inv : UniformContinuous fun x : α => x⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.inv`：UniformContinuous.inv [UniformSpace β] {f : β -> 
α} (hf : UniformContinuous f) : UniformContinuous fun x => (f x)⁻¹
· 使用定理 `uniformContinuous_id`：uniformContinuous_id : UniformContinuous (@id α)
-/
theorem uniformContinuous_inv : UniformContinuous fun x : α => x⁻¹ :=
  uniformContinuous_id.inv

@[to_additive (attr := fun_prop)]
/-
**UniformContinuous.mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformContinuous.mul [UniformSpace β] {f : β -> α} {g : β -> α} (hf : Uni
formContinuous f) (hg : UniformContinuous g) : UniformContinuous fun x => f x * 
g x
参数：hf : UniformContinuous f；hg : UniformContinuous g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.div`：UniformContinuous.div [UniformSpace β] {f : β -> 
α} {g : β -> α} (hf : UniformContinuous f) (hg : UniformContinuous g) : UniformC
ontinuous f…
· 使用定理 `UniformContinuous.inv`：UniformContinuous.inv [UniformSpace β] {f : β -> 
α} (hf : UniformContinuous f) : UniformContinuous fun x => (f x)⁻¹
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_inv_eq_mul`：div_inv_eq_mul : a / b⁻¹ = a * b
-/
theorem UniformContinuous.mul [UniformSpace β] {f : β → α} {g : β → α} (hf : UniformContinuous f)
    (hg : UniformContinuous g) : UniformContinuous fun x => f x * g x := by
  have : UniformContinuous fun x => f x / (g x)⁻¹ := hf.div hg.inv
  simp_all

@[to_additive]
/-
**Finset.uniformContinuous_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.uniformContinuous_prod {α β ι : Type*} [UniformSpace α] [CommGroup 
α] [IsUniformGroup α] [UniformSpace β] {f : ι -> β -> α} (s : Finset ι) (h : for
all i in s, UniformContinuous (f i)) : UniformContinuous (∏ i in s, f i ·)
参数：s : Finset ι；h : forall i in s, UniformContinuous (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction`：∀ {α : Type u_3} {motive : Finset α → Prop},   mo
tive ∅ → (∀ (a : α) (s : Finset α) (h : a ∉ s), motive s → motive (Finset.cons a
 s h)) → ∀ …
· 使用定理 `uniformContinuous_const`：uniformContinuous_const {b : β} : UniformContin
uous fun _ : α => b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.prod_cons`：prod_cons (h : a ∉ s) : ∏ x in cons a s h, f x = f a *
 ∏ x in s, f x
· 使用定理 `UniformContinuous.mul`：UniformContinuous.mul [UniformSpace β] {f : β -> 
α} {g : β -> α} (hf : UniformContinuous f) (hg : UniformContinuous g) : UniformC
ontinuous f…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Finset.uniformContinuous_prod {α β ι : Type*} [UniformSpace α] [CommGroup α]
    [IsUniformGroup α] [UniformSpace β] {f : ι → β → α} (s : Finset ι)
    (h : ∀ i ∈ s, UniformContinuous (f i)) :
    UniformContinuous (∏ i ∈ s, f i ·) := by
  induction s using Finset.cons_induction with
  | empty => simpa using uniformContinuous_const
  | cons a s ha ih =>
    simp_rw [Finset.mem_cons, forall_eq_or_imp] at h
    simpa [Finset.prod_cons] using h.1.mul (ih h.2)

@[to_additive]
/-
**uniformContinuous_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformContinuous_mul : UniformContinuous fun p : α × α => p.1 * p.2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.mul`：UniformContinuous.mul [UniformSpace β] {f : β -> 
α} {g : β -> α} (hf : UniformContinuous f) (hg : UniformContinuous g) : UniformC
ontinuous f…
· 使用定理 `uniformContinuous_fst`：uniformContinuous_fst [UniformSpace α] [UniformSp
ace β] : UniformContinuous fun p : α × β => p.1
· 使用定理 `uniformContinuous_snd`：uniformContinuous_snd [UniformSpace α] [UniformSp
ace β] : UniformContinuous fun p : α × β => p.2
-/
theorem uniformContinuous_mul : UniformContinuous fun p : α × α => p.1 * p.2 :=
  uniformContinuous_fst.mul uniformContinuous_snd

@[to_additive]
/-
**UniformContinuous.mul_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformContinuous.mul_const [UniformSpace β] {f : β -> α} (hf : UniformCon
tinuous f) (a : α) : UniformContinuous fun x => f x * a
参数：hf : UniformContinuous f；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.mul`：UniformContinuous.mul [UniformSpace β] {f : β -> 
α} {g : β -> α} (hf : UniformContinuous f) (hg : UniformContinuous g) : UniformC
ontinuous f…
· 使用定理 `uniformContinuous_const`：uniformContinuous_const {b : β} : UniformContin
uous fun _ : α => b
-/
theorem UniformContinuous.mul_const [UniformSpace β] {f : β → α} (hf : UniformContinuous f)
    (a : α) : UniformContinuous fun x ↦ f x * a :=
  hf.mul uniformContinuous_const

@[to_additive]
/-
**UniformContinuous.const_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformContinuous.const_mul [UniformSpace β] {f : β -> α} (hf : UniformCon
tinuous f) (a : α) : UniformContinuous fun x => a * f x
参数：hf : UniformContinuous f；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.mul`：UniformContinuous.mul [UniformSpace β] {f : β -> 
α} {g : β -> α} (hf : UniformContinuous f) (hg : UniformContinuous g) : UniformC
ontinuous f…
· 使用定理 `uniformContinuous_const`：uniformContinuous_const {b : β} : UniformContin
uous fun _ : α => b
-/
theorem UniformContinuous.const_mul [UniformSpace β] {f : β → α} (hf : UniformContinuous f)
    (a : α) : UniformContinuous fun x ↦ a * f x :=
  uniformContinuous_const.mul hf

@[to_additive]
/-
**uniformContinuous_mul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformContinuous_mul_left (a : α) : UniformContinuous fun b : α => a * b
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.const_mul`：UniformContinuous.const_mul [UniformSpace β
] {f : β -> α} (hf : UniformContinuous f) (a : α) : UniformContinuous fun x => a
 * f x
· 使用定理 `uniformContinuous_id`：uniformContinuous_id : UniformContinuous (@id α)
-/
theorem uniformContinuous_mul_left (a : α) : UniformContinuous fun b : α => a * b :=
  uniformContinuous_id.const_mul _

@[to_additive]
/-
**uniformContinuous_mul_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformContinuous_mul_right (a : α) : UniformContinuous fun b : α => b * a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.mul_const`：UniformContinuous.mul_const [UniformSpace β
] {f : β -> α} (hf : UniformContinuous f) (a : α) : UniformContinuous fun x => f
 x * a
· 使用定理 `uniformContinuous_id`：uniformContinuous_id : UniformContinuous (@id α)
-/
theorem uniformContinuous_mul_right (a : α) : UniformContinuous fun b : α => b * a :=
  uniformContinuous_id.mul_const _

@[to_additive]
/-
**UniformContinuous.div_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformContinuous.div_const [UniformSpace β] {f : β -> α} (hf : UniformCon
tinuous f) (a : α) : UniformContinuous fun x => f x / a
参数：hf : UniformContinuous f；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.div`：UniformContinuous.div [UniformSpace β] {f : β -> 
α} {g : β -> α} (hf : UniformContinuous f) (hg : UniformContinuous g) : UniformC
ontinuous f…
· 使用定理 `uniformContinuous_const`：uniformContinuous_const {b : β} : UniformContin
uous fun _ : α => b
-/
theorem UniformContinuous.div_const [UniformSpace β] {f : β → α} (hf : UniformContinuous f)
    (a : α) : UniformContinuous fun x ↦ f x / a :=
  hf.div uniformContinuous_const

@[to_additive]
/-
**uniformContinuous_div_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformContinuous_div_const (a : α) : UniformContinuous fun b : α => b / a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.div_const`：UniformContinuous.div_const [UniformSpace β
] {f : β -> α} (hf : UniformContinuous f) (a : α) : UniformContinuous fun x => f
 x / a
· 使用定理 `uniformContinuous_id`：uniformContinuous_id : UniformContinuous (@id α)
-/
theorem uniformContinuous_div_const (a : α) : UniformContinuous fun b : α => b / a :=
  uniformContinuous_id.div_const _

@[to_additive]
/-
**Filter.Tendsto.uniformity_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.uniformity_mul {ι : Type*} {f g : ι -> α × α} {l : Filter ι
} (hf : Tendsto f l (𝓤 α)) (hg : Tendsto g l (𝓤 α)) : Tendsto (f * g) l (𝓤 α)
参数：hf : Tendsto f l (𝓤 α)；hg : Tendsto g l (𝓤 α)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `uniformity_prod_eq_prod`：uniformity_prod_eq_prod [UniformSpace α] [Unifo
rmSpace β] : 𝓤 (α × β) = map (fun p : (α × α) × β × β => ((p.1.1, p.2.1), (p.1.2
, p.2.2))) (𝓤…
· 使用定理 `uniformContinuous_mul`：uniformContinuous_mul : UniformContinuous fun p :
 α × α => p.1 * p.2
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Filter.Tendsto.prodMk`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f
 : Filter α} {g : Filter β} {h : Filter γ} {m₁ : α → β} {m₂ : α → γ},   Filter.T
endsto m₁ f…
-/
theorem Filter.Tendsto.uniformity_mul {ι : Type*} {f g : ι → α × α} {l : Filter ι}
    (hf : Tendsto f l (𝓤 α)) (hg : Tendsto g l (𝓤 α)) :
    Tendsto (f * g) l (𝓤 α) :=
  have : Tendsto (fun (p : (α × α) × (α × α)) ↦ p.1 * p.2) (𝓤 α ×ˢ 𝓤 α) (𝓤 α) := by
    simpa [UniformContinuous, uniformity_prod_eq_prod] using! uniformContinuous_mul (α := α)
  this.comp (hf.prodMk hg)

@[to_additive]
/-
**Filter.Tendsto.uniformity_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.uniformity_inv {ι : Type*} {f : ι -> α × α} {l : Filter ι} 
(hf : Tendsto f l (𝓤 α)) : Tendsto (f⁻¹) l (𝓤 α)
参数：hf : Tendsto f l (𝓤 α)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `uniformContinuous_inv`：uniformContinuous_inv : UniformContinuous fun x :
 α => x⁻¹
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
-/
theorem Filter.Tendsto.uniformity_inv {ι : Type*} {f : ι → α × α} {l : Filter ι}
    (hf : Tendsto f l (𝓤 α)) :
    Tendsto (f⁻¹) l (𝓤 α) :=
  have : Tendsto (· ⁻¹) (𝓤 α) (𝓤 α) := uniformContinuous_inv
  this.comp hf

@[to_additive]
/-
**Filter.Tendsto.uniformity_inv_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.uniformity_inv_iff {ι : Type*} {f : ι -> α × α} {l : Filter
 ι} : Tendsto (f⁻¹) l (𝓤 α) ↔ Tendsto f l (𝓤 α)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.uniformity_inv`：Filter.Tendsto.uniformity_inv {ι : Type*}
 {f : ι -> α × α} {l : Filter ι} (hf : Tendsto f l (𝓤 α)) : Tendsto (f⁻¹) l (𝓤 α
)
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
-/
theorem Filter.Tendsto.uniformity_inv_iff {ι : Type*} {f : ι → α × α} {l : Filter ι} :
    Tendsto (f⁻¹) l (𝓤 α) ↔ Tendsto f l (𝓤 α) :=
  ⟨fun H ↦ inv_inv f ▸ H.uniformity_inv, Filter.Tendsto.uniformity_inv⟩

@[to_additive]
/-
**Filter.Tendsto.uniformity_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.uniformity_div {ι : Type*} {f g : ι -> α × α} {l : Filter ι
} (hf : Tendsto f l (𝓤 α)) (hg : Tendsto g l (𝓤 α)) : Tendsto (f / g) l (𝓤 α)
参数：hf : Tendsto f l (𝓤 α)；hg : Tendsto g l (𝓤 α)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Filter.Tendsto.uniformity_mul`：Filter.Tendsto.uniformity_mul {ι : Type*}
 {f g : ι -> α × α} {l : Filter ι} (hf : Tendsto f l (𝓤 α)) (hg : Tendsto g l (𝓤
 α)) : Tendsto (f *…
· 使用定理 `Filter.Tendsto.uniformity_inv`：Filter.Tendsto.uniformity_inv {ι : Type*}
 {f : ι -> α × α} {l : Filter ι} (hf : Tendsto f l (𝓤 α)) : Tendsto (f⁻¹) l (𝓤 α
)
-/
theorem Filter.Tendsto.uniformity_div {ι : Type*} {f g : ι → α × α} {l : Filter ι}
    (hf : Tendsto f l (𝓤 α)) (hg : Tendsto g l (𝓤 α)) :
    Tendsto (f / g) l (𝓤 α) := by
  rw [div_eq_mul_inv]
  exact hf.uniformity_mul hg.uniformity_inv

/-- If `f : ι → G × G` converges to the uniformity, then any `g : ι → G × G` converges to the
uniformity iff `f * g` does. This is often useful when `f` is valued in the diagonal,
in which case its convergence is automatic. -/
@[to_additive /-- If `f : ι → G × G` converges to the uniformity, then any `g : ι → G × G`
converges to the uniformity iff `f + g` does. This is often useful when `f` is valued in the
diagonal, in which case its convergence is automatic. -/]
/-
**Filter.Tendsto.uniformity_mul_iff_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.uniformity_mul_iff_right {ι : Type*} {f g : ι -> α × α} {l 
: Filter ι} (hf : Tendsto f l (𝓤 α)) : Tendsto (f * g) l (𝓤 α) ↔ Tendsto g l (𝓤 
α)
参数：hf : Tendsto f l (𝓤 α)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_mul_cancel_left`：inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b
· 使用定理 `Filter.Tendsto.uniformity_mul`：Filter.Tendsto.uniformity_mul {ι : Type*}
 {f g : ι -> α × α} {l : Filter ι} (hf : Tendsto f l (𝓤 α)) (hg : Tendsto g l (𝓤
 α)) : Tendsto (f *…
· 使用定理 `Filter.Tendsto.uniformity_inv`：Filter.Tendsto.uniformity_inv {ι : Type*}
 {f : ι -> α × α} {l : Filter ι} (hf : Tendsto f l (𝓤 α)) : Tendsto (f⁻¹) l (𝓤 α
)
-/
theorem Filter.Tendsto.uniformity_mul_iff_right {ι : Type*} {f g : ι → α × α} {l : Filter ι}
    (hf : Tendsto f l (𝓤 α)) :
    Tendsto (f * g) l (𝓤 α) ↔ Tendsto g l (𝓤 α) :=
  ⟨fun hfg ↦ by simpa using hf.uniformity_inv.uniformity_mul hfg, hf.uniformity_mul⟩

/-- If `g : ι → G × G` converges to the uniformity, then any `f : ι → G × G` converges to the
uniformity iff `f * g` does. This is often useful when `g` is valued in the diagonal,
in which case its convergence is automatic. -/
@[to_additive /-- If `g : ι → G × G` converges to the uniformity, then any `f : ι → G × G`
converges to the uniformity iff `f + g` does. This is often useful when `g` is valued in the
diagonal, in which case its convergence is automatic. -/]
/-
**Filter.Tendsto.uniformity_mul_iff_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.uniformity_mul_iff_left {ι : Type*} {f g : ι -> α × α} {l :
 Filter ι} (hg : Tendsto g l (𝓤 α)) : Tendsto (f * g) l (𝓤 α) ↔ Tendsto f l (𝓤 α
)
参数：hg : Tendsto g l (𝓤 α)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_inv_cancel_right`：mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a
· 使用定理 `Filter.Tendsto.uniformity_mul`：Filter.Tendsto.uniformity_mul {ι : Type*}
 {f g : ι -> α × α} {l : Filter ι} (hf : Tendsto f l (𝓤 α)) (hg : Tendsto g l (𝓤
 α)) : Tendsto (f *…
· 使用定理 `Filter.Tendsto.uniformity_inv`：Filter.Tendsto.uniformity_inv {ι : Type*}
 {f : ι -> α × α} {l : Filter ι} (hf : Tendsto f l (𝓤 α)) : Tendsto (f⁻¹) l (𝓤 α
)
-/
theorem Filter.Tendsto.uniformity_mul_iff_left {ι : Type*} {f g : ι → α × α} {l : Filter ι}
    (hg : Tendsto g l (𝓤 α)) :
    Tendsto (f * g) l (𝓤 α) ↔ Tendsto f l (𝓤 α) :=
  ⟨fun hfg ↦ by simpa using hfg.uniformity_mul hg.uniformity_inv, fun hf ↦ hf.uniformity_mul hg⟩

@[to_additive (attr := fun_prop) UniformContinuous.const_nsmul]
/-
**UniformContinuous.pow_const** 是 Mathlib 中的一个定理，位于命名空间 `UniformContinuous`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : UniformSpace α] [inst_1 : Group α]
 [IsUniformGroup α] [inst_3 : UniformSpace β]   {f : β → α}, UniformContinuous f
 → ∀ (n : ℕ), UniformContinuous fun x => f x ^ n
参数：n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem UniformContinuous.pow_const [UniformSpace β] {f : β → α} (hf : UniformContinuous f) :
    ∀ n : ℕ, UniformContinuous fun x => f x ^ n
  | 0 => by
    simp_rw [pow_zero]
    exact uniformContinuous_const
  | n + 1 => by
    simp_rw [pow_succ']
    exact hf.mul (hf.pow_const n)

@[to_additive uniformContinuous_const_nsmul]
/-
**uniformContinuous_pow_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformContinuous_pow_const (n : Nat) : UniformContinuous fun x : α => x ^
 n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.pow_const`：∀ {α : Type u_1} {β : Type u_2} [inst : Uni
formSpace α] [inst_1 : Group α] [IsUniformGroup α] [inst_3 : UniformSpace β]   {
f : β → α}, Unifo…
· 使用定理 `uniformContinuous_id`：uniformContinuous_id : UniformContinuous (@id α)
-/
theorem uniformContinuous_pow_const (n : ℕ) : UniformContinuous fun x : α => x ^ n :=
  uniformContinuous_id.pow_const n

@[to_additive (attr := fun_prop) UniformContinuous.const_zsmul]
/-
**UniformContinuous.zpow_const** 是 Mathlib 中的一个定理，位于命名空间 `UniformContinuous`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : UniformSpace α] [inst_1 : Group α]
 [IsUniformGroup α] [inst_3 : UniformSpace β]   {f : β → α}, UniformContinuous f
 → ∀ (n : ℤ), UniformContinuous fun x => f x ^ n
参数：n : ℤ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `UniformContinuous.pow_const`：∀ {α : Type u_1} {β : Type u_2} [inst : Uni
formSpace α] [inst_1 : Group α] [IsUniformGroup α] [inst_3 : UniformSpace β]   {
f : β → α}, Unifo…
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
· 使用定理 `UniformContinuous.inv`：UniformContinuous.inv [UniformSpace β] {f : β -> 
α} (hf : UniformContinuous f) : UniformContinuous fun x => (f x)⁻¹
-/
theorem UniformContinuous.zpow_const [UniformSpace β] {f : β → α} (hf : UniformContinuous f) :
    ∀ n : ℤ, UniformContinuous fun x => f x ^ n
  | (n : ℕ) => by
    simp_rw [zpow_natCast]
    exact hf.pow_const _
  | Int.negSucc n => by
    simp_rw [zpow_negSucc]
    exact (hf.pow_const _).inv

@[to_additive uniformContinuous_const_zsmul]
/-
**uniformContinuous_zpow_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformContinuous_zpow_const (n : Int) : UniformContinuous fun x : α => x 
^ n
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.zpow_const`：∀ {α : Type u_1} {β : Type u_2} [inst : Un
iformSpace α] [inst_1 : Group α] [IsUniformGroup α] [inst_3 : UniformSpace β]   
{f : β → α}, Unifo…
· 使用定理 `uniformContinuous_id`：uniformContinuous_id : UniformContinuous (@id α)
-/
theorem uniformContinuous_zpow_const (n : ℤ) : UniformContinuous fun x : α => x ^ n :=
  uniformContinuous_id.zpow_const n

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 10) IsUniformGroup.to_topologicalGroup : IsTopologicalGroup α where
  continuous_mul := uniformContinuous_mul.continuous
  continuous_inv := uniformContinuous_inv.continuous

@[to_additive]
/-
**uniformity_translate_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformity_translate_mul (a : α) : ((𝓤 α).map fun x : α × α => (x.1 * a, x
.2 * a)) = 𝓤 α
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `UniformContinuous.mul`：UniformContinuous.mul [UniformSpace β] {f : β -> 
α} {g : β -> α} (hf : UniformContinuous f) (hg : UniformContinuous g) : UniformC
ontinuous f…
· 使用定理 `uniformContinuous_id`：uniformContinuous_id : UniformContinuous (@id α)
· 使用定理 `uniformContinuous_const`：uniformContinuous_const {b : β} : UniformContin
uous fun _ : α => b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.map_map`：map_map : Filter.map m' (Filter.map m f) = Filter.map (m
' ∘ m) f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `inv_mul_cancel_right`：inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a
· 使用定理 `Prod.mk.eta`：∀ {α : Type u_1} {β : Type u_2} {p : α × β}, (p.1, p.2) = p
· 使用定理 `Filter.map_id'`：map_id' : Filter.map (fun x => x) f = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.map_mono`：map_mono : Monotone (map m)
-/
theorem uniformity_translate_mul (a : α) : ((𝓤 α).map fun x : α × α => (x.1 * a, x.2 * a)) = 𝓤 α :=
  le_antisymm (uniformContinuous_id.mul uniformContinuous_const)
    (calc
      𝓤 α =
          ((𝓤 α).map fun x : α × α => (x.1 * a⁻¹, x.2 * a⁻¹)).map fun x : α × α =>
            (x.1 * a, x.2 * a) := by simp [Filter.map_map, Function.comp_def]
      _ ≤ (𝓤 α).map fun x : α × α => (x.1 * a, x.2 * a) :=
        Filter.map_mono (uniformContinuous_id.mul uniformContinuous_const))

namespace MulOpposite

@[to_additive]
/-
**MulOpposite.** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsUniformGroup αᵐᵒᵖ :=
  ⟨uniformContinuous_op.comp
      ((uniformContinuous_unop.comp uniformContinuous_snd).inv.mul <|
        uniformContinuous_unop.comp uniformContinuous_fst)⟩

end MulOpposite

section

variable (α)

@[to_additive]
/-
**IsUniformGroup.isRightUniformGroup** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：IsUniformGroup.isRightUniformGroup : IsRightUniformGroup α where uniformit
y_eq
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformGroup.to_topologicalGroup`：∀ {α : Type u_1} [inst : UniformSpac
e α] [inst_1 : Group α] [IsUniformGroup α], IsTopologicalGroup α
· 使用引理 `eq_of_forall_le_iff`：eq_of_forall_le_iff (H : forall c, c <= a ↔ c <= b)
 : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_eq_comap_uniformity`：nhds_eq_comap_uniformity {x : α} : 𝓝 x = (𝓤 α)
.comap (Prod.mk x)
· 使用定理 `Filter.comap_comap`：comap_comap {m : γ -> β} {n : β -> α} : comap m (com
ap n f) = comap (n ∘ m) f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.tendsto_iff_comap`：tendsto_iff_comap {f : α -> β} {l₁ : Filter α}
 {l₂ : Filter β} : Tendsto f l₁ l₂ ↔ l₁ <= l₂.comap f
· 使用定理 `Filter.Tendsto.uniformity_mul_iff_left`：Filter.Tendsto.uniformity_mul_if
f_left {ι : Type*} {f g : ι -> α × α} {l : Filter ι} (hg : Tendsto g l (𝓤 α)) : 
Tendsto (f * g) l (𝓤 α) ↔ Te…
· 使用定理 `tendsto_diag_uniformity`：tendsto_diag_uniformity (f : β -> α) (l : Filte
r β) : Tendsto (fun x => (f x, f x)) l (𝓤 α)
· 使用定理 `Filter.tendsto_id'`：tendsto_id' {x y : Filter α} : Tendsto id x y ↔ x <=
 y
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `inv_mul_cancel_right`：inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a
· 使用定理 `Prod.mk.eta`：∀ {α : Type u_1} {β : Type u_2} {p : α × β}, (p.1, p.2) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance IsUniformGroup.isRightUniformGroup : IsRightUniformGroup α where
  uniformity_eq := by
    refine eq_of_forall_le_iff fun 𝓕 ↦ ?_
    rw [nhds_eq_comap_uniformity, comap_comap, ← tendsto_iff_comap,
      ← (tendsto_diag_uniformity Prod.fst 𝓕).uniformity_mul_iff_left, ← tendsto_id']
    congrm Tendsto ?_ _ _
    ext <;> simp

@[to_additive]
/-
**IsUniformGroup.isLeftUniformGroup** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：IsUniformGroup.isLeftUniformGroup : IsLeftUniformGroup α where uniformity_
eq
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformGroup.to_topologicalGroup`：∀ {α : Type u_1} [inst : UniformSpac
e α] [inst_1 : Group α] [IsUniformGroup α], IsTopologicalGroup α
· 使用引理 `eq_of_forall_le_iff`：eq_of_forall_le_iff (H : forall c, c <= a ↔ c <= b)
 : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_eq_comap_uniformity`：nhds_eq_comap_uniformity {x : α} : 𝓝 x = (𝓤 α)
.comap (Prod.mk x)
· 使用定理 `Filter.comap_comap`：comap_comap {m : γ -> β} {n : β -> α} : comap m (com
ap n f) = comap (n ∘ m) f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.tendsto_iff_comap`：tendsto_iff_comap {f : α -> β} {l₁ : Filter α}
 {l₂ : Filter β} : Tendsto f l₁ l₂ ↔ l₁ <= l₂.comap f
· 使用定理 `Filter.Tendsto.uniformity_mul_iff_right`：Filter.Tendsto.uniformity_mul_i
ff_right {ι : Type*} {f g : ι -> α × α} {l : Filter ι} (hf : Tendsto f l (𝓤 α)) 
: Tendsto (f * g) l (𝓤 α) ↔ T…
· 使用定理 `tendsto_diag_uniformity`：tendsto_diag_uniformity (f : β -> α) (l : Filte
r β) : Tendsto (fun x => (f x, f x)) l (𝓤 α)
· 使用定理 `Filter.tendsto_id'`：tendsto_id' {x y : Filter α} : Tendsto id x y ↔ x <=
 y
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
· 使用定理 `Prod.mk.eta`：∀ {α : Type u_1} {β : Type u_2} {p : α × β}, (p.1, p.2) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance IsUniformGroup.isLeftUniformGroup : IsLeftUniformGroup α where
  uniformity_eq := by
    refine eq_of_forall_le_iff fun 𝓕 ↦ ?_
    rw [nhds_eq_comap_uniformity, comap_comap, ← tendsto_iff_comap,
      ← (tendsto_diag_uniformity Prod.fst 𝓕).uniformity_mul_iff_right, ← tendsto_id']
    congrm Tendsto ?_ _ _
    ext <;> simp

@[to_additive]
/-
**IsUniformGroup.ext** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUniformGroup.ext {G : Type*} [Group G] {u v : UniformSpace G} (hu : @IsU
niformGroup G u _) (hv : @IsUniformGroup G v _) (h : @nhds _ u.toTopologicalSpac
e 1 = @nhds _ v.toTopologicalSpace 1) : u = v
参数：hu : @IsUniformGroup G u _；hv : @IsUniformGroup G v _；h : @nhds _ u.toTopolog
icalSpace 1 = @nhds _ v.toTopologicalSpace 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.ext`：∀ {α : Type ua} {u₁ u₂ : UniformSpace α}, uniformity α
 = uniformity α → u₁ = u₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `uniformity_eq_comap_nhds_one`：uniformity_eq_comap_nhds_one : 𝓤 Gᵣ = coma
p (fun x : Gᵣ × Gᵣ => x.2 / x.1) (𝓝 1)
-/
theorem IsUniformGroup.ext {G : Type*} [Group G] {u v : UniformSpace G} (hu : @IsUniformGroup G u _)
    (hv : @IsUniformGroup G v _)
    (h : @nhds _ u.toTopologicalSpace 1 = @nhds _ v.toTopologicalSpace 1) : u = v :=
  UniformSpace.ext <| by
    rw [(have := hu; uniformity_eq_comap_nhds_one), (have := hv; uniformity_eq_comap_nhds_one), h]

@[to_additive]
/-
**IsUniformGroup.ext_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUniformGroup.ext_iff {G : Type*} [Group G] {u v : UniformSpace G} (hu : 
@IsUniformGroup G u _) (hv : @IsUniformGroup G v _) : u = v ↔ @nhds _ u.toTopolo
gicalSpace 1 = @nhds _ v.toTopologicalSpace 1
参数：hu : @IsUniformGroup G u _；hv : @IsUniformGroup G v _。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformGroup.ext`：IsUniformGroup.ext {G : Type*} [Group G] {u v : Unif
ormSpace G} (hu : @IsUniformGroup G u _) (hv : @IsUniformGroup G v _) (h : @nhds
 _ u.toT…
-/
theorem IsUniformGroup.ext_iff {G : Type*} [Group G] {u v : UniformSpace G}
    (hu : @IsUniformGroup G u _) (hv : @IsUniformGroup G v _) :
    u = v ↔ @nhds _ u.toTopologicalSpace 1 = @nhds _ v.toTopologicalSpace 1 :=
  ⟨fun h => h ▸ rfl, hu.ext hv⟩

variable {α}

@[to_additive]
/-
**IsUniformGroup.uniformity_countably_generated** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUniformGroup.uniformity_countably_generated [(𝓝 (1 : α)).IsCountablyGene
rated] : (𝓤 α).IsCountablyGenerated
参数：𝓝 (1 : α)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `uniformity_eq_comap_nhds_one`：uniformity_eq_comap_nhds_one : 𝓤 Gᵣ = coma
p (fun x : Gᵣ × Gᵣ => x.2 / x.1) (𝓝 1)
· 使用定理 `Filter.comap.isCountablyGenerated`：∀ {α : Type u_1} {β : Type u_2} (l : 
Filter β) [l.IsCountablyGenerated] (f : α → β),   (Filter.comap f l).IsCountably
Generated
-/
theorem IsUniformGroup.uniformity_countably_generated [(𝓝 (1 : α)).IsCountablyGenerated] :
    (𝓤 α).IsCountablyGenerated := by
  rw [uniformity_eq_comap_nhds_one]
  exact Filter.comap.isCountablyGenerated _ _

end

section OfLeftAndRight

variable [UniformSpace β] [Group β] [IsLeftUniformGroup β] [IsRightUniformGroup β]

open Prod (snd) in
/-- Note: this assumes `[IsLeftUniformGroup β] [IsRightUniformGroup β]` instead of the more typical
(and equivalent) `[IsUniformGroup β]` because this is used in the proof of said equivalence. -/
@[to_additive /-- Note: this assumes `[IsLeftUniformAddGroup β] [IsRightUniformAddGroup β]`
instead of the more typical (and equivalent) `[IsUniformAddGroup β]` because this is used
in the proof of said equivalence. -/]
/-
**comap_conj_nhds_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：comap_conj_nhds_one : comap (fun gx : β × β => gx.1 * gx.2 * gx.1⁻¹) (𝓝 1)
 = comap snd (𝓝 1)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.mulLeft_symm`：mulLeft_symm (a : G) : (Equiv.mulLeft a).symm = Equi
v.mulLeft a⁻¹
· 使用定理 `Equiv.prodShear_apply`：∀ {α₁ : Type u_9} {α₂ : Type u_10} {β₁ : Type u_1
1} {β₂ : Type u_12} (e₁ : α₁ ≃ α₂) (e₂ : α₁ → β₁ ≃ β₂),   ⇑(e₁.prodShear e₂) = f
un x => (e₁…
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Filter.comap_injective`：comap_injective {f : α -> β} (hf : Surjective f)
 : Injective (comap f)
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `Filter.comap_comap`：comap_comap {m : γ -> β} {n : β -> α} : comap m (com
ap n f) = comap (n ∘ m) f
· 使用引理 `uniformity_eq_comap_inv_mul_nhds_one`：uniformity_eq_comap_inv_mul_nhds_o
ne : 𝓤 Gₗ = comap (fun x : Gₗ × Gₗ => x.1⁻¹ * x.2) (𝓝 1)
· 使用引理 `uniformity_eq_comap_mul_inv_nhds_one`：uniformity_eq_comap_mul_inv_nhds_o
ne : 𝓤 Gᵣ = comap (fun x : Gᵣ × Gᵣ => x.2 * x.1⁻¹) (𝓝 1)
-/
theorem comap_conj_nhds_one :
    comap (fun gx : β × β ↦ gx.1 * gx.2 * gx.1⁻¹) (𝓝 1) = comap snd (𝓝 1) := by
  let dr : β × β → β := fun xy ↦ xy.2 * xy.1⁻¹
  let dl : β × β → β := fun xy ↦ xy.1⁻¹ * xy.2
  let conj : β × β → β := fun gx ↦ gx.1 * gx.2 * gx.1⁻¹
  let φ : β × β ≃ β × β := (Equiv.refl β).prodShear (fun b ↦ (Equiv.mulLeft b).symm)
  have conj_φ : conj ∘ φ = dr := by
    ext; simp [conj, φ, dr]
  have snd_φ : snd ∘ φ = dl := by
    ext; simp [φ, dl]
  rw [← (comap_injective φ.surjective).eq_iff, comap_comap, comap_comap, conj_φ, snd_φ,
      ← uniformity_eq_comap_inv_mul_nhds_one, ← uniformity_eq_comap_mul_inv_nhds_one]

open Prod (snd) in
/-- Note: this assumes `[IsLeftUniformGroup β] [IsRightUniformGroup β]` instead of the more typical
(and equivalent) `[IsUniformGroup β]` because this is used in the proof of said equivalence. -/
@[to_additive /-- Note: this assumes `[IsLeftUniformAddGroup β] [IsRightUniformAddGroup β]`
instead of the more typical (and equivalent) `[IsUniformAddGroup β]` because this is used
in the proof of said equivalence. -/]
/-
**tendsto_conj_nhds_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_conj_nhds_one : Tendsto (fun gx : β × β => gx.1 * gx.2 * gx.1⁻¹) (
comap snd (𝓝 1)) (𝓝 1)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.tendsto_iff_comap`：tendsto_iff_comap {f : α -> β} {l₁ : Filter α}
 {l₂ : Filter β} : Tendsto f l₁ l₂ ↔ l₁ <= l₂.comap f
· 使用定理 `comap_conj_nhds_one`：comap_conj_nhds_one : comap (fun gx : β × β => gx.1
 * gx.2 * gx.1⁻¹) (𝓝 1) = comap snd (𝓝 1)
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem tendsto_conj_nhds_one :
    Tendsto (fun gx : β × β ↦ gx.1 * gx.2 * gx.1⁻¹) (comap snd (𝓝 1)) (𝓝 1) := by
  rw [tendsto_iff_comap, comap_conj_nhds_one]

/-- Note: this assumes `[IsLeftUniformGroup β] [IsRightUniformGroup β]` instead of the more typical
(and equivalent) `[IsUniformGroup β]` because this is used in the proof of said equivalence. -/
@[to_additive /-- Note: this assumes `[IsLeftUniformAddGroup β] [IsRightUniformAddGroup β]`
instead of the more typical (and equivalent) `[IsUniformAddGroup β]` because this is used
in the proof of said equivalence. -/]
/-
**Filter.Tendsto.conj_nhds_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.conj_nhds_one {ι : Type*} {l : Filter ι} {x : ι -> β} (hx :
 Tendsto x l (𝓝 1)) (g : ι -> β) : Tendsto (g * x * g⁻¹) l (𝓝 1)
参数：hx : Tendsto x l (𝓝 1)；g : ι -> β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.tendsto_comap_iff`：tendsto_comap_iff {f : α -> β} {g : β -> γ} {a
 : Filter α} {c : Filter γ} : Tendsto f a (c.comap g) ↔ Tendsto (g ∘ f) a c
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `tendsto_conj_nhds_one`：tendsto_conj_nhds_one : Tendsto (fun gx : β × β =
> gx.1 * gx.2 * gx.1⁻¹) (comap snd (𝓝 1)) (𝓝 1)
-/
theorem Filter.Tendsto.conj_nhds_one {ι : Type*} {l : Filter ι} {x : ι → β}
    (hx : Tendsto x l (𝓝 1)) (g : ι → β) :
    Tendsto (g * x * g⁻¹) l (𝓝 1) := by
  have : Tendsto (fun i ↦ (g i, x i)) l (comap Prod.snd (𝓝 1)) := by
    rwa [tendsto_comap_iff]
  -- `exact` works but is quite slow...
  convert! tendsto_conj_nhds_one.comp this
/-
**IsUniformGroup.of_left_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUniformGroup.of_left_right : IsUniformGroup β where uniformContinuous_di
v
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Filter.Tendsto.mul`：Filter.Tendsto.mul {α : Type*} {f g : α -> M} {x : F
ilter α} {a b : M} (hf : Tendsto f x (𝓝 a)) (hg : Tendsto g x (𝓝 b)) : Tendsto (
fun x =>…
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `IsLeftUniformGroup.toIsTopologicalGroup`：∀ {G : Type u_7} {inst : Unifor
mSpace G} {inst_1 : Group G} [self : IsLeftUniformGroup G], IsTopologicalGroup G
· 使用引理 `uniformity_eq_comap_inv_mul_nhds_one`：uniformity_eq_comap_inv_mul_nhds_o
ne : 𝓤 Gₗ = comap (fun x : Gₗ × Gₗ => x.1⁻¹ * x.2) (𝓝 1)
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Filter.tendsto_comap`：tendsto_comap {f : α -> β} {x : Filter β} : Tendst
o f (comap f x) x
· 使用定理 `Filter.tendsto_fst`：tendsto_fst : Tendsto Prod.fst (f ×ˢ g) f
· 使用引理 `uniformity_eq_comap_inv_mul_nhds_one_swapped`：uniformity_eq_comap_inv_mu
l_nhds_one_swapped : 𝓤 Gₗ = comap (fun x : Gₗ × Gₗ => x.2⁻¹ * x.1) (𝓝 1)
· 使用定理 `Filter.tendsto_snd`：tendsto_snd : Tendsto Prod.snd (f ×ˢ g) g
· 使用定理 `Filter.Tendsto.conj_nhds_one`：Filter.Tendsto.conj_nhds_one {ι : Type*} {
l : Filter ι} {x : ι -> β} (hx : Tendsto x l (𝓝 1)) (g : ι -> β) : Tendsto (g * 
x * g⁻¹) l (𝓝 1)
· 使用定理 `UniformContinuous.eq_1`：∀ {α : Type ua} {β : Type ub} [inst : UniformSpa
ce α] [inst_1 : UniformSpace β] (f : α → β),   UniformContinuous f = Filter.Tend
sto (fun x =…
· 使用引理 `uniformity_eq_comap_mul_inv_nhds_one`：uniformity_eq_comap_mul_inv_nhds_o
ne : 𝓤 Gᵣ = comap (fun x : Gᵣ × Gᵣ => x.2 * x.1⁻¹) (𝓝 1)
· 使用定理 `Filter.tendsto_comap_iff`：tendsto_comap_iff {f : α -> β} {g : β -> γ} {a
 : Filter α} {c : Filter γ} : Tendsto f a (c.comap g) ↔ Tendsto (g ∘ f) a c
· 使用定理 `uniformity_prod_eq_prod`：uniformity_prod_eq_prod [UniformSpace α] [Unifo
rmSpace β] : 𝓤 (α × β) = map (fun p : (α × α) × β × β => ((p.1.1, p.2.1), (p.1.2
, p.2.2))) (𝓤…
· 使用定理 `Filter.tendsto_map'_iff`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} 
{f : β → γ} {g : α → β} {x : Filter α} {y : Filter γ},   Filter.Tendsto f (Filte
r.map g x) y …
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
-/
theorem IsUniformGroup.of_left_right : IsUniformGroup β where
  uniformContinuous_div := by
    let φ : (β × β) × (β × β) → β := fun ⟨⟨x₁, x₂⟩, ⟨y₁, y₂⟩⟩ ↦ x₂ * y₂⁻¹ * y₁ * x₁⁻¹
    let ψ : (β × β) × (β × β) → β := fun ⟨⟨x₁, x₂⟩, ⟨y₁, y₂⟩⟩ ↦ (x₁⁻¹ * x₂) * (y₂⁻¹ * y₁)
    let g : (β × β) × (β × β) → β := fun ⟨⟨x₁, x₂⟩, ⟨y₁, y₂⟩⟩ ↦ x₁
    suffices Tendsto φ (𝓤 β ×ˢ 𝓤 β) (𝓝 1) by
      rw [UniformContinuous, uniformity_eq_comap_mul_inv_nhds_one β, tendsto_comap_iff,
        uniformity_prod_eq_prod, tendsto_map'_iff]
      simpa [Function.comp_def, div_eq_mul_inv, ← mul_assoc]
    have φ_ψ_conj : φ = g * ψ * g⁻¹ := by
      ext
      simp [φ, ψ, g, mul_assoc]
    have ψ_tendsto : Tendsto ψ (𝓤 β ×ˢ 𝓤 β) (𝓝 1) := by
      rw [← one_mul 1]
      refine .mul ?_ ?_
      · rw [uniformity_eq_comap_inv_mul_nhds_one]
        exact tendsto_comap.comp tendsto_fst
      · rw [uniformity_eq_comap_inv_mul_nhds_one_swapped]
        exact tendsto_comap.comp tendsto_snd
    exact φ_ψ_conj ▸ ψ_tendsto.conj_nhds_one g
/-
**isUniformGroup_iff_left_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isUniformGroup_iff_left_right {γ : Type*} [Group γ] [UniformSpace γ] : IsU
niformGroup γ ↔ IsLeftUniformGroup γ ∧ IsRightUniformGroup γ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformGroup.of_left_right`：IsUniformGroup.of_left_right : IsUniformGr
oup β where uniformContinuous_div
-/
theorem isUniformGroup_iff_left_right {γ : Type*} [Group γ] [UniformSpace γ] :
    IsUniformGroup γ ↔ IsLeftUniformGroup γ ∧ IsRightUniformGroup γ :=
  ⟨fun _ ↦ ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ ↦ .of_left_right⟩
/-
**eventually_forall_conj_nhds_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eventually_forall_conj_nhds_one {p : α -> Prop} (hp : forallᶠ x in 𝓝 1, p 
x) : forallᶠ x in 𝓝 1, forall g, p (g * x * g⁻¹)
参数：hp : forallᶠ x in 𝓝 1, p x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `tendsto_conj_nhds_one`：tendsto_conj_nhds_one : Tendsto (fun gx : β × β =
> gx.1 * gx.2 * gx.1⁻¹) (comap snd (𝓝 1)) (𝓝 1)
-/
theorem eventually_forall_conj_nhds_one {p : α → Prop}
    (hp : ∀ᶠ x in 𝓝 1, p x) :
    ∀ᶠ x in 𝓝 1, ∀ g, p (g * x * g⁻¹) := by
  simpa using tendsto_conj_nhds_one.eventually hp

end OfLeftAndRight

@[to_additive]
/-
**Filter.HasBasis.uniformity_of_nhds_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.HasBasis.uniformity_of_nhds_one {ι} {p : ι -> Prop} {U : ι -> Set α
} (h : (𝓝 (1 : α)).HasBasis p U) : (𝓤 α).HasBasis p fun i => { x : α × α | x.2 /
 x.1 in U i }
参数：h : (𝓝 (1 : α)).HasBasis p U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `uniformity_eq_comap_nhds_one`：uniformity_eq_comap_nhds_one : 𝓤 Gᵣ = coma
p (fun x : Gᵣ × Gᵣ => x.2 / x.1) (𝓝 1)
· 使用定理 `Filter.HasBasis.comap`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l
 : Filter α} {p : ι → Prop} {s : ι → Set α} (f : β → α),   l.HasBasis p s → (Fil
ter.comap f…
-/
theorem Filter.HasBasis.uniformity_of_nhds_one {ι} {p : ι → Prop} {U : ι → Set α}
    (h : (𝓝 (1 : α)).HasBasis p U) :
    (𝓤 α).HasBasis p fun i => { x : α × α | x.2 / x.1 ∈ U i } := by
  rw [uniformity_eq_comap_nhds_one]
  exact h.comap _

@[to_additive]
/-
**Filter.HasBasis.uniformity_of_nhds_one_inv_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.HasBasis.uniformity_of_nhds_one_inv_mul {ι} {p : ι -> Prop} {U : ι 
-> Set α} (h : (𝓝 (1 : α)).HasBasis p U) : (𝓤 α).HasBasis p fun i => { x : α × α
 | x.1⁻¹ * x.2 in U i }
参数：h : (𝓝 (1 : α)).HasBasis p U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `uniformity_eq_comap_inv_mul_nhds_one`：uniformity_eq_comap_inv_mul_nhds_o
ne : 𝓤 Gₗ = comap (fun x : Gₗ × Gₗ => x.1⁻¹ * x.2) (𝓝 1)
· 使用定理 `Filter.HasBasis.comap`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l
 : Filter α} {p : ι → Prop} {s : ι → Set α} (f : β → α),   l.HasBasis p s → (Fil
ter.comap f…
-/
theorem Filter.HasBasis.uniformity_of_nhds_one_inv_mul {ι} {p : ι → Prop} {U : ι → Set α}
    (h : (𝓝 (1 : α)).HasBasis p U) :
    (𝓤 α).HasBasis p fun i => { x : α × α | x.1⁻¹ * x.2 ∈ U i } := by
  rw [uniformity_eq_comap_inv_mul_nhds_one]
  exact h.comap _

@[to_additive]
/-
**Filter.HasBasis.uniformity_of_nhds_one_swapped** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.HasBasis.uniformity_of_nhds_one_swapped {ι} {p : ι -> Prop} {U : ι 
-> Set α} (h : (𝓝 (1 : α)).HasBasis p U) : (𝓤 α).HasBasis p fun i => { x : α × α
 | x.1 / x.2 in U i }
参数：h : (𝓝 (1 : α)).HasBasis p U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `uniformity_eq_comap_nhds_one_swapped`：uniformity_eq_comap_nhds_one_swapp
ed : 𝓤 Gᵣ = comap (fun x : Gᵣ × Gᵣ => x.1 / x.2) (𝓝 1)
· 使用定理 `Filter.HasBasis.comap`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l
 : Filter α} {p : ι → Prop} {s : ι → Set α} (f : β → α),   l.HasBasis p s → (Fil
ter.comap f…
-/
theorem Filter.HasBasis.uniformity_of_nhds_one_swapped {ι} {p : ι → Prop} {U : ι → Set α}
    (h : (𝓝 (1 : α)).HasBasis p U) :
    (𝓤 α).HasBasis p fun i => { x : α × α | x.1 / x.2 ∈ U i } := by
  rw [uniformity_eq_comap_nhds_one_swapped]
  exact h.comap _

@[to_additive]
/-
**Filter.HasBasis.uniformity_of_nhds_one_inv_mul_swapped** 是 Mathlib 中的一个定理，位于命名
空间 ``。
形式化陈述：Filter.HasBasis.uniformity_of_nhds_one_inv_mul_swapped {ι} {p : ι -> Prop}
 {U : ι -> Set α} (h : (𝓝 (1 : α)).HasBasis p U) : (𝓤 α).HasBasis p fun i => { x
 : α × α | x.2⁻¹ * x.1 in U i }
参数：h : (𝓝 (1 : α)).HasBasis p U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `uniformity_eq_comap_inv_mul_nhds_one_swapped`：uniformity_eq_comap_inv_mu
l_nhds_one_swapped : 𝓤 Gₗ = comap (fun x : Gₗ × Gₗ => x.2⁻¹ * x.1) (𝓝 1)
· 使用定理 `Filter.HasBasis.comap`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l
 : Filter α} {p : ι → Prop} {s : ι → Set α} (f : β → α),   l.HasBasis p s → (Fil
ter.comap f…
-/
theorem Filter.HasBasis.uniformity_of_nhds_one_inv_mul_swapped {ι} {p : ι → Prop} {U : ι → Set α}
    (h : (𝓝 (1 : α)).HasBasis p U) :
    (𝓤 α).HasBasis p fun i => { x : α × α | x.2⁻¹ * x.1 ∈ U i } := by
  rw [uniformity_eq_comap_inv_mul_nhds_one_swapped]
  exact h.comap _

@[to_additive]
/-
**uniformContinuous_of_tendsto_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformContinuous_of_tendsto_one {hom : Type*} [UniformSpace β] [Group β] 
[IsUniformGroup β] [FunLike hom α β] [MonoidHomClass hom α β] {f : hom} (h : Ten
dsto f (𝓝 1) (𝓝 1)) : UniformContinuous f
参数：h : Tendsto f (𝓝 1) (𝓝 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_div`：map_div [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) : forall a b, f (a / b) = f a / f b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `UniformContinuous.eq_1`：∀ {α : Type ua} {β : Type ub} [inst : UniformSpa
ce α] [inst_1 : UniformSpace β] (f : α → β),   UniformContinuous f = Filter.Tend
sto (fun x =…
· 使用定理 `uniformity_eq_comap_nhds_one`：uniformity_eq_comap_nhds_one : 𝓤 Gᵣ = coma
p (fun x : Gᵣ × Gᵣ => x.2 / x.1) (𝓝 1)
· 使用定理 `Filter.tendsto_comap_iff`：tendsto_comap_iff {f : α -> β} {g : β -> γ} {a
 : Filter α} {c : Filter γ} : Tendsto f a (c.comap g) ↔ Tendsto (g ∘ f) a c
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Filter.tendsto_comap`：tendsto_comap {f : α -> β} {x : Filter β} : Tendst
o f (comap f x) x
-/
theorem uniformContinuous_of_tendsto_one {hom : Type*} [UniformSpace β] [Group β] [IsUniformGroup β]
    [FunLike hom α β] [MonoidHomClass hom α β] {f : hom} (h : Tendsto f (𝓝 1) (𝓝 1)) :
    UniformContinuous f := by
  have :
    ((fun x : β × β => x.2 / x.1) ∘ fun x : α × α => (f x.1, f x.2)) = fun x : α × α =>
      f (x.2 / x.1) := by ext; simp only [Function.comp_apply, map_div]
  rw [UniformContinuous, uniformity_eq_comap_nhds_one α, uniformity_eq_comap_nhds_one β,
    tendsto_comap_iff, this]
  exact Tendsto.comp h tendsto_comap

/-- A group homomorphism (a bundled morphism of a type that implements `MonoidHomClass`) between
two uniform groups is uniformly continuous provided that it is continuous at one. See also
`continuous_of_continuousAt_one`. -/
@[to_additive /-- An additive group homomorphism (a bundled morphism of a type that implements
`AddMonoidHomClass`) between two uniform additive groups is uniformly continuous provided that it
is continuous at zero. See also `continuous_of_continuousAt_zero`. -/]
/-
**uniformContinuous_of_continuousAt_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformContinuous_of_continuousAt_one {hom : Type*} [UniformSpace β] [Grou
p β] [IsUniformGroup β] [FunLike hom α β] [MonoidHomClass hom α β] (f : hom) (hf
 : ContinuousAt f 1) : UniformContinuous f
参数：f : hom；hf : ContinuousAt f 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `uniformContinuous_of_tendsto_one`：uniformContinuous_of_tendsto_one {hom 
: Type*} [UniformSpace β] [Group β] [IsUniformGroup β] [FunLike hom α β] [Monoid
HomClass hom α β] {f :…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `ContinuousAt.tendsto`：ContinuousAt.tendsto (h : ContinuousAt f x) : Tend
sto f (𝓝 x) (𝓝 (f x))
-/
theorem uniformContinuous_of_continuousAt_one {hom : Type*} [UniformSpace β] [Group β]
    [IsUniformGroup β] [FunLike hom α β] [MonoidHomClass hom α β]
    (f : hom) (hf : ContinuousAt f 1) :
    UniformContinuous f :=
  uniformContinuous_of_tendsto_one (by simpa using hf.tendsto)

@[to_additive]
/-
**MonoidHom.uniformContinuous_of_continuousAt_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonoidHom.uniformContinuous_of_continuousAt_one [UniformSpace β] [Group β]
 [IsUniformGroup β] (f : α ->* β) (hf : ContinuousAt f 1) : UniformContinuous f
参数：f : α ->* β；hf : ContinuousAt f 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `uniformContinuous_of_continuousAt_one`：uniformContinuous_of_continuousAt
_one {hom : Type*} [UniformSpace β] [Group β] [IsUniformGroup β] [FunLike hom α 
β] [MonoidHomClass hom α β]…
-/
theorem MonoidHom.uniformContinuous_of_continuousAt_one [UniformSpace β] [Group β]
    [IsUniformGroup β] (f : α →* β) (hf : ContinuousAt f 1) : UniformContinuous f :=
  _root_.uniformContinuous_of_continuousAt_one f hf

/-- A homomorphism from a uniform group to a discrete uniform group is continuous if and only if
its kernel is open. -/
@[to_additive /-- A homomorphism from a uniform additive group to a discrete uniform additive group
is continuous if and only if its kernel is open. -/]
/-
**IsUniformGroup.uniformContinuous_iff_isOpen_ker** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUniformGroup.uniformContinuous_iff_isOpen_ker {hom : Type*} [UniformSpac
e β] [DiscreteTopology β] [Group β] [IsUniformGroup β] [FunLike hom α β] [Monoid
HomClass hom α β] {f : hom} : UniformContinuous f ↔ IsOpen ((f : α ->* β).ker : 
Set α)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `UniformContinuous.continuous`：UniformContinuous.continuous (hf : Uniform
Continuous f) : Continuous f
· 使用定理 `isOpen_discrete`：isOpen_discrete (s : Set α) : IsOpen s
· 使用定理 `uniformContinuous_of_continuousAt_one`：uniformContinuous_of_continuousAt
_one {hom : Type*} [UniformSpace β] [Group β] [IsUniformGroup β] [FunLike hom α 
β] [MonoidHomClass hom α β]…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousAt.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSp
ace X] [inst_1 : TopologicalSpace Y] (f : X → Y) (x : X),   ContinuousAt f x = F
ilter.T…
· 使用定理 `nhds_discrete`：nhds_discrete (α : Type*) [TopologicalSpace α] [DiscreteT
opology α] : @nhds α _ = pure
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `Filter.tendsto_pure`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {a : Fi
lter α} {b : β},   Filter.Tendsto f a (pure b) ↔ ∀ᶠ (x : α) in a, f x = b
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
-/
theorem IsUniformGroup.uniformContinuous_iff_isOpen_ker {hom : Type*} [UniformSpace β]
    [DiscreteTopology β] [Group β] [IsUniformGroup β] [FunLike hom α β] [MonoidHomClass hom α β]
    {f : hom} :
    UniformContinuous f ↔ IsOpen ((f : α →* β).ker : Set α) := by
  refine ⟨fun hf => ?_, fun hf => ?_⟩
  · apply (isOpen_discrete ({1} : Set β)).preimage hf.continuous
  · apply uniformContinuous_of_continuousAt_one
    rw [ContinuousAt, nhds_discrete β, map_one, tendsto_pure]
    exact hf.mem_nhds (map_one f)

@[to_additive]
/-
**uniformContinuous_monoidHom_of_continuous** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformContinuous_monoidHom_of_continuous {hom : Type*} [UniformSpace β] [
Group β] [IsUniformGroup β] [FunLike hom α β] [MonoidHomClass hom α β] {f : hom}
 (h : Continuous f) : UniformContinuous f
参数：h : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `uniformContinuous_of_tendsto_one`：uniformContinuous_of_tendsto_one {hom 
: Type*} [UniformSpace β] [Group β] [IsUniformGroup β] [FunLike hom α β] [Monoid
HomClass hom α β] {f :…
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
-/
theorem uniformContinuous_monoidHom_of_continuous {hom : Type*} [UniformSpace β] [Group β]
    [IsUniformGroup β] [FunLike hom α β] [MonoidHomClass hom α β] {f : hom} (h : Continuous f) :
    UniformContinuous f :=
  uniformContinuous_of_tendsto_one <|
    suffices Tendsto f (𝓝 1) (𝓝 (f 1)) by rwa [map_one] at this
    h.tendsto 1

@[to_additive]
/-
**MonoidHom.isUniformInducing_of_isInducing** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonoidHom.isUniformInducing_of_isInducing {Hom : Type*} [UniformSpace β] [
Group β] [IsUniformGroup β] [FunLike Hom α β] [MonoidHomClass Hom α β] {f : Hom}
 (h : IsInducing f) : IsUniformInducing f where comap_uniformity
参数：h : IsInducing f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `uniformity_eq_comap_nhds_one`：uniformity_eq_comap_nhds_one : 𝓤 Gᵣ = coma
p (fun x : Gᵣ × Gᵣ => x.2 / x.1) (𝓝 1)
· 使用定理 `Filter.comap_comap`：comap_comap {m : γ -> β} {n : β -> α} : comap m (com
ap n f) = comap (n ∘ m) f
· 使用引理 `Topology.IsInducing.nhds_eq_comap`：nhds_eq_comap (hf : IsInducing f) : f
orall x : X, 𝓝 x = comap f (𝓝 <| f x)
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_div`：map_div [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) : forall a b, f (a / b) = f a / f b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem MonoidHom.isUniformInducing_of_isInducing {Hom : Type*} [UniformSpace β] [Group β]
    [IsUniformGroup β] [FunLike Hom α β] [MonoidHomClass Hom α β] {f : Hom} (h : IsInducing f) :
    IsUniformInducing f where
  comap_uniformity := by
    simp [uniformity_eq_comap_nhds_one, comap_comap, Function.comp_def, h.nhds_eq_comap]

@[to_additive]
/-
**MonoidHom.isUniformEmbedding_of_isEmbedding** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonoidHom.isUniformEmbedding_of_isEmbedding {Hom : Type*} [UniformSpace β]
 [Group β] [IsUniformGroup β] [FunLike Hom α β] [MonoidHomClass Hom α β] {f : Ho
m} (h : IsEmbedding f) : IsUniformEmbedding f where toIsUniformInducing
参数：h : IsEmbedding f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.isUniformInducing_of_isInducing`：MonoidHom.isUniformInducing_o
f_isInducing {Hom : Type*} [UniformSpace β] [Group β] [IsUniformGroup β] [FunLik
e Hom α β] [MonoidHomClass Hom …
· 使用定理 `Topology.IsEmbedding.isInducing`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEmb
edding f → Topology.I…
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
-/
theorem MonoidHom.isUniformEmbedding_of_isEmbedding {Hom : Type*} [UniformSpace β] [Group β]
    [IsUniformGroup β] [FunLike Hom α β] [MonoidHomClass Hom α β] {f : Hom} (h : IsEmbedding f) :
    IsUniformEmbedding f where
  toIsUniformInducing := MonoidHom.isUniformInducing_of_isInducing h.isInducing
  injective := h.injective

end IsUniformGroup

section IsTopologicalGroup

open Filter

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The right uniformity on a topological group (as opposed to the left uniformity).

Warning: in general the right and left uniformities do not coincide and so one does not obtain a
`IsUniformGroup` structure. Two important special cases where they _do_ coincide are for
commutative groups (see `isUniformGroup_of_commGroup`) and for compact groups (see
`IsUniformGroup.of_compactSpace`). -/
@[to_additive (attr := instance_reducible)
/-- The right uniformity on a topological additive group (as opposed to the left
uniformity).

Warning: in general the right and left uniformities do not coincide and so one does not obtain a
`IsUniformAddGroup` structure. Two important special cases where they _do_ coincide are for
commutative additive groups (see `isUniformAddGroup_of_addCommGroup`) and for compact
additive groups (see `IsUniformAddGroup.of_compactSpace`). -/]
/-
**IsTopologicalGroup.rightUniformSpace** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsTopologicalGroup.rightUniformSpace : UniformSpace G where uniformity
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def IsTopologicalGroup.rightUniformSpace : UniformSpace G where
  uniformity := comap (fun p : G × G => p.2 * p.1⁻¹) (𝓝 1)
  symm :=
    have : Tendsto (fun p : G × G ↦ (p.2 * p.1⁻¹)⁻¹) (comap (fun p : G × G ↦ p.2 * p.1⁻¹) (𝓝 1))
      (𝓝 1⁻¹) := tendsto_id.inv.comp tendsto_comap
    by simpa [tendsto_comap_iff]
  comp := Tendsto.le_comap fun U H ↦ by
    rcases exists_nhds_one_split H with ⟨V, V_nhds, V_mul⟩
    refine mem_map.2 (mem_of_superset (mem_lift' <| preimage_mem_comap V_nhds) ?_)
    rintro ⟨x, y⟩ ⟨z, hz₁, hz₂⟩
    simpa using V_mul _ hz₂ _ hz₁
  nhds_eq_comap_uniformity _ := by
    simp only [comap_comap, Function.comp_def, nhds_translation_mul_inv]

attribute [local instance] IsTopologicalGroup.rightUniformSpace

@[to_additive]
/-
**uniformity_eq_comap_nhds_one'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformity_eq_comap_nhds_one' : 𝓤 G = comap (fun p : G × G => p.2 * p.1⁻¹)
 (𝓝 (1 : G))
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem uniformity_eq_comap_nhds_one' : 𝓤 G = comap (fun p : G × G => p.2 * p.1⁻¹) (𝓝 (1 : G)) :=
  rfl

end IsTopologicalGroup


section IsTopologicalGroup

open Filter

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The left uniformity on a topological group (as opposed to the right uniformity).

Warning: in general the right and left uniformities do not coincide and so one does not obtain a
`IsUniformGroup` structure. Two important special cases where they _do_ coincide are for
commutative groups (see `isUniformGroup_of_commGroup`) and for compact groups (see
`IsUniformGroup.of_compactSpace`). -/
@[to_additive (attr := instance_reducible)
/-- The left uniformity on a topological additive group (as opposed to the right
uniformity).

Warning: in general the right and left uniformities do not coincide and so one does not obtain a
`IsUniformAddGroup` structure. Two important special cases where they _do_ coincide are for
commutative additive groups (see `isUniformAddGroup_of_addCommGroup`) and for compact
additive groups (see `IsUniformAddGroup.of_compactSpace`). -/]
/-
**IsTopologicalGroup.leftUniformSpace** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsTopologicalGroup.leftUniformSpace : UniformSpace G where uniformity
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def IsTopologicalGroup.leftUniformSpace : UniformSpace G where
  uniformity := comap (fun p : G × G => p.1⁻¹ * p.2) (𝓝 1)
  symm :=
    have : Tendsto (fun p : G × G ↦ (p.1⁻¹ * p.2)⁻¹) (comap (fun p : G × G ↦ p.1⁻¹ * p.2) (𝓝 1))
      (𝓝 1⁻¹) := tendsto_id.inv.comp tendsto_comap
    by simpa [tendsto_comap_iff]
  comp := Tendsto.le_comap fun U H ↦ by
    rcases exists_nhds_one_split H with ⟨V, V_nhds, V_mul⟩
    refine mem_map.2 (mem_of_superset (mem_lift' <| preimage_mem_comap V_nhds) ?_)
    rintro ⟨x, y⟩ ⟨z, hz₁, hz₂⟩
    simpa using V_mul _ hz₁ _ hz₂
  nhds_eq_comap_uniformity _ := by
    simp only [comap_comap, Function.comp_def, nhds_translation_inv_mul]

attribute [local instance] IsTopologicalGroup.leftUniformSpace

@[to_additive]
/-
**uniformity_eq_comap_nhds_one_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformity_eq_comap_nhds_one_left : 𝓤 G = comap (fun p : G × G => p.1⁻¹ * 
p.2) (𝓝 (1 : G))
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem uniformity_eq_comap_nhds_one_left :
    𝓤 G = comap (fun p : G × G => p.1⁻¹ * p.2) (𝓝 (1 : G)) :=
  rfl

end IsTopologicalGroup

section TopologicalCommGroup

universe u v w x

open Filter

variable (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]

section

attribute [local instance] IsTopologicalGroup.rightUniformSpace

variable {G}

@[to_additive]
/-
**isUniformGroup_of_commGroup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isUniformGroup_of_commGroup : IsUniformGroup G
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `uniformity_prod_eq_prod`：uniformity_prod_eq_prod [UniformSpace α] [Unifo
rmSpace β] : 𝓤 (α × β) = map (fun p : (α × α) × β × β => ((p.1.1, p.2.1), (p.1.2
, p.2.2))) (𝓤…
· 使用定理 `Filter.prod_comap_comap_eq`：prod_comap_comap_eq.{u, v, w, x} {α₁ : Type 
u} {α₂ : Type v} {β₁ : Type w} {β₂ : Type x} {f₁ : Filter α₁} {f₂ : Filter α₂} {
m₁ : β₁ -> α₁} {…
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `continuous_mul`：continuous_mul : Continuous fun p : M × M => p.1 * p.2
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `Continuous.fst`：Continuous.fst {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).1
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Continuous.fun_inv`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace G] [inst_2 : Inv G]   [ContinuousInv G] {f : 
X → G}, …
· 使用定理 `IsTopologicalGroup.toContinuousInv`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousInv G
· 使用定理 `Continuous.snd`：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).2
· 使用定理 `Filter.tendsto_comap`：tendsto_comap {f : α -> β} {x : Filter β} : Tendst
o f (comap f x) x
-/
theorem isUniformGroup_of_commGroup : IsUniformGroup G := by
  constructor
  have : (fun (x : (G × G) × (G × G)) ↦ x.1.2 * x.2.2⁻¹ * (x.2.1 * x.1.1⁻¹)) =
    (fun (p : G × G) ↦ p.1 * p.2⁻¹)
      ∘ (fun (p : (G × G) × (G × G)) ↦ (p.1.2 * p.1.1⁻¹, p.2.2 * p.2.1⁻¹)) := by
    ext x
    simp only [Function.comp_apply, mul_inv_rev, inv_inv]
    rw [mul_assoc, mul_comm x.2.2⁻¹, mul_comm x.2.1]
    simp [mul_assoc]
  simp only [UniformContinuous, div_eq_mul_inv, uniformity_prod_eq_prod,
    uniformity_eq_comap_nhds_one', prod_comap_comap_eq, ← nhds_prod_eq, tendsto_comap_iff,
    Function.comp_def, mul_inv_rev, inv_inv, tendsto_map'_iff]
  rw [this]
  apply Tendsto.comp ?_ tendsto_comap
  nth_rewrite 3 [show (1 : G) = 1 * 1⁻¹ by simp]
  apply Continuous.tendsto (by fun_prop)

alias comm_topologicalGroup_is_uniform := isUniformGroup_of_commGroup

end

@[to_additive]
/-
**IsUniformGroup.rightUniformSpace_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUniformGroup.rightUniformSpace_eq {G : Type*} [u : UniformSpace G] [Grou
p G] [IsUniformGroup G] : IsTopologicalGroup.rightUniformSpace G = u
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.ext`：∀ {α : Type ua} {u₁ u₂ : UniformSpace α}, uniformity α
 = uniformity α → u₁ = u₂
· 使用定理 `IsUniformGroup.to_topologicalGroup`：∀ {α : Type u_1} [inst : UniformSpac
e α] [inst_1 : Group α] [IsUniformGroup α], IsTopologicalGroup α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `uniformity_eq_comap_nhds_one'`：uniformity_eq_comap_nhds_one' : 𝓤 G = com
ap (fun p : G × G => p.2 * p.1⁻¹) (𝓝 (1 : G))
· 使用引理 `uniformity_eq_comap_mul_inv_nhds_one`：uniformity_eq_comap_mul_inv_nhds_o
ne : 𝓤 Gᵣ = comap (fun x : Gᵣ × Gᵣ => x.2 * x.1⁻¹) (𝓝 1)
-/
theorem IsUniformGroup.rightUniformSpace_eq {G : Type*} [u : UniformSpace G] [Group G]
    [IsUniformGroup G] : IsTopologicalGroup.rightUniformSpace G = u := by
  ext : 1
  rw [uniformity_eq_comap_nhds_one' G, uniformity_eq_comap_mul_inv_nhds_one]

end TopologicalCommGroup

