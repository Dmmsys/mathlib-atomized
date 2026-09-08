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

/-- Basic hypothesis to talk about a topological additive group. A topological additive group
over `M`, for example, is obtained by requiring the instances `AddGroup M` and
`ContinuousAdd M` and `ContinuousNeg M`. -/
/-
**ContinuousNeg** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(G : Type u) → [TopologicalSpace G] → [Neg G] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Basic hypothesis to talk about a topological additive group. A topological addit
ive group
over `M`, for example, is obtained by requiring the instances `AddGroup M` and
`ContinuousAdd M` and `ContinuousNeg M`.
-/
class ContinuousNeg (G : Type u) [TopologicalSpace G] [Neg G] : Prop where
  continuous_neg : Continuous fun a : G => -a

attribute [continuity, fun_prop] ContinuousNeg.continuous_neg

/-- Basic hypothesis to talk about a topological group. A topological group over `M`, for example,
is obtained by requiring the instances `Group M` and `ContinuousMul M` and
`ContinuousInv M`. -/
@[to_additive (attr := continuity)]
/-
**ContinuousInv** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(G : Type u) → [TopologicalSpace G] → [Inv G] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Basic hypothesis to talk about a topological group. A topological group over `M`
, for example,
is obtained by requiring the instances `Group M` and `ContinuousMul M` and
`ContinuousInv M`.
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
/-
**Filter.Tendsto.inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.inv {f : α -> G} {l : Filter α} {y : G} (h : Tendsto f l (𝓝
 y)) : Tendsto (fun x => (f x)⁻¹) l (𝓝 y⁻¹)
参数：h : Tendsto f l (𝓝 y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `ContinuousInv.continuous_inv`：∀ {G : Type u} {inst : TopologicalSpace G}
 {inst_1 : Inv G} [self : ContinuousInv G], Continuous fun a => a⁻¹
-/
theorem Filter.Tendsto.inv {f : α → G} {l : Filter α} {y : G} (h : Tendsto f l (𝓝 y)) :
    Tendsto (fun x => (f x)⁻¹) l (𝓝 y⁻¹) :=
  (continuous_inv.tendsto y).comp h

variable {f : X → G} {s : Set X} {x : X}

@[to_fun (attr := to_additive (attr := continuity, fun_prop))]
/-
**Continuous.inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.inv (hf : Continuous f) : Continuous f⁻¹
参数：hf : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `ContinuousInv.continuous_inv`：∀ {G : Type u} {inst : TopologicalSpace G}
 {inst_1 : Inv G} [self : ContinuousInv G], Continuous fun a => a⁻¹
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
/-
**ContinuousOn.inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.inv (hf : ContinuousOn f s) : ContinuousOn f⁻¹ s
参数：hf : ContinuousOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.inv`：∀ {G : Type u_1} {X : Type u_3} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace G] [inst_2 : Inv G]   [ContinuousInv G] {
f : X → G} {…
-/
theorem ContinuousOn.inv (hf : ContinuousOn f s) : ContinuousOn f⁻¹ s := fun x hx ↦
  (hf x hx).inv

end ContinuousInv

/-- A topological (additive) group is a group in which the addition and negation operations are
continuous.

When you declare an instance that does not already have a `UniformSpace` instance,
you should also provide an instance of `UniformSpace` and `IsUniformAddGroup` using
`IsTopologicalAddGroup.rightUniformSpace` and `isUniformAddGroup_of_addCommGroup`. -/
/-
**IsTopologicalAddGroup** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(G : Type u) → [TopologicalSpace G] → [AddGroup G] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A topological (additive) group is a group in which the addition and negation ope
rations are
continuous.

When you declare an instance that does not already have a `UniformSpace` instanc
e,
you should also provide an instance of `UniformSpace` and `IsUniformAddGroup` us
ing
`IsTopologicalAddGroup.rightUniformSpace` and `isUniformAddGroup_of_addCommGroup
`.
-/
class IsTopologicalAddGroup (G : Type u) [TopologicalSpace G] [AddGroup G] : Prop
    extends ContinuousAdd G, ContinuousNeg G

/-- A topological group is a group in which the multiplication and inversion operations are
continuous.

When you declare an instance that does not already have a `UniformSpace` instance,
you should also provide an instance of `UniformSpace` and `IsUniformGroup` using
`IsTopologicalGroup.rightUniformSpace` and `isUniformGroup_of_commGroup`. -/
@[to_additive]
/-
**IsTopologicalGroup** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(G : Type u_4) → [TopologicalSpace G] → [Group G] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A topological group is a group in which the multiplication and inversion operati
ons are
continuous.

When you declare an instance that does not already have a `UniformSpace` instanc
e,
you should also provide an instance of `UniformSpace` and `IsUniformGroup` using
`IsTopologicalGroup.rightUniformSpace` and `isUniformGroup_of_commGroup`.
-/
class IsTopologicalGroup (G : Type*) [TopologicalSpace G] [Group G] : Prop
    extends ContinuousMul G, ContinuousInv G

/-- A typeclass saying that `p : G × G ↦ p.1 - p.2` is a continuous function. This property
automatically holds for topological additive groups but it also holds, e.g., for `ℝ≥0`. -/
/-
**ContinuousSub** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(G : Type u_4) → [TopologicalSpace G] → [Sub G] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A typeclass saying that `p : G × G ↦ p.1 - p.2` is a continuous function. This p
roperty
automatically holds for topological additive groups but it also holds, e.g., for
 `ℝ≥0`.
-/
class ContinuousSub (G : Type*) [TopologicalSpace G] [Sub G] : Prop where
  continuous_sub : Continuous fun p : G × G => p.1 - p.2

/-- A typeclass saying that `p : G × G ↦ p.1 / p.2` is a continuous function. This property
automatically holds for topological groups. Lemmas using this class have primes.
The unprimed version is for `GroupWithZero`. -/
@[to_additive existing]
/-
**ContinuousDiv** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(G : Type u_4) → [TopologicalSpace G] → [Div G] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A typeclass saying that `p : G × G ↦ p.1 / p.2` is a continuous function. This p
roperty
automatically holds for topological groups. Lemmas using this class have primes.
The unprimed version is for `GroupWithZero`.
-/
class ContinuousDiv (G : Type*) [TopologicalSpace G] [Div G] : Prop where
  continuous_div' : Continuous fun p : G × G => p.1 / p.2

-- see Note [lower instance priority]
@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) IsTopologicalGroup.to_continuousDiv
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] : ContinuousDiv G where
  continuous_div' := by
    simp only [div_eq_mul_inv]
    exact continuous_mul.comp₂ continuous_fst <| continuous_inv.comp continuous_snd

export ContinuousSub (continuous_sub)
export ContinuousDiv (continuous_div')

section ContinuousDiv

variable [TopologicalSpace G] [Div G] [ContinuousDiv G]

@[to_additive sub]
/-
**Filter.Tendsto.div'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.div' {f g : α -> G} {l : Filter α} {a b : G} (hf : Tendsto 
f l (𝓝 a)) (hg : Tendsto g l (𝓝 b)) : Tendsto (fun x => f x / g x) l (𝓝 (a / b))
参数：hf : Tendsto f l (𝓝 a)；hg : Tendsto g l (𝓝 b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `ContinuousDiv.continuous_div'`：∀ {G : Type u_4} {inst : TopologicalSpace
 G} {inst_1 : Div G} [self : ContinuousDiv G], Continuous fun p => p.1 / p.2
· 使用定理 `Filter.Tendsto.prodMk_nhds`：Filter.Tendsto.prodMk_nhds {γ} {x : X} {y : 
Y} {f : Filter γ} {mx : γ -> X} {my : γ -> Y} (hx : Tendsto mx f (𝓝 x)) (hy : Te
ndsto my f (𝓝 y)…
-/
theorem Filter.Tendsto.div' {f g : α → G} {l : Filter α} {a b : G} (hf : Tendsto f l (𝓝 a))
    (hg : Tendsto g l (𝓝 b)) : Tendsto (fun x => f x / g x) l (𝓝 (a / b)) :=
  (continuous_div'.tendsto (a, b)).comp (hf.prodMk_nhds hg)

variable {f g : X → G} {s : Set X} {x : X}

@[to_additive (attr := to_fun (attr := fun_prop)) sub]
nonrec theorem ContinuousAt.div' (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    ContinuousAt (f / g) x :=
  hf.div' hg

@[to_additive (attr := to_fun (attr := fun_prop)) sub]
/-
**ContinuousWithinAt.div'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.div' (hf : ContinuousWithinAt f s x) (hg : ContinuousWi
thinAt g s x) : ContinuousWithinAt (f / g) s x
参数：hf : ContinuousWithinAt f s x；hg : ContinuousWithinAt g s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.div'`：Filter.Tendsto.div' {f g : α -> G} {l : Filter α} {
a b : G} (hf : Tendsto f l (𝓝 a)) (hg : Tendsto g l (𝓝 b)) : Tendsto (fun x => f
 x / g x)…
-/
theorem ContinuousWithinAt.div' (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x) :
    ContinuousWithinAt (f / g) s x :=
  Filter.Tendsto.div' hf hg

@[to_additive (attr := to_fun (attr := fun_prop)) sub]
/-
**ContinuousOn.div'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.div' (hf : ContinuousOn f s) (hg : ContinuousOn g s) : Contin
uousOn (f / g) s
参数：hf : ContinuousOn f s；hg : ContinuousOn g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.div'`：ContinuousWithinAt.div' (hf : ContinuousWithinA
t f s x) (hg : ContinuousWithinAt g s x) : ContinuousWithinAt (f / g) s x
-/
theorem ContinuousOn.div' (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (f / g) s := fun x hx => (hf x hx).div' (hg x hx)

@[to_additive (attr := to_fun (attr := continuity, fun_prop)) sub]
/-
**Continuous.div'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.div' (hf : Continuous f) (hg : Continuous g) : Continuous (f / 
g)
参数：hf : Continuous f；hg : Continuous g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp₂`：Continuous.comp₂ {g : X × Y -> Z} (hg : Continuous g) 
{e : W -> X} (he : Continuous e) {f : W -> Y} (hf : Continuous f) : Continuous f
un w =…
· 使用定理 `ContinuousDiv.continuous_div'`：∀ {G : Type u_4} {inst : TopologicalSpace
 G} {inst_1 : Div G} [self : ContinuousDiv G], Continuous fun p => p.1 / p.2
-/
theorem Continuous.div' (hf : Continuous f) (hg : Continuous g) : Continuous (f / g) :=
  continuous_div'.comp₂ hf hg

end ContinuousDiv

