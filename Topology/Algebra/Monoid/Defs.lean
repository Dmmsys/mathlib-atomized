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

/-- Basic hypothesis to talk about a topological additive monoid or a topological additive
semigroup. A topological additive monoid over `M`, for example, is obtained by requiring both the
instances `AddMonoid M` and `ContinuousAdd M`.

Continuity in each argument separately can be stated using `SeparatelyContinuousAdd α`. If one wants
only continuity in either the left or right argument, but not both one can use
`ContinuousConstVAdd α α`/`ContinuousConstVAdd αᵐᵒᵖ α`. -/
/-
**ContinuousAdd** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(M : Type u_1) → [TopologicalSpace M] → [Add M] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Basic hypothesis to talk about a topological additive monoid or a topological ad
ditive
semigroup. A topological additive monoid over `M`, for example, is obtained by r
equiring both the
instances `AddMonoid M` and `ContinuousAdd M`.

Continuity in each argument separately can be stated using `SeparatelyContinuous
Add α`. If one wants
only continuity in either the left or right argument, but not both one can use
`ContinuousConstVAdd α α`/`ContinuousConstVAdd αᵐᵒᵖ α`.
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
/-
**ContinuousMul** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(M : Type u_1) → [TopologicalSpace M] → [Mul M] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Basic hypothesis to talk about a topological monoid or a topological semigroup.
A topological monoid over `M`, for example, is obtained by requiring both the in
stances `Monoid M`
and `ContinuousMul M`.

Continuity in each argument separately can be stated using `SeparatelyContinuous
Mul α`. If one wants
only continuity in either the left or right argument, but not both one can use
`ContinuousConstSMul α α`/`ContinuousConstSMul αᵐᵒᵖ α`.
-/
class ContinuousMul (M : Type*) [TopologicalSpace M] [Mul M] : Prop where
  continuous_mul : Continuous fun p : M × M => p.1 * p.2

/-- A type class encoding that addition is continuous in each argument. This is weaker than
`ContinuousAdd`. -/
/-
**SeparatelyContinuousAdd** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(M : Type u_1) → [TopologicalSpace M] → [Add M] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type class encoding that addition is continuous in each argument. This is weak
er than
`ContinuousAdd`.
-/
class SeparatelyContinuousAdd (M : Type*) [TopologicalSpace M] [Add M] : Prop where
  continuous_const_add {a : M} : Continuous (a + ·)
  continuous_add_const {a : M} : Continuous (· + a)

/-- A type class encoding that addition is continuous in each argument. This is weaker than
`ContinuousMul`. -/
@[to_additive]
/-
**SeparatelyContinuousMul** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(M : Type u_1) → [TopologicalSpace M] → [Mul M] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type class encoding that addition is continuous in each argument. This is weak
er than
`ContinuousMul`.
-/
class SeparatelyContinuousMul (M : Type*) [TopologicalSpace M] [Mul M] : Prop where
  continuous_const_mul {a : M} : Continuous (a * ·)
  continuous_mul_const {a : M} : Continuous (· * a)

section ContinuousMul

variable {M : Type*} [TopologicalSpace M] [Mul M] [ContinuousMul M]

@[to_additive (attr := continuity, fun_prop)]
/-
**continuous_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_mul : Continuous fun p : M × M => p.1 * p.2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMul.continuous_mul`：∀ {M : Type u_1} {inst : TopologicalSpace 
M} {inst_1 : Mul M} [self : ContinuousMul M], Continuous fun p => p.1 * p.2
-/
theorem continuous_mul : Continuous fun p : M × M => p.1 * p.2 :=
  ContinuousMul.continuous_mul

@[to_additive]
/-
**Filter.Tendsto.mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.mul {α : Type*} {f g : α -> M} {x : Filter α} {a b : M} (hf
 : Tendsto f x (𝓝 a)) (hg : Tendsto g x (𝓝 b)) : Tendsto (fun x => f x * g x) x 
(𝓝 (a * b))
参数：hf : Tendsto f x (𝓝 a)；hg : Tendsto g x (𝓝 b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `continuous_mul`：continuous_mul : Continuous fun p : M × M => p.1 * p.2
· 使用定理 `Filter.Tendsto.prodMk_nhds`：Filter.Tendsto.prodMk_nhds {γ} {x : X} {y : 
Y} {f : Filter γ} {mx : γ -> X} {my : γ -> Y} (hx : Tendsto mx f (𝓝 x)) (hy : Te
ndsto my f (𝓝 y)…
-/
theorem Filter.Tendsto.mul {α : Type*} {f g : α → M} {x : Filter α} {a b : M}
    (hf : Tendsto f x (𝓝 a)) (hg : Tendsto g x (𝓝 b)) : Tendsto (fun x ↦ f x * g x) x (𝓝 (a * b)) :=
  (continuous_mul.tendsto _).comp (hf.prodMk_nhds hg)

@[to_additive]
/-
**Filter.tendsto_of_div_tendsto_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Filter.tendsto_of_div_tendsto_one {α E : Type*} [CommGroup E] [Topological
Space E] [ContinuousMul E] {f g : α -> E} (m : E) {x : Filter α} (hf : Tendsto f
 x (𝓝 m)) (hfg : Tendsto (g / f) x (𝓝 1)) : Tendsto g x (𝓝 m)
参数：m : E；hf : Tendsto f x (𝓝 m)；hfg : Tendsto (g / f) x (𝓝 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_div_cancel`：mul_div_cancel (a b : G) : a * (b / a) = b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Filter.Tendsto.mul`：Filter.Tendsto.mul {α : Type*} {f g : α -> M} {x : F
ilter α} {a b : M} (hf : Tendsto f x (𝓝 a)) (hg : Tendsto g x (𝓝 b)) : Tendsto (
fun x =>…
-/
lemma Filter.tendsto_of_div_tendsto_one {α E : Type*} [CommGroup E] [TopologicalSpace E]
    [ContinuousMul E] {f g : α → E} (m : E) {x : Filter α} (hf : Tendsto f x (𝓝 m))
    (hfg : Tendsto (g / f) x (𝓝 1)) : Tendsto g x (𝓝 m) := by
  simpa using Tendsto.mul hf hfg

variable {X : Type*} [TopologicalSpace X] {f g : X → M} {s : Set X} {x : X}

@[to_fun (attr := to_additive (attr := continuity, fun_prop))]
/-
**Continuous.mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.mul (hf : Continuous f) (hg : Continuous g) : Continuous (f * g
)
参数：hf : Continuous f；hg : Continuous g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp₂`：Continuous.comp₂ {g : X × Y -> Z} (hg : Continuous g) 
{e : W -> X} (he : Continuous e) {f : W -> Y} (hf : Continuous f) : Continuous f
un w =…
· 使用定理 `continuous_mul`：continuous_mul : Continuous fun p : M × M => p.1 * p.2
-/
theorem Continuous.mul (hf : Continuous f) (hg : Continuous g) :
    Continuous (f * g) :=
  continuous_mul.comp₂ hf hg

@[to_fun (attr := to_additive (attr := fun_prop))]
/-
**ContinuousWithinAt.mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.mul (hf : ContinuousWithinAt f s x) (hg : ContinuousWit
hinAt g s x) : ContinuousWithinAt (f * g) s x
参数：hf : ContinuousWithinAt f s x；hg : ContinuousWithinAt g s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.mul`：Filter.Tendsto.mul {α : Type*} {f g : α -> M} {x : F
ilter α} {a b : M} (hf : Tendsto f x (𝓝 a)) (hg : Tendsto g x (𝓝 b)) : Tendsto (
fun x =>…
-/
theorem ContinuousWithinAt.mul (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x) :
    ContinuousWithinAt (f * g) s x :=
  Filter.Tendsto.mul hf hg

@[to_fun (attr := to_additive (attr := fun_prop))]
/-
**ContinuousAt.mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousAt.mul (hf : ContinuousAt f x) (hg : ContinuousAt g x) : Continu
ousAt (f * g) x
参数：hf : ContinuousAt f x；hg : ContinuousAt g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.mul`：Filter.Tendsto.mul {α : Type*} {f g : α -> M} {x : F
ilter α} {a b : M} (hf : Tendsto f x (𝓝 a)) (hg : Tendsto g x (𝓝 b)) : Tendsto (
fun x =>…
-/
theorem ContinuousAt.mul (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    ContinuousAt (f * g) x :=
  Filter.Tendsto.mul hf hg

@[to_fun (attr := to_additive (attr := fun_prop))]
/-
**ContinuousOn.mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.mul (hf : ContinuousOn f s) (hg : ContinuousOn g s) : Continu
ousOn (f * g) s
参数：hf : ContinuousOn f s；hg : ContinuousOn g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.mul`：ContinuousWithinAt.mul (hf : ContinuousWithinAt 
f s x) (hg : ContinuousWithinAt g s x) : ContinuousWithinAt (f * g) s x
-/
theorem ContinuousOn.mul (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (f * g) s := fun x hx ↦
  (hf x hx).mul (hg x hx)

end ContinuousMul

section

variable {M : Type*} [TopologicalSpace M] [Mul M]

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [ContinuousMul M] : SeparatelyContinuousMul M where
  continuous_const_mul := continuous_const.mul continuous_id
  continuous_mul_const := continuous_id.mul continuous_const

variable [SeparatelyContinuousMul M]

@[to_additive (attr := continuity, fun_prop)]
/-
**continuous_const_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_const_mul (m : M) : Continuous (m * ·)
参数：m : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeparatelyContinuousMul.continuous_const_mul`：∀ {M : Type u_1} {inst : T
opologicalSpace M} {inst_1 : Mul M} [self : SeparatelyContinuousMul M] {a : M}, 
  Continuous fun x => a * x
-/
theorem continuous_const_mul (m : M) : Continuous (m * ·) :=
  SeparatelyContinuousMul.continuous_const_mul

@[to_additive (attr := continuity, fun_prop)]
/-
**continuous_mul_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_mul_const (m : M) : Continuous (· * m)
参数：m : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeparatelyContinuousMul.continuous_mul_const`：∀ {M : Type u_1} {inst : T
opologicalSpace M} {inst_1 : Mul M} [self : SeparatelyContinuousMul M] {a : M}, 
  Continuous fun x => x * a
-/
theorem continuous_mul_const (m : M) : Continuous (· * m) :=
  SeparatelyContinuousMul.continuous_mul_const

@[to_additive]
/-
**Filter.Tendsto.const_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.const_mul {α : Type*} {f : α -> M} {x : Filter α} {a : M} (
b : M) (hf : Tendsto f x (𝓝 a)) : Tendsto (b * f ·) x (𝓝 (b * a))
参数：b : M；hf : Tendsto f x (𝓝 a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `continuous_const_mul`：continuous_const_mul (m : M) : Continuous (m * ·)
-/
theorem Filter.Tendsto.const_mul {α : Type*} {f : α → M} {x : Filter α} {a : M}
    (b : M) (hf : Tendsto f x (𝓝 a)) : Tendsto (b * f ·) x (𝓝 (b * a)) :=
  continuous_const_mul b |>.tendsto _ |>.comp hf

@[to_additive]
/-
**Filter.Tendsto.mul_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.mul_const {α : Type*} {f : α -> M} {x : Filter α} {a : M} (
b : M) (hf : Tendsto f x (𝓝 a)) : Tendsto (f · * b) x (𝓝 (a * b))
参数：b : M；hf : Tendsto f x (𝓝 a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `continuous_mul_const`：continuous_mul_const (m : M) : Continuous (· * m)
-/
theorem Filter.Tendsto.mul_const {α : Type*} {f : α → M} {x : Filter α} {a : M}
    (b : M) (hf : Tendsto f x (𝓝 a)) : Tendsto (f · * b) x (𝓝 (a * b)) :=
  continuous_mul_const b |>.tendsto _ |>.comp hf

variable {X : Type*} [TopologicalSpace X] {f g : X → M} {s : Set X} {x : X}

@[to_additive (attr := continuity, fun_prop)]
/-
**Continuous.mul_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.mul_const (hf : Continuous f) (b : M) : Continuous (f · * b)
参数：hf : Continuous f；b : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_mul_const`：continuous_mul_const (m : M) : Continuous (· * m)
-/
theorem Continuous.mul_const (hf : Continuous f) (b : M) : Continuous (f · * b) :=
  continuous_mul_const b |>.comp hf

@[to_additive (attr := continuity, fun_prop)]
/-
**Continuous.const_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.const_mul (hf : Continuous f) (b : M) : Continuous (b * f ·)
参数：hf : Continuous f；b : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_const_mul`：continuous_const_mul (m : M) : Continuous (m * ·)
-/
theorem Continuous.const_mul (hf : Continuous f) (b : M) : Continuous (b * f ·) :=
  continuous_const_mul b |>.comp hf

@[to_additive (attr := fun_prop)]
/-
**ContinuousWithinAt.mul_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.mul_const (hf : ContinuousWithinAt f s x) (b : M) : Con
tinuousWithinAt (f · * b) s x
参数：hf : ContinuousWithinAt f s x；b : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.mul_const`：Filter.Tendsto.mul_const {α : Type*} {f : α ->
 M} {x : Filter α} {a : M} (b : M) (hf : Tendsto f x (𝓝 a)) : Tendsto (f · * b) 
x (𝓝 (a * b))
-/
theorem ContinuousWithinAt.mul_const (hf : ContinuousWithinAt f s x) (b : M) :
    ContinuousWithinAt (f · * b) s x :=
  Filter.Tendsto.mul_const b hf

@[to_additive (attr := fun_prop)]
/-
**ContinuousWithinAt.const_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.const_mul (hf : ContinuousWithinAt f s x) (b : M) : Con
tinuousWithinAt (b * f ·) s x
参数：hf : ContinuousWithinAt f s x；b : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.const_mul`：Filter.Tendsto.const_mul {α : Type*} {f : α ->
 M} {x : Filter α} {a : M} (b : M) (hf : Tendsto f x (𝓝 a)) : Tendsto (b * f ·) 
x (𝓝 (b * a))
-/
theorem ContinuousWithinAt.const_mul (hf : ContinuousWithinAt f s x) (b : M) :
    ContinuousWithinAt (b * f ·) s x :=
  Filter.Tendsto.const_mul b hf

@[to_additive (attr := fun_prop)]
/-
**ContinuousAt.mul_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousAt.mul_const (hf : ContinuousAt f x) (b : M) : ContinuousAt (f ·
 * b) x
参数：hf : ContinuousAt f x；b : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.mul_const`：Filter.Tendsto.mul_const {α : Type*} {f : α ->
 M} {x : Filter α} {a : M} (b : M) (hf : Tendsto f x (𝓝 a)) : Tendsto (f · * b) 
x (𝓝 (a * b))
-/
theorem ContinuousAt.mul_const (hf : ContinuousAt f x) (b : M) :
    ContinuousAt (f · * b) x :=
  Filter.Tendsto.mul_const b hf

@[to_additive (attr := fun_prop)]
/-
**ContinuousAt.const_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousAt.const_mul (hf : ContinuousAt f x) (b : M) : ContinuousAt (b *
 f ·) x
参数：hf : ContinuousAt f x；b : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.const_mul`：Filter.Tendsto.const_mul {α : Type*} {f : α ->
 M} {x : Filter α} {a : M} (b : M) (hf : Tendsto f x (𝓝 a)) : Tendsto (b * f ·) 
x (𝓝 (b * a))
-/
theorem ContinuousAt.const_mul (hf : ContinuousAt f x) (b : M) :
    ContinuousAt (b * f ·) x :=
  Filter.Tendsto.const_mul b hf

@[to_additive (attr := fun_prop)]
/-
**ContinuousOn.mul_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.mul_const (hf : ContinuousOn f s) (b : M) : ContinuousOn (f ·
 * b) s
参数：hf : ContinuousOn f s；b : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.mul_const`：ContinuousWithinAt.mul_const (hf : Continu
ousWithinAt f s x) (b : M) : ContinuousWithinAt (f · * b) s x
-/
theorem ContinuousOn.mul_const (hf : ContinuousOn f s) (b : M) :
    ContinuousOn (f · * b) s :=
  fun x hx ↦ (hf x hx).mul_const b

@[to_additive (attr := fun_prop)]
/-
**ContinuousOn.const_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.const_mul (hf : ContinuousOn f s) (b : M) : ContinuousOn (b *
 f ·) s
参数：hf : ContinuousOn f s；b : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.const_mul`：ContinuousWithinAt.const_mul (hf : Continu
ousWithinAt f s x) (b : M) : ContinuousWithinAt (b * f ·) s x
-/
theorem ContinuousOn.const_mul (hf : ContinuousOn f s) (b : M) :
    ContinuousOn (b * f ·) s :=
  fun x hx ↦ (hf x hx).const_mul b
