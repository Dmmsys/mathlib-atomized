/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.MeasureTheory.Measure.AEMeasurable

/-!
# Typeclasses for measurability of operations

In this file we define classes `MeasurableMul` etc. and prove dot-style lemmas
(`Measurable.mul`, `AEMeasurable.mul` etc). For binary operations we define two typeclasses:

- `MeasurableMul` says that both left and right multiplication are measurable;
- `MeasurableMul₂` says that `fun p : α × α => p.1 * p.2` is measurable,

and similarly for other binary operations. The reason for introducing these classes is that in case
of topological space `α` equipped with the Borel `σ`-algebra, instances for `MeasurableMul₂`
etc. require `α` to have a second countable topology.

We define separate classes for `MeasurableDiv`/`MeasurableSub`
because on some types (e.g., `ℕ`, `ℝ≥0∞`) division and/or subtraction are not defined as `a * b⁻¹` /
`a + (-b)`.

For instances relating, e.g., `ContinuousMul` to `MeasurableMul` see file
`MeasureTheory.BorelSpace`.

## Implementation notes

For the heuristics of `@[to_additive]` it is important that the type with a multiplication
(or another multiplicative operation) is the first (implicit) argument of all declarations.

## Tags

measurable function, arithmetic operator

## TODO

* Uniformize the treatment of `pow` and `smul`.
* Use `@[to_additive]` to send `MeasurablePow` to `MeasurableSMul₂`.
* This might require changing the definition (swapping the arguments in the function that is
  in the conclusion of `MeasurableSMul`.)
-/

public section

open MeasureTheory
open scoped Pointwise

universe u v
variable {α : Type*}

/-!
### Binary operations: `(· + ·)`, `(· * ·)`, `(· - ·)`, `(· / ·)`
-/


/-- We say that a type has `MeasurableAdd` if `(c + ·)` and `(· + c)` are measurable functions.
For a typeclass assuming measurability of `uncurry (· + ·)` see `MeasurableAdd₂`. -/
/-
**MeasurableAdd** 是 Mathlib 中的一个类，位于命名空间 ``。
形式化陈述：MeasurableAdd (M : Type*) [MeasurableSpace M] [Add M] : Prop where measura
ble_const_add : forall c : M, Measurable (c + ·)
参数：M : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that a type has `MeasurableAdd` if `(c + ·)` and `(· + c)` are measurable
 functions.
For a typeclass assuming measurability of `uncurry (· + ·)` see `MeasurableAdd₂`
.
-/
class MeasurableAdd (M : Type*) [MeasurableSpace M] [Add M] : Prop where
  measurable_const_add : ∀ c : M, Measurable (c + ·) := by intro; fun_prop
  measurable_add_const : ∀ c : M, Measurable (· + c) := by intro; fun_prop

export MeasurableAdd (measurable_const_add measurable_add_const)

/-- We say that a type has `MeasurableAdd₂` if `uncurry (· + ·)` is a measurable function.
For a typeclass assuming measurability of `(c + ·)` and `(· + c)` see `MeasurableAdd`. -/
/-
**MeasurableAdd** 是 Mathlib 中的一个类，位于命名空间 ``。
形式化陈述：MeasurableAdd (M : Type*) [MeasurableSpace M] [Add M] : Prop where measura
ble_const_add : forall c : M, Measurable (c + ·)
参数：M : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that a type has `MeasurableAdd₂` if `uncurry (· + ·)` is a measurable fun
ction.
For a typeclass assuming measurability of `(c + ·)` and `(· + c)` see `Measurabl
eAdd`.
-/
class MeasurableAdd₂ (M : Type*) [MeasurableSpace M] [Add M] : Prop where
  measurable_add : Measurable fun p : M × M => p.1 + p.2

export MeasurableAdd₂ (measurable_add)

/-- We say that a type has `MeasurableMul` if `(c * ·)` and `(· * c)` are measurable functions.
For a typeclass assuming measurability of `uncurry (*)` see `MeasurableMul₂`. -/
@[to_additive]
/-
**MeasurableMul** 是 Mathlib 中的一个类，位于命名空间 ``。
形式化陈述：MeasurableMul (M : Type*) [MeasurableSpace M] [Mul M] : Prop where measura
ble_const_mul : forall c : M, Measurable (c * ·)
参数：M : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that a type has `MeasurableMul` if `(c * ·)` and `(· * c)` are measurable
 functions.
For a typeclass assuming measurability of `uncurry (*)` see `MeasurableMul₂`.
-/
class MeasurableMul (M : Type*) [MeasurableSpace M] [Mul M] : Prop where
  measurable_const_mul : ∀ c : M, Measurable (c * ·) := by intro; fun_prop
  measurable_mul_const : ∀ c : M, Measurable (· * c) := by intro; fun_prop

export MeasurableMul (measurable_const_mul measurable_mul_const)

/-- We say that a type has `MeasurableMul₂` if `uncurry (· * ·)` is a measurable function.
For a typeclass assuming measurability of `(c * ·)` and `(· * c)` see `MeasurableMul`. -/
@[to_additive MeasurableAdd₂]
/-
**MeasurableMul** 是 Mathlib 中的一个类，位于命名空间 ``。
形式化陈述：MeasurableMul (M : Type*) [MeasurableSpace M] [Mul M] : Prop where measura
ble_const_mul : forall c : M, Measurable (c * ·)
参数：M : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that a type has `MeasurableMul₂` if `uncurry (· * ·)` is a measurable fun
ction.
For a typeclass assuming measurability of `(c * ·)` and `(· * c)` see `Measurabl
eMul`.
-/
class MeasurableMul₂ (M : Type*) [MeasurableSpace M] [Mul M] : Prop where
  measurable_mul : Measurable fun p : M × M => p.1 * p.2

export MeasurableMul₂ (measurable_mul)

section Mul

variable {M α β : Type*} [MeasurableSpace M] [Mul M] {m : MeasurableSpace α}
  {mβ : MeasurableSpace β} {f g : α → M} {μ : Measure α}

@[to_additive (attr := fun_prop)]
/-
**Measurable.const_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.const_mul [MeasurableMul M] (hf : Measurable f) (c : M) : Measu
rable fun x => c * f x
参数：hf : Measurable f；c : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `MeasurableMul.measurable_const_mul`：∀ {M : Type u_2} {inst : MeasurableS
pace M} {inst_1 : Mul M} [self : MeasurableMul M] (c : M), Measurable fun x => c
 * x
-/
theorem Measurable.const_mul [MeasurableMul M] (hf : Measurable f) (c : M) :
    Measurable fun x => c * f x :=
  (measurable_const_mul c).comp hf

@[to_additive (attr := fun_prop)]
/-
**AEMeasurable.const_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AEMeasurable.const_mul [MeasurableMul M] (hf : AEMeasurable f μ) (c : M) :
 AEMeasurable (fun x => c * f x) μ
参数：hf : AEMeasurable f μ；c : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp_aemeasurable`：Measurable.comp_aemeasurable [MeasurableSp
ace δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) : A
EMeasurable (g ∘ f…
· 使用定理 `MeasurableMul.measurable_const_mul`：∀ {M : Type u_2} {inst : MeasurableS
pace M} {inst_1 : Mul M} [self : MeasurableMul M] (c : M), Measurable fun x => c
 * x
-/
theorem AEMeasurable.const_mul [MeasurableMul M] (hf : AEMeasurable f μ) (c : M) :
    AEMeasurable (fun x => c * f x) μ :=
  (MeasurableMul.measurable_const_mul c).comp_aemeasurable hf

@[to_additive (attr := fun_prop)]
/-
**Measurable.mul_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.mul_const [MeasurableMul M] (hf : Measurable f) (c : M) : Measu
rable fun x => f x * c
参数：hf : Measurable f；c : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `MeasurableMul.measurable_mul_const`：∀ {M : Type u_2} {inst : MeasurableS
pace M} {inst_1 : Mul M} [self : MeasurableMul M] (c : M), Measurable fun x => x
 * c
-/
theorem Measurable.mul_const [MeasurableMul M] (hf : Measurable f) (c : M) :
    Measurable fun x => f x * c :=
  (measurable_mul_const c).comp hf

@[to_additive (attr := fun_prop)]
/-
**AEMeasurable.mul_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AEMeasurable.mul_const [MeasurableMul M] (hf : AEMeasurable f μ) (c : M) :
 AEMeasurable (fun x => f x * c) μ
参数：hf : AEMeasurable f μ；c : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp_aemeasurable`：Measurable.comp_aemeasurable [MeasurableSp
ace δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) : A
EMeasurable (g ∘ f…
· 使用定理 `MeasurableMul.measurable_mul_const`：∀ {M : Type u_2} {inst : MeasurableS
pace M} {inst_1 : Mul M} [self : MeasurableMul M] (c : M), Measurable fun x => x
 * c
-/
theorem AEMeasurable.mul_const [MeasurableMul M] (hf : AEMeasurable f μ) (c : M) :
    AEMeasurable (fun x => f x * c) μ :=
  (measurable_mul_const c).comp_aemeasurable hf

@[to_fun (attr := to_additive (attr := fun_prop))]
/-
**Measurable.mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.mul [MeasurableMul₂ M] (hf : Measurable f) (hg : Measurable g) 
: Measurable (f * g)
参数：hf : Measurable f；hg : Measurable g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `MeasurableMul₂.measurable_mul`：∀ {M : Type u_2} {inst : MeasurableSpace 
M} {inst_1 : Mul M} [self : MeasurableMul₂ M], Measurable fun p => p.1 * p.2
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
-/
theorem Measurable.mul [MeasurableMul₂ M] (hf : Measurable f) (hg : Measurable g) :
    Measurable (f * g) :=
  measurable_mul.comp (hf.prodMk hg)

/-- Compositional version of `Measurable.mul` for use by `fun_prop`. -/
@[to_additive (attr := fun_prop)
/-- Compositional version of `Measurable.add` for use by `fun_prop`. -/]
/-
**Measurable.mul'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Measurable.mul' [MeasurableMul₂ M] {f g : α -> β -> M} {h : α -> β} (hf : 
Measurable ↿f) (hg : Measurable ↿g) (hh : Measurable h) : Measurable fun a => (f
 a * g a) (h a)
参数：hf : Measurable ↿f；hg : Measurable ↿g；hh : Measurable h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.fun_mul`：∀ {M : Type u_2} {α : Type u_3} [inst : MeasurableSp
ace M] [inst_1 : Mul M] {m : MeasurableSpace α} {f g : α → M}   [MeasurableMul₂ 
M], Meas…
· 使用定理 `Measurable.fun_comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x :
 MeasurableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β
 → γ} {f …
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
-/
lemma Measurable.mul' [MeasurableMul₂ M] {f g : α → β → M} {h : α → β} (hf : Measurable ↿f)
    (hg : Measurable ↿g) (hh : Measurable h) : Measurable fun a ↦ (f a * g a) (h a) := by
  dsimp; fun_prop

@[to_fun (attr := to_additive (attr := fun_prop))]
/-
**AEMeasurable.mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AEMeasurable.mul [MeasurableMul₂ M] (hf : AEMeasurable f μ) (hg : AEMeasur
able g μ) : AEMeasurable (f * g) μ
参数：hf : AEMeasurable f μ；hg : AEMeasurable g μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp_aemeasurable`：Measurable.comp_aemeasurable [MeasurableSp
ace δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) : A
EMeasurable (g ∘ f…
· 使用定理 `MeasurableMul₂.measurable_mul`：∀ {M : Type u_2} {inst : MeasurableSpace 
M} {inst_1 : Mul M} [self : MeasurableMul₂ M], Measurable fun p => p.1 * p.2
· 使用定理 `AEMeasurable.prodMk`：prodMk {f : α -> β} {g : α -> γ} (hf : AEMeasurable
 f μ) (hg : AEMeasurable g μ) : AEMeasurable (fun x => (f x, g x)) μ
-/
theorem AEMeasurable.mul [MeasurableMul₂ M] (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    AEMeasurable (f * g) μ :=
  measurable_mul.comp_aemeasurable (hf.prodMk hg)

@[deprecated (since := "2026-06-26")] alias AEMeasurable.mul' := AEMeasurable.mul
@[deprecated (since := "2026-06-26")] alias AEMeasurable.add' := AEMeasurable.add

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) MeasurableMul₂.toMeasurableMul [MeasurableMul₂ M] :
    MeasurableMul M where

@[to_additive]
/-
**Pi.measurableMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.measurableMul {ι : Type*} {α : ι -> Type*} [forall i, Mul (α i)] [foral
l i, MeasurableSpace (α i)] [forall i, MeasurableMul (α i)] : MeasurableMul (for
all i, α i)
参数：α i；α i；α i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `measurable_pi_iff`：measurable_pi_iff {g : α -> forall a, X a} : Measurab
le g ↔ forall a, Measurable fun x => g x a
· 使用定理 `Measurable.const_mul`：Measurable.const_mul [MeasurableMul M] (hf : Measu
rable f) (c : M) : Measurable fun x => c * f x
· 使用定理 `measurable_pi_apply`：measurable_pi_apply (a : δ) : Measurable fun f : fo
rall a, X a => f a
· 使用定理 `Measurable.mul_const`：Measurable.mul_const [MeasurableMul M] (hf : Measu
rable f) (c : M) : Measurable fun x => f x * c
-/
instance Pi.measurableMul {ι : Type*} {α : ι → Type*} [∀ i, Mul (α i)]
    [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableMul (α i)] : MeasurableMul (∀ i, α i) :=
  ⟨fun _ => measurable_pi_iff.mpr fun i => (measurable_pi_apply i).const_mul _, fun _ =>
    measurable_pi_iff.mpr fun i => (measurable_pi_apply i).mul_const _⟩

@[to_additive Pi.measurableAdd₂]
/-
**Pi.measurableMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.measurableMul {ι : Type*} {α : ι -> Type*} [forall i, Mul (α i)] [foral
l i, MeasurableSpace (α i)] [forall i, MeasurableMul (α i)] : MeasurableMul (for
all i, α i)
参数：α i；α i；α i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `measurable_pi_iff`：measurable_pi_iff {g : α -> forall a, X a} : Measurab
le g ↔ forall a, Measurable fun x => g x a
· 使用定理 `Measurable.const_mul`：Measurable.const_mul [MeasurableMul M] (hf : Measu
rable f) (c : M) : Measurable fun x => c * f x
· 使用定理 `measurable_pi_apply`：measurable_pi_apply (a : δ) : Measurable fun f : fo
rall a, X a => f a
· 使用定理 `Measurable.mul_const`：Measurable.mul_const [MeasurableMul M] (hf : Measu
rable f) (c : M) : Measurable fun x => f x * c
-/
instance Pi.measurableMul₂ {ι : Type*} {α : ι → Type*} [∀ i, Mul (α i)]
    [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableMul₂ (α i)] : MeasurableMul₂ (∀ i, α i) :=
  ⟨measurable_pi_iff.mpr fun _ => measurable_fst.eval.mul measurable_snd.eval⟩

end Mul

/-- A version of `measurable_div_const` that assumes `MeasurableMul` instead of
  `MeasurableDiv`. This can be nice to avoid unnecessary type-class assumptions. -/
@[to_additive /-- A version of `measurable_sub_const` that assumes `MeasurableAdd` instead of
  `MeasurableSub`. This can be nice to avoid unnecessary type-class assumptions. -/]
/-
**measurable_div_const'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_div_const' {G : Type*} [DivInvMonoid G] [MeasurableSpace G] [Me
asurableMul G] (g : G) : Measurable fun h => h / g
参数：g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem measurable_div_const' {G : Type*} [DivInvMonoid G] [MeasurableSpace G] [MeasurableMul G]
    (g : G) : Measurable fun h => h / g := by simp_rw [div_eq_mul_inv, measurable_mul_const]

/-- This class assumes that the map `β × γ → β` given by `(x, y) ↦ x ^ y` is measurable. -/
/-
**MeasurablePow** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(β : Type u_2) → (γ : Type u_3) → [MeasurableSpace β] → [MeasurableSpace γ
] → [Pow β γ] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This class assumes that the map `β × γ → β` given by `(x, y) ↦ x ^ y` is measura
ble.
-/
class MeasurablePow (β γ : Type*) [MeasurableSpace β] [MeasurableSpace γ] [Pow β γ] : Prop where
  measurable_pow : Measurable fun p : β × γ => p.1 ^ p.2

export MeasurablePow (measurable_pow)

/-- `Monoid.Pow` is measurable. -/
/-
**Monoid.measurablePow** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Monoid.measurablePow (M : Type*) [Monoid M] [MeasurableSpace M] [Measurabl
eMul₂ M] : MeasurablePow M Nat
参数：M : Type*。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_from_prod_countable_left`：measurable_from_prod_countable_left
 [Countable β] [MeasurableSingletonClass β] {f : α × β -> γ} (hf : forall y, Mea
surable fun x => f (x, y)…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `Measurable.mul`：Measurable.mul [MeasurableMul₂ M] (hf : Measurable f) (h
g : Measurable g) : Measurable (f * g)
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)

--- 原说明 ---
`Monoid.Pow` is measurable.
-/
instance Monoid.measurablePow (M : Type*) [Monoid M] [MeasurableSpace M] [MeasurableMul₂ M] :
    MeasurablePow M ℕ :=
  ⟨measurable_from_prod_countable_left fun n => by
      induction n with
      | zero => simp only [pow_zero, ← Pi.one_def, measurable_one]
      | succ n ih =>
        simp only [pow_succ]
        exact ih.mul measurable_id⟩

section Pow

variable {β γ α : Type*} [MeasurableSpace β] [MeasurableSpace γ] [Pow β γ] [MeasurablePow β γ]
  {m : MeasurableSpace α} {μ : Measure α} {f : α → β} {g : α → γ}

@[fun_prop]
/-
**Measurable.pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.pow (hf : Measurable f) (hg : Measurable g) : Measurable fun x 
=> f x ^ g x
参数：hf : Measurable f；hg : Measurable g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `MeasurablePow.measurable_pow`：∀ {β : Type u_2} {γ : Type u_3} {inst : Me
asurableSpace β} {inst_1 : MeasurableSpace γ} {inst_2 : Pow β γ}   [self : Measu
rablePow β γ], Mea…
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
-/
theorem Measurable.pow (hf : Measurable f) (hg : Measurable g) : Measurable fun x => f x ^ g x :=
  measurable_pow.comp (hf.prodMk hg)

@[fun_prop]
/-
**AEMeasurable.pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AEMeasurable.pow (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) : AEMeasu
rable (fun x => f x ^ g x) μ
参数：hf : AEMeasurable f μ；hg : AEMeasurable g μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp_aemeasurable`：Measurable.comp_aemeasurable [MeasurableSp
ace δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) : A
EMeasurable (g ∘ f…
· 使用定理 `MeasurablePow.measurable_pow`：∀ {β : Type u_2} {γ : Type u_3} {inst : Me
asurableSpace β} {inst_1 : MeasurableSpace γ} {inst_2 : Pow β γ}   [self : Measu
rablePow β γ], Mea…
· 使用定理 `AEMeasurable.prodMk`：prodMk {f : α -> β} {g : α -> γ} (hf : AEMeasurable
 f μ) (hg : AEMeasurable g μ) : AEMeasurable (fun x => (f x, g x)) μ
-/
theorem AEMeasurable.pow (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    AEMeasurable (fun x => f x ^ g x) μ :=
  measurable_pow.comp_aemeasurable (hf.prodMk hg)

@[fun_prop]
/-
**Measurable.pow_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.pow_const (hf : Measurable f) (c : γ) : Measurable fun x => f x
 ^ c
参数：hf : Measurable f；c : γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.pow`：Measurable.pow (hf : Measurable f) (hg : Measurable g) :
 Measurable fun x => f x ^ g x
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
-/
theorem Measurable.pow_const (hf : Measurable f) (c : γ) : Measurable fun x => f x ^ c :=
  hf.pow measurable_const

@[fun_prop]
/-
**AEMeasurable.pow_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AEMeasurable.pow_const (hf : AEMeasurable f μ) (c : γ) : AEMeasurable (fun
 x => f x ^ c) μ
参数：hf : AEMeasurable f μ；c : γ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AEMeasurable.pow`：AEMeasurable.pow (hf : AEMeasurable f μ) (hg : AEMeasu
rable g μ) : AEMeasurable (fun x => f x ^ g x) μ
· 使用定理 `aemeasurable_const`：aemeasurable_const {b : β} : AEMeasurable (fun _a : 
α => b) μ
-/
theorem AEMeasurable.pow_const (hf : AEMeasurable f μ) (c : γ) :
    AEMeasurable (fun x => f x ^ c) μ :=
  hf.pow aemeasurable_const

@[fun_prop]
/-
**Measurable.const_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.const_pow (hg : Measurable g) (c : β) : Measurable fun x => c ^
 g x
参数：hg : Measurable g；c : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.pow`：Measurable.pow (hf : Measurable f) (hg : Measurable g) :
 Measurable fun x => f x ^ g x
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
-/
theorem Measurable.const_pow (hg : Measurable g) (c : β) : Measurable fun x => c ^ g x :=
  measurable_const.pow hg

@[fun_prop]
/-
**AEMeasurable.const_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AEMeasurable.const_pow (hg : AEMeasurable g μ) (c : β) : AEMeasurable (fun
 x => c ^ g x) μ
参数：hg : AEMeasurable g μ；c : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AEMeasurable.pow`：AEMeasurable.pow (hf : AEMeasurable f μ) (hg : AEMeasu
rable g μ) : AEMeasurable (fun x => f x ^ g x) μ
· 使用定理 `aemeasurable_const`：aemeasurable_const {b : β} : AEMeasurable (fun _a : 
α => b) μ
-/
theorem AEMeasurable.const_pow (hg : AEMeasurable g μ) (c : β) :
    AEMeasurable (fun x => c ^ g x) μ :=
  aemeasurable_const.pow hg

end Pow

/-- We say that a type has `MeasurableSub` if `(c - ·)` and `(· - c)` are measurable
functions. For a typeclass assuming measurability of `uncurry (-)` see `MeasurableSub₂`. -/
/-
**MeasurableSub** 是 Mathlib 中的一个类，位于命名空间 ``。
形式化陈述：MeasurableSub (G : Type*) [MeasurableSpace G] [Sub G] : Prop where measura
ble_const_sub : forall c : G, Measurable (c - ·)
参数：G : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that a type has `MeasurableSub` if `(c - ·)` and `(· - c)` are measurable
functions. For a typeclass assuming measurability of `uncurry (-)` see `Measurab
leSub₂`.
-/
class MeasurableSub (G : Type*) [MeasurableSpace G] [Sub G] : Prop where
  measurable_const_sub : ∀ c : G, Measurable (c - ·) := by intro; fun_prop
  measurable_sub_const : ∀ c : G, Measurable (· - c) := by intro; fun_prop

export MeasurableSub (measurable_const_sub measurable_sub_const)

/-- We say that a type has `MeasurableSub₂` if `uncurry (· - ·)` is a measurable function.
For a typeclass assuming measurability of `(c - ·)` and `(· - c)` see `MeasurableSub`. -/
/-
**MeasurableSub** 是 Mathlib 中的一个类，位于命名空间 ``。
形式化陈述：MeasurableSub (G : Type*) [MeasurableSpace G] [Sub G] : Prop where measura
ble_const_sub : forall c : G, Measurable (c - ·)
参数：G : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that a type has `MeasurableSub₂` if `uncurry (· - ·)` is a measurable fun
ction.
For a typeclass assuming measurability of `(c - ·)` and `(· - c)` see `Measurabl
eSub`.
-/
class MeasurableSub₂ (G : Type*) [MeasurableSpace G] [Sub G] : Prop where
  measurable_sub : Measurable fun p : G × G => p.1 - p.2

export MeasurableSub₂ (measurable_sub)

/-- We say that a type has `MeasurableDiv` if `(c / ·)` and `(· / c)` are measurable functions.
For a typeclass assuming measurability of `uncurry (· / ·)` see `MeasurableDiv₂`. -/
@[to_additive]
/-
**MeasurableDiv** 是 Mathlib 中的一个类，位于命名空间 ``。
形式化陈述：MeasurableDiv (G₀ : Type*) [MeasurableSpace G₀] [Div G₀] : Prop where meas
urable_const_div : forall c : G₀, Measurable (c / ·)
参数：G₀ : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that a type has `MeasurableDiv` if `(c / ·)` and `(· / c)` are measurable
 functions.
For a typeclass assuming measurability of `uncurry (· / ·)` see `MeasurableDiv₂`
.
-/
class MeasurableDiv (G₀ : Type*) [MeasurableSpace G₀] [Div G₀] : Prop where
  measurable_const_div : ∀ c : G₀, Measurable (c / ·) := by intro; fun_prop
  measurable_div_const : ∀ c : G₀, Measurable (· / c) := by intro; fun_prop

export MeasurableDiv (measurable_const_div measurable_div_const)

/-- We say that a type has `MeasurableDiv₂` if `uncurry (· / ·)` is a measurable function.
For a typeclass assuming measurability of `(c / ·)` and `(· / c)` see `MeasurableDiv`. -/
@[to_additive MeasurableSub₂]
/-
**MeasurableDiv** 是 Mathlib 中的一个类，位于命名空间 ``。
形式化陈述：MeasurableDiv (G₀ : Type*) [MeasurableSpace G₀] [Div G₀] : Prop where meas
urable_const_div : forall c : G₀, Measurable (c / ·)
参数：G₀ : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that a type has `MeasurableDiv₂` if `uncurry (· / ·)` is a measurable fun
ction.
For a typeclass assuming measurability of `(c / ·)` and `(· / c)` see `Measurabl
eDiv`.
-/
class MeasurableDiv₂ (G₀ : Type*) [MeasurableSpace G₀] [Div G₀] : Prop where
  measurable_div : Measurable fun p : G₀ × G₀ => p.1 / p.2

export MeasurableDiv₂ (measurable_div)

section Div

variable {G α β : Type*} [MeasurableSpace G] [Div G] {m : MeasurableSpace α}
  {mβ : MeasurableSpace β} {f g : α → G} {μ : Measure α}

@[to_additive (attr := fun_prop)]
/-
**Measurable.const_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.const_div [MeasurableDiv G] (hf : Measurable f) (c : G) : Measu
rable fun x => c / f x
参数：hf : Measurable f；c : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `MeasurableDiv.measurable_const_div`：∀ {G₀ : Type u_2} {inst : Measurable
Space G₀} {inst_1 : Div G₀} [self : MeasurableDiv G₀] (c : G₀),   Measurable fun
 x => c / x
-/
theorem Measurable.const_div [MeasurableDiv G] (hf : Measurable f) (c : G) :
    Measurable fun x => c / f x :=
  (MeasurableDiv.measurable_const_div c).comp hf

@[to_additive (attr := fun_prop)]
/-
**AEMeasurable.const_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AEMeasurable.const_div [MeasurableDiv G] (hf : AEMeasurable f μ) (c : G) :
 AEMeasurable (fun x => c / f x) μ
参数：hf : AEMeasurable f μ；c : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp_aemeasurable`：Measurable.comp_aemeasurable [MeasurableSp
ace δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) : A
EMeasurable (g ∘ f…
· 使用定理 `MeasurableDiv.measurable_const_div`：∀ {G₀ : Type u_2} {inst : Measurable
Space G₀} {inst_1 : Div G₀} [self : MeasurableDiv G₀] (c : G₀),   Measurable fun
 x => c / x
-/
theorem AEMeasurable.const_div [MeasurableDiv G] (hf : AEMeasurable f μ) (c : G) :
    AEMeasurable (fun x => c / f x) μ :=
  (MeasurableDiv.measurable_const_div c).comp_aemeasurable hf

@[to_additive (attr := fun_prop)]
/-
**Measurable.div_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.div_const [MeasurableDiv G] (hf : Measurable f) (c : G) : Measu
rable fun x => f x / c
参数：hf : Measurable f；c : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `MeasurableDiv.measurable_div_const`：∀ {G₀ : Type u_2} {inst : Measurable
Space G₀} {inst_1 : Div G₀} [self : MeasurableDiv G₀] (c : G₀),   Measurable fun
 x => x / c
-/
theorem Measurable.div_const [MeasurableDiv G] (hf : Measurable f) (c : G) :
    Measurable fun x => f x / c :=
  (MeasurableDiv.measurable_div_const c).comp hf

@[to_additive (attr := fun_prop)]
/-
**AEMeasurable.div_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AEMeasurable.div_const [MeasurableDiv G] (hf : AEMeasurable f μ) (c : G) :
 AEMeasurable (fun x => f x / c) μ
参数：hf : AEMeasurable f μ；c : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp_aemeasurable`：Measurable.comp_aemeasurable [MeasurableSp
ace δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) : A
EMeasurable (g ∘ f…
· 使用定理 `MeasurableDiv.measurable_div_const`：∀ {G₀ : Type u_2} {inst : Measurable
Space G₀} {inst_1 : Div G₀} [self : MeasurableDiv G₀] (c : G₀),   Measurable fun
 x => x / c
-/
theorem AEMeasurable.div_const [MeasurableDiv G] (hf : AEMeasurable f μ) (c : G) :
    AEMeasurable (fun x => f x / c) μ :=
  (MeasurableDiv.measurable_div_const c).comp_aemeasurable hf

@[to_fun (attr := to_additive (attr := fun_prop))]
/-
**Measurable.div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.div [MeasurableDiv₂ G] (hf : Measurable f) (hg : Measurable g) 
: Measurable (f / g)
参数：hf : Measurable f；hg : Measurable g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `MeasurableDiv₂.measurable_div`：∀ {G₀ : Type u_2} {inst : MeasurableSpace
 G₀} {inst_1 : Div G₀} [self : MeasurableDiv₂ G₀],   Measurable fun p => p.1 / p
.2
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
-/
theorem Measurable.div [MeasurableDiv₂ G] (hf : Measurable f) (hg : Measurable g) :
    Measurable (f / g) :=
  measurable_div.comp (hf.prodMk hg)

@[to_additive (attr := fun_prop)]
/-
**Measurable.div'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Measurable.div' [MeasurableDiv₂ G] {f g : α -> β -> G} {h : α -> β} (hf : 
Measurable ↿f) (hg : Measurable ↿g) (hh : Measurable h) : Measurable fun a => (f
 a / g a) (h a)
参数：hf : Measurable ↿f；hg : Measurable ↿g；hh : Measurable h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.fun_div`：∀ {G : Type u_2} {α : Type u_3} [inst : MeasurableSp
ace G] [inst_1 : Div G] {m : MeasurableSpace α} {f g : α → G}   [MeasurableDiv₂ 
G], Meas…
· 使用定理 `Measurable.fun_comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x :
 MeasurableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β
 → γ} {f …
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
-/
lemma Measurable.div' [MeasurableDiv₂ G] {f g : α → β → G} {h : α → β} (hf : Measurable ↿f)
    (hg : Measurable ↿g) (hh : Measurable h) : Measurable fun a ↦ (f a / g a) (h a) := by
  dsimp; fun_prop

@[to_fun (attr := to_additive (attr := fun_prop))]
/-
**AEMeasurable.div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AEMeasurable.div [MeasurableDiv₂ G] (hf : AEMeasurable f μ) (hg : AEMeasur
able g μ) : AEMeasurable (f / g) μ
参数：hf : AEMeasurable f μ；hg : AEMeasurable g μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp_aemeasurable`：Measurable.comp_aemeasurable [MeasurableSp
ace δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) : A
EMeasurable (g ∘ f…
· 使用定理 `MeasurableDiv₂.measurable_div`：∀ {G₀ : Type u_2} {inst : MeasurableSpace
 G₀} {inst_1 : Div G₀} [self : MeasurableDiv₂ G₀],   Measurable fun p => p.1 / p
.2
· 使用定理 `AEMeasurable.prodMk`：prodMk {f : α -> β} {g : α -> γ} (hf : AEMeasurable
 f μ) (hg : AEMeasurable g μ) : AEMeasurable (fun x => (f x, g x)) μ
-/
theorem AEMeasurable.div [MeasurableDiv₂ G] (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    AEMeasurable (f / g) μ :=
  measurable_div.comp_aemeasurable (hf.prodMk hg)

@[deprecated (since := "2026-06-26")] alias AEMeasurable.div' := AEMeasurable.div
@[deprecated (since := "2026-06-26")] alias AEMeasurable.sub' := AEMeasurable.sub

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) MeasurableDiv₂.toMeasurableDiv [MeasurableDiv₂ G] :
    MeasurableDiv G :=
  ⟨fun _ => measurable_const.div measurable_id, fun _ => measurable_id.div measurable_const⟩

@[to_additive]
/-
**Pi.measurableDiv** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.measurableDiv {ι : Type*} {α : ι -> Type*} [forall i, Div (α i)] [foral
l i, MeasurableSpace (α i)] [forall i, MeasurableDiv (α i)] : MeasurableDiv (for
all i, α i)
参数：α i；α i；α i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `measurable_pi_iff`：measurable_pi_iff {g : α -> forall a, X a} : Measurab
le g ↔ forall a, Measurable fun x => g x a
· 使用定理 `Measurable.const_div`：Measurable.const_div [MeasurableDiv G] (hf : Measu
rable f) (c : G) : Measurable fun x => c / f x
· 使用定理 `measurable_pi_apply`：measurable_pi_apply (a : δ) : Measurable fun f : fo
rall a, X a => f a
· 使用定理 `Measurable.div_const`：Measurable.div_const [MeasurableDiv G] (hf : Measu
rable f) (c : G) : Measurable fun x => f x / c
-/
instance Pi.measurableDiv {ι : Type*} {α : ι → Type*} [∀ i, Div (α i)]
    [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableDiv (α i)] : MeasurableDiv (∀ i, α i) :=
  ⟨fun _ => measurable_pi_iff.mpr fun i => (measurable_pi_apply i).const_div _, fun _ =>
    measurable_pi_iff.mpr fun i => (measurable_pi_apply i).div_const _⟩

@[to_additive Pi.measurableSub₂]
/-
**Pi.measurableDiv** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.measurableDiv {ι : Type*} {α : ι -> Type*} [forall i, Div (α i)] [foral
l i, MeasurableSpace (α i)] [forall i, MeasurableDiv (α i)] : MeasurableDiv (for
all i, α i)
参数：α i；α i；α i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `measurable_pi_iff`：measurable_pi_iff {g : α -> forall a, X a} : Measurab
le g ↔ forall a, Measurable fun x => g x a
· 使用定理 `Measurable.const_div`：Measurable.const_div [MeasurableDiv G] (hf : Measu
rable f) (c : G) : Measurable fun x => c / f x
· 使用定理 `measurable_pi_apply`：measurable_pi_apply (a : δ) : Measurable fun f : fo
rall a, X a => f a
· 使用定理 `Measurable.div_const`：Measurable.div_const [MeasurableDiv G] (hf : Measu
rable f) (c : G) : Measurable fun x => f x / c
-/
instance Pi.measurableDiv₂ {ι : Type*} {α : ι → Type*} [∀ i, Div (α i)]
    [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableDiv₂ (α i)] : MeasurableDiv₂ (∀ i, α i) :=
  ⟨measurable_pi_iff.mpr fun _ => measurable_fst.eval.div measurable_snd.eval⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {E} [MeasurableSpace E] [AddGroup E] [MeasurableSingletonClass E] [MeasurableSub₂ E] :
    MeasurableEq E := by
  constructor
  simp_rw +singlePass [Set.diagonal, ← sub_eq_zero]
  measurability
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {β : Type*} [AddCommMonoid β] [PartialOrder β]
    [CanonicallyOrderedAdd β] [Sub β] [OrderedSub β]
    {_ : MeasurableSpace β} [MeasurableSub₂ β] [MeasurableSingletonClass β] :
    MeasurableEq β := by
  constructor
  simp_rw [Set.diagonal, le_antisymm_iff, ← tsub_eq_zero_iff_le]
  measurability

end Div

/-- We say that a type has `MeasurableNeg` if `x ↦ -x` is a measurable function. -/
/-
**MeasurableNeg** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(G : Type u_2) → [Neg G] → [MeasurableSpace G] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that a type has `MeasurableNeg` if `x ↦ -x` is a measurable function.
-/
class MeasurableNeg (G : Type*) [Neg G] [MeasurableSpace G] : Prop where
  measurable_neg : Measurable (Neg.neg : G → G)

/-- We say that a type has `MeasurableInv` if `x ↦ x⁻¹` is a measurable function. -/
@[to_additive]
/-
**MeasurableInv** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(G : Type u_2) → [Inv G] → [MeasurableSpace G] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that a type has `MeasurableInv` if `x ↦ x⁻¹` is a measurable function.
-/
class MeasurableInv (G : Type*) [Inv G] [MeasurableSpace G] : Prop where
  measurable_inv : Measurable (Inv.inv : G → G)

export MeasurableInv (measurable_inv)

export MeasurableNeg (measurable_neg)

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) measurableDiv_of_mul_inv (G : Type*) [MeasurableSpace G]
    [DivInvMonoid G] [MeasurableMul G] [MeasurableInv G] : MeasurableDiv G where
  measurable_const_div c := by
    convert! measurable_inv.const_mul c using 1
    ext1
    apply div_eq_mul_inv
  measurable_div_const c := by
    convert! measurable_id.mul_const c⁻¹ using 1
    ext1
    apply div_eq_mul_inv

section Inv

variable {G α : Type*} [Inv G] [MeasurableSpace G] [MeasurableInv G] {m : MeasurableSpace α}
  {f : α → G} {μ : Measure α}

@[to_fun (attr := to_additive (attr := fun_prop))]
/-
**Measurable.inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.inv (hf : Measurable f) : Measurable f⁻¹
参数：hf : Measurable f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `MeasurableInv.measurable_inv`：∀ {G : Type u_2} {inst : Inv G} {inst_1 : 
MeasurableSpace G} [self : MeasurableInv G], Measurable Inv.inv
-/
theorem Measurable.inv (hf : Measurable f) : Measurable f⁻¹ :=
  measurable_inv.comp hf

@[to_fun (attr := to_additive (attr := fun_prop))]
/-
**AEMeasurable.inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AEMeasurable.inv (hf : AEMeasurable f μ) : AEMeasurable f⁻¹ μ
参数：hf : AEMeasurable f μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp_aemeasurable`：Measurable.comp_aemeasurable [MeasurableSp
ace δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) : A
EMeasurable (g ∘ f…
· 使用定理 `MeasurableInv.measurable_inv`：∀ {G : Type u_2} {inst : Inv G} {inst_1 : 
MeasurableSpace G} [self : MeasurableInv G], Measurable Inv.inv
-/
theorem AEMeasurable.inv (hf : AEMeasurable f μ) : AEMeasurable f⁻¹ μ :=
  measurable_inv.comp_aemeasurable hf

@[to_additive (attr := simp)]
/-
**measurable_inv_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_inv_iff {G : Type*} [InvolutiveInv G] [MeasurableSpace G] [Meas
urableInv G] {f : α -> G} : (Measurable fun x => (f x)⁻¹) ↔ Measurable f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Measurable.fun_inv`：∀ {G : Type u_2} {α : Type u_3} [inst : Inv G] [inst
_1 : MeasurableSpace G] [MeasurableInv G] {m : MeasurableSpace α}   {f : α → G},
 Measura…
· 使用定理 `Measurable.inv`：Measurable.inv (hf : Measurable f) : Measurable f⁻¹
-/
theorem measurable_inv_iff {G : Type*} [InvolutiveInv G] [MeasurableSpace G] [MeasurableInv G]
    {f : α → G} : (Measurable fun x => (f x)⁻¹) ↔ Measurable f :=
  ⟨fun h => by simpa only [inv_inv] using h.fun_inv, fun h => h.inv⟩

@[to_additive (attr := simp)]
/-
**aemeasurable_inv_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：aemeasurable_inv_iff {G : Type*} [InvolutiveInv G] [MeasurableSpace G] [Me
asurableInv G] {f : α -> G} : AEMeasurable (fun x => (f x)⁻¹) μ ↔ AEMeasurable f
 μ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `AEMeasurable.fun_inv`：∀ {G : Type u_2} {α : Type u_3} [inst : Inv G] [in
st_1 : MeasurableSpace G] [MeasurableInv G] {m : MeasurableSpace α}   {f : α → G
} {μ : Mea…
· 使用定理 `AEMeasurable.inv`：AEMeasurable.inv (hf : AEMeasurable f μ) : AEMeasurabl
e f⁻¹ μ
-/
theorem aemeasurable_inv_iff {G : Type*} [InvolutiveInv G] [MeasurableSpace G] [MeasurableInv G]
    {f : α → G} : AEMeasurable (fun x => (f x)⁻¹) μ ↔ AEMeasurable f μ :=
  ⟨fun h => by simpa only [inv_inv] using h.fun_inv, fun h => h.inv⟩

@[to_additive]
/-
**Pi.measurableInv** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.measurableInv {ι : Type*} {α : ι -> Type*} [forall i, Inv (α i)] [foral
l i, MeasurableSpace (α i)] [forall i, MeasurableInv (α i)] : MeasurableInv (for
all i, α i)
参数：α i；α i；α i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `measurable_pi_iff`：measurable_pi_iff {g : α -> forall a, X a} : Measurab
le g ↔ forall a, Measurable fun x => g x a
· 使用定理 `Measurable.inv`：Measurable.inv (hf : Measurable f) : Measurable f⁻¹
· 使用定理 `measurable_pi_apply`：measurable_pi_apply (a : δ) : Measurable fun f : fo
rall a, X a => f a
-/
instance Pi.measurableInv {ι : Type*} {α : ι → Type*} [∀ i, Inv (α i)]
    [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableInv (α i)] : MeasurableInv (∀ i, α i) :=
  ⟨measurable_pi_iff.mpr fun i => (measurable_pi_apply i).inv⟩

@[to_additive]
/-
**MeasurableSet.inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeasurableSet.inv {s : Set G} (hs : MeasurableSet s) : MeasurableSet s⁻¹
参数：hs : MeasurableSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableInv.measurable_inv`：∀ {G : Type u_2} {inst : Inv G} {inst_1 : 
MeasurableSpace G} [self : MeasurableInv G], Measurable Inv.inv
-/
theorem MeasurableSet.inv {s : Set G} (hs : MeasurableSet s) : MeasurableSet s⁻¹ :=
  measurable_inv hs

@[to_additive]
/-
**measurableEmbedding_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurableEmbedding_inv [InvolutiveInv α] [MeasurableInv α] : MeasurableEm
bedding (Inv.inv (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inv_injective`：inv_injective : Function.Injective (Inv.inv : G -> G)
· 使用定理 `MeasurableInv.measurable_inv`：∀ {G : Type u_2} {inst : Inv G} {inst_1 : 
MeasurableSpace G} [self : MeasurableInv G], Measurable Inv.inv
· 使用定理 `MeasurableSet.inv`：MeasurableSet.inv {s : Set G} (hs : MeasurableSet s) 
: MeasurableSet s⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_inv_eq_inv`：image_inv_eq_inv : (·⁻¹) '' s = s⁻¹
-/
theorem measurableEmbedding_inv [InvolutiveInv α] [MeasurableInv α] :
    MeasurableEmbedding (Inv.inv (α := α)) :=
  ⟨inv_injective, measurable_inv, fun s hs ↦ s.image_inv_eq_inv ▸ hs.inv⟩

end Inv

@[to_additive]
/-
**Measurable.mul_iff_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.mul_iff_right {G : Type*} [MeasurableSpace G] [MeasurableSpace 
α] [CommGroup G] [MeasurableMul₂ G] [MeasurableInv G] {f g : α -> G} (hf : Measu
rable f) : Measurable (f * g) ↔ Measurable g
参数：hf : Measurable f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.mul`：Measurable.mul [MeasurableMul₂ M] (hf : Measurable f) (h
g : Measurable g) : Measurable (f * g)
· 使用定理 `Measurable.inv`：Measurable.inv (hf : Measurable f) : Measurable f⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `mul_inv_cancel_comm`：mul_inv_cancel_comm (a b : G) : a * b * a⁻¹ = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Measurable.mul_iff_right {G : Type*} [MeasurableSpace G] [MeasurableSpace α] [CommGroup G]
    [MeasurableMul₂ G] [MeasurableInv G] {f g : α → G} (hf : Measurable f) :
    Measurable (f * g) ↔ Measurable g :=
  ⟨fun h ↦ show g = f * g * f⁻¹ by simp only [mul_inv_cancel_comm] ▸ h.mul hf.inv,
    fun h ↦ hf.mul h⟩

@[to_additive]
/-
**AEMeasurable.mul_iff_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AEMeasurable.mul_iff_right {G : Type*} [MeasurableSpace G] [MeasurableSpac
e α] [CommGroup G] [MeasurableMul₂ G] [MeasurableInv G] {μ : Measure α} {f g : α
 -> G} (hf : AEMeasurable f μ) : AEMeasurable (f * g) μ ↔ AEMeasurable g μ
参数：hf : AEMeasurable f μ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AEMeasurable.mul`：AEMeasurable.mul [MeasurableMul₂ M] (hf : AEMeasurable
 f μ) (hg : AEMeasurable g μ) : AEMeasurable (f * g) μ
· 使用定理 `AEMeasurable.inv`：AEMeasurable.inv (hf : AEMeasurable f μ) : AEMeasurabl
e f⁻¹ μ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `mul_inv_cancel_comm`：mul_inv_cancel_comm (a b : G) : a * b * a⁻¹ = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem AEMeasurable.mul_iff_right {G : Type*} [MeasurableSpace G] [MeasurableSpace α] [CommGroup G]
    [MeasurableMul₂ G] [MeasurableInv G] {μ : Measure α} {f g : α → G} (hf : AEMeasurable f μ) :
    AEMeasurable (f * g) μ ↔ AEMeasurable g μ :=
  ⟨fun h ↦ show g = f * g * f⁻¹ by simp only [mul_inv_cancel_comm] ▸ h.mul hf.inv,
    fun h ↦ hf.mul h⟩

@[to_additive]
/-
**Measurable.mul_iff_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.mul_iff_left {G : Type*} [MeasurableSpace G] [MeasurableSpace α
] [CommGroup G] [MeasurableMul₂ G] [MeasurableInv G] {f g : α -> G} (hf : Measur
able f) : Measurable (g * f) ↔ Measurable g
参数：hf : Measurable f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.mul_iff_right`：Measurable.mul_iff_right {G : Type*} [Measurab
leSpace G] [MeasurableSpace α] [CommGroup G] [MeasurableMul₂ G] [MeasurableInv G
] {f g : α -> …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem Measurable.mul_iff_left {G : Type*} [MeasurableSpace G] [MeasurableSpace α] [CommGroup G]
    [MeasurableMul₂ G] [MeasurableInv G] {f g : α → G} (hf : Measurable f) :
    Measurable (g * f) ↔ Measurable g :=
  mul_comm g f ▸ Measurable.mul_iff_right hf

@[to_additive]
/-
**AEMeasurable.mul_iff_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AEMeasurable.mul_iff_left {G : Type*} [MeasurableSpace G] [MeasurableSpace
 α] [CommGroup G] [MeasurableMul₂ G] [MeasurableInv G] {μ : Measure α} {f g : α 
-> G} (hf : AEMeasurable f μ) : AEMeasurable (g * f) μ ↔ AEMeasurable g μ
参数：hf : AEMeasurable f μ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AEMeasurable.mul_iff_right`：AEMeasurable.mul_iff_right {G : Type*} [Meas
urableSpace G] [MeasurableSpace α] [CommGroup G] [MeasurableMul₂ G] [MeasurableI
nv G] {μ : Measu…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem AEMeasurable.mul_iff_left {G : Type*} [MeasurableSpace G] [MeasurableSpace α] [CommGroup G]
    [MeasurableMul₂ G] [MeasurableInv G] {μ : Measure α} {f g : α → G} (hf : AEMeasurable f μ) :
    AEMeasurable (g * f) μ ↔ AEMeasurable g μ :=
  mul_comm g f ▸ AEMeasurable.mul_iff_right hf

/-- `DivInvMonoid.Pow` is measurable. -/
/-
**DivInvMonoid.measurableZPow** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：DivInvMonoid.measurableZPow (G : Type u) [DivInvMonoid G] [MeasurableSpace
 G] [MeasurableMul₂ G] [MeasurableInv G] : MeasurablePow G Int
参数：G : Type u。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_from_prod_countable_left`：measurable_from_prod_countable_left
 [Countable β] [MeasurableSingletonClass β] {f : α × β -> γ} (hf : forall y, Mea
surable fun x => f (x, y)…
· 使用定理 `instCountableInt`：Countable ℤ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `Measurable.pow_const`：Measurable.pow_const (hf : Measurable f) (c : γ) :
 Measurable fun x => f x ^ c
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
· 使用定理 `Measurable.inv`：Measurable.inv (hf : Measurable f) : Measurable f⁻¹

--- 原说明 ---
`DivInvMonoid.Pow` is measurable.
-/
instance DivInvMonoid.measurableZPow (G : Type u) [DivInvMonoid G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G] : MeasurablePow G ℤ :=
  ⟨measurable_from_prod_countable_left fun n => by
      rcases n with n | n
      · simp_rw [Int.ofNat_eq_natCast, zpow_natCast]
        exact measurable_id.pow_const _
      · simp_rw [zpow_negSucc]
        exact (measurable_id.pow_const (n + 1)).inv⟩

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) measurableDiv₂_of_mul_inv (G : Type*) [MeasurableSpace G]
    [DivInvMonoid G] [MeasurableMul₂ G] [MeasurableInv G] : MeasurableDiv₂ G :=
  ⟨by
    simp only [div_eq_mul_inv]
    exact measurable_fst.mul measurable_snd.inv⟩

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) MeasurableDiv.toMeasurableInv [MeasurableSpace α] [Group α]
    [MeasurableDiv α] : MeasurableInv α where
  measurable_inv := by simpa using measurable_const_div (1 : α)

/-- We say that the action of `M` on `α` has `MeasurableConstVAdd` if for each `c` the map
`x ↦ c +ᵥ x` is a measurable function. -/
/-
**MeasurableConstVAdd** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(M : Type u_2) → (α : Type u_3) → [VAdd M α] → [MeasurableSpace α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that the action of `M` on `α` has `MeasurableConstVAdd` if for each `c` t
he map
`x ↦ c +ᵥ x` is a measurable function.
-/
class MeasurableConstVAdd (M α : Type*) [VAdd M α] [MeasurableSpace α] : Prop where
  measurable_const_vadd : ∀ c : M, Measurable (c +ᵥ · : α → α)

/-- We say that the action of `M` on `α` has `MeasurableConstSMul` if for each `c` the map
`x ↦ c • x` is a measurable function. -/
@[to_additive]
/-
**MeasurableConstSMul** 是 Mathlib 中的一个类，位于命名空间 ``。
形式化陈述：MeasurableConstSMul (M α : Type*) [SMul M α] [MeasurableSpace α] : Prop wh
ere measurable_const_smul : forall c : M, Measurable (c • · : α -> α)
参数：M α : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that the action of `M` on `α` has `MeasurableConstSMul` if for each `c` t
he map
`x ↦ c • x` is a measurable function.
-/
class MeasurableConstSMul (M α : Type*) [SMul M α] [MeasurableSpace α] : Prop where
  measurable_const_smul : ∀ c : M, Measurable (c • · : α → α) := by measurability

/-- We say that the action of `M` on `α` has `MeasurableVAdd` if for each `c` the map `x ↦ c +ᵥ x`
is a measurable function and for each `x` the map `c ↦ c +ᵥ x` is a measurable function. -/
/-
**MeasurableVAdd** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(M : Type u_2) → (α : Type u_3) → [VAdd M α] → [MeasurableSpace M] → [Meas
urableSpace α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that the action of `M` on `α` has `MeasurableVAdd` if for each `c` the ma
p `x ↦ c +ᵥ x`
is a measurable function and for each `x` the map `c ↦ c +ᵥ x` is a measurable f
unction.
-/
class MeasurableVAdd (M α : Type*) [VAdd M α] [MeasurableSpace M] [MeasurableSpace α]
    extends MeasurableConstVAdd M α where
  measurable_vadd_const : ∀ x : α, Measurable (· +ᵥ x : M → α)

/-- We say that the action of `M` on `α` has `MeasurableSMul` if for each `c` the map `x ↦ c • x`
is a measurable function and for each `x` the map `c ↦ c • x` is a measurable function. -/
@[to_additive]
/-
**MeasurableSMul** 是 Mathlib 中的一个类，位于命名空间 ``。
形式化陈述：MeasurableSMul (M α : Type*) [SMul M α] [MeasurableSpace M] [MeasurableSpa
ce α] extends MeasurableConstSMul M α where measurable_smul_const : forall x : α
, Measurable (· • x : M -> α)
参数：M α : Type*。
继承自：MeasurableConstSMul M α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that the action of `M` on `α` has `MeasurableSMul` if for each `c` the ma
p `x ↦ c • x`
is a measurable function and for each `x` the map `c ↦ c • x` is a measurable fu
nction.
-/
class MeasurableSMul (M α : Type*) [SMul M α] [MeasurableSpace M] [MeasurableSpace α]
    extends MeasurableConstSMul M α where
  measurable_smul_const : ∀ x : α, Measurable (· • x : M → α) := by measurability

/-- We say that the action of `M` on `α` has `MeasurableVAdd₂` if the map
`(c, x) ↦ c +ᵥ x` is a measurable function. -/
/-
**MeasurableVAdd** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(M : Type u_2) → (α : Type u_3) → [VAdd M α] → [MeasurableSpace M] → [Meas
urableSpace α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that the action of `M` on `α` has `MeasurableVAdd₂` if the map
`(c, x) ↦ c +ᵥ x` is a measurable function.
-/
class MeasurableVAdd₂ (M α : Type*) [VAdd M α] [MeasurableSpace M] [MeasurableSpace α] :
    Prop where
  measurable_vadd : Measurable (Function.uncurry (· +ᵥ ·) : M × α → α)

/-- We say that the action of `M` on `α` has `MeasurableSMul₂` if the map
`(c, x) ↦ c • x` is a measurable function. -/
@[to_additive MeasurableVAdd₂]
/-
**MeasurableSMul** 是 Mathlib 中的一个类，位于命名空间 ``。
形式化陈述：MeasurableSMul (M α : Type*) [SMul M α] [MeasurableSpace M] [MeasurableSpa
ce α] extends MeasurableConstSMul M α where measurable_smul_const : forall x : α
, Measurable (· • x : M -> α)
参数：M α : Type*。
继承自：MeasurableConstSMul M α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that the action of `M` on `α` has `MeasurableSMul₂` if the map
`(c, x) ↦ c • x` is a measurable function.
-/
class MeasurableSMul₂ (M α : Type*) [SMul M α] [MeasurableSpace M] [MeasurableSpace α] :
    Prop where
  measurable_smul : Measurable (Function.uncurry (· • ·) : M × α → α)

export MeasurableConstVAdd (measurable_const_vadd)
export MeasurableConstSMul (measurable_const_smul)
export MeasurableVAdd (measurable_vadd_const)
export MeasurableSMul (measurable_smul_const)
export MeasurableSMul₂ (measurable_smul)
export MeasurableVAdd₂ (measurable_vadd)

@[to_additive]
/-
**measurableSMul_of_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ (M : Type u_2) [inst : Mul M] [inst_1 : MeasurableSpace M] [MeasurableMu
l M], MeasurableSMul M M
参数：M : Type u_2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.const_mul`：Measurable.const_mul [MeasurableMul M] (hf : Measu
rable f) (c : M) : Measurable fun x => c * f x
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
· 使用定理 `Measurable.mul_const`：Measurable.mul_const [MeasurableMul M] (hf : Measu
rable f) (c : M) : Measurable fun x => f x * c
-/
instance measurableSMul_of_mul (M : Type*) [Mul M] [MeasurableSpace M] [MeasurableMul M] :
    MeasurableSMul M M where

@[to_additive]
/-
**measurableSMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance measurableSMul₂_of_mul (M : Type*) [Mul M] [MeasurableSpace M] [MeasurableMul₂ M] :
    MeasurableSMul₂ M M :=
  ⟨measurable_mul⟩

@[to_additive]
/-
**Submonoid.instMeasurableConstSMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Submonoid.instMeasurableConstSMul {M α} [MeasurableSpace α] [Monoid M] [Mu
lAction M α] [MeasurableConstSMul M α] (s : Submonoid M) : MeasurableConstSMul s
 α where measurable_const_smul c
参数：s : Submonoid M。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableConstSMul.measurable_const_smul`：∀ {M : Type u_2} {α : Type u_
3} {inst : SMul M α} {inst_1 : MeasurableSpace α} [self : MeasurableConstSMul M 
α] (c : M),   Measurable fun x …
-/
instance Submonoid.instMeasurableConstSMul {M α} [MeasurableSpace α] [Monoid M] [MulAction M α]
    [MeasurableConstSMul M α] (s : Submonoid M) : MeasurableConstSMul s α where
  measurable_const_smul c := by simpa only using! measurable_const_smul (c : M)

@[to_additive]
/-
**Submonoid.instMeasurableSMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Submonoid.instMeasurableSMul {M α} [MeasurableSpace M] [MeasurableSpace α]
 [Monoid M] [MulAction M α] [MeasurableSMul M α] (s : Submonoid M) : MeasurableS
Mul s α where measurable_smul_const x
参数：s : Submonoid M。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSMul.toMeasurableConstSMul`：∀ {M : Type u_2} {α : Type u_3} {i
nst : SMul M α} {inst_1 : MeasurableSpace M} {inst_2 : MeasurableSpace α}   [sel
f : MeasurableSMul M α], M…
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `MeasurableSMul.measurable_smul_const`：∀ {M : Type u_2} {α : Type u_3} {i
nst : SMul M α} {inst_1 : MeasurableSpace M} {inst_2 : MeasurableSpace α}   [sel
f : MeasurableSMul M α] (x…
· 使用定理 `measurable_subtype_coe`：measurable_subtype_coe {p : α -> Prop} : Measura
ble ((↑) : Subtype p -> α)
-/
instance Submonoid.instMeasurableSMul {M α} [MeasurableSpace M] [MeasurableSpace α] [Monoid M]
    [MulAction M α] [MeasurableSMul M α] (s : Submonoid M) : MeasurableSMul s α where
  measurable_smul_const x := (measurable_smul_const (M := M) x).comp measurable_subtype_coe

@[to_additive]
/-
**Subgroup.instMeasurableConstSMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Subgroup.instMeasurableConstSMul {G α} [MeasurableSpace α] [Group G] [MulA
ction G α] [MeasurableConstSMul G α] (s : Subgroup G) : MeasurableConstSMul s α
参数：s : Subgroup G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Subgroup.instMeasurableConstSMul {G α} [MeasurableSpace α] [Group G] [MulAction G α]
    [MeasurableConstSMul G α] (s : Subgroup G) : MeasurableConstSMul s α :=
  s.toSubmonoid.instMeasurableConstSMul

@[to_additive]
/-
**Subgroup.instMeasurableSMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Subgroup.instMeasurableSMul {G α} [MeasurableSpace G] [MeasurableSpace α] 
[Group G] [MulAction G α] [MeasurableSMul G α] (s : Subgroup G) : MeasurableSMul
 s α
参数：s : Subgroup G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Subgroup.instMeasurableSMul {G α} [MeasurableSpace G] [MeasurableSpace α] [Group G]
    [MulAction G α] [MeasurableSMul G α] (s : Subgroup G) : MeasurableSMul s α :=
  s.toSubmonoid.instMeasurableSMul

section SMul
variable {M X α β : Type*} [MeasurableSpace X] [SMul M X]
  {m : MeasurableSpace α} {mβ : MeasurableSpace β} {μ : Measure α} {f : α → M} {g : α → X}

section MeasurableConstSMul
variable [MeasurableConstSMul M X]

@[to_additive (attr := to_fun (attr := fun_prop))]
/-
**Measurable.const_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Measurable.const_smul (hg : Measurable g) (c : M) : Measurable (c • g)
参数：hg : Measurable g；c : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `MeasurableConstSMul.measurable_const_smul`：∀ {M : Type u_2} {α : Type u_
3} {inst : SMul M α} {inst_1 : MeasurableSpace α} [self : MeasurableConstSMul M 
α] (c : M),   Measurable fun x …
-/
lemma Measurable.const_smul (hg : Measurable g) (c : M) : Measurable (c • g) :=
  (measurable_const_smul c).comp hg

@[to_additive (attr := to_fun (attr := fun_prop))]
/-
**AEMeasurable.const_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AEMeasurable.const_smul (hg : AEMeasurable g μ) (c : M) : AEMeasurable (c 
• g) μ
参数：hg : AEMeasurable g μ；c : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp_aemeasurable`：Measurable.comp_aemeasurable [MeasurableSp
ace δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) : A
EMeasurable (g ∘ f…
· 使用定理 `MeasurableConstSMul.measurable_const_smul`：∀ {M : Type u_2} {α : Type u_
3} {inst : SMul M α} {inst_1 : MeasurableSpace α} [self : MeasurableConstSMul M 
α] (c : M),   Measurable fun x …
-/
lemma AEMeasurable.const_smul (hg : AEMeasurable g μ) (c : M) : AEMeasurable (c • g) μ :=
  (measurable_const_smul c).comp_aemeasurable hg

@[to_additive]
/-
**Pi.instMeasurableConstSMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.instMeasurableConstSMul {ι : Type*} {α : ι -> Type*} [forall i, SMul M 
(α i)] [forall i, MeasurableSpace (α i)] [forall i, MeasurableConstSMul M (α i)]
 : MeasurableConstSMul M (forall i, α i) where measurable_const_smul _
参数：α i；α i；α i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `measurable_pi_iff`：measurable_pi_iff {g : α -> forall a, X a} : Measurab
le g ↔ forall a, Measurable fun x => g x a
· 使用引理 `Measurable.const_smul`：Measurable.const_smul (hg : Measurable g) (c : M)
 : Measurable (c • g)
· 使用定理 `measurable_pi_apply`：measurable_pi_apply (a : δ) : Measurable fun f : fo
rall a, X a => f a
-/
instance Pi.instMeasurableConstSMul {ι : Type*} {α : ι → Type*} [∀ i, SMul M (α i)]
    [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableConstSMul M (α i)] :
    MeasurableConstSMul M (∀ i, α i) where
  measurable_const_smul _ := measurable_pi_iff.2 fun i ↦ (measurable_pi_apply i).const_smul _

/-- If a scalar is central, then its right action is measurable when its left action is. -/
@[to_additive /-- If a vector is central, then its right action is measurable when its left
action is. -/]
nonrec instance MulOpposite.instMeasurableConstSMul [SMul M α] [SMul Mᵐᵒᵖ α] [IsCentralScalar M α]
    [MeasurableConstSMul M α] : MeasurableConstSMul Mᵐᵒᵖ α where
  measurable_const_smul := by simpa using measurable_const_smul

end MeasurableConstSMul

variable [MeasurableSpace M]

@[to_fun (attr := to_additive (attr := fun_prop))]
/-
**Measurable.smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.smul [MeasurableSMul₂ M X] (hf : Measurable f) (hg : Measurable
 g) : Measurable (f • g)
参数：hf : Measurable f；hg : Measurable g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `MeasurableSMul₂.measurable_smul`：∀ {M : Type u_2} {α : Type u_3} {inst :
 SMul M α} {inst_1 : MeasurableSpace M} {inst_2 : MeasurableSpace α}   [self : M
easurableSMul₂ M α], …
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
-/
theorem Measurable.smul [MeasurableSMul₂ M X] (hf : Measurable f) (hg : Measurable g) :
    Measurable (f • g) :=
  measurable_smul.comp (hf.prodMk hg)

/-- Compositional version of `Measurable.smul` for use by `fun_prop`. -/
@[to_additive (attr := fun_prop)
/-- Compositional version of `Measurable.vadd` for use by `fun_prop`. -/]
/-
**Measurable.smul'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Measurable.smul' [MeasurableSMul₂ M X] {f : α -> β -> M} {g : α -> β -> X}
 {h : α -> β} (hf : Measurable ↿f) (hg : Measurable ↿g) (hh : Measurable h) : Me
asurable fun a => (f a • g a) (h a)
参数：hf : Measurable ↿f；hg : Measurable ↿g；hh : Measurable h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.fun_smul`：∀ {M : Type u_2} {X : Type u_3} {α : Type u_4} [ins
t : MeasurableSpace X] [inst_1 : SMul M X] {m : MeasurableSpace α}   {f : α → M}
 {g : α →…
· 使用定理 `Measurable.fun_comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x :
 MeasurableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β
 → γ} {f …
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
-/
lemma Measurable.smul' [MeasurableSMul₂ M X] {f : α → β → M} {g : α → β → X} {h : α → β}
    (hf : Measurable ↿f) (hg : Measurable ↿g) (hh : Measurable h) :
    Measurable fun a ↦ (f a • g a) (h a) := by dsimp; fun_prop

@[to_fun (attr := to_additive (attr := fun_prop))]
/-
**AEMeasurable.smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AEMeasurable.smul [MeasurableSMul₂ M X] {μ : Measure α} (hf : AEMeasurable
 f μ) (hg : AEMeasurable g μ) : AEMeasurable (f • g) μ
参数：hf : AEMeasurable f μ；hg : AEMeasurable g μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp_aemeasurable`：Measurable.comp_aemeasurable [MeasurableSp
ace δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) : A
EMeasurable (g ∘ f…
· 使用定理 `MeasurableSMul₂.measurable_smul`：∀ {M : Type u_2} {α : Type u_3} {inst :
 SMul M α} {inst_1 : MeasurableSpace M} {inst_2 : MeasurableSpace α}   [self : M
easurableSMul₂ M α], …
· 使用定理 `AEMeasurable.prodMk`：prodMk {f : α -> β} {g : α -> γ} (hf : AEMeasurable
 f μ) (hg : AEMeasurable g μ) : AEMeasurable (fun x => (f x, g x)) μ
-/
theorem AEMeasurable.smul [MeasurableSMul₂ M X] {μ : Measure α} (hf : AEMeasurable f μ)
    (hg : AEMeasurable g μ) : AEMeasurable (f • g) μ :=
  MeasurableSMul₂.measurable_smul.comp_aemeasurable (hf.prodMk hg)

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) MeasurableSMul₂.toMeasurableSMul [MeasurableSMul₂ M X] :
    MeasurableSMul M X where

variable [MeasurableSMul M X]

@[to_additive (attr := fun_prop)]
/-
**Measurable.smul_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.smul_const (hf : Measurable f) (y : X) : Measurable fun x => f 
x • y
参数：hf : Measurable f；y : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `MeasurableSMul.measurable_smul_const`：∀ {M : Type u_2} {α : Type u_3} {i
nst : SMul M α} {inst_1 : MeasurableSpace M} {inst_2 : MeasurableSpace α}   [sel
f : MeasurableSMul M α] (x…
-/
theorem Measurable.smul_const (hf : Measurable f) (y : X) : Measurable fun x => f x • y :=
  (MeasurableSMul.measurable_smul_const y).comp hf

@[to_additive (attr := fun_prop)]
/-
**AEMeasurable.smul_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AEMeasurable.smul_const (hf : AEMeasurable f μ) (y : X) : AEMeasurable (fu
n x => f x • y) μ
参数：hf : AEMeasurable f μ；y : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp_aemeasurable'`：Measurable.comp_aemeasurable' [Measurable
Space δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) :
 AEMeasurable (fun …
· 使用定理 `Measurable.smul_const`：Measurable.smul_const (hf : Measurable f) (y : X)
 : Measurable fun x => f x • y
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
-/
theorem AEMeasurable.smul_const (hf : AEMeasurable f μ) (y : X) :
    AEMeasurable (fun x => f x • y) μ := by fun_prop

@[to_additive]
/-
**Pi.measurableSMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.measurableSMul {ι : Type*} {α : ι -> Type*} [forall i, SMul M (α i)] [f
orall i, MeasurableSpace (α i)] [forall i, MeasurableSMul M (α i)] : MeasurableS
Mul M (forall i, α i) where measurable_smul_const _
参数：α i；α i；α i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSMul.toMeasurableConstSMul`：∀ {M : Type u_2} {α : Type u_3} {i
nst : SMul M α} {inst_1 : MeasurableSpace M} {inst_2 : MeasurableSpace α}   [sel
f : MeasurableSMul M α], M…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `measurable_pi_iff`：measurable_pi_iff {g : α -> forall a, X a} : Measurab
le g ↔ forall a, Measurable fun x => g x a
· 使用定理 `MeasurableSMul.measurable_smul_const`：∀ {M : Type u_2} {α : Type u_3} {i
nst : SMul M α} {inst_1 : MeasurableSpace M} {inst_2 : MeasurableSpace α}   [sel
f : MeasurableSMul M α] (x…
-/
instance Pi.measurableSMul {ι : Type*} {α : ι → Type*} [∀ i, SMul M (α i)]
    [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableSMul M (α i)] :
    MeasurableSMul M (∀ i, α i) where
  measurable_smul_const _ := measurable_pi_iff.2 fun _ ↦ measurable_smul_const _

/-- `AddMonoid.SMul` is measurable. -/
/-
**AddMonoid.measurableSMul_nat** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`AddMonoid.SMul` is measurable.
-/
instance AddMonoid.measurableSMul_nat₂ (M : Type*) [AddMonoid M] [MeasurableSpace M]
    [MeasurableAdd₂ M] : MeasurableSMul₂ ℕ M :=
  ⟨by
    suffices Measurable fun p : M × ℕ => p.2 • p.1 by apply this.comp measurable_swap
    refine measurable_from_prod_countable_left fun n => ?_
    induction n with
    | zero => simp only [zero_smul, ← Pi.zero_def, measurable_zero]
    | succ n ih =>
      simp only [succ_nsmul]
      exact ih.add measurable_id⟩

/-- `SubNegMonoid.SMulInt` is measurable. -/
/-
**SubNegMonoid.measurableSMul_int** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`SubNegMonoid.SMulInt` is measurable.
-/
instance SubNegMonoid.measurableSMul_int₂ (M : Type*) [SubNegMonoid M] [MeasurableSpace M]
    [MeasurableAdd₂ M] [MeasurableNeg M] : MeasurableSMul₂ ℤ M :=
  ⟨by
    suffices Measurable fun p : M × ℤ => p.2 • p.1 by apply this.comp measurable_swap
    refine measurable_from_prod_countable_left fun n => ?_
    cases n with
    | ofNat n =>
      simp only [Int.ofNat_eq_natCast, natCast_zsmul]
      exact measurable_const_smul _
    | negSucc n =>
      simp only [negSucc_zsmul]
      exact (measurable_const_smul _).neg⟩

end SMul

section IterateMulAct

variable {α : Type*} {_ : MeasurableSpace α} {f : α → α}

@[to_additive]
/-
**Measurable.measurableSMul** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Measurable.measurableSMul₂_iterateMulAct (h : Measurable f) :
    MeasurableSMul₂ (IterateMulAct f) α where
  measurable_smul :=
    suffices Measurable fun p : α × IterateMulAct f ↦ f^[p.2.val] p.1 from this.comp measurable_swap
    measurable_from_prod_countable_left fun n ↦ h.iterate n.val

@[to_additive (attr := simp)]
/-
**measurableSMul_iterateMulAct** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurableSMul_iterateMulAct : MeasurableSMul (IterateMulAct f) α ↔ Measur
able f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableConstSMul.measurable_const_smul`：∀ {M : Type u_2} {α : Type u_
3} {inst : SMul M α} {inst_1 : MeasurableSpace α} [self : MeasurableConstSMul M 
α] (c : M),   Measurable fun x …
· 使用定理 `MeasurableSMul.toMeasurableConstSMul`：∀ {M : Type u_2} {α : Type u_3} {i
nst : SMul M α} {inst_1 : MeasurableSpace M} {inst_2 : MeasurableSpace α}   [sel
f : MeasurableSMul M α], M…
· 使用定理 `Measurable.measurableSMul₂_iterateMulAct`：Measurable.measurableSMul₂_ite
rateMulAct (h : Measurable f) : MeasurableSMul₂ (IterateMulAct f) α where measur
able_smul
· 使用定理 `MeasurableSMul₂.toMeasurableSMul`：∀ {M : Type u_2} {X : Type u_3} [inst 
: MeasurableSpace X] [inst_1 : SMul M X] [inst_2 : MeasurableSpace M]   [Measura
bleSMul₂ M X], Measura…
-/
theorem measurableSMul_iterateMulAct : MeasurableSMul (IterateMulAct f) α ↔ Measurable f :=
  ⟨fun _ ↦ measurable_const_smul (IterateMulAct.mk (f := f) 1), fun h ↦
    have := h.measurableSMul₂_iterateMulAct; inferInstance⟩

@[to_additive (attr := simp)]
/-
**measurableSMul** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem measurableSMul₂_iterateMulAct : MeasurableSMul₂ (IterateMulAct f) α ↔ Measurable f :=
  ⟨fun _ ↦ measurableSMul_iterateMulAct.mp inferInstance,
    Measurable.measurableSMul₂_iterateMulAct⟩

end IterateMulAct

section MulAction
variable {G G₀ M β α : Type*} [MeasurableSpace β] [MeasurableSpace α] {f : α → β} {μ : Measure α}

section Group
variable {G : Type*} [Group G] [MulAction G β] [MeasurableConstSMul G β]

@[to_additive]
/-
**measurable_const_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_const_smul_iff (c : G) : (Measurable fun x => c • f x) ↔ Measur
able f
参数：c : G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `inv_smul_smul`：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a
· 使用引理 `Measurable.const_smul`：Measurable.const_smul (hg : Measurable g) (c : M)
 : Measurable (c • g)
-/
theorem measurable_const_smul_iff (c : G) : (Measurable fun x => c • f x) ↔ Measurable f :=
  ⟨fun h => by simpa [inv_smul_smul, Pi.smul_def] using h.const_smul c⁻¹, fun h => h.const_smul c⟩

@[to_additive]
/-
**aemeasurable_const_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：aemeasurable_const_smul_iff (c : G) : AEMeasurable (fun x => c • f x) μ ↔ 
AEMeasurable f μ
参数：c : G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `inv_smul_smul`：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a
· 使用引理 `AEMeasurable.const_smul`：AEMeasurable.const_smul (hg : AEMeasurable g μ)
 (c : M) : AEMeasurable (c • g) μ
-/
theorem aemeasurable_const_smul_iff (c : G) :
    AEMeasurable (fun x => c • f x) μ ↔ AEMeasurable f μ :=
  ⟨fun h => by simpa [inv_smul_smul, Pi.smul_def] using h.const_smul c⁻¹, fun h => h.const_smul c⟩

end Group

section Monoid
variable [Monoid M] [MulAction M β]

section MeasurableConstSMul
variable [MeasurableConstSMul M β]

@[to_additive]
/-
**Units.instMeasurableConstSMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Units.instMeasurableConstSMul : MeasurableConstSMul Mˣ β where measurable_
const_smul c
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableConstSMul.measurable_const_smul`：∀ {M : Type u_2} {α : Type u_
3} {inst : SMul M α} {inst_1 : MeasurableSpace α} [self : MeasurableConstSMul M 
α] (c : M),   Measurable fun x …
-/
instance Units.instMeasurableConstSMul : MeasurableConstSMul Mˣ β where
  measurable_const_smul c := measurable_const_smul (c : M)

@[to_additive]
nonrec theorem IsUnit.measurable_const_smul_iff {c : M} (hc : IsUnit c) :
    (Measurable fun x => c • f x) ↔ Measurable f :=
  let ⟨u, hu⟩ := hc
  hu ▸ measurable_const_smul_iff u

@[to_additive]
nonrec theorem IsUnit.aemeasurable_const_smul_iff {c : M} (hc : IsUnit c) :
    AEMeasurable (fun x => c • f x) μ ↔ AEMeasurable f μ :=
  let ⟨u, hu⟩ := hc
  hu ▸ aemeasurable_const_smul_iff u

end MeasurableConstSMul

section MeasurableSMul
variable [MeasurableSpace M] [MeasurableSMul M β]

@[to_additive]
/-
**Units.instMeasurableSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Units.instMeasurableSpace : MeasurableSpace Mˣ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Units.instMeasurableSpace : MeasurableSpace Mˣ := .comap Units.val ‹_›

@[to_additive]
/-
**Units.measurableSMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Units.measurableSMul : MeasurableSMul Mˣ β where measurable_smul_const x
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSMul.toMeasurableConstSMul`：∀ {M : Type u_2} {α : Type u_3} {i
nst : SMul M α} {inst_1 : MeasurableSpace M} {inst_2 : MeasurableSpace α}   [sel
f : MeasurableSMul M α], M…
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `MeasurableSMul.measurable_smul_const`：∀ {M : Type u_2} {α : Type u_3} {i
nst : SMul M α} {inst_1 : MeasurableSpace M} {inst_2 : MeasurableSpace α}   [sel
f : MeasurableSMul M α] (x…
· 使用定理 `MeasurableSpace.le_map_comap`：le_map_comap : m <= (m.comap g).map g
-/
instance Units.measurableSMul : MeasurableSMul Mˣ β where
  measurable_smul_const x :=
    (measurable_smul_const x : Measurable fun c : M => c • x).comp MeasurableSpace.le_map_comap

end MeasurableSMul
end Monoid

section GroupWithZero
variable [GroupWithZero G₀] [MulAction G₀ β] [MeasurableConstSMul G₀ β]

/-
**measurable_const_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_const_smul_iff (c : G) : (Measurable fun x => c • f x) ↔ Measur
able f
参数：c : G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `inv_smul_smul`：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a
· 使用引理 `Measurable.const_smul`：Measurable.const_smul (hg : Measurable g) (c : M)
 : Measurable (c • g)
-/
theorem measurable_const_smul_iff₀ {c : G₀} (hc : c ≠ 0) :
    (Measurable fun x => c • f x) ↔ Measurable f :=
  (IsUnit.mk0 c hc).measurable_const_smul_iff
/-
**aemeasurable_const_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：aemeasurable_const_smul_iff (c : G) : AEMeasurable (fun x => c • f x) μ ↔ 
AEMeasurable f μ
参数：c : G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `inv_smul_smul`：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a
· 使用引理 `AEMeasurable.const_smul`：AEMeasurable.const_smul (hg : AEMeasurable g μ)
 (c : M) : AEMeasurable (c • g) μ
-/
theorem aemeasurable_const_smul_iff₀ {c : G₀} (hc : c ≠ 0) :
    AEMeasurable (fun x => c • f x) μ ↔ AEMeasurable f μ :=
  (IsUnit.mk0 c hc).aemeasurable_const_smul_iff

end GroupWithZero
end MulAction

/-!
### Opposite monoid
-/


section Opposite

open MulOpposite

@[to_additive]
/-
**MulOpposite.instMeasurableSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：MulOpposite.instMeasurableSpace {α : Type*} [h : MeasurableSpace α] : Meas
urableSpace αᵐᵒᵖ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance MulOpposite.instMeasurableSpace {α : Type*} [h : MeasurableSpace α] :
    MeasurableSpace αᵐᵒᵖ :=
  MeasurableSpace.map op h

@[to_additive]
/-
**measurable_mul_op** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_mul_op {α : Type*} [MeasurableSpace α] : Measurable (op : α -> 
αᵐᵒᵖ)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem measurable_mul_op {α : Type*} [MeasurableSpace α] : Measurable (op : α → αᵐᵒᵖ) := fun _ =>
  id

@[to_additive]
/-
**measurable_mul_unop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_mul_unop {α : Type*} [MeasurableSpace α] : Measurable (unop : α
ᵐᵒᵖ -> α)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem measurable_mul_unop {α : Type*} [MeasurableSpace α] : Measurable (unop : αᵐᵒᵖ → α) :=
  fun _ => id

@[to_additive]
/-
**MulOpposite.instMeasurableMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：MulOpposite.instMeasurableMul {M : Type*} [Mul M] [MeasurableSpace M] [Mea
surableMul M] : MeasurableMul Mᵐᵒᵖ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `measurable_mul_op`：measurable_mul_op {α : Type*} [MeasurableSpace α] : M
easurable (op : α -> αᵐᵒᵖ)
· 使用定理 `Measurable.mul_const`：Measurable.mul_const [MeasurableMul M] (hf : Measu
rable f) (c : M) : Measurable fun x => f x * c
· 使用定理 `measurable_mul_unop`：measurable_mul_unop {α : Type*} [MeasurableSpace α]
 : Measurable (unop : αᵐᵒᵖ -> α)
· 使用定理 `Measurable.const_mul`：Measurable.const_mul [MeasurableMul M] (hf : Measu
rable f) (c : M) : Measurable fun x => c * f x
-/
instance MulOpposite.instMeasurableMul {M : Type*} [Mul M] [MeasurableSpace M]
    [MeasurableMul M] : MeasurableMul Mᵐᵒᵖ :=
  ⟨fun _ => measurable_mul_op.comp (measurable_mul_unop.mul_const _), fun _ =>
    measurable_mul_op.comp (measurable_mul_unop.const_mul _)⟩

@[to_additive]
/-
**MulOpposite.instMeasurableMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：MulOpposite.instMeasurableMul {M : Type*} [Mul M] [MeasurableSpace M] [Mea
surableMul M] : MeasurableMul Mᵐᵒᵖ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `measurable_mul_op`：measurable_mul_op {α : Type*} [MeasurableSpace α] : M
easurable (op : α -> αᵐᵒᵖ)
· 使用定理 `Measurable.mul_const`：Measurable.mul_const [MeasurableMul M] (hf : Measu
rable f) (c : M) : Measurable fun x => f x * c
· 使用定理 `measurable_mul_unop`：measurable_mul_unop {α : Type*} [MeasurableSpace α]
 : Measurable (unop : αᵐᵒᵖ -> α)
· 使用定理 `Measurable.const_mul`：Measurable.const_mul [MeasurableMul M] (hf : Measu
rable f) (c : M) : Measurable fun x => c * f x
-/
instance MulOpposite.instMeasurableMul₂ {M : Type*} [Mul M] [MeasurableSpace M]
    [MeasurableMul₂ M] : MeasurableMul₂ Mᵐᵒᵖ :=
  ⟨measurable_mul_op.comp
      ((measurable_mul_unop.comp measurable_snd).mul (measurable_mul_unop.comp measurable_fst))⟩

/-- If a scalar is central, then its right action is measurable when its left action is. -/
@[to_additive /-- If a vector is central, then its right action is measurable when its left
action is. -/]
nonrec instance MeasurableSMul.op {M α} [MeasurableSpace M] [MeasurableSpace α] [SMul M α]
    [SMul Mᵐᵒᵖ α] [IsCentralScalar M α] [MeasurableSMul M α] : MeasurableSMul Mᵐᵒᵖ α where
  measurable_smul_const x :=
    show Measurable fun c => op (unop c) • x by
      simpa only [op_smul_eq_smul] using! (measurable_smul_const x).comp measurable_mul_unop

/-- If a scalar is central, then its right action is measurable when its left action is. -/
nonrec instance MeasurableSMul₂.op {M α} [MeasurableSpace M] [MeasurableSpace α] [SMul M α]
    [SMul Mᵐᵒᵖ α] [IsCentralScalar M α] [MeasurableSMul₂ M α] : MeasurableSMul₂ Mᵐᵒᵖ α :=
  ⟨show Measurable fun x : Mᵐᵒᵖ × α => op (unop x.1) • x.2 by
      simp_rw [op_smul_eq_smul]
      exact (measurable_mul_unop.comp measurable_fst).smul measurable_snd⟩

@[to_additive]
/-
**measurableSMul_opposite_of_mul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：measurableSMul_opposite_of_mul {M : Type*} [Mul M] [MeasurableSpace M] [Me
asurableMul M] : MeasurableSMul Mᵐᵒᵖ M where measurable_smul_const x
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.mul_const`：Measurable.mul_const [MeasurableMul M] (hf : Measu
rable f) (c : M) : Measurable fun x => f x * c
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
· 使用定理 `Measurable.const_mul`：Measurable.const_mul [MeasurableMul M] (hf : Measu
rable f) (c : M) : Measurable fun x => c * f x
· 使用定理 `measurable_mul_unop`：measurable_mul_unop {α : Type*} [MeasurableSpace α]
 : Measurable (unop : αᵐᵒᵖ -> α)
-/
instance measurableSMul_opposite_of_mul {M : Type*} [Mul M] [MeasurableSpace M]
    [MeasurableMul M] : MeasurableSMul Mᵐᵒᵖ M where
  measurable_smul_const x := measurable_mul_unop.const_mul x

@[to_additive]
/-
**measurableSMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance measurableSMul₂_opposite_of_mul {M : Type*} [Mul M] [MeasurableSpace M]
    [MeasurableMul₂ M] : MeasurableSMul₂ Mᵐᵒᵖ M :=
  ⟨measurable_snd.mul (measurable_mul_unop.comp measurable_fst)⟩

end Opposite

/-!
### Big operators: `∏` and `∑`
-/


section Monoid

variable {M α : Type*} [Monoid M] [MeasurableSpace M] [MeasurableMul₂ M] {m : MeasurableSpace α}
  {μ : Measure α}

-- TODO: `fun_prop` cannot use lemmas with a condition quantifying over the function
@[to_additive (attr := fun_prop)]
/-
**List.measurable_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：List.measurable_prod (l : List (α -> M)) (hl : forall f in l, Measurable f
) : Measurable l.prod
参数：l : List (α -> M)；hl : forall f in l, Measurable f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_one`：measurable_one [One α] : Measurable (1 : β -> α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.prod_cons`：∀ {α : Type u} [inst : Mul α] [inst_1 : One α] {a : α} {
l : List α}, (a :: l).prod = a * l.prod
· 使用定理 `Measurable.mul`：Measurable.mul [MeasurableMul₂ M] (hf : Measurable f) (h
g : Measurable g) : Measurable (f * g)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `List.forall_mem_cons`：∀ {α : Type u_1} {p : α → Prop} {a : α} {l : List 
α}, (∀ x ∈ a :: l, p x) ↔ p a ∧ ∀ x ∈ l, p x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem List.measurable_prod (l : List (α → M)) (hl : ∀ f ∈ l, Measurable f) :
    Measurable l.prod := by
  induction l with
  | nil => exact measurable_one
  | cons f l ihl =>
    rw [List.forall_mem_cons] at hl
    rw [List.prod_cons]
    exact hl.1.mul (ihl hl.2)

@[to_additive (attr := fun_prop)]
/-
**List.aemeasurable_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：List.aemeasurable_prod (l : List (α -> M)) (hl : forall f in l, AEMeasurab
le f μ) : AEMeasurable l.prod μ
参数：l : List (α -> M)；hl : forall f in l, AEMeasurable f μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `aemeasurable_one`：aemeasurable_one [One β] : AEMeasurable (fun _ : α => 
(1 : β)) μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.prod_cons`：∀ {α : Type u} [inst : Mul α] [inst_1 : One α] {a : α} {
l : List α}, (a :: l).prod = a * l.prod
· 使用定理 `AEMeasurable.mul`：AEMeasurable.mul [MeasurableMul₂ M] (hf : AEMeasurable
 f μ) (hg : AEMeasurable g μ) : AEMeasurable (f * g) μ
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `List.forall_mem_cons`：∀ {α : Type u_1} {p : α → Prop} {a : α} {l : List 
α}, (∀ x ∈ a :: l, p x) ↔ p a ∧ ∀ x ∈ l, p x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem List.aemeasurable_prod (l : List (α → M)) (hl : ∀ f ∈ l, AEMeasurable f μ) :
    AEMeasurable l.prod μ := by
  induction l with
  | nil => exact aemeasurable_one
  | cons f l ihl =>
    rw [List.forall_mem_cons] at hl
    rw [List.prod_cons]
    exact hl.1.mul (ihl hl.2)

@[to_additive (attr := fun_prop)]
/-
**List.measurable_fun_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：List.measurable_fun_prod (l : List (α -> M)) (hl : forall f in l, Measurab
le f) : Measurable fun x => (l.map fun f : α -> M => f x).prod
参数：l : List (α -> M)；hl : forall f in l, Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `List.measurable_prod`：List.measurable_prod (l : List (α -> M)) (hl : for
all f in l, Measurable f) : Measurable l.prod
-/
theorem List.measurable_fun_prod (l : List (α → M)) (hl : ∀ f ∈ l, Measurable f) :
    Measurable fun x => (l.map fun f : α → M => f x).prod := by
  simpa only [← Pi.list_prod_apply] using l.measurable_prod hl

@[to_additive (attr := fun_prop)]
/-
**List.aemeasurable_fun_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：List.aemeasurable_fun_prod (l : List (α -> M)) (hl : forall f in l, AEMeas
urable f μ) : AEMeasurable (fun x => (l.map fun f : α -> M => f x).prod) μ
参数：l : List (α -> M)；hl : forall f in l, AEMeasurable f μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `List.aemeasurable_prod`：List.aemeasurable_prod (l : List (α -> M)) (hl :
 forall f in l, AEMeasurable f μ) : AEMeasurable l.prod μ
-/
theorem List.aemeasurable_fun_prod (l : List (α → M)) (hl : ∀ f ∈ l, AEMeasurable f μ) :
    AEMeasurable (fun x => (l.map fun f : α → M => f x).prod) μ := by
  simpa only [← Pi.list_prod_apply] using l.aemeasurable_prod hl

end Monoid

section CommMonoid

variable {M ι α β : Type*} [CommMonoid M] [MeasurableSpace M] [MeasurableMul₂ M]
  {m : MeasurableSpace α} {mβ : MeasurableSpace β} {μ : Measure α} {f : ι → α → M}

@[to_additive (attr := fun_prop)]
/-
**Multiset.measurable_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Multiset.measurable_prod (l : Multiset (α -> M)) (hl : forall f in l, Meas
urable f) : Measurable l.prod
参数：l : Multiset (α -> M)；hl : forall f in l, Measurable f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.measurable_prod`：List.measurable_prod (l : List (α -> M)) (hl : for
all f in l, Measurable f) : Measurable l.prod
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem Multiset.measurable_prod (l : Multiset (α → M)) (hl : ∀ f ∈ l, Measurable f) :
    Measurable l.prod := by
  rcases l with ⟨l⟩
  simpa using l.measurable_prod (by simpa using hl)

@[to_additive (attr := fun_prop)]
/-
**Multiset.aemeasurable_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Multiset.aemeasurable_prod (l : Multiset (α -> M)) (hl : forall f in l, AE
Measurable f μ) : AEMeasurable l.prod μ
参数：l : Multiset (α -> M)；hl : forall f in l, AEMeasurable f μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.aemeasurable_prod`：List.aemeasurable_prod (l : List (α -> M)) (hl :
 forall f in l, AEMeasurable f μ) : AEMeasurable l.prod μ
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem Multiset.aemeasurable_prod (l : Multiset (α → M)) (hl : ∀ f ∈ l, AEMeasurable f μ) :
    AEMeasurable l.prod μ := by
  rcases l with ⟨l⟩
  simpa using l.aemeasurable_prod (by simpa using hl)

@[to_additive (attr := fun_prop)]
/-
**Multiset.measurable_fun_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Multiset.measurable_fun_prod (s : Multiset (α -> M)) (hs : forall f in s, 
Measurable f) : Measurable fun x => (s.map fun f : α -> M => f x).prod
参数：s : Multiset (α -> M)；hs : forall f in s, Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Multiset.measurable_prod`：Multiset.measurable_prod (l : Multiset (α -> M
)) (hl : forall f in l, Measurable f) : Measurable l.prod
-/
theorem Multiset.measurable_fun_prod (s : Multiset (α → M)) (hs : ∀ f ∈ s, Measurable f) :
    Measurable fun x => (s.map fun f : α → M => f x).prod := by
  simpa only [← Pi.multiset_prod_apply] using s.measurable_prod hs

@[to_additive (attr := fun_prop)]
/-
**Multiset.aemeasurable_fun_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Multiset.aemeasurable_fun_prod (s : Multiset (α -> M)) (hs : forall f in s
, AEMeasurable f μ) : AEMeasurable (fun x => (s.map fun f : α -> M => f x).prod)
 μ
参数：s : Multiset (α -> M)；hs : forall f in s, AEMeasurable f μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Multiset.aemeasurable_prod`：Multiset.aemeasurable_prod (l : Multiset (α 
-> M)) (hl : forall f in l, AEMeasurable f μ) : AEMeasurable l.prod μ
-/
theorem Multiset.aemeasurable_fun_prod (s : Multiset (α → M)) (hs : ∀ f ∈ s, AEMeasurable f μ) :
    AEMeasurable (fun x => (s.map fun f : α → M => f x).prod) μ := by
  simpa only [← Pi.multiset_prod_apply] using s.aemeasurable_prod hs

@[to_additive (attr := fun_prop)]
/-
**Finset.measurable_fun_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.measurable_fun_prod (s : Finset ι) (hf : forall i in s, Measurable 
(f i)) : Measurable fun a => ∏ i in s, f i a
参数：s : Finset ι；hf : forall i in s, Measurable (f i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.prod_induction`：prod_induction {M : Type*} [CommMonoid M] (f : ι 
-> M) (p : M -> Prop) (hom : forall a b, p a -> p b -> p (a * b)) (unit : p 1) (
base : fora…
· 使用定理 `Measurable.mul`：Measurable.mul [MeasurableMul₂ M] (hf : Measurable f) (h
g : Measurable g) : Measurable (f * g)
· 使用定理 `measurable_one`：measurable_one [One α] : Measurable (1 : β -> α)
-/
theorem Finset.measurable_fun_prod (s : Finset ι) (hf : ∀ i ∈ s, Measurable (f i)) :
    Measurable fun a ↦ ∏ i ∈ s, f i a := by
  simp_rw [← Finset.prod_apply]
  exact Finset.prod_induction _ _ (fun _ _ => Measurable.mul) (@measurable_one M _ _ _ _) hf

@[to_additive (attr := fun_prop)]
/-
**Finset.measurable_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.measurable_prod (s : Finset ι) (hf : forall i in s, Measurable (f i
)) : Measurable fun a => ∏ i in s, f i a
参数：s : Finset ι；hf : forall i in s, Measurable (f i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.prod_induction`：prod_induction {M : Type*} [CommMonoid M] (f : ι 
-> M) (p : M -> Prop) (hom : forall a b, p a -> p b -> p (a * b)) (unit : p 1) (
base : fora…
· 使用定理 `Measurable.mul`：Measurable.mul [MeasurableMul₂ M] (hf : Measurable f) (h
g : Measurable g) : Measurable (f * g)
· 使用定理 `measurable_one`：measurable_one [One α] : Measurable (1 : β -> α)
-/
theorem Finset.measurable_prod (s : Finset ι) (hf : ∀ i ∈ s, Measurable (f i)) :
    Measurable fun a ↦ ∏ i ∈ s, f i a := by
  simp_rw [← Finset.prod_apply]
  exact Finset.prod_induction _ _ (fun _ _ => Measurable.mul) (@measurable_one M _ _ _ _) hf

/-- Compositional version of `Finset.measurable_prod` for use by `fun_prop`. -/
@[to_additive (attr := fun_prop)
/-- Compositional version of `Finset.measurable_sum` for use by `fun_prop`. -/]
/-
**Finset.measurable_prod_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Finset.measurable_prod_apply {f : ι -> α -> β -> M} {g : α -> β} {s : Fins
et ι} (hf : forall i in s, Measurable ↿(f i)) (hg : Measurable g) : Measurable f
un a => (∏ i in s, f i a) (g a)
参数：hf : forall i in s, Measurable ↿(f i)；hg : Measurable g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.prod_apply`：Finset.prod_apply {α : Type*} {M : α -> Type*} [foral
l a, CommMonoid (M a)] (a : α) (s : Finset ι) (g : ι -> forall a, M a) : (∏ c in
 s, g c…
· 使用定理 `Finset.measurable_prod`：Finset.measurable_prod (s : Finset ι) (hf : fora
ll i in s, Measurable (f i)) : Measurable fun a => ∏ i in s, f i a
· 使用定理 `Measurable.fun_comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x :
 MeasurableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β
 → γ} {f …
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
-/
lemma Finset.measurable_prod_apply {f : ι → α → β → M} {g : α → β} {s : Finset ι}
    (hf : ∀ i ∈ s, Measurable ↿(f i)) (hg : Measurable g) :
    Measurable fun a ↦ (∏ i ∈ s, f i a) (g a) := by
  simp only [prod_apply]; fun_prop

@[to_additive (attr := fun_prop)]
/-
**Finset.aemeasurable_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.aemeasurable_prod (s : Finset ι) (hf : forall i in s, AEMeasurable 
(f i) μ) : AEMeasurable (∏ i in s, f i) μ
参数：s : Finset ι；hf : forall i in s, AEMeasurable (f i) μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.aemeasurable_prod`：Multiset.aemeasurable_prod (l : Multiset (α 
-> M)) (hl : forall f in l, AEMeasurable f μ) : AEMeasurable l.prod μ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_map`：mem_map {f : α -> β} {b : β} {s : Multiset α} : b in m
ap f s ↔ exists a, a in s ∧ f a = b
-/
theorem Finset.aemeasurable_prod (s : Finset ι) (hf : ∀ i ∈ s, AEMeasurable (f i) μ) :
    AEMeasurable (∏ i ∈ s, f i) μ :=
  Multiset.aemeasurable_prod _ fun _g hg =>
    let ⟨_i, hi, hg⟩ := Multiset.mem_map.1 hg
    hg ▸ hf _ hi

@[to_additive (attr := fun_prop)]
/-
**Finset.aemeasurable_fun_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.aemeasurable_fun_prod (s : Finset ι) (hf : forall i in s, AEMeasura
ble (f i) μ) : AEMeasurable (fun a => ∏ i in s, f i a) μ
参数：s : Finset ι；hf : forall i in s, AEMeasurable (f i) μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.aemeasurable_prod`：Finset.aemeasurable_prod (s : Finset ι) (hf : 
forall i in s, AEMeasurable (f i) μ) : AEMeasurable (∏ i in s, f i) μ
-/
theorem Finset.aemeasurable_fun_prod (s : Finset ι) (hf : ∀ i ∈ s, AEMeasurable (f i) μ) :
    AEMeasurable (fun a => ∏ i ∈ s, f i a) μ := by
  simpa only [← Finset.prod_apply] using s.aemeasurable_prod hf

end CommMonoid

variable [MeasurableSpace α] [Mul α] [Div α] [Inv α]

@[to_additive] -- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) DiscreteMeasurableSpace.toMeasurableMul [DiscreteMeasurableSpace α] :
    MeasurableMul α where

@[to_additive DiscreteMeasurableSpace.toMeasurableAdd₂] -- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) DiscreteMeasurableSpace.toMeasurableMul₂
    [DiscreteMeasurableSpace (α × α)] : MeasurableMul₂ α := ⟨.of_discrete⟩

@[to_additive] -- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) DiscreteMeasurableSpace.toMeasurableInv [DiscreteMeasurableSpace α] :
    MeasurableInv α := ⟨.of_discrete⟩

@[to_additive] -- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) DiscreteMeasurableSpace.toMeasurableDiv [DiscreteMeasurableSpace α] :
    MeasurableDiv α where

@[to_additive DiscreteMeasurableSpace.toMeasurableSub₂] -- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) DiscreteMeasurableSpace.toMeasurableDiv₂
    [DiscreteMeasurableSpace (α × α)] : MeasurableDiv₂ α := ⟨.of_discrete⟩
