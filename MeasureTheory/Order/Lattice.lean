/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.AEMeasurable

/-!
# Typeclasses for measurability of lattice operations

In this file we define classes `MeasurableSup` and `MeasurableInf` and prove dot-style
lemmas (`Measurable.sup`, `AEMeasurable.sup` etc). For binary operations we define two typeclasses:

- `MeasurableSup` says that both left and right sup are measurable;
- `MeasurableSup₂` says that `fun p : α × α => p.1 ⊔ p.2` is measurable,

and similarly for other binary operations. The reason for introducing these classes is that in case
of topological space `α` equipped with the Borel `σ`-algebra, instances for `MeasurableSup₂`
etc. require `α` to have a second countable topology.

For instances relating, e.g., `ContinuousSup` to `MeasurableSup` see file
`MeasureTheory.BorelSpace`.

## Tags

measurable function, lattice operation

-/

public section


open MeasureTheory

/-- We say that a type has `MeasurableSup` if `(c ⊔ ·)` and `(· ⊔ c)` are measurable functions.
For a typeclass assuming measurability of `uncurry (· ⊔ ·)` see `MeasurableSup₂`. -/
/-
**MeasurableSup** 是 Mathlib 中的一个类，位于命名空间 ``。
形式化陈述：MeasurableSup (M : Type*) [MeasurableSpace M] [Max M] : Prop where measura
ble_const_sup : forall c : M, Measurable (c ⊔ ·)
参数：M : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that a type has `MeasurableSup` if `(c ⊔ ·)` and `(· ⊔ c)` are measurable
 functions.
For a typeclass assuming measurability of `uncurry (· ⊔ ·)` see `MeasurableSup₂`
.
-/
class MeasurableSup (M : Type*) [MeasurableSpace M] [Max M] : Prop where
  measurable_const_sup : ∀ c : M, Measurable (c ⊔ ·) := by intro c; fun_prop
  measurable_sup_const : ∀ c : M, Measurable (· ⊔ c) := by intro c; fun_prop

/-- We say that a type has `MeasurableSup₂` if `uncurry (· ⊔ ·)` is a measurable functions.
For a typeclass assuming measurability of `(c ⊔ ·)` and `(· ⊔ c)` see `MeasurableSup`. -/
/-
**MeasurableSup** 是 Mathlib 中的一个类，位于命名空间 ``。
形式化陈述：MeasurableSup (M : Type*) [MeasurableSpace M] [Max M] : Prop where measura
ble_const_sup : forall c : M, Measurable (c ⊔ ·)
参数：M : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that a type has `MeasurableSup₂` if `uncurry (· ⊔ ·)` is a measurable fun
ctions.
For a typeclass assuming measurability of `(c ⊔ ·)` and `(· ⊔ c)` see `Measurabl
eSup`.
-/
class MeasurableSup₂ (M : Type*) [MeasurableSpace M] [Max M] : Prop where
  measurable_sup : Measurable fun p : M × M => p.1 ⊔ p.2 := by intro p; fun_prop

export MeasurableSup₂ (measurable_sup)

export MeasurableSup (measurable_const_sup measurable_sup_const)

/-- We say that a type has `MeasurableInf` if `(c ⊓ ·)` and `(· ⊓ c)` are measurable functions.
For a typeclass assuming measurability of `uncurry (· ⊓ ·)` see `MeasurableInf₂`. -/
/-
**MeasurableInf** 是 Mathlib 中的一个类，位于命名空间 ``。
形式化陈述：MeasurableInf (M : Type*) [MeasurableSpace M] [Min M] : Prop where measura
ble_const_inf : forall c : M, Measurable (c ⊓ ·)
参数：M : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that a type has `MeasurableInf` if `(c ⊓ ·)` and `(· ⊓ c)` are measurable
 functions.
For a typeclass assuming measurability of `uncurry (· ⊓ ·)` see `MeasurableInf₂`
.
-/
class MeasurableInf (M : Type*) [MeasurableSpace M] [Min M] : Prop where
  measurable_const_inf : ∀ c : M, Measurable (c ⊓ ·) := by intro c; fun_prop
  measurable_inf_const : ∀ c : M, Measurable (· ⊓ c) := by intro c; fun_prop

/-- We say that a type has `MeasurableInf₂` if `uncurry (· ⊓ ·)` is a measurable functions.
For a typeclass assuming measurability of `(c ⊓ ·)` and `(· ⊓ c)` see `MeasurableInf`. -/
/-
**MeasurableInf** 是 Mathlib 中的一个类，位于命名空间 ``。
形式化陈述：MeasurableInf (M : Type*) [MeasurableSpace M] [Min M] : Prop where measura
ble_const_inf : forall c : M, Measurable (c ⊓ ·)
参数：M : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that a type has `MeasurableInf₂` if `uncurry (· ⊓ ·)` is a measurable fun
ctions.
For a typeclass assuming measurability of `(c ⊓ ·)` and `(· ⊓ c)` see `Measurabl
eInf`.
-/
class MeasurableInf₂ (M : Type*) [MeasurableSpace M] [Min M] : Prop where
  measurable_inf : Measurable fun p : M × M => p.1 ⊓ p.2 := by intro p; fun_prop

export MeasurableInf₂ (measurable_inf)

export MeasurableInf (measurable_const_inf measurable_inf_const)

variable {M : Type*} [MeasurableSpace M]

section OrderDual

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) OrderDual.instMeasurableSup [Min M] [MeasurableInf M] :
    MeasurableSup Mᵒᵈ :=
  ⟨@measurable_const_inf M _ _ _, @measurable_inf_const M _ _ _⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) OrderDual.instMeasurableInf [Max M] [MeasurableSup M] :
    MeasurableInf Mᵒᵈ :=
  ⟨@measurable_const_sup M _ _ _, @measurable_sup_const M _ _ _⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) OrderDual.instMeasurableSup₂ [Min M] [MeasurableInf₂ M] :
    MeasurableSup₂ Mᵒᵈ :=
  ⟨@measurable_inf M _ _ _⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) OrderDual.instMeasurableInf₂ [Max M] [MeasurableSup₂ M] :
    MeasurableInf₂ Mᵒᵈ :=
  ⟨@measurable_sup M _ _ _⟩

end OrderDual

variable {α : Type*} {m : MeasurableSpace α} {μ : Measure α} {f g : α → M}

section Sup

variable [Max M]

section MeasurableSup

variable [MeasurableSup M]

@[fun_prop]
/-
**Measurable.const_sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.const_sup (hf : Measurable f) (c : M) : Measurable fun x => c ⊔
 f x
参数：hf : Measurable f；c : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `MeasurableSup.measurable_const_sup`：∀ {M : Type u_1} {inst : MeasurableS
pace M} {inst_1 : Max M} [self : MeasurableSup M] (c : M), Measurable fun x => c
 ⊔ x
-/
theorem Measurable.const_sup (hf : Measurable f) (c : M) : Measurable fun x => c ⊔ f x :=
  (measurable_const_sup c).comp hf

@[fun_prop]
/-
**AEMeasurable.const_sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AEMeasurable.const_sup (hf : AEMeasurable f μ) (c : M) : AEMeasurable (fun
 x => c ⊔ f x) μ
参数：hf : AEMeasurable f μ；c : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp_aemeasurable`：Measurable.comp_aemeasurable [MeasurableSp
ace δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) : A
EMeasurable (g ∘ f…
· 使用定理 `MeasurableSup.measurable_const_sup`：∀ {M : Type u_1} {inst : MeasurableS
pace M} {inst_1 : Max M} [self : MeasurableSup M] (c : M), Measurable fun x => c
 ⊔ x
-/
theorem AEMeasurable.const_sup (hf : AEMeasurable f μ) (c : M) :
    AEMeasurable (fun x => c ⊔ f x) μ :=
  (MeasurableSup.measurable_const_sup c).comp_aemeasurable hf

@[fun_prop]
/-
**Measurable.sup_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.sup_const (hf : Measurable f) (c : M) : Measurable fun x => f x
 ⊔ c
参数：hf : Measurable f；c : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `MeasurableSup.measurable_sup_const`：∀ {M : Type u_1} {inst : MeasurableS
pace M} {inst_1 : Max M} [self : MeasurableSup M] (c : M), Measurable fun x => x
 ⊔ c
-/
theorem Measurable.sup_const (hf : Measurable f) (c : M) : Measurable fun x => f x ⊔ c :=
  (measurable_sup_const c).comp hf

@[fun_prop]
/-
**AEMeasurable.sup_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AEMeasurable.sup_const (hf : AEMeasurable f μ) (c : M) : AEMeasurable (fun
 x => f x ⊔ c) μ
参数：hf : AEMeasurable f μ；c : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp_aemeasurable`：Measurable.comp_aemeasurable [MeasurableSp
ace δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) : A
EMeasurable (g ∘ f…
· 使用定理 `MeasurableSup.measurable_sup_const`：∀ {M : Type u_1} {inst : MeasurableS
pace M} {inst_1 : Max M} [self : MeasurableSup M] (c : M), Measurable fun x => x
 ⊔ c
-/
theorem AEMeasurable.sup_const (hf : AEMeasurable f μ) (c : M) :
    AEMeasurable (fun x => f x ⊔ c) μ :=
  (measurable_sup_const c).comp_aemeasurable hf

end MeasurableSup

section MeasurableSup₂

variable [MeasurableSup₂ M]

@[to_fun (attr := fun_prop)]
/-
**Measurable.sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.sup (hf : Measurable f) (hg : Measurable g) : Measurable (f ⊔ g
)
参数：hf : Measurable f；hg : Measurable g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `MeasurableSup₂.measurable_sup`：∀ {M : Type u_1} {inst : MeasurableSpace 
M} {inst_1 : Max M} [self : MeasurableSup₂ M], Measurable fun p => p.1 ⊔ p.2
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
-/
theorem Measurable.sup (hf : Measurable f) (hg : Measurable g) : Measurable (f ⊔ g) :=
  measurable_sup.comp (hf.prodMk hg)

@[deprecated (since := "2026-06-26")] alias Measurable.sup' := Measurable.sup

@[to_fun (attr := fun_prop)]
/-
**AEMeasurable.sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AEMeasurable.sup (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) : AEMeasu
rable (f ⊔ g) μ
参数：hf : AEMeasurable f μ；hg : AEMeasurable g μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp_aemeasurable`：Measurable.comp_aemeasurable [MeasurableSp
ace δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) : A
EMeasurable (g ∘ f…
· 使用定理 `MeasurableSup₂.measurable_sup`：∀ {M : Type u_1} {inst : MeasurableSpace 
M} {inst_1 : Max M} [self : MeasurableSup₂ M], Measurable fun p => p.1 ⊔ p.2
· 使用定理 `AEMeasurable.prodMk`：prodMk {f : α -> β} {g : α -> γ} (hf : AEMeasurable
 f μ) (hg : AEMeasurable g μ) : AEMeasurable (fun x => (f x, g x)) μ
-/
theorem AEMeasurable.sup (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    AEMeasurable (f ⊔ g) μ :=
  measurable_sup.comp_aemeasurable (hf.prodMk hg)

@[deprecated (since := "2026-06-26")] alias AEMeasurable.sup' := AEMeasurable.sup
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) MeasurableSup₂.toMeasurableSup : MeasurableSup M where

end MeasurableSup₂

end Sup

section Inf

variable [Min M]

section MeasurableInf

variable [MeasurableInf M]

@[fun_prop]
/-
**Measurable.const_inf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.const_inf (hf : Measurable f) (c : M) : Measurable fun x => c ⊓
 f x
参数：hf : Measurable f；c : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `MeasurableInf.measurable_const_inf`：∀ {M : Type u_1} {inst : MeasurableS
pace M} {inst_1 : Min M} [self : MeasurableInf M] (c : M), Measurable fun x => c
 ⊓ x
-/
theorem Measurable.const_inf (hf : Measurable f) (c : M) : Measurable fun x => c ⊓ f x :=
  (measurable_const_inf c).comp hf

@[fun_prop]
/-
**AEMeasurable.const_inf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AEMeasurable.const_inf (hf : AEMeasurable f μ) (c : M) : AEMeasurable (fun
 x => c ⊓ f x) μ
参数：hf : AEMeasurable f μ；c : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp_aemeasurable`：Measurable.comp_aemeasurable [MeasurableSp
ace δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) : A
EMeasurable (g ∘ f…
· 使用定理 `MeasurableInf.measurable_const_inf`：∀ {M : Type u_1} {inst : MeasurableS
pace M} {inst_1 : Min M} [self : MeasurableInf M] (c : M), Measurable fun x => c
 ⊓ x
-/
theorem AEMeasurable.const_inf (hf : AEMeasurable f μ) (c : M) :
    AEMeasurable (fun x => c ⊓ f x) μ :=
  (MeasurableInf.measurable_const_inf c).comp_aemeasurable hf

@[fun_prop]
/-
**Measurable.inf_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.inf_const (hf : Measurable f) (c : M) : Measurable fun x => f x
 ⊓ c
参数：hf : Measurable f；c : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `MeasurableInf.measurable_inf_const`：∀ {M : Type u_1} {inst : MeasurableS
pace M} {inst_1 : Min M} [self : MeasurableInf M] (c : M), Measurable fun x => x
 ⊓ c
-/
theorem Measurable.inf_const (hf : Measurable f) (c : M) : Measurable fun x => f x ⊓ c :=
  (measurable_inf_const c).comp hf

@[fun_prop]
/-
**AEMeasurable.inf_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AEMeasurable.inf_const (hf : AEMeasurable f μ) (c : M) : AEMeasurable (fun
 x => f x ⊓ c) μ
参数：hf : AEMeasurable f μ；c : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp_aemeasurable`：Measurable.comp_aemeasurable [MeasurableSp
ace δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) : A
EMeasurable (g ∘ f…
· 使用定理 `MeasurableInf.measurable_inf_const`：∀ {M : Type u_1} {inst : MeasurableS
pace M} {inst_1 : Min M} [self : MeasurableInf M] (c : M), Measurable fun x => x
 ⊓ c
-/
theorem AEMeasurable.inf_const (hf : AEMeasurable f μ) (c : M) :
    AEMeasurable (fun x => f x ⊓ c) μ :=
  (measurable_inf_const c).comp_aemeasurable hf

end MeasurableInf

section MeasurableInf₂

variable [MeasurableInf₂ M]

@[to_fun (attr := fun_prop)]
/-
**Measurable.inf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.inf (hf : Measurable f) (hg : Measurable g) : Measurable (f ⊓ g
)
参数：hf : Measurable f；hg : Measurable g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `MeasurableInf₂.measurable_inf`：∀ {M : Type u_1} {inst : MeasurableSpace 
M} {inst_1 : Min M} [self : MeasurableInf₂ M], Measurable fun p => p.1 ⊓ p.2
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
-/
theorem Measurable.inf (hf : Measurable f) (hg : Measurable g) : Measurable (f ⊓ g) :=
  measurable_inf.comp (hf.prodMk hg)

@[deprecated (since := "2026-06-26")] alias Measurable.inf' := Measurable.inf

@[to_fun (attr := fun_prop)]
/-
**AEMeasurable.inf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AEMeasurable.inf (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) : AEMeasu
rable (f ⊓ g) μ
参数：hf : AEMeasurable f μ；hg : AEMeasurable g μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp_aemeasurable`：Measurable.comp_aemeasurable [MeasurableSp
ace δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) : A
EMeasurable (g ∘ f…
· 使用定理 `MeasurableInf₂.measurable_inf`：∀ {M : Type u_1} {inst : MeasurableSpace 
M} {inst_1 : Min M} [self : MeasurableInf₂ M], Measurable fun p => p.1 ⊓ p.2
· 使用定理 `AEMeasurable.prodMk`：prodMk {f : α -> β} {g : α -> γ} (hf : AEMeasurable
 f μ) (hg : AEMeasurable g μ) : AEMeasurable (fun x => (f x, g x)) μ
-/
theorem AEMeasurable.inf (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    AEMeasurable (f ⊓ g) μ :=
  measurable_inf.comp_aemeasurable (hf.prodMk hg)

@[deprecated (since := "2026-06-26")] alias AEMeasurable.inf' := AEMeasurable.inf
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) MeasurableInf₂.to_hasMeasurableInf : MeasurableInf M where

end MeasurableInf₂

end Inf

section SemilatticeSup

open Finset

variable {δ : Type*} [MeasurableSpace δ] [SemilatticeSup α] [MeasurableSup₂ α]

@[fun_prop]
/-
**Finset.measurable_sup'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.measurable_sup' {ι : Type*} {s : Finset ι} (hs : s.Nonempty) {f : ι
 -> δ -> α} (hf : forall n in s, Measurable (f n)) : Measurable (s.sup' hs f)
参数：hs : s.Nonempty；hf : forall n in s, Measurable (f n)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sup'_induction`：∀ {α : Type u_2} {β : Type u_3} [inst : Semilatti
ceSup α] {s : Finset β} (H : s.Nonempty) (f : β → α) {p : α → Prop},   (∀ (a₁ : 
α), p a₁ → …
· 使用定理 `Measurable.sup`：Measurable.sup (hf : Measurable f) (hg : Measurable g) :
 Measurable (f ⊔ g)
-/
theorem Finset.measurable_sup' {ι : Type*} {s : Finset ι} (hs : s.Nonempty) {f : ι → δ → α}
    (hf : ∀ n ∈ s, Measurable (f n)) : Measurable (s.sup' hs f) :=
  Finset.sup'_induction hs _ (fun _f hf _g hg => hf.sup hg) fun n hn => hf n hn

@[fun_prop]
/-
**Finset.measurable_range_sup'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.measurable_range_sup' {f : Nat -> δ -> α} {n : Nat} (hf : forall k 
<= n, Measurable (f k)) : Measurable ((range (n + 1)).sup' nonempty_range_add_on
e f)
参数：hf : forall k <= n, Measurable (f k)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.measurable_sup'`：Finset.measurable_sup' {ι : Type*} {s : Finset ι
} (hs : s.Nonempty) {f : ι -> δ -> α} (hf : forall n in s, Measurable (f n)) : M
easurable (s…
· 使用定理 `Finset.nonempty_range_add_one`：nonempty_range_add_one : (range <| n + 1)
.Nonempty
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem Finset.measurable_range_sup' {f : ℕ → δ → α} {n : ℕ} (hf : ∀ k ≤ n, Measurable (f k)) :
    Measurable ((range (n + 1)).sup' nonempty_range_add_one f) := by
  refine Finset.measurable_sup' _ ?_
  simpa [Finset.mem_range]

@[fun_prop]
/-
**Finset.measurable_range_sup''** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.measurable_range_sup'' {f : Nat -> δ -> α} {n : Nat} (hf : forall k
 <= n, Measurable (f k)) : Measurable fun x => (range (n + 1)).sup' nonempty_ran
ge_add_one fun k => f k x
参数：hf : forall k <= n, Measurable (f k)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.nonempty_range_add_one`：nonempty_range_add_one : (range <| n + 1)
.Nonempty
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup'_apply`：∀ {α : Type u_2} {β : Type u_3} {C : β → Type u_7} [i
nst : (b : β) → SemilatticeSup (C b)] {s : Finset α}   (H : s.Nonempty) (f : α →
 (b : β…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.measurable_range_sup'`：Finset.measurable_range_sup' {f : Nat -> δ
 -> α} {n : Nat} (hf : forall k <= n, Measurable (f k)) : Measurable ((range (n 
+ 1)).sup' nonempt…
-/
theorem Finset.measurable_range_sup'' {f : ℕ → δ → α} {n : ℕ} (hf : ∀ k ≤ n, Measurable (f k)) :
    Measurable fun x => (range (n + 1)).sup' nonempty_range_add_one fun k => f k x := by
  convert! Finset.measurable_range_sup' hf using 1
  ext x
  simp

end SemilatticeSup

