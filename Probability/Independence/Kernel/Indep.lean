/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Basic
public import Mathlib.Tactic.Peel
public import Mathlib.Analysis.Normed.Group.Basic

/-!
# Independence of families of sets with respect to a kernel and a measure

A family of sets of sets `π : ι → Set (Set Ω)` is independent with respect to a kernel
`κ : Kernel α Ω` and a measure `μ` on `α` if for any finite set of indices `s = {i_1, ..., i_n}`,
for any sets `f i_1 ∈ π i_1, ..., f i_n ∈ π i_n`, then for `μ`-almost every `a : α`,
`κ a (⋂ i in s, f i) = ∏ i ∈ s, κ a (f i)`.

This notion of independence is a generalization of both independence and conditional independence.
For conditional independence, `κ` is the conditional kernel `ProbabilityTheory.condExpKernel` and
`μ` is the ambient measure. For (non-conditional) independence, `κ = Kernel.const Unit μ` and the
measure is the Dirac measure on `Unit`.

The main purpose of this file is to prove only once the properties that hold for both conditional
and non-conditional independence.

This file contains results about independence of families of sets and `σ`-algebras.
See the `IndepFun` file for results about independence of random variables.

## Main definitions

* `ProbabilityTheory.Kernel.iIndepSets`: independence of a family of sets of sets.
  Variant for two sets of sets: `ProbabilityTheory.Kernel.IndepSets`.
* `ProbabilityTheory.Kernel.iIndep`: independence of a family of σ-algebras. Variant for two
  σ-algebras: `Indep`.
* `ProbabilityTheory.Kernel.iIndepSet`: independence of a family of sets. Variant for two sets:
  `ProbabilityTheory.Kernel.IndepSet`.

See the file `Mathlib/Probability/Kernel/Basic.lean` for a more detailed discussion of these
definitions in the particular case of the usual independence notion.

## Main statements

* `ProbabilityTheory.Kernel.iIndepSets.iIndep`: if π-systems are independent as sets of sets,
  then the measurable space structures they generate are independent.
* `ProbabilityTheory.Kernel.IndepSets.Indep`: variant with two π-systems.
-/

@[expose] public section

open Set MeasureTheory MeasurableSpace

open scoped MeasureTheory ENNReal

namespace ProbabilityTheory.Kernel

variable {α Ω ι : Type*}

section Definitions

variable {_mα : MeasurableSpace α}

/-- A family of sets of sets `π : ι → Set (Set Ω)` is independent with respect to a kernel `κ` and
a measure `μ` if for any finite set of indices `s = {i_1, ..., i_n}`, for any sets
`f i_1 ∈ π i_1, ..., f i_n ∈ π i_n`, then `∀ᵐ a ∂μ, κ a (⋂ i in s, f i) = ∏ i ∈ s, κ a (f i)`.
It will be used for families of π-systems. -/
/-
**ProbabilityTheory.Kernel.iIndepSets** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheo
ry.Kernel`。
形式化陈述：iIndepSets {_mΩ : MeasurableSpace Ω} (π : ι -> Set (Set Ω)) (κ : Kernel α 
Ω) (μ : Measure α
参数：π : ι -> Set (Set Ω)；κ : Kernel α Ω。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α

--- 原说明 ---
A family of sets of sets `π : ι → Set (Set Ω)` is independent with respect to a 
kernel `κ` and
a measure `μ` if for any finite set of indices `s = {i_1, ..., i_n}`, for any se
ts
`f i_1 ∈ π i_1, ..., f i_n ∈ π i_n`, then `∀ᵐ a ∂μ, κ a (⋂ i in s, f i) = ∏ i ∈ 
s, κ a (f i)`.
It will be used for families of π-systems.
-/
def iIndepSets {_mΩ : MeasurableSpace Ω}
    (π : ι → Set (Set Ω)) (κ : Kernel α Ω) (μ : Measure α := by volume_tac) : Prop :=
  ∀ (s : Finset ι) {f : ι → Set Ω} (_H : ∀ i, i ∈ s → f i ∈ π i),
  ∀ᵐ a ∂μ, κ a (⋂ i ∈ s, f i) = ∏ i ∈ s, κ a (f i)

/-- Two sets of sets `s₁, s₂` are independent with respect to a kernel `κ` and a measure `μ` if for
any sets `t₁ ∈ s₁, t₂ ∈ s₂`, then `∀ᵐ a ∂μ, κ a (t₁ ∩ t₂) = κ a (t₁) * κ a (t₂)` -/
/-
**ProbabilityTheory.Kernel.IndepSets** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheor
y.Kernel`。
形式化陈述：IndepSets {_mΩ : MeasurableSpace Ω} (s1 s2 : Set (Set Ω)) (κ : Kernel α Ω)
 (μ : Measure α
参数：s1 s2 : Set (Set Ω)；κ : Kernel α Ω。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α

--- 原说明 ---
Two sets of sets `s₁, s₂` are independent with respect to a kernel `κ` and a mea
sure `μ` if for
any sets `t₁ ∈ s₁, t₂ ∈ s₂`, then `∀ᵐ a ∂μ, κ a (t₁ ∩ t₂) = κ a (t₁) * κ a (t₂)`
-/
def IndepSets {_mΩ : MeasurableSpace Ω}
    (s1 s2 : Set (Set Ω)) (κ : Kernel α Ω) (μ : Measure α := by volume_tac) : Prop :=
  ∀ t1 t2 : Set Ω, t1 ∈ s1 → t2 ∈ s2 → (∀ᵐ a ∂μ, κ a (t1 ∩ t2) = κ a t1 * κ a t2)

/-- A family of measurable space structures (i.e. of σ-algebras) is independent with respect to a
kernel `κ` and a measure `μ` if the family of sets of measurable sets they define is independent. -/
/-
**ProbabilityTheory.Kernel.iIndep** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory.K
ernel`。
形式化陈述：iIndep (m : ι -> MeasurableSpace Ω) {_mΩ : MeasurableSpace Ω} (κ : Kernel 
α Ω) (μ : Measure α
参数：m : ι -> MeasurableSpace Ω；κ : Kernel α Ω。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family of measurable space structures (i.e. of σ-algebras) is independent with
 respect to a
kernel `κ` and a measure `μ` if the family of sets of measurable sets they defin
e is independent.
-/
def iIndep (m : ι → MeasurableSpace Ω) {_mΩ : MeasurableSpace Ω} (κ : Kernel α Ω)
    (μ : Measure α := by volume_tac) : Prop :=
  iIndepSets (fun x ↦ {s | MeasurableSet[m x] s}) κ μ

/-- Two measurable space structures (or σ-algebras) `m₁, m₂` are independent with respect to a
kernel `κ` and a measure `μ` if for any sets `t₁ ∈ m₁, t₂ ∈ m₂`,
`∀ᵐ a ∂μ, κ a (t₁ ∩ t₂) = κ a (t₁) * κ a (t₂)` -/
/-
**ProbabilityTheory.Kernel.Indep** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory.Ke
rnel`。
形式化陈述：Indep (m₁ m₂ : MeasurableSpace Ω) {_mΩ : MeasurableSpace Ω} (κ : Kernel α 
Ω) (μ : Measure α
参数：m₁ m₂ : MeasurableSpace Ω；κ : Kernel α Ω。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two measurable space structures (or σ-algebras) `m₁, m₂` are independent with re
spect to a
kernel `κ` and a measure `μ` if for any sets `t₁ ∈ m₁, t₂ ∈ m₂`,
`∀ᵐ a ∂μ, κ a (t₁ ∩ t₂) = κ a (t₁) * κ a (t₂)`
-/
def Indep (m₁ m₂ : MeasurableSpace Ω) {_mΩ : MeasurableSpace Ω} (κ : Kernel α Ω)
    (μ : Measure α := by volume_tac) : Prop :=
  IndepSets {s | MeasurableSet[m₁] s} {s | MeasurableSet[m₂] s} κ μ

/-- A family of sets is independent if the family of measurable space structures they generate is
independent. For a set `s`, the generated measurable space has measurable sets `∅, s, sᶜ, univ`. -/
/-
**ProbabilityTheory.Kernel.iIndepSet** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheor
y.Kernel`。
形式化陈述：iIndepSet {_mΩ : MeasurableSpace Ω} (s : ι -> Set Ω) (κ : Kernel α Ω) (μ :
 Measure α
参数：s : ι -> Set Ω；κ : Kernel α Ω。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family of sets is independent if the family of measurable space structures the
y generate is
independent. For a set `s`, the generated measurable space has measurable sets `
∅, s, sᶜ, univ`.
-/
def iIndepSet {_mΩ : MeasurableSpace Ω} (s : ι → Set Ω) (κ : Kernel α Ω)
    (μ : Measure α := by volume_tac) : Prop :=
  iIndep (m := fun i ↦ generateFrom {s i}) κ μ

/-- Two sets are independent if the two measurable space structures they generate are independent.
For a set `s`, the generated measurable space structure has measurable sets `∅, s, sᶜ, univ`. -/
/-
**ProbabilityTheory.Kernel.IndepSet** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory
.Kernel`。
形式化陈述：IndepSet {_mΩ : MeasurableSpace Ω} (s t : Set Ω) (κ : Kernel α Ω) (μ : Mea
sure α
参数：s t : Set Ω；κ : Kernel α Ω。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two sets are independent if the two measurable space structures they generate ar
e independent.
For a set `s`, the generated measurable space structure has measurable sets `∅, 
s, sᶜ, univ`.
-/
def IndepSet {_mΩ : MeasurableSpace Ω} (s t : Set Ω) (κ : Kernel α Ω)
    (μ : Measure α := by volume_tac) : Prop :=
  Indep (generateFrom {s}) (generateFrom {t}) κ μ

end Definitions

section ByDefinition

variable {β : ι → Type*} {mβ : ∀ i, MeasurableSpace (β i)}
  {_mα : MeasurableSpace α} {m : ι → MeasurableSpace Ω} {_mΩ : MeasurableSpace Ω}
  {κ η : Kernel α Ω} {μ : Measure α}
  {π : ι → Set (Set Ω)} {s : ι → Set Ω} {S : Finset ι} {f : ∀ x : ι, Ω → β x}
  {s1 s2 : Set (Set Ω)} {ι' : Type*} {g : ι' → ι}

/-
**ProbabilityTheory.Kernel.iIndepSets_zero_right** 是 Mathlib 中的一个定理，位于命名空间 `Prob
abilityTheory.Kernel`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {
_mΩ : MeasurableSpace Ω}   {κ : ProbabilityTheory.Kernel α Ω} {π : ι → Set (Set 
Ω)}, ProbabilityTheory.Kernel.iIndepSets π κ 0
参数：Set Ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ae_zero`：ae_zero {_m0 : MeasurableSpace α} : ae (0 : Measu
re α) = ⊥
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] lemma iIndepSets_zero_right : iIndepSets π κ 0 := by simp [iIndepSets]
/-
**ProbabilityTheory.Kernel.indepSets_zero_right** 是 Mathlib 中的一个定理，位于命名空间 `Proba
bilityTheory.Kernel`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {_mα : MeasurableSpace α} {_mΩ : Measurabl
eSpace Ω} {κ : ProbabilityTheory.Kernel α Ω}   {s1 s2 : Set (Set Ω)}, Probabilit
yTheory.Kernel.IndepSets s1 s2 κ 0
参数：Set Ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ae_zero`：ae_zero {_m0 : MeasurableSpace α} : ae (0 : Measu
re α) = ⊥
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] lemma indepSets_zero_right : IndepSets s1 s2 κ 0 := by simp [IndepSets]
/-
**ProbabilityTheory.Kernel.indepSets_zero_left** 是 Mathlib 中的一个定理，位于命名空间 `Probab
ilityTheory.Kernel`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {_mα : MeasurableSpace α} {_mΩ : Measurabl
eSpace Ω} {μ : MeasureTheory.Measure α}   {s1 s2 : Set (Set Ω)}, ProbabilityTheo
ry.Kernel.IndepSets s1 s2 0 μ
参数：Set Ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ProbabilityTheory.Kernel.instIsZeroApplyMeasure`：∀ {α : Type u_1} {β : T
ype u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β},   IsZeroApply (Proba
bilityTheory.Kernel α β) α (MeasureTh…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] lemma indepSets_zero_left : IndepSets s1 s2 (0 : Kernel α Ω) μ := by simp [IndepSets]
/-
**ProbabilityTheory.Kernel.iIndep_zero_right** 是 Mathlib 中的一个定理，位于命名空间 `Probabil
ityTheory.Kernel`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {
m : ι → MeasurableSpace Ω}   {_mΩ : MeasurableSpace Ω} {κ : ProbabilityTheory.Ke
rnel α Ω}, ProbabilityTheory.Kernel.iIndep m κ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
@[simp] lemma iIndep_zero_right : iIndep m κ 0 := by simp [iIndep]
/-
**ProbabilityTheory.Kernel.indep_zero_right** 是 Mathlib 中的一个定理，位于命名空间 `Probabili
tyTheory.Kernel`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {_mα : MeasurableSpace α} {m₁ m₂ _mΩ : Mea
surableSpace Ω}   {κ : ProbabilityTheory.Kernel α Ω}, ProbabilityTheory.Kernel.I
ndep m₁ m₂ κ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
@[simp] lemma indep_zero_right {m₁ m₂ : MeasurableSpace Ω} {_mΩ : MeasurableSpace Ω}
    {κ : Kernel α Ω} : Indep m₁ m₂ κ 0 := by simp [Indep]
/-
**ProbabilityTheory.Kernel.indep_zero_left** 是 Mathlib 中的一个定理，位于命名空间 `Probabilit
yTheory.Kernel`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {_mα : MeasurableSpace α} {μ : MeasureTheo
ry.Measure α} {m₁ m₂ _mΩ : MeasurableSpace Ω},   ProbabilityTheory.Kernel.Indep 
m₁ m₂ 0 μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
@[simp] lemma indep_zero_left {m₁ m₂ : MeasurableSpace Ω} {_mΩ : MeasurableSpace Ω} :
    Indep m₁ m₂ (0 : Kernel α Ω) μ := by simp [Indep]
/-
**ProbabilityTheory.Kernel.iIndepSet_zero_right** 是 Mathlib 中的一个定理，位于命名空间 `Proba
bilityTheory.Kernel`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {
_mΩ : MeasurableSpace Ω}   {κ : ProbabilityTheory.Kernel α Ω} {s : ι → Set Ω}, P
robabilityTheory.Kernel.iIndepSet s κ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasurableSpace.generateFrom_singleton`：∀ {α : Type u_1} (s : Set α), Me
asurableSpace.generateFrom {s} = MeasurableSpace.comap (fun x => x ∈ s) ⊤
-/
@[simp] lemma iIndepSet_zero_right : iIndepSet s κ 0 := by simp [iIndepSet]
/-
**ProbabilityTheory.Kernel.indepSet_zero_right** 是 Mathlib 中的一个定理，位于命名空间 `Probab
ilityTheory.Kernel`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {_mα : MeasurableSpace α} {_mΩ : Measurabl
eSpace Ω} {κ : ProbabilityTheory.Kernel α Ω}   {s t : Set Ω}, ProbabilityTheory.
Kernel.IndepSet s t κ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasurableSpace.generateFrom_singleton`：∀ {α : Type u_1} (s : Set α), Me
asurableSpace.generateFrom {s} = MeasurableSpace.comap (fun x => x ∈ s) ⊤
-/
@[simp] lemma indepSet_zero_right {s t : Set Ω} : IndepSet s t κ 0 := by simp [IndepSet]
/-
**ProbabilityTheory.Kernel.indepSet_zero_left** 是 Mathlib 中的一个定理，位于命名空间 `Probabi
lityTheory.Kernel`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {_mα : MeasurableSpace α} {_mΩ : Measurabl
eSpace Ω} {μ : MeasureTheory.Measure α}   {s t : Set Ω}, ProbabilityTheory.Kerne
l.IndepSet s t 0 μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasurableSpace.generateFrom_singleton`：∀ {α : Type u_1} (s : Set α), Me
asurableSpace.generateFrom {s} = MeasurableSpace.comap (fun x => x ∈ s) ⊤
-/
@[simp] lemma indepSet_zero_left {s t : Set Ω} : IndepSet s t (0 : Kernel α Ω) μ := by
  simp [IndepSet]
/-
**ProbabilityTheory.Kernel.iIndepSets_congr** 是 Mathlib 中的一个引理，位于命名空间 `Probabili
tyTheory.Kernel`。
形式化陈述：iIndepSets_congr (h : κ =ᵐ[μ] η) : iIndepSets π κ μ ↔ iIndepSets π η μ
参数：h : κ =ᵐ[μ] η。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
-/
lemma iIndepSets_congr (h : κ =ᵐ[μ] η) : iIndepSets π κ μ ↔ iIndepSets π η μ := by
  peel 3
  refine ⟨fun h' ↦ ?_, fun h' ↦ ?_⟩ <;>
  · filter_upwards [h, h'] with a ha h'a
    simpa [ha] using h'a

alias ⟨iIndepSets.congr, _⟩ := iIndepSets_congr
/-
**ProbabilityTheory.Kernel.indepSets_congr** 是 Mathlib 中的一个引理，位于命名空间 `Probabilit
yTheory.Kernel`。
形式化陈述：indepSets_congr (h : κ =ᵐ[μ] η) : IndepSets s1 s2 κ μ ↔ IndepSets s1 s2 η 
μ
参数：h : κ =ᵐ[μ] η。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
lemma indepSets_congr (h : κ =ᵐ[μ] η) : IndepSets s1 s2 κ μ ↔ IndepSets s1 s2 η μ := by
  peel 4
  refine ⟨fun h' ↦ ?_, fun h' ↦ ?_⟩ <;>
  · filter_upwards [h, h'] with a ha h'a
    simpa [ha] using h'a

alias ⟨IndepSets.congr, _⟩ := indepSets_congr
/-
**ProbabilityTheory.Kernel.iIndep_congr** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTh
eory.Kernel`。
形式化陈述：iIndep_congr (h : κ =ᵐ[μ] η) : iIndep m κ μ ↔ iIndep m η μ
参数：h : κ =ᵐ[μ] η。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `ProbabilityTheory.Kernel.iIndepSets_congr`：iIndepSets_congr (h : κ =ᵐ[μ]
 η) : iIndepSets π κ μ ↔ iIndepSets π η μ
-/
lemma iIndep_congr (h : κ =ᵐ[μ] η) : iIndep m κ μ ↔ iIndep m η μ :=
  iIndepSets_congr h

alias ⟨iIndep.congr, _⟩ := iIndep_congr
/-
**ProbabilityTheory.Kernel.indep_congr** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityThe
ory.Kernel`。
形式化陈述：indep_congr {m₁ m₂ : MeasurableSpace Ω} {_mΩ : MeasurableSpace Ω} {κ η : K
ernel α Ω} (h : κ =ᵐ[μ] η) : Indep m₁ m₂ κ μ ↔ Indep m₁ m₂ η μ
参数：h : κ =ᵐ[μ] η。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `ProbabilityTheory.Kernel.indepSets_congr`：indepSets_congr (h : κ =ᵐ[μ] η
) : IndepSets s1 s2 κ μ ↔ IndepSets s1 s2 η μ
-/
lemma indep_congr {m₁ m₂ : MeasurableSpace Ω} {_mΩ : MeasurableSpace Ω}
    {κ η : Kernel α Ω} (h : κ =ᵐ[μ] η) : Indep m₁ m₂ κ μ ↔ Indep m₁ m₂ η μ :=
  indepSets_congr h

alias ⟨Indep.congr, _⟩ := indep_congr
/-
**ProbabilityTheory.Kernel.iIndepSet_congr** 是 Mathlib 中的一个引理，位于命名空间 `Probabilit
yTheory.Kernel`。
形式化陈述：iIndepSet_congr (h : κ =ᵐ[μ] η) : iIndepSet s κ μ ↔ iIndepSet s η μ
参数：h : κ =ᵐ[μ] η。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `ProbabilityTheory.Kernel.iIndep_congr`：iIndep_congr (h : κ =ᵐ[μ] η) : iI
ndep m κ μ ↔ iIndep m η μ
-/
lemma iIndepSet_congr (h : κ =ᵐ[μ] η) : iIndepSet s κ μ ↔ iIndepSet s η μ :=
  iIndep_congr h

alias ⟨iIndepSet.congr, _⟩ := iIndepSet_congr
/-
**ProbabilityTheory.Kernel.indepSet_congr** 是 Mathlib 中的一个引理，位于命名空间 `Probability
Theory.Kernel`。
形式化陈述：indepSet_congr {s t : Set Ω} (h : κ =ᵐ[μ] η) : IndepSet s t κ μ ↔ IndepSet
 s t η μ
参数：h : κ =ᵐ[μ] η。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `ProbabilityTheory.Kernel.indep_congr`：indep_congr {m₁ m₂ : MeasurableSpa
ce Ω} {_mΩ : MeasurableSpace Ω} {κ η : Kernel α Ω} (h : κ =ᵐ[μ] η) : Indep m₁ m₂
 κ μ ↔ Indep m₁ m₂ η μ
-/
lemma indepSet_congr {s t : Set Ω} (h : κ =ᵐ[μ] η) : IndepSet s t κ μ ↔ IndepSet s t η μ :=
  indep_congr h

alias ⟨indepSet.congr, _⟩ := indepSet_congr
/-
**ProbabilityTheory.Kernel.iIndepSets.meas_biInter** 是 Mathlib 中的一个定理，位于命名空间 `Pr
obabilityTheory.Kernel.iIndepSets`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {
_mΩ : MeasurableSpace Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ : MeasureTheory
.Measure α} {π : ι → Set (Set Ω)},   ProbabilityTheory.Kernel.iIndepSets π κ μ →
     ∀ (s : Finset ι) {f : ι → Set Ω}, (∀ i ∈ s, f i ∈ π i) → ∀ᵐ (a : α) ∂μ, (κ 
a) (⋂ i ∈ s, f i) = ∏ i ∈ s, (κ a) (f i)
参数：Set Ω；s : Finset ι；∀ i ∈ s, f i ∈ π i；a : α；κ a；⋂ i ∈ s, f i；κ a；f i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma iIndepSets.meas_biInter (h : iIndepSets π κ μ) (s : Finset ι)
    {f : ι → Set Ω} (hf : ∀ i, i ∈ s → f i ∈ π i) :
    ∀ᵐ a ∂μ, κ a (⋂ i ∈ s, f i) = ∏ i ∈ s, κ a (f i) := h s hf
/-
**ProbabilityTheory.Kernel.iIndepSets.ae_isProbabilityMeasure** 是 Mathlib 中的一个定理
，位于命名空间 `ProbabilityTheory.Kernel.iIndepSets`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {
_mΩ : MeasurableSpace Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ : MeasureTheory
.Measure α} {π : ι → Set (Set Ω)},   ProbabilityTheory.Kernel.iIndepSets π κ μ →
 ∀ᵐ (a : α) ∂μ, MeasureTheory.IsProbabilityMeasure (κ a)
参数：Set Ω；a : α；κ a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.Kernel.iIndepSets.meas_biInter`：∀ {α : Type u_1} {Ω : 
Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {_mΩ : MeasurableSpace Ω}   {
κ : ProbabilityTheory.Kernel α Ω} {μ :…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iInter_of_empty`：iInter_of_empty [IsEmpty ι] (s : ι -> Set α) : ⋂ i,
 s i = univ
· 使用定理 `Set.iInter_univ`：iInter_univ : (⋂ _ : ι, univ : Set α) = univ
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
-/
lemma iIndepSets.ae_isProbabilityMeasure (h : iIndepSets π κ μ) :
    ∀ᵐ a ∂μ, IsProbabilityMeasure (κ a) := by
  filter_upwards [h.meas_biInter ∅ (f := fun _ ↦ Set.univ) (by simp)] with a ha
  exact ⟨by simpa using ha⟩
/-
**ProbabilityTheory.Kernel.iIndepSets.meas_iInter** 是 Mathlib 中的一个定理，位于命名空间 `Pro
babilityTheory.Kernel.iIndepSets`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {
_mΩ : MeasurableSpace Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ : MeasureTheory
.Measure α} {π : ι → Set (Set Ω)} {s : ι → Set Ω}   [inst : Fintype ι],   Probab
ilityTheory.Kernel.iIndepSets π κ μ →     (∀ (i : ι), s i ∈ π i) → ∀ᵐ (a : α) ∂μ
, (κ a) (⋂ i, s i) = ∏ i, (κ a) (s i)
参数：Set Ω；∀ (i : ι), s i ∈ π i；a : α；κ a；⋂ i, s i；κ a；s i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.Kernel.iIndepSets.meas_biInter`：∀ {α : Type u_1} {Ω : 
Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {_mΩ : MeasurableSpace Ω}   {
κ : ProbabilityTheory.Kernel α Ω} {μ :…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iInter_true`：iInter_true {s : True -> Set α} : iInter s = s trivial
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma iIndepSets.meas_iInter [Fintype ι] (h : iIndepSets π κ μ) (hs : ∀ i, s i ∈ π i) :
    ∀ᵐ a ∂μ, κ a (⋂ i, s i) = ∏ i, κ a (s i) := by
  filter_upwards [h.meas_biInter Finset.univ (fun _i _ ↦ hs _)] with a ha using by simp [← ha]
/-
**ProbabilityTheory.Kernel.iIndep.iIndepSets'** 是 Mathlib 中的一个定理，位于命名空间 `Probabi
lityTheory.Kernel.iIndep`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {
m : ι → MeasurableSpace Ω}   {_mΩ : MeasurableSpace Ω} {κ : ProbabilityTheory.Ke
rnel α Ω} {μ : MeasureTheory.Measure α},   ProbabilityTheory.Kernel.iIndep m κ μ
 → ProbabilityTheory.Kernel.iIndepSets (fun x => {s | MeasurableSet s}) κ μ
参数：fun x => {s | MeasurableSet s}。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma iIndep.iIndepSets' (hμ : iIndep m κ μ) :
    iIndepSets (fun x ↦ {s | MeasurableSet[m x] s}) κ μ := hμ
/-
**ProbabilityTheory.Kernel.iIndep.ae_isProbabilityMeasure** 是 Mathlib 中的一个定理，位于命
名空间 `ProbabilityTheory.Kernel.iIndep`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {
m : ι → MeasurableSpace Ω}   {_mΩ : MeasurableSpace Ω} {κ : ProbabilityTheory.Ke
rnel α Ω} {μ : MeasureTheory.Measure α},   ProbabilityTheory.Kernel.iIndep m κ μ
 → ∀ᵐ (a : α) ∂μ, MeasureTheory.IsProbabilityMeasure (κ a)
参数：a : α；κ a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepSets.ae_isProbabilityMeasure`：∀ {α : Type
 u_1} {Ω : Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {_mΩ : MeasurableS
pace Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ :…
· 使用定理 `ProbabilityTheory.Kernel.iIndep.iIndepSets'`：∀ {α : Type u_1} {Ω : Type 
u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {m : ι → MeasurableSpace Ω}   {_mΩ
 : MeasurableSpace Ω} {κ : Probab…
-/
lemma iIndep.ae_isProbabilityMeasure (h : iIndep m κ μ) :
    ∀ᵐ a ∂μ, IsProbabilityMeasure (κ a) :=
  h.iIndepSets'.ae_isProbabilityMeasure
/-
**ProbabilityTheory.Kernel.iIndep.meas_biInter** 是 Mathlib 中的一个定理，位于命名空间 `Probab
ilityTheory.Kernel.iIndep`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {
m : ι → MeasurableSpace Ω}   {_mΩ : MeasurableSpace Ω} {κ : ProbabilityTheory.Ke
rnel α Ω} {μ : MeasureTheory.Measure α} {s : ι → Set Ω}   {S : Finset ι},   Prob
abilityTheory.Kernel.iIndep m κ μ →     (∀ i ∈ S, MeasurableSet (s i)) → ∀ᵐ (a :
 α) ∂μ, (κ a) (⋂ i ∈ S, s i) = ∏ i ∈ S, (κ a) (s i)
参数：∀ i ∈ S, MeasurableSet (s i)；a : α；κ a；⋂ i ∈ S, s i；κ a；s i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma iIndep.meas_biInter (hμ : iIndep m κ μ) (hs : ∀ i, i ∈ S → MeasurableSet[m i] (s i)) :
    ∀ᵐ a ∂μ, κ a (⋂ i ∈ S, s i) = ∏ i ∈ S, κ a (s i) := hμ _ hs
/-
**ProbabilityTheory.Kernel.iIndep.meas_iInter** 是 Mathlib 中的一个定理，位于命名空间 `Probabi
lityTheory.Kernel.iIndep`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {
m : ι → MeasurableSpace Ω}   {_mΩ : MeasurableSpace Ω} {κ : ProbabilityTheory.Ke
rnel α Ω} {μ : MeasureTheory.Measure α} {s : ι → Set Ω}   [inst : Fintype ι],   
ProbabilityTheory.Kernel.iIndep m κ μ →     (∀ (i : ι), MeasurableSet (s i)) → ∀
ᵐ (a : α) ∂μ, (κ a) (⋂ i, s i) = ∏ i, (κ a) (s i)
参数：∀ (i : ι), MeasurableSet (s i)；a : α；κ a；⋂ i, s i；κ a；s i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.Kernel.iIndep.meas_biInter`：∀ {α : Type u_1} {Ω : Type
 u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {m : ι → MeasurableSpace Ω}   {_m
Ω : MeasurableSpace Ω} {κ : Probab…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iInter_true`：iInter_true {s : True -> Set α} : iInter s = s trivial
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma iIndep.meas_iInter [Fintype ι] (h : iIndep m κ μ) (hs : ∀ i, MeasurableSet[m i] (s i)) :
    ∀ᵐ a ∂μ, κ a (⋂ i, s i) = ∏ i, κ a (s i) := by
  filter_upwards [h.meas_biInter (fun i (_ : i ∈ Finset.univ) ↦ hs _)] with a ha
  simp [← ha]

@[nontriviality, simp]
/-
**ProbabilityTheory.Kernel.iIndepSets.of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 
`ProbabilityTheory.Kernel.iIndepSets`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {
_mΩ : MeasurableSpace Ω}   {μ : MeasureTheory.Measure α} [Subsingleton ι] {m : ι
 → Set (Set Ω)} {κ : ProbabilityTheory.Kernel α Ω}   [ProbabilityTheory.IsMarkov
Kernel κ], ProbabilityTheory.Kernel.iIndepSets m κ μ
参数：Set Ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.Subsingleton.eq_empty_or_singleton`：∀ {α : Type u} {s : Set α}, s.Su
bsingleton → s = ∅ ∨ ∃ x, s = {x}
· 使用定理 `Set.subsingleton_of_subsingleton`：subsingleton_of_subsingleton [Subsingl
eton α] {s : Set α} : s.Subsingleton
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iInter_of_empty`：iInter_of_empty [IsEmpty ι] (s : ι -> Set α) : ⋂ i,
 s i = univ
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `Set.iInter_univ`：iInter_univ : (⋂ _ : ι, univ : Set α) = univ
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `ProbabilityTheory.IsMarkovKernel.is_probability_measure'`：∀ {α : Type u_
1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabi
lityTheory.Kernel α β}   [ProbabilityTheory.Is…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.iInter_iInter_eq_left`：iInter_iInter_eq_left {b : β} {s : forall x :
 β, x = b -> Set α} : ⋂ (x) (h : x = b), s x h = s b rfl
· 使用定理 `Finset.prod_singleton`：prod_singleton (f : ι -> M) (a : ι) : ∏ x in sing
leton a, f x = f a
-/
lemma iIndepSets.of_subsingleton [Subsingleton ι] {m : ι → Set (Set Ω)} {κ : Kernel α Ω}
    [IsMarkovKernel κ] : iIndepSets m κ μ := by
  rintro s f hf
  obtain rfl | ⟨i, rfl⟩ : s = ∅ ∨ ∃ i, s = {i} := by
    simpa using (subsingleton_of_subsingleton (s := (s : Set ι))).eq_empty_or_singleton
  all_goals simp

@[nontriviality, simp]
/-
**ProbabilityTheory.Kernel.iIndep.of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Pro
babilityTheory.Kernel.iIndep`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {
_mΩ : MeasurableSpace Ω}   {μ : MeasureTheory.Measure α} [Subsingleton ι] {m : ι
 → MeasurableSpace Ω} {κ : ProbabilityTheory.Kernel α Ω}   [ProbabilityTheory.Is
MarkovKernel κ], ProbabilityTheory.Kernel.iIndep m κ μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma iIndep.of_subsingleton [Subsingleton ι] {m : ι → MeasurableSpace Ω} {κ : Kernel α Ω}
    [IsMarkovKernel κ] : iIndep m κ μ := by simp [iIndep]
/-
**ProbabilityTheory.Kernel.iIndepSets.precomp** 是 Mathlib 中的一个定理，位于命名空间 `Probabi
lityTheory.Kernel.iIndepSets`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {
_mΩ : MeasurableSpace Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ : MeasureTheory
.Measure α} {π : ι → Set (Set Ω)} {ι' : Type u_5} {g : ι' → ι},   Function.Injec
tive g → ProbabilityTheory.Kernel.iIndepSets π κ μ → ProbabilityTheory.Kernel.iI
ndepSets (π ∘ g) κ μ
参数：Set Ω；π ∘ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.extend_apply`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} {f : α → β},   Function.Injective f → ∀ (g : α → γ) (e' : β → γ) (a : α)
, Function.extend f g…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iInter_exists`：iInter_exists {p : ι -> Prop} {f : Exists p -> Set α}
 : ⋂ x, f x = ⋂ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `Set.biInter_and'`：biInter_and' (p : ι' -> Prop) (q : ι -> ι' -> Prop) (s
 : forall x y, p y ∧ q x y -> Set α) : ⋂ (x : ι) (y : ι') (h : p y ∧ q x y), s x
 y h =…
· 使用定理 `Set.iInter_iInter_eq_right`：iInter_iInter_eq_right {b : β} {s : forall x
 : β, b = x -> Set α} : ⋂ (x) (h : b = x), s x h = s b rfl
· 使用定理 `Finset.prod_image`：prod_image [DecidableEq ι] {s : Finset κ} {g : κ -> ι
} : Set.InjOn g s -> ∏ x in s.image g, f x = ∏ x in s, f (g x)
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
-/
lemma iIndepSets.precomp (hg : Function.Injective g) (h : iIndepSets π κ μ) :
    iIndepSets (π ∘ g) κ μ := by
  intro s f hf
  let f' := Function.extend g f fun _ => ∅
  have f'_apply x : f' (g x) = f x := hg.extend_apply ..
  classical
  have hf' : ∀ i ∈ s.image g, f' i ∈ π i := by
    simp_rw [Finset.forall_mem_image, f'_apply]
    exact hf
  filter_upwards [@h (s.image g) f' hf'] with a ha
  simpa [Finset.set_biInter_finset_image, Finset.prod_image hg.injOn, f'_apply] using ha
/-
**ProbabilityTheory.Kernel.iIndepSets.of_precomp** 是 Mathlib 中的一个定理，位于命名空间 `Prob
abilityTheory.Kernel.iIndepSets`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {
_mΩ : MeasurableSpace Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ : MeasureTheory
.Measure α} {π : ι → Set (Set Ω)} {ι' : Type u_5} {g : ι' → ι},   Function.Surje
ctive g → ProbabilityTheory.Kernel.iIndepSets (π ∘ g) κ μ → ProbabilityTheory.Ke
rnel.iIndepSets π κ μ
参数：Set Ω；π ∘ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.hasRightInverse`：∀ {α : Sort u} {β : Sort v} {f : α 
→ β}, Function.Surjective f → Function.HasRightInverse f
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.comp_assoc`：comp_assoc (f : φ -> δ) (g : β -> φ) (h : α -> β) :
 (f ∘ g) ∘ h = f ∘ g ∘ h
· 使用定理 `Function.RightInverse.comp_eq_id`：∀ {α : Sort u_1} {β : Sort u_2} {f : α
 → β} {g : β → α}, Function.RightInverse f g → g ∘ f = id
· 使用定理 `Function.comp_id`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β), f ∘ id = 
f
· 使用定理 `ProbabilityTheory.Kernel.iIndepSets.precomp`：∀ {α : Type u_1} {Ω : Type 
u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {_mΩ : MeasurableSpace Ω}   {κ : P
robabilityTheory.Kernel α Ω} {μ :…
· 使用定理 `Function.RightInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α 
→ β} {g : β → α}, Function.RightInverse f g → Function.Injective f
-/
lemma iIndepSets.of_precomp (hg : Function.Surjective g) (h : iIndepSets (π ∘ g) κ μ) :
    iIndepSets π κ μ := by
  obtain ⟨g', hg'⟩ := hg.hasRightInverse
  convert! h.precomp hg'.injective
  rw [Function.comp_assoc, hg'.comp_eq_id, Function.comp_id]
/-
**ProbabilityTheory.Kernel.iIndepSets_precomp_of_bijective** 是 Mathlib 中的一个引理，位于
命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：iIndepSets_precomp_of_bijective (hg : Function.Bijective g) : iIndepSets (
π ∘ g) κ μ ↔ iIndepSets π κ μ
参数：hg : Function.Bijective g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepSets.of_precomp`：∀ {α : Type u_1} {Ω : Ty
pe u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {_mΩ : MeasurableSpace Ω}   {κ 
: ProbabilityTheory.Kernel α Ω} {μ :…
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
· 使用定理 `ProbabilityTheory.Kernel.iIndepSets.precomp`：∀ {α : Type u_1} {Ω : Type 
u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {_mΩ : MeasurableSpace Ω}   {κ : P
robabilityTheory.Kernel α Ω} {μ :…
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
-/
lemma iIndepSets_precomp_of_bijective (hg : Function.Bijective g) :
    iIndepSets (π ∘ g) κ μ ↔ iIndepSets π κ μ :=
  ⟨.of_precomp hg.surjective, .precomp hg.injective⟩
/-
**ProbabilityTheory.Kernel.iIndep.precomp** 是 Mathlib 中的一个定理，位于命名空间 `Probability
Theory.Kernel.iIndep`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {
m : ι → MeasurableSpace Ω}   {_mΩ : MeasurableSpace Ω} {κ : ProbabilityTheory.Ke
rnel α Ω} {μ : MeasureTheory.Measure α} {ι' : Type u_5}   {g : ι' → ι},   Functi
on.Injective g → ProbabilityTheory.Kernel.iIndep m κ μ → ProbabilityTheory.Kerne
l.iIndep (m ∘ g) κ μ
参数：m ∘ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepSets.precomp`：∀ {α : Type u_1} {Ω : Type 
u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {_mΩ : MeasurableSpace Ω}   {κ : P
robabilityTheory.Kernel α Ω} {μ :…
-/
lemma iIndep.precomp (hg : Function.Injective g) (h : iIndep m κ μ) :
    iIndep (m ∘ g) κ μ :=
  (iIndepSets.precomp hg h :)
/-
**ProbabilityTheory.Kernel.iIndep.of_precomp** 是 Mathlib 中的一个定理，位于命名空间 `Probabil
ityTheory.Kernel.iIndep`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {
m : ι → MeasurableSpace Ω}   {_mΩ : MeasurableSpace Ω} {κ : ProbabilityTheory.Ke
rnel α Ω} {μ : MeasureTheory.Measure α} {ι' : Type u_5}   {g : ι' → ι},   Functi
on.Surjective g → ProbabilityTheory.Kernel.iIndep (m ∘ g) κ μ → ProbabilityTheor
y.Kernel.iIndep m κ μ
参数：m ∘ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepSets.of_precomp`：∀ {α : Type u_1} {Ω : Ty
pe u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {_mΩ : MeasurableSpace Ω}   {κ 
: ProbabilityTheory.Kernel α Ω} {μ :…
-/
lemma iIndep.of_precomp (hg : Function.Surjective g) (h : iIndep (m ∘ g) κ μ) :
    iIndep m κ μ :=
  iIndepSets.of_precomp hg h
/-
**ProbabilityTheory.Kernel.iIndep_precomp_of_bijective** 是 Mathlib 中的一个引理，位于命名空间
 `ProbabilityTheory.Kernel`。
形式化陈述：iIndep_precomp_of_bijective (hg : Function.Bijective g) : iIndep (m ∘ g) κ
 μ ↔ iIndep m κ μ
参数：hg : Function.Bijective g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndep.of_precomp`：∀ {α : Type u_1} {Ω : Type u
_2} {ι : Type u_3} {_mα : MeasurableSpace α} {m : ι → MeasurableSpace Ω}   {_mΩ 
: MeasurableSpace Ω} {κ : Probab…
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
· 使用定理 `ProbabilityTheory.Kernel.iIndep.precomp`：∀ {α : Type u_1} {Ω : Type u_2}
 {ι : Type u_3} {_mα : MeasurableSpace α} {m : ι → MeasurableSpace Ω}   {_mΩ : M
easurableSpace Ω} {κ : Probab…
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
-/
lemma iIndep_precomp_of_bijective (hg : Function.Bijective g) :
    iIndep (m ∘ g) κ μ ↔ iIndep m κ μ :=
  ⟨.of_precomp hg.surjective, .precomp hg.injective⟩
/-
**ProbabilityTheory.Kernel.iIndepSet.precomp** 是 Mathlib 中的一个定理，位于命名空间 `Probabil
ityTheory.Kernel.iIndepSet`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {
_mΩ : MeasurableSpace Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ : MeasureTheory
.Measure α} {s : ι → Set Ω} {ι' : Type u_5} {g : ι' → ι},   Function.Injective g
 → ProbabilityTheory.Kernel.iIndepSet s κ μ → ProbabilityTheory.Kernel.iIndepSet
 (s ∘ g) κ μ
参数：s ∘ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndep.precomp`：∀ {α : Type u_1} {Ω : Type u_2}
 {ι : Type u_3} {_mα : MeasurableSpace α} {m : ι → MeasurableSpace Ω}   {_mΩ : M
easurableSpace Ω} {κ : Probab…
-/
lemma iIndepSet.precomp (hg : Function.Injective g) (h : iIndepSet s κ μ) :
    iIndepSet (s ∘ g) κ μ :=
  iIndep.precomp hg h
/-
**ProbabilityTheory.Kernel.iIndepSet.of_precomp** 是 Mathlib 中的一个定理，位于命名空间 `Proba
bilityTheory.Kernel.iIndepSet`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {
_mΩ : MeasurableSpace Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ : MeasureTheory
.Measure α} {s : ι → Set Ω} {ι' : Type u_5} {g : ι' → ι},   Function.Surjective 
g → ProbabilityTheory.Kernel.iIndepSet (s ∘ g) κ μ → ProbabilityTheory.Kernel.iI
ndepSet s κ μ
参数：s ∘ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndep.of_precomp`：∀ {α : Type u_1} {Ω : Type u
_2} {ι : Type u_3} {_mα : MeasurableSpace α} {m : ι → MeasurableSpace Ω}   {_mΩ 
: MeasurableSpace Ω} {κ : Probab…
-/
lemma iIndepSet.of_precomp (hg : Function.Surjective g) (h : iIndepSet (s ∘ g) κ μ) :
    iIndepSet s κ μ :=
  iIndep.of_precomp hg h
/-
**ProbabilityTheory.Kernel.iIndepSet_precomp_of_bijective** 是 Mathlib 中的一个引理，位于命
名空间 `ProbabilityTheory.Kernel`。
形式化陈述：iIndepSet_precomp_of_bijective (hg : Function.Bijective g) : iIndepSet (s 
∘ g) κ μ ↔ iIndepSet s κ μ
参数：hg : Function.Bijective g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepSet.of_precomp`：∀ {α : Type u_1} {Ω : Typ
e u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {_mΩ : MeasurableSpace Ω}   {κ :
 ProbabilityTheory.Kernel α Ω} {μ :…
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
· 使用定理 `ProbabilityTheory.Kernel.iIndepSet.precomp`：∀ {α : Type u_1} {Ω : Type u
_2} {ι : Type u_3} {_mα : MeasurableSpace α} {_mΩ : MeasurableSpace Ω}   {κ : Pr
obabilityTheory.Kernel α Ω} {μ :…
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
-/
lemma iIndepSet_precomp_of_bijective (hg : Function.Bijective g) :
    iIndepSet (s ∘ g) κ μ ↔ iIndepSet s κ μ :=
  ⟨.of_precomp hg.surjective, .precomp hg.injective⟩

end ByDefinition

section Indep

variable {_mα : MeasurableSpace α}

@[symm]
/-
**ProbabilityTheory.Kernel.IndepSets.symm** 是 Mathlib 中的一个定理，位于命名空间 `Probability
Theory.Kernel.IndepSets`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {_mα : MeasurableSpace α} {_mΩ : Measurabl
eSpace Ω} {κ : ProbabilityTheory.Kernel α Ω}   {μ : MeasureTheory.Measure α} {s₁
 s₂ : Set (Set Ω)},   ProbabilityTheory.Kernel.IndepSets s₁ s₂ κ μ → Probability
Theory.Kernel.IndepSets s₂ s₁ κ μ
参数：Set Ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem IndepSets.symm {_mΩ : MeasurableSpace Ω} {κ : Kernel α Ω} {μ : Measure α}
    {s₁ s₂ : Set (Set Ω)} (h : IndepSets s₁ s₂ κ μ) :
    IndepSets s₂ s₁ κ μ := by
  intro t1 t2 ht1 ht2
  filter_upwards [h t2 t1 ht2 ht1] with a ha
  rwa [Set.inter_comm, mul_comm]

@[symm]
/-
**ProbabilityTheory.Kernel.Indep.symm** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheo
ry.Kernel.Indep`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {_mα : MeasurableSpace α} {m₁ m₂ _mΩ : Mea
surableSpace Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ : MeasureTheory.Measure 
α},   ProbabilityTheory.Kernel.Indep m₁ m₂ κ μ → ProbabilityTheory.Kernel.Indep 
m₂ m₁ κ μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IndepSets.symm`：∀ {α : Type u_1} {Ω : Type u_2}
 {_mα : MeasurableSpace α} {_mΩ : MeasurableSpace Ω} {κ : ProbabilityTheory.Kern
el α Ω}   {μ : MeasureTheory.…
-/
theorem Indep.symm {m₁ m₂ : MeasurableSpace Ω} {_mΩ : MeasurableSpace Ω} {κ : Kernel α Ω}
    {μ : Measure α} (h : Indep m₁ m₂ κ μ) :
    Indep m₂ m₁ κ μ :=
  IndepSets.symm h
/-
**ProbabilityTheory.Kernel.indep_bot_right** 是 Mathlib 中的一个定理，位于命名空间 `Probabilit
yTheory.Kernel`。
形式化陈述：indep_bot_right (m' : MeasurableSpace Ω) {_mΩ : MeasurableSpace Ω} {κ : Ke
rnel α Ω} {μ : Measure α} [IsZeroOrMarkovKernel κ] : Indep m' ⊥ κ μ
参数：m' : MeasurableSpace Ω。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.eq_zero_or_isMarkovKernel`：eq_zero_or_isMarkovKernel (
κ : Kernel α β) [h : IsZeroOrMarkovKernel κ] : κ = 0 ∨ IsMarkovKernel κ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ProbabilityTheory.Kernel.instIsZeroApplyMeasure`：∀ {α : Type u_1} {β : T
ype u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β},   IsZeroApply (Proba
bilityTheory.Kernel α β) α (MeasureTh…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasurableSpace.measurableSet_bot_iff`：measurableSet_bot_iff {s : Set α}
 : MeasurableSet[⊥] s ↔ s = ∅ ∨ s = univ
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用定理 `Set.inter_empty`：inter_empty (a : Set α) : a inter ∅ = ∅
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `ProbabilityTheory.IsMarkovKernel.is_probability_measure'`：∀ {α : Type u_
1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabi
lityTheory.Kernel α β}   [ProbabilityTheory.Is…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem indep_bot_right (m' : MeasurableSpace Ω) {_mΩ : MeasurableSpace Ω}
    {κ : Kernel α Ω} {μ : Measure α} [IsZeroOrMarkovKernel κ] :
    Indep m' ⊥ κ μ := by
  intro s t _ ht
  rw [Set.mem_ofPred_eq, MeasurableSpace.measurableSet_bot_iff] at ht
  rcases eq_zero_or_isMarkovKernel κ with rfl | h
  · simp
  refine Filter.Eventually.of_forall (fun a ↦ ?_)
  rcases ht with ht | ht
  · rw [ht, Set.inter_empty, measure_empty, mul_zero]
  · rw [ht, Set.inter_univ, measure_univ, mul_one]
/-
**ProbabilityTheory.Kernel.indep_bot_left** 是 Mathlib 中的一个定理，位于命名空间 `Probability
Theory.Kernel`。
形式化陈述：indep_bot_left (m' : MeasurableSpace Ω) {_mΩ : MeasurableSpace Ω} {κ : Ker
nel α Ω} {μ : Measure α} [IsZeroOrMarkovKernel κ] : Indep ⊥ m' κ μ
参数：m' : MeasurableSpace Ω。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.Indep.symm`：∀ {α : Type u_1} {Ω : Type u_2} {_m
α : MeasurableSpace α} {m₁ m₂ _mΩ : MeasurableSpace Ω}   {κ : ProbabilityTheory.
Kernel α Ω} {μ : MeasureT…
· 使用定理 `ProbabilityTheory.Kernel.indep_bot_right`：indep_bot_right (m' : Measurab
leSpace Ω) {_mΩ : MeasurableSpace Ω} {κ : Kernel α Ω} {μ : Measure α} [IsZeroOrM
arkovKernel κ] : Indep m' ⊥ κ …
-/
theorem indep_bot_left (m' : MeasurableSpace Ω) {_mΩ : MeasurableSpace Ω}
    {κ : Kernel α Ω} {μ : Measure α} [IsZeroOrMarkovKernel κ] :
    Indep ⊥ m' κ μ := (indep_bot_right m').symm
/-
**ProbabilityTheory.Kernel.indepSet_empty_right** 是 Mathlib 中的一个定理，位于命名空间 `Proba
bilityTheory.Kernel`。
形式化陈述：indepSet_empty_right {_mΩ : MeasurableSpace Ω} {κ : Kernel α Ω} {μ : Measu
re α} [IsZeroOrMarkovKernel κ] (s : Set Ω) : IndepSet s ∅ κ μ
参数：s : Set Ω。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasurableSpace.generateFrom_singleton_empty`：generateFrom_singleton_emp
ty : generateFrom {∅} = (⊥ : MeasurableSpace α)
· 使用定理 `ProbabilityTheory.Kernel.indep_bot_right`：indep_bot_right (m' : Measurab
leSpace Ω) {_mΩ : MeasurableSpace Ω} {κ : Kernel α Ω} {μ : Measure α} [IsZeroOrM
arkovKernel κ] : Indep m' ⊥ κ …
-/
theorem indepSet_empty_right {_mΩ : MeasurableSpace Ω}
    {κ : Kernel α Ω} {μ : Measure α} [IsZeroOrMarkovKernel κ] (s : Set Ω) :
    IndepSet s ∅ κ μ := by
  simp only [IndepSet, generateFrom_singleton_empty]
  exact indep_bot_right _
/-
**ProbabilityTheory.Kernel.indepSet_empty_left** 是 Mathlib 中的一个定理，位于命名空间 `Probab
ilityTheory.Kernel`。
形式化陈述：indepSet_empty_left {_mΩ : MeasurableSpace Ω} {κ : Kernel α Ω} {μ : Measur
e α} [IsZeroOrMarkovKernel κ] (s : Set Ω) : IndepSet ∅ s κ μ
参数：s : Set Ω。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.Indep.symm`：∀ {α : Type u_1} {Ω : Type u_2} {_m
α : MeasurableSpace α} {m₁ m₂ _mΩ : MeasurableSpace Ω}   {κ : ProbabilityTheory.
Kernel α Ω} {μ : MeasureT…
· 使用定理 `ProbabilityTheory.Kernel.indepSet_empty_right`：indepSet_empty_right {_mΩ
 : MeasurableSpace Ω} {κ : Kernel α Ω} {μ : Measure α} [IsZeroOrMarkovKernel κ] 
(s : Set Ω) : IndepSet s ∅ κ μ
-/
theorem indepSet_empty_left {_mΩ : MeasurableSpace Ω} {κ : Kernel α Ω}
    {μ : Measure α} [IsZeroOrMarkovKernel κ] (s : Set Ω) :
    IndepSet ∅ s κ μ :=
  (indepSet_empty_right s).symm
/-
**ProbabilityTheory.Kernel.indepSets_of_indepSets_of_le_left** 是 Mathlib 中的一个定理，
位于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：indepSets_of_indepSets_of_le_left {s₁ s₂ s₃ : Set (Set Ω)} {_mΩ : Measurab
leSpace Ω} {κ : Kernel α Ω} {μ : Measure α} (h_indep : IndepSets s₁ s₂ κ μ) (h31
 : s₃ subseteq s₁) : IndepSets s₃ s₂ κ μ
参数：Set Ω；h_indep : IndepSets s₁ s₂ κ μ；h31 : s₃ subseteq s₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_of_subset_of_mem`：∀ {α : Type u} {s₁ s₂ : Set α} {a : α}, s₁ ⊆ s
₂ → a ∈ s₁ → a ∈ s₂
-/
theorem indepSets_of_indepSets_of_le_left {s₁ s₂ s₃ : Set (Set Ω)} {_mΩ : MeasurableSpace Ω}
    {κ : Kernel α Ω} {μ : Measure α} (h_indep : IndepSets s₁ s₂ κ μ) (h31 : s₃ ⊆ s₁) :
    IndepSets s₃ s₂ κ μ :=
  fun t1 t2 ht1 ht2 => h_indep t1 t2 (Set.mem_of_subset_of_mem h31 ht1) ht2
/-
**ProbabilityTheory.Kernel.indepSets_of_indepSets_of_le_right** 是 Mathlib 中的一个定理
，位于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：indepSets_of_indepSets_of_le_right {s₁ s₂ s₃ : Set (Set Ω)} {_mΩ : Measura
bleSpace Ω} {κ : Kernel α Ω} {μ : Measure α} (h_indep : IndepSets s₁ s₂ κ μ) (h3
2 : s₃ subseteq s₂) : IndepSets s₁ s₃ κ μ
参数：Set Ω；h_indep : IndepSets s₁ s₂ κ μ；h32 : s₃ subseteq s₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_of_subset_of_mem`：∀ {α : Type u} {s₁ s₂ : Set α} {a : α}, s₁ ⊆ s
₂ → a ∈ s₁ → a ∈ s₂
-/
theorem indepSets_of_indepSets_of_le_right {s₁ s₂ s₃ : Set (Set Ω)} {_mΩ : MeasurableSpace Ω}
    {κ : Kernel α Ω} {μ : Measure α} (h_indep : IndepSets s₁ s₂ κ μ) (h32 : s₃ ⊆ s₂) :
    IndepSets s₁ s₃ κ μ :=
  fun t1 t2 ht1 ht2 => h_indep t1 t2 ht1 (Set.mem_of_subset_of_mem h32 ht2)
/-
**ProbabilityTheory.Kernel.indep_of_indep_of_le_left** 是 Mathlib 中的一个定理，位于命名空间 `
ProbabilityTheory.Kernel`。
形式化陈述：indep_of_indep_of_le_left {m₁ m₂ m₃ : MeasurableSpace Ω} {_mΩ : Measurable
Space Ω} {κ : Kernel α Ω} {μ : Measure α} (h_indep : Indep m₁ m₂ κ μ) (h31 : m₃ 
<= m₁) : Indep m₃ m₂ κ μ
参数：h_indep : Indep m₁ m₂ κ μ；h31 : m₃ <= m₁。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem indep_of_indep_of_le_left {m₁ m₂ m₃ : MeasurableSpace Ω} {_mΩ : MeasurableSpace Ω}
    {κ : Kernel α Ω} {μ : Measure α} (h_indep : Indep m₁ m₂ κ μ) (h31 : m₃ ≤ m₁) :
    Indep m₃ m₂ κ μ :=
  fun t1 t2 ht1 ht2 => h_indep t1 t2 (h31 _ ht1) ht2
/-
**ProbabilityTheory.Kernel.indep_of_indep_of_le_right** 是 Mathlib 中的一个定理，位于命名空间 
`ProbabilityTheory.Kernel`。
形式化陈述：indep_of_indep_of_le_right {m₁ m₂ m₃ : MeasurableSpace Ω} {_mΩ : Measurabl
eSpace Ω} {κ : Kernel α Ω} {μ : Measure α} (h_indep : Indep m₁ m₂ κ μ) (h32 : m₃
 <= m₂) : Indep m₁ m₃ κ μ
参数：h_indep : Indep m₁ m₂ κ μ；h32 : m₃ <= m₂。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem indep_of_indep_of_le_right {m₁ m₂ m₃ : MeasurableSpace Ω} {_mΩ : MeasurableSpace Ω}
    {κ : Kernel α Ω} {μ : Measure α} (h_indep : Indep m₁ m₂ κ μ) (h32 : m₃ ≤ m₂) :
    Indep m₁ m₃ κ μ :=
  fun t1 t2 ht1 ht2 => h_indep t1 t2 ht1 (h32 _ ht2)
/-
**ProbabilityTheory.Kernel.indep_of_indep_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Proba
bilityTheory.Kernel`。
形式化陈述：indep_of_indep_of_le {m₁ m₂ m₃ m₄ : MeasurableSpace Ω} {_mΩ : MeasurableSp
ace Ω} {κ : Kernel α Ω} {μ : Measure α} (h_indep : Indep m₁ m₂ κ μ) (h31 : m₃ <=
 m₁) (h42 : m₄ <= m₂) : Indep m₃ m₄ κ μ
参数：h_indep : Indep m₁ m₂ κ μ；h31 : m₃ <= m₁；h42 : m₄ <= m₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.indep_of_indep_of_le_left`：indep_of_indep_of_le
_left {m₁ m₂ m₃ : MeasurableSpace Ω} {_mΩ : MeasurableSpace Ω} {κ : Kernel α Ω} 
{μ : Measure α} (h_indep : Indep m₁ m₂ κ…
· 使用定理 `ProbabilityTheory.Kernel.indep_of_indep_of_le_right`：indep_of_indep_of_l
e_right {m₁ m₂ m₃ : MeasurableSpace Ω} {_mΩ : MeasurableSpace Ω} {κ : Kernel α Ω
} {μ : Measure α} (h_indep : Indep m₁ m₂ …
-/
theorem indep_of_indep_of_le {m₁ m₂ m₃ m₄ : MeasurableSpace Ω} {_mΩ : MeasurableSpace Ω}
    {κ : Kernel α Ω} {μ : Measure α} (h_indep : Indep m₁ m₂ κ μ)
    (h31 : m₃ ≤ m₁) (h42 : m₄ ≤ m₂) :
    Indep m₃ m₄ κ μ :=
  indep_of_indep_of_le_left (indep_of_indep_of_le_right h_indep h42) h31
/-
**ProbabilityTheory.Kernel.iIndep_of_iIndep_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Pro
babilityTheory.Kernel`。
形式化陈述：iIndep_of_iIndep_of_le {m₁ m₂ : ι -> MeasurableSpace Ω} {_mΩ : MeasurableS
pace Ω} {κ : Kernel α Ω} {μ : Measure α} (h_indep : iIndep m₂ κ μ) (h_le : foral
l i, m₁ i <= m₂ i) : iIndep m₁ κ μ
参数：h_indep : iIndep m₂ κ μ；h_le : forall i, m₁ i <= m₂ i。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iIndep_of_iIndep_of_le {m₁ m₂ : ι → MeasurableSpace Ω} {_mΩ : MeasurableSpace Ω}
    {κ : Kernel α Ω} {μ : Measure α} (h_indep : iIndep m₂ κ μ) (h_le : ∀ i, m₁ i ≤ m₂ i) :
    iIndep m₁ κ μ :=
  fun s t ht ↦ h_indep s fun i hi ↦ h_le i (t i) <| ht i hi
/-
**ProbabilityTheory.Kernel.IndepSets.union** 是 Mathlib 中的一个定理，位于命名空间 `Probabilit
yTheory.Kernel.IndepSets`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {_mα : MeasurableSpace α} {s₁ s₂ s' : Set 
(Set Ω)} {_mΩ : MeasurableSpace Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ : Mea
sureTheory.Measure α},   ProbabilityTheory.Kernel.IndepSets s₁ s' κ μ →     Prob
abilityTheory.Kernel.IndepSets s₂ s' κ μ → ProbabilityTheory.Kernel.IndepSets (s
₁ ∪ s₂) s' κ μ
参数：Set Ω；s₁ ∪ s₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_union`：mem_union (x : α) (a b : Set α) : x in a union b ↔ x in a
 ∨ x in b
-/
theorem IndepSets.union {s₁ s₂ s' : Set (Set Ω)} {_mΩ : MeasurableSpace Ω}
    {κ : Kernel α Ω} {μ : Measure α}
    (h₁ : IndepSets s₁ s' κ μ) (h₂ : IndepSets s₂ s' κ μ) :
    IndepSets (s₁ ∪ s₂) s' κ μ := by
  intro t1 t2 ht1 ht2
  rcases (Set.mem_union _ _ _).mp ht1 with ht1₁ | ht1₂
  · exact h₁ t1 t2 ht1₁ ht2
  · exact h₂ t1 t2 ht1₂ ht2

@[simp]
/-
**ProbabilityTheory.Kernel.IndepSets.union_iff** 是 Mathlib 中的一个定理，位于命名空间 `Probab
ilityTheory.Kernel.IndepSets`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {_mα : MeasurableSpace α} {s₁ s₂ s' : Set 
(Set Ω)} {_mΩ : MeasurableSpace Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ : Mea
sureTheory.Measure α},   ProbabilityTheory.Kernel.IndepSets (s₁ ∪ s₂) s' κ μ ↔  
   ProbabilityTheory.Kernel.IndepSets s₁ s' κ μ ∧ ProbabilityTheory.Kernel.Indep
Sets s₂ s' κ μ
参数：Set Ω；s₁ ∪ s₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.indepSets_of_indepSets_of_le_left`：indepSets_of
_indepSets_of_le_left {s₁ s₂ s₃ : Set (Set Ω)} {_mΩ : MeasurableSpace Ω} {κ : Ke
rnel α Ω} {μ : Measure α} (h_indep : IndepSets s…
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `ProbabilityTheory.Kernel.IndepSets.union`：∀ {α : Type u_1} {Ω : Type u_2
} {_mα : MeasurableSpace α} {s₁ s₂ s' : Set (Set Ω)} {_mΩ : MeasurableSpace Ω}  
 {κ : ProbabilityTheory.Kernel…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem IndepSets.union_iff {s₁ s₂ s' : Set (Set Ω)} {_mΩ : MeasurableSpace Ω}
    {κ : Kernel α Ω} {μ : Measure α} :
    IndepSets (s₁ ∪ s₂) s' κ μ ↔ IndepSets s₁ s' κ μ ∧ IndepSets s₂ s' κ μ :=
  ⟨fun h =>
    ⟨indepSets_of_indepSets_of_le_left h Set.subset_union_left,
      indepSets_of_indepSets_of_le_left h Set.subset_union_right⟩,
    fun h => IndepSets.union h.left h.right⟩
/-
**ProbabilityTheory.Kernel.IndepSets.iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Probabili
tyTheory.Kernel.IndepSets`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {
s : ι → Set (Set Ω)} {s' : Set (Set Ω)}   {_mΩ : MeasurableSpace Ω} {κ : Probabi
lityTheory.Kernel α Ω} {μ : MeasureTheory.Measure α},   (∀ (n : ι), ProbabilityT
heory.Kernel.IndepSets (s n) s' κ μ) → ProbabilityTheory.Kernel.IndepSets (⋃ n, 
s n) s' κ μ
参数：Set Ω；Set Ω；∀ (n : ι), ProbabilityTheory.Kernel.IndepSets (s n) s' κ μ；⋃ n, s
 n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
-/
theorem IndepSets.iUnion {s : ι → Set (Set Ω)} {s' : Set (Set Ω)} {_mΩ : MeasurableSpace Ω}
    {κ : Kernel α Ω} {μ : Measure α} (hyp : ∀ n, IndepSets (s n) s' κ μ) :
    IndepSets (⋃ n, s n) s' κ μ := by
  intro t1 t2 ht1 ht2
  rw [Set.mem_iUnion] at ht1
  obtain ⟨n, ht1⟩ := ht1
  exact hyp n t1 t2 ht1 ht2
/-
**ProbabilityTheory.Kernel.IndepSets.biUnion** 是 Mathlib 中的一个定理，位于命名空间 `Probabil
ityTheory.Kernel.IndepSets`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {
s : ι → Set (Set Ω)} {s' : Set (Set Ω)}   {_mΩ : MeasurableSpace Ω} {κ : Probabi
lityTheory.Kernel α Ω} {μ : MeasureTheory.Measure α} {u : Set ι},   (∀ n ∈ u, Pr
obabilityTheory.Kernel.IndepSets (s n) s' κ μ) → ProbabilityTheory.Kernel.IndepS
ets (⋃ n ∈ u, s n) s' κ μ
参数：Set Ω；Set Ω；∀ n ∈ u, ProbabilityTheory.Kernel.IndepSets (s n) s' κ μ；⋃ n ∈ u,
 s n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem IndepSets.biUnion {s : ι → Set (Set Ω)} {s' : Set (Set Ω)} {_mΩ : MeasurableSpace Ω}
    {κ : Kernel α Ω} {μ : Measure α} {u : Set ι} (hyp : ∀ n ∈ u, IndepSets (s n) s' κ μ) :
    IndepSets (⋃ n ∈ u, s n) s' κ μ := by
  intro t1 t2 ht1 ht2
  simp_rw [Set.mem_iUnion] at ht1
  rcases ht1 with ⟨n, hpn, ht1⟩
  exact hyp n hpn t1 t2 ht1 ht2
/-
**ProbabilityTheory.Kernel.IndepSets.inter** 是 Mathlib 中的一个定理，位于命名空间 `Probabilit
yTheory.Kernel.IndepSets`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {_mα : MeasurableSpace α} {s₁ s' : Set (Se
t Ω)} (s₂ : Set (Set Ω))   {_mΩ : MeasurableSpace Ω} {κ : ProbabilityTheory.Kern
el α Ω} {μ : MeasureTheory.Measure α},   ProbabilityTheory.Kernel.IndepSets s₁ s
' κ μ → ProbabilityTheory.Kernel.IndepSets (s₁ ∩ s₂) s' κ μ
参数：Set Ω；s₂ : Set (Set Ω)；s₁ ∩ s₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_inter_iff`：mem_inter_iff (x : α) (a b : Set α) : x in a inter b 
↔ x in a ∧ x in b
-/
theorem IndepSets.inter {s₁ s' : Set (Set Ω)} (s₂ : Set (Set Ω)) {_mΩ : MeasurableSpace Ω}
    {κ : Kernel α Ω} {μ : Measure α} (h₁ : IndepSets s₁ s' κ μ) :
    IndepSets (s₁ ∩ s₂) s' κ μ :=
  fun t1 t2 ht1 ht2 => h₁ t1 t2 ((Set.mem_inter_iff _ _ _).mp ht1).left ht2
/-
**ProbabilityTheory.Kernel.IndepSets.iInter** 是 Mathlib 中的一个定理，位于命名空间 `Probabili
tyTheory.Kernel.IndepSets`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {
s : ι → Set (Set Ω)} {s' : Set (Set Ω)}   {_mΩ : MeasurableSpace Ω} {κ : Probabi
lityTheory.Kernel α Ω} {μ : MeasureTheory.Measure α},   (∃ n, ProbabilityTheory.
Kernel.IndepSets (s n) s' κ μ) → ProbabilityTheory.Kernel.IndepSets (⋂ n, s n) s
' κ μ
参数：Set Ω；Set Ω；∃ n, ProbabilityTheory.Kernel.IndepSets (s n) s' κ μ；⋂ n, s n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_iInter`：mem_iInter {x : α} {s : ι -> Set α} : (x in ⋂ i, s i) ↔ 
forall i, x in s i
-/
theorem IndepSets.iInter {s : ι → Set (Set Ω)} {s' : Set (Set Ω)} {_mΩ : MeasurableSpace Ω}
    {κ : Kernel α Ω} {μ : Measure α} (h : ∃ n, IndepSets (s n) s' κ μ) :
    IndepSets (⋂ n, s n) s' κ μ := by
  intro t1 t2 ht1 ht2; obtain ⟨n, h⟩ := h; exact h t1 t2 (Set.mem_iInter.mp ht1 n) ht2
/-
**ProbabilityTheory.Kernel.IndepSets.bInter** 是 Mathlib 中的一个定理，位于命名空间 `Probabili
tyTheory.Kernel.IndepSets`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {
s : ι → Set (Set Ω)} {s' : Set (Set Ω)}   {_mΩ : MeasurableSpace Ω} {κ : Probabi
lityTheory.Kernel α Ω} {μ : MeasureTheory.Measure α} {u : Set ι},   (∃ n ∈ u, Pr
obabilityTheory.Kernel.IndepSets (s n) s' κ μ) → ProbabilityTheory.Kernel.IndepS
ets (⋂ n ∈ u, s n) s' κ μ
参数：Set Ω；Set Ω；∃ n ∈ u, ProbabilityTheory.Kernel.IndepSets (s n) s' κ μ；⋂ n ∈ u,
 s n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.biInter_subset_of_mem`：biInter_subset_of_mem {s : Set α} {t : α -> S
et β} {x : α} (xs : x in s) : ⋂ x in s, t x subseteq t x
-/
theorem IndepSets.bInter {s : ι → Set (Set Ω)} {s' : Set (Set Ω)} {_mΩ : MeasurableSpace Ω}
    {κ : Kernel α Ω} {μ : Measure α} {u : Set ι} (h : ∃ n ∈ u, IndepSets (s n) s' κ μ) :
    IndepSets (⋂ n ∈ u, s n) s' κ μ := by
  intro t1 t2 ht1 ht2
  rcases h with ⟨n, hn, h⟩
  exact h t1 t2 (Set.biInter_subset_of_mem hn ht1) ht2
/-
**ProbabilityTheory.Kernel.iIndep_comap_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `Proba
bilityTheory.Kernel`。
形式化陈述：iIndep_comap_mem_iff {f : ι -> Set Ω} {_mΩ : MeasurableSpace Ω} {κ : Kerne
l α Ω} {μ : Measure α} : iIndep (fun i => MeasurableSpace.comap (· in f i) ⊤) κ 
μ ↔ iIndepSet f κ μ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem iIndep_comap_mem_iff {f : ι → Set Ω} {_mΩ : MeasurableSpace Ω}
    {κ : Kernel α Ω} {μ : Measure α} :
    iIndep (fun i => MeasurableSpace.comap (· ∈ f i) ⊤) κ μ ↔ iIndepSet f κ μ := by
  simp_rw [← generateFrom_singleton, iIndepSet]
/-
**ProbabilityTheory.Kernel.iIndepSets_singleton_iff** 是 Mathlib 中的一个定理，位于命名空间 `P
robabilityTheory.Kernel`。
形式化陈述：iIndepSets_singleton_iff {s : ι -> Set Ω} {_mΩ : MeasurableSpace Ω} {κ : K
ernel α Ω} {μ : Measure α} : iIndepSets (fun i => {s i}) κ μ ↔ forall S : Finset
 ι, forallᵐ a ∂μ, κ a (⋂ i in S, s i) = ∏ i in S, κ a (s i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用引理 `Set.iInter₂_congr`：iInter₂_congr {s t : forall i, κ i -> Set α} (h : for
all i j, s i j = t i j) : ⋂ (i) (j), s i j = ⋂ (i) (j), t i j
-/
theorem iIndepSets_singleton_iff {s : ι → Set Ω} {_mΩ : MeasurableSpace Ω}
    {κ : Kernel α Ω} {μ : Measure α} :
    iIndepSets (fun i ↦ {s i}) κ μ ↔
      ∀ S : Finset ι, ∀ᵐ a ∂μ, κ a (⋂ i ∈ S, s i) = ∏ i ∈ S, κ a (s i) := by
  refine ⟨fun h S ↦ h S (fun i _ ↦ rfl), fun h S f hf ↦ ?_⟩
  filter_upwards [h S] with a ha
  have : ∀ i ∈ S, κ a (f i) = κ a (s i) := fun i hi ↦ by rw [hf i hi]
  rwa [Finset.prod_congr rfl this, Set.iInter₂_congr hf]
/-
**ProbabilityTheory.Kernel.indepSets_singleton_iff** 是 Mathlib 中的一个定理，位于命名空间 `Pr
obabilityTheory.Kernel`。
形式化陈述：indepSets_singleton_iff {s t : Set Ω} {_mΩ : MeasurableSpace Ω} {κ : Kerne
l α Ω} {μ : Measure α} : IndepSets {s} {t} κ μ ↔ forallᵐ a ∂μ, κ a (s inter t) =
 κ a s * κ a t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
-/
theorem indepSets_singleton_iff {s t : Set Ω} {_mΩ : MeasurableSpace Ω}
    {κ : Kernel α Ω} {μ : Measure α} :
    IndepSets {s} {t} κ μ ↔ ∀ᵐ a ∂μ, κ a (s ∩ t) = κ a s * κ a t :=
  ⟨fun h ↦ h s t rfl rfl,
   fun h s1 t1 hs1 ht1 ↦ by rwa [Set.mem_singleton_iff.mp hs1, Set.mem_singleton_iff.mp ht1]⟩

end Indep

/-! ### Deducing `Indep` from `iIndep` -/


section FromiIndepToIndep

variable {_mα : MeasurableSpace α}

/-
**ProbabilityTheory.Kernel.iIndepSets.indepSets** 是 Mathlib 中的一个定理，位于命名空间 `Proba
bilityTheory.Kernel.iIndepSets`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {
s : ι → Set (Set Ω)} {_mΩ : MeasurableSpace Ω}   {κ : ProbabilityTheory.Kernel α
 Ω} {μ : MeasureTheory.Measure α},   ProbabilityTheory.Kernel.iIndepSets s κ μ →
 ∀ {i j : ι}, i ≠ j → ProbabilityTheory.Kernel.IndepSets (s i) (s j) κ μ
参数：Set Ω；s i；s j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_insert`：mem_insert : a in insert b s ↔ a = b ∨ a in s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Finset.mem_singleton`：mem_singleton {a b : α} : b in ({a} : Finset α) ↔ 
b = a
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Finset.set_biInter_insert`：set_biInter_insert (a : α) (s : Finset α) (t 
: α -> Set β) : ⋂ x in insert a s, t x = t a inter ⋂ x in s, t x
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Finset.set_biInter_singleton`：set_biInter_singleton (a : α) (s : α -> Se
t β) : ⋂ x in ({a} : Finset α), s x = s a
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
-/
theorem iIndepSets.indepSets {s : ι → Set (Set Ω)} {_mΩ : MeasurableSpace Ω}
    {κ : Kernel α Ω} {μ : Measure α} (h_indep : iIndepSets s κ μ) {i j : ι} (hij : i ≠ j) :
    IndepSets (s i) (s j) κ μ := by
  classical
  intro t₁ t₂ ht₁ ht₂
  have hf_m : ∀ x : ι, x ∈ ({i, j} : Finset ι) → ite (x = i) t₁ t₂ ∈ s x := by
    intro x hx
    rcases Finset.mem_insert.mp hx with hx | hx
    · simp [hx, ht₁]
    · simp [Finset.mem_singleton.mp hx, hij.symm, ht₂]
  have h_inter : ⋂ (t : ι) (_ : t ∈ ({i, j} : Finset ι)), ite (t = i) t₁ t₂ =
      ite (i = i) t₁ t₂ ∩ ite (j = i) t₁ t₂ := by
    simp only [Finset.set_biInter_singleton, Finset.set_biInter_insert]
  filter_upwards [h_indep {i, j} hf_m] with a h_indep'
  grind
/-
**ProbabilityTheory.Kernel.iIndep.indep** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTh
eory.Kernel.iIndep`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {
m : ι → MeasurableSpace Ω}   {_mΩ : MeasurableSpace Ω} {κ : ProbabilityTheory.Ke
rnel α Ω} {μ : MeasureTheory.Measure α},   ProbabilityTheory.Kernel.iIndep m κ μ
 → ∀ {i j : ι}, i ≠ j → ProbabilityTheory.Kernel.Indep (m i) (m j) κ μ
参数：m i；m j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepSets.indepSets`：∀ {α : Type u_1} {Ω : Typ
e u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {s : ι → Set (Set Ω)} {_mΩ : Mea
surableSpace Ω}   {κ : ProbabilityT…
-/
theorem iIndep.indep {m : ι → MeasurableSpace Ω} {_mΩ : MeasurableSpace Ω}
    {κ : Kernel α Ω} {μ : Measure α}
    (h_indep : iIndep m κ μ) {i j : ι} (hij : i ≠ j) : Indep (m i) (m j) κ μ :=
  iIndepSets.indepSets h_indep hij

end FromiIndepToIndep

/-!
## π-system lemma

Independence of measurable spaces is equivalent to independence of generating π-systems.
-/


section FromMeasurableSpacesToSetsOfSets

/-! ### Independence of measurable space structures implies independence of generating π-systems -/

variable {_mα : MeasurableSpace α}

/-
**ProbabilityTheory.Kernel.iIndep.iIndepSets** 是 Mathlib 中的一个定理，位于命名空间 `Probabil
ityTheory.Kernel.iIndep`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {
_mΩ : MeasurableSpace Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ : MeasureTheory
.Measure α} {m : ι → MeasurableSpace Ω} {s : ι → Set (Set Ω)},   (∀ (n : ι), m n
 = MeasurableSpace.generateFrom (s n)) →     ProbabilityTheory.Kernel.iIndep m κ
 μ → ProbabilityTheory.Kernel.iIndepSets s κ μ
参数：Set Ω；∀ (n : ι), m n = MeasurableSpace.generateFrom (s n)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSpace.measurableSet_generateFrom`：measurableSet_generateFrom {
s : Set (Set α)} {t : Set α} (ht : t in s) : MeasurableSet[generateFrom s] t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem iIndep.iIndepSets {_mΩ : MeasurableSpace Ω}
    {κ : Kernel α Ω} {μ : Measure α} {m : ι → MeasurableSpace Ω}
    {s : ι → Set (Set Ω)} (hms : ∀ n, m n = generateFrom (s n)) (h_indep : iIndep m κ μ) :
    iIndepSets s κ μ :=
  fun S f hfs =>
  h_indep S fun x hxS =>
    ((hms x).symm ▸ measurableSet_generateFrom (hfs x hxS) : MeasurableSet[m x] (f x))
/-
**ProbabilityTheory.Kernel.Indep.indepSets** 是 Mathlib 中的一个定理，位于命名空间 `Probabilit
yTheory.Kernel.Indep`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {_mα : MeasurableSpace α} {_mΩ : Measurabl
eSpace Ω} {κ : ProbabilityTheory.Kernel α Ω}   {μ : MeasureTheory.Measure α} {s1
 s2 : Set (Set Ω)},   ProbabilityTheory.Kernel.Indep (MeasurableSpace.generateFr
om s1) (MeasurableSpace.generateFrom s2) κ μ →     ProbabilityTheory.Kernel.Inde
pSets s1 s2 κ μ
参数：Set Ω；MeasurableSpace.generateFrom s1；MeasurableSpace.generateFrom s2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSpace.measurableSet_generateFrom`：measurableSet_generateFrom {
s : Set (Set α)} {t : Set α} (ht : t in s) : MeasurableSet[generateFrom s] t
-/
theorem Indep.indepSets {_mΩ : MeasurableSpace Ω}
    {κ : Kernel α Ω} {μ : Measure α} {s1 s2 : Set (Set Ω)}
    (h_indep : Indep (generateFrom s1) (generateFrom s2) κ μ) :
    IndepSets s1 s2 κ μ :=
  fun t1 t2 ht1 ht2 =>
  h_indep t1 t2 (measurableSet_generateFrom ht1) (measurableSet_generateFrom ht2)

end FromMeasurableSpacesToSetsOfSets

section FromPiSystemsToMeasurableSpaces

/-! ### Independence of generating π-systems implies independence of measurable space structures -/

variable {_mα : MeasurableSpace α}

/-
**ProbabilityTheory.Kernel.IndepSets.indep_aux** 是 Mathlib 中的一个定理，位于命名空间 `Probab
ilityTheory.Kernel.IndepSets`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {_mα : MeasurableSpace α} {m₂ m : Measurab
leSpace Ω} {κ : ProbabilityTheory.Kernel α Ω}   {μ : MeasureTheory.Measure α} [P
robabilityTheory.IsZeroOrMarkovKernel κ] {p1 p2 : Set (Set Ω)},   m₂ ≤ m →     I
sPiSystem p2 →       m₂ = MeasurableSpace.generateFrom p2 →         ProbabilityT
heory.Kernel.IndepSets p1 p2 κ μ →           ∀ {t1 t2 : Set Ω},             t1 ∈
 p1 → MeasurableSet t1 → MeasurableSet t2 → ∀ᵐ (a : α) ∂μ, (κ a) (t1 ∩ t2) = (κ 
a) t1 * (κ a) t2
参数：Set Ω；a : α；κ a；t1 ∩ t2；κ a；κ a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.eq_zero_or_isMarkovKernel`：eq_zero_or_isMarkovKernel (
κ : Kernel α β) [h : IsZeroOrMarkovKernel κ] : κ = 0 ∨ IsMarkovKernel κ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ProbabilityTheory.Kernel.instIsZeroApplyMeasure`：∀ {α : Type u_1} {β : T
ype u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β},   IsZeroApply (Proba
bilityTheory.Kernel α β) α (MeasureTh…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasurableSpace.induction_on_inter`：induction_on_inter {m : MeasurableSp
ace α} {C : forall s : Set α, MeasurableSet s -> Prop} {s : Set (Set α)} (h_eq :
 m = generateFrom s) (h_…
· 使用定理 `Set.inter_empty`：inter_empty (a : Set α) : a inter ∅ = ∅
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Set.sdiff_eq`：sdiff_eq (s t : Set α) : s \ t = s inter tᶜ
· 使用定理 `Set.sdiff_self_inter`：sdiff_self_inter {s t : Set α} : s \ (s inter t) =
 s \ t
· 使用定理 `MeasureTheory.measure_sdiff`：measure_sdiff (h : s₂ subseteq s₁) (h₂ : Nu
llMeasurableSet s₂ μ) (h_fin : μ s₂ != ∞) : μ (s₁ \ s₂) = μ s₁ - μ s₂
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `ProbabilityTheory.IsFiniteKernel.isFiniteMeasure`：∀ {α : Type u_1} {β : 
Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheo
ry.Kernel α β}   [ProbabilityTheory.Is…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `MeasureTheory.measure_compl`：measure_compl (h₁ : MeasurableSet s) (h_fin
 : μ s != ∞) : μ sᶜ = μ univ - μ s
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `ProbabilityTheory.IsMarkovKernel.is_probability_measure'`：∀ {α : Type u_
1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabi
lityTheory.Kernel α β}   [ProbabilityTheory.Is…
（共 40 条，此处仅展示前 30 条）
-/
theorem IndepSets.indep_aux {m₂ m : MeasurableSpace Ω}
    {κ : Kernel α Ω} {μ : Measure α} [IsZeroOrMarkovKernel κ] {p1 p2 : Set (Set Ω)} (h2 : m₂ ≤ m)
    (hp2 : IsPiSystem p2) (hpm2 : m₂ = generateFrom p2) (hyp : IndepSets p1 p2 κ μ) {t1 t2 : Set Ω}
    (ht1 : t1 ∈ p1) (ht1m : MeasurableSet[m] t1) (ht2m : MeasurableSet[m₂] t2) :
    ∀ᵐ a ∂μ, κ a (t1 ∩ t2) = κ a t1 * κ a t2 := by
  rcases eq_zero_or_isMarkovKernel κ with rfl | h
  · simp
  induction t2, ht2m using induction_on_inter hpm2 hp2 with
  | empty => simp
  | basic u hu => exact hyp t1 u ht1 hu
  | compl u hu ihu =>
    filter_upwards [ihu] with a ha
    rw [← Set.sdiff_eq, ← Set.sdiff_self_inter,
      measure_sdiff inter_subset_left (ht1m.inter (h2 _ hu)).nullMeasurableSet (measure_ne_top _ _),
      ha, measure_compl (h2 _ hu) (measure_ne_top _ _), measure_univ, ENNReal.mul_sub, mul_one]
    exact fun _ _ ↦ measure_ne_top _ _
  | iUnion f hfd hfm ihf =>
    rw [← ae_all_iff] at ihf
    filter_upwards [ihf] with a ha
    rw [inter_iUnion, measure_iUnion, measure_iUnion hfd fun i ↦ h2 _ (hfm i)]
    · simp only [ENNReal.tsum_mul_left, ha]
    · exact hfd.mono fun i j h ↦ (h.inter_left' _).inter_right' _
    · exact fun i ↦ .inter ht1m (h2 _ <| hfm i)

/-- The measurable space structures generated by independent pi-systems are independent. -/
/-
**ProbabilityTheory.Kernel.IndepSets.indep** 是 Mathlib 中的一个定理，位于命名空间 `Probabilit
yTheory.Kernel.IndepSets`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {_mα : MeasurableSpace α} {m1 m2 m : Measu
rableSpace Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ : MeasureTheory.Measure α}
 [ProbabilityTheory.IsZeroOrMarkovKernel κ]   {p1 p2 : Set (Set Ω)},   m1 ≤ m → 
    m2 ≤ m →       IsPiSystem p1 →         IsPiSystem p2 →           m1 = Measur
ableSpace.generateFrom p1 →             m2 = MeasurableSpace.generateFrom p2 →  
             ProbabilityTheory.Kernel.IndepSets p1 p2 κ μ → ProbabilityTheory.Ke
rnel.Indep m1 m2 κ μ
参数：Set Ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.eq_zero_or_isMarkovKernel`：eq_zero_or_isMarkovKernel (
κ : Kernel α β) [h : IsZeroOrMarkovKernel κ] : κ = 0 ∨ IsMarkovKernel κ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasurableSpace.induction_on_inter`：induction_on_inter {m : MeasurableSp
ace α} {C : forall s : Set α, MeasurableSet s -> Prop} {s : Set (Set α)} (h_eq :
 m = generateFrom s) (h_…
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.empty_inter`：empty_inter (a : Set α) : ∅ inter a = ∅
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ProbabilityTheory.Kernel.IndepSets.indep_aux`：∀ {α : Type u_1} {Ω : Type
 u_2} {_mα : MeasurableSpace α} {m₂ m : MeasurableSpace Ω} {κ : ProbabilityTheor
y.Kernel α Ω}   {μ : MeasureTheory…
· 使用定理 `MeasurableSpace.measurableSet_generateFrom`：measurableSet_generateFrom {
s : Set (Set α)} {t : Set α} (ht : t in s) : MeasurableSet[generateFrom s] t
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `Set.sdiff_self_inter`：sdiff_self_inter {s t : Set α} : s \ (s inter t) =
 s \ t
· 使用定理 `Set.sdiff_eq_compl_inter`：sdiff_eq_compl_inter {s t : Set α} : s \ t = t
ᶜ inter s
· 使用定理 `MeasureTheory.measure_sdiff`：measure_sdiff (h : s₂ subseteq s₁) (h₂ : Nu
llMeasurableSet s₂ μ) (h_fin : μ s₂ != ∞) : μ (s₁ \ s₂) = μ s₁ - μ s₂
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `ProbabilityTheory.IsFiniteKernel.isFiniteMeasure`：∀ {α : Type u_1} {β : 
Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheo
ry.Kernel α β}   [ProbabilityTheory.Is…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `MeasureTheory.measure_compl`：measure_compl (h₁ : MeasurableSet s) (h_fin
 : μ s != ∞) : μ sᶜ = μ univ - μ s
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
（共 42 条，此处仅展示前 30 条）

--- 原说明 ---
The measurable space structures generated by independent pi-systems are independ
ent.
-/
theorem IndepSets.indep {m1 m2 m : MeasurableSpace Ω} {κ : Kernel α Ω} {μ : Measure α}
    [IsZeroOrMarkovKernel κ] {p1 p2 : Set (Set Ω)} (h1 : m1 ≤ m) (h2 : m2 ≤ m) (hp1 : IsPiSystem p1)
    (hp2 : IsPiSystem p2) (hpm1 : m1 = generateFrom p1) (hpm2 : m2 = generateFrom p2)
    (hyp : IndepSets p1 p2 κ μ) :
    Indep m1 m2 κ μ := by
  rcases eq_zero_or_isMarkovKernel κ with rfl | h
  · simp
  intro t1 t2 ht1 ht2
  induction t1, ht1 using induction_on_inter hpm1 hp1 with
  | empty =>
    simp only [Set.empty_inter, measure_empty, zero_mul, Filter.eventually_true]
  | basic t ht =>
    refine IndepSets.indep_aux h2 hp2 hpm2 hyp ht (h1 _ ?_) ht2
    rw [hpm1]
    exact measurableSet_generateFrom ht
  | compl t ht iht =>
    filter_upwards [iht] with a ha
    have : tᶜ ∩ t2 = t2 \ (t ∩ t2) := by
      rw [Set.inter_comm t, Set.sdiff_self_inter, Set.sdiff_eq_compl_inter]
    rw [this, Set.inter_comm t t2,
      measure_sdiff Set.inter_subset_left ((h2 _ ht2).inter (h1 _ ht)).nullMeasurableSet
        (measure_ne_top (κ a) _),
      Set.inter_comm, ha, measure_compl (h1 _ ht) (measure_ne_top (κ a) t), measure_univ,
      mul_comm (1 - κ a t), ENNReal.mul_sub (fun _ _ ↦ measure_ne_top (κ a) _), mul_one, mul_comm]
  | iUnion f hf_disj hf_meas h =>
    rw [← ae_all_iff] at h
    filter_upwards [h] with a ha
    rw [Set.inter_comm, Set.inter_iUnion, measure_iUnion]
    · rw [measure_iUnion hf_disj (fun i ↦ h1 _ (hf_meas i))]
      rw [← ENNReal.tsum_mul_right]
      congr 1 with i
      rw [Set.inter_comm t2, ha i]
    · intro i j hij
      rw [Function.onFun, Set.inter_comm t2, Set.inter_comm t2]
      exact Disjoint.inter_left _ (Disjoint.inter_right _ (hf_disj hij))
    · exact fun i ↦ (h2 _ ht2).inter (h1 _ (hf_meas i))
/-
**ProbabilityTheory.Kernel.IndepSets.indep'** 是 Mathlib 中的一个定理，位于命名空间 `Probabili
tyTheory.Kernel.IndepSets`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {_mα : MeasurableSpace α} {_mΩ : Measurabl
eSpace Ω} {κ : ProbabilityTheory.Kernel α Ω}   {μ : MeasureTheory.Measure α} [Pr
obabilityTheory.IsZeroOrMarkovKernel κ] {p1 p2 : Set (Set Ω)},   (∀ s ∈ p1, Meas
urableSet s) →     (∀ s ∈ p2, MeasurableSet s) →       IsPiSystem p1 →         I
sPiSystem p2 →           ProbabilityTheory.Kernel.IndepSets p1 p2 κ μ →         
    ProbabilityTheory.Kernel.Indep (MeasurableSpace.generateFrom p1) (Measurable
Space.generateFrom p2) κ μ
参数：Set Ω；∀ s ∈ p1, MeasurableSet s；∀ s ∈ p2, MeasurableSet s；MeasurableSpace.gen
erateFrom p1；MeasurableSpace.generateFrom p2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IndepSets.indep`：∀ {α : Type u_1} {Ω : Type u_2
} {_mα : MeasurableSpace α} {m1 m2 m : MeasurableSpace Ω}   {κ : ProbabilityTheo
ry.Kernel α Ω} {μ : MeasureThe…
· 使用定理 `MeasurableSpace.generateFrom_le`：generateFrom_le {s : Set (Set α)} {m : 
MeasurableSpace α} (h : forall t in s, MeasurableSet[m] t) : generateFrom s <= m
-/
theorem IndepSets.indep' {_mΩ : MeasurableSpace Ω}
    {κ : Kernel α Ω} {μ : Measure α} [IsZeroOrMarkovKernel κ]
    {p1 p2 : Set (Set Ω)} (hp1m : ∀ s ∈ p1, MeasurableSet s) (hp2m : ∀ s ∈ p2, MeasurableSet s)
    (hp1 : IsPiSystem p1) (hp2 : IsPiSystem p2) (hyp : IndepSets p1 p2 κ μ) :
    Indep (generateFrom p1) (generateFrom p2) κ μ :=
  hyp.indep (generateFrom_le hp1m) (generateFrom_le hp2m) hp1 hp2 rfl rfl

variable {_mΩ : MeasurableSpace Ω} {κ : Kernel α Ω} {μ : Measure α}
/-
**ProbabilityTheory.Kernel.indepSets_piiUnionInter_of_disjoint** 是 Mathlib 中的一个定
理，位于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：indepSets_piiUnionInter_of_disjoint {s : ι -> Set (Set Ω)} {S T : Set ι} (
h_indep : iIndepSets s κ μ) (hST : Disjoint S T) : IndepSets (piiUnionInter s S)
 (piiUnionInter s T) κ μ
参数：Set Ω；h_indep : iIndepSets s κ μ；hST : Disjoint S T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_union`：mem_union : a in s union t ↔ a in s ∨ a in t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `Set.disjoint_right`：disjoint_right : Disjoint s t ↔ forall ⦃a⦄, a in t -
> a ∉ s
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.Kernel.iIndepSets.ae_isProbabilityMeasure`：∀ {α : Type
 u_1} {Ω : Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {_mΩ : MeasurableS
pace Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ :…
· 使用引理 `Set.disjoint_iff_forall_ne`：disjoint_iff_forall_ne : Disjoint s t ↔ fora
ll ⦃a⦄, a in s -> forall ⦃b⦄, b in t -> a != b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
（共 36 条，此处仅展示前 30 条）
-/
theorem indepSets_piiUnionInter_of_disjoint {s : ι → Set (Set Ω)}
    {S T : Set ι} (h_indep : iIndepSets s κ μ) (hST : Disjoint S T) :
    IndepSets (piiUnionInter s S) (piiUnionInter s T) κ μ := by
  rintro t1 t2 ⟨p1, hp1, f1, ht1_m, ht1_eq⟩ ⟨p2, hp2, f2, ht2_m, ht2_eq⟩
  classical
  let g i := ite (i ∈ p1) (f1 i) Set.univ ∩ ite (i ∈ p2) (f2 i) Set.univ
  have h_P_inter : ∀ᵐ a ∂μ, κ a (t1 ∩ t2) = ∏ n ∈ p1 ∪ p2, κ a (g n) := by
    have hgm : ∀ i ∈ p1 ∪ p2, g i ∈ s i := by
      intro i hi_mem_union
      rw [Finset.mem_union] at hi_mem_union
      rcases hi_mem_union with hi1 | hi2
      · have hi2 : i ∉ p2 := fun hip2 => Set.disjoint_left.mp hST (hp1 hi1) (hp2 hip2)
        simp_rw [g, if_pos hi1, if_neg hi2, Set.inter_univ]
        exact ht1_m i hi1
      · have hi1 : i ∉ p1 := fun hip1 => Set.disjoint_right.mp hST (hp2 hi2) (hp1 hip1)
        simp_rw [g, if_neg hi1, if_pos hi2, Set.univ_inter]
        exact ht2_m i hi2
    have h_p1_inter_p2 :
      ((⋂ x ∈ p1, f1 x) ∩ ⋂ x ∈ p2, f2 x) =
        ⋂ i ∈ p1 ∪ p2, ite (i ∈ p1) (f1 i) Set.univ ∩ ite (i ∈ p2) (f2 i) Set.univ := by
      ext1 x
      simp only [Set.mem_ite_univ_right, Set.mem_inter_iff, Set.mem_iInter, Finset.mem_union]
      exact
        ⟨fun h i _ => ⟨h.1 i, h.2 i⟩, fun h =>
          ⟨fun i hi => (h i (Or.inl hi)).1 hi, fun i hi => (h i (Or.inr hi)).2 hi⟩⟩
    filter_upwards [h_indep _ hgm] with a ha
    rw [ht1_eq, ht2_eq, h_p1_inter_p2, ← ha]
  filter_upwards [h_P_inter, h_indep p1 ht1_m, h_indep p2 ht2_m, h_indep.ae_isProbabilityMeasure]
    with a h_P_inter ha1 ha2 h'
  have h_μg : ∀ n, κ a (g n) = (ite (n ∈ p1) (κ a (f1 n)) 1) * (ite (n ∈ p2) (κ a (f2 n)) 1) := by
    intro n
    dsimp only [g]
    split_ifs with h1 h2
    · exact absurd rfl (Set.disjoint_iff_forall_ne.mp hST (hp1 h1) (hp2 h2))
    all_goals simp only [measure_univ, one_mul, mul_one, Set.inter_univ, Set.univ_inter]
  simp_rw [h_P_inter, h_μg, Finset.prod_mul_distrib,
    Finset.prod_ite_mem (p1 ∪ p2) p1 (fun x ↦ κ a (f1 x)), Finset.union_inter_cancel_left,
    Finset.prod_ite_mem (p1 ∪ p2) p2 (fun x => κ a (f2 x)), Finset.union_inter_cancel_right, ht1_eq,
      ← ha1, ht2_eq, ← ha2]
/-
**ProbabilityTheory.Kernel.iIndepSet.indep_generateFrom_of_disjoint** 是 Mathlib 
中的一个定理，位于命名空间 `ProbabilityTheory.Kernel.iIndepSet`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {
_mΩ : MeasurableSpace Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ : MeasureTheory
.Measure α} {s : ι → Set Ω},   (∀ (n : ι), MeasurableSet (s n)) →     Probabilit
yTheory.Kernel.iIndepSet s κ μ →       ∀ (S T : Set ι),         Disjoint S T →  
         ProbabilityTheory.Kernel.Indep (MeasurableSpace.generateFrom {t | ∃ n ∈
 S, s n = t})             (MeasurableSpace.generateFrom {t | ∃ k ∈ T, s k = t}) 
κ μ
参数：∀ (n : ι), MeasurableSet (s n)；S T : Set ι；MeasurableSpace.generateFrom {t | 
∃ n ∈ S, s n = t}；MeasurableSpace.generateFrom {t | ∃ k ∈ T, s k = t}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `ProbabilityTheory.Kernel.exists_ae_eq_isMarkovKernel`：exists_ae_eq_isMar
kovKernel {μ : Measure α} (h : forallᵐ a ∂μ, IsProbabilityMeasure (κ a)) (h' : μ
 != 0) : exists (η : Kernel α β), (κ =ᵐ[μ]…
· 使用定理 `ProbabilityTheory.Kernel.iIndep.ae_isProbabilityMeasure`：∀ {α : Type u_1
} {Ω : Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {m : ι → MeasurableSpa
ce Ω}   {_mΩ : MeasurableSpace Ω} {κ : Probab…
· 使用定理 `ProbabilityTheory.Kernel.Indep.congr`：∀ {α : Type u_1} {Ω : Type u_2} {_
mα : MeasurableSpace α} {μ : MeasureTheory.Measure α} {m₁ m₂ _mΩ : MeasurableSpa
ce Ω}   {κ η : Probability…
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `generateFrom_piiUnionInter_singleton_left`：generateFrom_piiUnionInter_si
ngleton_left (s : ι -> Set α) (S : Set ι) : generateFrom (piiUnionInter (fun k =
> {s k}) S) = generateFrom { t …
· 使用定理 `ProbabilityTheory.Kernel.IndepSets.indep'`：∀ {α : Type u_1} {Ω : Type u_
2} {_mα : MeasurableSpace α} {_mΩ : MeasurableSpace Ω} {κ : ProbabilityTheory.Ke
rnel α Ω}   {μ : MeasureTheory.…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `generateFrom_piiUnionInter_le`：generateFrom_piiUnionInter_le {m : Measur
ableSpace α} (π : ι -> Set (Set α)) (h : forall n, generateFrom (π n) <= m) (S :
 Set ι) : generateF…
· 使用定理 `MeasurableSpace.generateFrom_le`：generateFrom_le {s : Set (Set α)} {m : 
MeasurableSpace α} (h : forall t in s, MeasurableSet[m] t) : generateFrom s <= m
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `MeasurableSpace.measurableSet_generateFrom`：measurableSet_generateFrom {
s : Set (Set α)} {t : Set α} (ht : t in s) : MeasurableSet[generateFrom s] t
· 使用定理 `isPiSystem_piiUnionInter`：isPiSystem_piiUnionInter (π : ι -> Set (Set α)
) (hpi : forall x, IsPiSystem (π x)) (S : Set ι) : IsPiSystem (piiUnionInter π S
)
· 使用定理 `IsPiSystem.singleton`：IsPiSystem.singleton (S : Set α) : IsPiSystem ({S}
 : Set (Set α))
· 使用定理 `ProbabilityTheory.Kernel.indepSets_piiUnionInter_of_disjoint`：indepSets_
piiUnionInter_of_disjoint {s : ι -> Set (Set Ω)} {S T : Set ι} (h_indep : iIndep
Sets s κ μ) (hST : Disjoint S T) : IndepSets (piiU…
· 使用定理 `ProbabilityTheory.Kernel.iIndep.iIndepSets`：∀ {α : Type u_1} {Ω : Type u
_2} {ι : Type u_3} {_mα : MeasurableSpace α} {_mΩ : MeasurableSpace Ω}   {κ : Pr
obabilityTheory.Kernel α Ω} {μ :…
· 使用定理 `ProbabilityTheory.Kernel.iIndepSet.congr`：∀ {α : Type u_1} {Ω : Type u_2
} {ι : Type u_3} {_mα : MeasurableSpace α} {_mΩ : MeasurableSpace Ω}   {κ η : Pr
obabilityTheory.Kernel α Ω} {μ…
-/
theorem iIndepSet.indep_generateFrom_of_disjoint {s : ι → Set Ω}
    (hsm : ∀ n, MeasurableSet (s n)) (hs : iIndepSet s κ μ) (S T : Set ι) (hST : Disjoint S T) :
    Indep (generateFrom { t | ∃ n ∈ S, s n = t }) (generateFrom { t | ∃ k ∈ T, s k = t }) κ μ := by
  rcases eq_or_ne μ 0 with rfl | hμ
  · simp
  obtain ⟨η, η_eq, hη⟩ : ∃ (η : Kernel α Ω), κ =ᵐ[μ] η ∧ IsMarkovKernel η :=
    exists_ae_eq_isMarkovKernel hs.ae_isProbabilityMeasure hμ
  apply Indep.congr (Filter.EventuallyEq.symm η_eq)
  rw [← generateFrom_piiUnionInter_singleton_left, ← generateFrom_piiUnionInter_singleton_left]
  refine
    IndepSets.indep'
      (fun t ht => generateFrom_piiUnionInter_le _ ?_ _ _ (measurableSet_generateFrom ht))
      (fun t ht => generateFrom_piiUnionInter_le _ ?_ _ _ (measurableSet_generateFrom ht)) ?_ ?_ ?_
  · exact fun k => generateFrom_le fun t ht => (Set.mem_singleton_iff.1 ht).symm ▸ hsm k
  · exact fun k => generateFrom_le fun t ht => (Set.mem_singleton_iff.1 ht).symm ▸ hsm k
  · exact isPiSystem_piiUnionInter _ (fun k => IsPiSystem.singleton _) _
  · exact isPiSystem_piiUnionInter _ (fun k => IsPiSystem.singleton _) _
  · exact indepSets_piiUnionInter_of_disjoint (iIndep.iIndepSets (fun n => rfl) (hs.congr η_eq)) hST
/-
**ProbabilityTheory.Kernel.indep_iSup_of_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Pro
babilityTheory.Kernel`。
形式化陈述：indep_iSup_of_disjoint {m : ι -> MeasurableSpace Ω} (h_le : forall i, m i 
<= _mΩ) (h_indep : iIndep m κ μ) {S T : Set ι} (hST : Disjoint S T) : Indep (⨆ i
 in S, m i) (⨆ i in T, m i) κ μ
参数：h_le : forall i, m i <= _mΩ；h_indep : iIndep m κ μ；hST : Disjoint S T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `ProbabilityTheory.Kernel.exists_ae_eq_isMarkovKernel`：exists_ae_eq_isMar
kovKernel {μ : Measure α} (h : forallᵐ a ∂μ, IsProbabilityMeasure (κ a)) (h' : μ
 != 0) : exists (η : Kernel α β), (κ =ᵐ[μ]…
· 使用定理 `ProbabilityTheory.Kernel.iIndep.ae_isProbabilityMeasure`：∀ {α : Type u_1
} {Ω : Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {m : ι → MeasurableSpa
ce Ω}   {_mΩ : MeasurableSpace Ω} {κ : Probab…
· 使用定理 `ProbabilityTheory.Kernel.Indep.congr`：∀ {α : Type u_1} {Ω : Type u_2} {_
mα : MeasurableSpace α} {μ : MeasureTheory.Measure α} {m₁ m₂ _mΩ : MeasurableSpa
ce Ω}   {κ η : Probability…
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `ProbabilityTheory.Kernel.IndepSets.indep`：∀ {α : Type u_1} {Ω : Type u_2
} {_mα : MeasurableSpace α} {m1 m2 m : MeasurableSpace Ω}   {κ : ProbabilityTheo
ry.Kernel α Ω} {μ : MeasureThe…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
· 使用定理 `isPiSystem_piiUnionInter`：isPiSystem_piiUnionInter (π : ι -> Set (Set α)
) (hpi : forall x, IsPiSystem (π x)) (S : Set ι) : IsPiSystem (piiUnionInter π S
)
· 使用定理 `MeasurableSpace.isPiSystem_measurableSet`：isPiSystem_measurableSet {α : 
Type*} [MeasurableSpace α] : IsPiSystem { s : Set α | MeasurableSet s }
· 使用定理 `generateFrom_piiUnionInter_measurableSet`：generateFrom_piiUnionInter_mea
surableSet (m : ι -> MeasurableSpace α) (S : Set ι) : generateFrom (piiUnionInte
r (fun n => { s | MeasurableSe…
· 使用定理 `ProbabilityTheory.Kernel.indepSets_piiUnionInter_of_disjoint`：indepSets_
piiUnionInter_of_disjoint {s : ι -> Set (Set Ω)} {S T : Set ι} (h_indep : iIndep
Sets s κ μ) (hST : Disjoint S T) : IndepSets (piiU…
· 使用定理 `ProbabilityTheory.Kernel.iIndep.congr`：∀ {α : Type u_1} {Ω : Type u_2} {
ι : Type u_3} {_mα : MeasurableSpace α} {m : ι → MeasurableSpace Ω}   {_mΩ : Mea
surableSpace Ω} {κ η : Prob…
-/
theorem indep_iSup_of_disjoint {m : ι → MeasurableSpace Ω}
    (h_le : ∀ i, m i ≤ _mΩ) (h_indep : iIndep m κ μ) {S T : Set ι} (hST : Disjoint S T) :
    Indep (⨆ i ∈ S, m i) (⨆ i ∈ T, m i) κ μ := by
  rcases eq_or_ne μ 0 with rfl | hμ
  · simp
  obtain ⟨η, η_eq, hη⟩ : ∃ (η : Kernel α Ω), κ =ᵐ[μ] η ∧ IsMarkovKernel η :=
    exists_ae_eq_isMarkovKernel h_indep.ae_isProbabilityMeasure hμ
  apply Indep.congr (Filter.EventuallyEq.symm η_eq)
  refine
    IndepSets.indep (iSup₂_le fun i _ => h_le i) (iSup₂_le fun i _ => h_le i) ?_ ?_
      (generateFrom_piiUnionInter_measurableSet m S).symm
      (generateFrom_piiUnionInter_measurableSet m T).symm ?_
  · exact isPiSystem_piiUnionInter _ (fun n => @isPiSystem_measurableSet Ω (m n)) _
  · exact isPiSystem_piiUnionInter _ (fun n => @isPiSystem_measurableSet Ω (m n)) _
  · exact indepSets_piiUnionInter_of_disjoint (h_indep.congr η_eq) hST
/-
**ProbabilityTheory.Kernel.indep_iSup_of_directed_le** 是 Mathlib 中的一个定理，位于命名空间 `
ProbabilityTheory.Kernel`。
形式化陈述：indep_iSup_of_directed_le {Ω} {m : ι -> MeasurableSpace Ω} {m' m0 : Measur
ableSpace Ω} {κ : Kernel α Ω} {μ : Measure α} [IsZeroOrMarkovKernel κ] (h_indep 
: forall i, Indep (m i) m' κ μ) (h_le : forall i, m i <= m0) (h_le' : m' <= m0) 
(hm : Directed (· <= ·) m) : Indep (⨆ i, m i) m' κ μ
参数：h_indep : forall i, Indep (m i) m' κ μ；h_le : forall i, m i <= m0；h_le' : m' 
<= m0；hm : Directed (· <= ·) m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSpace.isPiSystem_measurableSet`：isPiSystem_measurableSet {α : 
Type*} [MeasurableSpace α] : IsPiSystem { s : Set α | MeasurableSet s }
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasurableSpace.generateFrom_measurableSet`：generateFrom_measurableSet [
MeasurableSpace α] : generateFrom {s : Set α | MeasurableSet s} = ‹_›
· 使用定理 `isPiSystem_iUnion_of_directed_le`：isPiSystem_iUnion_of_directed_le {α ι}
 (p : ι -> Set (Set α)) (hp_pi : forall n, IsPiSystem (p n)) (hp_directed : Dire
cted (· <= ·) p) : IsP…
· 使用定理 `ProbabilityTheory.Kernel.IndepSets.iUnion`：∀ {α : Type u_1} {Ω : Type u_
2} {ι : Type u_3} {_mα : MeasurableSpace α} {s : ι → Set (Set Ω)} {s' : Set (Set
 Ω)}   {_mΩ : MeasurableSpace Ω…
· 使用定理 `ProbabilityTheory.Kernel.Indep.indepSets`：∀ {α : Type u_1} {Ω : Type u_2
} {_mα : MeasurableSpace α} {_mΩ : MeasurableSpace Ω} {κ : ProbabilityTheory.Ker
nel α Ω}   {μ : MeasureTheory.…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.IndepSets.indep`：∀ {α : Type u_1} {Ω : Type u_2
} {_mα : MeasurableSpace α} {m1 m2 m : MeasurableSpace Ω}   {κ : ProbabilityTheo
ry.Kernel α Ω} {μ : MeasureThe…
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `MeasurableSpace.generateFrom_iUnion_measurableSet`：generateFrom_iUnion_m
easurableSet (m : ι -> MeasurableSpace α) : generateFrom (⋃ n, { t | MeasurableS
et[m n] t }) = ⨆ n, m n
-/
theorem indep_iSup_of_directed_le {Ω} {m : ι → MeasurableSpace Ω} {m' m0 : MeasurableSpace Ω}
    {κ : Kernel α Ω} {μ : Measure α} [IsZeroOrMarkovKernel κ] (h_indep : ∀ i, Indep (m i) m' κ μ)
    (h_le : ∀ i, m i ≤ m0) (h_le' : m' ≤ m0) (hm : Directed (· ≤ ·) m) :
    Indep (⨆ i, m i) m' κ μ := by
  let p : ι → Set (Set Ω) := fun n => { t | MeasurableSet[m n] t }
  have hp : ∀ n, IsPiSystem (p n) := fun n => @isPiSystem_measurableSet Ω (m n)
  have h_gen_n : ∀ n, m n = generateFrom (p n) := fun n =>
    (@generateFrom_measurableSet Ω (m n)).symm
  have hp_supr_pi : IsPiSystem (⋃ n, p n) := isPiSystem_iUnion_of_directed_le p hp hm
  let p' := { t : Set Ω | MeasurableSet[m'] t }
  have hp'_pi : IsPiSystem p' := @isPiSystem_measurableSet Ω m'
  have h_gen' : m' = generateFrom p' := (@generateFrom_measurableSet Ω m').symm
  -- the π-systems defined are independent
  have h_pi_system_indep : IndepSets (⋃ n, p n) p' κ μ := by
    refine IndepSets.iUnion ?_
    conv at h_indep =>
      intro i
      rw [h_gen_n i, h_gen']
    exact fun n => (h_indep n).indepSets
  -- now go from π-systems to σ-algebras
  refine IndepSets.indep (iSup_le h_le) h_le' hp_supr_pi hp'_pi ?_ h_gen' h_pi_system_indep
  exact (generateFrom_iUnion_measurableSet _).symm
/-
**ProbabilityTheory.Kernel.iIndepSet.indep_generateFrom_lt** 是 Mathlib 中的一个定理，位于
命名空间 `ProbabilityTheory.Kernel.iIndepSet`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {
_mΩ : MeasurableSpace Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ : MeasureTheory
.Measure α} [inst : Preorder ι] {s : ι → Set Ω},   (∀ (n : ι), MeasurableSet (s 
n)) →     ProbabilityTheory.Kernel.iIndepSet s κ μ →       ∀ (i : ι),         Pr
obabilityTheory.Kernel.Indep (MeasurableSpace.generateFrom {s i})           (Mea
surableSpace.generateFrom {t | ∃ j < i, s j = t}) κ μ
参数：∀ (n : ι), MeasurableSet (s n)；i : ι；MeasurableSpace.generateFrom {s i}；Measu
rableSpace.generateFrom {t | ∃ j < i, s j = t}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.ofPred_eq_eq_singleton'`：ofPred_eq_eq_singleton' {a : α} : { x | a =
 x } = {a}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ProbabilityTheory.Kernel.iIndepSet.indep_generateFrom_of_disjoint`：∀ {α 
: Type u_1} {Ω : Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {_mΩ : Measu
rableSpace Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ :…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.disjoint_singleton_left`：disjoint_singleton_left : Disjoint {a} s ↔ 
a ∉ s
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
-/
theorem iIndepSet.indep_generateFrom_lt [Preorder ι] {s : ι → Set Ω}
    (hsm : ∀ n, MeasurableSet (s n)) (hs : iIndepSet s κ μ) (i : ι) :
    Indep (generateFrom {s i}) (generateFrom { t | ∃ j < i, s j = t }) κ μ := by
  convert!
    iIndepSet.indep_generateFrom_of_disjoint hsm hs { i } {j | j < i}
      (Set.disjoint_singleton_left.mpr (lt_irrefl _)) using 1
  simp only [Set.mem_singleton_iff, exists_eq_left, Set.ofPred_eq_eq_singleton']
/-
**ProbabilityTheory.Kernel.iIndepSet.indep_generateFrom_le** 是 Mathlib 中的一个定理，位于
命名空间 `ProbabilityTheory.Kernel.iIndepSet`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {
_mΩ : MeasurableSpace Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ : MeasureTheory
.Measure α} [inst : Preorder ι] {s : ι → Set Ω},   (∀ (n : ι), MeasurableSet (s 
n)) →     ProbabilityTheory.Kernel.iIndepSet s κ μ →       ∀ (i : ι) {k : ι},   
      i < k →           ProbabilityTheory.Kernel.Indep (MeasurableSpace.generate
From {s k})             (MeasurableSpace.generateFrom {t | ∃ j ≤ i, s j = t}) κ 
μ
参数：∀ (n : ι), MeasurableSet (s n)；i : ι；MeasurableSpace.generateFrom {s k}；Measu
rableSpace.generateFrom {t | ∃ j ≤ i, s j = t}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.ofPred_eq_eq_singleton'`：ofPred_eq_eq_singleton' {a : α} : { x | a =
 x } = {a}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ProbabilityTheory.Kernel.iIndepSet.indep_generateFrom_of_disjoint`：∀ {α 
: Type u_1} {Ω : Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {_mΩ : Measu
rableSpace Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ :…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.disjoint_singleton_left`：disjoint_singleton_left : Disjoint {a} s ↔ 
a ∉ s
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
-/
theorem iIndepSet.indep_generateFrom_le [Preorder ι] {s : ι → Set Ω}
    (hsm : ∀ n, MeasurableSet (s n)) (hs : iIndepSet s κ μ) (i : ι) {k : ι} (hk : i < k) :
    Indep (generateFrom {s k}) (generateFrom { t | ∃ j ≤ i, s j = t }) κ μ := by
  convert!
    iIndepSet.indep_generateFrom_of_disjoint hsm hs { k } {j | j ≤ i}
      (Set.disjoint_singleton_left.mpr hk.not_ge) using 1
  simp only [Set.mem_singleton_iff, exists_eq_left, Set.ofPred_eq_eq_singleton']
/-
**ProbabilityTheory.Kernel.iIndepSet.indep_generateFrom_le_nat** 是 Mathlib 中的一个定
理，位于命名空间 `ProbabilityTheory.Kernel.iIndepSet`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {_mα : MeasurableSpace α} {_mΩ : Measurabl
eSpace Ω} {κ : ProbabilityTheory.Kernel α Ω}   {μ : MeasureTheory.Measure α} {s 
: ℕ → Set Ω},   (∀ (n : ℕ), MeasurableSet (s n)) →     ProbabilityTheory.Kernel.
iIndepSet s κ μ →       ∀ (n : ℕ),         ProbabilityTheory.Kernel.Indep (Measu
rableSpace.generateFrom {s (n + 1)})           (MeasurableSpace.generateFrom {t 
| ∃ k ≤ n, s k = t}) κ μ
参数：∀ (n : ℕ), MeasurableSet (s n)；n : ℕ；MeasurableSpace.generateFrom {s (n + 1)}
；MeasurableSpace.generateFrom {t | ∃ k ≤ n, s k = t}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepSet.indep_generateFrom_le`：∀ {α : Type u_
1} {Ω : Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {_mΩ : MeasurableSpac
e Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ :…
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
-/
theorem iIndepSet.indep_generateFrom_le_nat {s : ℕ → Set Ω}
    (hsm : ∀ n, MeasurableSet (s n)) (hs : iIndepSet s κ μ) (n : ℕ) :
    Indep (generateFrom {s (n + 1)}) (generateFrom { t | ∃ k ≤ n, s k = t }) κ μ :=
  iIndepSet.indep_generateFrom_le hsm hs _ n.lt_succ_self
/-
**ProbabilityTheory.Kernel.indep_iSup_of_monotone** 是 Mathlib 中的一个定理，位于命名空间 `Pro
babilityTheory.Kernel`。
形式化陈述：indep_iSup_of_monotone [SemilatticeSup ι] {Ω} {m : ι -> MeasurableSpace Ω}
 {m' m0 : MeasurableSpace Ω} {κ : Kernel α Ω} {μ : Measure α} [IsZeroOrMarkovKer
nel κ] (h_indep : forall i, Indep (m i) m' κ μ) (h_le : forall i, m i <= m0) (h_
le' : m' <= m0) (hm : Monotone m) : Indep (⨆ i, m i) m' κ μ
参数：h_indep : forall i, Indep (m i) m' κ μ；h_le : forall i, m i <= m0；h_le' : m' 
<= m0；hm : Monotone m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.indep_iSup_of_directed_le`：indep_iSup_of_direct
ed_le {Ω} {m : ι -> MeasurableSpace Ω} {m' m0 : MeasurableSpace Ω} {κ : Kernel α
 Ω} {μ : Measure α} [IsZeroOrMarkovKerne…
· 使用定理 `Monotone.directed_le`：Monotone.directed_le [Preorder α] [IsDirectedOrder
 α] [Preorder β] {f : α -> β} : Monotone f -> Directed (· <= ·) f
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
-/
theorem indep_iSup_of_monotone [SemilatticeSup ι] {Ω} {m : ι → MeasurableSpace Ω}
    {m' m0 : MeasurableSpace Ω} {κ : Kernel α Ω} {μ : Measure α} [IsZeroOrMarkovKernel κ]
    (h_indep : ∀ i, Indep (m i) m' κ μ) (h_le : ∀ i, m i ≤ m0) (h_le' : m' ≤ m0)
    (hm : Monotone m) :
    Indep (⨆ i, m i) m' κ μ :=
  indep_iSup_of_directed_le h_indep h_le h_le' (Monotone.directed_le hm)
/-
**ProbabilityTheory.Kernel.indep_iSup_of_antitone** 是 Mathlib 中的一个定理，位于命名空间 `Pro
babilityTheory.Kernel`。
形式化陈述：indep_iSup_of_antitone [SemilatticeInf ι] {Ω} {m : ι -> MeasurableSpace Ω}
 {m' m0 : MeasurableSpace Ω} {κ : Kernel α Ω} {μ : Measure α} [IsZeroOrMarkovKer
nel κ] (h_indep : forall i, Indep (m i) m' κ μ) (h_le : forall i, m i <= m0) (h_
le' : m' <= m0) (hm : Antitone m) : Indep (⨆ i, m i) m' κ μ
参数：h_indep : forall i, Indep (m i) m' κ μ；h_le : forall i, m i <= m0；h_le' : m' 
<= m0；hm : Antitone m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.indep_iSup_of_directed_le`：indep_iSup_of_direct
ed_le {Ω} {m : ι -> MeasurableSpace Ω} {m' m0 : MeasurableSpace Ω} {κ : Kernel α
 Ω} {μ : Measure α} [IsZeroOrMarkovKerne…
· 使用定理 `Antitone.directed_le`：Antitone.directed_le [Preorder α] [IsCodirectedOrd
er α] [Preorder β] {f : α -> β} (hf : Antitone f) : Directed (· <= ·) f
· 使用定理 `SemilatticeInf.instIsCodirectedOrder`：∀ {α : Type u_1} [inst : Semilatti
ceInf α], IsCodirectedOrder α
-/
theorem indep_iSup_of_antitone [SemilatticeInf ι] {Ω} {m : ι → MeasurableSpace Ω}
    {m' m0 : MeasurableSpace Ω} {κ : Kernel α Ω} {μ : Measure α} [IsZeroOrMarkovKernel κ]
    (h_indep : ∀ i, Indep (m i) m' κ μ) (h_le : ∀ i, m i ≤ m0) (h_le' : m' ≤ m0)
    (hm : Antitone m) :
    Indep (⨆ i, m i) m' κ μ :=
  indep_iSup_of_directed_le h_indep h_le h_le' hm.directed_le
/-
**ProbabilityTheory.Kernel.iIndepSets.piiUnionInter_of_notMem** 是 Mathlib 中的一个定理
，位于命名空间 `ProbabilityTheory.Kernel.iIndepSets`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {
_mΩ : MeasurableSpace Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ : MeasureTheory
.Measure α} {π : ι → Set (Set Ω)} {a : ι} {S : Finset ι},   ProbabilityTheory.Ke
rnel.iIndepSets π κ μ → a ∉ S → ProbabilityTheory.Kernel.IndepSets (piiUnionInte
r π ↑S) (π a) κ μ
参数：Set Ω；piiUnionInter π ↑S；π a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_insert`：mem_insert : a in insert b s ↔ a = b ∨ a in s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Finset.coe_subset`：coe_subset {s₁ s₂ : Finset α} : (s₁ : Set α) subseteq
 s₂ ↔ s₁ subseteq s₂
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.set_biInter_insert`：set_biInter_insert (a : α) (s : Finset α) (t 
: α -> Set β) : ⋂ x in insert a s, t x = t a inter ⋂ x in s, t x
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem iIndepSets.piiUnionInter_of_notMem {π : ι → Set (Set Ω)} {a : ι} {S : Finset ι}
    (hp_ind : iIndepSets π κ μ) (haS : a ∉ S) :
    IndepSets (piiUnionInter π S) (π a) κ μ := by
  rintro t1 t2 ⟨s, hs_mem, ft1, hft1_mem, ht1_eq⟩ ht2_mem_pia
  rw [Finset.coe_subset] at hs_mem
  classical
  let f := fun n => ite (n = a) t2 (ite (n ∈ s) (ft1 n) Set.univ)
  have h_f_mem : ∀ n ∈ insert a s, f n ∈ π n := by
    intro n hn_mem_insert
    dsimp only [f]
    rcases Finset.mem_insert.mp hn_mem_insert with hn_mem | hn_mem
    · simp [hn_mem, ht2_mem_pia]
    · grind
  have h_f_mem_pi : ∀ n ∈ s, f n ∈ π n := fun x hxS => h_f_mem x (by simp [hxS])
  have h_t1 : t1 = ⋂ n ∈ s, f n := by
    suffices h_forall : ∀ n ∈ s, f n = ft1 n by grind
    intro n hnS
    have hn_ne_a : n ≠ a := by rintro rfl; exact haS (hs_mem hnS)
    simp_rw [f, if_pos hnS, if_neg hn_ne_a]
  have h_μ_t1 : ∀ᵐ a' ∂μ, κ a' t1 = ∏ n ∈ s, κ a' (f n) := by
    filter_upwards [hp_ind s h_f_mem_pi] with a' ha'
    rw [h_t1, ← ha']
  have h_t2 : t2 = f a := by simp [f]
  have h_μ_inter : ∀ᵐ a' ∂μ, κ a' (t1 ∩ t2) = ∏ n ∈ insert a s, κ a' (f n) := by
    have h_t1_inter_t2 : t1 ∩ t2 = ⋂ n ∈ insert a s, f n := by
      rw [h_t1, h_t2, Finset.set_biInter_insert, Set.inter_comm]
    filter_upwards [hp_ind (insert a s) h_f_mem] with a' ha'
    rw [h_t1_inter_t2, ← ha']
  have has : a ∉ s := fun has_mem => haS (hs_mem has_mem)
  filter_upwards [h_μ_t1, h_μ_inter] with a' ha1 ha2
  rw [ha2, Finset.prod_insert has, h_t2, mul_comm, ha1]

/-- The measurable space structures generated by independent pi-systems are independent. -/
/-
**ProbabilityTheory.Kernel.iIndepSets.iIndep** 是 Mathlib 中的一个定理，位于命名空间 `Probabil
ityTheory.Kernel.iIndepSets`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {
_mΩ : MeasurableSpace Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ : MeasureTheory
.Measure α} (m : ι → MeasurableSpace Ω),   (∀ (i : ι), m i ≤ _mΩ) →     ∀ (π : ι
 → Set (Set Ω)),       (∀ (n : ι), IsPiSystem (π n)) →         (∀ (i : ι), m i =
 MeasurableSpace.generateFrom (π i)) →           ProbabilityTheory.Kernel.iIndep
Sets π κ μ → ProbabilityTheory.Kernel.iIndep m κ μ
参数：m : ι → MeasurableSpace Ω；∀ (i : ι), m i ≤ _mΩ；π : ι → Set (Set Ω)；∀ (n : ι),
 IsPiSystem (π n)；∀ (i : ι), m i = MeasurableSpace.generateFrom (π i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `ProbabilityTheory.Kernel.exists_ae_eq_isMarkovKernel`：exists_ae_eq_isMar
kovKernel {μ : Measure α} (h : forallᵐ a ∂μ, IsProbabilityMeasure (κ a)) (h' : μ
 != 0) : exists (η : Kernel α β), (κ =ᵐ[μ]…
· 使用定理 `ProbabilityTheory.Kernel.iIndepSets.ae_isProbabilityMeasure`：∀ {α : Type
 u_1} {Ω : Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {_mΩ : MeasurableS
pace Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ :…
· 使用定理 `ProbabilityTheory.Kernel.iIndep.congr`：∀ {α : Type u_1} {Ω : Type u_2} {
ι : Type u_3} {_mα : MeasurableSpace α} {m : ι → MeasurableSpace Ω}   {_mΩ : Mea
surableSpace Ω} {κ η : Prob…
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iInter_of_empty`：iInter_of_empty [IsEmpty ι] (s : ι -> Set α) : ⋂ i,
 s i = univ
· 使用定理 `Set.iInter_univ`：iInter_univ : (⋂ _ : ι, univ : Set α) = univ
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `ProbabilityTheory.IsMarkovKernel.is_probability_measure'`：∀ {α : Type u_
1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabi
lityTheory.Kernel α β}   [ProbabilityTheory.Is…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `isPiSystem_piiUnionInter`：isPiSystem_piiUnionInter (π : ι -> Set (Set α)
) (hpi : forall x, IsPiSystem (π x)) (S : Set ι) : IsPiSystem (piiUnionInter π S
)
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `generateFrom_piiUnionInter_le`：generateFrom_piiUnionInter_le {m : Measur
ableSpace α} (π : ι -> Set (Set α)) (h : forall n, generateFrom (π n) <= m) (S :
 Set ι) : generateF…
· 使用定理 `ProbabilityTheory.Kernel.IndepSets.indep`：∀ {α : Type u_1} {Ω : Type u_2
} {_mα : MeasurableSpace α} {m1 m2 m : MeasurableSpace Ω}   {κ : ProbabilityTheo
ry.Kernel α Ω} {μ : MeasureThe…
（共 41 条，此处仅展示前 30 条）

--- 原说明 ---
The measurable space structures generated by independent pi-systems are independ
ent.
-/
theorem iIndepSets.iIndep (m : ι → MeasurableSpace Ω)
    (h_le : ∀ i, m i ≤ _mΩ) (π : ι → Set (Set Ω)) (h_pi : ∀ n, IsPiSystem (π n))
    (h_generate : ∀ i, m i = generateFrom (π i)) (h_ind : iIndepSets π κ μ) :
    iIndep m κ μ := by
  classical
  rcases eq_or_ne μ 0 with rfl | hμ
  · simp
  obtain ⟨η, η_eq, hη⟩ : ∃ (η : Kernel α Ω), κ =ᵐ[μ] η ∧ IsMarkovKernel η :=
    exists_ae_eq_isMarkovKernel h_ind.ae_isProbabilityMeasure hμ
  apply iIndep.congr (Filter.EventuallyEq.symm η_eq)
  intro s f
  refine Finset.induction ?_ ?_ s
  · simp
  · intro a S ha_notin_S h_rec hf_m
    have hf_m_S : ∀ x ∈ S, MeasurableSet[m x] (f x) := fun x hx => hf_m x (by simp [hx])
    let p := piiUnionInter π S
    set m_p := generateFrom p with hS_eq_generate
    have h_indep : Indep m_p (m a) η μ := by
      have hp : IsPiSystem p := isPiSystem_piiUnionInter π h_pi S
      have h_le' : ∀ i, generateFrom (π i) ≤ _mΩ := fun i ↦ (h_generate i).symm.trans_le (h_le i)
      have hm_p : m_p ≤ _mΩ := generateFrom_piiUnionInter_le π h_le' S
      exact IndepSets.indep hm_p (h_le a) hp (h_pi a) hS_eq_generate (h_generate a)
        (iIndepSets.piiUnionInter_of_notMem (h_ind.congr η_eq) ha_notin_S)
    have h := h_indep.symm (f a) (⋂ n ∈ S, f n) (hf_m a (Finset.mem_insert_self a S)) ?_
    · filter_upwards [h_rec hf_m_S, h] with a' ha' h'
      rwa [Finset.set_biInter_insert, Finset.prod_insert ha_notin_S, ← ha']
    · have h_le_p : ∀ i ∈ S, m i ≤ m_p := by
        intro n hn
        rw [hS_eq_generate, h_generate n]
        exact le_generateFrom_piiUnionInter (S : Set ι) hn
      have h_S_f : ∀ i ∈ S, MeasurableSet[m_p] (f i) :=
        fun i hi ↦ (h_le_p i hi) (f i) (hf_m_S i hi)
      exact S.measurableSet_biInter h_S_f

end FromPiSystemsToMeasurableSpaces

section IndepSet

/-! ### Independence of measurable sets

We prove the following equivalences on `IndepSet`, for measurable sets `s, t`.
* `IndepSet s t κ μ ↔ ∀ᵐ a ∂μ, κ a (s ∩ t) = κ a s * κ a t`,
* `IndepSet s t κ μ ↔ IndepSets {s} {t} κ μ`.
-/

variable {_mα : MeasurableSpace α}

/-
**ProbabilityTheory.Kernel.iIndepSet_iff_iIndepSets_singleton** 是 Mathlib 中的一个定理
，位于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：iIndepSet_iff_iIndepSets_singleton {_mΩ : MeasurableSpace Ω} {κ : Kernel α
 Ω} {μ : Measure α} {f : ι -> Set Ω} (hf : forall i, MeasurableSet (f i)) : iInd
epSet f κ μ ↔ iIndepSets (fun i => {f i}) κ μ
参数：hf : forall i, MeasurableSet (f i)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndep.iIndepSets`：∀ {α : Type u_1} {Ω : Type u
_2} {ι : Type u_3} {_mα : MeasurableSpace α} {_mΩ : MeasurableSpace Ω}   {κ : Pr
obabilityTheory.Kernel α Ω} {μ :…
· 使用定理 `ProbabilityTheory.Kernel.iIndepSets.iIndep`：∀ {α : Type u_1} {Ω : Type u
_2} {ι : Type u_3} {_mα : MeasurableSpace α} {_mΩ : MeasurableSpace Ω}   {κ : Pr
obabilityTheory.Kernel α Ω} {μ :…
· 使用定理 `MeasurableSpace.generateFrom_le`：generateFrom_le {s : Set (Set α)} {m : 
MeasurableSpace α} (h : forall t in s, MeasurableSet[m] t) : generateFrom s <= m
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsPiSystem.singleton`：IsPiSystem.singleton (S : Set α) : IsPiSystem ({S}
 : Set (Set α))
-/
theorem iIndepSet_iff_iIndepSets_singleton {_mΩ : MeasurableSpace Ω} {κ : Kernel α Ω}
    {μ : Measure α} {f : ι → Set Ω} (hf : ∀ i, MeasurableSet (f i)) :
    iIndepSet f κ μ ↔ iIndepSets (fun i ↦ {f i}) κ μ :=
  ⟨iIndep.iIndepSets fun _ ↦ rfl,
    iIndepSets.iIndep _ (fun i ↦ generateFrom_le <| by rintro t (rfl : t = _); exact hf _) _
      (fun _ ↦ IsPiSystem.singleton _) fun _ ↦ rfl⟩
/-
**ProbabilityTheory.Kernel.iIndepSet.meas_biInter** 是 Mathlib 中的一个定理，位于命名空间 `Pro
babilityTheory.Kernel.iIndepSet`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {
_mΩ : MeasurableSpace Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ : MeasureTheory
.Measure α} {f : ι → Set Ω},   ProbabilityTheory.Kernel.iIndepSet f κ μ →     ∀ 
(s : Finset ι), ∀ᵐ (a : α) ∂μ, (κ a) (⋂ i ∈ s, f i) = ∏ i ∈ s, (κ a) (f i)
参数：s : Finset ι；a : α；κ a；⋂ i ∈ s, f i；κ a；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndep.iIndepSets`：∀ {α : Type u_1} {Ω : Type u
_2} {ι : Type u_3} {_mα : MeasurableSpace α} {_mΩ : MeasurableSpace Ω}   {κ : Pr
obabilityTheory.Kernel α Ω} {μ :…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem iIndepSet.meas_biInter {_mΩ : MeasurableSpace Ω} {κ : Kernel α Ω}
    {μ : Measure α} {f : ι → Set Ω} (h : iIndepSet f κ μ) (s : Finset ι) :
    ∀ᵐ a ∂μ, κ a (⋂ i ∈ s, f i) = ∏ i ∈ s, κ a (f i) :=
  iIndep.iIndepSets (fun _ ↦ rfl) h _ (by simp)
/-
**ProbabilityTheory.Kernel.iIndepSet_iff_meas_biInter** 是 Mathlib 中的一个定理，位于命名空间 
`ProbabilityTheory.Kernel`。
形式化陈述：iIndepSet_iff_meas_biInter {_mΩ : MeasurableSpace Ω} {κ : Kernel α Ω} {μ :
 Measure α} {f : ι -> Set Ω} (hf : forall i, MeasurableSet (f i)) : iIndepSet f 
κ μ ↔ forall s, forallᵐ a ∂μ, κ a (⋂ i in s, f i) = ∏ i in s, κ a (f i)
参数：hf : forall i, MeasurableSet (f i)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.Kernel.iIndepSet_iff_iIndepSets_singleton`：iIndepSet_i
ff_iIndepSets_singleton {_mΩ : MeasurableSpace Ω} {κ : Kernel α Ω} {μ : Measure 
α} {f : ι -> Set Ω} (hf : forall i, MeasurableSet…
· 使用定理 `ProbabilityTheory.Kernel.iIndepSets_singleton_iff`：iIndepSets_singleton_
iff {s : ι -> Set Ω} {_mΩ : MeasurableSpace Ω} {κ : Kernel α Ω} {μ : Measure α} 
: iIndepSets (fun i => {s i}) κ μ ↔ for…
-/
theorem iIndepSet_iff_meas_biInter {_mΩ : MeasurableSpace Ω} {κ : Kernel α Ω}
    {μ : Measure α} {f : ι → Set Ω} (hf : ∀ i, MeasurableSet (f i)) :
    iIndepSet f κ μ ↔ ∀ s, ∀ᵐ a ∂μ, κ a (⋂ i ∈ s, f i) = ∏ i ∈ s, κ a (f i) :=
  (iIndepSet_iff_iIndepSets_singleton hf).trans iIndepSets_singleton_iff
/-
**ProbabilityTheory.Kernel.iIndepSets.iIndepSet_of_mem** 是 Mathlib 中的一个定理，位于命名空间
 `ProbabilityTheory.Kernel.iIndepSets`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {
_mΩ : MeasurableSpace Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ : MeasureTheory
.Measure α} {π : ι → Set (Set Ω)} {f : ι → Set Ω},   (∀ (i : ι), f i ∈ π i) →   
  (∀ (i : ι), MeasurableSet (f i)) →       ProbabilityTheory.Kernel.iIndepSets π
 κ μ → ProbabilityTheory.Kernel.iIndepSet f κ μ
参数：Set Ω；∀ (i : ι), f i ∈ π i；∀ (i : ι), MeasurableSet (f i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.Kernel.iIndepSet_iff_meas_biInter`：iIndepSet_iff_meas_
biInter {_mΩ : MeasurableSpace Ω} {κ : Kernel α Ω} {μ : Measure α} {f : ι -> Set
 Ω} (hf : forall i, MeasurableSet (f i)) …
· 使用定理 `ProbabilityTheory.Kernel.iIndepSets.meas_biInter`：∀ {α : Type u_1} {Ω : 
Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {_mΩ : MeasurableSpace Ω}   {
κ : ProbabilityTheory.Kernel α Ω} {μ :…
-/
theorem iIndepSets.iIndepSet_of_mem {_mΩ : MeasurableSpace Ω} {κ : Kernel α Ω}
    {μ : Measure α} {π : ι → Set (Set Ω)} {f : ι → Set Ω}
    (hfπ : ∀ i, f i ∈ π i) (hf : ∀ i, MeasurableSet (f i)) (hπ : iIndepSets π κ μ) :
    iIndepSet f κ μ :=
  (iIndepSet_iff_meas_biInter hf).2 fun _t ↦ hπ.meas_biInter _ fun _i _ ↦ hfπ _

variable {s t : Set Ω} (S T : Set (Set Ω))
/-
**ProbabilityTheory.Kernel.indepSet_iff_indepSets_singleton** 是 Mathlib 中的一个定理，位
于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：indepSet_iff_indepSets_singleton {m0 : MeasurableSpace Ω} (hs_meas : Measu
rableSet s) (ht_meas : MeasurableSet t) (κ : Kernel α Ω) (μ : Measure α) [IsZero
OrMarkovKernel κ] : IndepSet s t κ μ ↔ IndepSets {s} {t} κ μ
参数：hs_meas : MeasurableSet s；ht_meas : MeasurableSet t；κ : Kernel α Ω；μ : Measur
e α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.Indep.indepSets`：∀ {α : Type u_1} {Ω : Type u_2
} {_mα : MeasurableSpace α} {_mΩ : MeasurableSpace Ω} {κ : ProbabilityTheory.Ker
nel α Ω}   {μ : MeasureTheory.…
· 使用定理 `ProbabilityTheory.Kernel.IndepSets.indep`：∀ {α : Type u_1} {Ω : Type u_2
} {_mα : MeasurableSpace α} {m1 m2 m : MeasurableSpace Ω}   {κ : ProbabilityTheo
ry.Kernel α Ω} {μ : MeasureThe…
· 使用定理 `MeasurableSpace.generateFrom_le`：generateFrom_le {s : Set (Set α)} {m : 
MeasurableSpace α} (h : forall t in s, MeasurableSet[m] t) : generateFrom s <= m
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `IsPiSystem.singleton`：IsPiSystem.singleton (S : Set α) : IsPiSystem ({S}
 : Set (Set α))
-/
theorem indepSet_iff_indepSets_singleton {m0 : MeasurableSpace Ω} (hs_meas : MeasurableSet s)
    (ht_meas : MeasurableSet t) (κ : Kernel α Ω) (μ : Measure α)
    [IsZeroOrMarkovKernel κ] :
    IndepSet s t κ μ ↔ IndepSets {s} {t} κ μ :=
  ⟨Indep.indepSets, fun h =>
    IndepSets.indep
      (generateFrom_le fun u hu => by rwa [Set.mem_singleton_iff.mp hu])
      (generateFrom_le fun u hu => by rwa [Set.mem_singleton_iff.mp hu])
      (IsPiSystem.singleton s) (IsPiSystem.singleton t) rfl rfl h⟩
/-
**ProbabilityTheory.Kernel.indepSet_iff_measure_inter_eq_mul** 是 Mathlib 中的一个定理，
位于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：indepSet_iff_measure_inter_eq_mul {_m0 : MeasurableSpace Ω} (hs_meas : Mea
surableSet s) (ht_meas : MeasurableSet t) (κ : Kernel α Ω) (μ : Measure α) [IsZe
roOrMarkovKernel κ] : IndepSet s t κ μ ↔ forallᵐ a ∂μ, κ a (s inter t) = κ a s *
 κ a t
参数：hs_meas : MeasurableSet s；ht_meas : MeasurableSet t；κ : Kernel α Ω；μ : Measur
e α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.Kernel.indepSet_iff_indepSets_singleton`：indepSet_iff_
indepSets_singleton {m0 : MeasurableSpace Ω} (hs_meas : MeasurableSet s) (ht_mea
s : MeasurableSet t) (κ : Kernel α Ω) (μ : Meas…
· 使用定理 `ProbabilityTheory.Kernel.indepSets_singleton_iff`：indepSets_singleton_if
f {s t : Set Ω} {_mΩ : MeasurableSpace Ω} {κ : Kernel α Ω} {μ : Measure α} : Ind
epSets {s} {t} κ μ ↔ forallᵐ a ∂μ, κ a…
-/
theorem indepSet_iff_measure_inter_eq_mul {_m0 : MeasurableSpace Ω} (hs_meas : MeasurableSet s)
    (ht_meas : MeasurableSet t) (κ : Kernel α Ω) (μ : Measure α)
    [IsZeroOrMarkovKernel κ] :
    IndepSet s t κ μ ↔ ∀ᵐ a ∂μ, κ a (s ∩ t) = κ a s * κ a t :=
  (indepSet_iff_indepSets_singleton hs_meas ht_meas κ μ).trans indepSets_singleton_iff
/-
**ProbabilityTheory.Kernel.IndepSet.measure_inter_eq_mul** 是 Mathlib 中的一个定理，位于命名
空间 `ProbabilityTheory.Kernel.IndepSet`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {_mα : MeasurableSpace α} {s t : Set Ω} {_
m0 : MeasurableSpace Ω}   (κ : ProbabilityTheory.Kernel α Ω) (μ : MeasureTheory.
Measure α),   ProbabilityTheory.Kernel.IndepSet s t κ μ → ∀ᵐ (a : α) ∂μ, (κ a) (
s ∩ t) = (κ a) s * (κ a) t
参数：κ : ProbabilityTheory.Kernel α Ω；μ : MeasureTheory.Measure α；a : α；κ a；s ∩ t；
κ a；κ a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.Indep.indepSets`：∀ {α : Type u_1} {Ω : Type u_2
} {_mα : MeasurableSpace α} {_mΩ : MeasurableSpace Ω} {κ : ProbabilityTheory.Ker
nel α Ω}   {μ : MeasureTheory.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IndepSet.measure_inter_eq_mul {_m0 : MeasurableSpace Ω} (κ : Kernel α Ω) (μ : Measure α)
    (h : IndepSet s t κ μ) : ∀ᵐ a ∂μ, κ a (s ∩ t) = κ a s * κ a t :=
  Indep.indepSets h _ _ (by simp) (by simp)
/-
**ProbabilityTheory.Kernel.IndepSets.indepSet_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `
ProbabilityTheory.Kernel.IndepSets`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {_mα : MeasurableSpace α} {s t : Set Ω} (S
 T : Set (Set Ω)) {_m0 : MeasurableSpace Ω},   s ∈ S →     t ∈ T →       Measura
bleSet s →         MeasurableSet t →           ∀ (κ : ProbabilityTheory.Kernel α
 Ω) (μ : MeasureTheory.Measure α) [ProbabilityTheory.IsZeroOrMarkovKernel κ],   
          ProbabilityTheory.Kernel.IndepSets S T κ μ → ProbabilityTheory.Kernel.
IndepSet s t κ μ
参数：S T : Set (Set Ω)；κ : ProbabilityTheory.Kernel α Ω；μ : MeasureTheory.Measure 
α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.Kernel.indepSet_iff_measure_inter_eq_mul`：indepSet_iff
_measure_inter_eq_mul {_m0 : MeasurableSpace Ω} (hs_meas : MeasurableSet s) (ht_
meas : MeasurableSet t) (κ : Kernel α Ω) (μ : Me…
-/
theorem IndepSets.indepSet_of_mem {_m0 : MeasurableSpace Ω} (hs : s ∈ S) (ht : t ∈ T)
    (hs_meas : MeasurableSet s) (ht_meas : MeasurableSet t)
    (κ : Kernel α Ω) (μ : Measure α) [IsZeroOrMarkovKernel κ]
    (h_indep : IndepSets S T κ μ) :
    IndepSet s t κ μ :=
  (indepSet_iff_measure_inter_eq_mul hs_meas ht_meas κ μ).mpr (h_indep s t hs ht)
/-
**ProbabilityTheory.Kernel.Indep.indepSet_of_measurableSet** 是 Mathlib 中的一个定理，位于
命名空间 `ProbabilityTheory.Kernel.Indep`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {_mα : MeasurableSpace α} {m₁ m₂ x : Measu
rableSpace Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ : MeasureTheory.Measure α}
,   ProbabilityTheory.Kernel.Indep m₁ m₂ κ μ →     ∀ {s t : Set Ω}, MeasurableSe
t s → MeasurableSet t → ProbabilityTheory.Kernel.IndepSet s t κ μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSpace.generateFrom_induction`：generateFrom_induction (C : Set 
(Set α)) (p : forall s : Set α, MeasurableSet[generateFrom C] s -> Prop) (hC : f
orall t in C, forall ht, p t…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasurableSet.empty`：MeasurableSet.empty [MeasurableSpace α] : Measurabl
eSet (∅ : Set α)
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `MeasurableSet.iUnion`：∀ {α : Type u_1} {ι : Sort u_6} {m : MeasurableSpa
ce α} [Countable ι] ⦃f : ι → Set α⦄,   (∀ (b : ι), MeasurableSet (f b)) → Measur
ableSet (⋃…
· 使用定理 `instCountableNat`：Countable ℕ
-/
theorem Indep.indepSet_of_measurableSet {m₁ m₂ _ : MeasurableSpace Ω} {κ : Kernel α Ω}
    {μ : Measure α}
    (h_indep : Indep m₁ m₂ κ μ) {s t : Set Ω} (hs : MeasurableSet[m₁] s)
    (ht : MeasurableSet[m₂] t) :
    IndepSet s t κ μ := by
  refine fun s' t' hs' ht' => h_indep s' t' ?_ ?_
  · induction s', hs' using generateFrom_induction with
    | hC t ht => exact ht ▸ hs
    | empty => exact @MeasurableSet.empty _ m₁
    | compl u _ hu => exact hu.compl
    | iUnion f _ hf => exact .iUnion hf
  · induction t', ht' using generateFrom_induction with
    | hC s hs => exact hs ▸ ht
    | empty => exact @MeasurableSet.empty _ m₂
    | compl u _ hu => exact hu.compl
    | iUnion f _ hf => exact .iUnion hf
/-
**ProbabilityTheory.Kernel.indep_iff_forall_indepSet** 是 Mathlib 中的一个定理，位于命名空间 `
ProbabilityTheory.Kernel`。
形式化陈述：indep_iff_forall_indepSet (m₁ m₂ : MeasurableSpace Ω) {_m0 : MeasurableSpa
ce Ω} (κ : Kernel α Ω) (μ : Measure α) : Indep m₁ m₂ κ μ ↔ forall s t, Measurabl
eSet[m₁] s -> MeasurableSet[m₂] t -> IndepSet s t κ μ
参数：m₁ m₂ : MeasurableSpace Ω；κ : Kernel α Ω；μ : Measure α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.Indep.indepSet_of_measurableSet`：∀ {α : Type u_
1} {Ω : Type u_2} {_mα : MeasurableSpace α} {m₁ m₂ x : MeasurableSpace Ω}   {κ :
 ProbabilityTheory.Kernel α Ω} {μ : MeasureThe…
· 使用定理 `MeasurableSpace.measurableSet_generateFrom`：measurableSet_generateFrom {
s : Set (Set α)} {t : Set α} (ht : t in s) : MeasurableSet[generateFrom s] t
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
-/
theorem indep_iff_forall_indepSet (m₁ m₂ : MeasurableSpace Ω) {_m0 : MeasurableSpace Ω}
    (κ : Kernel α Ω) (μ : Measure α) :
    Indep m₁ m₂ κ μ ↔ ∀ s t, MeasurableSet[m₁] s → MeasurableSet[m₂] t → IndepSet s t κ μ :=
  ⟨fun h => fun _s _t hs ht => h.indepSet_of_measurableSet hs ht, fun h s t hs ht =>
    h s t hs ht s t (measurableSet_generateFrom (Set.mem_singleton s))
      (measurableSet_generateFrom (Set.mem_singleton t))⟩

end IndepSet

end ProbabilityTheory.Kernel

