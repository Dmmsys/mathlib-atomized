/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Independence.Kernel.IndepFun
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Group.Convolution

/-!
# Independence of sets of sets and measure spaces (σ-algebras)

* A family of sets of sets `π : ι → Set (Set Ω)` is independent with respect to a measure `μ` if for
  any finite set of indices `s = {i_1, ..., i_n}`, for any sets `f i_1 ∈ π i_1, ..., f i_n ∈ π i_n`,
  `μ (⋂ i in s, f i) = ∏ i ∈ s, μ (f i)`. It will be used for families of π-systems.
* A family of measurable space structures (i.e. of σ-algebras) is independent with respect to a
  measure `μ` (typically defined on a finer σ-algebra) if the family of sets of measurable sets they
  define is independent. I.e., `m : ι → MeasurableSpace Ω` is independent with respect to a
  measure `μ` if for any finite set of indices `s = {i_1, ..., i_n}`, for any sets
  `f i_1 ∈ m i_1, ..., f i_n ∈ m i_n`, then `μ (⋂ i in s, f i) = ∏ i ∈ s, μ (f i)`.
* Independence of sets (or events in probabilistic parlance) is defined as independence of the
  measurable space structures they generate: a set `s` generates the measurable space structure with
  measurable sets `∅, s, sᶜ, univ`.
* Independence of functions (or random variables) is also defined as independence of the measurable
  space structures they generate: a function `f` for which we have a measurable space `m` on the
  codomain generates `MeasurableSpace.comap f m`.

## Main statements

* `iIndepSets.iIndep`: if π-systems are independent as sets of sets, then the
  measurable space structures they generate are independent.
* `IndepSets.indep`: variant with two π-systems.

## Notation

* `X ⟂ᵢ[μ] Y` for `IndepFun X Y μ`, independence of two random variables.
* `X ⟂ᵢ Y` for `IndepFun X Y volume`.

These notations are scoped in the `ProbabilityTheory` namespace.

## Implementation notes

The definitions of independence in this file are a particular case of independence with respect to a
kernel and a measure, as defined in the file `Kernel.lean`.

We provide four definitions of independence:
* `iIndepSets`: independence of a family of sets of sets `pi : ι → Set (Set Ω)`. This is meant to
  be used with π-systems.
* `iIndep`: independence of a family of measurable space structures `m : ι → MeasurableSpace Ω`,
* `iIndepSet`: independence of a family of sets `s : ι → Set Ω`,
* `iIndepFun`: independence of a family of functions. For measurable spaces
  `m : Π (i : ι), MeasurableSpace (β i)`, we consider functions `f : Π (i : ι), Ω → β i`.

Additionally, we provide four corresponding statements for two measurable space structures (resp.
sets of sets, sets, functions) instead of a family. These properties are denoted by the same names
as for a family, but without the starting `i`, for example `IndepFun` is the version of `iIndepFun`
for two functions.

The definition of independence for `iIndepSets` uses finite sets (`Finset`). See
`ProbabilityTheory.Kernel.iIndepSets`. An alternative and equivalent way of defining independence
would have been to use countable sets.

Most of the definitions and lemmas in this file list all variables instead of using the `variable`
keyword at the beginning of a section, for example
`lemma Indep.symm {Ω} {m₁ m₂ : MeasurableSpace Ω} {_mΩ : MeasurableSpace Ω} {μ : measure Ω} ...` .
This is intentional, to be able to control the order of the `MeasurableSpace` variables. Indeed
when defining `μ` in the example above, the measurable space used is the last one defined, here
`{_mΩ : MeasurableSpace Ω}`, and not `m₁` or `m₂`.

## References

* Williams, David. Probability with martingales. Cambridge university press, 1991.
  Part A, Chapter 4.
-/

@[expose] public section

assert_not_exists MeasureTheory.Integrable

open MeasureTheory MeasurableSpace Set

open scoped MeasureTheory ENNReal

namespace ProbabilityTheory

variable {Ω ι β γ : Type*} {κ : ι → Type*}

section Definitions

/-- A family of sets of sets `π : ι → Set (Set Ω)` is independent with respect to a measure `μ` if
for any finite set of indices `s = {i_1, ..., i_n}`, for any sets
`f i_1 ∈ π i_1, ..., f i_n ∈ π i_n`, then `μ (⋂ i in s, f i) = ∏ i ∈ s, μ (f i) `.
It will be used for families of π-systems. -/
/-
**ProbabilityTheory.iIndepSets** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory`。
形式化陈述：iIndepSets {_mΩ : MeasurableSpace Ω} (π : ι -> Set (Set Ω)) (μ : Measure Ω
参数：π : ι -> Set (Set Ω)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family of sets of sets `π : ι → Set (Set Ω)` is independent with respect to a 
measure `μ` if
for any finite set of indices `s = {i_1, ..., i_n}`, for any sets
`f i_1 ∈ π i_1, ..., f i_n ∈ π i_n`, then `μ (⋂ i in s, f i) = ∏ i ∈ s, μ (f i) 
`.
It will be used for families of π-systems.
-/
def iIndepSets {_mΩ : MeasurableSpace Ω}
    (π : ι → Set (Set Ω)) (μ : Measure Ω := by volume_tac) : Prop :=
  Kernel.iIndepSets π (Kernel.const Unit μ) (Measure.dirac () : Measure Unit)

/-- Two sets of sets `s₁, s₂` are independent with respect to a measure `μ` if for any sets
`t₁ ∈ p₁, t₂ ∈ s₂`, then `μ (t₁ ∩ t₂) = μ (t₁) * μ (t₂)` -/
/-
**ProbabilityTheory.IndepSets** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory`。
形式化陈述：IndepSets {_mΩ : MeasurableSpace Ω} (s1 s2 : Set (Set Ω)) (μ : Measure Ω
参数：s1 s2 : Set (Set Ω)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two sets of sets `s₁, s₂` are independent with respect to a measure `μ` if for a
ny sets
`t₁ ∈ p₁, t₂ ∈ s₂`, then `μ (t₁ ∩ t₂) = μ (t₁) * μ (t₂)`
-/
def IndepSets {_mΩ : MeasurableSpace Ω}
    (s1 s2 : Set (Set Ω)) (μ : Measure Ω := by volume_tac) : Prop :=
  Kernel.IndepSets s1 s2 (Kernel.const Unit μ) (Measure.dirac () : Measure Unit)

/-- A family of measurable space structures (i.e. of σ-algebras) is independent with respect to a
measure `μ` (typically defined on a finer σ-algebra) if the family of sets of measurable sets they
define is independent. `m : ι → MeasurableSpace Ω` is independent with respect to measure `μ` if
for any finite set of indices `s = {i_1, ..., i_n}`, for any sets
`f i_1 ∈ m i_1, ..., f i_n ∈ m i_n`, then `μ (⋂ i in s, f i) = ∏ i ∈ s, μ (f i)`. -/
/-
**ProbabilityTheory.iIndep** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory`。
形式化陈述：iIndep (m : ι -> MeasurableSpace Ω) {_mΩ : MeasurableSpace Ω} (μ : Measure
 Ω
参数：m : ι -> MeasurableSpace Ω。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family of measurable space structures (i.e. of σ-algebras) is independent with
 respect to a
measure `μ` (typically defined on a finer σ-algebra) if the family of sets of me
asurable sets they
define is independent. `m : ι → MeasurableSpace Ω` is independent with respect t
o measure `μ` if
for any finite set of indices `s = {i_1, ..., i_n}`, for any sets
`f i_1 ∈ m i_1, ..., f i_n ∈ m i_n`, then `μ (⋂ i in s, f i) = ∏ i ∈ s, μ (f i)`
.
-/
def iIndep (m : ι → MeasurableSpace Ω) {_mΩ : MeasurableSpace Ω} (μ : Measure Ω := by volume_tac) :
    Prop :=
  Kernel.iIndep m (Kernel.const Unit μ) (Measure.dirac () : Measure Unit)

/-- Two measurable space structures (or σ-algebras) `m₁, m₂` are independent with respect to a
measure `μ` (defined on a third σ-algebra) if for any sets `t₁ ∈ m₁, t₂ ∈ m₂`,
`μ (t₁ ∩ t₂) = μ (t₁) * μ (t₂)` -/
/-
**ProbabilityTheory.Indep** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory`。
形式化陈述：Indep (m₁ m₂ : MeasurableSpace Ω) {_mΩ : MeasurableSpace Ω} (μ : Measure Ω
参数：m₁ m₂ : MeasurableSpace Ω。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two measurable space structures (or σ-algebras) `m₁, m₂` are independent with re
spect to a
measure `μ` (defined on a third σ-algebra) if for any sets `t₁ ∈ m₁, t₂ ∈ m₂`,
`μ (t₁ ∩ t₂) = μ (t₁) * μ (t₂)`
-/
def Indep (m₁ m₂ : MeasurableSpace Ω)
    {_mΩ : MeasurableSpace Ω} (μ : Measure Ω := by volume_tac) : Prop :=
  Kernel.Indep m₁ m₂ (Kernel.const Unit μ) (Measure.dirac () : Measure Unit)

/-- A family of sets is independent if the family of measurable space structures they generate is
independent. For a set `s`, the generated measurable space has measurable sets `∅, s, sᶜ, univ`. -/
/-
**ProbabilityTheory.iIndepSet** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory`。
形式化陈述：iIndepSet {_mΩ : MeasurableSpace Ω} (s : ι -> Set Ω) (μ : Measure Ω
参数：s : ι -> Set Ω。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family of sets is independent if the family of measurable space structures the
y generate is
independent. For a set `s`, the generated measurable space has measurable sets `
∅, s, sᶜ, univ`.
-/
def iIndepSet {_mΩ : MeasurableSpace Ω} (s : ι → Set Ω) (μ : Measure Ω := by volume_tac) : Prop :=
  Kernel.iIndepSet s (Kernel.const Unit μ) (Measure.dirac () : Measure Unit)

/-- Two sets are independent if the two measurable space structures they generate are independent.
For a set `s`, the generated measurable space structure has measurable sets `∅, s, sᶜ, univ`. -/
/-
**ProbabilityTheory.IndepSet** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory`。
形式化陈述：IndepSet {_mΩ : MeasurableSpace Ω} (s t : Set Ω) (μ : Measure Ω
参数：s t : Set Ω。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two sets are independent if the two measurable space structures they generate ar
e independent.
For a set `s`, the generated measurable space structure has measurable sets `∅, 
s, sᶜ, univ`.
-/
def IndepSet {_mΩ : MeasurableSpace Ω} (s t : Set Ω) (μ : Measure Ω := by volume_tac) : Prop :=
  Kernel.IndepSet s t (Kernel.const Unit μ) (Measure.dirac () : Measure Unit)

/-- A family of functions defined on the same space `Ω` and taking values in possibly different
spaces, each with a measurable space structure, is independent if the family of measurable space
structures they generate on `Ω` is independent. For a function `g` with codomain having measurable
space structure `m`, the generated measurable space structure is `MeasurableSpace.comap g m`. -/
/-
**ProbabilityTheory.iIndepFun** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory`。
形式化陈述：iIndepFun {_mΩ : MeasurableSpace Ω} {β : ι -> Type*} [m : forall x : ι, Me
asurableSpace (β x)] (f : forall x : ι, Ω -> β x) (μ : Measure Ω
参数：β x；f : forall x : ι, Ω -> β x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family of functions defined on the same space `Ω` and taking values in possibl
y different
spaces, each with a measurable space structure, is independent if the family of 
measurable space
structures they generate on `Ω` is independent. For a function `g` with codomain
 having measurable
space structure `m`, the generated measurable space structure is `MeasurableSpac
e.comap g m`.
-/
def iIndepFun {_mΩ : MeasurableSpace Ω} {β : ι → Type*} [m : ∀ x : ι, MeasurableSpace (β x)]
    (f : ∀ x : ι, Ω → β x) (μ : Measure Ω := by volume_tac) : Prop :=
  Kernel.iIndepFun f (Kernel.const Unit μ) (Measure.dirac () : Measure Unit)

/-- Two functions are independent if the two measurable space structures they generate are
independent. For a function `f` with codomain having measurable space structure `m`, the generated
measurable space structure is `MeasurableSpace.comap f m`.
We use the notation `f ⟂ᵢ[μ] g` for `IndepFun f g μ` (scoped in `ProbabilityTheory`). -/
/-
**ProbabilityTheory.IndepFun** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory`。
形式化陈述：IndepFun {β γ} {_mΩ : MeasurableSpace Ω} [MeasurableSpace β] [MeasurableSp
ace γ] (f : Ω -> β) (g : Ω -> γ) (μ : Measure Ω
参数：f : Ω -> β；g : Ω -> γ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two functions are independent if the two measurable space structures they genera
te are
independent. For a function `f` with codomain having measurable space structure 
`m`, the generated
measurable space structure is `MeasurableSpace.comap f m`.
We use the notation `f ⟂ᵢ[μ] g` for `IndepFun f g μ` (scoped in `ProbabilityTheo
ry`).
-/
def IndepFun {β γ} {_mΩ : MeasurableSpace Ω} [MeasurableSpace β] [MeasurableSpace γ]
    (f : Ω → β) (g : Ω → γ) (μ : Measure Ω := by volume_tac) : Prop :=
  Kernel.IndepFun f g (Kernel.const Unit μ) (Measure.dirac () : Measure Unit)

end Definitions

@[inherit_doc ProbabilityTheory.IndepFun]
scoped[ProbabilityTheory] notation3 X:50 " ⟂ᵢ[" μ "] " Y:50 => ProbabilityTheory.IndepFun X Y μ

@[inherit_doc ProbabilityTheory.IndepFun]
scoped[ProbabilityTheory] notation3 X:50 " ⟂ᵢ " Y:50 => ProbabilityTheory.IndepFun X Y volume

section Definition_lemmas
variable {π : ι → Set (Set Ω)} {m : ι → MeasurableSpace Ω} {_ : MeasurableSpace Ω} {μ : Measure Ω}
  {S : Finset ι} {s : ι → Set Ω} {ι' : Type*} {g : ι' → ι}

/-
**ProbabilityTheory.iIndepSets_iff** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`
。
形式化陈述：iIndepSets_iff (π : ι -> Set (Set Ω)) (μ : Measure Ω) : iIndepSets π μ ↔ f
orall (s : Finset ι) {f : ι -> Set Ω} (_H : forall i, i in s -> f i in π i), μ (
⋂ i in s, f i) = ∏ i in s, μ (f i)
参数：π : ι -> Set (Set Ω)；μ : Measure Ω。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `MeasureTheory.ae_dirac_eq`：ae_dirac_eq [MeasurableSingletonClass α] (a :
 α) : ae (dirac a) = pure a
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `standardBorelSpace_of_discreteMeasurableSpace`：∀ {α : Type u_1} [inst : 
MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α], StandardBorelSpace
 α
· 使用定理 `instDiscreteMeasurableSpace`：∀ {α : Type u_1}, DiscreteMeasurableSpace α
· 使用定理 `instCountablePUnit`：Countable PUnit.{u}
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma iIndepSets_iff (π : ι → Set (Set Ω)) (μ : Measure Ω) :
    iIndepSets π μ ↔ ∀ (s : Finset ι) {f : ι → Set Ω} (_H : ∀ i, i ∈ s → f i ∈ π i),
      μ (⋂ i ∈ s, f i) = ∏ i ∈ s, μ (f i) := by
  simp only [iIndepSets, Kernel.iIndepSets, ae_dirac_eq, Filter.eventually_pure, Kernel.const_apply]
/-
**ProbabilityTheory.iIndepSets.meas_biInter** 是 Mathlib 中的一个定理，位于命名空间 `Probabili
tyTheory.iIndepSets`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {π : ι → Set (Set Ω)} {x : MeasurableSpace
 Ω} {μ : MeasureTheory.Measure Ω},   ProbabilityTheory.iIndepSets π μ →     ∀ (s
 : Finset ι) {f : ι → Set Ω}, (∀ i ∈ s, f i ∈ π i) → μ (⋂ i ∈ s, f i) = ∏ i ∈ s,
 μ (f i)
参数：Set Ω；s : Finset ι；∀ i ∈ s, f i ∈ π i；⋂ i ∈ s, f i；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `ProbabilityTheory.iIndepSets_iff`：iIndepSets_iff (π : ι -> Set (Set Ω)) 
(μ : Measure Ω) : iIndepSets π μ ↔ forall (s : Finset ι) {f : ι -> Set Ω} (_H : 
forall i, i in s -> f …
-/
lemma iIndepSets.meas_biInter (h : iIndepSets π μ) (s : Finset ι) {f : ι → Set Ω}
    (hf : ∀ i, i ∈ s → f i ∈ π i) : μ (⋂ i ∈ s, f i) = ∏ i ∈ s, μ (f i) :=
  (iIndepSets_iff _ _).1 h s hf
/-
**ProbabilityTheory.iIndepSets.isProbabilityMeasure** 是 Mathlib 中的一个定理，位于命名空间 `P
robabilityTheory.iIndepSets`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {π : ι → Set (Set Ω)} {x : MeasurableSpace
 Ω} {μ : MeasureTheory.Measure Ω},   ProbabilityTheory.iIndepSets π μ → MeasureT
heory.IsProbabilityMeasure μ
参数：Set Ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
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
· 使用定理 `MeasureTheory.ae_dirac_eq`：ae_dirac_eq [MeasurableSingletonClass α] (a :
 α) : ae (dirac a) = pure a
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `standardBorelSpace_of_discreteMeasurableSpace`：∀ {α : Type u_1} [inst : 
MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α], StandardBorelSpace
 α
· 使用定理 `instDiscreteMeasurableSpace`：∀ {α : Type u_1}, DiscreteMeasurableSpace α
· 使用定理 `instCountablePUnit`：Countable PUnit.{u}
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
lemma iIndepSets.isProbabilityMeasure (h : iIndepSets π μ) : IsProbabilityMeasure μ :=
  ⟨by simpa using h ∅ (f := fun _ ↦ univ)⟩
/-
**ProbabilityTheory.iIndepSets.meas_iInter** 是 Mathlib 中的一个定理，位于命名空间 `Probabilit
yTheory.iIndepSets`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {π : ι → Set (Set Ω)} {x : MeasurableSpace
 Ω} {μ : MeasureTheory.Measure Ω}   {s : ι → Set Ω} [inst : Fintype ι],   Probab
ilityTheory.iIndepSets π μ → (∀ (i : ι), s i ∈ π i) → μ (⋂ i, s i) = ∏ i, μ (s i
)
参数：Set Ω；∀ (i : ι), s i ∈ π i；⋂ i, s i；s i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.iIndepSets.meas_biInter`：∀ {Ω : Type u_1} {ι : Type u_
2} {π : ι → Set (Set Ω)} {x : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω}, 
  ProbabilityTheory.iIndepSets …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iInter_true`：iInter_true {s : True -> Set α} : iInter s = s trivial
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma iIndepSets.meas_iInter [Fintype ι] (h : iIndepSets π μ) (hs : ∀ i, s i ∈ π i) :
    μ (⋂ i, s i) = ∏ i, μ (s i) := by simp [← h.meas_biInter _ fun _i _ ↦ hs _]
/-
**ProbabilityTheory.IndepSets_iff** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：IndepSets_iff (s1 s2 : Set (Set Ω)) (μ : Measure Ω) : IndepSets s1 s2 μ ↔ 
forall t1 t2 : Set Ω, t1 in s1 -> t2 in s2 -> (μ (t1 inter t2) = μ t1 * μ t2)
参数：s1 s2 : Set (Set Ω)；μ : Measure Ω。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `MeasureTheory.ae_dirac_eq`：ae_dirac_eq [MeasurableSingletonClass α] (a :
 α) : ae (dirac a) = pure a
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `standardBorelSpace_of_discreteMeasurableSpace`：∀ {α : Type u_1} [inst : 
MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α], StandardBorelSpace
 α
· 使用定理 `instDiscreteMeasurableSpace`：∀ {α : Type u_1}, DiscreteMeasurableSpace α
· 使用定理 `instCountablePUnit`：Countable PUnit.{u}
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma IndepSets_iff (s1 s2 : Set (Set Ω)) (μ : Measure Ω) :
    IndepSets s1 s2 μ ↔ ∀ t1 t2 : Set Ω, t1 ∈ s1 → t2 ∈ s2 → (μ (t1 ∩ t2) = μ t1 * μ t2) := by
  simp only [IndepSets, Kernel.IndepSets, ae_dirac_eq, Filter.eventually_pure, Kernel.const_apply]
/-
**ProbabilityTheory.iIndep_iff_iIndepSets** 是 Mathlib 中的一个引理，位于命名空间 `Probability
Theory`。
形式化陈述：iIndep_iff_iIndepSets (m : ι -> MeasurableSpace Ω) {_mΩ : MeasurableSpace 
Ω} (μ : Measure Ω) : iIndep m μ ↔ iIndepSets (fun x => {s | MeasurableSet[m x] s
}) μ
参数：m : ι -> MeasurableSpace Ω；μ : Measure Ω。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma iIndep_iff_iIndepSets (m : ι → MeasurableSpace Ω) {_mΩ : MeasurableSpace Ω} (μ : Measure Ω) :
    iIndep m μ ↔ iIndepSets (fun x ↦ {s | MeasurableSet[m x] s}) μ := by
  simp only [iIndep, iIndepSets, Kernel.iIndep]
/-
**ProbabilityTheory.iIndep.iIndepSets'** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityThe
ory.iIndep`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {m : ι → MeasurableSpace Ω} {x : Measurabl
eSpace Ω} {μ : MeasureTheory.Measure Ω},   ProbabilityTheory.iIndep m μ → Probab
ilityTheory.iIndepSets (fun x => {s | MeasurableSet s}) μ
参数：fun x => {s | MeasurableSet s}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `ProbabilityTheory.iIndep_iff_iIndepSets`：iIndep_iff_iIndepSets (m : ι ->
 MeasurableSpace Ω) {_mΩ : MeasurableSpace Ω} (μ : Measure Ω) : iIndep m μ ↔ iIn
depSets (fun x => {s | Measur…
-/
lemma iIndep.iIndepSets' {m : ι → MeasurableSpace Ω}
    {_ : MeasurableSpace Ω} {μ : Measure Ω} (hμ : iIndep m μ) :
    iIndepSets (fun x ↦ {s | MeasurableSet[m x] s}) μ := (iIndep_iff_iIndepSets _ _).1 hμ
/-
**ProbabilityTheory.iIndep.isProbabilityMeasure** 是 Mathlib 中的一个定理，位于命名空间 `Proba
bilityTheory.iIndep`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {m : ι → MeasurableSpace Ω} {x : Measurabl
eSpace Ω} {μ : MeasureTheory.Measure Ω},   ProbabilityTheory.iIndep m μ → Measur
eTheory.IsProbabilityMeasure μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.iIndepSets.isProbabilityMeasure`：∀ {Ω : Type u_1} {ι :
 Type u_2} {π : ι → Set (Set Ω)} {x : MeasurableSpace Ω} {μ : MeasureTheory.Meas
ure Ω},   ProbabilityTheory.iIndepSets …
· 使用定理 `ProbabilityTheory.iIndep.iIndepSets'`：∀ {Ω : Type u_1} {ι : Type u_2} {m
 : ι → MeasurableSpace Ω} {x : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω},
   ProbabilityTheory.iInde…
-/
lemma iIndep.isProbabilityMeasure (h : iIndep m μ) : IsProbabilityMeasure μ :=
  h.iIndepSets'.isProbabilityMeasure
/-
**ProbabilityTheory.iIndep_iff** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：iIndep_iff (m : ι -> MeasurableSpace Ω) {_mΩ : MeasurableSpace Ω} (μ : Mea
sure Ω) : iIndep m μ ↔ forall (s : Finset ι) {f : ι -> Set Ω} (_H : forall i, i 
in s -> MeasurableSet[m i] (f i)), μ (⋂ i in s, f i) = ∏ i in s, μ (f i)
参数：m : ι -> MeasurableSpace Ω；μ : Measure Ω。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma iIndep_iff (m : ι → MeasurableSpace Ω) {_mΩ : MeasurableSpace Ω} (μ : Measure Ω) :
    iIndep m μ ↔ ∀ (s : Finset ι) {f : ι → Set Ω} (_H : ∀ i, i ∈ s → MeasurableSet[m i] (f i)),
      μ (⋂ i ∈ s, f i) = ∏ i ∈ s, μ (f i) := by
  simp only [iIndep_iff_iIndepSets, iIndepSets_iff]; rfl
/-
**ProbabilityTheory.iIndep.meas_biInter** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTh
eory.iIndep`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {m : ι → MeasurableSpace Ω} {x : Measurabl
eSpace Ω} {μ : MeasureTheory.Measure Ω}   {S : Finset ι} {s : ι → Set Ω},   Prob
abilityTheory.iIndep m μ → (∀ i ∈ S, MeasurableSet (s i)) → μ (⋂ i ∈ S, s i) = ∏
 i ∈ S, μ (s i)
参数：∀ i ∈ S, MeasurableSet (s i)；⋂ i ∈ S, s i；s i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `ProbabilityTheory.iIndep_iff`：iIndep_iff (m : ι -> MeasurableSpace Ω) {_
mΩ : MeasurableSpace Ω} (μ : Measure Ω) : iIndep m μ ↔ forall (s : Finset ι) {f 
: ι -> Set Ω} (_H …
-/
lemma iIndep.meas_biInter (hμ : iIndep m μ) (hs : ∀ i, i ∈ S → MeasurableSet[m i] (s i)) :
    μ (⋂ i ∈ S, s i) = ∏ i ∈ S, μ (s i) := (iIndep_iff _ _).1 hμ _ hs
/-
**ProbabilityTheory.iIndep.meas_iInter** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityThe
ory.iIndep`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {m : ι → MeasurableSpace Ω} {x : Measurabl
eSpace Ω} {μ : MeasureTheory.Measure Ω}   {s : ι → Set Ω} [inst : Fintype ι],   
ProbabilityTheory.iIndep m μ → (∀ (i : ι), MeasurableSet (s i)) → μ (⋂ i, s i) =
 ∏ i, μ (s i)
参数：∀ (i : ι), MeasurableSet (s i)；⋂ i, s i；s i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.iIndep.meas_biInter`：∀ {Ω : Type u_1} {ι : Type u_2} {
m : ι → MeasurableSpace Ω} {x : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω}
   {S : Finset ι} {s : ι → …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iInter_true`：iInter_true {s : True -> Set α} : iInter s = s trivial
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma iIndep.meas_iInter [Fintype ι] (hμ : iIndep m μ) (hs : ∀ i, MeasurableSet[m i] (s i)) :
    μ (⋂ i, s i) = ∏ i, μ (s i) := by simp [← hμ.meas_biInter fun _ _ ↦ hs _]
/-
**ProbabilityTheory.Indep_iff_IndepSets** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTh
eory`。
形式化陈述：Indep_iff_IndepSets (m₁ m₂ : MeasurableSpace Ω) {_mΩ : MeasurableSpace Ω} 
(μ : Measure Ω) : Indep m₁ m₂ μ ↔ IndepSets {s | MeasurableSet[m₁] s} {s | Measu
rableSet[m₂] s} μ
参数：m₁ m₂ : MeasurableSpace Ω；μ : Measure Ω。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma Indep_iff_IndepSets (m₁ m₂ : MeasurableSpace Ω) {_mΩ : MeasurableSpace Ω} (μ : Measure Ω) :
    Indep m₁ m₂ μ ↔ IndepSets {s | MeasurableSet[m₁] s} {s | MeasurableSet[m₂] s} μ := by
  simp only [Indep, IndepSets, Kernel.Indep]
/-
**ProbabilityTheory.Indep_iff** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：Indep_iff (m₁ m₂ : MeasurableSpace Ω) {_mΩ : MeasurableSpace Ω} (μ : Measu
re Ω) : Indep m₁ m₂ μ ↔ forall t1 t2, MeasurableSet[m₁] t1 -> MeasurableSet[m₂] 
t2 -> μ (t1 inter t2) = μ t1 * μ t2
参数：m₁ m₂ : MeasurableSpace Ω；μ : Measure Ω。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.Indep_iff_IndepSets`：Indep_iff_IndepSets (m₁ m₂ : Meas
urableSpace Ω) {_mΩ : MeasurableSpace Ω} (μ : Measure Ω) : Indep m₁ m₂ μ ↔ Indep
Sets {s | MeasurableSet[m₁]…
· 使用引理 `ProbabilityTheory.IndepSets_iff`：IndepSets_iff (s1 s2 : Set (Set Ω)) (μ 
: Measure Ω) : IndepSets s1 s2 μ ↔ forall t1 t2 : Set Ω, t1 in s1 -> t2 in s2 ->
 (μ (t1 inter t2) = μ…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma Indep_iff (m₁ m₂ : MeasurableSpace Ω) {_mΩ : MeasurableSpace Ω} (μ : Measure Ω) :
    Indep m₁ m₂ μ
      ↔ ∀ t1 t2, MeasurableSet[m₁] t1 → MeasurableSet[m₂] t2 → μ (t1 ∩ t2) = μ t1 * μ t2 := by
  rw [Indep_iff_IndepSets, IndepSets_iff]; rfl
/-
**ProbabilityTheory.iIndepSet_iff_iIndep** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityT
heory`。
形式化陈述：iIndepSet_iff_iIndep (s : ι -> Set Ω) (μ : Measure Ω) : iIndepSet s μ ↔ iI
ndep (fun i => generateFrom {s i}) μ
参数：s : ι -> Set Ω；μ : Measure Ω。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma iIndepSet_iff_iIndep (s : ι → Set Ω) (μ : Measure Ω) :
    iIndepSet s μ ↔ iIndep (fun i ↦ generateFrom {s i}) μ := by
  simp only [iIndepSet, iIndep, Kernel.iIndepSet]
/-
**ProbabilityTheory.iIndepSet.isProbabilityMeasure** 是 Mathlib 中的一个定理，位于命名空间 `Pr
obabilityTheory.iIndepSet`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {x : MeasurableSpace Ω} {μ : MeasureTheory
.Measure Ω} {s : ι → Set Ω},   ProbabilityTheory.iIndepSet s μ → MeasureTheory.I
sProbabilityMeasure μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.iIndep.isProbabilityMeasure`：∀ {Ω : Type u_1} {ι : Typ
e u_2} {m : ι → MeasurableSpace Ω} {x : MeasurableSpace Ω} {μ : MeasureTheory.Me
asure Ω},   ProbabilityTheory.iInde…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `ProbabilityTheory.iIndepSet_iff_iIndep`：iIndepSet_iff_iIndep (s : ι -> S
et Ω) (μ : Measure Ω) : iIndepSet s μ ↔ iIndep (fun i => generateFrom {s i}) μ
-/
lemma iIndepSet.isProbabilityMeasure (h : iIndepSet s μ) : IsProbabilityMeasure μ :=
  ((iIndepSet_iff_iIndep _ _).1 h).isProbabilityMeasure
/-
**ProbabilityTheory.iIndepSet_iff** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：iIndepSet_iff (s : ι -> Set Ω) (μ : Measure Ω) : iIndepSet s μ ↔ forall (s
' : Finset ι) {f : ι -> Set Ω} (_H : forall i, i in s' -> MeasurableSet[generate
From {s i}] (f i)), μ (⋂ i in s', f i) = ∏ i in s', μ (f i)
参数：s : ι -> Set Ω；μ : Measure Ω。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma iIndepSet_iff (s : ι → Set Ω) (μ : Measure Ω) :
    iIndepSet s μ ↔ ∀ (s' : Finset ι) {f : ι → Set Ω}
      (_H : ∀ i, i ∈ s' → MeasurableSet[generateFrom {s i}] (f i)),
      μ (⋂ i ∈ s', f i) = ∏ i ∈ s', μ (f i) := by
  simp only [iIndepSet_iff_iIndep, iIndep_iff]
/-
**ProbabilityTheory.IndepSet_iff_Indep** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityThe
ory`。
形式化陈述：IndepSet_iff_Indep (s t : Set Ω) (μ : Measure Ω) : IndepSet s t μ ↔ Indep 
(generateFrom {s}) (generateFrom {t}) μ
参数：s t : Set Ω；μ : Measure Ω。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma IndepSet_iff_Indep (s t : Set Ω) (μ : Measure Ω) :
    IndepSet s t μ ↔ Indep (generateFrom {s}) (generateFrom {t}) μ := by
  simp only [IndepSet, Indep, Kernel.IndepSet]
/-
**ProbabilityTheory.IndepSet_iff** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：IndepSet_iff (s t : Set Ω) (μ : Measure Ω) : IndepSet s t μ ↔ forall t1 t2
, MeasurableSet[generateFrom {s}] t1 -> MeasurableSet[generateFrom {t}] t2 -> μ 
(t1 inter t2) = μ t1 * μ t2
参数：s t : Set Ω；μ : Measure Ω。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma IndepSet_iff (s t : Set Ω) (μ : Measure Ω) :
    IndepSet s t μ ↔ ∀ t1 t2, MeasurableSet[generateFrom {s}] t1
      → MeasurableSet[generateFrom {t}] t2 → μ (t1 ∩ t2) = μ t1 * μ t2 := by
  simp only [IndepSet_iff_Indep, Indep_iff]
/-
**ProbabilityTheory.iIndepFun_iff_iIndep** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityT
heory`。
形式化陈述：iIndepFun_iff_iIndep {β : ι -> Type*} (m : forall x : ι, MeasurableSpace (
β x)) (f : forall x : ι, Ω -> β x) (μ : Measure Ω) : iIndepFun f μ ↔ iIndep (fun
 x => (m x).comap (f x)) μ
参数：m : forall x : ι, MeasurableSpace (β x)；f : forall x : ι, Ω -> β x；μ : Measur
e Ω。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma iIndepFun_iff_iIndep {β : ι → Type*}
    (m : ∀ x : ι, MeasurableSpace (β x)) (f : ∀ x : ι, Ω → β x) (μ : Measure Ω) :
    iIndepFun f μ ↔ iIndep (fun x ↦ (m x).comap (f x)) μ := by
  simp only [iIndepFun, iIndep, Kernel.iIndepFun]

@[nontriviality, simp]
/-
**ProbabilityTheory.iIndepSets.of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Probab
ilityTheory.iIndepSets`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {x : MeasurableSpace Ω} {μ : MeasureTheory
.Measure Ω} [Subsingleton ι]   {m : ι → Set (Set Ω)} [MeasureTheory.IsProbabilit
yMeasure μ], ProbabilityTheory.iIndepSets m μ
参数：Set Ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepSets.of_subsingleton`：∀ {α : Type u_1} {Ω
 : Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {_mΩ : MeasurableSpace Ω} 
  {μ : MeasureTheory.Measure α} [Subsingl…
· 使用定理 `ProbabilityTheory.Kernel.const.instIsMarkovKernel`：∀ {α : Type u_1} {β :
 Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μβ : MeasureTheory
.Measure β}   [hμβ : MeasureTheory.IsPr…
-/
lemma iIndepSets.of_subsingleton [Subsingleton ι] {m : ι → Set (Set Ω)} [IsProbabilityMeasure μ] :
    iIndepSets m μ := Kernel.iIndepSets.of_subsingleton

@[nontriviality, simp]
/-
**ProbabilityTheory.iIndep.of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Probabilit
yTheory.iIndep`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {x : MeasurableSpace Ω} {μ : MeasureTheory
.Measure Ω} [Subsingleton ι]   {m : ι → MeasurableSpace Ω} [MeasureTheory.IsProb
abilityMeasure μ], ProbabilityTheory.iIndep m μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndep.of_subsingleton`：∀ {α : Type u_1} {Ω : T
ype u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {_mΩ : MeasurableSpace Ω}   {μ
 : MeasureTheory.Measure α} [Subsingl…
· 使用定理 `ProbabilityTheory.Kernel.const.instIsMarkovKernel`：∀ {α : Type u_1} {β :
 Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μβ : MeasureTheory
.Measure β}   [hμβ : MeasureTheory.IsPr…
-/
lemma iIndep.of_subsingleton [Subsingleton ι] {m : ι → MeasurableSpace Ω} [IsProbabilityMeasure μ] :
    iIndep m μ := Kernel.iIndep.of_subsingleton

@[nontriviality, simp]
/-
**ProbabilityTheory.iIndepFun.of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Probabi
lityTheory.iIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {x : MeasurableSpace Ω} {μ : MeasureTheory
.Measure Ω} [Subsingleton ι]   {β : ι → Type u_7} {m : (i : ι) → MeasurableSpace
 (β i)} {f : (i : ι) → Ω → β i}   [MeasureTheory.IsProbabilityMeasure μ], Probab
ilityTheory.iIndepFun f μ
参数：i : ι；β i；i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.of_subsingleton`：∀ {α : Type u_1} {Ω 
: Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {_mΩ : MeasurableSpace Ω}  
 {κ : ProbabilityTheory.Kernel α Ω} {μ :…
· 使用定理 `ProbabilityTheory.Kernel.const.instIsMarkovKernel`：∀ {α : Type u_1} {β :
 Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μβ : MeasureTheory
.Measure β}   [hμβ : MeasureTheory.IsPr…
-/
lemma iIndepFun.of_subsingleton [Subsingleton ι] {β : ι → Type*} {m : ∀ i, MeasurableSpace (β i)}
    {f : ∀ i, Ω → β i} [IsProbabilityMeasure μ] : iIndepFun f μ :=
  Kernel.iIndepFun.of_subsingleton
/-
**ProbabilityTheory.iIndepFun.iIndep** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheor
y.iIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {κ : ι → Type u_5} {x : MeasurableSpace Ω}
 {μ : MeasureTheory.Measure Ω}   {m : (i : ι) → MeasurableSpace (κ i)} {f : (x :
 ι) → Ω → κ x},   ProbabilityTheory.iIndepFun f μ → ProbabilityTheory.iIndep (fu
n x => MeasurableSpace.comap (f x) (m x)) μ
参数：i : ι；κ i；x : ι；fun x => MeasurableSpace.comap (f x) (m x)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma iIndepFun.iIndep {m : ∀ i, MeasurableSpace (κ i)} {f : ∀ x : ι, Ω → κ x}
    (hf : iIndepFun f μ) :
    iIndep (fun x ↦ (m x).comap (f x)) μ := hf
/-
**ProbabilityTheory.iIndepFun_iff** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：iIndepFun_iff {β : ι -> Type*} (m : forall x : ι, MeasurableSpace (β x)) (
f : forall x : ι, Ω -> β x) (μ : Measure Ω) : iIndepFun f μ ↔ forall (s : Finset
 ι) {f' : ι -> Set Ω} (_H : forall i, i in s -> MeasurableSet[(m i).comap (f i)]
 (f' i)), μ (⋂ i in s, f' i) = ∏ i in s, μ (f' i)
参数：m : forall x : ι, MeasurableSpace (β x)；f : forall x : ι, Ω -> β x；μ : Measur
e Ω。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma iIndepFun_iff {β : ι → Type*}
    (m : ∀ x : ι, MeasurableSpace (β x)) (f : ∀ x : ι, Ω → β x) (μ : Measure Ω) :
    iIndepFun f μ ↔ ∀ (s : Finset ι) {f' : ι → Set Ω}
      (_H : ∀ i, i ∈ s → MeasurableSet[(m i).comap (f i)] (f' i)),
      μ (⋂ i ∈ s, f' i) = ∏ i ∈ s, μ (f' i) := by
  simp only [iIndepFun_iff_iIndep, iIndep_iff]
/-
**ProbabilityTheory.iIndepFun.meas_biInter** 是 Mathlib 中的一个定理，位于命名空间 `Probabilit
yTheory.iIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {κ : ι → Type u_5} {x : MeasurableSpace Ω}
 {μ : MeasureTheory.Measure Ω} {S : Finset ι}   {s : ι → Set Ω} {m : (i : ι) → M
easurableSpace (κ i)} {f : (x : ι) → Ω → κ x},   ProbabilityTheory.iIndepFun f μ
 → (∀ i ∈ S, MeasurableSet (s i)) → μ (⋂ i ∈ S, s i) = ∏ i ∈ S, μ (s i)
参数：i : ι；κ i；x : ι；∀ i ∈ S, MeasurableSet (s i)；⋂ i ∈ S, s i；s i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.iIndep.meas_biInter`：∀ {Ω : Type u_1} {ι : Type u_2} {
m : ι → MeasurableSpace Ω} {x : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω}
   {S : Finset ι} {s : ι → …
· 使用定理 `ProbabilityTheory.iIndepFun.iIndep`：∀ {Ω : Type u_1} {ι : Type u_2} {κ :
 ι → Type u_5} {x : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω}   {m : (i :
 ι) → MeasurableSpace (κ…
-/
lemma iIndepFun.meas_biInter {m : ∀ i, MeasurableSpace (κ i)} {f : ∀ x : ι, Ω → κ x}
    (hf : iIndepFun f μ) (hs : ∀ i, i ∈ S → MeasurableSet[(m i).comap (f i)] (s i)) :
    μ (⋂ i ∈ S, s i) = ∏ i ∈ S, μ (s i) := hf.iIndep.meas_biInter hs
/-
**ProbabilityTheory.iIndepFun.meas_iInter** 是 Mathlib 中的一个定理，位于命名空间 `Probability
Theory.iIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {κ : ι → Type u_5} {x : MeasurableSpace Ω}
 {μ : MeasureTheory.Measure Ω} {s : ι → Set Ω}   [inst : Fintype ι] {m : (i : ι)
 → MeasurableSpace (κ i)} {f : (x : ι) → Ω → κ x},   ProbabilityTheory.iIndepFun
 f μ → (∀ (i : ι), MeasurableSet (s i)) → μ (⋂ i, s i) = ∏ i, μ (s i)
参数：i : ι；κ i；x : ι；∀ (i : ι), MeasurableSet (s i)；⋂ i, s i；s i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.iIndep.meas_iInter`：∀ {Ω : Type u_1} {ι : Type u_2} {m
 : ι → MeasurableSpace Ω} {x : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} 
  {s : ι → Set Ω} [inst : …
· 使用定理 `ProbabilityTheory.iIndepFun.iIndep`：∀ {Ω : Type u_1} {ι : Type u_2} {κ :
 ι → Type u_5} {x : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω}   {m : (i :
 ι) → MeasurableSpace (κ…
-/
lemma iIndepFun.meas_iInter [Fintype ι] {m : ∀ i, MeasurableSpace (κ i)} {f : ∀ x : ι, Ω → κ x}
    (hf : iIndepFun f μ) (hs : ∀ i, MeasurableSet[(m i).comap (f i)] (s i)) :
    μ (⋂ i, s i) = ∏ i, μ (s i) := hf.iIndep.meas_iInter hs
/-
**ProbabilityTheory.IndepFun_iff_Indep** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityThe
ory`。
形式化陈述：IndepFun_iff_Indep [mβ : MeasurableSpace β] [mγ : MeasurableSpace γ] (f : 
Ω -> β) (g : Ω -> γ) (μ : Measure Ω) : f ⟂ᵢ[μ] g ↔ Indep (MeasurableSpace.comap 
f mβ) (MeasurableSpace.comap g mγ) μ
参数：f : Ω -> β；g : Ω -> γ；μ : Measure Ω。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma IndepFun_iff_Indep [mβ : MeasurableSpace β]
    [mγ : MeasurableSpace γ] (f : Ω → β) (g : Ω → γ) (μ : Measure Ω) :
    f ⟂ᵢ[μ] g ↔ Indep (MeasurableSpace.comap f mβ) (MeasurableSpace.comap g mγ) μ := by
  simp only [IndepFun, Indep, Kernel.IndepFun]
/-
**ProbabilityTheory.IndepFun_iff** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：IndepFun_iff {β γ} [mβ : MeasurableSpace β] [mγ : MeasurableSpace γ] (f : 
Ω -> β) (g : Ω -> γ) (μ : Measure Ω) : f ⟂ᵢ[μ] g ↔ forall t1 t2, MeasurableSet[M
easurableSpace.comap f mβ] t1 -> MeasurableSet[MeasurableSpace.comap g mγ] t2 ->
 μ (t1 inter t2) = μ t1 * μ t2
参数：f : Ω -> β；g : Ω -> γ；μ : Measure Ω。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.IndepFun_iff_Indep`：IndepFun_iff_Indep [mβ : Measurabl
eSpace β] [mγ : MeasurableSpace γ] (f : Ω -> β) (g : Ω -> γ) (μ : Measure Ω) : f
 ⟂ᵢ[μ] g ↔ Indep (Measurab…
· 使用引理 `ProbabilityTheory.Indep_iff`：Indep_iff (m₁ m₂ : MeasurableSpace Ω) {_mΩ 
: MeasurableSpace Ω} (μ : Measure Ω) : Indep m₁ m₂ μ ↔ forall t1 t2, MeasurableS
et[m₁] t1 -> Meas…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma IndepFun_iff {β γ} [mβ : MeasurableSpace β] [mγ : MeasurableSpace γ]
    (f : Ω → β) (g : Ω → γ) (μ : Measure Ω) :
    f ⟂ᵢ[μ] g ↔ ∀ t1 t2, MeasurableSet[MeasurableSpace.comap f mβ] t1
      → MeasurableSet[MeasurableSpace.comap g mγ] t2 → μ (t1 ∩ t2) = μ t1 * μ t2 := by
  rw [IndepFun_iff_Indep, Indep_iff]
/-
**ProbabilityTheory.IndepFun.meas_inter** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTh
eory.IndepFun`。
形式化陈述：∀ {Ω : Type u_1} {β : Type u_3} {γ : Type u_4} {x : MeasurableSpace Ω} {μ 
: MeasureTheory.Measure Ω}   [mβ : MeasurableSpace β] [mγ : MeasurableSpace γ] {
f : Ω → β} {g : Ω → γ},   ProbabilityTheory.IndepFun f g μ → ∀ {s t : Set Ω}, Me
asurableSet s → MeasurableSet t → μ (s ∩ t) = μ s * μ t
参数：s ∩ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `ProbabilityTheory.IndepFun_iff`：IndepFun_iff {β γ} [mβ : MeasurableSpace
 β] [mγ : MeasurableSpace γ] (f : Ω -> β) (g : Ω -> γ) (μ : Measure Ω) : f ⟂ᵢ[μ]
 g ↔ forall t1 t2, M…
-/
lemma IndepFun.meas_inter [mβ : MeasurableSpace β] [mγ : MeasurableSpace γ] {f : Ω → β} {g : Ω → γ}
    (hfg : f ⟂ᵢ[μ] g) {s t : Set Ω} (hs : MeasurableSet[mβ.comap f] s)
    (ht : MeasurableSet[mγ.comap g] t) :
    μ (s ∩ t) = μ s * μ t :=
  (IndepFun_iff _ _ _).1 hfg _ _ hs ht
/-
**ProbabilityTheory.iIndepSets.precomp** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityThe
ory.iIndepSets`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {π : ι → Set (Set Ω)} {x : MeasurableSpace
 Ω} {μ : MeasureTheory.Measure Ω}   {ι' : Type u_6} {g : ι' → ι},   Function.Inj
ective g → ProbabilityTheory.iIndepSets π μ → ProbabilityTheory.iIndepSets (π ∘ 
g) μ
参数：Set Ω；π ∘ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepSets.precomp`：∀ {α : Type u_1} {Ω : Type 
u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {_mΩ : MeasurableSpace Ω}   {κ : P
robabilityTheory.Kernel α Ω} {μ :…
-/
lemma iIndepSets.precomp (hg : Function.Injective g) (h : iIndepSets π μ) :
    iIndepSets (π ∘ g) μ :=
  Kernel.iIndepSets.precomp hg h
/-
**ProbabilityTheory.iIndepSets.of_precomp** 是 Mathlib 中的一个定理，位于命名空间 `Probability
Theory.iIndepSets`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {π : ι → Set (Set Ω)} {x : MeasurableSpace
 Ω} {μ : MeasureTheory.Measure Ω}   {ι' : Type u_6} {g : ι' → ι},   Function.Sur
jective g → ProbabilityTheory.iIndepSets (π ∘ g) μ → ProbabilityTheory.iIndepSet
s π μ
参数：Set Ω；π ∘ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepSets.of_precomp`：∀ {α : Type u_1} {Ω : Ty
pe u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {_mΩ : MeasurableSpace Ω}   {κ 
: ProbabilityTheory.Kernel α Ω} {μ :…
-/
lemma iIndepSets.of_precomp (hg : Function.Surjective g) (h : iIndepSets (π ∘ g) μ) :
    iIndepSets π μ :=
  Kernel.iIndepSets.of_precomp hg h
/-
**ProbabilityTheory.iIndepSets_precomp_of_bijective** 是 Mathlib 中的一个引理，位于命名空间 `P
robabilityTheory`。
形式化陈述：iIndepSets_precomp_of_bijective (hg : Function.Bijective g) : iIndepSets (
π ∘ g) μ ↔ iIndepSets π μ
参数：hg : Function.Bijective g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.Kernel.iIndepSets_precomp_of_bijective`：iIndepSets_pre
comp_of_bijective (hg : Function.Bijective g) : iIndepSets (π ∘ g) κ μ ↔ iIndepS
ets π κ μ
-/
lemma iIndepSets_precomp_of_bijective (hg : Function.Bijective g) :
    iIndepSets (π ∘ g) μ ↔ iIndepSets π μ :=
  Kernel.iIndepSets_precomp_of_bijective hg
/-
**ProbabilityTheory.iIndep.precomp** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory.
iIndep`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {m : ι → MeasurableSpace Ω} {x : Measurabl
eSpace Ω} {μ : MeasureTheory.Measure Ω}   {ι' : Type u_6} {g : ι' → ι}, Function
.Injective g → ProbabilityTheory.iIndep m μ → ProbabilityTheory.iIndep (m ∘ g) μ
参数：m ∘ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndep.precomp`：∀ {α : Type u_1} {Ω : Type u_2}
 {ι : Type u_3} {_mα : MeasurableSpace α} {m : ι → MeasurableSpace Ω}   {_mΩ : M
easurableSpace Ω} {κ : Probab…
-/
lemma iIndep.precomp (hg : Function.Injective g) (h : iIndep m μ) :
    iIndep (m ∘ g) μ :=
  Kernel.iIndep.precomp hg h
/-
**ProbabilityTheory.iIndep.of_precomp** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheo
ry.iIndep`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {m : ι → MeasurableSpace Ω} {x : Measurabl
eSpace Ω} {μ : MeasureTheory.Measure Ω}   {ι' : Type u_6} {g : ι' → ι},   Functi
on.Surjective g → ProbabilityTheory.iIndep (m ∘ g) μ → ProbabilityTheory.iIndep 
m μ
参数：m ∘ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndep.of_precomp`：∀ {α : Type u_1} {Ω : Type u
_2} {ι : Type u_3} {_mα : MeasurableSpace α} {m : ι → MeasurableSpace Ω}   {_mΩ 
: MeasurableSpace Ω} {κ : Probab…
-/
lemma iIndep.of_precomp (hg : Function.Surjective g) (h : iIndep (m ∘ g) μ) :
    iIndep m μ :=
  Kernel.iIndep.of_precomp hg h
/-
**ProbabilityTheory.iIndep_precomp_of_bijective** 是 Mathlib 中的一个引理，位于命名空间 `Proba
bilityTheory`。
形式化陈述：iIndep_precomp_of_bijective (hg : Function.Bijective g) : iIndep (m ∘ g) μ
 ↔ iIndep m μ
参数：hg : Function.Bijective g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.Kernel.iIndep_precomp_of_bijective`：iIndep_precomp_of_
bijective (hg : Function.Bijective g) : iIndep (m ∘ g) κ μ ↔ iIndep m κ μ
-/
lemma iIndep_precomp_of_bijective (hg : Function.Bijective g) :
    iIndep (m ∘ g) μ ↔ iIndep m μ :=
  Kernel.iIndep_precomp_of_bijective hg
/-
**ProbabilityTheory.iIndepSet.precomp** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheo
ry.iIndepSet`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {x : MeasurableSpace Ω} {μ : MeasureTheory
.Measure Ω} {s : ι → Set Ω} {ι' : Type u_6}   {g : ι' → ι}, Function.Injective g
 → ProbabilityTheory.iIndepSet s μ → ProbabilityTheory.iIndepSet (s ∘ g) μ
参数：s ∘ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepSet.precomp`：∀ {α : Type u_1} {Ω : Type u
_2} {ι : Type u_3} {_mα : MeasurableSpace α} {_mΩ : MeasurableSpace Ω}   {κ : Pr
obabilityTheory.Kernel α Ω} {μ :…
-/
lemma iIndepSet.precomp (hg : Function.Injective g) (h : iIndepSet s μ) :
    iIndepSet (s ∘ g) μ :=
  Kernel.iIndepSet.precomp hg h
/-
**ProbabilityTheory.iIndepSet.of_precomp** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityT
heory.iIndepSet`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {x : MeasurableSpace Ω} {μ : MeasureTheory
.Measure Ω} {s : ι → Set Ω} {ι' : Type u_6}   {g : ι' → ι}, Function.Surjective 
g → ProbabilityTheory.iIndepSet (s ∘ g) μ → ProbabilityTheory.iIndepSet s μ
参数：s ∘ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepSet.of_precomp`：∀ {α : Type u_1} {Ω : Typ
e u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {_mΩ : MeasurableSpace Ω}   {κ :
 ProbabilityTheory.Kernel α Ω} {μ :…
-/
lemma iIndepSet.of_precomp (hg : Function.Surjective g) (h : iIndepSet (s ∘ g) μ) :
    iIndepSet s μ :=
  Kernel.iIndepSet.of_precomp hg h
/-
**ProbabilityTheory.iIndepSet_precomp_of_bijective** 是 Mathlib 中的一个引理，位于命名空间 `Pr
obabilityTheory`。
形式化陈述：iIndepSet_precomp_of_bijective (hg : Function.Bijective g) : iIndepSet (s 
∘ g) μ ↔ iIndepSet s μ
参数：hg : Function.Bijective g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.Kernel.iIndepSet_precomp_of_bijective`：iIndepSet_preco
mp_of_bijective (hg : Function.Bijective g) : iIndepSet (s ∘ g) κ μ ↔ iIndepSet 
s κ μ
-/
lemma iIndepSet_precomp_of_bijective (hg : Function.Bijective g) :
    iIndepSet (s ∘ g) μ ↔ iIndepSet s μ :=
  Kernel.iIndepSet_precomp_of_bijective hg

variable {β : ι → Type*} {m : ∀ i, MeasurableSpace (β i)} {f : ∀ i, Ω → β i}
/-
**ProbabilityTheory.iIndepFun.precomp** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheo
ry.iIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {x : MeasurableSpace Ω} {μ : MeasureTheory
.Measure Ω} {ι' : Type u_6} {g : ι' → ι}   {β : ι → Type u_7} {m : (i : ι) → Mea
surableSpace (β i)} {f : (i : ι) → Ω → β i},   Function.Injective g → Probabilit
yTheory.iIndepFun f μ → ProbabilityTheory.iIndepFun (fun i => f (g i)) μ
参数：i : ι；β i；i : ι；fun i => f (g i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.precomp`：∀ {α : Type u_1} {Ω : Type u
_2} {ι : Type u_3} {β : ι → Type u_8} {mβ : (i : ι) → MeasurableSpace (β i)}   {
_mα : MeasurableSpace α} {_mΩ : …
-/
lemma iIndepFun.precomp (hg : g.Injective) (h : iIndepFun f μ) :
    iIndepFun (m := fun i ↦ m (g i)) (fun i ↦ f (g i)) μ :=
  Kernel.iIndepFun.precomp hg h
/-
**ProbabilityTheory.iIndepFun.of_precomp** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityT
heory.iIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {x : MeasurableSpace Ω} {μ : MeasureTheory
.Measure Ω} {ι' : Type u_6} {g : ι' → ι}   {β : ι → Type u_7} {m : (i : ι) → Mea
surableSpace (β i)} {f : (i : ι) → Ω → β i},   Function.Surjective g → Probabili
tyTheory.iIndepFun (fun i => f (g i)) μ → ProbabilityTheory.iIndepFun f μ
参数：i : ι；β i；i : ι；fun i => f (g i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.of_precomp`：∀ {α : Type u_1} {Ω : Typ
e u_2} {ι : Type u_3} {β : ι → Type u_8} {mβ : (i : ι) → MeasurableSpace (β i)} 
  {_mα : MeasurableSpace α} {_mΩ : …
-/
lemma iIndepFun.of_precomp (hg : g.Surjective)
    (h : iIndepFun (m := fun i ↦ m (g i)) (fun i ↦ f (g i)) μ) : iIndepFun f μ :=
  Kernel.iIndepFun.of_precomp hg h
/-
**ProbabilityTheory.iIndepFun_precomp_of_bijective** 是 Mathlib 中的一个引理，位于命名空间 `Pr
obabilityTheory`。
形式化陈述：iIndepFun_precomp_of_bijective (hg : g.Bijective) : iIndepFun (m
参数：hg : g.Bijective。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.Kernel.iIndepFun_precomp_of_bijective`：iIndepFun_preco
mp_of_bijective (hg : Function.Bijective g) : iIndepFun (fun i => f (g i)) κ μ ↔
 iIndepFun f κ μ
-/
lemma iIndepFun_precomp_of_bijective (hg : g.Bijective) :
    iIndepFun (m := fun i ↦ m (g i)) (fun i ↦ f (g i)) μ ↔ iIndepFun f μ :=
  Kernel.iIndepFun_precomp_of_bijective hg

end Definition_lemmas

section Indep

variable {m₁ m₂ m₃ m₄ : MeasurableSpace Ω} (m' : MeasurableSpace Ω)
  {_mΩ : MeasurableSpace Ω} {μ : Measure Ω}

@[symm]
/-
**ProbabilityTheory.IndepSets.symm** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory.
IndepSets`。
形式化陈述：∀ {Ω : Type u_1} {_mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {
s₁ s₂ : Set (Set Ω)},   ProbabilityTheory.IndepSets s₁ s₂ μ → ProbabilityTheory.
IndepSets s₂ s₁ μ
参数：Set Ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IndepSets.symm`：∀ {α : Type u_1} {Ω : Type u_2}
 {_mα : MeasurableSpace α} {_mΩ : MeasurableSpace Ω} {κ : ProbabilityTheory.Kern
el α Ω}   {μ : MeasureTheory.…
-/
theorem IndepSets.symm {s₁ s₂ : Set (Set Ω)} (h : IndepSets s₁ s₂ μ) : IndepSets s₂ s₁ μ :=
  Kernel.IndepSets.symm h

@[symm]
/-
**ProbabilityTheory.Indep.symm** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory.Inde
p`。
形式化陈述：∀ {Ω : Type u_1} {m₁ m₂ _mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measur
e Ω},   ProbabilityTheory.Indep m₁ m₂ μ → ProbabilityTheory.Indep m₂ m₁ μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IndepSets.symm`：∀ {Ω : Type u_1} {_mΩ : MeasurableSpac
e Ω} {μ : MeasureTheory.Measure Ω} {s₁ s₂ : Set (Set Ω)},   ProbabilityTheory.In
depSets s₁ s₂ μ → Prob…
-/
theorem Indep.symm (h : Indep m₁ m₂ μ) : Indep m₂ m₁ μ := IndepSets.symm h
/-
**ProbabilityTheory.indep_bot_right** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory
`。
形式化陈述：indep_bot_right [IsZeroOrProbabilityMeasure μ] : Indep m' ⊥ μ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.indep_bot_right`：indep_bot_right (m' : Measurab
leSpace Ω) {_mΩ : MeasurableSpace Ω} {κ : Kernel α Ω} {μ : Measure α} [IsZeroOrM
arkovKernel κ] : Indep m' ⊥ κ …
· 使用定理 `ProbabilityTheory.Kernel.const.instIsZeroOrMarkovKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μβ : Measure
Theory.Measure β}   [hμβ : MeasureTheory.IsZe…
-/
theorem indep_bot_right [IsZeroOrProbabilityMeasure μ] : Indep m' ⊥ μ :=
  Kernel.indep_bot_right m'
/-
**ProbabilityTheory.indep_bot_left** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory`
。
形式化陈述：indep_bot_left [IsZeroOrProbabilityMeasure μ] : Indep ⊥ m' μ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Indep.symm`：∀ {Ω : Type u_1} {m₁ m₂ _mΩ : MeasurableSp
ace Ω} {μ : MeasureTheory.Measure Ω},   ProbabilityTheory.Indep m₁ m₂ μ → Probab
ilityTheory.Indep …
· 使用定理 `ProbabilityTheory.indep_bot_right`：indep_bot_right [IsZeroOrProbabilityM
easure μ] : Indep m' ⊥ μ
-/
theorem indep_bot_left [IsZeroOrProbabilityMeasure μ] : Indep ⊥ m' μ := (indep_bot_right m').symm
/-
**ProbabilityTheory.indepSet_empty_right** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityT
heory`。
形式化陈述：indepSet_empty_right [IsZeroOrProbabilityMeasure μ] (s : Set Ω) : IndepSet
 s ∅ μ
参数：s : Set Ω。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.indepSet_empty_right`：indepSet_empty_right {_mΩ
 : MeasurableSpace Ω} {κ : Kernel α Ω} {μ : Measure α} [IsZeroOrMarkovKernel κ] 
(s : Set Ω) : IndepSet s ∅ κ μ
· 使用定理 `ProbabilityTheory.Kernel.const.instIsZeroOrMarkovKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μβ : Measure
Theory.Measure β}   [hμβ : MeasureTheory.IsZe…
-/
theorem indepSet_empty_right [IsZeroOrProbabilityMeasure μ] (s : Set Ω) : IndepSet s ∅ μ :=
  Kernel.indepSet_empty_right s
/-
**ProbabilityTheory.indepSet_empty_left** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTh
eory`。
形式化陈述：indepSet_empty_left [IsZeroOrProbabilityMeasure μ] (s : Set Ω) : IndepSet 
∅ s μ
参数：s : Set Ω。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.indepSet_empty_left`：indepSet_empty_left {_mΩ :
 MeasurableSpace Ω} {κ : Kernel α Ω} {μ : Measure α} [IsZeroOrMarkovKernel κ] (s
 : Set Ω) : IndepSet ∅ s κ μ
· 使用定理 `ProbabilityTheory.Kernel.const.instIsZeroOrMarkovKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μβ : Measure
Theory.Measure β}   [hμβ : MeasureTheory.IsZe…
-/
theorem indepSet_empty_left [IsZeroOrProbabilityMeasure μ] (s : Set Ω) : IndepSet ∅ s μ :=
  Kernel.indepSet_empty_left s
/-
**ProbabilityTheory.indepSets_of_indepSets_of_le_left** 是 Mathlib 中的一个定理，位于命名空间 
`ProbabilityTheory`。
形式化陈述：indepSets_of_indepSets_of_le_left {s₁ s₂ s₃ : Set (Set Ω)} (h_indep : Inde
pSets s₁ s₂ μ) (h31 : s₃ subseteq s₁) : IndepSets s₃ s₂ μ
参数：Set Ω；h_indep : IndepSets s₁ s₂ μ；h31 : s₃ subseteq s₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.indepSets_of_indepSets_of_le_left`：indepSets_of
_indepSets_of_le_left {s₁ s₂ s₃ : Set (Set Ω)} {_mΩ : MeasurableSpace Ω} {κ : Ke
rnel α Ω} {μ : Measure α} (h_indep : IndepSets s…
-/
theorem indepSets_of_indepSets_of_le_left {s₁ s₂ s₃ : Set (Set Ω)}
    (h_indep : IndepSets s₁ s₂ μ) (h31 : s₃ ⊆ s₁) :
    IndepSets s₃ s₂ μ :=
  Kernel.indepSets_of_indepSets_of_le_left h_indep h31
/-
**ProbabilityTheory.indepSets_of_indepSets_of_le_right** 是 Mathlib 中的一个定理，位于命名空间
 `ProbabilityTheory`。
形式化陈述：indepSets_of_indepSets_of_le_right {s₁ s₂ s₃ : Set (Set Ω)} (h_indep : Ind
epSets s₁ s₂ μ) (h32 : s₃ subseteq s₂) : IndepSets s₁ s₃ μ
参数：Set Ω；h_indep : IndepSets s₁ s₂ μ；h32 : s₃ subseteq s₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.indepSets_of_indepSets_of_le_right`：indepSets_o
f_indepSets_of_le_right {s₁ s₂ s₃ : Set (Set Ω)} {_mΩ : MeasurableSpace Ω} {κ : 
Kernel α Ω} {μ : Measure α} (h_indep : IndepSets …
-/
theorem indepSets_of_indepSets_of_le_right {s₁ s₂ s₃ : Set (Set Ω)}
    (h_indep : IndepSets s₁ s₂ μ) (h32 : s₃ ⊆ s₂) :
    IndepSets s₁ s₃ μ :=
  Kernel.indepSets_of_indepSets_of_le_right h_indep h32
/-
**ProbabilityTheory.indep_of_indep_of_le_left** 是 Mathlib 中的一个定理，位于命名空间 `Probabi
lityTheory`。
形式化陈述：indep_of_indep_of_le_left (h_indep : Indep m₁ m₂ μ) (h31 : m₃ <= m₁) : Ind
ep m₃ m₂ μ
参数：h_indep : Indep m₁ m₂ μ；h31 : m₃ <= m₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.indep_of_indep_of_le_left`：indep_of_indep_of_le
_left {m₁ m₂ m₃ : MeasurableSpace Ω} {_mΩ : MeasurableSpace Ω} {κ : Kernel α Ω} 
{μ : Measure α} (h_indep : Indep m₁ m₂ κ…
-/
theorem indep_of_indep_of_le_left (h_indep : Indep m₁ m₂ μ) (h31 : m₃ ≤ m₁) :
    Indep m₃ m₂ μ :=
  Kernel.indep_of_indep_of_le_left h_indep h31
/-
**ProbabilityTheory.indep_of_indep_of_le_right** 是 Mathlib 中的一个定理，位于命名空间 `Probab
ilityTheory`。
形式化陈述：indep_of_indep_of_le_right (h_indep : Indep m₁ m₂ μ) (h32 : m₃ <= m₂) : In
dep m₁ m₃ μ
参数：h_indep : Indep m₁ m₂ μ；h32 : m₃ <= m₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.indep_of_indep_of_le_right`：indep_of_indep_of_l
e_right {m₁ m₂ m₃ : MeasurableSpace Ω} {_mΩ : MeasurableSpace Ω} {κ : Kernel α Ω
} {μ : Measure α} (h_indep : Indep m₁ m₂ …
-/
theorem indep_of_indep_of_le_right (h_indep : Indep m₁ m₂ μ) (h32 : m₃ ≤ m₂) :
    Indep m₁ m₃ μ :=
  Kernel.indep_of_indep_of_le_right h_indep h32
/-
**ProbabilityTheory.indep_of_indep_of_le** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityT
heory`。
形式化陈述：indep_of_indep_of_le (h_indep : Indep m₁ m₂ μ) (h31 : m₃ <= m₁) (h42 : m₄ 
<= m₂) : Indep m₃ m₄ μ
参数：h_indep : Indep m₁ m₂ μ；h31 : m₃ <= m₁；h42 : m₄ <= m₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.indep_of_indep_of_le`：indep_of_indep_of_le {m₁ 
m₂ m₃ m₄ : MeasurableSpace Ω} {_mΩ : MeasurableSpace Ω} {κ : Kernel α Ω} {μ : Me
asure α} (h_indep : Indep m₁ m₂ κ μ…
-/
theorem indep_of_indep_of_le (h_indep : Indep m₁ m₂ μ) (h31 : m₃ ≤ m₁) (h42 : m₄ ≤ m₂) :
    Indep m₃ m₄ μ :=
  Kernel.indep_of_indep_of_le h_indep h31 h42
/-
**ProbabilityTheory.iIndep_of_iIndep_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Probabilit
yTheory`。
形式化陈述：iIndep_of_iIndep_of_le {m₁ m₂ : ι -> MeasurableSpace Ω} (h_indep : iIndep 
m₂ μ) (h_le : forall i, m₁ i <= m₂ i) : iIndep m₁ μ
参数：h_indep : iIndep m₂ μ；h_le : forall i, m₁ i <= m₂ i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndep_of_iIndep_of_le`：iIndep_of_iIndep_of_le 
{m₁ m₂ : ι -> MeasurableSpace Ω} {_mΩ : MeasurableSpace Ω} {κ : Kernel α Ω} {μ :
 Measure α} (h_indep : iIndep m₂ κ μ)…
-/
theorem iIndep_of_iIndep_of_le {m₁ m₂ : ι → MeasurableSpace Ω} (h_indep : iIndep m₂ μ)
    (h_le : ∀ i, m₁ i ≤ m₂ i) : iIndep m₁ μ :=
  Kernel.iIndep_of_iIndep_of_le h_indep h_le
/-
**ProbabilityTheory.IndepSets.union** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory
.IndepSets`。
形式化陈述：∀ {Ω : Type u_1} {_mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {
s₁ s₂ s' : Set (Set Ω)},   ProbabilityTheory.IndepSets s₁ s' μ → ProbabilityTheo
ry.IndepSets s₂ s' μ → ProbabilityTheory.IndepSets (s₁ ∪ s₂) s' μ
参数：Set Ω；s₁ ∪ s₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IndepSets.union`：∀ {α : Type u_1} {Ω : Type u_2
} {_mα : MeasurableSpace α} {s₁ s₂ s' : Set (Set Ω)} {_mΩ : MeasurableSpace Ω}  
 {κ : ProbabilityTheory.Kernel…
-/
theorem IndepSets.union {s₁ s₂ s' : Set (Set Ω)} (h₁ : IndepSets s₁ s' μ) (h₂ : IndepSets s₂ s' μ) :
    IndepSets (s₁ ∪ s₂) s' μ :=
  Kernel.IndepSets.union h₁ h₂

@[simp]
/-
**ProbabilityTheory.IndepSets.union_iff** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTh
eory.IndepSets`。
形式化陈述：∀ {Ω : Type u_1} {_mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {
s₁ s₂ s' : Set (Set Ω)},   ProbabilityTheory.IndepSets (s₁ ∪ s₂) s' μ ↔ Probabil
ityTheory.IndepSets s₁ s' μ ∧ ProbabilityTheory.IndepSets s₂ s' μ
参数：Set Ω；s₁ ∪ s₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IndepSets.union_iff`：∀ {α : Type u_1} {Ω : Type
 u_2} {_mα : MeasurableSpace α} {s₁ s₂ s' : Set (Set Ω)} {_mΩ : MeasurableSpace 
Ω}   {κ : ProbabilityTheory.Kernel…
-/
theorem IndepSets.union_iff {s₁ s₂ s' : Set (Set Ω)} :
    IndepSets (s₁ ∪ s₂) s' μ ↔ IndepSets s₁ s' μ ∧ IndepSets s₂ s' μ :=
  Kernel.IndepSets.union_iff
/-
**ProbabilityTheory.IndepSets.iUnion** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheor
y.IndepSets`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {_mΩ : MeasurableSpace Ω} {μ : MeasureTheo
ry.Measure Ω} {s : ι → Set (Set Ω)}   {s' : Set (Set Ω)}, (∀ (n : ι), Probabilit
yTheory.IndepSets (s n) s' μ) → ProbabilityTheory.IndepSets (⋃ n, s n) s' μ
参数：Set Ω；Set Ω；∀ (n : ι), ProbabilityTheory.IndepSets (s n) s' μ；⋃ n, s n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IndepSets.iUnion`：∀ {α : Type u_1} {Ω : Type u_
2} {ι : Type u_3} {_mα : MeasurableSpace α} {s : ι → Set (Set Ω)} {s' : Set (Set
 Ω)}   {_mΩ : MeasurableSpace Ω…
-/
theorem IndepSets.iUnion {s : ι → Set (Set Ω)} {s' : Set (Set Ω)}
    (hyp : ∀ n, IndepSets (s n) s' μ) :
    IndepSets (⋃ n, s n) s' μ :=
  Kernel.IndepSets.iUnion hyp
/-
**ProbabilityTheory.IndepSets.biUnion** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheo
ry.IndepSets`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {_mΩ : MeasurableSpace Ω} {μ : MeasureTheo
ry.Measure Ω} {s : ι → Set (Set Ω)}   {s' : Set (Set Ω)} {u : Set ι},   (∀ n ∈ u
, ProbabilityTheory.IndepSets (s n) s' μ) → ProbabilityTheory.IndepSets (⋃ n ∈ u
, s n) s' μ
参数：Set Ω；Set Ω；∀ n ∈ u, ProbabilityTheory.IndepSets (s n) s' μ；⋃ n ∈ u, s n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IndepSets.biUnion`：∀ {α : Type u_1} {Ω : Type u
_2} {ι : Type u_3} {_mα : MeasurableSpace α} {s : ι → Set (Set Ω)} {s' : Set (Se
t Ω)}   {_mΩ : MeasurableSpace Ω…
-/
theorem IndepSets.biUnion {s : ι → Set (Set Ω)} {s' : Set (Set Ω)}
    {u : Set ι} (hyp : ∀ n ∈ u, IndepSets (s n) s' μ) :
    IndepSets (⋃ n ∈ u, s n) s' μ :=
  Kernel.IndepSets.biUnion hyp
/-
**ProbabilityTheory.IndepSets.inter** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory
.IndepSets`。
形式化陈述：∀ {Ω : Type u_1} {_mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {
s₁ s' : Set (Set Ω)} (s₂ : Set (Set Ω)),   ProbabilityTheory.IndepSets s₁ s' μ →
 ProbabilityTheory.IndepSets (s₁ ∩ s₂) s' μ
参数：Set Ω；s₂ : Set (Set Ω)；s₁ ∩ s₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IndepSets.inter`：∀ {α : Type u_1} {Ω : Type u_2
} {_mα : MeasurableSpace α} {s₁ s' : Set (Set Ω)} (s₂ : Set (Set Ω))   {_mΩ : Me
asurableSpace Ω} {κ : Probabil…
-/
theorem IndepSets.inter {s₁ s' : Set (Set Ω)} (s₂ : Set (Set Ω)) (h₁ : IndepSets s₁ s' μ) :
    IndepSets (s₁ ∩ s₂) s' μ :=
  Kernel.IndepSets.inter s₂ h₁
/-
**ProbabilityTheory.IndepSets.iInter** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheor
y.IndepSets`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {_mΩ : MeasurableSpace Ω} {μ : MeasureTheo
ry.Measure Ω} {s : ι → Set (Set Ω)}   {s' : Set (Set Ω)}, (∃ n, ProbabilityTheor
y.IndepSets (s n) s' μ) → ProbabilityTheory.IndepSets (⋂ n, s n) s' μ
参数：Set Ω；Set Ω；∃ n, ProbabilityTheory.IndepSets (s n) s' μ；⋂ n, s n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IndepSets.iInter`：∀ {α : Type u_1} {Ω : Type u_
2} {ι : Type u_3} {_mα : MeasurableSpace α} {s : ι → Set (Set Ω)} {s' : Set (Set
 Ω)}   {_mΩ : MeasurableSpace Ω…
-/
theorem IndepSets.iInter {s : ι → Set (Set Ω)} {s' : Set (Set Ω)}
    (h : ∃ n, IndepSets (s n) s' μ) :
    IndepSets (⋂ n, s n) s' μ :=
  Kernel.IndepSets.iInter h
/-
**ProbabilityTheory.IndepSets.bInter** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheor
y.IndepSets`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {_mΩ : MeasurableSpace Ω} {μ : MeasureTheo
ry.Measure Ω} {s : ι → Set (Set Ω)}   {s' : Set (Set Ω)} {u : Set ι},   (∃ n ∈ u
, ProbabilityTheory.IndepSets (s n) s' μ) → ProbabilityTheory.IndepSets (⋂ n ∈ u
, s n) s' μ
参数：Set Ω；Set Ω；∃ n ∈ u, ProbabilityTheory.IndepSets (s n) s' μ；⋂ n ∈ u, s n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IndepSets.bInter`：∀ {α : Type u_1} {Ω : Type u_
2} {ι : Type u_3} {_mα : MeasurableSpace α} {s : ι → Set (Set Ω)} {s' : Set (Set
 Ω)}   {_mΩ : MeasurableSpace Ω…
-/
theorem IndepSets.bInter {s : ι → Set (Set Ω)} {s' : Set (Set Ω)}
    {u : Set ι} (h : ∃ n ∈ u, IndepSets (s n) s' μ) :
    IndepSets (⋂ n ∈ u, s n) s' μ :=
  Kernel.IndepSets.bInter h
/-
**ProbabilityTheory.indepSets_singleton_iff** 是 Mathlib 中的一个定理，位于命名空间 `Probabili
tyTheory`。
形式化陈述：indepSets_singleton_iff {s t : Set Ω} : IndepSets {s} {t} μ ↔ μ (s inter t
) = μ s * μ t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_dirac_eq`：ae_dirac_eq [MeasurableSingletonClass α] (a :
 α) : ae (dirac a) = pure a
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `standardBorelSpace_of_discreteMeasurableSpace`：∀ {α : Type u_1} [inst : 
MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α], StandardBorelSpace
 α
· 使用定理 `instDiscreteMeasurableSpace`：∀ {α : Type u_1}, DiscreteMeasurableSpace α
· 使用定理 `instCountablePUnit`：Countable PUnit.{u}
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem indepSets_singleton_iff {s t : Set Ω} :
    IndepSets {s} {t} μ ↔ μ (s ∩ t) = μ s * μ t := by
  simp only [IndepSets, Kernel.indepSets_singleton_iff, ae_dirac_eq, Filter.eventually_pure,
    Kernel.const_apply]
/-
**ProbabilityTheory.indepSets_iff_singleton_indepSets** 是 Mathlib 中的一个引理，位于命名空间 
`ProbabilityTheory`。
形式化陈述：indepSets_iff_singleton_indepSets {𝒜 ℬ : Set (Set Ω)} : IndepSets 𝒜 ℬ μ ↔ 
forall A in 𝒜, IndepSets {A} ℬ μ where mp h A hA
参数：Set Ω。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.indepSets_of_indepSets_of_le_left`：indepSets_of_indepS
ets_of_le_left {s₁ s₂ s₃ : Set (Set Ω)} (h_indep : IndepSets s₁ s₂ μ) (h31 : s₃ 
subseteq s₁) : IndepSets s₃ s₂ μ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.biUnion_of_singleton`：biUnion_of_singleton (s : Set α) : ⋃ x in s, {
x} = s
· 使用定理 `ProbabilityTheory.IndepSets.biUnion`：∀ {Ω : Type u_1} {ι : Type u_2} {_m
Ω : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {s : ι → Set (Set Ω)}   {s'
 : Set (Set Ω)} {u : Set …
-/
lemma indepSets_iff_singleton_indepSets {𝒜 ℬ : Set (Set Ω)} :
    IndepSets 𝒜 ℬ μ ↔ ∀ A ∈ 𝒜, IndepSets {A} ℬ μ where
  mp h A hA := indepSets_of_indepSets_of_le_left h (Set.singleton_subset_iff.2 hA)
  mpr h := by
    rw [← 𝒜.biUnion_of_singleton]
    exact IndepSets.biUnion h

end Indep

/-! ### Deducing `Indep` from `iIndep` -/


section FromIndepToIndep

variable {m : ι → MeasurableSpace Ω} {_mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-
**ProbabilityTheory.iIndepSets.indepSets** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityT
heory.iIndepSets`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {_mΩ : MeasurableSpace Ω} {μ : MeasureTheo
ry.Measure Ω} {s : ι → Set (Set Ω)},   ProbabilityTheory.iIndepSets s μ → ∀ {i j
 : ι}, i ≠ j → ProbabilityTheory.IndepSets (s i) (s j) μ
参数：Set Ω；s i；s j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepSets.indepSets`：∀ {α : Type u_1} {Ω : Typ
e u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {s : ι → Set (Set Ω)} {_mΩ : Mea
surableSpace Ω}   {κ : ProbabilityT…
-/
theorem iIndepSets.indepSets {s : ι → Set (Set Ω)}
    (h_indep : iIndepSets s μ) {i j : ι} (hij : i ≠ j) : IndepSets (s i) (s j) μ :=
  Kernel.iIndepSets.indepSets h_indep hij
/-
**ProbabilityTheory.iIndep.indep** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory.iI
ndep`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {m : ι → MeasurableSpace Ω} {_mΩ : Measura
bleSpace Ω} {μ : MeasureTheory.Measure Ω},   ProbabilityTheory.iIndep m μ → ∀ {i
 j : ι}, i ≠ j → ProbabilityTheory.Indep (m i) (m j) μ
参数：m i；m j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndep.indep`：∀ {α : Type u_1} {Ω : Type u_2} {
ι : Type u_3} {_mα : MeasurableSpace α} {m : ι → MeasurableSpace Ω}   {_mΩ : Mea
surableSpace Ω} {κ : Probab…
-/
theorem iIndep.indep
    (h_indep : iIndep m μ) {i j : ι} (hij : i ≠ j) : Indep (m i) (m j) μ :=
  Kernel.iIndep.indep h_indep hij
/-
**ProbabilityTheory.iIndepFun.indepFun** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityThe
ory.iIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {_mΩ : MeasurableSpace Ω} {μ : MeasureTheo
ry.Measure Ω} {β : ι → Type u_6}   {m : (x : ι) → MeasurableSpace (β x)} {f : (i
 : ι) → Ω → β i},   ProbabilityTheory.iIndepFun f μ → ∀ {i j : ι}, i ≠ j → Proba
bilityTheory.IndepFun (f i) (f j) μ
参数：x : ι；β x；i : ι；f i；f j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.indepFun`：∀ {α : Type u_1} {Ω : Type 
u_2} {ι : Type u_3} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω}   {κ : Pro
babilityTheory.Kernel α Ω} {μ : M…
-/
theorem iIndepFun.indepFun {β : ι → Type*}
    {m : ∀ x, MeasurableSpace (β x)} {f : ∀ i, Ω → β i} (hf_Indep : iIndepFun f μ) {i j : ι}
    (hij : i ≠ j) :
    f i ⟂ᵢ[μ] f j :=
  Kernel.iIndepFun.indepFun hf_Indep hij

end FromIndepToIndep

/-!
## π-system lemma

Independence of measurable spaces is equivalent to independence of generating π-systems.
-/


section FromMeasurableSpacesToSetsOfSets

variable {m : ι → MeasurableSpace Ω} {_mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-! ### Independence of measurable space structures implies independence of generating π-systems -/

/-
**ProbabilityTheory.iIndep.iIndepSets** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheo
ry.iIndep`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {m : ι → MeasurableSpace Ω} {_mΩ : Measura
bleSpace Ω} {μ : MeasureTheory.Measure Ω}   {s : ι → Set (Set Ω)},   (∀ (n : ι),
 m n = MeasurableSpace.generateFrom (s n)) →     ProbabilityTheory.iIndep m μ → 
ProbabilityTheory.iIndepSets s μ
参数：Set Ω；∀ (n : ι), m n = MeasurableSpace.generateFrom (s n)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndep.iIndepSets`：∀ {α : Type u_1} {Ω : Type u
_2} {ι : Type u_3} {_mα : MeasurableSpace α} {_mΩ : MeasurableSpace Ω}   {κ : Pr
obabilityTheory.Kernel α Ω} {μ :…

--- 原说明 ---
### Independence of measurable space structures implies independence of generati
ng π-systems
-/
theorem iIndep.iIndepSets
    {s : ι → Set (Set Ω)} (hms : ∀ n, m n = generateFrom (s n)) (h_indep : iIndep m μ) :
    iIndepSets s μ :=
  Kernel.iIndep.iIndepSets hms h_indep
/-
**ProbabilityTheory.Indep.indepSets** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory
.Indep`。
形式化陈述：∀ {Ω : Type u_1} {_mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {
s1 s2 : Set (Set Ω)},   ProbabilityTheory.Indep (MeasurableSpace.generateFrom s1
) (MeasurableSpace.generateFrom s2) μ →     ProbabilityTheory.IndepSets s1 s2 μ
参数：Set Ω；MeasurableSpace.generateFrom s1；MeasurableSpace.generateFrom s2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.Indep.indepSets`：∀ {α : Type u_1} {Ω : Type u_2
} {_mα : MeasurableSpace α} {_mΩ : MeasurableSpace Ω} {κ : ProbabilityTheory.Ker
nel α Ω}   {μ : MeasureTheory.…
-/
theorem Indep.indepSets {s1 s2 : Set (Set Ω)}
    (h_indep : Indep (generateFrom s1) (generateFrom s2) μ) :
    IndepSets s1 s2 μ :=
  Kernel.Indep.indepSets h_indep

end FromMeasurableSpacesToSetsOfSets

section FromPiSystemsToMeasurableSpaces

variable {m : ι → MeasurableSpace Ω} {m1 m2 _mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-! ### Independence of generating π-systems implies independence of measurable space structures -/

/-
**ProbabilityTheory.IndepSets.indep** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory
.IndepSets`。
形式化陈述：∀ {Ω : Type u_1} {m1 m2 _mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measur
e Ω}   [MeasureTheory.IsZeroOrProbabilityMeasure μ] {p1 p2 : Set (Set Ω)},   m1 
≤ _mΩ →     m2 ≤ _mΩ →       IsPiSystem p1 →         IsPiSystem p2 →           m
1 = MeasurableSpace.generateFrom p1 →             m2 = MeasurableSpace.generateF
rom p2 → ProbabilityTheory.IndepSets p1 p2 μ → ProbabilityTheory.Indep m1 m2 μ
参数：Set Ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IndepSets.indep`：∀ {α : Type u_1} {Ω : Type u_2
} {_mα : MeasurableSpace α} {m1 m2 m : MeasurableSpace Ω}   {κ : ProbabilityTheo
ry.Kernel α Ω} {μ : MeasureThe…
· 使用定理 `ProbabilityTheory.Kernel.const.instIsZeroOrMarkovKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μβ : Measure
Theory.Measure β}   [hμβ : MeasureTheory.IsZe…

--- 原说明 ---
### Independence of generating π-systems implies independence of measurable spac
e structures
-/
theorem IndepSets.indep [IsZeroOrProbabilityMeasure μ]
    {p1 p2 : Set (Set Ω)} (h1 : m1 ≤ _mΩ) (h2 : m2 ≤ _mΩ) (hp1 : IsPiSystem p1)
    (hp2 : IsPiSystem p2) (hpm1 : m1 = generateFrom p1) (hpm2 : m2 = generateFrom p2)
    (hyp : IndepSets p1 p2 μ) :
    Indep m1 m2 μ :=
  Kernel.IndepSets.indep h1 h2 hp1 hp2 hpm1 hpm2 hyp
/-
**ProbabilityTheory.IndepSets.indep'** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheor
y.IndepSets`。
形式化陈述：∀ {Ω : Type u_1} {_mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} [
MeasureTheory.IsZeroOrProbabilityMeasure μ]   {p1 p2 : Set (Set Ω)},   (∀ s ∈ p1
, MeasurableSet s) →     (∀ s ∈ p2, MeasurableSet s) →       IsPiSystem p1 →    
     IsPiSystem p2 →           ProbabilityTheory.IndepSets p1 p2 μ →            
 ProbabilityTheory.Indep (MeasurableSpace.generateFrom p1) (MeasurableSpace.gene
rateFrom p2) μ
参数：Set Ω；∀ s ∈ p1, MeasurableSet s；∀ s ∈ p2, MeasurableSet s；MeasurableSpace.gen
erateFrom p1；MeasurableSpace.generateFrom p2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IndepSets.indep'`：∀ {α : Type u_1} {Ω : Type u_
2} {_mα : MeasurableSpace α} {_mΩ : MeasurableSpace Ω} {κ : ProbabilityTheory.Ke
rnel α Ω}   {μ : MeasureTheory.…
· 使用定理 `ProbabilityTheory.Kernel.const.instIsZeroOrMarkovKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μβ : Measure
Theory.Measure β}   [hμβ : MeasureTheory.IsZe…
-/
theorem IndepSets.indep' [IsZeroOrProbabilityMeasure μ]
    {p1 p2 : Set (Set Ω)} (hp1m : ∀ s ∈ p1, MeasurableSet s) (hp2m : ∀ s ∈ p2, MeasurableSet s)
    (hp1 : IsPiSystem p1) (hp2 : IsPiSystem p2) (hyp : IndepSets p1 p2 μ) :
    Indep (generateFrom p1) (generateFrom p2) μ :=
  Kernel.IndepSets.indep' hp1m hp2m hp1 hp2 hyp
/-
**ProbabilityTheory.indepSets_piiUnionInter_of_disjoint** 是 Mathlib 中的一个定理，位于命名空
间 `ProbabilityTheory`。
形式化陈述：indepSets_piiUnionInter_of_disjoint {s : ι -> Set (Set Ω)} {S T : Set ι} (
h_indep : iIndepSets s μ) (hST : Disjoint S T) : IndepSets (piiUnionInter s S) (
piiUnionInter s T) μ
参数：Set Ω；h_indep : iIndepSets s μ；hST : Disjoint S T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.indepSets_piiUnionInter_of_disjoint`：indepSets_
piiUnionInter_of_disjoint {s : ι -> Set (Set Ω)} {S T : Set ι} (h_indep : iIndep
Sets s κ μ) (hST : Disjoint S T) : IndepSets (piiU…
-/
theorem indepSets_piiUnionInter_of_disjoint {s : ι → Set (Set Ω)}
    {S T : Set ι} (h_indep : iIndepSets s μ) (hST : Disjoint S T) :
    IndepSets (piiUnionInter s S) (piiUnionInter s T) μ :=
  Kernel.indepSets_piiUnionInter_of_disjoint h_indep hST
/-
**ProbabilityTheory.iIndepSet.indep_generateFrom_of_disjoint** 是 Mathlib 中的一个定理，
位于命名空间 `ProbabilityTheory.iIndepSet`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {_mΩ : MeasurableSpace Ω} {μ : MeasureTheo
ry.Measure Ω} {s : ι → Set Ω},   (∀ (n : ι), MeasurableSet (s n)) →     Probabil
ityTheory.iIndepSet s μ →       ∀ (S T : Set ι),         Disjoint S T →         
  ProbabilityTheory.Indep (MeasurableSpace.generateFrom {t | ∃ n ∈ S, s n = t}) 
            (MeasurableSpace.generateFrom {t | ∃ k ∈ T, s k = t}) μ
参数：∀ (n : ι), MeasurableSet (s n)；S T : Set ι；MeasurableSpace.generateFrom {t | 
∃ n ∈ S, s n = t}；MeasurableSpace.generateFrom {t | ∃ k ∈ T, s k = t}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepSet.indep_generateFrom_of_disjoint`：∀ {α 
: Type u_1} {Ω : Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {_mΩ : Measu
rableSpace Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ :…
-/
theorem iIndepSet.indep_generateFrom_of_disjoint {s : ι → Set Ω}
    (hsm : ∀ n, MeasurableSet (s n)) (hs : iIndepSet s μ) (S T : Set ι) (hST : Disjoint S T) :
    Indep (generateFrom { t | ∃ n ∈ S, s n = t }) (generateFrom { t | ∃ k ∈ T, s k = t }) μ :=
  Kernel.iIndepSet.indep_generateFrom_of_disjoint hsm hs S T hST
/-
**ProbabilityTheory.indep_iSup_of_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Probabilit
yTheory`。
形式化陈述：indep_iSup_of_disjoint (h_le : forall i, m i <= _mΩ) (h_indep : iIndep m μ
) {S T : Set ι} (hST : Disjoint S T) : Indep (⨆ i in S, m i) (⨆ i in T, m i) μ
参数：h_le : forall i, m i <= _mΩ；h_indep : iIndep m μ；hST : Disjoint S T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.indep_iSup_of_disjoint`：indep_iSup_of_disjoint 
{m : ι -> MeasurableSpace Ω} (h_le : forall i, m i <= _mΩ) (h_indep : iIndep m κ
 μ) {S T : Set ι} (hST : Disjoint S T…
-/
theorem indep_iSup_of_disjoint
    (h_le : ∀ i, m i ≤ _mΩ) (h_indep : iIndep m μ) {S T : Set ι} (hST : Disjoint S T) :
    Indep (⨆ i ∈ S, m i) (⨆ i ∈ T, m i) μ :=
  Kernel.indep_iSup_of_disjoint h_le h_indep hST
/-
**ProbabilityTheory.indep_iSup_of_directed_le** 是 Mathlib 中的一个定理，位于命名空间 `Probabi
lityTheory`。
形式化陈述：indep_iSup_of_directed_le [IsZeroOrProbabilityMeasure μ] (h_indep : forall
 i, Indep (m i) m1 μ) (h_le : forall i, m i <= _mΩ) (h_le' : m1 <= _mΩ) (hm : Di
rected (· <= ·) m) : Indep (⨆ i, m i) m1 μ
参数：h_indep : forall i, Indep (m i) m1 μ；h_le : forall i, m i <= _mΩ；h_le' : m1 <
= _mΩ；hm : Directed (· <= ·) m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.indep_iSup_of_directed_le`：indep_iSup_of_direct
ed_le {Ω} {m : ι -> MeasurableSpace Ω} {m' m0 : MeasurableSpace Ω} {κ : Kernel α
 Ω} {μ : Measure α} [IsZeroOrMarkovKerne…
· 使用定理 `ProbabilityTheory.Kernel.const.instIsZeroOrMarkovKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μβ : Measure
Theory.Measure β}   [hμβ : MeasureTheory.IsZe…
-/
theorem indep_iSup_of_directed_le
    [IsZeroOrProbabilityMeasure μ] (h_indep : ∀ i, Indep (m i) m1 μ)
    (h_le : ∀ i, m i ≤ _mΩ) (h_le' : m1 ≤ _mΩ) (hm : Directed (· ≤ ·) m) :
    Indep (⨆ i, m i) m1 μ :=
  Kernel.indep_iSup_of_directed_le h_indep h_le h_le' hm
/-
**ProbabilityTheory.iIndepSet.indep_generateFrom_lt** 是 Mathlib 中的一个定理，位于命名空间 `P
robabilityTheory.iIndepSet`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {_mΩ : MeasurableSpace Ω} {μ : MeasureTheo
ry.Measure Ω} [inst : Preorder ι]   {s : ι → Set Ω},   (∀ (n : ι), MeasurableSet
 (s n)) →     ProbabilityTheory.iIndepSet s μ →       ∀ (i : ι),         Probabi
lityTheory.Indep (MeasurableSpace.generateFrom {s i})           (MeasurableSpace
.generateFrom {t | ∃ j < i, s j = t}) μ
参数：∀ (n : ι), MeasurableSet (s n)；i : ι；MeasurableSpace.generateFrom {s i}；Measu
rableSpace.generateFrom {t | ∃ j < i, s j = t}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepSet.indep_generateFrom_lt`：∀ {α : Type u_
1} {Ω : Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {_mΩ : MeasurableSpac
e Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ :…
-/
theorem iIndepSet.indep_generateFrom_lt [Preorder ι] {s : ι → Set Ω}
    (hsm : ∀ n, MeasurableSet (s n)) (hs : iIndepSet s μ) (i : ι) :
    Indep (generateFrom {s i}) (generateFrom { t | ∃ j < i, s j = t }) μ :=
  Kernel.iIndepSet.indep_generateFrom_lt hsm hs i
/-
**ProbabilityTheory.iIndepSet.indep_generateFrom_le** 是 Mathlib 中的一个定理，位于命名空间 `P
robabilityTheory.iIndepSet`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {_mΩ : MeasurableSpace Ω} {μ : MeasureTheo
ry.Measure Ω} [inst : Preorder ι]   {s : ι → Set Ω},   (∀ (n : ι), MeasurableSet
 (s n)) →     ProbabilityTheory.iIndepSet s μ →       ∀ (i : ι) {k : ι},        
 i < k →           ProbabilityTheory.Indep (MeasurableSpace.generateFrom {s k}) 
            (MeasurableSpace.generateFrom {t | ∃ j ≤ i, s j = t}) μ
参数：∀ (n : ι), MeasurableSet (s n)；i : ι；MeasurableSpace.generateFrom {s k}；Measu
rableSpace.generateFrom {t | ∃ j ≤ i, s j = t}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepSet.indep_generateFrom_le`：∀ {α : Type u_
1} {Ω : Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {_mΩ : MeasurableSpac
e Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ :…
-/
theorem iIndepSet.indep_generateFrom_le [Preorder ι]
    {s : ι → Set Ω}
    (hsm : ∀ n, MeasurableSet (s n)) (hs : iIndepSet s μ) (i : ι) {k : ι} (hk : i < k) :
    Indep (generateFrom {s k}) (generateFrom { t | ∃ j ≤ i, s j = t }) μ :=
  Kernel.iIndepSet.indep_generateFrom_le hsm hs i hk
/-
**ProbabilityTheory.iIndepSet.indep_generateFrom_le_nat** 是 Mathlib 中的一个定理，位于命名空
间 `ProbabilityTheory.iIndepSet`。
形式化陈述：∀ {Ω : Type u_1} {_mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {
s : ℕ → Set Ω},   (∀ (n : ℕ), MeasurableSet (s n)) →     ProbabilityTheory.iInde
pSet s μ →       ∀ (n : ℕ),         ProbabilityTheory.Indep (MeasurableSpace.gen
erateFrom {s (n + 1)})           (MeasurableSpace.generateFrom {t | ∃ k ≤ n, s k
 = t}) μ
参数：∀ (n : ℕ), MeasurableSet (s n)；n : ℕ；MeasurableSpace.generateFrom {s (n + 1)}
；MeasurableSpace.generateFrom {t | ∃ k ≤ n, s k = t}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepSet.indep_generateFrom_le_nat`：∀ {α : Typ
e u_1} {Ω : Type u_2} {_mα : MeasurableSpace α} {_mΩ : MeasurableSpace Ω} {κ : P
robabilityTheory.Kernel α Ω}   {μ : MeasureTheory.…
-/
theorem iIndepSet.indep_generateFrom_le_nat {s : ℕ → Set Ω}
    (hsm : ∀ n, MeasurableSet (s n)) (hs : iIndepSet s μ) (n : ℕ) :
    Indep (generateFrom {s (n + 1)}) (generateFrom { t | ∃ k ≤ n, s k = t }) μ :=
  Kernel.iIndepSet.indep_generateFrom_le_nat hsm hs n
/-
**ProbabilityTheory.indep_iSup_of_monotone** 是 Mathlib 中的一个定理，位于命名空间 `Probabilit
yTheory`。
形式化陈述：indep_iSup_of_monotone [SemilatticeSup ι] [IsZeroOrProbabilityMeasure μ] (
h_indep : forall i, Indep (m i) m1 μ) (h_le : forall i, m i <= _mΩ) (h_le' : m1 
<= _mΩ) (hm : Monotone m) : Indep (⨆ i, m i) m1 μ
参数：h_indep : forall i, Indep (m i) m1 μ；h_le : forall i, m i <= _mΩ；h_le' : m1 <
= _mΩ；hm : Monotone m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.indep_iSup_of_monotone`：indep_iSup_of_monotone 
[SemilatticeSup ι] {Ω} {m : ι -> MeasurableSpace Ω} {m' m0 : MeasurableSpace Ω} 
{κ : Kernel α Ω} {μ : Measure α} [IsZ…
· 使用定理 `ProbabilityTheory.Kernel.const.instIsZeroOrMarkovKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μβ : Measure
Theory.Measure β}   [hμβ : MeasureTheory.IsZe…
-/
theorem indep_iSup_of_monotone [SemilatticeSup ι] [IsZeroOrProbabilityMeasure μ]
    (h_indep : ∀ i, Indep (m i) m1 μ) (h_le : ∀ i, m i ≤ _mΩ) (h_le' : m1 ≤ _mΩ) (hm : Monotone m) :
    Indep (⨆ i, m i) m1 μ :=
  Kernel.indep_iSup_of_monotone h_indep h_le h_le' hm
/-
**ProbabilityTheory.indep_iSup_of_antitone** 是 Mathlib 中的一个定理，位于命名空间 `Probabilit
yTheory`。
形式化陈述：indep_iSup_of_antitone [SemilatticeInf ι] [IsZeroOrProbabilityMeasure μ] (
h_indep : forall i, Indep (m i) m1 μ) (h_le : forall i, m i <= _mΩ) (h_le' : m1 
<= _mΩ) (hm : Antitone m) : Indep (⨆ i, m i) m1 μ
参数：h_indep : forall i, Indep (m i) m1 μ；h_le : forall i, m i <= _mΩ；h_le' : m1 <
= _mΩ；hm : Antitone m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.indep_iSup_of_antitone`：indep_iSup_of_antitone 
[SemilatticeInf ι] {Ω} {m : ι -> MeasurableSpace Ω} {m' m0 : MeasurableSpace Ω} 
{κ : Kernel α Ω} {μ : Measure α} [IsZ…
· 使用定理 `ProbabilityTheory.Kernel.const.instIsZeroOrMarkovKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μβ : Measure
Theory.Measure β}   [hμβ : MeasureTheory.IsZe…
-/
theorem indep_iSup_of_antitone [SemilatticeInf ι] [IsZeroOrProbabilityMeasure μ]
    (h_indep : ∀ i, Indep (m i) m1 μ) (h_le : ∀ i, m i ≤ _mΩ) (h_le' : m1 ≤ _mΩ) (hm : Antitone m) :
    Indep (⨆ i, m i) m1 μ :=
  Kernel.indep_iSup_of_antitone h_indep h_le h_le' hm
/-
**ProbabilityTheory.iIndepSets.piiUnionInter_of_notMem** 是 Mathlib 中的一个定理，位于命名空间
 `ProbabilityTheory.iIndepSets`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {_mΩ : MeasurableSpace Ω} {μ : MeasureTheo
ry.Measure Ω} {π : ι → Set (Set Ω)} {a : ι}   {S : Finset ι}, ProbabilityTheory.
iIndepSets π μ → a ∉ S → ProbabilityTheory.IndepSets (piiUnionInter π ↑S) (π a) 
μ
参数：Set Ω；piiUnionInter π ↑S；π a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepSets.piiUnionInter_of_notMem`：∀ {α : Type
 u_1} {Ω : Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {_mΩ : MeasurableS
pace Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ :…
-/
theorem iIndepSets.piiUnionInter_of_notMem {π : ι → Set (Set Ω)} {a : ι} {S : Finset ι}
    (hp_ind : iIndepSets π μ) (haS : a ∉ S) :
    IndepSets (piiUnionInter π S) (π a) μ :=
  Kernel.iIndepSets.piiUnionInter_of_notMem hp_ind haS

/-- The measurable space structures generated by independent pi-systems are independent. -/
/-
**ProbabilityTheory.iIndepSets.iIndep** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheo
ry.iIndepSets`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {m : ι → MeasurableSpace Ω} {_mΩ : Measura
bleSpace Ω} {μ : MeasureTheory.Measure Ω},   (∀ (i : ι), m i ≤ _mΩ) →     ∀ (π :
 ι → Set (Set Ω)),       (∀ (n : ι), IsPiSystem (π n)) →         (∀ (i : ι), m i
 = MeasurableSpace.generateFrom (π i)) →           ProbabilityTheory.iIndepSets 
π μ → ProbabilityTheory.iIndep m μ
参数：∀ (i : ι), m i ≤ _mΩ；π : ι → Set (Set Ω)；∀ (n : ι), IsPiSystem (π n)；∀ (i : ι
), m i = MeasurableSpace.generateFrom (π i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepSets.iIndep`：∀ {α : Type u_1} {Ω : Type u
_2} {ι : Type u_3} {_mα : MeasurableSpace α} {_mΩ : MeasurableSpace Ω}   {κ : Pr
obabilityTheory.Kernel α Ω} {μ :…

--- 原说明 ---
The measurable space structures generated by independent pi-systems are independ
ent.
-/
theorem iIndepSets.iIndep
    (h_le : ∀ i, m i ≤ _mΩ) (π : ι → Set (Set Ω)) (h_pi : ∀ n, IsPiSystem (π n))
    (h_generate : ∀ i, m i = generateFrom (π i)) (h_ind : iIndepSets π μ) :
    iIndep m μ :=
  Kernel.iIndepSets.iIndep m h_le π h_pi h_generate h_ind

end FromPiSystemsToMeasurableSpaces

section IndepSet

/-! ### Independence of measurable sets

We prove the following equivalences on `IndepSet`, for measurable sets `s, t`.
* `IndepSet s t μ ↔ μ (s ∩ t) = μ s * μ t`,
* `IndepSet s t μ ↔ IndepSets {s} {t} μ`.
-/


variable {m₁ m₂ _mΩ : MeasurableSpace Ω} {μ : Measure Ω} {s t : Set Ω} (S T : Set (Set Ω))

/-
**ProbabilityTheory.indepSet_iff_indepSets_singleton** 是 Mathlib 中的一个定理，位于命名空间 `
ProbabilityTheory`。
形式化陈述：indepSet_iff_indepSets_singleton (hs_meas : MeasurableSet s) (ht_meas : Me
asurableSet t) (μ : Measure Ω
参数：hs_meas : MeasurableSet s；ht_meas : MeasurableSet t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.indepSet_iff_indepSets_singleton`：indepSet_iff_
indepSets_singleton {m0 : MeasurableSpace Ω} (hs_meas : MeasurableSet s) (ht_mea
s : MeasurableSet t) (κ : Kernel α Ω) (μ : Meas…
· 使用定理 `ProbabilityTheory.Kernel.const.instIsZeroOrMarkovKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μβ : Measure
Theory.Measure β}   [hμβ : MeasureTheory.IsZe…
-/
theorem indepSet_iff_indepSets_singleton (hs_meas : MeasurableSet s)
    (ht_meas : MeasurableSet t) (μ : Measure Ω := by volume_tac)
    [IsZeroOrProbabilityMeasure μ] : IndepSet s t μ ↔ IndepSets {s} {t} μ :=
  Kernel.indepSet_iff_indepSets_singleton hs_meas ht_meas _ _
/-
**ProbabilityTheory.indepSet_iff_measure_inter_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 
`ProbabilityTheory`。
形式化陈述：indepSet_iff_measure_inter_eq_mul (hs_meas : MeasurableSet s) (ht_meas : M
easurableSet t) (μ : Measure Ω
参数：hs_meas : MeasurableSet s；ht_meas : MeasurableSet t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `ProbabilityTheory.indepSet_iff_indepSets_singleton`：indepSet_iff_indepSe
ts_singleton (hs_meas : MeasurableSet s) (ht_meas : MeasurableSet t) (μ : Measur
e Ω
· 使用定理 `ProbabilityTheory.indepSets_singleton_iff`：indepSets_singleton_iff {s t 
: Set Ω} : IndepSets {s} {t} μ ↔ μ (s inter t) = μ s * μ t
-/
theorem indepSet_iff_measure_inter_eq_mul (hs_meas : MeasurableSet s)
    (ht_meas : MeasurableSet t) (μ : Measure Ω := by volume_tac)
    [IsZeroOrProbabilityMeasure μ] : IndepSet s t μ ↔ μ (s ∩ t) = μ s * μ t :=
  (indepSet_iff_indepSets_singleton hs_meas ht_meas μ).trans indepSets_singleton_iff
/-
**ProbabilityTheory.IndepSet.measure_inter_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 `Pro
babilityTheory.IndepSet`。
形式化陈述：∀ {Ω : Type u_1} {_mΩ : MeasurableSpace Ω} {s t : Set Ω} {μ : MeasureTheor
y.Measure Ω},   ProbabilityTheory.IndepSet s t μ → μ (s ∩ t) = μ s * μ t
参数：s ∩ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ae_dirac_eq`：ae_dirac_eq [MeasurableSingletonClass α] (a :
 α) : ae (dirac a) = pure a
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `standardBorelSpace_of_discreteMeasurableSpace`：∀ {α : Type u_1} [inst : 
MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α], StandardBorelSpace
 α
· 使用定理 `instDiscreteMeasurableSpace`：∀ {α : Type u_1}, DiscreteMeasurableSpace α
· 使用定理 `instCountablePUnit`：Countable PUnit.{u}
· 使用定理 `ProbabilityTheory.Kernel.IndepSet.measure_inter_eq_mul`：∀ {α : Type u_1}
 {Ω : Type u_2} {_mα : MeasurableSpace α} {s t : Set Ω} {_m0 : MeasurableSpace Ω
}   (κ : ProbabilityTheory.Kernel α Ω) (μ : …
-/
lemma IndepSet.measure_inter_eq_mul {μ : Measure Ω} (h : IndepSet s t μ) :
    μ (s ∩ t) = μ s * μ t := by
  simpa using Kernel.IndepSet.measure_inter_eq_mul _ _ h
/-
**ProbabilityTheory.IndepSets.indepSet_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Probabi
lityTheory.IndepSets`。
形式化陈述：∀ {Ω : Type u_1} {_mΩ : MeasurableSpace Ω} {s t : Set Ω} (S T : Set (Set Ω
)),   s ∈ S →     t ∈ T →       MeasurableSet s →         MeasurableSet t →     
      ∀ (μ : autoParam (MeasureTheory.Measure Ω) ProbabilityTheory.IndepSets.ind
epSet_of_mem._auto_1)             [MeasureTheory.IsZeroOrProbabilityMeasure μ], 
            ProbabilityTheory.IndepSets S T μ → ProbabilityTheory.IndepSet s t μ
参数：S T : Set (Set Ω)；μ : autoParam (MeasureTheory.Measure Ω) ProbabilityTheory.I
ndepSets.indepSet_of_mem._auto_1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IndepSets.indepSet_of_mem`：∀ {α : Type u_1} {Ω 
: Type u_2} {_mα : MeasurableSpace α} {s t : Set Ω} (S T : Set (Set Ω)) {_m0 : M
easurableSpace Ω},   s ∈ S →     t ∈ T →…
· 使用定理 `ProbabilityTheory.Kernel.const.instIsZeroOrMarkovKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μβ : Measure
Theory.Measure β}   [hμβ : MeasureTheory.IsZe…
-/
theorem IndepSets.indepSet_of_mem (hs : s ∈ S) (ht : t ∈ T)
    (hs_meas : MeasurableSet s) (ht_meas : MeasurableSet t)
    (μ : Measure Ω := by volume_tac) [IsZeroOrProbabilityMeasure μ]
    (h_indep : IndepSets S T μ) :
    IndepSet s t μ :=
  Kernel.IndepSets.indepSet_of_mem _ _ hs ht hs_meas ht_meas _ _ h_indep
/-
**ProbabilityTheory.Indep.indepSet_of_measurableSet** 是 Mathlib 中的一个定理，位于命名空间 `P
robabilityTheory.Indep`。
形式化陈述：∀ {Ω : Type u_1} {m₁ m₂ _mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measur
e Ω},   ProbabilityTheory.Indep m₁ m₂ μ →     ∀ {s t : Set Ω}, MeasurableSet s →
 MeasurableSet t → ProbabilityTheory.IndepSet s t μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.Indep.indepSet_of_measurableSet`：∀ {α : Type u_
1} {Ω : Type u_2} {_mα : MeasurableSpace α} {m₁ m₂ x : MeasurableSpace Ω}   {κ :
 ProbabilityTheory.Kernel α Ω} {μ : MeasureThe…
-/
theorem Indep.indepSet_of_measurableSet
    (h_indep : Indep m₁ m₂ μ) {s t : Set Ω} (hs : MeasurableSet[m₁] s) (ht : MeasurableSet[m₂] t) :
    IndepSet s t μ :=
  Kernel.Indep.indepSet_of_measurableSet h_indep hs ht
/-
**ProbabilityTheory.indep_iff_forall_indepSet** 是 Mathlib 中的一个定理，位于命名空间 `Probabi
lityTheory`。
形式化陈述：indep_iff_forall_indepSet (μ : Measure Ω) : Indep m₁ m₂ μ ↔ forall s t, Me
asurableSet[m₁] s -> MeasurableSet[m₂] t -> IndepSet s t μ
参数：μ : Measure Ω。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.indep_iff_forall_indepSet`：indep_iff_forall_ind
epSet (m₁ m₂ : MeasurableSpace Ω) {_m0 : MeasurableSpace Ω} (κ : Kernel α Ω) (μ 
: Measure α) : Indep m₁ m₂ κ μ ↔ forall …
-/
theorem indep_iff_forall_indepSet (μ : Measure Ω) :
    Indep m₁ m₂ μ ↔ ∀ s t, MeasurableSet[m₁] s → MeasurableSet[m₂] t → IndepSet s t μ :=
  Kernel.indep_iff_forall_indepSet m₁ m₂ _ _
/-
**ProbabilityTheory.iIndep_comap_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityT
heory`。
形式化陈述：iIndep_comap_mem_iff {f : ι -> Set Ω} : iIndep (fun i => MeasurableSpace.c
omap (· in f i) ⊤) μ ↔ iIndepSet f μ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndep_comap_mem_iff`：iIndep_comap_mem_iff {f :
 ι -> Set Ω} {_mΩ : MeasurableSpace Ω} {κ : Kernel α Ω} {μ : Measure α} : iIndep
 (fun i => MeasurableSpace.comap (·…
-/
theorem iIndep_comap_mem_iff {f : ι → Set Ω} :
    iIndep (fun i => MeasurableSpace.comap (· ∈ f i) ⊤) μ ↔ iIndepSet f μ :=
  Kernel.iIndep_comap_mem_iff

alias ⟨_, iIndepSet.iIndep_comap_mem⟩ := iIndep_comap_mem_iff
/-
**ProbabilityTheory.iIndepSets_singleton_iff** 是 Mathlib 中的一个定理，位于命名空间 `Probabil
ityTheory`。
形式化陈述：iIndepSets_singleton_iff {s : ι -> Set Ω} : iIndepSets (fun i => {s i}) μ 
↔ forall t, μ (⋂ i in t, s i) = ∏ i in t, μ (s i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `MeasureTheory.ae_dirac_eq`：ae_dirac_eq [MeasurableSingletonClass α] (a :
 α) : ae (dirac a) = pure a
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `standardBorelSpace_of_discreteMeasurableSpace`：∀ {α : Type u_1} [inst : 
MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α], StandardBorelSpace
 α
· 使用定理 `instDiscreteMeasurableSpace`：∀ {α : Type u_1}, DiscreteMeasurableSpace α
· 使用定理 `instCountablePUnit`：Countable PUnit.{u}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem iIndepSets_singleton_iff {s : ι → Set Ω} :
    iIndepSets (fun i ↦ {s i}) μ ↔ ∀ t, μ (⋂ i ∈ t, s i) = ∏ i ∈ t, μ (s i) := by
  simp_rw [iIndepSets, Kernel.iIndepSets_singleton_iff, ae_dirac_eq, Filter.eventually_pure,
    Kernel.const_apply]
/-
**ProbabilityTheory.iIndepSet.meas_biInter** 是 Mathlib 中的一个定理，位于命名空间 `Probabilit
yTheory.iIndepSet`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {_mΩ : MeasurableSpace Ω} {μ : MeasureTheo
ry.Measure Ω} {f : ι → Set Ω},   ProbabilityTheory.iIndepSet f μ → ∀ (s : Finset
 ι), μ (⋂ i ∈ s, f i) = ∏ i ∈ s, μ (f i)
参数：s : Finset ι；⋂ i ∈ s, f i；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ae_dirac_eq`：ae_dirac_eq [MeasurableSingletonClass α] (a :
 α) : ae (dirac a) = pure a
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `standardBorelSpace_of_discreteMeasurableSpace`：∀ {α : Type u_1} [inst : 
MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α], StandardBorelSpace
 α
· 使用定理 `instDiscreteMeasurableSpace`：∀ {α : Type u_1}, DiscreteMeasurableSpace α
· 使用定理 `instCountablePUnit`：Countable PUnit.{u}
· 使用定理 `ProbabilityTheory.Kernel.iIndepSet.meas_biInter`：∀ {α : Type u_1} {Ω : T
ype u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {_mΩ : MeasurableSpace Ω}   {κ
 : ProbabilityTheory.Kernel α Ω} {μ :…
-/
theorem iIndepSet.meas_biInter {f : ι → Set Ω} (h : iIndepSet f μ) (s : Finset ι) :
    μ (⋂ i ∈ s, f i) = ∏ i ∈ s, μ (f i) := by
  simpa using Kernel.iIndepSet.meas_biInter h s
/-
**ProbabilityTheory.iIndepSet_iff_iIndepSets_singleton** 是 Mathlib 中的一个定理，位于命名空间
 `ProbabilityTheory`。
形式化陈述：iIndepSet_iff_iIndepSets_singleton {f : ι -> Set Ω} (hf : forall i, Measur
ableSet (f i)) : iIndepSet f μ ↔ iIndepSets (fun i => {f i}) μ
参数：hf : forall i, MeasurableSet (f i)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepSet_iff_iIndepSets_singleton`：iIndepSet_i
ff_iIndepSets_singleton {_mΩ : MeasurableSpace Ω} {κ : Kernel α Ω} {μ : Measure 
α} {f : ι -> Set Ω} (hf : forall i, MeasurableSet…
-/
theorem iIndepSet_iff_iIndepSets_singleton {f : ι → Set Ω} (hf : ∀ i, MeasurableSet (f i)) :
    iIndepSet f μ ↔ iIndepSets (fun i ↦ {f i}) μ :=
  Kernel.iIndepSet_iff_iIndepSets_singleton hf
/-
**ProbabilityTheory.iIndepSet_iff_meas_biInter** 是 Mathlib 中的一个定理，位于命名空间 `Probab
ilityTheory`。
形式化陈述：iIndepSet_iff_meas_biInter {f : ι -> Set Ω} (hf : forall i, MeasurableSet 
(f i)) : iIndepSet f μ ↔ forall s, μ (⋂ i in s, f i) = ∏ i in s, μ (f i)
参数：hf : forall i, MeasurableSet (f i)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.iIndepSet_iff_meas_biInter`：iIndepSet_iff_meas_
biInter {_mΩ : MeasurableSpace Ω} {κ : Kernel α Ω} {μ : Measure α} {f : ι -> Set
 Ω} (hf : forall i, MeasurableSet (f i)) …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `MeasureTheory.ae_dirac_eq`：ae_dirac_eq [MeasurableSingletonClass α] (a :
 α) : ae (dirac a) = pure a
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `standardBorelSpace_of_discreteMeasurableSpace`：∀ {α : Type u_1} [inst : 
MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α], StandardBorelSpace
 α
· 使用定理 `instDiscreteMeasurableSpace`：∀ {α : Type u_1}, DiscreteMeasurableSpace α
· 使用定理 `instCountablePUnit`：Countable PUnit.{u}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem iIndepSet_iff_meas_biInter {f : ι → Set Ω} (hf : ∀ i, MeasurableSet (f i)) :
    iIndepSet f μ ↔ ∀ s, μ (⋂ i ∈ s, f i) = ∏ i ∈ s, μ (f i) := by
  simp_rw [iIndepSet, Kernel.iIndepSet_iff_meas_biInter hf, ae_dirac_eq, Filter.eventually_pure,
    Kernel.const_apply]
/-
**ProbabilityTheory.iIndepSets.iIndepSet_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Proba
bilityTheory.iIndepSets`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {_mΩ : MeasurableSpace Ω} {μ : MeasureTheo
ry.Measure Ω} {π : ι → Set (Set Ω)}   {f : ι → Set Ω},   (∀ (i : ι), f i ∈ π i) 
→     (∀ (i : ι), MeasurableSet (f i)) → ProbabilityTheory.iIndepSets π μ → Prob
abilityTheory.iIndepSet f μ
参数：Set Ω；∀ (i : ι), f i ∈ π i；∀ (i : ι), MeasurableSet (f i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepSets.iIndepSet_of_mem`：∀ {α : Type u_1} {
Ω : Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {_mΩ : MeasurableSpace Ω}
   {κ : ProbabilityTheory.Kernel α Ω} {μ :…
-/
theorem iIndepSets.iIndepSet_of_mem {π : ι → Set (Set Ω)} {f : ι → Set Ω}
    (hfπ : ∀ i, f i ∈ π i) (hf : ∀ i, MeasurableSet (f i))
    (hπ : iIndepSets π μ) : iIndepSet f μ :=
  Kernel.iIndepSets.iIndepSet_of_mem hfπ hf hπ

end IndepSet

section IndepFun

/-! ### Independence of random variables

-/


variable {β β' γ γ' : Type*} {_mΩ : MeasurableSpace Ω} {μ : Measure Ω} {f : Ω → β} {g : Ω → β'}

/-
**ProbabilityTheory.indepFun_iff_measure_inter_preimage_eq_mul** 是 Mathlib 中的一个定
理，位于命名空间 `ProbabilityTheory`。
形式化陈述：indepFun_iff_measure_inter_preimage_eq_mul {mβ : MeasurableSpace β} {mβ' :
 MeasurableSpace β'} : f ⟂ᵢ[μ] g ↔ forall s t, MeasurableSet s -> MeasurableSet 
t -> μ (f ⁻¹' s inter g ⁻¹' t) = μ (f ⁻¹' s) * μ (g ⁻¹' t)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `MeasureTheory.ae_dirac_eq`：ae_dirac_eq [MeasurableSingletonClass α] (a :
 α) : ae (dirac a) = pure a
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `standardBorelSpace_of_discreteMeasurableSpace`：∀ {α : Type u_1} [inst : 
MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α], StandardBorelSpace
 α
· 使用定理 `instDiscreteMeasurableSpace`：∀ {α : Type u_1}, DiscreteMeasurableSpace α
· 使用定理 `instCountablePUnit`：Countable PUnit.{u}
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem indepFun_iff_measure_inter_preimage_eq_mul {mβ : MeasurableSpace β}
    {mβ' : MeasurableSpace β'} :
    f ⟂ᵢ[μ] g ↔
      ∀ s t, MeasurableSet s → MeasurableSet t
        → μ (f ⁻¹' s ∩ g ⁻¹' t) = μ (f ⁻¹' s) * μ (g ⁻¹' t) := by
  simp only [IndepFun, Kernel.indepFun_iff_measure_inter_preimage_eq_mul, ae_dirac_eq,
    Filter.eventually_pure, Kernel.const_apply]

alias ⟨IndepFun.measure_inter_preimage_eq_mul, _⟩ := indepFun_iff_measure_inter_preimage_eq_mul
/-
**ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul** 是 Mathlib 中的一个
定理，位于命名空间 `ProbabilityTheory`。
形式化陈述：iIndepFun_iff_measure_inter_preimage_eq_mul {ι : Type*} {β : ι -> Type*} {
m : forall x, MeasurableSpace (β x)} {f : forall i, Ω -> β i} : iIndepFun f μ ↔ 
forall (S : Finset ι) {sets : forall i : ι, Set (β i)} (_H : forall i, i in S ->
 MeasurableSet[m i] (sets i)), μ (⋂ i in S, f i ⁻¹' sets i) = ∏ i in S, μ (f i ⁻
¹' sets i)
参数：β x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `MeasureTheory.ae_dirac_eq`：ae_dirac_eq [MeasurableSingletonClass α] (a :
 α) : ae (dirac a) = pure a
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `standardBorelSpace_of_discreteMeasurableSpace`：∀ {α : Type u_1} [inst : 
MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α], StandardBorelSpace
 α
· 使用定理 `instDiscreteMeasurableSpace`：∀ {α : Type u_1}, DiscreteMeasurableSpace α
· 使用定理 `instCountablePUnit`：Countable PUnit.{u}
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem iIndepFun_iff_measure_inter_preimage_eq_mul {ι : Type*} {β : ι → Type*}
    {m : ∀ x, MeasurableSpace (β x)} {f : ∀ i, Ω → β i} :
    iIndepFun f μ ↔
      ∀ (S : Finset ι) {sets : ∀ i : ι, Set (β i)} (_H : ∀ i, i ∈ S → MeasurableSet[m i] (sets i)),
        μ (⋂ i ∈ S, f i ⁻¹' sets i) = ∏ i ∈ S, μ (f i ⁻¹' sets i) := by
  simp only [iIndepFun, Kernel.iIndepFun_iff_measure_inter_preimage_eq_mul, ae_dirac_eq,
    Filter.eventually_pure, Kernel.const_apply]

alias ⟨iIndepFun.measure_inter_preimage_eq_mul, _⟩ := iIndepFun_iff_measure_inter_preimage_eq_mul
/-
**ProbabilityTheory.iIndepFun_congr** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory
`。
形式化陈述：iIndepFun_congr {β : ι -> Type*} {mβ : forall i, MeasurableSpace (β i)} {f
 g : Π i, Ω -> β i} (h : forall i, f i =ᵐ[μ] g i) : iIndepFun f μ ↔ iIndepFun g 
μ
参数：β i；h : forall i, f i =ᵐ[μ] g i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun_congr'`：iIndepFun_congr' {β : ι -> Ty
pe*} {mβ : forall i, MeasurableSpace (β i)} {f g : Π i, Ω -> β i} (h : forall i,
 forallᵐ a ∂μ, f i =ᵐ[κ a] g i)…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MeasureTheory.ae_dirac_eq`：ae_dirac_eq [MeasurableSingletonClass α] (a :
 α) : ae (dirac a) = pure a
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `standardBorelSpace_of_discreteMeasurableSpace`：∀ {α : Type u_1} [inst : 
MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α], StandardBorelSpace
 α
· 使用定理 `instDiscreteMeasurableSpace`：∀ {α : Type u_1}, DiscreteMeasurableSpace α
· 使用定理 `instCountablePUnit`：Countable PUnit.{u}
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem iIndepFun_congr {β : ι → Type*} {mβ : ∀ i, MeasurableSpace (β i)}
    {f g : Π i, Ω → β i} (h : ∀ i, f i =ᵐ[μ] g i) :
    iIndepFun f μ ↔ iIndepFun g μ := Kernel.iIndepFun_congr' (by simp [h])

alias ⟨iIndepFun.congr, _⟩ := iIndepFun_congr

nonrec lemma iIndepFun.comp {β γ : ι → Type*} {mβ : ∀ i, MeasurableSpace (β i)}
    {mγ : ∀ i, MeasurableSpace (γ i)} {f : ∀ i, Ω → β i}
    (h : iIndepFun f μ) (g : ∀ i, β i → γ i) (hg : ∀ i, Measurable (g i)) :
    iIndepFun (fun i ↦ g i ∘ f i) μ := h.comp _ hg

nonrec lemma iIndepFun.comp₀ {β γ : ι → Type*} {mβ : ∀ i, MeasurableSpace (β i)}
    {mγ : ∀ i, MeasurableSpace (γ i)} {f : ∀ i, Ω → β i}
    (h : iIndepFun f μ) (g : ∀ i, β i → γ i)
    (hf : ∀ i, AEMeasurable (f i) μ) (hg : ∀ i, AEMeasurable (g i) (μ.map (f i))) :
    iIndepFun (fun i ↦ g i ∘ f i) μ := h.comp₀ _ (by simp [hf]) (by simp [hg])
/-
**ProbabilityTheory.indepFun_iff_indepSet_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Pr
obabilityTheory`。
形式化陈述：indepFun_iff_indepSet_preimage {mβ : MeasurableSpace β} {mβ' : MeasurableS
pace β'} [IsZeroOrProbabilityMeasure μ] (hf : Measurable f) (hg : Measurable g) 
: f ⟂ᵢ[μ] g ↔ forall s t, MeasurableSet s -> MeasurableSet t -> IndepSet (f ⁻¹' 
s) (g ⁻¹' t) μ
参数：hf : Measurable f；hg : Measurable g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.indepFun_iff_indepSet_preimage`：indepFun_iff_in
depSet_preimage {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'} [IsZeroOrMar
kovKernel κ] (hf : Measurable f) (hg : Measur…
· 使用定理 `ProbabilityTheory.Kernel.const.instIsZeroOrMarkovKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μβ : Measure
Theory.Measure β}   [hμβ : MeasureTheory.IsZe…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem indepFun_iff_indepSet_preimage {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    [IsZeroOrProbabilityMeasure μ] (hf : Measurable f) (hg : Measurable g) :
    f ⟂ᵢ[μ] g ↔
      ∀ s t, MeasurableSet s → MeasurableSet t → IndepSet (f ⁻¹' s) (g ⁻¹' t) μ := by
  simp only [IndepFun, IndepSet, Kernel.indepFun_iff_indepSet_preimage hf hg]
/-
**ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map'** 是 Mathlib 中的一个定理，位于
命名空间 `ProbabilityTheory`。
形式化陈述：indepFun_iff_map_prod_eq_prod_map_map' {mβ : MeasurableSpace β} {mβ' : Mea
surableSpace β'} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) (σf : SigmaFini
te (μ.map f)) (σg : SigmaFinite (μ.map g)) : f ⟂ᵢ[μ] g ↔ μ.map (fun ω => (f ω, g
 ω)) = (μ.map f).prod (μ.map g)
参数：hf : AEMeasurable f μ；hg : AEMeasurable g μ；σf : SigmaFinite (μ.map f)；σg : S
igmaFinite (μ.map g)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.indepFun_iff_measure_inter_preimage_eq_mul`：indepFun_i
ff_measure_inter_preimage_eq_mul {mβ : MeasurableSpace β} {mβ' : MeasurableSpace
 β'} : f ⟂ᵢ[μ] g ↔ forall s t, MeasurableSet s -> …
· 使用定理 `MeasureTheory.Measure.map_apply_of_aemeasurable`：map_apply_of_aemeasurab
le (hf : AEMeasurable f μ) {s : Set β} (hs : MeasurableSet s) : μ.map f s = μ (f
 ⁻¹' s)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AEMeasurable.prodMk`：prodMk {f : α -> β} {g : α -> γ} (hf : AEMeasurable
 f μ) (hg : AEMeasurable g μ) : AEMeasurable (fun x => (f x, g x)) μ
· 使用定理 `MeasurableSet.prod`：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace
 α} {mβ : MeasurableSpace β} {s : Set α} {t : Set β},   MeasurableSet s → Measur
ableSet …
· 使用定理 `MeasureTheory.Measure.prod_eq`：prod_eq {μ : Measure α} [SigmaFinite μ] {
ν : Measure β} [SigmaFinite ν] {μν : Measure (α × β)} (h : forall s t, Measurabl
eSet s -> Measurabl…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.Measure.prod_prod`：prod_prod (s : Set α) (t : Set β) : μ.p
rod ν (s ×ˢ t) = μ s * ν t
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
-/
theorem indepFun_iff_map_prod_eq_prod_map_map' {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (σf : SigmaFinite (μ.map f)) (σg : SigmaFinite (μ.map g)) :
    f ⟂ᵢ[μ] g ↔ μ.map (fun ω ↦ (f ω, g ω)) = (μ.map f).prod (μ.map g) := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  have h₀ {s : Set β} {t : Set β'} (hs : MeasurableSet s) (ht : MeasurableSet t) :
      μ (f ⁻¹' s) * μ (g ⁻¹' t) = μ.map f s * μ.map g t ∧
      μ (f ⁻¹' s ∩ g ⁻¹' t) = μ.map (fun ω ↦ (f ω, g ω)) (s ×ˢ t) :=
    ⟨by rw [Measure.map_apply_of_aemeasurable hf hs, Measure.map_apply_of_aemeasurable hg ht],
      (Measure.map_apply_of_aemeasurable (hf.prodMk hg) (hs.prod ht)).symm⟩
  constructor
  · refine fun h ↦ (Measure.prod_eq fun s t hs ht ↦ ?_).symm
    rw [← (h₀ hs ht).1, ← (h₀ hs ht).2, h s t hs ht]
  · intro h s t hs ht
    rw [(h₀ hs ht).1, (h₀ hs ht).2, h, Measure.prod_prod]
/-
**ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map** 是 Mathlib 中的一个定理，位于命
名空间 `ProbabilityTheory`。
形式化陈述：indepFun_iff_map_prod_eq_prod_map_map {mβ : MeasurableSpace β} {mβ' : Meas
urableSpace β'} [IsFiniteMeasure μ] (hf : AEMeasurable f μ) (hg : AEMeasurable g
 μ) : f ⟂ᵢ[μ] g ↔ μ.map (fun ω => (f ω, g ω)) = (μ.map f).prod (μ.map g)
参数：hf : AEMeasurable f μ；hg : AEMeasurable g μ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map'`：indepFun_iff_m
ap_prod_eq_prod_map_map' {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'} (hf
 : AEMeasurable f μ) (hg : AEMeasurable g μ) (…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasureTheory.Measure.isFiniteMeasure_map`：∀ {α : Type u_1} {β : Type u_
2} [mβ : MeasurableSpace β] {m : MeasurableSpace α} (μ : MeasureTheory.Measure α
)   [MeasureTheory.IsFiniteMeas…
-/
theorem indepFun_iff_map_prod_eq_prod_map_map {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    [IsFiniteMeasure μ] (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    f ⟂ᵢ[μ] g ↔ μ.map (fun ω ↦ (f ω, g ω)) = (μ.map f).prod (μ.map g) := by
  apply indepFun_iff_map_prod_eq_prod_map_map' hf hg <;> apply IsFiniteMeasure.toSigmaFinite

alias ⟨IndepFun.map_prod_eq_prod_map_map, _⟩ := indepFun_iff_map_prod_eq_prod_map_map

@[symm]
nonrec theorem IndepFun.symm {_ : MeasurableSpace β} {_ : MeasurableSpace β'}
    (hfg : f ⟂ᵢ[μ] g) : g ⟂ᵢ[μ] f := hfg.symm
/-
**ProbabilityTheory.IndepFun.congr** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory.
IndepFun`。
形式化陈述：∀ {Ω : Type u_1} {β : Type u_6} {β' : Type u_7} {_mΩ : MeasurableSpace Ω} 
{μ : MeasureTheory.Measure Ω} {f : Ω → β}   {g : Ω → β'} {mβ : MeasurableSpace β
} {mβ' : MeasurableSpace β'} {f' : Ω → β} {g' : Ω → β'},   ProbabilityTheory.Ind
epFun f g μ → f =ᵐ[μ] f' → g =ᵐ[μ] g' → ProbabilityTheory.IndepFun f' g' μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.Kernel.IndepFun.congr'`：∀ {α : Type u_1} {Ω : Type u_2
} {β : Type u_4} {β' : Type u_5} {mα : MeasurableSpace α} {mΩ : MeasurableSpace 
Ω}   {κ : ProbabilityTheory.Ke…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ae_dirac_eq`：ae_dirac_eq [MeasurableSingletonClass α] (a :
 α) : ae (dirac a) = pure a
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `standardBorelSpace_of_discreteMeasurableSpace`：∀ {α : Type u_1} [inst : 
MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α], StandardBorelSpace
 α
· 使用定理 `instDiscreteMeasurableSpace`：∀ {α : Type u_1}, DiscreteMeasurableSpace α
· 使用定理 `instCountablePUnit`：Countable PUnit.{u}
-/
theorem IndepFun.congr {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    {f' : Ω → β} {g' : Ω → β'} (hfg : f ⟂ᵢ[μ] g) (hf : f =ᵐ[μ] f') (hg : g =ᵐ[μ] g') :
    f' ⟂ᵢ[μ] g' := by
  refine Kernel.IndepFun.congr' hfg ?_ ?_ <;> simpa

section Prod

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
    {μ : Measure Ω} {ν : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {𝓧 𝓨 : Type*} [MeasurableSpace 𝓧] [MeasurableSpace 𝓨] {X : Ω → 𝓧} {Y : Ω' → 𝓨}

/-- Given random variables `X : Ω → 𝓧` and `Y : Ω' → 𝓨`, they are independent when viewed as random
variables defined on the product space `Ω × Ω'`. -/
/-
**ProbabilityTheory.indepFun_prod** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：indepFun_prod (mX : Measurable X) (mY : Measurable Y) : (fun ω => X ω.1) ⟂
ᵢ[μ.prod ν] (fun ω => Y ω.2)
参数：mX : Measurable X；mY : Measurable Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map`：indepFun_iff_ma
p_prod_eq_prod_map_map {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'} [IsFi
niteMeasure μ] (hf : AEMeasurable f μ) (hg : …
· 使用定理 `MeasureTheory.Measure.prod.instIsFiniteMeasure`：∀ {α : Type u_4} {β : Ty
pe u_5} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (μ : MeasureTheory.Mea
sure α)   (ν : MeasureTheory.Measure…
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `Measurable.comp_aemeasurable'`：Measurable.comp_aemeasurable' [Measurable
Space δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) :
 AEMeasurable (fun …
· 使用定理 `AEMeasurable.fst`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} {m0 : M
easurableSpace α} [inst : MeasurableSpace β]   [inst_1 : MeasurableSpace γ] {μ :
 Measu…
· 使用定理 `aemeasurable_id`：aemeasurable_id : AEMeasurable id μ
· 使用定理 `AEMeasurable.snd`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} {m0 : M
easurableSpace α} [inst : MeasurableSpace β]   [inst_1 : MeasurableSpace γ] {μ :
 Measu…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `MeasureTheory.Measure.map_map`：map_map {g : β -> γ} {f : α -> β} (hg : M
easurable g) (hf : Measurable f) : (μ.map f).map g = μ.map (g ∘ f)
· 使用定理 `measurable_fst`：measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.fst : α × β -> α)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.Measure.map_fst_prod`：∀ {α : Type u_1} {β : Type u_2} [ins
t : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μ : MeasureTheory.Measure α
}   {ν : MeasureTheory.M…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
· 使用定理 `MeasureTheory.Measure.map_snd_prod`：∀ {α : Type u_1} {β : Type u_2} [ins
t : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μ : MeasureTheory.Measure α
}   {ν : MeasureTheory.M…
· 使用定理 `MeasureTheory.Measure.map_prod_map`：map_prod_map {δ} [MeasurableSpace δ]
 {f : α -> β} {g : γ -> δ} (μa : Measure α) (μc : Measure γ) [SFinite μa] [SFini
te μc] (hf : Measurable …

--- 原说明 ---
Given random variables `X : Ω → 𝓧` and `Y : Ω' → 𝓨`, they are independent when v
iewed as random
variables defined on the product space `Ω × Ω'`.
-/
lemma indepFun_prod (mX : Measurable X) (mY : Measurable Y) :
    (fun ω ↦ X ω.1) ⟂ᵢ[μ.prod ν] (fun ω ↦ Y ω.2) := by
  refine indepFun_iff_map_prod_eq_prod_map_map (by fun_prop) (by fun_prop) |>.2 ?_
  convert! Measure.map_prod_map μ ν mX mY |>.symm
  · rw [← Function.comp_def, ← Measure.map_map mX measurable_fst, Measure.map_fst_prod,
      measure_univ, one_smul]
  · rw [← Function.comp_def, ← Measure.map_map mY measurable_snd, Measure.map_snd_prod,
      measure_univ, one_smul]

/-- Given random variables `X : Ω → 𝓧` and `Y : Ω' → 𝓨`, they are independent when viewed as random
variables defined on the product space `Ω × Ω'`. -/
/-
**ProbabilityTheory.indepFun_prod** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：indepFun_prod (mX : Measurable X) (mY : Measurable Y) : (fun ω => X ω.1) ⟂
ᵢ[μ.prod ν] (fun ω => Y ω.2)
参数：mX : Measurable X；mY : Measurable Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map`：indepFun_iff_ma
p_prod_eq_prod_map_map {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'} [IsFi
niteMeasure μ] (hf : AEMeasurable f μ) (hg : …
· 使用定理 `MeasureTheory.Measure.prod.instIsFiniteMeasure`：∀ {α : Type u_4} {β : Ty
pe u_5} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (μ : MeasureTheory.Mea
sure α)   (ν : MeasureTheory.Measure…
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `Measurable.comp_aemeasurable'`：Measurable.comp_aemeasurable' [Measurable
Space δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) :
 AEMeasurable (fun …
· 使用定理 `AEMeasurable.fst`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} {m0 : M
easurableSpace α} [inst : MeasurableSpace β]   [inst_1 : MeasurableSpace γ] {μ :
 Measu…
· 使用定理 `aemeasurable_id`：aemeasurable_id : AEMeasurable id μ
· 使用定理 `AEMeasurable.snd`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} {m0 : M
easurableSpace α} [inst : MeasurableSpace β]   [inst_1 : MeasurableSpace γ] {μ :
 Measu…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `MeasureTheory.Measure.map_map`：map_map {g : β -> γ} {f : α -> β} (hg : M
easurable g) (hf : Measurable f) : (μ.map f).map g = μ.map (g ∘ f)
· 使用定理 `measurable_fst`：measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.fst : α × β -> α)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.Measure.map_fst_prod`：∀ {α : Type u_1} {β : Type u_2} [ins
t : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μ : MeasureTheory.Measure α
}   {ν : MeasureTheory.M…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
· 使用定理 `MeasureTheory.Measure.map_snd_prod`：∀ {α : Type u_1} {β : Type u_2} [ins
t : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μ : MeasureTheory.Measure α
}   {ν : MeasureTheory.M…
· 使用定理 `MeasureTheory.Measure.map_prod_map`：map_prod_map {δ} [MeasurableSpace δ]
 {f : α -> β} {g : γ -> δ} (μa : Measure α) (μc : Measure γ) [SFinite μa] [SFini
te μc] (hf : Measurable …

--- 原说明 ---
Given random variables `X : Ω → 𝓧` and `Y : Ω' → 𝓨`, they are independent when v
iewed as random
variables defined on the product space `Ω × Ω'`.
-/
lemma indepFun_prod₀ (mX : AEMeasurable X μ) (mY : AEMeasurable Y ν) :
    (fun ω ↦ X ω.1) ⟂ᵢ[μ.prod ν] (fun ω ↦ Y ω.2) := by
  have : (fun ω ↦ mX.mk X ω.1) ⟂ᵢ[μ.prod ν] (fun ω ↦ mY.mk Y ω.2) :=
    indepFun_prod mX.measurable_mk mY.measurable_mk
  refine this.congr ?_ ?_
  · rw [← Function.comp_def, ← Function.comp_def]
    apply ae_eq_comp
    · exact measurable_fst.aemeasurable
    · rw [measurePreserving_fst.map_eq]
      exact (AEMeasurable.ae_eq_mk mX).symm
  · rw [← Function.comp_def, ← Function.comp_def]
    apply ae_eq_comp
    · exact measurable_snd.aemeasurable
    · rw [measurePreserving_snd.map_eq]
      exact (AEMeasurable.ae_eq_mk mY).symm

end Prod

/-
**ProbabilityTheory.IndepFun.comp** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory.I
ndepFun`。
形式化陈述：∀ {Ω : Type u_1} {β : Type u_6} {β' : Type u_7} {γ : Type u_8} {γ' : Type 
u_9} {_mΩ : MeasurableSpace Ω}   {μ : MeasureTheory.Measure Ω} {f : Ω → β} {g : 
Ω → β'} {_mβ : MeasurableSpace β} {_mβ' : MeasurableSpace β'}   {_mγ : Measurabl
eSpace γ} {_mγ' : MeasurableSpace γ'} {φ : β → γ} {ψ : β' → γ'},   ProbabilityTh
eory.IndepFun f g μ → Measurable φ → Measurable ψ → ProbabilityTheory.IndepFun (
φ ∘ f) (ψ ∘ g) μ
参数：φ ∘ f；ψ ∘ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IndepFun.comp`：∀ {α : Type u_1} {Ω : Type u_2} 
{β : Type u_4} {β' : Type u_5} {γ : Type u_6} {γ' : Type u_7} {mα : MeasurableSp
ace α}   {mΩ : MeasurableSpa…
-/
theorem IndepFun.comp {_mβ : MeasurableSpace β} {_mβ' : MeasurableSpace β'}
    {_mγ : MeasurableSpace γ} {_mγ' : MeasurableSpace γ'} {φ : β → γ} {ψ : β' → γ'}
    (hfg : f ⟂ᵢ[μ] g) (hφ : Measurable φ) (hψ : Measurable ψ) :
    (φ ∘ f) ⟂ᵢ[μ] ψ ∘ g :=
  Kernel.IndepFun.comp hfg hφ hψ
/-
**ProbabilityTheory.IndepFun.comp** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory.I
ndepFun`。
形式化陈述：∀ {Ω : Type u_1} {β : Type u_6} {β' : Type u_7} {γ : Type u_8} {γ' : Type 
u_9} {_mΩ : MeasurableSpace Ω}   {μ : MeasureTheory.Measure Ω} {f : Ω → β} {g : 
Ω → β'} {_mβ : MeasurableSpace β} {_mβ' : MeasurableSpace β'}   {_mγ : Measurabl
eSpace γ} {_mγ' : MeasurableSpace γ'} {φ : β → γ} {ψ : β' → γ'},   ProbabilityTh
eory.IndepFun f g μ → Measurable φ → Measurable ψ → ProbabilityTheory.IndepFun (
φ ∘ f) (ψ ∘ g) μ
参数：φ ∘ f；ψ ∘ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IndepFun.comp`：∀ {α : Type u_1} {Ω : Type u_2} 
{β : Type u_4} {β' : Type u_5} {γ : Type u_6} {γ' : Type u_7} {mα : MeasurableSp
ace α}   {mΩ : MeasurableSpa…
-/
theorem IndepFun.comp₀ {_mβ : MeasurableSpace β} {_mβ' : MeasurableSpace β'}
    {_mγ : MeasurableSpace γ} {_mγ' : MeasurableSpace γ'} {φ : β → γ} {ψ : β' → γ'}
    (hfg : f ⟂ᵢ[μ] g) (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (hφ : AEMeasurable φ (μ.map f)) (hψ : AEMeasurable ψ (μ.map g)) :
    (φ ∘ f) ⟂ᵢ[μ] (ψ ∘ g) :=
  Kernel.IndepFun.comp₀ hfg (by simp [hf]) (by simp [hg]) (by simp [hφ]) (by simp [hψ])
/-
**ProbabilityTheory.indepFun_const_left** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTh
eory`。
形式化陈述：indepFun_const_left {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'} [I
sZeroOrProbabilityMeasure μ] (c : β) (X : Ω -> β') : (fun _ => c) ⟂ᵢ[μ] X
参数：c : β；X : Ω -> β'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.Kernel.indepFun_const_left`：indepFun_const_left {mβ : 
MeasurableSpace β} {mβ' : MeasurableSpace β'} [IsZeroOrMarkovKernel κ] (c : β') 
(X : Ω -> β) : IndepFun (fun _ => …
· 使用定理 `ProbabilityTheory.Kernel.const.instIsZeroOrMarkovKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μβ : Measure
Theory.Measure β}   [hμβ : MeasureTheory.IsZe…
-/
lemma indepFun_const_left {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    [IsZeroOrProbabilityMeasure μ] (c : β) (X : Ω → β') :
    (fun _ ↦ c) ⟂ᵢ[μ] X :=
  Kernel.indepFun_const_left c X
/-
**ProbabilityTheory.indepFun_const_right** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityT
heory`。
形式化陈述：indepFun_const_right {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'} [
IsZeroOrProbabilityMeasure μ] (X : Ω -> β) (c : β') : X ⟂ᵢ[μ] (fun _ => c)
参数：X : Ω -> β；c : β'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.Kernel.indepFun_const_right`：indepFun_const_right {mβ 
: MeasurableSpace β} {mβ' : MeasurableSpace β'} [IsZeroOrMarkovKernel κ] (X : Ω 
-> β) (c : β') : IndepFun X (fun _ …
· 使用定理 `ProbabilityTheory.Kernel.const.instIsZeroOrMarkovKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μβ : Measure
Theory.Measure β}   [hμβ : MeasureTheory.IsZe…
-/
lemma indepFun_const_right {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    [IsZeroOrProbabilityMeasure μ] (X : Ω → β) (c : β') :
    X ⟂ᵢ[μ] (fun _ ↦ c) :=
  Kernel.indepFun_const_right X c
/-
**ProbabilityTheory.IndepFun.neg_right** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityThe
ory.IndepFun`。
形式化陈述：∀ {Ω : Type u_1} {β : Type u_6} {β' : Type u_7} {_mΩ : MeasurableSpace Ω} 
{μ : MeasureTheory.Measure Ω} {f : Ω → β}   {g : Ω → β'} {_mβ : MeasurableSpace 
β} {_mβ' : MeasurableSpace β'} [inst : Neg β'] [MeasurableNeg β'],   Probability
Theory.IndepFun f g μ → ProbabilityTheory.IndepFun f (-g) μ
参数：-g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IndepFun.comp`：∀ {Ω : Type u_1} {β : Type u_6} {β' : T
ype u_7} {γ : Type u_8} {γ' : Type u_9} {_mΩ : MeasurableSpace Ω}   {μ : Measure
Theory.Measure Ω} {f …
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)
· 使用定理 `MeasurableNeg.measurable_neg`：∀ {G : Type u_2} {inst : Neg G} {inst_1 : 
MeasurableSpace G} [self : MeasurableNeg G], Measurable Neg.neg
-/
theorem IndepFun.neg_right {_mβ : MeasurableSpace β} {_mβ' : MeasurableSpace β'} [Neg β']
    [MeasurableNeg β'] (hfg : f ⟂ᵢ[μ] g) :
    f ⟂ᵢ[μ] (-g) := hfg.comp measurable_id measurable_neg
/-
**ProbabilityTheory.IndepFun.neg_left** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheo
ry.IndepFun`。
形式化陈述：∀ {Ω : Type u_1} {β : Type u_6} {β' : Type u_7} {_mΩ : MeasurableSpace Ω} 
{μ : MeasureTheory.Measure Ω} {f : Ω → β}   {g : Ω → β'} {_mβ : MeasurableSpace 
β} {_mβ' : MeasurableSpace β'} [inst : Neg β] [MeasurableNeg β],   ProbabilityTh
eory.IndepFun f g μ → ProbabilityTheory.IndepFun (-f) g μ
参数：-f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IndepFun.comp`：∀ {Ω : Type u_1} {β : Type u_6} {β' : T
ype u_7} {γ : Type u_8} {γ' : Type u_9} {_mΩ : MeasurableSpace Ω}   {μ : Measure
Theory.Measure Ω} {f …
· 使用定理 `MeasurableNeg.measurable_neg`：∀ {G : Type u_2} {inst : Neg G} {inst_1 : 
MeasurableSpace G} [self : MeasurableNeg G], Measurable Neg.neg
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)
-/
theorem IndepFun.neg_left {_mβ : MeasurableSpace β} {_mβ' : MeasurableSpace β'} [Neg β]
    [MeasurableNeg β] (hfg : f ⟂ᵢ[μ] g) :
    (-f) ⟂ᵢ[μ] g := hfg.comp measurable_neg measurable_id

section iIndepFun
variable {β : ι → Type*} {m : ∀ i, MeasurableSpace (β i)} {f : ∀ i, Ω → β i}

/-
**ProbabilityTheory.iIndepFun.isProbabilityMeasure** 是 Mathlib 中的一个定理，位于命名空间 `Pr
obabilityTheory.iIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {_mΩ : MeasurableSpace Ω} {μ : MeasureTheo
ry.Measure Ω} {β : ι → Type u_10}   {m : (i : ι) → MeasurableSpace (β i)} {f : (
i : ι) → Ω → β i},   ProbabilityTheory.iIndepFun f μ → MeasureTheory.IsProbabili
tyMeasure μ
参数：i : ι；β i；i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
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
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `Set.iInter_univ`：iInter_univ : (⋂ _ : ι, univ : Set α) = univ
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `ProbabilityTheory.iIndepFun.meas_biInter`：∀ {Ω : Type u_1} {ι : Type u_2
} {κ : ι → Type u_5} {x : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {S : 
Finset ι}   {s : ι → Set Ω} {m…
-/
lemma iIndepFun.isProbabilityMeasure (h : iIndepFun f μ) : IsProbabilityMeasure μ :=
  ⟨by simpa using h.meas_biInter (S := ∅) (s := fun _ ↦ univ)⟩

/-- If `f` is a family of mutually independent random variables (`iIndepFun m f μ`) and `S, T` are
two disjoint finite index sets, then the tuple formed by `f i` for `i ∈ S` is independent of the
tuple `(f i)_i` for `i ∈ T`. -/
/-
**ProbabilityTheory.iIndepFun.indepFun_finset** 是 Mathlib 中的一个定理，位于命名空间 `Probabi
lityTheory.iIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {_mΩ : MeasurableSpace Ω} {μ : MeasureTheo
ry.Measure Ω} {β : ι → Type u_10}   {m : (i : ι) → MeasurableSpace (β i)} {f : (
i : ι) → Ω → β i} (S T : Finset ι),   Disjoint S T →     ProbabilityTheory.iInde
pFun f μ →       (∀ (i : ι), Measurable (f i)) → ProbabilityTheory.IndepFun (fun
 a i => f (↑i) a) (fun a i => f (↑i) a) μ
参数：i : ι；β i；i : ι；S T : Finset ι；∀ (i : ι), Measurable (f i)；fun a i => f (↑i) 
a；fun a i => f (↑i) a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.indepFun_finset`：∀ {α : Type u_1} {Ω 
: Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω}   {
κ : ProbabilityTheory.Kernel α Ω} {μ : M…

--- 原说明 ---
If `f` is a family of mutually independent random variables (`iIndepFun m f μ`) 
and `S, T` are
two disjoint finite index sets, then the tuple formed by `f i` for `i ∈ S` is in
dependent of the
tuple `(f i)_i` for `i ∈ T`.
-/
lemma iIndepFun.indepFun_finset (S T : Finset ι) (hST : Disjoint S T) (hf_Indep : iIndepFun f μ)
    (hf_meas : ∀ i, Measurable (f i)) :
    IndepFun (fun a (i : S) ↦ f i a) (fun a (i : T) ↦ f i a) μ :=
  Kernel.iIndepFun.indepFun_finset S T hST hf_Indep hf_meas

/-- If `f` is a family of mutually independent random variables (`iIndepFun m f μ`) and `S, T` are
two disjoint finite index sets, then the tuple formed by `f i` for `i ∈ S` is independent of the
tuple `(f i)_i` for `i ∈ T`. -/
/-
**ProbabilityTheory.iIndepFun.indepFun_finset** 是 Mathlib 中的一个定理，位于命名空间 `Probabi
lityTheory.iIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {_mΩ : MeasurableSpace Ω} {μ : MeasureTheo
ry.Measure Ω} {β : ι → Type u_10}   {m : (i : ι) → MeasurableSpace (β i)} {f : (
i : ι) → Ω → β i} (S T : Finset ι),   Disjoint S T →     ProbabilityTheory.iInde
pFun f μ →       (∀ (i : ι), Measurable (f i)) → ProbabilityTheory.IndepFun (fun
 a i => f (↑i) a) (fun a i => f (↑i) a) μ
参数：i : ι；β i；i : ι；S T : Finset ι；∀ (i : ι), Measurable (f i)；fun a i => f (↑i) 
a；fun a i => f (↑i) a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.indepFun_finset`：∀ {α : Type u_1} {Ω 
: Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω}   {
κ : ProbabilityTheory.Kernel α Ω} {μ : M…

--- 原说明 ---
If `f` is a family of mutually independent random variables (`iIndepFun m f μ`) 
and `S, T` are
two disjoint finite index sets, then the tuple formed by `f i` for `i ∈ S` is in
dependent of the
tuple `(f i)_i` for `i ∈ T`.
-/
lemma iIndepFun.indepFun_finset₀ (S T : Finset ι) (hST : Disjoint S T) (hf_Indep : iIndepFun f μ)
    (hf_meas : ∀ i, AEMeasurable (f i) μ) :
    IndepFun (fun a (i : S) ↦ f i a) (fun a (i : T) ↦ f i a) μ :=
  Kernel.iIndepFun.indepFun_finset₀ S T hST hf_Indep (by simp [hf_meas])
/-
**ProbabilityTheory.iIndepFun.indepFun_prodMk** 是 Mathlib 中的一个定理，位于命名空间 `Probabi
lityTheory.iIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {_mΩ : MeasurableSpace Ω} {μ : MeasureTheo
ry.Measure Ω} {β : ι → Type u_10}   {m : (i : ι) → MeasurableSpace (β i)} {f : (
i : ι) → Ω → β i},   ProbabilityTheory.iIndepFun f μ →     (∀ (i : ι), Measurabl
e (f i)) →       ∀ (i j k : ι), i ≠ k → j ≠ k → ProbabilityTheory.IndepFun (fun 
a => (f i a, f j a)) (f k) μ
参数：i : ι；β i；i : ι；∀ (i : ι), Measurable (f i)；i j k : ι；fun a => (f i a, f j a)
；f k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.indepFun_prodMk`：∀ {α : Type u_1} {Ω 
: Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω}   {
κ : ProbabilityTheory.Kernel α Ω} {μ : M…
-/
lemma iIndepFun.indepFun_prodMk (hf_Indep : iIndepFun f μ) (hf_meas : ∀ i, Measurable (f i))
    (i j k : ι) (hik : i ≠ k) (hjk : j ≠ k) :
    IndepFun (fun a => (f i a, f j a)) (f k) μ :=
  Kernel.iIndepFun.indepFun_prodMk hf_Indep hf_meas i j k hik hjk
/-
**ProbabilityTheory.iIndepFun.indepFun_prodMk** 是 Mathlib 中的一个定理，位于命名空间 `Probabi
lityTheory.iIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {_mΩ : MeasurableSpace Ω} {μ : MeasureTheo
ry.Measure Ω} {β : ι → Type u_10}   {m : (i : ι) → MeasurableSpace (β i)} {f : (
i : ι) → Ω → β i},   ProbabilityTheory.iIndepFun f μ →     (∀ (i : ι), Measurabl
e (f i)) →       ∀ (i j k : ι), i ≠ k → j ≠ k → ProbabilityTheory.IndepFun (fun 
a => (f i a, f j a)) (f k) μ
参数：i : ι；β i；i : ι；∀ (i : ι), Measurable (f i)；i j k : ι；fun a => (f i a, f j a)
；f k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.indepFun_prodMk`：∀ {α : Type u_1} {Ω 
: Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω}   {
κ : ProbabilityTheory.Kernel α Ω} {μ : M…
-/
lemma iIndepFun.indepFun_prodMk₀ (hf_Indep : iIndepFun f μ) (hf_meas : ∀ i, AEMeasurable (f i) μ)
    (i j k : ι) (hik : i ≠ k) (hjk : j ≠ k) :
    IndepFun (fun a => (f i a, f j a)) (f k) μ :=
  Kernel.iIndepFun.indepFun_prodMk₀ hf_Indep (by simp [hf_meas]) i j k hik hjk
/-
**ProbabilityTheory.iIndepFun.indepFun_prodMk_prodMk** 是 Mathlib 中的一个定理，位于命名空间 `
ProbabilityTheory.iIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {_mΩ : MeasurableSpace Ω} {μ : MeasureTheo
ry.Measure Ω} {β : ι → Type u_10}   {m : (i : ι) → MeasurableSpace (β i)} {f : (
i : ι) → Ω → β i},   ProbabilityTheory.iIndepFun f μ →     (∀ (i : ι), Measurabl
e (f i)) →       ∀ (i j k l : ι),         i ≠ k → i ≠ l → j ≠ k → j ≠ l → Probab
ilityTheory.IndepFun (fun a => (f i a, f j a)) (fun a => (f k a, f l a)) μ
参数：i : ι；β i；i : ι；∀ (i : ι), Measurable (f i)；i j k l : ι；fun a => (f i a, f j 
a)；fun a => (f k a, f l a)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.indepFun_prodMk_prodMk`：∀ {α : Type u
_1} {Ω : Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {mΩ : MeasurableSpace
 Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ : M…
-/
lemma iIndepFun.indepFun_prodMk_prodMk (h_indep : iIndepFun f μ) (hf : ∀ i, Measurable (f i))
    (i j k l : ι) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    IndepFun (fun a ↦ (f i a, f j a)) (fun a ↦ (f k a, f l a)) μ :=
  Kernel.iIndepFun.indepFun_prodMk_prodMk h_indep hf i j k l hik hil hjk hjl
/-
**ProbabilityTheory.iIndepFun.indepFun_prodMk_prodMk** 是 Mathlib 中的一个定理，位于命名空间 `
ProbabilityTheory.iIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {_mΩ : MeasurableSpace Ω} {μ : MeasureTheo
ry.Measure Ω} {β : ι → Type u_10}   {m : (i : ι) → MeasurableSpace (β i)} {f : (
i : ι) → Ω → β i},   ProbabilityTheory.iIndepFun f μ →     (∀ (i : ι), Measurabl
e (f i)) →       ∀ (i j k l : ι),         i ≠ k → i ≠ l → j ≠ k → j ≠ l → Probab
ilityTheory.IndepFun (fun a => (f i a, f j a)) (fun a => (f k a, f l a)) μ
参数：i : ι；β i；i : ι；∀ (i : ι), Measurable (f i)；i j k l : ι；fun a => (f i a, f j 
a)；fun a => (f k a, f l a)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.indepFun_prodMk_prodMk`：∀ {α : Type u
_1} {Ω : Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {mΩ : MeasurableSpace
 Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ : M…
-/
lemma iIndepFun.indepFun_prodMk_prodMk₀ (h_indep : iIndepFun f μ) (hf : ∀ i, AEMeasurable (f i) μ)
    (i j k l : ι) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    IndepFun (fun a ↦ (f i a, f j a)) (fun a ↦ (f k a, f l a)) μ :=
  Kernel.iIndepFun.indepFun_prodMk_prodMk₀ h_indep (by simp [hf]) i j k l hik hil hjk hjl
/-
**ProbabilityTheory.iIndepFun_iff_finset** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityT
heory`。
形式化陈述：iIndepFun_iff_finset : iIndepFun f μ ↔ forall s : Finset ι, iIndepFun (s.r
estrict f) μ where mp h s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.iIndepFun.precomp`：∀ {Ω : Type u_1} {ι : Type u_2} {x 
: MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {ι' : Type u_6} {g : ι' → ι} 
  {β : ι → Type u_7} {m :…
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.iIndepFun_iff`：iIndepFun_iff {β : ι -> Type*} (m : for
all x : ι, MeasurableSpace (β x)) (f : forall x : ι, Ω -> β x) (μ : Measure Ω) :
 iIndepFun f μ ↔ fora…
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_coe_sort`：prod_coe_sort : ∏ i : s, f i = ∏ i in s, f i
· 使用定理 `ProbabilityTheory.iIndepFun.meas_iInter`：∀ {Ω : Type u_1} {ι : Type u_2}
 {κ : ι → Type u_5} {x : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {s : ι
 → Set Ω}   [inst : Fintype ι…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma iIndepFun_iff_finset : iIndepFun f μ ↔ ∀ s : Finset ι, iIndepFun (s.restrict f) μ where
  mp h s := h.precomp (g := ((↑) : s → ι)) Subtype.val_injective
  mpr h := by
    rw [iIndepFun_iff]
    intro s f hs
    have : ⋂ i ∈ s, f i = ⋂ i : s, f i := by ext; simp
    rw [← Finset.prod_coe_sort, this]
    exact (h s).meas_iInter fun i ↦ hs i i.2

alias ⟨iIndepFun.restrict, _⟩ := iIndepFun_iff_finset
/-
**ProbabilityTheory.iIndepFun.map_fun_eq_pi_map** 是 Mathlib 中的一个定理，位于命名空间 `Proba
bilityTheory.iIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {_mΩ : MeasurableSpace Ω} {μ : MeasureTheo
ry.Measure Ω} [inst : Fintype ι]   {β : ι → Type u_11} {m : (i : ι) → Measurable
Space (β i)} {f : (i : ι) → Ω → β i},   (∀ (i : ι), AEMeasurable (f i) μ) →     
ProbabilityTheory.iIndepFun f μ →       MeasureTheory.Measure.map (fun ω i => f 
i ω) μ =         MeasureTheory.Measure.pi fun i => MeasureTheory.Measure.map (f 
i) μ
参数：i : ι；β i；i : ι；∀ (i : ι), AEMeasurable (f i) μ；fun ω i => f i ω；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.iIndepFun.isProbabilityMeasure`：∀ {Ω : Type u_1} {ι : 
Type u_2} {_mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {β : ι → Type 
u_10}   {m : (i : ι) → MeasurableSpace…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_apply_of_aemeasurable`：map_apply_of_aemeasurab
le (hf : AEMeasurable f μ) {s : Set β} (hs : MeasurableSet s) : μ.map f s = μ (f
 ⁻¹' s)
· 使用定理 `aemeasurable_pi_lambda`：aemeasurable_pi_lambda (f : α -> Π a, X a) (hf :
 forall a, AEMeasurable (fun c => f c a) μ) : AEMeasurable f μ
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `MeasurableSet.univ_pi`：∀ {δ : Type u_4} {X : δ → Type u_6} [inst : (a : 
δ) → MeasurableSpace (X a)] [Countable δ] {t : (i : δ) → Set (X i)},   (∀ (i : δ
), Measurab…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.pi_eq`：pi_eq [forall i, SigmaFinite (μ i)] {μ' : M
easure (forall i, α i)} (h : forall s : forall i, Set (α i), (forall i, Measurab
leSet (s i)) -> μ…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasureTheory.Measure.isFiniteMeasure_map`：∀ {α : Type u_1} {β : Type u_
2} [mβ : MeasurableSpace β] {m : MeasurableSpace α} (μ : MeasureTheory.Measure α
)   [MeasureTheory.IsFiniteMeas…
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
（共 33 条，此处仅展示前 30 条）
-/
theorem iIndepFun.map_fun_eq_pi_map [Fintype ι] {β : ι → Type*}
    {m : ∀ i, MeasurableSpace (β i)} {f : Π i, Ω → β i}
    (hf : ∀ i, AEMeasurable (f i) μ) (h : iIndepFun f μ) :
    μ.map (fun ω i ↦ f i ω) = Measure.pi (fun i ↦ μ.map (f i)) := by
  have := h.isProbabilityMeasure
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at h
  have h₀ {s : ∀ i, Set (β i)} (hm : ∀ (i : ι), MeasurableSet (s i)) :
      ∏ i : ι, μ (f i ⁻¹' s i) = ∏ i : ι, μ.map (f i) (s i) ∧
      μ (⋂ i : ι, (f i ⁻¹' s i)) = μ.map (fun ω i ↦ f i ω) (univ.pi s) := by
    constructor
    · congr with x
      rw [Measure.map_apply_of_aemeasurable (hf x) (hm x)]
    · rw [Measure.map_apply_of_aemeasurable (aemeasurable_pi_lambda _ fun x ↦ hf x)
        (.univ_pi hm)]
      congr with x
      simp
  refine (Measure.pi_eq fun h' hm ↦ ?_).symm
  rw [← (h₀ hm).1, ← (h₀ hm).2]
  simpa [hm] using h Finset.univ (sets := h')
/-
**ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map** 是 Mathlib 中的一个定理，位于命名空间 `P
robabilityTheory`。
形式化陈述：iIndepFun_iff_map_fun_eq_pi_map [Fintype ι] {β : ι -> Type*} {m : forall i
, MeasurableSpace (β i)} {f : Π i, Ω -> β i} [IsProbabilityMeasure μ] (hf : fora
ll i, AEMeasurable (f i) μ) : iIndepFun f μ ↔ μ.map (fun ω i => f i ω) = Measure
.pi (fun i => μ.map (f i))
参数：β i；hf : forall i, AEMeasurable (f i) μ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.iIndepFun.map_fun_eq_pi_map`：∀ {Ω : Type u_1} {ι : Typ
e u_2} {_mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} [inst : Fintype ι
]   {β : ι → Type u_11} {m : (i : ι…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul`：iIndepFun
_iff_measure_inter_preimage_eq_mul {ι : Type*} {β : ι -> Type*} {m : forall x, M
easurableSpace (β x)} {f : forall i, Ω -> β i} : iI…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.Measure.map_apply_of_aemeasurable`：map_apply_of_aemeasurab
le (hf : AEMeasurable f μ) {s : Set β} (hs : MeasurableSet s) : μ.map f s = μ (f
 ⁻¹' s)
· 使用定理 `aemeasurable_pi_lambda`：aemeasurable_pi_lambda (f : α -> Π a, X a) (hf :
 forall a, AEMeasurable (fun c => f c a) μ) : AEMeasurable f μ
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `MeasurableSet.univ_pi`：∀ {δ : Type u_4} {X : δ → Type u_6} [inst : (a : 
δ) → MeasurableSpace (X a)] [Countable δ] {t : (i : δ) → Set (X i)},   (∀ (i : δ
), Measurab…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `Finset.prod_ite_mem`：prod_ite_mem [DecidableEq ι] (s t : Finset ι) (f : 
ι -> M) : ∏ i in s, (if i in t then f i else 1) = ∏ i in s inter t, f i
· 使用定理 `Finset.univ_inter`：∀ {α : Type u_1} [inst : Fintype α] [inst_1 : Decidab
leEq α] (s : Finset α), Finset.univ ∩ s = s
· 使用定理 `Finset.prod_ite`：prod_ite {s : Finset ι} {p : ι -> Prop} [DecidablePred 
p] (f g : ι -> M) : ∏ x in s, (if p x then f x else g x) = (∏ x in s with p x, f
 x) *…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Finset.filter_univ_mem`：filter_univ_mem (s : Finset α) : univ.filter (· 
in s) = s
· 使用定理 `Set.iInter_ite`：iInter_ite (f g : ι -> Set α) : ⋂ i, (if p i then f i el
se g i) = (⋂ (i) (_ : p i), f i) inter ⋂ (i) (_ : ¬p i), g i
（共 42 条，此处仅展示前 30 条）
-/
theorem iIndepFun_iff_map_fun_eq_pi_map [Fintype ι] {β : ι → Type*}
    {m : ∀ i, MeasurableSpace (β i)} {f : Π i, Ω → β i} [IsProbabilityMeasure μ]
    (hf : ∀ i, AEMeasurable (f i) μ) :
    iIndepFun f μ ↔ μ.map (fun ω i ↦ f i ω) = Measure.pi (fun i ↦ μ.map (f i)) := by
  refine ⟨iIndepFun.map_fun_eq_pi_map hf, ?_⟩
  classical
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  have h₀ {s : ∀ i, Set (β i)} (hm : ∀ (i : ι), MeasurableSet (s i)) :
      ∏ i : ι, μ (f i ⁻¹' s i) = ∏ i : ι, μ.map (f i) (s i) ∧
      μ (⋂ i : ι, (f i ⁻¹' s i)) = μ.map (fun ω i ↦ f i ω) (univ.pi s) := by
    constructor
    · congr with x
      rw [Measure.map_apply_of_aemeasurable (hf x) (hm x)]
    · rw [Measure.map_apply_of_aemeasurable (aemeasurable_pi_lambda _ fun x ↦ hf x)
        (.univ_pi hm)]
      congr with x
      simp
  intro h S s hs
  specialize h₀ (s := fun i ↦ if i ∈ S then s i else univ)
    fun i ↦ by split_ifs with hiS <;> simp [hiS, hs]
  simp only [apply_ite, preimage_univ, measure_univ, Finset.prod_ite_mem, Finset.univ_inter,
    Finset.prod_ite, Finset.filter_univ_mem, iInter_ite, iInter_univ, inter_univ, h,
    Measure.pi_pi] at h₀
  rw [h₀.2, ← h₀.1]

variable {ι : Type*} [Fintype ι] {Ω : ι → Type*} {mΩ : ∀ i, MeasurableSpace (Ω i)}
    {μ : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {𝓧 : ι → Type*} [∀ i, MeasurableSpace (𝓧 i)] {X : (i : ι) → Ω i → 𝓧 i}

/-- Given random variables `X i : Ω i → 𝓧 i`, they are independent when viewed as random
variables defined on the product space `Π i, Ω i`. -/
/-
**ProbabilityTheory.iIndepFun_pi** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：iIndepFun_pi (mX : forall i, AEMeasurable (X i) (μ i)) : iIndepFun (fun i 
ω => X i (ω i)) (Measure.pi μ)
参数：mX : forall i, AEMeasurable (X i) (μ i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map`：iIndepFun_iff_map_fun
_eq_pi_map [Fintype ι] {β : ι -> Type*} {m : forall i, MeasurableSpace (β i)} {f
 : Π i, Ω -> β i} [IsProbabilityMeasure…
· 使用定理 `MeasureTheory.Measure.pi.instIsProbabilityMeasure`：∀ {ι : Type u_1} {α :
 ι → Type u_3} [inst : Fintype ι] [inst_1 : (i : ι) → MeasurableSpace (α i)]   (
μ : (i : ι) → MeasureTheory.Measure (α …
· 使用定理 `AEMeasurable.comp_quasiMeasurePreserving`：comp_quasiMeasurePreserving {ν
 : Measure δ} {f : α -> δ} {g : δ -> β} (hg : AEMeasurable g ν) (hf : QuasiMeasu
rePreserving f μ ν) : AEMeasur…
· 使用定理 `MeasureTheory.Measure.quasiMeasurePreserving_eval`：quasiMeasurePreservin
g_eval (i : ι) : QuasiMeasurePreserving (Function.eval i) (Measure.pi μ) (μ i)
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.pi_map_pi`：pi_map_pi {X Y : ι -> Type*} {mX : fora
ll i, MeasurableSpace (X i)} {μ : (i : ι) -> Measure (X i)} [forall i, Measurabl
eSpace (Y i)] {f : (i…
· 使用定理 `MeasureTheory.Measure.isFiniteMeasure_map`：∀ {α : Type u_1} {β : Type u_
2} [mβ : MeasurableSpace β] {m : MeasurableSpace α} (μ : MeasureTheory.Measure α
)   [MeasureTheory.IsFiniteMeas…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.MeasurePreserving.map_eq`：∀ {α : Type u_1} {β : Type u_2} 
[inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : auto
Param (MeasureTheory.Measure…
· 使用定理 `MeasureTheory.measurePreserving_eval`：∀ {ι : Type u_1} {α : ι → Type u_3
} [inst : Fintype ι] [inst_1 : (i : ι) → MeasurableSpace (α i)]   (μ : (i : ι) →
 MeasureTheory.Measure (α …
· 使用定理 `AEMeasurable.map_map_of_aemeasurable`：map_map_of_aemeasurable {g : β -> 
γ} {f : α -> β} (hg : AEMeasurable g (Measure.map f μ)) (hf : AEMeasurable f μ) 
: (μ.map f).map g = μ.map …
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `measurable_pi_apply`：measurable_pi_apply (a : δ) : Measurable fun f : fo
rall a, X a => f a
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)

--- 原说明 ---
Given random variables `X i : Ω i → 𝓧 i`, they are independent when viewed as ra
ndom
variables defined on the product space `Π i, Ω i`.
-/
lemma iIndepFun_pi (mX : ∀ i, AEMeasurable (X i) (μ i)) :
    iIndepFun (fun i ω ↦ X i (ω i)) (Measure.pi μ) := by
  refine iIndepFun_iff_map_fun_eq_pi_map ?_ |>.2 ?_
  · exact fun i ↦ (mX i).comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_eval _ i)
  rw [Measure.pi_map_pi mX]
  congr
  ext i : 1
  rw [← (measurePreserving_eval μ i).map_eq, AEMeasurable.map_map_of_aemeasurable,
    Function.comp_def]
  · rw [(measurePreserving_eval μ i).map_eq]
    exact mX i
  · exact (measurable_pi_apply i).aemeasurable

end iIndepFun

section Mul
variable {β : Type*} {m : MeasurableSpace β} [Mul β] [MeasurableMul₂ β] {f : ι → Ω → β}

@[to_additive]
/-
**ProbabilityTheory.iIndepFun.indepFun_mul_left** 是 Mathlib 中的一个定理，位于命名空间 `Proba
bilityTheory.iIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {_mΩ : MeasurableSpace Ω} {μ : MeasureTheo
ry.Measure Ω} {β : Type u_10}   {m : MeasurableSpace β} [inst : Mul β] [Measurab
leMul₂ β] {f : ι → Ω → β},   ProbabilityTheory.iIndepFun f μ →     (∀ (i : ι), M
easurable (f i)) → ∀ (i j k : ι), i ≠ k → j ≠ k → ProbabilityTheory.IndepFun (f 
i * f j) (f k) μ
参数：∀ (i : ι), Measurable (f i)；i j k : ι；f i * f j；f k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.indepFun_mul_left`：∀ {α : Type u_1} {
Ω : Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω}  
 {κ : ProbabilityTheory.Kernel α Ω} {μ : M…
-/
lemma iIndepFun.indepFun_mul_left (hf_indep : iIndepFun f μ)
    (hf_meas : ∀ i, Measurable (f i)) (i j k : ι) (hik : i ≠ k) (hjk : j ≠ k) :
    IndepFun (f i * f j) (f k) μ :=
  Kernel.iIndepFun.indepFun_mul_left hf_indep hf_meas i j k hik hjk

@[to_additive]
/-
**ProbabilityTheory.iIndepFun.indepFun_mul_left** 是 Mathlib 中的一个定理，位于命名空间 `Proba
bilityTheory.iIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {_mΩ : MeasurableSpace Ω} {μ : MeasureTheo
ry.Measure Ω} {β : Type u_10}   {m : MeasurableSpace β} [inst : Mul β] [Measurab
leMul₂ β] {f : ι → Ω → β},   ProbabilityTheory.iIndepFun f μ →     (∀ (i : ι), M
easurable (f i)) → ∀ (i j k : ι), i ≠ k → j ≠ k → ProbabilityTheory.IndepFun (f 
i * f j) (f k) μ
参数：∀ (i : ι), Measurable (f i)；i j k : ι；f i * f j；f k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.indepFun_mul_left`：∀ {α : Type u_1} {
Ω : Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω}  
 {κ : ProbabilityTheory.Kernel α Ω} {μ : M…
-/
lemma iIndepFun.indepFun_mul_left₀ (hf_indep : iIndepFun f μ)
    (hf_meas : ∀ i, AEMeasurable (f i) μ) (i j k : ι) (hik : i ≠ k) (hjk : j ≠ k) :
    IndepFun (f i * f j) (f k) μ :=
  Kernel.iIndepFun.indepFun_mul_left₀ hf_indep (by simp [hf_meas]) i j k hik hjk

@[to_additive]
/-
**ProbabilityTheory.iIndepFun.indepFun_mul_right** 是 Mathlib 中的一个定理，位于命名空间 `Prob
abilityTheory.iIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {_mΩ : MeasurableSpace Ω} {μ : MeasureTheo
ry.Measure Ω} {β : Type u_10}   {m : MeasurableSpace β} [inst : Mul β] [Measurab
leMul₂ β] {f : ι → Ω → β},   ProbabilityTheory.iIndepFun f μ →     (∀ (i : ι), M
easurable (f i)) → ∀ (i j k : ι), i ≠ j → i ≠ k → ProbabilityTheory.IndepFun (f 
i) (f j * f k) μ
参数：∀ (i : ι), Measurable (f i)；i j k : ι；f i；f j * f k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.indepFun_mul_right`：∀ {α : Type u_1} 
{Ω : Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω} 
  {κ : ProbabilityTheory.Kernel α Ω} {μ : M…
-/
lemma iIndepFun.indepFun_mul_right (hf_indep : iIndepFun f μ)
    (hf_meas : ∀ i, Measurable (f i)) (i j k : ι) (hij : i ≠ j) (hik : i ≠ k) :
    IndepFun (f i) (f j * f k) μ :=
  Kernel.iIndepFun.indepFun_mul_right hf_indep hf_meas i j k hij hik

@[to_additive]
/-
**ProbabilityTheory.iIndepFun.indepFun_mul_right** 是 Mathlib 中的一个定理，位于命名空间 `Prob
abilityTheory.iIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {_mΩ : MeasurableSpace Ω} {μ : MeasureTheo
ry.Measure Ω} {β : Type u_10}   {m : MeasurableSpace β} [inst : Mul β] [Measurab
leMul₂ β] {f : ι → Ω → β},   ProbabilityTheory.iIndepFun f μ →     (∀ (i : ι), M
easurable (f i)) → ∀ (i j k : ι), i ≠ j → i ≠ k → ProbabilityTheory.IndepFun (f 
i) (f j * f k) μ
参数：∀ (i : ι), Measurable (f i)；i j k : ι；f i；f j * f k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.indepFun_mul_right`：∀ {α : Type u_1} 
{Ω : Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω} 
  {κ : ProbabilityTheory.Kernel α Ω} {μ : M…
-/
lemma iIndepFun.indepFun_mul_right₀ (hf_indep : iIndepFun f μ)
    (hf_meas : ∀ i, AEMeasurable (f i) μ) (i j k : ι) (hij : i ≠ j) (hik : i ≠ k) :
    IndepFun (f i) (f j * f k) μ :=
  Kernel.iIndepFun.indepFun_mul_right₀ hf_indep (by simp [hf_meas]) i j k hij hik

@[to_additive]
/-
**ProbabilityTheory.iIndepFun.indepFun_mul_mul** 是 Mathlib 中的一个定理，位于命名空间 `Probab
ilityTheory.iIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {_mΩ : MeasurableSpace Ω} {μ : MeasureTheo
ry.Measure Ω} {β : Type u_10}   {m : MeasurableSpace β} [inst : Mul β] [Measurab
leMul₂ β] {f : ι → Ω → β},   ProbabilityTheory.iIndepFun f μ →     (∀ (i : ι), M
easurable (f i)) →       ∀ (i j k l : ι), i ≠ k → i ≠ l → j ≠ k → j ≠ l → Probab
ilityTheory.IndepFun (f i * f j) (f k * f l) μ
参数：∀ (i : ι), Measurable (f i)；i j k l : ι；f i * f j；f k * f l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.indepFun_mul_mul`：∀ {α : Type u_1} {Ω
 : Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω}   
{κ : ProbabilityTheory.Kernel α Ω} {μ : M…
-/
lemma iIndepFun.indepFun_mul_mul (hf_indep : iIndepFun f μ)
    (hf_meas : ∀ i, Measurable (f i))
    (i j k l : ι) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    IndepFun (f i * f j) (f k * f l) μ :=
  Kernel.iIndepFun.indepFun_mul_mul hf_indep hf_meas i j k l hik hil hjk hjl

@[to_additive]
/-
**ProbabilityTheory.iIndepFun.indepFun_mul_mul** 是 Mathlib 中的一个定理，位于命名空间 `Probab
ilityTheory.iIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {_mΩ : MeasurableSpace Ω} {μ : MeasureTheo
ry.Measure Ω} {β : Type u_10}   {m : MeasurableSpace β} [inst : Mul β] [Measurab
leMul₂ β] {f : ι → Ω → β},   ProbabilityTheory.iIndepFun f μ →     (∀ (i : ι), M
easurable (f i)) →       ∀ (i j k l : ι), i ≠ k → i ≠ l → j ≠ k → j ≠ l → Probab
ilityTheory.IndepFun (f i * f j) (f k * f l) μ
参数：∀ (i : ι), Measurable (f i)；i j k l : ι；f i * f j；f k * f l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.indepFun_mul_mul`：∀ {α : Type u_1} {Ω
 : Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω}   
{κ : ProbabilityTheory.Kernel α Ω} {μ : M…
-/
lemma iIndepFun.indepFun_mul_mul₀ (hf_indep : iIndepFun f μ)
    (hf_meas : ∀ i, AEMeasurable (f i) μ)
    (i j k l : ι) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    IndepFun (f i * f j) (f k * f l) μ :=
  Kernel.iIndepFun.indepFun_mul_mul₀ hf_indep (by simp [hf_meas]) i j k l hik hil hjk hjl

end Mul

section Div
variable {β : Type*} {m : MeasurableSpace β} [Div β] [MeasurableDiv₂ β] {f : ι → Ω → β}

@[to_additive]
/-
**ProbabilityTheory.iIndepFun.indepFun_div_left** 是 Mathlib 中的一个定理，位于命名空间 `Proba
bilityTheory.iIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {_mΩ : MeasurableSpace Ω} {μ : MeasureTheo
ry.Measure Ω} {β : Type u_10}   {m : MeasurableSpace β} [inst : Div β] [Measurab
leDiv₂ β] {f : ι → Ω → β},   ProbabilityTheory.iIndepFun f μ →     (∀ (i : ι), M
easurable (f i)) → ∀ (i j k : ι), i ≠ k → j ≠ k → ProbabilityTheory.IndepFun (f 
i / f j) (f k) μ
参数：∀ (i : ι), Measurable (f i)；i j k : ι；f i / f j；f k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.indepFun_div_left`：∀ {α : Type u_1} {
Ω : Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω}  
 {κ : ProbabilityTheory.Kernel α Ω} {μ : M…
-/
lemma iIndepFun.indepFun_div_left (hf_indep : iIndepFun f μ)
    (hf_meas : ∀ i, Measurable (f i)) (i j k : ι) (hik : i ≠ k) (hjk : j ≠ k) :
    IndepFun (f i / f j) (f k) μ :=
  Kernel.iIndepFun.indepFun_div_left hf_indep hf_meas i j k hik hjk

@[to_additive]
/-
**ProbabilityTheory.iIndepFun.indepFun_div_left** 是 Mathlib 中的一个定理，位于命名空间 `Proba
bilityTheory.iIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {_mΩ : MeasurableSpace Ω} {μ : MeasureTheo
ry.Measure Ω} {β : Type u_10}   {m : MeasurableSpace β} [inst : Div β] [Measurab
leDiv₂ β] {f : ι → Ω → β},   ProbabilityTheory.iIndepFun f μ →     (∀ (i : ι), M
easurable (f i)) → ∀ (i j k : ι), i ≠ k → j ≠ k → ProbabilityTheory.IndepFun (f 
i / f j) (f k) μ
参数：∀ (i : ι), Measurable (f i)；i j k : ι；f i / f j；f k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.indepFun_div_left`：∀ {α : Type u_1} {
Ω : Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω}  
 {κ : ProbabilityTheory.Kernel α Ω} {μ : M…
-/
lemma iIndepFun.indepFun_div_left₀ (hf_indep : iIndepFun f μ)
    (hf_meas : ∀ i, AEMeasurable (f i) μ) (i j k : ι) (hik : i ≠ k) (hjk : j ≠ k) :
    IndepFun (f i / f j) (f k) μ :=
  Kernel.iIndepFun.indepFun_div_left₀ hf_indep (by simp [hf_meas]) i j k hik hjk

@[to_additive]
/-
**ProbabilityTheory.iIndepFun.indepFun_div_right** 是 Mathlib 中的一个定理，位于命名空间 `Prob
abilityTheory.iIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {_mΩ : MeasurableSpace Ω} {μ : MeasureTheo
ry.Measure Ω} {β : Type u_10}   {m : MeasurableSpace β} [inst : Div β] [Measurab
leDiv₂ β] {f : ι → Ω → β},   ProbabilityTheory.iIndepFun f μ →     (∀ (i : ι), M
easurable (f i)) → ∀ (i j k : ι), i ≠ j → i ≠ k → ProbabilityTheory.IndepFun (f 
i) (f j / f k) μ
参数：∀ (i : ι), Measurable (f i)；i j k : ι；f i；f j / f k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.indepFun_div_right`：∀ {α : Type u_1} 
{Ω : Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω} 
  {κ : ProbabilityTheory.Kernel α Ω} {μ : M…
-/
lemma iIndepFun.indepFun_div_right (hf_indep : iIndepFun f μ)
    (hf_meas : ∀ i, Measurable (f i)) (i j k : ι) (hij : i ≠ j) (hik : i ≠ k) :
    IndepFun (f i) (f j / f k) μ :=
  Kernel.iIndepFun.indepFun_div_right hf_indep hf_meas i j k hij hik

@[to_additive]
/-
**ProbabilityTheory.iIndepFun.indepFun_div_right** 是 Mathlib 中的一个定理，位于命名空间 `Prob
abilityTheory.iIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {_mΩ : MeasurableSpace Ω} {μ : MeasureTheo
ry.Measure Ω} {β : Type u_10}   {m : MeasurableSpace β} [inst : Div β] [Measurab
leDiv₂ β] {f : ι → Ω → β},   ProbabilityTheory.iIndepFun f μ →     (∀ (i : ι), M
easurable (f i)) → ∀ (i j k : ι), i ≠ j → i ≠ k → ProbabilityTheory.IndepFun (f 
i) (f j / f k) μ
参数：∀ (i : ι), Measurable (f i)；i j k : ι；f i；f j / f k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.indepFun_div_right`：∀ {α : Type u_1} 
{Ω : Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω} 
  {κ : ProbabilityTheory.Kernel α Ω} {μ : M…
-/
lemma iIndepFun.indepFun_div_right₀ (hf_indep : iIndepFun f μ)
    (hf_meas : ∀ i, AEMeasurable (f i) μ) (i j k : ι) (hij : i ≠ j) (hik : i ≠ k) :
    IndepFun (f i) (f j / f k) μ :=
  Kernel.iIndepFun.indepFun_div_right₀ hf_indep (by simp [hf_meas]) i j k hij hik

@[to_additive]
/-
**ProbabilityTheory.iIndepFun.indepFun_div_div** 是 Mathlib 中的一个定理，位于命名空间 `Probab
ilityTheory.iIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {_mΩ : MeasurableSpace Ω} {μ : MeasureTheo
ry.Measure Ω} {β : Type u_10}   {m : MeasurableSpace β} [inst : Div β] [Measurab
leDiv₂ β] {f : ι → Ω → β},   ProbabilityTheory.iIndepFun f μ →     (∀ (i : ι), M
easurable (f i)) →       ∀ (i j k l : ι), i ≠ k → i ≠ l → j ≠ k → j ≠ l → Probab
ilityTheory.IndepFun (f i / f j) (f k / f l) μ
参数：∀ (i : ι), Measurable (f i)；i j k l : ι；f i / f j；f k / f l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.indepFun_div_div`：∀ {α : Type u_1} {Ω
 : Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω}   
{κ : ProbabilityTheory.Kernel α Ω} {μ : M…
-/
lemma iIndepFun.indepFun_div_div (hf_indep : iIndepFun f μ)
    (hf_meas : ∀ i, Measurable (f i))
    (i j k l : ι) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    IndepFun (f i / f j) (f k / f l) μ :=
  Kernel.iIndepFun.indepFun_div_div hf_indep hf_meas i j k l hik hil hjk hjl

@[to_additive]
/-
**ProbabilityTheory.iIndepFun.indepFun_div_div** 是 Mathlib 中的一个定理，位于命名空间 `Probab
ilityTheory.iIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {_mΩ : MeasurableSpace Ω} {μ : MeasureTheo
ry.Measure Ω} {β : Type u_10}   {m : MeasurableSpace β} [inst : Div β] [Measurab
leDiv₂ β] {f : ι → Ω → β},   ProbabilityTheory.iIndepFun f μ →     (∀ (i : ι), M
easurable (f i)) →       ∀ (i j k l : ι), i ≠ k → i ≠ l → j ≠ k → j ≠ l → Probab
ilityTheory.IndepFun (f i / f j) (f k / f l) μ
参数：∀ (i : ι), Measurable (f i)；i j k l : ι；f i / f j；f k / f l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.indepFun_div_div`：∀ {α : Type u_1} {Ω
 : Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω}   
{κ : ProbabilityTheory.Kernel α Ω} {μ : M…
-/
lemma iIndepFun.indepFun_div_div₀ (hf_indep : iIndepFun f μ)
    (hf_meas : ∀ i, AEMeasurable (f i) μ)
    (i j k l : ι) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    IndepFun (f i / f j) (f k / f l) μ :=
  Kernel.iIndepFun.indepFun_div_div₀ hf_indep (by simp [hf_meas]) i j k l hik hil hjk hjl

end Div

section CommMonoid
variable {β : Type*} {m : MeasurableSpace β} [CommMonoid β] [MeasurableMul₂ β] {f : ι → Ω → β}

@[to_additive]
/-
**ProbabilityTheory.iIndepFun.indepFun_finsetProd_of_notMem** 是 Mathlib 中的一个定理，位
于命名空间 `ProbabilityTheory.iIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {_mΩ : MeasurableSpace Ω} {μ : MeasureTheo
ry.Measure Ω} {β : Type u_10}   {m : MeasurableSpace β} [inst : CommMonoid β] [M
easurableMul₂ β] {f : ι → Ω → β},   ProbabilityTheory.iIndepFun f μ →     (∀ (i 
: ι), Measurable (f i)) → ∀ {s : Finset ι} {i : ι}, i ∉ s → ProbabilityTheory.In
depFun (∏ j ∈ s, f j) (f i) μ
参数：∀ (i : ι), Measurable (f i)；∏ j ∈ s, f j；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.indepFun_finsetProd_of_notMem`：∀ {α :
 Type u_1} {Ω : Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {mΩ : Measurab
leSpace Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ : M…
-/
lemma iIndepFun.indepFun_finsetProd_of_notMem (hf_Indep : iIndepFun f μ)
    (hf_meas : ∀ i, Measurable (f i)) {s : Finset ι} {i : ι} (hi : i ∉ s) :
    IndepFun (∏ j ∈ s, f j) (f i) μ :=
  Kernel.iIndepFun.indepFun_finsetProd_of_notMem hf_Indep hf_meas hi

@[deprecated (since := "2026-04-08")]
alias iIndepFun.indepFun_finset_sum_of_notMem := iIndepFun.indepFun_finsetSum_of_notMem

@[to_additive existing, deprecated (since := "2026-04-08")]
alias iIndepFun.indepFun_finset_prod_of_notMem := iIndepFun.indepFun_finsetProd_of_notMem

@[to_additive]
/-
**ProbabilityTheory.iIndepFun.indepFun_finsetProd_of_notMem** 是 Mathlib 中的一个定理，位
于命名空间 `ProbabilityTheory.iIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {_mΩ : MeasurableSpace Ω} {μ : MeasureTheo
ry.Measure Ω} {β : Type u_10}   {m : MeasurableSpace β} [inst : CommMonoid β] [M
easurableMul₂ β] {f : ι → Ω → β},   ProbabilityTheory.iIndepFun f μ →     (∀ (i 
: ι), Measurable (f i)) → ∀ {s : Finset ι} {i : ι}, i ∉ s → ProbabilityTheory.In
depFun (∏ j ∈ s, f j) (f i) μ
参数：∀ (i : ι), Measurable (f i)；∏ j ∈ s, f j；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.indepFun_finsetProd_of_notMem`：∀ {α :
 Type u_1} {Ω : Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {mΩ : Measurab
leSpace Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ : M…
-/
lemma iIndepFun.indepFun_finsetProd_of_notMem₀ (hf_Indep : iIndepFun f μ)
    (hf_meas : ∀ i, AEMeasurable (f i) μ) {s : Finset ι} {i : ι} (hi : i ∉ s) :
    IndepFun (∏ j ∈ s, f j) (f i) μ :=
  Kernel.iIndepFun.indepFun_finsetProd_of_notMem₀ hf_Indep (by simp [hf_meas]) hi

@[deprecated (since := "2026-04-08")]
alias iIndepFun.indepFun_finset_sum_of_notMem₀ := iIndepFun.indepFun_finsetSum_of_notMem₀

@[to_additive existing, deprecated (since := "2026-04-08")]
alias iIndepFun.indepFun_finset_prod_of_notMem₀ := iIndepFun.indepFun_finsetProd_of_notMem₀

@[to_additive]
/-
**ProbabilityTheory.iIndepFun.indepFun_prod_range_succ** 是 Mathlib 中的一个定理，位于命名空间
 `ProbabilityTheory.iIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {_mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {
β : Type u_10} {m : MeasurableSpace β}   [inst : CommMonoid β] [MeasurableMul₂ β
] {f : ℕ → Ω → β},   ProbabilityTheory.iIndepFun f μ →     (∀ (i : ℕ), Measurabl
e (f i)) → ∀ (n : ℕ), ProbabilityTheory.IndepFun (∏ j ∈ Finset.range n, f j) (f 
n) μ
参数：∀ (i : ℕ), Measurable (f i)；n : ℕ；∏ j ∈ Finset.range n, f j；f n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.indepFun_prod_range_succ`：∀ {α : Type
 u_1} {Ω : Type u_2} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω} {κ : Prob
abilityTheory.Kernel α Ω}   {μ : MeasureTheory.Me…
-/
lemma iIndepFun.indepFun_prod_range_succ {f : ℕ → Ω → β} (hf_Indep : iIndepFun f μ)
    (hf_meas : ∀ i, Measurable (f i)) (n : ℕ) : IndepFun (∏ j ∈ Finset.range n, f j) (f n) μ :=
  Kernel.iIndepFun.indepFun_prod_range_succ hf_Indep hf_meas n

@[to_additive]
/-
**ProbabilityTheory.iIndepFun.indepFun_prod_range_succ** 是 Mathlib 中的一个定理，位于命名空间
 `ProbabilityTheory.iIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {_mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {
β : Type u_10} {m : MeasurableSpace β}   [inst : CommMonoid β] [MeasurableMul₂ β
] {f : ℕ → Ω → β},   ProbabilityTheory.iIndepFun f μ →     (∀ (i : ℕ), Measurabl
e (f i)) → ∀ (n : ℕ), ProbabilityTheory.IndepFun (∏ j ∈ Finset.range n, f j) (f 
n) μ
参数：∀ (i : ℕ), Measurable (f i)；n : ℕ；∏ j ∈ Finset.range n, f j；f n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.indepFun_prod_range_succ`：∀ {α : Type
 u_1} {Ω : Type u_2} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω} {κ : Prob
abilityTheory.Kernel α Ω}   {μ : MeasureTheory.Me…
-/
lemma iIndepFun.indepFun_prod_range_succ₀ {f : ℕ → Ω → β} (hf_Indep : iIndepFun f μ)
    (hf_meas : ∀ i, AEMeasurable (f i) μ) (n : ℕ) :
    IndepFun (∏ j ∈ Finset.range n, f j) (f n) μ :=
  hf_Indep.indepFun_finsetProd_of_notMem₀ hf_meas (by simp)

end CommMonoid

/-
**ProbabilityTheory.iIndepSet.iIndepFun_indicator** 是 Mathlib 中的一个定理，位于命名空间 `Pro
babilityTheory.iIndepSet`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {β : Type u_6} {_mΩ : MeasurableSpace Ω} {
μ : MeasureTheory.Measure Ω} [inst : Zero β]   [inst_1 : One β] {m : MeasurableS
pace β} {s : ι → Set Ω},   ProbabilityTheory.iIndepSet s μ → ProbabilityTheory.i
IndepFun (fun n => (s n).indicator fun _ω => 1) μ
参数：fun n => (s n).indicator fun _ω => 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepSet.iIndepFun_indicator`：∀ {α : Type u_1}
 {Ω : Type u_2} {ι : Type u_3} {β : Type u_4} {mα : MeasurableSpace α} {mΩ : Mea
surableSpace Ω}   {κ : ProbabilityTheory.Ker…
-/
theorem iIndepSet.iIndepFun_indicator [Zero β] [One β] {m : MeasurableSpace β} {s : ι → Set Ω}
    (hs : iIndepSet s μ) :
    iIndepFun (fun n => (s n).indicator fun _ω => (1 : β)) μ :=
  Kernel.iIndepSet.iIndepFun_indicator hs
/-
**ProbabilityTheory.Indep.indicator_indepFun** 是 Mathlib 中的一个定理，位于命名空间 `Probabil
ityTheory.Indep`。
形式化陈述：∀ {Ω : Type u_1} {_mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {
m : MeasurableSpace Ω} {M : Type u_10}   {𝓧 : Type u_11} [inst : Zero M] [inst_1
 : MeasurableSpace M] (c : M) {m𝓧 : MeasurableSpace 𝓧} {A : Set Ω} {X : Ω → 𝓧}, 
  MeasurableSet A →     ProbabilityTheory.Indep m (MeasurableSpace.comap X m𝓧) μ
 → ProbabilityTheory.IndepFun (A.indicator fun x => c) X μ
参数：c : M；MeasurableSpace.comap X m𝓧；A.indicator fun x => c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.Indep.indicator_const_indepFun`：∀ {α : Type u_1
} {Ω : Type u_2} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω} {κ : Probabil
ityTheory.Kernel α Ω}   {μ : MeasureTheory.Me…
-/
lemma Indep.indicator_indepFun {m : MeasurableSpace Ω} {M 𝓧 : Type*}
    [Zero M] [MeasurableSpace M] (c : M) {m𝓧 : MeasurableSpace 𝓧} {A : Set Ω}
    {X : Ω → 𝓧} (hA : MeasurableSet[m] A) (h : Indep m (m𝓧.comap X) μ) :
    (A.indicator (fun _ ↦ c)) ⟂ᵢ[μ] X :=
  Kernel.Indep.indicator_const_indepFun c hA h

end IndepFun

variable {ι Ω α β : Type*} {mΩ : MeasurableSpace Ω} {mα : MeasurableSpace α}
  {mβ : MeasurableSpace β} {μ : Measure Ω} {X : ι → Ω → α} {Y : ι → Ω → β} {f : _ → Set Ω}
  {t : ι → Set β} {s : Finset ι}

/-- The probability of an intersection of preimages conditioning on another intersection factors
into a product. -/
/-
**ProbabilityTheory.cond_iInter** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：cond_iInter [Finite ι] (hY : forall i, Measurable (Y i)) (hindep : iIndepF
un (fun i ω => (X i ω, Y i ω)) μ) (hf : forall i in s, MeasurableSet[mα.comap (X
 i)] (f i)) (hy : forall i ∉ s, μ (Y i ⁻¹' t i) != 0) (ht : forall i, Measurable
Set (t i)) : μ[⋂ i in s, f i | ⋂ i, Y i ⁻¹' t i] = ∏ i in s, μ[f i | Y i in t i]
参数：hY : forall i, Measurable (Y i)；hindep : iIndepFun (fun i ω => (X i ω, Y i ω)
) μ；hf : forall i in s, MeasurableSet[mα.comap (X i)] (f i)；hy : forall i ∉ s, μ
 (Y i ⁻¹' t i) != 0；ht : forall i, MeasurableSet (t i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.iIndepFun.isProbabilityMeasure`：∀ {Ω : Type u_1} {ι : 
Type u_2} {_mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {β : ι → Type 
u_10}   {m : (i : ι) → MeasurableSpace…
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.cond_apply`：cond_apply (hms : MeasurableSet s) (μ : Me
asure Ω) (t : Set Ω) : μ[t | s] = (μ s)⁻¹ * μ (s inter t)
· 使用定理 `MeasurableSet.iInter`：MeasurableSet.iInter [Countable ι] {f : ι -> Set α
} (h : forall b, MeasurableSet (f b)) : MeasurableSet (⋂ b, f b)
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.iInter_ite`：iInter_ite (f g : ι -> Set α) : ⋂ i, (if p i then f i el
se g i) = (⋂ (i) (_ : p i), f i) inter ⋂ (i) (_ : ¬p i), g i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_univ`：iInter_univ : (⋂ _ : ι, univ : Set α) = univ
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.iInter_inter_distrib`：iInter_inter_distrib (s : ι -> Set β) (t : ι -
> Set β) : ⋂ i, s i inter t i = (⋂ i, s i) inter ⋂ i, t i
· 使用引理 `Set.iInter_congr`：iInter_congr {s t : ι -> Set α} (h : forall i, s i = t
 i) : ⋂ i, s i = ⋂ i, t i
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `ProbabilityTheory.iIndepFun.meas_iInter`：∀ {Ω : Type u_1} {ι : Type u_2}
 {κ : ι → Type u_5} {x : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {s : ι
 → Set Ω}   [inst : Fintype ι…
· 使用定理 `MeasurableSet.prod`：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace
 α} {mβ : MeasurableSpace β} {s : Set α} {t : Set β},   MeasurableSet s → Measur
ableSet …
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
（共 41 条，此处仅展示前 30 条）

--- 原说明 ---
The probability of an intersection of preimages conditioning on another intersec
tion factors
into a product.
-/
lemma cond_iInter [Finite ι] (hY : ∀ i, Measurable (Y i))
    (hindep : iIndepFun (fun i ω ↦ (X i ω, Y i ω)) μ)
    (hf : ∀ i ∈ s, MeasurableSet[mα.comap (X i)] (f i))
    (hy : ∀ i ∉ s, μ (Y i ⁻¹' t i) ≠ 0) (ht : ∀ i, MeasurableSet (t i)) :
    μ[⋂ i ∈ s, f i | ⋂ i, Y i ⁻¹' t i] = ∏ i ∈ s, μ[f i | Y i in t i] := by
  have : IsProbabilityMeasure (μ : Measure Ω) := hindep.isProbabilityMeasure
  classical
  cases nonempty_fintype ι
  let g (i' : ι) := if i' ∈ s then Y i' ⁻¹' t i' ∩ f i' else Y i' ⁻¹' t i'
  calc
    _ = (μ (⋂ i, Y i ⁻¹' t i))⁻¹ * μ ((⋂ i, Y i ⁻¹' t i) ∩ ⋂ i ∈ s, f i) := by
      rw [cond_apply]; exact .iInter fun i ↦ hY i (ht i)
    _ = (μ (⋂ i, Y i ⁻¹' t i))⁻¹ * μ (⋂ i, g i) := by
      congr
      calc
        _ = (⋂ i, Y i ⁻¹' t i) ∩ ⋂ i, if i ∈ s then f i else .univ := by
          simp only [Set.iInter_ite, Set.iInter_univ, Set.inter_univ]
        _ = ⋂ i, Y i ⁻¹' t i ∩ (if i ∈ s then f i else .univ) := by rw [Set.iInter_inter_distrib]
        _ = _ := Set.iInter_congr fun i ↦ by by_cases hi : i ∈ s <;> simp [hi, g]
    _ = (∏ i, μ (Y i ⁻¹' t i))⁻¹ * μ (⋂ i, g i) := by
      rw [hindep.meas_iInter]
      exact fun i ↦ ⟨.univ ×ˢ t i, MeasurableSet.univ.prod (ht _), by ext; simp⟩
    _ = (∏ i, μ (Y i ⁻¹' t i))⁻¹ * ∏ i, μ (g i) := by
      rw [hindep.meas_iInter]
      intro i
      by_cases hi : i ∈ s <;> simp only [hi, ↓reduceIte, g]
      · obtain ⟨A, hA, hA'⟩ := hf i hi
        exact .inter ⟨.univ ×ˢ t i, MeasurableSet.univ.prod (ht _), by ext; simp⟩
          ⟨A ×ˢ Set.univ, hA.prod .univ, by ext; simp [← hA']⟩
      · exact ⟨.univ ×ˢ t i, MeasurableSet.univ.prod (ht _), by ext; simp⟩
    _ = ∏ i, (μ (Y i ⁻¹' t i))⁻¹ * μ (g i) := by
      rw [Finset.prod_mul_distrib, ENNReal.prod_inv_distrib]
      exact fun _ _ i _ _ ↦ .inr <| measure_ne_top _ _
    _ = ∏ i, if i ∈ s then μ[f i | Y i ⁻¹' t i] else 1 := by
      refine Finset.prod_congr rfl fun i _ ↦ ?_
      by_cases hi : i ∈ s
      · simp only [hi, ↓reduceIte, g, cond_apply (hY i (ht i))]
      · simp only [hi, ↓reduceIte, g, ENNReal.inv_mul_cancel (hy i hi) (measure_ne_top μ _)]
    _ = _ := by simp
/-
**ProbabilityTheory.iIndepFun.cond** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory.
iIndepFun`。
形式化陈述：∀ {ι : Type u_6} {Ω : Type u_7} {α : Type u_8} {β : Type u_9} {mΩ : Measur
ableSpace Ω} {mα : MeasurableSpace α}   {mβ : MeasurableSpace β} {μ : MeasureThe
ory.Measure Ω} {X : ι → Ω → α} {Y : ι → Ω → β} {t : ι → Set β} [Finite ι],   (∀ 
(i : ι), Measurable (Y i)) →     ProbabilityTheory.iIndepFun (fun i ω => (X i ω,
 Y i ω)) μ →       (∀ (i : ι), μ (Y i ⁻¹' t i) ≠ 0) →         (∀ (i : ι), Measur
ableSet (t i)) → ProbabilityTheory.iIndepFun X μ[|⋂ i, Y i ⁻¹' t i]
参数：∀ (i : ι), Measurable (Y i)；fun i ω => (X i ω, Y i ω)；∀ (i : ι), μ (Y i ⁻¹' t
 i) ≠ 0；∀ (i : ι), MeasurableSet (t i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.iIndepFun_iff`：iIndepFun_iff {β : ι -> Type*} (m : for
all x : ι, MeasurableSpace (β x)) (f : forall x : ι, Ω -> β x) (μ : Measure Ω) :
 iIndepFun f μ ↔ fora…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iInter_iInter_eq_left`：iInter_iInter_eq_left {b : β} {s : forall x :
 β, x = b -> Set α} : ⋂ (x) (h : x = b), s x h = s b rfl
· 使用定理 `Finset.prod_singleton`：prod_singleton (f : ι -> M) (a : ι) : ∏ x in sing
leton a, f x = f a
· 使用引理 `ProbabilityTheory.cond_iInter`：cond_iInter [Finite ι] (hY : forall i, Me
asurable (Y i)) (hindep : iIndepFun (fun i ω => (X i ω, Y i ω)) μ) (hf : forall 
i in s, MeasurableS…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_singleton`：mem_singleton {a b : α} : b in ({a} : Finset α) ↔ 
b = a
-/
lemma iIndepFun.cond [Finite ι] (hY : ∀ i, Measurable (Y i))
    (hindep : iIndepFun (fun i ω ↦ (X i ω, Y i ω)) μ)
    (hy : ∀ i, μ (Y i ⁻¹' t i) ≠ 0) (ht : ∀ i, MeasurableSet (t i)) :
    iIndepFun X μ[|⋂ i, Y i ⁻¹' t i] := by
  rw [iIndepFun_iff]
  intro s f hf
  convert! cond_iInter hY hindep hf (fun i _ ↦ hy _) ht using 2 with i hi
  simpa using cond_iInter hY hindep (fun j hj ↦ hf _ <| Finset.mem_singleton.1 hj ▸ hi)
    (fun i _ ↦ hy _) ht

section Monoid

variable {M : Type*} [Monoid M] [MeasurableSpace M] [MeasurableMul₂ M]

@[to_additive]
/-
**ProbabilityTheory.IndepFun.map_mul_eq_map_mconv_map** 是 Mathlib 中的一个定理，位于命名空间 
`ProbabilityTheory.IndepFun`。
形式化陈述：∀ {Ω : Type u_7} {mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {M
 : Type u_10} [inst : Monoid M]   [inst_1 : MeasurableSpace M] [MeasurableMul₂ M
] [MeasureTheory.IsFiniteMeasure μ] {f g : Ω → M},   Measurable f →     Measurab
le g →       ProbabilityTheory.IndepFun f g μ →         MeasureTheory.Measure.ma
p (f * g) μ = (MeasureTheory.Measure.map f μ).mconv (MeasureTheory.Measure.map g
 μ)
参数：f * g；MeasureTheory.Measure.map f μ；MeasureTheory.Measure.map g μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IndepFun.map_mul_eq_map_mconv_map₀`：∀ {Ω : Type u_7} {
mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {M : Type u_10} [inst : Mo
noid M]   [inst_1 : MeasurableSpace M] [Me…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
-/
theorem IndepFun.map_mul_eq_map_mconv_map₀'
    {f g : Ω → M} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (σf : SigmaFinite (μ.map f)) (σg : SigmaFinite (μ.map g)) (hfg : f ⟂ᵢ[μ] g) :
    μ.map (f * g) = (μ.map f) ∗ₘ (μ.map g) := by
  conv in f * g => change (fun x ↦ x.1 * x.2) ∘ (fun ω ↦ (f ω, g ω))
  rw [← measurable_mul.aemeasurable.map_map_of_aemeasurable (hf.prodMk hg),
    (indepFun_iff_map_prod_eq_prod_map_map' hf hg σf σg).mp hfg, Measure.mconv]

@[to_additive]
/-
**ProbabilityTheory.IndepFun.map_mul_eq_map_mconv_map'** 是 Mathlib 中的一个定理，位于命名空间
 `ProbabilityTheory.IndepFun`。
形式化陈述：∀ {Ω : Type u_7} {mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {M
 : Type u_10} [inst : Monoid M]   [inst_1 : MeasurableSpace M] [MeasurableMul₂ M
] {f g : Ω → M},   Measurable f →     Measurable g →       MeasureTheory.SigmaFi
nite (MeasureTheory.Measure.map f μ) →         MeasureTheory.SigmaFinite (Measur
eTheory.Measure.map g μ) →           ProbabilityTheory.IndepFun f g μ →         
    MeasureTheory.Measure.map (f * g) μ = (MeasureTheory.Measure.map f μ).mconv 
(MeasureTheory.Measure.map g μ)
参数：MeasureTheory.Measure.map f μ；MeasureTheory.Measure.map g μ；f * g；MeasureTheo
ry.Measure.map f μ；MeasureTheory.Measure.map g μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IndepFun.map_mul_eq_map_mconv_map₀'`：∀ {Ω : Type u_7} 
{mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {M : Type u_10} [inst : M
onoid M]   [inst_1 : MeasurableSpace M] [Me…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
-/
theorem IndepFun.map_mul_eq_map_mconv_map'
    {f g : Ω → M} (hf : Measurable f) (hg : Measurable g)
    (σf : SigmaFinite (μ.map f)) (σg : SigmaFinite (μ.map g)) (hfg : f ⟂ᵢ[μ] g) :
    μ.map (f * g) = (μ.map f) ∗ₘ (μ.map g) :=
  hfg.map_mul_eq_map_mconv_map₀' hf.aemeasurable hg.aemeasurable σf σg

@[to_additive]
/-
**ProbabilityTheory.IndepFun.map_mul_eq_map_mconv_map** 是 Mathlib 中的一个定理，位于命名空间 
`ProbabilityTheory.IndepFun`。
形式化陈述：∀ {Ω : Type u_7} {mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {M
 : Type u_10} [inst : Monoid M]   [inst_1 : MeasurableSpace M] [MeasurableMul₂ M
] [MeasureTheory.IsFiniteMeasure μ] {f g : Ω → M},   Measurable f →     Measurab
le g →       ProbabilityTheory.IndepFun f g μ →         MeasureTheory.Measure.ma
p (f * g) μ = (MeasureTheory.Measure.map f μ).mconv (MeasureTheory.Measure.map g
 μ)
参数：f * g；MeasureTheory.Measure.map f μ；MeasureTheory.Measure.map g μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IndepFun.map_mul_eq_map_mconv_map₀`：∀ {Ω : Type u_7} {
mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {M : Type u_10} [inst : Mo
noid M]   [inst_1 : MeasurableSpace M] [Me…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
-/
theorem IndepFun.map_mul_eq_map_mconv_map₀
    [IsFiniteMeasure μ] {f g : Ω → M} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (hfg : f ⟂ᵢ[μ] g) :
    μ.map (f * g) = (μ.map f) ∗ₘ (μ.map g) := by
  apply hfg.map_mul_eq_map_mconv_map₀' hf hg
    <;> apply IsFiniteMeasure.toSigmaFinite

@[to_additive]
/-
**ProbabilityTheory.IndepFun.map_mul_eq_map_mconv_map** 是 Mathlib 中的一个定理，位于命名空间 
`ProbabilityTheory.IndepFun`。
形式化陈述：∀ {Ω : Type u_7} {mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {M
 : Type u_10} [inst : Monoid M]   [inst_1 : MeasurableSpace M] [MeasurableMul₂ M
] [MeasureTheory.IsFiniteMeasure μ] {f g : Ω → M},   Measurable f →     Measurab
le g →       ProbabilityTheory.IndepFun f g μ →         MeasureTheory.Measure.ma
p (f * g) μ = (MeasureTheory.Measure.map f μ).mconv (MeasureTheory.Measure.map g
 μ)
参数：f * g；MeasureTheory.Measure.map f μ；MeasureTheory.Measure.map g μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IndepFun.map_mul_eq_map_mconv_map₀`：∀ {Ω : Type u_7} {
mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {M : Type u_10} [inst : Mo
noid M]   [inst_1 : MeasurableSpace M] [Me…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
-/
theorem IndepFun.map_mul_eq_map_mconv_map
    [IsFiniteMeasure μ] {f g : Ω → M} (hf : Measurable f) (hg : Measurable g)
    (hfg : f ⟂ᵢ[μ] g) :
    μ.map (f * g) = (μ.map f) ∗ₘ (μ.map g) :=
  hfg.map_mul_eq_map_mconv_map₀ hf.aemeasurable hg.aemeasurable

end Monoid

end ProbabilityTheory

