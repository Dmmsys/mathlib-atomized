/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Independence.Kernel.IndepFun
public import Mathlib.Probability.Kernel.CompProdEqIff
public import Mathlib.Probability.Kernel.Composition.Lemmas
public import Mathlib.Probability.Kernel.Condexp

/-!
# Conditional Independence

We define conditional independence of sets/σ-algebras/functions with respect to a σ-algebra.

Two σ-algebras `m₁` and `m₂` are conditionally independent given a third σ-algebra `m'` if for all
`m₁`-measurable sets `t₁` and `m₂`-measurable sets `t₂`,
`μ⟦t₁ ∩ t₂ | m'⟧ =ᵐ[μ] μ⟦t₁ | m'⟧ * μ⟦t₂ | m'⟧`.

On standard Borel spaces, the conditional expectation with respect to `m'` defines a kernel
`ProbabilityTheory.condExpKernel`, and the definition above is equivalent to
`∀ᵐ ω ∂μ, condExpKernel μ m' ω (t₁ ∩ t₂) = condExpKernel μ m' ω t₁ * condExpKernel μ m' ω t₂`.
We use this property as the definition of conditional independence.

## Main definitions

We provide four definitions of conditional independence:
* `iCondIndepSets`: conditional independence of a family of sets of sets `pi : ι → Set (Set Ω)`.
  This is meant to be used with π-systems.
* `iCondIndep`: conditional independence of a family of measurable space structures
  `m : ι → MeasurableSpace Ω`,
* `iCondIndepSet`: conditional independence of a family of sets `s : ι → Set Ω`,
* `iCondIndepFun`: conditional independence of a family of functions. For measurable spaces
  `m : Π (i : ι), MeasurableSpace (β i)`, we consider functions `f : Π (i : ι), Ω → β i`.

Additionally, we provide four corresponding statements for two measurable space structures (resp.
sets of sets, sets, functions) instead of a family. These properties are denoted by the same names
as for a family, but without the starting `i`, for example `CondIndepFun` is the version of
`iCondIndepFun` for two functions.

## Main statements

* `ProbabilityTheory.iCondIndepSets.iCondIndep`: if π-systems are conditionally independent as sets
  of sets, then the measurable space structures they generate are conditionally independent.
* `ProbabilityTheory.condIndepSets.condIndep`: variant with two π-systems.

## Notation

* `X ⟂ᵢ[Z, hZ; μ] Y` for `CondIndepFun (MeasurableSpace.comap Z inferInstance) hZ.comap_le X Y μ`,
  independence of `X` and `Y` given `Z`.
* `X ⟂ᵢ[Z, hZ] Y` for the cases of `μ = volume`.

These notations are scoped in the `ProbabilityTheory` namespace.

## Implementation notes

The definitions of conditional independence in this file are a particular case of independence with
respect to a kernel and a measure, as defined in the file
`Mathlib/Probability/Independence/Kernel.lean`.
The kernel used is `ProbabilityTheory.condExpKernel`.

-/

@[expose] public section

open MeasureTheory MeasurableSpace

open scoped MeasureTheory ENNReal

namespace ProbabilityTheory

variable {Ω ι : Type*}

section Definitions

section

variable (m' : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω] (hm' : m' ≤ mΩ)

/-- A family of sets of sets `π : ι → Set (Set Ω)` is conditionally independent given `m'` with
respect to a measure `μ` if for any finite set of indices `s = {i_1, ..., i_n}`, for any sets
`f i_1 ∈ π i_1, ..., f i_n ∈ π i_n`, then `μ⟦⋂ i in s, f i | m'⟧ =ᵐ[μ] ∏ i ∈ s, μ⟦f i | m'⟧`.
See `ProbabilityTheory.iCondIndepSets_iff`.
It will be used for families of π-systems. -/
/-
**ProbabilityTheory.iCondIndepSets** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory`
。
形式化陈述：iCondIndepSets (π : ι -> Set (Set Ω)) (μ : Measure Ω
参数：π : ι -> Set (Set Ω)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family of sets of sets `π : ι → Set (Set Ω)` is conditionally independent give
n `m'` with
respect to a measure `μ` if for any finite set of indices `s = {i_1, ..., i_n}`,
 for any sets
`f i_1 ∈ π i_1, ..., f i_n ∈ π i_n`, then `μ⟦⋂ i in s, f i | m'⟧ =ᵐ[μ] ∏ i ∈ s, 
μ⟦f i | m'⟧`.
See `ProbabilityTheory.iCondIndepSets_iff`.
It will be used for families of π-systems.
-/
def iCondIndepSets (π : ι → Set (Set Ω)) (μ : Measure Ω := by volume_tac) [IsFiniteMeasure μ] :
    Prop :=
  Kernel.iIndepSets π (condExpKernel μ m') (μ.trim hm')

/-- Two sets of sets `s₁, s₂` are conditionally independent given `m'` with respect to a measure
`μ` if for any sets `t₁ ∈ s₁, t₂ ∈ s₂`, then `μ⟦t₁ ∩ t₂ | m'⟧ =ᵐ[μ] μ⟦t₁ | m'⟧ * μ⟦t₂ | m'⟧`.
See `ProbabilityTheory.condIndepSets_iff`. -/
/-
**ProbabilityTheory.CondIndepSets** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory`。
形式化陈述：CondIndepSets (s1 s2 : Set (Set Ω)) (μ : Measure Ω
参数：s1 s2 : Set (Set Ω)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two sets of sets `s₁, s₂` are conditionally independent given `m'` with respect 
to a measure
`μ` if for any sets `t₁ ∈ s₁, t₂ ∈ s₂`, then `μ⟦t₁ ∩ t₂ | m'⟧ =ᵐ[μ] μ⟦t₁ | m'⟧ *
 μ⟦t₂ | m'⟧`.
See `ProbabilityTheory.condIndepSets_iff`.
-/
def CondIndepSets (s1 s2 : Set (Set Ω)) (μ : Measure Ω := by volume_tac) [IsFiniteMeasure μ] :
    Prop :=
  Kernel.IndepSets s1 s2 (condExpKernel μ m') (μ.trim hm')

/-- A family of measurable space structures (i.e. of σ-algebras) is conditionally independent given
`m'` with respect to a measure `μ` (typically defined on a finer σ-algebra) if the family of sets of
measurable sets they define is independent. `m : ι → MeasurableSpace Ω` is conditionally independent
given `m'` with respect to measure `μ` if for any finite set of indices `s = {i_1, ..., i_n}`, for
any sets `f i_1 ∈ m i_1, ..., f i_n ∈ m i_n`, then
`μ⟦⋂ i in s, f i | m'⟧ =ᵐ[μ] ∏ i ∈ s, μ⟦f i | m'⟧ `.
See `ProbabilityTheory.iCondIndep_iff`. -/
/-
**ProbabilityTheory.iCondIndep** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory`。
形式化陈述：iCondIndep (m : ι -> MeasurableSpace Ω) (μ : @Measure Ω mΩ
参数：m : ι -> MeasurableSpace Ω。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family of measurable space structures (i.e. of σ-algebras) is conditionally in
dependent given
`m'` with respect to a measure `μ` (typically defined on a finer σ-algebra) if t
he family of sets of
measurable sets they define is independent. `m : ι → MeasurableSpace Ω` is condi
tionally independent
given `m'` with respect to measure `μ` if for any finite set of indices `s = {i_
1, ..., i_n}`, for
any sets `f i_1 ∈ m i_1, ..., f i_n ∈ m i_n`, then
`μ⟦⋂ i in s, f i | m'⟧ =ᵐ[μ] ∏ i ∈ s, μ⟦f i | m'⟧ `.
See `ProbabilityTheory.iCondIndep_iff`.
-/
def iCondIndep (m : ι → MeasurableSpace Ω)
    (μ : @Measure Ω mΩ := by volume_tac) [IsFiniteMeasure μ] : Prop :=
  Kernel.iIndep m (condExpKernel (mΩ := mΩ) μ m') (μ.trim hm')

end

/-- Two measurable space structures (or σ-algebras) `m₁, m₂` are conditionally independent given
`m'` with respect to a measure `μ` (defined on a third σ-algebra) if for any sets
`t₁ ∈ m₁, t₂ ∈ m₂`, `μ⟦t₁ ∩ t₂ | m'⟧ =ᵐ[μ] μ⟦t₁ | m'⟧ * μ⟦t₂ | m'⟧`.
See `ProbabilityTheory.condIndep_iff`. -/
/-
**ProbabilityTheory.CondIndep** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory`。
形式化陈述：CondIndep (m' m₁ m₂ : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} [Standar
dBorelSpace Ω] (hm' : m' <= mΩ) (μ : Measure Ω
参数：m' m₁ m₂ : MeasurableSpace Ω；hm' : m' <= mΩ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two measurable space structures (or σ-algebras) `m₁, m₂` are conditionally indep
endent given
`m'` with respect to a measure `μ` (defined on a third σ-algebra) if for any set
s
`t₁ ∈ m₁, t₂ ∈ m₂`, `μ⟦t₁ ∩ t₂ | m'⟧ =ᵐ[μ] μ⟦t₁ | m'⟧ * μ⟦t₂ | m'⟧`.
See `ProbabilityTheory.condIndep_iff`.
-/
def CondIndep (m' m₁ m₂ : MeasurableSpace Ω)
    {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    (hm' : m' ≤ mΩ) (μ : Measure Ω := by volume_tac) [IsFiniteMeasure μ] : Prop :=
  Kernel.Indep m₁ m₂ (condExpKernel μ m') (μ.trim hm')

section

variable (m' : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
  (hm' : m' ≤ mΩ)

/-- A family of sets is conditionally independent if the family of measurable space structures they
generate is conditionally independent. For a set `s`, the generated measurable space has measurable
sets `∅, s, sᶜ, univ`.
See `ProbabilityTheory.iCondIndepSet_iff`. -/
/-
**ProbabilityTheory.iCondIndepSet** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory`。
形式化陈述：iCondIndepSet (s : ι -> Set Ω) (μ : Measure Ω
参数：s : ι -> Set Ω。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family of sets is conditionally independent if the family of measurable space 
structures they
generate is conditionally independent. For a set `s`, the generated measurable s
pace has measurable
sets `∅, s, sᶜ, univ`.
See `ProbabilityTheory.iCondIndepSet_iff`.
-/
def iCondIndepSet (s : ι → Set Ω) (μ : Measure Ω := by volume_tac) [IsFiniteMeasure μ] : Prop :=
  Kernel.iIndepSet s (condExpKernel μ m') (μ.trim hm')

/-- Two sets are conditionally independent if the two measurable space structures they generate are
conditionally independent. For a set `s`, the generated measurable space structure has measurable
sets `∅, s, sᶜ, univ`.
See `ProbabilityTheory.condIndepSet_iff`. -/
/-
**ProbabilityTheory.CondIndepSet** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory`。
形式化陈述：CondIndepSet (s t : Set Ω) (μ : Measure Ω
参数：s t : Set Ω。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two sets are conditionally independent if the two measurable space structures th
ey generate are
conditionally independent. For a set `s`, the generated measurable space structu
re has measurable
sets `∅, s, sᶜ, univ`.
See `ProbabilityTheory.condIndepSet_iff`.
-/
def CondIndepSet (s t : Set Ω) (μ : Measure Ω := by volume_tac) [IsFiniteMeasure μ] : Prop :=
  Kernel.IndepSet s t (condExpKernel μ m') (μ.trim hm')

/-- A family of functions defined on the same space `Ω` and taking values in possibly different
spaces, each with a measurable space structure, is conditionally independent if the family of
measurable space structures they generate on `Ω` is conditionally independent. For a function `g`
with codomain having measurable space structure `m`, the generated measurable space structure is
`m.comap g`.
See `ProbabilityTheory.iCondIndepFun_iff`. -/
/-
**ProbabilityTheory.iCondIndepFun** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory`。
形式化陈述：iCondIndepFun {β : ι -> Type*} [m : forall x : ι, MeasurableSpace (β x)] (
f : forall x : ι, Ω -> β x) (μ : Measure Ω
参数：β x；f : forall x : ι, Ω -> β x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family of functions defined on the same space `Ω` and taking values in possibl
y different
spaces, each with a measurable space structure, is conditionally independent if 
the family of
measurable space structures they generate on `Ω` is conditionally independent. F
or a function `g`
with codomain having measurable space structure `m`, the generated measurable sp
ace structure is
`m.comap g`.
See `ProbabilityTheory.iCondIndepFun_iff`.
-/
def iCondIndepFun {β : ι → Type*} [m : ∀ x : ι, MeasurableSpace (β x)]
    (f : ∀ x : ι, Ω → β x) (μ : Measure Ω := by volume_tac) [IsFiniteMeasure μ] : Prop :=
  Kernel.iIndepFun f (condExpKernel μ m') (μ.trim hm')

/-- Two functions are conditionally independent if the two measurable space structures they generate
are conditionally independent. For a function `f` with codomain having measurable space structure
`m`, the generated measurable space structure is `m.comap f`.
See `ProbabilityTheory.condIndepFun_iff`.
We use the notation `X ⟂ᵢ[Z, hZ; μ] Y` to write that `X` and `Y` are conditionally independent
given (the σ-algebra generated by) `Z` (scoped in `ProbabilityTheory`). -/
/-
**ProbabilityTheory.CondIndepFun** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory`。
形式化陈述：CondIndepFun {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ] (f : Ω 
-> β) (g : Ω -> γ) (μ : Measure Ω
参数：f : Ω -> β；g : Ω -> γ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two functions are conditionally independent if the two measurable space structur
es they generate
are conditionally independent. For a function `f` with codomain having measurabl
e space structure
`m`, the generated measurable space structure is `m.comap f`.
See `ProbabilityTheory.condIndepFun_iff`.
We use the notation `X ⟂ᵢ[Z, hZ; μ] Y` to write that `X` and `Y` are conditional
ly independent
given (the σ-algebra generated by) `Z` (scoped in `ProbabilityTheory`).
-/
def CondIndepFun {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    (f : Ω → β) (g : Ω → γ) (μ : Measure Ω := by volume_tac) [IsFiniteMeasure μ] : Prop :=
  Kernel.IndepFun f g (condExpKernel μ m') (μ.trim hm')

end

end Definitions

@[inherit_doc ProbabilityTheory.CondIndepFun]
scoped[ProbabilityTheory] notation3 X:50 " ⟂ᵢ[" Z ", " hZ "; " μ "] " Y:50 =>
  ProbabilityTheory.CondIndepFun (MeasurableSpace.comap Z inferInstance) (Measurable.comap_le hZ)
  X Y μ

@[inherit_doc ProbabilityTheory.CondIndepFun]
scoped[ProbabilityTheory] notation3 X:50 " ⟂ᵢ[" Z ", " hZ "] " Y:50 =>
  ProbabilityTheory.CondIndepFun (MeasurableSpace.comap Z inferInstance) (Measurable.comap_le hZ)
  X Y volume

section DefinitionLemmas

section
variable (m' : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω] (hm' : m' ≤ mΩ)

/-
**ProbabilityTheory.iCondIndepSets_iff** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityThe
ory`。
形式化陈述：iCondIndepSets_iff (π : ι -> Set (Set Ω)) (hπ : forall i s (_hs : s in π i
), MeasurableSet s) (μ : Measure Ω) [IsFiniteMeasure μ] : iCondIndepSets m' hm' 
π μ ↔ forall (s : Finset ι) {f : ι -> Set Ω} (_H : forall i, i in s -> f i in π 
i), μ⟦⋂ i in s, f i | m'⟧ =ᵐ[μ] ∏ i in s, (μ⟦f i | m'⟧)
参数：π : ι -> Set (Set Ω)；hπ : forall i s (_hs : s in π i), MeasurableSet s；μ : Me
asure Ω。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `ProbabilityTheory.condExpKernel_ae_eq_condExp`：condExpKernel_ae_eq_condE
xp (hm : m <= mΩ) {s : Set Ω} (hs : MeasurableSet s) : (fun ω => (condExpKernel 
μ m ω).real s) =ᵐ[μ] μ⟦s | m⟧
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `MeasureTheory.ae_ball_iff`：ae_ball_iff {ι : Type*} {S : Set ι} (hS : S.C
ountable) {p : α -> forall i in S, Prop} : (forallᵐ x ∂μ, forall i (hi : i in S)
, p x i hi) ↔ f…
· 使用定理 `Finset.countable_toSet`：Finset.countable_toSet (s : Finset α) : Set.Coun
table (↑s : Set α)
· 使用定理 `MeasurableSet.biInter`：MeasurableSet.biInter {f : β -> Set α} {s : Set β
} (hs : s.Countable) (h : forall b in s, MeasurableSet (f b)) : MeasurableSet (⋂
 b in s, f …
· 使用定理 `MeasureTheory.ae_eq_of_ae_eq_trim`：ae_eq_of_ae_eq_trim {E} {hm : m <= m0
} {f₁ f₂ : α -> E} (h12 : f₁ =ᵐ[μ.trim hm] f₂) : f₁ =ᵐ[μ] f₂
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.toReal_prod`：toReal_prod (s : Finset ι) (f : ι -> Real>=0∞) : (∏
 i in s, f i).toReal = ∏ i in s, (f i).toReal
· 使用定理 `Finset.prod_apply`：Finset.prod_apply {α : Type*} {M : α -> Type*} [foral
l a, CommMonoid (M a)] (a : α) (s : Finset ι) (g : ι -> forall a, M a) : (∏ c in
 s, g c…
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `MeasureTheory.StronglyMeasurable.ae_eq_trim_iff`：ae_eq_trim_iff (hm : m 
<= m₀) (hf : StronglyMeasurable[m] f) (hg : StronglyMeasurable[m] g) : f =ᵐ[μ.tr
im hm] g ↔ f =ᵐ[μ] g
· 使用定理 `ENNReal.instMetrizableSpace`：TopologicalSpace.MetrizableSpace ENNReal
· 使用定理 `ProbabilityTheory.stronglyMeasurable_condExpKernel`：stronglyMeasurable_c
ondExpKernel {s : Set Ω} (hs : MeasurableSet s) : StronglyMeasurable[m] fun ω =>
 condExpKernel μ m ω s
· 使用定理 `Measurable.stronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {f : α → 
β} {mα : MeasurableSpace α} [inst : MeasurableSpace β]   [inst_1 : TopologicalSp
ace β] [Topological…
· 使用定理 `TopologicalSpace.MetrizableSpace.toPseudoMetrizableSpace`：∀ {X : Type u_
5} {t : TopologicalSpace X} [self : TopologicalSpace.MetrizableSpace X],   Topol
ogicalSpace.PseudoMetrizableSpace X
· 使用定理 `ENNReal.instSecondCountableTopology`：SecondCountableTopology ENNReal
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Finset.measurable_fun_prod`：Finset.measurable_fun_prod (s : Finset ι) (h
f : forall i in s, Measurable (f i)) : Measurable fun a => ∏ i in s, f i a
· 使用定理 `ProbabilityTheory.measurable_condExpKernel`：measurable_condExpKernel {s 
: Set Ω} (hs : MeasurableSet s) : Measurable[m] fun ω => condExpKernel μ m ω s
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `ProbabilityTheory.IsFiniteKernel.isFiniteMeasure`：∀ {α : Type u_1} {β : 
Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheo
ry.Kernel α β}   [ProbabilityTheory.Is…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
（共 34 条，此处仅展示前 30 条）
-/
lemma iCondIndepSets_iff (π : ι → Set (Set Ω)) (hπ : ∀ i s (_hs : s ∈ π i), MeasurableSet s)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    iCondIndepSets m' hm' π μ ↔ ∀ (s : Finset ι) {f : ι → Set Ω} (_H : ∀ i, i ∈ s → f i ∈ π i),
      μ⟦⋂ i ∈ s, f i | m'⟧ =ᵐ[μ] ∏ i ∈ s, (μ⟦f i | m'⟧) := by
  simp only [iCondIndepSets, Kernel.iIndepSets]
  have h_eq' : ∀ (s : Finset ι) (f : ι → Set Ω) (_H : ∀ i, i ∈ s → f i ∈ π i) i (_hi : i ∈ s),
      (fun ω ↦ ENNReal.toReal (condExpKernel μ m' ω (f i))) =ᵐ[μ] μ⟦f i | m'⟧ :=
    fun s f H i hi ↦ condExpKernel_ae_eq_condExp hm' (hπ i (f i) (H i hi))
  have h_eq : ∀ (s : Finset ι) (f : ι → Set Ω) (_H : ∀ i, i ∈ s → f i ∈ π i), ∀ᵐ ω ∂μ,
      ∀ i ∈ s, ENNReal.toReal (condExpKernel μ m' ω (f i)) = (μ⟦f i | m'⟧) ω := by
    intro s f H
    simp_rw [← Finset.mem_coe]
    rw [ae_ball_iff (Finset.countable_toSet s)]
    exact h_eq' s f H
  have h_inter_eq : ∀ (s : Finset ι) (f : ι → Set Ω) (_H : ∀ i, i ∈ s → f i ∈ π i),
      (fun ω ↦ ENNReal.toReal (condExpKernel μ m' ω (⋂ i ∈ s, f i)))
        =ᵐ[μ] μ⟦⋂ i ∈ s, f i | m'⟧ := by
    refine fun s f H ↦ condExpKernel_ae_eq_condExp hm' ?_
    exact MeasurableSet.biInter (Finset.countable_toSet _) (fun i hi ↦ hπ i _ (H i hi))
  refine ⟨fun h s f hf ↦ ?_, fun h s f hf ↦ ?_⟩ <;> specialize h s hf
  · have h' := ae_eq_of_ae_eq_trim h
    filter_upwards [h_eq s f hf, h_inter_eq s f hf, h'] with ω h_eq h_inter_eq h'
    rw [← h_inter_eq, h', ENNReal.toReal_prod, Finset.prod_apply]
    exact Finset.prod_congr rfl h_eq
  · refine ((stronglyMeasurable_condExpKernel ?_).ae_eq_trim_iff hm' ?_).mpr ?_
    · exact .biInter (Finset.countable_toSet _) (fun i hi ↦ hπ i _ (hf i hi))
    · refine Measurable.stronglyMeasurable ?_
      exact Finset.measurable_fun_prod s (fun i hi ↦ measurable_condExpKernel (hπ i _ (hf i hi)))
    filter_upwards [h_eq s f hf, h_inter_eq s f hf, h] with ω h_eq h_inter_eq h
    have h_ne_top : condExpKernel μ m' ω (⋂ i ∈ s, f i) ≠ ∞ :=
      (measure_ne_top (condExpKernel μ m' ω) _)
    have : (∏ i ∈ s, condExpKernel μ m' ω (f i)) ≠ ∞ :=
      ENNReal.prod_ne_top fun _ _ ↦ measure_ne_top (condExpKernel μ m' ω) _
    rw [← ENNReal.ofReal_toReal h_ne_top, h_inter_eq, h, Finset.prod_apply,
      ← ENNReal.ofReal_toReal this, ENNReal.toReal_prod]
    congr 1
    exact Finset.prod_congr rfl (fun i hi ↦ (h_eq i hi).symm)
/-
**ProbabilityTheory.condIndepSets_iff** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheo
ry`。
形式化陈述：condIndepSets_iff (s1 s2 : Set (Set Ω)) (hs1 : forall s in s1, MeasurableS
et s) (hs2 : forall s in s2, MeasurableSet s) (μ : Measure Ω) [IsFiniteMeasure μ
] : CondIndepSets m' hm' s1 s2 μ ↔ forall (t1 t2 : Set Ω) (_ : t1 in s1) (_ : t2
 in s2), (μ⟦t1 inter t2 | m'⟧) =ᵐ[μ] (μ⟦t1 | m'⟧) * (μ⟦t2 | m'⟧)
参数：s1 s2 : Set (Set Ω)；hs1 : forall s in s1, MeasurableSet s；hs2 : forall s in s
2, MeasurableSet s；μ : Measure Ω。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `ProbabilityTheory.condExpKernel_ae_eq_condExp`：condExpKernel_ae_eq_condE
xp (hm : m <= mΩ) {s : Set Ω} (hs : MeasurableSet s) : (fun ω => (condExpKernel 
μ m ω).real s) =ᵐ[μ] μ⟦s | m⟧
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `MeasureTheory.ae_eq_of_ae_eq_trim`：ae_eq_of_ae_eq_trim {E} {hm : m <= m0
} {f₁ f₂ : α -> E} (h12 : f₁ =ᵐ[μ.trim hm] f₂) : f₁ =ᵐ[μ] f₂
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Pi.mul_apply`：mul_apply (f g : forall i, M i) (i : ι) : (f * g) i = f i 
* g i
· 使用定理 `ENNReal.toReal_mul`：toReal_mul : (a * b).toReal = a.toReal * b.toReal
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `MeasureTheory.StronglyMeasurable.ae_eq_trim_iff`：ae_eq_trim_iff (hm : m 
<= m₀) (hf : StronglyMeasurable[m] f) (hg : StronglyMeasurable[m] g) : f =ᵐ[μ.tr
im hm] g ↔ f =ᵐ[μ] g
· 使用定理 `ENNReal.instMetrizableSpace`：TopologicalSpace.MetrizableSpace ENNReal
· 使用定理 `ProbabilityTheory.stronglyMeasurable_condExpKernel`：stronglyMeasurable_c
ondExpKernel {s : Set Ω} (hs : MeasurableSet s) : StronglyMeasurable[m] fun ω =>
 condExpKernel μ m ω s
· 使用定理 `Measurable.stronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {f : α → 
β} {mα : MeasurableSpace α} [inst : MeasurableSpace β]   [inst_1 : TopologicalSp
ace β] [Topological…
· 使用定理 `TopologicalSpace.MetrizableSpace.toPseudoMetrizableSpace`：∀ {X : Type u_
5} {t : TopologicalSpace X} [self : TopologicalSpace.MetrizableSpace X],   Topol
ogicalSpace.PseudoMetrizableSpace X
· 使用定理 `ENNReal.instSecondCountableTopology`：SecondCountableTopology ENNReal
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Measurable.fun_mul`：∀ {M : Type u_2} {α : Type u_3} [inst : MeasurableSp
ace M] [inst_1 : Mul M] {m : MeasurableSpace α} {f g : α → M}   [MeasurableMul₂ 
M], Meas…
· 使用定理 `ProbabilityTheory.measurable_condExpKernel`：measurable_condExpKernel {s 
: Set Ω} (hs : MeasurableSet s) : Measurable[m] fun ω => condExpKernel μ m ω s
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `ProbabilityTheory.IsFiniteKernel.isFiniteMeasure`：∀ {α : Type u_1} {β : 
Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheo
ry.Kernel α β}   [ProbabilityTheory.Is…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.instIsMarkovKernelCondExpKernel`：∀ {Ω : Type u_1} {m :
 MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [inst : StandardBorelSpace Ω]   {μ 
: MeasureTheory.Measure Ω} [inst_1 : Me…
· 使用定理 `ENNReal.ofReal_toReal`：ofReal_toReal {a : Real>=0∞} (h : a != ∞) : ENNRe
al.ofReal a.toReal = a
· 使用定理 `ENNReal.mul_ne_top`：mul_ne_top : a != ∞ -> b != ∞ -> a * b != ∞
-/
lemma condIndepSets_iff (s1 s2 : Set (Set Ω)) (hs1 : ∀ s ∈ s1, MeasurableSet s)
    (hs2 : ∀ s ∈ s2, MeasurableSet s) (μ : Measure Ω) [IsFiniteMeasure μ] :
    CondIndepSets m' hm' s1 s2 μ ↔ ∀ (t1 t2 : Set Ω) (_ : t1 ∈ s1) (_ : t2 ∈ s2),
      (μ⟦t1 ∩ t2 | m'⟧) =ᵐ[μ] (μ⟦t1 | m'⟧) * (μ⟦t2 | m'⟧) := by
  simp only [CondIndepSets, Kernel.IndepSets]
  have hs1_eq : ∀ s ∈ s1, (fun ω ↦ ENNReal.toReal (condExpKernel μ m' ω s)) =ᵐ[μ] μ⟦s | m'⟧ :=
    fun s hs ↦ condExpKernel_ae_eq_condExp hm' (hs1 s hs)
  have hs2_eq : ∀ s ∈ s2, (fun ω ↦ ENNReal.toReal (condExpKernel μ m' ω s)) =ᵐ[μ] μ⟦s | m'⟧ :=
    fun s hs ↦ condExpKernel_ae_eq_condExp hm' (hs2 s hs)
  have hs12_eq : ∀ s ∈ s1, ∀ t ∈ s2, (fun ω ↦ ENNReal.toReal (condExpKernel μ m' ω (s ∩ t)))
      =ᵐ[μ] μ⟦s ∩ t | m'⟧ :=
    fun s hs t ht ↦ condExpKernel_ae_eq_condExp hm' ((hs1 s hs).inter ((hs2 t ht)))
  refine ⟨fun h s t hs ht ↦ ?_, fun h s t hs ht ↦ ?_⟩ <;> specialize h s t hs ht
  · have h' := ae_eq_of_ae_eq_trim h
    filter_upwards [hs1_eq s hs, hs2_eq t ht, hs12_eq s hs t ht, h'] with ω hs_eq ht_eq hst_eq h'
    rw [← hst_eq, Pi.mul_apply, ← hs_eq, ← ht_eq, h', ENNReal.toReal_mul]
  · refine ((stronglyMeasurable_condExpKernel ((hs1 s hs).inter (hs2 t ht))).ae_eq_trim_iff hm'
      ((measurable_condExpKernel (hs1 s hs)).fun_mul
        (measurable_condExpKernel (hs2 t ht))).stronglyMeasurable).mpr ?_
    filter_upwards [hs1_eq s hs, hs2_eq t ht, hs12_eq s hs t ht, h] with ω hs_eq ht_eq hst_eq h
    have h_ne_top : condExpKernel μ m' ω (s ∩ t) ≠ ∞ := measure_ne_top (condExpKernel μ m' ω) _
    rw [← ENNReal.ofReal_toReal h_ne_top, hst_eq, h, Pi.mul_apply, ← hs_eq, ← ht_eq,
      ← ENNReal.toReal_mul, ENNReal.ofReal_toReal]
    exact ENNReal.mul_ne_top (measure_ne_top (condExpKernel μ m' ω) s)
      (measure_ne_top (condExpKernel μ m' ω) t)
/-
**ProbabilityTheory.iCondIndepSets_singleton_iff** 是 Mathlib 中的一个引理，位于命名空间 `Prob
abilityTheory`。
形式化陈述：iCondIndepSets_singleton_iff (s : ι -> Set Ω) (hπ : forall i, MeasurableSe
t (s i)) (μ : Measure Ω) [IsFiniteMeasure μ] : iCondIndepSets m' hm' (fun i => {
s i}) μ ↔ forall S : Finset ι, μ⟦⋂ i in S, s i | m'⟧ =ᵐ[μ] ∏ i in S, (μ⟦s i | m'
⟧)
参数：s : ι -> Set Ω；hπ : forall i, MeasurableSet (s i)；μ : Measure Ω。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.iCondIndepSets_iff`：iCondIndepSets_iff (π : ι -> Set (
Set Ω)) (hπ : forall i s (_hs : s in π i), MeasurableSet s) (μ : Measure Ω) [IsF
initeMeasure μ] : iCondInd…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
lemma iCondIndepSets_singleton_iff (s : ι → Set Ω) (hπ : ∀ i, MeasurableSet (s i))
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    iCondIndepSets m' hm' (fun i ↦ {s i}) μ ↔ ∀ S : Finset ι,
      μ⟦⋂ i ∈ S, s i | m'⟧ =ᵐ[μ] ∏ i ∈ S, (μ⟦s i | m'⟧) := by
  rw [iCondIndepSets_iff]
  · simp_all only [Set.mem_singleton_iff]
    constructor
    · intros
      simp [*]
    · grind
  · simpa
/-
**ProbabilityTheory.condIndepSets_singleton_iff** 是 Mathlib 中的一个定理，位于命名空间 `Proba
bilityTheory`。
形式化陈述：condIndepSets_singleton_iff {μ : Measure Ω} [IsFiniteMeasure μ] {s t : Set
 Ω} (hs : MeasurableSet s) (ht : MeasurableSet t) : CondIndepSets m' hm' {s} {t}
 μ ↔ (μ⟦s inter t | m'⟧) =ᵐ[μ] (μ⟦s | m'⟧) * (μ⟦t | m'⟧)
参数：hs : MeasurableSet s；ht : MeasurableSet t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.condIndepSets_iff`：condIndepSets_iff (s1 s2 : Set (Set
 Ω)) (hs1 : forall s in s1, MeasurableSet s) (hs2 : forall s in s2, MeasurableSe
t s) (μ : Measure Ω) [IsF…
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem condIndepSets_singleton_iff {μ : Measure Ω} [IsFiniteMeasure μ]
    {s t : Set Ω} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    CondIndepSets m' hm' {s} {t} μ ↔ (μ⟦s ∩ t | m'⟧) =ᵐ[μ] (μ⟦s | m'⟧) * (μ⟦t | m'⟧) := by
  rw [condIndepSets_iff _ _ _ _ ?_ ?_]
  · simp
  · intro s' hs'
    rw [Set.mem_singleton_iff] at hs'
    rwa [hs']
  · intro s' hs'
    rw [Set.mem_singleton_iff] at hs'
    rwa [hs']
/-
**ProbabilityTheory.iCondIndep_iff_iCondIndepSets** 是 Mathlib 中的一个引理，位于命名空间 `Pro
babilityTheory`。
形式化陈述：iCondIndep_iff_iCondIndepSets (m : ι -> MeasurableSpace Ω) (μ : @Measure Ω
 mΩ) [IsFiniteMeasure μ] : iCondIndep m' hm' m μ ↔ iCondIndepSets m' hm' (fun x 
=> {s | MeasurableSet[m x] s}) μ
参数：m : ι -> MeasurableSpace Ω；μ : @Measure Ω mΩ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma iCondIndep_iff_iCondIndepSets (m : ι → MeasurableSpace Ω)
    (μ : @Measure Ω mΩ) [IsFiniteMeasure μ] :
    iCondIndep m' hm' m μ ↔ iCondIndepSets m' hm' (fun x ↦ {s | MeasurableSet[m x] s}) μ := by
  simp only [iCondIndep, iCondIndepSets, Kernel.iIndep]
/-
**ProbabilityTheory.iCondIndep_iff** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`
。
形式化陈述：iCondIndep_iff (m : ι -> MeasurableSpace Ω) (hm : forall i, m i <= mΩ) (μ 
: @Measure Ω mΩ) [IsFiniteMeasure μ] : iCondIndep m' hm' m μ ↔ forall (s : Finse
t ι) {f : ι -> Set Ω} (_H : forall i, i in s -> MeasurableSet[m i] (f i)), μ⟦⋂ i
 in s, f i | m'⟧ =ᵐ[μ] ∏ i in s, (μ⟦f i | m'⟧)
参数：m : ι -> MeasurableSpace Ω；hm : forall i, m i <= mΩ；μ : @Measure Ω mΩ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.iCondIndep_iff_iCondIndepSets`：iCondIndep_iff_iCondInd
epSets (m : ι -> MeasurableSpace Ω) (μ : @Measure Ω mΩ) [IsFiniteMeasure μ] : iC
ondIndep m' hm' m μ ↔ iCondIndepSets …
· 使用引理 `ProbabilityTheory.iCondIndepSets_iff`：iCondIndepSets_iff (π : ι -> Set (
Set Ω)) (hπ : forall i s (_hs : s in π i), MeasurableSet s) (μ : Measure Ω) [IsF
initeMeasure μ] : iCondInd…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma iCondIndep_iff (m : ι → MeasurableSpace Ω) (hm : ∀ i, m i ≤ mΩ)
    (μ : @Measure Ω mΩ) [IsFiniteMeasure μ] :
    iCondIndep m' hm' m μ
      ↔ ∀ (s : Finset ι) {f : ι → Set Ω} (_H : ∀ i, i ∈ s → MeasurableSet[m i] (f i)),
      μ⟦⋂ i ∈ s, f i | m'⟧ =ᵐ[μ] ∏ i ∈ s, (μ⟦f i | m'⟧) := by
  rw [iCondIndep_iff_iCondIndepSets, iCondIndepSets_iff]
  · rfl
  · exact hm

end

section CondIndep

/-
**ProbabilityTheory.condIndep_iff_condIndepSets** 是 Mathlib 中的一个引理，位于命名空间 `Proba
bilityTheory`。
形式化陈述：condIndep_iff_condIndepSets (m' m₁ m₂ : MeasurableSpace Ω) {mΩ : Measurabl
eSpace Ω} [StandardBorelSpace Ω] (hm' : m' <= mΩ) (μ : Measure Ω) [IsFiniteMeasu
re μ] : CondIndep m' m₁ m₂ hm' μ ↔ CondIndepSets m' hm' {s | MeasurableSet[m₁] s
} {s | MeasurableSet[m₂] s} μ
参数：m' m₁ m₂ : MeasurableSpace Ω；hm' : m' <= mΩ；μ : Measure Ω。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma condIndep_iff_condIndepSets (m' m₁ m₂ : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω}
    [StandardBorelSpace Ω] (hm' : m' ≤ mΩ) (μ : Measure Ω) [IsFiniteMeasure μ] :
    CondIndep m' m₁ m₂ hm' μ
      ↔ CondIndepSets m' hm' {s | MeasurableSet[m₁] s} {s | MeasurableSet[m₂] s} μ := by
  simp only [CondIndep, CondIndepSets, Kernel.Indep]
/-
**ProbabilityTheory.condIndep_iff** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：condIndep_iff (m' m₁ m₂ : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} [Sta
ndardBorelSpace Ω] (hm' : m' <= mΩ) (hm₁ : m₁ <= mΩ) (hm₂ : m₂ <= mΩ) (μ : Measu
re Ω) [IsFiniteMeasure μ] : CondIndep m' m₁ m₂ hm' μ ↔ forall t1 t2, MeasurableS
et[m₁] t1 -> MeasurableSet[m₂] t2 -> (μ⟦t1 inter t2 | m'⟧) =ᵐ[μ] (μ⟦t1 | m'⟧) * 
(μ⟦t2 | m'⟧)
参数：m' m₁ m₂ : MeasurableSpace Ω；hm' : m' <= mΩ；hm₁ : m₁ <= mΩ；hm₂ : m₂ <= mΩ；μ :
 Measure Ω。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.condIndep_iff_condIndepSets`：condIndep_iff_condIndepSe
ts (m' m₁ m₂ : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω
] (hm' : m' <= mΩ) (μ : Measure Ω) …
· 使用引理 `ProbabilityTheory.condIndepSets_iff`：condIndepSets_iff (s1 s2 : Set (Set
 Ω)) (hs1 : forall s in s1, MeasurableSet s) (hs2 : forall s in s2, MeasurableSe
t s) (μ : Measure Ω) [IsF…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma condIndep_iff (m' m₁ m₂ : MeasurableSpace Ω)
    {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    (hm' : m' ≤ mΩ) (hm₁ : m₁ ≤ mΩ) (hm₂ : m₂ ≤ mΩ) (μ : Measure Ω) [IsFiniteMeasure μ] :
    CondIndep m' m₁ m₂ hm' μ
      ↔ ∀ t1 t2, MeasurableSet[m₁] t1 → MeasurableSet[m₂] t2
        → (μ⟦t1 ∩ t2 | m'⟧) =ᵐ[μ] (μ⟦t1 | m'⟧) * (μ⟦t2 | m'⟧) := by
  rw [condIndep_iff_condIndepSets, condIndepSets_iff]
  · rfl
  · exact hm₁
  · exact hm₂

end CondIndep

variable (m' : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
  (hm' : m' ≤ mΩ)

/-
**ProbabilityTheory.iCondIndepSet_iff_iCondIndep** 是 Mathlib 中的一个引理，位于命名空间 `Prob
abilityTheory`。
形式化陈述：iCondIndepSet_iff_iCondIndep (s : ι -> Set Ω) (μ : Measure Ω) [IsFiniteMea
sure μ] : iCondIndepSet m' hm' s μ ↔ iCondIndep m' hm' (fun i => generateFrom {s
 i}) μ
参数：s : ι -> Set Ω；μ : Measure Ω。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma iCondIndepSet_iff_iCondIndep (s : ι → Set Ω) (μ : Measure Ω) [IsFiniteMeasure μ] :
    iCondIndepSet m' hm' s μ ↔ iCondIndep m' hm' (fun i ↦ generateFrom {s i}) μ := by
  simp only [iCondIndepSet, iCondIndep, Kernel.iIndepSet]
/-
**ProbabilityTheory.iCondIndepSet_iff_iCondIndepSets_singleton** 是 Mathlib 中的一个定
理，位于命名空间 `ProbabilityTheory`。
形式化陈述：iCondIndepSet_iff_iCondIndepSets_singleton (s : ι -> Set Ω) (hs : forall i
, MeasurableSet (s i)) (μ : Measure Ω) [IsFiniteMeasure μ] : iCondIndepSet m' hm
' s μ ↔ iCondIndepSets m' hm' (fun i => {s i}) μ
参数：s : ι -> Set Ω；hs : forall i, MeasurableSet (s i)；μ : Measure Ω。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepSet_iff_iIndepSets_singleton`：iIndepSet_i
ff_iIndepSets_singleton {_mΩ : MeasurableSpace Ω} {κ : Kernel α Ω} {μ : Measure 
α} {f : ι -> Set Ω} (hf : forall i, MeasurableSet…
-/
theorem iCondIndepSet_iff_iCondIndepSets_singleton (s : ι → Set Ω) (hs : ∀ i, MeasurableSet (s i))
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    iCondIndepSet m' hm' s μ ↔ iCondIndepSets m' hm' (fun i ↦ {s i}) μ :=
  Kernel.iIndepSet_iff_iIndepSets_singleton hs
/-
**ProbabilityTheory.iCondIndepSet_iff** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheo
ry`。
形式化陈述：iCondIndepSet_iff (s : ι -> Set Ω) (hs : forall i, MeasurableSet (s i)) (μ
 : Measure Ω) [IsFiniteMeasure μ] : iCondIndepSet m' hm' s μ ↔ forall S : Finset
 ι, μ⟦⋂ i in S, s i | m'⟧ =ᵐ[μ] ∏ i in S, μ⟦s i | m'⟧
参数：s : ι -> Set Ω；hs : forall i, MeasurableSet (s i)；μ : Measure Ω。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.iCondIndepSet_iff_iCondIndepSets_singleton`：iCondIndep
Set_iff_iCondIndepSets_singleton (s : ι -> Set Ω) (hs : forall i, MeasurableSet 
(s i)) (μ : Measure Ω) [IsFiniteMeasure μ] : iCond…
· 使用引理 `ProbabilityTheory.iCondIndepSets_singleton_iff`：iCondIndepSets_singleton
_iff (s : ι -> Set Ω) (hπ : forall i, MeasurableSet (s i)) (μ : Measure Ω) [IsFi
niteMeasure μ] : iCondIndepSets m' h…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma iCondIndepSet_iff (s : ι → Set Ω) (hs : ∀ i, MeasurableSet (s i))
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    iCondIndepSet m' hm' s μ ↔
      ∀ S : Finset ι, μ⟦⋂ i ∈ S, s i | m'⟧ =ᵐ[μ] ∏ i ∈ S, μ⟦s i | m'⟧ := by
  rw [iCondIndepSet_iff_iCondIndepSets_singleton _ _ _ hs, iCondIndepSets_singleton_iff _ _ _ hs]
/-
**ProbabilityTheory.condIndepSet_iff_condIndep** 是 Mathlib 中的一个引理，位于命名空间 `Probab
ilityTheory`。
形式化陈述：condIndepSet_iff_condIndep (s t : Set Ω) (μ : Measure Ω) [IsFiniteMeasure 
μ] : CondIndepSet m' hm' s t μ ↔ CondIndep m' (generateFrom {s}) (generateFrom {
t}) hm' μ
参数：s t : Set Ω；μ : Measure Ω。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma condIndepSet_iff_condIndep (s t : Set Ω) (μ : Measure Ω) [IsFiniteMeasure μ] :
    CondIndepSet m' hm' s t μ ↔ CondIndep m' (generateFrom {s}) (generateFrom {t}) hm' μ := by
  simp only [CondIndepSet, CondIndep, Kernel.IndepSet]
/-
**ProbabilityTheory.condIndepSet_iff_condIndepSets_singleton** 是 Mathlib 中的一个定理，
位于命名空间 `ProbabilityTheory`。
形式化陈述：condIndepSet_iff_condIndepSets_singleton {s t : Set Ω} (hs_meas : Measurab
leSet s) (ht_meas : MeasurableSet t) (μ : Measure Ω) [IsFiniteMeasure μ] : CondI
ndepSet m' hm' s t μ ↔ CondIndepSets m' hm' {s} {t} μ
参数：hs_meas : MeasurableSet s；ht_meas : MeasurableSet t；μ : Measure Ω。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.indepSet_iff_indepSets_singleton`：indepSet_iff_
indepSets_singleton {m0 : MeasurableSpace Ω} (hs_meas : MeasurableSet s) (ht_mea
s : MeasurableSet t) (κ : Kernel α Ω) (μ : Meas…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.instIsMarkovKernelCondExpKernel`：∀ {Ω : Type u_1} {m :
 MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [inst : StandardBorelSpace Ω]   {μ 
: MeasureTheory.Measure Ω} [inst_1 : Me…
-/
theorem condIndepSet_iff_condIndepSets_singleton {s t : Set Ω} (hs_meas : MeasurableSet s)
    (ht_meas : MeasurableSet t) (μ : Measure Ω) [IsFiniteMeasure μ] :
    CondIndepSet m' hm' s t μ ↔ CondIndepSets m' hm' {s} {t} μ :=
  Kernel.indepSet_iff_indepSets_singleton hs_meas ht_meas _ _
/-
**ProbabilityTheory.condIndepSet_iff** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheor
y`。
形式化陈述：condIndepSet_iff (s t : Set Ω) (hs : MeasurableSet s) (ht : MeasurableSet 
t) (μ : Measure Ω) [IsFiniteMeasure μ] : CondIndepSet m' hm' s t μ ↔ (μ⟦s inter 
t | m'⟧) =ᵐ[μ] (μ⟦s | m'⟧) * (μ⟦t | m'⟧)
参数：s t : Set Ω；hs : MeasurableSet s；ht : MeasurableSet t；μ : Measure Ω。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.condIndepSet_iff_condIndepSets_singleton`：condIndepSet
_iff_condIndepSets_singleton {s t : Set Ω} (hs_meas : MeasurableSet s) (ht_meas 
: MeasurableSet t) (μ : Measure Ω) [IsFiniteMeas…
· 使用定理 `ProbabilityTheory.condIndepSets_singleton_iff`：condIndepSets_singleton_i
ff {μ : Measure Ω} [IsFiniteMeasure μ] {s t : Set Ω} (hs : MeasurableSet s) (ht 
: MeasurableSet t) : CondIndepSets …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma condIndepSet_iff (s t : Set Ω) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    CondIndepSet m' hm' s t μ ↔ (μ⟦s ∩ t | m'⟧) =ᵐ[μ] (μ⟦s | m'⟧) * (μ⟦t | m'⟧) := by
  rw [condIndepSet_iff_condIndepSets_singleton _ _ hs ht μ, condIndepSets_singleton_iff _ _ hs ht]
/-
**ProbabilityTheory.iCondIndepFun_iff_iCondIndep** 是 Mathlib 中的一个引理，位于命名空间 `Prob
abilityTheory`。
形式化陈述：iCondIndepFun_iff_iCondIndep {β : ι -> Type*} (m : forall x : ι, Measurabl
eSpace (β x)) (f : forall x : ι, Ω -> β x) (μ : Measure Ω) [IsFiniteMeasure μ] :
 iCondIndepFun m' hm' f μ ↔ iCondIndep m' hm' (fun x => MeasurableSpace.comap (f
 x) (m x)) μ
参数：m : forall x : ι, MeasurableSpace (β x)；f : forall x : ι, Ω -> β x；μ : Measur
e Ω。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma iCondIndepFun_iff_iCondIndep {β : ι → Type*}
    (m : ∀ x : ι, MeasurableSpace (β x)) (f : ∀ x : ι, Ω → β x)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    iCondIndepFun m' hm' f μ
      ↔ iCondIndep m' hm' (fun x ↦ MeasurableSpace.comap (f x) (m x)) μ := by
  simp only [iCondIndepFun, iCondIndep, Kernel.iIndepFun]
/-
**ProbabilityTheory.iCondIndepFun_iff** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheo
ry`。
形式化陈述：iCondIndepFun_iff {β : ι -> Type*} (m : forall x : ι, MeasurableSpace (β x
)) (f : forall x : ι, Ω -> β x) (hf : forall i, Measurable (f i)) (μ : Measure Ω
) [IsFiniteMeasure μ] : iCondIndepFun m' hm' f μ ↔ forall (s : Finset ι) {g : ι 
-> Set Ω} (_H : forall i, i in s -> MeasurableSet[(m i).comap (f i)] (g i)), μ⟦⋂
 i in s, g i | m'⟧ =ᵐ[μ] ∏ i in s, (μ⟦g i | m'⟧)
参数：m : forall x : ι, MeasurableSpace (β x)；f : forall x : ι, Ω -> β x；hf : foral
l i, Measurable (f i)；μ : Measure Ω。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.iCondIndep_iff`：iCondIndep_iff (m : ι -> MeasurableSpa
ce Ω) (hm : forall i, m i <= mΩ) (μ : @Measure Ω mΩ) [IsFiniteMeasure μ] : iCond
Indep m' hm' m μ ↔ for…
· 使用定理 `Measurable.comap_le`：∀ {α : Type u_1} {β : Type u_2} {m₁ : MeasurableSpa
ce α} {m₂ : MeasurableSpace β} {f : α → β},   Measurable f → MeasurableSpace.com
ap f m₂ ≤…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma iCondIndepFun_iff {β : ι → Type*}
    (m : ∀ x : ι, MeasurableSpace (β x)) (f : ∀ x : ι, Ω → β x) (hf : ∀ i, Measurable (f i))
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    iCondIndepFun m' hm' f μ
      ↔ ∀ (s : Finset ι) {g : ι → Set Ω} (_H : ∀ i, i ∈ s → MeasurableSet[(m i).comap (f i)] (g i)),
      μ⟦⋂ i ∈ s, g i | m'⟧ =ᵐ[μ] ∏ i ∈ s, (μ⟦g i | m'⟧) := by
  simp only [iCondIndepFun_iff_iCondIndep]
  rw [iCondIndep_iff]
  exact fun i ↦ (hf i).comap_le
/-
**ProbabilityTheory.condIndepFun_iff_condIndep** 是 Mathlib 中的一个引理，位于命名空间 `Probab
ilityTheory`。
形式化陈述：condIndepFun_iff_condIndep {β γ : Type*} [mβ : MeasurableSpace β] [mγ : Me
asurableSpace γ] (f : Ω -> β) (g : Ω -> γ) (μ : Measure Ω) [IsFiniteMeasure μ] :
 CondIndepFun m' hm' f g μ ↔ CondIndep m' (MeasurableSpace.comap f mβ) (Measurab
leSpace.comap g mγ) hm' μ
参数：f : Ω -> β；g : Ω -> γ；μ : Measure Ω。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma condIndepFun_iff_condIndep {β γ : Type*} [mβ : MeasurableSpace β]
    [mγ : MeasurableSpace γ] (f : Ω → β) (g : Ω → γ) (μ : Measure Ω) [IsFiniteMeasure μ] :
    CondIndepFun m' hm' f g μ
      ↔ CondIndep m' (MeasurableSpace.comap f mβ) (MeasurableSpace.comap g mγ) hm' μ := by
  simp only [CondIndepFun, CondIndep, Kernel.IndepFun]
/-
**ProbabilityTheory.condIndepFun_iff** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheor
y`。
形式化陈述：condIndepFun_iff {β γ : Type*} [mβ : MeasurableSpace β] [mγ : MeasurableSp
ace γ] (f : Ω -> β) (g : Ω -> γ) (hf : Measurable f) (hg : Measurable g) (μ : Me
asure Ω) [IsFiniteMeasure μ] : CondIndepFun m' hm' f g μ ↔ forall t1 t2, Measura
bleSet[MeasurableSpace.comap f mβ] t1 -> MeasurableSet[MeasurableSpace.comap g m
γ] t2 -> (μ⟦t1 inter t2 | m'⟧) =ᵐ[μ] (μ⟦t1 | m'⟧) * (μ⟦t2 | m'⟧)
参数：f : Ω -> β；g : Ω -> γ；hf : Measurable f；hg : Measurable g；μ : Measure Ω。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.condIndepFun_iff_condIndep`：condIndepFun_iff_condIndep
 {β γ : Type*} [mβ : MeasurableSpace β] [mγ : MeasurableSpace γ] (f : Ω -> β) (g
 : Ω -> γ) (μ : Measure Ω) [IsFini…
· 使用引理 `ProbabilityTheory.condIndep_iff`：condIndep_iff (m' m₁ m₂ : MeasurableSpa
ce Ω) {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω] (hm' : m' <= mΩ) (hm₁ : m₁
 <= mΩ) (hm₂ : m₂ <= …
· 使用定理 `Measurable.comap_le`：∀ {α : Type u_1} {β : Type u_2} {m₁ : MeasurableSpa
ce α} {m₂ : MeasurableSpace β} {f : α → β},   Measurable f → MeasurableSpace.com
ap f m₂ ≤…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma condIndepFun_iff {β γ : Type*} [mβ : MeasurableSpace β] [mγ : MeasurableSpace γ]
    (f : Ω → β) (g : Ω → γ) (hf : Measurable f) (hg : Measurable g)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    CondIndepFun m' hm' f g μ ↔ ∀ t1 t2, MeasurableSet[MeasurableSpace.comap f mβ] t1
      → MeasurableSet[MeasurableSpace.comap g mγ] t2
        → (μ⟦t1 ∩ t2 | m'⟧) =ᵐ[μ] (μ⟦t1 | m'⟧) * (μ⟦t2 | m'⟧) := by
  rw [condIndepFun_iff_condIndep, condIndep_iff _ _ _ _ hf.comap_le hg.comap_le]

end DefinitionLemmas

section CondIndepSets

variable {m' : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
  {hm' : m' ≤ mΩ} {μ : Measure Ω} [IsFiniteMeasure μ]

@[symm]
/-
**ProbabilityTheory.CondIndepSets.symm** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityThe
ory.CondIndepSets`。
形式化陈述：∀ {Ω : Type u_1} {m' mΩ : MeasurableSpace Ω} [inst : StandardBorelSpace Ω]
 {hm' : m' ≤ mΩ} {μ : MeasureTheory.Measure Ω}   [inst_1 : MeasureTheory.IsFinit
eMeasure μ] {s₁ s₂ : Set (Set Ω)},   ProbabilityTheory.CondIndepSets m' hm' s₁ s
₂ μ → ProbabilityTheory.CondIndepSets m' hm' s₂ s₁ μ
参数：Set Ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IndepSets.symm`：∀ {α : Type u_1} {Ω : Type u_2}
 {_mα : MeasurableSpace α} {_mΩ : MeasurableSpace Ω} {κ : ProbabilityTheory.Kern
el α Ω}   {μ : MeasureTheory.…
-/
theorem CondIndepSets.symm {s₁ s₂ : Set (Set Ω)}
    (h : CondIndepSets m' hm' s₁ s₂ μ) : CondIndepSets m' hm' s₂ s₁ μ :=
  Kernel.IndepSets.symm h
/-
**ProbabilityTheory.condIndepSets_of_condIndepSets_of_le_left** 是 Mathlib 中的一个定理
，位于命名空间 `ProbabilityTheory`。
形式化陈述：condIndepSets_of_condIndepSets_of_le_left {s₁ s₂ s₃ : Set (Set Ω)} (h_inde
p : CondIndepSets m' hm' s₁ s₂ μ) (h31 : s₃ subseteq s₁) : CondIndepSets m' hm' 
s₃ s₂ μ
参数：Set Ω；h_indep : CondIndepSets m' hm' s₁ s₂ μ；h31 : s₃ subseteq s₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.indepSets_of_indepSets_of_le_left`：indepSets_of
_indepSets_of_le_left {s₁ s₂ s₃ : Set (Set Ω)} {_mΩ : MeasurableSpace Ω} {κ : Ke
rnel α Ω} {μ : Measure α} (h_indep : IndepSets s…
-/
theorem condIndepSets_of_condIndepSets_of_le_left {s₁ s₂ s₃ : Set (Set Ω)}
    (h_indep : CondIndepSets m' hm' s₁ s₂ μ) (h31 : s₃ ⊆ s₁) :
    CondIndepSets m' hm' s₃ s₂ μ :=
  Kernel.indepSets_of_indepSets_of_le_left h_indep h31
/-
**ProbabilityTheory.condIndepSets_of_condIndepSets_of_le_right** 是 Mathlib 中的一个定
理，位于命名空间 `ProbabilityTheory`。
形式化陈述：condIndepSets_of_condIndepSets_of_le_right {s₁ s₂ s₃ : Set (Set Ω)} (h_ind
ep : CondIndepSets m' hm' s₁ s₂ μ) (h32 : s₃ subseteq s₂) : CondIndepSets m' hm'
 s₁ s₃ μ
参数：Set Ω；h_indep : CondIndepSets m' hm' s₁ s₂ μ；h32 : s₃ subseteq s₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.indepSets_of_indepSets_of_le_right`：indepSets_o
f_indepSets_of_le_right {s₁ s₂ s₃ : Set (Set Ω)} {_mΩ : MeasurableSpace Ω} {κ : 
Kernel α Ω} {μ : Measure α} (h_indep : IndepSets …
-/
theorem condIndepSets_of_condIndepSets_of_le_right {s₁ s₂ s₃ : Set (Set Ω)}
    (h_indep : CondIndepSets m' hm' s₁ s₂ μ) (h32 : s₃ ⊆ s₂) :
    CondIndepSets m' hm' s₁ s₃ μ :=
  Kernel.indepSets_of_indepSets_of_le_right h_indep h32
/-
**ProbabilityTheory.CondIndepSets.union** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTh
eory.CondIndepSets`。
形式化陈述：∀ {Ω : Type u_1} {m' mΩ : MeasurableSpace Ω} [inst : StandardBorelSpace Ω]
 {hm' : m' ≤ mΩ} {μ : MeasureTheory.Measure Ω}   [inst_1 : MeasureTheory.IsFinit
eMeasure μ] {s₁ s₂ s' : Set (Set Ω)},   ProbabilityTheory.CondIndepSets m' hm' s
₁ s' μ →     ProbabilityTheory.CondIndepSets m' hm' s₂ s' μ → ProbabilityTheory.
CondIndepSets m' hm' (s₁ ∪ s₂) s' μ
参数：Set Ω；s₁ ∪ s₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IndepSets.union`：∀ {α : Type u_1} {Ω : Type u_2
} {_mα : MeasurableSpace α} {s₁ s₂ s' : Set (Set Ω)} {_mΩ : MeasurableSpace Ω}  
 {κ : ProbabilityTheory.Kernel…
-/
theorem CondIndepSets.union {s₁ s₂ s' : Set (Set Ω)}
    (h₁ : CondIndepSets m' hm' s₁ s' μ) (h₂ : CondIndepSets m' hm' s₂ s' μ) :
    CondIndepSets m' hm' (s₁ ∪ s₂) s' μ :=
  Kernel.IndepSets.union h₁ h₂

@[simp]
/-
**ProbabilityTheory.CondIndepSets.union_iff** 是 Mathlib 中的一个定理，位于命名空间 `Probabili
tyTheory.CondIndepSets`。
形式化陈述：∀ {Ω : Type u_1} {m' mΩ : MeasurableSpace Ω} [inst : StandardBorelSpace Ω]
 {hm' : m' ≤ mΩ} {μ : MeasureTheory.Measure Ω}   [inst_1 : MeasureTheory.IsFinit
eMeasure μ] {s₁ s₂ s' : Set (Set Ω)},   ProbabilityTheory.CondIndepSets m' hm' (
s₁ ∪ s₂) s' μ ↔     ProbabilityTheory.CondIndepSets m' hm' s₁ s' μ ∧ Probability
Theory.CondIndepSets m' hm' s₂ s' μ
参数：Set Ω；s₁ ∪ s₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IndepSets.union_iff`：∀ {α : Type u_1} {Ω : Type
 u_2} {_mα : MeasurableSpace α} {s₁ s₂ s' : Set (Set Ω)} {_mΩ : MeasurableSpace 
Ω}   {κ : ProbabilityTheory.Kernel…
-/
theorem CondIndepSets.union_iff {s₁ s₂ s' : Set (Set Ω)} :
    CondIndepSets m' hm' (s₁ ∪ s₂) s' μ
      ↔ CondIndepSets m' hm' s₁ s' μ ∧ CondIndepSets m' hm' s₂ s' μ :=
  Kernel.IndepSets.union_iff
/-
**ProbabilityTheory.CondIndepSets.iUnion** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityT
heory.CondIndepSets`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {m' mΩ : MeasurableSpace Ω} [inst : Standa
rdBorelSpace Ω] {hm' : m' ≤ mΩ}   {μ : MeasureTheory.Measure Ω} [inst_1 : Measur
eTheory.IsFiniteMeasure μ] {s : ι → Set (Set Ω)} {s' : Set (Set Ω)},   (∀ (n : ι
), ProbabilityTheory.CondIndepSets m' hm' (s n) s' μ) →     ProbabilityTheory.Co
ndIndepSets m' hm' (⋃ n, s n) s' μ
参数：Set Ω；Set Ω；∀ (n : ι), ProbabilityTheory.CondIndepSets m' hm' (s n) s' μ；⋃ n,
 s n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IndepSets.iUnion`：∀ {α : Type u_1} {Ω : Type u_
2} {ι : Type u_3} {_mα : MeasurableSpace α} {s : ι → Set (Set Ω)} {s' : Set (Set
 Ω)}   {_mΩ : MeasurableSpace Ω…
-/
theorem CondIndepSets.iUnion {s : ι → Set (Set Ω)} {s' : Set (Set Ω)}
    (hyp : ∀ n, CondIndepSets m' hm' (s n) s' μ) :
    CondIndepSets m' hm' (⋃ n, s n) s' μ :=
  Kernel.IndepSets.iUnion hyp
/-
**ProbabilityTheory.CondIndepSets.biUnion** 是 Mathlib 中的一个定理，位于命名空间 `Probability
Theory.CondIndepSets`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {m' mΩ : MeasurableSpace Ω} [inst : Standa
rdBorelSpace Ω] {hm' : m' ≤ mΩ}   {μ : MeasureTheory.Measure Ω} [inst_1 : Measur
eTheory.IsFiniteMeasure μ] {s : ι → Set (Set Ω)} {s' : Set (Set Ω)}   {u : Set ι
},   (∀ n ∈ u, ProbabilityTheory.CondIndepSets m' hm' (s n) s' μ) →     Probabil
ityTheory.CondIndepSets m' hm' (⋃ n ∈ u, s n) s' μ
参数：Set Ω；Set Ω；∀ n ∈ u, ProbabilityTheory.CondIndepSets m' hm' (s n) s' μ；⋃ n ∈ 
u, s n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IndepSets.biUnion`：∀ {α : Type u_1} {Ω : Type u
_2} {ι : Type u_3} {_mα : MeasurableSpace α} {s : ι → Set (Set Ω)} {s' : Set (Se
t Ω)}   {_mΩ : MeasurableSpace Ω…
-/
theorem CondIndepSets.biUnion {s : ι → Set (Set Ω)} {s' : Set (Set Ω)}
    {u : Set ι} (hyp : ∀ n ∈ u, CondIndepSets m' hm' (s n) s' μ) :
    CondIndepSets m' hm' (⋃ n ∈ u, s n) s' μ :=
  Kernel.IndepSets.biUnion hyp
/-
**ProbabilityTheory.CondIndepSets.inter** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTh
eory.CondIndepSets`。
形式化陈述：∀ {Ω : Type u_1} {m' mΩ : MeasurableSpace Ω} [inst : StandardBorelSpace Ω]
 {hm' : m' ≤ mΩ} {μ : MeasureTheory.Measure Ω}   [inst_1 : MeasureTheory.IsFinit
eMeasure μ] {s₁ s' : Set (Set Ω)} (s₂ : Set (Set Ω)),   ProbabilityTheory.CondIn
depSets m' hm' s₁ s' μ → ProbabilityTheory.CondIndepSets m' hm' (s₁ ∩ s₂) s' μ
参数：Set Ω；s₂ : Set (Set Ω)；s₁ ∩ s₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IndepSets.inter`：∀ {α : Type u_1} {Ω : Type u_2
} {_mα : MeasurableSpace α} {s₁ s' : Set (Set Ω)} (s₂ : Set (Set Ω))   {_mΩ : Me
asurableSpace Ω} {κ : Probabil…
-/
theorem CondIndepSets.inter {s₁ s' : Set (Set Ω)} (s₂ : Set (Set Ω))
    (h₁ : CondIndepSets m' hm' s₁ s' μ) :
    CondIndepSets m' hm' (s₁ ∩ s₂) s' μ :=
  Kernel.IndepSets.inter s₂ h₁
/-
**ProbabilityTheory.CondIndepSets.iInter** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityT
heory.CondIndepSets`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {m' mΩ : MeasurableSpace Ω} [inst : Standa
rdBorelSpace Ω] {hm' : m' ≤ mΩ}   {μ : MeasureTheory.Measure Ω} [inst_1 : Measur
eTheory.IsFiniteMeasure μ] {s : ι → Set (Set Ω)} {s' : Set (Set Ω)},   (∃ n, Pro
babilityTheory.CondIndepSets m' hm' (s n) s' μ) → ProbabilityTheory.CondIndepSet
s m' hm' (⋂ n, s n) s' μ
参数：Set Ω；Set Ω；∃ n, ProbabilityTheory.CondIndepSets m' hm' (s n) s' μ；⋂ n, s n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IndepSets.iInter`：∀ {α : Type u_1} {Ω : Type u_
2} {ι : Type u_3} {_mα : MeasurableSpace α} {s : ι → Set (Set Ω)} {s' : Set (Set
 Ω)}   {_mΩ : MeasurableSpace Ω…
-/
theorem CondIndepSets.iInter {s : ι → Set (Set Ω)} {s' : Set (Set Ω)}
    (h : ∃ n, CondIndepSets m' hm' (s n) s' μ) :
    CondIndepSets m' hm' (⋂ n, s n) s' μ :=
  Kernel.IndepSets.iInter h
/-
**ProbabilityTheory.CondIndepSets.bInter** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityT
heory.CondIndepSets`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {m' mΩ : MeasurableSpace Ω} [inst : Standa
rdBorelSpace Ω] {hm' : m' ≤ mΩ}   {μ : MeasureTheory.Measure Ω} [inst_1 : Measur
eTheory.IsFiniteMeasure μ] {s : ι → Set (Set Ω)} {s' : Set (Set Ω)}   {u : Set ι
},   (∃ n ∈ u, ProbabilityTheory.CondIndepSets m' hm' (s n) s' μ) →     Probabil
ityTheory.CondIndepSets m' hm' (⋂ n ∈ u, s n) s' μ
参数：Set Ω；Set Ω；∃ n ∈ u, ProbabilityTheory.CondIndepSets m' hm' (s n) s' μ；⋂ n ∈ 
u, s n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IndepSets.bInter`：∀ {α : Type u_1} {Ω : Type u_
2} {ι : Type u_3} {_mα : MeasurableSpace α} {s : ι → Set (Set Ω)} {s' : Set (Set
 Ω)}   {_mΩ : MeasurableSpace Ω…
-/
theorem CondIndepSets.bInter {s : ι → Set (Set Ω)} {s' : Set (Set Ω)}
    {u : Set ι} (h : ∃ n ∈ u, CondIndepSets m' hm' (s n) s' μ) :
    CondIndepSets m' hm' (⋂ n ∈ u, s n) s' μ :=
  Kernel.IndepSets.bInter h

end CondIndepSets

section CondIndepSet

variable {m' : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
  {hm' : m' ≤ mΩ} {μ : Measure Ω} [IsFiniteMeasure μ]

/-
**ProbabilityTheory.condIndepSet_empty_right** 是 Mathlib 中的一个定理，位于命名空间 `Probabil
ityTheory`。
形式化陈述：condIndepSet_empty_right (s : Set Ω) : CondIndepSet m' hm' s ∅ μ
参数：s : Set Ω。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.indepSet_empty_right`：indepSet_empty_right {_mΩ
 : MeasurableSpace Ω} {κ : Kernel α Ω} {μ : Measure α} [IsZeroOrMarkovKernel κ] 
(s : Set Ω) : IndepSet s ∅ κ μ
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.instIsMarkovKernelCondExpKernel`：∀ {Ω : Type u_1} {m :
 MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [inst : StandardBorelSpace Ω]   {μ 
: MeasureTheory.Measure Ω} [inst_1 : Me…
-/
theorem condIndepSet_empty_right (s : Set Ω) : CondIndepSet m' hm' s ∅ μ :=
  Kernel.indepSet_empty_right s
/-
**ProbabilityTheory.condIndepSet_empty_left** 是 Mathlib 中的一个定理，位于命名空间 `Probabili
tyTheory`。
形式化陈述：condIndepSet_empty_left (s : Set Ω) : CondIndepSet m' hm' ∅ s μ
参数：s : Set Ω。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.indepSet_empty_left`：indepSet_empty_left {_mΩ :
 MeasurableSpace Ω} {κ : Kernel α Ω} {μ : Measure α} [IsZeroOrMarkovKernel κ] (s
 : Set Ω) : IndepSet ∅ s κ μ
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.instIsMarkovKernelCondExpKernel`：∀ {Ω : Type u_1} {m :
 MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [inst : StandardBorelSpace Ω]   {μ 
: MeasureTheory.Measure Ω} [inst_1 : Me…
-/
theorem condIndepSet_empty_left (s : Set Ω) : CondIndepSet m' hm' ∅ s μ :=
  Kernel.indepSet_empty_left s

end CondIndepSet

section CondIndep

@[symm]
/-
**ProbabilityTheory.CondIndep.symm** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory.
CondIndep`。
形式化陈述：∀ {Ω : Type u_1} {m' m₁ m₂ mΩ : MeasurableSpace Ω} [inst : StandardBorelSp
ace Ω] {hm' : m' ≤ mΩ}   {μ : MeasureTheory.Measure Ω} [inst_1 : MeasureTheory.I
sFiniteMeasure μ],   ProbabilityTheory.CondIndep m' m₁ m₂ hm' μ → ProbabilityThe
ory.CondIndep m' m₂ m₁ hm' μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.CondIndepSets.symm`：∀ {Ω : Type u_1} {m' mΩ : Measurab
leSpace Ω} [inst : StandardBorelSpace Ω] {hm' : m' ≤ mΩ} {μ : MeasureTheory.Meas
ure Ω}   [inst_1 : Measure…
-/
theorem CondIndep.symm {m' m₁ m₂ : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω}
    [StandardBorelSpace Ω] {hm' : m' ≤ mΩ} {μ : Measure Ω} [IsFiniteMeasure μ]
    (h : CondIndep m' m₁ m₂ hm' μ) :
    CondIndep m' m₂ m₁ hm' μ :=
  CondIndepSets.symm h
/-
**ProbabilityTheory.condIndep_bot_right** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTh
eory`。
形式化陈述：condIndep_bot_right (m₁ : MeasurableSpace Ω) {m' : MeasurableSpace Ω} {mΩ 
: MeasurableSpace Ω} [StandardBorelSpace Ω] {hm' : m' <= mΩ} {μ : Measure Ω} [Is
FiniteMeasure μ] : CondIndep m' m₁ ⊥ hm' μ
参数：m₁ : MeasurableSpace Ω。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.indep_bot_right`：indep_bot_right (m' : Measurab
leSpace Ω) {_mΩ : MeasurableSpace Ω} {κ : Kernel α Ω} {μ : Measure α} [IsZeroOrM
arkovKernel κ] : Indep m' ⊥ κ …
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.instIsMarkovKernelCondExpKernel`：∀ {Ω : Type u_1} {m :
 MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [inst : StandardBorelSpace Ω]   {μ 
: MeasureTheory.Measure Ω} [inst_1 : Me…
-/
theorem condIndep_bot_right (m₁ : MeasurableSpace Ω) {m' : MeasurableSpace Ω}
    {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {hm' : m' ≤ mΩ} {μ : Measure Ω} [IsFiniteMeasure μ] :
    CondIndep m' m₁ ⊥ hm' μ :=
  Kernel.indep_bot_right m₁
/-
**ProbabilityTheory.condIndep_bot_left** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityThe
ory`。
形式化陈述：condIndep_bot_left (m₁ : MeasurableSpace Ω) {m' : MeasurableSpace Ω} {mΩ :
 MeasurableSpace Ω} [StandardBorelSpace Ω] {hm' : m' <= mΩ} {μ : Measure Ω} [IsF
initeMeasure μ] : CondIndep m' ⊥ m₁ hm' μ
参数：m₁ : MeasurableSpace Ω。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.Indep.symm`：∀ {α : Type u_1} {Ω : Type u_2} {_m
α : MeasurableSpace α} {m₁ m₂ _mΩ : MeasurableSpace Ω}   {κ : ProbabilityTheory.
Kernel α Ω} {μ : MeasureT…
· 使用定理 `ProbabilityTheory.Kernel.indep_bot_right`：indep_bot_right (m' : Measurab
leSpace Ω) {_mΩ : MeasurableSpace Ω} {κ : Kernel α Ω} {μ : Measure α} [IsZeroOrM
arkovKernel κ] : Indep m' ⊥ κ …
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.instIsMarkovKernelCondExpKernel`：∀ {Ω : Type u_1} {m :
 MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [inst : StandardBorelSpace Ω]   {μ 
: MeasureTheory.Measure Ω} [inst_1 : Me…
-/
theorem condIndep_bot_left (m₁ : MeasurableSpace Ω) {m' : MeasurableSpace Ω}
    {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {hm' : m' ≤ mΩ} {μ : Measure Ω} [IsFiniteMeasure μ] :
    CondIndep m' ⊥ m₁ hm' μ :=
  (Kernel.indep_bot_right m₁).symm
/-
**ProbabilityTheory.condIndep_of_condIndep_of_le_left** 是 Mathlib 中的一个定理，位于命名空间 
`ProbabilityTheory`。
形式化陈述：condIndep_of_condIndep_of_le_left {m' m₁ m₂ m₃ : MeasurableSpace Ω} {mΩ : 
MeasurableSpace Ω} [StandardBorelSpace Ω] {hm' : m' <= mΩ} {μ : Measure Ω} [IsFi
niteMeasure μ] (h_indep : CondIndep m' m₁ m₂ hm' μ) (h31 : m₃ <= m₁) : CondIndep
 m' m₃ m₂ hm' μ
参数：h_indep : CondIndep m' m₁ m₂ hm' μ；h31 : m₃ <= m₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.indep_of_indep_of_le_left`：indep_of_indep_of_le
_left {m₁ m₂ m₃ : MeasurableSpace Ω} {_mΩ : MeasurableSpace Ω} {κ : Kernel α Ω} 
{μ : Measure α} (h_indep : Indep m₁ m₂ κ…
-/
theorem condIndep_of_condIndep_of_le_left {m' m₁ m₂ m₃ : MeasurableSpace Ω}
    {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {hm' : m' ≤ mΩ} {μ : Measure Ω} [IsFiniteMeasure μ]
    (h_indep : CondIndep m' m₁ m₂ hm' μ) (h31 : m₃ ≤ m₁) :
    CondIndep m' m₃ m₂ hm' μ :=
  Kernel.indep_of_indep_of_le_left h_indep h31
/-
**ProbabilityTheory.condIndep_of_condIndep_of_le_right** 是 Mathlib 中的一个定理，位于命名空间
 `ProbabilityTheory`。
形式化陈述：condIndep_of_condIndep_of_le_right {m' m₁ m₂ m₃ : MeasurableSpace Ω} {mΩ :
 MeasurableSpace Ω} [StandardBorelSpace Ω] {hm' : m' <= mΩ} {μ : Measure Ω} [IsF
initeMeasure μ] (h_indep : CondIndep m' m₁ m₂ hm' μ) (h32 : m₃ <= m₂) : CondInde
p m' m₁ m₃ hm' μ
参数：h_indep : CondIndep m' m₁ m₂ hm' μ；h32 : m₃ <= m₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.indep_of_indep_of_le_right`：indep_of_indep_of_l
e_right {m₁ m₂ m₃ : MeasurableSpace Ω} {_mΩ : MeasurableSpace Ω} {κ : Kernel α Ω
} {μ : Measure α} (h_indep : Indep m₁ m₂ …
-/
theorem condIndep_of_condIndep_of_le_right {m' m₁ m₂ m₃ : MeasurableSpace Ω}
    {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {hm' : m' ≤ mΩ} {μ : Measure Ω} [IsFiniteMeasure μ]
    (h_indep : CondIndep m' m₁ m₂ hm' μ) (h32 : m₃ ≤ m₂) :
    CondIndep m' m₁ m₃ hm' μ :=
  Kernel.indep_of_indep_of_le_right h_indep h32

end CondIndep

/-! ### Deducing `CondIndep` from `iCondIndep` -/


section FromiCondIndepToCondIndep

variable {m' : MeasurableSpace Ω}
  {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
  {hm' : m' ≤ mΩ} {μ : Measure Ω} [IsFiniteMeasure μ]

/-
**ProbabilityTheory.iCondIndepSets.condIndepSets** 是 Mathlib 中的一个定理，位于命名空间 `Prob
abilityTheory.iCondIndepSets`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {m' mΩ : MeasurableSpace Ω} [inst : Standa
rdBorelSpace Ω] {hm' : m' ≤ mΩ}   {μ : MeasureTheory.Measure Ω} [inst_1 : Measur
eTheory.IsFiniteMeasure μ] {s : ι → Set (Set Ω)},   ProbabilityTheory.iCondIndep
Sets m' hm' s μ →     ∀ {i j : ι}, i ≠ j → ProbabilityTheory.CondIndepSets m' hm
' (s i) (s j) μ
参数：Set Ω；s i；s j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepSets.indepSets`：∀ {α : Type u_1} {Ω : Typ
e u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {s : ι → Set (Set Ω)} {_mΩ : Mea
surableSpace Ω}   {κ : ProbabilityT…
-/
theorem iCondIndepSets.condIndepSets {s : ι → Set (Set Ω)}
    (h_indep : iCondIndepSets m' hm' s μ) {i j : ι} (hij : i ≠ j) :
    CondIndepSets m' hm' (s i) (s j) μ :=
  Kernel.iIndepSets.indepSets h_indep hij
/-
**ProbabilityTheory.iCondIndep.condIndep** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityT
heory.iCondIndep`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {m' mΩ : MeasurableSpace Ω} [inst : Standa
rdBorelSpace Ω] {hm' : m' ≤ mΩ}   {μ : MeasureTheory.Measure Ω} [inst_1 : Measur
eTheory.IsFiniteMeasure μ] {m : ι → MeasurableSpace Ω},   ProbabilityTheory.iCon
dIndep m' hm' m μ → ∀ {i j : ι}, i ≠ j → ProbabilityTheory.CondIndep m' (m i) (m
 j) hm' μ
参数：m i；m j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndep.indep`：∀ {α : Type u_1} {Ω : Type u_2} {
ι : Type u_3} {_mα : MeasurableSpace α} {m : ι → MeasurableSpace Ω}   {_mΩ : Mea
surableSpace Ω} {κ : Probab…
-/
theorem iCondIndep.condIndep {m : ι → MeasurableSpace Ω}
    (h_indep : iCondIndep m' hm' m μ) {i j : ι} (hij : i ≠ j) :
      CondIndep m' (m i) (m j) hm' μ :=
  Kernel.iIndep.indep h_indep hij
/-
**ProbabilityTheory.iCondIndepFun.condIndepFun** 是 Mathlib 中的一个定理，位于命名空间 `Probab
ilityTheory.iCondIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {m' mΩ : MeasurableSpace Ω} [inst : Standa
rdBorelSpace Ω] {hm' : m' ≤ mΩ}   {μ : MeasureTheory.Measure Ω} [inst_1 : Measur
eTheory.IsFiniteMeasure μ] {β : ι → Type u_3}   {m : (x : ι) → MeasurableSpace (
β x)} {f : (i : ι) → Ω → β i},   ProbabilityTheory.iCondIndepFun m' hm' f μ → ∀ 
{i j : ι}, i ≠ j → ProbabilityTheory.CondIndepFun m' hm' (f i) (f j) μ
参数：x : ι；β x；i : ι；f i；f j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.indepFun`：∀ {α : Type u_1} {Ω : Type 
u_2} {ι : Type u_3} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω}   {κ : Pro
babilityTheory.Kernel α Ω} {μ : M…
-/
theorem iCondIndepFun.condIndepFun {β : ι → Type*}
    {m : ∀ x, MeasurableSpace (β x)} {f : ∀ i, Ω → β i}
    (hf_Indep : iCondIndepFun m' hm' f μ) {i j : ι} (hij : i ≠ j) :
    CondIndepFun m' hm' (f i) (f j) μ :=
  Kernel.iIndepFun.indepFun hf_Indep hij

end FromiCondIndepToCondIndep

/-!
## π-system lemma

Conditional independence of measurable spaces is equivalent to conditional independence of
generating π-systems.
-/


section FromMeasurableSpacesToSetsOfSets

/-! ### Conditional independence of σ-algebras implies conditional independence of
  generating π-systems -/

variable {m' : MeasurableSpace Ω}
  {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
  {hm' : m' ≤ mΩ} {μ : Measure Ω} [IsFiniteMeasure μ]

/-
**ProbabilityTheory.iCondIndep.iCondIndepSets** 是 Mathlib 中的一个定理，位于命名空间 `Probabi
lityTheory.iCondIndep`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {m' mΩ : MeasurableSpace Ω} [inst : Standa
rdBorelSpace Ω] {hm' : m' ≤ mΩ}   {μ : MeasureTheory.Measure Ω} [inst_1 : Measur
eTheory.IsFiniteMeasure μ] {m : ι → MeasurableSpace Ω}   {s : ι → Set (Set Ω)}, 
  (∀ (n : ι), m n = MeasurableSpace.generateFrom (s n)) →     ProbabilityTheory.
iCondIndep m' hm' m μ → ProbabilityTheory.iCondIndepSets m' hm' s μ
参数：Set Ω；∀ (n : ι), m n = MeasurableSpace.generateFrom (s n)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndep.iIndepSets`：∀ {α : Type u_1} {Ω : Type u
_2} {ι : Type u_3} {_mα : MeasurableSpace α} {_mΩ : MeasurableSpace Ω}   {κ : Pr
obabilityTheory.Kernel α Ω} {μ :…
-/
theorem iCondIndep.iCondIndepSets {m : ι → MeasurableSpace Ω}
    {s : ι → Set (Set Ω)} (hms : ∀ n, m n = generateFrom (s n))
    (h_indep : iCondIndep m' hm' m μ) :
    iCondIndepSets m' hm' s μ :=
  Kernel.iIndep.iIndepSets hms h_indep
/-
**ProbabilityTheory.CondIndep.condIndepSets** 是 Mathlib 中的一个定理，位于命名空间 `Probabili
tyTheory.CondIndep`。
形式化陈述：∀ {Ω : Type u_1} {m' mΩ : MeasurableSpace Ω} [inst : StandardBorelSpace Ω]
 {hm' : m' ≤ mΩ} {μ : MeasureTheory.Measure Ω}   [inst_1 : MeasureTheory.IsFinit
eMeasure μ] {s1 s2 : Set (Set Ω)},   ProbabilityTheory.CondIndep m' (MeasurableS
pace.generateFrom s1) (MeasurableSpace.generateFrom s2) hm' μ →     ProbabilityT
heory.CondIndepSets m' hm' s1 s2 μ
参数：Set Ω；MeasurableSpace.generateFrom s1；MeasurableSpace.generateFrom s2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.Indep.indepSets`：∀ {α : Type u_1} {Ω : Type u_2
} {_mα : MeasurableSpace α} {_mΩ : MeasurableSpace Ω} {κ : ProbabilityTheory.Ker
nel α Ω}   {μ : MeasureTheory.…
-/
theorem CondIndep.condIndepSets {s1 s2 : Set (Set Ω)}
    (h_indep : CondIndep m' (generateFrom s1) (generateFrom s2) hm' μ) :
    CondIndepSets m' hm' s1 s2 μ :=
  Kernel.Indep.indepSets h_indep

end FromMeasurableSpacesToSetsOfSets

section FromPiSystemsToMeasurableSpaces

/-! ### Conditional independence of generating π-systems implies conditional independence of
  σ-algebras -/

variable {m' m₁ m₂ : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
  {hm' : m' ≤ mΩ} {μ : Measure Ω} [IsFiniteMeasure μ]

/-
**ProbabilityTheory.CondIndepSets.condIndep** 是 Mathlib 中的一个定理，位于命名空间 `Probabili
tyTheory.CondIndepSets`。
形式化陈述：∀ {Ω : Type u_1} {m' m₁ m₂ mΩ : MeasurableSpace Ω} [inst : StandardBorelSp
ace Ω] {hm' : m' ≤ mΩ}   {μ : MeasureTheory.Measure Ω} [inst_1 : MeasureTheory.I
sFiniteMeasure μ] {p1 p2 : Set (Set Ω)},   m₁ ≤ mΩ →     m₂ ≤ mΩ →       IsPiSys
tem p1 →         IsPiSystem p2 →           m₁ = MeasurableSpace.generateFrom p1 
→             m₂ = MeasurableSpace.generateFrom p2 →               ProbabilityTh
eory.CondIndepSets m' hm' p1 p2 μ → ProbabilityTheory.CondIndep m' m₁ m₂ hm' μ
参数：Set Ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IndepSets.indep`：∀ {α : Type u_1} {Ω : Type u_2
} {_mα : MeasurableSpace α} {m1 m2 m : MeasurableSpace Ω}   {κ : ProbabilityTheo
ry.Kernel α Ω} {μ : MeasureThe…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.instIsMarkovKernelCondExpKernel`：∀ {Ω : Type u_1} {m :
 MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [inst : StandardBorelSpace Ω]   {μ 
: MeasureTheory.Measure Ω} [inst_1 : Me…
-/
theorem CondIndepSets.condIndep
    {p1 p2 : Set (Set Ω)} (h1 : m₁ ≤ mΩ) (h2 : m₂ ≤ mΩ)
    (hp1 : IsPiSystem p1) (hp2 : IsPiSystem p2)
    (hpm1 : m₁ = generateFrom p1) (hpm2 : m₂ = generateFrom p2)
    (hyp : CondIndepSets m' hm' p1 p2 μ) :
    CondIndep m' m₁ m₂ hm' μ :=
  Kernel.IndepSets.indep h1 h2 hp1 hp2 hpm1 hpm2 hyp
/-
**ProbabilityTheory.CondIndepSets.condIndep'** 是 Mathlib 中的一个定理，位于命名空间 `Probabil
ityTheory.CondIndepSets`。
形式化陈述：∀ {Ω : Type u_1} {m' mΩ : MeasurableSpace Ω} [inst : StandardBorelSpace Ω]
 {hm' : m' ≤ mΩ} {μ : MeasureTheory.Measure Ω}   [inst_1 : MeasureTheory.IsFinit
eMeasure μ] {p1 p2 : Set (Set Ω)},   (∀ s ∈ p1, MeasurableSet s) →     (∀ s ∈ p2
, MeasurableSet s) →       IsPiSystem p1 →         IsPiSystem p2 →           Pro
babilityTheory.CondIndepSets m' hm' p1 p2 μ →             ProbabilityTheory.Cond
Indep m' (MeasurableSpace.generateFrom p1) (MeasurableSpace.generateFrom p2) hm'
 μ
参数：Set Ω；∀ s ∈ p1, MeasurableSet s；∀ s ∈ p2, MeasurableSet s；MeasurableSpace.gen
erateFrom p1；MeasurableSpace.generateFrom p2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IndepSets.indep'`：∀ {α : Type u_1} {Ω : Type u_
2} {_mα : MeasurableSpace α} {_mΩ : MeasurableSpace Ω} {κ : ProbabilityTheory.Ke
rnel α Ω}   {μ : MeasureTheory.…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.instIsMarkovKernelCondExpKernel`：∀ {Ω : Type u_1} {m :
 MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [inst : StandardBorelSpace Ω]   {μ 
: MeasureTheory.Measure Ω} [inst_1 : Me…
-/
theorem CondIndepSets.condIndep'
    {p1 p2 : Set (Set Ω)} (hp1m : ∀ s ∈ p1, MeasurableSet s) (hp2m : ∀ s ∈ p2, MeasurableSet s)
    (hp1 : IsPiSystem p1) (hp2 : IsPiSystem p2) (hyp : CondIndepSets m' hm' p1 p2 μ) :
    CondIndep m' (generateFrom p1) (generateFrom p2) hm' μ :=
  Kernel.IndepSets.indep' hp1m hp2m hp1 hp2 hyp
/-
**ProbabilityTheory.condIndepSets_piiUnionInter_of_disjoint** 是 Mathlib 中的一个定理，位
于命名空间 `ProbabilityTheory`。
形式化陈述：condIndepSets_piiUnionInter_of_disjoint {s : ι -> Set (Set Ω)} {S T : Set 
ι} (h_indep : iCondIndepSets m' hm' s μ) (hST : Disjoint S T) : CondIndepSets m'
 hm' (piiUnionInter s S) (piiUnionInter s T) μ
参数：Set Ω；h_indep : iCondIndepSets m' hm' s μ；hST : Disjoint S T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.indepSets_piiUnionInter_of_disjoint`：indepSets_
piiUnionInter_of_disjoint {s : ι -> Set (Set Ω)} {S T : Set ι} (h_indep : iIndep
Sets s κ μ) (hST : Disjoint S T) : IndepSets (piiU…
-/
theorem condIndepSets_piiUnionInter_of_disjoint {s : ι → Set (Set Ω)}
    {S T : Set ι} (h_indep : iCondIndepSets m' hm' s μ) (hST : Disjoint S T) :
    CondIndepSets m' hm' (piiUnionInter s S) (piiUnionInter s T) μ :=
  Kernel.indepSets_piiUnionInter_of_disjoint h_indep hST
/-
**ProbabilityTheory.iCondIndepSet.condIndep_generateFrom_of_disjoint** 是 Mathlib
 中的一个定理，位于命名空间 `ProbabilityTheory.iCondIndepSet`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {m' mΩ : MeasurableSpace Ω} [inst : Standa
rdBorelSpace Ω] {hm' : m' ≤ mΩ}   {μ : MeasureTheory.Measure Ω} [inst_1 : Measur
eTheory.IsFiniteMeasure μ] {s : ι → Set Ω},   (∀ (n : ι), MeasurableSet (s n)) →
     ProbabilityTheory.iCondIndepSet m' hm' s μ →       ∀ (S T : Set ι),        
 Disjoint S T →           ProbabilityTheory.CondIndep m' (MeasurableSpace.genera
teFrom {t | ∃ n ∈ S, s n = t})             (MeasurableSpace.generateFrom {t | ∃ 
k ∈ T, s k = t}) hm' μ
参数：∀ (n : ι), MeasurableSet (s n)；S T : Set ι；MeasurableSpace.generateFrom {t | 
∃ n ∈ S, s n = t}；MeasurableSpace.generateFrom {t | ∃ k ∈ T, s k = t}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepSet.indep_generateFrom_of_disjoint`：∀ {α 
: Type u_1} {Ω : Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {_mΩ : Measu
rableSpace Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ :…
-/
theorem iCondIndepSet.condIndep_generateFrom_of_disjoint {s : ι → Set Ω}
    (hsm : ∀ n, MeasurableSet (s n)) (hs : iCondIndepSet m' hm' s μ) (S T : Set ι)
    (hST : Disjoint S T) :
    CondIndep m' (generateFrom { t | ∃ n ∈ S, s n = t })
      (generateFrom { t | ∃ k ∈ T, s k = t }) hm' μ :=
  Kernel.iIndepSet.indep_generateFrom_of_disjoint hsm hs S T hST
/-
**ProbabilityTheory.condIndep_iSup_of_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Probab
ilityTheory`。
形式化陈述：condIndep_iSup_of_disjoint {m : ι -> MeasurableSpace Ω} (h_le : forall i, 
m i <= mΩ) (h_indep : iCondIndep m' hm' m μ) {S T : Set ι} (hST : Disjoint S T) 
: CondIndep m' (⨆ i in S, m i) (⨆ i in T, m i) hm' μ
参数：h_le : forall i, m i <= mΩ；h_indep : iCondIndep m' hm' m μ；hST : Disjoint S T
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.indep_iSup_of_disjoint`：indep_iSup_of_disjoint 
{m : ι -> MeasurableSpace Ω} (h_le : forall i, m i <= _mΩ) (h_indep : iIndep m κ
 μ) {S T : Set ι} (hST : Disjoint S T…
-/
theorem condIndep_iSup_of_disjoint {m : ι → MeasurableSpace Ω}
    (h_le : ∀ i, m i ≤ mΩ) (h_indep : iCondIndep m' hm' m μ) {S T : Set ι} (hST : Disjoint S T) :
    CondIndep m' (⨆ i ∈ S, m i) (⨆ i ∈ T, m i) hm' μ :=
  Kernel.indep_iSup_of_disjoint h_le h_indep hST
/-
**ProbabilityTheory.condIndep_iSup_of_directed_le** 是 Mathlib 中的一个定理，位于命名空间 `Pro
babilityTheory`。
形式化陈述：condIndep_iSup_of_directed_le {m : ι -> MeasurableSpace Ω} (h_indep : fora
ll i, CondIndep m' (m i) m₁ hm' μ) (h_le : forall i, m i <= mΩ) (h_le' : m₁ <= m
Ω) (hm : Directed (· <= ·) m) : CondIndep m' (⨆ i, m i) m₁ hm' μ
参数：h_indep : forall i, CondIndep m' (m i) m₁ hm' μ；h_le : forall i, m i <= mΩ；h_
le' : m₁ <= mΩ；hm : Directed (· <= ·) m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.indep_iSup_of_directed_le`：indep_iSup_of_direct
ed_le {Ω} {m : ι -> MeasurableSpace Ω} {m' m0 : MeasurableSpace Ω} {κ : Kernel α
 Ω} {μ : Measure α} [IsZeroOrMarkovKerne…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.instIsMarkovKernelCondExpKernel`：∀ {Ω : Type u_1} {m :
 MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [inst : StandardBorelSpace Ω]   {μ 
: MeasureTheory.Measure Ω} [inst_1 : Me…
-/
theorem condIndep_iSup_of_directed_le {m : ι → MeasurableSpace Ω}
    (h_indep : ∀ i, CondIndep m' (m i) m₁ hm' μ)
    (h_le : ∀ i, m i ≤ mΩ) (h_le' : m₁ ≤ mΩ) (hm : Directed (· ≤ ·) m) :
    CondIndep m' (⨆ i, m i) m₁ hm' μ :=
  Kernel.indep_iSup_of_directed_le h_indep h_le h_le' hm
/-
**ProbabilityTheory.iCondIndepSet.condIndep_generateFrom_lt** 是 Mathlib 中的一个定理，位
于命名空间 `ProbabilityTheory.iCondIndepSet`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {m' mΩ : MeasurableSpace Ω} [inst : Standa
rdBorelSpace Ω] {hm' : m' ≤ mΩ}   {μ : MeasureTheory.Measure Ω} [inst_1 : Measur
eTheory.IsFiniteMeasure μ] [inst_2 : Preorder ι] {s : ι → Set Ω},   (∀ (n : ι), 
MeasurableSet (s n)) →     ProbabilityTheory.iCondIndepSet m' hm' s μ →       ∀ 
(i : ι),         ProbabilityTheory.CondIndep m' (MeasurableSpace.generateFrom {s
 i})           (MeasurableSpace.generateFrom {t | ∃ j < i, s j = t}) hm' μ
参数：∀ (n : ι), MeasurableSet (s n)；i : ι；MeasurableSpace.generateFrom {s i}；Measu
rableSpace.generateFrom {t | ∃ j < i, s j = t}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepSet.indep_generateFrom_lt`：∀ {α : Type u_
1} {Ω : Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {_mΩ : MeasurableSpac
e Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ :…
-/
theorem iCondIndepSet.condIndep_generateFrom_lt [Preorder ι] {s : ι → Set Ω}
    (hsm : ∀ n, MeasurableSet (s n)) (hs : iCondIndepSet m' hm' s μ) (i : ι) :
    CondIndep m' (generateFrom {s i}) (generateFrom { t | ∃ j < i, s j = t }) hm' μ :=
  Kernel.iIndepSet.indep_generateFrom_lt hsm hs i
/-
**ProbabilityTheory.iCondIndepSet.condIndep_generateFrom_le** 是 Mathlib 中的一个定理，位
于命名空间 `ProbabilityTheory.iCondIndepSet`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {m' mΩ : MeasurableSpace Ω} [inst : Standa
rdBorelSpace Ω] {hm' : m' ≤ mΩ}   {μ : MeasureTheory.Measure Ω} [inst_1 : Measur
eTheory.IsFiniteMeasure μ] [inst_2 : Preorder ι] {s : ι → Set Ω},   (∀ (n : ι), 
MeasurableSet (s n)) →     ProbabilityTheory.iCondIndepSet m' hm' s μ →       ∀ 
(i : ι) {k : ι},         i < k →           ProbabilityTheory.CondIndep m' (Measu
rableSpace.generateFrom {s k})             (MeasurableSpace.generateFrom {t | ∃ 
j ≤ i, s j = t}) hm' μ
参数：∀ (n : ι), MeasurableSet (s n)；i : ι；MeasurableSpace.generateFrom {s k}；Measu
rableSpace.generateFrom {t | ∃ j ≤ i, s j = t}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepSet.indep_generateFrom_le`：∀ {α : Type u_
1} {Ω : Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {_mΩ : MeasurableSpac
e Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ :…
-/
theorem iCondIndepSet.condIndep_generateFrom_le [Preorder ι] {s : ι → Set Ω}
    (hsm : ∀ n, MeasurableSet (s n)) (hs : iCondIndepSet m' hm' s μ) (i : ι) {k : ι} (hk : i < k) :
    CondIndep m' (generateFrom {s k}) (generateFrom { t | ∃ j ≤ i, s j = t }) hm' μ :=
  Kernel.iIndepSet.indep_generateFrom_le hsm hs i hk
/-
**ProbabilityTheory.iCondIndepSet.condIndep_generateFrom_le_nat** 是 Mathlib 中的一个
定理，位于命名空间 `ProbabilityTheory.iCondIndepSet`。
形式化陈述：∀ {Ω : Type u_1} {m' mΩ : MeasurableSpace Ω} [inst : StandardBorelSpace Ω]
 {hm' : m' ≤ mΩ} {μ : MeasureTheory.Measure Ω}   [inst_1 : MeasureTheory.IsFinit
eMeasure μ] {s : ℕ → Set Ω},   (∀ (n : ℕ), MeasurableSet (s n)) →     Probabilit
yTheory.iCondIndepSet m' hm' s μ →       ∀ (n : ℕ),         ProbabilityTheory.Co
ndIndep m' (MeasurableSpace.generateFrom {s (n + 1)})           (MeasurableSpace
.generateFrom {t | ∃ k ≤ n, s k = t}) hm' μ
参数：∀ (n : ℕ), MeasurableSet (s n)；n : ℕ；MeasurableSpace.generateFrom {s (n + 1)}
；MeasurableSpace.generateFrom {t | ∃ k ≤ n, s k = t}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepSet.indep_generateFrom_le_nat`：∀ {α : Typ
e u_1} {Ω : Type u_2} {_mα : MeasurableSpace α} {_mΩ : MeasurableSpace Ω} {κ : P
robabilityTheory.Kernel α Ω}   {μ : MeasureTheory.…
-/
theorem iCondIndepSet.condIndep_generateFrom_le_nat {s : ℕ → Set Ω}
    (hsm : ∀ n, MeasurableSet (s n)) (hs : iCondIndepSet m' hm' s μ) (n : ℕ) :
    CondIndep m' (generateFrom {s (n + 1)}) (generateFrom { t | ∃ k ≤ n, s k = t }) hm' μ :=
  Kernel.iIndepSet.indep_generateFrom_le_nat hsm hs n
/-
**ProbabilityTheory.condIndep_iSup_of_monotone** 是 Mathlib 中的一个定理，位于命名空间 `Probab
ilityTheory`。
形式化陈述：condIndep_iSup_of_monotone [SemilatticeSup ι] {m : ι -> MeasurableSpace Ω}
 (h_indep : forall i, CondIndep m' (m i) m₁ hm' μ) (h_le : forall i, m i <= mΩ) 
(h_le' : m₁ <= mΩ) (hm : Monotone m) : CondIndep m' (⨆ i, m i) m₁ hm' μ
参数：h_indep : forall i, CondIndep m' (m i) m₁ hm' μ；h_le : forall i, m i <= mΩ；h_
le' : m₁ <= mΩ；hm : Monotone m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.indep_iSup_of_monotone`：indep_iSup_of_monotone 
[SemilatticeSup ι] {Ω} {m : ι -> MeasurableSpace Ω} {m' m0 : MeasurableSpace Ω} 
{κ : Kernel α Ω} {μ : Measure α} [IsZ…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.instIsMarkovKernelCondExpKernel`：∀ {Ω : Type u_1} {m :
 MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [inst : StandardBorelSpace Ω]   {μ 
: MeasureTheory.Measure Ω} [inst_1 : Me…
-/
theorem condIndep_iSup_of_monotone [SemilatticeSup ι] {m : ι → MeasurableSpace Ω}
    (h_indep : ∀ i, CondIndep m' (m i) m₁ hm' μ) (h_le : ∀ i, m i ≤ mΩ) (h_le' : m₁ ≤ mΩ)
    (hm : Monotone m) :
    CondIndep m' (⨆ i, m i) m₁ hm' μ :=
  Kernel.indep_iSup_of_monotone h_indep h_le h_le' hm
/-
**ProbabilityTheory.condIndep_iSup_of_antitone** 是 Mathlib 中的一个定理，位于命名空间 `Probab
ilityTheory`。
形式化陈述：condIndep_iSup_of_antitone [SemilatticeInf ι] {m : ι -> MeasurableSpace Ω}
 (h_indep : forall i, CondIndep m' (m i) m₁ hm' μ) (h_le : forall i, m i <= mΩ) 
(h_le' : m₁ <= mΩ) (hm : Antitone m) : CondIndep m' (⨆ i, m i) m₁ hm' μ
参数：h_indep : forall i, CondIndep m' (m i) m₁ hm' μ；h_le : forall i, m i <= mΩ；h_
le' : m₁ <= mΩ；hm : Antitone m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.indep_iSup_of_antitone`：indep_iSup_of_antitone 
[SemilatticeInf ι] {Ω} {m : ι -> MeasurableSpace Ω} {m' m0 : MeasurableSpace Ω} 
{κ : Kernel α Ω} {μ : Measure α} [IsZ…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.instIsMarkovKernelCondExpKernel`：∀ {Ω : Type u_1} {m :
 MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [inst : StandardBorelSpace Ω]   {μ 
: MeasureTheory.Measure Ω} [inst_1 : Me…
-/
theorem condIndep_iSup_of_antitone [SemilatticeInf ι] {m : ι → MeasurableSpace Ω}
    (h_indep : ∀ i, CondIndep m' (m i) m₁ hm' μ) (h_le : ∀ i, m i ≤ mΩ) (h_le' : m₁ ≤ mΩ)
    (hm : Antitone m) :
    CondIndep m' (⨆ i, m i) m₁ hm' μ :=
  Kernel.indep_iSup_of_antitone h_indep h_le h_le' hm
/-
**ProbabilityTheory.iCondIndepSets.piiUnionInter_of_notMem** 是 Mathlib 中的一个定理，位于
命名空间 `ProbabilityTheory.iCondIndepSets`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {m' mΩ : MeasurableSpace Ω} [inst : Standa
rdBorelSpace Ω] {hm' : m' ≤ mΩ}   {μ : MeasureTheory.Measure Ω} [inst_1 : Measur
eTheory.IsFiniteMeasure μ] {π : ι → Set (Set Ω)} {a : ι} {S : Finset ι},   Proba
bilityTheory.iCondIndepSets m' hm' π μ →     a ∉ S → ProbabilityTheory.CondIndep
Sets m' hm' (piiUnionInter π ↑S) (π a) μ
参数：Set Ω；piiUnionInter π ↑S；π a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepSets.piiUnionInter_of_notMem`：∀ {α : Type
 u_1} {Ω : Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {_mΩ : MeasurableS
pace Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ :…
-/
theorem iCondIndepSets.piiUnionInter_of_notMem {π : ι → Set (Set Ω)} {a : ι} {S : Finset ι}
    (hp_ind : iCondIndepSets m' hm' π μ) (haS : a ∉ S) :
    CondIndepSets m' hm' (piiUnionInter π S) (π a) μ :=
  Kernel.iIndepSets.piiUnionInter_of_notMem hp_ind haS

/-- The σ-algebras generated by conditionally independent pi-systems are conditionally independent.
-/
/-
**ProbabilityTheory.iCondIndepSets.iCondIndep** 是 Mathlib 中的一个定理，位于命名空间 `Probabi
lityTheory.iCondIndepSets`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {m' mΩ : MeasurableSpace Ω} [inst : Standa
rdBorelSpace Ω] {hm' : m' ≤ mΩ}   {μ : MeasureTheory.Measure Ω} [inst_1 : Measur
eTheory.IsFiniteMeasure μ] (m : ι → MeasurableSpace Ω),   (∀ (i : ι), m i ≤ mΩ) 
→     ∀ (π : ι → Set (Set Ω)),       (∀ (n : ι), IsPiSystem (π n)) →         (∀ 
(i : ι), m i = MeasurableSpace.generateFrom (π i)) →           ProbabilityTheory
.iCondIndepSets m' hm' π μ → ProbabilityTheory.iCondIndep m' hm' m μ
参数：m : ι → MeasurableSpace Ω；∀ (i : ι), m i ≤ mΩ；π : ι → Set (Set Ω)；∀ (n : ι), 
IsPiSystem (π n)；∀ (i : ι), m i = MeasurableSpace.generateFrom (π i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepSets.iIndep`：∀ {α : Type u_1} {Ω : Type u
_2} {ι : Type u_3} {_mα : MeasurableSpace α} {_mΩ : MeasurableSpace Ω}   {κ : Pr
obabilityTheory.Kernel α Ω} {μ :…

--- 原说明 ---
The σ-algebras generated by conditionally independent pi-systems are conditional
ly independent.
-/
theorem iCondIndepSets.iCondIndep (m : ι → MeasurableSpace Ω)
    (h_le : ∀ i, m i ≤ mΩ) (π : ι → Set (Set Ω)) (h_pi : ∀ n, IsPiSystem (π n))
    (h_generate : ∀ i, m i = generateFrom (π i)) (h_ind : iCondIndepSets m' hm' π μ) :
    iCondIndep m' hm' m μ :=
  Kernel.iIndepSets.iIndep m h_le π h_pi h_generate h_ind

end FromPiSystemsToMeasurableSpaces

section CondIndepSet

/-! ### Conditional independence of measurable sets

-/

variable {m' m₁ m₂ : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
  {hm' : m' ≤ mΩ}
  {s t : Set Ω} (S T : Set (Set Ω))

/-
**ProbabilityTheory.CondIndepSets.condIndepSet_of_mem** 是 Mathlib 中的一个定理，位于命名空间 
`ProbabilityTheory.CondIndepSets`。
形式化陈述：∀ {Ω : Type u_1} {m' mΩ : MeasurableSpace Ω} [inst : StandardBorelSpace Ω]
 {hm' : m' ≤ mΩ} {s t : Set Ω}   (S T : Set (Set Ω)),   s ∈ S →     t ∈ T →     
  MeasurableSet s →         MeasurableSet t →           ∀ (μ : MeasureTheory.Mea
sure Ω) [inst_1 : MeasureTheory.IsFiniteMeasure μ],             ProbabilityTheor
y.CondIndepSets m' hm' S T μ → ProbabilityTheory.CondIndepSet m' hm' s t μ
参数：S T : Set (Set Ω)；μ : MeasureTheory.Measure Ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IndepSets.indepSet_of_mem`：∀ {α : Type u_1} {Ω 
: Type u_2} {_mα : MeasurableSpace α} {s t : Set Ω} (S T : Set (Set Ω)) {_m0 : M
easurableSpace Ω},   s ∈ S →     t ∈ T →…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.instIsMarkovKernelCondExpKernel`：∀ {Ω : Type u_1} {m :
 MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [inst : StandardBorelSpace Ω]   {μ 
: MeasureTheory.Measure Ω} [inst_1 : Me…
-/
theorem CondIndepSets.condIndepSet_of_mem (hs : s ∈ S) (ht : t ∈ T)
    (hs_meas : MeasurableSet s) (ht_meas : MeasurableSet t) (μ : Measure Ω) [IsFiniteMeasure μ]
    (h_indep : CondIndepSets m' hm' S T μ) :
    CondIndepSet m' hm' s t μ :=
  Kernel.IndepSets.indepSet_of_mem _ _ hs ht hs_meas ht_meas _ _ h_indep
/-
**ProbabilityTheory.CondIndep.condIndepSet_of_measurableSet** 是 Mathlib 中的一个定理，位
于命名空间 `ProbabilityTheory.CondIndep`。
形式化陈述：∀ {Ω : Type u_1} {m' m₁ m₂ mΩ : MeasurableSpace Ω} [inst : StandardBorelSp
ace Ω] {hm' : m' ≤ mΩ}   {μ : MeasureTheory.Measure Ω} [inst_1 : MeasureTheory.I
sFiniteMeasure μ],   ProbabilityTheory.CondIndep m' m₁ m₂ hm' μ →     ∀ {s t : S
et Ω}, MeasurableSet s → MeasurableSet t → ProbabilityTheory.CondIndepSet m' hm'
 s t μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.Indep.indepSet_of_measurableSet`：∀ {α : Type u_
1} {Ω : Type u_2} {_mα : MeasurableSpace α} {m₁ m₂ x : MeasurableSpace Ω}   {κ :
 ProbabilityTheory.Kernel α Ω} {μ : MeasureThe…
-/
theorem CondIndep.condIndepSet_of_measurableSet {μ : Measure Ω} [IsFiniteMeasure μ]
    (h_indep : CondIndep m' m₁ m₂ hm' μ) {s t : Set Ω} (hs : MeasurableSet[m₁] s)
    (ht : MeasurableSet[m₂] t) :
    CondIndepSet m' hm' s t μ :=
  Kernel.Indep.indepSet_of_measurableSet h_indep hs ht
/-
**ProbabilityTheory.condIndep_iff_forall_condIndepSet** 是 Mathlib 中的一个定理，位于命名空间 
`ProbabilityTheory`。
形式化陈述：condIndep_iff_forall_condIndepSet (μ : Measure Ω) [IsFiniteMeasure μ] : Co
ndIndep m' m₁ m₂ hm' μ ↔ forall s t, MeasurableSet[m₁] s -> MeasurableSet[m₂] t 
-> CondIndepSet m' hm' s t μ
参数：μ : Measure Ω。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.indep_iff_forall_indepSet`：indep_iff_forall_ind
epSet (m₁ m₂ : MeasurableSpace Ω) {_m0 : MeasurableSpace Ω} (κ : Kernel α Ω) (μ 
: Measure α) : Indep m₁ m₂ κ μ ↔ forall …
-/
theorem condIndep_iff_forall_condIndepSet (μ : Measure Ω) [IsFiniteMeasure μ] :
    CondIndep m' m₁ m₂ hm' μ ↔ ∀ s t, MeasurableSet[m₁] s → MeasurableSet[m₂] t
      → CondIndepSet m' hm' s t μ :=
  Kernel.indep_iff_forall_indepSet m₁ m₂ _ _

end CondIndepSet

section CondIndepFun

/-! ### Conditional independence of random variables

-/

variable {β β' : Type*} {m' : MeasurableSpace Ω}
  {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
  {hm' : m' ≤ mΩ} {μ : Measure Ω} [IsFiniteMeasure μ]
  {f : Ω → β} {g : Ω → β'}

/-
**ProbabilityTheory.condIndepFun_iff_condExp_inter_preimage_eq_mul** 是 Mathlib 中
的一个定理，位于命名空间 `ProbabilityTheory`。
形式化陈述：condIndepFun_iff_condExp_inter_preimage_eq_mul {mβ : MeasurableSpace β} {m
β' : MeasurableSpace β'} (hf : Measurable f) (hg : Measurable g) : CondIndepFun 
m' hm' f g μ ↔ forall s t, MeasurableSet s -> MeasurableSet t -> (μ⟦f ⁻¹' s inte
r g ⁻¹' t | m'⟧) =ᵐ[μ] fun ω => (μ⟦f ⁻¹' s | m'⟧) ω * (μ⟦g ⁻¹' t | m'⟧) ω
参数：hf : Measurable f；hg : Measurable g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.condIndepFun_iff`：condIndepFun_iff {β γ : Type*} [mβ :
 MeasurableSpace β] [mγ : MeasurableSpace γ] (f : Ω -> β) (g : Ω -> γ) (hf : Mea
surable f) (hg : Measura…
-/
theorem condIndepFun_iff_condExp_inter_preimage_eq_mul {mβ : MeasurableSpace β}
    {mβ' : MeasurableSpace β'} (hf : Measurable f) (hg : Measurable g) :
    CondIndepFun m' hm' f g μ ↔
      ∀ s t, MeasurableSet s → MeasurableSet t
        → (μ⟦f ⁻¹' s ∩ g ⁻¹' t | m'⟧) =ᵐ[μ] fun ω ↦ (μ⟦f ⁻¹' s | m'⟧) ω * (μ⟦g ⁻¹' t | m'⟧) ω := by
  rw [condIndepFun_iff _ _ _ _ hf hg]
  refine ⟨fun h s t hs ht ↦ ?_, fun h s t ↦ ?_⟩
  · exact h (f ⁻¹' s) (g ⁻¹' t) ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
  · rintro ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
    exact h s t hs ht
/-
**ProbabilityTheory.iCondIndepFun_iff_condExp_inter_preimage_eq_mul** 是 Mathlib 
中的一个定理，位于命名空间 `ProbabilityTheory`。
形式化陈述：iCondIndepFun_iff_condExp_inter_preimage_eq_mul {β : ι -> Type*} (m : fora
ll x, MeasurableSpace (β x)) (f : forall i, Ω -> β i) (hf : forall i, Measurable
 (f i)) : iCondIndepFun m' hm' f μ ↔ forall (S : Finset ι) {sets : forall i : ι,
 Set (β i)} (_H : forall i, i in S -> MeasurableSet[m i] (sets i)), (μ⟦⋂ i in S,
 f i ⁻¹' sets i | m'⟧) =ᵐ[μ] ∏ i in S, (μ⟦f i ⁻¹' sets i | m'⟧)
参数：m : forall x, MeasurableSpace (β x)；f : forall i, Ω -> β i；hf : forall i, Mea
surable (f i)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.iCondIndepFun_iff`：iCondIndepFun_iff {β : ι -> Type*} 
(m : forall x : ι, MeasurableSpace (β x)) (f : forall x : ι, Ω -> β x) (hf : for
all i, Measurable (f i)) …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem iCondIndepFun_iff_condExp_inter_preimage_eq_mul {β : ι → Type*}
    (m : ∀ x, MeasurableSpace (β x)) (f : ∀ i, Ω → β i) (hf : ∀ i, Measurable (f i)) :
    iCondIndepFun m' hm' f μ ↔
      ∀ (S : Finset ι) {sets : ∀ i : ι, Set (β i)} (_H : ∀ i, i ∈ S → MeasurableSet[m i] (sets i)),
        (μ⟦⋂ i ∈ S, f i ⁻¹' sets i | m'⟧) =ᵐ[μ] ∏ i ∈ S, (μ⟦f i ⁻¹' sets i | m'⟧) := by
  rw [iCondIndepFun_iff]
  swap
  · exact hf
  refine ⟨fun h s sets h_sets ↦ ?_, fun h s sets h_sets ↦ ?_⟩
  · refine h s (g := fun i ↦ f i ⁻¹' (sets i)) (fun i hi ↦ ?_)
    exact ⟨sets i, h_sets i hi, rfl⟩
  · classical
    let g := fun i ↦ if hi : i ∈ s then (h_sets i hi).choose else Set.univ
    specialize h s (sets := g) (fun i hi ↦ ?_)
    · simp only [g, dif_pos hi]
      exact (h_sets i hi).choose_spec.1
    · have hg : ∀ i ∈ s, sets i = f i ⁻¹' g i := by
        intro i hi
        rw [(h_sets i hi).choose_spec.2.symm]
        simp only [g, dif_pos hi]
      convert! h with i hi i hi <;> exact hg i hi
/-
**ProbabilityTheory.condIndepFun_iff_condIndepSet_preimage** 是 Mathlib 中的一个定理，位于
命名空间 `ProbabilityTheory`。
形式化陈述：condIndepFun_iff_condIndepSet_preimage {mβ : MeasurableSpace β} {mβ' : Mea
surableSpace β'} (hf : Measurable f) (hg : Measurable g) : CondIndepFun m' hm' f
 g μ ↔ forall s t, MeasurableSet s -> MeasurableSet t -> CondIndepSet m' hm' (f 
⁻¹' s) (g ⁻¹' t) μ
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
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.instIsMarkovKernelCondExpKernel`：∀ {Ω : Type u_1} {m :
 MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [inst : StandardBorelSpace Ω]   {μ 
: MeasureTheory.Measure Ω} [inst_1 : Me…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem condIndepFun_iff_condIndepSet_preimage {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    (hf : Measurable f) (hg : Measurable g) :
    CondIndepFun m' hm' f g μ ↔
      ∀ s t, MeasurableSet s → MeasurableSet t → CondIndepSet m' hm' (f ⁻¹' s) (g ⁻¹' t) μ := by
  simp only [CondIndepFun, CondIndepSet, Kernel.indepFun_iff_indepSet_preimage hf hg]

@[symm]
nonrec theorem CondIndepFun.symm {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    {f : Ω → β} {g : Ω → β'} (hfg : CondIndepFun m' hm' f g μ) :
    CondIndepFun m' hm' g f μ :=
  hfg.symm
/-
**ProbabilityTheory.CondIndepFun.comp** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheo
ry.CondIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {β : Type u_3} {β' : Type u_4} {m' mΩ : MeasurableSpace Ω
} [inst : StandardBorelSpace Ω]   {hm' : m' ≤ mΩ} {μ : MeasureTheory.Measure Ω} 
[inst_1 : MeasureTheory.IsFiniteMeasure μ] {f : Ω → β} {g : Ω → β'}   {γ : Type 
u_5} {γ' : Type u_6} {_mβ : MeasurableSpace β} {_mβ' : MeasurableSpace β'} {_mγ 
: MeasurableSpace γ}   {_mγ' : MeasurableSpace γ'} {φ : β → γ} {ψ : β' → γ'},   
ProbabilityTheory.CondIndepFun m' hm' f g μ →     Measurable φ → Measurable ψ → 
ProbabilityTheory.CondIndepFun m' hm' (φ ∘ f) (ψ ∘ g) μ
参数：φ ∘ f；ψ ∘ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IndepFun.comp`：∀ {α : Type u_1} {Ω : Type u_2} 
{β : Type u_4} {β' : Type u_5} {γ : Type u_6} {γ' : Type u_7} {mα : MeasurableSp
ace α}   {mΩ : MeasurableSpa…
-/
theorem CondIndepFun.comp {γ γ' : Type*} {_mβ : MeasurableSpace β} {_mβ' : MeasurableSpace β'}
    {_mγ : MeasurableSpace γ} {_mγ' : MeasurableSpace γ'} {φ : β → γ} {ψ : β' → γ'}
    (hfg : CondIndepFun m' hm' f g μ) (hφ : Measurable φ) (hψ : Measurable ψ) :
    CondIndepFun m' hm' (φ ∘ f) (ψ ∘ g) μ :=
  Kernel.IndepFun.comp hfg hφ hψ
/-
**ProbabilityTheory.condIndepFun_const_left** 是 Mathlib 中的一个引理，位于命名空间 `Probabili
tyTheory`。
形式化陈述：condIndepFun_const_left {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'
} (c : β) (X : Ω -> β') : CondIndepFun m' hm' (fun _ => c) X μ
参数：c : β；X : Ω -> β'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.Kernel.indepFun_const_left`：indepFun_const_left {mβ : 
MeasurableSpace β} {mβ' : MeasurableSpace β'} [IsZeroOrMarkovKernel κ] (c : β') 
(X : Ω -> β) : IndepFun (fun _ => …
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.instIsMarkovKernelCondExpKernel`：∀ {Ω : Type u_1} {m :
 MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [inst : StandardBorelSpace Ω]   {μ 
: MeasureTheory.Measure Ω} [inst_1 : Me…
-/
lemma condIndepFun_const_left {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    (c : β) (X : Ω → β') :
    CondIndepFun m' hm' (fun _ ↦ c) X μ :=
  Kernel.indepFun_const_left c X
/-
**ProbabilityTheory.condIndepFun_const_right** 是 Mathlib 中的一个引理，位于命名空间 `Probabil
ityTheory`。
形式化陈述：condIndepFun_const_right {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β
'} (X : Ω -> β) (c : β') : CondIndepFun m' hm' X (fun _ => c) μ
参数：X : Ω -> β；c : β'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.Kernel.indepFun_const_right`：indepFun_const_right {mβ 
: MeasurableSpace β} {mβ' : MeasurableSpace β'} [IsZeroOrMarkovKernel κ] (X : Ω 
-> β) (c : β') : IndepFun X (fun _ …
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.instIsMarkovKernelCondExpKernel`：∀ {Ω : Type u_1} {m :
 MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [inst : StandardBorelSpace Ω]   {μ 
: MeasureTheory.Measure Ω} [inst_1 : Me…
-/
lemma condIndepFun_const_right {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    (X : Ω → β) (c : β') :
    CondIndepFun m' hm' X (fun _ ↦ c) μ :=
  Kernel.indepFun_const_right X c
/-
**ProbabilityTheory.CondIndepFun.neg_right** 是 Mathlib 中的一个定理，位于命名空间 `Probabilit
yTheory.CondIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {β : Type u_3} {β' : Type u_4} {m' mΩ : MeasurableSpace Ω
} [inst : StandardBorelSpace Ω]   {hm' : m' ≤ mΩ} {μ : MeasureTheory.Measure Ω} 
[inst_1 : MeasureTheory.IsFiniteMeasure μ] {f : Ω → β} {g : Ω → β'}   {_mβ : Mea
surableSpace β} {_mβ' : MeasurableSpace β'} [inst_2 : Neg β'] [MeasurableNeg β']
,   ProbabilityTheory.CondIndepFun m' hm' f g μ → ProbabilityTheory.CondIndepFun
 m' hm' f (-g) μ
参数：-g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.CondIndepFun.comp`：∀ {Ω : Type u_1} {β : Type u_3} {β'
 : Type u_4} {m' mΩ : MeasurableSpace Ω} [inst : StandardBorelSpace Ω]   {hm' : 
m' ≤ mΩ} {μ : MeasureTheo…
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)
· 使用定理 `MeasurableNeg.measurable_neg`：∀ {G : Type u_2} {inst : Neg G} {inst_1 : 
MeasurableSpace G} [self : MeasurableNeg G], Measurable Neg.neg
-/
theorem CondIndepFun.neg_right {_mβ : MeasurableSpace β} {_mβ' : MeasurableSpace β'} [Neg β']
    [MeasurableNeg β'] (hfg : CondIndepFun m' hm' f g μ) :
    CondIndepFun m' hm' f (-g) μ := hfg.comp measurable_id measurable_neg
/-
**ProbabilityTheory.CondIndepFun.neg_left** 是 Mathlib 中的一个定理，位于命名空间 `Probability
Theory.CondIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {β : Type u_3} {β' : Type u_4} {m' mΩ : MeasurableSpace Ω
} [inst : StandardBorelSpace Ω]   {hm' : m' ≤ mΩ} {μ : MeasureTheory.Measure Ω} 
[inst_1 : MeasureTheory.IsFiniteMeasure μ] {f : Ω → β} {g : Ω → β'}   {_mβ : Mea
surableSpace β} {_mβ' : MeasurableSpace β'} [inst_2 : Neg β] [MeasurableNeg β], 
  ProbabilityTheory.CondIndepFun m' hm' f g μ → ProbabilityTheory.CondIndepFun m
' hm' (-f) g μ
参数：-f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.CondIndepFun.comp`：∀ {Ω : Type u_1} {β : Type u_3} {β'
 : Type u_4} {m' mΩ : MeasurableSpace Ω} [inst : StandardBorelSpace Ω]   {hm' : 
m' ≤ mΩ} {μ : MeasureTheo…
· 使用定理 `MeasurableNeg.measurable_neg`：∀ {G : Type u_2} {inst : Neg G} {inst_1 : 
MeasurableSpace G} [self : MeasurableNeg G], Measurable Neg.neg
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)
-/
theorem CondIndepFun.neg_left {_mβ : MeasurableSpace β} {_mβ' : MeasurableSpace β'} [Neg β]
    [MeasurableNeg β] (hfg : CondIndepFun m' hm' f g μ) :
    CondIndepFun m' hm' (-f) g μ := hfg.comp measurable_neg measurable_id
/-
**ProbabilityTheory.condIndepFun_of_measurable_left** 是 Mathlib 中的一个引理，位于命名空间 `P
robabilityTheory`。
形式化陈述：condIndepFun_of_measurable_left {mβ : MeasurableSpace β} {mβ' : Measurable
Space β'} {X : Ω -> β} {Y : Ω -> β'} (hX : Measurable[m'] X) (hY : Measurable Y)
 : CondIndepFun m' hm' X Y μ
参数：hX : Measurable[m'] X；hY : Measurable Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.condIndepFun_iff`：condIndepFun_iff {β γ : Type*} [mβ :
 MeasurableSpace β] [mγ : MeasurableSpace γ] (f : Ω -> β) (g : Ω -> γ) (hf : Mea
surable f) (hg : Measura…
· 使用定理 `Measurable.mono`：Measurable.mono {ma ma' : MeasurableSpace α} {mb mb' : 
MeasurableSpace β} {f : α -> β} (hf : @Measurable α β ma mb f) (ha : ma <= ma') 
(hb :…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用引理 `Set.inter_indicator_one`：inter_indicator_one : (s inter t).indicator (1 
: ι -> M₀) = s.indicator 1 * t.indicator 1
· 使用定理 `MeasureTheory.condExp_stronglyMeasurable_mul_of_bound`：condExp_stronglyM
easurable_mul_of_bound (hm : m <= mΩ) [IsFiniteMeasure μ] {f g : Ω -> Real} (hf 
: StronglyMeasurable[m] f) (hg : Integrable…
· 使用定理 `MeasureTheory.StronglyMeasurable.indicator`：∀ {α : Type u_1} {β : Type u
_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β] [inst_1 : Ze
ro β],   MeasureTheory.StronglyM…
· 使用定理 `MeasureTheory.stronglyMeasurable_const`：stronglyMeasurable_const {b : β}
 : StronglyMeasurable fun _ : α => b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.integrable_indicator_iff`：integrable_indicator_iff (hs : M
easurableSet s) : Integrable (indicator s f) μ ↔ IntegrableOn f s μ
· 使用定理 `MeasureTheory.integrableOn_const`：integrableOn_const {C : ε'} (hs : μ s 
!= ∞
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用引理 `enorm_ne_top`：enorm_ne_top : ‖x‖ₑ != ∞
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `Set.indicator.eq_1`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] (s :
 Set α) (f : α → M) (x : α),   s.indicator f x = if x ∈ s then f x else 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `MeasureTheory.condExp_of_stronglyMeasurable`：condExp_of_stronglyMeasurab
le (hm : m <= m₀) [hμm : SigmaFinite (μ.trim hm)] {f : α -> E} (hf : StronglyMea
surable[m] f) (hfi : Integrable f…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `Measurable.le`：Measurable.le {α} {m m0 : MeasurableSpace α} {_ : Measura
bleSpace β} (hm : m <= m0) {f : α -> β} (hf : Measurable[m] f) : Measurable[m0] 
f
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
-/
lemma condIndepFun_of_measurable_left {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    {X : Ω → β} {Y : Ω → β'} (hX : Measurable[m'] X) (hY : Measurable Y) :
    CondIndepFun m' hm' X Y μ := by
  rw [condIndepFun_iff _ hm' _ _ (hX.mono hm' le_rfl) hY]
  rintro _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
  rw [show (fun ω : Ω ↦ (1 : ℝ)) = 1 from rfl, Set.inter_indicator_one]
  calc μ[(X ⁻¹' s).indicator 1 * (Y ⁻¹' t).indicator 1 | m']
  _ =ᵐ[μ] (X ⁻¹' s).indicator 1 * μ[(Y ⁻¹' t).indicator 1 | m'] := by
    refine condExp_stronglyMeasurable_mul_of_bound hm' (stronglyMeasurable_const.indicator (hX hs))
      ((integrable_indicator_iff (hY ht)).2 integrableOn_const) 1 (ae_of_all μ fun ω ↦ ?_)
    rw [Set.indicator]
    split_ifs with h <;> simp
  _ =ᵐ[μ] μ[(X ⁻¹' s).indicator 1 | m'] * μ[(Y ⁻¹' t).indicator 1 | m'] := by
    nth_rw 2 [condExp_of_stronglyMeasurable hm']
    · exact stronglyMeasurable_const.indicator (hX hs)
    · exact (integrable_indicator_iff ((hX.le hm') hs)).2 integrableOn_const
/-
**ProbabilityTheory.condIndepFun_of_measurable_right** 是 Mathlib 中的一个引理，位于命名空间 `
ProbabilityTheory`。
形式化陈述：condIndepFun_of_measurable_right {mβ : MeasurableSpace β} {mβ' : Measurabl
eSpace β'} {X : Ω -> β} {Y : Ω -> β'} (hX : Measurable X) (hY : Measurable[m'] Y
) : CondIndepFun m' hm' X Y μ
参数：hX : Measurable X；hY : Measurable[m'] Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.CondIndepFun.symm`：∀ {Ω : Type u_1} {β : Type u_3} {β'
 : Type u_4} {m' mΩ : MeasurableSpace Ω} [inst : StandardBorelSpace Ω]   {hm' : 
m' ≤ mΩ} {μ : MeasureTheo…
· 使用引理 `ProbabilityTheory.condIndepFun_of_measurable_left`：condIndepFun_of_measu
rable_left {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'} {X : Ω -> β} {Y :
 Ω -> β'} (hX : Measurable[m'] X) (hY :…
-/
lemma condIndepFun_of_measurable_right {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    {X : Ω → β} {Y : Ω → β'} (hX : Measurable X) (hY : Measurable[m'] Y) :
    CondIndepFun m' hm' X Y μ :=
  (condIndepFun_of_measurable_left hY hX).symm
/-
**ProbabilityTheory.condIndepFun_self_left** 是 Mathlib 中的一个引理，位于命名空间 `Probabilit
yTheory`。
形式化陈述：condIndepFun_self_left {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
 {X : Ω -> β} {Z : Ω -> β'} (hX : Measurable X) (hZ : Measurable Z) : Z ⟂ᵢ[Z, hZ
; μ] X
参数：hX : Measurable X；hZ : Measurable Z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.condIndepFun_of_measurable_left`：condIndepFun_of_measu
rable_left {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'} {X : Ω -> β} {Y :
 Ω -> β'} (hX : Measurable[m'] X) (hY :…
· 使用定理 `Measurable.comap_le`：∀ {α : Type u_1} {β : Type u_2} {m₁ : MeasurableSpa
ce α} {m₂ : MeasurableSpace β} {f : α → β},   Measurable f → MeasurableSpace.com
ap f m₂ ≤…
· 使用定理 `comap_measurable`：comap_measurable {m : MeasurableSpace β} (f : α -> β) 
: Measurable[m.comap f] f
-/
lemma condIndepFun_self_left {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    {X : Ω → β} {Z : Ω → β'} (hX : Measurable X) (hZ : Measurable Z) :
    Z ⟂ᵢ[Z, hZ; μ] X :=
  condIndepFun_of_measurable_left (comap_measurable Z) hX
/-
**ProbabilityTheory.condIndepFun_self_right** 是 Mathlib 中的一个引理，位于命名空间 `Probabili
tyTheory`。
形式化陈述：condIndepFun_self_right {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'
} {X : Ω -> β} {Z : Ω -> β'} (hX : Measurable X) (hZ : Measurable Z) : X ⟂ᵢ[Z, h
Z; μ] Z
参数：hX : Measurable X；hZ : Measurable Z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.condIndepFun_of_measurable_right`：condIndepFun_of_meas
urable_right {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'} {X : Ω -> β} {Y
 : Ω -> β'} (hX : Measurable X) (hY : Me…
· 使用定理 `Measurable.comap_le`：∀ {α : Type u_1} {β : Type u_2} {m₁ : MeasurableSpa
ce α} {m₂ : MeasurableSpace β} {f : α → β},   Measurable f → MeasurableSpace.com
ap f m₂ ≤…
· 使用定理 `comap_measurable`：comap_measurable {m : MeasurableSpace β} (f : α -> β) 
: Measurable[m.comap f] f
-/
lemma condIndepFun_self_right {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    {X : Ω → β} {Z : Ω → β'} (hX : Measurable X) (hZ : Measurable Z) :
    X ⟂ᵢ[Z, hZ; μ] Z :=
  condIndepFun_of_measurable_right hX (comap_measurable Z)

/-- Two random variables are conditionally independent iff they satisfy the almost sure equality
of conditional expectations `μ⟦f ⁻¹' s ∩ g ⁻¹' t | m'⟧ =ᵐ[μ] μ⟦f ⁻¹' s | m'⟧ * μ⟦g ⁻¹' t | m'⟧`
for all measurable sets `s` and `t` (see `condIndepFun_iff_condExp_inter_preimage_eq_mul`).
Here, this is phrased with Markov kernels associated to the conditional expectations, and the
almost sure equality is expressed as equality of the composition-product with the measure, which is
equivalent to a.e. equality. See `condIndepFun_iff_map_prod_eq_prod_map_map` for the a.e. equality
version with kernels.

For a random variable `f`, `(condExpKernel μ m').map f` is the law of the conditional expectation
of `f` given `m'`: almost surely, `(condExpKernel μ m').map f ω s = μ⟦f ⁻¹' s | m'⟧ ω`. -/
/-
**ProbabilityTheory.condIndepFun_iff_compProd_map_prod_eq_compProd_prod_map_map*
* 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory`。
形式化陈述：condIndepFun_iff_compProd_map_prod_eq_compProd_prod_map_map {mβ : Measurab
leSpace β} {mβ' : MeasurableSpace β'} (hf : Measurable f) (hg : Measurable g) : 
CondIndepFun m' hm' f g μ ↔ (μ.trim hm') otimesₘ (condExpKernel μ m').map (fun ω
 => (f ω, g ω)) = (μ.trim hm') otimesₘ ((condExpKernel μ m').map f ×ₖ (condExpKe
rnel μ m').map g)
参数：hf : Measurable f；hg : Measurable g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.indepFun_iff_compProd_map_prod_eq_compProd_prod
_map_map`：indepFun_iff_compProd_map_prod_eq_compProd_prod_map_map {mβ : Measurab
leSpace β} {mγ : MeasurableSpace γ} [IsFiniteMeasure μ] [IsFiniteKerne…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.instIsMarkovKernelCondExpKernel`：∀ {Ω : Type u_1} {m :
 MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [inst : StandardBorelSpace Ω]   {μ 
: MeasureTheory.Measure Ω} [inst_1 : Me…

--- 原说明 ---
Two random variables are conditionally independent iff they satisfy the almost s
ure equality
of conditional expectations `μ⟦f ⁻¹' s ∩ g ⁻¹' t | m'⟧ =ᵐ[μ] μ⟦f ⁻¹' s | m'⟧ * μ
⟦g ⁻¹' t | m'⟧`
for all measurable sets `s` and `t` (see `condIndepFun_iff_condExp_inter_preimag
e_eq_mul`).
Here, this is phrased with Markov kernels associated to the conditional expectat
ions, and the
almost sure equality is expressed as equality of the composition-product with th
e measure, which is
equivalent to a.e. equality. See `condIndepFun_iff_map_prod_eq_prod_map_map` for
 the a.e. equality
version with kernels.

For a random variable `f`, `(condExpKernel μ m').map f` is the law of the condit
ional expectation
of `f` given `m'`: almost surely, `(condExpKernel μ m').map f ω s = μ⟦f ⁻¹' s | 
m'⟧ ω`.
-/
theorem condIndepFun_iff_compProd_map_prod_eq_compProd_prod_map_map
    {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'} (hf : Measurable f) (hg : Measurable g) :
    CondIndepFun m' hm' f g μ
      ↔ (μ.trim hm') ⊗ₘ (condExpKernel μ m').map (fun ω ↦ (f ω, g ω))
        = (μ.trim hm') ⊗ₘ ((condExpKernel μ m').map f ×ₖ (condExpKernel μ m').map g) :=
  Kernel.indepFun_iff_compProd_map_prod_eq_compProd_prod_map_map hf hg

/-- Two random variables are conditionally independent iff they satisfy the almost sure equality
of conditional expectations `μ⟦f ⁻¹' s ∩ g ⁻¹' t | m'⟧ =ᵐ[μ] μ⟦f ⁻¹' s | m'⟧ * μ⟦g ⁻¹' t | m'⟧`
for all measurable sets `s` and `t` (see `condIndepFun_iff_condExp_inter_preimage_eq_mul`).
Here, this is phrased with Markov kernels associated to the conditional expectations.

For a random variable `f`, `(condExpKernel μ m').map f` is the law of the conditional expectation
of `f` given `m'`: almost surely, `(condExpKernel μ m').map f ω s = μ⟦f ⁻¹' s | m'⟧ ω`. -/
/-
**ProbabilityTheory.condIndepFun_iff_map_prod_eq_prod_map_map** 是 Mathlib 中的一个定理
，位于命名空间 `ProbabilityTheory`。
形式化陈述：condIndepFun_iff_map_prod_eq_prod_map_map {mβ : MeasurableSpace β} {mβ' : 
MeasurableSpace β'} [CountableOrCountablyGenerated Ω (β × β')] (hf : Measurable 
f) (hg : Measurable g) : CondIndepFun m' hm' f g μ ↔ (condExpKernel μ m').map (f
un ω => (f ω, g ω)) =ᵐ[μ.trim hm'] (condExpKernel μ m').map f ×ₖ (condExpKernel 
μ m').map g
参数：β × β'；hf : Measurable f；hg : Measurable g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.condIndepFun_iff_compProd_map_prod_eq_compProd_prod_ma
p_map`：condIndepFun_iff_compProd_map_prod_eq_compProd_prod_map_map {mβ : Measura
bleSpace β} {mβ' : MeasurableSpace β'} (hf : Measurable f) (hg : Me…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.Kernel.compProd_eq_iff`：compProd_eq_iff [IsFiniteMeasu
re μ] [IsFiniteKernel κ] [IsFiniteKernel η] : μ otimesₘ κ = μ otimesₘ η ↔ κ =ᵐ[μ
] η
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.map`：∀ {α : Type u_1} {β : Type 
u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ : Me
asurableSpace γ} (κ : Probability…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.instIsMarkovKernelCondExpKernel`：∀ {Ω : Type u_1} {m :
 MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [inst : StandardBorelSpace Ω]   {μ 
: MeasureTheory.Measure Ω} [inst_1 : Me…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.prod`：∀ {α : Type u_1} {β : Type
 u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ : M
easurableSpace γ} (κ : Probability…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Two random variables are conditionally independent iff they satisfy the almost s
ure equality
of conditional expectations `μ⟦f ⁻¹' s ∩ g ⁻¹' t | m'⟧ =ᵐ[μ] μ⟦f ⁻¹' s | m'⟧ * μ
⟦g ⁻¹' t | m'⟧`
for all measurable sets `s` and `t` (see `condIndepFun_iff_condExp_inter_preimag
e_eq_mul`).
Here, this is phrased with Markov kernels associated to the conditional expectat
ions.

For a random variable `f`, `(condExpKernel μ m').map f` is the law of the condit
ional expectation
of `f` given `m'`: almost surely, `(condExpKernel μ m').map f ω s = μ⟦f ⁻¹' s | 
m'⟧ ω`.
-/
theorem condIndepFun_iff_map_prod_eq_prod_map_map
    {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'} [CountableOrCountablyGenerated Ω (β × β')]
    (hf : Measurable f) (hg : Measurable g) :
    CondIndepFun m' hm' f g μ
      ↔ (condExpKernel μ m').map (fun ω ↦ (f ω, g ω))
        =ᵐ[μ.trim hm'] (condExpKernel μ m').map f ×ₖ (condExpKernel μ m').map g := by
  rw [condIndepFun_iff_compProd_map_prod_eq_compProd_prod_map_map hf hg, ← Kernel.compProd_eq_iff]

/-- Two random variables are conditionally independent with respect to `m'` iff the law of
`(id, f, g)` under `μ`, in which the identity is to the space with σ-algebra `m'`, can be written
as a product involving the conditional expectations of `f` and `g` given `m'`.

For a random variable `f`, `(condExpKernel μ m').map f` is the law of the conditional expectation
of `f` given `m'`: almost surely, `(condExpKernel μ m').map f ω s = μ⟦f ⁻¹' s | m'⟧ ω`. -/
/-
**ProbabilityTheory.condIndepFun_iff_map_prod_eq_prod_comp_trim** 是 Mathlib 中的一个
引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：condIndepFun_iff_map_prod_eq_prod_comp_trim {mβ : MeasurableSpace β} {mβ' 
: MeasurableSpace β'} (hf : Measurable f) (hg : Measurable g) : CondIndepFun m' 
hm' f g μ ↔ @Measure.map _ _ _ (m'.prod _) (fun ω => (ω, f ω, g ω)) μ = (Kernel.
id ×ₖ ((condExpKernel μ m').map f ×ₖ (condExpKernel μ m').map g)) ∘ₘ μ.trim hm'
参数：hf : Measurable f；hg : Measurable g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.condIndepFun_iff_compProd_map_prod_eq_compProd_prod_ma
p_map`：condIndepFun_iff_compProd_map_prod_eq_compProd_prod_map_map {mβ : Measura
bleSpace β} {mβ' : MeasurableSpace β'} (hf : Measurable f) (hg : Me…
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.Measure.compProd_map`：compProd_map [SFinite μ] [IsSFiniteK
ernel κ] {f : β -> γ} (hf : Measurable f) : μ otimesₘ (κ.map f) = (μ otimesₘ κ).
map (Prod.map id f)
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.instIsMarkovKernelCondExpKernel`：∀ {Ω : Type u_1} {m :
 MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [inst : StandardBorelSpace Ω]   {μ 
: MeasureTheory.Measure Ω} [inst_1 : Me…
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
· 使用引理 `ProbabilityTheory.compProd_trim_condExpKernel`：compProd_trim_condExpKern
el (hm : m <= mΩ) : (μ.trim hm) otimesₘ condExpKernel μ m = @Measure.map Ω (Ω × 
Ω) mΩ (m.prod mΩ) Function.diag μ
· 使用定理 `MeasureTheory.Measure.map_map`：map_map {g : β -> γ} {f : α -> β} (hg : M
easurable g) (hf : Measurable f) : (μ.map f).map g = μ.map (g ∘ f)
· 使用定理 `Measurable.prodMap`：Measurable.prodMap [MeasurableSpace δ] {f : α -> β} 
{g : γ -> δ} (hf : Measurable f) (hg : Measurable g) : Measurable (Prod.map f g)
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
· 使用定理 `Measurable.mono`：Measurable.mono {ma ma' : MeasurableSpace α} {mb mb' : 
MeasurableSpace β} {f : α -> β} (hf : @Measurable α β ma mb f) (ha : ma <= ma') 
(hb :…
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用引理 `MeasureTheory.Measure.compProd_eq_comp_prod`：compProd_eq_comp_prod (μ : 
Measure α) [SFinite μ] (κ : Kernel α β) [IsSFiniteKernel κ] : μ otimesₘ κ = (Ker
nel.id ×ₖ κ) ∘ₘ μ
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.prod`：∀ {α : Type u_1} {β : Typ
e u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ : 
MeasurableSpace γ} (κ : Probability…

--- 原说明 ---
Two random variables are conditionally independent with respect to `m'` iff the 
law of
`(id, f, g)` under `μ`, in which the identity is to the space with σ-algebra `m'
`, can be written
as a product involving the conditional expectations of `f` and `g` given `m'`.

For a random variable `f`, `(condExpKernel μ m').map f` is the law of the condit
ional expectation
of `f` given `m'`: almost surely, `(condExpKernel μ m').map f ω s = μ⟦f ⁻¹' s | 
m'⟧ ω`.
-/
lemma condIndepFun_iff_map_prod_eq_prod_comp_trim
    {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'} (hf : Measurable f) (hg : Measurable g) :
    CondIndepFun m' hm' f g μ
      ↔ @Measure.map _ _ _ (m'.prod _) (fun ω ↦ (ω, f ω, g ω)) μ
        = (Kernel.id ×ₖ ((condExpKernel μ m').map f ×ₖ (condExpKernel μ m').map g))
          ∘ₘ μ.trim hm' := by
  rw [condIndepFun_iff_compProd_map_prod_eq_compProd_prod_map_map hf hg]
  congr!
  · rw [Measure.compProd_map (by fun_prop), compProd_trim_condExpKernel]
    exact Measure.map_map (by fun_prop) ((measurable_id.mono le_rfl hm').prodMk measurable_id)
  · rw [Measure.compProd_eq_comp_prod]

/-- Two random variables `f, g` are conditionally independent given a third `k` iff the
joint distribution of `k, f, g` factors into a product of their conditional distributions
given `k`. -/
/-
**ProbabilityTheory.condIndepFun_iff_map_prod_eq_prod_condDistrib_prod_condDistr
ib** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory`。
形式化陈述：condIndepFun_iff_map_prod_eq_prod_condDistrib_prod_condDistrib {γ : Type*}
 {mγ : MeasurableSpace γ} {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'} [S
tandardBorelSpace β] [Nonempty β] [StandardBorelSpace β'] [Nonempty β'] (hf : Me
asurable f) (hg : Measurable g) {k : Ω -> γ} (hk : Measurable k) : f ⟂ᵢ[k, hk; μ
] g ↔ μ.map (fun ω => (k ω, f ω, g ω)) = (Kernel.id ×ₖ (condDistrib f k μ ×ₖ con
dDistrib g k μ)) ∘ₘ μ.map k
参数：hf : Measurable f；hg : Measurable g；hk : Measurable k。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comap_le`：∀ {α : Type u_1} {β : Type u_2} {m₁ : MeasurableSpa
ce α} {m₂ : MeasurableSpace β} {f : α → β},   Measurable f → MeasurableSpace.com
ap f m₂ ≤…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.condIndepFun_iff_map_prod_eq_prod_comp_trim`：condIndep
Fun_iff_map_prod_eq_prod_comp_trim {mβ : MeasurableSpace β} {mβ' : MeasurableSpa
ce β'} (hf : Measurable f) (hg : Measurable g) : Co…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.Measure.isFiniteMeasure_map`：∀ {α : Type u_1} {β : Type u_
2} [mβ : MeasurableSpace β] {m : MeasurableSpace α} (μ : MeasureTheory.Measure α
)   [MeasureTheory.IsFiniteMeas…
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
· 使用定理 `MeasurableSet.prod`：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace
 α} {mβ : MeasurableSpace β} {s : Set α} {t : Set β},   MeasurableSet s → Measur
ableSet …
· 使用定理 `Measurable.mono`：Measurable.mono {ma ma' : MeasurableSpace α} {mb mb' : 
MeasurableSpace β} {f : α -> β} (hf : @Measurable α β ma mb f) (ha : ma <= ma') 
(hb :…
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.Measure.bind_apply`：bind_apply {m : Measure α} {f : α -> M
easure β} {s : Set β} (hs : MeasurableSet s) (hf : AEMeasurable f m) : bind m f 
s = ∫⁻ a, f a s ∂m
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用引理 `ProbabilityTheory.Kernel.measurable`：measurable (κ : Kernel α β) : Measu
rable κ
· 使用定理 `MeasureTheory.lintegral_map`：lintegral_map {f : β -> Real>=0∞} {g : α ->
 β} (hf : Measurable f) (hg : Measurable g) : ∫⁻ a, f a ∂map g μ = ∫⁻ a, f (g a)
 ∂μ
· 使用定理 `ProbabilityTheory.Kernel.measurable_coe`：∀ {α : Type u_1} {β : Type u_2}
 {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (κ : ProbabilityTheory.Kernel
 α β)   {s : Set β}, Measurab…
· 使用定理 `MeasureTheory.lintegral_trim`：lintegral_trim {μ : Measure α} (hm : m <= 
m0) {f : α -> Real>=0∞} (hf : Measurable[m] f) : ∫⁻ a, f a ∂μ.trim hm = ∫⁻ a, f 
a ∂μ
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `ProbabilityTheory.condDistrib_apply_ae_eq_condExpKernel_map`：condDistrib
_apply_ae_eq_condExpKernel_map {β γ : Type*} {mβ : MeasurableSpace β} {mγ : Meas
urableSpace γ} [StandardBorelSpace β] [Nonempty β…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `ProbabilityTheory.Kernel.prod_apply_prod`：prod_apply_prod {κ : Kernel α 
β} {η : Kernel α γ} [IsSFiniteKernel κ] [IsSFiniteKernel η] {s : Set β} {t : Set
 γ} {a : α} : (κ ×ₖ η) a (s ×ˢ…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.Kernel.instIsMarkovKernelId`：∀ {α : Type u_1} {mα : Me
asurableSpace α}, ProbabilityTheory.IsMarkovKernel ProbabilityTheory.Kernel.id
（共 39 条，此处仅展示前 30 条）

--- 原说明 ---
Two random variables `f, g` are conditionally independent given a third `k` iff 
the
joint distribution of `k, f, g` factors into a product of their conditional dist
ributions
given `k`.
-/
theorem condIndepFun_iff_map_prod_eq_prod_condDistrib_prod_condDistrib
    {γ : Type*} {mγ : MeasurableSpace γ} {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    [StandardBorelSpace β] [Nonempty β] [StandardBorelSpace β'] [Nonempty β']
    (hf : Measurable f) (hg : Measurable g) {k : Ω → γ} (hk : Measurable k) :
    f ⟂ᵢ[k, hk; μ] g ↔
      μ.map (fun ω ↦ (k ω, f ω, g ω)) =
        (Kernel.id ×ₖ (condDistrib f k μ ×ₖ condDistrib g k μ)) ∘ₘ μ.map k := by
  rw [condIndepFun_iff_map_prod_eq_prod_comp_trim hf hg]
  simp_rw [Measure.ext_prod₃_iff]
  have hk_meas {s : Set γ} (hs : MeasurableSet s) : MeasurableSet[mγ.comap k] (k ⁻¹' s) :=
    ⟨s, hs, rfl⟩
  have h_left {s : Set γ} {t : Set β} {u : Set β'} (hs : MeasurableSet s) (ht : MeasurableSet t)
      (hu : MeasurableSet u) :
      (μ.map (fun ω ↦ (k ω, f ω, g ω))) (s ×ˢ t ×ˢ u) =
        (@Measure.map _ _ _ ((mγ.comap k).prod inferInstance)
          (fun ω ↦ (ω, f ω, g ω)) μ) ((k ⁻¹' s) ×ˢ t ×ˢ u) := by
    rw [Measure.map_apply (by fun_prop) (hs.prod (ht.prod hu)),
      Measure.map_apply _ ((hk_meas hs).prod (ht.prod hu))]
    · simp [Set.mk_preimage_prod]
    · exact (measurable_id.mono le_rfl hk.comap_le).prodMk (by fun_prop)
  have h_right {s : Set γ} {t : Set β} {u : Set β'} (hs : MeasurableSet s) (ht : MeasurableSet t)
      (hu : MeasurableSet u) :
      ((Kernel.id ×ₖ (condDistrib f k μ ×ₖ condDistrib g k μ)) ∘ₘ μ.map k) (s ×ˢ t ×ˢ u) =
        ((Kernel.id ×ₖ
          ((condExpKernel μ (mγ.comap k)).map f ×ₖ (condExpKernel μ (mγ.comap k)).map g)) ∘ₘ
        μ.trim hk.comap_le) ((k ⁻¹' s) ×ˢ t ×ˢ u) := by
    rw [Measure.bind_apply ((hk_meas hs).prod (ht.prod hu)) (by fun_prop),
      Measure.bind_apply (hs.prod (ht.prod hu)) (by fun_prop), lintegral_map ?_ (by fun_prop),
      lintegral_trim]
    rotate_left
    · exact Kernel.measurable_coe _ ((hk_meas hs).prod (ht.prod hu))
    · exact Kernel.measurable_coe _ (hs.prod (ht.prod hu))
    refine lintegral_congr_ae ?_
    filter_upwards [condDistrib_apply_ae_eq_condExpKernel_map hf hk ht,
      condDistrib_apply_ae_eq_condExpKernel_map hg hk hu] with a haX haT
    simp only [Kernel.prod_apply_prod, Kernel.id_apply, Measure.dirac_apply' _ hs]
    rw [@Measure.dirac_apply' _ (mγ.comap k) _ _ (hk_meas hs)]
    congr
  refine ⟨fun h s t u hs ht hu ↦ ?_, fun h ↦ ?_⟩
  · convert! h (hk_meas hs) ht hu
    · exact h_left hs ht hu
    · exact h_right hs ht hu
  · rintro - t u ⟨s, hs, rfl⟩ ht hu
    convert! h hs ht hu
    · exact (h_left hs ht hu).symm
    · exact (h_right hs ht hu).symm

/-- Two random variables `f, g` are conditionally independent given a third `k` iff the
conditional distribution of `f` given `k` and `g` is equal to the conditional distribution of `f`
given `k`. -/
/-
**ProbabilityTheory.condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight** 是 Math
lib 中的一个定理，位于命名空间 `ProbabilityTheory`。
形式化陈述：condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight {γ : Type*} {mγ : Meas
urableSpace γ} {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'} [StandardBore
lSpace β] [Nonempty β] [StandardBorelSpace β'] [Nonempty β'] (hf : Measurable f)
 (hg : Measurable g) {k : Ω -> γ} (hk : Measurable k) : g ⟂ᵢ[k, hk; μ] f ↔ condD
istrib f (fun ω => (k ω, g ω)) μ =ᵐ[μ.map (fun ω => (k ω, g ω))] (condDistrib f 
k μ).prodMkRight _
参数：hf : Measurable f；hg : Measurable g；hk : Measurable k。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comap_le`：∀ {α : Type u_1} {β : Type u_2} {m₁ : MeasurableSpa
ce α} {m₂ : MeasurableSpace β} {f : α → β},   Measurable f → MeasurableSpace.com
ap f m₂ ≤…
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.condDistrib_ae_eq_iff_measure_eq_compProd`：condDistrib
_ae_eq_iff_measure_eq_compProd (X : α -> β) (hY : AEMeasurable Y μ) (κ : Kernel 
β Ω) [IsFiniteKernel κ] : (condDistrib Y X μ =ᵐ[μ…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.prodMkRight`：∀ {α : Type u_1} {β
 : Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   
{mγ : MeasurableSpace γ} (κ : Probability…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.instIsMarkovKernelCondDistrib`：∀ {α : Type u_1} {β : T
ype u_2} {Ω : Type u_3} [inst : MeasurableSpace Ω] [inst_1 : StandardBorelSpace 
Ω]   [inst_2 : Nonempty Ω] {mα : Meas…
· 使用定理 `ProbabilityTheory.condIndepFun_iff_map_prod_eq_prod_condDistrib_prod_con
dDistrib`：condIndepFun_iff_map_prod_eq_prod_condDistrib_prod_condDistrib {γ : Ty
pe*} {mγ : MeasurableSpace γ} {mβ : MeasurableSpace β} {mβ' : Measurab…
· 使用引理 `MeasureTheory.Measure.compProd_eq_comp_prod`：compProd_eq_comp_prod (μ : 
Measure α) [SFinite μ] (κ : Kernel α β) [IsSFiniteKernel κ] : μ otimesₘ κ = (Ker
nel.id ×ₖ κ) ∘ₘ μ
· 使用定理 `MeasureTheory.Measure.instSFiniteMap`：∀ {α : Type u_2} {β : Type u_3} {m
0 : MeasurableSpace α} [inst : MeasurableSpace β] (μ : MeasureTheory.Measure α) 
  (f : α → β) [MeasureTheo…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.prodMkRight`：∀ {α : Type u_1} {
β : Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}  
 {mγ : MeasurableSpace γ} (κ : Probability…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用引理 `MeasureTheory.Measure.comp_assoc`：comp_assoc {η : Kernel β γ} : η ∘ₘ (κ 
∘ₘ μ) = (η ∘ₖ κ) ∘ₘ μ
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)
· 使用引理 `ProbabilityTheory.Kernel.prod_prodMkRight_comp_deterministic_prod`：prod_
prodMkRight_comp_deterministic_prod {β' ε : Type*} {mβ' : MeasurableSpace β'} {m
ε : MeasurableSpace ε} (κ : Kernel γ β) [IsSFiniteKerne…
· 使用定理 `ProbabilityTheory.Kernel.isFiniteKernel_of_isFiniteKernel_snd`：∀ {α : Ty
pe u_1} {β : Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β}   {mγ : MeasurableSpace γ} {κ : Probability…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.snd`：∀ {α : Type u_1} {β : Type 
u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {mγ : Me
asurableSpace γ} (κ : Probability…
· 使用定理 `ProbabilityTheory.Kernel.isFiniteKernel_of_isFiniteKernel_fst`：∀ {α : Ty
pe u_1} {β : Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β}   {mγ : MeasurableSpace γ} {κ : Probability…
· 使用定理 `ProbabilityTheory.Kernel.IsZeroOrMarkovKernel.fst`：∀ {α : Type u_1} {β :
 Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {m
γ : MeasurableSpace γ} (κ : Probability…
· 使用定理 `ProbabilityTheory.Kernel.instIsMarkovKernelId`：∀ {α : Type u_1} {mα : Me
asurableSpace α}, ProbabilityTheory.IsMarkovKernel ProbabilityTheory.Kernel.id
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ProbabilityTheory.Kernel.id_comp`：∀ {α : Type u_1} {β : Type u_2} {mα : 
MeasurableSpace α} {mβ : MeasurableSpace β} (κ : ProbabilityTheory.Kernel α β), 
  ProbabilityTheory.Ke…
· 使用定理 `ProbabilityTheory.Kernel.comp_id`：∀ {β : Type u_2} {γ : Type u_3} {mβ : 
MeasurableSpace β} {mγ : MeasurableSpace γ} (κ : ProbabilityTheory.Kernel β γ), 
  κ.comp ProbabilityTh…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.Kernel.id.eq_1`：∀ {α : Type u_1} {mα : MeasurableSpace
 α}, ProbabilityTheory.Kernel.id = ProbabilityTheory.Kernel.deterministic id ⋯
（共 39 条，此处仅展示前 30 条）

--- 原说明 ---
Two random variables `f, g` are conditionally independent given a third `k` iff 
the
conditional distribution of `f` given `k` and `g` is equal to the conditional di
stribution of `f`
given `k`.
-/
theorem condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight
    {γ : Type*} {mγ : MeasurableSpace γ} {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    [StandardBorelSpace β] [Nonempty β] [StandardBorelSpace β'] [Nonempty β']
    (hf : Measurable f) (hg : Measurable g) {k : Ω → γ} (hk : Measurable k) :
    g ⟂ᵢ[k, hk; μ] f ↔
      condDistrib f (fun ω ↦ (k ω, g ω)) μ =ᵐ[μ.map (fun ω ↦ (k ω, g ω))]
        (condDistrib f k μ).prodMkRight _ := by
  rw [condDistrib_ae_eq_iff_measure_eq_compProd (μ := μ) _ hf.aemeasurable,
    condIndepFun_iff_map_prod_eq_prod_condDistrib_prod_condDistrib hg hf hk,
    Measure.compProd_eq_comp_prod]
  let e : γ × β' × β ≃ᵐ (γ × β') × β := MeasurableEquiv.prodAssoc.symm
  have h_eq : ((Kernel.id ×ₖ condDistrib g k μ) ×ₖ condDistrib f k μ) ∘ₘ μ.map k =
      (Kernel.id ×ₖ (condDistrib f k μ).prodMkRight _) ∘ₘ μ.map (fun a ↦ (k a, g a)) := by
    calc ((Kernel.id ×ₖ condDistrib g k μ) ×ₖ condDistrib f k μ) ∘ₘ μ.map k
    _ = (Kernel.id ×ₖ (condDistrib f k μ).prodMkRight _) ∘ₘ (μ.map k ⊗ₘ condDistrib g k μ) := by
      rw [Measure.compProd_eq_comp_prod, Measure.comp_assoc]
      congr 2
      have h := Kernel.prod_prodMkRight_comp_deterministic_prod (condDistrib g k μ)
        (condDistrib f k μ) Kernel.id measurable_id
      rw [← Kernel.id] at h
      simpa using h.symm
    _ = (Kernel.id ×ₖ (condDistrib f k μ).prodMkRight _) ∘ₘ μ.map (fun a ↦ (k a, g a)) := by
      rw [compProd_map_condDistrib hg.aemeasurable]
  rw [← h_eq]
  have h1 : μ.map (fun x ↦ ((k x, g x), f x)) = (μ.map (fun a ↦ (k a, g a, f a))).map e := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  have h1_symm : μ.map (fun a ↦ (k a, g a, f a)) =
      (μ.map (fun x ↦ ((k x, g x), f x))).map e.symm := by
    rw [h1, Measure.map_map (by fun_prop) (by fun_prop), MeasurableEquiv.symm_comp_self,
      Measure.map_id]
  have h2 : ((Kernel.id ×ₖ condDistrib g k μ) ×ₖ condDistrib f k μ) ∘ₘ μ.map k =
      ((Kernel.id ×ₖ (condDistrib g k μ ×ₖ condDistrib f k μ)) ∘ₘ μ.map k).map e := by
    rw [← Measure.deterministic_comp_eq_map e.measurable, Measure.comp_assoc]
    congr 2
    unfold e
    rw [Kernel.deterministic_comp_eq_map, Kernel.prodAssoc_symm_prod]
  have h2_symm : (Kernel.id ×ₖ (condDistrib g k μ ×ₖ condDistrib f k μ)) ∘ₘ μ.map k =
      (((Kernel.id ×ₖ condDistrib g k μ) ×ₖ condDistrib f k μ) ∘ₘ μ.map k).map e.symm := by
    rw [h2, Measure.map_map (by fun_prop) (by fun_prop), MeasurableEquiv.symm_comp_self,
      Measure.map_id]
  rw [h1, h2]
  exact ⟨fun h ↦ by rw [h], fun h ↦ by rw [h1_symm, h1, h2_symm, h2, h]⟩

section iCondIndepFun
variable {β : ι → Type*} {m : ∀ i, MeasurableSpace (β i)} {f : ∀ i, Ω → β i}

@[nontriviality]
/-
**ProbabilityTheory.iCondIndepFun.of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Pro
babilityTheory.iCondIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {m' mΩ : MeasurableSpace Ω} [inst : Standa
rdBorelSpace Ω] {hm' : m' ≤ mΩ}   {μ : MeasureTheory.Measure Ω} [inst_1 : Measur
eTheory.IsFiniteMeasure μ] {β : ι → Type u_5}   {m : (i : ι) → MeasurableSpace (
β i)} {f : (i : ι) → Ω → β i} [Subsingleton ι],   ProbabilityTheory.iCondIndepFu
n m' hm' f μ
参数：i : ι；β i；i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.of_subsingleton`：∀ {α : Type u_1} {Ω 
: Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {_mΩ : MeasurableSpace Ω}  
 {κ : ProbabilityTheory.Kernel α Ω} {μ :…
· 使用定理 `ProbabilityTheory.instIsMarkovKernelCondExpKernel`：∀ {Ω : Type u_1} {m :
 MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [inst : StandardBorelSpace Ω]   {μ 
: MeasureTheory.Measure Ω} [inst_1 : Me…
-/
lemma iCondIndepFun.of_subsingleton [Subsingleton ι] : iCondIndepFun m' hm' f μ :=
  Kernel.iIndepFun.of_subsingleton

/-- If `f` is a family of mutually conditionally independent random variables
(`iCondIndepFun m' hm' m f μ`) and `S, T` are two disjoint finite index sets, then the tuple formed
by `f i` for `i ∈ S` is conditionally independent of the tuple `(f i)_i` for `i ∈ T`. -/
/-
**ProbabilityTheory.iCondIndepFun.condIndepFun_finset** 是 Mathlib 中的一个定理，位于命名空间 
`ProbabilityTheory.iCondIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {m' mΩ : MeasurableSpace Ω} [inst : Standa
rdBorelSpace Ω] {hm' : m' ≤ mΩ}   {μ : MeasureTheory.Measure Ω} [inst_1 : Measur
eTheory.IsFiniteMeasure μ] {β : ι → Type u_6}   {m : (i : ι) → MeasurableSpace (
β i)} {f : (i : ι) → Ω → β i} (S T : Finset ι),   Disjoint S T →     Probability
Theory.iCondIndepFun m' hm' f μ →       (∀ (i : ι), Measurable (f i)) →         
ProbabilityTheory.CondIndepFun m' hm' (fun a i => f (↑i) a) (fun a i => f (↑i) a
) μ
参数：i : ι；β i；i : ι；S T : Finset ι；∀ (i : ι), Measurable (f i)；fun a i => f (↑i) 
a；fun a i => f (↑i) a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.indepFun_finset`：∀ {α : Type u_1} {Ω 
: Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω}   {
κ : ProbabilityTheory.Kernel α Ω} {μ : M…

--- 原说明 ---
If `f` is a family of mutually conditionally independent random variables
(`iCondIndepFun m' hm' m f μ`) and `S, T` are two disjoint finite index sets, th
en the tuple formed
by `f i` for `i ∈ S` is conditionally independent of the tuple `(f i)_i` for `i 
∈ T`.
-/
theorem iCondIndepFun.condIndepFun_finset {β : ι → Type*}
    {m : ∀ i, MeasurableSpace (β i)} {f : ∀ i, Ω → β i} (S T : Finset ι) (hST : Disjoint S T)
    (hf_Indep : iCondIndepFun m' hm' f μ) (hf_meas : ∀ i, Measurable (f i)) :
    CondIndepFun m' hm' (fun a (i : S) => f i a) (fun a (i : T) => f i a) μ :=
  Kernel.iIndepFun.indepFun_finset S T hST hf_Indep hf_meas
/-
**ProbabilityTheory.iCondIndepFun.condIndepFun_prodMk** 是 Mathlib 中的一个定理，位于命名空间 
`ProbabilityTheory.iCondIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {m' mΩ : MeasurableSpace Ω} [inst : Standa
rdBorelSpace Ω] {hm' : m' ≤ mΩ}   {μ : MeasureTheory.Measure Ω} [inst_1 : Measur
eTheory.IsFiniteMeasure μ] {β : ι → Type u_6}   {m : (i : ι) → MeasurableSpace (
β i)} {f : (i : ι) → Ω → β i},   ProbabilityTheory.iCondIndepFun m' hm' f μ →   
  (∀ (i : ι), Measurable (f i)) →       ∀ (i j k : ι), i ≠ k → j ≠ k → Probabili
tyTheory.CondIndepFun m' hm' (fun a => (f i a, f j a)) (f k) μ
参数：i : ι；β i；i : ι；∀ (i : ι), Measurable (f i)；i j k : ι；fun a => (f i a, f j a)
；f k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.indepFun_prodMk`：∀ {α : Type u_1} {Ω 
: Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω}   {
κ : ProbabilityTheory.Kernel α Ω} {μ : M…
-/
theorem iCondIndepFun.condIndepFun_prodMk {β : ι → Type*}
    {m : ∀ i, MeasurableSpace (β i)} {f : ∀ i, Ω → β i} (hf_Indep : iCondIndepFun m' hm' f μ)
    (hf_meas : ∀ i, Measurable (f i)) (i j k : ι) (hik : i ≠ k) (hjk : j ≠ k) :
    CondIndepFun m' hm' (fun a => (f i a, f j a)) (f k) μ :=
  Kernel.iIndepFun.indepFun_prodMk hf_Indep hf_meas i j k hik hjk

open Finset in
/-
**ProbabilityTheory.iCondIndepFun.condIndepFun_prodMk_prodMk** 是 Mathlib 中的一个定理，
位于命名空间 `ProbabilityTheory.iCondIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {m' mΩ : MeasurableSpace Ω} [inst : Standa
rdBorelSpace Ω] {hm' : m' ≤ mΩ}   {μ : MeasureTheory.Measure Ω} [inst_1 : Measur
eTheory.IsFiniteMeasure μ] {β : ι → Type u_5}   {m : (i : ι) → MeasurableSpace (
β i)} {f : (i : ι) → Ω → β i},   ProbabilityTheory.iCondIndepFun m' hm' f μ →   
  (∀ (i : ι), Measurable (f i)) →       ∀ (i j k l : ι),         i ≠ k →        
   i ≠ l →             j ≠ k → j ≠ l → ProbabilityTheory.CondIndepFun m' hm' (fu
n a => (f i a, f j a)) (fun a => (f k a, f l a)) μ
参数：i : ι；β i；i : ι；∀ (i : ι), Measurable (f i)；i j k l : ι；fun a => (f i a, f j 
a)；fun a => (f k a, f l a)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s
· 使用定理 `Finset.mem_singleton_self`：mem_singleton_self (a : α) : a in ({a} : Fins
et α)
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
· 使用定理 `measurable_pi_apply`：measurable_pi_apply (a : δ) : Measurable fun f : fo
rall a, X a => f a
· 使用定理 `ProbabilityTheory.Kernel.IndepFun.comp`：∀ {α : Type u_1} {Ω : Type u_2} 
{β : Type u_4} {β' : Type u_5} {γ : Type u_6} {γ' : Type u_7} {mα : MeasurableSp
ace α}   {mΩ : MeasurableSpa…
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.indepFun_finset`：∀ {α : Type u_1} {Ω 
: Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω}   {
κ : ProbabilityTheory.Kernel α Ω} {μ : M…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
-/
lemma iCondIndepFun.condIndepFun_prodMk_prodMk (h_indep : iCondIndepFun m' hm' f μ)
    (hf : ∀ i, Measurable (f i))
    (i j k l : ι) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    CondIndepFun m' hm' (fun a ↦ (f i a, f j a)) (fun a ↦ (f k a, f l a)) μ := by
  classical
  let g (i j : ι) (v : Π x : ({i, j} : Finset ι), β x) : β i × β j :=
    ⟨v ⟨i, mem_insert_self _ _⟩, v ⟨j, mem_insert_of_mem <| mem_singleton_self _⟩⟩
  have hg (i j : ι) : Measurable (g i j) := by fun_prop
  exact (h_indep.indepFun_finset {i, j} {k, l} (by aesop) hf).comp (hg i j) (hg k l)

end iCondIndepFun

section Mul
variable {m : MeasurableSpace β} [Mul β] [MeasurableMul₂ β] {f : ι → Ω → β}

@[to_additive]
/-
**ProbabilityTheory.iCondIndepFun.indepFun_mul_left** 是 Mathlib 中的一个定理，位于命名空间 `P
robabilityTheory.iCondIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {β : Type u_3} {m' mΩ : MeasurableSpace Ω}
 [inst : StandardBorelSpace Ω] {hm' : m' ≤ mΩ}   {μ : MeasureTheory.Measure Ω} [
inst_1 : MeasureTheory.IsFiniteMeasure μ] {m : MeasurableSpace β} [inst_2 : Mul 
β]   [MeasurableMul₂ β] {f : ι → Ω → β},   ProbabilityTheory.iCondIndepFun m' hm
' f μ →     (∀ (i : ι), Measurable (f i)) →       ∀ (i j k : ι), i ≠ k → j ≠ k →
 ProbabilityTheory.CondIndepFun m' hm' (f i * f j) (f k) μ
参数：∀ (i : ι), Measurable (f i)；i j k : ι；f i * f j；f k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.indepFun_mul_left`：∀ {α : Type u_1} {
Ω : Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω}  
 {κ : ProbabilityTheory.Kernel α Ω} {μ : M…
-/
lemma iCondIndepFun.indepFun_mul_left (hf_indep : iCondIndepFun m' hm' f μ)
    (hf_meas : ∀ i, Measurable (f i)) (i j k : ι) (hik : i ≠ k) (hjk : j ≠ k) :
    CondIndepFun m' hm' (f i * f j) (f k) μ :=
  Kernel.iIndepFun.indepFun_mul_left hf_indep hf_meas i j k hik hjk

@[to_additive]
/-
**ProbabilityTheory.iCondIndepFun.indepFun_mul_right** 是 Mathlib 中的一个定理，位于命名空间 `
ProbabilityTheory.iCondIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {β : Type u_3} {m' mΩ : MeasurableSpace Ω}
 [inst : StandardBorelSpace Ω] {hm' : m' ≤ mΩ}   {μ : MeasureTheory.Measure Ω} [
inst_1 : MeasureTheory.IsFiniteMeasure μ] {m : MeasurableSpace β} [inst_2 : Mul 
β]   [MeasurableMul₂ β] {f : ι → Ω → β},   ProbabilityTheory.iCondIndepFun m' hm
' f μ →     (∀ (i : ι), Measurable (f i)) →       ∀ (i j k : ι), i ≠ j → i ≠ k →
 ProbabilityTheory.CondIndepFun m' hm' (f i) (f j * f k) μ
参数：∀ (i : ι), Measurable (f i)；i j k : ι；f i；f j * f k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.indepFun_mul_right`：∀ {α : Type u_1} 
{Ω : Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω} 
  {κ : ProbabilityTheory.Kernel α Ω} {μ : M…
-/
lemma iCondIndepFun.indepFun_mul_right (hf_indep : iCondIndepFun m' hm' f μ)
    (hf_meas : ∀ i, Measurable (f i)) (i j k : ι) (hij : i ≠ j) (hik : i ≠ k) :
    CondIndepFun m' hm' (f i) (f j * f k) μ :=
  Kernel.iIndepFun.indepFun_mul_right hf_indep hf_meas i j k hij hik

@[to_additive]
/-
**ProbabilityTheory.iCondIndepFun.indepFun_mul_mul** 是 Mathlib 中的一个定理，位于命名空间 `Pr
obabilityTheory.iCondIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {β : Type u_3} {m' mΩ : MeasurableSpace Ω}
 [inst : StandardBorelSpace Ω] {hm' : m' ≤ mΩ}   {μ : MeasureTheory.Measure Ω} [
inst_1 : MeasureTheory.IsFiniteMeasure μ] {m : MeasurableSpace β} [inst_2 : Mul 
β]   [MeasurableMul₂ β] {f : ι → Ω → β},   ProbabilityTheory.iCondIndepFun m' hm
' f μ →     (∀ (i : ι), Measurable (f i)) →       ∀ (i j k l : ι), i ≠ k → i ≠ l
 → j ≠ k → j ≠ l → ProbabilityTheory.CondIndepFun m' hm' (f i * f j) (f k * f l)
 μ
参数：∀ (i : ι), Measurable (f i)；i j k l : ι；f i * f j；f k * f l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.indepFun_mul_mul`：∀ {α : Type u_1} {Ω
 : Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω}   
{κ : ProbabilityTheory.Kernel α Ω} {μ : M…
-/
lemma iCondIndepFun.indepFun_mul_mul (hf_indep : iCondIndepFun m' hm' f μ)
    (hf_meas : ∀ i, Measurable (f i))
    (i j k l : ι) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    CondIndepFun m' hm' (f i * f j) (f k * f l) μ :=
  Kernel.iIndepFun.indepFun_mul_mul hf_indep hf_meas i j k l hik hil hjk hjl

end Mul

section Div
variable {m : MeasurableSpace β} [Div β] [MeasurableDiv₂ β] {f : ι → Ω → β}

@[to_additive]
/-
**ProbabilityTheory.iCondIndepFun.indepFun_div_left** 是 Mathlib 中的一个定理，位于命名空间 `P
robabilityTheory.iCondIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {β : Type u_3} {m' mΩ : MeasurableSpace Ω}
 [inst : StandardBorelSpace Ω] {hm' : m' ≤ mΩ}   {μ : MeasureTheory.Measure Ω} [
inst_1 : MeasureTheory.IsFiniteMeasure μ] {m : MeasurableSpace β} [inst_2 : Div 
β]   [MeasurableDiv₂ β] {f : ι → Ω → β},   ProbabilityTheory.iCondIndepFun m' hm
' f μ →     (∀ (i : ι), Measurable (f i)) →       ∀ (i j k : ι), i ≠ k → j ≠ k →
 ProbabilityTheory.CondIndepFun m' hm' (f i / f j) (f k) μ
参数：∀ (i : ι), Measurable (f i)；i j k : ι；f i / f j；f k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.indepFun_div_left`：∀ {α : Type u_1} {
Ω : Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω}  
 {κ : ProbabilityTheory.Kernel α Ω} {μ : M…
-/
lemma iCondIndepFun.indepFun_div_left (hf_indep : iCondIndepFun m' hm' f μ)
    (hf_meas : ∀ i, Measurable (f i)) (i j k : ι) (hik : i ≠ k) (hjk : j ≠ k) :
    CondIndepFun m' hm' (f i / f j) (f k) μ :=
  Kernel.iIndepFun.indepFun_div_left hf_indep hf_meas i j k hik hjk

@[to_additive]
/-
**ProbabilityTheory.iCondIndepFun.indepFun_div_right** 是 Mathlib 中的一个定理，位于命名空间 `
ProbabilityTheory.iCondIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {β : Type u_3} {m' mΩ : MeasurableSpace Ω}
 [inst : StandardBorelSpace Ω] {hm' : m' ≤ mΩ}   {μ : MeasureTheory.Measure Ω} [
inst_1 : MeasureTheory.IsFiniteMeasure μ] {m : MeasurableSpace β} [inst_2 : Div 
β]   [MeasurableDiv₂ β] {f : ι → Ω → β},   ProbabilityTheory.iCondIndepFun m' hm
' f μ →     (∀ (i : ι), Measurable (f i)) →       ∀ (i j k : ι), i ≠ j → i ≠ k →
 ProbabilityTheory.CondIndepFun m' hm' (f i) (f j / f k) μ
参数：∀ (i : ι), Measurable (f i)；i j k : ι；f i；f j / f k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.indepFun_div_right`：∀ {α : Type u_1} 
{Ω : Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω} 
  {κ : ProbabilityTheory.Kernel α Ω} {μ : M…
-/
lemma iCondIndepFun.indepFun_div_right (hf_indep : iCondIndepFun m' hm' f μ)
    (hf_meas : ∀ i, Measurable (f i)) (i j k : ι) (hij : i ≠ j) (hik : i ≠ k) :
    CondIndepFun m' hm' (f i) (f j / f k) μ :=
  Kernel.iIndepFun.indepFun_div_right hf_indep hf_meas i j k hij hik

@[to_additive]
/-
**ProbabilityTheory.iCondIndepFun.indepFun_div_div** 是 Mathlib 中的一个定理，位于命名空间 `Pr
obabilityTheory.iCondIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {β : Type u_3} {m' mΩ : MeasurableSpace Ω}
 [inst : StandardBorelSpace Ω] {hm' : m' ≤ mΩ}   {μ : MeasureTheory.Measure Ω} [
inst_1 : MeasureTheory.IsFiniteMeasure μ] {m : MeasurableSpace β} [inst_2 : Div 
β]   [MeasurableDiv₂ β] {f : ι → Ω → β},   ProbabilityTheory.iCondIndepFun m' hm
' f μ →     (∀ (i : ι), Measurable (f i)) →       ∀ (i j k l : ι), i ≠ k → i ≠ l
 → j ≠ k → j ≠ l → ProbabilityTheory.CondIndepFun m' hm' (f i / f j) (f k / f l)
 μ
参数：∀ (i : ι), Measurable (f i)；i j k l : ι；f i / f j；f k / f l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.indepFun_div_div`：∀ {α : Type u_1} {Ω
 : Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω}   
{κ : ProbabilityTheory.Kernel α Ω} {μ : M…
-/
lemma iCondIndepFun.indepFun_div_div (hf_indep : iCondIndepFun m' hm' f μ)
    (hf_meas : ∀ i, Measurable (f i))
    (i j k l : ι) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    CondIndepFun m' hm' (f i / f j) (f k / f l) μ :=
  Kernel.iIndepFun.indepFun_div_div hf_indep hf_meas i j k l hik hil hjk hjl

end Div

section CommMonoid
variable {m : MeasurableSpace β} [CommMonoid β] [MeasurableMul₂ β] {f : ι → Ω → β}

@[to_additive]
/-
**ProbabilityTheory.iCondIndepFun.condIndepFun_finsetProd_of_notMem** 是 Mathlib 
中的一个定理，位于命名空间 `ProbabilityTheory.iCondIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {β : Type u_3} {m' mΩ : MeasurableSpace Ω}
 [inst : StandardBorelSpace Ω] {hm' : m' ≤ mΩ}   {μ : MeasureTheory.Measure Ω} [
inst_1 : MeasureTheory.IsFiniteMeasure μ] {m : MeasurableSpace β}   [inst_2 : Co
mmMonoid β] [MeasurableMul₂ β] {f : ι → Ω → β},   ProbabilityTheory.iCondIndepFu
n m' hm' f μ →     (∀ (i : ι), Measurable (f i)) →       ∀ {s : Finset ι} {i : ι
}, i ∉ s → ProbabilityTheory.CondIndepFun m' hm' (∏ j ∈ s, f j) (f i) μ
参数：∀ (i : ι), Measurable (f i)；∏ j ∈ s, f j；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.indepFun_finsetProd_of_notMem`：∀ {α :
 Type u_1} {Ω : Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {mΩ : Measurab
leSpace Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ : M…
-/
theorem iCondIndepFun.condIndepFun_finsetProd_of_notMem
    (hf_Indep : iCondIndepFun m' hm' f μ) (hf_meas : ∀ i, Measurable (f i))
    {s : Finset ι} {i : ι} (hi : i ∉ s) :
    CondIndepFun m' hm' (∏ j ∈ s, f j) (f i) μ :=
  Kernel.iIndepFun.indepFun_finsetProd_of_notMem hf_Indep hf_meas hi

@[deprecated (since := "2026-04-08")]
alias iCondIndepFun.condIndepFun_finset_sum_of_notMem :=
  iCondIndepFun.condIndepFun_finsetSum_of_notMem

@[to_additive existing, deprecated (since := "2026-04-08")]
alias iCondIndepFun.condIndepFun_finset_prod_of_notMem :=
  iCondIndepFun.condIndepFun_finsetProd_of_notMem

@[to_additive]
/-
**ProbabilityTheory.iCondIndepFun.condIndepFun_prod_range_succ** 是 Mathlib 中的一个定
理，位于命名空间 `ProbabilityTheory.iCondIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {β : Type u_3} {m' mΩ : MeasurableSpace Ω} [inst : Standa
rdBorelSpace Ω] {hm' : m' ≤ mΩ}   {μ : MeasureTheory.Measure Ω} [inst_1 : Measur
eTheory.IsFiniteMeasure μ] {m : MeasurableSpace β}   [inst_2 : CommMonoid β] [Me
asurableMul₂ β] {f : ℕ → Ω → β},   ProbabilityTheory.iCondIndepFun m' hm' f μ → 
    (∀ (i : ℕ), Measurable (f i)) → ∀ (n : ℕ), ProbabilityTheory.CondIndepFun m'
 hm' (∏ j ∈ Finset.range n, f j) (f n) μ
参数：∀ (i : ℕ), Measurable (f i)；n : ℕ；∏ j ∈ Finset.range n, f j；f n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.indepFun_prod_range_succ`：∀ {α : Type
 u_1} {Ω : Type u_2} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω} {κ : Prob
abilityTheory.Kernel α Ω}   {μ : MeasureTheory.Me…
-/
theorem iCondIndepFun.condIndepFun_prod_range_succ {f : ℕ → Ω → β}
    (hf_Indep : iCondIndepFun m' hm' f μ) (hf_meas : ∀ i, Measurable (f i)) (n : ℕ) :
    CondIndepFun m' hm' (∏ j ∈ Finset.range n, f j) (f n) μ :=
  Kernel.iIndepFun.indepFun_prod_range_succ hf_Indep hf_meas n

end CommMonoid

/-
**ProbabilityTheory.iCondIndepSet.iCondIndepFun_indicator** 是 Mathlib 中的一个定理，位于命
名空间 `ProbabilityTheory.iCondIndepSet`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {β : Type u_3} {m' mΩ : MeasurableSpace Ω}
 [inst : StandardBorelSpace Ω] {hm' : m' ≤ mΩ}   {μ : MeasureTheory.Measure Ω} [
inst_1 : MeasureTheory.IsFiniteMeasure μ] [inst_2 : Zero β] [inst_3 : One β]   {
m : MeasurableSpace β} {s : ι → Set Ω},   ProbabilityTheory.iCondIndepSet m' hm'
 s μ →     ProbabilityTheory.iCondIndepFun m' hm' (fun n => (s n).indicator fun 
_ω => 1) μ
参数：fun n => (s n).indicator fun _ω => 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepSet.iIndepFun_indicator`：∀ {α : Type u_1}
 {Ω : Type u_2} {ι : Type u_3} {β : Type u_4} {mα : MeasurableSpace α} {mΩ : Mea
surableSpace Ω}   {κ : ProbabilityTheory.Ker…
-/
theorem iCondIndepSet.iCondIndepFun_indicator [Zero β] [One β] {m : MeasurableSpace β}
    {s : ι → Set Ω} (hs : iCondIndepSet m' hm' s μ) :
    iCondIndepFun m' hm' (fun n => (s n).indicator fun _ω => (1 : β)) μ :=
  Kernel.iIndepSet.iIndepFun_indicator hs

end CondIndepFun

end ProbabilityTheory

