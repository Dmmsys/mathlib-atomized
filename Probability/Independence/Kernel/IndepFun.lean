/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Independence.Kernel.Indep
public import Mathlib.MeasureTheory.MeasurableSpace.Pi
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# Independence of random variables with respect to a kernel and a measure

A family of random variables is independent if the corresponding `σ`-algebras are independent.
Independence of families of sets and `σ`-algebras is covered in the `Indep` file.
This file deals with independence of random variables specifically.

Note that we define independence with respect to a kernel and a measure. This notion of independence
is a generalization of both independence and conditional independence.
For conditional independence, `κ` is the conditional kernel `ProbabilityTheory.condExpKernel` and
`μ` is the ambient measure. For (non-conditional) independence, `κ = Kernel.const Unit μ` and the
measure is the Dirac measure on `Unit`.

## Main definition

* `ProbabilityTheory.Kernel.iIndepFun`: independence of a family of functions (random variables).
  Variant for two functions: `ProbabilityTheory.Kernel.IndepFun`.
-/

@[expose] public section

open Set MeasureTheory MeasurableSpace

namespace ProbabilityTheory.Kernel

variable {α Ω ι β β' γ γ' : Type*} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω}
  {κ η : Kernel α Ω} {μ : Measure α} {f : Ω → β} {g : Ω → β'}

section Definitions

/-- A family of functions defined on the same space `Ω` and taking values in possibly different
spaces, each with a measurable space structure, is independent if the family of measurable space
structures they generate on `Ω` is independent. For a function `g` with codomain having measurable
space structure `m`, the generated measurable space structure is `MeasurableSpace.comap g m`. -/
/-
**ProbabilityTheory.Kernel.iIndepFun** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheor
y.Kernel`。
形式化陈述：iIndepFun {β : ι -> Type*} [m : forall x : ι, MeasurableSpace (β x)] (f : 
forall x : ι, Ω -> β x) (κ : Kernel α Ω) (μ : Measure α
参数：β x；f : forall x : ι, Ω -> β x；κ : Kernel α Ω。
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
def iIndepFun {β : ι → Type*} [m : ∀ x : ι, MeasurableSpace (β x)]
    (f : ∀ x : ι, Ω → β x) (κ : Kernel α Ω)
    (μ : Measure α := by volume_tac) : Prop :=
  iIndep (m := fun x ↦ MeasurableSpace.comap (f x) (m x)) κ μ

/-- Two functions are independent if the two measurable space structures they generate are
independent. For a function `f` with codomain having measurable space structure `m`, the generated
measurable space structure is `MeasurableSpace.comap f m`. -/
/-
**ProbabilityTheory.Kernel.IndepFun** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory
.Kernel`。
形式化陈述：IndepFun [mβ : MeasurableSpace β] [mγ : MeasurableSpace γ] (f : Ω -> β) (g
 : Ω -> γ) (κ : Kernel α Ω) (μ : Measure α
参数：f : Ω -> β；g : Ω -> γ；κ : Kernel α Ω。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two functions are independent if the two measurable space structures they genera
te are
independent. For a function `f` with codomain having measurable space structure 
`m`, the generated
measurable space structure is `MeasurableSpace.comap f m`.
-/
def IndepFun [mβ : MeasurableSpace β] [mγ : MeasurableSpace γ]
    (f : Ω → β) (g : Ω → γ) (κ : Kernel α Ω)
    (μ : Measure α := by volume_tac) : Prop :=
  Indep (MeasurableSpace.comap f mβ) (MeasurableSpace.comap g mγ) κ μ

end Definitions

section ByDefinition

variable {β : ι → Type*} {mβ : ∀ i, MeasurableSpace (β i)}
  {_mα : MeasurableSpace α} {m : ι → MeasurableSpace Ω} {_mΩ : MeasurableSpace Ω}
  {κ η : Kernel α Ω} {μ : Measure α}
  {π : ι → Set (Set Ω)} {s : ι → Set Ω} {S : Finset ι} {f : ∀ x : ι, Ω → β x}
  {s1 s2 : Set (Set Ω)} {ι' : Type*} {g : ι' → ι}

/-
**ProbabilityTheory.Kernel.iIndepFun_zero_right** 是 Mathlib 中的一个定理，位于命名空间 `Proba
bilityTheory.Kernel`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {
_mΩ : MeasurableSpace Ω}   {κ : ProbabilityTheory.Kernel α Ω} {β : ι → Type u_10
} {m : (x : ι) → MeasurableSpace (β x)} {f : (x : ι) → Ω → β x},   ProbabilityTh
eory.Kernel.iIndepFun f κ 0
参数：x : ι；β x；x : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
@[simp] lemma iIndepFun_zero_right {β : ι → Type*} {m : ∀ x : ι, MeasurableSpace (β x)}
    {f : ∀ x : ι, Ω → β x} : iIndepFun f κ 0 := by simp [iIndepFun]
/-
**ProbabilityTheory.Kernel.indepFun_zero_right** 是 Mathlib 中的一个定理，位于命名空间 `Probab
ilityTheory.Kernel`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {γ : Type u_6} {_mα : MeasurableSpace α} {
_mΩ : MeasurableSpace Ω}   {κ : ProbabilityTheory.Kernel α Ω} {β : Type u_10} [i
nst : MeasurableSpace β] [inst_1 : MeasurableSpace γ] {f : Ω → β}   {g : Ω → γ},
 ProbabilityTheory.Kernel.IndepFun f g κ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
@[simp] lemma indepFun_zero_right {β} [MeasurableSpace β] [MeasurableSpace γ]
    {f : Ω → β} {g : Ω → γ} : IndepFun f g κ 0 := by simp [IndepFun]
/-
**ProbabilityTheory.Kernel.indepFun_zero_left** 是 Mathlib 中的一个定理，位于命名空间 `Probabi
lityTheory.Kernel`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {γ : Type u_6} {_mα : MeasurableSpace α} {
_mΩ : MeasurableSpace Ω}   {μ : MeasureTheory.Measure α} {β : Type u_10} [inst :
 MeasurableSpace β] [inst_1 : MeasurableSpace γ] {f : Ω → β}   {g : Ω → γ}, Prob
abilityTheory.Kernel.IndepFun f g 0 μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
@[simp] lemma indepFun_zero_left {β} [MeasurableSpace β] [MeasurableSpace γ]
    {f : Ω → β} {g : Ω → γ} : IndepFun f g (0 : Kernel α Ω) μ := by simp [IndepFun]
/-
**ProbabilityTheory.Kernel.iIndepFun_congr** 是 Mathlib 中的一个引理，位于命名空间 `Probabilit
yTheory.Kernel`。
形式化陈述：iIndepFun_congr {β : ι -> Type*} {m : forall x : ι, MeasurableSpace (β x)}
 {f : forall x : ι, Ω -> β x} (h : κ =ᵐ[μ] η) : iIndepFun f κ μ ↔ iIndepFun f η 
μ
参数：β x；h : κ =ᵐ[μ] η。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `ProbabilityTheory.Kernel.iIndep_congr`：iIndep_congr (h : κ =ᵐ[μ] η) : iI
ndep m κ μ ↔ iIndep m η μ
-/
lemma iIndepFun_congr {β : ι → Type*} {m : ∀ x : ι, MeasurableSpace (β x)}
    {f : ∀ x : ι, Ω → β x} (h : κ =ᵐ[μ] η) : iIndepFun f κ μ ↔ iIndepFun f η μ :=
  iIndep_congr h

alias ⟨iIndepFun.congr, _⟩ := iIndepFun_congr
/-
**ProbabilityTheory.Kernel.indepFun_congr** 是 Mathlib 中的一个引理，位于命名空间 `Probability
Theory.Kernel`。
形式化陈述：indepFun_congr {β} [MeasurableSpace β] [MeasurableSpace γ] {f : Ω -> β} {g
 : Ω -> γ} (h : κ =ᵐ[μ] η) : IndepFun f g κ μ ↔ IndepFun f g η μ
参数：h : κ =ᵐ[μ] η。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `ProbabilityTheory.Kernel.indep_congr`：indep_congr {m₁ m₂ : MeasurableSpa
ce Ω} {_mΩ : MeasurableSpace Ω} {κ η : Kernel α Ω} (h : κ =ᵐ[μ] η) : Indep m₁ m₂
 κ μ ↔ Indep m₁ m₂ η μ
-/
lemma indepFun_congr {β} [MeasurableSpace β] [MeasurableSpace γ]
    {f : Ω → β} {g : Ω → γ} (h : κ =ᵐ[μ] η) : IndepFun f g κ μ ↔ IndepFun f g η μ :=
  indep_congr h

alias ⟨IndepFun.congr, _⟩ := indepFun_congr

@[nontriviality, simp]
/-
**ProbabilityTheory.Kernel.iIndepFun.of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `
ProbabilityTheory.Kernel.iIndepFun`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {
_mΩ : MeasurableSpace Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ : MeasureTheory
.Measure α} [Subsingleton ι] {β : ι → Type u_10}   {m : (i : ι) → MeasurableSpac
e (β i)} {f : (i : ι) → Ω → β i} [ProbabilityTheory.IsMarkovKernel κ],   Probabi
lityTheory.Kernel.iIndepFun f κ μ
参数：i : ι；β i；i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma iIndepFun.of_subsingleton [Subsingleton ι] {β : ι → Type*} {m : ∀ i, MeasurableSpace (β i)}
    {f : ∀ i, Ω → β i} [IsMarkovKernel κ] : iIndepFun f κ μ := by
  simp [iIndepFun]
/-
**ProbabilityTheory.Kernel.iIndepFun.iIndep** 是 Mathlib 中的一个定理，位于命名空间 `Probabili
tyTheory.Kernel.iIndepFun`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {β : ι → Type u_8} {mβ : (i
 : ι) → MeasurableSpace (β i)}   {_mα : MeasurableSpace α} {_mΩ : MeasurableSpac
e Ω} {κ : ProbabilityTheory.Kernel α Ω} {μ : MeasureTheory.Measure α}   {f : (x 
: ι) → Ω → β x},   ProbabilityTheory.Kernel.iIndepFun f κ μ →     ProbabilityThe
ory.Kernel.iIndep (fun x => MeasurableSpace.comap (f x) (mβ x)) κ μ
参数：i : ι；β i；x : ι；fun x => MeasurableSpace.comap (f x) (mβ x)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma iIndepFun.iIndep (hf : iIndepFun f κ μ) :
    iIndep (fun x ↦ (mβ x).comap (f x)) κ μ := hf
/-
**ProbabilityTheory.Kernel.iIndepFun.ae_isProbabilityMeasure** 是 Mathlib 中的一个定理，
位于命名空间 `ProbabilityTheory.Kernel.iIndepFun`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {β : ι → Type u_8} {mβ : (i
 : ι) → MeasurableSpace (β i)}   {_mα : MeasurableSpace α} {_mΩ : MeasurableSpac
e Ω} {κ : ProbabilityTheory.Kernel α Ω} {μ : MeasureTheory.Measure α}   {f : (x 
: ι) → Ω → β x},   ProbabilityTheory.Kernel.iIndepFun f κ μ → ∀ᵐ (a : α) ∂μ, Mea
sureTheory.IsProbabilityMeasure (κ a)
参数：i : ι；β i；x : ι；a : α；κ a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndep.ae_isProbabilityMeasure`：∀ {α : Type u_1
} {Ω : Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {m : ι → MeasurableSpa
ce Ω}   {_mΩ : MeasurableSpace Ω} {κ : Probab…
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.iIndep`：∀ {α : Type u_1} {Ω : Type u_
2} {ι : Type u_3} {β : ι → Type u_8} {mβ : (i : ι) → MeasurableSpace (β i)}   {_
mα : MeasurableSpace α} {_mΩ : …
-/
lemma iIndepFun.ae_isProbabilityMeasure (h : iIndepFun f κ μ) :
    ∀ᵐ a ∂μ, IsProbabilityMeasure (κ a) :=
  h.iIndep.ae_isProbabilityMeasure
/-
**ProbabilityTheory.Kernel.iIndepFun.meas_biInter** 是 Mathlib 中的一个定理，位于命名空间 `Pro
babilityTheory.Kernel.iIndepFun`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {β : ι → Type u_8} {mβ : (i
 : ι) → MeasurableSpace (β i)}   {_mα : MeasurableSpace α} {_mΩ : MeasurableSpac
e Ω} {κ : ProbabilityTheory.Kernel α Ω} {μ : MeasureTheory.Measure α}   {s : ι →
 Set Ω} {S : Finset ι} {f : (x : ι) → Ω → β x},   ProbabilityTheory.Kernel.iInde
pFun f κ μ →     (∀ i ∈ S, MeasurableSet (s i)) → ∀ᵐ (a : α) ∂μ, (κ a) (⋂ i ∈ S,
 s i) = ∏ i ∈ S, (κ a) (s i)
参数：i : ι；β i；x : ι；∀ i ∈ S, MeasurableSet (s i)；a : α；κ a；⋂ i ∈ S, s i；κ a；s i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndep.meas_biInter`：∀ {α : Type u_1} {Ω : Type
 u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {m : ι → MeasurableSpace Ω}   {_m
Ω : MeasurableSpace Ω} {κ : Probab…
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.iIndep`：∀ {α : Type u_1} {Ω : Type u_
2} {ι : Type u_3} {β : ι → Type u_8} {mβ : (i : ι) → MeasurableSpace (β i)}   {_
mα : MeasurableSpace α} {_mΩ : …
-/
lemma iIndepFun.meas_biInter (hf : iIndepFun f κ μ)
    (hs : ∀ i, i ∈ S → MeasurableSet[(mβ i).comap (f i)] (s i)) :
    ∀ᵐ a ∂μ, κ a (⋂ i ∈ S, s i) = ∏ i ∈ S, κ a (s i) := hf.iIndep.meas_biInter hs
/-
**ProbabilityTheory.Kernel.iIndepFun.meas_iInter** 是 Mathlib 中的一个定理，位于命名空间 `Prob
abilityTheory.Kernel.iIndepFun`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {β : ι → Type u_8} {mβ : (i
 : ι) → MeasurableSpace (β i)}   {_mα : MeasurableSpace α} {_mΩ : MeasurableSpac
e Ω} {κ : ProbabilityTheory.Kernel α Ω} {μ : MeasureTheory.Measure α}   {s : ι →
 Set Ω} {f : (x : ι) → Ω → β x} [inst : Fintype ι],   ProbabilityTheory.Kernel.i
IndepFun f κ μ →     (∀ (i : ι), MeasurableSet (s i)) → ∀ᵐ (a : α) ∂μ, (κ a) (⋂ 
i, s i) = ∏ i, (κ a) (s i)
参数：i : ι；β i；x : ι；∀ (i : ι), MeasurableSet (s i)；a : α；κ a；⋂ i, s i；κ a；s i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndep.meas_iInter`：∀ {α : Type u_1} {Ω : Type 
u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {m : ι → MeasurableSpace Ω}   {_mΩ
 : MeasurableSpace Ω} {κ : Probab…
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.iIndep`：∀ {α : Type u_1} {Ω : Type u_
2} {ι : Type u_3} {β : ι → Type u_8} {mβ : (i : ι) → MeasurableSpace (β i)}   {_
mα : MeasurableSpace α} {_mΩ : …
-/
lemma iIndepFun.meas_iInter [Fintype ι] (hf : iIndepFun f κ μ)
    (hs : ∀ i, MeasurableSet[(mβ i).comap (f i)] (s i)) :
    ∀ᵐ a ∂μ, κ a (⋂ i, s i) = ∏ i, κ a (s i) := hf.iIndep.meas_iInter hs
/-
**ProbabilityTheory.Kernel.IndepFun.meas_inter** 是 Mathlib 中的一个定理，位于命名空间 `Probab
ilityTheory.Kernel.IndepFun`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {γ : Type u_6} {_mα : MeasurableSpace α} {
_mΩ : MeasurableSpace Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ : MeasureTheory
.Measure α} {β : Type u_10} [mβ : MeasurableSpace β]   [mγ : MeasurableSpace γ] 
{f : Ω → β} {g : Ω → γ},   ProbabilityTheory.Kernel.IndepFun f g κ μ →     ∀ {s 
t : Set Ω}, MeasurableSet s → MeasurableSet t → ∀ᵐ (a : α) ∂μ, (κ a) (s ∩ t) = (
κ a) s * (κ a) t
参数：a : α；κ a；s ∩ t；κ a；κ a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IndepFun.meas_inter {β} [mβ : MeasurableSpace β] [mγ : MeasurableSpace γ]
    {f : Ω → β} {g : Ω → γ} (hfg : IndepFun f g κ μ)
    {s t : Set Ω} (hs : MeasurableSet[mβ.comap f] s) (ht : MeasurableSet[mγ.comap g] t) :
    ∀ᵐ a ∂μ, κ a (s ∩ t) = κ a s * κ a t := hfg _ _ hs ht
/-
**ProbabilityTheory.Kernel.iIndepFun.precomp** 是 Mathlib 中的一个定理，位于命名空间 `Probabil
ityTheory.Kernel.iIndepFun`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {β : ι → Type u_8} {mβ : (i
 : ι) → MeasurableSpace (β i)}   {_mα : MeasurableSpace α} {_mΩ : MeasurableSpac
e Ω} {κ : ProbabilityTheory.Kernel α Ω} {μ : MeasureTheory.Measure α}   {f : (x 
: ι) → Ω → β x} {ι' : Type u_9} {g : ι' → ι},   Function.Injective g →     Proba
bilityTheory.Kernel.iIndepFun f κ μ → ProbabilityTheory.Kernel.iIndepFun (fun i 
=> f (g i)) κ μ
参数：i : ι；β i；x : ι；fun i => f (g i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndep.precomp`：∀ {α : Type u_1} {Ω : Type u_2}
 {ι : Type u_3} {_mα : MeasurableSpace α} {m : ι → MeasurableSpace Ω}   {_mΩ : M
easurableSpace Ω} {κ : Probab…
-/
lemma iIndepFun.precomp (hg : Function.Injective g) (h : iIndepFun f κ μ) :
    iIndepFun (fun i ↦ f (g i)) κ μ :=
  iIndep.precomp hg h
/-
**ProbabilityTheory.Kernel.iIndepFun.of_precomp** 是 Mathlib 中的一个定理，位于命名空间 `Proba
bilityTheory.Kernel.iIndepFun`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {β : ι → Type u_8} {mβ : (i
 : ι) → MeasurableSpace (β i)}   {_mα : MeasurableSpace α} {_mΩ : MeasurableSpac
e Ω} {κ : ProbabilityTheory.Kernel α Ω} {μ : MeasureTheory.Measure α}   {f : (x 
: ι) → Ω → β x} {ι' : Type u_9} {g : ι' → ι},   Function.Surjective g →     Prob
abilityTheory.Kernel.iIndepFun (fun i => f (g i)) κ μ → ProbabilityTheory.Kernel
.iIndepFun f κ μ
参数：i : ι；β i；x : ι；fun i => f (g i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndep.of_precomp`：∀ {α : Type u_1} {Ω : Type u
_2} {ι : Type u_3} {_mα : MeasurableSpace α} {m : ι → MeasurableSpace Ω}   {_mΩ 
: MeasurableSpace Ω} {κ : Probab…
-/
lemma iIndepFun.of_precomp (hg : Function.Surjective g) (h : iIndepFun (fun i ↦ f (g i)) κ μ) :
    iIndepFun f κ μ :=
  iIndep.of_precomp hg h
/-
**ProbabilityTheory.Kernel.iIndepFun_precomp_of_bijective** 是 Mathlib 中的一个引理，位于命
名空间 `ProbabilityTheory.Kernel`。
形式化陈述：iIndepFun_precomp_of_bijective (hg : Function.Bijective g) : iIndepFun (fu
n i => f (g i)) κ μ ↔ iIndepFun f κ μ
参数：hg : Function.Bijective g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.of_precomp`：∀ {α : Type u_1} {Ω : Typ
e u_2} {ι : Type u_3} {β : ι → Type u_8} {mβ : (i : ι) → MeasurableSpace (β i)} 
  {_mα : MeasurableSpace α} {_mΩ : …
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.precomp`：∀ {α : Type u_1} {Ω : Type u
_2} {ι : Type u_3} {β : ι → Type u_8} {mβ : (i : ι) → MeasurableSpace (β i)}   {
_mα : MeasurableSpace α} {_mΩ : …
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
-/
lemma iIndepFun_precomp_of_bijective (hg : Function.Bijective g) :
    iIndepFun (fun i ↦ f (g i)) κ μ ↔ iIndepFun f κ μ :=
  ⟨.of_precomp hg.surjective, .precomp hg.injective⟩

end ByDefinition

/-
**ProbabilityTheory.Kernel.iIndepFun.indepFun** 是 Mathlib 中的一个定理，位于命名空间 `Probabi
lityTheory.Kernel.iIndepFun`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {m
Ω : MeasurableSpace Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ : MeasureTheory.M
easure α} {β : ι → Type u_8}   {m : (x : ι) → MeasurableSpace (β x)} {f : (i : ι
) → Ω → β i},   ProbabilityTheory.Kernel.iIndepFun f κ μ → ∀ {i j : ι}, i ≠ j → 
ProbabilityTheory.Kernel.IndepFun (f i) (f j) κ μ
参数：x : ι；β x；i : ι；f i；f j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndep.indep`：∀ {α : Type u_1} {Ω : Type u_2} {
ι : Type u_3} {_mα : MeasurableSpace α} {m : ι → MeasurableSpace Ω}   {_mΩ : Mea
surableSpace Ω} {κ : Probab…
-/
theorem iIndepFun.indepFun {β : ι → Type*} {m : ∀ x, MeasurableSpace (β x)} {f : ∀ i, Ω → β i}
    (hf_Indep : iIndepFun f κ μ) {i j : ι} (hij : i ≠ j) : IndepFun (f i) (f j) κ μ :=
  hf_Indep.indep hij
/-
**ProbabilityTheory.Kernel.indepFun_iff_measure_inter_preimage_eq_mul** 是 Mathli
b 中的一个定理，位于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：indepFun_iff_measure_inter_preimage_eq_mul {mβ : MeasurableSpace β} {mβ' :
 MeasurableSpace β'} : IndepFun f g κ μ ↔ forall s t, MeasurableSet s -> Measura
bleSet t -> forallᵐ a ∂μ, κ a (f ⁻¹' s inter g ⁻¹' t) = κ a (f ⁻¹' s) * κ a (g ⁻
¹' t)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
theorem indepFun_iff_measure_inter_preimage_eq_mul {mβ : MeasurableSpace β}
    {mβ' : MeasurableSpace β'} :
    IndepFun f g κ μ ↔
      ∀ s t, MeasurableSet s → MeasurableSet t
        → ∀ᵐ a ∂μ, κ a (f ⁻¹' s ∩ g ⁻¹' t) = κ a (f ⁻¹' s) * κ a (g ⁻¹' t) := by
  constructor <;> intro h
  · refine fun s t hs ht => h (f ⁻¹' s) (g ⁻¹' t) ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
  · rintro _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩; exact h s t hs ht

alias ⟨IndepFun.measure_inter_preimage_eq_mul, _⟩ := indepFun_iff_measure_inter_preimage_eq_mul
/-
**ProbabilityTheory.Kernel.iIndepFun_iff_measure_inter_preimage_eq_mul** 是 Mathl
ib 中的一个定理，位于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：iIndepFun_iff_measure_inter_preimage_eq_mul {ι : Type*} {β : ι -> Type*} (
m : forall x, MeasurableSpace (β x)) (f : forall i, Ω -> β i) : iIndepFun f κ μ 
↔ forall (S : Finset ι) {sets : forall i : ι, Set (β i)} (_H : forall i, i in S 
-> MeasurableSet[m i] (sets i)), forallᵐ a ∂μ, κ a (⋂ i in S, (f i) ⁻¹' (sets i)
) = ∏ i in S, κ a ((f i) ⁻¹' (sets i))
参数：m : forall x, MeasurableSpace (β x)；f : forall i, Ω -> β i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem iIndepFun_iff_measure_inter_preimage_eq_mul {ι : Type*} {β : ι → Type*}
    (m : ∀ x, MeasurableSpace (β x)) (f : ∀ i, Ω → β i) :
    iIndepFun f κ μ ↔
      ∀ (S : Finset ι) {sets : ∀ i : ι, Set (β i)} (_H : ∀ i, i ∈ S → MeasurableSet[m i] (sets i)),
        ∀ᵐ a ∂μ, κ a (⋂ i ∈ S, (f i) ⁻¹' (sets i)) = ∏ i ∈ S, κ a ((f i) ⁻¹' (sets i)) := by
  refine ⟨fun h S sets h_meas => h _ fun i hi_mem => ⟨sets i, h_meas i hi_mem, rfl⟩, ?_⟩
  intro h S setsΩ h_meas
  classical
  let setsβ : ∀ i : ι, Set (β i) := fun i =>
    dite (i ∈ S) (fun hi_mem => (h_meas i hi_mem).choose) fun _ => Set.univ
  have h_measβ : ∀ i ∈ S, MeasurableSet[m i] (setsβ i) := by
    intro i hi_mem
    simp_rw [setsβ, dif_pos hi_mem]
    exact (h_meas i hi_mem).choose_spec.1
  have h_preim : ∀ i ∈ S, setsΩ i = f i ⁻¹' setsβ i := by
    intro i hi_mem
    simp_rw [setsβ, dif_pos hi_mem]
    exact (h_meas i hi_mem).choose_spec.2.symm
  simp_all

alias ⟨iIndepFun.measure_inter_preimage_eq_mul, _⟩ := iIndepFun_iff_measure_inter_preimage_eq_mul
/-
**ProbabilityTheory.Kernel.iIndepFun.congr'** 是 Mathlib 中的一个定理，位于命名空间 `Probabili
tyTheory.Kernel.iIndepFun`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {m
Ω : MeasurableSpace Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ : MeasureTheory.M
easure α} {β : ι → Type u_8}   {mβ : (i : ι) → MeasurableSpace (β i)} {f g : (i 
: ι) → Ω → β i},   ProbabilityTheory.Kernel.iIndepFun f κ μ →     (∀ (i : ι), ∀ᵐ
 (a : α) ∂μ, f i =ᵐ[κ a] g i) → ProbabilityTheory.Kernel.iIndepFun g κ μ
参数：i : ι；β i；i : ι；∀ (i : ι), ∀ᵐ (a : α) ∂μ, f i =ᵐ[κ a] g i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun_iff_measure_inter_preimage_eq_mul`：iI
ndepFun_iff_measure_inter_preimage_eq_mul {ι : Type*} {β : ι -> Type*} (m : fora
ll x, MeasurableSpace (β x)) (f : forall i, Ω -> β i) : iI…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.ae_ball_iff`：ae_ball_iff {ι : Type*} {S : Set ι} (hS : S.C
ountable) {p : α -> forall i in S, Prop} : (forallᵐ x ∂μ, forall i (hi : i in S)
, p x i hi) ↔ f…
· 使用定理 `Finset.countable_toSet`：Finset.countable_toSet (s : Finset α) : Set.Coun
table (↑s : Set α)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `MeasureTheory.measure_congr`：measure_congr (H : s =ᵐ[μ] t) : μ s = μ t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
-/
theorem iIndepFun.congr' {β : ι → Type*} {mβ : ∀ i, MeasurableSpace (β i)}
    {f g : Π i, Ω → β i} (hf : iIndepFun f κ μ)
    (h : ∀ i, ∀ᵐ a ∂μ, f i =ᵐ[κ a] g i) :
    iIndepFun g κ μ := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at hf ⊢
  intro S sets hmeas
  have : ∀ᵐ a ∂μ, ∀ i ∈ S, f i =ᵐ[κ a] g i :=
    (ae_ball_iff (Finset.countable_toSet S)).2 (fun i hi ↦ h i)
  filter_upwards [this, hf S hmeas] with a ha h'a
  have A i (hi : i ∈ S) : (κ a) (g i ⁻¹' sets i) = (κ a) (f i ⁻¹' sets i) := by
    apply measure_congr
    filter_upwards [ha i hi] with ω hω
    change (g i ω ∈ sets i) = (f i ω ∈ sets i)
    simp [hω]
  have B : (κ a) (⋂ i ∈ S, g i ⁻¹' sets i) = (κ a) (⋂ i ∈ S, f i ⁻¹' sets i) := by
    apply measure_congr
    filter_upwards [(ae_ball_iff (Finset.countable_toSet S)).2 ha] with ω hω
    change (ω ∈ ⋂ i ∈ S, g i ⁻¹' sets i) = (ω ∈ ⋂ i ∈ S, f i ⁻¹' sets i)
    simp +contextual [hω]
  convert! h'a using 2 with i hi
  exact A i hi
/-
**ProbabilityTheory.Kernel.iIndepFun_congr'** 是 Mathlib 中的一个定理，位于命名空间 `Probabili
tyTheory.Kernel`。
形式化陈述：iIndepFun_congr' {β : ι -> Type*} {mβ : forall i, MeasurableSpace (β i)} {
f g : Π i, Ω -> β i} (h : forall i, forallᵐ a ∂μ, f i =ᵐ[κ a] g i) : iIndepFun f
 κ μ ↔ iIndepFun g κ μ where mp h'
参数：β i；h : forall i, forallᵐ a ∂μ, f i =ᵐ[κ a] g i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.congr'`：∀ {α : Type u_1} {Ω : Type u_
2} {ι : Type u_3} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω}   {κ : Proba
bilityTheory.Kernel α Ω} {μ : M…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
theorem iIndepFun_congr' {β : ι → Type*} {mβ : ∀ i, MeasurableSpace (β i)}
    {f g : Π i, Ω → β i} (h : ∀ i, ∀ᵐ a ∂μ, f i =ᵐ[κ a] g i) :
    iIndepFun f κ μ ↔ iIndepFun g κ μ where
  mp h' := h'.congr' h
  mpr h' := by
    refine h'.congr' fun i ↦ ?_
    filter_upwards [h i] with a ha using ha.symm
/-
**ProbabilityTheory.Kernel.iIndepFun.comp** 是 Mathlib 中的一个定理，位于命名空间 `Probability
Theory.Kernel.iIndepFun`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {m
Ω : MeasurableSpace Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ : MeasureTheory.M
easure α} {β : ι → Type u_8} {γ : ι → Type u_9}   {mβ : (i : ι) → MeasurableSpac
e (β i)} {mγ : (i : ι) → MeasurableSpace (γ i)} {f : (i : ι) → Ω → β i},   Proba
bilityTheory.Kernel.iIndepFun f κ μ →     ∀ (g : (i : ι) → β i → γ i),       (∀ 
(i : ι), Measurable (g i)) → ProbabilityTheory.Kernel.iIndepFun (fun i => g i ∘ 
f i) κ μ
参数：i : ι；β i；i : ι；γ i；i : ι；g : (i : ι) → β i → γ i；∀ (i : ι), Measurable (g i)
；fun i => g i ∘ f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun_iff_measure_inter_preimage_eq_mul`：iI
ndepFun_iff_measure_inter_preimage_eq_mul {ι : Type*} {β : ι -> Type*} (m : fora
ll x, MeasurableSpace (β x)) (f : forall i, Ω -> β i) : iI…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
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
-/
lemma iIndepFun.comp {β γ : ι → Type*} {mβ : ∀ i, MeasurableSpace (β i)}
    {mγ : ∀ i, MeasurableSpace (γ i)} {f : ∀ i, Ω → β i}
    (h : iIndepFun f κ μ) (g : ∀ i, β i → γ i) (hg : ∀ i, Measurable (g i)) :
    iIndepFun (fun i ↦ g i ∘ f i) κ μ := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at h ⊢
  refine fun t s hs ↦ ?_
  have := h t (sets := fun i ↦ g i ⁻¹' (s i)) (fun i a ↦ hg i (hs i a))
  filter_upwards [this] with a ha
  simp_rw [Set.preimage_comp]
  exact ha
/-
**ProbabilityTheory.Kernel.iIndepFun.comp** 是 Mathlib 中的一个定理，位于命名空间 `Probability
Theory.Kernel.iIndepFun`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {m
Ω : MeasurableSpace Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ : MeasureTheory.M
easure α} {β : ι → Type u_8} {γ : ι → Type u_9}   {mβ : (i : ι) → MeasurableSpac
e (β i)} {mγ : (i : ι) → MeasurableSpace (γ i)} {f : (i : ι) → Ω → β i},   Proba
bilityTheory.Kernel.iIndepFun f κ μ →     ∀ (g : (i : ι) → β i → γ i),       (∀ 
(i : ι), Measurable (g i)) → ProbabilityTheory.Kernel.iIndepFun (fun i => g i ∘ 
f i) κ μ
参数：i : ι；β i；i : ι；γ i；i : ι；g : (i : ι) → β i → γ i；∀ (i : ι), Measurable (g i)
；fun i => g i ∘ f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun_iff_measure_inter_preimage_eq_mul`：iI
ndepFun_iff_measure_inter_preimage_eq_mul {ι : Type*} {β : ι -> Type*} (m : fora
ll x, MeasurableSpace (β x)) (f : forall i, Ω -> β i) : iI…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
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
-/
lemma iIndepFun.comp₀ {β γ : ι → Type*} {mβ : ∀ i, MeasurableSpace (β i)}
    {mγ : ∀ i, MeasurableSpace (γ i)} {f : ∀ i, Ω → β i}
    (h : iIndepFun f κ μ) (g : ∀ i, β i → γ i)
    (hf : ∀ i, AEMeasurable (f i) (κ ∘ₘ μ)) (hg : ∀ i, AEMeasurable (g i) ((κ ∘ₘ μ).map (f i))) :
    iIndepFun (fun i ↦ g i ∘ f i) κ μ := by
  have h : iIndepFun (fun i ↦ ((hg i).mk (g i)) ∘ f i) κ μ :=
    iIndepFun.comp h (fun i ↦ (hg i).mk (g i)) fun i ↦ (hg i).measurable_mk
  have h_ae i := ae_of_ae_map (hf i) (hg i).ae_eq_mk.symm
  exact iIndepFun.congr' h fun i ↦ Measure.ae_ae_of_ae_comp (h_ae i)
/-
**ProbabilityTheory.Kernel.indepFun_iff_indepSet_preimage** 是 Mathlib 中的一个定理，位于命
名空间 `ProbabilityTheory.Kernel`。
形式化陈述：indepFun_iff_indepSet_preimage {mβ : MeasurableSpace β} {mβ' : MeasurableS
pace β'} [IsZeroOrMarkovKernel κ] (hf : Measurable f) (hg : Measurable g) : Inde
pFun f g κ μ ↔ forall s t, MeasurableSet s -> MeasurableSet t -> IndepSet (f ⁻¹'
 s) (g ⁻¹' t) κ μ
参数：hf : Measurable f；hg : Measurable g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.Kernel.indepFun_iff_measure_inter_preimage_eq_mul`：ind
epFun_iff_measure_inter_preimage_eq_mul {mβ : MeasurableSpace β} {mβ' : Measurab
leSpace β'} : IndepFun f g κ μ ↔ forall s t, MeasurableSe…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.indepSet_iff_measure_inter_eq_mul`：indepSet_iff
_measure_inter_eq_mul {_m0 : MeasurableSpace Ω} (hs_meas : MeasurableSet s) (ht_
meas : MeasurableSet t) (κ : Kernel α Ω) (μ : Me…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem indepFun_iff_indepSet_preimage {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    [IsZeroOrMarkovKernel κ] (hf : Measurable f) (hg : Measurable g) :
    IndepFun f g κ μ ↔
      ∀ s t, MeasurableSet s → MeasurableSet t → IndepSet (f ⁻¹' s) (g ⁻¹' t) κ μ := by
  refine indepFun_iff_measure_inter_preimage_eq_mul.trans ?_
  constructor <;> intro h s t hs ht <;> specialize h s t hs ht
  · rwa [indepSet_iff_measure_inter_eq_mul (hf hs) (hg ht) κ μ]
  · rwa [← indepSet_iff_measure_inter_eq_mul (hf hs) (hg ht) κ μ]

@[symm]
nonrec theorem IndepFun.symm {_ : MeasurableSpace β} {_ : MeasurableSpace β'}
    (hfg : IndepFun f g κ μ) : IndepFun g f κ μ := hfg.symm
/-
**ProbabilityTheory.Kernel.IndepFun.congr'** 是 Mathlib 中的一个定理，位于命名空间 `Probabilit
yTheory.Kernel.IndepFun`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {β : Type u_4} {β' : Type u_5} {mα : Measu
rableSpace α} {mΩ : MeasurableSpace Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ :
 MeasureTheory.Measure α} {f : Ω → β} {g : Ω → β'} {mβ : MeasurableSpace β}   {m
β' : MeasurableSpace β'} {f' : Ω → β} {g' : Ω → β'},   ProbabilityTheory.Kernel.
IndepFun f g κ μ →     (∀ᵐ (a : α) ∂μ, f =ᵐ[κ a] f') → (∀ᵐ (a : α) ∂μ, g =ᵐ[κ a]
 g') → ProbabilityTheory.Kernel.IndepFun f' g' κ μ
参数：∀ᵐ (a : α) ∂μ, f =ᵐ[κ a] f'；∀ᵐ (a : α) ∂μ, g =ᵐ[κ a] g'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Filter.EventuallyEq.fun_comp`：∀ {α : Type u} {β : Type v} {γ : Type w} {
f g : α → β} {l : Filter α}, f =ᶠ[l] g → ∀ (h : β → γ), h ∘ f =ᶠ[l] h ∘ g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.measure_congr`：measure_congr (H : s =ᵐ[μ] t) : μ s = μ t
· 使用定理 `Filter.EventuallyEq.inter`：∀ {α : Type u} {s t s' t' : Set α} {l : Filte
r α}, s =ᶠ[l] t → s' =ᶠ[l] t' → s ∩ s' =ᶠ[l] t ∩ t'
-/
theorem IndepFun.congr' {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    {f' : Ω → β} {g' : Ω → β'} (hfg : IndepFun f g κ μ)
    (hf : ∀ᵐ a ∂μ, f =ᵐ[κ a] f') (hg : ∀ᵐ a ∂μ, g =ᵐ[κ a] g') :
    IndepFun f' g' κ μ := by
  rintro _ _ ⟨A, hA, rfl⟩ ⟨B, hB, rfl⟩
  filter_upwards [hf, hg, hfg _ _ ⟨_, hA, rfl⟩ ⟨_, hB, rfl⟩] with a hf' hg' hfg'
  have h1 : f ⁻¹' A =ᵐ[κ a] f' ⁻¹' A := hf'.fun_comp (· ∈ A)
  have h2 : g ⁻¹' B =ᵐ[κ a] g' ⁻¹' B := hg'.fun_comp (· ∈ B)
  rwa [← measure_congr h1, ← measure_congr h2, ← measure_congr (h1.inter h2)]
/-
**ProbabilityTheory.Kernel.IndepFun.comp** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityT
heory.Kernel.IndepFun`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {β : Type u_4} {β' : Type u_5} {γ : Type u
_6} {γ' : Type u_7} {mα : MeasurableSpace α}   {mΩ : MeasurableSpace Ω} {κ : Pro
babilityTheory.Kernel α Ω} {μ : MeasureTheory.Measure α} {f : Ω → β} {g : Ω → β'
}   {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'} {mγ : MeasurableSpace γ}
 {mγ' : MeasurableSpace γ'} {φ : β → γ}   {ψ : β' → γ'},   ProbabilityTheory.Ker
nel.IndepFun f g κ μ →     Measurable φ → Measurable ψ → ProbabilityTheory.Kerne
l.IndepFun (φ ∘ f) (ψ ∘ g) κ μ
参数：φ ∘ f；ψ ∘ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.preimage_comp`：preimage_comp {s : Set γ} : g ∘ f ⁻¹' s = f ⁻¹' g ⁻¹'
 s
-/
theorem IndepFun.comp {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    {mγ : MeasurableSpace γ} {mγ' : MeasurableSpace γ'} {φ : β → γ} {ψ : β' → γ'}
    (hfg : IndepFun f g κ μ) (hφ : Measurable φ) (hψ : Measurable ψ) :
    IndepFun (φ ∘ f) (ψ ∘ g) κ μ := by
  rintro _ _ ⟨A, hA, rfl⟩ ⟨B, hB, rfl⟩
  apply hfg
  · exact ⟨φ ⁻¹' A, hφ hA, Set.preimage_comp.symm⟩
  · exact ⟨ψ ⁻¹' B, hψ hB, Set.preimage_comp.symm⟩
/-
**ProbabilityTheory.Kernel.IndepFun.comp** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityT
heory.Kernel.IndepFun`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {β : Type u_4} {β' : Type u_5} {γ : Type u
_6} {γ' : Type u_7} {mα : MeasurableSpace α}   {mΩ : MeasurableSpace Ω} {κ : Pro
babilityTheory.Kernel α Ω} {μ : MeasureTheory.Measure α} {f : Ω → β} {g : Ω → β'
}   {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'} {mγ : MeasurableSpace γ}
 {mγ' : MeasurableSpace γ'} {φ : β → γ}   {ψ : β' → γ'},   ProbabilityTheory.Ker
nel.IndepFun f g κ μ →     Measurable φ → Measurable ψ → ProbabilityTheory.Kerne
l.IndepFun (φ ∘ f) (ψ ∘ g) κ μ
参数：φ ∘ f；ψ ∘ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.preimage_comp`：preimage_comp {s : Set γ} : g ∘ f ⁻¹' s = f ⁻¹' g ⁻¹'
 s
-/
theorem IndepFun.comp₀ {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    {mγ : MeasurableSpace γ} {mγ' : MeasurableSpace γ'} {φ : β → γ} {ψ : β' → γ'}
    (hfg : IndepFun f g κ μ)
    (hf : AEMeasurable f (κ ∘ₘ μ)) (hg : AEMeasurable g (κ ∘ₘ μ))
    (hφ : AEMeasurable φ ((κ ∘ₘ μ).map f)) (hψ : AEMeasurable ψ ((κ ∘ₘ μ).map g)) :
    IndepFun (φ ∘ f) (ψ ∘ g) κ μ := by
  have h : IndepFun ((hφ.mk φ) ∘ f) ((hψ.mk ψ) ∘ g) κ μ := by
    refine IndepFun.comp hfg hφ.measurable_mk hψ.measurable_mk
  have hφ_ae := ae_of_ae_map hf hφ.ae_eq_mk
  have hψ_ae := ae_of_ae_map hg hψ.ae_eq_mk
  refine IndepFun.congr' h ?_ ?_
  · filter_upwards [Measure.ae_ae_of_ae_comp (hφ_ae)] with a haφ
    filter_upwards [haφ] with ω hωφ
    simp [hωφ]
  · filter_upwards [Measure.ae_ae_of_ae_comp (hψ_ae)] with a haψ
    filter_upwards [haψ] with ω hωψ
    simp [hωψ]
/-
**ProbabilityTheory.Kernel.indepFun_const_left** 是 Mathlib 中的一个引理，位于命名空间 `Probab
ilityTheory.Kernel`。
形式化陈述：indepFun_const_left {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'} [I
sZeroOrMarkovKernel κ] (c : β') (X : Ω -> β) : IndepFun (fun _ => c) X κ μ
参数：c : β'；X : Ω -> β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.IndepFun.eq_1`：∀ {α : Type u_1} {Ω : Type u_2} 
{β : Type u_4} {γ : Type u_6} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω} 
  [mβ : MeasurableSpace β] […
· 使用定理 `MeasurableSpace.comap_const`：∀ {α : Type u_1} {β : Type u_2} {m : Measur
ableSpace β} (b : β), MeasurableSpace.comap (fun _a => b) m = ⊥
· 使用定理 `ProbabilityTheory.Kernel.indep_bot_left`：indep_bot_left (m' : Measurable
Space Ω) {_mΩ : MeasurableSpace Ω} {κ : Kernel α Ω} {μ : Measure α} [IsZeroOrMar
kovKernel κ] : Indep ⊥ m' κ μ
-/
lemma indepFun_const_left {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    [IsZeroOrMarkovKernel κ] (c : β') (X : Ω → β) :
    IndepFun (fun _ ↦ c) X κ μ := by
  rw [IndepFun, MeasurableSpace.comap_const]
  exact indep_bot_left _
/-
**ProbabilityTheory.Kernel.indepFun_const_right** 是 Mathlib 中的一个引理，位于命名空间 `Proba
bilityTheory.Kernel`。
形式化陈述：indepFun_const_right {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'} [
IsZeroOrMarkovKernel κ] (X : Ω -> β) (c : β') : IndepFun X (fun _ => c) κ μ
参数：X : Ω -> β；c : β'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IndepFun.symm`：∀ {α : Type u_1} {Ω : Type u_2} 
{β : Type u_4} {β' : Type u_5} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω}
   {κ : ProbabilityTheory.Ke…
· 使用引理 `ProbabilityTheory.Kernel.indepFun_const_left`：indepFun_const_left {mβ : 
MeasurableSpace β} {mβ' : MeasurableSpace β'} [IsZeroOrMarkovKernel κ] (c : β') 
(X : Ω -> β) : IndepFun (fun _ => …
-/
lemma indepFun_const_right {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    [IsZeroOrMarkovKernel κ] (X : Ω → β) (c : β') :
    IndepFun X (fun _ ↦ c) κ μ :=
  (indepFun_const_left c X).symm
/-
**ProbabilityTheory.Kernel.IndepFun.neg_right** 是 Mathlib 中的一个定理，位于命名空间 `Probabi
lityTheory.Kernel.IndepFun`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {β : Type u_4} {β' : Type u_5} {mα : Measu
rableSpace α} {mΩ : MeasurableSpace Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ :
 MeasureTheory.Measure α} {f : Ω → β} {g : Ω → β'} {_mβ : MeasurableSpace β}   {
_mβ' : MeasurableSpace β'} [inst : Neg β'] [MeasurableNeg β'],   ProbabilityTheo
ry.Kernel.IndepFun f g κ μ → ProbabilityTheory.Kernel.IndepFun f (-g) κ μ
参数：-g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IndepFun.comp`：∀ {α : Type u_1} {Ω : Type u_2} 
{β : Type u_4} {β' : Type u_5} {γ : Type u_6} {γ' : Type u_7} {mα : MeasurableSp
ace α}   {mΩ : MeasurableSpa…
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)
· 使用定理 `MeasurableNeg.measurable_neg`：∀ {G : Type u_2} {inst : Neg G} {inst_1 : 
MeasurableSpace G} [self : MeasurableNeg G], Measurable Neg.neg
-/
theorem IndepFun.neg_right {_mβ : MeasurableSpace β} {_mβ' : MeasurableSpace β'} [Neg β']
    [MeasurableNeg β'] (hfg : IndepFun f g κ μ) :
    IndepFun f (-g) κ μ := hfg.comp measurable_id measurable_neg
/-
**ProbabilityTheory.Kernel.IndepFun.neg_left** 是 Mathlib 中的一个定理，位于命名空间 `Probabil
ityTheory.Kernel.IndepFun`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {β : Type u_4} {β' : Type u_5} {mα : Measu
rableSpace α} {mΩ : MeasurableSpace Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ :
 MeasureTheory.Measure α} {f : Ω → β} {g : Ω → β'} {_mβ : MeasurableSpace β}   {
_mβ' : MeasurableSpace β'} [inst : Neg β] [MeasurableNeg β],   ProbabilityTheory
.Kernel.IndepFun f g κ μ → ProbabilityTheory.Kernel.IndepFun (-f) g κ μ
参数：-f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IndepFun.comp`：∀ {α : Type u_1} {Ω : Type u_2} 
{β : Type u_4} {β' : Type u_5} {γ : Type u_6} {γ' : Type u_7} {mα : MeasurableSp
ace α}   {mΩ : MeasurableSpa…
· 使用定理 `MeasurableNeg.measurable_neg`：∀ {G : Type u_2} {inst : Neg G} {inst_1 : 
MeasurableSpace G} [self : MeasurableNeg G], Measurable Neg.neg
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)
-/
theorem IndepFun.neg_left {_mβ : MeasurableSpace β} {_mβ' : MeasurableSpace β'} [Neg β]
    [MeasurableNeg β] (hfg : IndepFun f g κ μ) :
    IndepFun (-f) g κ μ := hfg.comp measurable_neg measurable_id

/-- Two random variables `f, g` are independent given a kernel `κ` and a measure `μ` iff
`μ ⊗ₘ κ.map (fun ω ↦ (f ω, g ω)) = μ ⊗ₘ (κ.map f ×ₖ κ.map g)`. -/
/-
**ProbabilityTheory.Kernel.indepFun_iff_compProd_map_prod_eq_compProd_prod_map_m
ap** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：indepFun_iff_compProd_map_prod_eq_compProd_prod_map_map {mβ : MeasurableSp
ace β} {mγ : MeasurableSpace γ} [IsFiniteMeasure μ] [IsFiniteKernel κ] {f : Ω ->
 β} {g : Ω -> γ} (hf : Measurable f) (hg : Measurable g) : IndepFun f g κ μ ↔ μ 
otimesₘ κ.map (fun ω => (f ω, g ω)) = μ otimesₘ (κ.map f ×ₖ κ.map g)
参数：hf : Measurable f；hg : Measurable g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.indepFun_iff_measure_inter_preimage_eq_mul`：ind
epFun_iff_measure_inter_preimage_eq_mul {mβ : MeasurableSpace β} {mβ' : Measurab
leSpace β'} : IndepFun f g κ μ ↔ forall s t, MeasurableSe…
· 使用引理 `MeasureTheory.Measure.ext_prod₃_iff`：ext_prod₃_iff {α β γ : Type*} {mα :
 MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ} {μ ν : Mea
sure (α × β × γ)} [IsFini…
· 使用定理 `MeasureTheory.Measure.instIsFiniteMeasureProdCompProdOfIsFiniteKernel`：∀
 {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
 {μ : MeasureTheory.Measure α}   {κ : ProbabilityTheory.Ker…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.map`：∀ {α : Type u_1} {β : Type 
u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ : Me
asurableSpace γ} (κ : Probability…
· 使用引理 `MeasureTheory.Measure.compProd_apply`：compProd_apply [SFinite μ] [IsSFin
iteKernel κ] {s : Set (α × β)} (hs : MeasurableSet s) : (μ otimesₘ κ) s = ∫⁻ a, 
κ a (Prod.mk a ⁻¹' s) ∂μ
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.map`：∀ {α : Type u_1} {β : Type
 u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ : M
easurableSpace γ} (κ : Probability…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `MeasurableSet.prod`：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace
 α} {mβ : MeasurableSpace β} {s : Set α} {t : Set β},   MeasurableSet s → Measur
ableSet …
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.prod`：∀ {α : Type u_1} {β : Typ
e u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ : 
MeasurableSpace γ} (κ : Probability…
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ProbabilityTheory.Kernel.map_apply`：map_apply (κ : Kernel α β) (hf : Mea
surable f) (a : α) : map κ f a = (κ a).map f
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `Set.mk_preimage_prod`：mk_preimage_prod (f : γ -> α) (g : γ -> β) : (fun 
x => (f x, g x)) ⁻¹' s ×ˢ t = f ⁻¹' s inter g ⁻¹' t
· 使用引理 `ProbabilityTheory.Kernel.prod_apply_prod`：prod_apply_prod {κ : Kernel α 
β} {η : Kernel α γ} [IsSFiniteKernel κ] [IsSFiniteKernel η] {s : Set β} {t : Set
 γ} {a : α} : (κ ×ₖ η) a (s ×ˢ…
· 使用定理 `ProbabilityTheory.Kernel.map_apply'`：map_apply' (κ : Kernel α β) (hf : M
easurable f) (a : α) {s : Set γ} (hs : MeasurableSet s) : map κ f a s = κ a (f ⁻
¹' s)
（共 41 条，此处仅展示前 30 条）

--- 原说明 ---
Two random variables `f, g` are independent given a kernel `κ` and a measure `μ`
 iff
`μ ⊗ₘ κ.map (fun ω ↦ (f ω, g ω)) = μ ⊗ₘ (κ.map f ×ₖ κ.map g)`.
-/
theorem indepFun_iff_compProd_map_prod_eq_compProd_prod_map_map
    {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
    [IsFiniteMeasure μ] [IsFiniteKernel κ] {f : Ω → β} {g : Ω → γ}
    (hf : Measurable f) (hg : Measurable g) :
    IndepFun f g κ μ ↔ μ ⊗ₘ κ.map (fun ω ↦ (f ω, g ω)) = μ ⊗ₘ (κ.map f ×ₖ κ.map g) := by
  classical
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [Measure.ext_prod₃_iff]
    intro u s t hu hs ht
    rw [Measure.compProd_apply (hu.prod (hs.prod ht)),
      Measure.compProd_apply (hu.prod (hs.prod ht))]
    refine lintegral_congr_ae ?_
    have h_set_eq ω : Prod.mk ω ⁻¹' u ×ˢ s ×ˢ t = if ω ∈ u then s ×ˢ t else ∅ := by ext; simp
    simp_rw [h_set_eq]
    filter_upwards [h s t hs ht] with ω hω
    by_cases hωu : ω ∈ u
    swap; · simp [hωu]
    simp only [hωu, ↓reduceIte]
    rw [map_apply _ (by fun_prop), Measure.map_apply (by fun_prop) (hs.prod ht),
      mk_preimage_prod, hω, prod_apply_prod, map_apply' _ (by fun_prop), map_apply' _ (by fun_prop)]
    exacts [ht, hs]
  · intro s t hs ht
    rw [Measure.ext_prod₃_iff] at h
    refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite ?_ ?_ ?_
    · exact Kernel.measurable_coe _ ((hf hs).inter (hg ht))
    · exact (Kernel.measurable_coe _ (hf hs)).mul (Kernel.measurable_coe _ (hg ht))
    intro u hu hμu
    specialize h hu hs ht
    rw [Measure.compProd_apply_prod hu (hs.prod ht),
      Measure.compProd_apply_prod hu (hs.prod ht)] at h
    convert! h with ω ω
    · rw [map_apply' _ (by fun_prop) _ (hs.prod ht), mk_preimage_prod]
    · rw [prod_apply_prod, map_apply' _ (by fun_prop) _ hs, map_apply' _ (by fun_prop) _ ht]

section iIndepFun
variable {β : ι → Type*} {m : ∀ i, MeasurableSpace (β i)} {f : ∀ i, Ω → β i}


/-- If `f` is a family of mutually independent random variables (`iIndepFun m f μ`) and `S, T` are
two disjoint finite index sets, then the tuple formed by `f i` for `i ∈ S` is independent of the
tuple `(f i)_i` for `i ∈ T`. -/
/-
**ProbabilityTheory.Kernel.iIndepFun.indepFun_finset** 是 Mathlib 中的一个定理，位于命名空间 `
ProbabilityTheory.Kernel.iIndepFun`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {m
Ω : MeasurableSpace Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ : MeasureTheory.M
easure α} {β : ι → Type u_8}   {m : (i : ι) → MeasurableSpace (β i)} {f : (i : ι
) → Ω → β i} (S T : Finset ι),   Disjoint S T →     ProbabilityTheory.Kernel.iIn
depFun f κ μ →       (∀ (i : ι), Measurable (f i)) → ProbabilityTheory.Kernel.In
depFun (fun a i => f (↑i) a) (fun a i => f (↑i) a) κ μ
参数：i : ι；β i；i : ι；S T : Finset ι；∀ (i : ι), Measurable (f i)；fun a i => f (↑i) 
a；fun a i => f (↑i) a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `ProbabilityTheory.Kernel.exists_ae_eq_isMarkovKernel`：exists_ae_eq_isMar
kovKernel {μ : Measure α} (h : forallᵐ a ∂μ, IsProbabilityMeasure (κ a)) (h' : μ
 != 0) : exists (η : Kernel α β), (κ =ᵐ[μ]…
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.ae_isProbabilityMeasure`：∀ {α : Type 
u_1} {Ω : Type u_2} {ι : Type u_3} {β : ι → Type u_8} {mβ : (i : ι) → Measurable
Space (β i)}   {_mα : MeasurableSpace α} {_mΩ : …
· 使用定理 `ProbabilityTheory.Kernel.IndepFun.congr`：∀ {α : Type u_1} {Ω : Type u_2}
 {γ : Type u_6} {_mα : MeasurableSpace α} {_mΩ : MeasurableSpace Ω}   {κ η : Pro
babilityTheory.Kernel α Ω} {μ…
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `IsPiSystem.comap`：IsPiSystem.comap {α β} {S : Set (Set β)} (h_pi : IsPiS
ystem S) (f : α -> β) : IsPiSystem { s : Set α | exists t in S, f ⁻¹' t = s }
· 使用定理 `isPiSystem_pi`：isPiSystem_pi [forall i, MeasurableSpace (α i)] : IsPiSys
tem (pi univ '' pi univ fun i => { s : Set (α i) | MeasurableSet s })
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `generateFrom_pi`：generateFrom_pi [forall i, MeasurableSpace (α i)] : gen
erateFrom (pi univ '' pi univ fun i => { s : Set (α i) | MeasurableSet s }) = Me
asura…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `MeasurableSpace.comap_generateFrom`：comap_generateFrom {f : α -> β} {s :
 Set (Set β)} : (generateFrom s).comap f = generateFrom (preimage f '' s)
· 使用定理 `ProbabilityTheory.Kernel.IndepSets.indep`：∀ {α : Type u_1} {Ω : Type u_2
} {_mα : MeasurableSpace α} {m1 m2 m : MeasurableSpace Ω}   {κ : ProbabilityTheo
ry.Kernel α Ω} {μ : MeasureThe…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `Measurable.comap_le`：∀ {α : Type u_1} {β : Type u_2} {m₁ : MeasurableSpa
ce α} {m₂ : MeasurableSpace β} {f : α → β},   Measurable f → MeasurableSpace.com
ap f m₂ ≤…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `measurable_pi_iff`：measurable_pi_iff {g : α -> forall a, X a} : Measurab
le g ↔ forall a, Measurable fun x => g x a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.disjoint_right`：disjoint_right : Disjoint s t ↔ forall ⦃a⦄, a in 
t -> a ∉ s
· 使用定理 `Finset.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s 
-> a ∉ t
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
（共 42 条，此处仅展示前 30 条）

--- 原说明 ---
If `f` is a family of mutually independent random variables (`iIndepFun m f μ`) 
and `S, T` are
two disjoint finite index sets, then the tuple formed by `f i` for `i ∈ S` is in
dependent of the
tuple `(f i)_i` for `i ∈ T`.
-/
theorem iIndepFun.indepFun_finset (S T : Finset ι) (hST : Disjoint S T)
    (hf_Indep : iIndepFun f κ μ) (hf_meas : ∀ i, Measurable (f i)) :
    IndepFun (fun a (i : S) => f i a) (fun a (i : T) => f i a) κ μ := by
  rcases eq_or_ne μ 0 with rfl | hμ
  · simp
  obtain ⟨η, η_eq, hη⟩ : ∃ (η : Kernel α Ω), κ =ᵐ[μ] η ∧ IsMarkovKernel η :=
    exists_ae_eq_isMarkovKernel hf_Indep.ae_isProbabilityMeasure hμ
  apply IndepFun.congr (Filter.EventuallyEq.symm η_eq)
  -- We introduce π-systems, built from the π-system of boxes which generates `MeasurableSpace.pi`.
  let πSβ := Set.pi (Set.univ : Set S) ''
    Set.pi (Set.univ : Set S) fun i => { s : Set (β i) | MeasurableSet[m i] s }
  let πS := { s : Set Ω | ∃ t ∈ πSβ, (fun a (i : S) => f i a) ⁻¹' t = s }
  have hπS_pi : IsPiSystem πS := by exact IsPiSystem.comap (@isPiSystem_pi _ _ ?_) _
  have hπS_gen : (MeasurableSpace.pi.comap fun a (i : S) => f i a) = generateFrom πS := by
    rw [generateFrom_pi.symm, comap_generateFrom]
    congr
  let πTβ := Set.pi (Set.univ : Set T) ''
      Set.pi (Set.univ : Set T) fun i => { s : Set (β i) | MeasurableSet[m i] s }
  let πT := { s : Set Ω | ∃ t ∈ πTβ, (fun a (i : T) => f i a) ⁻¹' t = s }
  have hπT_pi : IsPiSystem πT := by exact IsPiSystem.comap (@isPiSystem_pi _ _ ?_) _
  have hπT_gen : (MeasurableSpace.pi.comap fun a (i : T) => f i a) = generateFrom πT := by
    rw [generateFrom_pi.symm, comap_generateFrom]
    congr
  -- To prove independence, we prove independence of the generating π-systems.
  refine IndepSets.indep (Measurable.comap_le (measurable_pi_iff.mpr fun i => hf_meas i))
    (Measurable.comap_le (measurable_pi_iff.mpr fun i => hf_meas i)) hπS_pi hπT_pi hπS_gen hπT_gen
    ?_
  rintro _ _ ⟨s, ⟨sets_s, hs1, hs2⟩, rfl⟩ ⟨t, ⟨sets_t, ht1, ht2⟩, rfl⟩
  simp only [Set.mem_univ_pi, Set.mem_ofPred_eq] at hs1 ht1
  rw [← hs2, ← ht2]
  classical
  let sets_s' : ∀ i : ι, Set (β i) := fun i =>
    dite (i ∈ S) (fun hi => sets_s ⟨i, hi⟩) fun _ => Set.univ
  have h_sets_s'_eq : ∀ {i} (hi : i ∈ S), sets_s' i = sets_s ⟨i, hi⟩ := by
    intro i hi; simp_rw [sets_s', dif_pos hi]
  have h_sets_s'_univ : ∀ {i} (_hi : i ∈ T), sets_s' i = Set.univ := by
    intro i hi; simp_rw [sets_s', dif_neg (Finset.disjoint_right.mp hST hi)]
  let sets_t' : ∀ i : ι, Set (β i) := fun i =>
    dite (i ∈ T) (fun hi => sets_t ⟨i, hi⟩) fun _ => Set.univ
  have h_sets_t'_univ : ∀ {i} (_hi : i ∈ S), sets_t' i = Set.univ := by
    intro i hi; simp_rw [sets_t', dif_neg (Finset.disjoint_left.mp hST hi)]
  have h_meas_s' : ∀ i ∈ S, MeasurableSet (sets_s' i) := by
    intro i hi; rw [h_sets_s'_eq hi]; exact hs1 _
  have h_meas_t' : ∀ i ∈ T, MeasurableSet (sets_t' i) := by
    intro i hi; simp_rw [sets_t', dif_pos hi]; exact ht1 _
  have h_eq_inter_S : (fun (ω : Ω) (i : ↥S) =>
    f (↑i) ω) ⁻¹' Set.pi Set.univ sets_s = ⋂ i ∈ S, f i ⁻¹' sets_s' i := by
    ext1 x
    simp_rw [Set.mem_preimage, Set.mem_univ_pi, Set.mem_iInter]
    grind
  have h_eq_inter_T : (fun (ω : Ω) (i : ↥T) => f (↑i) ω) ⁻¹' Set.pi Set.univ sets_t
    = ⋂ i ∈ T, f i ⁻¹' sets_t' i := by
    ext1 x
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_iInter]
    constructor <;> intro h
    · intro i hi; simp_rw [sets_t', dif_pos hi]; exact h ⟨i, hi⟩
    · rintro ⟨i, hi⟩; specialize h i hi; simp_rw [sets_t', dif_pos hi] at h; exact h
  replace hf_Indep := hf_Indep.congr η_eq
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at hf_Indep
  have h_Inter_inter :
    ((⋂ i ∈ S, f i ⁻¹' sets_s' i) ∩ ⋂ i ∈ T, f i ⁻¹' sets_t' i) =
      ⋂ i ∈ S ∪ T, f i ⁻¹' (sets_s' i ∩ sets_t' i) := by
    ext1 x
    simp_rw [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Finset.mem_union]
    constructor <;> intro h
    · grind
    · exact ⟨fun i hi => (h i (Or.inl hi)).1, fun i hi => (h i (Or.inr hi)).2⟩
  have h_meas_inter : ∀ i ∈ S ∪ T, MeasurableSet (sets_s' i ∩ sets_t' i) := by
    intro i hi_mem
    rw [Finset.mem_union] at hi_mem
    rcases hi_mem with hi_mem | hi_mem
    · rw [h_sets_t'_univ hi_mem, Set.inter_univ]
      exact h_meas_s' i hi_mem
    · rw [h_sets_s'_univ hi_mem, Set.univ_inter]
      exact h_meas_t' i hi_mem
  filter_upwards [hf_Indep S h_meas_s', hf_Indep T h_meas_t', hf_Indep (S ∪ T) h_meas_inter]
    with a h_indepS h_indepT h_indepST
  rw [h_eq_inter_S, h_eq_inter_T, h_indepS, h_indepT, h_Inter_inter, h_indepST,
    Finset.prod_union hST]
  congr 1
  · refine Finset.prod_congr rfl fun i hi => ?_
    rw [h_sets_t'_univ hi, Set.inter_univ]
  · refine Finset.prod_congr rfl fun i hi => ?_
    rw [h_sets_s'_univ hi, Set.univ_inter]
/-
**ProbabilityTheory.Kernel.iIndepFun.indepFun_finset** 是 Mathlib 中的一个定理，位于命名空间 `
ProbabilityTheory.Kernel.iIndepFun`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {m
Ω : MeasurableSpace Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ : MeasureTheory.M
easure α} {β : ι → Type u_8}   {m : (i : ι) → MeasurableSpace (β i)} {f : (i : ι
) → Ω → β i} (S T : Finset ι),   Disjoint S T →     ProbabilityTheory.Kernel.iIn
depFun f κ μ →       (∀ (i : ι), Measurable (f i)) → ProbabilityTheory.Kernel.In
depFun (fun a i => f (↑i) a) (fun a i => f (↑i) a) κ μ
参数：i : ι；β i；i : ι；S T : Finset ι；∀ (i : ι), Measurable (f i)；fun a i => f (↑i) 
a；fun a i => f (↑i) a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `ProbabilityTheory.Kernel.exists_ae_eq_isMarkovKernel`：exists_ae_eq_isMar
kovKernel {μ : Measure α} (h : forallᵐ a ∂μ, IsProbabilityMeasure (κ a)) (h' : μ
 != 0) : exists (η : Kernel α β), (κ =ᵐ[μ]…
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.ae_isProbabilityMeasure`：∀ {α : Type 
u_1} {Ω : Type u_2} {ι : Type u_3} {β : ι → Type u_8} {mβ : (i : ι) → Measurable
Space (β i)}   {_mα : MeasurableSpace α} {_mΩ : …
· 使用定理 `ProbabilityTheory.Kernel.IndepFun.congr`：∀ {α : Type u_1} {Ω : Type u_2}
 {γ : Type u_6} {_mα : MeasurableSpace α} {_mΩ : MeasurableSpace Ω}   {κ η : Pro
babilityTheory.Kernel α Ω} {μ…
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `IsPiSystem.comap`：IsPiSystem.comap {α β} {S : Set (Set β)} (h_pi : IsPiS
ystem S) (f : α -> β) : IsPiSystem { s : Set α | exists t in S, f ⁻¹' t = s }
· 使用定理 `isPiSystem_pi`：isPiSystem_pi [forall i, MeasurableSpace (α i)] : IsPiSys
tem (pi univ '' pi univ fun i => { s : Set (α i) | MeasurableSet s })
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `generateFrom_pi`：generateFrom_pi [forall i, MeasurableSpace (α i)] : gen
erateFrom (pi univ '' pi univ fun i => { s : Set (α i) | MeasurableSet s }) = Me
asura…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `MeasurableSpace.comap_generateFrom`：comap_generateFrom {f : α -> β} {s :
 Set (Set β)} : (generateFrom s).comap f = generateFrom (preimage f '' s)
· 使用定理 `ProbabilityTheory.Kernel.IndepSets.indep`：∀ {α : Type u_1} {Ω : Type u_2
} {_mα : MeasurableSpace α} {m1 m2 m : MeasurableSpace Ω}   {κ : ProbabilityTheo
ry.Kernel α Ω} {μ : MeasureThe…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `Measurable.comap_le`：∀ {α : Type u_1} {β : Type u_2} {m₁ : MeasurableSpa
ce α} {m₂ : MeasurableSpace β} {f : α → β},   Measurable f → MeasurableSpace.com
ap f m₂ ≤…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `measurable_pi_iff`：measurable_pi_iff {g : α -> forall a, X a} : Measurab
le g ↔ forall a, Measurable fun x => g x a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.disjoint_right`：disjoint_right : Disjoint s t ↔ forall ⦃a⦄, a in 
t -> a ∉ s
· 使用定理 `Finset.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s 
-> a ∉ t
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
（共 42 条，此处仅展示前 30 条）
-/
theorem iIndepFun.indepFun_finset₀ (S T : Finset ι) (hST : Disjoint S T)
    (hf_Indep : iIndepFun f κ μ) (hf_meas : ∀ i, AEMeasurable (f i) (κ ∘ₘ μ)) :
    IndepFun (fun a (i : S) ↦ f i a) (fun a (i : T) ↦ f i a) κ μ := by
  have h : IndepFun (fun a (i : S) ↦ (hf_meas i).mk (f i) a)
      (fun a (i : T) ↦ (hf_meas i).mk (f i) a) κ μ := by
    refine iIndepFun.indepFun_finset S T hST ?_ fun i ↦ (hf_meas i).measurable_mk
    exact iIndepFun.congr' hf_Indep fun i ↦ Measure.ae_ae_of_ae_comp (hf_meas i).ae_eq_mk
  refine IndepFun.congr' h ?_ ?_
  · have : ∀ᵐ (a : α) ∂μ, ∀ (i : S), f i =ᵐ[κ a] (hf_meas i).mk := by
      rw [ae_all_iff]
      exact fun i ↦ Measure.ae_ae_of_ae_comp (hf_meas i).ae_eq_mk
    filter_upwards [this] with a ha
    filter_upwards [ae_all_iff.2 ha] with b hb
    ext i
    exact (hb i).symm
  · have : ∀ᵐ (a : α) ∂μ, ∀ (i : T), f i =ᵐ[κ a] (hf_meas i).mk := by
      rw [ae_all_iff]
      exact fun i ↦ Measure.ae_ae_of_ae_comp (hf_meas i).ae_eq_mk
    filter_upwards [this] with a ha
    filter_upwards [ae_all_iff.2 ha] with b hb
    ext i
    exact (hb i).symm
/-
**ProbabilityTheory.Kernel.iIndepFun.indepFun_prodMk** 是 Mathlib 中的一个定理，位于命名空间 `
ProbabilityTheory.Kernel.iIndepFun`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {m
Ω : MeasurableSpace Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ : MeasureTheory.M
easure α} {β : ι → Type u_8}   {m : (i : ι) → MeasurableSpace (β i)} {f : (i : ι
) → Ω → β i},   ProbabilityTheory.Kernel.iIndepFun f κ μ →     (∀ (i : ι), Measu
rable (f i)) →       ∀ (i j k : ι), i ≠ k → j ≠ k → ProbabilityTheory.Kernel.Ind
epFun (fun a => (f i a, f j a)) (f k) κ μ
参数：i : ι；β i；i : ι；∀ (i : ι), Measurable (f i)；i j k : ι；fun a => (f i a, f j a)
；f k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_singleton_self`：mem_singleton_self (a : α) : a in ({a} : Fins
et α)
· 使用定理 `measurable_pi_apply`：measurable_pi_apply (a : δ) : Measurable fun f : fo
rall a, X a => f a
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Measurable.prod`：Measurable.prod {f : α -> β × γ} (hf₁ : Measurable fun 
a => (f a).1) (hf₂ : Measurable fun a => (f a).2) : Measurable f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.IndepFun.comp`：∀ {α : Type u_1} {Ω : Type u_2} 
{β : Type u_4} {β' : Type u_5} {γ : Type u_6} {γ' : Type u_7} {mα : MeasurableSp
ace α}   {mΩ : MeasurableSpa…
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.indepFun_finset`：∀ {α : Type u_1} {Ω 
: Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω}   {
κ : ProbabilityTheory.Kernel α Ω} {μ : M…
· 使用定理 `Finset.disjoint_singleton_right`：disjoint_singleton_right : Disjoint s (
singleton a) ↔ a ∉ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
theorem iIndepFun.indepFun_prodMk (hf_Indep : iIndepFun f κ μ)
    (hf_meas : ∀ i, Measurable (f i)) (i j k : ι) (hik : i ≠ k) (hjk : j ≠ k) :
    IndepFun (fun a => (f i a, f j a)) (f k) κ μ := by
  classical
  have h_right :
      f k = (fun p : ∀ j : ({k} : Finset ι), β j => p ⟨k, Finset.mem_singleton_self k⟩) ∘
        fun a (j : ({k} : Finset ι)) => f j a :=
    rfl
  have h_meas_right : Measurable fun p : ∀ j : ({k} : Finset ι),
      β j => p ⟨k, Finset.mem_singleton_self k⟩ :=
    measurable_pi_apply _
  let s : Finset ι := {i, j}
  have h_left : (fun ω => (f i ω, f j ω)) = (fun p : ∀ l : s, β l =>
      (p ⟨i, Finset.mem_insert_self i _⟩,
        p ⟨j, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩)) ∘
        fun a (j : s) => f j a := by
    ext1 a
    simp only
    constructor
  have h_meas_left : Measurable fun p : ∀ l : s, β l =>
      (p ⟨i, Finset.mem_insert_self i _⟩,
        p ⟨j, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩) :=
    Measurable.prod (measurable_pi_apply _) (measurable_pi_apply _)
  rw [h_left, h_right]
  refine (hf_Indep.indepFun_finset s {k} ?_ hf_meas).comp h_meas_left h_meas_right
  rw [Finset.disjoint_singleton_right]
  simp only [s, Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨hik.symm, hjk.symm⟩
/-
**ProbabilityTheory.Kernel.iIndepFun.indepFun_prodMk** 是 Mathlib 中的一个定理，位于命名空间 `
ProbabilityTheory.Kernel.iIndepFun`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {m
Ω : MeasurableSpace Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ : MeasureTheory.M
easure α} {β : ι → Type u_8}   {m : (i : ι) → MeasurableSpace (β i)} {f : (i : ι
) → Ω → β i},   ProbabilityTheory.Kernel.iIndepFun f κ μ →     (∀ (i : ι), Measu
rable (f i)) →       ∀ (i j k : ι), i ≠ k → j ≠ k → ProbabilityTheory.Kernel.Ind
epFun (fun a => (f i a, f j a)) (f k) κ μ
参数：i : ι；β i；i : ι；∀ (i : ι), Measurable (f i)；i j k : ι；fun a => (f i a, f j a)
；f k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_singleton_self`：mem_singleton_self (a : α) : a in ({a} : Fins
et α)
· 使用定理 `measurable_pi_apply`：measurable_pi_apply (a : δ) : Measurable fun f : fo
rall a, X a => f a
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Measurable.prod`：Measurable.prod {f : α -> β × γ} (hf₁ : Measurable fun 
a => (f a).1) (hf₂ : Measurable fun a => (f a).2) : Measurable f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.IndepFun.comp`：∀ {α : Type u_1} {Ω : Type u_2} 
{β : Type u_4} {β' : Type u_5} {γ : Type u_6} {γ' : Type u_7} {mα : MeasurableSp
ace α}   {mΩ : MeasurableSpa…
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.indepFun_finset`：∀ {α : Type u_1} {Ω 
: Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω}   {
κ : ProbabilityTheory.Kernel α Ω} {μ : M…
· 使用定理 `Finset.disjoint_singleton_right`：disjoint_singleton_right : Disjoint s (
singleton a) ↔ a ∉ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
theorem iIndepFun.indepFun_prodMk₀ (hf_Indep : iIndepFun f κ μ)
    (hf_meas : ∀ i, AEMeasurable (f i) (κ ∘ₘ μ)) (i j k : ι) (hik : i ≠ k) (hjk : j ≠ k) :
    IndepFun (fun a ↦ (f i a, f j a)) (f k) κ μ := by
  have h : IndepFun (fun a ↦ ((hf_meas i).mk (f i) a, (hf_meas j).mk (f j) a))
      ((hf_meas k).mk (f k)) κ μ := by
    refine iIndepFun.indepFun_prodMk ?_ (fun i ↦ (hf_meas i).measurable_mk) _ _ _ hik hjk
    exact iIndepFun.congr' hf_Indep fun i ↦ Measure.ae_ae_of_ae_comp (hf_meas i).ae_eq_mk
  refine IndepFun.congr' h ?_ ?_
  · filter_upwards [Measure.ae_ae_of_ae_comp (hf_meas i).ae_eq_mk,
      Measure.ae_ae_of_ae_comp (hf_meas j).ae_eq_mk] with a hi hj
    filter_upwards [hi, hj] with ω hωi hωj
    rw [← hωi, ← hωj]
  · exact Measure.ae_ae_of_ae_comp (hf_meas k).ae_eq_mk.symm

open Finset in
/-
**ProbabilityTheory.Kernel.iIndepFun.indepFun_prodMk_prodMk** 是 Mathlib 中的一个定理，位
于命名空间 `ProbabilityTheory.Kernel.iIndepFun`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {m
Ω : MeasurableSpace Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ : MeasureTheory.M
easure α} {β : ι → Type u_8}   {m : (i : ι) → MeasurableSpace (β i)} {f : (i : ι
) → Ω → β i},   ProbabilityTheory.Kernel.iIndepFun f κ μ →     (∀ (i : ι), Measu
rable (f i)) →       ∀ (i j k l : ι),         i ≠ k →           i ≠ l →         
    j ≠ k → j ≠ l → ProbabilityTheory.Kernel.IndepFun (fun a => (f i a, f j a)) 
(fun a => (f k a, f l a)) κ μ
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
lemma iIndepFun.indepFun_prodMk_prodMk (hf_indep : iIndepFun f κ μ)
    (hf_meas : ∀ i, Measurable (f i))
    (i j k l : ι) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    IndepFun (fun a ↦ (f i a, f j a)) (fun a ↦ (f k a, f l a)) κ μ := by
  classical
  let g (i j : ι) (v : Π x : ({i, j} : Finset ι), β x) : β i × β j :=
    ⟨v ⟨i, mem_insert_self _ _⟩, v ⟨j, mem_insert_of_mem <| mem_singleton_self _⟩⟩
  have hg (i j : ι) : Measurable (g i j) := by fun_prop
  exact (hf_indep.indepFun_finset {i, j} {k, l} (by aesop) hf_meas).comp (hg i j) (hg k l)
/-
**ProbabilityTheory.Kernel.iIndepFun.indepFun_prodMk_prodMk** 是 Mathlib 中的一个定理，位
于命名空间 `ProbabilityTheory.Kernel.iIndepFun`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {m
Ω : MeasurableSpace Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ : MeasureTheory.M
easure α} {β : ι → Type u_8}   {m : (i : ι) → MeasurableSpace (β i)} {f : (i : ι
) → Ω → β i},   ProbabilityTheory.Kernel.iIndepFun f κ μ →     (∀ (i : ι), Measu
rable (f i)) →       ∀ (i j k l : ι),         i ≠ k →           i ≠ l →         
    j ≠ k → j ≠ l → ProbabilityTheory.Kernel.IndepFun (fun a => (f i a, f j a)) 
(fun a => (f k a, f l a)) κ μ
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
theorem iIndepFun.indepFun_prodMk_prodMk₀ (hf_indep : iIndepFun f κ μ)
    (hf_meas : ∀ i, AEMeasurable (f i) (κ ∘ₘ μ))
    (i j k l : ι) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    IndepFun (fun a ↦ (f i a, f j a)) (fun a ↦ (f k a, f l a)) κ μ := by
  have h : IndepFun (fun a ↦ ((hf_meas i).mk (f i) a, (hf_meas j).mk (f j) a))
      (fun a ↦ ((hf_meas k).mk (f k) a, (hf_meas l).mk (f l) a)) κ μ := by
    refine iIndepFun.indepFun_prodMk_prodMk ?_ (fun i ↦ (hf_meas i).measurable_mk) _ _ _ _ hik hil
      hjk hjl
    exact iIndepFun.congr' hf_indep fun i ↦ Measure.ae_ae_of_ae_comp (hf_meas i).ae_eq_mk
  refine IndepFun.congr' h ?_ ?_
  · filter_upwards [Measure.ae_ae_of_ae_comp (hf_meas i).ae_eq_mk,
      Measure.ae_ae_of_ae_comp (hf_meas j).ae_eq_mk] with a hi hj
    filter_upwards [hi, hj] with ω hωi hωj
    rw [← hωi, ← hωj]
  · filter_upwards [Measure.ae_ae_of_ae_comp (hf_meas k).ae_eq_mk,
      Measure.ae_ae_of_ae_comp (hf_meas l).ae_eq_mk] with a hk hl
    filter_upwards [hk, hl] with ω hωk hωl
    rw [← hωk, ← hωl]

end iIndepFun

section Mul
variable {β : Type*} {m : MeasurableSpace β} [Mul β] [MeasurableMul₂ β] {f : ι → Ω → β}

@[to_additive]
/-
**ProbabilityTheory.Kernel.iIndepFun.indepFun_mul_left** 是 Mathlib 中的一个定理，位于命名空间
 `ProbabilityTheory.Kernel.iIndepFun`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {m
Ω : MeasurableSpace Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ : MeasureTheory.M
easure α} {β : Type u_8} {m : MeasurableSpace β} [inst : Mul β]   [MeasurableMul
₂ β] {f : ι → Ω → β},   ProbabilityTheory.Kernel.iIndepFun f κ μ →     (∀ (i : ι
), Measurable (f i)) →       ∀ (i j k : ι), i ≠ k → j ≠ k → ProbabilityTheory.Ke
rnel.IndepFun (f i * f j) (f k) κ μ
参数：∀ (i : ι), Measurable (f i)；i j k : ι；f i * f j；f k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.indepFun_prodMk`：∀ {α : Type u_1} {Ω 
: Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω}   {
κ : ProbabilityTheory.Kernel α Ω} {μ : M…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CompTriple.comp_eq`：∀ {M : Type u_1} {N : Type u_2} {P : Type u_3} {φ : 
M → N} {ψ : N → P} {χ : outParam (M → P)} [self : CompTriple φ ψ χ],   ψ ∘ φ = χ
· 使用定理 `CompTriple.instIsIdId`：∀ {M : Type u_1}, CompTriple.IsId id
· 使用定理 `ProbabilityTheory.Kernel.IndepFun.comp`：∀ {α : Type u_1} {Ω : Type u_2} 
{β : Type u_4} {β' : Type u_5} {γ : Type u_6} {γ' : Type u_7} {mα : MeasurableSp
ace α}   {mΩ : MeasurableSpa…
· 使用定理 `Measurable.mul`：Measurable.mul [MeasurableMul₂ M] (hf : Measurable f) (h
g : Measurable g) : Measurable (f * g)
· 使用定理 `measurable_fst`：measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.fst : α × β -> α)
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)
-/
lemma iIndepFun.indepFun_mul_left (hf_indep : iIndepFun f κ μ)
    (hf_meas : ∀ i, Measurable (f i)) (i j k : ι) (hik : i ≠ k) (hjk : j ≠ k) :
    IndepFun (f i * f j) (f k) κ μ := by
  have : IndepFun (fun ω => (f i ω, f j ω)) (f k) κ μ :=
    hf_indep.indepFun_prodMk hf_meas i j k hik hjk
  simpa using! this.comp (measurable_fst.mul measurable_snd) measurable_id

@[to_additive]
/-
**ProbabilityTheory.Kernel.iIndepFun.indepFun_mul_left** 是 Mathlib 中的一个定理，位于命名空间
 `ProbabilityTheory.Kernel.iIndepFun`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {m
Ω : MeasurableSpace Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ : MeasureTheory.M
easure α} {β : Type u_8} {m : MeasurableSpace β} [inst : Mul β]   [MeasurableMul
₂ β] {f : ι → Ω → β},   ProbabilityTheory.Kernel.iIndepFun f κ μ →     (∀ (i : ι
), Measurable (f i)) →       ∀ (i j k : ι), i ≠ k → j ≠ k → ProbabilityTheory.Ke
rnel.IndepFun (f i * f j) (f k) κ μ
参数：∀ (i : ι), Measurable (f i)；i j k : ι；f i * f j；f k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.indepFun_prodMk`：∀ {α : Type u_1} {Ω 
: Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω}   {
κ : ProbabilityTheory.Kernel α Ω} {μ : M…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CompTriple.comp_eq`：∀ {M : Type u_1} {N : Type u_2} {P : Type u_3} {φ : 
M → N} {ψ : N → P} {χ : outParam (M → P)} [self : CompTriple φ ψ χ],   ψ ∘ φ = χ
· 使用定理 `CompTriple.instIsIdId`：∀ {M : Type u_1}, CompTriple.IsId id
· 使用定理 `ProbabilityTheory.Kernel.IndepFun.comp`：∀ {α : Type u_1} {Ω : Type u_2} 
{β : Type u_4} {β' : Type u_5} {γ : Type u_6} {γ' : Type u_7} {mα : MeasurableSp
ace α}   {mΩ : MeasurableSpa…
· 使用定理 `Measurable.mul`：Measurable.mul [MeasurableMul₂ M] (hf : Measurable f) (h
g : Measurable g) : Measurable (f * g)
· 使用定理 `measurable_fst`：measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.fst : α × β -> α)
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)
-/
lemma iIndepFun.indepFun_mul_left₀ (hf_indep : iIndepFun f κ μ)
    (hf_meas : ∀ i, AEMeasurable (f i) (κ ∘ₘ μ)) (i j k : ι) (hik : i ≠ k) (hjk : j ≠ k) :
    IndepFun (f i * f j) (f k) κ μ := by
  have : IndepFun (fun ω => (f i ω, f j ω)) (f k) κ μ :=
    hf_indep.indepFun_prodMk₀ hf_meas i j k hik hjk
  simpa using! this.comp (measurable_fst.mul measurable_snd) measurable_id

@[to_additive]
/-
**ProbabilityTheory.Kernel.iIndepFun.indepFun_mul_right** 是 Mathlib 中的一个定理，位于命名空
间 `ProbabilityTheory.Kernel.iIndepFun`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {m
Ω : MeasurableSpace Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ : MeasureTheory.M
easure α} {β : Type u_8} {m : MeasurableSpace β} [inst : Mul β]   [MeasurableMul
₂ β] {f : ι → Ω → β},   ProbabilityTheory.Kernel.iIndepFun f κ μ →     (∀ (i : ι
), Measurable (f i)) →       ∀ (i j k : ι), i ≠ j → i ≠ k → ProbabilityTheory.Ke
rnel.IndepFun (f i) (f j * f k) κ μ
参数：∀ (i : ι), Measurable (f i)；i j k : ι；f i；f j * f k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IndepFun.symm`：∀ {α : Type u_1} {Ω : Type u_2} 
{β : Type u_4} {β' : Type u_5} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω}
   {κ : ProbabilityTheory.Ke…
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.indepFun_mul_left`：∀ {α : Type u_1} {
Ω : Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω}  
 {κ : ProbabilityTheory.Kernel α Ω} {μ : M…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
lemma iIndepFun.indepFun_mul_right (hf_indep : iIndepFun f κ μ)
    (hf_meas : ∀ i, Measurable (f i)) (i j k : ι) (hij : i ≠ j) (hik : i ≠ k) :
    IndepFun (f i) (f j * f k) κ μ :=
  (hf_indep.indepFun_mul_left hf_meas _ _ _ hij.symm hik.symm).symm

@[to_additive]
/-
**ProbabilityTheory.Kernel.iIndepFun.indepFun_mul_right** 是 Mathlib 中的一个定理，位于命名空
间 `ProbabilityTheory.Kernel.iIndepFun`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {m
Ω : MeasurableSpace Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ : MeasureTheory.M
easure α} {β : Type u_8} {m : MeasurableSpace β} [inst : Mul β]   [MeasurableMul
₂ β] {f : ι → Ω → β},   ProbabilityTheory.Kernel.iIndepFun f κ μ →     (∀ (i : ι
), Measurable (f i)) →       ∀ (i j k : ι), i ≠ j → i ≠ k → ProbabilityTheory.Ke
rnel.IndepFun (f i) (f j * f k) κ μ
参数：∀ (i : ι), Measurable (f i)；i j k : ι；f i；f j * f k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IndepFun.symm`：∀ {α : Type u_1} {Ω : Type u_2} 
{β : Type u_4} {β' : Type u_5} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω}
   {κ : ProbabilityTheory.Ke…
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.indepFun_mul_left`：∀ {α : Type u_1} {
Ω : Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω}  
 {κ : ProbabilityTheory.Kernel α Ω} {μ : M…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
lemma iIndepFun.indepFun_mul_right₀ (hf_indep : iIndepFun f κ μ)
    (hf_meas : ∀ i, AEMeasurable (f i) (κ ∘ₘ μ)) (i j k : ι) (hij : i ≠ j) (hik : i ≠ k) :
    IndepFun (f i) (f j * f k) κ μ :=
  (hf_indep.indepFun_mul_left₀ hf_meas _ _ _ hij.symm hik.symm).symm

@[to_additive]
/-
**ProbabilityTheory.Kernel.iIndepFun.indepFun_mul_mul** 是 Mathlib 中的一个定理，位于命名空间 
`ProbabilityTheory.Kernel.iIndepFun`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {m
Ω : MeasurableSpace Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ : MeasureTheory.M
easure α} {β : Type u_8} {m : MeasurableSpace β} [inst : Mul β]   [MeasurableMul
₂ β] {f : ι → Ω → β},   ProbabilityTheory.Kernel.iIndepFun f κ μ →     (∀ (i : ι
), Measurable (f i)) →       ∀ (i j k l : ι), i ≠ k → i ≠ l → j ≠ k → j ≠ l → Pr
obabilityTheory.Kernel.IndepFun (f i * f j) (f k * f l) κ μ
参数：∀ (i : ι), Measurable (f i)；i j k l : ι；f i * f j；f k * f l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IndepFun.comp`：∀ {α : Type u_1} {Ω : Type u_2} 
{β : Type u_4} {β' : Type u_5} {γ : Type u_6} {γ' : Type u_7} {mα : MeasurableSp
ace α}   {mΩ : MeasurableSpa…
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.indepFun_prodMk_prodMk`：∀ {α : Type u
_1} {Ω : Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {mΩ : MeasurableSpace
 Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ : M…
· 使用定理 `MeasurableMul₂.measurable_mul`：∀ {M : Type u_2} {inst : MeasurableSpace 
M} {inst_1 : Mul M} [self : MeasurableMul₂ M], Measurable fun p => p.1 * p.2
-/
lemma iIndepFun.indepFun_mul_mul (hf_indep : iIndepFun f κ μ)
    (hf_meas : ∀ i, Measurable (f i))
    (i j k l : ι) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    IndepFun (f i * f j) (f k * f l) κ μ :=
  (hf_indep.indepFun_prodMk_prodMk hf_meas i j k l hik hil hjk hjl).comp
    measurable_mul measurable_mul

@[to_additive]
/-
**ProbabilityTheory.Kernel.iIndepFun.indepFun_mul_mul** 是 Mathlib 中的一个定理，位于命名空间 
`ProbabilityTheory.Kernel.iIndepFun`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {m
Ω : MeasurableSpace Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ : MeasureTheory.M
easure α} {β : Type u_8} {m : MeasurableSpace β} [inst : Mul β]   [MeasurableMul
₂ β] {f : ι → Ω → β},   ProbabilityTheory.Kernel.iIndepFun f κ μ →     (∀ (i : ι
), Measurable (f i)) →       ∀ (i j k l : ι), i ≠ k → i ≠ l → j ≠ k → j ≠ l → Pr
obabilityTheory.Kernel.IndepFun (f i * f j) (f k * f l) κ μ
参数：∀ (i : ι), Measurable (f i)；i j k l : ι；f i * f j；f k * f l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IndepFun.comp`：∀ {α : Type u_1} {Ω : Type u_2} 
{β : Type u_4} {β' : Type u_5} {γ : Type u_6} {γ' : Type u_7} {mα : MeasurableSp
ace α}   {mΩ : MeasurableSpa…
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.indepFun_prodMk_prodMk`：∀ {α : Type u
_1} {Ω : Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {mΩ : MeasurableSpace
 Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ : M…
· 使用定理 `MeasurableMul₂.measurable_mul`：∀ {M : Type u_2} {inst : MeasurableSpace 
M} {inst_1 : Mul M} [self : MeasurableMul₂ M], Measurable fun p => p.1 * p.2
-/
lemma iIndepFun.indepFun_mul_mul₀ (hf_indep : iIndepFun f κ μ)
    (hf_meas : ∀ i, AEMeasurable (f i) (κ ∘ₘ μ))
    (i j k l : ι) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    IndepFun (f i * f j) (f k * f l) κ μ :=
  (hf_indep.indepFun_prodMk_prodMk₀ hf_meas i j k l hik hil hjk hjl).comp
    measurable_mul measurable_mul

end Mul

section Div
variable {β : Type*} {m : MeasurableSpace β} [Div β] [MeasurableDiv₂ β] {f : ι → Ω → β}

@[to_additive]
/-
**ProbabilityTheory.Kernel.iIndepFun.indepFun_div_left** 是 Mathlib 中的一个定理，位于命名空间
 `ProbabilityTheory.Kernel.iIndepFun`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {m
Ω : MeasurableSpace Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ : MeasureTheory.M
easure α} {β : Type u_8} {m : MeasurableSpace β} [inst : Div β]   [MeasurableDiv
₂ β] {f : ι → Ω → β},   ProbabilityTheory.Kernel.iIndepFun f κ μ →     (∀ (i : ι
), Measurable (f i)) →       ∀ (i j k : ι), i ≠ k → j ≠ k → ProbabilityTheory.Ke
rnel.IndepFun (f i / f j) (f k) κ μ
参数：∀ (i : ι), Measurable (f i)；i j k : ι；f i / f j；f k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.indepFun_prodMk`：∀ {α : Type u_1} {Ω 
: Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω}   {
κ : ProbabilityTheory.Kernel α Ω} {μ : M…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CompTriple.comp_eq`：∀ {M : Type u_1} {N : Type u_2} {P : Type u_3} {φ : 
M → N} {ψ : N → P} {χ : outParam (M → P)} [self : CompTriple φ ψ χ],   ψ ∘ φ = χ
· 使用定理 `CompTriple.instIsIdId`：∀ {M : Type u_1}, CompTriple.IsId id
· 使用定理 `ProbabilityTheory.Kernel.IndepFun.comp`：∀ {α : Type u_1} {Ω : Type u_2} 
{β : Type u_4} {β' : Type u_5} {γ : Type u_6} {γ' : Type u_7} {mα : MeasurableSp
ace α}   {mΩ : MeasurableSpa…
· 使用定理 `Measurable.div`：Measurable.div [MeasurableDiv₂ G] (hf : Measurable f) (h
g : Measurable g) : Measurable (f / g)
· 使用定理 `measurable_fst`：measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.fst : α × β -> α)
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)
-/
lemma iIndepFun.indepFun_div_left (hf_indep : iIndepFun f κ μ)
    (hf_meas : ∀ i, Measurable (f i)) (i j k : ι) (hik : i ≠ k) (hjk : j ≠ k) :
    IndepFun (f i / f j) (f k) κ μ := by
  have : IndepFun (fun ω => (f i ω, f j ω)) (f k) κ μ :=
    hf_indep.indepFun_prodMk hf_meas i j k hik hjk
  simpa using! this.comp (measurable_fst.div measurable_snd) measurable_id

@[to_additive]
/-
**ProbabilityTheory.Kernel.iIndepFun.indepFun_div_left** 是 Mathlib 中的一个定理，位于命名空间
 `ProbabilityTheory.Kernel.iIndepFun`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {m
Ω : MeasurableSpace Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ : MeasureTheory.M
easure α} {β : Type u_8} {m : MeasurableSpace β} [inst : Div β]   [MeasurableDiv
₂ β] {f : ι → Ω → β},   ProbabilityTheory.Kernel.iIndepFun f κ μ →     (∀ (i : ι
), Measurable (f i)) →       ∀ (i j k : ι), i ≠ k → j ≠ k → ProbabilityTheory.Ke
rnel.IndepFun (f i / f j) (f k) κ μ
参数：∀ (i : ι), Measurable (f i)；i j k : ι；f i / f j；f k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.indepFun_prodMk`：∀ {α : Type u_1} {Ω 
: Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω}   {
κ : ProbabilityTheory.Kernel α Ω} {μ : M…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CompTriple.comp_eq`：∀ {M : Type u_1} {N : Type u_2} {P : Type u_3} {φ : 
M → N} {ψ : N → P} {χ : outParam (M → P)} [self : CompTriple φ ψ χ],   ψ ∘ φ = χ
· 使用定理 `CompTriple.instIsIdId`：∀ {M : Type u_1}, CompTriple.IsId id
· 使用定理 `ProbabilityTheory.Kernel.IndepFun.comp`：∀ {α : Type u_1} {Ω : Type u_2} 
{β : Type u_4} {β' : Type u_5} {γ : Type u_6} {γ' : Type u_7} {mα : MeasurableSp
ace α}   {mΩ : MeasurableSpa…
· 使用定理 `Measurable.div`：Measurable.div [MeasurableDiv₂ G] (hf : Measurable f) (h
g : Measurable g) : Measurable (f / g)
· 使用定理 `measurable_fst`：measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.fst : α × β -> α)
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)
-/
lemma iIndepFun.indepFun_div_left₀ (hf_indep : iIndepFun f κ μ)
    (hf_meas : ∀ i, AEMeasurable (f i) (κ ∘ₘ μ)) (i j k : ι) (hik : i ≠ k) (hjk : j ≠ k) :
    IndepFun (f i / f j) (f k) κ μ := by
  have : IndepFun (fun ω => (f i ω, f j ω)) (f k) κ μ :=
    hf_indep.indepFun_prodMk₀ hf_meas i j k hik hjk
  simpa using! this.comp (measurable_fst.div measurable_snd) measurable_id

@[to_additive]
/-
**ProbabilityTheory.Kernel.iIndepFun.indepFun_div_right** 是 Mathlib 中的一个定理，位于命名空
间 `ProbabilityTheory.Kernel.iIndepFun`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {m
Ω : MeasurableSpace Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ : MeasureTheory.M
easure α} {β : Type u_8} {m : MeasurableSpace β} [inst : Div β]   [MeasurableDiv
₂ β] {f : ι → Ω → β},   ProbabilityTheory.Kernel.iIndepFun f κ μ →     (∀ (i : ι
), Measurable (f i)) →       ∀ (i j k : ι), i ≠ j → i ≠ k → ProbabilityTheory.Ke
rnel.IndepFun (f i) (f j / f k) κ μ
参数：∀ (i : ι), Measurable (f i)；i j k : ι；f i；f j / f k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IndepFun.symm`：∀ {α : Type u_1} {Ω : Type u_2} 
{β : Type u_4} {β' : Type u_5} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω}
   {κ : ProbabilityTheory.Ke…
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.indepFun_div_left`：∀ {α : Type u_1} {
Ω : Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω}  
 {κ : ProbabilityTheory.Kernel α Ω} {μ : M…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
lemma iIndepFun.indepFun_div_right (hf_indep : iIndepFun f κ μ)
    (hf_meas : ∀ i, Measurable (f i)) (i j k : ι) (hij : i ≠ j) (hik : i ≠ k) :
    IndepFun (f i) (f j / f k) κ μ :=
  (hf_indep.indepFun_div_left hf_meas _ _ _ hij.symm hik.symm).symm

@[to_additive]
/-
**ProbabilityTheory.Kernel.iIndepFun.indepFun_div_right** 是 Mathlib 中的一个定理，位于命名空
间 `ProbabilityTheory.Kernel.iIndepFun`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {m
Ω : MeasurableSpace Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ : MeasureTheory.M
easure α} {β : Type u_8} {m : MeasurableSpace β} [inst : Div β]   [MeasurableDiv
₂ β] {f : ι → Ω → β},   ProbabilityTheory.Kernel.iIndepFun f κ μ →     (∀ (i : ι
), Measurable (f i)) →       ∀ (i j k : ι), i ≠ j → i ≠ k → ProbabilityTheory.Ke
rnel.IndepFun (f i) (f j / f k) κ μ
参数：∀ (i : ι), Measurable (f i)；i j k : ι；f i；f j / f k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IndepFun.symm`：∀ {α : Type u_1} {Ω : Type u_2} 
{β : Type u_4} {β' : Type u_5} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω}
   {κ : ProbabilityTheory.Ke…
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.indepFun_div_left`：∀ {α : Type u_1} {
Ω : Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω}  
 {κ : ProbabilityTheory.Kernel α Ω} {μ : M…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
lemma iIndepFun.indepFun_div_right₀ (hf_indep : iIndepFun f κ μ)
    (hf_meas : ∀ i, AEMeasurable (f i) (κ ∘ₘ μ)) (i j k : ι) (hij : i ≠ j) (hik : i ≠ k) :
    IndepFun (f i) (f j / f k) κ μ :=
  (hf_indep.indepFun_div_left₀ hf_meas _ _ _ hij.symm hik.symm).symm

@[to_additive]
/-
**ProbabilityTheory.Kernel.iIndepFun.indepFun_div_div** 是 Mathlib 中的一个定理，位于命名空间 
`ProbabilityTheory.Kernel.iIndepFun`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {m
Ω : MeasurableSpace Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ : MeasureTheory.M
easure α} {β : Type u_8} {m : MeasurableSpace β} [inst : Div β]   [MeasurableDiv
₂ β] {f : ι → Ω → β},   ProbabilityTheory.Kernel.iIndepFun f κ μ →     (∀ (i : ι
), Measurable (f i)) →       ∀ (i j k l : ι), i ≠ k → i ≠ l → j ≠ k → j ≠ l → Pr
obabilityTheory.Kernel.IndepFun (f i / f j) (f k / f l) κ μ
参数：∀ (i : ι), Measurable (f i)；i j k l : ι；f i / f j；f k / f l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IndepFun.comp`：∀ {α : Type u_1} {Ω : Type u_2} 
{β : Type u_4} {β' : Type u_5} {γ : Type u_6} {γ' : Type u_7} {mα : MeasurableSp
ace α}   {mΩ : MeasurableSpa…
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.indepFun_prodMk_prodMk`：∀ {α : Type u
_1} {Ω : Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {mΩ : MeasurableSpace
 Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ : M…
· 使用定理 `MeasurableDiv₂.measurable_div`：∀ {G₀ : Type u_2} {inst : MeasurableSpace
 G₀} {inst_1 : Div G₀} [self : MeasurableDiv₂ G₀],   Measurable fun p => p.1 / p
.2
-/
lemma iIndepFun.indepFun_div_div (hf_indep : iIndepFun f κ μ)
    (hf_meas : ∀ i, Measurable (f i))
    (i j k l : ι) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    IndepFun (f i / f j) (f k / f l) κ μ :=
  (hf_indep.indepFun_prodMk_prodMk hf_meas i j k l hik hil hjk hjl).comp
    measurable_div measurable_div

@[to_additive]
/-
**ProbabilityTheory.Kernel.iIndepFun.indepFun_div_div** 是 Mathlib 中的一个定理，位于命名空间 
`ProbabilityTheory.Kernel.iIndepFun`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {m
Ω : MeasurableSpace Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ : MeasureTheory.M
easure α} {β : Type u_8} {m : MeasurableSpace β} [inst : Div β]   [MeasurableDiv
₂ β] {f : ι → Ω → β},   ProbabilityTheory.Kernel.iIndepFun f κ μ →     (∀ (i : ι
), Measurable (f i)) →       ∀ (i j k l : ι), i ≠ k → i ≠ l → j ≠ k → j ≠ l → Pr
obabilityTheory.Kernel.IndepFun (f i / f j) (f k / f l) κ μ
参数：∀ (i : ι), Measurable (f i)；i j k l : ι；f i / f j；f k / f l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IndepFun.comp`：∀ {α : Type u_1} {Ω : Type u_2} 
{β : Type u_4} {β' : Type u_5} {γ : Type u_6} {γ' : Type u_7} {mα : MeasurableSp
ace α}   {mΩ : MeasurableSpa…
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.indepFun_prodMk_prodMk`：∀ {α : Type u
_1} {Ω : Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {mΩ : MeasurableSpace
 Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ : M…
· 使用定理 `MeasurableDiv₂.measurable_div`：∀ {G₀ : Type u_2} {inst : MeasurableSpace
 G₀} {inst_1 : Div G₀} [self : MeasurableDiv₂ G₀],   Measurable fun p => p.1 / p
.2
-/
lemma iIndepFun.indepFun_div_div₀ (hf_indep : iIndepFun f κ μ)
    (hf_meas : ∀ i, AEMeasurable (f i) (κ ∘ₘ μ))
    (i j k l : ι) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    IndepFun (f i / f j) (f k / f l) κ μ :=
  (hf_indep.indepFun_prodMk_prodMk₀ hf_meas i j k l hik hil hjk hjl).comp
    measurable_div measurable_div

end Div

section CommMonoid
variable {β : Type*} {m : MeasurableSpace β} [CommMonoid β] [MeasurableMul₂ β] {f : ι → Ω → β}

@[to_additive]
/-
**ProbabilityTheory.Kernel.iIndepFun.indepFun_finsetProd_of_notMem** 是 Mathlib 中
的一个定理，位于命名空间 `ProbabilityTheory.Kernel.iIndepFun`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {m
Ω : MeasurableSpace Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ : MeasureTheory.M
easure α} {β : Type u_8} {m : MeasurableSpace β}   [inst : CommMonoid β] [Measur
ableMul₂ β] {f : ι → Ω → β},   ProbabilityTheory.Kernel.iIndepFun f κ μ →     (∀
 (i : ι), Measurable (f i)) →       ∀ {s : Finset ι} {i : ι}, i ∉ s → Probabilit
yTheory.Kernel.IndepFun (∏ j ∈ s, f j) (f i) κ μ
参数：∀ (i : ι), Measurable (f i)；∏ j ∈ s, f j；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_singleton_self`：mem_singleton_self (a : α) : a in ({a} : Fins
et α)
· 使用定理 `measurable_pi_apply`：measurable_pi_apply (a : δ) : Measurable fun f : fo
rall a, X a => f a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_apply`：Finset.prod_apply {α : Type*} {M : α -> Type*} [foral
l a, CommMonoid (M a)] (a : α) (s : Finset ι) (g : ι -> forall a, M a) : (∏ c in
 s, g c…
· 使用定理 `Finset.prod_coe_sort`：prod_coe_sort : ∏ i : s, f i = ∏ i in s, f i
· 使用定理 `Finset.measurable_fun_prod`：Finset.measurable_fun_prod (s : Finset ι) (h
f : forall i in s, Measurable (f i)) : Measurable fun a => ∏ i in s, f i a
· 使用定理 `ProbabilityTheory.Kernel.IndepFun.comp`：∀ {α : Type u_1} {Ω : Type u_2} 
{β : Type u_4} {β' : Type u_5} {γ : Type u_6} {γ' : Type u_7} {mα : MeasurableSp
ace α}   {mΩ : MeasurableSpa…
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.indepFun_finset`：∀ {α : Type u_1} {Ω 
: Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω}   {
κ : ProbabilityTheory.Kernel α Ω} {μ : M…
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.disjoint_singleton_left`：disjoint_singleton_left : Disjoint (sing
leton a) s ↔ a ∉ s
-/
theorem iIndepFun.indepFun_finsetProd_of_notMem (hf_Indep : iIndepFun f κ μ)
    (hf_meas : ∀ i, Measurable (f i)) {s : Finset ι} {i : ι} (hi : i ∉ s) :
    IndepFun (∏ j ∈ s, f j) (f i) κ μ := by
  have h_right : f i =
    (fun p : ({i} : Finset ι) → β => p ⟨i, Finset.mem_singleton_self i⟩) ∘
    fun a (j : ({i} : Finset ι)) => f j a := rfl
  have h_meas_right : Measurable fun p : ({i} : Finset ι) → β =>
      p ⟨i, Finset.mem_singleton_self i⟩ := measurable_pi_apply _
  have h_left : ∏ j ∈ s, f j = (fun p : s → β => ∏ j, p j) ∘ fun a (j : s) => f j a := by
    ext1 a
    simp only [Function.comp_apply]
    have : (∏ j : ↥s, f (↑j) a) = (∏ j : ↥s, f ↑j) a := by rw [Finset.prod_apply]
    rw [this, Finset.prod_coe_sort]
  have h_meas_left : Measurable fun p : s → β => ∏ j, p j :=
    Finset.univ.measurable_fun_prod fun (j : ↥s) (_H : j ∈ Finset.univ) => measurable_pi_apply j
  rw [h_left, h_right]
  exact
    (hf_Indep.indepFun_finset s {i} (Finset.disjoint_singleton_left.mpr hi).symm hf_meas).comp
      h_meas_left h_meas_right

@[deprecated (since := "2026-04-08")]
alias iIndepFun.indepFun_finset_sum_of_notMem := iIndepFun.indepFun_finsetSum_of_notMem

@[to_additive existing, deprecated (since := "2026-04-08")]
alias iIndepFun.indepFun_finset_prod_of_notMem := iIndepFun.indepFun_finsetProd_of_notMem

@[to_additive]
/-
**ProbabilityTheory.Kernel.iIndepFun.indepFun_finsetProd_of_notMem** 是 Mathlib 中
的一个定理，位于命名空间 `ProbabilityTheory.Kernel.iIndepFun`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {m
Ω : MeasurableSpace Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ : MeasureTheory.M
easure α} {β : Type u_8} {m : MeasurableSpace β}   [inst : CommMonoid β] [Measur
ableMul₂ β] {f : ι → Ω → β},   ProbabilityTheory.Kernel.iIndepFun f κ μ →     (∀
 (i : ι), Measurable (f i)) →       ∀ {s : Finset ι} {i : ι}, i ∉ s → Probabilit
yTheory.Kernel.IndepFun (∏ j ∈ s, f j) (f i) κ μ
参数：∀ (i : ι), Measurable (f i)；∏ j ∈ s, f j；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_singleton_self`：mem_singleton_self (a : α) : a in ({a} : Fins
et α)
· 使用定理 `measurable_pi_apply`：measurable_pi_apply (a : δ) : Measurable fun f : fo
rall a, X a => f a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_apply`：Finset.prod_apply {α : Type*} {M : α -> Type*} [foral
l a, CommMonoid (M a)] (a : α) (s : Finset ι) (g : ι -> forall a, M a) : (∏ c in
 s, g c…
· 使用定理 `Finset.prod_coe_sort`：prod_coe_sort : ∏ i : s, f i = ∏ i in s, f i
· 使用定理 `Finset.measurable_fun_prod`：Finset.measurable_fun_prod (s : Finset ι) (h
f : forall i in s, Measurable (f i)) : Measurable fun a => ∏ i in s, f i a
· 使用定理 `ProbabilityTheory.Kernel.IndepFun.comp`：∀ {α : Type u_1} {Ω : Type u_2} 
{β : Type u_4} {β' : Type u_5} {γ : Type u_6} {γ' : Type u_7} {mα : MeasurableSp
ace α}   {mΩ : MeasurableSpa…
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.indepFun_finset`：∀ {α : Type u_1} {Ω 
: Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω}   {
κ : ProbabilityTheory.Kernel α Ω} {μ : M…
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.disjoint_singleton_left`：disjoint_singleton_left : Disjoint (sing
leton a) s ↔ a ∉ s
-/
theorem iIndepFun.indepFun_finsetProd_of_notMem₀ (hf_Indep : iIndepFun f κ μ)
    (hf_meas : ∀ i, AEMeasurable (f i) (κ ∘ₘ μ)) {s : Finset ι} {i : ι} (hi : i ∉ s) :
    IndepFun (∏ j ∈ s, f j) (f i) κ μ := by
  have h : IndepFun (∏ j ∈ s, (hf_meas j).mk (f j)) ((hf_meas i).mk (f i)) κ μ := by
    refine iIndepFun.indepFun_finsetProd_of_notMem ?_ (fun i ↦ (hf_meas i).measurable_mk) hi
    exact iIndepFun.congr' hf_Indep fun i ↦ Measure.ae_ae_of_ae_comp (hf_meas i).ae_eq_mk
  refine IndepFun.congr' h ?_ ?_
  · have : ∀ᵐ a ∂μ, ∀ (i : s), f i =ᵐ[κ a] (hf_meas i).mk := by
      rw [ae_all_iff]
      exact fun i ↦ Measure.ae_ae_of_ae_comp (hf_meas i).ae_eq_mk
    filter_upwards [this] with a ha
    filter_upwards [ae_all_iff.2 ha] with ω hω
    simp only [Finset.prod_apply]
    exact Finset.prod_congr rfl fun i hi ↦ (hω ⟨i, hi⟩).symm
  · exact Measure.ae_ae_of_ae_comp (hf_meas i).ae_eq_mk.symm

@[deprecated (since := "2026-04-08")]
alias iIndepFun.indepFun_finset_sum_of_notMem₀ := iIndepFun.indepFun_finsetSum_of_notMem₀

@[to_additive existing, deprecated (since := "2026-04-08")]
alias iIndepFun.indepFun_finset_prod_of_notMem₀ := iIndepFun.indepFun_finsetProd_of_notMem₀


@[to_additive]
/-
**ProbabilityTheory.Kernel.iIndepFun.indepFun_prod_range_succ** 是 Mathlib 中的一个定理
，位于命名空间 `ProbabilityTheory.Kernel.iIndepFun`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {mα : MeasurableSpace α} {mΩ : MeasurableS
pace Ω} {κ : ProbabilityTheory.Kernel α Ω}   {μ : MeasureTheory.Measure α} {β : 
Type u_8} {m : MeasurableSpace β} [inst : CommMonoid β] [MeasurableMul₂ β]   {f 
: ℕ → Ω → β},   ProbabilityTheory.Kernel.iIndepFun f κ μ →     (∀ (i : ℕ), Measu
rable (f i)) → ∀ (n : ℕ), ProbabilityTheory.Kernel.IndepFun (∏ j ∈ Finset.range 
n, f j) (f n) κ μ
参数：∀ (i : ℕ), Measurable (f i)；n : ℕ；∏ j ∈ Finset.range n, f j；f n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.indepFun_finsetProd_of_notMem`：∀ {α :
 Type u_1} {Ω : Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {mΩ : Measurab
leSpace Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ : M…
· 使用定理 `Finset.notMem_range_self`：notMem_range_self : n ∉ range n
-/
theorem iIndepFun.indepFun_prod_range_succ {f : ℕ → Ω → β}
    (hf_Indep : iIndepFun f κ μ) (hf_meas : ∀ i, Measurable (f i)) (n : ℕ) :
    IndepFun (∏ j ∈ Finset.range n, f j) (f n) κ μ :=
  hf_Indep.indepFun_finsetProd_of_notMem hf_meas Finset.notMem_range_self

@[to_additive]
/-
**ProbabilityTheory.Kernel.iIndepFun.indepFun_prod_range_succ** 是 Mathlib 中的一个定理
，位于命名空间 `ProbabilityTheory.Kernel.iIndepFun`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {mα : MeasurableSpace α} {mΩ : MeasurableS
pace Ω} {κ : ProbabilityTheory.Kernel α Ω}   {μ : MeasureTheory.Measure α} {β : 
Type u_8} {m : MeasurableSpace β} [inst : CommMonoid β] [MeasurableMul₂ β]   {f 
: ℕ → Ω → β},   ProbabilityTheory.Kernel.iIndepFun f κ μ →     (∀ (i : ℕ), Measu
rable (f i)) → ∀ (n : ℕ), ProbabilityTheory.Kernel.IndepFun (∏ j ∈ Finset.range 
n, f j) (f n) κ μ
参数：∀ (i : ℕ), Measurable (f i)；n : ℕ；∏ j ∈ Finset.range n, f j；f n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.indepFun_finsetProd_of_notMem`：∀ {α :
 Type u_1} {Ω : Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {mΩ : Measurab
leSpace Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ : M…
· 使用定理 `Finset.notMem_range_self`：notMem_range_self : n ∉ range n
-/
theorem iIndepFun.indepFun_prod_range_succ₀ {f : ℕ → Ω → β}
    (hf_Indep : iIndepFun f κ μ) (hf_meas : ∀ i, AEMeasurable (f i) (κ ∘ₘ μ)) (n : ℕ) :
    IndepFun (∏ j ∈ Finset.range n, f j) (f n) κ μ :=
  hf_Indep.indepFun_finsetProd_of_notMem₀ hf_meas Finset.notMem_range_self

end CommMonoid

/-
**ProbabilityTheory.Kernel.iIndepSet.iIndepFun_indicator** 是 Mathlib 中的一个定理，位于命名
空间 `ProbabilityTheory.Kernel.iIndepSet`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {β : Type u_4} {mα : Measur
ableSpace α} {mΩ : MeasurableSpace Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ : 
MeasureTheory.Measure α} [inst : Zero β] [inst_1 : One β]   {m : MeasurableSpace
 β} {s : ι → Set Ω},   ProbabilityTheory.Kernel.iIndepSet s κ μ →     Probabilit
yTheory.Kernel.iIndepFun (fun n => (s n).indicator fun _ω => 1) κ μ
参数：fun n => (s n).indicator fun _ω => 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun_iff_measure_inter_preimage_eq_mul`：iI
ndepFun_iff_measure_inter_preimage_eq_mul {ι : Type*} {β : ι -> Type*} (m : fora
ll x, MeasurableSpace (β x)) (f : forall i, Ω -> β i) : iI…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.indicator_const_preimage_eq_union`：∀ {α : Type u_1} {M : Type u_3} [
inst : Zero M] (U : Set α) (s : Set M) (a : M) [inst_1 : Decidable (a ∈ s)]   [i
nst_2 : Decidable (0 ∈ s)],…
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `MeasurableSpace.measurableSet_generateFrom`：measurableSet_generateFrom {
s : Set (Set α)} {t : Set α} (ht : t in s) : MeasurableSet[generateFrom s] t
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用定理 `MeasurableSet.union`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∪ s₂)
· 使用定理 `MeasurableSet.ite'`：MeasurableSet.ite' {s t : Set α} {p : Prop} (hs : p 
-> MeasurableSet s) (ht : ¬p -> MeasurableSet t) : MeasurableSet (ite p s t)
· 使用定理 `MeasurableSet.empty`：MeasurableSet.empty [MeasurableSpace α] : Measurabl
eSet (∅ : Set α)
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
-/
theorem iIndepSet.iIndepFun_indicator [Zero β] [One β] {m : MeasurableSpace β} {s : ι → Set Ω}
    (hs : iIndepSet s κ μ) :
    iIndepFun (fun n => (s n).indicator fun _ω => (1 : β)) κ μ := by
  classical
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  rintro S π _hπ
  simp_rw [Set.indicator_const_preimage_eq_union]
  apply hs _ fun i _hi ↦ ?_
  have hsi : MeasurableSet[generateFrom {s i}] (s i) :=
    measurableSet_generateFrom (Set.mem_singleton _)
  refine
    MeasurableSet.union (MeasurableSet.ite' (fun _ => hsi) fun _ => ?_)
      (MeasurableSet.ite' (fun _ => hsi.compl) fun _ => ?_)
  · exact @MeasurableSet.empty _ (generateFrom {s i})
  · exact @MeasurableSet.empty _ (generateFrom {s i})
/-
**ProbabilityTheory.Kernel.Indep.indicator_const_indepFun** 是 Mathlib 中的一个定理，位于命
名空间 `ProbabilityTheory.Kernel.Indep`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {mα : MeasurableSpace α} {mΩ : MeasurableS
pace Ω} {κ : ProbabilityTheory.Kernel α Ω}   {μ : MeasureTheory.Measure α} {m : 
MeasurableSpace Ω} {M : Type u_8} {𝓧 : Type u_9} [inst : Zero M]   [inst_1 : Mea
surableSpace M] (c : M) {m𝓧 : MeasurableSpace 𝓧} {A : Set Ω} {X : Ω → 𝓧},   Meas
urableSet A →     ProbabilityTheory.Kernel.Indep m (MeasurableSpace.comap X m𝓧) 
κ μ →       ProbabilityTheory.Kernel.IndepFun (A.indicator fun x => c) X κ μ
参数：c : M；MeasurableSpace.comap X m𝓧；A.indicator fun x => c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.indep_of_indep_of_le_left`：indep_of_indep_of_le
_left {m₁ m₂ m₃ : MeasurableSpace Ω} {_mΩ : MeasurableSpace Ω} {κ : Kernel α Ω} 
{μ : Measure α} (h_indep : Indep m₁ m₂ κ…
· 使用定理 `Measurable.comap_le`：∀ {α : Type u_1} {β : Type u_2} {m₁ : MeasurableSpa
ce α} {m₂ : MeasurableSpace β} {f : α → β},   Measurable f → MeasurableSpace.com
ap f m₂ ≤…
· 使用定理 `Measurable.indicator`：Measurable.indicator [Zero β] (hf : Measurable f) 
(hs : MeasurableSet s) : Measurable (s.indicator f)
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
-/
lemma Indep.indicator_const_indepFun {m : MeasurableSpace Ω} {M 𝓧 : Type*}
    [Zero M] [MeasurableSpace M] (c : M) {m𝓧 : MeasurableSpace 𝓧} {A : Set Ω}
    {X : Ω → 𝓧} (hA : MeasurableSet[m] A) (h : Indep m (m𝓧.comap X) κ μ) :
    IndepFun (A.indicator (fun _ ↦ c)) X κ μ :=
  indep_of_indep_of_le_left h (measurable_const.indicator hA).comap_le

variable {mβ : MeasurableSpace β} {X : ι → Ω → α} {Y : ι → Ω → β}
  {f : _ → Set Ω} {t : ι → Set β} {s : Finset ι}

/-- The probability of an intersection of preimages conditioning on another intersection factors
into a product. -/
/-
**ProbabilityTheory.Kernel.iIndepFun.cond_iInter** 是 Mathlib 中的一个定理，位于命名空间 `Prob
abilityTheory.Kernel.iIndepFun`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {β : Type u_4} {mα : Measur
ableSpace α} {mΩ : MeasurableSpace Ω}   {κ : ProbabilityTheory.Kernel α Ω} {μ : 
MeasureTheory.Measure α} {mβ : MeasurableSpace β} {X : ι → Ω → α}   {Y : ι → Ω →
 β} {f : ι → Set Ω} {t : ι → Set β} {s : Finset ι} [Finite ι],   (∀ (i : ι), Mea
surable (Y i)) →     ProbabilityTheory.Kernel.iIndepFun (fun i ω => (X i ω, Y i 
ω)) κ μ →       (∀ i ∈ s, MeasurableSet (f i)) →         (∀ᵐ (a : α) ∂μ, ∀ i ∉ s
, (κ a) (Y i ⁻¹' t i) ≠ 0) →           (∀ (i : ι), MeasurableSet (t i)) →       
      ∀ᵐ (a : α) ∂μ, (κ a)[⋂ i ∈ s, f i | ⋂ i, Y i ⁻¹' t i] = ∏ i ∈ s, (κ a)[f i
 | Y i ⁻¹' t i]
参数：∀ (i : ι), Measurable (Y i)；fun i ω => (X i ω, Y i ω)；∀ i ∈ s, MeasurableSet 
(f i)；∀ᵐ (a : α) ∂μ, ∀ i ∉ s, (κ a) (Y i ⁻¹' t i) ≠ 0；∀ (i : ι), MeasurableSet (
t i)；a : α；κ a；κ a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `MeasurableSet.prod`：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace
 α} {mβ : MeasurableSpace β} {s : Set α} {t : Set β},   MeasurableSet s → Measur
ableSet …
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.meas_iInter`：∀ {α : Type u_1} {Ω : Ty
pe u_2} {ι : Type u_3} {β : ι → Type u_8} {mβ : (i : ι) → MeasurableSpace (β i)}
   {_mα : MeasurableSpace α} {_mΩ : …
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.ae_isProbabilityMeasure`：∀ {α : Type 
u_1} {Ω : Type u_2} {ι : Type u_3} {β : ι → Type u_8} {mβ : (i : ι) → Measurable
Space (β i)}   {_mα : MeasurableSpace α} {_mΩ : …
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `ProbabilityTheory.cond_apply`：cond_apply (hms : MeasurableSet s) (μ : Me
asure Ω) (t : Set Ω) : μ[t | s] = (μ s)⁻¹ * μ (s inter t)
· 使用定理 `MeasurableSet.iInter`：MeasurableSet.iInter [Countable ι] {f : ι -> Set α
} (h : forall b, MeasurableSet (f b)) : MeasurableSet (⋂ b, f b)
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Set.iInter_ite`：iInter_ite (f g : ι -> Set α) : ⋂ i, (if p i then f i el
se g i) = (⋂ (i) (_ : p i), f i) inter ⋂ (i) (_ : ¬p i), g i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
（共 44 条，此处仅展示前 30 条）

--- 原说明 ---
The probability of an intersection of preimages conditioning on another intersec
tion factors
into a product.
-/
lemma iIndepFun.cond_iInter [Finite ι] (hY : ∀ i, Measurable (Y i))
    (hindep : iIndepFun (fun i ω ↦ (X i ω, Y i ω)) κ μ)
    (hf : ∀ i ∈ s, MeasurableSet[mα.comap (X i)] (f i))
    (hy : ∀ᵐ a ∂μ, ∀ i ∉ s, κ a (Y i ⁻¹' t i) ≠ 0) (ht : ∀ i, MeasurableSet (t i)) :
    ∀ᵐ a ∂μ, (κ a)[⋂ i ∈ s, f i | ⋂ i, Y i ⁻¹' t i] = ∏ i ∈ s, (κ a)[f i | Y i in t i] := by
  classical
  cases nonempty_fintype ι
  let g (i' : ι) := if i' ∈ s then Y i' ⁻¹' t i' ∩ f i' else Y i' ⁻¹' t i'
  have hYt i : MeasurableSet[(mα.prod mβ).comap fun ω ↦ (X i ω, Y i ω)] (Y i ⁻¹' t i) :=
    ⟨.univ ×ˢ t i, .prod .univ (ht _), by ext; simp⟩
  have hg i : MeasurableSet[(mα.prod mβ).comap fun ω ↦ (X i ω, Y i ω)] (g i) := by
    by_cases hi : i ∈ s <;> simp only [hi, ↓reduceIte, g]
    · obtain ⟨A, hA, hA'⟩ := hf i hi
      exact (hYt _).inter ⟨A ×ˢ .univ, hA.prod .univ, by ext; simp [← hA']⟩
    · exact hYt _
  filter_upwards [hy, hindep.ae_isProbabilityMeasure, hindep.meas_iInter hYt, hindep.meas_iInter hg]
    with a hy _ hYt hg
  calc
    _ = (κ a (⋂ i, Y i ⁻¹' t i))⁻¹ * κ a ((⋂ i, Y i ⁻¹' t i) ∩ ⋂ i ∈ s, f i) := by
      rw [cond_apply]; exact .iInter fun i ↦ hY i (ht i)
    _ = (κ a (⋂ i, Y i ⁻¹' t i))⁻¹ * κ a (⋂ i, g i) := by
      congr 2
      calc
        _ = (⋂ i, Y i ⁻¹' t i) ∩ ⋂ i, if i ∈ s then f i else .univ := by
          congr 1
          simp only [Set.iInter_ite, Set.iInter_univ, Set.inter_univ]
        _ = ⋂ i, Y i ⁻¹' t i ∩ (if i ∈ s then f i else .univ) := by rw [Set.iInter_inter_distrib]
        _ = _ := Set.iInter_congr fun i ↦ by by_cases hi : i ∈ s <;> simp [hi, g]
    _ = (∏ i, κ a (Y i ⁻¹' t i))⁻¹ * κ a (⋂ i, g i) := by
      rw [hYt]
    _ = (∏ i, κ a (Y i ⁻¹' t i))⁻¹ * ∏ i, κ a (g i) := by
      rw [hg]
    _ = ∏ i, (κ a (Y i ⁻¹' t i))⁻¹ * κ a (g i) := by
      rw [Finset.prod_mul_distrib, ENNReal.prod_inv_distrib]
      exact fun _ _ i _ _ ↦ .inr <| measure_ne_top _ _
    _ = ∏ i, if i ∈ s then (κ a)[f i | Y i ⁻¹' t i] else 1 := by
      refine Finset.prod_congr rfl fun i _ ↦ ?_
      by_cases hi : i ∈ s
      · simp only [hi, ↓reduceIte, g, cond_apply (hY i (ht i))]
      · simp only [hi, ↓reduceIte, g, ENNReal.inv_mul_cancel (hy i hi) (measure_ne_top _ _)]
    _ = _ := by simp

-- TODO: We can't state `Kernel.iIndepFun.cond` (the `Kernel` analogue of
-- `ProbabilityTheory.iIndepFun.cond`) because we don't have a version of `ProbabilityTheory.cond`
-- for kernels

end ProbabilityTheory.Kernel

