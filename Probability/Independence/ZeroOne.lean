/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Independence.Conditional

/-!
# Kolmogorov's 0-1 law

Let `s : ι → MeasurableSpace Ω` be an independent sequence of sub-σ-algebras. Then any set which
is measurable with respect to the tail σ-algebra `limsup s atTop` has probability 0 or 1.

## Main statements

* `measure_zero_or_one_of_measurableSet_limsup_atTop`: Kolmogorov's 0-1 law. Any set which is
  measurable with respect to the tail σ-algebra `limsup s atTop` of an independent sequence of
  σ-algebras `s` has probability 0 or 1.
-/

public section

open MeasureTheory MeasurableSpace

open scoped MeasureTheory ENNReal

namespace ProbabilityTheory

variable {α Ω ι : Type*} {_mα : MeasurableSpace α} {s : ι → MeasurableSpace Ω}
  {m m0 : MeasurableSpace Ω} {κ : Kernel α Ω} {μα : Measure α} {μ : Measure Ω}

/-
**ProbabilityTheory.Kernel.measure_eq_zero_or_one_or_top_of_indepSet_self** 是 Ma
thlib 中的一个定理，位于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {_mα : MeasurableSpace α} {m0 : Measurable
Space Ω} {κ : ProbabilityTheory.Kernel α Ω}   {μα : MeasureTheory.Measure α} {t 
: Set Ω},   ProbabilityTheory.Kernel.IndepSet t t κ μα → ∀ᵐ (a : α) ∂μα, (κ a) t
 = 0 ∨ (κ a) t = 1 ∨ (κ a) t = ⊤
参数：a : α；κ a；κ a；κ a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasurableSpace.measurableSet_generateFrom`：measurableSet_generateFrom {
s : Set (Set α)} {t : Set α} (ht : t in s) : MeasurableSet[generateFrom s] t
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.mul_left_inj`：∀ {a b c : ENNReal}, c ≠ 0 → c ≠ ⊤ → (a * c = b * 
c ↔ a = b)
· 使用定理 `Set.inter_self`：inter_self (a : Set α) : a inter a = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem Kernel.measure_eq_zero_or_one_or_top_of_indepSet_self {t : Set Ω}
    (h_indep : Kernel.IndepSet t t κ μα) :
    ∀ᵐ a ∂μα, κ a t = 0 ∨ κ a t = 1 ∨ κ a t = ∞ := by
  specialize h_indep t t (measurableSet_generateFrom (Set.mem_singleton t))
    (measurableSet_generateFrom (Set.mem_singleton t))
  filter_upwards [h_indep] with a ha
  by_cases h0 : κ a t = 0
  · exact Or.inl h0
  by_cases h_top : κ a t = ∞
  · exact Or.inr (Or.inr h_top)
  rw [← one_mul (κ a (t ∩ t)), Set.inter_self, ENNReal.mul_left_inj h0 h_top] at ha
  exact Or.inr (Or.inl ha.symm)
/-
**ProbabilityTheory.measure_eq_zero_or_one_or_top_of_indepSet_self** 是 Mathlib 中
的一个定理，位于命名空间 `ProbabilityTheory`。
形式化陈述：measure_eq_zero_or_one_or_top_of_indepSet_self {t : Set Ω} (h_indep : Inde
pSet t t μ) : μ t = 0 ∨ μ t = 1 ∨ μ t = ∞
参数：h_indep : IndepSet t t μ。
该定理/引理给出了一组等式。
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
· 使用定理 `ProbabilityTheory.Kernel.measure_eq_zero_or_one_or_top_of_indepSet_self`
：∀ {α : Type u_1} {Ω : Type u_2} {_mα : MeasurableSpace α} {m0 : MeasurableSpace
 Ω} {κ : ProbabilityTheory.Kernel α Ω}   {μα : MeasureTheory.…
-/
theorem measure_eq_zero_or_one_or_top_of_indepSet_self {t : Set Ω}
    (h_indep : IndepSet t t μ) : μ t = 0 ∨ μ t = 1 ∨ μ t = ∞ := by
  simpa only [ae_dirac_eq, Filter.eventually_pure]
    using! Kernel.measure_eq_zero_or_one_or_top_of_indepSet_self h_indep
/-
**ProbabilityTheory.Kernel.measure_eq_zero_or_one_of_indepSet_self'** 是 Mathlib 
中的一个定理，位于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {_mα : MeasurableSpace α} {m0 : Measurable
Space Ω} {κ : ProbabilityTheory.Kernel α Ω}   {μα : MeasureTheory.Measure α},   
(∀ᵐ (a : α) ∂μα, MeasureTheory.IsFiniteMeasure (κ a)) →     ∀ {t : Set Ω}, Proba
bilityTheory.Kernel.IndepSet t t κ μα → ∀ᵐ (a : α) ∂μα, (κ a) t = 0 ∨ (κ a) t = 
1
参数：∀ᵐ (a : α) ∂μα, MeasureTheory.IsFiniteMeasure (κ a)；a : α；κ a；κ a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `ProbabilityTheory.Kernel.measure_eq_zero_or_one_or_top_of_indepSet_self`
：∀ {α : Type u_1} {Ω : Type u_2} {_mα : MeasurableSpace α} {m0 : MeasurableSpace
 Ω} {κ : ProbabilityTheory.Kernel α Ω}   {μα : MeasureTheory.…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
-/
theorem Kernel.measure_eq_zero_or_one_of_indepSet_self' (h : ∀ᵐ a ∂μα, IsFiniteMeasure (κ a))
    {t : Set Ω} (h_indep : IndepSet t t κ μα) :
    ∀ᵐ a ∂μα, κ a t = 0 ∨ κ a t = 1 := by
  filter_upwards [measure_eq_zero_or_one_or_top_of_indepSet_self h_indep, h] with a h_0_1_top h'
  simpa only [measure_ne_top (κ a), or_false] using h_0_1_top
/-
**ProbabilityTheory.Kernel.measure_eq_zero_or_one_of_indepSet_self** 是 Mathlib 中
的一个定理，位于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {_mα : MeasurableSpace α} {m0 : Measurable
Space Ω} {κ : ProbabilityTheory.Kernel α Ω}   {μα : MeasureTheory.Measure α} [h 
: ∀ (a : α), MeasureTheory.IsFiniteMeasure (κ a)] {t : Set Ω},   ProbabilityTheo
ry.Kernel.IndepSet t t κ μα → ∀ᵐ (a : α) ∂μα, (κ a) t = 0 ∨ (κ a) t = 1
参数：a : α；κ a；a : α；κ a；κ a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.measure_eq_zero_or_one_of_indepSet_self'`：∀ {α 
: Type u_1} {Ω : Type u_2} {_mα : MeasurableSpace α} {m0 : MeasurableSpace Ω} {κ
 : ProbabilityTheory.Kernel α Ω}   {μα : MeasureTheory.…
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
theorem Kernel.measure_eq_zero_or_one_of_indepSet_self [h : ∀ a, IsFiniteMeasure (κ a)] {t : Set Ω}
    (h_indep : IndepSet t t κ μα) :
    ∀ᵐ a ∂μα, κ a t = 0 ∨ κ a t = 1 :=
  Kernel.measure_eq_zero_or_one_of_indepSet_self' (ae_of_all μα h) h_indep
/-
**ProbabilityTheory.Kernel.measure_eq_zero_or_one_of_indep_self** 是 Mathlib 中的一个
定理，位于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {_mα : MeasurableSpace α} {m m0 : Measurab
leSpace Ω} {κ : ProbabilityTheory.Kernel α Ω}   {μα : MeasureTheory.Measure α} [
h : ∀ (a : α), MeasureTheory.IsFiniteMeasure (κ a)],   ProbabilityTheory.Kernel.
Indep m m κ μα → ∀ {t : Set Ω}, MeasurableSet t → ∀ᵐ (a : α) ∂μα, (κ a) t = 0 ∨ 
(κ a) t = 1
参数：a : α；κ a；a : α；κ a；κ a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.measure_eq_zero_or_one_of_indepSet_self`：∀ {α :
 Type u_1} {Ω : Type u_2} {_mα : MeasurableSpace α} {m0 : MeasurableSpace Ω} {κ 
: ProbabilityTheory.Kernel α Ω}   {μα : MeasureTheory.…
· 使用定理 `ProbabilityTheory.Kernel.indep_of_indep_of_le`：indep_of_indep_of_le {m₁ 
m₂ m₃ m₄ : MeasurableSpace Ω} {_mΩ : MeasurableSpace Ω} {κ : Kernel α Ω} {μ : Me
asure α} (h_indep : Indep m₁ m₂ κ μ…
· 使用引理 `MeasurableSpace.generateFrom_singleton_le`：generateFrom_singleton_le {m 
: MeasurableSpace α} {s : Set α} (hs : MeasurableSet s) : MeasurableSpace.genera
teFrom {s} <= m
-/
lemma Kernel.measure_eq_zero_or_one_of_indep_self [h : ∀ a, IsFiniteMeasure (κ a)]
    (hm : Indep m m κ μα) {t : Set Ω} (ht : MeasurableSet[m] t) :
    ∀ᵐ a ∂μα, κ a t = 0 ∨ κ a t = 1 :=
  measure_eq_zero_or_one_of_indepSet_self
    (indep_of_indep_of_le hm (generateFrom_singleton_le ht) (generateFrom_singleton_le ht))
/-
**ProbabilityTheory.measure_eq_zero_or_one_of_indepSet_self** 是 Mathlib 中的一个定理，位
于命名空间 `ProbabilityTheory`。
形式化陈述：measure_eq_zero_or_one_of_indepSet_self [IsFiniteMeasure μ] {t : Set Ω} (h
_indep : IndepSet t t μ) : μ t = 0 ∨ μ t = 1
参数：h_indep : IndepSet t t μ。
该定理/引理给出了一组等式。
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
· 使用定理 `ProbabilityTheory.Kernel.measure_eq_zero_or_one_of_indepSet_self`：∀ {α :
 Type u_1} {Ω : Type u_2} {_mα : MeasurableSpace α} {m0 : MeasurableSpace Ω} {κ 
: ProbabilityTheory.Kernel α Ω}   {μα : MeasureTheory.…
· 使用定理 `ProbabilityTheory.IsFiniteKernel.isFiniteMeasure`：∀ {α : Type u_1} {β : 
Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheo
ry.Kernel α β}   [ProbabilityTheory.Is…
· 使用定理 `ProbabilityTheory.Kernel.const.instIsFiniteKernel`：∀ {α : Type u_1} {β :
 Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μβ : MeasureTheory
.Measure β}   [MeasureTheory.IsFiniteMe…
-/
theorem measure_eq_zero_or_one_of_indepSet_self [IsFiniteMeasure μ] {t : Set Ω}
    (h_indep : IndepSet t t μ) : μ t = 0 ∨ μ t = 1 := by
  simpa only [ae_dirac_eq, Filter.eventually_pure]
    using! Kernel.measure_eq_zero_or_one_of_indepSet_self h_indep
/-
**ProbabilityTheory.measure_eq_zero_or_one_of_indep_self** 是 Mathlib 中的一个引理，位于命名
空间 `ProbabilityTheory`。
形式化陈述：measure_eq_zero_or_one_of_indep_self [IsFiniteMeasure μ] (hm : Indep m m μ
) {t : Set Ω} (ht : MeasurableSet[m] t) : μ t = 0 ∨ μ t = 1
参数：hm : Indep m m μ；ht : MeasurableSet[m] t。
该定理/引理给出了一组等式。
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
· 使用定理 `ProbabilityTheory.Kernel.measure_eq_zero_or_one_of_indep_self`：∀ {α : Ty
pe u_1} {Ω : Type u_2} {_mα : MeasurableSpace α} {m m0 : MeasurableSpace Ω} {κ :
 ProbabilityTheory.Kernel α Ω}   {μα : MeasureTheor…
· 使用定理 `ProbabilityTheory.IsFiniteKernel.isFiniteMeasure`：∀ {α : Type u_1} {β : 
Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheo
ry.Kernel α β}   [ProbabilityTheory.Is…
· 使用定理 `ProbabilityTheory.Kernel.const.instIsFiniteKernel`：∀ {α : Type u_1} {β :
 Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μβ : MeasureTheory
.Measure β}   [MeasureTheory.IsFiniteMe…
-/
lemma measure_eq_zero_or_one_of_indep_self [IsFiniteMeasure μ] (hm : Indep m m μ)
    {t : Set Ω} (ht : MeasurableSet[m] t) :
    μ t = 0 ∨ μ t = 1 := by
  simpa using Kernel.measure_eq_zero_or_one_of_indep_self hm ht
/-
**ProbabilityTheory.condExp_eq_zero_or_one_of_condIndepSet_self** 是 Mathlib 中的一个
定理，位于命名空间 `ProbabilityTheory`。
形式化陈述：condExp_eq_zero_or_one_of_condIndepSet_self [StandardBorelSpace Ω] (hm : m
 <= m0) [hμ : IsFiniteMeasure μ] {t : Set Ω} (ht : MeasurableSet t) (h_indep : C
ondIndepSet m hm t t μ) : forallᵐ ω ∂μ, (μ⟦t | m⟧) ω = 0 ∨ (μ⟦t | m⟧) ω = 1
参数：hm : m <= m0；ht : MeasurableSet t；h_indep : CondIndepSet m hm t t μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_of_ae_trim`：ae_of_ae_trim (hm : m <= m0) {μ : Measure α
} {P : α -> Prop} (h : forallᵐ x ∂μ.trim hm, P x) : forallᵐ x ∂μ, P x
· 使用定理 `ProbabilityTheory.Kernel.measure_eq_zero_or_one_of_indepSet_self`：∀ {α :
 Type u_1} {Ω : Type u_2} {_mα : MeasurableSpace α} {m0 : MeasurableSpace Ω} {κ 
: ProbabilityTheory.Kernel α Ω}   {μα : MeasureTheory.…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用引理 `ProbabilityTheory.condExpKernel_ae_eq_condExp`：condExpKernel_ae_eq_condE
xp (hm : m <= mΩ) {s : Set Ω} (hs : MeasurableSet s) : (fun ω => (condExpKernel 
μ m ω).real s) =ᵐ[μ] μ⟦s | m⟧
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.measureReal_eq_zero_iff`：measureReal_eq_zero_iff (h : μ s 
!= ∞
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `MeasureTheory.measureReal_def`：measureReal_def {α : Type*} {m : Measurab
leSpace α} (μ : Measure α) (s : Set α) : μ.real s = (μ s).toReal
· 使用定理 `ENNReal.toReal_eq_one_iff`：toReal_eq_one_iff (x : Real>=0∞) : x.toReal =
 1 ↔ x = 1
-/
theorem condExp_eq_zero_or_one_of_condIndepSet_self
    [StandardBorelSpace Ω]
    (hm : m ≤ m0) [hμ : IsFiniteMeasure μ] {t : Set Ω} (ht : MeasurableSet t)
    (h_indep : CondIndepSet m hm t t μ) :
    ∀ᵐ ω ∂μ, (μ⟦t | m⟧) ω = 0 ∨ (μ⟦t | m⟧) ω = 1 := by
  -- TODO: Why is not inferred?
  have (a : _) : IsFiniteMeasure (condExpKernel μ m a) := inferInstance
  have h := ae_of_ae_trim hm (Kernel.measure_eq_zero_or_one_of_indepSet_self h_indep)
  filter_upwards [condExpKernel_ae_eq_condExp hm ht, h] with ω hω_eq hω
  rwa [← hω_eq, measureReal_eq_zero_iff, measureReal_def, ENNReal.toReal_eq_one_iff]

open Filter
/-
**ProbabilityTheory.Kernel.indep_biSup_compl** 是 Mathlib 中的一个定理，位于命名空间 `Probabil
ityTheory.Kernel`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {
s : ι → MeasurableSpace Ω}   {m0 : MeasurableSpace Ω} {κ : ProbabilityTheory.Ker
nel α Ω} {μα : MeasureTheory.Measure α},   (∀ (n : ι), s n ≤ m0) →     Probabili
tyTheory.Kernel.iIndep s κ μα →       ∀ (t : Set ι), ProbabilityTheory.Kernel.In
dep (⨆ n ∈ t, s n) (⨆ n ∈ tᶜ, s n) κ μα
参数：∀ (n : ι), s n ≤ m0；t : Set ι；⨆ n ∈ t, s n；⨆ n ∈ tᶜ, s n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.indep_iSup_of_disjoint`：indep_iSup_of_disjoint 
{m : ι -> MeasurableSpace Ω} (h_le : forall i, m i <= _mΩ) (h_indep : iIndep m κ
 μ) {S T : Set ι} (hST : Disjoint S T…
· 使用定理 `disjoint_compl_right`：disjoint_compl_right : Disjoint a aᶜ
-/
theorem Kernel.indep_biSup_compl (h_le : ∀ n, s n ≤ m0) (h_indep : iIndep s κ μα) (t : Set ι) :
    Indep (⨆ n ∈ t, s n) (⨆ n ∈ tᶜ, s n) κ μα :=
  indep_iSup_of_disjoint h_le h_indep disjoint_compl_right
/-
**ProbabilityTheory.indep_biSup_compl** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheo
ry`。
形式化陈述：indep_biSup_compl (h_le : forall n, s n <= m0) (h_indep : iIndep s μ) (t :
 Set ι) : Indep (⨆ n in t, s n) (⨆ n in tᶜ, s n) μ
参数：h_le : forall n, s n <= m0；h_indep : iIndep s μ；t : Set ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.indep_biSup_compl`：∀ {α : Type u_1} {Ω : Type u
_2} {ι : Type u_3} {_mα : MeasurableSpace α} {s : ι → MeasurableSpace Ω}   {m0 :
 MeasurableSpace Ω} {κ : Probabi…
-/
theorem indep_biSup_compl (h_le : ∀ n, s n ≤ m0) (h_indep : iIndep s μ) (t : Set ι) :
    Indep (⨆ n ∈ t, s n) (⨆ n ∈ tᶜ, s n) μ :=
  Kernel.indep_biSup_compl h_le h_indep t
/-
**ProbabilityTheory.condIndep_biSup_compl** 是 Mathlib 中的一个定理，位于命名空间 `Probability
Theory`。
形式化陈述：condIndep_biSup_compl [StandardBorelSpace Ω] (hm : m <= m0) [IsFiniteMeasu
re μ] (h_le : forall n, s n <= m0) (h_indep : iCondIndep m hm s μ) (t : Set ι) :
 CondIndep m (⨆ n in t, s n) (⨆ n in tᶜ, s n) hm μ
参数：hm : m <= m0；h_le : forall n, s n <= m0；h_indep : iCondIndep m hm s μ；t : Set
 ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.indep_biSup_compl`：∀ {α : Type u_1} {Ω : Type u
_2} {ι : Type u_3} {_mα : MeasurableSpace α} {s : ι → MeasurableSpace Ω}   {m0 :
 MeasurableSpace Ω} {κ : Probabi…
-/
theorem condIndep_biSup_compl [StandardBorelSpace Ω]
    (hm : m ≤ m0) [IsFiniteMeasure μ]
    (h_le : ∀ n, s n ≤ m0) (h_indep : iCondIndep m hm s μ) (t : Set ι) :
    CondIndep m (⨆ n ∈ t, s n) (⨆ n ∈ tᶜ, s n) hm μ :=
  Kernel.indep_biSup_compl h_le h_indep t

section Abstract

variable {β : Type*} {p : Set ι → Prop} {f : Filter ι} {ns : β → Set ι}

/-! We prove a version of Kolmogorov's 0-1 law for the σ-algebra `limsup s f` where `f` is a filter
for which we can define the following two functions:
* `p : Set ι → Prop` such that for a set `t`, `p t → tᶜ ∈ f`,
* `ns : α → Set ι` a directed sequence of sets which all verify `p` and such that
  `⋃ a, ns a = Set.univ`.

For the example of `f = atTop`, we can take
`p = bddAbove` and `ns : ι → Set ι := fun i => Set.Iic i`.
-/

/-
**ProbabilityTheory.Kernel.indep_biSup_limsup** 是 Mathlib 中的一个定理，位于命名空间 `Probabi
lityTheory.Kernel`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {
s : ι → MeasurableSpace Ω}   {m0 : MeasurableSpace Ω} {κ : ProbabilityTheory.Ker
nel α Ω} {μα : MeasureTheory.Measure α} {p : Set ι → Prop}   {f : Filter ι},   (
∀ (n : ι), s n ≤ m0) →     ProbabilityTheory.Kernel.iIndep s κ μα →       (∀ (t 
: Set ι), p t → tᶜ ∈ f) →         ∀ {t : Set ι}, p t → ProbabilityTheory.Kernel.
Indep (⨆ n ∈ t, s n) (Filter.limsup s f) κ μα
参数：∀ (n : ι), s n ≤ m0；∀ (t : Set ι), p t → tᶜ ∈ f；⨆ n ∈ t, s n；Filter.limsup s 
f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.indep_of_indep_of_le_right`：indep_of_indep_of_l
e_right {m₁ m₂ m₃ : MeasurableSpace Ω} {_mΩ : MeasurableSpace Ω} {κ : Kernel α Ω
} {μ : Measure α} (h_indep : Indep m₁ m₂ …
· 使用定理 `ProbabilityTheory.Kernel.indep_biSup_compl`：∀ {α : Type u_1} {Ω : Type u
_2} {ι : Type u_3} {_mα : MeasurableSpace α} {s : ι → MeasurableSpace Ω}   {m0 :
 MeasurableSpace Ω} {κ : Probabi…
· 使用定理 `Filter.limsSup_le_of_le`：limsSup_le_of_le {f : Filter α} {a} (hf : f.IsC
obounded (· <= ·)
· 使用定理 `Filter.isCobounded_le_of_bot`：isCobounded_le_of_bot [LE α] [OrderBot α] 
{f : Filter α} : f.IsCobounded (· <= ·)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Filter.eventually_of_mem`：eventually_of_mem {f : Filter α} {P : α -> Pro
p} {U : Set α} (hU : U in f) (h : forall x in U, P x) : forallᶠ x in f, P x
· 使用定理 `le_iSup₂`：le_iSup₂ {f : forall i, κ i -> α} (i : ι) (j : κ i) : f i j <=
 ⨆ (i) (j), f i j

--- 原说明 ---
We prove a version of Kolmogorov's 0-1 law for the σ-algebra `limsup s f` where 
`f` is a filter
for which we can define the following two functions:
* `p : Set ι → Prop` such that for a set `t`, `p t → tᶜ ∈ f`,
* `ns : α → Set ι` a directed sequence of sets which all verify `p` and such tha
t
  `⋃ a, ns a = Set.univ`.

For the example of `f = atTop`, we can take
`p = bddAbove` and `ns : ι → Set ι := fun i => Set.Iic i`.
-/
theorem Kernel.indep_biSup_limsup (h_le : ∀ n, s n ≤ m0) (h_indep : iIndep s κ μα)
    (hf : ∀ t, p t → tᶜ ∈ f) {t : Set ι} (ht : p t) :
    Indep (⨆ n ∈ t, s n) (limsup s f) κ μα := by
  refine indep_of_indep_of_le_right (indep_biSup_compl h_le h_indep t) ?_
  refine limsSup_le_of_le (by isBoundedDefault) ?_
  simp only [Set.mem_compl_iff, eventually_map]
  exact eventually_of_mem (hf t ht) le_iSup₂
/-
**ProbabilityTheory.indep_biSup_limsup** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityThe
ory`。
形式化陈述：indep_biSup_limsup (h_le : forall n, s n <= m0) (h_indep : iIndep s μ) (hf
 : forall t, p t -> tᶜ in f) {t : Set ι} (ht : p t) : Indep (⨆ n in t, s n) (lim
sup s f) μ
参数：h_le : forall n, s n <= m0；h_indep : iIndep s μ；hf : forall t, p t -> tᶜ in f
；ht : p t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.indep_biSup_limsup`：∀ {α : Type u_1} {Ω : Type 
u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {s : ι → MeasurableSpace Ω}   {m0 
: MeasurableSpace Ω} {κ : Probabi…
-/
theorem indep_biSup_limsup
    (h_le : ∀ n, s n ≤ m0) (h_indep : iIndep s μ) (hf : ∀ t, p t → tᶜ ∈ f)
    {t : Set ι} (ht : p t) :
    Indep (⨆ n ∈ t, s n) (limsup s f) μ :=
  Kernel.indep_biSup_limsup h_le h_indep hf ht
/-
**ProbabilityTheory.condIndep_biSup_limsup** 是 Mathlib 中的一个定理，位于命名空间 `Probabilit
yTheory`。
形式化陈述：condIndep_biSup_limsup [StandardBorelSpace Ω] (hm : m <= m0) [IsFiniteMeas
ure μ] (h_le : forall n, s n <= m0) (h_indep : iCondIndep m hm s μ) (hf : forall
 t, p t -> tᶜ in f) {t : Set ι} (ht : p t) : CondIndep m (⨆ n in t, s n) (limsup
 s f) hm μ
参数：hm : m <= m0；h_le : forall n, s n <= m0；h_indep : iCondIndep m hm s μ；hf : fo
rall t, p t -> tᶜ in f；ht : p t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.indep_biSup_limsup`：∀ {α : Type u_1} {Ω : Type 
u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {s : ι → MeasurableSpace Ω}   {m0 
: MeasurableSpace Ω} {κ : Probabi…
-/
theorem condIndep_biSup_limsup [StandardBorelSpace Ω]
    (hm : m ≤ m0) [IsFiniteMeasure μ]
    (h_le : ∀ n, s n ≤ m0) (h_indep : iCondIndep m hm s μ) (hf : ∀ t, p t → tᶜ ∈ f)
    {t : Set ι} (ht : p t) :
    CondIndep m (⨆ n ∈ t, s n) (limsup s f) hm μ :=
  Kernel.indep_biSup_limsup h_le h_indep hf ht
/-
**ProbabilityTheory.Kernel.indep_iSup_directed_limsup** 是 Mathlib 中的一个定理，位于命名空间 
`ProbabilityTheory.Kernel`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {
s : ι → MeasurableSpace Ω}   {m0 : MeasurableSpace Ω} {κ : ProbabilityTheory.Ker
nel α Ω} {μα : MeasureTheory.Measure α} {β : Type u_4}   {p : Set ι → Prop} {f :
 Filter ι} {ns : β → Set ι},   (∀ (n : ι), s n ≤ m0) →     ProbabilityTheory.Ker
nel.iIndep s κ μα →       (∀ (t : Set ι), p t → tᶜ ∈ f) →         Directed (fun 
x1 x2 => x1 ⊆ x2) ns →           (∀ (a : β), p (ns a)) → ProbabilityTheory.Kerne
l.Indep (⨆ a, ⨆ n ∈ ns a, s n) (Filter.limsup s f) κ μα
参数：∀ (n : ι), s n ≤ m0；∀ (t : Set ι), p t → tᶜ ∈ f；fun x1 x2 => x1 ⊆ x2；∀ (a : β
), p (ns a)；⨆ a, ⨆ n ∈ ns a, s n；Filter.limsup s f。
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
· 使用定理 `ProbabilityTheory.Kernel.iIndep.congr`：∀ {α : Type u_1} {Ω : Type u_2} {
ι : Type u_3} {_mα : MeasurableSpace α} {m : ι → MeasurableSpace Ω}   {_mΩ : Mea
surableSpace Ω} {κ η : Prob…
· 使用定理 `ProbabilityTheory.Kernel.Indep.congr`：∀ {α : Type u_1} {Ω : Type u_2} {_
mα : MeasurableSpace α} {μ : MeasureTheory.Measure α} {m₁ m₂ _mΩ : MeasurableSpa
ce Ω}   {κ η : Probability…
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `ProbabilityTheory.Kernel.indep_iSup_of_directed_le`：indep_iSup_of_direct
ed_le {Ω} {m : ι -> MeasurableSpace Ω} {m' m0 : MeasurableSpace Ω} {κ : Kernel α
 Ω} {μ : Measure α} [IsZeroOrMarkovKerne…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.Kernel.indep_biSup_limsup`：∀ {α : Type u_1} {Ω : Type 
u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {s : ι → MeasurableSpace Ω}   {m0 
: MeasurableSpace Ω} {κ : Probabi…
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Filter.limsup_le_iSup`：limsup_le_iSup {f : Filter β} {u : β -> α} : lims
up u f <= ⨆ n, u n
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `iSup_mono`：iSup_mono (h : forall i, f i <= g i) : iSup f <= iSup g
· 使用定理 `iSup_mono'`：iSup_mono' {g : ι' -> α} (h : forall i, exists i', f i <= g 
i') : iSup f <= iSup g
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Kernel.indep_iSup_directed_limsup (h_le : ∀ n, s n ≤ m0) (h_indep : iIndep s κ μα)
    (hf : ∀ t, p t → tᶜ ∈ f) (hns : Directed (· ≤ ·) ns) (hnsp : ∀ a, p (ns a)) :
    Indep (⨆ a, ⨆ n ∈ ns a, s n) (limsup s f) κ μα := by
  rcases eq_or_ne μα 0 with rfl | hμ
  · simp
  obtain ⟨η, η_eq, hη⟩ : ∃ (η : Kernel α Ω), κ =ᵐ[μα] η ∧ IsMarkovKernel η :=
    exists_ae_eq_isMarkovKernel h_indep.ae_isProbabilityMeasure hμ
  replace h_indep := h_indep.congr η_eq
  apply Indep.congr (Filter.EventuallyEq.symm η_eq)
  apply indep_iSup_of_directed_le
  · exact fun a => indep_biSup_limsup h_le h_indep hf (hnsp a)
  · exact fun a => iSup₂_le fun n _ => h_le n
  · exact limsup_le_iSup.trans (iSup_le h_le)
  · intro a b
    obtain ⟨c, hc⟩ := hns a b
    refine ⟨c, ?_, ?_⟩ <;> refine iSup_mono fun n => iSup_mono' fun hn => ⟨?_, le_rfl⟩
    · exact hc.1 hn
    · exact hc.2 hn
/-
**ProbabilityTheory.indep_iSup_directed_limsup** 是 Mathlib 中的一个定理，位于命名空间 `Probab
ilityTheory`。
形式化陈述：indep_iSup_directed_limsup (h_le : forall n, s n <= m0) (h_indep : iIndep 
s μ) (hf : forall t, p t -> tᶜ in f) (hns : Directed (· <= ·) ns) (hnsp : forall
 a, p (ns a)) : Indep (⨆ a, ⨆ n in ns a, s n) (limsup s f) μ
参数：h_le : forall n, s n <= m0；h_indep : iIndep s μ；hf : forall t, p t -> tᶜ in f
；hns : Directed (· <= ·) ns；hnsp : forall a, p (ns a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.indep_iSup_directed_limsup`：∀ {α : Type u_1} {Ω
 : Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {s : ι → MeasurableSpace Ω
}   {m0 : MeasurableSpace Ω} {κ : Probabi…
-/
theorem indep_iSup_directed_limsup
    (h_le : ∀ n, s n ≤ m0) (h_indep : iIndep s μ)
    (hf : ∀ t, p t → tᶜ ∈ f) (hns : Directed (· ≤ ·) ns) (hnsp : ∀ a, p (ns a)) :
    Indep (⨆ a, ⨆ n ∈ ns a, s n) (limsup s f) μ :=
  Kernel.indep_iSup_directed_limsup h_le h_indep hf hns hnsp
/-
**ProbabilityTheory.condIndep_iSup_directed_limsup** 是 Mathlib 中的一个定理，位于命名空间 `Pr
obabilityTheory`。
形式化陈述：condIndep_iSup_directed_limsup [StandardBorelSpace Ω] (hm : m <= m0) [IsFi
niteMeasure μ] (h_le : forall n, s n <= m0) (h_indep : iCondIndep m hm s μ) (hf 
: forall t, p t -> tᶜ in f) (hns : Directed (· <= ·) ns) (hnsp : forall a, p (ns
 a)) : CondIndep m (⨆ a, ⨆ n in ns a, s n) (limsup s f) hm μ
参数：hm : m <= m0；h_le : forall n, s n <= m0；h_indep : iCondIndep m hm s μ；hf : fo
rall t, p t -> tᶜ in f；hns : Directed (· <= ·) ns；hnsp : forall a, p (ns a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.indep_iSup_directed_limsup`：∀ {α : Type u_1} {Ω
 : Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {s : ι → MeasurableSpace Ω
}   {m0 : MeasurableSpace Ω} {κ : Probabi…
-/
theorem condIndep_iSup_directed_limsup [StandardBorelSpace Ω]
    (hm : m ≤ m0) [IsFiniteMeasure μ]
    (h_le : ∀ n, s n ≤ m0) (h_indep : iCondIndep m hm s μ)
    (hf : ∀ t, p t → tᶜ ∈ f) (hns : Directed (· ≤ ·) ns) (hnsp : ∀ a, p (ns a)) :
    CondIndep m (⨆ a, ⨆ n ∈ ns a, s n) (limsup s f) hm μ :=
  Kernel.indep_iSup_directed_limsup h_le h_indep hf hns hnsp
/-
**ProbabilityTheory.Kernel.indep_iSup_limsup** 是 Mathlib 中的一个定理，位于命名空间 `Probabil
ityTheory.Kernel`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {
s : ι → MeasurableSpace Ω}   {m0 : MeasurableSpace Ω} {κ : ProbabilityTheory.Ker
nel α Ω} {μα : MeasureTheory.Measure α} {β : Type u_4}   {p : Set ι → Prop} {f :
 Filter ι} {ns : β → Set ι},   (∀ (n : ι), s n ≤ m0) →     ProbabilityTheory.Ker
nel.iIndep s κ μα →       (∀ (t : Set ι), p t → tᶜ ∈ f) →         Directed (fun 
x1 x2 => x1 ⊆ x2) ns →           (∀ (a : β), p (ns a)) →             (∀ (n : ι),
 ∃ a, n ∈ ns a) → ProbabilityTheory.Kernel.Indep (⨆ n, s n) (Filter.limsup s f) 
κ μα
参数：∀ (n : ι), s n ≤ m0；∀ (t : Set ι), p t → tᶜ ∈ f；fun x1 x2 => x1 ⊆ x2；∀ (a : β
), p (ns a)；∀ (n : ι), ∃ a, n ∈ ns a；⨆ n, s n；Filter.limsup s f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_comm`：iSup_comm {f : ι -> ι' -> α} : ⨆ (i) (j), f i j = ⨆ (j) (i), 
f i j
· 使用定理 `iSup_congr`：iSup_congr (h : forall i, f i = g i) : ⨆ i, f i = ⨆ i, g i
· 使用定理 `iSup_exists`：iSup_exists {p : ι -> Prop} {f : Exists p -> α} : ⨆ x, f x 
= ⨆ (i) (h), f ⟨i, h⟩
· 使用定理 `iSup_const`：iSup_const [Nonempty ι] : ⨆ _ : ι, a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.Kernel.indep_iSup_directed_limsup`：∀ {α : Type u_1} {Ω
 : Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {s : ι → MeasurableSpace Ω
}   {m0 : MeasurableSpace Ω} {κ : Probabi…
-/
theorem Kernel.indep_iSup_limsup (h_le : ∀ n, s n ≤ m0) (h_indep : iIndep s κ μα)
    (hf : ∀ t, p t → tᶜ ∈ f)
    (hns : Directed (· ≤ ·) ns) (hnsp : ∀ a, p (ns a)) (hns_univ : ∀ n, ∃ a, n ∈ ns a) :
    Indep (⨆ n, s n) (limsup s f) κ μα := by
  suffices (⨆ a, ⨆ n ∈ ns a, s n) = ⨆ n, s n by
    rw [← this]
    exact indep_iSup_directed_limsup h_le h_indep hf hns hnsp
  rw [iSup_comm]
  refine iSup_congr fun n => ?_
  have h : ⨆ (i : β) (_ : n ∈ ns i), s n = ⨆ _ : ∃ i, n ∈ ns i, s n := by rw [iSup_exists]
  have : Nonempty (∃ i : β, n ∈ ns i) := ⟨hns_univ n⟩
  rw [h, iSup_const]
/-
**ProbabilityTheory.indep_iSup_limsup** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheo
ry`。
形式化陈述：indep_iSup_limsup (h_le : forall n, s n <= m0) (h_indep : iIndep s μ) (hf 
: forall t, p t -> tᶜ in f) (hns : Directed (· <= ·) ns) (hnsp : forall a, p (ns
 a)) (hns_univ : forall n, exists a, n in ns a) : Indep (⨆ n, s n) (limsup s f) 
μ
参数：h_le : forall n, s n <= m0；h_indep : iIndep s μ；hf : forall t, p t -> tᶜ in f
；hns : Directed (· <= ·) ns；hnsp : forall a, p (ns a)；hns_univ : forall n, exist
s a, n in ns a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.indep_iSup_limsup`：∀ {α : Type u_1} {Ω : Type u
_2} {ι : Type u_3} {_mα : MeasurableSpace α} {s : ι → MeasurableSpace Ω}   {m0 :
 MeasurableSpace Ω} {κ : Probabi…
-/
theorem indep_iSup_limsup
    (h_le : ∀ n, s n ≤ m0) (h_indep : iIndep s μ) (hf : ∀ t, p t → tᶜ ∈ f)
    (hns : Directed (· ≤ ·) ns) (hnsp : ∀ a, p (ns a)) (hns_univ : ∀ n, ∃ a, n ∈ ns a) :
    Indep (⨆ n, s n) (limsup s f) μ :=
  Kernel.indep_iSup_limsup h_le h_indep hf hns hnsp hns_univ
/-
**ProbabilityTheory.condIndep_iSup_limsup** 是 Mathlib 中的一个定理，位于命名空间 `Probability
Theory`。
形式化陈述：condIndep_iSup_limsup [StandardBorelSpace Ω] (hm : m <= m0) [IsFiniteMeasu
re μ] (h_le : forall n, s n <= m0) (h_indep : iCondIndep m hm s μ) (hf : forall 
t, p t -> tᶜ in f) (hns : Directed (· <= ·) ns) (hnsp : forall a, p (ns a)) (hns
_univ : forall n, exists a, n in ns a) : CondIndep m (⨆ n, s n) (limsup s f) hm 
μ
参数：hm : m <= m0；h_le : forall n, s n <= m0；h_indep : iCondIndep m hm s μ；hf : fo
rall t, p t -> tᶜ in f；hns : Directed (· <= ·) ns；hnsp : forall a, p (ns a)；hns_
univ : forall n, exists a, n in ns a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.indep_iSup_limsup`：∀ {α : Type u_1} {Ω : Type u
_2} {ι : Type u_3} {_mα : MeasurableSpace α} {s : ι → MeasurableSpace Ω}   {m0 :
 MeasurableSpace Ω} {κ : Probabi…
-/
theorem condIndep_iSup_limsup [StandardBorelSpace Ω]
    (hm : m ≤ m0) [IsFiniteMeasure μ]
    (h_le : ∀ n, s n ≤ m0) (h_indep : iCondIndep m hm s μ) (hf : ∀ t, p t → tᶜ ∈ f)
    (hns : Directed (· ≤ ·) ns) (hnsp : ∀ a, p (ns a)) (hns_univ : ∀ n, ∃ a, n ∈ ns a) :
    CondIndep m (⨆ n, s n) (limsup s f) hm μ :=
  Kernel.indep_iSup_limsup h_le h_indep hf hns hnsp hns_univ
/-
**ProbabilityTheory.Kernel.indep_limsup_self** 是 Mathlib 中的一个定理，位于命名空间 `Probabil
ityTheory.Kernel`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {
s : ι → MeasurableSpace Ω}   {m0 : MeasurableSpace Ω} {κ : ProbabilityTheory.Ker
nel α Ω} {μα : MeasureTheory.Measure α} {β : Type u_4}   {p : Set ι → Prop} {f :
 Filter ι} {ns : β → Set ι},   (∀ (n : ι), s n ≤ m0) →     ProbabilityTheory.Ker
nel.iIndep s κ μα →       (∀ (t : Set ι), p t → tᶜ ∈ f) →         Directed (fun 
x1 x2 => x1 ⊆ x2) ns →           (∀ (a : β), p (ns a)) →             (∀ (n : ι),
 ∃ a, n ∈ ns a) → ProbabilityTheory.Kernel.Indep (Filter.limsup s f) (Filter.lim
sup s f) κ μα
参数：∀ (n : ι), s n ≤ m0；∀ (t : Set ι), p t → tᶜ ∈ f；fun x1 x2 => x1 ⊆ x2；∀ (a : β
), p (ns a)；∀ (n : ι), ∃ a, n ∈ ns a；Filter.limsup s f；Filter.limsup s f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.indep_of_indep_of_le_left`：indep_of_indep_of_le
_left {m₁ m₂ m₃ : MeasurableSpace Ω} {_mΩ : MeasurableSpace Ω} {κ : Kernel α Ω} 
{μ : Measure α} (h_indep : Indep m₁ m₂ κ…
· 使用定理 `ProbabilityTheory.Kernel.indep_iSup_limsup`：∀ {α : Type u_1} {Ω : Type u
_2} {ι : Type u_3} {_mα : MeasurableSpace α} {s : ι → MeasurableSpace Ω}   {m0 :
 MeasurableSpace Ω} {κ : Probabi…
· 使用定理 `Filter.limsup_le_iSup`：limsup_le_iSup {f : Filter β} {u : β -> α} : lims
up u f <= ⨆ n, u n
-/
theorem Kernel.indep_limsup_self (h_le : ∀ n, s n ≤ m0) (h_indep : iIndep s κ μα)
    (hf : ∀ t, p t → tᶜ ∈ f)
    (hns : Directed (· ≤ ·) ns) (hnsp : ∀ a, p (ns a)) (hns_univ : ∀ n, ∃ a, n ∈ ns a) :
    Indep (limsup s f) (limsup s f) κ μα :=
  indep_of_indep_of_le_left (indep_iSup_limsup h_le h_indep hf hns hnsp hns_univ) limsup_le_iSup
/-
**ProbabilityTheory.indep_limsup_self** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheo
ry`。
形式化陈述：indep_limsup_self (h_le : forall n, s n <= m0) (h_indep : iIndep s μ) (hf 
: forall t, p t -> tᶜ in f) (hns : Directed (· <= ·) ns) (hnsp : forall a, p (ns
 a)) (hns_univ : forall n, exists a, n in ns a) : Indep (limsup s f) (limsup s f
) μ
参数：h_le : forall n, s n <= m0；h_indep : iIndep s μ；hf : forall t, p t -> tᶜ in f
；hns : Directed (· <= ·) ns；hnsp : forall a, p (ns a)；hns_univ : forall n, exist
s a, n in ns a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.indep_limsup_self`：∀ {α : Type u_1} {Ω : Type u
_2} {ι : Type u_3} {_mα : MeasurableSpace α} {s : ι → MeasurableSpace Ω}   {m0 :
 MeasurableSpace Ω} {κ : Probabi…
-/
theorem indep_limsup_self
    (h_le : ∀ n, s n ≤ m0) (h_indep : iIndep s μ) (hf : ∀ t, p t → tᶜ ∈ f)
    (hns : Directed (· ≤ ·) ns) (hnsp : ∀ a, p (ns a)) (hns_univ : ∀ n, ∃ a, n ∈ ns a) :
    Indep (limsup s f) (limsup s f) μ :=
  Kernel.indep_limsup_self h_le h_indep hf hns hnsp hns_univ
/-
**ProbabilityTheory.condIndep_limsup_self** 是 Mathlib 中的一个定理，位于命名空间 `Probability
Theory`。
形式化陈述：condIndep_limsup_self [StandardBorelSpace Ω] (hm : m <= m0) [IsFiniteMeasu
re μ] (h_le : forall n, s n <= m0) (h_indep : iCondIndep m hm s μ) (hf : forall 
t, p t -> tᶜ in f) (hns : Directed (· <= ·) ns) (hnsp : forall a, p (ns a)) (hns
_univ : forall n, exists a, n in ns a) : CondIndep m (limsup s f) (limsup s f) h
m μ
参数：hm : m <= m0；h_le : forall n, s n <= m0；h_indep : iCondIndep m hm s μ；hf : fo
rall t, p t -> tᶜ in f；hns : Directed (· <= ·) ns；hnsp : forall a, p (ns a)；hns_
univ : forall n, exists a, n in ns a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.indep_limsup_self`：∀ {α : Type u_1} {Ω : Type u
_2} {ι : Type u_3} {_mα : MeasurableSpace α} {s : ι → MeasurableSpace Ω}   {m0 :
 MeasurableSpace Ω} {κ : Probabi…
-/
theorem condIndep_limsup_self [StandardBorelSpace Ω]
    (hm : m ≤ m0) [IsFiniteMeasure μ]
    (h_le : ∀ n, s n ≤ m0) (h_indep : iCondIndep m hm s μ) (hf : ∀ t, p t → tᶜ ∈ f)
    (hns : Directed (· ≤ ·) ns) (hnsp : ∀ a, p (ns a)) (hns_univ : ∀ n, ∃ a, n ∈ ns a) :
    CondIndep m (limsup s f) (limsup s f) hm μ :=
  Kernel.indep_limsup_self h_le h_indep hf hns hnsp hns_univ
/-
**ProbabilityTheory.Kernel.measure_zero_or_one_of_measurableSet_limsup** 是 Mathl
ib 中的一个定理，位于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {
s : ι → MeasurableSpace Ω}   {m0 : MeasurableSpace Ω} {κ : ProbabilityTheory.Ker
nel α Ω} {μα : MeasureTheory.Measure α} {β : Type u_4}   {p : Set ι → Prop} {f :
 Filter ι} {ns : β → Set ι},   (∀ (n : ι), s n ≤ m0) →     ProbabilityTheory.Ker
nel.iIndep s κ μα →       (∀ (t : Set ι), p t → tᶜ ∈ f) →         Directed (fun 
x1 x2 => x1 ⊆ x2) ns →           (∀ (a : β), p (ns a)) →             (∀ (n : ι),
 ∃ a, n ∈ ns a) → ∀ {t : Set Ω}, MeasurableSet t → ∀ᵐ (a : α) ∂μα, (κ a) t = 0 ∨
 (κ a) t = 1
参数：∀ (n : ι), s n ≤ m0；∀ (t : Set ι), p t → tᶜ ∈ f；fun x1 x2 => x1 ⊆ x2；∀ (a : β
), p (ns a)；∀ (n : ι), ∃ a, n ∈ ns a；a : α；κ a；κ a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.measure_eq_zero_or_one_of_indepSet_self'`：∀ {α 
: Type u_1} {Ω : Type u_2} {_mα : MeasurableSpace α} {m0 : MeasurableSpace Ω} {κ
 : ProbabilityTheory.Kernel α Ω}   {μα : MeasureTheory.…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.Kernel.iIndep.ae_isProbabilityMeasure`：∀ {α : Type u_1
} {Ω : Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {m : ι → MeasurableSpa
ce Ω}   {_mΩ : MeasurableSpace Ω} {κ : Probab…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `ProbabilityTheory.Kernel.Indep.indepSet_of_measurableSet`：∀ {α : Type u_
1} {Ω : Type u_2} {_mα : MeasurableSpace α} {m₁ m₂ x : MeasurableSpace Ω}   {κ :
 ProbabilityTheory.Kernel α Ω} {μ : MeasureThe…
· 使用定理 `ProbabilityTheory.Kernel.indep_limsup_self`：∀ {α : Type u_1} {Ω : Type u
_2} {ι : Type u_3} {_mα : MeasurableSpace α} {s : ι → MeasurableSpace Ω}   {m0 :
 MeasurableSpace Ω} {κ : Probabi…
-/
theorem Kernel.measure_zero_or_one_of_measurableSet_limsup (h_le : ∀ n, s n ≤ m0)
    (h_indep : iIndep s κ μα)
    (hf : ∀ t, p t → tᶜ ∈ f) (hns : Directed (· ≤ ·) ns) (hnsp : ∀ a, p (ns a))
    (hns_univ : ∀ n, ∃ a, n ∈ ns a) {t : Set Ω} (ht_tail : MeasurableSet[limsup s f] t) :
    ∀ᵐ a ∂μα, κ a t = 0 ∨ κ a t = 1 := by
  apply measure_eq_zero_or_one_of_indepSet_self' ?_
    ((indep_limsup_self h_le h_indep hf hns hnsp hns_univ).indepSet_of_measurableSet ht_tail
      ht_tail)
  filter_upwards [h_indep.ae_isProbabilityMeasure] with a ha using by infer_instance
/-
**ProbabilityTheory.measure_zero_or_one_of_measurableSet_limsup** 是 Mathlib 中的一个
定理，位于命名空间 `ProbabilityTheory`。
形式化陈述：measure_zero_or_one_of_measurableSet_limsup (h_le : forall n, s n <= m0) (
h_indep : iIndep s μ) (hf : forall t, p t -> tᶜ in f) (hns : Directed (· <= ·) n
s) (hnsp : forall a, p (ns a)) (hns_univ : forall n, exists a, n in ns a) {t : S
et Ω} (ht_tail : MeasurableSet[limsup s f] t) : μ t = 0 ∨ μ t = 1
参数：h_le : forall n, s n <= m0；h_indep : iIndep s μ；hf : forall t, p t -> tᶜ in f
；hns : Directed (· <= ·) ns；hnsp : forall a, p (ns a)；hns_univ : forall n, exist
s a, n in ns a；ht_tail : MeasurableSet[limsup s f] t。
该定理/引理给出了一组等式。
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
· 使用定理 `ProbabilityTheory.Kernel.measure_zero_or_one_of_measurableSet_limsup`：∀ 
{α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {s : ι → 
MeasurableSpace Ω}   {m0 : MeasurableSpace Ω} {κ : Probabi…
-/
theorem measure_zero_or_one_of_measurableSet_limsup
    (h_le : ∀ n, s n ≤ m0) (h_indep : iIndep s μ)
    (hf : ∀ t, p t → tᶜ ∈ f) (hns : Directed (· ≤ ·) ns) (hnsp : ∀ a, p (ns a))
    (hns_univ : ∀ n, ∃ a, n ∈ ns a) {t : Set Ω} (ht_tail : MeasurableSet[limsup s f] t) :
    μ t = 0 ∨ μ t = 1 := by
  simpa only [ae_dirac_eq, Filter.eventually_pure]
    using! Kernel.measure_zero_or_one_of_measurableSet_limsup h_le h_indep hf hns hnsp hns_univ
      ht_tail
/-
**ProbabilityTheory.condExp_zero_or_one_of_measurableSet_limsup** 是 Mathlib 中的一个
定理，位于命名空间 `ProbabilityTheory`。
形式化陈述：condExp_zero_or_one_of_measurableSet_limsup [StandardBorelSpace Ω] (hm : m
 <= m0) [IsFiniteMeasure μ] (h_le : forall n, s n <= m0) (h_indep : iCondIndep m
 hm s μ) (hf : forall t, p t -> tᶜ in f) (hns : Directed (· <= ·) ns) (hnsp : fo
rall a, p (ns a)) (hns_univ : forall n, exists a, n in ns a) {t : Set Ω} (ht_tai
l : MeasurableSet[limsup s f] t) : forallᵐ ω ∂μ, (μ⟦t | m⟧) ω = 0 ∨ (μ⟦t | m⟧) ω
 = 1
参数：hm : m <= m0；h_le : forall n, s n <= m0；h_indep : iCondIndep m hm s μ；hf : fo
rall t, p t -> tᶜ in f；hns : Directed (· <= ·) ns；hnsp : forall a, p (ns a)；hns_
univ : forall n, exists a, n in ns a；ht_tail : MeasurableSet[limsup s f] t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_of_ae_trim`：ae_of_ae_trim (hm : m <= m0) {μ : Measure α
} {P : α -> Prop} (h : forallᵐ x ∂μ.trim hm, P x) : forallᵐ x ∂μ, P x
· 使用定理 `ProbabilityTheory.Kernel.measure_zero_or_one_of_measurableSet_limsup`：∀ 
{α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {s : ι → 
MeasurableSpace Ω}   {m0 : MeasurableSpace Ω} {κ : Probabi…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Filter.limsup_le_iSup`：limsup_le_iSup {f : Filter β} {u : β -> α} : lims
up u f <= ⨆ n, u n
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用引理 `ProbabilityTheory.condExpKernel_ae_eq_condExp`：condExpKernel_ae_eq_condE
xp (hm : m <= mΩ) {s : Set Ω} (hs : MeasurableSet s) : (fun ω => (condExpKernel 
μ m ω).real s) =ᵐ[μ] μ⟦s | m⟧
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.measureReal_eq_zero_iff`：measureReal_eq_zero_iff (h : μ s 
!= ∞
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
· 使用定理 `MeasureTheory.measureReal_def`：measureReal_def {α : Type*} {m : Measurab
leSpace α} (μ : Measure α) (s : Set α) : μ.real s = (μ s).toReal
· 使用定理 `ENNReal.toReal_eq_one_iff`：toReal_eq_one_iff (x : Real>=0∞) : x.toReal =
 1 ↔ x = 1
-/
theorem condExp_zero_or_one_of_measurableSet_limsup [StandardBorelSpace Ω]
    (hm : m ≤ m0) [IsFiniteMeasure μ]
    (h_le : ∀ n, s n ≤ m0) (h_indep : iCondIndep m hm s μ)
    (hf : ∀ t, p t → tᶜ ∈ f) (hns : Directed (· ≤ ·) ns) (hnsp : ∀ a, p (ns a))
    (hns_univ : ∀ n, ∃ a, n ∈ ns a) {t : Set Ω} (ht_tail : MeasurableSet[limsup s f] t) :
    ∀ᵐ ω ∂μ, (μ⟦t | m⟧) ω = 0 ∨ (μ⟦t | m⟧) ω = 1 := by
  have h := ae_of_ae_trim hm
    (Kernel.measure_zero_or_one_of_measurableSet_limsup h_le h_indep hf hns hnsp hns_univ ht_tail)
  have ht : MeasurableSet t := limsup_le_iSup.trans (iSup_le h_le) t ht_tail
  filter_upwards [condExpKernel_ae_eq_condExp hm ht, h] with ω hω_eq hω
  rwa [← hω_eq, measureReal_eq_zero_iff, measureReal_def, ENNReal.toReal_eq_one_iff]

end Abstract

section AtTop

variable [SemilatticeSup ι] [NoMaxOrder ι] [Nonempty ι]

/-
**ProbabilityTheory.Kernel.indep_limsup_atTop_self** 是 Mathlib 中的一个定理，位于命名空间 `Pr
obabilityTheory.Kernel`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {
s : ι → MeasurableSpace Ω}   {m0 : MeasurableSpace Ω} {κ : ProbabilityTheory.Ker
nel α Ω} {μα : MeasureTheory.Measure α} [inst : SemilatticeSup ι]   [NoMaxOrder 
ι] [Nonempty ι],   (∀ (n : ι), s n ≤ m0) →     ProbabilityTheory.Kernel.iIndep s
 κ μα →       ProbabilityTheory.Kernel.Indep (Filter.limsup s Filter.atTop) (Fil
ter.limsup s Filter.atTop) κ μα
参数：∀ (n : ι), s n ≤ m0；Filter.limsup s Filter.atTop；Filter.limsup s Filter.atTop
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bddAbove_Iic`：bddAbove_Iic : BddAbove (Iic a)
· 使用定理 `ProbabilityTheory.Kernel.indep_limsup_self`：∀ {α : Type u_1} {Ω : Type u
_2} {ι : Type u_3} {_mα : MeasurableSpace α} {s : ι → MeasurableSpace Ω}   {m0 :
 MeasurableSpace Ω} {κ : Probabi…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `NoMaxOrder.exists_gt`：∀ {α : Type u_3} {inst : LT α} [self : NoMaxOrder 
α] (a : α), ∃ b, a < b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `Monotone.directed_le`：Monotone.directed_le [Preorder α] [IsDirectedOrder
 α] [Preorder β] {f : α -> β} : Monotone f -> Directed (· <= ·) f
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem Kernel.indep_limsup_atTop_self (h_le : ∀ n, s n ≤ m0) (h_indep : iIndep s κ μα) :
    Indep (limsup s atTop) (limsup s atTop) κ μα := by
  let ns : ι → Set ι := Set.Iic
  have hnsp : ∀ i, BddAbove (ns i) := fun i => bddAbove_Iic
  refine indep_limsup_self h_le h_indep ?_ ?_ hnsp ?_
  · simp only [mem_atTop_sets, Set.mem_compl_iff, BddAbove, upperBounds, Set.Nonempty]
    rintro t ⟨a, ha⟩
    obtain ⟨b, hb⟩ : ∃ b, a < b := exists_gt a
    refine ⟨b, fun c hc hct => ?_⟩
    suffices ∀ i ∈ t, i < c from lt_irrefl c (this c hct)
    exact fun i hi => (ha hi).trans_lt (hb.trans_le hc)
  · exact Monotone.directed_le fun i j hij k hki => le_trans hki hij
  · exact fun n => ⟨n, le_rfl⟩
/-
**ProbabilityTheory.indep_limsup_atTop_self** 是 Mathlib 中的一个定理，位于命名空间 `Probabili
tyTheory`。
形式化陈述：indep_limsup_atTop_self (h_le : forall n, s n <= m0) (h_indep : iIndep s μ
) : Indep (limsup s atTop) (limsup s atTop) μ
参数：h_le : forall n, s n <= m0；h_indep : iIndep s μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.indep_limsup_atTop_self`：∀ {α : Type u_1} {Ω : 
Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {s : ι → MeasurableSpace Ω}  
 {m0 : MeasurableSpace Ω} {κ : Probabi…
-/
theorem indep_limsup_atTop_self (h_le : ∀ n, s n ≤ m0) (h_indep : iIndep s μ) :
    Indep (limsup s atTop) (limsup s atTop) μ :=
  Kernel.indep_limsup_atTop_self h_le h_indep
/-
**ProbabilityTheory.condIndep_limsup_atTop_self** 是 Mathlib 中的一个定理，位于命名空间 `Proba
bilityTheory`。
形式化陈述：condIndep_limsup_atTop_self [StandardBorelSpace Ω] (hm : m <= m0) [IsFinit
eMeasure μ] (h_le : forall n, s n <= m0) (h_indep : iCondIndep m hm s μ) : CondI
ndep m (limsup s atTop) (limsup s atTop) hm μ
参数：hm : m <= m0；h_le : forall n, s n <= m0；h_indep : iCondIndep m hm s μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.indep_limsup_atTop_self`：∀ {α : Type u_1} {Ω : 
Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {s : ι → MeasurableSpace Ω}  
 {m0 : MeasurableSpace Ω} {κ : Probabi…
-/
theorem condIndep_limsup_atTop_self [StandardBorelSpace Ω]
    (hm : m ≤ m0) [IsFiniteMeasure μ]
    (h_le : ∀ n, s n ≤ m0) (h_indep : iCondIndep m hm s μ) :
    CondIndep m (limsup s atTop) (limsup s atTop) hm μ :=
  Kernel.indep_limsup_atTop_self h_le h_indep
/-
**ProbabilityTheory.Kernel.measure_zero_or_one_of_measurableSet_limsup_atTop** 是
 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {
s : ι → MeasurableSpace Ω}   {m0 : MeasurableSpace Ω} {κ : ProbabilityTheory.Ker
nel α Ω} {μα : MeasureTheory.Measure α} [inst : SemilatticeSup ι]   [NoMaxOrder 
ι] [Nonempty ι],   (∀ (n : ι), s n ≤ m0) →     ProbabilityTheory.Kernel.iIndep s
 κ μα → ∀ {t : Set Ω}, MeasurableSet t → ∀ᵐ (a : α) ∂μα, (κ a) t = 0 ∨ (κ a) t =
 1
参数：∀ (n : ι), s n ≤ m0；a : α；κ a；κ a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.measure_eq_zero_or_one_of_indepSet_self'`：∀ {α 
: Type u_1} {Ω : Type u_2} {_mα : MeasurableSpace α} {m0 : MeasurableSpace Ω} {κ
 : ProbabilityTheory.Kernel α Ω}   {μα : MeasureTheory.…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.Kernel.iIndep.ae_isProbabilityMeasure`：∀ {α : Type u_1
} {Ω : Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {m : ι → MeasurableSpa
ce Ω}   {_mΩ : MeasurableSpace Ω} {κ : Probab…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `ProbabilityTheory.Kernel.Indep.indepSet_of_measurableSet`：∀ {α : Type u_
1} {Ω : Type u_2} {_mα : MeasurableSpace α} {m₁ m₂ x : MeasurableSpace Ω}   {κ :
 ProbabilityTheory.Kernel α Ω} {μ : MeasureThe…
· 使用定理 `ProbabilityTheory.Kernel.indep_limsup_atTop_self`：∀ {α : Type u_1} {Ω : 
Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {s : ι → MeasurableSpace Ω}  
 {m0 : MeasurableSpace Ω} {κ : Probabi…
-/
theorem Kernel.measure_zero_or_one_of_measurableSet_limsup_atTop (h_le : ∀ n, s n ≤ m0)
    (h_indep : iIndep s κ μα) {t : Set Ω} (ht_tail : MeasurableSet[limsup s atTop] t) :
    ∀ᵐ a ∂μα, κ a t = 0 ∨ κ a t = 1 := by
  apply measure_eq_zero_or_one_of_indepSet_self' ?_
    ((indep_limsup_atTop_self h_le h_indep).indepSet_of_measurableSet ht_tail ht_tail)
  filter_upwards [h_indep.ae_isProbabilityMeasure] with a ha using by infer_instance

/-- **Kolmogorov's 0-1 law** : any event in the tail σ-algebra of an independent sequence of
sub-σ-algebras has probability 0 or 1.
The tail σ-algebra `limsup s atTop` is the same as `⋂ n, ⋃ i ≥ n, s i`. -/
/-
**ProbabilityTheory.measure_zero_or_one_of_measurableSet_limsup_atTop** 是 Mathli
b 中的一个定理，位于命名空间 `ProbabilityTheory`。
形式化陈述：measure_zero_or_one_of_measurableSet_limsup_atTop (h_le : forall n, s n <=
 m0) (h_indep : iIndep s μ) {t : Set Ω} (ht_tail : MeasurableSet[limsup s atTop]
 t) : μ t = 0 ∨ μ t = 1
参数：h_le : forall n, s n <= m0；h_indep : iIndep s μ；ht_tail : MeasurableSet[limsu
p s atTop] t。
该定理/引理给出了一组等式。
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
· 使用定理 `ProbabilityTheory.Kernel.measure_zero_or_one_of_measurableSet_limsup_atT
op`：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {s 
: ι → MeasurableSpace Ω}   {m0 : MeasurableSpace Ω} {κ : Probabi…

--- 原说明 ---
**Kolmogorov's 0-1 law** : any event in the tail σ-algebra of an independent seq
uence of
sub-σ-algebras has probability 0 or 1.
The tail σ-algebra `limsup s atTop` is the same as `⋂ n, ⋃ i ≥ n, s i`.
-/
theorem measure_zero_or_one_of_measurableSet_limsup_atTop
    (h_le : ∀ n, s n ≤ m0)
    (h_indep : iIndep s μ) {t : Set Ω} (ht_tail : MeasurableSet[limsup s atTop] t) :
    μ t = 0 ∨ μ t = 1 := by
  simpa only [ae_dirac_eq, Filter.eventually_pure]
    using! Kernel.measure_zero_or_one_of_measurableSet_limsup_atTop h_le h_indep ht_tail
/-
**ProbabilityTheory.condExp_zero_or_one_of_measurableSet_limsup_atTop** 是 Mathli
b 中的一个定理，位于命名空间 `ProbabilityTheory`。
形式化陈述：condExp_zero_or_one_of_measurableSet_limsup_atTop [StandardBorelSpace Ω] (
hm : m <= m0) [IsFiniteMeasure μ] (h_le : forall n, s n <= m0) (h_indep : iCondI
ndep m hm s μ) {t : Set Ω} (ht_tail : MeasurableSet[limsup s atTop] t) : forallᵐ
 ω ∂μ, (μ⟦t | m⟧) ω = 0 ∨ (μ⟦t | m⟧) ω = 1
参数：hm : m <= m0；h_le : forall n, s n <= m0；h_indep : iCondIndep m hm s μ；ht_tail
 : MeasurableSet[limsup s atTop] t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.condExp_eq_zero_or_one_of_condIndepSet_self`：condExp_e
q_zero_or_one_of_condIndepSet_self [StandardBorelSpace Ω] (hm : m <= m0) [hμ : I
sFiniteMeasure μ] {t : Set Ω} (ht : MeasurableSet t…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Filter.limsup_le_iSup`：limsup_le_iSup {f : Filter β} {u : β -> α} : lims
up u f <= ⨆ n, u n
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `ProbabilityTheory.CondIndep.condIndepSet_of_measurableSet`：∀ {Ω : Type u
_1} {m' m₁ m₂ mΩ : MeasurableSpace Ω} [inst : StandardBorelSpace Ω] {hm' : m' ≤ 
mΩ}   {μ : MeasureTheory.Measure Ω} [inst_1 : M…
· 使用定理 `ProbabilityTheory.condIndep_limsup_atTop_self`：condIndep_limsup_atTop_se
lf [StandardBorelSpace Ω] (hm : m <= m0) [IsFiniteMeasure μ] (h_le : forall n, s
 n <= m0) (h_indep : iCondIndep m h…
-/
theorem condExp_zero_or_one_of_measurableSet_limsup_atTop [StandardBorelSpace Ω]
    (hm : m ≤ m0) [IsFiniteMeasure μ] (h_le : ∀ n, s n ≤ m0)
    (h_indep : iCondIndep m hm s μ) {t : Set Ω} (ht_tail : MeasurableSet[limsup s atTop] t) :
    ∀ᵐ ω ∂μ, (μ⟦t | m⟧) ω = 0 ∨ (μ⟦t | m⟧) ω = 1 :=
  condExp_eq_zero_or_one_of_condIndepSet_self hm (limsup_le_iSup.trans (iSup_le h_le) t ht_tail)
    ((condIndep_limsup_atTop_self hm h_le h_indep).condIndepSet_of_measurableSet ht_tail ht_tail)

end AtTop

section AtBot

variable [SemilatticeInf ι] [NoMinOrder ι] [Nonempty ι]

/-
**ProbabilityTheory.Kernel.indep_limsup_atBot_self** 是 Mathlib 中的一个定理，位于命名空间 `Pr
obabilityTheory.Kernel`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {
s : ι → MeasurableSpace Ω}   {m0 : MeasurableSpace Ω} {κ : ProbabilityTheory.Ker
nel α Ω} {μα : MeasureTheory.Measure α} [inst : SemilatticeInf ι]   [NoMinOrder 
ι] [Nonempty ι],   (∀ (n : ι), s n ≤ m0) →     ProbabilityTheory.Kernel.iIndep s
 κ μα →       ProbabilityTheory.Kernel.Indep (Filter.limsup s Filter.atBot) (Fil
ter.limsup s Filter.atBot) κ μα
参数：∀ (n : ι), s n ≤ m0；Filter.limsup s Filter.atBot；Filter.limsup s Filter.atBot
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bddBelow_Ici`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, BddBelow (Se
t.Ici a)
· 使用定理 `ProbabilityTheory.Kernel.indep_limsup_self`：∀ {α : Type u_1} {Ω : Type u
_2} {ι : Type u_3} {_mα : MeasurableSpace α} {s : ι → MeasurableSpace Ω}   {m0 :
 MeasurableSpace Ω} {κ : Probabi…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SemilatticeInf.instIsCodirectedOrder`：∀ {α : Type u_1} [inst : Semilatti
ceInf α], IsCodirectedOrder α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `NoMinOrder.exists_lt`：∀ {α : Type u_3} {inst : LT α} [self : NoMinOrder 
α] (a : α), ∃ b, b < a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `Antitone.directed_le`：Antitone.directed_le [Preorder α] [IsCodirectedOrd
er α] [Preorder β] {f : α -> β} (hf : Antitone f) : Directed (· <= ·) f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.Ici_subset_Ici`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.
Ici a ⊆ Set.Ici b ↔ b ≤ a
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem Kernel.indep_limsup_atBot_self (h_le : ∀ n, s n ≤ m0) (h_indep : iIndep s κ μα) :
    Indep (limsup s atBot) (limsup s atBot) κ μα := by
  let ns : ι → Set ι := Set.Ici
  have hnsp : ∀ i, BddBelow (ns i) := fun i => bddBelow_Ici
  refine indep_limsup_self h_le h_indep ?_ ?_ hnsp ?_
  · simp only [mem_atBot_sets, Set.mem_compl_iff, BddBelow, lowerBounds, Set.Nonempty]
    rintro t ⟨a, ha⟩
    obtain ⟨b, hb⟩ : ∃ b, b < a := exists_lt a
    refine ⟨b, fun c hc hct => ?_⟩
    suffices ∀ i ∈ t, c < i from lt_irrefl c (this c hct)
    exact fun i hi => hc.trans_lt (hb.trans_le (ha hi))
  · exact Antitone.directed_le fun _ _ ↦ Set.Ici_subset_Ici.2
  · exact fun n => ⟨n, le_rfl⟩
/-
**ProbabilityTheory.indep_limsup_atBot_self** 是 Mathlib 中的一个定理，位于命名空间 `Probabili
tyTheory`。
形式化陈述：indep_limsup_atBot_self (h_le : forall n, s n <= m0) (h_indep : iIndep s μ
) : Indep (limsup s atBot) (limsup s atBot) μ
参数：h_le : forall n, s n <= m0；h_indep : iIndep s μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.indep_limsup_atBot_self`：∀ {α : Type u_1} {Ω : 
Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {s : ι → MeasurableSpace Ω}  
 {m0 : MeasurableSpace Ω} {κ : Probabi…
-/
theorem indep_limsup_atBot_self
    (h_le : ∀ n, s n ≤ m0) (h_indep : iIndep s μ) :
    Indep (limsup s atBot) (limsup s atBot) μ :=
  Kernel.indep_limsup_atBot_self h_le h_indep
/-
**ProbabilityTheory.condIndep_limsup_atBot_self** 是 Mathlib 中的一个定理，位于命名空间 `Proba
bilityTheory`。
形式化陈述：condIndep_limsup_atBot_self [StandardBorelSpace Ω] (hm : m <= m0) [IsFinit
eMeasure μ] (h_le : forall n, s n <= m0) (h_indep : iCondIndep m hm s μ) : CondI
ndep m (limsup s atBot) (limsup s atBot) hm μ
参数：hm : m <= m0；h_le : forall n, s n <= m0；h_indep : iCondIndep m hm s μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.indep_limsup_atBot_self`：∀ {α : Type u_1} {Ω : 
Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {s : ι → MeasurableSpace Ω}  
 {m0 : MeasurableSpace Ω} {κ : Probabi…
-/
theorem condIndep_limsup_atBot_self [StandardBorelSpace Ω]
    (hm : m ≤ m0) [IsFiniteMeasure μ]
    (h_le : ∀ n, s n ≤ m0) (h_indep : iCondIndep m hm s μ) :
    CondIndep m (limsup s atBot) (limsup s atBot) hm μ :=
  Kernel.indep_limsup_atBot_self h_le h_indep

/-- **Kolmogorov's 0-1 law**, kernel version: any event in the tail σ-algebra of an independent
sequence of sub-σ-algebras has probability 0 or 1 almost surely. -/
/-
**ProbabilityTheory.Kernel.measure_zero_or_one_of_measurableSet_limsup_atBot** 是
 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {
s : ι → MeasurableSpace Ω}   {m0 : MeasurableSpace Ω} {κ : ProbabilityTheory.Ker
nel α Ω} {μα : MeasureTheory.Measure α} [inst : SemilatticeInf ι]   [NoMinOrder 
ι] [Nonempty ι],   (∀ (n : ι), s n ≤ m0) →     ProbabilityTheory.Kernel.iIndep s
 κ μα → ∀ {t : Set Ω}, MeasurableSet t → ∀ᵐ (a : α) ∂μα, (κ a) t = 0 ∨ (κ a) t =
 1
参数：∀ (n : ι), s n ≤ m0；a : α；κ a；κ a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.measure_eq_zero_or_one_of_indepSet_self'`：∀ {α 
: Type u_1} {Ω : Type u_2} {_mα : MeasurableSpace α} {m0 : MeasurableSpace Ω} {κ
 : ProbabilityTheory.Kernel α Ω}   {μα : MeasureTheory.…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.Kernel.iIndep.ae_isProbabilityMeasure`：∀ {α : Type u_1
} {Ω : Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {m : ι → MeasurableSpa
ce Ω}   {_mΩ : MeasurableSpace Ω} {κ : Probab…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `ProbabilityTheory.Kernel.Indep.indepSet_of_measurableSet`：∀ {α : Type u_
1} {Ω : Type u_2} {_mα : MeasurableSpace α} {m₁ m₂ x : MeasurableSpace Ω}   {κ :
 ProbabilityTheory.Kernel α Ω} {μ : MeasureThe…
· 使用定理 `ProbabilityTheory.Kernel.indep_limsup_atBot_self`：∀ {α : Type u_1} {Ω : 
Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {s : ι → MeasurableSpace Ω}  
 {m0 : MeasurableSpace Ω} {κ : Probabi…

--- 原说明 ---
**Kolmogorov's 0-1 law**, kernel version: any event in the tail σ-algebra of an 
independent
sequence of sub-σ-algebras has probability 0 or 1 almost surely.
-/
theorem Kernel.measure_zero_or_one_of_measurableSet_limsup_atBot (h_le : ∀ n, s n ≤ m0)
    (h_indep : iIndep s κ μα) {t : Set Ω} (ht_tail : MeasurableSet[limsup s atBot] t) :
    ∀ᵐ a ∂μα, κ a t = 0 ∨ κ a t = 1 := by
  apply measure_eq_zero_or_one_of_indepSet_self' ?_
    ((indep_limsup_atBot_self h_le h_indep).indepSet_of_measurableSet ht_tail ht_tail)
  filter_upwards [h_indep.ae_isProbabilityMeasure] with a ha using by infer_instance

/-- **Kolmogorov's 0-1 law** : any event in the tail σ-algebra of an independent sequence of
sub-σ-algebras has probability 0 or 1. -/
/-
**ProbabilityTheory.measure_zero_or_one_of_measurableSet_limsup_atBot** 是 Mathli
b 中的一个定理，位于命名空间 `ProbabilityTheory`。
形式化陈述：measure_zero_or_one_of_measurableSet_limsup_atBot (h_le : forall n, s n <=
 m0) (h_indep : iIndep s μ) {t : Set Ω} (ht_tail : MeasurableSet[limsup s atBot]
 t) : μ t = 0 ∨ μ t = 1
参数：h_le : forall n, s n <= m0；h_indep : iIndep s μ；ht_tail : MeasurableSet[limsu
p s atBot] t。
该定理/引理给出了一组等式。
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
· 使用定理 `ProbabilityTheory.Kernel.measure_zero_or_one_of_measurableSet_limsup_atB
ot`：∀ {α : Type u_1} {Ω : Type u_2} {ι : Type u_3} {_mα : MeasurableSpace α} {s 
: ι → MeasurableSpace Ω}   {m0 : MeasurableSpace Ω} {κ : Probabi…

--- 原说明 ---
**Kolmogorov's 0-1 law** : any event in the tail σ-algebra of an independent seq
uence of
sub-σ-algebras has probability 0 or 1.
-/
theorem measure_zero_or_one_of_measurableSet_limsup_atBot
    (h_le : ∀ n, s n ≤ m0) (h_indep : iIndep s μ) {t : Set Ω}
    (ht_tail : MeasurableSet[limsup s atBot] t) :
    μ t = 0 ∨ μ t = 1 := by
  simpa only [ae_dirac_eq, Filter.eventually_pure]
    using! Kernel.measure_zero_or_one_of_measurableSet_limsup_atBot h_le h_indep ht_tail

/-- **Kolmogorov's 0-1 law**, conditional version: any event in the tail σ-algebra of a
conditionally independent sequence of sub-σ-algebras has conditional probability 0 or 1. -/
/-
**ProbabilityTheory.condExp_zero_or_one_of_measurableSet_limsup_atBot** 是 Mathli
b 中的一个定理，位于命名空间 `ProbabilityTheory`。
形式化陈述：condExp_zero_or_one_of_measurableSet_limsup_atBot [StandardBorelSpace Ω] (
hm : m <= m0) [IsFiniteMeasure μ] (h_le : forall n, s n <= m0) (h_indep : iCondI
ndep m hm s μ) {t : Set Ω} (ht_tail : MeasurableSet[limsup s atBot] t) : forallᵐ
 ω ∂μ, (μ⟦t | m⟧) ω = 0 ∨ (μ⟦t | m⟧) ω = 1
参数：hm : m <= m0；h_le : forall n, s n <= m0；h_indep : iCondIndep m hm s μ；ht_tail
 : MeasurableSet[limsup s atBot] t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.condExp_eq_zero_or_one_of_condIndepSet_self`：condExp_e
q_zero_or_one_of_condIndepSet_self [StandardBorelSpace Ω] (hm : m <= m0) [hμ : I
sFiniteMeasure μ] {t : Set Ω} (ht : MeasurableSet t…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Filter.limsup_le_iSup`：limsup_le_iSup {f : Filter β} {u : β -> α} : lims
up u f <= ⨆ n, u n
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `ProbabilityTheory.CondIndep.condIndepSet_of_measurableSet`：∀ {Ω : Type u
_1} {m' m₁ m₂ mΩ : MeasurableSpace Ω} [inst : StandardBorelSpace Ω] {hm' : m' ≤ 
mΩ}   {μ : MeasureTheory.Measure Ω} [inst_1 : M…
· 使用定理 `ProbabilityTheory.condIndep_limsup_atBot_self`：condIndep_limsup_atBot_se
lf [StandardBorelSpace Ω] (hm : m <= m0) [IsFiniteMeasure μ] (h_le : forall n, s
 n <= m0) (h_indep : iCondIndep m h…

--- 原说明 ---
**Kolmogorov's 0-1 law**, conditional version: any event in the tail σ-algebra o
f a
conditionally independent sequence of sub-σ-algebras has conditional probability
 0 or 1.
-/
theorem condExp_zero_or_one_of_measurableSet_limsup_atBot [StandardBorelSpace Ω]
    (hm : m ≤ m0) [IsFiniteMeasure μ] (h_le : ∀ n, s n ≤ m0)
    (h_indep : iCondIndep m hm s μ) {t : Set Ω} (ht_tail : MeasurableSet[limsup s atBot] t) :
    ∀ᵐ ω ∂μ, (μ⟦t | m⟧) ω = 0 ∨ (μ⟦t | m⟧) ω = 1 :=
  condExp_eq_zero_or_one_of_condIndepSet_self hm (limsup_le_iSup.trans (iSup_le h_le) t ht_tail)
    ((condIndep_limsup_atBot_self hm h_le h_indep).condIndepSet_of_measurableSet ht_tail ht_tail)

end AtBot

end ProbabilityTheory

