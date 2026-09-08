/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Sub
public import Mathlib.MeasureTheory.Measure.Typeclasses.ZeroOne
public import Mathlib.Probability.Kernel.Composition.Prod

/-!
# Class `IsDeterministic` of deterministic kernels

This file defines the class `IsDeterministic` of deterministic kernels, and proves some
properties about them.

## Main definitions

* `Kernel.IsDeterministic`: a kernel is deterministic if copying then applying the kernel to the
  two copies is the same as first applying the kernel then copying.

## Main statements

* `isDeterministic_iff_isZeroOneMeasure`: a finite kernel is deterministic if and
  only if it is a zero-one measure for every input.
* `IsDeterministic.exists_eq_deterministic`: in a standard Borel space, a deterministic Markov
  kernel is a Dirac kernel of some measurable function.
* `comp_parallelComp_comp_copy`: if the composition of two Markov kernels `η ∘ₖ κ` is
  deterministic, the distribution over both `η ∘ₖ κ` and `κ` can be obtained by computing `η ∘ₖ κ`
  and `κ` independently. This corresponds to the equation of a Positive Markov category.
  See Example 11.25 of [fritz2020].

## Implementation notes

`comp_parallelComp_comp_copy` is true only when considering Markov kernels. To see why, consider
the counterexample with $X = Y = \{\varnothing\}$, kernels $\kappa(\cdot | \varnothing) = 2\delta_
{\varnothing}$ and $\eta(\cdot | \varnothing) = (1/2)\delta_{\varnothing}$: although their
composition is deterministic, the equation fails.

## References

* [A synthetic approach to
  Markov kernels, conditional independence and theorems on sufficient statistics][fritz2020]
* [Moss and Perrone, *A category-theoretic proof of the ergodic decomposition theorem*][moss2023]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

namespace ProbabilityTheory

/-- A kernel is deterministic if copying then applying the kernel to the two copies is the same
as first applying the kernel then copying. -/
/-
**ProbabilityTheory.IsDeterministic** 是 Mathlib 中的一个归纳类型，位于命名空间 `ProbabilityTheo
ry`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} → {mα : MeasurableSpace α} → {mβ : Measu
rableSpace β} → ProbabilityTheory.Kernel α β → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A kernel is deterministic if copying then applying the kernel to the two copies 
is the same
as first applying the kernel then copying.
-/
class IsDeterministic (κ : Kernel α β) : Prop where
  parallelComp_self_comp_copy' : (κ ∥ₖ κ) ∘ₖ Kernel.copy α = Kernel.copy β ∘ₖ κ

namespace Kernel

/-
**ProbabilityTheory.Kernel.parallelComp_self_comp_copy** 是 Mathlib 中的一个引理，位于命名空间
 `ProbabilityTheory.Kernel`。
形式化陈述：parallelComp_self_comp_copy {κ : Kernel α β} [IsDeterministic κ] : (κ ∥ₖ κ
) ∘ₖ Kernel.copy α = Kernel.copy β ∘ₖ κ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IsDeterministic.parallelComp_self_comp_copy'`：∀ {α : T
ype u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : P
robabilityTheory.Kernel α β}   [self : ProbabilityTh…
-/
lemma parallelComp_self_comp_copy {κ : Kernel α β} [IsDeterministic κ] :
    (κ ∥ₖ κ) ∘ₖ Kernel.copy α = Kernel.copy β ∘ₖ κ :=
  IsDeterministic.parallelComp_self_comp_copy'
/-
**ProbabilityTheory.Kernel.** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory.Kernel`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {f : α → β} (hf : Measurable f) : IsDeterministic (deterministic f hf) where
  parallelComp_self_comp_copy' := by
    simp_rw [parallelComp_comp_copy, deterministic_prod_deterministic, copy,
      deterministic_comp_deterministic, Function.comp_def, Function.diag_def]
/-
**ProbabilityTheory.Kernel.** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory.Kernel`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsDeterministic (mβ := mα) (Kernel.id (α := α)) := by unfold Kernel.id; infer_instance
/-
**ProbabilityTheory.Kernel.** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory.Kernel`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsDeterministic (copy α) := by unfold copy; infer_instance
/-
**ProbabilityTheory.Kernel.** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory.Kernel`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsDeterministic (discard α) := by unfold discard; infer_instance
/-
**ProbabilityTheory.Kernel.** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory.Kernel`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsDeterministic (swap α β) := by unfold swap; infer_instance

open IsZeroOneMeasure
/-
**ProbabilityTheory.Kernel.isDeterministic_iff_isZeroOneMeasure** 是 Mathlib 中的一个
引理，位于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：isDeterministic_iff_isZeroOneMeasure (κ : Kernel α β) [IsFiniteKernel κ] :
 IsDeterministic κ ↔ forall a, IsZeroOneMeasure (κ a)
参数：κ : Kernel α β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用引理 `ProbabilityTheory.Kernel.parallelComp_self_comp_copy`：parallelComp_self_
comp_copy {κ : Kernel α β} [IsDeterministic κ] : (κ ∥ₖ κ) ∘ₖ Kernel.copy α = Ker
nel.copy β ∘ₖ κ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.mul_eq_left`：∀ {a b : ENNReal}, a ≠ 0 → a ≠ ⊤ → (a * b = a ↔ b =
 1)
· 使用定理 `ProbabilityTheory.IsFiniteKernel.isFiniteMeasure`：∀ {α : Type u_1} {β : 
Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheo
ry.Kernel α β}   [ProbabilityTheory.Is…
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Set.inter_self`：inter_self (a : Set α) : a inter a = a
· 使用引理 `ProbabilityTheory.Kernel.copy_comp_apply_prod`：copy_comp_apply_prod (κ :
 Kernel α β) (a : α) {s t : Set β} (hs : MeasurableSet s) (ht : MeasurableSet t)
 : (copy β ∘ₖ κ) a (s ×ˢ t) = κ a (…
· 使用引理 `ProbabilityTheory.Kernel.prod_apply_prod`：prod_apply_prod {κ : Kernel α 
β} {η : Kernel α γ} [IsSFiniteKernel κ] [IsSFiniteKernel η] {s : Set β} {t : Set
 γ} {a : α} : (κ ×ₖ η) a (s ×ˢ…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用引理 `ProbabilityTheory.Kernel.parallelComp_comp_copy`：parallelComp_comp_copy 
(κ : Kernel α β) (η : Kernel α γ) : (κ ∥ₖ η) ∘ₖ copy α = κ ×ₖ η
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用引理 `ProbabilityTheory.Kernel.prod_apply`：prod_apply (κ : Kernel α β) [IsSFin
iteKernel κ] (η : Kernel α γ) [IsSFiniteKernel η] (a : α) : (κ ×ₖ η) a = (κ a).p
rod (η a)
· 使用定理 `MeasureTheory.Measure.prod_eq`：prod_eq {μ : Measure α} [SigmaFinite μ] {
ν : Measure β} [SigmaFinite ν] {μν : Measure (α × β)} (h : forall s t, Measurabl
eSet s -> Measurabl…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用引理 `MeasureTheory.IsZeroOneMeasure.measure_inter_eq_prod`：measure_inter_eq_p
rod {s t : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t) : μ (s inter t) 
= μ s * μ t
-/
lemma isDeterministic_iff_isZeroOneMeasure (κ : Kernel α β) [IsFiniteKernel κ] :
    IsDeterministic κ ↔ ∀ a, IsZeroOneMeasure (κ a) := by
  constructor
  · intro h a
    refine ⟨fun s hs ↦ ?_⟩
    have := DFunLike.congr_fun κ.parallelComp_self_comp_copy a |> DFunLike.congr_fun
      <| (s ×ˢ s)
    rw [parallelComp_comp_copy, prod_apply_prod, copy_comp_apply_prod, inter_self] at this
    · by_cases hκ : κ a s = 0
      · simp [hκ]
      · exact Or.inr <| (ENNReal.mul_eq_left hκ (by simp)).mp this
    all_goals exact hs
  · intro _
    refine ⟨?_⟩
    ext : 1
    rw [parallelComp_comp_copy, prod_apply]
    refine Measure.prod_eq fun s t hs ht ↦ ?_
    rw [copy_comp_apply_prod _ _ hs ht]
    exact measure_inter_eq_prod hs ht
/-
**ProbabilityTheory.Kernel.** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory.Kernel`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (κ : Kernel α β) [IsFiniteKernel κ] [IsDeterministic κ] : ∀ a, IsZeroOneMeasure (κ a) :=
  (isDeterministic_iff_isZeroOneMeasure κ).mp ‹_›

/-- in a standard Borel space, a deterministic Markov kernel is a Dirac kernel of one measurable
function. -/
/-
**ProbabilityTheory.Kernel.IsDeterministic.exists_eq_deterministic** 是 Mathlib 中
的一个定理，位于命名空间 `ProbabilityTheory.Kernel.IsDeterministic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} [StandardBorelSpace β]   (κ : ProbabilityTheory.Kernel α β) [Probability
Theory.IsMarkovKernel κ] [ProbabilityTheory.IsDeterministic κ],   ∃ f, ∃ (hf : M
easurable f), κ = ProbabilityTheory.Kernel.deterministic f hf
参数：κ : ProbabilityTheory.Kernel α β；hf : Measurable f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.dirac_apply'`：dirac_apply' (a : α) (hs : Measurabl
eSet s) : dirac a s = s.indicator 1 a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `Set.indicator_eq_one_iff_mem`：indicator_eq_one_iff_mem : indicator s 1 i
 = (1 : M₀) ↔ i in s
· 使用定理 `ENNReal.instNontrivial`：Nontrivial ENNReal
· 使用定理 `ProbabilityTheory.Kernel.measurable_coe`：∀ {α : Type u_1} {β : Type u_2}
 {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (κ : ProbabilityTheory.Kernel
 α β)   {s : Set β}, Measurab…
· 使用定理 `MeasurableSingletonClass.measurableSet_singleton`：∀ {α : Type u_7} {inst
 : MeasurableSpace α} [self : MeasurableSingletonClass α] (x : α), MeasurableSet
 {x}
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `standardBorel_of_polish`：∀ {α : Type u_1} [inst : MeasurableSpace α] [τ 
: TopologicalSpace α] [BorelSpace α] [PolishSpace α],   StandardBorelSpace α
· 使用定理 `PolishSpace.instENNReal`：PolishSpace ENNReal
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.IsZeroOneMeasure.exists_eq_dirac`：exists_eq_dirac [Standar
dBorelSpace α] [NeZero μ] : exists x₀, μ = Measure.dirac x₀
· 使用定理 `ProbabilityTheory.Kernel.instIsZeroOneMeasureCoeMeasureOfIsFiniteKernelO
fIsDeterministic`：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ :
 MeasurableSpace β} (κ : ProbabilityTheory.Kernel α β)   [ProbabilityTheory.Is…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `MeasureTheory.IsProbabilityMeasure.neZero`：∀ {α : Type u_1} {m0 : Measur
ableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure μ
], NeZero μ
· 使用定理 `ProbabilityTheory.IsMarkovKernel.is_probability_measure'`：∀ {α : Type u_
1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabi
lityTheory.Kernel α β}   [ProbabilityTheory.Is…
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
in a standard Borel space, a deterministic Markov kernel is a Dirac kernel of on
e measurable
function.
-/
theorem IsDeterministic.exists_eq_deterministic [StandardBorelSpace β] (κ : Kernel α β)
    [IsMarkovKernel κ] [IsDeterministic κ] :
    ∃ (f : α → β) (hf : Measurable f), κ = deterministic f hf := by
  choose f hf using fun a ↦ exists_eq_dirac (μ := κ a)
  refine ⟨f, ?_, ?_⟩
  · intro s hs
    have : f ⁻¹' s = (fun a => κ a s) ⁻¹' {1} := by
      simp only [preimage, mem_singleton_iff]
      simp_rw [hf, Measure.dirac_apply' _ hs]
      ext x
      exact (indicator_eq_one_iff_mem ENNReal).symm
    rw [this]
    exact κ.measurable_coe hs <| measurableSet_singleton 1
  · ext a : 1
    exact hf a

/-- The equation of a Positive Markov category: if the composition of two Markov kernels `η ∘ₖ κ` is
deterministic, the distribution over both `η ∘ₖ κ` and `κ` can be obtained by computing `η ∘ₖ κ`
and `κ` independently. -/
/-
**ProbabilityTheory.Kernel.comp_parallelComp_comp_copy** 是 Mathlib 中的一个引理，位于命名空间
 `ProbabilityTheory.Kernel`。
形式化陈述：comp_parallelComp_comp_copy {γ : Type*} [MeasurableSpace γ] {κ : Kernel α 
β} {η : Kernel β γ} [IsMarkovKernel κ] [IsMarkovKernel η] [IsDeterministic (η ∘ₖ
 κ)] : η ∘ₖ κ ∥ₖ κ ∘ₖ copy α = η ∥ₖ Kernel.id ∘ₖ copy β ∘ₖ κ
参数：η ∘ₖ κ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.Kernel.prod_apply`：prod_apply (κ : Kernel α β) [IsSFin
iteKernel κ] (η : Kernel α γ) [IsSFiniteKernel η] (a : α) : (κ ×ₖ η) a = (κ a).p
rod (η a)
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.comp`：∀ {α : Type u_1} {β : Typ
e u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {mγ : 
MeasurableSpace γ} (η : Probability…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `MeasureTheory.Measure.prod_eq`：prod_eq {μ : Measure α} [SigmaFinite μ] {
ν : Measure β} [SigmaFinite ν] {μν : Measure (α × β)} (h : forall s t, Measurabl
eSet s -> Measurabl…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `ProbabilityTheory.IsFiniteKernel.isFiniteMeasure`：∀ {α : Type u_1} {β : 
Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheo
ry.Kernel α β}   [ProbabilityTheory.Is…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.comp`：∀ {α : Type u_1} {β : Type
 u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {mγ : M
easurableSpace γ} (η : Probability…
· 使用定理 `ProbabilityTheory.Kernel.comp_apply'`：comp_apply' (η : Kernel β γ) (κ : 
Kernel α β) (a : α) {s : Set γ} (hs : MeasurableSet s) : (η ∘ₖ κ) a s = ∫⁻ b, η 
b s ∂κ a
· 使用定理 `MeasurableSet.prod`：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace
 α} {mβ : MeasurableSpace β} {s : Set α} {t : Set β},   MeasurableSet s → Measur
ableSet …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `ProbabilityTheory.Kernel.prod_apply_prod`：prod_apply_prod {κ : Kernel α 
β} {η : Kernel α γ} [IsSFiniteKernel κ] [IsSFiniteKernel η] {s : Set β} {t : Set
 γ} {a : α} : (κ ×ₖ η) a (s ×ˢ…
· 使用定理 `ProbabilityTheory.Kernel.instIsMarkovKernelId`：∀ {α : Type u_1} {mα : Me
asurableSpace α}, ProbabilityTheory.IsMarkovKernel ProbabilityTheory.Kernel.id
· 使用引理 `ProbabilityTheory.Kernel.id_apply`：id_apply (a : α) : Kernel.id a = Meas
ure.dirac a
· 使用定理 `MeasureTheory.Measure.dirac_apply'`：dirac_apply' (a : α) (hs : Measurabl
eSet s) : dirac a s = s.indicator 1 a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `MeasureTheory.lintegral_indicator`：lintegral_indicator {s : Set α} (hs :
 MeasurableSet s) (f : α -> Real>=0∞) : ∫⁻ a, s.indicator f a ∂μ = ∫⁻ a in s, f 
a ∂μ
· 使用定理 `MeasureTheory.Measure.zero_one`：∀ {α : Type u_1} {mα : MeasurableSpace α
} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZeroOneMeasure μ] (s : Set α), 
  μ s = 0 ∨ μ s = 1
· 使用定理 `ProbabilityTheory.Kernel.instIsZeroOneMeasureCoeMeasureOfIsFiniteKernelO
fIsDeterministic`：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ :
 MeasurableSpace β} (κ : ProbabilityTheory.Kernel α β)   [ProbabilityTheory.Is…
（共 60 条，此处仅展示前 30 条）

--- 原说明 ---
The equation of a Positive Markov category: if the composition of two Markov ker
nels `η ∘ₖ κ` is
deterministic, the distribution over both `η ∘ₖ κ` and `κ` can be obtained by co
mputing `η ∘ₖ κ`
and `κ` independently.
-/
lemma comp_parallelComp_comp_copy {γ : Type*} [MeasurableSpace γ] {κ : Kernel α β}
    {η : Kernel β γ} [IsMarkovKernel κ] [IsMarkovKernel η] [IsDeterministic (η ∘ₖ κ)] :
    η ∘ₖ κ ∥ₖ κ ∘ₖ copy α = η ∥ₖ Kernel.id ∘ₖ copy β ∘ₖ κ := by
  simp only [parallelComp_comp_copy]
  ext a : 1
  rw [prod_apply]
  refine Measure.prod_eq fun s t hs ht ↦ ?_
  rw [comp_apply' _ _ _ (hs.prod ht)]
  simp_rw [prod_apply_prod, Kernel.id_apply, Measure.dirac_apply' _ ht]
  have (b : β) : (η b) s * t.indicator 1 b = t.indicator (fun b ↦ η b s) b := by
    simp only [indicator]
    split_ifs
    all_goals simp_all
  simp_rw [this]
  rw [lintegral_indicator ht]
  rcases ((η ∘ₖ κ) a).zero_one s with (h₀ | h₁)
  · rw [h₀, zero_mul, setLIntegral_eq_zero_iff ht <| η.measurable_coe hs]
    rw [comp_apply' _ _ _ hs, lintegral_eq_zero_iff <| η.measurable_coe hs] at h₀
    filter_upwards [h₀] with x hx _ using hx
  · /- In Example 11.25 of [gritz2020], the case where `((η ∘ₖ κ) a) s = 1` is not explicitly
    treated. We prove it here by using the fact that the hypothesis implies that
    `((η ∘ₖ κ) a) sᶜ = 0`, and thus that the integral of `1 - (η b) s` over `κ a` is zero. -/
    rw [h₁, one_mul]
    have integral_le_kernel : ∫⁻ b in t, (η b) s ∂κ a ≤ κ a t := by
      calc
      _ ≤ ∫⁻ a in t, 1 ∂κ a := by
        refine lintegral_mono ?_
        intro b
        rw [← measure_univ (μ := η b)]
        exact measure_mono (by simp)
      _ = κ a t := by rw [setLIntegral_one]
    refine le_antisymm integral_le_kernel <| tsub_eq_zero_iff_le.mp ?_
    rw [← nonpos_iff_eq_zero]
    calc
    _ = ∫⁻ b in t, 1 ∂κ a - ∫⁻ b in t, (η b) s ∂κ a := by
      rw [setLIntegral_one]
    _ = ∫⁻ b in t, 1 - (η b) s ∂κ a := by
      rw [lintegral_sub]
      · exact η.measurable_coe hs
      · exact ne_top_of_le_ne_top (by simp) integral_le_kernel
      · refine ae_of_all _ fun b ↦ ?_
        rw [← measure_univ (μ := η b)]
        exact measure_mono (by simp)
    _ ≤ ∫⁻ b, 1 - (η b) s ∂κ a := setLIntegral_le_lintegral _ _
    _ = ∫⁻ x, (η x) sᶜ ∂κ a := by
        congr with x
        rw [measure_compl hs (by simp)]
        simp
    _ = (η ∘ₖ κ) a sᶜ := by
        rw [η.comp_apply' _ _ hs.compl]
    _ = 0 := by
      rw [measure_compl hs (by simp), measure_univ h₁, h₁, tsub_self]

end ProbabilityTheory.Kernel

