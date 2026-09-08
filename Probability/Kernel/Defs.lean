/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
# Markov Kernels

A kernel from a measurable space `α` to another measurable space `β` is a measurable map
`α → MeasureTheory.Measure β`, where the measurable space instance on `measure β` is the one defined
in `MeasureTheory.Measure.instMeasurableSpace`. That is, a kernel `κ` verifies that for all
measurable sets `s` of `β`, `a ↦ κ a s` is measurable.

## Main definitions

Classes of kernels:
* `ProbabilityTheory.Kernel α β`: kernels from `α` to `β`.
* `ProbabilityTheory.IsMarkovKernel κ`: a kernel from `α` to `β` is said to be a Markov kernel
  if for all `a : α`, `k a` is a probability measure.
* `ProbabilityTheory.IsZeroOrMarkovKernel κ`: a kernel from `α` to `β` which is zero or
  a Markov kernel.
* `ProbabilityTheory.IsFiniteKernel κ`: a kernel from `α` to `β` is said to be finite if there
  exists `C : ℝ≥0∞` such that `C < ∞` and for all `a : α`, `κ a univ ≤ C`. This implies in
  particular that all measures in the image of `κ` are finite, but is stronger since it requires a
  uniform bound. This stronger condition is necessary to ensure that the composition of two finite
  kernels is finite.
* `ProbabilityTheory.IsSFiniteKernel κ`: a kernel is called s-finite if it is a countable
  sum of finite kernels.

## Main statements

* `ProbabilityTheory.Kernel.ext_fun`: if `∫⁻ b, f b ∂(κ a) = ∫⁻ b, f b ∂(η a)` for all measurable
  functions `f` and all `a`, then the two kernels `κ` and `η` are equal.

-/

@[expose] public section

assert_not_exists MeasureTheory.integral

open MeasureTheory

open scoped ENNReal

namespace ProbabilityTheory

/-- A kernel from a measurable space `α` to another measurable space `β` is a measurable function
`κ : α → Measure β`. The measurable space structure on `MeasureTheory.Measure β` is given by
`MeasureTheory.Measure.instMeasurableSpace`. A map `κ : α → MeasureTheory.Measure β` is measurable
iff `∀ s : Set β, MeasurableSet s → Measurable (fun a ↦ κ a s)`. -/
/-
**ProbabilityTheory.Kernel** 是 Mathlib 中的一个归纳类型，位于命名空间 `ProbabilityTheory`。
形式化陈述：(α : Type u_1) → (β : Type u_2) → [MeasurableSpace α] → [MeasurableSpace β
] → Type (max u_1 u_2)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A kernel from a measurable space `α` to another measurable space `β` is a measur
able function
`κ : α → Measure β`. The measurable space structure on `MeasureTheory.Measure β`
 is given by
`MeasureTheory.Measure.instMeasurableSpace`. A map `κ : α → MeasureTheory.Measur
e β` is measurable
iff `∀ s : Set β, MeasurableSet s → Measurable (fun a ↦ κ a s)`.
-/
structure Kernel (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] where
  /-- The underlying function of a kernel.

  Do not use this function directly. Instead use the coercion coming from the `DFunLike`
  instance. -/
  toFun : α → Measure β
  /-- A kernel is a measurable map.

  Do not use this lemma directly. Use `Kernel.measurable` instead. -/
  measurable' : Measurable toFun

/-- Notation for `Kernel` with respect to a non-standard σ-algebra in the domain. -/
scoped notation "Kernel[" mα "] " α:arg β:arg => @Kernel α β mα _

/-- Notation for `Kernel` with respect to a non-standard σ-algebra in the domain and codomain. -/
scoped notation "Kernel[" mα ", " mβ "] " α:arg β:arg => @Kernel α β mα mβ

variable {α β ι : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

namespace Kernel

/-
**ProbabilityTheory.Kernel.instFunLike** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityThe
ory.Kernel`。
形式化陈述：instFunLike : FunLike (Kernel α β) α (Measure β) where coe
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instFunLike : FunLike (Kernel α β) α (Measure β) where
  coe := toFun
  coe_injective f g h := by cases f; cases g; congr

@[fun_prop]
/-
**ProbabilityTheory.Kernel.measurable** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheo
ry.Kernel`。
形式化陈述：measurable (κ : Kernel α β) : Measurable κ
参数：κ : Kernel α β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.measurable'`：∀ {α : Type u_1} {β : Type u_2} [i
nst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   (self : ProbabilityTheor
y.Kernel α β), Measurable …
-/
lemma measurable (κ : Kernel α β) : Measurable κ := κ.measurable'
/-
**ProbabilityTheory.Kernel.aemeasurable** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTh
eory.Kernel`。
形式化陈述：aemeasurable (κ : Kernel α β) {μ : Measure α} : AEMeasurable κ μ
参数：κ : Kernel α β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用引理 `ProbabilityTheory.Kernel.measurable`：measurable (κ : Kernel α β) : Measu
rable κ
-/
lemma aemeasurable (κ : Kernel α β) {μ : Measure α} : AEMeasurable κ μ := κ.measurable.aemeasurable
/-
**ProbabilityTheory.Kernel.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory.K
ernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} (f : α → MeasureTheory.Measure β)   (hf : Measurable f), ⇑{ toFun := f, 
measurable' := hf } = f
参数：f : α → MeasureTheory.Measure β；hf : Measurable f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_mk (f : α → Measure β) (hf) : mk f hf = f := rfl

initialize_simps_projections Kernel (toFun → apply)
/-
**ProbabilityTheory.Kernel.instZero** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory
.Kernel`。
形式化陈述：instZero : Zero (Kernel α β) where zero
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instZero : Zero (Kernel α β) where zero := ⟨0, measurable_zero⟩
/-
**ProbabilityTheory.Kernel.instAdd** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory.
Kernel`。
形式化陈述：instAdd : Add (Kernel α β) where add κ η
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance instAdd : Add (Kernel α β) where add κ η := ⟨κ + η, κ.2.add η.2⟩
/-
**ProbabilityTheory.Kernel.instSMulNat** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityThe
ory.Kernel`。
形式化陈述：instSMulNat : SMul Nat (Kernel α β) where smul n κ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance instSMulNat : SMul ℕ (Kernel α β) where
  smul n κ := ⟨n • κ, (measurable_const (a := n)).smul κ.2⟩
/-
**ProbabilityTheory.Kernel.** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory.Kernel`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsZeroApply (Kernel α β) α (Measure β) where
  zero_apply _ := rfl
/-
**ProbabilityTheory.Kernel.** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory.Kernel`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsAddApply (Kernel α β) α (Measure β) where
  add_apply _ _ _ := rfl
/-
**ProbabilityTheory.Kernel.** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory.Kernel`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsSMulApply ℕ (Kernel α β) α (Measure β) where
  smul_apply _ _ _ := rfl

@[deprecated (since := "2026-06-30")] alias coe_zero := FunLike.coe_zero
@[deprecated (since := "2026-06-30")] alias coe_add := FunLike.coe_add
@[deprecated (since := "2026-06-30")] alias coe_nsmul := FunLike.coe_smul

@[deprecated (since := "2026-06-30")] protected alias zero_apply := zero_apply
@[deprecated (since := "2026-06-30")] protected alias add_apply := add_apply
@[deprecated (since := "2026-06-30")] protected alias nsmul_apply := smul_apply
/-
**ProbabilityTheory.Kernel.instAddCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Probabil
ityTheory.Kernel`。
形式化陈述：instAddCommMonoid : AddCommMonoid (Kernel α β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance instAddCommMonoid : AddCommMonoid (Kernel α β) :=
  fast_instance% FunLike.addCommMonoid
/-
**ProbabilityTheory.Kernel.instPartialOrder** 是 Mathlib 中的一个实例，位于命名空间 `Probabili
tyTheory.Kernel`。
形式化陈述：instPartialOrder : PartialOrder (Kernel α β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instPartialOrder : PartialOrder (Kernel α β) := .lift _ DFunLike.coe_injective
/-
**ProbabilityTheory.Kernel.** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory.Kernel`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] :
    AddLeftMono (Kernel α β) :=
  ⟨fun _ _ _ hμ a ↦ add_le_add_right (hμ a) _⟩

noncomputable
/-
**ProbabilityTheory.Kernel.instOrderBot** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTh
eory.Kernel`。
形式化陈述：instOrderBot {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] : Order
Bot (Kernel α β) where bot
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instOrderBot {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] :
    OrderBot (Kernel α β) where
  bot := 0
  bot_le κ a := by simp only [zero_apply, Measure.zero_le]

@[deprecated (since := "2026-06-30")] alias coeAddHom := FunLike.coe_coeAddMonoidHom

@[deprecated (since := "2026-06-30")] alias coeAddHom_apply := FunLike.coeAddMonoidHom_apply

@[deprecated (since := "2026-06-30")] alias coe_finsetSum := FunLike.coe_sum

@[deprecated (since := "2026-04-08")] alias coe_finset_sum := FunLike.coe_sum

@[deprecated (since := "2026-06-30")] alias finsetSum_apply := sum_apply

@[deprecated (since := "2026-04-08")] alias finset_sum_apply := sum_apply
/-
**ProbabilityTheory.Kernel.finsetSum_apply'** 是 Mathlib 中的一个定理，位于命名空间 `Probabili
tyTheory.Kernel`。
形式化陈述：finsetSum_apply' (I : Finset ι) (κ : ι -> Kernel α β) (a : α) (s : Set β) 
: (∑ i in I, κ i) a s = ∑ i in I, κ i a s
参数：I : Finset ι；κ : ι -> Kernel α β；a : α；s : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sum_apply`：∀ {F : Type u_8} {α : Type u_9} {β : Type u_10} {ι : Type u_1
1} [inst : FunLike F α β] [inst_1 : AddCommMonoid β]   [inst_2 : AddCommMonoid …
· 使用定理 `ProbabilityTheory.Kernel.instIsZeroApplyMeasure`：∀ {α : Type u_1} {β : T
ype u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β},   IsZeroApply (Proba
bilityTheory.Kernel α β) α (MeasureTh…
· 使用定理 `ProbabilityTheory.Kernel.instIsAddApplyMeasure`：∀ {α : Type u_1} {β : Ty
pe u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β},   IsAddApply (Probabi
lityTheory.Kernel α β) α (MeasureThe…
· 使用定理 `MeasureTheory.Measure.finsetSum_apply`：finsetSum_apply {m : MeasurableSp
ace α} (I : Finset ι) (μ : ι -> Measure α) (s : Set α) : (∑ i in I, μ i) s = ∑ i
 in I, μ i s
-/
theorem finsetSum_apply' (I : Finset ι) (κ : ι → Kernel α β) (a : α) (s : Set β) :
    (∑ i ∈ I, κ i) a s = ∑ i ∈ I, κ i a s := by rw [sum_apply, Measure.finsetSum_apply]

@[deprecated (since := "2026-04-08")] alias finset_sum_apply' := finsetSum_apply'

end Kernel

/-- A kernel is a Markov kernel if every measure in its image is a probability measure. -/
/-
**ProbabilityTheory.IsMarkovKernel** 是 Mathlib 中的一个归纳类型，位于命名空间 `ProbabilityTheor
y`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} → {mα : MeasurableSpace α} → {mβ : Measu
rableSpace β} → ProbabilityTheory.Kernel α β → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A kernel is a Markov kernel if every measure in its image is a probability measu
re.
-/
class IsMarkovKernel (κ : Kernel α β) : Prop where
  isProbabilityMeasure : ∀ a, IsProbabilityMeasure (κ a)

/-- A class for kernels which are zero or a Markov kernel. -/
/-
**ProbabilityTheory.IsZeroOrMarkovKernel** 是 Mathlib 中的一个归纳类型，位于命名空间 `Probabilit
yTheory`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} → {mα : MeasurableSpace α} → {mβ : Measu
rableSpace β} → ProbabilityTheory.Kernel α β → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A class for kernels which are zero or a Markov kernel.
-/
class IsZeroOrMarkovKernel (κ : Kernel α β) : Prop where
  eq_zero_or_isMarkovKernel' : κ = 0 ∨ IsMarkovKernel κ

/-- A kernel is finite if every measure in its image is finite, with a uniform bound. -/
/-
**ProbabilityTheory.IsFiniteKernel** 是 Mathlib 中的一个归纳类型，位于命名空间 `ProbabilityTheor
y`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} → {mα : MeasurableSpace α} → {mβ : Measu
rableSpace β} → ProbabilityTheory.Kernel α β → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A kernel is finite if every measure in its image is finite, with a uniform bound
.
-/
class IsFiniteKernel (κ : Kernel α β) : Prop where
  exists_univ_le : ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ a, κ a Set.univ ≤ C
/-
**ProbabilityTheory.eq_zero_or_isMarkovKernel** 是 Mathlib 中的一个定理，位于命名空间 `Probabi
lityTheory`。
形式化陈述：eq_zero_or_isMarkovKernel (κ : Kernel α β) [h : IsZeroOrMarkovKernel κ] : 
κ = 0 ∨ IsMarkovKernel κ
参数：κ : Kernel α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.eq_zero_or_isMarkovKernel'`：∀ {α 
: Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ 
: ProbabilityTheory.Kernel α β}   [self : ProbabilityTh…
-/
theorem eq_zero_or_isMarkovKernel
    (κ : Kernel α β) [h : IsZeroOrMarkovKernel κ] :
    κ = 0 ∨ IsMarkovKernel κ :=
  h.eq_zero_or_isMarkovKernel'

/-- A constant `C : ℝ≥0∞` such that `C < ∞` for a finite kernel
(`ProbabilityTheory.IsFiniteKernel.bound_lt_top κ`) and for all `a : α` and `s : Set β`,
`κ a s ≤ C` (`ProbabilityTheory.Kernel.measure_le_bound κ a s`). -/
/-
**ProbabilityTheory.Kernel.bound** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory.Ke
rnel`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} → {mα : MeasurableSpace α} → {mβ : Measu
rableSpace β} → ProbabilityTheory.Kernel α β → ENNReal
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A constant `C : ℝ≥0∞` such that `C < ∞` for a finite kernel
(`ProbabilityTheory.IsFiniteKernel.bound_lt_top κ`) and for all `a : α` and `s :
 Set β`,
`κ a s ≤ C` (`ProbabilityTheory.Kernel.measure_le_bound κ a s`).
-/
noncomputable def Kernel.bound (κ : Kernel α β) : ℝ≥0∞ :=
  ⨆ a, κ a Set.univ

namespace Kernel

/-
**ProbabilityTheory.Kernel.bound_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTh
eory.Kernel`。
形式化陈述：bound_lt_top (κ : Kernel α β) [h : IsFiniteKernel κ] : κ.bound < ∞
参数：κ : Kernel α β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IsFiniteKernel.exists_univ_le`：∀ {α : Type u_1} {β : T
ype u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheor
y.Kernel α β}   [self : ProbabilityTh…
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem bound_lt_top (κ : Kernel α β) [h : IsFiniteKernel κ] : κ.bound < ∞ := by
  obtain ⟨C, hC, hle⟩ := h.exists_univ_le
  refine lt_of_le_of_lt ?_ hC
  simp [bound, hle]
/-
**ProbabilityTheory.Kernel.bound_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTh
eory.Kernel`。
形式化陈述：bound_ne_top (κ : Kernel α β) [IsFiniteKernel κ] : κ.bound != ∞
参数：κ : Kernel α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `ProbabilityTheory.Kernel.bound_lt_top`：bound_lt_top (κ : Kernel α β) [h 
: IsFiniteKernel κ] : κ.bound < ∞
-/
theorem bound_ne_top (κ : Kernel α β) [IsFiniteKernel κ] :
    κ.bound ≠ ∞ := κ.bound_lt_top.ne
/-
**ProbabilityTheory.Kernel.measure_le_bound** 是 Mathlib 中的一个定理，位于命名空间 `Probabili
tyTheory.Kernel`。
形式化陈述：measure_le_bound (κ : Kernel α β) (a : α) (s : Set β) : κ a s <= κ.bound
参数：κ : Kernel α β；a : α；s : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
-/
theorem measure_le_bound (κ : Kernel α β) (a : α) (s : Set β) :
    κ a s ≤ κ.bound :=
  (measure_mono (Set.subset_univ s)).trans <| le_iSup (f := fun a ↦ κ a .univ) a

@[simp]
/-
**ProbabilityTheory.Kernel.bound_eq_zero_of_isEmpty** 是 Mathlib 中的一个引理，位于命名空间 `P
robabilityTheory.Kernel`。
形式化陈述：bound_eq_zero_of_isEmpty [IsEmpty α] (κ : Kernel α β) : κ.bound = 0
参数：κ : Kernel α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ciSup_of_empty`：ciSup_of_empty [IsEmpty ι] (f : ι -> α) : ⨆ i, f i = ⊥
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma bound_eq_zero_of_isEmpty [IsEmpty α] (κ : Kernel α β) :
    κ.bound = 0 := by simp [bound]

@[simp]
/-
**ProbabilityTheory.Kernel.bound_eq_zero_of_isEmpty'** 是 Mathlib 中的一个引理，位于命名空间 `
ProbabilityTheory.Kernel`。
形式化陈述：bound_eq_zero_of_isEmpty' [IsEmpty β] (κ : Kernel α β) : κ.bound = 0
参数：κ : Kernel α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `ENNReal.iSup_zero`：∀ {ι : Sort u_1}, ⨆ x, 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma bound_eq_zero_of_isEmpty' [IsEmpty β] (κ : Kernel α β) :
    κ.bound = 0 := by simp [bound, Subsingleton.elim _ (0 : Measure β)]

@[simp]
/-
**ProbabilityTheory.Kernel.bound_zero** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheo
ry.Kernel`。
形式化陈述：bound_zero : bound (0 : Kernel α β) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ProbabilityTheory.Kernel.instIsZeroApplyMeasure`：∀ {α : Type u_1} {β : T
ype u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β},   IsZeroApply (Proba
bilityTheory.Kernel α β) α (MeasureTh…
· 使用定理 `ENNReal.iSup_zero`：∀ {ι : Sort u_1}, ⨆ x, 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma bound_zero : bound (0 : Kernel α β) = 0 := by
  simp [bound]

end Kernel

/-
**ProbabilityTheory.isFiniteKernel_zero** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTh
eory`。
形式化陈述：isFiniteKernel_zero (α β : Type*) {_ : MeasurableSpace α} {_ : MeasurableS
pace β} : IsFiniteKernel (0 : Kernel α β)
参数：α β : Type*。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.coe_lt_top`：∀ {r : NNReal}, ↑r < ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ProbabilityTheory.Kernel.instIsZeroApplyMeasure`：∀ {α : Type u_1} {β : T
ype u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β},   IsZeroApply (Proba
bilityTheory.Kernel α β) α (MeasureTh…
-/
instance isFiniteKernel_zero (α β : Type*) {_ : MeasurableSpace α} {_ : MeasurableSpace β} :
    IsFiniteKernel (0 : Kernel α β) :=
  ⟨⟨0, ENNReal.coe_lt_top, fun _ => by simp⟩⟩
/-
**ProbabilityTheory.IsFiniteKernel.add** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityThe
ory.IsFiniteKernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} (κ η : ProbabilityTheory.Kernel α β)   [ProbabilityTheory.IsFiniteKernel
 κ] [ProbabilityTheory.IsFiniteKernel η], ProbabilityTheory.IsFiniteKernel (κ + 
η)
参数：κ η : ProbabilityTheory.Kernel α β；κ + η。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.add_lt_top`：∀ {a b : ENNReal}, a + b < ⊤ ↔ a < ⊤ ∧ b < ⊤
· 使用定理 `ProbabilityTheory.Kernel.bound_lt_top`：bound_lt_top (κ : Kernel α β) [h 
: IsFiniteKernel κ] : κ.bound < ∞
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `ProbabilityTheory.Kernel.measure_le_bound`：measure_le_bound (κ : Kernel 
α β) (a : α) (s : Set β) : κ a s <= κ.bound
-/
instance IsFiniteKernel.add (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    IsFiniteKernel (κ + η) := by
  refine ⟨⟨κ.bound + η.bound, ENNReal.add_lt_top.mpr ⟨κ.bound_lt_top, η.bound_lt_top⟩, fun a => ?_⟩⟩
  exact add_le_add (Kernel.measure_le_bound _ _ _) (Kernel.measure_le_bound _ _ _)
/-
**ProbabilityTheory.isFiniteKernel_of_le** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityT
heory`。
形式化陈述：isFiniteKernel_of_le {κ ν : Kernel α β} [hν : IsFiniteKernel ν] (hκν : κ <
= ν) : IsFiniteKernel κ
参数：hκν : κ <= ν。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.bound_lt_top`：bound_lt_top (κ : Kernel α β) [h 
: IsFiniteKernel κ] : κ.bound < ∞
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `ProbabilityTheory.Kernel.measure_le_bound`：measure_le_bound (κ : Kernel 
α β) (a : α) (s : Set β) : κ a s <= κ.bound
-/
lemma isFiniteKernel_of_le {κ ν : Kernel α β} [hν : IsFiniteKernel ν] (hκν : κ ≤ ν) :
    IsFiniteKernel κ :=
  ⟨ν.bound, ν.bound_lt_top, fun a ↦ (hκν _ _).trans (ν.measure_le_bound a Set.univ)⟩

variable {κ η : Kernel α β}
/-
**ProbabilityTheory.IsMarkovKernel.is_probability_measure'** 是 Mathlib 中的一个定理，位于
命名空间 `ProbabilityTheory.IsMarkovKernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} {κ : ProbabilityTheory.Kernel α β}   [ProbabilityTheory.IsMarkovKernel κ
] (a : α), MeasureTheory.IsProbabilityMeasure (κ a)
参数：a : α；κ a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IsMarkovKernel.isProbabilityMeasure`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [self : ProbabilityTh…
-/
instance IsMarkovKernel.is_probability_measure' [IsMarkovKernel κ] (a : α) :
    IsProbabilityMeasure (κ a) :=
  IsMarkovKernel.isProbabilityMeasure a
/-
**ProbabilityTheory.** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsZeroOrMarkovKernel (0 : Kernel α β) := ⟨Or.inl rfl⟩
/-
**ProbabilityTheory.** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) IsMarkovKernel.IsZeroOrMarkovKernel [h : IsMarkovKernel κ] :
    IsZeroOrMarkovKernel κ := ⟨Or.inr h⟩
/-
**ProbabilityTheory.** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) IsZeroOrMarkovKernel.isZeroOrProbabilityMeasure
    [IsZeroOrMarkovKernel κ] (a : α) : IsZeroOrProbabilityMeasure (κ a) := by
  rcases eq_zero_or_isMarkovKernel κ with rfl | h'
  · simp only [zero_apply]
    infer_instance
  · infer_instance
/-
**ProbabilityTheory.IsFiniteKernel.isFiniteMeasure** 是 Mathlib 中的一个定理，位于命名空间 `Pr
obabilityTheory.IsFiniteKernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} {κ : ProbabilityTheory.Kernel α β}   [ProbabilityTheory.IsFiniteKernel κ
] (a : α), MeasureTheory.IsFiniteMeasure (κ a)
参数：a : α；κ a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `ProbabilityTheory.Kernel.measure_le_bound`：measure_le_bound (κ : Kernel 
α β) (a : α) (s : Set β) : κ a s <= κ.bound
· 使用定理 `ProbabilityTheory.Kernel.bound_lt_top`：bound_lt_top (κ : Kernel α β) [h 
: IsFiniteKernel κ] : κ.bound < ∞
-/
instance IsFiniteKernel.isFiniteMeasure [IsFiniteKernel κ] (a : α) : IsFiniteMeasure (κ a) :=
  ⟨(κ.measure_le_bound a Set.univ).trans_lt κ.bound_lt_top⟩
/-
**ProbabilityTheory.** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) IsZeroOrMarkovKernel.isFiniteKernel [h : IsZeroOrMarkovKernel κ] :
    IsFiniteKernel κ := by
  rcases eq_zero_or_isMarkovKernel κ with rfl | _h'
  · infer_instance
  · exact ⟨⟨1, ENNReal.one_lt_top, fun _ => prob_le_one⟩⟩

namespace Kernel

@[simp]
/-
**ProbabilityTheory.Kernel.bound_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTh
eory.Kernel`。
形式化陈述：bound_eq_one [Nonempty α] (κ : Kernel α β) [IsMarkovKernel κ] : κ.bound = 
1
参数：κ : Kernel α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `ProbabilityTheory.IsMarkovKernel.is_probability_measure'`：∀ {α : Type u_
1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabi
lityTheory.Kernel α β}   [ProbabilityTheory.Is…
· 使用定理 `ciSup_const`：ciSup_const [hι : Nonempty ι] {a : α} : ⨆ _ : ι, a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma bound_eq_one [Nonempty α] (κ : Kernel α β) [IsMarkovKernel κ] :
    κ.bound = 1 := by simp [bound]

@[simp]
/-
**ProbabilityTheory.Kernel.bound_le_one** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTh
eory.Kernel`。
形式化陈述：bound_le_one (κ : Kernel α β) [IsZeroOrMarkovKernel κ] : κ.bound <= 1
参数：κ : Kernel α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.Kernel.bound_eq_zero_of_isEmpty`：bound_eq_zero_of_isEm
pty [IsEmpty α] (κ : Kernel α β) : κ.bound = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ProbabilityTheory.eq_zero_or_isMarkovKernel`：eq_zero_or_isMarkovKernel (
κ : Kernel α β) [h : IsZeroOrMarkovKernel κ] : κ = 0 ∨ IsMarkovKernel κ
· 使用引理 `ProbabilityTheory.Kernel.bound_zero`：bound_zero : bound (0 : Kernel α β)
 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.Kernel.bound_eq_one`：bound_eq_one [Nonempty α] (κ : Ke
rnel α β) [IsMarkovKernel κ] : κ.bound = 1
-/
lemma bound_le_one (κ : Kernel α β) [IsZeroOrMarkovKernel κ] :
    κ.bound ≤ 1 := by
  rcases isEmpty_or_nonempty α
  · simp
  · rcases eq_zero_or_isMarkovKernel κ with rfl | _ <;> simp

@[ext]
/-
**ProbabilityTheory.Kernel.ext** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory.Kern
el`。
形式化陈述：ext (h : forall a, κ a = η a) : κ = η
参数：h : forall a, κ a = η a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext (h : ∀ a, κ a = η a) : κ = η := DFunLike.ext _ _ h
/-
**ProbabilityTheory.Kernel.ext_iff'** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory
.Kernel`。
形式化陈述：ext_iff' : κ = η ↔ forall a s, MeasurableSet s -> κ a s = η a s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ext_iff' : κ = η ↔ ∀ a s, MeasurableSet s → κ a s = η a s := by
  simp_rw [Kernel.ext_iff, Measure.ext_iff]
/-
**ProbabilityTheory.Kernel.ext_fun** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory.
Kernel`。
形式化陈述：ext_fun (h : forall a f, Measurable f -> ∫⁻ b, f b ∂κ a = ∫⁻ b, f b ∂η a) 
: κ = η
参数：h : forall a f, Measurable f -> ∫⁻ b, f b ∂κ a = ∫⁻ b, f b ∂η a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `MeasureTheory.lintegral_indicator_const`：lintegral_indicator_const {s : 
Set α} (hs : MeasurableSet s) (c : Real>=0∞) : ∫⁻ a, s.indicator (fun _ => c) a 
∂μ = c * μ s
· 使用定理 `Measurable.indicator`：Measurable.indicator [Zero β] (hf : Measurable f) 
(hs : MeasurableSet s) : Measurable (s.indicator f)
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
-/
theorem ext_fun (h : ∀ a f, Measurable f → ∫⁻ b, f b ∂κ a = ∫⁻ b, f b ∂η a) :
    κ = η := by
  ext a s hs
  specialize h a (s.indicator fun _ => 1) (Measurable.indicator measurable_const hs)
  simp_rw [lintegral_indicator_const hs, one_mul] at h
  rw [h]
/-
**ProbabilityTheory.Kernel.ext_fun_iff** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityThe
ory.Kernel`。
形式化陈述：ext_fun_iff : κ = η ↔ forall a f, Measurable f -> ∫⁻ b, f b ∂κ a = ∫⁻ b, f
 b ∂η a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.ext_fun`：ext_fun (h : forall a f, Measurable f 
-> ∫⁻ b, f b ∂κ a = ∫⁻ b, f b ∂η a) : κ = η
-/
theorem ext_fun_iff : κ = η ↔ ∀ a f, Measurable f → ∫⁻ b, f b ∂κ a = ∫⁻ b, f b ∂η a :=
  ⟨fun h a f _ => by rw [h], ext_fun⟩

section IsEmptyNonempty

/-
**ProbabilityTheory.Kernel.** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory.Kernel`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsEmpty β] : Subsingleton (Kernel α β) where
  allEq κ η := by ext a s; simp [Set.eq_empty_of_isEmpty s]
/-
**ProbabilityTheory.Kernel.** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory.Kernel`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsEmpty α] (κ : Kernel α β) : IsMarkovKernel κ where
  isProbabilityMeasure := by simp
/-
**ProbabilityTheory.Kernel.** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory.Kernel`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsEmpty β] (κ : Kernel α β) : IsZeroOrMarkovKernel κ where
  eq_zero_or_isMarkovKernel' := by
    left
    ext a s
    simp [Set.eq_empty_of_isEmpty s]
/-
**ProbabilityTheory.Kernel.not_isMarkovKernel_zero** 是 Mathlib 中的一个引理，位于命名空间 `Pr
obabilityTheory.Kernel`。
形式化陈述：not_isMarkovKernel_zero [Nonempty α] : ¬ IsMarkovKernel (0 : Kernel α β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `ProbabilityTheory.IsMarkovKernel.isProbabilityMeasure`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [self : ProbabilityTh…
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
-/
lemma not_isMarkovKernel_zero [Nonempty α] : ¬ IsMarkovKernel (0 : Kernel α β) := by
  by_contra h
  let x : α := Nonempty.some inferInstance
  have h1 : (0 : Measure β) .univ = 1 := (h.isProbabilityMeasure x).measure_univ
  simp at h1

end IsEmptyNonempty

/-
**ProbabilityTheory.Kernel.measurable_coe** 是 Mathlib 中的一个定理，位于命名空间 `Probability
Theory.Kernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} (κ : ProbabilityTheory.Kernel α β)   {s : Set β}, MeasurableSet s → Meas
urable fun a => (κ a) s
参数：κ : ProbabilityTheory.Kernel α β；κ a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `MeasureTheory.Measure.measurable_coe`：measurable_coe {s : Set α} (hs : M
easurableSet s) : Measurable fun μ : Measure α => μ s
· 使用引理 `ProbabilityTheory.Kernel.measurable`：measurable (κ : Kernel α β) : Measu
rable κ
-/
protected theorem measurable_coe (κ : Kernel α β) {s : Set β} (hs : MeasurableSet s) :
    Measurable fun a => κ a s :=
  (Measure.measurable_coe hs).comp κ.measurable
/-
**ProbabilityTheory.Kernel.apply_congr_of_mem_measurableAtom** 是 Mathlib 中的一个引理，
位于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：apply_congr_of_mem_measurableAtom (κ : Kernel α β) {y' y : α} (hy' : y' in
 measurableAtom y) : κ y' = κ y
参数：κ : Kernel α β；hy' : y' in measurableAtom y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用引理 `mem_of_mem_measurableAtom`：mem_of_mem_measurableAtom {x y : β} (h : y in
 measurableAtom x) {s : Set β} (hs : MeasurableSet s) (hxs : x in s) : y in s
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
-/
lemma apply_congr_of_mem_measurableAtom (κ : Kernel α β) {y' y : α} (hy' : y' ∈ measurableAtom y) :
    κ y' = κ y := by
  ext s hs
  exact mem_of_mem_measurableAtom hy' (κ.measurable_coe hs (measurableSet_singleton (κ y s))) rfl
/-
**ProbabilityTheory.Kernel.eq_zero_of_isEmpty_left** 是 Mathlib 中的一个引理，位于命名空间 `Pr
obabilityTheory.Kernel`。
形式化陈述：eq_zero_of_isEmpty_left (κ : Kernel α β) [h : IsEmpty α] : κ = 0
参数：κ : Kernel α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
-/
lemma eq_zero_of_isEmpty_left (κ : Kernel α β) [h : IsEmpty α] : κ = 0 := by
  ext a
  exact h.elim a
/-
**ProbabilityTheory.Kernel.eq_zero_of_isEmpty_right** 是 Mathlib 中的一个引理，位于命名空间 `P
robabilityTheory.Kernel`。
形式化陈述：eq_zero_of_isEmpty_right (κ : Kernel α β) [IsEmpty β] : κ = 0
参数：κ : Kernel α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.eq_zero_of_isEmpty`：eq_zero_of_isEmpty [IsEmpty α]
 {_m : MeasurableSpace α} (μ : Measure α) : μ = 0
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ProbabilityTheory.Kernel.instIsZeroApplyMeasure`：∀ {α : Type u_1} {β : T
ype u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β},   IsZeroApply (Proba
bilityTheory.Kernel α β) α (MeasureTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma eq_zero_of_isEmpty_right (κ : Kernel α β) [IsEmpty β] : κ = 0 := by
  ext a
  simp [Measure.eq_zero_of_isEmpty (κ a)]

section Sum

/-- Sum of an indexed family of kernels. -/
/-
**ProbabilityTheory.Kernel.sum** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory.Kern
el`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} →     {ι : Type u_3} →       {mα : Measu
rableSpace α} →         {mβ : MeasurableSpace β} → [Countable ι] → (ι → Probabil
ityTheory.Kernel α β) → ProbabilityTheory.Kernel α β
参数：ι → ProbabilityTheory.Kernel α β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Sum of an indexed family of kernels.
-/
protected noncomputable def sum [Countable ι] (κ : ι → Kernel α β) : Kernel α β where
  toFun a := Measure.sum fun n => κ n a
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    simp_rw [Measure.sum_apply _ hs]
    exact Measurable.tsum fun n => Kernel.measurable_coe (κ n) hs
/-
**ProbabilityTheory.Kernel.sum_apply** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheor
y.Kernel`。
形式化陈述：sum_apply [Countable ι] (κ : ι -> Kernel α β) (a : α) : Kernel.sum κ a = M
easure.sum fun n => κ n a
参数：κ : ι -> Kernel α β；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sum_apply [Countable ι] (κ : ι → Kernel α β) (a : α) :
    Kernel.sum κ a = Measure.sum fun n => κ n a :=
  rfl
/-
**ProbabilityTheory.Kernel.sum_apply'** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheo
ry.Kernel`。
形式化陈述：sum_apply' [Countable ι] (κ : ι -> Kernel α β) (a : α) {s : Set β} (hs : M
easurableSet s) : Kernel.sum κ a s = ∑' n, κ n a s
参数：κ : ι -> Kernel α β；a : α；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.sum_apply`：sum_apply [Countable ι] (κ : ι -> Ke
rnel α β) (a : α) : Kernel.sum κ a = Measure.sum fun n => κ n a
· 使用定理 `MeasureTheory.Measure.sum_apply`：sum_apply (f : ι -> Measure α) {s : Set
 α} (hs : MeasurableSet s) : sum f s = ∑' i, f i s
-/
theorem sum_apply' [Countable ι] (κ : ι → Kernel α β) (a : α) {s : Set β} (hs : MeasurableSet s) :
    Kernel.sum κ a s = ∑' n, κ n a s := by rw [sum_apply κ a, Measure.sum_apply _ hs]

@[simp]
/-
**ProbabilityTheory.Kernel.sum_zero** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory
.Kernel`。
形式化陈述：sum_zero [Countable ι] : (Kernel.sum fun _ : ι => (0 : Kernel α β)) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.sum_apply'`：sum_apply' [Countable ι] (κ : ι -> 
Kernel α β) (a : α) {s : Set β} (hs : MeasurableSet s) : Kernel.sum κ a s = ∑' n
, κ n a s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ProbabilityTheory.Kernel.instIsZeroApplyMeasure`：∀ {α : Type u_1} {β : T
ype u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β},   IsZeroApply (Proba
bilityTheory.Kernel α β) α (MeasureTh…
· 使用定理 `tsum_zero`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [ins
t_1 : TopologicalSpace α] {L : SummationFilter β},   ∑'[L] (x : β), 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sum_zero [Countable ι] : (Kernel.sum fun _ : ι => (0 : Kernel α β)) = 0 := by
  ext a s hs
  rw [sum_apply' _ a hs]
  simp only [zero_apply, Measure.coe_zero, Pi.zero_apply, tsum_zero]
/-
**ProbabilityTheory.Kernel.sum_comm** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory
.Kernel`。
形式化陈述：sum_comm [Countable ι] (κ : ι -> ι -> Kernel α β) : (Kernel.sum fun n => K
ernel.sum (κ n)) = Kernel.sum fun m => Kernel.sum fun n => κ n m
参数：κ : ι -> ι -> Kernel α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.sum_comm`：sum_comm {ι' : Type*} (μ : ι -> ι' -> Me
asure α) : (sum fun n => sum (μ n)) = sum fun m => sum fun n => μ n m
-/
theorem sum_comm [Countable ι] (κ : ι → ι → Kernel α β) :
    (Kernel.sum fun n => Kernel.sum (κ n)) = Kernel.sum fun m => Kernel.sum fun n => κ n m := by
  ext a s; simp_rw [sum_apply]; rw [Measure.sum_comm]

@[simp]
/-
**ProbabilityTheory.Kernel.sum_fintype** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityThe
ory.Kernel`。
形式化陈述：sum_fintype [Fintype ι] (κ : ι -> Kernel α β) : Kernel.sum κ = ∑ i, κ i
参数：κ : ι -> Kernel α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.sum_apply'`：sum_apply' [Countable ι] (κ : ι -> 
Kernel α β) (a : α) {s : Set β} (hs : MeasurableSet s) : Kernel.sum κ a s = ∑' n
, κ n a s
· 使用定理 `tsum_fintype`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [
inst_1 : TopologicalSpace α] {L : SummationFilter β}   [L.LeAtTop] [inst_3 : Fin
ty…
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `ProbabilityTheory.Kernel.finsetSum_apply'`：finsetSum_apply' (I : Finset 
ι) (κ : ι -> Kernel α β) (a : α) (s : Set β) : (∑ i in I, κ i) a s = ∑ i in I, κ
 i a s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sum_fintype [Fintype ι] (κ : ι → Kernel α β) : Kernel.sum κ = ∑ i, κ i := by
  ext a s hs
  simp only [sum_apply' κ a hs, finsetSum_apply' _ κ a s, tsum_fintype]
/-
**ProbabilityTheory.Kernel.sum_add** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory.
Kernel`。
形式化陈述：sum_add [Countable ι] (κ η : ι -> Kernel α β) : (Kernel.sum fun n => κ n +
 η n) = Kernel.sum κ + Kernel.sum η
参数：κ η : ι -> Kernel α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `ProbabilityTheory.Kernel.instIsAddApplyMeasure`：∀ {α : Type u_1} {β : Ty
pe u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β},   IsAddApply (Probabi
lityTheory.Kernel α β) α (MeasureThe…
· 使用定理 `MeasureTheory.Measure.sum_apply`：sum_apply (f : ι -> Measure α) {s : Set
 α} (hs : MeasurableSet s) : sum f s = ∑' i, f i s
· 使用定理 `Summable.tsum_add`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid
 α] [inst_1 : TopologicalSpace α] {f g : β → α}   {L : SummationFilter β} [T2Spa
ce α] […
· 使用定理 `ENNReal.instT2Space`：T2Space ENNReal
· 使用定理 `ENNReal.instContinuousAdd`：ContinuousAdd ENNReal
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `ENNReal.summable`：∀ {α : Type u_1} {f : α → ENNReal}, Summable f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sum_add [Countable ι] (κ η : ι → Kernel α β) :
    (Kernel.sum fun n => κ n + η n) = Kernel.sum κ + Kernel.sum η := by
  ext a s hs
  simp only [add_apply, sum_apply, Measure.sum_apply _ hs, Pi.add_apply,
    Measure.coe_add, ENNReal.summable.tsum_add ENNReal.summable]

end Sum

section SFinite

/-- A kernel is s-finite if it can be written as the sum of countably many finite kernels. -/
/-
**ProbabilityTheory.Kernel._root_.ProbabilityTheory.IsSFiniteKernel** 是 Mathlib 
中的一个类，位于命名空间 `ProbabilityTheory.Kernel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A kernel is s-finite if it can be written as the sum of countably many finite ke
rnels.
-/
class _root_.ProbabilityTheory.IsSFiniteKernel (κ : Kernel α β) : Prop where
  tsum_finite : ∃ κs : ℕ → Kernel α β, (∀ n, IsFiniteKernel (κs n)) ∧ κ = Kernel.sum κs
/-
**ProbabilityTheory.Kernel.** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory.Kernel`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) IsFiniteKernel.isSFiniteKernel [h : IsFiniteKernel κ] :
    IsSFiniteKernel κ :=
  ⟨⟨fun n => if n = 0 then κ else 0, fun n => by
      simp only; split_ifs
      · exact h
      · infer_instance, by
      ext a s hs
      rw [Kernel.sum_apply' _ _ hs]
      have : (fun i => ((ite (i = 0) κ 0) a) s) = fun i => ite (i = 0) (κ a s) 0 := by
        ext1 i; split_ifs <;> rfl
      rw [this, tsum_ite_eq]⟩⟩

/-- A sequence of finite kernels such that `κ = ProbabilityTheory.Kernel.sum (seq κ)`. See
`ProbabilityTheory.Kernel.isFiniteKernel_seq` and `ProbabilityTheory.Kernel.kernel_sum_seq`. -/
/-
**ProbabilityTheory.Kernel.seq** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory.Kern
el`。
形式化陈述：seq (κ : Kernel α β) [h : IsSFiniteKernel κ] : Nat -> Kernel α β
参数：κ : Kernel α β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `ProbabilityTheory.IsSFiniteKernel.tsum_finite`：∀ {α : Type u_1} {β : Typ
e u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheory.
Kernel α β}   [self : ProbabilityTh…

--- 原说明 ---
A sequence of finite kernels such that `κ = ProbabilityTheory.Kernel.sum (seq κ)
`. See
`ProbabilityTheory.Kernel.isFiniteKernel_seq` and `ProbabilityTheory.Kernel.kern
el_sum_seq`.
-/
noncomputable def seq (κ : Kernel α β) [h : IsSFiniteKernel κ] : ℕ → Kernel α β :=
  h.tsum_finite.choose
/-
**ProbabilityTheory.Kernel.kernel_sum_seq** 是 Mathlib 中的一个定理，位于命名空间 `Probability
Theory.Kernel`。
形式化陈述：kernel_sum_seq (κ : Kernel α β) [h : IsSFiniteKernel κ] : Kernel.sum (seq 
κ) = κ
参数：κ : Kernel α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `ProbabilityTheory.IsSFiniteKernel.tsum_finite`：∀ {α : Type u_1} {β : Typ
e u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheory.
Kernel α β}   [self : ProbabilityTh…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem kernel_sum_seq (κ : Kernel α β) [h : IsSFiniteKernel κ] : Kernel.sum (seq κ) = κ :=
  h.tsum_finite.choose_spec.2.symm
/-
**ProbabilityTheory.Kernel.measure_sum_seq** 是 Mathlib 中的一个定理，位于命名空间 `Probabilit
yTheory.Kernel`。
形式化陈述：measure_sum_seq (κ : Kernel α β) [h : IsSFiniteKernel κ] (a : α) : (Measur
e.sum fun n => seq κ n a) = κ a
参数：κ : Kernel α β；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.Kernel.sum_apply`：sum_apply [Countable ι] (κ : ι -> Ke
rnel α β) (a : α) : Kernel.sum κ a = Measure.sum fun n => κ n a
· 使用定理 `ProbabilityTheory.Kernel.kernel_sum_seq`：kernel_sum_seq (κ : Kernel α β)
 [h : IsSFiniteKernel κ] : Kernel.sum (seq κ) = κ
-/
theorem measure_sum_seq (κ : Kernel α β) [h : IsSFiniteKernel κ] (a : α) :
    (Measure.sum fun n => seq κ n a) = κ a := by rw [← Kernel.sum_apply, kernel_sum_seq κ]
/-
**ProbabilityTheory.Kernel.isFiniteKernel_seq** 是 Mathlib 中的一个实例，位于命名空间 `Probabi
lityTheory.Kernel`。
形式化陈述：isFiniteKernel_seq (κ : Kernel α β) [h : IsSFiniteKernel κ] (n : Nat) : Is
FiniteKernel (Kernel.seq κ n)
参数：κ : Kernel α β；n : Nat。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `ProbabilityTheory.IsSFiniteKernel.tsum_finite`：∀ {α : Type u_1} {β : Typ
e u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheory.
Kernel α β}   [self : ProbabilityTh…
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
instance isFiniteKernel_seq (κ : Kernel α β) [h : IsSFiniteKernel κ] (n : ℕ) :
    IsFiniteKernel (Kernel.seq κ n) :=
  h.tsum_finite.choose_spec.1 n
/-
**ProbabilityTheory.Kernel._root_.ProbabilityTheory.IsSFiniteKernel.sFinite** 是 
Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory.Kernel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.ProbabilityTheory.IsSFiniteKernel.sFinite [IsSFiniteKernel κ] (a : α) :
    SFinite (κ a) :=
  ⟨⟨fun n ↦ seq κ n a, inferInstance, (measure_sum_seq κ a).symm⟩⟩
/-
**ProbabilityTheory.Kernel.IsSFiniteKernel.add** 是 Mathlib 中的一个定理，位于命名空间 `Probab
ilityTheory.Kernel.IsSFiniteKernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} (κ η : ProbabilityTheory.Kernel α β)   [ProbabilityTheory.IsSFiniteKerne
l κ] [ProbabilityTheory.IsSFiniteKernel η], ProbabilityTheory.IsSFiniteKernel (κ
 + η)
参数：κ η : ProbabilityTheory.Kernel α β；κ + η。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `ProbabilityTheory.IsFiniteKernel.add`：∀ {α : Type u_1} {β : Type u_2} {m
α : MeasurableSpace α} {mβ : MeasurableSpace β} (κ η : ProbabilityTheory.Kernel 
α β)   [ProbabilityTheory.…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.sum_add`：sum_add [Countable ι] (κ η : ι -> Kern
el α β) : (Kernel.sum fun n => κ n + η n) = Kernel.sum κ + Kernel.sum η
· 使用定理 `ProbabilityTheory.Kernel.kernel_sum_seq`：kernel_sum_seq (κ : Kernel α β)
 [h : IsSFiniteKernel κ] : Kernel.sum (seq κ) = κ
-/
instance IsSFiniteKernel.add (κ η : Kernel α β) [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    IsSFiniteKernel (κ + η) := by
  refine ⟨⟨fun n => seq κ n + seq η n, fun n => inferInstance, ?_⟩⟩
  rw [sum_add, kernel_sum_seq κ, kernel_sum_seq η]
/-
**ProbabilityTheory.Kernel.IsSFiniteKernel.finsetSum** 是 Mathlib 中的一个定理，位于命名空间 `
ProbabilityTheory.Kernel.IsSFiniteKernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {m
β : MeasurableSpace β}   {κs : ι → ProbabilityTheory.Kernel α β} (I : Finset ι),
   (∀ i ∈ I, ProbabilityTheory.IsSFiniteKernel (κs i)) → ProbabilityTheory.IsSFi
niteKernel (∑ i ∈ I, κs i)
参数：I : Finset ι；∀ i ∈ I, ProbabilityTheory.IsSFiniteKernel (κs i)；∑ i ∈ I, κs i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_empty`：∀ {ι : Type u_1} {M : Type u_3} {f : ι → M} [inst : Ad
dCommMonoid M], ∑ x ∈ ∅, f x = 0
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.add`：∀ {α : Type u_1} {β : Type
 u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (κ η : ProbabilityTheory
.Kernel α β)   [ProbabilityTheory.…
-/
theorem IsSFiniteKernel.finsetSum {κs : ι → Kernel α β} (I : Finset ι)
    (h : ∀ i ∈ I, IsSFiniteKernel (κs i)) : IsSFiniteKernel (∑ i ∈ I, κs i) := by
  classical
  induction I using Finset.induction with
  | empty => rw [Finset.sum_empty]; infer_instance
  | insert i I hi_notMem_I h_ind =>
    rw [Finset.sum_insert hi_notMem_I]
    have : IsSFiniteKernel (κs i) := h i (Finset.mem_insert_self _ _)
    have : IsSFiniteKernel (∑ x ∈ I, κs x) :=
      h_ind fun i hiI => h i (Finset.mem_insert_of_mem hiI)
    exact IsSFiniteKernel.add _ _

@[deprecated (since := "2026-04-08")] alias IsSFiniteKernel.finset_sum := IsSFiniteKernel.finsetSum
/-
**ProbabilityTheory.Kernel.isSFiniteKernel_sum_of_denumerable** 是 Mathlib 中的一个定理
，位于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：isSFiniteKernel_sum_of_denumerable [Denumerable ι] {κs : ι -> Kernel α β} 
(hκs : forall n, IsSFiniteKernel (κs n)) : IsSFiniteKernel (Kernel.sum κs)
参数：hκs : forall n, IsSFiniteKernel (κs n)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Encodable.countable`：∀ {α : Type u_1} [Encodable α], Countable α
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.sum.congr_simp`：∀ {α : Type u_1} {β : Type u_2}
 {ι : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} [inst : Counta
ble ι]   (κ κ_1 : ι → Probabi…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ProbabilityTheory.Kernel.kernel_sum_seq`：kernel_sum_seq (κ : Kernel α β)
 [h : IsSFiniteKernel κ] : Kernel.sum (seq κ) = κ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ProbabilityTheory.Kernel.sum_apply'`：sum_apply' [Countable ι] (κ : ι -> 
Kernel α β) (a : α) {s : Set β} (hs : MeasurableSet s) : Kernel.sum κ a s = ∑' n
, κ n a s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : Ad
dCommMonoid α] [inst_1 : TopologicalSpace α] (e : γ ≃ β)   (f : β → α), ∑' (c : 
γ),…
· 使用定理 `Summable.tsum_prod'`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [ins
t : AddCommMonoid α] [inst_1 : TopologicalSpace α] [ContinuousAdd α]   [T3Space 
α] {f : β…
· 使用定理 `ENNReal.instContinuousAdd`：ContinuousAdd ENNReal
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `ENNReal.instT4Space`：T4Space ENNReal
· 使用定理 `ENNReal.summable`：∀ {α : Type u_1} {f : α → ENNReal}, Summable f
-/
theorem isSFiniteKernel_sum_of_denumerable [Denumerable ι] {κs : ι → Kernel α β}
    (hκs : ∀ n, IsSFiniteKernel (κs n)) : IsSFiniteKernel (Kernel.sum κs) := by
  let e : ℕ ≃ ι × ℕ := (Denumerable.eqv (ι × ℕ)).symm
  refine ⟨⟨fun n => seq (κs (e n).1) (e n).2, inferInstance, ?_⟩⟩
  have hκ_eq : Kernel.sum κs = Kernel.sum fun n => Kernel.sum (seq (κs n)) := by
    simp_rw [kernel_sum_seq]
  ext a s hs
  rw [hκ_eq]
  simp_rw [Kernel.sum_apply' _ _ hs]
  change (∑' i, ∑' m, seq (κs i) m a s) = ∑' n, (fun im : ι × ℕ => seq (κs im.fst) im.snd a s) (e n)
  rw [e.tsum_eq (fun im : ι × ℕ => seq (κs im.fst) im.snd a s),
    ENNReal.summable.tsum_prod' fun _ => ENNReal.summable]
/-
**ProbabilityTheory.Kernel.isSFiniteKernel_sum** 是 Mathlib 中的一个实例，位于命名空间 `Probab
ilityTheory.Kernel`。
形式化陈述：isSFiniteKernel_sum [Countable ι] {κs : ι -> Kernel α β} [hκs : forall n, 
IsSFiniteKernel (κs n)] : IsSFiniteKernel (Kernel.sum κs)
参数：κs n。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `ProbabilityTheory.Kernel.sum_fintype`：sum_fintype [Fintype ι] (κ : ι -> 
Kernel α β) : Kernel.sum κ = ∑ i, κ i
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.finsetSum`：∀ {α : Type u_1} {β 
: Type u_2} {ι : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {
κs : ι → ProbabilityTheory.Kernel α β} (…
· 使用定理 `nonempty_denumerable`：nonempty_denumerable (α : Type*) [Countable α] [In
finite α] : Nonempty (Denumerable α)
· 使用定理 `ProbabilityTheory.Kernel.isSFiniteKernel_sum_of_denumerable`：isSFiniteKe
rnel_sum_of_denumerable [Denumerable ι] {κs : ι -> Kernel α β} (hκs : forall n, 
IsSFiniteKernel (κs n)) : IsSFiniteKernel (Kernel…
-/
instance isSFiniteKernel_sum [Countable ι] {κs : ι → Kernel α β}
    [hκs : ∀ n, IsSFiniteKernel (κs n)] : IsSFiniteKernel (Kernel.sum κs) := by
  cases fintypeOrInfinite ι
  · rw [sum_fintype]
    exact IsSFiniteKernel.finsetSum Finset.univ fun i _ => hκs i
  cases nonempty_denumerable ι
  exact isSFiniteKernel_sum_of_denumerable hκs

end SFinite
end Kernel
end ProbabilityTheory

