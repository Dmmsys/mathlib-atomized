/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Patrick Massot, Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Topology
import Mathlib.Algebra.Order.Interval.Set.Group

/-!
# Integral over an interval

In this file we define `∫ x in a..b, f x ∂μ` to be `∫ x in Ioc a b, f x ∂μ` if `a ≤ b` and
`-∫ x in Ioc b a, f x ∂μ` if `b ≤ a`.

## Implementation notes

### Avoiding `if`, `min`, and `max`

In order to avoid `if`s in the definition, we define `IntervalIntegrable f μ a b` as
`IntegrableOn f (Ioc a b) μ ∧ IntegrableOn f (Ioc b a) μ`. For any `a`, `b` one of these
intervals is empty and the other coincides with `Set.uIoc a b = Set.Ioc (min a b) (max a b)`.

Similarly, we define `∫ x in a..b, f x ∂μ` to be `∫ x in Ioc a b, f x ∂μ - ∫ x in Ioc b a, f x ∂μ`.
Again, for any `a`, `b` one of these integrals is zero, and the other gives the expected result.

This way some properties can be translated from integrals over sets without dealing with
the cases `a ≤ b` and `b ≤ a` separately.

### Choice of the interval

We use integral over `Set.uIoc a b = Set.Ioc (min a b) (max a b)` instead of one of the other
three possible intervals with the same endpoints for two reasons:

* this way `∫ x in a..b, f x ∂μ + ∫ x in b..c, f x ∂μ = ∫ x in a..c, f x ∂μ` holds whenever
  `f` is integrable on each interval; in particular, it works even if the measure `μ` has an atom
  at `b`; this rules out `Set.Ioo` and `Set.Icc` intervals;
* with this definition for a probability measure `μ`, the integral `∫ x in a..b, 1 ∂μ` equals
  the difference $F_μ(b)-F_μ(a)$, where $F_μ(a)=μ(-∞, a]$ is the
  [cumulative distribution function](https://en.wikipedia.org/wiki/Cumulative_distribution_function)
  of `μ`.

## Tags

integral
-/

@[expose] public section


noncomputable section

open MeasureTheory Set Filter Function TopologicalSpace

open scoped Topology Filter ENNReal Interval NNReal

variable {ι 𝕜 ε ε' E F A : Type*} [NormedAddCommGroup E]
  [TopologicalSpace ε] [ENormedAddMonoid ε] [TopologicalSpace ε'] [ENormedAddMonoid ε']

/-!
### Integrability on an interval
-/


/-- A function `f` is called *interval integrable* with respect to a measure `μ` on an unordered
interval `a..b` if it is integrable on both intervals `(a, b]` and `(b, a]`. One of these
intervals is always empty, so this property is equivalent to `f` being integrable on
`(min a b, max a b]`. -/
/-
**IntervalIntegrable** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IntervalIntegrable (f : Real -> ε) (μ : Measure Real) (a b : Real) : Prop
参数：f : Real -> ε；μ : Measure Real；a b : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f` is called *interval integrable* with respect to a measure `μ` on 
an unordered
interval `a..b` if it is integrable on both intervals `(a, b]` and `(b, a]`. One
 of these
intervals is always empty, so this property is equivalent to `f` being integrabl
e on
`(min a b, max a b]`.
-/
def IntervalIntegrable (f : ℝ → ε) (μ : Measure ℝ) (a b : ℝ) : Prop :=
  IntegrableOn f (Ioc a b) μ ∧ IntegrableOn f (Ioc b a) μ

/-!
## Basic iff's for `IntervalIntegrable`
-/
section

variable [PseudoMetrizableSpace ε] {f : ℝ → ε} {a b : ℝ} {μ : Measure ℝ}

/-- A function is interval integrable with respect to a given measure `μ` on `a..b` if and
  only if it is integrable on `uIoc a b` with respect to `μ`. This is an equivalent
  definition of `IntervalIntegrable`. -/
/-
**intervalIntegrable_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：intervalIntegrable_iff : IntervalIntegrable f μ a b ↔ IntegrableOn f (Ι a 
b) μ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.uIoc_eq_union`：uIoc_eq_union : Ι a b = Ioc a b union Ioc b a
· 使用定理 `MeasureTheory.integrableOn_union`：integrableOn_union [PseudoMetrizableSp
ace ε] : IntegrableOn f (s union t) μ ↔ IntegrableOn f s μ ∧ IntegrableOn f t μ
· 使用定理 `IntervalIntegrable.eq_1`：∀ {ε : Type u_3} [inst : TopologicalSpace ε] [i
nst_1 : ENormedAddMonoid ε] (f : ℝ → ε) (μ : MeasureTheory.Measure ℝ)   (a b : ℝ
),   Interval…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A function is interval integrable with respect to a given measure `μ` on `a..b` 
if and
  only if it is integrable on `uIoc a b` with respect to `μ`. This is an equival
ent
  definition of `IntervalIntegrable`.
-/
theorem intervalIntegrable_iff : IntervalIntegrable f μ a b ↔ IntegrableOn f (Ι a b) μ := by
  rw [uIoc_eq_union, integrableOn_union, IntervalIntegrable]

/-- If a function is interval integrable with respect to a given measure `μ` on `a..b` then
  it is integrable on `uIoc a b` with respect to `μ`. -/
/-
**IntervalIntegrable.def'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IntervalIntegrable.def' (h : IntervalIntegrable f μ a b) : IntegrableOn f 
(Ι a b) μ
参数：h : IntervalIntegrable f μ a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `intervalIntegrable_iff`：intervalIntegrable_iff : IntervalIntegrable f μ 
a b ↔ IntegrableOn f (Ι a b) μ

--- 原说明 ---
If a function is interval integrable with respect to a given measure `μ` on `a..
b` then
  it is integrable on `uIoc a b` with respect to `μ`.
-/
theorem IntervalIntegrable.def' (h : IntervalIntegrable f μ a b) : IntegrableOn f (Ι a b) μ :=
  intervalIntegrable_iff.mp h
/-
**intervalIntegrable_congr_ae** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：intervalIntegrable_congr_ae {g : Real -> ε} (h : f =ᵐ[μ.restrict (Ι a b)] 
g) : IntervalIntegrable f μ a b ↔ IntervalIntegrable g μ a b
参数：h : f =ᵐ[μ.restrict (Ι a b)] g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intervalIntegrable_iff`：intervalIntegrable_iff : IntervalIntegrable f μ 
a b ↔ IntegrableOn f (Ι a b) μ
· 使用定理 `MeasureTheory.integrableOn_congr_fun_ae`：integrableOn_congr_fun_ae (hst 
: f =ᵐ[μ.restrict s] g) : IntegrableOn f s μ ↔ IntegrableOn g s μ
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem intervalIntegrable_congr_ae {g : ℝ → ε} (h : f =ᵐ[μ.restrict (Ι a b)] g) :
    IntervalIntegrable f μ a b ↔ IntervalIntegrable g μ a b := by
  rw [intervalIntegrable_iff, integrableOn_congr_fun_ae h, intervalIntegrable_iff]
/-
**intervalIntegrable_congr_uIoo** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：intervalIntegrable_congr_uIoo [NullSingletonClass μ] {g : Real -> ε} (h : 
EqOn f g (uIoo a b)) : IntervalIntegrable f μ a b ↔ IntervalIntegrable g μ a b
参数：h : EqOn f g (uIoo a b)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `intervalIntegrable_congr_ae`：intervalIntegrable_congr_ae {g : Real -> ε}
 (h : f =ᵐ[μ.restrict (Ι a b)] g) : IntervalIntegrable f μ a b ↔ IntervalIntegra
ble g μ a b
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.uIoc.eq_1`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), Set.uI
oc a b = Set.Ioc (min a b) (max a b)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.restrict_Ioo_eq_restrict_Ioc`：restrict_Ioo_eq_restrict_Ioc
 : μ.restrict (Ioo a b) = μ.restrict (Ioc a b)
· 使用定理 `MeasureTheory.ae_restrict_of_forall_mem`：ae_restrict_of_forall_mem {μ : 
Measure α} {s : Set α} (hs : MeasurableSet s) {p : α -> Prop} (h : forall x in s
, p x) : forallᵐ (x : α) ∂μ.r…
· 使用定理 `measurableSet_Ioo`：measurableSet_Ioo [OrderClosedTopology α] : Measurabl
eSet (Ioo a b)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
-/
theorem intervalIntegrable_congr_uIoo [NullSingletonClass μ] {g : ℝ → ε} (h : EqOn f g (uIoo a b)) :
    IntervalIntegrable f μ a b ↔ IntervalIntegrable g μ a b := by
  apply intervalIntegrable_congr_ae
  rw [uIoc, ← restrict_Ioo_eq_restrict_Ioc]
  apply ae_restrict_of_forall_mem measurableSet_Ioo h
/-
**IntervalIntegrable.congr_ae** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IntervalIntegrable.congr_ae {g : Real -> ε} (hf : IntervalIntegrable f μ a
 b) (h : f =ᵐ[μ.restrict (Ι a b)] g) : IntervalIntegrable g μ a b
参数：hf : IntervalIntegrable f μ a b；h : f =ᵐ[μ.restrict (Ι a b)] g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `intervalIntegrable_congr_ae`：intervalIntegrable_congr_ae {g : Real -> ε}
 (h : f =ᵐ[μ.restrict (Ι a b)] g) : IntervalIntegrable f μ a b ↔ IntervalIntegra
ble g μ a b
-/
theorem IntervalIntegrable.congr_ae {g : ℝ → ε} (hf : IntervalIntegrable f μ a b)
    (h : f =ᵐ[μ.restrict (Ι a b)] g) :
    IntervalIntegrable g μ a b := by
  rwa [← intervalIntegrable_congr_ae h]
/-
**IntervalIntegrable.congr_uIoo** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IntervalIntegrable.congr_uIoo [NullSingletonClass μ] {g : Real -> ε} (hf :
 IntervalIntegrable f μ a b) (h : EqOn f g (uIoo a b)) : IntervalIntegrable g μ 
a b
参数：hf : IntervalIntegrable f μ a b；h : EqOn f g (uIoo a b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `intervalIntegrable_congr_uIoo`：intervalIntegrable_congr_uIoo [NullSingle
tonClass μ] {g : Real -> ε} (h : EqOn f g (uIoo a b)) : IntervalIntegrable f μ a
 b ↔ IntervalIntegr…
-/
theorem IntervalIntegrable.congr_uIoo [NullSingletonClass μ] {g : ℝ → ε}
    (hf : IntervalIntegrable f μ a b) (h : EqOn f g (uIoo a b)) : IntervalIntegrable g μ a b :=
  intervalIntegrable_congr_uIoo h |>.mp hf
/-
**intervalIntegrable_congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：intervalIntegrable_congr {g : Real -> ε} (h : EqOn f g (Ι a b)) : Interval
Integrable f μ a b ↔ IntervalIntegrable g μ a b
参数：h : EqOn f g (Ι a b)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `intervalIntegrable_congr_ae`：intervalIntegrable_congr_ae {g : Real -> ε}
 (h : f =ᵐ[μ.restrict (Ι a b)] g) : IntervalIntegrable f μ a b ↔ IntervalIntegra
ble g μ a b
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_restrict_mem`：ae_restrict_mem (hs : MeasurableSet s) : 
forallᵐ x ∂μ.restrict s, x in s
· 使用定理 `measurableSet_uIoc`：measurableSet_uIoc [ClosedIicTopology α] : Measurabl
eSet (uIoc a b)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
-/
theorem intervalIntegrable_congr {g : ℝ → ε} (h : EqOn f g (Ι a b)) :
    IntervalIntegrable f μ a b ↔ IntervalIntegrable g μ a b :=
  intervalIntegrable_congr_ae <| (ae_restrict_mem measurableSet_uIoc).mono h

alias ⟨IntervalIntegrable.congr, _⟩ := intervalIntegrable_congr

/-- Interval integrability is invariant when functions change along discrete sets. -/
/-
**IntervalIntegrable.congr_codiscreteWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IntervalIntegrable.congr_codiscreteWithin {g : Real -> ε} [NullSingletonCl
ass μ] (h : f =ᶠ[codiscreteWithin (Ι a b)] g) (hf : IntervalIntegrable f μ a b) 
: IntervalIntegrable g μ a b
参数：h : f =ᶠ[codiscreteWithin (Ι a b)] g；hf : IntervalIntegrable f μ a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntervalIntegrable.congr_ae`：IntervalIntegrable.congr_ae {g : Real -> ε}
 (hf : IntervalIntegrable f μ a b) (h : f =ᵐ[μ.restrict (Ι a b)] g) : IntervalIn
tegrable g μ a b
· 使用定理 `ae_restrict_le_codiscreteWithin`：ae_restrict_le_codiscreteWithin {α : Ty
pe*} [MeasurableSpace α] [TopologicalSpace α] [SecondCountableTopology α] {μ : M
easure α} [NullSingle…
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `measurableSet_Ioc`：measurableSet_Ioc [ClosedIicTopology α] : MeasurableS
et (Ioc a b)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ

--- 原说明 ---
Interval integrability is invariant when functions change along discrete sets.
-/
theorem IntervalIntegrable.congr_codiscreteWithin {g : ℝ → ε} [NullSingletonClass μ]
    (h : f =ᶠ[codiscreteWithin (Ι a b)] g) (hf : IntervalIntegrable f μ a b) :
    IntervalIntegrable g μ a b :=
  hf.congr_ae (ae_restrict_le_codiscreteWithin measurableSet_Ioc h)

/-- Interval integrability is invariant when functions change along discrete sets. -/
/-
**intervalIntegrable_congr_codiscreteWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：intervalIntegrable_congr_codiscreteWithin {g : Real -> ε} [NullSingletonCl
ass μ] (h : f =ᶠ[codiscreteWithin (Ι a b)] g) : IntervalIntegrable f μ a b ↔ Int
ervalIntegrable g μ a b
参数：h : f =ᶠ[codiscreteWithin (Ι a b)] g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntervalIntegrable.congr_codiscreteWithin`：IntervalIntegrable.congr_codi
screteWithin {g : Real -> ε} [NullSingletonClass μ] (h : f =ᶠ[codiscreteWithin (
Ι a b)] g) (hf : IntervalIntegr…
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f

--- 原说明 ---
Interval integrability is invariant when functions change along discrete sets.
-/
theorem intervalIntegrable_congr_codiscreteWithin {g : ℝ → ε} [NullSingletonClass μ]
    (h : f =ᶠ[codiscreteWithin (Ι a b)] g) :
    IntervalIntegrable f μ a b ↔ IntervalIntegrable g μ a b :=
  ⟨(IntervalIntegrable.congr_codiscreteWithin h ·),
    (IntervalIntegrable.congr_codiscreteWithin h.symm ·)⟩
/-
**intervalIntegrable_iff_integrableOn_Ioc_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：intervalIntegrable_iff_integrableOn_Ioc_of_le (hab : a <= b) : IntervalInt
egrable f μ a b ↔ IntegrableOn f (Ioc a b) μ
参数：hab : a <= b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intervalIntegrable_iff`：intervalIntegrable_iff : IntervalIntegrable f μ 
a b ↔ IntegrableOn f (Ι a b) μ
· 使用定理 `Set.uIoc_of_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b
 → Set.uIoc a b = Set.Ioc a b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem intervalIntegrable_iff_integrableOn_Ioc_of_le (hab : a ≤ b) :
    IntervalIntegrable f μ a b ↔ IntegrableOn f (Ioc a b) μ := by
  rw [intervalIntegrable_iff, uIoc_of_le hab]
/-
**intervalIntegrable_iff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：intervalIntegrable_iff' [NullSingletonClass μ] (h : ‖f (min a b)‖ₑ != ∞
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intervalIntegrable_iff`：intervalIntegrable_iff : IntervalIntegrable f μ 
a b ↔ IntegrableOn f (Ι a b) μ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Icc_min_max`：Icc_min_max : Icc (min a b) (max a b) = [[a, b]]
· 使用定理 `Set.uIoc.eq_1`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), Set.uI
oc a b = Set.Ioc (min a b) (max a b)
· 使用定理 `integrableOn_Icc_iff_integrableOn_Ioc`：integrableOn_Icc_iff_integrableOn
_Ioc (ha : ‖f a‖ₑ != ∞
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `standardBorel_of_polish`：∀ {α : Type u_1} [inst : MeasurableSpace α] [τ 
: TopologicalSpace α] [BorelSpace α] [PolishSpace α],   StandardBorelSpace α
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem intervalIntegrable_iff' [NullSingletonClass μ] (h : ‖f (min a b)‖ₑ ≠ ∞ := by finiteness) :
    IntervalIntegrable f μ a b ↔ IntegrableOn f (uIcc a b) μ := by
  rw [intervalIntegrable_iff, ← Icc_min_max, uIoc, integrableOn_Icc_iff_integrableOn_Ioc h]
/-
**intervalIntegrable_iff_integrableOn_Icc_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：intervalIntegrable_iff_integrableOn_Icc_of_le [NullSingletonClass μ] (hab 
: a <= b) (ha : ‖f a‖ₑ != ∞
参数：hab : a <= b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intervalIntegrable_iff_integrableOn_Ioc_of_le`：intervalIntegrable_iff_in
tegrableOn_Ioc_of_le (hab : a <= b) : IntervalIntegrable f μ a b ↔ IntegrableOn 
f (Ioc a b) μ
· 使用定理 `integrableOn_Icc_iff_integrableOn_Ioc`：integrableOn_Icc_iff_integrableOn
_Ioc (ha : ‖f a‖ₑ != ∞
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `standardBorel_of_polish`：∀ {α : Type u_1} [inst : MeasurableSpace α] [τ 
: TopologicalSpace α] [BorelSpace α] [PolishSpace α],   StandardBorelSpace α
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem intervalIntegrable_iff_integrableOn_Icc_of_le [NullSingletonClass μ]
    (hab : a ≤ b) (ha : ‖f a‖ₑ ≠ ∞ := by finiteness) :
    IntervalIntegrable f μ a b ↔ IntegrableOn f (Icc a b) μ := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab, integrableOn_Icc_iff_integrableOn_Ioc ha]
/-
**intervalIntegrable_iff_integrableOn_Ico_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：intervalIntegrable_iff_integrableOn_Ico_of_le [NullSingletonClass μ] (hab 
: a <= b) (ha : ‖f a‖ₑ != ∞
参数：hab : a <= b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intervalIntegrable_iff_integrableOn_Icc_of_le`：intervalIntegrable_iff_in
tegrableOn_Icc_of_le [NullSingletonClass μ] (hab : a <= b) (ha : ‖f a‖ₑ != ∞
· 使用定理 `integrableOn_Icc_iff_integrableOn_Ico`：integrableOn_Icc_iff_integrableOn
_Ico (hb : ‖f b‖ₑ != ∞
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `standardBorel_of_polish`：∀ {α : Type u_1} [inst : MeasurableSpace α] [τ 
: TopologicalSpace α] [BorelSpace α] [PolishSpace α],   StandardBorelSpace α
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem intervalIntegrable_iff_integrableOn_Ico_of_le [NullSingletonClass μ]
    (hab : a ≤ b) (ha : ‖f a‖ₑ ≠ ∞ := by finiteness) (hb : ‖f b‖ₑ ≠ ∞ := by finiteness) :
    IntervalIntegrable f μ a b ↔ IntegrableOn f (Ico a b) μ := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab ha,
    integrableOn_Icc_iff_integrableOn_Ico hb]
/-
**intervalIntegrable_iff_integrableOn_Ioo_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：intervalIntegrable_iff_integrableOn_Ioo_of_le [NullSingletonClass μ] (hab 
: a <= b) (ha : ‖f a‖ₑ != ∞
参数：hab : a <= b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intervalIntegrable_iff_integrableOn_Icc_of_le`：intervalIntegrable_iff_in
tegrableOn_Icc_of_le [NullSingletonClass μ] (hab : a <= b) (ha : ‖f a‖ₑ != ∞
· 使用定理 `integrableOn_Icc_iff_integrableOn_Ioo`：integrableOn_Icc_iff_integrableOn
_Ioo (ha : ‖f a‖ₑ != ∞
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `standardBorel_of_polish`：∀ {α : Type u_1} [inst : MeasurableSpace α] [τ 
: TopologicalSpace α] [BorelSpace α] [PolishSpace α],   StandardBorelSpace α
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem intervalIntegrable_iff_integrableOn_Ioo_of_le [NullSingletonClass μ]
    (hab : a ≤ b) (ha : ‖f a‖ₑ ≠ ∞ := by finiteness) (hb : ‖f b‖ₑ ≠ ∞ := by finiteness) :
    IntervalIntegrable f μ a b ↔ IntegrableOn f (Ioo a b) μ := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab ha,
    integrableOn_Icc_iff_integrableOn_Ioo ha hb]

omit [PseudoMetrizableSpace ε] in
/-- If a function is integrable with respect to a given measure `μ` then it is interval integrable
  with respect to `μ` on `uIcc a b`. -/
/-
**MeasureTheory.Integrable.intervalIntegrable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeasureTheory.Integrable.intervalIntegrable (hf : Integrable f μ) : Interv
alIntegrable f μ a b
参数：hf : Integrable f μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.integrableOn`：∀ {α : Type u_1} {ε : Type u_3} {
mα : MeasurableSpace α} {f : α → ε} {s : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace ε]…

--- 原说明 ---
If a function is integrable with respect to a given measure `μ` then it is inter
val integrable
  with respect to `μ` on `uIcc a b`.
-/
theorem MeasureTheory.Integrable.intervalIntegrable (hf : Integrable f μ) :
    IntervalIntegrable f μ a b :=
  ⟨hf.integrableOn, hf.integrableOn⟩

omit [PseudoMetrizableSpace ε] in
/-
**MeasureTheory.IntegrableOn.intervalIntegrable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeasureTheory.IntegrableOn.intervalIntegrable (hf : IntegrableOn f [[a, b]
] μ) : IntervalIntegrable f μ a b
参数：hf : IntegrableOn f [[a, b]] μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IntegrableOn.mono_set`：∀ {α : Type u_1} {ε : Type u_3} {mα
 : MeasurableSpace α} {f : α → ε} {s t : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace …
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.Ioc_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc a b ⊆ Set.Icc a b
· 使用引理 `Set.Icc_subset_uIcc`：Icc_subset_uIcc : Icc a b subseteq [[a, b]]
· 使用引理 `Set.Icc_subset_uIcc'`：Icc_subset_uIcc' : Icc b a subseteq [[a, b]]
-/
theorem MeasureTheory.IntegrableOn.intervalIntegrable (hf : IntegrableOn f [[a, b]] μ) :
    IntervalIntegrable f μ a b :=
  ⟨hf.mono_set (Ioc_subset_Icc_self.trans Icc_subset_uIcc),
    hf.mono_set (Ioc_subset_Icc_self.trans Icc_subset_uIcc')⟩
/-
**intervalIntegrable_const_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：intervalIntegrable_const_iff {c : ε} (hc : ‖c‖ₑ != ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integrableOn_const_iff`：integrableOn_const_iff {C : ε'} (h
C : ‖C‖ₑ != ∞
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem intervalIntegrable_const_iff {c : ε} (hc : ‖c‖ₑ ≠ ⊤ := by finiteness) :
    IntervalIntegrable (fun _ => c) μ a b ↔ c = 0 ∨ μ (Ι a b) < ∞ := by
  simp [intervalIntegrable_iff, integrableOn_const_iff hc]

@[simp]
/-
**intervalIntegrable_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：intervalIntegrable_const [IsLocallyFiniteMeasure μ] {c : E} : IntervalInte
grable (fun _ => c) μ a b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `intervalIntegrable_const_iff`：intervalIntegrable_const_iff {c : ε} (hc :
 ‖c‖ₑ != ⊤
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `measure_Ioc_lt_top`：measure_Ioc_lt_top : μ (Ioc a b) < ∞
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
-/
theorem intervalIntegrable_const [IsLocallyFiniteMeasure μ] {c : E} :
    IntervalIntegrable (fun _ => c) μ a b :=
  intervalIntegrable_const_iff (by simp) |>.2 <| Or.inr measure_Ioc_lt_top
/-
**IntervalIntegrable.zero** 是 Mathlib 中的一个定理，位于命名空间 `IntervalIntegrable`。
形式化陈述：∀ {E : Type u_5} [inst : NormedAddCommGroup E] {a b : ℝ} {μ : MeasureTheor
y.Measure ℝ}, IntervalIntegrable 0 μ a b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `intervalIntegrable_const_iff`：intervalIntegrable_const_iff {c : ε} (hc :
 ‖c‖ₑ != ⊤
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用引理 `enorm_ne_top`：enorm_ne_top : ‖x‖ₑ != ∞
-/
protected theorem IntervalIntegrable.zero : IntervalIntegrable (0 : ℝ → E) μ a b :=
  (intervalIntegrable_const_iff <| by finiteness).mpr <| .inl rfl

end

/-!
## Basic properties of interval integrability
- interval integrability is symmetric, reflexive, transitive
- monotonicity and strong measurability of the interval integral
- if `f` is interval integrable, so are its absolute value and norm
- arithmetic properties
-/
namespace IntervalIntegrable

section

variable {f : ℝ → ε} {a b c d : ℝ} {μ ν : Measure ℝ}

@[symm]
nonrec theorem symm (h : IntervalIntegrable f μ a b) : IntervalIntegrable f μ b a :=
  h.symm

/-
**IntervalIntegrable.symm_iff** 是 Mathlib 中的一个定理，位于命名空间 `IntervalIntegrable`。
形式化陈述：symm_iff : IntervalIntegrable f μ a b ↔ IntervalIntegrable f μ b a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntervalIntegrable.symm`：∀ {ε : Type u_3} [inst : TopologicalSpace ε] [i
nst_1 : ENormedAddMonoid ε] {f : ℝ → ε} {a b : ℝ}   {μ : MeasureTheory.Measure ℝ
}, IntervalIn…
-/
theorem symm_iff : IntervalIntegrable f μ a b ↔ IntervalIntegrable f μ b a := ⟨.symm, .symm⟩

@[refl, simp]
/-
**IntervalIntegrable.refl** 是 Mathlib 中的一个定理，位于命名空间 `IntervalIntegrable`。
形式化陈述：refl : IntervalIntegrable f μ a a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Ioc_eq_empty`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, ¬b < a
 → Set.Ioc b a = ∅
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem refl : IntervalIntegrable f μ a a := by constructor <;> simp

variable [PseudoMetrizableSpace ε]

@[trans]
/-
**IntervalIntegrable.trans** 是 Mathlib 中的一个定理，位于命名空间 `IntervalIntegrable`。
形式化陈述：trans {a b c : Real} (hab : IntervalIntegrable f μ a b) (hbc : IntervalInt
egrable f μ b c) : IntervalIntegrable f μ a c
参数：hab : IntervalIntegrable f μ a b；hbc : IntervalIntegrable f μ b c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IntegrableOn.mono_set`：∀ {α : Type u_1} {ε : Type u_3} {mα
 : MeasurableSpace α} {f : α → ε} {s t : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace …
· 使用定理 `MeasureTheory.IntegrableOn.union`：∀ {α : Type u_1} {ε : Type u_3} {mα : 
MeasurableSpace α} {f : α → ε} {s t : Set α} {μ : MeasureTheory.Measure α}   [in
st : TopologicalSpace …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.Ioc_subset_Ioc_union_Ioc`：Ioc_subset_Ioc_union_Ioc : Ioc a c subsete
q Ioc a b union Ioc b c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem trans {a b c : ℝ} (hab : IntervalIntegrable f μ a b) (hbc : IntervalIntegrable f μ b c) :
    IntervalIntegrable f μ a c :=
  ⟨(hab.1.union hbc.1).mono_set Ioc_subset_Ioc_union_Ioc,
    (hbc.2.union hab.2).mono_set Ioc_subset_Ioc_union_Ioc⟩
/-
**IntervalIntegrable.trans_iff** 是 Mathlib 中的一个定理，位于命名空间 `IntervalIntegrable`。
形式化陈述：trans_iff (h : b in [[a, c]]) : IntervalIntegrable f μ a c ↔ IntervalInteg
rable f μ a b ∧ IntervalIntegrable f μ b c
参数：h : b in [[a, c]]。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Set.uIoc_union_uIoc`：uIoc_union_uIoc (h : b in [[a, c]]) : Ι a b union Ι
 b c = Ι a c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem trans_iff (h : b ∈ [[a, c]]) :
    IntervalIntegrable f μ a c ↔ IntervalIntegrable f μ a b ∧ IntervalIntegrable f μ b c := by
  simp only [intervalIntegrable_iff, ← integrableOn_union, uIoc_union_uIoc h]
/-
**IntervalIntegrable.trans_iterate_Ico** 是 Mathlib 中的一个定理，位于命名空间 `IntervalIntegr
able`。
形式化陈述：trans_iterate_Ico {a : Nat -> Real} {m n : Nat} (hmn : m <= n) (hint : for
all k in Ico m n, IntervalIntegrable f μ (a k) (a <| k + 1)) : IntervalIntegrabl
e f μ (a m) (a n)
参数：hmn : m <= n；hint : forall k in Ico m n, IntervalIntegrable f μ (a k) (a <| k
 + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.le_induction`：le_induction {m : Nat} {P : forall n, m <= n -> Prop} 
(base : P m m.le_refl) (succ : forall n hmn, P n hmn -> P (n + 1) (le_succ_of_le
 hmn))…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Ico_eq_empty`：Ico_eq_empty (h : ¬a < b) : Ico a b = ∅
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `IntervalIntegrable.trans`：trans {a b c : Real} (hab : IntervalIntegrable
 f μ a b) (hbc : IntervalIntegrable f μ b c) : IntervalIntegrable f μ a c
· 使用定理 `Set.Ico_subset_Ico_right`：∀ {α : Type u_1} [inst : Preorder α] {a₁ a₂ b 
: α}, a₂ ≤ a₁ → Set.Ico b a₂ ⊆ Set.Ico b a₁
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem trans_iterate_Ico {a : ℕ → ℝ} {m n : ℕ} (hmn : m ≤ n)
    (hint : ∀ k ∈ Ico m n, IntervalIntegrable f μ (a k) (a <| k + 1)) :
    IntervalIntegrable f μ (a m) (a n) := by
  revert hint
  refine Nat.le_induction ?_ ?_ n hmn
  · simp
  · intro p hp IH h
    exact (IH fun k hk => h k (Ico_subset_Ico_right p.le_succ hk)).trans (h p (by simp [hp]))
/-
**IntervalIntegrable.trans_iterate** 是 Mathlib 中的一个定理，位于命名空间 `IntervalIntegrable
`。
形式化陈述：trans_iterate {a : Nat -> Real} {n : Nat} (hint : forall k < n, IntervalIn
tegrable f μ (a k) (a <| k + 1)) : IntervalIntegrable f μ (a 0) (a n)
参数：hint : forall k < n, IntervalIntegrable f μ (a k) (a <| k + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntervalIntegrable.trans_iterate_Ico`：trans_iterate_Ico {a : Nat -> Real
} {m n : Nat} (hmn : m <= n) (hint : forall k in Ico m n, IntervalIntegrable f μ
 (a k) (a <| k + 1)) : Int…
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem trans_iterate {a : ℕ → ℝ} {n : ℕ}
    (hint : ∀ k < n, IntervalIntegrable f μ (a k) (a <| k + 1)) :
    IntervalIntegrable f μ (a 0) (a n) :=
  trans_iterate_Ico bot_le fun k hk => hint k hk.2
/-
**IntervalIntegrable.neg** 是 Mathlib 中的一个定理，位于命名空间 `IntervalIntegrable`。
形式化陈述：neg {f : Real -> E} (h : IntervalIntegrable f μ a b) : IntervalIntegrable 
(-f) μ a b
参数：h : IntervalIntegrable f μ a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IntegrableOn.neg`：∀ {α : Type u_1} {E : Type u_5} {mα : Me
asurableSpace α} [inst : NormedAddCommGroup E] {s : Set α}   {μ : MeasureTheory.
Measure α} {f : α → …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem neg {f : ℝ → E} (h : IntervalIntegrable f μ a b) : IntervalIntegrable (-f) μ a b :=
  ⟨h.1.neg, h.2.neg⟩

omit [PseudoMetrizableSpace ε] in
/-
**IntervalIntegrable.enorm** 是 Mathlib 中的一个定理，位于命名空间 `IntervalIntegrable`。
形式化陈述：enorm (h : IntervalIntegrable f μ a b) : IntervalIntegrable (‖f ·‖ₑ) μ a b
参数：h : IntervalIntegrable f μ a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.enorm`：∀ {α : Type u_1} {ε : Type u_5} {m : Mea
surableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace ε]   [ins
t_1 : ContinuousENor…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem enorm (h : IntervalIntegrable f μ a b) : IntervalIntegrable (‖f ·‖ₑ) μ a b :=
  ⟨h.1.enorm, h.2.enorm⟩
/-
**IntervalIntegrable.norm** 是 Mathlib 中的一个定理，位于命名空间 `IntervalIntegrable`。
形式化陈述：norm {f : Real -> E} (h : IntervalIntegrable f μ a b) : IntervalIntegrable
 (‖f ·‖) μ a b
参数：h : IntervalIntegrable f μ a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.norm`：∀ {α : Type u_1} {β : Type u_2} {m : Meas
urableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f 
: α → β}, MeasureTh…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem norm {f : ℝ → E} (h : IntervalIntegrable f μ a b) : IntervalIntegrable (‖f ·‖) μ a b :=
  ⟨h.1.norm, h.2.norm⟩
/-
**IntervalIntegrable.intervalIntegrable_enorm_iff** 是 Mathlib 中的一个定理，位于命名空间 `Int
ervalIntegrable`。
形式化陈述：intervalIntegrable_enorm_iff {μ : Measure Real} {a b : Real} (hf : AEStron
glyMeasurable f (μ.restrict (Ι a b))) : IntervalIntegrable (fun t => ‖f t‖ₑ) μ a
 b ↔ IntervalIntegrable f μ a b
参数：hf : AEStronglyMeasurable f (μ.restrict (Ι a b))。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopologicalSpace.MetrizableSpace.toPseudoMetrizableSpace`：∀ {X : Type u_
5} {t : TopologicalSpace X} [self : TopologicalSpace.MetrizableSpace X],   Topol
ogicalSpace.PseudoMetrizableSpace X
· 使用定理 `ENNReal.instMetrizableSpace`：TopologicalSpace.MetrizableSpace ENNReal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.integrable_enorm_iff`：integrable_enorm_iff {f : α -> ε} (h
f : AEStronglyMeasurable f μ) : Integrable (‖f ·‖ₑ) μ ↔ Integrable f μ
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem intervalIntegrable_enorm_iff {μ : Measure ℝ} {a b : ℝ}
    (hf : AEStronglyMeasurable f (μ.restrict (Ι a b))) :
    IntervalIntegrable (fun t => ‖f t‖ₑ) μ a b ↔ IntervalIntegrable f μ a b := by
  simp_rw [intervalIntegrable_iff, IntegrableOn, integrable_enorm_iff hf]
/-
**IntervalIntegrable.intervalIntegrable_norm_iff** 是 Mathlib 中的一个定理，位于命名空间 `Inte
rvalIntegrable`。
形式化陈述：intervalIntegrable_norm_iff {f : Real -> E} {μ : Measure Real} {a b : Real
} (hf : AEStronglyMeasurable f (μ.restrict (Ι a b))) : IntervalIntegrable (fun t
 => ‖f t‖) μ a b ↔ IntervalIntegrable f μ a b
参数：hf : AEStronglyMeasurable f (μ.restrict (Ι a b))。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.integrable_norm_iff`：integrable_norm_iff {f : α -> β} (hf 
: AEStronglyMeasurable f μ) : Integrable (fun a => ‖f a‖) μ ↔ Integrable f μ
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem intervalIntegrable_norm_iff {f : ℝ → E} {μ : Measure ℝ} {a b : ℝ}
    (hf : AEStronglyMeasurable f (μ.restrict (Ι a b))) :
    IntervalIntegrable (fun t => ‖f t‖) μ a b ↔ IntervalIntegrable f μ a b := by
  simp_rw [intervalIntegrable_iff, IntegrableOn, integrable_norm_iff hf]
/-
**IntervalIntegrable.abs** 是 Mathlib 中的一个定理，位于命名空间 `IntervalIntegrable`。
形式化陈述：abs {f : Real -> Real} (h : IntervalIntegrable f μ a b) : IntervalIntegrab
le (fun x => |f x|) μ a b
参数：h : IntervalIntegrable f μ a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntervalIntegrable.norm`：norm {f : Real -> E} (h : IntervalIntegrable f 
μ a b) : IntervalIntegrable (‖f ·‖) μ a b
-/
theorem abs {f : ℝ → ℝ} (h : IntervalIntegrable f μ a b) :
    IntervalIntegrable (fun x => |f x|) μ a b :=
  h.norm
/-
**IntervalIntegrable.mono** 是 Mathlib 中的一个定理，位于命名空间 `IntervalIntegrable`。
形式化陈述：mono (hf : IntervalIntegrable f ν a b) (h1 : [[c, d]] subseteq [[a, b]]) (
h2 : μ <= ν) : IntervalIntegrable f μ c d
参数：hf : IntervalIntegrable f ν a b；h1 : [[c, d]] subseteq [[a, b]]；h2 : μ <= ν。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `intervalIntegrable_iff`：intervalIntegrable_iff : IntervalIntegrable f μ 
a b ↔ IntegrableOn f (Ι a b) μ
· 使用定理 `MeasureTheory.IntegrableOn.mono`：∀ {α : Type u_1} {ε : Type u_3} {mα : M
easurableSpace α} {f : α → ε} {s t : Set α} {μ ν : MeasureTheory.Measure α}   [i
nst : TopologicalSpac…
· 使用定理 `IntervalIntegrable.def'`：IntervalIntegrable.def' (h : IntervalIntegrable
 f μ a b) : IntegrableOn f (Ι a b) μ
· 使用引理 `Set.uIoc_subset_uIoc_of_uIcc_subset_uIcc`：uIoc_subset_uIoc_of_uIcc_subse
t_uIcc {a b c d : α} (h : [[a, b]] subseteq [[c, d]]) : Ι a b subseteq Ι c d
-/
theorem mono (hf : IntervalIntegrable f ν a b) (h1 : [[c, d]] ⊆ [[a, b]]) (h2 : μ ≤ ν) :
    IntervalIntegrable f μ c d :=
  intervalIntegrable_iff.mpr <| hf.def'.mono (uIoc_subset_uIoc_of_uIcc_subset_uIcc h1) h2
/-
**IntervalIntegrable.mono_measure** 是 Mathlib 中的一个定理，位于命名空间 `IntervalIntegrable`
。
形式化陈述：mono_measure (hf : IntervalIntegrable f ν a b) (h : μ <= ν) : IntervalInte
grable f μ a b
参数：hf : IntervalIntegrable f ν a b；h : μ <= ν。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntervalIntegrable.mono`：mono (hf : IntervalIntegrable f ν a b) (h1 : [[
c, d]] subseteq [[a, b]]) (h2 : μ <= ν) : IntervalIntegrable f μ c d
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
theorem mono_measure (hf : IntervalIntegrable f ν a b) (h : μ ≤ ν) : IntervalIntegrable f μ a b :=
  hf.mono Subset.rfl h
/-
**IntervalIntegrable.mono_set** 是 Mathlib 中的一个定理，位于命名空间 `IntervalIntegrable`。
形式化陈述：mono_set (hf : IntervalIntegrable f μ a b) (h : [[c, d]] subseteq [[a, b]]
) : IntervalIntegrable f μ c d
参数：hf : IntervalIntegrable f μ a b；h : [[c, d]] subseteq [[a, b]]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntervalIntegrable.mono`：mono (hf : IntervalIntegrable f ν a b) (h1 : [[
c, d]] subseteq [[a, b]]) (h2 : μ <= ν) : IntervalIntegrable f μ c d
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem mono_set (hf : IntervalIntegrable f μ a b) (h : [[c, d]] ⊆ [[a, b]]) :
    IntervalIntegrable f μ c d :=
  hf.mono h le_rfl
/-
**IntervalIntegrable.mono_set_ae** 是 Mathlib 中的一个定理，位于命名空间 `IntervalIntegrable`。
形式化陈述：mono_set_ae (hf : IntervalIntegrable f μ a b) (h : Ι c d <=ᵐ[μ] Ι a b) : I
ntervalIntegrable f μ c d
参数：hf : IntervalIntegrable f μ a b；h : Ι c d <=ᵐ[μ] Ι a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `intervalIntegrable_iff`：intervalIntegrable_iff : IntervalIntegrable f μ 
a b ↔ IntegrableOn f (Ι a b) μ
· 使用定理 `MeasureTheory.IntegrableOn.mono_set_ae`：∀ {α : Type u_1} {ε : Type u_3} 
{mα : MeasurableSpace α} {f : α → ε} {s t : Set α} {μ : MeasureTheory.Measure α}
   [inst : TopologicalSpace …
· 使用定理 `IntervalIntegrable.def'`：IntervalIntegrable.def' (h : IntervalIntegrable
 f μ a b) : IntegrableOn f (Ι a b) μ
-/
theorem mono_set_ae (hf : IntervalIntegrable f μ a b) (h : Ι c d ≤ᵐ[μ] Ι a b) :
    IntervalIntegrable f μ c d :=
  intervalIntegrable_iff.mpr <| hf.def'.mono_set_ae h
/-
**IntervalIntegrable.mono_set'** 是 Mathlib 中的一个定理，位于命名空间 `IntervalIntegrable`。
形式化陈述：mono_set' (hf : IntervalIntegrable f μ a b) (hsub : Ι c d subseteq Ι a b) 
: IntervalIntegrable f μ c d
参数：hf : IntervalIntegrable f μ a b；hsub : Ι c d subseteq Ι a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntervalIntegrable.mono_set_ae`：mono_set_ae (hf : IntervalIntegrable f μ
 a b) (h : Ι c d <=ᵐ[μ] Ι a b) : IntervalIntegrable f μ c d
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
theorem mono_set' (hf : IntervalIntegrable f μ a b) (hsub : Ι c d ⊆ Ι a b) :
    IntervalIntegrable f μ c d :=
  hf.mono_set_ae <| Eventually.of_forall hsub
/-
**IntervalIntegrable.mono_fun_enorm** 是 Mathlib 中的一个定理，位于命名空间 `IntervalIntegrabl
e`。
形式化陈述：mono_fun_enorm [PseudoMetrizableSpace ε'] {g : Real -> ε'} (hf : IntervalI
ntegrable f μ a b) (hgm : AEStronglyMeasurable g (μ.restrict (Ι a b))) (hle : (‖
g ·‖ₑ) <=ᵐ[μ.restrict (Ι a b)] (‖f ·‖ₑ)) : IntervalIntegrable g μ a b
参数：hf : IntervalIntegrable f μ a b；hgm : AEStronglyMeasurable g (μ.restrict (Ι a
 b))；hle : (‖g ·‖ₑ) <=ᵐ[μ.restrict (Ι a b)] (‖f ·‖ₑ)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `intervalIntegrable_iff`：intervalIntegrable_iff : IntervalIntegrable f μ 
a b ↔ IntegrableOn f (Ι a b) μ
· 使用定理 `MeasureTheory.Integrable.mono_enorm`：∀ {α : Type u_1} {ε : Type u_5} {ε'
 : Type u_6} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [inst : Top
ologicalSpace ε] [inst_1 …
· 使用定理 `MeasureTheory.IntegrableOn.integrable`：∀ {α : Type u_1} {ε : Type u_3} {
mα : MeasurableSpace α} {f : α → ε} {s : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace ε]…
· 使用定理 `IntervalIntegrable.def'`：IntervalIntegrable.def' (h : IntervalIntegrable
 f μ a b) : IntegrableOn f (Ι a b) μ
-/
theorem mono_fun_enorm [PseudoMetrizableSpace ε'] {g : ℝ → ε'}
    (hf : IntervalIntegrable f μ a b) (hgm : AEStronglyMeasurable g (μ.restrict (Ι a b)))
    (hle : (‖g ·‖ₑ) ≤ᵐ[μ.restrict (Ι a b)] (‖f ·‖ₑ)) : IntervalIntegrable g μ a b :=
  intervalIntegrable_iff.2 <| hf.def'.integrable.mono_enorm hgm hle
/-
**IntervalIntegrable.mono_fun** 是 Mathlib 中的一个定理，位于命名空间 `IntervalIntegrable`。
形式化陈述：mono_fun {f : Real -> E} [NormedAddCommGroup F] {g : Real -> F} (hf : Inte
rvalIntegrable f μ a b) (hgm : AEStronglyMeasurable g (μ.restrict (Ι a b))) (hle
 : (fun x => ‖g x‖) <=ᵐ[μ.restrict (Ι a b)] fun x => ‖f x‖) : IntervalIntegrable
 g μ a b
参数：hf : IntervalIntegrable f μ a b；hgm : AEStronglyMeasurable g (μ.restrict (Ι a
 b))；hle : (fun x => ‖g x‖) <=ᵐ[μ.restrict (Ι a b)] fun x => ‖f x‖。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `intervalIntegrable_iff`：intervalIntegrable_iff : IntervalIntegrable f μ 
a b ↔ IntegrableOn f (Ι a b) μ
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.Integrable.mono`：∀ {α : Type u_1} {β : Type u_2} {γ : Type
 u_3} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [inst : NormedAddC
ommGroup β] [inst_1…
· 使用定理 `MeasureTheory.IntegrableOn.integrable`：∀ {α : Type u_1} {ε : Type u_3} {
mα : MeasurableSpace α} {f : α → ε} {s : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace ε]…
· 使用定理 `IntervalIntegrable.def'`：IntervalIntegrable.def' (h : IntervalIntegrable
 f μ a b) : IntegrableOn f (Ι a b) μ
-/
theorem mono_fun {f : ℝ → E} [NormedAddCommGroup F] {g : ℝ → F} (hf : IntervalIntegrable f μ a b)
    (hgm : AEStronglyMeasurable g (μ.restrict (Ι a b)))
    (hle : (fun x => ‖g x‖) ≤ᵐ[μ.restrict (Ι a b)] fun x => ‖f x‖) : IntervalIntegrable g μ a b :=
  intervalIntegrable_iff.2 <| hf.def'.integrable.mono hgm hle

-- XXX: the best spelling of this lemma may look slightly different (e.gl, with different domain)
/-
**IntervalIntegrable.mono_fun_enorm'** 是 Mathlib 中的一个定理，位于命名空间 `IntervalIntegrab
le`。
形式化陈述：mono_fun_enorm' {f : Real -> ε} {g : Real -> Real>=0∞} (hg : IntervalInteg
rable g μ a b) (hfm : AEStronglyMeasurable f (μ.restrict (Ι a b))) (hle : (fun x
 => ‖f x‖ₑ) <=ᵐ[μ.restrict (Ι a b)] g) : IntervalIntegrable f μ a b
参数：hg : IntervalIntegrable g μ a b；hfm : AEStronglyMeasurable f (μ.restrict (Ι a
 b))；hle : (fun x => ‖f x‖ₑ) <=ᵐ[μ.restrict (Ι a b)] g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `intervalIntegrable_iff`：intervalIntegrable_iff : IntervalIntegrable f μ 
a b ↔ IntegrableOn f (Ι a b) μ
· 使用定理 `MeasureTheory.Integrable.mono_enorm`：∀ {α : Type u_1} {ε : Type u_5} {ε'
 : Type u_6} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [inst : Top
ologicalSpace ε] [inst_1 …
· 使用定理 `MeasureTheory.IntegrableOn.integrable`：∀ {α : Type u_1} {ε : Type u_3} {
mα : MeasurableSpace α} {f : α → ε} {s : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace ε]…
· 使用定理 `IntervalIntegrable.def'`：IntervalIntegrable.def' (h : IntervalIntegrable
 f μ a b) : IntegrableOn f (Ι a b) μ
· 使用定理 `TopologicalSpace.MetrizableSpace.toPseudoMetrizableSpace`：∀ {X : Type u_
5} {t : TopologicalSpace X} [self : TopologicalSpace.MetrizableSpace X],   Topol
ogicalSpace.PseudoMetrizableSpace X
· 使用定理 `ENNReal.instMetrizableSpace`：TopologicalSpace.MetrizableSpace ENNReal
-/
theorem mono_fun_enorm' {f : ℝ → ε} {g : ℝ → ℝ≥0∞} (hg : IntervalIntegrable g μ a b)
    (hfm : AEStronglyMeasurable f (μ.restrict (Ι a b)))
    (hle : (fun x => ‖f x‖ₑ) ≤ᵐ[μ.restrict (Ι a b)] g) : IntervalIntegrable f μ a b :=
  intervalIntegrable_iff.2 <| hg.def'.integrable.mono_enorm hfm hle
/-
**IntervalIntegrable.mono_fun'** 是 Mathlib 中的一个定理，位于命名空间 `IntervalIntegrable`。
形式化陈述：mono_fun' {f : Real -> E} {g : Real -> Real} (hg : IntervalIntegrable g μ 
a b) (hfm : AEStronglyMeasurable f (μ.restrict (Ι a b))) (hle : (fun x => ‖f x‖)
 <=ᵐ[μ.restrict (Ι a b)] g) : IntervalIntegrable f μ a b
参数：hg : IntervalIntegrable g μ a b；hfm : AEStronglyMeasurable f (μ.restrict (Ι a
 b))；hle : (fun x => ‖f x‖) <=ᵐ[μ.restrict (Ι a b)] g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `intervalIntegrable_iff`：intervalIntegrable_iff : IntervalIntegrable f μ 
a b ↔ IntegrableOn f (Ι a b) μ
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.Integrable.mono'`：∀ {α : Type u_1} {β : Type u_2} {m : Mea
surableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f
 : α → β} {g : α → ℝ…
· 使用定理 `MeasureTheory.IntegrableOn.integrable`：∀ {α : Type u_1} {ε : Type u_3} {
mα : MeasurableSpace α} {f : α → ε} {s : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace ε]…
· 使用定理 `IntervalIntegrable.def'`：IntervalIntegrable.def' (h : IntervalIntegrable
 f μ a b) : IntegrableOn f (Ι a b) μ
-/
theorem mono_fun' {f : ℝ → E} {g : ℝ → ℝ} (hg : IntervalIntegrable g μ a b)
    (hfm : AEStronglyMeasurable f (μ.restrict (Ι a b)))
    (hle : (fun x => ‖f x‖) ≤ᵐ[μ.restrict (Ι a b)] g) : IntervalIntegrable f μ a b :=
  intervalIntegrable_iff.2 <| hg.def'.integrable.mono' hfm hle

omit [PseudoMetrizableSpace ε] in
/-
**IntervalIntegrable.aestronglyMeasurable** 是 Mathlib 中的一个定理，位于命名空间 `IntervalInt
egrable`。
形式化陈述：∀ {ε : Type u_3} [inst : TopologicalSpace ε] [inst_1 : ENormedAddMonoid ε]
 {f : ℝ → ε} {a b : ℝ}   {μ : MeasureTheory.Measure ℝ},   IntervalIntegrable f μ
 a b → MeasureTheory.AEStronglyMeasurable f (μ.restrict (Set.Ioc a b))
参数：μ.restrict (Set.Ioc a b)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Typ
e u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topological
Space ε]   [inst_1 : ContinuousENor…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
protected theorem aestronglyMeasurable (h : IntervalIntegrable f μ a b) :
    AEStronglyMeasurable f (μ.restrict (Ioc a b)) :=
  h.1.aestronglyMeasurable

omit [PseudoMetrizableSpace ε] in
/-
**IntervalIntegrable.aestronglyMeasurable'** 是 Mathlib 中的一个定理，位于命名空间 `IntervalIn
tegrable`。
形式化陈述：∀ {ε : Type u_3} [inst : TopologicalSpace ε] [inst_1 : ENormedAddMonoid ε]
 {f : ℝ → ε} {a b : ℝ}   {μ : MeasureTheory.Measure ℝ},   IntervalIntegrable f μ
 a b → MeasureTheory.AEStronglyMeasurable f (μ.restrict (Set.Ioc b a))
参数：μ.restrict (Set.Ioc b a)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Typ
e u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topological
Space ε]   [inst_1 : ContinuousENor…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
protected theorem aestronglyMeasurable' (h : IntervalIntegrable f μ a b) :
    AEStronglyMeasurable f (μ.restrict (Ioc b a)) :=
  h.2.aestronglyMeasurable

omit [PseudoMetrizableSpace ε] in
/-
**IntervalIntegrable.aestronglyMeasurable_restrict_uIoc** 是 Mathlib 中的一个定理，位于命名空
间 `IntervalIntegrable`。
形式化陈述：∀ {ε : Type u_3} [inst : TopologicalSpace ε] [inst_1 : ENormedAddMonoid ε]
 {f : ℝ → ε} {a b : ℝ}   {μ : MeasureTheory.Measure ℝ},   IntervalIntegrable f μ
 a b → MeasureTheory.AEStronglyMeasurable f (μ.restrict (Set.uIoc a b))
参数：μ.restrict (Set.uIoc a b)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.uIoc_of_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b
 → Set.uIoc a b = Set.Ioc a b
· 使用定理 `IntervalIntegrable.aestronglyMeasurable`：∀ {ε : Type u_3} [inst : Topolo
gicalSpace ε] [inst_1 : ENormedAddMonoid ε] {f : ℝ → ε} {a b : ℝ}   {μ : Measure
Theory.Measure ℝ},   Interval…
· 使用定理 `Set.uIoc_of_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a
 → Set.uIoc a b = Set.Ioc b a
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf_zero`：∀ {R : Type u_1} [inst :
 CommSemiring R] {a b : R} (x : R) (e : ℕ),   Mathlib.Meta.NormNum.IsNat (a + b)
 0 → Mathlib.Meta.NormNum.IsNat (x ^…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
（共 35 条，此处仅展示前 30 条）
-/
protected theorem aestronglyMeasurable_restrict_uIoc (h : IntervalIntegrable f μ a b) :
    AEStronglyMeasurable f (μ.restrict (uIoc a b)) := by
  by_cases hab : a ≤ b
  · rw [uIoc_of_le hab]; exact h.aestronglyMeasurable
  · rw [uIoc_of_ge (by linarith)]; exact h.aestronglyMeasurable'

end

variable [NormedRing A] {f g : ℝ → ε} {a b : ℝ} {μ : Measure ℝ}

/-
**IntervalIntegrable.smul** 是 Mathlib 中的一个定理，位于命名空间 `IntervalIntegrable`。
形式化陈述：smul {R : Type*} [NormedAddCommGroup R] [SMulZeroClass R E] [IsBoundedSMul
 R E] {f : Real -> E} (h : IntervalIntegrable f μ a b) (r : R) : IntervalIntegra
ble (r • f) μ a b
参数：h : IntervalIntegrable f μ a b；r : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.smul`：∀ {α : Type u_1} {β : Type u_2} {m : Meas
urableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {𝕜 
: Type u_8} [inst_1…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem smul {R : Type*} [NormedAddCommGroup R] [SMulZeroClass R E] [IsBoundedSMul R E] {f : ℝ → E}
    (h : IntervalIntegrable f μ a b) (r : R) :
    IntervalIntegrable (r • f) μ a b :=
  ⟨h.1.smul r, h.2.smul r⟩

@[simp]
/-
**IntervalIntegrable.add** 是 Mathlib 中的一个定理，位于命名空间 `IntervalIntegrable`。
形式化陈述：add [ContinuousAdd ε] (hf : IntervalIntegrable f μ a b) (hg : IntervalInte
grable g μ a b) : IntervalIntegrable (fun x => f x + g x) μ a b
参数：hf : IntervalIntegrable f μ a b；hg : IntervalIntegrable g μ a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IntegrableOn.add`：∀ {α : Type u_1} {ε' : Type u_4} {mα : M
easurableSpace α} {s : Set α} {μ : MeasureTheory.Measure α}   [inst : Topologica
lSpace ε'] [inst_1 :…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem add [ContinuousAdd ε] (hf : IntervalIntegrable f μ a b) (hg : IntervalIntegrable g μ a b) :
    IntervalIntegrable (fun x => f x + g x) μ a b :=
  ⟨hf.1.add hg.1, hf.2.add hg.2⟩

@[simp]
/-
**IntervalIntegrable.sub** 是 Mathlib 中的一个定理，位于命名空间 `IntervalIntegrable`。
形式化陈述：sub {f g : Real -> E} (hf : IntervalIntegrable f μ a b) (hg : IntervalInte
grable g μ a b) : IntervalIntegrable (fun x => f x - g x) μ a b
参数：hf : IntervalIntegrable f μ a b；hg : IntervalIntegrable g μ a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IntegrableOn.sub`：∀ {α : Type u_1} {E : Type u_5} {mα : Me
asurableSpace α} [inst : NormedAddCommGroup E] {s : Set α}   {μ : MeasureTheory.
Measure α} {f g : α …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem sub {f g : ℝ → E} (hf : IntervalIntegrable f μ a b) (hg : IntervalIntegrable g μ a b) :
    IntervalIntegrable (fun x => f x - g x) μ a b :=
  ⟨hf.1.sub hg.1, hf.2.sub hg.2⟩
/-
**IntervalIntegrable.sum** 是 Mathlib 中的一个定理，位于命名空间 `IntervalIntegrable`。
形式化陈述：sum {ε} [TopologicalSpace ε] [ENormedAddCommMonoid ε] [ContinuousAdd ε] (s
 : Finset ι) {f : ι -> Real -> ε} (h : forall i in s, IntervalIntegrable (f i) μ
 a b) : IntervalIntegrable (∑ i in s, f i) μ a b
参数：s : Finset ι；h : forall i in s, IntervalIntegrable (f i) μ a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integrable_finsetSum'`：integrable_finsetSum' {ι} (s : Fins
et ι) {f : ι -> α -> ε'} (hf : forall i in s, Integrable (f i) μ) : Integrable (
∑ i in s, f i) μ
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem sum {ε} [TopologicalSpace ε] [ENormedAddCommMonoid ε] [ContinuousAdd ε]
    (s : Finset ι) {f : ι → ℝ → ε} (h : ∀ i ∈ s, IntervalIntegrable (f i) μ a b) :
    IntervalIntegrable (∑ i ∈ s, f i) μ a b :=
  ⟨integrable_finsetSum' s fun i hi => (h i hi).1, integrable_finsetSum' s fun i hi => (h i hi).2⟩

/-- Finite sums of interval integrable functions are interval integrable. -/
@[simp]
/-
**IntervalIntegrable.finsum** 是 Mathlib 中的一个定理，位于命名空间 `IntervalIntegrable`。
形式化陈述：∀ {ι : Type u_1} {a b : ℝ} {μ : MeasureTheory.Measure ℝ} {ε : Type u_8} [i
nst : TopologicalSpace ε]   [inst_1 : ENormedAddCommMonoid ε] [ContinuousAdd ε] 
[TopologicalSpace.PseudoMetrizableSpace ε] {f : ι → ℝ → ε},   (∀ (i : ι), Interv
alIntegrable (f i) μ a b) → IntervalIntegrable (∑ᶠ (i : ι), f i) μ a b
参数：∀ (i : ι), IntervalIntegrable (f i) μ a b；∑ᶠ (i : ι), f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finsum_eq_sum`：∀ {α : Type u_1} {M : Type u_5} [inst : AddCommMonoid M] 
(f : α → M) (hf : Function.HasFiniteSupport f),   ∑ᶠ (i : α), f i = ∑ i ∈ Set.Fi
nit…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `IntervalIntegrable.sum`：sum {ε} [TopologicalSpace ε] [ENormedAddCommMono
id ε] [ContinuousAdd ε] (s : Finset ι) {f : ι -> Real -> ε} (h : forall i in s, 
IntervalInte…
· 使用定理 `finsum_of_infinite_support`：∀ {α : Type u_1} {M : Type u_5} [inst : AddC
ommMonoid M] {f : α → M},   (Function.support f).Infinite → ∑ᶠ (i : α), f i = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `intervalIntegrable_const_iff`：intervalIntegrable_const_iff {c : ε} (hc :
 ‖c‖ₑ != ⊤
· 使用定理 `enorm_zero`：∀ {E : Type u_8} [inst : TopologicalSpace E] [inst_1 : ESemi
normedAddMonoid E], ‖0‖ₑ = 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b

--- 原说明 ---
Finite sums of interval integrable functions are interval integrable.
-/
protected theorem finsum
    {ε} [TopologicalSpace ε] [ENormedAddCommMonoid ε] [ContinuousAdd ε] [PseudoMetrizableSpace ε]
    {f : ι → ℝ → ε} (h : ∀ i, IntervalIntegrable (f i) μ a b) :
    IntervalIntegrable (∑ᶠ i, f i) μ a b := by
  by_cases h₁ : f.support.Finite
  · simp [finsum_eq_sum _ h₁, IntervalIntegrable.sum h₁.toFinset (fun i _ ↦ h i)]
  · rw [finsum_of_infinite_support h₁]
    apply intervalIntegrable_const_iff (c := 0) (by simp) |>.2
    tauto

section Mul

/-
**IntervalIntegrable.mul_continuousOn** 是 Mathlib 中的一个定理，位于命名空间 `IntervalIntegra
ble`。
形式化陈述：mul_continuousOn {f g : Real -> A} (hf : IntervalIntegrable f μ a b) (hg :
 ContinuousOn g [[a, b]]) : IntervalIntegrable (fun x => f x * g x) μ a b
参数：hf : IntervalIntegrable f μ a b；hg : ContinuousOn g [[a, b]]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intervalIntegrable_iff`：intervalIntegrable_iff : IntervalIntegrable f μ 
a b ↔ IntegrableOn f (Ι a b) μ
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.IntegrableOn.mul_continuousOn_of_subset`：∀ {X : Type u_1} 
{R : Type u_8} [inst : MeasurableSpace X] [inst_1 : TopologicalSpace X] {μ : Mea
sureTheory.Measure X}   [OpensMeasurableSpa…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `secondCountableTopologyEither_of_left`：∀ (α : Type u_6) (β : Type u_7) [
inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolog
y α],   SecondCountableTopo…
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `measurableSet_Ioc`：measurableSet_Ioc [ClosedIicTopology α] : MeasurableS
et (Ioc a b)
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `isCompact_uIcc`：isCompact_uIcc {α : Type*} [LinearOrder α] [TopologicalS
pace α] [CompactIccSpace α] {a b : α} : IsCompact (uIcc a b)
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Set.Ioc_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc a b ⊆ Set.Icc a b
-/
theorem mul_continuousOn {f g : ℝ → A} (hf : IntervalIntegrable f μ a b)
    (hg : ContinuousOn g [[a, b]]) : IntervalIntegrable (fun x => f x * g x) μ a b := by
  rw [intervalIntegrable_iff] at hf ⊢
  exact hf.mul_continuousOn_of_subset hg measurableSet_Ioc isCompact_uIcc Ioc_subset_Icc_self
/-
**IntervalIntegrable.continuousOn_mul** 是 Mathlib 中的一个定理，位于命名空间 `IntervalIntegra
ble`。
形式化陈述：continuousOn_mul {f g : Real -> A} (hf : IntervalIntegrable f μ a b) (hg :
 ContinuousOn g [[a, b]]) : IntervalIntegrable (fun x => g x * f x) μ a b
参数：hf : IntervalIntegrable f μ a b；hg : ContinuousOn g [[a, b]]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intervalIntegrable_iff`：intervalIntegrable_iff : IntervalIntegrable f μ 
a b ↔ IntegrableOn f (Ι a b) μ
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.IntegrableOn.continuousOn_mul_of_subset`：∀ {X : Type u_1} 
{R : Type u_8} [inst : MeasurableSpace X] [inst_1 : TopologicalSpace X] {μ : Mea
sureTheory.Measure X}   [OpensMeasurableSpa…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `secondCountableTopologyEither_of_left`：∀ (α : Type u_6) (β : Type u_7) [
inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolog
y α],   SecondCountableTopo…
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `isCompact_uIcc`：isCompact_uIcc {α : Type*} [LinearOrder α] [TopologicalS
pace α] [CompactIccSpace α] {a b : α} : IsCompact (uIcc a b)
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `measurableSet_Ioc`：measurableSet_Ioc [ClosedIicTopology α] : MeasurableS
et (Ioc a b)
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Set.Ioc_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc a b ⊆ Set.Icc a b
-/
theorem continuousOn_mul {f g : ℝ → A} (hf : IntervalIntegrable f μ a b)
    (hg : ContinuousOn g [[a, b]]) : IntervalIntegrable (fun x => g x * f x) μ a b := by
  rw [intervalIntegrable_iff] at hf ⊢
  exact hf.continuousOn_mul_of_subset hg isCompact_uIcc measurableSet_Ioc Ioc_subset_Icc_self

@[simp]
/-
**IntervalIntegrable.const_mul** 是 Mathlib 中的一个定理，位于命名空间 `IntervalIntegrable`。
形式化陈述：const_mul {f : Real -> A} (hf : IntervalIntegrable f μ a b) (c : A) : Inte
rvalIntegrable (fun x => c * f x) μ a b
参数：hf : IntervalIntegrable f μ a b；c : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntervalIntegrable.continuousOn_mul`：continuousOn_mul {f g : Real -> A} 
(hf : IntervalIntegrable f μ a b) (hg : ContinuousOn g [[a, b]]) : IntervalInteg
rable (fun x => g x * f x…
· 使用定理 `continuousOn_const`：continuousOn_const {s : Set α} {c : β} : ContinuousO
n (fun _ => c) s
-/
theorem const_mul {f : ℝ → A} (hf : IntervalIntegrable f μ a b) (c : A) :
    IntervalIntegrable (fun x => c * f x) μ a b :=
  hf.continuousOn_mul continuousOn_const

@[simp]
/-
**IntervalIntegrable.mul_const** 是 Mathlib 中的一个定理，位于命名空间 `IntervalIntegrable`。
形式化陈述：mul_const {f : Real -> A} (hf : IntervalIntegrable f μ a b) (c : A) : Inte
rvalIntegrable (fun x => f x * c) μ a b
参数：hf : IntervalIntegrable f μ a b；c : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntervalIntegrable.mul_continuousOn`：mul_continuousOn {f g : Real -> A} 
(hf : IntervalIntegrable f μ a b) (hg : ContinuousOn g [[a, b]]) : IntervalInteg
rable (fun x => f x * g x…
· 使用定理 `continuousOn_const`：continuousOn_const {s : Set α} {c : β} : ContinuousO
n (fun _ => c) s
-/
theorem mul_const {f : ℝ → A} (hf : IntervalIntegrable f μ a b) (c : A) :
    IntervalIntegrable (fun x => f x * c) μ a b :=
  hf.mul_continuousOn continuousOn_const

end Mul

section SMul

variable {f : ℝ → 𝕜} {g : ℝ → E} [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

/-
**IntervalIntegrable.smul_continuousOn** 是 Mathlib 中的一个定理，位于命名空间 `IntervalIntegr
able`。
形式化陈述：smul_continuousOn (hf : IntervalIntegrable f μ a b) (hg : ContinuousOn g [
[a, b]]) : IntervalIntegrable (fun x => f x • g x) μ a b
参数：hf : IntervalIntegrable f μ a b；hg : ContinuousOn g [[a, b]]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intervalIntegrable_iff`：intervalIntegrable_iff : IntervalIntegrable f μ 
a b ↔ IntegrableOn f (Ι a b) μ
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.IntegrableOn.smul_continuousOn_of_subset`：∀ {X : Type u_1}
 {E : Type u_6} [inst : MeasurableSpace X] [inst_1 : TopologicalSpace X] [inst_2
 : NormedAddCommGroup E]   {μ : MeasureTheor…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `secondCountableTopologyEither_of_left`：∀ (α : Type u_6) (β : Type u_7) [
inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolog
y α],   SecondCountableTopo…
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `measurableSet_Ioc`：measurableSet_Ioc [ClosedIicTopology α] : MeasurableS
et (Ioc a b)
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `isCompact_uIcc`：isCompact_uIcc {α : Type*} [LinearOrder α] [TopologicalS
pace α] [CompactIccSpace α] {a b : α} : IsCompact (uIcc a b)
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Set.Ioc_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc a b ⊆ Set.Icc a b
-/
theorem smul_continuousOn (hf : IntervalIntegrable f μ a b)
    (hg : ContinuousOn g [[a, b]]) : IntervalIntegrable (fun x => f x • g x) μ a b := by
  rw [intervalIntegrable_iff] at hf ⊢
  exact hf.smul_continuousOn_of_subset hg measurableSet_Ioc isCompact_uIcc Ioc_subset_Icc_self
/-
**IntervalIntegrable.continuousOn_smul** 是 Mathlib 中的一个定理，位于命名空间 `IntervalIntegr
able`。
形式化陈述：continuousOn_smul (hg : IntervalIntegrable g μ a b) (hf : ContinuousOn f [
[a, b]]) : IntervalIntegrable (fun x => f x • g x) μ a b
参数：hg : IntervalIntegrable g μ a b；hf : ContinuousOn f [[a, b]]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intervalIntegrable_iff`：intervalIntegrable_iff : IntervalIntegrable f μ 
a b ↔ IntegrableOn f (Ι a b) μ
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.IntegrableOn.continuousOn_smul_of_subset`：∀ {X : Type u_1}
 {E : Type u_6} [inst : MeasurableSpace X] [inst_1 : TopologicalSpace X] [inst_2
 : NormedAddCommGroup E]   {μ : MeasureTheor…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `secondCountableTopologyEither_of_left`：∀ (α : Type u_6) (β : Type u_7) [
inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolog
y α],   SecondCountableTopo…
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `isCompact_uIcc`：isCompact_uIcc {α : Type*} [LinearOrder α] [TopologicalS
pace α] [CompactIccSpace α] {a b : α} : IsCompact (uIcc a b)
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `measurableSet_Ioc`：measurableSet_Ioc [ClosedIicTopology α] : MeasurableS
et (Ioc a b)
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Set.Ioc_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc a b ⊆ Set.Icc a b
-/
theorem continuousOn_smul (hg : IntervalIntegrable g μ a b)
    (hf : ContinuousOn f [[a, b]]) : IntervalIntegrable (fun x => f x • g x) μ a b := by
  rw [intervalIntegrable_iff] at hg ⊢
  exact hg.continuousOn_smul_of_subset hf isCompact_uIcc measurableSet_Ioc Ioc_subset_Icc_self

end SMul

@[simp]
/-
**IntervalIntegrable.div_const** 是 Mathlib 中的一个定理，位于命名空间 `IntervalIntegrable`。
形式化陈述：div_const {𝕜 : Type*} {f : Real -> 𝕜} [NormedDivisionRing 𝕜] (h : Interval
Integrable f μ a b) (c : 𝕜) : IntervalIntegrable (fun x => f x / c) μ a b
参数：h : IntervalIntegrable f μ a b；c : 𝕜。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `IntervalIntegrable.mul_const`：mul_const {f : Real -> A} (hf : IntervalIn
tegrable f μ a b) (c : A) : IntervalIntegrable (fun x => f x * c) μ a b
-/
theorem div_const {𝕜 : Type*} {f : ℝ → 𝕜} [NormedDivisionRing 𝕜] (h : IntervalIntegrable f μ a b)
    (c : 𝕜) : IntervalIntegrable (fun x => f x / c) μ a b := by
  simpa only [div_eq_mul_inv] using mul_const h c⁻¹

variable [PseudoMetrizableSpace ε]
/-
**IntervalIntegrable.comp_mul_left** 是 Mathlib 中的一个定理，位于命名空间 `IntervalIntegrable
`。
形式化陈述：comp_mul_left (hf : IntervalIntegrable f volume a b) {c : Real} (h : ‖f (m
in a b)‖ₑ != ∞
参数：hf : IntervalIntegrable f volume a b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `intervalIntegrable_iff'`：intervalIntegrable_iff' [NullSingletonClass μ] 
(h : ‖f (min a b)‖ₑ != ∞
· 使用定理 `Topology.IsClosedEmbedding.measurableEmbedding`：∀ {α : Type u_1} {β : Ty
pe u_2} [inst : TopologicalSpace α] [mα : MeasurableSpace α] [BorelSpace α]   [m
β : TopologicalSpace β] [inst_2 : Me…
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
· 使用定理 `Homeomorph.isClosedEmbedding`：isClosedEmbedding (h : X ≃ₜ Y) : IsClosedE
mbedding h
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.smul_map_volume_mul_right`：smul_map_volume_mul_right {a : Real} (h 
: a != 0) : ENNReal.ofReal |a| • Measure.map (· * a) volume = volume
· 使用定理 `MeasureTheory.IntegrableOn.eq_1`：∀ {α : Type u_1} {ε : Type u_3} {mα : M
easurableSpace α} [inst : TopologicalSpace ε] [inst_1 : ContinuousENorm ε]   (f 
: α → ε) (s : Set α) …
· 使用定理 `MeasureTheory.Measure.restrict_smul`：restrict_smul {_m0 : MeasurableSpac
e α} {R : Type*} [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] (c : R) (
μ : Measure α) (s : Set α…
· 使用定理 `MeasureTheory.integrable_smul_measure`：integrable_smul_measure {f : α ->
 ε} {c : Real>=0∞} (h₁ : c != 0) (h₂ : c != ∞) : Integrable f (c • μ) ↔ Integrab
le f μ
· 使用定理 `abs_inv`：abs_inv (a : α) : |a⁻¹| = |a|⁻¹
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `ENNReal.ofReal_ne_top`：ofReal_ne_top {r : Real} : ENNReal.ofReal r != ∞
· 使用定理 `MeasurableEmbedding.integrableOn_map_iff`：∀ {α : Type u_1} {β : Type u_2
} {ε : Type u_3} {mα : MeasurableSpace α} [inst : TopologicalSpace ε]   [inst_1 
: ContinuousENorm ε] [inst_2 :…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
（共 64 条，此处仅展示前 30 条）
-/
theorem comp_mul_left (hf : IntervalIntegrable f volume a b) {c : ℝ}
    (h : ‖f (min a b)‖ₑ ≠ ∞ := by finiteness)
    (h' : ‖f (c * min (a / c) (b / c))‖ₑ ≠ ∞ := by finiteness) :
    IntervalIntegrable (fun x => f (c * x)) volume (a / c) (b / c) := by
  rcases eq_or_ne c 0 with (hc | hc); · rw [hc]; simp
  rw [intervalIntegrable_iff' h] at hf
  rw [intervalIntegrable_iff' h'] at ⊢
  have A : MeasurableEmbedding fun x => x * c⁻¹ :=
    (Homeomorph.mulRight₀ _ (inv_ne_zero hc)).isClosedEmbedding.measurableEmbedding
  rw [← Real.smul_map_volume_mul_right (inv_ne_zero hc), IntegrableOn, Measure.restrict_smul,
    integrable_smul_measure (by simpa : ENNReal.ofReal |c⁻¹| ≠ 0) ENNReal.ofReal_ne_top,
    ← IntegrableOn, MeasurableEmbedding.integrableOn_map_iff A]
  convert! hf using 1
  · ext; simp only [comp_apply]; congr 1; field
  · rw [preimage_mul_const_uIcc (inv_ne_zero hc)]; field_simp

-- Note that `h'` is **not** implied by `h` if `c` is negative.
-- TODO: generalise this lemma to enorms!
/-
**IntervalIntegrable.comp_mul_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `IntervalIntegr
able`。
形式化陈述：comp_mul_left_iff {f : Real -> E} {c : Real} (hc : c != 0) (h : ‖f (min a 
b)‖ₑ != ∞
参数：hc : c != 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_inv_cancel_left₀`：mul_inv_cancel_left₀ (h : a != 0) (b : G₀) : a * (
a⁻¹ * b) = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `div_inv_eq_mul`：div_inv_eq_mul : a / b⁻¹ = a * b
· 使用定理 `IsUnit.div_mul_cancel`：∀ {α : Type u} [inst : DivisionMonoid α] {b : α},
 IsUnit b → ∀ (a : α), a / b * b = a
· 使用定理 `IntervalIntegrable.comp_mul_left`：comp_mul_left (hf : IntervalIntegrable
 f volume a b) {c : Real} (h : ‖f (min a b)‖ₑ != ∞
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
-/
theorem comp_mul_left_iff {f : ℝ → E} {c : ℝ} (hc : c ≠ 0) (h : ‖f (min a b)‖ₑ ≠ ∞ := by finiteness)
    (h' : ‖f (c * min (a / c) (b / c))‖ₑ ≠ ∞ := by finiteness) :
    IntervalIntegrable (fun x ↦ f (c * x)) volume (a / c) (b / c) ↔
      IntervalIntegrable f volume a b := by
  exact ⟨fun h ↦ by simpa [hc] using h.comp_mul_left (c := c⁻¹) h' (by simp),
    (comp_mul_left · h h')⟩
/-
**IntervalIntegrable.comp_mul_right** 是 Mathlib 中的一个定理，位于命名空间 `IntervalIntegrabl
e`。
形式化陈述：comp_mul_right (hf : IntervalIntegrable f volume a b) {c : Real} (h : ‖f (
min a b)‖ₑ != ∞
参数：hf : IntervalIntegrable f volume a b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `IntervalIntegrable.comp_mul_left`：comp_mul_left (hf : IntervalIntegrable
 f volume a b) {c : Real} (h : ‖f (min a b)‖ₑ != ∞
-/
theorem comp_mul_right (hf : IntervalIntegrable f volume a b) {c : ℝ}
    (h : ‖f (min a b)‖ₑ ≠ ∞ := by finiteness)
    (h' : ‖f (c * min (a / c) (b / c))‖ₑ ≠ ∞ := by finiteness) :
    IntervalIntegrable (fun x => f (x * c)) volume (a / c) (b / c) := by
  simpa only [mul_comm] using comp_mul_left hf h h'
/-
**IntervalIntegrable.comp_add_right** 是 Mathlib 中的一个定理，位于命名空间 `IntervalIntegrabl
e`。
形式化陈述：comp_add_right (hf : IntervalIntegrable f volume a b) (c : Real) (h : ‖f (
min a b)‖ₑ != ∞
参数：hf : IntervalIntegrable f volume a b；c : Real。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `min_sub_sub_right`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : Li
nearOrder α] [IsOrderedAddMonoid α] (a b c : α),   min (a - c) (b - c) = min a b
 - c
· 使用定理 `sub_add`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c : α), 
a - b + c = a - (b - c)
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `intervalIntegrable_iff'`：intervalIntegrable_iff' [NullSingletonClass μ] 
(h : ‖f (min a b)‖ₑ != ∞
· 使用定理 `Topology.IsClosedEmbedding.measurableEmbedding`：∀ {α : Type u_1} {β : Ty
pe u_2} [inst : TopologicalSpace α] [mα : MeasurableSpace α] [BorelSpace α]   [m
β : TopologicalSpace β] [inst_2 : Me…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Homeomorph.isClosedEmbedding`：isClosedEmbedding (h : X ≃ₜ Y) : IsClosedE
mbedding h
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.preimage_add_const_uIcc`：preimage_add_const_uIcc : (fun x => x + a) 
⁻¹' [[b, c]] = [[b - a, c - a]]
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasurableEmbedding.integrableOn_map_iff`：∀ {α : Type u_1} {β : Type u_2
} {ε : Type u_3} {mα : MeasurableSpace α} [inst : TopologicalSpace ε]   [inst_1 
: ContinuousENorm ε] [inst_2 :…
· 使用定理 `MeasureTheory.map_add_right_eq_self`：∀ {G : Type u_1} [inst : Measurable
Space G] [inst_1 : Add G] (μ : MeasureTheory.Measure G) [μ.IsAddRightInvariant] 
  (g : G), MeasureTheory.…
· 使用定理 `MeasureTheory.IsAddLeftInvariant.isAddRightInvariant`：∀ {G : Type u_1} [
inst : MeasurableSpace G] [inst_1 : AddCommSemigroup G] {μ : MeasureTheory.Measu
re G}   [μ.IsAddLeftInvariant], μ.IsAddRig…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsAddLeftInvariant`：∀ {G : Type
 u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpac
e G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `IntervalIntegrable.symm`：∀ {ε : Type u_3} [inst : TopologicalSpace ε] [i
nst_1 : ENormedAddMonoid ε] {f : ℝ → ε} {a b : ℝ}   {μ : MeasureTheory.Measure ℝ
}, IntervalIn…
· 使用引理 `min_comm`：min_comm (a b : α) : min a b = min b a
· 使用定理 `le_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b 
→ b ≤ a
-/
theorem comp_add_right (hf : IntervalIntegrable f volume a b) (c : ℝ)
    (h : ‖f (min a b)‖ₑ ≠ ∞ := by finiteness) :
    IntervalIntegrable (fun x ↦ f (x + c)) volume (a - c) (b - c) := by
  have h' : ‖f (min (a - c) (b - c) + c)‖ₑ ≠ ⊤ := by
    rw [min_sub_sub_right, sub_add, sub_self, sub_zero]
    exact h
  wlog hab : a ≤ b generalizing a b
  · apply IntervalIntegrable.symm (this hf.symm ?_ ?_ (le_of_not_ge hab))
    · rw [min_comm]; exact h
    · rw [min_comm]; exact h'
  rw [intervalIntegrable_iff' h] at hf
  rw [intervalIntegrable_iff' h'] at ⊢
  have A : MeasurableEmbedding fun x => x + c :=
    (Homeomorph.addRight c).isClosedEmbedding.measurableEmbedding
  rw [← map_add_right_eq_self volume c] at hf
  convert! (MeasurableEmbedding.integrableOn_map_iff A).mp hf using 1
  rw [preimage_add_const_uIcc]
/-
**IntervalIntegrable.comp_add_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `IntervalInteg
rable`。
形式化陈述：comp_add_right_iff {c : Real} (h : ‖f (min a b + c)‖ₑ != ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `neg_add_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ -b + b = a
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `IntervalIntegrable.comp_add_right`：comp_add_right (hf : IntervalIntegrab
le f volume a b) (c : Real) (h : ‖f (min a b)‖ₑ != ∞
· 使用定理 `min_add_add_right`：∀ {α : Type u_1} [inst : LinearOrder α] [inst_1 : Add
 α] [AddRightMono α] (a b c : α), min (a + c) (b + c) = min a b + c
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
-/
theorem comp_add_right_iff {c : ℝ} (h : ‖f (min a b + c)‖ₑ ≠ ⊤ := by finiteness) :
    IntervalIntegrable (fun x ↦ f (x + c)) volume a b
      ↔ IntervalIntegrable f volume (a + c) (b + c) where
  mp hf := by simpa using hf.comp_add_right (-c)
  mpr hf := by
    have : ‖f (min (a + c) (b + c))‖ₑ ≠ ⊤ := by rwa [min_add_add_right]
    simpa using hf.comp_add_right c
/-
**IntervalIntegrable.comp_add_left** 是 Mathlib 中的一个定理，位于命名空间 `IntervalIntegrable
`。
形式化陈述：comp_add_left (hf : IntervalIntegrable f volume a b) (c : Real) (h : ‖f (m
in a b)‖ₑ != ∞
参数：hf : IntervalIntegrable f volume a b；c : Real。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `IntervalIntegrable.comp_add_right`：comp_add_right (hf : IntervalIntegrab
le f volume a b) (c : Real) (h : ‖f (min a b)‖ₑ != ∞
-/
theorem comp_add_left (hf : IntervalIntegrable f volume a b) (c : ℝ)
    (h : ‖f (min a b)‖ₑ ≠ ∞ := by finiteness) :
    IntervalIntegrable (fun x ↦ f (c + x)) volume (a - c) (b - c) := by
  simpa [add_comm] using IntervalIntegrable.comp_add_right hf c h
/-
**IntervalIntegrable.comp_add_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `IntervalIntegr
able`。
形式化陈述：comp_add_left_iff {c : Real} (h : ‖f (min a b)‖ₑ != ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `IntervalIntegrable.comp_add_right_iff`：comp_add_right_iff {c : Real} (h 
: ‖f (min a b + c)‖ₑ != ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem comp_add_left_iff {c : ℝ} (h : ‖f (min a b)‖ₑ ≠ ⊤ := by finiteness) :
    IntervalIntegrable (fun x ↦ f (c + x)) volume (a - c) (b - c)
      ↔ IntervalIntegrable f volume a b := by
  simp_rw [add_comm c]
  rw [IntervalIntegrable.comp_add_right_iff (by grind)]
  simp
/-
**IntervalIntegrable.comp_sub_right** 是 Mathlib 中的一个定理，位于命名空间 `IntervalIntegrabl
e`。
形式化陈述：comp_sub_right (hf : IntervalIntegrable f volume a b) (c : Real) (h : ‖f (
min a b)‖ₑ != ∞
参数：hf : IntervalIntegrable f volume a b；c : Real。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `IntervalIntegrable.comp_add_right`：comp_add_right (hf : IntervalIntegrab
le f volume a b) (c : Real) (h : ‖f (min a b)‖ₑ != ∞
-/
theorem comp_sub_right (hf : IntervalIntegrable f volume a b) (c : ℝ)
    (h : ‖f (min a b)‖ₑ ≠ ∞ := by finiteness) :
    IntervalIntegrable (fun x ↦ f (x - c)) volume (a + c) (b + c) := by
  simpa only [sub_neg_eq_add] using! IntervalIntegrable.comp_add_right hf (-c) h
/-
**IntervalIntegrable.comp_sub_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `IntervalInteg
rable`。
形式化陈述：comp_sub_right_iff {c : Real} (h : ‖f (min a b)‖ₑ != ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `IntervalIntegrable.comp_add_right_iff`：comp_add_right_iff {c : Real} (h 
: ‖f (min a b + c)‖ₑ != ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_neg_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b + -b = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem comp_sub_right_iff {c : ℝ} (h : ‖f (min a b)‖ₑ ≠ ⊤ := by finiteness) :
    IntervalIntegrable (fun x ↦ f (x - c)) volume (a + c) (b + c)
      ↔ IntervalIntegrable f volume a b := by
  simp_rw [sub_eq_add_neg]
  rw [IntervalIntegrable.comp_add_right_iff (by grind)]
  simp

-- TODO: generalise this lemma to enorms!
/-
**IntervalIntegrable.iff_comp_neg** 是 Mathlib 中的一个定理，位于命名空间 `IntervalIntegrable`
。
形式化陈述：iff_comp_neg {f : Real -> E} (h : ‖f (min a b)‖ₑ != ∞
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntervalIntegrable.comp_mul_left_iff`：comp_mul_left_iff {f : Real -> E} 
{c : Real} (hc : c != 0) (h : ‖f (min a b)‖ₑ != ∞
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_ne_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a ≠
 0 ↔ a ≠ 0
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `div_neg`：div_neg (a : R) : a / -b = -(a / b)
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem iff_comp_neg {f : ℝ → E} (h : ‖f (min a b)‖ₑ ≠ ∞ := by finiteness) :
    IntervalIntegrable f volume a b ↔ IntervalIntegrable (fun x ↦ f (-x)) volume (-a) (-b) := by
  rw [← comp_mul_left_iff (neg_ne_zero.2 one_ne_zero) h (by simp)]; simp [div_neg]

-- TODO: generalise this lemma to enorms!
/-
**IntervalIntegrable.comp_sub_left** 是 Mathlib 中的一个定理，位于命名空间 `IntervalIntegrable
`。
形式化陈述：comp_sub_left {f : Real -> E} (hf : IntervalIntegrable f volume a b) (c : 
Real) (h : ‖f (min a b)‖ₑ != ∞
参数：hf : IntervalIntegrable f volume a b；c : Real。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IntervalIntegrable.iff_comp_neg`：iff_comp_neg {f : Real -> E} (h : ‖f (m
in a b)‖ₑ != ∞
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `IntervalIntegrable.comp_add_left`：comp_add_left (hf : IntervalIntegrable
 f volume a b) (c : Real) (h : ‖f (min a b)‖ₑ != ∞
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
-/
theorem comp_sub_left {f : ℝ → E} (hf : IntervalIntegrable f volume a b) (c : ℝ)
    (h : ‖f (min a b)‖ₑ ≠ ∞ := by finiteness) :
    IntervalIntegrable (fun x ↦ f (c - x)) volume (c - a) (c - b) := by
  simpa only [neg_sub, ← sub_eq_add_neg] using (iff_comp_neg (by simp)).mp (hf.comp_add_left c h)

-- TODO: generalise this lemma to enorms!
/-
**IntervalIntegrable.comp_sub_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `IntervalIntegr
able`。
形式化陈述：comp_sub_left_iff {f : Real -> E} (c : Real) (h : ‖f (min a b)‖ₑ != ∞
参数：c : Real。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - 
(a - b) = b
· 使用定理 `IntervalIntegrable.comp_sub_left`：comp_sub_left {f : Real -> E} (hf : In
tervalIntegrable f volume a b) (c : Real) (h : ‖f (min a b)‖ₑ != ∞
· 使用引理 `enorm_ne_top`：enorm_ne_top : ‖x‖ₑ != ∞
-/
theorem comp_sub_left_iff {f : ℝ → E} (c : ℝ) (h : ‖f (min a b)‖ₑ ≠ ∞ := by finiteness) :
    IntervalIntegrable (fun x => f (c - x)) volume (c - a) (c - b) ↔
      IntervalIntegrable f volume a b :=
  ⟨fun h ↦ by simpa using h.comp_sub_left c, (.comp_sub_left · c h)⟩

end IntervalIntegrable

/-!
## Continuous functions are interval integrable
-/
section

variable {μ : Measure ℝ} [IsLocallyFiniteMeasure μ]

/-
**ContinuousOn.intervalIntegrable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.intervalIntegrable {u : Real -> E} {a b : Real} (hu : Continu
ousOn u (uIcc a b)) : IntervalIntegrable u μ a b
参数：hu : ContinuousOn u (uIcc a b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IntegrableOn.intervalIntegrable`：MeasureTheory.IntegrableO
n.intervalIntegrable (hf : IntegrableOn f [[a, b]] μ) : IntervalIntegrable f μ a
 b
· 使用定理 `ContinuousOn.integrableOn_Icc`：ContinuousOn.integrableOn_Icc [Preorder X
] [CompactIccSpace X] [T2Space X] (hf : ContinuousOn f (Icc a b)) : IntegrableOn
 f (Icc a b) μ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `MeasureTheory.Measure.Regular.toIsFiniteMeasureOnCompacts`：∀ {α : Type u
_1} {inst : MeasurableSpace α} {inst_1 : TopologicalSpace α} {μ : MeasureTheory.
Measure α}   [self : μ.Regular], MeasureTheory.…
· 使用定理 `MeasureTheory.Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMea
sure`：∀ {X : Type u_3} [inst : TopologicalSpace X] [TopologicalSpace.PseudoMetri
zableSpace X] [SigmaCompactSpace X]   [inst_3 : MeasurableSpace X]…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
-/
theorem ContinuousOn.intervalIntegrable {u : ℝ → E} {a b : ℝ} (hu : ContinuousOn u (uIcc a b)) :
    IntervalIntegrable u μ a b :=
  (ContinuousOn.integrableOn_Icc hu).intervalIntegrable
/-
**ContinuousOn.intervalIntegrable_of_Icc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.intervalIntegrable_of_Icc {u : Real -> E} {a b : Real} (h : a
 <= b) (hu : ContinuousOn u (Icc a b)) : IntervalIntegrable u μ a b
参数：h : a <= b；hu : ContinuousOn u (Icc a b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.intervalIntegrable`：ContinuousOn.intervalIntegrable {u : Re
al -> E} {a b : Real} (hu : ContinuousOn u (uIcc a b)) : IntervalIntegrable u μ 
a b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.uIcc_of_le`：uIcc_of_le (h : a <= b) : [[a, b]] = Icc a b
-/
theorem ContinuousOn.intervalIntegrable_of_Icc {u : ℝ → E} {a b : ℝ} (h : a ≤ b)
    (hu : ContinuousOn u (Icc a b)) : IntervalIntegrable u μ a b :=
  ContinuousOn.intervalIntegrable ((uIcc_of_le h).symm ▸ hu)

/-- A continuous function on `ℝ` is `IntervalIntegrable` with respect to any locally finite measure
`ν` on ℝ. -/
/-
**Continuous.intervalIntegrable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.intervalIntegrable {u : Real -> E} (hu : Continuous u) (a b : R
eal) : IntervalIntegrable u μ a b
参数：hu : Continuous u；a b : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.intervalIntegrable`：ContinuousOn.intervalIntegrable {u : Re
al -> E} {a b : Real} (hu : ContinuousOn u (uIcc a b)) : IntervalIntegrable u μ 
a b
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s

--- 原说明 ---
A continuous function on `ℝ` is `IntervalIntegrable` with respect to any locally
 finite measure
`ν` on ℝ.
-/
theorem Continuous.intervalIntegrable {u : ℝ → E} (hu : Continuous u) (a b : ℝ) :
    IntervalIntegrable u μ a b :=
  hu.continuousOn.intervalIntegrable

end

/-!
## Monotone and antitone functions are integral integrable
-/
section

variable {μ : Measure ℝ} [IsLocallyFiniteMeasure μ] [ConditionallyCompleteLinearOrder E]
  [OrderTopology E] [SecondCountableTopology E]

/-
**MonotoneOn.intervalIntegrable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonotoneOn.intervalIntegrable {u : Real -> E} {a b : Real} (hu : MonotoneO
n u (uIcc a b)) : IntervalIntegrable u μ a b
参数：hu : MonotoneOn u (uIcc a b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intervalIntegrable_iff`：intervalIntegrable_iff : IntervalIntegrable f μ 
a b ↔ IntegrableOn f (Ι a b) μ
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.IntegrableOn.mono_set`：∀ {α : Type u_1} {ε : Type u_3} {mα
 : MeasurableSpace α} {f : α → ε} {s t : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace …
· 使用定理 `MonotoneOn.integrableOn_isCompact`：MonotoneOn.integrableOn_isCompact [Is
FiniteMeasureOnCompacts μ] (hs : IsCompact s) (hmono : MonotoneOn f s) : Integra
bleOn f s μ
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `MeasureTheory.Measure.Regular.toIsFiniteMeasureOnCompacts`：∀ {α : Type u
_1} {inst : MeasurableSpace α} {inst_1 : TopologicalSpace α} {μ : MeasureTheory.
Measure α}   [self : μ.Regular], MeasureTheory.…
· 使用定理 `MeasureTheory.Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMea
sure`：∀ {X : Type u_3} [inst : TopologicalSpace X] [TopologicalSpace.PseudoMetri
zableSpace X] [SigmaCompactSpace X]   [inst_3 : MeasurableSpace X]…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `isCompact_uIcc`：isCompact_uIcc {α : Type*} [LinearOrder α] [TopologicalS
pace α] [CompactIccSpace α] {a b : α} : IsCompact (uIcc a b)
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `Set.Ioc_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc a b ⊆ Set.Icc a b
-/
theorem MonotoneOn.intervalIntegrable {u : ℝ → E} {a b : ℝ} (hu : MonotoneOn u (uIcc a b)) :
    IntervalIntegrable u μ a b := by
  rw [intervalIntegrable_iff]
  exact (hu.integrableOn_isCompact isCompact_uIcc).mono_set Ioc_subset_Icc_self

set_option backward.isDefEq.respectTransparency.types false in
/-
**AntitoneOn.intervalIntegrable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntitoneOn.intervalIntegrable {u : Real -> E} {a b : Real} (hu : AntitoneO
n u (uIcc a b)) : IntervalIntegrable u μ a b
参数：hu : AntitoneOn u (uIcc a b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonotoneOn.intervalIntegrable`：MonotoneOn.intervalIntegrable {u : Real -
> E} {a b : Real} (hu : MonotoneOn u (uIcc a b)) : IntervalIntegrable u μ a b
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `instSecondCountableTopologyOrderDual`：∀ {α : Type u} [inst : Topological
Space α] [h : SecondCountableTopology α], SecondCountableTopology αᵒᵈ
· 使用定理 `AntitoneOn.dual_right`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [
inst_1 : Preorder β] {f : α → β} {s : Set α},   AntitoneOn f s → MonotoneOn (⇑Or
derDual.toD…
-/
theorem AntitoneOn.intervalIntegrable {u : ℝ → E} {a b : ℝ} (hu : AntitoneOn u (uIcc a b)) :
    IntervalIntegrable u μ a b :=
  hu.dual_right.intervalIntegrable
/-
**Monotone.intervalIntegrable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.intervalIntegrable {u : Real -> E} {a b : Real} (hu : Monotone u)
 : IntervalIntegrable u μ a b
参数：hu : Monotone u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonotoneOn.intervalIntegrable`：MonotoneOn.intervalIntegrable {u : Real -
> E} {a b : Real} (hu : MonotoneOn u (uIcc a b)) : IntervalIntegrable u μ a b
· 使用定理 `Monotone.monotoneOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Monotone f → ∀ (s : Set α), MonotoneOn f s
-/
theorem Monotone.intervalIntegrable {u : ℝ → E} {a b : ℝ} (hu : Monotone u) :
    IntervalIntegrable u μ a b :=
  (hu.monotoneOn _).intervalIntegrable
/-
**Antitone.intervalIntegrable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antitone.intervalIntegrable {u : Real -> E} {a b : Real} (hu : Antitone u)
 : IntervalIntegrable u μ a b
参数：hu : Antitone u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntitoneOn.intervalIntegrable`：AntitoneOn.intervalIntegrable {u : Real -
> E} {a b : Real} (hu : AntitoneOn u (uIcc a b)) : IntervalIntegrable u μ a b
· 使用定理 `Antitone.antitoneOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Antitone f → ∀ (s : Set α), AntitoneOn f s
-/
theorem Antitone.intervalIntegrable {u : ℝ → E} {a b : ℝ} (hu : Antitone u) :
    IntervalIntegrable u μ a b :=
  (hu.antitoneOn _).intervalIntegrable

end

/-!
## Interval integrability of functions with even or odd parity
-/
section

variable {f : ℝ → E}

/-- An even function is interval integrable (with respect to the volume measure) on every interval
of the form `0..x` if it is interval integrable (with respect to the volume measure) on every
interval of the form `0..x`, for positive `x`.

See `intervalIntegrable_of_even` for a stronger result. -/
/-
**intervalIntegrable_of_even** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：intervalIntegrable_of_even (h₁f : forall x, f x = f (-x)) (h₂f : forall x,
 0 < x -> IntervalIntegrable f volume 0 x) {a b : Real} (ha : ‖f (min 0 a)‖ₑ != 
∞
参数：h₁f : forall x, f x = f (-x)；h₂f : forall x, 0 < x -> IntervalIntegrable f vo
lume 0 x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntervalIntegrable.trans`：trans {a b c : Real} (hab : IntervalIntegrable
 f μ a b) (hbc : IntervalIntegrable f μ b c) : IntervalIntegrable f μ a c
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `IntervalIntegrable.symm`：∀ {ε : Type u_3} [inst : TopologicalSpace ε] [i
nst_1 : ENormedAddMonoid ε] {f : ℝ → ε} {a b : ℝ}   {μ : MeasureTheory.Measure ℝ
}, IntervalIn…
· 使用引理 `intervalIntegrable_of_even₀`：intervalIntegrable_of_even₀ (h₁f : forall x
, f x = f (-x)) (h₂f : forall x, 0 < x -> IntervalIntegrable f volume 0 x) {t : 
Real} (ht : ‖f (m…

--- 原说明 ---
An even function is interval integrable (with respect to the volume measure) on 
every interval
of the form `0..x` if it is interval integrable (with respect to the volume meas
ure) on every
interval of the form `0..x`, for positive `x`.

See `intervalIntegrable_of_even` for a stronger result.
-/
lemma intervalIntegrable_of_even₀ (h₁f : ∀ x, f x = f (-x))
    (h₂f : ∀ x, 0 < x → IntervalIntegrable f volume 0 x)
    {t : ℝ} (ht : ‖f (min 0 t)‖ₑ ≠ ∞ := by finiteness) :
    IntervalIntegrable f volume 0 t := by
  rcases lt_trichotomy t 0 with h | h | h
  · rw [IntervalIntegrable.iff_comp_neg ht]
    conv => arg 1; intro t; rw [← h₁f]
    simp [h₂f (-t) (by simp [h])]
  · rw [h]
  · exact h₂f t h

/-- An even function is interval integrable (with respect to the volume measure) on every interval
if it is interval integrable (with respect to the volume measure) on every interval of the form
`0..x`, for positive `x`. -/
/-
**intervalIntegrable_of_even** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：intervalIntegrable_of_even (h₁f : forall x, f x = f (-x)) (h₂f : forall x,
 0 < x -> IntervalIntegrable f volume 0 x) {a b : Real} (ha : ‖f (min 0 a)‖ₑ != 
∞
参数：h₁f : forall x, f x = f (-x)；h₂f : forall x, 0 < x -> IntervalIntegrable f vo
lume 0 x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntervalIntegrable.trans`：trans {a b c : Real} (hab : IntervalIntegrable
 f μ a b) (hbc : IntervalIntegrable f μ b c) : IntervalIntegrable f μ a c
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `IntervalIntegrable.symm`：∀ {ε : Type u_3} [inst : TopologicalSpace ε] [i
nst_1 : ENormedAddMonoid ε] {f : ℝ → ε} {a b : ℝ}   {μ : MeasureTheory.Measure ℝ
}, IntervalIn…
· 使用引理 `intervalIntegrable_of_even₀`：intervalIntegrable_of_even₀ (h₁f : forall x
, f x = f (-x)) (h₂f : forall x, 0 < x -> IntervalIntegrable f volume 0 x) {t : 
Real} (ht : ‖f (m…

--- 原说明 ---
An even function is interval integrable (with respect to the volume measure) on 
every interval
if it is interval integrable (with respect to the volume measure) on every inter
val of the form
`0..x`, for positive `x`.
-/
theorem intervalIntegrable_of_even
    (h₁f : ∀ x, f x = f (-x)) (h₂f : ∀ x, 0 < x → IntervalIntegrable f volume 0 x) {a b : ℝ}
    (ha : ‖f (min 0 a)‖ₑ ≠ ∞ := by finiteness) (hb : ‖f (min 0 b)‖ₑ ≠ ∞ := by finiteness) :
    IntervalIntegrable f volume a b :=
  -- Split integral and apply lemma
  (intervalIntegrable_of_even₀ h₁f h₂f ha).symm.trans (b := 0)
    (intervalIntegrable_of_even₀ h₁f h₂f hb)

/-- An odd function is interval integrable (with respect to the volume measure) on every interval
of the form `0..x` if it is interval integrable (with respect to the volume measure) on every
interval of the form `0..x`, for positive `x`.

See `intervalIntegrable_of_odd` for a stronger result. -/
/-
**intervalIntegrable_of_odd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：intervalIntegrable_of_odd (h₁f : forall x, -f x = f (-x)) (h₂f : forall x,
 0 < x -> IntervalIntegrable f volume 0 x) {a b : Real} (ha : ‖f (min 0 a)‖ₑ != 
∞
参数：h₁f : forall x, -f x = f (-x)；h₂f : forall x, 0 < x -> IntervalIntegrable f v
olume 0 x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntervalIntegrable.trans`：trans {a b c : Real} (hab : IntervalIntegrable
 f μ a b) (hbc : IntervalIntegrable f μ b c) : IntervalIntegrable f μ a c
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `IntervalIntegrable.symm`：∀ {ε : Type u_3} [inst : TopologicalSpace ε] [i
nst_1 : ENormedAddMonoid ε] {f : ℝ → ε} {a b : ℝ}   {μ : MeasureTheory.Measure ℝ
}, IntervalIn…
· 使用引理 `intervalIntegrable_of_odd₀`：intervalIntegrable_of_odd₀ (h₁f : forall x, 
-f x = f (-x)) (h₂f : forall x, 0 < x -> IntervalIntegrable f volume 0 x) {t : R
eal} (ht : ‖f (m…

--- 原说明 ---
An odd function is interval integrable (with respect to the volume measure) on e
very interval
of the form `0..x` if it is interval integrable (with respect to the volume meas
ure) on every
interval of the form `0..x`, for positive `x`.

See `intervalIntegrable_of_odd` for a stronger result.
-/
lemma intervalIntegrable_of_odd₀ (h₁f : ∀ x, -f x = f (-x))
    (h₂f : ∀ x, 0 < x → IntervalIntegrable f volume 0 x) {t : ℝ}
    (ht : ‖f (min 0 t)‖ₑ ≠ ∞ := by finiteness) :
    IntervalIntegrable f volume 0 t := by
  rcases lt_trichotomy t 0 with h | h | h
  · rw [IntervalIntegrable.iff_comp_neg]
    conv => arg 1; intro t; rw [← h₁f]
    apply IntervalIntegrable.neg
    simp [h₂f (-t) (by simp [h])]
  · rw [h]
  · exact h₂f t h

/-- An odd function is interval integrable (with respect to the volume measure) on every interval
iff it is interval integrable (with respect to the volume measure) on every interval of the form
`0..x`, for positive `x`. -/
/-
**intervalIntegrable_of_odd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：intervalIntegrable_of_odd (h₁f : forall x, -f x = f (-x)) (h₂f : forall x,
 0 < x -> IntervalIntegrable f volume 0 x) {a b : Real} (ha : ‖f (min 0 a)‖ₑ != 
∞
参数：h₁f : forall x, -f x = f (-x)；h₂f : forall x, 0 < x -> IntervalIntegrable f v
olume 0 x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntervalIntegrable.trans`：trans {a b c : Real} (hab : IntervalIntegrable
 f μ a b) (hbc : IntervalIntegrable f μ b c) : IntervalIntegrable f μ a c
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `IntervalIntegrable.symm`：∀ {ε : Type u_3} [inst : TopologicalSpace ε] [i
nst_1 : ENormedAddMonoid ε] {f : ℝ → ε} {a b : ℝ}   {μ : MeasureTheory.Measure ℝ
}, IntervalIn…
· 使用引理 `intervalIntegrable_of_odd₀`：intervalIntegrable_of_odd₀ (h₁f : forall x, 
-f x = f (-x)) (h₂f : forall x, 0 < x -> IntervalIntegrable f volume 0 x) {t : R
eal} (ht : ‖f (m…

--- 原说明 ---
An odd function is interval integrable (with respect to the volume measure) on e
very interval
iff it is interval integrable (with respect to the volume measure) on every inte
rval of the form
`0..x`, for positive `x`.
-/
theorem intervalIntegrable_of_odd
    (h₁f : ∀ x, -f x = f (-x)) (h₂f : ∀ x, 0 < x → IntervalIntegrable f volume 0 x) {a b : ℝ}
    (ha : ‖f (min 0 a)‖ₑ ≠ ∞ := by finiteness) (hb : ‖f (min 0 b)‖ₑ ≠ ∞ := by finiteness) :
    IntervalIntegrable f volume a b :=
  -- Split integral and apply lemma
  (intervalIntegrable_of_odd₀ h₁f h₂f ha).symm.trans (intervalIntegrable_of_odd₀ h₁f h₂f hb)

end

/-!
## Limits of intervals
-/

/-- Let `l'` be a measurably generated filter; let `l` be a of filter such that each `s ∈ l'`
eventually includes `Ioc u v` as both `u` and `v` tend to `l`. Let `μ` be a measure finite at `l'`.

Suppose that `f : ℝ → E` has a finite limit at `l' ⊓ ae μ`. Then `f` is interval integrable on
`u..v` provided that both `u` and `v` tend to `l`.

Typeclass instances allow Lean to find `l'` based on `l` but not vice versa, so
`apply Tendsto.eventually_intervalIntegrable_ae` will generate goals `Filter ℝ` and
`TendstoIxxClass Ioc ?m_1 l'`. -/
/-
**Filter.Tendsto.eventually_intervalIntegrable_ae** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.eventually_intervalIntegrable_ae {f : Real -> E} {μ : Measu
re Real} {l l' : Filter Real} (hfm : StronglyMeasurableAtFilter f l' μ) [Tendsto
IxxClass Ioc l l'] [IsMeasurablyGenerated l'] (hμ : μ.FiniteAtFilter l') {c : E}
 (hf : Tendsto f (l' ⊓ ae μ) (𝓝 c)) {u v : ι -> Real} {lt : Filter ι} (hu : Tend
sto u lt l) (hv : Tendsto v lt l) : forallᶠ t in lt, IntervalIntegrable f μ (u t
) (v t)
参数：hfm : StronglyMeasurableAtFilter f l' μ；hμ : μ.FiniteAtFilter l'；hf : Tendsto
 f (l' ⊓ ae μ) (𝓝 c)；hu : Tendsto u lt l；hv : Tendsto v lt l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.IntegrableAtFilter.eventually`：∀ {α : Type u_1} {ε : Type 
u_3} {mα : MeasurableSpace α} {f : α → ε} {μ : MeasureTheory.Measure α}   [inst 
: TopologicalSpace ε] [inst_1 : C…
· 使用定理 `Filter.Tendsto.integrableAtFilter_ae`：∀ {α : Type u_1} {E : Type u_5} {m
α : MeasurableSpace α} [inst : NormedAddCommGroup E] {μ : MeasureTheory.Measure 
α}   {f : α → E} {l : Filt…
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `Filter.Tendsto.Ioc`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] 
{l₁ l₂ : Filter α} [Filter.TendstoIxxClass Set.Ioc l₁ l₂]   {lb : Filter β} {u₁ 
u₂ : β →…

--- 原说明 ---
Let `l'` be a measurably generated filter; let `l` be a of filter such that each
 `s ∈ l'`
eventually includes `Ioc u v` as both `u` and `v` tend to `l`. Let `μ` be a meas
ure finite at `l'`.

Suppose that `f : ℝ → E` has a finite limit at `l' ⊓ ae μ`. Then `f` is interval
 integrable on
`u..v` provided that both `u` and `v` tend to `l`.

Typeclass instances allow Lean to find `l'` based on `l` but not vice versa, so
`apply Tendsto.eventually_intervalIntegrable_ae` will generate goals `Filter ℝ` 
and
`TendstoIxxClass Ioc ?m_1 l'`.
-/
theorem Filter.Tendsto.eventually_intervalIntegrable_ae {f : ℝ → E} {μ : Measure ℝ}
    {l l' : Filter ℝ} (hfm : StronglyMeasurableAtFilter f l' μ) [TendstoIxxClass Ioc l l']
    [IsMeasurablyGenerated l'] (hμ : μ.FiniteAtFilter l') {c : E} (hf : Tendsto f (l' ⊓ ae μ) (𝓝 c))
    {u v : ι → ℝ} {lt : Filter ι} (hu : Tendsto u lt l) (hv : Tendsto v lt l) :
    ∀ᶠ t in lt, IntervalIntegrable f μ (u t) (v t) :=
  have := (hf.integrableAtFilter_ae hfm hμ).eventually
  ((hu.Ioc hv).eventually this).and <| (hv.Ioc hu).eventually this

/-- Let `l'` be a measurably generated filter; let `l` be a of filter such that each `s ∈ l'`
eventually includes `Ioc u v` as both `u` and `v` tend to `l`. Let `μ` be a measure finite at `l'`.

Suppose that `f : ℝ → E` has a finite limit at `l`. Then `f` is interval integrable on `u..v`
provided that both `u` and `v` tend to `l`.

Typeclass instances allow Lean to find `l'` based on `l` but not vice versa, so
`apply Tendsto.eventually_intervalIntegrable` will generate goals `Filter ℝ` and
`TendstoIxxClass Ioc ?m_1 l'`. -/
/-
**Filter.Tendsto.eventually_intervalIntegrable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.eventually_intervalIntegrable {f : Real -> E} {μ : Measure 
Real} {l l' : Filter Real} (hfm : StronglyMeasurableAtFilter f l' μ) [TendstoIxx
Class Ioc l l'] [IsMeasurablyGenerated l'] (hμ : μ.FiniteAtFilter l') {c : E} (h
f : Tendsto f l' (𝓝 c)) {u v : ι -> Real} {lt : Filter ι} (hu : Tendsto u lt l) 
(hv : Tendsto v lt l) : forallᶠ t in lt, IntervalIntegrable f μ (u t) (v t)
参数：hfm : StronglyMeasurableAtFilter f l' μ；hμ : μ.FiniteAtFilter l'；hf : Tendsto
 f l' (𝓝 c)；hu : Tendsto u lt l；hv : Tendsto v lt l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.eventually_intervalIntegrable_ae`：Filter.Tendsto.eventual
ly_intervalIntegrable_ae {f : Real -> E} {μ : Measure Real} {l l' : Filter Real}
 (hfm : StronglyMeasurableAtFilter f …
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a

--- 原说明 ---
Let `l'` be a measurably generated filter; let `l` be a of filter such that each
 `s ∈ l'`
eventually includes `Ioc u v` as both `u` and `v` tend to `l`. Let `μ` be a meas
ure finite at `l'`.

Suppose that `f : ℝ → E` has a finite limit at `l`. Then `f` is interval integra
ble on `u..v`
provided that both `u` and `v` tend to `l`.

Typeclass instances allow Lean to find `l'` based on `l` but not vice versa, so
`apply Tendsto.eventually_intervalIntegrable` will generate goals `Filter ℝ` and
`TendstoIxxClass Ioc ?m_1 l'`.
-/
theorem Filter.Tendsto.eventually_intervalIntegrable {f : ℝ → E} {μ : Measure ℝ} {l l' : Filter ℝ}
    (hfm : StronglyMeasurableAtFilter f l' μ) [TendstoIxxClass Ioc l l'] [IsMeasurablyGenerated l']
    (hμ : μ.FiniteAtFilter l') {c : E} (hf : Tendsto f l' (𝓝 c)) {u v : ι → ℝ} {lt : Filter ι}
    (hu : Tendsto u lt l) (hv : Tendsto v lt l) : ∀ᶠ t in lt, IntervalIntegrable f μ (u t) (v t) :=
  (hf.mono_left inf_le_left).eventually_intervalIntegrable_ae hfm hμ hu hv

/-!
### Interval integral: definition and basic properties

In this section we define `∫ x in a..b, f x ∂μ` as `∫ x in Ioc a b, f x ∂μ - ∫ x in Ioc b a, f x ∂μ`
and prove some basic properties.
-/

variable [NormedSpace ℝ E]

/-- The interval integral `∫ x in a..b, f x ∂μ` is defined
as `∫ x in Ioc a b, f x ∂μ - ∫ x in Ioc b a, f x ∂μ`. If `a ≤ b`, then it equals
`∫ x in Ioc a b, f x ∂μ`, otherwise it equals `-∫ x in Ioc b a, f x ∂μ`. -/
/-
**intervalIntegral** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：intervalIntegral (f : Real -> E) (a b : Real) (μ : Measure Real) : E
参数：f : Real -> E；a b : Real；μ : Measure Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The interval integral `∫ x in a..b, f x ∂μ` is defined
as `∫ x in Ioc a b, f x ∂μ - ∫ x in Ioc b a, f x ∂μ`. If `a ≤ b`, then it equals
`∫ x in Ioc a b, f x ∂μ`, otherwise it equals `-∫ x in Ioc b a, f x ∂μ`.
-/
def intervalIntegral (f : ℝ → E) (a b : ℝ) (μ : Measure ℝ) : E :=
  (∫ x in Ioc a b, f x ∂μ) - ∫ x in Ioc b a, f x ∂μ

@[inherit_doc intervalIntegral]
notation3"∫ "(...)" in "a".."b", "r:60:(scoped f => f)" ∂"μ:70 => intervalIntegral r a b μ

/-- The interval integral `∫ x in a..b, f x` is defined
as `∫ x in Ioc a b, f x - ∫ x in Ioc b a, f x`. If `a ≤ b`, then it equals
`∫ x in Ioc a b, f x`, otherwise it equals `-∫ x in Ioc b a, f x`. -/
notation3"∫ "(...)" in "a".."b", "r:60:(scoped f => intervalIntegral f a b volume) => r

namespace intervalIntegral

section Basic

variable {a b : ℝ} {f g : ℝ → E} {μ : Measure ℝ}

@[simp]
/-
**intervalIntegral.integral_zero** 是 Mathlib 中的一个定理，位于命名空间 `intervalIntegral`。
形式化陈述：integral_zero : (∫ _ in a..b, (0 : E) ∂μ) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.integral_zero`：integral_zero : ∫ _ : α, (0 : G) ∂μ = 0
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integral_zero : (∫ _ in a..b, (0 : E) ∂μ) = 0 := by simp [intervalIntegral]
/-
**intervalIntegral.integral_of_le** 是 Mathlib 中的一个定理，位于命名空间 `intervalIntegral`。
形式化陈述：integral_of_le (h : a <= b) : ∫ x in a..b, f x ∂μ = ∫ x in Ioc a b, f x ∂μ
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Ioc_eq_empty`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, ¬b < a
 → Set.Ioc b a = ∅
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MeasureTheory.Measure.restrict_empty`：restrict_empty : μ.restrict ∅ = 0
· 使用定理 `MeasureTheory.integral_zero_measure`：integral_zero_measure {m : Measurab
leSpace α} (f : α -> G) : (∫ x, f x ∂(0 : Measure α)) = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integral_of_le (h : a ≤ b) : ∫ x in a..b, f x ∂μ = ∫ x in Ioc a b, f x ∂μ := by
  simp [intervalIntegral, h]

@[simp]
/-
**intervalIntegral.integral_same** 是 Mathlib 中的一个定理，位于命名空间 `intervalIntegral`。
形式化陈述：integral_same : ∫ x in a..a, f x ∂μ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
-/
theorem integral_same : ∫ x in a..a, f x ∂μ = 0 :=
  sub_self _
/-
**intervalIntegral.integral_symm** 是 Mathlib 中的一个定理，位于命名空间 `intervalIntegral`。
形式化陈述：integral_symm (a b) : ∫ x in b..a, f x ∂μ = -∫ x in a..b, f x ∂μ
参数：a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integral_symm (a b) : ∫ x in b..a, f x ∂μ = -∫ x in a..b, f x ∂μ := by
  simp only [intervalIntegral, neg_sub]
/-
**intervalIntegral.integral_of_ge** 是 Mathlib 中的一个定理，位于命名空间 `intervalIntegral`。
形式化陈述：integral_of_ge (h : b <= a) : ∫ x in a..b, f x ∂μ = -∫ x in Ioc b a, f x ∂
μ
参数：h : b <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intervalIntegral.integral_symm`：integral_symm (a b) : ∫ x in b..a, f x ∂
μ = -∫ x in a..b, f x ∂μ
· 使用定理 `intervalIntegral.integral_of_le`：integral_of_le (h : a <= b) : ∫ x in a.
.b, f x ∂μ = ∫ x in Ioc a b, f x ∂μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integral_of_ge (h : b ≤ a) : ∫ x in a..b, f x ∂μ = -∫ x in Ioc b a, f x ∂μ := by
  simp only [integral_symm b, integral_of_le h]
/-
**intervalIntegral.intervalIntegral_eq_integral_uIoc** 是 Mathlib 中的一个定理，位于命名空间 `
intervalIntegral`。
形式化陈述：intervalIntegral_eq_integral_uIoc (f : Real -> E) (a b : Real) (μ : Measur
e Real) : ∫ x in a..b, f x ∂μ = (if a <= b then 1 else -1 : Real) • ∫ x in Ι a b
, f x ∂μ
参数：f : Real -> E；a b : Real；μ : Measure Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `intervalIntegral.integral_of_le`：integral_of_le (h : a <= b) : ∫ x in a.
.b, f x ∂μ = ∫ x in Ioc a b, f x ∂μ
· 使用定理 `Set.uIoc_of_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b
 → Set.uIoc a b = Set.Ioc a b
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `intervalIntegral.integral_of_ge`：integral_of_ge (h : b <= a) : ∫ x in a.
.b, f x ∂μ = -∫ x in Ioc b a, f x ∂μ
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `Set.uIoc_of_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a
 → Set.uIoc a b = Set.Ioc b a
· 使用定理 `neg_one_smul`：neg_one_smul (x : M) : (-1 : R) • x = -x
-/
theorem intervalIntegral_eq_integral_uIoc (f : ℝ → E) (a b : ℝ) (μ : Measure ℝ) :
    ∫ x in a..b, f x ∂μ = (if a ≤ b then 1 else -1 : ℝ) • ∫ x in Ι a b, f x ∂μ := by
  split_ifs with h
  · simp only [integral_of_le h, uIoc_of_le h, one_smul]
  · simp only [integral_of_ge (not_le.1 h).le, uIoc_of_ge (not_le.1 h).le, neg_one_smul]
/-
**intervalIntegral.norm_intervalIntegral_eq** 是 Mathlib 中的一个定理，位于命名空间 `intervalI
ntegral`。
形式化陈述：norm_intervalIntegral_eq (f : Real -> E) (a b : Real) (μ : Measure Real) :
 ‖∫ x in a..b, f x ∂μ‖ = ‖∫ x in Ι a b, f x ∂μ‖
参数：f : Real -> E；a b : Real；μ : Measure Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intervalIntegral.intervalIntegral_eq_integral_uIoc`：intervalIntegral_eq_
integral_uIoc (f : Real -> E) (a b : Real) (μ : Measure Real) : ∫ x in a..b, f x
 ∂μ = (if a <= b then 1 else -1 : Real) …
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
-/
theorem norm_intervalIntegral_eq (f : ℝ → E) (a b : ℝ) (μ : Measure ℝ) :
    ‖∫ x in a..b, f x ∂μ‖ = ‖∫ x in Ι a b, f x ∂μ‖ := by
  simp_rw [intervalIntegral_eq_integral_uIoc, norm_smul]
  split_ifs <;> simp only [norm_neg, norm_one, one_mul]
/-
**intervalIntegral.abs_intervalIntegral_eq** 是 Mathlib 中的一个定理，位于命名空间 `intervalIn
tegral`。
形式化陈述：abs_intervalIntegral_eq (f : Real -> Real) (a b : Real) (μ : Measure Real)
 : |∫ x in a..b, f x ∂μ| = |∫ x in Ι a b, f x ∂μ|
参数：f : Real -> Real；a b : Real；μ : Measure Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `intervalIntegral.norm_intervalIntegral_eq`：norm_intervalIntegral_eq (f :
 Real -> E) (a b : Real) (μ : Measure Real) : ‖∫ x in a..b, f x ∂μ‖ = ‖∫ x in Ι 
a b, f x ∂μ‖
-/
theorem abs_intervalIntegral_eq (f : ℝ → ℝ) (a b : ℝ) (μ : Measure ℝ) :
    |∫ x in a..b, f x ∂μ| = |∫ x in Ι a b, f x ∂μ| :=
  norm_intervalIntegral_eq f a b μ
/-
**intervalIntegral.integral_cases** 是 Mathlib 中的一个定理，位于命名空间 `intervalIntegral`。
形式化陈述：integral_cases (f : Real -> E) (a b) : (∫ x in a..b, f x ∂μ) in ({∫ x in Ι
 a b, f x ∂μ, -∫ x in Ι a b, f x ∂μ} : Set E)
参数：f : Real -> E；a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intervalIntegral.intervalIntegral_eq_integral_uIoc`：intervalIntegral_eq_
integral_uIoc (f : Real -> E) (a b : Real) (μ : Measure Real) : ∫ x in a..b, f x
 ∂μ = (if a <= b then 1 else -1 : Real) …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
theorem integral_cases (f : ℝ → E) (a b) :
    (∫ x in a..b, f x ∂μ) ∈ ({∫ x in Ι a b, f x ∂μ, -∫ x in Ι a b, f x ∂μ} : Set E) := by
  rw [intervalIntegral_eq_integral_uIoc]; split_ifs <;> simp

nonrec theorem integral_undef (h : ¬IntervalIntegrable f μ a b) : ∫ x in a..b, f x ∂μ = 0 := by
  rw [intervalIntegrable_iff] at h
  rw [intervalIntegral_eq_integral_uIoc, integral_undef h, smul_zero]
/-
**intervalIntegral.intervalIntegrable_of_integral_ne_zero** 是 Mathlib 中的一个定理，位于命
名空间 `intervalIntegral`。
形式化陈述：intervalIntegrable_of_integral_ne_zero {a b : Real} {f : Real -> E} {μ : M
easure Real} (h : (∫ x in a..b, f x ∂μ) != 0) : IntervalIntegrable f μ a b
参数：h : (∫ x in a..b, f x ∂μ) != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_imp_comm`：not_imp_comm : ¬a -> b ↔ ¬b -> a
· 使用定理 `intervalIntegral.integral_undef`：∀ {E : Type u_5} [inst : NormedAddCommG
roup E] [inst_1 : NormedSpace ℝ E] {a b : ℝ} {f : ℝ → E}   {μ : MeasureTheory.Me
asure ℝ}, ¬IntervalIn…
-/
theorem intervalIntegrable_of_integral_ne_zero {a b : ℝ} {f : ℝ → E} {μ : Measure ℝ}
    (h : (∫ x in a..b, f x ∂μ) ≠ 0) : IntervalIntegrable f μ a b :=
  not_imp_comm.1 integral_undef h

nonrec theorem integral_non_aestronglyMeasurable
    (hf : ¬AEStronglyMeasurable f (μ.restrict (Ι a b))) :
    ∫ x in a..b, f x ∂μ = 0 := by
  rw [intervalIntegral_eq_integral_uIoc, integral_non_aestronglyMeasurable hf, smul_zero]
/-
**intervalIntegral.integral_non_aestronglyMeasurable_of_le** 是 Mathlib 中的一个定理，位于
命名空间 `intervalIntegral`。
形式化陈述：integral_non_aestronglyMeasurable_of_le (h : a <= b) (hf : ¬AEStronglyMeas
urable f (μ.restrict (Ioc a b))) : ∫ x in a..b, f x ∂μ = 0
参数：h : a <= b；hf : ¬AEStronglyMeasurable f (μ.restrict (Ioc a b))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `intervalIntegral.integral_non_aestronglyMeasurable`：∀ {E : Type u_5} [in
st : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {a b : ℝ} {f : ℝ → E}   {μ
 : MeasureTheory.Measure ℝ},   ¬MeasureT…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.uIoc_of_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b
 → Set.uIoc a b = Set.Ioc a b
-/
theorem integral_non_aestronglyMeasurable_of_le (h : a ≤ b)
    (hf : ¬AEStronglyMeasurable f (μ.restrict (Ioc a b))) : ∫ x in a..b, f x ∂μ = 0 :=
  integral_non_aestronglyMeasurable <| by rwa [uIoc_of_le h]
/-
**intervalIntegral.norm_integral_min_max** 是 Mathlib 中的一个定理，位于命名空间 `intervalInte
gral`。
形式化陈述：norm_integral_min_max (f : Real -> E) : ‖∫ x in min a b..max a b, f x ∂μ‖ 
= ‖∫ x in a..b, f x ∂μ‖
参数：f : Real -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `intervalIntegral.integral_symm`：integral_symm (a b) : ∫ x in b..a, f x ∂
μ = -∫ x in a..b, f x ∂μ
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
-/
theorem norm_integral_min_max (f : ℝ → E) :
    ‖∫ x in min a b..max a b, f x ∂μ‖ = ‖∫ x in a..b, f x ∂μ‖ := by
  cases le_total a b <;> simp [*, integral_symm a b]
/-
**intervalIntegral.norm_integral_eq_norm_integral_uIoc** 是 Mathlib 中的一个定理，位于命名空间
 `intervalIntegral`。
形式化陈述：norm_integral_eq_norm_integral_uIoc (f : Real -> E) : ‖∫ x in a..b, f x ∂μ
‖ = ‖∫ x in Ι a b, f x ∂μ‖
参数：f : Real -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `intervalIntegral.norm_integral_min_max`：norm_integral_min_max (f : Real 
-> E) : ‖∫ x in min a b..max a b, f x ∂μ‖ = ‖∫ x in a..b, f x ∂μ‖
· 使用定理 `intervalIntegral.integral_of_le`：integral_of_le (h : a <= b) : ∫ x in a.
.b, f x ∂μ = ∫ x in Ioc a b, f x ∂μ
· 使用定理 `min_le_max`：min_le_max : min a b <= max a b
· 使用定理 `Set.uIoc.eq_1`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), Set.uI
oc a b = Set.Ioc (min a b) (max a b)
-/
theorem norm_integral_eq_norm_integral_uIoc (f : ℝ → E) :
    ‖∫ x in a..b, f x ∂μ‖ = ‖∫ x in Ι a b, f x ∂μ‖ := by
  rw [← norm_integral_min_max, integral_of_le min_le_max, uIoc]
/-
**intervalIntegral.abs_integral_eq_abs_integral_uIoc** 是 Mathlib 中的一个定理，位于命名空间 `
intervalIntegral`。
形式化陈述：abs_integral_eq_abs_integral_uIoc (f : Real -> Real) : |∫ x in a..b, f x ∂
μ| = |∫ x in Ι a b, f x ∂μ|
参数：f : Real -> Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `intervalIntegral.norm_integral_eq_norm_integral_uIoc`：norm_integral_eq_n
orm_integral_uIoc (f : Real -> E) : ‖∫ x in a..b, f x ∂μ‖ = ‖∫ x in Ι a b, f x ∂
μ‖
-/
theorem abs_integral_eq_abs_integral_uIoc (f : ℝ → ℝ) :
    |∫ x in a..b, f x ∂μ| = |∫ x in Ι a b, f x ∂μ| :=
  norm_integral_eq_norm_integral_uIoc f
/-
**intervalIntegral.norm_integral_le_integral_norm_uIoc** 是 Mathlib 中的一个定理，位于命名空间
 `intervalIntegral`。
形式化陈述：norm_integral_le_integral_norm_uIoc : ‖∫ x in a..b, f x ∂μ‖ <= ∫ x in Ι a 
b, ‖f x‖ ∂μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `intervalIntegral.norm_integral_eq_norm_integral_uIoc`：norm_integral_eq_n
orm_integral_uIoc (f : Real -> E) : ‖∫ x in a..b, f x ∂μ‖ = ‖∫ x in Ι a b, f x ∂
μ‖
· 使用定理 `MeasureTheory.norm_integral_le_integral_norm`：norm_integral_le_integral_
norm (f : α -> G) : ‖∫ a, f a ∂μ‖ <= ∫ a, ‖f a‖ ∂μ
-/
theorem norm_integral_le_integral_norm_uIoc : ‖∫ x in a..b, f x ∂μ‖ ≤ ∫ x in Ι a b, ‖f x‖ ∂μ :=
  calc
    ‖∫ x in a..b, f x ∂μ‖ = ‖∫ x in Ι a b, f x ∂μ‖ := norm_integral_eq_norm_integral_uIoc f
    _ ≤ ∫ x in Ι a b, ‖f x‖ ∂μ := norm_integral_le_integral_norm f
/-
**intervalIntegral.norm_integral_le_abs_integral_norm** 是 Mathlib 中的一个定理，位于命名空间 
`intervalIntegral`。
形式化陈述：norm_integral_le_abs_integral_norm : ‖∫ x in a..b, f x ∂μ‖ <= |∫ x in a..b
, ‖f x‖ ∂μ|
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intervalIntegral.norm_integral_eq_norm_integral_uIoc`：norm_integral_eq_n
orm_integral_uIoc (f : Real -> E) : ‖∫ x in a..b, f x ∂μ‖ = ‖∫ x in Ι a b, f x ∂
μ‖
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `MeasureTheory.norm_integral_le_integral_norm`：norm_integral_le_integral_
norm (f : α -> G) : ‖∫ a, f a ∂μ‖ <= ∫ a, ‖f a‖ ∂μ
· 使用定理 `le_abs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (
a : α), a ≤ |a|
-/
theorem norm_integral_le_abs_integral_norm : ‖∫ x in a..b, f x ∂μ‖ ≤ |∫ x in a..b, ‖f x‖ ∂μ| := by
  simp only [← Real.norm_eq_abs, norm_integral_eq_norm_integral_uIoc]
  exact le_trans (norm_integral_le_integral_norm _) (le_abs_self _)
/-
**intervalIntegral.norm_integral_le_integral_norm** 是 Mathlib 中的一个定理，位于命名空间 `int
ervalIntegral`。
形式化陈述：norm_integral_le_integral_norm (h : a <= b) : ‖∫ x in a..b, f x ∂μ‖ <= ∫ x
 in a..b, ‖f x‖ ∂μ
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `intervalIntegral.norm_integral_le_integral_norm_uIoc`：norm_integral_le_i
ntegral_norm_uIoc : ‖∫ x in a..b, f x ∂μ‖ <= ∫ x in Ι a b, ‖f x‖ ∂μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.uIoc_of_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b
 → Set.uIoc a b = Set.Ioc a b
· 使用定理 `intervalIntegral.integral_of_le`：integral_of_le (h : a <= b) : ∫ x in a.
.b, f x ∂μ = ∫ x in Ioc a b, f x ∂μ
-/
theorem norm_integral_le_integral_norm (h : a ≤ b) :
    ‖∫ x in a..b, f x ∂μ‖ ≤ ∫ x in a..b, ‖f x‖ ∂μ :=
  norm_integral_le_integral_norm_uIoc.trans_eq <| by rw [uIoc_of_le h, integral_of_le h]
/-
**intervalIntegral.norm_integral_le_abs_of_norm_le** 是 Mathlib 中的一个定理，位于命名空间 `in
tervalIntegral`。
形式化陈述：norm_integral_le_abs_of_norm_le {g : Real -> Real} (h : forallᵐ t ∂μ.restr
ict <| Ι a b, ‖f t‖ <= g t) (hbound : IntervalIntegrable g μ a b) : ‖∫ t in a..b
, f t ∂μ‖ <= |∫ t in a..b, g t ∂μ|
参数：h : forallᵐ t ∂μ.restrict <| Ι a b, ‖f t‖ <= g t；hbound : IntervalIntegrable 
g μ a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intervalIntegral.norm_intervalIntegral_eq`：norm_intervalIntegral_eq (f :
 Real -> E) (a b : Real) (μ : Measure Real) : ‖∫ x in a..b, f x ∂μ‖ = ‖∫ x in Ι 
a b, f x ∂μ‖
· 使用定理 `intervalIntegral.abs_intervalIntegral_eq`：abs_intervalIntegral_eq (f : R
eal -> Real) (a b : Real) (μ : Measure Real) : |∫ x in a..b, f x ∂μ| = |∫ x in Ι
 a b, f x ∂μ|
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.norm_integral_le_of_norm_le`：norm_integral_le_of_norm_le {
f : α -> G} {g : α -> Real} (hg : Integrable g μ) (h : forallᵐ x ∂μ, ‖f x‖ <= g 
x) : ‖∫ x, f x ∂μ‖ <= ∫ x, g x …
· 使用定理 `IntervalIntegrable.def'`：IntervalIntegrable.def' (h : IntervalIntegrable
 f μ a b) : IntegrableOn f (Ι a b) μ
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `le_abs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (
a : α), a ≤ |a|
-/
theorem norm_integral_le_abs_of_norm_le {g : ℝ → ℝ} (h : ∀ᵐ t ∂μ.restrict <| Ι a b, ‖f t‖ ≤ g t)
    (hbound : IntervalIntegrable g μ a b) : ‖∫ t in a..b, f t ∂μ‖ ≤ |∫ t in a..b, g t ∂μ| := by
  rw [norm_intervalIntegral_eq, abs_intervalIntegral_eq]
  exact (norm_integral_le_of_norm_le hbound.def' h).trans (le_abs_self _)
/-
**intervalIntegral.norm_integral_le_of_norm_le** 是 Mathlib 中的一个定理，位于命名空间 `interv
alIntegral`。
形式化陈述：norm_integral_le_of_norm_le {g : Real -> Real} (hab : a <= b) (h : forallᵐ
 t ∂μ, t in Set.Ioc a b -> ‖f t‖ <= g t) (hbound : IntervalIntegrable g μ a b) :
 ‖∫ t in a..b, f t ∂μ‖ <= ∫ t in a..b, g t ∂μ
参数：hab : a <= b；h : forallᵐ t ∂μ, t in Set.Ioc a b -> ‖f t‖ <= g t；hbound : Inte
rvalIntegrable g μ a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intervalIntegral.integral_of_le`：integral_of_le (h : a <= b) : ∫ x in a.
.b, f x ∂μ = ∫ x in Ioc a b, f x ∂μ
· 使用定理 `MeasureTheory.norm_integral_le_of_norm_le`：norm_integral_le_of_norm_le {
f : α -> G} {g : α -> Real} (hg : Integrable g μ) (h : forallᵐ x ∂μ, ‖f x‖ <= g 
x) : ‖∫ x, f x ∂μ‖ <= ∫ x, g x …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.ae_restrict_iff'`：ae_restrict_iff'₀ {p : α -> Prop} (hs : 
NullMeasurableSet s μ) : (forallᵐ x ∂μ.restrict s, p x) ↔ forallᵐ x ∂μ, x in s -
> p x
· 使用定理 `measurableSet_Ioc`：measurableSet_Ioc [ClosedIicTopology α] : MeasurableS
et (Ioc a b)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
-/
theorem norm_integral_le_of_norm_le {g : ℝ → ℝ} (hab : a ≤ b)
    (h : ∀ᵐ t ∂μ, t ∈ Set.Ioc a b → ‖f t‖ ≤ g t) (hbound : IntervalIntegrable g μ a b) :
    ‖∫ t in a..b, f t ∂μ‖ ≤ ∫ t in a..b, g t ∂μ := by
  simp only [integral_of_le hab, ← ae_restrict_iff' measurableSet_Ioc] at *
  exact MeasureTheory.norm_integral_le_of_norm_le hbound.1 h
/-
**intervalIntegral.norm_integral_le_of_norm_le_const_ae** 是 Mathlib 中的一个定理，位于命名空
间 `intervalIntegral`。
形式化陈述：norm_integral_le_of_norm_le_const_ae {a b C : Real} {f : Real -> E} (h : f
orallᵐ x, x in Ι a b -> ‖f x‖ <= C) : ‖∫ x in a..b, f x‖ <= C * |b - a|
参数：h : forallᵐ x, x in Ι a b -> ‖f x‖ <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intervalIntegral.norm_integral_eq_norm_integral_uIoc`：norm_integral_eq_n
orm_integral_uIoc (f : Real -> E) : ‖∫ x in a..b, f x ∂μ‖ = ‖∫ x in Ι a b, f x ∂
μ‖
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.uIoc.eq_1`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), Set.uI
oc a b = Set.Ioc (min a b) (max a b)
· 使用定理 `Real.volume_real_Ioc_of_le`：volume_real_Ioc_of_le {a b : Real} (hab : a 
<= b) : volume.real (Ioc a b) = b - a
· 使用定理 `inf_le_sup`：inf_le_sup : a ⊓ b <= a ⊔ b
· 使用定理 `max_sub_min_eq_abs`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : Linea
rOrder α] [AddLeftMono α] [AddRightMono α] (a b : α),   max a b - min a b = |b -
 a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `MeasureTheory.norm_setIntegral_le_of_norm_le_const_ae'`：norm_setIntegral
_le_of_norm_le_const_ae' {C : Real} (hs : μ s < ∞) (hC : forallᵐ x ∂μ, x in s ->
 ‖f x‖ <= C) : ‖∫ x in s, f x ∂μ‖ <= C * μ.r…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Real.volume_Ioc`：volume_Ioc {a b : Real} : volume (Ioc a b) = ofReal (b 
- a)
-/
theorem norm_integral_le_of_norm_le_const_ae {a b C : ℝ} {f : ℝ → E}
    (h : ∀ᵐ x, x ∈ Ι a b → ‖f x‖ ≤ C) : ‖∫ x in a..b, f x‖ ≤ C * |b - a| := by
  rw [norm_integral_eq_norm_integral_uIoc]
  convert! norm_setIntegral_le_of_norm_le_const_ae' _ h using 1
  · rw [uIoc, Real.volume_real_Ioc_of_le inf_le_sup, max_sub_min_eq_abs]
  · simp [uIoc, Real.volume_Ioc]
/-
**intervalIntegral.norm_integral_le_of_norm_le_const** 是 Mathlib 中的一个定理，位于命名空间 `
intervalIntegral`。
形式化陈述：norm_integral_le_of_norm_le_const {a b C : Real} {f : Real -> E} (h : fora
ll x in Ι a b, ‖f x‖ <= C) : ‖∫ x in a..b, f x‖ <= C * |b - a|
参数：h : forall x in Ι a b, ‖f x‖ <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `intervalIntegral.norm_integral_le_of_norm_le_const_ae`：norm_integral_le_
of_norm_le_const_ae {a b C : Real} {f : Real -> E} (h : forallᵐ x, x in Ι a b ->
 ‖f x‖ <= C) : ‖∫ x in a..b, f x‖ <= C * |b…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
theorem norm_integral_le_of_norm_le_const {a b C : ℝ} {f : ℝ → E} (h : ∀ x ∈ Ι a b, ‖f x‖ ≤ C) :
    ‖∫ x in a..b, f x‖ ≤ C * |b - a| :=
  norm_integral_le_of_norm_le_const_ae <| Eventually.of_forall h

@[simp]
nonrec theorem integral_add (hf : IntervalIntegrable f μ a b) (hg : IntervalIntegrable g μ a b) :
    ∫ x in a..b, f x + g x ∂μ = (∫ x in a..b, f x ∂μ) + ∫ x in a..b, g x ∂μ := by
  simp only [intervalIntegral_eq_integral_uIoc, integral_add hf.def' hg.def', smul_add]

nonrec theorem integral_finsetSum {ι} {s : Finset ι} {f : ι → ℝ → E}
    (h : ∀ i ∈ s, IntervalIntegrable (f i) μ a b) :
    ∫ x in a..b, ∑ i ∈ s, f i x ∂μ = ∑ i ∈ s, ∫ x in a..b, f i x ∂μ := by
  simp only [intervalIntegral_eq_integral_uIoc, integral_finsetSum s fun i hi => (h i hi).def',
    Finset.smul_sum]

@[deprecated (since := "2026-04-08")] alias integral_finset_sum := integral_finsetSum

@[simp]
nonrec theorem integral_neg : ∫ x in a..b, -f x ∂μ = -∫ x in a..b, f x ∂μ := by
  simp only [intervalIntegral, integral_neg]; abel

@[simp]
/-
**intervalIntegral.integral_sub** 是 Mathlib 中的一个定理，位于命名空间 `intervalIntegral`。
形式化陈述：integral_sub (hf : IntervalIntegrable f μ a b) (hg : IntervalIntegrable g 
μ a b) : ∫ x in a..b, f x - g x ∂μ = (∫ x in a..b, f x ∂μ) - ∫ x in a..b, g x ∂μ
参数：hf : IntervalIntegrable f μ a b；hg : IntervalIntegrable g μ a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `intervalIntegral.integral_add`：∀ {E : Type u_5} [inst : NormedAddCommGro
up E] [inst_1 : NormedSpace ℝ E] {a b : ℝ} {f g : ℝ → E}   {μ : MeasureTheory.Me
asure ℝ},   Interva…
· 使用定理 `IntervalIntegrable.neg`：neg {f : Real -> E} (h : IntervalIntegrable f μ 
a b) : IntervalIntegrable (-f) μ a b
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `intervalIntegral.integral_neg`：∀ {E : Type u_5} [inst : NormedAddCommGro
up E] [inst_1 : NormedSpace ℝ E] {a b : ℝ} {f : ℝ → E}   {μ : MeasureTheory.Meas
ure ℝ}, ∫ (x : ℝ) i…
-/
theorem integral_sub (hf : IntervalIntegrable f μ a b) (hg : IntervalIntegrable g μ a b) :
    ∫ x in a..b, f x - g x ∂μ = (∫ x in a..b, f x ∂μ) - ∫ x in a..b, g x ∂μ := by
  simpa only [sub_eq_add_neg] using! (integral_add hf hg.neg).trans (congr_arg _ integral_neg)

/-- Compatibility with scalar multiplication. Note this assumes `𝕜` is a division ring in order to
ensure that for `c ≠ 0`, `c • f` is integrable iff `f` is. For scalar multiplication by more
general rings assuming integrability, see `IntervalIntegrable.integral_smul`. -/
@[simp]
nonrec theorem integral_smul [NormedDivisionRing 𝕜] [Module 𝕜 E] [NormSMulClass 𝕜 E]
    [SMulCommClass ℝ 𝕜 E] (r : 𝕜) (f : ℝ → E) :
    ∫ x in a..b, r • f x ∂μ = r • ∫ x in a..b, f x ∂μ := by
  simp only [intervalIntegral, integral_smul, smul_sub]

/-
**intervalIntegral._root_.IntervalIntegrable.integral_smul** 是 Mathlib 中的一个定理，位于
命名空间 `intervalIntegral`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IntervalIntegrable.integral_smul
    {R : Type*} [NormedRing R] [Module R E] [IsBoundedSMul R E] [SMulCommClass ℝ R E]
    {f : ℝ → E} (r : R) (hf : IntervalIntegrable f μ a b) :
    ∫ x in a..b, r • f x ∂μ = r • ∫ x in a..b, f x ∂μ := by
  simp only [intervalIntegral, smul_sub, hf.1.integral_smul, hf.2.integral_smul]

@[simp]
nonrec theorem integral_smul_const [CompleteSpace E]
    {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 E] (f : ℝ → 𝕜) (c : E) :
    ∫ x in a..b, f x • c ∂μ = (∫ x in a..b, f x ∂μ) • c := by
  simp only [intervalIntegral_eq_integral_uIoc, integral_smul_const, smul_assoc]

@[simp]
/-
**intervalIntegral.integral_const_mul** 是 Mathlib 中的一个定理，位于命名空间 `intervalIntegra
l`。
形式化陈述：integral_const_mul [NormedDivisionRing 𝕜] [NormedAlgebra Real 𝕜] (r : 𝕜) (
f : Real -> 𝕜) : ∫ x in a..b, r * f x ∂μ = r * ∫ x in a..b, f x ∂μ
参数：r : 𝕜；f : Real -> 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `intervalIntegral.integral_smul`：∀ {𝕜 : Type u_2} {E : Type u_5} [inst : 
NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {a b : ℝ}   {μ : MeasureTheory.
Measure ℝ} [inst_2 :…
· 使用定理 `NormMulClass.toNormSMulClass`：∀ {α : Type u_1} [inst : Norm α] [inst_1 :
 Mul α] [NormMulClass α], NormSMulClass α α
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem integral_const_mul [NormedDivisionRing 𝕜] [NormedAlgebra ℝ 𝕜] (r : 𝕜) (f : ℝ → 𝕜) :
    ∫ x in a..b, r * f x ∂μ = r * ∫ x in a..b, f x ∂μ :=
  integral_smul r f

@[simp]
/-
**intervalIntegral.integral_mul_const** 是 Mathlib 中的一个定理，位于命名空间 `intervalIntegra
l`。
形式化陈述：integral_mul_const {𝕜 : Type*} [RCLike 𝕜] (r : 𝕜) (f : Real -> 𝕜) : ∫ x in
 a..b, f x * r ∂μ = (∫ x in a..b, f x ∂μ) * r
参数：r : 𝕜；f : Real -> 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `intervalIntegral.integral_const_mul`：integral_const_mul [NormedDivisionR
ing 𝕜] [NormedAlgebra Real 𝕜] (r : 𝕜) (f : Real -> 𝕜) : ∫ x in a..b, r * f x ∂μ 
= r * ∫ x in a..b, f x ∂μ
-/
theorem integral_mul_const {𝕜 : Type*} [RCLike 𝕜] (r : 𝕜) (f : ℝ → 𝕜) :
    ∫ x in a..b, f x * r ∂μ = (∫ x in a..b, f x ∂μ) * r := by
  simpa only [mul_comm r] using integral_const_mul r f

@[simp]
/-
**intervalIntegral.integral_div** 是 Mathlib 中的一个定理，位于命名空间 `intervalIntegral`。
形式化陈述：integral_div {𝕜 : Type*} [RCLike 𝕜] (r : 𝕜) (f : Real -> 𝕜) : ∫ x in a..b,
 f x / r ∂μ = (∫ x in a..b, f x ∂μ) / r
参数：r : 𝕜；f : Real -> 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `intervalIntegral.integral_mul_const`：integral_mul_const {𝕜 : Type*} [RCL
ike 𝕜] (r : 𝕜) (f : Real -> 𝕜) : ∫ x in a..b, f x * r ∂μ = (∫ x in a..b, f x ∂μ)
 * r
-/
theorem integral_div {𝕜 : Type*} [RCLike 𝕜] (r : 𝕜) (f : ℝ → 𝕜) :
    ∫ x in a..b, f x / r ∂μ = (∫ x in a..b, f x ∂μ) / r := by
  simpa only [div_eq_mul_inv] using integral_mul_const r⁻¹ f
/-
**intervalIntegral.integral_const'** 是 Mathlib 中的一个定理，位于命名空间 `intervalIntegral`。
形式化陈述：integral_const' [CompleteSpace E] (c : E) : ∫ _ in a..b, c ∂μ = (μ.real (I
oc a b) - μ.real (Ioc b a)) • c
参数：c : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.setIntegral_const`：setIntegral_const [CompleteSpace E] (c 
: E) : ∫ _ in s, c ∂μ = μ.real s • c
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integral_const' [CompleteSpace E] (c : E) :
    ∫ _ in a..b, c ∂μ = (μ.real (Ioc a b) - μ.real (Ioc b a)) • c := by
  simp only [measureReal_def, intervalIntegral, setIntegral_const, sub_smul]

@[simp]
/-
**intervalIntegral.integral_const** 是 Mathlib 中的一个定理，位于命名空间 `intervalIntegral`。
形式化陈述：integral_const [CompleteSpace E] (c : E) : ∫ _ in a..b, c = (b - a) • c
参数：c : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intervalIntegral.integral_const'`：integral_const' [CompleteSpace E] (c :
 E) : ∫ _ in a..b, c ∂μ = (μ.real (Ioc a b) - μ.real (Ioc b a)) • c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Real.volume_Ioc`：volume_Ioc {a b : Real} : volume (Ioc a b) = ofReal (b 
- a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `max_zero_sub_eq_self`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : Lin
earOrder α] [AddLeftMono α] (a : α), max a 0 - max (-a) 0 = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integral_const [CompleteSpace E] (c : E) : ∫ _ in a..b, c = (b - a) • c := by
  simp only [integral_const', Real.volume_Ioc, ENNReal.toReal_ofReal', ← neg_sub b,
    max_zero_sub_eq_self, measureReal_def]

nonrec theorem integral_smul_measure (c : ℝ≥0∞) :
    ∫ x in a..b, f x ∂c • μ = c.toReal • ∫ x in a..b, f x ∂μ := by
  simp only [intervalIntegral, Measure.restrict_smul, integral_smul_measure, smul_sub]

end Basic

-- TODO: add `Complex.ofReal` version of `_root_.integral_ofReal`

nonrec theorem _root_.RCLike.intervalIntegral_ofReal {𝕜 : Type*} [RCLike 𝕜] {a b : ℝ}
    {μ : Measure ℝ} {f : ℝ → ℝ} : (∫ x in a..b, (f x : 𝕜) ∂μ) = ↑(∫ x in a..b, f x ∂μ) := by
  simp only [intervalIntegral, integral_ofReal, RCLike.ofReal_sub]

nonrec theorem integral_ofReal {a b : ℝ} {μ : Measure ℝ} {f : ℝ → ℝ} :
    (∫ x in a..b, (f x : ℂ) ∂μ) = ↑(∫ x in a..b, f x ∂μ) :=
  RCLike.intervalIntegral_ofReal

section ContinuousLinearMap

variable {a b : ℝ} {μ : Measure ℝ} {f : ℝ → E}
variable [RCLike 𝕜] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

open ContinuousLinearMap

/-
**intervalIntegral._root_.ContinuousLinearMap.intervalIntegral_apply** 是 Mathlib
 中的一个定理，位于命名空间 `intervalIntegral`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.ContinuousLinearMap.intervalIntegral_apply {a b : ℝ} {φ : ℝ → F →L[𝕜] E}
    (hφ : IntervalIntegrable φ μ a b) (v : F) :
    (∫ x in a..b, φ x ∂μ) v = ∫ x in a..b, φ x v ∂μ := by
  simp_rw [intervalIntegral_eq_integral_uIoc, ← integral_apply hφ.def' v, smul_apply]

variable [NormedSpace ℝ F] [CompleteSpace F]
/-
**intervalIntegral._root_.ContinuousLinearMap.intervalIntegral_comp_comm** 是 Mat
hlib 中的一个定理，位于命名空间 `intervalIntegral`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.ContinuousLinearMap.intervalIntegral_comp_comm [CompleteSpace E] (L : E →L[𝕜] F)
    (hf : IntervalIntegrable f μ a b) : (∫ x in a..b, L (f x) ∂μ) = L (∫ x in a..b, f x ∂μ) := by
  simp_rw [intervalIntegral, L.integral_comp_comm hf.1, L.integral_comp_comm hf.2, L.map_sub]

end ContinuousLinearMap

section LinearIsometry

variable {a b : ℝ} {μ : Measure ℝ} {f : ℝ → E} [RCLike 𝕜]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]

variable [NormedSpace ℝ F] [CompleteSpace E] [CompleteSpace F]

/-
**intervalIntegral._root_.LinearIsometry.intervalIntegral_comp_comm** 是 Mathlib 
中的一个定理，位于命名空间 `intervalIntegral`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.LinearIsometry.intervalIntegral_comp_comm (L : E →ₗᵢ[𝕜] F) (f : ℝ → E) :
    ∫ x in a..b, L (f x) ∂μ = L (∫ x in a..b, f x ∂μ) := by
  simp_rw [intervalIntegral, L.integral_comp_comm, L.map_sub]

end LinearIsometry

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜] {f : ℝ → 𝕜} {a b : ℝ} {μ : Measure ℝ}

/-
**intervalIntegral.intervalIntegral_re** 是 Mathlib 中的一个定理，位于命名空间 `intervalIntegr
al`。
形式化陈述：intervalIntegral_re (hf : IntervalIntegrable f μ a b) : ∫ x in a..b, RCLik
e.re (f x) ∂μ = RCLike.re (∫ x in a..b, f x ∂μ)
参数：hf : IntervalIntegrable f μ a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.intervalIntegral_comp_comm`：∀ {𝕜 : Type u_2} {E : Ty
pe u_5} {F : Type u_6} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] 
{a b : ℝ}   {μ : MeasureTheory.Measu…
· 使用定理 `RCLike.toCompleteSpace`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K
], CompleteSpace K
-/
theorem intervalIntegral_re (hf : IntervalIntegrable f μ a b) :
    ∫ x in a..b, RCLike.re (f x) ∂μ = RCLike.re (∫ x in a..b, f x ∂μ) :=
  RCLike.reCLM.intervalIntegral_comp_comm hf
/-
**intervalIntegral.intervalIntegral_im** 是 Mathlib 中的一个定理，位于命名空间 `intervalIntegr
al`。
形式化陈述：intervalIntegral_im (hf : IntervalIntegrable f μ a b) : ∫ x in a..b, RCLik
e.im (f x) ∂μ = RCLike.im (∫ x in a..b, f x ∂μ)
参数：hf : IntervalIntegrable f μ a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.intervalIntegral_comp_comm`：∀ {𝕜 : Type u_2} {E : Ty
pe u_5} {F : Type u_6} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] 
{a b : ℝ}   {μ : MeasureTheory.Measu…
· 使用定理 `RCLike.toCompleteSpace`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K
], CompleteSpace K
-/
theorem intervalIntegral_im (hf : IntervalIntegrable f μ a b) :
    ∫ x in a..b, RCLike.im (f x) ∂μ = RCLike.im (∫ x in a..b, f x ∂μ) :=
  RCLike.imCLM.intervalIntegral_comp_comm hf

open scoped ComplexConjugate in
/-
**intervalIntegral.intervalIntegral_conj** 是 Mathlib 中的一个定理，位于命名空间 `intervalInte
gral`。
形式化陈述：intervalIntegral_conj : ∫ x in a..b, conj (f x) ∂μ = conj (∫ x in a..b, f 
x ∂μ)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometry.intervalIntegral_comp_comm`：∀ {𝕜 : Type u_2} {E : Type u_
5} {F : Type u_6} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {a b 
: ℝ}   {μ : MeasureTheory.Measu…
· 使用定理 `RCLike.toCompleteSpace`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K
], CompleteSpace K
-/
theorem intervalIntegral_conj : ∫ x in a..b, conj (f x) ∂μ = conj (∫ x in a..b, f x ∂μ) :=
  RCLike.conjLIE.toLinearIsometry.intervalIntegral_comp_comm f

end RCLike

/-!
## Basic arithmetic
Includes addition, scalar multiplication and affine transformations.
-/
section Comp

variable {a b c d : ℝ} (f : ℝ → E)

@[simp]
/-
**intervalIntegral.integral_comp_mul_right** 是 Mathlib 中的一个定理，位于命名空间 `intervalIn
tegral`。
形式化陈述：integral_comp_mul_right (hc : c != 0) : (∫ x in a..b, f (x * c)) = c⁻¹ • ∫
 x in a * c..b * c, f x
参数：hc : c != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsClosedEmbedding.measurableEmbedding`：∀ {α : Type u_1} {β : Ty
pe u_2} [inst : TopologicalSpace α] [mα : MeasurableSpace α] [BorelSpace α]   [m
β : TopologicalSpace β] [inst_2 : Me…
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Homeomorph.isClosedEmbedding`：isClosedEmbedding (h : X ≃ₜ Y) : IsClosedE
mbedding h
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.smul_map_volume_mul_right`：smul_map_volume_mul_right {a : Real} (h 
: a != 0) : ENNReal.ofReal |a| • Measure.map (· * a) volume = volume
· 使用定理 `intervalIntegral.integral_smul_measure`：∀ {E : Type u_5} [inst : NormedA
ddCommGroup E] [inst_1 : NormedSpace ℝ E] {a b : ℝ} {f : ℝ → E}   {μ : MeasureTh
eory.Measure ℝ} (c : ENNReal…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasurableEmbedding.setIntegral_map`：∀ {X : Type u_1} {E : Type u_3} {mX
 : MeasurableSpace X} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]  
 {μ : MeasureTheory.Measu…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.toReal_ofReal`：toReal_ofReal {r : Real} (h : 0 <= r) : (ENNReal.
ofReal r).toReal = r
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `abs_of_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], a < 0 → |a| = -a
· 使用定理 `Set.preimage_mul_const_Ioc_of_neg`：preimage_mul_const_Ioc_of_neg (a b : 
α) {c : α} (h : c < 0) : (fun x => x * c) ⁻¹' Ioc a b = Ico (b / c) (a / c)
· 使用定理 `mul_div_cancel_right₀`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] [ins
t_1 : Div M₀] [MulDivCancelClass M₀] (a : M₀) {b : M₀},   b ≠ 0 → a * b / b = a
· 使用定理 `EuclideanDomain.toMulDivCancelClass`：∀ {R : Type u} [inst : EuclideanDom
ain R], MulDivCancelClass R
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MeasureTheory.Measure.restrict_congr_set`：restrict_congr_set (h : s =ᵐ[μ
] t) : μ.restrict s = μ.restrict t
· 使用定理 `MeasureTheory.Ico_ae_eq_Ioc`：Ico_ae_eq_Ioc : Ico a b =ᵐ[μ] Ioc a b
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
（共 39 条，此处仅展示前 30 条）
-/
theorem integral_comp_mul_right (hc : c ≠ 0) :
    (∫ x in a..b, f (x * c)) = c⁻¹ • ∫ x in a * c..b * c, f x := by
  have A : MeasurableEmbedding fun x => x * c :=
    (Homeomorph.mulRight₀ c hc).isClosedEmbedding.measurableEmbedding
  conv_rhs => rw [← Real.smul_map_volume_mul_right hc]
  simp_rw [integral_smul_measure, intervalIntegral, A.setIntegral_map,
    ENNReal.toReal_ofReal (abs_nonneg c)]
  rcases hc.lt_or_gt with h | h
  · simp [h, mul_div_cancel_right₀, hc, abs_of_neg,
      Measure.restrict_congr_set (α := ℝ) (μ := volume) Ico_ae_eq_Ioc]
  · simp [h, mul_div_cancel_right₀, hc, abs_of_pos]

@[simp]
/-
**intervalIntegral.smul_integral_comp_mul_right** 是 Mathlib 中的一个定理，位于命名空间 `inter
valIntegral`。
形式化陈述：smul_integral_comp_mul_right (c) : (c • ∫ x in a..b, f (x * c)) = ∫ x in a
 * c..b * c, f x
参数：c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `intervalIntegral.integral_same`：integral_same : ∫ x in a..a, f x ∂μ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `intervalIntegral.integral_comp_mul_right`：integral_comp_mul_right (hc : 
c != 0) : (∫ x in a..b, f (x * c)) = c⁻¹ • ∫ x in a * c..b * c, f x
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `smul_inv_smul₀`：smul_inv_smul₀ (ha : a != 0) (x : β) : a • a⁻¹ • x = x
-/
theorem smul_integral_comp_mul_right (c) :
    (c • ∫ x in a..b, f (x * c)) = ∫ x in a * c..b * c, f x := by
  by_cases hc : c = 0 <;> simp [hc, integral_comp_mul_right]

@[simp]
/-
**intervalIntegral.integral_comp_mul_left** 是 Mathlib 中的一个定理，位于命名空间 `intervalInt
egral`。
形式化陈述：integral_comp_mul_left (hc : c != 0) : (∫ x in a..b, f (c * x)) = c⁻¹ • ∫ 
x in c * a..c * b, f x
参数：hc : c != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `intervalIntegral.integral_comp_mul_right`：integral_comp_mul_right (hc : 
c != 0) : (∫ x in a..b, f (x * c)) = c⁻¹ • ∫ x in a * c..b * c, f x
-/
theorem integral_comp_mul_left (hc : c ≠ 0) :
    (∫ x in a..b, f (c * x)) = c⁻¹ • ∫ x in c * a..c * b, f x := by
  simpa only [mul_comm c] using integral_comp_mul_right f hc

@[simp]
/-
**intervalIntegral.smul_integral_comp_mul_left** 是 Mathlib 中的一个定理，位于命名空间 `interv
alIntegral`。
形式化陈述：smul_integral_comp_mul_left (c) : (c • ∫ x in a..b, f (c * x)) = ∫ x in c 
* a..c * b, f x
参数：c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `intervalIntegral.integral_same`：integral_same : ∫ x in a..a, f x ∂μ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `intervalIntegral.integral_comp_mul_left`：integral_comp_mul_left (hc : c 
!= 0) : (∫ x in a..b, f (c * x)) = c⁻¹ • ∫ x in c * a..c * b, f x
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `smul_inv_smul₀`：smul_inv_smul₀ (ha : a != 0) (x : β) : a • a⁻¹ • x = x
-/
theorem smul_integral_comp_mul_left (c) :
    (c • ∫ x in a..b, f (c * x)) = ∫ x in c * a..c * b, f x := by
  by_cases hc : c = 0 <;> simp [hc, integral_comp_mul_left]

@[simp]
/-
**intervalIntegral.integral_comp_div** 是 Mathlib 中的一个定理，位于命名空间 `intervalIntegral
`。
形式化陈述：integral_comp_div (hc : c != 0) : (∫ x in a..b, f (x / c)) = c • ∫ x in a 
/ c..b / c, f x
参数：hc : c != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `intervalIntegral.integral_comp_mul_right`：integral_comp_mul_right (hc : 
c != 0) : (∫ x in a..b, f (x * c)) = c⁻¹ • ∫ x in a * c..b * c, f x
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
-/
theorem integral_comp_div (hc : c ≠ 0) :
    (∫ x in a..b, f (x / c)) = c • ∫ x in a / c..b / c, f x := by
  simpa only [inv_inv] using! integral_comp_mul_right f (inv_ne_zero hc)

@[simp]
/-
**intervalIntegral.inv_smul_integral_comp_div** 是 Mathlib 中的一个定理，位于命名空间 `interva
lIntegral`。
形式化陈述：inv_smul_integral_comp_div (c) : (c⁻¹ • ∫ x in a..b, f (x / c)) = ∫ x in a
 / c..b / c, f x
参数：c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `intervalIntegral.integral_same`：integral_same : ∫ x in a..a, f x ∂μ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `intervalIntegral.integral_comp_div`：integral_comp_div (hc : c != 0) : (∫
 x in a..b, f (x / c)) = c • ∫ x in a / c..b / c, f x
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `inv_smul_smul₀`：∀ {α : Type u_4} {β : Type u_5} [inst : GroupWithZero α]
 [inst_1 : MulAction α β] {a : α},   a ≠ 0 → ∀ (x : β), a⁻¹ • a • x = x
-/
theorem inv_smul_integral_comp_div (c) :
    (c⁻¹ • ∫ x in a..b, f (x / c)) = ∫ x in a / c..b / c, f x := by
  by_cases hc : c = 0 <;> simp [hc, integral_comp_div]

@[simp]
/-
**intervalIntegral.integral_comp_add_right** 是 Mathlib 中的一个定理，位于命名空间 `intervalIn
tegral`。
形式化陈述：integral_comp_add_right (d) : (∫ x in a..b, f (x + d)) = ∫ x in a + d..b +
 d, f x
参数：d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsClosedEmbedding.measurableEmbedding`：∀ {α : Type u_1} {β : Ty
pe u_2} [inst : TopologicalSpace α] [mα : MeasurableSpace α] [BorelSpace α]   [m
β : TopologicalSpace β] [inst_2 : Me…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Homeomorph.isClosedEmbedding`：isClosedEmbedding (h : X ≃ₜ Y) : IsClosedE
mbedding h
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasurableEmbedding.setIntegral_map`：∀ {X : Type u_1} {E : Type u_3} {mX
 : MeasurableSpace X} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]  
 {μ : MeasureTheory.Measu…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.preimage_add_const_Ioc`：∀ {α : Type u_1} [inst : AddCommGroup α] [in
st_1 : PartialOrder α] [IsOrderedAddMonoid α] (a b c : α),   (fun x => x + a) ⁻¹
' Set.Ioc b c = …
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.map_add_right_eq_self`：∀ {G : Type u_1} [inst : Measurable
Space G] [inst_1 : Add G] (μ : MeasureTheory.Measure G) [μ.IsAddRightInvariant] 
  (g : G), MeasureTheory.…
· 使用定理 `MeasureTheory.IsAddLeftInvariant.isAddRightInvariant`：∀ {G : Type u_1} [
inst : MeasurableSpace G] [inst_1 : AddCommSemigroup G] {μ : MeasureTheory.Measu
re G}   [μ.IsAddLeftInvariant], μ.IsAddRig…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsAddLeftInvariant`：∀ {G : Type
 u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpac
e G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
-/
theorem integral_comp_add_right (d) : (∫ x in a..b, f (x + d)) = ∫ x in a + d..b + d, f x :=
  have A : MeasurableEmbedding fun x => x + d :=
    (Homeomorph.addRight d).isClosedEmbedding.measurableEmbedding
  calc
    (∫ x in a..b, f (x + d)) = ∫ x in a + d..b + d, f x ∂Measure.map (fun x => x + d) volume := by
      simp [intervalIntegral, A.setIntegral_map]
    _ = ∫ x in a + d..b + d, f x := by rw [map_add_right_eq_self]

@[simp]
nonrec theorem integral_comp_add_left (d) :
    (∫ x in a..b, f (d + x)) = ∫ x in d + a..d + b, f x := by
  simpa only [add_comm d] using integral_comp_add_right f d

@[simp]
/-
**intervalIntegral.integral_comp_mul_add** 是 Mathlib 中的一个定理，位于命名空间 `intervalInte
gral`。
形式化陈述：integral_comp_mul_add (hc : c != 0) (d) : (∫ x in a..b, f (c * x + d)) = c
⁻¹ • ∫ x in c * a + d..c * b + d, f x
参数：hc : c != 0；d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `intervalIntegral.integral_comp_add_right`：integral_comp_add_right (d) : 
(∫ x in a..b, f (x + d)) = ∫ x in a + d..b + d, f x
· 使用定理 `intervalIntegral.integral_comp_mul_left`：integral_comp_mul_left (hc : c 
!= 0) : (∫ x in a..b, f (c * x)) = c⁻¹ • ∫ x in c * a..c * b, f x
-/
theorem integral_comp_mul_add (hc : c ≠ 0) (d) :
    (∫ x in a..b, f (c * x + d)) = c⁻¹ • ∫ x in c * a + d..c * b + d, f x := by
  rw [← integral_comp_add_right, ← integral_comp_mul_left _ hc]

@[simp]
/-
**intervalIntegral.smul_integral_comp_mul_add** 是 Mathlib 中的一个定理，位于命名空间 `interva
lIntegral`。
形式化陈述：smul_integral_comp_mul_add (c d) : (c • ∫ x in a..b, f (c * x + d)) = ∫ x 
in c * a + d..c * b + d, f x
参数：c d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `intervalIntegral.integral_same`：integral_same : ∫ x in a..a, f x ∂μ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `intervalIntegral.integral_comp_mul_add`：integral_comp_mul_add (hc : c !=
 0) (d) : (∫ x in a..b, f (c * x + d)) = c⁻¹ • ∫ x in c * a + d..c * b + d, f x
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `smul_inv_smul₀`：smul_inv_smul₀ (ha : a != 0) (x : β) : a • a⁻¹ • x = x
-/
theorem smul_integral_comp_mul_add (c d) :
    (c • ∫ x in a..b, f (c * x + d)) = ∫ x in c * a + d..c * b + d, f x := by
  by_cases hc : c = 0 <;> simp [hc, integral_comp_mul_add]

@[simp]
/-
**intervalIntegral.integral_comp_add_mul** 是 Mathlib 中的一个定理，位于命名空间 `intervalInte
gral`。
形式化陈述：integral_comp_add_mul (hc : c != 0) (d) : (∫ x in a..b, f (d + c * x)) = c
⁻¹ • ∫ x in d + c * a..d + c * b, f x
参数：hc : c != 0；d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `intervalIntegral.integral_comp_add_left`：∀ {E : Type u_5} [inst : Normed
AddCommGroup E] [inst_1 : NormedSpace ℝ E] {a b : ℝ} (f : ℝ → E) (d : ℝ),   ∫ (x
 : ℝ) in a..b, f (d + x) = ∫ …
· 使用定理 `intervalIntegral.integral_comp_mul_left`：integral_comp_mul_left (hc : c 
!= 0) : (∫ x in a..b, f (c * x)) = c⁻¹ • ∫ x in c * a..c * b, f x
-/
theorem integral_comp_add_mul (hc : c ≠ 0) (d) :
    (∫ x in a..b, f (d + c * x)) = c⁻¹ • ∫ x in d + c * a..d + c * b, f x := by
  rw [← integral_comp_add_left, ← integral_comp_mul_left _ hc]

@[simp]
/-
**intervalIntegral.smul_integral_comp_add_mul** 是 Mathlib 中的一个定理，位于命名空间 `interva
lIntegral`。
形式化陈述：smul_integral_comp_add_mul (c d) : (c • ∫ x in a..b, f (d + c * x)) = ∫ x 
in d + c * a..d + c * b, f x
参数：c d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `intervalIntegral.integral_same`：integral_same : ∫ x in a..a, f x ∂μ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `intervalIntegral.integral_comp_add_mul`：integral_comp_add_mul (hc : c !=
 0) (d) : (∫ x in a..b, f (d + c * x)) = c⁻¹ • ∫ x in d + c * a..d + c * b, f x
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `smul_inv_smul₀`：smul_inv_smul₀ (ha : a != 0) (x : β) : a • a⁻¹ • x = x
-/
theorem smul_integral_comp_add_mul (c d) :
    (c • ∫ x in a..b, f (d + c * x)) = ∫ x in d + c * a..d + c * b, f x := by
  by_cases hc : c = 0 <;> simp [hc, integral_comp_add_mul]

@[simp]
/-
**intervalIntegral.integral_comp_div_add** 是 Mathlib 中的一个定理，位于命名空间 `intervalInte
gral`。
形式化陈述：integral_comp_div_add (hc : c != 0) (d) : (∫ x in a..b, f (x / c + d)) = c
 • ∫ x in a / c + d..b / c + d, f x
参数：hc : c != 0；d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `intervalIntegral.integral_comp_mul_add`：integral_comp_mul_add (hc : c !=
 0) (d) : (∫ x in a..b, f (c * x + d)) = c⁻¹ • ∫ x in c * a + d..c * b + d, f x
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
-/
theorem integral_comp_div_add (hc : c ≠ 0) (d) :
    (∫ x in a..b, f (x / c + d)) = c • ∫ x in a / c + d..b / c + d, f x := by
  simpa only [div_eq_inv_mul, inv_inv] using integral_comp_mul_add f (inv_ne_zero hc) d

@[simp]
/-
**intervalIntegral.inv_smul_integral_comp_div_add** 是 Mathlib 中的一个定理，位于命名空间 `int
ervalIntegral`。
形式化陈述：inv_smul_integral_comp_div_add (c d) : (c⁻¹ • ∫ x in a..b, f (x / c + d)) 
= ∫ x in a / c + d..b / c + d, f x
参数：c d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `intervalIntegral.integral_same`：integral_same : ∫ x in a..a, f x ∂μ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `intervalIntegral.integral_comp_div_add`：integral_comp_div_add (hc : c !=
 0) (d) : (∫ x in a..b, f (x / c + d)) = c • ∫ x in a / c + d..b / c + d, f x
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `inv_smul_smul₀`：∀ {α : Type u_4} {β : Type u_5} [inst : GroupWithZero α]
 [inst_1 : MulAction α β] {a : α},   a ≠ 0 → ∀ (x : β), a⁻¹ • a • x = x
-/
theorem inv_smul_integral_comp_div_add (c d) :
    (c⁻¹ • ∫ x in a..b, f (x / c + d)) = ∫ x in a / c + d..b / c + d, f x := by
  by_cases hc : c = 0 <;> simp [hc, integral_comp_div_add]

@[simp]
/-
**intervalIntegral.integral_comp_add_div** 是 Mathlib 中的一个定理，位于命名空间 `intervalInte
gral`。
形式化陈述：integral_comp_add_div (hc : c != 0) (d) : (∫ x in a..b, f (d + x / c)) = c
 • ∫ x in d + a / c..d + b / c, f x
参数：hc : c != 0；d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `intervalIntegral.integral_comp_add_mul`：integral_comp_add_mul (hc : c !=
 0) (d) : (∫ x in a..b, f (d + c * x)) = c⁻¹ • ∫ x in d + c * a..d + c * b, f x
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
-/
theorem integral_comp_add_div (hc : c ≠ 0) (d) :
    (∫ x in a..b, f (d + x / c)) = c • ∫ x in d + a / c..d + b / c, f x := by
  simpa only [div_eq_inv_mul, inv_inv] using integral_comp_add_mul f (inv_ne_zero hc) d

@[simp]
/-
**intervalIntegral.inv_smul_integral_comp_add_div** 是 Mathlib 中的一个定理，位于命名空间 `int
ervalIntegral`。
形式化陈述：inv_smul_integral_comp_add_div (c d) : (c⁻¹ • ∫ x in a..b, f (d + x / c)) 
= ∫ x in d + a / c..d + b / c, f x
参数：c d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `intervalIntegral.integral_same`：integral_same : ∫ x in a..a, f x ∂μ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `intervalIntegral.integral_comp_add_div`：integral_comp_add_div (hc : c !=
 0) (d) : (∫ x in a..b, f (d + x / c)) = c • ∫ x in d + a / c..d + b / c, f x
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `inv_smul_smul₀`：∀ {α : Type u_4} {β : Type u_5} [inst : GroupWithZero α]
 [inst_1 : MulAction α β] {a : α},   a ≠ 0 → ∀ (x : β), a⁻¹ • a • x = x
-/
theorem inv_smul_integral_comp_add_div (c d) :
    (c⁻¹ • ∫ x in a..b, f (d + x / c)) = ∫ x in d + a / c..d + b / c, f x := by
  by_cases hc : c = 0 <;> simp [hc, integral_comp_add_div]

@[simp]
/-
**intervalIntegral.integral_comp_mul_sub** 是 Mathlib 中的一个定理，位于命名空间 `intervalInte
gral`。
形式化陈述：integral_comp_mul_sub (hc : c != 0) (d) : (∫ x in a..b, f (c * x - d)) = c
⁻¹ • ∫ x in c * a - d..c * b - d, f x
参数：hc : c != 0；d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `intervalIntegral.integral_comp_mul_add`：integral_comp_mul_add (hc : c !=
 0) (d) : (∫ x in a..b, f (c * x + d)) = c⁻¹ • ∫ x in c * a + d..c * b + d, f x
-/
theorem integral_comp_mul_sub (hc : c ≠ 0) (d) :
    (∫ x in a..b, f (c * x - d)) = c⁻¹ • ∫ x in c * a - d..c * b - d, f x := by
  simpa only [sub_eq_add_neg] using integral_comp_mul_add f hc (-d)

@[simp]
/-
**intervalIntegral.smul_integral_comp_mul_sub** 是 Mathlib 中的一个定理，位于命名空间 `interva
lIntegral`。
形式化陈述：smul_integral_comp_mul_sub (c d) : (c • ∫ x in a..b, f (c * x - d)) = ∫ x 
in c * a - d..c * b - d, f x
参数：c d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `intervalIntegral.integral_same`：integral_same : ∫ x in a..a, f x ∂μ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `intervalIntegral.integral_comp_mul_sub`：integral_comp_mul_sub (hc : c !=
 0) (d) : (∫ x in a..b, f (c * x - d)) = c⁻¹ • ∫ x in c * a - d..c * b - d, f x
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `smul_inv_smul₀`：smul_inv_smul₀ (ha : a != 0) (x : β) : a • a⁻¹ • x = x
-/
theorem smul_integral_comp_mul_sub (c d) :
    (c • ∫ x in a..b, f (c * x - d)) = ∫ x in c * a - d..c * b - d, f x := by
  by_cases hc : c = 0 <;> simp [hc, integral_comp_mul_sub]

@[simp]
/-
**intervalIntegral.integral_comp_sub_mul** 是 Mathlib 中的一个定理，位于命名空间 `intervalInte
gral`。
形式化陈述：integral_comp_sub_mul (hc : c != 0) (d) : (∫ x in a..b, f (d - c * x)) = c
⁻¹ • ∫ x in d - c * b..d - c * a, f x
参数：hc : c != 0；d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `neg_mul_eq_neg_mul`：neg_mul_eq_neg_mul (a b : α) : -(a * b) = -a * b
· 使用定理 `intervalIntegral.integral_comp_add_mul`：integral_comp_add_mul (hc : c !=
 0) (d) : (∫ x in a..b, f (d + c * x)) = c⁻¹ • ∫ x in d + c * a..d + c * b, f x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_ne_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a ≠
 0 ↔ a ≠ 0
· 使用定理 `intervalIntegral.integral_symm`：integral_symm (a b) : ∫ x in b..a, f x ∂
μ = -∫ x in a..b, f x ∂μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `inv_neg`：inv_neg : (-a)⁻¹ = -a⁻¹
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integral_comp_sub_mul (hc : c ≠ 0) (d) :
    (∫ x in a..b, f (d - c * x)) = c⁻¹ • ∫ x in d - c * b..d - c * a, f x := by
  simp only [sub_eq_add_neg, neg_mul_eq_neg_mul]
  rw [integral_comp_add_mul f (neg_ne_zero.mpr hc) d, integral_symm]
  simp only [inv_neg, smul_neg, neg_neg, neg_smul]

@[simp]
/-
**intervalIntegral.smul_integral_comp_sub_mul** 是 Mathlib 中的一个定理，位于命名空间 `interva
lIntegral`。
形式化陈述：smul_integral_comp_sub_mul (c d) : (c • ∫ x in a..b, f (d - c * x)) = ∫ x 
in d - c * b..d - c * a, f x
参数：c d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `intervalIntegral.integral_same`：integral_same : ∫ x in a..a, f x ∂μ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `intervalIntegral.integral_comp_sub_mul`：integral_comp_sub_mul (hc : c !=
 0) (d) : (∫ x in a..b, f (d - c * x)) = c⁻¹ • ∫ x in d - c * b..d - c * a, f x
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `smul_inv_smul₀`：smul_inv_smul₀ (ha : a != 0) (x : β) : a • a⁻¹ • x = x
-/
theorem smul_integral_comp_sub_mul (c d) :
    (c • ∫ x in a..b, f (d - c * x)) = ∫ x in d - c * b..d - c * a, f x := by
  by_cases hc : c = 0 <;> simp [hc, integral_comp_sub_mul]

@[simp]
/-
**intervalIntegral.integral_comp_div_sub** 是 Mathlib 中的一个定理，位于命名空间 `intervalInte
gral`。
形式化陈述：integral_comp_div_sub (hc : c != 0) (d) : (∫ x in a..b, f (x / c - d)) = c
 • ∫ x in a / c - d..b / c - d, f x
参数：hc : c != 0；d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `intervalIntegral.integral_comp_mul_sub`：integral_comp_mul_sub (hc : c !=
 0) (d) : (∫ x in a..b, f (c * x - d)) = c⁻¹ • ∫ x in c * a - d..c * b - d, f x
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
-/
theorem integral_comp_div_sub (hc : c ≠ 0) (d) :
    (∫ x in a..b, f (x / c - d)) = c • ∫ x in a / c - d..b / c - d, f x := by
  simpa only [div_eq_inv_mul, inv_inv] using integral_comp_mul_sub f (inv_ne_zero hc) d

@[simp]
/-
**intervalIntegral.inv_smul_integral_comp_div_sub** 是 Mathlib 中的一个定理，位于命名空间 `int
ervalIntegral`。
形式化陈述：inv_smul_integral_comp_div_sub (c d) : (c⁻¹ • ∫ x in a..b, f (x / c - d)) 
= ∫ x in a / c - d..b / c - d, f x
参数：c d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `intervalIntegral.integral_same`：integral_same : ∫ x in a..a, f x ∂μ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `intervalIntegral.integral_comp_div_sub`：integral_comp_div_sub (hc : c !=
 0) (d) : (∫ x in a..b, f (x / c - d)) = c • ∫ x in a / c - d..b / c - d, f x
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `inv_smul_smul₀`：∀ {α : Type u_4} {β : Type u_5} [inst : GroupWithZero α]
 [inst_1 : MulAction α β] {a : α},   a ≠ 0 → ∀ (x : β), a⁻¹ • a • x = x
-/
theorem inv_smul_integral_comp_div_sub (c d) :
    (c⁻¹ • ∫ x in a..b, f (x / c - d)) = ∫ x in a / c - d..b / c - d, f x := by
  by_cases hc : c = 0 <;> simp [hc, integral_comp_div_sub]

@[simp]
/-
**intervalIntegral.integral_comp_sub_div** 是 Mathlib 中的一个定理，位于命名空间 `intervalInte
gral`。
形式化陈述：integral_comp_sub_div (hc : c != 0) (d) : (∫ x in a..b, f (d - x / c)) = c
 • ∫ x in d - b / c..d - a / c, f x
参数：hc : c != 0；d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `intervalIntegral.integral_comp_sub_mul`：integral_comp_sub_mul (hc : c !=
 0) (d) : (∫ x in a..b, f (d - c * x)) = c⁻¹ • ∫ x in d - c * b..d - c * a, f x
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
-/
theorem integral_comp_sub_div (hc : c ≠ 0) (d) :
    (∫ x in a..b, f (d - x / c)) = c • ∫ x in d - b / c..d - a / c, f x := by
  simpa only [div_eq_inv_mul, inv_inv] using integral_comp_sub_mul f (inv_ne_zero hc) d

@[simp]
/-
**intervalIntegral.inv_smul_integral_comp_sub_div** 是 Mathlib 中的一个定理，位于命名空间 `int
ervalIntegral`。
形式化陈述：inv_smul_integral_comp_sub_div (c d) : (c⁻¹ • ∫ x in a..b, f (d - x / c)) 
= ∫ x in d - b / c..d - a / c, f x
参数：c d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `intervalIntegral.integral_same`：integral_same : ∫ x in a..a, f x ∂μ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `intervalIntegral.integral_comp_sub_div`：integral_comp_sub_div (hc : c !=
 0) (d) : (∫ x in a..b, f (d - x / c)) = c • ∫ x in d - b / c..d - a / c, f x
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `inv_smul_smul₀`：∀ {α : Type u_4} {β : Type u_5} [inst : GroupWithZero α]
 [inst_1 : MulAction α β] {a : α},   a ≠ 0 → ∀ (x : β), a⁻¹ • a • x = x
-/
theorem inv_smul_integral_comp_sub_div (c d) :
    (c⁻¹ • ∫ x in a..b, f (d - x / c)) = ∫ x in d - b / c..d - a / c, f x := by
  by_cases hc : c = 0 <;> simp [hc, integral_comp_sub_div]

@[simp]
/-
**intervalIntegral.integral_comp_sub_right** 是 Mathlib 中的一个定理，位于命名空间 `intervalIn
tegral`。
形式化陈述：integral_comp_sub_right (d) : (∫ x in a..b, f (x - d)) = ∫ x in a - d..b -
 d, f x
参数：d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `intervalIntegral.integral_comp_add_right`：integral_comp_add_right (d) : 
(∫ x in a..b, f (x + d)) = ∫ x in a + d..b + d, f x
-/
theorem integral_comp_sub_right (d) : (∫ x in a..b, f (x - d)) = ∫ x in a - d..b - d, f x := by
  simpa only [sub_eq_add_neg] using integral_comp_add_right f (-d)

@[simp]
/-
**intervalIntegral.integral_comp_sub_left** 是 Mathlib 中的一个定理，位于命名空间 `intervalInt
egral`。
形式化陈述：integral_comp_sub_left (d) : (∫ x in a..b, f (d - x)) = ∫ x in d - b..d - 
a, f x
参数：d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `intervalIntegral.integral_comp_sub_mul`：integral_comp_sub_mul (hc : c !=
 0) (d) : (∫ x in a..b, f (d - c * x)) = c⁻¹ • ∫ x in d - c * b..d - c * a, f x
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem integral_comp_sub_left (d) : (∫ x in a..b, f (d - x)) = ∫ x in d - b..d - a, f x := by
  simpa only [one_mul, one_smul, inv_one] using integral_comp_sub_mul f one_ne_zero d

@[simp]
/-
**intervalIntegral.integral_comp_neg** 是 Mathlib 中的一个定理，位于命名空间 `intervalIntegral
`。
形式化陈述：integral_comp_neg : (∫ x in a..b, f (-x)) = ∫ x in -b..-a, f x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `intervalIntegral.integral_comp_sub_left`：integral_comp_sub_left (d) : (∫
 x in a..b, f (d - x)) = ∫ x in d - b..d - a, f x
-/
theorem integral_comp_neg : (∫ x in a..b, f (-x)) = ∫ x in -b..-a, f x := by
  simpa only [zero_sub] using integral_comp_sub_left f 0

end Comp

/-!
### Integral is an additive function of the interval

In this section we prove that `∫ x in a..b, f x ∂μ + ∫ x in b..c, f x ∂μ = ∫ x in a..c, f x ∂μ`
as well as a few other identities trivially equivalent to this one. We also prove that
`∫ x in a..b, f x ∂μ = ∫ x, f x ∂μ` provided that `support f ⊆ Ioc a b`.

-/

section OrderClosedTopology

variable {a b c d : ℝ} {f g : ℝ → E} {μ : Measure ℝ}

/-- If two functions are equal in the relevant interval, their interval integrals are also equal. -/
/-
**intervalIntegral.integral_congr** 是 Mathlib 中的一个定理，位于命名空间 `intervalIntegral`。
形式化陈述：integral_congr {a b : Real} (h : EqOn f g [[a, b]]) : ∫ x in a..b, f x ∂μ 
= ∫ x in a..b, g x ∂μ
参数：h : EqOn f g [[a, b]]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intervalIntegral.integral_of_le`：integral_of_le (h : a <= b) : ∫ x in a.
.b, f x ∂μ = ∫ x in Ioc a b, f x ∂μ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `MeasureTheory.setIntegral_congr_fun`：setIntegral_congr_fun (hs : Measura
bleSet s) (h : EqOn f g s) : ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ
· 使用定理 `measurableSet_Ioc`：measurableSet_Ioc [ClosedIicTopology α] : MeasurableS
et (Ioc a b)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Set.EqOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {f₁ f₂ : 
α → β}, s₁ ⊆ s₂ → Set.EqOn f₁ f₂ s₂ → Set.EqOn f₁ f₂ s₁
· 使用定理 `Set.Ioc_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc a b ⊆ Set.Icc a b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `intervalIntegral.integral_of_ge`：integral_of_ge (h : b <= a) : ∫ x in a.
.b, f x ∂μ = -∫ x in Ioc b a, f x ∂μ
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a

--- 原说明 ---
If two functions are equal in the relevant interval, their interval integrals ar
e also equal.
-/
theorem integral_congr {a b : ℝ} (h : EqOn f g [[a, b]]) :
    ∫ x in a..b, f x ∂μ = ∫ x in a..b, g x ∂μ := by
  rcases le_total a b with hab | hab <;>
    simpa [hab, integral_of_le, integral_of_ge] using
      setIntegral_congr_fun measurableSet_Ioc (h.mono Ioc_subset_Icc_self)
/-
**intervalIntegral.integral_add_adjacent_intervals_cancel** 是 Mathlib 中的一个定理，位于命
名空间 `intervalIntegral`。
形式化陈述：integral_add_adjacent_intervals_cancel (hab : IntervalIntegrable f μ a b) 
(hbc : IntervalIntegrable f μ b c) : (((∫ x in a..b, f x ∂μ) + ∫ x in b..c, f x 
∂μ) + ∫ x in c..a, f x ∂μ) = 0
参数：hab : IntervalIntegrable f μ a b；hbc : IntervalIntegrable f μ b c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntervalIntegrable.trans`：trans {a b c : Real} (hab : IntervalIntegrable
 f μ a b) (hbc : IntervalIntegrable f μ b c) : IntervalIntegrable f μ a c
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_add_sub_comm`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b
 c d : α), a - b + (c - d) = a + c - (b + d)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.setIntegral_union`：setIntegral_union (hst : Disjoint s t) 
(ht : MeasurableSet t) (hfs : IntegrableOn f s μ) (hft : IntegrableOn f t μ) : ∫
 x in s union t, f x …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.Ioc_union_Ioc_union_Ioc_cycle`：Ioc_union_Ioc_union_Ioc_cycle : Ioc a
 b union Ioc b c union Ioc c a = Ioc (min a (min b c)) (max a (max b c))
· 使用定理 `Set.union_right_comm`：union_right_comm (s₁ s₂ s₃ : Set α) : s₁ union s₂ 
union s₃ = s₁ union s₃ union s₂
· 使用引理 `min_left_comm`：min_left_comm (a b c : α) : min a (min b c) = min b (min 
a c)
· 使用定理 `max_left_comm`：∀ {α : Type u_1} [inst : LinearOrder α] (a b c : α), max 
a (max b c) = max b (max a c)
-/
theorem integral_add_adjacent_intervals_cancel (hab : IntervalIntegrable f μ a b)
    (hbc : IntervalIntegrable f μ b c) :
    (((∫ x in a..b, f x ∂μ) + ∫ x in b..c, f x ∂μ) + ∫ x in c..a, f x ∂μ) = 0 := by
  have hac := hab.trans hbc
  simp only [intervalIntegral, sub_add_sub_comm, sub_eq_zero]
  iterate 4 rw [← setIntegral_union]
  · suffices Ioc a b ∪ Ioc b c ∪ Ioc c a = Ioc b a ∪ Ioc c b ∪ Ioc a c by rw [this]
    rw [Ioc_union_Ioc_union_Ioc_cycle, union_right_comm, Ioc_union_Ioc_union_Ioc_cycle,
      min_left_comm, max_left_comm]
  all_goals
    simp [*, hab.1, hab.2, hbc.1, hbc.2, hac.1, hac.2]
/-
**intervalIntegral.integral_add_adjacent_intervals** 是 Mathlib 中的一个定理，位于命名空间 `in
tervalIntegral`。
形式化陈述：integral_add_adjacent_intervals (hab : IntervalIntegrable f μ a b) (hbc : 
IntervalIntegrable f μ b c) : ((∫ x in a..b, f x ∂μ) + ∫ x in b..c, f x ∂μ) = ∫ 
x in a..c, f x ∂μ
参数：hab : IntervalIntegrable f μ a b；hbc : IntervalIntegrable f μ b c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_neg_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a + -b 
= 0 ↔ a = b
· 使用定理 `intervalIntegral.integral_symm`：integral_symm (a b) : ∫ x in b..a, f x ∂
μ = -∫ x in a..b, f x ∂μ
· 使用定理 `intervalIntegral.integral_add_adjacent_intervals_cancel`：integral_add_ad
jacent_intervals_cancel (hab : IntervalIntegrable f μ a b) (hbc : IntervalIntegr
able f μ b c) : (((∫ x in a..b, f x ∂μ) + ∫ x…
-/
theorem integral_add_adjacent_intervals (hab : IntervalIntegrable f μ a b)
    (hbc : IntervalIntegrable f μ b c) :
    ((∫ x in a..b, f x ∂μ) + ∫ x in b..c, f x ∂μ) = ∫ x in a..c, f x ∂μ := by
  rw [← add_neg_eq_zero, ← integral_symm, integral_add_adjacent_intervals_cancel hab hbc]
/-
**intervalIntegral.sum_integral_adjacent_intervals_Ico** 是 Mathlib 中的一个定理，位于命名空间
 `intervalIntegral`。
形式化陈述：sum_integral_adjacent_intervals_Ico {a : Nat -> Real} {m n : Nat} (hmn : m
 <= n) (hint : forall k in Ico m n, IntervalIntegrable f μ (a k) (a <| k + 1)) :
 ∑ k in Finset.Ico m n, ∫ x in a k..a k + 1, f x ∂μ = ∫ x in a m..a n, f x ∂μ
参数：hmn : m <= n；hint : forall k in Ico m n, IntervalIntegrable f μ (a k) (a <| k
 + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.le_induction`：le_induction {m : Nat} {P : forall n, m <= n -> Prop} 
(base : P m m.le_refl) (succ : forall n hmn, P n hmn -> P (n + 1) (le_succ_of_le
 hmn))…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Ico_eq_empty`：Ico_eq_empty (h : ¬a < b) : Ico a b = ∅
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.Ico_eq_empty_of_le`：Ico_eq_empty_of_le (h : b <= a) : Ico a b = ∅
· 使用定理 `intervalIntegral.integral_same`：integral_same : ∫ x in a..a, f x ∂μ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sum_Ico_succ_top`：∀ {M : Type u_3} [inst : AddCommMonoid M] {a b 
: ℕ},   a ≤ b → ∀ (f : ℕ → M), ∑ k ∈ Finset.Ico a (b + 1), f k = ∑ k ∈ Finset.Ic
o a b, f k + …
· 使用定理 `Set.Ico_subset_Ico_right`：∀ {α : Type u_1} [inst : Preorder α] {a₁ a₂ b 
: α}, a₂ ≤ a₁ → Set.Ico b a₂ ⊆ Set.Ico b a₁
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `intervalIntegral.integral_add_adjacent_intervals`：integral_add_adjacent_
intervals (hab : IntervalIntegrable f μ a b) (hbc : IntervalIntegrable f μ b c) 
: ((∫ x in a..b, f x ∂μ) + ∫ x in b..c…
· 使用定理 `IntervalIntegrable.trans_iterate_Ico`：trans_iterate_Ico {a : Nat -> Real
} {m n : Nat} (hmn : m <= n) (hint : forall k in Ico m n, IntervalIntegrable f μ
 (a k) (a <| k + 1)) : Int…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `Set.Ico_subset_Ico`：Ico_subset_Ico (ha : a₂ <= a₁) (hb : b₁ <= b₂) : Ico
 a₁ b₁ subseteq Ico a₂ b₂
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
（共 32 条，此处仅展示前 30 条）
-/
theorem sum_integral_adjacent_intervals_Ico {a : ℕ → ℝ} {m n : ℕ} (hmn : m ≤ n)
    (hint : ∀ k ∈ Ico m n, IntervalIntegrable f μ (a k) (a <| k + 1)) :
    ∑ k ∈ Finset.Ico m n, ∫ x in a k..a <| k + 1, f x ∂μ = ∫ x in a m..a n, f x ∂μ := by
  revert hint
  refine Nat.le_induction ?_ ?_ n hmn
  · simp
  · intro p hmp IH h
    rw [Finset.sum_Ico_succ_top hmp, IH, integral_add_adjacent_intervals]
    · refine IntervalIntegrable.trans_iterate_Ico hmp fun k hk => h k ?_
      exact (Ico_subset_Ico le_rfl (Nat.le_succ _)) hk
    · apply h
      simp [hmp]
    · intro k hk
      exact h _ (Ico_subset_Ico_right p.le_succ hk)
/-
**intervalIntegral.sum_integral_adjacent_intervals** 是 Mathlib 中的一个定理，位于命名空间 `in
tervalIntegral`。
形式化陈述：sum_integral_adjacent_intervals {a : Nat -> Real} {n : Nat} (hint : forall
 k < n, IntervalIntegrable f μ (a k) (a <| k + 1)) : ∑ k in Finset.range n, ∫ x 
in a k..a k + 1, f x ∂μ = ∫ x in (a 0)..(a n), f x ∂μ
参数：hint : forall k < n, IntervalIntegrable f μ (a k) (a <| k + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.Ico_zero_eq_range`：Ico_zero_eq_range : Ico 0 a = range a
· 使用定理 `intervalIntegral.sum_integral_adjacent_intervals_Ico`：sum_integral_adjac
ent_intervals_Ico {a : Nat -> Real} {m n : Nat} (hmn : m <= n) (hint : forall k 
in Ico m n, IntervalIntegrable f μ (a k) (…
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem sum_integral_adjacent_intervals {a : ℕ → ℝ} {n : ℕ}
    (hint : ∀ k < n, IntervalIntegrable f μ (a k) (a <| k + 1)) :
    ∑ k ∈ Finset.range n, ∫ x in a k..a <| k + 1, f x ∂μ = ∫ x in (a 0)..(a n), f x ∂μ := by
  rw [← Nat.Ico_zero_eq_range]
  exact sum_integral_adjacent_intervals_Ico zero_le fun k hk => hint k hk.2
/-
**intervalIntegral.integral_interval_sub_left** 是 Mathlib 中的一个定理，位于命名空间 `interva
lIntegral`。
形式化陈述：integral_interval_sub_left (hab : IntervalIntegrable f μ a b) (hac : Inter
valIntegrable f μ a c) : ((∫ x in a..b, f x ∂μ) - ∫ x in a..c, f x ∂μ) = ∫ x in 
c..b, f x ∂μ
参数：hab : IntervalIntegrable f μ a b；hac : IntervalIntegrable f μ a c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sub_eq_of_eq_add'`：∀ {G : Type u_3} [inst : AddCommGroup G] {a b c : G},
 a = b + c → a - b = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `intervalIntegral.integral_add_adjacent_intervals`：integral_add_adjacent_
intervals (hab : IntervalIntegrable f μ a b) (hbc : IntervalIntegrable f μ b c) 
: ((∫ x in a..b, f x ∂μ) + ∫ x in b..c…
· 使用定理 `IntervalIntegrable.trans`：trans {a b c : Real} (hab : IntervalIntegrable
 f μ a b) (hbc : IntervalIntegrable f μ b c) : IntervalIntegrable f μ a c
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `IntervalIntegrable.symm`：∀ {ε : Type u_3} [inst : TopologicalSpace ε] [i
nst_1 : ENormedAddMonoid ε] {f : ℝ → ε} {a b : ℝ}   {μ : MeasureTheory.Measure ℝ
}, IntervalIn…
-/
theorem integral_interval_sub_left (hab : IntervalIntegrable f μ a b)
    (hac : IntervalIntegrable f μ a c) :
    ((∫ x in a..b, f x ∂μ) - ∫ x in a..c, f x ∂μ) = ∫ x in c..b, f x ∂μ :=
  sub_eq_of_eq_add' <| Eq.symm <| integral_add_adjacent_intervals hac (hac.symm.trans hab)
/-
**intervalIntegral.integral_interval_add_interval_comm** 是 Mathlib 中的一个定理，位于命名空间
 `intervalIntegral`。
形式化陈述：integral_interval_add_interval_comm (hab : IntervalIntegrable f μ a b) (hc
d : IntervalIntegrable f μ c d) (hac : IntervalIntegrable f μ a c) : ((∫ x in a.
.b, f x ∂μ) + ∫ x in c..d, f x ∂μ) = (∫ x in a..d, f x ∂μ) + ∫ x in c..b, f x ∂μ
参数：hab : IntervalIntegrable f μ a b；hcd : IntervalIntegrable f μ c d；hac : Inter
valIntegrable f μ a c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `intervalIntegral.integral_add_adjacent_intervals`：integral_add_adjacent_
intervals (hab : IntervalIntegrable f μ a b) (hbc : IntervalIntegrable f μ b c) 
: ((∫ x in a..b, f x ∂μ) + ∫ x in b..c…
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `add_left_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G),
 a + (b + c) = b + (a + c)
· 使用定理 `IntervalIntegrable.trans`：trans {a b c : Real} (hab : IntervalIntegrable
 f μ a b) (hbc : IntervalIntegrable f μ b c) : IntervalIntegrable f μ a c
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `IntervalIntegrable.symm`：∀ {ε : Type u_3} [inst : TopologicalSpace ε] [i
nst_1 : ENormedAddMonoid ε] {f : ℝ → ε} {a b : ℝ}   {μ : MeasureTheory.Measure ℝ
}, IntervalIn…
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem integral_interval_add_interval_comm (hab : IntervalIntegrable f μ a b)
    (hcd : IntervalIntegrable f μ c d) (hac : IntervalIntegrable f μ a c) :
    ((∫ x in a..b, f x ∂μ) + ∫ x in c..d, f x ∂μ) =
      (∫ x in a..d, f x ∂μ) + ∫ x in c..b, f x ∂μ := by
  rw [← integral_add_adjacent_intervals hac hcd, add_assoc, add_left_comm,
    integral_add_adjacent_intervals hac (hac.symm.trans hab), add_comm]
/-
**intervalIntegral.integral_interval_sub_interval_comm** 是 Mathlib 中的一个定理，位于命名空间
 `intervalIntegral`。
形式化陈述：integral_interval_sub_interval_comm (hab : IntervalIntegrable f μ a b) (hc
d : IntervalIntegrable f μ c d) (hac : IntervalIntegrable f μ a c) : ((∫ x in a.
.b, f x ∂μ) - ∫ x in c..d, f x ∂μ) = (∫ x in a..c, f x ∂μ) - ∫ x in b..d, f x ∂μ
参数：hab : IntervalIntegrable f μ a b；hcd : IntervalIntegrable f μ c d；hac : Inter
valIntegrable f μ a c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `intervalIntegral.integral_interval_add_interval_comm`：integral_interval_
add_interval_comm (hab : IntervalIntegrable f μ a b) (hcd : IntervalIntegrable f
 μ c d) (hac : IntervalIntegrable f μ a c)…
· 使用定理 `IntervalIntegrable.symm`：∀ {ε : Type u_3} [inst : TopologicalSpace ε] [i
nst_1 : ENormedAddMonoid ε] {f : ℝ → ε} {a b : ℝ}   {μ : MeasureTheory.Measure ℝ
}, IntervalIn…
· 使用定理 `IntervalIntegrable.trans`：trans {a b c : Real} (hab : IntervalIntegrable
 f μ a b) (hbc : IntervalIntegrable f μ b c) : IntervalIntegrable f μ a c
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integral_interval_sub_interval_comm (hab : IntervalIntegrable f μ a b)
    (hcd : IntervalIntegrable f μ c d) (hac : IntervalIntegrable f μ a c) :
    ((∫ x in a..b, f x ∂μ) - ∫ x in c..d, f x ∂μ) =
      (∫ x in a..c, f x ∂μ) - ∫ x in b..d, f x ∂μ := by
  simp only [sub_eq_add_neg, ← integral_symm,
    integral_interval_add_interval_comm hab hcd.symm (hac.trans hcd)]
/-
**intervalIntegral.integral_interval_sub_interval_comm'** 是 Mathlib 中的一个定理，位于命名空
间 `intervalIntegral`。
形式化陈述：integral_interval_sub_interval_comm' (hab : IntervalIntegrable f μ a b) (h
cd : IntervalIntegrable f μ c d) (hac : IntervalIntegrable f μ a c) : ((∫ x in a
..b, f x ∂μ) - ∫ x in c..d, f x ∂μ) = (∫ x in d..b, f x ∂μ) - ∫ x in c..a, f x ∂
μ
参数：hab : IntervalIntegrable f μ a b；hcd : IntervalIntegrable f μ c d；hac : Inter
valIntegrable f μ a c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intervalIntegral.integral_interval_sub_interval_comm`：integral_interval_
sub_interval_comm (hab : IntervalIntegrable f μ a b) (hcd : IntervalIntegrable f
 μ c d) (hac : IntervalIntegrable f μ a c)…
· 使用定理 `intervalIntegral.integral_symm`：integral_symm (a b) : ∫ x in b..a, f x ∂
μ = -∫ x in a..b, f x ∂μ
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `sub_eq_neg_add`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b :
 α), a - b = -b + a
-/
theorem integral_interval_sub_interval_comm' (hab : IntervalIntegrable f μ a b)
    (hcd : IntervalIntegrable f μ c d) (hac : IntervalIntegrable f μ a c) :
    ((∫ x in a..b, f x ∂μ) - ∫ x in c..d, f x ∂μ) =
      (∫ x in d..b, f x ∂μ) - ∫ x in c..a, f x ∂μ := by
  rw [integral_interval_sub_interval_comm hab hcd hac, integral_symm b d, integral_symm a c,
    sub_neg_eq_add, sub_eq_neg_add]
/-
**intervalIntegral.integral_Iic_sub_Iic** 是 Mathlib 中的一个定理，位于命名空间 `intervalInteg
ral`。
形式化陈述：integral_Iic_sub_Iic (ha : IntegrableOn f (Iic a) μ) (hb : IntegrableOn f 
(Iic b) μ) : ((∫ x in Iic b, f x ∂μ) - ∫ x in Iic a, f x ∂μ) = ∫ x in a..b, f x 
∂μ
参数：ha : IntegrableOn f (Iic a) μ；hb : IntegrableOn f (Iic b) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_iff_eq_add'`：∀ {G : Type u_3} [inst : AddCommGroup G] {a b c : G}
, a - b = c ↔ a = b + c
· 使用定理 `intervalIntegral.integral_of_le`：integral_of_le (h : a <= b) : ∫ x in a.
.b, f x ∂μ = ∫ x in Ioc a b, f x ∂μ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.setIntegral_union`：setIntegral_union (hst : Disjoint s t) 
(ht : MeasurableSet t) (hfs : IntegrableOn f s μ) (hft : IntegrableOn f t μ) : ∫
 x in s union t, f x …
· 使用定理 `Set.Iic_disjoint_Ioc`：Iic_disjoint_Ioc (h : a <= b) : Disjoint (Iic a) (
Ioc b c)
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `measurableSet_Ioc`：measurableSet_Ioc [ClosedIicTopology α] : MeasurableS
et (Ioc a b)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `MeasureTheory.IntegrableOn.mono_set`：∀ {α : Type u_1} {ε : Type u_3} {mα
 : MeasurableSpace α} {f : α → ε} {s t : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.Iic_union_Ioc_eq_Iic`：Iic_union_Ioc_eq_Iic (h : a <= b) : Iic a unio
n Ioc a b = Iic b
· 使用定理 `intervalIntegral.integral_symm`：integral_symm (a b) : ∫ x in b..a, f x ∂
μ = -∫ x in a..b, f x ∂μ
· 使用定理 `le_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b 
→ b ≤ a
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
-/
theorem integral_Iic_sub_Iic (ha : IntegrableOn f (Iic a) μ) (hb : IntegrableOn f (Iic b) μ) :
    ((∫ x in Iic b, f x ∂μ) - ∫ x in Iic a, f x ∂μ) = ∫ x in a..b, f x ∂μ := by
  wlog hab : a ≤ b generalizing a b
  · rw [integral_symm, ← this hb ha (le_of_not_ge hab), neg_sub]
  rw [sub_eq_iff_eq_add', integral_of_le hab, ← setIntegral_union (Iic_disjoint_Ioc le_rfl),
    Iic_union_Ioc_eq_Iic hab]
  exacts [measurableSet_Ioc, ha, hb.mono_set fun _ => And.right]
/-
**intervalIntegral.integral_interval_add_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `interval
Integral`。
形式化陈述：integral_interval_add_Ioi (ha : IntegrableOn f (Ioi a) μ) (hb : Integrable
On f (Ioi b) μ) : ∫ (x : Real) in a..b, f x ∂μ + ∫ (x : Real) in Ioi b, f x ∂μ =
 ∫ (x : Real) in Ioi a, f x ∂μ
参数：ha : IntegrableOn f (Ioi a) μ；hb : IntegrableOn f (Ioi b) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intervalIntegral.integral_of_le`：integral_of_le (h : a <= b) : ∫ x in a.
.b, f x ∂μ = ∫ x in Ioc a b, f x ∂μ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.setIntegral_union`：setIntegral_union (hst : Disjoint s t) 
(ht : MeasurableSet t) (hfs : IntegrableOn f s μ) (hft : IntegrableOn f t μ) : ∫
 x in s union t, f x …
· 使用定理 `Set.Ioc_disjoint_Ioi_same`：Ioc_disjoint_Ioi_same : Disjoint (Ioc a b) (I
oi b)
· 使用定理 `measurableSet_Ioi`：measurableSet_Ioi [ClosedIicTopology α] : MeasurableS
et (Ioi a)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `MeasureTheory.IntegrableOn.mono_set`：∀ {α : Type u_1} {ε : Type u_3} {mα
 : MeasurableSpace α} {f : α → ε} {s t : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace …
· 使用定理 `Set.Ioc_subset_Ioi_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc b a ⊆ Set.Ioi b
· 使用定理 `Set.Ioc_union_Ioi_eq_Ioi`：Ioc_union_Ioi_eq_Ioi (h : a <= b) : Ioc a b un
ion Ioi b = Ioi a
· 使用定理 `intervalIntegral.integral_symm`：integral_symm (a b) : ∫ x in b..a, f x ∂
μ = -∫ x in a..b, f x ∂μ
· 使用定理 `le_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b 
→ b ≤ a
-/
theorem integral_interval_add_Ioi (ha : IntegrableOn f (Ioi a) μ)
    (hb : IntegrableOn f (Ioi b) μ) :
    ∫ (x : ℝ) in a..b, f x ∂μ + ∫ (x : ℝ) in Ioi b, f x ∂μ
    = ∫ (x : ℝ) in Ioi a, f x ∂μ := by
  wlog hab : a ≤ b generalizing a b
  · rw [integral_symm, ← this hb ha (le_of_not_ge hab)]; grind
  rw [integral_of_le hab, ← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
    (ha.mono_set Ioc_subset_Ioi_self) hb, Ioc_union_Ioi_eq_Ioi hab]
/-
**intervalIntegral.integral_interval_add_Ioi'** 是 Mathlib 中的一个定理，位于命名空间 `interva
lIntegral`。
形式化陈述：integral_interval_add_Ioi' (ha : IntervalIntegrable f μ a b) (hb : Integra
bleOn f (Ioi b) μ) : ∫ (x : Real) in a..b, f x ∂μ + ∫ (x : Real) in Ioi b, f x ∂
μ = ∫ (x : Real) in Ioi a, f x ∂μ
参数：ha : IntervalIntegrable f μ a b；hb : IntegrableOn f (Ioi b) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intervalIntegral.integral_interval_add_Ioi`：integral_interval_add_Ioi (h
a : IntegrableOn f (Ioi a) μ) (hb : IntegrableOn f (Ioi b) μ) : ∫ (x : Real) in 
a..b, f x ∂μ + ∫ (x : Real) in I…
· 使用定理 `MeasureTheory.IntegrableOn.union`：∀ {α : Type u_1} {ε : Type u_3} {mα : 
MeasurableSpace α} {f : α → ε} {s t : Set α} {μ : MeasureTheory.Measure α}   [in
st : TopologicalSpace …
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `intervalIntegrable_iff_integrableOn_Ioc_of_le`：intervalIntegrable_iff_in
tegrableOn_Ioc_of_le (hab : a <= b) : IntervalIntegrable f μ a b ↔ IntegrableOn 
f (Ioc a b) μ
· 使用定理 `Set.Ioc_union_Ioi_eq_Ioi`：Ioc_union_Ioi_eq_Ioi (h : a <= b) : Ioc a b un
ion Ioi b = Ioi a
· 使用定理 `MeasureTheory.IntegrableOn.mono_set`：∀ {α : Type u_1} {ε : Type u_3} {mα
 : MeasurableSpace α} {f : α → ε} {s t : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace …
· 使用定理 `Set.Ioi_subset_Ioi`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b ≤ 
a → Set.Ioi a ⊆ Set.Ioi b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem integral_interval_add_Ioi' (ha : IntervalIntegrable f μ a b)
    (hb : IntegrableOn f (Ioi b) μ) :
    ∫ (x : ℝ) in a..b, f x ∂μ + ∫ (x : ℝ) in Ioi b, f x ∂μ
    = ∫ (x : ℝ) in Ioi a, f x ∂μ := by
  rw [integral_interval_add_Ioi _ hb]
  by_cases! h : a ≤ b
  · exact (Ioc_union_Ioi_eq_Ioi h) ▸ IntegrableOn.union
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le h).1 ha) hb
  · exact hb.mono_set <| Ioi_subset_Ioi h.le
/-
**intervalIntegral.integral_Ioi_sub_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `intervalInteg
ral`。
形式化陈述：integral_Ioi_sub_Ioi (hf : IntegrableOn f (Ioi a) μ) (hab : a <= b) : ∫ x 
in Ioi a, f x ∂μ - ∫ x in Ioi b, f x ∂μ = ∫ x in a..b, f x ∂μ
参数：hf : IntegrableOn f (Ioi a) μ；hab : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sub_eq_of_eq_add`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a = 
c + b → a - b = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `intervalIntegral.integral_interval_add_Ioi`：integral_interval_add_Ioi (h
a : IntegrableOn f (Ioi a) μ) (hb : IntegrableOn f (Ioi b) μ) : ∫ (x : Real) in 
a..b, f x ∂μ + ∫ (x : Real) in I…
· 使用定理 `MeasureTheory.IntegrableOn.mono_set`：∀ {α : Type u_1} {ε : Type u_3} {mα
 : MeasurableSpace α} {f : α → ε} {s t : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace …
· 使用定理 `Set.Ioi_subset_Ioi`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b ≤ 
a → Set.Ioi a ⊆ Set.Ioi b
-/
theorem integral_Ioi_sub_Ioi (hf : IntegrableOn f (Ioi a) μ) (hab : a ≤ b) :
    ∫ x in Ioi a, f x ∂μ - ∫ x in Ioi b, f x ∂μ = ∫ x in a..b, f x ∂μ :=
  sub_eq_of_eq_add (integral_interval_add_Ioi hf (hf.mono_set (Ioi_subset_Ioi hab))).symm
/-
**intervalIntegral.integral_Ioi_sub_Ioi'** 是 Mathlib 中的一个定理，位于命名空间 `intervalInte
gral`。
形式化陈述：integral_Ioi_sub_Ioi' (hf : IntegrableOn f (Ioi a) μ) (hg : IntegrableOn f
 (Ioi b) μ) : ∫ x in Ioi a, f x ∂μ - ∫ x in Ioi b, f x ∂μ = ∫ x in a..b, f x ∂μ
参数：hf : IntegrableOn f (Ioi a) μ；hg : IntegrableOn f (Ioi b) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `intervalIntegral.integral_Ioi_sub_Ioi`：integral_Ioi_sub_Ioi (hf : Integr
ableOn f (Ioi a) μ) (hab : a <= b) : ∫ x in Ioi a, f x ∂μ - ∫ x in Ioi b, f x ∂μ
 = ∫ x in a..b, f x ∂μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intervalIntegral.integral_symm`：integral_symm (a b) : ∫ x in b..a, f x ∂
μ = -∫ x in a..b, f x ∂μ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
-/
theorem integral_Ioi_sub_Ioi' (hf : IntegrableOn f (Ioi a) μ) (hg : IntegrableOn f (Ioi b) μ) :
    ∫ x in Ioi a, f x ∂μ - ∫ x in Ioi b, f x ∂μ = ∫ x in a..b, f x ∂μ := by
  wlog! hab : a ≤ b generalizing a b
  · rw [integral_symm, ← this hg hf hab.le, neg_sub]
  exact integral_Ioi_sub_Ioi hf hab
/-
**intervalIntegral.integral_Iio_sub_Iio** 是 Mathlib 中的一个定理，位于命名空间 `intervalInteg
ral`。
形式化陈述：integral_Iio_sub_Iio (hf : IntegrableOn f (Iio b) μ) (hab : a <= b) : ∫ x 
in Iio b, f x ∂μ - ∫ x in Iio a, f x ∂μ = ∫ x in Ico a b, f x ∂μ
参数：hf : IntegrableOn f (Iio b) μ；hab : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IntegrableOn.mono_set`：∀ {α : Type u_1} {ε : Type u_3} {mα
 : MeasurableSpace α} {f : α → ε} {s t : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace …
· 使用定理 `Set.Iio_subset_Iio`：Iio_subset_Iio (h : a <= b) : Iio a subseteq Iio b
· 使用定理 `Set.Ico_subset_Iio_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ico a b ⊆ Set.Iio b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_iff_eq_add'`：∀ {G : Type u_3} [inst : AddCommGroup G] {a b c : G}
, a - b = c ↔ a = b + c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.setIntegral_union`：setIntegral_union (hst : Disjoint s t) 
(ht : MeasurableSet t) (hfs : IntegrableOn f s μ) (hft : IntegrableOn f t μ) : ∫
 x in s union t, f x …
· 使用定理 `measurableSet_Ico`：measurableSet_Ico [ClosedIciTopology α] : MeasurableS
et (Ico a b)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Set.Iio_union_Ico_eq_Iio`：Iio_union_Ico_eq_Iio (h : a <= b) : Iio a unio
n Ico a b = Iio b
-/
theorem integral_Iio_sub_Iio (hf : IntegrableOn f (Iio b) μ) (hab : a ≤ b) :
    ∫ x in Iio b, f x ∂μ - ∫ x in Iio a, f x ∂μ = ∫ x in Ico a b, f x ∂μ := by
  have ha : IntegrableOn f (Iio a) μ := hf.mono_set (Iio_subset_Iio hab)
  have h : IntegrableOn f (Ico a b) μ := hf.mono_set Ico_subset_Iio_self
  rw [sub_eq_iff_eq_add', ← setIntegral_union (by grind) measurableSet_Ico ha h,
      Iio_union_Ico_eq_Iio hab]
/-
**intervalIntegral.integral_Iio_sub_Iio'** 是 Mathlib 中的一个定理，位于命名空间 `intervalInte
gral`。
形式化陈述：integral_Iio_sub_Iio' [NullSingletonClass μ] (hf : IntegrableOn f (Iio b) 
μ) (hg : IntegrableOn f (Iio a) μ) : ∫ x in Iio b, f x ∂μ - ∫ x in Iio a, f x ∂μ
 = ∫ x in a..b, f x ∂μ
参数：hf : IntegrableOn f (Iio b) μ；hg : IntegrableOn f (Iio a) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intervalIntegral.integral_Iio_sub_Iio`：integral_Iio_sub_Iio (hf : Integr
ableOn f (Iio b) μ) (hab : a <= b) : ∫ x in Iio b, f x ∂μ - ∫ x in Iio a, f x ∂μ
 = ∫ x in Ico a b, f x ∂μ
· 使用定理 `intervalIntegral.integral_of_le`：integral_of_le (h : a <= b) : ∫ x in a.
.b, f x ∂μ = ∫ x in Ioc a b, f x ∂μ
· 使用定理 `MeasureTheory.integral_Ico_eq_integral_Ioc`：integral_Ico_eq_integral_Ioc
 : ∫ t in Ico x y, f t ∂μ = ∫ t in Ioc x y, f t ∂μ
· 使用定理 `intervalIntegral.integral_symm`：integral_symm (a b) : ∫ x in b..a, f x ∂
μ = -∫ x in a..b, f x ∂μ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
-/
theorem integral_Iio_sub_Iio' [NullSingletonClass μ] (hf : IntegrableOn f (Iio b) μ)
    (hg : IntegrableOn f (Iio a) μ) :
    ∫ x in Iio b, f x ∂μ - ∫ x in Iio a, f x ∂μ = ∫ x in a..b, f x ∂μ := by
  wlog! hab : a ≤ b generalizing a b
  · rw [integral_symm, ← this hg hf hab.le, neg_sub]
  rw [integral_Iio_sub_Iio hf hab, integral_of_le hab, integral_Ico_eq_integral_Ioc]
/-
**intervalIntegral.integral_Ici_sub_Ici** 是 Mathlib 中的一个定理，位于命名空间 `intervalInteg
ral`。
形式化陈述：integral_Ici_sub_Ici (hf : IntegrableOn f (Ici a) μ) (hab : a <= b) : ∫ x 
in Ici a, f x ∂μ - ∫ x in Ici b, f x ∂μ = ∫ x in Ico a b, f x ∂μ
参数：hf : IntegrableOn f (Ici a) μ；hab : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IntegrableOn.mono_set`：∀ {α : Type u_1} {ε : Type u_3} {mα
 : MeasurableSpace α} {f : α → ε} {s t : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.Ici_subset_Ici`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.
Ici a ⊆ Set.Ici b ↔ b ≤ a
· 使用定理 `Set.Ico_subset_Ici_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ico b a ⊆ Set.Ici b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_iff_eq_add'`：∀ {G : Type u_3} [inst : AddCommGroup G] {a b c : G}
, a - b = c ↔ a = b + c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.setIntegral_union`：setIntegral_union (hst : Disjoint s t) 
(ht : MeasurableSet t) (hfs : IntegrableOn f s μ) (hft : IntegrableOn f t μ) : ∫
 x in s union t, f x …
· 使用定理 `measurableSet_Ico`：measurableSet_Ico [ClosedIciTopology α] : MeasurableS
et (Ico a b)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
· 使用定理 `Set.Ico_union_Ici_eq_Ici`：Ico_union_Ici_eq_Ici (h : a <= b) : Ico a b un
ion Ici b = Ici a
-/
theorem integral_Ici_sub_Ici (hf : IntegrableOn f (Ici a) μ) (hab : a ≤ b) :
    ∫ x in Ici a, f x ∂μ - ∫ x in Ici b, f x ∂μ = ∫ x in Ico a b, f x ∂μ := by
  have ha : IntegrableOn f (Ici b) μ := hf.mono_set (Ici_subset_Ici.2 hab)
  have h : IntegrableOn f (Ico a b) μ := hf.mono_set Ico_subset_Ici_self
  rw [sub_eq_iff_eq_add', ← setIntegral_union (by grind) measurableSet_Ico ha h, union_comm,
    Ico_union_Ici_eq_Ici hab]
/-
**intervalIntegral.integral_Ici_sub_Ici'** 是 Mathlib 中的一个定理，位于命名空间 `intervalInte
gral`。
形式化陈述：integral_Ici_sub_Ici' [NullSingletonClass μ] (hf : IntegrableOn f (Ici a) 
μ) (hg : IntegrableOn f (Ici b) μ) : ∫ x in Ici a, f x ∂μ - ∫ x in Ici b, f x ∂μ
 = ∫ x in a..b, f x ∂μ
参数：hf : IntegrableOn f (Ici a) μ；hg : IntegrableOn f (Ici b) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intervalIntegral.integral_Ici_sub_Ici`：integral_Ici_sub_Ici (hf : Integr
ableOn f (Ici a) μ) (hab : a <= b) : ∫ x in Ici a, f x ∂μ - ∫ x in Ici b, f x ∂μ
 = ∫ x in Ico a b, f x ∂μ
· 使用定理 `intervalIntegral.integral_of_le`：integral_of_le (h : a <= b) : ∫ x in a.
.b, f x ∂μ = ∫ x in Ioc a b, f x ∂μ
· 使用定理 `MeasureTheory.integral_Ico_eq_integral_Ioc`：integral_Ico_eq_integral_Ioc
 : ∫ t in Ico x y, f t ∂μ = ∫ t in Ioc x y, f t ∂μ
· 使用定理 `intervalIntegral.integral_symm`：integral_symm (a b) : ∫ x in b..a, f x ∂
μ = -∫ x in a..b, f x ∂μ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
-/
theorem integral_Ici_sub_Ici' [NullSingletonClass μ] (hf : IntegrableOn f (Ici a) μ)
    (hg : IntegrableOn f (Ici b) μ) :
    ∫ x in Ici a, f x ∂μ - ∫ x in Ici b, f x ∂μ = ∫ x in a..b, f x ∂μ := by
  wlog! hab : a ≤ b generalizing a b
  · rw [integral_symm, ← this hg hf hab.le, neg_sub]
  rw [integral_Ici_sub_Ici hf hab, integral_of_le hab, integral_Ico_eq_integral_Ioc]
/-
**intervalIntegral.integral_Iic_add_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `intervalInteg
ral`。
形式化陈述：integral_Iic_add_Ioi (h_left : IntegrableOn f (Iic b) μ) (h_right : Integr
ableOn f (Ioi b) μ) : (∫ x in Iic b, f x ∂μ) + (∫ x in Ioi b, f x ∂μ) = ∫ (x : R
eal), f x ∂μ
参数：h_left : IntegrableOn f (Iic b) μ；h_right : IntegrableOn f (Ioi b) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Iic_union_Ioi`：Iic_union_Ioi : Iic a union Ioi a = univ
· 使用定理 `MeasureTheory.Measure.restrict_univ`：restrict_univ : μ.restrict univ = μ
· 使用定理 `MeasureTheory.setIntegral_union`：setIntegral_union (hst : Disjoint s t) 
(ht : MeasurableSet t) (hfs : IntegrableOn f s μ) (hft : IntegrableOn f t μ) : ∫
 x in s union t, f x …
· 使用定理 `Set.Iic_disjoint_Ioi`：Iic_disjoint_Ioi (h : a <= b) : Disjoint (Iic a) (
Ioi b)
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `measurableSet_Ioi`：measurableSet_Ioi [ClosedIicTopology α] : MeasurableS
et (Ioi a)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
-/
theorem integral_Iic_add_Ioi (h_left : IntegrableOn f (Iic b) μ)
    (h_right : IntegrableOn f (Ioi b) μ) :
    (∫ x in Iic b, f x ∂μ) + (∫ x in Ioi b, f x ∂μ) = ∫ (x : ℝ), f x ∂μ := by
  convert! (setIntegral_union (Iic_disjoint_Ioi <| Eq.le rfl) measurableSet_Ioi h_left h_right).symm
  rw [Iic_union_Ioi, Measure.restrict_univ]
/-
**intervalIntegral.integral_Iio_add_Ici** 是 Mathlib 中的一个定理，位于命名空间 `intervalInteg
ral`。
形式化陈述：integral_Iio_add_Ici (h_left : IntegrableOn f (Iio b) μ) (h_right : Integr
ableOn f (Ici b) μ) : (∫ x in Iio b, f x ∂μ) + (∫ x in Ici b, f x ∂μ) = ∫ (x : R
eal), f x ∂μ
参数：h_left : IntegrableOn f (Iio b) μ；h_right : IntegrableOn f (Ici b) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Iio_union_Ici`：Iio_union_Ici : Iio a union Ici a = univ
· 使用定理 `MeasureTheory.Measure.restrict_univ`：restrict_univ : μ.restrict univ = μ
· 使用定理 `MeasureTheory.setIntegral_union`：setIntegral_union (hst : Disjoint s t) 
(ht : MeasurableSet t) (hfs : IntegrableOn f s μ) (hft : IntegrableOn f t μ) : ∫
 x in s union t, f x …
· 使用定理 `Set.Iio_disjoint_Ici`：Iio_disjoint_Ici (h : a <= b) : Disjoint (Iio a) (
Ici b)
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `measurableSet_Ici`：measurableSet_Ici [ClosedIciTopology α] : MeasurableS
et (Ici a)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
-/
theorem integral_Iio_add_Ici (h_left : IntegrableOn f (Iio b) μ)
    (h_right : IntegrableOn f (Ici b) μ) :
    (∫ x in Iio b, f x ∂μ) + (∫ x in Ici b, f x ∂μ) = ∫ (x : ℝ), f x ∂μ := by
  convert! (setIntegral_union (Iio_disjoint_Ici <| Eq.le rfl) measurableSet_Ici h_left h_right).symm
  rw [Iio_union_Ici, Measure.restrict_univ]

/-- If `μ` is a finite measure then `∫ x in a..b, c ∂μ = (μ (Iic b) - μ (Iic a)) • c`. -/
/-
**intervalIntegral.integral_const_of_cdf** 是 Mathlib 中的一个定理，位于命名空间 `intervalInte
gral`。
形式化陈述：integral_const_of_cdf [CompleteSpace E] [IsFiniteMeasure μ] (c : E) : ∫ _ 
in a..b, c ∂μ = (μ.real (Iic b) - μ.real (Iic a)) • c
参数：c : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `intervalIntegral.integral_Iic_sub_Iic`：integral_Iic_sub_Iic (ha : Integr
ableOn f (Iic a) μ) (hb : IntegrableOn f (Iic b) μ) : ((∫ x in Iic b, f x ∂μ) - 
∫ x in Iic a, f x ∂μ) = ∫ x…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True

--- 原说明 ---
If `μ` is a finite measure then `∫ x in a..b, c ∂μ = (μ (Iic b) - μ (Iic a)) • c
`.
-/
theorem integral_const_of_cdf [CompleteSpace E] [IsFiniteMeasure μ] (c : E) :
    ∫ _ in a..b, c ∂μ = (μ.real (Iic b) - μ.real (Iic a)) • c := by
  simp only [sub_smul, ← setIntegral_const]
  refine (integral_Iic_sub_Iic ?_ ?_).symm <;> simp
/-
**intervalIntegral.integral_eq_integral_of_support_subset** 是 Mathlib 中的一个定理，位于命
名空间 `intervalIntegral`。
形式化陈述：integral_eq_integral_of_support_subset {a b} (h : support f subseteq Ioc a
 b) : ∫ x in a..b, f x ∂μ = ∫ x, f x ∂μ
参数：h : support f subseteq Ioc a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intervalIntegral.integral_of_le`：integral_of_le (h : a <= b) : ∫ x in a.
.b, f x ∂μ = ∫ x in Ioc a b, f x ∂μ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_indicator`：integral_indicator (hs : MeasurableSet
 s) : ∫ x, indicator s f x ∂μ = ∫ x in s, f x ∂μ
· 使用定理 `measurableSet_Ioc`：measurableSet_Ioc [ClosedIicTopology α] : MeasurableS
et (Ioc a b)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.indicator_eq_self`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {
s : Set α} {f : α → M}, s.indicator f = f ↔ Function.support f ⊆ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.support_eq_empty_iff`：∀ {ι : Type u_1} {M : Type u_3} [inst : Z
ero M] {f : ι → M}, Function.support f = ∅ ↔ f = 0
· 使用定理 `Set.subset_empty_iff`：subset_empty_iff {s : Set α} : s subseteq ∅ ↔ s = 
∅
· 使用定理 `Set.Ioc_eq_empty`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, ¬b < a
 → Set.Ioc b a = ∅
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `intervalIntegral.integral_zero`：integral_zero : (∫ _ in a..b, (0 : E) ∂μ
) = 0
· 使用定理 `MeasureTheory.integral_zero`：integral_zero : ∫ _ : α, (0 : G) ∂μ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integral_eq_integral_of_support_subset {a b} (h : support f ⊆ Ioc a b) :
    ∫ x in a..b, f x ∂μ = ∫ x, f x ∂μ := by
  rcases le_total a b with hab | hab
  · rw [integral_of_le hab, ← integral_indicator measurableSet_Ioc, indicator_eq_self.2 h]
  · rw [Ioc_eq_empty hab.not_gt, subset_empty_iff, support_eq_empty_iff] at h
    simp [h]
/-
**intervalIntegral.integral_congr_ae'** 是 Mathlib 中的一个定理，位于命名空间 `intervalIntegra
l`。
形式化陈述：integral_congr_ae' (h : forallᵐ x ∂μ, x in Ioc a b -> f x = g x) (h' : for
allᵐ x ∂μ, x in Ioc b a -> f x = g x) : ∫ x in a..b, f x ∂μ = ∫ x in a..b, g x ∂
μ
参数：h : forallᵐ x ∂μ, x in Ioc a b -> f x = g x；h' : forallᵐ x ∂μ, x in Ioc b a -
> f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.setIntegral_congr_ae`：setIntegral_congr_ae (hs : Measurabl
eSet s) (h : forallᵐ x ∂μ, x in s -> f x = g x) : ∫ x in s, f x ∂μ = ∫ x in s, g
 x ∂μ
· 使用定理 `measurableSet_Ioc`：measurableSet_Ioc [ClosedIicTopology α] : MeasurableS
et (Ioc a b)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integral_congr_ae' (h : ∀ᵐ x ∂μ, x ∈ Ioc a b → f x = g x)
    (h' : ∀ᵐ x ∂μ, x ∈ Ioc b a → f x = g x) : ∫ x in a..b, f x ∂μ = ∫ x in a..b, g x ∂μ := by
  simp only [intervalIntegral, setIntegral_congr_ae measurableSet_Ioc h,
    setIntegral_congr_ae measurableSet_Ioc h']
/-
**intervalIntegral.integral_congr_ae** 是 Mathlib 中的一个定理，位于命名空间 `intervalIntegral
`。
形式化陈述：integral_congr_ae (h : forallᵐ x ∂μ, x in Ι a b -> f x = g x) : ∫ x in a..
b, f x ∂μ = ∫ x in a..b, g x ∂μ
参数：h : forallᵐ x ∂μ, x in Ι a b -> f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `intervalIntegral.integral_congr_ae'`：integral_congr_ae' (h : forallᵐ x ∂
μ, x in Ioc a b -> f x = g x) (h' : forallᵐ x ∂μ, x in Ioc b a -> f x = g x) : ∫
 x in a..b, f x ∂μ = ∫ x …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.ae_uIoc_iff`：ae_uIoc_iff [LinearOrder α] {a b : α} {P : α 
-> Prop} : (forallᵐ x ∂μ, x in Ι a b -> P x) ↔ (forallᵐ x ∂μ, x in Ioc a b -> P 
x) ∧ forallᵐ x …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem integral_congr_ae (h : ∀ᵐ x ∂μ, x ∈ Ι a b → f x = g x) :
    ∫ x in a..b, f x ∂μ = ∫ x in a..b, g x ∂μ :=
  integral_congr_ae' (ae_uIoc_iff.mp h).1 (ae_uIoc_iff.mp h).2
/-
**intervalIntegral.integral_congr_uIoo** 是 Mathlib 中的一个定理，位于命名空间 `intervalIntegr
al`。
形式化陈述：integral_congr_uIoo [NullSingletonClass μ] (h : (uIoo a b).EqOn f g) : ∫ x
 in a..b, f x ∂μ = ∫ x in a..b, g x ∂μ
参数：h : (uIoo a b).EqOn f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `intervalIntegral.integral_congr_ae`：integral_congr_ae (h : forallᵐ x ∂μ,
 x in Ι a b -> f x = g x) : ∫ x in a..b, f x ∂μ = ∫ x in a..b, g x ∂μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.ae_ne`：∀ {α : Type u_1} {m0 : MeasurableSpace α} (
μ : MeasureTheory.Measure α) [MeasureTheory.NullSingletonClass μ] (a : α),   ∀ᵐ 
(x : α) ∂μ, x ≠ a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem integral_congr_uIoo [NullSingletonClass μ] (h : (uIoo a b).EqOn f g) :
    ∫ x in a..b, f x ∂μ = ∫ x in a..b, g x ∂μ := by
  apply integral_congr_ae
  filter_upwards [μ.ae_ne <| a ⊔ b] with x _ hx
  exact h ⟨hx.left, lt_of_le_of_ne hx.right ‹_›⟩
/-
**intervalIntegral.integral_congr_Ioo_of_le** 是 Mathlib 中的一个定理，位于命名空间 `intervalI
ntegral`。
形式化陈述：integral_congr_Ioo_of_le [NullSingletonClass μ] (hab : a <= b) (h : (Ioo a
 b).EqOn f g) : ∫ x in a..b, f x ∂μ = ∫ x in a..b, g x ∂μ
参数：hab : a <= b；h : (Ioo a b).EqOn f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `intervalIntegral.integral_congr_uIoo`：integral_congr_uIoo [NullSingleton
Class μ] (h : (uIoo a b).EqOn f g) : ∫ x in a..b, f x ∂μ = ∫ x in a..b, g x ∂μ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.uIoo_of_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b
 → Set.uIoo a b = Set.Ioo a b
-/
theorem integral_congr_Ioo_of_le [NullSingletonClass μ] (hab : a ≤ b) (h : (Ioo a b).EqOn f g) :
    ∫ x in a..b, f x ∂μ = ∫ x in a..b, g x ∂μ :=
  integral_congr_uIoo <| uIoo_of_le hab ▸ h

/-- Integrals are equal for functions that agree almost everywhere for the restricted measure. -/
/-
**intervalIntegral.integral_congr_ae_restrict** 是 Mathlib 中的一个定理，位于命名空间 `interva
lIntegral`。
形式化陈述：integral_congr_ae_restrict {a b : Real} {f g : Real -> E} {μ : Measure Rea
l} (h : f =ᵐ[μ.restrict (Ι a b)] g) : ∫ x in a..b, f x ∂μ = ∫ x in a..b, g x ∂μ
参数：h : f =ᵐ[μ.restrict (Ι a b)] g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `intervalIntegral.integral_congr_ae`：integral_congr_ae (h : forallᵐ x ∂μ,
 x in Ι a b -> f x = g x) : ∫ x in a..b, f x ∂μ = ∫ x in a..b, g x ∂μ
· 使用定理 `MeasureTheory.ae_imp_of_ae_restrict`：ae_imp_of_ae_restrict {s : Set α} {
p : α -> Prop} (h : forallᵐ x ∂μ.restrict s, p x) : forallᵐ x ∂μ, x in s -> p x

--- 原说明 ---
Integrals are equal for functions that agree almost everywhere for the restricte
d measure.
-/
theorem integral_congr_ae_restrict {a b : ℝ} {f g : ℝ → E} {μ : Measure ℝ}
    (h : f =ᵐ[μ.restrict (Ι a b)] g) :
    ∫ x in a..b, f x ∂μ = ∫ x in a..b, g x ∂μ :=
  integral_congr_ae (ae_imp_of_ae_restrict h)

/-- Integrals are invariant when functions change along discrete sets. -/
/-
**intervalIntegral.integral_congr_codiscreteWithin** 是 Mathlib 中的一个定理，位于命名空间 `in
tervalIntegral`。
形式化陈述：integral_congr_codiscreteWithin {a b : Real} {f₁ f₂ : Real -> Real} (hf : 
f₁ =ᶠ[codiscreteWithin (Ι a b)] f₂) : ∫ (x : Real) in a..b, f₁ x = ∫ (x : Real) 
in a..b, f₂ x
参数：hf : f₁ =ᶠ[codiscreteWithin (Ι a b)] f₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `intervalIntegral.integral_congr_ae_restrict`：integral_congr_ae_restrict 
{a b : Real} {f g : Real -> E} {μ : Measure Real} (h : f =ᵐ[μ.restrict (Ι a b)] 
g) : ∫ x in a..b, f x ∂μ = ∫ x in…
· 使用定理 `ae_restrict_le_codiscreteWithin`：ae_restrict_le_codiscreteWithin {α : Ty
pe*} [MeasurableSpace α] [TopologicalSpace α] [SecondCountableTopology α] {μ : M
easure α} [NullSingle…
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `measurableSet_uIoc`：measurableSet_uIoc [ClosedIicTopology α] : Measurabl
eSet (uIoc a b)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ

--- 原说明 ---
Integrals are invariant when functions change along discrete sets.
-/
theorem integral_congr_codiscreteWithin {a b : ℝ} {f₁ f₂ : ℝ → ℝ}
    (hf : f₁ =ᶠ[codiscreteWithin (Ι a b)] f₂) :
    ∫ (x : ℝ) in a..b, f₁ x = ∫ (x : ℝ) in a..b, f₂ x :=
  integral_congr_ae_restrict (ae_restrict_le_codiscreteWithin measurableSet_uIoc hf)
/-
**intervalIntegral.integral_zero_ae** 是 Mathlib 中的一个定理，位于命名空间 `intervalIntegral`
。
形式化陈述：integral_zero_ae (h : forallᵐ x ∂μ, x in Ι a b -> f x = 0) : ∫ x in a..b, 
f x ∂μ = 0
参数：h : forallᵐ x ∂μ, x in Ι a b -> f x = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `intervalIntegral.integral_congr_ae`：integral_congr_ae (h : forallᵐ x ∂μ,
 x in Ι a b -> f x = g x) : ∫ x in a..b, f x ∂μ = ∫ x in a..b, g x ∂μ
· 使用定理 `intervalIntegral.integral_zero`：integral_zero : (∫ _ in a..b, (0 : E) ∂μ
) = 0
-/
theorem integral_zero_ae (h : ∀ᵐ x ∂μ, x ∈ Ι a b → f x = 0) : ∫ x in a..b, f x ∂μ = 0 :=
  calc
    ∫ x in a..b, f x ∂μ = ∫ _ in a..b, 0 ∂μ := integral_congr_ae h
    _ = 0 := integral_zero

nonrec theorem integral_indicator {a₁ a₂ a₃ : ℝ} (h : a₂ ∈ Icc a₁ a₃) :
    ∫ x in a₁..a₃, indicator {x | x ≤ a₂} f x ∂μ = ∫ x in a₁..a₂, f x ∂μ := by
  have : {x | x ≤ a₂} ∩ Ioc a₁ a₃ = Ioc a₁ a₂ := Iic_inter_Ioc_of_le h.2
  rw [integral_of_le h.1, integral_of_le (h.1.trans h.2), integral_indicator,
    Measure.restrict_restrict, this]
  · exact measurableSet_Iic
  all_goals apply measurableSet_Iic

end OrderClosedTopology

section

variable {f g : ℝ → ℝ} {a b : ℝ} {μ : Measure ℝ}

/-
**intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae** 是 Mathlib 中的一个定理，位于
命名空间 `intervalIntegral`。
形式化陈述：integral_eq_zero_iff_of_le_of_nonneg_ae (hab : a <= b) (hf : 0 <=ᵐ[μ.restr
ict (Ioc a b)] f) (hfi : IntervalIntegrable f μ a b) : ∫ x in a..b, f x ∂μ = 0 ↔
 f =ᵐ[μ.restrict (Ioc a b)] 0
参数：hab : a <= b；hf : 0 <=ᵐ[μ.restrict (Ioc a b)] f；hfi : IntervalIntegrable f μ 
a b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intervalIntegral.integral_of_le`：integral_of_le (h : a <= b) : ∫ x in a.
.b, f x ∂μ = ∫ x in Ioc a b, f x ∂μ
· 使用定理 `MeasureTheory.integral_eq_zero_iff_of_nonneg_ae`：integral_eq_zero_iff_of
_nonneg_ae {f : α -> Real} (hf : 0 <=ᵐ[μ] f) (hfi : Integrable f μ) : ∫ x, f x ∂
μ = 0 ↔ f =ᵐ[μ] 0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem integral_eq_zero_iff_of_le_of_nonneg_ae (hab : a ≤ b) (hf : 0 ≤ᵐ[μ.restrict (Ioc a b)] f)
    (hfi : IntervalIntegrable f μ a b) :
    ∫ x in a..b, f x ∂μ = 0 ↔ f =ᵐ[μ.restrict (Ioc a b)] 0 := by
  rw [integral_of_le hab, integral_eq_zero_iff_of_nonneg_ae hf hfi.1]
/-
**intervalIntegral.integral_eq_zero_iff_of_nonneg_ae** 是 Mathlib 中的一个定理，位于命名空间 `
intervalIntegral`。
形式化陈述：integral_eq_zero_iff_of_nonneg_ae (hf : 0 <=ᵐ[μ.restrict (Ioc a b union Io
c b a)] f) (hfi : IntervalIntegrable f μ a b) : ∫ x in a..b, f x ∂μ = 0 ↔ f =ᵐ[μ
.restrict (Ioc a b union Ioc b a)] 0
参数：hf : 0 <=ᵐ[μ.restrict (Ioc a b union Ioc b a)] f；hfi : IntervalIntegrable f μ
 a b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.ae.congr_simp`：∀ {α : Type u_1} {F : Type u_3} [inst : Fun
Like F (Set α) ENNReal] [inst_1 : MeasureTheory.OuterMeasureClass F α]   (μ μ_1 
: F), μ = μ_1 → M…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.Ioc_eq_empty`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, ¬b < a
 → Set.Ioc b a = ∅
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `Set.union_empty`：union_empty (a : Set α) : a union ∅ = a
· 使用定理 `intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae`：integral_eq_ze
ro_iff_of_le_of_nonneg_ae (hab : a <= b) (hf : 0 <=ᵐ[μ.restrict (Ioc a b)] f) (h
fi : IntervalIntegrable f μ a b) : ∫ x in a..b…
· 使用定理 `Set.empty_union`：empty_union (a : Set α) : ∅ union a = a
· 使用定理 `intervalIntegral.integral_symm`：integral_symm (a b) : ∫ x in b..a, f x ∂
μ = -∫ x in a..b, f x ∂μ
· 使用定理 `neg_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a =
 0 ↔ a = 0
· 使用定理 `IntervalIntegrable.symm`：∀ {ε : Type u_3} [inst : TopologicalSpace ε] [i
nst_1 : ENormedAddMonoid ε] {f : ℝ → ε} {a b : ℝ}   {μ : MeasureTheory.Measure ℝ
}, IntervalIn…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem integral_eq_zero_iff_of_nonneg_ae (hf : 0 ≤ᵐ[μ.restrict (Ioc a b ∪ Ioc b a)] f)
    (hfi : IntervalIntegrable f μ a b) :
    ∫ x in a..b, f x ∂μ = 0 ↔ f =ᵐ[μ.restrict (Ioc a b ∪ Ioc b a)] 0 := by
  rcases le_total a b with hab | hab <;>
    simp only [Ioc_eq_empty hab.not_gt, empty_union, union_empty] at hf ⊢
  · exact integral_eq_zero_iff_of_le_of_nonneg_ae hab hf hfi
  · rw [integral_symm, neg_eq_zero, integral_eq_zero_iff_of_le_of_nonneg_ae hab hf hfi.symm]

/-- If `f` is nonnegative and integrable on the unordered interval `Set.uIoc a b`, then its
integral over `a..b` is positive if and only if `a < b` and the measure of
`Function.support f ∩ Set.Ioc a b` is positive. -/
/-
**intervalIntegral.integral_pos_iff_support_of_nonneg_ae'** 是 Mathlib 中的一个定理，位于命
名空间 `intervalIntegral`。
形式化陈述：integral_pos_iff_support_of_nonneg_ae' (hf : 0 <=ᵐ[μ.restrict (Ι a b)] f) 
(hfi : IntervalIntegrable f μ a b) : (0 < ∫ x in a..b, f x ∂μ) ↔ a < b ∧ 0 < μ (
support f inter Ioc a b)
参数：hf : 0 <=ᵐ[μ.restrict (Ι a b)] f；hfi : IntervalIntegrable f μ a b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intervalIntegral.integral_of_le`：integral_of_le (h : a <= b) : ∫ x in a.
.b, f x ∂μ = ∫ x in Ioc a b, f x ∂μ
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae`：setIntegral_pos_
iff_support_of_nonneg_ae {f : X -> Real} (hf : 0 <=ᵐ[μ.restrict s] f) (hfi : Int
egrableOn f s μ) : (0 < ∫ x in s, f x ∂μ) ↔ …
· 使用定理 `Set.uIoc_of_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b
 → Set.uIoc a b = Set.Ioc a b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `intervalIntegral.integral_of_ge`：integral_of_ge (h : b <= a) : ∫ x in a.
.b, f x ∂μ = -∫ x in Ioc b a, f x ∂μ
· 使用定理 `neg_nonpos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftM
ono α] {a : α}, -a ≤ 0 ↔ 0 ≤ a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `MeasureTheory.integral_nonneg_of_ae`：integral_nonneg_of_ae {f : α -> E} 
(hf : 0 <=ᵐ[μ] f) : 0 <= ∫ x, f x ∂μ
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用引理 `Set.uIoc_comm`：uIoc_comm (a b : α) : Ι a b = Ι b a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False

--- 原说明 ---
If `f` is nonnegative and integrable on the unordered interval `Set.uIoc a b`, t
hen its
integral over `a..b` is positive if and only if `a < b` and the measure of
`Function.support f ∩ Set.Ioc a b` is positive.
-/
theorem integral_pos_iff_support_of_nonneg_ae' (hf : 0 ≤ᵐ[μ.restrict (Ι a b)] f)
    (hfi : IntervalIntegrable f μ a b) :
    (0 < ∫ x in a..b, f x ∂μ) ↔ a < b ∧ 0 < μ (support f ∩ Ioc a b) := by
  rcases lt_or_ge a b with hab | hba
  · rw [uIoc_of_le hab.le] at hf
    simp only [hab, true_and, integral_of_le hab.le,
      setIntegral_pos_iff_support_of_nonneg_ae hf hfi.1]
  · suffices (∫ x in a..b, f x ∂μ) ≤ 0 by simp only [this.not_gt, hba.not_gt, false_and]
    rw [integral_of_ge hba, neg_nonpos]
    rw [uIoc_comm, uIoc_of_le hba] at hf
    exact integral_nonneg_of_ae hf

/-- If `f` is nonnegative a.e.-everywhere and it is integrable on the unordered interval
`Set.uIoc a b`, then its integral over `a..b` is positive if and only if `a < b` and the
measure of `Function.support f ∩ Set.Ioc a b` is positive. -/
/-
**intervalIntegral.integral_pos_iff_support_of_nonneg_ae** 是 Mathlib 中的一个定理，位于命名
空间 `intervalIntegral`。
形式化陈述：integral_pos_iff_support_of_nonneg_ae (hf : 0 <=ᵐ[μ] f) (hfi : IntervalInt
egrable f μ a b) : (0 < ∫ x in a..b, f x ∂μ) ↔ a < b ∧ 0 < μ (support f inter Io
c a b)
参数：hf : 0 <=ᵐ[μ] f；hfi : IntervalIntegrable f μ a b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `intervalIntegral.integral_pos_iff_support_of_nonneg_ae'`：integral_pos_if
f_support_of_nonneg_ae' (hf : 0 <=ᵐ[μ.restrict (Ι a b)] f) (hfi : IntervalIntegr
able f μ a b) : (0 < ∫ x in a..b, f x ∂μ) ↔ a…
· 使用定理 `MeasureTheory.ae_mono`：ae_mono (h : μ <= ν) : ae μ <= ae ν
· 使用定理 `MeasureTheory.Measure.restrict_le_self`：restrict_le_self : μ.restrict s 
<= μ

--- 原说明 ---
If `f` is nonnegative a.e.-everywhere and it is integrable on the unordered inte
rval
`Set.uIoc a b`, then its integral over `a..b` is positive if and only if `a < b`
 and the
measure of `Function.support f ∩ Set.Ioc a b` is positive.
-/
theorem integral_pos_iff_support_of_nonneg_ae (hf : 0 ≤ᵐ[μ] f) (hfi : IntervalIntegrable f μ a b) :
    (0 < ∫ x in a..b, f x ∂μ) ↔ a < b ∧ 0 < μ (support f ∩ Ioc a b) :=
  integral_pos_iff_support_of_nonneg_ae' (ae_mono Measure.restrict_le_self hf) hfi

/-- If `f : ℝ → ℝ` is integrable on `(a, b]` for real numbers `a < b`, and positive on the interior
of the interval, then its integral over `a..b` is strictly positive. -/
/-
**intervalIntegral.intervalIntegral_pos_of_pos_on** 是 Mathlib 中的一个定理，位于命名空间 `int
ervalIntegral`。
形式化陈述：intervalIntegral_pos_of_pos_on {f : Real -> Real} {a b : Real} (hfi : Inte
rvalIntegrable f volume a b) (hpos : forall x : Real, x in Ioo a b -> 0 < f x) (
hab : a < b) : 0 < ∫ x : Real in a..b, f x
参数：hfi : IntervalIntegrable f volume a b；hpos : forall x : Real, x in Ioo a b ->
 0 < f x；hab : a < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.mem_support`：∀ {ι : Type u_1} {M : Type u_3} [inst : Zero M] {f
 : ι → M} {x : ι}, x ∈ Function.support f ↔ f x ≠ 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Set.Ioo_subset_Ioc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo b a ⊆ Set.Ioc b a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.EventuallyLE.eq_1`：∀ {α : Type u_1} {β : Type u_2} [inst : LE β] 
(l : Filter α) (f g : α → β), (f ≤ᶠ[l] g) = ∀ᶠ (x : α) in l, f x ≤ g x
· 使用定理 `Set.uIoc_of_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b
 → Set.uIoc a b = Set.Ioc a b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `MeasureTheory.ae_restrict_of_ae_eq_of_ae_restrict`：ae_restrict_of_ae_eq_
of_ae_restrict {s t} (hst : s =ᵐ[μ] t) {p : α -> Prop} : (forallᵐ x ∂μ.restrict 
s, p x) -> forallᵐ x ∂μ.restrict t, p x
· 使用定理 `MeasureTheory.Ioo_ae_eq_Ioc`：Ioo_ae_eq_Ioc : Ioo a b =ᵐ[μ] Ioc a b
· 使用定理 `MeasureTheory.ae_restrict_iff'`：ae_restrict_iff'₀ {p : α -> Prop} (hs : 
NullMeasurableSet s μ) : (forallᵐ x ∂μ.restrict s, p x) ↔ forallᵐ x ∂μ, x in s -
> p x
· 使用定理 `measurableSet_Ioo`：measurableSet_Ioo [OrderClosedTopology α] : Measurabl
eSet (Ioo a b)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `intervalIntegral.integral_pos_iff_support_of_nonneg_ae'`：integral_pos_if
f_support_of_nonneg_ae' (hf : 0 <=ᵐ[μ.restrict (Ι a b)] f) (hfi : IntervalIntegr
able f μ a b) : (0 < ∫ x in a..b, f x ∂μ) ↔ a…
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `MeasureTheory.Measure.measure_Ioo_pos`：measure_Ioo_pos [DenselyOrdered X
] {a b : X} : 0 < μ (Ioo a b) ↔ a < b
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsOpenPosMeasure`：∀ {G : Type u
_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpace 
G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t

--- 原说明 ---
If `f : ℝ → ℝ` is integrable on `(a, b]` for real numbers `a < b`, and positive 
on the interior
of the interval, then its integral over `a..b` is strictly positive.
-/
theorem intervalIntegral_pos_of_pos_on {f : ℝ → ℝ} {a b : ℝ} (hfi : IntervalIntegrable f volume a b)
    (hpos : ∀ x : ℝ, x ∈ Ioo a b → 0 < f x) (hab : a < b) : 0 < ∫ x : ℝ in a..b, f x := by
  have hsupp : Ioo a b ⊆ support f ∩ Ioc a b := fun x hx =>
    ⟨mem_support.mpr (hpos x hx).ne', Ioo_subset_Ioc_self hx⟩
  have h₀ : 0 ≤ᵐ[volume.restrict (uIoc a b)] f := by
    rw [EventuallyLE, uIoc_of_le hab.le]
    refine ae_restrict_of_ae_eq_of_ae_restrict Ioo_ae_eq_Ioc ?_
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards with x hx using (hpos x hx).le
  rw [integral_pos_iff_support_of_nonneg_ae' h₀ hfi]
  exact ⟨hab, ((Measure.measure_Ioo_pos _).mpr hab).trans_le (measure_mono hsupp)⟩

/-- If `f : ℝ → ℝ` is strictly positive everywhere, and integrable on `(a, b]` for real numbers
`a < b`, then its integral over `a..b` is strictly positive. (See `intervalIntegral_pos_of_pos_on`
for a version only assuming positivity of `f` on `(a, b)` rather than everywhere.) -/
/-
**intervalIntegral.intervalIntegral_pos_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `interv
alIntegral`。
形式化陈述：intervalIntegral_pos_of_pos {f : Real -> Real} {a b : Real} (hfi : Interva
lIntegrable f MeasureSpace.volume a b) (hpos : forall x, 0 < f x) (hab : a < b) 
: 0 < ∫ x in a..b, f x
参数：hfi : IntervalIntegrable f MeasureSpace.volume a b；hpos : forall x, 0 < f x；h
ab : a < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `intervalIntegral.intervalIntegral_pos_of_pos_on`：intervalIntegral_pos_of
_pos_on {f : Real -> Real} {a b : Real} (hfi : IntervalIntegrable f volume a b) 
(hpos : forall x : Real, x in Ioo a b…

--- 原说明 ---
If `f : ℝ → ℝ` is strictly positive everywhere, and integrable on `(a, b]` for r
eal numbers
`a < b`, then its integral over `a..b` is strictly positive. (See `intervalInteg
ral_pos_of_pos_on`
for a version only assuming positivity of `f` on `(a, b)` rather than everywhere
.)
-/
theorem intervalIntegral_pos_of_pos {f : ℝ → ℝ} {a b : ℝ}
    (hfi : IntervalIntegrable f MeasureSpace.volume a b) (hpos : ∀ x, 0 < f x) (hab : a < b) :
    0 < ∫ x in a..b, f x :=
  intervalIntegral_pos_of_pos_on hfi (fun x _ => hpos x) hab

/-- If `f` and `g` are two functions that are interval integrable on `a..b`, `a ≤ b`,
`f x ≤ g x` for a.e. `x ∈ Set.Ioc a b`, and `f x < g x` on a subset of `Set.Ioc a b`
of nonzero measure, then `∫ x in a..b, f x ∂μ < ∫ x in a..b, g x ∂μ`. -/
/-
**intervalIntegral.integral_lt_integral_of_ae_le_of_measure_setOfPred_lt_ne_zero
** 是 Mathlib 中的一个定理，位于命名空间 `intervalIntegral`。
形式化陈述：integral_lt_integral_of_ae_le_of_measure_setOfPred_lt_ne_zero (hab : a <= 
b) (hfi : IntervalIntegrable f μ a b) (hgi : IntervalIntegrable g μ a b) (hle : 
f <=ᵐ[μ.restrict (Ioc a b)] g) (hlt : μ.restrict (Ioc a b) {x | f x < g x} != 0)
 : (∫ x in a..b, f x ∂μ) < ∫ x in a..b, g x ∂μ
参数：hab : a <= b；hfi : IntervalIntegrable f μ a b；hgi : IntervalIntegrable g μ a 
b；hle : f <=ᵐ[μ.restrict (Ioc a b)] g；hlt : μ.restrict (Ioc a b) {x | f x < g x}
 != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRightStr
ictMono α] {a b : α}, 0 < a - b ↔ b < a
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `intervalIntegral.integral_sub`：integral_sub (hf : IntervalIntegrable f μ
 a b) (hg : IntervalIntegrable g μ a b) : ∫ x in a..b, f x - g x ∂μ = (∫ x in a.
.b, f x ∂μ) - ∫ x i…
· 使用定理 `intervalIntegral.integral_of_le`：integral_of_le (h : a <= b) : ∫ x in a.
.b, f x ∂μ = ∫ x in Ioc a b, f x ∂μ
· 使用定理 `MeasureTheory.integral_pos_iff_support_of_nonneg_ae`：integral_pos_iff_su
pport_of_nonneg_ae {f : α -> Real} (hf : 0 <=ᵐ[μ] f) (hfi : Integrable f μ) : (0
 < ∫ x, f x ∂μ) ↔ 0 < μ (Function.support…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `MeasureTheory.IntegrableOn.sub`：∀ {α : Type u_1} {E : Type u_5} {mα : Me
asurableSpace α} [inst : NormedAddCommGroup E] {s : Set α}   {μ : MeasureTheory.
Measure α} {f g : α …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `MeasureTheory.measure_mono_null`：measure_mono_null (h : s subseteq t) (h
t : μ t = 0) : μ s = 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Membership.mem.out`：∀ {α : Type u} {a : α} {p : α → Prop}, a ∈ {x | p x}
 → p a

--- 原说明 ---
If `f` and `g` are two functions that are interval integrable on `a..b`, `a ≤ b`
,
`f x ≤ g x` for a.e. `x ∈ Set.Ioc a b`, and `f x < g x` on a subset of `Set.Ioc 
a b`
of nonzero measure, then `∫ x in a..b, f x ∂μ < ∫ x in a..b, g x ∂μ`.
-/
theorem integral_lt_integral_of_ae_le_of_measure_setOfPred_lt_ne_zero (hab : a ≤ b)
    (hfi : IntervalIntegrable f μ a b) (hgi : IntervalIntegrable g μ a b)
    (hle : f ≤ᵐ[μ.restrict (Ioc a b)] g) (hlt : μ.restrict (Ioc a b) {x | f x < g x} ≠ 0) :
    (∫ x in a..b, f x ∂μ) < ∫ x in a..b, g x ∂μ := by
  rw [← sub_pos, ← integral_sub hgi hfi, integral_of_le hab,
    MeasureTheory.integral_pos_iff_support_of_nonneg_ae]
  · refine pos_iff_ne_zero.2 (mt (measure_mono_null ?_) hlt)
    exact fun x hx => (sub_pos.2 hx.out).ne'
  exacts [hle.mono fun x => sub_nonneg.2, hgi.1.sub hfi.1]

@[deprecated (since := "2026-07-09")]
alias integral_lt_integral_of_ae_le_of_measure_setOf_lt_ne_zero :=
  integral_lt_integral_of_ae_le_of_measure_setOfPred_lt_ne_zero

/-- If `f` and `g` are continuous on `[a, b]`, `a < b`, `f x ≤ g x` on this interval, and
`f c < g c` at some point `c ∈ [a, b]`, then `∫ x in a..b, f x < ∫ x in a..b, g x`. -/
/-
**intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt** 是 M
athlib 中的一个定理，位于命名空间 `intervalIntegral`。
形式化陈述：integral_lt_integral_of_continuousOn_of_le_of_exists_lt {f g : Real -> Rea
l} {a b : Real} (hab : a < b) (hfc : ContinuousOn f (Icc a b)) (hgc : Continuous
On g (Icc a b)) (hle : forall x in Ioc a b, f x <= g x) (hlt : exists c in Icc a
 b, f c < g c) : (∫ x in a..b, f x) < ∫ x in a..b, g x
参数：hab : a < b；hfc : ContinuousOn f (Icc a b)；hgc : ContinuousOn g (Icc a b)；hle
 : forall x in Ioc a b, f x <= g x；hlt : exists c in Icc a b, f c < g c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `intervalIntegral.integral_lt_integral_of_ae_le_of_measure_setOfPred_lt_n
e_zero`：integral_lt_integral_of_ae_le_of_measure_setOfPred_lt_ne_zero (hab : a <
= b) (hfi : IntervalIntegrable f μ a b) (hgi : IntervalIntegrable g …
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `ContinuousOn.intervalIntegrable_of_Icc`：ContinuousOn.intervalIntegrable_
of_Icc {u : Real -> E} {a b : Real} (h : a <= b) (hu : ContinuousOn u (Icc a b))
 : IntervalIntegrable u μ a …
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ae_restrict_eq`：ae_restrict_eq (hs : MeasurableSet s) : ae
 (μ.restrict s) = ae μ ⊓ 𝓟 s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `MeasureTheory.ae_restrict_mem`：ae_restrict_mem (hs : MeasurableSet s) : 
forallᵐ x ∂μ.restrict s, x in s
· 使用定理 `measurableSet_Ioc`：measurableSet_Ioc [ClosedIicTopology α] : MeasurableS
et (Ioc a b)
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `Filter.EventuallyLE.antisymm`：∀ {α : Type u} {β : Type v} [inst : Partia
lOrder β] {l : Filter α} {f g : α → β}, f ≤ᶠ[l] g → g ≤ᶠ[l] f → f =ᶠ[l] g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.ae_restrict_iff'`：ae_restrict_iff'₀ {p : α -> Prop} (hs : 
NullMeasurableSet s μ) : (forallᵐ x ∂μ.restrict s, p x) ↔ forallᵐ x ∂μ, x in s -
> p x
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `MeasureTheory.Measure.eqOn_Icc_of_ae_eq`：eqOn_Icc_of_ae_eq [DenselyOrder
ed X] {a b : X} (hne : a != b) {f g : X -> Y} (hfg : f =ᵐ[μ.restrict (Icc a b)] 
g) (hf : ContinuousOn f (Icc …
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
（共 39 条，此处仅展示前 30 条）

--- 原说明 ---
If `f` and `g` are continuous on `[a, b]`, `a < b`, `f x ≤ g x` on this interval
, and
`f c < g c` at some point `c ∈ [a, b]`, then `∫ x in a..b, f x < ∫ x in a..b, g 
x`.
-/
theorem integral_lt_integral_of_continuousOn_of_le_of_exists_lt {f g : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hfc : ContinuousOn f (Icc a b)) (hgc : ContinuousOn g (Icc a b))
    (hle : ∀ x ∈ Ioc a b, f x ≤ g x) (hlt : ∃ c ∈ Icc a b, f c < g c) :
    (∫ x in a..b, f x) < ∫ x in a..b, g x := by
  apply integral_lt_integral_of_ae_le_of_measure_setOfPred_lt_ne_zero hab.le
    (hfc.intervalIntegrable_of_Icc hab.le) (hgc.intervalIntegrable_of_Icc hab.le)
  · simpa only [measurableSet_Ioc, ae_restrict_eq]
      using! (ae_restrict_mem measurableSet_Ioc).mono hle
  contrapose! hlt
  have h_eq : f =ᵐ[volume.restrict (Ioc a b)] g := by
    simp only [← not_le, ← ae_iff] at hlt
    exact EventuallyLE.antisymm ((ae_restrict_iff' measurableSet_Ioc).2 <|
      Eventually.of_forall hle) hlt
  rw [Measure.restrict_congr_set Ioc_ae_eq_Icc] at h_eq
  exact fun c hc ↦ (Measure.eqOn_Icc_of_ae_eq volume hab.ne h_eq hfc hgc hc).ge
/-
**intervalIntegral.integral_nonneg_of_ae_restrict** 是 Mathlib 中的一个定理，位于命名空间 `int
ervalIntegral`。
形式化陈述：integral_nonneg_of_ae_restrict (hab : a <= b) (hf : 0 <=ᵐ[μ.restrict (Icc 
a b)] f) : 0 <= ∫ u in a..b, f u ∂μ
参数：hab : a <= b；hf : 0 <=ᵐ[μ.restrict (Icc a b)] f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_restrict_of_ae_restrict_of_subset`：ae_restrict_of_ae_re
strict_of_subset {s t : Set α} {p : α -> Prop} (hst : s subseteq t) (h : forallᵐ
 x ∂μ.restrict t, p x) : forallᵐ x ∂μ.re…
· 使用定理 `Set.Ioc_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc a b ⊆ Set.Icc a b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intervalIntegral.integral_of_le`：integral_of_le (h : a <= b) : ∫ x in a.
.b, f x ∂μ = ∫ x in Ioc a b, f x ∂μ
· 使用定理 `MeasureTheory.setIntegral_nonneg_of_ae_restrict`：setIntegral_nonneg_of_a
e_restrict (hf : 0 <=ᵐ[μ.restrict s] f) : 0 <= ∫ x in s, f x ∂μ
-/
theorem integral_nonneg_of_ae_restrict (hab : a ≤ b) (hf : 0 ≤ᵐ[μ.restrict (Icc a b)] f) :
    0 ≤ ∫ u in a..b, f u ∂μ := by
  let H := ae_restrict_of_ae_restrict_of_subset Ioc_subset_Icc_self hf
  simpa only [integral_of_le hab] using setIntegral_nonneg_of_ae_restrict H
/-
**intervalIntegral.integral_nonneg_of_ae** 是 Mathlib 中的一个定理，位于命名空间 `intervalInte
gral`。
形式化陈述：integral_nonneg_of_ae (hab : a <= b) (hf : 0 <=ᵐ[μ] f) : 0 <= ∫ u in a..b,
 f u ∂μ
参数：hab : a <= b；hf : 0 <=ᵐ[μ] f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `intervalIntegral.integral_nonneg_of_ae_restrict`：integral_nonneg_of_ae_r
estrict (hab : a <= b) (hf : 0 <=ᵐ[μ.restrict (Icc a b)] f) : 0 <= ∫ u in a..b, 
f u ∂μ
· 使用定理 `MeasureTheory.ae_restrict_of_ae`：ae_restrict_of_ae {s : Set α} {p : α ->
 Prop} (h : forallᵐ x ∂μ, p x) : forallᵐ x ∂μ.restrict s, p x
-/
theorem integral_nonneg_of_ae (hab : a ≤ b) (hf : 0 ≤ᵐ[μ] f) : 0 ≤ ∫ u in a..b, f u ∂μ :=
  integral_nonneg_of_ae_restrict hab <| ae_restrict_of_ae hf
/-
**intervalIntegral.integral_nonneg_of_forall** 是 Mathlib 中的一个定理，位于命名空间 `interval
Integral`。
形式化陈述：integral_nonneg_of_forall (hab : a <= b) (hf : forall u, 0 <= f u) : 0 <= 
∫ u in a..b, f u ∂μ
参数：hab : a <= b；hf : forall u, 0 <= f u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `intervalIntegral.integral_nonneg_of_ae`：integral_nonneg_of_ae (hab : a <
= b) (hf : 0 <=ᵐ[μ] f) : 0 <= ∫ u in a..b, f u ∂μ
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
theorem integral_nonneg_of_forall (hab : a ≤ b) (hf : ∀ u, 0 ≤ f u) : 0 ≤ ∫ u in a..b, f u ∂μ :=
  integral_nonneg_of_ae hab <| Eventually.of_forall hf
/-
**intervalIntegral.integral_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `intervalIntegral`。
形式化陈述：integral_nonneg (hab : a <= b) (hf : forall u, u in Icc a b -> 0 <= f u) :
 0 <= ∫ u in a..b, f u ∂μ
参数：hab : a <= b；hf : forall u, u in Icc a b -> 0 <= f u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `intervalIntegral.integral_nonneg_of_ae_restrict`：integral_nonneg_of_ae_r
estrict (hab : a <= b) (hf : 0 <=ᵐ[μ.restrict (Icc a b)] f) : 0 <= ∫ u in a..b, 
f u ∂μ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_restrict_iff'`：ae_restrict_iff'₀ {p : α -> Prop} (hs : 
NullMeasurableSet s μ) : (forallᵐ x ∂μ.restrict s, p x) ↔ forallᵐ x ∂μ, x in s -
> p x
· 使用定理 `measurableSet_Icc`：measurableSet_Icc [OrderClosedTopology α] : Measurabl
eSet (Icc a b)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
-/
theorem integral_nonneg (hab : a ≤ b) (hf : ∀ u, u ∈ Icc a b → 0 ≤ f u) : 0 ≤ ∫ u in a..b, f u ∂μ :=
  integral_nonneg_of_ae_restrict hab <| (ae_restrict_iff' measurableSet_Icc).mpr <| ae_of_all μ hf
/-
**intervalIntegral.abs_integral_le_integral_abs** 是 Mathlib 中的一个定理，位于命名空间 `inter
valIntegral`。
形式化陈述：abs_integral_le_integral_abs (hab : a <= b) : |∫ x in a..b, f x ∂μ| <= ∫ x
 in a..b, |f x| ∂μ
参数：hab : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `intervalIntegral.norm_integral_le_integral_norm`：norm_integral_le_integr
al_norm (h : a <= b) : ‖∫ x in a..b, f x ∂μ‖ <= ∫ x in a..b, ‖f x‖ ∂μ
-/
theorem abs_integral_le_integral_abs (hab : a ≤ b) :
    |∫ x in a..b, f x ∂μ| ≤ ∫ x in a..b, |f x| ∂μ := by
  simpa only [← Real.norm_eq_abs] using norm_integral_le_integral_norm hab
/-
**intervalIntegral.integral_pos** 是 Mathlib 中的一个引理，位于命名空间 `intervalIntegral`。
形式化陈述：integral_pos (hab : a < b) (hfc : ContinuousOn f (Icc a b)) (hle : forall 
x in Ioc a b, 0 <= f x) (hlt : exists c in Icc a b, 0 < f c) : 0 < ∫ x in a..b, 
f x
参数：hab : a < b；hfc : ContinuousOn f (Icc a b)；hle : forall x in Ioc a b, 0 <= f 
x；hlt : exists c in Icc a b, 0 < f c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_eq'`：∀ {α : Type u_1} {a b c : α} [inst : LT α], b < a → b =
 c → c < a
· 使用定理 `intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
`：integral_lt_integral_of_continuousOn_of_le_of_exists_lt {f g : Real -> Real} {
a b : Real} (hab : a < b) (hfc : ContinuousOn f (Icc a b)) (hg…
· 使用定理 `continuousOn_const`：continuousOn_const {s : Set α} {c : β} : ContinuousO
n (fun _ => c) s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intervalIntegral.integral_zero`：integral_zero : (∫ _ in a..b, (0 : E) ∂μ
) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma integral_pos (hab : a < b)
    (hfc : ContinuousOn f (Icc a b)) (hle : ∀ x ∈ Ioc a b, 0 ≤ f x) (hlt : ∃ c ∈ Icc a b, 0 < f c) :
    0 < ∫ x in a..b, f x :=
  (integral_lt_integral_of_continuousOn_of_le_of_exists_lt hab
    continuousOn_const hfc hle hlt).trans_eq' (by simp)

section Mono

/-
**intervalIntegral.integral_mono_interval** 是 Mathlib 中的一个定理，位于命名空间 `intervalInt
egral`。
形式化陈述：integral_mono_interval {c d} (hca : c <= a) (hab : a <= b) (hbd : b <= d) 
(hf : 0 <=ᵐ[μ.restrict (Ioc c d)] f) (hfi : IntervalIntegrable f μ c d) : (∫ x i
n a..b, f x ∂μ) <= ∫ x in c..d, f x ∂μ
参数：hca : c <= a；hab : a <= b；hbd : b <= d；hf : 0 <=ᵐ[μ.restrict (Ioc c d)] f；hfi
 : IntervalIntegrable f μ c d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intervalIntegral.integral_of_le`：integral_of_le (h : a <= b) : ∫ x in a.
.b, f x ∂μ = ∫ x in Ioc a b, f x ∂μ
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.setIntegral_mono_set`：setIntegral_mono_set [OrderClosedTop
ology E] (hfi : IntegrableOn f t μ) (hf : 0 <=ᵐ[μ.restrict t] f) (hst : s <=ᵐ[μ]
 t) : ∫ x in s, f x ∂μ <…
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.eventuallyLE`：LE.le.eventuallyLE {α} {l : Filter α} {s t : Set α} 
(h : s subseteq t) : s <=ᶠ[l] t
· 使用定理 `Set.Ioc_subset_Ioc`：∀ {α : Type u_1} [inst : Preorder α] {a₁ a₂ b₁ b₂ : 
α}, b₂ ≤ b₁ → a₁ ≤ a₂ → Set.Ioc b₁ a₁ ⊆ Set.Ioc b₂ a₂
-/
theorem integral_mono_interval {c d} (hca : c ≤ a) (hab : a ≤ b) (hbd : b ≤ d)
    (hf : 0 ≤ᵐ[μ.restrict (Ioc c d)] f) (hfi : IntervalIntegrable f μ c d) :
    (∫ x in a..b, f x ∂μ) ≤ ∫ x in c..d, f x ∂μ := by
  rw [integral_of_le hab, integral_of_le (hca.trans (hab.trans hbd))]
  exact setIntegral_mono_set hfi.1 hf (Ioc_subset_Ioc hca hbd).eventuallyLE
/-
**intervalIntegral.abs_integral_mono_interval** 是 Mathlib 中的一个定理，位于命名空间 `interva
lIntegral`。
形式化陈述：abs_integral_mono_interval {c d} (h : Ι a b subseteq Ι c d) (hf : 0 <=ᵐ[μ.
restrict (Ι c d)] f) (hfi : IntervalIntegrable f μ c d) : |∫ x in a..b, f x ∂μ| 
<= |∫ x in c..d, f x ∂μ|
参数：h : Ι a b subseteq Ι c d；hf : 0 <=ᵐ[μ.restrict (Ι c d)] f；hfi : IntervalInteg
rable f μ c d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_mono`：ae_mono (h : μ <= ν) : ae μ <= ae ν
· 使用定理 `MeasureTheory.Measure.restrict_mono`：restrict_mono {_m0 : MeasurableSpac
e α} ⦃s s' : Set α⦄ (hs : s subseteq s') ⦃μ ν : Measure α⦄ (hμν : μ <= ν) : μ.re
strict s <= ν.restrict s'
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `intervalIntegral.abs_integral_eq_abs_integral_uIoc`：abs_integral_eq_abs_
integral_uIoc (f : Real -> Real) : |∫ x in a..b, f x ∂μ| = |∫ x in Ι a b, f x ∂μ
|
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `MeasureTheory.integral_nonneg_of_ae`：integral_nonneg_of_ae {f : α -> E} 
(hf : 0 <=ᵐ[μ] f) : 0 <= ∫ x, f x ∂μ
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `MeasureTheory.setIntegral_mono_set`：setIntegral_mono_set [OrderClosedTop
ology E] (hfi : IntegrableOn f t μ) (hf : 0 <=ᵐ[μ.restrict t] f) (hst : s <=ᵐ[μ]
 t) : ∫ x in s, f x ∂μ <…
· 使用定理 `IntervalIntegrable.def'`：IntervalIntegrable.def' (h : IntervalIntegrable
 f μ a b) : IntegrableOn f (Ι a b) μ
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `LE.le.eventuallyLE`：LE.le.eventuallyLE {α} {l : Filter α} {s t : Set α} 
(h : s subseteq t) : s <=ᶠ[l] t
· 使用定理 `le_abs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (
a : α), a ≤ |a|
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem abs_integral_mono_interval {c d} (h : Ι a b ⊆ Ι c d) (hf : 0 ≤ᵐ[μ.restrict (Ι c d)] f)
    (hfi : IntervalIntegrable f μ c d) : |∫ x in a..b, f x ∂μ| ≤ |∫ x in c..d, f x ∂μ| :=
  have hf' : 0 ≤ᵐ[μ.restrict (Ι a b)] f := ae_mono (Measure.restrict_mono h le_rfl) hf
  calc
    |∫ x in a..b, f x ∂μ| = |∫ x in Ι a b, f x ∂μ| := abs_integral_eq_abs_integral_uIoc f
    _ = ∫ x in Ι a b, f x ∂μ := abs_of_nonneg (MeasureTheory.integral_nonneg_of_ae hf')
    _ ≤ ∫ x in Ι c d, f x ∂μ := setIntegral_mono_set hfi.def' hf h.eventuallyLE
    _ ≤ |∫ x in Ι c d, f x ∂μ| := le_abs_self _
    _ = |∫ x in c..d, f x ∂μ| := (abs_integral_eq_abs_integral_uIoc f).symm

variable (hab : a ≤ b) (hf : IntervalIntegrable f μ a b) (hg : IntervalIntegrable g μ a b)
include hab hf hg
/-
**intervalIntegral.integral_mono_ae_restrict** 是 Mathlib 中的一个定理，位于命名空间 `interval
Integral`。
形式化陈述：integral_mono_ae_restrict (h : f <=ᵐ[μ.restrict (Icc a b)] g) : (∫ u in a.
.b, f u ∂μ) <= ∫ u in a..b, g u ∂μ
参数：h : f <=ᵐ[μ.restrict (Icc a b)] g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.Eventually.filter_mono`：∀ {α : Type u} {f₁ f₂ : Filter α}, f₁ ≤ f
₂ → ∀ {p : α → Prop}, (∀ᶠ (x : α) in f₂, p x) → ∀ᶠ (x : α) in f₁, p x
· 使用定理 `MeasureTheory.ae_mono`：ae_mono (h : μ <= ν) : ae μ <= ae ν
· 使用定理 `MeasureTheory.Measure.restrict_mono`：restrict_mono {_m0 : MeasurableSpac
e α} ⦃s s' : Set α⦄ (hs : s subseteq s') ⦃μ ν : Measure α⦄ (hμν : μ <= ν) : μ.re
strict s <= ν.restrict s'
· 使用定理 `Set.Ioc_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc a b ⊆ Set.Icc a b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intervalIntegral.integral_of_le`：integral_of_le (h : a <= b) : ∫ x in a.
.b, f x ∂μ = ∫ x in Ioc a b, f x ∂μ
· 使用定理 `MeasureTheory.setIntegral_mono_ae_restrict`：setIntegral_mono_ae_restrict
 (h : f <=ᵐ[μ.restrict s] g) : ∫ x in s, f x ∂μ <= ∫ x in s, g x ∂μ
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem integral_mono_ae_restrict (h : f ≤ᵐ[μ.restrict (Icc a b)] g) :
    (∫ u in a..b, f u ∂μ) ≤ ∫ u in a..b, g u ∂μ := by
  let H := h.filter_mono <| ae_mono <| Measure.restrict_mono Ioc_subset_Icc_self <| le_refl μ
  simpa only [integral_of_le hab] using setIntegral_mono_ae_restrict hf.1 hg.1 H
/-
**intervalIntegral.integral_mono_ae** 是 Mathlib 中的一个定理，位于命名空间 `intervalIntegral`
。
形式化陈述：integral_mono_ae (h : f <=ᵐ[μ] g) : (∫ u in a..b, f u ∂μ) <= ∫ u in a..b, 
g u ∂μ
参数：h : f <=ᵐ[μ] g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intervalIntegral.integral_of_le`：integral_of_le (h : a <= b) : ∫ x in a.
.b, f x ∂μ = ∫ x in Ioc a b, f x ∂μ
· 使用定理 `MeasureTheory.setIntegral_mono_ae`：setIntegral_mono_ae (h : f <=ᵐ[μ] g) 
: ∫ x in s, f x ∂μ <= ∫ x in s, g x ∂μ
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem integral_mono_ae (h : f ≤ᵐ[μ] g) : (∫ u in a..b, f u ∂μ) ≤ ∫ u in a..b, g u ∂μ := by
  simpa only [integral_of_le hab] using setIntegral_mono_ae hf.1 hg.1 h
/-
**intervalIntegral.integral_mono_on** 是 Mathlib 中的一个定理，位于命名空间 `intervalIntegral`
。
形式化陈述：integral_mono_on (h : forall x in Icc a b, f x <= g x) : (∫ u in a..b, f u
 ∂μ) <= ∫ u in a..b, g u ∂μ
参数：h : forall x in Icc a b, f x <= g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Ioc_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc a b ⊆ Set.Icc a b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intervalIntegral.integral_of_le`：integral_of_le (h : a <= b) : ∫ x in a.
.b, f x ∂μ = ∫ x in Ioc a b, f x ∂μ
· 使用定理 `MeasureTheory.setIntegral_mono_on`：setIntegral_mono_on (hs : MeasurableS
et s) (h : forall x in s, f x <= g x) : ∫ x in s, f x ∂μ <= ∫ x in s, g x ∂μ
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `measurableSet_Ioc`：measurableSet_Ioc [ClosedIicTopology α] : MeasurableS
et (Ioc a b)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
-/
theorem integral_mono_on (h : ∀ x ∈ Icc a b, f x ≤ g x) :
    (∫ u in a..b, f u ∂μ) ≤ ∫ u in a..b, g u ∂μ := by
  let H x hx := h x <| Ioc_subset_Icc_self hx
  simpa only [integral_of_le hab] using setIntegral_mono_on hf.1 hg.1 measurableSet_Ioc H
/-
**intervalIntegral.integral_mono_on_of_le_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `interva
lIntegral`。
形式化陈述：integral_mono_on_of_le_Ioo [NullSingletonClass μ] (h : forall x in Ioo a b
, f x <= g x) : (∫ u in a..b, f u ∂μ) <= ∫ u in a..b, g u ∂μ
参数：h : forall x in Ioo a b, f x <= g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `intervalIntegral.integral_of_le`：integral_of_le (h : a <= b) : ∫ x in a.
.b, f x ∂μ = ∫ x in Ioc a b, f x ∂μ
· 使用定理 `MeasureTheory.integral_Ioc_eq_integral_Ioo`：integral_Ioc_eq_integral_Ioo
 : ∫ t in Ioc x y, f t ∂μ = ∫ t in Ioo x y, f t ∂μ
· 使用定理 `MeasureTheory.setIntegral_mono_on`：setIntegral_mono_on (hs : MeasurableS
et s) (h : forall x in s, f x <= g x) : ∫ x in s, f x ∂μ <= ∫ x in s, g x ∂μ
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `MeasureTheory.IntegrableOn.mono`：∀ {α : Type u_1} {ε : Type u_3} {mα : M
easurableSpace α} {f : α → ε} {s t : Set α} {μ ν : MeasureTheory.Measure α}   [i
nst : TopologicalSpac…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.Ioo_subset_Ioc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo b a ⊆ Set.Ioc b a
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `measurableSet_Ioo`：measurableSet_Ioo [OrderClosedTopology α] : Measurabl
eSet (Ioo a b)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
-/
theorem integral_mono_on_of_le_Ioo [NullSingletonClass μ] (h : ∀ x ∈ Ioo a b, f x ≤ g x) :
    (∫ u in a..b, f u ∂μ) ≤ ∫ u in a..b, g u ∂μ := by
  simp only [integral_of_le hab, integral_Ioc_eq_integral_Ioo]
  apply setIntegral_mono_on
  · apply hf.1.mono Ioo_subset_Ioc_self le_rfl
  · apply hg.1.mono Ioo_subset_Ioc_self le_rfl
  · exact measurableSet_Ioo
  · exact h
/-
**intervalIntegral.integral_mono** 是 Mathlib 中的一个定理，位于命名空间 `intervalIntegral`。
形式化陈述：integral_mono (h : f <= g) : (∫ u in a..b, f u ∂μ) <= ∫ u in a..b, g u ∂μ
参数：h : f <= g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `intervalIntegral.integral_mono_ae`：integral_mono_ae (h : f <=ᵐ[μ] g) : (
∫ u in a..b, f u ∂μ) <= ∫ u in a..b, g u ∂μ
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
theorem integral_mono (h : f ≤ g) : (∫ u in a..b, f u ∂μ) ≤ ∫ u in a..b, g u ∂μ :=
  integral_mono_ae hab hf hg <| ae_of_all _ h

end Mono

end

section HasSum

variable {μ : Measure ℝ} {f : ℝ → E}

/-
**intervalIntegral._root_.MeasureTheory.Integrable.hasSum_intervalIntegral** 是 M
athlib 中的一个定理，位于命名空间 `intervalIntegral`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasureTheory.Integrable.hasSum_intervalIntegral (hfi : Integrable f μ) (y : ℝ) :
    HasSum (fun n : ℤ => ∫ x in y + n..y + n + 1, f x ∂μ) (∫ x, f x ∂μ) := by
  simp_rw [integral_of_le (le_add_of_nonneg_right zero_le_one)]
  rw [← setIntegral_univ, ← iUnion_Ioc_add_intCast y]
  exact
    hasSum_integral_iUnion (fun i => measurableSet_Ioc) (pairwise_disjoint_Ioc_add_intCast y)
      hfi.integrableOn
/-
**intervalIntegral._root_.MeasureTheory.Integrable.hasSum_intervalIntegral_comp_
add_int** 是 Mathlib 中的一个定理，位于命名空间 `intervalIntegral`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasureTheory.Integrable.hasSum_intervalIntegral_comp_add_int (hfi : Integrable f) :
    HasSum (fun n : ℤ => ∫ x in (0 : ℝ)..(1 : ℝ), f (x + n)) (∫ x, f x) := by
  simpa only [integral_comp_add_right, zero_add, add_comm (1 : ℝ)] using
    hfi.hasSum_intervalIntegral 0

end HasSum

end intervalIntegral

