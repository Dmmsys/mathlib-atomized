/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov, Sébastien Gouëzel, Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

/-!
# Additivity on measurable sets with finite measure

Let `T : Set α → E →L[ℝ] F` be additive for measurable sets with finite measure, in the sense that
for `s, t` two such sets, `Disjoint s t → T (s ∪ t) = T s + T t`. `T` is akin to a bilinear map on
`Set α × E`, or a linear map on indicator functions.

This property is named `FinMeasAdditive` in this file. We also define `DominatedFinMeasAdditive`,
which requires in addition that the norm on every set is less than the measure of the set
(up to a multiplicative constant); in `Mathlib/MeasureTheory/Integral/SetToL1.lean` we extend
set functions with this stronger property to integrable (L1) functions.

## Main definitions

- `FinMeasAdditive μ T`: the property that `T` is additive on measurable sets with finite measure.
  For two such sets, `Disjoint s t → T (s ∪ t) = T s + T t`.
- `DominatedFinMeasAdditive μ T C`: `FinMeasAdditive μ T ∧ ∀ s, ‖T s‖ ≤ C * μ.real s`.
  This is the property needed to perform the extension from indicators to L1.

## Implementation notes

The starting object `T : Set α → E →L[ℝ] F` matters only through its restriction on measurable sets
with finite measure. Its value on other sets is ignored.
-/

@[expose] public section


noncomputable section

open Set Filter ENNReal Finset

namespace MeasureTheory

variable {α E F F' G 𝕜 : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup F'] [NormedSpace ℝ F']
  [NormedAddCommGroup G] {m : MeasurableSpace α} {μ : Measure α}

local infixr:25 " →ₛ " => SimpleFunc

section FinMeasAdditive

/-- A set function is `FinMeasAdditive` if its value on the union of two disjoint measurable
sets with finite measure is the sum of its values on each set. -/
/-
**MeasureTheory.FinMeasAdditive** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：FinMeasAdditive {β} [AddMonoid β] {_ : MeasurableSpace α} (μ : Measure α) 
(T : Set α -> β) : Prop
参数：μ : Measure α；T : Set α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set function is `FinMeasAdditive` if its value on the union of two disjoint me
asurable
sets with finite measure is the sum of its values on each set.
-/
def FinMeasAdditive {β} [AddMonoid β] {_ : MeasurableSpace α} (μ : Measure α) (T : Set α → β) :
    Prop :=
  ∀ s t, MeasurableSet s → MeasurableSet t → μ s ≠ ∞ → μ t ≠ ∞ → Disjoint s t →
    T (s ∪ t) = T s + T t

namespace FinMeasAdditive

variable {β : Type*} {T T' : Set α → β}

section AddMonoid

variable [AddMonoid β]

/-
**MeasureTheory.FinMeasAdditive.zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Fi
nMeasAdditive`。
形式化陈述：zero : FinMeasAdditive μ (0 : Set α -> β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem zero : FinMeasAdditive μ (0 : Set α → β) := fun _ _ _ _ _ _ _ => by simp
/-
**MeasureTheory.FinMeasAdditive.smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Fi
nMeasAdditive`。
形式化陈述：smul [DistribSMul 𝕜 β] (hT : FinMeasAdditive μ T) (c : 𝕜) : FinMeasAdditiv
e μ fun s => c • T s
参数：hT : FinMeasAdditive μ T；c : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smul [DistribSMul 𝕜 β] (hT : FinMeasAdditive μ T) (c : 𝕜) :
    FinMeasAdditive μ fun s => c • T s := fun s t hs ht hμs hμt hst => by
  simp [hT s t hs ht hμs hμt hst]
/-
**MeasureTheory.FinMeasAdditive.of_eq_top_imp_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.FinMeasAdditive`。
形式化陈述：of_eq_top_imp_eq_top {μ' : Measure α} (h : forall s, MeasurableSet s -> μ 
s = ∞ -> μ' s = ∞) (hT : FinMeasAdditive μ T) : FinMeasAdditive μ' T
参数：h : forall s, MeasurableSet s -> μ s = ∞ -> μ' s = ∞；hT : FinMeasAdditive μ T
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
-/
theorem of_eq_top_imp_eq_top {μ' : Measure α} (h : ∀ s, MeasurableSet s → μ s = ∞ → μ' s = ∞)
    (hT : FinMeasAdditive μ T) : FinMeasAdditive μ' T := fun s t hs ht hμ's hμ't hst =>
  hT s t hs ht (mt (h s hs) hμ's) (mt (h t ht) hμ't) hst
/-
**MeasureTheory.FinMeasAdditive.add_right_measure** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.FinMeasAdditive`。
形式化陈述：add_right_measure {ν : Measure α} (hT : FinMeasAdditive μ T) : FinMeasAddi
tive (μ + ν) T
参数：hT : FinMeasAdditive μ T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.FinMeasAdditive.of_eq_top_imp_eq_top`：of_eq_top_imp_eq_top
 {μ' : Measure α} (h : forall s, MeasurableSet s -> μ s = ∞ -> μ' s = ∞) (hT : F
inMeasAdditive μ T) : FinMeasAdditive μ'…
· 使用定理 `top_unique`：top_unique (h : ⊤ <= a) : a = ⊤
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.le_add_right`：∀ {α : Type u_1} {m0 : MeasurableSpa
ce α} {μ ν ν' : MeasureTheory.Measure α}, μ ≤ ν → μ ≤ ν + ν'
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem add_right_measure {ν : Measure α} (hT : FinMeasAdditive μ T) :
    FinMeasAdditive (μ + ν) T :=
  hT.of_eq_top_imp_eq_top fun s _ hμs =>
    top_unique <| hμs.symm.trans_le (Measure.le_add_right le_rfl s)
/-
**MeasureTheory.FinMeasAdditive.add_left_measure** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.FinMeasAdditive`。
形式化陈述：add_left_measure {ν : Measure α} (hT : FinMeasAdditive μ T) : FinMeasAddit
ive (ν + μ) T
参数：hT : FinMeasAdditive μ T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.FinMeasAdditive.of_eq_top_imp_eq_top`：of_eq_top_imp_eq_top
 {μ' : Measure α} (h : forall s, MeasurableSet s -> μ s = ∞ -> μ' s = ∞) (hT : F
inMeasAdditive μ T) : FinMeasAdditive μ'…
· 使用定理 `top_unique`：top_unique (h : ⊤ <= a) : a = ⊤
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.le_add_left`：∀ {α : Type u_1} {m0 : MeasurableSpac
e α} {μ ν ν' : MeasureTheory.Measure α}, μ ≤ ν → μ ≤ ν' + ν
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem add_left_measure {ν : Measure α} (hT : FinMeasAdditive μ T) :
    FinMeasAdditive (ν + μ) T :=
  hT.of_eq_top_imp_eq_top fun s _ hμs =>
    top_unique <| hμs.symm.trans_le (Measure.le_add_left le_rfl s)
/-
**MeasureTheory.FinMeasAdditive.of_smul_measure** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.FinMeasAdditive`。
形式化陈述：of_smul_measure {c : Real>=0∞} (hc_ne_top : c != ∞) (hT : FinMeasAdditive 
(c • μ) T) : FinMeasAdditive μ T
参数：hc_ne_top : c != ∞；hT : FinMeasAdditive (c • μ) T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.FinMeasAdditive.of_eq_top_imp_eq_top`：of_eq_top_imp_eq_top
 {μ' : Measure α} (h : forall s, MeasurableSet s -> μ s = ∞ -> μ' s = ∞) (hT : F
inMeasAdditive μ T) : FinMeasAdditive μ'…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `ENNReal.mul_eq_top`：mul_eq_top : a * b = ∞ ↔ a != 0 ∧ b = ∞ ∨ a = ∞ ∧ b 
!= 0
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `MeasureTheory.Measure.smul_apply`：smul_apply {_m : MeasurableSpace α} (c
 : R) (μ : Measure α) (s : Set α) : (c • μ) s = c • μ s
-/
theorem of_smul_measure {c : ℝ≥0∞} (hc_ne_top : c ≠ ∞) (hT : FinMeasAdditive (c • μ) T) :
    FinMeasAdditive μ T := by
  refine of_eq_top_imp_eq_top (fun s _ hμs => ?_) hT
  rw [Measure.smul_apply, smul_eq_mul, ENNReal.mul_eq_top] at hμs
  simp only [hc_ne_top, or_false, Ne, false_and] at hμs
  exact hμs.2
/-
**MeasureTheory.FinMeasAdditive.smul_measure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.FinMeasAdditive`。
形式化陈述：smul_measure (c : Real>=0∞) (hc_ne_zero : c != 0) (hT : FinMeasAdditive μ 
T) : FinMeasAdditive (c • μ) T
参数：c : Real>=0∞；hc_ne_zero : c != 0；hT : FinMeasAdditive μ T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.FinMeasAdditive.of_eq_top_imp_eq_top`：of_eq_top_imp_eq_top
 {μ' : Measure α} (h : forall s, MeasurableSet s -> μ s = ∞ -> μ' s = ∞) (hT : F
inMeasAdditive μ T) : FinMeasAdditive μ'…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.smul_apply`：smul_apply {_m : MeasurableSpace α} (c
 : R) (μ : Measure α) (s : Set α) : (c • μ) s = c • μ s
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `ENNReal.mul_eq_top`：mul_eq_top : a * b = ∞ ↔ a != 0 ∧ b = ∞ ∨ a = ∞ ∧ b 
!= 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
theorem smul_measure (c : ℝ≥0∞) (hc_ne_zero : c ≠ 0) (hT : FinMeasAdditive μ T) :
    FinMeasAdditive (c • μ) T := by
  refine of_eq_top_imp_eq_top (fun s _ hμs => ?_) hT
  rw [Measure.smul_apply, smul_eq_mul, ENNReal.mul_eq_top]
  simp only [hc_ne_zero, true_and, Ne, not_false_iff]
  exact Or.inl hμs
/-
**MeasureTheory.FinMeasAdditive.smul_measure_iff** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.FinMeasAdditive`。
形式化陈述：smul_measure_iff (c : Real>=0∞) (hc_ne_zero : c != 0) (hc_ne_top : c != ∞)
 : FinMeasAdditive (c • μ) T ↔ FinMeasAdditive μ T
参数：c : Real>=0∞；hc_ne_zero : c != 0；hc_ne_top : c != ∞。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.FinMeasAdditive.of_smul_measure`：of_smul_measure {c : Real
>=0∞} (hc_ne_top : c != ∞) (hT : FinMeasAdditive (c • μ) T) : FinMeasAdditive μ 
T
· 使用定理 `MeasureTheory.FinMeasAdditive.smul_measure`：smul_measure (c : Real>=0∞) 
(hc_ne_zero : c != 0) (hT : FinMeasAdditive μ T) : FinMeasAdditive (c • μ) T
-/
theorem smul_measure_iff (c : ℝ≥0∞) (hc_ne_zero : c ≠ 0) (hc_ne_top : c ≠ ∞) :
    FinMeasAdditive (c • μ) T ↔ FinMeasAdditive μ T :=
  ⟨fun hT => of_smul_measure hc_ne_top hT, fun hT => smul_measure c hc_ne_zero hT⟩
/-
**MeasureTheory.FinMeasAdditive.map_empty_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.FinMeasAdditive`。
形式化陈述：map_empty_eq_zero {β} [AddCancelMonoid β] {T : Set α -> β} (hT : FinMeasAd
ditive μ T) : T ∅ = 0
参数：hT : FinMeasAdditive μ T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ENNReal.coe_lt_top`：∀ {r : NNReal}, ↑r < ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_left_cancel`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G] {a 
b c : G}, a + b = a + c → b = c
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Set.union_empty`：union_empty (a : Set α) : a union ∅ = a
· 使用定理 `MeasurableSet.empty`：MeasurableSet.empty [MeasurableSpace α] : Measurabl
eSet (∅ : Set α)
· 使用定理 `Set.disjoint_empty`：∀ {α : Type u} (s : Set α), Disjoint s ∅
-/
theorem map_empty_eq_zero {β} [AddCancelMonoid β] {T : Set α → β} (hT : FinMeasAdditive μ T) :
    T ∅ = 0 := by
  have h_empty : μ ∅ ≠ ∞ := (measure_empty.le.trans_lt ENNReal.coe_lt_top).ne
  specialize hT ∅ ∅ MeasurableSet.empty MeasurableSet.empty h_empty h_empty (disjoint_empty _)
  rw [Set.union_empty] at hT
  nth_rw 1 [← add_zero (T ∅)] at hT
  exact (add_left_cancel hT).symm

end AddMonoid

section AddCommMonoid

variable [AddCommMonoid β]

/-
**MeasureTheory.FinMeasAdditive.add** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Fin
MeasAdditive`。
形式化陈述：add (hT : FinMeasAdditive μ T) (hT' : FinMeasAdditive μ T') : FinMeasAddit
ive μ (T + T')
参数：hT : FinMeasAdditive μ T；hT' : FinMeasAdditive μ T'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `_private.Mathlib.MeasureTheory.Integral.FinMeasAdditive.0.MeasureTheory.
FinMeasAdditive.add._abel_1_1`：∀ {α : Type u_2} {β : Type u_1} {T T' : Set α → β
} [inst : AddCommMonoid β] (s t : Set α),   T s + T t + (T' s + T' t) = T s + T'
 s + (T t +…
-/
theorem add (hT : FinMeasAdditive μ T) (hT' : FinMeasAdditive μ T') :
    FinMeasAdditive μ (T + T') := by
  intro s t hs ht hμs hμt hst
  simp only [hT s t hs ht hμs hμt hst, hT' s t hs ht hμs hμt hst, Pi.add_apply]
  abel
/-
**MeasureTheory.FinMeasAdditive.add_measure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.FinMeasAdditive`。
形式化陈述：add_measure {ν : Measure α} (hT : FinMeasAdditive μ T) (hT' : FinMeasAddit
ive ν T') : FinMeasAdditive (μ + ν) (T + T')
参数：hT : FinMeasAdditive μ T；hT' : FinMeasAdditive ν T'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.FinMeasAdditive.add`：add (hT : FinMeasAdditive μ T) (hT' :
 FinMeasAdditive μ T') : FinMeasAdditive μ (T + T')
· 使用定理 `MeasureTheory.FinMeasAdditive.add_right_measure`：add_right_measure {ν : 
Measure α} (hT : FinMeasAdditive μ T) : FinMeasAdditive (μ + ν) T
· 使用定理 `MeasureTheory.FinMeasAdditive.add_left_measure`：add_left_measure {ν : Me
asure α} (hT : FinMeasAdditive μ T) : FinMeasAdditive (ν + μ) T
-/
theorem add_measure {ν : Measure α} (hT : FinMeasAdditive μ T) (hT' : FinMeasAdditive ν T') :
    FinMeasAdditive (μ + ν) (T + T') :=
  hT.add_right_measure.add (hT'.add_left_measure)
/-
**MeasureTheory.FinMeasAdditive.map_iUnion_fin_meas_set_eq_sum** 是 Mathlib 中的一个定
理，位于命名空间 `MeasureTheory.FinMeasAdditive`。
形式化陈述：map_iUnion_fin_meas_set_eq_sum (T : Set α -> β) (T_empty : T ∅ = 0) (h_add
 : FinMeasAdditive μ T) {ι} (S : ι -> Set α) (sι : Finset ι) (hS_meas : forall i
, MeasurableSet (S i)) (hSp : forall i in sι, μ (S i) != ∞) (h_disj : forallᵉ (i
 in sι) (j in sι), i != j -> Disjoint (S i) (S j)) : T (⋃ i in sι, S i) = ∑ i in
 sι, T (S i)
参数：T : Set α -> β；T_empty : T ∅ = 0；h_add : FinMeasAdditive μ T；S : ι -> Set α；s
ι : Finset ι；hS_meas : forall i, MeasurableSet (S i)；hSp : forall i in sι, μ (S 
i) != ∞；h_disj : forallᵉ (i in sι) (j in sι), i != j -> Disjoint (S i) (S j)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_false`：iUnion_false {s : False -> Set α} : iUnion s = ∅
· 使用定理 `Set.iUnion_empty`：iUnion_empty : (⋃ _ : ι, ∅ : Set α) = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s
· 使用定理 `Finset.measurableSet_biUnion`：Finset.measurableSet_biUnion {f : β -> Set
 α} (s : Finset β) (h : forall b in s, MeasurableSet (f b)) : MeasurableSet (⋃ b
 in s, f b)
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `MeasureTheory.measure_biUnion_lt_top`：measure_biUnion_lt_top {s : Set β}
 {f : β -> Set α} (hs : s.Finite) (hfin : forall i in s, μ (f i) < ∞) : μ (⋃ i i
n s, f i) < ∞
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Finset.iSup_insert`：iSup_insert (a : α) (s : Finset α) (t : α -> β) : ⨆ 
x in insert a s, t x = t a ⊔ ⨆ x in s, t x
-/
theorem map_iUnion_fin_meas_set_eq_sum (T : Set α → β) (T_empty : T ∅ = 0)
    (h_add : FinMeasAdditive μ T) {ι} (S : ι → Set α) (sι : Finset ι)
    (hS_meas : ∀ i, MeasurableSet (S i)) (hSp : ∀ i ∈ sι, μ (S i) ≠ ∞)
    (h_disj : ∀ᵉ (i ∈ sι) (j ∈ sι), i ≠ j → Disjoint (S i) (S j)) :
    T (⋃ i ∈ sι, S i) = ∑ i ∈ sι, T (S i) := by
  classical
  revert hSp h_disj
  refine Finset.induction_on sι ?_ ?_
  · simp only [Finset.notMem_empty, IsEmpty.forall_iff, iUnion_false, iUnion_empty, sum_empty,
      imp_true_iff, T_empty]
  intro a s has h hps h_disj
  rw [Finset.sum_insert has, ← h]
  swap; · exact fun i hi => hps i (Finset.mem_insert_of_mem hi)
  swap
  · exact fun i hi j hj hij =>
      h_disj i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
  rw [←
    h_add (S a) (⋃ i ∈ s, S i) (hS_meas a) (measurableSet_biUnion _ fun i _ => hS_meas i)
      (hps a (Finset.mem_insert_self a s))]
  · congr; convert! Finset.iSup_insert a s S
  · exact (measure_biUnion_lt_top s.finite_toSet fun i hi ↦
      (hps i <| Finset.mem_insert_of_mem hi).lt_top).ne
  · simp_rw [Set.disjoint_iUnion_right]
    intro i hi
    refine h_disj a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi) fun hai ↦ ?_
    rw [← hai] at hi
    exact has hi

end AddCommMonoid

/-
**MeasureTheory.FinMeasAdditive.neg** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Fin
MeasAdditive`。
形式化陈述：neg [AddGroup β] (hT : FinMeasAdditive μ T) : FinMeasAdditive μ (-T)
参数：hT : FinMeasAdditive μ T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_add_rev`：∀ {G : Type u_1} [inst : SubtractionMonoid G] (a b : G), -(
a + b) = -b + -a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem neg [AddGroup β] (hT : FinMeasAdditive μ T) :
    FinMeasAdditive μ (-T) := by
  intro s t hs ht hμs hμt hst
  have h_comm : T s + T t = T t + T s := by
    rw [← hT s t hs ht hμs hμt hst, ← hT t s ht hs hμt hμs hst.symm, union_comm]
  simp_all [hT s t hs ht hμs hμt hst, neg_add_rev]
/-
**MeasureTheory.FinMeasAdditive.sub** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Fin
MeasAdditive`。
形式化陈述：sub [AddCommGroup β] (hT : FinMeasAdditive μ T) (hT' : FinMeasAdditive μ T
') : FinMeasAdditive μ (T - T')
参数：hT : FinMeasAdditive μ T；hT' : FinMeasAdditive μ T'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.FinMeasAdditive.add`：add (hT : FinMeasAdditive μ T) (hT' :
 FinMeasAdditive μ T') : FinMeasAdditive μ (T + T')
· 使用定理 `MeasureTheory.FinMeasAdditive.neg`：neg [AddGroup β] (hT : FinMeasAdditiv
e μ T) : FinMeasAdditive μ (-T)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
-/
theorem sub [AddCommGroup β] (hT : FinMeasAdditive μ T) (hT' : FinMeasAdditive μ T') :
    FinMeasAdditive μ (T - T') :=
  sub_eq_add_neg T T' ▸ hT.add hT'.neg

end FinMeasAdditive

/-- A `FinMeasAdditive` set function whose norm on every set is less than the measure of the
set (up to a multiplicative constant). -/
/-
**MeasureTheory.DominatedFinMeasAdditive** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheor
y`。
形式化陈述：DominatedFinMeasAdditive {β} [SeminormedAddCommGroup β] {_ : MeasurableSpa
ce α} (μ : Measure α) (T : Set α -> β) (C : Real) : Prop
参数：μ : Measure α；T : Set α -> β；C : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `FinMeasAdditive` set function whose norm on every set is less than the measur
e of the
set (up to a multiplicative constant).
-/
def DominatedFinMeasAdditive {β} [SeminormedAddCommGroup β] {_ : MeasurableSpace α} (μ : Measure α)
    (T : Set α → β) (C : ℝ) : Prop :=
  FinMeasAdditive μ T ∧ ∀ s, MeasurableSet s → μ s < ∞ → ‖T s‖ ≤ C * μ.real s

namespace DominatedFinMeasAdditive

variable {β : Type*} [SeminormedAddCommGroup β] {T T' : Set α → β} {C C' : ℝ}

/-
**MeasureTheory.DominatedFinMeasAdditive.zero** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.DominatedFinMeasAdditive`。
形式化陈述：zero {m : MeasurableSpace α} (μ : Measure α) (hC : 0 <= C) : DominatedFinM
easAdditive μ (0 : Set α -> β) C
参数：μ : Measure α；hC : 0 <= C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.FinMeasAdditive.zero`：zero : FinMeasAdditive μ (0 : Set α 
-> β)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.zero_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Zer
o (M i)] (i : ι), 0 i = 0
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `ENNReal.toReal_nonneg`：∀ {a : ENNReal}, 0 ≤ a.toReal
-/
theorem zero {m : MeasurableSpace α} (μ : Measure α) (hC : 0 ≤ C) :
    DominatedFinMeasAdditive μ (0 : Set α → β) C := by
  refine ⟨FinMeasAdditive.zero, fun s _ _ => ?_⟩
  rw [Pi.zero_apply, norm_zero]
  exact mul_nonneg hC toReal_nonneg
/-
**MeasureTheory.DominatedFinMeasAdditive.eq_zero_of_measure_zero** 是 Mathlib 中的一
个定理，位于命名空间 `MeasureTheory.DominatedFinMeasAdditive`。
形式化陈述：eq_zero_of_measure_zero {β : Type*} [NormedAddCommGroup β] {T : Set α -> β
} {C : Real} (hT : DominatedFinMeasAdditive μ T C) {s : Set α} (hs : MeasurableS
et s) (hs_zero : μ s = 0) : T s = 0
参数：hT : DominatedFinMeasAdditive μ T C；hs : MeasurableSet s；hs_zero : μ s = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `norm_eq_zero`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a‖ = 
0 ↔ a = 0
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `MeasureTheory.measureReal_def`：measureReal_def {α : Type*} {m : Measurab
leSpace α} (μ : Measure α) (s : Set α) : μ.real s = (μ s).toReal
· 使用定理 `ENNReal.toReal_zero`：ENNReal.toReal 0 = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
-/
theorem eq_zero_of_measure_zero {β : Type*} [NormedAddCommGroup β] {T : Set α → β} {C : ℝ}
    (hT : DominatedFinMeasAdditive μ T C) {s : Set α} (hs : MeasurableSet s) (hs_zero : μ s = 0) :
    T s = 0 := by
  refine norm_eq_zero.mp ?_
  refine ((hT.2 s hs (by simp [hs_zero])).trans (le_of_eq ?_)).antisymm (norm_nonneg _)
  rw [measureReal_def, hs_zero, ENNReal.toReal_zero, mul_zero]
/-
**MeasureTheory.DominatedFinMeasAdditive.eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.DominatedFinMeasAdditive`。
形式化陈述：eq_zero {β : Type*} [NormedAddCommGroup β] {T : Set α -> β} {C : Real} {_ 
: MeasurableSpace α} (hT : DominatedFinMeasAdditive (0 : Measure α) T C) {s : Se
t α} (hs : MeasurableSet s) : T s = 0
参数：hT : DominatedFinMeasAdditive (0 : Measure α) T C；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.DominatedFinMeasAdditive.eq_zero_of_measure_zero`：eq_zero_
of_measure_zero {β : Type*} [NormedAddCommGroup β] {T : Set α -> β} {C : Real} (
hT : DominatedFinMeasAdditive μ T C) {s : Set α} (hs…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eq_zero {β : Type*} [NormedAddCommGroup β] {T : Set α → β} {C : ℝ} {_ : MeasurableSpace α}
    (hT : DominatedFinMeasAdditive (0 : Measure α) T C) {s : Set α} (hs : MeasurableSet s) :
    T s = 0 :=
  eq_zero_of_measure_zero hT hs (by simp only [Measure.coe_zero, Pi.zero_apply])
/-
**MeasureTheory.DominatedFinMeasAdditive.of_le** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.DominatedFinMeasAdditive`。
形式化陈述：of_le (hT : DominatedFinMeasAdditive μ T C) (hC : C <= C') : DominatedFinM
easAdditive μ T C'
参数：hT : DominatedFinMeasAdditive μ T C；hC : C <= C'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `MeasureTheory.measureReal_nonneg`：∀ {α : Type u_1} {x : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α}, 0 ≤ μ.real s
-/
theorem of_le (hT : DominatedFinMeasAdditive μ T C) (hC : C ≤ C') :
    DominatedFinMeasAdditive μ T C' :=
  ⟨hT.1, fun s hs hμs => (hT.2 s hs hμs).trans <| mul_le_mul_of_nonneg_right hC measureReal_nonneg⟩
/-
**MeasureTheory.DominatedFinMeasAdditive.add** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.DominatedFinMeasAdditive`。
形式化陈述：add (hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedFinMeasAdditive 
μ T' C') : DominatedFinMeasAdditive μ (T + T') (C + C')
参数：hT : DominatedFinMeasAdditive μ T C；hT' : DominatedFinMeasAdditive μ T' C'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.FinMeasAdditive.add`：add (hT : FinMeasAdditive μ T) (hT' :
 FinMeasAdditive μ T') : FinMeasAdditive μ (T + T')
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.add_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Add 
(M i)] (f g : (i : ι) → M i) (i : ι), (f + g) i = f i + g i
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `norm_add_le`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a b : E), ‖
a + b‖ ≤ ‖a‖ + ‖b‖
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem add (hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedFinMeasAdditive μ T' C') :
    DominatedFinMeasAdditive μ (T + T') (C + C') := by
  refine ⟨hT.1.add hT'.1, fun s hs hμs => ?_⟩
  rw [Pi.add_apply, add_mul]
  exact (norm_add_le _ _).trans (add_le_add (hT.2 s hs hμs) (hT'.2 s hs hμs))
/-
**MeasureTheory.DominatedFinMeasAdditive.neg** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.DominatedFinMeasAdditive`。
形式化陈述：neg (hT : DominatedFinMeasAdditive μ T C) : DominatedFinMeasAdditive μ (-T
) C
参数：hT : DominatedFinMeasAdditive μ T C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.FinMeasAdditive.neg`：neg [AddGroup β] (hT : FinMeasAdditiv
e μ T) : FinMeasAdditive μ (-T)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem neg (hT : DominatedFinMeasAdditive μ T C) :
    DominatedFinMeasAdditive μ (-T) C :=
  ⟨hT.1.neg, fun s hs hμs => by simpa using hT.2 s hs hμs⟩
/-
**MeasureTheory.DominatedFinMeasAdditive.smul** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.DominatedFinMeasAdditive`。
形式化陈述：smul [SeminormedAddGroup 𝕜] [DistribSMul 𝕜 β] [IsBoundedSMul 𝕜 β] (hT : Do
minatedFinMeasAdditive μ T C) (c : 𝕜) : DominatedFinMeasAdditive μ (fun s => c •
 T s) (‖c‖ * C)
参数：hT : DominatedFinMeasAdditive μ T C；c : 𝕜。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.FinMeasAdditive.smul`：smul [DistribSMul 𝕜 β] (hT : FinMeas
Additive μ T) (c : 𝕜) : FinMeasAdditive μ fun s => c • T s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `norm_smul_le`：norm_smul_le (r : α) (x : β) : ‖r • x‖ <= ‖r‖ * ‖x‖
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
-/
theorem smul [SeminormedAddGroup 𝕜] [DistribSMul 𝕜 β] [IsBoundedSMul 𝕜 β]
    (hT : DominatedFinMeasAdditive μ T C) (c : 𝕜) :
    DominatedFinMeasAdditive μ (fun s => c • T s) (‖c‖ * C) := by
  refine ⟨hT.1.smul c, fun s hs hμs => (norm_smul_le _ _).trans ?_⟩
  rw [mul_assoc]
  exact mul_le_mul le_rfl (hT.2 s hs hμs) (norm_nonneg _) (norm_nonneg _)
/-
**MeasureTheory.DominatedFinMeasAdditive.of_measure_le** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.DominatedFinMeasAdditive`。
形式化陈述：of_measure_le {μ' : Measure α} (h : μ <= μ') (hT : DominatedFinMeasAdditiv
e μ T C) (hC : 0 <= C) : DominatedFinMeasAdditive μ' T C
参数：h : μ <= μ'；hT : DominatedFinMeasAdditive μ T C；hC : 0 <= C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `top_unique`：top_unique (h : ⊤ <= a) : a = ⊤
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.FinMeasAdditive.of_eq_top_imp_eq_top`：of_eq_top_imp_eq_top
 {μ' : Measure α} (h : forall s, MeasurableSet s -> μ s = ∞ -> μ' s = ∞) (hT : F
inMeasAdditive μ T) : FinMeasAdditive μ'…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `ENNReal.toReal_mono`：toReal_mono (hb : b != ∞) (h : a <= b) : a.toReal <
= b.toReal
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `MeasureTheory.Measure.measure_mono_left`：∀ {α : Type u_1} {m0 : Measurab
leSpace α} {μ ν : MeasureTheory.Measure α}, μ ≤ ν → ∀ (s : Set α), μ s ≤ ν s
-/
theorem of_measure_le {μ' : Measure α} (h : μ ≤ μ') (hT : DominatedFinMeasAdditive μ T C)
    (hC : 0 ≤ C) : DominatedFinMeasAdditive μ' T C := by
  have h' : ∀ s, μ s = ∞ → μ' s = ∞ := fun s hs ↦ top_unique <| hs.symm.trans_le (h _)
  refine ⟨hT.1.of_eq_top_imp_eq_top fun s _ ↦ h' s, fun s hs hμ's ↦ ?_⟩
  have hμs : μ s < ∞ := (h s).trans_lt hμ's
  calc
    ‖T s‖ ≤ C * μ.real s := hT.2 s hs hμs
    _ ≤ C * μ'.real s := by
      simp only [measureReal_def]
      gcongr
      exact hμ's.ne
/-
**MeasureTheory.DominatedFinMeasAdditive.add_measure** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.DominatedFinMeasAdditive`。
形式化陈述：add_measure {C' : Real} (μ ν : Measure α) (hT : DominatedFinMeasAdditive μ
 T C) (hT' : DominatedFinMeasAdditive ν T' C') : DominatedFinMeasAdditive (μ + ν
) (T + T') (max C C')
参数：μ ν : Measure α；hT : DominatedFinMeasAdditive μ T C；hT' : DominatedFinMeasAdd
itive ν T' C'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.FinMeasAdditive.add_measure`：add_measure {ν : Measure α} (
hT : FinMeasAdditive μ T) (hT' : FinMeasAdditive ν T') : FinMeasAdditive (μ + ν)
 (T + T')
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.Measure.le_add_right`：∀ {α : Type u_1} {m0 : MeasurableSpa
ce α} {μ ν ν' : MeasureTheory.Measure α}, μ ≤ ν → μ ≤ ν + ν'
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `MeasureTheory.Measure.le_add_left`：∀ {α : Type u_1} {m0 : MeasurableSpac
e α} {μ ν ν' : MeasureTheory.Measure α}, μ ≤ ν → μ ≤ ν' + ν
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.add_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Add 
(M i)] (f g : (i : ι) → M i) (i : ι), (f + g) i = f i + g i
· 使用定理 `MeasureTheory.measureReal_add_apply`：measureReal_add_apply {μ₁ μ₂ : Meas
ure α} (h₁ : μ₁ s != ∞
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `norm_add_le`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a b : E), ‖
a + b‖ ≤ ‖a‖ + ‖b‖
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `MeasureTheory.measureReal_nonneg`：∀ {α : Type u_1} {x : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α}, 0 ≤ μ.real s
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
-/
theorem add_measure {C' : ℝ} (μ ν : Measure α)
    (hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedFinMeasAdditive ν T' C') :
    DominatedFinMeasAdditive (μ + ν) (T + T') (max C C') := by
  refine ⟨hT.1.add_measure hT'.1, fun s hs hsf ↦ ?_⟩
  have hμs : μ s < ∞ := (Measure.le_add_right le_rfl s).trans_lt hsf
  have hνs : ν s < ∞ := (Measure.le_add_left le_rfl s).trans_lt hsf
  rw [Pi.add_apply, measureReal_add_apply hμs.ne hνs.ne, mul_add]
  calc
    ‖T s + T' s‖ ≤ ‖T s‖ + ‖T' s‖ := norm_add_le _ _
    _ ≤ C * μ.real s + C' * ν.real s := add_le_add (hT.2 s hs hμs) (hT'.2 s hs hνs)
    _ ≤ max C C' * μ.real s + max C C' * ν.real s := by
      gcongr
      · exact le_max_left C C'
      · exact le_max_right C C'
/-
**MeasureTheory.DominatedFinMeasAdditive.sub_measure** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.DominatedFinMeasAdditive`。
形式化陈述：sub_measure {C' : Real} (μ ν : Measure α) (hT : DominatedFinMeasAdditive μ
 T C) (hT' : DominatedFinMeasAdditive ν T' C') : DominatedFinMeasAdditive (μ + ν
) (T - T') (max C C')
参数：μ ν : Measure α；hT : DominatedFinMeasAdditive μ T C；hT' : DominatedFinMeasAdd
itive ν T' C'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.DominatedFinMeasAdditive.add_measure`：add_measure {C' : Re
al} (μ ν : Measure α) (hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedFinM
easAdditive ν T' C') : DominatedFinMeasA…
· 使用定理 `MeasureTheory.DominatedFinMeasAdditive.neg`：neg (hT : DominatedFinMeasAd
ditive μ T C) : DominatedFinMeasAdditive μ (-T) C
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
-/
theorem sub_measure {C' : ℝ} (μ ν : Measure α)
    (hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedFinMeasAdditive ν T' C') :
    DominatedFinMeasAdditive (μ + ν) (T - T') (max C C') :=
  sub_eq_add_neg T T' ▸ hT.add_measure μ ν hT'.neg
/-
**MeasureTheory.DominatedFinMeasAdditive.add_measure_right** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory.DominatedFinMeasAdditive`。
形式化陈述：add_measure_right {_ : MeasurableSpace α} (μ ν : Measure α) (hT : Dominate
dFinMeasAdditive μ T C) (hC : 0 <= C) : DominatedFinMeasAdditive (μ + ν) T C
参数：μ ν : Measure α；hT : DominatedFinMeasAdditive μ T C；hC : 0 <= C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.DominatedFinMeasAdditive.of_measure_le`：of_measure_le {μ' 
: Measure α} (h : μ <= μ') (hT : DominatedFinMeasAdditive μ T C) (hC : 0 <= C) :
 DominatedFinMeasAdditive μ' T C
· 使用定理 `MeasureTheory.Measure.le_add_right`：∀ {α : Type u_1} {m0 : MeasurableSpa
ce α} {μ ν ν' : MeasureTheory.Measure α}, μ ≤ ν → μ ≤ ν + ν'
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem add_measure_right {_ : MeasurableSpace α} (μ ν : Measure α)
    (hT : DominatedFinMeasAdditive μ T C) (hC : 0 ≤ C) : DominatedFinMeasAdditive (μ + ν) T C :=
  of_measure_le (Measure.le_add_right le_rfl) hT hC
/-
**MeasureTheory.DominatedFinMeasAdditive.add_measure_left** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory.DominatedFinMeasAdditive`。
形式化陈述：add_measure_left {_ : MeasurableSpace α} (μ ν : Measure α) (hT : Dominated
FinMeasAdditive ν T C) (hC : 0 <= C) : DominatedFinMeasAdditive (μ + ν) T C
参数：μ ν : Measure α；hT : DominatedFinMeasAdditive ν T C；hC : 0 <= C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.DominatedFinMeasAdditive.of_measure_le`：of_measure_le {μ' 
: Measure α} (h : μ <= μ') (hT : DominatedFinMeasAdditive μ T C) (hC : 0 <= C) :
 DominatedFinMeasAdditive μ' T C
· 使用定理 `MeasureTheory.Measure.le_add_left`：∀ {α : Type u_1} {m0 : MeasurableSpac
e α} {μ ν ν' : MeasureTheory.Measure α}, μ ≤ ν → μ ≤ ν' + ν
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem add_measure_left {_ : MeasurableSpace α} (μ ν : Measure α)
    (hT : DominatedFinMeasAdditive ν T C) (hC : 0 ≤ C) : DominatedFinMeasAdditive (μ + ν) T C :=
  of_measure_le (Measure.le_add_left le_rfl) hT hC
/-
**MeasureTheory.DominatedFinMeasAdditive.finsetSum_measure** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory.DominatedFinMeasAdditive`。
形式化陈述：finsetSum_measure {ι} {s : Finset ι} (hs : s.Nonempty) (μ : ι -> Measure α
) (T : ι -> Set α -> β) (C : ι -> Real) (hT : forall i, DominatedFinMeasAdditive
 (μ i) (T i) (C i)) : DominatedFinMeasAdditive (∑ i in s, μ i) (∑ i in s, T i) (
s.sup' hs C)
参数：hs : s.Nonempty；μ : ι -> Measure α；T : ι -> Set α -> β；C : ι -> Real；hT : for
all i, DominatedFinMeasAdditive (μ i) (T i) (C i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Nonempty.cons_induction`：∀ {α : Type u_3} {motive : (s : Finset α
) → s.Nonempty → Prop},   (∀ (a : α), motive {a} ⋯) →     (∀ (a : α) (s : Finset
 α) (h : a ∉ s) (hs …
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Finset.cons_nonempty`：cons_nonempty (h : a ∉ s) : (cons a s h).Nonempty
· 使用定理 `Finset.sum_cons`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι} 
[inst : AddCommMonoid M] {f : ι → M} (h : a ∉ s),   ∑ x ∈ Finset.cons a s h, f x
 = f …
· 使用定理 `Finset.sup'_cons`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup
 α] {s : Finset β} (H : s.Nonempty) (f : β → α) {b : β}   {hb : b ∉ s}, (Finset.
cons b…
· 使用定理 `MeasureTheory.DominatedFinMeasAdditive.add_measure`：add_measure {C' : Re
al} (μ ν : Measure α) (hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedFinM
easAdditive ν T' C') : DominatedFinMeasA…
-/
theorem finsetSum_measure {ι} {s : Finset ι} (hs : s.Nonempty) (μ : ι → Measure α)
    (T : ι → Set α → β) (C : ι → ℝ) (hT : ∀ i, DominatedFinMeasAdditive (μ i) (T i) (C i)) :
    DominatedFinMeasAdditive (∑ i ∈ s, μ i) (∑ i ∈ s, T i) (s.sup' hs C) := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton i => simp_all
  | @cons i s his hs' ih =>
    simpa [his, Finset.sup'_cons hs' C] using (hT i).add_measure (μ i) (∑ j ∈ s, μ j) ih
/-
**MeasureTheory.DominatedFinMeasAdditive.of_smul_measure** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.DominatedFinMeasAdditive`。
形式化陈述：of_smul_measure {c : Real>=0∞} (hc_ne_top : c != ∞) (hT : DominatedFinMeas
Additive (c • μ) T C) : DominatedFinMeasAdditive μ T (c.toReal * C)
参数：hc_ne_top : c != ∞；hT : DominatedFinMeasAdditive (c • μ) T C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `MeasureTheory.FinMeasAdditive.of_eq_top_imp_eq_top`：of_eq_top_imp_eq_top
 {μ' : Measure α} (h : forall s, MeasurableSet s -> μ s = ∞ -> μ' s = ∞) (hT : F
inMeasAdditive μ T) : FinMeasAdditive μ'…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `MeasureTheory.measureReal_ennreal_smul_apply`：∀ {α : Type u_1} {x : Meas
urableSpace α} {μ : MeasureTheory.Measure α} {s : Set α} (c : ENNReal),   (c • μ
).real s = c.toReal * μ.real s
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
（共 31 条，此处仅展示前 30 条）
-/
theorem of_smul_measure {c : ℝ≥0∞} (hc_ne_top : c ≠ ∞) (hT : DominatedFinMeasAdditive (c • μ) T C) :
    DominatedFinMeasAdditive μ T (c.toReal * C) := by
  have h : ∀ s, MeasurableSet s → c • μ s = ∞ → μ s = ∞ := by
    intro s _ hcμs
    simp only [hc_ne_top, smul_eq_mul, ENNReal.mul_eq_top, or_false, Ne,
      false_and] at hcμs
    exact hcμs.2
  refine ⟨hT.1.of_eq_top_imp_eq_top (μ := c • μ) h, fun s hs hμs => ?_⟩
  have hcμs : c • μ s ≠ ∞ := mt (h s hs) hμs.ne
  rw [smul_eq_mul] at hcμs
  refine (hT.2 s hs hcμs.lt_top).trans (le_of_eq ?_)
  simp only [measureReal_ennreal_smul_apply]
  ring
/-
**MeasureTheory.DominatedFinMeasAdditive.of_measure_le_smul** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory.DominatedFinMeasAdditive`。
形式化陈述：of_measure_le_smul {μ' : Measure α} {c : Real>=0∞} (hc : c != ∞) (h : μ <=
 c • μ') (hT : DominatedFinMeasAdditive μ T C) (hC : 0 <= C) : DominatedFinMeasA
dditive μ' T (c.toReal * C)
参数：hc : c != ∞；h : μ <= c • μ'；hT : DominatedFinMeasAdditive μ T C；hC : 0 <= C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.DominatedFinMeasAdditive.of_smul_measure`：of_smul_measure 
{c : Real>=0∞} (hc_ne_top : c != ∞) (hT : DominatedFinMeasAdditive (c • μ) T C) 
: DominatedFinMeasAdditive μ T (c.toReal * C…
· 使用定理 `MeasureTheory.DominatedFinMeasAdditive.of_measure_le`：of_measure_le {μ' 
: Measure α} (h : μ <= μ') (hT : DominatedFinMeasAdditive μ T C) (hC : 0 <= C) :
 DominatedFinMeasAdditive μ' T C
-/
theorem of_measure_le_smul {μ' : Measure α} {c : ℝ≥0∞} (hc : c ≠ ∞) (h : μ ≤ c • μ')
    (hT : DominatedFinMeasAdditive μ T C) (hC : 0 ≤ C) :
    DominatedFinMeasAdditive μ' T (c.toReal * C) :=
  (hT.of_measure_le h hC).of_smul_measure hc

end DominatedFinMeasAdditive

end FinMeasAdditive

namespace SimpleFunc

/-- Extend `Set α → (F →L[ℝ] F')` to `(α →ₛ F) → F'`. -/
/-
**MeasureTheory.SimpleFunc.setToSimpleFunc** 是 Mathlib 中的一个定义，位于命名空间 `MeasureThe
ory.SimpleFunc`。
形式化陈述：setToSimpleFunc {_ : MeasurableSpace α} (T : Set α -> F ->L[Real] F') (f :
 α ->ₛ F) : F'
参数：T : Set α -> F ->L[Real] F'；f : α ->ₛ F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extend `Set α → (F →L[ℝ] F')` to `(α →ₛ F) → F'`.
-/
def setToSimpleFunc {_ : MeasurableSpace α} (T : Set α → F →L[ℝ] F') (f : α →ₛ F) : F' :=
  ∑ x ∈ f.range, T (f ⁻¹' {x}) x

@[simp]
/-
**MeasureTheory.SimpleFunc.setToSimpleFunc_zero** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.SimpleFunc`。
形式化陈述：setToSimpleFunc_zero {m : MeasurableSpace α} (f : α ->ₛ F) : setToSimpleFu
nc (0 : Set α -> F ->L[Real] F') f = 0
参数：f : α ->ₛ F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem setToSimpleFunc_zero {m : MeasurableSpace α} (f : α →ₛ F) :
    setToSimpleFunc (0 : Set α → F →L[ℝ] F') f = 0 := by simp [setToSimpleFunc]
/-
**MeasureTheory.SimpleFunc.setToSimpleFunc_zero'** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.SimpleFunc`。
形式化陈述：setToSimpleFunc_zero' {T : Set α -> E ->L[Real] F'} (h_zero : forall s, Me
asurableSet s -> μ s < ∞ -> T s = 0) (f : α ->ₛ E) (hf : Integrable f μ) : setTo
SimpleFunc T f = 0
参数：h_zero : forall s, MeasurableSet s -> μ s < ∞ -> T s = 0；f : α ->ₛ E；hf : Int
egrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.SimpleFunc.measurableSet_fiber`：measurableSet_fiber (f : α
 ->ₛ β) (x : β) : MeasurableSet (f ⁻¹' {x})
· 使用定理 `MeasureTheory.SimpleFunc.measure_preimage_lt_top_of_integrable`：measure_
preimage_lt_top_of_integrable (f : α ->ₛ E) (hf : Integrable f μ) {x : E} (hx : 
x != 0) : μ (f ⁻¹' {x}) < ∞
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
-/
theorem setToSimpleFunc_zero' {T : Set α → E →L[ℝ] F'}
    (h_zero : ∀ s, MeasurableSet s → μ s < ∞ → T s = 0) (f : α →ₛ E) (hf : Integrable f μ) :
    setToSimpleFunc T f = 0 := by
  simp_rw [setToSimpleFunc]
  refine sum_eq_zero fun x _ => ?_
  by_cases hx0 : x = 0
  · simp [hx0]
  rw [h_zero (f ⁻¹' ({x} : Set E)) (measurableSet_fiber _ _)
      (measure_preimage_lt_top_of_integrable f hf hx0), zero_apply]

@[simp]
/-
**MeasureTheory.SimpleFunc.setToSimpleFunc_zero_apply** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.SimpleFunc`。
形式化陈述：setToSimpleFunc_zero_apply {m : MeasurableSpace α} (T : Set α -> F ->L[Rea
l] F') : setToSimpleFunc T (0 : α ->ₛ F) = 0
参数：T : Set α -> F ->L[Real] F'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SimpleFunc.range_eq_empty_of_isEmpty`：range_eq_empty_of_is
Empty {β} [hα : IsEmpty α] (f : α ->ₛ β) : f.range = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.SimpleFunc.range_zero`：∀ {α : Type u_1} {β : Type u_2} [in
st : MeasurableSpace α] [Nonempty α] [inst_2 : Zero β],   MeasureTheory.SimpleFu
nc.range 0 = {0}
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
-/
theorem setToSimpleFunc_zero_apply {m : MeasurableSpace α} (T : Set α → F →L[ℝ] F') :
    setToSimpleFunc T (0 : α →ₛ F) = 0 := by
  cases isEmpty_or_nonempty α <;> simp [setToSimpleFunc]
/-
**MeasureTheory.SimpleFunc.setToSimpleFunc_eq_sum_filter** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.SimpleFunc`。
形式化陈述：setToSimpleFunc_eq_sum_filter [DecidablePred fun x => x != (0 : F)] {m : M
easurableSpace α} (T : Set α -> F ->L[Real] F') (f : α ->ₛ F) : setToSimpleFunc 
T f = ∑ x in f.range with x != 0, T (f ⁻¹' {x}) x
参数：0 : F；T : Set α -> F ->L[Real] F'；f : α ->ₛ F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_filter_of_ne`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} 
[inst : AddCommMonoid M] {f : ι → M} {p : ι → Prop}   [inst_1 : DecidablePred p]
, (∀ x ∈ s, f…
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
-/
theorem setToSimpleFunc_eq_sum_filter [DecidablePred fun x ↦ x ≠ (0 : F)]
    {m : MeasurableSpace α} (T : Set α → F →L[ℝ] F') (f : α →ₛ F) :
    setToSimpleFunc T f = ∑ x ∈ f.range with x ≠ 0, T (f ⁻¹' {x}) x := by
  symm
  refine sum_filter_of_ne fun x _ => mt fun hx0 => ?_
  rw [hx0]
  exact map_zero _

/-- The `setToSimpleFunc` is equal to a sum over any set that includes `f.range` (except `0`). -/
/-
**MeasureTheory.SimpleFunc.setToSimpleFunc_eq_sum_of_subset** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory.SimpleFunc`。
形式化陈述：setToSimpleFunc_eq_sum_of_subset [DecidablePred fun x : F => x != 0] (T : 
Set α -> F ->L[Real] F') (hT : T ∅ = 0) {f : α ->ₛ F} {s : Finset F} (hs : {x in
 f.range | x != 0} subseteq s) : setToSimpleFunc T f = ∑ x in s, T (f ⁻¹' {x}) x
参数：T : Set α -> F ->L[Real] F'；hT : T ∅ = 0；hs : {x in f.range | x != 0} subsete
q s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SimpleFunc.setToSimpleFunc_eq_sum_filter`：setToSimpleFunc_
eq_sum_filter [DecidablePred fun x => x != (0 : F)] {m : MeasurableSpace α} (T :
 Set α -> F ->L[Real] F') (f : α ->ₛ F) : se…
· 使用定理 `Finset.sum_subset`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [i
nst : AddCommMonoid M] {f : ι → M},   s₁ ⊆ s₂ → (∀ x ∈ s₂, x ∉ s₁ → f x = 0) → ∑
 x ∈ s₁…
· 使用定理 `Or.symm`：∀ {a b : Prop}, a ∨ b → b ∨ a
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `not_and_or`：not_and_or : ¬(a ∧ b) ↔ ¬a ∨ ¬b
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.preimage_eq_empty`：preimage_eq_empty {s : Set β} (h : Disjoint s (ra
nge f)) : f ⁻¹' s = ∅
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `MeasureTheory.SimpleFunc.mem_range`：mem_range {f : α ->ₛ β} {b} : b in f
.range ↔ b in range f
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…

--- 原说明 ---
The `setToSimpleFunc` is equal to a sum over any set that includes `f.range` (ex
cept `0`).
-/
theorem setToSimpleFunc_eq_sum_of_subset [DecidablePred fun x : F => x ≠ 0]
    (T : Set α → F →L[ℝ] F') (hT : T ∅ = 0) {f : α →ₛ F} {s : Finset F}
    (hs : {x ∈ f.range | x ≠ 0} ⊆ s) :
    setToSimpleFunc T f = ∑ x ∈ s, T (f ⁻¹' {x}) x := by
  rw [setToSimpleFunc_eq_sum_filter, Finset.sum_subset hs]
  rintro x - hx; rw [Finset.mem_filter, not_and_or, Ne, Classical.not_not] at hx
  rcases hx.symm with (rfl | hx)
  · simp
  rw [SimpleFunc.mem_range] at hx
  rw [preimage_eq_empty] <;> simp [Set.disjoint_singleton_left, hx, hT]
/-
**MeasureTheory.SimpleFunc.map_setToSimpleFunc** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.SimpleFunc`。
形式化陈述：map_setToSimpleFunc (T : Set α -> F ->L[Real] F') (h_add : FinMeasAdditive
 μ T) {f : α ->ₛ G} (hf : Integrable f μ) {g : G -> F} (hg : g 0 = 0) : (f.map g
).setToSimpleFunc T = ∑ x in f.range, T (f ⁻¹' {x}) (g x)
参数：T : Set α -> F ->L[Real] F'；h_add : FinMeasAdditive μ T；hf : Integrable f μ；h
g : g 0 = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.FinMeasAdditive.map_empty_eq_zero`：map_empty_eq_zero {β} [
AddCancelMonoid β] {T : Set α -> β} (hT : FinMeasAdditive μ T) : T ∅ = 0
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `MeasureTheory.SimpleFunc.measure_preimage_lt_top_of_integrable`：measure_
preimage_lt_top_of_integrable (f : α ->ₛ E) (hf : Integrable f μ) {x : E} (hx : 
x != 0) : μ (f ⁻¹' {x}) < ∞
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `MeasureTheory.SimpleFunc.range_map`：range_map [DecidableEq γ] (g : β -> 
γ) (f : α ->ₛ β) : (f.map g).range = f.range.image g
· 使用定理 `Finset.sum_image'`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_4} [inst 
: AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι]   {s : Finset κ} {g : κ 
→ ι} (h…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.SimpleFunc.mem_range`：mem_range {f : α ->ₛ β} {b} : b in f
.range ↔ b in range f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `MeasureTheory.SimpleFunc.map_preimage_singleton`：map_preimage_singleton 
(f : α ->ₛ β) (g : β -> γ) (c : γ) : f.map g ⁻¹' {c} = f ⁻¹' ↑{b in f.range | g 
b = c}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.set_biUnion_preimage_singleton`：set_biUnion_preimage_singleton (f
 : α -> β) (s : Finset β) : ⋃ y in s, f ⁻¹' {y} = f ⁻¹' s
· 使用定理 `MeasureTheory.FinMeasAdditive.map_iUnion_fin_meas_set_eq_sum`：map_iUnion
_fin_meas_set_eq_sum (T : Set α -> β) (T_empty : T ∅ = 0) (h_add : FinMeasAdditi
ve μ T) {ι} (S : ι -> Set α) (sι : Finset ι) (hS_m…
· 使用定理 `MeasureTheory.SimpleFunc.measurableSet_fiber`：measurableSet_fiber (f : α
 ->ₛ β) (x : β) : MeasurableSet (f ⁻¹' {x})
· 使用定理 `sum_apply`：∀ {F : Type u_8} {α : Type u_9} {β : Type u_10} {ι : Type u_1
1} [inst : FunLike F α β] [inst_1 : AddCommMonoid β]   [inst_2 : AddCommMonoid …
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
-/
theorem map_setToSimpleFunc (T : Set α → F →L[ℝ] F') (h_add : FinMeasAdditive μ T) {f : α →ₛ G}
    (hf : Integrable f μ) {g : G → F} (hg : g 0 = 0) :
    (f.map g).setToSimpleFunc T = ∑ x ∈ f.range, T (f ⁻¹' {x}) (g x) := by
  classical
  have T_empty : T ∅ = 0 := h_add.map_empty_eq_zero
  have hfp : ∀ x ∈ f.range, x ≠ 0 → μ (f ⁻¹' {x}) ≠ ∞ := fun x _ hx0 =>
    (measure_preimage_lt_top_of_integrable f hf hx0).ne
  simp only [setToSimpleFunc, range_map]
  refine Finset.sum_image' _ fun b hb => ?_
  rcases mem_range.1 hb with ⟨a, rfl⟩
  by_cases h0 : g (f a) = 0
  · simp_rw [h0]
    rw [map_zero, Finset.sum_eq_zero fun x hx => ?_]
    rw [mem_filter] at hx
    rw [hx.2, map_zero]
  have h_left_eq :
    T (map g f ⁻¹' {g (f a)}) (g (f a))
      = T (f ⁻¹' ({b ∈ f.range | g b = g (f a)} : Finset _)) (g (f a)) := by
    rw [map_preimage_singleton]
  rw [h_left_eq]
  have h_left_eq' :
    T (f ⁻¹' ({b ∈ f.range | g b = g (f a)} : Finset _)) (g (f a))
      = T (⋃ y ∈ {b ∈ f.range | g b = g (f a)}, f ⁻¹' {y}) (g (f a)) := by
    rw [← Finset.set_biUnion_preimage_singleton]
  rw [h_left_eq']
  rw [h_add.map_iUnion_fin_meas_set_eq_sum T T_empty]
  · simp only [_root_.sum_apply]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [mem_filter] at hx
    rw [hx.2]
  · exact fun i => measurableSet_fiber _ _
  · grind
  · grind [Set.disjoint_iff]
/-
**MeasureTheory.SimpleFunc.setToSimpleFunc_congr'** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.SimpleFunc`。
形式化陈述：setToSimpleFunc_congr' (T : Set α -> E ->L[Real] F) (h_add : FinMeasAdditi
ve μ T) {f g : α ->ₛ E} (hf : Integrable f μ) (hg : Integrable g μ) (h : Pairwis
e fun x y => T (f ⁻¹' {x} inter g ⁻¹' {y}) = 0) : f.setToSimpleFunc T = g.setToS
impleFunc T
参数：T : Set α -> E ->L[Real] F；h_add : FinMeasAdditive μ T；hf : Integrable f μ；hg
 : Integrable g μ；h : Pairwise fun x y => T (f ⁻¹' {x} inter g ⁻¹' {y}) = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.SimpleFunc.integrable_pair`：integrable_pair {f : α ->ₛ E} 
{g : α ->ₛ F} : Integrable f μ -> Integrable g μ -> Integrable (pair f g) μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SimpleFunc.map_setToSimpleFunc`：map_setToSimpleFunc (T : S
et α -> F ->L[Real] F') (h_add : FinMeasAdditive μ T) {f : α ->ₛ G} (hf : Integr
able f μ) {g : G -> F} (hg : g 0 =…
· 使用定理 `Prod.fst_zero`：∀ {M : Type u_3} {N : Type u_4} [inst : Zero M] [inst_1 :
 Zero N], 0.1 = 0
· 使用定理 `Prod.snd_zero`：∀ {M : Type u_3} {N : Type u_4} [inst : Zero M] [inst_1 :
 Zero N], 0.2 = 0
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.SimpleFunc.mem_range`：mem_range {f : α ->ₛ β} {b} : b in f
.range ↔ b in range f
· 使用定理 `MeasureTheory.SimpleFunc.pair_preimage_singleton`：pair_preimage_singleto
n (f : α ->ₛ β) (g : α ->ₛ γ) (b : β) (c : γ) : pair f g ⁻¹' {(b, c)} = f ⁻¹' {b
} inter g ⁻¹' {c}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem setToSimpleFunc_congr' (T : Set α → E →L[ℝ] F) (h_add : FinMeasAdditive μ T) {f g : α →ₛ E}
    (hf : Integrable f μ) (hg : Integrable g μ)
    (h : Pairwise fun x y => T (f ⁻¹' {x} ∩ g ⁻¹' {y}) = 0) :
    f.setToSimpleFunc T = g.setToSimpleFunc T :=
  show ((pair f g).map Prod.fst).setToSimpleFunc T = ((pair f g).map Prod.snd).setToSimpleFunc T by
    have h_pair : Integrable (f.pair g) μ := integrable_pair hf hg
    rw [map_setToSimpleFunc T h_add h_pair Prod.fst_zero]
    rw [map_setToSimpleFunc T h_add h_pair Prod.snd_zero]
    refine Finset.sum_congr rfl fun p hp => ?_
    rcases mem_range.1 hp with ⟨a, rfl⟩
    by_cases eq : f a = g a
    · dsimp only [pair_apply]; rw [eq]
    · have : T (pair f g ⁻¹' {(f a, g a)}) = 0 := by
        have h_eq : T ((⇑(f.pair g)) ⁻¹' {(f a, g a)}) = T (f ⁻¹' {f a} ∩ g ⁻¹' {g a}) := by
          congr; rw [pair_preimage_singleton f g]
        rw [h_eq]
        exact h eq
      simp only [this, zero_apply, pair_apply]
/-
**MeasureTheory.SimpleFunc.setToSimpleFunc_congr** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.SimpleFunc`。
形式化陈述：setToSimpleFunc_congr (T : Set α -> E ->L[Real] F) (h_zero : forall s, Mea
surableSet s -> μ s = 0 -> T s = 0) (h_add : FinMeasAdditive μ T) {f g : α ->ₛ E
} (hf : Integrable f μ) (h : f =ᵐ[μ] g) : f.setToSimpleFunc T = g.setToSimpleFun
c T
参数：T : Set α -> E ->L[Real] F；h_zero : forall s, MeasurableSet s -> μ s = 0 -> T
 s = 0；h_add : FinMeasAdditive μ T；hf : Integrable f μ；h : f =ᵐ[μ] g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.SimpleFunc.setToSimpleFunc_congr'`：setToSimpleFunc_congr' 
(T : Set α -> E ->L[Real] F) (h_add : FinMeasAdditive μ T) {f g : α ->ₛ E} (hf :
 Integrable f μ) (hg : Integrable g μ…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.integrable_congr`：integrable_congr {f g : α -> ε} (h : f =
ᵐ[μ] g) : Integrable f μ ↔ Integrable g μ
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `MeasureTheory.SimpleFunc.measurableSet_fiber`：measurableSet_fiber (f : α
 ->ₛ β) (x : β) : MeasurableSet (f ⁻¹' {x})
· 使用定理 `MeasureTheory.measure_mono_null`：measure_mono_null (h : s subseteq t) (h
t : μ t = 0) : μ s = 0
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.ae_iff`：ae_iff {p : α -> Prop} : (forallᵐ a ∂μ, p a) ↔ μ {
 a | ¬p a } = 0
· 使用定理 `Filter.EventuallyEq.eq_1`：∀ {α : Type u_1} {β : Type u_2} (l : Filter α)
 (f g : α → β), (f =ᶠ[l] g) = ∀ᶠ (x : α) in l, f x = g x
-/
theorem setToSimpleFunc_congr (T : Set α → E →L[ℝ] F)
    (h_zero : ∀ s, MeasurableSet s → μ s = 0 → T s = 0) (h_add : FinMeasAdditive μ T) {f g : α →ₛ E}
    (hf : Integrable f μ) (h : f =ᵐ[μ] g) : f.setToSimpleFunc T = g.setToSimpleFunc T := by
  refine setToSimpleFunc_congr' T h_add hf ((integrable_congr h).mp hf) ?_
  refine fun x y hxy => h_zero _ ((measurableSet_fiber f x).inter (measurableSet_fiber g y)) ?_
  rw [EventuallyEq, ae_iff] at h
  refine measure_mono_null (fun z => ?_) h
  simp_rw [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
  intro h
  rwa [h.1, h.2]
/-
**MeasureTheory.SimpleFunc.setToSimpleFunc_congr_left** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.SimpleFunc`。
形式化陈述：setToSimpleFunc_congr_left (T T' : Set α -> E ->L[Real] F) (h : forall s, 
MeasurableSet s -> μ s < ∞ -> T s = T' s) (f : α ->ₛ E) (hf : Integrable f μ) : 
setToSimpleFunc T f = setToSimpleFunc T' f
参数：T T' : Set α -> E ->L[Real] F；h : forall s, MeasurableSet s -> μ s < ∞ -> T s
 = T' s；f : α ->ₛ E；hf : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.SimpleFunc.measurableSet_fiber`：measurableSet_fiber (f : α
 ->ₛ β) (x : β) : MeasurableSet (f ⁻¹' {x})
· 使用定理 `MeasureTheory.SimpleFunc.measure_preimage_lt_top_of_integrable`：measure_
preimage_lt_top_of_integrable (f : α ->ₛ E) (hf : Integrable f μ) {x : E} (hx : 
x != 0) : μ (f ⁻¹' {x}) < ∞
-/
theorem setToSimpleFunc_congr_left (T T' : Set α → E →L[ℝ] F)
    (h : ∀ s, MeasurableSet s → μ s < ∞ → T s = T' s) (f : α →ₛ E) (hf : Integrable f μ) :
    setToSimpleFunc T f = setToSimpleFunc T' f := by
  simp_rw [setToSimpleFunc]
  refine sum_congr rfl fun x _ => ?_
  by_cases hx0 : x = 0
  · simp [hx0]
  · rw [h (f ⁻¹' {x}) (SimpleFunc.measurableSet_fiber _ _)
        (SimpleFunc.measure_preimage_lt_top_of_integrable _ hf hx0)]
/-
**MeasureTheory.SimpleFunc.setToSimpleFunc_add_left** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.SimpleFunc`。
形式化陈述：setToSimpleFunc_add_left {m : MeasurableSpace α} (T T' : Set α -> F ->L[Re
al] F') {f : α ->ₛ F} : setToSimpleFunc (T + T') f = setToSimpleFunc T f + setTo
SimpleFunc T' f
参数：T T' : Set α -> F ->L[Real] F'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `FunLike.coe_add`：∀ {F : Type u_3} {α : Type u_5} {β : Type u_6} [inst : 
FunLike F α β] [inst_1 : Add F] [inst_2 : Add β]   [IsAddApply F α β] (f g : F),
 ⇑(f …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_add_distrib`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [
inst : AddCommMonoid M] {f g : ι → M},   ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑
 x ∈ s, g x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem setToSimpleFunc_add_left {m : MeasurableSpace α} (T T' : Set α → F →L[ℝ] F') {f : α →ₛ F} :
    setToSimpleFunc (T + T') f = setToSimpleFunc T f + setToSimpleFunc T' f := by
  simp_rw [setToSimpleFunc, Pi.add_apply]
  push_cast
  simp_rw [Pi.add_apply, sum_add_distrib]
/-
**MeasureTheory.SimpleFunc.setToSimpleFunc_add_left'** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.SimpleFunc`。
形式化陈述：setToSimpleFunc_add_left' (T T' T'' : Set α -> E ->L[Real] F) (h_add : for
all s, MeasurableSet s -> μ s < ∞ -> T'' s = T s + T' s) {f : α ->ₛ E} (hf : Int
egrable f μ) : setToSimpleFunc T'' f = setToSimpleFunc T f + setToSimpleFunc T' 
f
参数：T T' T'' : Set α -> E ->L[Real] F；h_add : forall s, MeasurableSet s -> μ s < 
∞ -> T'' s = T s + T' s；hf : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SimpleFunc.setToSimpleFunc_eq_sum_filter`：setToSimpleFunc_
eq_sum_filter [DecidablePred fun x => x != (0 : F)] {m : MeasurableSpace α} (T :
 Set α -> F ->L[Real] F') (f : α ->ₛ F) : se…
· 使用定理 `MeasureTheory.SimpleFunc.measurableSet_preimage`：measurableSet_preimage 
(f : α ->ₛ β) (s) : MeasurableSet (f ⁻¹' s)
· 使用定理 `MeasureTheory.SimpleFunc.measure_preimage_lt_top_of_integrable`：measure_
preimage_lt_top_of_integrable (f : α ->ₛ E) (hf : Integrable f μ) {x : E} (hx : 
x != 0) : μ (f ⁻¹' {x}) < ∞
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_add_distrib`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [
inst : AddCommMonoid M] {f g : ι → M},   ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑
 x ∈ s, g x
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `FunLike.coe_add`：∀ {F : Type u_3} {α : Type u_5} {β : Type u_6} [inst : 
FunLike F α β] [inst_1 : Add F] [inst_2 : Add β]   [IsAddApply F α β] (f g : F),
 ⇑(f …
· 使用定理 `Pi.add_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Add 
(M i)] (f g : (i : ι) → M i) (i : ι), (f + g) i = f i + g i
-/
theorem setToSimpleFunc_add_left' (T T' T'' : Set α → E →L[ℝ] F)
    (h_add : ∀ s, MeasurableSet s → μ s < ∞ → T'' s = T s + T' s) {f : α →ₛ E}
    (hf : Integrable f μ) : setToSimpleFunc T'' f = setToSimpleFunc T f + setToSimpleFunc T' f := by
  classical
  simp_rw [setToSimpleFunc_eq_sum_filter]
  suffices ∀ x ∈ {x ∈ f.range | x ≠ 0}, T'' (f ⁻¹' {x}) = T (f ⁻¹' {x}) + T' (f ⁻¹' {x}) by
    rw [← sum_add_distrib]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [this x hx]
    push_cast
    rw [Pi.add_apply]
  intro x hx
  refine
    h_add (f ⁻¹' {x}) (measurableSet_preimage _ _) (measure_preimage_lt_top_of_integrable _ hf ?_)
  rw [mem_filter] at hx
  exact hx.2
/-
**MeasureTheory.SimpleFunc.setToSimpleFunc_smul_left** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.SimpleFunc`。
形式化陈述：setToSimpleFunc_smul_left {m : MeasurableSpace α} (T : Set α -> F ->L[Real
] F') (c : Real) (f : α ->ₛ F) : setToSimpleFunc (fun s => c • T s) f = c • setT
oSimpleFunc T f
参数：T : Set α -> F ->L[Real] F'；c : Real；f : α ->ₛ F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.smul_sum`：Finset.smul_sum {f : γ -> N} {s : Finset γ} : (r • ∑ x 
in s, f x) = ∑ x in s, r • f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem setToSimpleFunc_smul_left {m : MeasurableSpace α} (T : Set α → F →L[ℝ] F') (c : ℝ)
    (f : α →ₛ F) : setToSimpleFunc (fun s => c • T s) f = c • setToSimpleFunc T f := by
  simp_rw [setToSimpleFunc, _root_.smul_apply, smul_sum]
/-
**MeasureTheory.SimpleFunc.setToSimpleFunc_smul_left'** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.SimpleFunc`。
形式化陈述：setToSimpleFunc_smul_left' (T T' : Set α -> E ->L[Real] F') (c : Real) (h_
smul : forall s, MeasurableSet s -> μ s < ∞ -> T' s = c • T s) {f : α ->ₛ E} (hf
 : Integrable f μ) : setToSimpleFunc T' f = c • setToSimpleFunc T f
参数：T T' : Set α -> E ->L[Real] F'；c : Real；h_smul : forall s, MeasurableSet s ->
 μ s < ∞ -> T' s = c • T s；hf : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SimpleFunc.setToSimpleFunc_eq_sum_filter`：setToSimpleFunc_
eq_sum_filter [DecidablePred fun x => x != (0 : F)] {m : MeasurableSpace α} (T :
 Set α -> F ->L[Real] F') (f : α ->ₛ F) : se…
· 使用定理 `MeasureTheory.SimpleFunc.measurableSet_preimage`：measurableSet_preimage 
(f : α ->ₛ β) (s) : MeasurableSet (f ⁻¹' s)
· 使用定理 `MeasureTheory.SimpleFunc.measure_preimage_lt_top_of_integrable`：measure_
preimage_lt_top_of_integrable (f : α ->ₛ E) (hf : Integrable f μ) {x : E} (hx : 
x != 0) : μ (f ⁻¹' {x}) < ∞
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `Finset.smul_sum`：Finset.smul_sum {f : γ -> N} {s : Finset γ} : (r • ∑ x 
in s, f x) = ∑ x in s, r • f x
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
-/
theorem setToSimpleFunc_smul_left' (T T' : Set α → E →L[ℝ] F') (c : ℝ)
    (h_smul : ∀ s, MeasurableSet s → μ s < ∞ → T' s = c • T s) {f : α →ₛ E} (hf : Integrable f μ) :
    setToSimpleFunc T' f = c • setToSimpleFunc T f := by
  classical
  simp_rw [setToSimpleFunc_eq_sum_filter]
  suffices ∀ x ∈ {x ∈ f.range | x ≠ 0}, T' (f ⁻¹' {x}) = c • T (f ⁻¹' {x}) by
    rw [smul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [this x hx, _root_.smul_apply]
  intro x hx
  refine
    h_smul (f ⁻¹' {x}) (measurableSet_preimage _ _) (measure_preimage_lt_top_of_integrable _ hf ?_)
  rw [mem_filter] at hx
  exact hx.2
/-
**MeasureTheory.SimpleFunc.setToSimpleFunc_add** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.SimpleFunc`。
形式化陈述：setToSimpleFunc_add (T : Set α -> E ->L[Real] F) (h_add : FinMeasAdditive 
μ T) {f g : α ->ₛ E} (hf : Integrable f μ) (hg : Integrable g μ) : setToSimpleFu
nc T (f + g) = setToSimpleFunc T f + setToSimpleFunc T g
参数：T : Set α -> E ->L[Real] F；h_add : FinMeasAdditive μ T；hf : Integrable f μ；hg
 : Integrable g μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.SimpleFunc.integrable_pair`：integrable_pair {f : α ->ₛ E} 
{g : α ->ₛ F} : Integrable f μ -> Integrable g μ -> Integrable (pair f g) μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SimpleFunc.add_eq_map₂`：∀ {α : Type u_1} {β : Type u_2} [i
nst : MeasurableSpace α] [inst_1 : Add β] (f g : MeasureTheory.SimpleFunc α β), 
  f + g = MeasureTheory.Si…
· 使用定理 `MeasureTheory.SimpleFunc.map_setToSimpleFunc`：map_setToSimpleFunc (T : S
et α -> F ->L[Real] F') (h_add : FinMeasAdditive μ T) {f : α ->ₛ G} (hf : Integr
able f μ) {g : G -> F} (hg : g 0 =…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `ContinuousLinearMap.map_add`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : S
emiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_2 :
 TopologicalSpace…
· 使用定理 `Finset.sum_add_distrib`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [
inst : AddCommMonoid M] {f g : ι → M},   ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑
 x ∈ s, g x
· 使用定理 `Prod.snd_zero`：∀ {M : Type u_3} {N : Type u_4} [inst : Zero M] [inst_1 :
 Zero N], 0.2 = 0
· 使用定理 `Prod.fst_zero`：∀ {M : Type u_3} {N : Type u_4} [inst : Zero M] [inst_1 :
 Zero N], 0.1 = 0
-/
theorem setToSimpleFunc_add (T : Set α → E →L[ℝ] F) (h_add : FinMeasAdditive μ T) {f g : α →ₛ E}
    (hf : Integrable f μ) (hg : Integrable g μ) :
    setToSimpleFunc T (f + g) = setToSimpleFunc T f + setToSimpleFunc T g :=
  have hp_pair : Integrable (f.pair g) μ := integrable_pair hf hg
  calc
    setToSimpleFunc T (f + g) = ∑ x ∈ (pair f g).range, T (pair f g ⁻¹' {x}) (x.fst + x.snd) := by
      rw [add_eq_map₂, map_setToSimpleFunc T h_add hp_pair]; simp
    _ = ∑ x ∈ (pair f g).range, (T (pair f g ⁻¹' {x}) x.fst + T (pair f g ⁻¹' {x}) x.snd) :=
      (Finset.sum_congr rfl fun _ _ => ContinuousLinearMap.map_add _ _ _)
    _ = (∑ x ∈ (pair f g).range, T (pair f g ⁻¹' {x}) x.fst) +
          ∑ x ∈ (pair f g).range, T (pair f g ⁻¹' {x}) x.snd := by
      rw [Finset.sum_add_distrib]
    _ = ((pair f g).map Prod.fst).setToSimpleFunc T +
          ((pair f g).map Prod.snd).setToSimpleFunc T := by
      rw [map_setToSimpleFunc T h_add hp_pair Prod.snd_zero,
        map_setToSimpleFunc T h_add hp_pair Prod.fst_zero]
/-
**MeasureTheory.SimpleFunc.setToSimpleFunc_neg** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.SimpleFunc`。
形式化陈述：setToSimpleFunc_neg (T : Set α -> E ->L[Real] F) (h_add : FinMeasAdditive 
μ T) {f : α ->ₛ E} (hf : Integrable f μ) : setToSimpleFunc T (-f) = -setToSimple
Func T f
参数：T : Set α -> E ->L[Real] F；h_add : FinMeasAdditive μ T；hf : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SimpleFunc.map_setToSimpleFunc`：map_setToSimpleFunc (T : S
et α -> F ->L[Real] F') (h_add : FinMeasAdditive μ T) {f : α ->ₛ G} (hf : Integr
able f μ) {g : G -> F} (hg : g 0 =…
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `MeasureTheory.SimpleFunc.setToSimpleFunc.eq_1`：∀ {α : Type u_1} {F : Typ
e u_3} {F' : Type u_4} [inst : NormedAddCommGroup F] [inst_1 : NormedSpace ℝ F] 
  [inst_2 : NormedAddCommGroup F'] …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_neg_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f : ι → G),   ∑ x ∈ s, -f x = -∑ x ∈ s, f x
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
-/
theorem setToSimpleFunc_neg (T : Set α → E →L[ℝ] F) (h_add : FinMeasAdditive μ T) {f : α →ₛ E}
    (hf : Integrable f μ) : setToSimpleFunc T (-f) = -setToSimpleFunc T f :=
  calc
    setToSimpleFunc T (-f) = setToSimpleFunc T (f.map Neg.neg) := rfl
    _ = -setToSimpleFunc T f := by
      rw [map_setToSimpleFunc T h_add hf neg_zero, setToSimpleFunc, ← sum_neg_distrib]
      exact Finset.sum_congr rfl fun x _ => map_neg _ _
/-
**MeasureTheory.SimpleFunc.setToSimpleFunc_sub** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.SimpleFunc`。
形式化陈述：setToSimpleFunc_sub (T : Set α -> E ->L[Real] F) (h_add : FinMeasAdditive 
μ T) {f g : α ->ₛ E} (hf : Integrable f μ) (hg : Integrable g μ) : setToSimpleFu
nc T (f - g) = setToSimpleFunc T f - setToSimpleFunc T g
参数：T : Set α -> E ->L[Real] F；h_add : FinMeasAdditive μ T；hf : Integrable f μ；hg
 : Integrable g μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `MeasureTheory.SimpleFunc.setToSimpleFunc_add`：setToSimpleFunc_add (T : S
et α -> E ->L[Real] F) (h_add : FinMeasAdditive μ T) {f g : α ->ₛ E} (hf : Integ
rable f μ) (hg : Integrable g μ) :…
· 使用定理 `MeasureTheory.SimpleFunc.integrable_iff`：integrable_iff {f : α ->ₛ E} : 
Integrable f μ ↔ forall y, y != 0 -> μ (f ⁻¹' {y}) < ∞
· 使用定理 `MeasureTheory.SimpleFunc.coe_neg`：∀ {α : Type u_1} {β : Type u_2} [inst 
: MeasurableSpace α] [inst_1 : Neg β] (f : MeasureTheory.SimpleFunc α β),   ⇑(-f
) = -⇑f
· 使用定理 `Pi.neg_def`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : (i : ι) → Neg (G
 i)] (f : (i : ι) → G i), -f = fun i => -f i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `Set.preimage_comp`：preimage_comp {s : Set γ} : g ∘ f ⁻¹' s = f ⁻¹' g ⁻¹'
 s
· 使用定理 `Set.neg_preimage`：∀ {α : Type u_2} [inst : Neg α] {s : Set α}, Neg.neg ⁻
¹' s = -s
· 使用定理 `Set.neg_singleton`：∀ {α : Type u_2} [inst : InvolutiveNeg α] (a : α), -{
a} = {-a}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MeasureTheory.SimpleFunc.setToSimpleFunc_neg`：setToSimpleFunc_neg (T : S
et α -> E ->L[Real] F) (h_add : FinMeasAdditive μ T) {f : α ->ₛ E} (hf : Integra
ble f μ) : setToSimpleFunc T (-f) …
-/
theorem setToSimpleFunc_sub (T : Set α → E →L[ℝ] F) (h_add : FinMeasAdditive μ T) {f g : α →ₛ E}
    (hf : Integrable f μ) (hg : Integrable g μ) :
    setToSimpleFunc T (f - g) = setToSimpleFunc T f - setToSimpleFunc T g := by
  rw [sub_eq_add_neg, setToSimpleFunc_add T h_add hf, setToSimpleFunc_neg T h_add hg,
    sub_eq_add_neg]
  rw [integrable_iff] at hg ⊢
  intro x hx_ne
  rw [SimpleFunc.coe_neg, Pi.neg_def, ← Function.comp_def, preimage_comp, neg_preimage,
    Set.neg_singleton]
  refine hg (-x) ?_
  simp [hx_ne]
/-
**MeasureTheory.SimpleFunc.setToSimpleFunc_smul_real** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.SimpleFunc`。
形式化陈述：setToSimpleFunc_smul_real (T : Set α -> E ->L[Real] F) (h_add : FinMeasAdd
itive μ T) (c : Real) {f : α ->ₛ E} (hf : Integrable f μ) : setToSimpleFunc T (c
 • f) = c • setToSimpleFunc T f
参数：T : Set α -> E ->L[Real] F；h_add : FinMeasAdditive μ T；c : Real；hf : Integrab
le f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SimpleFunc.smul_eq_map`：smul_eq_map [SMul K β] (k : K) (f 
: α ->ₛ β) : k • f = f.map (k • ·)
· 使用定理 `MeasureTheory.SimpleFunc.map_setToSimpleFunc`：map_setToSimpleFunc (T : S
et α -> F ->L[Real] F') (h_add : FinMeasAdditive μ T) {f : α ->ₛ G} (hf : Integr
able f μ) {g : G -> F} (hg : g 0 =…
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.smul_sum`：Finset.smul_sum {f : γ -> N} {s : Finset γ} : (r • ∑ x 
in s, f x) = ∑ x in s, r • f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem setToSimpleFunc_smul_real (T : Set α → E →L[ℝ] F) (h_add : FinMeasAdditive μ T) (c : ℝ)
    {f : α →ₛ E} (hf : Integrable f μ) : setToSimpleFunc T (c • f) = c • setToSimpleFunc T f :=
  calc
    setToSimpleFunc T (c • f) = ∑ x ∈ f.range, T (f ⁻¹' {x}) (c • x) := by
      rw [smul_eq_map c f, map_setToSimpleFunc T h_add hf]; rw [smul_zero]
    _ = ∑ x ∈ f.range, c • T (f ⁻¹' {x}) x :=
      (Finset.sum_congr rfl fun b _ => by rw [map_smul (T (f ⁻¹' {b})) c b])
    _ = c • setToSimpleFunc T f := by simp only [setToSimpleFunc, smul_sum]
/-
**MeasureTheory.SimpleFunc.setToSimpleFunc_smul** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.SimpleFunc`。
形式化陈述：setToSimpleFunc_smul {E} [NormedAddCommGroup E] [SMulZeroClass 𝕜 E] [Norme
dSpace Real E] [DistribSMul 𝕜 F] (T : Set α -> E ->L[Real] F) (h_add : FinMeasAd
ditive μ T) (h_smul : forall c : 𝕜, forall s x, T s (c • x) = c • T s x) (c : 𝕜)
 {f : α ->ₛ E} (hf : Integrable f μ) : setToSimpleFunc T (c • f) = c • setToSimp
leFunc T f
参数：T : Set α -> E ->L[Real] F；h_add : FinMeasAdditive μ T；h_smul : forall c : 𝕜,
 forall s x, T s (c • x) = c • T s x；c : 𝕜；hf : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SimpleFunc.smul_eq_map`：smul_eq_map [SMul K β] (k : K) (f 
: α ->ₛ β) : k • f = f.map (k • ·)
· 使用定理 `MeasureTheory.SimpleFunc.map_setToSimpleFunc`：map_setToSimpleFunc (T : S
et α -> F ->L[Real] F') (h_add : FinMeasAdditive μ T) {f : α ->ₛ G} (hf : Integr
able f μ) {g : G -> F} (hg : g 0 =…
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.smul_sum`：Finset.smul_sum {f : γ -> N} {s : Finset γ} : (r • ∑ x 
in s, f x) = ∑ x in s, r • f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem setToSimpleFunc_smul {E} [NormedAddCommGroup E] [SMulZeroClass 𝕜 E]
    [NormedSpace ℝ E] [DistribSMul 𝕜 F] (T : Set α → E →L[ℝ] F) (h_add : FinMeasAdditive μ T)
    (h_smul : ∀ c : 𝕜, ∀ s x, T s (c • x) = c • T s x) (c : 𝕜) {f : α →ₛ E} (hf : Integrable f μ) :
    setToSimpleFunc T (c • f) = c • setToSimpleFunc T f :=
  calc
    setToSimpleFunc T (c • f) = ∑ x ∈ f.range, T (f ⁻¹' {x}) (c • x) := by
      rw [smul_eq_map c f, map_setToSimpleFunc T h_add hf]; rw [smul_zero]
    _ = ∑ x ∈ f.range, c • T (f ⁻¹' {x}) x := Finset.sum_congr rfl fun b _ => by rw [h_smul]
    _ = c • setToSimpleFunc T f := by simp only [setToSimpleFunc, smul_sum]

section Order

variable {G' G'' : Type*}
  [NormedAddCommGroup G''] [PartialOrder G''] [IsOrderedAddMonoid G''] [NormedSpace ℝ G'']
  [NormedAddCommGroup G'] [PartialOrder G'] [NormedSpace ℝ G']

/-
**MeasureTheory.SimpleFunc.setToSimpleFunc_mono_left** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.SimpleFunc`。
形式化陈述：setToSimpleFunc_mono_left {m : MeasurableSpace α} (T T' : Set α -> F ->L[R
eal] G'') (hTT' : forall s x, T s x <= T' s x) (f : α ->ₛ F) : setToSimpleFunc T
 f <= setToSimpleFunc T' f
参数：T T' : Set α -> F ->L[Real] G''；hTT' : forall s x, T s x <= T' s x；f : α ->ₛ 
F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem setToSimpleFunc_mono_left {m : MeasurableSpace α} (T T' : Set α → F →L[ℝ] G'')
    (hTT' : ∀ s x, T s x ≤ T' s x) (f : α →ₛ F) : setToSimpleFunc T f ≤ setToSimpleFunc T' f := by
  simp_rw [setToSimpleFunc]; gcongr; apply hTT'
/-
**MeasureTheory.SimpleFunc.setToSimpleFunc_mono_left'** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.SimpleFunc`。
形式化陈述：setToSimpleFunc_mono_left' (T T' : Set α -> E ->L[Real] G'') (hTT' : foral
l s, MeasurableSet s -> μ s < ∞ -> forall x, T s x <= T' s x) (f : α ->ₛ E) (hf 
: Integrable f μ) : setToSimpleFunc T f <= setToSimpleFunc T' f
参数：T T' : Set α -> E ->L[Real] G''；hTT' : forall s, MeasurableSet s -> μ s < ∞ -
> forall x, T s x <= T' s x；f : α ->ₛ E；hf : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `MeasureTheory.SimpleFunc.measurableSet_fiber`：measurableSet_fiber (f : α
 ->ₛ β) (x : β) : MeasurableSet (f ⁻¹' {x})
· 使用定理 `MeasureTheory.SimpleFunc.measure_preimage_lt_top_of_integrable`：measure_
preimage_lt_top_of_integrable (f : α ->ₛ E) (hf : Integrable f μ) {x : E} (hx : 
x != 0) : μ (f ⁻¹' {x}) < ∞
-/
theorem setToSimpleFunc_mono_left' (T T' : Set α → E →L[ℝ] G'')
    (hTT' : ∀ s, MeasurableSet s → μ s < ∞ → ∀ x, T s x ≤ T' s x) (f : α →ₛ E)
    (hf : Integrable f μ) : setToSimpleFunc T f ≤ setToSimpleFunc T' f := by
  unfold setToSimpleFunc
  gcongr with i _
  by_cases h0 : i = 0
  · simp [h0]
  · exact hTT' _ (measurableSet_fiber _ _) (measure_preimage_lt_top_of_integrable _ hf h0) i
/-
**MeasureTheory.SimpleFunc.setToSimpleFunc_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.SimpleFunc`。
形式化陈述：setToSimpleFunc_nonneg {m : MeasurableSpace α} (T : Set α -> G' ->L[Real] 
G'') (hT_nonneg : forall s x, 0 <= x -> 0 <= T s x) (f : α ->ₛ G') (hf : 0 <= f)
 : 0 <= setToSimpleFunc T f
参数：T : Set α -> G' ->L[Real] G''；hT_nonneg : forall s x, 0 <= x -> 0 <= T s x；f 
: α ->ₛ G'；hf : 0 <= f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈ s
, 0 ≤ f…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_range`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} {x : α}, x ∈ Se
t.range f ↔ ∃ y, f y = x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SimpleFunc.mem_range`：mem_range {f : α ->ₛ β} {b} : b in f
.range ↔ b in range f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem setToSimpleFunc_nonneg {m : MeasurableSpace α} (T : Set α → G' →L[ℝ] G'')
    (hT_nonneg : ∀ s x, 0 ≤ x → 0 ≤ T s x) (f : α →ₛ G') (hf : 0 ≤ f) :
    0 ≤ setToSimpleFunc T f := by
  refine sum_nonneg fun i hi => hT_nonneg _ i ?_
  rw [mem_range] at hi
  obtain ⟨y, hy⟩ := Set.mem_range.mp hi
  rw [← hy]
  refine le_trans ?_ (hf y)
  simp
/-
**MeasureTheory.SimpleFunc.setToSimpleFunc_nonneg'** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.SimpleFunc`。
形式化陈述：setToSimpleFunc_nonneg' (T : Set α -> G' ->L[Real] G'') (hT_nonneg : foral
l s, MeasurableSet s -> μ s < ∞ -> forall x, 0 <= x -> 0 <= T s x) (f : α ->ₛ G'
) (hf : 0 <= f) (hfi : Integrable f μ) : 0 <= setToSimpleFunc T f
参数：T : Set α -> G' ->L[Real] G''；hT_nonneg : forall s, MeasurableSet s -> μ s < 
∞ -> forall x, 0 <= x -> 0 <= T s x；f : α ->ₛ G'；hf : 0 <= f；hfi : Integrable f 
μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈ s
, 0 ≤ f…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `MeasureTheory.SimpleFunc.measurableSet_fiber`：measurableSet_fiber (f : α
 ->ₛ β) (x : β) : MeasurableSet (f ⁻¹' {x})
· 使用定理 `MeasureTheory.SimpleFunc.measure_preimage_lt_top_of_integrable`：measure_
preimage_lt_top_of_integrable (f : α ->ₛ E) (hf : Integrable f μ) {x : E} (hx : 
x != 0) : μ (f ⁻¹' {x}) < ∞
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_range`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} {x : α}, x ∈ Se
t.range f ↔ ∃ y, f y = x
· 使用定理 `MeasureTheory.SimpleFunc.mem_range`：mem_range {f : α ->ₛ β} {b} : b in f
.range ↔ b in range f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem setToSimpleFunc_nonneg' (T : Set α → G' →L[ℝ] G'')
    (hT_nonneg : ∀ s, MeasurableSet s → μ s < ∞ → ∀ x, 0 ≤ x → 0 ≤ T s x) (f : α →ₛ G') (hf : 0 ≤ f)
    (hfi : Integrable f μ) : 0 ≤ setToSimpleFunc T f := by
  refine sum_nonneg fun i hi => ?_
  by_cases h0 : i = 0
  · simp [h0]
  refine
    hT_nonneg _ (measurableSet_fiber _ _) (measure_preimage_lt_top_of_integrable _ hfi h0) i ?_
  rw [mem_range] at hi
  obtain ⟨y, hy⟩ := Set.mem_range.mp hi
  rw [← hy]
  convert! hf y
/-
**MeasureTheory.SimpleFunc.setToSimpleFunc_mono** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.SimpleFunc`。
形式化陈述：setToSimpleFunc_mono [IsOrderedAddMonoid G'] {T : Set α -> G' ->L[Real] G'
'} (h_add : FinMeasAdditive μ T) (hT_nonneg : forall s, MeasurableSet s -> μ s <
 ∞ -> forall x, 0 <= x -> 0 <= T s x) {f g : α ->ₛ G'} (hfi : Integrable f μ) (h
gi : Integrable g μ) (hfg : f <= g) : setToSimpleFunc T f <= setToSimpleFunc T g
参数：h_add : FinMeasAdditive μ T；hT_nonneg : forall s, MeasurableSet s -> μ s < ∞ 
-> forall x, 0 <= x -> 0 <= T s x；hfi : Integrable f μ；hgi : Integrable g μ；hfg 
: f <= g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `MeasureTheory.SimpleFunc.setToSimpleFunc_sub`：setToSimpleFunc_sub (T : S
et α -> E ->L[Real] F) (h_add : FinMeasAdditive μ T) {f g : α ->ₛ E} (hf : Integ
rable f μ) (hg : Integrable g μ) :…
· 使用定理 `MeasureTheory.SimpleFunc.setToSimpleFunc_nonneg'`：setToSimpleFunc_nonneg
' (T : Set α -> G' ->L[Real] G'') (hT_nonneg : forall s, MeasurableSet s -> μ s 
< ∞ -> forall x, 0 <= x -> 0 <= T s x)…
· 使用定理 `MeasureTheory.Integrable.sub`：∀ {α : Type u_1} {β : Type u_2} {m : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f g
 : α → β}, Measure…
-/
theorem setToSimpleFunc_mono [IsOrderedAddMonoid G']
    {T : Set α → G' →L[ℝ] G''} (h_add : FinMeasAdditive μ T)
    (hT_nonneg : ∀ s, MeasurableSet s → μ s < ∞ → ∀ x, 0 ≤ x → 0 ≤ T s x) {f g : α →ₛ G'}
    (hfi : Integrable f μ) (hgi : Integrable g μ) (hfg : f ≤ g) :
    setToSimpleFunc T f ≤ setToSimpleFunc T g := by
  rw [← sub_nonneg, ← setToSimpleFunc_sub T h_add hgi hfi]
  refine setToSimpleFunc_nonneg' T hT_nonneg _ ?_ (hgi.sub hfi)
  intro x
  simp only [coe_sub, sub_nonneg, coe_zero, Pi.zero_apply, Pi.sub_apply]
  exact hfg x

end Order

/-
**MeasureTheory.SimpleFunc.norm_setToSimpleFunc_le_sum_opNorm** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory.SimpleFunc`。
形式化陈述：norm_setToSimpleFunc_le_sum_opNorm {m : MeasurableSpace α} (T : Set α -> F
' ->L[Real] F) (f : α ->ₛ F') : ‖f.setToSimpleFunc T‖ <= ∑ x in f.range, ‖T (f ⁻
¹' {x})‖ * ‖x‖
参数：T : Set α -> F' ->L[Real] F；f : α ->ₛ F'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `norm_sum_le`：norm_sum_le {E} [SeminormedAddCommGroup E] (s : Finset ι) (
f : ι -> E) : ‖∑ i in s, f i‖ <= ∑ i in s, ‖f i‖
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ContinuousLinearMap.le_opNorm`：le_opNorm : ‖f x‖ <= ‖f‖ * ‖x‖
-/
theorem norm_setToSimpleFunc_le_sum_opNorm {m : MeasurableSpace α} (T : Set α → F' →L[ℝ] F)
    (f : α →ₛ F') : ‖f.setToSimpleFunc T‖ ≤ ∑ x ∈ f.range, ‖T (f ⁻¹' {x})‖ * ‖x‖ :=
  calc
    ‖∑ x ∈ f.range, T (f ⁻¹' {x}) x‖ ≤ ∑ x ∈ f.range, ‖T (f ⁻¹' {x}) x‖ := norm_sum_le _ _
    _ ≤ ∑ x ∈ f.range, ‖T (f ⁻¹' {x})‖ * ‖x‖ := by
      gcongr with b; apply ContinuousLinearMap.le_opNorm
/-
**MeasureTheory.SimpleFunc.norm_setToSimpleFunc_le_sum_mul_norm** 是 Mathlib 中的一个
定理，位于命名空间 `MeasureTheory.SimpleFunc`。
形式化陈述：norm_setToSimpleFunc_le_sum_mul_norm (T : Set α -> F ->L[Real] F') {C : Re
al} (hT_norm : forall s, MeasurableSet s -> ‖T s‖ <= C * μ.real s) (f : α ->ₛ F)
 : ‖f.setToSimpleFunc T‖ <= C * ∑ x in f.range, μ.real (f ⁻¹' {x}) * ‖x‖
参数：T : Set α -> F ->L[Real] F'；hT_norm : forall s, MeasurableSet s -> ‖T s‖ <= C
 * μ.real s；f : α ->ₛ F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SimpleFunc.norm_setToSimpleFunc_le_sum_opNorm`：norm_setToS
impleFunc_le_sum_opNorm {m : MeasurableSpace α} (T : Set α -> F' ->L[Real] F) (f
 : α ->ₛ F') : ‖f.setToSimpleFunc T‖ <= ∑ x in f.…
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `MeasureTheory.SimpleFunc.measurableSet_fiber`：measurableSet_fiber (f : α
 ->ₛ β) (x : β) : MeasurableSet (f ⁻¹' {x})
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem norm_setToSimpleFunc_le_sum_mul_norm (T : Set α → F →L[ℝ] F') {C : ℝ}
    (hT_norm : ∀ s, MeasurableSet s → ‖T s‖ ≤ C * μ.real s) (f : α →ₛ F) :
    ‖f.setToSimpleFunc T‖ ≤ C * ∑ x ∈ f.range, μ.real (f ⁻¹' {x}) * ‖x‖ :=
  calc
    ‖f.setToSimpleFunc T‖ ≤ ∑ x ∈ f.range, ‖T (f ⁻¹' {x})‖ * ‖x‖ :=
      norm_setToSimpleFunc_le_sum_opNorm T f
    _ ≤ ∑ x ∈ f.range, C * μ.real (f ⁻¹' {x}) * ‖x‖ := by
      gcongr
      exact hT_norm _ <| SimpleFunc.measurableSet_fiber _ _
    _ ≤ C * ∑ x ∈ f.range, μ.real (f ⁻¹' {x}) * ‖x‖ := by simp_rw [mul_sum, ← mul_assoc]; rfl
/-
**MeasureTheory.SimpleFunc.norm_setToSimpleFunc_le_sum_mul_norm_of_integrable** 
是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.SimpleFunc`。
形式化陈述：norm_setToSimpleFunc_le_sum_mul_norm_of_integrable (T : Set α -> E ->L[Rea
l] F') {C : Real} (hT_norm : forall s, MeasurableSet s -> μ s < ∞ -> ‖T s‖ <= C 
* μ.real s) (f : α ->ₛ E) (hf : Integrable f μ) : ‖f.setToSimpleFunc T‖ <= C * ∑
 x in f.range, μ.real (f ⁻¹' {x}) * ‖x‖
参数：T : Set α -> E ->L[Real] F'；hT_norm : forall s, MeasurableSet s -> μ s < ∞ ->
 ‖T s‖ <= C * μ.real s；f : α ->ₛ E；hf : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SimpleFunc.norm_setToSimpleFunc_le_sum_opNorm`：norm_setToS
impleFunc_le_sum_opNorm {m : MeasurableSpace α} (T : Set α -> F' ->L[Real] F) (f
 : α ->ₛ F') : ‖f.setToSimpleFunc T‖ <= ∑ x in f.…
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `MeasureTheory.SimpleFunc.measurableSet_fiber`：measurableSet_fiber (f : α
 ->ₛ β) (x : β) : MeasurableSet (f ⁻¹' {x})
· 使用定理 `MeasureTheory.SimpleFunc.measure_preimage_lt_top_of_integrable`：measure_
preimage_lt_top_of_integrable (f : α ->ₛ E) (hf : Integrable f μ) {x : E} (hx : 
x != 0) : μ (f ⁻¹' {x}) < ∞
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem norm_setToSimpleFunc_le_sum_mul_norm_of_integrable (T : Set α → E →L[ℝ] F') {C : ℝ}
    (hT_norm : ∀ s, MeasurableSet s → μ s < ∞ → ‖T s‖ ≤ C * μ.real s) (f : α →ₛ E)
    (hf : Integrable f μ) :
    ‖f.setToSimpleFunc T‖ ≤ C * ∑ x ∈ f.range, μ.real (f ⁻¹' {x}) * ‖x‖ :=
  calc
    ‖f.setToSimpleFunc T‖ ≤ ∑ x ∈ f.range, ‖T (f ⁻¹' {x})‖ * ‖x‖ :=
      norm_setToSimpleFunc_le_sum_opNorm T f
    _ ≤ ∑ x ∈ f.range, C * μ.real (f ⁻¹' {x}) * ‖x‖ := by
      refine Finset.sum_le_sum fun b hb => ?_
      obtain rfl | hb := eq_or_ne b 0
      · simp
      gcongr
      exact hT_norm _ (SimpleFunc.measurableSet_fiber _ _) <|
        SimpleFunc.measure_preimage_lt_top_of_integrable _ hf hb
    _ ≤ C * ∑ x ∈ f.range, μ.real (f ⁻¹' {x}) * ‖x‖ := by simp_rw [mul_sum, ← mul_assoc]; rfl
/-
**MeasureTheory.SimpleFunc.setToSimpleFunc_indicator** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.SimpleFunc`。
形式化陈述：setToSimpleFunc_indicator (T : Set α -> F ->L[Real] F') (hT_empty : T ∅ = 
0) {m : MeasurableSpace α} {s : Set α} (hs : MeasurableSet s) (x : F) : SimpleFu
nc.setToSimpleFunc T (SimpleFunc.piecewise s hs (SimpleFunc.const α x) (SimpleFu
nc.const α 0)) = T s x
参数：T : Set α -> F ->L[Real] F'；hT_empty : T ∅ = 0；hs : MeasurableSet s；x : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SimpleFunc.piecewise_empty`：piecewise_empty (f g : α ->ₛ β
) : piecewise ∅ MeasurableSet.empty f g = g
· 使用定理 `MeasureTheory.SimpleFunc.setToSimpleFunc_zero_apply`：setToSimpleFunc_zer
o_apply {m : MeasurableSpace α} (T : Set α -> F ->L[Real] F') : setToSimpleFunc 
T (0 : α ->ₛ F) = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Set.Nonempty.to_type`：∀ {α : Type u} {s : Set α}, s.Nonempty → Nonempty 
α
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `MeasureTheory.SimpleFunc.piecewise_univ`：piecewise_univ (f g : α ->ₛ β) 
: piecewise univ MeasurableSet.univ f g = f
· 使用定理 `MeasureTheory.SimpleFunc.range_const`：range_const (α) [MeasurableSpace α
] [Nonempty α] (b : β) : (const α b).range = {b}
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `Set.preimage_const_of_mem`：preimage_const_of_mem {b : β} {s : Set β} (h 
: b in s) : (fun _ : α => b) ⁻¹' s = univ
· 使用定理 `MeasureTheory.SimpleFunc.range_indicator`：range_indicator {s : Set α} (h
s : MeasurableSet s) (hs_nonempty : s.Nonempty) (hs_ne_univ : s != univ) (x y : 
β) : (piecewise s hs (const α …
· 使用定理 `MeasureTheory.SimpleFunc.piecewise.congr_simp`：∀ {α : Type u_1} {β : Typ
e u_2} [inst : MeasurableSpace α] (s s_1 : Set α) (e_s : s = s_1) (hs : Measurab
leSet s)   (f f_1 : MeasureTheory.S…
· 使用定理 `Finset.insert_eq_of_mem`：insert_eq_of_mem (h : a in s) : insert a s = s
· 使用定理 `MeasureTheory.SimpleFunc.piecewise_same`：piecewise_same (f : α ->ₛ β) {s
 : Set α} (hs : MeasurableSet s) : piecewise s hs f f = f
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `Finset.mem_singleton`：mem_singleton {a b : α} : b in ({a} : Finset α) ↔ 
b = a
（共 42 条，此处仅展示前 30 条）
-/
theorem setToSimpleFunc_indicator (T : Set α → F →L[ℝ] F') (hT_empty : T ∅ = 0)
    {m : MeasurableSpace α} {s : Set α} (hs : MeasurableSet s) (x : F) :
    SimpleFunc.setToSimpleFunc T
        (SimpleFunc.piecewise s hs (SimpleFunc.const α x) (SimpleFunc.const α 0)) =
      T s x := by
  classical
  obtain rfl | hs_empty := s.eq_empty_or_nonempty
  · simp only [hT_empty, zero_apply, piecewise_empty, const_zero,
      setToSimpleFunc_zero_apply]
  simp_rw [setToSimpleFunc]
  obtain rfl | hs_univ := eq_or_ne s univ
  · have hα := hs_empty.to_type
    simp [← Function.const_def]
  rw [range_indicator hs hs_empty hs_univ]
  by_cases hx0 : x = 0
  · simp_rw [hx0]; simp
  rw [sum_insert]
  swap; · rw [Finset.mem_singleton]; exact hx0
  rw [sum_singleton, (T _).map_zero, add_zero]
  congr
  simp only [coe_piecewise, piecewise_eq_indicator, coe_const, Function.const_zero,
    piecewise_eq_indicator]
  rw [indicator_preimage, ← Function.const_def, preimage_const_of_mem]
  swap; · exact Set.mem_singleton x
  rw [← Function.const_zero, ← Function.const_def, preimage_const_of_notMem]
  swap; · rw [Set.mem_singleton_iff]; exact Ne.symm hx0
  simp
/-
**MeasureTheory.SimpleFunc.setToSimpleFunc_const'** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.SimpleFunc`。
形式化陈述：setToSimpleFunc_const' [Nonempty α] (T : Set α -> F ->L[Real] F') (x : F) 
{m : MeasurableSpace α} : SimpleFunc.setToSimpleFunc T (SimpleFunc.const α x) = 
T univ x
参数：T : Set α -> F ->L[Real] F'；x : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SimpleFunc.range_const`：range_const (α) [MeasurableSpace α
] [Nonempty α] (b : β) : (const α b).range = {b}
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `Set.preimage_const_of_mem`：preimage_const_of_mem {b : β} {s : Set β} (h 
: b in s) : (fun _ : α => b) ⁻¹' s = univ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem setToSimpleFunc_const' [Nonempty α] (T : Set α → F →L[ℝ] F') (x : F)
    {m : MeasurableSpace α} : SimpleFunc.setToSimpleFunc T (SimpleFunc.const α x) = T univ x := by
  simp only [setToSimpleFunc, range_const, Set.mem_singleton, preimage_const_of_mem,
    sum_singleton, ← Function.const_def, coe_const]
/-
**MeasureTheory.SimpleFunc.setToSimpleFunc_const** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.SimpleFunc`。
形式化陈述：setToSimpleFunc_const (T : Set α -> F ->L[Real] F') (hT_empty : T ∅ = 0) (
x : F) {m : MeasurableSpace α} : SimpleFunc.setToSimpleFunc T (SimpleFunc.const 
α x) = T univ x
参数：T : Set α -> F ->L[Real] F'；hT_empty : T ∅ = 0；x : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `MeasureTheory.SimpleFunc.range_eq_empty_of_isEmpty`：range_eq_empty_of_is
Empty {β} [hα : IsEmpty α] (f : α ->ₛ β) : f.range = ∅
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.SimpleFunc.setToSimpleFunc_const'`：setToSimpleFunc_const' 
[Nonempty α] (T : Set α -> F ->L[Real] F') (x : F) {m : MeasurableSpace α} : Sim
pleFunc.setToSimpleFunc T (SimpleFunc…
-/
theorem setToSimpleFunc_const (T : Set α → F →L[ℝ] F') (hT_empty : T ∅ = 0) (x : F)
    {m : MeasurableSpace α} : SimpleFunc.setToSimpleFunc T (SimpleFunc.const α x) = T univ x := by
  cases isEmpty_or_nonempty α
  · have h_univ_empty : (univ : Set α) = ∅ := Subsingleton.elim _ _
    rw [h_univ_empty, hT_empty]
    simp only [setToSimpleFunc, zero_apply, sum_empty,
      range_eq_empty_of_isEmpty]
  · exact setToSimpleFunc_const' T x

end SimpleFunc

end MeasureTheory

