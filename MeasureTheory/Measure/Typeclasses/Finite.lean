/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.MeasureTheory.Measure.Restrict

/-!
# Classes for finite measures

We introduce the following typeclasses for measures:

* `IsFiniteMeasure μ`: `μ univ < ∞`;
* `IsLocallyFiniteMeasure μ` : `∀ x, ∃ s ∈ 𝓝 x, μ s < ∞`.
-/

@[expose] public section

open scoped NNReal Topology
open Set MeasureTheory Measure Filter Function MeasurableSpace ENNReal

variable {α β δ ι : Type*}

namespace MeasureTheory

variable {m0 : MeasurableSpace α} [mβ : MeasurableSpace β] {μ ν ν₁ ν₂ : Measure α}
  {s t : Set α}

section IsFiniteMeasure

/-- A measure `μ` is called finite if `μ univ < ∞`. -/
@[mk_iff]
/-
**MeasureTheory.IsFiniteMeasure** 是 Mathlib 中的一个归纳类型，位于命名空间 `MeasureTheory`。
形式化陈述：{α : Type u_1} → {m0 : MeasurableSpace α} → MeasureTheory.Measure α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A measure `μ` is called finite if `μ univ < ∞`.
-/
class IsFiniteMeasure (μ : Measure α) : Prop where
  measure_univ_lt_top : μ univ < ∞
/-
**MeasureTheory.not_isFiniteMeasure_iff** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory
`。
形式化陈述：not_isFiniteMeasure_iff : ¬IsFiniteMeasure μ ↔ μ univ = ∞
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
lemma not_isFiniteMeasure_iff : ¬IsFiniteMeasure μ ↔ μ univ = ∞ := by simp [isFiniteMeasure_iff]
/-
**MeasureTheory.isFiniteMeasure_restrict** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheor
y`。
形式化陈述：isFiniteMeasure_restrict : IsFiniteMeasure (μ.restrict s) ↔ μ s != ∞
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isFiniteMeasure_restrict : IsFiniteMeasure (μ.restrict s) ↔ μ s ≠ ∞ := by
  simp [isFiniteMeasure_iff, lt_top_iff_ne_top]
/-
**MeasureTheory.Restrict.isFiniteMeasure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.Restrict`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} {s : Set α} (μ : MeasureTheory.M
easure α) [hs : Fact (μ s < ⊤)],   MeasureTheory.IsFiniteMeasure (μ.restrict s)
参数：μ : MeasureTheory.Measure α；μ s < ⊤；μ.restrict s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `Fact.elim`：Fact.elim {p : Prop} (h : Fact p) : p
-/
instance Restrict.isFiniteMeasure (μ : Measure α) [hs : Fact (μ s < ∞)] :
    IsFiniteMeasure (μ.restrict s) :=
  ⟨by simpa using hs.elim⟩

@[simp]
/-
**MeasureTheory.measure_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measure_lt_top (μ : Measure α) [IsFiniteMeasure μ] (s : Set α) : μ s < ∞
参数：μ : Measure α；s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `MeasureTheory.IsFiniteMeasure.measure_univ_lt_top`：∀ {α : Type u_1} {m0 
: MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsFinit
eMeasure μ],   μ Set.univ < ⊤
-/
theorem measure_lt_top (μ : Measure α) [IsFiniteMeasure μ] (s : Set α) : μ s < ∞ :=
  (measure_mono (subset_univ s)).trans_lt IsFiniteMeasure.measure_univ_lt_top
/-
**MeasureTheory.isFiniteMeasureRestrict** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory
`。
形式化陈述：isFiniteMeasureRestrict (μ : Measure α) (s : Set α) [h : IsFiniteMeasure μ
] : IsFiniteMeasure (μ.restrict s)
参数：μ : Measure α；s : Set α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
-/
instance isFiniteMeasureRestrict (μ : Measure α) (s : Set α) [h : IsFiniteMeasure μ] :
    IsFiniteMeasure (μ.restrict s) := ⟨by simp⟩

@[simp, aesop (rule_sets := [finiteness]) safe apply]
/-
**MeasureTheory.measure_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measure_ne_top (μ : Measure α) [IsFiniteMeasure μ] (s : Set α) : μ s != ∞
参数：μ : Measure α；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `MeasureTheory.measure_lt_top`：measure_lt_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s < ∞
-/
theorem measure_ne_top (μ : Measure α) [IsFiniteMeasure μ] (s : Set α) : μ s ≠ ∞ :=
  ne_of_lt (measure_lt_top μ s)
/-
**MeasureTheory.measure_compl_le_add_of_le_add** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：measure_compl_le_add_of_le_add [IsFiniteMeasure μ] (hs : MeasurableSet s) 
(ht : MeasurableSet t) {ε : Real>=0∞} (h : μ s <= μ t + ε) : μ tᶜ <= μ sᶜ + ε
参数：hs : MeasurableSet s；ht : MeasurableSet t；h : μ s <= μ t + ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measure_compl`：measure_compl (h₁ : MeasurableSet s) (h_fin
 : μ s != ∞) : μ sᶜ = μ univ - μ s
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `tsub_le_iff_right`：tsub_le_iff_right [LE α] [Add α] [Sub α] [OrderedSub 
α] {a b c : α} : a - b <= c ↔ a <= c + b
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `add_right_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G)
, a + b + c = a + c + b
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
-/
theorem measure_compl_le_add_of_le_add [IsFiniteMeasure μ] (hs : MeasurableSet s)
    (ht : MeasurableSet t) {ε : ℝ≥0∞} (h : μ s ≤ μ t + ε) : μ tᶜ ≤ μ sᶜ + ε := by
  rw [measure_compl ht (by finiteness), measure_compl hs (by finiteness), tsub_le_iff_right]
  calc
    μ univ = μ univ - μ s + μ s := (tsub_add_cancel_of_le <| measure_mono s.subset_univ).symm
    _ ≤ μ univ - μ s + (μ t + ε) := by gcongr
    _ = _ := by rw [add_right_comm, add_assoc]
/-
**MeasureTheory.measure_compl_le_add_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：measure_compl_le_add_iff [IsFiniteMeasure μ] (hs : MeasurableSet s) (ht : 
MeasurableSet t) {ε : Real>=0∞} : μ sᶜ <= μ tᶜ + ε ↔ μ t <= μ s + ε
参数：hs : MeasurableSet s；ht : MeasurableSet t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measure_compl_le_add_of_le_add`：measure_compl_le_add_of_le
_add [IsFiniteMeasure μ] (hs : MeasurableSet s) (ht : MeasurableSet t) {ε : Real
>=0∞} (h : μ s <= μ t + ε) : μ tᶜ …
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
-/
theorem measure_compl_le_add_iff [IsFiniteMeasure μ] (hs : MeasurableSet s) (ht : MeasurableSet t)
    {ε : ℝ≥0∞} : μ sᶜ ≤ μ tᶜ + ε ↔ μ t ≤ μ s + ε :=
  ⟨fun h => compl_compl s ▸ compl_compl t ▸ measure_compl_le_add_of_le_add hs.compl ht.compl h,
    measure_compl_le_add_of_le_add ht hs⟩
/-
**MeasureTheory.cofinite_eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：cofinite_eq_bot_iff : μ.cofinite = ⊥ ↔ IsFiniteMeasure μ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.mem_cofinite`：mem_cofinite : s in μ.cofinite ↔ μ s
ᶜ < ∞
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.compl_empty`：compl_empty : (∅ : Set α)ᶜ = univ
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem cofinite_eq_bot_iff : μ.cofinite = ⊥ ↔ IsFiniteMeasure μ := by
  simp [← empty_mem_iff_bot, μ.mem_cofinite, isFiniteMeasure_iff]

@[nontriviality, simp]
/-
**MeasureTheory.cofinite_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：cofinite_eq_bot [IsFiniteMeasure μ] : μ.cofinite = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.cofinite_eq_bot_iff`：cofinite_eq_bot_iff : μ.cofinite = ⊥ 
↔ IsFiniteMeasure μ
-/
theorem cofinite_eq_bot [IsFiniteMeasure μ] : μ.cofinite = ⊥ := cofinite_eq_bot_iff.2 ‹_›

/-- The measure of the whole space with respect to a finite measure, considered as `ℝ≥0`. -/
/-
**MeasureTheory.measureUnivNNReal** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：measureUnivNNReal (μ : Measure α) : Real>=0
参数：μ : Measure α。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The measure of the whole space with respect to a finite measure, considered as `
ℝ≥0`.
-/
def measureUnivNNReal (μ : Measure α) : ℝ≥0 :=
  (μ univ).toNNReal

@[simp]
/-
**MeasureTheory.coe_measureUnivNNReal** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：coe_measureUnivNNReal (μ : Measure α) [IsFiniteMeasure μ] : ↑(measureUnivN
NReal μ) = μ univ
参数：μ : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.coe_toNNReal`：∀ {a : ENNReal}, a ≠ ⊤ → ↑a.toNNReal = a
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
-/
theorem coe_measureUnivNNReal (μ : Measure α) [IsFiniteMeasure μ] :
    ↑(measureUnivNNReal μ) = μ univ :=
  ENNReal.coe_toNNReal (by finiteness)
/-
**MeasureTheory.isFiniteMeasureZero** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory`。
形式化陈述：isFiniteMeasureZero : IsFiniteMeasure (0 : Measure α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
instance isFiniteMeasureZero : IsFiniteMeasure (0 : Measure α) :=
  ⟨by simp⟩
/-
**MeasureTheory.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 50) isFiniteMeasureOfIsEmpty [IsEmpty α] : IsFiniteMeasure μ := by
  rw [eq_zero_of_isEmpty μ]
  infer_instance

@[simp]
/-
**MeasureTheory.measureUnivNNReal_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：measureUnivNNReal_zero : measureUnivNNReal (0 : Measure α) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem measureUnivNNReal_zero : measureUnivNNReal (0 : Measure α) = 0 :=
  rfl
/-
**MeasureTheory.isFiniteMeasureAdd** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory`。
形式化陈述：isFiniteMeasureAdd [IsFiniteMeasure μ] [IsFiniteMeasure ν] : IsFiniteMeasu
re (μ + ν) where measure_univ_lt_top
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.coe_add`：coe_add {_m : MeasurableSpace α} (μ₁ μ₂ :
 Measure α) : ⇑(μ₁ + μ₂) = μ₁ + μ₂
· 使用定理 `Pi.add_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Add 
(M i)] (f g : (i : ι) → M i) (i : ι), (f + g) i = f i + g i
· 使用定理 `ENNReal.add_lt_top`：∀ {a b : ENNReal}, a + b < ⊤ ↔ a < ⊤ ∧ b < ⊤
· 使用定理 `MeasureTheory.measure_lt_top`：measure_lt_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s < ∞
-/
instance isFiniteMeasureAdd [IsFiniteMeasure μ] [IsFiniteMeasure ν] : IsFiniteMeasure (μ + ν) where
  measure_univ_lt_top := by
    rw [Measure.coe_add, Pi.add_apply, ENNReal.add_lt_top]
    exact ⟨measure_lt_top _ _, measure_lt_top _ _⟩
/-
**MeasureTheory.isFiniteMeasureSMulNNReal** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheo
ry`。
形式化陈述：isFiniteMeasureSMulNNReal [IsFiniteMeasure μ] {r : Real>=0} : IsFiniteMeas
ure (r • μ) where measure_univ_lt_top
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `ENNReal.mul_lt_top`：mul_lt_top : a < ∞ -> b < ∞ -> a * b < ∞
· 使用定理 `ENNReal.coe_lt_top`：∀ {r : NNReal}, ↑r < ⊤
· 使用定理 `MeasureTheory.measure_lt_top`：measure_lt_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s < ∞
-/
instance isFiniteMeasureSMulNNReal [IsFiniteMeasure μ] {r : ℝ≥0} : IsFiniteMeasure (r • μ) where
  measure_univ_lt_top := ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_lt_top _ _)
/-
**MeasureTheory.IsFiniteMeasure.average** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.IsFiniteMeasure`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α},  
 MeasureTheory.IsFiniteMeasure ((μ Set.univ)⁻¹ • μ)
参数：(μ Set.univ)⁻¹ • μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.smul_apply`：smul_apply {_m : MeasurableSpace α} (c
 : R) (μ : Measure α) (s : Set α) : (c • μ) s = c • μ s
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.div_eq_inv_mul`：∀ {a b : ENNReal}, a / b = b⁻¹ * a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `ENNReal.div_self_le_one`：∀ {a : ENNReal}, a / a ≤ 1
· 使用定理 `ENNReal.one_lt_top`：1 < ⊤
-/
instance IsFiniteMeasure.average : IsFiniteMeasure ((μ univ)⁻¹ • μ) where
  measure_univ_lt_top := by
    rw [Measure.smul_apply, smul_eq_mul, ← ENNReal.div_eq_inv_mul]
    exact ENNReal.div_self_le_one.trans_lt ENNReal.one_lt_top
/-
**MeasureTheory.isFiniteMeasureSMulOfNNRealTower** 是 Mathlib 中的一个实例，位于命名空间 `Meas
ureTheory`。
形式化陈述：isFiniteMeasureSMulOfNNRealTower {R} [SMul R Real>=0] [SMul R Real>=0∞] [I
sScalarTower R Real>=0 Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] [IsFiniteMe
asure μ] {r : R} : IsFiniteMeasure (r • μ)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_one_smul`：smul_one_smul {M} (N) [Monoid N] [SMul M N] [MulAction N 
α] [SMul M α] [IsScalarTower M N α] (x : M) (y : α) : (x • (1 : N)) • y = x • y
-/
instance isFiniteMeasureSMulOfNNRealTower {R} [SMul R ℝ≥0] [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0 ℝ≥0∞]
    [IsScalarTower R ℝ≥0∞ ℝ≥0∞] [IsFiniteMeasure μ] {r : R} : IsFiniteMeasure (r • μ) := by
  rw [← smul_one_smul ℝ≥0 r μ]
  infer_instance
/-
**MeasureTheory.isFiniteMeasure_of_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：isFiniteMeasure_of_le (μ : Measure α) [IsFiniteMeasure μ] (h : ν <= μ) : I
sFiniteMeasure ν
参数：μ : Measure α；h : ν <= μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.measure_lt_top`：measure_lt_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s < ∞
-/
theorem isFiniteMeasure_of_le (μ : Measure α) [IsFiniteMeasure μ] (h : ν ≤ μ) : IsFiniteMeasure ν :=
  { measure_univ_lt_top := (h Set.univ).trans_lt (measure_lt_top _ _) }

@[instance]
/-
**MeasureTheory.Measure.isFiniteMeasure_map** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.Measure`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [mβ : MeasurableSpace β] {m : MeasurableSp
ace α} (μ : MeasureTheory.Measure α)   [MeasureTheory.IsFiniteMeasure μ] (f : α 
→ β), MeasureTheory.IsFiniteMeasure (MeasureTheory.Measure.map f μ)
参数：μ : MeasureTheory.Measure α；f : α → β；MeasureTheory.Measure.map f μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_apply_of_aemeasurable`：map_apply_of_aemeasurab
le (hf : AEMeasurable f μ) {s : Set β} (hs : MeasurableSet s) : μ.map f s = μ (f
 ⁻¹' s)
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `MeasureTheory.measure_lt_top`：measure_lt_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s < ∞
· 使用定理 `MeasureTheory.Measure.map_of_not_aemeasurable`：map_of_not_aemeasurable {
f : α -> β} {μ : Measure α} (hf : ¬AEMeasurable f μ) : μ.map f = 0
-/
theorem Measure.isFiniteMeasure_map {m : MeasurableSpace α} (μ : Measure α) [IsFiniteMeasure μ]
    (f : α → β) : IsFiniteMeasure (μ.map f) := by
  by_cases hf : AEMeasurable f μ
  · constructor
    rw [map_apply_of_aemeasurable hf MeasurableSet.univ]
    exact measure_lt_top μ _
  · rw [map_of_not_aemeasurable hf]
    exact MeasureTheory.isFiniteMeasureZero
/-
**MeasureTheory.Measure.isFiniteMeasure_of_map** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.Measure`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m0 : MeasurableSpace α} [mβ : MeasurableS
pace β] {μ : MeasureTheory.Measure α}   {f : α → β},   AEMeasurable f μ → ∀ [Mea
sureTheory.IsFiniteMeasure (MeasureTheory.Measure.map f μ)], MeasureTheory.IsFin
iteMeasure μ
参数：MeasureTheory.Measure.map f μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.preimage_univ`：preimage_univ : f ⁻¹' univ = univ
· 使用定理 `MeasureTheory.Measure.map_apply_of_aemeasurable`：map_apply_of_aemeasurab
le (hf : AEMeasurable f μ) {s : Set β} (hs : MeasurableSet s) : μ.map f s = μ (f
 ⁻¹' s)
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `MeasureTheory.IsFiniteMeasure.measure_univ_lt_top`：∀ {α : Type u_1} {m0 
: MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsFinit
eMeasure μ],   μ Set.univ < ⊤
-/
theorem Measure.isFiniteMeasure_of_map {μ : Measure α} {f : α → β}
    (hf : AEMeasurable f μ) [IsFiniteMeasure (μ.map f)] : IsFiniteMeasure μ where
  measure_univ_lt_top := by
    rw [← Set.preimage_univ (f := f), ← map_apply_of_aemeasurable hf .univ]
    exact IsFiniteMeasure.measure_univ_lt_top
/-
**MeasureTheory.Measure.isFiniteMeasure_map_iff** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.Measure`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m0 : MeasurableSpace α} [mβ : MeasurableS
pace β] {μ : MeasureTheory.Measure α}   {f : α → β},   AEMeasurable f μ → (Measu
reTheory.IsFiniteMeasure (MeasureTheory.Measure.map f μ) ↔ MeasureTheory.IsFinit
eMeasure μ)
参数：MeasureTheory.IsFiniteMeasure (MeasureTheory.Measure.map f μ) ↔ MeasureTheory
.IsFiniteMeasure μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.isFiniteMeasure_of_map`：∀ {α : Type u_1} {β : Type
 u_2} {m0 : MeasurableSpace α} [mβ : MeasurableSpace β] {μ : MeasureTheory.Measu
re α}   {f : α → β},   AEMeasurabl…
· 使用定理 `MeasureTheory.Measure.isFiniteMeasure_map`：∀ {α : Type u_1} {β : Type u_
2} [mβ : MeasurableSpace β] {m : MeasurableSpace α} (μ : MeasureTheory.Measure α
)   [MeasureTheory.IsFiniteMeas…
-/
theorem Measure.isFiniteMeasure_map_iff {μ : Measure α} {f : α → β}
    (hf : AEMeasurable f μ) : IsFiniteMeasure (μ.map f) ↔ IsFiniteMeasure μ :=
  ⟨fun _ ↦ isFiniteMeasure_of_map hf, fun _ ↦ isFiniteMeasure_map μ f⟩
/-
**MeasureTheory.IsFiniteMeasure_comap** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory`。
形式化陈述：IsFiniteMeasure_comap (f : β -> α) [IsFiniteMeasure μ] : IsFiniteMeasure (
μ.comap f) where measure_univ_lt_top
参数：f : β -> α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.Measure.comap_apply_le`：comap_apply_le (f : α -> β) (μ : M
easure β) (hs : NullMeasurableSet s (μ.comap f)) : μ.comap f s <= μ (f '' s)
· 使用定理 `MeasureTheory.nullMeasurableSet_univ`：nullMeasurableSet_univ : NullMeasu
rableSet univ μ
· 使用定理 `MeasureTheory.measure_lt_top`：measure_lt_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s < ∞
-/
instance IsFiniteMeasure_comap (f : β → α) [IsFiniteMeasure μ] : IsFiniteMeasure (μ.comap f) where
  measure_univ_lt_top :=
    (Measure.comap_apply_le _ _ nullMeasurableSet_univ).trans_lt (measure_lt_top _ _)

@[simp]
/-
**MeasureTheory.measureUnivNNReal_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：measureUnivNNReal_eq_zero [IsFiniteMeasure μ] : measureUnivNNReal μ = 0 ↔ 
μ = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.measure_univ_eq_zero`：measure_univ_eq_zero : μ uni
v = 0 ↔ μ = 0
· 使用定理 `MeasureTheory.coe_measureUnivNNReal`：coe_measureUnivNNReal (μ : Measure 
α) [IsFiniteMeasure μ] : ↑(measureUnivNNReal μ) = μ univ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem measureUnivNNReal_eq_zero [IsFiniteMeasure μ] : measureUnivNNReal μ = 0 ↔ μ = 0 := by
  rw [← MeasureTheory.Measure.measure_univ_eq_zero, ← coe_measureUnivNNReal]
  norm_cast
/-
**MeasureTheory.measureUnivNNReal_pos** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measureUnivNNReal_pos [IsFiniteMeasure μ] (hμ : μ != 0) : 0 < measureUnivN
NReal μ
参数：hμ : μ != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
-/
theorem measureUnivNNReal_pos [IsFiniteMeasure μ] (hμ : μ ≠ 0) : 0 < measureUnivNNReal μ := by
  contrapose! hμ
  simpa [measureUnivNNReal_eq_zero, Nat.le_zero] using hμ

/-- `le_of_add_le_add_left` is normally applicable to ordered cancellative monoids,
but it holds for measures with the additional assumption that μ is finite. -/
/-
**MeasureTheory.Measure.le_of_add_le_add_left** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.Measure`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} {μ ν₁ ν₂ : MeasureTheory.Measure
 α} [MeasureTheory.IsFiniteMeasure μ],   μ + ν₁ ≤ μ + ν₂ → ν₁ ≤ ν₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.le_of_add_le_add_left`：∀ {a b c : ENNReal}, a ≠ ⊤ → a + b ≤ a + 
c → b ≤ c
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞

--- 原说明 ---
`le_of_add_le_add_left` is normally applicable to ordered cancellative monoids,
but it holds for measures with the additional assumption that μ is finite.
-/
theorem Measure.le_of_add_le_add_left [IsFiniteMeasure μ] (A2 : μ + ν₁ ≤ μ + ν₂) : ν₁ ≤ ν₂ :=
  fun S => ENNReal.le_of_add_le_add_left (MeasureTheory.measure_ne_top μ S) (A2 S)
/-
**MeasureTheory.Measure.eq_of_le_of_measure_univ_eq** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.Measure`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} 
[MeasureTheory.IsFiniteMeasure μ],   μ ≤ ν → μ Set.univ = ν Set.univ → μ = ν
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `MeasureTheory.Measure.le_intro`：le_intro (h : forall s, MeasurableSet s 
-> s.Nonempty -> μ₁ s <= μ₂ s) : μ₁ <= μ₂
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.disjoint_compl_right_iff_subset`：disjoint_compl_right_iff_subset : D
isjoint s tᶜ ↔ s subseteq t
· 使用定理 `subset_rfl`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorde
r α] {a : α}, a ⊆ a
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `ENNReal.add_lt_add_of_lt_of_le`：∀ {a b c d : ENNReal}, c ≠ ⊤ → a < b → c
 ≤ d → a + c < b + d
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measure_union`：measure_union (hd : Disjoint s₁ s₂) (h : Me
asurableSet s₂) : μ (s₁ union s₂) = μ s₁ + μ s₂
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `Set.union_compl_self`：union_compl_self (s : Set α) : s union sᶜ = univ
-/
lemma Measure.eq_of_le_of_measure_univ_eq [IsFiniteMeasure μ]
    (hμν : μ ≤ ν) (h_univ : μ univ = ν univ) : μ = ν := by
  refine le_antisymm hμν (le_intro fun s hs _ ↦ ?_)
  by_contra! h_lt
  have h_disj : Disjoint s sᶜ := disjoint_compl_right_iff_subset.mpr subset_rfl
  rw [← union_compl_self s, measure_union h_disj hs.compl, measure_union h_disj hs.compl] at h_univ
  exact ENNReal.add_lt_add_of_lt_of_le (by finiteness) h_lt (hμν sᶜ) |>.not_ge h_univ.symm.le
/-
**MeasureTheory.summable_measure_toReal** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：summable_measure_toReal [hμ : IsFiniteMeasure μ] {f : Nat -> Set α} (hf₁ :
 forall i : Nat, MeasurableSet (f i)) (hf₂ : Pairwise (Disjoint on f)) : Summabl
e fun x => μ.real (f x)
参数：hf₁ : forall i : Nat, MeasurableSet (f i)；hf₂ : Pairwise (Disjoint on f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.summable_toReal`：summable_toReal {f : α -> Real>=0∞} (hsum : ∑' 
x, f x != ∞) : Summable fun x => (f x).toReal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.measure_iUnion`：measure_iUnion {m0 : MeasurableSpace α} {μ
 : Measure α} [Countable ι] {f : ι -> Set α} (hn : Pairwise (Disjoint on f)) (h 
: forall i, Measur…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `MeasureTheory.measure_lt_top`：measure_lt_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s < ∞
-/
theorem summable_measure_toReal [hμ : IsFiniteMeasure μ] {f : ℕ → Set α}
    (hf₁ : ∀ i : ℕ, MeasurableSet (f i)) (hf₂ : Pairwise (Disjoint on f)) :
    Summable fun x => μ.real (f x) := by
  apply ENNReal.summable_toReal
  rw [← MeasureTheory.measure_iUnion hf₂ hf₁]
  exact ne_of_lt (measure_lt_top _ _)
/-
**MeasureTheory.ae_eq_univ_iff_measure_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：ae_eq_univ_iff_measure_eq [IsFiniteMeasure μ] (hs : NullMeasurableSet s μ)
 : s =ᵐ[μ] univ ↔ μ s = μ univ
参数：hs : NullMeasurableSet s μ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.measure_congr`：measure_congr (H : s =ᵐ[μ] t) : μ s = μ t
· 使用定理 `MeasureTheory.ae_eq_of_subset_of_measure_ge`：ae_eq_of_subset_of_measure_
ge (h₁ : s subseteq t) (h₂ : μ t <= μ s) (hsm : NullMeasurableSet s μ) (ht : μ t
 != ∞) : s =ᵐ[μ] t
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
-/
theorem ae_eq_univ_iff_measure_eq [IsFiniteMeasure μ] (hs : NullMeasurableSet s μ) :
    s =ᵐ[μ] univ ↔ μ s = μ univ :=
  ⟨measure_congr, fun h ↦ ae_eq_of_subset_of_measure_ge (subset_univ _) h.ge hs (by finiteness)⟩
/-
**MeasureTheory.ae_iff_measure_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_iff_measure_eq [IsFiniteMeasure μ] {p : α -> Prop} (hp : NullMeasurable
Set { a | p a } μ) : (forallᵐ a ∂μ, p a) ↔ μ { a | p a } = μ univ
参数：hp : NullMeasurableSet { a | p a } μ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.ae_eq_univ_iff_measure_eq`：ae_eq_univ_iff_measure_eq [IsFi
niteMeasure μ] (hs : NullMeasurableSet s μ) : s =ᵐ[μ] univ ↔ μ s = μ univ
· 使用定理 `Filter.eventuallyEq_univ`：eventuallyEq_univ {s : Set α} {l : Filter α} :
 s =ᶠ[l] univ ↔ s in l
· 使用定理 `Filter.eventually_iff`：eventually_iff {f : Filter α} {P : α -> Prop} : (
forallᶠ x in f, P x) ↔ { x | P x } in f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ae_iff_measure_eq [IsFiniteMeasure μ] {p : α → Prop}
    (hp : NullMeasurableSet { a | p a } μ) : (∀ᵐ a ∂μ, p a) ↔ μ { a | p a } = μ univ := by
  rw [← ae_eq_univ_iff_measure_eq hp, eventuallyEq_univ, eventually_iff]
/-
**MeasureTheory.ae_mem_iff_measure_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_mem_iff_measure_eq [IsFiniteMeasure μ] {s : Set α} (hs : NullMeasurable
Set s μ) : (forallᵐ a ∂μ, a in s) ↔ μ s = μ univ
参数：hs : NullMeasurableSet s μ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.ae_iff_measure_eq`：ae_iff_measure_eq [IsFiniteMeasure μ] {
p : α -> Prop} (hp : NullMeasurableSet { a | p a } μ) : (forallᵐ a ∂μ, p a) ↔ μ 
{ a | p a } = μ univ
-/
theorem ae_mem_iff_measure_eq [IsFiniteMeasure μ] {s : Set α} (hs : NullMeasurableSet s μ) :
    (∀ᵐ a ∂μ, a ∈ s) ↔ μ s = μ univ :=
  ae_iff_measure_eq hs
/-
**MeasureTheory.tendsto_measure_biUnion_Ici_zero_of_pairwise_disjoint** 是 Mathli
b 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：tendsto_measure_biUnion_Ici_zero_of_pairwise_disjoint {X : Type*} [Measura
bleSpace X] {μ : Measure X} [IsFiniteMeasure μ] {Es : Nat -> Set X} (Es_mble : f
orall i, NullMeasurableSet (Es i) μ) (Es_disj : Pairwise fun n m => Disjoint (Es
 n) (Es m)) : Tendsto (μ ∘ fun n => ⋃ i >= n, Es i) atTop (𝓝 0)
参数：Es_mble : forall i, NullMeasurableSet (Es i) μ；Es_disj : Pairwise fun n m => 
Disjoint (Es n) (Es m)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.biUnion_mono`：biUnion_mono {s s' : Set α} {t t' : α -> Set β} (hs : 
s' subseteq s) (h : forall x in s, t x subseteq t' x) : ⋃ x in s', t x subseteq 
⋃ x in…
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `subset_rfl`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorde
r α] {a : α}, a ⊆ a
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Disjoint.ne_of_mem`：∀ {α : Type u} {s t : Set α}, Disjoint s t → ∀ ⦃a : 
α⦄, a ∈ s → ∀ ⦃b : α⦄, b ∈ t → a ≠ b
· 使用定理 `Nat.ne_of_lt`：∀ {a b : ℕ}, a < b → a ≠ b
· 使用定理 `Set.empty_subset`：empty_subset (s : Set α) : ∅ subseteq s
· 使用定理 `MeasureTheory.tendsto_measure_iInter_atTop`：tendsto_measure_iInter_atTop
 [Preorder ι] [IsCountablyGenerated (atTop : Filter ι)] {s : ι -> Set α} (hs : f
orall i, NullMeasurableSet (s i)…
· 使用定理 `instDiscreteTopologyNat`：DiscreteTopology ℕ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `TopologicalSpace.instSecondCountableTopologyOfLindelofSpaceOfPseudoMetri
zableSpace`：∀ (X : Type u_5) [inst : TopologicalSpace X] [LindelofSpace X] [Topo
logicalSpace.PseudoMetrizableSpace X],   SecondCountableTopology X
· 使用定理 `Countable.LindelofSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Cou
ntable X], LindelofSpace X
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `MeasureTheory.NullMeasurableSet.iUnion`：∀ {α : Type u_2} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} {ι : Sort u_5} [Countable ι] {s : ι → Se
t α},   (∀ (i : ι), MeasureT…
· 使用定理 `Prop.countable`：∀ (p : Prop), Countable p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
lemma tendsto_measure_biUnion_Ici_zero_of_pairwise_disjoint
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {Es : ℕ → Set X} (Es_mble : ∀ i, NullMeasurableSet (Es i) μ)
    (Es_disj : Pairwise fun n m ↦ Disjoint (Es n) (Es m)) :
    Tendsto (μ ∘ fun n ↦ ⋃ i ≥ n, Es i) atTop (𝓝 0) := by
  have decr : Antitone fun n ↦ ⋃ i ≥ n, Es i :=
    fun n m hnm ↦ biUnion_mono (fun _ hi ↦ le_trans hnm hi) (fun _ _ ↦ subset_rfl)
  have nothing : ⋂ n, ⋃ i ≥ n, Es i = ∅ := by
    apply subset_antisymm _ (empty_subset _)
    intro x hx
    simp only [mem_iInter, mem_iUnion, exists_prop] at hx
    obtain ⟨j, _, x_in_Es_j⟩ := hx 0
    obtain ⟨k, k_gt_j, x_in_Es_k⟩ := hx (j + 1)
    have oops := (Es_disj (Nat.ne_of_lt k_gt_j)).ne_of_mem x_in_Es_j x_in_Es_k
    contradiction
  have key := tendsto_measure_iInter_atTop (μ := μ) (fun n ↦ by measurability)
    decr ⟨0, measure_ne_top _ _⟩
  simp only [nothing, measure_empty] at key
  convert! key

open scoped symmDiff
/-
**MeasureTheory.abs_measureReal_sub_le_measureReal_symmDiff'** 是 Mathlib 中的一个定理，
位于命名空间 `MeasureTheory`。
形式化陈述：abs_measureReal_sub_le_measureReal_symmDiff' (hs : NullMeasurableSet s μ) 
(ht : NullMeasurableSet t μ) (hs' : μ s != ∞) (ht' : μ t != ∞) : |μ.real s - μ.r
eal t| <= μ.real (s ∆ t)
参数：hs : NullMeasurableSet s μ；ht : NullMeasurableSet t μ；hs' : μ s != ∞；ht' : μ 
t != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `MeasureTheory.measure_lt_top_of_subset`：measure_lt_top_of_subset (hst : 
t subseteq s) (hs : μ s != ∞) : μ t < ∞
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measure_sdiff'`：measure_sdiff' (s : Set α) (hm : NullMeasu
rableSet t μ) (h_fin : μ t != ∞) : μ (s \ t) = μ (s union t) - μ t
· 使用引理 `ENNReal.toReal_sub_of_le`：toReal_sub_of_le (hba : b <= a) (ha : a != ∞) 
: (a - b).toReal = a.toReal - b.toReal
· 使用定理 `MeasureTheory.measure_le_measure_union_right`：measure_le_measure_union_r
ight : μ t <= μ (s union t)
· 使用定理 `MeasureTheory.measure_union_ne_top`：measure_union_ne_top (hs : μ s != ∞)
 (ht : μ t != ∞) : μ (s union t) != ∞
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
· 使用定理 `_private.Mathlib.MeasureTheory.Measure.Typeclasses.Finite.0.MeasureTheor
y.abs_measureReal_sub_le_measureReal_symmDiff'._abel_1_4`：∀ {α : Type u_1} {m0 :
 MeasurableSpace α} {μ : MeasureTheory.Measure α} {s t : Set α},   (μ s).toReal 
- (μ t).toReal = (μ (s ∪ t)).toReal - …
· 使用引理 `MeasureTheory.measure_symmDiff_eq`：measure_symmDiff_eq (hs : NullMeasura
bleSet s μ) (ht : NullMeasurableSet t μ) : μ (s ∆ t) = μ (s \ t) + μ (t \ s)
· 使用定理 `ENNReal.toReal_add`：toReal_add (ha : a != ∞) (hb : b != ∞) : (a + b).toR
eal = a.toReal + b.toReal
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ENNReal.abs_toReal`：abs_toReal {x : Real>=0∞} : |x.toReal| = x.toReal
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `abs_sub`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOrder 
G] [IsOrderedAddMonoid G] (a b : G), |a - b| ≤ |a| + |b|
-/
theorem abs_measureReal_sub_le_measureReal_symmDiff'
    (hs : NullMeasurableSet s μ) (ht : NullMeasurableSet t μ) (hs' : μ s ≠ ∞) (ht' : μ t ≠ ∞) :
    |μ.real s - μ.real t| ≤ μ.real (s ∆ t) := by
  simp only [Measure.real]
  have hst : μ (s \ t) ≠ ∞ := (measure_lt_top_of_subset sdiff_subset hs').ne
  have hts : μ (t \ s) ≠ ∞ := (measure_lt_top_of_subset sdiff_subset ht').ne
  suffices (μ s).toReal - (μ t).toReal = (μ (s \ t)).toReal - (μ (t \ s)).toReal by
    rw [this, measure_symmDiff_eq hs ht, ENNReal.toReal_add hst hts]
    convert! abs_sub (μ (s \ t)).toReal (μ (t \ s)).toReal <;> simp
  rw [measure_sdiff' s ht ht', measure_sdiff' t hs hs',
    ENNReal.toReal_sub_of_le measure_le_measure_union_right (by finiteness),
    ENNReal.toReal_sub_of_le measure_le_measure_union_right (by finiteness),
    union_comm t s]
  abel
/-
**MeasureTheory.abs_measureReal_sub_le_measureReal_symmDiff** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory`。
形式化陈述：abs_measureReal_sub_le_measureReal_symmDiff [IsFiniteMeasure μ] (hs : Null
MeasurableSet s μ) (ht : NullMeasurableSet t μ) : |μ.real s - μ.real t| <= μ.rea
l (s ∆ t)
参数：hs : NullMeasurableSet s μ；ht : NullMeasurableSet t μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.abs_measureReal_sub_le_measureReal_symmDiff'`：abs_measureR
eal_sub_le_measureReal_symmDiff' (hs : NullMeasurableSet s μ) (ht : NullMeasurab
leSet t μ) (hs' : μ s != ∞) (ht' : μ t != ∞) : |…
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
-/
theorem abs_measureReal_sub_le_measureReal_symmDiff [IsFiniteMeasure μ]
    (hs : NullMeasurableSet s μ) (ht : NullMeasurableSet t μ) :
    |μ.real s - μ.real t| ≤ μ.real (s ∆ t) :=
  abs_measureReal_sub_le_measureReal_symmDiff' hs ht (by finiteness) (by finiteness)
/-
**MeasureTheory.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {s : Finset ι} {μ : ι → Measure α} [∀ i, IsFiniteMeasure (μ i)] :
    IsFiniteMeasure (∑ i ∈ s, μ i) where measure_univ_lt_top := by simp [measure_lt_top]
/-
**MeasureTheory.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Finite ι] {μ : ι → Measure α} [∀ i, IsFiniteMeasure (μ i)] :
    IsFiniteMeasure (.sum μ) where
  measure_univ_lt_top := by
    cases nonempty_fintype ι
    simp [measure_lt_top]

end IsFiniteMeasure

/-
**MeasureTheory.ite_ae_eq_of_measure_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：ite_ae_eq_of_measure_zero {γ} (f : α -> γ) (g : α -> γ) (s : Set α) [Decid
ablePred (· in s)] (hs_zero : μ s = 0) : (fun x => ite (x in s) (f x) (g x)) =ᵐ[
μ] g
参数：f : α -> γ；g : α -> γ；s : Set α；· in s；hs_zero : μ s = 0。
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
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_compl_iff`：mem_compl_iff (s : Set α) (x : α) : x in sᶜ ↔ x ∉ s
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `MeasureTheory.measure_mono_null`：measure_mono_null (h : s subseteq t) (h
t : μ t = 0) : μ s = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `Set.compl_subset_compl`：compl_subset_compl : sᶜ subseteq tᶜ ↔ t subseteq
 s
-/
theorem ite_ae_eq_of_measure_zero {γ} (f : α → γ) (g : α → γ) (s : Set α) [DecidablePred (· ∈ s)]
    (hs_zero : μ s = 0) :
    (fun x => ite (x ∈ s) (f x) (g x)) =ᵐ[μ] g := by
  have h_ss : sᶜ ⊆ { a : α | ite (a ∈ s) (f a) (g a) = g a } := fun x hx => by
    simp [(Set.mem_compl_iff _ _).mp hx]
  refine measure_mono_null ?_ hs_zero
  conv_rhs => rw [← compl_compl s]
  rwa [Set.compl_subset_compl]
/-
**MeasureTheory.ite_ae_eq_of_measure_compl_zero** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
形式化陈述：ite_ae_eq_of_measure_compl_zero {γ} (f : α -> γ) (g : α -> γ) (s : Set α) 
[DecidablePred (· in s)] (hs_zero : μ sᶜ = 0) : (fun x => ite (x in s) (f x) (g 
x)) =ᵐ[μ] f
参数：f : α -> γ；g : α -> γ；s : Set α；· in s；hs_zero : μ sᶜ = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.mem_ae_iff`：mem_ae_iff {s : Set α} : s in ae μ ↔ μ sᶜ = 0
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem ite_ae_eq_of_measure_compl_zero {γ} (f : α → γ) (g : α → γ)
    (s : Set α) [DecidablePred (· ∈ s)] (hs_zero : μ sᶜ = 0) :
    (fun x => ite (x ∈ s) (f x) (g x)) =ᵐ[μ] f := by
  rw [← mem_ae_iff] at hs_zero
  filter_upwards [hs_zero]
  intros
  split_ifs
  rfl

namespace Measure

/-- A measure is called finite at filter `f` if it is finite at some set `s ∈ f`.
Equivalently, it is eventually finite at `s` in `f.small_sets`. -/
/-
**MeasureTheory.Measure.FiniteAtFilter** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.
Measure`。
形式化陈述：FiniteAtFilter {_m0 : MeasurableSpace α} (μ : Measure α) (f : Filter α) : 
Prop
参数：μ : Measure α；f : Filter α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A measure is called finite at filter `f` if it is finite at some set `s ∈ f`.
Equivalently, it is eventually finite at `s` in `f.small_sets`.
-/
def FiniteAtFilter {_m0 : MeasurableSpace α} (μ : Measure α) (f : Filter α) : Prop :=
  ∃ s ∈ f, μ s < ∞
/-
**MeasureTheory.Measure.finiteAtFilter_of_finite** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.Measure`。
形式化陈述：finiteAtFilter_of_finite {_m0 : MeasurableSpace α} (μ : Measure α) [IsFini
teMeasure μ] (f : Filter α) : μ.FiniteAtFilter f
参数：μ : Measure α；f : Filter α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
· 使用定理 `MeasureTheory.measure_lt_top`：measure_lt_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s < ∞
-/
theorem finiteAtFilter_of_finite {_m0 : MeasurableSpace α} (μ : Measure α) [IsFiniteMeasure μ]
    (f : Filter α) : μ.FiniteAtFilter f :=
  ⟨univ, univ_mem, measure_lt_top μ univ⟩
/-
**MeasureTheory.Measure.FiniteAtFilter.exists_mem_basis** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory.Measure.FiniteAtFilter`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_4} {m0 : MeasurableSpace α} {μ : MeasureTheor
y.Measure α} {f : Filter α},   μ.FiniteAtFilter f → ∀ {p : ι → Prop} {s : ι → Se
t α}, f.HasBasis p s → ∃ i, p i ∧ μ (s i) < ⊤
参数：s i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.exists_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ {P : Set α → Prop}, (∀ ⦃
s t : Set α⦄, s …
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
theorem FiniteAtFilter.exists_mem_basis {f : Filter α} (hμ : FiniteAtFilter μ f) {p : ι → Prop}
    {s : ι → Set α} (hf : f.HasBasis p s) : ∃ i, p i ∧ μ (s i) < ∞ :=
  (hf.exists_iff fun {_s _t} hst ht => (measure_mono hst).trans_lt ht).1 hμ
/-
**MeasureTheory.Measure.finiteAtBot** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Mea
sure`。
形式化陈述：finiteAtBot {m0 : MeasurableSpace α} (μ : Measure α) : μ.FiniteAtFilter ⊥
参数：μ : Measure α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_bot`：mem_bot {s : Set α} : s in (⊥ : Filter α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
theorem finiteAtBot {m0 : MeasurableSpace α} (μ : Measure α) : μ.FiniteAtFilter ⊥ :=
  ⟨∅, mem_bot, by simp only [measure_empty, zero_lt_top]⟩

/-- `μ` has finite spanning sets in `C` if there is a countable sequence of sets in `C` that have
  finite measures. This structure is a type, which is useful if we want to record extra properties
  about the sets, such as that they are monotone.
  `SigmaFinite` is defined in terms of this: `μ` is σ-finite if there exists a sequence of
  finite spanning sets in the collection of all measurable sets. -/
/-
**MeasureTheory.Measure.FiniteSpanningSetsIn** 是 Mathlib 中的一个归纳类型，位于命名空间 `Measur
eTheory.Measure`。
形式化陈述：{α : Type u_1} → {m0 : MeasurableSpace α} → MeasureTheory.Measure α → Set 
(Set α) → Type u_1
参数：Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`μ` has finite spanning sets in `C` if there is a countable sequence of sets in 
`C` that have
  finite measures. This structure is a type, which is useful if we want to recor
d extra properties
  about the sets, such as that they are monotone.
  `SigmaFinite` is defined in terms of this: `μ` is σ-finite if there exists a s
equence of
  finite spanning sets in the collection of all measurable sets.
-/
structure FiniteSpanningSetsIn {m0 : MeasurableSpace α} (μ : Measure α) (C : Set (Set α)) where
  /-- The sequence of sets in `C` with finite measures -/
  protected set : ℕ → Set α
  protected set_mem : ∀ i, set i ∈ C
  protected finite : ∀ i, μ (set i) < ∞
  protected spanning : ⋃ i, set i = univ

end Measure

/-- A measure is called locally finite if it is finite in some neighborhood of each point. -/
/-
**MeasureTheory.IsLocallyFiniteMeasure** 是 Mathlib 中的一个归纳类型，位于命名空间 `MeasureTheor
y`。
形式化陈述：{α : Type u_1} → {m0 : MeasurableSpace α} → [TopologicalSpace α] → Measure
Theory.Measure α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A measure is called locally finite if it is finite in some neighborhood of each 
point.
-/
class IsLocallyFiniteMeasure [TopologicalSpace α] (μ : Measure α) : Prop where
  finiteAtNhds : ∀ x, μ.FiniteAtFilter (𝓝 x)

-- see Note [lower instance priority]
/-
**MeasureTheory.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) IsFiniteMeasure.toIsLocallyFiniteMeasure [TopologicalSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] : IsLocallyFiniteMeasure μ :=
  ⟨fun _ => finiteAtFilter_of_finite _ _⟩
/-
**MeasureTheory.Measure.finiteAt_nhds** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.M
easure`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} [inst : TopologicalSpace α] (μ :
 MeasureTheory.Measure α)   [MeasureTheory.IsLocallyFiniteMeasure μ] (x : α), μ.
FiniteAtFilter (nhds x)
参数：μ : MeasureTheory.Measure α；x : α；nhds x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsLocallyFiniteMeasure.finiteAtNhds`：∀ {α : Type u_1} {m0 
: MeasurableSpace α} {inst : TopologicalSpace α} {μ : MeasureTheory.Measure α}  
 [self : MeasureTheory.IsLocallyFiniteM…
-/
theorem Measure.finiteAt_nhds [TopologicalSpace α] (μ : Measure α) [IsLocallyFiniteMeasure μ]
    (x : α) : μ.FiniteAtFilter (𝓝 x) :=
  IsLocallyFiniteMeasure.finiteAtNhds x
/-
**MeasureTheory.Measure.smul_finite** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Mea
sure`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [M
easureTheory.IsFiniteMeasure μ] {c : ENNReal},   c ≠ ⊤ → MeasureTheory.IsFiniteM
easure (c • μ)
参数：μ : MeasureTheory.Measure α；c • μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
-/
theorem Measure.smul_finite (μ : Measure α) [IsFiniteMeasure μ] {c : ℝ≥0∞} (hc : c ≠ ∞) :
    IsFiniteMeasure (c • μ) := by
  lift c to ℝ≥0 using hc
  exact MeasureTheory.isFiniteMeasureSMulNNReal
/-
**MeasureTheory.Measure.exists_isOpen_measure_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.Measure`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} [inst : TopologicalSpace α] (μ :
 MeasureTheory.Measure α)   [MeasureTheory.IsLocallyFiniteMeasure μ] (x : α), ∃ 
s, x ∈ s ∧ IsOpen s ∧ μ s < ⊤
参数：μ : MeasureTheory.Measure α；x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.Measure.FiniteAtFilter.exists_mem_basis`：∀ {α : Type u_1} 
{ι : Type u_4} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {f : Filte
r α},   μ.FiniteAtFilter f → ∀ {p : ι → Pro…
· 使用定理 `MeasureTheory.Measure.finiteAt_nhds`：∀ {α : Type u_1} {m0 : MeasurableSp
ace α} [inst : TopologicalSpace α] (μ : MeasureTheory.Measure α)   [MeasureTheor
y.IsLocallyFiniteMeasure …
· 使用定理 `nhds_basis_opens`：nhds_basis_opens (x : X) : (𝓝 x).HasBasis (fun s : Set
 X => x in s ∧ IsOpen s) fun s => s
-/
theorem Measure.exists_isOpen_measure_lt_top [TopologicalSpace α] (μ : Measure α)
    [IsLocallyFiniteMeasure μ] (x : α) : ∃ s : Set α, x ∈ s ∧ IsOpen s ∧ μ s < ∞ := by
  simpa only [and_assoc] using (μ.finiteAt_nhds x).exists_mem_basis (nhds_basis_opens x)
/-
**MeasureTheory.isLocallyFiniteMeasureSMulNNReal** 是 Mathlib 中的一个实例，位于命名空间 `Meas
ureTheory`。
形式化陈述：isLocallyFiniteMeasureSMulNNReal [TopologicalSpace α] (μ : Measure α) [IsL
ocallyFiniteMeasure μ] (c : Real>=0) : IsLocallyFiniteMeasure (c • μ)
参数：μ : Measure α；c : Real>=0。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.Measure.exists_isOpen_measure_lt_top`：∀ {α : Type u_1} {m0
 : MeasurableSpace α} [inst : TopologicalSpace α] (μ : MeasureTheory.Measure α) 
  [MeasureTheory.IsLocallyFiniteMeasure …
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `ENNReal.mul_lt_top`：mul_lt_top : a < ∞ -> b < ∞ -> a * b < ∞
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
instance isLocallyFiniteMeasureSMulNNReal [TopologicalSpace α] (μ : Measure α)
    [IsLocallyFiniteMeasure μ] (c : ℝ≥0) : IsLocallyFiniteMeasure (c • μ) := by
  refine ⟨fun x => ?_⟩
  rcases μ.exists_isOpen_measure_lt_top x with ⟨o, xo, o_open, μo⟩
  refine ⟨o, o_open.mem_nhds xo, ?_⟩
  apply ENNReal.mul_lt_top _ μo
  simp
/-
**MeasureTheory.Measure.isTopologicalBasis_isOpen_lt_top** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.Measure`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} [inst : TopologicalSpace α] (μ :
 MeasureTheory.Measure α)   [MeasureTheory.IsLocallyFiniteMeasure μ], Topologica
lSpace.IsTopologicalBasis {s | IsOpen s ∧ μ s < ⊤}
参数：μ : MeasureTheory.Measure α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds`：isTopologicalBasi
s_of_isOpen_of_nhds {s : Set (Set α)} (h_open : forall u in s, IsOpen u) (h_nhds
 : forall (a : α) (u : Set α), a in u -> Is…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.Measure.exists_isOpen_measure_lt_top`：∀ {α : Type u_1} {m0
 : MeasurableSpace α} [inst : TopologicalSpace α] (μ : MeasureTheory.Measure α) 
  [MeasureTheory.IsLocallyFiniteMeasure …
· 使用定理 `IsOpen.inter`：IsOpen.inter (s t : Set α) : IsOpen α s -> IsOpen α t -> I
sOpen α (s inter t)
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
-/
protected theorem Measure.isTopologicalBasis_isOpen_lt_top [TopologicalSpace α]
    (μ : Measure α) [IsLocallyFiniteMeasure μ] :
    TopologicalSpace.IsTopologicalBasis { s | IsOpen s ∧ μ s < ∞ } := by
  refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds (fun s hs => hs.1) ?_
  intro x s xs hs
  rcases μ.exists_isOpen_measure_lt_top x with ⟨v, xv, hv, μv⟩
  refine ⟨v ∩ s, ⟨hv.inter hs, lt_of_le_of_lt ?_ μv⟩, ⟨xv, xs⟩, inter_subset_right⟩
  exact measure_mono inter_subset_left
/-
**MeasureTheory.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [TopologicalSpace α] (μ : Measure α) [hμ : IsLocallyFiniteMeasure μ] :
    IsLocallyFiniteMeasure (μ.restrict s) where
  finiteAtNhds x := by
    obtain ⟨t, ht, hmus⟩ := hμ.finiteAtNhds x
    exact ⟨t, ht, lt_of_le_of_lt (restrict_apply_le s t) hmus⟩

/-- A measure `μ` is finite on compacts if any compact set `K` satisfies `μ K < ∞`. -/
/-
**MeasureTheory.IsFiniteMeasureOnCompacts** 是 Mathlib 中的一个归纳类型，位于命名空间 `MeasureTh
eory`。
形式化陈述：{α : Type u_1} → {m0 : MeasurableSpace α} → [TopologicalSpace α] → Measure
Theory.Measure α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A measure `μ` is finite on compacts if any compact set `K` satisfies `μ K < ∞`.
-/
class IsFiniteMeasureOnCompacts [TopologicalSpace α] (μ : Measure α) : Prop where
  protected lt_top_of_isCompact : ∀ ⦃K : Set α⦄, IsCompact K → μ K < ∞

/-- A compact subset has finite measure for a measure which is finite on compacts. -/
/-
**MeasureTheory._root_.IsCompact.measure_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A compact subset has finite measure for a measure which is finite on compacts.
-/
theorem _root_.IsCompact.measure_lt_top [TopologicalSpace α] {μ : Measure α}
    [IsFiniteMeasureOnCompacts μ] ⦃K : Set α⦄ (hK : IsCompact K) : μ K < ∞ :=
  IsFiniteMeasureOnCompacts.lt_top_of_isCompact hK

/-- A compact subset has finite measure for a measure which is finite on compacts. -/
/-
**MeasureTheory._root_.IsCompact.measure_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A compact subset has finite measure for a measure which is finite on compacts.
-/
theorem _root_.IsCompact.measure_ne_top [TopologicalSpace α] {μ : Measure α}
    [IsFiniteMeasureOnCompacts μ] ⦃K : Set α⦄ (hK : IsCompact K) : μ K ≠ ∞ :=
  hK.measure_lt_top.ne

/-- A bounded subset has finite measure for a measure which is finite on compact sets, in a
proper space. -/
/-
**MeasureTheory._root_.Bornology.IsBounded.measure_lt_top** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A bounded subset has finite measure for a measure which is finite on compact set
s, in a
proper space.
-/
theorem _root_.Bornology.IsBounded.measure_lt_top [PseudoMetricSpace α] [ProperSpace α]
    {μ : Measure α} [IsFiniteMeasureOnCompacts μ] ⦃s : Set α⦄ (hs : Bornology.IsBounded s) :
    μ s < ∞ :=
  calc
    μ s ≤ μ (closure s) := measure_mono subset_closure
    _ < ∞ := (Metric.isCompact_of_isClosed_isBounded isClosed_closure hs.closure).measure_lt_top
/-
**MeasureTheory.measure_closedBall_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：measure_closedBall_lt_top [PseudoMetricSpace α] [ProperSpace α] {μ : Measu
re α} [IsFiniteMeasureOnCompacts μ] {x : α} {r : Real} : μ (Metric.closedBall x 
r) < ∞
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bornology.IsBounded.measure_lt_top`：∀ {α : Type u_1} {m0 : MeasurableSpa
ce α} [inst : PseudoMetricSpace α] [ProperSpace α] {μ : MeasureTheory.Measure α}
   [MeasureTheory.IsFini…
· 使用定理 `Metric.isBounded_closedBall`：isBounded_closedBall : IsBounded (closedBal
l x r)
-/
theorem measure_closedBall_lt_top [PseudoMetricSpace α] [ProperSpace α] {μ : Measure α}
    [IsFiniteMeasureOnCompacts μ] {x : α} {r : ℝ} : μ (Metric.closedBall x r) < ∞ :=
  Metric.isBounded_closedBall.measure_lt_top

@[aesop (rule_sets := [finiteness]) safe apply]
/-
**MeasureTheory.measure_ball_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measure_ball_ne_top [PseudoMetricSpace α] [ProperSpace α] {μ : Measure α} 
[IsFiniteMeasureOnCompacts μ] {x : α} {r : Real} : μ (Metric.ball x r) != ∞
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Bornology.IsBounded.measure_lt_top`：∀ {α : Type u_1} {m0 : MeasurableSpa
ce α} [inst : PseudoMetricSpace α] [ProperSpace α] {μ : MeasureTheory.Measure α}
   [MeasureTheory.IsFini…
· 使用定理 `Metric.isBounded_ball`：isBounded_ball : IsBounded (ball x r)
-/
theorem measure_ball_ne_top [PseudoMetricSpace α] [ProperSpace α] {μ : Measure α}
    [IsFiniteMeasureOnCompacts μ] {x : α} {r : ℝ} : μ (Metric.ball x r) ≠ ∞ :=
  Metric.isBounded_ball.measure_lt_top.ne
/-
**MeasureTheory.measure_ball_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measure_ball_lt_top [PseudoMetricSpace α] [ProperSpace α] {μ : Measure α} 
[IsFiniteMeasureOnCompacts μ] {x : α} {r : Real} : μ (Metric.ball x r) < ∞
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `MeasureTheory.measure_ball_ne_top`：measure_ball_ne_top [PseudoMetricSpac
e α] [ProperSpace α] {μ : Measure α} [IsFiniteMeasureOnCompacts μ] {x : α} {r : 
Real} : μ (Metric.ball …
-/
theorem measure_ball_lt_top [PseudoMetricSpace α] [ProperSpace α] {μ : Measure α}
    [IsFiniteMeasureOnCompacts μ] {x : α} {r : ℝ} : μ (Metric.ball x r) < ∞ := by finiteness
/-
**MeasureTheory.IsFiniteMeasureOnCompacts.smul** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.IsFiniteMeasureOnCompacts`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} [inst : TopologicalSpace α] (μ :
 MeasureTheory.Measure α)   [MeasureTheory.IsFiniteMeasureOnCompacts μ] {c : ENN
Real}, c ≠ ⊤ → MeasureTheory.IsFiniteMeasureOnCompacts (c • μ)
参数：μ : MeasureTheory.Measure α；c • μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `ENNReal.mul_lt_top`：mul_lt_top : a < ∞ -> b < ∞ -> a * b < ∞
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `IsCompact.measure_lt_top`：∀ {α : Type u_1} {m0 : MeasurableSpace α} [ins
t : TopologicalSpace α] {μ : MeasureTheory.Measure α}   [MeasureTheory.IsFiniteM
easureOnCompac…
-/
protected theorem IsFiniteMeasureOnCompacts.smul [TopologicalSpace α] (μ : Measure α)
    [IsFiniteMeasureOnCompacts μ] {c : ℝ≥0∞} (hc : c ≠ ∞) : IsFiniteMeasureOnCompacts (c • μ) :=
  ⟨fun _K hK => ENNReal.mul_lt_top hc.lt_top hK.measure_lt_top⟩
/-
**MeasureTheory.IsFiniteMeasureOnCompacts.smul_nnreal** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.IsFiniteMeasureOnCompacts`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} [inst : TopologicalSpace α] (μ :
 MeasureTheory.Measure α)   [MeasureTheory.IsFiniteMeasureOnCompacts μ] (c : NNR
eal), MeasureTheory.IsFiniteMeasureOnCompacts (c • μ)
参数：μ : MeasureTheory.Measure α；c : NNReal；c • μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsFiniteMeasureOnCompacts.smul`：∀ {α : Type u_1} {m0 : Mea
surableSpace α} [inst : TopologicalSpace α] (μ : MeasureTheory.Measure α)   [Mea
sureTheory.IsFiniteMeasureOnCompac…
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞
-/
instance IsFiniteMeasureOnCompacts.smul_nnreal [TopologicalSpace α] (μ : Measure α)
    [IsFiniteMeasureOnCompacts μ] (c : ℝ≥0) : IsFiniteMeasureOnCompacts (c • μ) :=
  IsFiniteMeasureOnCompacts.smul μ coe_ne_top
/-
**MeasureTheory.instIsFiniteMeasureOnCompactsRestrict** 是 Mathlib 中的一个实例，位于命名空间 
`MeasureTheory`。
形式化陈述：instIsFiniteMeasureOnCompactsRestrict [TopologicalSpace α] {μ : Measure α}
 [IsFiniteMeasureOnCompacts μ] {s : Set α} : IsFiniteMeasureOnCompacts (μ.restri
ct s)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.Measure.restrict_apply_le`：restrict_apply_le (s t : Set α)
 : μ.restrict s t <= μ t
· 使用定理 `IsCompact.measure_lt_top`：∀ {α : Type u_1} {m0 : MeasurableSpace α} [ins
t : TopologicalSpace α] {μ : MeasureTheory.Measure α}   [MeasureTheory.IsFiniteM
easureOnCompac…
-/
instance instIsFiniteMeasureOnCompactsRestrict [TopologicalSpace α] {μ : Measure α}
    [IsFiniteMeasureOnCompacts μ] {s : Set α} : IsFiniteMeasureOnCompacts (μ.restrict s) :=
  ⟨fun _k hk ↦ (restrict_apply_le _ _).trans_lt hk.measure_lt_top⟩

variable {mβ} in
/-
**MeasureTheory.IsFiniteMeasureOnCompacts.comap'** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.IsFiniteMeasureOnCompacts`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m0 : MeasurableSpace α} {mβ : MeasurableS
pace β} [inst : TopologicalSpace α]   [inst_1 : TopologicalSpace β] (μ : Measure
Theory.Measure β) [MeasureTheory.IsFiniteMeasureOnCompacts μ] {f : α → β},   Con
tinuous f → MeasurableEmbedding f → MeasureTheory.IsFiniteMeasureOnCompacts (Mea
sureTheory.Measure.comap f μ)
参数：μ : MeasureTheory.Measure β；MeasureTheory.Measure.comap f μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasurableEmbedding.comap_apply`：comap_apply (μ : Measure β) (s : Set α)
 : comap f μ s = μ (f '' s)
· 使用定理 `MeasureTheory.IsFiniteMeasureOnCompacts.lt_top_of_isCompact`：∀ {α : Type
 u_1} {m0 : MeasurableSpace α} {inst : TopologicalSpace α} {μ : MeasureTheory.Me
asure α}   [self : MeasureTheory.IsFiniteMeasureO…
· 使用定理 `IsCompact.image`：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : C
ontinuous f) : IsCompact (f '' s)
-/
protected theorem IsFiniteMeasureOnCompacts.comap' [TopologicalSpace α] [TopologicalSpace β]
    (μ : Measure β) [IsFiniteMeasureOnCompacts μ] {f : α → β} (f_cont : Continuous f)
    (f_me : MeasurableEmbedding f) : IsFiniteMeasureOnCompacts (μ.comap f) where
  lt_top_of_isCompact K hK := by
    rw [f_me.comap_apply]
    exact IsFiniteMeasureOnCompacts.lt_top_of_isCompact (hK.image f_cont)
/-
**MeasureTheory.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) CompactSpace.isFiniteMeasure [TopologicalSpace α] [CompactSpace α]
    [IsFiniteMeasureOnCompacts μ] : IsFiniteMeasure μ :=
  ⟨IsFiniteMeasureOnCompacts.lt_top_of_isCompact isCompact_univ⟩

/-- A measure which is finite on compact sets in a locally compact space is locally finite. -/
/-
**MeasureTheory.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A measure which is finite on compact sets in a locally compact space is locally 
finite.
-/
instance (priority := 100) isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts [TopologicalSpace α]
    [WeaklyLocallyCompactSpace α] [IsFiniteMeasureOnCompacts μ] : IsLocallyFiniteMeasure μ :=
  ⟨fun x ↦
    let ⟨K, K_compact, K_mem⟩ := exists_compact_mem_nhds x
    ⟨K, K_mem, K_compact.measure_lt_top⟩⟩
/-
**MeasureTheory.exists_pos_measure_of_cover** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：exists_pos_measure_of_cover [Countable ι] {U : ι -> Set α} (hU : ⋃ i, U i 
= univ) (hμ : μ != 0) : exists i, 0 < μ (U i)
参数：hU : ⋃ i, U i = univ；hμ : μ != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.measure_univ_eq_zero`：measure_univ_eq_zero : μ uni
v = 0 ↔ μ = 0
· 使用定理 `MeasureTheory.measure_iUnion_null`：∀ {α : Type u_1} {F : Type u_3} [inst
 : FunLike F (Set α) ENNReal] [MeasureTheory.OuterMeasureClass F α] {μ : F}   {ι
 : Sort u_4} [Countable…
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
-/
theorem exists_pos_measure_of_cover [Countable ι] {U : ι → Set α} (hU : ⋃ i, U i = univ)
    (hμ : μ ≠ 0) : ∃ i, 0 < μ (U i) := by
  contrapose! hμ with H
  rw [← measure_univ_eq_zero, ← hU]
  exact measure_iUnion_null fun i => nonpos_iff_eq_zero.1 (H i)
/-
**MeasureTheory.exists_pos_preimage_ball** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：exists_pos_preimage_ball [PseudoMetricSpace δ] (f : α -> δ) (x : δ) (hμ : 
μ != 0) : exists n : Nat, 0 < μ (f ⁻¹' Metric.ball x n)
参数：f : α -> δ；x : δ；hμ : μ != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.exists_pos_measure_of_cover`：exists_pos_measure_of_cover [
Countable ι] {U : ι -> Set α} (hU : ⋃ i, U i = univ) (hμ : μ != 0) : exists i, 0
 < μ (U i)
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.preimage_iUnion`：preimage_iUnion {f : α -> β} {s : ι -> Set β} : (f 
⁻¹' ⋃ i, s i) = ⋃ i, f ⁻¹' s i
· 使用定理 `Metric.iUnion_ball_nat`：iUnion_ball_nat (x : α) : ⋃ n : Nat, ball x n = 
univ
· 使用定理 `Set.preimage_univ`：preimage_univ : f ⁻¹' univ = univ
-/
theorem exists_pos_preimage_ball [PseudoMetricSpace δ] (f : α → δ) (x : δ) (hμ : μ ≠ 0) :
    ∃ n : ℕ, 0 < μ (f ⁻¹' Metric.ball x n) :=
  exists_pos_measure_of_cover (by rw [← preimage_iUnion, Metric.iUnion_ball_nat, preimage_univ]) hμ
/-
**MeasureTheory.exists_pos_ball** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：exists_pos_ball [PseudoMetricSpace α] (x : α) (hμ : μ != 0) : exists n : N
at, 0 < μ (Metric.ball x n)
参数：x : α；hμ : μ != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.exists_pos_preimage_ball`：exists_pos_preimage_ball [Pseudo
MetricSpace δ] (f : α -> δ) (x : δ) (hμ : μ != 0) : exists n : Nat, 0 < μ (f ⁻¹'
 Metric.ball x n)
-/
theorem exists_pos_ball [PseudoMetricSpace α] (x : α) (hμ : μ ≠ 0) :
    ∃ n : ℕ, 0 < μ (Metric.ball x n) :=
  exists_pos_preimage_ball id x hμ

/-- If a set has zero measure in a neighborhood of each of its points, then it has zero measure
in a second-countable space. -/
/-
**MeasureTheory.exists_ne_forall_mem_nhds_pos_measure_preimage** 是 Mathlib 中的一个定
理，位于命名空间 `MeasureTheory`。
形式化陈述：exists_ne_forall_mem_nhds_pos_measure_preimage {β} [TopologicalSpace β] [T
1Space β] [SecondCountableTopology β] [Nonempty β] {f : α -> β} (h : forall b, e
xistsᵐ x ∂μ, f x != b) : exists a b : β, a != b ∧ (forall s in 𝓝 a, 0 < μ (f ⁻¹'
 s)) ∧ forall t in 𝓝 b, 0 < μ (f ⁻¹' t)
参数：h : forall b, existsᵐ x ∂μ, f x != b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.not_eventually`：not_eventually {p : α -> Prop} {f : Filter α} : (
¬forallᶠ x in f, p x) ↔ existsᶠ x in f, ¬p x
· 使用定理 `ne_bot_of_le_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : Or
derBot α] {a b : α}, b ≠ ⊥ → b ≤ a → a ≠ ⊥
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.OuterMeasure.instOuterMeasureClass`：∀ {α : Type u_1}, Meas
ureTheory.OuterMeasureClass (MeasureTheory.OuterMeasure α) α
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `MeasureTheory.exists_mem_forall_mem_nhdsWithin_pos_measure`：exists_mem_f
orall_mem_nhdsWithin_pos_measure [TopologicalSpace α] [SecondCountableTopology α
] {s : Set α} (hs : μ s != 0) : exists x in s, f…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOpen.nhdsWithin_eq`：IsOpen.nhdsWithin_eq {a : α} {s : Set α} (h : IsOp
en s) (ha : a in s) : 𝓝[s] a = 𝓝 a
· 使用定理 `isOpen_compl_singleton`：isOpen_compl_singleton [T1Space X] {x : X} : IsO
pen ({x}ᶜ : Set X)
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a

--- 原说明 ---
If a set has zero measure in a neighborhood of each of its points, then it has z
ero measure
in a second-countable space.
-/
theorem exists_ne_forall_mem_nhds_pos_measure_preimage {β} [TopologicalSpace β] [T1Space β]
    [SecondCountableTopology β] [Nonempty β] {f : α → β} (h : ∀ b, ∃ᵐ x ∂μ, f x ≠ b) :
    ∃ a b : β, a ≠ b ∧ (∀ s ∈ 𝓝 a, 0 < μ (f ⁻¹' s)) ∧ ∀ t ∈ 𝓝 b, 0 < μ (f ⁻¹' t) := by
  -- We use an `OuterMeasure` so that the proof works without `Measurable f`
  set m : OuterMeasure β := OuterMeasure.map f μ.toOuterMeasure
  replace h : ∀ b : β, m {b}ᶜ ≠ 0 := fun b => not_eventually.mpr (h b)
  inhabit β
  have : m univ ≠ 0 := ne_bot_of_le_ne_bot (h default) (measure_mono <| subset_univ _)
  rcases exists_mem_forall_mem_nhdsWithin_pos_measure this with ⟨b, -, hb⟩
  simp only [nhdsWithin_univ] at hb
  rcases exists_mem_forall_mem_nhdsWithin_pos_measure (h b) with ⟨a, hab : a ≠ b, ha⟩
  simp only [isOpen_compl_singleton.nhdsWithin_eq hab] at ha
  exact ⟨a, b, hab, ha, hb⟩

/-- If two finite measures give the same mass to the whole space and coincide on a π-system made
of measurable sets, then they coincide on all sets in the σ-algebra generated by the π-system. -/
/-
**MeasureTheory.ext_on_measurableSpace_of_generate_finite** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory`。
形式化陈述：ext_on_measurableSpace_of_generate_finite {α} (m₀ : MeasurableSpace α) {μ 
ν : Measure α} [IsFiniteMeasure μ] (C : Set (Set α)) (hμν : forall s in C, μ s =
 ν s) {m : MeasurableSpace α} (h : m <= m₀) (hA : m = MeasurableSpace.generateFr
om C) (hC : IsPiSystem C) (h_univ : μ Set.univ = ν Set.univ) {s : Set α} (hs : M
easurableSet[m] s) : μ s = ν s
参数：m₀ : MeasurableSpace α；C : Set (Set α)；hμν : forall s in C, μ s = ν s；h : m <
= m₀；hA : m = MeasurableSpace.generateFrom C；hC : IsPiSystem C；h_univ : μ Set.un
iv = ν Set.univ；hs : MeasurableSet[m] s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.IsFiniteMeasure.measure_univ_lt_top`：∀ {α : Type u_1} {m0 
: MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsFinit
eMeasure μ],   μ Set.univ < ⊤
· 使用定理 `MeasurableSpace.induction_on_inter`：induction_on_inter {m : MeasurableSp
ace α} {C : forall s : Set α, MeasurableSet s -> Prop} {s : Set (Set α)} (h_eq :
 m = generateFrom s) (h_…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.measure_compl`：measure_compl (h₁ : MeasurableSet s) (h_fin
 : μ s != ∞) : μ sᶜ = μ univ - μ s
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `MeasureTheory.measure_iUnion`：measure_iUnion {m0 : MeasurableSpace α} {μ
 : Measure α} [Countable ι] {f : ι -> Set α} (hn : Pairwise (Disjoint on f)) (h 
: forall i, Measur…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g

--- 原说明 ---
If two finite measures give the same mass to the whole space and coincide on a π
-system made
of measurable sets, then they coincide on all sets in the σ-algebra generated by
 the π-system.
-/
theorem ext_on_measurableSpace_of_generate_finite {α} (m₀ : MeasurableSpace α) {μ ν : Measure α}
    [IsFiniteMeasure μ] (C : Set (Set α)) (hμν : ∀ s ∈ C, μ s = ν s) {m : MeasurableSpace α}
    (h : m ≤ m₀) (hA : m = MeasurableSpace.generateFrom C) (hC : IsPiSystem C)
    (h_univ : μ Set.univ = ν Set.univ) {s : Set α} (hs : MeasurableSet[m] s) : μ s = ν s := by
  have : IsFiniteMeasure ν := by
    constructor
    rw [← h_univ]
    apply IsFiniteMeasure.measure_univ_lt_top
  induction s, hs using induction_on_inter hA hC with
  | empty => simp
  | basic t ht => exact hμν t ht
  | compl t htm iht =>
    rw [measure_compl (h t htm) (by finiteness), measure_compl (h t htm) (by finiteness), iht,
      h_univ]
  | iUnion f hfd hfm ihf =>
    simp [measure_iUnion, hfd, h _ (hfm _), ihf]

/-- Two finite measures are equal if they are equal on the π-system generating the σ-algebra
  (and `univ`). -/
/-
**MeasureTheory.ext_of_generate_finite** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：ext_of_generate_finite (C : Set (Set α)) (hA : m0 = generateFrom C) (hC : 
IsPiSystem C) [IsFiniteMeasure μ] (hμν : forall s in C, μ s = ν s) (h_univ : μ u
niv = ν univ) : μ = ν
参数：C : Set (Set α)；hA : m0 = generateFrom C；hC : IsPiSystem C；hμν : forall s in 
C, μ s = ν s；h_univ : μ univ = ν univ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `MeasureTheory.ext_on_measurableSpace_of_generate_finite`：ext_on_measurab
leSpace_of_generate_finite {α} (m₀ : MeasurableSpace α) {μ ν : Measure α} [IsFin
iteMeasure μ] (C : Set (Set α)) (hμν : forall…
· 使用引理 `le_rfl`：le_rfl : a <= a

--- 原说明 ---
Two finite measures are equal if they are equal on the π-system generating the σ
-algebra
  (and `univ`).
-/
theorem ext_of_generate_finite (C : Set (Set α)) (hA : m0 = generateFrom C) (hC : IsPiSystem C)
    [IsFiniteMeasure μ] (hμν : ∀ s ∈ C, μ s = ν s) (h_univ : μ univ = ν univ) : μ = ν :=
  Measure.ext fun _s hs =>
    ext_on_measurableSpace_of_generate_finite m0 C hμν le_rfl hA hC h_univ hs

namespace Measure

namespace FiniteAtFilter

variable {f g : Filter α}

/-
**MeasureTheory.Measure.FiniteAtFilter.filter_mono** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.Measure.FiniteAtFilter`。
形式化陈述：filter_mono (h : f <= g) : μ.FiniteAtFilter g -> μ.FiniteAtFilter f
参数：h : f <= g。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem filter_mono (h : f ≤ g) : μ.FiniteAtFilter g → μ.FiniteAtFilter f := fun ⟨s, hs, hμ⟩ =>
  ⟨s, h hs, hμ⟩
/-
**MeasureTheory.Measure.FiniteAtFilter.inf_of_left** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.Measure.FiniteAtFilter`。
形式化陈述：inf_of_left (h : μ.FiniteAtFilter f) : μ.FiniteAtFilter (f ⊓ g)
参数：h : μ.FiniteAtFilter f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.FiniteAtFilter.filter_mono`：filter_mono (h : f <= 
g) : μ.FiniteAtFilter g -> μ.FiniteAtFilter f
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
-/
theorem inf_of_left (h : μ.FiniteAtFilter f) : μ.FiniteAtFilter (f ⊓ g) :=
  h.filter_mono inf_le_left
/-
**MeasureTheory.Measure.FiniteAtFilter.inf_of_right** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.Measure.FiniteAtFilter`。
形式化陈述：inf_of_right (h : μ.FiniteAtFilter g) : μ.FiniteAtFilter (f ⊓ g)
参数：h : μ.FiniteAtFilter g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.FiniteAtFilter.filter_mono`：filter_mono (h : f <= 
g) : μ.FiniteAtFilter g -> μ.FiniteAtFilter f
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
-/
theorem inf_of_right (h : μ.FiniteAtFilter g) : μ.FiniteAtFilter (f ⊓ g) :=
  h.filter_mono inf_le_right

@[simp]
/-
**MeasureTheory.Measure.FiniteAtFilter.inf_ae_iff** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.Measure.FiniteAtFilter`。
形式化陈述：inf_ae_iff : μ.FiniteAtFilter (f ⊓ ae μ) ↔ μ.FiniteAtFilter f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.measure_mono_ae`：measure_mono_ae (H : s <=ᵐ[μ] t) : μ s <=
 μ t
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.FiniteAtFilter.filter_mono`：filter_mono (h : f <= 
g) : μ.FiniteAtFilter g -> μ.FiniteAtFilter f
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
-/
theorem inf_ae_iff : μ.FiniteAtFilter (f ⊓ ae μ) ↔ μ.FiniteAtFilter f := by
  refine ⟨?_, fun h => h.filter_mono inf_le_left⟩
  rintro ⟨s, ⟨t, ht, u, hu, rfl⟩, hμ⟩
  suffices μ t ≤ μ (t ∩ u) from ⟨t, ht, this.trans_lt hμ⟩
  exact measure_mono_ae (mem_of_superset hu fun x hu ht => ⟨ht, hu⟩)

alias ⟨of_inf_ae, _⟩ := inf_ae_iff
/-
**MeasureTheory.Measure.FiniteAtFilter.filter_mono_ae** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.Measure.FiniteAtFilter`。
形式化陈述：filter_mono_ae (h : f ⊓ (ae μ) <= g) (hg : μ.FiniteAtFilter g) : μ.FiniteA
tFilter f
参数：h : f ⊓ (ae μ) <= g；hg : μ.FiniteAtFilter g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.Measure.FiniteAtFilter.inf_ae_iff`：inf_ae_iff : μ.FiniteAt
Filter (f ⊓ ae μ) ↔ μ.FiniteAtFilter f
· 使用定理 `MeasureTheory.Measure.FiniteAtFilter.filter_mono`：filter_mono (h : f <= 
g) : μ.FiniteAtFilter g -> μ.FiniteAtFilter f
-/
theorem filter_mono_ae (h : f ⊓ (ae μ) ≤ g) (hg : μ.FiniteAtFilter g) : μ.FiniteAtFilter f :=
  inf_ae_iff.1 (hg.filter_mono h)
/-
**MeasureTheory.Measure.FiniteAtFilter.measure_mono** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.Measure.FiniteAtFilter`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} 
{f : Filter α},   μ ≤ ν → ν.FiniteAtFilter f → μ.FiniteAtFilter f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.Measure.le_iff'`：le_iff' : μ₁ <= μ₂ ↔ forall s, μ₁ s <= μ₂
 s
-/
protected theorem measure_mono (h : μ ≤ ν) : ν.FiniteAtFilter f → μ.FiniteAtFilter f :=
  fun ⟨s, hs, hν⟩ => ⟨s, hs, (Measure.le_iff'.1 h s).trans_lt hν⟩

@[gcongr, mono]
/-
**MeasureTheory.Measure.FiniteAtFilter.mono** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.Measure.FiniteAtFilter`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} 
{f g : Filter α},   f ≤ g → μ ≤ ν → ν.FiniteAtFilter g → μ.FiniteAtFilter f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.FiniteAtFilter.measure_mono`：∀ {α : Type u_1} {m0 
: MeasurableSpace α} {μ ν : MeasureTheory.Measure α} {f : Filter α},   μ ≤ ν → ν
.FiniteAtFilter f → μ.FiniteAtFilter f
· 使用定理 `MeasureTheory.Measure.FiniteAtFilter.filter_mono`：filter_mono (h : f <= 
g) : μ.FiniteAtFilter g -> μ.FiniteAtFilter f
-/
protected theorem mono (hf : f ≤ g) (hμ : μ ≤ ν) : ν.FiniteAtFilter g → μ.FiniteAtFilter f :=
  fun h => (h.filter_mono hf).measure_mono hμ
/-
**MeasureTheory.Measure.FiniteAtFilter.eventually** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.Measure.FiniteAtFilter`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {f
 : Filter α},   μ.FiniteAtFilter f → ∀ᶠ (s : Set α) in f.smallSets, μ s < ⊤
参数：s : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.eventually_smallSets'`：eventually_smallSets' {p : Set α -> Prop} 
(hp : forall ⦃s t⦄, s subseteq t -> p t -> p s) : (forallᶠ s in l.smallSets, p s
) ↔ exists s in l,…
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
protected theorem eventually (h : μ.FiniteAtFilter f) : ∀ᶠ s in f.smallSets, μ s < ∞ :=
  (eventually_smallSets' fun _s _t hst ht => (measure_mono hst).trans_lt ht).2 h
/-
**MeasureTheory.Measure.FiniteAtFilter.filterSup** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.Measure.FiniteAtFilter`。
形式化陈述：filterSup : μ.FiniteAtFilter f -> μ.FiniteAtFilter g -> μ.FiniteAtFilter (
f ⊔ g)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.union_mem_sup`：union_mem_sup {f g : Filter α} {s t : Set α} (hs :
 s in f) (ht : t in g) : s union t in f ⊔ g
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.measure_union_le`：measure_union_le (s t : Set α) : μ (s un
ion t) <= μ s + μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.add_lt_top`：∀ {a b : ENNReal}, a + b < ⊤ ↔ a < ⊤ ∧ b < ⊤
-/
theorem filterSup : μ.FiniteAtFilter f → μ.FiniteAtFilter g → μ.FiniteAtFilter (f ⊔ g) :=
  fun ⟨s, hsf, hsμ⟩ ⟨t, htg, htμ⟩ =>
  ⟨s ∪ t, union_mem_sup hsf htg, (measure_union_le s t).trans_lt (ENNReal.add_lt_top.2 ⟨hsμ, htμ⟩)⟩

end FiniteAtFilter

/-
**MeasureTheory.Measure.finiteAt_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.Measure`。
形式化陈述：finiteAt_nhdsWithin [TopologicalSpace α] {_m0 : MeasurableSpace α} (μ : Me
asure α) [IsLocallyFiniteMeasure μ] (x : α) (s : Set α) : μ.FiniteAtFilter (𝓝[s]
 x)
参数：μ : Measure α；x : α；s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.FiniteAtFilter.inf_of_left`：inf_of_left (h : μ.Fin
iteAtFilter f) : μ.FiniteAtFilter (f ⊓ g)
· 使用定理 `MeasureTheory.Measure.finiteAt_nhds`：∀ {α : Type u_1} {m0 : MeasurableSp
ace α} [inst : TopologicalSpace α] (μ : MeasureTheory.Measure α)   [MeasureTheor
y.IsLocallyFiniteMeasure …
-/
theorem finiteAt_nhdsWithin [TopologicalSpace α] {_m0 : MeasurableSpace α} (μ : Measure α)
    [IsLocallyFiniteMeasure μ] (x : α) (s : Set α) : μ.FiniteAtFilter (𝓝[s] x) :=
  (finiteAt_nhds μ x).inf_of_left

@[simp]
/-
**MeasureTheory.Measure.finiteAt_principal** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.Measure`。
形式化陈述：finiteAt_principal : μ.FiniteAtFilter (𝓟 s) ↔ μ s < ∞
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.mem_principal_self`：mem_principal_self (s : Set α) : s in 𝓟 s
-/
theorem finiteAt_principal : μ.FiniteAtFilter (𝓟 s) ↔ μ s < ∞ :=
  ⟨fun ⟨_t, ht, hμ⟩ => (measure_mono ht).trans_lt hμ, fun h => ⟨s, mem_principal_self s, h⟩⟩
/-
**MeasureTheory.Measure.isLocallyFiniteMeasure_of_le** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.Measure`。
形式化陈述：isLocallyFiniteMeasure_of_le [TopologicalSpace α] {_m : MeasurableSpace α}
 {μ ν : Measure α} [H : IsLocallyFiniteMeasure μ] (h : ν <= μ) : IsLocallyFinite
Measure ν
参数：h : ν <= μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsLocallyFiniteMeasure.finiteAtNhds`：∀ {α : Type u_1} {m0 
: MeasurableSpace α} {inst : TopologicalSpace α} {μ : MeasureTheory.Measure α}  
 [self : MeasureTheory.IsLocallyFiniteM…
· 使用定理 `MeasureTheory.Measure.FiniteAtFilter.measure_mono`：∀ {α : Type u_1} {m0 
: MeasurableSpace α} {μ ν : MeasureTheory.Measure α} {f : Filter α},   μ ≤ ν → ν
.FiniteAtFilter f → μ.FiniteAtFilter f
-/
theorem isLocallyFiniteMeasure_of_le [TopologicalSpace α] {_m : MeasurableSpace α} {μ ν : Measure α}
    [H : IsLocallyFiniteMeasure μ] (h : ν ≤ μ) : IsLocallyFiniteMeasure ν :=
  let F := H.finiteAtNhds
  ⟨fun x => (F x).measure_mono h⟩

end Measure

end MeasureTheory

namespace IsCompact

variable [TopologicalSpace α] [MeasurableSpace α] {μ : Measure α} {s : Set α}

/-- If `s` is a compact set and `μ` is finite at `𝓝 x` for every `x ∈ s`, then `s` admits an open
superset of finite measure. -/
/-
**IsCompact.exists_open_superset_measure_lt_top'** 是 Mathlib 中的一个定理，位于命名空间 `IsCo
mpact`。
形式化陈述：exists_open_superset_measure_lt_top' (h : IsCompact s) (hμ : forall x in s
, μ.FiniteAtFilter (𝓝 x)) : exists U ⊇ s, IsOpen U ∧ μ U < ∞
参数：h : IsCompact s；hμ : forall x in s, μ.FiniteAtFilter (𝓝 x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.induction_on`：IsCompact.induction_on (hs : IsCompact s) {p : S
et X -> Prop} (he : p ∅) (hmono : forall ⦃s t⦄, s subseteq t -> p t -> p s) (hun
ion : forall…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.union_subset_union`：union_subset_union {s₁ s₂ t₁ t₂ : Set α} (h₁ : s
₁ subseteq s₂) (h₂ : t₁ subseteq t₂) : s₁ union t₁ subseteq s₂ union t₂
· 使用定理 `IsOpen.union`：IsOpen.union (h₁ : IsOpen s₁) (h₂ : IsOpen s₂) : IsOpen (s
₁ union s₂)
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.measure_union_le`：measure_union_le (s t : Set α) : μ (s un
ion t) <= μ s + μ t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.add_lt_top`：∀ {a b : ENNReal}, a + b < ⊤ ↔ a < ⊤ ∧ b < ⊤
· 使用定理 `MeasureTheory.Measure.FiniteAtFilter.exists_mem_basis`：∀ {α : Type u_1} 
{ι : Type u_4} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {f : Filte
r α},   μ.FiniteAtFilter f → ∀ {p : ι → Pro…
· 使用定理 `nhds_basis_opens`：nhds_basis_opens (x : X) : (𝓝 x).HasBasis (fun s : Set
 X => x in s ∧ IsOpen s) fun s => s
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s

--- 原说明 ---
If `s` is a compact set and `μ` is finite at `𝓝 x` for every `x ∈ s`, then `s` a
dmits an open
superset of finite measure.
-/
theorem exists_open_superset_measure_lt_top' (h : IsCompact s)
    (hμ : ∀ x ∈ s, μ.FiniteAtFilter (𝓝 x)) : ∃ U ⊇ s, IsOpen U ∧ μ U < ∞ := by
  refine IsCompact.induction_on h ?_ ?_ ?_ ?_
  · use ∅
    simp
  · rintro s t hst ⟨U, htU, hUo, hU⟩
    exact ⟨U, hst.trans htU, hUo, hU⟩
  · rintro s t ⟨U, hsU, hUo, hU⟩ ⟨V, htV, hVo, hV⟩
    refine
      ⟨U ∪ V, union_subset_union hsU htV, hUo.union hVo,
        (measure_union_le _ _).trans_lt <| ENNReal.add_lt_top.2 ⟨hU, hV⟩⟩
  · intro x hx
    rcases (hμ x hx).exists_mem_basis (nhds_basis_opens _) with ⟨U, ⟨hx, hUo⟩, hU⟩
    exact ⟨U, nhdsWithin_le_nhds (hUo.mem_nhds hx), U, Subset.rfl, hUo, hU⟩

/-- If `s` is a compact set and `μ` is a locally finite measure, then `s` admits an open superset of
finite measure. -/
/-
**IsCompact.exists_open_superset_measure_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `IsCom
pact`。
形式化陈述：exists_open_superset_measure_lt_top (h : IsCompact s) (μ : Measure α) [IsL
ocallyFiniteMeasure μ] : exists U ⊇ s, IsOpen U ∧ μ U < ∞
参数：h : IsCompact s；μ : Measure α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.exists_open_superset_measure_lt_top'`：exists_open_superset_mea
sure_lt_top' (h : IsCompact s) (hμ : forall x in s, μ.FiniteAtFilter (𝓝 x)) : ex
ists U ⊇ s, IsOpen U ∧ μ U < ∞
· 使用定理 `MeasureTheory.Measure.finiteAt_nhds`：∀ {α : Type u_1} {m0 : MeasurableSp
ace α} [inst : TopologicalSpace α] (μ : MeasureTheory.Measure α)   [MeasureTheor
y.IsLocallyFiniteMeasure …

--- 原说明 ---
If `s` is a compact set and `μ` is a locally finite measure, then `s` admits an 
open superset of
finite measure.
-/
theorem exists_open_superset_measure_lt_top (h : IsCompact s) (μ : Measure α)
    [IsLocallyFiniteMeasure μ] : ∃ U ⊇ s, IsOpen U ∧ μ U < ∞ :=
  h.exists_open_superset_measure_lt_top' fun x _ => μ.finiteAt_nhds x
/-
**IsCompact.measure_lt_top_of_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 `IsCompact`。
形式化陈述：measure_lt_top_of_nhdsWithin (h : IsCompact s) (hμ : forall x in s, μ.Fini
teAtFilter (𝓝[s] x)) : μ s < ∞
参数：h : IsCompact s；hμ : forall x in s, μ.FiniteAtFilter (𝓝[s] x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.induction_on`：IsCompact.induction_on (hs : IsCompact s) {p : S
et X -> Prop} (he : p ∅) (hmono : forall ⦃s t⦄, s subseteq t -> p t -> p s) (hun
ion : forall…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.measure_union_le`：measure_union_le (s t : Set α) : μ (s un
ion t) <= μ s + μ t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.add_lt_top`：∀ {a b : ENNReal}, a + b < ⊤ ↔ a < ⊤ ∧ b < ⊤
-/
theorem measure_lt_top_of_nhdsWithin (h : IsCompact s) (hμ : ∀ x ∈ s, μ.FiniteAtFilter (𝓝[s] x)) :
    μ s < ∞ :=
  IsCompact.induction_on h (by simp) (fun _ _ hst ht => (measure_mono hst).trans_lt ht)
    (fun s t hs ht => (measure_union_le s t).trans_lt (ENNReal.add_lt_top.2 ⟨hs, ht⟩)) hμ
/-
**IsCompact.measure_zero_of_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 `IsCompact`。
形式化陈述：measure_zero_of_nhdsWithin (hs : IsCompact s) : (forall a in s, exists t i
n 𝓝[s] a, μ t = 0) -> μ s = 0
参数：hs : IsCompact s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsCompact.compl_mem_sets_of_nhdsWithin`：IsCompact.compl_mem_sets_of_nhds
Within (hs : IsCompact s) {f : Filter X} (hf : forall x in s, exists t in 𝓝[s] x
, tᶜ in f) : sᶜ in f
-/
theorem measure_zero_of_nhdsWithin (hs : IsCompact s) :
    (∀ a ∈ s, ∃ t ∈ 𝓝[s] a, μ t = 0) → μ s = 0 := by
  simpa only [← compl_mem_ae_iff] using hs.compl_mem_sets_of_nhdsWithin

end IsCompact

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure [TopologicalSpace α]
    {_ : MeasurableSpace α} {μ : Measure α} [IsLocallyFiniteMeasure μ] :
    IsFiniteMeasureOnCompacts μ :=
  ⟨fun _s hs => hs.measure_lt_top_of_nhdsWithin fun _ _ => μ.finiteAt_nhdsWithin _ _⟩
/-
**isFiniteMeasure_iff_isFiniteMeasureOnCompacts_of_compactSpace** 是 Mathlib 中的一个
定理，位于命名空间 ``。
形式化陈述：isFiniteMeasure_iff_isFiniteMeasureOnCompacts_of_compactSpace [Topological
Space α] [MeasurableSpace α] {μ : Measure α} [CompactSpace α] : IsFiniteMeasure 
μ ↔ IsFiniteMeasureOnCompacts μ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure`：∀ {α : Type u_1} [i
nst : TopologicalSpace α] {x : MeasurableSpace α} {μ : MeasureTheory.Measure α} 
  [MeasureTheory.IsLocallyFiniteMeasure μ…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toIsLocallyFiniteMeasure`：∀ {α : Type u_1}
 {m0 : MeasurableSpace α} [inst : TopologicalSpace α] (μ : MeasureTheory.Measure
 α)   [MeasureTheory.IsFiniteMeasure μ], Mea…
· 使用定理 `MeasureTheory.CompactSpace.isFiniteMeasure`：∀ {α : Type u_1} {m0 : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace α] [Compact
Space α]   [MeasureTheory.IsFini…
-/
theorem isFiniteMeasure_iff_isFiniteMeasureOnCompacts_of_compactSpace [TopologicalSpace α]
    [MeasurableSpace α] {μ : Measure α} [CompactSpace α] :
    IsFiniteMeasure μ ↔ IsFiniteMeasureOnCompacts μ := by
  constructor <;> intros
  · infer_instance
  · exact CompactSpace.isFiniteMeasure

/-- Compact covering of a `σ`-compact topological space as
`MeasureTheory.Measure.FiniteSpanningSetsIn`. -/
-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/-
**MeasureTheory.Measure.finiteSpanningSetsInCompact** 是 Mathlib 中的一个定义，位于命名空间 ``
。
形式化陈述：MeasureTheory.Measure.finiteSpanningSetsInCompact [TopologicalSpace α] [Si
gmaCompactSpace α] {_ : MeasurableSpace α} (μ : Measure α) [IsLocallyFiniteMeasu
re μ] : μ.FiniteSpanningSetsIn { K | IsCompact K } where set
参数：μ : Measure α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `isCompact_compactCovering`：isCompact_compactCovering (n : Nat) : IsCompa
ct (compactCovering X n)
· 使用定理 `iUnion_compactCovering`：iUnion_compactCovering : ⋃ n, compactCovering X 
n = univ
-/
noncomputable def MeasureTheory.Measure.finiteSpanningSetsInCompact
    [TopologicalSpace α] [SigmaCompactSpace α]
    {_ : MeasurableSpace α} (μ : Measure α) [IsLocallyFiniteMeasure μ] :
    μ.FiniteSpanningSetsIn { K | IsCompact K } where
  set := compactCovering α
  set_mem := isCompact_compactCovering α
  finite n := (isCompact_compactCovering α n).measure_lt_top
  spanning := iUnion_compactCovering α

/-- A locally finite measure on a `σ`-compact topological space admits a finite spanning sequence
of open sets. -/
-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/-
**MeasureTheory.Measure.finiteSpanningSetsInOpen** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MeasureTheory.Measure.finiteSpanningSetsInOpen [TopologicalSpace α] [Sigma
CompactSpace α] {_ : MeasurableSpace α} (μ : Measure α) [IsLocallyFiniteMeasure 
μ] : μ.FiniteSpanningSetsIn { K | IsOpen K } where set n
参数：μ : Measure α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def MeasureTheory.Measure.finiteSpanningSetsInOpen
    [TopologicalSpace α] [SigmaCompactSpace α]
    {_ : MeasurableSpace α} (μ : Measure α) [IsLocallyFiniteMeasure μ] :
    μ.FiniteSpanningSetsIn { K | IsOpen K } where
  set n := ((isCompact_compactCovering α n).exists_open_superset_measure_lt_top μ).choose
  set_mem n :=
    ((isCompact_compactCovering α n).exists_open_superset_measure_lt_top μ).choose_spec.2.1
  finite n :=
    ((isCompact_compactCovering α n).exists_open_superset_measure_lt_top μ).choose_spec.2.2
  spanning :=
    eq_univ_of_subset
      (iUnion_mono fun n =>
        ((isCompact_compactCovering α n).exists_open_superset_measure_lt_top μ).choose_spec.1)
      (iUnion_compactCovering α)

open TopologicalSpace

/-- A locally finite measure on a second countable topological space admits a finite spanning
sequence of open sets. -/
noncomputable irreducible_def MeasureTheory.Measure.finiteSpanningSetsInOpen' [TopologicalSpace α]
  [SecondCountableTopology α] {m : MeasurableSpace α} (μ : Measure α) [IsLocallyFiniteMeasure μ] :
  μ.FiniteSpanningSetsIn { K | IsOpen K } := by
  suffices H : Nonempty (μ.FiniteSpanningSetsIn { K | IsOpen K }) from H.some
  cases isEmpty_or_nonempty α
  · exact
      ⟨{  set := fun _ => ∅
          set_mem := fun _ => by simp
          finite := fun _ => by simp
          spanning := by simp [eq_iff_true_of_subsingleton] }⟩
  inhabit α
  let S : Set (Set α) := { s | IsOpen s ∧ μ s < ∞ }
  obtain ⟨T, T_count, TS, hT⟩ : ∃ T : Set (Set α), T.Countable ∧ T ⊆ S ∧ ⋃₀ T = ⋃₀ S :=
    isOpen_sUnion_countable S fun s hs => hs.1
  rw [μ.isTopologicalBasis_isOpen_lt_top.sUnion_eq] at hT
  have T_ne : T.Nonempty := by
    by_contra h'T
    rw [not_nonempty_iff_eq_empty.1 h'T, sUnion_empty] at hT
    simpa only [← hT] using! mem_univ (default : α)
  obtain ⟨f, hf⟩ : ∃ f : ℕ → Set α, T = range f := T_count.exists_eq_range T_ne
  have fS : ∀ n, f n ∈ S := by
    intro n
    apply TS
    rw [hf]
    exact mem_range_self n
  refine
    ⟨{  set := f
        set_mem := fun n => (fS n).1
        finite := fun n => (fS n).2
        spanning := ?_ }⟩
  refine eq_univ_of_forall fun x => ?_
  obtain ⟨t, tT, xt⟩ : ∃ t : Set α, t ∈ range f ∧ x ∈ t := by
    have : x ∈ ⋃₀ T := by simp only [hT, mem_univ]
    simpa only [mem_sUnion, exists_prop, ← hf]
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, f n = t := by simpa only using! tT
  exact mem_iUnion_of_mem _ xt

section MeasureIxx

variable [Preorder α] [TopologicalSpace α] [CompactIccSpace α] {m : MeasurableSpace α}
  {μ : Measure α} [IsLocallyFiniteMeasure μ] {a b : α}

/-
**measure_Icc_lt_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measure_Icc_lt_top : μ (Icc a b) < ∞
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.measure_lt_top`：∀ {α : Type u_1} {m0 : MeasurableSpace α} [ins
t : TopologicalSpace α] {μ : MeasureTheory.Measure α}   [MeasureTheory.IsFiniteM
easureOnCompac…
· 使用定理 `isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure`：∀ {α : Type u_1} [i
nst : TopologicalSpace α] {x : MeasurableSpace α} {μ : MeasureTheory.Measure α} 
  [MeasureTheory.IsLocallyFiniteMeasure μ…
· 使用定理 `CompactIccSpace.isCompact_Icc`：∀ {α : Type u_1} {inst : TopologicalSpace
 α} {inst_1 : Preorder α} [self : CompactIccSpace α] {a b : α},   IsCompact (Set
.Icc a b)
-/
theorem measure_Icc_lt_top : μ (Icc a b) < ∞ :=
  isCompact_Icc.measure_lt_top
/-
**measure_Ico_lt_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measure_Ico_lt_top : μ (Ico a b) < ∞
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.Ico_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ico b a ⊆ Set.Icc b a
· 使用定理 `measure_Icc_lt_top`：measure_Icc_lt_top : μ (Icc a b) < ∞
-/
theorem measure_Ico_lt_top : μ (Ico a b) < ∞ :=
  (measure_mono Ico_subset_Icc_self).trans_lt measure_Icc_lt_top
/-
**measure_Ioc_lt_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measure_Ioc_lt_top : μ (Ioc a b) < ∞
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.Ioc_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc a b ⊆ Set.Icc a b
· 使用定理 `measure_Icc_lt_top`：measure_Icc_lt_top : μ (Icc a b) < ∞
-/
theorem measure_Ioc_lt_top : μ (Ioc a b) < ∞ :=
  (measure_mono Ioc_subset_Icc_self).trans_lt measure_Icc_lt_top
/-
**measure_Ioo_lt_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measure_Ioo_lt_top : μ (Ioo a b) < ∞
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.Ioo_subset_Icc_self`：Ioo_subset_Icc_self : Ioo a b subseteq Icc a b
· 使用定理 `measure_Icc_lt_top`：measure_Icc_lt_top : μ (Icc a b) < ∞
-/
theorem measure_Ioo_lt_top : μ (Ioo a b) < ∞ :=
  (measure_mono Ioo_subset_Icc_self).trans_lt measure_Icc_lt_top

end MeasureIxx

