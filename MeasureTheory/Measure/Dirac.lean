/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
public import Mathlib.MeasureTheory.Measure.MutuallySingular
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

/-!
# Dirac measure

In this file we define the Dirac measure `MeasureTheory.Measure.dirac a`
and prove some basic facts about it.
-/

@[expose] public section

open Function Set
open scoped ENNReal NNReal

noncomputable section

variable {α β δ : Type*} [MeasurableSpace α] [MeasurableSpace β] {s : Set α} {a : α}

namespace MeasureTheory

namespace Measure

/-- The dirac measure. -/
/-
**MeasureTheory.Measure.dirac** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：dirac (a : α) : Measure α
参数：a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The dirac measure.
-/
def dirac (a : α) : Measure α := (OuterMeasure.dirac a).toMeasure (by simp)
/-
**MeasureTheory.Measure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MeasureSpace PUnit :=
  ⟨dirac PUnit.unit⟩
/-
**MeasureTheory.Measure.le_dirac_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
Measure`。
形式化陈述：le_dirac_apply {a} : s.indicator 1 a <= dirac a s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.le_toMeasure_apply`：le_toMeasure_apply (m : OuterMeasure α
) (h : ms <= m.caratheodory) (s : Set α) : m s <= m.toMeasure h s
· 使用定理 `MeasureTheory.OuterMeasure.dirac_apply`：dirac_apply (a : α) (s : Set α) 
: dirac a s = indicator s (fun _ => 1) a
-/
theorem le_dirac_apply {a} : s.indicator 1 a ≤ dirac a s :=
  OuterMeasure.dirac_apply a s ▸ le_toMeasure_apply _ _ _

@[simp]
/-
**MeasureTheory.Measure.dirac_apply'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Me
asure`。
形式化陈述：dirac_apply' (a : α) (hs : MeasurableSet s) : dirac a s = s.indicator 1 a
参数：a : α；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.toMeasure_apply`：toMeasure_apply (m : OuterMeasure α) (h :
 ms <= m.caratheodory) {s : Set α} (hs : MeasurableSet s) : m.toMeasure h s = m 
s
-/
theorem dirac_apply' (a : α) (hs : MeasurableSet s) : dirac a s = s.indicator 1 a :=
  toMeasure_apply _ _ hs
/-
**MeasureTheory.Measure.dirac_apply_eq_zero_or_one** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.Measure`。
形式化陈述：dirac_apply_eq_zero_or_one : dirac a s = 0 ∨ dirac a s = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.measure_toMeasurable`：measure_toMeasurable (s : Set α) : μ
 (toMeasurable μ s) = μ s
· 使用定理 `MeasureTheory.Measure.dirac_apply'`：dirac_apply' (a : α) (hs : Measurabl
eSet s) : dirac a s = s.indicator 1 a
· 使用定理 `MeasureTheory.measurableSet_toMeasurable`：measurableSet_toMeasurable (μ 
: Measure α) (s : Set α) : MeasurableSet (toMeasurable μ s)
· 使用定理 `Set.indicator.eq_1`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] (s :
 Set α) (f : α → M) (x : α),   s.indicator f x = if x ∈ s then f x else 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Decidable.of_not_not`：∀ {p : Prop} [Decidable p], ¬¬p → p
-/
theorem dirac_apply_eq_zero_or_one :
    dirac a s = 0 ∨ dirac a s = 1 := by
  rw [← measure_toMeasurable s, dirac_apply' a (measurableSet_toMeasurable ..), indicator]
  simp only [Pi.one_apply, ite_eq_right_iff, one_ne_zero, imp_false, ite_eq_left_iff, zero_ne_one,
    not_not]
  tauto

@[simp]
/-
**MeasureTheory.Measure.dirac_apply_ne_zero_iff_eq_one** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.Measure`。
形式化陈述：dirac_apply_ne_zero_iff_eq_one : dirac a s != 0 ↔ dirac a s = 1 where mp
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `MeasureTheory.Measure.dirac_apply_eq_zero_or_one`：dirac_apply_eq_zero_or
_one : dirac a s = 0 ∨ dirac a s = 1
· 使用引理 `ne_zero_of_eq_one`：ne_zero_of_eq_one [One α] [NeZero (1 : α)] {a : α} (h
 : a = 1) : a != 0
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
-/
theorem dirac_apply_ne_zero_iff_eq_one :
    dirac a s ≠ 0 ↔ dirac a s = 1 where
  mp := dirac_apply_eq_zero_or_one.resolve_left
  mpr := ne_zero_of_eq_one

@[simp]
/-
**MeasureTheory.Measure.dirac_apply_ne_one_iff_eq_zero** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.Measure`。
形式化陈述：dirac_apply_ne_one_iff_eq_zero : dirac a s != 1 ↔ dirac a s = 0 where mp
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `MeasureTheory.Measure.dirac_apply_eq_zero_or_one`：dirac_apply_eq_zero_or
_one : dirac a s = 0 ∨ dirac a s = 1
· 使用定理 `zero_ne_one`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 0 ≠ 1
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem dirac_apply_ne_one_iff_eq_zero :
    dirac a s ≠ 1 ↔ dirac a s = 0 where
  mp := dirac_apply_eq_zero_or_one.resolve_right
  mpr h := h ▸ zero_ne_one

@[simp]
/-
**MeasureTheory.Measure.dirac_apply_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.Measure`。
形式化陈述：dirac_apply_of_mem {a : α} (h : a in s) : dirac a s = 1
参数：h : a in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.dirac_apply'`：dirac_apply' (a : α) (hs : Measurabl
eSet s) : dirac a s = s.indicator 1 a
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `trivial`：True
· 使用定理 `MeasureTheory.Measure.le_dirac_apply`：le_dirac_apply {a} : s.indicator 1
 a <= dirac a s
-/
theorem dirac_apply_of_mem {a : α} (h : a ∈ s) : dirac a s = 1 := by
  have : ∀ t : Set α, a ∈ t → t.indicator (1 : α → ℝ≥0∞) a = 1 := fun t ht => indicator_of_mem ht 1
  refine le_antisymm (this univ trivial ▸ ?_) (this s h ▸ le_dirac_apply)
  rw [← dirac_apply' a MeasurableSet.univ]
  exact measure_mono (subset_univ s)

@[simp]
/-
**MeasureTheory.Measure.dirac_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Mea
sure`。
形式化陈述：dirac_apply [MeasurableSingletonClass α] (a : α) (s : Set α) : dirac a s =
 s.indicator 1 a
参数：a : α；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.dirac_apply_of_mem`：dirac_apply_of_mem {a : α} (h 
: a in s) : dirac a s = 1
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用引理 `Pi.one_apply`：one_apply (i : ι) : (1 : forall i, M i) i = 1
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.subset_compl_comm`：subset_compl_comm : s subseteq tᶜ ↔ t subseteq sᶜ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.dirac_apply'`：dirac_apply' (a : α) (hs : Measurabl
eSet s) : dirac a s = s.indicator 1 a
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `MeasurableSingletonClass.measurableSet_singleton`：∀ {α : Type u_7} {inst
 : MeasurableSpace α} [self : MeasurableSingletonClass α] (x : α), MeasurableSet
 {x}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem dirac_apply [MeasurableSingletonClass α] (a : α) (s : Set α) :
    dirac a s = s.indicator 1 a := by
  by_cases h : a ∈ s; · rw [dirac_apply_of_mem h, indicator_of_mem h, Pi.one_apply]
  rw [indicator_of_notMem h, ← nonpos_iff_eq_zero]
  calc
    dirac a s ≤ dirac a {a}ᶜ := measure_mono (subset_compl_comm.1 <| singleton_subset_iff.2 h)
    _ = 0 := by simp [dirac_apply' _ (measurableSet_singleton _).compl]
/-
**MeasureTheory.Measure.dirac_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.M
easure`。
形式化陈述：∀ {α : Type u_1} [inst : MeasurableSpace α] {a : α}, MeasureTheory.Measure
.dirac a ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `MeasureTheory.Measure.dirac_apply_of_mem`：dirac_apply_of_mem {a : α} (h 
: a in s) : dirac a s = 1
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
@[simp] lemma dirac_ne_zero : dirac a ≠ 0 :=
  fun h ↦ by simpa [h] using dirac_apply_of_mem (mem_univ a)

@[simp]
/-
**MeasureTheory.Measure.map_dirac'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Meas
ure`。
形式化陈述：map_dirac' {f : α -> β} (hf : Measurable f) (a : α) : (dirac a).map f = di
rac (f a)
参数：hf : Measurable f；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `MeasureTheory.Measure.dirac_apply'`：dirac_apply' (a : α) (hs : Measurabl
eSet s) : dirac a s = s.indicator 1 a
· 使用定理 `Set.indicator_apply`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] (s 
: Set α) (f : α → M) (a : α) [inst_1 : Decidable (a ∈ s)],   s.indicator f a = i
f a ∈ s t…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_dirac' {f : α → β} (hf : Measurable f) (a : α) : (dirac a).map f = dirac (f a) := by
  classical
  exact ext fun s hs => by simp [hs, map_apply hf hs, hf hs, indicator_apply]

@[simp]
/-
**MeasureTheory.Measure.map_const** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Measu
re`。
形式化陈述：map_const (μ : Measure α) (c : β) : μ.map (fun _ => c) = (μ Set.univ) • di
rac c
参数：μ : Measure α；c : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.dirac_apply'`：dirac_apply' (a : α) (hs : Measurabl
eSet s) : dirac a s = s.indicator 1 a
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `Set.preimage_const`：preimage_const (b : β) (s : Set β) [Decidable (b in 
s)] : (fun _ : α => b) ⁻¹' s = if b in s then univ else ∅
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.indicator_eq_one_iff_mem`：indicator_eq_one_iff_mem : indicator s 1 i
 = (1 : M₀) ↔ i in s
· 使用定理 `ENNReal.instNontrivial`：Nontrivial ENNReal
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用引理 `Set.indicator_eq_zero_iff_notMem`：indicator_eq_zero_iff_notMem : indicat
or s 1 i = (0 : M₀) ↔ i ∉ s
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
lemma map_const (μ : Measure α) (c : β) : μ.map (fun _ ↦ c) = (μ Set.univ) • dirac c := by
  ext s hs
  simp only [Measure.coe_smul, Pi.smul_apply,
    dirac_apply' _ hs, smul_eq_mul]
  classical
  rw [Measure.map_apply measurable_const hs, Set.preimage_const]
  by_cases hsc : c ∈ s
  · rw [(Set.indicator_eq_one_iff_mem _).mpr hsc, mul_one, if_pos hsc]
  · rw [if_neg hsc, (Set.indicator_eq_zero_iff_notMem _).mpr hsc, measure_empty, mul_zero]

@[simp]
/-
**MeasureTheory.Measure.restrict_singleton** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.Measure`。
形式化陈述：restrict_singleton (μ : Measure α) (a : α) : μ.restrict {a} = μ {a} • dira
c a
参数：μ : Measure α；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `MeasureTheory.Measure.dirac_apply'`：dirac_apply' (a : α) (hs : Measurabl
eSet s) : dirac a s = s.indicator 1 a
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.inter_singleton_eq_empty`：inter_singleton_eq_empty : s inter {a} = ∅
 ↔ a ∉ s
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
theorem restrict_singleton (μ : Measure α) (a : α) : μ.restrict {a} = μ {a} • dirac a := by
  ext1 s hs
  by_cases ha : a ∈ s
  · have : s ∩ {a} = {a} := by simpa
    simp [*]
  · have : s ∩ {a} = ∅ := inter_singleton_eq_empty.2 ha
    simp [*]

/-- Two measures on a countable space are equal if they agree on singletons. -/
/-
**MeasureTheory.Measure.ext_of_singleton** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.Measure`。
形式化陈述：ext_of_singleton [Countable α] {μ ν : Measure α} (h : forall a, μ {a} = ν 
{a}) : μ = ν
参数：h : forall a, μ {a} = ν {a}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext_of_sUnion_eq_univ`：∀ {α : Type u_2} {m0 : Meas
urableSpace α} {μ ν : MeasureTheory.Measure α} {S : Set (Set α)},   S.Countable 
→ ⋃₀ S = Set.univ → (∀ s ∈ S, μ.r…
· 使用定理 `Set.countable_range`：countable_range [Countable ι] (f : ι -> β) : (range
 f).Countable
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.Measure.restrict_singleton`：restrict_singleton (μ : Measur
e α) (a : α) : μ.restrict {a} = μ {a} • dirac a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
Two measures on a countable space are equal if they agree on singletons.
-/
theorem ext_of_singleton [Countable α] {μ ν : Measure α} (h : ∀ a, μ {a} = ν {a}) : μ = ν :=
  ext_of_sUnion_eq_univ (countable_range singleton) (by aesop) (by simp_all)

/-- Two measures on a countable space are equal if and only if they agree on singletons. -/
/-
**MeasureTheory.Measure.ext_iff_singleton** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.Measure`。
形式化陈述：ext_iff_singleton [Countable α] {μ ν : Measure α} : μ = ν ↔ forall a, μ {a
} = ν {a}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext_of_singleton`：ext_of_singleton [Countable α] {
μ ν : Measure α} (h : forall a, μ {a} = ν {a}) : μ = ν

--- 原说明 ---
Two measures on a countable space are equal if and only if they agree on singlet
ons.
-/
theorem ext_iff_singleton [Countable α] {μ ν : Measure α} : μ = ν ↔ ∀ a, μ {a} = ν {a} :=
  ⟨fun h _ ↦ h ▸ rfl, ext_of_singleton⟩
/-
**MeasureTheory.Measure._root_.MeasureTheory.ext_iff_measureReal_singleton** 是 M
athlib 中的一个定理，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasureTheory.ext_iff_measureReal_singleton [Countable α]
    {μ1 μ2 : Measure α} [SigmaFinite μ1] [SigmaFinite μ2] :
    μ1 = μ2 ↔ ∀ x, μ1.real {x} = μ2.real {x} := by
  rw [Measure.ext_iff_singleton]
  congr! with x
  rw [measureReal_def, measureReal_def, ENNReal.toReal_eq_toReal_iff]
  simp [measure_singleton_lt_top, ne_of_lt]

alias ⟨_, ext_of_measureReal_singleton⟩ := MeasureTheory.ext_iff_measureReal_singleton

/-- If `f` is a map with countable codomain, then `μ.map f` is a sum of Dirac measures. -/
/-
**MeasureTheory.Measure.map_eq_sum** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Meas
ure`。
形式化陈述：map_eq_sum [Countable β] [MeasurableSingletonClass β] (μ : Measure α) (f :
 α -> β) (hf : Measurable f) : μ.map f = sum fun b : β => μ (f ⁻¹' {b}) • dirac 
b
参数：μ : Measure α；f : α -> β；hf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasurableSingletonClass.measurableSet_singleton`：∀ {α : Type u_7} {inst
 : MeasurableSpace α} [self : MeasurableSingletonClass α] (x : α), MeasurableSet
 {x}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.tsum_measure_preimage_singleton`：tsum_measure_preimage_sin
gleton {s : Set β} (hs : s.Countable) {f : α -> β} (hf : forall y in s, Measurab
leSet (f ⁻¹' {y})) : (∑' b : s, μ (…
· 使用定理 `Set.to_countable`：to_countable (s : Set α) [Countable s] : s.Countable
· 使用定理 `SetCoe.countable`：∀ {α : Type u} [Countable α] (s : Set α), Countable ↑s
· 使用定理 `tsum_subtype`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [
inst_1 : TopologicalSpace α] (s : Set β) (f : β → α),   ∑' (x : ↑s), f ↑x = ∑' (
x …
· 使用定理 `MeasureTheory.Measure.sum_apply`：sum_apply (f : ι -> Measure α) {s : Set
 α} (hs : MeasurableSet s) : sum f s = ∑' i, f i s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.Measure.dirac_apply'`：dirac_apply' (a : α) (hs : Measurabl
eSet s) : dirac a s = s.indicator 1 a
· 使用引理 `Set.indicator_mul_right`：indicator_mul_right (s : Set ι) (f g : ι -> M₀)
 : indicator s (fun j => f j * g j) i = f i * indicator s g i
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `f` is a map with countable codomain, then `μ.map f` is a sum of Dirac measur
es.
-/
theorem map_eq_sum [Countable β] [MeasurableSingletonClass β] (μ : Measure α) (f : α → β)
    (hf : Measurable f) : μ.map f = sum fun b : β => μ (f ⁻¹' {b}) • dirac b := by
  ext s
  have : ∀ y ∈ s, MeasurableSet (f ⁻¹' {y}) := fun y _ => hf (measurableSet_singleton _)
  simp [← tsum_measure_preimage_singleton (to_countable s) this, *,
    tsum_subtype s fun b => μ (f ⁻¹' {b}), ← indicator_mul_right s fun b => μ (f ⁻¹' {b})]

/-- A measure on a countable type is a sum of Dirac measures. -/
@[simp]
/-
**MeasureTheory.Measure.sum_smul_dirac** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
Measure`。
形式化陈述：sum_smul_dirac [Countable α] [MeasurableSingletonClass α] (μ : Measure α) 
: (sum fun a => μ {a} • dirac a) = μ
参数：μ : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_id`：map_id : map id μ = μ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.map_eq_sum`：map_eq_sum [Countable β] [MeasurableSi
ngletonClass β] (μ : Measure α) (f : α -> β) (hf : Measurable f) : μ.map f = sum
 fun b : β => μ (f ⁻¹'…
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)

--- 原说明 ---
A measure on a countable type is a sum of Dirac measures.
-/
theorem sum_smul_dirac [Countable α] [MeasurableSingletonClass α] (μ : Measure α) :
    (sum fun a => μ {a} • dirac a) = μ := by simpa using (map_eq_sum μ id measurable_id).symm

/-- The sum of scaled Dirac measures applied to a singleton is the coefficient of that singleton. -/
/-
**MeasureTheory.Measure.sum_smul_dirac_singleton** 是 Mathlib 中的一个引理，位于命名空间 `Meas
ureTheory.Measure`。
形式化陈述：sum_smul_dirac_singleton [MeasurableSingletonClass α] {f : α -> Real>=0∞} 
{a : α} : sum (fun b : α => f b • dirac b) {a} = f a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.sum_apply`：sum_apply (f : ι -> Measure α) {s : Set
 α} (hs : MeasurableSet s) : sum f s = ∑' i, f i s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.Measure.dirac_apply'`：dirac_apply' (a : α) (hs : Measurabl
eSet s) : dirac a s = s.indicator 1 a
· 使用定理 `tsum_eq_single`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   [L.LeAtTop] {f : β → α}
 (b …
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a

--- 原说明 ---
The sum of scaled Dirac measures applied to a singleton is the coefficient of th
at singleton.
-/
lemma sum_smul_dirac_singleton [MeasurableSingletonClass α] {f : α → ℝ≥0∞} {a : α} :
    sum (fun b : α ↦ f b • dirac b) {a} = f a := by
  simp +contextual [tsum_eq_single a]

/-- A measure on a countable type is a sum of Dirac measures.
If `α` has measurable singletons, `sum_smul_dirac` gives a simpler sum. -/
/-
**MeasureTheory.Measure.exists_sum_smul_dirac** 是 Mathlib 中的一个引理，位于命名空间 `Measure
Theory.Measure`。
形式化陈述：exists_sum_smul_dirac [Countable α] (μ : Measure α) : exists s : Set α, μ 
= Measure.sum (fun x : s => μ (measurableAtom x) • dirac (x : α))
参数：μ : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mem_measurableAtom_self`：∀ {β : Type u_2} [inst : MeasurableSpace β] (x 
: β), x ∈ measurableAtom x
· 使用定理 `Set.Nonempty.some_mem`：∀ {α : Type u} {s : Set α} (h : s.Nonempty), h.so
me ∈ s
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `MeasureTheory.ext_of_measurableAtoms`：ext_of_measurableAtoms [Countable 
α] {μ ν : Measure α} (h : forall x, μ (measurableAtom x) = ν (measurableAtom x))
 : μ = ν
· 使用定理 `MeasureTheory.Measure.sum_apply`：sum_apply (f : ι -> Measure α) {s : Set
 α} (hs : MeasurableSet s) : sum f s = ∑' i, f i s
· 使用引理 `MeasurableSet.measurableAtom_of_countable`：MeasurableSet.measurableAtom_
of_countable [Countable β] (x : β) : MeasurableSet (measurableAtom x)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.Measure.dirac_apply'`：dirac_apply' (a : α) (hs : Measurabl
eSet s) : dirac a s = s.indicator 1 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `tsum_eq_single`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   [L.LeAtTop] {f : β → α}
 (b …
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `ENNReal.instNoZeroDivisors`：NoZeroDivisors ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用引理 `measurableAtom_eq_of_mem`：measurableAtom_eq_of_mem {x y : β} (hx : x in 
measurableAtom y) : measurableAtom x = measurableAtom y
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'

--- 原说明 ---
A measure on a countable type is a sum of Dirac measures.
If `α` has measurable singletons, `sum_smul_dirac` gives a simpler sum.
-/
lemma exists_sum_smul_dirac [Countable α] (μ : Measure α) :
    ∃ s : Set α, μ = Measure.sum (fun x : s ↦ μ (measurableAtom x) • dirac (x : α)) := by
  let measurableAtoms := measurableAtom '' (Set.univ : Set α)
  have h_nonempty (s : measurableAtoms) : Set.Nonempty s.1 := by
    obtain ⟨y, _, hy⟩ := s.2
    rw [← hy]
    exact ⟨y, mem_measurableAtom_self y⟩
  let points : measurableAtoms → α := fun s ↦ (h_nonempty s).some
  have h_points_mem (s : measurableAtoms) : points s ∈ s.1 := (h_nonempty s).some_mem
  refine ⟨Set.range points, ext_of_measurableAtoms fun x ↦ ?_⟩
  rw [sum_apply _ (MeasurableSet.measurableAtom_of_countable x)]
  simp only [Measure.smul_apply, smul_eq_mul]
  simp_rw [dirac_apply' _ (MeasurableSet.measurableAtom_of_countable x)]
  rw [tsum_eq_single ⟨points ⟨measurableAtom x, by simp [measurableAtoms]⟩, by simp⟩]
  · rw [indicator_of_mem]
    · simp only [Pi.one_apply, mul_one]
      congr 1
      refine (measurableAtom_eq_of_mem ?_).symm
      convert! h_points_mem _
      simp
    · convert! h_points_mem _
      simp
  · simp only [ne_eq, mul_eq_zero, indicator_apply_eq_zero, Pi.one_apply, one_ne_zero, imp_false,
      Subtype.forall, Set.mem_range, Subtype.exists, Subtype.mk.injEq, forall_exists_index]
    refine fun y s hs hsy hyx ↦ .inr fun hyx' ↦ hyx ?_
    rw [← hsy]
    congr
    have h1 : measurableAtom y = measurableAtom x := measurableAtom_eq_of_mem hyx'
    have h2 : measurableAtom y = s := by
      specialize h_points_mem ⟨s, hs⟩
      obtain ⟨z, _, hz⟩ := hs
      simp only at h_points_mem
      rw [← hz, ← hsy]
      refine measurableAtom_eq_of_mem ?_
      convert! h_points_mem
    rw [← h2, h1]

/-- Given that `α` is a countable, measurable space with all singleton sets measurable,
write the measure of a set `s` as the sum of the measure of `{x}` for all `x ∈ s`. -/
/-
**MeasureTheory.Measure.tsum_indicator_apply_singleton** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.Measure`。
形式化陈述：tsum_indicator_apply_singleton [Countable α] [MeasurableSingletonClass α] 
(μ : Measure α) (s : Set α) (hs : MeasurableSet s) : (∑' x : α, s.indicator (fun
 x => μ {x}) x) = μ s
参数：μ : Measure α；s : Set α；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
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
· 使用定理 `Set.indicator_apply`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] (s 
: Set α) (f : α → M) (a : α) [inst_1 : Decidable (a ∈ s)],   s.indicator f a = i
f a ∈ s t…
· 使用定理 `MeasureTheory.Measure.sum_apply`：sum_apply (f : ι -> Measure α) {s : Set
 α} (hs : MeasurableSet s) : sum f s = ∑' i, f i s
· 使用定理 `MeasureTheory.Measure.dirac_apply`：dirac_apply [MeasurableSingletonClass
 α] (a : α) (s : Set α) : dirac a s = s.indicator 1 a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.Measure.sum_smul_dirac`：sum_smul_dirac [Countable α] [Meas
urableSingletonClass α] (μ : Measure α) : (sum fun a => μ {a} • dirac a) = μ

--- 原说明 ---
Given that `α` is a countable, measurable space with all singleton sets measurab
le,
write the measure of a set `s` as the sum of the measure of `{x}` for all `x ∈ s
`.
-/
theorem tsum_indicator_apply_singleton [Countable α] [MeasurableSingletonClass α] (μ : Measure α)
    (s : Set α) (hs : MeasurableSet s) : (∑' x : α, s.indicator (fun x => μ {x}) x) = μ s := by
  classical
  calc
    (∑' x : α, s.indicator (fun x => μ {x}) x) =
      Measure.sum (fun a => μ {a} • Measure.dirac a) s := by
      simp only [Measure.sum_apply _ hs, Measure.smul_apply, smul_eq_mul, Measure.dirac_apply,
        Set.indicator_apply, mul_ite, Pi.one_apply, mul_one, mul_zero]
    _ = μ s := by rw [μ.sum_smul_dirac]

end Measure

open Measure

/-
**MeasureTheory.mem_ae_dirac_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：mem_ae_dirac_iff {a : α} (hs : MeasurableSet s) : s in ae (dirac a) ↔ a in
 s
参数：hs : MeasurableSet s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.dirac_apply'`：dirac_apply' (a : α) (hs : Measurabl
eSet s) : dirac a s = s.indicator 1 a
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
-/
theorem mem_ae_dirac_iff {a : α} (hs : MeasurableSet s) : s ∈ ae (dirac a) ↔ a ∈ s := by
  by_cases a ∈ s <;> simp [mem_ae_iff, dirac_apply', hs.compl, *]
/-
**MeasureTheory.ae_dirac_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：∀ {α : Type u_1} [inst : MeasurableSpace α] {a : α} {p : α → Prop},   Meas
urableSet {x | p x} → ((∀ᵐ (x : α) ∂MeasureTheory.Measure.dirac a, p x) ↔ p a)
参数：(∀ᵐ (x : α) ∂MeasureTheory.Measure.dirac a, p x) ↔ p a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.mem_ae_dirac_iff`：mem_ae_dirac_iff {a : α} (hs : Measurabl
eSet s) : s in ae (dirac a) ↔ a in s
-/
@[simp] theorem ae_dirac_iff {a : α} {p : α → Prop} (hp : MeasurableSet { x | p x }) :
    (∀ᵐ x ∂dirac a, p x) ↔ p a :=
  mem_ae_dirac_iff hp

@[simp]
/-
**MeasureTheory.ae_dirac_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_dirac_eq [MeasurableSingletonClass α] (a : α) : ae (dirac a) = pure a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.ext`：∀ {α : Type u_1} {f g : Filter α}, (∀ (s : Set α), s ∈ f ↔ s
 ∈ g) → f = g
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.dirac_apply`：dirac_apply [MeasurableSingletonClass
 α] (a : α) (s : Set α) : dirac a s = s.indicator 1 a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ae_dirac_eq [MeasurableSingletonClass α] (a : α) : ae (dirac a) = pure a := by
  ext s
  simp [mem_ae_iff, imp_false]
/-
**MeasureTheory.ae_eq_dirac'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_eq_dirac' [MeasurableSingletonClass β] {a : α} {f : α -> β} (hf : Measu
rable f) : f =ᵐ[dirac a] const α (f a)
参数：hf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_dirac_iff`：∀ {α : Type u_1} [inst : MeasurableSpace α] 
{a : α} {p : α → Prop},   MeasurableSet {x | p x} → ((∀ᵐ (x : α) ∂MeasureTheory.
Measure.dirac a,…
· 使用定理 `MeasurableSingletonClass.measurableSet_singleton`：∀ {α : Type u_7} {inst
 : MeasurableSpace α} [self : MeasurableSingletonClass α] (x : α), MeasurableSet
 {x}
-/
theorem ae_eq_dirac' [MeasurableSingletonClass β] {a : α} {f : α → β} (hf : Measurable f) :
    f =ᵐ[dirac a] const α (f a) :=
  (ae_dirac_iff <| show MeasurableSet (f ⁻¹' {f a}) from hf <| measurableSet_singleton _).2 rfl
/-
**MeasureTheory.ae_eq_dirac** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_eq_dirac [MeasurableSingletonClass α] {a : α} (f : α -> δ) : f =ᵐ[dirac
 a] const α (f a)
参数：f : α -> δ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ae_dirac_eq`：ae_dirac_eq [MeasurableSingletonClass α] (a :
 α) : ae (dirac a) = pure a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ae_eq_dirac [MeasurableSingletonClass α] {a : α} (f : α → δ) :
    f =ᵐ[dirac a] const α (f a) := by simp [Filter.EventuallyEq]

@[fun_prop]
/-
**MeasureTheory.aemeasurable_dirac** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：aemeasurable_dirac [MeasurableSingletonClass α] {a : α} {f : α -> β} : AEM
easurable f (Measure.dirac a)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `MeasureTheory.ae_eq_dirac`：ae_eq_dirac [MeasurableSingletonClass α] {a :
 α} (f : α -> δ) : f =ᵐ[dirac a] const α (f a)
-/
lemma aemeasurable_dirac [MeasurableSingletonClass α] {a : α} {f : α → β} :
    AEMeasurable f (Measure.dirac a) :=
  ⟨fun _ ↦ f a, measurable_const, ae_eq_dirac f⟩

@[simp]
/-
**MeasureTheory.Measure.map_dirac** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measu
re`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : Measu
rableSpace β] [MeasurableSingletonClass α]   [MeasurableSingletonClass β] {f : α
 → β} (a : α),   MeasureTheory.Measure.map f (MeasureTheory.Measure.dirac a) = M
easureTheory.Measure.dirac (f a)
参数：a : α；MeasureTheory.Measure.dirac a；f a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_apply_of_aemeasurable`：map_apply_of_aemeasurab
le (hf : AEMeasurable f μ) {s : Set β} (hs : MeasurableSet s) : μ.map f s = μ (f
 ⁻¹' s)
· 使用引理 `MeasureTheory.aemeasurable_dirac`：aemeasurable_dirac [MeasurableSingleto
nClass α] {a : α} {f : α -> β} : AEMeasurable f (Measure.dirac a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.Measure.dirac_apply`：dirac_apply [MeasurableSingletonClass
 α] (a : α) (s : Set α) : dirac a s = s.indicator 1 a
· 使用定理 `Set.indicator_apply`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] (s 
: Set α) (f : α → M) (a : α) [inst_1 : Decidable (a ∈ s)],   s.indicator f a = i
f a ∈ s t…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Measure.map_dirac [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    {f : α → β} (a : α) : (dirac a).map f = dirac (f a) := by
  classical
  ext s hs
  rw [map_apply_of_aemeasurable (by fun_prop) hs]
  simp [indicator_apply]
/-
**MeasureTheory.Measure.dirac.isProbabilityMeasure** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.Measure.dirac`。
形式化陈述：∀ {α : Type u_1} [inst : MeasurableSpace α] {x : α}, MeasureTheory.IsProba
bilityMeasure (MeasureTheory.Measure.dirac x)
参数：MeasureTheory.Measure.dirac x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.dirac_apply_of_mem`：dirac_apply_of_mem {a : α} (h 
: a in s) : dirac a s = 1
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
instance Measure.dirac.isProbabilityMeasure {x : α} : IsProbabilityMeasure (dirac x) :=
  ⟨dirac_apply_of_mem <| mem_univ x⟩
/-
**MeasureTheory._root_.HasSum.isProbabilityMeasure_sum_dirac_ennreal** 是 Mathlib
 中的一个引理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.HasSum.isProbabilityMeasure_sum_dirac_ennreal {ι : Type*} {mδ : MeasurableSpace δ}
    {c : ι → ℝ≥0∞} {d : ι → δ} (h : HasSum c 1) :
    IsProbabilityMeasure (Measure.sum fun i ↦ c i • .dirac (d i)) where
  measure_univ := by simp [h.tsum_eq]
/-
**MeasureTheory._root_.HasSum.isProbabilityMeasure_sum_dirac_nnreal** 是 Mathlib 
中的一个引理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.HasSum.isProbabilityMeasure_sum_dirac_nnreal {ι : Type*} {mδ : MeasurableSpace δ}
    {c : ι → ℝ≥0} {d : ι → δ} (h : HasSum c 1) :
    IsProbabilityMeasure (Measure.sum fun i ↦ c i • .dirac (d i)) :=
  (ENNReal.hasSum_coe.2 h).isProbabilityMeasure_sum_dirac_ennreal
/-
**MeasureTheory._root_.HasSum.isProbabilityMeasure_sum_dirac** 是 Mathlib 中的一个引理，
位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.HasSum.isProbabilityMeasure_sum_dirac {ι : Type*} {mδ : MeasurableSpace δ}
    {c : ι → ℝ} {d : ι → δ} (h1 : ∀ i, 0 ≤ c i) (h2 : HasSum c 1) :
    IsProbabilityMeasure (Measure.sum fun i ↦ ENNReal.ofReal (c i) • .dirac (d i)) :=
  HasSum.isProbabilityMeasure_sum_dirac_nnreal (by simpa using h2.toNNReal h1)
/-
**MeasureTheory.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [hα : Nonempty α] : Nonempty {μ : Measure α // IsProbabilityMeasure μ} :=
  ⟨Measure.dirac hα.some, inferInstance⟩

/-! Extra instances to short-circuit type class resolution -/

/-
**MeasureTheory.Measure.dirac.instIsFiniteMeasure** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.Measure.dirac`。
形式化陈述：∀ {α : Type u_1} [inst : MeasurableSpace α] {a : α}, MeasureTheory.IsFinit
eMeasure (MeasureTheory.Measure.dirac a)
参数：MeasureTheory.Measure.dirac a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `MeasureTheory.Measure.dirac.isProbabilityMeasure`：∀ {α : Type u_1} [inst
 : MeasurableSpace α] {x : α}, MeasureTheory.IsProbabilityMeasure (MeasureTheory
.Measure.dirac x)

--- 原说明 ---
Extra instances to short-circuit type class resolution
-/
instance Measure.dirac.instIsFiniteMeasure {a : α} : IsFiniteMeasure (dirac a) := inferInstance
/-
**MeasureTheory.Measure.dirac.instSigmaFinite** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.Measure.dirac`。
形式化陈述：∀ {α : Type u_1} [inst : MeasurableSpace α] {a : α}, MeasureTheory.SigmaFi
nite (MeasureTheory.Measure.dirac a)
参数：MeasureTheory.Measure.dirac a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasureTheory.Measure.dirac.instIsFiniteMeasure`：∀ {α : Type u_1} [inst 
: MeasurableSpace α] {a : α}, MeasureTheory.IsFiniteMeasure (MeasureTheory.Measu
re.dirac a)
-/
instance Measure.dirac.instSigmaFinite {a : α} : SigmaFinite (dirac a) := inferInstance
/-
**MeasureTheory.dirac_eq_one_iff_mem** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：dirac_eq_one_iff_mem (hs : MeasurableSet s) : dirac a s = 1 ↔ a in s
参数：hs : MeasurableSet s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.prob_compl_eq_zero_iff`：prob_compl_eq_zero_iff (hs : Measu
rableSet s) : μ sᶜ = 0 ↔ μ s = 1
· 使用定理 `MeasureTheory.Measure.dirac.isProbabilityMeasure`：∀ {α : Type u_1} [inst
 : MeasurableSpace α] {x : α}, MeasureTheory.IsProbabilityMeasure (MeasureTheory
.Measure.dirac x)
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.mem_ae_iff`：mem_ae_iff {s : Set α} : s in ae μ ↔ μ sᶜ = 0
· 使用定理 `MeasureTheory.mem_ae_dirac_iff`：mem_ae_dirac_iff {a : α} (hs : Measurabl
eSet s) : s in ae (dirac a) ↔ a in s
-/
theorem dirac_eq_one_iff_mem (hs : MeasurableSet s) : dirac a s = 1 ↔ a ∈ s := by
  rw [← prob_compl_eq_zero_iff hs, ← mem_ae_iff]
  apply mem_ae_dirac_iff hs
/-
**MeasureTheory.dirac_eq_zero_iff_not_mem** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：dirac_eq_zero_iff_not_mem (hs : MeasurableSet s) : dirac a s = 0 ↔ a ∉ s
参数：hs : MeasurableSet s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.mem_ae_iff`：mem_ae_iff {s : Set α} : s in ae μ ↔ μ sᶜ = 0
· 使用定理 `Set.notMem_compl_iff`：notMem_compl_iff {x : α} : x ∉ sᶜ ↔ x in s
· 使用定理 `MeasureTheory.mem_ae_dirac_iff`：mem_ae_dirac_iff {a : α} (hs : Measurabl
eSet s) : s in ae (dirac a) ↔ a in s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasurableSet.compl_iff`：MeasurableSet.compl_iff : MeasurableSet sᶜ ↔ Me
asurableSet s
-/
theorem dirac_eq_zero_iff_not_mem (hs : MeasurableSet s) : dirac a s = 0 ↔ a ∉ s := by
  rw [← compl_compl s, ← mem_ae_iff, notMem_compl_iff]
  apply mem_ae_dirac_iff (MeasurableSet.compl_iff.mpr hs)
/-
**MeasureTheory.restrict_dirac'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：restrict_dirac' (hs : MeasurableSet s) [Decidable (a in s)] : (Measure.dir
ac a).restrict s = if a in s then Measure.dirac a else 0
参数：hs : MeasurableSet s；a in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `MeasureTheory.Measure.restrict_eq_self_of_ae_mem`：restrict_eq_self_of_ae
_mem {_m0 : MeasurableSpace α} ⦃s : Set α⦄ ⦃μ : Measure α⦄ (hs : forallᵐ x ∂μ, x
 in s) : μ.restrict s = μ
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_dirac_iff`：∀ {α : Type u_1} [inst : MeasurableSpace α] 
{a : α} {p : α → Prop},   MeasurableSet {x | p x} → ((∀ᵐ (x : α) ∂MeasureTheory.
Measure.dirac a,…
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `MeasureTheory.Measure.restrict_eq_zero`：restrict_eq_zero : μ.restrict s 
= 0 ↔ μ s = 0
· 使用定理 `MeasureTheory.Measure.dirac_apply'`：dirac_apply' (a : α) (hs : Measurabl
eSet s) : dirac a s = s.indicator 1 a
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
-/
theorem restrict_dirac' (hs : MeasurableSet s) [Decidable (a ∈ s)] :
    (Measure.dirac a).restrict s = if a ∈ s then Measure.dirac a else 0 := by
  split_ifs with has
  · apply restrict_eq_self_of_ae_mem
    rw [ae_dirac_iff] <;> assumption
  · rw [restrict_eq_zero, dirac_apply' _ hs, indicator_of_notMem has]
/-
**MeasureTheory.restrict_dirac** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：restrict_dirac [MeasurableSingletonClass α] [Decidable (a in s)] : (Measur
e.dirac a).restrict s = if a in s then Measure.dirac a else 0
参数：a in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `MeasureTheory.Measure.restrict_eq_self_of_ae_mem`：restrict_eq_self_of_ae
_mem {_m0 : MeasurableSpace α} ⦃s : Set α⦄ ⦃μ : Measure α⦄ (hs : forallᵐ x ∂μ, x
 in s) : μ.restrict s = μ
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_dirac_eq`：ae_dirac_eq [MeasurableSingletonClass α] (a :
 α) : ae (dirac a) = pure a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `MeasureTheory.Measure.restrict_eq_zero`：restrict_eq_zero : μ.restrict s 
= 0 ↔ μ s = 0
· 使用定理 `MeasureTheory.Measure.dirac_apply`：dirac_apply [MeasurableSingletonClass
 α] (a : α) (s : Set α) : dirac a s = s.indicator 1 a
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
-/
theorem restrict_dirac [MeasurableSingletonClass α] [Decidable (a ∈ s)] :
    (Measure.dirac a).restrict s = if a ∈ s then Measure.dirac a else 0 := by
  split_ifs with has
  · apply restrict_eq_self_of_ae_mem
    rwa [ae_dirac_eq]
  · rw [restrict_eq_zero, dirac_apply, indicator_of_notMem has]
/-
**MeasureTheory.mutuallySingular_dirac** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`
。
形式化陈述：mutuallySingular_dirac [MeasurableSingletonClass α] (x : α) (μ : Measure α
) [NullSingletonClass μ] : Measure.dirac x ⟂ₘ μ
参数：x : α；μ : Measure α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用引理 `MeasurableSet.singleton`：MeasurableSet.singleton [MeasurableSpace α] [Me
asurableSingletonClass α] (a : α) : MeasurableSet {a}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.dirac_apply'`：dirac_apply' (a : α) (hs : Measurabl
eSet s) : dirac a s = s.indicator 1 a
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `MeasureTheory.NullSingletonClass.measure_singleton`：∀ {α : Type u_1} {m0
 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.NullSi
ngletonClass μ]   (x : α), μ {x} = 0
-/
lemma mutuallySingular_dirac [MeasurableSingletonClass α] (x : α) (μ : Measure α)
    [NullSingletonClass μ] :
    Measure.dirac x ⟂ₘ μ :=
  ⟨{x}ᶜ, (MeasurableSet.singleton x).compl, by simp, by simp⟩

section dirac_injective

/-- Dirac delta measures at two points are equal if every measurable set contains either both or
neither of the points. -/
/-
**MeasureTheory.dirac_eq_dirac_iff_forall_mem_iff_mem** 是 Mathlib 中的一个引理，位于命名空间 
`MeasureTheory`。
形式化陈述：dirac_eq_dirac_iff_forall_mem_iff_mem {x y : α} : Measure.dirac x = Measur
e.dirac y ↔ forall A, MeasurableSet A -> (x in A ↔ y in A)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `Eq.comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `ENNReal.instNontrivial`：Nontrivial ENNReal
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.Measure.dirac_apply'`：dirac_apply' (a : α) (hs : Measurabl
eSet s) : dirac a s = s.indicator 1 a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_iff`：∀ (p : Prop), (False ↔ p) = ¬p
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Dirac delta measures at two points are equal if every measurable set contains ei
ther both or
neither of the points.
-/
lemma dirac_eq_dirac_iff_forall_mem_iff_mem {x y : α} :
    Measure.dirac x = Measure.dirac y ↔ ∀ A, MeasurableSet A → (x ∈ A ↔ y ∈ A) := by
  constructor
  · intro h A A_mble
    have obs := congr_arg (fun μ ↦ μ A) h
    simp only [Measure.dirac_apply' _ A_mble] at obs
    by_cases x_in_A : x ∈ A
    · simpa only [x_in_A, indicator_of_mem, Pi.one_apply, true_iff, Eq.comm (a := (1 : ℝ≥0∞)),
                  indicator_eq_one_iff_mem] using obs
    · simpa only [x_in_A, indicator_of_notMem, Eq.comm (a := (0 : ℝ≥0∞)), indicator_apply_eq_zero,
                  false_iff, not_false_eq_true, Pi.one_apply, one_ne_zero, imp_false] using obs
  · intro h
    ext A A_mble
    by_cases x_in_A : x ∈ A
    · simp only [Measure.dirac_apply' _ A_mble, x_in_A, indicator_of_mem, Pi.one_apply,
                 (h A A_mble).mp x_in_A]
    · have y_notin_A : y ∉ A := by simp_all only [not_false_eq_true]
      simp only [Measure.dirac_apply' _ A_mble, x_in_A, y_notin_A,
                 not_false_eq_true, indicator_of_notMem]

/-- Dirac delta measures at two points are different if and only if there is a measurable set
containing one of the points but not the other. -/
/-
**MeasureTheory.dirac_ne_dirac_iff_exists_measurableSet** 是 Mathlib 中的一个引理，位于命名空
间 `MeasureTheory`。
形式化陈述：dirac_ne_dirac_iff_exists_measurableSet {x y : α} : Measure.dirac x != Mea
sure.dirac y ↔ exists A, MeasurableSet A ∧ x in A ∧ y ∉ A
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_iff`：∀ (p : Prop), (False ↔ p) = ¬p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasurableSet.compl_iff`：MeasurableSet.compl_iff : MeasurableSet sᶜ ↔ Me
asurableSet s

--- 原说明 ---
Dirac delta measures at two points are different if and only if there is a measu
rable set
containing one of the points but not the other.
-/
lemma dirac_ne_dirac_iff_exists_measurableSet {x y : α} :
    Measure.dirac x ≠ Measure.dirac y ↔ ∃ A, MeasurableSet A ∧ x ∈ A ∧ y ∉ A := by
  apply not_iff_not.mp
  simp only [ne_eq, not_not, not_exists, not_and, dirac_eq_dirac_iff_forall_mem_iff_mem]
  refine ⟨fun h A A_mble ↦ by simp only [h A A_mble, imp_self], fun h A A_mble ↦ ?_⟩
  by_cases x_in_A : x ∈ A
  · simp only [x_in_A, h A A_mble x_in_A]
  · simpa only [x_in_A, false_iff] using! h Aᶜ (MeasurableSet.compl_iff.mpr A_mble) x_in_A

open MeasurableSpace
/-- Dirac delta measures at two different points are different, assuming the measurable space
separates points. -/
/-
**MeasureTheory.dirac_ne_dirac** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：dirac_ne_dirac [SeparatesPoints α] {x y : α} (x_ne_y : x != y) : Measure.d
irac x != Measure.dirac y
参数：x_ne_y : x != y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSpace.exists_measurableSet_of_ne`：exists_measurableSet_of_ne [
MeasurableSpace α] [SeparatesPoints α] {x y : α} (h : x != y) : exists s, Measur
ableSet s ∧ x in s ∧ y ∉ s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `MeasureTheory.dirac_ne_dirac_iff_exists_measurableSet`：dirac_ne_dirac_if
f_exists_measurableSet {x y : α} : Measure.dirac x != Measure.dirac y ↔ exists A
, MeasurableSet A ∧ x in A ∧ y ∉ A

--- 原说明 ---
Dirac delta measures at two different points are different, assuming the measura
ble space
separates points.
-/
lemma dirac_ne_dirac [SeparatesPoints α] {x y : α} (x_ne_y : x ≠ y) :
    Measure.dirac x ≠ Measure.dirac y := by
  obtain ⟨A, A_mble, x_in_A, y_notin_A⟩ := exists_measurableSet_of_ne x_ne_y
  exact dirac_ne_dirac_iff_exists_measurableSet.mpr ⟨A, A_mble, x_in_A, y_notin_A⟩

/-- Dirac delta measures at two points are different if and only if the two points are different,
assuming the measurable space separates points. -/
/-
**MeasureTheory.dirac_ne_dirac_iff** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：dirac_ne_dirac_iff [SeparatesPoints α] {x y : α} : Measure.dirac x != Meas
ure.dirac y ↔ x != y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.dirac_ne_dirac`：dirac_ne_dirac [SeparatesPoints α] {x y : 
α} (x_ne_y : x != y) : Measure.dirac x != Measure.dirac y

--- 原说明 ---
Dirac delta measures at two points are different if and only if the two points a
re different,
assuming the measurable space separates points.
-/
lemma dirac_ne_dirac_iff [SeparatesPoints α] {x y : α} :
    Measure.dirac x ≠ Measure.dirac y ↔ x ≠ y :=
  ⟨fun h x_eq_y ↦ h <| congrArg dirac x_eq_y, fun h ↦ dirac_ne_dirac h⟩

/-- Dirac delta measures at two points are equal if and only if the two points are equal,
assuming the measurable space separates points. -/
/-
**MeasureTheory.dirac_eq_dirac_iff** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：dirac_eq_dirac_iff [SeparatesPoints α] {x y : α} : Measure.dirac x = Measu
re.dirac y ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用引理 `MeasureTheory.dirac_ne_dirac_iff`：dirac_ne_dirac_iff [SeparatesPoints α]
 {x y : α} : Measure.dirac x != Measure.dirac y ↔ x != y

--- 原说明 ---
Dirac delta measures at two points are equal if and only if the two points are e
qual,
assuming the measurable space separates points.
-/
lemma dirac_eq_dirac_iff [SeparatesPoints α] {x y : α} :
    Measure.dirac x = Measure.dirac y ↔ x = y := not_iff_not.mp dirac_ne_dirac_iff

/-- The assignment `x ↦ dirac x` is injective, assuming the measurable space separates points. -/
/-
**MeasureTheory.injective_dirac** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：injective_dirac [SeparatesPoints α] : Function.Injective (fun (x : α) => d
irac x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.dirac_eq_dirac_iff`：dirac_eq_dirac_iff [SeparatesPoints α]
 {x y : α} : Measure.dirac x = Measure.dirac y ↔ x = y

--- 原说明 ---
The assignment `x ↦ dirac x` is injective, assuming the measurable space separat
es points.
-/
lemma injective_dirac [SeparatesPoints α] :
    Function.Injective (fun (x : α) ↦ dirac x) := fun x y x_ne_y ↦ by rwa [← dirac_eq_dirac_iff]

end dirac_injective

end MeasureTheory

namespace MeasureTheory.Measure
variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  [MeasurableSingletonClass α] {f : β → α} {μ : Measure α} {s : Finset α} {a₁ a₂ : α}

/-
**MeasureTheory.Measure.ae_mem_finset_iff** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheo
ry.Measure`。
形式化陈述：ae_mem_finset_iff : (forallᵐ a ∂μ, a in s) ↔ μ = ∑ a in s, μ {a} • .dirac 
a where mp hμ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.measure_sdiff_null`：measure_sdiff_null (ht : μ t = 0) : μ 
(s \ t) = μ s
· 使用定理 `Set.sdiff_compl`：sdiff_compl : s \ tᶜ = s inter t
· 使用定理 `Set.biUnion_of_singleton`：biUnion_of_singleton (s : Set α) : ⋃ x in s, {
x} = s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.inter_iUnion`：inter_iUnion (s : Set β) (t : ι -> Set β) : (s inter ⋃
 i, t i) = ⋃ i, s inter t i
· 使用定理 `MeasureTheory.measure_biUnion_finset`：measure_biUnion_finset {s : Finset
 ι} {f : ι -> Set α} (hd : PairwiseDisjoint (↑s) f) (hm : forall b in s, Measura
bleSet (f b)) : μ (⋃ b in …
· 使用定理 `Disjoint.inter_left'`：inter_left' (u : Set α) (h : Disjoint s t) : Disjo
int (u inter s) t
· 使用定理 `Disjoint.inter_right'`：inter_right' (u : Set α) (h : Disjoint s t) : Dis
joint s (u inter t)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MeasureTheory.Measure.coe_finsetSum`：coe_finsetSum {_m : MeasurableSpace
 α} (I : Finset ι) (μ : ι -> Measure α) : ⇑(∑ i in I, μ i) = ∑ i in I, ⇑(μ i)
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.inter_singleton_of_mem`：∀ {α : Type u_1} {s : Set α} {a : α}, a ∈ s 
→ s ∩ {a} = {a}
· 使用定理 `MeasureTheory.Measure.dirac_apply'`：dirac_apply' (a : α) (hs : Measurabl
eSet s) : dirac a s = s.indicator 1 a
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.inter_singleton_of_notMem`：∀ {α : Type u_1} {s : Set α} {a : α}, a ∉
 s → s ∩ {a} = ∅
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
（共 37 条，此处仅展示前 30 条）
-/
lemma ae_mem_finset_iff : (∀ᵐ a ∂μ, a ∈ s) ↔ μ = ∑ a ∈ s, μ {a} • .dirac a where
  mp hμ := by
    ext t ht
    rw [← measure_sdiff_null (s := t) hμ]
    dsimp
    rw [Set.sdiff_compl, ← (s : Set α).biUnion_of_singleton]
    simp_rw [Finset.mem_coe, Set.inter_iUnion]
    rw [measure_biUnion_finset (fun i hi j hj hij ↦ .inter_left' _ <| .inter_right' _ ?_)
      (by measurability)]
    · simp only [coe_finsetSum, Finset.sum_apply, smul_apply]
      congr with a
      by_cases ha : a ∈ t <;> simp [*]
    simpa
  mpr hμ := by rw [hμ, ae_finsetSum_measure_iff]; exact fun i hi ↦ ae_smul_measure (by simpa) _
/-
**MeasureTheory.Measure.ae_eq_or_eq_iff_eq_dirac_add_dirac** 是 Mathlib 中的一个引理，位于
命名空间 `MeasureTheory.Measure`。
形式化陈述：ae_eq_or_eq_iff_eq_dirac_add_dirac (ha : a₁ != a₂) : (forallᵐ a ∂μ, a = a₁
 ∨ a = a₂) ↔ μ = μ {a₁} • .dirac a₁ + μ {a₂} • .dirac a₂
参数：ha : a₁ != a₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Finset.sum_cons`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι} 
[inst : AddCommMonoid M] {f : ι → M} (h : a ∉ s),   ∑ x ∈ Finset.cons a s h, f x
 = f …
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `MeasureTheory.Measure.ae_mem_finset_iff`：ae_mem_finset_iff : (forallᵐ a 
∂μ, a in s) ↔ μ = ∑ a in s, μ {a} • .dirac a where mp hμ
-/
lemma ae_eq_or_eq_iff_eq_dirac_add_dirac (ha : a₁ ≠ a₂) :
    (∀ᵐ a ∂μ, a = a₁ ∨ a = a₂) ↔ μ = μ {a₁} • .dirac a₁ + μ {a₂} • .dirac a₂ := by
  -- FIXME: Why does `simpa using ...` not work?
  convert! ae_mem_finset_iff (s := .cons a₁ { a₂ } <| by simpa) <;> simp
/-
**MeasureTheory.Measure.ae_mem_finset_iff_map_eq_sum_dirac** 是 Mathlib 中的一个引理，位于
命名空间 `MeasureTheory.Measure`。
形式化陈述：ae_mem_finset_iff_map_eq_sum_dirac {μ : Measure β} (hf : AEMeasurable f μ)
 : (forallᵐ b ∂μ, f b in s) ↔ μ.map f = ∑ a in s, μ (f ⁻¹' {a}) • .dirac a
参数：hf : AEMeasurable f μ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.ae_map_iff`：ae_map_iff {f : α -> β} (hf : AEMeasurable f μ
) {p : β -> Prop} (hp : MeasurableSet { x | p x }) : (forallᵐ y ∂μ.map f, p y) ↔
 forallᵐ x ∂μ,…
· 使用定理 `Finset.measurableSet`：∀ {α : Type u_1} [inst : MeasurableSpace α] [Measu
rableSingletonClass α] (s : Finset α), MeasurableSet ↑s
· 使用引理 `MeasureTheory.Measure.ae_mem_finset_iff`：ae_mem_finset_iff : (forallᵐ a 
∂μ, a in s) ↔ μ = ∑ a in s, μ {a} • .dirac a where mp hμ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `MeasureTheory.Measure.map_apply₀`：map_apply₀ {f : α -> β} (hf : AEMeasur
able f μ) {s : Set β} (hs : NullMeasurableSet s (map f μ)) : μ.map f s = μ (f ⁻¹
' s)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma ae_mem_finset_iff_map_eq_sum_dirac {μ : Measure β} (hf : AEMeasurable f μ) :
    (∀ᵐ b ∂μ, f b ∈ s) ↔ μ.map f = ∑ a ∈ s, μ (f ⁻¹' {a}) • .dirac a := by
  rw [← ae_map_iff hf (by measurability), ae_mem_finset_iff]
  simp [map_apply₀ hf]
/-
**MeasureTheory.Measure.ae_eq_or_eq_iff_map_eq_dirac_add_dirac** 是 Mathlib 中的一个引
理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：ae_eq_or_eq_iff_map_eq_dirac_add_dirac {μ : Measure β} (hf : AEMeasurable 
f μ) (ha : a₁ != a₂) : (forallᵐ b ∂μ, f b = a₁ ∨ f b = a₂) ↔ μ.map f = μ (f ⁻¹' 
{a₁}) • .dirac a₁ + μ (f ⁻¹' {a₂}) • .dirac a₂
参数：hf : AEMeasurable f μ；ha : a₁ != a₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Finset.sum_cons`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι} 
[inst : AddCommMonoid M] {f : ι → M} (h : a ∉ s),   ∑ x ∈ Finset.cons a s h, f x
 = f …
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `MeasureTheory.Measure.ae_mem_finset_iff_map_eq_sum_dirac`：ae_mem_finset_
iff_map_eq_sum_dirac {μ : Measure β} (hf : AEMeasurable f μ) : (forallᵐ b ∂μ, f 
b in s) ↔ μ.map f = ∑ a in s, μ (f ⁻¹' {a}) • …
-/
lemma ae_eq_or_eq_iff_map_eq_dirac_add_dirac {μ : Measure β} (hf : AEMeasurable f μ)
    (ha : a₁ ≠ a₂) :
    (∀ᵐ b ∂μ, f b = a₁ ∨ f b = a₂) ↔
      μ.map f = μ (f ⁻¹' {a₁}) • .dirac a₁ + μ (f ⁻¹' {a₂}) • .dirac a₂ := by
  -- FIXME: Why does `simpa using ...` not work?
  convert! ae_mem_finset_iff_map_eq_sum_dirac (s := .cons a₁ { a₂ } <| by simpa) hf <;> simp

end MeasureTheory.Measure

