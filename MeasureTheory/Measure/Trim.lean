/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

/-!
# Restriction of a measure to a sub-σ-algebra


## Main definitions

* `MeasureTheory.Measure.trim`: restriction of a measure to a sub-sigma algebra.

-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

variable {α β : Type*}

/-- Restriction of a measure to a sub-σ-algebra.
It is common to see a measure `μ` on a measurable space structure `m0` as being also a measure on
any `m ≤ m0`. Since measures in mathlib have to be trimmed to the measurable space, `μ` itself
cannot be a measure on `m`, hence the definition of `μ.trim hm`.

This notion is related to `OuterMeasure.trim`, see the lemma
`toOuterMeasure_trim_eq_trim_toOuterMeasure`. -/
noncomputable
/-
**MeasureTheory.Measure.trim** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：{α : Type u_1} → {m m0 : MeasurableSpace α} → MeasureTheory.Measure α → m 
≤ m0 → MeasureTheory.Measure α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Measure.trim {m m0 : MeasurableSpace α} (μ : @Measure α m0) (hm : m ≤ m0) : @Measure α m :=
  @OuterMeasure.toMeasure α m μ.toOuterMeasure (hm.trans (le_toOuterMeasure_caratheodory μ))

@[simp]
/-
**MeasureTheory.trim_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：trim_eq_self [MeasurableSpace α] {μ : Measure α} : μ.trim le_rfl = μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.toOuterMeasure_toMeasure`：toOuterMeasure_toMeasure {μ : Me
asure α} : μ.toOuterMeasure.toMeasure (le_toOuterMeasure_caratheodory _) = μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem trim_eq_self [MeasurableSpace α] {μ : Measure α} : μ.trim le_rfl = μ := by
  simp [Measure.trim]

variable {m m0 : MeasurableSpace α} {mβ : MeasurableSpace β} {μ : Measure α} {s : Set α}
/-
**MeasureTheory.toOuterMeasure_trim_eq_trim_toOuterMeasure** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory`。
形式化陈述：toOuterMeasure_trim_eq_trim_toOuterMeasure (μ : Measure α) (hm : m <= m0) 
: @Measure.toOuterMeasure _ m (μ.trim hm) = @OuterMeasure.trim _ m μ.toOuterMeas
ure
参数：μ : Measure α；hm : m <= m0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.trim.eq_1`：∀ {α : Type u_1} {m m0 : MeasurableSpac
e α} (μ : MeasureTheory.Measure α) (hm : m ≤ m0), μ.trim hm = μ.toMeasure ⋯
· 使用定理 `MeasureTheory.toMeasure_toOuterMeasure`：toMeasure_toOuterMeasure (m : Ou
terMeasure α) (h : ms <= m.caratheodory) : (m.toMeasure h).toOuterMeasure = m.tr
im
-/
theorem toOuterMeasure_trim_eq_trim_toOuterMeasure (μ : Measure α) (hm : m ≤ m0) :
    @Measure.toOuterMeasure _ m (μ.trim hm) = @OuterMeasure.trim _ m μ.toOuterMeasure := by
  rw [Measure.trim, toMeasure_toOuterMeasure (ms := m)]

@[simp]
/-
**MeasureTheory.zero_trim** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：zero_trim (hm : m <= m0) : (0 : Measure α).trim hm = (0 : @Measure α m)
参数：hm : m <= m0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.OuterMeasure.toMeasure_zero`：∀ {α : Type u_1} [ms : Measur
ableSpace α] (h : ms ≤ MeasureTheory.OuterMeasure.caratheodory 0),   MeasureTheo
ry.OuterMeasure.toMeasure 0 h =…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem zero_trim (hm : m ≤ m0) : (0 : Measure α).trim hm = (0 : @Measure α m) := by
  simp [Measure.trim, @OuterMeasure.toMeasure_zero _ m]
/-
**MeasureTheory.trim_measurableSet_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：trim_measurableSet_eq (hm : m <= m0) (hs : @MeasurableSet α m s) : μ.trim 
hm s = μ s
参数：hm : m <= m0；hs : @MeasurableSet α m s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.trim.eq_1`：∀ {α : Type u_1} {m m0 : MeasurableSpac
e α} (μ : MeasureTheory.Measure α) (hm : m ≤ m0), μ.trim hm = μ.toMeasure ⋯
· 使用定理 `MeasureTheory.toMeasure_apply`：toMeasure_apply (m : OuterMeasure α) (h :
 ms <= m.caratheodory) {s : Set α} (hs : MeasurableSet s) : m.toMeasure h s = m 
s
· 使用定理 `MeasureTheory.Measure.coe_toOuterMeasure`：∀ {α : Type u_1} [inst : Measu
rableSpace α] (μ : MeasureTheory.Measure α), ⇑μ.toOuterMeasure = ⇑μ
-/
theorem trim_measurableSet_eq (hm : m ≤ m0) (hs : @MeasurableSet α m s) : μ.trim hm s = μ s := by
  rw [Measure.trim, toMeasure_apply (ms := m) _ _ hs, Measure.coe_toOuterMeasure]
/-
**MeasureTheory.le_trim** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：le_trim (hm : m <= m0) : μ s <= μ.trim hm s
参数：hm : m <= m0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.le_toMeasure_apply`：le_toMeasure_apply (m : OuterMeasure α
) (h : ms <= m.caratheodory) (s : Set α) : m s <= m.toMeasure h s
-/
theorem le_trim (hm : m ≤ m0) : μ s ≤ μ.trim hm s := by
  simp_rw [Measure.trim]
  exact @le_toMeasure_apply _ m _ _ _
/-
**MeasureTheory.trim_eq_map** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：trim_eq_map (hm : m <= m0) : μ.trim hm = @Measure.map _ _ _ m id μ
参数：hm : m <= m0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `measurable_id''`：measurable_id'' {m mα : MeasurableSpace α} (hm : m <= m
α) : @Measurable α α mα m id
· 使用定理 `MeasureTheory.trim_measurableSet_eq`：trim_measurableSet_eq (hm : m <= m0
) (hs : @MeasurableSet α m s) : μ.trim hm s = μ s
· 使用定理 `Set.preimage_id`：preimage_id {s : Set α} : id ⁻¹' s = s
-/
lemma trim_eq_map (hm : m ≤ m0) : μ.trim hm = @Measure.map _ _ _ m id μ := by
  refine @Measure.ext α m _ _ (fun s hs ↦ ?_)
  rw [Measure.map_apply (measurable_id'' hm) hs, trim_measurableSet_eq hm hs, Set.preimage_id]
/-
**MeasureTheory.map_trim_comap** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：map_trim_comap {f : α -> β} (hf : Measurable f) : @Measure.map _ _ (mβ.com
ap f) _ f (μ.trim hf.comap_le) = μ.map f
参数：hf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `Measurable.comap_le`：∀ {α : Type u_1} {β : Type u_2} {m₁ : MeasurableSpa
ce α} {m₂ : MeasurableSpace β} {f : α → β},   Measurable f → MeasurableSpace.com
ap f m₂ ≤…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `Measurable.of_comap_le`：∀ {α : Type u_1} {β : Type u_2} {m₁ : Measurable
Space α} {m₂ : MeasurableSpace β} {f : α → β},   MeasurableSpace.comap f m₂ ≤ m₁
 → Measurabl…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `MeasureTheory.trim_measurableSet_eq`：trim_measurableSet_eq (hm : m <= m0
) (hs : @MeasurableSet α m s) : μ.trim hm s = μ s
-/
lemma map_trim_comap {f : α → β} (hf : Measurable f) :
    @Measure.map _ _ (mβ.comap f) _ f (μ.trim hf.comap_le) = μ.map f := by
  ext s hs
  rw [Measure.map_apply hf hs, Measure.map_apply _ hs, trim_measurableSet_eq]
  · exact ⟨s, hs, rfl⟩
  · exact Measurable.of_comap_le le_rfl
/-
**MeasureTheory.trim_comap_apply** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：trim_comap_apply {f : α -> β} (hf : Measurable f) {s : Set β} (hs : Measur
ableSet s) : μ.trim hf.comap_le (f ⁻¹' s) = μ.map f s
参数：hf : Measurable f；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comap_le`：∀ {α : Type u_1} {β : Type u_2} {m₁ : MeasurableSpa
ce α} {m₂ : MeasurableSpace β} {f : α → β},   Measurable f → MeasurableSpace.com
ap f m₂ ≤…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.map_trim_comap`：map_trim_comap {f : α -> β} (hf : Measurab
le f) : @Measure.map _ _ (mβ.comap f) _ f (μ.trim hf.comap_le) = μ.map f
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `Measurable.of_comap_le`：∀ {α : Type u_1} {β : Type u_2} {m₁ : Measurable
Space α} {m₂ : MeasurableSpace β} {f : α → β},   MeasurableSpace.comap f m₂ ≤ m₁
 → Measurabl…
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma trim_comap_apply {f : α → β} (hf : Measurable f) {s : Set β} (hs : MeasurableSet s) :
    μ.trim hf.comap_le (f ⁻¹' s) = μ.map f s := by
  rw [← map_trim_comap hf, Measure.map_apply (Measurable.of_comap_le le_rfl) hs]
/-
**MeasureTheory.ae_map_iff_ae_trim** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_map_iff_ae_trim {f : α -> β} (hf : Measurable f) {p : β -> Prop} (hp : 
MeasurableSet { x | p x }) : (forallᵐ y ∂μ.map f, p y) ↔ forallᵐ x ∂(μ.trim hf.c
omap_le), p (f x)
参数：hf : Measurable f；hp : MeasurableSet { x | p x }。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Measurable.comap_le`：∀ {α : Type u_1} {β : Type u_2} {m₁ : MeasurableSpa
ce α} {m₂ : MeasurableSpace β} {f : α → β},   Measurable f → MeasurableSpace.com
ap f m₂ ≤…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.map_trim_comap`：map_trim_comap {f : α -> β} (hf : Measurab
le f) : @Measure.map _ _ (mβ.comap f) _ f (μ.trim hf.comap_le) = μ.map f
· 使用定理 `MeasureTheory.ae_map_iff`：ae_map_iff {f : α -> β} (hf : AEMeasurable f μ
) {p : β -> Prop} (hp : MeasurableSet { x | p x }) : (forallᵐ y ∂μ.map f, p y) ↔
 forallᵐ x ∂μ,…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `Measurable.of_comap_le`：∀ {α : Type u_1} {β : Type u_2} {m₁ : Measurable
Space α} {m₂ : MeasurableSpace β} {f : α → β},   MeasurableSpace.comap f m₂ ≤ m₁
 → Measurabl…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma ae_map_iff_ae_trim {f : α → β} (hf : Measurable f)
    {p : β → Prop} (hp : MeasurableSet { x | p x }) :
    (∀ᵐ y ∂μ.map f, p y) ↔ ∀ᵐ x ∂(μ.trim hf.comap_le), p (f x) := by
  rw [← map_trim_comap hf, ae_map_iff (Measurable.of_comap_le le_rfl).aemeasurable hp]
/-
**MeasureTheory.trim_add** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：trim_add {ν : Measure α} (hm : m <= m0) : (μ + ν).trim hm = μ.trim hm + ν.
trim hm
参数：hm : m <= m0。
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
· 使用定理 `MeasureTheory.trim_measurableSet_eq`：trim_measurableSet_eq (hm : m <= m0
) (hs : @MeasurableSet α m s) : μ.trim hm s = μ s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma trim_add {ν : Measure α} (hm : m ≤ m0) : (μ + ν).trim hm = μ.trim hm + ν.trim hm :=
  @Measure.ext _ m _ _ (fun s hs ↦ by simp [trim_measurableSet_eq hm hs])
/-
**MeasureTheory.measure_eq_zero_of_trim_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
形式化陈述：measure_eq_zero_of_trim_eq_zero (hm : m <= m0) (h : μ.trim hm s = 0) : μ s
 = 0
参数：hm : m <= m0；h : μ.trim hm s = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `MeasureTheory.le_trim`：le_trim (hm : m <= m0) : μ s <= μ.trim hm s
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem measure_eq_zero_of_trim_eq_zero (hm : m ≤ m0) (h : μ.trim hm s = 0) : μ s = 0 := by
  grw [← nonpos_iff_eq_zero, ← h, le_trim hm]
/-
**MeasureTheory.measure_trim_toMeasurable_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory`。
形式化陈述：measure_trim_toMeasurable_eq_zero {hm : m <= m0} (hs : μ.trim hm s = 0) : 
μ (@toMeasurable α m (μ.trim hm) s) = 0
参数：hs : μ.trim hm s = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measure_eq_zero_of_trim_eq_zero`：measure_eq_zero_of_trim_e
q_zero (hm : m <= m0) (h : μ.trim hm s = 0) : μ s = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measure_toMeasurable`：measure_toMeasurable (s : Set α) : μ
 (toMeasurable μ s) = μ s
-/
theorem measure_trim_toMeasurable_eq_zero {hm : m ≤ m0} (hs : μ.trim hm s = 0) :
    μ (@toMeasurable α m (μ.trim hm) s) = 0 :=
  measure_eq_zero_of_trim_eq_zero hm (by rwa [@measure_toMeasurable _ m])
/-
**MeasureTheory.ae_of_ae_trim** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_of_ae_trim (hm : m <= m0) {μ : Measure α} {P : α -> Prop} (h : forallᵐ 
x ∂μ.trim hm, P x) : forallᵐ x ∂μ, P x
参数：hm : m <= m0；h : forallᵐ x ∂μ.trim hm, P x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.measure_eq_zero_of_trim_eq_zero`：measure_eq_zero_of_trim_e
q_zero (hm : m <= m0) (h : μ.trim hm s = 0) : μ s = 0
-/
theorem ae_of_ae_trim (hm : m ≤ m0) {μ : Measure α} {P : α → Prop} (h : ∀ᵐ x ∂μ.trim hm, P x) :
    ∀ᵐ x ∂μ, P x :=
  measure_eq_zero_of_trim_eq_zero hm h
/-
**MeasureTheory.ae_eq_of_ae_eq_trim** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_eq_of_ae_eq_trim {E} {hm : m <= m0} {f₁ f₂ : α -> E} (h12 : f₁ =ᵐ[μ.tri
m hm] f₂) : f₁ =ᵐ[μ] f₂
参数：h12 : f₁ =ᵐ[μ.trim hm] f₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.measure_eq_zero_of_trim_eq_zero`：measure_eq_zero_of_trim_e
q_zero (hm : m <= m0) (h : μ.trim hm s = 0) : μ s = 0
-/
theorem ae_eq_of_ae_eq_trim {E} {hm : m ≤ m0} {f₁ f₂ : α → E}
    (h12 : f₁ =ᵐ[μ.trim hm] f₂) : f₁ =ᵐ[μ] f₂ :=
  measure_eq_zero_of_trim_eq_zero hm h12
/-
**MeasureTheory.ae_le_of_ae_le_trim** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_le_of_ae_le_trim {E} [LE E] {hm : m <= m0} {f₁ f₂ : α -> E} (h12 : f₁ <
=ᵐ[μ.trim hm] f₂) : f₁ <=ᵐ[μ] f₂
参数：h12 : f₁ <=ᵐ[μ.trim hm] f₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.measure_eq_zero_of_trim_eq_zero`：measure_eq_zero_of_trim_e
q_zero (hm : m <= m0) (h : μ.trim hm s = 0) : μ s = 0
-/
theorem ae_le_of_ae_le_trim {E} [LE E] {hm : m ≤ m0} {f₁ f₂ : α → E}
    (h12 : f₁ ≤ᵐ[μ.trim hm] f₂) : f₁ ≤ᵐ[μ] f₂ :=
  measure_eq_zero_of_trim_eq_zero hm h12
/-
**MeasureTheory.trim_trim** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：trim_trim {m₁ m₂ : MeasurableSpace α} {hm₁₂ : m₁ <= m₂} {hm₂ : m₂ <= m0} :
 (μ.trim hm₂).trim hm₁₂ = μ.trim (hm₁₂.trans hm₂)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.trim_measurableSet_eq`：trim_measurableSet_eq (hm : m <= m0
) (hs : @MeasurableSet α m s) : μ.trim hm s = μ s
-/
theorem trim_trim {m₁ m₂ : MeasurableSpace α} {hm₁₂ : m₁ ≤ m₂} {hm₂ : m₂ ≤ m0} :
    (μ.trim hm₂).trim hm₁₂ = μ.trim (hm₁₂.trans hm₂) := by
  refine @Measure.ext _ m₁ _ _ (fun t ht => ?_)
  rw [trim_measurableSet_eq hm₁₂ ht, trim_measurableSet_eq (hm₁₂.trans hm₂) ht,
    trim_measurableSet_eq hm₂ (hm₁₂ t ht)]
/-
**MeasureTheory.restrict_trim** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：restrict_trim (hm : m <= m0) (μ : Measure α) (hs : @MeasurableSet α m s) :
 @Measure.restrict α m (μ.trim hm) s = (μ.restrict s).trim hm
参数：hm : m <= m0；μ : Measure α；hs : @MeasurableSet α m s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `MeasureTheory.trim_measurableSet_eq`：trim_measurableSet_eq (hm : m <= m0
) (hs : @MeasurableSet α m s) : μ.trim hm s = μ s
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
-/
theorem restrict_trim (hm : m ≤ m0) (μ : Measure α) (hs : @MeasurableSet α m s) :
    @Measure.restrict α m (μ.trim hm) s = (μ.restrict s).trim hm := by
  refine @Measure.ext _ m _ _ (fun t ht => ?_)
  rw [@Measure.restrict_apply α m _ _ _ ht, trim_measurableSet_eq hm ht,
    Measure.restrict_apply (hm t ht),
    trim_measurableSet_eq hm (@MeasurableSet.inter α m t s ht hs)]
/-
**MeasureTheory.measure_spanningSets_trim_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory`。
形式化陈述：measure_spanningSets_trim_lt_top (hm : m <= m0) (μ : Measure α) [SigmaFini
te (μ.trim hm)] (n : Nat) : μ (spanningSets (μ.trim hm) n) < ⊤
参数：hm : m <= m0；μ : Measure α；μ.trim hm；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.le_trim`：le_trim (hm : m <= m0) : μ s <= μ.trim hm s
· 使用定理 `MeasureTheory.measure_spanningSets_lt_top`：measure_spanningSets_lt_top (
μ : Measure α) [SigmaFinite μ] (i : Nat) : μ (spanningSets μ i) < ∞
-/
theorem measure_spanningSets_trim_lt_top (hm : m ≤ m0) (μ : Measure α) [SigmaFinite (μ.trim hm)]
    (n : ℕ) :
    μ (spanningSets (μ.trim hm) n) < ⊤ :=
  (le_trim hm).trans_lt (measure_spanningSets_lt_top (μ.trim hm) n)
/-
**MeasureTheory.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (hm : m ≤ m0) (μ : Measure α) [SigmaFinite (μ.trim hm)] (n : ℕ) :
    IsFiniteMeasure (μ.restrict (spanningSets (μ.trim hm) n)) :=
  isFiniteMeasure_restrict.2 (measure_spanningSets_trim_lt_top hm μ n).ne
/-
**MeasureTheory.isFiniteMeasure_trim** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory`。
形式化陈述：isFiniteMeasure_trim (hm : m <= m0) [IsFiniteMeasure μ] : IsFiniteMeasure 
(μ.trim hm) where measure_univ_lt_top
参数：hm : m <= m0。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.trim_measurableSet_eq`：trim_measurableSet_eq (hm : m <= m0
) (hs : @MeasurableSet α m s) : μ.trim hm s = μ s
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `MeasureTheory.measure_lt_top`：measure_lt_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s < ∞
-/
instance isFiniteMeasure_trim (hm : m ≤ m0) [IsFiniteMeasure μ] : IsFiniteMeasure (μ.trim hm) where
  measure_univ_lt_top := by
    rw [trim_measurableSet_eq hm (@MeasurableSet.univ _ m)]
    exact measure_lt_top _ _
/-
**MeasureTheory.sigmaFiniteTrim_mono** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：sigmaFiniteTrim_mono {m m₂ m0 : MeasurableSpace α} {μ : Measure α} (hm : m
 <= m0) (hm₂ : m₂ <= m) [SigmaFinite (μ.trim (hm₂.trans hm))] : SigmaFinite (μ.t
rim hm)
参数：hm : m <= m0；hm₂ : m₂ <= m；μ.trim (hm₂.trans hm)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.trim_trim`：trim_trim {m₁ m₂ : MeasurableSpace α} {hm₁₂ : m
₁ <= m₂} {hm₂ : m₂ <= m0} : (μ.trim hm₂).trim hm₁₂ = μ.trim (hm₁₂.trans hm₂)
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `MeasureTheory.measure_spanningSets_trim_lt_top`：measure_spanningSets_tri
m_lt_top (hm : m <= m0) (μ : Measure α) [SigmaFinite (μ.trim hm)] (n : Nat) : μ 
(spanningSets (μ.trim hm) n) < ⊤
· 使用定理 `MeasureTheory.iUnion_spanningSets`：iUnion_spanningSets (μ : Measure α) [
SigmaFinite μ] : ⋃ i : Nat, spanningSets μ i = univ
-/
theorem sigmaFiniteTrim_mono {m m₂ m0 : MeasurableSpace α} {μ : Measure α} (hm : m ≤ m0)
    (hm₂ : m₂ ≤ m) [SigmaFinite (μ.trim (hm₂.trans hm))] : SigmaFinite (μ.trim hm) := by
  have : SigmaFinite ((μ.trim hm).trim hm₂) := by simpa [trim_trim]
  exact ⟨⟨
    { set := spanningSets ((μ.trim hm).trim hm₂)
      set_mem := fun _ => Set.mem_univ _
      finite := fun i => measure_spanningSets_trim_lt_top hm₂ (μ.trim hm) i
      spanning := iUnion_spanningSets _ }⟩⟩
/-
**MeasureTheory.SigmaFinite.of_trim** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Sig
maFinite`。
形式化陈述：∀ {α : Type u_1} {m m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} 
(hm : m ≤ m0)   [MeasureTheory.SigmaFinite (μ.trim hm)], MeasureTheory.SigmaFini
te μ
参数：hm : m ≤ m0；μ.trim hm。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.trim_eq_self`：trim_eq_self [MeasurableSpace α] {μ : Measur
e α} : μ.trim le_rfl = μ
· 使用定理 `MeasureTheory.sigmaFiniteTrim_mono`：sigmaFiniteTrim_mono {m m₂ m0 : Meas
urableSpace α} {μ : Measure α} (hm : m <= m0) (hm₂ : m₂ <= m) [SigmaFinite (μ.tr
im (hm₂.trans hm))] : Si…
-/
lemma SigmaFinite.of_trim {m m0 : MeasurableSpace α} {μ : Measure α} (hm : m ≤ m0)
    [SigmaFinite (μ.trim hm)] : SigmaFinite μ := by
  rw [← trim_eq_self (μ := μ)]
  exact sigmaFiniteTrim_mono le_rfl hm
/-
**MeasureTheory.sigmaFinite_trim_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：sigmaFinite_trim_bot_iff : SigmaFinite (μ.trim bot_le) ↔ IsFiniteMeasure μ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.sigmaFinite_bot_iff`：sigmaFinite_bot_iff (μ : @Measure α ⊥
) : SigmaFinite μ ↔ IsFiniteMeasure μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.measure_univ_lt_top`：∀ {α : Type u_1} {m0 
: MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsFinit
eMeasure μ],   μ Set.univ < ⊤
· 使用定理 `MeasureTheory.trim_measurableSet_eq`：trim_measurableSet_eq (hm : m <= m0
) (hs : @MeasurableSet α m s) : μ.trim hm s = μ s
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
-/
theorem sigmaFinite_trim_bot_iff : SigmaFinite (μ.trim bot_le) ↔ IsFiniteMeasure μ := by
  rw [sigmaFinite_bot_iff]
  refine ⟨fun h => ⟨?_⟩, fun h => ⟨?_⟩⟩ <;> have h_univ := h.measure_univ_lt_top
  · rwa [trim_measurableSet_eq bot_le MeasurableSet.univ] at h_univ
  · rwa [trim_measurableSet_eq bot_le MeasurableSet.univ]
/-
**MeasureTheory.Measure.AbsolutelyContinuous.trim** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.Measure.AbsolutelyContinuous`。
形式化陈述：∀ {α : Type u_1} {m m0 : MeasurableSpace α} {μ ν : MeasureTheory.Measure α
},   μ.AbsolutelyContinuous ν → ∀ (hm : m ≤ m0), (μ.trim hm).AbsolutelyContinuou
s (ν.trim hm)
参数：hm : m ≤ m0；μ.trim hm；ν.trim hm。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.mk`：mk (h : forall ⦃s : Set α
⦄, MeasurableSet s -> ν s = 0 -> μ s = 0) : μ ≪ ν
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.trim_measurableSet_eq`：trim_measurableSet_eq (hm : m <= m0
) (hs : @MeasurableSet α m s) : μ.trim hm s = μ s
-/
lemma Measure.AbsolutelyContinuous.trim {ν : Measure α} (hμν : μ ≪ ν) (hm : m ≤ m0) :
    μ.trim hm ≪ ν.trim hm := by
  refine Measure.AbsolutelyContinuous.mk (fun s hs hsν ↦ ?_)
  rw [trim_measurableSet_eq hm hs] at hsν ⊢
  exact hμν hsν
/-
**MeasureTheory._root_.ae_eq_trim_of_measurable** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.ae_eq_trim_of_measurable {α β} {m m0 : MeasurableSpace α} {μ : Measure α}
    [MeasurableSpace β] [MeasurableEq β]
    (hm : m ≤ m0) {f g : α → β} (hf : Measurable[m] f) (hg : Measurable[m] g) (hfg : f =ᵐ[μ] g) :
    f =ᵐ[μ.trim hm] g := by
  rwa [Filter.EventuallyEq, ae_iff, trim_measurableSet_eq hm _]
  measurability

end MeasureTheory

