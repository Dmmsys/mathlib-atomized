/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Order.Filter.ENNReal
public import Mathlib.Probability.UniformOn

/-!
# Essential supremum and infimum

We define the essential supremum and infimum of a function `f : α → β` with respect to a measure
`μ` on `α`. The essential supremum is the infimum of the constants `c : β` such that `f x ≤ c`
almost everywhere.

TODO: The essential supremum of functions `α → ℝ≥0∞` is used in particular to define the norm in
the `L∞` space (see `Mathlib/MeasureTheory/Function/LpSeminorm/Defs.lean`).

There is a different quantity which is sometimes also called essential supremum: the least
upper-bound among measurable functions of a family of measurable functions (in an almost-everywhere
sense). We do not define that quantity here, which is simply the supremum of a map with values in
`α →ₘ[μ] β` (see `Mathlib/MeasureTheory/Function/AEEqFun.lean`).

## Main definitions

* `essSup f μ := (ae μ).limsup f`
* `essInf f μ := (ae μ).liminf f`
-/

@[expose] public section


open Filter MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped ENNReal NNReal

variable {α β : Type*} {m : MeasurableSpace α} {μ ν : Measure α}

section ConditionallyCompleteLattice

variable [ConditionallyCompleteLattice β] {f : α → β}

/-- Essential supremum of `f` with respect to measure `μ`: the smallest `c : β` such that
`f x ≤ c` a.e. -/
/-
**essSup** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：essSup {_ : MeasurableSpace α} (f : α -> β) (μ : Measure α)
参数：f : α -> β；μ : Measure α。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α

--- 原说明 ---
Essential supremum of `f` with respect to measure `μ`: the smallest `c : β` such
 that
`f x ≤ c` a.e.
-/
def essSup {_ : MeasurableSpace α} (f : α → β) (μ : Measure α) :=
  (ae μ).limsup f

/-- Essential infimum of `f` with respect to measure `μ`: the greatest `c : β` such that
`c ≤ f x` a.e. -/
/-
**essInf** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：essInf {_ : MeasurableSpace α} (f : α -> β) (μ : Measure α)
参数：f : α -> β；μ : Measure α。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α

--- 原说明 ---
Essential infimum of `f` with respect to measure `μ`: the greatest `c : β` such 
that
`c ≤ f x` a.e.
-/
def essInf {_ : MeasurableSpace α} (f : α → β) (μ : Measure α) :=
  (ae μ).liminf f
/-
**essSup_congr_ae** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：essSup_congr_ae {f g : α -> β} (hfg : f =ᵐ[μ] g) : essSup f μ = essSup g μ
参数：hfg : f =ᵐ[μ] g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.limsup_congr`：limsup_congr {α : Type*} [ConditionallyCompleteLatt
ice β] {f : Filter α} {u v : α -> β} (h : forallᶠ a in f, u a = v a) : limsup u 
f = limsu…
-/
theorem essSup_congr_ae {f g : α → β} (hfg : f =ᵐ[μ] g) : essSup f μ = essSup g μ :=
  limsup_congr hfg
/-
**essInf_congr_ae** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：essInf_congr_ae {f g : α -> β} (hfg : f =ᵐ[μ] g) : essInf f μ = essInf g μ
参数：hfg : f =ᵐ[μ] g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `essSup_congr_ae`：essSup_congr_ae {f g : α -> β} (hfg : f =ᵐ[μ] g) : essS
up f μ = essSup g μ
-/
theorem essInf_congr_ae {f g : α → β} (hfg : f =ᵐ[μ] g) : essInf f μ = essInf g μ :=
  @essSup_congr_ae α βᵒᵈ _ _ _ _ _ hfg

@[simp]
/-
**essSup_const'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：essSup_const' [NeZero μ] (c : β) : essSup (fun _ : α => c) μ = c
参数：c : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.limsup_const`：limsup_const {α : Type*} [ConditionallyCompleteLatt
ice β] {f : Filter α} [NeBot f] (b : β) : limsup (fun _ => b) f = b
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.ae.neBot`：∀ {α : Type u_1} {m0 : MeasurableSpace α
} {μ : MeasureTheory.Measure α} [NeZero μ], (MeasureTheory.ae μ).NeBot
-/
theorem essSup_const' [NeZero μ] (c : β) : essSup (fun _ : α => c) μ = c :=
  limsup_const _

@[simp]
/-
**essInf_const'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：essInf_const' [NeZero μ] (c : β) : essInf (fun _ : α => c) μ = c
参数：c : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.liminf_const`：liminf_const {α : Type*} [ConditionallyCompleteLatt
ice β] {f : Filter α} [NeBot f] (b : β) : liminf (fun _ => b) f = b
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.ae.neBot`：∀ {α : Type u_1} {m0 : MeasurableSpace α
} {μ : MeasureTheory.Measure α} [NeZero μ], (MeasureTheory.ae μ).NeBot
-/
theorem essInf_const' [NeZero μ] (c : β) : essInf (fun _ : α => c) μ = c :=
  liminf_const _
/-
**essSup_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：essSup_const (c : β) (hμ : μ != 0) : essSup (fun _ : α => c) μ = c
参数：c : β；hμ : μ != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `essSup_const'`：essSup_const' [NeZero μ] (c : β) : essSup (fun _ : α => c
) μ = c
-/
theorem essSup_const (c : β) (hμ : μ ≠ 0) : essSup (fun _ : α => c) μ = c :=
  have := NeZero.mk hμ; essSup_const' _
/-
**essInf_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：essInf_const (c : β) (hμ : μ != 0) : essInf (fun _ : α => c) μ = c
参数：c : β；hμ : μ != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `essInf_const'`：essInf_const' [NeZero μ] (c : β) : essInf (fun _ : α => c
) μ = c
-/
theorem essInf_const (c : β) (hμ : μ ≠ 0) : essInf (fun _ : α => c) μ = c :=
  have := NeZero.mk hμ; essInf_const' _

section SMul
variable {R : Type*} [Semiring R] [IsDomain R] [Module R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
  [Module.IsTorsionFree R ℝ≥0∞] {c : R}

@[simp]
/-
**essSup_smul_measure** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：essSup_smul_measure (hc : c != 0) (f : α -> β) : essSup f (c • μ) = essSup
 f μ
参数：hc : c != 0；f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.ae_smul_measure_eq`：∀ {α : Type u_1} {m0 : Measura
bleSpace α} {R : Type u_8} [inst : Semiring R] [IsDomain R]   [inst_2 : _root_.M
odule R ENNReal] [inst_3 : IsS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma essSup_smul_measure (hc : c ≠ 0) (f : α → β) : essSup f (c • μ) = essSup f μ := by
  simp_rw [essSup, Measure.ae_smul_measure_eq hc]

end SMul

@[simp]
/-
**essSup_ennreal_smul_measure** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：essSup_ennreal_smul_measure {c : Real>=0∞} (hc : c != 0) (f : α -> β) : es
sSup f (c • μ) = essSup f μ
参数：hc : c != 0；f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.ae_ennreal_smul_measure_eq`：∀ {α : Type u_1} {m0 :
 MeasurableSpace α} {c : ENNReal},   c ≠ 0 → ∀ (μ : MeasureTheory.Measure α), Me
asureTheory.ae (c • μ) = MeasureTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma essSup_ennreal_smul_measure {c : ℝ≥0∞} (hc : c ≠ 0) (f : α → β) :
    essSup f (c • μ) = essSup f μ := by
  simp_rw [essSup, Measure.ae_ennreal_smul_measure_eq hc]
/-
**essSup_mono_ae** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：essSup_mono_ae {f g : α -> β} (hfg : f <=ᵐ[μ] g) (hf : IsCoboundedUnder (·
 <= ·) (ae μ) f
参数：hfg : f <=ᵐ[μ] g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.limsup_le_limsup`：limsup_le_limsup {α : Type*} [ConditionallyComp
leteLattice β] {f : Filter α} {u v : α -> β} (h : u <=ᶠ[f] v) (hu : f.IsCobounde
dUnder (· <= …
-/
theorem essSup_mono_ae {f g : α → β} (hfg : f ≤ᵐ[μ] g)
    (hf : IsCoboundedUnder (· ≤ ·) (ae μ) f := by isBoundedDefault)
    (hg : IsBoundedUnder (· ≤ ·) (ae μ) g := by isBoundedDefault) :
    essSup f μ ≤ essSup g μ :=
  limsup_le_limsup hfg hf hg
/-
**essInf_mono_ae** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：essInf_mono_ae {f g : α -> β} (hfg : f <=ᵐ[μ] g) (hf : IsBoundedUnder (· >
= ·) (ae μ) f
参数：hfg : f <=ᵐ[μ] g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.liminf_le_liminf`：liminf_le_liminf {α : Type*} [ConditionallyComp
leteLattice β] {f : Filter α} {u v : α -> β} (h : forallᶠ a in f, u a <= v a) (h
u : f.IsBound…
-/
theorem essInf_mono_ae {f g : α → β} (hfg : f ≤ᵐ[μ] g)
    (hf : IsBoundedUnder (· ≥ ·) (ae μ) f := by isBoundedDefault)
    (hg : IsCoboundedUnder (· ≥ ·) (ae μ) g := by isBoundedDefault) :
    essInf f μ ≤ essInf g μ :=
  liminf_le_liminf hfg hf hg
/-
**essSup_le_of_ae_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：essSup_le_of_ae_le {f : α -> β} (c : β) (hf : f <=ᵐ[μ] fun _ => c) (hfbdd 
: IsCoboundedUnder (· <= ·) (ae μ) f
参数：c : β；hf : f <=ᵐ[μ] fun _ => c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.limsup_le_of_le`：limsup_le_of_le {f : Filter β} {u : β -> α} {a} 
(hf : f.IsCoboundedUnder (· <= ·) u
-/
theorem essSup_le_of_ae_le {f : α → β} (c : β) (hf : f ≤ᵐ[μ] fun _ => c)
    (hfbdd : IsCoboundedUnder (· ≤ ·) (ae μ) f := by isBoundedDefault) :
    essSup f μ ≤ c :=
  limsup_le_of_le hfbdd hf
/-
**le_essInf_of_ae_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_essInf_of_ae_le {f : α -> β} (c : β) (hf : (fun _ => c) <=ᵐ[μ] f) (hfbd
d : IsCoboundedUnder (· >= ·) (ae μ) f
参数：c : β；hf : (fun _ => c) <=ᵐ[μ] f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.le_liminf_of_le`：le_liminf_of_le {f : Filter β} {u : β -> α} {a} 
(hf : f.IsCoboundedUnder (· >= ·) u
-/
theorem le_essInf_of_ae_le {f : α → β} (c : β) (hf : (fun _ => c) ≤ᵐ[μ] f)
    (hfbdd : IsCoboundedUnder (· ≥ ·) (ae μ) f := by isBoundedDefault) :
    c ≤ essInf f μ :=
  le_liminf_of_le hfbdd hf
/-
**OrderIso.essSup_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OrderIso.essSup_apply {_ : MeasurableSpace α} {γ} [ConditionallyCompleteLa
ttice γ] (f : α -> β) (μ : Measure α) (g : β ≃o γ) (hf : IsBoundedUnder (· <= ·)
 (ae μ) f
参数：f : α -> β；μ : Measure α；g : β ≃o γ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `OrderIso.limsup_apply`：OrderIso.limsup_apply {γ} [ConditionallyCompleteL
attice β] [ConditionallyCompleteLattice γ] {f : Filter α} {u : α -> β} (g : β ≃o
 γ) (hu : f…
-/
theorem OrderIso.essSup_apply {_ : MeasurableSpace α} {γ} [ConditionallyCompleteLattice γ]
    (f : α → β) (μ : Measure α) (g : β ≃o γ)
    (hf : IsBoundedUnder (· ≤ ·) (ae μ) f := by isBoundedDefault)
    (hf_co : IsCoboundedUnder (· ≤ ·) (ae μ) f := by isBoundedDefault)
    (hgf : IsBoundedUnder (· ≤ ·) (ae μ) (fun x => g (f x)) := by isBoundedDefault)
    (hgf_co : IsCoboundedUnder (· ≤ ·) (ae μ) (fun x => g (f x)) := by
      isBoundedDefault) :
    g (essSup f μ) = essSup (fun x => g (f x)) μ :=
  OrderIso.limsup_apply g hf hf_co hgf hgf_co
/-
**OrderIso.essInf_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OrderIso.essInf_apply {_ : MeasurableSpace α} {γ} [ConditionallyCompleteLa
ttice γ] (f : α -> β) (μ : Measure α) (g : β ≃o γ) (hf : IsBoundedUnder (· >= ·)
 (ae μ) f
参数：f : α -> β；μ : Measure α；g : β ≃o γ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `OrderIso.liminf_apply`：OrderIso.liminf_apply {γ} [ConditionallyCompleteL
attice β] [ConditionallyCompleteLattice γ] {f : Filter α} {u : α -> β} (g : β ≃o
 γ) (hu : f…
-/
theorem OrderIso.essInf_apply {_ : MeasurableSpace α} {γ} [ConditionallyCompleteLattice γ]
    (f : α → β) (μ : Measure α) (g : β ≃o γ)
    (hf : IsBoundedUnder (· ≥ ·) (ae μ) f := by isBoundedDefault)
    (hf_co : IsCoboundedUnder (· ≥ ·) (ae μ) f := by isBoundedDefault)
    (hgf : IsBoundedUnder (· ≥ ·) (ae μ) (fun x => g (f x)) := by isBoundedDefault)
    (hgf_co : IsCoboundedUnder (· ≥ ·) (ae μ) (fun x => g (f x)) := by
      isBoundedDefault) :
    g (essInf f μ) = essInf (fun x => g (f x)) μ :=
  OrderIso.liminf_apply g hf hf_co hgf hgf_co
/-
**essSup_mono_measure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：essSup_mono_measure {f : α -> β} (hμν : ν ≪ μ) (hνf : IsCoboundedUnder (· 
<= ·) (ae ν) f
参数：hμν : ν ≪ μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.limsup_le_limsup_of_le`：limsup_le_limsup_of_le {α β} [Conditional
lyCompleteLattice β] {f g : Filter α} (h : f <= g) {u : α -> β} (hf : f.IsCoboun
dedUnder (· <= ·) u
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.ae_le_iff_absolutelyContinuous`：ae_le_iff_absolute
lyContinuous : ae μ <= ae ν ↔ μ ≪ ν
-/
theorem essSup_mono_measure {f : α → β} (hμν : ν ≪ μ)
    (hνf : IsCoboundedUnder (· ≤ ·) (ae ν) f := by isBoundedDefault)
    (hμf : IsBoundedUnder (· ≤ ·) (ae μ) f := by isBoundedDefault) :
    essSup f ν ≤ essSup f μ :=
  limsup_le_limsup_of_le (Measure.ae_le_iff_absolutelyContinuous.mpr hμν) hνf hμf
/-
**essSup_mono_measure'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：essSup_mono_measure' {f : α -> β} (hμν : ν <= μ) (hνf : IsCoboundedUnder (
· <= ·) (ae ν) f
参数：hμν : ν <= μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `essSup_mono_measure`：essSup_mono_measure {f : α -> β} (hμν : ν ≪ μ) (hνf
 : IsCoboundedUnder (· <= ·) (ae ν) f
· 使用定理 `MeasureTheory.Measure.absolutelyContinuous_of_le`：absolutelyContinuous_o
f_le (h : μ <= ν) : μ ≪ ν
-/
theorem essSup_mono_measure' {f : α → β} (hμν : ν ≤ μ)
    (hνf : IsCoboundedUnder (· ≤ ·) (ae ν) f := by isBoundedDefault)
    (hμf : IsBoundedUnder (· ≤ ·) (ae μ) f := by isBoundedDefault) :
    essSup f ν ≤ essSup f μ :=
  essSup_mono_measure (Measure.absolutelyContinuous_of_le hμν) hνf hμf
/-
**essInf_antitone_measure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：essInf_antitone_measure {f : α -> β} (hμν : μ ≪ ν) (hνf : IsBoundedUnder (
· >= ·) (ae ν) f
参数：hμν : μ ≪ ν。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.liminf_le_liminf_of_le`：liminf_le_liminf_of_le {α β} [Conditional
lyCompleteLattice β] {f g : Filter α} (h : g <= f) {u : α -> β} (hf : f.IsBounde
dUnder (· >= ·) u
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.ae_le_iff_absolutelyContinuous`：ae_le_iff_absolute
lyContinuous : ae μ <= ae ν ↔ μ ≪ ν
-/
theorem essInf_antitone_measure {f : α → β} (hμν : μ ≪ ν)
    (hνf : IsBoundedUnder (· ≥ ·) (ae ν) f := by isBoundedDefault)
    (hμf : IsCoboundedUnder (· ≥ ·) (ae μ) f := by isBoundedDefault) :
    essInf f ν ≤ essInf f μ :=
  liminf_le_liminf_of_le (Measure.ae_le_iff_absolutelyContinuous.mpr hμν) hνf hμf

section TopologicalSpace

variable {γ : Type*} {mγ : MeasurableSpace γ} {f : α → γ} {g : γ → β}

/-
**essSup_comp_le_essSup_map_measure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：essSup_comp_le_essSup_map_measure (hf : AEMeasurable f μ) (hgf : IsCobound
edUnder (· <= ·) (ae μ) (g ∘ f)
参数：hf : AEMeasurable f μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.limsSup_le_limsSup_of_le`：limsSup_le_limsSup_of_le {f g : Filter 
α} (h : f <= g) (hf : f.IsCobounded (· <= ·)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.map_map`：map_map : Filter.map m' (Filter.map m f) = Filter.map (m
' ∘ m) f
· 使用定理 `Filter.map_mono`：map_mono : Monotone (map m)
· 使用定理 `MeasureTheory.Measure.tendsto_ae_map`：tendsto_ae_map {f : α -> β} (hf : 
AEMeasurable f μ) : Tendsto f (ae μ) (ae (μ.map f))
-/
theorem essSup_comp_le_essSup_map_measure (hf : AEMeasurable f μ)
    (hgf : IsCoboundedUnder (· ≤ ·) (ae μ) (g ∘ f) := by isBoundedDefault)
    (hg : IsBoundedUnder (· ≤ ·) (ae (Measure.map f μ)) g := by isBoundedDefault) :
    essSup (g ∘ f) μ ≤ essSup g (Measure.map f μ) := by
  refine limsSup_le_limsSup_of_le ?_ hgf hg
  rw [← map_map]
  exact map_mono (Measure.tendsto_ae_map hf)
/-
**MeasurableEmbedding.essSup_map_measure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeasurableEmbedding.essSup_map_measure (hf : MeasurableEmbedding f) (hg_co
 : IsCoboundedUnder (· <= ·) (ae (Measure.map f μ)) g
参数：hf : MeasurableEmbedding f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Filter.limsSup_le_limsSup`：limsSup_le_limsSup {f g : Filter α} (hf : f.I
sCobounded (· <= ·)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.eventually_map`：eventually_map {P : β -> Prop} : (forallᶠ b in ma
p m f, P b) ↔ forallᶠ a in f, P (m a)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasurableEmbedding.ae_map_iff`：ae_map_iff {p : β -> Prop} {μ : Measure 
α} : (forallᵐ x ∂μ.map f, p x) ↔ forallᵐ x ∂μ, p (f x)
· 使用定理 `essSup_comp_le_essSup_map_measure`：essSup_comp_le_essSup_map_measure (hf
 : AEMeasurable f μ) (hgf : IsCoboundedUnder (· <= ·) (ae μ) (g ∘ f)
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `MeasurableEmbedding.measurable`：∀ {α : Type u_1} {β : Type u_2} [inst : 
MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β},   MeasurableEmbeddi
ng f → Measurable f
-/
theorem MeasurableEmbedding.essSup_map_measure (hf : MeasurableEmbedding f)
    (hg_co : IsCoboundedUnder (· ≤ ·) (ae (Measure.map f μ)) g := by isBoundedDefault)
    (hgf : IsBoundedUnder (· ≤ ·) (ae μ) (g ∘ f) := by isBoundedDefault)
    (hgf_co : IsCoboundedUnder (· ≤ ·) (ae μ) (g ∘ f) := by isBoundedDefault)
    (hg : IsBoundedUnder (· ≤ ·) (ae (Measure.map f μ)) g := by isBoundedDefault) :
    essSup g (Measure.map f μ) = essSup (g ∘ f) μ := by
  refine le_antisymm ?_ (essSup_comp_le_essSup_map_measure hf.measurable.aemeasurable hgf_co hg)
  refine limsSup_le_limsSup hg_co hgf (fun c h_le => ?_)
  rw [eventually_map] at h_le ⊢
  exact hf.ae_map_iff.mpr h_le

variable [MeasurableSpace β] [TopologicalSpace β] [SecondCountableTopology β]
  [OrderClosedTopology β] [OpensMeasurableSpace β]
/-
**essSup_map_measure_of_measurable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：essSup_map_measure_of_measurable (hg : Measurable g) (hf : AEMeasurable f 
μ) (hg_co : IsCoboundedUnder (· <= ·) (ae (Measure.map f μ)) g
参数：hg : Measurable g；hf : AEMeasurable f μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Filter.limsSup_le_limsSup`：limsSup_le_limsSup {f g : Filter α} (hf : f.I
sCobounded (· <= ·)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.eventually_map`：eventually_map {P : β -> Prop} : (forallᶠ b in ma
p m f, P b) ↔ forallᶠ a in f, P (m a)
· 使用定理 `MeasureTheory.ae_map_iff`：ae_map_iff {f : α -> β} (hf : AEMeasurable f μ
) {p : β -> Prop} (hp : MeasurableSet { x | p x }) : (forallᵐ y ∂μ.map f, p y) ↔
 forallᵐ x ∂μ,…
· 使用定理 `measurableSet_le`：measurableSet_le {f g : δ -> α} (hf : Measurable f) (h
g : Measurable g) : MeasurableSet { a | f a <= g a }
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `essSup_comp_le_essSup_map_measure`：essSup_comp_le_essSup_map_measure (hf
 : AEMeasurable f μ) (hgf : IsCoboundedUnder (· <= ·) (ae μ) (g ∘ f)
-/
theorem essSup_map_measure_of_measurable (hg : Measurable g) (hf : AEMeasurable f μ)
    (hg_co : IsCoboundedUnder (· ≤ ·) (ae (Measure.map f μ)) g := by isBoundedDefault)
    (hgf : IsBoundedUnder (· ≤ ·) (ae μ) (g ∘ f) := by isBoundedDefault)
    (hgf_co : IsCoboundedUnder (· ≤ ·) (ae μ) (g ∘ f) := by isBoundedDefault)
    (hg_bdd : IsBoundedUnder (· ≤ ·) (ae (Measure.map f μ)) g := by isBoundedDefault) :
    essSup g (Measure.map f μ) = essSup (g ∘ f) μ := by
  refine le_antisymm ?_ (essSup_comp_le_essSup_map_measure hf hgf_co hg_bdd)
  refine limsSup_le_limsSup hg_co hgf (fun c h_le => ?_)
  rw [eventually_map] at h_le ⊢
  rw [ae_map_iff hf (measurableSet_le hg measurable_const)]
  exact h_le
/-
**essSup_map_measure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：essSup_map_measure (hg : AEMeasurable g (Measure.map f μ)) (hf : AEMeasura
ble f μ) (hg_co : IsCoboundedUnder (· <= ·) (ae (Measure.map f μ)) g
参数：hg : AEMeasurable g (Measure.map f μ)；hf : AEMeasurable f μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.map_congr`：map_congr {m₁ m₂ : α -> β} {f : Filter α} (h : m₁ =ᶠ[f
] m₂) : map m₁ f = map m₂ f
· 使用定理 `AEMeasurable.ae_eq_mk`：ae_eq_mk (h : AEMeasurable f μ) : f =ᵐ[μ] h.mk f
· 使用定理 `MeasureTheory.ae_eq_comp`：ae_eq_comp {f : α -> β} {g g' : β -> δ} (hf : 
AEMeasurable f μ) (h : g =ᵐ[μ.map f] g') : g ∘ f =ᵐ[μ] g' ∘ f
· 使用定理 `essSup_congr_ae`：essSup_congr_ae {f g : α -> β} (hfg : f =ᵐ[μ] g) : essS
up f μ = essSup g μ
· 使用定理 `essSup_map_measure_of_measurable`：essSup_map_measure_of_measurable (hg :
 Measurable g) (hf : AEMeasurable f μ) (hg_co : IsCoboundedUnder (· <= ·) (ae (M
easure.map f μ)) g
· 使用定理 `AEMeasurable.measurable_mk`：measurable_mk (h : AEMeasurable f μ) : Measu
rable (h.mk f)
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
theorem essSup_map_measure (hg : AEMeasurable g (Measure.map f μ)) (hf : AEMeasurable f μ)
    (hg_co : IsCoboundedUnder (· ≤ ·) (ae (Measure.map f μ)) g := by isBoundedDefault)
    (hgf : IsBoundedUnder (· ≤ ·) (ae μ) (g ∘ f) := by isBoundedDefault)
    (hgf_co : IsCoboundedUnder (· ≤ ·) (ae μ) (g ∘ f) := by isBoundedDefault)
    (hg_bdd : IsBoundedUnder (· ≤ ·) (ae (Measure.map f μ)) g := by isBoundedDefault) :
    essSup g (Measure.map f μ) = essSup (g ∘ f) μ := by
  have hg_mk_co : IsCoboundedUnder (· ≤ ·) (ae (Measure.map f μ)) (hg.mk g) := by
    simpa [IsCoboundedUnder, ← map_congr hg.ae_eq_mk]
  have hg_mk_bdd : IsBoundedUnder (· ≤ ·) (ae (Measure.map f μ)) (hg.mk g) := by
    simpa [IsBoundedUnder, ← map_congr hg.ae_eq_mk]
  have h_eq := ae_eq_comp hf hg.ae_eq_mk
  have hg_mk_f : IsBoundedUnder (· ≤ ·) (ae μ) ((hg.mk g) ∘ f) := by
    simpa [IsBoundedUnder, ← map_congr h_eq]
  have hg_mk_f_co : IsCoboundedUnder (· ≤ ·) (ae μ) ((hg.mk g) ∘ f) := by
    simpa [IsCoboundedUnder, ← map_congr h_eq]
  rw [essSup_congr_ae hg.ae_eq_mk,
    essSup_map_measure_of_measurable hg.measurable_mk hf hg_mk_co hg_mk_f hg_mk_f_co hg_mk_bdd]
  exact essSup_congr_ae h_eq.symm

end TopologicalSpace

variable [Nonempty α]

/-
**essSup_eq_ciSup** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：essSup_eq_ciSup (hμ : forall a, μ {a} != 0) (hf : BddAbove (Set.range f)) 
: essSup f μ = ⨆ a, f a
参数：hμ : forall a, μ {a} != 0；hf : BddAbove (Set.range f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `essSup.eq_1`：∀ {α : Type u_1} {β : Type u_2} [inst : ConditionallyComple
teLattice β] {x : MeasurableSpace α} (f : α → β)   (μ : MeasureTheory.Measure α)
,…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.ae_eq_top`：∀ {α : Type u_1} {F : Type u_3} [inst : FunLike
 F (Set α) ENNReal] [inst_1 : MeasureTheory.OuterMeasureClass F α]   {μ : F}, Me
asureTheory.a…
· 使用引理 `Filter.limsup_top_eq_ciSup`：limsup_top_eq_ciSup [Nonempty β] (hu : BddAb
ove (range u)) : limsup u ⊤ = ⨆ i, u i
-/
lemma essSup_eq_ciSup (hμ : ∀ a, μ {a} ≠ 0) (hf : BddAbove (Set.range f)) :
    essSup f μ = ⨆ a, f a := by rw [essSup, ae_eq_top.2 hμ, limsup_top_eq_ciSup hf]
/-
**essInf_eq_ciInf** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：essInf_eq_ciInf (hμ : forall a, μ {a} != 0) (hf : BddBelow (Set.range f)) 
: essInf f μ = ⨅ a, f a
参数：hμ : forall a, μ {a} != 0；hf : BddBelow (Set.range f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `essInf.eq_1`：∀ {α : Type u_1} {β : Type u_2} [inst : ConditionallyComple
teLattice β] {x : MeasurableSpace α} (f : α → β)   (μ : MeasureTheory.Measure α)
,…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.ae_eq_top`：∀ {α : Type u_1} {F : Type u_3} [inst : FunLike
 F (Set α) ENNReal] [inst_1 : MeasureTheory.OuterMeasureClass F α]   {μ : F}, Me
asureTheory.a…
· 使用引理 `Filter.liminf_top_eq_ciInf`：liminf_top_eq_ciInf [Nonempty β] (hu : BddBe
low (range u)) : liminf u ⊤ = ⨅ i, u i
-/
lemma essInf_eq_ciInf (hμ : ∀ a, μ {a} ≠ 0) (hf : BddBelow (Set.range f)) :
    essInf f μ = ⨅ a, f a := by rw [essInf, ae_eq_top.2 hμ, liminf_top_eq_ciInf hf]

variable [MeasurableSingletonClass α]
/-
**essSup_count_eq_ciSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} [inst : Conditiona
llyCompleteLattice β] {f : α → β} [Nonempty α]   [MeasurableSingletonClass α], B
ddAbove (Set.range f) → essSup f MeasureTheory.Measure.count = ⨆ a, f a
参数：Set.range f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `essSup_eq_ciSup`：essSup_eq_ciSup (hμ : forall a, μ {a} != 0) (hf : BddAb
ove (Set.range f)) : essSup f μ = ⨆ a, f a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.count_singleton'`：count_singleton' {a : α} (ha : M
easurableSet ({a} : Set α)) : count ({a} : Set α) = 1
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] lemma essSup_count_eq_ciSup (hf : BddAbove (Set.range f)) :
    essSup f .count = ⨆ a, f a := essSup_eq_ciSup (by simp) hf
/-
**essInf_count_eq_ciInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} [inst : Conditiona
llyCompleteLattice β] {f : α → β} [Nonempty α]   [MeasurableSingletonClass α], B
ddBelow (Set.range f) → essInf f MeasureTheory.Measure.count = ⨅ a, f a
参数：Set.range f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `essInf_eq_ciInf`：essInf_eq_ciInf (hμ : forall a, μ {a} != 0) (hf : BddBe
low (Set.range f)) : essInf f μ = ⨅ a, f a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.count_singleton'`：count_singleton' {a : α} (ha : M
easurableSet ({a} : Set α)) : count ({a} : Set α) = 1
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] lemma essInf_count_eq_ciInf (hf : BddBelow (Set.range f)) :
    essInf f .count = ⨅ a, f a := essInf_eq_ciInf (by simp) hf
/-
**essSup_uniformOn_eq_ciSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} [inst : Conditiona
llyCompleteLattice β] {f : α → β} [Nonempty α]   [MeasurableSingletonClass α] [F
inite α],   BddAbove (Set.range f) → essSup f (ProbabilityTheory.uniformOn Set.u
niv) = ⨆ a, f a
参数：Set.range f；ProbabilityTheory.uniformOn Set.univ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `essSup_eq_ciSup`：essSup_eq_ciSup (hμ : forall a, μ {a} != 0) (hf : BddAb
ove (Set.range f)) : essSup f μ = ⨆ a, f a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.cond_apply`：cond_apply (hms : MeasurableSet s) (μ : Me
asure Ω) (t : Set Ω) : μ[t | s] = (μ s)⁻¹ * μ (s inter t)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `MeasureTheory.Measure.count_univ`：count_univ : count (univ : Set α) = EN
at.card α
· 使用定理 `Set.inter_singleton_of_mem`：∀ {α : Type u_1} {s : Set α} {a : α}, a ∈ s 
→ s ∩ {a} = {a}
· 使用定理 `MeasureTheory.Measure.count_singleton'`：count_singleton' {a : α} (ha : M
easurableSet ({a} : Set α)) : count ({a} : Set α) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
@[simp] lemma essSup_uniformOn_eq_ciSup [Finite α] (hf : BddAbove (Set.range f)) :
    essSup f (uniformOn univ) = ⨆ a, f a :=
  essSup_eq_ciSup (by simpa [uniformOn, cond_apply]) hf
/-
**essInf_cond_count_eq_ciInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} [inst : Conditiona
llyCompleteLattice β] {f : α → β} [Nonempty α]   [MeasurableSingletonClass α] [F
inite α],   BddBelow (Set.range f) → essInf f (ProbabilityTheory.uniformOn Set.u
niv) = ⨅ a, f a
参数：Set.range f；ProbabilityTheory.uniformOn Set.univ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `essInf_eq_ciInf`：essInf_eq_ciInf (hμ : forall a, μ {a} != 0) (hf : BddBe
low (Set.range f)) : essInf f μ = ⨅ a, f a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.cond_apply`：cond_apply (hms : MeasurableSet s) (μ : Me
asure Ω) (t : Set Ω) : μ[t | s] = (μ s)⁻¹ * μ (s inter t)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `MeasureTheory.Measure.count_univ`：count_univ : count (univ : Set α) = EN
at.card α
· 使用定理 `Set.inter_singleton_of_mem`：∀ {α : Type u_1} {s : Set α} {a : α}, a ∈ s 
→ s ∩ {a} = {a}
· 使用定理 `MeasureTheory.Measure.count_singleton'`：count_singleton' {a : α} (ha : M
easurableSet ({a} : Set α)) : count ({a} : Set α) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
@[simp] lemma essInf_cond_count_eq_ciInf [Finite α] (hf : BddBelow (Set.range f)) :
    essInf f (uniformOn univ) = ⨅ a, f a :=
  essInf_eq_ciInf (by simpa [uniformOn, cond_apply]) hf

end ConditionallyCompleteLattice

section ConditionallyCompleteLinearOrder

variable [ConditionallyCompleteLinearOrder β] {x : β} {f : α → β}

/-
**essSup_eq_sInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：essSup_eq_sInf {m : MeasurableSpace α} (μ : Measure α) (f : α -> β) : essS
up f μ = sInf { a | μ { x | a < f x } = 0 }
参数：μ : Measure α；f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem essSup_eq_sInf {m : MeasurableSpace α} (μ : Measure α) (f : α → β) :
    essSup f μ = sInf { a | μ { x | a < f x } = 0 } := by
  dsimp [essSup, limsup, limsSup]
  simp only [eventually_map, ae_iff, not_le]
/-
**essInf_eq_sSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：essInf_eq_sSup {m : MeasurableSpace α} (μ : Measure α) (f : α -> β) : essI
nf f μ = sSup { a | μ { x | f x < a } = 0 }
参数：μ : Measure α；f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem essInf_eq_sSup {m : MeasurableSpace α} (μ : Measure α) (f : α → β) :
    essInf f μ = sSup { a | μ { x | f x < a } = 0 } := by
  dsimp [essInf, liminf, limsInf]
  simp only [eventually_map, ae_iff, not_le]
/-
**ae_lt_of_essSup_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ae_lt_of_essSup_lt (hx : essSup f μ < x) (hf : IsBoundedUnder (· <= ·) (ae
 μ) f
参数：hx : essSup f μ < x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.eventually_lt_of_limsup_lt`：eventually_lt_of_limsup_lt {f : Filte
r α} [ConditionallyCompleteLinearOrder β] {u : α -> β} {b : β} (h : limsup u f <
 b) (hu : f.IsBoundedUn…
-/
theorem ae_lt_of_essSup_lt (hx : essSup f μ < x)
    (hf : IsBoundedUnder (· ≤ ·) (ae μ) f := by isBoundedDefault) :
    ∀ᵐ y ∂μ, f y < x :=
  eventually_lt_of_limsup_lt hx hf
/-
**ae_lt_of_lt_essInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ae_lt_of_lt_essInf (hx : x < essInf f μ) (hf : IsBoundedUnder (· >= ·) (ae
 μ) f
参数：hx : x < essInf f μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.eventually_lt_of_lt_liminf`：eventually_lt_of_lt_liminf {f : Filte
r α} [ConditionallyCompleteLinearOrder β] {u : α -> β} {b : β} (h : b < liminf u
 f) (hu : f.IsBoundedUn…
-/
theorem ae_lt_of_lt_essInf (hx : x < essInf f μ)
    (hf : IsBoundedUnder (· ≥ ·) (ae μ) f := by isBoundedDefault) :
    ∀ᵐ y ∂μ, x < f y :=
  eventually_lt_of_lt_liminf hx hf

variable [TopologicalSpace β] [FirstCountableTopology β] [OrderTopology β]
/-
**ae_le_essSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ae_le_essSup (hf : IsBoundedUnder (· <= ·) (ae μ) f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `eventually_le_limsup`：eventually_le_limsup (hf : IsBoundedUnder (· <= ·)
 f u
· 使用定理 `MeasureTheory.instCountableInterFilterAe`：∀ {α : Type u_1} {F : Type u_2
} [inst : FunLike F (Set α) ENNReal] [inst_1 : MeasureTheory.OuterMeasureClass F
 α]   (μ : F), CountableInterF…
-/
theorem ae_le_essSup
    (hf : IsBoundedUnder (· ≤ ·) (ae μ) f := by isBoundedDefault) :
    ∀ᵐ y ∂μ, f y ≤ essSup f μ :=
  eventually_le_limsup hf
/-
**ae_essInf_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ae_essInf_le (hf : IsBoundedUnder (· >= ·) (ae μ) f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `eventually_liminf_le`：eventually_liminf_le (hf : IsBoundedUnder (· >= ·)
 f u
· 使用定理 `MeasureTheory.instCountableInterFilterAe`：∀ {α : Type u_1} {F : Type u_2
} [inst : FunLike F (Set α) ENNReal] [inst_1 : MeasureTheory.OuterMeasureClass F
 α]   (μ : F), CountableInterF…
-/
theorem ae_essInf_le
    (hf : IsBoundedUnder (· ≥ ·) (ae μ) f := by isBoundedDefault) :
    ∀ᵐ y ∂μ, essInf f μ ≤ f y :=
  eventually_liminf_le hf
/-
**meas_essSup_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：meas_essSup_lt (hf : IsBoundedUnder (· <= ·) (ae μ) f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ae_le_essSup`：ae_le_essSup (hf : IsBoundedUnder (· <= ·) (ae μ) f
-/
theorem meas_essSup_lt
    (hf : IsBoundedUnder (· ≤ ·) (ae μ) f := by isBoundedDefault) :
    μ { y | essSup f μ < f y } = 0 := by
  simp_rw [← not_le]
  exact ae_le_essSup hf
/-
**meas_lt_essInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：meas_lt_essInf (hf : IsBoundedUnder (· >= ·) (ae μ) f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ae_essInf_le`：ae_essInf_le (hf : IsBoundedUnder (· >= ·) (ae μ) f
-/
theorem meas_lt_essInf
    (hf : IsBoundedUnder (· ≥ ·) (ae μ) f := by isBoundedDefault) :
    μ { y | f y < essInf f μ } = 0 := by
  simp_rw [← not_le]
  exact ae_essInf_le hf

end ConditionallyCompleteLinearOrder

section CompleteLattice

variable [CompleteLattice β]

@[simp]
/-
**essSup_measure_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：essSup_measure_zero {m : MeasurableSpace α} {f : α -> β} : essSup f (0 : M
easure α) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.ae_zero`：ae_zero {_m0 : MeasurableSpace α} : ae (0 : Measu
re α) = ⊥
· 使用定理 `Filter.map_bot`：∀ {α : Type u_1} {β : Type u_2} {m : α → β}, Filter.map 
m ⊥ = ⊥
-/
theorem essSup_measure_zero {m : MeasurableSpace α} {f : α → β} : essSup f (0 : Measure α) = ⊥ :=
  le_bot_iff.mp (sInf_le (by simp))

@[simp]
/-
**essInf_measure_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：essInf_measure_zero {_ : MeasurableSpace α} {f : α -> β} : essInf f (0 : M
easure α) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `essSup_measure_zero`：essSup_measure_zero {m : MeasurableSpace α} {f : α 
-> β} : essSup f (0 : Measure α) = ⊥
-/
theorem essInf_measure_zero {_ : MeasurableSpace α} {f : α → β} : essInf f (0 : Measure α) = ⊤ :=
  @essSup_measure_zero α βᵒᵈ _ _ _
/-
**essSup_const_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：essSup_const_bot : essSup (fun _ : α => (⊥ : β)) μ = (⊥ : β)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.limsup_const_bot`：limsup_const_bot {f : Filter β} : limsup (fun _
 : β => (⊥ : α)) f = (⊥ : α)
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
theorem essSup_const_bot : essSup (fun _ : α => (⊥ : β)) μ = (⊥ : β) :=
  limsup_const_bot
/-
**essInf_const_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：essInf_const_top : essInf (fun _ : α => (⊤ : β)) μ = (⊤ : β)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.liminf_const_top`：liminf_const_top {f : Filter β} : liminf (fun _
 : β => (⊤ : α)) f = (⊤ : α)
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
theorem essInf_const_top : essInf (fun _ : α => (⊤ : β)) μ = (⊤ : β) :=
  liminf_const_top
/-
**essSup_eq_iSup** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：essSup_eq_iSup (hμ : forall a, μ {a} != 0) (f : α -> β) : essSup f μ = ⨆ i
, f i
参数：hμ : forall a, μ {a} != 0；f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `essSup.eq_1`：∀ {α : Type u_1} {β : Type u_2} [inst : ConditionallyComple
teLattice β] {x : MeasurableSpace α} (f : α → β)   (μ : MeasureTheory.Measure α)
,…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.ae_eq_top`：∀ {α : Type u_1} {F : Type u_3} [inst : FunLike
 F (Set α) ENNReal] [inst_1 : MeasureTheory.OuterMeasureClass F α]   {μ : F}, Me
asureTheory.a…
· 使用定理 `Filter.limsup_top_eq_iSup`：∀ {α : Type u_1} {β : Type u_2} [inst : Compl
eteLattice α] (u : β → α), Filter.limsup u ⊤ = ⨆ i, u i
-/
lemma essSup_eq_iSup (hμ : ∀ a, μ {a} ≠ 0) (f : α → β) : essSup f μ = ⨆ i, f i := by
  rw [essSup, ae_eq_top.2 hμ, limsup_top_eq_iSup]
/-
**essSup_le_iSup** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：essSup_le_iSup {f : α -> β} : essSup f μ <= ⨆ i, f i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `essSup_le_of_ae_le`：essSup_le_of_ae_le {f : α -> β} (c : β) (hf : f <=ᵐ[
μ] fun _ => c) (hfbdd : IsCoboundedUnder (· <= ·) (ae μ) f
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `Filter.isCobounded_le_of_bot`：isCobounded_le_of_bot [LE α] [OrderBot α] 
{f : Filter α} : f.IsCobounded (· <= ·)
-/
lemma essSup_le_iSup {f : α → β} : essSup f μ ≤ ⨆ i, f i :=
  essSup_le_of_ae_le _ (ae_of_all _ (le_iSup f))
/-
**essInf_eq_iInf** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：essInf_eq_iInf (hμ : forall a, μ {a} != 0) (f : α -> β) : essInf f μ = ⨅ i
, f i
参数：hμ : forall a, μ {a} != 0；f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `essInf.eq_1`：∀ {α : Type u_1} {β : Type u_2} [inst : ConditionallyComple
teLattice β] {x : MeasurableSpace α} (f : α → β)   (μ : MeasureTheory.Measure α)
,…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.ae_eq_top`：∀ {α : Type u_1} {F : Type u_3} [inst : FunLike
 F (Set α) ENNReal] [inst_1 : MeasureTheory.OuterMeasureClass F α]   {μ : F}, Me
asureTheory.a…
· 使用定理 `Filter.liminf_top_eq_iInf`：∀ {α : Type u_1} {β : Type u_2} [inst : Compl
eteLattice α] (u : β → α), Filter.liminf u ⊤ = ⨅ i, u i
-/
lemma essInf_eq_iInf (hμ : ∀ a, μ {a} ≠ 0) (f : α → β) : essInf f μ = ⨅ i, f i := by
  rw [essInf, ae_eq_top.2 hμ, liminf_top_eq_iInf]
/-
**essSup_count** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} [inst : CompleteLa
ttice β] [MeasurableSingletonClass α]   (f : α → β), essSup f MeasureTheory.Meas
ure.count = ⨆ i, f i
参数：f : α → β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `essSup_eq_iSup`：essSup_eq_iSup (hμ : forall a, μ {a} != 0) (f : α -> β) 
: essSup f μ = ⨆ i, f i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.count_singleton'`：count_singleton' {a : α} (ha : M
easurableSet ({a} : Set α)) : count ({a} : Set α) = 1
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] lemma essSup_count [MeasurableSingletonClass α] (f : α → β) : essSup f .count = ⨆ i, f i :=
  essSup_eq_iSup (by simp) _
/-
**essInf_count** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} [inst : CompleteLa
ttice β] [MeasurableSingletonClass α]   (f : α → β), essInf f MeasureTheory.Meas
ure.count = ⨅ i, f i
参数：f : α → β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `essInf_eq_iInf`：essInf_eq_iInf (hμ : forall a, μ {a} != 0) (f : α -> β) 
: essInf f μ = ⨅ i, f i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.count_singleton'`：count_singleton' {a : α} (ha : M
easurableSet ({a} : Set α)) : count ({a} : Set α) = 1
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] lemma essInf_count [MeasurableSingletonClass α] (f : α → β) : essInf f .count = ⨅ i, f i :=
  essInf_eq_iInf (by simp) _

end CompleteLattice

section CompleteLinearOrder

variable [CompleteLinearOrder β]

/-
**iSup_eq_essSup** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：iSup_eq_essSup {f : α -> β} (h : forall ⦃x a⦄, a < f x -> μ {y | a < f y} 
!= 0) : ⨆ x, f x = essSup f μ
参数：h : forall ⦃x a⦄, a < f x -> μ {y | a < f y} != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `essSup_eq_sInf`：essSup_eq_sInf {m : MeasurableSpace α} (μ : Measure α) (
f : α -> β) : essSup f μ = sInf { a | μ { x | a < f x } = 0 }
· 使用定理 `le_sInf`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, (∀ b ∈ s, a ≤ b) → a ≤ sInf s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用引理 `essSup_le_iSup`：essSup_le_iSup {f : α -> β} : essSup f μ <= ⨆ i, f i
-/
lemma iSup_eq_essSup {f : α → β} (h : ∀ ⦃x a⦄, a < f x → μ {y | a < f y} ≠ 0) :
    ⨆ x, f x = essSup f μ := by
  apply le_antisymm (iSup_le _) essSup_le_iSup
  intro i
  rw [essSup_eq_sInf]
  apply le_sInf
  intro b hb
  exact not_lt.mp fun a ↦ h a hb

end CompleteLinearOrder

namespace ENNReal

variable {f : α → ℝ≥0∞}

/-
**ENNReal.essSup_piecewise** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：essSup_piecewise {s : Set α} [DecidablePred (· in s)] {g} (hs : Measurable
Set s) : essSup (s.piecewise f g) μ = max (essSup f (μ.restrict s)) (essSup g (μ
.restrict sᶜ))
参数：· in s；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Filter.limsup_piecewise`：limsup_piecewise {s : Set β} [DecidablePred (· 
in s)] {v} : limsup (s.piecewise u v) f = blimsup u f (· in s) ⊔ blimsup v f (· 
∉ s)
· 使用引理 `Filter.blimsup_eq_limsup`：blimsup_eq_limsup {f : Filter β} {u : β -> α} 
{p : β -> Prop} : blimsup u f p = limsup u (f ⊓ 𝓟 {x | p x})
· 使用定理 `MeasureTheory.ae_restrict_eq`：ae_restrict_eq (hs : MeasurableSet s) : ae
 (μ.restrict s) = ae μ ⊓ 𝓟 s
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
-/
lemma essSup_piecewise {s : Set α} [DecidablePred (· ∈ s)] {g} (hs : MeasurableSet s) :
    essSup (s.piecewise f g) μ = max (essSup f (μ.restrict s)) (essSup g (μ.restrict sᶜ)) := by
  simp only [essSup, limsup_piecewise, blimsup_eq_limsup, ae_restrict_eq, hs, hs.compl]; rfl
/-
**ENNReal.essSup_indicator_eq_essSup_restrict** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal
`。
形式化陈述：essSup_indicator_eq_essSup_restrict {s : Set α} {f : α -> Real>=0∞} (hs : 
MeasurableSet s) : essSup (s.indicator f) μ = essSup f (μ.restrict s)
参数：hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ENNReal.essSup_piecewise`：essSup_piecewise {s : Set α} [DecidablePred (·
 in s)] {g} (hs : MeasurableSet s) : essSup (s.piecewise f g) μ = max (essSup f 
(μ.restrict s)…
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.limsup_const_bot`：limsup_const_bot {f : Filter β} : limsup (fun _
 : β => (⊥ : α)) f = (⊥ : α)
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
-/
theorem essSup_indicator_eq_essSup_restrict {s : Set α} {f : α → ℝ≥0∞} (hs : MeasurableSet s) :
    essSup (s.indicator f) μ = essSup f (μ.restrict s) := by
  classical
  simp only [← piecewise_eq_indicator, essSup_piecewise hs, max_eq_left_iff]
  exact limsup_const_bot.trans_le zero_le
/-
**ENNReal.ae_le_essSup** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：ae_le_essSup (f : α -> Real>=0∞) : forallᵐ y ∂μ, f y <= essSup f μ
参数：f : α -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.eventually_le_limsup`：eventually_le_limsup [CountableInterFilter
 f] (u : α -> Real>=0∞) : forallᶠ y in f, u y <= f.limsup u
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.instCountableInterFilterAe`：∀ {α : Type u_1} {F : Type u_2
} [inst : FunLike F (Set α) ENNReal] [inst_1 : MeasureTheory.OuterMeasureClass F
 α]   (μ : F), CountableInterF…
-/
theorem ae_le_essSup (f : α → ℝ≥0∞) : ∀ᵐ y ∂μ, f y ≤ essSup f μ :=
  eventually_le_limsup f

@[simp]
/-
**ENNReal.essSup_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：essSup_eq_zero_iff : essSup f μ = 0 ↔ f =ᵐ[μ] 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.limsup_eq_zero_iff`：limsup_eq_zero_iff [CountableInterFilter f] 
{u : α -> Real>=0∞} : f.limsup u = 0 ↔ u =ᶠ[f] 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.instCountableInterFilterAe`：∀ {α : Type u_1} {F : Type u_2
} [inst : FunLike F (Set α) ENNReal] [inst_1 : MeasureTheory.OuterMeasureClass F
 α]   (μ : F), CountableInterF…
-/
theorem essSup_eq_zero_iff : essSup f μ = 0 ↔ f =ᵐ[μ] 0 :=
  limsup_eq_zero_iff
/-
**ENNReal.essSup_const_mul** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：essSup_const_mul {a : Real>=0∞} : essSup (fun x : α => a * f x) μ = a * es
sSup f μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.limsup_const_mul`：limsup_const_mul [CountableInterFilter f] {u :
 α -> Real>=0∞} {a : Real>=0∞} : f.limsup (a * u ·) = a * f.limsup u
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.instCountableInterFilterAe`：∀ {α : Type u_1} {F : Type u_2
} [inst : FunLike F (Set α) ENNReal] [inst_1 : MeasureTheory.OuterMeasureClass F
 α]   (μ : F), CountableInterF…
-/
theorem essSup_const_mul {a : ℝ≥0∞} : essSup (fun x : α => a * f x) μ = a * essSup f μ :=
  limsup_const_mul
/-
**ENNReal.essSup_mul_le** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：essSup_mul_le (f g : α -> Real>=0∞) : essSup (f * g) μ <= essSup f μ * ess
Sup g μ
参数：f g : α -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.limsup_mul_le`：limsup_mul_le [CountableInterFilter f] (u v : α -
> Real>=0∞) : f.limsup (u * v) <= f.limsup u * f.limsup v
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.instCountableInterFilterAe`：∀ {α : Type u_1} {F : Type u_2
} [inst : FunLike F (Set α) ENNReal] [inst_1 : MeasureTheory.OuterMeasureClass F
 α]   (μ : F), CountableInterF…
-/
theorem essSup_mul_le (f g : α → ℝ≥0∞) : essSup (f * g) μ ≤ essSup f μ * essSup g μ :=
  limsup_mul_le f g
/-
**ENNReal.essSup_add_le** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：essSup_add_le (f g : α -> Real>=0∞) : essSup (f + g) μ <= essSup f μ + ess
Sup g μ
参数：f g : α -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.limsup_add_le`：limsup_add_le [CountableInterFilter f] (u v : α -
> Real>=0∞) : f.limsup (u + v) <= f.limsup u + f.limsup v
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.instCountableInterFilterAe`：∀ {α : Type u_1} {F : Type u_2
} [inst : FunLike F (Set α) ENNReal] [inst_1 : MeasureTheory.OuterMeasureClass F
 α]   (μ : F), CountableInterF…
-/
theorem essSup_add_le (f g : α → ℝ≥0∞) : essSup (f + g) μ ≤ essSup f μ + essSup g μ :=
  limsup_add_le f g
/-
**ENNReal.essSup_liminf_le** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：essSup_liminf_le {ι} [Countable ι] [Preorder ι] (f : ι -> α -> Real>=0∞) :
 essSup (fun x => atTop.liminf fun n => f n x) μ <= atTop.liminf fun n => essSup
 (fun x => f n x) μ
参数：f : ι -> α -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.limsup_liminf_le_liminf_limsup`：limsup_liminf_le_liminf_limsup {
β} [Countable β] {f : Filter α} [CountableInterFilter f] {g : Filter β} (u : α -
> β -> Real>=0∞) : (f.limsup…
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.instCountableInterFilterAe`：∀ {α : Type u_1} {F : Type u_2
} [inst : FunLike F (Set α) ENNReal] [inst_1 : MeasureTheory.OuterMeasureClass F
 α]   (μ : F), CountableInterF…
-/
theorem essSup_liminf_le {ι} [Countable ι] [Preorder ι] (f : ι → α → ℝ≥0∞) :
    essSup (fun x => atTop.liminf fun n => f n x) μ ≤
      atTop.liminf fun n => essSup (fun x => f n x) μ := by
  simp_rw [essSup]
  exact ENNReal.limsup_liminf_le_liminf_limsup fun a b => f b a
/-
**ENNReal.coe_essSup** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：coe_essSup {f : α -> Real>=0} (hf : IsBoundedUnder (· <= ·) (ae μ) f) : ((
essSup f μ : Real>=0) : Real>=0∞) = essSup (fun x => (f x : Real>=0∞)) μ
参数：hf : IsBoundedUnder (· <= ·) (ae μ) f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ENNReal.coe_sInf`：coe_sInf {s : Set Real>=0} (hs : s.Nonempty) : (↑(sInf
 s) : Real>=0∞) = ⨅ a in s, ↑a
· 使用引理 `eq_of_forall_le_iff`：eq_of_forall_le_iff (H : forall c, c <= a ↔ c <= b)
 : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coe_essSup {f : α → ℝ≥0} (hf : IsBoundedUnder (· ≤ ·) (ae μ) f) :
    ((essSup f μ : ℝ≥0) : ℝ≥0∞) = essSup (fun x => (f x : ℝ≥0∞)) μ :=
  (ENNReal.coe_sInf <| hf).trans <|
    eq_of_forall_le_iff fun r => by
      simp [essSup, limsup, limsSup, eventually_map, ENNReal.forall_ennreal]; rfl
/-
**ENNReal.ofReal_essSup** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：ofReal_essSup {f : α -> Real} (h₁ : IsCoboundedUnder (· <= ·) (ae μ) f) (h
₂ : IsBoundedUnder (· <= ·) (ae μ) f) : ENNReal.ofReal (essSup f μ) = essSup (fu
n a => .ofReal (f a)) μ
参数：h₁ : IsCoboundedUnder (· <= ·) (ae μ) f；h₂ : IsBoundedUnder (· <= ·) (ae μ) f
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `ENNReal.ofReal_limsup`：ofReal_limsup {u : α -> Real} (h₁ : IsCoboundedUn
der (· <= ·) f u
-/
lemma ofReal_essSup {f : α → ℝ} (h₁ : IsCoboundedUnder (· ≤ ·) (ae μ) f)
    (h₂ : IsBoundedUnder (· ≤ ·) (ae μ) f) :
    ENNReal.ofReal (essSup f μ) = essSup (fun a ↦ .ofReal (f a)) μ := ENNReal.ofReal_limsup
/-
**ENNReal.toReal_essSup** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：toReal_essSup {f : α -> Real>=0∞} (h₁ : forallᵐ a ∂μ, f a != ⊤) (h₂ : IsBo
undedUnder (· <= ·) (ae μ) fun i => (f i).toReal) : (essSup f μ).toReal = essSup
 (fun a => (f a).toReal) μ
参数：h₁ : forallᵐ a ∂μ, f a != ⊤；h₂ : IsBoundedUnder (· <= ·) (ae μ) fun i => (f i
).toReal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `eq_zero_or_neZero`：eq_zero_or_neZero (a : R) : a = 0 ∨ NeZero a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.ae_zero`：ae_zero {_m0 : MeasurableSpace α} : ae (0 : Measu
re α) = ⊥
· 使用定理 `Filter.map_bot`：∀ {α : Type u_1} {β : Type u_2} {m : α → β}, Filter.map 
m ⊥ = ⊥
· 使用定理 `sInf_univ`：∀ {α : Type u_1} [inst : CompleteLattice α], sInf Set.univ = 
⊥
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `csInf_of_not_bddBelow`：∀ {α : Type u_1} [inst : ConditionallyCompleteLin
earOrder α] {s : Set α}, ¬BddBelow s → sInf s = sInf ∅
· 使用定理 `instNoBotOrderOfNoMinOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMinO
rder α], NoBotOrder α
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Real.sInf_empty`：sInf_empty : sInf (∅ : Set Real) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ENNReal.toReal_limsup`：toReal_limsup {u : α -> Real>=0∞} (h₁ : forallᶠ a
 in f, u a != ∞) (h₂ : IsBoundedUnder (· <= ·) f fun a => (u a).toReal
-/
lemma toReal_essSup {f : α → ℝ≥0∞} (h₁ : ∀ᵐ a ∂μ, f a ≠ ⊤)
    (h₂ : IsBoundedUnder (· ≤ ·) (ae μ) fun i ↦ (f i).toReal) :
    (essSup f μ).toReal = essSup (fun a ↦ (f a).toReal) μ := by
  obtain rfl | hμ := eq_zero_or_neZero μ
  · simp [essSup, limsup, limsSup]
  · exact ENNReal.toReal_limsup h₁
/-
**ENNReal.essSup_restrict_eq_of_support_subset** 是 Mathlib 中的一个引理，位于命名空间 `ENNRea
l`。
形式化陈述：essSup_restrict_eq_of_support_subset {s : Set α} {f : α -> Real>=0∞} (hsf 
: f.support subseteq s) : essSup f (μ.restrict s) = essSup f μ
参数：hsf : f.support subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `essSup_mono_measure'`：essSup_mono_measure' {f : α -> β} (hμν : ν <= μ) (
hνf : IsCoboundedUnder (· <= ·) (ae ν) f
· 使用定理 `MeasureTheory.Measure.restrict_le_self`：restrict_le_self : μ.restrict s 
<= μ
· 使用定理 `Filter.isCobounded_le_of_bot`：isCobounded_le_of_bot [LE α] [OrderBot α] 
{f : Filter α} : f.IsCobounded (· <= ·)
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.isBounded_le_of_top`：isBounded_le_of_top [LE α] [OrderTop α] {f :
 Filter α} : f.IsBounded (· <= ·)
· 使用定理 `le_of_forall_lt`：le_of_forall_lt (H : forall c, c < a -> c < b) : a <= b
· 使用定理 `exists_between`：exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a
₁ < a₂ -> exists a, a₁ < a ∧ a < a₂
· 使用定理 `ENNReal.instDenselyOrdered`：DenselyOrdered ENNReal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_apply_self`：restrict_apply_self (s : Set 
α) : (μ.restrict s) s = μ s
· 使用定理 `notMem_of_lt_csInf`：notMem_of_lt_csInf {x : α} {s : Set α} (h : x < sInf
 s) (hs : BddBelow s) : x ∉ s
· 使用定理 `essSup_eq_sInf`：essSup_eq_sInf {m : MeasurableSpace α} (μ : Measure α) (
f : α -> β) : essSup f μ = sInf { a | μ { x | a < f x } = 0 }
· 使用定理 `OrderBot.bddBelow`：∀ {α : Type u_1} [inst : Preorder α] [OrderBot α] (s 
: Set α), BddBelow s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `bot_lt_iff_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : Orde
rBot α] {a : α}, ⊥ < a ↔ a ≠ ⊥
· 使用定理 `MeasureTheory.Measure.restrict_mono`：restrict_mono {_m0 : MeasurableSpac
e α} ⦃s s' : Set α⦄ (hs : s subseteq s') ⦃μ ν : Measure α⦄ (hμν : μ <= ν) : μ.re
strict s <= ν.restrict s'
· 使用定理 `subset_trans`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preor
der α] {a b c : α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `le_sInf`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, (∀ b ∈ s, a ≤ b) → a ≤ sInf s
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
-/
lemma essSup_restrict_eq_of_support_subset {s : Set α} {f : α → ℝ≥0∞} (hsf : f.support ⊆ s) :
    essSup f (μ.restrict s) = essSup f μ := by
  apply le_antisymm (essSup_mono_measure' Measure.restrict_le_self)
  apply le_of_forall_lt (fun c hc ↦ ?_)
  obtain ⟨d, cd, hd⟩ : ∃ d, c < d ∧ d < essSup f μ := exists_between hc
  let t := {x | d < f x}
  have A : 0 < (μ.restrict t) t := by
    simp only [Measure.restrict_apply_self]
    rw [essSup_eq_sInf] at hd
    have : d ∉ {a | μ {x | a < f x} = 0} := notMem_of_lt_csInf hd (OrderBot.bddBelow _)
    exact bot_lt_iff_ne_bot.2 this
  have B : 0 < (μ.restrict s) t := by
    have : μ.restrict t ≤ μ.restrict s := by
      apply Measure.restrict_mono _ le_rfl
      apply subset_trans _ hsf
      intro x (hx : d < f x)
      exact (lt_of_le_of_lt bot_le hx).ne'
    exact lt_of_lt_of_le A (this _)
  apply cd.trans_le
  rw [essSup_eq_sInf]
  apply le_sInf (fun b hb ↦ ?_)
  contrapose! hb
  exact ne_of_gt (B.trans_le (measure_mono (fun x hx ↦ hb.trans hx)))

end ENNReal

