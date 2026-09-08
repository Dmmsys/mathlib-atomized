/-
Copyright (c) 2022 Rémy Degenne, Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Kexing Ying
-/
module

public import Mathlib.MeasureTheory.Function.Egorov
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Convergence in measure

We define convergence in measure which is one of the many notions of convergence in probability.
A sequence of functions `f` is said to converge in measure to some function `g`
if for all `ε > 0`, the measure of the set `{x | ε ≤ edist (f i x) (g x)}` tends to 0 as `i`
converges along some given filter `l`.

Convergence in measure is most notably used in the formulation of the weak law of large numbers
and is also useful in theorems such as the Vitali convergence theorem. This file provides some
basic lemmas for working with convergence in measure and establishes some relations between
convergence in measure and other notions of convergence.

## Main definitions

* `MeasureTheory.TendstoInMeasure (μ : Measure α) (f : ι → α → E) (g : α → E)`: `f` converges
  in `μ`-measure to `g`.

## Main results

* `MeasureTheory.tendstoInMeasure_of_tendsto_ae`: convergence almost everywhere in a finite
  measure space implies convergence in measure.
* `MeasureTheory.TendstoInMeasure.exists_seq_tendsto_ae`: if `f` is a sequence of functions
  which converges in measure to `g`, then `f` has a subsequence which converges almost
  everywhere to `g`.
* `MeasureTheory.exists_seq_tendstoInMeasure_atTop_iff`: for a sequence of functions `f`,
  convergence in measure is equivalent to the fact that every subsequence has another subsequence
  that converges almost surely.
* `MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm`: convergence in Lp implies convergence
  in measure.
-/

@[expose] public section


open TopologicalSpace Filter

open scoped NNReal ENNReal MeasureTheory Topology

namespace MeasureTheory

variable {α ι κ E : Type*} {m : MeasurableSpace α} {μ : Measure α}

/-- A sequence of functions `f` is said to converge in measure to some function `g` if for all
`ε > 0`, the measure of the set `{x | ε ≤ dist (f i x) (g x)}` tends to 0 as `i` converges along
some given filter `l`. -/
/-
**MeasureTheory.TendstoInMeasure** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：TendstoInMeasure [EDist E] {_ : MeasurableSpace α} (μ : Measure α) (f : ι 
-> α -> E) (l : Filter ι) (g : α -> E) : Prop
参数：μ : Measure α；f : ι -> α -> E；l : Filter ι；g : α -> E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A sequence of functions `f` is said to converge in measure to some function `g` 
if for all
`ε > 0`, the measure of the set `{x | ε ≤ dist (f i x) (g x)}` tends to 0 as `i`
 converges along
some given filter `l`.
-/
def TendstoInMeasure [EDist E] {_ : MeasurableSpace α} (μ : Measure α) (f : ι → α → E)
    (l : Filter ι) (g : α → E) : Prop :=
  ∀ ε, 0 < ε → Tendsto (fun i => μ { x | ε ≤ edist (f i x) (g x) }) l (𝓝 0)
/-
**MeasureTheory.tendstoInMeasure_of_ne_top** 是 Mathlib 中的一个引理，位于命名空间 `MeasureThe
ory`。
形式化陈述：tendstoInMeasure_of_ne_top [EDist E] {f : ι -> α -> E} {l : Filter ι} {g :
 α -> E} (h : forall ε, 0 < ε -> ε != ∞ -> Tendsto (fun i => μ { x | ε <= edist 
(f i x) (g x) }) l (𝓝 0)) : TendstoInMeasure μ f l g
参数：h : forall ε, 0 < ε -> ε != ∞ -> Tendsto (fun i => μ { x | ε <= edist (f i x)
 (g x) }) l (𝓝 0)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `tendsto_of_tendsto_of_tendsto_of_le_of_le`：tendsto_of_tendsto_of_tendsto
_of_le_of_le [OrderTopology α] {f g h : β -> α} {b : Filter β} {a : α} (hg : Ten
dsto g b (𝓝 a)) (hh : Tendsto h…
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.ofPred_subset_ofPred_of_imp`：∀ {α : Type u} {p q : α → Prop}, (∀ (a 
: α), p a → q a) → {a | p a} ⊆ {a | q a}
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma tendstoInMeasure_of_ne_top [EDist E] {f : ι → α → E} {l : Filter ι} {g : α → E}
    (h : ∀ ε, 0 < ε → ε ≠ ∞ → Tendsto (fun i => μ { x | ε ≤ edist (f i x) (g x) }) l (𝓝 0)) :
    TendstoInMeasure μ f l g := by
  intro ε hε
  by_cases hε_top : ε = ∞
  · have h1 : Tendsto (fun n ↦ μ {ω | 1 ≤ edist (f n ω) (g ω)}) l (𝓝 0) := h 1 (by simp) (by simp)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1 (fun _ ↦ zero_le) ?_
    intro n
    simp only [hε_top]
    gcongr
    simp
  · exact h ε hε hε_top

/-- `TendstoInMeasure` expressed with an extended norm instead of a distance. -/
/-
**MeasureTheory.tendstoInMeasure_iff_enorm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：tendstoInMeasure_iff_enorm [SeminormedAddCommGroup E] {l : Filter ι} {f : 
ι -> α -> E} {g : α -> E} : TendstoInMeasure μ f l g ↔ forall ε, 0 < ε -> ε != ∞
 -> Tendsto (fun i => μ { x | ε <= ‖f i x - g x‖ₑ }) l (𝓝 0)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `MeasureTheory.tendstoInMeasure_of_ne_top`：tendstoInMeasure_of_ne_top [ED
ist E] {f : ι -> α -> E} {l : Filter ι} {g : α -> E} (h : forall ε, 0 < ε -> ε !
= ∞ -> Tendsto (fun i => μ { x…

--- 原说明 ---
`TendstoInMeasure` expressed with an extended norm instead of a distance.
-/
theorem tendstoInMeasure_iff_enorm [SeminormedAddCommGroup E] {l : Filter ι} {f : ι → α → E}
    {g : α → E} :
    TendstoInMeasure μ f l g ↔
      ∀ ε, 0 < ε → ε ≠ ∞ → Tendsto (fun i => μ { x | ε ≤ ‖f i x - g x‖ₑ }) l (𝓝 0) := by
  simp_rw [← edist_eq_enorm_sub]
  exact ⟨fun h ε hε hε_top ↦ h ε hε, tendstoInMeasure_of_ne_top⟩

/-- `TendstoInMeasure` expressed with the real-valued measure of a set defined with
an extended norm.

The `IsFiniteMeasure` hypothesis is necessary, otherwise `μ.real {...}` could be zero because
the measure of the set is infinite. -/
/-
**MeasureTheory.tendstoInMeasure_iff_measureReal_enorm** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory`。
形式化陈述：tendstoInMeasure_iff_measureReal_enorm [SeminormedAddCommGroup E] [IsFinit
eMeasure μ] {l : Filter ι} {f : ι -> α -> E} {g : α -> E} : TendstoInMeasure μ f
 l g ↔ forall ε, 0 < ε -> ε != ∞ -> Tendsto (fun i => μ.real { x | ε <= ‖f i x -
 g x‖ₑ }) l (𝓝 0)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.tendstoInMeasure_iff_enorm`：tendstoInMeasure_iff_enorm [Se
minormedAddCommGroup E] {l : Filter ι} {f : ι -> α -> E} {g : α -> E} : TendstoI
nMeasure μ f l g ↔ forall ε, 0…
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ENNReal.tendsto_toReal_zero_iff`：tendsto_toReal_zero_iff {ι} {fi : Filte
r ι} {f : ι -> Real>=0∞} (hf : forall i, f i != ∞
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
`TendstoInMeasure` expressed with the real-valued measure of a set defined with
an extended norm.

The `IsFiniteMeasure` hypothesis is necessary, otherwise `μ.real {...}` could be
 zero because
the measure of the set is infinite.
-/
theorem tendstoInMeasure_iff_measureReal_enorm [SeminormedAddCommGroup E] [IsFiniteMeasure μ]
    {l : Filter ι} {f : ι → α → E} {g : α → E} :
    TendstoInMeasure μ f l g ↔
      ∀ ε, 0 < ε → ε ≠ ∞ → Tendsto (fun i ↦ μ.real { x | ε ≤ ‖f i x - g x‖ₑ }) l (𝓝 0) := by
  rw [tendstoInMeasure_iff_enorm]
  congr! with ε hε hε_top
  simp_rw [measureReal_def, ENNReal.tendsto_toReal_zero_iff (fun _ ↦ measure_ne_top _ _)]

/-- `TendstoInMeasure` expressed with a distance `dist` instead of an extended distance `edist`. -/
/-
**MeasureTheory.tendstoInMeasure_iff_dist** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：tendstoInMeasure_iff_dist [PseudoMetricSpace E] {f : ι -> α -> E} {l : Fil
ter ι} {g : α -> E} : TendstoInMeasure μ f l g ↔ forall ε, 0 < ε -> Tendsto (fun
 i => μ { x | ε <= dist (f i x) (g x) }) l (𝓝 0)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `edist_dist`：edist_dist (x y : α) : edist x y = ENNReal.ofReal (dist x y)
· 使用定理 `ENNReal.ofReal_le_ofReal_iff`：ofReal_le_ofReal_iff {p q : Real} (h : 0 <
= q) : ENNReal.ofReal p <= ENNReal.ofReal q ↔ p <= q
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.ofReal_pos`：ofReal_pos {p : Real} : 0 < ENNReal.ofReal p ↔ 0 < p
· 使用引理 `MeasureTheory.tendstoInMeasure_of_ne_top`：tendstoInMeasure_of_ne_top [ED
ist E] {f : ι -> α -> E} {l : Filter ι} {g : α -> E} (h : forall ε, 0 < ε -> ε !
= ∞ -> Tendsto (fun i => μ { x…
· 使用定理 `ENNReal.le_ofReal_iff_toReal_le`：le_ofReal_iff_toReal_le {a : Real>=0∞} 
{b : Real} (ha : a != ∞) (hb : 0 <= b) : a <= ENNReal.ofReal b ↔ ENNReal.toReal 
a <= b
· 使用定理 `ENNReal.toReal_pos`：toReal_pos {a : Real>=0∞} (ha₀ : a != 0) (ha_top : a
 != ∞) : 0 < a.toReal
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b

--- 原说明 ---
`TendstoInMeasure` expressed with a distance `dist` instead of an extended dista
nce `edist`.
-/
lemma tendstoInMeasure_iff_dist [PseudoMetricSpace E] {f : ι → α → E} {l : Filter ι} {g : α → E} :
    TendstoInMeasure μ f l g
      ↔ ∀ ε, 0 < ε → Tendsto (fun i => μ { x | ε ≤ dist (f i x) (g x) }) l (𝓝 0) := by
  refine ⟨fun h ε hε ↦ ?_, fun h ↦ ?_⟩
  · convert! h (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε) with i a
    rw [edist_dist, ENNReal.ofReal_le_ofReal_iff (by positivity)]
  · refine tendstoInMeasure_of_ne_top fun ε hε hε_top ↦ ?_
    convert! h ε.toReal (ENNReal.toReal_pos hε.ne' hε_top) with i a
    rw [edist_dist, ENNReal.le_ofReal_iff_toReal_le hε_top (by positivity)]

/-- `TendstoInMeasure` expressed with the real-valued measure of a set defined with a distance.

The `IsFiniteMeasure` hypothesis is necessary, otherwise `μ.real {...}` could be zero because
the measure of the set is infinite. -/
/-
**MeasureTheory.tendstoInMeasure_iff_measureReal_dist** 是 Mathlib 中的一个引理，位于命名空间 
`MeasureTheory`。
形式化陈述：tendstoInMeasure_iff_measureReal_dist [PseudoMetricSpace E] [IsFiniteMeasu
re μ] {f : ι -> α -> E} {l : Filter ι} {g : α -> E} : TendstoInMeasure μ f l g ↔
 forall ε, 0 < ε -> Tendsto (fun i => μ.real { x | ε <= dist (f i x) (g x) }) l 
(𝓝 0)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.tendstoInMeasure_iff_dist`：tendstoInMeasure_iff_dist [Pseu
doMetricSpace E] {f : ι -> α -> E} {l : Filter ι} {g : α -> E} : TendstoInMeasur
e μ f l g ↔ forall ε, 0 < ε -…
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ENNReal.tendsto_toReal_zero_iff`：tendsto_toReal_zero_iff {ι} {fi : Filte
r ι} {f : ι -> Real>=0∞} (hf : forall i, f i != ∞
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
`TendstoInMeasure` expressed with the real-valued measure of a set defined with 
a distance.

The `IsFiniteMeasure` hypothesis is necessary, otherwise `μ.real {...}` could be
 zero because
the measure of the set is infinite.
-/
lemma tendstoInMeasure_iff_measureReal_dist [PseudoMetricSpace E] [IsFiniteMeasure μ]
    {f : ι → α → E} {l : Filter ι} {g : α → E} :
    TendstoInMeasure μ f l g ↔
      ∀ ε, 0 < ε → Tendsto (fun i ↦ μ.real { x | ε ≤ dist (f i x) (g x) }) l (𝓝 0) := by
  rw [tendstoInMeasure_iff_dist]
  congr! with ε hε hε_top
  simp_rw [measureReal_def, ENNReal.tendsto_toReal_zero_iff (fun _ ↦ measure_ne_top _ _)]

/-- `TendstoInMeasure` expressed with a norm instead of a distance. -/
/-
**MeasureTheory.tendstoInMeasure_iff_norm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：tendstoInMeasure_iff_norm [SeminormedAddCommGroup E] {l : Filter ι} {f : ι
 -> α -> E} {g : α -> E} : TendstoInMeasure μ f l g ↔ forall ε, 0 < ε -> Tendsto
 (fun i => μ { x | ε <= ‖f i x - g x‖ }) l (𝓝 0)
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
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dist_eq_norm_sub`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a 
b : E), dist a b = ‖a - b‖
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
`TendstoInMeasure` expressed with a norm instead of a distance.
-/
theorem tendstoInMeasure_iff_norm [SeminormedAddCommGroup E] {l : Filter ι} {f : ι → α → E}
    {g : α → E} :
    TendstoInMeasure μ f l g ↔
      ∀ ε, 0 < ε → Tendsto (fun i => μ { x | ε ≤ ‖f i x - g x‖ }) l (𝓝 0) := by
  simp_rw [tendstoInMeasure_iff_dist, dist_eq_norm_sub]

/-- `TendstoInMeasure` expressed with the real-valued measure of a set defined with a norm.

The `IsFiniteMeasure` hypothesis is necessary, otherwise `μ.real {...}` could be zero because
the measure of the set is infinite. -/
/-
**MeasureTheory.tendstoInMeasure_iff_measureReal_norm** 是 Mathlib 中的一个引理，位于命名空间 
`MeasureTheory`。
形式化陈述：tendstoInMeasure_iff_measureReal_norm [SeminormedAddCommGroup E] [IsFinite
Measure μ] {l : Filter ι} {f : ι -> α -> E} {g : α -> E} : TendstoInMeasure μ f 
l g ↔ forall ε, 0 < ε -> Tendsto (fun i => μ.real { x | ε <= ‖f i x - g x‖ }) l 
(𝓝 0)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.tendstoInMeasure_iff_norm`：tendstoInMeasure_iff_norm [Semi
normedAddCommGroup E] {l : Filter ι} {f : ι -> α -> E} {g : α -> E} : TendstoInM
easure μ f l g ↔ forall ε, 0 …
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ENNReal.tendsto_toReal_zero_iff`：tendsto_toReal_zero_iff {ι} {fi : Filte
r ι} {f : ι -> Real>=0∞} (hf : forall i, f i != ∞
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
`TendstoInMeasure` expressed with the real-valued measure of a set defined with 
a norm.

The `IsFiniteMeasure` hypothesis is necessary, otherwise `μ.real {...}` could be
 zero because
the measure of the set is infinite.
-/
lemma tendstoInMeasure_iff_measureReal_norm [SeminormedAddCommGroup E] [IsFiniteMeasure μ]
    {l : Filter ι} {f : ι → α → E} {g : α → E} :
    TendstoInMeasure μ f l g ↔
      ∀ ε, 0 < ε → Tendsto (fun i ↦ μ.real { x | ε ≤ ‖f i x - g x‖ }) l (𝓝 0) := by
  rw [tendstoInMeasure_iff_norm]
  congr! with ε hε hε_top
  simp_rw [measureReal_def, ENNReal.tendsto_toReal_zero_iff (fun _ ↦ measure_ne_top _ _)]
/-
**MeasureTheory.tendstoInMeasure_iff_tendsto_toNNReal** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory`。
形式化陈述：tendstoInMeasure_iff_tendsto_toNNReal [EDist E] [IsFiniteMeasure μ] {f : ι
 -> α -> E} {l : Filter ι} {g : α -> E} : TendstoInMeasure μ f l g ↔ forall ε, 0
 < ε -> Tendsto (fun i => (μ { x | ε <= edist (f i x) (g x) }).toNNReal) l (𝓝 0)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.tendsto_toNNReal_iff'`：tendsto_toNNReal_iff' {f : α -> Real>=0∞}
 {u : Filter α} {a : Real>=0} (hf : forall x, f x != ∞) : Tendsto (ENNReal.toNNR
eal ∘ f) u (𝓝 a) ↔ …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.tendsto_toNNReal_iff`：tendsto_toNNReal_iff {f : α -> Real>=0∞} {
u : Filter α} (ha : a != ∞) (hf : forall x, f x != ∞) : Tendsto (ENNReal.toNNRea
l ∘ f) u (𝓝 (a.toN…
· 使用定理 `ENNReal.zero_ne_top`：0 ≠ ⊤
-/
theorem tendstoInMeasure_iff_tendsto_toNNReal [EDist E] [IsFiniteMeasure μ]
    {f : ι → α → E} {l : Filter ι} {g : α → E} :
    TendstoInMeasure μ f l g ↔
      ∀ ε, 0 < ε → Tendsto (fun i => (μ { x | ε ≤ edist (f i x) (g x) }).toNNReal) l (𝓝 0) := by
  have hfin ε i : μ { x | ε ≤ edist (f i x) (g x) } ≠ ⊤ :=
    measure_ne_top μ {x | ε ≤ edist (f i x) (g x)}
  refine ⟨fun h ε hε ↦ ?_, fun h ε hε ↦ ?_⟩
  · have hf : (fun i => (μ { x | ε ≤ edist (f i x) (g x) }).toNNReal) =
        ENNReal.toNNReal ∘ (fun i ↦ (μ { x | ε ≤ edist (f i x) (g x) })) := rfl
    rw [hf, ENNReal.tendsto_toNNReal_iff' (hfin ε)]
    exact h ε hε
  · rw [← ENNReal.tendsto_toNNReal_iff ENNReal.zero_ne_top (hfin ε)]
    exact h ε hε

namespace TendstoInMeasure

variable [EDist E] {l : Filter ι} {f f' : ι → α → E} {g g' : α → E}

/-
**MeasureTheory.TendstoInMeasure.mono** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.T
endstoInMeasure`。
形式化陈述：mono {v : Filter ι} (huv : v <= l) (hg : TendstoInMeasure μ f l g) : Tends
toInMeasure μ f v g
参数：huv : v <= l；hg : TendstoInMeasure μ f l g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
-/
lemma mono {v : Filter ι} (huv : v ≤ l) (hg : TendstoInMeasure μ f l g) :
    TendstoInMeasure μ f v g := fun ε hε => (hg ε hε).mono_left huv
/-
**MeasureTheory.TendstoInMeasure.comp** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.T
endstoInMeasure`。
形式化陈述：comp {v : Filter κ} {ns : κ -> ι} (hg : TendstoInMeasure μ f l g) (hns : T
endsto ns v l) : TendstoInMeasure μ (f ∘ ns) v g
参数：hg : TendstoInMeasure μ f l g；hns : Tendsto ns v l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
-/
lemma comp {v : Filter κ} {ns : κ → ι} (hg : TendstoInMeasure μ f l g)
    (hns : Tendsto ns v l) : TendstoInMeasure μ (f ∘ ns) v g := fun ε hε ↦ (hg ε hε).comp hns
/-
**MeasureTheory.TendstoInMeasure.indicator** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.TendstoInMeasure`。
形式化陈述：indicator {F : Type*} [PseudoEMetricSpace F] [Zero F] {f : ι -> α -> F} {g
 : α -> F} (hg : TendstoInMeasure μ f l g) (s : Set α) : TendstoInMeasure μ (fun
 i => s.indicator (f i)) l (s.indicator g)
参数：hg : TendstoInMeasure μ f l g；s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_of_tendsto_of_tendsto_of_le_of_le`：tendsto_of_tendsto_of_tendsto
_of_le_of_le [OrderTopology α] {f g h : β -> α} {b : Filter β} {a : α} (hg : Ten
dsto g b (𝓝 a)) (hh : Tendsto h…
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `PseudoEMetricSpace.edist_self`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x : α), edist x x = 0
-/
theorem indicator {F : Type*} [PseudoEMetricSpace F] [Zero F] {f : ι → α → F} {g : α → F}
    (hg : TendstoInMeasure μ f l g) (s : Set α) :
    TendstoInMeasure μ (fun i => s.indicator (f i)) l (s.indicator g) := by
  refine fun ε hε => tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hg ε hε) ?_ ?_
  · intro; simp
  · refine fun n => measure_mono (fun x hx => ?_)
    by_cases x ∈ s <;> simp_all
/-
**MeasureTheory.TendstoInMeasure.congr'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.TendstoInMeasure`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_2} {E : Type u_4} {m : MeasurableSpace α} {μ 
: MeasureTheory.Measure α} [inst : EDist E]   {l : Filter ι} {f f' : ι → α → E} 
{g g' : α → E},   (∀ᶠ (i : ι) in l, f i =ᵐ[μ] f' i) →     g =ᵐ[μ] g' → MeasureTh
eory.TendstoInMeasure μ f l g → MeasureTheory.TendstoInMeasure μ f' l g'
参数：∀ᶠ (i : ι) in l, f i =ᵐ[μ] f' i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `MeasureTheory.measure_congr`：measure_congr (H : s =ᵐ[μ] t) : μ s = μ t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_iff_iff`：∀ {a b : Prop}, a = b ↔ (a ↔ b)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Filter.tendsto_congr'`：tendsto_congr' {f₁ f₂ : α -> β} {l₁ : Filter α} {
l₂ : Filter β} (hl : f₁ =ᶠ[l₁] f₂) : Tendsto f₁ l₁ l₂ ↔ Tendsto f₂ l₁ l₂
-/
protected theorem congr' (h_left : ∀ᶠ i in l, f i =ᵐ[μ] f' i) (h_right : g =ᵐ[μ] g')
    (h_tendsto : TendstoInMeasure μ f l g) : TendstoInMeasure μ f' l g' := by
  intro ε hε
  suffices
    (fun i ↦ μ { x | ε ≤ edist (f' i x) (g' x) }) =ᶠ[l] fun i ↦ μ { x | ε ≤ edist (f i x) (g x) } by
    rw [tendsto_congr' this]
    exact h_tendsto ε hε
  filter_upwards [h_left] with i h_ae_eq
  refine measure_congr ?_
  filter_upwards [h_ae_eq, h_right] with x hxf hxg
  rw [eq_iff_iff]
  change ε ≤ edist (f' i x) (g' x) ↔ ε ≤ edist (f i x) (g x)
  rw [hxg, hxf]
/-
**MeasureTheory.TendstoInMeasure.congr** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
TendstoInMeasure`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_2} {E : Type u_4} {m : MeasurableSpace α} {μ 
: MeasureTheory.Measure α} [inst : EDist E]   {l : Filter ι} {f f' : ι → α → E} 
{g g' : α → E},   (∀ (i : ι), f i =ᵐ[μ] f' i) →     g =ᵐ[μ] g' → MeasureTheory.T
endstoInMeasure μ f l g → MeasureTheory.TendstoInMeasure μ f' l g'
参数：∀ (i : ι), f i =ᵐ[μ] f' i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.TendstoInMeasure.congr'`：∀ {α : Type u_1} {ι : Type u_2} {
E : Type u_4} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : EDis
t E]   {l : Filter ι} {f f'…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
-/
protected theorem congr (h_left : ∀ i, f i =ᵐ[μ] f' i) (h_right : g =ᵐ[μ] g')
    (h_tendsto : TendstoInMeasure μ f l g) : TendstoInMeasure μ f' l g' :=
  TendstoInMeasure.congr' (Eventually.of_forall h_left) h_right h_tendsto
/-
**MeasureTheory.TendstoInMeasure.congr_left** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.TendstoInMeasure`。
形式化陈述：congr_left (h : forall i, f i =ᵐ[μ] f' i) (h_tendsto : TendstoInMeasure μ 
f l g) : TendstoInMeasure μ f' l g
参数：h : forall i, f i =ᵐ[μ] f' i；h_tendsto : TendstoInMeasure μ f l g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.TendstoInMeasure.congr`：∀ {α : Type u_1} {ι : Type u_2} {E
 : Type u_4} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : EDist
 E]   {l : Filter ι} {f f'…
· 使用定理 `Filter.EventuallyEq.rfl`：∀ {α : Type u} {β : Type v} {l : Filter α} {f :
 α → β}, f =ᶠ[l] f
-/
theorem congr_left (h : ∀ i, f i =ᵐ[μ] f' i) (h_tendsto : TendstoInMeasure μ f l g) :
    TendstoInMeasure μ f' l g :=
  h_tendsto.congr h EventuallyEq.rfl
/-
**MeasureTheory.TendstoInMeasure.congr_right** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.TendstoInMeasure`。
形式化陈述：congr_right (h : g =ᵐ[μ] g') (h_tendsto : TendstoInMeasure μ f l g) : Tend
stoInMeasure μ f l g'
参数：h : g =ᵐ[μ] g'；h_tendsto : TendstoInMeasure μ f l g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.TendstoInMeasure.congr`：∀ {α : Type u_1} {ι : Type u_2} {E
 : Type u_4} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : EDist
 E]   {l : Filter ι} {f f'…
· 使用定理 `Filter.EventuallyEq.rfl`：∀ {α : Type u} {β : Type v} {l : Filter α} {f :
 α → β}, f =ᶠ[l] f
-/
theorem congr_right (h : g =ᵐ[μ] g') (h_tendsto : TendstoInMeasure μ f l g) :
    TendstoInMeasure μ f l g' :=
  h_tendsto.congr (fun _ => EventuallyEq.rfl) h

end TendstoInMeasure

section ExistsSeqTendstoAe

variable [PseudoEMetricSpace E]
variable {f : ℕ → α → E} {g : α → E}

/-
**MeasureTheory.tendstoInMeasure_of_tendsto_ae_of_measurable_edist** 是 Mathlib 中
的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：tendstoInMeasure_of_tendsto_ae_of_measurable_edist [IsFiniteMeasure μ] (hf
 : forall n, Measurable (fun a => edist (f n a) (g a))) (hfg : forallᵐ x ∂μ, Ten
dsto (fun n => f n x) atTop (𝓝 (g x))) : TendstoInMeasure μ f atTop g
参数：hf : forall n, Measurable (fun a => edist (f n a) (g a))；hfg : forallᵐ x ∂μ, 
Tendsto (fun n => f n x) atTop (𝓝 (g x))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.tendsto_atTop_zero`：∀ {β : Type u_2} [Nonempty β] [inst : Semila
tticeSup β] {f : β → ENNReal},   Filter.Tendsto f Filter.atTop (nhds 0) ↔ ∀ ε > 
0, ∃ N, ∀ n ≥ N,…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `MeasureTheory.tendstoUniformlyOn_of_ae_tendsto_of_measurable_edist'`：ten
dstoUniformlyOn_of_ae_tendsto_of_measurable_edist' [IsFiniteMeasure μ] (hf : for
all n, Measurable (fun a => edist (f n a) (g a))) (hfg : …
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.coe_pos`：∀ {r : NNReal}, 0 < ↑r ↔ 0 < r
· 使用定理 `ENNReal.coe_pos`：∀ {r : NNReal}, 0 < ↑r ↔ 0 < r
· 使用定理 `gt_iff_lt`：∀ {α : Type u_1} [inst : LT α] {x y : α}, x > y ↔ y < x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `EMetric.tendstoUniformlyOn_iff`：tendstoUniformlyOn_iff {ι : Type*} {F : 
ι -> β -> α} {f : β -> α} {p : Filter ι} {s : Set β} : TendstoUniformlyOn F f p 
s ↔ forall ε > 0, fo…
· 使用定理 `Set.compl_subset_compl`：compl_subset_compl : sᶜ subseteq tᶜ ↔ t subseteq
 s
· 使用定理 `Set.mem_compl_iff`：mem_compl_iff (s : Set α) (x : α) : x in sᶜ ↔ x ∉ s
· 使用定理 `Set.notMem_ofPred_iff`：notMem_ofPred_iff {a : α} {p : α -> Prop} : a ∉ {
 x | p x } ↔ ¬p a
· 使用定理 `PseudoEMetricSpace.edist_comm`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x y : α), edist x y = edist y x
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
（共 31 条，此处仅展示前 30 条）
-/
theorem tendstoInMeasure_of_tendsto_ae_of_measurable_edist [IsFiniteMeasure μ]
    (hf : ∀ n, Measurable (fun a ↦ edist (f n a) (g a)))
    (hfg : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) : TendstoInMeasure μ f atTop g := by
  refine fun ε hε => ENNReal.tendsto_atTop_zero.mpr fun δ hδ => ?_
  by_cases hδi : δ = ∞
  · simp only [hδi, imp_true_iff, le_top, exists_const]
  lift δ to ℝ≥0 using hδi
  rw [gt_iff_lt, ENNReal.coe_pos, ← NNReal.coe_pos] at hδ
  obtain ⟨t, _, ht, hunif⟩ :=
    tendstoUniformlyOn_of_ae_tendsto_of_measurable_edist' hf hfg hδ
  rw [ENNReal.ofReal_coe_nnreal] at ht
  rw [EMetric.tendstoUniformlyOn_iff] at hunif
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hunif ε hε)
  refine ⟨N, fun n hn => ?_⟩
  suffices { x : α | ε ≤ edist (f n x) (g x) } ⊆ t from (measure_mono this).trans ht
  rw [← Set.compl_subset_compl]
  intro x hx
  rw [Set.mem_compl_iff, Set.notMem_ofPred_iff, edist_comm, not_le]
  exact hN n hn x hx

/-- Convergence a.e. implies convergence in measure in a finite measure space. -/
/-
**MeasureTheory.tendstoInMeasure_of_tendsto_ae** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：tendstoInMeasure_of_tendsto_ae [IsFiniteMeasure μ] (hf : forall n, AEStron
glyMeasurable (f n) μ) (hfg : forallᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g
 x))) : TendstoInMeasure μ f atTop g
参数：hf : forall n, AEStronglyMeasurable (f n) μ；hfg : forallᵐ x ∂μ, Tendsto (fun 
n => f n x) atTop (𝓝 (g x))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `aestronglyMeasurable_of_tendsto_ae`：∀ {α : Type u_1} {β : Type u_2} [ins
t : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}  
 {ι : Type u_5} [Topolog…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
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
· 使用定理 `MeasureTheory.TendstoInMeasure.congr`：∀ {α : Type u_1} {ι : Type u_2} {E
 : Type u_4} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : EDist
 E]   {l : Filter ι} {f f'…
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.AEStronglyMeasurable.ae_eq_mk`：ae_eq_mk (hf : AEStronglyMe
asurable[m] f μ) : f =ᵐ[μ] hf.mk f
· 使用定理 `MeasureTheory.tendstoInMeasure_of_tendsto_ae_of_measurable_edist`：tendst
oInMeasure_of_tendsto_ae_of_measurable_edist [IsFiniteMeasure μ] (hf : forall n,
 Measurable (fun a => edist (f n a) (g a))) (hfg : for…
· 使用定理 `MeasureTheory.StronglyMeasurable.measurable`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [Topologi
calSpace.PseudoMetrizableSpace β]…
· 使用定理 `TopologicalSpace.MetrizableSpace.toPseudoMetrizableSpace`：∀ {X : Type u_
5} {t : TopologicalSpace X} [self : TopologicalSpace.MetrizableSpace X],   Topol
ogicalSpace.PseudoMetrizableSpace X
· 使用定理 `ENNReal.instMetrizableSpace`：TopologicalSpace.MetrizableSpace ENNReal
· 使用定理 `MeasureTheory.StronglyMeasurable.edist`：∀ {α : Type u_1} {x : Measurable
Space α} {β : Type u_5} [inst : PseudoEMetricSpace β] {f g : α → β},   MeasureTh
eory.StronglyMeasurable f → …
· 使用引理 `MeasureTheory.AEStronglyMeasurable.stronglyMeasurable_mk`：stronglyMeasur
able_mk (hf : AEStronglyMeasurable[m] f μ) : StronglyMeasurable[m] (hf.mk f)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.ae_all_iff`：ae_all_iff {ι : Sort*} [Countable ι] {p : α ->
 ι -> Prop} : (forallᵐ a ∂μ, forall i, p a i) ↔ forall i, forallᵐ a ∂μ, p a i
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g

--- 原说明 ---
Convergence a.e. implies convergence in measure in a finite measure space.
-/
theorem tendstoInMeasure_of_tendsto_ae [IsFiniteMeasure μ] (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (hfg : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) : TendstoInMeasure μ f atTop g := by
  have hg : AEStronglyMeasurable g μ := aestronglyMeasurable_of_tendsto_ae _ hf hfg
  refine TendstoInMeasure.congr (fun i => (hf i).ae_eq_mk.symm) hg.ae_eq_mk.symm ?_
  refine tendstoInMeasure_of_tendsto_ae_of_measurable_edist
    (fun n ↦ ((hf n).stronglyMeasurable_mk.edist hg.stronglyMeasurable_mk).measurable) ?_
  have hf_eq_ae : ∀ᵐ x ∂μ, ∀ n, (hf n).mk (f n) x = f n x :=
    ae_all_iff.mpr fun n => (hf n).ae_eq_mk.symm
  filter_upwards [hf_eq_ae, hg.ae_eq_mk, hfg] with x hxf hxg hxfg
  rw [← hxg, funext fun n => hxf n]
  exact hxfg

namespace ExistsSeqTendstoAe

/-
**MeasureTheory.ExistsSeqTendstoAe.exists_nat_measure_lt_two_inv** 是 Mathlib 中的一
个定理，位于命名空间 `MeasureTheory.ExistsSeqTendstoAe`。
形式化陈述：exists_nat_measure_lt_two_inv (hfg : TendstoInMeasure μ f atTop g) (n : Na
t) : exists N, forall m >= N, μ { x | (2 : Real>=0∞)⁻¹ ^ n <= edist (f m x) (g x
) } <= (2⁻¹ : Real>=0∞) ^ n
参数：hfg : TendstoInMeasure μ f atTop g；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.tendsto_atTop_zero`：∀ {β : Type u_2} [Nonempty β] [inst : Semila
tticeSup β] {f : β → ENNReal},   Filter.Tendsto f Filter.atTop (nhds 0) ↔ ∀ ε > 
0, ∃ N, ∀ n ≥ N,…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `ENNReal.pow_pos`：∀ {a : ENNReal}, 0 < a → ∀ (n : ℕ), 0 < a ^ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `ENNReal.instNoZeroDivisors`：NoZeroDivisors ENNReal
-/
theorem exists_nat_measure_lt_two_inv (hfg : TendstoInMeasure μ f atTop g) (n : ℕ) :
    ∃ N, ∀ m ≥ N, μ { x | (2 : ℝ≥0∞)⁻¹ ^ n ≤ edist (f m x) (g x) } ≤ (2⁻¹ : ℝ≥0∞) ^ n := by
  specialize hfg ((2⁻¹ : ℝ≥0∞) ^ n) (ENNReal.pow_pos (by simp) _)
  rw [ENNReal.tendsto_atTop_zero] at hfg
  exact hfg ((2 : ℝ≥0∞)⁻¹ ^ n) (pos_iff_ne_zero.mpr <| pow_ne_zero _ <| by simp)

/-- Given a sequence of functions `f` which converges in measure to `g`,
`seqTendstoAeSeqAux` is a sequence such that
`∀ m ≥ seqTendstoAeSeqAux n, μ {x | 2⁻¹ ^ n ≤ dist (f m x) (g x)} ≤ 2⁻¹ ^ n`. -/
/-
**MeasureTheory.ExistsSeqTendstoAe.seqTendstoAeSeqAux** 是 Mathlib 中的一个定义，位于命名空间 
`MeasureTheory.ExistsSeqTendstoAe`。
形式化陈述：seqTendstoAeSeqAux (hfg : TendstoInMeasure μ f atTop g) (n : Nat)
参数：hfg : TendstoInMeasure μ f atTop g；n : Nat。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.ExistsSeqTendstoAe.exists_nat_measure_lt_two_inv`：exists_n
at_measure_lt_two_inv (hfg : TendstoInMeasure μ f atTop g) (n : Nat) : exists N,
 forall m >= N, μ { x | (2 : Real>=0∞)⁻¹ ^ n <= edis…

--- 原说明 ---
Given a sequence of functions `f` which converges in measure to `g`,
`seqTendstoAeSeqAux` is a sequence such that
`∀ m ≥ seqTendstoAeSeqAux n, μ {x | 2⁻¹ ^ n ≤ dist (f m x) (g x)} ≤ 2⁻¹ ^ n`.
-/
noncomputable def seqTendstoAeSeqAux (hfg : TendstoInMeasure μ f atTop g) (n : ℕ) :=
  Classical.choose (exists_nat_measure_lt_two_inv hfg n)

/-- Transformation of `seqTendstoAeSeqAux` to makes sure it is strictly monotone. -/
/-
**MeasureTheory.ExistsSeqTendstoAe.seqTendstoAeSeq** 是 Mathlib 中的一个定义，位于命名空间 `Me
asureTheory.ExistsSeqTendstoAe`。
形式化陈述：{α : Type u_1} →   {E : Type u_4} →     {m : MeasurableSpace α} →       {μ
 : MeasureTheory.Measure α} →         [inst : PseudoEMetricSpace E] →           
{f : ℕ → α → E} → {g : α → E} → MeasureTheory.TendstoInMeasure μ f Filter.atTop 
g → ℕ → ℕ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transformation of `seqTendstoAeSeqAux` to makes sure it is strictly monotone.
-/
noncomputable def seqTendstoAeSeq (hfg : TendstoInMeasure μ f atTop g) : ℕ → ℕ
  | 0 => seqTendstoAeSeqAux hfg 0
  | n + 1 => max (seqTendstoAeSeqAux hfg (n + 1)) (seqTendstoAeSeq hfg n + 1)
/-
**MeasureTheory.ExistsSeqTendstoAe.seqTendstoAeSeq_succ** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory.ExistsSeqTendstoAe`。
形式化陈述：seqTendstoAeSeq_succ (hfg : TendstoInMeasure μ f atTop g) {n : Nat} : seqT
endstoAeSeq hfg (n + 1) = max (seqTendstoAeSeqAux hfg (n + 1)) (seqTendstoAeSeq 
hfg n + 1)
参数：hfg : TendstoInMeasure μ f atTop g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ExistsSeqTendstoAe.seqTendstoAeSeq.eq_2`：∀ {α : Type u_1} 
{E : Type u_4} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Pse
udoEMetricSpace E]   {f : ℕ → α → E} {g : α…
-/
theorem seqTendstoAeSeq_succ (hfg : TendstoInMeasure μ f atTop g) {n : ℕ} :
    seqTendstoAeSeq hfg (n + 1) =
      max (seqTendstoAeSeqAux hfg (n + 1)) (seqTendstoAeSeq hfg n + 1) := by
  rw [seqTendstoAeSeq]
/-
**MeasureTheory.ExistsSeqTendstoAe.seqTendstoAeSeq_spec** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory.ExistsSeqTendstoAe`。
形式化陈述：seqTendstoAeSeq_spec (hfg : TendstoInMeasure μ f atTop g) (n k : Nat) (hn 
: seqTendstoAeSeq hfg n <= k) : μ { x | (2 : Real>=0∞)⁻¹ ^ n <= edist (f k x) (g
 x) } <= (2 : Real>=0∞)⁻¹ ^ n
参数：hfg : TendstoInMeasure μ f atTop g；n k : Nat；hn : seqTendstoAeSeq hfg n <= k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `MeasureTheory.ExistsSeqTendstoAe.exists_nat_measure_lt_two_inv`：exists_n
at_measure_lt_two_inv (hfg : TendstoInMeasure μ f atTop g) (n : Nat) : exists N,
 forall m >= N, μ { x | (2 : Real>=0∞)⁻¹ ^ n <= edis…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
-/
theorem seqTendstoAeSeq_spec (hfg : TendstoInMeasure μ f atTop g) (n k : ℕ)
    (hn : seqTendstoAeSeq hfg n ≤ k) :
    μ { x | (2 : ℝ≥0∞)⁻¹ ^ n ≤ edist (f k x) (g x) } ≤ (2 : ℝ≥0∞)⁻¹ ^ n := by
  cases n
  · exact Classical.choose_spec (exists_nat_measure_lt_two_inv hfg 0) k hn
  · exact Classical.choose_spec
      (exists_nat_measure_lt_two_inv hfg _) _ (le_trans (le_max_left _ _) hn)
/-
**MeasureTheory.ExistsSeqTendstoAe.seqTendstoAeSeq_strictMono** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory.ExistsSeqTendstoAe`。
形式化陈述：seqTendstoAeSeq_strictMono (hfg : TendstoInMeasure μ f atTop g) : StrictMo
no (seqTendstoAeSeq hfg)
参数：hfg : TendstoInMeasure μ f atTop g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `strictMono_nat_of_lt_succ`：strictMono_nat_of_lt_succ {f : Nat -> α} (hf 
: forall n, f n < f (n + 1)) : StrictMono f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ExistsSeqTendstoAe.seqTendstoAeSeq_succ`：seqTendstoAeSeq_s
ucc (hfg : TendstoInMeasure μ f atTop g) {n : Nat} : seqTendstoAeSeq hfg (n + 1)
 = max (seqTendstoAeSeqAux hfg (n + 1)) (se…
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用引理 `lt_add_one`：lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLE
OneClass α] [NeZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
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
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
-/
theorem seqTendstoAeSeq_strictMono (hfg : TendstoInMeasure μ f atTop g) :
    StrictMono (seqTendstoAeSeq hfg) := by
  refine strictMono_nat_of_lt_succ fun n => ?_
  rw [seqTendstoAeSeq_succ]
  exact lt_of_lt_of_le (lt_add_one <| seqTendstoAeSeq hfg n) (le_max_right _ _)

end ExistsSeqTendstoAe

/-- If `f` is a sequence of functions which converges in measure to `g`, then there exists a
subsequence of `f` which converges a.e. to `g`. -/
/-
**MeasureTheory.TendstoInMeasure.exists_seq_tendsto_ae** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.TendstoInMeasure`。
形式化陈述：∀ {α : Type u_1} {E : Type u_4} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : PseudoEMetricSpace E]   {f : ℕ → α → E} {g : α → E},   Measu
reTheory.TendstoInMeasure μ f Filter.atTop g →     ∃ ns, StrictMono ns ∧ ∀ᵐ (x :
 α) ∂μ, Filter.Tendsto (fun i => f (ns i) x) Filter.atTop (nhds (g x))
参数：x : α；fun i => f (ns i) x；nhds (g x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ENNReal.exists_inv_two_pow_lt`：exists_inv_two_pow_lt (ha : a != 0) : exi
sts n : Nat, 2⁻¹ ^ n < a
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `lt_of_eq_of_lt`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a = b → b < 
c → a < c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `ENNReal.mul_inv_cancel`：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a * a⁻¹ = 1
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instNontrivial`：Nontrivial ENNReal
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ExistsSeqTendstoAe.seqTendstoAeSeq_spec`：seqTendstoAeSeq_s
pec (hfg : TendstoInMeasure μ f atTop g) (n k : Nat) (hn : seqTendstoAeSeq hfg n
 <= k) : μ { x | (2 : Real>=0∞)⁻¹ ^ n <= ed…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `MeasureTheory.measure_limsup_atTop_eq_zero`：measure_limsup_atTop_eq_zero
 {s : Nat -> Set α} (hs : ∑' i, μ (s i) != ∞) : μ (limsup s atTop) = 0
· 使用定理 `ne_top_of_le_ne_top`：ne_top_of_le_ne_top (hb : b != ⊤) (hab : a <= b) : 
a != ⊤
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.tsum_geometric`：ENNReal.tsum_geometric (r : Real>=0∞) : ∑' n : N
at, r ^ n = (1 - r)⁻¹
· 使用定理 `ENNReal.one_sub_inv_two`：one_sub_inv_two : (1 : Real>=0∞) - 2⁻¹ = 2⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用引理 `ENNReal.ofNat_ne_top`：ofNat_ne_top {n : Nat} [Nat.AtLeastTwo n] : ofNat(
n) != ∞
（共 71 条，此处仅展示前 30 条）

--- 原说明 ---
If `f` is a sequence of functions which converges in measure to `g`, then there 
exists a
subsequence of `f` which converges a.e. to `g`.
-/
theorem TendstoInMeasure.exists_seq_tendsto_ae (hfg : TendstoInMeasure μ f atTop g) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ x ∂μ, Tendsto (fun i => f (ns i) x) atTop (𝓝 (g x)) := by
  /- Since `f` tends to `g` in measure, it has a subsequence `k ↦ f (ns k)` such that
    `μ {|f (ns k) - g| ≥ 2⁻ᵏ} ≤ 2⁻ᵏ` for all `k`. Defining
    `s := ⋂ k, ⋃ i ≥ k, {|f (ns k) - g| ≥ 2⁻ᵏ}`, we see that `μ s = 0` by the
    first Borel-Cantelli lemma.

    On the other hand, as `s` is precisely the set for which `f (ns k)`
    doesn't converge to `g`, `f (ns k)` converges almost everywhere to `g` as required. -/
  have h_lt_ε_real (ε : ℝ≥0∞) (hε : 0 < ε) : ∃ k : ℕ, 2 * (2 : ℝ≥0∞)⁻¹ ^ k < ε := by
    obtain ⟨k, h_k⟩ : ∃ k : ℕ, (2 : ℝ≥0∞)⁻¹ ^ k < ε := ENNReal.exists_inv_two_pow_lt hε.ne'
    refine ⟨k + 1, lt_of_eq_of_lt ?_ h_k⟩
    rw [pow_succ', ← mul_assoc, ENNReal.mul_inv_cancel, one_mul]
    · positivity
    · simp
  set ns := ExistsSeqTendstoAe.seqTendstoAeSeq hfg
  use ns
  let S := fun k => { x | (2 : ℝ≥0∞)⁻¹ ^ k ≤ edist (f (ns k) x) (g x) }
  have hμS_le : ∀ k, μ (S k) ≤ (2 : ℝ≥0∞)⁻¹ ^ k :=
    fun k => ExistsSeqTendstoAe.seqTendstoAeSeq_spec hfg k (ns k) le_rfl
  set s := Filter.atTop.limsup S with hs
  have hμs : μ s = 0 := by
    refine measure_limsup_atTop_eq_zero (ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hμS_le))
    simpa only [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv] using ENNReal.ofNat_ne_top
  have h_tendsto : ∀ x ∈ sᶜ, Tendsto (fun i => f (ns i) x) atTop (𝓝 (g x)) := by
    refine fun x hx => EMetric.tendsto_atTop.mpr fun ε hε => ?_
    rw [hs, limsup_eq_iInf_iSup_of_nat] at hx
    simp only [S, Set.iSup_eq_iUnion, Set.iInf_eq_iInter, Set.compl_iInter, Set.compl_iUnion,
      Set.mem_iUnion, Set.mem_iInter, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hx
    obtain ⟨N, hNx⟩ := hx
    obtain ⟨k, hk_lt_ε⟩ := h_lt_ε_real ε hε
    refine ⟨max N (k - 1), fun n hn_ge => lt_of_le_of_lt ?_ hk_lt_ε⟩
    specialize hNx n ((le_max_left _ _).trans hn_ge)
    have h_inv_n_le_k : (2 : ℝ≥0∞)⁻¹ ^ n ≤ 2 * (2 : ℝ≥0∞)⁻¹ ^ k := by
      nth_rw 2 [← pow_one (2 : ℝ≥0∞)]
      rw [mul_comm, ← ENNReal.inv_pow, ← ENNReal.inv_pow, ENNReal.inv_le_iff_le_mul, ← mul_assoc,
        mul_comm (_ ^ n), mul_assoc, ← ENNReal.inv_le_iff_le_mul, inv_inv, ← pow_add]
      · gcongr
        · simp
        · omega
      all_goals simp
    exact le_trans hNx.le h_inv_n_le_k
  rw [ae_iff]
  refine ⟨ExistsSeqTendstoAe.seqTendstoAeSeq_strictMono hfg, measure_mono_null (fun x => ?_) hμs⟩
  rw [Set.mem_ofPred_eq, ← @Classical.not_not (x ∈ s), not_imp_not]
  exact h_tendsto x
/-
**MeasureTheory.TendstoInMeasure.exists_seq_tendstoInMeasure_atTop** 是 Mathlib 中
的一个定理，位于命名空间 `MeasureTheory.TendstoInMeasure`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_2} {E : Type u_4} {m : MeasurableSpace α} {μ 
: MeasureTheory.Measure α}   [inst : PseudoEMetricSpace E] {u : Filter ι} [u.NeB
ot] [u.IsCountablyGenerated] {f : ι → α → E} {g : α → E},   MeasureTheory.Tendst
oInMeasure μ f u g →     ∃ ns, Filter.Tendsto ns Filter.atTop u ∧ MeasureTheory.
TendstoInMeasure μ (fun n => f (ns n)) Filter.atTop g
参数：fun n => f (ns n)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.exists_seq_tendsto`：exists_seq_tendsto (f : Filter α) [IsCountabl
yGenerated f] [NeBot f] : exists x : Nat -> α, Tendsto x atTop f
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
-/
theorem TendstoInMeasure.exists_seq_tendstoInMeasure_atTop {u : Filter ι} [NeBot u]
    [IsCountablyGenerated u] {f : ι → α → E} {g : α → E} (hfg : TendstoInMeasure μ f u g) :
    ∃ ns : ℕ → ι, Tendsto ns atTop u ∧ TendstoInMeasure μ (fun n => f (ns n)) atTop g := by
  obtain ⟨ns, h_tendsto_ns⟩ : ∃ ns : ℕ → ι, Tendsto ns atTop u := exists_seq_tendsto u
  exact ⟨ns, h_tendsto_ns, fun ε hε => (hfg ε hε).comp h_tendsto_ns⟩
/-
**MeasureTheory.TendstoInMeasure.exists_seq_tendsto_ae'** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory.TendstoInMeasure`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_2} {E : Type u_4} {m : MeasurableSpace α} {μ 
: MeasureTheory.Measure α}   [inst : PseudoEMetricSpace E] {u : Filter ι} [u.NeB
ot] [u.IsCountablyGenerated] {f : ι → α → E} {g : α → E},   MeasureTheory.Tendst
oInMeasure μ f u g →     ∃ ns,       Filter.Tendsto ns Filter.atTop u ∧ ∀ᵐ (x : 
α) ∂μ, Filter.Tendsto (fun i => f (ns i) x) Filter.atTop (nhds (g x))
参数：x : α；fun i => f (ns i) x；nhds (g x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.TendstoInMeasure.exists_seq_tendstoInMeasure_atTop`：∀ {α :
 Type u_1} {ι : Type u_2} {E : Type u_4} {m : MeasurableSpace α} {μ : MeasureThe
ory.Measure α}   [inst : PseudoEMetricSpace E] {u : Fi…
· 使用定理 `MeasureTheory.TendstoInMeasure.exists_seq_tendsto_ae`：∀ {α : Type u_1} {
E : Type u_4} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Pseu
doEMetricSpace E]   {f : ℕ → α → E} {g : α…
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `StrictMono.tendsto_atTop`：∀ {φ : ℕ → ℕ}, StrictMono φ → Filter.Tendsto φ
 Filter.atTop Filter.atTop
-/
theorem TendstoInMeasure.exists_seq_tendsto_ae' {u : Filter ι} [NeBot u] [IsCountablyGenerated u]
    {f : ι → α → E} {g : α → E} (hfg : TendstoInMeasure μ f u g) :
    ∃ ns : ℕ → ι, Tendsto ns atTop u ∧ ∀ᵐ x ∂μ, Tendsto (fun i => f (ns i) x) atTop (𝓝 (g x)) := by
  obtain ⟨ms, hms1, hms2⟩ := hfg.exists_seq_tendstoInMeasure_atTop
  obtain ⟨ns, hns1, hns2⟩ := hms2.exists_seq_tendsto_ae
  exact ⟨ms ∘ ns, hms1.comp hns1.tendsto_atTop, hns2⟩

/-- `TendstoInMeasure` is equivalent to every subsequence having another subsequence
which converges almost surely. -/
/-
**MeasureTheory.exists_seq_tendstoInMeasure_atTop_iff** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory`。
形式化陈述：exists_seq_tendstoInMeasure_atTop_iff [IsFiniteMeasure μ] {f : Nat -> α ->
 E} (hf : forall (n : Nat), AEStronglyMeasurable (f n) μ) {g : α -> E} : Tendsto
InMeasure μ f atTop g ↔ forall ns : Nat -> Nat, StrictMono ns -> exists ns' : Na
t -> Nat, StrictMono ns' ∧ forallᵐ (ω : α) ∂μ, Tendsto (fun i => f (ns (ns' i)) 
ω) atTop (𝓝 (g ω))
参数：hf : forall (n : Nat), AEStronglyMeasurable (f n) μ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.TendstoInMeasure.exists_seq_tendsto_ae`：∀ {α : Type u_1} {
E : Type u_4} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Pseu
doEMetricSpace E]   {f : ℕ → α → E} {g : α…
· 使用引理 `MeasureTheory.TendstoInMeasure.comp`：comp {v : Filter κ} {ns : κ -> ι} (
hg : TendstoInMeasure μ f l g) (hns : Tendsto ns v l) : TendstoInMeasure μ (f ∘ 
ns) v g
· 使用定理 `StrictMono.tendsto_atTop`：∀ {φ : ℕ → ℕ}, StrictMono φ → Filter.Tendsto φ
 Filter.atTop Filter.atTop
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.tendstoInMeasure_iff_tendsto_toNNReal`：tendstoInMeasure_if
f_tendsto_toNNReal [EDist E] [IsFiniteMeasure μ] {f : ι -> α -> E} {l : Filter ι
} {g : α -> E} : TendstoInMeasure μ f l g…
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.not_tendsto_iff_exists_frequently_notMem`：not_tendsto_iff_exists_
frequently_notMem {f : α -> β} {l₁ : Filter α} {l₂ : Filter β} : ¬Tendsto f l₁ l
₂ ↔ exists s in l₂, existsᶠ x in l₁, …
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `NNReal.nhds_zero_basis`：nhds_zero_basis : (𝓝 (0 : Real>=0)).HasBasis (fu
n a : Real>=0 => 0 < a) fun a => Iio a
· 使用定理 `Filter.extraction_of_frequently_atTop`：extraction_of_frequently_atTop {P
 : Nat -> Prop} (h : existsᶠ n in atTop, P n) : exists φ : Nat -> Nat, StrictMon
o φ ∧ forall n, P (φ n)
· 使用定理 `Set.notMem_Iio`：∀ {α : Type u_1} [inst : LinearOrder α] {a c : α}, c ∉ S
et.Iio a ↔ a ≤ c
· 使用定理 `Set.notMem_subset`：notMem_subset (h : s subseteq t) : a ∉ t -> a ∉ s
· 使用定理 `MeasureTheory.tendstoInMeasure_of_tendsto_ae`：tendstoInMeasure_of_tendst
o_ae [IsFiniteMeasure μ] (hf : forall n, AEStronglyMeasurable (f n) μ) (hfg : fo
rallᵐ x ∂μ, Tendsto (fun n => f n …
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `ge_of_tendsto'`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace α] 
[inst_1 : Preorder α] [ClosedIciTopology α] {f : β → α}   {a b : α} {x : Filter 
β} […
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `NNReal.instOrderTopology`：OrderTopology NNReal
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α

--- 原说明 ---
`TendstoInMeasure` is equivalent to every subsequence having another subsequence
which converges almost surely.
-/
theorem exists_seq_tendstoInMeasure_atTop_iff [IsFiniteMeasure μ]
    {f : ℕ → α → E} (hf : ∀ (n : ℕ), AEStronglyMeasurable (f n) μ) {g : α → E} :
    TendstoInMeasure μ f atTop g ↔
      ∀ ns : ℕ → ℕ, StrictMono ns → ∃ ns' : ℕ → ℕ, StrictMono ns' ∧
        ∀ᵐ (ω : α) ∂μ, Tendsto (fun i ↦ f (ns (ns' i)) ω) atTop (𝓝 (g ω)) := by
  refine ⟨fun hfg _ hns ↦ (hfg.comp hns.tendsto_atTop).exists_seq_tendsto_ae, fun h1 ↦ ?_⟩
  rw [tendstoInMeasure_iff_tendsto_toNNReal]
  by_contra! ⟨ε, hε, h2⟩
  obtain ⟨δ, ns, hδ, hns, h3⟩ : ∃ (δ : ℝ≥0) (ns : ℕ → ℕ), 0 < δ ∧ StrictMono ns ∧
      ∀ n, δ ≤ (μ {x | ε ≤ edist (f (ns n) x) (g x)}).toNNReal := by
    obtain ⟨s, hs, h4⟩ := not_tendsto_iff_exists_frequently_notMem.1 h2
    obtain ⟨δ, hδ, h5⟩ := NNReal.nhds_zero_basis.mem_iff.1 hs
    obtain ⟨ns, hns, h6⟩ := extraction_of_frequently_atTop h4
    exact ⟨δ, ns, hδ, hns, fun n ↦ Set.notMem_Iio.1 (Set.notMem_subset h5 (h6 n))⟩
  obtain ⟨ns', _, h6⟩ := h1 ns hns
  have h7 := tendstoInMeasure_iff_tendsto_toNNReal.mp <|
    tendstoInMeasure_of_tendsto_ae (fun n ↦ hf _) h6
  exact lt_irrefl _ (lt_of_le_of_lt (ge_of_tendsto' (h7 ε hε) (fun n ↦ h3 _)) hδ)

end ExistsSeqTendstoAe

/-- If the `eLpNorm` of a collection of `AEStronglyMeasurable` functions that converges in measure
is bounded by some constant `C`, then the `eLpNorm` of its limit is also bounded by `C`. -/
/-
**MeasureTheory.eLpNorm_le_of_tendstoInMeasure** 是 Mathlib 中的一个引理，位于命名空间 `Measur
eTheory`。
形式化陈述：eLpNorm_le_of_tendstoInMeasure {ι : Type*} [SeminormedAddGroup E] {u : Fil
ter ι} [NeBot u] [IsCountablyGenerated u] {f : ι -> α -> E} {g : α -> E} {C : Re
al>=0∞} {p : Real>=0∞} (bound : forallᶠ i in u, eLpNorm (f i) p μ <= C) (h_tends
to : TendstoInMeasure μ f u g) (hf : forall i, AEStronglyMeasurable (f i) μ) : e
LpNorm g p μ <= C
参数：bound : forallᶠ i in u, eLpNorm (f i) p μ <= C；h_tendsto : TendstoInMeasure μ
 f u g；hf : forall i, AEStronglyMeasurable (f i) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.TendstoInMeasure.exists_seq_tendsto_ae'`：∀ {α : Type u_1} 
{ι : Type u_2} {E : Type u_4} {m : MeasurableSpace α} {μ : MeasureTheory.Measure
 α}   [inst : PseudoEMetricSpace E] {u : Fi…
· 使用定理 `MeasureTheory.Lp.eLpNorm_le_of_ae_tendsto`：eLpNorm_le_of_ae_tendsto {ι :
 Type*} {u : Filter ι} [NeBot u] [IsCountablyGenerated u] {f : ι -> α -> E} {g :
 α -> E} {C : Real>=0∞} (bound …
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
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
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
If the `eLpNorm` of a collection of `AEStronglyMeasurable` functions that conver
ges in measure
is bounded by some constant `C`, then the `eLpNorm` of its limit is also bounded
 by `C`.
-/
lemma eLpNorm_le_of_tendstoInMeasure {ι : Type*} [SeminormedAddGroup E]
    {u : Filter ι} [NeBot u] [IsCountablyGenerated u] {f : ι → α → E} {g : α → E} {C : ℝ≥0∞}
    {p : ℝ≥0∞} (bound : ∀ᶠ i in u, eLpNorm (f i) p μ ≤ C) (h_tendsto : TendstoInMeasure μ f u g)
    (hf : ∀ i, AEStronglyMeasurable (f i) μ) : eLpNorm g p μ ≤ C := by
  obtain ⟨l, hl⟩ := h_tendsto.exists_seq_tendsto_ae'
  exact Lp.eLpNorm_le_of_ae_tendsto (hl.1.eventually bound) (fun n => hf (l n)) hl.2

section TendstoInMeasureUnique

/-- The limit in measure is ae unique. -/
/-
**MeasureTheory.tendstoInMeasure_ae_unique** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：tendstoInMeasure_ae_unique [EMetricSpace E] {g h : α -> E} {f : ι -> α -> 
E} {u : Filter ι} [NeBot u] [IsCountablyGenerated u] (hg : TendstoInMeasure μ f 
u g) (hh : TendstoInMeasure μ f u h) : g =ᵐ[μ] h
参数：hg : TendstoInMeasure μ f u g；hh : TendstoInMeasure μ f u h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.TendstoInMeasure.exists_seq_tendsto_ae'`：∀ {α : Type u_1} 
{ι : Type u_2} {E : Type u_4} {m : MeasurableSpace α} {μ : MeasureTheory.Measure
 α}   [inst : PseudoEMetricSpace E] {u : Fi…
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
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
· 使用引理 `MeasureTheory.TendstoInMeasure.comp`：comp {v : Filter κ} {ns : κ -> ι} (
hg : TendstoInMeasure μ f l g) (hns : Tendsto ns v l) : TendstoInMeasure μ (f ∘ 
ns) v g
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `tendsto_nhds_unique`：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : F
ilter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) :
 a = b
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …

--- 原说明 ---
The limit in measure is ae unique.
-/
theorem tendstoInMeasure_ae_unique [EMetricSpace E] {g h : α → E} {f : ι → α → E} {u : Filter ι}
    [NeBot u] [IsCountablyGenerated u] (hg : TendstoInMeasure μ f u g)
    (hh : TendstoInMeasure μ f u h) : g =ᵐ[μ] h := by
  obtain ⟨ns, h1, h1'⟩ := hg.exists_seq_tendsto_ae'
  obtain ⟨ns', h2, h2'⟩ := (hh.comp h1).exists_seq_tendsto_ae'
  filter_upwards [h1', h2'] with ω hg1 hh1
  exact tendsto_nhds_unique (hg1.comp h2) hh1

end TendstoInMeasureUnique

section AEMeasurableOf

variable [PseudoEMetricSpace E]

/-
**MeasureTheory.TendstoInMeasure.aestronglyMeasurable** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.TendstoInMeasure`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_2} {E : Type u_4} {m : MeasurableSpace α} {μ 
: MeasureTheory.Measure α}   [inst : PseudoEMetricSpace E] {u : Filter ι} [u.NeB
ot] [u.IsCountablyGenerated] {f : ι → α → E} {g : α → E},   (∀ (n : ι), MeasureT
heory.AEStronglyMeasurable (f n) μ) →     MeasureTheory.TendstoInMeasure μ f u g
 → MeasureTheory.AEStronglyMeasurable g μ
参数：∀ (n : ι), MeasureTheory.AEStronglyMeasurable (f n) μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.TendstoInMeasure.exists_seq_tendsto_ae'`：∀ {α : Type u_1} 
{ι : Type u_2} {E : Type u_4} {m : MeasurableSpace α} {μ : MeasureTheory.Measure
 α}   [inst : PseudoEMetricSpace E] {u : Fi…
· 使用定理 `aestronglyMeasurable_of_tendsto_ae`：∀ {α : Type u_1} {β : Type u_2} [ins
t : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}  
 {ι : Type u_5} [Topolog…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
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
-/
theorem TendstoInMeasure.aestronglyMeasurable {u : Filter ι} [NeBot u] [IsCountablyGenerated u]
    {f : ι → α → E} {g : α → E} (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (h_tendsto : TendstoInMeasure μ f u g) : AEStronglyMeasurable g μ := by
  obtain ⟨ns, -, hns⟩ := h_tendsto.exists_seq_tendsto_ae'
  exact aestronglyMeasurable_of_tendsto_ae atTop (fun n => hf (ns n)) hns

variable [MeasurableSpace E] [BorelSpace E]
/-
**MeasureTheory.TendstoInMeasure.aemeasurable** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.TendstoInMeasure`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_2} {E : Type u_4} {m : MeasurableSpace α} {μ 
: MeasureTheory.Measure α}   [inst : PseudoEMetricSpace E] [inst_1 : MeasurableS
pace E] [BorelSpace E] {u : Filter ι} [u.NeBot]   [u.IsCountablyGenerated] {f : 
ι → α → E} {g : α → E},   (∀ (n : ι), AEMeasurable (f n) μ) → MeasureTheory.Tend
stoInMeasure μ f u g → AEMeasurable g μ
参数：∀ (n : ι), AEMeasurable (f n) μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.TendstoInMeasure.exists_seq_tendsto_ae'`：∀ {α : Type u_1} 
{ι : Type u_2} {E : Type u_4} {m : MeasurableSpace α} {μ : MeasureTheory.Measure
 α}   [inst : PseudoEMetricSpace E] {u : Fi…
· 使用定理 `aemeasurable_of_tendsto_metrizable_ae`：aemeasurable_of_tendsto_metrizabl
e_ae {ι} {μ : Measure α} {f : ι -> α -> β} {g : α -> β} (u : Filter ι) [hu : NeB
ot u] [IsCountablyGenerated…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
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
-/
theorem TendstoInMeasure.aemeasurable {u : Filter ι} [NeBot u] [IsCountablyGenerated u]
    {f : ι → α → E} {g : α → E} (hf : ∀ n, AEMeasurable (f n) μ)
    (h_tendsto : TendstoInMeasure μ f u g) : AEMeasurable g μ := by
  obtain ⟨ns, -, hns⟩ := h_tendsto.exists_seq_tendsto_ae'
  exact aemeasurable_of_tendsto_metrizable_ae atTop (fun n => hf (ns n)) hns

end AEMeasurableOf

section TendstoInMeasureOf

variable {p : ℝ≥0∞}
variable {f : ι → α → E} {g : α → E}

/-- This lemma is superseded by `MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm` where we
allow `p = ∞` and only require `AEStronglyMeasurable`. -/
/-
**MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm_of_stronglyMeasurable** 是 Ma
thlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：tendstoInMeasure_of_tendsto_eLpNorm_of_stronglyMeasurable [SeminormedAddCo
mmGroup E] (hp_ne_zero : p != 0) (hp_ne_top : p != ∞) (hf : forall n, StronglyMe
asurable (f n)) (hg : StronglyMeasurable g) {l : Filter ι} (hfg : Tendsto (fun n
 => eLpNorm (f n - g) p μ) l (𝓝 0)) : TendstoInMeasure μ f l g
参数：hp_ne_zero : p != 0；hp_ne_top : p != ∞；hf : forall n, StronglyMeasurable (f n
)；hg : StronglyMeasurable g；hfg : Tendsto (fun n => eLpNorm (f n - g) p μ) l (𝓝 
0)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.tendstoInMeasure_of_ne_top`：tendstoInMeasure_of_ne_top [ED
ist E] {f : ι -> α -> E} {l : Filter ι} {g : α -> E} (h : forall ε, 0 < ε -> ε !
= ∞ -> Tendsto (fun i => μ { x…
· 使用定理 `ENNReal.Tendsto.const_mul`：∀ {α : Type u_1} {f : Filter α} {m : α → ENNR
eal} {a b : ENNReal},   Filter.Tendsto m f (nhds b) → b ≠ 0 ∨ a ≠ ⊤ → Filter.Ten
dsto (fun b => …
· 使用定理 `Filter.Tendsto.ennrpow_const`：Filter.Tendsto.ennrpow_const {α : Type*} {
f : Filter α} {m : α -> Real>=0∞} {a : Real>=0∞} (r : Real) (hm : Tendsto m f (𝓝
 a)) : Tendsto (fu…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `ENNReal.tendsto_nhds_zero`：∀ {α : Type u_1} {f : Filter α} {u : α → ENNR
eal}, Filter.Tendsto u f (nhds 0) ↔ ∀ ε > 0, ∀ᶠ (x : α) in f, u x ≤ ε
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `ENNReal.zero_rpow_of_pos`：zero_rpow_of_pos {y : Real} (h : 0 < y) : (0 :
 Real>=0∞) ^ y = 0
· 使用定理 `ENNReal.toReal_pos`：toReal_pos {a : Real>=0∞} (ha₀ : a != 0) (ha_top : a
 != ∞) : 0 < a.toReal
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.inv_mul_le_iff`：∀ {x y z : ENNReal}, x ≠ 0 → x ≠ ⊤ → (x⁻¹ * y ≤ 
z ↔ y ≤ x * z)
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `edist_eq_enorm_sub`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (
a b : E), edist a b = ‖a - b‖ₑ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.mul_meas_ge_le_pow_eLpNorm'`：mul_meas_ge_le_pow_eLpNorm' (
hp_ne_zero : p != 0) (hp_ne_top : p != ∞) {f : α -> ε'} (hf : AEStronglyMeasurab
le f μ) (ε : Real>=0∞) : ε ^ p.…
· 使用定理 `MeasureTheory.StronglyMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} 
{β : Type u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : Measu
reTheory.Measure α}   {f : α → β}, MeasureT…
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
This lemma is superseded by `MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm` 
where we
allow `p = ∞` and only require `AEStronglyMeasurable`.
-/
theorem tendstoInMeasure_of_tendsto_eLpNorm_of_stronglyMeasurable [SeminormedAddCommGroup E]
    (hp_ne_zero : p ≠ 0)
    (hp_ne_top : p ≠ ∞) (hf : ∀ n, StronglyMeasurable (f n)) (hg : StronglyMeasurable g)
    {l : Filter ι} (hfg : Tendsto (fun n => eLpNorm (f n - g) p μ) l (𝓝 0)) :
    TendstoInMeasure μ f l g := by
  refine tendstoInMeasure_of_ne_top fun ε hε hε_top ↦ ?_
  replace hfg := ENNReal.Tendsto.const_mul (a := 1 / ε ^ p.toReal)
    (Tendsto.ennrpow_const p.toReal hfg) (Or.inr <| by simp [hε.ne'])
  simp only [mul_zero,
    ENNReal.zero_rpow_of_pos (ENNReal.toReal_pos hp_ne_zero hp_ne_top)] at hfg
  rw [ENNReal.tendsto_nhds_zero] at hfg ⊢
  intro δ hδ
  refine (hfg δ hδ).mono fun n hn => ?_
  refine le_trans ?_ hn
  rw [one_div, ← ENNReal.inv_mul_le_iff, inv_inv]
  · convert!
      mul_meas_ge_le_pow_eLpNorm' μ hp_ne_zero hp_ne_top ((hf n).sub hg).aestronglyMeasurable ε
      using 6
    simp [edist_eq_enorm_sub]
  · simp [hε_top]
  · simp [hε.ne']

/-- This lemma is superseded by `MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm` where we
allow `p = ∞`. -/
/-
**MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm_of_ne_top** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory`。
形式化陈述：tendstoInMeasure_of_tendsto_eLpNorm_of_ne_top [SeminormedAddCommGroup E] (
hp_ne_zero : p != 0) (hp_ne_top : p != ∞) (hf : forall n, AEStronglyMeasurable (
f n) μ) (hg : AEStronglyMeasurable g μ) {l : Filter ι} (hfg : Tendsto (fun n => 
eLpNorm (f n - g) p μ) l (𝓝 0)) : TendstoInMeasure μ f l g
参数：hp_ne_zero : p != 0；hp_ne_top : p != ∞；hf : forall n, AEStronglyMeasurable (f
 n) μ；hg : AEStronglyMeasurable g μ；hfg : Tendsto (fun n => eLpNorm (f n - g) p 
μ) l (𝓝 0)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.TendstoInMeasure.congr`：∀ {α : Type u_1} {ι : Type u_2} {E
 : Type u_4} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : EDist
 E]   {l : Filter ι} {f f'…
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.AEStronglyMeasurable.ae_eq_mk`：ae_eq_mk (hf : AEStronglyMe
asurable[m] f μ) : f =ᵐ[μ] hf.mk f
· 使用定理 `MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm_of_stronglyMeasurable`
：tendstoInMeasure_of_tendsto_eLpNorm_of_stronglyMeasurable [SeminormedAddCommGro
up E] (hp_ne_zero : p != 0) (hp_ne_top : p != ∞) (hf : forall…
· 使用引理 `MeasureTheory.AEStronglyMeasurable.stronglyMeasurable_mk`：stronglyMeasur
able_mk (hf : AEStronglyMeasurable[m] f μ) : StronglyMeasurable[m] (hf.mk f)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.eLpNorm_congr_ae`：eLpNorm_congr_ae {f g : α -> ε} (hfg : f
 =ᵐ[μ] g) : eLpNorm f p μ = eLpNorm g p μ
· 使用定理 `Filter.EventuallyEq.sub`：∀ {α : Type u} {β : Type v} [inst : Sub β] {f f
' g g' : α → β} {l : Filter α},   f =ᶠ[l] g → f' =ᶠ[l] g' → f - f' =ᶠ[l] g - g'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
This lemma is superseded by `MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm` 
where we
allow `p = ∞`.
-/
theorem tendstoInMeasure_of_tendsto_eLpNorm_of_ne_top [SeminormedAddCommGroup E]
    (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hg : AEStronglyMeasurable g μ) {l : Filter ι}
    (hfg : Tendsto (fun n => eLpNorm (f n - g) p μ) l (𝓝 0)) : TendstoInMeasure μ f l g := by
  refine TendstoInMeasure.congr (fun i => (hf i).ae_eq_mk.symm) hg.ae_eq_mk.symm ?_
  refine tendstoInMeasure_of_tendsto_eLpNorm_of_stronglyMeasurable
    hp_ne_zero hp_ne_top (fun i => (hf i).stronglyMeasurable_mk) hg.stronglyMeasurable_mk ?_
  have : (fun n => eLpNorm ((hf n).mk (f n) - hg.mk g) p μ) = fun n => eLpNorm (f n - g) p μ := by
    ext1 n; refine eLpNorm_congr_ae (EventuallyEq.sub (hf n).ae_eq_mk.symm hg.ae_eq_mk.symm)
  rw [this]
  exact hfg

/-- See also `MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm` which work for general
Lp-convergence for all `p ≠ 0`. -/
/-
**MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm_top** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory`。
形式化陈述：tendstoInMeasure_of_tendsto_eLpNorm_top {E} [SeminormedAddCommGroup E] {f 
: ι -> α -> E} {g : α -> E} {l : Filter ι} (hfg : Tendsto (fun n => eLpNorm (f n
 - g) ∞ μ) l (𝓝 0)) : TendstoInMeasure μ f l g
参数：hfg : Tendsto (fun n => eLpNorm (f n - g) ∞ μ) l (𝓝 0)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.tendstoInMeasure_of_ne_top`：tendstoInMeasure_of_ne_top [ED
ist E] {f : ι -> α -> E} {l : Filter ι} {g : α -> E} (h : forall ε, 0 < ε -> ε !
= ∞ -> Tendsto (fun i => μ { x…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.tendsto_nhds_zero`：∀ {α : Type u_1} {f : Filter α} {u : α → ENNR
eal}, Filter.Tendsto u f (nhds 0) ↔ ∀ ε > 0, ∀ᶠ (x : α) in f, u x ≤ ε
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.eLpNorm_exponent_top`：eLpNorm_exponent_top {f : α -> ε} : 
eLpNorm f ∞ μ = eLpNormEssSup f μ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.div_pos_iff`：∀ {a b : ENNReal}, 0 < a / b ↔ a ≠ 0 ∧ b ≠ ⊤
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `ENNReal.ofNat_ne_top`：ofNat_ne_top {n : Nat} [Nat.AtLeastTwo n] : ofNat(
n) != ∞
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `ENNReal.half_lt_self`：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a / 2 < a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `edist_eq_enorm_sub`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (
a b : E), edist a b = ‖a - b‖ₑ
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `ae_lt_of_essSup_lt`：ae_lt_of_essSup_lt (hx : essSup f μ < x) (hf : IsBou
ndedUnder (· <= ·) (ae μ) f
· 使用定理 `Filter.isBounded_le_of_top`：isBounded_le_of_top [LE α] [OrderTop α] {f :
 Filter α} : f.IsBounded (· <= ·)
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b

--- 原说明 ---
See also `MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm` which work for gene
ral
Lp-convergence for all `p ≠ 0`.
-/
theorem tendstoInMeasure_of_tendsto_eLpNorm_top {E} [SeminormedAddCommGroup E] {f : ι → α → E}
    {g : α → E} {l : Filter ι} (hfg : Tendsto (fun n => eLpNorm (f n - g) ∞ μ) l (𝓝 0)) :
    TendstoInMeasure μ f l g := by
  refine tendstoInMeasure_of_ne_top fun δ hδ hδ_top ↦ ?_
  simp only [eLpNorm_exponent_top, eLpNormEssSup] at hfg
  rw [ENNReal.tendsto_nhds_zero] at hfg ⊢
  intro ε hε
  specialize hfg (δ / 2) (ENNReal.div_pos_iff.2 ⟨hδ.ne', ENNReal.ofNat_ne_top⟩)
  refine hfg.mono fun n hn => ?_
  simp only [Pi.sub_apply] at *
  have : essSup (fun x : α => ‖f n x - g x‖ₑ) μ < δ :=
    hn.trans_lt (ENNReal.half_lt_self hδ.ne' hδ_top)
  refine ((le_of_eq ?_).trans (ae_lt_of_essSup_lt this).le).trans hε.le
  congr with x
  simp [edist_eq_enorm_sub]

/-- Convergence in Lp implies convergence in measure. -/
/-
**MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory`。
形式化陈述：tendstoInMeasure_of_tendsto_eLpNorm [NormedAddCommGroup E] {l : Filter ι} 
(hp_ne_zero : p != 0) (hf : forall n, AEStronglyMeasurable (f n) μ) (hg : AEStro
nglyMeasurable g μ) (hfg : Tendsto (fun n => eLpNorm (f n - g) p μ) l (𝓝 0)) : T
endstoInMeasure μ f l g
参数：hp_ne_zero : p != 0；hf : forall n, AEStronglyMeasurable (f n) μ；hg : AEStrong
lyMeasurable g μ；hfg : Tendsto (fun n => eLpNorm (f n - g) p μ) l (𝓝 0)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm_top`：tendstoInMeasure_
of_tendsto_eLpNorm_top {E} [SeminormedAddCommGroup E] {f : ι -> α -> E} {g : α -
> E} {l : Filter ι} (hfg : Tendsto (fun n =…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm_of_ne_top`：tendstoInMe
asure_of_tendsto_eLpNorm_of_ne_top [SeminormedAddCommGroup E] (hp_ne_zero : p !=
 0) (hp_ne_top : p != ∞) (hf : forall n, AEStrong…

--- 原说明 ---
Convergence in Lp implies convergence in measure.
-/
theorem tendstoInMeasure_of_tendsto_eLpNorm [NormedAddCommGroup E]
    {l : Filter ι} (hp_ne_zero : p ≠ 0)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hg : AEStronglyMeasurable g μ)
    (hfg : Tendsto (fun n => eLpNorm (f n - g) p μ) l (𝓝 0)) : TendstoInMeasure μ f l g := by
  by_cases hp_ne_top : p = ∞
  · subst hp_ne_top
    exact tendstoInMeasure_of_tendsto_eLpNorm_top hfg
  · exact tendstoInMeasure_of_tendsto_eLpNorm_of_ne_top hp_ne_zero hp_ne_top hf hg hfg

/-- Convergence in Lp implies convergence in measure. -/
/-
**MeasureTheory.tendstoInMeasure_of_tendsto_Lp** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：tendstoInMeasure_of_tendsto_Lp [NormedAddCommGroup E] [hp : Fact (1 <= p)]
 {f : ι -> Lp E p μ} {g : Lp E p μ} {l : Filter ι} (hfg : Tendsto f l (𝓝 g)) : T
endstoInMeasure μ (fun n => f n) l g
参数：1 <= p；hfg : Tendsto f l (𝓝 g)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm`：tendstoInMeasure_of_t
endsto_eLpNorm [NormedAddCommGroup E] {l : Filter ι} (hp_ne_zero : p != 0) (hf :
 forall n, AEStronglyMeasurable (f n) μ…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `Fact.elim`：Fact.elim {p : Prop} (h : Fact p) : p
· 使用定理 `MeasureTheory.Lp.aestronglyMeasurable`：∀ {α : Type u_1} {E : Type u_4} {
m : MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : Nor
medAddCommGroup E] (f : ↥(M…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.Lp.tendsto_Lp_iff_tendsto_eLpNorm'`：tendsto_Lp_iff_tendsto
_eLpNorm' {ι} {fi : Filter ι} [Fact (1 <= p)] (f : ι -> Lp E p μ) (f_lim : Lp E 
p μ) : fi.Tendsto f (𝓝 f_lim) ↔ fi.Ten…

--- 原说明 ---
Convergence in Lp implies convergence in measure.
-/
theorem tendstoInMeasure_of_tendsto_Lp [NormedAddCommGroup E] [hp : Fact (1 ≤ p)]
    {f : ι → Lp E p μ} {g : Lp E p μ}
    {l : Filter ι} (hfg : Tendsto f l (𝓝 g)) : TendstoInMeasure μ (fun n => f n) l g :=
  tendstoInMeasure_of_tendsto_eLpNorm (zero_lt_one.trans_le hp.elim).ne.symm
    (fun _ => Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
    ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp hfg)

end TendstoInMeasureOf

end MeasureTheory

