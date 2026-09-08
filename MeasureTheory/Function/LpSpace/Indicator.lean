/-
Copyright (c) 2020 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Order.Filter.IndicatorFunction

/-!
# Indicator of a set as an element of `Lp`

For a set `s` with `(hs : MeasurableSet s)` and `(hμs : μ s < ∞)`, we build
`indicatorConstLp p hs hμs c`, the element of `Lp` corresponding to `s.indicator (fun _ => c)`.

## Main definitions

* `MeasureTheory.indicatorConstLp`: Indicator of a set as an element of `Lp`.
* `MeasureTheory.Lp.const`: Constant function as an element of `Lp` for a finite measure.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology symmDiff

variable {α E : Type*} {m : MeasurableSpace α} {p : ℝ≥0∞} {μ : Measure α} [NormedAddCommGroup E]

namespace MeasureTheory

/-- The `eLpNorm` of the indicator of a set is uniformly small if the set itself has small measure,
for any `p < ∞`. Given here as an existential `∀ ε > 0, ∃ η > 0, ...` to avoid later
management of `ℝ≥0∞`-arithmetic. -/
/-
**MeasureTheory.exists_eLpNorm_indicator_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：exists_eLpNorm_indicator_le (hp : p != ∞) (c : E) {ε : Real>=0∞} (hε : ε !
= 0) : exists η : Real>=0, 0 < η ∧ forall s : Set α, μ s <= η -> eLpNorm (s.indi
cator fun _ => c) p μ <= ε
参数：hp : p != ∞；c : E；hε : ε != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instZeroLEOneClass`：∀ {α : Type u_2} [inst : Semiring α] [
inst_1 : PartialOrder α] [FloorSemiring α], ZeroLEOneClass α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.eLpNorm_exponent_zero`：eLpNorm_exponent_zero {f : α -> ε} 
: eLpNorm f 0 μ = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `bot_lt_iff_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : Orde
rBot α] {a : α}, ⊥ < a ↔ a ≠ ⊥
· 使用引理 `div_nonneg`：div_nonneg (ha : 0 <= a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `ENNReal.toReal_nonneg`：∀ {a : ENNReal}, 0 ≤ a.toReal
· 使用定理 `ENNReal.toReal_pos`：toReal_pos {a : Real>=0∞} (ha₀ : a != 0) (ha_top : a
 != ∞) : 0 < a.toReal
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `ENNReal.tendsto_coe`：tendsto_coe {f : Filter α} {m : α -> Real>=0} {a : 
Real>=0} : Tendsto (fun a => (m a : Real>=0∞)) f (𝓝 ↑a) ↔ Tendsto m f (𝓝 a)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `NNReal.zero_rpow`：zero_rpow {x : Real} (h : x != 0) : (0 : Real>=0) ^ x 
= 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
（共 59 条，此处仅展示前 30 条）

--- 原说明 ---
The `eLpNorm` of the indicator of a set is uniformly small if the set itself has
 small measure,
for any `p < ∞`. Given here as an existential `∀ ε > 0, ∃ η > 0, ...` to avoid l
ater
management of `ℝ≥0∞`-arithmetic.
-/
theorem exists_eLpNorm_indicator_le (hp : p ≠ ∞) (c : E) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ η : ℝ≥0, 0 < η ∧ ∀ s : Set α, μ s ≤ η → eLpNorm (s.indicator fun _ => c) p μ ≤ ε := by
  rcases eq_or_ne p 0 with (rfl | h'p)
  · exact ⟨1, zero_lt_one, fun s _ => by simp⟩
  have hp₀ : 0 < p := bot_lt_iff_ne_bot.2 h'p
  have hp₀' : 0 ≤ 1 / p.toReal := div_nonneg zero_le_one ENNReal.toReal_nonneg
  have hp₀'' : 0 < p.toReal := ENNReal.toReal_pos hp₀.ne' hp
  obtain ⟨η, hη_pos, hη_le⟩ : ∃ η : ℝ≥0, 0 < η ∧ ‖c‖ₑ * (η : ℝ≥0∞) ^ (1 / p.toReal) ≤ ε := by
    have :
      Filter.Tendsto (fun x : ℝ≥0 => ((‖c‖₊ * x ^ (1 / p.toReal) : ℝ≥0) : ℝ≥0∞)) (𝓝 0)
        (𝓝 (0 : ℝ≥0)) := by
      rw [ENNReal.tendsto_coe]
      convert! (NNReal.continuousAt_rpow_const (Or.inr hp₀')).tendsto.const_mul _
      simp [hp₀''.ne']
    have hε' : 0 < ε := hε.bot_lt
    obtain ⟨δ, hδ, hδε'⟩ := NNReal.nhds_zero_basis.eventually_iff.mp (this.eventually_le_const hε')
    obtain ⟨η, hη, hηδ⟩ := exists_between hδ
    refine ⟨η, hη, ?_⟩
    simpa only [← ENNReal.coe_rpow_of_nonneg _ hp₀', enorm, ← ENNReal.coe_mul] using hδε' hηδ
  refine ⟨η, hη_pos, fun s hs => ?_⟩
  grw [eLpNorm_indicator_const_le, ← hη_le, hs]

section Topology
variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  {μ : Measure X} [IsFiniteMeasureOnCompacts μ]

/-- A bounded measurable function with compact support is in L^p. -/
/-
**MeasureTheory._root_.HasCompactSupport.memLp_of_bound** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A bounded measurable function with compact support is in L^p.
-/
theorem _root_.HasCompactSupport.memLp_of_bound {f : X → E} (hf : HasCompactSupport f)
    (h2f : AEStronglyMeasurable f μ) (C : ℝ) (hfC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) : MemLp f p μ := by
  have := memLp_top_of_bound h2f C hfC
  exact this.mono_exponent_of_measure_support_ne_top
    (fun x ↦ image_eq_zero_of_notMem_tsupport) (hf.measure_lt_top.ne) le_top

/-- A bounded measurable function with compact support is in L^p.
This is the `ENNReal`-valued version of `HasCompactSupport.memLp_of_bound`. -/
/-
**MeasureTheory._root_.HasCompactSupport.memLp_of_enorm_bound** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A bounded measurable function with compact support is in L^p.
This is the `ENNReal`-valued version of `HasCompactSupport.memLp_of_bound`.
-/
theorem _root_.HasCompactSupport.memLp_of_enorm_bound {f : X → E} (hf : HasCompactSupport f)
    (h2f : AEStronglyMeasurable f μ) {C : ℝ≥0∞} (hfC : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ C) (hC : C ≠ ⊤) :
      MemLp f p μ := by
  have : MemLp f ∞ μ :=
    ⟨h2f, eLpNormEssSup_le_of_ae_enorm_bound hfC |>.trans_lt hC.lt_top⟩
  exact this.mono_exponent_of_measure_support_ne_top
    (fun x ↦ image_eq_zero_of_notMem_tsupport) hf.measure_ne_top le_top

/-- A continuous function with compact support is in L^p. -/
/-
**MeasureTheory._root_.Continuous.memLp_of_hasCompactSupport** 是 Mathlib 中的一个定理，
位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A continuous function with compact support is in L^p.
-/
theorem _root_.Continuous.memLp_of_hasCompactSupport [OpensMeasurableSpace X]
    {f : X → E} (hf : Continuous f) (h'f : HasCompactSupport f) : MemLp f p μ := by
  have := hf.memLp_top_of_hasCompactSupport h'f μ
  exact this.mono_exponent_of_measure_support_ne_top
    (fun x ↦ image_eq_zero_of_notMem_tsupport) (h'f.measure_lt_top.ne) le_top

end Topology

section IndicatorConstLp

open Set Function

variable {s : Set α} {hs : MeasurableSet s} {hμs : μ s ≠ ∞} {c : E}

/-- Indicator of a set as an element of `Lp`. -/
/-
**MeasureTheory.indicatorConstLp** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：indicatorConstLp (p : Real>=0∞) (hs : MeasurableSet s) (hμs : μ s != ∞) (c
 : E) : Lp E p μ
参数：p : Real>=0∞；hs : MeasurableSet s；hμs : μ s != ∞；c : E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Indicator of a set as an element of `Lp`.
-/
def indicatorConstLp (p : ℝ≥0∞) (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : E) : Lp E p μ :=
  MemLp.toLp (s.indicator fun _ => c) (memLp_indicator_const p hs c (Or.inr hμs))

/-- A version of `Set.indicator_add` for `MeasureTheory.indicatorConstLp` -/
/-
**MeasureTheory.indicatorConstLp_add** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：indicatorConstLp_add {c' : E} : indicatorConstLp p hs hμs c + indicatorCon
stLp p hs hμs c' = indicatorConstLp p hs hμs (c + c')
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.MemLp.add`：∀ {α : Type u_1} {ε : Type u_3} {m : Measurable
Space α} [inst : TopologicalSpace ε] [inst_1 : ESeminormedAddMonoid ε]   {p : EN
NReal} {μ : M…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `Set.indicator_add`：∀ {α : Type u_1} {M : Type u_4} [inst : AddZeroClass 
M] (s : Set α) (f g : α → M),   (s.indicator fun a => f a + g a) = fun a => s.in
dicator…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.MemLp.toLp.congr_simp`：∀ {α : Type u_1} {E : Type u_4} {m 
: MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : Norme
dAddCommGroup E] (f f_1 :…

--- 原说明 ---
A version of `Set.indicator_add` for `MeasureTheory.indicatorConstLp`
-/
theorem indicatorConstLp_add {c' : E} :
    indicatorConstLp p hs hμs c + indicatorConstLp p hs hμs c' =
    indicatorConstLp p hs hμs (c + c') := by
  simp_rw [indicatorConstLp, ← MemLp.toLp_add, indicator_add]
  rfl

/-- A version of `Set.indicator_sub` for `MeasureTheory.indicatorConstLp` -/
/-
**MeasureTheory.indicatorConstLp_sub** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：indicatorConstLp_sub {c' : E} : indicatorConstLp p hs hμs c - indicatorCon
stLp p hs hμs c' = indicatorConstLp p hs hμs (c - c')
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.MemLp.sub`：∀ {α : Type u_1} {E : Type u_2} {m : Measurable
Space α} [inst : NormedAddCommGroup E] {p : ENNReal}   {μ : MeasureTheory.Measur
e α} {f g : α…
· 使用定理 `Set.indicator_sub`：∀ {α : Type u_1} {G : Type u_6} [inst : AddGroup G] (
s : Set α) (f g : α → G),   (s.indicator fun a => f a - g a) = fun a => s.indica
tor f a…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.MemLp.toLp.congr_simp`：∀ {α : Type u_1} {E : Type u_4} {m 
: MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : Norme
dAddCommGroup E] (f f_1 :…

--- 原说明 ---
A version of `Set.indicator_sub` for `MeasureTheory.indicatorConstLp`
-/
theorem indicatorConstLp_sub {c' : E} :
    indicatorConstLp p hs hμs c - indicatorConstLp p hs hμs c' =
    indicatorConstLp p hs hμs (c - c') := by
  simp_rw [indicatorConstLp, ← MemLp.toLp_sub, indicator_sub]
  rfl
/-
**MeasureTheory.indicatorConstLp_coeFn** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：indicatorConstLp_coeFn : ⇑(indicatorConstLp p hs hμs c) =ᵐ[μ] s.indicator 
fun _ => c
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MemLp.coeFn_toLp`：coeFn_toLp {f : α -> E} (hf : MemLp f p 
μ) : hf.toLp f =ᵐ[μ] f
· 使用引理 `MeasureTheory.memLp_indicator_const`：memLp_indicator_const (p : Real>=0∞
) (hs : MeasurableSet s) (c : E) (hμsc : c = 0 ∨ μ s != ∞) : MemLp (s.indicator 
fun _ => c) p μ
-/
theorem indicatorConstLp_coeFn : ⇑(indicatorConstLp p hs hμs c) =ᵐ[μ] s.indicator fun _ => c :=
  MemLp.coeFn_toLp (memLp_indicator_const p hs c (Or.inr hμs))
/-
**MeasureTheory.indicatorConstLp_coeFn_mem** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：indicatorConstLp_coeFn_mem : forallᵐ x : α ∂μ, x in s -> indicatorConstLp 
p hs hμs c x = c
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.indicatorConstLp_coeFn`：indicatorConstLp_coeFn : ⇑(indicat
orConstLp p hs hμs c) =ᵐ[μ] s.indicator fun _ => c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
-/
theorem indicatorConstLp_coeFn_mem : ∀ᵐ x : α ∂μ, x ∈ s → indicatorConstLp p hs hμs c x = c :=
  indicatorConstLp_coeFn.mono fun _x hx hxs => hx.trans (Set.indicator_of_mem hxs _)
/-
**MeasureTheory.indicatorConstLp_coeFn_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory`。
形式化陈述：indicatorConstLp_coeFn_notMem : forallᵐ x : α ∂μ, x ∉ s -> indicatorConstL
p p hs hμs c x = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.indicatorConstLp_coeFn`：indicatorConstLp_coeFn : ⇑(indicat
orConstLp p hs hμs c) =ᵐ[μ] s.indicator fun _ => c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
-/
theorem indicatorConstLp_coeFn_notMem : ∀ᵐ x : α ∂μ, x ∉ s → indicatorConstLp p hs hμs c x = 0 :=
  indicatorConstLp_coeFn.mono fun _x hx hxs => hx.trans (Set.indicator_of_notMem hxs _)
/-
**MeasureTheory.norm_indicatorConstLp** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：norm_indicatorConstLp (hp_ne_zero : p != 0) (hp_ne_top : p != ∞) : ‖indica
torConstLp p hs hμs c‖ = ‖c‖ * μ.real s ^ (1 / p.toReal)
参数：hp_ne_zero : p != 0；hp_ne_top : p != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Lp.norm_def`：norm_def (f : Lp E p μ) : ‖f‖ = ENNReal.toRea
l (eLpNorm f p μ)
· 使用定理 `MeasureTheory.eLpNorm_congr_ae`：eLpNorm_congr_ae {f g : α -> ε} (hfg : f
 =ᵐ[μ] g) : eLpNorm f p μ = eLpNorm g p μ
· 使用定理 `MeasureTheory.indicatorConstLp_coeFn`：indicatorConstLp_coeFn : ⇑(indicat
orConstLp p hs hμs c) =ᵐ[μ] s.indicator fun _ => c
· 使用引理 `MeasureTheory.eLpNorm_indicator_const`：eLpNorm_indicator_const (hs : Mea
surableSet s) (hp : p != 0) (hp_top : p != ∞) : eLpNorm (s.indicator fun _ => c)
 p μ = ‖c‖ₑ * μ s ^ (1 / p.…
· 使用定理 `ENNReal.toReal_mul`：toReal_mul : (a * b).toReal = a.toReal * b.toReal
· 使用定理 `MeasureTheory.measureReal_def`：measureReal_def {α : Type*} {m : Measurab
leSpace α} (μ : Measure α) (s : Set α) : μ.real s = (μ s).toReal
· 使用定理 `ENNReal.toReal_rpow`：toReal_rpow (x : Real>=0∞) (z : Real) : x.toReal ^ 
z = (x ^ z).toReal
· 使用定理 `toReal_enorm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (x : E), ‖x
‖ₑ.toReal = ‖x‖
-/
theorem norm_indicatorConstLp (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) :
    ‖indicatorConstLp p hs hμs c‖ = ‖c‖ * μ.real s ^ (1 / p.toReal) := by
  rw [Lp.norm_def, eLpNorm_congr_ae indicatorConstLp_coeFn,
    eLpNorm_indicator_const hs hp_ne_zero hp_ne_top, ENNReal.toReal_mul, measureReal_def,
    ENNReal.toReal_rpow, toReal_enorm]
/-
**MeasureTheory.norm_indicatorConstLp_top** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：norm_indicatorConstLp_top (hμs_ne_zero : μ s != 0) : ‖indicatorConstLp ∞ h
s hμs c‖ = ‖c‖
参数：hμs_ne_zero : μ s != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Lp.norm_def`：norm_def (f : Lp E p μ) : ‖f‖ = ENNReal.toRea
l (eLpNorm f p μ)
· 使用定理 `MeasureTheory.eLpNorm_congr_ae`：eLpNorm_congr_ae {f g : α -> ε} (hfg : f
 =ᵐ[μ] g) : eLpNorm f p μ = eLpNorm g p μ
· 使用定理 `MeasureTheory.indicatorConstLp_coeFn`：indicatorConstLp_coeFn : ⇑(indicat
orConstLp p hs hμs c) =ᵐ[μ] s.indicator fun _ => c
· 使用引理 `MeasureTheory.eLpNorm_indicator_const'`：eLpNorm_indicator_const' (hs : M
easurableSet s) (hμs : μ s != 0) (hp : p != 0) : eLpNorm (s.indicator fun _ => c
) p μ = ‖c‖ₑ * μ s ^ (1 / p.…
· 使用定理 `ENNReal.top_ne_zero`：⊤ ≠ 0
· 使用定理 `ENNReal.toReal_top`：⊤.toReal = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `ENNReal.rpow_zero`：rpow_zero {x : Real>=0∞} : x ^ (0 : Real) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `toReal_enorm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (x : E), ‖x
‖ₑ.toReal = ‖x‖
-/
theorem norm_indicatorConstLp_top (hμs_ne_zero : μ s ≠ 0) :
    ‖indicatorConstLp ∞ hs hμs c‖ = ‖c‖ := by
  rw [Lp.norm_def, eLpNorm_congr_ae indicatorConstLp_coeFn,
    eLpNorm_indicator_const' hs hμs_ne_zero ENNReal.top_ne_zero, ENNReal.toReal_top,
    _root_.div_zero, ENNReal.rpow_zero, mul_one, toReal_enorm]
/-
**MeasureTheory.norm_indicatorConstLp'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：norm_indicatorConstLp' (hp_pos : p != 0) (hμs_pos : μ s != 0) : ‖indicator
ConstLp p hs hμs c‖ = ‖c‖ * μ.real s ^ (1 / p.toReal)
参数：hp_pos : p != 0；hμs_pos : μ s != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.toReal_top`：⊤.toReal = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `Real.rpow_zero`：rpow_zero (x : Real) : x ^ (0 : Real) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MeasureTheory.norm_indicatorConstLp_top`：norm_indicatorConstLp_top (hμs_
ne_zero : μ s != 0) : ‖indicatorConstLp ∞ hs hμs c‖ = ‖c‖
· 使用定理 `MeasureTheory.norm_indicatorConstLp`：norm_indicatorConstLp (hp_ne_zero :
 p != 0) (hp_ne_top : p != ∞) : ‖indicatorConstLp p hs hμs c‖ = ‖c‖ * μ.real s ^
 (1 / p.toReal)
-/
theorem norm_indicatorConstLp' (hp_pos : p ≠ 0) (hμs_pos : μ s ≠ 0) :
    ‖indicatorConstLp p hs hμs c‖ = ‖c‖ * μ.real s ^ (1 / p.toReal) := by
  by_cases hp_top : p = ∞
  · rw [hp_top, ENNReal.toReal_top, _root_.div_zero, Real.rpow_zero, mul_one]
    exact norm_indicatorConstLp_top hμs_pos
  · exact norm_indicatorConstLp hp_pos hp_top
/-
**MeasureTheory.norm_indicatorConstLp_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：norm_indicatorConstLp_le : ‖indicatorConstLp p hs hμs c‖ <= ‖c‖ * μ.real s
 ^ (1 / p.toReal)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.indicatorConstLp.eq_1`：∀ {α : Type u_1} {E : Type u_2} {m 
: MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup E]
   {s : Set α} (p : ENNRe…
· 使用引理 `MeasureTheory.Lp.norm_toLp`：norm_toLp (f : α -> E) (hf : MemLp f p μ) : 
‖hf.toLp f‖ = ENNReal.toReal (eLpNorm f p μ)
· 使用定理 `ENNReal.toReal_le_of_le_ofReal`：toReal_le_of_le_ofReal {a : Real>=0∞} {b
 : Real} (hb : 0 <= b) (h : a <= ENNReal.ofReal b) : ENNReal.toReal a <= b
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Real.rpow_nonneg`：rpow_nonneg {x : Real} (hx : 0 <= x) (y : Real) : 0 <=
 x ^ y
· 使用定理 `MeasureTheory.measureReal_nonneg`：∀ {α : Type u_1} {x : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α}, 0 ≤ μ.real s
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用引理 `MeasureTheory.eLpNorm_indicator_const_le`：eLpNorm_indicator_const_le (p 
: Real>=0∞) : eLpNorm (s.indicator fun _ => c) p μ <= ‖c‖ₑ * μ s ^ (1 / p.toReal
)
· 使用定理 `ENNReal.ofReal_mul`：ofReal_mul {p q : Real} (hp : 0 <= p) : ENNReal.ofRe
al (p * q) = ENNReal.ofReal p * ENNReal.ofReal q
· 使用定理 `ofReal_norm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (x : E), ENN
Real.ofReal ‖x‖ = ‖x‖ₑ
· 使用定理 `MeasureTheory.measureReal_def`：measureReal_def {α : Type*} {m : Measurab
leSpace α} (μ : Measure α) (s : Set α) : μ.real s = (μ s).toReal
· 使用定理 `ENNReal.toReal_rpow`：toReal_rpow (x : Real>=0∞) (z : Real) : x.toReal ^ 
z = (x ^ z).toReal
· 使用定理 `ENNReal.ofReal_toReal`：ofReal_toReal {a : Real>=0∞} (h : a != ∞) : ENNRe
al.ofReal a.toReal = a
· 使用定理 `ENNReal.rpow_ne_top_of_nonneg`：rpow_ne_top_of_nonneg {x : Real>=0∞} {y :
 Real} (hy0 : 0 <= y) (h : x != ⊤) : x ^ y != ⊤
· 使用引理 `Mathlib.Meta.Positivity.div_nonneg_of_pos_of_nonneg`：div_nonneg_of_pos_o
f_nonneg [PosMulReflectLT α] (ha : 0 < a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `ENNReal.toReal_nonneg`：∀ {a : ENNReal}, 0 ≤ a.toReal
-/
theorem norm_indicatorConstLp_le :
    ‖indicatorConstLp p hs hμs c‖ ≤ ‖c‖ * μ.real s ^ (1 / p.toReal) := by
  rw [indicatorConstLp, Lp.norm_toLp]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  refine (eLpNorm_indicator_const_le _ _).trans_eq ?_
  rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, measureReal_def,
    ENNReal.toReal_rpow, ENNReal.ofReal_toReal]
  finiteness
/-
**MeasureTheory.nnnorm_indicatorConstLp_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：nnnorm_indicatorConstLp_le : ‖indicatorConstLp p hs hμs c‖₊ <= ‖c‖₊ * (μ s
).toNNReal ^ (1 / p.toReal)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.norm_indicatorConstLp_le`：norm_indicatorConstLp_le : ‖indi
catorConstLp p hs hμs c‖ <= ‖c‖ * μ.real s ^ (1 / p.toReal)
-/
theorem nnnorm_indicatorConstLp_le :
    ‖indicatorConstLp p hs hμs c‖₊ ≤ ‖c‖₊ * (μ s).toNNReal ^ (1 / p.toReal) :=
  norm_indicatorConstLp_le
/-
**MeasureTheory.enorm_indicatorConstLp_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：enorm_indicatorConstLp_le : ‖indicatorConstLp p hs hμs c‖ₑ <= ‖c‖ₑ * μ s ^
 (1 / p.toReal)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Lp.enorm_def`：enorm_def (f : Lp E p μ) : ‖f‖ₑ = eLpNorm f 
p μ
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ENNReal.coe_rpow_of_nonneg`：coe_rpow_of_nonneg (x : Real>=0) {y : Real} 
(h : 0 <= y) : ↑(x ^ y) = (x : Real>=0∞) ^ y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.coe_toNNReal`：∀ {a : ENNReal}, a ≠ ⊤ → ↑a.toNNReal = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.coe_le_coe`：∀ {r q : NNReal}, ↑r ≤ ↑q ↔ r ≤ q
· 使用定理 `MeasureTheory.nnnorm_indicatorConstLp_le`：nnnorm_indicatorConstLp_le : ‖
indicatorConstLp p hs hμs c‖₊ <= ‖c‖₊ * (μ s).toNNReal ^ (1 / p.toReal)
-/
theorem enorm_indicatorConstLp_le :
    ‖indicatorConstLp p hs hμs c‖ₑ ≤ ‖c‖ₑ * μ s ^ (1 / p.toReal) := by
  simpa [ENNReal.coe_rpow_of_nonneg, ENNReal.coe_toNNReal hμs, Lp.enorm_def, ← enorm_eq_nnnorm]
    using ENNReal.coe_le_coe.2 <| nnnorm_indicatorConstLp_le (c := c) (hμs := hμs)
/-
**MeasureTheory.edist_indicatorConstLp_eq_enorm** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
形式化陈述：edist_indicatorConstLp_eq_enorm {t : Set α} {ht : MeasurableSet t} {hμt : 
μ t != ∞} : edist (indicatorConstLp p hs hμs c) (indicatorConstLp p ht hμt c) = 
‖indicatorConstLp (μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasurableSet.symmDiff`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ 
: Set α},   MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (symmDiff s₁ s₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Lp.edist_toLp_toLp`：edist_toLp_toLp (f g : α -> E) (hf : M
emLp f p μ) (hg : MemLp g p μ) : edist (hf.toLp f) (hg.toLp g) = eLpNorm (f - g)
 p μ
· 使用定理 `MeasureTheory.eLpNorm_indicator_sub_indicator`：eLpNorm_indicator_sub_ind
icator (s t : Set α) (f : α -> E) : eLpNorm (s.indicator f - t.indicator f) p μ 
= eLpNorm ((s ∆ t).indicator f) p μ
· 使用引理 `MeasureTheory.Lp.enorm_toLp`：enorm_toLp {f : α -> E} (hf : MemLp f p μ) 
: ‖hf.toLp f‖ₑ = eLpNorm f p μ
-/
theorem edist_indicatorConstLp_eq_enorm {t : Set α} {ht : MeasurableSet t} {hμt : μ t ≠ ∞} :
    edist (indicatorConstLp p hs hμs c) (indicatorConstLp p ht hμt c) =
      ‖indicatorConstLp (μ := μ) p (hs.symmDiff ht) (by finiteness) c‖ₑ := by
  unfold indicatorConstLp
  rw [Lp.edist_toLp_toLp, eLpNorm_indicator_sub_indicator, Lp.enorm_toLp]
/-
**MeasureTheory.dist_indicatorConstLp_eq_norm** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory`。
形式化陈述：dist_indicatorConstLp_eq_norm {t : Set α} {ht : MeasurableSet t} {hμt : μ 
t != ∞} : dist (indicatorConstLp p hs hμs c) (indicatorConstLp p ht hμt c) = ‖in
dicatorConstLp (μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasurableSet.symmDiff`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ 
: Set α},   MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (symmDiff s₁ s₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Lp.dist_edist`：∀ {α : Type u_1} {E : Type u_4} {m : Measur
ableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddComm
Group E] (f g : ↥…
· 使用定理 `MeasureTheory.edist_indicatorConstLp_eq_enorm`：edist_indicatorConstLp_eq
_enorm {t : Set α} {ht : MeasurableSet t} {hμt : μ t != ∞} : edist (indicatorCon
stLp p hs hμs c) (indicatorConstLp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dist_indicatorConstLp_eq_norm {t : Set α} {ht : MeasurableSet t} {hμt : μ t ≠ ∞} :
    dist (indicatorConstLp p hs hμs c) (indicatorConstLp p ht hμt c) =
      ‖indicatorConstLp (μ := μ) p (hs.symmDiff ht) (by finiteness) c‖ := by
  -- Squeezed for performance reasons
  simp only [Lp.dist_edist, edist_indicatorConstLp_eq_enorm, enorm, ENNReal.coe_toReal,
    Lp.coe_nnnorm]

/-- A family of `indicatorConstLp` functions tends to an `indicatorConstLp`,
if the underlying sets tend to the set in the sense of the measure of the symmetric difference. -/
/-
**MeasureTheory.tendsto_indicatorConstLp_set** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：tendsto_indicatorConstLp_set [hp₁ : Fact (1 <= p)] {β : Type*} {l : Filter
 β} {t : β -> Set α} {ht : forall b, MeasurableSet (t b)} {hμt : forall b, μ (t 
b) != ∞} (hp : p != ∞) (h : Tendsto (fun b => μ (t b ∆ s)) l (𝓝 0)) : Tendsto (f
un b => indicatorConstLp p (ht b) (hμt b) c) l (𝓝 (indicatorConstLp p hs hμs c))
参数：1 <= p；t b；t b；hp : p != ∞；h : Tendsto (fun b => μ (t b ∆ s)) l (𝓝 0)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tendsto_iff_dist_tendsto_zero`：tendsto_iff_dist_tendsto_zero {f : β -> α
} {x : Filter β} {a : α} : Tendsto f x (𝓝 a) ↔ Tendsto (fun b => dist (f b) a) x
 (𝓝 0)
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasurableSet.symmDiff`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ 
: Set α},   MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (symmDiff s₁ s₂)
· 使用定理 `MeasureTheory.dist_indicatorConstLp_eq_norm`：dist_indicatorConstLp_eq_no
rm {t : Set α} {ht : MeasurableSet t} {hμt : μ t != ∞} : dist (indicatorConstLp 
p hs hμs c) (indicatorConstLp p h…
· 使用定理 `MeasureTheory.norm_indicatorConstLp`：norm_indicatorConstLp (hp_ne_zero :
 p != 0) (hp_ne_top : p != ∞) : ‖indicatorConstLp p hs hμs c‖ = ‖c‖ * μ.real s ^
 (1 / p.toReal)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Real.zero_rpow`：zero_rpow {x : Real} (h : x != 0) : (0 : Real) ^ x = 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.Tendsto.mul`：Filter.Tendsto.mul {α : Type*} {f g : α -> M} {x : F
ilter α} {a b : M} (hf : Tendsto f x (𝓝 a)) (hg : Tendsto g x (𝓝 b)) : Tendsto (
fun x =>…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
（共 41 条，此处仅展示前 30 条）

--- 原说明 ---
A family of `indicatorConstLp` functions tends to an `indicatorConstLp`,
if the underlying sets tend to the set in the sense of the measure of the symmet
ric difference.
-/
theorem tendsto_indicatorConstLp_set [hp₁ : Fact (1 ≤ p)] {β : Type*} {l : Filter β} {t : β → Set α}
    {ht : ∀ b, MeasurableSet (t b)} {hμt : ∀ b, μ (t b) ≠ ∞} (hp : p ≠ ∞)
    (h : Tendsto (fun b ↦ μ (t b ∆ s)) l (𝓝 0)) :
    Tendsto (fun b ↦ indicatorConstLp p (ht b) (hμt b) c) l (𝓝 (indicatorConstLp p hs hμs c)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hp₀ : p ≠ 0 := (one_pos.trans_le hp₁.out).ne'
  simp only [dist_indicatorConstLp_eq_norm, norm_indicatorConstLp hp₀ hp]
  convert!
    tendsto_const_nhds.mul (((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h).rpow_const _)
  · simp [ENNReal.toReal_eq_zero_iff, hp, hp₀]
  · simp

/-- A family of `indicatorConstLp` functions is continuous in the parameter,
if `μ (s y ∆ s x)` tends to zero as `y` tends to `x` for all `x`. -/
/-
**MeasureTheory.continuous_indicatorConstLp_set** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
形式化陈述：continuous_indicatorConstLp_set [Fact (1 <= p)] {X : Type*} [TopologicalSp
ace X] {s : X -> Set α} {hs : forall x, MeasurableSet (s x)} {hμs : forall x, μ 
(s x) != ∞} (hp : p != ∞) (h : forall x, Tendsto (fun y => μ (s y ∆ s x)) (𝓝 x) 
(𝓝 0)) : Continuous fun x => indicatorConstLp p (hs x) (hμs x) c
参数：1 <= p；s x；s x；hp : p != ∞；h : forall x, Tendsto (fun y => μ (s y ∆ s x)) (𝓝 
x) (𝓝 0)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `MeasureTheory.tendsto_indicatorConstLp_set`：tendsto_indicatorConstLp_set
 [hp₁ : Fact (1 <= p)] {β : Type*} {l : Filter β} {t : β -> Set α} {ht : forall 
b, MeasurableSet (t b)} {hμt : f…

--- 原说明 ---
A family of `indicatorConstLp` functions is continuous in the parameter,
if `μ (s y ∆ s x)` tends to zero as `y` tends to `x` for all `x`.
-/
theorem continuous_indicatorConstLp_set [Fact (1 ≤ p)] {X : Type*} [TopologicalSpace X]
    {s : X → Set α} {hs : ∀ x, MeasurableSet (s x)} {hμs : ∀ x, μ (s x) ≠ ∞} (hp : p ≠ ∞)
    (h : ∀ x, Tendsto (fun y ↦ μ (s y ∆ s x)) (𝓝 x) (𝓝 0)) :
    Continuous fun x ↦ indicatorConstLp p (hs x) (hμs x) c :=
  continuous_iff_continuousAt.2 fun x ↦ tendsto_indicatorConstLp_set hp (h x)

@[simp]
/-
**MeasureTheory.indicatorConstLp_empty** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：indicatorConstLp_empty : indicatorConstLp p MeasurableSet.empty (by simp :
 μ ∅ != ∞) c = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasurableSet.empty`：MeasurableSet.empty [MeasurableSpace α] : Measurabl
eSet (∅ : Set α)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.MemLp.toLp.congr_simp`：∀ {α : Type u_1} {E : Type u_4} {m 
: MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : Norme
dAddCommGroup E] (f f_1 :…
· 使用定理 `Set.indicator_empty'`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] (f
 : α → M), ∅.indicator f = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem indicatorConstLp_empty :
    indicatorConstLp p MeasurableSet.empty (by simp : μ ∅ ≠ ∞) c = 0 := by
  simp only [indicatorConstLp, Set.indicator_empty', MemLp.toLp_zero]
/-
**MeasureTheory.indicatorConstLp_inj** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：indicatorConstLp_inj {s t : Set α} (hs : MeasurableSet s) (hsμ : μ s != ∞)
 (ht : MeasurableSet t) (htμ : μ t != ∞) {c : E} (hc : c != 0) : indicatorConstL
p p hs hsμ c = indicatorConstLp p ht htμ c ↔ s =ᵐ[μ] t
参数：hs : MeasurableSet s；hsμ : μ s != ∞；ht : MeasurableSet t；htμ : μ t != ∞；hc : 
c != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.indicator_const_eventuallyEq`：∀ {α : Type u_1} {β : Type u_2} [in
st : Zero β] {l : Filter α} {c : β},   c ≠ 0 → ∀ {s t : Set α}, ((s.indicator fu
n x => c) =ᶠ[l] t.indicat…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem indicatorConstLp_inj {s t : Set α} (hs : MeasurableSet s) (hsμ : μ s ≠ ∞)
    (ht : MeasurableSet t) (htμ : μ t ≠ ∞) {c : E} (hc : c ≠ 0) :
    indicatorConstLp p hs hsμ c = indicatorConstLp p ht htμ c ↔ s =ᵐ[μ] t := by
  simp_rw [← indicator_const_eventuallyEq hc, indicatorConstLp, MemLp.toLp_eq_toLp_iff]
/-
**MeasureTheory.memLp_add_of_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：memLp_add_of_disjoint {f g : α -> E} (h : Disjoint (support f) (support g)
) (hf : StronglyMeasurable f) (hg : StronglyMeasurable g) : MemLp (f + g) p μ ↔ 
MemLp f p μ ∧ MemLp g p μ
参数：h : Disjoint (support f) (support g)；hf : StronglyMeasurable f；hg : StronglyM
easurable g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.indicator_add_eq_left`：∀ {α : Type u_1} {M : Type u_4} [inst : AddZe
roClass M] {f g : α → M},   Disjoint (Function.support f) (Function.support g) →
 (Function.supp…
· 使用定理 `MeasureTheory.MemLp.indicator`：∀ {α : Type u_1} {m0 : MeasurableSpace α}
 {p : ENNReal} {μ : MeasureTheory.Measure α} {ε : Type u_7}   [inst : Topologica
lSpace ε] [inst_1 :…
· 使用定理 `measurableSet_support`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {m : 
MeasurableSpace α} {mβ : MeasurableSpace β} [inst : Zero β]   [MeasurableSinglet
onClass β],…
· 使用定理 `OpensMeasurableSpace.toMeasurableSingletonClass`：∀ {α : Type u_1} [inst 
: TopologicalSpace α] [inst_1 : MeasurableSpace α] [OpensMeasurableSpace α] [T1S
pace α],   MeasurableSingletonClass α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `MeasureTheory.StronglyMeasurable.measurable`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [Topologi
calSpace.PseudoMetrizableSpace β]…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `Set.indicator_add_eq_right`：∀ {α : Type u_1} {M : Type u_4} [inst : AddZ
eroClass M] {f g : α → M},   Disjoint (Function.support f) (Function.support g) 
→ (Function.supp…
· 使用定理 `MeasureTheory.MemLp.add`：∀ {α : Type u_1} {ε : Type u_3} {m : Measurable
Space α} [inst : TopologicalSpace ε] [inst_1 : ESeminormedAddMonoid ε]   {p : EN
NReal} {μ : M…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem memLp_add_of_disjoint {f g : α → E} (h : Disjoint (support f) (support g))
    (hf : StronglyMeasurable f) (hg : StronglyMeasurable g) :
    MemLp (f + g) p μ ↔ MemLp f p μ ∧ MemLp g p μ := by
  borelize E
  refine ⟨fun hfg => ⟨?_, ?_⟩, fun h => h.1.add h.2⟩
  · rw [← Set.indicator_add_eq_left h]; exact hfg.indicator (measurableSet_support hf.measurable)
  · rw [← Set.indicator_add_eq_right h]; exact hfg.indicator (measurableSet_support hg.measurable)

/-- The indicator of a disjoint union of two sets is the sum of the indicators of the sets. -/
/-
**MeasureTheory.indicatorConstLp_disjoint_union** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
形式化陈述：indicatorConstLp_disjoint_union {s t : Set α} (hs : MeasurableSet s) (ht :
 MeasurableSet t) (hμs : μ s != ∞) (hμt : μ t != ∞) (hst : Disjoint s t) (c : E)
 : indicatorConstLp p (hs.union ht) (by finiteness) c = indicatorConstLp p hs hμ
s c + indicatorConstLp p ht hμt c
参数：hs : MeasurableSet s；ht : MeasurableSet t；hμs : μ s != ∞；hμt : μ t != ∞；hst :
 Disjoint s t；c : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Lp.ext`：ext {f g : Lp E p μ} (h : f =ᵐ[μ] g) : f = g
· 使用定理 `MeasurableSet.union`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∪ s₂)
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用引理 `Mathlib.Tactic.GCongr.rel_imp_rel`：rel_imp_rel (h₁ : r c a) (h₂ : r b d)
 : r a b -> r c d
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `instIsTransOfTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [Trans r r r], I
sTrans α r
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.Lp.coeFn_add`：coeFn_add (f g : Lp E p μ) : ⇑(f + g) =ᵐ[μ] 
f + g
· 使用定理 `MeasureTheory.indicatorConstLp_coeFn`：indicatorConstLp_coeFn : ⇑(indicat
orConstLp p hs hμs c) =ᵐ[μ] s.indicator fun _ => c
· 使用定理 `Filter.EventuallyEq.add`：∀ {α : Type u} {β : Type v} [inst : Add β] {f f
' g g' : α → β} {l : Filter α},   f =ᶠ[l] g → f' =ᶠ[l] g' → f + f' =ᶠ[l] g + g'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.indicator_union_of_disjoint`：∀ {α : Type u_1} {M : Type u_4} [inst :
 AddZeroClass M] {s t : Set α},   Disjoint s t → ∀ (f : α → M), (s ∪ t).indicato
r f = fun a => s.indi…
· 使用定理 `Pi.add_def`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Add (M
 i)] (f g : (i : ι) → M i), f + g = fun i => f i + g i

--- 原说明 ---
The indicator of a disjoint union of two sets is the sum of the indicators of th
e sets.
-/
theorem indicatorConstLp_disjoint_union {s t : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hμs : μ s ≠ ∞) (hμt : μ t ≠ ∞) (hst : Disjoint s t) (c : E) :
    indicatorConstLp p (hs.union ht) (by finiteness) c =
      indicatorConstLp p hs hμs c + indicatorConstLp p ht hμt c := by
  ext1
  grw [Lp.coeFn_add, indicatorConstLp_coeFn, indicatorConstLp_coeFn, indicatorConstLp_coeFn]
  rw [Set.indicator_union_of_disjoint hst, Pi.add_def]
end IndicatorConstLp

section const

variable (μ p)
variable [IsFiniteMeasure μ] (c : E)

/-- Constant function as an element of `MeasureTheory.Lp` for a finite measure. -/
/-
**MeasureTheory.Lp.const** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：{α : Type u_1} →   {E : Type u_2} →     {m : MeasurableSpace α} →       (p
 : ENNReal) →         (μ : MeasureTheory.Measure α) →           [inst : NormedAd
dCommGroup E] → [MeasureTheory.IsFiniteMeasure μ] → E →+ ↥(MeasureTheory.Lp E p 
μ)
参数：p : ENNReal；μ : MeasureTheory.Measure α；MeasureTheory.Lp E p μ。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Lp.const_mem_Lp`：const_mem_Lp (α) {_ : MeasurableSpace α} 
(μ : Measure α) (c : E) [IsFiniteMeasure μ] : @AEEqFun.const α _ _ μ _ c in Lp E
 p μ

--- 原说明 ---
Constant function as an element of `MeasureTheory.Lp` for a finite measure.
-/
protected def Lp.const : E →+ Lp E p μ where
  toFun c := ⟨AEEqFun.const α c, const_mem_Lp α μ c⟩
  map_zero' := rfl
  map_add' _ _ := rfl
/-
**MeasureTheory.Lp.coeFn_const** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：∀ {α : Type u_1} {E : Type u_2} {m : MeasurableSpace α} (p : ENNReal) (μ :
 MeasureTheory.Measure α)   [inst : NormedAddCommGroup E] [inst_1 : MeasureTheor
y.IsFiniteMeasure μ] (c : E),   ↑↑((MeasureTheory.Lp.const p μ) c) =ᵐ[μ] Functio
n.const α c
参数：p : ENNReal；μ : MeasureTheory.Measure α；c : E；(MeasureTheory.Lp.const p μ) c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEEqFun.coeFn_const`：coeFn_const (b : β) : (const α b : α 
->ₘ[μ] β) =ᵐ[μ] Function.const α b
-/
lemma Lp.coeFn_const : Lp.const p μ c =ᵐ[μ] Function.const α c :=
  AEEqFun.coeFn_const α c
/-
**MeasureTheory.Lp.const_val** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：∀ {α : Type u_1} {E : Type u_2} {m : MeasurableSpace α} (p : ENNReal) (μ :
 MeasureTheory.Measure α)   [inst : NormedAddCommGroup E] [inst_1 : MeasureTheor
y.IsFiniteMeasure μ] (c : E),   ↑((MeasureTheory.Lp.const p μ) c) = MeasureTheor
y.AEEqFun.const α c
参数：p : ENNReal；μ : MeasureTheory.Measure α；c : E；(MeasureTheory.Lp.const p μ) c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
@[simp] lemma Lp.const_val : (Lp.const p μ c).1 = AEEqFun.const α c := rfl

@[simp]
/-
**MeasureTheory.MemLp.toLp_const** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.MemLp`
。
形式化陈述：∀ {α : Type u_1} {E : Type u_2} {m : MeasurableSpace α} (p : ENNReal) (μ :
 MeasureTheory.Measure α)   [inst : NormedAddCommGroup E] [inst_1 : MeasureTheor
y.IsFiniteMeasure μ] (c : E),   MeasureTheory.MemLp.toLp (fun x => c) ⋯ = (Measu
reTheory.Lp.const p μ) c
参数：p : ENNReal；μ : MeasureTheory.Measure α；c : E；fun x => c；MeasureTheory.Lp.con
st p μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.memLp_const`：memLp_const (c : E) [IsFiniteMeasure μ] : Mem
Lp (fun _ : α => c) p μ
-/
lemma MemLp.toLp_const : MemLp.toLp _ (memLp_const c) = Lp.const p μ c := rfl

@[simp]
/-
**MeasureTheory.indicatorConstLp_univ** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：indicatorConstLp_univ : indicatorConstLp p .univ (measure_ne_top μ _) c = 
Lp.const p μ c
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `MeasureTheory.memLp_const`：memLp_const (c : E) [IsFiniteMeasure μ] : Mem
Lp (fun _ : α => c) p μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.MemLp.toLp_const`：∀ {α : Type u_1} {E : Type u_2} {m : Mea
surableSpace α} (p : ENNReal) (μ : MeasureTheory.Measure α)   [inst : NormedAddC
ommGroup E] [inst_1 …
· 使用定理 `MeasureTheory.indicatorConstLp.eq_1`：∀ {α : Type u_1} {E : Type u_2} {m 
: MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup E]
   {s : Set α} (p : ENNRe…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.indicator_univ`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] (f :
 α → M), Set.univ.indicator f = f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.MemLp.toLp.congr_simp`：∀ {α : Type u_1} {E : Type u_4} {m 
: MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : Norme
dAddCommGroup E] (f f_1 :…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma indicatorConstLp_univ :
    indicatorConstLp p .univ (measure_ne_top μ _) c = Lp.const p μ c := by
  rw [← MemLp.toLp_const, indicatorConstLp]
  simp only [Set.indicator_univ]
/-
**MeasureTheory.Lp.norm_const** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：∀ {α : Type u_1} {E : Type u_2} {m : MeasurableSpace α} (p : ENNReal) (μ :
 MeasureTheory.Measure α)   [inst : NormedAddCommGroup E] [inst_1 : MeasureTheor
y.IsFiniteMeasure μ] (c : E) [NeZero μ],   p ≠ 0 → ‖(MeasureTheory.Lp.const p μ)
 c‖ = ‖c‖ * μ.real Set.univ ^ (1 / p.toReal)
参数：p : ENNReal；μ : MeasureTheory.Measure α；c : E；MeasureTheory.Lp.const p μ；1 / 
p.toReal。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.memLp_const`：memLp_const (c : E) [IsFiniteMeasure μ] : Mem
Lp (fun _ : α => c) p μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.MemLp.toLp_const`：∀ {α : Type u_1} {E : Type u_2} {m : Mea
surableSpace α} (p : ENNReal) (μ : MeasureTheory.Measure α)   [inst : NormedAddC
ommGroup E] [inst_1 …
· 使用引理 `MeasureTheory.Lp.norm_toLp`：norm_toLp (f : α -> E) (hf : MemLp f p μ) : 
‖hf.toLp f‖ = ENNReal.toReal (eLpNorm f p μ)
· 使用定理 `MeasureTheory.eLpNorm_const`：eLpNorm_const (c : ε) (h0 : p != 0) (hμ : μ
 != 0) : eLpNorm (fun _ : α => c) p μ = ‖c‖ₑ * μ Set.univ ^ (1 / ENNReal.toReal 
p)
· 使用定理 `MeasureTheory.measureReal_def`：measureReal_def {α : Type*} {m : Measurab
leSpace α} (μ : Measure α) (s : Set α) : μ.real s = (μ s).toReal
· 使用定理 `ENNReal.toReal_mul`：toReal_mul : (a * b).toReal = a.toReal * b.toReal
· 使用定理 `toReal_enorm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (x : E), ‖x
‖ₑ.toReal = ‖x‖
· 使用定理 `ENNReal.toReal_rpow`：toReal_rpow (x : Real>=0∞) (z : Real) : x.toReal ^ 
z = (x ^ z).toReal
-/
theorem Lp.norm_const [NeZero μ] (hp_zero : p ≠ 0) :
    ‖Lp.const p μ c‖ = ‖c‖ * μ.real Set.univ ^ (1 / p.toReal) := by
  have := NeZero.ne μ
  rw [← MemLp.toLp_const, Lp.norm_toLp, eLpNorm_const] <;> try assumption
  rw [measureReal_def, ENNReal.toReal_mul, toReal_enorm, ← ENNReal.toReal_rpow]
/-
**MeasureTheory.Lp.norm_const'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：∀ {α : Type u_1} {E : Type u_2} {m : MeasurableSpace α} (p : ENNReal) (μ :
 MeasureTheory.Measure α)   [inst : NormedAddCommGroup E] [inst_1 : MeasureTheor
y.IsFiniteMeasure μ] (c : E),   p ≠ 0 → p ≠ ⊤ → ‖(MeasureTheory.Lp.const p μ) c‖
 = ‖c‖ * μ.real Set.univ ^ (1 / p.toReal)
参数：p : ENNReal；μ : MeasureTheory.Measure α；c : E；MeasureTheory.Lp.const p μ；1 / 
p.toReal。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.memLp_const`：memLp_const (c : E) [IsFiniteMeasure μ] : Mem
Lp (fun _ : α => c) p μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.MemLp.toLp_const`：∀ {α : Type u_1} {E : Type u_2} {m : Mea
surableSpace α} (p : ENNReal) (μ : MeasureTheory.Measure α)   [inst : NormedAddC
ommGroup E] [inst_1 …
· 使用引理 `MeasureTheory.Lp.norm_toLp`：norm_toLp (f : α -> E) (hf : MemLp f p μ) : 
‖hf.toLp f‖ = ENNReal.toReal (eLpNorm f p μ)
· 使用定理 `MeasureTheory.eLpNorm_const'`：eLpNorm_const' (c : ε) (h0 : p != 0) (h_to
p : p != ∞) : eLpNorm (fun _ : α => c) p μ = ‖c‖ₑ * μ Set.univ ^ (1 / ENNReal.to
Real p)
· 使用定理 `MeasureTheory.measureReal_def`：measureReal_def {α : Type*} {m : Measurab
leSpace α} (μ : Measure α) (s : Set α) : μ.real s = (μ s).toReal
· 使用定理 `ENNReal.toReal_mul`：toReal_mul : (a * b).toReal = a.toReal * b.toReal
· 使用定理 `toReal_enorm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (x : E), ‖x
‖ₑ.toReal = ‖x‖
· 使用定理 `ENNReal.toReal_rpow`：toReal_rpow (x : Real>=0∞) (z : Real) : x.toReal ^ 
z = (x ^ z).toReal
-/
theorem Lp.norm_const' (hp_zero : p ≠ 0) (hp_top : p ≠ ∞) :
    ‖Lp.const p μ c‖ = ‖c‖ * μ.real Set.univ ^ (1 / p.toReal) := by
  rw [← MemLp.toLp_const, Lp.norm_toLp, eLpNorm_const'] <;> try assumption
  rw [measureReal_def, ENNReal.toReal_mul, toReal_enorm, ← ENNReal.toReal_rpow]
/-
**MeasureTheory.Lp.norm_const_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：∀ {α : Type u_1} {E : Type u_2} {m : MeasurableSpace α} (p : ENNReal) (μ :
 MeasureTheory.Measure α)   [inst : NormedAddCommGroup E] [inst_1 : MeasureTheor
y.IsFiniteMeasure μ] (c : E),   ‖(MeasureTheory.Lp.const p μ) c‖ ≤ ‖c‖ * μ.real 
Set.univ ^ (1 / p.toReal)
参数：p : ENNReal；μ : MeasureTheory.Measure α；c : E；MeasureTheory.Lp.const p μ；1 / 
p.toReal。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.indicatorConstLp_univ`：indicatorConstLp_univ : indicatorCo
nstLp p .univ (measure_ne_top μ _) c = Lp.const p μ c
· 使用定理 `MeasureTheory.norm_indicatorConstLp_le`：norm_indicatorConstLp_le : ‖indi
catorConstLp p hs hμs c‖ <= ‖c‖ * μ.real s ^ (1 / p.toReal)
-/
theorem Lp.norm_const_le : ‖Lp.const p μ c‖ ≤ ‖c‖ * μ.real Set.univ ^ (1 / p.toReal) := by
  rw [← indicatorConstLp_univ]
  exact norm_indicatorConstLp_le

/-- `MeasureTheory.Lp.const` as a `LinearMap`. -/
/-
**MeasureTheory.Lp.const** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：{α : Type u_1} →   {E : Type u_2} →     {m : MeasurableSpace α} →       (p
 : ENNReal) →         (μ : MeasureTheory.Measure α) →           [inst : NormedAd
dCommGroup E] → [MeasureTheory.IsFiniteMeasure μ] → E →+ ↥(MeasureTheory.Lp E p 
μ)
参数：p : ENNReal；μ : MeasureTheory.Measure α；MeasureTheory.Lp E p μ。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Lp.const_mem_Lp`：const_mem_Lp (α) {_ : MeasurableSpace α} 
(μ : Measure α) (c : E) [IsFiniteMeasure μ] : @AEEqFun.const α _ _ μ _ c in Lp E
 p μ

--- 原说明 ---
`MeasureTheory.Lp.const` as a `LinearMap`.
-/
@[simps] protected def Lp.constₗ (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] :
    E →ₗ[𝕜] Lp E p μ where
  toFun := Lp.const p μ
  map_add' := map_add _
  map_smul' _ _ := rfl

/-- `MeasureTheory.Lp.const` as a `ContinuousLinearMap`. -/
@[simps! apply]
/-
**MeasureTheory.Lp.constL** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：{α : Type u_1} →   {E : Type u_2} →     {m : MeasurableSpace α} →       (p
 : ENNReal) →         (μ : MeasureTheory.Measure α) →           [inst : NormedAd
dCommGroup E] →             [MeasureTheory.IsFiniteMeasure μ] →               (𝕜
 : Type u_3) →                 [inst_2 : NormedRing 𝕜] →                   [inst
_3 : _root_.Module 𝕜 E] →                     [inst_4 : IsBoundedSMul 𝕜 E] → [in
st_5 : Fact (1 ≤ p)] → E →L[𝕜] ↥(MeasureTheory.Lp E p μ)
参数：p : ENNReal；μ : MeasureTheory.Measure α；𝕜 : Type u_3；1 ≤ p；MeasureTheory.Lp E
 p μ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`MeasureTheory.Lp.const` as a `ContinuousLinearMap`.
-/
protected def Lp.constL (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] [Fact (1 ≤ p)] :
    E →L[𝕜] Lp E p μ :=
  (Lp.constₗ p μ 𝕜).mkContinuous (μ.real Set.univ ^ (1 / p.toReal)) fun _ ↦
    (Lp.norm_const_le _ _ _).trans_eq (mul_comm _ _)
/-
**MeasureTheory.Lp.norm_constL_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：∀ {α : Type u_1} {E : Type u_2} {m : MeasurableSpace α} (p : ENNReal) (μ :
 MeasureTheory.Measure α)   [inst : NormedAddCommGroup E] [inst_1 : MeasureTheor
y.IsFiniteMeasure μ] (𝕜 : Type u_3)   [inst_2 : NontriviallyNormedField 𝕜] [inst
_3 : NormedSpace 𝕜 E] [inst_4 : Fact (1 ≤ p)],   ‖MeasureTheory.Lp.constL p μ 𝕜‖
 ≤ μ.real Set.univ ^ (1 / p.toReal)
参数：p : ENNReal；μ : MeasureTheory.Measure α；𝕜 : Type u_3；1 ≤ p；1 / p.toReal。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.mkContinuous_norm_le`：mkContinuous_norm_le (f : E ->ₛₗ[σ₁₂] F)
 {C : Real} (hC : 0 <= C) (h : forall x, ‖f x‖ <= C * ‖x‖) : ‖f.mkContinuous C h
‖ <= C
· 使用定理 `Real.rpow_nonneg`：rpow_nonneg {x : Real} (hx : 0 <= x) (y : Real) : 0 <=
 x ^ y
· 使用定理 `MeasureTheory.measureReal_nonneg`：∀ {α : Type u_1} {x : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α}, 0 ≤ μ.real s
-/
theorem Lp.norm_constL_le (𝕜 : Type*) [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]
    [Fact (1 ≤ p)] :
    ‖(Lp.constL p μ 𝕜 : E →L[𝕜] Lp E p μ)‖ ≤ μ.real Set.univ ^ (1 / p.toReal) :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

end const

namespace Lp

variable {β : Type*} [MeasurableSpace β] {μb : MeasureTheory.Measure β} {f : α → β}

/-
**MeasureTheory.Lp.indicatorConstLp_compMeasurePreserving** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory.Lp`。
形式化陈述：indicatorConstLp_compMeasurePreserving {s : Set β} (hs : MeasurableSet s) 
(hμs : μb s != ∞) (c : E) (hf : MeasurePreserving f μ μb) : Lp.compMeasurePreser
ving f hf (indicatorConstLp p hs hμs c) = indicatorConstLp p (hs.preimage hf.mea
surable) (by rwa [hf.measure_preimage hs.nullMeasurableSet]) c
参数：hs : MeasurableSet s；hμs : μb s != ∞；c : E；hf : MeasurePreserving f μ μb。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem indicatorConstLp_compMeasurePreserving {s : Set β} (hs : MeasurableSet s)
    (hμs : μb s ≠ ∞) (c : E) (hf : MeasurePreserving f μ μb) :
    Lp.compMeasurePreserving f hf (indicatorConstLp p hs hμs c) =
      indicatorConstLp p (hs.preimage hf.measurable)
        (by rwa [hf.measure_preimage hs.nullMeasurableSet]) c :=
  rfl

end Lp

/-
**MeasureTheory.indicatorConstLp_eq_toSpanSingleton_compLp** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory`。
形式化陈述：indicatorConstLp_eq_toSpanSingleton_compLp {s : Set α} [NormedSpace Real E
] (hs : MeasurableSet s) (hμs : μ s != ∞) (x : E) : indicatorConstLp 2 hs hμs x 
= (ContinuousLinearMap.toSpanSingleton Real x).compLp (indicatorConstLp 2 hs hμs
 (1 : Real))
参数：hs : MeasurableSet s；hμs : μ s != ∞；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Lp.ext`：ext {f g : Lp E p μ} (h : f =ᵐ[μ] g) : f = g
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.indicatorConstLp_coeFn`：indicatorConstLp_coeFn : ⇑(indicat
orConstLp p hs hμs c) =ᵐ[μ] s.indicator fun _ => c
· 使用定理 `ContinuousLinearMap.coeFn_compLp`：coeFn_compLp (L : E ->SL[σ] F) (f : Lp
 E p μ) : forallᵐ a ∂μ, (L.compLp f) a = L (f a)
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.EventuallyEq.eq_1`：∀ {α : Type u_1} {β : Type u_2} (l : Filter α)
 (f g : α → β), (f =ᶠ[l] g) = ∀ᶠ (x : α) in l, f x = g x
-/
theorem indicatorConstLp_eq_toSpanSingleton_compLp {s : Set α} [NormedSpace ℝ E]
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : E) :
    indicatorConstLp 2 hs hμs x =
      (ContinuousLinearMap.toSpanSingleton ℝ x).compLp (indicatorConstLp 2 hs hμs (1 : ℝ)) := by
  ext1
  refine indicatorConstLp_coeFn.trans ?_
  have h_compLp :=
    (ContinuousLinearMap.toSpanSingleton ℝ x).coeFn_compLp (indicatorConstLp 2 hs hμs (1 : ℝ))
  rw [← EventuallyEq] at h_compLp
  refine EventuallyEq.trans ?_ h_compLp.symm
  refine (@indicatorConstLp_coeFn _ _ _ 2 μ _ s hs hμs (1 : ℝ)).mono fun y hy => ?_
  dsimp only
  rw [hy]
  simp_rw [ContinuousLinearMap.toSpanSingleton_apply]
  by_cases hy_mem : y ∈ s <;> simp [hy_mem]

end MeasureTheory

