/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lp

/-!
# If an `Lp` space is complete, so is the target space
-/

@[expose] public section

open scoped ENNReal Topology
open Filter ContinuousLinearMap

namespace MeasureTheory

variable {α E : Type*} [NormedAddCommGroup E] {mα : MeasurableSpace α} {p : ℝ≥0∞} {μ : Measure α}

/-
**MeasureTheory.FinStronglyMeasurable.exists_measurableSet_measure_pos_lt_top** 
是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.FinStronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {E : Type u_2} [inst : NormedAddCommGroup E] {mα : Measur
ableSpace α} {μ : MeasureTheory.Measure α}   {f : α → E}, MeasureTheory.FinStron
glyMeasurable f μ → ¬f =ᵐ[μ] 0 → ∃ s, MeasurableSet s ∧ 0 < μ s ∧ μ s < ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `MeasureTheory.SimpleFunc.measurableSet_support`：measurableSet_support [M
easurableSpace α] (f : α ->ₛ β) : MeasurableSet (support f)
· 使用定理 `lt_of_le_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.ae_all_iff`：ae_all_iff {ι : Sort*} [Countable ι] {p : α ->
 ι -> Prop} : (forallᵐ a ∂μ, forall i, p a i) ↔ forall i, forallᵐ a ∂μ, p a i
· 使用定理 `instCountableNat`：Countable ℕ
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
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
（共 32 条，此处仅展示前 30 条）
-/
lemma FinStronglyMeasurable.exists_measurableSet_measure_pos_lt_top {f : α → E}
    (hf : FinStronglyMeasurable f μ) (h'f : ¬(f =ᵐ[μ] 0)) :
    ∃ s, MeasurableSet s ∧ 0 < μ s ∧ μ s < ∞ := by
  contrapose! h'f
  rcases hf with ⟨fn, hfn, hfn_lim⟩
  have A n : μ (Function.support (fn n)) = 0 := by
    by_contra!
    have := h'f (Function.support (fn n)) (fn n).measurableSet_support (by positivity)
    grind
  have B : ∀ᵐ x ∂μ, ∀ n, fn n x = 0 := ae_all_iff.mpr A
  filter_upwards [B] with x hx
  apply tendsto_nhds_unique (hfn_lim x)
  simp [hx]
/-
**MeasureTheory.AEFinStronglyMeasurable.exists_measurableSet_measure_pos_lt_top*
* 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEFinStronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {E : Type u_2} [inst : NormedAddCommGroup E] {mα : Measur
ableSpace α} {μ : MeasureTheory.Measure α}   {f : α → E}, MeasureTheory.AEFinStr
onglyMeasurable f μ → ¬f =ᵐ[μ] 0 → ∃ s, MeasurableSet s ∧ 0 < μ s ∧ μ s < ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.FinStronglyMeasurable.exists_measurableSet_measure_pos_lt_
top`：∀ {α : Type u_1} {E : Type u_2} [inst : NormedAddCommGroup E] {mα : Measura
bleSpace α} {μ : MeasureTheory.Measure α}   {f : α → E}, MeasureT…
· 使用定理 `MeasureTheory.AEFinStronglyMeasurable.finStronglyMeasurable_mk`：finStron
glyMeasurable_mk (hf : AEFinStronglyMeasurable f μ) : FinStronglyMeasurable (hf.
mk f) μ
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `MeasureTheory.AEFinStronglyMeasurable.ae_eq_mk`：ae_eq_mk (hf : AEFinStro
nglyMeasurable f μ) : f =ᵐ[μ] hf.mk f
-/
lemma AEFinStronglyMeasurable.exists_measurableSet_measure_pos_lt_top {f : α → E}
    (hf : AEFinStronglyMeasurable f μ) (h'f : ¬(f =ᵐ[μ] 0)) :
    ∃ s, MeasurableSet s ∧ 0 < μ s ∧ μ s < ∞ := by
  apply hf.finStronglyMeasurable_mk.exists_measurableSet_measure_pos_lt_top
  contrapose! h'f
  exact hf.ae_eq_mk.trans h'f

variable (E p μ) in
/-
**MeasureTheory.nontrivial_Lp_real_of_nontrivial_Lp** 是 Mathlib 中的一个引理，位于命名空间 `M
easureTheory`。
形式化陈述：nontrivial_Lp_real_of_nontrivial_Lp [Nontrivial (Lp E p μ)] : Nontrivial (
Lp Real p μ)
参数：Lp E p μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `MeasureTheory.Lp.ext`：ext {f g : Lp E p μ} (h : f =ᵐ[μ] g) : f = g
· 使用引理 `Mathlib.Tactic.GCongr.rel_imp_rel`：rel_imp_rel (h₁ : r c a) (h₂ : r b d)
 : r a b -> r c d
· 使用定理 `instIsTransOfTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [Trans r r r], I
sTrans α r
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.Lp.coeFn_zero`：coeFn_zero : ⇑(0 : Lp E p μ) =ᵐ[μ] 0
· 使用定理 `eq_top_or_lt_top`：eq_top_or_lt_top (a : α) : a = ⊤ ∨ a < ⊤
· 使用定理 `nontrivial_of_ne`：nontrivial_of_ne (x y : α) (h : x != y) : Nontrivial α
· 使用定理 `MeasureTheory.memLp_top_const`：memLp_top_const (c : E) : MemLp (fun _ : 
α => c) ∞ μ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.Lp.ext_iff`：∀ {α : Type u_1} {E : Type u_4} {m : Measurabl
eSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddCommGro
up E] {f g : ↥…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.MemLp.coeFn_toLp`：coeFn_toLp {f : α -> E} (hf : MemLp f p 
μ) : hf.toLp f =ᵐ[μ] f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `MeasureTheory.aestronglyMeasurable_const`：aestronglyMeasurable_const {b 
: β} : AEStronglyMeasurable[m] (fun _ : α => b) μ
· 使用定理 `MeasureTheory.MemLp.aefinStronglyMeasurable`：∀ {α : Type u_1} {G : Type 
u_2} {p : ENNReal} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [ins
t : NormedAddCommGroup G] {f : α …
· 使用定理 `MeasureTheory.Lp.memLp`：∀ {α : Type u_1} {E : Type u_4} {m : MeasurableS
pace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddCommGroup
 E] (f : ↥(M…
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `MeasureTheory.AEFinStronglyMeasurable.exists_measurableSet_measure_pos_l
t_top`：∀ {α : Type u_1} {E : Type u_2} [inst : NormedAddCommGroup E] {mα : Measu
rableSpace α} {μ : MeasureTheory.Measure α}   {f : α → E}, MeasureT…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
（共 50 条，此处仅展示前 30 条）
-/
lemma nontrivial_Lp_real_of_nontrivial_Lp [Nontrivial (Lp E p μ)] : Nontrivial (Lp ℝ p μ) := by
  obtain ⟨f, hf⟩ : ∃ f : Lp E p μ, f ≠ 0 := exists_ne 0
  have hfne : ¬ (f =ᵐ[μ] 0) := by
    contrapose! hf
    ext
    grw [hf, Lp.coeFn_zero E p μ]
  rcases eq_top_or_lt_top p with rfl | h'p
  · apply nontrivial_of_ne ((memLp_top_const (1 : ℝ)).toLp _) 0
    contrapose! hfne
    have := Lp.ext_iff.1 hfne
    grw [Lp.coeFn_zero, MemLp.coeFn_toLp] at this
    filter_upwards [this] with x hx using by simp at hx
  rcases eq_or_ne p 0 with rfl | hp
  · have : MemLp (fun (_ : α) ↦ (1 : ℝ)) 0 μ := by simpa using aestronglyMeasurable_const
    apply nontrivial_of_ne (this.toLp _) 0
    contrapose! hfne
    have := Lp.ext_iff.1 hfne
    grw [Lp.coeFn_zero, MemLp.coeFn_toLp] at this
    filter_upwards [this] with x hx using by simp at hx
  · have h'f : AEFinStronglyMeasurable f μ :=
      MemLp.aefinStronglyMeasurable (Lp.memLp f) hp h'p.ne
    obtain ⟨s, s_meas, s_pos, s_top⟩ : ∃ s, MeasurableSet s ∧ 0 < μ s ∧ μ s < ∞ :=
      h'f.exists_measurableSet_measure_pos_lt_top hfne
    apply nontrivial_of_ne (indicatorConstLp p s_meas s_top.ne 1) 0
    intro hzero
    have : ‖indicatorConstLp p s_meas s_top.ne (1 : ℝ)‖ = ‖(0 : Lp ℝ p μ)‖ := by rw [hzero]
    simp only [norm_indicatorConstLp hp h'p.ne, norm_one, one_div, one_mul, Lp.norm_zero] at this
    rw [Real.rpow_eq_zero (by positivity) (by simp [ENNReal.toReal_eq_zero_iff, hp, h'p.ne]),
      measureReal_eq_zero_iff] at this
    order

variable [NormedSpace ℝ E]

variable (E p μ) in
/-- If an `L^p` space is complete and nontrivial, then the target space is complete. -/
/-
**MeasureTheory.completeSpace_of_completeSpace_Lp** 是 Mathlib 中的一个引理，位于命名空间 `Mea
sureTheory`。
形式化陈述：completeSpace_of_completeSpace_Lp [hp : Fact (1 <= p)] [CompleteSpace (Lp 
E p μ)] [Nontrivial (Lp E p μ)] : CompleteSpace E
参数：1 <= p；Lp E p μ；Lp E p μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用引理 `MeasureTheory.nontrivial_Lp_real_of_nontrivial_Lp`：nontrivial_Lp_real_of
_nontrivial_Lp [Nontrivial (Lp E p μ)] : Nontrivial (Lp Real p μ)
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Metric.complete_of_cauchySeq_tendsto`：Metric.complete_of_cauchySeq_tends
to : (forall u : Nat -> α, CauchySeq u -> exists a, Tendsto u atTop (𝓝 a)) -> Co
mpleteSpace α
· 使用定理 `cauchySeq_tendsto_of_complete`：cauchySeq_tendsto_of_complete [Preorder β
] [CompleteSpace α] {u : β -> α} (H : CauchySeq u) : exists x, Tendsto u atTop (
𝓝 x)
· 使用引理 `LipschitzWith.cauchySeq_comp`：LipschitzWith.cauchySeq_comp {f : α -> β} 
(hf : LipschitzWith K f) {u : Nat -> α} (hu : CauchySeq u) : CauchySeq (f ∘ u)
· 使用定理 `ContinuousLinearMap.lipschitz`：lipschitz (f : E ->SL[σ₁₂] F) : Lipschitz
With ‖f‖₊ f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.TendstoInMeasure.exists_seq_tendsto_ae`：∀ {α : Type u_1} {
E : Type u_4} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Pseu
doEMetricSpace E]   {f : ℕ → α → E} {g : α…
· 使用定理 `MeasureTheory.tendstoInMeasure_of_tendsto_Lp`：tendstoInMeasure_of_tendst
o_Lp [NormedAddCommGroup E] [hp : Fact (1 <= p)] {f : ι -> Lp E p μ} {g : Lp E p
 μ} {l : Filter ι} (hfg : Tendsto …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.ae_restrict_neBot`：ae_restrict_neBot {s} : (ae <| μ.restri
ct s).NeBot ↔ μ s != 0
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `MeasureTheory.Measure.measure_support_eq_zero_iff`：measure_support_eq_ze
ro_iff {E : Type*} [Zero E] (μ : Measure α
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `MeasureTheory.Lp.ext`：ext {f g : Lp E p μ} (h : f =ᵐ[μ] g) : f = g
· 使用引理 `Mathlib.Tactic.GCongr.rel_imp_rel`：rel_imp_rel (h₁ : r c a) (h₂ : r b d)
 : r a b -> r c d
· 使用定理 `instIsTransOfTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [Trans r r r], I
sTrans α r
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.Lp.coeFn_zero`：coeFn_zero : ⇑(0 : Lp E p μ) =ᵐ[μ] 0
· 使用定理 `MeasureTheory.ae_restrict_of_ae`：ae_restrict_of_ae {s : Set α} {p : α ->
 Prop} (h : forallᵐ x ∂μ, p x) : forallᵐ x ∂μ.restrict s, p x
· 使用定理 `MeasureTheory.ae_restrict_mem`：ae_restrict_mem (hs : MeasurableSet s) : 
forallᵐ x ∂μ.restrict s, x in s
· 使用定理 `measurableSet_support`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {m : 
MeasurableSpace α} {mβ : MeasurableSpace β} [inst : Zero β]   [MeasurableSinglet
onClass β],…
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `standardBorel_of_polish`：∀ {α : Type u_1} [inst : MeasurableSpace α] [τ 
: TopologicalSpace α] [BorelSpace α] [PolishSpace α],   StandardBorelSpace α
（共 67 条，此处仅展示前 30 条）

--- 原说明 ---
If an `L^p` space is complete and nontrivial, then the target space is complete.
-/
lemma completeSpace_of_completeSpace_Lp [hp : Fact (1 ≤ p)]
    [CompleteSpace (Lp E p μ)] [Nontrivial (Lp E p μ)] : CompleteSpace E := by
  /- Consider a nonzero function `f : α → ℝ` in `L^p`. Given a Cauchy sequence `uₙ` in `E`, form
  the Cauchy sequence `f • uₙ` in `L^p E`. By completeness, it converges. Consider a subsequence
  which converges almost everywhere. As `f` is nonzero, we get some `x` such that `f x • uₙ`
  converges along this subsequence and `f x ≠ 0`. Then `uₙ` converges along this subsequence, and
  therefore along all indices as it is Cauchy. -/
  obtain ⟨f, hf⟩ : ∃ f : Lp ℝ p μ, f ≠ 0 := by
    have : Nontrivial (Lp ℝ p μ) := nontrivial_Lp_real_of_nontrivial_Lp E p μ
    exact exists_ne 0
  let m : E →L[ℝ] Lp E p μ := ((ContinuousLinearMap.lsmul ℝ ℝ).flip.compLpL₂ p μ).flip f
  apply Metric.complete_of_cauchySeq_tendsto (fun u hu ↦ ?_)
  obtain ⟨g, hg⟩ : ∃ g, Tendsto (m ∘ u) atTop (𝓝 g) :=
    cauchySeq_tendsto_of_complete (m.lipschitz.cauchySeq_comp hu)
  let f' : ℕ → (α → E) := fun n ↦ (m ∘ u) n
  obtain ⟨ns, hns, nslim⟩ : ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ x ∂μ, Tendsto (fun i ↦ f' (ns i) x) atTop (𝓝 (g x)) :=
    (tendstoInMeasure_of_tendsto_Lp hg).exists_seq_tendsto_ae
  have : (ae (μ.restrict (Function.support f))).NeBot := by
    apply ae_restrict_neBot.2
    apply μ.measure_support_eq_zero_iff.not.2
    contrapose! hf
    ext
    grw [Lp.coeFn_zero]
    exact hf
  have A : ∀ᵐ x ∂(μ.restrict (Function.support f)),
    Tendsto (fun i ↦ f' (ns i) x) atTop (𝓝 (g x)) := ae_restrict_of_ae nslim
  have B : ∀ᵐ x ∂(μ.restrict (Function.support f)), x ∈ Function.support f :=
    ae_restrict_mem (measurableSet_support (by fun_prop))
  have C : ∀ᵐ x ∂(μ.restrict (Function.support f)), ∀ n, m (u n) x = (f x) • u n := by
    apply ae_restrict_of_ae
    apply ae_all_iff.2 (fun n ↦ ?_)
    filter_upwards [(toSpanSingleton ℝ (u n)).coeFn_compLp f] with x hx using by simp [m, hx]
  obtain ⟨x, xlim, hx, hmx⟩ : ∃ x, Tendsto (fun i ↦ f' (ns i) x) atTop (𝓝 (g x))
    ∧ x ∈ Function.support f ∧ ∀ n, m (u n) x = (f x) • u n := (A.and (B.and C)).exists
  simp only [Function.comp_apply, hmx, f'] at xlim
  refine ⟨(f x)⁻¹ • g x, ?_⟩
  apply tendsto_nhds_of_cauchySeq_of_subseq hu hns.tendsto_atTop
  convert xlim.const_smul (f x)⁻¹ with n
  rw [smul_smul, inv_mul_cancel₀, one_smul, Function.comp]
  exact hx

end MeasureTheory

