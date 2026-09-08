/-
Copyright (c) 2024 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.Probability.Independence.Basic

/-!
# Independence of functions implies that the measure is a probability measure

If a nonzero function belongs to `ℒ^p` (in particular if it is integrable) and is independent
of another function, then the space is a probability space.

-/

public section

open Filter ProbabilityTheory

open scoped ENNReal NNReal Topology

namespace MeasureTheory

variable {Ω E F : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup E] [MeasurableSpace E] [OpensMeasurableSpace E]
  [MeasurableSpace F]

/-- If a nonzero function belongs to `ℒ^p` and is independent of another function, then
the space is a probability space. -/
/-
**MeasureTheory.MemLp.isProbabilityMeasure_of_indepFun** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.MemLp`。
形式化陈述：∀ {Ω : Type u_1} {E : Type u_2} {F : Type u_3} [inst : MeasurableSpace Ω] 
{μ : MeasureTheory.Measure Ω}   [inst_1 : NormedAddCommGroup E] [inst_2 : Measur
ableSpace E] [OpensMeasurableSpace E] [inst_4 : MeasurableSpace F]   (f : Ω → E)
 (g : Ω → F) {p : ENNReal},   p ≠ 0 →     p ≠ ⊤ →       MeasureTheory.MemLp f p 
μ →         (¬∀ᵐ (ω : Ω) ∂μ, f ω = 0) → ProbabilityTheory.IndepFun f g μ → Measu
reTheory.IsProbabilityMeasure μ
参数：f : Ω → E；g : Ω → F；¬∀ᵐ (ω : Ω) ∂μ, f ω = 0。
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `exists_seq_strictAnti_tendsto`：exists_seq_strictAnti_tendsto [DenselyOrd
ered α] [NoMaxOrder α] [FirstCountableTopology α] (x : α) : exists u : Nat -> α,
 StrictAnti u ∧ (fo…
· 使用定理 `NNReal.instOrderTopology`：OrderTopology NNReal
· 使用定理 `NNReal.instDenselyOrdered`：DenselyOrdered NNReal
· 使用定理 `IsStrictOrderedRing.toNoMaxOrder`：∀ {R : Type u} [inst : Semiring R] [in
st_1 : PartialOrder R] [IsStrictOrderedRing R], NoMaxOrder R
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.ae_all_iff`：ae_all_iff {ι : Sort*} [Countable ι] {p : α ->
 ι -> Prop} : (forallᵐ a ∂μ, forall i, p a i) ↔ forall i, forallᵐ a ∂μ, p a i
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `ge_of_tendsto'`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace α] 
[inst_1 : Preorder α] [ClosedIciTopology α] {f : β → α}   {a b : α} {x : Filter 
β} […
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
（共 45 条，此处仅展示前 30 条）

--- 原说明 ---
If a nonzero function belongs to `ℒ^p` and is independent of another function, t
hen
the space is a probability space.
-/
lemma MemLp.isProbabilityMeasure_of_indepFun
    (f : Ω → E) (g : Ω → F) {p : ℝ≥0∞} (hp : p ≠ 0) (hp' : p ≠ ∞)
    (hℒp : MemLp f p μ) (h'f : ¬ (∀ᵐ ω ∂μ, f ω = 0)) (hindep : f ⟂ᵢ[μ] g) :
    IsProbabilityMeasure μ := by
  obtain ⟨c, c_pos, hc⟩ : ∃ (c : ℝ≥0), 0 < c ∧ 0 < μ {ω | c ≤ ‖f ω‖₊} := by
    contrapose! h'f
    have A (c : ℝ≥0) (hc : 0 < c) : ∀ᵐ ω ∂μ, ‖f ω‖₊ < c := by simpa [ae_iff] using h'f c hc
    obtain ⟨u, -, u_pos, u_lim⟩ : ∃ u, StrictAnti u ∧ (∀ (n : ℕ), 0 < u n)
      ∧ Tendsto u atTop (𝓝 0) := exists_seq_strictAnti_tendsto (0 : ℝ≥0)
    filter_upwards [ae_all_iff.2 (fun n ↦ A (u n) (u_pos n))] with ω hω
    simpa using ge_of_tendsto' u_lim (fun i ↦ (hω i).le)
  have h'c : μ {ω | c ≤ ‖f ω‖₊} < ∞ := hℒp.meas_ge_lt_top hp hp' c_pos.ne'
  have := hindep.measure_inter_preimage_eq_mul {x | c ≤ ‖x‖₊} Set.univ
    (isClosed_le continuous_const continuous_nnnorm).measurableSet MeasurableSet.univ
  simp only [Set.preimage_ofPred_eq, Set.preimage_univ, Set.inter_univ] at this
  exact ⟨(ENNReal.mul_eq_left hc.ne' h'c.ne).1 this.symm⟩


/-- If a nonzero function is integrable and is independent of another function, then
the space is a probability space. -/
/-
**MeasureTheory.Integrable.isProbabilityMeasure_of_indepFun** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory.Integrable`。
形式化陈述：∀ {Ω : Type u_1} {E : Type u_2} {F : Type u_3} [inst : MeasurableSpace Ω] 
{μ : MeasureTheory.Measure Ω}   [inst_1 : NormedAddCommGroup E] [inst_2 : Measur
ableSpace E] [OpensMeasurableSpace E] [inst_4 : MeasurableSpace F]   (f : Ω → E)
 (g : Ω → F),   MeasureTheory.Integrable f μ →     (¬∀ᵐ (ω : Ω) ∂μ, f ω = 0) → P
robabilityTheory.IndepFun f g μ → MeasureTheory.IsProbabilityMeasure μ
参数：f : Ω → E；g : Ω → F；¬∀ᵐ (ω : Ω) ∂μ, f ω = 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.MemLp.isProbabilityMeasure_of_indepFun`：∀ {Ω : Type u_1} {
E : Type u_2} {F : Type u_3} [inst : MeasurableSpace Ω] {μ : MeasureTheory.Measu
re Ω}   [inst_1 : NormedAddCommGroup E] [i…
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `ENNReal.one_ne_top`：1 ≠ ⊤
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.memLp_one_iff_integrable`：memLp_one_iff_integrable {f : α 
-> ε} : MemLp f 1 μ ↔ Integrable f μ

--- 原说明 ---
If a nonzero function is integrable and is independent of another function, then
the space is a probability space.
-/
lemma Integrable.isProbabilityMeasure_of_indepFun (f : Ω → E) (g : Ω → F)
    (hf : Integrable f μ) (h'f : ¬ (∀ᵐ ω ∂μ, f ω = 0)) (hindep : f ⟂ᵢ[μ] g) :
    IsProbabilityMeasure μ :=
  MemLp.isProbabilityMeasure_of_indepFun f g one_ne_zero ENNReal.one_ne_top
    (memLp_one_iff_integrable.mpr hf) h'f hindep

end MeasureTheory

