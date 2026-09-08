/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Measured sets

Consider a measure `μ` on a measurable space. One can define an extended distance on the space
of measurable sets, by `edist s t := μ (s ∆ t)`. In this file, we introduce this definition
on the type synonym `MeasuredSets μ`, and we prove that `μ` is a continuous function on this space.

We also give a density criterion for this distance,
in `exists_measure_symmDiff_lt_of_generateFrom_isSetRing`: given a ring of sets `C` covering the
space modulo `0` and generating the measurable space structure, then any measurable set can be
approximated by elements of `C`.
Note that the covering condition is necessary: for a counterexample otherwise, take `{0, 1}` with
the counting measure and `C = {∅, {0}}`. Then the set `{1}` can not be approximated by
an element of `C`.
-/

@[expose] public section

open MeasurableSpace Set Filter
open scoped symmDiff ENNReal Topology

namespace MeasureTheory

variable {α : Type*} [mα : MeasurableSpace α] {μ : Measure α}

set_option linter.unusedVariables false in
/-- The subtype of all measurable sets. We denote it as `MeasuredSets μ`, with an explicit but
unused parameter `μ`, to be able to define a distance on it given by `edist s t = μ (s ∆ t)` -/
@[nolint unusedArguments]
/-
**MeasureTheory.MeasuredSets** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：MeasuredSets (μ : Measure α) : Type _
参数：μ : Measure α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The subtype of all measurable sets. We denote it as `MeasuredSets μ`, with an ex
plicit but
unused parameter `μ`, to be able to define a distance on it given by `edist s t 
= μ (s ∆ t)`
-/
def MeasuredSets (μ : Measure α) : Type _ := {s : Set α // MeasurableSet s}
/-
**MeasureTheory.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SetLike (MeasuredSets μ) α where
  coe s := s.1
  coe_injective := Subtype.coe_injective
/-
**MeasureTheory.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : PseudoEMetricSpace (MeasuredSets μ) where
  edist s t := μ ((s : Set α) ∆ t)
  edist_self := by simp
  edist_comm := by grind
  edist_triangle s t u := measure_symmDiff_le _ _ _
/-
**MeasureTheory.MeasuredSets.edist_def** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
MeasuredSets`。
形式化陈述：∀ {α : Type u_1} [mα : MeasurableSpace α] {μ : MeasureTheory.Measure α} (s
 t : MeasureTheory.MeasuredSets μ),   edist s t = μ (symmDiff ↑s ↑t)
参数：s t : MeasureTheory.MeasuredSets μ；symmDiff ↑s ↑t。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma MeasuredSets.edist_def (s t : MeasuredSets μ) : edist s t = μ ((s : Set α) ∆ t) := rfl

/-- Measure on `MeasuredSets` is a 1-lipschitz function.

We cannot state this in terms of `LipschitzWith`, because `ℝ≥0∞` is not a `PseudoEMetricSpace`. -/
/-
**MeasureTheory.MeasuredSets.sub_le_edist** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.MeasuredSets`。
形式化陈述：∀ {α : Type u_1} [mα : MeasurableSpace α] {μ : MeasureTheory.Measure α} (s
 t : MeasureTheory.MeasuredSets μ),   μ ↑s - μ ↑t ≤ edist s t
参数：s t : MeasureTheory.MeasuredSets μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.le_measure_sdiff`：le_measure_sdiff : μ s₁ - μ s₂ <= μ (s₁ 
\ s₂)
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t

--- 原说明 ---
Measure on `MeasuredSets` is a 1-lipschitz function.

We cannot state this in terms of `LipschitzWith`, because `ℝ≥0∞` is not a `Pseud
oEMetricSpace`.
-/
lemma MeasuredSets.sub_le_edist (s t : MeasuredSets μ) : μ s - μ t ≤ edist s t :=
  le_measure_sdiff.trans <| measure_mono subset_union_left
/-
**MeasureTheory.MeasuredSets.continuous_measure** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.MeasuredSets`。
形式化陈述：∀ {α : Type u_1} [mα : MeasurableSpace α] {μ : MeasureTheory.Measure α}, C
ontinuous fun s => μ ↑s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_of_le_add_edist`：continuous_of_le_add_edist {f : α -> Real>=0
∞} (C : Real>=0∞) (hC : C != ∞) (h : forall x y, f x <= f y + C * edist x y) : C
ontinuous f
· 使用定理 `ENNReal.one_ne_top`：1 ≠ ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tsub_le_iff_left`：tsub_le_iff_left : a - b <= c ↔ a <= b + c
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `MeasureTheory.MeasuredSets.sub_le_edist`：∀ {α : Type u_1} [mα : Measurab
leSpace α] {μ : MeasureTheory.Measure α} (s t : MeasureTheory.MeasuredSets μ),  
 μ ↑s - μ ↑t ≤ edist s t
-/
lemma MeasuredSets.continuous_measure : Continuous (fun (s : MeasuredSets μ) ↦ μ s) := by
  refine continuous_of_le_add_edist 1 ENNReal.one_ne_top fun s t ↦ ?_
  rw [one_mul, ← tsub_le_iff_left]
  exact sub_le_edist s t
/-
**MeasureTheory.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [IsFiniteMeasure μ] : PseudoMetricSpace (MeasuredSets μ) :=
  PseudoEMetricSpace.toPseudoMetricSpaceOfDist
    (fun s t ↦ μ.real ((s : Set α) ∆ t)) (fun s t ↦ ENNReal.toReal_nonneg)
    (fun s t ↦ by simp [Measure.real, MeasuredSets.edist_def])
/-
**MeasureTheory.MeasuredSets.dist_def** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.M
easuredSets`。
形式化陈述：∀ {α : Type u_1} [mα : MeasurableSpace α] {μ : MeasureTheory.Measure α} [i
nst : MeasureTheory.IsFiniteMeasure μ]   (s t : MeasureTheory.MeasuredSets μ), d
ist s t = μ.real (symmDiff ↑s ↑t)
参数：s t : MeasureTheory.MeasuredSets μ；symmDiff ↑s ↑t。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma MeasuredSets.dist_def [IsFiniteMeasure μ] (s t : MeasuredSets μ) :
    dist s t = μ.real ((s : Set α) ∆ t) := rfl
/-
**MeasureTheory.MeasuredSets.real_sub_real_le_dist** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.MeasuredSets`。
形式化陈述：∀ {α : Type u_1} [mα : MeasurableSpace α] {μ : MeasureTheory.Measure α} [i
nst : MeasureTheory.IsFiniteMeasure μ]   (s t : MeasureTheory.MeasuredSets μ), μ
.real ↑s - μ.real ↑t ≤ dist s t
参数：s t : MeasureTheory.MeasuredSets μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_edist`：dist_edist (x y : α) : dist x y = (edist x y).toReal
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `ENNReal.toReal_mono`：toReal_mono (hb : b != ∞) (h : a <= b) : a.toReal <
= b.toReal
· 使用定理 `edist_ne_top`：edist_ne_top (x y : α) : edist x y != ⊤
· 使用定理 `MeasureTheory.MeasuredSets.sub_le_edist`：∀ {α : Type u_1} [mα : Measurab
leSpace α] {μ : MeasureTheory.Measure α} (s t : MeasureTheory.MeasuredSets μ),  
 μ ↑s - μ ↑t ≤ edist s t
· 使用定理 `ENNReal.le_toReal_sub`：le_toReal_sub {a b : Real>=0∞} (hb : b != ∞) : a.
toReal - b.toReal <= (a - b).toReal
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
-/
lemma MeasuredSets.real_sub_real_le_dist [IsFiniteMeasure μ] (s t : MeasuredSets μ) :
    μ.real s - μ.real t ≤ dist s t := by
  grw [dist_edist, ← sub_le_edist]
  exacts [ENNReal.le_toReal_sub (measure_ne_top _ _), edist_ne_top _ _]
/-
**MeasureTheory.MeasuredSets.lipschitzWith_measureReal** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.MeasuredSets`。
形式化陈述：∀ {α : Type u_1} [mα : MeasurableSpace α] {μ : MeasureTheory.Measure α} [M
easureTheory.IsFiniteMeasure μ],   LipschitzWith 1 fun s => μ.real ↑s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.of_le_add`：∀ {α : Type u} [inst : PseudoMetricSpace α] {f 
: α → ℝ}, (∀ (x y : α), f x ≤ f y + dist x y) → LipschitzWith 1 f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sub_le_iff_le_add'`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : LE 
α] [AddLeftMono α] {a b c : α}, a - b ≤ c ↔ a ≤ b + c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `MeasureTheory.MeasuredSets.real_sub_real_le_dist`：∀ {α : Type u_1} [mα :
 MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst : MeasureTheory.IsFinite
Measure μ]   (s t : MeasureTheory.Meas…
-/
lemma MeasuredSets.lipschitzWith_measureReal [IsFiniteMeasure μ] :
    LipschitzWith 1 (fun s : MeasuredSets μ ↦ μ.real s) :=
  .of_le_add fun s t ↦ sub_le_iff_le_add'.mp <| real_sub_real_le_dist s t

/-- Given a ring of sets `C` covering the space modulo `0` and generating the measurable space
structure, any measurable set can be approximated by elements of `C`. -/
/-
**MeasureTheory.exists_measure_symmDiff_lt_of_generateFrom_isSetRing** 是 Mathlib
 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：exists_measure_symmDiff_lt_of_generateFrom_isSetRing [IsFiniteMeasure μ] {
C : Set (Set α)} (hC : IsSetRing C) (h'C : exists D : Set (Set α), D.Countable ∧
 D subseteq C ∧ μ (⋃₀ D)ᶜ = 0) (h : mα = generateFrom C) {s : Set α} (hs : Measu
rableSet s) {ε : Real>=0∞} (hε : 0 < ε) : exists t in C, μ (t ∆ s) < ε
参数：Set α；hC : IsSetRing C；h'C : exists D : Set (Set α), D.Countable ∧ D subseteq
 C ∧ μ (⋃₀ D)ᶜ = 0；h : mα = generateFrom C；hs : MeasurableSet s；hε : 0 < ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSpace.induction_on_inter`：induction_on_inter {m : MeasurableSp
ace α} {C : forall s : Set α, MeasurableSet s -> Prop} {s : Set (Set α)} (h_eq :
 m = generateFrom s) (h_…
· 使用引理 `MeasureTheory.IsSetSemiring.isPiSystem`：isPiSystem (hC : IsSetSemiring C
) : IsPiSystem C
· 使用引理 `MeasureTheory.IsSetRing.isSetSemiring`：isSetSemiring (hC : IsSetRing C) 
: IsSetSemiring C where empty_mem
· 使用定理 `MeasureTheory.IsSetRing.empty_mem`：∀ {α : Type u_1} {C : Set (Set α)}, M
easureTheory.IsSetRing C → ∅ ∈ C
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `symmDiff_self`：symmDiff_self : a ∆ a = ⊥
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ENNReal.half_pos`：∀ {a : ENNReal}, a ≠ 0 → 0 < a / 2
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Set.Countable.union`：∀ {α : Type u} {s t : Set α}, s.Countable → t.Count
able → (s ∪ t).Countable
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `Set.sUnion_insert`：sUnion_insert (s : Set α) (T : Set (Set α)) : ⋃₀ inse
rt s T = s union ⋃₀ T
· 使用定理 `Set.empty_union`：empty_union (a : Set α) : ∅ union a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.Countable.exists_eq_range`：∀ {α : Type u} {s : Set α}, s.Countable →
 s.Nonempty → ∃ f, s = Set.range f
· 使用定理 `MeasureTheory.IsSetRing.accumulate_mem`：accumulate_mem (hC : IsSetRing C
) {s : Nat -> Set α} (hs : forall i, s i in C) (n : Nat) : accumulate s n in C
· 使用定理 `Set.iUnion_accumulate`：iUnion_accumulate [Preorder α] : ⋃ x, accumulate 
s x = ⋃ x, s x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.compl_iUnion`：compl_iUnion (s : ι -> Set β) : (⋃ i, s i)ᶜ = ⋂ i, (s 
i)ᶜ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
（共 76 条，此处仅展示前 30 条）

--- 原说明 ---
Given a ring of sets `C` covering the space modulo `0` and generating the measur
able space
structure, any measurable set can be approximated by elements of `C`.
-/
lemma exists_measure_symmDiff_lt_of_generateFrom_isSetRing [IsFiniteMeasure μ]
    {C : Set (Set α)} (hC : IsSetRing C)
    (h'C : ∃ D : Set (Set α), D.Countable ∧ D ⊆ C ∧ μ (⋃₀ D)ᶜ = 0) (h : mα = generateFrom C)
    {s : Set α} (hs : MeasurableSet s) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ t ∈ C, μ (t ∆ s) < ε := by
  /- We check that the set of sets satisfying the conclusion of the lemma for all positive
  `ε` contains `C` and is stable under complement and disjoint union. It follows that it is
  all the sigma-algebra, as desired. -/
  apply MeasurableSpace.induction_on_inter (C := fun s hs ↦ ∀ (ε : ℝ≥0∞) (hε : 0 < ε),
    ∃ t ∈ C, μ (t ∆ s) < ε) h hC.isSetSemiring.isPiSystem ?_ ?_ ?_ ?_ s hs ε hε
  · intro ε εpos
    exact ⟨∅, hC.empty_mem, by simp [εpos]⟩
  · intro s hs ε εpos
    exact ⟨s, hs, by simp [εpos]⟩
  · /- To check the stability under complement, we use the condition `h'C` which guarantees
    that the space is almost an element of `C`. If `t` approximates `s`, then `univ \ t`
    approximates well `sᶜ`, and therefore `t' \ t` approximates well `sᶜ` when `t'` is a good
    enough approximation to `univ`. As `t' \ t` belongs to `C` when `t` and `t'` do, this
    concludes this step. -/
    intro s hs h's ε εpos
    obtain ⟨t, tC, ht⟩ : ∃ t ∈ C, μ (t ∆ s) < ε / 2 := h's _ (ENNReal.half_pos εpos.ne')
    obtain ⟨t', t'C, ht'⟩ : ∃ t' ∈ C, μ (t'ᶜ) < ε / 2 := by
      obtain ⟨D, D_count, DC, hD, Dne⟩ :
          ∃ D : Set (Set α), D.Countable ∧ D ⊆ C ∧ μ (⋃₀ D)ᶜ = 0 ∧ D.Nonempty := by
        rcases h'C with ⟨D, D_count, DC, hD⟩
        refine ⟨D ∪ {∅}, D_count.union (by simp), ?_⟩
        simp only [union_subset_iff, DC, singleton_subset_iff, true_and, and_true, hC.empty_mem]
        simp only [union_singleton, sUnion_insert, empty_union, insert_nonempty, and_true, hD]
      obtain ⟨f, hf⟩ : ∃ f : ℕ → Set α, D = Set.range f := Set.Countable.exists_eq_range D_count Dne
      have fC n : Set.accumulate f n ∈ C := hC.accumulate_mem (fun n ↦ DC (by simp [hf])) n
      have : Tendsto (fun n ↦ μ (Set.accumulate f n)ᶜ) atTop (𝓝 0) := by
        have : ⋃₀ D = ⋃ n, Set.accumulate f n := by simp [hf, iUnion_accumulate]
        rw [show (⋃₀ D)ᶜ = ⋂ n, (Set.accumulate f n)ᶜ by simp [this, accumulate]] at hD
        rw [← hD]
        apply tendsto_measure_iInter_atTop (fun i ↦ ?_)
          (fun i j hij ↦ by simpa using monotone_accumulate hij) ⟨0, by simp⟩
        apply MeasurableSet.nullMeasurableSet
        rw [h]
        exact (measurableSet_generateFrom (fC i)).compl
      obtain ⟨n, hn⟩ : ∃ n, μ (accumulate f n)ᶜ < ε / 2 :=
        ((tendsto_order.1 this).2 _ (ENNReal.half_pos εpos.ne')).exists
      exact ⟨accumulate f n, fC n, hn⟩
    refine ⟨t' \ t, hC.sdiff_mem t'C tC, ?_⟩
    calc μ ((t' \ t) ∆ sᶜ)
      _ ≤ μ (t ∆ s ∪ t'ᶜ) := by gcongr; grind
      _ ≤ μ (t ∆ s) + μ (t'ᶜ) := measure_union_le _ _
      _ < ε / 2 + ε / 2 := by gcongr
      _ = ε := ENNReal.add_halves ε
  · /- To check the stability under disjoint union, approximate `f n` by a set `t n ∈ C`. Then
    `⋃ i, f i` is well approximated by `U i < n, f i` for large enough `n`, which is itself
    well approximated by `⋃ i < n, t i`. As this set belongs to `C`, this concludes this step. -/
    intro f f_disj f_meas hf ε εpos
    rcases ENNReal.exists_pos_sum_of_countable' (ENNReal.half_pos εpos.ne').ne' ℕ with ⟨δ, δpos, hδ⟩
    have A i : ∃ t ∈ C, μ (t ∆ (f i)) < δ i := hf i _ (δpos i)
    choose! t tC ht using A
    have : Tendsto (fun n ↦ μ (⋃ i ∈ Ici n, f i)) atTop (𝓝 0) :=
      tendsto_measure_biUnion_Ici_zero_of_pairwise_disjoint
        (fun i ↦ (f_meas i).nullMeasurableSet) f_disj
    obtain ⟨n, hn⟩ : ∃ n, μ (⋃ i ∈ Ici n, f i) < ε / 2 :=
      ((tendsto_order.1 this).2 _ (ENNReal.half_pos εpos.ne')).exists
    refine ⟨⋃ i ∈ Finset.range n, t i, hC.biUnion_mem _ (fun i hi ↦ tC _), ?_⟩
    calc μ ((⋃ i ∈ Finset.range n, t i) ∆ (⋃ i, f i))
    _ ≤ μ ((⋃ i ∈ Finset.range n, (t i) ∆ (f i)) ∪ ⋃ i ∈ Ici n, f i) := by
      gcongr
      intro x hx
      simp only [Finset.mem_range, mem_symmDiff, mem_iUnion, exists_prop, not_exists, not_and,
        mem_Ici, mem_union] at hx ⊢
      grind
    _ ≤ ∑ i ∈ Finset.range n, μ (t i ∆ f i) + μ (⋃ i ∈ Ici n, f i) := by
      apply (measure_union_le _ _).trans
      gcongr
      apply measure_biUnion_finset_le
    _ ≤ ∑ i ∈ Finset.range n, δ i + μ (⋃ i ∈ Ici n, f i) := by
      gcongr with i; exact (ht i).le
    _ ≤ ∑' i, δ i + μ (⋃ i ∈ Ici n, f i) := by
      gcongr; exact ENNReal.sum_le_tsum (Finset.range n)
    _ < ε / 2 + ε / 2 := by gcongr
    _ = ε := ENNReal.add_halves ε

/-- Given a semiring of sets `C` covering the space modulo `0` and generating the measurable space
structure, any measurable set can be approximated by finite unions of elements of `C`. -/
/-
**MeasureTheory.exists_measure_symmDiff_lt_of_generateFrom_isSetSemiring** 是 Mat
hlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：exists_measure_symmDiff_lt_of_generateFrom_isSetSemiring [IsFiniteMeasure 
μ] {C : Set (Set α)} (hC : IsSetSemiring C) (h'C : exists D : Set (Set α), D.Cou
ntable ∧ D subseteq C ∧ μ (⋃₀ D)ᶜ = 0) (h : mα = generateFrom C) {s : Set α} (hs
 : MeasurableSet s) {ε : Real>=0∞} (hε : 0 < ε) : exists t in supClosure C, μ (t
 ∆ s) < ε
参数：Set α；hC : IsSetSemiring C；h'C : exists D : Set (Set α), D.Countable ∧ D subs
eteq C ∧ μ (⋃₀ D)ᶜ = 0；h : mα = generateFrom C；hs : MeasurableSet s；hε : 0 < ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.exists_measure_symmDiff_lt_of_generateFrom_isSetRing`：exis
ts_measure_symmDiff_lt_of_generateFrom_isSetRing [IsFiniteMeasure μ] {C : Set (S
et α)} (hC : IsSetRing C) (h'C : exists D : Set (Set α),…
· 使用定理 `MeasureTheory.IsSetSemiring.isSetRing_supClosure`：isSetRing_supClosure (
hC : IsSetSemiring C) : IsSetRing (supClosure C) where empty_mem
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `subset_supClosure`：subset_supClosure {s : Set α} : s subseteq supClosure
 s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `MeasurableSpace.generateFrom_mono`：generateFrom_mono {s t : Set (Set α)}
 (h : s subseteq t) : generateFrom s <= generateFrom t
· 使用定理 `MeasurableSpace.generateFrom_le`：generateFrom_le {s : Set (Set α)} {m : 
MeasurableSpace α} (h : forall t in s, MeasurableSet[m] t) : generateFrom s <= m
· 使用定理 `measurableSet_generateFrom_of_mem_supClosure`：measurableSet_generateFrom
_of_mem_supClosure {s : Set (Set α)} {t : Set α} (ht : t in supClosure s) : Meas
urableSet[generateFrom s] t

--- 原说明 ---
Given a semiring of sets `C` covering the space modulo `0` and generating the me
asurable space
structure, any measurable set can be approximated by finite unions of elements o
f `C`.
-/
lemma exists_measure_symmDiff_lt_of_generateFrom_isSetSemiring [IsFiniteMeasure μ]
    {C : Set (Set α)} (hC : IsSetSemiring C)
    (h'C : ∃ D : Set (Set α), D.Countable ∧ D ⊆ C ∧ μ (⋃₀ D)ᶜ = 0) (h : mα = generateFrom C)
    {s : Set α} (hs : MeasurableSet s) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ t ∈ supClosure C, μ (t ∆ s) < ε := by
  apply exists_measure_symmDiff_lt_of_generateFrom_isSetRing hC.isSetRing_supClosure ?_ ?_ hs hε
  · rcases h'C with ⟨D, D_count, DC, hD⟩
    exact ⟨D, D_count, DC.trans subset_supClosure, hD⟩
  · rw [h]
    apply le_antisymm (generateFrom_mono subset_supClosure)
    apply generateFrom_le (fun t ht ↦ ?_)
    apply measurableSet_generateFrom_of_mem_supClosure ht

/-- A ring of sets covering the space modulo `0` and generating the measurable space
/-
**MeasureTheory.is** 是 Mathlib 中的一个结构，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
structure is dense among measurable sets. -/
/-
**MeasureTheory.dense_of_generateFrom_isSetRing** 是 Mathlib 中的一个引理，位于命名空间 `Measu
reTheory`。
形式化陈述：dense_of_generateFrom_isSetRing [IsFiniteMeasure μ] {C : Set (Set α)} (hC 
: IsSetRing C) (h'C : exists D : Set (Set α), D.Countable ∧ D subseteq C ∧ μ (⋃₀
 D)ᶜ = 0) (h : mα = generateFrom C) : Dense ((SetLike.coe : MeasuredSets μ -> Se
t α) ⁻¹' C)
参数：Set α；hC : IsSetRing C；h'C : exists D : Set (Set α), D.Countable ∧ D subseteq
 C ∧ μ (⋃₀ D)ᶜ = 0；h : mα = generateFrom C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `EMetric.dense_iff`：dense_iff : Dense s ↔ forall (x : α), forall r > 0, (
eball x r inter s).Nonempty
· 使用引理 `MeasureTheory.exists_measure_symmDiff_lt_of_generateFrom_isSetRing`：exis
ts_measure_symmDiff_lt_of_generateFrom_isSetRing [IsFiniteMeasure μ] {C : Set (S
et α)} (hC : IsSetRing C) (h'C : exists D : Set (Set α),…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `MeasurableSpace.measurableSet_generateFrom`：measurableSet_generateFrom {
s : Set (Set α)} {t : Set α} (ht : t in s) : MeasurableSet[generateFrom s] t

--- 原说明 ---
A ring of sets covering the space modulo `0` and generating the measurable space
structure is dense among measurable sets.
-/
lemma dense_of_generateFrom_isSetRing [IsFiniteMeasure μ]
    {C : Set (Set α)} (hC : IsSetRing C)
    (h'C : ∃ D : Set (Set α), D.Countable ∧ D ⊆ C ∧ μ (⋃₀ D)ᶜ = 0) (h : mα = generateFrom C) :
    Dense ((SetLike.coe : MeasuredSets μ → Set α) ⁻¹' C) := by
  rw [EMetric.dense_iff]
  rintro s ε εpos
  rcases exists_measure_symmDiff_lt_of_generateFrom_isSetRing hC h'C h s.2 εpos with ⟨t, tC, ht⟩
  have t_meas : MeasurableSet t := by rw [h]; exact measurableSet_generateFrom tC
  refine ⟨⟨t, t_meas⟩, ?_, tC⟩
  simpa [MeasuredSets.edist_def] using! ht

/-- Given a semiring of sets `C` covering the space modulo `0` and generating the measurable space
structure, finite unions of elements of `C` are dense among measurable sets. -/
/-
**MeasureTheory.dense_of_generateFrom_isSetSemiring** 是 Mathlib 中的一个引理，位于命名空间 `M
easureTheory`。
形式化陈述：dense_of_generateFrom_isSetSemiring [IsFiniteMeasure μ] {C : Set (Set α)} 
(hC : IsSetSemiring C) (h'C : exists D : Set (Set α), D.Countable ∧ D subseteq C
 ∧ μ (⋃₀ D)ᶜ = 0) (h : mα = generateFrom C) : Dense ((SetLike.coe : MeasuredSets
 μ -> Set α) ⁻¹' (supClosure C))
参数：Set α；hC : IsSetSemiring C；h'C : exists D : Set (Set α), D.Countable ∧ D subs
eteq C ∧ μ (⋃₀ D)ᶜ = 0；h : mα = generateFrom C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `EMetric.dense_iff`：dense_iff : Dense s ↔ forall (x : α), forall r > 0, (
eball x r inter s).Nonempty
· 使用引理 `MeasureTheory.exists_measure_symmDiff_lt_of_generateFrom_isSetSemiring`：
exists_measure_symmDiff_lt_of_generateFrom_isSetSemiring [IsFiniteMeasure μ] {C 
: Set (Set α)} (hC : IsSetSemiring C) (h'C : exists D : Set …
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `measurableSet_generateFrom_of_mem_supClosure`：measurableSet_generateFrom
_of_mem_supClosure {s : Set (Set α)} {t : Set α} (ht : t in supClosure s) : Meas
urableSet[generateFrom s] t

--- 原说明 ---
Given a semiring of sets `C` covering the space modulo `0` and generating the me
asurable space
structure, finite unions of elements of `C` are dense among measurable sets.
-/
lemma dense_of_generateFrom_isSetSemiring [IsFiniteMeasure μ]
    {C : Set (Set α)} (hC : IsSetSemiring C)
    (h'C : ∃ D : Set (Set α), D.Countable ∧ D ⊆ C ∧ μ (⋃₀ D)ᶜ = 0) (h : mα = generateFrom C) :
    Dense ((SetLike.coe : MeasuredSets μ → Set α) ⁻¹' (supClosure C)) := by
  rw [EMetric.dense_iff]
  rintro s ε εpos
  rcases exists_measure_symmDiff_lt_of_generateFrom_isSetSemiring hC h'C h s.2 εpos
    with ⟨t, tC, ht⟩
  refine ⟨⟨t, ?_⟩, by simpa [MeasuredSets.edist_def] using! ht, tC⟩
  rw [h]
  exact measurableSet_generateFrom_of_mem_supClosure tC

end MeasureTheory

