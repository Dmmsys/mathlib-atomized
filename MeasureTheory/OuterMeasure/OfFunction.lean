/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.MeasureTheory.OuterMeasure.Operations
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Outer measures from functions

Given an arbitrary function `m : Set α → ℝ≥0∞` that sends `∅` to `0` we can define an outer
measure on `α` that on `s` is defined to be the infimum of `∑ᵢ, m (sᵢ)` for all collections of sets
`sᵢ` that cover `s`. This is the unique maximal outer measure that is at most the given function.

Given an outer measure `m`, the Carathéodory-measurable sets are the sets `s` such that
for all sets `t` we have `m t = m (t ∩ s) + m (t \ s)`. This forms a measurable space.

## Main definitions and statements

* `OuterMeasure.boundedBy` is the greatest outer measure that is at most the given function.
  If you know that the given function sends `∅` to `0`, then `OuterMeasure.ofFunction` is a
  special case.
* `sInf_eq_boundedBy_sInfGen` is a characterization of the infimum of outer measures.

## References

* <https://en.wikipedia.org/wiki/Outer_measure>
* <https://en.wikipedia.org/wiki/Carath%C3%A9odory%27s_criterion>

## Tags

outer measure, Carathéodory-measurable, Carathéodory's criterion

-/

@[expose] public section

assert_not_exists Module.Basis

noncomputable section

open Set Function Filter
open scoped NNReal Topology ENNReal

namespace MeasureTheory
namespace OuterMeasure

section OfFunction

variable {α : Type*}

/-- Given any function `m` assigning measures to sets satisfying `m ∅ = 0`, there is
  a unique maximal outer measure `μ` satisfying `μ s ≤ m s` for all `s : Set α`. -/
/-
**MeasureTheory.OuterMeasure.ofFunction** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory
.OuterMeasure`。
形式化陈述：{α : Type u_1} → (m : Set α → ENNReal) → m ∅ = 0 → MeasureTheory.OuterMeas
ure α
参数：m : Set α → ENNReal。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given any function `m` assigning measures to sets satisfying `m ∅ = 0`, there is
  a unique maximal outer measure `μ` satisfying `μ s ≤ m s` for all `s : Set α`.
-/
protected def ofFunction (m : Set α → ℝ≥0∞) (m_empty : m ∅ = 0) : OuterMeasure α :=
  let μ s := ⨅ (f : ℕ → Set α) (_ : s ⊆ ⋃ i, f i), ∑' i, m (f i)
  { measureOf := μ
    empty := by
      rw [← nonpos_iff_eq_zero]
      exact (iInf_le_of_le fun _ => ∅) <| iInf_le_of_le (empty_subset _) <| by simpa
    mono := fun {_ _} hs => iInf_mono fun _ => iInf_mono' fun hb => ⟨hs.trans hb, le_rfl⟩
    iUnion_nat := fun s _ =>
      ENNReal.le_of_forall_pos_le_add <| by
        intro ε hε (hb : (∑' i, μ (s i)) < ∞)
        rcases ENNReal.exists_pos_sum_of_countable (ENNReal.coe_pos.2 hε).ne' ℕ with ⟨ε', hε', hl⟩
        grw [← hl]
        rw [← ENNReal.tsum_add]
        choose f hf using
          show ∀ i, ∃ f : ℕ → Set α, (s i ⊆ ⋃ i, f i) ∧ (∑' i, m (f i)) < μ (s i) + ε' i by
            intro i
            have : μ (s i) < μ (s i) + ε' i :=
              ENNReal.lt_add_right (ne_top_of_le_ne_top hb.ne <| ENNReal.le_tsum _)
                (by simpa using (hε' i).ne')
            rcases iInf_lt_iff.mp this with ⟨t, ht⟩
            exists t
            contrapose! ht
            exact le_iInf ht
        refine le_trans ?_ (ENNReal.tsum_le_tsum fun i => le_of_lt (hf i).2)
        rw [← ENNReal.tsum_prod, ← Nat.pairEquiv.symm.tsum_eq]
        refine iInf_le_of_le _ (iInf_le _ ?_)
        apply iUnion_subset
        intro i
        apply Subset.trans (hf i).1
        apply iUnion_subset
        simp only [Nat.pairEquiv_symm_apply]
        rw [iUnion_unpair]
        intro j
        apply subset_iUnion₂ i }

variable (m : Set α → ℝ≥0∞) (m_empty : m ∅ = 0)

/-- `ofFunction` of a set `s` is the infimum of `∑ᵢ, m (tᵢ)` for all collections of sets
`tᵢ` that cover `s`. -/
/-
**MeasureTheory.OuterMeasure.ofFunction_apply** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.OuterMeasure`。
形式化陈述：ofFunction_apply (s : Set α) : OuterMeasure.ofFunction m m_empty s = ⨅ (t 
: Nat -> Set α) (_ : s subseteq iUnion t), ∑' n, m (t n)
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ofFunction` of a set `s` is the infimum of `∑ᵢ, m (tᵢ)` for all collections of 
sets
`tᵢ` that cover `s`.
-/
theorem ofFunction_apply (s : Set α) :
    OuterMeasure.ofFunction m m_empty s = ⨅ (t : ℕ → Set α) (_ : s ⊆ iUnion t), ∑' n, m (t n) :=
  rfl

/-- `ofFunction` of a set `s` is the infimum of `∑ᵢ, m (tᵢ)` for all collections of sets
`tᵢ` that cover `s`, with all `tᵢ` satisfying a predicate `P` such that `m` is infinite for sets
that don't satisfy `P`.
This is similar to `ofFunction_apply`, except that the sets `tᵢ` satisfy `P`.
The hypothesis `m_top` applies in particular to a function of the form `extend m'`. -/
/-
**MeasureTheory.OuterMeasure.ofFunction_eq_iInf_mem** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.OuterMeasure`。
形式化陈述：ofFunction_eq_iInf_mem {P : Set α -> Prop} (m_top : forall s, ¬ P s -> m s
 = ∞) (s : Set α) : OuterMeasure.ofFunction m m_empty s = ⨅ (t : Nat -> Set α) (
_ : forall i, P (t i)) (_ : s subseteq ⋃ i, t i), ∑' i, m (t i)
参数：m_top : forall s, ¬ P s -> m s = ∞；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.OuterMeasure.ofFunction_apply`：ofFunction_apply (s : Set α
) : OuterMeasure.ofFunction m m_empty s = ⨅ (t : Nat -> Set α) (_ : s subseteq i
Union t), ∑' n, m (t n)
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f :
 ι → α} {a : α}, (∀ (i : ι), a ≤ f i) → a ≤ iInf f
· 使用定理 `iInf₂_le`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst : Com
pleteLattice α] {f : (i : ι) → κ i → α} (i : ι) (j : κ i),   ⨅ i, ⨅ j, f i j ≤…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iInf_le_of_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α
] {f : ι → α} {a : α} (i : ι), f i ≤ a → iInf f ≤ a
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `iInf_neg`：∀ {α : Type u_1} [inst : CompleteLattice α] {p : Prop} {f : p 
→ α}, ¬p → ⨅ (h : p), f h = ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `ENNReal.tsum_eq_top_of_eq_top`：∀ {α : Type u_1} {f : α → ENNReal}, (∃ a,
 f a = ⊤) → ∑' (a : α), f a = ⊤

--- 原说明 ---
`ofFunction` of a set `s` is the infimum of `∑ᵢ, m (tᵢ)` for all collections of 
sets
`tᵢ` that cover `s`, with all `tᵢ` satisfying a predicate `P` such that `m` is i
nfinite for sets
that don't satisfy `P`.
This is similar to `ofFunction_apply`, except that the sets `tᵢ` satisfy `P`.
The hypothesis `m_top` applies in particular to a function of the form `extend m
'`.
-/
theorem ofFunction_eq_iInf_mem {P : Set α → Prop} (m_top : ∀ s, ¬ P s → m s = ∞) (s : Set α) :
    OuterMeasure.ofFunction m m_empty s =
      ⨅ (t : ℕ → Set α) (_ : ∀ i, P (t i)) (_ : s ⊆ ⋃ i, t i), ∑' i, m (t i) := by
  rw [OuterMeasure.ofFunction_apply]
  apply le_antisymm
  · exact le_iInf fun t ↦ le_iInf fun _ ↦ le_iInf fun h ↦ iInf₂_le _ (by exact h)
  · simp_rw [le_iInf_iff]
    refine fun t ht_subset ↦ iInf_le_of_le t ?_
    by_cases ht : ∀ i, P (t i)
    · exact iInf_le_of_le ht (iInf_le_of_le ht_subset le_rfl)
    · simp only [ht, not_false_eq_true, iInf_neg, top_le_iff]
      push Not at ht
      obtain ⟨i, hti_notMem⟩ := ht
      have hfi_top : m (t i) = ∞ := m_top _ hti_notMem
      exact ENNReal.tsum_eq_top_of_eq_top ⟨i, hfi_top⟩

variable {m m_empty}
/-
**MeasureTheory.OuterMeasure.ofFunction_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.OuterMeasure`。
形式化陈述：ofFunction_le (s : Set α) : OuterMeasure.ofFunction m m_empty s <= m s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_le_of_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α
] {f : ι → α} {a : α} (i : ι), f i ≤ a → iInf f ≤ a
· 使用定理 `Set.subset_iUnion`：subset_iUnion : forall (s : ι -> Set β) (i : ι), s i 
subseteq ⋃ i, s i
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `tsum_eq_single`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   [L.LeAtTop] {f : β → α}
 (b …
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem ofFunction_le (s : Set α) : OuterMeasure.ofFunction m m_empty s ≤ m s :=
  let f : ℕ → Set α := fun i => Nat.casesOn i s fun _ => ∅
  iInf_le_of_le f <|
    iInf_le_of_le (subset_iUnion f 0) <|
      le_of_eq <| tsum_eq_single 0 <| by
        rintro (_ | i)
        · simp
        · simp [f, m_empty]
/-
**MeasureTheory.OuterMeasure.ofFunction_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.OuterMeasure`。
形式化陈述：ofFunction_eq (s : Set α) (m_mono : forall ⦃t : Set α⦄, s subseteq t -> m 
s <= m t) (m_subadd : forall s : Nat -> Set α, m (⋃ i, s i) <= ∑' i, m (s i)) : 
OuterMeasure.ofFunction m m_empty s = m s
参数：s : Set α；m_mono : forall ⦃t : Set α⦄, s subseteq t -> m s <= m t；m_subadd : 
forall s : Nat -> Set α, m (⋃ i, s i) <= ∑' i, m (s i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `MeasureTheory.OuterMeasure.ofFunction_le`：ofFunction_le (s : Set α) : Ou
terMeasure.ofFunction m m_empty s <= m s
· 使用定理 `le_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f :
 ι → α} {a : α}, (∀ (i : ι), a ≤ f i) → a ≤ iInf f
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
-/
theorem ofFunction_eq (s : Set α) (m_mono : ∀ ⦃t : Set α⦄, s ⊆ t → m s ≤ m t)
    (m_subadd : ∀ s : ℕ → Set α, m (⋃ i, s i) ≤ ∑' i, m (s i)) :
    OuterMeasure.ofFunction m m_empty s = m s :=
  le_antisymm (ofFunction_le s) <|
    le_iInf fun f => le_iInf fun hf => le_trans (m_mono hf) (m_subadd f)
/-
**MeasureTheory.OuterMeasure.le_ofFunction** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.OuterMeasure`。
形式化陈述：le_ofFunction {μ : OuterMeasure α} : μ <= OuterMeasure.ofFunction m m_empt
y ↔ forall s, μ s <= m s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `MeasureTheory.OuterMeasure.ofFunction_le`：ofFunction_le (s : Set α) : Ou
terMeasure.ofFunction m m_empty s <= m s
· 使用定理 `le_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f :
 ι → α} {a : α}, (∀ (i : ι), a ≤ f i) → a ≤ iInf f
· 使用定理 `MeasureTheory.OuterMeasure.mono`：∀ {α : Type u_2} (self : MeasureTheory.
OuterMeasure α) {s₁ s₂ : Set α}, s₁ ⊆ s₂ → self.measureOf s₁ ≤ self.measureOf s₂
· 使用定理 `MeasureTheory.measure_iUnion_le`：measure_iUnion_le [Countable ι] (s : ι 
-> Set α) : μ (⋃ i, s i) <= ∑' i, μ (s i)
· 使用定理 `MeasureTheory.OuterMeasure.instOuterMeasureClass`：∀ {α : Type u_1}, Meas
ureTheory.OuterMeasureClass (MeasureTheory.OuterMeasure α) α
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `ENNReal.tsum_le_tsum`：∀ {α : Type u_1} {f g : α → ENNReal}, (∀ (a : α), 
f a ≤ g a) → ∑' (a : α), f a ≤ ∑' (a : α), g a
-/
theorem le_ofFunction {μ : OuterMeasure α} :
    μ ≤ OuterMeasure.ofFunction m m_empty ↔ ∀ s, μ s ≤ m s :=
  ⟨fun H s => le_trans (H s) (ofFunction_le s), fun H _ =>
    le_iInf fun f =>
      le_iInf fun hs =>
        le_trans (μ.mono hs) <| le_trans (measure_iUnion_le f) <| ENNReal.tsum_le_tsum fun _ => H _⟩
/-
**MeasureTheory.OuterMeasure.isGreatest_ofFunction** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.OuterMeasure`。
形式化陈述：isGreatest_ofFunction : IsGreatest { μ : OuterMeasure α | forall s, μ s <=
 m s } (OuterMeasure.ofFunction m m_empty)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.OuterMeasure.ofFunction_le`：ofFunction_le (s : Set α) : Ou
terMeasure.ofFunction m m_empty s <= m s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.OuterMeasure.le_ofFunction`：le_ofFunction {μ : OuterMeasur
e α} : μ <= OuterMeasure.ofFunction m m_empty ↔ forall s, μ s <= m s
-/
theorem isGreatest_ofFunction :
    IsGreatest { μ : OuterMeasure α | ∀ s, μ s ≤ m s } (OuterMeasure.ofFunction m m_empty) :=
  ⟨fun _ => ofFunction_le _, fun _ => le_ofFunction.2⟩
/-
**MeasureTheory.OuterMeasure.ofFunction_eq_sSup** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.OuterMeasure`。
形式化陈述：ofFunction_eq_sSup : OuterMeasure.ofFunction m m_empty = sSup { μ | forall
 s, μ s <= m s }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLUB.sSup_eq`：∀ {α : Type u_1} [inst : CompleteSemilatticeSup α] {s : S
et α} {a : α}, IsLUB s a → sSup s = a
· 使用定理 `IsGreatest.isLUB`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α} {a : 
α}, IsGreatest s a → IsLUB s a
· 使用定理 `MeasureTheory.OuterMeasure.isGreatest_ofFunction`：isGreatest_ofFunction 
: IsGreatest { μ : OuterMeasure α | forall s, μ s <= m s } (OuterMeasure.ofFunct
ion m m_empty)
-/
theorem ofFunction_eq_sSup : OuterMeasure.ofFunction m m_empty = sSup { μ | ∀ s, μ s ≤ m s } :=
  (@isGreatest_ofFunction α m m_empty).isLUB.sSup_eq.symm

/-- If `m u = ∞` for any set `u` that has nonempty intersection both with `s` and `t`, then
`μ (s ∪ t) = μ s + μ t`, where `μ = MeasureTheory.OuterMeasure.ofFunction m m_empty`.

E.g., if `α` is an (e)metric space and `m u = ∞` on any set of diameter `≥ r`, then this lemma
implies that `μ (s ∪ t) = μ s + μ t` on any two sets such that `r ≤ edist x y` for all `x ∈ s`
and `y ∈ t`. -/
/-
**MeasureTheory.OuterMeasure.ofFunction_union_of_top_of_nonempty_inter** 是 Mathl
ib 中的一个定理，位于命名空间 `MeasureTheory.OuterMeasure`。
形式化陈述：ofFunction_union_of_top_of_nonempty_inter {s t : Set α} (h : forall u, (s 
inter u).Nonempty -> (t inter u).Nonempty -> m u = ∞) : OuterMeasure.ofFunction 
m m_empty (s union t) = OuterMeasure.ofFunction m m_empty s + OuterMeasure.ofFun
ction m m_empty t
参数：h : forall u, (s inter u).Nonempty -> (t inter u).Nonempty -> m u = ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `MeasureTheory.measure_union_le`：measure_union_le (s t : Set α) : μ (s un
ion t) <= μ s + μ t
· 使用定理 `MeasureTheory.OuterMeasure.instOuterMeasureClass`：∀ {α : Type u_1}, Meas
ureTheory.OuterMeasureClass (MeasureTheory.OuterMeasure α) α
· 使用定理 `le_iInf₂`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst : Com
pleteLattice α] {a : α} {f : (i : ι) → κ i → α},   (∀ (i : ι) (j : κ i), a ≤ f…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.le_tsum`：∀ {α : Type u_1} {f : α → ENNReal} (a : α), f a ≤ ∑' (a
 : α), f a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `disjoint_iff_inf_le`：disjoint_iff_inf_le : Disjoint a b ↔ a ⊓ b <= ⊥
· 使用定理 `MeasureTheory.OuterMeasure.mono`：∀ {α : Type u_2} (self : MeasureTheory.
OuterMeasure α) {s₁ s₂ : Set α}, s₁ ⊆ s₂ → self.measureOf s₁ ≤ self.measureOf s₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `MeasureTheory.measure_iUnion_le`：measure_iUnion_le [Countable ι] (s : ι 
-> Set α) : μ (⋃ i, s i) <= ∑' i, μ (s i)
· 使用定理 `SetCoe.countable`：∀ {α : Type u} [Countable α] (s : Set α), Countable ↑s
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `Summable.tsum_union_disjoint`：∀ {α : Type u_1} {β : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : TopologicalSpace α] {f : β → α} [T2Space α]   [Continuo
usAdd α] {s t : Se…
· 使用定理 `ENNReal.instT2Space`：T2Space ENNReal
· 使用定理 `ENNReal.instContinuousAdd`：ContinuousAdd ENNReal
· 使用定理 `ENNReal.summable`：∀ {α : Type u_1} {f : α → ENNReal}, Summable f
· 使用定理 `Summable.tsum_le_tsum_of_inj`：∀ {ι : Type u_1} {κ : Type u_2} {α : Type 
u_3} [inst : AddCommMonoid α] [inst_1 : Preorder α] [IsOrderedAddMonoid α]   [in
st_3 : Topological…
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
（共 37 条，此处仅展示前 30 条）

--- 原说明 ---
If `m u = ∞` for any set `u` that has nonempty intersection both with `s` and `t
`, then
`μ (s ∪ t) = μ s + μ t`, where `μ = MeasureTheory.OuterMeasure.ofFunction m m_em
pty`.

E.g., if `α` is an (e)metric space and `m u = ∞` on any set of diameter `≥ r`, t
hen this lemma
implies that `μ (s ∪ t) = μ s + μ t` on any two sets such that `r ≤ edist x y` f
or all `x ∈ s`
and `y ∈ t`.
-/
theorem ofFunction_union_of_top_of_nonempty_inter {s t : Set α}
    (h : ∀ u, (s ∩ u).Nonempty → (t ∩ u).Nonempty → m u = ∞) :
    OuterMeasure.ofFunction m m_empty (s ∪ t) =
      OuterMeasure.ofFunction m m_empty s + OuterMeasure.ofFunction m m_empty t := by
  refine le_antisymm (measure_union_le _ _) (le_iInf₂ fun f hf ↦ ?_)
  set μ := OuterMeasure.ofFunction m m_empty
  rcases Classical.em (∃ i, (s ∩ f i).Nonempty ∧ (t ∩ f i).Nonempty) with (⟨i, hs, ht⟩ | he)
  · calc
      μ s + μ t ≤ ∞ := le_top
      _ = m (f i) := (h (f i) hs ht).symm
      _ ≤ ∑' i, m (f i) := ENNReal.le_tsum i
  set I := fun s => { i : ℕ | (s ∩ f i).Nonempty }
  have hd : Disjoint (I s) (I t) := disjoint_iff_inf_le.mpr fun i hi => he ⟨i, hi⟩
  have hI : ∀ u ⊆ s ∪ t, μ u ≤ ∑' i : I u, μ (f i) := fun u hu =>
    calc
      μ u ≤ μ (⋃ i : I u, f i) :=
        μ.mono fun x hx =>
          let ⟨i, hi⟩ := mem_iUnion.1 (hf (hu hx))
          mem_iUnion.2 ⟨⟨i, ⟨x, hx, hi⟩⟩, hi⟩
      _ ≤ ∑' i : I u, μ (f i) := measure_iUnion_le _
  calc
    μ s + μ t ≤ (∑' i : I s, μ (f i)) + ∑' i : I t, μ (f i) :=
      add_le_add (hI _ subset_union_left) (hI _ subset_union_right)
    _ = ∑' i : ↑(I s ∪ I t), μ (f i) :=
      (ENNReal.summable.tsum_union_disjoint (f := fun i => μ (f i)) hd ENNReal.summable).symm
    _ ≤ ∑' i, μ (f i) :=
      (ENNReal.summable.tsum_le_tsum_of_inj (↑) Subtype.coe_injective (fun _ _ => zero_le)
        (fun _ => le_rfl) ENNReal.summable)
    _ ≤ ∑' i, m (f i) := ENNReal.tsum_le_tsum fun i => ofFunction_le _
/-
**MeasureTheory.OuterMeasure.comap_ofFunction** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.OuterMeasure`。
形式化陈述：comap_ofFunction {β} (f : β -> α) (h : Monotone m ∨ Surjective f) : comap 
f (OuterMeasure.ofFunction m m_empty) = OuterMeasure.ofFunction (fun s => m (f '
' s)) (by simp; simp [m_empty])
参数：f : β -> α；h : Monotone m ∨ Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.OuterMeasure.le_ofFunction`：le_ofFunction {μ : OuterMeasur
e α} : μ <= OuterMeasure.ofFunction m m_empty ↔ forall s, μ s <= m s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.OuterMeasure.comap_apply`：comap_apply {β} (f : α -> β) (m 
: OuterMeasure β) (s : Set α) : comap f m s = m (f '' s)
· 使用定理 `MeasureTheory.OuterMeasure.ofFunction_le`：ofFunction_le (s : Set α) : Ou
terMeasure.ofFunction m m_empty s <= m s
· 使用定理 `MeasureTheory.OuterMeasure.ofFunction_apply`：ofFunction_apply (s : Set α
) : OuterMeasure.ofFunction m m_empty s = ⨅ (t : Nat -> Set α) (_ : s subseteq i
Union t), ∑' n, m (t n)
· 使用定理 `iInf_mono'`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort u_5} [inst : Comp
leteLattice α] {f : ι → α} {g : ι' → α},   (∀ (i : ι), ∃ i', g i' ≤ f i) → iInf 
…
· 使用定理 `Set.preimage_iUnion`：preimage_iUnion {f : α -> β} {s : ι -> Set β} : (f 
⁻¹' ⋃ i, s i) = ⋃ i, f ⁻¹' s i
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `ENNReal.tsum_le_tsum`：∀ {α : Type u_1} {f g : α → ENNReal}, (∀ (a : α), 
f a ≤ g a) → ∑' (a : α), f a ≤ ∑' (a : α), g a
· 使用定理 `Set.image_preimage_subset`：image_preimage_subset (f : α -> β) (s : Set β
) : f '' f ⁻¹' s subseteq s
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Function.Surjective.image_preimage`：∀ {α : Type u_1} {β : Type u_2} {f :
 α → β}, Function.Surjective f → ∀ (s : Set β), f '' f ⁻¹' s = s
-/
theorem comap_ofFunction {β} (f : β → α) (h : Monotone m ∨ Surjective f) :
    comap f (OuterMeasure.ofFunction m m_empty) =
      OuterMeasure.ofFunction (fun s => m (f '' s)) (by simp; simp [m_empty]) := by
  refine le_antisymm (le_ofFunction.2 fun s => ?_) fun s => ?_
  · rw [comap_apply]
    apply ofFunction_le
  · rw [comap_apply, ofFunction_apply, ofFunction_apply]
    refine iInf_mono' fun t => ⟨fun k => f ⁻¹' t k, ?_⟩
    refine iInf_mono' fun ht => ?_
    rw [Set.image_subset_iff, preimage_iUnion] at ht
    refine ⟨ht, ENNReal.tsum_le_tsum fun n => ?_⟩
    rcases h with hl | hr
    exacts [hl (image_preimage_subset _ _), (congr_arg m (hr.image_preimage (t n))).le]
/-
**MeasureTheory.OuterMeasure.map_ofFunction_le** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.OuterMeasure`。
形式化陈述：map_ofFunction_le {β} (f : α -> β) : map f (OuterMeasure.ofFunction m m_em
pty) <= OuterMeasure.ofFunction (fun s => m (f ⁻¹' s)) m_empty
参数：f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.OuterMeasure.le_ofFunction`：le_ofFunction {μ : OuterMeasur
e α} : μ <= OuterMeasure.ofFunction m m_empty ↔ forall s, μ s <= m s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.OuterMeasure.map_apply`：map_apply {β} (f : α -> β) (m : Ou
terMeasure α) (s : Set β) : map f m s = m (f ⁻¹' s)
· 使用定理 `MeasureTheory.OuterMeasure.ofFunction_le`：ofFunction_le (s : Set α) : Ou
terMeasure.ofFunction m m_empty s <= m s
-/
theorem map_ofFunction_le {β} (f : α → β) :
    map f (OuterMeasure.ofFunction m m_empty) ≤
      OuterMeasure.ofFunction (fun s => m (f ⁻¹' s)) m_empty :=
  le_ofFunction.2 fun s => by
    rw [map_apply]
    apply ofFunction_le
/-
**MeasureTheory.OuterMeasure.map_ofFunction** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.OuterMeasure`。
形式化陈述：map_ofFunction {β} {f : α -> β} (hf : Injective f) : map f (OuterMeasure.o
fFunction m m_empty) = OuterMeasure.ofFunction (fun s => m (f ⁻¹' s)) m_empty
参数：hf : Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.OuterMeasure.map_ofFunction_le`：map_ofFunction_le {β} (f :
 α -> β) : map f (OuterMeasure.ofFunction m m_empty) <= OuterMeasure.ofFunction 
(fun s => m (f ⁻¹' s)) m_empty
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iInf_le_of_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α
] {f : ι → α} {a : α} (i : ι), f i ≤ a → iInf f ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.union_iUnion`：union_iUnion [Nonempty ι] (s : Set β) (t : ι -> Set β)
 : (s union ⋃ i, t i) = ⋃ i, s union t i
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Set.inter_subset`：inter_subset (a b c : Set α) : a inter b subseteq c ↔ 
a subseteq bᶜ union c
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用定理 `Set.image_iUnion`：image_iUnion {f : α -> β} {s : ι -> Set α} : (f '' ⋃ i
, s i) = ⋃ i, f '' s i
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `ENNReal.tsum_le_tsum`：∀ {α : Type u_1} {f g : α → ENNReal}, (∀ (a : α), 
f a ≤ g a) → ∑' (a : α), f a ≤ ∑' (a : α), g a
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.preimage_range`：preimage_range (f : α -> β) : f ⁻¹' range f = univ
· 使用定理 `Set.compl_univ`：compl_univ : (univ : Set α)ᶜ = ∅
· 使用定理 `Function.Injective.preimage_image`：∀ {α : Type u_1} {β : Type u_2} {f : 
α → β}, Function.Injective f → ∀ (s : Set α), f ⁻¹' f '' s = s
· 使用定理 `Set.empty_union`：empty_union (a : Set α) : ∅ union a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_ofFunction {β} {f : α → β} (hf : Injective f) :
    map f (OuterMeasure.ofFunction m m_empty) =
      OuterMeasure.ofFunction (fun s => m (f ⁻¹' s)) m_empty := by
  refine (map_ofFunction_le _).antisymm fun s => ?_
  simp only [ofFunction_apply, map_apply, le_iInf_iff]
  intro t ht
  refine iInf_le_of_le (fun n => (range f)ᶜ ∪ f '' t n) (iInf_le_of_le ?_ ?_)
  · rw [← union_iUnion, ← inter_subset, ← image_preimage_eq_inter_range, ← image_iUnion]
    exact image_mono ht
  · refine ENNReal.tsum_le_tsum fun n => le_of_eq ?_
    simp [hf.preimage_image]

-- TODO (kmill): change `m (t ∩ s)` to `m (s ∩ t)`
/-
**MeasureTheory.OuterMeasure.restrict_ofFunction** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.OuterMeasure`。
形式化陈述：restrict_ofFunction (s : Set α) (hm : Monotone m) : restrict s (OuterMeasu
re.ofFunction m m_empty) = OuterMeasure.ofFunction (fun t => m (t inter s)) (by 
simp; simp [m_empty])
参数：s : Set α；hm : Monotone m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.OuterMeasure.restrict.eq_1`：∀ {α : Type u_1} (s : Set α), 
  MeasureTheory.OuterMeasure.restrict s =     MeasureTheory.OuterMeasure.map Sub
type.val ∘ₗ MeasureTheory.Oute…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `MeasureTheory.OuterMeasure.ofFunction.congr_simp`：∀ {α : Type u_1} (m m_
1 : Set α → ENNReal) (e_m : m = m_1) (m_empty : m ∅ = 0),   MeasureTheory.OuterM
easure.ofFunction m m_empty = MeasureT…
· 使用定理 `MeasureTheory.OuterMeasure.comap_ofFunction`：comap_ofFunction {β} (f : β
 -> α) (h : Monotone m ∨ Surjective f) : comap f (OuterMeasure.ofFunction m m_em
pty) = OuterMeasure.ofFunction (f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subtype.image_preimage_coe`：image_preimage_coe (s t : Set α) : ((↑) : s 
-> α) '' ((↑) : s -> α) ⁻¹' t = s inter t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.OuterMeasure.map_ofFunction`：map_ofFunction {β} {f : α -> 
β} (hf : Injective f) : map f (OuterMeasure.ofFunction m m_empty) = OuterMeasure
.ofFunction (fun s => m (f ⁻¹' …
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem restrict_ofFunction (s : Set α) (hm : Monotone m) :
    restrict s (OuterMeasure.ofFunction m m_empty) =
      OuterMeasure.ofFunction (fun t => m (t ∩ s)) (by simp; simp [m_empty]) := by
      rw [restrict]
      simp only [inter_comm _ s, LinearMap.comp_apply]
      rw [comap_ofFunction _ (Or.inl hm)]
      simp only [map_ofFunction Subtype.coe_injective, Subtype.image_preimage_coe]
/-
**MeasureTheory.OuterMeasure.smul_ofFunction** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.OuterMeasure`。
形式化陈述：smul_ofFunction {c : Real>=0∞} (hc : c != ∞) : c • OuterMeasure.ofFunction
 m m_empty = OuterMeasure.ofFunction (c • m) (by simp [m_empty])
参数：hc : c != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.OuterMeasure.ext`：ext {μ₁ μ₂ : OuterMeasure α} (h : forall
 s, μ₁ s = μ₂ s) : μ₁ = μ₂
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Set.subset_iUnion`：subset_iUnion : forall (s : ι -> Set β) (i : ι), s i 
subseteq ⋃ i, s i
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `MeasureTheory.OuterMeasure.instIsSMulApplySetENNReal`：∀ {α : Type u_1} {
R : Type u_3} [inst : SMul R ENNReal] [inst_1 : IsScalarTower R ENNReal ENNReal]
,   IsSMulApply R (MeasureTheory.OuterMeas…
· 使用定理 `iInf_subtype'`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α
] {p : ι → Prop} {f : (i : ι) → p i → α},   ⨅ i, ⨅ (h : p i), f i h = ⨅ x, f ↑x 
⋯
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `ENNReal.tsum_mul_left`：∀ {α : Type u_1} {a : ENNReal} {f : α → ENNReal},
 ∑' (i : α), a * f i = a * ∑' (i : α), f i
· 使用引理 `ENNReal.mul_iInf`：mul_iInf [Nonempty ι] (hinfty : a = ∞ -> ⨅ i, f i = 0 
-> exists i, f i = 0) : a * ⨅ i, f i = ⨅ i, a * f i
-/
theorem smul_ofFunction {c : ℝ≥0∞} (hc : c ≠ ∞) : c • OuterMeasure.ofFunction m m_empty =
    OuterMeasure.ofFunction (c • m) (by simp [m_empty]) := by
  ext1 s
  have : Nonempty { t : ℕ → Set α // s ⊆ ⋃ i, t i } := ⟨⟨fun _ => s, subset_iUnion (fun _ => s) 0⟩⟩
  simp only [smul_apply, ofFunction_apply, ENNReal.tsum_mul_left, Pi.smul_apply, smul_eq_mul,
  iInf_subtype']
  rw [ENNReal.mul_iInf fun h => (hc h).elim]

end OfFunction

section BoundedBy

variable {α : Type*} (m : Set α → ℝ≥0∞)

/-- Given any function `m` assigning measures to sets, there is a unique maximal outer measure `μ`
  satisfying `μ s ≤ m s` for all `s : Set α`. This is the same as `OuterMeasure.ofFunction`,
  except that it doesn't require `m ∅ = 0`. -/
/-
**MeasureTheory.OuterMeasure.boundedBy** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.
OuterMeasure`。
形式化陈述：boundedBy : OuterMeasure α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given any function `m` assigning measures to sets, there is a unique maximal out
er measure `μ`
  satisfying `μ s ≤ m s` for all `s : Set α`. This is the same as `OuterMeasure.
ofFunction`,
  except that it doesn't require `m ∅ = 0`.
-/
def boundedBy : OuterMeasure α :=
  OuterMeasure.ofFunction (fun s => ⨆ _ : s.Nonempty, m s) (by simp [Set.not_nonempty_empty])

variable {m}
/-
**MeasureTheory.OuterMeasure.boundedBy_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.OuterMeasure`。
形式化陈述：boundedBy_le (s : Set α) : boundedBy m s <= m s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.OuterMeasure.ofFunction_le`：ofFunction_le (s : Set α) : Ou
terMeasure.ofFunction m m_empty s <= m s
· 使用定理 `iSup_const_le`：iSup_const_le : ⨆ _ : ι, a <= a
-/
theorem boundedBy_le (s : Set α) : boundedBy m s ≤ m s :=
  (ofFunction_le _).trans iSup_const_le
/-
**MeasureTheory.OuterMeasure.boundedBy_eq_ofFunction** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.OuterMeasure`。
形式化陈述：boundedBy_eq_ofFunction (m_empty : m ∅ = 0) (s : Set α) : boundedBy m s = 
OuterMeasure.ofFunction m m_empty s
参数：m_empty : m ∅ = 0；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iSup_neg`：iSup_neg {p : Prop} {f : p -> α} (hp : ¬p) : ⨆ h : p, f h = ⊥
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `iSup_pos`：iSup_pos {p : Prop} {f : p -> α} (hp : p) : ⨆ h : p, f h = f h
p
· 使用定理 `MeasureTheory.OuterMeasure.ofFunction.congr_simp`：∀ {α : Type u_1} (m m_
1 : Set α → ENNReal) (e_m : m = m_1) (m_empty : m ∅ = 0),   MeasureTheory.OuterM
easure.ofFunction m m_empty = MeasureT…
-/
theorem boundedBy_eq_ofFunction (m_empty : m ∅ = 0) (s : Set α) :
    boundedBy m s = OuterMeasure.ofFunction m m_empty s := by
  have : (fun s : Set α => ⨆ _ : s.Nonempty, m s) = m := by
    ext1 t
    rcases t.eq_empty_or_nonempty with h | h <;> simp [h, Set.not_nonempty_empty, m_empty]
  simp [boundedBy, this]
/-
**MeasureTheory.OuterMeasure.boundedBy_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.OuterMeasure`。
形式化陈述：boundedBy_apply (s : Set α) : boundedBy m s = ⨅ (t : Nat -> Set α) (_ : s 
subseteq iUnion t), ∑' n, ⨆ _ : (t n).Nonempty, m (t n)
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem boundedBy_apply (s : Set α) :
    boundedBy m s = ⨅ (t : ℕ → Set α) (_ : s ⊆ iUnion t),
                      ∑' n, ⨆ _ : (t n).Nonempty, m (t n) := by
  simp [boundedBy, ofFunction_apply]
/-
**MeasureTheory.OuterMeasure.boundedBy_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.OuterMeasure`。
形式化陈述：boundedBy_eq (s : Set α) (m_empty : m ∅ = 0) (m_mono : forall ⦃t : Set α⦄,
 s subseteq t -> m s <= m t) (m_subadd : forall s : Nat -> Set α, m (⋃ i, s i) <
= ∑' i, m (s i)) : boundedBy m s = m s
参数：s : Set α；m_empty : m ∅ = 0；m_mono : forall ⦃t : Set α⦄, s subseteq t -> m s 
<= m t；m_subadd : forall s : Nat -> Set α, m (⋃ i, s i) <= ∑' i, m (s i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.OuterMeasure.boundedBy_eq_ofFunction`：boundedBy_eq_ofFunct
ion (m_empty : m ∅ = 0) (s : Set α) : boundedBy m s = OuterMeasure.ofFunction m 
m_empty s
· 使用定理 `MeasureTheory.OuterMeasure.ofFunction_eq`：ofFunction_eq (s : Set α) (m_m
ono : forall ⦃t : Set α⦄, s subseteq t -> m s <= m t) (m_subadd : forall s : Nat
 -> Set α, m (⋃ i, s i) <= ∑' …
-/
theorem boundedBy_eq (s : Set α) (m_empty : m ∅ = 0) (m_mono : ∀ ⦃t : Set α⦄, s ⊆ t → m s ≤ m t)
    (m_subadd : ∀ s : ℕ → Set α, m (⋃ i, s i) ≤ ∑' i, m (s i)) : boundedBy m s = m s := by
  rw [boundedBy_eq_ofFunction m_empty, ofFunction_eq s m_mono m_subadd]

@[simp]
/-
**MeasureTheory.OuterMeasure.boundedBy_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.OuterMeasure`。
形式化陈述：boundedBy_eq_self (m : OuterMeasure α) : boundedBy m = m
参数：m : OuterMeasure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.OuterMeasure.ext`：ext {μ₁ μ₂ : OuterMeasure α} (h : forall
 s, μ₁ s = μ₂ s) : μ₁ = μ₂
· 使用定理 `MeasureTheory.OuterMeasure.boundedBy_eq`：boundedBy_eq (s : Set α) (m_emp
ty : m ∅ = 0) (m_mono : forall ⦃t : Set α⦄, s subseteq t -> m s <= m t) (m_subad
d : forall s : Nat -> Set α, …
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.OuterMeasure.instOuterMeasureClass`：∀ {α : Type u_1}, Meas
ureTheory.OuterMeasureClass (MeasureTheory.OuterMeasure α) α
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.measure_iUnion_le`：measure_iUnion_le [Countable ι] (s : ι 
-> Set α) : μ (⋃ i, s i) <= ∑' i, μ (s i)
· 使用定理 `instCountableNat`：Countable ℕ
-/
theorem boundedBy_eq_self (m : OuterMeasure α) : boundedBy m = m :=
  ext fun _ => boundedBy_eq _ measure_empty (fun _ ht => measure_mono ht) measure_iUnion_le
/-
**MeasureTheory.OuterMeasure.le_boundedBy** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.OuterMeasure`。
形式化陈述：le_boundedBy {μ : OuterMeasure α} : μ <= boundedBy m ↔ forall s, μ s <= m 
s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.OuterMeasure.boundedBy.eq_1`：∀ {α : Type u_1} (m : Set α →
 ENNReal),   MeasureTheory.OuterMeasure.boundedBy m = MeasureTheory.OuterMeasure
.ofFunction (fun s => ⨆ (_ : s.…
· 使用定理 `MeasureTheory.OuterMeasure.le_ofFunction`：le_ofFunction {μ : OuterMeasur
e α} : μ <= OuterMeasure.ofFunction m m_empty ↔ forall s, μ s <= m s
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.OuterMeasure.instOuterMeasureClass`：∀ {α : Type u_1}, Meas
ureTheory.OuterMeasureClass (MeasureTheory.OuterMeasure α) α
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iSup_neg`：iSup_neg {p : Prop} {f : p -> α} (hp : ¬p) : ⨆ h : p, f h = ⊥
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `iSup_pos`：iSup_pos {p : Prop} {f : p -> α} (hp : p) : ⨆ h : p, f h = f h
p
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_boundedBy {μ : OuterMeasure α} : μ ≤ boundedBy m ↔ ∀ s, μ s ≤ m s := by
  rw [boundedBy, le_ofFunction, forall_congr']; intro s
  rcases s.eq_empty_or_nonempty with h | h <;> simp [h, Set.not_nonempty_empty]
/-
**MeasureTheory.OuterMeasure.le_boundedBy'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.OuterMeasure`。
形式化陈述：le_boundedBy' {μ : OuterMeasure α} : μ <= boundedBy m ↔ forall s : Set α, 
s.Nonempty -> μ s <= m s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.OuterMeasure.le_boundedBy`：le_boundedBy {μ : OuterMeasure 
α} : μ <= boundedBy m ↔ forall s, μ s <= m s
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.OuterMeasure.instOuterMeasureClass`：∀ {α : Type u_1}, Meas
ureTheory.OuterMeasureClass (MeasureTheory.OuterMeasure α) α
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_boundedBy' {μ : OuterMeasure α} :
    μ ≤ boundedBy m ↔ ∀ s : Set α, s.Nonempty → μ s ≤ m s := by
  rw [le_boundedBy, forall_congr']
  intro s
  rcases s.eq_empty_or_nonempty with h | h <;> simp [h]

@[simp]
/-
**MeasureTheory.OuterMeasure.boundedBy_top** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.OuterMeasure`。
形式化陈述：boundedBy_top : boundedBy (⊤ : Set α -> Real>=0∞) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `MeasureTheory.OuterMeasure.le_boundedBy'`：le_boundedBy' {μ : OuterMeasur
e α} : μ <= boundedBy m ↔ forall s : Set α, s.Nonempty -> μ s <= m s
· 使用定理 `MeasureTheory.OuterMeasure.top_apply`：top_apply {s : Set α} (h : s.Nonem
pty) : (⊤ : OuterMeasure α) s = ∞
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem boundedBy_top : boundedBy (⊤ : Set α → ℝ≥0∞) = ⊤ := by
  rw [eq_top_iff, le_boundedBy']
  intro s hs
  rw [top_apply hs]
  exact le_rfl

@[simp]
/-
**MeasureTheory.OuterMeasure.boundedBy_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.OuterMeasure`。
形式化陈述：boundedBy_zero : boundedBy (0 : Set α -> Real>=0∞) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.OuterMeasure.coe_bot`：coe_bot : (⊥ : OuterMeasure α) = 0
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `MeasureTheory.OuterMeasure.boundedBy_le`：boundedBy_le (s : Set α) : boun
dedBy m s <= m s
-/
theorem boundedBy_zero : boundedBy (0 : Set α → ℝ≥0∞) = 0 := by
  rw [← coe_bot, eq_bot_iff]
  apply boundedBy_le
/-
**MeasureTheory.OuterMeasure.smul_boundedBy** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.OuterMeasure`。
形式化陈述：smul_boundedBy {c : Real>=0∞} (hc : c != ∞) : c • boundedBy m = boundedBy 
(c • m)
参数：hc : c != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.OuterMeasure.smul_ofFunction`：smul_ofFunction {c : Real>=0
∞} (hc : c != ∞) : c • OuterMeasure.ofFunction m m_empty = OuterMeasure.ofFuncti
on (c • m) (by simp [m_empty])
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iSup_neg`：iSup_neg {p : Prop} {f : p -> α} (hp : ¬p) : ⨆ h : p, f h = ⊥
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `iSup_pos`：iSup_pos {p : Prop} {f : p -> α} (hp : p) : ⨆ h : p, f h = f h
p
-/
theorem smul_boundedBy {c : ℝ≥0∞} (hc : c ≠ ∞) : c • boundedBy m = boundedBy (c • m) := by
  simp only [boundedBy, smul_ofFunction hc]
  congr 1 with s : 1
  rcases s.eq_empty_or_nonempty with (rfl | hs) <;> simp [*]
/-
**MeasureTheory.OuterMeasure.comap_boundedBy** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.OuterMeasure`。
形式化陈述：comap_boundedBy {β} (f : β -> α) (h : (Monotone fun s : { s : Set α // s.N
onempty } => m s) ∨ Surjective f) : comap f (boundedBy m) = boundedBy fun s => m
 (f '' s)
参数：f : β -> α；h : (Monotone fun s : { s : Set α // s.Nonempty } => m s) ∨ Surjec
tive f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.OuterMeasure.comap_ofFunction`：comap_ofFunction {β} (f : β
 -> α) (h : Monotone m ∨ Surjective f) : comap f (OuterMeasure.ofFunction m m_em
pty) = OuterMeasure.ofFunction (f…
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `Set.Nonempty.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Nonempty → t.
Nonempty
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_nonempty`：image_nonempty {f : α -> β} {s : Set α} : (f '' s).N
onempty ↔ s.Nonempty
-/
theorem comap_boundedBy {β} (f : β → α)
    (h : (Monotone fun s : { s : Set α // s.Nonempty } => m s) ∨ Surjective f) :
    comap f (boundedBy m) = boundedBy fun s => m (f '' s) := by
  refine (comap_ofFunction _ ?_).trans ?_
  · refine h.imp (fun H s t hst => iSup_le fun hs => ?_) id
    have ht : t.Nonempty := hs.mono hst
    exact (@H ⟨s, hs⟩ ⟨t, ht⟩ hst).trans (le_iSup (fun _ : t.Nonempty => m t) ht)
  · dsimp only [boundedBy]
    congr with s : 1
    rw [image_nonempty]

/-- If `m u = ∞` for any set `u` that has nonempty intersection both with `s` and `t`, then
`μ (s ∪ t) = μ s + μ t`, where `μ = MeasureTheory.OuterMeasure.boundedBy m`.

E.g., if `α` is an (e)metric space and `m u = ∞` on any set of diameter `≥ r`, then this lemma
implies that `μ (s ∪ t) = μ s + μ t` on any two sets such that `r ≤ edist x y` for all `x ∈ s`
and `y ∈ t`. -/
/-
**MeasureTheory.OuterMeasure.boundedBy_union_of_top_of_nonempty_inter** 是 Mathli
b 中的一个定理，位于命名空间 `MeasureTheory.OuterMeasure`。
形式化陈述：boundedBy_union_of_top_of_nonempty_inter {s t : Set α} (h : forall u, (s i
nter u).Nonempty -> (t inter u).Nonempty -> m u = ∞) : boundedBy m (s union t) =
 boundedBy m s + boundedBy m t
参数：h : forall u, (s inter u).Nonempty -> (t inter u).Nonempty -> m u = ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.OuterMeasure.ofFunction_union_of_top_of_nonempty_inter`：of
Function_union_of_top_of_nonempty_inter {s t : Set α} (h : forall u, (s inter u)
.Nonempty -> (t inter u).Nonempty -> m u = ∞) : OuterMeasu…
· 使用定理 `top_unique`：top_unique (h : ⊤ <= a) : a = ⊤
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `Set.Nonempty.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Nonempty → t.
Nonempty
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t

--- 原说明 ---
If `m u = ∞` for any set `u` that has nonempty intersection both with `s` and `t
`, then
`μ (s ∪ t) = μ s + μ t`, where `μ = MeasureTheory.OuterMeasure.boundedBy m`.

E.g., if `α` is an (e)metric space and `m u = ∞` on any set of diameter `≥ r`, t
hen this lemma
implies that `μ (s ∪ t) = μ s + μ t` on any two sets such that `r ≤ edist x y` f
or all `x ∈ s`
and `y ∈ t`.
-/
theorem boundedBy_union_of_top_of_nonempty_inter {s t : Set α}
    (h : ∀ u, (s ∩ u).Nonempty → (t ∩ u).Nonempty → m u = ∞) :
    boundedBy m (s ∪ t) = boundedBy m s + boundedBy m t :=
  ofFunction_union_of_top_of_nonempty_inter fun u hs ht =>
    top_unique <| (h u hs ht).ge.trans <| le_iSup (fun _ => m u) (hs.mono inter_subset_right)

end BoundedBy

section sInfGen

variable {α : Type*}

/-- Given a set of outer measures, we define a new function that on a set `s` is defined to be the
  infimum of `μ(s)` for the outer measures `μ` in the collection. We ensure that this
  function is defined to be `0` on `∅`, even if the collection of outer measures is empty.
  The outer measure generated by this function is the infimum of the given outer measures. -/
/-
**MeasureTheory.OuterMeasure.sInfGen** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Ou
terMeasure`。
形式化陈述：sInfGen (m : Set (OuterMeasure α)) (s : Set α) : Real>=0∞
参数：m : Set (OuterMeasure α)；s : Set α。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a set of outer measures, we define a new function that on a set `s` is def
ined to be the
  infimum of `μ(s)` for the outer measures `μ` in the collection. We ensure that
 this
  function is defined to be `0` on `∅`, even if the collection of outer measures
 is empty.
  The outer measure generated by this function is the infimum of the given outer
 measures.
-/
def sInfGen (m : Set (OuterMeasure α)) (s : Set α) : ℝ≥0∞ :=
  ⨅ (μ : OuterMeasure α) (_ : μ ∈ m), μ s
/-
**MeasureTheory.OuterMeasure.sInfGen_def** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.OuterMeasure`。
形式化陈述：sInfGen_def (m : Set (OuterMeasure α)) (t : Set α) : sInfGen m t = ⨅ (μ : 
OuterMeasure α) (_ : μ in m), μ t
参数：m : Set (OuterMeasure α)；t : Set α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sInfGen_def (m : Set (OuterMeasure α)) (t : Set α) :
    sInfGen m t = ⨅ (μ : OuterMeasure α) (_ : μ ∈ m), μ t :=
  rfl
/-
**MeasureTheory.OuterMeasure.sInf_eq_boundedBy_sInfGen** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.OuterMeasure`。
形式化陈述：sInf_eq_boundedBy_sInfGen (m : Set (OuterMeasure α)) : sInf m = OuterMeasu
re.boundedBy (sInfGen m)
参数：m : Set (OuterMeasure α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.OuterMeasure.le_boundedBy`：le_boundedBy {μ : OuterMeasure 
α} : μ <= boundedBy m ↔ forall s, μ s <= m s
· 使用定理 `le_iInf₂`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst : Com
pleteLattice α] {a : α} {f : (i : ι) → κ i → α},   (∀ (i : ι) (j : κ i), a ≤ f…
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a
· 使用定理 `le_sInf`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, (∀ b ∈ s, a ≤ b) → a ≤ sInf s
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `MeasureTheory.OuterMeasure.boundedBy_le`：boundedBy_le (s : Set α) : boun
dedBy m s <= m s
· 使用定理 `iInf₂_le`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst : Com
pleteLattice α] {f : (i : ι) → κ i → α} (i : ι) (j : κ i),   ⨅ i, ⨅ j, f i j ≤…
-/
theorem sInf_eq_boundedBy_sInfGen (m : Set (OuterMeasure α)) :
    sInf m = OuterMeasure.boundedBy (sInfGen m) := by
  refine le_antisymm ?_ ?_
  · refine le_boundedBy.2 fun s => le_iInf₂ fun μ hμ => ?_
    apply sInf_le hμ
  · refine le_sInf ?_
    intro μ hμ t
    exact le_trans (boundedBy_le t) (iInf₂_le μ hμ)
/-
**MeasureTheory.OuterMeasure.iSup_sInfGen_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.OuterMeasure`。
形式化陈述：iSup_sInfGen_nonempty {m : Set (OuterMeasure α)} (h : m.Nonempty) (t : Set
 α) : ⨆ _ : t.Nonempty, sInfGen m t = ⨅ (μ : OuterMeasure α) (_ : μ in m), μ t
参数：OuterMeasure α；h : m.Nonempty；t : Set α。
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
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iSup_neg`：iSup_neg {p : Prop} {f : p -> α} (hp : ¬p) : ⨆ h : p, f h = ⊥
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.OuterMeasure.instOuterMeasureClass`：∀ {α : Type u_1}, Meas
ureTheory.OuterMeasureClass (MeasureTheory.OuterMeasure α) α
· 使用定理 `biInf_const`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLattice α] 
{a : α} {s : Set β}, s.Nonempty → ⨅ i ∈ s, a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iSup_pos`：iSup_pos {p : Prop} {f : p -> α} (hp : p) : ⨆ h : p, f h = f h
p
-/
theorem iSup_sInfGen_nonempty {m : Set (OuterMeasure α)} (h : m.Nonempty) (t : Set α) :
    ⨆ _ : t.Nonempty, sInfGen m t = ⨅ (μ : OuterMeasure α) (_ : μ ∈ m), μ t := by
  rcases t.eq_empty_or_nonempty with (rfl | ht)
  · simp [biInf_const h]
  · simp [ht, sInfGen_def]

/-- The value of the Infimum of a nonempty set of outer measures on a set is not simply
the minimum value of a measure on that set: it is the infimum sum of measures of countable set of
sets that covers that set, where a different measure can be used for each set in the cover. -/
/-
**MeasureTheory.OuterMeasure.sInf_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.OuterMeasure`。
形式化陈述：sInf_apply {m : Set (OuterMeasure α)} {s : Set α} (h : m.Nonempty) : sInf 
m s = ⨅ (t : Nat -> Set α) (_ : s subseteq iUnion t), ∑' n, ⨅ (μ : OuterMeasure 
α) (_ : μ in m), μ (t n)
参数：OuterMeasure α；h : m.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.OuterMeasure.sInf_eq_boundedBy_sInfGen`：sInf_eq_boundedBy_
sInfGen (m : Set (OuterMeasure α)) : sInf m = OuterMeasure.boundedBy (sInfGen m)
· 使用定理 `MeasureTheory.OuterMeasure.boundedBy_apply`：boundedBy_apply (s : Set α) 
: boundedBy m s = ⨅ (t : Nat -> Set α) (_ : s subseteq iUnion t), ∑' n, ⨆ _ : (t
 n).Nonempty, m (t n)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `MeasureTheory.OuterMeasure.iSup_sInfGen_nonempty`：iSup_sInfGen_nonempty 
{m : Set (OuterMeasure α)} (h : m.Nonempty) (t : Set α) : ⨆ _ : t.Nonempty, sInf
Gen m t = ⨅ (μ : OuterMeasure α) (_ : …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The value of the Infimum of a nonempty set of outer measures on a set is not sim
ply
the minimum value of a measure on that set: it is the infimum sum of measures of
 countable set of
sets that covers that set, where a different measure can be used for each set in
 the cover.
-/
theorem sInf_apply {m : Set (OuterMeasure α)} {s : Set α} (h : m.Nonempty) :
    sInf m s =
      ⨅ (t : ℕ → Set α) (_ : s ⊆ iUnion t), ∑' n, ⨅ (μ : OuterMeasure α) (_ : μ ∈ m), μ (t n) := by
  simp_rw [sInf_eq_boundedBy_sInfGen, boundedBy_apply, iSup_sInfGen_nonempty h]

/-- The value of the Infimum of a set of outer measures on a nonempty set is not simply
the minimum value of a measure on that set: it is the infimum sum of measures of countable set of
sets that covers that set, where a different measure can be used for each set in the cover. -/
/-
**MeasureTheory.OuterMeasure.sInf_apply'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.OuterMeasure`。
形式化陈述：sInf_apply' {m : Set (OuterMeasure α)} {s : Set α} (h : s.Nonempty) : sInf
 m s = ⨅ (t : Nat -> Set α) (_ : s subseteq iUnion t), ∑' n, ⨅ (μ : OuterMeasure
 α) (_ : μ in m), μ (t n)
参数：OuterMeasure α；h : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sInf_empty`：∀ {α : Type u_1} [inst : CompleteLattice α], sInf ∅ = ⊤
· 使用定理 `MeasureTheory.OuterMeasure.top_apply`：top_apply {s : Set α} (h : s.Nonem
pty) : (⊤ : OuterMeasure α) s = ∞
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iInf_neg`：∀ {α : Type u_1} [inst : CompleteLattice α] {p : Prop} {f : p 
→ α}, ¬p → ⨅ (h : p), f h = ⊤
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `iInf_top`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α], ⨅ 
x, ⊤ = ⊤
· 使用定理 `ENNReal.tsum_top`：∀ {α : Type u_1} [Nonempty α], ∑' (x : α), ⊤ = ⊤
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.OuterMeasure.sInf_apply`：sInf_apply {m : Set (OuterMeasure
 α)} {s : Set α} (h : m.Nonempty) : sInf m s = ⨅ (t : Nat -> Set α) (_ : s subse
teq iUnion t), ∑' n, ⨅ (μ :…

--- 原说明 ---
The value of the Infimum of a set of outer measures on a nonempty set is not sim
ply
the minimum value of a measure on that set: it is the infimum sum of measures of
 countable set of
sets that covers that set, where a different measure can be used for each set in
 the cover.
-/
theorem sInf_apply' {m : Set (OuterMeasure α)} {s : Set α} (h : s.Nonempty) :
    sInf m s =
      ⨅ (t : ℕ → Set α) (_ : s ⊆ iUnion t), ∑' n, ⨅ (μ : OuterMeasure α) (_ : μ ∈ m), μ (t n) :=
  m.eq_empty_or_nonempty.elim (fun hm => by simp [hm, h]) sInf_apply

/-- The value of the Infimum of a nonempty family of outer measures on a set is not simply
the minimum value of a measure on that set: it is the infimum sum of measures of countable set of
sets that covers that set, where a different measure can be used for each set in the cover. -/
/-
**MeasureTheory.OuterMeasure.iInf_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.OuterMeasure`。
形式化陈述：iInf_apply {ι} [Nonempty ι] (m : ι -> OuterMeasure α) (s : Set α) : (⨅ i, 
m i) s = ⨅ (t : Nat -> Set α) (_ : s subseteq iUnion t), ∑' n, ⨅ i, m i (t n)
参数：m : ι -> OuterMeasure α；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iInf.eq_1`：∀ {α : Type u} {ι : Sort v} [inst : InfSet α] (s : ι → α), iI
nf s = sInf (Set.range s)
· 使用定理 `MeasureTheory.OuterMeasure.sInf_apply`：sInf_apply {m : Set (OuterMeasure
 α)} {s : Set α} (h : m.Nonempty) : sInf m s = ⨅ (t : Nat -> Set α) (_ : s subse
teq iUnion t), ∑' n, ⨅ (μ :…
· 使用定理 `Set.range_nonempty`：range_nonempty [h : Nonempty ι] (f : ι -> α) : (rang
e f).Nonempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iInf_range`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} [inst : Compl
eteLattice α] {g : β → α} {f : ι → β},   ⨅ b ∈ Set.range f, g b = ⨅ i, g (f i)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The value of the Infimum of a nonempty family of outer measures on a set is not 
simply
the minimum value of a measure on that set: it is the infimum sum of measures of
 countable set of
sets that covers that set, where a different measure can be used for each set in
 the cover.
-/
theorem iInf_apply {ι} [Nonempty ι] (m : ι → OuterMeasure α) (s : Set α) :
    (⨅ i, m i) s = ⨅ (t : ℕ → Set α) (_ : s ⊆ iUnion t), ∑' n, ⨅ i, m i (t n) := by
  rw [iInf, sInf_apply (range_nonempty m)]
  simp only [iInf_range]

/-- The value of the Infimum of a family of outer measures on a nonempty set is not simply
the minimum value of a measure on that set: it is the infimum sum of measures of countable set of
sets that covers that set, where a different measure can be used for each set in the cover. -/
/-
**MeasureTheory.OuterMeasure.iInf_apply'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.OuterMeasure`。
形式化陈述：iInf_apply' {ι} (m : ι -> OuterMeasure α) {s : Set α} (hs : s.Nonempty) : 
(⨅ i, m i) s = ⨅ (t : Nat -> Set α) (_ : s subseteq iUnion t), ∑' n, ⨅ i, m i (t
 n)
参数：m : ι -> OuterMeasure α；hs : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iInf.eq_1`：∀ {α : Type u} {ι : Sort v} [inst : InfSet α] (s : ι → α), iI
nf s = sInf (Set.range s)
· 使用定理 `MeasureTheory.OuterMeasure.sInf_apply'`：sInf_apply' {m : Set (OuterMeasu
re α)} {s : Set α} (h : s.Nonempty) : sInf m s = ⨅ (t : Nat -> Set α) (_ : s sub
seteq iUnion t), ∑' n, ⨅ (μ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iInf_range`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} [inst : Compl
eteLattice α] {g : β → α} {f : ι → β},   ⨅ b ∈ Set.range f, g b = ⨅ i, g (f i)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The value of the Infimum of a family of outer measures on a nonempty set is not 
simply
the minimum value of a measure on that set: it is the infimum sum of measures of
 countable set of
sets that covers that set, where a different measure can be used for each set in
 the cover.
-/
theorem iInf_apply' {ι} (m : ι → OuterMeasure α) {s : Set α} (hs : s.Nonempty) :
    (⨅ i, m i) s = ⨅ (t : ℕ → Set α) (_ : s ⊆ iUnion t), ∑' n, ⨅ i, m i (t n) := by
  rw [iInf, sInf_apply' hs]
  simp only [iInf_range]

/-- The value of the Infimum of a nonempty family of outer measures on a set is not simply
the minimum value of a measure on that set: it is the infimum sum of measures of countable set of
sets that covers that set, where a different measure can be used for each set in the cover. -/
/-
**MeasureTheory.OuterMeasure.biInf_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.OuterMeasure`。
形式化陈述：biInf_apply {ι} {I : Set ι} (hI : I.Nonempty) (m : ι -> OuterMeasure α) (s
 : Set α) : (⨅ i in I, m i) s = ⨅ (t : Nat -> Set α) (_ : s subseteq iUnion t), 
∑' n, ⨅ i in I, m i (t n)
参数：hI : I.Nonempty；m : ι -> OuterMeasure α；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.to_subtype`：∀ {α : Type u} {s : Set α}, s.Nonempty → Nonemp
ty ↑s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.OuterMeasure.iInf_apply`：iInf_apply {ι} [Nonempty ι] (m : 
ι -> OuterMeasure α) (s : Set α) : (⨅ i, m i) s = ⨅ (t : Nat -> Set α) (_ : s su
bseteq iUnion t), ∑' n, ⨅ i…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The value of the Infimum of a nonempty family of outer measures on a set is not 
simply
the minimum value of a measure on that set: it is the infimum sum of measures of
 countable set of
sets that covers that set, where a different measure can be used for each set in
 the cover.
-/
theorem biInf_apply {ι} {I : Set ι} (hI : I.Nonempty) (m : ι → OuterMeasure α) (s : Set α) :
    (⨅ i ∈ I, m i) s = ⨅ (t : ℕ → Set α) (_ : s ⊆ iUnion t), ∑' n, ⨅ i ∈ I, m i (t n) := by
  have := hI.to_subtype
  simp only [← iInf_subtype'', iInf_apply]

/-- The value of the Infimum of a nonempty family of outer measures on a set is not simply
the minimum value of a measure on that set: it is the infimum sum of measures of countable set of
sets that covers that set, where a different measure can be used for each set in the cover. -/
/-
**MeasureTheory.OuterMeasure.biInf_apply'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.OuterMeasure`。
形式化陈述：biInf_apply' {ι} (I : Set ι) (m : ι -> OuterMeasure α) {s : Set α} (hs : s
.Nonempty) : (⨅ i in I, m i) s = ⨅ (t : Nat -> Set α) (_ : s subseteq iUnion t),
 ∑' n, ⨅ i in I, m i (t n)
参数：I : Set ι；m : ι -> OuterMeasure α；hs : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.OuterMeasure.iInf_apply'`：iInf_apply' {ι} (m : ι -> OuterM
easure α) {s : Set α} (hs : s.Nonempty) : (⨅ i, m i) s = ⨅ (t : Nat -> Set α) (_
 : s subseteq iUnion t), ∑' …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The value of the Infimum of a nonempty family of outer measures on a set is not 
simply
the minimum value of a measure on that set: it is the infimum sum of measures of
 countable set of
sets that covers that set, where a different measure can be used for each set in
 the cover.
-/
theorem biInf_apply' {ι} (I : Set ι) (m : ι → OuterMeasure α) {s : Set α} (hs : s.Nonempty) :
    (⨅ i ∈ I, m i) s = ⨅ (t : ℕ → Set α) (_ : s ⊆ iUnion t), ∑' n, ⨅ i ∈ I, m i (t n) := by
  simp only [← iInf_subtype'', iInf_apply' _ hs]
/-
**MeasureTheory.OuterMeasure.map_iInf_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.OuterMeasure`。
形式化陈述：map_iInf_le {ι β} (f : α -> β) (m : ι -> OuterMeasure α) : map f (⨅ i, m i
) <= ⨅ i, map f (m i)
参数：f : α -> β；m : ι -> OuterMeasure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_iInf_le`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} [in
st : CompleteLattice α] {s : ι → α} [inst_1 : CompleteLattice β]   {f : α → β}, 
Monotone f…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.OuterMeasure.map_mono`：map_mono {β} (f : α -> β) : Monoton
e (map f)
-/
theorem map_iInf_le {ι β} (f : α → β) (m : ι → OuterMeasure α) :
    map f (⨅ i, m i) ≤ ⨅ i, map f (m i) :=
  (map_mono f).map_iInf_le
/-
**MeasureTheory.OuterMeasure.comap_iInf** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.OuterMeasure`。
形式化陈述：comap_iInf {ι β} (f : α -> β) (m : ι -> OuterMeasure β) : comap f (⨅ i, m 
i) = ⨅ i, comap f (m i)
参数：f : α -> β；m : ι -> OuterMeasure β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.OuterMeasure.ext_nonempty`：ext_nonempty {μ₁ μ₂ : OuterMeas
ure α} (h : forall s : Set α, s.Nonempty -> μ₁ s = μ₂ s) : μ₁ = μ₂
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Monotone.map_iInf_le`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} [in
st : CompleteLattice α] {s : ι → α} [inst_1 : CompleteLattice β]   {f : α → β}, 
Monotone f…
· 使用定理 `MeasureTheory.OuterMeasure.comap_mono`：comap_mono {β} (f : α -> β) : Mon
otone (comap f)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.OuterMeasure.iInf_apply'`：iInf_apply' {ι} (m : ι -> OuterM
easure α) {s : Set α} (hs : s.Nonempty) : (⨅ i, m i) s = ⨅ (t : Nat -> Set α) (_
 : s subseteq iUnion t), ∑' …
· 使用定理 `Set.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {s : Set
 α}, s.Nonempty → (f '' s).Nonempty
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.preimage_iUnion`：preimage_iUnion {f : α -> β} {s : ι -> Set β} : (f 
⁻¹' ⋃ i, s i) = ⋃ i, f ⁻¹' s i
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iInf_le_of_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α
] {f : ι → α} {a : α} (i : ι), f i ≤ a → iInf f ≤ a
· 使用定理 `ENNReal.tsum_le_tsum`：∀ {α : Type u_1} {f g : α → ENNReal}, (∀ (a : α), 
f a ≤ g a) → ∑' (a : α), f a ≤ ∑' (a : α), g a
· 使用定理 `iInf_mono`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f
 g : ι → α}, (∀ (i : ι), g i ≤ f i) → iInf g ≤ iInf f
· 使用定理 `MeasureTheory.OuterMeasure.mono`：∀ {α : Type u_2} (self : MeasureTheory.
OuterMeasure α) {s₁ s₂ : Set α}, s₁ ⊆ s₂ → self.measureOf s₁ ≤ self.measureOf s₂
· 使用定理 `Set.image_preimage_subset`：image_preimage_subset (f : α -> β) (s : Set β
) : f '' f ⁻¹' s subseteq s
-/
theorem comap_iInf {ι β} (f : α → β) (m : ι → OuterMeasure β) :
    comap f (⨅ i, m i) = ⨅ i, comap f (m i) := by
  refine ext_nonempty fun s hs => ?_
  refine ((comap_mono f).map_iInf_le s).antisymm ?_
  simp only [comap_apply, iInf_apply' _ hs, iInf_apply' _ (hs.image _), le_iInf_iff,
    Set.image_subset_iff, preimage_iUnion]
  refine fun t ht => iInf_le_of_le _ (iInf_le_of_le ht <| ENNReal.tsum_le_tsum fun k => ?_)
  exact iInf_mono fun i => (m i).mono (image_preimage_subset _ _)
/-
**MeasureTheory.OuterMeasure.map_iInf** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.O
uterMeasure`。
形式化陈述：map_iInf {ι β} {f : α -> β} (hf : Injective f) (m : ι -> OuterMeasure α) :
 map f (⨅ i, m i) = restrict (range f) (⨅ i, map f (m i))
参数：hf : Injective f；m : ι -> OuterMeasure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.OuterMeasure.comap_iInf`：comap_iInf {ι β} (f : α -> β) (m 
: ι -> OuterMeasure β) : comap f (⨅ i, m i) = ⨅ i, comap f (m i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.OuterMeasure.comap_map`：comap_map {β} {f : α -> β} (hf : I
njective f) (m : OuterMeasure α) : comap f (map f m) = m
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.OuterMeasure.map_comap`：map_comap {β} (f : α -> β) (m : Ou
terMeasure β) : map f (comap f m) = restrict (range f) m
-/
theorem map_iInf {ι β} {f : α → β} (hf : Injective f) (m : ι → OuterMeasure α) :
    map f (⨅ i, m i) = restrict (range f) (⨅ i, map f (m i)) := by
  refine Eq.trans ?_ (map_comap _ _)
  simp only [comap_iInf, comap_map hf]
/-
**MeasureTheory.OuterMeasure.map_iInf_comap** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.OuterMeasure`。
形式化陈述：map_iInf_comap {ι β} [Nonempty ι] {f : α -> β} (m : ι -> OuterMeasure β) :
 map f (⨅ i, comap f (m i)) = ⨅ i, map f (comap f (m i))
参数：m : ι -> OuterMeasure β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.OuterMeasure.map_iInf_le`：map_iInf_le {ι β} (f : α -> β) (
m : ι -> OuterMeasure α) : map f (⨅ i, m i) <= ⨅ i, map f (m i)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.OuterMeasure.iInf_apply`：iInf_apply {ι} [Nonempty ι] (m : 
ι -> OuterMeasure α) (s : Set α) : (⨅ i, m i) s = ⨅ (t : Nat -> Set α) (_ : s su
bseteq iUnion t), ∑' n, ⨅ i…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iInf_le_of_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α
] {f : ι → α} {a : α} (i : ι), f i ≤ a → iInf f ≤ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.iUnion_union`：iUnion_union [Nonempty ι] (s : Set β) (t : ι -> Set β)
 : (⋃ i, t i) union s = ⋃ i, t i union s
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
· 使用定理 `Set.inter_subset`：inter_subset (a b c : Set α) : a inter b subseteq c ↔ 
a subseteq bᶜ union c
· 使用定理 `Set.image_iUnion`：image_iUnion {f : α -> β} {s : ι -> Set α} : (f '' ⋃ i
, s i) = ⋃ i, f '' s i
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `ENNReal.tsum_le_tsum`：∀ {α : Type u_1} {f g : α → ENNReal}, (∀ (a : α), 
f a ≤ g a) → ∑' (a : α), f a ≤ ∑' (a : α), g a
· 使用定理 `iInf_mono`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f
 g : ι → α}, (∀ (i : ι), g i ≤ f i) → iInf g ≤ iInf f
· 使用定理 `MeasureTheory.OuterMeasure.mono`：∀ {α : Type u_2} (self : MeasureTheory.
OuterMeasure α) {s₁ s₂ : Set α}, s₁ ⊆ s₂ → self.measureOf s₁ ≤ self.measureOf s₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.preimage_range`：preimage_range (f : α -> β) : f ⁻¹' range f = univ
· 使用定理 `Set.compl_univ`：compl_univ : (univ : Set α)ᶜ = ∅
· 使用定理 `Set.union_empty`：union_empty (a : Set α) : a union ∅ = a
· 使用定理 `subset_rfl`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorde
r α] {a : α}, a ⊆ a
-/
theorem map_iInf_comap {ι β} [Nonempty ι] {f : α → β} (m : ι → OuterMeasure β) :
    map f (⨅ i, comap f (m i)) = ⨅ i, map f (comap f (m i)) := by
  refine (map_iInf_le _ _).antisymm fun s => ?_
  simp only [map_apply, comap_apply, iInf_apply, le_iInf_iff]
  refine fun t ht => iInf_le_of_le (fun n => f '' t n ∪ (range f)ᶜ) (iInf_le_of_le ?_ ?_)
  · rw [← iUnion_union, Set.union_comm, ← inter_subset, ← image_iUnion, ←
      image_preimage_eq_inter_range]
    exact image_mono ht
  · refine ENNReal.tsum_le_tsum fun n => iInf_mono fun i => (m i).mono ?_
    simpa only [preimage_union, preimage_compl, preimage_range, compl_univ, union_empty,
      image_subset_iff] using subset_rfl
/-
**MeasureTheory.OuterMeasure.map_biInf_comap** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.OuterMeasure`。
形式化陈述：map_biInf_comap {ι β} {I : Set ι} (hI : I.Nonempty) {f : α -> β} (m : ι ->
 OuterMeasure β) : map f (⨅ i in I, comap f (m i)) = ⨅ i in I, map f (comap f (m
 i))
参数：hI : I.Nonempty；m : ι -> OuterMeasure β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.to_subtype`：∀ {α : Type u} {s : Set α}, s.Nonempty → Nonemp
ty ↑s
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iInf_subtype''`：∀ {α : Type u_1} [inst : CompleteLattice α] {ι : Type u_
8} (s : Set ι) (f : ι → α), ⨅ i, f ↑i = ⨅ t ∈ s, f t
· 使用定理 `MeasureTheory.OuterMeasure.map_iInf_comap`：map_iInf_comap {ι β} [Nonempt
y ι] {f : α -> β} (m : ι -> OuterMeasure β) : map f (⨅ i, comap f (m i)) = ⨅ i, 
map f (comap f (m i))
-/
theorem map_biInf_comap {ι β} {I : Set ι} (hI : I.Nonempty) {f : α → β} (m : ι → OuterMeasure β) :
    map f (⨅ i ∈ I, comap f (m i)) = ⨅ i ∈ I, map f (comap f (m i)) := by
  have := hI.to_subtype
  rw [← iInf_subtype'', ← iInf_subtype'']
  exact map_iInf_comap _
/-
**MeasureTheory.OuterMeasure.restrict_iInf_restrict** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.OuterMeasure`。
形式化陈述：restrict_iInf_restrict {ι} (s : Set α) (m : ι -> OuterMeasure α) : restric
t s (⨅ i, restrict s (m i)) = restrict s (⨅ i, m i)
参数：s : Set α；m : ι -> OuterMeasure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.OuterMeasure.map_iInf`：map_iInf {ι β} {f : α -> β} (hf : I
njective f) (m : ι -> OuterMeasure α) : map f (⨅ i, m i) = restrict (range f) (⨅
 i, map f (m i))
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `MeasureTheory.OuterMeasure.comap_iInf`：comap_iInf {ι β} (f : α -> β) (m 
: ι -> OuterMeasure β) : comap f (⨅ i, m i) = ⨅ i, comap f (m i)
-/
theorem restrict_iInf_restrict {ι} (s : Set α) (m : ι → OuterMeasure α) :
    restrict s (⨅ i, restrict s (m i)) = restrict s (⨅ i, m i) :=
  calc restrict s (⨅ i, restrict s (m i))
    _ = restrict (range ((↑) : s → α)) (⨅ i, restrict s (m i)) := by rw [Subtype.range_coe]
    _ = map ((↑) : s → α) (⨅ i, comap (↑) (m i)) := (map_iInf Subtype.coe_injective _).symm
    _ = restrict s (⨅ i, m i) := congr_arg (map ((↑) : s → α)) (comap_iInf _ _).symm
/-
**MeasureTheory.OuterMeasure.restrict_iInf** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.OuterMeasure`。
形式化陈述：restrict_iInf {ι} [Nonempty ι] (s : Set α) (m : ι -> OuterMeasure α) : res
trict s (⨅ i, m i) = ⨅ i, restrict s (m i)
参数：s : Set α；m : ι -> OuterMeasure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `MeasureTheory.OuterMeasure.comap_iInf`：comap_iInf {ι β} (f : α -> β) (m 
: ι -> OuterMeasure β) : comap f (⨅ i, m i) = ⨅ i, comap f (m i)
· 使用定理 `MeasureTheory.OuterMeasure.map_iInf_comap`：map_iInf_comap {ι β} [Nonempt
y ι] {f : α -> β} (m : ι -> OuterMeasure β) : map f (⨅ i, comap f (m i)) = ⨅ i, 
map f (comap f (m i))
-/
theorem restrict_iInf {ι} [Nonempty ι] (s : Set α) (m : ι → OuterMeasure α) :
    restrict s (⨅ i, m i) = ⨅ i, restrict s (m i) :=
  (congr_arg (map ((↑) : s → α)) (comap_iInf _ _)).trans (map_iInf_comap _)
/-
**MeasureTheory.OuterMeasure.restrict_biInf** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.OuterMeasure`。
形式化陈述：restrict_biInf {ι} {I : Set ι} (hI : I.Nonempty) (s : Set α) (m : ι -> Out
erMeasure α) : restrict s (⨅ i in I, m i) = ⨅ i in I, restrict s (m i)
参数：hI : I.Nonempty；s : Set α；m : ι -> OuterMeasure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.to_subtype`：∀ {α : Type u} {s : Set α}, s.Nonempty → Nonemp
ty ↑s
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iInf_subtype''`：∀ {α : Type u_1} [inst : CompleteLattice α] {ι : Type u_
8} (s : Set ι) (f : ι → α), ⨅ i, f ↑i = ⨅ t ∈ s, f t
· 使用定理 `MeasureTheory.OuterMeasure.restrict_iInf`：restrict_iInf {ι} [Nonempty ι]
 (s : Set α) (m : ι -> OuterMeasure α) : restrict s (⨅ i, m i) = ⨅ i, restrict s
 (m i)
-/
theorem restrict_biInf {ι} {I : Set ι} (hI : I.Nonempty) (s : Set α) (m : ι → OuterMeasure α) :
    restrict s (⨅ i ∈ I, m i) = ⨅ i ∈ I, restrict s (m i) := by
  have := hI.to_subtype
  rw [← iInf_subtype'', ← iInf_subtype'']
  exact restrict_iInf _ _

/-- This proves that Inf and restrict commute for outer measures, so long as the set of
outer measures is nonempty. -/
/-
**MeasureTheory.OuterMeasure.restrict_sInf_eq_sInf_restrict** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory.OuterMeasure`。
形式化陈述：restrict_sInf_eq_sInf_restrict (m : Set (OuterMeasure α)) {s : Set α} (hm 
: m.Nonempty) : restrict s (sInf m) = sInf (restrict s '' m)
参数：m : Set (OuterMeasure α)；hm : m.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sInf_eq_iInf`：∀ {α : Type u_1} [inst : CompleteLattice α] {s : Set α}, s
Inf s = ⨅ a ∈ s, a
· 使用定理 `MeasureTheory.OuterMeasure.restrict_biInf`：restrict_biInf {ι} {I : Set ι
} (hI : I.Nonempty) (s : Set α) (m : ι -> OuterMeasure α) : restrict s (⨅ i in I
, m i) = ⨅ i in I, restrict s (…
· 使用定理 `iInf_image`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLattice α] {
γ : Type u_8} {f : β → γ} {g : γ → α} {t : Set β},   ⨅ c ∈ f '' t, g c = ⨅ b ∈ t
…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
This proves that Inf and restrict commute for outer measures, so long as the set
 of
outer measures is nonempty.
-/
theorem restrict_sInf_eq_sInf_restrict (m : Set (OuterMeasure α)) {s : Set α} (hm : m.Nonempty) :
    restrict s (sInf m) = sInf (restrict s '' m) := by
  simp only [sInf_eq_iInf, restrict_biInf, hm, iInf_image]

end sInfGen

end OuterMeasure

end MeasureTheory

