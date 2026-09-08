/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

/-!
# Method of exhaustion

If `μ, ν` are two measures with `ν` s-finite, then there exists a set `s` such that
`μ` is sigma-finite on `s`, and for all sets `t ⊆ sᶜ`, either `ν t = 0` or `μ t = ∞`.

## Main definitions

* `MeasureTheory.Measure.sigmaFiniteSetWRT`: if such a set exists, `μ.sigmaFiniteSetWRT ν` is
  a measurable set such that `μ.restrict (μ.sigmaFiniteSetWRT ν)` is sigma-finite and
  for all sets `t ⊆ (μ.sigmaFiniteSetWRT ν)ᶜ`, either `ν t = 0` or `μ t = ∞`.
  If no such set exists (which is only possible if `ν` is not s-finite), we define
  `μ.sigmaFiniteSetWRT ν = ∅`.
* `MeasureTheory.Measure.sigmaFiniteSet`: for an s-finite measure `μ`, a measurable set such that
  `μ.restrict μ.sigmaFiniteSet` is sigma-finite, and for all sets `s ⊆ μ.sigmaFiniteSetᶜ`,
  either `μ s = 0` or `μ s = ∞`.
  Defined as `μ.sigmaFiniteSetWRT μ`.

## Main statements

* `measure_eq_top_of_subset_compl_sigmaFiniteSetWRT`: for s-finite `ν`, for all sets `s`
  in `(sigmaFiniteSetWRT μ ν)ᶜ`, if `ν s ≠ 0` then `μ s = ∞`.
* An instance showing that `μ.restrict (sigmaFiniteSetWRT μ ν)` is sigma-finite.
* `restrict_compl_sigmaFiniteSetWRT`: if `μ ≪ ν` and `ν` is s-finite, then
  `μ.restrict (μ.sigmaFiniteSetWRT ν)ᶜ = ∞ • ν.restrict (μ.sigmaFiniteSetWRT ν)ᶜ`. As a consequence,
  that restriction is s-finite.

* An instance showing that `μ.restrict μ.sigmaFiniteSet` is sigma-finite.
* `restrict_compl_sigmaFiniteSet_eq_zero_or_top`: the measure `μ.restrict μ.sigmaFiniteSetᶜ` takes
  only two values: 0 and ∞ .
* `measure_compl_sigmaFiniteSet_eq_zero_iff_sigmaFinite`: a measure `μ` is sigma-finite
  iff `μ μ.sigmaFiniteSetᶜ = 0`.

## References

* [P. R. Halmos, *Measure theory*, 17.3 and 30.11][halmos1950measure]

-/

@[expose] public section

assert_not_exists MeasureTheory.Measure.rnDeriv
assert_not_exists MeasureTheory.VectorMeasure

open scoped ENNReal Topology

open Filter

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α} {s t : Set α}

open scoped Classical in
/-- A measurable set such that `μ.restrict (μ.sigmaFiniteSetWRT ν)` is sigma-finite and for all
measurable sets `t ⊆ sᶜ`, either `ν t = 0` or `μ t = ∞`. -/
-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/-
**MeasureTheory.Measure.sigmaFiniteSetWRT** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheo
ry.Measure`。
形式化陈述：{α : Type u_1} → {mα : MeasurableSpace α} → MeasureTheory.Measure α → Meas
ureTheory.Measure α → Set α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def Measure.sigmaFiniteSetWRT (μ ν : Measure α) : Set α :=
  if h : ∃ s : Set α, MeasurableSet s ∧ SigmaFinite (μ.restrict s)
    ∧ (∀ t, t ⊆ sᶜ → ν t ≠ 0 → μ t = ∞)
  then h.choose
  else ∅

@[measurability]
/-
**MeasureTheory.measurableSet_sigmaFiniteSetWRT** 是 Mathlib 中的一个引理，位于命名空间 `Measu
reTheory`。
形式化陈述：measurableSet_sigmaFiniteSetWRT : MeasurableSet (μ.sigmaFiniteSetWRT ν)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.sigmaFiniteSetWRT.eq_1`：∀ {α : Type u_1} {mα : Mea
surableSpace α} (μ ν : MeasureTheory.Measure α),   μ.sigmaFiniteSetWRT ν =     i
f h : ∃ s, MeasurableSet s ∧ Measu…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `MeasurableSet.empty`：MeasurableSet.empty [MeasurableSpace α] : Measurabl
eSet (∅ : Set α)
-/
lemma measurableSet_sigmaFiniteSetWRT :
    MeasurableSet (μ.sigmaFiniteSetWRT ν) := by
  rw [Measure.sigmaFiniteSetWRT]
  split_ifs with h
  · exact h.choose_spec.1
  · exact MeasurableSet.empty
/-
**MeasureTheory.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SigmaFinite (μ.restrict (μ.sigmaFiniteSetWRT ν)) := by
  rw [Measure.sigmaFiniteSetWRT]
  split_ifs with h
  · exact h.choose_spec.2.1
  · rw [Measure.restrict_empty]
    infer_instance

section IsFiniteMeasure

/-! We prove that the condition in the definition of `sigmaFiniteSetWRT` is true for finite
measures. Since every s-finite measure is absolutely continuous with respect to a finite measure,
the condition will then also be true for s-finite measures. -/

/-- Let `C` be the supremum of `ν s` over all measurable sets `s` such that `μ.restrict s` is
sigma-finite. `C` is finite since `ν` is a finite measure. Then there exists a measurable set `t`
with `μ.restrict t` sigma-finite such that `ν t ≥ C - 1/n`. -/
/-
**MeasureTheory.exists_isSigmaFiniteSet_measure_ge** 是 Mathlib 中的一个引理，位于命名空间 `Me
asureTheory`。
形式化陈述：exists_isSigmaFiniteSet_measure_ge (μ ν : Measure α) [IsFiniteMeasure ν] (
n : Nat) : exists t, MeasurableSet t ∧ SigmaFinite (μ.restrict t) ∧ (⨆ (s) (_ : 
MeasurableSet s) (_ : SigmaFinite (μ.restrict s)), ν s) - 1 / n <= ν t
参数：μ ν : Measure α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `MeasureTheory.measure_lt_top`：measure_lt_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s < ∞
· 使用定理 `exists_lt_of_lt_ciSup`：exists_lt_of_lt_ciSup [Nonempty ι] {f : ι -> α} (
h : b < iSup f) : exists i, b < f i
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `ENNReal.sub_lt_self`：∀ {a b : ENNReal}, a ≠ ⊤ → a ≠ 0 → b ≠ 0 → a - b < 
a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LT.lt.ne_bot`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderBot α] {
a b : α}, b < a → a ≠ ⊥
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iSup_neg`：iSup_neg {p : Prop} {f : p -> α} (hp : ¬p) : ⨆ h : p, f h = ⊥
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `ENNReal.iSup_zero`：∀ {ι : Sort u_1}, ⨆ x, 0 = 0
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `iSup_true`：iSup_true {s : True -> α} : iSup s = s trivial
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
Let `C` be the supremum of `ν s` over all measurable sets `s` such that `μ.restr
ict s` is
sigma-finite. `C` is finite since `ν` is a finite measure. Then there exists a m
easurable set `t`
with `μ.restrict t` sigma-finite such that `ν t ≥ C - 1/n`.
-/
lemma exists_isSigmaFiniteSet_measure_ge (μ ν : Measure α) [IsFiniteMeasure ν] (n : ℕ) :
    ∃ t, MeasurableSet t ∧ SigmaFinite (μ.restrict t)
      ∧ (⨆ (s) (_ : MeasurableSet s) (_ : SigmaFinite (μ.restrict s)), ν s) - 1 / n ≤ ν t := by
  by_cases! hC_lt : 1 / n < ⨆ (s) (_ : MeasurableSet s) (_ : SigmaFinite (μ.restrict s)), ν s
  · have h_lt_top : ⨆ (s) (_ : MeasurableSet s) (_ : SigmaFinite (μ.restrict s)), ν s < ∞ := by
      refine (?_ : ⨆ (s) (_ : MeasurableSet s)
        (_ : SigmaFinite (μ.restrict s)), ν s ≤ ν Set.univ).trans_lt (measure_lt_top _ _)
      refine iSup_le (fun s ↦ ?_)
      exact iSup_le (fun _ ↦ iSup_le (fun _ ↦ measure_mono (Set.subset_univ s)))
    obtain ⟨t, ht⟩ := exists_lt_of_lt_ciSup
      (ENNReal.sub_lt_self h_lt_top.ne hC_lt.ne_bot (by simp) :
          (⨆ (s) (_ : MeasurableSet s) (_ : SigmaFinite (μ.restrict s)), ν s) - 1 / n
        < ⨆ (s) (_ : MeasurableSet s) (_ : SigmaFinite (μ.restrict s)), ν s)
    have ht_meas : MeasurableSet t := by
      by_contra h_notMem
      simp only [h_notMem] at ht
      simp at ht
    have ht_mem : SigmaFinite (μ.restrict t) := by
      by_contra h_notMem
      simp only [h_notMem] at ht
      simp at ht
    refine ⟨t, ht_meas, ht_mem, ?_⟩
    simp only [ht_meas, ht_mem, iSup_true] at ht
    exact ht.le
  · refine ⟨∅, MeasurableSet.empty, by rw [Measure.restrict_empty]; infer_instance, ?_⟩
    rw [tsub_eq_zero_of_le hC_lt]
    exact zero_le

/-- A measurable set such that `μ.restrict (μ.sigmaFiniteSetGE ν n)` is sigma-finite and
for `C` the supremum of `ν s` over all measurable sets `s` with `μ.restrict s` sigma-finite,
`ν (μ.sigmaFiniteSetGE ν n) ≥ C - 1/n`. -/
-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/-
**MeasureTheory.Measure.sigmaFiniteSetGE** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheor
y.Measure`。
形式化陈述：{α : Type u_1} →   {mα : MeasurableSpace α} →     MeasureTheory.Measure α 
→ (ν : MeasureTheory.Measure α) → [MeasureTheory.IsFiniteMeasure ν] → ℕ → Set α
参数：ν : MeasureTheory.Measure α。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.exists_isSigmaFiniteSet_measure_ge`：exists_isSigmaFiniteSe
t_measure_ge (μ ν : Measure α) [IsFiniteMeasure ν] (n : Nat) : exists t, Measura
bleSet t ∧ SigmaFinite (μ.restrict t) …
-/
noncomputable def Measure.sigmaFiniteSetGE (μ ν : Measure α) [IsFiniteMeasure ν] (n : ℕ) : Set α :=
  (exists_isSigmaFiniteSet_measure_ge μ ν n).choose
/-
**MeasureTheory.measurableSet_sigmaFiniteSetGE** 是 Mathlib 中的一个引理，位于命名空间 `Measur
eTheory`。
形式化陈述：measurableSet_sigmaFiniteSetGE [IsFiniteMeasure ν] (n : Nat) : MeasurableS
et (μ.sigmaFiniteSetGE ν n)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `MeasureTheory.exists_isSigmaFiniteSet_measure_ge`：exists_isSigmaFiniteSe
t_measure_ge (μ ν : Measure α) [IsFiniteMeasure ν] (n : Nat) : exists t, Measura
bleSet t ∧ SigmaFinite (μ.restrict t) …
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
lemma measurableSet_sigmaFiniteSetGE [IsFiniteMeasure ν] (n : ℕ) :
    MeasurableSet (μ.sigmaFiniteSetGE ν n) :=
  (exists_isSigmaFiniteSet_measure_ge μ ν n).choose_spec.1
/-
**MeasureTheory.sigmaFinite_restrict_sigmaFiniteSetGE** 是 Mathlib 中的一个引理，位于命名空间 
`MeasureTheory`。
形式化陈述：sigmaFinite_restrict_sigmaFiniteSetGE (μ ν : Measure α) [IsFiniteMeasure ν
] (n : Nat) : SigmaFinite (μ.restrict (μ.sigmaFiniteSetGE ν n))
参数：μ ν : Measure α；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `MeasureTheory.exists_isSigmaFiniteSet_measure_ge`：exists_isSigmaFiniteSe
t_measure_ge (μ ν : Measure α) [IsFiniteMeasure ν] (n : Nat) : exists t, Measura
bleSet t ∧ SigmaFinite (μ.restrict t) …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
lemma sigmaFinite_restrict_sigmaFiniteSetGE (μ ν : Measure α) [IsFiniteMeasure ν] (n : ℕ) :
    SigmaFinite (μ.restrict (μ.sigmaFiniteSetGE ν n)) :=
  (exists_isSigmaFiniteSet_measure_ge μ ν n).choose_spec.2.1
/-
**MeasureTheory.measure_sigmaFiniteSetGE_le** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTh
eory`。
形式化陈述：measure_sigmaFiniteSetGE_le (μ ν : Measure α) [IsFiniteMeasure ν] (n : Nat
) : ν (μ.sigmaFiniteSetGE ν n) <= ⨆ (s) (_ : MeasurableSet s) (_ : SigmaFinite (
μ.restrict s)), ν s
参数：μ ν : Measure α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用引理 `MeasureTheory.sigmaFinite_restrict_sigmaFiniteSetGE`：sigmaFinite_restric
t_sigmaFiniteSetGE (μ ν : Measure α) [IsFiniteMeasure ν] (n : Nat) : SigmaFinite
 (μ.restrict (μ.sigmaFiniteSetGE ν n))
· 使用定理 `le_iSup₂`：le_iSup₂ {f : forall i, κ i -> α} (i : ι) (j : κ i) : f i j <=
 ⨆ (i) (j), f i j
· 使用引理 `MeasureTheory.measurableSet_sigmaFiniteSetGE`：measurableSet_sigmaFiniteS
etGE [IsFiniteMeasure ν] (n : Nat) : MeasurableSet (μ.sigmaFiniteSetGE ν n)
-/
lemma measure_sigmaFiniteSetGE_le (μ ν : Measure α) [IsFiniteMeasure ν] (n : ℕ) :
    ν (μ.sigmaFiniteSetGE ν n)
      ≤ ⨆ (s) (_ : MeasurableSet s) (_ : SigmaFinite (μ.restrict s)), ν s := by
  refine (le_iSup (f := fun s ↦ _)
    (sigmaFinite_restrict_sigmaFiniteSetGE μ ν n)).trans ?_
  exact le_iSup₂ (f := fun s _ ↦ ⨆ (_ : SigmaFinite (μ.restrict s)), ν s) (μ.sigmaFiniteSetGE ν n)
    (measurableSet_sigmaFiniteSetGE n)
/-
**MeasureTheory.measure_sigmaFiniteSetGE_ge** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTh
eory`。
形式化陈述：measure_sigmaFiniteSetGE_ge (μ ν : Measure α) [IsFiniteMeasure ν] (n : Nat
) : (⨆ (s) (_ : MeasurableSet s) (_ : SigmaFinite (μ.restrict s)), ν s) - 1 / n 
<= ν (μ.sigmaFiniteSetGE ν n)
参数：μ ν : Measure α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `MeasureTheory.exists_isSigmaFiniteSet_measure_ge`：exists_isSigmaFiniteSe
t_measure_ge (μ ν : Measure α) [IsFiniteMeasure ν] (n : Nat) : exists t, Measura
bleSet t ∧ SigmaFinite (μ.restrict t) …
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
lemma measure_sigmaFiniteSetGE_ge (μ ν : Measure α) [IsFiniteMeasure ν] (n : ℕ) :
    (⨆ (s) (_ : MeasurableSet s) (_ : SigmaFinite (μ.restrict s)), ν s) - 1 / n
      ≤ ν (μ.sigmaFiniteSetGE ν n) :=
  (exists_isSigmaFiniteSet_measure_ge μ ν n).choose_spec.2.2
/-
**MeasureTheory.tendsto_measure_sigmaFiniteSetGE** 是 Mathlib 中的一个引理，位于命名空间 `Meas
ureTheory`。
形式化陈述：tendsto_measure_sigmaFiniteSetGE (μ ν : Measure α) [IsFiniteMeasure ν] : T
endsto (fun n => ν (μ.sigmaFiniteSetGE ν n)) atTop (𝓝 (⨆ (s) (_ : MeasurableSet 
s) (_ : SigmaFinite (μ.restrict s)), ν s))
参数：μ ν : Measure α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_of_tendsto_of_tendsto_of_le_of_le`：tendsto_of_tendsto_of_tendsto
_of_le_of_le [OrderTopology α] {f g h : β -> α} {b : Filter β} {a : α} (hg : Ten
dsto g b (𝓝 a)) (hh : Tendsto h…
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tsub_zero`：tsub_zero (a : α) : a - 0 = a
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `ENNReal.Tendsto.sub`：∀ {α : Type u_1} {f : Filter α} {ma mb : α → ENNRea
l} {a b : ENNReal},   Filter.Tendsto ma f (nhds a) →     Filter.Tendsto mb f (nh
ds b) → a…
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `ENNReal.tendsto_inv_nat_nhds_zero`：Filter.Tendsto (fun n => (↑n)⁻¹) Filt
er.atTop (nhds 0)
· 使用定理 `ENNReal.zero_ne_top`：0 ≠ ⊤
· 使用引理 `MeasureTheory.measure_sigmaFiniteSetGE_ge`：measure_sigmaFiniteSetGE_ge (
μ ν : Measure α) [IsFiniteMeasure ν] (n : Nat) : (⨆ (s) (_ : MeasurableSet s) (_
 : SigmaFinite (μ.restrict s)),…
· 使用引理 `MeasureTheory.measure_sigmaFiniteSetGE_le`：measure_sigmaFiniteSetGE_le (
μ ν : Measure α) [IsFiniteMeasure ν] (n : Nat) : ν (μ.sigmaFiniteSetGE ν n) <= ⨆
 (s) (_ : MeasurableSet s) (_ :…
-/
lemma tendsto_measure_sigmaFiniteSetGE (μ ν : Measure α) [IsFiniteMeasure ν] :
    Tendsto (fun n ↦ ν (μ.sigmaFiniteSetGE ν n)) atTop
      (𝓝 (⨆ (s) (_ : MeasurableSet s) (_ : SigmaFinite (μ.restrict s)), ν s)) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le ?_
    tendsto_const_nhds (measure_sigmaFiniteSetGE_ge μ ν) (measure_sigmaFiniteSetGE_le μ ν)
  nth_rewrite 2 [← tsub_zero (⨆ (s) (_ : MeasurableSet s) (_ : SigmaFinite (μ.restrict s)), ν s)]
  refine ENNReal.Tendsto.sub tendsto_const_nhds ?_ (Or.inr ENNReal.zero_ne_top)
  simp only [one_div]
  exact ENNReal.tendsto_inv_nat_nhds_zero

/-- A measurable set such that `μ.restrict (μ.sigmaFiniteSetWRT' ν)` is sigma-finite and
`ν (μ.sigmaFiniteSetWRT' ν)` has maximal measure among such sets. -/
-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/-
**MeasureTheory.Measure.sigmaFiniteSetWRT'** 是 Mathlib 中的一个定义，位于命名空间 `MeasureThe
ory.Measure`。
形式化陈述：{α : Type u_1} →   {mα : MeasurableSpace α} →     MeasureTheory.Measure α 
→ (ν : MeasureTheory.Measure α) → [MeasureTheory.IsFiniteMeasure ν] → Set α
参数：ν : MeasureTheory.Measure α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def Measure.sigmaFiniteSetWRT' (μ ν : Measure α) [IsFiniteMeasure ν] : Set α :=
  ⋃ n, μ.sigmaFiniteSetGE ν n
/-
**MeasureTheory.measurableSet_sigmaFiniteSetWRT'** 是 Mathlib 中的一个引理，位于命名空间 `Meas
ureTheory`。
形式化陈述：measurableSet_sigmaFiniteSetWRT' [IsFiniteMeasure ν] : MeasurableSet (μ.si
gmaFiniteSetWRT' ν)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.iUnion`：∀ {α : Type u_1} {ι : Sort u_6} {m : MeasurableSpa
ce α} [Countable ι] ⦃f : ι → Set α⦄,   (∀ (b : ι), MeasurableSet (f b)) → Measur
ableSet (⋃…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用引理 `MeasureTheory.measurableSet_sigmaFiniteSetGE`：measurableSet_sigmaFiniteS
etGE [IsFiniteMeasure ν] (n : Nat) : MeasurableSet (μ.sigmaFiniteSetGE ν n)
-/
lemma measurableSet_sigmaFiniteSetWRT' [IsFiniteMeasure ν] :
    MeasurableSet (μ.sigmaFiniteSetWRT' ν) :=
  MeasurableSet.iUnion measurableSet_sigmaFiniteSetGE
/-
**MeasureTheory.sigmaFinite_restrict_sigmaFiniteSetWRT'** 是 Mathlib 中的一个引理，位于命名空
间 `MeasureTheory`。
形式化陈述：sigmaFinite_restrict_sigmaFiniteSetWRT' (μ ν : Measure α) [IsFiniteMeasure
 ν] : SigmaFinite (μ.restrict (μ.sigmaFiniteSetWRT' ν))
参数：μ ν : Measure α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.sigmaFinite_restrict_sigmaFiniteSetGE`：sigmaFinite_restric
t_sigmaFiniteSetGE (μ ν : Measure α) [IsFiniteMeasure ν] (n : Nat) : SigmaFinite
 (μ.restrict (μ.sigmaFiniteSetGE ν n))
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Nat.pairEquiv_symm_apply`：⇑Nat.pairEquiv.symm = Nat.unpair
· 使用定理 `MeasureTheory.Measure.restrict_apply'`：restrict_apply' (hs : MeasurableS
et s) : μ.restrict s t = μ (t inter s)
· 使用引理 `MeasureTheory.measurableSet_sigmaFiniteSetWRT'`：measurableSet_sigmaFinit
eSetWRT' [IsFiniteMeasure ν] : MeasurableSet (μ.sigmaFiniteSetWRT' ν)
· 使用定理 `Set.compl_inter_self`：compl_inter_self (s : Set α) : sᶜ inter s = ∅
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.measurableSet_sigmaFiniteSetGE`：measurableSet_sigmaFiniteS
etGE [IsFiniteMeasure ν] (n : Nat) : MeasurableSet (μ.sigmaFiniteSetGE ν n)
· 使用定理 `MeasureTheory.measure_spanningSets_lt_top`：measure_spanningSets_lt_top (
μ : Measure α) [SigmaFinite μ] (i : Nat) : μ (spanningSets μ i) < ∞
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.union_iUnion`：union_iUnion [Nonempty ι] (s : Set β) (t : ι -> Set β)
 : (s union ⋃ i, t i) = ⋃ i, s union t i
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Set.iUnion_unpair`：iUnion_unpair {α} (f : Nat -> Nat -> Set α) : ⋃ n : N
at, f n.unpair.1 n.unpair.2 = ⋃ (i : Nat) (j : Nat), f i j
· 使用引理 `Set.iUnion_congr`：iUnion_congr {s t : ι -> Set α} (h : forall i, s i = t
 i) : ⋃ i, s i = ⋃ i, t i
· 使用定理 `Set.iUnion_inter`：iUnion_inter (s : Set β) (t : ι -> Set β) : (⋃ i, t i)
 inter s = ⋃ i, t i inter s
· 使用定理 `MeasureTheory.iUnion_spanningSets`：iUnion_spanningSets (μ : Measure α) [
SigmaFinite μ] : ⋃ i : Nat, spanningSets μ i = univ
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `Set.compl_union_self`：compl_union_self (s : Set α) : sᶜ union s = univ
· 使用定理 `MeasureTheory.Measure.FiniteSpanningSetsIn.sigmaFinite`：∀ {α : Type u_1}
 {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {C : Set (Set α)}   (h :
 μ.FiniteSpanningSetsIn C), MeasureTheory.Si…
-/
lemma sigmaFinite_restrict_sigmaFiniteSetWRT' (μ ν : Measure α) [IsFiniteMeasure ν] :
    SigmaFinite (μ.restrict (μ.sigmaFiniteSetWRT' ν)) := by
  have := sigmaFinite_restrict_sigmaFiniteSetGE μ ν
  let f : ℕ × ℕ → Set α := fun p : ℕ × ℕ ↦ (μ.sigmaFiniteSetWRT' ν)ᶜ
    ∪ (spanningSets (μ.restrict (μ.sigmaFiniteSetGE ν p.1)) p.2 ∩ (μ.sigmaFiniteSetGE ν p.1))
  suffices (μ.restrict (μ.sigmaFiniteSetWRT' ν)).FiniteSpanningSetsIn (Set.range f) from
    this.sigmaFinite
  let e : ℕ ≃ ℕ × ℕ := Nat.pairEquiv.symm
  refine ⟨fun n ↦ f (e n), fun _ ↦ by simp, fun n ↦ ?_, ?_⟩
  · simp only [Nat.pairEquiv_symm_apply, measure_union_lt_top_iff, f, e]
    rw [Measure.restrict_apply' measurableSet_sigmaFiniteSetWRT', Set.compl_inter_self,
      Measure.restrict_apply' measurableSet_sigmaFiniteSetWRT']
    simp only [measure_empty, ENNReal.zero_lt_top, true_and]
    refine (measure_mono Set.inter_subset_left).trans_lt ?_
    rw [← Measure.restrict_apply' (measurableSet_sigmaFiniteSetGE _)]
    exact measure_spanningSets_lt_top _ _
  · simp only [Nat.pairEquiv_symm_apply, f, e]
    rw [← Set.union_iUnion]
    suffices ⋃ n, (spanningSets (μ.restrict (μ.sigmaFiniteSetGE ν (Nat.unpair n).1)) n.unpair.2
        ∩ μ.sigmaFiniteSetGE ν n.unpair.1) = μ.sigmaFiniteSetWRT' ν by
      rw [this, Set.compl_union_self]
    calc ⋃ n, (spanningSets (μ.restrict (μ.sigmaFiniteSetGE ν (Nat.unpair n).1)) n.unpair.2
        ∩ μ.sigmaFiniteSetGE ν n.unpair.1)
      = ⋃ n, ⋃ m, (spanningSets (μ.restrict (μ.sigmaFiniteSetGE ν n)) m
            ∩ μ.sigmaFiniteSetGE ν n) :=
          Set.iUnion_unpair (fun n m ↦ spanningSets (μ.restrict (μ.sigmaFiniteSetGE ν n)) m
            ∩ μ.sigmaFiniteSetGE ν n)
    _ = ⋃ n, μ.sigmaFiniteSetGE ν n := by
        refine Set.iUnion_congr (fun n ↦ ?_)
        rw [← Set.iUnion_inter, iUnion_spanningSets, Set.univ_inter]
    _ = μ.sigmaFiniteSetWRT' ν := rfl

/-- `μ.sigmaFiniteSetWRT' ν` has maximal `ν`-measure among all measurable sets `s` with sigma-finite
`μ.restrict s`. -/
/-
**MeasureTheory.measure_sigmaFiniteSetWRT'** 是 Mathlib 中的一个引理，位于命名空间 `MeasureThe
ory`。
形式化陈述：measure_sigmaFiniteSetWRT' (μ ν : Measure α) [IsFiniteMeasure ν] : ν (μ.si
gmaFiniteSetWRT' ν) = ⨆ (s) (_ : MeasurableSet s) (_ : SigmaFinite (μ.restrict s
)), ν s
参数：μ ν : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用引理 `MeasureTheory.sigmaFinite_restrict_sigmaFiniteSetWRT'`：sigmaFinite_restr
ict_sigmaFiniteSetWRT' (μ ν : Measure α) [IsFiniteMeasure ν] : SigmaFinite (μ.re
strict (μ.sigmaFiniteSetWRT' ν))
· 使用定理 `le_iSup₂`：le_iSup₂ {f : forall i, κ i -> α} (i : ι) (j : κ i) : f i j <=
 ⨆ (i) (j), f i j
· 使用引理 `MeasureTheory.measurableSet_sigmaFiniteSetWRT'`：measurableSet_sigmaFinit
eSetWRT' [IsFiniteMeasure ν] : MeasurableSet (μ.sigmaFiniteSetWRT' ν)
· 使用定理 `le_of_tendsto'`：le_of_tendsto' {x : Filter β} [hx : NeBot x] (lim : Tend
sto f x (𝓝 a)) (h : forall c, f c <= b) : a <= b
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `MeasureTheory.tendsto_measure_sigmaFiniteSetGE`：tendsto_measure_sigmaFin
iteSetGE (μ ν : Measure α) [IsFiniteMeasure ν] : Tendsto (fun n => ν (μ.sigmaFin
iteSetGE ν n)) atTop (𝓝 (⨆ (s) (_ : …
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.subset_iUnion`：subset_iUnion : forall (s : ι -> Set β) (i : ι), s i 
subseteq ⋃ i, s i

--- 原说明 ---
`μ.sigmaFiniteSetWRT' ν` has maximal `ν`-measure among all measurable sets `s` w
ith sigma-finite
`μ.restrict s`.
-/
lemma measure_sigmaFiniteSetWRT' (μ ν : Measure α) [IsFiniteMeasure ν] :
    ν (μ.sigmaFiniteSetWRT' ν)
      = ⨆ (s) (_ : MeasurableSet s) (_ : SigmaFinite (μ.restrict s)), ν s := by
  apply le_antisymm
  · refine (le_iSup (f := fun _ ↦ _)
      (sigmaFinite_restrict_sigmaFiniteSetWRT' μ ν)).trans ?_
    exact le_iSup₂ (f := fun s _ ↦ ⨆ (_ : SigmaFinite (μ.restrict s)), ν s) (μ.sigmaFiniteSetWRT' ν)
      measurableSet_sigmaFiniteSetWRT'
  · exact le_of_tendsto' (tendsto_measure_sigmaFiniteSetGE μ ν)
      (fun _ ↦ measure_mono (Set.subset_iUnion _ _))

/-- Auxiliary lemma for `measure_eq_top_of_subset_compl_sigmaFiniteSetWRT'`. -/
/-
**MeasureTheory.measure_eq_top_of_subset_compl_sigmaFiniteSetWRT'_of_measurableS
et** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：∀ {α : Type u_1} {mα : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} 
{s : Set α}   [inst : MeasureTheory.IsFiniteMeasure ν], MeasurableSet s → s ⊆ (μ
.sigmaFiniteSetWRT' ν)ᶜ → ν s ≠ 0 → μ s = ⊤
参数：μ.sigmaFiniteSetWRT' ν。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measure_union`：measure_union (hd : Disjoint s₁ s₂) (h : Me
asurableSet s₂) : μ (s₁ union s₂) = μ s₁ + μ s₂
· 使用定理 `Disjoint.mono_right`：Disjoint.mono_right (h : b <= c) : Disjoint a c -> 
Disjoint a b
· 使用定理 `disjoint_compl_right`：disjoint_compl_right : Disjoint a aᶜ
· 使用定理 `ENNReal.lt_add_right`：lt_add_right (ha : a != ∞) (hb : b != 0) : a < a +
 b
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `MeasureTheory.measure_sigmaFiniteSetWRT'`：measure_sigmaFiniteSetWRT' (μ 
ν : Measure α) [IsFiniteMeasure ν] : ν (μ.sigmaFiniteSetWRT' ν) = ⨆ (s) (_ : Mea
surableSet s) (_ : SigmaFinite…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用引理 `MeasureTheory.sigmaFinite_restrict_sigmaFiniteSetWRT'`：sigmaFinite_restr
ict_sigmaFiniteSetWRT' (μ ν : Measure α) [IsFiniteMeasure ν] : SigmaFinite (μ.re
strict (μ.sigmaFiniteSetWRT' ν))
· 使用定理 `MeasureTheory.instSigmaFiniteRestrictUnionSet`：∀ {α : Type u_1} {m0 : Me
asurableSpace α} {μ : MeasureTheory.Measure α} {s t : Set α}   [MeasureTheory.Si
gmaFinite (μ.restrict s)] [MeasureT…
· 使用定理 `le_iSup₂`：le_iSup₂ {f : forall i, κ i -> α} (i : ι) (j : κ i) : f i j <=
 ⨆ (i) (j), f i j
· 使用定理 `MeasurableSet.union`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∪ s₂)
· 使用引理 `MeasureTheory.measurableSet_sigmaFiniteSetWRT'`：measurableSet_sigmaFinit
eSetWRT' [IsFiniteMeasure ν] : MeasurableSet (μ.sigmaFiniteSetWRT' ν)
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasureTheory.Restrict.isFiniteMeasure`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {s : Set α} (μ : MeasureTheory.Measure α) [hs : Fact (μ s < ⊤)],   Mea
sureTheory.IsFiniteMeasure (…

--- 原说明 ---
Auxiliary lemma for `measure_eq_top_of_subset_compl_sigmaFiniteSetWRT'`.
-/
lemma measure_eq_top_of_subset_compl_sigmaFiniteSetWRT'_of_measurableSet [IsFiniteMeasure ν]
    (hs : MeasurableSet s) (hs_subset : s ⊆ (μ.sigmaFiniteSetWRT' ν)ᶜ) (hνs : ν s ≠ 0) :
    μ s = ∞ := by
  suffices ¬ SigmaFinite (μ.restrict s) by
    by_contra h
    have h_lt_top : Fact (μ s < ∞) := ⟨Ne.lt_top h⟩
    exact this inferInstance
  intro hsσ
  have h_lt : ν (μ.sigmaFiniteSetWRT' ν) < ν (μ.sigmaFiniteSetWRT' ν ∪ s) := by
    rw [measure_union _ hs]
    · exact ENNReal.lt_add_right (measure_ne_top _ _) hνs
    · exact disjoint_compl_right.mono_right hs_subset
  have h_le : ν (μ.sigmaFiniteSetWRT' ν ∪ s) ≤ ν (μ.sigmaFiniteSetWRT' ν) := by
    conv_rhs => rw [measure_sigmaFiniteSetWRT']
    refine (le_iSup
      (f := fun (_ : SigmaFinite (μ.restrict (μ.sigmaFiniteSetWRT' ν ∪ s))) ↦ _) ?_).trans ?_
    · have := sigmaFinite_restrict_sigmaFiniteSetWRT' μ ν
      infer_instance
    · exact le_iSup₂ (f := fun s _ ↦ ⨆ (_ : SigmaFinite (μ.restrict _)), ν s)
        (μ.sigmaFiniteSetWRT' ν ∪ s) (measurableSet_sigmaFiniteSetWRT'.union hs)
  exact h_lt.not_ge h_le

/-- For all sets `s` in `(μ.sigmaFiniteSetWRT ν)ᶜ`, if `ν s ≠ 0` then `μ s = ∞`. -/
/-
**MeasureTheory.measure_eq_top_of_subset_compl_sigmaFiniteSetWRT'** 是 Mathlib 中的
一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：measure_eq_top_of_subset_compl_sigmaFiniteSetWRT'_of_measurableSet [IsFini
teMeasure ν] (hs : MeasurableSet s) (hs_subset : s subseteq (μ.sigmaFiniteSetWRT
' ν)ᶜ) (hνs : ν s != 0) : μ s = ∞
参数：hs : MeasurableSet s；hs_subset : s subseteq (μ.sigmaFiniteSetWRT' ν)ᶜ；hνs : ν
 s != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measure_eq_iInf`：measure_eq_iInf (s : Set α) : μ s = ⨅ (t)
 (_ : s subseteq t) (_ : MeasurableSet t), μ t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `MeasureTheory.measure_eq_top_of_subset_compl_sigmaFiniteSetWRT'_of_measu
rableSet`：∀ {α : Type u_1} {mα : MeasurableSpace α} {μ ν : MeasureTheory.Measure
 α} {s : Set α}   [inst : MeasureTheory.IsFiniteMeasure ν], Measurable…
· 使用定理 `MeasureTheory.measure_mono_null`：measure_mono_null (h : s subseteq t) (h
t : μ t = 0) : μ s = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.subset_inter`：subset_inter {s t r : Set α} (rs : r subseteq s) (rt :
 r subseteq t) : r subseteq s inter t
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用引理 `MeasureTheory.measurableSet_sigmaFiniteSetWRT'`：measurableSet_sigmaFinit
eSetWRT' [IsFiniteMeasure ν] : MeasurableSet (μ.sigmaFiniteSetWRT' ν)
· 使用定理 `MeasureTheory.measure_mono_top`：measure_mono_top (h : s₁ subseteq s₂) (h
₁ : μ s₁ = ∞) : μ s₂ = ∞
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s

--- 原说明 ---
For all sets `s` in `(μ.sigmaFiniteSetWRT ν)ᶜ`, if `ν s ≠ 0` then `μ s = ∞`.
-/
lemma measure_eq_top_of_subset_compl_sigmaFiniteSetWRT' [IsFiniteMeasure ν]
    (hs_subset : s ⊆ (μ.sigmaFiniteSetWRT' ν)ᶜ) (hνs : ν s ≠ 0) :
    μ s = ∞ := by
  rw [measure_eq_iInf]
  simp_rw [iInf_eq_top]
  suffices ∀ t, t ⊆ (μ.sigmaFiniteSetWRT' ν)ᶜ → s ⊆ t → MeasurableSet t → μ t = ∞ by
    intro t hts ht
    suffices μ (t ∩ (μ.sigmaFiniteSetWRT' ν)ᶜ) = ∞ from
      measure_mono_top Set.inter_subset_left this
    have hs_subset_t : s ⊆ t ∩ (μ.sigmaFiniteSetWRT' ν)ᶜ := Set.subset_inter hts hs_subset
    exact this (t ∩ (μ.sigmaFiniteSetWRT' ν)ᶜ) Set.inter_subset_right hs_subset_t
      (ht.inter measurableSet_sigmaFiniteSetWRT'.compl)
  intro t ht_subset hst ht
  refine measure_eq_top_of_subset_compl_sigmaFiniteSetWRT'_of_measurableSet ht ht_subset ?_
  exact fun hνt ↦ hνs (measure_mono_null hst hνt)

end IsFiniteMeasure

section SFinite

/-- For all sets `s` in `(μ.sigmaFiniteSetWRT ν)ᶜ`, if `ν s ≠ 0` then `μ s = ∞`. -/
/-
**MeasureTheory.measure_eq_top_of_subset_compl_sigmaFiniteSetWRT** 是 Mathlib 中的一
个引理，位于命名空间 `MeasureTheory`。
形式化陈述：measure_eq_top_of_subset_compl_sigmaFiniteSetWRT [SFinite ν] (hs_subset : 
s subseteq (μ.sigmaFiniteSetWRT ν)ᶜ) (hνs : ν s != 0) : μ s = ∞
参数：hs_subset : s subseteq (μ.sigmaFiniteSetWRT ν)ᶜ；hνs : ν s != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.exists_isFiniteMeasure_absolutelyContinuous`：exists_isFini
teMeasure_absolutelyContinuous [SFinite μ] : exists ν : Measure α, IsFiniteMeasu
re ν ∧ μ ≪ ν ∧ ν ≪ μ
· 使用引理 `MeasureTheory.measurableSet_sigmaFiniteSetWRT'`：measurableSet_sigmaFinit
eSetWRT' [IsFiniteMeasure ν] : MeasurableSet (μ.sigmaFiniteSetWRT' ν)
· 使用引理 `MeasureTheory.sigmaFinite_restrict_sigmaFiniteSetWRT'`：sigmaFinite_restr
ict_sigmaFiniteSetWRT' (μ ν : Measure α) [IsFiniteMeasure ν] : SigmaFinite (μ.re
strict (μ.sigmaFiniteSetWRT' ν))
· 使用引理 `MeasureTheory.measure_eq_top_of_subset_compl_sigmaFiniteSetWRT'`：measure
_eq_top_of_subset_compl_sigmaFiniteSetWRT'_of_measurableSet [IsFiniteMeasure ν] 
(hs : MeasurableSet s) (hs_subset : s subseteq (μ.sig…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `MeasureTheory.Measure.sigmaFiniteSetWRT.eq_1`：∀ {α : Type u_1} {mα : Mea
surableSpace α} (μ ν : MeasureTheory.Measure α),   μ.sigmaFiniteSetWRT ν =     i
f h : ∃ s, MeasurableSet s ∧ Measu…

--- 原说明 ---
For all sets `s` in `(μ.sigmaFiniteSetWRT ν)ᶜ`, if `ν s ≠ 0` then `μ s = ∞`.
-/
lemma measure_eq_top_of_subset_compl_sigmaFiniteSetWRT [SFinite ν]
    (hs_subset : s ⊆ (μ.sigmaFiniteSetWRT ν)ᶜ) (hνs : ν s ≠ 0) :
    μ s = ∞ := by
  have ⟨ν', hν', hνν', _⟩ := exists_isFiniteMeasure_absolutelyContinuous ν
  have h : ∃ s : Set α, MeasurableSet s ∧ SigmaFinite (μ.restrict s)
      ∧ (∀ t ⊆ sᶜ, ν t ≠ 0 → μ t = ∞) := by
    refine ⟨μ.sigmaFiniteSetWRT' ν', measurableSet_sigmaFiniteSetWRT',
      sigmaFinite_restrict_sigmaFiniteSetWRT' _ _,
      fun t ht_subset hνt ↦ measure_eq_top_of_subset_compl_sigmaFiniteSetWRT' ht_subset ?_⟩
    exact fun hν't ↦ hνt (hνν' hν't)
  rw [Measure.sigmaFiniteSetWRT, dif_pos h] at hs_subset
  exact h.choose_spec.2.2 s hs_subset hνs
/-
**MeasureTheory.restrict_compl_sigmaFiniteSetWRT** 是 Mathlib 中的一个引理，位于命名空间 `Meas
ureTheory`。
形式化陈述：restrict_compl_sigmaFiniteSetWRT [SFinite ν] (hμν : μ ≪ ν) : μ.restrict (μ
.sigmaFiniteSetWRT ν)ᶜ = ∞ • ν.restrict (μ.sigmaFiniteSetWRT ν)ᶜ
参数：hμν : μ ≪ ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_apply'`：restrict_apply' (hs : MeasurableS
et s) : μ.restrict s t = μ (t inter s)
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用引理 `MeasureTheory.measurableSet_sigmaFiniteSetWRT`：measurableSet_sigmaFinite
SetWRT : MeasurableSet (μ.sigmaFiniteSetWRT ν)
· 使用定理 `MeasureTheory.Measure.smul_apply`：smul_apply {_m : MeasurableSpace α} (c
 : R) (μ : Measure α) (s : Set α) : (c • μ) s = c • μ s
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `ENNReal.top_mul`：∀ {a : ENNReal}, a ≠ 0 → ⊤ * a = ⊤
· 使用引理 `MeasureTheory.measure_eq_top_of_subset_compl_sigmaFiniteSetWRT`：measure_
eq_top_of_subset_compl_sigmaFiniteSetWRT [SFinite ν] (hs_subset : s subseteq (μ.
sigmaFiniteSetWRT ν)ᶜ) (hνs : ν s != 0) : μ s = ∞
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
-/
lemma restrict_compl_sigmaFiniteSetWRT [SFinite ν] (hμν : μ ≪ ν) :
    μ.restrict (μ.sigmaFiniteSetWRT ν)ᶜ = ∞ • ν.restrict (μ.sigmaFiniteSetWRT ν)ᶜ := by
  ext s
  rw [Measure.restrict_apply' measurableSet_sigmaFiniteSetWRT.compl,
    Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply' measurableSet_sigmaFiniteSetWRT.compl]
  by_cases hνs : ν (s ∩ (μ.sigmaFiniteSetWRT ν)ᶜ) = 0
  · rw [hνs, mul_zero]
    exact hμν hνs
  · rw [ENNReal.top_mul hνs, measure_eq_top_of_subset_compl_sigmaFiniteSetWRT
      Set.inter_subset_right hνs]

end SFinite

@[simp]
/-
**MeasureTheory.measure_compl_sigmaFiniteSetWRT** 是 Mathlib 中的一个引理，位于命名空间 `Measu
reTheory`。
形式化陈述：measure_compl_sigmaFiniteSetWRT (hμν : μ ≪ ν) [SigmaFinite μ] [SFinite ν] 
: ν (μ.sigmaFiniteSetWRT ν)ᶜ = 0
参数：hμν : μ ≪ ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.measure_eq_top_of_subset_compl_sigmaFiniteSetWRT`：measure_
eq_top_of_subset_compl_sigmaFiniteSetWRT [SFinite ν] (hs_subset : s subseteq (μ.
sigmaFiniteSetWRT ν)ᶜ) (hνs : ν s != 0) : μ s = ∞
· 使用定理 `subset_rfl`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorde
r α] {a : α}, a ⊆ a
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `ENNReal.top_ne_zero`：⊤ ≠ 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.iSup_restrict_spanningSets`：iSup_restrict_spanning
Sets [SigmaFinite μ] (s : Set α) : ⨆ i, μ.restrict (spanningSets μ i) s = μ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.Measure.restrict_apply'`：restrict_apply' (hs : MeasurableS
et s) : μ.restrict s t = μ (t inter s)
· 使用定理 `MeasureTheory.measurableSet_spanningSets`：measurableSet_spanningSets (μ 
: Measure α) [SigmaFinite μ] (i : Nat) : MeasurableSet (spanningSets μ i)
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `MeasureTheory.measure_spanningSets_lt_top`：measure_spanningSets_lt_top (
μ : Measure α) [SigmaFinite μ] (i : Nat) : μ (spanningSets μ i) < ∞
-/
lemma measure_compl_sigmaFiniteSetWRT (hμν : μ ≪ ν) [SigmaFinite μ] [SFinite ν] :
    ν (μ.sigmaFiniteSetWRT ν)ᶜ = 0 := by
  have h : ν (μ.sigmaFiniteSetWRT ν)ᶜ ≠ 0 → μ (μ.sigmaFiniteSetWRT ν)ᶜ = ∞ :=
    measure_eq_top_of_subset_compl_sigmaFiniteSetWRT subset_rfl
  by_contra h0
  refine ENNReal.top_ne_zero ?_
  rw [← h h0, ← Measure.iSup_restrict_spanningSets]
  simp_rw [Measure.restrict_apply' (measurableSet_spanningSets μ _), ENNReal.iSup_eq_zero]
  intro i
  by_contra h_ne_zero
  have h_zero_top := measure_eq_top_of_subset_compl_sigmaFiniteSetWRT
    (Set.inter_subset_left : (μ.sigmaFiniteSetWRT ν)ᶜ ∩ spanningSets μ i ⊆ _) ?_
  swap; · exact fun h ↦ h_ne_zero (hμν h)
  refine absurd h_zero_top (ne_of_lt ?_)
  exact (measure_mono Set.inter_subset_right).trans_lt (measure_spanningSets_lt_top μ i)

section SigmaFiniteSet

/-- A measurable set such that `μ.restrict μ.sigmaFiniteSet` is sigma-finite,
  and for all measurable sets `s ⊆ μ.sigmaFiniteSetᶜ`, either `μ s = 0` or `μ s = ∞`. -/
-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/-
**MeasureTheory.Measure.sigmaFiniteSet** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.
Measure`。
形式化陈述：{α : Type u_1} → {mα : MeasurableSpace α} → MeasureTheory.Measure α → Set 
α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def Measure.sigmaFiniteSet (μ : Measure α) : Set α := μ.sigmaFiniteSetWRT μ

@[measurability]
/-
**MeasureTheory.measurableSet_sigmaFiniteSet** 是 Mathlib 中的一个引理，位于命名空间 `MeasureT
heory`。
形式化陈述：measurableSet_sigmaFiniteSet : MeasurableSet μ.sigmaFiniteSet
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.measurableSet_sigmaFiniteSetWRT`：measurableSet_sigmaFinite
SetWRT : MeasurableSet (μ.sigmaFiniteSetWRT ν)
-/
lemma measurableSet_sigmaFiniteSet : MeasurableSet μ.sigmaFiniteSet :=
  measurableSet_sigmaFiniteSetWRT
/-
**MeasureTheory.measure_eq_zero_or_top_of_subset_compl_sigmaFiniteSet** 是 Mathli
b 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：measure_eq_zero_or_top_of_subset_compl_sigmaFiniteSet [SFinite μ] (ht_subs
et : t subseteq μ.sigmaFiniteSetᶜ) : μ t = 0 ∨ μ t = ∞
参数：ht_subset : t subseteq μ.sigmaFiniteSetᶜ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用引理 `MeasureTheory.measure_eq_top_of_subset_compl_sigmaFiniteSetWRT`：measure_
eq_top_of_subset_compl_sigmaFiniteSetWRT [SFinite ν] (hs_subset : s subseteq (μ.
sigmaFiniteSetWRT ν)ᶜ) (hνs : ν s != 0) : μ s = ∞
-/
lemma measure_eq_zero_or_top_of_subset_compl_sigmaFiniteSet [SFinite μ]
    (ht_subset : t ⊆ μ.sigmaFiniteSetᶜ) :
    μ t = 0 ∨ μ t = ∞ := by
  rw [or_iff_not_imp_left]
  exact measure_eq_top_of_subset_compl_sigmaFiniteSetWRT ht_subset

/-- The measure `μ.restrict μ.sigmaFiniteSetᶜ` takes only two values: 0 and ∞ . -/
/-
**MeasureTheory.restrict_compl_sigmaFiniteSet_eq_zero_or_top** 是 Mathlib 中的一个引理，
位于命名空间 `MeasureTheory`。
形式化陈述：restrict_compl_sigmaFiniteSet_eq_zero_or_top (μ : Measure α) [SFinite μ] (
s : Set α) : μ.restrict μ.sigmaFiniteSetᶜ s = 0 ∨ μ.restrict μ.sigmaFiniteSetᶜ s
 = ∞
参数：μ : Measure α；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_apply'`：restrict_apply' (hs : MeasurableS
et s) : μ.restrict s t = μ (t inter s)
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用引理 `MeasureTheory.measurableSet_sigmaFiniteSet`：measurableSet_sigmaFiniteSet
 : MeasurableSet μ.sigmaFiniteSet
· 使用引理 `MeasureTheory.measure_eq_zero_or_top_of_subset_compl_sigmaFiniteSet`：mea
sure_eq_zero_or_top_of_subset_compl_sigmaFiniteSet [SFinite μ] (ht_subset : t su
bseteq μ.sigmaFiniteSetᶜ) : μ t = 0 ∨ μ t = ∞
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t

--- 原说明 ---
The measure `μ.restrict μ.sigmaFiniteSetᶜ` takes only two values: 0 and ∞ .
-/
lemma restrict_compl_sigmaFiniteSet_eq_zero_or_top (μ : Measure α) [SFinite μ] (s : Set α) :
    μ.restrict μ.sigmaFiniteSetᶜ s = 0 ∨ μ.restrict μ.sigmaFiniteSetᶜ s = ∞ := by
  rw [Measure.restrict_apply' measurableSet_sigmaFiniteSet.compl]
  exact measure_eq_zero_or_top_of_subset_compl_sigmaFiniteSet Set.inter_subset_right

/-- The restriction of an s-finite measure `μ` to `μ.sigmaFiniteSet` is sigma-finite. -/
/-
**MeasureTheory.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The restriction of an s-finite measure `μ` to `μ.sigmaFiniteSet` is sigma-finite
.
-/
instance : SigmaFinite (μ.restrict μ.sigmaFiniteSet) := by
  rw [Measure.sigmaFiniteSet]
  infer_instance
/-
**MeasureTheory.sigmaFinite_of_measure_compl_sigmaFiniteSet_eq_zero** 是 Mathlib 
中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：sigmaFinite_of_measure_compl_sigmaFiniteSet_eq_zero (h : μ μ.sigmaFiniteSe
tᶜ = 0) : SigmaFinite μ
参数：h : μ μ.sigmaFiniteSetᶜ = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.restrict_add_restrict_compl`：restrict_add_restrict
_compl (hs : MeasurableSet s) : μ.restrict s + μ.restrict sᶜ = μ
· 使用引理 `MeasureTheory.measurableSet_sigmaFiniteSet`：measurableSet_sigmaFiniteSet
 : MeasurableSet μ.sigmaFiniteSet
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.restrict_eq_zero`：restrict_eq_zero : μ.restrict s 
= 0 ↔ μ s = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `MeasureTheory.instSigmaFiniteRestrictSigmaFiniteSet`：∀ {α : Type u_1} {m
α : MeasurableSpace α} {μ : MeasureTheory.Measure α},   MeasureTheory.SigmaFinit
e (μ.restrict μ.sigmaFiniteSet)
-/
lemma sigmaFinite_of_measure_compl_sigmaFiniteSet_eq_zero (h : μ μ.sigmaFiniteSetᶜ = 0) :
    SigmaFinite μ := by
  rw [← Measure.restrict_add_restrict_compl (μ := μ) (measurableSet_sigmaFiniteSet (μ := μ)),
    Measure.restrict_eq_zero.mpr h, add_zero]
  infer_instance

@[simp]
/-
**MeasureTheory.measure_compl_sigmaFiniteSet** 是 Mathlib 中的一个引理，位于命名空间 `MeasureT
heory`。
形式化陈述：measure_compl_sigmaFiniteSet (μ : Measure α) [SigmaFinite μ] : μ μ.sigmaFi
niteSetᶜ = 0
参数：μ : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.measure_compl_sigmaFiniteSetWRT`：measure_compl_sigmaFinite
SetWRT (hμν : μ ≪ ν) [SigmaFinite μ] [SFinite ν] : ν (μ.sigmaFiniteSetWRT ν)ᶜ = 
0
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.rfl`：∀ {α : Type u_1} {mα : M
easurableSpace α} {μ : MeasureTheory.Measure α}, μ.AbsolutelyContinuous μ
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
-/
lemma measure_compl_sigmaFiniteSet (μ : Measure α) [SigmaFinite μ] : μ μ.sigmaFiniteSetᶜ = 0 :=
  measure_compl_sigmaFiniteSetWRT Measure.AbsolutelyContinuous.rfl

/-- An s-finite measure `μ` is sigma-finite iff `μ μ.sigmaFiniteSetᶜ = 0`. -/
/-
**MeasureTheory.measure_compl_sigmaFiniteSet_eq_zero_iff_sigmaFinite** 是 Mathlib
 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：measure_compl_sigmaFiniteSet_eq_zero_iff_sigmaFinite (μ : Measure α) : μ μ
.sigmaFiniteSetᶜ = 0 ↔ SigmaFinite μ
参数：μ : Measure α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.sigmaFinite_of_measure_compl_sigmaFiniteSet_eq_zero`：sigma
Finite_of_measure_compl_sigmaFiniteSet_eq_zero (h : μ μ.sigmaFiniteSetᶜ = 0) : S
igmaFinite μ
· 使用引理 `MeasureTheory.measure_compl_sigmaFiniteSet`：measure_compl_sigmaFiniteSet
 (μ : Measure α) [SigmaFinite μ] : μ μ.sigmaFiniteSetᶜ = 0

--- 原说明 ---
An s-finite measure `μ` is sigma-finite iff `μ μ.sigmaFiniteSetᶜ = 0`.
-/
lemma measure_compl_sigmaFiniteSet_eq_zero_iff_sigmaFinite (μ : Measure α) :
    μ μ.sigmaFiniteSetᶜ = 0 ↔ SigmaFinite μ :=
  ⟨sigmaFinite_of_measure_compl_sigmaFiniteSet_eq_zero, fun _ ↦ measure_compl_sigmaFiniteSet μ⟩

end SigmaFiniteSet

end MeasureTheory

