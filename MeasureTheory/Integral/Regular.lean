/-
Copyright (c) 2025 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Topology.UrysohnsLemma

/-!
# Integrals of continuous functions with respect to regular measures

When a measure is regular, one may express the measure of compact sets and of open sets
in terms of the integral of continuous functions equal to 1 on the compact set, or to 0 outside
of the open set respectively.
-/

public section

open Filter Set MeasureTheory Measure

/-- In a locally compact regular space with an inner regular measure, the measure of a compact
set `k` is the infimum of the integrals of compactly supported functions equal to `1` on `k`. -/
/-
**IsCompact.measure_eq_biInf_integral_hasCompactSupport** 是 Mathlib 中的一个引理，位于命名空
间 ``。
形式化陈述：IsCompact.measure_eq_biInf_integral_hasCompactSupport {X : Type*} [Topolog
icalSpace X] [MeasurableSpace X] [BorelSpace X] {k : Set X} (hk : IsCompact k) (
μ : Measure X) [IsFiniteMeasureOnCompacts μ] [InnerRegularCompactLTTop μ] [Local
lyCompactSpace X] [RegularSpace X] : μ k = ⨅ (f : X -> Real) (_ : Continuous f) 
(_ : HasCompactSupport f) (_ : EqOn f 1 k) (_ : 0 <= f), ENNReal.ofReal (∫ x, f 
x ∂μ)
参数：hk : IsCompact k；μ : Measure X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `MeasureTheory.Integrable.measure_le_integral`：∀ {X : Type u_1} {mX : Mea
surableSpace X} {μ : MeasureTheory.Measure X} {f : X → ℝ},   MeasureTheory.Integ
rable f μ →     0 ≤ᵐ[μ] f → ∀ {s :…
· 使用定理 `Continuous.integrable_of_hasCompactSupport`：Continuous.integrable_of_has
CompactSupport (hf : Continuous f) (hcf : HasCompactSupport f) : Integrable f μ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_of_forall_gt`：∀ {α : Type u_2} [inst : LinearOrder α] {a b : α}, (∀ (
c : α), a < c → b < c) → b ≤ a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `IsCompact.exists_isOpen_lt_of_lt`：∀ {α : Type u_1} [inst : MeasurableSpa
ce α] {μ : MeasureTheory.Measure α} [inst_1 : TopologicalSpace α]   [μ.InnerRegu
larCompactLTTop] [Meas…
· 使用定理 `MeasureTheory.isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts`：∀ {α 
: Type u_1} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topol
ogicalSpace α]   [WeaklyLocallyCompactSpace α] [Measure…
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `instR1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [RegularSpace 
X], R1Space X
· 使用定理 `exists_continuous_one_zero_of_isCompact`：exists_continuous_one_zero_of_i
sCompact [RegularSpace X] [LocallyCompactSpace X] {s t : Set X} (hs : IsCompact 
s) (ht : IsClosed t) (hd : Di…
· 使用定理 `IsOpen.isClosed_compl`：∀ {X : Type u} [inst : TopologicalSpace X] {s : S
et X}, IsOpen s → IsClosed sᶜ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.disjoint_compl_right_iff_subset`：disjoint_compl_right_iff_subset : D
isjoint s tᶜ ↔ s subseteq t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用引理 `MeasureTheory.integral_le_measure`：integral_le_measure {f : X -> Real} {
s : Set X} (hs : forall x in s, f x <= 1) (h's : forall x in sᶜ, f x <= 0) : ENN
Real.ofReal (∫ x, f x ∂…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b

--- 原说明 ---
In a locally compact regular space with an inner regular measure, the measure of
 a compact
set `k` is the infimum of the integrals of compactly supported functions equal t
o `1` on `k`.
-/
lemma IsCompact.measure_eq_biInf_integral_hasCompactSupport
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    {k : Set X} (hk : IsCompact k)
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] [InnerRegularCompactLTTop μ]
    [LocallyCompactSpace X] [RegularSpace X] :
    μ k = ⨅ (f : X → ℝ) (_ : Continuous f) (_ : HasCompactSupport f) (_ : EqOn f 1 k)
      (_ : 0 ≤ f), ENNReal.ofReal (∫ x, f x ∂μ) := by
  apply le_antisymm
  · simp only [le_iInf_iff]
    intro f f_cont f_comp fk f_nonneg
    apply (f_cont.integrable_of_hasCompactSupport f_comp).measure_le_integral
    · exact Eventually.of_forall f_nonneg
    · exact fun x hx ↦ by simp [fk hx]
  · apply le_of_forall_gt (fun r hr ↦ ?_)
    simp only [iInf_lt_iff, exists_prop]
    obtain ⟨U, kU, U_open, mu_U⟩ : ∃ U, k ⊆ U ∧ IsOpen U ∧ μ U < r :=
      hk.exists_isOpen_lt_of_lt r hr
    obtain ⟨⟨f, f_cont⟩, fk, fU, f_comp, f_range⟩ : ∃ (f : C(X, ℝ)), EqOn f 1 k ∧ EqOn f 0 Uᶜ
        ∧ HasCompactSupport f ∧ ∀ (x : X), f x ∈ Icc 0 1 := exists_continuous_one_zero_of_isCompact
      hk U_open.isClosed_compl (disjoint_compl_right_iff_subset.mpr kU)
    refine ⟨f, f_cont, f_comp, fk, fun x ↦ (f_range x).1, ?_⟩
    exact (integral_le_measure (fun x _hx ↦ (f_range x).2) (fun x hx ↦ (fU hx).le)).trans_lt mu_U

/-- Given an inner regular finite measure, the measure of an open set is the supremum of the
integrals of nonnegative continuous functions supported in this set and bounded by `1`. -/
/-
**IsOpen.measure_eq_biSup_integral_continuous** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsOpen.measure_eq_biSup_integral_continuous {X : Type*} [TopologicalSpace 
X] [MeasurableSpace X] [BorelSpace X] [T2Space X] {U : Set X} (hU : IsOpen U) (μ
 : Measure X) [IsFiniteMeasure μ] [InnerRegularCompactLTTop μ] [NormalSpace X] :
 μ U = ⨆ (f : X -> Real) (_ : Continuous f) (_ : EqOn f 0 Uᶜ) (_ : 0 <= f) (_ : 
f <= 1), ENNReal.ofReal (∫ x, f x ∂μ)
参数：hU : IsOpen U；μ : Measure X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_of_forall_lt`：le_of_forall_lt (H : forall c, c < a -> c < b) : a <= b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `MeasurableSet.exists_lt_isCompact_of_ne_top`：∀ {α : Type u_1} [inst : Me
asurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : TopologicalSpace α]   [
μ.InnerRegularCompactLTTop] ⦃A : …
· 使用定理 `IsOpen.measurableSet`：IsOpen.measurableSet (h : IsOpen s) : MeasurableSe
t s
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `exists_continuous_zero_one_of_isClosed`：exists_continuous_zero_one_of_is
Closed [NormalSpace X] {s t : Set X} (hs : IsClosed s) (ht : IsClosed t) (hd : D
isjoint s t) : exists f : C(…
· 使用定理 `IsOpen.isClosed_compl`：∀ {X : Type u} [inst : TopologicalSpace X] {s : S
et X}, IsOpen s → IsClosed sᶜ
· 使用定理 `IsCompact.isClosed`：IsCompact.isClosed [T2Space X] {s : Set X} (hs : IsC
ompact s) : IsClosed s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.disjoint_compl_left_iff_subset`：disjoint_compl_left_iff_subset : Dis
joint sᶜ t ↔ t subseteq s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `MeasureTheory.Integrable.measure_le_integral`：∀ {X : Type u_1} {mX : Mea
surableSpace X} {μ : MeasureTheory.Measure X} {f : X → ℝ},   MeasureTheory.Integ
rable f μ →     0 ≤ᵐ[μ] f → ∀ {s :…
· 使用定理 `MeasureTheory.Integrable.of_mem_Icc`：∀ {α : Type u_1} {m : MeasurableSpa
ce α} {μ : MeasureTheory.Measure α} [MeasureTheory.IsFiniteMeasure μ] (a b : ℝ) 
  {X : α → ℝ}, AEMeasurab…
· 使用定理 `Continuous.aemeasurable`：Continuous.aemeasurable {f : α -> γ} (h : Conti
nuous f) {μ : Measure α} : AEMeasurable f μ
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `MeasureTheory.integral_le_measure`：integral_le_measure {f : X -> Real} {
s : Set X} (hs : forall x in s, f x <= 1) (h's : forall x in sᶜ, f x <= 0) : ENN
Real.ofReal (∫ x, f x ∂…
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b

--- 原说明 ---
Given an inner regular finite measure, the measure of an open set is the supremu
m of the
integrals of nonnegative continuous functions supported in this set and bounded 
by `1`.
-/
lemma IsOpen.measure_eq_biSup_integral_continuous
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [T2Space X]
    {U : Set X} (hU : IsOpen U)
    (μ : Measure X) [IsFiniteMeasure μ] [InnerRegularCompactLTTop μ] [NormalSpace X] :
    μ U = ⨆ (f : X → ℝ) (_ : Continuous f) (_ : EqOn f 0 Uᶜ) (_ : 0 ≤ f) (_ : f ≤ 1),
      ENNReal.ofReal (∫ x, f x ∂μ) := by
  apply le_antisymm
  · apply le_of_forall_lt (fun r hr ↦ ?_)
    simp only [lt_iSup_iff, exists_prop]
    obtain ⟨K, KU, K_comp, hK⟩ : ∃ K ⊆ U, IsCompact K ∧ r < μ K :=
      MeasurableSet.exists_lt_isCompact_of_ne_top hU.measurableSet (by simp) hr
    obtain ⟨⟨f, f_cont⟩, fU, fK, f_range⟩ : ∃ (f : C(X, ℝ)), EqOn f 0 Uᶜ ∧ EqOn f 1 K
        ∧ ∀ (x : X), f x ∈ Icc 0 1 := exists_continuous_zero_one_of_isClosed
      hU.isClosed_compl K_comp.isClosed (disjoint_compl_left_iff_subset.mpr KU)
    refine ⟨f, f_cont, fU, fun x ↦ (f_range x).1, fun x ↦ (f_range x).2, ?_⟩
    apply hK.trans_le
    apply Integrable.measure_le_integral
    · apply Integrable.of_mem_Icc 0 1 f_cont.aemeasurable
      filter_upwards [] with x using f_range x
    · filter_upwards [] with x using (f_range x).1
    · intro x hx
      apply Eq.ge
      exact fK hx
  · simp only [iSup_le_iff]
    intro f f_cont fU f_nonneg f_le
    exact integral_le_measure (fun x hx ↦ f_le x) (fun x hx ↦ le_of_eq (fU hx))
