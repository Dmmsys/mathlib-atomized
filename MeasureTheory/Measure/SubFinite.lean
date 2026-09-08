/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.Sub

import Mathlib.MeasureTheory.Integral.Lebesgue.Sub
public import Mathlib.MeasureTheory.Measure.Decomposition.Hahn
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Results about subtraction of finite measures

The content of this file is not placed in `MeasureTheory.Measure.Sub` because it uses tools that are
not imported in the other file: the Hahn decomposition of finite measures and measures built with
`withDensity`.

## Main statements

* `sub_le_iff_le_add`: for `μ` and `ν` finite measures, `μ - ν ≤ ξ ↔ μ ≤ ξ + ν`. See also
  `sub_le_iff_le_add_of_le` for the case where only `ν` is finite, with the additional hypothesis
  `ν ≤ μ`.
* `withDensity_sub`: If `μ.withDensity g` is finite, then
  `μ.withDensity (f - g) = μ.withDensity f - μ.withDensity g`.

-/

public section

open scoped ENNReal

namespace MeasureTheory.Measure

variable {α : Type*} {mα : MeasurableSpace α} {μ ν ξ : Measure α}

/-
**MeasureTheory.Measure.sub_le_iff_le_add** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheo
ry.Measure`。
形式化陈述：sub_le_iff_le_add [IsFiniteMeasure μ] [IsFiniteMeasure ν] : μ - ν <= ξ ↔ μ
 <= ξ + ν
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.exists_isHahnDecomposition`：exists_isHahnDecomposition (μ 
ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] : exists s : Set α, IsHah
nDecomposition μ ν s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.IsHahnDecomposition.le_on`：∀ {α : Type u_1} {mα : Measurab
leSpace α} {μ ν : MeasureTheory.Measure α} {s : Set α},   MeasureTheory.IsHahnDe
composition μ ν s → μ.restric…
· 使用定理 `MeasureTheory.Measure.le_add_left`：∀ {α : Type u_1} {m0 : MeasurableSpac
e α} {μ ν ν' : MeasureTheory.Measure α}, μ ≤ ν → μ ≤ ν' + ν
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `MeasureTheory.Measure.sub_le_iff_le_add_of_le`：sub_le_iff_le_add_of_le [
IsFiniteMeasure ν] (h_le : ν <= μ) : μ - ν <= ξ ↔ μ <= ξ + ν
· 使用定理 `MeasureTheory.IsHahnDecomposition.ge_on_compl`：∀ {α : Type u_1} {mα : Me
asurableSpace α} {μ ν : MeasureTheory.Measure α} {s : Set α},   MeasureTheory.Is
HahnDecomposition μ ν s → ν.restric…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.restrict_sub_eq_restrict_sub_restrict`：restrict_su
b_eq_restrict_sub_restrict (h_meas_s : MeasurableSet s) : (μ - ν).restrict s = μ
.restrict s - ν.restrict s
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `MeasureTheory.IsHahnDecomposition.measurableSet`：∀ {α : Type u_1} {mα : 
MeasurableSpace α} {μ ν : MeasureTheory.Measure α} {s : Set α},   MeasureTheory.
IsHahnDecomposition μ ν s → Measurabl…
· 使用定理 `MeasureTheory.Measure.restrict_mono`：restrict_mono {_m0 : MeasurableSpac
e α} ⦃s s' : Set α⦄ (hs : s subseteq s') ⦃μ ν : Measure α⦄ (hμν : μ <= ν) : μ.re
strict s <= ν.restrict s'
· 使用定理 `subset_rfl`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorde
r α] {a : α}, a ⊆ a
· 使用定理 `MeasureTheory.Measure.restrict_add_restrict_compl`：restrict_add_restrict
_compl (hs : MeasurableSet s) : μ.restrict s + μ.restrict sᶜ = μ
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `_private.Mathlib.MeasureTheory.Measure.SubFinite.0.MeasureTheory.Measure
.sub_le_iff_le_add._abel_1_1`：∀ {α : Type u_1} {mα : MeasurableSpace α} {ν ξ : M
easureTheory.Measure α} (s : Set α),   ξ.restrict s + ν.restrict s + (ξ.restrict
 sᶜ + ν.re…
· 使用定理 `MeasureTheory.Measure.sub_le_of_le_add`：sub_le_of_le_add {d} (h : μ <= d
 + ν) : μ - ν <= d
-/
lemma sub_le_iff_le_add [IsFiniteMeasure μ] [IsFiniteMeasure ν] : μ - ν ≤ ξ ↔ μ ≤ ξ + ν := by
  refine ⟨fun h ↦ ?_, sub_le_of_le_add⟩
  obtain ⟨s, hs⟩ := exists_isHahnDecomposition μ ν
  have h_le_s : μ.restrict s ≤ ξ.restrict s + ν.restrict s :=
    hs.le_on.trans (Measure.le_add_left le_rfl)
  have h_le_s_compl : μ.restrict sᶜ ≤ ξ.restrict sᶜ + ν.restrict sᶜ := by
    refine (sub_le_iff_le_add_of_le hs.ge_on_compl).mp ?_
    rw [← restrict_sub_eq_restrict_sub_restrict hs.measurableSet.compl]
    exact restrict_mono subset_rfl h
  rw [← restrict_add_restrict_compl (μ := μ) hs.measurableSet,
    ← restrict_add_restrict_compl (μ := ξ) hs.measurableSet,
    ← restrict_add_restrict_compl (μ := ν) hs.measurableSet]
  suffices μ.restrict s + μ.restrict sᶜ ≤
    ξ.restrict s + ν.restrict s + (ξ.restrict sᶜ + ν.restrict sᶜ) from this.trans_eq (by abel)
  gcongr
/-
**MeasureTheory.Measure.withDensity_sub_of_le** 是 Mathlib 中的一个引理，位于命名空间 `Measure
Theory.Measure`。
形式化陈述：withDensity_sub_of_le {f g : α -> Real>=0∞} [IsFiniteMeasure (μ.withDensit
y g)] (hg : Measurable g) (hgf : g <=ᵐ[μ] f) : μ.withDensity (f - g) = μ.withDen
sity f - μ.withDensity g
参数：μ.withDensity g；hg : Measurable g；hgf : g <=ᵐ[μ] f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.sub_apply`：sub_apply [IsFiniteMeasure ν] (h₁ : Mea
surableSet s) (h₂ : ν <= μ) : (μ - ν) s = μ s - ν s
· 使用引理 `MeasureTheory.withDensity_mono`：withDensity_mono {f g : α -> Real>=0∞} (
hfg : f <=ᵐ[μ] g) : μ.withDensity f <= μ.withDensity g
· 使用定理 `MeasureTheory.withDensity_apply`：withDensity_apply (f : α -> Real>=0∞) {
s : Set α} (hs : MeasurableSet s) : μ.withDensity f s = ∫⁻ a in s, f a ∂μ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_sub`：lintegral_sub {f g : α -> Real>=0∞} (hg : M
easurable g) (hg_fin : ∫⁻ a, g a ∂μ != ∞) (h_le : g <=ᵐ[μ] f) : ∫⁻ a, f a - g a 
∂μ = ∫⁻ a, f a ∂μ…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MeasureTheory.ae_restrict_of_ae`：ae_restrict_of_ae {s : Set α} {p : α ->
 Prop} (h : forallᵐ x ∂μ, p x) : forallᵐ x ∂μ.restrict s, p x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma withDensity_sub_of_le {f g : α → ℝ≥0∞} [IsFiniteMeasure (μ.withDensity g)]
    (hg : Measurable g) (hgf : g ≤ᵐ[μ] f) :
    μ.withDensity (f - g) = μ.withDensity f - μ.withDensity g := by
  ext s hs
  rw [sub_apply hs (withDensity_mono hgf), withDensity_apply _ hs, withDensity_apply _ hs,
    withDensity_apply _ hs, ← lintegral_sub hg _ (ae_restrict_of_ae hgf)]
  · simp
  · simp [← withDensity_apply _ hs]
/-
**MeasureTheory.Measure.withDensity_sub** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory
.Measure`。
形式化陈述：withDensity_sub {f g : α -> Real>=0∞} [IsFiniteMeasure (μ.withDensity g)] 
(hf : Measurable f) (hg : Measurable g) : μ.withDensity (f - g) = μ.withDensity 
f - μ.withDensity g
参数：μ.withDensity g；hf : Measurable f；hg : Measurable g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `measurableSet_le`：measurableSet_le {f g : δ -> α} (hf : Measurable f) (h
g : Measurable g) : MeasurableSet { a | f a <= g a }
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `ENNReal.instSecondCountableTopology`：SecondCountableTopology ENNReal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.restrict_add_restrict_compl`：restrict_add_restrict
_compl (hs : MeasurableSet s) : μ.restrict s + μ.restrict sᶜ = μ
· 使用定理 `MeasureTheory.withDensity_apply`：withDensity_apply (f : α -> Real>=0∞) {
s : Set α} (hs : MeasurableSet s) : μ.withDensity f s = ∫⁻ a in s, f a ∂μ
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.lintegral_eq_zero_iff`：lintegral_eq_zero_iff {f : α -> Rea
l>=0∞} (hf : Measurable f) : ∫⁻ a, f a ∂μ = 0 ↔ f =ᵐ[μ] 0
· 使用定理 `Measurable.sub`：∀ {G : Type u_2} {α : Type u_3} [inst : MeasurableSpace 
G] [inst_1 : Sub G] {m : MeasurableSpace α} {f g : α → G}   [MeasurableSub₂ G], 
Meas…
· 使用定理 `MeasureTheory.ae_restrict_of_forall_mem`：ae_restrict_of_forall_mem {μ : 
Measure α} {s : Set α} (hs : MeasurableSet s) {p : α -> Prop} (h : forall x in s
, p x) : forallᵐ (x : α) ∂μ.r…
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `MeasureTheory.Measure.restrict_sub_eq_restrict_sub_restrict`：restrict_su
b_eq_restrict_sub_restrict (h_meas_s : MeasurableSet s) : (μ - ν).restrict s = μ
.restrict s - ν.restrict s
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.restrict_withDensity`：restrict_withDensity {s : Set α} (hs
 : MeasurableSet s) (f : α -> Real>=0∞) : (μ.withDensity f).restrict s = (μ.rest
rict s).withDensity f
· 使用引理 `MeasureTheory.Measure.withDensity_sub_of_le`：withDensity_sub_of_le {f g 
: α -> Real>=0∞} [IsFiniteMeasure (μ.withDensity g)] (hg : Measurable g) (hgf : 
g <=ᵐ[μ] f) : μ.withDensity (f - …
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.Measure.le_add_left`：∀ {α : Type u_1} {m0 : MeasurableSpac
e α} {μ ν ν' : MeasureTheory.Measure α}, μ ≤ ν → μ ≤ ν' + ν
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `MeasureTheory.Measure.sub_le_of_le_add`：sub_le_of_le_add {d} (h : μ <= d
 + ν) : μ - ν <= d
· 使用定理 `MeasureTheory.withDensity_add_right`：withDensity_add_right (f : α -> Rea
l>=0∞) {g : α -> Real>=0∞} (hg : Measurable g) : μ.withDensity (f + g) = μ.withD
ensity f + μ.withDensity …
（共 33 条，此处仅展示前 30 条）
-/
lemma withDensity_sub {f g : α → ℝ≥0∞} [IsFiniteMeasure (μ.withDensity g)]
    (hf : Measurable f) (hg : Measurable g) :
    μ.withDensity (f - g) = μ.withDensity f - μ.withDensity g := by
  refine le_antisymm ?_ ?_
  · let t := {x | f x ≤ g x}
    have ht : MeasurableSet t := measurableSet_le hf hg
    rw [← restrict_add_restrict_compl (μ := μ.withDensity (f - g)) ht,
      ← restrict_add_restrict_compl (μ := μ.withDensity f - μ.withDensity g) ht]
    have h_zero : (μ.withDensity (f - g)).restrict t = 0 := by
      simp only [restrict_eq_zero]
      rw [withDensity_apply _ ht, lintegral_eq_zero_iff (by fun_prop)]
      refine ae_restrict_of_forall_mem ht fun x hx ↦ ?_
      simpa [tsub_eq_zero_iff_le]
    rw [h_zero, zero_add]
    suffices (μ.withDensity (f - g)).restrict tᶜ ≤
      (μ.withDensity f - μ.withDensity g).restrict tᶜ from this.trans (Measure.le_add_left le_rfl)
    rw [restrict_sub_eq_restrict_sub_restrict ht.compl]
    simp_rw [restrict_withDensity ht.compl]
    have : IsFiniteMeasure ((μ.restrict tᶜ).withDensity g) := by
      rw [← restrict_withDensity ht.compl]
      infer_instance
    rw [withDensity_sub_of_le hg]
    refine ae_restrict_of_forall_mem ht.compl fun x hx ↦ ?_
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le, t] at hx
    exact hx.le
  · refine sub_le_of_le_add ?_
    rw [← withDensity_add_right _ hg]
    exact withDensity_mono (ae_of_all _ fun x ↦ le_tsub_add)

end MeasureTheory.Measure

