/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Measure.Trim
public import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated

/-!
# Almost everywhere measurable functions

A function is almost everywhere measurable if it coincides almost everywhere with a measurable
function. This property, called `AEMeasurable f μ`, is defined in the file `MeasureSpaceDef`.
We discuss several of its properties that are analogous to properties of measurable functions.
-/

public section

open MeasureTheory MeasureTheory.Measure Filter Set Function ENNReal

variable {ι α β γ δ R : Type*} {m0 : MeasurableSpace α} [MeasurableSpace β] [MeasurableSpace γ]
  [MeasurableSpace δ] {f g : α → β} {μ ν : Measure α}

section

@[nontriviality]
/-
**Subsingleton.aemeasurable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subsingleton.aemeasurable [Subsingleton α] : AEMeasurable f μ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `Subsingleton.measurable`：Subsingleton.measurable [Subsingleton α] : Meas
urable f
-/
theorem Subsingleton.aemeasurable [Subsingleton α] : AEMeasurable f μ :=
  Subsingleton.measurable.aemeasurable

@[nontriviality, fun_prop]
/-
**aemeasurable_of_subsingleton_codomain** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：aemeasurable_of_subsingleton_codomain [Subsingleton β] : AEMeasurable f μ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `measurable_of_subsingleton_codomain`：measurable_of_subsingleton_codomain
 [Subsingleton β] (f : α -> β) : Measurable f
-/
theorem aemeasurable_of_subsingleton_codomain [Subsingleton β] : AEMeasurable f μ :=
  (measurable_of_subsingleton_codomain f).aemeasurable

@[simp, fun_prop]
/-
**aemeasurable_zero_measure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：aemeasurable_zero_measure : AEMeasurable f (0 : Measure α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
-/
theorem aemeasurable_zero_measure : AEMeasurable f (0 : Measure α) := by
  nontriviality α; inhabit α
  exact ⟨fun _ => f default, measurable_const, rfl⟩
/-
**aemeasurable_id''** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：aemeasurable_id'' (μ : Measure α) {m : MeasurableSpace α} (hm : m <= m0) :
 @AEMeasurable α α m m0 id μ
参数：μ : Measure α；hm : m <= m0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `measurable_id''`：measurable_id'' {m mα : MeasurableSpace α} (hm : m <= m
α) : @Measurable α α mα m id
-/
theorem aemeasurable_id'' (μ : Measure α) {m : MeasurableSpace α} (hm : m ≤ m0) :
    @AEMeasurable α α m m0 id μ :=
  @Measurable.aemeasurable α α m0 m id μ (measurable_id'' hm)
/-
**aemeasurable_of_map_neZero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：aemeasurable_of_map_neZero {μ : Measure α} {f : α -> β} (h : NeZero (μ.map
 f)) : AEMeasurable f μ
参数：h : NeZero (μ.map f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_of_not_aemeasurable`：map_of_not_aemeasurable {
f : α -> β} {μ : Measure α} (hf : ¬AEMeasurable f μ) : μ.map f = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma aemeasurable_of_map_neZero {μ : Measure α}
    {f : α → β} (h : NeZero (μ.map f)) :
    AEMeasurable f μ := by
  by_contra h'
  simp [h'] at h

namespace AEMeasurable

/-
**AEMeasurable.mono_ac** 是 Mathlib 中的一个引理，位于命名空间 `AEMeasurable`。
形式化陈述：mono_ac (hf : AEMeasurable f ν) (hμν : μ ≪ ν) : AEMeasurable f μ
参数：hf : AEMeasurable f ν；hμν : μ ≪ ν。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `AEMeasurable.measurable_mk`：measurable_mk (h : AEMeasurable f μ) : Measu
rable (h.mk f)
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.ae_le`：∀ {α : Type u_1} {mα :
 MeasurableSpace α} {μ ν : MeasureTheory.Measure α},   μ.AbsolutelyContinuous ν 
→ MeasureTheory.ae μ ≤ MeasureTheory.a…
· 使用定理 `AEMeasurable.ae_eq_mk`：ae_eq_mk (h : AEMeasurable f μ) : f =ᵐ[μ] h.mk f
-/
lemma mono_ac (hf : AEMeasurable f ν) (hμν : μ ≪ ν) : AEMeasurable f μ :=
  ⟨hf.mk f, hf.measurable_mk, hμν.ae_le hf.ae_eq_mk⟩
/-
**AEMeasurable.mono_measure** 是 Mathlib 中的一个定理，位于命名空间 `AEMeasurable`。
形式化陈述：mono_measure (h : AEMeasurable f μ) (h' : ν <= μ) : AEMeasurable f ν
参数：h : AEMeasurable f μ；h' : ν <= μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AEMeasurable.mono_ac`：mono_ac (hf : AEMeasurable f ν) (hμν : μ ≪ ν) : AE
Measurable f μ
· 使用定理 `LE.le.absolutelyContinuous`：∀ {α : Type u_1} {mα : MeasurableSpace α} {μ
 ν : MeasureTheory.Measure α}, μ ≤ ν → μ.AbsolutelyContinuous ν
-/
theorem mono_measure (h : AEMeasurable f μ) (h' : ν ≤ μ) : AEMeasurable f ν :=
  mono_ac h h'.absolutelyContinuous
/-
**AEMeasurable.mono_set** 是 Mathlib 中的一个定理，位于命名空间 `AEMeasurable`。
形式化陈述：mono_set {s t} (h : s subseteq t) (ht : AEMeasurable f (μ.restrict t)) : A
EMeasurable f (μ.restrict s)
参数：h : s subseteq t；ht : AEMeasurable f (μ.restrict t)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AEMeasurable.mono_measure`：mono_measure (h : AEMeasurable f μ) (h' : ν <
= μ) : AEMeasurable f ν
· 使用定理 `MeasureTheory.Measure.restrict_mono`：restrict_mono {_m0 : MeasurableSpac
e α} ⦃s s' : Set α⦄ (hs : s subseteq s') ⦃μ ν : Measure α⦄ (hμν : μ <= ν) : μ.re
strict s <= ν.restrict s'
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem mono_set {s t} (h : s ⊆ t) (ht : AEMeasurable f (μ.restrict t)) :
    AEMeasurable f (μ.restrict s) :=
  ht.mono_measure (restrict_mono h le_rfl)

@[fun_prop]
/-
**AEMeasurable.mono'** 是 Mathlib 中的一个定理，位于命名空间 `AEMeasurable`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} {m0 : MeasurableSpace α} [inst : Measurabl
eSpace β] {f : α → β}   {μ ν : MeasureTheory.Measure α}, AEMeasurable f μ → ν.Ab
solutelyContinuous μ → AEMeasurable f ν
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `AEMeasurable.measurable_mk`：measurable_mk (h : AEMeasurable f μ) : Measu
rable (h.mk f)
· 使用定理 `AEMeasurable.ae_eq_mk`：ae_eq_mk (h : AEMeasurable f μ) : f =ᵐ[μ] h.mk f
-/
protected theorem mono' (h : AEMeasurable f μ) (h' : ν ≪ μ) : AEMeasurable f ν :=
  ⟨h.mk f, h.measurable_mk, h' h.ae_eq_mk⟩
/-
**AEMeasurable.ae_mem_imp_eq_mk** 是 Mathlib 中的一个定理，位于命名空间 `AEMeasurable`。
形式化陈述：ae_mem_imp_eq_mk {s} (h : AEMeasurable f (μ.restrict s)) : forallᵐ x ∂μ, x
 in s -> f x = h.mk f x
参数：h : AEMeasurable f (μ.restrict s)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.ae_imp_of_ae_restrict`：ae_imp_of_ae_restrict {s : Set α} {
p : α -> Prop} (h : forallᵐ x ∂μ.restrict s, p x) : forallᵐ x ∂μ, x in s -> p x
· 使用定理 `AEMeasurable.ae_eq_mk`：ae_eq_mk (h : AEMeasurable f μ) : f =ᵐ[μ] h.mk f
-/
theorem ae_mem_imp_eq_mk {s} (h : AEMeasurable f (μ.restrict s)) :
    ∀ᵐ x ∂μ, x ∈ s → f x = h.mk f x :=
  ae_imp_of_ae_restrict h.ae_eq_mk
/-
**AEMeasurable.ae_inf_principal_eq_mk** 是 Mathlib 中的一个定理，位于命名空间 `AEMeasurable`。
形式化陈述：ae_inf_principal_eq_mk {s} (h : AEMeasurable f (μ.restrict s)) : f =ᶠ[ae μ
 ⊓ 𝓟 s] h.mk f
参数：h : AEMeasurable f (μ.restrict s)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.le_ae_restrict`：le_ae_restrict : ae μ ⊓ 𝓟 s <= ae (μ.restr
ict s)
· 使用定理 `AEMeasurable.ae_eq_mk`：ae_eq_mk (h : AEMeasurable f μ) : f =ᵐ[μ] h.mk f
-/
theorem ae_inf_principal_eq_mk {s} (h : AEMeasurable f (μ.restrict s)) : f =ᶠ[ae μ ⊓ 𝓟 s] h.mk f :=
  le_ae_restrict h.ae_eq_mk

@[fun_prop]
/-
**AEMeasurable.sum_measure** 是 Mathlib 中的一个定理，位于命名空间 `AEMeasurable`。
形式化陈述：sum_measure [Countable ι] {μ : ι -> Measure α} (h : forall i, AEMeasurable
 f (μ i)) : AEMeasurable f (sum μ)
参数：h : forall i, AEMeasurable f (μ i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measure_toMeasurable`：measure_toMeasurable (s : Set α) : μ
 (toMeasurable μ s) = μ s
· 使用定理 `AEMeasurable.ae_eq_mk`：ae_eq_mk (h : AEMeasurable f μ) : f =ᵐ[μ] h.mk f
· 使用定理 `MeasurableSet.iInter`：MeasurableSet.iInter [Countable ι] {f : ι -> Set α
} (h : forall b, MeasurableSet (f b)) : MeasurableSet (⋂ b, f b)
· 使用定理 `MeasureTheory.measurableSet_toMeasurable`：measurableSet_toMeasurable (μ 
: Measure α) (s : Set α) : MeasurableSet (toMeasurable μ s)
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `MeasureTheory.subset_toMeasurable`：subset_toMeasurable (μ : Measure α) (
s : Set α) : s subseteq toMeasurable μ s
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `measurable_of_restrict_of_restrict_compl`：measurable_of_restrict_of_rest
rict_compl {f : α -> β} {s : Set α} (hs : MeasurableSet s) (h₁ : Measurable (s.d
omRestrict f)) (h₂ : Measurabl…
· 使用定理 `Set.domRestrict_piecewise`：domRestrict_piecewise (f g : α -> β) (s : Set
 α) [forall x, Decidable (x in s)] : s.domRestrict (piecewise s f g) = s.domRest
rict f
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `Set.domRestrict_piecewise_compl`：domRestrict_piecewise_compl (f g : α ->
 β) (s : Set α) [forall x, Decidable (x in s)] : sᶜ.domRestrict (piecewise s f g
) = sᶜ.domRestrict g
· 使用定理 `Set.compl_iInter`：compl_iInter (s : ι -> Set β) : (⋂ i, s i)ᶜ = ⋃ i, (s 
i)ᶜ
· 使用定理 `MeasurableSet.iUnion`：∀ {α : Type u_1} {ι : Sort u_6} {m : MeasurableSpa
ce α} [Countable ι] ⦃f : ι → Set α⦄,   (∀ (b : ι), MeasurableSet (f b)) → Measur
ableSet (⋃…
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `AEMeasurable.measurable_mk`：measurable_mk (h : AEMeasurable f μ) : Measu
rable (h.mk f)
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.ae_sum_iff`：ae_sum_iff [Countable ι] {μ : ι -> Mea
sure α} {p : α -> Prop} : (forallᵐ x ∂sum μ, p x) ↔ forall i, forallᵐ x ∂μ i, p 
x
· 使用定理 `MeasureTheory.measure_mono_null`：measure_mono_null (h : s subseteq t) (h
t : μ t = 0) : μ s = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.piecewise_eq_of_notMem`：piecewise_eq_of_notMem {i : α} (hi : i ∉ s) 
: s.piecewise f g i = g i
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
（共 31 条，此处仅展示前 30 条）
-/
theorem sum_measure [Countable ι] {μ : ι → Measure α} (h : ∀ i, AEMeasurable f (μ i)) :
    AEMeasurable f (sum μ) := by
  classical
  nontriviality β
  inhabit β
  set s : ι → Set α := fun i => toMeasurable (μ i) { x | f x ≠ (h i).mk f x }
  have hsμ : ∀ i, μ i (s i) = 0 := by
    intro i
    rw [measure_toMeasurable]
    exact (h i).ae_eq_mk
  have hsm : MeasurableSet (⋂ i, s i) :=
    MeasurableSet.iInter fun i => measurableSet_toMeasurable _ _
  have hs : ∀ i x, x ∉ s i → f x = (h i).mk f x := by
    intro i x hx
    contrapose! hx
    exact subset_toMeasurable _ _ hx
  set g : α → β := (⋂ i, s i).piecewise (const α default) f
  refine ⟨g, measurable_of_restrict_of_restrict_compl hsm ?_ ?_, ae_sum_iff.mpr fun i => ?_⟩
  · rw [domRestrict_piecewise]
    simp only [s]
    exact measurable_const
  · rw [domRestrict_piecewise_compl, compl_iInter]
    intro t ht
    refine ⟨⋃ i, (h i).mk f ⁻¹' t ∩ (s i)ᶜ, MeasurableSet.iUnion fun i ↦
      (measurable_mk _ ht).inter (measurableSet_toMeasurable _ _).compl, ?_⟩
    ext ⟨x, hx⟩
    simp only [mem_preimage, mem_iUnion, Set.domRestrict, mem_inter_iff,
      mem_compl_iff] at hx ⊢
    constructor
    · rintro ⟨i, hxt, hxs⟩
      rwa [hs _ _ hxs]
    · rcases hx with ⟨i, hi⟩
      rw [hs _ _ hi]
      exact fun h => ⟨i, h, hi⟩
  · refine measure_mono_null (fun x (hx : f x ≠ g x) => ?_) (hsμ i)
    contrapose hx
    refine (piecewise_eq_of_notMem _ _ _ ?_).symm
    exact fun h => hx (mem_iInter.1 h i)

@[simp]
/-
**AEMeasurable._root_.aemeasurable_sum_measure_iff** 是 Mathlib 中的一个定理，位于命名空间 `AE
Measurable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.aemeasurable_sum_measure_iff [Countable ι] {μ : ι → Measure α} :
    AEMeasurable f (sum μ) ↔ ∀ i, AEMeasurable f (μ i) :=
  ⟨fun h _ => h.mono_measure (le_sum _ _), sum_measure⟩

@[simp]
/-
**AEMeasurable._root_.aemeasurable_add_measure_iff** 是 Mathlib 中的一个定理，位于命名空间 `AE
Measurable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.aemeasurable_add_measure_iff :
    AEMeasurable f (μ + ν) ↔ AEMeasurable f μ ∧ AEMeasurable f ν := by
  rw [← sum_cond, aemeasurable_sum_measure_iff, Bool.forall_bool, and_comm]
  rfl

@[fun_prop]
/-
**AEMeasurable.add_measure** 是 Mathlib 中的一个定理，位于命名空间 `AEMeasurable`。
形式化陈述：add_measure {f : α -> β} (hμ : AEMeasurable f μ) (hν : AEMeasurable f ν) :
 AEMeasurable f (μ + ν)
参数：hμ : AEMeasurable f μ；hν : AEMeasurable f ν。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `aemeasurable_add_measure_iff`：∀ {α : Type u_2} {β : Type u_3} {m0 : Meas
urableSpace α} [inst : MeasurableSpace β] {f : α → β}   {μ ν : MeasureTheory.Mea
sure α}, AEMeasura…
-/
theorem add_measure {f : α → β} (hμ : AEMeasurable f μ) (hν : AEMeasurable f ν) :
    AEMeasurable f (μ + ν) :=
  aemeasurable_add_measure_iff.2 ⟨hμ, hν⟩
/-
**AEMeasurable.map_add** 是 Mathlib 中的一个定理，位于命名空间 `AEMeasurable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem map_add₀ {μ ν : Measure α} {f : α → β}
    (hμ : AEMeasurable f μ) (hν : AEMeasurable f ν) :
    (μ + ν).map f = μ.map f + ν.map f := by
  ext
  simp [*]

@[fun_prop]
/-
**AEMeasurable.iUnion** 是 Mathlib 中的一个定理，位于命名空间 `AEMeasurable`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} {β : Type u_3} {m0 : MeasurableSpace α} [i
nst : MeasurableSpace β] {f : α → β}   {μ : MeasureTheory.Measure α} [Countable 
ι] {s : ι → Set α},   (∀ (i : ι), AEMeasurable f (μ.restrict (s i))) → AEMeasura
ble f (μ.restrict (⋃ i, s i))
参数：∀ (i : ι), AEMeasurable f (μ.restrict (s i))；μ.restrict (⋃ i, s i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AEMeasurable.mono_measure`：mono_measure (h : AEMeasurable f μ) (h' : ν <
= μ) : AEMeasurable f ν
· 使用定理 `AEMeasurable.sum_measure`：sum_measure [Countable ι] {μ : ι -> Measure α}
 (h : forall i, AEMeasurable f (μ i)) : AEMeasurable f (sum μ)
· 使用定理 `MeasureTheory.Measure.restrict_iUnion_le`：restrict_iUnion_le [Countable 
ι] {s : ι -> Set α} : μ.restrict (⋃ i, s i) <= sum fun i => μ.restrict (s i)
-/
protected theorem iUnion [Countable ι] {s : ι → Set α}
    (h : ∀ i, AEMeasurable f (μ.restrict (s i))) : AEMeasurable f (μ.restrict (⋃ i, s i)) :=
  (sum_measure h).mono_measure <| restrict_iUnion_le

@[simp]
/-
**AEMeasurable._root_.aemeasurable_iUnion_iff** 是 Mathlib 中的一个定理，位于命名空间 `AEMeasu
rable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.aemeasurable_iUnion_iff [Countable ι] {s : ι → Set α} :
    AEMeasurable f (μ.restrict (⋃ i, s i)) ↔ ∀ i, AEMeasurable f (μ.restrict (s i)) :=
  ⟨fun h _ => h.mono_measure <| restrict_mono (subset_iUnion _ _) le_rfl, AEMeasurable.iUnion⟩

@[simp]
/-
**AEMeasurable._root_.aemeasurable_union_iff** 是 Mathlib 中的一个定理，位于命名空间 `AEMeasur
able`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.aemeasurable_union_iff {s t : Set α} :
    AEMeasurable f (μ.restrict (s ∪ t)) ↔
      AEMeasurable f (μ.restrict s) ∧ AEMeasurable f (μ.restrict t) := by
  simp only [union_eq_iUnion, aemeasurable_iUnion_iff, Bool.forall_bool, cond, and_comm]

@[fun_prop]
/-
**AEMeasurable.smul_measure** 是 Mathlib 中的一个定理，位于命名空间 `AEMeasurable`。
形式化陈述：smul_measure [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] (h : AE
Measurable f μ) (c : R) : AEMeasurable f (c • μ)
参数：h : AEMeasurable f μ；c : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `AEMeasurable.measurable_mk`：measurable_mk (h : AEMeasurable f μ) : Measu
rable (h.mk f)
· 使用定理 `MeasureTheory.Measure.ae_smul_measure`：ae_smul_measure {p : α -> Prop} [
SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] (h : forallᵐ x ∂μ, p x) (c 
: R) : forallᵐ x ∂c • μ, p …
· 使用定理 `AEMeasurable.ae_eq_mk`：ae_eq_mk (h : AEMeasurable f μ) : f =ᵐ[μ] h.mk f
-/
theorem smul_measure [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    (h : AEMeasurable f μ) (c : R) : AEMeasurable f (c • μ) :=
  ⟨h.mk f, h.measurable_mk, ae_smul_measure h.ae_eq_mk c⟩
/-
**AEMeasurable.comp_aemeasurable** 是 Mathlib 中的一个定理，位于命名空间 `AEMeasurable`。
形式化陈述：comp_aemeasurable {f : α -> δ} {g : δ -> β} (hg : AEMeasurable g (μ.map f)
) (hf : AEMeasurable f μ) : AEMeasurable (g ∘ f) μ
参数：hg : AEMeasurable g (μ.map f)；hf : AEMeasurable f μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `AEMeasurable.measurable_mk`：measurable_mk (h : AEMeasurable f μ) : Measu
rable (h.mk f)
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `MeasureTheory.ae_eq_comp`：ae_eq_comp {f : α -> β} {g g' : β -> δ} (hf : 
AEMeasurable f μ) (h : g =ᵐ[μ.map f] g') : g ∘ f =ᵐ[μ] g' ∘ f
· 使用定理 `AEMeasurable.ae_eq_mk`：ae_eq_mk (h : AEMeasurable f μ) : f =ᵐ[μ] h.mk f
· 使用定理 `Filter.EventuallyEq.fun_comp`：∀ {α : Type u} {β : Type v} {γ : Type w} {
f g : α → β} {l : Filter α}, f =ᶠ[l] g → ∀ (h : β → γ), h ∘ f =ᶠ[l] h ∘ g
-/
theorem comp_aemeasurable {f : α → δ} {g : δ → β} (hg : AEMeasurable g (μ.map f))
    (hf : AEMeasurable f μ) : AEMeasurable (g ∘ f) μ :=
  ⟨hg.mk g ∘ hf.mk f, hg.measurable_mk.comp hf.measurable_mk,
    (ae_eq_comp hf hg.ae_eq_mk).trans (hf.ae_eq_mk.fun_comp (mk g hg))⟩

@[fun_prop]
/-
**AEMeasurable.comp_aemeasurable'** 是 Mathlib 中的一个定理，位于命名空间 `AEMeasurable`。
形式化陈述：comp_aemeasurable' {f : α -> δ} {g : δ -> β} (hg : AEMeasurable g (μ.map f
)) (hf : AEMeasurable f μ) : AEMeasurable (fun x => g (f x)) μ
参数：hg : AEMeasurable g (μ.map f)；hf : AEMeasurable f μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AEMeasurable.comp_aemeasurable`：comp_aemeasurable {f : α -> δ} {g : δ ->
 β} (hg : AEMeasurable g (μ.map f)) (hf : AEMeasurable f μ) : AEMeasurable (g ∘ 
f) μ
-/
theorem comp_aemeasurable' {f : α → δ} {g : δ → β} (hg : AEMeasurable g (μ.map f))
    (hf : AEMeasurable f μ) : AEMeasurable (fun x ↦ g (f x)) μ := comp_aemeasurable hg hf
/-
**AEMeasurable.comp_measurable** 是 Mathlib 中的一个定理，位于命名空间 `AEMeasurable`。
形式化陈述：comp_measurable {f : α -> δ} {g : δ -> β} (hg : AEMeasurable g (μ.map f)) 
(hf : Measurable f) : AEMeasurable (g ∘ f) μ
参数：hg : AEMeasurable g (μ.map f)；hf : Measurable f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AEMeasurable.comp_aemeasurable`：comp_aemeasurable {f : α -> δ} {g : δ ->
 β} (hg : AEMeasurable g (μ.map f)) (hf : AEMeasurable f μ) : AEMeasurable (g ∘ 
f) μ
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
-/
theorem comp_measurable {f : α → δ} {g : δ → β} (hg : AEMeasurable g (μ.map f))
    (hf : Measurable f) : AEMeasurable (g ∘ f) μ :=
  hg.comp_aemeasurable hf.aemeasurable

@[fun_prop]
/-
**AEMeasurable.comp_quasiMeasurePreserving** 是 Mathlib 中的一个定理，位于命名空间 `AEMeasurab
le`。
形式化陈述：comp_quasiMeasurePreserving {ν : Measure δ} {f : α -> δ} {g : δ -> β} (hg 
: AEMeasurable g ν) (hf : QuasiMeasurePreserving f μ ν) : AEMeasurable (g ∘ f) μ
参数：hg : AEMeasurable g ν；hf : QuasiMeasurePreserving f μ ν。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AEMeasurable.comp_measurable`：comp_measurable {f : α -> δ} {g : δ -> β} 
(hg : AEMeasurable g (μ.map f)) (hf : Measurable f) : AEMeasurable (g ∘ f) μ
· 使用定理 `AEMeasurable.mono'`：∀ {α : Type u_2} {β : Type u_3} {m0 : MeasurableSpac
e α} [inst : MeasurableSpace β] {f : α → β}   {μ ν : MeasureTheory.Measure α}, A
EMeasura…
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.absolutelyContinuous`：∀ {α 
: Type u_1} {β : Type u_2} {mβ : MeasurableSpace β} {m0 : MeasurableSpace α} {f 
: α → β}   {μa : autoParam (MeasureTheory.Measure α) Me…
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.measurable`：∀ {α : Type u_1
} {β : Type u_2} {mβ : MeasurableSpace β} {m0 : MeasurableSpace α} {f : α → β}  
 {μa : autoParam (MeasureTheory.Measure α) Me…
-/
theorem comp_quasiMeasurePreserving {ν : Measure δ} {f : α → δ} {g : δ → β} (hg : AEMeasurable g ν)
    (hf : QuasiMeasurePreserving f μ ν) : AEMeasurable (g ∘ f) μ :=
  (hg.mono' hf.absolutelyContinuous).comp_measurable hf.measurable
/-
**AEMeasurable.map_map_of_aemeasurable** 是 Mathlib 中的一个定理，位于命名空间 `AEMeasurable`。
形式化陈述：map_map_of_aemeasurable {g : β -> γ} {f : α -> β} (hg : AEMeasurable g (Me
asure.map f μ)) (hf : AEMeasurable f μ) : (μ.map f).map g = μ.map (g ∘ f)
参数：hg : AEMeasurable g (Measure.map f μ)；hf : AEMeasurable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_apply_of_aemeasurable`：map_apply_of_aemeasurab
le (hf : AEMeasurable f μ) {s : Set β} (hs : MeasurableSet s) : μ.map f s = μ (f
 ⁻¹' s)
· 使用引理 `MeasureTheory.Measure.map_apply₀`：map_apply₀ {f : α -> β} (hf : AEMeasur
able f μ) {s : Set β} (hs : NullMeasurableSet s (map f μ)) : μ.map f s = μ (f ⁻¹
' s)
· 使用定理 `AEMeasurable.nullMeasurable`：∀ {α : Type u_1} {β : Type u_2} {m0 : Measu
rableSpace α} {mβ : MeasurableSpace β} {μ : MeasureTheory.Measure α}   {f : α → 
β}, AEMeasurable …
· 使用定理 `AEMeasurable.comp_aemeasurable`：comp_aemeasurable {f : α -> δ} {g : δ ->
 β} (hg : AEMeasurable g (μ.map f)) (hf : AEMeasurable f μ) : AEMeasurable (g ∘ 
f) μ
· 使用定理 `Set.preimage_comp`：preimage_comp {s : Set γ} : g ∘ f ⁻¹' s = f ⁻¹' g ⁻¹'
 s
-/
theorem map_map_of_aemeasurable {g : β → γ} {f : α → β} (hg : AEMeasurable g (Measure.map f μ))
    (hf : AEMeasurable f μ) : (μ.map f).map g = μ.map (g ∘ f) := by
  ext1 s hs
  rw [map_apply_of_aemeasurable hg hs, map_apply₀ hf (hg.nullMeasurable hs),
    map_apply_of_aemeasurable (hg.comp_aemeasurable hf) hs, preimage_comp]

@[fun_prop]
/-
**AEMeasurable.fst** 是 Mathlib 中的一个定理，位于命名空间 `AEMeasurable`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} {m0 : MeasurableSpace α} [i
nst : MeasurableSpace β]   [inst_1 : MeasurableSpace γ] {μ : MeasureTheory.Measu
re α} {f : α → β × γ},   AEMeasurable f μ → AEMeasurable (fun x => (f x).1) μ
参数：fun x => (f x).1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp_aemeasurable`：Measurable.comp_aemeasurable [MeasurableSp
ace δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) : A
EMeasurable (g ∘ f…
· 使用定理 `measurable_fst`：measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.fst : α × β -> α)
-/
protected theorem fst {f : α → β × γ} (hf : AEMeasurable f μ) :
    AEMeasurable (fun x ↦ (f x).1) μ :=
  measurable_fst.comp_aemeasurable hf

@[fun_prop]
/-
**AEMeasurable.snd** 是 Mathlib 中的一个定理，位于命名空间 `AEMeasurable`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} {m0 : MeasurableSpace α} [i
nst : MeasurableSpace β]   [inst_1 : MeasurableSpace γ] {μ : MeasureTheory.Measu
re α} {f : α → β × γ},   AEMeasurable f μ → AEMeasurable (fun x => (f x).2) μ
参数：fun x => (f x).2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp_aemeasurable`：Measurable.comp_aemeasurable [MeasurableSp
ace δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) : A
EMeasurable (g ∘ f…
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
-/
protected theorem snd {f : α → β × γ} (hf : AEMeasurable f μ) :
    AEMeasurable (fun x ↦ (f x).2) μ :=
  measurable_snd.comp_aemeasurable hf

@[fun_prop]
/-
**AEMeasurable.prodMk** 是 Mathlib 中的一个定理，位于命名空间 `AEMeasurable`。
形式化陈述：prodMk {f : α -> β} {g : α -> γ} (hf : AEMeasurable f μ) (hg : AEMeasurabl
e g μ) : AEMeasurable (fun x => (f x, g x)) μ
参数：hf : AEMeasurable f μ；hg : AEMeasurable g μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
· 使用定理 `AEMeasurable.measurable_mk`：measurable_mk (h : AEMeasurable f μ) : Measu
rable (h.mk f)
· 使用定理 `Filter.EventuallyEq.prodMk`：∀ {α : Type u} {β : Type v} {γ : Type w} {l 
: Filter α} {f f' : α → β},   f =ᶠ[l] f' → ∀ {g g' : α → γ}, g =ᶠ[l] g' → (fun x
 => (f x, g x)) …
· 使用定理 `AEMeasurable.ae_eq_mk`：ae_eq_mk (h : AEMeasurable f μ) : f =ᵐ[μ] h.mk f
-/
theorem prodMk {f : α → β} {g : α → γ} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    AEMeasurable (fun x => (f x, g x)) μ :=
  ⟨fun a => (hf.mk f a, hg.mk g a), hf.measurable_mk.prodMk hg.measurable_mk,
    hf.ae_eq_mk.prodMk hg.ae_eq_mk⟩
/-
**AEMeasurable._root_.nullMeasurableSet_eq_fun** 是 Mathlib 中的一个定理，位于命名空间 `AEMeas
urable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.nullMeasurableSet_eq_fun [MeasurableEq β]
    {f g : α → β} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    NullMeasurableSet { x | f x = g x } μ :=
  (hf.prodMk hg).nullMeasurableSet_preimage measurableSet_diagonal
/-
**AEMeasurable.exists_ae_eq_range_subset** 是 Mathlib 中的一个定理，位于命名空间 `AEMeasurable
`。
形式化陈述：exists_ae_eq_range_subset (H : AEMeasurable f μ) {t : Set β} (ht : forallᵐ
 x ∂μ, f x in t) (h₀ : t.Nonempty) : exists g, Measurable g ∧ range g subseteq t
 ∧ f =ᵐ[μ] g
参数：H : AEMeasurable f μ；ht : forallᵐ x ∂μ, f x in t；h₀ : t.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Measurable.piecewise`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f g :
 α → β} {m : MeasurableSpace α} {mβ : MeasurableSpace β}   {x : DecidablePred fu
n x => x ∈…
· 使用定理 `MeasureTheory.measurableSet_toMeasurable`：measurableSet_toMeasurable (μ 
: Measure α) (s : Set α) : MeasurableSet (toMeasurable μ s)
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `AEMeasurable.measurable_mk`：measurable_mk (h : AEMeasurable f μ) : Measu
rable (h.mk f)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.piecewise_eq_of_mem`：piecewise_eq_of_mem {i : α} (hi : i in s) : s.p
iecewise f g i = f i
· 使用定理 `Set.Nonempty.some_mem`：∀ {α : Type u} {s : Set α} (h : s.Nonempty), h.so
me ∈ s
· 使用定理 `Set.piecewise_eq_of_notMem`：piecewise_eq_of_notMem {i : α} (hi : i ∉ s) 
: s.piecewise f g i = g i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `MeasureTheory.subset_toMeasurable`：subset_toMeasurable (μ : Measure α) (
s : Set α) : s subseteq toMeasurable μ s
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `MeasureTheory.measure_toMeasurable`：measure_toMeasurable (s : Set α) : μ
 (toMeasurable μ s) = μ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.compl_mem_ae_iff`：compl_mem_ae_iff {s : Set α} : sᶜ in ae 
μ ↔ μ s = 0
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `AEMeasurable.ae_eq_mk`：ae_eq_mk (h : AEMeasurable f μ) : f =ᵐ[μ] h.mk f
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Set.mem_compl_iff`：mem_compl_iff (s : Set α) (x : α) : x in sᶜ ↔ x ∉ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
-/
theorem exists_ae_eq_range_subset (H : AEMeasurable f μ) {t : Set β} (ht : ∀ᵐ x ∂μ, f x ∈ t)
    (h₀ : t.Nonempty) : ∃ g, Measurable g ∧ range g ⊆ t ∧ f =ᵐ[μ] g := by
  classical
  let s : Set α := toMeasurable μ { x | f x = H.mk f x ∧ f x ∈ t }ᶜ
  let g : α → β := piecewise s (fun _ => h₀.some) (H.mk f)
  refine ⟨g, ?_, ?_, ?_⟩
  · exact Measurable.piecewise (measurableSet_toMeasurable _ _) measurable_const H.measurable_mk
  · rintro _ ⟨x, rfl⟩
    by_cases hx : x ∈ s
    · simpa [g, hx] using h₀.some_mem
    · simp only [g, hx, piecewise_eq_of_notMem, not_false_iff]
      contrapose hx
      apply subset_toMeasurable
      simp +contextual only [hx, mem_compl_iff, mem_ofPred_eq, not_and,
        not_false_iff, imp_true_iff]
  · have A : μ (toMeasurable μ { x | f x = H.mk f x ∧ f x ∈ t }ᶜ) = 0 := by
      rw [measure_toMeasurable, ← compl_mem_ae_iff, compl_compl]
      exact H.ae_eq_mk.and ht
    filter_upwards [compl_mem_ae_iff.2 A] with x hx
    rw [mem_compl_iff] at hx
    simp only [s, g, hx, piecewise_eq_of_notMem, not_false_iff]
    contrapose! hx
    apply subset_toMeasurable
    simp only [hx, mem_compl_iff, mem_ofPred_eq, false_and, not_false_iff]
/-
**AEMeasurable.exists_measurable_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `AEMeasurable`
。
形式化陈述：exists_measurable_nonneg {β} [Preorder β] [Zero β] {mβ : MeasurableSpace β
} {f : α -> β} (hf : AEMeasurable f μ) (f_nn : forallᵐ t ∂μ, 0 <= f t) : exists 
g, Measurable g ∧ 0 <= g ∧ f =ᵐ[μ] g
参数：hf : AEMeasurable f μ；f_nn : forallᵐ t ∂μ, 0 <= f t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `AEMeasurable.exists_ae_eq_range_subset`：exists_ae_eq_range_subset (H : A
EMeasurable f μ) {t : Set β} (ht : forallᵐ x ∂μ, f x in t) (h₀ : t.Nonempty) : e
xists g, Measurable g ∧ rang…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
-/
theorem exists_measurable_nonneg {β} [Preorder β] [Zero β] {mβ : MeasurableSpace β} {f : α → β}
    (hf : AEMeasurable f μ) (f_nn : ∀ᵐ t ∂μ, 0 ≤ f t) : ∃ g, Measurable g ∧ 0 ≤ g ∧ f =ᵐ[μ] g := by
  obtain ⟨G, hG_meas, hG_mem, hG_ae_eq⟩ := hf.exists_ae_eq_range_subset f_nn ⟨0, le_rfl⟩
  exact ⟨G, hG_meas, fun x => hG_mem (mem_range_self x), hG_ae_eq⟩
/-
**AEMeasurable.subtype_mk** 是 Mathlib 中的一个定理，位于命名空间 `AEMeasurable`。
形式化陈述：subtype_mk (h : AEMeasurable f μ) {s : Set β} {hfs : forall x, f x in s} :
 AEMeasurable (codRestrict f s hfs) μ
参数：h : AEMeasurable f μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `AEMeasurable.exists_ae_eq_range_subset`：exists_ae_eq_range_subset (H : A
EMeasurable f μ) {t : Set β} (ht : forallᵐ x ∂μ, f x in t) (h₀ : t.Nonempty) : e
xists g, Measurable g ∧ rang…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `Measurable.subtype_mk`：Measurable.subtype_mk {p : β -> Prop} {f : α -> β
} (hf : Measurable f) {h : forall x, p (f x)} : Measurable fun x => (⟨f x, h x⟩ 
: Subtype p…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
-/
theorem subtype_mk (h : AEMeasurable f μ) {s : Set β} {hfs : ∀ x, f x ∈ s} :
    AEMeasurable (codRestrict f s hfs) μ := by
  nontriviality α; inhabit α
  obtain ⟨g, g_meas, hg, fg⟩ : ∃ g : α → β, Measurable g ∧ range g ⊆ s ∧ f =ᵐ[μ] g :=
    h.exists_ae_eq_range_subset (Eventually.of_forall hfs) ⟨_, hfs default⟩
  refine ⟨codRestrict g s fun x => hg (mem_range_self _), Measurable.subtype_mk g_meas, ?_⟩
  filter_upwards [fg] with x hx
  simpa [Subtype.ext_iff]

end AEMeasurable

/-
**aemeasurable_const'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：aemeasurable_const' (h : forallᵐ (x) (y) ∂μ, f x = f y) : AEMeasurable f μ
参数：h : forallᵐ (x) (y) ∂μ, f x = f y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `aemeasurable_zero_measure`：aemeasurable_zero_measure : AEMeasurable f (0
 : Measure α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.ae_neBot`：ae_neBot : (ae μ).NeBot ↔ μ != 0
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
theorem aemeasurable_const' (h : ∀ᵐ (x) (y) ∂μ, f x = f y) : AEMeasurable f μ := by
  rcases eq_or_ne μ 0 with (rfl | hμ)
  · exact aemeasurable_zero_measure
  · have := ae_neBot.2 hμ
    rcases h.exists with ⟨x, hx⟩
    exact ⟨const α (f x), measurable_const, EventuallyEq.symm hx⟩

open scoped Interval in
/-
**aemeasurable_uIoc_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：aemeasurable_uIoc_iff [LinearOrder α] {f : α -> β} {a b : α} : (AEMeasurab
le f <| μ.restrict <| Ι a b) ↔ (AEMeasurable f <| μ.restrict <| Ioc a b) ∧ (AEMe
asurable f <| μ.restrict <| Ioc b a)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.uIoc_eq_union`：uIoc_eq_union : Ι a b = Ioc a b union Ioc b a
· 使用定理 `aemeasurable_union_iff`：∀ {α : Type u_2} {β : Type u_3} {m0 : Measurable
Space α} [inst : MeasurableSpace β] {f : α → β}   {μ : MeasureTheory.Measure α} 
{s t : Set α…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem aemeasurable_uIoc_iff [LinearOrder α] {f : α → β} {a b : α} :
    (AEMeasurable f <| μ.restrict <| Ι a b) ↔
      (AEMeasurable f <| μ.restrict <| Ioc a b) ∧ (AEMeasurable f <| μ.restrict <| Ioc b a) := by
  rw [uIoc_eq_union, aemeasurable_union_iff]
/-
**aemeasurable_iff_measurable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：aemeasurable_iff_measurable [μ.IsComplete] : AEMeasurable f μ ↔ Measurable
 f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.NullMeasurable.measurable_of_complete`：∀ {α : Type u_2} {β
 : Type u_3} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [μ.IsComplet
e]   {_m1 : MeasurableSpace β} {f : α → β…
· 使用定理 `AEMeasurable.nullMeasurable`：∀ {α : Type u_1} {β : Type u_2} {m0 : Measu
rableSpace α} {mβ : MeasurableSpace β} {μ : MeasureTheory.Measure α}   {f : α → 
β}, AEMeasurable …
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
-/
theorem aemeasurable_iff_measurable [μ.IsComplete] : AEMeasurable f μ ↔ Measurable f :=
  ⟨fun h => h.nullMeasurable.measurable_of_complete, fun h => h.aemeasurable⟩
/-
**MeasurableEmbedding.aemeasurable_map_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeasurableEmbedding.aemeasurable_map_iff {g : β -> γ} (hf : MeasurableEmbe
dding f) : AEMeasurable g (μ.map f) ↔ AEMeasurable (g ∘ f) μ
参数：hf : MeasurableEmbedding f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AEMeasurable.comp_measurable`：comp_measurable {f : α -> δ} {g : δ -> β} 
(hg : AEMeasurable g (μ.map f)) (hf : Measurable f) : AEMeasurable (g ∘ f) μ
· 使用定理 `MeasurableEmbedding.measurable`：∀ {α : Type u_1} {β : Type u_2} [inst : 
MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β},   MeasurableEmbeddi
ng f → Measurable f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasurableEmbedding.exists_measurable_extend`：exists_measurable_extend (
hf : MeasurableEmbedding f) {g : α -> γ} (hg : Measurable g) (hne : β -> Nonempt
y γ) : exists g' : β -> γ, Measura…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasurableEmbedding.ae_map_iff`：ae_map_iff {p : β -> Prop} {μ : Measure 
α} : (forallᵐ x ∂μ.map f, p x) ↔ forallᵐ x ∂μ, p (f x)
-/
theorem MeasurableEmbedding.aemeasurable_map_iff {g : β → γ} (hf : MeasurableEmbedding f) :
    AEMeasurable g (μ.map f) ↔ AEMeasurable (g ∘ f) μ := by
  refine ⟨fun H => H.comp_measurable hf.measurable, ?_⟩
  rintro ⟨g₁, hgm₁, heq⟩
  rcases hf.exists_measurable_extend hgm₁ fun x => ⟨g x⟩ with ⟨g₂, hgm₂, rfl⟩
  exact ⟨g₂, hgm₂, hf.ae_map_iff.2 heq⟩
/-
**MeasurableEmbedding.aemeasurable_comp_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeasurableEmbedding.aemeasurable_comp_iff {g : β -> γ} (hg : MeasurableEmb
edding g) {μ : Measure α} : AEMeasurable (g ∘ f) μ ↔ AEMeasurable f μ
参数：hg : MeasurableEmbedding g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp_aemeasurable`：Measurable.comp_aemeasurable [MeasurableSp
ace δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) : A
EMeasurable (g ∘ f…
· 使用定理 `MeasurableEmbedding.measurable_rangeSplitting`：measurable_rangeSplitting
 (hf : MeasurableEmbedding f) : Measurable (rangeSplitting f)
· 使用定理 `AEMeasurable.subtype_mk`：subtype_mk (h : AEMeasurable f μ) {s : Set β} {
hfs : forall x, f x in s} : AEMeasurable (codRestrict f s hfs) μ
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.RightInverse.comp_eq_id`：∀ {α : Sort u_1} {β : Sort u_2} {f : α
 → β} {g : β → α}, Function.RightInverse f g → g ∘ f = id
· 使用定理 `Set.rightInverse_rangeSplitting`：rightInverse_rangeSplitting {f : α -> β
} (h : Injective f) : RightInverse (rangeFactorization f) (rangeSplitting f)
· 使用定理 `MeasurableEmbedding.injective`：∀ {α : Type u_1} {β : Type u_2} [inst : M
easurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β},   MeasurableEmbeddin
g f → Function.Inje…
· 使用定理 `MeasurableEmbedding.measurable`：∀ {α : Type u_1} {β : Type u_2} [inst : 
MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β},   MeasurableEmbeddi
ng f → Measurable f
-/
theorem MeasurableEmbedding.aemeasurable_comp_iff {g : β → γ} (hg : MeasurableEmbedding g)
    {μ : Measure α} : AEMeasurable (g ∘ f) μ ↔ AEMeasurable f μ := by
  refine ⟨fun H => ?_, hg.measurable.comp_aemeasurable⟩
  suffices AEMeasurable ((rangeSplitting g ∘ rangeFactorization g) ∘ f) μ by
    rwa [(rightInverse_rangeSplitting hg.injective).comp_eq_id] at this
  exact hg.measurable_rangeSplitting.comp_aemeasurable H.subtype_mk
/-
**aemeasurable_restrict_iff_comap_subtype** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：aemeasurable_restrict_iff_comap_subtype {s : Set α} (hs : MeasurableSet s)
 {μ : Measure α} {f : α -> β} : AEMeasurable f (μ.restrict s) ↔ AEMeasurable (f 
∘ (↑) : s -> β) (comap (↑) μ)
参数：hs : MeasurableSet s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_comap_subtype_coe`：map_comap_subtype_coe {m0 : MeasurableSpace α} {s
 : Set α} (hs : MeasurableSet s) (μ : Measure α) : (comap (↑) μ).map ((↑) : s ->
 α) = μ.res…
· 使用定理 `MeasurableEmbedding.aemeasurable_map_iff`：MeasurableEmbedding.aemeasurab
le_map_iff {g : β -> γ} (hf : MeasurableEmbedding f) : AEMeasurable g (μ.map f) 
↔ AEMeasurable (g ∘ f) μ
· 使用定理 `MeasurableEmbedding.subtype_coe`：subtype_coe (hs : MeasurableSet s) : Me
asurableEmbedding ((↑) : s -> α) where injective
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem aemeasurable_restrict_iff_comap_subtype {s : Set α} (hs : MeasurableSet s) {μ : Measure α}
    {f : α → β} : AEMeasurable f (μ.restrict s) ↔ AEMeasurable (f ∘ (↑) : s → β) (comap (↑) μ) := by
  rw [← map_comap_subtype_coe hs, (MeasurableEmbedding.subtype_coe hs).aemeasurable_map_iff]

@[to_additive]
/-
**aemeasurable_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：aemeasurable_one [One β] : AEMeasurable (fun _ : α => (1 : β)) μ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `measurable_one`：measurable_one [One α] : Measurable (1 : β -> α)
-/
theorem aemeasurable_one [One β] : AEMeasurable (fun _ : α => (1 : β)) μ :=
  measurable_one.aemeasurable

@[simp]
/-
**aemeasurable_smul_measure_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：aemeasurable_smul_measure_iff {c : Real>=0∞} (hc : c != 0) : AEMeasurable 
f (c • μ) ↔ AEMeasurable f μ
参数：hc : c != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `AEMeasurable.measurable_mk`：measurable_mk (h : AEMeasurable f μ) : Measu
rable (h.mk f)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `MeasureTheory.Measure.ae_ennreal_smul_measure_iff`：ae_ennreal_smul_measu
re_iff {c : Real>=0∞} {p : α -> Prop} (hc : c != 0) {μ : Measure α} : (forallᵐ x
 ∂c • μ, p x) ↔ forallᵐ x ∂μ, p x
· 使用定理 `AEMeasurable.ae_eq_mk`：ae_eq_mk (h : AEMeasurable f μ) : f =ᵐ[μ] h.mk f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem aemeasurable_smul_measure_iff {c : ℝ≥0∞} (hc : c ≠ 0) :
    AEMeasurable f (c • μ) ↔ AEMeasurable f μ :=
  ⟨fun h => ⟨h.mk f, h.measurable_mk, (ae_ennreal_smul_measure_iff hc).1 h.ae_eq_mk⟩, fun h =>
    ⟨h.mk f, h.measurable_mk, (ae_ennreal_smul_measure_iff hc).2 h.ae_eq_mk⟩⟩
/-
**aemeasurable_of_aemeasurable_trim** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：aemeasurable_of_aemeasurable_trim {α} {m m0 : MeasurableSpace α} {μ : Meas
ure α} (hm : m <= m0) {f : α -> β} (hf : AEMeasurable f (μ.trim hm)) : AEMeasura
ble f μ
参数：hm : m <= m0；hf : AEMeasurable f (μ.trim hm)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Measurable.mono`：Measurable.mono {ma ma' : MeasurableSpace α} {mb mb' : 
MeasurableSpace β} {f : α -> β} (hf : @Measurable α β ma mb f) (ha : ma <= ma') 
(hb :…
· 使用定理 `AEMeasurable.measurable_mk`：measurable_mk (h : AEMeasurable f μ) : Measu
rable (h.mk f)
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `MeasureTheory.ae_eq_of_ae_eq_trim`：ae_eq_of_ae_eq_trim {E} {hm : m <= m0
} {f₁ f₂ : α -> E} (h12 : f₁ =ᵐ[μ.trim hm] f₂) : f₁ =ᵐ[μ] f₂
· 使用定理 `AEMeasurable.ae_eq_mk`：ae_eq_mk (h : AEMeasurable f μ) : f =ᵐ[μ] h.mk f
-/
theorem aemeasurable_of_aemeasurable_trim {α} {m m0 : MeasurableSpace α} {μ : Measure α}
    (hm : m ≤ m0) {f : α → β} (hf : AEMeasurable f (μ.trim hm)) : AEMeasurable f μ :=
  ⟨hf.mk f, Measurable.mono hf.measurable_mk hm le_rfl, ae_eq_of_ae_eq_trim hf.ae_eq_mk⟩
/-
**aemeasurable_restrict_of_measurable_subtype** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：aemeasurable_restrict_of_measurable_subtype {s : Set α} (hs : MeasurableSe
t s) (hf : Measurable fun x : s => f x) : AEMeasurable f (μ.restrict s)
参数：hs : MeasurableSet s；hf : Measurable fun x : s => f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `aemeasurable_restrict_iff_comap_subtype`：aemeasurable_restrict_iff_comap
_subtype {s : Set α} (hs : MeasurableSet s) {μ : Measure α} {f : α -> β} : AEMea
surable f (μ.restrict s) ↔ AE…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
-/
theorem aemeasurable_restrict_of_measurable_subtype {s : Set α} (hs : MeasurableSet s)
    (hf : Measurable fun x : s => f x) : AEMeasurable f (μ.restrict s) :=
  (aemeasurable_restrict_iff_comap_subtype hs).2 hf.aemeasurable
/-
**aemeasurable_map_equiv_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：aemeasurable_map_equiv_iff (e : α ≃ᵐ β) {f : β -> γ} : AEMeasurable f (μ.m
ap e) ↔ AEMeasurable (f ∘ e) μ
参数：e : α ≃ᵐ β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableEmbedding.aemeasurable_map_iff`：MeasurableEmbedding.aemeasurab
le_map_iff {g : β -> γ} (hf : MeasurableEmbedding f) : AEMeasurable g (μ.map f) 
↔ AEMeasurable (g ∘ f) μ
· 使用定理 `MeasurableEquiv.measurableEmbedding`：∀ {α : Type u_1} {β : Type u_2} [in
st : MeasurableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β),   MeasurableE
mbedding ⇑e
-/
theorem aemeasurable_map_equiv_iff (e : α ≃ᵐ β) {f : β → γ} :
    AEMeasurable f (μ.map e) ↔ AEMeasurable (f ∘ e) μ :=
  e.measurableEmbedding.aemeasurable_map_iff

end

@[fun_prop]
/-
**AEMeasurable.restrict** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AEMeasurable.restrict (hfm : AEMeasurable f μ) {s} : AEMeasurable f (μ.res
trict s)
参数：hfm : AEMeasurable f μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `AEMeasurable.measurable_mk`：measurable_mk (h : AEMeasurable f μ) : Measu
rable (h.mk f)
· 使用定理 `MeasureTheory.ae_restrict_of_ae`：ae_restrict_of_ae {s : Set α} {p : α ->
 Prop} (h : forallᵐ x ∂μ, p x) : forallᵐ x ∂μ.restrict s, p x
· 使用定理 `AEMeasurable.ae_eq_mk`：ae_eq_mk (h : AEMeasurable f μ) : f =ᵐ[μ] h.mk f
-/
theorem AEMeasurable.restrict (hfm : AEMeasurable f μ) {s} : AEMeasurable f (μ.restrict s) :=
  ⟨AEMeasurable.mk f hfm, hfm.measurable_mk, ae_restrict_of_ae hfm.ae_eq_mk⟩
/-
**aemeasurable_Ioi_of_forall_Ioc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：aemeasurable_Ioi_of_forall_Ioc {β} {mβ : MeasurableSpace β} [LinearOrder α
] [(atTop : Filter α).IsCountablyGenerated] {x : α} {g : α -> β} (g_meas : foral
l t > x, AEMeasurable g (μ.restrict (Ioc x t))) : AEMeasurable g (μ.restrict (Io
i x))
参数：atTop : Filter α；g_meas : forall t > x, AEMeasurable g (μ.restrict (Ioc x t))
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.exists_seq_tendsto`：exists_seq_tendsto (f : Filter α) [IsCountabl
yGenerated f] [NeBot f] : exists x : Nat -> α, Tendsto x atTop f
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.iUnion_Ioc_eq_Ioi_self_iff`：iUnion_Ioc_eq_Ioi_self_iff {f : ι -> α} 
{a : α} : ⋃ i, Ioc a (f i) = Ioi a ↔ forall x, a < x -> exists i, x <= f i
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
· 使用定理 `aemeasurable_iUnion_iff`：∀ {ι : Type u_1} {α : Type u_2} {β : Type u_3} 
{m0 : MeasurableSpace α} [inst : MeasurableSpace β] {f : α → β}   {μ : MeasureTh
eory.Measure …
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `Set.Ioc_eq_empty`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, ¬b < a
 → Set.Ioc b a = ∅
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `MeasureTheory.Measure.restrict_empty`：restrict_empty : μ.restrict ∅ = 0
· 使用定理 `aemeasurable_zero_measure`：aemeasurable_zero_measure : AEMeasurable f (0
 : Measure α)
-/
theorem aemeasurable_Ioi_of_forall_Ioc {β} {mβ : MeasurableSpace β} [LinearOrder α]
    [(atTop : Filter α).IsCountablyGenerated] {x : α} {g : α → β}
    (g_meas : ∀ t > x, AEMeasurable g (μ.restrict (Ioc x t))) :
    AEMeasurable g (μ.restrict (Ioi x)) := by
  have : Nonempty α := ⟨x⟩
  obtain ⟨u, hu_tendsto⟩ := exists_seq_tendsto (atTop : Filter α)
  have Ioi_eq_iUnion : Ioi x = ⋃ n : ℕ, Ioc x (u n) := by
    rw [iUnion_Ioc_eq_Ioi_self_iff.mpr _]
    exact fun y _ => (hu_tendsto.eventually (eventually_ge_atTop y)).exists
  rw [Ioi_eq_iUnion, aemeasurable_iUnion_iff]
  intro n
  rcases lt_or_ge x (u n) with h | h
  · exact g_meas (u n) h
  · rw [Ioc_eq_empty (not_lt.mpr h), Measure.restrict_empty]
    exact aemeasurable_zero_measure

section Zero

variable [Zero β]

/-
**aemeasurable_indicator_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：aemeasurable_indicator_iff {s} (hs : MeasurableSet s) : AEMeasurable (indi
cator s f) μ ↔ AEMeasurable f (μ.restrict s)
参数：hs : MeasurableSet s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AEMeasurable.congr`：congr (hf : AEMeasurable f μ) (h : f =ᵐ[μ] g) : AEMe
asurable g μ
· 使用定理 `AEMeasurable.mono_measure`：mono_measure (h : AEMeasurable f μ) (h' : ν <
= μ) : AEMeasurable f ν
· 使用定理 `MeasureTheory.Measure.restrict_le_self`：restrict_le_self : μ.restrict s 
<= μ
· 使用定理 `indicator_ae_eq_restrict`：indicator_ae_eq_restrict (hs : MeasurableSet s
) : indicator s f =ᵐ[μ.restrict s] f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Measurable.indicator`：Measurable.indicator [Zero β] (hf : Measurable f) 
(hs : MeasurableSet s) : Measurable (s.indicator f)
· 使用定理 `AEMeasurable.measurable_mk`：measurable_mk (h : AEMeasurable f μ) : Measu
rable (h.mk f)
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `AEMeasurable.ae_eq_mk`：ae_eq_mk (h : AEMeasurable f μ) : f =ᵐ[μ] h.mk f
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `indicator_ae_eq_restrict_compl`：indicator_ae_eq_restrict_compl (hs : Mea
surableSet s) : indicator s f =ᵐ[μ.restrict sᶜ] 0
· 使用定理 `MeasureTheory.ae_of_ae_restrict_of_ae_restrict_compl`：ae_of_ae_restrict_
of_ae_restrict_compl (t : Set α) {p : α -> Prop} (ht : forallᵐ x ∂μ.restrict t, 
p x) (htc : forallᵐ x ∂μ.restrict tᶜ, p x)…
-/
theorem aemeasurable_indicator_iff {s} (hs : MeasurableSet s) :
    AEMeasurable (indicator s f) μ ↔ AEMeasurable f (μ.restrict s) := by
  constructor
  · intro h
    exact (h.mono_measure Measure.restrict_le_self).congr (indicator_ae_eq_restrict hs)
  · intro h
    refine ⟨indicator s (h.mk f), h.measurable_mk.indicator hs, ?_⟩
    have A : s.indicator f =ᵐ[μ.restrict s] s.indicator (AEMeasurable.mk f h) :=
      (indicator_ae_eq_restrict hs).trans (h.ae_eq_mk.trans <| (indicator_ae_eq_restrict hs).symm)
    have B : s.indicator f =ᵐ[μ.restrict sᶜ] s.indicator (AEMeasurable.mk f h) :=
      (indicator_ae_eq_restrict_compl hs).trans (indicator_ae_eq_restrict_compl hs).symm
    exact ae_of_ae_restrict_of_ae_restrict_compl _ A B
/-
**aemeasurable_indicator_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：aemeasurable_indicator_iff {s} (hs : MeasurableSet s) : AEMeasurable (indi
cator s f) μ ↔ AEMeasurable f (μ.restrict s)
参数：hs : MeasurableSet s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AEMeasurable.congr`：congr (hf : AEMeasurable f μ) (h : f =ᵐ[μ] g) : AEMe
asurable g μ
· 使用定理 `AEMeasurable.mono_measure`：mono_measure (h : AEMeasurable f μ) (h' : ν <
= μ) : AEMeasurable f ν
· 使用定理 `MeasureTheory.Measure.restrict_le_self`：restrict_le_self : μ.restrict s 
<= μ
· 使用定理 `indicator_ae_eq_restrict`：indicator_ae_eq_restrict (hs : MeasurableSet s
) : indicator s f =ᵐ[μ.restrict s] f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Measurable.indicator`：Measurable.indicator [Zero β] (hf : Measurable f) 
(hs : MeasurableSet s) : Measurable (s.indicator f)
· 使用定理 `AEMeasurable.measurable_mk`：measurable_mk (h : AEMeasurable f μ) : Measu
rable (h.mk f)
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `AEMeasurable.ae_eq_mk`：ae_eq_mk (h : AEMeasurable f μ) : f =ᵐ[μ] h.mk f
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `indicator_ae_eq_restrict_compl`：indicator_ae_eq_restrict_compl (hs : Mea
surableSet s) : indicator s f =ᵐ[μ.restrict sᶜ] 0
· 使用定理 `MeasureTheory.ae_of_ae_restrict_of_ae_restrict_compl`：ae_of_ae_restrict_
of_ae_restrict_compl (t : Set α) {p : α -> Prop} (ht : forallᵐ x ∂μ.restrict t, 
p x) (htc : forallᵐ x ∂μ.restrict tᶜ, p x)…
-/
theorem aemeasurable_indicator_iff₀ {s} (hs : NullMeasurableSet s μ) :
    AEMeasurable (indicator s f) μ ↔ AEMeasurable f (μ.restrict s) := by
  rcases hs with ⟨t, ht, hst⟩
  rw [← aemeasurable_congr (indicator_ae_eq_of_ae_eq_set hst.symm), aemeasurable_indicator_iff ht,
      restrict_congr_set hst]

/-- A characterization of the a.e.-measurability of the indicator function which takes a constant
value `b` on a set `A` and `0` elsewhere. -/
/-
**aemeasurable_indicator_const_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：aemeasurable_indicator_const_iff {s} [MeasurableSingletonClass β] (b : β) 
[NeZero b] : AEMeasurable (s.indicator (fun _ => b)) μ ↔ NullMeasurableSet s μ
参数：b : β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.indicator_const_preimage_eq_union`：∀ {α : Type u_1} {M : Type u_3} [
inst : Zero M] (U : Set α) (s : Set M) (a : M) [inst_1 : Decidable (a ∈ s)]   [i
nst_2 : Decidable (0 ∈ s)],…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Set.union_empty`：union_empty (a : Set α) : a union ∅ = a
· 使用定理 `AEMeasurable.nullMeasurable`：∀ {α : Type u_1} {β : Type u_2} {m0 : Measu
rableSpace α} {mβ : MeasurableSpace β} {μ : MeasureTheory.Measure α}   {f : α → 
β}, AEMeasurable …
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用引理 `MeasurableSet.singleton`：MeasurableSet.singleton [MeasurableSpace α] [Me
asurableSingletonClass α] (a : α) : MeasurableSet {a}
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `aemeasurable_indicator_iff₀`：aemeasurable_indicator_iff₀ {s} (hs : NullM
easurableSet s μ) : AEMeasurable (indicator s f) μ ↔ AEMeasurable f (μ.restrict 
s)
· 使用定理 `aemeasurable_const`：aemeasurable_const {b : β} : AEMeasurable (fun _a : 
α => b) μ

--- 原说明 ---
A characterization of the a.e.-measurability of the indicator function which tak
es a constant
value `b` on a set `A` and `0` elsewhere.
-/
lemma aemeasurable_indicator_const_iff {s} [MeasurableSingletonClass β] (b : β) [NeZero b] :
    AEMeasurable (s.indicator (fun _ ↦ b)) μ ↔ NullMeasurableSet s μ := by
  classical
  constructor <;> intro h
  · convert! h.nullMeasurable (MeasurableSet.singleton (0 : β)).compl
    rw [indicator_const_preimage_eq_union s {0}ᶜ b]
    simp [NeZero.ne b]
  · exact (aemeasurable_indicator_iff₀ h).mpr aemeasurable_const

@[fun_prop]
/-
**AEMeasurable.indicator** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AEMeasurable.indicator (hfm : AEMeasurable f μ) {s} (hs : MeasurableSet s)
 : AEMeasurable (s.indicator f) μ
参数：hfm : AEMeasurable f μ；hs : MeasurableSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `aemeasurable_indicator_iff`：aemeasurable_indicator_iff {s} (hs : Measura
bleSet s) : AEMeasurable (indicator s f) μ ↔ AEMeasurable f (μ.restrict s)
· 使用定理 `AEMeasurable.restrict`：AEMeasurable.restrict (hfm : AEMeasurable f μ) {s
} : AEMeasurable f (μ.restrict s)
-/
theorem AEMeasurable.indicator (hfm : AEMeasurable f μ) {s} (hs : MeasurableSet s) :
    AEMeasurable (s.indicator f) μ :=
  (aemeasurable_indicator_iff hs).mpr hfm.restrict
/-
**AEMeasurable.indicator** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AEMeasurable.indicator (hfm : AEMeasurable f μ) {s} (hs : MeasurableSet s)
 : AEMeasurable (s.indicator f) μ
参数：hfm : AEMeasurable f μ；hs : MeasurableSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `aemeasurable_indicator_iff`：aemeasurable_indicator_iff {s} (hs : Measura
bleSet s) : AEMeasurable (indicator s f) μ ↔ AEMeasurable f (μ.restrict s)
· 使用定理 `AEMeasurable.restrict`：AEMeasurable.restrict (hfm : AEMeasurable f μ) {s
} : AEMeasurable f (μ.restrict s)
-/
theorem AEMeasurable.indicator₀ (hfm : AEMeasurable f μ) {s} (hs : NullMeasurableSet s μ) :
    AEMeasurable (s.indicator f) μ :=
  (aemeasurable_indicator_iff₀ hs).mpr hfm.restrict

end Zero

/-
**MeasureTheory.Measure.restrict_map_of_aemeasurable** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：MeasureTheory.Measure.restrict_map_of_aemeasurable {f : α -> δ} (hf : AEMe
asurable f μ) {s : Set δ} (hs : MeasurableSet s) : (μ.map f).restrict s = (μ.res
trict <| f ⁻¹' s).map f
参数：hf : AEMeasurable f μ；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.map_congr`：map_congr {f g : α -> β} (h : f =ᵐ[μ] g
) : Measure.map f μ = Measure.map g μ
· 使用定理 `AEMeasurable.ae_eq_mk`：ae_eq_mk (h : AEMeasurable f μ) : f =ᵐ[μ] h.mk f
· 使用定理 `MeasureTheory.Measure.restrict_map`：restrict_map {f : α -> β} (hf : Meas
urable f) {s : Set β} (hs : MeasurableSet s) : (μ.map f).restrict s = (μ.restric
t <| f ⁻¹' s).map f
· 使用定理 `AEMeasurable.measurable_mk`：measurable_mk (h : AEMeasurable f μ) : Measu
rable (h.mk f)
· 使用定理 `MeasureTheory.ae_restrict_of_ae`：ae_restrict_of_ae {s : Set α} {p : α ->
 Prop} (h : forallᵐ x ∂μ, p x) : forallᵐ x ∂μ.restrict s, p x
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `MeasureTheory.measure_congr`：measure_congr (H : s =ᵐ[μ] t) : μ s = μ t
· 使用定理 `Filter.EventuallyEq.inter`：∀ {α : Type u} {s t s' t' : Set α} {l : Filte
r α}, s =ᶠ[l] t → s' =ᶠ[l] t' → s ∩ s' =ᶠ[l] t ∩ t'
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
· 使用定理 `Filter.EventuallyEq.preimage`：∀ {α : Type u} {β : Type v} {l : Filter α}
 {f g : α → β}, f =ᶠ[l] g → ∀ (s : Set β), f ⁻¹' s =ᶠ[l] g ⁻¹' s
-/
theorem MeasureTheory.Measure.restrict_map_of_aemeasurable {f : α → δ} (hf : AEMeasurable f μ)
    {s : Set δ} (hs : MeasurableSet s) : (μ.map f).restrict s = (μ.restrict <| f ⁻¹' s).map f :=
  calc
    (μ.map f).restrict s = (μ.map (hf.mk f)).restrict s := by
      congr 1
      apply Measure.map_congr hf.ae_eq_mk
    _ = (μ.restrict <| hf.mk f ⁻¹' s).map (hf.mk f) := Measure.restrict_map hf.measurable_mk hs
    _ = (μ.restrict <| hf.mk f ⁻¹' s).map f :=
      (Measure.map_congr (ae_restrict_of_ae hf.ae_eq_mk.symm))
    _ = (μ.restrict <| f ⁻¹' s).map f := by
      apply congr_arg
      ext1 t ht
      simp only [ht, Measure.restrict_apply]
      apply measure_congr
      apply (EventuallyEq.refl _ _).inter (hf.ae_eq_mk.symm.preimage s)
/-
**MeasureTheory.Measure.map_mono_of_aemeasurable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeasureTheory.Measure.map_mono_of_aemeasurable {f : α -> δ} (h : μ <= ν) (
hf : AEMeasurable f ν) : μ.map f <= ν.map f
参数：h : μ <= ν；hf : AEMeasurable f ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.le_iff`：le_iff : μ₁ <= μ₂ ↔ forall s, MeasurableSe
t s -> μ₁ s <= μ₂ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_apply_of_aemeasurable`：map_apply_of_aemeasurab
le (hf : AEMeasurable f μ) {s : Set β} (hs : MeasurableSet s) : μ.map f s = μ (f
 ⁻¹' s)
· 使用定理 `AEMeasurable.mono_measure`：mono_measure (h : AEMeasurable f μ) (h' : ν <
= μ) : AEMeasurable f ν
-/
theorem MeasureTheory.Measure.map_mono_of_aemeasurable {f : α → δ} (h : μ ≤ ν)
    (hf : AEMeasurable f ν) : μ.map f ≤ ν.map f :=
  le_iff.2 fun s hs ↦ by simpa [hf, hs, hf.mono_measure h] using h (f ⁻¹' s)

/-- If the `σ`-algebra of the codomain of a null measurable function is countably generated,
then the function is a.e.-measurable. -/
/-
**MeasureTheory.NullMeasurable.aemeasurable** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MeasureTheory.NullMeasurable.aemeasurable {f : α -> β} [hc : MeasurableSpa
ce.CountablyGenerated β] (h : NullMeasurable f μ) : AEMeasurable f μ
参数：h : NullMeasurable f μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasurableSpace.CountablyGenerated.isCountablyGenerated`：∀ {α : Type u_3
} {m : MeasurableSpace α} [self : MeasurableSpace.CountablyGenerated α],   ∃ b, 
b.Countable ∧ m = MeasurableSpace.generateFro…
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasurableSet.biUnion`：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSp
ace α} {f : β → Set α} {s : Set β},   s.Countable → (∀ b ∈ s, MeasurableSet (f b
)) → Measur…
· 使用定理 `MeasurableSet.diff`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : Se
t α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ \ s₂)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.measure_biUnion_null_iff`：measure_biUnion_null_iff {I : Se
t ι} (hI : I.Countable) {s : ι -> Set α} : μ (⋃ i in I, s i) = 0 ↔ forall i in I
, μ (s i) = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.ae_le_set`：ae_le_set : s <=ᵐ[μ] t ↔ μ (s \ t) = 0
· 使用定理 `Filter.EventuallyEq.le`：∀ {α : Type u} {β : Type v} [inst : Preorder β] 
{l : Filter α} {f g : α → β}, f =ᶠ[l] g → f ≤ᶠ[l] g
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `measurable_of_restrict_of_restrict_compl`：measurable_of_restrict_of_rest
rict_compl {f : α -> β} {s : Set α} (hs : MeasurableSet s) (h₁ : Measurable (s.d
omRestrict f)) (h₂ : Measurabl…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.domRestrict_piecewise`：domRestrict_piecewise (f g : α -> β) (s : Set
 α) [forall x, Decidable (x in s)] : s.domRestrict (piecewise s f g) = s.domRest
rict f
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `Set.domRestrict_piecewise_compl`：domRestrict_piecewise_compl (f g : α ->
 β) (s : Set α) [forall x, Decidable (x in s)] : sᶜ.domRestrict (piecewise s f g
) = sᶜ.domRestrict g
· 使用定理 `Set.domRestrict_eq`：domRestrict_eq (f : α -> β) (s : Set α) : s.domRestr
ict f = f ∘ Subtype.val
· 使用定理 `measurable_generateFrom`：measurable_generateFrom [MeasurableSpace α] {s 
: Set (Set β)} {f : α -> β} (h : forall t in s, MeasurableSet (f ⁻¹' t)) : @Meas
urable _ _ _ …
· 使用定理 `MeasurableSet.of_subtype_image`：MeasurableSet.of_subtype_image {s : Set 
α} {t : Set s} (h : MeasurableSet (Subtype.val '' t)) : MeasurableSet t
· 使用定理 `Set.preimage_comp`：preimage_comp {s : Set γ} : g ∘ f ⁻¹' s = f ⁻¹' g ⁻¹'
 s
· 使用定理 `Subtype.image_preimage_coe`：image_preimage_coe (s t : Set α) : ((↑) : s 
-> α) '' ((↑) : s -> α) ⁻¹' t = s inter t
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
（共 41 条，此处仅展示前 30 条）

--- 原说明 ---
If the `σ`-algebra of the codomain of a null measurable function is countably ge
nerated,
then the function is a.e.-measurable.
-/
lemma MeasureTheory.NullMeasurable.aemeasurable {f : α → β}
    [hc : MeasurableSpace.CountablyGenerated β] (h : NullMeasurable f μ) : AEMeasurable f μ := by
  classical
  nontriviality β; inhabit β
  rcases hc.1 with ⟨S, hSc, rfl⟩
  choose! T hTf hTm hTeq using fun s hs ↦ (h <| .basic s hs).exists_measurable_subset_ae_eq
  choose! U hUf hUm hUeq using fun s hs ↦ (h <| .basic s hs).exists_measurable_superset_ae_eq
  set v := ⋃ s ∈ S, U s \ T s
  have hvm : MeasurableSet v := .biUnion hSc fun s hs ↦ (hUm s hs).diff (hTm s hs)
  have hvμ : μ v = 0 := (measure_biUnion_null_iff hSc).2 fun s hs ↦ ae_le_set.1 <|
    ((hUeq s hs).trans (hTeq s hs).symm).le
  refine ⟨v.piecewise (fun _ ↦ default) f, ?_, measure_mono_null (fun x ↦
    not_imp_comm.2 fun hxv ↦ (piecewise_eq_of_notMem _ _ _ hxv).symm) hvμ⟩
  refine measurable_of_restrict_of_restrict_compl hvm ?_ ?_
  · rw [domRestrict_piecewise]
    apply measurable_const
  · rw [domRestrict_piecewise_compl, domRestrict_eq]
    refine measurable_generateFrom fun s hs ↦ .of_subtype_image ?_
    rw [preimage_comp, Subtype.image_preimage_coe]
    convert! (hTm s hs).diff hvm using 1
    rw [inter_comm]
    refine Set.ext fun x ↦ and_congr_left fun hxv ↦ ⟨fun hx ↦ ?_, fun hx ↦ hTf s hs hx⟩
    exact by_contra fun hx' ↦ hxv <| mem_biUnion hs ⟨hUf s hs hx, hx'⟩

/-- Let `f : α → β` be a null measurable function
such that a.e. all values of `f` belong to a set `t`
such that the restriction of the `σ`-algebra in the codomain to `t` is countably generated,
then `f` is a.e.-measurable. -/
/-
**MeasureTheory.NullMeasurable.aemeasurable_of_aerange** 是 Mathlib 中的一个引理，位于命名空间
 ``。
形式化陈述：MeasureTheory.NullMeasurable.aemeasurable_of_aerange {f : α -> β} {t : Set
 β} [MeasurableSpace.CountablyGenerated t] (h : NullMeasurable f μ) (hft : foral
lᵐ x ∂μ, f x in t) : AEMeasurable f μ
参数：h : NullMeasurable f μ；hft : forallᵐ x ∂μ, f x in t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `aemeasurable_zero_measure`：aemeasurable_zero_measure : AEMeasurable f (0
 : Measure α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AEMeasurable.exists_ae_eq_range_subset`：exists_ae_eq_range_subset (H : A
EMeasurable f μ) {t : Set β} (ht : forallᵐ x ∂μ, f x in t) (h₀ : t.Nonempty) : e
xists g, Measurable g ∧ rang…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `MeasureTheory.NullMeasurable.measurable'`：∀ {α : Type u_2} {β : Type u_3
} [m : MeasurableSpace α] [inst : MeasurableSpace β] {f : α → β}   {μ : MeasureT
heory.Measure α}, MeasureTheor…
· 使用定理 `MeasureTheory.Measure.ae_completion`：ae_completion {_ : MeasurableSpace 
α} (μ : Measure α) : ae μ.completion = ae μ
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s
· 使用定理 `Measurable.subtype_mk`：Measurable.subtype_mk {p : β -> Prop} {f : α -> β
} (hf : Measurable f) {h : forall x, p (f x)} : Measurable fun x => (⟨f x, h x⟩ 
: Subtype p…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `AEMeasurable.congr`：congr (hf : AEMeasurable f μ) (h : f =ᵐ[μ] g) : AEMe
asurable g μ
· 使用定理 `Measurable.comp_aemeasurable`：Measurable.comp_aemeasurable [MeasurableSp
ace δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) : A
EMeasurable (g ∘ f…
· 使用定理 `measurable_subtype_coe`：measurable_subtype_coe {p : α -> Prop} : Measura
ble ((↑) : Subtype p -> α)
· 使用引理 `MeasureTheory.NullMeasurable.aemeasurable`：MeasureTheory.NullMeasurable.
aemeasurable {f : α -> β} [hc : MeasurableSpace.CountablyGenerated β] (h : NullM
easurable f μ) : AEMeasurable f…
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f

--- 原说明 ---
Let `f : α → β` be a null measurable function
such that a.e. all values of `f` belong to a set `t`
such that the restriction of the `σ`-algebra in the codomain to `t` is countably
 generated,
then `f` is a.e.-measurable.
-/
lemma MeasureTheory.NullMeasurable.aemeasurable_of_aerange {f : α → β} {t : Set β}
    [MeasurableSpace.CountablyGenerated t] (h : NullMeasurable f μ) (hft : ∀ᵐ x ∂μ, f x ∈ t) :
    AEMeasurable f μ := by
  rcases eq_empty_or_nonempty t with rfl | hne
  · obtain rfl : μ = 0 := by simpa using hft
    apply aemeasurable_zero_measure
  · rw [← μ.ae_completion] at hft
    obtain ⟨f', hf'm, hf't, hff'⟩ :
        ∃ f' : α → β, NullMeasurable f' μ ∧ range f' ⊆ t ∧ f =ᵐ[μ] f' :=
      h.measurable'.aemeasurable.exists_ae_eq_range_subset hft hne
    rw [range_subset_iff] at hf't
    lift f' to α → t using hf't
    replace hf'm : NullMeasurable f' μ := hf'm.measurable'.subtype_mk
    exact (measurable_subtype_coe.comp_aemeasurable hf'm.aemeasurable).congr hff'.symm

namespace MeasureTheory
namespace Measure

/-
**MeasureTheory.Measure.map_sum** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Measure
`。
形式化陈述：map_sum {ι : Type*} {m : ι -> Measure α} {f : α -> β} (hf : AEMeasurable f
 (Measure.sum m)) : Measure.map f (Measure.sum m) = Measure.sum (fun i => Measur
e.map f (m i))
参数：hf : AEMeasurable f (Measure.sum m)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_apply_of_aemeasurable`：map_apply_of_aemeasurab
le (hf : AEMeasurable f μ) {s : Set β} (hs : MeasurableSet s) : μ.map f s = μ (f
 ⁻¹' s)
· 使用定理 `MeasureTheory.Measure.sum_apply₀`：sum_apply₀ (f : ι -> Measure α) {s : S
et α} (hs : NullMeasurableSet s (sum f)) : sum f s = ∑' i, f i s
· 使用定理 `AEMeasurable.nullMeasurable`：∀ {α : Type u_1} {β : Type u_2} {m0 : Measu
rableSpace α} {mβ : MeasurableSpace β} {μ : MeasureTheory.Measure α}   {f : α → 
β}, AEMeasurable …
· 使用定理 `MeasureTheory.Measure.sum_apply`：sum_apply (f : ι -> Measure α) {s : Set
 α} (hs : MeasurableSet s) : sum f s = ∑' i, f i s
· 使用定理 `AEMeasurable.mono_measure`：mono_measure (h : AEMeasurable f μ) (h' : ν <
= μ) : AEMeasurable f ν
· 使用定理 `MeasureTheory.Measure.le_sum`：le_sum (μ : ι -> Measure α) (i : ι) : μ i 
<= sum μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_sum {ι : Type*} {m : ι → Measure α} {f : α → β} (hf : AEMeasurable f (Measure.sum m)) :
    Measure.map f (Measure.sum m) = Measure.sum (fun i ↦ Measure.map f (m i)) := by
  ext s hs
  rw [map_apply_of_aemeasurable hf hs, sum_apply₀ _ (hf.nullMeasurable hs), sum_apply _ hs]
  have M i : AEMeasurable f (m i) := hf.mono_measure (le_sum m i)
  simp_rw [map_apply_of_aemeasurable (M _) hs]
/-
**MeasureTheory.Measure.map_finset_sum** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.
Measure`。
形式化陈述：map_finset_sum {ι β : Type*} {mβ : MeasurableSpace β} {m : ι -> Measure α}
 {f : α -> β} {s : Finset ι} (hf : AEMeasurable f (∑ i in s, m i)) : map f (∑ i 
in s, m i) = ∑ i in s, (m i).map f
参数：hf : AEMeasurable f (∑ i in s, m i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.sum_coe_finset`：sum_coe_finset (s : Finset ι) (μ :
 ι -> Measure α) : (sum fun i : s => μ i) = ∑ i in s, μ i
· 使用引理 `MeasureTheory.Measure.map_sum`：map_sum {ι : Type*} {m : ι -> Measure α} 
{f : α -> β} (hf : AEMeasurable f (Measure.sum m)) : Measure.map f (Measure.sum 
m) = Measure.sum (f…
-/
lemma map_finset_sum {ι β : Type*} {mβ : MeasurableSpace β} {m : ι → Measure α}
    {f : α → β} {s : Finset ι} (hf : AEMeasurable f (∑ i ∈ s, m i)) :
    map f (∑ i ∈ s, m i) = ∑ i ∈ s, (m i).map f := by
  rw [← sum_coe_finset, ← sum_coe_finset, Measure.map_sum]
  rwa [sum_coe_finset]
/-
**MeasureTheory.Measure.map_finset_sum'** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory
.Measure`。
形式化陈述：map_finset_sum' {ι β : Type*} [Fintype ι] {mβ : MeasurableSpace β} {m : ι 
-> Measure α} {f : α -> β} (hf : AEMeasurable f (∑ i, m i)) : map f (∑ i, m i) =
 ∑ i, (m i).map f
参数：hf : AEMeasurable f (∑ i, m i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.Measure.map_finset_sum`：map_finset_sum {ι β : Type*} {mβ :
 MeasurableSpace β} {m : ι -> Measure α} {f : α -> β} {s : Finset ι} (hf : AEMea
surable f (∑ i in s, m i))…
-/
lemma map_finset_sum' {ι β : Type*} [Fintype ι] {mβ : MeasurableSpace β} {m : ι → Measure α}
    {f : α → β} (hf : AEMeasurable f (∑ i, m i)) :
    map f (∑ i, m i) = ∑ i, (m i).map f := map_finset_sum hf
/-
**MeasureTheory.Measure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (μ : Measure α) (f : α → β) [SFinite μ] : SFinite (μ.map f) := by
  by_cases H : AEMeasurable f μ
  · rw [← sum_sfiniteSeq μ] at H ⊢
    rw [map_sum H]
    infer_instance
  · rw [map_of_not_aemeasurable H]
    infer_instance

end Measure
end MeasureTheory

