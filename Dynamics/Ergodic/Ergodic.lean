/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Ergodic maps and measures

Let `f : α → α` be measure preserving with respect to a measure `μ`. We say `f` is ergodic with
respect to `μ` (or `μ` is ergodic with respect to `f`) if the only measurable sets `s` such that
`f⁻¹' s = s` are either almost empty or full.

In this file we define ergodic maps / measures together with quasi-ergodic maps / measures and
provide some basic API. Quasi-ergodicity is a weaker condition than ergodicity for which the measure
preserving condition is relaxed to quasi-measure-preserving.

## Main definitions

* `PreErgodic`: the ergodicity condition without the measure-preserving condition. This exists
  to share code between the `Ergodic` and `QuasiErgodic` definitions.
* `Ergodic`: the definition of ergodic maps / measures.
* `QuasiErgodic`: the definition of quasi-ergodic maps / measures.
* `Ergodic.quasiErgodic`: an ergodic map / measure is quasi-ergodic.
* `QuasiErgodic.ae_empty_or_univ'`: when the map is quasi-measure-preserving, one may relax the
  strict invariance condition to almost invariance in the ergodicity condition.

-/

public section

open Set Function Filter MeasureTheory MeasureTheory.Measure

open ENNReal

variable {α : Type*} {m : MeasurableSpace α} {s : Set α}

/-- A map `f : α → α` is said to be pre-ergodic with respect to a measure `μ` if any measurable
strictly invariant set is either almost empty or full. -/
/-
**PreErgodic** 是 Mathlib 中的一个结构，位于命名空间 ``。
形式化陈述：PreErgodic (f : α -> α) (μ : Measure α
参数：f : α -> α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A map `f : α → α` is said to be pre-ergodic with respect to a measure `μ` if any
 measurable
strictly invariant set is either almost empty or full.
-/
structure PreErgodic (f : α → α) (μ : Measure α := by volume_tac) : Prop where
  aeconst_set ⦃s : Set α⦄ : MeasurableSet s → f ⁻¹' s = s → EventuallyConst s (ae μ)

/-- A map `f : α → α` is said to be ergodic with respect to a measure `μ` if it is measure
preserving and pre-ergodic. -/
/-
**Ergodic** 是 Mathlib 中的一个结构，位于命名空间 ``。
形式化陈述：Ergodic (f : α -> α) (μ : Measure α
参数：f : α -> α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A map `f : α → α` is said to be ergodic with respect to a measure `μ` if it is m
easure
preserving and pre-ergodic.
-/
structure Ergodic (f : α → α) (μ : Measure α := by volume_tac) : Prop extends
  MeasurePreserving f μ μ, PreErgodic f μ

/-- A map `f : α → α` is said to be quasi-ergodic with respect to a measure `μ` if it is
quasi-measure-preserving and pre-ergodic. -/
/-
**QuasiErgodic** 是 Mathlib 中的一个结构，位于命名空间 ``。
形式化陈述：QuasiErgodic (f : α -> α) (μ : Measure α
参数：f : α -> α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A map `f : α → α` is said to be quasi-ergodic with respect to a measure `μ` if i
t is
quasi-measure-preserving and pre-ergodic.
-/
structure QuasiErgodic (f : α → α) (μ : Measure α := by volume_tac) : Prop extends
  QuasiMeasurePreserving f μ μ, PreErgodic f μ

variable {f : α → α} {μ : Measure α}

namespace PreErgodic

/-
**PreErgodic.ae_empty_or_univ** 是 Mathlib 中的一个定理，位于命名空间 `PreErgodic`。
形式化陈述：ae_empty_or_univ (hf : PreErgodic f μ) (hs : MeasurableSet s) (hfs : f ⁻¹'
 s = s) : s =ᵐ[μ] (∅ : Set α) ∨ s =ᵐ[μ] univ
参数：hf : PreErgodic f μ；hs : MeasurableSet s；hfs : f ⁻¹' s = s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `PreErgodic.aeconst_set`：∀ {α : Type u_1} {m : MeasurableSpace α} {f : α 
→ α} {μ : autoParam (MeasureTheory.Measure α) PreErgodic._auto_1},   PreErgodic 
f μ → ∀ ⦃s :…
-/
theorem ae_empty_or_univ (hf : PreErgodic f μ) (hs : MeasurableSet s) (hfs : f ⁻¹' s = s) :
    s =ᵐ[μ] (∅ : Set α) ∨ s =ᵐ[μ] univ := by
  simpa only [eventuallyConst_set'] using hf.aeconst_set hs hfs
/-
**PreErgodic.measure_self_or_compl_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `PreErgodic
`。
形式化陈述：measure_self_or_compl_eq_zero (hf : PreErgodic f μ) (hs : MeasurableSet s)
 (hs' : f ⁻¹' s = s) : μ s = 0 ∨ μ sᶜ = 0
参数：hf : PreErgodic f μ；hs : MeasurableSet s；hs' : f ⁻¹' s = s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PreErgodic.ae_empty_or_univ`：ae_empty_or_univ (hf : PreErgodic f μ) (hs 
: MeasurableSet s) (hfs : f ⁻¹' s = s) : s =ᵐ[μ] (∅ : Set α) ∨ s =ᵐ[μ] univ
-/
theorem measure_self_or_compl_eq_zero (hf : PreErgodic f μ) (hs : MeasurableSet s)
    (hs' : f ⁻¹' s = s) : μ s = 0 ∨ μ sᶜ = 0 := by
  simpa using hf.ae_empty_or_univ hs hs'
/-
**PreErgodic.ae_mem_or_ae_notMem** 是 Mathlib 中的一个定理，位于命名空间 `PreErgodic`。
形式化陈述：ae_mem_or_ae_notMem (hf : PreErgodic f μ) (hsm : MeasurableSet s) (hs : f 
⁻¹' s = s) : (forallᵐ x ∂μ, x in s) ∨ forallᵐ x ∂μ, x ∉ s
参数：hf : PreErgodic f μ；hsm : MeasurableSet s；hs : f ⁻¹' s = s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.eventuallyConst_set`：eventuallyConst_set {s : Set α} : Eventually
Const s l ↔ (forallᶠ x in l, x in s) ∨ (forallᶠ x in l, x ∉ s)
· 使用定理 `PreErgodic.aeconst_set`：∀ {α : Type u_1} {m : MeasurableSpace α} {f : α 
→ α} {μ : autoParam (MeasureTheory.Measure α) PreErgodic._auto_1},   PreErgodic 
f μ → ∀ ⦃s :…
-/
theorem ae_mem_or_ae_notMem (hf : PreErgodic f μ) (hsm : MeasurableSet s) (hs : f ⁻¹' s = s) :
    (∀ᵐ x ∂μ, x ∈ s) ∨ ∀ᵐ x ∂μ, x ∉ s :=
  eventuallyConst_set.1 <| hf.aeconst_set hsm hs

/-- On a probability space, the (pre)ergodicity condition is a zero-one law. -/
/-
**PreErgodic.prob_eq_zero_or_one** 是 Mathlib 中的一个定理，位于命名空间 `PreErgodic`。
形式化陈述：prob_eq_zero_or_one [IsProbabilityMeasure μ] (hf : PreErgodic f μ) (hs : M
easurableSet s) (hs' : f ⁻¹' s = s) : μ s = 0 ∨ μ s = 1
参数：hf : PreErgodic f μ；hs : MeasurableSet s；hs' : f ⁻¹' s = s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `PreErgodic.measure_self_or_compl_eq_zero`：measure_self_or_compl_eq_zero 
(hf : PreErgodic f μ) (hs : MeasurableSet s) (hs' : f ⁻¹' s = s) : μ s = 0 ∨ μ s
ᶜ = 0

--- 原说明 ---
On a probability space, the (pre)ergodicity condition is a zero-one law.
-/
theorem prob_eq_zero_or_one [IsProbabilityMeasure μ] (hf : PreErgodic f μ) (hs : MeasurableSet s)
    (hs' : f ⁻¹' s = s) : μ s = 0 ∨ μ s = 1 := by
  simpa [hs] using hf.measure_self_or_compl_eq_zero hs hs'
/-
**PreErgodic.of_iterate** 是 Mathlib 中的一个定理，位于命名空间 `PreErgodic`。
形式化陈述：of_iterate (n : Nat) (hf : PreErgodic f^[n] μ) : PreErgodic f μ
参数：n : Nat；hf : PreErgodic f^[n] μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PreErgodic.aeconst_set`：∀ {α : Type u_1} {m : MeasurableSpace α} {f : α 
→ α} {μ : autoParam (MeasureTheory.Measure α) PreErgodic._auto_1},   PreErgodic 
f μ → ∀ ⦃s :…
· 使用定理 `Function.IsFixedPt.preimage_iterate`：preimage_iterate {s : Set α} (h : I
sFixedPt (Set.preimage f) s) (n : Nat) : IsFixedPt (Set.preimage f^[n]) s
-/
theorem of_iterate (n : ℕ) (hf : PreErgodic f^[n] μ) : PreErgodic f μ :=
  ⟨fun _ hs hs' => hf.aeconst_set hs <| IsFixedPt.preimage_iterate hs' n⟩
/-
**PreErgodic.smul_measure** 是 Mathlib 中的一个定理，位于命名空间 `PreErgodic`。
形式化陈述：smul_measure {R : Type*} [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>
=0∞] (hf : PreErgodic f μ) (c : R) : PreErgodic f (c • μ) where aeconst_set _s h
s hfs
参数：hf : PreErgodic f μ；c : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyConst.anti`：∀ {α : Type u_1} {β : Type u_2} {l : Filter
 α} {f : α → β} {l' : Filter α},   Filter.EventuallyConst f l → l' ≤ l → Filter.
EventuallyConst f…
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `PreErgodic.aeconst_set`：∀ {α : Type u_1} {m : MeasurableSpace α} {f : α 
→ α} {μ : autoParam (MeasureTheory.Measure α) PreErgodic._auto_1},   PreErgodic 
f μ → ∀ ⦃s :…
· 使用定理 `MeasureTheory.Measure.ae_smul_measure_le`：ae_smul_measure_le [SMul R Rea
l>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] (c : R) : ae (c • μ) <= ae μ
-/
theorem smul_measure {R : Type*} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    (hf : PreErgodic f μ) (c : R) : PreErgodic f (c • μ) where
  aeconst_set _s hs hfs := (hf.aeconst_set hs hfs).anti <| ae_smul_measure_le _

set_option backward.isDefEq.respectTransparency false in
/-
**PreErgodic.zero_measure** 是 Mathlib 中的一个定理，位于命名空间 `PreErgodic`。
形式化陈述：zero_measure (f : α -> α) : @PreErgodic α m f 0 where aeconst_set _ _ _
参数：f : α -> α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ae_zero`：ae_zero {_m0 : MeasurableSpace α} : ae (0 : Measu
re α) = ⊥
-/
theorem zero_measure (f : α → α) : @PreErgodic α m f 0 where
  aeconst_set _ _ _ := by simp

end PreErgodic

namespace MeasureTheory.MeasurePreserving

variable {β : Type*} {m' : MeasurableSpace β} {μ' : Measure β} {g : α → β}

/-
**MeasureTheory.MeasurePreserving.preErgodic_of_preErgodic_semiconj** 是 Mathlib 
中的一个定理，位于命名空间 `MeasureTheory.MeasurePreserving`。
形式化陈述：preErgodic_of_preErgodic_semiconj (hg : MeasurePreserving g μ μ') (hf : Pr
eErgodic f μ) {f' : β -> β} (h_comm : Semiconj g f f') : PreErgodic f' μ' where 
aeconst_set s hs₀ hs₁
参数：hg : MeasurePreserving g μ μ'；hf : PreErgodic f μ；h_comm : Semiconj g f f'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.MeasurePreserving.aeconst_preimage`：aeconst_preimage {f : 
α -> β} (hf : MeasurePreserving f μa μb) {s : Set β} (hs : NullMeasurableSet s μ
b) : Filter.EventuallyConst (f ⁻¹' s) …
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用定理 `PreErgodic.aeconst_set`：∀ {α : Type u_1} {m : MeasurableSpace α} {f : α 
→ α} {μ : autoParam (MeasureTheory.Measure α) PreErgodic._auto_1},   PreErgodic 
f μ → ∀ ⦃s :…
· 使用定理 `MeasureTheory.MeasurePreserving.measurable`：∀ {α : Type u_1} {β : Type u
_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : 
autoParam (MeasureTheory.Measure…
· 使用定理 `Set.preimage_comp`：preimage_comp {s : Set γ} : g ∘ f ⁻¹' s = f ⁻¹' g ⁻¹'
 s
· 使用定理 `Function.Semiconj.comp_eq`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
ga : α → α} {gb : β → β}, Function.Semiconj f ga gb → f ∘ ga = gb ∘ f
-/
theorem preErgodic_of_preErgodic_semiconj (hg : MeasurePreserving g μ μ') (hf : PreErgodic f μ)
    {f' : β → β} (h_comm : Semiconj g f f') : PreErgodic f' μ' where
  aeconst_set s hs₀ hs₁ := by
    rw [← hg.aeconst_preimage hs₀.nullMeasurableSet]
    apply hf.aeconst_set (hg.measurable hs₀)
    rw [← preimage_comp, h_comm.comp_eq, preimage_comp, hs₁]
/-
**MeasureTheory.MeasurePreserving.ergodic_of_ergodic_semiconj** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory.MeasurePreserving`。
形式化陈述：ergodic_of_ergodic_semiconj (hg : MeasurePreserving g μ μ') (hf : Ergodic 
f μ) {f' : β -> β} (hf' : Measurable f') (h_comm : Semiconj g f f') : Ergodic f'
 μ'
参数：hg : MeasurePreserving g μ μ'；hf : Ergodic f μ；hf' : Measurable f'；h_comm : S
emiconj g f f'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MeasurePreserving.of_semiconj`：∀ {α : Type u_1} {β : Type 
u_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μa : MeasureTheory
.Measure α}   {μb : MeasureTheory…
· 使用定理 `Ergodic.toMeasurePreserving`：∀ {α : Type u_1} {m : MeasurableSpace α} {f
 : α → α} {μ : autoParam (MeasureTheory.Measure α) Ergodic._auto_1},   Ergodic f
 μ → MeasureTheor…
· 使用定理 `MeasureTheory.MeasurePreserving.preErgodic_of_preErgodic_semiconj`：preEr
godic_of_preErgodic_semiconj (hg : MeasurePreserving g μ μ') (hf : PreErgodic f 
μ) {f' : β -> β} (h_comm : Semiconj g f f') : PreErgodi…
· 使用定理 `Ergodic.toPreErgodic`：∀ {α : Type u_1} {m : MeasurableSpace α} {f : α → 
α} {μ : autoParam (MeasureTheory.Measure α) Ergodic._auto_1},   Ergodic f μ → Pr
eErgodic f…
-/
theorem ergodic_of_ergodic_semiconj (hg : MeasurePreserving g μ μ') (hf : Ergodic f μ)
    {f' : β → β} (hf' : Measurable f') (h_comm : Semiconj g f f') : Ergodic f' μ' :=
  ⟨hg.of_semiconj hf.toMeasurePreserving h_comm hf',
   hg.preErgodic_of_preErgodic_semiconj hf.toPreErgodic h_comm⟩
/-
**MeasureTheory.MeasurePreserving.preErgodic_conjugate_iff** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory.MeasurePreserving`。
形式化陈述：preErgodic_conjugate_iff {e : α ≃ᵐ β} (h : MeasurePreserving e μ μ') : Pre
Ergodic (e ∘ f ∘ e.symm) μ' ↔ PreErgodic f μ
参数：h : MeasurePreserving e μ μ'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MeasurePreserving.preErgodic_of_preErgodic_semiconj`：preEr
godic_of_preErgodic_semiconj (hg : MeasurePreserving g μ μ') (hf : PreErgodic f 
μ) {f' : β -> β} (h_comm : Semiconj g f f') : PreErgodi…
· 使用定理 `MeasureTheory.MeasurePreserving.symm`：symm (e : α ≃ᵐ β) {μa : Measure α}
 {μb : Measure β} (h : MeasurePreserving e μa μb) : MeasurePreserving e.symm μb 
μa
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasurableEquiv.symm_apply_apply`：symm_apply_apply (e : α ≃ᵐ β) (x : α) 
: e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem preErgodic_conjugate_iff {e : α ≃ᵐ β} (h : MeasurePreserving e μ μ') :
    PreErgodic (e ∘ f ∘ e.symm) μ' ↔ PreErgodic f μ := by
  refine ⟨fun hf => preErgodic_of_preErgodic_semiconj (h.symm e) hf ?_,
      fun hf => preErgodic_of_preErgodic_semiconj h hf ?_⟩
  · simp [Semiconj]
  · simp [Semiconj]
/-
**MeasureTheory.MeasurePreserving.ergodic_conjugate_iff** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory.MeasurePreserving`。
形式化陈述：ergodic_conjugate_iff {e : α ≃ᵐ β} (h : MeasurePreserving e μ μ') : Ergodi
c (e ∘ f ∘ e.symm) μ' ↔ Ergodic f μ
参数：h : MeasurePreserving e μ μ'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.MeasurePreserving.comp_left_iff`：∀ {α : Type u_1} {β : Typ
e u_2} {γ : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   
[inst_2 : MeasurableSpace γ] {μa : …
· 使用定理 `MeasureTheory.MeasurePreserving.comp_right_iff`：∀ {α : Type u_1} {β : Ty
pe u_2} {γ : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]  
 [inst_2 : MeasurableSpace γ] {μa : …
· 使用定理 `MeasureTheory.MeasurePreserving.symm`：symm (e : α ≃ᵐ β) {μa : Measure α}
 {μb : Measure β} (h : MeasurePreserving e μa μb) : MeasurePreserving e.symm μb 
μa
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `MeasureTheory.MeasurePreserving.preErgodic_conjugate_iff`：preErgodic_con
jugate_iff {e : α ≃ᵐ β} (h : MeasurePreserving e μ μ') : PreErgodic (e ∘ f ∘ e.s
ymm) μ' ↔ PreErgodic f μ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ergodic.toMeasurePreserving`：∀ {α : Type u_1} {m : MeasurableSpace α} {f
 : α → α} {μ : autoParam (MeasureTheory.Measure α) Ergodic._auto_1},   Ergodic f
 μ → MeasureTheor…
· 使用定理 `Ergodic.toPreErgodic`：∀ {α : Type u_1} {m : MeasurableSpace α} {f : α → 
α} {μ : autoParam (MeasureTheory.Measure α) Ergodic._auto_1},   Ergodic f μ → Pr
eErgodic f…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem ergodic_conjugate_iff {e : α ≃ᵐ β} (h : MeasurePreserving e μ μ') :
    Ergodic (e ∘ f ∘ e.symm) μ' ↔ Ergodic f μ := by
  have : MeasurePreserving (e ∘ f ∘ e.symm) μ' μ' ↔ MeasurePreserving f μ μ := by
    rw [h.comp_left_iff, (MeasurePreserving.symm e h).comp_right_iff]
  replace h : PreErgodic (e ∘ f ∘ e.symm) μ' ↔ PreErgodic f μ := h.preErgodic_conjugate_iff
  exact ⟨fun hf => { this.mp hf.toMeasurePreserving, h.mp hf.toPreErgodic with },
    fun hf => { this.mpr hf.toMeasurePreserving, h.mpr hf.toPreErgodic with }⟩

end MeasureTheory.MeasurePreserving

namespace QuasiErgodic

/-
**QuasiErgodic.aeconst_set** 是 Mathlib 中的一个定理，位于命名空间 `QuasiErgodic`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem aeconst_set₀ (hf : QuasiErgodic f μ) (hsm : NullMeasurableSet s μ) (hs : f ⁻¹' s =ᵐ[μ] s) :
    EventuallyConst s (ae μ) :=
  let ⟨_t, h₀, h₁, h₂⟩ := hf.toQuasiMeasurePreserving.exists_preimage_eq_of_preimage_ae hsm hs
  (hf.aeconst_set h₀ h₂).congr h₁

/-- For a quasi-ergodic map, sets that are almost invariant (rather than strictly invariant) are
still either almost empty or full. -/
/-
**QuasiErgodic.ae_empty_or_univ** 是 Mathlib 中的一个定理，位于命名空间 `QuasiErgodic`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a quasi-ergodic map, sets that are almost invariant (rather than strictly in
variant) are
still either almost empty or full.
-/
theorem ae_empty_or_univ₀ (hf : QuasiErgodic f μ) (hsm : NullMeasurableSet s μ)
    (hs : f ⁻¹' s =ᵐ[μ] s) :
    s =ᵐ[μ] (∅ : Set α) ∨ s =ᵐ[μ] univ :=
  eventuallyConst_set'.mp <| hf.aeconst_set₀ hsm hs

/-- For a quasi-ergodic map, sets that are almost invariant (rather than strictly invariant) are
still either almost empty or full. -/
/-
**QuasiErgodic.ae_mem_or_ae_notMem** 是 Mathlib 中的一个定理，位于命名空间 `QuasiErgodic`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a quasi-ergodic map, sets that are almost invariant (rather than strictly in
variant) are
still either almost empty or full.
-/
theorem ae_mem_or_ae_notMem₀ (hf : QuasiErgodic f μ) (hsm : NullMeasurableSet s μ)
    (hs : f ⁻¹' s =ᵐ[μ] s) :
    (∀ᵐ x ∂μ, x ∈ s) ∨ ∀ᵐ x ∂μ, x ∉ s :=
  eventuallyConst_set.mp <| hf.aeconst_set₀ hsm hs
/-
**QuasiErgodic.smul_measure** 是 Mathlib 中的一个定理，位于命名空间 `QuasiErgodic`。
形式化陈述：smul_measure {R : Type*} [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>
=0∞] (hf : QuasiErgodic f μ) (c : R) : QuasiErgodic f (c • μ)
参数：hf : QuasiErgodic f μ；c : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.smul_measure`：smul_measure 
{R : Type*} [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] (hf : QuasiMea
surePreserving f μa μb) (c : R) : QuasiMeasureP…
· 使用定理 `QuasiErgodic.toQuasiMeasurePreserving`：∀ {α : Type u_1} {m : MeasurableS
pace α} {f : α → α} {μ : autoParam (MeasureTheory.Measure α) QuasiErgodic._auto_
1},   QuasiErgodic f μ → Me…
· 使用定理 `PreErgodic.smul_measure`：smul_measure {R : Type*} [SMul R Real>=0∞] [IsS
calarTower R Real>=0∞ Real>=0∞] (hf : PreErgodic f μ) (c : R) : PreErgodic f (c 
• μ) where ae…
· 使用定理 `QuasiErgodic.toPreErgodic`：∀ {α : Type u_1} {m : MeasurableSpace α} {f :
 α → α} {μ : autoParam (MeasureTheory.Measure α) QuasiErgodic._auto_1},   QuasiE
rgodic f μ → Pr…
-/
theorem smul_measure {R : Type*} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    (hf : QuasiErgodic f μ) (c : R) : QuasiErgodic f (c • μ) :=
  ⟨hf.1.smul_measure _, hf.2.smul_measure _⟩
/-
**QuasiErgodic.zero_measure** 是 Mathlib 中的一个定理，位于命名空间 `QuasiErgodic`。
形式化陈述：zero_measure {f : α -> α} (hf : Measurable f) : @QuasiErgodic α m f 0 wher
e measurable
参数：hf : Measurable f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PreErgodic.zero_measure`：zero_measure (f : α -> α) : @PreErgodic α m f 0
 where aeconst_set _ _ _
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_zero`：∀ {α : Type u_1} {β : Type u_2} {mα : Me
asurableSpace α} {mβ : MeasurableSpace β} (f : α → β),   MeasureTheory.Measure.m
ap f 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem zero_measure {f : α → α} (hf : Measurable f) : @QuasiErgodic α m f 0 where
  measurable := hf
  absolutelyContinuous := by simp
  toPreErgodic := .zero_measure f

end QuasiErgodic

namespace Ergodic

/-- An ergodic map is quasi-ergodic. -/
/-
**Ergodic.quasiErgodic** 是 Mathlib 中的一个定理，位于命名空间 `Ergodic`。
形式化陈述：quasiErgodic (hf : Ergodic f μ) : QuasiErgodic f μ
参数：hf : Ergodic f μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ergodic.toPreErgodic`：∀ {α : Type u_1} {m : MeasurableSpace α} {f : α → 
α} {μ : autoParam (MeasureTheory.Measure α) Ergodic._auto_1},   Ergodic f μ → Pr
eErgodic f…
· 使用定理 `MeasureTheory.MeasurePreserving.quasiMeasurePreserving`：∀ {α : Type u_1}
 {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μa : Me
asureTheory.Measure α}   {μb : MeasureTheory…
· 使用定理 `Ergodic.toMeasurePreserving`：∀ {α : Type u_1} {m : MeasurableSpace α} {f
 : α → α} {μ : autoParam (MeasureTheory.Measure α) Ergodic._auto_1},   Ergodic f
 μ → MeasureTheor…

--- 原说明 ---
An ergodic map is quasi-ergodic.
-/
theorem quasiErgodic (hf : Ergodic f μ) : QuasiErgodic f μ :=
  { hf.toPreErgodic, hf.toMeasurePreserving.quasiMeasurePreserving with }

/-- See also `Ergodic.ae_empty_or_univ_of_preimage_ae_le`. -/
/-
**Ergodic.ae_empty_or_univ_of_preimage_ae_le'** 是 Mathlib 中的一个定理，位于命名空间 `Ergodic
`。
形式化陈述：ae_empty_or_univ_of_preimage_ae_le' (hf : Ergodic f μ) (hs : NullMeasurabl
eSet s μ) (hs' : f ⁻¹' s <=ᵐ[μ] s) (h_fin : μ s != ∞) : s =ᵐ[μ] (∅ : Set α) ∨ s 
=ᵐ[μ] univ
参数：hf : Ergodic f μ；hs : NullMeasurableSet s μ；hs' : f ⁻¹' s <=ᵐ[μ] s；h_fin : μ 
s != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `QuasiErgodic.ae_empty_or_univ₀`：ae_empty_or_univ₀ (hf : QuasiErgodic f μ
) (hsm : NullMeasurableSet s μ) (hs : f ⁻¹' s =ᵐ[μ] s) : s =ᵐ[μ] (∅ : Set α) ∨ s
 =ᵐ[μ] univ
· 使用定理 `Ergodic.quasiErgodic`：quasiErgodic (hf : Ergodic f μ) : QuasiErgodic f μ
· 使用定理 `MeasureTheory.ae_eq_of_ae_subset_of_measure_ge`：ae_eq_of_ae_subset_of_me
asure_ge (h₁ : s <=ᵐ[μ] t) (h₂ : μ t <= μ s) (hsm : NullMeasurableSet s μ) (ht :
 μ t != ∞) : s =ᵐ[μ] t
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `MeasureTheory.MeasurePreserving.measure_preimage`：measure_preimage {f : 
α -> β} (hf : MeasurePreserving f μa μb) {s : Set β} (hs : NullMeasurableSet s μ
b) : μa (f ⁻¹' s) = μb s
· 使用定理 `Ergodic.toMeasurePreserving`：∀ {α : Type u_1} {m : MeasurableSpace α} {f
 : α → α} {μ : autoParam (MeasureTheory.Measure α) Ergodic._auto_1},   Ergodic f
 μ → MeasureTheor…
· 使用定理 `MeasureTheory.NullMeasurableSet.preimage`：∀ {α : Type u_1} {β : Type u_2
} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μa : MeasureTheory.Measure 
α}   {μb : MeasureTheory.Measu…
· 使用定理 `MeasureTheory.MeasurePreserving.quasiMeasurePreserving`：∀ {α : Type u_1}
 {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μa : Me
asureTheory.Measure α}   {μb : MeasureTheory…

--- 原说明 ---
See also `Ergodic.ae_empty_or_univ_of_preimage_ae_le`.
-/
theorem ae_empty_or_univ_of_preimage_ae_le' (hf : Ergodic f μ) (hs : NullMeasurableSet s μ)
    (hs' : f ⁻¹' s ≤ᵐ[μ] s) (h_fin : μ s ≠ ∞) : s =ᵐ[μ] (∅ : Set α) ∨ s =ᵐ[μ] univ := by
  refine hf.quasiErgodic.ae_empty_or_univ₀ hs ?_
  refine ae_eq_of_ae_subset_of_measure_ge hs' (hf.measure_preimage hs).ge ?_ h_fin
  exact hs.preimage hf.quasiMeasurePreserving

/-- See also `Ergodic.ae_empty_or_univ_of_ae_le_preimage`. -/
/-
**Ergodic.ae_empty_or_univ_of_ae_le_preimage'** 是 Mathlib 中的一个定理，位于命名空间 `Ergodic
`。
形式化陈述：ae_empty_or_univ_of_ae_le_preimage' (hf : Ergodic f μ) (hs : NullMeasurabl
eSet s μ) (hs' : s <=ᵐ[μ] f ⁻¹' s) (h_fin : μ s != ∞) : s =ᵐ[μ] (∅ : Set α) ∨ s 
=ᵐ[μ] univ
参数：hf : Ergodic f μ；hs : NullMeasurableSet s μ；hs' : s <=ᵐ[μ] f ⁻¹' s；h_fin : μ 
s != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.MeasurePreserving.measure_preimage`：measure_preimage {f : 
α -> β} (hf : MeasurePreserving f μa μb) {s : Set β} (hs : NullMeasurableSet s μ
b) : μa (f ⁻¹' s) = μb s
· 使用定理 `Ergodic.toMeasurePreserving`：∀ {α : Type u_1} {m : MeasurableSpace α} {f
 : α → α} {μ : autoParam (MeasureTheory.Measure α) Ergodic._auto_1},   Ergodic f
 μ → MeasureTheor…
· 使用定理 `QuasiErgodic.ae_empty_or_univ₀`：ae_empty_or_univ₀ (hf : QuasiErgodic f μ
) (hsm : NullMeasurableSet s μ) (hs : f ⁻¹' s =ᵐ[μ] s) : s =ᵐ[μ] (∅ : Set α) ∨ s
 =ᵐ[μ] univ
· 使用定理 `Ergodic.quasiErgodic`：quasiErgodic (hf : Ergodic f μ) : QuasiErgodic f μ
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.ae_eq_of_ae_subset_of_measure_ge`：ae_eq_of_ae_subset_of_me
asure_ge (h₁ : s <=ᵐ[μ] t) (h₂ : μ t <= μ s) (hsm : NullMeasurableSet s μ) (ht :
 μ t != ∞) : s =ᵐ[μ] t
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b

--- 原说明 ---
See also `Ergodic.ae_empty_or_univ_of_ae_le_preimage`.
-/
theorem ae_empty_or_univ_of_ae_le_preimage' (hf : Ergodic f μ) (hs : NullMeasurableSet s μ)
    (hs' : s ≤ᵐ[μ] f ⁻¹' s) (h_fin : μ s ≠ ∞) : s =ᵐ[μ] (∅ : Set α) ∨ s =ᵐ[μ] univ := by
  replace h_fin : μ (f ⁻¹' s) ≠ ∞ := by rwa [hf.measure_preimage hs]
  refine hf.quasiErgodic.ae_empty_or_univ₀ hs ?_
  exact (ae_eq_of_ae_subset_of_measure_ge hs' (hf.measure_preimage hs).le hs h_fin).symm

/-- See also `Ergodic.ae_empty_or_univ_of_image_ae_le`. -/
/-
**Ergodic.ae_empty_or_univ_of_image_ae_le'** 是 Mathlib 中的一个定理，位于命名空间 `Ergodic`。
形式化陈述：ae_empty_or_univ_of_image_ae_le' (hf : Ergodic f μ) (hs : NullMeasurableSe
t s μ) (hs' : f '' s <=ᵐ[μ] s) (h_fin : μ s != ∞) : s =ᵐ[μ] (∅ : Set α) ∨ s =ᵐ[μ
] univ
参数：hf : Ergodic f μ；hs : NullMeasurableSet s μ；hs' : f '' s <=ᵐ[μ] s；h_fin : μ s
 != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.EventuallyLE.trans`：∀ {α : Type u} {β : Type v} [inst : Preorder 
β] {l : Filter α} {f g h : α → β}, f ≤ᶠ[l] g → g ≤ᶠ[l] h → f ≤ᶠ[l] h
· 使用定理 `LE.le.eventuallyLE`：LE.le.eventuallyLE {α} {l : Filter α} {s t : Set α} 
(h : s subseteq t) : s <=ᶠ[l] t
· 使用定理 `Set.subset_preimage_image`：subset_preimage_image (f : α -> β) (s : Set α
) : s subseteq f ⁻¹' f '' s
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.preimage_mono_ae`：preimage_
mono_ae {s t : Set β} (hf : QuasiMeasurePreserving f μa μb) (h : s <=ᵐ[μb] t) : 
f ⁻¹' s <=ᵐ[μa] f ⁻¹' t
· 使用定理 `MeasureTheory.MeasurePreserving.quasiMeasurePreserving`：∀ {α : Type u_1}
 {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μa : Me
asureTheory.Measure α}   {μb : MeasureTheory…
· 使用定理 `Ergodic.toMeasurePreserving`：∀ {α : Type u_1} {m : MeasurableSpace α} {f
 : α → α} {μ : autoParam (MeasureTheory.Measure α) Ergodic._auto_1},   Ergodic f
 μ → MeasureTheor…
· 使用定理 `Ergodic.ae_empty_or_univ_of_ae_le_preimage'`：ae_empty_or_univ_of_ae_le_p
reimage' (hf : Ergodic f μ) (hs : NullMeasurableSet s μ) (hs' : s <=ᵐ[μ] f ⁻¹' s
) (h_fin : μ s != ∞) : s =ᵐ[μ] (∅…

--- 原说明 ---
See also `Ergodic.ae_empty_or_univ_of_image_ae_le`.
-/
theorem ae_empty_or_univ_of_image_ae_le' (hf : Ergodic f μ) (hs : NullMeasurableSet s μ)
    (hs' : f '' s ≤ᵐ[μ] s) (h_fin : μ s ≠ ∞) : s =ᵐ[μ] (∅ : Set α) ∨ s =ᵐ[μ] univ := by
  replace hs' : s ≤ᵐ[μ] f ⁻¹' s :=
    (LE.le.eventuallyLE (subset_preimage_image f s)).trans
      (hf.quasiMeasurePreserving.preimage_mono_ae hs')
  exact ae_empty_or_univ_of_ae_le_preimage' hf hs hs' h_fin

/-- If a measurable equivalence is ergodic, then so is the inverse map. -/
/-
**Ergodic.symm** 是 Mathlib 中的一个定理，位于命名空间 `Ergodic`。
形式化陈述：symm {e : α ≃ᵐ α} (he : Ergodic e μ) : Ergodic e.symm μ where toMeasurePre
serving
参数：he : Ergodic e μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MeasurePreserving.symm`：symm (e : α ≃ᵐ β) {μa : Measure α}
 {μb : Measure β} (h : MeasurePreserving e μa μb) : MeasurePreserving e.symm μb 
μa
· 使用定理 `Ergodic.toMeasurePreserving`：∀ {α : Type u_1} {m : MeasurableSpace α} {f
 : α → α} {μ : autoParam (MeasureTheory.Measure α) Ergodic._auto_1},   Ergodic f
 μ → MeasureTheor…
· 使用定理 `PreErgodic.aeconst_set`：∀ {α : Type u_1} {m : MeasurableSpace α} {f : α 
→ α} {μ : autoParam (MeasureTheory.Measure α) PreErgodic._auto_1},   PreErgodic 
f μ → ∀ ⦃s :…
· 使用定理 `Ergodic.toPreErgodic`：∀ {α : Type u_1} {m : MeasurableSpace α} {f : α → 
α} {μ : autoParam (MeasureTheory.Measure α) Ergodic._auto_1},   Ergodic f μ → Pr
eErgodic f…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasurableEquiv.image_eq_preimage_symm`：image_eq_preimage_symm (e : α ≃ᵐ
 β) (s : Set α) : e '' s = e.symm ⁻¹' s
· 使用引理 `MeasurableEquiv.preimage_image`：preimage_image (e : α ≃ᵐ β) (s : Set α) 
: e ⁻¹' e '' s = s

--- 原说明 ---
If a measurable equivalence is ergodic, then so is the inverse map.
-/
theorem symm {e : α ≃ᵐ α} (he : Ergodic e μ) : Ergodic e.symm μ where
  toMeasurePreserving := he.toMeasurePreserving.symm
  aeconst_set s hsm hs := he.aeconst_set hsm <| by
    conv_lhs => rw [← hs, ← e.image_eq_preimage_symm, e.preimage_image]
/-
**Ergodic.symm_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ergodic`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {e 
: α ≃ᵐ α},   Ergodic (⇑e.symm) μ ↔ Ergodic (⇑e) μ
参数：⇑e.symm；⇑e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ergodic.symm`：symm {e : α ≃ᵐ α} (he : Ergodic e μ) : Ergodic e.symm μ wh
ere toMeasurePreserving
-/
@[simp] theorem symm_iff {e : α ≃ᵐ α} : Ergodic e.symm μ ↔ Ergodic e μ := ⟨.symm, .symm⟩
/-
**Ergodic.smul_measure** 是 Mathlib 中的一个定理，位于命名空间 `Ergodic`。
形式化陈述：smul_measure {R : Type*} [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>
=0∞] (hf : Ergodic f μ) (c : R) : Ergodic f (c • μ)
参数：hf : Ergodic f μ；c : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MeasurePreserving.smul_measure`：smul_measure {R : Type*} [
SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] {f : α -> β} (hf : MeasureP
reserving f μa μb) (c : R) : Measu…
· 使用定理 `Ergodic.toMeasurePreserving`：∀ {α : Type u_1} {m : MeasurableSpace α} {f
 : α → α} {μ : autoParam (MeasureTheory.Measure α) Ergodic._auto_1},   Ergodic f
 μ → MeasureTheor…
· 使用定理 `PreErgodic.smul_measure`：smul_measure {R : Type*} [SMul R Real>=0∞] [IsS
calarTower R Real>=0∞ Real>=0∞] (hf : PreErgodic f μ) (c : R) : PreErgodic f (c 
• μ) where ae…
· 使用定理 `Ergodic.toPreErgodic`：∀ {α : Type u_1} {m : MeasurableSpace α} {f : α → 
α} {μ : autoParam (MeasureTheory.Measure α) Ergodic._auto_1},   Ergodic f μ → Pr
eErgodic f…
-/
theorem smul_measure {R : Type*} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    (hf : Ergodic f μ) (c : R) : Ergodic f (c • μ) :=
  ⟨hf.1.smul_measure _, hf.2.smul_measure _⟩
/-
**Ergodic.zero_measure** 是 Mathlib 中的一个定理，位于命名空间 `Ergodic`。
形式化陈述：zero_measure {f : α -> α} (hf : Measurable f) : @Ergodic α m f 0 where mea
surable
参数：hf : Measurable f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PreErgodic.zero_measure`：zero_measure (f : α -> α) : @PreErgodic α m f 0
 where aeconst_set _ _ _
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_zero`：∀ {α : Type u_1} {β : Type u_2} {mα : Me
asurableSpace α} {mβ : MeasurableSpace β} (f : α → β),   MeasureTheory.Measure.m
ap f 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem zero_measure {f : α → α} (hf : Measurable f) : @Ergodic α m f 0 where
  measurable := hf
  map_eq := by simp
  toPreErgodic := .zero_measure f

section IsFiniteMeasure

variable [IsFiniteMeasure μ]

/-
**Ergodic.ae_empty_or_univ_of_preimage_ae_le** 是 Mathlib 中的一个定理，位于命名空间 `Ergodic`
。
形式化陈述：ae_empty_or_univ_of_preimage_ae_le (hf : Ergodic f μ) (hs : NullMeasurable
Set s μ) (hs' : f ⁻¹' s <=ᵐ[μ] s) : s =ᵐ[μ] (∅ : Set α) ∨ s =ᵐ[μ] univ
参数：hf : Ergodic f μ；hs : NullMeasurableSet s μ；hs' : f ⁻¹' s <=ᵐ[μ] s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Ergodic.ae_empty_or_univ_of_preimage_ae_le'`：ae_empty_or_univ_of_preimag
e_ae_le' (hf : Ergodic f μ) (hs : NullMeasurableSet s μ) (hs' : f ⁻¹' s <=ᵐ[μ] s
) (h_fin : μ s != ∞) : s =ᵐ[μ] (∅…
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
-/
theorem ae_empty_or_univ_of_preimage_ae_le (hf : Ergodic f μ) (hs : NullMeasurableSet s μ)
    (hs' : f ⁻¹' s ≤ᵐ[μ] s) : s =ᵐ[μ] (∅ : Set α) ∨ s =ᵐ[μ] univ :=
  ae_empty_or_univ_of_preimage_ae_le' hf hs hs' <| measure_ne_top μ s
/-
**Ergodic.ae_empty_or_univ_of_ae_le_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Ergodic`
。
形式化陈述：ae_empty_or_univ_of_ae_le_preimage (hf : Ergodic f μ) (hs : NullMeasurable
Set s μ) (hs' : s <=ᵐ[μ] f ⁻¹' s) : s =ᵐ[μ] (∅ : Set α) ∨ s =ᵐ[μ] univ
参数：hf : Ergodic f μ；hs : NullMeasurableSet s μ；hs' : s <=ᵐ[μ] f ⁻¹' s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Ergodic.ae_empty_or_univ_of_ae_le_preimage'`：ae_empty_or_univ_of_ae_le_p
reimage' (hf : Ergodic f μ) (hs : NullMeasurableSet s μ) (hs' : s <=ᵐ[μ] f ⁻¹' s
) (h_fin : μ s != ∞) : s =ᵐ[μ] (∅…
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
-/
theorem ae_empty_or_univ_of_ae_le_preimage (hf : Ergodic f μ) (hs : NullMeasurableSet s μ)
    (hs' : s ≤ᵐ[μ] f ⁻¹' s) : s =ᵐ[μ] (∅ : Set α) ∨ s =ᵐ[μ] univ :=
  ae_empty_or_univ_of_ae_le_preimage' hf hs hs' <| measure_ne_top μ s
/-
**Ergodic.ae_empty_or_univ_of_image_ae_le** 是 Mathlib 中的一个定理，位于命名空间 `Ergodic`。
形式化陈述：ae_empty_or_univ_of_image_ae_le (hf : Ergodic f μ) (hs : NullMeasurableSet
 s μ) (hs' : f '' s <=ᵐ[μ] s) : s =ᵐ[μ] (∅ : Set α) ∨ s =ᵐ[μ] univ
参数：hf : Ergodic f μ；hs : NullMeasurableSet s μ；hs' : f '' s <=ᵐ[μ] s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Ergodic.ae_empty_or_univ_of_image_ae_le'`：ae_empty_or_univ_of_image_ae_l
e' (hf : Ergodic f μ) (hs : NullMeasurableSet s μ) (hs' : f '' s <=ᵐ[μ] s) (h_fi
n : μ s != ∞) : s =ᵐ[μ] (∅ : S…
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
-/
theorem ae_empty_or_univ_of_image_ae_le (hf : Ergodic f μ) (hs : NullMeasurableSet s μ)
    (hs' : f '' s ≤ᵐ[μ] s) : s =ᵐ[μ] (∅ : Set α) ∨ s =ᵐ[μ] univ :=
  ae_empty_or_univ_of_image_ae_le' hf hs hs' <| measure_ne_top μ s

end IsFiniteMeasure

end Ergodic

