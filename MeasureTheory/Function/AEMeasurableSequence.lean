/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

/-!
# Sequence of measurable functions associated to a sequence of a.e.-measurable functions

We define here tools to prove statements about limits (infi, supr...) of sequences of
`AEMeasurable` functions.
Given a sequence of a.e.-measurable functions `f : ι → α → β` with hypothesis
`hf : ∀ i, AEMeasurable (f i) μ`, and a pointwise property `p : α → (ι → β) → Prop` such that we
have `hp : ∀ᵐ x ∂μ, p x (fun n ↦ f n x)`, we define a sequence of measurable functions `aeSeq hf p`
and a measurable set `aeSeqSet hf p`, such that
* `μ (aeSeqSet hf p)ᶜ = 0`
* `x ∈ aeSeqSet hf p → ∀ i : ι, aeSeq hf hp i x = f i x`
* `x ∈ aeSeqSet hf p → p x (fun n ↦ f n x)`
-/

@[expose] public noncomputable section


open MeasureTheory

variable {ι : Sort*} {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] {f : ι → α → β}
  {μ : Measure α} {p : α → (ι → β) → Prop}

/-- If we have the additional hypothesis `∀ᵐ x ∂μ, p x (fun n ↦ f n x)`, this is a measurable set
whose complement has measure 0 such that for all `x ∈ aeSeqSet`, `f i x` is equal to
`(hf i).mk (f i) x` for all `i` and we have the pointwise property `p x (fun n ↦ f n x)`. -/
/-
**aeSeqSet** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：aeSeqSet (hf : forall i, AEMeasurable (f i) μ) (p : α -> (ι -> β) -> Prop)
 : Set α
参数：hf : forall i, AEMeasurable (f i) μ；p : α -> (ι -> β) -> Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If we have the additional hypothesis `∀ᵐ x ∂μ, p x (fun n ↦ f n x)`, this is a m
easurable set
whose complement has measure 0 such that for all `x ∈ aeSeqSet`, `f i x` is equa
l to
`(hf i).mk (f i) x` for all `i` and we have the pointwise property `p x (fun n ↦
 f n x)`.
-/
def aeSeqSet (hf : ∀ i, AEMeasurable (f i) μ) (p : α → (ι → β) → Prop) : Set α :=
  (toMeasurable μ { x | (∀ i, f i x = (hf i).mk (f i) x) ∧ p x fun n => f n x }ᶜ)ᶜ

open scoped Classical in
/-- A sequence of measurable functions that are equal to `f` and verify property `p` on the
measurable set `aeSeqSet hf p`. -/
/-
**aeSeq** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：aeSeq (hf : forall i, AEMeasurable (f i) μ) (p : α -> (ι -> β) -> Prop) : 
ι -> α -> β
参数：hf : forall i, AEMeasurable (f i) μ；p : α -> (ι -> β) -> Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A sequence of measurable functions that are equal to `f` and verify property `p`
 on the
measurable set `aeSeqSet hf p`.
-/
def aeSeq (hf : ∀ i, AEMeasurable (f i) μ) (p : α → (ι → β) → Prop) : ι → α → β :=
  fun i x => ite (x ∈ aeSeqSet hf p) ((hf i).mk (f i) x) (⟨f i x⟩ : Nonempty β).some

namespace aeSeq

section MemAESeqSet

/-
**aeSeq.mk_eq_fun_of_mem_aeSeqSet** 是 Mathlib 中的一个定理，位于命名空间 `aeSeq`。
形式化陈述：mk_eq_fun_of_mem_aeSeqSet (hf : forall i, AEMeasurable (f i) μ) {x : α} (h
x : x in aeSeqSet hf p) (i : ι) : (hf i).mk (f i) x = f i x
参数：hf : forall i, AEMeasurable (f i) μ；hx : x in aeSeqSet hf p；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `aeSeqSet.eq_1`：∀ {ι : Sort u_1} {α : Type u_2} {β : Type u_3} [inst : Me
asurableSpace α] [inst_1 : MeasurableSpace β] {f : ι → α → β}   {μ : MeasureTheo
ry.…
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `Set.compl_subset_compl`：compl_subset_compl : sᶜ subseteq tᶜ ↔ t subseteq
 s
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.subset_toMeasurable`：subset_toMeasurable (μ : Measure α) (
s : Set α) : s subseteq toMeasurable μ s
-/
theorem mk_eq_fun_of_mem_aeSeqSet (hf : ∀ i, AEMeasurable (f i) μ) {x : α} (hx : x ∈ aeSeqSet hf p)
    (i : ι) : (hf i).mk (f i) x = f i x :=
  haveI h_ss : aeSeqSet hf p ⊆ { x | ∀ i, f i x = (hf i).mk (f i) x } := by
    rw [aeSeqSet, ← compl_compl { x | ∀ i, f i x = (hf i).mk (f i) x }, Set.compl_subset_compl]
    refine Set.Subset.trans (Set.compl_subset_compl.mpr fun x h => ?_) (subset_toMeasurable _ _)
    exact h.1
  (h_ss hx i).symm
/-
**aeSeq.aeSeq_eq_mk_of_mem_aeSeqSet** 是 Mathlib 中的一个定理，位于命名空间 `aeSeq`。
形式化陈述：aeSeq_eq_mk_of_mem_aeSeqSet (hf : forall i, AEMeasurable (f i) μ) {x : α} 
(hx : x in aeSeqSet hf p) (i : ι) : aeSeq hf p i x = (hf i).mk (f i) x
参数：hf : forall i, AEMeasurable (f i) μ；hx : x in aeSeqSet hf p；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `if_true`：∀ {α : Sort u_1} {x : Decidable True} (t e : α), (if True then 
t else e) = t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem aeSeq_eq_mk_of_mem_aeSeqSet (hf : ∀ i, AEMeasurable (f i) μ) {x : α}
    (hx : x ∈ aeSeqSet hf p) (i : ι) : aeSeq hf p i x = (hf i).mk (f i) x := by
  simp only [aeSeq, hx, if_true]
/-
**aeSeq.aeSeq_eq_fun_of_mem_aeSeqSet** 是 Mathlib 中的一个定理，位于命名空间 `aeSeq`。
形式化陈述：aeSeq_eq_fun_of_mem_aeSeqSet (hf : forall i, AEMeasurable (f i) μ) {x : α}
 (hx : x in aeSeqSet hf p) (i : ι) : aeSeq hf p i x = f i x
参数：hf : forall i, AEMeasurable (f i) μ；hx : x in aeSeqSet hf p；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `aeSeq.aeSeq_eq_mk_of_mem_aeSeqSet`：aeSeq_eq_mk_of_mem_aeSeqSet (hf : for
all i, AEMeasurable (f i) μ) {x : α} (hx : x in aeSeqSet hf p) (i : ι) : aeSeq h
f p i x = (hf i).mk (f …
· 使用定理 `aeSeq.mk_eq_fun_of_mem_aeSeqSet`：mk_eq_fun_of_mem_aeSeqSet (hf : forall 
i, AEMeasurable (f i) μ) {x : α} (hx : x in aeSeqSet hf p) (i : ι) : (hf i).mk (
f i) x = f i x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem aeSeq_eq_fun_of_mem_aeSeqSet (hf : ∀ i, AEMeasurable (f i) μ) {x : α}
    (hx : x ∈ aeSeqSet hf p) (i : ι) : aeSeq hf p i x = f i x := by
  simp only [aeSeq_eq_mk_of_mem_aeSeqSet hf hx i, mk_eq_fun_of_mem_aeSeqSet hf hx i]
/-
**aeSeq.prop_of_mem_aeSeqSet** 是 Mathlib 中的一个定理，位于命名空间 `aeSeq`。
形式化陈述：prop_of_mem_aeSeqSet (hf : forall i, AEMeasurable (f i) μ) {x : α} (hx : x
 in aeSeqSet hf p) : p x fun n => aeSeq hf p n x
参数：hf : forall i, AEMeasurable (f i) μ；hx : x in aeSeqSet hf p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `if_true`：∀ {α : Sort u_1} {x : Decidable True} (t e : α), (if True then 
t else e) = t
· 使用定理 `aeSeq.mk_eq_fun_of_mem_aeSeqSet`：mk_eq_fun_of_mem_aeSeqSet (hf : forall 
i, AEMeasurable (f i) μ) {x : α} (hx : x in aeSeqSet hf p) (i : ι) : (hf i).mk (
f i) x = f i x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `aeSeqSet.eq_1`：∀ {ι : Sort u_1} {α : Type u_2} {β : Type u_3} [inst : Me
asurableSpace α] [inst_1 : MeasurableSpace β] {f : ι → α → β}   {μ : MeasureTheo
ry.…
· 使用定理 `Set.compl_subset_compl`：compl_subset_compl : sᶜ subseteq tᶜ ↔ t subseteq
 s
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.subset_toMeasurable`：subset_toMeasurable (μ : Measure α) (
s : Set α) : s subseteq toMeasurable μ s
· 使用定理 `Set.mem_of_subset_of_mem`：∀ {α : Type u} {s₁ s₂ : Set α} {a : α}, s₁ ⊆ s
₂ → a ∈ s₁ → a ∈ s₂
-/
theorem prop_of_mem_aeSeqSet (hf : ∀ i, AEMeasurable (f i) μ) {x : α} (hx : x ∈ aeSeqSet hf p) :
    p x fun n => aeSeq hf p n x := by
  simp only [aeSeq, hx, if_true]
  rw [funext fun n => mk_eq_fun_of_mem_aeSeqSet hf hx n]
  have h_ss : aeSeqSet hf p ⊆ { x | p x fun n => f n x } := by
    rw [← compl_compl { x | p x fun n => f n x }, aeSeqSet, Set.compl_subset_compl]
    refine Set.Subset.trans (Set.compl_subset_compl.mpr ?_) (subset_toMeasurable _ _)
    exact fun x hx => hx.2
  have hx' := Set.mem_of_subset_of_mem h_ss hx
  exact hx'
/-
**aeSeq.fun_prop_of_mem_aeSeqSet** 是 Mathlib 中的一个定理，位于命名空间 `aeSeq`。
形式化陈述：fun_prop_of_mem_aeSeqSet (hf : forall i, AEMeasurable (f i) μ) {x : α} (hx
 : x in aeSeqSet hf p) : p x fun n => f n x
参数：hf : forall i, AEMeasurable (f i) μ；hx : x in aeSeqSet hf p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `aeSeq.aeSeq_eq_fun_of_mem_aeSeqSet`：aeSeq_eq_fun_of_mem_aeSeqSet (hf : f
orall i, AEMeasurable (f i) μ) {x : α} (hx : x in aeSeqSet hf p) (i : ι) : aeSeq
 hf p i x = f i x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `aeSeq.prop_of_mem_aeSeqSet`：prop_of_mem_aeSeqSet (hf : forall i, AEMeasu
rable (f i) μ) {x : α} (hx : x in aeSeqSet hf p) : p x fun n => aeSeq hf p n x
-/
theorem fun_prop_of_mem_aeSeqSet (hf : ∀ i, AEMeasurable (f i) μ) {x : α} (hx : x ∈ aeSeqSet hf p) :
    p x fun n => f n x := by
  have h_eq : (fun n => f n x) = fun n => aeSeq hf p n x :=
    funext fun n => (aeSeq_eq_fun_of_mem_aeSeqSet hf hx n).symm
  rw [h_eq]
  exact prop_of_mem_aeSeqSet hf hx

end MemAESeqSet

/-
**aeSeq.aeSeqSet_measurableSet** 是 Mathlib 中的一个定理，位于命名空间 `aeSeq`。
形式化陈述：aeSeqSet_measurableSet {hf : forall i, AEMeasurable (f i) μ} : MeasurableS
et (aeSeqSet hf p)
参数：f i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `MeasureTheory.measurableSet_toMeasurable`：measurableSet_toMeasurable (μ 
: Measure α) (s : Set α) : MeasurableSet (toMeasurable μ s)
-/
theorem aeSeqSet_measurableSet {hf : ∀ i, AEMeasurable (f i) μ} : MeasurableSet (aeSeqSet hf p) :=
  (measurableSet_toMeasurable _ _).compl
/-
**aeSeq.measurable** 是 Mathlib 中的一个定理，位于命名空间 `aeSeq`。
形式化陈述：measurable (hf : forall i, AEMeasurable (f i) μ) (p : α -> (ι -> β) -> Pro
p) (i : ι) : Measurable (aeSeq hf p i)
参数：hf : forall i, AEMeasurable (f i) μ；p : α -> (ι -> β) -> Prop；i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.ite`：Measurable.ite {p : α -> Prop} {_ : DecidablePred p} (hp
 : MeasurableSet { a : α | p a }) (hf : Measurable f) (hg : Measurable g) : Meas
urab…
· 使用定理 `aeSeq.aeSeqSet_measurableSet`：aeSeqSet_measurableSet {hf : forall i, AEM
easurable (f i) μ} : MeasurableSet (aeSeqSet hf p)
· 使用定理 `AEMeasurable.measurable_mk`：measurable_mk (h : AEMeasurable f μ) : Measu
rable (h.mk f)
· 使用定理 `measurable_const'`：measurable_const' {f : β -> α} (hf : forall x y, f x 
= f y) : Measurable f
-/
theorem measurable (hf : ∀ i, AEMeasurable (f i) μ) (p : α → (ι → β) → Prop) (i : ι) :
    Measurable (aeSeq hf p i) :=
  Measurable.ite aeSeqSet_measurableSet (hf i).measurable_mk <| measurable_const' fun _ _ => rfl
/-
**aeSeq.measure_compl_aeSeqSet_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `aeSeq`。
形式化陈述：measure_compl_aeSeqSet_eq_zero [Countable ι] (hf : forall i, AEMeasurable 
(f i) μ) (hp : forallᵐ x ∂μ, p x fun n => f n x) : μ (aeSeqSet hf p)ᶜ = 0
参数：hf : forall i, AEMeasurable (f i) μ；hp : forallᵐ x ∂μ, p x fun n => f n x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `aeSeqSet.eq_1`：∀ {ι : Sort u_1} {α : Type u_2} {β : Type u_3} [inst : Me
asurableSpace α] [inst_1 : MeasurableSpace β] {f : ι → α → β}   {μ : MeasureTheo
ry.…
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `MeasureTheory.measure_toMeasurable`：measure_toMeasurable (s : Set α) : μ
 (toMeasurable μ s) = μ s
· 使用定理 `AEMeasurable.ae_eq_mk`：ae_eq_mk (h : AEMeasurable f μ) : f =ᵐ[μ] h.mk f
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
-/
theorem measure_compl_aeSeqSet_eq_zero [Countable ι] (hf : ∀ i, AEMeasurable (f i) μ)
    (hp : ∀ᵐ x ∂μ, p x fun n => f n x) : μ (aeSeqSet hf p)ᶜ = 0 := by
  rw [aeSeqSet, compl_compl, measure_toMeasurable]
  have hf_eq := fun i => (hf i).ae_eq_mk
  simp_rw [Filter.EventuallyEq, ← ae_all_iff] at hf_eq
  exact Filter.Eventually.and hf_eq hp
/-
**aeSeq.aeSeq_eq_mk_ae** 是 Mathlib 中的一个定理，位于命名空间 `aeSeq`。
形式化陈述：aeSeq_eq_mk_ae [Countable ι] (hf : forall i, AEMeasurable (f i) μ) (hp : f
orallᵐ x ∂μ, p x fun n => f n x) : forallᵐ a : α ∂μ, forall i : ι, aeSeq hf p i 
a = (hf i).mk (f i) a
参数：hf : forall i, AEMeasurable (f i) μ；hp : forallᵐ x ∂μ, p x fun n => f n x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `if_true`：∀ {α : Sort u_1} {x : Decidable True} (t e : α), (if True then 
t else e) = t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.ae_iff`：ae_iff {p : α -> Prop} : (forallᵐ a ∂μ, p a) ↔ μ {
 a | ¬p a } = 0
· 使用定理 `aeSeq.measure_compl_aeSeqSet_eq_zero`：measure_compl_aeSeqSet_eq_zero [Co
untable ι] (hf : forall i, AEMeasurable (f i) μ) (hp : forallᵐ x ∂μ, p x fun n =
> f n x) : μ (aeSeqSet hf …
-/
theorem aeSeq_eq_mk_ae [Countable ι] (hf : ∀ i, AEMeasurable (f i) μ)
    (hp : ∀ᵐ x ∂μ, p x fun n => f n x) : ∀ᵐ a : α ∂μ, ∀ i : ι, aeSeq hf p i a = (hf i).mk (f i) a :=
  have h_ss : aeSeqSet hf p ⊆ { a : α | ∀ i, aeSeq hf p i a = (hf i).mk (f i) a } := fun x hx i =>
    by simp only [aeSeq, hx, if_true]
  (ae_iff.2 (measure_compl_aeSeqSet_eq_zero hf hp)).mono h_ss
/-
**aeSeq.aeSeq_eq_fun_ae** 是 Mathlib 中的一个定理，位于命名空间 `aeSeq`。
形式化陈述：aeSeq_eq_fun_ae [Countable ι] (hf : forall i, AEMeasurable (f i) μ) (hp : 
forallᵐ x ∂μ, p x fun n => f n x) : forallᵐ a : α ∂μ, forall i : ι, aeSeq hf p i
 a = f i a
参数：hf : forall i, AEMeasurable (f i) μ；hp : forallᵐ x ∂μ, p x fun n => f n x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.measure_mono_null`：measure_mono_null (h : s subseteq t) (h
t : μ t = 0) : μ s = 0
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `aeSeq.aeSeq_eq_fun_of_mem_aeSeqSet`：aeSeq_eq_fun_of_mem_aeSeqSet (hf : f
orall i, AEMeasurable (f i) μ) {x : α} (hx : x in aeSeqSet hf p) (i : ι) : aeSeq
 hf p i x = f i x
· 使用定理 `aeSeq.measure_compl_aeSeqSet_eq_zero`：measure_compl_aeSeqSet_eq_zero [Co
untable ι] (hf : forall i, AEMeasurable (f i) μ) (hp : forallᵐ x ∂μ, p x fun n =
> f n x) : μ (aeSeqSet hf …
-/
theorem aeSeq_eq_fun_ae [Countable ι] (hf : ∀ i, AEMeasurable (f i) μ)
    (hp : ∀ᵐ x ∂μ, p x fun n => f n x) : ∀ᵐ a : α ∂μ, ∀ i : ι, aeSeq hf p i a = f i a :=
  haveI h_ss : { a : α | ¬∀ i : ι, aeSeq hf p i a = f i a } ⊆ (aeSeqSet hf p)ᶜ := fun _ =>
    mt fun hx i => aeSeq_eq_fun_of_mem_aeSeqSet hf hx i
  measure_mono_null h_ss (measure_compl_aeSeqSet_eq_zero hf hp)
/-
**aeSeq.aeSeq_n_eq_fun_n_ae** 是 Mathlib 中的一个定理，位于命名空间 `aeSeq`。
形式化陈述：aeSeq_n_eq_fun_n_ae [Countable ι] (hf : forall i, AEMeasurable (f i) μ) (h
p : forallᵐ x ∂μ, p x fun n => f n x) (n : ι) : aeSeq hf p n =ᵐ[μ] f n
参数：hf : forall i, AEMeasurable (f i) μ；hp : forallᵐ x ∂μ, p x fun n => f n x；n :
 ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.ae_all_iff`：ae_all_iff {ι : Sort*} [Countable ι] {p : α ->
 ι -> Prop} : (forallᵐ a ∂μ, forall i, p a i) ↔ forall i, forallᵐ a ∂μ, p a i
· 使用定理 `aeSeq.aeSeq_eq_fun_ae`：aeSeq_eq_fun_ae [Countable ι] (hf : forall i, AEM
easurable (f i) μ) (hp : forallᵐ x ∂μ, p x fun n => f n x) : forallᵐ a : α ∂μ, f
orall i : ι…
-/
theorem aeSeq_n_eq_fun_n_ae [Countable ι] (hf : ∀ i, AEMeasurable (f i) μ)
    (hp : ∀ᵐ x ∂μ, p x fun n => f n x) (n : ι) : aeSeq hf p n =ᵐ[μ] f n :=
  ae_all_iff.mp (aeSeq_eq_fun_ae hf hp) n
/-
**aeSeq.iSup** 是 Mathlib 中的一个定理，位于命名空间 `aeSeq`。
形式化陈述：iSup [SupSet β] [Countable ι] (hf : forall i, AEMeasurable (f i) μ) (hp : 
forallᵐ x ∂μ, p x fun n => f n x) : ⨆ n, aeSeq hf p n =ᵐ[μ] ⨆ n, f n
参数：hf : forall i, AEMeasurable (f i) μ；hp : forallᵐ x ∂μ, p x fun n => f n x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `aeSeq.aeSeq_eq_fun_ae`：aeSeq_eq_fun_ae [Countable ι] (hf : forall i, AEM
easurable (f i) μ) (hp : forallᵐ x ∂μ, p x fun n => f n x) : forallᵐ a : α ∂μ, f
orall i : ι…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_apply`：iSup_apply {α : Type*} {β : α -> Type*} {ι : Sort*} [forall 
i, SupSet (β i)] {f : ι -> forall a, β a} {a : α} : (⨆ i, f i) a = ⨆ i, f i a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iSup [SupSet β] [Countable ι] (hf : ∀ i, AEMeasurable (f i) μ)
    (hp : ∀ᵐ x ∂μ, p x fun n => f n x) : ⨆ n, aeSeq hf p n =ᵐ[μ] ⨆ n, f n := by
  filter_upwards [aeSeq_eq_fun_ae hf hp] with x hx
  simp [iSup_apply, hx]
/-
**aeSeq.iInf** 是 Mathlib 中的一个定理，位于命名空间 `aeSeq`。
形式化陈述：iInf [InfSet β] [Countable ι] (hf : forall i, AEMeasurable (f i) μ) (hp : 
forallᵐ x ∂μ, p x fun n => f n x) : ⨅ n, aeSeq hf p n =ᵐ[μ] ⨅ n, f n
参数：hf : forall i, AEMeasurable (f i) μ；hp : forallᵐ x ∂μ, p x fun n => f n x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `aeSeq.iSup`：iSup [SupSet β] [Countable ι] (hf : forall i, AEMeasurable (
f i) μ) (hp : forallᵐ x ∂μ, p x fun n => f n x) : ⨆ n, aeSeq hf p n =ᵐ[μ] ⨆ n, f
…
-/
theorem iInf [InfSet β] [Countable ι] (hf : ∀ i, AEMeasurable (f i) μ)
    (hp : ∀ᵐ x ∂μ, p x fun n ↦ f n x) : ⨅ n, aeSeq hf p n =ᵐ[μ] ⨅ n, f n :=
  iSup (β := βᵒᵈ) hf hp

end aeSeq

