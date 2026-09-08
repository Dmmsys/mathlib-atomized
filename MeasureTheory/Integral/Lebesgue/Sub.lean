/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Subtraction of Lebesgue integrals

In this file we first show that Lebesgue integrals can be subtracted with the expected results –
`∫⁻ f - ∫⁻ g ≤ ∫⁻ (f - g)`, with equality if `g ≤ f` almost everywhere. Then we prove variants of
the monotone convergence theorem that use this subtraction in their proofs.
-/

public section

open Filter ENNReal Topology

namespace MeasureTheory

variable {α β : Type*} [MeasurableSpace α] {μ : Measure α}

/-
**MeasureTheory.lintegral_sub'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_sub' {f g : α -> Real>=0∞} (hg : AEMeasurable g μ) (hg_fin : ∫⁻ 
a, g a ∂μ != ∞) (h_le : g <=ᵐ[μ] f) : ∫⁻ a, f a - g a ∂μ = ∫⁻ a, f a ∂μ - ∫⁻ a, 
g a ∂μ
参数：hg : AEMeasurable g μ；hg_fin : ∫⁻ a, g a ∂μ != ∞；h_le : g <=ᵐ[μ] f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ENNReal.eq_sub_of_add_eq`：∀ {a b c : ENNReal}, c ≠ ⊤ → a + c = b → a = b
 - c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_add_right'`：lintegral_add_right' (f : α -> Real>
=0∞) {g : α -> Real>=0∞} (hg : AEMeasurable g μ) : ∫⁻ a, f a + g a ∂μ = ∫⁻ a, f 
a ∂μ + ∫⁻ a, g a ∂μ
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
-/
theorem lintegral_sub' {f g : α → ℝ≥0∞} (hg : AEMeasurable g μ) (hg_fin : ∫⁻ a, g a ∂μ ≠ ∞)
    (h_le : g ≤ᵐ[μ] f) : ∫⁻ a, f a - g a ∂μ = ∫⁻ a, f a ∂μ - ∫⁻ a, g a ∂μ := by
  refine ENNReal.eq_sub_of_add_eq hg_fin ?_
  rw [← lintegral_add_right' _ hg]
  exact lintegral_congr_ae (h_le.mono fun x hx => tsub_add_cancel_of_le hx)
/-
**MeasureTheory.lintegral_sub** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_sub {f g : α -> Real>=0∞} (hg : Measurable g) (hg_fin : ∫⁻ a, g 
a ∂μ != ∞) (h_le : g <=ᵐ[μ] f) : ∫⁻ a, f a - g a ∂μ = ∫⁻ a, f a ∂μ - ∫⁻ a, g a ∂
μ
参数：hg : Measurable g；hg_fin : ∫⁻ a, g a ∂μ != ∞；h_le : g <=ᵐ[μ] f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.lintegral_sub'`：lintegral_sub' {f g : α -> Real>=0∞} (hg :
 AEMeasurable g μ) (hg_fin : ∫⁻ a, g a ∂μ != ∞) (h_le : g <=ᵐ[μ] f) : ∫⁻ a, f a 
- g a ∂μ = ∫⁻ a, f…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
-/
theorem lintegral_sub {f g : α → ℝ≥0∞} (hg : Measurable g) (hg_fin : ∫⁻ a, g a ∂μ ≠ ∞)
    (h_le : g ≤ᵐ[μ] f) : ∫⁻ a, f a - g a ∂μ = ∫⁻ a, f a ∂μ - ∫⁻ a, g a ∂μ :=
  lintegral_sub' hg.aemeasurable hg_fin h_le
/-
**MeasureTheory.lintegral_sub_le'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_sub_le' (f g : α -> Real>=0∞) (hf : AEMeasurable f μ) : ∫⁻ x, g 
x ∂μ - ∫⁻ x, f x ∂μ <= ∫⁻ x, g x - f x ∂μ
参数：f g : α -> Real>=0∞；hf : AEMeasurable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tsub_le_iff_right`：tsub_le_iff_right [LE α] [Add α] [Sub α] [OrderedSub 
α] {a b c : α} : a - b <= c ↔ a <= c + b
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `add_top`：add_top (a : α) : a + ⊤ = ⊤
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_add_right'`：lintegral_add_right' (f : α -> Real>
=0∞) {g : α -> Real>=0∞} (hg : AEMeasurable g μ) : ∫⁻ a, f a + g a ∂μ = ∫⁻ a, f 
a ∂μ + ∫⁻ a, g a ∂μ
· 使用定理 `MeasureTheory.lintegral_mono_fn'`：∀ {α : Type u_1} {m : MeasurableSpace 
α} {μ ν : MeasureTheory.Measure α},   μ ≤ ν → ∀ ⦃f g : α → ENNReal⦄, (∀ (x : α),
 f x ≤ g x) → ∫⁻ (a : …
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `le_tsub_add`：le_tsub_add : b <= b - a + a
-/
theorem lintegral_sub_le' (f g : α → ℝ≥0∞) (hf : AEMeasurable f μ) :
    ∫⁻ x, g x ∂μ - ∫⁻ x, f x ∂μ ≤ ∫⁻ x, g x - f x ∂μ := by
  rw [tsub_le_iff_right]
  by_cases hfi : ∫⁻ x, f x ∂μ = ∞
  · rw [hfi, add_top]
    exact le_top
  · rw [← lintegral_add_right' _ hf]
    gcongr
    exact le_tsub_add
/-
**MeasureTheory.lintegral_sub_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_sub_le (f g : α -> Real>=0∞) (hf : Measurable f) : ∫⁻ x, g x ∂μ 
- ∫⁻ x, f x ∂μ <= ∫⁻ x, g x - f x ∂μ
参数：f g : α -> Real>=0∞；hf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.lintegral_sub_le'`：lintegral_sub_le' (f g : α -> Real>=0∞)
 (hf : AEMeasurable f μ) : ∫⁻ x, g x ∂μ - ∫⁻ x, f x ∂μ <= ∫⁻ x, g x - f x ∂μ
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
-/
theorem lintegral_sub_le (f g : α → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x, g x ∂μ - ∫⁻ x, f x ∂μ ≤ ∫⁻ x, g x - f x ∂μ :=
  lintegral_sub_le' f g hf.aemeasurable

/-- **Monotone convergence theorem** for nonincreasing sequences of functions. -/
/-
**MeasureTheory.lintegral_iInf_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_iInf_ae {f : Nat -> α -> Real>=0∞} (h_meas : forall n, Measurabl
e (f n)) (h_mono : forall n : Nat, f n.succ <=ᵐ[μ] f n) (h_fin : ∫⁻ a, f 0 a ∂μ 
!= ∞) : ∫⁻ a, ⨅ n, f n a ∂μ = ⨅ n, ∫⁻ a, f n a ∂μ
参数：h_meas : forall n, Measurable (f n)；h_mono : forall n : Nat, f n.succ <=ᵐ[μ] 
f n；h_fin : ∫⁻ a, f 0 a ∂μ != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.lintegral_mono`：lintegral_mono ⦃f g : α -> Real>=0∞⦄ (hfg 
: f <= g) : ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ
· 使用定理 `iInf_le_of_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α
] {f : ι → α} {a : α} (i : ι), f i ≤ a → iInf f ≤ a
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.sub_right_inj`：sub_right_inj {a b c : Real>=0∞} (ha : a != ∞) (h
b : b <= a) (hc : c <= a) : a - b = a - c ↔ b = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_sub`：lintegral_sub {f g : α -> Real>=0∞} (hg : M
easurable g) (hg_fin : ∫⁻ a, g a ∂μ != ∞) (h_le : g <=ᵐ[μ] f) : ∫⁻ a, f a - g a 
∂μ = ∫⁻ a, f a ∂μ…
· 使用定理 `Measurable.iInf`：∀ {α : Type u_1} {δ : Type u_4} [inst : TopologicalSpac
e α] {mα : MeasurableSpace α} [BorelSpace α]   {mδ : MeasurableSpace δ} [inst_2 
: Con…
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `ENNReal.instSecondCountableTopology`：SecondCountableTopology ENNReal
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `ne_top_of_le_ne_top`：ne_top_of_le_ne_top (hb : b != ⊤) (hab : a <= b) : 
a != ⊤
· 使用定理 `iInf_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] (f :
 ι → α) (i : ι), iInf f ≤ f i
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ENNReal.sub_iInf`：sub_iInf : (a - ⨅ i, f i) = ⨆ i, a - f i
· 使用定理 `MeasureTheory.lintegral_iSup_ae`：lintegral_iSup_ae {f : Nat -> α -> Real
>=0∞} (hf : forall n, Measurable (f n)) (h_mono : forall n, forallᵐ a ∂μ, f n a 
<= f n.succ a) : ∫⁻ a…
· 使用定理 `Measurable.sub`：∀ {G : Type u_2} {α : Type u_3} [inst : MeasurableSpace 
G] [inst_1 : Sub G] {m : MeasurableSpace α} {f g : α → G}   [MeasurableSub₂ G], 
Meas…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `tsub_le_tsub`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : AddCommSemi
group α] [inst_2 : Sub α] [OrderedSub α] {a b c d : α}   [AddLeftMono α], a ≤ b 
→ …
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.ae_all_iff`：ae_all_iff {ι : Sort*} [Countable ι] {p : α ->
 ι -> Prop} : (forallᵐ a ∂μ, forall i, p a i) ↔ forall i, forallᵐ a ∂μ, p a i
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
**Monotone convergence theorem** for nonincreasing sequences of functions.
-/
theorem lintegral_iInf_ae {f : ℕ → α → ℝ≥0∞} (h_meas : ∀ n, Measurable (f n))
    (h_mono : ∀ n : ℕ, f n.succ ≤ᵐ[μ] f n) (h_fin : ∫⁻ a, f 0 a ∂μ ≠ ∞) :
    ∫⁻ a, ⨅ n, f n a ∂μ = ⨅ n, ∫⁻ a, f n a ∂μ :=
  have fn_le_f0 : ∫⁻ a, ⨅ n, f n a ∂μ ≤ ∫⁻ a, f 0 a ∂μ :=
    lintegral_mono fun _ => iInf_le_of_le 0 le_rfl
  have fn_le_f0' : ⨅ n, ∫⁻ a, f n a ∂μ ≤ ∫⁻ a, f 0 a ∂μ := iInf_le_of_le 0 le_rfl
  (ENNReal.sub_right_inj h_fin fn_le_f0 fn_le_f0').1 <|
    show ∫⁻ a, f 0 a ∂μ - ∫⁻ a, ⨅ n, f n a ∂μ = ∫⁻ a, f 0 a ∂μ - ⨅ n, ∫⁻ a, f n a ∂μ from
      calc
        ∫⁻ a, f 0 a ∂μ - ∫⁻ a, ⨅ n, f n a ∂μ = ∫⁻ a, f 0 a - ⨅ n, f n a ∂μ :=
          (lintegral_sub (.iInf h_meas)
              (ne_top_of_le_ne_top h_fin <| lintegral_mono fun _ => iInf_le _ _)
              (ae_of_all _ fun _ => iInf_le _ _)).symm
        _ = ∫⁻ a, ⨆ n, f 0 a - f n a ∂μ := congr rfl (funext fun _ => ENNReal.sub_iInf)
        _ = ⨆ n, ∫⁻ a, f 0 a - f n a ∂μ :=
          (lintegral_iSup_ae (fun n => (h_meas 0).sub (h_meas n)) fun n =>
            (h_mono n).mono fun _ ha => tsub_le_tsub le_rfl ha)
        _ = ⨆ n, ∫⁻ a, f 0 a ∂μ - ∫⁻ a, f n a ∂μ :=
          (have h_mono : ∀ᵐ a ∂μ, ∀ n : ℕ, f n.succ a ≤ f n a := ae_all_iff.2 h_mono
          have h_mono : ∀ n, ∀ᵐ a ∂μ, f n a ≤ f 0 a := fun n =>
            h_mono.mono fun a h => by
              induction n with
              | zero => rfl
              | succ n ih => exact (h n).trans ih
          congr_arg iSup <|
            funext fun n =>
              lintegral_sub (h_meas _) (ne_top_of_le_ne_top h_fin <| lintegral_mono_ae <| h_mono n)
                (h_mono n))
        _ = ∫⁻ a, f 0 a ∂μ - ⨅ n, ∫⁻ a, f n a ∂μ := ENNReal.sub_iInf.symm

/-- **Monotone convergence theorem** for nonincreasing sequences of functions. -/
/-
**MeasureTheory.lintegral_iInf** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_iInf {f : Nat -> α -> Real>=0∞} (h_meas : forall n, Measurable (
f n)) (h_anti : Antitone f) (h_fin : ∫⁻ a, f 0 a ∂μ != ∞) : ∫⁻ a, ⨅ n, f n a ∂μ 
= ⨅ n, ∫⁻ a, f n a ∂μ
参数：h_meas : forall n, Measurable (f n)；h_anti : Antitone f；h_fin : ∫⁻ a, f 0 a ∂
μ != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.lintegral_iInf_ae`：lintegral_iInf_ae {f : Nat -> α -> Real
>=0∞} (h_meas : forall n, Measurable (f n)) (h_mono : forall n : Nat, f n.succ <
=ᵐ[μ] f n) (h_fin : ∫…
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ

--- 原说明 ---
**Monotone convergence theorem** for nonincreasing sequences of functions.
-/
theorem lintegral_iInf {f : ℕ → α → ℝ≥0∞} (h_meas : ∀ n, Measurable (f n)) (h_anti : Antitone f)
    (h_fin : ∫⁻ a, f 0 a ∂μ ≠ ∞) : ∫⁻ a, ⨅ n, f n a ∂μ = ⨅ n, ∫⁻ a, f n a ∂μ :=
  lintegral_iInf_ae h_meas (fun n => ae_of_all _ <| h_anti n.le_succ) h_fin
/-
**MeasureTheory.lintegral_iInf'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_iInf' {f : Nat -> α -> Real>=0∞} (h_meas : forall n, AEMeasurabl
e (f n) μ) (h_anti : forallᵐ a ∂μ, Antitone (fun i => f i a)) (h_fin : ∫⁻ a, f 0
 a ∂μ != ∞) : ∫⁻ a, ⨅ n, f n a ∂μ = ⨅ n, ∫⁻ a, f n a ∂μ
参数：h_meas : forall n, AEMeasurable (f n) μ；h_anti : forallᵐ a ∂μ, Antitone (fun 
i => f i a)；h_fin : ∫⁻ a, f 0 a ∂μ != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `aeSeq.prop_of_mem_aeSeqSet`：prop_of_mem_aeSeqSet (hf : forall i, AEMeasu
rable (f i) μ) {x : α} (hx : x in aeSeqSet hf p) : p x fun n => aeSeq hf p n x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `if_false`：∀ {α : Sort u_1} {x : Decidable False} (t e : α), (if False th
en t else e) = e
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `aeSeq.iInf`：iInf [InfSet β] [Countable ι] (hf : forall i, AEMeasurable (
f i) μ) (hp : forallᵐ x ∂μ, p x fun n => f n x) : ⨅ n, aeSeq hf p n =ᵐ[μ] ⨅ n, f
…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `iInf_apply`：∀ {α : Type u_8} {β : α → Type u_9} {ι : Sort u_10} [inst : 
(i : α) → InfSet (β i)] {f : ι → (a : α) → β a} {a : α},   (⨅ i, f i) a = ⨅ i, f
…
· 使用定理 `MeasureTheory.lintegral_iInf`：lintegral_iInf {f : Nat -> α -> Real>=0∞} 
(h_meas : forall n, Measurable (f n)) (h_anti : Antitone f) (h_fin : ∫⁻ a, f 0 a
 ∂μ != ∞) : ∫⁻ a, …
· 使用定理 `aeSeq.measurable`：measurable (hf : forall i, AEMeasurable (f i) μ) (p : 
α -> (ι -> β) -> Prop) (i : ι) : Measurable (aeSeq hf p i)
· 使用定理 `aeSeq.aeSeq_n_eq_fun_n_ae`：aeSeq_n_eq_fun_n_ae [Countable ι] (hf : foral
l i, AEMeasurable (f i) μ) (hp : forallᵐ x ∂μ, p x fun n => f n x) (n : ι) : aeS
eq hf p n =ᵐ[μ]…
-/
theorem lintegral_iInf' {f : ℕ → α → ℝ≥0∞} (h_meas : ∀ n, AEMeasurable (f n) μ)
    (h_anti : ∀ᵐ a ∂μ, Antitone (fun i ↦ f i a)) (h_fin : ∫⁻ a, f 0 a ∂μ ≠ ∞) :
    ∫⁻ a, ⨅ n, f n a ∂μ = ⨅ n, ∫⁻ a, f n a ∂μ := by
  simp_rw [← iInf_apply]
  let p : α → (ℕ → ℝ≥0∞) → Prop := fun _ f' => Antitone f'
  have hp : ∀ᵐ x ∂μ, p x fun i => f i x := h_anti
  have h_ae_seq_mono : Antitone (aeSeq h_meas p) := by
    intro n m hnm x
    by_cases hx : x ∈ aeSeqSet h_meas p
    · exact aeSeq.prop_of_mem_aeSeqSet h_meas hx hnm
    · simp only [aeSeq, hx, if_false]
      exact le_rfl
  rw [lintegral_congr_ae (aeSeq.iInf h_meas hp).symm]
  simp_rw [iInf_apply]
  rw [lintegral_iInf (aeSeq.measurable h_meas p) h_ae_seq_mono]
  · congr
    exact funext fun n ↦ lintegral_congr_ae (aeSeq.aeSeq_n_eq_fun_n_ae h_meas hp n)
  · rwa [lintegral_congr_ae (aeSeq.aeSeq_n_eq_fun_n_ae h_meas hp 0)]

/-- **Monotone convergence theorem** for an infimum over a directed family and indexed by a
countable type. -/
/-
**MeasureTheory.lintegral_iInf_directed_of_measurable** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory`。
形式化陈述：lintegral_iInf_directed_of_measurable [Countable β] {f : β -> α -> Real>=0
∞} {μ : Measure α} (hμ : μ != 0) (hf : forall b, Measurable (f b)) (hf_int : for
all b, ∫⁻ a, f b a ∂μ != ∞) (h_directed : Directed (· >= ·) f) : ∫⁻ a, ⨅ b, f b 
a ∂μ = ⨅ b, ∫⁻ a, f b a ∂μ
参数：hμ : μ != 0；hf : forall b, Measurable (f b)；hf_int : forall b, ∫⁻ a, f b a ∂μ
 != ∞；h_directed : Directed (· >= ·) f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_encodable`：nonempty_encodable (α : Type*) [Countable α] : Nonem
pty (Encodable α)
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_of_empty`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α
] [IsEmpty ι] (f : ι → α), iInf f = ⊤
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `ENNReal.top_mul`：∀ {a : ENNReal}, a ≠ 0 → ⊤ * a = ⊤
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.measure_univ_ne_zero`：measure_univ_ne_zero : μ uni
v != 0 ↔ μ != 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f :
 ι → α} {a : α}, (∀ (i : ι), a ≤ f i) → a ≤ iInf f
· 使用定理 `iInf_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] (f :
 ι → α) (i : ι), iInf f ≤ f i
· 使用定理 `iInf_le_of_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α
] {f : ι → α} {a : α} (i : ι), f i ≤ a → iInf f ≤ a
· 使用定理 `Directed.sequence_le`：sequence_le (a : α) : f (hf.sequence f (Encodable.
encode a + 1)) <= f a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.lintegral_iInf`：lintegral_iInf {f : Nat -> α -> Real>=0∞} 
(h_meas : forall n, Measurable (f n)) (h_anti : Antitone f) (h_fin : ∫⁻ a, f 0 a
 ∂μ != ∞) : ∫⁻ a, …
· 使用定理 `Directed.sequence_anti`：sequence_anti : Antitone (f ∘ hf.sequence f)
· 使用定理 `MeasureTheory.lintegral_mono`：lintegral_mono ⦃f g : α -> Real>=0∞⦄ (hfg 
: f <= g) : ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ

--- 原说明 ---
**Monotone convergence theorem** for an infimum over a directed family and index
ed by a
countable type.
-/
theorem lintegral_iInf_directed_of_measurable [Countable β]
    {f : β → α → ℝ≥0∞} {μ : Measure α} (hμ : μ ≠ 0) (hf : ∀ b, Measurable (f b))
    (hf_int : ∀ b, ∫⁻ a, f b a ∂μ ≠ ∞) (h_directed : Directed (· ≥ ·) f) :
    ∫⁻ a, ⨅ b, f b a ∂μ = ⨅ b, ∫⁻ a, f b a ∂μ := by
  cases nonempty_encodable β
  cases isEmpty_or_nonempty β
  · simp only [iInf_of_empty, lintegral_const,
      ENNReal.top_mul (Measure.measure_univ_ne_zero.mpr hμ)]
  inhabit β
  have : ∀ a, ⨅ b, f b a = ⨅ n, f (h_directed.sequence f n) a := by
    refine fun a =>
      le_antisymm (le_iInf fun n => iInf_le _ _)
        (le_iInf fun b => iInf_le_of_le (Encodable.encode b + 1) ?_)
    exact h_directed.sequence_le b a
  calc
    ∫⁻ a, ⨅ b, f b a ∂μ
    _ = ∫⁻ a, ⨅ n, (f ∘ h_directed.sequence f) n a ∂μ := by simp only [this, Function.comp_apply]
    _ = ⨅ n, ∫⁻ a, (f ∘ h_directed.sequence f) n a ∂μ := by
      rw [lintegral_iInf ?_ h_directed.sequence_anti]
      · exact hf_int _
      · exact fun n => hf _
    _ = ⨅ b, ∫⁻ a, f b a ∂μ := by
      refine le_antisymm (le_iInf fun b => ?_) (le_iInf fun n => ?_)
      · exact iInf_le_of_le (Encodable.encode b + 1) (lintegral_mono <| h_directed.sequence_le b)
      · exact iInf_le (fun b => ∫⁻ a, f b a ∂μ) _
/-
**MeasureTheory.lintegral_tendsto_of_tendsto_of_antitone** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory`。
形式化陈述：lintegral_tendsto_of_tendsto_of_antitone {f : Nat -> α -> Real>=0∞} {F : α
 -> Real>=0∞} (hf : forall n, AEMeasurable (f n) μ) (h_anti : forallᵐ x ∂μ, Anti
tone fun n => f n x) (h0 : ∫⁻ a, f 0 a ∂μ != ∞) (h_tendsto : forallᵐ x ∂μ, Tends
to (fun n => f n x) atTop (𝓝 (F x))) : Tendsto (fun n => ∫⁻ x, f n x ∂μ) atTop (
𝓝 (∫⁻ x, F x ∂μ))
参数：hf : forall n, AEMeasurable (f n) μ；h_anti : forallᵐ x ∂μ, Antitone fun n => 
f n x；h0 : ∫⁻ a, f 0 a ∂μ != ∞；h_tendsto : forallᵐ x ∂μ, Tendsto (fun n => f n x
) atTop (𝓝 (F x))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.lintegral_mono_ae`：lintegral_mono_ae {f g : α -> Real>=0∞}
 (h : forallᵐ a ∂μ, f a <= g a) : ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_iInf'`：lintegral_iInf' {f : Nat -> α -> Real>=0∞
} (h_meas : forall n, AEMeasurable (f n) μ) (h_anti : forallᵐ a ∂μ, Antitone (fu
n i => f i a)) (h_f…
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `tendsto_nhds_unique`：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : F
ilter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) :
 a = b
· 使用定理 `ENNReal.instT2Space`：T2Space ENNReal
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `tendsto_atTop_iInf`：tendsto_atTop_iInf (h_anti : Antitone f) : Tendsto f
 atTop (𝓝 (⨅ i, f i))
· 使用定理 `LinearOrder.infConvergenceClass`：∀ {α : Type u_1} [inst : TopologicalSpa
ce α] [inst_1 : LinearOrder α] [OrderTopology α], InfConvergenceClass α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
-/
theorem lintegral_tendsto_of_tendsto_of_antitone {f : ℕ → α → ℝ≥0∞} {F : α → ℝ≥0∞}
    (hf : ∀ n, AEMeasurable (f n) μ) (h_anti : ∀ᵐ x ∂μ, Antitone fun n ↦ f n x)
    (h0 : ∫⁻ a, f 0 a ∂μ ≠ ∞)
    (h_tendsto : ∀ᵐ x ∂μ, Tendsto (fun n ↦ f n x) atTop (𝓝 (F x))) :
    Tendsto (fun n ↦ ∫⁻ x, f n x ∂μ) atTop (𝓝 (∫⁻ x, F x ∂μ)) := by
  have : Antitone fun n ↦ ∫⁻ x, f n x ∂μ := fun i j hij ↦
    lintegral_mono_ae (h_anti.mono fun x hx ↦ hx hij)
  suffices key : ∫⁻ x, F x ∂μ = ⨅ n, ∫⁻ x, f n x ∂μ by
    rw [key]
    exact tendsto_atTop_iInf this
  rw [← lintegral_iInf' hf h_anti h0]
  refine lintegral_congr_ae ?_
  filter_upwards [h_anti, h_tendsto] with _ hx_anti hx_tendsto
    using tendsto_nhds_unique hx_tendsto (tendsto_atTop_iInf hx_anti)

section UnifTight

local infixr:25 " →ₛ " => SimpleFunc

open Function in
/-- If `f : α → ℝ≥0∞` has finite integral, then there exists a measurable set `s` of finite measure
such that the integral of `f` over `sᶜ` is less than a given positive number.

Also used to prove an `Lᵖ`-norm version in
`MeasureTheory.MemLp.exists_eLpNorm_indicator_compl_le`. -/
/-
**MeasureTheory.exists_setLIntegral_compl_lt** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：exists_setLIntegral_compl_lt {f : α -> Real>=0∞} (hf : ∫⁻ a, f a ∂μ != ∞) 
{ε : Real>=0∞} (hε : ε != 0) : exists s : Set α, MeasurableSet s ∧ μ s < ∞ ∧ ∫⁻ 
a in sᶜ, f a ∂μ < ε
参数：hf : ∫⁻ a, f a ∂μ != ∞；hε : ε != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.empty`：MeasurableSet.empty [MeasurableSpace α] : Measurabl
eSet (∅ : Set α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.compl_empty`：compl_empty : (∅ : Set α)ᶜ = univ
· 使用定理 `MeasureTheory.Measure.restrict_univ`：restrict_univ : μ.restrict univ = μ
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ENNReal.sub_lt_self`：∀ {a b : ENNReal}, a ≠ ⊤ → a ≠ 0 → b ≠ 0 → a - b < 
a
· 使用定理 `MeasureTheory.SimpleFunc.measurable`：∀ {α : Type u_1} {β : Type u_2} [in
st : MeasurableSpace α] [inst_1 : MeasurableSpace β]   (f : MeasureTheory.Simple
Func α β), Measurable ⇑f
· 使用定理 `MeasureTheory.SimpleFunc.FinMeasSupp.of_lintegral_ne_top`：of_lintegral_n
e_top {f : α ->ₛ Real>=0∞} (h : f.lintegral μ != ∞) : f.FinMeasSupp μ
· 使用定理 `ne_top_of_le_ne_top`：ne_top_of_le_ne_top (hb : b != ⊤) (hab : a <= b) : 
a != ⊤
· 使用定理 `MeasureTheory.lintegral_mono`：lintegral_mono ⦃f g : α -> Real>=0∞⦄ (hfg 
: f <= g) : ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ
· 使用定理 `MeasureTheory.SimpleFunc.lintegral_eq_lintegral`：∀ {α : Type u_1} {m : M
easurableSpace α} (f : MeasureTheory.SimpleFunc α ENNReal) (μ : MeasureTheory.Me
asure α),   ∫⁻ (a : α), f a ∂μ = f.li…
· 使用定理 `measurableSet_support`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {m : 
MeasurableSpace α} {mβ : MeasurableSpace β} [inst : Zero β]   [MeasurableSinglet
onClass β],…
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `instMeasurableEqOfSecondCountableTopologyOfT2Space`：∀ {α : Type u_1} [in
st : TopologicalSpace α] [inst_1 : MeasurableSpace α] [OpensMeasurableSpace α]  
 [SecondCountableTopology α] [T2Space α]…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `ENNReal.instSecondCountableTopology`：SecondCountableTopology ENNReal
· 使用定理 `ENNReal.instT2Space`：T2Space ENNReal
· 使用定理 `MeasureTheory.setLIntegral_congr_fun`：setLIntegral_congr_fun {f g : α ->
 Real>=0∞} {s : Set α} (hs : MeasurableSet s) (hfg : EqOn f g s) : ∫⁻ x in s, f 
x ∂μ = ∫⁻ x in s, g x ∂μ
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `tsub_zero`：tsub_zero (a : α) : a - 0 = a
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
If `f : α → ℝ≥0∞` has finite integral, then there exists a measurable set `s` of
 finite measure
such that the integral of `f` over `sᶜ` is less than a given positive number.

Also used to prove an `Lᵖ`-norm version in
`MeasureTheory.MemLp.exists_eLpNorm_indicator_compl_le`.
-/
theorem exists_setLIntegral_compl_lt {f : α → ℝ≥0∞} (hf : ∫⁻ a, f a ∂μ ≠ ∞)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ s : Set α, MeasurableSet s ∧ μ s < ∞ ∧ ∫⁻ a in sᶜ, f a ∂μ < ε := by
  by_cases hf₀ : ∫⁻ a, f a ∂μ = 0
  · exact ⟨∅, .empty, by simp, by simpa [hf₀, pos_iff_ne_zero]⟩
  obtain ⟨g, hgf, hg_meas, hgsupp, hgε⟩ :
      ∃ g ≤ f, Measurable g ∧ μ (support g) < ∞ ∧ ∫⁻ a, f a ∂μ - ε < ∫⁻ a, g a ∂μ := by
    obtain ⟨g, hgf, hgε⟩ : ∃ (g : α →ₛ ℝ≥0∞) (_ : g ≤ f), ∫⁻ a, f a ∂μ - ε < g.lintegral μ := by
      simpa only [← lt_iSup_iff, ← lintegral_def] using ENNReal.sub_lt_self hf hf₀ hε
    refine ⟨g, hgf, g.measurable, ?_, by rwa [g.lintegral_eq_lintegral]⟩
    exact SimpleFunc.FinMeasSupp.of_lintegral_ne_top <| ne_top_of_le_ne_top hf <|
      g.lintegral_eq_lintegral μ ▸ lintegral_mono hgf
  refine ⟨_, measurableSet_support hg_meas, hgsupp, ?_⟩
  calc
    ∫⁻ a in (support g)ᶜ, f a ∂μ
      = ∫⁻ a in (support g)ᶜ, f a - g a ∂μ := setLIntegral_congr_fun
      (measurableSet_support hg_meas).compl <| by intro; simp_all
    _ ≤ ∫⁻ a, f a - g a ∂μ := setLIntegral_le_lintegral _ _
    _ = ∫⁻ a, f a ∂μ - ∫⁻ a, g a ∂μ :=
      lintegral_sub hg_meas (ne_top_of_le_ne_top hf <| lintegral_mono hgf) (ae_of_all _ hgf)
    _ < ε := ENNReal.sub_lt_of_lt_add (lintegral_mono hgf) <|
      ENNReal.lt_add_of_sub_lt_left (.inl hf) hgε

/-- For any function `f : α → ℝ≥0∞`, there exists a measurable function `g ≤ f` with the same
integral over any measurable set. -/
/-
**MeasureTheory.exists_measurable_le_setLIntegral_eq_of_integrable** 是 Mathlib 中
的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：exists_measurable_le_setLIntegral_eq_of_integrable {f : α -> Real>=0∞} (hf
 : ∫⁻ a, f a ∂μ != ∞) : exists (g : α -> Real>=0∞), Measurable g ∧ g <= f ∧ fora
ll s : Set α, MeasurableSet s -> ∫⁻ a in s, f a ∂μ = ∫⁻ a in s, g a ∂μ
参数：hf : ∫⁻ a, f a ∂μ != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.exists_measurable_le_lintegral_eq`：exists_measurable_le_li
ntegral_eq (f : α -> Real>=0∞) : exists g : α -> Real>=0∞, Measurable g ∧ g <= f
 ∧ ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `MeasureTheory.setLIntegral_compl`：setLIntegral_compl {f : α -> Real>=0∞}
 {s : Set α} (hsm : MeasurableSet s) (hfs : ∫⁻ x in s, f x ∂μ != ∞) : ∫⁻ x in sᶜ
, f x ∂μ = ∫⁻ x, f x ∂…
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `ne_top_of_le_ne_top`：ne_top_of_le_ne_top (hb : b != ⊤) (hab : a <= b) : 
a != ⊤
· 使用定理 `MeasureTheory.setLIntegral_le_lintegral`：setLIntegral_le_lintegral (s : 
Set α) (f : α -> Real>=0∞) : ∫⁻ x in s, f x ∂μ <= ∫⁻ x, f x ∂μ
· 使用定理 `tsub_le_tsub`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : AddCommSemi
group α] [inst_2 : Sub α] [OrderedSub α] {a b c d : α}   [AddLeftMono α], a ≤ b 
→ …
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `MeasureTheory.lintegral_mono_fn'`：∀ {α : Type u_1} {m : MeasurableSpace 
α} {μ ν : MeasureTheory.Measure α},   μ ≤ ν → ∀ ⦃f g : α → ENNReal⦄, (∀ (x : α),
 f x ≤ g x) → ∫⁻ (a : …
· 使用定理 `MeasureTheory.lintegral_mono`：lintegral_mono ⦃f g : α -> Real>=0∞⦄ (hfg 
: f <= g) : ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ

--- 原说明 ---
For any function `f : α → ℝ≥0∞`, there exists a measurable function `g ≤ f` with
 the same
integral over any measurable set.
-/
theorem exists_measurable_le_setLIntegral_eq_of_integrable {f : α → ℝ≥0∞} (hf : ∫⁻ a, f a ∂μ ≠ ∞) :
    ∃ (g : α → ℝ≥0∞), Measurable g ∧ g ≤ f ∧ ∀ s : Set α, MeasurableSet s →
      ∫⁻ a in s, f a ∂μ = ∫⁻ a in s, g a ∂μ := by
  obtain ⟨g, hmg, hgf, hifg⟩ := exists_measurable_le_lintegral_eq (μ := μ) f
  use g, hmg, hgf
  refine fun s hms ↦ le_antisymm ?_ (lintegral_mono hgf)
  rw [← compl_compl s, setLIntegral_compl hms.compl, setLIntegral_compl hms.compl, hifg]
  · gcongr; apply hgf
  · rw [hifg] at hf
    exact ne_top_of_le_ne_top hf (setLIntegral_le_lintegral _ _)
  · exact ne_top_of_le_ne_top hf (setLIntegral_le_lintegral _ _)

end UnifTight

end MeasureTheory

