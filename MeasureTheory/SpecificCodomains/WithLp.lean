/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# Integrability in `WithLp`

We prove that `f : X → PiLp q E` is in `Lᵖ` if and only if for all `i`, `f · i` is in `Lᵖ`.
We do the same for `f : X → WithLp q (E × F)`.
-/

public section

open scoped ENNReal

namespace MeasureTheory

variable {X : Type*} {mX : MeasurableSpace X} {μ : Measure X} {p q : ℝ≥0∞} [Fact (1 ≤ q)]

section Pi

variable {ι : Type*} [Fintype ι] {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] {f : X → PiLp q E}

/-
**MeasureTheory.memLp_piLp_iff** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：memLp_piLp_iff : MemLp f p μ ↔ forall i, MemLp (f · i) p μ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `LipschitzWith.memLp_comp_iff_of_antilipschitz`：memLp_comp_iff_of_antilip
schitz {α E F} {K K'} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
 [NormedAddCommGroup F] {f : α -> E…
· 使用引理 `PiLp.lipschitzWith_ofLp`：lipschitzWith_ofLp [forall i, PseudoEMetricSpac
e (β i)] : LipschitzWith 1 (@ofLp p (forall i, β i))
· 使用定理 `PiLp.antilipschitzWith_ofLp`：antilipschitzWith_ofLp [forall i, PseudoEMe
tricSpace (β i)] : AntilipschitzWith ((Fintype.card ι : Real>=0) ^ (1 / p).toRea
l) (@ofLp p (fora…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma memLp_piLp_iff : MemLp f p μ ↔ ∀ i, MemLp (f · i) p μ := by
  simp_rw [← memLp_pi_iff, ← Function.comp_apply (f := WithLp.ofLp)]
  exact (PiLp.lipschitzWith_ofLp q E).memLp_comp_iff_of_antilipschitz
    (PiLp.antilipschitzWith_ofLp q E) (by simp) |>.symm

alias ⟨MemLp.eval_piLp, MemLp.of_eval_piLp⟩ := memLp_piLp_iff
/-
**MeasureTheory.integrable_piLp_iff** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：integrable_piLp_iff : Integrable f μ ↔ forall i, Integrable (f · i) μ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma integrable_piLp_iff : Integrable f μ ↔ ∀ i, Integrable (f · i) μ := by
  simp_rw [← memLp_one_iff_integrable, memLp_piLp_iff]

alias ⟨Integrable.eval_piLp, Integrable.of_eval_piLp⟩ := integrable_piLp_iff

variable [∀ i, NormedSpace ℝ (E i)] [∀ i, CompleteSpace (E i)]
/-
**MeasureTheory.eval_integral_piLp** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：eval_integral_piLp (hf : forall i, Integrable (f · i) μ) (i : ι) : (∫ x, f
 x ∂μ) i = ∫ x, f x i ∂μ
参数：hf : forall i, Integrable (f · i) μ；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PiLp.proj_apply`：∀ (p : ENNReal) {𝕜 : Type u_1} {ι : Type u_2} (β : ι → 
Type u_4) [inst : Semiring 𝕜]   [inst_1 : (i : ι) → NormedAddCommGroup (β i)] [i
nst_2…
· 使用定理 `ContinuousLinearMap.integral_comp_comm`：integral_comp_comm [CompleteSpac
e E] (L : E ->L[𝕜] Fₗ) {φ : X -> E} (φ_int : Integrable φ μ) : ∫ x, L (φ x) ∂μ =
 L (∫ x, φ x ∂μ)
· 使用定理 `MeasureTheory.Integrable.of_eval_piLp`：∀ {X : Type u_1} {mX : Measurable
Space X} {μ : MeasureTheory.Measure X} {q : ENNReal} [inst : Fact (1 ≤ q)]   {ι 
: Type u_2} [inst_1 : Finty…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma eval_integral_piLp (hf : ∀ i, Integrable (f · i) μ) (i : ι) :
    (∫ x, f x ∂μ) i = ∫ x, f x i ∂μ := by
  rw [← PiLp.proj_apply (𝕜 := ℝ) q E i (∫ x, f x ∂μ), ← ContinuousLinearMap.integral_comp_comm]
  · simp
  exact Integrable.of_eval_piLp hf

end Pi

section Prod

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] {f : X → WithLp q (E × F)}

/-
**MeasureTheory.memLp_prodLp_iff** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：memLp_prodLp_iff : MemLp f p μ ↔ MemLp (fun x => (f x).fst) p μ ∧ MemLp (f
un x => (f x).snd) p μ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `LipschitzWith.memLp_comp_iff_of_antilipschitz`：memLp_comp_iff_of_antilip
schitz {α E F} {K K'} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
 [NormedAddCommGroup F] {f : α -> E…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `WithLp.prod_lipschitzWith_ofLp`：prod_lipschitzWith_ofLp [PseudoEMetricSp
ace α] [PseudoEMetricSpace β] : LipschitzWith 1 (@ofLp p (α × β))
· 使用引理 `WithLp.prod_antilipschitzWith_ofLp`：prod_antilipschitzWith_ofLp [PseudoE
MetricSpace α] [PseudoEMetricSpace β] : AntilipschitzWith ((2 : Real>=0) ^ (1 / 
p).toReal) (@ofLp p (α ×…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma memLp_prodLp_iff :
    MemLp f p μ ↔ MemLp (fun x ↦ (f x).fst) p μ ∧ MemLp (fun x ↦ (f x).snd) p μ := by
  simp_rw [← WithLp.ofLp_fst, ← WithLp.ofLp_snd, ← memLp_prod_iff]
  exact (WithLp.prod_lipschitzWith_ofLp q E F).memLp_comp_iff_of_antilipschitz
    (WithLp.prod_antilipschitzWith_ofLp q E F) (by simp) |>.symm
/-
**MeasureTheory.MemLp.prodLp_fst** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.MemLp`
。
形式化陈述：∀ {X : Type u_1} {mX : MeasurableSpace X} {μ : MeasureTheory.Measure X} {p
 q : ENNReal} [inst : Fact (1 ≤ q)]   {E : Type u_2} {F : Type u_3} [inst_1 : No
rmedAddCommGroup E] [inst_2 : NormedAddCommGroup F]   {f : X → WithLp q (E × F)}
, MeasureTheory.MemLp f p μ → MeasureTheory.MemLp (fun x => (f x).fst) p μ
参数：1 ≤ q；E × F；fun x => (f x).fst。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `MeasureTheory.memLp_prodLp_iff`：memLp_prodLp_iff : MemLp f p μ ↔ MemLp (
fun x => (f x).fst) p μ ∧ MemLp (fun x => (f x).snd) p μ
-/
lemma MemLp.prodLp_fst (h : MemLp f p μ) : MemLp (fun x ↦ (f x).fst) p μ :=
  memLp_prodLp_iff.1 h |>.1
/-
**MeasureTheory.MemLp.prodLp_snd** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.MemLp`
。
形式化陈述：∀ {X : Type u_1} {mX : MeasurableSpace X} {μ : MeasureTheory.Measure X} {p
 q : ENNReal} [inst : Fact (1 ≤ q)]   {E : Type u_2} {F : Type u_3} [inst_1 : No
rmedAddCommGroup E] [inst_2 : NormedAddCommGroup F]   {f : X → WithLp q (E × F)}
, MeasureTheory.MemLp f p μ → MeasureTheory.MemLp (fun x => (f x).snd) p μ
参数：1 ≤ q；E × F；fun x => (f x).snd。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `MeasureTheory.memLp_prodLp_iff`：memLp_prodLp_iff : MemLp f p μ ↔ MemLp (
fun x => (f x).fst) p μ ∧ MemLp (fun x => (f x).snd) p μ
-/
lemma MemLp.prodLp_snd (h : MemLp f p μ) : MemLp (fun x ↦ (f x).snd) p μ :=
  memLp_prodLp_iff.1 h |>.2

alias ⟨_, MemLp.of_fst_of_snd_prodLp⟩ := memLp_prodLp_iff
/-
**MeasureTheory.integrable_prodLp_iff** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：integrable_prodLp_iff : Integrable f μ ↔ Integrable (fun x => (f x).fst) μ
 ∧ Integrable (fun x => (f x).snd) μ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma integrable_prodLp_iff :
    Integrable f μ ↔
    Integrable (fun x ↦ (f x).fst) μ ∧
    Integrable (fun x ↦ (f x).snd) μ := by
  simp_rw [← memLp_one_iff_integrable, memLp_prodLp_iff]
/-
**MeasureTheory.Integrable.prodLp_fst** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.I
ntegrable`。
形式化陈述：∀ {X : Type u_1} {mX : MeasurableSpace X} {μ : MeasureTheory.Measure X} {q
 : ENNReal} [inst : Fact (1 ≤ q)]   {E : Type u_2} {F : Type u_3} [inst_1 : Norm
edAddCommGroup E] [inst_2 : NormedAddCommGroup F]   {f : X → WithLp q (E × F)}, 
MeasureTheory.Integrable f μ → MeasureTheory.Integrable (fun x => (f x).fst) μ
参数：1 ≤ q；E × F；fun x => (f x).fst。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `MeasureTheory.integrable_prodLp_iff`：integrable_prodLp_iff : Integrable 
f μ ↔ Integrable (fun x => (f x).fst) μ ∧ Integrable (fun x => (f x).snd) μ
-/
lemma Integrable.prodLp_fst (h : Integrable f μ) : Integrable (fun x ↦ (f x).fst) μ :=
  integrable_prodLp_iff.1 h |>.1
/-
**MeasureTheory.Integrable.prodLp_snd** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.I
ntegrable`。
形式化陈述：∀ {X : Type u_1} {mX : MeasurableSpace X} {μ : MeasureTheory.Measure X} {q
 : ENNReal} [inst : Fact (1 ≤ q)]   {E : Type u_2} {F : Type u_3} [inst_1 : Norm
edAddCommGroup E] [inst_2 : NormedAddCommGroup F]   {f : X → WithLp q (E × F)}, 
MeasureTheory.Integrable f μ → MeasureTheory.Integrable (fun x => (f x).snd) μ
参数：1 ≤ q；E × F；fun x => (f x).snd。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `MeasureTheory.integrable_prodLp_iff`：integrable_prodLp_iff : Integrable 
f μ ↔ Integrable (fun x => (f x).fst) μ ∧ Integrable (fun x => (f x).snd) μ
-/
lemma Integrable.prodLp_snd (h : Integrable f μ) : Integrable (fun x ↦ (f x).snd) μ :=
  integrable_prodLp_iff.1 h |>.2

alias ⟨_, Integrable.of_fst_of_snd_prodLp⟩ := integrable_prodLp_iff

variable [NormedSpace ℝ E] [NormedSpace ℝ F]
/-
**MeasureTheory.fst_integral_withLp** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：fst_integral_withLp [CompleteSpace F] (hf : Integrable f μ) : (∫ x, f x ∂μ
).fst = ∫ x, (f x).fst ∂μ
参数：hf : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithLp.ofLp_fst`：∀ {p : ENNReal} {α : Type u_2} {β : Type u_3} (x : With
Lp p (α × β)), x.ofLp.1 = x.fst
· 使用定理 `ContinuousLinearEquiv.integral_comp_comm`：integral_comp_comm (L : E ≃L[𝕜
] F) (φ : X -> E) : ∫ x, L (φ x) ∂μ = L (∫ x, φ x ∂μ)
· 使用定理 `fst_integral`：fst_integral [CompleteSpace F] {f : X -> E × F} (hf : Inte
grable f μ) : (∫ x, f x ∂μ).1 = ∫ x, (f x).1 ∂μ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ContinuousLinearEquiv.integrable_comp_iff`：ContinuousLinearEquiv.integra
ble_comp_iff {φ : α -> H} (L : H ≃SL[σ] E) : Integrable (fun a : α => L (φ a)) μ
 ↔ Integrable φ μ
-/
theorem fst_integral_withLp [CompleteSpace F] (hf : Integrable f μ) :
    (∫ x, f x ∂μ).fst = ∫ x, (f x).fst ∂μ := by
  rw [← WithLp.ofLp_fst]
  conv => enter [1, 1]; change WithLp.prodContinuousLinearEquiv q ℝ E F _
  rw [← ContinuousLinearEquiv.integral_comp_comm, fst_integral]
  · rfl
  · exact (ContinuousLinearEquiv.integrable_comp_iff _).2 hf
/-
**MeasureTheory.snd_integral_withLp** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：snd_integral_withLp [CompleteSpace E] (hf : Integrable f μ) : (∫ x, f x ∂μ
).snd = ∫ x, (f x).snd ∂μ
参数：hf : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithLp.ofLp_snd`：∀ {p : ENNReal} {α : Type u_2} {β : Type u_3} (x : With
Lp p (α × β)), x.ofLp.2 = x.snd
· 使用定理 `ContinuousLinearEquiv.integral_comp_comm`：integral_comp_comm (L : E ≃L[𝕜
] F) (φ : X -> E) : ∫ x, L (φ x) ∂μ = L (∫ x, φ x ∂μ)
· 使用定理 `snd_integral`：snd_integral [CompleteSpace E] {f : X -> E × F} (hf : Inte
grable f μ) : (∫ x, f x ∂μ).2 = ∫ x, (f x).2 ∂μ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ContinuousLinearEquiv.integrable_comp_iff`：ContinuousLinearEquiv.integra
ble_comp_iff {φ : α -> H} (L : H ≃SL[σ] E) : Integrable (fun a : α => L (φ a)) μ
 ↔ Integrable φ μ
-/
theorem snd_integral_withLp [CompleteSpace E] (hf : Integrable f μ) :
    (∫ x, f x ∂μ).snd = ∫ x, (f x).snd ∂μ := by
  rw [← WithLp.ofLp_snd]
  conv => enter [1, 1]; change WithLp.prodContinuousLinearEquiv q ℝ E F _
  rw [← ContinuousLinearEquiv.integral_comp_comm, snd_integral]
  · rfl
  · exact (ContinuousLinearEquiv.integrable_comp_iff _).2 hf

end Prod

end MeasureTheory

