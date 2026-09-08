/-
Copyright (c) 2020 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity

/-!
# Scalar multiplication on ℒp space
-/

public noncomputable section

open Filter

open scoped ENNReal

namespace MeasureTheory

variable {α F : Type*} {m : MeasurableSpace α} {p : ℝ≥0∞} {q : ℝ} {μ : Measure α}
  [NormedAddCommGroup F] {f : α → F}

section Lp

/-!
### Bounded actions by normed rings
In this section we show inequalities on the norm.
-/

section IsBoundedSMul

variable {𝕜 : Type*} [NormedRing 𝕜] [MulActionWithZero 𝕜 F] [IsBoundedSMul 𝕜 F] {c : 𝕜}

/-
**MeasureTheory.eLpNorm'_const_smul_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：∀ {α : Type u_1} {F : Type u_2} {m : MeasurableSpace α} {q : ℝ} {μ : Measu
reTheory.Measure α}   [inst : NormedAddCommGroup F] {f : α → F} {𝕜 : Type u_3} [
inst_1 : NormedRing 𝕜] [inst_2 : MulActionWithZero 𝕜 F]   [IsBoundedSMul 𝕜 F] {c
 : 𝕜}, 0 < q → MeasureTheory.eLpNorm' (c • f) q μ ≤ ‖c‖ₑ * MeasureTheory.eLpNorm
' f q μ
参数：c • f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.eLpNorm'_le_nnreal_smul_eLpNorm'_of_ae_le_mul`：∀ {α : Type
 u_1} {F : Type u_3} {G : Type u_4} {m : MeasurableSpace α} {μ : MeasureTheory.M
easure α}   [inst : NormedAddCommGroup F] [inst_1…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `nnnorm_smul_le`：nnnorm_smul_le (r : α) (x : β) : ‖r • x‖₊ <= ‖r‖₊ * ‖x‖₊
-/
theorem eLpNorm'_const_smul_le (hq : 0 < q) : eLpNorm' (c • f) q μ ≤ ‖c‖ₑ * eLpNorm' f q μ :=
  eLpNorm'_le_nnreal_smul_eLpNorm'_of_ae_le_mul (Eventually.of_forall fun _ => nnnorm_smul_le ..) hq
/-
**MeasureTheory.eLpNormEssSup_const_smul_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：eLpNormEssSup_const_smul_le : eLpNormEssSup (c • f) μ <= ‖c‖ₑ * eLpNormEss
Sup f μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul`：e
LpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul {f : α -> F} {g : α -> G}
 {c : Real>=0} (h : forallᵐ x ∂μ, ‖f x‖₊ <= c * ‖g x‖₊) : e…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem eLpNormEssSup_const_smul_le : eLpNormEssSup (c • f) μ ≤ ‖c‖ₑ * eLpNormEssSup f μ :=
  eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul
    (Eventually.of_forall fun _ => by simp [nnnorm_smul_le])
/-
**MeasureTheory.eLpNorm_const_smul_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：eLpNorm_const_smul_le : eLpNorm (c • f) p μ <= ‖c‖ₑ * eLpNorm f p μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul`：eLpNorm_le_nn
real_smul_eLpNorm_of_ae_le_mul {f : α -> F} {g : α -> G} {c : Real>=0} (h : fora
llᵐ x ∂μ, ‖f x‖₊ <= c * ‖g x‖₊) (p : Real>=0∞) …
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem eLpNorm_const_smul_le : eLpNorm (c • f) p μ ≤ ‖c‖ₑ * eLpNorm f p μ :=
  eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul
    (Eventually.of_forall fun _ => by simp [nnnorm_smul_le]) _
/-
**MeasureTheory.MemLp.const_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.MemLp`
。
形式化陈述：∀ {α : Type u_1} {F : Type u_2} {m : MeasurableSpace α} {p : ENNReal} {μ :
 MeasureTheory.Measure α}   [inst : NormedAddCommGroup F] {f : α → F} {𝕜 : Type 
u_3} [inst_1 : NormedRing 𝕜] [inst_2 : MulActionWithZero 𝕜 F]   [IsBoundedSMul 𝕜
 F], MeasureTheory.MemLp f p μ → ∀ (c : 𝕜), MeasureTheory.MemLp (c • f) p μ
参数：c : 𝕜；c • f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEStronglyMeasurable.const_smul`：∀ {α : Type u_1} {β : Typ
e u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory
.Measure α}   {f : α → β} {𝕜 : Type…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.eLpNorm_const_smul_le`：eLpNorm_const_smul_le : eLpNorm (c 
• f) p μ <= ‖c‖ₑ * eLpNorm f p μ
· 使用定理 `ENNReal.mul_lt_top`：mul_lt_top : a < ∞ -> b < ∞ -> a * b < ∞
· 使用定理 `ENNReal.coe_lt_top`：∀ {r : NNReal}, ↑r < ⊤
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem MemLp.const_smul (hf : MemLp f p μ) (c : 𝕜) : MemLp (c • f) p μ :=
  ⟨hf.1.const_smul c, eLpNorm_const_smul_le.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hf.2)⟩
/-
**MeasureTheory.MemLp.const_mul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.MemLp`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.
Measure α} {𝕜 : Type u_3}   [inst : NormedRing 𝕜] {f : α → 𝕜}, MeasureTheory.Mem
Lp f p μ → ∀ (c : 𝕜), MeasureTheory.MemLp (fun x => c * f x) p μ
参数：c : 𝕜；fun x => c * f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MemLp.const_smul`：∀ {α : Type u_1} {F : Type u_2} {m : Mea
surableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddC
ommGroup F] {f : α →…
-/
theorem MemLp.const_mul {f : α → 𝕜} (hf : MemLp f p μ) (c : 𝕜) : MemLp (fun x => c * f x) p μ :=
  hf.const_smul c
/-
**MeasureTheory.MemLp.mul_const** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.MemLp`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.
Measure α} {𝕜 : Type u_3}   [inst : NormedRing 𝕜] {f : α → 𝕜}, MeasureTheory.Mem
Lp f p μ → ∀ (c : 𝕜), MeasureTheory.MemLp (fun x => f x * c) p μ
参数：c : 𝕜；fun x => f x * c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MemLp.const_smul`：∀ {α : Type u_1} {F : Type u_2} {m : Mea
surableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddC
ommGroup F] {f : α →…
-/
theorem MemLp.mul_const {f : α → 𝕜} (hf : MemLp f p μ) (c : 𝕜) :
    MemLp (fun x => f x * c) p μ :=
  hf.const_smul (MulOpposite.op c)

end IsBoundedSMul

section ENormSMulClass

variable {𝕜 : Type*} [NormedRing 𝕜]
  {ε : Type*} [TopologicalSpace ε] [ESeminormedAddMonoid ε] [SMul 𝕜 ε] [ENormSMulClass 𝕜 ε]
  {c : 𝕜} {f : α → ε}

/-
**MeasureTheory.eLpNorm'_const_smul_le'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {q : ℝ} {μ : MeasureTheory.Measur
e α} {𝕜 : Type u_3} [inst : NormedRing 𝕜]   {ε : Type u_4} [inst_1 : Topological
Space ε] [inst_2 : ESeminormedAddMonoid ε] [inst_3 : SMul 𝕜 ε]   [ENormSMulClass
 𝕜 ε] {c : 𝕜} {f : α → ε},   0 < q → MeasureTheory.eLpNorm' (c • f) q μ ≤ ‖c‖ₑ *
 MeasureTheory.eLpNorm' f q μ
参数：c • f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.eLpNorm'_le_nnreal_smul_eLpNorm'_of_ae_le_mul'`：∀ {α : Typ
e u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {ε : Type u_5} {ε' 
: Type u_6}   [inst : TopologicalSpace ε] [inst_1 …
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用引理 `enorm_smul`：enorm_smul [ENorm α] [ENorm β] [SMul α β] [ENormSMulClass α 
β] (r : α) (x : β) : ‖r • x‖ₑ = ‖r‖ₑ * ‖x‖ₑ
-/
theorem eLpNorm'_const_smul_le' (hq : 0 < q) : eLpNorm' (c • f) q μ ≤ ‖c‖ₑ * eLpNorm' f q μ :=
  eLpNorm'_le_nnreal_smul_eLpNorm'_of_ae_le_mul'
    (Eventually.of_forall fun _ ↦ le_of_eq (enorm_smul ..)) hq
/-
**MeasureTheory.eLpNormEssSup_const_smul_le'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：eLpNormEssSup_const_smul_le' : eLpNormEssSup (c • f) μ <= ‖c‖ₑ * eLpNormEs
sSup f μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul'`：
eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul' {f : α -> ε} {g : α -> 
ε'} {c : Real>=0∞} (h : forallᵐ x ∂μ, ‖f x‖ₑ <= c * ‖g x‖ₑ) …
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `enorm_smul`：enorm_smul [ENorm α] [ENorm β] [SMul α β] [ENormSMulClass α 
β] (r : α) (x : β) : ‖r • x‖ₑ = ‖r‖ₑ * ‖x‖ₑ
-/
theorem eLpNormEssSup_const_smul_le' : eLpNormEssSup (c • f) μ ≤ ‖c‖ₑ * eLpNormEssSup f μ :=
  eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul'
    (Eventually.of_forall fun _ => by simp [enorm_smul])
/-
**MeasureTheory.eLpNorm_const_smul_le'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：eLpNorm_const_smul_le' : eLpNorm (c • f) p μ <= ‖c‖ₑ * eLpNorm f p μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul'`：eLpNorm_le_n
nreal_smul_eLpNorm_of_ae_le_mul' {f : α -> ε} {g : α -> ε'} {c : Real>=0} (h : f
orallᵐ x ∂μ, ‖f x‖ₑ <= c * ‖g x‖ₑ) (p : Real>=0∞…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用引理 `enorm_smul`：enorm_smul [ENorm α] [ENorm β] [SMul α β] [ENormSMulClass α 
β] (r : α) (x : β) : ‖r • x‖ₑ = ‖r‖ₑ * ‖x‖ₑ
-/
theorem eLpNorm_const_smul_le' : eLpNorm (c • f) p μ ≤ ‖c‖ₑ * eLpNorm f p μ :=
  eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul'
    (Eventually.of_forall fun _ => le_of_eq (enorm_smul ..)) _
/-
**MeasureTheory.MemLp.const_smul'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.MemLp
`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.
Measure α} {𝕜 : Type u_3}   [inst : NormedRing 𝕜] {ε : Type u_4} [inst_1 : Topol
ogicalSpace ε] [inst_2 : ESeminormedAddMonoid ε]   [inst_3 : SMul 𝕜 ε] [ENormSMu
lClass 𝕜 ε] {f : α → ε} [ContinuousConstSMul 𝕜 ε],   MeasureTheory.MemLp f p μ →
 ∀ (c : 𝕜), MeasureTheory.MemLp (c • f) p μ
参数：c : 𝕜；c • f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEStronglyMeasurable.const_smul`：∀ {α : Type u_1} {β : Typ
e u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory
.Measure α}   {f : α → β} {𝕜 : Type…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.eLpNorm_const_smul_le'`：eLpNorm_const_smul_le' : eLpNorm (
c • f) p μ <= ‖c‖ₑ * eLpNorm f p μ
· 使用定理 `ENNReal.mul_lt_top`：mul_lt_top : a < ∞ -> b < ∞ -> a * b < ∞
· 使用定理 `ENNReal.coe_lt_top`：∀ {r : NNReal}, ↑r < ⊤
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem MemLp.const_smul' [ContinuousConstSMul 𝕜 ε] (hf : MemLp f p μ) (c : 𝕜) :
    MemLp (c • f) p μ :=
  ⟨hf.1.const_smul c, eLpNorm_const_smul_le'.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hf.2)⟩
/-
**MeasureTheory.MemLp.const_mul'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.MemLp`
。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.
Measure α} {𝕜 : Type u_3}   [inst : NormedRing 𝕜] {f : α → 𝕜}, MeasureTheory.Mem
Lp f p μ → ∀ (c : 𝕜), MeasureTheory.MemLp (fun x => c * f x) p μ
参数：c : 𝕜；fun x => c * f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MemLp.const_smul`：∀ {α : Type u_1} {F : Type u_2} {m : Mea
surableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddC
ommGroup F] {f : α →…
-/
theorem MemLp.const_mul' {f : α → 𝕜} (hf : MemLp f p μ) (c : 𝕜) : MemLp (fun x => c * f x) p μ :=
  hf.const_smul c

end ENormSMulClass

/-!
### Bounded actions by normed division rings
The inequalities in the previous section are now tight.

TODO: do these results hold for any `NormedRing` assuming `NormSMulClass`?
-/

section NormedSpace

variable {𝕜 : Type*} [NormedDivisionRing 𝕜] [Module 𝕜 F] [NormSMulClass 𝕜 F]

/-
**MeasureTheory.eLpNorm'_const_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：∀ {α : Type u_1} {F : Type u_2} {m : MeasurableSpace α} {q : ℝ} {μ : Measu
reTheory.Measure α}   [inst : NormedAddCommGroup F] {𝕜 : Type u_3} [inst_1 : Nor
medDivisionRing 𝕜] [inst_2 : _root_.Module 𝕜 F]   [NormSMulClass 𝕜 F] {f : α → F
} (c : 𝕜),   0 < q → MeasureTheory.eLpNorm' (c • f) q μ = ‖c‖ₑ * MeasureTheory.e
LpNorm' f q μ
参数：c : 𝕜；c • f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `enorm_zero`：∀ {E : Type u_8} [inst : TopologicalSpace E] [inst_1 : ESemi
normedAddMonoid E], ‖0‖ₑ = 0
· 使用定理 `ENNReal.zero_rpow_of_pos`：zero_rpow_of_pos {y : Real} (h : 0 < y) : (0 :
 Real>=0∞) ^ y = 0
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `MeasureTheory.eLpNorm'_const_smul_le`：∀ {α : Type u_1} {F : Type u_2} {m
 : MeasurableSpace α} {q : ℝ} {μ : MeasureTheory.Measure α}   [inst : NormedAddC
ommGroup F] {f : α → F} {𝕜…
· 使用定理 `ENNReal.mul_le_of_le_div'`：mul_le_of_le_div' (h : a <= b / c) : c * a <=
 b
· 使用定理 `ENNReal.div_eq_inv_mul`：∀ {a b : ENNReal}, a / b = b⁻¹ * a
· 使用定理 `inv_smul_smul₀`：∀ {α : Type u_4} {β : Type u_5} [inst : GroupWithZero α]
 [inst_1 : MulAction α β] {a : α},   a ≠ 0 → ∀ (x : β), a⁻¹ • a • x = x
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `enorm_inv`：enorm_inv {a : α} (ha : a != 0) : ‖a⁻¹‖ₑ = ‖a‖ₑ⁻¹
-/
theorem eLpNorm'_const_smul {f : α → F} (c : 𝕜) (hq_pos : 0 < q) :
    eLpNorm' (c • f) q μ = ‖c‖ₑ * eLpNorm' f q μ := by
  obtain rfl | hc := eq_or_ne c 0
  · simp [eLpNorm'_eq_lintegral_enorm, hq_pos]
  refine le_antisymm (eLpNorm'_const_smul_le hq_pos) <| ENNReal.mul_le_of_le_div' ?_
  simpa [enorm_inv, hc, ENNReal.div_eq_inv_mul]
    using eLpNorm'_const_smul_le (c := c⁻¹) (f := c • f) hq_pos
/-
**MeasureTheory.eLpNormEssSup_const_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：eLpNormEssSup_const_smul (c : 𝕜) (f : α -> F) : eLpNormEssSup (c • f) μ = 
‖c‖ₑ * eLpNormEssSup f μ
参数：c : 𝕜；f : α -> F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `enorm_smul`：enorm_smul [ENorm α] [ENorm β] [SMul α β] [ENormSMulClass α 
β] (r : α) (x : β) : ‖r • x‖ₑ = ‖r‖ₑ * ‖x‖ₑ
· 使用定理 `instENormSMulClass`：∀ {α : Type u_1} {β : Type u_2} [inst : SeminormedRi
ng α] [inst_1 : SeminormedAddGroup β] [inst_2 : SMul α β]   [NormSMulClass α β],
 ENormSM…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ENNReal.essSup_const_mul`：essSup_const_mul {a : Real>=0∞} : essSup (fun 
x : α => a * f x) μ = a * essSup f μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eLpNormEssSup_const_smul (c : 𝕜) (f : α → F) :
    eLpNormEssSup (c • f) μ = ‖c‖ₑ * eLpNormEssSup f μ := by
  simp_rw [eLpNormEssSup_eq_essSup_enorm, Pi.smul_apply, enorm_smul,
    ENNReal.essSup_const_mul]
/-
**MeasureTheory.eLpNorm_const_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：eLpNorm_const_smul (c : 𝕜) (f : α -> F) (p : Real>=0∞) (μ : Measure α) : e
LpNorm (c • f) p μ = ‖c‖ₑ * eLpNorm f p μ
参数：c : 𝕜；f : α -> F；p : Real>=0∞；μ : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `MeasureTheory.eLpNorm_zero`：eLpNorm_zero : eLpNorm (0 : α -> ε) p μ = 0
· 使用定理 `enorm_zero`：∀ {E : Type u_8} [inst : TopologicalSpace E] [inst_1 : ESemi
normedAddMonoid E], ‖0‖ₑ = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `MeasureTheory.eLpNorm_const_smul_le`：eLpNorm_const_smul_le : eLpNorm (c 
• f) p μ <= ‖c‖ₑ * eLpNorm f p μ
· 使用定理 `ENNReal.mul_le_of_le_div'`：mul_le_of_le_div' (h : a <= b / c) : c * a <=
 b
· 使用定理 `ENNReal.div_eq_inv_mul`：∀ {a b : ENNReal}, a / b = b⁻¹ * a
· 使用定理 `inv_smul_smul₀`：∀ {α : Type u_4} {β : Type u_5} [inst : GroupWithZero α]
 [inst_1 : MulAction α β] {a : α},   a ≠ 0 → ∀ (x : β), a⁻¹ • a • x = x
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `enorm_inv`：enorm_inv {a : α} (ha : a != 0) : ‖a⁻¹‖ₑ = ‖a‖ₑ⁻¹
-/
theorem eLpNorm_const_smul (c : 𝕜) (f : α → F) (p : ℝ≥0∞) (μ : Measure α) :
    eLpNorm (c • f) p μ = ‖c‖ₑ * eLpNorm f p μ := by
  obtain rfl | hc := eq_or_ne c 0
  · simp
  refine le_antisymm eLpNorm_const_smul_le <| ENNReal.mul_le_of_le_div' ?_
  simpa [enorm_inv, hc, ENNReal.div_eq_inv_mul]
    using eLpNorm_const_smul_le (c := c⁻¹) (f := c • f)
/-
**MeasureTheory.eLpNorm_nsmul** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：eLpNorm_nsmul [NormedSpace Real F] (n : Nat) (f : α -> F) : eLpNorm (n • f
) p μ = n * eLpNorm f p μ
参数：n : Nat；f : α -> F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用定理 `Real.enorm_natCast`：∀ (n : ℕ), ‖↑n‖ₑ = ↑n
· 使用定理 `MeasureTheory.eLpNorm_const_smul`：eLpNorm_const_smul (c : 𝕜) (f : α -> F
) (p : Real>=0∞) (μ : Measure α) : eLpNorm (c • f) p μ = ‖c‖ₑ * eLpNorm f p μ
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
-/
lemma eLpNorm_nsmul [NormedSpace ℝ F] (n : ℕ) (f : α → F) :
    eLpNorm (n • f) p μ = n * eLpNorm f p μ := by
  simpa [Nat.cast_smul_eq_nsmul] using eLpNorm_const_smul (n : ℝ) f ..

end NormedSpace

end Lp
end MeasureTheory

