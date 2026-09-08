/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Integrability in a product space

We prove that `f : X → Π i, E i` is in `Lᵖ` if and only if for all `i`, `f · i` is in `Lᵖ`.
We do the same for `f : X → (E × F)`.
-/

public section

namespace MeasureTheory

open scoped ENNReal

variable {X : Type*} {mX : MeasurableSpace X} {μ : Measure X} {p : ℝ≥0∞}

section Pi

variable {ι : Type*} [Fintype ι] {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    {f : X → Π i, E i}

/-
**MeasureTheory.memLp_pi_iff** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：memLp_pi_iff : MemLp f p μ ↔ forall i, MemLp (f · i) p μ where mp hf i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.comp_memLp`：LipschitzWith.comp_memLp {α E F} {K} [Measurab
leSpace α] {μ : Measure α} [NormedAddCommGroup E] [NormedAddCommGroup F] {f : α 
-> E} {g : E -…
· 使用定理 `LipschitzWith.eval`：∀ {ι : Type x} {α : ι → Type u} [inst : (i : ι) → Ps
eudoEMetricSpace (α i)] [inst_1 : Fintype ι] (i : ι),   LipschitzWith 1 (Functio
n.eval i…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_pi_single`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : Decida
bleEq ι] [inst_1 : (a : ι) → AddCommMonoid (M a)] (a : ι)   (f : (a : ι) → M a) 
(s : Finse…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.memLp_finsetSum'`：memLp_finsetSum' [ContinuousAdd ε'] {ι} 
(s : Finset ι) {f : ι -> α -> ε'} (hf : forall i in s, MemLp (f i) p μ) : MemLp 
(∑ i in s, f i) p μ
· 使用定理 `Pi.continuousAdd`：∀ {ι : Type u_1} {C : ι → Type u_6} [inst : (i : ι) → 
TopologicalSpace (C i)] [inst_1 : (i : ι) → Add (C i)]   [∀ (i : ι), ContinuousA
dd (C …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Isometry.lipschitz`：lipschitz (h : Isometry f) : LipschitzWith 1 f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Pi.single_zero`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) → Ze
ro (M i)] [inst_1 : DecidableEq ι] (i : ι), Pi.single i 0 = 0
-/
lemma memLp_pi_iff : MemLp f p μ ↔ ∀ i, MemLp (f · i) p μ where
  mp hf i := (LipschitzWith.eval (α := E) i).comp_memLp rfl hf
  mpr hf := by
    classical
    have : f = ∑ i, (Pi.single i) ∘ (f · i) := by ext; simp
    rw [this]
    refine memLp_finsetSum' _ fun i _ ↦ ?_
    exact (Isometry.single i).lipschitz.comp_memLp (by simp) (hf i)

alias ⟨MemLp.eval, MemLp.of_eval⟩ := memLp_pi_iff
/-
**MeasureTheory.integrable_pi_iff** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：integrable_pi_iff : Integrable f μ ↔ forall i, Integrable (f · i) μ
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
lemma integrable_pi_iff : Integrable f μ ↔ ∀ i, Integrable (f · i) μ := by
  simp_rw [← memLp_one_iff_integrable, memLp_pi_iff]

alias ⟨Integrable.eval, Integrable.of_eval⟩ := integrable_pi_iff

variable [∀ i, NormedSpace ℝ (E i)] [∀ i, CompleteSpace (E i)]
/-
**MeasureTheory.eval_integral** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：eval_integral (hf : forall i, Integrable (f · i) μ) (i : ι) : (∫ x, f x ∂μ
) i = ∫ x, f x i ∂μ
参数：hf : forall i, Integrable (f · i) μ；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearMap.integral_comp_comm`：integral_comp_comm [CompleteSpac
e E] (L : E ->L[𝕜] Fₗ) {φ : X -> E} (φ_int : Integrable φ μ) : ∫ x, L (φ x) ∂μ =
 L (∫ x, φ x ∂μ)
· 使用定理 `MeasureTheory.Integrable.of_eval`：∀ {X : Type u_1} {mX : MeasurableSpace
 X} {μ : MeasureTheory.Measure X} {ι : Type u_2} [inst : Fintype ι]   {E : ι → T
ype u_3} [inst_1 : (i …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma eval_integral (hf : ∀ i, Integrable (f · i) μ) (i : ι) :
    (∫ x, f x ∂μ) i = ∫ x, f x i ∂μ := by
  simp [← ContinuousLinearMap.proj_apply (R := ℝ) i (∫ x, f x ∂μ),
    ← ContinuousLinearMap.integral_comp_comm _ (Integrable.of_eval hf)]

end Pi

section Prod

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] {f : X → E × F}

/-
**MeasureTheory.memLp_prod_iff** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：memLp_prod_iff : MemLp f p μ ↔ MemLp (fun x => (f x).fst) p μ ∧ MemLp (fun
 x => (f x).snd) p μ where mp h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.comp_memLp`：LipschitzWith.comp_memLp {α E F} {K} [Measurab
leSpace α] {μ : Measure α} [NormedAddCommGroup E] [NormedAddCommGroup F] {f : α 
-> E} {g : E -…
· 使用定理 `LipschitzWith.prod_fst`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetri
cSpace α] [inst_1 : PseudoEMetricSpace β], LipschitzWith 1 Prod.fst
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LipschitzWith.prod_snd`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetri
cSpace α] [inst_1 : PseudoEMetricSpace β], LipschitzWith 1 Prod.snd
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Prod.mk.eta`：∀ {α : Type u_1} {β : Type u_2} {p : α × β}, (p.1, p.2) = p
· 使用定理 `MeasureTheory.MemLp.add`：∀ {α : Type u_1} {ε : Type u_3} {m : Measurable
Space α} [inst : TopologicalSpace ε] [inst_1 : ESeminormedAddMonoid ε]   {p : EN
NReal} {μ : M…
· 使用定理 `Prod.continuousAdd`：∀ {M : Type u_3} {N : Type u_4} [inst : TopologicalS
pace M] [inst_1 : Add M] [ContinuousAdd M]   [inst_3 : TopologicalSpace N] [inst
_4 : Add…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Isometry.lipschitz`：lipschitz (h : Isometry f) : LipschitzWith 1 f
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma memLp_prod_iff :
    MemLp f p μ ↔ MemLp (fun x ↦ (f x).fst) p μ ∧ MemLp (fun x ↦ (f x).snd) p μ where
  mp h := ⟨LipschitzWith.prod_fst.comp_memLp (by simp) h,
    LipschitzWith.prod_snd.comp_memLp (by simp) h⟩
  mpr h := by
    have : f = (AddMonoidHom.inl E F) ∘ (fun x ↦ (f x).fst) +
        (AddMonoidHom.inr E F) ∘ (fun x ↦ (f x).snd) := by
      ext; all_goals simp
    rw [this]
    exact MemLp.add (Isometry.inl.lipschitz.comp_memLp (by simp) h.1)
      (Isometry.inr.lipschitz.comp_memLp (by simp) h.2)
/-
**MeasureTheory.MemLp.fst** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.MemLp`。
形式化陈述：∀ {X : Type u_1} {mX : MeasurableSpace X} {μ : MeasureTheory.Measure X} {p
 : ENNReal} {E : Type u_2} {F : Type u_3}   [inst : NormedAddCommGroup E] [inst_
1 : NormedAddCommGroup F] {f : X → E × F},   MeasureTheory.MemLp f p μ → Measure
Theory.MemLp (fun x => (f x).1) p μ
参数：fun x => (f x).1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `MeasureTheory.memLp_prod_iff`：memLp_prod_iff : MemLp f p μ ↔ MemLp (fun 
x => (f x).fst) p μ ∧ MemLp (fun x => (f x).snd) p μ where mp h
-/
lemma MemLp.fst (h : MemLp f p μ) : MemLp (fun x ↦ (f x).fst) p μ :=
  memLp_prod_iff.1 h |>.1
/-
**MeasureTheory.MemLp.snd** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.MemLp`。
形式化陈述：∀ {X : Type u_1} {mX : MeasurableSpace X} {μ : MeasureTheory.Measure X} {p
 : ENNReal} {E : Type u_2} {F : Type u_3}   [inst : NormedAddCommGroup E] [inst_
1 : NormedAddCommGroup F] {f : X → E × F},   MeasureTheory.MemLp f p μ → Measure
Theory.MemLp (fun x => (f x).2) p μ
参数：fun x => (f x).2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `MeasureTheory.memLp_prod_iff`：memLp_prod_iff : MemLp f p μ ↔ MemLp (fun 
x => (f x).fst) p μ ∧ MemLp (fun x => (f x).snd) p μ where mp h
-/
lemma MemLp.snd (h : MemLp f p μ) : MemLp (fun x ↦ (f x).snd) p μ :=
  memLp_prod_iff.1 h |>.2

alias ⟨_, MemLp.of_fst_snd⟩ := memLp_prod_iff

end Prod

end MeasureTheory

