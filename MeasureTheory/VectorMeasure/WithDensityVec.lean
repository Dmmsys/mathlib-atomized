/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.VectorMeasure.SetIntegral
public import Mathlib.MeasureTheory.VectorMeasure.WithDensity

/-!
# Vector measure with density with respect to a vector measure

Given a vector measure `μ`, a function `f` and a pairing `B`, we define the vector measure
with density `f` and pairing `B`, denoted `μ.withDensity f B`. It associates to a
measurable set the mass `∫ᵛ x in s, f x ∂[B; μ]`.

This file implements the basic property of this notion. Notably, we show in `variation_withDensity`
that the variation of the vector measure `μ.withDensity f B` is the positive measure with
density `‖f‖` with respect to the positive measure `μ.variation`.
-/

open Set Filter
open scoped Topology ENNReal

@[expose] public section

namespace MeasureTheory.VectorMeasure

local infixr:25 " →ₛ " => SimpleFunc

variable {X E F G : Type*} {mX : MeasurableSpace X}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {μ : VectorMeasure X F} {f g : X → E} {B : E →L[ℝ] F →L[ℝ] G} {s : Set X}

open scoped Classical in
/-- The vector measure with density `f` with respect to a vector measure `μ`, associating to a
measurable set the mass `∫ᵛ x in s, f x ∂[B; μ]`.
If `f` is not integrable, we use the junk value `0`. -/
/-
**MeasureTheory.VectorMeasure.withDensity** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheo
ry.VectorMeasure`。
形式化陈述：withDensity (μ : VectorMeasure X F) (f : X -> E) (B : E ->L[Real] F ->L[Re
al] G) : VectorMeasure X G
参数：μ : VectorMeasure X F；f : X -> E；B : E ->L[Real] F ->L[Real] G。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.VectorMeasure.setIntegral_eq_zero_of_not_measurableSet`：se
tIntegral_eq_zero_of_not_measurableSet (hs : ¬MeasurableSet s) : ∫ᵛ x in s, f x 
∂[B; μ] = 0

--- 原说明 ---
The vector measure with density `f` with respect to a vector measure `μ`, associ
ating to a
measurable set the mass `∫ᵛ x in s, f x ∂[B; μ]`.
If `f` is not integrable, we use the junk value `0`.
-/
noncomputable def withDensity (μ : VectorMeasure X F) (f : X → E) (B : E →L[ℝ] F →L[ℝ] G) :
    VectorMeasure X G :=
  if h : μ.Integrable f then
    { measureOf' s := ∫ᵛ x in s, f x ∂[B; μ]
      empty' := by simp
      not_measurable' s hs := setIntegral_eq_zero_of_not_measurableSet hs
      m_iUnion' s s_meas s_disj := hasSum_setIntegral_iUnion s_meas s_disj h.integrableOn }
  else 0
/-
**MeasureTheory.VectorMeasure.withDensity_apply** 是 Mathlib 中的一个引理，位于命名空间 `Measu
reTheory.VectorMeasure`。
形式化陈述：withDensity_apply (hf : μ.Integrable f) : μ.withDensity f B s = ∫ᵛ x in s,
 f x ∂[B; μ]
参数：hf : μ.Integrable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.setIntegral_eq_zero_of_not_measurableSet`：se
tIntegral_eq_zero_of_not_measurableSet (hs : ¬MeasurableSet s) : ∫ᵛ x in s, f x 
∂[B; μ] = 0
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma withDensity_apply (hf : μ.Integrable f) :
    μ.withDensity f B s = ∫ᵛ x in s, f x ∂[B; μ] := by
  simp [withDensity, hf]
/-
**MeasureTheory.VectorMeasure.withDensity_apply_univ** 是 Mathlib 中的一个引理，位于命名空间 `
MeasureTheory.VectorMeasure`。
形式化陈述：withDensity_apply_univ : μ.withDensity f B univ = ∫ᵛ x, f x ∂[B; μ]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.VectorMeasure.withDensity_apply`：withDensity_apply (hf : μ
.Integrable f) : μ.withDensity f B s = ∫ᵛ x in s, f x ∂[B; μ]
· 使用定理 `MeasureTheory.VectorMeasure.restrict_univ`：restrict_univ : v.restrict Se
t.univ = v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `MeasureTheory.VectorMeasure.setIntegral_eq_zero_of_not_measurableSet`：se
tIntegral_eq_zero_of_not_measurableSet (hs : ¬MeasurableSet s) : ∫ᵛ x in s, f x 
∂[B; μ] = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `MeasureTheory.VectorMeasure.instIsZeroApplySet`：∀ {α : Type u_1} {m : Me
asurableSpace α} {M : Type u_3} [inst : AddCommMonoid M] [inst_1 : TopologicalSp
ace M],   IsZeroApply (MeasureTheory…
· 使用定理 `MeasureTheory.VectorMeasure.integral_undef`：integral_undef (h : ¬ μ.Inte
grable f) : ∫ᵛ x, f x ∂[B; μ] = 0
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma withDensity_apply_univ : μ.withDensity f B univ = ∫ᵛ x, f x ∂[B; μ] := by
  by_cases hf : μ.Integrable f
  · simp [withDensity_apply hf]
  · simp [withDensity, hf, integral_undef]

@[simp]
/-
**MeasureTheory.VectorMeasure.withDensity_zero_vectorMeasure** 是 Mathlib 中的一个引理，
位于命名空间 `MeasureTheory.VectorMeasure`。
形式化陈述：withDensity_zero_vectorMeasure : (0 : VectorMeasure X F).withDensity f B =
 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.VectorMeasure.ext`：ext {s t : VectorMeasure α M} (h : fora
ll i : Set α, MeasurableSet i -> s i = t i) : s = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.VectorMeasure.withDensity_apply`：withDensity_apply (hf : μ
.Integrable f) : μ.withDensity f B s = ∫ᵛ x in s, f x ∂[B; μ]
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.VectorMeasure.restrict_zero`：restrict_zero {i : Set α} : (
0 : VectorMeasure α M).restrict i = 0
· 使用定理 `MeasureTheory.VectorMeasure.integral_zero_vectorMeasure`：integral_zero_v
ectorMeasure : ∫ᵛ x, f x ∂[B; (0 : VectorMeasure X F)] = 0
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `MeasureTheory.VectorMeasure.instIsZeroApplySet`：∀ {α : Type u_1} {m : Me
asurableSpace α} {M : Type u_3} [inst : AddCommMonoid M] [inst_1 : TopologicalSp
ace M],   IsZeroApply (MeasureTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma withDensity_zero_vectorMeasure : (0 : VectorMeasure X F).withDensity f B = 0 := by
  ext s hs
  simp [withDensity_apply]

@[to_fun (attr := simp) withDensity_fun_zero]
/-
**MeasureTheory.VectorMeasure.withDensity_zero** 是 Mathlib 中的一个引理，位于命名空间 `Measur
eTheory.VectorMeasure`。
形式化陈述：withDensity_zero : μ.withDensity 0 B = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.VectorMeasure.ext`：ext {s t : VectorMeasure α M} (h : fora
ll i : Set α, MeasurableSet i -> s i = t i) : s = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.VectorMeasure.withDensity_apply`：withDensity_apply (hf : μ
.Integrable f) : μ.withDensity f B s = ∫ᵛ x in s, f x ∂[B; μ]
· 使用定理 `MeasureTheory.VectorMeasure.integral_zero`：integral_zero : ∫ᵛ _, 0 ∂[B; 
μ] = 0
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `MeasureTheory.VectorMeasure.instIsZeroApplySet`：∀ {α : Type u_1} {m : Me
asurableSpace α} {M : Type u_3} [inst : AddCommMonoid M] [inst_1 : TopologicalSp
ace M],   IsZeroApply (MeasureTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma withDensity_zero : μ.withDensity 0 B = 0 := by
  ext s hs
  simp [withDensity_apply]
/-
**MeasureTheory.VectorMeasure.withDensity_congr** 是 Mathlib 中的一个引理，位于命名空间 `Measu
reTheory.VectorMeasure`。
形式化陈述：withDensity_congr (h : f =ᵐ[μ.variation] g) : μ.withDensity f B = μ.withDe
nsity g B
参数：h : f =ᵐ[μ.variation] g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.VectorMeasure.setIntegral_eq_zero_of_not_measurableSet`：se
tIntegral_eq_zero_of_not_measurableSet (hs : ¬MeasurableSet s) : ∫ᵛ x in s, f x 
∂[B; μ] = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MeasureTheory.Integrable.congr`：∀ {α : Type u_1} {ε : Type u_5} {m : Mea
surableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace ε]   [ins
t_1 : ContinuousENor…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `MeasureTheory.VectorMeasure.mk.injEq`：∀ {α : Type u_3} [inst : Measurabl
eSpace α] {M : Type u_4} [inst_1 : AddCommMonoid M] [inst_2 : TopologicalSpace M
]   (measureOf' : Set α → …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.VectorMeasure.setIntegral_congr_ae`：setIntegral_congr_ae (
h : forallᵐ x ∂μ.variation, x in s -> f x = g x) : ∫ᵛ x in s, f x ∂[B; μ] = ∫ᵛ x
 in s, g x ∂[B; μ]
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integrable_congr`：integrable_congr {f g : α -> ε} (h : f =
ᵐ[μ] g) : Integrable f μ ↔ Integrable g μ
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma withDensity_congr (h : f =ᵐ[μ.variation] g) :
    μ.withDensity f B = μ.withDensity g B := by
  by_cases hf : μ.Integrable f
  · simp only [withDensity, hf, ↓reduceDIte, Integrable.congr hf h, mk.injEq]
    ext s
    apply setIntegral_congr_ae
    filter_upwards [h] with x hx xs using hx
  · have : ¬(μ.Integrable g) := by simpa [← integrable_congr h] using hf
    simp [withDensity, hf, this]
/-
**MeasureTheory.VectorMeasure.restrict_withDensity** 是 Mathlib 中的一个引理，位于命名空间 `Me
asureTheory.VectorMeasure`。
形式化陈述：restrict_withDensity (hf : μ.Integrable f) : (μ.withDensity f B).restrict 
s = (μ.restrict s).withDensity f B
参数：hf : μ.Integrable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.VectorMeasure.ext`：ext {s t : VectorMeasure α M} (h : fora
ll i : Set α, MeasurableSet i -> s i = t i) : s = t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.restrict_apply`：restrict_apply {i : Set α} (
hi : MeasurableSet i) {j : Set α} (hj : MeasurableSet j) : v.restrict i j = v (j
 inter i)
· 使用引理 `MeasureTheory.VectorMeasure.withDensity_apply`：withDensity_apply (hf : μ
.Integrable f) : μ.withDensity f B s = ∫ᵛ x in s, f x ∂[B; μ]
· 使用定理 `MeasureTheory.VectorMeasure.Integrable.restrict`：∀ {X : Type u_2} {E : T
ype u_4} {F : Type u_5} {mX : MeasurableSpace X} [inst : NormedAddCommGroup E]  
 [inst_1 : NormedAddCommGroup F] {f :…
· 使用定理 `MeasureTheory.VectorMeasure.restrict_restrict`：restrict_restrict {s t : 
Set α} (hs : MeasurableSet s) (ht : MeasurableSet t) : (v.restrict t).restrict s
 = v.restrict (s inter t)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.VectorMeasure.restrict_not_measurable`：restrict_not_measur
able {i : Set α} (hi : ¬MeasurableSet i) : v.restrict i = 0
· 使用引理 `MeasureTheory.VectorMeasure.withDensity_zero_vectorMeasure`：withDensity_
zero_vectorMeasure : (0 : VectorMeasure X F).withDensity f B = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma restrict_withDensity (hf : μ.Integrable f) :
    (μ.withDensity f B).restrict s = (μ.restrict s).withDensity f B := by
  by_cases hs : MeasurableSet s; swap
  · simp [restrict_not_measurable _ hs]
  · ext t ht
    simp only [hs, ht, restrict_apply]
    rw [withDensity_apply hf, withDensity_apply hf.restrict, restrict_restrict _ ht hs]
/-
**MeasureTheory.VectorMeasure.variation_WithDensity_le** 是 Mathlib 中的一个引理，位于命名空间
 `MeasureTheory.VectorMeasure`。
形式化陈述：variation_WithDensity_le : (μ.withDensity f B).variation <= (μ.transpose B
).variation.withDensity (fun x => ‖f x‖ₑ)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用引理 `MeasureTheory.VectorMeasure.variation_le_of_forall_enorm_le`：variation_l
e_of_forall_enorm_le {m : Measure X} (h : forall E, MeasurableSet E -> ‖μ E‖ₑ <=
 m E) : μ.variation <= m
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.VectorMeasure.withDensity_apply`：withDensity_apply (hf : μ
.Integrable f) : μ.withDensity f B s = ∫ᵛ x in s, f x ∂[B; μ]
· 使用定理 `MeasureTheory.withDensity_apply`：withDensity_apply (f : α -> Real>=0∞) {
s : Set α} (hs : MeasurableSet s) : μ.withDensity f s = ∫⁻ a in s, f a ∂μ
· 使用定理 `MeasureTheory.VectorMeasure.enorm_setIntegral_le_lintegral_enorm_transpo
se`：enorm_setIntegral_le_lintegral_enorm_transpose : ‖∫ᵛ x in s, f x ∂[B; μ]‖ₑ <
= ∫⁻ x in s, ‖f x‖ₑ ∂(μ.transpose B).variation
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.VectorMeasure.variation.congr_simp`：∀ {X : Type u_1} {mX :
 MeasurableSpace X} {V : Type u_2} [inst : TopologicalSpace V] [inst_1 : ENormed
AddCommMonoid V]   [inst_2 : T2Space V…
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `MeasureTheory.VectorMeasure.setIntegral_eq_zero_of_not_measurableSet`：se
tIntegral_eq_zero_of_not_measurableSet (hs : ¬MeasurableSet s) : ∫ᵛ x in s, f x 
∂[B; μ] = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用引理 `MeasureTheory.VectorMeasure.variation_zero`：variation_zero : (0 : Vector
Measure X V).variation = 0
-/
lemma variation_WithDensity_le :
    (μ.withDensity f B).variation ≤ (μ.transpose B).variation.withDensity (fun x ↦ ‖f x‖ₑ) := by
  by_cases hf : μ.Integrable f
  · apply variation_le_of_forall_enorm_le (fun s hs ↦ ?_)
    rw [withDensity_apply hf, MeasureTheory.withDensity_apply _ hs]
    apply enorm_setIntegral_le_lintegral_enorm_transpose
  · simp [withDensity, hf, Measure.zero_le ]

set_option backward.isDefEq.respectTransparency.types false in
/-- If `‖B x y‖ = ‖B · y‖ * ‖x‖` for all `x, y`, then the variation of a vector measure with
density `f` wrt `μ` is the measure with density `‖f‖ₑ` with respect to the variation of `μ`.

The condition on `B` is necessary: for a counterexample without it, let `B` be the scalar
product in `ℝ²` and `f x` everywhere horizontal and `μ s` everywhere vertical.
Then `μ.withDensity f B = 0` so its variation is zero, while the integral of `‖f‖ₑ` is not.

See also `variation_withDensity` under the very common condition `‖B x y‖ = ‖x‖ ‖y‖`.
-/
/-
**MeasureTheory.VectorMeasure.variation_withDensity'** 是 Mathlib 中的一个引理，位于命名空间 `
MeasureTheory.VectorMeasure`。
形式化陈述：variation_withDensity' [CompleteSpace G] (hf : μ.Integrable f) (hB : foral
l x y, ‖B x y‖₊ = ‖B.flip y‖₊ * ‖x‖₊) : (μ.withDensity f B).variation = (μ.trans
pose B).variation.withDensity (fun x => ‖f x‖ₑ)
参数：hf : μ.Integrable f；hB : forall x y, ‖B x y‖₊ = ‖B.flip y‖₊ * ‖x‖₊。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用引理 `MeasureTheory.VectorMeasure.variation_WithDensity_le`：variation_WithDens
ity_le : (μ.withDensity f B).variation <= (μ.transpose B).variation.withDensity 
(fun x => ‖f x‖ₑ)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.le_iff`：le_iff : μ₁ <= μ₂ ↔ forall s, MeasurableSe
t s -> μ₁ s <= μ₂ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.withDensity_apply`：withDensity_apply (f : α -> Real>=0∞) {
s : Set α} (hs : MeasurableSet s) : μ.withDensity f s = ∫⁻ a in s, f a ∂μ
· 使用定理 `ENNReal.le_of_forall_pos_le_add`：le_of_forall_pos_le_add (h : forall ε :
 Real>=0, 0 < ε -> b < ∞ -> a <= b + ε) : a <= b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `Mathlib.Meta.NormNum.isNat_lt_true`：∀ {α : Type u_1} [inst : Semiring α]
 [inst_1 : PartialOrder α] [IsOrderedRing α] [CharZero α] {a b : α} {a' b' : ℕ},
   Mathlib.Meta.NormNum.…
· 使用定理 `NNReal.instIsOrderedRing_1`：IsOrderedRing NNReal
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instZeroLEOneClass`：∀ {α : Type u_2} [inst : Semiring α] [
inst_1 : PartialOrder α] [FloorSemiring α], ZeroLEOneClass α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
（共 183 条，此处仅展示前 30 条）

--- 原说明 ---
If `‖B x y‖ = ‖B · y‖ * ‖x‖` for all `x, y`, then the variation of a vector meas
ure with
density `f` wrt `μ` is the measure with density `‖f‖ₑ` with respect to the varia
tion of `μ`.

The condition on `B` is necessary: for a counterexample without it, let `B` be t
he scalar
product in `ℝ²` and `f x` everywhere horizontal and `μ s` everywhere vertical.
Then `μ.withDensity f B = 0` so its variation is zero, while the integral of `‖f
‖ₑ` is not.

See also `variation_withDensity` under the very common condition `‖B x y‖ = ‖x‖ 
‖y‖`.
-/
lemma variation_withDensity' [CompleteSpace G]
    (hf : μ.Integrable f) (hB : ∀ x y, ‖B x y‖₊ = ‖B.flip y‖₊ * ‖x‖₊) :
    (μ.withDensity f B).variation = (μ.transpose B).variation.withDensity (fun x ↦ ‖f x‖ₑ) := by
  apply le_antisymm variation_WithDensity_le
  apply Measure.le_iff.2 (fun s hs ↦ ?_)
  /- For the nontrivial direction, we have to show that for each measurable set `s`,
  `∫⁻ (a : X) in s, ‖f a‖ₑ ∂(μ.transpose B).variation ≤ (μ.withDensity f B).variation s`.
  As the variation is a supremum over finite partitions, we need to exhibit a partition. For this,
  we approximate `f` by a simple function `g`. Then the left term is approximately
  `∑ i, ‖g i‖ₑ * (μ.transpose B).variation (g ⁻¹' {i})` (where everything is intersected with `s`).
  By definition, the variation of `g ⁻¹' {i}` is close to a sum `∑ j, ‖(μ.transpose B) Pᵢⱼ‖ₑ` over
  a partition `Pᵢⱼ` of `g ⁻¹' {i}`. Putting all these together, one gets the desired
  partition of `s`, for which `∫⁻ a in s, ‖f a‖ₑ ∂(μ.transpose B).variation` is close to
  `∑ i j, ‖∫ x in Pᵢⱼ, f x ∂[B; μ]‖ₑ`, i.e., `∑ i j, ‖(μ.withDensity f B) Pᵢⱼ‖ₑ`. The latter sum
  is bounded by `(μ.withDensity f B).variation s` as desired. -/
  rw [MeasureTheory.withDensity_apply _ hs]
  apply ENNReal.le_of_forall_pos_le_add
  rintro ε εpos -
  let δ := ε / 3
  have δpos : 0 < δ := div_pos εpos (by norm_num)
  -- first step: approximate `f` by a simple function `g`.
  obtain ⟨g, hg, gmem⟩ : ∃ (g : X →ₛ E), eLpNorm (f - ⇑g) 1 (μ.transpose B).variation ≤ δ
      ∧ MemLp (⇑g) 1 μ.variation := by
    obtain ⟨ρ, ρpos, hδ⟩ : ∃ ρ > 0, ‖B‖₊ * ρ ≤ δ := by
      rcases eq_or_ne (‖B‖₊) 0 with hB | hB
      · exact ⟨1, zero_lt_one, by simp [hB]⟩
      · refine ⟨‖B‖₊ ⁻¹ * δ, by positivity, ?_⟩
        rw [← mul_assoc]
        apply mul_le_of_le_one_left (by positivity) mul_inv_le_one
    obtain ⟨g, h'g, gmem⟩ : ∃ (g : X →ₛ E), eLpNorm (f - ⇑g) 1 μ.variation < ρ
        ∧ MemLp (⇑g) 1 μ.variation :=
      (memLp_one_iff_integrable.2 hf).exists_simpleFunc_eLpNorm_sub_lt (by simp)
        (by simpa using ρpos.ne')
    refine ⟨g, ?_, gmem⟩
    grw [variation_transpose_le]
    rw [eLpNorm_smul_measure_of_ne_top' (by simp)]
    grw [h'g.le]
    simp only [ENNReal.toReal_one, inv_one, NNReal.rpow_one, ENNReal.smul_def, smul_eq_mul]
    exact_mod_cast hδ
  -- the integral of `‖f‖ₑ` is approximated up to `δ` by that of `‖g‖ₑ`.
  have I1 : ∫⁻ a in s, ‖f a‖ₑ ∂(μ.transpose B).variation
        ≤ ∫⁻ a in s, ‖g a‖ₑ ∂(μ.transpose B).variation + δ := calc
    _ ≤ ∫⁻ a in s, ‖f a - g a‖ₑ + ‖g a‖ₑ ∂(μ.transpose B).variation := by
      gcongr with a
      nth_rw 1 [show f a = (f a - g a) + g a by abel]
      exact enorm_add_le (f a - g a) (g a)
    _ = ∫⁻ a in s, ‖g a‖ₑ ∂(μ.transpose B).variation +
          ∫⁻ a in s, ‖f a - g a‖ₑ ∂(μ.transpose B).variation := by
      rw [lintegral_add_right, add_comm]
      exact g.stronglyMeasurable.enorm
    _ ≤ ∫⁻ a in s, ‖g a‖ₑ ∂(μ.transpose B).variation +
          ∫⁻ a, ‖f a - g a‖ₑ ∂(μ.transpose B).variation := by
      gcongr
      exact Measure.restrict_le_self
    _ ≤ ∫⁻ a in s, ‖g a‖ₑ ∂(μ.transpose B).variation + δ := by
      rw [eLpNorm_one_eq_lintegral_enorm] at hg
      gcongr
      exact hg
  -- the integral of `‖g‖ₑ` can be rewritten as a weighted sum of measures, as `g` is a simple
  -- function.
  have I2 : ∫⁻ a in s, ‖g a‖ₑ ∂(μ.transpose B).variation =
      ∑ i ∈ g.range, ‖i‖ₑ * ((μ.transpose B).restrict s).variation (g ⁻¹' {i}) := calc
    _ = (g.map (‖·‖ₑ)).lintegral ((μ.transpose B).variation.restrict s) :=
      SimpleFunc.lintegral_eq_lintegral _ _
    _ = ∑ i ∈ g.range, ‖i‖ₑ * (μ.transpose B).variation.restrict s (g ⁻¹' {i}) :=
      SimpleFunc.map_lintegral _ _
    _ = ∑ i ∈ g.range, ‖i‖ₑ * ((μ.transpose B).restrict s).variation (g ⁻¹' {i}) := by
      simp_rw [variation_restrict hs]
  -- For each `i`, choose a partition `P i` of `g ⁻¹' {i}` such that the sum of the enorms
  -- of their measures approximates well enough the variation, by definition of the variation.
  obtain ⟨ρ,ρpos, hρ⟩ : ∃ ρ > 0, ∑ i ∈ g.range, ‖i‖ₑ * ρ ≤ δ := by
    refine ⟨δ * (∑ i ∈ g.range, ‖i‖ₑ)⁻¹, by simp [δpos], ?_⟩
    grw [← Finset.sum_mul, mul_comm (δ : ℝ≥0∞), ← mul_assoc, ENNReal.mul_inv_le_one, one_mul]
  have C i : ∃ (P : Finset (Set X)), (∀ t ∈ P, t ⊆ g ⁻¹' {i})
      ∧ ((P : Set (Set X)).PairwiseDisjoint id) ∧
      (∀ t ∈ P, MeasurableSet t) ∧
      ‖i‖ₑ * ((μ.transpose B).restrict s).variation (g ⁻¹' {i}) ≤
        ‖i‖ₑ * (∑ p ∈ P, ‖(μ.transpose B).restrict s p‖ₑ + ρ) := by
    rcases eq_or_ne i 0 with rfl | hi
    · exact ⟨∅, by simp⟩
    suffices ∃ (P : Finset (Set X)), (∀ t ∈ P, t ⊆ g ⁻¹' {i})
        ∧ ((P : Set (Set X)).PairwiseDisjoint id) ∧ (∀ t ∈ P, MeasurableSet t) ∧
        ((μ.transpose B).restrict s).variation (g ⁻¹' {i}) ≤
        (∑ p ∈ P, ‖(μ.transpose B).restrict s p‖ₑ + ρ) by
      obtain ⟨P, hP, h'P, h''P, h'''P⟩ := this
      exact ⟨P, hP, h'P, h''P, by gcongr⟩
    apply exists_variation_le_add' _ (g.measurableSet_fiber i) ρpos
    rw [variation_restrict hs]
    have : MemLp (⇑g) 1 (μ.transpose B).variation :=
      gmem.of_measure_le_smul (c := ‖B‖₊) (by simp) (variation_transpose_le _ _)
    exact (g.integrable_iff.1 (memLp_one_iff_integrable.1 this).restrict i hi).ne
  choose P Pg Pdisj Pmeas hP using C
  -- rewrite everything in terms of the global partition made by putting together the `Pᵢ`,
  -- and register that the resulting error is bounded by `δ`.
  have I3 : ∑ i ∈ g.range, ‖i‖ₑ * ((μ.transpose B).restrict s).variation (g ⁻¹' {i}) ≤
      ∑ i ∈ g.range.sigma P, ‖i.1‖ₑ * ‖(μ.transpose B).restrict s i.2‖ₑ + δ := calc
    ∑ i ∈ g.range, ‖i‖ₑ * ((μ.transpose B).restrict s).variation (g ⁻¹' {i})
    _ ≤ ∑ i ∈ g.range, ‖i‖ₑ * ((∑ p ∈ P i, ‖(μ.transpose B).restrict s p‖ₑ) + ρ) := by
      gcongr 1 with i hi
      exact hP i
    _ ≤ ∑ i ∈ g.range, ∑ p ∈ P i, ‖i‖ₑ * ‖(μ.transpose B).restrict s p‖ₑ + δ := by
      simp_rw [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      gcongr
    _ = ∑ i ∈ g.range.sigma P, ‖i.1‖ₑ * ‖(μ.transpose B).restrict s i.2‖ₑ + δ := by
      rw [Finset.sum_sigma']
  -- in the above sum, replace the values of `g` by `f`, as these two functions are close
  -- in `L^1` norm.
  have I4 : ∑ i ∈ g.range.sigma P, ‖i.1‖ₑ * ‖(μ.transpose B).restrict s i.2‖ₑ
      ≤ ∑ i ∈ g.range.sigma P, ‖∫ᵛ x in i.2, f x ∂[B; μ.restrict s]‖ₑ + δ := calc
    ∑ i ∈ g.range.sigma P, ‖i.1‖ₑ * ‖(μ.transpose B).restrict s i.2‖ₑ
    _ = ∑ i ∈ g.range.sigma P, ‖∫ᵛ x in i.2, i.1 ∂[B; μ.restrict s]‖ₑ := by
      congr! with ⟨i, p⟩ hi
      rcases eq_or_ne i 0 with rfl | h'i
      · simp
      simp only [Finset.mem_sigma] at hi
      have pmeas : MeasurableSet p := Pmeas i _ hi.2
      have : IsFiniteMeasure ((μ.restrict s).variation.restrict p) := by
        constructor
        rw [variation_restrict hs, Measure.restrict_restrict pmeas,
          MeasureTheory.Measure.restrict_apply_univ]
        apply lt_of_le_of_lt ?_ (g.integrable_iff.1 (memLp_one_iff_integrable.1 gmem) i h'i)
        exact measure_mono (inter_subset_left.trans (Pg i _ hi.2))
      rw [setIntegral_const, restrict_apply _ hs pmeas, restrict_apply _ hs pmeas]
      simp [transpose, hB, enorm_eq_nnnorm, mul_comm]
    _ = ∑ i ∈ g.range.sigma P, ‖∫ᵛ x in i.2, g x ∂[B; μ.restrict s]‖ₑ := by
      congr! 2 with ⟨i, p⟩ hi
      simp only [Finset.mem_sigma] at hi
      apply setIntegral_congr_ae
      filter_upwards with x hx using (Pg i _ hi.2 hx).symm
    _ = ∑ i ∈ g.range.sigma P, ‖∫ᵛ x in i.2, (g x - f x) + f x ∂[B; μ.restrict s]‖ₑ := by simp
    _ = ∑ i ∈ g.range.sigma P, ‖∫ᵛ x in i.2, (g x - f x) ∂[B; μ.restrict s]
          + ∫ᵛ x in i.2, f x ∂[B; μ.restrict s]‖ₑ := by
      congr! with i hi
      rw [integral_fun_add]
      · apply Integrable.restrict
        apply Integrable.restrict
        apply Integrable.sub (memLp_one_iff_integrable.1 gmem) hf
      · apply hf.restrict.restrict
    _ ≤ ∑ i ∈ g.range.sigma P, ‖∫ᵛ x in i.2, (g x - f x) ∂[B; μ.restrict s]‖ₑ
        + ∑ i ∈ g.range.sigma P, ‖∫ᵛ x in i.2, f x ∂[B; μ.restrict s]‖ₑ := by
      rw [← Finset.sum_add_distrib]
      gcongr with i hi
      apply enorm_add_le
    _ ≤ ∑ i ∈ g.range.sigma P, ∫⁻ x in i.2, ‖g x - f x‖ₑ ∂(μ.transpose B).variation
        + ∑ i ∈ g.range.sigma P, ‖∫ᵛ x in i.2, f x ∂[B; μ.restrict s]‖ₑ := by
      gcongr with i hi
      grw [enorm_setIntegral_le_lintegral_enorm_transpose]
      apply lintegral_mono' _ le_rfl
      apply Measure.restrict_mono le_rfl
      rw [transpose_restrict, variation_restrict hs]
      apply Measure.restrict_le_self
    _ = ∫⁻ x in (⋃ i ∈ g.range.sigma P, i.2), ‖g x - f x‖ₑ ∂(μ.transpose B).variation
        + ∑ i ∈ g.range.sigma P, ‖∫ᵛ x in i.2, f x ∂[B; μ.restrict s]‖ₑ := by
      rw [lintegral_biUnion_finset]
      · rintro ⟨i, p⟩ hi ⟨j, q⟩ hj hijpq
        simp only [Finset.coe_sigma, SimpleFunc.coe_range, mem_sigma_iff, mem_range,
          SetLike.mem_coe] at hi hj
        rcases eq_or_ne i j with rfl | hij
        · simp only [ne_eq, Sigma.mk.injEq, heq_eq_eq, true_and] at hijpq
          exact Pdisj i hi.2 hj.2 hijpq
        · have : Disjoint (g ⁻¹' {i}) (g ⁻¹' {j}) := by grind
          exact this.mono (Pg i p hi.2) (Pg j q hj.2)
      · rintro ⟨i, p⟩ hip
        simp only [Finset.mem_sigma, SimpleFunc.mem_range, mem_range] at hip
        exact Pmeas i p hip.2
    _ ≤ ∑ i ∈ g.range.sigma P, ‖∫ᵛ x in i.2, f x ∂[B; μ.restrict s]‖ₑ +
        ∫⁻ x, ‖g x - f x‖ₑ ∂(μ.transpose B).variation := by
      rw [add_comm]
      gcongr
      apply Measure.restrict_le_self
    _ ≤ ∑ i ∈ g.range.sigma P, ‖∫ᵛ x in i.2, f x ∂[B; μ.restrict s]‖ₑ + δ := by
      gcongr
      simp_rw [enorm_sub_rev, ← eLpNorm_one_eq_lintegral_enorm]
      exact hg
  -- register that the sum of the enorms of the integrals of `f` over the pieces `Pᵢⱼ` of the
  -- partition is bounded by the variation of `μ.withDensity f B`, by definition of the variation.
  have I5 : ∑ i ∈ g.range.sigma P, ‖∫ᵛ x in i.2, f x ∂[B; μ.restrict s]‖ₑ
      ≤ (μ.withDensity f B).variation s := by
    let Q : Finset (Set X) := (g.range.sigma P).image (fun p ↦ p.2 ∩ s)
    calc ∑ i ∈ g.range.sigma P, ‖∫ᵛ x in i.2, f x ∂[B; μ.restrict s]‖ₑ
    _ = ∑ j ∈ Q, ‖∫ᵛ x in j, f x ∂[B; μ]‖ₑ := by
      simp only [Q]
      rw [Finset.sum_image_of_pairwise_eq_zero]; swap
      · rintro ⟨i, p⟩ hi ⟨j, q⟩ hj hijpq h'ij
        simp only [Finset.coe_sigma, SimpleFunc.coe_range, mem_sigma_iff, mem_range,
          SetLike.mem_coe] at hi hj
        suffices H : Disjoint p q by
          have : Disjoint (p ∩ s) (q ∩ s) := H.mono inter_subset_left inter_subset_left
          rw [← h'ij, disjoint_self] at this
          simp [this]
        rcases eq_or_ne i j with rfl | hij
        · simp only [ne_eq, Sigma.mk.injEq, heq_eq_eq, true_and] at hijpq
          exact Pdisj i hi.2 hj.2 hijpq
        · have : Disjoint (g ⁻¹' {i}) (g ⁻¹' {j}) := by grind
          exact this.mono (Pg i p hi.2) (Pg j q hj.2)
      apply Finset.sum_congr rfl
      rintro ⟨i, p⟩ hi
      simp only [Finset.mem_sigma, SimpleFunc.mem_range, mem_range] at hi
      rw [restrict_restrict _ (Pmeas i p hi.2) hs]
    _ = ∑ j ∈ Q, ‖μ.withDensity f B j‖ₑ :=
      Finset.sum_congr rfl (fun t ht ↦ by rw [withDensity_apply hf])
    _ ≤ (μ.withDensity f B).variation s := by
      apply le_variation _ hs
      · intro t ht
        simp only [Finset.mem_image, Finset.mem_sigma, SimpleFunc.mem_range, mem_range,
          Sigma.exists, ↓existsAndEq, true_and, exists_and_right, Q] at ht
        rcases ht with ⟨p, -, rfl⟩
        exact inter_subset_right
      · intro t ht u hu htu
        simp only [Finset.coe_image, Finset.coe_sigma, SimpleFunc.coe_range, mem_image,
          mem_sigma_iff, mem_range, SetLike.mem_coe, Sigma.exists, ↓existsAndEq, true_and,
          exists_and_right, Q] at ht hu
        rcases ht with ⟨p, ⟨i, hi⟩, rfl⟩
        rcases hu with ⟨q, ⟨j, hj⟩, rfl⟩
        have hpq : p ≠ q := by grind only
        suffices H : Disjoint p q from H.mono inter_subset_left inter_subset_left
        rcases eq_or_ne (g i) (g j) with hij | hij
        · rw [← hij] at hj
          exact Pdisj (g i) hi hj hpq
        · have : Disjoint (g ⁻¹' {g i}) (g ⁻¹' {g j}) := by grind
          exact this.mono (Pg (g i) p hi) (Pg (g j) q hj)
  -- finally, put together the above inequalities, and argue that the overall error `3δ` is
  -- bounded by `ε` by design.
  calc ∫⁻ (a : X) in s, ‖f a‖ₑ ∂(μ.transpose B).variation
  _ ≤ ∫⁻ a in s, ‖g a‖ₑ ∂(μ.transpose B).variation + δ := I1
  _ = ∑ i ∈ g.range, ‖i‖ₑ * ((μ.transpose B).restrict s).variation (g ⁻¹' {i}) + δ := by rw [I2]
  _ ≤ (∑ i ∈ g.range.sigma P, ‖i.1‖ₑ * ‖(μ.transpose B).restrict s i.2‖ₑ + δ) + δ := by gcongr
  _ ≤ ((∑ i ∈ g.range.sigma P, ‖∫ᵛ x in i.2, f x ∂[B; μ.restrict s]‖ₑ + δ) + δ) + δ := by gcongr
  _ = (∑ i ∈ g.range.sigma P, ‖∫ᵛ x in i.2, f x ∂[B; μ.restrict s]‖ₑ) + 3 * δ := by ring
  _ ≤ (μ.withDensity f B).variation s + 3 * δ := by gcongr
  _ ≤ (μ.withDensity f B).variation s + ε := by
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, ENNReal.coe_div, ENNReal.coe_ofNat, δ]
    rw [ENNReal.mul_div_cancel (by simp) (by simp)]

/-- If `‖B x y‖ = ‖x‖ * ‖y‖` for all `x, y`, then the variation of a vector measure with
density `f` wrt `μ` is the measure with density `‖f‖ₑ` with respect to the variation of `μ`.

The condition on `B` is necessary: for a counterexample without it, let `B` be the scalar
product in `ℝ²` and `f x` everywhere horizontal and `μ s` everywhere vertical.
Then `μ.withDensity f B = 0` so its variation is zero, while the integral of `‖f‖ₑ` is not.
-/
/-
**MeasureTheory.VectorMeasure.variation_withDensity** 是 Mathlib 中的一个引理，位于命名空间 `M
easureTheory.VectorMeasure`。
形式化陈述：variation_withDensity [CompleteSpace G] (hf : μ.Integrable f) (hB : forall
 x y, ‖B x y‖₊ = ‖x‖₊ * ‖y‖₊) : (μ.withDensity f B).variation = (μ.transpose B).
variation.withDensity (fun x => ‖f x‖ₑ)
参数：hf : μ.Integrable f；hB : forall x y, ‖B x y‖₊ = ‖x‖₊ * ‖y‖₊。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用引理 `MeasureTheory.VectorMeasure.variation_withDensity'`：variation_withDensit
y' [CompleteSpace G] (hf : μ.Integrable f) (hB : forall x y, ‖B x y‖₊ = ‖B.flip 
y‖₊ * ‖x‖₊) : (μ.withDensity f B).variat…
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `ContinuousLinearMap.le_opNorm`：le_opNorm : ‖f x‖ <= ‖f‖ * ‖x‖
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `ContinuousLinearMap.opNNNorm_le_bound`：opNNNorm_le_bound (f : E ->SL[σ₁₂
] F) (M : Real>=0) (hM : forall x, ‖f x‖₊ <= M * ‖x‖₊) : ‖f‖₊ <= M
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
If `‖B x y‖ = ‖x‖ * ‖y‖` for all `x, y`, then the variation of a vector measure 
with
density `f` wrt `μ` is the measure with density `‖f‖ₑ` with respect to the varia
tion of `μ`.

The condition on `B` is necessary: for a counterexample without it, let `B` be t
he scalar
product in `ℝ²` and `f x` everywhere horizontal and `μ s` everywhere vertical.
Then `μ.withDensity f B = 0` so its variation is zero, while the integral of `‖f
‖ₑ` is not.
-/
lemma variation_withDensity [CompleteSpace G]
    (hf : μ.Integrable f) (hB : ∀ x y, ‖B x y‖₊ = ‖x‖₊ * ‖y‖₊) :
    (μ.withDensity f B).variation = (μ.transpose B).variation.withDensity (fun x ↦ ‖f x‖ₑ) := by
  apply variation_withDensity' hf (fun x y ↦ ?_)
  refine le_antisymm (ContinuousLinearMap.le_opNorm (B.flip y) x) ?_
  rw [hB, mul_comm]
  gcongr
  apply ContinuousLinearMap.opNNNorm_le_bound
  simp [hB, mul_comm]

/-- The variation of a vecture measure with density `f` with respect to a positive measure `μ`
is the measure with density `‖f‖ₑ` with respect to `μ`. -/
/-
**MeasureTheory.VectorMeasure._root_.MeasureTheory.Measure.variation_withDensity
** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.VectorMeasure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The variation of a vecture measure with density `f` with respect to a positive m
easure `μ`
is the measure with density `‖f‖ₑ` with respect to `μ`.
-/
lemma _root_.MeasureTheory.Measure.variation_withDensityᵥ [CompleteSpace E]
    {μ : Measure X} {f : X → E} (hf : Integrable f μ) :
    (μ.withDensityᵥ f).variation = μ.withDensity (fun x ↦ ‖f x‖ₑ) := by
  /- We deduce this statement from the statement `variation_withDensity` for vector measures
  with density. For this, we write `μ.withDensityᵥ f` as the vector measure with density `f / ‖f‖`
  with respect to the measure `μ.withDensity ‖f‖` interpreted as a signed measure. -/
  rcases subsingleton_or_nontrivial E with hE | hE
  · simp [show f = 0 from Subsingleton.elim _ _]
  have : IsFiniteMeasure (μ.withDensity fun x ↦ ‖f x‖ₑ) := ⟨by simpa using! hf.2⟩
  have I : (μ.withDensity fun x ↦ ‖f x‖ₑ).toSignedMeasure.Integrable (fun x ↦ ‖f x‖⁻¹ • f x) := by
    simp only [VectorMeasure.Integrable, Measure.variation_toSignedMeasure]
    apply Integrable.of_bound (C := 1)
    · apply AEStronglyMeasurable.mono_ac (withDensity_absolutelyContinuous _ _)
      exact hf.aestronglyMeasurable.norm.inv₀.smul hf.aestronglyMeasurable
    · filter_upwards with x using by simp [norm_smul, inv_mul_le_one]
  have : μ.withDensityᵥ f = (μ.withDensity (‖f ·‖ₑ)).toSignedMeasure.withDensity
      (fun x ↦ ‖f x‖⁻¹ • f x) (ContinuousLinearMap.lsmul ℝ ℝ).flip := by
    ext s hs
    rw [withDensityᵥ_apply hf hs, withDensity_apply I, setIntegral_toSignedMeasure hs,
        setIntegral_withDensity_eq_setIntegral_toReal_smul₀ _ _ _ hs]; rotate_left
    · exact hf.aestronglyMeasurable.restrict.enorm
    · filter_upwards with x using by simp
    congr with x
    rcases eq_or_ne (f x) 0 with hx | hx
    · simp [hx]
    simp only [toReal_enorm, smul_smul]
    rw [mul_inv_cancel₀, one_smul]
    simpa using hx
  rw [this, variation_withDensity I (by simp [nnnorm_smul, mul_comm]),
    variation_transpose_eq _ _ (by simp [nnnorm_smul, mul_comm]), Measure.variation_toSignedMeasure,
    ← withDensity_mul₀ hf.aestronglyMeasurable.enorm]; swap
  · exact (hf.aestronglyMeasurable.norm.inv₀.smul hf.aestronglyMeasurable).enorm
  congr with x
  rcases eq_or_ne (f x) 0 with hx | hx
  · simp [hx]
  have h'x : ‖f x‖ ≠ 0 := by simp [hx]
  simp only [enorm_smul, Pi.mul_apply, ne_eq, h'x, not_false_eq_true, enorm_inv, enorm_norm]
  rw [ENNReal.inv_mul_cancel (by simpa using hx) (by simp), mul_one]

end MeasureTheory.VectorMeasure

