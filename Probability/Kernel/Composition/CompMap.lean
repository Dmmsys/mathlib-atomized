/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Composition.Comp
public import Mathlib.Probability.Kernel.Composition.MapComap

/-!
# Lemmas about compositions and maps of kernels

This file contains results that use both the composition of kernels and the map of a kernel by a
function.

Map and comap are particular cases of composition: they correspond to composition with
a deterministic kernel. See `deterministic_comp_eq_map` and `comp_deterministic_eq_comap`.

-/

public section


open MeasureTheory

open scoped ENNReal

namespace ProbabilityTheory

namespace Kernel

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}


variable {γ δ : Type*} {mγ : MeasurableSpace γ} {mδ : MeasurableSpace δ} {f : β → γ} {g : γ → α}

/-
**ProbabilityTheory.Kernel.deterministic_comp_eq_map** 是 Mathlib 中的一个定理，位于命名空间 `
ProbabilityTheory.Kernel`。
形式化陈述：deterministic_comp_eq_map (hf : Measurable f) (κ : Kernel α β) : determini
stic f hf ∘ₖ κ = map κ f
参数：hf : Measurable f；κ : Kernel α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.map_apply'`：map_apply' (κ : Kernel α β) (hf : M
easurable f) (a : α) {s : Set γ} (hs : MeasurableSet s) : map κ f a s = κ a (f ⁻
¹' s)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ProbabilityTheory.Kernel.comp_apply'`：comp_apply' (η : Kernel β γ) (κ : 
Kernel α β) (a : α) {s : Set γ} (hs : MeasurableSet s) : (η ∘ₖ κ) a s = ∫⁻ b, η 
b s ∂κ a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ProbabilityTheory.Kernel.deterministic_apply'`：deterministic_apply' {f :
 α -> β} (hf : Measurable f) (a : α) {s : Set β} (hs : MeasurableSet s) : determ
inistic f hf a s = s.indicator (fun…
· 使用定理 `MeasureTheory.lintegral_indicator_const_comp`：lintegral_indicator_const_
comp {f : α -> β} {s : Set β} (hf : Measurable f) (hs : MeasurableSet s) (c : Re
al>=0∞) : ∫⁻ a, s.indicator (fun _…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem deterministic_comp_eq_map (hf : Measurable f) (κ : Kernel α β) :
    deterministic f hf ∘ₖ κ = map κ f := by
  ext a s hs
  simp_rw [map_apply' _ hf _ hs, comp_apply' _ _ _ hs, deterministic_apply' hf _ hs,
    lintegral_indicator_const_comp hf hs, one_mul]
/-
**ProbabilityTheory.Kernel.comp_deterministic_eq_comap** 是 Mathlib 中的一个定理，位于命名空间
 `ProbabilityTheory.Kernel`。
形式化陈述：comp_deterministic_eq_comap (κ : Kernel α β) (hg : Measurable g) : κ ∘ₖ de
terministic g hg = comap κ g hg
参数：κ : Kernel α β；hg : Measurable g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.comap_apply'`：comap_apply' (κ : Kernel α β) (hg
 : Measurable g) (c : γ) (s : Set β) : comap κ g hg c s = κ (g c) s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ProbabilityTheory.Kernel.comp_apply'`：comp_apply' (η : Kernel β γ) (κ : 
Kernel α β) (a : α) {s : Set γ} (hs : MeasurableSet s) : (η ∘ₖ κ) a s = ∫⁻ b, η 
b s ∂κ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.lintegral_dirac'`：lintegral_dirac' (a : α) {f : α -> Real>
=0∞} (hf : Measurable f) : ∫⁻ a, f a ∂dirac a = f a
· 使用定理 `ProbabilityTheory.Kernel.measurable_coe`：∀ {α : Type u_1} {β : Type u_2}
 {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (κ : ProbabilityTheory.Kernel
 α β)   {s : Set β}, Measurab…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comp_deterministic_eq_comap (κ : Kernel α β) (hg : Measurable g) :
    κ ∘ₖ deterministic g hg = comap κ g hg := by
  ext a s hs
  simp_rw [comap_apply' _ _ _ s, comp_apply' _ _ _ hs, deterministic_apply hg a,
    lintegral_dirac' _ (Kernel.measurable_coe κ hs)]
/-
**ProbabilityTheory.Kernel.deterministic_comp_deterministic** 是 Mathlib 中的一个引理，位
于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：deterministic_comp_deterministic (hf : Measurable f) (hg : Measurable g) :
 (deterministic g hg) ∘ₖ (deterministic f hf) = deterministic (g ∘ f) (hg.comp h
f)
参数：hf : Measurable f；hg : Measurable g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.comp_deterministic_eq_comap`：comp_deterministic
_eq_comap (κ : Kernel α β) (hg : Measurable g) : κ ∘ₖ deterministic g hg = comap
 κ g hg
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma deterministic_comp_deterministic (hf : Measurable f) (hg : Measurable g) :
    (deterministic g hg) ∘ₖ (deterministic f hf) = deterministic (g ∘ f) (hg.comp hf) := by
  ext; simp [comp_deterministic_eq_comap, comap_apply, deterministic_apply]

@[simp]
/-
**ProbabilityTheory.Kernel.swap_swap** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheor
y.Kernel`。
形式化陈述：swap_swap : (swap α β) ∘ₖ (swap β α) = Kernel.id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_swap`：measurable_swap : Measurable (Prod.swap : α × β -> β × 
α)
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.Kernel.deterministic_comp_deterministic`：deterministic
_comp_deterministic (hf : Measurable f) (hg : Measurable g) : (deterministic g h
g) ∘ₖ (deterministic f hf) = deterministic (g ∘…
· 使用定理 `Prod.swap_swap_eq`：∀ {α : Type u_1} {β : Type u_2}, Prod.swap ∘ Prod.swa
p = id
· 使用定理 `ProbabilityTheory.Kernel.deterministic.congr_simp`：∀ {α : Type u_1} {β :
 Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (f f_1 : α → β) (e_
f : f = f_1)   (hf : Measurable f), Pro…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma swap_swap : (swap α β) ∘ₖ (swap β α) = Kernel.id := by
  simp_rw [swap, Kernel.deterministic_comp_deterministic, Prod.swap_swap_eq, Kernel.id]
/-
**ProbabilityTheory.Kernel.swap_comp_eq_map** 是 Mathlib 中的一个引理，位于命名空间 `Probabili
tyTheory.Kernel`。
形式化陈述：swap_comp_eq_map {κ : Kernel α (β × γ)} : (swap β γ) ∘ₖ κ = κ.map Prod.swa
p
参数：β × γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_swap`：measurable_swap : Measurable (Prod.swap : α × β -> β × 
α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.swap.eq_1`：∀ (α : Type u_4) (β : Type u_5) [ins
t : MeasurableSpace α] [inst_1 : MeasurableSpace β],   ProbabilityTheory.Kernel.
swap α β = ProbabilityTh…
· 使用定理 `ProbabilityTheory.Kernel.deterministic_comp_eq_map`：deterministic_comp_e
q_map (hf : Measurable f) (κ : Kernel α β) : deterministic f hf ∘ₖ κ = map κ f
-/
lemma swap_comp_eq_map {κ : Kernel α (β × γ)} : (swap β γ) ∘ₖ κ = κ.map Prod.swap := by
  rw [swap, deterministic_comp_eq_map]
/-
**ProbabilityTheory.Kernel.map_comp** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory
.Kernel`。
形式化陈述：map_comp (κ : Kernel α β) (η : Kernel β γ) (f : γ -> δ) : (η ∘ₖ κ).map f =
 (η.map f) ∘ₖ κ
参数：κ : Kernel α β；η : Kernel β γ；f : γ -> δ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.map_apply'`：map_apply' (κ : Kernel α β) (hf : M
easurable f) (a : α) {s : Set γ} (hs : MeasurableSet s) : map κ f a s = κ a (f ⁻
¹' s)
· 使用定理 `ProbabilityTheory.Kernel.comp_apply'`：comp_apply' (η : Kernel β γ) (κ : 
Kernel α β) (a : α) {s : Set γ} (hs : MeasurableSet s) : (η ∘ₖ κ) a s = ∫⁻ b, η 
b s ∂κ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ProbabilityTheory.Kernel.map_of_not_measurable`：map_of_not_measurable (κ
 : Kernel α β) {f : β -> γ} (hf : ¬(Measurable f)) : map κ f = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ProbabilityTheory.Kernel.zero_comp`：∀ {α : Type u_1} {β : Type u_2} {γ :
 Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {mγ : MeasurableS
pace γ} (κ : Probability…
-/
lemma map_comp (κ : Kernel α β) (η : Kernel β γ) (f : γ → δ) :
    (η ∘ₖ κ).map f = (η.map f) ∘ₖ κ := by
  by_cases hf : Measurable f
  · ext a s hs
    rw [map_apply' _ hf _ hs, comp_apply', comp_apply' _ _ _ hs]
    · simp_rw [map_apply' _ hf _ hs]
    · exact hf hs
  · simp [map_of_not_measurable _ hf]
/-
**ProbabilityTheory.Kernel.comp_map** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory
.Kernel`。
形式化陈述：comp_map (κ : Kernel α β) (η : Kernel γ δ) {f : β -> γ} (hf : Measurable f
) : η ∘ₖ (κ.map f) = (η.comap f hf) ∘ₖ κ
参数：κ : Kernel α β；η : Kernel γ δ；hf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.comp_apply'`：comp_apply' (η : Kernel β γ) (κ : 
Kernel α β) (a : α) {s : Set γ} (hs : MeasurableSet s) : (η ∘ₖ κ) a s = ∫⁻ b, η 
b s ∂κ a
· 使用定理 `ProbabilityTheory.Kernel.lintegral_map`：∀ {α : Type u_1} {β : Type u_2} 
{mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ : Measura
bleSpace γ} {f : β → γ} (κ :…
· 使用定理 `ProbabilityTheory.Kernel.measurable_coe`：∀ {α : Type u_1} {β : Type u_2}
 {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (κ : ProbabilityTheory.Kernel
 α β)   {s : Set β}, Measurab…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comp_map (κ : Kernel α β) (η : Kernel γ δ) {f : β → γ} (hf : Measurable f) :
    η ∘ₖ (κ.map f) = (η.comap f hf) ∘ₖ κ := by
  ext x s ms
  rw [comp_apply' _ _ _ ms, lintegral_map _ hf _ (η.measurable_coe ms), comp_apply' _ _ _ ms]
  simp_rw [comap_apply']
/-
**ProbabilityTheory.Kernel.fst_comp** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory
.Kernel`。
形式化陈述：fst_comp (κ : Kernel α β) (η : Kernel β (γ × δ)) : (η ∘ₖ κ).fst = η.fst ∘ₖ
 κ
参数：κ : Kernel α β；η : Kernel β (γ × δ)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.fst_eq`：fst_eq (κ : Kernel α (β × γ)) : fst κ =
 map κ Prod.fst
· 使用引理 `ProbabilityTheory.Kernel.map_comp`：map_comp (κ : Kernel α β) (η : Kernel
 β γ) (f : γ -> δ) : (η ∘ₖ κ).map f = (η.map f) ∘ₖ κ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma fst_comp (κ : Kernel α β) (η : Kernel β (γ × δ)) : (η ∘ₖ κ).fst = η.fst ∘ₖ κ := by
  simp [fst_eq, map_comp κ η _]
/-
**ProbabilityTheory.Kernel.snd_comp** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory
.Kernel`。
形式化陈述：snd_comp (κ : Kernel α β) (η : Kernel β (γ × δ)) : (η ∘ₖ κ).snd = η.snd ∘ₖ
 κ
参数：κ : Kernel α β；η : Kernel β (γ × δ)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.snd_eq`：snd_eq (κ : Kernel α (β × γ)) : snd κ =
 map κ Prod.snd
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `ProbabilityTheory.Kernel.map_comp`：map_comp (κ : Kernel α β) (η : Kernel
 β γ) (f : γ -> δ) : (η ∘ₖ κ).map f = (η.map f) ∘ₖ κ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma snd_comp (κ : Kernel α β) (η : Kernel β (γ × δ)) : (η ∘ₖ κ).snd = η.snd ∘ₖ κ := by
  simp_rw [snd_eq, map_comp κ η _]

end Kernel
end ProbabilityTheory

