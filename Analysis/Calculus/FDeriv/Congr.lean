/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# The Fréchet derivative: congruence properties

Lemmas about congruence properties of the Fréchet derivative under change of function, set, etc.

## Tags

derivative, differentiable, Fréchet, calculus

-/

public section

open Filter Asymptotics ContinuousLinearMap Set Metric Topology NNReal ENNReal

noncomputable section

section
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
variable {F : Type*} [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]

variable {f f₀ f₁ g : E → F}
variable {f' f₀' f₁' g' : E →L[𝕜] F}
variable {x : E}
variable {s t : Set E}
variable {L : Filter (E × E)}

section congr

/-! ### congr properties of the derivative -/

/-
**hasFDerivWithinAt_congr_set_nhdsNE** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivWithinAt_congr_set_nhdsNE (h : s =ᶠ[𝓝[!=] x] t) : HasFDerivWithin
At f f' s x ↔ HasFDerivWithinAt f f' t x
参数：h : s =ᶠ[𝓝[!=] x] t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `hasFDerivWithinAt_sdiff_singleton_self`：hasFDerivWithinAt_sdiff_singleto
n_self : HasFDerivWithinAt f f' (s \ {x}) x ↔ HasFDerivWithinAt f f' s x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sdiff_eq`：sdiff_eq (s t : Set α) : s \ t = s inter tᶜ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
### congr properties of the derivative
-/
theorem hasFDerivWithinAt_congr_set_nhdsNE (h : s =ᶠ[𝓝[≠] x] t) :
    HasFDerivWithinAt f f' s x ↔ HasFDerivWithinAt f f' t x :=
  calc
    HasFDerivWithinAt f f' s x ↔ HasFDerivWithinAt f f' (s \ {x}) x :=
      hasFDerivWithinAt_sdiff_singleton_self.symm
    _ ↔ HasFDerivWithinAt f f' (t \ {x}) x := by
      suffices 𝓝[s \ {x}] x = 𝓝[t \ {x}] x by simp only [HasFDerivWithinAt, this]
      simpa only [set_eventuallyEq_iff_inf_principal, ← nhdsWithin_inter', sdiff_eq, inter_comm]
        using h
    _ ↔ HasFDerivWithinAt f f' t x := hasFDerivWithinAt_sdiff_singleton_self
/-
**hasFDerivWithinAt_congr_set** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivWithinAt_congr_set (h : s =ᶠ[𝓝 x] t) : HasFDerivWithinAt f f' s x
 ↔ HasFDerivWithinAt f f' t x
参数：h : s =ᶠ[𝓝 x] t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivWithinAt_congr_set_nhdsNE`：hasFDerivWithinAt_congr_set_nhdsNE (
h : s =ᶠ[𝓝[!=] x] t) : HasFDerivWithinAt f f' s x ↔ HasFDerivWithinAt f f' t x
· 使用定理 `Filter.EventuallyEq.filter_mono`：∀ {α : Type u} {β : Type v} {l l' : Fil
ter α} {f g : α → β}, f =ᶠ[l] g → l' ≤ l → f =ᶠ[l'] g
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
-/
theorem hasFDerivWithinAt_congr_set (h : s =ᶠ[𝓝 x] t) :
    HasFDerivWithinAt f f' s x ↔ HasFDerivWithinAt f f' t x :=
  hasFDerivWithinAt_congr_set_nhdsNE <| h.filter_mono inf_le_left

/-- In the case `y = x`, see also `hasFDerivWithinAt_congr_set_nhdsNE`,
which does not require the domain to be a T₁ space. -/
/-
**hasFDerivWithinAt_congr_set'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivWithinAt_congr_set' [T1Space E] (y : E) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
 HasFDerivWithinAt f f' s x ↔ HasFDerivWithinAt f f' t x
参数：y : E；h : s =ᶠ[𝓝[{y}ᶜ] x] t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `hasFDerivWithinAt_congr_set_nhdsNE`：hasFDerivWithinAt_congr_set_nhdsNE (
h : s =ᶠ[𝓝[!=] x] t) : HasFDerivWithinAt f f' s x ↔ HasFDerivWithinAt f f' t x
· 使用定理 `hasFDerivWithinAt_congr_set`：hasFDerivWithinAt_congr_set (h : s =ᶠ[𝓝 x] 
t) : HasFDerivWithinAt f f' s x ↔ HasFDerivWithinAt f f' t x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ne.nhdsWithin_compl_singleton`：Ne.nhdsWithin_compl_singleton [T1Space X]
 {x y : X} (h : x != y) : 𝓝[{y}ᶜ] x = 𝓝 x

--- 原说明 ---
In the case `y = x`, see also `hasFDerivWithinAt_congr_set_nhdsNE`,
which does not require the domain to be a T₁ space.
-/
theorem hasFDerivWithinAt_congr_set' [T1Space E] (y : E)
    (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    HasFDerivWithinAt f f' s x ↔ HasFDerivWithinAt f f' t x := by
  rcases eq_or_ne x y with rfl | hne
  · exact hasFDerivWithinAt_congr_set_nhdsNE h
  · rw [hne.nhdsWithin_compl_singleton] at h
    exact hasFDerivWithinAt_congr_set h
/-
**differentiableWithinAt_congr_set_nhdsNE** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableWithinAt_congr_set_nhdsNE (h : s =ᶠ[𝓝[!=] x] t) : Differenti
ableWithinAt 𝕜 f s x ↔ DifferentiableWithinAt 𝕜 f t x
参数：h : s =ᶠ[𝓝[!=] x] t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `hasFDerivWithinAt_congr_set_nhdsNE`：hasFDerivWithinAt_congr_set_nhdsNE (
h : s =ᶠ[𝓝[!=] x] t) : HasFDerivWithinAt f f' s x ↔ HasFDerivWithinAt f f' t x
-/
theorem differentiableWithinAt_congr_set_nhdsNE (h : s =ᶠ[𝓝[≠] x] t) :
    DifferentiableWithinAt 𝕜 f s x ↔ DifferentiableWithinAt 𝕜 f t x :=
  exists_congr fun _ => hasFDerivWithinAt_congr_set_nhdsNE h

/-- In the case `y = x`, see also `differentiableWithinAt_congr_set_nhdsNE`,
which does not require the domain to be a T₁ space. -/
/-
**differentiableWithinAt_congr_set'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableWithinAt_congr_set' [T1Space E] (y : E) (h : s =ᶠ[𝓝[{y}ᶜ] x]
 t) : DifferentiableWithinAt 𝕜 f s x ↔ DifferentiableWithinAt 𝕜 f t x
参数：y : E；h : s =ᶠ[𝓝[{y}ᶜ] x] t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `hasFDerivWithinAt_congr_set'`：hasFDerivWithinAt_congr_set' [T1Space E] (
y : E) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) : HasFDerivWithinAt f f' s x ↔ HasFDerivWithinAt 
f f' t x

--- 原说明 ---
In the case `y = x`, see also `differentiableWithinAt_congr_set_nhdsNE`,
which does not require the domain to be a T₁ space.
-/
theorem differentiableWithinAt_congr_set' [T1Space E] (y : E) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    DifferentiableWithinAt 𝕜 f s x ↔ DifferentiableWithinAt 𝕜 f t x :=
  exists_congr fun _ => hasFDerivWithinAt_congr_set' _ h
/-
**differentiableWithinAt_congr_set** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableWithinAt_congr_set (h : s =ᶠ[𝓝 x] t) : DifferentiableWithinA
t 𝕜 f s x ↔ DifferentiableWithinAt 𝕜 f t x
参数：h : s =ᶠ[𝓝 x] t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `hasFDerivWithinAt_congr_set`：hasFDerivWithinAt_congr_set (h : s =ᶠ[𝓝 x] 
t) : HasFDerivWithinAt f f' s x ↔ HasFDerivWithinAt f f' t x
-/
theorem differentiableWithinAt_congr_set (h : s =ᶠ[𝓝 x] t) :
    DifferentiableWithinAt 𝕜 f s x ↔ DifferentiableWithinAt 𝕜 f t x :=
  exists_congr fun _ => hasFDerivWithinAt_congr_set h
/-
**fderivWithin_congr_set_nhdsNE** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_congr_set_nhdsNE (h : s =ᶠ[𝓝[!=] x] t) : fderivWithin 𝕜 f s x
 = fderivWithin 𝕜 f t x
参数：h : s =ᶠ[𝓝[!=] x] t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `differentiableWithinAt_congr_set_nhdsNE`：differentiableWithinAt_congr_se
t_nhdsNE (h : s =ᶠ[𝓝[!=] x] t) : DifferentiableWithinAt 𝕜 f s x ↔ Differentiable
WithinAt 𝕜 f t x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `hasFDerivWithinAt_congr_set_nhdsNE`：hasFDerivWithinAt_congr_set_nhdsNE (
h : s =ᶠ[𝓝[!=] x] t) : HasFDerivWithinAt f f' s x ↔ HasFDerivWithinAt f f' t x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fderivWithin_def`：∀ (𝕜 : Type u_4) [inst : NontriviallyNormedField 𝕜] {E
 : Type u_5} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 : 
Topolo…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `Classical.choose.congr_simp`：∀ {α : Sort u} {p p_1 : α → Prop} (e_p : p 
= p_1) (h : ∃ x, p x), Classical.choose h = Classical.choose ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fderivWithin_congr_set_nhdsNE (h : s =ᶠ[𝓝[≠] x] t) :
    fderivWithin 𝕜 f s x = fderivWithin 𝕜 f t x := by
  classical
  simp only [fderivWithin, differentiableWithinAt_congr_set_nhdsNE h,
    hasFDerivWithinAt_congr_set_nhdsNE h]

/-- In the case `y = x`, see also `fderivWithin_congr_set_nhdsNE`,
which does not require the domain to be a T₁ space. -/
/-
**fderivWithin_congr_set'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_congr_set' [T1Space E] (y : E) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) : fder
ivWithin 𝕜 f s x = fderivWithin 𝕜 f t x
参数：y : E；h : s =ᶠ[𝓝[{y}ᶜ] x] t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `differentiableWithinAt_congr_set'`：differentiableWithinAt_congr_set' [T1
Space E] (y : E) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) : DifferentiableWithinAt 𝕜 f s x ↔ Diff
erentiableWithinAt 𝕜 f …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `hasFDerivWithinAt_congr_set'`：hasFDerivWithinAt_congr_set' [T1Space E] (
y : E) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) : HasFDerivWithinAt f f' s x ↔ HasFDerivWithinAt 
f f' t x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fderivWithin_def`：∀ (𝕜 : Type u_4) [inst : NontriviallyNormedField 𝕜] {E
 : Type u_5} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 : 
Topolo…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `Classical.choose.congr_simp`：∀ {α : Sort u} {p p_1 : α → Prop} (e_p : p 
= p_1) (h : ∃ x, p x), Classical.choose h = Classical.choose ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
In the case `y = x`, see also `fderivWithin_congr_set_nhdsNE`,
which does not require the domain to be a T₁ space.
-/
theorem fderivWithin_congr_set' [T1Space E] (y : E) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    fderivWithin 𝕜 f s x = fderivWithin 𝕜 f t x := by
  classical
  simp only [fderivWithin, differentiableWithinAt_congr_set' _ h, hasFDerivWithinAt_congr_set' _ h]
/-
**fderivWithin_congr_set** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_congr_set (h : s =ᶠ[𝓝 x] t) : fderivWithin 𝕜 f s x = fderivWi
thin 𝕜 f t x
参数：h : s =ᶠ[𝓝 x] t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fderivWithin_congr_set_nhdsNE`：fderivWithin_congr_set_nhdsNE (h : s =ᶠ[𝓝
[!=] x] t) : fderivWithin 𝕜 f s x = fderivWithin 𝕜 f t x
· 使用定理 `Filter.EventuallyEq.filter_mono`：∀ {α : Type u} {β : Type v} {l l' : Fil
ter α} {f g : α → β}, f =ᶠ[l] g → l' ≤ l → f =ᶠ[l'] g
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
-/
theorem fderivWithin_congr_set (h : s =ᶠ[𝓝 x] t) : fderivWithin 𝕜 f s x = fderivWithin 𝕜 f t x :=
  fderivWithin_congr_set_nhdsNE <| h.filter_mono inf_le_left
/-
**fderivWithin_eventually_congr_set'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_eventually_congr_set' [T1Space E] (y : E) (h : s =ᶠ[𝓝[{y}ᶜ] x
] t) : fderivWithin 𝕜 f s =ᶠ[𝓝 x] fderivWithin 𝕜 f t
参数：y : E；h : s =ᶠ[𝓝[{y}ᶜ] x] t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eventually_nhds_nhdsWithin`：eventually_nhds_nhdsWithin {a : α} {s : Set 
α} {p : α -> Prop} : (forallᶠ y in 𝓝 a, forallᶠ x in 𝓝[s] y, p x) ↔ forallᶠ x in
 𝓝[s] a, p x
· 使用定理 `fderivWithin_congr_set'`：fderivWithin_congr_set' [T1Space E] (y : E) (h 
: s =ᶠ[𝓝[{y}ᶜ] x] t) : fderivWithin 𝕜 f s x = fderivWithin 𝕜 f t x
-/
theorem fderivWithin_eventually_congr_set' [T1Space E] (y : E) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    fderivWithin 𝕜 f s =ᶠ[𝓝 x] fderivWithin 𝕜 f t :=
  (eventually_nhds_nhdsWithin.2 h).mono fun _ => fderivWithin_congr_set' y
/-
**fderivWithin_eventually_congr_set** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_eventually_congr_set (h : s =ᶠ[𝓝 x] t) : fderivWithin 𝕜 f s =
ᶠ[𝓝 x] fderivWithin 𝕜 f t
参数：h : s =ᶠ[𝓝 x] t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eventually_eventually_nhds`：eventually_eventually_nhds {p : X -> Prop} :
 (forallᶠ y in 𝓝 x, forallᶠ x in 𝓝 y, p x) ↔ forallᶠ x in 𝓝 x, p x
· 使用定理 `fderivWithin_congr_set`：fderivWithin_congr_set (h : s =ᶠ[𝓝 x] t) : fderi
vWithin 𝕜 f s x = fderivWithin 𝕜 f t x
-/
theorem fderivWithin_eventually_congr_set (h : s =ᶠ[𝓝 x] t) :
    fderivWithin 𝕜 f s =ᶠ[𝓝 x] fderivWithin 𝕜 f t :=
  (eventually_eventually_nhds.2 h).mono fun _ => fderivWithin_congr_set
/-
**Filter.EventuallyEq.hasFDerivAtFilter_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.hasFDerivAtFilter_iff (h₀ : Prod.map f₀ f₀ =ᶠ[L] Prod.
map f₁ f₁) (h₁ : forall x, f₀' x = f₁' x) : HasFDerivAtFilter f₀ f₀' L ↔ HasFDer
ivAtFilter f₁ f₁' L
参数：h₀ : Prod.map f₀ f₀ =ᶠ[L] Prod.map f₁ f₁；h₁ : forall x, f₀' x = f₁' x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Asymptotics.isLittleOTVS_congr`：isLittleOTVS_congr (hf : f₁ =ᶠ[l] f₂) (h
g : g₁ =ᶠ[l] g₂) : f₁ =o[𝕜; l] g₁ ↔ f₂ =o[𝕜; l] g₂
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.EventuallyEq.rfl`：∀ {α : Type u} {β : Type v} {l : Filter α} {f :
 α → β}, f =ᶠ[l] f
-/
theorem Filter.EventuallyEq.hasFDerivAtFilter_iff (h₀ : Prod.map f₀ f₀ =ᶠ[L] Prod.map f₁ f₁)
    (h₁ : ∀ x, f₀' x = f₁' x) : HasFDerivAtFilter f₀ f₀' L ↔ HasFDerivAtFilter f₁ f₁' L := by
  simp only [hasFDerivAtFilter_iff_isLittleOTVS]
  exact isLittleOTVS_congr (h₀.mono fun y hy => by simp_all [Prod.map]) .rfl
/-
**Filter.EventuallyEq.hasStrictFDerivAt_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.hasStrictFDerivAt_iff (h : f₀ =ᶠ[𝓝 x] f₁) (h' : forall
 y, f₀' y = f₁' y) : HasStrictFDerivAt f₀ f₀' x ↔ HasStrictFDerivAt f₁ f₁' x
参数：h : f₀ =ᶠ[𝓝 x] f₁；h' : forall y, f₀' y = f₁' y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.hasFDerivAtFilter_iff`：Filter.EventuallyEq.hasFDeriv
AtFilter_iff (h₀ : Prod.map f₀ f₀ =ᶠ[L] Prod.map f₁ f₁) (h₁ : forall x, f₀' x = 
f₁' x) : HasFDerivAtFilter f₀ f…
· 使用定理 `Filter.EventuallyEq.prodMap_nhds`：Filter.EventuallyEq.prodMap_nhds {α β 
: Type*} {f₁ f₂ : X -> α} {g₁ g₂ : Y -> β} {x : X} {y : Y} (hf : f₁ =ᶠ[𝓝 x] f₂) 
(hg : g₁ =ᶠ[𝓝 y] g₂) :…
-/
theorem Filter.EventuallyEq.hasStrictFDerivAt_iff (h : f₀ =ᶠ[𝓝 x] f₁) (h' : ∀ y, f₀' y = f₁' y) :
    HasStrictFDerivAt f₀ f₀' x ↔ HasStrictFDerivAt f₁ f₁' x :=
  h.prodMap_nhds h |>.hasFDerivAtFilter_iff h'
/-
**HasStrictFDerivAt.congr_fderiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictFDerivAt.congr_fderiv (h : HasStrictFDerivAt f f' x) (h' : f' = g
') : HasStrictFDerivAt f g' x
参数：h : HasStrictFDerivAt f f' x；h' : f' = g'。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem HasStrictFDerivAt.congr_fderiv (h : HasStrictFDerivAt f f' x) (h' : f' = g') :
    HasStrictFDerivAt f g' x :=
  h' ▸ h
/-
**HasFDerivAt.congr_fderiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.congr_fderiv (h : HasFDerivAt f f' x) (h' : f' = g') : HasFDer
ivAt f g' x
参数：h : HasFDerivAt f f' x；h' : f' = g'。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem HasFDerivAt.congr_fderiv (h : HasFDerivAt f f' x) (h' : f' = g') : HasFDerivAt f g' x :=
  h' ▸ h
/-
**HasFDerivWithinAt.congr_fderiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.congr_fderiv (h : HasFDerivWithinAt f f' s x) (h' : f' =
 g') : HasFDerivWithinAt f g' s x
参数：h : HasFDerivWithinAt f f' s x；h' : f' = g'。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem HasFDerivWithinAt.congr_fderiv (h : HasFDerivWithinAt f f' s x) (h' : f' = g') :
    HasFDerivWithinAt f g' s x :=
  h' ▸ h
/-
**HasStrictFDerivAt.congr_of_eventuallyEq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictFDerivAt.congr_of_eventuallyEq (h : HasStrictFDerivAt f f' x) (h₁
 : f =ᶠ[𝓝 x] f₁) : HasStrictFDerivAt f₁ f' x
参数：h : HasStrictFDerivAt f f' x；h₁ : f =ᶠ[𝓝 x] f₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.EventuallyEq.hasStrictFDerivAt_iff`：Filter.EventuallyEq.hasStrict
FDerivAt_iff (h : f₀ =ᶠ[𝓝 x] f₁) (h' : forall y, f₀' y = f₁' y) : HasStrictFDeri
vAt f₀ f₀' x ↔ HasStrictFDerivA…
-/
theorem HasStrictFDerivAt.congr_of_eventuallyEq (h : HasStrictFDerivAt f f' x)
    (h₁ : f =ᶠ[𝓝 x] f₁) : HasStrictFDerivAt f₁ f' x :=
  (h₁.hasStrictFDerivAt_iff fun _ => rfl).1 h
/-
**HasFDerivAtFilter.congr_of_eventuallyEq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAtFilter.congr_of_eventuallyEq (h : HasFDerivAtFilter f f' L) (hL
 : Prod.map f₁ f₁ =ᶠ[L] Prod.map f f) : HasFDerivAtFilter f₁ f' L
参数：h : HasFDerivAtFilter f f' L；hL : Prod.map f₁ f₁ =ᶠ[L] Prod.map f f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.EventuallyEq.hasFDerivAtFilter_iff`：Filter.EventuallyEq.hasFDeriv
AtFilter_iff (h₀ : Prod.map f₀ f₀ =ᶠ[L] Prod.map f₁ f₁) (h₁ : forall x, f₀' x = 
f₁' x) : HasFDerivAtFilter f₀ f…
-/
theorem HasFDerivAtFilter.congr_of_eventuallyEq (h : HasFDerivAtFilter f f' L)
    (hL : Prod.map f₁ f₁ =ᶠ[L] Prod.map f f) :
    HasFDerivAtFilter f₁ f' L :=
  (hL.hasFDerivAtFilter_iff fun _ => rfl).2 h
/-
**Filter.EventuallyEq.hasFDerivAt_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.hasFDerivAt_iff (h : f₀ =ᶠ[𝓝 x] f₁) : HasFDerivAt f₀ f
' x ↔ HasFDerivAt f₁ f' x
参数：h : f₀ =ᶠ[𝓝 x] f₁。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.hasFDerivAtFilter_iff`：Filter.EventuallyEq.hasFDeriv
AtFilter_iff (h₀ : Prod.map f₀ f₀ =ᶠ[L] Prod.map f₁ f₁) (h₁ : forall x, f₀' x = 
f₁' x) : HasFDerivAtFilter f₀ f…
· 使用定理 `Filter.EventuallyEq.prodMap`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u
_3} {δ : Type u_6} {la : Filter α} {fa ga : α → γ},   fa =ᶠ[la] ga → ∀ {lb : Fil
ter β} {fb gb : β…
· 使用定理 `Filter.EventuallyEq.filter_mono`：∀ {α : Type u} {β : Type v} {l l' : Fil
ter α} {f g : α → β}, f =ᶠ[l] g → l' ≤ l → f =ᶠ[l'] g
· 使用定理 `pure_le_nhds`：pure_le_nhds : pure <= (𝓝 : X -> Filter X)
-/
theorem Filter.EventuallyEq.hasFDerivAt_iff (h : f₀ =ᶠ[𝓝 x] f₁) :
    HasFDerivAt f₀ f' x ↔ HasFDerivAt f₁ f' x :=
  h.prodMap (h.filter_mono <| pure_le_nhds _) |>.hasFDerivAtFilter_iff fun _ => rfl
/-
**Filter.EventuallyEq.differentiableAt_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.differentiableAt_iff (h : f₀ =ᶠ[𝓝 x] f₁) : Differentia
bleAt 𝕜 f₀ x ↔ DifferentiableAt 𝕜 f₁ x
参数：h : f₀ =ᶠ[𝓝 x] f₁。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `Filter.EventuallyEq.hasFDerivAt_iff`：Filter.EventuallyEq.hasFDerivAt_iff
 (h : f₀ =ᶠ[𝓝 x] f₁) : HasFDerivAt f₀ f' x ↔ HasFDerivAt f₁ f' x
-/
theorem Filter.EventuallyEq.differentiableAt_iff (h : f₀ =ᶠ[𝓝 x] f₁) :
    DifferentiableAt 𝕜 f₀ x ↔ DifferentiableAt 𝕜 f₁ x :=
  exists_congr fun _ => h.hasFDerivAt_iff
/-
**Filter.EventuallyEq.hasFDerivWithinAt_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.hasFDerivWithinAt_iff (h : f₀ =ᶠ[𝓝[s] x] f₁) (hx : f₀ 
x = f₁ x) : HasFDerivWithinAt f₀ f' s x ↔ HasFDerivWithinAt f₁ f' s x
参数：h : f₀ =ᶠ[𝓝[s] x] f₁；hx : f₀ x = f₁ x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.hasFDerivAtFilter_iff`：Filter.EventuallyEq.hasFDeriv
AtFilter_iff (h₀ : Prod.map f₀ f₀ =ᶠ[L] Prod.map f₁ f₁) (h₁ : forall x, f₀' x = 
f₁' x) : HasFDerivAtFilter f₀ f…
· 使用定理 `Filter.EventuallyEq.prodMap`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u
_3} {δ : Type u_6} {la : Filter α} {fa ga : α → γ},   fa =ᶠ[la] ga → ∀ {lb : Fil
ter β} {fb gb : β…
-/
theorem Filter.EventuallyEq.hasFDerivWithinAt_iff (h : f₀ =ᶠ[𝓝[s] x] f₁) (hx : f₀ x = f₁ x) :
    HasFDerivWithinAt f₀ f' s x ↔ HasFDerivWithinAt f₁ f' s x :=
  h.prodMap (by assumption) |>.hasFDerivAtFilter_iff fun _ => _root_.rfl
/-
**Filter.EventuallyEq.hasFDerivWithinAt_iff_of_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.hasFDerivWithinAt_iff_of_mem (h : f₀ =ᶠ[𝓝[s] x] f₁) (h
x : x in s) : HasFDerivWithinAt f₀ f' s x ↔ HasFDerivWithinAt f₁ f' s x
参数：h : f₀ =ᶠ[𝓝[s] x] f₁；hx : x in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.hasFDerivWithinAt_iff`：Filter.EventuallyEq.hasFDeriv
WithinAt_iff (h : f₀ =ᶠ[𝓝[s] x] f₁) (hx : f₀ x = f₁ x) : HasFDerivWithinAt f₀ f'
 s x ↔ HasFDerivWithinAt f₁ f' …
· 使用定理 `Filter.EventuallyEq.eq_of_nhdsWithin`：Filter.EventuallyEq.eq_of_nhdsWith
in {s : Set α} {f g : α -> β} {a : α} (h : f =ᶠ[𝓝[s] a] g) (hmem : a in s) : f a
 = g a
-/
theorem Filter.EventuallyEq.hasFDerivWithinAt_iff_of_mem (h : f₀ =ᶠ[𝓝[s] x] f₁) (hx : x ∈ s) :
    HasFDerivWithinAt f₀ f' s x ↔ HasFDerivWithinAt f₁ f' s x :=
  h.hasFDerivWithinAt_iff (h.eq_of_nhdsWithin hx)
/-
**Filter.EventuallyEq.differentiableWithinAt_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.differentiableWithinAt_iff (h : f₀ =ᶠ[𝓝[s] x] f₁) (hx 
: f₀ x = f₁ x) : DifferentiableWithinAt 𝕜 f₀ s x ↔ DifferentiableWithinAt 𝕜 f₁ s
 x
参数：h : f₀ =ᶠ[𝓝[s] x] f₁；hx : f₀ x = f₁ x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `Filter.EventuallyEq.hasFDerivWithinAt_iff`：Filter.EventuallyEq.hasFDeriv
WithinAt_iff (h : f₀ =ᶠ[𝓝[s] x] f₁) (hx : f₀ x = f₁ x) : HasFDerivWithinAt f₀ f'
 s x ↔ HasFDerivWithinAt f₁ f' …
-/
theorem Filter.EventuallyEq.differentiableWithinAt_iff (h : f₀ =ᶠ[𝓝[s] x] f₁) (hx : f₀ x = f₁ x) :
    DifferentiableWithinAt 𝕜 f₀ s x ↔ DifferentiableWithinAt 𝕜 f₁ s x :=
  exists_congr fun _ => h.hasFDerivWithinAt_iff hx
/-
**Filter.EventuallyEq.differentiableWithinAt_iff_of_mem** 是 Mathlib 中的一个定理，位于命名空
间 ``。
形式化陈述：Filter.EventuallyEq.differentiableWithinAt_iff_of_mem (h : f₀ =ᶠ[𝓝[s] x] f
₁) (hx : x in s) : DifferentiableWithinAt 𝕜 f₀ s x ↔ DifferentiableWithinAt 𝕜 f₁
 s x
参数：h : f₀ =ᶠ[𝓝[s] x] f₁；hx : x in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.differentiableWithinAt_iff`：Filter.EventuallyEq.diff
erentiableWithinAt_iff (h : f₀ =ᶠ[𝓝[s] x] f₁) (hx : f₀ x = f₁ x) : Differentiabl
eWithinAt 𝕜 f₀ s x ↔ DifferentiableW…
· 使用定理 `Filter.EventuallyEq.eq_of_nhdsWithin`：Filter.EventuallyEq.eq_of_nhdsWith
in {s : Set α} {f g : α -> β} {a : α} (h : f =ᶠ[𝓝[s] a] g) (hmem : a in s) : f a
 = g a
-/
theorem Filter.EventuallyEq.differentiableWithinAt_iff_of_mem (h : f₀ =ᶠ[𝓝[s] x] f₁) (hx : x ∈ s) :
    DifferentiableWithinAt 𝕜 f₀ s x ↔ DifferentiableWithinAt 𝕜 f₁ s x :=
  h.differentiableWithinAt_iff (h.eq_of_nhdsWithin hx)
/-
**HasFDerivWithinAt.congr_of_eventuallyEq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.congr_of_eventuallyEq (h : HasFDerivWithinAt f f' s x) (
h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : HasFDerivWithinAt f₁ f' s x
参数：h : HasFDerivWithinAt f f' s x；h₁ : f₁ =ᶠ[𝓝[s] x] f；hx : f₁ x = f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.EventuallyEq.hasFDerivWithinAt_iff`：Filter.EventuallyEq.hasFDeriv
WithinAt_iff (h : f₀ =ᶠ[𝓝[s] x] f₁) (hx : f₀ x = f₁ x) : HasFDerivWithinAt f₀ f'
 s x ↔ HasFDerivWithinAt f₁ f' …
-/
theorem HasFDerivWithinAt.congr_of_eventuallyEq (h : HasFDerivWithinAt f f' s x)
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : HasFDerivWithinAt f₁ f' s x :=
  h₁.hasFDerivWithinAt_iff hx |>.mpr h
/-
**HasFDerivWithinAt.congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.congr (h : HasFDerivWithinAt f f' s x) (hs : EqOn f₁ f s
) (hx : f₁ x = f x) : HasFDerivWithinAt f₁ f' s x
参数：h : HasFDerivWithinAt f f' s x；hs : EqOn f₁ f s；hx : f₁ x = f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.congr_of_eventuallyEq`：HasFDerivWithinAt.congr_of_even
tuallyEq (h : HasFDerivWithinAt f f' s x) (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f 
x) : HasFDerivWithinAt f₁ f' …
· 使用定理 `Set.EqOn.eventuallyEq_nhdsWithin`：Set.EqOn.eventuallyEq_nhdsWithin {f g 
: α -> β} {s : Set α} {a : α} (h : EqOn f g s) : f =ᶠ[𝓝[s] a] g
-/
theorem HasFDerivWithinAt.congr (h : HasFDerivWithinAt f f' s x) (hs : EqOn f₁ f s)
    (hx : f₁ x = f x) : HasFDerivWithinAt f₁ f' s x :=
  h.congr_of_eventuallyEq hs.eventuallyEq_nhdsWithin hx
/-
**HasFDerivWithinAt.congr'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.congr' (h : HasFDerivWithinAt f f' s x) (hs : EqOn f₁ f 
s) (hx : x in s) : HasFDerivWithinAt f₁ f' s x
参数：h : HasFDerivWithinAt f f' s x；hs : EqOn f₁ f s；hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.congr`：HasFDerivWithinAt.congr (h : HasFDerivWithinAt 
f f' s x) (hs : EqOn f₁ f s) (hx : f₁ x = f x) : HasFDerivWithinAt f₁ f' s x
-/
theorem HasFDerivWithinAt.congr' (h : HasFDerivWithinAt f f' s x) (hs : EqOn f₁ f s) (hx : x ∈ s) :
    HasFDerivWithinAt f₁ f' s x :=
  h.congr hs (hs hx)
/-
**HasFDerivWithinAt.congr_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.congr_mono (h : HasFDerivWithinAt f f' s x) (ht : EqOn f
₁ f t) (hx : f₁ x = f x) (h₁ : t subseteq s) : HasFDerivWithinAt f₁ f' t x
参数：h : HasFDerivWithinAt f f' s x；ht : EqOn f₁ f t；hx : f₁ x = f x；h₁ : t subset
eq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.congr`：HasFDerivWithinAt.congr (h : HasFDerivWithinAt 
f f' s x) (hs : EqOn f₁ f s) (hx : f₁ x = f x) : HasFDerivWithinAt f₁ f' s x
· 使用定理 `HasFDerivWithinAt.mono`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [ins
t_3 : Topolo…
-/
theorem HasFDerivWithinAt.congr_mono (h : HasFDerivWithinAt f f' s x) (ht : EqOn f₁ f t)
    (hx : f₁ x = f x) (h₁ : t ⊆ s) : HasFDerivWithinAt f₁ f' t x :=
  h.mono h₁ |>.congr ht hx
/-
**HasFDerivAt.congr_of_eventuallyEq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.congr_of_eventuallyEq (h : HasFDerivAt f f' x) (h₁ : f₁ =ᶠ[𝓝 x
] f) : HasFDerivAt f₁ f' x
参数：h : HasFDerivAt f f' x；h₁ : f₁ =ᶠ[𝓝 x] f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.EventuallyEq.hasFDerivAt_iff`：Filter.EventuallyEq.hasFDerivAt_iff
 (h : f₀ =ᶠ[𝓝 x] f₁) : HasFDerivAt f₀ f' x ↔ HasFDerivAt f₁ f' x
-/
theorem HasFDerivAt.congr_of_eventuallyEq (h : HasFDerivAt f f' x) (h₁ : f₁ =ᶠ[𝓝 x] f) :
    HasFDerivAt f₁ f' x :=
  h₁.hasFDerivAt_iff.mpr h
/-
**DifferentiableWithinAt.congr_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.congr_mono (h : DifferentiableWithinAt 𝕜 f s x) (ht
 : EqOn f₁ f t) (hx : f₁ x = f x) (h₁ : t subseteq s) : DifferentiableWithinAt 𝕜
 f₁ t x
参数：h : DifferentiableWithinAt 𝕜 f s x；ht : EqOn f₁ f t；hx : f₁ x = f x；h₁ : t su
bseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.differentiableWithinAt`：HasFDerivWithinAt.differentiab
leWithinAt (h : HasFDerivWithinAt f f' s x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `HasFDerivWithinAt.congr_mono`：HasFDerivWithinAt.congr_mono (h : HasFDeri
vWithinAt f f' s x) (ht : EqOn f₁ f t) (hx : f₁ x = f x) (h₁ : t subseteq s) : H
asFDerivWithinAt f…
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem DifferentiableWithinAt.congr_mono (h : DifferentiableWithinAt 𝕜 f s x) (ht : EqOn f₁ f t)
    (hx : f₁ x = f x) (h₁ : t ⊆ s) : DifferentiableWithinAt 𝕜 f₁ t x :=
  (HasFDerivWithinAt.congr_mono h.hasFDerivWithinAt ht hx h₁).differentiableWithinAt
/-
**DifferentiableWithinAt.congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.congr (h : DifferentiableWithinAt 𝕜 f s x) (ht : fo
rall x in s, f₁ x = f x) (hx : f₁ x = f x) : DifferentiableWithinAt 𝕜 f₁ s x
参数：h : DifferentiableWithinAt 𝕜 f s x；ht : forall x in s, f₁ x = f x；hx : f₁ x =
 f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.congr_mono`：DifferentiableWithinAt.congr_mono (h 
: DifferentiableWithinAt 𝕜 f s x) (ht : EqOn f₁ f t) (hx : f₁ x = f x) (h₁ : t s
ubseteq s) : Differenti…
· 使用定理 `Set.Subset.refl`：∀ {α : Type u} (a : Set α), a ⊆ a
-/
theorem DifferentiableWithinAt.congr (h : DifferentiableWithinAt 𝕜 f s x) (ht : ∀ x ∈ s, f₁ x = f x)
    (hx : f₁ x = f x) : DifferentiableWithinAt 𝕜 f₁ s x :=
  DifferentiableWithinAt.congr_mono h ht hx (Subset.refl _)
/-
**DifferentiableWithinAt.congr_of_eventuallyEq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.congr_of_eventuallyEq (h : DifferentiableWithinAt 𝕜
 f s x) (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : DifferentiableWithinAt 𝕜 f₁ s
 x
参数：h : DifferentiableWithinAt 𝕜 f s x；h₁ : f₁ =ᶠ[𝓝[s] x] f；hx : f₁ x = f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.differentiableWithinAt`：HasFDerivWithinAt.differentiab
leWithinAt (h : HasFDerivWithinAt f f' s x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `HasFDerivWithinAt.congr_of_eventuallyEq`：HasFDerivWithinAt.congr_of_even
tuallyEq (h : HasFDerivWithinAt f f' s x) (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f 
x) : HasFDerivWithinAt f₁ f' …
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem DifferentiableWithinAt.congr_of_eventuallyEq (h : DifferentiableWithinAt 𝕜 f s x)
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : DifferentiableWithinAt 𝕜 f₁ s x :=
  (h.hasFDerivWithinAt.congr_of_eventuallyEq h₁ hx).differentiableWithinAt
/-
**DifferentiableWithinAt.congr_of_eventuallyEq_of_mem** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：DifferentiableWithinAt.congr_of_eventuallyEq_of_mem (h : DifferentiableWit
hinAt 𝕜 f s x) (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : x in s) : DifferentiableWithinAt 𝕜 f
₁ s x
参数：h : DifferentiableWithinAt 𝕜 f s x；h₁ : f₁ =ᶠ[𝓝[s] x] f；hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.congr_of_eventuallyEq`：DifferentiableWithinAt.con
gr_of_eventuallyEq (h : DifferentiableWithinAt 𝕜 f s x) (h₁ : f₁ =ᶠ[𝓝[s] x] f) (
hx : f₁ x = f x) : DifferentiableW…
· 使用定理 `mem_of_mem_nhdsWithin`：mem_of_mem_nhdsWithin {a : α} {s t : Set α} (ha :
 a in s) (ht : t in 𝓝[s] a) : a in t
-/
theorem DifferentiableWithinAt.congr_of_eventuallyEq_of_mem (h : DifferentiableWithinAt 𝕜 f s x)
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : x ∈ s) : DifferentiableWithinAt 𝕜 f₁ s x :=
  h.congr_of_eventuallyEq h₁ (mem_of_mem_nhdsWithin hx h₁ :)
/-
**DifferentiableWithinAt.congr_of_eventuallyEq_insert** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：DifferentiableWithinAt.congr_of_eventuallyEq_insert (h : DifferentiableWit
hinAt 𝕜 f s x) (h₁ : f₁ =ᶠ[𝓝[insert x s] x] f) : DifferentiableWithinAt 𝕜 f₁ s x
参数：h : DifferentiableWithinAt 𝕜 f s x；h₁ : f₁ =ᶠ[𝓝[insert x s] x] f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.of_insert`：DifferentiableWithinAt.of_insert {y : 
E} (h : DifferentiableWithinAt 𝕜 f (insert y s) x) : DifferentiableWithinAt 𝕜 f 
s x
· 使用定理 `DifferentiableWithinAt.congr_of_eventuallyEq_of_mem`：DifferentiableWithi
nAt.congr_of_eventuallyEq_of_mem (h : DifferentiableWithinAt 𝕜 f s x) (h₁ : f₁ =
ᶠ[𝓝[s] x] f) (hx : x in s) : Differentiab…
· 使用定理 `DifferentiableWithinAt.insert`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 
E] [inst_3 : Topolo…
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
-/
theorem DifferentiableWithinAt.congr_of_eventuallyEq_insert (h : DifferentiableWithinAt 𝕜 f s x)
    (h₁ : f₁ =ᶠ[𝓝[insert x s] x] f) : DifferentiableWithinAt 𝕜 f₁ s x :=
  (h.insert.congr_of_eventuallyEq_of_mem h₁ (mem_insert _ _)).of_insert
/-
**DifferentiableOn.congr_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableOn.congr_mono (h : DifferentiableOn 𝕜 f s) (h' : forall x in
 t, f₁ x = f x) (h₁ : t subseteq s) : DifferentiableOn 𝕜 f₁ t
参数：h : DifferentiableOn 𝕜 f s；h' : forall x in t, f₁ x = f x；h₁ : t subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.congr_mono`：DifferentiableWithinAt.congr_mono (h 
: DifferentiableWithinAt 𝕜 f s x) (ht : EqOn f₁ f t) (hx : f₁ x = f x) (h₁ : t s
ubseteq s) : Differenti…
-/
theorem DifferentiableOn.congr_mono (h : DifferentiableOn 𝕜 f s) (h' : ∀ x ∈ t, f₁ x = f x)
    (h₁ : t ⊆ s) : DifferentiableOn 𝕜 f₁ t := fun x hx => (h x (h₁ hx)).congr_mono h' (h' x hx) h₁
/-
**DifferentiableOn.congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableOn.congr (h : DifferentiableOn 𝕜 f s) (h' : forall x in s, f
₁ x = f x) : DifferentiableOn 𝕜 f₁ s
参数：h : DifferentiableOn 𝕜 f s；h' : forall x in s, f₁ x = f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.congr`：DifferentiableWithinAt.congr (h : Differen
tiableWithinAt 𝕜 f s x) (ht : forall x in s, f₁ x = f x) (hx : f₁ x = f x) : Dif
ferentiableWithinA…
-/
theorem DifferentiableOn.congr (h : DifferentiableOn 𝕜 f s) (h' : ∀ x ∈ s, f₁ x = f x) :
    DifferentiableOn 𝕜 f₁ s := fun x hx => (h x hx).congr h' (h' x hx)
/-
**differentiableOn_congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableOn_congr (h' : forall x in s, f₁ x = f x) : DifferentiableOn
 𝕜 f₁ s ↔ DifferentiableOn 𝕜 f s
参数：h' : forall x in s, f₁ x = f x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableOn.congr`：DifferentiableOn.congr (h : DifferentiableOn 𝕜 f
 s) (h' : forall x in s, f₁ x = f x) : DifferentiableOn 𝕜 f₁ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem differentiableOn_congr (h' : ∀ x ∈ s, f₁ x = f x) :
    DifferentiableOn 𝕜 f₁ s ↔ DifferentiableOn 𝕜 f s :=
  ⟨fun h => DifferentiableOn.congr h fun y hy => (h' y hy).symm, fun h =>
    DifferentiableOn.congr h h'⟩
/-
**DifferentiableAt.congr_of_eventuallyEq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.congr_of_eventuallyEq (h : DifferentiableAt 𝕜 f x) (hL : 
f₁ =ᶠ[𝓝 x] f) : DifferentiableAt 𝕜 f₁ x
参数：h : DifferentiableAt 𝕜 f x；hL : f₁ =ᶠ[𝓝 x] f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.EventuallyEq.differentiableAt_iff`：Filter.EventuallyEq.differenti
ableAt_iff (h : f₀ =ᶠ[𝓝 x] f₁) : DifferentiableAt 𝕜 f₀ x ↔ DifferentiableAt 𝕜 f₁
 x
-/
theorem DifferentiableAt.congr_of_eventuallyEq (h : DifferentiableAt 𝕜 f x) (hL : f₁ =ᶠ[𝓝 x] f) :
    DifferentiableAt 𝕜 f₁ x :=
  hL.differentiableAt_iff.2 h
/-
**DifferentiableWithinAt.fderivWithin_congr_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.fderivWithin_congr_mono [ContinuousAdd E] [Continuo
usSMul 𝕜 E] [ContinuousAdd F] [ContinuousSMul 𝕜 F] [T2Space F] (h : Differentiab
leWithinAt 𝕜 f s x) (hs : EqOn f₁ f t) (hx : f₁ x = f x) (hxt : UniqueDiffWithin
At 𝕜 t x) (h₁ : t subseteq s) : fderivWithin 𝕜 f₁ t x = fderivWithin 𝕜 f s x
参数：h : DifferentiableWithinAt 𝕜 f s x；hs : EqOn f₁ f t；hx : f₁ x = f x；hxt : Uni
queDiffWithinAt 𝕜 t x；h₁ : t subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.fderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜
 E] [inst_3 : Topolo…
· 使用定理 `HasFDerivWithinAt.congr_mono`：HasFDerivWithinAt.congr_mono (h : HasFDeri
vWithinAt f f' s x) (ht : EqOn f₁ f t) (hx : f₁ x = f x) (h₁ : t subseteq s) : H
asFDerivWithinAt f…
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem DifferentiableWithinAt.fderivWithin_congr_mono
    [ContinuousAdd E] [ContinuousSMul 𝕜 E] [ContinuousAdd F] [ContinuousSMul 𝕜 F] [T2Space F]
    (h : DifferentiableWithinAt 𝕜 f s x)
    (hs : EqOn f₁ f t) (hx : f₁ x = f x) (hxt : UniqueDiffWithinAt 𝕜 t x) (h₁ : t ⊆ s) :
    fderivWithin 𝕜 f₁ t x = fderivWithin 𝕜 f s x :=
  (HasFDerivWithinAt.congr_mono h.hasFDerivWithinAt hs hx h₁).fderivWithin hxt

set_option backward.isDefEq.respectTransparency false in
/-
**Filter.EventuallyEq.fderivWithin_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.fderivWithin_eq (hs : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f 
x) : fderivWithin 𝕜 f₁ s x = fderivWithin 𝕜 f s x
参数：hs : f₁ =ᶠ[𝓝[s] x] f；hx : f₁ x = f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.EventuallyEq.hasFDerivWithinAt_iff`：Filter.EventuallyEq.hasFDeriv
WithinAt_iff (h : f₀ =ᶠ[𝓝[s] x] f₁) (hx : f₀ x = f₁ x) : HasFDerivWithinAt f₀ f'
 s x ↔ HasFDerivWithinAt f₁ f' …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `fderivWithin_def`：∀ (𝕜 : Type u_4) [inst : NontriviallyNormedField 𝕜] {E
 : Type u_5} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 : 
Topolo…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `Classical.choose.congr_simp`：∀ {α : Sort u} {p p_1 : α → Prop} (e_p : p 
= p_1) (h : ∃ x, p x), Classical.choose h = Classical.choose ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Filter.EventuallyEq.fderivWithin_eq (hs : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) :
    fderivWithin 𝕜 f₁ s x = fderivWithin 𝕜 f s x := by
  classical
  simp only [fderivWithin, DifferentiableWithinAt, hs.hasFDerivWithinAt_iff hx]
/-
**Filter.EventuallyEq.fderivWithin_eq_of_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.fderivWithin_eq_of_mem (hs : f₁ =ᶠ[𝓝[s] x] f) (hx : x 
in s) : fderivWithin 𝕜 f₁ s x = fderivWithin 𝕜 f s x
参数：hs : f₁ =ᶠ[𝓝[s] x] f；hx : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.fderivWithin_eq`：Filter.EventuallyEq.fderivWithin_eq
 (hs : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : fderivWithin 𝕜 f₁ s x = fderivWithin
 𝕜 f s x
· 使用定理 `mem_of_mem_nhdsWithin`：mem_of_mem_nhdsWithin {a : α} {s t : Set α} (ha :
 a in s) (ht : t in 𝓝[s] a) : a in t
-/
theorem Filter.EventuallyEq.fderivWithin_eq_of_mem (hs : f₁ =ᶠ[𝓝[s] x] f) (hx : x ∈ s) :
    fderivWithin 𝕜 f₁ s x = fderivWithin 𝕜 f s x :=
  hs.fderivWithin_eq (mem_of_mem_nhdsWithin hx hs :)
/-
**Filter.EventuallyEq.fderivWithin_eq_of_insert** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.fderivWithin_eq_of_insert (hs : f₁ =ᶠ[𝓝[insert x s] x]
 f) : fderivWithin 𝕜 f₁ s x = fderivWithin 𝕜 f s x
参数：hs : f₁ =ᶠ[𝓝[insert x s] x] f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.fderivWithin_eq`：Filter.EventuallyEq.fderivWithin_eq
 (hs : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : fderivWithin 𝕜 f₁ s x = fderivWithin
 𝕜 f s x
· 使用定理 `nhdsWithin_mono`：nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t
) : 𝓝[s] x <= 𝓝[t] x
· 使用定理 `Set.subset_insert`：subset_insert (x : α) (s : Set α) : s subseteq insert
 x s
· 使用定理 `mem_of_mem_nhdsWithin`：mem_of_mem_nhdsWithin {a : α} {s t : Set α} (ha :
 a in s) (ht : t in 𝓝[s] a) : a in t
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
-/
theorem Filter.EventuallyEq.fderivWithin_eq_of_insert (hs : f₁ =ᶠ[𝓝[insert x s] x] f) :
    fderivWithin 𝕜 f₁ s x = fderivWithin 𝕜 f s x := by
  apply Filter.EventuallyEq.fderivWithin_eq (nhdsWithin_mono _ (subset_insert x s) hs)
  exact (mem_of_mem_nhdsWithin (mem_insert x s) hs :)
/-
**Filter.EventuallyEq.fderivWithin'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.fderivWithin' (hs : f₁ =ᶠ[𝓝[s] x] f) (ht : t subseteq 
s) : fderivWithin 𝕜 f₁ t =ᶠ[𝓝[s] x] fderivWithin 𝕜 f t
参数：hs : f₁ =ᶠ[𝓝[s] x] f；ht : t subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∀ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eventually_eventually_nhdsWithin`：eventually_eventually_nhdsWithin {a : 
α} {s : Set α} {p : α -> Prop} : (forallᶠ y in 𝓝[s] a, forallᶠ x in 𝓝[s] y, p x)
 ↔ forallᶠ x in 𝓝[s] a…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `eventually_mem_nhdsWithin`：eventually_mem_nhdsWithin {a : α} {s : Set α}
 : forallᶠ x in 𝓝[s] a, x in s
· 使用定理 `Filter.EventuallyEq.fderivWithin_eq`：Filter.EventuallyEq.fderivWithin_eq
 (hs : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : fderivWithin 𝕜 f₁ s x = fderivWithin
 𝕜 f s x
· 使用定理 `Filter.Eventually.filter_mono`：∀ {α : Type u} {f₁ f₂ : Filter α}, f₁ ≤ f
₂ → ∀ {p : α → Prop}, (∀ᶠ (x : α) in f₂, p x) → ∀ᶠ (x : α) in f₁, p x
· 使用定理 `nhdsWithin_mono`：nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t
) : 𝓝[s] x <= 𝓝[t] x
· 使用定理 `Filter.Eventually.self_of_nhdsWithin`：Filter.Eventually.self_of_nhdsWith
in {p : α -> Prop} {s : Set α} {x : α} (h : forallᶠ y in 𝓝[s] x, p y) (hx : x in
 s) : p x
-/
theorem Filter.EventuallyEq.fderivWithin' (hs : f₁ =ᶠ[𝓝[s] x] f) (ht : t ⊆ s) :
    fderivWithin 𝕜 f₁ t =ᶠ[𝓝[s] x] fderivWithin 𝕜 f t :=
  (eventually_eventually_nhdsWithin.2 hs).mp <|
    eventually_mem_nhdsWithin.mono fun _y hys hs =>
      EventuallyEq.fderivWithin_eq (hs.filter_mono <| nhdsWithin_mono _ ht)
        (hs.self_of_nhdsWithin hys)
/-
**Filter.EventuallyEq.fderivWithin** 是 Mathlib 中的一个定理，位于命名空间 `Filter.EventuallyE
q`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 : TopologicalSpace E] 
{F : Type u_3} [inst_4 : AddCommGroup F]   [inst_5 : _root_.Module 𝕜 F] [inst_6 
: TopologicalSpace F] {f f₁ : E → F} {x : E} {s : Set E},   f₁ =ᶠ[nhdsWithin x s
] f → fderivWithin 𝕜 f₁ s =ᶠ[nhdsWithin x s] fderivWithin 𝕜 f s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.fderivWithin'`：Filter.EventuallyEq.fderivWithin' (hs
 : f₁ =ᶠ[𝓝[s] x] f) (ht : t subseteq s) : fderivWithin 𝕜 f₁ t =ᶠ[𝓝[s] x] fderivW
ithin 𝕜 f t
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
protected theorem Filter.EventuallyEq.fderivWithin (hs : f₁ =ᶠ[𝓝[s] x] f) :
    fderivWithin 𝕜 f₁ s =ᶠ[𝓝[s] x] fderivWithin 𝕜 f s :=
  hs.fderivWithin' Subset.rfl
/-
**Filter.EventuallyEq.fderivWithin_eq_of_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.fderivWithin_eq_of_nhds (h : f₁ =ᶠ[𝓝 x] f) : fderivWit
hin 𝕜 f₁ s x = fderivWithin 𝕜 f s x
参数：h : f₁ =ᶠ[𝓝 x] f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.fderivWithin_eq`：Filter.EventuallyEq.fderivWithin_eq
 (hs : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : fderivWithin 𝕜 f₁ s x = fderivWithin
 𝕜 f s x
· 使用定理 `Filter.EventuallyEq.filter_mono`：∀ {α : Type u} {β : Type v} {l l' : Fil
ter α} {f g : α → β}, f =ᶠ[l] g → l' ≤ l → f =ᶠ[l'] g
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `Filter.Eventually.self_of_nhds`：Filter.Eventually.self_of_nhds {p : X ->
 Prop} (h : forallᶠ y in 𝓝 x, p y) : p x
-/
theorem Filter.EventuallyEq.fderivWithin_eq_of_nhds (h : f₁ =ᶠ[𝓝 x] f) :
    fderivWithin 𝕜 f₁ s x = fderivWithin 𝕜 f s x :=
  (h.filter_mono nhdsWithin_le_nhds).fderivWithin_eq h.self_of_nhds
/-
**fderivWithin_congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_congr (hs : EqOn f₁ f s) (hx : f₁ x = f x) : fderivWithin 𝕜 f
₁ s x = fderivWithin 𝕜 f s x
参数：hs : EqOn f₁ f s；hx : f₁ x = f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.fderivWithin_eq`：Filter.EventuallyEq.fderivWithin_eq
 (hs : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : fderivWithin 𝕜 f₁ s x = fderivWithin
 𝕜 f s x
· 使用定理 `Filter.EventuallyEq.filter_mono`：∀ {α : Type u} {β : Type v} {l l' : Fil
ter α} {f g : α → β}, f =ᶠ[l] g → l' ≤ l → f =ᶠ[l'] g
· 使用定理 `Set.EqOn.eventuallyEq`：Set.EqOn.eventuallyEq {α β} {s : Set α} {f g : α 
-> β} (h : EqOn f g s) : f =ᶠ[𝓟 s] g
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
-/
theorem fderivWithin_congr (hs : EqOn f₁ f s) (hx : f₁ x = f x) :
    fderivWithin 𝕜 f₁ s x = fderivWithin 𝕜 f s x :=
  (hs.eventuallyEq.filter_mono inf_le_right).fderivWithin_eq hx
/-
**fderivWithin_congr'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_congr' (hs : EqOn f₁ f s) (hx : x in s) : fderivWithin 𝕜 f₁ s
 x = fderivWithin 𝕜 f s x
参数：hs : EqOn f₁ f s；hx : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fderivWithin_congr`：fderivWithin_congr (hs : EqOn f₁ f s) (hx : f₁ x = f
 x) : fderivWithin 𝕜 f₁ s x = fderivWithin 𝕜 f s x
-/
theorem fderivWithin_congr' (hs : EqOn f₁ f s) (hx : x ∈ s) :
    fderivWithin 𝕜 f₁ s x = fderivWithin 𝕜 f s x :=
  fderivWithin_congr hs (hs hx)
/-
**Filter.EventuallyEq.fderiv_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.fderiv_eq (h : f₁ =ᶠ[𝓝 x] f) : fderiv 𝕜 f₁ x = fderiv 
𝕜 f x
参数：h : f₁ =ᶠ[𝓝 x] f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `fderivWithin_univ`：fderivWithin_univ : fderivWithin 𝕜 f univ = fderiv 𝕜 
f
· 使用定理 `Filter.EventuallyEq.fderivWithin_eq_of_nhds`：Filter.EventuallyEq.fderivW
ithin_eq_of_nhds (h : f₁ =ᶠ[𝓝 x] f) : fderivWithin 𝕜 f₁ s x = fderivWithin 𝕜 f s
 x
-/
theorem Filter.EventuallyEq.fderiv_eq (h : f₁ =ᶠ[𝓝 x] f) : fderiv 𝕜 f₁ x = fderiv 𝕜 f x := by
  rw [← fderivWithin_univ, ← fderivWithin_univ, h.fderivWithin_eq_of_nhds]
/-
**Filter.EventuallyEq.fderiv** 是 Mathlib 中的一个定理，位于命名空间 `Filter.EventuallyEq`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 : TopologicalSpace E] 
{F : Type u_3} [inst_4 : AddCommGroup F]   [inst_5 : _root_.Module 𝕜 F] [inst_6 
: TopologicalSpace F] {f f₁ : E → F} {x : E},   f₁ =ᶠ[nhds x] f → fderiv 𝕜 f₁ =ᶠ
[nhds x] fderiv 𝕜 f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.EventuallyEq.eventuallyEq_nhds`：Filter.EventuallyEq.eventuallyEq_
nhds {f g : X -> α} (h : f =ᶠ[𝓝 x] g) : forallᶠ y in 𝓝 x, f =ᶠ[𝓝 y] g
· 使用定理 `Filter.EventuallyEq.fderiv_eq`：Filter.EventuallyEq.fderiv_eq (h : f₁ =ᶠ[
𝓝 x] f) : fderiv 𝕜 f₁ x = fderiv 𝕜 f x
-/
protected theorem Filter.EventuallyEq.fderiv (h : f₁ =ᶠ[𝓝 x] f) : fderiv 𝕜 f₁ =ᶠ[𝓝 x] fderiv 𝕜 f :=
  h.eventuallyEq_nhds.mono fun _ h => h.fderiv_eq

end congr

end

