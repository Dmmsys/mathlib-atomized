/-
Copyright (c) 2025 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
module

public import Mathlib.Analysis.ODE.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Translation and scaling of integral curves

New integral curves may be constructed by translating or scaling the domain of an existing integral
curve.

## Tags

integral curve, vector field
-/

public section

open Function Set Pointwise

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {γ γ' : ℝ → E} {v : ℝ → E → E} {s s' : Set ℝ} {t₀ : ℝ}

/-! ### Translation lemmas -/

section Translation

/-
**IsIntegralCurveOn.comp_add** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsIntegralCurveOn.comp_add (hγ : IsIntegralCurveOn γ v s) (dt : Real) : Is
IntegralCurveOn (γ ∘ (· + dt)) (v ∘ (· + dt)) (-dt +ᵥ s)
参数：hγ : IsIntegralCurveOn γ v s；dt : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `hasDerivWithinAt_iff_hasFDerivWithinAt`：hasDerivWithinAt_iff_hasFDerivWi
thinAt {f' : F} : HasDerivWithinAt f f' s x ↔ HasFDerivWithinAt f (toSpanSinglet
on 𝕜 f') s x
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `hasFDerivWithinAt_comp_add_right`：hasFDerivWithinAt_comp_add_right (a : 
E) : HasFDerivWithinAt (fun x => f (x + a)) f' s x ↔ HasFDerivWithinAt f f' (a +
ᵥ s) (x + a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vadd_neg_vadd`：∀ {G : Type u_3} {α : Type u_5} [inst : AddGroup G] [inst
_1 : AddAction G α] (g : G) (a : α), g +ᵥ -g +ᵥ a = a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `vadd_eq_add`：∀ {α : Type u_9} [inst : Add α] (a b : α), a +ᵥ b = a + b
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Set.mem_vadd_set_iff_neg_vadd_mem`：∀ {α : Type u_2} {β : Type u_3} [inst
 : AddGroup α] [inst_1 : AddAction α β] {A : Set β} {a : α} {x : β},   x ∈ a +ᵥ 
A ↔ -a +ᵥ x ∈ A
-/
lemma IsIntegralCurveOn.comp_add (hγ : IsIntegralCurveOn γ v s) (dt : ℝ) :
    IsIntegralCurveOn (γ ∘ (· + dt)) (v ∘ (· + dt)) (-dt +ᵥ s) := by
  intros t ht
  rw [comp_apply, hasDerivWithinAt_iff_hasFDerivWithinAt, Function.comp_def,
    hasFDerivWithinAt_comp_add_right, ← hasDerivWithinAt_iff_hasFDerivWithinAt, vadd_neg_vadd]
  apply hγ (t + dt)
  rwa [mem_vadd_set_iff_neg_vadd_mem, neg_neg, vadd_eq_add, add_comm] at ht
/-
**isIntegralCurveOn_comp_add** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isIntegralCurveOn_comp_add {dt : Real} : IsIntegralCurveOn (γ ∘ (· + dt)) 
(v ∘ (· + dt)) (-dt +ᵥ s) ↔ IsIntegralCurveOn γ v s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_add_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ -b + b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `vadd_neg_vadd`：∀ {G : Type u_3} {α : Type u_5} [inst : AddGroup G] [inst
_1 : AddAction G α] (g : G) (a : α), g +ᵥ -g +ᵥ a = a
· 使用引理 `IsIntegralCurveOn.comp_add`：IsIntegralCurveOn.comp_add (hγ : IsIntegralC
urveOn γ v s) (dt : Real) : IsIntegralCurveOn (γ ∘ (· + dt)) (v ∘ (· + dt)) (-dt
 +ᵥ s)
-/
lemma isIntegralCurveOn_comp_add {dt : ℝ} :
    IsIntegralCurveOn (γ ∘ (· + dt)) (v ∘ (· + dt)) (-dt +ᵥ s) ↔ IsIntegralCurveOn γ v s := by
  refine ⟨fun hγ ↦ ?_, fun hγ ↦ hγ.comp_add _⟩
  convert! hγ.comp_add (-dt)
  · ext t
    simp only [comp_apply, neg_add_cancel_right]
  · ext t
    simp only [comp_apply, neg_add_cancel_right]
  · simp only [neg_neg, vadd_neg_vadd]
/-
**isIntegralCurveOn_comp_sub** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isIntegralCurveOn_comp_sub {dt : Real} : IsIntegralCurveOn (γ ∘ (· - dt)) 
(v ∘ (· - dt)) (dt +ᵥ s) ↔ IsIntegralCurveOn γ v s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用引理 `isIntegralCurveOn_comp_add`：isIntegralCurveOn_comp_add {dt : Real} : IsI
ntegralCurveOn (γ ∘ (· + dt)) (v ∘ (· + dt)) (-dt +ᵥ s) ↔ IsIntegralCurveOn γ v 
s
-/
lemma isIntegralCurveOn_comp_sub {dt : ℝ} :
    IsIntegralCurveOn (γ ∘ (· - dt)) (v ∘ (· - dt)) (dt +ᵥ s) ↔ IsIntegralCurveOn γ v s := by
  simpa using! isIntegralCurveOn_comp_add (dt := -dt)
/-
**IsIntegralCurveOn.comp_sub** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsIntegralCurveOn.comp_sub (hγ : IsIntegralCurveOn γ v s) (dt : Real) : Is
IntegralCurveOn (γ ∘ (· - dt)) (v ∘ (· - dt)) (dt +ᵥ s)
参数：hγ : IsIntegralCurveOn γ v s；dt : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `isIntegralCurveOn_comp_sub`：isIntegralCurveOn_comp_sub {dt : Real} : IsI
ntegralCurveOn (γ ∘ (· - dt)) (v ∘ (· - dt)) (dt +ᵥ s) ↔ IsIntegralCurveOn γ v s
-/
lemma IsIntegralCurveOn.comp_sub (hγ : IsIntegralCurveOn γ v s) (dt : ℝ) :
    IsIntegralCurveOn (γ ∘ (· - dt)) (v ∘ (· - dt)) (dt +ᵥ s) :=
  isIntegralCurveOn_comp_sub.mpr hγ
/-
**isIntegralCurveAt_comp_add** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isIntegralCurveAt_comp_add {dt : Real} : IsIntegralCurveAt (γ ∘ (· + dt)) 
(v ∘ (· + dt)) (t₀ - dt) ↔ IsIntegralCurveAt γ v t₀
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Metric.vadd_ball`：∀ {G : Type v} {X : Type w} [inst : PseudoMetricSpace 
X] [inst_1 : AddGroup G] [inst_2 : AddAction G X]   [IsIsometricVAdd G X] (c : G
) (x :…
· 使用定理 `NormedAddGroup.to_isIsometricVAdd`：∀ {E : Type u_2} [inst : SeminormedAd
dGroup E], IsIsometricVAdd E E
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_add_eq_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b :
 α), -a + b = b - a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `isIntegralCurveOn_comp_add`：isIntegralCurveOn_comp_add {dt : Real} : IsI
ntegralCurveOn (γ ∘ (· + dt)) (v ∘ (· + dt)) (-dt +ᵥ s) ↔ IsIntegralCurveOn γ v 
s
-/
lemma isIntegralCurveAt_comp_add {dt : ℝ} :
    IsIntegralCurveAt (γ ∘ (· + dt)) (v ∘ (· + dt)) (t₀ - dt) ↔ IsIntegralCurveAt γ v t₀ := by
  simp_rw [isIntegralCurveAt_iff_exists_pos]
  congrm ∃ ε > 0, ?_
  convert! isIntegralCurveOn_comp_add
  simp [neg_add_eq_sub]
/-
**IsIntegralCurveAt.comp_add** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsIntegralCurveAt.comp_add (hγ : IsIntegralCurveAt γ v t₀) (dt : Real) : I
sIntegralCurveAt (γ ∘ (· + dt)) (v ∘ (· + dt)) (t₀ - dt)
参数：hγ : IsIntegralCurveAt γ v t₀；dt : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `isIntegralCurveAt_comp_add`：isIntegralCurveAt_comp_add {dt : Real} : IsI
ntegralCurveAt (γ ∘ (· + dt)) (v ∘ (· + dt)) (t₀ - dt) ↔ IsIntegralCurveAt γ v t
₀
-/
lemma IsIntegralCurveAt.comp_add (hγ : IsIntegralCurveAt γ v t₀) (dt : ℝ) :
    IsIntegralCurveAt (γ ∘ (· + dt)) (v ∘ (· + dt)) (t₀ - dt) :=
  isIntegralCurveAt_comp_add.mpr hγ
/-
**isIntegralCurveAt_comp_sub** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isIntegralCurveAt_comp_sub {dt : Real} : IsIntegralCurveAt (γ ∘ (· - dt)) 
(v ∘ (· - dt)) (t₀ + dt) ↔ IsIntegralCurveAt γ v t₀
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用引理 `isIntegralCurveAt_comp_add`：isIntegralCurveAt_comp_add {dt : Real} : IsI
ntegralCurveAt (γ ∘ (· + dt)) (v ∘ (· + dt)) (t₀ - dt) ↔ IsIntegralCurveAt γ v t
₀
-/
lemma isIntegralCurveAt_comp_sub {dt : ℝ} :
    IsIntegralCurveAt (γ ∘ (· - dt)) (v ∘ (· - dt)) (t₀ + dt) ↔ IsIntegralCurveAt γ v t₀ := by
  simpa using! isIntegralCurveAt_comp_add (dt := -dt)
/-
**IsIntegralCurveAt.comp_sub** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsIntegralCurveAt.comp_sub (hγ : IsIntegralCurveAt γ v t₀) (dt : Real) : I
sIntegralCurveAt (γ ∘ (· - dt)) (v ∘ (· - dt)) (t₀ + dt)
参数：hγ : IsIntegralCurveAt γ v t₀；dt : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `isIntegralCurveAt_comp_sub`：isIntegralCurveAt_comp_sub {dt : Real} : IsI
ntegralCurveAt (γ ∘ (· - dt)) (v ∘ (· - dt)) (t₀ + dt) ↔ IsIntegralCurveAt γ v t
₀
-/
lemma IsIntegralCurveAt.comp_sub (hγ : IsIntegralCurveAt γ v t₀) (dt : ℝ) :
    IsIntegralCurveAt (γ ∘ (· - dt)) (v ∘ (· - dt)) (t₀ + dt) :=
  isIntegralCurveAt_comp_sub.mpr hγ
/-
**IsIntegralCurve.comp_add** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsIntegralCurve.comp_add (hγ : IsIntegralCurve γ v) (dt : Real) : IsIntegr
alCurve (γ ∘ (· + dt)) (v ∘ (· + dt))
参数：hγ : IsIntegralCurve γ v；dt : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `isIntegralCurveOn_univ`：isIntegralCurveOn_univ : IsIntegralCurveOn γ v u
niv ↔ IsIntegralCurve γ v
· 使用定理 `Set.vadd_set_univ`：∀ {α : Type u_2} {β : Type u_3} [inst : AddGroup α] [
inst_1 : AddAction α β] {a : α}, a +ᵥ Set.univ = Set.univ
· 使用引理 `IsIntegralCurveOn.comp_add`：IsIntegralCurveOn.comp_add (hγ : IsIntegralC
urveOn γ v s) (dt : Real) : IsIntegralCurveOn (γ ∘ (· + dt)) (v ∘ (· + dt)) (-dt
 +ᵥ s)
-/
lemma IsIntegralCurve.comp_add (hγ : IsIntegralCurve γ v) (dt : ℝ) :
    IsIntegralCurve (γ ∘ (· + dt)) (v ∘ (· + dt)) := by
  rw [← isIntegralCurveOn_univ] at *
  simpa using hγ.comp_add dt
/-
**isIntegralCurve_comp_add** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isIntegralCurve_comp_add {dt : Real} : IsIntegralCurve (γ ∘ (· + dt)) (v ∘
 (· + dt)) ↔ IsIntegralCurve γ v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.vadd_set_univ`：∀ {α : Type u_2} {β : Type u_3} [inst : AddGroup α] [
inst_1 : AddAction α β] {a : α}, a +ᵥ Set.univ = Set.univ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `isIntegralCurveOn_comp_add`：isIntegralCurveOn_comp_add {dt : Real} : IsI
ntegralCurveOn (γ ∘ (· + dt)) (v ∘ (· + dt)) (-dt +ᵥ s) ↔ IsIntegralCurveOn γ v 
s
-/
lemma isIntegralCurve_comp_add {dt : ℝ} :
    IsIntegralCurve (γ ∘ (· + dt)) (v ∘ (· + dt)) ↔ IsIntegralCurve γ v := by
  simp_rw [← isIntegralCurveOn_univ]
  convert! isIntegralCurveOn_comp_add
  simp
/-
**isIntegralCurve_comp_sub** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isIntegralCurve_comp_sub {dt : Real} : IsIntegralCurve (γ ∘ (· - dt)) (v ∘
 (· - dt)) ↔ IsIntegralCurve γ v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `isIntegralCurve_comp_add`：isIntegralCurve_comp_add {dt : Real} : IsInteg
ralCurve (γ ∘ (· + dt)) (v ∘ (· + dt)) ↔ IsIntegralCurve γ v
-/
lemma isIntegralCurve_comp_sub {dt : ℝ} :
    IsIntegralCurve (γ ∘ (· - dt)) (v ∘ (· - dt)) ↔ IsIntegralCurve γ v := by
  simpa using! isIntegralCurve_comp_add (dt := -dt)
/-
**IsIntegralCurve.comp_sub** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsIntegralCurve.comp_sub (hγ : IsIntegralCurve γ v) (dt : Real) : IsIntegr
alCurve (γ ∘ (· - dt)) (v ∘ (· - dt))
参数：hγ : IsIntegralCurve γ v；dt : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `isIntegralCurve_comp_sub`：isIntegralCurve_comp_sub {dt : Real} : IsInteg
ralCurve (γ ∘ (· - dt)) (v ∘ (· - dt)) ↔ IsIntegralCurve γ v
-/
lemma IsIntegralCurve.comp_sub (hγ : IsIntegralCurve γ v) (dt : ℝ) :
    IsIntegralCurve (γ ∘ (· - dt)) (v ∘ (· - dt)) :=
  isIntegralCurve_comp_sub.mpr hγ

end Translation

/-! ### Scaling lemmas -/

section Scaling

/-
**IsIntegralCurveOn.comp_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsIntegralCurveOn.comp_mul (hγ : IsIntegralCurveOn γ v s) (a : Real) : IsI
ntegralCurveOn (γ ∘ (· * a)) (a • v ∘ (· * a)) { t | t * a in s }
参数：hγ : IsIntegralCurveOn γ v s；a : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivWithinAt.scomp`：HasDerivWithinAt.scomp (hg : HasDerivWithinAt g₁
 g₁' t' (h x)) (hh : HasDerivWithinAt h h' s x) (hst : MapsTo h s t') : HasDeriv
WithinAt (g₁…
· 使用定理 `HasDerivAt.hasDerivWithinAt`：HasDerivAt.hasDerivWithinAt (h : HasDerivAt
 f f' x) : HasDerivWithinAt f f' s x
· 使用定理 `hasDerivAt_mul_const`：hasDerivAt_mul_const (c : 𝕜) : HasDerivAt (fun x =
> x * c) c x
-/
lemma IsIntegralCurveOn.comp_mul (hγ : IsIntegralCurveOn γ v s) (a : ℝ) :
    IsIntegralCurveOn (γ ∘ (· * a)) (a • v ∘ (· * a)) { t | t * a ∈ s } := fun t ht ↦ by
  simp only [comp_apply, Pi.smul_apply]
  exact HasDerivWithinAt.scomp t (hγ (t * a) ht) (hasDerivAt_mul_const a).hasDerivWithinAt
    fun _ ht' ↦ ht'
/-
**isIntegralCurveOn_comp_mul_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isIntegralCurveOn_comp_mul_ne_zero {a : Real} (ha : a != 0) : IsIntegralCu
rveOn (γ ∘ (· * a)) (a • v ∘ (· * a)) (a⁻¹ • s) ↔ IsIntegralCurveOn γ v s
参数：ha : a != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.mem_inv_smul_set_iff₀`：mem_inv_smul_set_iff₀ (ha : a != 0) (A : Set 
β) (x : β) : x in a⁻¹ • A ↔ a • x in A
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `inv_mul_eq_div`：inv_mul_eq_div : a⁻¹ * b = b / a
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用引理 `smul_inv_smul₀`：smul_inv_smul₀ (ha : a != 0) (x : β) : a • a⁻¹ • x = x
· 使用引理 `IsIntegralCurveOn.comp_mul`：IsIntegralCurveOn.comp_mul (hγ : IsIntegralC
urveOn γ v s) (a : Real) : IsIntegralCurveOn (γ ∘ (· * a)) (a • v ∘ (· * a)) { t
 | t * a in s }
-/
lemma isIntegralCurveOn_comp_mul_ne_zero {a : ℝ} (ha : a ≠ 0) :
    IsIntegralCurveOn (γ ∘ (· * a)) (a • v ∘ (· * a)) (a⁻¹ • s) ↔ IsIntegralCurveOn γ v s := by
  have heq : a⁻¹ • s = { t | t * a ∈ s } := by
    ext t
    rw [mem_inv_smul_set_iff₀ ha, smul_eq_mul, mul_comm]
    rfl
  refine ⟨fun hγ ↦ ?_, heq ▸ fun hγ ↦ hγ.comp_mul a⟩
  convert! hγ.comp_mul a⁻¹
  · ext t
    simp only [comp_apply, mul_assoc, inv_mul_eq_div, div_self ha, mul_one]
  · ext t
    simp only [comp_apply, Pi.smul_apply, mul_assoc, inv_mul_eq_div, div_self ha, mul_one,
      smul_smul, one_smul]
  · simp only [mul_comm _ a⁻¹, ← smul_eq_mul, mem_inv_smul_set_iff₀ ha, smul_inv_smul₀ ha,
      ofPred_mem_eq]
/-
**IsIntegralCurveAt.comp_mul_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsIntegralCurveAt.comp_mul_ne_zero (hγ : IsIntegralCurveAt γ v t₀) {a : Re
al} (ha : a != 0) : IsIntegralCurveAt (γ ∘ (· * a)) (a • v ∘ (· * a)) (t₀ / a)
参数：hγ : IsIntegralCurveAt γ v t₀；ha : a != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `isIntegralCurveAt_iff_exists_pos`：isIntegralCurveAt_iff_exists_pos : IsI
ntegralCurveAt γ v t₀ ↔ exists ε > 0, IsIntegralCurveOn γ v (Metric.ball t₀ ε)
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Mathlib.Meta.Positivity.abs_pos_of_ne_zero`：abs_pos_of_ne_zero {α : Type
*} [AddGroup α] [LinearOrder α] [AddLeftMono α] {a : α} : a != 0 -> 0 < |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用定理 `Metric.mem_ball`：mem_ball : y in ball x ε ↔ dist y x < ε
· 使用定理 `Real.dist_eq`：Real.dist_eq (x y : Real) : dist x y = |x - y|
· 使用引理 `lt_div_iff₀`：lt_div_iff₀ (hc : 0 < c) : a < b / c ↔ a * c < b
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `abs_pos`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α] [
AddLeftMono α] {a : α}, 0 < |a| ↔ a ≠ 0
· 使用引理 `abs_mul`：abs_mul (a b : α) : |a * b| = |a| * |b|
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用引理 `div_mul_cancel₀`：div_mul_cancel₀ (a : G₀) (h : b != 0) : a / b * b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用引理 `IsIntegralCurveOn.comp_mul`：IsIntegralCurveOn.comp_mul (hγ : IsIntegralC
urveOn γ v s) (a : Real) : IsIntegralCurveOn (γ ∘ (· * a)) (a • v ∘ (· * a)) { t
 | t * a in s }
-/
lemma IsIntegralCurveAt.comp_mul_ne_zero (hγ : IsIntegralCurveAt γ v t₀) {a : ℝ} (ha : a ≠ 0) :
    IsIntegralCurveAt (γ ∘ (· * a)) (a • v ∘ (· * a)) (t₀ / a) := by
  rw [isIntegralCurveAt_iff_exists_pos] at *
  obtain ⟨ε, hε, h⟩ := hγ
  refine ⟨ε / |a|, by positivity, ?_⟩
  convert! h.comp_mul a
  ext t
  rw [mem_ofPred_eq, Metric.mem_ball, Metric.mem_ball, Real.dist_eq, Real.dist_eq,
    lt_div_iff₀ (abs_pos.mpr ha), ← abs_mul, sub_mul, div_mul_cancel₀ _ ha]
/-
**isIntegralCurveAt_comp_mul_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isIntegralCurveAt_comp_mul_ne_zero {a : Real} (ha : a != 0) : IsIntegralCu
rveAt (γ ∘ (· * a)) (a • v ∘ (· * a)) (t₀ / a) ↔ IsIntegralCurveAt γ v t₀
参数：ha : a != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `inv_mul_eq_div`：inv_mul_eq_div : a⁻¹ * b = b / a
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `div_inv_eq_mul`：div_inv_eq_mul : a / b⁻¹ = a * b
· 使用引理 `div_mul_cancel₀`：div_mul_cancel₀ (a : G₀) (h : b != 0) : a / b * b = a
· 使用引理 `IsIntegralCurveAt.comp_mul_ne_zero`：IsIntegralCurveAt.comp_mul_ne_zero (
hγ : IsIntegralCurveAt γ v t₀) {a : Real} (ha : a != 0) : IsIntegralCurveAt (γ ∘
 (· * a)) (a • v ∘ (· * …
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
-/
lemma isIntegralCurveAt_comp_mul_ne_zero {a : ℝ} (ha : a ≠ 0) :
    IsIntegralCurveAt (γ ∘ (· * a)) (a • v ∘ (· * a)) (t₀ / a) ↔ IsIntegralCurveAt γ v t₀ := by
  refine ⟨fun hγ ↦ ?_, fun hγ ↦ hγ.comp_mul_ne_zero ha⟩
  convert! hγ.comp_mul_ne_zero (inv_ne_zero ha)
  · ext t
    simp only [comp_apply, mul_assoc, inv_mul_eq_div, div_self ha, mul_one]
  · ext t
    simp only [comp_apply, Pi.smul_apply, mul_assoc, inv_mul_eq_div, div_self ha, mul_one,
      smul_smul, one_smul]
  · simp only [div_inv_eq_mul, div_mul_cancel₀ _ ha]
/-
**IsIntegralCurve.comp_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsIntegralCurve.comp_mul (hγ : IsIntegralCurve γ v) (a : Real) : IsIntegra
lCurve (γ ∘ (· * a)) (a • v ∘ (· * a))
参数：hγ : IsIntegralCurve γ v；a : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `isIntegralCurveOn_univ`：isIntegralCurveOn_univ : IsIntegralCurveOn γ v u
niv ↔ IsIntegralCurve γ v
· 使用引理 `IsIntegralCurveOn.comp_mul`：IsIntegralCurveOn.comp_mul (hγ : IsIntegralC
urveOn γ v s) (a : Real) : IsIntegralCurveOn (γ ∘ (· * a)) (a • v ∘ (· * a)) { t
 | t * a in s }
-/
lemma IsIntegralCurve.comp_mul (hγ : IsIntegralCurve γ v) (a : ℝ) :
    IsIntegralCurve (γ ∘ (· * a)) (a • v ∘ (· * a)) := by
  rw [← isIntegralCurveOn_univ] at *
  exact hγ.comp_mul _
/-
**isIntegralCurve_comp_mul_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isIntegralCurve_comp_mul_ne_zero {a : Real} (ha : a != 0) : IsIntegralCurv
e (γ ∘ (· * a)) (a • v ∘ (· * a)) ↔ IsIntegralCurve γ v
参数：ha : a != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `inv_mul_eq_div`：inv_mul_eq_div : a⁻¹ * b = b / a
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用引理 `IsIntegralCurve.comp_mul`：IsIntegralCurve.comp_mul (hγ : IsIntegralCurve
 γ v) (a : Real) : IsIntegralCurve (γ ∘ (· * a)) (a • v ∘ (· * a))
-/
lemma isIntegralCurve_comp_mul_ne_zero {a : ℝ} (ha : a ≠ 0) :
    IsIntegralCurve (γ ∘ (· * a)) (a • v ∘ (· * a)) ↔ IsIntegralCurve γ v := by
  refine ⟨fun hγ ↦ ?_, fun hγ ↦ hγ.comp_mul _⟩
  convert! hγ.comp_mul a⁻¹
  · ext t
    simp only [comp_apply, mul_assoc, inv_mul_eq_div, div_self ha, mul_one]
  · ext t
    simp only [comp_apply, Pi.smul_apply, mul_assoc, inv_mul_eq_div, div_self ha, mul_one,
      smul_smul, one_smul]

/-- If the vector field `v` vanishes at `x₀` for all times, then the constant curve at `x₀`
is a global integral curve of `v`. -/
/-
**isIntegralCurve_const** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isIntegralCurve_const {x : E} (h : forall t, v t x = 0) : IsIntegralCurve 
(fun _ => x) v
参数：h : forall t, v t x = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasDerivAt_const`：hasDerivAt_const : HasDerivAt (fun _ => c) 0 x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If the vector field `v` vanishes at `x₀` for all times, then the constant curve 
at `x₀`
is a global integral curve of `v`.
-/
lemma isIntegralCurve_const {x : E} (h : ∀ t, v t x = 0) : IsIntegralCurve (fun _ ↦ x) v :=
  fun t ↦ (h t) ▸ hasDerivAt_const _ _

end Scaling

