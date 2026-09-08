/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Iterated derivatives of analytic functions with power factors

This file contains lemmas about the iterated derivative of a function that factors as a
power of `(· - z₀)` times an analytic function.
-/

public section

open scoped Nat

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜] [CompleteSpace 𝕜]

/-- If a function `R : 𝕜 → 𝕜` factors as `R z = (z - z₀) ^ (k + t) * R₁ z`, where `R₁` is
analytic everywhere, then there exists an everywhere analytic function `R₂ : 𝕜 → 𝕜` such that
the `k`-th iterated derivative of `R` is given by
`iteratedDeriv k R z = (z - z₀) ^ t * ((k + t)! / t ! * R₁ z + (z - z₀) * R₂ z)`. -/
/-
**iteratedDeriv_mul_pow_sub_of_analytic** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：iteratedDeriv_mul_pow_sub_of_analytic {k t : Nat} {z₀ : 𝕜} {R R₁ : 𝕜 -> 𝕜}
 (hf1 : forall z, AnalyticAt 𝕜 R₁ z) (hR₁ : forall z, R z = (z - z₀) ^ (k + t) *
 R₁ z) : exists R₂, (forall z, AnalyticAt 𝕜 R₂ z) ∧ forall z, iteratedDeriv k R 
z = (z - z₀) ^ t * ((k + t)! / t ! * R₁ z + (z - z₀) * R₂ z)
参数：hf1 : forall z, AnalyticAt 𝕜 R₁ z；hR₁ : forall z, R z = (z - z₀) ^ (k + t) * 
R₁ z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `analyticAt_const`：analyticAt_const {v : F} {x : E} : AnalyticAt 𝕜 (fun _
 => v) x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iteratedDeriv_zero`：iteratedDeriv_zero : iteratedDeriv 0 f = f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `AnalyticAt.fun_add`：∀ {𝕜 : Type u_2} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_3} {F : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 …
· 使用定理 `AnalyticAt.fun_mul`：∀ {𝕜 : Type u_2} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {A :
 Type u_…
· 使用定理 `AnalyticAt.deriv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {F
 : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {f : 𝕜 →
 F} {x…
· 使用定理 `AnalyticAt.fun_sub`：∀ {𝕜 : Type u_2} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_3} {F : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 …
· 使用引理 `analyticAt_id`：analyticAt_id : AnalyticAt 𝕜 (id : E -> E) z
· 使用定理 `iteratedDeriv_succ`：iteratedDeriv_succ : iteratedDeriv (n + 1) f = deriv
 (iteratedDeriv n f)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `HasDerivAt.sub_const`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] 
{F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {f : 𝕜
 → F} {f' …
· 使用定理 `hasDerivAt_id`：hasDerivAt_id : HasDerivAt id 1 x
（共 50 条，此处仅展示前 30 条）

--- 原说明 ---
If a function `R : 𝕜 → 𝕜` factors as `R z = (z - z₀) ^ (k + t) * R₁ z`, where `R
₁` is
analytic everywhere, then there exists an everywhere analytic function `R₂ : 𝕜 →
 𝕜` such that
the `k`-th iterated derivative of `R` is given by
`iteratedDeriv k R z = (z - z₀) ^ t * ((k + t)! / t ! * R₁ z + (z - z₀) * R₂ z)`
.
-/
lemma iteratedDeriv_mul_pow_sub_of_analytic {k t : ℕ} {z₀ : 𝕜} {R R₁ : 𝕜 → 𝕜}
    (hf1 : ∀ z, AnalyticAt 𝕜 R₁ z) (hR₁ : ∀ z, R z = (z - z₀) ^ (k + t) * R₁ z) :
    ∃ R₂, (∀ z, AnalyticAt 𝕜 R₂ z) ∧ ∀ z, iteratedDeriv k R z =
      (z - z₀) ^ t * ((k + t)! / t ! * R₁ z + (z - z₀) * R₂ z) := by
  induction k generalizing t with
  | zero => exact ⟨0, fun _ ↦ analyticAt_const, by simp [hR₁, Nat.factorial_ne_zero]⟩
  | succ k IH =>
    obtain ⟨R₂, hR₂, hR₂_eq⟩ := IH (t := t + 1) (by grind)
    set R₂' : 𝕜 → 𝕜 := fun z ↦ (t + 1) * R₂ z + ((k + (t + 1))! / (t + 1)! * deriv R₁ z +
      (R₂ z + (z - z₀) * deriv R₂ z))
    refine ⟨R₂', by fun_prop, fun z ↦ ?_⟩
    calc iteratedDeriv (k + 1) R z
      _ = deriv (fun w ↦ (w - z₀) ^ (t + 1)
          * (↑(k + (t + 1))! / ↑(t + 1)! * R₁ w + (w - z₀) * R₂ w)) z := by
        rw [iteratedDeriv_succ, funext hR₂_eq]
      _ = (t + 1) * (z - z₀) ^ t * ((k + (t + 1))! / (t + 1)! * R₁ z + (z - z₀) * R₂ z) +
        (z - z₀) ^ (t + 1) * ((k + (t + 1))! / (t + 1)! * deriv R₁ z +
          (R₂ z + (z - z₀) * deriv R₂ z)) := by
        have hsub : HasDerivAt (· - z₀) 1 z := (hasDerivAt_id z).sub_const z₀
        simpa using! ((hsub.fun_pow (t + 1)).mul
          (((hf1 z).differentiableAt.hasDerivAt.const_mul ((k + (t + 1))! / (t + 1)! : 𝕜)).add
            (hsub.mul (hR₂ z).differentiableAt.hasDerivAt))).deriv
      _ = (z - z₀) ^ t * ((k + 1 + t)! / t ! * R₁ z + (z - z₀) * R₂' z) := by
        have : (t : 𝕜) + 1 ≠ 0 := mod_cast t.succ_ne_zero
        have : ((t + 1)! : 𝕜) = (t + 1) * t ! := by simp [Nat.factorial_succ]
        grind
