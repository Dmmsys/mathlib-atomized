/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.NumberTheory.EulerProduct.Basic

/-!
# Logarithms of Euler Products

We consider `f : ℕ →*₀ ℂ` and show that `exp (∑ p in Primes, log (1 - f p)⁻¹) = ∑ n : ℕ, f n`
under suitable conditions on `f`. This can be seen as a logarithmic version of the
Euler product for `f`.
-/

public section

open Complex

open Topology in
/-- If `f : α → ℂ` is summable, then so is `n ↦ log (1 - f n)`. -/
/-
**Summable.clog_one_sub** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Summable.clog_one_sub {α : Type*} {f : α -> Complex} (hsum : Summable f) :
 Summable fun n => log (1 - f n)
参数：hsum : Summable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.one_mem_slitPlane`：1 ∈ Complex.slitPlane
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `DifferentiableAt.fun_comp'`：DifferentiableAt.fun_comp' {f : E -> F} {g :
 F -> G} (hg : DifferentiableAt 𝕜 g (f x)) (hf : DifferentiableAt 𝕜 f x) : Diffe
rentiableAt 𝕜 (f…
· 使用引理 `Complex.differentiableAt_log`：differentiableAt_log {z : Complex} (hz : z
 in slitPlane) : DifferentiableAt Complex log z
· 使用定理 `DifferentiableAt.const_sub`：DifferentiableAt.const_sub (hf : Differentia
bleAt 𝕜 f x) (c : F) : DifferentiableAt 𝕜 (fun y => c - f y) x
· 使用定理 `differentiableAt_id`：differentiableAt_id : DifferentiableAt 𝕜 id x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Complex.log_one`：log_one : log 1 = 0
· 使用定理 `DifferentiableAt.isBigO_sub`：DifferentiableAt.isBigO_sub (h : Differenti
ableAt 𝕜 f x₀) : (f · - f x₀) =O[𝓝 x₀] (· - x₀)
· 使用引理 `Asymptotics.IsBigO.comp_summable`：Asymptotics.IsBigO.comp_summable {ι E 
F : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [FiniteDimensional Real E
] [NormedAddCommGroup …
· 使用定理 `Complex.instFiniteDimensionalReal`：FiniteDimensional ℝ ℂ
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ

--- 原说明 ---
If `f : α → ℂ` is summable, then so is `n ↦ log (1 - f n)`.
-/
lemma Summable.clog_one_sub {α : Type*} {f : α → ℂ} (hsum : Summable f) :
    Summable fun n ↦ log (1 - f n) := by
  have hg : DifferentiableAt ℂ (fun z ↦ log (1 - z)) 0 := by
    have : 1 - 0 ∈ slitPlane := (sub_zero (1 : ℂ)).symm ▸ one_mem_slitPlane
    fun_prop
  have : (fun z ↦ log (1 - z)) =O[𝓝 0] id := by
    simpa only [sub_zero, log_one] using! hg.isBigO_sub
  exact this.comp_summable hsum

namespace EulerProduct

set_option backward.isDefEq.respectTransparency false in
/-- A variant of the Euler Product formula in terms of the exponential of a sum of logarithms. -/
/-
**EulerProduct.exp_tsum_primes_log_eq_tsum** 是 Mathlib 中的一个定理，位于命名空间 `EulerProdu
ct`。
形式化陈述：exp_tsum_primes_log_eq_tsum {f : Nat ->*₀ Complex} (hsum : Summable (‖f ·‖
)) : exp (∑' p : Nat.Primes, -log (1 - f p)) = ∑' n : Nat, f n
参数：hsum : Summable (‖f ·‖)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Summable.norm_lt_one`：Summable.norm_lt_one {F : Type*} [NormedDivisionRi
ng F] [CompleteSpace F] {f : Nat ->* F} (hsum : Summable f) {p : Nat} (hp : 1 < 
p) : ‖f p‖…
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `Summable.of_norm`：Summable.of_norm {f : ι -> E} (hf : Summable fun a => 
‖f a‖) : Summable f
· 使用定理 `LT.lt.false`：∀ {α : Type u_2} [inst : Preorder α] {a : α}, a < a → False
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `HasProd.tprod_eq`：HasProd.tprod_eq (ha : HasProd f a L) : ∏'[L] b, f b =
 a
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用引理 `HasSum.cexp`：HasSum.cexp {ι : Type*} {f : ι -> Complex} {a : Complex} (h
 : HasSum f a) : HasProd (cexp ∘ f) (cexp a)
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
· 使用定理 `Summable.subtype`：∀ {α : Type u_1} {β : Type u_2} [inst : UniformSpace α
] [inst_1 : AddCommGroup α] [IsUniformAddGroup α] {f : β → α}   [CompleteSpace α
], Sum…
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `Summable.neg`：∀ {α : Type u_1} {β : Type u_2} {L : SummationFilter β} [i
nst : AddCommGroup α] [inst_1 : TopologicalSpace α]   [IsTopologicalAddGroup α] 
{f…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用引理 `Summable.clog_one_sub`：Summable.clog_one_sub {α : Type*} {f : α -> Compl
ex} (hsum : Summable f) : Summable fun n => log (1 - f n)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Complex.exp_neg`：exp_neg : exp (-x) = (exp x)⁻¹
· 使用定理 `Complex.exp_log`：exp_log {x : Complex} (hx : x != 0) : exp (log x) = x
· 使用定理 `EulerProduct.eulerProduct_completely_multiplicative_tprod`：eulerProduct_
completely_multiplicative_tprod {f : Nat ->*₀ F} (hsum : Summable (‖f ·‖)) : ∏' 
p : Primes, (1 - f p)⁻¹ = ∑' n, f n

--- 原说明 ---
A variant of the Euler Product formula in terms of the exponential of a sum of l
ogarithms.
-/
theorem exp_tsum_primes_log_eq_tsum {f : ℕ →*₀ ℂ} (hsum : Summable (‖f ·‖)) :
    exp (∑' p : Nat.Primes, -log (1 - f p)) = ∑' n : ℕ, f n := by
  have hs {p : ℕ} (hp : 1 < p) : ‖f p‖ < 1 := hsum.of_norm.norm_lt_one (f := f.toMonoidHom) hp
  have hp (p : Nat.Primes) : 1 - f p ≠ 0 :=
    fun h ↦ (norm_one (α := ℂ) ▸ (sub_eq_zero.mp h) ▸ hs p.prop.one_lt).false
  have H := hsum.of_norm.clog_one_sub.neg.subtype Nat.Prime |>.hasSum.cexp.tprod_eq
  simp only [Function.comp_apply, exp_neg, exp_log (hp _)] at H
  exact H.symm.trans <| eulerProduct_completely_multiplicative_tprod hsum

end EulerProduct

