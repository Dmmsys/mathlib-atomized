/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Nicolò Cavalleri
-/
module

public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Topology.ContinuousMap.Algebra

/-!
# Sums of translates of a continuous function is a period continuous function.

-/

public section
assert_not_exists StoneCech StarModule

namespace ContinuousMap

section Periodicity

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-! ### Summing translates of a function -/

/-- Summing the translates of `f` by `ℤ • p` gives a map which is periodic with period `p`.
(This is true without any convergence conditions, since if the sum doesn't converge it is taken to
be the zero map, which is periodic.) -/
/-
**ContinuousMap.periodic_tsum_comp_add_zsmul** 是 Mathlib 中的一个定理，位于命名空间 `Continuo
usMap`。
形式化陈述：periodic_tsum_comp_add_zsmul [AddCommGroup X] [ContinuousAdd X] [AddCommMo
noid Y] [ContinuousAdd Y] [T2Space Y] (f : C(X, Y)) (p : X) : Function.Periodic 
(⇑(∑' n : Int, f.comp (ContinuousMap.addRight (n • p)))) p
参数：f : C(X, Y)；p : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.summable_iff`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst
 : AddCommMonoid α] [inst_1 : TopologicalSpace α] {f : β → α}   (e : γ ≃ β), Sum
mable (f…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousMap.tsum_apply`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] [T2Space β]   [inst_3 : AddCommMonoi
d β] [inst_4 :…
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousMap.addRight.congr_simp`：∀ {X : Type u_5} [inst : TopologicalS
pace X] [inst_1 : Add X] [inst_2 : SeparatelyContinuousAdd X] (x x_1 : X),   x =
 x_1 → ContinuousMap.ad…
· 使用定理 `add_one_zsmul`：∀ {G : Type u_3} [inst : AddGroup G] (a : G) (n : ℤ), (n 
+ 1) • a = n • a + a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Equiv.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : Ad
dCommMonoid α] [inst_1 : TopologicalSpace α] (e : γ ≃ β)   (f : β → α), ∑' (c : 
γ),…
· 使用定理 `tsum_eq_zero_of_not_summable`：∀ {α : Type u_1} {β : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → 
α}, ¬Summable f L …

--- 原说明 ---
Summing the translates of `f` by `ℤ • p` gives a map which is periodic with peri
od `p`.
(This is true without any convergence conditions, since if the sum doesn't conve
rge it is taken to
be the zero map, which is periodic.)
-/
theorem periodic_tsum_comp_add_zsmul [AddCommGroup X] [ContinuousAdd X] [AddCommMonoid Y]
    [ContinuousAdd Y] [T2Space Y] (f : C(X, Y)) (p : X) :
    Function.Periodic (⇑(∑' n : ℤ, f.comp (ContinuousMap.addRight (n • p)))) p := by
  intro x
  by_cases h : Summable fun n : ℤ => f.comp (ContinuousMap.addRight (n • p))
  · convert! congr_arg (fun f : C(X, Y) => f x) ((Equiv.addRight (1 : ℤ)).tsum_eq _) using 1
    -- This `have` unfolds the function composition in `Equiv.summable_iff`.

    -- This `have` unfolds the function composition in `Equiv.summable_iff`.
    have : Summable fun (c : ℤ) => f.comp (ContinuousMap.addRight (Equiv.addRight 1 c • p)) :=
      (Equiv.addRight (1 : ℤ)).summable_iff.mpr h
    simp_rw [← tsum_apply h, ← tsum_apply this]
    simp [Equiv.coe_addRight, comp_apply, add_one_zsmul, add_comm (_ • p) p, ← add_assoc]
  · rw [tsum_eq_zero_of_not_summable h]
    simp only [coe_zero, Pi.zero_apply]

end Periodicity

end ContinuousMap

