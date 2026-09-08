/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Topology.DenseEmbedding

/-!
# Additive characters of topological monoids
-/

public section

/-
**DenseRange.addChar_eq_of_eval_one_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：DenseRange.addChar_eq_of_eval_one_eq {A M : Type*} [TopologicalSpace A] [A
ddMonoidWithOne A] [Monoid M] [TopologicalSpace M] [T2Space M] (hdr : DenseRange
 ((↑) : Nat -> A)) {κ₁ κ₂ : AddChar A M} (hκ₁ : Continuous κ₁) (hκ₂ : Continuous
 κ₂) (h : κ₁ 1 = κ₂ 1) : κ₁ = κ₂
参数：hdr : DenseRange ((↑) : Nat -> A)；hκ₁ : Continuous κ₁；hκ₂ : Continuous κ₂；h :
 κ₁ 1 = κ₂ 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
· 使用定理 `DenseRange.equalizer`：DenseRange.equalizer (hfd : DenseRange f) {g h : β
 -> γ} (hg : Continuous g) (hh : Continuous h) (H : g ∘ f = h ∘ f) : g = h
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AddChar.map_nsmul_eq_pow`：map_nsmul_eq_pow (ψ : AddChar A M) (n : Nat) (
x : A) : ψ (n • x) = ψ x ^ n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma DenseRange.addChar_eq_of_eval_one_eq {A M : Type*} [TopologicalSpace A] [AddMonoidWithOne A]
    [Monoid M] [TopologicalSpace M] [T2Space M] (hdr : DenseRange ((↑) : ℕ → A))
    {κ₁ κ₂ : AddChar A M} (hκ₁ : Continuous κ₁) (hκ₂ : Continuous κ₂) (h : κ₁ 1 = κ₂ 1) :
    κ₁ = κ₂ := by
  refine DFunLike.coe_injective <| hdr.equalizer hκ₁ hκ₂ (funext fun n ↦ ?_)
  simp only [Function.comp_apply, ← nsmul_one, h, AddChar.map_nsmul_eq_pow]
