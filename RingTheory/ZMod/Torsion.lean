/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Torsion group of `ZMod p` for prime `p`

This file shows that the `ZMod p` has `p - 1` roots-of-unity.

-/

public section

namespace ZMod

/-
**ZMod.rootsOfUnity_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：rootsOfUnity_eq_top {p : Nat} [Fact p.Prime] : (rootsOfUnity (p - 1) (ZMod
 p)) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `ZMod.pow_card_sub_one_eq_one`：pow_card_sub_one_eq_one {a : ZMod p} (ha :
 a != 0) : a ^ (p - 1) = 1
· 使用定理 `Units.ne_zero`：ne_zero [Nontrivial M₀] (u : M₀ˣ) : (u : M₀) != 0
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
-/
lemma rootsOfUnity_eq_top {p : ℕ} [Fact p.Prime] :
    (rootsOfUnity (p - 1) (ZMod p)) = ⊤ := by
  ext
  simpa [Units.ext_iff] using pow_card_sub_one_eq_one (Units.ne_zero _)
/-
**ZMod.** 是 Mathlib 中的一个实例，位于命名空间 `ZMod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {p : ℕ} [Fact p.Prime] : HasEnoughRootsOfUnity (ZMod p) (p - 1) := by
  have : NeZero (p - 1) := ⟨by have : 2 ≤ p := Nat.Prime.two_le Fact.out; grind⟩
  refine HasEnoughRootsOfUnity.of_card_le ?_
  have := Nat.card_congr (MulEquiv.subgroupCongr (ZMod.rootsOfUnity_eq_top (p := p))).toEquiv
  rw [this]
  simp [Fintype.card_units]

end ZMod

