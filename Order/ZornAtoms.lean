/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Order.Zorn
public import Mathlib.Order.Atoms

/-!
# Zorn lemma for (co)atoms

In this file we use Zorn's lemma to prove that a partial order is atomic if every nonempty chain
`c`, `⊥ ∉ c`, has a lower bound not equal to `⊥`. We also prove the order dual version of this
statement.
-/

public section


open Set

/-- **Zorn's lemma**: A partial order is coatomic if every nonempty chain `c`, `⊤ ∉ c`, has an upper
bound not equal to `⊤`. -/
/-
**IsCoatomic.of_isChain_bounded** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCoatomic.of_isChain_bounded {α : Type*} [PartialOrder α] [OrderTop α] (h
 : forall c : Set α, IsChain (· <= ·) c -> c.Nonempty -> ⊤ ∉ c -> exists x != ⊤,
 x in upperBounds c) : IsCoatomic α
参数：h : forall c : Set α, IsChain (· <= ·) c -> c.Nonempty -> ⊤ ∉ c -> exists x !
= ⊤, x in upperBounds c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp_right`：∀ {b c a : Prop}, (b → c) → a ∨ b → a ∨ c
· 使用定理 `zorn_le_nonempty₀`：zorn_le_nonempty₀ (s : Set α) (ih : forall c subseteq
 s, IsChain (· <= ·) c -> forall y in c, exists ub in s, forall z in c, z <= ub)
 (x : α…
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.left_mem_Ico`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ Se
t.Ico a b ↔ a < b
· 使用定理 `Maximal.prop`：∀ {α : Type u_1} [inst : LE α] {P : α → Prop} {x : α}, Max
imal P x → P x
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Maximal.eq_of_le`：∀ {α : Type u_2} {P : α → Prop} {x y : α} [inst : Part
ialOrder α], Maximal P x → P y → x ≤ y → x = y
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b

--- 原说明 ---
**Zorn's lemma**: A partial order is coatomic if every nonempty chain `c`, `⊤ ∉ 
c`, has an upper
bound not equal to `⊤`.
-/
theorem IsCoatomic.of_isChain_bounded {α : Type*} [PartialOrder α] [OrderTop α]
    (h : ∀ c : Set α, IsChain (· ≤ ·) c → c.Nonempty → ⊤ ∉ c → ∃ x ≠ ⊤, x ∈ upperBounds c) :
    IsCoatomic α := by
  refine ⟨fun x => le_top.eq_or_lt.imp_right fun hx => ?_⟩
  have := zorn_le_nonempty₀ (Ico x ⊤) (fun c hxc hc y hy => ?_) x (left_mem_Ico.2 hx)
  · obtain ⟨y, hxy, hmax⟩ := this
    refine ⟨y, ⟨hmax.prop.2.ne, fun z hyz ↦ le_top.eq_or_lt.resolve_right fun hz => ?_⟩, hxy⟩
    exact hyz.ne <| hmax.eq_of_le ⟨hxy.trans hyz.le, hz⟩ hyz.le
  rcases h c hc ⟨y, hy⟩ fun h => (hxc h).2.ne rfl with ⟨z, hz, hcz⟩
  exact ⟨z, ⟨le_trans (hxc hy).1 (hcz hy), hz.lt_top⟩, hcz⟩

/-- **Zorn's lemma**: A partial order is atomic if every nonempty chain `c`, `⊥ ∉ c`, has a lower
bound not equal to `⊥`. -/
/-
**IsAtomic.of_isChain_bounded** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsAtomic.of_isChain_bounded {α : Type*} [PartialOrder α] [OrderBot α] (h :
 forall c : Set α, IsChain (· <= ·) c -> c.Nonempty -> ⊥ ∉ c -> exists x != ⊥, x
 in lowerBounds c) : IsAtomic α
参数：h : forall c : Set α, IsChain (· <= ·) c -> c.Nonempty -> ⊥ ∉ c -> exists x !
= ⊥, x in lowerBounds c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isCoatomic_dual_iff_isAtomic`：isCoatomic_dual_iff_isAtomic [OrderBot α] 
: IsCoatomic αᵒᵈ ↔ IsAtomic α
· 使用定理 `IsCoatomic.of_isChain_bounded`：IsCoatomic.of_isChain_bounded {α : Type*}
 [PartialOrder α] [OrderTop α] (h : forall c : Set α, IsChain (· <= ·) c -> c.No
nempty -> ⊤ ∉ c -> …
· 使用定理 `IsChain.symm`：IsChain.symm (h : IsChain r s) : IsChain (flip r) s

--- 原说明 ---
**Zorn's lemma**: A partial order is atomic if every nonempty chain `c`, `⊥ ∉ c`
, has a lower
bound not equal to `⊥`.
-/
theorem IsAtomic.of_isChain_bounded {α : Type*} [PartialOrder α] [OrderBot α]
    (h :
      ∀ c : Set α,
        IsChain (· ≤ ·) c → c.Nonempty → ⊥ ∉ c → ∃ x ≠ ⊥, x ∈ lowerBounds c) :
    IsAtomic α :=
  isCoatomic_dual_iff_isAtomic.mp <| IsCoatomic.of_isChain_bounded fun c hc => h c hc.symm
