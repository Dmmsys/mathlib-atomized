/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kenny Lau
-/
module

public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Multiset.ZeroCons
public import Mathlib.Order.Directed

/-!
# Finsets of ordered types
-/

public section


universe u v w

variable {α : Type u}

/-
**Directed.finset_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Directed.finset_le {r : α -> α -> Prop} [IsTrans α r] {ι} [hι : Nonempty ι
] {f : ι -> α} (D : Directed r f) (s : Finset ι) : exists z, forall i in s, r (f
 i) (f z)
参数：D : Directed r f；s : Finset ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_cons`：mem_cons {a b : α} {s : Multiset α} : a in b ::ₘ s ↔ 
a = b ∨ a in s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
-/
theorem Directed.finset_le {r : α → α → Prop} [IsTrans α r] {ι} [hι : Nonempty ι] {f : ι → α}
    (D : Directed r f) (s : Finset ι) : ∃ z, ∀ i ∈ s, r (f i) (f z) :=
  show ∃ z, ∀ i ∈ s.1, r (f i) (f z) from
    Multiset.induction_on s.1 (let ⟨z⟩ := hι; ⟨z, fun _ ↦ by simp⟩)
      fun i _ ⟨j, H⟩ ↦
      let ⟨k, h₁, h₂⟩ := D i j
      ⟨k, fun _ h ↦ (Multiset.mem_cons.1 h).casesOn (fun h ↦ h.symm ▸ h₁)
        fun h ↦ _root_.trans (H _ h) h₂⟩
/-
**Finset.exists_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.exists_le [Nonempty α] [Preorder α] [IsDirectedOrder α] (s : Finset
 α) : exists M, forall i in s, i <= M
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Directed.finset_le`：Directed.finset_le {r : α -> α -> Prop} [IsTrans α r
] {ι} [hι : Nonempty ι] {f : ι -> α} (D : Directed r f) (s : Finset ι) : exists 
z, foral…
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
· 使用定理 `directed_id`：directed_id [IsDirected α r] : Directed r id
-/
theorem Finset.exists_le [Nonempty α] [Preorder α] [IsDirectedOrder α] (s : Finset α) :
    ∃ M, ∀ i ∈ s, i ≤ M :=
  directed_id.finset_le _
