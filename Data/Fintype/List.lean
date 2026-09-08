/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.List.Permutation

/-!

# Fintype instance for nodup lists

The subtype of `{l : List α // l.Nodup}` over a `[Fintype α]`
admits a `Fintype` instance.

## Implementation details
To construct the `Fintype` instance, a function lifting a `Multiset α`
to the `Multiset (List α)` is provided.
This function is applied to the `Finset.powerset` of `Finset.univ`.

-/

@[expose] public section


variable {α : Type*}
open List

namespace Multiset

/-- Given a `m : Multiset α`, we form the `Multiset` of `l : List α` with the property `⟦l⟧ = m`. -/
/-
**Multiset.lists** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：lists : Multiset α -> Multiset (List α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a `m : Multiset α`, we form the `Multiset` of `l : List α` with the proper
ty `⟦l⟧ = m`.
-/
def lists : Multiset α → Multiset (List α) := fun s =>
  Quotient.liftOn s (fun l => l.permutations) fun l l' (h : l ~ l') => by
    refine coe_eq_coe.mpr ?_
    exact Perm.permutations h

@[simp]
/-
**Multiset.lists_coe** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：lists_coe (l : List α) : lists (l : Multiset α) = l.permutations
参数：l : List α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lists_coe (l : List α) : lists (l : Multiset α) = l.permutations :=
  rfl

@[simp]
/-
**Multiset.lists_nodup_finset** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：lists_nodup_finset (l : Finset α) : (lists (l.val)).Nodup
参数：l : Finset α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.nodup`：∀ {α : Type u_4} (self : Finset α), self.val.Nodup
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_toList`：coe_toList (s : Finset α) : (s.toList : Multiset α) =
 s.val
· 使用定理 `List.nodup_permutations`：nodup_permutations (s : List α) (hs : Nodup s) 
: Nodup s.permutations
· 使用定理 `Multiset.coe_nodup`：coe_nodup {l : List α} : @Nodup α l ↔ l.Nodup
-/
theorem lists_nodup_finset (l : Finset α) : (lists (l.val)).Nodup := by
  have h_nodup : l.val.Nodup := l.nodup
  rw [← Finset.coe_toList l, Multiset.coe_nodup] at h_nodup
  rw [← Finset.coe_toList l]
  exact nodup_permutations l.val.toList (h_nodup)

@[simp]
/-
**Multiset.mem_lists_iff** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：mem_lists_iff (s : Multiset α) (l : List α) : l in lists s ↔ s = ⟦l⟧
参数：s : Multiset α；l : List α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.perm_comm`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Perm l₂ ↔ l₂.Perm 
l₁
-/
theorem mem_lists_iff (s : Multiset α) (l : List α) : l ∈ lists s ↔ s = ⟦l⟧ := by
  induction s using Quotient.inductionOn
  simpa using perm_comm

end Multiset

/-
**fintypeNodupList** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：fintypeNodupList [Fintype α] : Fintype { l : List α // l.Nodup }
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance fintypeNodupList [Fintype α] : Fintype { l : List α // l.Nodup } := by
  refine Fintype.subtype ?_ ?_
  · let univSubsets := ((Finset.univ : Finset α).powerset.1 : (Multiset (Finset α)))
    let allPerms := Multiset.bind univSubsets (fun s => (Multiset.lists s.1))
    refine ⟨allPerms, Multiset.nodup_bind.mpr ?_⟩
    simp only [Multiset.lists_nodup_finset, implies_true, true_and]
    unfold Multiset.Pairwise
    use ((Finset.univ : Finset α).powerset.toList : (List (Finset α)))
    constructor
    · simp only [Finset.coe_toList]
      rfl
    · -- Unfold `List.Nodup` in the type of the proof term to make it match with the goal.
      convert dsimp% [List.Nodup] Finset.nodup_toList (Finset.univ.powerset : Finset (Finset α))
        with m n
      simp only [_root_.Disjoint]
      rw [← m.coe_toList, ← n.coe_toList, Multiset.lists_coe, Multiset.lists_coe]
      have := Multiset.coe_disjoint m.toList.permutations n.toList.permutations
      rw [_root_.Disjoint] at this
      rw [this, List.disjoint_iff_ne]
      constructor
      · intro h
        by_contra hc
        rw [hc] at h
        contrapose! h
        use n.toList
        simp
      · intro h
        simp only [mem_permutations]
        intro a ha b hb
        by_contra hab
        absurd h
        rw [hab] at ha
        exact Finset.perm_toList.mp <| Perm.trans ha.symm hb
  · intro l
    simp only [Finset.mem_mk, Multiset.mem_bind, Finset.mem_val, Finset.mem_powerset,
      Finset.subset_univ, Multiset.mem_lists_iff, Multiset.quot_mk_to_coe, true_and]
    constructor
    · intro h
      rcases h with ⟨f, hf⟩
      convert! f.nodup
      rw [hf]
      rfl
    · intro h
      exact CanLift.prf _ h
