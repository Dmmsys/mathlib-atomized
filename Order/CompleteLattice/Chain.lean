/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Data.Set.Lattice
public import Mathlib.Order.Preorder.Chain

/-!
# Hausdorff's maximality principle

This file proves Hausdorff's maximality principle.

## Main declarations

* `maxChain_spec`: Hausdorff's Maximality Principle.

## Notes

Originally ported from Isabelle/HOL. The
[original file](https://isabelle.in.tum.de/dist/library/HOL/HOL/Zorn.html) was written by Jacques D.
Fleuriot, Tobias Nipkow, Christian Sternagel.
-/

@[expose] public section

open Set

variable {α : Type*} {r : α → α → Prop} {c c₁ c₂ s t : Set α} {a b x y : α}

/-- Predicate for whether a set is reachable from `∅` using `SuccChain` and `⋃₀`. -/
/-
**ChainClosure** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{α : Type u_1} → (α → α → Prop) → Set α → Prop
参数：α → α → Prop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Predicate for whether a set is reachable from `∅` using `SuccChain` and `⋃₀`.
-/
inductive ChainClosure (r : α → α → Prop) : Set α → Prop
  | succ : ∀ {s}, ChainClosure r s → ChainClosure r (SuccChain r s)
  | union : ∀ {s}, (∀ a ∈ s, ChainClosure r a) → ChainClosure r (⋃₀ s)

/-- An explicit maximal chain. `maxChain` is taken to be the union of all sets in `ChainClosure`. -/
/-
**maxChain** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：maxChain (r : α -> α -> Prop) : Set α
参数：r : α -> α -> Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An explicit maximal chain. `maxChain` is taken to be the union of all sets in `C
hainClosure`.
-/
def maxChain (r : α → α → Prop) : Set α := ⋃₀ Set.ofPred (ChainClosure r)
/-
**chainClosure_empty** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：chainClosure_empty : ChainClosure r ∅
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.notMem_empty`：notMem_empty (x : α) : x ∉ (∅ : Set α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sUnion_empty`：sUnion_empty : ⋃₀ ∅ = (∅ : Set α)
-/
lemma chainClosure_empty : ChainClosure r ∅ := by
  have : ChainClosure r (⋃₀ ∅) := ChainClosure.union fun a h => (notMem_empty _ h).elim
  simpa using this
/-
**chainClosure_maxChain** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：chainClosure_maxChain : ChainClosure r (maxChain r)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma chainClosure_maxChain : ChainClosure r (maxChain r) :=
  ChainClosure.union fun _ => id
/-
**chainClosure_succ_total_aux** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma chainClosure_succ_total_aux (hc₁ : ChainClosure r c₁)
    (h : ∀ ⦃c₃⦄, ChainClosure r c₃ → c₃ ⊆ c₂ → c₂ = c₃ ∨ SuccChain r c₃ ⊆ c₂) :
    SuccChain r c₂ ⊆ c₁ ∨ c₁ ⊆ c₂ := by
  induction hc₁ with
  | @succ c₃ hc₃ ih =>
    obtain ih | ih := ih
    · exact Or.inl (ih.trans subset_succChain)
    · exact (h hc₃ ih).imp_left fun (h : c₂ = c₃) => h ▸ Subset.rfl
  | union _ ih =>
    refine or_iff_not_imp_left.2 fun hn => sUnion_subset fun a ha => ?_
    exact (ih a ha).resolve_left fun h => hn <| h.trans <| subset_sUnion_of_mem ha
/-
**chainClosure_succ_total** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma chainClosure_succ_total (hc₁ : ChainClosure r c₁) (hc₂ : ChainClosure r c₂)
    (h : c₁ ⊆ c₂) : c₂ = c₁ ∨ SuccChain r c₁ ⊆ c₂ := by
  induction hc₂ generalizing c₁ hc₁ with
  | succ _ ih =>
    refine ((chainClosure_succ_total_aux hc₁) fun c₁ => ih).imp h.antisymm' fun h₁ => ?_
    obtain rfl | h₂ := ih hc₁ h₁
    · exact Subset.rfl
    · exact h₂.trans subset_succChain
  | union _ ih =>
    apply Or.imp_left h.antisymm'
    apply by_contradiction
    simp only [sUnion_subset_iff, not_or, not_forall, exists_prop, and_imp, forall_exists_index]
    intro c₃ hc₃ h₁ h₂
    obtain h | h := chainClosure_succ_total_aux hc₁ fun c₄ => ih _ hc₃
    · exact h₁ (subset_succChain.trans h)
    obtain h' | h' := ih c₃ hc₃ hc₁ h
    · exact h₁ h'.subset
    · exact h₂ (h'.trans <| subset_sUnion_of_mem hc₃)
/-
**ChainClosure.total** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ChainClosure.total (hc₁ : ChainClosure r c₁) (hc₂ : ChainClosure r c₂) : c
₁ subseteq c₂ ∨ c₂ subseteq c₁
参数：hc₁ : ChainClosure r c₁；hc₂ : ChainClosure r c₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp_left`：∀ {a b c : Prop}, (a → b) → a ∨ c → b ∨ c
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `subset_succChain`：subset_succChain : s subseteq SuccChain r s
· 使用定理 `_private.Mathlib.Order.CompleteLattice.Chain.0.chainClosure_succ_total_a
ux`：∀ {α : Type u_1} {r : α → α → Prop} {c₁ c₂ : Set α},   ChainClosure r c₁ →  
   (∀ ⦃c₃ : Set α⦄, ChainClosure r c₃ → c₃ ⊆ c₂ → c₂ = c₃ ∨ Succ…
· 使用定理 `_private.Mathlib.Order.CompleteLattice.Chain.0.chainClosure_succ_total`：
∀ {α : Type u_1} {r : α → α → Prop} {c₁ c₂ : Set α},   ChainClosure r c₁ → Chain
Closure r c₂ → c₁ ⊆ c₂ → c₂ = c₁ ∨ SuccChain r c₁ ⊆ c₂
-/
lemma ChainClosure.total (hc₁ : ChainClosure r c₁) (hc₂ : ChainClosure r c₂) :
    c₁ ⊆ c₂ ∨ c₂ ⊆ c₁ :=
  ((chainClosure_succ_total_aux hc₂) fun _ hc₃ => chainClosure_succ_total hc₃ hc₁).imp_left
    subset_succChain.trans
/-
**ChainClosure.succ_fixpoint** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ChainClosure.succ_fixpoint (hc₁ : ChainClosure r c₁) (hc₂ : ChainClosure r
 c₂) (hc : SuccChain r c₂ = c₂) : c₁ subseteq c₂
参数：hc₁ : ChainClosure r c₁；hc₂ : ChainClosure r c₂；hc : SuccChain r c₂ = c₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `_private.Mathlib.Order.CompleteLattice.Chain.0.chainClosure_succ_total`：
∀ {α : Type u_1} {r : α → α → Prop} {c₁ c₂ : Set α},   ChainClosure r c₁ → Chain
Closure r c₂ → c₁ ⊆ c₂ → c₂ = c₁ ∨ SuccChain r c₁ ⊆ c₂
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `Set.sUnion_subset`：sUnion_subset {S : Set (Set α)} {t : Set α} (h : fora
ll t' in S, t' subseteq t) : ⋃₀ S subseteq t
-/
lemma ChainClosure.succ_fixpoint (hc₁ : ChainClosure r c₁) (hc₂ : ChainClosure r c₂)
    (hc : SuccChain r c₂ = c₂) : c₁ ⊆ c₂ := by
  induction hc₁ with
  | succ hc₁ h => exact (chainClosure_succ_total hc₁ hc₂ h).elim (fun h => h ▸ hc.subset) id
  | union _ ih => exact sUnion_subset ih
/-
**ChainClosure.succ_fixpoint_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ChainClosure.succ_fixpoint_iff (hc : ChainClosure r c) : SuccChain r c = c
 ↔ c = maxChain r
参数：hc : ChainClosure r c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Set.subset_sUnion_of_mem`：subset_sUnion_of_mem {S : Set (Set α)} {t : Se
t α} (tS : t in S) : t subseteq ⋃₀ S
· 使用引理 `ChainClosure.succ_fixpoint`：ChainClosure.succ_fixpoint (hc₁ : ChainClosu
re r c₁) (hc₂ : ChainClosure r c₂) (hc : SuccChain r c₂ = c₂) : c₁ subseteq c₂
· 使用引理 `chainClosure_maxChain`：chainClosure_maxChain : ChainClosure r (maxChain 
r)
· 使用定理 `LE.le.antisymm'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≤ b → a = b
· 使用定理 `subset_succChain`：subset_succChain : s subseteq SuccChain r s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma ChainClosure.succ_fixpoint_iff (hc : ChainClosure r c) :
    SuccChain r c = c ↔ c = maxChain r :=
  ⟨fun h => (subset_sUnion_of_mem hc).antisymm <| chainClosure_maxChain.succ_fixpoint hc h,
    fun h => subset_succChain.antisymm' <| (subset_sUnion_of_mem hc.succ).trans h.symm.subset⟩
/-
**ChainClosure.isChain** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ChainClosure.isChain (hc : ChainClosure r c) : IsChain r c
参数：hc : ChainClosure r c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsChain.succ`：IsChain.succ (hs : IsChain r s) : IsChain r (SuccChain r s
)
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用引理 `ChainClosure.total`：ChainClosure.total (hc₁ : ChainClosure r c₁) (hc₂ : 
ChainClosure r c₂) : c₁ subseteq c₂ ∨ c₂ subseteq c₁
-/
lemma ChainClosure.isChain (hc : ChainClosure r c) : IsChain r c := by
  induction hc with
  | succ _ h => exact h.succ
  | union hs h =>
    exact fun c₁ ⟨t₁, ht₁, (hc₁ : c₁ ∈ t₁)⟩ c₂ ⟨t₂, ht₂, (hc₂ : c₂ ∈ t₂)⟩ hneq =>
      ((hs _ ht₁).total <| hs _ ht₂).elim (fun ht => h t₂ ht₂ (ht hc₁) hc₂ hneq) fun ht =>
        h t₁ ht₁ hc₁ (ht hc₂) hneq

/-- **Hausdorff's maximality principle**

There exists a maximal totally ordered set of `α`.
Note that we do not require `α` to be partially ordered by `r`. -/
/-
**maxChain_spec** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：maxChain_spec : IsMaxChain r (maxChain r)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `by_contradiction`：by_contradiction {p : Prop} : (¬p -> False) -> p
· 使用定理 `IsChain.superChain_succChain`：IsChain.superChain_succChain (hs₁ : IsChai
n r s) (hs₂ : ¬IsMaxChain r s) : SuperChain r s (SuccChain r s)
· 使用引理 `ChainClosure.isChain`：ChainClosure.isChain (hc : ChainClosure r c) : IsC
hain r c
· 使用引理 `chainClosure_maxChain`：chainClosure_maxChain : ChainClosure r (maxChain 
r)
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `ChainClosure.succ_fixpoint_iff`：ChainClosure.succ_fixpoint_iff (hc : Cha
inClosure r c) : SuccChain r c = c ↔ c = maxChain r

--- 原说明 ---
**Hausdorff's maximality principle**

There exists a maximal totally ordered set of `α`.
Note that we do not require `α` to be partially ordered by `r`.
-/
theorem maxChain_spec : IsMaxChain r (maxChain r) :=
  by_contradiction fun h =>
    let ⟨_, H⟩ := chainClosure_maxChain.isChain.superChain_succChain h
    H.ne (chainClosure_maxChain.succ_fixpoint_iff.mpr rfl).symm
