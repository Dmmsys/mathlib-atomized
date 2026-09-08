/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Vlad Tsyrklevich
-/
module

public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Set.Card

/-!

# Maximal length of chains

This file contains lemmas to work with the maximal lengths of chains of arbitrary relations. See
`Order.height` for a definition specialized to finding the height of an element in a preorder.

## Main definition

- `Set.chainHeight`: The maximal length of a chain in a set `s` with relation `r`.

## Main results

- `Set.exists_isChain_of_le_chainHeight`: For each `n : ℕ` such that `n ≤ s.chainHeight`, there
  exists a subset `t` of length `n` such that `IsChain r t`.
- `Set.chainHeight_mono`: If `s ⊆ t` then `s.chainHeight ≤ t.chainHeight`.
- `Set.chainHeight_eq_of_relEmbedding`: If `f` is an relation embedding, then
  `(f '' s).chainHeight = s.chainHeight`.

-/

@[expose] public section

assert_not_exists Field

namespace Set

open ENat

variable {α β : Type*} (s : Set α) (r : α → α → Prop)

/-- The maximal length of a chain in a set `s` with relation `r`. -/
/-
**Set.chainHeight** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：chainHeight : Nat∞
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The maximal length of a chain in a set `s` with relation `r`.
-/
noncomputable def chainHeight : ℕ∞ := ⨆ t : {t : Set α // t ⊆ s ∧ IsChain r t}, t.val.encard
/-
**Set.chainHeight_eq_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：chainHeight_eq_iSup : s.chainHeight r = ⨆ t : {t : Set α // t subseteq s ∧
 IsChain r t}, t.val.encard
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem chainHeight_eq_iSup :
    s.chainHeight r = ⨆ t : {t : Set α // t ⊆ s ∧ IsChain r t}, t.val.encard := rfl
/-
**Set.chainHeight_le_encard** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：chainHeight_le_encard : s.chainHeight r <= s.encard
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem chainHeight_le_encard : s.chainHeight r ≤ s.encard := by
  simp_all [chainHeight, encard_le_encard]
/-
**Set.chainHeight_ne_top_of_finite** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：chainHeight_ne_top_of_finite (h : s.Finite) : s.chainHeight r != ⊤
参数：h : s.Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne_top`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderTop α] {
a b : α}, a < b → a ≠ ⊤
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Set.chainHeight_le_encard`：chainHeight_le_encard : s.chainHeight r <= s.
encard
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
· 使用定理 `Set.encard_ne_top_iff`：encard_ne_top_iff : s.encard != ⊤ ↔ s.Finite
-/
theorem chainHeight_ne_top_of_finite (h : s.Finite) : s.chainHeight r ≠ ⊤ :=
  LT.lt.ne_top <| lt_of_le_of_lt (chainHeight_le_encard s r) <| lt_top_iff_ne_top.mpr <|
    encard_ne_top_iff.mpr h
/-
**Set.exists_isChain_of_le_chainHeight** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：exists_isChain_of_le_chainHeight {r} {s : Set α} (n : Nat) (h : n <= s.cha
inHeight r) : exists t subseteq s, t.encard = n ∧ IsChain r t
参数：n : Nat；h : n <= s.chainHeight r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.encard_empty`：∀ {α : Type u_1}, ∅.encard = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `iSup_lt_iff`：iSup_lt_iff : iSup f < l ↔ exists b < l, forall i, f i <= b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Nat.sub_one_lt`：∀ {n : ℕ}, n ≠ 0 → n - 1 < n
· 使用定理 `ENat.le_sub_one_of_lt`：∀ {a b : ℕ∞}, a < b → a ≤ b - 1
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.exists_subset_encard_eq`：exists_subset_encard_eq {k : Nat∞} (hk : k 
<= s.encard) : exists t, t subseteq s ∧ t.encard = k
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `IsChain.mono`：IsChain.mono : s subseteq t -> IsChain r t -> IsChain r s
-/
theorem exists_isChain_of_le_chainHeight {r} {s : Set α} (n : ℕ) (h : n ≤ s.chainHeight r) :
    ∃ t ⊆ s, t.encard = n ∧ IsChain r t := by
  by_cases h' : n = 0
  · exact ⟨∅, by simp [h']⟩
  · obtain ⟨t, ht₁, ht₂, ht₃⟩ : ∃ t ⊆ s, IsChain r t ∧ n ≤ t.encard := by
      contrapose! h
      refine iSup_lt_iff.mpr ⟨n - 1, ?_, fun m ↦ ENat.le_sub_one_of_lt <| h m.1 m.2.1 m.2.2⟩
      exact_mod_cast Nat.sub_one_lt h'
    obtain ⟨u, hu₁, hu₂⟩ := exists_subset_encard_eq ht₃
    exact ⟨u, hu₁.trans ht₁, hu₂, ht₂.mono hu₁⟩
/-
**Set.exists_eq_chainHeight_of_chainHeight_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `Set
`。
形式化陈述：exists_eq_chainHeight_of_chainHeight_ne_top (h : s.chainHeight r != ⊤) : e
xists t subseteq s, t.encard = s.chainHeight r ∧ IsChain r t
参数：h : s.chainHeight r != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用引理 `ENat.exists_eq_iSup_of_lt_top`：exists_eq_iSup_of_lt_top [Nonempty ι] (h 
: ⨆ i, f i < ⊤) : exists i, f i = ⨆ i, f i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.chainHeight_eq_iSup`：chainHeight_eq_iSup : s.chainHeight r = ⨆ t : {
t : Set α // t subseteq s ∧ IsChain r t}, t.val.encard
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem exists_eq_chainHeight_of_chainHeight_ne_top (h : s.chainHeight r ≠ ⊤) :
    ∃ t ⊆ s, t.encard = s.chainHeight r ∧ IsChain r t := by
  have : Nonempty { t // t ⊆ s ∧ IsChain r t } := ⟨∅, by simp⟩
  obtain ⟨t, ht⟩ := exists_eq_iSup_of_lt_top (by rwa [← chainHeight_eq_iSup, lt_top_iff_ne_top])
  exact ⟨t.1, t.2.1, ht, t.2.2⟩
/-
**Set.exists_eq_chainHeight_of_finite** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：exists_eq_chainHeight_of_finite (h : s.Finite) : exists t subseteq s, t.en
card = s.chainHeight r ∧ IsChain r t
参数：h : s.Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.exists_eq_chainHeight_of_chainHeight_ne_top`：exists_eq_chainHeight_o
f_chainHeight_ne_top (h : s.chainHeight r != ⊤) : exists t subseteq s, t.encard 
= s.chainHeight r ∧ IsChain r t
· 使用定理 `Set.chainHeight_ne_top_of_finite`：chainHeight_ne_top_of_finite (h : s.Fi
nite) : s.chainHeight r != ⊤
-/
theorem exists_eq_chainHeight_of_finite (h : s.Finite) :
     ∃ t ⊆ s, t.encard = s.chainHeight r ∧ IsChain r t :=
  exists_eq_chainHeight_of_chainHeight_ne_top s r (chainHeight_ne_top_of_finite s r h)
/-
**Set.encard_le_chainHeight_of_isChain** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：encard_le_chainHeight_of_isChain {r} (s t : Set α) (hs : t subseteq s) (hc
 : IsChain r t) : t.encard <= s.chainHeight r
参数：s t : Set α；hs : t subseteq s；hc : IsChain r t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `le_iSup_iff`：le_iSup_iff {s : ι -> α} : a <= iSup s ↔ forall b, (forall 
i, s i <= b) -> a <= b
-/
theorem encard_le_chainHeight_of_isChain {r} (s t : Set α) (hs : t ⊆ s) (hc : IsChain r t) :
    t.encard ≤ s.chainHeight r :=
  le_iSup_iff.mpr fun _ hb ↦ hb ⟨t, hs, hc⟩
/-
**Set.encard_eq_chainHeight_of_isChain** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：encard_eq_chainHeight_of_isChain {r} (s : Set α) (hc : IsChain r s) : s.en
card = s.chainHeight r
参数：s : Set α；hc : IsChain r s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Set.encard_le_chainHeight_of_isChain`：encard_le_chainHeight_of_isChain {
r} (s t : Set α) (hs : t subseteq s) (hc : IsChain r t) : t.encard <= s.chainHei
ght r
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `Set.chainHeight_le_encard`：chainHeight_le_encard : s.chainHeight r <= s.
encard
-/
theorem encard_eq_chainHeight_of_isChain {r} (s : Set α) (hc : IsChain r s) :
    s.encard = s.chainHeight r :=
  le_antisymm (encard_le_chainHeight_of_isChain _ _ Set.Subset.rfl hc) (chainHeight_le_encard _ _)
/-
**Set.finite_of_chainHeight_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：finite_of_chainHeight_ne_top {r} {s : Set α} (hc : IsChain r s) (h : s.cha
inHeight r != ⊤) : s.Finite
参数：hc : IsChain r s；h : s.chainHeight r != ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.encard_ne_top_iff`：encard_ne_top_iff : s.encard != ⊤ ↔ s.Finite
· 使用定理 `ne_top_of_le_ne_top`：ne_top_of_le_ne_top (hb : b != ⊤) (hab : a <= b) : 
a != ⊤
· 使用定理 `Set.encard_le_chainHeight_of_isChain`：encard_le_chainHeight_of_isChain {
r} (s t : Set α) (hs : t subseteq s) (hc : IsChain r t) : t.encard <= s.chainHei
ght r
· 使用定理 `subset_refl`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preord
er α] (a : α), a ⊆ a
-/
theorem finite_of_chainHeight_ne_top {r} {s : Set α} (hc : IsChain r s) (h : s.chainHeight r ≠ ⊤) :
    s.Finite :=
  Set.encard_ne_top_iff.mp <| ne_top_of_le_ne_top h <|
    encard_le_chainHeight_of_isChain _ _ (subset_refl _) hc
/-
**Set.not_isChain_of_chainHeight_lt_encard** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：not_isChain_of_chainHeight_lt_encard (s t : Set α) (ht : t subseteq s) (he
 : s.chainHeight r < t.encard) : ¬ IsChain r t
参数：s t : Set α；ht : t subseteq s；he : s.chainHeight r < t.encard。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `lt_self_iff_false`：lt_self_iff_false (x : α) : x < x ↔ False
· 使用定理 `lt_imp_lt_of_le_of_le`：lt_imp_lt_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a < b -> c < d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Set.encard_le_chainHeight_of_isChain`：encard_le_chainHeight_of_isChain {
r} (s t : Set α) (hs : t subseteq s) (hc : IsChain r t) : t.encard <= s.chainHei
ght r
-/
theorem not_isChain_of_chainHeight_lt_encard (s t : Set α) (ht : t ⊆ s)
    (he : s.chainHeight r < t.encard) : ¬ IsChain r t := by
  by_contra! hh
  grw [encard_le_chainHeight_of_isChain _ _ ht hh] at he
  exact (lt_self_iff_false _).mp he
/-
**Set.chainHeight_eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：chainHeight_eq_top_iff : s.chainHeight r = ⊤ ↔ forall n : Nat, exists t su
bseteq s, t.encard = n ∧ IsChain r t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.exists_isChain_of_le_chainHeight`：exists_isChain_of_le_chainHeight {
r} {s : Set α} (n : Nat) (h : n <= s.chainHeight r) : exists t subseteq s, t.enc
ard = n ∧ IsChain r t
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `ENat.ne_top_iff_exists`：ne_top_iff_exists : n != ⊤ ↔ exists m : Nat, ↑m 
= n
· 使用定理 `Set.not_isChain_of_chainHeight_lt_encard`：not_isChain_of_chainHeight_lt_
encard (s t : Set α) (ht : t subseteq s) (he : s.chainHeight r < t.encard) : ¬ I
sChain r t
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用引理 `lt_add_one`：lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLE
OneClass α] [NeZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
-/
theorem chainHeight_eq_top_iff :
    s.chainHeight r = ⊤ ↔ ∀ n : ℕ, ∃ t ⊆ s, t.encard = n ∧ IsChain r t := by
  refine ⟨fun h _ ↦ exists_isChain_of_le_chainHeight _ (le_top.trans_eq h.symm), fun h ↦ ?_⟩
  contrapose! h
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp h
  refine ⟨n + 1, fun l hl he ↦ not_isChain_of_chainHeight_lt_encard r s l hl ?_⟩
  rw [← hn, he]
  exact_mod_cast lt_add_one _

@[simp]
/-
**Set.chainHeight_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：chainHeight_eq_zero_iff : s.chainHeight r = 0 ↔ s = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem chainHeight_eq_zero_iff : s.chainHeight r = 0 ↔ s = ∅ := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · simp only [chainHeight, iSup_eq_zero, encard_eq_zero, Subtype.forall, and_imp] at h
    ext x
    simpa using h {x}
  · simp_all [chainHeight]

@[simp]
/-
**Set.chainHeight_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：chainHeight_empty : (∅ : Set α).chainHeight r = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.chainHeight_eq_zero_iff`：chainHeight_eq_zero_iff : s.chainHeight r =
 0 ↔ s = ∅
-/
theorem chainHeight_empty : (∅ : Set α).chainHeight r = 0 :=
  chainHeight_eq_zero_iff _ _ |>.mpr rfl

@[simp]
/-
**Set.one_le_chainHeight_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：one_le_chainHeight_iff : 1 <= s.chainHeight r ↔ s.Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.chainHeight_empty`：chainHeight_empty : (∅ : Set α).chainHeight r = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `instNontrivialENat`：Nontrivial ℕ∞
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
-/
theorem one_le_chainHeight_iff : 1 ≤ s.chainHeight r ↔ s.Nonempty := by
  constructor
  all_goals
  · intros
    by_contra! hh
    simp_all

@[simp]
/-
**Set.chainHeight_of_isEmpty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：chainHeight_of_isEmpty [IsEmpty α] : s.chainHeight r = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.chainHeight_eq_zero_iff`：chainHeight_eq_zero_iff : s.chainHeight r =
 0 ↔ s = ∅
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
theorem chainHeight_of_isEmpty [IsEmpty α] : s.chainHeight r = 0 :=
  chainHeight_eq_zero_iff s r |>.mpr (Subsingleton.elim _ _)

@[gcongr, mono]
/-
**Set.chainHeight_mono** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：chainHeight_mono (s t : Set α) (h : s subseteq t) : s.chainHeight r <= t.c
hainHeight r
参数：s t : Set α；h : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `ENat.forall_natCast_le_iff_le`：forall_natCast_le_iff_le : (forall a : Na
t, a <= m -> a <= n) ↔ m <= n
· 使用定理 `Set.exists_isChain_of_le_chainHeight`：exists_isChain_of_le_chainHeight {
r} {s : Set α} (n : Nat) (h : n <= s.chainHeight r) : exists t subseteq s, t.enc
ard = n ∧ IsChain r t
· 使用定理 `Set.encard_le_chainHeight_of_isChain`：encard_le_chainHeight_of_isChain {
r} (s t : Set α) (hs : t subseteq s) (hc : IsChain r t) : t.encard <= s.chainHei
ght r
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
theorem chainHeight_mono (s t : Set α) (h : s ⊆ t) : s.chainHeight r ≤ t.chainHeight r := by
  refine forall_natCast_le_iff_le.mp fun n hn ↦ ?_
  obtain ⟨a, ha₁, ha₂, ha₃⟩ := exists_isChain_of_le_chainHeight n hn
  exact ha₂ ▸ encard_le_chainHeight_of_isChain _ _ (ha₁.trans h) ha₃

@[simp]
/-
**Set.chainHeight_flip** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：chainHeight_flip : s.chainHeight (flip r) = s.chainHeight r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENat.eq_of_forall_natCast_le_iff`：eq_of_forall_natCast_le_iff (hm : fora
ll a : Nat, a <= m ↔ a <= n) : m = n
· 使用定理 `Set.exists_isChain_of_le_chainHeight`：exists_isChain_of_le_chainHeight {
r} {s : Set α} (n : Nat) (h : n <= s.chainHeight r) : exists t subseteq s, t.enc
ard = n ∧ IsChain r t
· 使用定理 `Set.encard_le_chainHeight_of_isChain`：encard_le_chainHeight_of_isChain {
r} (s t : Set α) (hs : t subseteq s) (hc : IsChain r t) : t.encard <= s.chainHei
ght r
-/
theorem chainHeight_flip : s.chainHeight (flip r) = s.chainHeight r := by
  refine eq_of_forall_natCast_le_iff fun n ↦ ⟨fun hn ↦ ?_, fun hn ↦ ?_⟩
  all_goals
  · obtain ⟨a, ha₁, ha₂, ha₃⟩ := exists_isChain_of_le_chainHeight n hn
    exact ha₂ ▸ encard_le_chainHeight_of_isChain _ _ ha₁ <|
      fun _ hx _ hy hne ↦ by simpa [flip, Or.comm] using ha₃ hx hy hne

section Rel

variable {r : α → α → Prop} {r' : β → β → Prop} (s : Set α)

/-
**Set.chainHeight_eq_of_relEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：chainHeight_eq_of_relEmbedding (e : r ↪r r') : (e '' s).chainHeight r' = s
.chainHeight r
参数：e : r ↪r r'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENat.eq_of_forall_natCast_le_iff`：eq_of_forall_natCast_le_iff (hm : fora
ll a : Nat, a <= m ↔ a <= n) : m = n
· 使用定理 `Set.exists_isChain_of_le_chainHeight`：exists_isChain_of_le_chainHeight {
r} {s : Set α} (n : Nat) (h : n <= s.chainHeight r) : exists t subseteq s, t.enc
ard = n ∧ IsChain r t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.encard_preimage_of_injective_subset_range`：encard_preimage_of_inject
ive_subset_range (hf : f.Injective) (ht : t subseteq range f) : (f ⁻¹' t).encard
 = t.encard
· 使用定理 `RelEmbedding.injective`：injective (f : r ↪r s) : Injective f
· 使用定理 `Set.encard_le_chainHeight_of_isChain`：encard_le_chainHeight_of_isChain {
r} (s t : Set α) (hs : t subseteq s) (hc : IsChain r t) : t.encard <= s.chainHei
ght r
· 使用引理 `Set.preimage_subset`：preimage_subset {s t} (hs : s subseteq f '' t) (hf 
: Set.InjOn f (f ⁻¹' s)) : f ⁻¹' s subseteq t
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `IsChain.preimage_relEmbedding`：IsChain.preimage_relEmbedding {t : Set β}
 (ht : IsChain r' t) (φ : r ↪r r') : IsChain r (φ ⁻¹' t)
· 使用定理 `Function.Injective.encard_image`：∀ {α : Type u_1} {β : Type u_2} {f : α 
→ β}, Function.Injective f → ∀ (s : Set α), (f '' s).encard = s.encard
· 使用定理 `IsChain.image`：IsChain.image [FunLike F α β] [RelHomClass F r r'] (hs : 
IsChain r s) (φ : F) : IsChain r' (φ '' s)
· 使用定理 `RelEmbedding.instRelHomClass`：∀ {α : Type u_1} {β : Type u_2} {r : α → α
 → Prop} {s : β → β → Prop}, RelHomClass (r ↪r s) r s
-/
theorem chainHeight_eq_of_relEmbedding (e : r ↪r r') :
    (e '' s).chainHeight r' = s.chainHeight r := by
  refine eq_of_forall_natCast_le_iff fun n ↦ ⟨fun hn ↦ ?_, fun hn ↦ ?_⟩
  · obtain ⟨a, ha₁, ha₂, ha₃⟩ := exists_isChain_of_le_chainHeight n hn
    rw [← ha₂, ← Set.encard_preimage_of_injective_subset_range e.injective (by grind)]
    exact encard_le_chainHeight_of_isChain _ _ (preimage_subset ha₁ e.injective.injOn) <|
      ha₃.preimage_relEmbedding e
  · obtain ⟨a, ha₁, ha₂, ha₃⟩ := exists_isChain_of_le_chainHeight n hn
    rw [← ha₂, ← e.injective.encard_image]
    exact encard_le_chainHeight_of_isChain _ _ (by grind) <| ha₃.image e
/-
**Set.chainHeight_eq_of_relIso** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：chainHeight_eq_of_relIso (e : r ≃r r') : (e '' s).chainHeight r' = s.chain
Height r
参数：e : r ≃r r'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.chainHeight_eq_of_relEmbedding`：chainHeight_eq_of_relEmbedding (e : 
r ↪r r') : (e '' s).chainHeight r' = s.chainHeight r
-/
theorem chainHeight_eq_of_relIso (e : r ≃r r') : (e '' s).chainHeight r' = s.chainHeight r :=
  chainHeight_eq_of_relEmbedding s e.toRelEmbedding

end Rel

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Set.chainHeight_coe_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：chainHeight_coe_univ : (@Set.univ ↑s).chainHeight (r ↑· ↑·) = s.chainHeigh
t r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.chainHeight_eq_of_relEmbedding`：chainHeight_eq_of_relEmbedding (e : 
r ↪r r') : (e '' s).chainHeight r' = s.chainHeight r
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Subtype.relEmbedding_apply`：∀ {X : Type u_5} (r : X → X → Prop) (p : X →
 Prop) (self : Subtype p), (Subtype.relEmbedding r p) self = ↑self
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem chainHeight_coe_univ : (@Set.univ ↑s).chainHeight (r ↑· ↑·) = s.chainHeight r := by
  have hc := Set.chainHeight_eq_of_relEmbedding univ <| Subtype.relEmbedding (r · ·) (· ∈ s)
  have hs : Subtype.val ⁻¹'o (r · ·) = (fun x y : s ↦ r x y) := by funext; simp
  simpa [hs] using hc.symm

@[simp]
/-
**Set.chainHeight_coe_univ_le** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：chainHeight_coe_univ_le [LE α] : (@Set.univ ↑s).chainHeight (· <= ·) = s.c
hainHeight (· <= ·)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.chainHeight_coe_univ`：chainHeight_coe_univ : (@Set.univ ↑s).chainHei
ght (r ↑· ↑·) = s.chainHeight r
-/
theorem chainHeight_coe_univ_le [LE α] :
    (@Set.univ ↑s).chainHeight (· ≤ ·) = s.chainHeight (· ≤ ·) := by
  simpa using chainHeight_coe_univ s (· ≤ ·)

@[simp]
/-
**Set.chainHeight_coe_univ_lt** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：chainHeight_coe_univ_lt [LT α] : (@Set.univ ↑s).chainHeight (· < ·) = s.ch
ainHeight (· < ·)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.chainHeight_coe_univ`：chainHeight_coe_univ : (@Set.univ ↑s).chainHei
ght (r ↑· ↑·) = s.chainHeight r
-/
theorem chainHeight_coe_univ_lt [LT α] :
    (@Set.univ ↑s).chainHeight (· < ·) = s.chainHeight (· < ·) := by
  simpa using chainHeight_coe_univ s (· < ·)

end Set

