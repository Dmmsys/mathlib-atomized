/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Bhavik Mehta, Oliver Nash
-/
module

public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.SuccPred
public import Mathlib.Order.Lattice.Nat

/-!
# Order-connected subsets of linear orders

In this file we provide some results about order-connected subsets of linear orders, together with
some convenience lemmas for characterising closed intervals in certain concrete types such as `ℤ`,
`ℕ`, and `Fin n`.

## Main results:
* `Set.ordConnected_iff_disjoint_Ioo_empty`: a characterisation of `Set.OrdConnected` for
  locally-finite linear orders.
* `Set.Nonempty.ordConnected_iff_of_bdd`: a characterisation of closed intervals for locally-finite
  conditionally complete linear orders.
* `Set.Nonempty.ordConnected_iff_of_bdd'`: a characterisation of closed intervals for
  locally-finite complete linear orders (convenient for `Fin n`).
* `Set.Nonempty.eq_Icc_iff_nat`: characterisation of closed intervals for `ℕ`.
* `Set.Nonempty.eq_Icc_iff_int`: characterisation of closed intervals for `ℤ`.
-/

public section

variable {α : Type*} {I : Set α}

/-
**Set.Nonempty.ordConnected_iff_of_bdd** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Set.Nonempty.ordConnected_iff_of_bdd [ConditionallyCompleteLinearOrder α] 
[LocallyFiniteOrder α] (h₀ : I.Nonempty) (h₁ : BddBelow I) (h₂ : BddAbove I) : I
.OrdConnected ↔ I = Icc (sInf I) (sSup I)
参数：h₀ : I.Nonempty；h₁ : BddBelow I；h₂ : BddAbove I。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BddBelow.finite_of_bddAbove`：BddBelow.finite_of_bddAbove [Preorder α] [L
ocallyFiniteOrder α] {s : Set α} (h₀ : BddBelow s) (h₁ : BddAbove s) : s.Finite
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `subset_Icc_csInf_csSup`：subset_Icc_csInf_csSup (hb : BddBelow s) (ha : B
ddAbove s) : s subseteq Icc (sInf s) (sSup s)
· 使用定理 `Set.Icc_subset`：∀ {α : Type u_1} [inst : Preorder α] (s : Set α) [hs : s
.OrdConnected] {x y : α}, x ∈ s → y ∈ s → Set.Icc x y ⊆ s
· 使用定理 `Set.Nonempty.csInf_mem`：Set.Nonempty.csInf_mem (h : s.Nonempty) (hs : s.
Finite) : sInf s in s
· 使用定理 `Set.Nonempty.csSup_mem`：Set.Nonempty.csSup_mem (h : s.Nonempty) (hs : s.
Finite) : sSup s in s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma Set.Nonempty.ordConnected_iff_of_bdd
    [ConditionallyCompleteLinearOrder α] [LocallyFiniteOrder α]
    (h₀ : I.Nonempty) (h₁ : BddBelow I) (h₂ : BddAbove I) :
    I.OrdConnected ↔ I = Icc (sInf I) (sSup I) :=
  have h₄ : I.Finite := h₁.finite_of_bddAbove h₂
  ⟨fun _ ↦ le_antisymm (subset_Icc_csInf_csSup h₁ h₂)
    (I.Icc_subset (h₀.csInf_mem h₄) (h₀.csSup_mem h₄)), fun h₃ ↦ h₃ ▸ ordConnected_Icc⟩

/-- A version of `Set.Nonempty.ordConnected_iff_of_bdd` for complete linear orders, such as `Fin n`,
in which the explicit boundedness hypotheses are not necessary. -/
/-
**Set.Nonempty.ordConnected_iff_of_bdd'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Set.Nonempty.ordConnected_iff_of_bdd' [ConditionallyCompleteLinearOrder α]
 [OrderTop α] [OrderBot α] [LocallyFiniteOrder α] (h₀ : I.Nonempty) : I.OrdConne
cted ↔ I = Icc (sInf I) (sSup I)
参数：h₀ : I.Nonempty。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.Nonempty.ordConnected_iff_of_bdd`：Set.Nonempty.ordConnected_iff_of_b
dd [ConditionallyCompleteLinearOrder α] [LocallyFiniteOrder α] (h₀ : I.Nonempty)
 (h₁ : BddBelow I) (h₂ : B…
· 使用定理 `OrderBot.bddBelow`：∀ {α : Type u_1} [inst : Preorder α] [OrderBot α] (s 
: Set α), BddBelow s
· 使用定理 `OrderTop.bddAbove`：∀ {α : Type u_1} [inst : Preorder α] [OrderTop α] (s 
: Set α), BddAbove s

--- 原说明 ---
A version of `Set.Nonempty.ordConnected_iff_of_bdd` for complete linear orders, 
such as `Fin n`,
in which the explicit boundedness hypotheses are not necessary.
-/
lemma Set.Nonempty.ordConnected_iff_of_bdd' [ConditionallyCompleteLinearOrder α]
    [OrderTop α] [OrderBot α] [LocallyFiniteOrder α]
    (h₀ : I.Nonempty) :
    I.OrdConnected ↔ I = Icc (sInf I) (sSup I) :=
  h₀.ordConnected_iff_of_bdd (OrderBot.bddBelow I) (OrderTop.bddAbove I)

/- TODO The `LocallyFiniteOrder` assumption here is probably too strong (e.g., it rules out `ℝ`
for which this result holds). However at the time of writing it is not clear what weaker
assumption(s) should replace it. -/
/-
**Set.ordConnected_iff_disjoint_Ioo_empty** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Set.ordConnected_iff_disjoint_Ioo_empty [LinearOrder α] [LocallyFiniteOrde
r α] : I.OrdConnected ↔ forallᵉ (x in I) (y in I), Disjoint (Ioo x y) I -> Ioo x
 y = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Set.OrdConnected.out`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α}, 
s.OrdConnected → ∀ ⦃x : α⦄, x ∈ s → ∀ ⦃y : α⦄, y ∈ s → Set.Icc x y ⊆ s
· 使用定理 `Set.mem_Icc_of_Ioo`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x 
∈ Set.Ioo a b → x ∈ Set.Icc a b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `Set.ordConnected_of_Ioo`：ordConnected_of_Ioo {α : Type*} [PartialOrder α
] {s : Set α} (hs : forall x in s, forall y in s, x < y -> Ioo x y subseteq s) :
 OrdConnected…
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Set.Finite.exists_le_maximal`：∀ {α : Type u_2} [inst : Preorder α] {s : 
Set α} {a : α}, s.Finite → a ∈ s → ∃ b, a ≤ b ∧ Maximal (fun x => x ∈ s) b
· 使用定理 `Set.Finite.inter_of_right`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ (t :
 Set α), (t ∩ s).Finite
· 使用引理 `Set.finite_Icc`：finite_Icc : (Icc a b).Finite
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
· 使用定理 `Set.Finite.exists_le_minimal`：∀ {α : Type u_2} [inst : Preorder α] {s : 
Set α} {a : α}, s.Finite → a ∈ s → ∃ b ≤ a, Minimal (fun x => x ∈ s) b
· 使用定理 `lt_of_le_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `Maximal.not_gt`：∀ {α : Type u_2} {P : α → Prop} {x y : α} [inst : Preord
er α], Maximal P x → P y → ¬x < y
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Minimal.not_lt`：Minimal.not_lt (h : Minimal P x) (hy : P y) : ¬(y < x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
TODO The `LocallyFiniteOrder` assumption here is probably too strong (e.g., it r
ules out `ℝ`
for which this result holds). However at the time of writing it is not clear wha
t weaker
assumption(s) should replace it.
-/
lemma Set.ordConnected_iff_disjoint_Ioo_empty [LinearOrder α] [LocallyFiniteOrder α] :
    I.OrdConnected ↔ ∀ᵉ (x ∈ I) (y ∈ I), Disjoint (Ioo x y) I → Ioo x y = ∅ := by
  simp_rw [← Set.subset_compl_iff_disjoint_right]
  refine ⟨fun h' x hx y hy hxy ↦ ?_, fun h' ↦ ordConnected_of_Ioo fun x hx y hy hxy z hz ↦ ?_⟩
  · suffices ∀ z, x < z → y ≤ z by ext z; simpa using this z
    intro z hz
    suffices z ∉ Ioo x y by simp_all
    exact fun contra ↦ hxy contra <| h'.out hx hy <| mem_Icc_of_Ioo contra
  · by_contra hz'
    obtain ⟨x', hx', hx''⟩ :=
      ((finite_Icc x z).inter_of_right I).exists_le_maximal ⟨hx, le_refl _, hz.1.le⟩
    have hxz : x' < z := lt_of_le_of_ne hx''.1.2.2 (ne_of_mem_of_not_mem hx''.1.1 hz')
    obtain ⟨y', hy', hy''⟩ :=
      ((finite_Icc z y).inter_of_right I).exists_le_minimal ⟨hy, hz.2.le, le_refl _⟩
    have hzy : z < y' := lt_of_le_of_ne' hy''.1.2.1 (ne_of_mem_of_not_mem hy''.1.1 hz')
    have h₃ : Ioc x' z ⊆ Iᶜ := fun t ht ht' ↦ hx''.not_gt (⟨ht', le_trans hx' ht.1.le, ht.2⟩) ht.1
    have h₄ : Ico z y' ⊆ Iᶜ := fun t ht ht' ↦ hy''.not_lt (⟨ht', ht.1, le_trans ht.2.le hy'⟩) ht.2
    have h₅ : Ioo x' y' ⊆ Iᶜ := by
      simp only [← Ioc_union_Ico_eq_Ioo hxz hzy, union_subset_iff, and_true, h₃, h₄]
    exact eq_empty_iff_forall_notMem.1 (h' x' hx''.prop.1 y' hy''.prop.1 h₅) z ⟨hxz, hzy⟩
/-
**Set.Nonempty.eq_Icc_iff_nat** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Set.Nonempty.eq_Icc_iff_nat {I : Set Nat} (h₀ : I.Nonempty) (h₂ : BddAbove
 I) : I = Icc (sInf I) (sSup I) ↔ forallᵉ (x in I) (y in I), Disjoint (Ioo x y) 
I -> y <= x + 1
参数：h₀ : I.Nonempty；h₂ : BddAbove I。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.Nonempty.ordConnected_iff_of_bdd`：Set.Nonempty.ordConnected_iff_of_b
dd [ConditionallyCompleteLinearOrder α] [LocallyFiniteOrder α] (h₀ : I.Nonempty)
 (h₁ : BddBelow I) (h₂ : B…
· 使用定理 `OrderBot.bddBelow`：∀ {α : Type u_1} [inst : Preorder α] [OrderBot α] (s 
: Set α), BddBelow s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma Set.Nonempty.eq_Icc_iff_nat {I : Set ℕ}
    (h₀ : I.Nonempty) (h₂ : BddAbove I) :
    I = Icc (sInf I) (sSup I) ↔ ∀ᵉ (x ∈ I) (y ∈ I), Disjoint (Ioo x y) I → y ≤ x + 1 := by
  simp [← h₀.ordConnected_iff_of_bdd (OrderBot.bddBelow I) h₂, ordConnected_iff_disjoint_Ioo_empty]
/-
**Set.Nonempty.eq_Icc_iff_int** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Set.Nonempty.eq_Icc_iff_int {I : Set Int} (h₀ : I.Nonempty) (h₁ : BddBelow
 I) (h₂ : BddAbove I) : I = Icc (sInf I) (sSup I) ↔ forallᵉ (x in I) (y in I), D
isjoint (Ioo x y) I -> y <= x + 1
参数：h₀ : I.Nonempty；h₁ : BddBelow I；h₂ : BddAbove I。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.Nonempty.ordConnected_iff_of_bdd`：Set.Nonempty.ordConnected_iff_of_b
dd [ConditionallyCompleteLinearOrder α] [LocallyFiniteOrder α] (h₀ : I.Nonempty)
 (h₁ : BddBelow I) (h₂ : B…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma Set.Nonempty.eq_Icc_iff_int {I : Set ℤ}
    (h₀ : I.Nonempty) (h₁ : BddBelow I) (h₂ : BddAbove I) :
    I = Icc (sInf I) (sSup I) ↔ ∀ᵉ (x ∈ I) (y ∈ I), Disjoint (Ioo x y) I → y ≤ x + 1 := by
  simp [← h₀.ordConnected_iff_of_bdd h₁ h₂, ordConnected_iff_disjoint_Ioo_empty]
