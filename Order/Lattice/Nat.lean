/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Floris van Doorn, Gabriel Ebner, Yury Kudryashov
-/
module

public import Mathlib.Order.ConditionallyCompleteLattice.Finset
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Conditionally complete linear order structure on `ℕ`

In this file we

* define a `ConditionallyCompleteLinearOrderBot` structure on `ℕ`;
* prove a few lemmas about `iSup`/`iInf`/`Set.iUnion`/`Set.iInter` and natural numbers.
-/

@[expose] public section

assert_not_exists MonoidWithZero

open Set

namespace Nat

open scoped Classical in
/-
**Nat.** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : InfSet ℕ :=
  ⟨fun s ↦ if h : ∃ n, n ∈ s then @Nat.find (fun n ↦ n ∈ s) _ h else 0⟩

open scoped Classical in
/-
**Nat.** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : SupSet ℕ :=
  ⟨fun s ↦ if h : ∃ n, ∀ a ∈ s, a ≤ n then @Nat.find (fun n ↦ ∀ a ∈ s, a ≤ n) _ h else 0⟩

open scoped Classical in
/-
**Nat.sInf_def** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：sInf_def {s : Set Nat} (h : s.Nonempty) : sInf s = @Nat.find (fun n => n i
n s) _ h
参数：h : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
theorem sInf_def {s : Set ℕ} (h : s.Nonempty) : sInf s = @Nat.find (fun n ↦ n ∈ s) _ h :=
  dif_pos _

open scoped Classical in
/-
**Nat.sSup_def** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：sSup_def {s : Set Nat} (h : exists n, forall a in s, a <= n) : sSup s = @N
at.find (fun n => forall a in s, a <= n) _ h
参数：h : exists n, forall a in s, a <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
theorem sSup_def {s : Set ℕ} (h : ∃ n, ∀ a ∈ s, a ≤ n) :
    sSup s = @Nat.find (fun n ↦ ∀ a ∈ s, a ≤ n) _ h :=
  dif_pos _
/-
**Nat._root_.Set.Infinite.Nat.sSup_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Set.Infinite.Nat.sSup_eq_zero {s : Set ℕ} (h : s.Infinite) : sSup s = 0 :=
  dif_neg fun ⟨n, hn⟩ ↦
    let ⟨k, hks, hk⟩ := h.exists_gt n
    (hn k hks).not_gt hk
/-
**Nat.sSup_of_not_bddAbove** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：sSup_of_not_bddAbove {s : Set Nat} (h : ¬BddAbove s) : sSup s = 0
参数：h : ¬BddAbove s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Infinite.Nat.sSup_eq_zero`：∀ {s : Set ℕ}, s.Infinite → sSup s = 0
· 使用定理 `Set.infinite_of_not_bddAbove`：infinite_of_not_bddAbove : ¬BddAbove s -> 
s.Infinite
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem sSup_of_not_bddAbove {s : Set ℕ} (h : ¬BddAbove s) : sSup s = 0 :=
  Set.Infinite.Nat.sSup_eq_zero <| Set.infinite_of_not_bddAbove h
/-
**Nat.iSup_of_not_bddAbove** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：iSup_of_not_bddAbove {ι : Sort*} {f : ι -> Nat} (h : ¬ BddAbove (Set.range
 f)) : (⨆ i, f i : Nat) = 0
参数：h : ¬ BddAbove (Set.range f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.sSup_of_not_bddAbove`：sSup_of_not_bddAbove {s : Set Nat} (h : ¬BddAb
ove s) : sSup s = 0
-/
lemma iSup_of_not_bddAbove {ι : Sort*} {f : ι → ℕ} (h : ¬ BddAbove (Set.range f)) :
    (⨆ i, f i : ℕ) = 0 := Nat.sSup_of_not_bddAbove h

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**Nat.sInf_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：sInf_eq_zero {s : Set Nat} : sInf s = 0 ↔ 0 in s ∨ s = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `Nat.find.congr_simp`：∀ {p p_1 : ℕ → Prop} (e_p : p = p_1) {inst : Decida
blePred p} [inst_1 : DecidablePred p_1] (H : ∃ n, p n),   Nat.find H = Nat.find 
⋯
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.sInf_def`：sInf_def {s : Set Nat} (h : s.Nonempty) : sInf s = @Nat.fi
nd (fun n => n in s) _ h
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Set.Nonempty.ne_empty`：∀ {α : Type u} {s : Set α}, s.Nonempty → s ≠ ∅
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
-/
theorem sInf_eq_zero {s : Set ℕ} : sInf s = 0 ↔ 0 ∈ s ∨ s = ∅ := by
  cases eq_empty_or_nonempty s with
  | inl h => subst h
             simp only [or_true, InfSet.sInf,
                        mem_empty_iff_false, exists_false, dif_neg, not_false_iff]
  | inr h => simp only [h.ne_empty, or_false, Nat.sInf_def, h, Nat.find_eq_zero]

@[simp]
/-
**Nat.sInf_empty** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：sInf_empty : sInf ∅ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.sInf_eq_zero`：sInf_eq_zero {s : Set Nat} : sInf s = 0 ↔ 0 in s ∨ s =
 ∅
-/
theorem sInf_empty : sInf ∅ = 0 := by
  rw [sInf_eq_zero]
  right
  rfl

@[simp]
/-
**Nat.iInf_of_empty** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：iInf_of_empty {ι : Sort*} [IsEmpty ι] (f : ι -> Nat) : iInf f = 0
参数：f : ι -> Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iInf_of_isEmpty`：∀ {α : Type u_8} {ι : Sort u_9} [inst : InfSet α] [IsEm
pty ι] (f : ι → α), iInf f = sInf ∅
· 使用定理 `Nat.sInf_empty`：sInf_empty : sInf ∅ = 0
-/
theorem iInf_of_empty {ι : Sort*} [IsEmpty ι] (f : ι → ℕ) : iInf f = 0 := by
  rw [iInf_of_isEmpty, sInf_empty]

/-- This combines `Nat.iInf_of_empty` with `ciInf_const`. -/
@[simp]
/-
**Nat.iInf_const_zero** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：iInf_const_zero {ι : Sort*} : ⨅ _ : ι, 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.iInf_of_empty`：iInf_of_empty {ι : Sort*} [IsEmpty ι] (f : ι -> Nat) 
: iInf f = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.sInf_eq_zero`：sInf_eq_zero {s : Set Nat} : sInf s = 0 ↔ 0 in s ∨ s =
 ∅
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.range_const`：range_const : forall [Nonempty ι] {c : α}, (range fun _
 : ι => c) = {c}
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p

--- 原说明 ---
This combines `Nat.iInf_of_empty` with `ciInf_const`.
-/
lemma iInf_const_zero {ι : Sort*} : ⨅ _ : ι, 0 = 0 :=
  (isEmpty_or_nonempty ι).elim (fun h ↦ by simp) fun h ↦ sInf_eq_zero.2 <| by simp
/-
**Nat.sInf_mem** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：sInf_mem {s : Set Nat} (h : s.Nonempty) : sInf s in s
参数：h : s.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.sInf_def`：sInf_def {s : Set Nat} (h : s.Nonempty) : sInf s = @Nat.fi
nd (fun n => n in s) _ h
· 使用定理 `Nat.find_spec`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n),
 p (Nat.find H)
-/
theorem sInf_mem {s : Set ℕ} (h : s.Nonempty) : sInf s ∈ s := by
  classical
  rw [Nat.sInf_def h]
  exact Nat.find_spec h
/-
**Nat.notMem_of_lt_sInf** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：notMem_of_lt_sInf {s : Set Nat} {m : Nat} (hm : m < sInf s) : m ∉ s
参数：hm : m < sInf s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `Set.notMem_empty`：notMem_empty (x : α) : x ∉ (∅ : Set α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.find_min`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n) {
m : ℕ}, m < Nat.find H → ¬p m
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.sInf_def`：sInf_def {s : Set Nat} (h : s.Nonempty) : sInf s = @Nat.fi
nd (fun n => n in s) _ h
-/
theorem notMem_of_lt_sInf {s : Set ℕ} {m : ℕ} (hm : m < sInf s) : m ∉ s := by
  classical
  cases eq_empty_or_nonempty s with
  | inl h => subst h; apply notMem_empty
  | inr h => rw [Nat.sInf_def h] at hm; exact Nat.find_min h hm
/-
**Nat.sInf_le** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {s : Set ℕ} {m : ℕ}, m ∈ s → sInf s ≤ m
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.sInf_def`：sInf_def {s : Set Nat} (h : s.Nonempty) : sInf s = @Nat.fi
nd (fun n => n in s) _ h
· 使用定理 `Nat.find_min'`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n) 
{m : ℕ}, p m → Nat.find H ≤ m
-/
protected theorem sInf_le {s : Set ℕ} {m : ℕ} (hm : m ∈ s) : sInf s ≤ m := by
  classical
  rw [Nat.sInf_def ⟨m, hm⟩]
  exact Nat.find_min' ⟨m, hm⟩ hm
/-
**Nat.nonempty_of_pos_sInf** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：nonempty_of_pos_sInf {s : Set Nat} (h : 0 < sInf s) : s.Nonempty
参数：h : 0 < sInf s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.sInf_eq_zero`：sInf_eq_zero {s : Set Nat} : sInf s = 0 ↔ 0 in s ∨ s =
 ∅
· 使用定理 `Set.not_nonempty_iff_eq_empty`：not_nonempty_iff_eq_empty : ¬s.Nonempty ↔
 s = ∅
-/
theorem nonempty_of_pos_sInf {s : Set ℕ} (h : 0 < sInf s) : s.Nonempty := by
  by_contra contra
  rw [Set.not_nonempty_iff_eq_empty] at contra
  have h' : sInf s ≠ 0 := ne_of_gt h
  apply h'
  rw [Nat.sInf_eq_zero]
  right
  assumption
/-
**Nat.nonempty_of_sInf_eq_succ** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：nonempty_of_sInf_eq_succ {s : Set Nat} {k : Nat} (h : sInf s = k + 1) : s.
Nonempty
参数：h : sInf s = k + 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.nonempty_of_pos_sInf`：nonempty_of_pos_sInf {s : Set Nat} (h : 0 < sI
nf s) : s.Nonempty
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem nonempty_of_sInf_eq_succ {s : Set ℕ} {k : ℕ} (h : sInf s = k + 1) : s.Nonempty :=
  nonempty_of_pos_sInf (h.symm ▸ succ_pos k : sInf s > 0)
/-
**Nat.eq_Ici_of_nonempty_of_upward_closed** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：eq_Ici_of_nonempty_of_upward_closed {s : Set Nat} (hs : s.Nonempty) (hs' :
 forall k₁ k₂ : Nat, k₁ <= k₂ -> k₁ in s -> k₂ in s) : s = Ici (sInf s)
参数：hs : s.Nonempty；hs' : forall k₁ k₂ : Nat, k₁ <= k₂ -> k₁ in s -> k₂ in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Nat.sInf_le`：∀ {s : Set ℕ} {m : ℕ}, m ∈ s → sInf s ≤ m
· 使用定理 `Nat.sInf_mem`：sInf_mem {s : Set Nat} (h : s.Nonempty) : sInf s in s
-/
theorem eq_Ici_of_nonempty_of_upward_closed {s : Set ℕ} (hs : s.Nonempty)
    (hs' : ∀ k₁ k₂ : ℕ, k₁ ≤ k₂ → k₁ ∈ s → k₂ ∈ s) : s = Ici (sInf s) :=
  ext fun n ↦ ⟨fun H ↦ Nat.sInf_le H, fun H ↦ hs' (sInf s) n H (sInf_mem hs)⟩
/-
**Nat.sInf_upward_closed_eq_succ_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：sInf_upward_closed_eq_succ_iff {s : Set Nat} (hs : forall k₁ k₂ : Nat, k₁ 
<= k₂ -> k₁ in s -> k₂ in s) (k : Nat) : sInf s = k + 1 ↔ k + 1 in s ∧ k ∉ s
参数：hs : forall k₁ k₂ : Nat, k₁ <= k₂ -> k₁ in s -> k₂ in s；k : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.eq_Ici_of_nonempty_of_upward_closed`：eq_Ici_of_nonempty_of_upward_cl
osed {s : Set Nat} (hs : s.Nonempty) (hs' : forall k₁ k₂ : Nat, k₁ <= k₂ -> k₁ i
n s -> k₂ in s) : s = Ici (sI…
· 使用定理 `Nat.nonempty_of_sInf_eq_succ`：nonempty_of_sInf_eq_succ {s : Set Nat} {k 
: Nat} (h : sInf s = k + 1) : s.Nonempty
· 使用定理 `Set.mem_Ici`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Ici
 b ↔ b ≤ x
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Nat.not_succ_le_self`：∀ (n : ℕ), ¬n.succ ≤ n
· 使用定理 `Nat.sInf_def`：sInf_def {s : Set Nat} (h : s.Nonempty) : sInf s = @Nat.fi
nd (fun n => n in s) _ h
· 使用引理 `Nat.find_eq_iff`：find_eq_iff (h : exists n : Nat, p n) : Nat.find h = m 
↔ p m ∧ forall n < m, ¬p n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.lt_succ_iff`：∀ {m n : ℕ}, m < n.succ ↔ m ≤ n
-/
theorem sInf_upward_closed_eq_succ_iff {s : Set ℕ} (hs : ∀ k₁ k₂ : ℕ, k₁ ≤ k₂ → k₁ ∈ s → k₂ ∈ s)
    (k : ℕ) : sInf s = k + 1 ↔ k + 1 ∈ s ∧ k ∉ s := by
  classical
  constructor
  · intro H
    rw [eq_Ici_of_nonempty_of_upward_closed (nonempty_of_sInf_eq_succ _) hs, H, mem_Ici, mem_Ici]
    · exact ⟨le_rfl, k.not_succ_le_self⟩
    · exact k
    · assumption
  · rintro ⟨H, H'⟩
    rw [sInf_def (⟨_, H⟩ : s.Nonempty), find_eq_iff]
    exact ⟨H, fun n hnk hns ↦ H' <| hs n k (Nat.lt_succ_iff.mp hnk) hns⟩

/-- This instance is necessary, otherwise the lattice operations would be derived via
`ConditionallyCompleteLinearOrderBot` and marked as noncomputable. -/
/-
**Nat.** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This instance is necessary, otherwise the lattice operations would be derived vi
a
`ConditionallyCompleteLinearOrderBot` and marked as noncomputable.
-/
instance : Lattice ℕ :=
  LinearOrder.toLattice

open scoped Classical in
/-
**Nat.** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : ConditionallyCompleteLinearOrderBot ℕ :=
  { (inferInstance : OrderBot ℕ), (LinearOrder.toLattice : Lattice ℕ),
    (inferInstance : LinearOrder ℕ) with
    isLUB_csSup _ hn hb := sSup_def hb ▸ Nat.isLeast_find hb
    isGLB_csInf _ hn hb := sInf_def hn ▸ (Nat.isLeast_find hn).isGLB
    csSup_empty := by
      simp only [sSup_def, Set.mem_empty_iff_false, forall_const, forall_prop_of_false,
        not_false_iff, exists_const]
      apply bot_unique (Nat.find_min' _ _)
      trivial
    csSup_of_not_bddAbove := by
      intro s hs
      simp only [sSup,
        mem_empty_iff_false, IsEmpty.forall_iff, forall_const, exists_const, dite_true]
      rw [dif_neg]
      · exact le_antisymm (zero_le _) (find_le trivial)
      · exact hs
    csInf_of_not_bddBelow := fun s hs ↦ by simp at hs }
/-
**Nat.sSup_mem** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：sSup_mem {s : Set Nat} (h₁ : s.Nonempty) (h₂ : BddAbove s) : sSup s in s
参数：h₁ : s.Nonempty；h₂ : BddAbove s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.csSup_mem`：Set.Nonempty.csSup_mem (h : s.Nonempty) (hs : s.
Finite) : sSup s in s
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.finite_le_nat`：finite_le_nat (n : Nat) : Set.Finite { i | i <= n }
-/
theorem sSup_mem {s : Set ℕ} (h₁ : s.Nonempty) (h₂ : BddAbove s) : sSup s ∈ s :=
  let ⟨k, hk⟩ := h₂
  h₁.csSup_mem ((finite_le_nat k).subset hk)
/-
**Nat.sInf_add** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：sInf_add {n : Nat} {p : Nat -> Prop} (hn : n <= sInf { m | p m }) : sInf {
 m | p (m + n) } + n = sInf { m | p m }
参数：hn : n <= sInf { m | p m }。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.sInf_empty`：sInf_empty : sInf ∅ = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用定理 `csInf_mem`：csInf_mem (hs : s.Nonempty) : sInf s in s
· 使用定理 `instWellFoundedLTNat`：WellFoundedLT ℕ
· 使用定理 `Nat.nonempty_of_pos_sInf`：nonempty_of_pos_sInf {s : Set Nat} (h : 0 < sI
nf s) : s.Nonempty
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `Nat.sInf_def`：sInf_def {s : Set Nat} (h : s.Nonempty) : sInf s = @Nat.fi
nd (fun n => n in s) _ h
· 使用引理 `Nat.find_add`：find_add {hₘ : exists m, p (m + n)} {hₙ : exists n, p n} (
hn : n <= Nat.find hₙ) : Nat.find hₘ + n = Nat.find hₙ
-/
theorem sInf_add {n : ℕ} {p : ℕ → Prop} (hn : n ≤ sInf { m | p m }) :
    sInf { m | p (m + n) } + n = sInf { m | p m } := by
  classical
  obtain h | ⟨m, hm⟩ := { m | p (m + n) }.eq_empty_or_nonempty
  · rw [h, Nat.sInf_empty, zero_add]
    obtain hnp | hnp := hn.eq_or_lt
    · exact hnp
    suffices hp : p (sInf { m | p m } - n + n) from (h.subset hp).elim
    rw [Nat.sub_add_cancel hn]
    exact csInf_mem (nonempty_of_pos_sInf <| n.zero_le.trans_lt hnp)
  · have hp : ∃ n, n ∈ { m | p m } := ⟨_, hm⟩
    rw [Nat.sInf_def ⟨m, hm⟩, Nat.sInf_def hp]
    rw [Nat.sInf_def hp] at hn
    exact find_add hn
/-
**Nat.sInf_add'** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：sInf_add' {n : Nat} {p : Nat -> Prop} (h : 0 < sInf { m | p m }) : sInf { 
m | p m } + n = sInf { m | p (m - n) }
参数：h : 0 < sInf { m | p m }。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.nonempty_of_pos_sInf`：nonempty_of_pos_sInf {s : Set Nat} (h : 0 < sI
nf s) : s.Nonempty
· 使用定理 `le_csInf`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {s : 
Set α} {a : α}, s.Nonempty → (∀ b ∈ s, a ≤ b) → a ≤ sInf s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.add_sub_cancel_right`：∀ (n m : ℕ), n + m - m = n
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
· 使用定理 `Nat.notMem_of_lt_sInf`：notMem_of_lt_sInf {s : Set Nat} {m : Nat} (hm : m
 < sInf s) : m ∉ s
· 使用定理 `Nat.sub_eq_zero_of_le`：∀ {n m : ℕ}, n ≤ m → n - m = 0
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.sInf_add`：sInf_add {n : Nat} {p : Nat -> Prop} (hn : n <= sInf { m |
 p m }) : sInf { m | p (m + n) } + n = sInf { m | p m }
-/
theorem sInf_add' {n : ℕ} {p : ℕ → Prop} (h : 0 < sInf { m | p m }) :
    sInf { m | p m } + n = sInf { m | p (m - n) } := by
  suffices h₁ : n ≤ sInf {m | p (m - n)} by
    convert! sInf_add h₁
    simp_rw [Nat.add_sub_cancel_right]
  obtain ⟨m, hm⟩ := nonempty_of_pos_sInf h
  refine
    le_csInf ⟨m + n, ?_⟩ fun b hb ↦
      le_of_not_gt fun hbn ↦
        ne_of_mem_of_not_mem ?_ (notMem_of_lt_sInf h) (Nat.sub_eq_zero_of_le hbn.le)
  · dsimp
    rwa [Nat.add_sub_cancel_right]
  · exact hb

section

variable {α : Type*} [CompleteLattice α]

/-
**Nat.iSup_lt_succ** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：iSup_lt_succ (u : Nat -> α) (n : Nat) : ⨆ k < n + 1, u k = (⨆ k < n, u k) 
⊔ u n
参数：u : Nat -> α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `biSup_le_eq_sup`：biSup_le_eq_sup : (⨆ j <= i, f j) = (⨆ j < i, f j) ⊔ f 
i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iSup_lt_succ (u : ℕ → α) (n : ℕ) : ⨆ k < n + 1, u k = (⨆ k < n, u k) ⊔ u n := by
  simp_rw [Nat.lt_add_one_iff, biSup_le_eq_sup]
/-
**Nat.iSup_lt_succ'** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：iSup_lt_succ' (u : Nat -> α) (n : Nat) : ⨆ k < n + 1, u k = u 0 ⊔ ⨆ k < n,
 u (k + 1)
参数：u : Nat -> α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sup_iSup_nat_succ`：sup_iSup_nat_succ (u : Nat -> α) : (u 0 ⊔ ⨆ i, u (i +
 1)) = ⨆ i, u i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iSup_pos`：iSup_pos {p : Prop} {f : p -> α} (hp : p) : ⨆ h : p, f h = f h
p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iSup_lt_succ' (u : ℕ → α) (n : ℕ) : ⨆ k < n + 1, u k = u 0 ⊔ ⨆ k < n, u (k + 1) := by
  rw [← sup_iSup_nat_succ]
  simp
/-
**Nat.iInf_lt_succ** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：iInf_lt_succ (u : Nat -> α) (n : Nat) : ⨅ k < n + 1, u k = (⨅ k < n, u k) 
⊓ u n
参数：u : Nat -> α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.iSup_lt_succ`：iSup_lt_succ (u : Nat -> α) (n : Nat) : ⨆ k < n + 1, u
 k = (⨆ k < n, u k) ⊔ u n
-/
theorem iInf_lt_succ (u : ℕ → α) (n : ℕ) : ⨅ k < n + 1, u k = (⨅ k < n, u k) ⊓ u n :=
  @iSup_lt_succ αᵒᵈ _ _ _
/-
**Nat.iInf_lt_succ'** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：iInf_lt_succ' (u : Nat -> α) (n : Nat) : ⨅ k < n + 1, u k = u 0 ⊓ ⨅ k < n,
 u (k + 1)
参数：u : Nat -> α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.iSup_lt_succ'`：iSup_lt_succ' (u : Nat -> α) (n : Nat) : ⨆ k < n + 1,
 u k = u 0 ⊔ ⨆ k < n, u (k + 1)
-/
theorem iInf_lt_succ' (u : ℕ → α) (n : ℕ) : ⨅ k < n + 1, u k = u 0 ⊓ ⨅ k < n, u (k + 1) :=
  @iSup_lt_succ' αᵒᵈ _ _ _
/-
**Nat.iSup_le_succ** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：iSup_le_succ (u : Nat -> α) (n : Nat) : ⨆ k <= n + 1, u k = (⨆ k <= n, u k
) ⊔ u (n + 1)
参数：u : Nat -> α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.iSup_lt_succ`：iSup_lt_succ (u : Nat -> α) (n : Nat) : ⨆ k < n + 1, u
 k = (⨆ k < n, u k) ⊔ u n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iSup_le_succ (u : ℕ → α) (n : ℕ) : ⨆ k ≤ n + 1, u k = (⨆ k ≤ n, u k) ⊔ u (n + 1) := by
  simp_rw [← Nat.lt_succ_iff, iSup_lt_succ]
/-
**Nat.iSup_le_succ'** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：iSup_le_succ' (u : Nat -> α) (n : Nat) : ⨆ k <= n + 1, u k = u 0 ⊔ ⨆ k <= 
n, u (k + 1)
参数：u : Nat -> α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.iSup_lt_succ'`：iSup_lt_succ' (u : Nat -> α) (n : Nat) : ⨆ k < n + 1,
 u k = u 0 ⊔ ⨆ k < n, u (k + 1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iSup_le_succ' (u : ℕ → α) (n : ℕ) : ⨆ k ≤ n + 1, u k = u 0 ⊔ ⨆ k ≤ n, u (k + 1) := by
  simp_rw [← Nat.lt_succ_iff, iSup_lt_succ']
/-
**Nat.iInf_le_succ** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：iInf_le_succ (u : Nat -> α) (n : Nat) : ⨅ k <= n + 1, u k = (⨅ k <= n, u k
) ⊓ u (n + 1)
参数：u : Nat -> α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.iSup_le_succ`：iSup_le_succ (u : Nat -> α) (n : Nat) : ⨆ k <= n + 1, 
u k = (⨆ k <= n, u k) ⊔ u (n + 1)
-/
theorem iInf_le_succ (u : ℕ → α) (n : ℕ) : ⨅ k ≤ n + 1, u k = (⨅ k ≤ n, u k) ⊓ u (n + 1) :=
  @iSup_le_succ αᵒᵈ _ _ _
/-
**Nat.iInf_le_succ'** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：iInf_le_succ' (u : Nat -> α) (n : Nat) : ⨅ k <= n + 1, u k = u 0 ⊓ ⨅ k <= 
n, u (k + 1)
参数：u : Nat -> α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.iSup_le_succ'`：iSup_le_succ' (u : Nat -> α) (n : Nat) : ⨆ k <= n + 1
, u k = u 0 ⊔ ⨆ k <= n, u (k + 1)
-/
theorem iInf_le_succ' (u : ℕ → α) (n : ℕ) : ⨅ k ≤ n + 1, u k = u 0 ⊓ ⨅ k ≤ n, u (k + 1) :=
  @iSup_le_succ' αᵒᵈ _ _ _

end

end Nat

namespace Set

variable {α : Type*}

/-
**Set.biUnion_lt_succ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：biUnion_lt_succ (u : Nat -> Set α) (n : Nat) : ⋃ k < n + 1, u k = (⋃ k < n
, u k) union u n
参数：u : Nat -> Set α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.iSup_lt_succ`：iSup_lt_succ (u : Nat -> α) (n : Nat) : ⨆ k < n + 1, u
 k = (⨆ k < n, u k) ⊔ u n
-/
theorem biUnion_lt_succ (u : ℕ → Set α) (n : ℕ) : ⋃ k < n + 1, u k = (⋃ k < n, u k) ∪ u n :=
  Nat.iSup_lt_succ u n
/-
**Set.biUnion_lt_succ'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：biUnion_lt_succ' (u : Nat -> Set α) (n : Nat) : ⋃ k < n + 1, u k = u 0 uni
on ⋃ k < n, u (k + 1)
参数：u : Nat -> Set α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.iSup_lt_succ'`：iSup_lt_succ' (u : Nat -> α) (n : Nat) : ⨆ k < n + 1,
 u k = u 0 ⊔ ⨆ k < n, u (k + 1)
-/
theorem biUnion_lt_succ' (u : ℕ → Set α) (n : ℕ) : ⋃ k < n + 1, u k = u 0 ∪ ⋃ k < n, u (k + 1) :=
  Nat.iSup_lt_succ' u n
/-
**Set.biInter_lt_succ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：biInter_lt_succ (u : Nat -> Set α) (n : Nat) : ⋂ k < n + 1, u k = (⋂ k < n
, u k) inter u n
参数：u : Nat -> Set α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.iInf_lt_succ`：iInf_lt_succ (u : Nat -> α) (n : Nat) : ⨅ k < n + 1, u
 k = (⨅ k < n, u k) ⊓ u n
-/
theorem biInter_lt_succ (u : ℕ → Set α) (n : ℕ) : ⋂ k < n + 1, u k = (⋂ k < n, u k) ∩ u n :=
  Nat.iInf_lt_succ u n
/-
**Set.biInter_lt_succ'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：biInter_lt_succ' (u : Nat -> Set α) (n : Nat) : ⋂ k < n + 1, u k = u 0 int
er ⋂ k < n, u (k + 1)
参数：u : Nat -> Set α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.iInf_lt_succ'`：iInf_lt_succ' (u : Nat -> α) (n : Nat) : ⨅ k < n + 1,
 u k = u 0 ⊓ ⨅ k < n, u (k + 1)
-/
theorem biInter_lt_succ' (u : ℕ → Set α) (n : ℕ) : ⋂ k < n + 1, u k = u 0 ∩ ⋂ k < n, u (k + 1) :=
  Nat.iInf_lt_succ' u n
/-
**Set.biUnion_le_succ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：biUnion_le_succ (u : Nat -> Set α) (n : Nat) : ⋃ k <= n + 1, u k = (⋃ k <=
 n, u k) union u (n + 1)
参数：u : Nat -> Set α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.iSup_le_succ`：iSup_le_succ (u : Nat -> α) (n : Nat) : ⨆ k <= n + 1, 
u k = (⨆ k <= n, u k) ⊔ u (n + 1)
-/
theorem biUnion_le_succ (u : ℕ → Set α) (n : ℕ) : ⋃ k ≤ n + 1, u k = (⋃ k ≤ n, u k) ∪ u (n + 1) :=
  Nat.iSup_le_succ u n
/-
**Set.biUnion_le_succ'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：biUnion_le_succ' (u : Nat -> Set α) (n : Nat) : ⋃ k <= n + 1, u k = u 0 un
ion ⋃ k <= n, u (k + 1)
参数：u : Nat -> Set α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.iSup_le_succ'`：iSup_le_succ' (u : Nat -> α) (n : Nat) : ⨆ k <= n + 1
, u k = u 0 ⊔ ⨆ k <= n, u (k + 1)
-/
theorem biUnion_le_succ' (u : ℕ → Set α) (n : ℕ) : ⋃ k ≤ n + 1, u k = u 0 ∪ ⋃ k ≤ n, u (k + 1) :=
  Nat.iSup_le_succ' u n
/-
**Set.biInter_le_succ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：biInter_le_succ (u : Nat -> Set α) (n : Nat) : ⋂ k <= n + 1, u k = (⋂ k <=
 n, u k) inter u (n + 1)
参数：u : Nat -> Set α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.iInf_le_succ`：iInf_le_succ (u : Nat -> α) (n : Nat) : ⨅ k <= n + 1, 
u k = (⨅ k <= n, u k) ⊓ u (n + 1)
-/
theorem biInter_le_succ (u : ℕ → Set α) (n : ℕ) : ⋂ k ≤ n + 1, u k = (⋂ k ≤ n, u k) ∩ u (n + 1) :=
  Nat.iInf_le_succ u n
/-
**Set.biInter_le_succ'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：biInter_le_succ' (u : Nat -> Set α) (n : Nat) : ⋂ k <= n + 1, u k = u 0 in
ter ⋂ k <= n, u (k + 1)
参数：u : Nat -> Set α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.iInf_le_succ'`：iInf_le_succ' (u : Nat -> α) (n : Nat) : ⨅ k <= n + 1
, u k = u 0 ⊓ ⨅ k <= n, u (k + 1)
-/
theorem biInter_le_succ' (u : ℕ → Set α) (n : ℕ) : ⋂ k ≤ n + 1, u k = u 0 ∩ ⋂ k ≤ n, u (k + 1) :=
  Nat.iInf_le_succ' u n

end Set

