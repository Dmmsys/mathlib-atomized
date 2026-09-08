/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Bhavik Mehta
-/
module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.ENat.Basic
public import Mathlib.Order.Lattice.Nat

/-!
# Extended natural numbers form a complete linear order

This instance is not in `Data.ENat.Basic` to avoid dependency on `Finset`s.

We also restate some lemmas about `WithTop` for `ENat` to have versions that use `Nat.cast` instead
of `WithTop.some`.

-/

public section

assert_not_exists Field

open Set

noncomputable section
deriving instance CompleteLinearOrder for ℕ∞
end

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : CompleteLinearOrder (WithBot ENat) :=
  inferInstanceAs (CompleteLinearOrder (WithBot (WithTop ℕ)))

namespace ENat
variable {ι : Sort*} {f : ι → ℕ} {s : Set ℕ}

/-
**ENat.iSup_natCast_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：iSup_natCast_eq_top : ⨆ i, (f i : Nat∞) = ⊤ ↔ ¬ BddAbove (range f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithTop.iSup_coe_eq_top`：iSup_coe_eq_top : ⨆ x, (f x : WithTop α) = ⊤ ↔ 
¬BddAbove (range f)
-/
lemma iSup_natCast_eq_top : ⨆ i, (f i : ℕ∞) = ⊤ ↔ ¬ BddAbove (range f) := WithTop.iSup_coe_eq_top
/-
**ENat.iSup_natCast_ne_top** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：iSup_natCast_ne_top : ⨆ i, (f i : Nat∞) != ⊤ ↔ BddAbove (range f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not_left`：Iff.not_left (h : a ↔ ¬b) : ¬a ↔ b
· 使用引理 `ENat.iSup_natCast_eq_top`：iSup_natCast_eq_top : ⨆ i, (f i : Nat∞) = ⊤ ↔ 
¬ BddAbove (range f)
-/
lemma iSup_natCast_ne_top : ⨆ i, (f i : ℕ∞) ≠ ⊤ ↔ BddAbove (range f) := iSup_natCast_eq_top.not_left
/-
**ENat.iSup_natCast_lt_top** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：iSup_natCast_lt_top : ⨆ i, (f i : Nat∞) < ⊤ ↔ BddAbove (range f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithTop.iSup_coe_lt_top`：iSup_coe_lt_top : ⨆ x, (f x : WithTop α) < ⊤ ↔ 
BddAbove (range f)
-/
lemma iSup_natCast_lt_top : ⨆ i, (f i : ℕ∞) < ⊤ ↔ BddAbove (range f) := WithTop.iSup_coe_lt_top
/-
**ENat.iInf_natCast_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：iInf_natCast_eq_top : ⨅ i, (f i : Nat∞) = ⊤ ↔ IsEmpty ι
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithTop.iInf_coe_eq_top`：iInf_coe_eq_top : ⨅ x, (f x : WithTop α) = ⊤ ↔ 
IsEmpty ι
-/
lemma iInf_natCast_eq_top : ⨅ i, (f i : ℕ∞) = ⊤ ↔ IsEmpty ι := WithTop.iInf_coe_eq_top
/-
**ENat.iInf_natCast_ne_top** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：iInf_natCast_ne_top : ⨅ i, (f i : Nat∞) != ⊤ ↔ Nonempty ι
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用引理 `ENat.iInf_natCast_eq_top`：iInf_natCast_eq_top : ⨅ i, (f i : Nat∞) = ⊤ ↔ 
IsEmpty ι
· 使用定理 `not_isEmpty_iff`：not_isEmpty_iff : ¬IsEmpty α ↔ Nonempty α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma iInf_natCast_ne_top : ⨅ i, (f i : ℕ∞) ≠ ⊤ ↔ Nonempty ι := by
  rw [Ne, iInf_natCast_eq_top, not_isEmpty_iff]
/-
**ENat.iInf_natCast_lt_top** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：iInf_natCast_lt_top : ⨅ i, (f i : Nat∞) < ⊤ ↔ Nonempty ι
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithTop.iInf_coe_lt_top`：iInf_coe_lt_top : ⨅ i, (f i : WithTop α) < ⊤ ↔ 
Nonempty ι
-/
lemma iInf_natCast_lt_top : ⨅ i, (f i : ℕ∞) < ⊤ ↔ Nonempty ι := WithTop.iInf_coe_lt_top

@[deprecated (since := "2026-07-17")] alias iSup_coe_eq_top := iSup_natCast_eq_top
@[deprecated (since := "2026-07-17")] alias iSup_coe_ne_top := iSup_natCast_ne_top
@[deprecated (since := "2026-07-17")] alias iSup_coe_lt_top := iSup_natCast_lt_top
@[deprecated (since := "2026-07-17")] alias iInf_coe_eq_top := iInf_natCast_eq_top
@[deprecated (since := "2026-07-17")] alias iInf_coe_ne_top := iInf_natCast_ne_top
@[deprecated (since := "2026-07-17")] alias iInf_coe_lt_top := iInf_natCast_lt_top
/-
**ENat.natCast_sSup** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：natCast_sSup : BddAbove s -> ↑(sSup s) = ⨆ a in s, (a : Nat∞)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.coe_sSup`：coe_sSup {s : Set α} (hb : BddAbove s) : ↑(sSup s) = (
⨆ a in s, ↑a : WithTop α)
-/
lemma natCast_sSup : BddAbove s → ↑(sSup s) = ⨆ a ∈ s, (a : ℕ∞) := WithTop.coe_sSup

@[deprecated (since := "2026-07-17")] alias coe_sSup := natCast_sSup
/-
**ENat.natCast_sInf** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：natCast_sInf (hs : s.Nonempty) : ↑(sInf s) = ⨅ a in s, (a : Nat∞)
参数：hs : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.coe_sInf`：coe_sInf {s : Set α} (hs : s.Nonempty) (h's : BddBelow
 s) : ↑(sInf s) = (⨅ a in s, ↑a : WithTop α)
· 使用定理 `OrderBot.bddBelow`：∀ {α : Type u_1} [inst : Preorder α] [OrderBot α] (s 
: Set α), BddBelow s
-/
lemma natCast_sInf (hs : s.Nonempty) : ↑(sInf s) = ⨅ a ∈ s, (a : ℕ∞) :=
  WithTop.coe_sInf hs (OrderBot.bddBelow s)

@[deprecated (since := "2026-07-17")] alias coe_sInf := natCast_sInf
/-
**ENat.natCast_iSup** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：natCast_iSup : BddAbove (range f) -> ↑(⨆ i, f i) = ⨆ i, (f i : Nat∞)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.coe_iSup`：WithTop.coe_iSup [SupSet α] (f : ι -> α) (h : BddAbove
 (Set.range f)) : ↑(⨆ i, f i) = (⨆ i, f i : WithTop α)
-/
lemma natCast_iSup : BddAbove (range f) → ↑(⨆ i, f i) = ⨆ i, (f i : ℕ∞) := WithTop.coe_iSup _

@[deprecated (since := "2026-07-17")] alias coe_iSup := natCast_iSup
/-
**ENat.natCast_iInf** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ {ι : Sort u_1} {f : ι → ℕ} [Nonempty ι], ↑(⨅ i, f i) = ⨅ i, ↑(f i)
参数：⨅ i, f i；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.coe_iInf`：WithTop.coe_iInf [Nonempty ι] [InfSet α] {f : ι -> α} 
(hf : BddBelow (range f)) : ↑(⨅ i, f i) = (⨅ i, f i : WithTop α)
· 使用定理 `OrderBot.bddBelow`：∀ {α : Type u_1} [inst : Preorder α] [OrderBot α] (s 
: Set α), BddBelow s
-/
@[norm_cast] lemma natCast_iInf [Nonempty ι] : ↑(⨅ i, f i) = ⨅ i, (f i : ℕ∞) :=
  WithTop.coe_iInf (OrderBot.bddBelow _)

@[deprecated (since := "2026-07-17")] alias coe_iInf := natCast_iInf

@[simp]
/-
**ENat.iInf_eq_top_of_isEmpty** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：iInf_eq_top_of_isEmpty [IsEmpty ι] : ⨅ i, (f i : Nat∞) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `ENat.iInf_natCast_eq_top`：iInf_natCast_eq_top : ⨅ i, (f i : Nat∞) = ⊤ ↔ 
IsEmpty ι
-/
lemma iInf_eq_top_of_isEmpty [IsEmpty ι] : ⨅ i, (f i : ℕ∞) = ⊤ :=
  iInf_natCast_eq_top.mpr ‹_›
/-
**ENat.iInf_eq_natCast_iff** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：iInf_eq_natCast_iff {f : ι -> Nat∞} {n : Nat} : ⨅ i, f i = n ↔ (exists i, 
f i = n) ∧ forall i, n <= f i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iInf_of_isEmpty`：∀ {α : Type u_8} {ι : Sort u_9} [inst : InfSet α] [IsEm
pty ι] (f : ι → α), iInf f = sInf ∅
· 使用定理 `sInf_empty`：∀ {α : Type u_1} [inst : CompleteLattice α], sInf ∅ = ⊤
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用引理 `ciInf_eq_iff`：ciInf_eq_iff [Nonempty ι] (f : ι -> α) (n : α) : ⨅ i, (f i
) = n ↔ (exists i, f i = n) ∧ forall i, n <= f i
· 使用定理 `instWellFoundedLTENat`：WellFoundedLT ℕ∞
-/
lemma iInf_eq_natCast_iff {f : ι → ℕ∞} {n : ℕ} :
    ⨅ i, f i = n ↔ (∃ i, f i = n) ∧ ∀ i, n ≤ f i := by
  by_cases! hι : IsEmpty ι
  · simp [iInf_of_isEmpty]
  apply ciInf_eq_iff

@[deprecated (since := "2026-07-17")] alias iInf_eq_coe_iff := iInf_eq_natCast_iff
/-
**ENat.iInf_toNat** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：iInf_toNat : (⨅ i, (f i : Nat∞)).toNat = ⨅ i, f i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ENat.iInf_eq_top_of_isEmpty`：iInf_eq_top_of_isEmpty [IsEmpty ι] : ⨅ i, (
f i : Nat∞) = ⊤
· 使用定理 `Nat.iInf_of_empty`：iInf_of_empty {ι : Sort*} [IsEmpty ι] (f : ι -> Nat) 
: iInf f = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
lemma iInf_toNat : (⨅ i, (f i : ℕ∞)).toNat = ⨅ i, f i := by
  cases isEmpty_or_nonempty ι
  · simp
  · norm_cast
/-
**ENat.iInf_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ {ι : Sort u_1} {f : ι → ℕ∞}, ⨅ i, f i = 0 ↔ ∃ i, f i = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `instNontrivialENat`：Nontrivial ℕ∞
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_lt_iff`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLinearOrder
 α] {a : α} {f : ι → α}, iInf f < a ↔ ∃ i, f i < a
-/
@[simp] lemma iInf_eq_zero {f : ι → ℕ∞} : ⨅ i, f i = 0 ↔ ∃ i, f i = 0 := by
  simpa [Order.lt_one_iff] using iInf_lt_iff (α := ℕ∞) (a := 1)

variable {f : ι → ℕ∞} {s : Set ℕ∞}
/-
**ENat.sSup_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：sSup_eq_zero : sSup s = 0 ↔ forall a in s, a = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sSup_eq_bot`：sSup_eq_bot : sSup s = ⊥ ↔ forall a in s, a = ⊥
-/
lemma sSup_eq_zero : sSup s = 0 ↔ ∀ a ∈ s, a = 0 :=
  sSup_eq_bot
/-
**ENat.sInf_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：sInf_eq_zero : sInf s = 0 ↔ 0 in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.lt_one_iff`：lt_one_iff : x < 1 ↔ x = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `instNontrivialENat`：Nontrivial ℕ∞
· 使用定理 `sInf_lt_iff`：∀ {α : Type u_1} [inst : CompleteLinearOrder α] {s : Set α}
 {b : α}, sInf s < b ↔ ∃ a ∈ s, a < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma sInf_eq_zero : sInf s = 0 ↔ 0 ∈ s := by
  rw [← Order.lt_one_iff, sInf_lt_iff]
  simp
/-
**ENat.sSup_eq_zero'** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：sSup_eq_zero' : sSup s = 0 ↔ s = ∅ ∨ s = {0}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `sSup_eq_bot'`：sSup_eq_bot' {s : Set α} : sSup s = ⊥ ↔ s = ∅ ∨ s = {⊥}
-/
lemma sSup_eq_zero' : sSup s = 0 ↔ s = ∅ ∨ s = {0} :=
  sSup_eq_bot'
/-
**ENat.iSup_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ {ι : Sort u_1} {f : ι → ℕ∞}, iSup f = 0 ↔ ∀ (i : ι), f i = 0
参数：i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_eq_bot`：iSup_eq_bot : iSup s = ⊥ ↔ forall i, s i = ⊥
-/
@[simp] lemma iSup_eq_zero : iSup f = 0 ↔ ∀ i, f i = 0 := iSup_eq_bot
/-
**ENat.iSup_zero** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ {ι : Sort u_1}, ⨆ x, 0 = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] lemma iSup_zero : ⨆ _ : ι, (0 : ℕ∞) = 0 := by simp
/-
**ENat.sSup_eq_top_of_infinite** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：sSup_eq_top_of_infinite (h : s.Infinite) : sSup s = ⊤
参数：h : s.Infinite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sSup_eq_top`：sSup_eq_top : sSup s = ⊤ ↔ forall b < ⊤, exists a in s, b <
 a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `ENat.toNat_le_of_le_natCast`：toNat_le_of_le_natCast {m : Nat∞} {n : Nat}
 (h : m <= n) : toNat m <= n
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne_top`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderTop α] {
a b : α}, a < b → a ≠ ⊤
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma sSup_eq_top_of_infinite (h : s.Infinite) : sSup s = ⊤ := by
  apply (sSup_eq_top ..).mpr
  intro x hx
  cases x with
  | top => simp at hx
  | coe x =>
    contrapose! h
    apply Finite.subset <| Finite.Set.finite_image {n : ℕ | n ≤ x} (fun (n : ℕ) => (n : ℕ∞))
    intro y hy
    specialize h y hy
    have hxt : y < ⊤ := lt_of_le_of_lt h hx
    use y.toNat
    simp [toNat_le_of_le_natCast h, LT.lt.ne_top hxt]
/-
**ENat.finite_of_sSup_lt_top** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：finite_of_sSup_lt_top (h : sSup s < ⊤) : s.Finite
参数：h : sSup s < ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `ENat.sSup_eq_top_of_infinite`：sSup_eq_top_of_infinite (h : s.Infinite) :
 sSup s = ⊤
-/
lemma finite_of_sSup_lt_top (h : sSup s < ⊤) : s.Finite := by
  contrapose! h
  simp only [top_le_iff]
  exact sSup_eq_top_of_infinite h
/-
**ENat.sSup_mem_of_nonempty_of_lt_top** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：sSup_mem_of_nonempty_of_lt_top [Nonempty s] (hs' : sSup s < ⊤) : sSup s in
 s
参数：hs' : sSup s < ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.csSup_mem`：Set.Nonempty.csSup_mem (h : s.Nonempty) (hs : s.
Finite) : sSup s in s
· 使用定理 `Set.Nonempty.of_subtype`：∀ {α : Type u} {s : Set α} [Nonempty ↑s], s.Non
empty
· 使用引理 `ENat.finite_of_sSup_lt_top`：finite_of_sSup_lt_top (h : sSup s < ⊤) : s.F
inite
-/
lemma sSup_mem_of_nonempty_of_lt_top [Nonempty s] (hs' : sSup s < ⊤) : sSup s ∈ s :=
  Nonempty.csSup_mem .of_subtype (finite_of_sSup_lt_top hs')
/-
**ENat.exists_eq_iSup_of_lt_top** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：exists_eq_iSup_of_lt_top [Nonempty ι] (h : ⨆ i, f i < ⊤) : exists i, f i =
 ⨆ i, f i
参数：h : ⨆ i, f i < ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENat.sSup_mem_of_nonempty_of_lt_top`：sSup_mem_of_nonempty_of_lt_top [Non
empty s] (hs' : sSup s < ⊤) : sSup s in s
-/
lemma exists_eq_iSup_of_lt_top [Nonempty ι] (h : ⨆ i, f i < ⊤) :
    ∃ i, f i = ⨆ i, f i :=
  sSup_mem_of_nonempty_of_lt_top h
/-
**ENat.exists_eq_iInf** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：exists_eq_iInf [Nonempty ι] (f : ι -> Nat∞) : exists a, f a = ⨅ x, f x
参数：f : ι -> Nat∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `csInf_mem`：csInf_mem (hs : s.Nonempty) : sInf s in s
· 使用定理 `instWellFoundedLTENat`：WellFoundedLT ℕ∞
· 使用定理 `Set.range_nonempty`：range_nonempty [h : Nonempty ι] (f : ι -> α) : (rang
e f).Nonempty
-/
lemma exists_eq_iInf [Nonempty ι] (f : ι → ℕ∞) : ∃ a, f a = ⨅ x, f x :=
  csInf_mem (range_nonempty fun i ↦ f i)
/-
**ENat.exists_eq_iSup** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma exists_eq_iSup₂_of_lt_top {ι₁ ι₂ : Type*} {f : ι₁ → ι₂ → ℕ∞} [Nonempty ι₁] [Nonempty ι₂]
    (h : ⨆ i, ⨆ j, f i j < ⊤) : ∃ i j, f i j = ⨆ i, ⨆ j, f i j := by
  rw [iSup_prod'] at h ⊢
  exact Prod.exists'.mp (exists_eq_iSup_of_lt_top h)

variable {ι κ : Sort*} {f g : ι → ℕ∞} {s : Set ℕ∞} {a : ℕ∞}
/-
**ENat.iSup_natCast** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：iSup_natCast : ⨆ n : Nat, (n : Nat∞) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `iSup_eq_top`：iSup_eq_top : iSup f = ⊤ ↔ forall b < ⊤, exists i, b < f i
· 使用定理 `ENat.exists_nat_gt`：∀ {n : ℕ∞}, n ≠ ⊤ → ∃ m, n < ↑m
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
-/
lemma iSup_natCast : ⨆ n : ℕ, (n : ℕ∞) = ⊤ :=
  iSup_eq_top.2 fun _b hb ↦ ENat.exists_nat_gt (lt_top_iff_ne_top.1 hb)
/-
**ENat.mul_iSup** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：mul_iSup (a : Nat∞) (f : ι -> Nat∞) : a * ⨆ i, f i = ⨆ i, a * f i
参数：a : Nat∞；f : ι -> Nat∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≤ b → a = b
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `CanonicallyOrderedAdd.toMulLeftMono`：∀ {R : Type u} [inst : NonUnitalNon
AssocSemiring R] [inst_1 : LE R] [CanonicallyOrderedAdd R], MulLeftMono R
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `le_iSup_iff`：le_iSup_iff {s : ι -> α} : a <= iSup s ↔ forall b, (forall 
i, s i <= b) -> a <= b
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `ciSup_of_empty`：ciSup_of_empty [IsEmpty ι] (f : ι -> α) : ⨆ i, f i = ⊥
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `iSup_eq_top`：iSup_eq_top : iSup f = ⊤ ↔ forall b < ⊤, exists i, b < f i
· 使用定理 `LT.lt.false`：∀ {α : Type u_2} [inst : Preorder α] {a : α}, a < a → False
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用引理 `ENat.self_le_mul_left`：self_le_mul_left (a : Nat∞) (hc : c != 0) : a <= 
c * a
· 使用引理 `ENat.exists_eq_iSup_of_lt_top`：exists_eq_iSup_of_lt_top [Nonempty ι] (h 
: ⨆ i, f i < ⊤) : exists i, f i = ⨆ i, f i
-/
lemma mul_iSup (a : ℕ∞) (f : ι → ℕ∞) : a * ⨆ i, f i = ⨆ i, a * f i := by
  refine (iSup_le fun i ↦ mul_le_mul' rfl.le <| le_iSup_iff.2 fun _ a ↦ a i).antisymm' <|
    le_iSup_iff.2 fun d h ↦ ?_
  obtain rfl | hne := eq_or_ne a 0
  · simp
  obtain hι | hι := isEmpty_or_nonempty ι
  · simp
  cases d with
  | top => simp
  | coe d =>
  have hlt : ⨆ i, f i < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    obtain ⟨i, hi : d < f i⟩ := (iSup_eq_top ..).1 htop d (by simp)
    exact (((h i).trans_lt hi).trans_le (ENat.self_le_mul_left _ hne)).false
  obtain ⟨j, hj⟩ := exists_eq_iSup_of_lt_top hlt
  rw [← hj]
  apply h
/-
**ENat.iSup_mul** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：iSup_mul (f : ι -> Nat∞) (a : Nat∞) : (⨆ i, f i) * a = ⨆ i, f i * a
参数：f : ι -> Nat∞；a : Nat∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `ENat.mul_iSup`：mul_iSup (a : Nat∞) (f : ι -> Nat∞) : a * ⨆ i, f i = ⨆ i,
 a * f i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma iSup_mul (f : ι → ℕ∞) (a : ℕ∞) : (⨆ i, f i) * a = ⨆ i, f i * a := by
  simp_rw [mul_comm, ENat.mul_iSup]
/-
**ENat.mul_sSup** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：mul_sSup : a * sSup s = ⨆ b in s, a * b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sSup_eq_iSup`：sSup_eq_iSup {s : Set α} : sSup s = ⨆ a in s, a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `ENat.mul_iSup`：mul_iSup (a : Nat∞) (f : ι -> Nat∞) : a * ⨆ i, f i = ⨆ i,
 a * f i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mul_sSup : a * sSup s = ⨆ b ∈ s, a * b := by
  simp_rw [sSup_eq_iSup, mul_iSup]
/-
**ENat.sSup_mul** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：sSup_mul : sSup s * a = ⨆ b in s, b * a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `ENat.mul_sSup`：mul_sSup : a * sSup s = ⨆ b in s, a * b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sSup_mul : sSup s * a = ⨆ b ∈ s, b * a := by
  simp_rw [mul_comm, mul_sSup]
/-
**ENat.mul_iInf** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：mul_iInf [Nonempty ι] : a * ⨅ i, f i = ⨅ i, a * f i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `le_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f :
 ι → α} {a : α}, (∀ (i : ι), a ≤ f i) → a ≤ iInf f
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `CanonicallyOrderedAdd.toMulLeftMono`：∀ {R : Type u} [inst : NonUnitalNon
AssocSemiring R] [inst_1 : LE R] [CanonicallyOrderedAdd R], MulLeftMono R
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `iInf_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] (f :
 ι → α) (i : ι), iInf f ≤ f i
· 使用引理 `ENat.exists_eq_iInf`：exists_eq_iInf [Nonempty ι] (f : ι -> Nat∞) : exist
s a, f a = ⨅ x, f x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iInf_le_iff`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteSemilattice
Inf α] {a : α} {s : ι → α},   iInf s ≤ a ↔ ∀ (b : α), (∀ (i : ι), b ≤ s i) → b ≤
 …
-/
lemma mul_iInf [Nonempty ι] : a * ⨅ i, f i = ⨅ i, a * f i := by
  refine (le_iInf fun x ↦ by grw [iInf_le]).antisymm ?_
  obtain ⟨b, hb⟩ := ENat.exists_eq_iInf f
  rw [← hb, iInf_le_iff]
  exact fun x h ↦ h _
/-
**ENat.iInf_mul** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：iInf_mul [Nonempty ι] : (⨅ i, f i) * a = ⨅ i, f i * a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `ENat.mul_iInf`：mul_iInf [Nonempty ι] : a * ⨅ i, f i = ⨅ i, a * f i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma iInf_mul [Nonempty ι] : (⨅ i, f i) * a = ⨅ i, f i * a := by
  simp_rw [mul_comm, mul_iInf]

/-- A version of `mul_iInf` with a slightly more general hypothesis. -/
/-
**ENat.mul_iInf'** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：mul_iInf' (h₀ : a = 0 -> Nonempty ι) : a * ⨅ i, f i = ⨅ i, a * f i
参数：h₀ : a = 0 -> Nonempty ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iInf_of_empty`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α
] [IsEmpty ι] (f : ι → α), iInf f = ⊤
· 使用定理 `ENat.mul_top'`：mul_top' : m * ⊤ = if m = 0 then 0 else ⊤
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `ENat.mul_iInf`：mul_iInf [Nonempty ι] : a * ⨅ i, f i = ⨅ i, a * f i

--- 原说明 ---
A version of `mul_iInf` with a slightly more general hypothesis.
-/
lemma mul_iInf' (h₀ : a = 0 → Nonempty ι) : a * ⨅ i, f i = ⨅ i, a * f i := by
  obtain hι | hι := isEmpty_or_nonempty ι
  · suffices a ≠ 0 by simpa [iInf_of_empty, ite_eq_right_iff, mul_top']
    aesop
  rw [mul_iInf]

/-- A version of `iInf_mul` with a slightly more general hypothesis. -/
/-
**ENat.iInf_mul'** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：iInf_mul' (h₀ : a = 0 -> Nonempty ι) : (⨅ i, f i) * a = ⨅ i, f i * a
参数：h₀ : a = 0 -> Nonempty ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `ENat.mul_iInf'`：mul_iInf' (h₀ : a = 0 -> Nonempty ι) : a * ⨅ i, f i = ⨅ 
i, a * f i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A version of `iInf_mul` with a slightly more general hypothesis.
-/
lemma iInf_mul' (h₀ : a = 0 → Nonempty ι) : (⨅ i, f i) * a = ⨅ i, f i * a := by
  simp_rw [mul_comm, mul_iInf' h₀]

/-- If `a ≠ 0`, then right multiplication by `a` maps infimum to infimum.
See also `ENat.iInf_mul` that assumes `[Nonempty ι]` but does not require `a ≠ 0`. -/
/-
**ENat.mul_iInf_of_ne** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：mul_iInf_of_ne (ha₀ : a != 0) : a * ⨅ i, f i = ⨅ i, a * f i
参数：ha₀ : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENat.mul_iInf'`：mul_iInf' (h₀ : a = 0 -> Nonempty ι) : a * ⨅ i, f i = ⨅ 
i, a * f i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False

--- 原说明 ---
If `a ≠ 0`, then right multiplication by `a` maps infimum to infimum.
See also `ENat.iInf_mul` that assumes `[Nonempty ι]` but does not require `a ≠ 0
`.
-/
lemma mul_iInf_of_ne (ha₀ : a ≠ 0) : a * ⨅ i, f i = ⨅ i, a * f i :=
  mul_iInf' <| by simp [ha₀]

/-- If `a ≠ 0`, then right multiplication by `a` maps infimum to infimum.
See also `ENat.iInf_mul` that assumes `[Nonempty ι]` but does not require `a ≠ 0`. -/
/-
**ENat.iInf_mul_of_ne** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：iInf_mul_of_ne (ha₀ : a != 0) : (⨅ i, f i) * a = ⨅ i, f i * a
参数：ha₀ : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENat.iInf_mul'`：iInf_mul' (h₀ : a = 0 -> Nonempty ι) : (⨅ i, f i) * a = 
⨅ i, f i * a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False

--- 原说明 ---
If `a ≠ 0`, then right multiplication by `a` maps infimum to infimum.
See also `ENat.iInf_mul` that assumes `[Nonempty ι]` but does not require `a ≠ 0
`.
-/
lemma iInf_mul_of_ne (ha₀ : a ≠ 0) : (⨅ i, f i) * a = ⨅ i, f i * a :=
  iInf_mul' <| by simp [ha₀]
/-
**ENat.add_iSup** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：add_iSup [Nonempty ι] (f : ι -> Nat∞) : a + ⨆ i, f i = ⨆ i, a + f i
参数：f : ι -> Nat∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `top_add`：top_add (a : α) : ⊤ + a = ⊤
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ciSup_const`：ciSup_const [hι : Nonempty ι] {a : α} : ⨆ _ : ι, a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `add_le_of_le_tsub_left_of_le`：add_le_of_le_tsub_left_of_le (h : a <= c) 
(h2 : b <= c - a) : a + b <= c
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instOrderedSubENat`：OrderedSub ℕ∞
· 使用定理 `le_iSup_of_le`：le_iSup_of_le (i : ι) (h : a <= f i) : a <= iSup f
· 使用定理 `le_self_add`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ a + b
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `ENat.le_sub_of_add_le_left`：∀ {a b c : ℕ∞}, a ≠ ⊤ → a + b ≤ c → b ≤ c - 
a
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
lemma add_iSup [Nonempty ι] (f : ι → ℕ∞) : a + ⨆ i, f i = ⨆ i, a + f i := by
  obtain rfl | ha := eq_or_ne a ⊤
  · simp
  refine le_antisymm ?_ <| iSup_le fun i ↦ by grw [← le_iSup]
  refine add_le_of_le_tsub_left_of_le (le_iSup_of_le (Classical.arbitrary _) le_self_add) ?_
  exact iSup_le fun i ↦ ENat.le_sub_of_add_le_left ha <| le_iSup (a + f ·) i
/-
**ENat.iSup_add** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：iSup_add [Nonempty ι] (f : ι -> Nat∞) : (⨆ i, f i) + a = ⨆ i, f i + a
参数：f : ι -> Nat∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `ENat.add_iSup`：add_iSup [Nonempty ι] (f : ι -> Nat∞) : a + ⨆ i, f i = ⨆ 
i, a + f i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma iSup_add [Nonempty ι] (f : ι → ℕ∞) : (⨆ i, f i) + a = ⨆ i, f i + a := by
  simp [add_comm, add_iSup]
/-
**ENat.add_biSup'** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：add_biSup' {p : ι -> Prop} (h : exists i, p i) (f : ι -> Nat∞) : a + ⨆ i, 
⨆ _ : p i, f i = ⨆ i, ⨆ _ : p i, a + f i
参数：h : exists i, p i；f : ι -> Nat∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `nonempty_subtype`：nonempty_subtype {α} {p : α -> Prop} : Nonempty (Subty
pe p) ↔ exists a : α, p a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_subtype'`：iSup_subtype' {p : ι -> Prop} {f : forall i, p i -> α} : 
⨆ (i) (h), f i h = ⨆ x : Subtype p, f x x.property
· 使用引理 `ENat.add_iSup`：add_iSup [Nonempty ι] (f : ι -> Nat∞) : a + ⨆ i, f i = ⨆ 
i, a + f i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma add_biSup' {p : ι → Prop} (h : ∃ i, p i) (f : ι → ℕ∞) :
    a + ⨆ i, ⨆ _ : p i, f i = ⨆ i, ⨆ _ : p i, a + f i := by
  have : Nonempty {i // p i} := nonempty_subtype.2 h
  simp only [iSup_subtype', add_iSup]
/-
**ENat.biSup_add'** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：biSup_add' {p : ι -> Prop} (h : exists i, p i) (f : ι -> Nat∞) : (⨆ i, ⨆ _
 : p i, f i) + a = ⨆ i, ⨆ _ : p i, f i + a
参数：h : exists i, p i；f : ι -> Nat∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `ENat.add_biSup'`：add_biSup' {p : ι -> Prop} (h : exists i, p i) (f : ι -
> Nat∞) : a + ⨆ i, ⨆ _ : p i, f i = ⨆ i, ⨆ _ : p i, a + f i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma biSup_add' {p : ι → Prop} (h : ∃ i, p i) (f : ι → ℕ∞) :
    (⨆ i, ⨆ _ : p i, f i) + a = ⨆ i, ⨆ _ : p i, f i + a := by simp only [add_comm, add_biSup' h]
/-
**ENat.add_biSup** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：add_biSup {ι : Type*} {s : Set ι} (hs : s.Nonempty) (f : ι -> Nat∞) : a + 
⨆ i in s, f i = ⨆ i in s, a + f i
参数：hs : s.Nonempty；f : ι -> Nat∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENat.add_biSup'`：add_biSup' {p : ι -> Prop} (h : exists i, p i) (f : ι -
> Nat∞) : a + ⨆ i, ⨆ _ : p i, f i = ⨆ i, ⨆ _ : p i, a + f i
-/
lemma add_biSup {ι : Type*} {s : Set ι} (hs : s.Nonempty) (f : ι → ℕ∞) :
    a + ⨆ i ∈ s, f i = ⨆ i ∈ s, a + f i := add_biSup' hs _
/-
**ENat.biSup_add** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：biSup_add {ι : Type*} {s : Set ι} (hs : s.Nonempty) (f : ι -> Nat∞) : (⨆ i
 in s, f i) + a = ⨆ i in s, f i + a
参数：hs : s.Nonempty；f : ι -> Nat∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENat.biSup_add'`：biSup_add' {p : ι -> Prop} (h : exists i, p i) (f : ι -
> Nat∞) : (⨆ i, ⨆ _ : p i, f i) + a = ⨆ i, ⨆ _ : p i, f i + a
-/
lemma biSup_add {ι : Type*} {s : Set ι} (hs : s.Nonempty) (f : ι → ℕ∞) :
    (⨆ i ∈ s, f i) + a = ⨆ i ∈ s, f i + a := biSup_add' hs _
/-
**ENat.add_sSup** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：add_sSup (hs : s.Nonempty) : a + sSup s = ⨆ b in s, a + b
参数：hs : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sSup_eq_iSup`：sSup_eq_iSup {s : Set α} : sSup s = ⨆ a in s, a
· 使用引理 `ENat.add_biSup`：add_biSup {ι : Type*} {s : Set ι} (hs : s.Nonempty) (f :
 ι -> Nat∞) : a + ⨆ i in s, f i = ⨆ i in s, a + f i
-/
lemma add_sSup (hs : s.Nonempty) : a + sSup s = ⨆ b ∈ s, a + b := by
  rw [sSup_eq_iSup, add_biSup hs]
/-
**ENat.sSup_add** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：sSup_add (hs : s.Nonempty) : sSup s + a = ⨆ b in s, b + a
参数：hs : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sSup_eq_iSup`：sSup_eq_iSup {s : Set α} : sSup s = ⨆ a in s, a
· 使用引理 `ENat.biSup_add`：biSup_add {ι : Type*} {s : Set ι} (hs : s.Nonempty) (f :
 ι -> Nat∞) : (⨆ i in s, f i) + a = ⨆ i in s, f i + a
-/
lemma sSup_add (hs : s.Nonempty) : sSup s + a = ⨆ b ∈ s, b + a := by
  rw [sSup_eq_iSup, biSup_add hs]
/-
**ENat.iSup_add_iSup_le** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：iSup_add_iSup_le [Nonempty ι] [Nonempty κ] {g : κ -> Nat∞} (h : forall i j
, f i + g j <= a) : iSup f + iSup g <= a
参数：h : forall i j, f i + g j <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ENat.iSup_add`：iSup_add [Nonempty ι] (f : ι -> Nat∞) : (⨆ i, f i) + a = 
⨆ i, f i + a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `ENat.add_iSup`：add_iSup [Nonempty ι] (f : ι -> Nat∞) : a + ⨆ i, f i = ⨆ 
i, a + f i
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
-/
lemma iSup_add_iSup_le [Nonempty ι] [Nonempty κ] {g : κ → ℕ∞} (h : ∀ i j, f i + g j ≤ a) :
    iSup f + iSup g ≤ a := by simp_rw [iSup_add, add_iSup]; exact iSup₂_le h
/-
**ENat.biSup_add_biSup_le'** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：biSup_add_biSup_le' {p : ι -> Prop} {q : κ -> Prop} (hp : exists i, p i) (
hq : exists j, q j) {g : κ -> Nat∞} (h : forall i, p i -> forall j, q j -> f i +
 g j <= a) : (⨆ i, ⨆ _ : p i, f i) + ⨆ j, ⨆ _ : q j, g j <= a
参数：hp : exists i, p i；hq : exists j, q j；h : forall i, p i -> forall j, q j -> f
 i + g j <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ENat.biSup_add'`：biSup_add' {p : ι -> Prop} (h : exists i, p i) (f : ι -
> Nat∞) : (⨆ i, ⨆ _ : p i, f i) + a = ⨆ i, ⨆ _ : p i, f i + a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用引理 `ENat.add_biSup'`：add_biSup' {p : ι -> Prop} (h : exists i, p i) (f : ι -
> Nat∞) : a + ⨆ i, ⨆ _ : p i, f i = ⨆ i, ⨆ _ : p i, a + f i
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
-/
lemma biSup_add_biSup_le' {p : ι → Prop} {q : κ → Prop} (hp : ∃ i, p i) (hq : ∃ j, q j)
    {g : κ → ℕ∞} (h : ∀ i, p i → ∀ j, q j → f i + g j ≤ a) :
    (⨆ i, ⨆ _ : p i, f i) + ⨆ j, ⨆ _ : q j, g j ≤ a := by
  simp_rw [biSup_add' hp, add_biSup' hq]
  exact iSup₂_le fun i hi => iSup₂_le (h i hi)
/-
**ENat.biSup_add_biSup_le** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：biSup_add_biSup_le {ι κ : Type*} {s : Set ι} {t : Set κ} (hs : s.Nonempty)
 (ht : t.Nonempty) {f : ι -> Nat∞} {g : κ -> Nat∞} {a : Nat∞} (h : forall i in s
, forall j in t, f i + g j <= a) : (⨆ i in s, f i) + ⨆ j in t, g j <= a
参数：hs : s.Nonempty；ht : t.Nonempty；h : forall i in s, forall j in t, f i + g j <
= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENat.biSup_add_biSup_le'`：biSup_add_biSup_le' {p : ι -> Prop} {q : κ -> 
Prop} (hp : exists i, p i) (hq : exists j, q j) {g : κ -> Nat∞} (h : forall i, p
 i -> forall j…
-/
lemma biSup_add_biSup_le {ι κ : Type*} {s : Set ι} {t : Set κ} (hs : s.Nonempty) (ht : t.Nonempty)
    {f : ι → ℕ∞} {g : κ → ℕ∞} {a : ℕ∞} (h : ∀ i ∈ s, ∀ j ∈ t, f i + g j ≤ a) :
    (⨆ i ∈ s, f i) + ⨆ j ∈ t, g j ≤ a := biSup_add_biSup_le' hs ht h
/-
**ENat.iSup_add_iSup** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：iSup_add_iSup (h : forall i j, exists k, f i + g j <= f k + g k) : iSup f 
+ iSup g = ⨆ i, f i + g i
参数：h : forall i j, exists k, f i + g j <= f k + g k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ciSup_of_empty`：ciSup_of_empty [IsEmpty ι] (f : ι -> α) : ⨆ i, f i = ⊥
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `ENat.iSup_add_iSup_le`：iSup_add_iSup_le [Nonempty ι] [Nonempty κ] {g : κ
 -> Nat∞} (h : forall i j, f i + g j <= a) : iSup f + iSup g <= a
· 使用定理 `le_iSup_of_le`：le_iSup_of_le (i : ι) (h : a <= f i) : a <= iSup f
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
-/
lemma iSup_add_iSup (h : ∀ i j, ∃ k, f i + g j ≤ f k + g k) : iSup f + iSup g = ⨆ i, f i + g i := by
  cases isEmpty_or_nonempty ι
  · simp
  · refine le_antisymm ?_ (iSup_le fun a => add_le_add (le_iSup _ _) (le_iSup _ _))
    refine iSup_add_iSup_le fun i j => ?_
    rcases h i j with ⟨k, hk⟩
    exact le_iSup_of_le k hk
/-
**ENat.iSup_add_iSup_of_monotone** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：iSup_add_iSup_of_monotone {ι : Type*} [Preorder ι] [IsDirectedOrder ι] {f 
g : ι -> Nat∞} (hf : Monotone f) (hg : Monotone g) : iSup f + iSup g = ⨆ a, f a 
+ g a
参数：hf : Monotone f；hg : Monotone g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENat.iSup_add_iSup`：iSup_add_iSup (h : forall i j, exists k, f i + g j <
= f k + g k) : iSup f + iSup g = ⨆ i, f i + g i
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `exists_ge_ge`：exists_ge_ge [LE α] [IsDirectedOrder α] (a b : α) : exists
 c, a <= c ∧ b <= c
-/
lemma iSup_add_iSup_of_monotone {ι : Type*} [Preorder ι] [IsDirectedOrder ι] {f g : ι → ℕ∞}
    (hf : Monotone f) (hg : Monotone g) : iSup f + iSup g = ⨆ a, f a + g a :=
  iSup_add_iSup fun i j ↦ (exists_ge_ge i j).imp fun _k ⟨hi, hj⟩ ↦ by gcongr <;> apply_rules
/-
**ENat.smul_iSup** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：smul_iSup {R} [SMul R Nat∞] [IsScalarTower R Nat∞ Nat∞] (f : ι -> Nat∞) (c
 : R) : c • ⨆ i, f i = ⨆ i, c • f i
参数：f : ι -> Nat∞；c : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_one_mul`：smul_one_mul {M N} [MulOneClass N] [SMul M N] [IsScalarTow
er M N N] (x : M) (y : N) : x • (1 : N) * y = x • y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `ENat.mul_iSup`：mul_iSup (a : Nat∞) (f : ι -> Nat∞) : a * ⨆ i, f i = ⨆ i,
 a * f i
-/
lemma smul_iSup {R} [SMul R ℕ∞] [IsScalarTower R ℕ∞ ℕ∞] (f : ι → ℕ∞) (c : R) :
    c • ⨆ i, f i = ⨆ i, c • f i := by
  simpa using mul_iSup (c • 1) f
/-
**ENat.smul_sSup** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：smul_sSup {R} [SMul R Nat∞] [IsScalarTower R Nat∞ Nat∞] (s : Set Nat∞) (c 
: R) : c • sSup s = ⨆ a in s, c • a
参数：s : Set Nat∞；c : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sSup_eq_iSup`：sSup_eq_iSup {s : Set α} : sSup s = ⨆ a in s, a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `ENat.smul_iSup`：smul_iSup {R} [SMul R Nat∞] [IsScalarTower R Nat∞ Nat∞] 
(f : ι -> Nat∞) (c : R) : c • ⨆ i, f i = ⨆ i, c • f i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma smul_sSup {R} [SMul R ℕ∞] [IsScalarTower R ℕ∞ ℕ∞] (s : Set ℕ∞) (c : R) :
    c • sSup s = ⨆ a ∈ s, c • a := by
  simp_rw [sSup_eq_iSup, smul_iSup]
/-
**ENat.sub_iSup** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：sub_iSup [Nonempty ι] (ha : a != ⊤) : a - ⨆ i, f i = ⨅ i, a - f i
参数：ha : a != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tsub_eq_zero_iff_le`：tsub_eq_zero_iff_le : a - b = 0 ↔ a <= b
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `instOrderedSubENat`：OrderedSub ℕ∞
· 使用定理 `le_iSup_of_le`：le_iSup_of_le (i : ι) (h : a <= f i) : a <= iSup f
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `iInf_eq_bot`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLinearOrder
 α] {f : ι → α}, iInf f = ⊥ ↔ ∀ (b : α), ⊥ < b → ∃ i, f i < b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `tsub_eq_zero_of_le`：∀ {α : Type u_1} [inst : AddCommMonoid α] [inst_1 : 
PartialOrder α] [CanonicallyOrderedAdd α] [inst_3 : Sub α]   [OrderedSub α] {a b
 : α}, a…
· 使用定理 `bot_eq_zero`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Zero α] 
[IsBotZeroClass α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f :
 ι → α} {a : α}, (∀ (i : ι), a ≤ f i) → a ≤ iInf f
· 使用定理 `tsub_le_tsub_left`：tsub_le_tsub_left (h : a <= b) (c : α) : c - b <= c -
 a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `ENat.le_sub_of_add_le_left`：∀ {a b c : ℕ∞}, a ≠ ⊤ → a + b ≤ c → b ≤ c - 
a
· 使用定理 `ne_top_of_le_ne_top`：ne_top_of_le_ne_top (hb : b != ⊤) (hab : a <= b) : 
a != ⊤
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `add_le_of_le_tsub_right_of_le`：add_le_of_le_tsub_right_of_le (h : b <= c
) (h2 : a <= c - b) : a + b <= c
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `iInf_le_of_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α
] {f : ι → α} {a : α} (i : ι), f i ≤ a → iInf f ≤ a
· 使用定理 `tsub_le_self`：tsub_le_self : a - b <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENat.sub_sub_cancel`：∀ {a b : ℕ∞}, a ≠ ⊤ → b ≤ a → a - (a - b) = b
（共 31 条，此处仅展示前 30 条）
-/
lemma sub_iSup [Nonempty ι] (ha : a ≠ ⊤) : a - ⨆ i, f i = ⨅ i, a - f i := by
  obtain ⟨i, hi⟩ | h := em (∃ i, a < f i)
  · rw [tsub_eq_zero_iff_le.2 <| le_iSup_of_le _ hi.le, iInf_eq_bot.2, bot_eq_zero]
    exact fun x hx ↦ ⟨i, by simpa [hi.le, tsub_eq_zero_of_le]⟩
  simp_rw [not_exists, not_lt] at h
  refine le_antisymm (le_iInf fun i ↦ tsub_le_tsub_left (le_iSup ..) _) <|
    ENat.le_sub_of_add_le_left (ne_top_of_le_ne_top ha <| iSup_le h) <|
    add_le_of_le_tsub_right_of_le (iInf_le_of_le (Classical.arbitrary _) tsub_le_self) <|
    iSup_le fun i ↦ ?_
  rw [← ENat.sub_sub_cancel ha (h _)]
  exact tsub_le_tsub_left (iInf_le (a - f ·) i) _
/-
**ENat.iInf_add** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：iInf_add : iInf f + a = ⨅ i, f i + a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f :
 ι → α} {a : α}, (∀ (i : ι), a ≤ f i) → a ≤ iInf f
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `iInf_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] (f :
 ι → α) (i : ι), iInf f ≤ f i
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `tsub_le_iff_right`：tsub_le_iff_right [LE α] [Add α] [Sub α] [OrderedSub 
α] {a b c : α} : a - b <= c ↔ a <= c + b
· 使用定理 `instOrderedSubENat`：OrderedSub ℕ∞
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
lemma iInf_add : iInf f + a = ⨅ i, f i + a :=
  le_antisymm (le_iInf fun _ ↦ add_le_add (iInf_le _ _) le_rfl) <|
    (tsub_le_iff_right.1 <| le_iInf fun _ ↦ tsub_le_iff_right.2 <| iInf_le _ _)
/-
**ENat.sub_iInf** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：sub_iInf : (a - ⨅ i, f i) = ⨆ i, a - f i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_forall_ge_iff`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 (∀ (c : α), a ≤ c ↔ b ≤ c) → a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tsub_le_iff_right`：tsub_le_iff_right [LE α] [Add α] [Sub α] [OrderedSub 
α] {a b c : α} : a - b <= c ↔ a <= c + b
· 使用定理 `instOrderedSubENat`：OrderedSub ℕ∞
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `ENat.iInf_add`：iInf_add : iInf f + a = ⨅ i, f i + a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem sub_iInf : (a - ⨅ i, f i) = ⨆ i, a - f i := by
  refine eq_of_forall_ge_iff fun c => ?_
  rw [tsub_le_iff_right, add_comm, iInf_add]
  simp [tsub_le_iff_right, add_comm]
/-
**ENat.sInf_add** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：sInf_add {s : Set Nat∞} : sInf s + a = ⨅ b in s, b + a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sInf_eq_iInf`：∀ {α : Type u_1} [inst : CompleteLattice α] {s : Set α}, s
Inf s = ⨅ a ∈ s, a
· 使用引理 `ENat.iInf_add`：iInf_add : iInf f + a = ⨅ i, f i + a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sInf_add {s : Set ℕ∞} : sInf s + a = ⨅ b ∈ s, b + a := by simp [sInf_eq_iInf, iInf_add]
/-
**ENat.add_iInf** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：add_iInf {a : Nat∞} : a + iInf f = ⨅ b, a + f b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `ENat.iInf_add`：iInf_add : iInf f + a = ⨅ i, f i + a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem add_iInf {a : ℕ∞} : a + iInf f = ⨅ b, a + f b := by
  rw [add_comm, iInf_add]; simp [add_comm]
/-
**ENat.iInf_add_iInf** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：iInf_add_iInf (h : forall i j, exists k, f k + g k <= f i + g j) : iInf f 
+ iInf g = ⨅ a, f a + g a
参数：h : forall i j, exists k, f k + g k <= f i + g j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_iInf₂`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst : Com
pleteLattice α] {a : α} {f : (i : ι) → κ i → α},   (∀ (i : ι) (j : κ i), a ≤ f…
· 使用定理 `iInf_le_of_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α
] {f : ι → α} {a : α} (i : ι), f i ≤ a → iInf f ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ENat.iInf_add`：iInf_add : iInf f + a = ⨅ i, f i + a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ENat.add_iInf`：add_iInf {a : Nat∞} : a + iInf f = ⨅ b, a + f b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f :
 ι → α} {a : α}, (∀ (i : ι), a ≤ f i) → a ≤ iInf f
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `iInf_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] (f :
 ι → α) (i : ι), iInf f ≤ f i
-/
theorem iInf_add_iInf (h : ∀ i j, ∃ k, f k + g k ≤ f i + g j) : iInf f + iInf g = ⨅ a, f a + g a :=
  suffices ⨅ a, f a + g a ≤ iInf f + iInf g from
    le_antisymm (le_iInf fun _ => add_le_add (iInf_le _ _) (iInf_le _ _)) this
  calc
    ⨅ a, f a + g a ≤ ⨅ (a) (a'), f a + g a' :=
      le_iInf₂ fun a a' => let ⟨k, h⟩ := h a a'; iInf_le_of_le k h
    _ = iInf f + iInf g := by simp_rw [iInf_add, add_iInf]
/-
**ENat.iInf_add_iInf_of_monotone** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：iInf_add_iInf_of_monotone {ι : Type*} [Preorder ι] [IsCodirectedOrder ι] {
f g : ι -> Nat∞} (hf : Monotone f) (hg : Monotone g) : iInf f + iInf g = ⨅ a, f 
a + g a
参数：hf : Monotone f；hg : Monotone g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENat.iInf_add_iInf`：iInf_add_iInf (h : forall i j, exists k, f k + g k <
= f i + g j) : iInf f + iInf g = ⨅ a, f a + g a
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `exists_le_le`：∀ {α : Type u_1} [inst : LE α] [IsCodirectedOrder α] (a b 
: α), ∃ c ≤ a, c ≤ b
-/
lemma iInf_add_iInf_of_monotone {ι : Type*} [Preorder ι] [IsCodirectedOrder ι] {f g : ι → ℕ∞}
    (hf : Monotone f) (hg : Monotone g) : iInf f + iInf g = ⨅ a, f a + g a :=
  iInf_add_iInf fun i j ↦ (exists_le_le i j).imp fun _k ⟨hi, hj⟩ ↦ by gcongr <;> apply_rules
/-
**ENat.add_iInf** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：add_iInf {a : Nat∞} : a + iInf f = ⨅ b, a + f b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `ENat.iInf_add`：iInf_add : iInf f + a = ⨅ i, f i + a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma add_iInf₂ {κ : ι → Sort*} (f : (i : ι) → κ i → ℕ∞) :
    a + ⨅ (i) (j), f i j = ⨅ (i) (j), a + f i j := by
  simp [add_iInf]
/-
**ENat.iInf** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma iInf₂_add {κ : ι → Sort*} (f : (i : ι) → κ i → ℕ∞) :
    (⨅ (i) (j), f i j) + a = ⨅ (i) (j), f i j + a := by
  simp only [add_comm, add_iInf₂]
/-
**ENat.add_sInf** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：add_sInf {s : Set Nat∞} : a + sInf s = ⨅ b in s, a + b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sInf_eq_iInf`：∀ {α : Type u_1} [inst : CompleteLattice α] {s : Set α}, s
Inf s = ⨅ a ∈ s, a
· 使用引理 `ENat.add_iInf₂`：add_iInf₂ {κ : ι -> Sort*} (f : (i : ι) -> κ i -> Nat∞) 
: a + ⨅ (i) (j), f i j = ⨅ (i) (j), a + f i j
-/
lemma add_sInf {s : Set ℕ∞} : a + sInf s = ⨅ b ∈ s, a + b := by
  rw [sInf_eq_iInf, add_iInf₂]

variable {κ : Sort*}
/-
**ENat.le_iInf_add_iInf** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：le_iInf_add_iInf {g : κ -> Nat∞} (h : forall i j, a <= f i + g j) : a <= i
Inf f + iInf g
参数：h : forall i j, a <= f i + g j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ENat.iInf_add`：iInf_add : iInf f + a = ⨅ i, f i + a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ENat.add_iInf`：add_iInf {a : Nat∞} : a + iInf f = ⨅ b, a + f b
· 使用定理 `le_iInf₂`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst : Com
pleteLattice α] {a : α} {f : (i : ι) → κ i → α},   (∀ (i : ι) (j : κ i), a ≤ f…
-/
lemma le_iInf_add_iInf {g : κ → ℕ∞} (h : ∀ i j, a ≤ f i + g j) :
    a ≤ iInf f + iInf g := by
  simp_rw [iInf_add, add_iInf]; exact le_iInf₂ h
/-
**ENat.le_iInf** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma le_iInf₂_add_iInf₂ {q₁ : ι → Sort*} {q₂ : κ → Sort*}
    {f : (i : ι) → q₁ i → ℕ∞} {g : (k : κ) → q₂ k → ℕ∞}
    (h : ∀ i pi k qk, a ≤ f i pi + g k qk) :
    a ≤ (⨅ (i) (qi), f i qi) + ⨅ (k) (qk), g k qk := by
  simp_rw [iInf₂_add, add_iInf₂]
  exact le_iInf₂ fun i hi => le_iInf₂ (h i hi)

end ENat

