/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Algebra.Order.Ring.NNRat
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.Tactic.Positivity.Basic

/-!
# Density of a finite set

This defines the density of a `Finset` and provides induction principles for finsets.

## Main declarations

* `Finset.dens s`: Density of `s : Finset α` in `α` as a nonnegative rational number.

## Implementation notes

There are many other ways to talk about the density of a finset and provide its API:
1. Use the uniform measure
2. Define finitely additive functions and generalise the `Finset.card` API to it. This could either
  be done with
  a. A structure `FinitelyAdditiveFun`
  b. A typeclass `IsFinitelyAdditiveFun`

Solution 1 would mean importing measure theory in simple files (not necessarily bad, but not
amazing), and every single API lemma would require the user to prove that all the sets they are
talking about are measurable in the trivial sigma-algebra (quite terrible user experience).

Solution 2 would mean that some API lemmas about density don't contain `dens` in their name because
they are general results about finitely additive functions. But not all lemmas would be like that
either since some really are `dens`-specific. Hence the user would need to think about whether the
lemma they are looking for is generally true for finitely additive measure or whether it is
`dens`-specific.

On top of this, solution 2.a would break dot notation on `Finset.dens` (possibly fixable by
introducing notation for `⇑Finset.dens`) and solution 2.b would run the risk of being bad
performance-wise.

These considerations more generally apply to `Finset.card` and `Finset.sum` and demonstrate that
overengineering basic definitions is likely to hinder user experience.
-/

@[expose] public section

-- TODO
-- assert_not_exists Ring

open Function Multiset Nat

variable {𝕜 α β : Type*} [Fintype α]

namespace Finset
variable {s t : Finset α} {a b : α}

/-- Density of a finset.

`dens s` is the number of elements of `s` divided by the size of the ambient type `α`. -/
/-
**Finset.dens** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：dens (s : Finset α) : Rat>=0
参数：s : Finset α。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Density of a finset.

`dens s` is the number of elements of `s` divided by the size of the ambient typ
e `α`.
-/
def dens (s : Finset α) : ℚ≥0 := s.card / Fintype.card α
/-
**Finset.dens_eq_card_div_card** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：dens_eq_card_div_card (s : Finset α) : dens s = s.card / Fintype.card α
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma dens_eq_card_div_card (s : Finset α) : dens s = s.card / Fintype.card α := rfl
/-
**Finset.dens_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : Fintype α], ∅.dens = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma dens_empty : dens (∅ : Finset α) = 0 := by simp [dens]
/-
**Finset.dens_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : Fintype α] (a : α), {a}.dens = (↑(Fintype.card α)
)⁻¹
参数：a : α；↑(Fintype.card α)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma dens_singleton (a : α) : dens ({a} : Finset α) = (Fintype.card α : ℚ≥0)⁻¹ := by
  simp [dens]
/-
**Finset.dens_cons** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : Fintype α] {s : Finset α} {a : α} (h : a ∉ s),   
(Finset.cons a s h).dens = s.dens + (↑(Fintype.card α))⁻¹
参数：h : a ∉ s；Finset.cons a s h；↑(Fintype.card α)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_cons`：card_cons (h : a ∉ s) : #(s.cons a h) = #s + 1
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `add_div`：add_div (a b c : K) : (a + b) / c = a / c + b / c
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma dens_cons (h : a ∉ s) : (s.cons a h).dens = dens s + (Fintype.card α : ℚ≥0)⁻¹ := by
  simp [dens, add_div]
/-
**Finset.dens_disjUnion** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : Fintype α] (s t : Finset α) (h : Disjoint s t), (
s.disjUnion t h).dens = s.dens + t.dens
参数：s t : Finset α；h : Disjoint s t；s.disjUnion t h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_disjUnion`：card_disjUnion (s t : Finset α) (h) : #(s.disjUni
on t h) = #s + #t
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_div`：add_div (a b c : K) : (a + b) / c = a / c + b / c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma dens_disjUnion (s t : Finset α) (h) : dens (s.disjUnion t h) = dens s + dens t := by
  simp_rw [dens, card_disjUnion, Nat.cast_add, add_div]
/-
**Finset.dens_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : Fintype α] {s : Finset α}, s.dens = 0 ↔ s = ∅
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `Finset.eq_empty_of_isEmpty`：eq_empty_of_isEmpty [IsEmpty α] (s : Finset 
α) : s = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] lemma dens_eq_zero : dens s = 0 ↔ s = ∅ := by
  simp +contextual [dens, Fintype.card_eq_zero_iff, eq_empty_of_isEmpty]
/-
**Finset.dens_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：dens_ne_zero : dens s != 0 ↔ s.Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Finset.dens_eq_zero`：∀ {α : Type u_2} [inst : Fintype α] {s : Finset α},
 s.dens = 0 ↔ s = ∅
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Finset.nonempty_iff_ne_empty`：nonempty_iff_ne_empty {s : Finset α} : s.N
onempty ↔ s != ∅
-/
lemma dens_ne_zero : dens s ≠ 0 ↔ s.Nonempty := dens_eq_zero.not.trans nonempty_iff_ne_empty.symm
/-
**Finset.dens_pos** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : Fintype α] {s : Finset α}, 0 < s.dens ↔ s.Nonempt
y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用引理 `Finset.dens_ne_zero`：dens_ne_zero : dens s != 0 ↔ s.Nonempty
-/
@[simp] lemma dens_pos : 0 < dens s ↔ s.Nonempty := pos_iff_ne_zero.trans dens_ne_zero

protected alias ⟨_, Nonempty.dens_pos⟩ := dens_pos
protected alias ⟨_, Nonempty.dens_ne_zero⟩ := dens_ne_zero

@[gcongr]
/-
**Finset.dens_le_dens** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：dens_le_dens (h : s subseteq t) : dens s <= dens t
参数：h : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `div_le_div_of_nonneg_right`：div_le_div_of_nonneg_right (hab : a <= b) (h
c : 0 <= c) : a / c <= b / c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `NNRat.instIsStrictOrderedRing`：IsStrictOrderedRing ℚ≥0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `Finset.card_mono`：card_mono : Monotone (@card α)
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
-/
lemma dens_le_dens (h : s ⊆ t) : dens s ≤ dens t :=
  div_le_div_of_nonneg_right (mod_cast card_mono h) <| by positivity

@[gcongr]
/-
**Finset.dens_lt_dens** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：dens_lt_dens (h : s ⊂ t) : dens s < dens t
参数：h : s ⊂ t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `div_lt_div_of_pos_right`：div_lt_div_of_pos_right (h : a < b) (hc : 0 < c
) : a / c < b / c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `NNRat.instIsStrictOrderedRing`：IsStrictOrderedRing ℚ≥0
· 使用定理 `Nat.strictMono_cast`：strictMono_cast : StrictMono (Nat.cast : Nat -> α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `Finset.card_lt_card`：∀ {α : Type u_1} {s t : Finset α}, s ⊂ t → s.card <
 t.card
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `Finset.card_le_univ`：Finset.card_le_univ [Fintype α] (s : Finset α) : #s
 <= Fintype.card α
-/
lemma dens_lt_dens (h : s ⊂ t) : dens s < dens t :=
  div_lt_div_of_pos_right (by gcongr) <| mod_cast calc
    0 ≤ #s := Nat.zero_le _
    _ < #t := by gcongr
    _ ≤ Fintype.card α := card_le_univ t
/-
**Finset.dens_mono** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : Fintype α], Monotone Finset.dens
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.dens_le_dens`：dens_le_dens (h : s subseteq t) : dens s <= dens t
-/
@[mono] lemma dens_mono : Monotone (dens : Finset α → ℚ≥0) := fun _ _ ↦ dens_le_dens
/-
**Finset.dens_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : Fintype α], StrictMono Finset.dens
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.dens_lt_dens`：dens_lt_dens (h : s ⊂ t) : dens s < dens t
-/
@[mono] lemma dens_strictMono : StrictMono (dens : Finset α → ℚ≥0) := fun _ _ ↦ dens_lt_dens
/-
**Finset.dens_map_le** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：dens_map_le [Fintype β] (f : α ↪ β) : dens (s.map f) <= dens s
参数：f : α ↪ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Finset.dens_empty`：∀ {α : Type u_2} [inst : Fintype α], ∅.dens = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用引理 `div_le_div₀`：div_le_div₀ (hc : 0 <= c) (hac : a <= c) (hd : 0 < d) (hdb 
: d <= b) : a / b <= c / d
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `NNRat.instIsStrictOrderedRing`：IsStrictOrderedRing ℚ≥0
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Fintype.card_pos`：card_pos [h : Nonempty α] : 0 < card α
· 使用定理 `Nat.mono_cast`：mono_cast : Monotone (Nat.cast : Nat -> α)
· 使用定理 `Fintype.card_le_of_injective`：card_le_of_injective (f : α -> β) (hf : Fu
nction.Injective f) : card α <= card β
（共 31 条，此处仅展示前 30 条）
-/
lemma dens_map_le [Fintype β] (f : α ↪ β) : dens (s.map f) ≤ dens s := by
  cases isEmpty_or_nonempty α
  · simp [Subsingleton.elim s ∅]
  simp_rw [dens, card_map]
  gcongr
  · exact mod_cast Fintype.card_pos
  · exact Fintype.card_le_of_injective _ f.2
/-
**Finset.dens_map_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : Fintype α] {s : Finset α} [inst_1 
: Fintype β] (e : α ≃ β),   (Finset.map e.toEmbedding s).dens = s.dens
参数：e : α ≃ β；Finset.map e.toEmbedding s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用定理 `Fintype.card_congr`：card_congr {α β} [Fintype α] [Fintype β] (f : α ≃ β)
 : card α = card β
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma dens_map_equiv [Fintype β] (e : α ≃ β) : (s.map e.toEmbedding).dens = s.dens := by
  simp [dens, Fintype.card_congr e]
/-
**Finset.dens_image** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：dens_image [Fintype β] [DecidableEq β] {f : α -> β} (hf : Bijective f) (s 
: Finset α) : (s.image f).dens = s.dens
参数：hf : Bijective f；s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.map_eq_image`：map_eq_image (f : α ↪ β) (s : Finset α) : s.map f =
 s.image f
· 使用定理 `Finset.dens_map_equiv`：∀ {α : Type u_2} {β : Type u_3} [inst : Fintype α
] {s : Finset α} [inst_1 : Fintype β] (e : α ≃ β),   (Finset.map e.toEmbedding s
).dens = s.…
-/
lemma dens_image [Fintype β] [DecidableEq β] {f : α → β} (hf : Bijective f) (s : Finset α) :
    (s.image f).dens = s.dens := by
  simpa [map_eq_image, -dens_map_equiv] using dens_map_equiv (.ofBijective f hf)
/-
**Finset.card_mul_dens** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : Fintype α] (s : Finset α), ↑(Fintype.card α) * s.
dens = ↑s.card
参数：s : Finset α；Fintype.card α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_eq_zero`：∀ {α : Type u_1} [inst : Fintype α] [IsEmpty α], F
intype.card α = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Finset.dens_empty`：∀ {α : Type u_2} [inst : Fintype α], ∅.dens = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.dens.eq_1`：∀ {α : Type u_2} [inst : Fintype α] (s : Finset α), s.
dens = ↑s.card / ↑(Fintype.card α)
· 使用引理 `mul_div_cancel₀`：mul_div_cancel₀ (a : G₀) (hb : b != 0) : b * (a / b) = 
a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.card_ne_zero`：card_ne_zero [Nonempty α] : card α != 0
-/
@[simp] lemma card_mul_dens (s : Finset α) : Fintype.card α * s.dens = s.card := by
  cases isEmpty_or_nonempty α
  · simp [Subsingleton.elim s ∅]
  rw [dens, mul_div_cancel₀]
  exact mod_cast Fintype.card_ne_zero
/-
**Finset.dens_mul_card** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : Fintype α] (s : Finset α), s.dens * ↑(Fintype.car
d α) = ↑s.card
参数：s : Finset α；Fintype.card α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Finset.card_mul_dens`：∀ {α : Type u_2} [inst : Fintype α] (s : Finset α)
, ↑(Fintype.card α) * s.dens = ↑s.card
-/
@[simp] lemma dens_mul_card (s : Finset α) : s.dens * Fintype.card α = s.card := by
  rw [mul_comm, card_mul_dens]

section Semifield
variable [Semifield 𝕜] [CharZero 𝕜]

/-
**Finset.natCast_card_mul_nnratCast_dens** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {𝕜 : Type u_1} {α : Type u_2} [inst : Fintype α] [inst_1 : Semifield 𝕜] 
[CharZero 𝕜] (s : Finset α),   ↑(Fintype.card α) * ↑s.dens = ↑s.card
参数：s : Finset α；Fintype.card α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNRat.cast_natCast`：∀ {α : Type u_3} [inst : DivisionSemiring α] (n : ℕ)
, ↑↑n = ↑n
· 使用定理 `Finset.card_mul_dens`：∀ {α : Type u_2} [inst : Fintype α] (s : Finset α)
, ↑(Fintype.card α) * s.dens = ↑s.card
-/
@[simp] lemma natCast_card_mul_nnratCast_dens (s : Finset α) :
    (Fintype.card α * s.dens : 𝕜) = s.card := mod_cast s.card_mul_dens
/-
**Finset.nnratCast_dens_mul_natCast_card** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {𝕜 : Type u_1} {α : Type u_2} [inst : Fintype α] [inst_1 : Semifield 𝕜] 
[CharZero 𝕜] (s : Finset α),   ↑s.dens * ↑(Fintype.card α) = ↑s.card
参数：s : Finset α；Fintype.card α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNRat.cast_natCast`：∀ {α : Type u_3} [inst : DivisionSemiring α] (n : ℕ)
, ↑↑n = ↑n
· 使用定理 `Finset.dens_mul_card`：∀ {α : Type u_2} [inst : Fintype α] (s : Finset α)
, s.dens * ↑(Fintype.card α) = ↑s.card
-/
@[simp] lemma nnratCast_dens_mul_natCast_card (s : Finset α) :
    (s.dens * Fintype.card α : 𝕜) = s.card := mod_cast s.dens_mul_card
/-
**Finset.nnratCast_dens** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {𝕜 : Type u_1} {α : Type u_2} [inst : Fintype α] [inst_1 : Semifield 𝕜] 
[CharZero 𝕜] (s : Finset α),   ↑s.dens = ↑s.card / ↑(Fintype.card α)
参数：s : Finset α；Fintype.card α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNRat.cast_div`：∀ {α : Type u_3} [inst : DivisionSemiring α] [CharZero α
] (p q : ℚ≥0), ↑(p / q) = ↑p / ↑q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `NNRat.cast_natCast`：∀ {α : Type u_3} [inst : DivisionSemiring α] (n : ℕ)
, ↑↑n = ↑n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[norm_cast] lemma nnratCast_dens (s : Finset α) : (s.dens : 𝕜) = s.card / Fintype.card α := by
  simp [dens]

end Semifield

section Nonempty
variable [Nonempty α]

/-
**Finset.dens_univ** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : Fintype α] [Nonempty α], Finset.univ.dens = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma dens_univ : dens (univ : Finset α) = 1 := by simp [dens, card_univ]
/-
**Finset.dens_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : Fintype α] {s : Finset α} [Nonempty α], s.dens = 
1 ↔ s = Finset.univ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma dens_eq_one : dens s = 1 ↔ s = univ := by
  simp [dens, div_eq_one_iff_eq, card_eq_iff_eq_univ]
/-
**Finset.dens_ne_one** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：dens_ne_one : dens s != 1 ↔ s != univ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Finset.dens_eq_one`：∀ {α : Type u_2} [inst : Fintype α] {s : Finset α} [
Nonempty α], s.dens = 1 ↔ s = Finset.univ
-/
lemma dens_ne_one : dens s ≠ 1 ↔ s ≠ univ := dens_eq_one.not

end Nonempty

/-
**Finset.dens_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : Fintype α] {s : Finset α}, s.dens ≤ 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Finset.dens_empty`：∀ {α : Type u_2} [inst : Fintype α], ∅.dens = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Finset.dens_univ`：∀ {α : Type u_2} [inst : Fintype α] [Nonempty α], Fins
et.univ.dens = 1
· 使用引理 `Finset.dens_le_dens`：dens_le_dens (h : s subseteq t) : dens s <= dens t
· 使用定理 `Finset.subset_univ`：subset_univ (s : Finset α) : s subseteq univ
-/
@[simp] lemma dens_le_one : s.dens ≤ 1 := by
  cases isEmpty_or_nonempty α
  · simp [Subsingleton.elim s ∅]
  · simpa using dens_le_dens s.subset_univ

section Lattice
variable [DecidableEq α]

/-
**Finset.dens_union_add_dens_inter** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：dens_union_add_dens_inter (s t : Finset α) : dens (s union t) + dens (s in
ter t) = dens s + dens t
参数：s t : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.card_union_add_card_inter`：card_union_add_card_inter (s t : Finse
t α) : #(s union t) + #(s inter t) = #s + #t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma dens_union_add_dens_inter (s t : Finset α) :
    dens (s ∪ t) + dens (s ∩ t) = dens s + dens t := by
  simp_rw [dens, ← add_div, ← Nat.cast_add, card_union_add_card_inter]
/-
**Finset.dens_inter_add_dens_union** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：dens_inter_add_dens_union (s t : Finset α) : dens (s inter t) + dens (s un
ion t) = dens s + dens t
参数：s t : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `Finset.dens_union_add_dens_inter`：dens_union_add_dens_inter (s t : Finse
t α) : dens (s union t) + dens (s inter t) = dens s + dens t
-/
lemma dens_inter_add_dens_union (s t : Finset α) :
    dens (s ∩ t) + dens (s ∪ t) = dens s + dens t := by rw [add_comm, dens_union_add_dens_inter]
/-
**Finset.dens_union_of_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : Fintype α] {s t : Finset α} [inst_1 : DecidableEq
 α],   Disjoint s t → (s ∪ t).dens = s.dens + t.dens
参数：s ∪ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.disjUnion_eq_union`：disjUnion_eq_union (s t h) : @disjUnion α s t
 h = s union t
· 使用定理 `Finset.dens_disjUnion`：∀ {α : Type u_2} [inst : Fintype α] (s t : Finset
 α) (h : Disjoint s t), (s.disjUnion t h).dens = s.dens + t.dens
-/
@[simp] lemma dens_union_of_disjoint (h : Disjoint s t) : dens (s ∪ t) = dens s + dens t := by
  rw [← disjUnion_eq_union s t h, dens_disjUnion]
/-
**Finset.dens_sdiff_add_dens_eq_dens** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：dens_sdiff_add_dens_eq_dens (h : s subseteq t) : dens (t \ s) + dens s = d
ens t
参数：h : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_sdiff_add_card_eq_card`：card_sdiff_add_card_eq_card (h : s s
ubseteq t) : #(t \ s) + #s = #t
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `add_div`：add_div (a b c : K) : (a + b) / c = a / c + b / c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma dens_sdiff_add_dens_eq_dens (h : s ⊆ t) : dens (t \ s) + dens s = dens t := by
  simp [dens, ← card_sdiff_add_card_eq_card h, add_div]
/-
**Finset.dens_sdiff_add_dens** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：dens_sdiff_add_dens (s t : Finset α) : dens (s \ t) + dens t = (s union t)
.dens
参数：s t : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.dens_union_of_disjoint`：∀ {α : Type u_2} [inst : Fintype α] {s t 
: Finset α} [inst_1 : DecidableEq α],   Disjoint s t → (s ∪ t).dens = s.dens + t
.dens
· 使用定理 `Finset.sdiff_disjoint`：sdiff_disjoint : Disjoint (t \ s) s
· 使用定理 `Finset.sdiff_union_self_eq_union`：sdiff_union_self_eq_union : s \ t unio
n t = s union t
-/
lemma dens_sdiff_add_dens (s t : Finset α) : dens (s \ t) + dens t = (s ∪ t).dens := by
  rw [← dens_union_of_disjoint sdiff_disjoint, sdiff_union_self_eq_union]
/-
**Finset.dens_sdiff_comm** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：dens_sdiff_comm (h : card s = card t) : dens (s \ t) = dens (t \ s)
参数：h : card s = card t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_left_injective`：∀ {G : Type u_1} [inst : Add G] [IsRightCancelAdd G]
 (a : G), Function.Injective fun x => x + a
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `NNRat.instIsStrictOrderedRing`：IsStrictOrderedRing ℚ≥0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.dens_sdiff_add_dens`：dens_sdiff_add_dens (s t : Finset α) : dens 
(s \ t) + dens t = (s union t).dens
· 使用定理 `Finset.union_comm`：union_comm (s₁ s₂ : Finset α) : s₁ union s₂ = s₂ unio
n s₁
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma dens_sdiff_comm (h : card s = card t) : dens (s \ t) = dens (t \ s) :=
  add_left_injective (dens t) <| by
    simp_rw [dens_sdiff_add_dens, union_comm s, ← dens_sdiff_add_dens, dens, h]

@[simp]
/-
**Finset.dens_sdiff_add_dens_inter** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：dens_sdiff_add_dens_inter (s t : Finset α) : dens (s \ t) + dens (s inter 
t) = dens s
参数：s t : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.dens_union_of_disjoint`：∀ {α : Type u_2} [inst : Fintype α] {s t 
: Finset α} [inst_1 : DecidableEq α],   Disjoint s t → (s ∪ t).dens = s.dens + t
.dens
· 使用定理 `Finset.disjoint_sdiff_inter`：disjoint_sdiff_inter (s t : Finset α) : Dis
joint (s \ t) (s inter t)
· 使用定理 `Finset.sdiff_union_inter`：sdiff_union_inter (s t : Finset α) : s \ t uni
on s inter t = s
-/
lemma dens_sdiff_add_dens_inter (s t : Finset α) : dens (s \ t) + dens (s ∩ t) = dens s := by
  rw [← dens_union_of_disjoint (disjoint_sdiff_inter _ _), sdiff_union_inter]

@[simp]
/-
**Finset.dens_inter_add_dens_sdiff** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：dens_inter_add_dens_sdiff (s t : Finset α) : dens (s inter t) + dens (s \ 
t) = dens s
参数：s t : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `Finset.dens_sdiff_add_dens_inter`：dens_sdiff_add_dens_inter (s t : Finse
t α) : dens (s \ t) + dens (s inter t) = dens s
-/
lemma dens_inter_add_dens_sdiff (s t : Finset α) : dens (s ∩ t) + dens (s \ t) = dens s := by
  rw [add_comm, dens_sdiff_add_dens_inter]
/-
**Finset.dens_filter_add_dens_filter_not_eq_dens** 是 Mathlib 中的一个引理，位于命名空间 `Fins
et`。
形式化陈述：dens_filter_add_dens_filter_not_eq_dens {α : Type*} [Fintype α] {s : Finse
t α} (p : α -> Prop) [DecidablePred p] [forall x, Decidable (¬p x)] : dens {a in
 s | p a} + dens {a in s | ¬ p a} = dens s
参数：p : α -> Prop；¬p x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.dens_union_of_disjoint`：∀ {α : Type u_2} [inst : Fintype α] {s t 
: Finset α} [inst_1 : DecidableEq α],   Disjoint s t → (s ∪ t).dens = s.dens + t
.dens
· 使用定理 `Finset.disjoint_filter_filter_not`：disjoint_filter_filter_not (s t : Fin
set α) (p : α -> Prop) [DecidablePred p] [forall x, Decidable (¬p x)] : Disjoint
 (s.filter p) (t.filter…
· 使用定理 `Finset.filter_union_filter_not_eq`：filter_union_filter_not_eq [forall x,
 Decidable (¬p x)] (s : Finset α) : (s.filter p union s.filter fun a => ¬p a) = 
s
-/
lemma dens_filter_add_dens_filter_not_eq_dens {α : Type*} [Fintype α] {s : Finset α}
    (p : α → Prop) [DecidablePred p] [∀ x, Decidable (¬p x)] :
    dens {a ∈ s | p a} + dens {a ∈ s | ¬ p a} = dens s := by
  classical
  rw [← dens_union_of_disjoint (disjoint_filter_filter_not ..), filter_union_filter_not_eq]
/-
**Finset.dens_union_le** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：dens_union_le (s t : Finset α) : dens (s union t) <= dens s + dens t
参数：s t : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_add_of_nonneg_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1
 : LE α] [AddLeftMono α] {a b : α}, 0 ≤ b → a ≤ a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `NNRat.instIsStrictOrderedRing`：IsStrictOrderedRing ℚ≥0
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用引理 `Finset.dens_union_add_dens_inter`：dens_union_add_dens_inter (s t : Finse
t α) : dens (s union t) + dens (s inter t) = dens s + dens t
-/
lemma dens_union_le (s t : Finset α) : dens (s ∪ t) ≤ dens s + dens t :=
  dens_union_add_dens_inter s t ▸ le_add_of_nonneg_right zero_le
/-
**Finset.dens_le_dens_sdiff_add_dens** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：dens_le_dens_sdiff_add_dens : dens s <= dens (s \ t) + dens t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.dens_le_dens`：dens_le_dens (h : s subseteq t) : dens s <= dens t
· 使用定理 `Finset.subset_union_left`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s₂
 : Finset α}, s₁ ⊆ s₁ ∪ s₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.dens_sdiff_add_dens`：dens_sdiff_add_dens (s t : Finset α) : dens 
(s \ t) + dens t = (s union t).dens
-/
lemma dens_le_dens_sdiff_add_dens : dens s ≤ dens (s \ t) + dens t :=
  dens_sdiff_add_dens s _ ▸ dens_le_dens subset_union_left
/-
**Finset.dens_sdiff** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：dens_sdiff (h : s subseteq t) : dens (t \ s) = dens t - dens s
参数：h : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_tsub_of_add_eq`：eq_tsub_of_add_eq (h : a + c = b) : a = b - c
· 使用定理 `NNRat.instOrderedSub`：OrderedSub ℚ≥0
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `NNRat.instIsStrictOrderedRing`：IsStrictOrderedRing ℚ≥0
· 使用引理 `Finset.dens_sdiff_add_dens_eq_dens`：dens_sdiff_add_dens_eq_dens (h : s s
ubseteq t) : dens (t \ s) + dens s = dens t
-/
lemma dens_sdiff (h : s ⊆ t) : dens (t \ s) = dens t - dens s :=
  eq_tsub_of_add_eq (dens_sdiff_add_dens_eq_dens h)
/-
**Finset.le_dens_sdiff** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：le_dens_sdiff (s t : Finset α) : dens t - dens s <= dens (t \ s)
参数：s t : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tsub_le_iff_right`：tsub_le_iff_right [LE α] [Add α] [Sub α] [OrderedSub 
α] {a b c : α} : a - b <= c ↔ a <= c + b
· 使用定理 `NNRat.instOrderedSub`：OrderedSub ℚ≥0
· 使用引理 `Finset.dens_le_dens_sdiff_add_dens`：dens_le_dens_sdiff_add_dens : dens s
 <= dens (s \ t) + dens t
-/
lemma le_dens_sdiff (s t : Finset α) : dens t - dens s ≤ dens (t \ s) :=
  tsub_le_iff_right.2 dens_le_dens_sdiff_add_dens

end Lattice
end Finset

