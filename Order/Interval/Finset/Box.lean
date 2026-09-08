/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Disjointed
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Algebra.Order.Ring.Prod
public import Mathlib.Data.Int.Interval
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Zify

/-!
# Decomposing a locally finite ordered ring into boxes

This file proves that any locally finite ordered ring can be decomposed into "boxes", namely
differences of consecutive intervals.

## Implementation notes

We don't need the full ring structure, only that there is an order embedding `ℤ → `
-/

@[expose] public section

/-! ### General locally finite ordered ring -/

namespace Finset
variable {α : Type*} [Ring α] [PartialOrder α] [IsOrderedRing α] [LocallyFiniteOrder α] {n : ℕ}

/-
**Finset.Icc_neg_mono** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma Icc_neg_mono : Monotone fun n : ℕ ↦ Icc (-n : α) n := by
  refine fun m n hmn ↦ by apply Icc_subset_Icc <;> simpa using Nat.mono_cast hmn

variable [DecidableEq α]

/-- Hollow box centered at `0 : α` going from `-n` to `n`. -/
/-
**Finset.box** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：box : Nat -> Finset α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Hollow box centered at `0 : α` going from `-n` to `n`.
-/
def box : ℕ → Finset α := disjointed fun n ↦ Icc (-n : α) n

omit [IsOrderedRing α] in
/-
**Finset.box_zero** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : Ring α] [inst_1 : PartialOrder α] [inst_2 : Local
lyFiniteOrder α] [inst_3 : DecidableEq α],   Finset.box 0 = {0}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `disjointed_zero`：disjointed_zero (f : Nat -> α) : disjointed f 0 = f 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `Finset.Icc_self`：Icc_self (a : α) : Icc a a = {a}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma box_zero : (box 0 : Finset α) = {0} := by simp [box]
/-
**Finset.box_succ_eq_sdiff** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：box_succ_eq_sdiff (n : Nat) : box (n + 1) = Icc (-n.succ : α) n.succ \ Icc
 (-n) n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.box.eq_1`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : PartialOrder
 α] [inst_2 : LocallyFiniteOrder α] [inst_3 : DecidableEq α],   Finset.box = dis
joint…
· 使用定理 `Monotone.disjointed_add_one`：∀ {α : Type u_1} {ι : Type u_2} [inst : Gen
eralizedBooleanAlgebra α] [inst_1 : LinearOrder ι]   [inst_2 : LocallyFiniteOrde
rBot ι] [inst_3 :…
· 使用定理 `_private.Mathlib.Order.Interval.Finset.Box.0.Finset.Icc_neg_mono`：∀ {α :
 Type u_1} [inst : Ring α] [inst_1 : PartialOrder α] [IsOrderedRing α] [inst_3 :
 LocallyFiniteOrder α],   Monotone fun n => Finset.Icc…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_add_one`：cast_add_one (n : Nat) : ((n + 1 : Nat) : R) = n + 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma box_succ_eq_sdiff (n : ℕ) :
    box (n + 1) = Icc (-n.succ : α) n.succ \ Icc (-n) n := by
  rw [box, Icc_neg_mono.disjointed_add_one]
  simp only [Nat.cast_add_one, Nat.succ_eq_add_one]
/-
**Finset.disjoint_box_succ_prod** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：disjoint_box_succ_prod (n : Nat) : Disjoint (box (n + 1)) (Icc (-n : α) n)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.box_succ_eq_sdiff`：box_succ_eq_sdiff (n : Nat) : box (n + 1) = Ic
c (-n.succ : α) n.succ \ Icc (-n) n
· 使用定理 `disjoint_sdiff_self_left`：disjoint_sdiff_self_left : Disjoint (y \ x) x
-/
lemma disjoint_box_succ_prod (n : ℕ) : Disjoint (box (n + 1)) (Icc (-n : α) n) := by
  rw [box_succ_eq_sdiff]; exact disjoint_sdiff_self_left
/-
**Finset.box_succ_union_prod** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : Ring α] [inst_1 : PartialOrder α] [IsOrderedRing 
α] [inst_3 : LocallyFiniteOrder α]   [inst_4 : DecidableEq α] (n : ℕ), Finset.bo
x (n + 1) ∪ Finset.Icc (-↑n) ↑n = Finset.Icc (-↑n.succ) ↑n.succ
参数：n : ℕ；n + 1；-↑n；-↑n.succ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.disjointed_add_one_sup`：∀ {α : Type u_1} {ι : Type u_2} [inst :
 GeneralizedBooleanAlgebra α] [inst_1 : LinearOrder ι]   [inst_2 : LocallyFinite
OrderBot ι] [inst_3 :…
· 使用定理 `_private.Mathlib.Order.Interval.Finset.Box.0.Finset.Icc_neg_mono`：∀ {α :
 Type u_1} [inst : Ring α] [inst_1 : PartialOrder α] [IsOrderedRing α] [inst_3 :
 LocallyFiniteOrder α],   Monotone fun n => Finset.Icc…
-/
@[simp] lemma box_succ_union_prod (n : ℕ) :
    box (n + 1) ∪ Icc (-n : α) n = Icc (-n.succ : α) n.succ :=
  Icc_neg_mono.disjointed_add_one_sup _
/-
**Finset.box_succ_disjUnion** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：box_succ_disjUnion (n : Nat) : (box (n + 1)).disjUnion (Icc (-n : α) n) (d
isjoint_box_succ_prod _) = Icc (-n.succ : α) n.succ
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.disjoint_box_succ_prod`：disjoint_box_succ_prod (n : Nat) : Disjoi
nt (box (n + 1)) (Icc (-n : α) n)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.disjUnion_eq_union`：disjUnion_eq_union (s t h) : @disjUnion α s t
 h = s union t
· 使用定理 `Finset.box_succ_union_prod`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : P
artialOrder α] [IsOrderedRing α] [inst_3 : LocallyFiniteOrder α]   [inst_4 : Dec
idableEq α] (n :…
-/
lemma box_succ_disjUnion (n : ℕ) :
    (box (n + 1)).disjUnion (Icc (-n : α) n) (disjoint_box_succ_prod _) =
      Icc (-n.succ : α) n.succ := by rw [disjUnion_eq_union, box_succ_union_prod]
/-
**Finset.zero_mem_box** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : Ring α] [inst_1 : PartialOrder α] [IsOrderedRing 
α] [inst_3 : LocallyFiniteOrder α] {n : ℕ}   [inst_4 : DecidableEq α], 0 ∈ Finse
t.box n ↔ n = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.box_zero`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : PartialOrder
 α] [inst_2 : LocallyFiniteOrder α] [inst_3 : DecidableEq α],   Finset.box 0 = {
0}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.box_succ_eq_sdiff`：box_succ_eq_sdiff (n : Nat) : box (n + 1) = Ic
c (-n.succ : α) n.succ \ Icc (-n) n
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `neg_add_rev`：∀ {G : Type u_1} [inst : SubtractionMonoid G] (a b : G), -(
a + b) = -b + -a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
@[simp] lemma zero_mem_box : (0 : α) ∈ box n ↔ n = 0 := by cases n <;> simp [box_succ_eq_sdiff]
/-
**Finset.eq_zero_iff_eq_zero_of_mem_box** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：eq_zero_iff_eq_zero_of_mem_box {x : α} (hx : x in box n) : x = 0 ↔ n = 0
参数：hx : x in box n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.zero_mem_box`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : PartialO
rder α] [IsOrderedRing α] [inst_3 : LocallyFiniteOrder α] {n : ℕ}   [inst_4 : De
cidableEq…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_singleton`：mem_singleton {a b : α} : b in ({a} : Finset α) ↔ 
b = a
· 使用定理 `Finset.box_zero`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : PartialOrder
 α] [inst_2 : LocallyFiniteOrder α] [inst_3 : DecidableEq α],   Finset.box 0 = {
0}
-/
lemma eq_zero_iff_eq_zero_of_mem_box {x : α} (hx : x ∈ box n) : x = 0 ↔ n = 0 :=
  ⟨zero_mem_box.mp ∘ (· ▸ hx), fun hn ↦ by rwa [hn, box_zero, mem_singleton] at hx⟩

end Finset

open Finset

/-! ### Product of locally finite ordered rings -/

namespace Prod
variable {α β : Type*} [Ring α] [PartialOrder α] [IsOrderedRing α]
  [Ring β] [PartialOrder β] [IsOrderedRing β] [LocallyFiniteOrder α] [LocallyFiniteOrder β]
  [DecidableEq α] [DecidableEq β] [DecidableLE (α × β)]

/-
**Prod.card_box_succ** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Ring α] [inst_1 : PartialOrder α] 
[IsOrderedRing α] [inst_3 : Ring β]   [inst_4 : PartialOrder β] [IsOrderedRing β
] [inst_6 : LocallyFiniteOrder α] [inst_7 : LocallyFiniteOrder β]   [inst_8 : De
cidableEq α] [inst_9 : DecidableEq β] [inst_10 : DecidableLE (α × β)] (n : ℕ),  
 (Finset.box (n + 1)).card =     (Finset.Icc (-↑n.succ) ↑n.succ).card * (Finset.
Icc (-↑n.succ) ↑n.succ).card -       (Finset.Icc (-↑n) ↑n).card * (Finset.Icc (-
↑n) ↑n).card
参数：α × β；n : ℕ；Finset.box (n + 1)；Finset.Icc (-↑n.succ) ↑n.succ；Finset.Icc (-↑n.
succ) ↑n.succ；Finset.Icc (-↑n) ↑n；Finset.Icc (-↑n) ↑n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.box_succ_eq_sdiff`：box_succ_eq_sdiff (n : Nat) : box (n + 1) = Ic
c (-n.succ : α) n.succ \ Icc (-n) n
· 使用定理 `instIsOrderedRingProd`：∀ {α : Type u_1} {β : Type u_2} [inst : Semiring 
α] [inst_1 : PartialOrder α] [IsOrderedRing α] [inst_3 : Semiring β]   [inst_4 :
 PartialOrd…
· 使用定理 `Finset.card_sdiff_of_subset`：card_sdiff_of_subset (h : s subseteq t) : #
(t \ s) = #t - #s
· 使用定理 `_private.Mathlib.Order.Interval.Finset.Box.0.Finset.Icc_neg_mono`：∀ {α :
 Type u_1} [inst : Ring α] [inst_1 : PartialOrder α] [IsOrderedRing α] [inst_3 :
 LocallyFiniteOrder α],   Monotone fun n => Finset.Icc…
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用引理 `Finset.card_Icc_prod`：Finset.card_Icc_prod (x y : α × β) : #(Icc x y) = 
#(Icc x.1 y.1) * #(Icc x.2 y.2)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `neg_add_rev`：∀ {G : Type u_1} [inst : SubtractionMonoid G] (a b : G), -(
a + b) = -b + -a
· 使用定理 `Prod.fst_natCast`：fst_natCast (n : Nat) : (n : α × β).fst = n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Prod.snd_natCast`：snd_natCast (n : Nat) : (n : α × β).snd = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma card_box_succ (n : ℕ) :
    #(box (n + 1) : Finset (α × β)) =
      #(Icc (-n.succ : α) n.succ) * #(Icc (-n.succ : β) n.succ) -
        #(Icc (-n : α) n) * #(Icc (-n : β) n) := by
  rw [box_succ_eq_sdiff, card_sdiff_of_subset (Icc_neg_mono n.le_succ), Finset.card_Icc_prod,
    Finset.card_Icc_prod]
  simp_rw [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, neg_add_rev, fst_add, fst_neg,
    fst_one, fst_natCast, snd_add, snd_neg, snd_one, snd_natCast]

end Prod

/-! ### `ℤ × ℤ` -/

namespace Int
variable {x : ℤ × ℤ}

attribute [norm_cast] toNat_natCast

/-
**Int.card_box** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：∀ {n : ℕ}, n ≠ 0 → (Finset.box n).card = 8 * n
参数：Finset.box n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Prod.card_box_succ`：∀ {α : Type u_1} {β : Type u_2} [inst : Ring α] [ins
t_1 : PartialOrder α] [IsOrderedRing α] [inst_3 : Ring β]   [inst_4 : PartialOrd
er β] [I…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.card_Icc`：card_Icc : #(Icc a b) = (b + 1 - a).toNat
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `tsub_eq_of_eq_add`：tsub_eq_of_eq_add (h : a = c + b) : a - b = c
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap`：∀ {R : Type u_1} [inst : 
CommSemiring R] {a₁ a₂ b₁ b₂ c₁ c₂ : R},   a₁ + b₁ = c₁ → a₂ + b₂ = c₂ → a₁ + a₂
 + (b₁ + b₂) = c₁ + c₂
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
（共 41 条，此处仅展示前 30 条）
-/
lemma card_box : ∀ {n}, n ≠ 0 → #(box n : Finset (ℤ × ℤ)) = 8 * n
  | n + 1, _ => by
    simp_rw [Prod.card_box_succ, card_Icc, sub_neg_eq_add]
    norm_cast
    refine tsub_eq_of_eq_add ?_
    zify
    ring
/-
**Int.mem_box** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：∀ {x : ℤ × ℤ} {n : ℕ}, x ∈ Finset.box n ↔ max x.1.natAbs x.2.natAbs = n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.box_zero`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : PartialOrder
 α] [inst_2 : LocallyFiniteOrder α] [inst_3 : DecidableEq α],   Finset.box 0 = {
0}
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用引理 `Finset.box_succ_eq_sdiff`：box_succ_eq_sdiff (n : Nat) : box (n + 1) = Ic
c (-n.succ : α) n.succ \ Icc (-n) n
· 使用定理 `instIsOrderedRingProd`：∀ {α : Type u_1} {β : Type u_2} [inst : Semiring 
α] [inst_1 : PartialOrder α] [IsOrderedRing α] [inst_3 : Semiring β]   [inst_4 :
 PartialOrd…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `neg_add_rev`：∀ {G : Type u_1} [inst : SubtractionMonoid G] (a b : G), -(
a + b) = -b + -a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Prod.instIsOrderedAddMonoid`：∀ {α : Type u_1} {β : Type u_2} [inst : Add
CommMonoid α] [inst_1 : Preorder α] [IsOrderedAddMonoid α]   [inst_3 : AddCommMo
noid β] [inst_4 :…
· 使用定理 `Prod.fst_natCast`：fst_natCast (n : Nat) : (n : α × β).fst = n
· 使用定理 `Prod.snd_natCast`：snd_natCast (n : Nat) : (n : α × β).snd = n
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
-/
@[simp] lemma mem_box : ∀ {n}, x ∈ box n ↔ max x.1.natAbs x.2.natAbs = n
  | 0 => by simp [Prod.ext_iff]
  | n + 1 => by
    simp [box_succ_eq_sdiff, Prod.le_def]
    omega

-- TODO: Can this be generalised to locally finite archimedean ordered rings?
/-
**Int.existsUnique_mem_box** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：existsUnique_mem_box (x : Int × Int) : exists! n : Nat, x in box n
参数：x : Int × Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
lemma existsUnique_mem_box (x : ℤ × ℤ) : ∃! n : ℕ, x ∈ box n := by
  use max x.1.natAbs x.2.natAbs; simp only [mem_box, and_self_iff, forall_eq']

end Int

