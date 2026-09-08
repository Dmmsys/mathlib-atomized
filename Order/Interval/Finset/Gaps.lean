/-
Copyright (c) 2025 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
module

public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Prod.Lex

/-!
# Gaps of disjoint closed intervals

This file defines `Finset.intervalGapsWithin` that computes the complement of the union of a
collection of pairwise disjoint subintervals of `[a, b]`.

If `LinearOrder α`, `F` is a finite subset of `α × α` such that for any `(x, y) ∈ F`,
`a ≤ x ≤ y ≤ b` and all such `[x, y]`'s are pairwise disjoint, `h` is a proof of `F.card = k`,
`i` is in `Fin (k + 1)`, we order `F` from left to right as
`(x 0, y 0), ..., (x (k - 1), y (k - 1))`, then `F.intervalGapsWithin h a b i` is
- `(a, b)` if `0 = i = k`;
- `(a, x 0)` if `0 = i < k`;
- `(y (i - 1), x i)` if `0 < i < k`;
- `(y (i - 1), b)` if `0 < i = k`.

Technically, the definition `F.intervalGapsWithin a b` does not require `F` to be pairwise disjoint
or endpoints to be within `[a, b]` or even require that `a ≤ b`, but it makes the most sense if
they are actually satisfied. If they are actually satisfied, then we show that
* `Finset.intervalGapsWithin_mapsTo`, `Finset.intervalGapsWithin_injective`,
  `Finset.intervalGapsWithin_surjOn`:
  `(fun j ↦ ((F.intervalGapsWithin h a b j.castSucc).2, (F.intervalGapsWithin h a b j.succ).1))` is
  a bijection between `Set.Iio k` and `F`.
* `Finset.intervalGapsWithin_le_fst`, `Finset.intervalGapsWithin_snd_le`,
  `Finset.intervalGapsWithin_fst_le_snd`:
  `[(F.intervalGapsWithin h a b j).1, (F.intervalGapsWithin h a b j).2]` is indeed a subinterval of
  `[a, b]` when `j < k`.
* `Finset.intervalGapsWithin_pairwiseDisjoint_Ioc`: the half-closed intervals
  `[(F.intervalGapsWithin h a b j).1, (F.intervalGapsWithin h a b j).2)` are pairwise disjoint
  for `j < k + 1`.
-/

@[expose] public section

open Fin Fin.NatCast Set

section IntervalGapsWithin

namespace Finset

variable {α : Type*} [LinearOrder α] (F : Finset (α × α)) {k : ℕ} (h : F.card = k) (a b : α)
  (j : ℕ)

/-- We order `F` in the lexicographic order as `(x 0, y 0), ..., (x (k - 1), y (k - 1))`.
Then `F.intervalGapsWithin h a b i` is
- `(a, b)` if `0 = i = k`;
- `(a, x 0)` if `0 = i < k`;
- `(y (i - 1), x i)` if `0 < i < k`;
- `(y (i - 1), b)` if `0 < i = k`.
-/
/-
**Finset.intervalGapsWithin** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：intervalGapsWithin (i : Fin (k + 1)) : α × α
参数：i : Fin (k + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We order `F` in the lexicographic order as `(x 0, y 0), ..., (x (k - 1), y (k - 
1))`.
Then `F.intervalGapsWithin h a b i` is
- `(a, b)` if `0 = i = k`;
- `(a, x 0)` if `0 = i < k`;
- `(y (i - 1), x i)` if `0 < i < k`;
- `(y (i - 1), b)` if `0 < i = k`.
-/
noncomputable def intervalGapsWithin (i : Fin (k + 1)) : α × α := (fst, snd) where
  /-- The first coordinate of `F.intervalGapsWithin h a b i` is `a` if `i = 0`,
  `y (i - 1)` otherwise. -/
  fst := if hi : i = 0 then a else
    F.orderEmbOfFin (α := α ×ₗ α) h (i.pred hi) |>.2
  /-- The second coordinate of `F.intervalGapsWithin h a b i` is `b` if `i = k`,
  `x i` otherwise. -/
  snd := if hi : i = last k then b else
    F.orderEmbOfFin (α := α ×ₗ α) h (i.castPred hi) |>.1

@[simp]
/-
**Finset.intervalGapsWithin_zero_fst** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：intervalGapsWithin_zero_fst : (F.intervalGapsWithin h a b 0).1 = a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem intervalGapsWithin_zero_fst : (F.intervalGapsWithin h a b 0).1 = a := by
  simp [intervalGapsWithin, intervalGapsWithin.fst]
/-
**Finset.intervalGapsWithin_succ_fst_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：intervalGapsWithin_succ_fst_of_lt (hj : j < k) : (F.intervalGapsWithin h a
 b (j.succ)).1 = (F.orderEmbOfFin (α
参数：hj : j < k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fin.ext`：∀ {n : ℕ} {a b : Fin n}, ↑a = ↑b → a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem intervalGapsWithin_succ_fst_of_lt (hj : j < k) :
    (F.intervalGapsWithin h a b (j.succ)).1 = (F.orderEmbOfFin (α := α ×ₗ α) h ⟨j, hj⟩).2 := by
  have : (j.succ : Fin (k + 1)) = (⟨j, hj⟩ : Fin k).succ := by ext; simp [hj]
  grind [intervalGapsWithin, intervalGapsWithin.fst]
/-
**Finset.intervalGapsWithin_fst_of_lt_lt** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：intervalGapsWithin_fst_of_lt_lt (hj₁ : 0 < j) (hj₂ : j - 1 < k) : (F.inter
valGapsWithin h a b j).1 = (F.orderEmbOfFin (α
参数：hj₁ : 0 < j；hj₂ : j - 1 < k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Finset.intervalGapsWithin_succ_fst_of_lt`：intervalGapsWithin_succ_fst_of
_lt (hj : j < k) : (F.intervalGapsWithin h a b (j.succ)).1 = (F.orderEmbOfFin (α
-/
theorem intervalGapsWithin_fst_of_lt_lt (hj₁ : 0 < j) (hj₂ : j - 1 < k) :
    (F.intervalGapsWithin h a b j).1 = (F.orderEmbOfFin (α := α ×ₗ α) h ⟨j - 1, hj₂⟩).2 := by
  convert! F.intervalGapsWithin_succ_fst_of_lt h a b (j - 1) hj₂
  omega

@[simp]
/-
**Finset.intervalGapsWithin_last_snd** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：intervalGapsWithin_last_snd : (F.intervalGapsWithin h a b (last k)).2 = b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem intervalGapsWithin_last_snd : (F.intervalGapsWithin h a b (last k)).2 = b := by
  simp [intervalGapsWithin, intervalGapsWithin.snd]
/-
**Finset.intervalGapsWithin_snd_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：intervalGapsWithin_snd_of_lt (hj : j < k) : (F.intervalGapsWithin h a b j)
.2 = (F.orderEmbOfFin (α
参数：hj : j < k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Fin.ext`：∀ {n : ℕ} {a b : Fin n}, ↑a = ↑b → a = b
-/
theorem intervalGapsWithin_snd_of_lt (hj : j < k) :
    (F.intervalGapsWithin h a b j).2 = (F.orderEmbOfFin (α := α ×ₗ α) h ⟨j, hj⟩).1 := by
  have : (j : Fin (k + 1)) ≠ last k := by grind [val_cast_of_lt]
  simp only [intervalGapsWithin, intervalGapsWithin.snd, this, ↓reduceDIte]
  congr
  ext
  simp only [coe_castPred, val_natCast, Nat.mod_succ_eq_iff_lt]
  lia
/-
**Finset.intervalGapsWithin_mapsTo** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：intervalGapsWithin_mapsTo : (Set.Iio k).MapsTo (fun (j : Nat) => ((F.inter
valGapsWithin h a b j).2, (F.intervalGapsWithin h a b j.succ).1)) F
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_Iio`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Iio
 b ↔ x < b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.intervalGapsWithin_snd_of_lt`：intervalGapsWithin_snd_of_lt (hj : 
j < k) : (F.intervalGapsWithin h a b j).2 = (F.orderEmbOfFin (α
· 使用定理 `Finset.intervalGapsWithin_succ_fst_of_lt`：intervalGapsWithin_succ_fst_of
_lt (hj : j < k) : (F.intervalGapsWithin h a b (j.succ)).1 = (F.orderEmbOfFin (α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.orderEmbOfFin_mem`：orderEmbOfFin_mem (s : Finset α) {k : Nat} (h 
: s.card = k) (i : Fin k) : s.orderEmbOfFin h i in s
-/
theorem intervalGapsWithin_mapsTo : (Set.Iio k).MapsTo
    (fun (j : ℕ) ↦ ((F.intervalGapsWithin h a b j).2, (F.intervalGapsWithin h a b j.succ).1))
    F := by
  intro j hj
  rw [mem_Iio] at hj
  simp only [intervalGapsWithin_snd_of_lt, intervalGapsWithin_succ_fst_of_lt,
    SetLike.mem_coe, hj]
  convert! F.orderEmbOfFin_mem h ⟨j, hj⟩ using 1
/-
**Finset.intervalGapsWithin_injOn** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：intervalGapsWithin_injOn : (Set.Iio k).InjOn (fun (j : Nat) => ((F.interva
lGapsWithin h a b j).2, (F.intervalGapsWithin h a b j.succ).1))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_Iio`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Iio
 b ↔ x < b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.intervalGapsWithin_snd_of_lt`：intervalGapsWithin_snd_of_lt (hj : 
j < k) : (F.intervalGapsWithin h a b j).2 = (F.orderEmbOfFin (α
· 使用定理 `Finset.intervalGapsWithin_succ_fst_of_lt`：intervalGapsWithin_succ_fst_of
_lt (hj : j < k) : (F.intervalGapsWithin h a b (j.succ)).1 = (F.orderEmbOfFin (α
-/
theorem intervalGapsWithin_injOn : (Set.Iio k).InjOn
    (fun (j : ℕ) ↦ ((F.intervalGapsWithin h a b j).2, (F.intervalGapsWithin h a b j.succ).1)) := by
  intro j hj j' hj' hjj'
  rw [mem_Iio] at hj hj'
  simp only [hj, hj', intervalGapsWithin_snd_of_lt, intervalGapsWithin_succ_fst_of_lt] at hjj'
  grind [F.orderEmbOfFin (α := α ×ₗ α) h |>.injective hjj']

set_option backward.isDefEq.respectTransparency false in
/-
**Finset.intervalGapsWithin_surjOn** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：intervalGapsWithin_surjOn : (Set.Iio k).SurjOn (fun (j : Nat) => ((F.inter
valGapsWithin h a b j).2, (F.intervalGapsWithin h a b j.succ).1)) F
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.range_orderEmbOfFin`：range_orderEmbOfFin (s : Finset α) {k : Nat}
 (h : s.card = k) : Set.range (s.orderEmbOfFin h) = s
· 使用定理 `Fin.prop`：∀ {n : ℕ} (a : Fin n), ↑a < n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.intervalGapsWithin_snd_of_lt`：intervalGapsWithin_snd_of_lt (hj : 
j < k) : (F.intervalGapsWithin h a b j).2 = (F.orderEmbOfFin (α
· 使用定理 `Finset.intervalGapsWithin_succ_fst_of_lt`：intervalGapsWithin_succ_fst_of
_lt (hj : j < k) : (F.intervalGapsWithin h a b (j.succ)).1 = (F.orderEmbOfFin (α
· 使用定理 `Prod.mk.eta`：∀ {α : Type u_1} {β : Type u_2} {p : α × β}, (p.1, p.2) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem intervalGapsWithin_surjOn : (Set.Iio k).SurjOn
    (fun (j : ℕ) ↦ ((F.intervalGapsWithin h a b j).2, (F.intervalGapsWithin h a b j.succ).1))
    F := by
  intro z hz
  rw [← F.range_orderEmbOfFin h (α := α ×ₗ α)] at hz
  obtain ⟨j, hj⟩ := hz
  use j.val, j.prop
  simp [intervalGapsWithin_snd_of_lt, intervalGapsWithin_succ_fst_of_lt, j.prop, hj,
    -coe_eq_castSucc]
/-
**Finset.intervalGapsWithin_le_fst** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：intervalGapsWithin_le_fst {a b : α} (hFab : forall ⦃z⦄, z in F -> a <= z.1
 ∧ z.1 <= z.2 ∧ z.2 <= b) : a <= (F.intervalGapsWithin h a b j).1
参数：hFab : forall ⦃z⦄, z in F -> a <= z.1 ∧ z.1 <= z.2 ∧ z.2 <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.intervalGapsWithin.congr_simp`：∀ {α : Type u_1} [inst : LinearOrd
er α] (F F_1 : Finset (α × α)) (e_F : F = F_1) {k : ℕ} (h : F.card = k) (a a_1 :
 α),   a = a_1 →     ∀ (b …
· 使用定理 `Fin.natCast_zero`：∀ {n : ℕ} [inst : NeZero n], ↑0 = 0
· 使用定理 `Finset.intervalGapsWithin_zero_fst`：intervalGapsWithin_zero_fst : (F.int
ervalGapsWithin h a b 0).1 = a
· 使用定理 `Finset.intervalGapsWithin_mapsTo`：intervalGapsWithin_mapsTo : (Set.Iio k
).MapsTo (fun (j : Nat) => ((F.intervalGapsWithin h a b j).2, (F.intervalGapsWit
hin h a b j.succ).1)) …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem intervalGapsWithin_le_fst {a b : α} (hFab : ∀ ⦃z⦄, z ∈ F → a ≤ z.1 ∧ z.1 ≤ z.2 ∧ z.2 ≤ b) :
    a ≤ (F.intervalGapsWithin h a b j).1 := by
  wlog hj : j < k + 1 generalizing j
  · grind [cast_val_eq_self]
  by_cases hj : j = 0
  · simp [hj]
  · have := hFab (F.intervalGapsWithin_mapsTo h a b (x := j - 1) (by grind))
    have hj₀ : j - 1 + 1 = j := by lia
    simp only [Nat.succ_eq_add_one, hj₀] at this
    grind
/-
**Finset.intervalGapsWithin_snd_le** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：intervalGapsWithin_snd_le {a b : α} (hFab : forall ⦃z⦄, z in F -> a <= z.1
 ∧ z.1 <= z.2 ∧ z.2 <= b) : (F.intervalGapsWithin h a b j).2 <= b
参数：hFab : forall ⦃z⦄, z in F -> a <= z.1 ∧ z.1 <= z.2 ∧ z.2 <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.intervalGapsWithin.congr_simp`：∀ {α : Type u_1} [inst : LinearOrd
er α] (F F_1 : Finset (α × α)) (e_F : F = F_1) {k : ℕ} (h : F.card = k) (a a_1 :
 α),   a = a_1 →     ∀ (b …
· 使用定理 `Fin.natCast_eq_last`：natCast_eq_last (n) : (n : Fin (n + 1)) = Fin.last 
n
· 使用定理 `Finset.intervalGapsWithin_last_snd`：intervalGapsWithin_last_snd : (F.int
ervalGapsWithin h a b (last k)).2 = b
· 使用定理 `Finset.intervalGapsWithin_mapsTo`：intervalGapsWithin_mapsTo : (Set.Iio k
).MapsTo (fun (j : Nat) => ((F.intervalGapsWithin h a b j).2, (F.intervalGapsWit
hin h a b j.succ).1)) …
-/
theorem intervalGapsWithin_snd_le {a b : α} (hFab : ∀ ⦃z⦄, z ∈ F → a ≤ z.1 ∧ z.1 ≤ z.2 ∧ z.2 ≤ b) :
    (F.intervalGapsWithin h a b j).2 ≤ b := by
  wlog hj : j < k + 1 generalizing j
  · grind [cast_val_eq_self]
  by_cases hj : j = k
  · simp [hj]
  · have := hFab (F.intervalGapsWithin_mapsTo h a b (x := j) (by grind))
    grind

set_option backward.isDefEq.respectTransparency false in
/-
**Finset.intervalGapsWithin_fst_le_snd** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：intervalGapsWithin_fst_le_snd {a b : α} (hab : a <= b) (hFab : forall ⦃z⦄,
 z in F -> a <= z.1 ∧ z.1 <= z.2 ∧ z.2 <= b) (hF : (SetLike.coe F).PairwiseDisjo
int (fun z => Set.Icc z.1 z.2)) : (F.intervalGapsWithin h a b j).1 <= (F.interva
lGapsWithin h a b j).2
参数：hab : a <= b；hFab : forall ⦃z⦄, z in F -> a <= z.1 ∧ z.1 <= z.2 ∧ z.2 <= b；hF
 : (SetLike.coe F).PairwiseDisjoint (fun z => Set.Icc z.1 z.2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.intervalGapsWithin.congr_simp`：∀ {α : Type u_1} [inst : LinearOrd
er α] (F F_1 : Finset (α × α)) (e_F : F = F_1) {k : ℕ} (h : F.card = k) (a a_1 :
 α),   a = a_1 →     ∀ (b …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Fin.natCast_zero`：∀ {n : ℕ} [inst : NeZero n], ↑0 = 0
· 使用定理 `Finset.intervalGapsWithin_zero_fst`：intervalGapsWithin_zero_fst : (F.int
ervalGapsWithin h a b 0).1 = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finset.intervalGapsWithin_last_snd`：intervalGapsWithin_last_snd : (F.int
ervalGapsWithin h a b (last k)).2 = b
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.intervalGapsWithin_mapsTo`：intervalGapsWithin_mapsTo : (Set.Iio k
).MapsTo (fun (j : Nat) => ((F.intervalGapsWithin h a b j).2, (F.intervalGapsWit
hin h a b j.succ).1)) …
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Fin.natCast_eq_last`：natCast_eq_last (n) : (n : Fin (n + 1)) = Fin.last 
n
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finset.intervalGapsWithin_fst_of_lt_lt`：intervalGapsWithin_fst_of_lt_lt 
(hj₁ : 0 < j) (hj₂ : j - 1 < k) : (F.intervalGapsWithin h a b j).1 = (F.orderEmb
OfFin (α
· 使用定理 `Finset.intervalGapsWithin_snd_of_lt`：intervalGapsWithin_snd_of_lt (hj : 
j < k) : (F.intervalGapsWithin h a b j).2 = (F.orderEmbOfFin (α
· 使用定理 `Finset.orderEmbOfFin_mem`：orderEmbOfFin_mem (s : Finset α) {k : Nat} (h 
: s.card = k) (i : Fin k) : s.orderEmbOfFin h i in s
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `RelEmbedding.injective`：injective (f : r ↪r s) : Injective f
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
（共 34 条，此处仅展示前 30 条）
-/
theorem intervalGapsWithin_fst_le_snd {a b : α} (hab : a ≤ b)
    (hFab : ∀ ⦃z⦄, z ∈ F → a ≤ z.1 ∧ z.1 ≤ z.2 ∧ z.2 ≤ b)
    (hF : (SetLike.coe F).PairwiseDisjoint (fun z ↦ Set.Icc z.1 z.2)) :
    (F.intervalGapsWithin h a b j).1 ≤ (F.intervalGapsWithin h a b j).2 := by
  wlog hj : j < k + 1 generalizing j
  · convert! this (j : Fin (k + 1)) (by grind) using 3 <;> grind [cast_val_eq_self]
  by_cases hj₁ : j = 0
  · simp only [hj₁]
    by_cases hk : 0 = k
    · simp only [natCast_zero, intervalGapsWithin_zero_fst]
      simp [show 0 = last k by grind, hab]
    · exact hFab (F.intervalGapsWithin_mapsTo h a b (x := 0) (by grind)) |>.left
  have hk : k - 1 + 1 = k := by omega
  by_cases hj₂ : j = k
  · simp only [hj₂, natCast_eq_last, intervalGapsWithin_last_snd, ge_iff_le]
    convert! hFab (F.intervalGapsWithin_mapsTo h a b (x := j - 1) (by grind)) |>.right.right using 1
    simp [hj₂, hk]
  rw [intervalGapsWithin_fst_of_lt_lt (hj₁ := by omega) (hj₂ := by omega),
      intervalGapsWithin_snd_of_lt (hj := by omega)]
  have hj₃ : (⟨j - 1, by omega⟩ : Fin k) ≠ ⟨j, by omega⟩ := by grind
  set G := F.orderEmbOfFin (α := α ×ₗ α) h
  have := hF (by simp [G, F.orderEmbOfFin_mem (α := α ×ₗ α)])
    (by simp [G, F.orderEmbOfFin_mem (α := α ×ₗ α)]) (G.injective.ne (hj₃))
  contrapose! this
  simp only [Set.not_disjoint_iff, Set.mem_Icc]
  use (G ⟨j, by omega⟩).1
  have hG : (G ⟨j - 1, by omega⟩).1 ≤ (G ⟨j, by omega⟩).1 :=
    Prod.Lex.le_iff'.mp (G.monotone (by simp [le_iff_val_le_val])) |>.left
  have hFabi := hFab (z := G ⟨j, by omega⟩) (by simp [G, F.orderEmbOfFin_mem (α := α ×ₗ α)])
  simp [hFabi, this.le, hG]
/-
**Finset.intervalGapsWithin_pairwiseDisjoint_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Fins
et`。
形式化陈述：intervalGapsWithin_pairwiseDisjoint_Ioc {a b : α} (hFab : forall ⦃z⦄, z in
 F -> a <= z.1 ∧ z.1 <= z.2 ∧ z.2 <= b) : (Set.Iio (k + 1)).PairwiseDisjoint (fu
n (j : Nat) => Set.Ioc (F.intervalGapsWithin h a b j).1 (F.intervalGapsWithin h 
a b j).2)
参数：hFab : forall ⦃z⦄, z in F -> a <= z.1 ∧ z.1 <= z.2 ∧ z.2 <= b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.onFun.eq_1`：∀ {α : Sort u₁} {β : Sort u₂} {φ : Sort u₃} (f : β 
→ β → φ) (g : α → β) (x y : α),   Function.onFun f g x y = f (g x) (g y)
· 使用定理 `Set.disjoint_iff_inter_eq_empty`：disjoint_iff_inter_eq_empty : Disjoint 
s t ↔ s inter t = ∅
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finset.intervalGapsWithin_mapsTo`：intervalGapsWithin_mapsTo : (Set.Iio k
).MapsTo (fun (j : Nat) => ((F.intervalGapsWithin h a b j).2, (F.intervalGapsWit
hin h a b j.succ).1)) …
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Finset.intervalGapsWithin.congr_simp`：∀ {α : Type u_1} [inst : LinearOrd
er α] (F F_1 : Finset (α × α)) (e_F : F = F_1) {k : ℕ} (h : F.card = k) (a a_1 :
 α),   a = a_1 →     ∀ (b …
· 使用定理 `Finset.intervalGapsWithin_snd_of_lt`：intervalGapsWithin_snd_of_lt (hj : 
j < k) : (F.intervalGapsWithin h a b j).2 = (F.orderEmbOfFin (α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Prod.Lex.le_iff'`：le_iff' {x y : α ×ₗ β} : x <= y ↔ (ofLex x).1 <= (ofLe
x y).1 ∧ ((ofLex x).1 = (ofLex y).1 -> (ofLex x).2 <= (ofLex y).2)
· 使用定理 `OrderEmbedding.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorde
r α] [inst_1 : Preorder β] (f : α ↪o β), Monotone ⇑f
· 使用定理 `Set.mem_Iio`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Iio
 b ↔ x < b
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
theorem intervalGapsWithin_pairwiseDisjoint_Ioc {a b : α}
    (hFab : ∀ ⦃z⦄, z ∈ F → a ≤ z.1 ∧ z.1 ≤ z.2 ∧ z.2 ≤ b) :
    (Set.Iio (k + 1)).PairwiseDisjoint (fun (j : ℕ) ↦
      Set.Ioc (F.intervalGapsWithin h a b j).1 (F.intervalGapsWithin h a b j).2) := by
  intro j hj j' hj' hjj'
  rw [mem_Iio] at hj hj'
  wlog hij' : j < j' generalizing j j'
  · exact (this hj' hj hjj'.symm (by omega)).symm
  rw [Function.onFun, Set.disjoint_iff_inter_eq_empty]
  suffices (F.intervalGapsWithin h a b j).2 ≤ (F.intervalGapsWithin h a b j').1 by grind
  have hj'₀ : j' - 1 + 1 = j' := by omega
  have := hFab (F.intervalGapsWithin_mapsTo h a b (x := j' - 1) (by grind)) |>.right.left
  simp only [Nat.succ_eq_add_one, hj'₀] at this
  grw [← this]
  rw [intervalGapsWithin_snd_of_lt (hj := by omega),
      intervalGapsWithin_snd_of_lt (hj := by omega)]
  exact Prod.Lex.le_iff'.mp (F.orderEmbOfFin (α := α ×ₗ α) h |>.monotone (by grind)) |>.left

end Finset

end IntervalGapsWithin

