/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta, Doga Can Sertbas
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Order.ConditionallyCompleteLattice.Indexed

import Mathlib.Tactic.Rify

/-!
# Schnirelmann density

We define the Schnirelmann density of a set `A` of natural numbers as
$inf_{n > 0} |A ∩ {1,...,n}| / n$. As this density is very sensitive to changes in small values,
we must exclude `0` from the infimum, and from the intersection.

## Main statements

* Simple bounds on the Schnirelmann density, that it is between 0 and 1 are given in
  `schnirelmannDensity_nonneg` and `schnirelmannDensity_le_one`.
* `schnirelmannDensity_le_of_notMem`: If `k ∉ A`, the density can be easily upper-bounded by
  `1 - k⁻¹`

## Implementation notes

Despite the definition being noncomputable, we include a decidable instance argument, since this
makes the definition easier to use in explicit cases.
Further, we use `Finset.Ioc` rather than a set intersection since the set is finite by construction,
which reduces the proof obligations later that would arise with `Nat.card`.

## TODO
* Give other calculations of the density, for example powers and their sumsets.
* Define other densities like the lower and upper asymptotic density, and the natural density,
  and show how these relate to the Schnirelmann density.
* Prove Schnirelmann's theorem and Mann's theorem on the subadditivity of this density.

## References

* [Ruzsa, Imre, *Sumsets and structure*][ruzsa2009]
-/

@[expose] public section

open Finset

/-- The Schnirelmann density is defined as the infimum of $|A ∩ {1, ..., n}| / n$ as n ranges over
the positive naturals. -/
/-
**schnirelmannDensity** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：schnirelmannDensity (A : Set Nat) [DecidablePred (· in A)] : Real
参数：A : Set Nat；· in A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Schnirelmann density is defined as the infimum of $|A ∩ {1, ..., n}| / n$ as
 n ranges over
the positive naturals.
-/
noncomputable def schnirelmannDensity (A : Set ℕ) [DecidablePred (· ∈ A)] : ℝ :=
  ⨅ n : {n : ℕ // 0 < n}, #{a ∈ Ioc 0 n | a ∈ A} / n

section

variable {A : Set ℕ} [DecidablePred (· ∈ A)]

/-
**schnirelmannDensity_nonneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：schnirelmannDensity_nonneg : 0 <= schnirelmannDensity A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.iInf_nonneg`：iInf_nonneg (hf : forall i, 0 <= f i) : 0 <= iInf f
· 使用引理 `div_nonneg`：div_nonneg (ha : 0 <= a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
lemma schnirelmannDensity_nonneg : 0 ≤ schnirelmannDensity A :=
  Real.iInf_nonneg (fun _ => by positivity)
/-
**schnirelmannDensity_le_div** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：schnirelmannDensity_le_div {n : Nat} (hn : n != 0) : schnirelmannDensity A
 <= #{a in Ioc 0 n | a in A} / n
参数：hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ciInf_le`：ciInf_le {f : ι -> α} (H : BddBelow (range f)) (c : ι) : iInf 
f <= f c
· 使用引理 `div_nonneg`：div_nonneg (ha : 0 <= a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
-/
lemma schnirelmannDensity_le_div {n : ℕ} (hn : n ≠ 0) :
    schnirelmannDensity A ≤ #{a ∈ Ioc 0 n | a ∈ A} / n :=
  ciInf_le ⟨0, fun _ ⟨_, hx⟩ => hx ▸ by positivity⟩ (⟨n, hn.bot_lt⟩ : {n : ℕ // 0 < n})

/--
For any natural `n`, the Schnirelmann density multiplied by `n` is bounded by `|A ∩ {1, ..., n}|`.
Note this property fails for the natural density.
-/
/-
**schnirelmannDensity_mul_le_card_filter** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：schnirelmannDensity_mul_le_card_filter {n : Nat} : schnirelmannDensity A *
 n <= #{a in Ioc 0 n | a in A}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Finset.filter.congr_simp`：∀ {α : Type u_1} (p p_1 : α → Prop),   p = p_1
 →     ∀ {inst : DecidablePred p} [inst_1 : DecidablePred p_1] (s s_1 : Finset α
),       s = s…
· 使用定理 `Finset.Ioc_eq_empty_of_le`：Ioc_eq_empty_of_le (h : b <= a) : Ioc a b = ∅
· 使用定理 `Finset.filter_empty`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidablePr
ed p], Finset.filter p ∅ = ∅
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `le_div_iff₀`：le_div_iff₀ (hc : 0 < c) : a <= b / c ↔ a * c <= b
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos'`：cast_pos' {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `lt_of_le_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用引理 `schnirelmannDensity_le_div`：schnirelmannDensity_le_div {n : Nat} (hn : n
 != 0) : schnirelmannDensity A <= #{a in Ioc 0 n | a in A} / n

--- 原说明 ---
For any natural `n`, the Schnirelmann density multiplied by `n` is bounded by `|
A ∩ {1, ..., n}|`.
Note this property fails for the natural density.
-/
lemma schnirelmannDensity_mul_le_card_filter {n : ℕ} :
    schnirelmannDensity A * n ≤ #{a ∈ Ioc 0 n | a ∈ A} := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  exact (le_div_iff₀ (by positivity)).1 (schnirelmannDensity_le_div hn)

/--
To show the Schnirelmann density is upper bounded by `x`, it suffices to show
`|A ∩ {1, ..., n}| / n ≤ x`, for any chosen positive value of `n`.

We provide `n` explicitly here to make this lemma more easily usable in `apply` or `refine`.
This lemma is analogous to `ciInf_le_of_le`.
-/
/-
**schnirelmannDensity_le_of_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：schnirelmannDensity_le_of_le {x : Real} (n : Nat) (hn : n != 0) (hx : #{a 
in Ioc 0 n | a in A} / n <= x) : schnirelmannDensity A <= x
参数：n : Nat；hn : n != 0；hx : #{a in Ioc 0 n | a in A} / n <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `schnirelmannDensity_le_div`：schnirelmannDensity_le_div {n : Nat} (hn : n
 != 0) : schnirelmannDensity A <= #{a in Ioc 0 n | a in A} / n

--- 原说明 ---
To show the Schnirelmann density is upper bounded by `x`, it suffices to show
`|A ∩ {1, ..., n}| / n ≤ x`, for any chosen positive value of `n`.

We provide `n` explicitly here to make this lemma more easily usable in `apply` 
or `refine`.
This lemma is analogous to `ciInf_le_of_le`.
-/
lemma schnirelmannDensity_le_of_le {x : ℝ} (n : ℕ) (hn : n ≠ 0)
    (hx : #{a ∈ Ioc 0 n | a ∈ A} / n ≤ x) : schnirelmannDensity A ≤ x :=
  (schnirelmannDensity_le_div hn).trans hx
/-
**schnirelmannDensity_le_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：schnirelmannDensity_le_one : schnirelmannDensity A <= 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `schnirelmannDensity_le_of_le`：schnirelmannDensity_le_of_le {x : Real} (n
 : Nat) (hn : n != 0) (hx : #{a in Ioc 0 n | a in A} / n <= x) : schnirelmannDen
sity A <= x
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Nat.cast_le_one`：cast_le_one : (n : α) <= 1 ↔ n <= 1
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Finset.card_filter_le`：card_filter_le (s : Finset α) (p : α -> Prop) [De
cidablePred p] : #(s.filter p) <= #s
-/
lemma schnirelmannDensity_le_one : schnirelmannDensity A ≤ 1 :=
  schnirelmannDensity_le_of_le 1 one_ne_zero <|
    by rw [Nat.cast_one, div_one, Nat.cast_le_one]; exact card_filter_le _ _

/--
If `k` is omitted from the set, its Schnirelmann density is upper bounded by `1 - k⁻¹`.
-/
/-
**schnirelmannDensity_le_of_notMem** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：schnirelmannDensity_le_of_notMem {k : Nat} (hk : k ∉ A) : schnirelmannDens
ity A <= 1 - (k⁻¹ : Real)
参数：hk : k ∉ A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用引理 `schnirelmannDensity_le_one`：schnirelmannDensity_le_one : schnirelmannDen
sity A <= 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `schnirelmannDensity_le_of_le`：schnirelmannDensity_le_of_le {x : Real} (n
 : Nat) (hn : n != 0) (hx : #{a in Ioc 0 n | a in A} / n <= x) : schnirelmannDen
sity A <= x
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `one_sub_div`：one_sub_div {a b : K} (h : b != 0) : 1 - a / b = (b - a) / 
b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos`：cast_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRing 
α] [Nontrivial α] {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用引理 `div_le_div_of_nonneg_right`：div_le_div_of_nonneg_right (hab : a <= b) (h
c : 0 <= c) : a / c <= b / c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Nat.cast_pred`：∀ {R : Type u} [inst : AddGroupWithOne R] {n : ℕ}, 0 < n 
→ ↑(n - 1) = ↑n - 1
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Finset.Ioo_insert_right`：Ioo_insert_right (h : a < b) : insert b (Ioo a 
b) = Ioc a b
· 使用定理 `Finset.filter_insert`：filter_insert (a : α) (s : Finset α) : (insert a s
).filter p = if p a then insert a (s.filter p) else s.filter p
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Finset.filter_subset`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidableP
red p] (s : Finset α), Finset.filter p s ⊆ s
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
If `k` is omitted from the set, its Schnirelmann density is upper bounded by `1 
- k⁻¹`.
-/
lemma schnirelmannDensity_le_of_notMem {k : ℕ} (hk : k ∉ A) :
    schnirelmannDensity A ≤ 1 - (k⁻¹ : ℝ) := by
  rcases k.eq_zero_or_pos with rfl | hk'
  · simpa using schnirelmannDensity_le_one
  apply schnirelmannDensity_le_of_le k hk'.ne'
  rw [← one_div, one_sub_div (Nat.cast_pos.2 hk').ne']
  gcongr
  rw [← Nat.cast_pred hk', Nat.cast_le]
  suffices {a ∈ Ioc 0 k | a ∈ A} ⊆ Ioo 0 k from (card_le_card this).trans_eq (by simp)
  rw [← Ioo_insert_right hk', filter_insert, if_neg hk]
  exact filter_subset _ _

/-- The Schnirelmann density of a set not containing `1` is `0`. -/
/-
**schnirelmannDensity_eq_zero_of_one_notMem** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：schnirelmannDensity_eq_zero_of_one_notMem (h : 1 ∉ A) : schnirelmannDensit
y A = 0
参数：h : 1 ∉ A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `schnirelmannDensity_le_of_notMem`：schnirelmannDensity_le_of_notMem {k : 
Nat} (hk : k ∉ A) : schnirelmannDensity A <= 1 - (k⁻¹ : Real)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用引理 `schnirelmannDensity_nonneg`：schnirelmannDensity_nonneg : 0 <= schnirelma
nnDensity A

--- 原说明 ---
The Schnirelmann density of a set not containing `1` is `0`.
-/
lemma schnirelmannDensity_eq_zero_of_one_notMem (h : 1 ∉ A) : schnirelmannDensity A = 0 :=
  ((schnirelmannDensity_le_of_notMem h).trans (by simp)).antisymm schnirelmannDensity_nonneg

/-- The Schnirelmann density is increasing with the set. -/
/-
**schnirelmannDensity_le_of_subset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：schnirelmannDensity_le_of_subset {B : Set Nat} [DecidablePred (· in B)] (h
 : A subseteq B) : schnirelmannDensity A <= schnirelmannDensity B
参数：· in B；h : A subseteq B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ciInf_mono`：ciInf_mono {f g : ι -> α} (B : BddBelow (range f)) (H : fora
ll x, f x <= g x) : iInf f <= iInf g
· 使用引理 `div_nonneg`：div_nonneg (ha : 0 <= a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `div_le_div_of_nonneg_right`：div_le_div_of_nonneg_right (hab : a <= b) (h
c : 0 <= c) : a / c <= b / c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Nat.mono_cast`：mono_cast : Monotone (Nat.cast : Nat -> α)
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
· 使用定理 `Finset.monotone_filter_right`：∀ {α : Type u_1} (s : Finset α) ⦃p q : α →
 Prop⦄ [inst : DecidablePred p] [inst_1 : DecidablePred q],   (∀ a ∈ s, p a → q 
a) → Finset.filter…
· 使用定理 `Set.mem_of_subset_of_mem`：∀ {α : Type u} {s₁ s₂ : Set α} {a : α}, s₁ ⊆ s
₂ → a ∈ s₁ → a ∈ s₂

--- 原说明 ---
The Schnirelmann density is increasing with the set.
-/
lemma schnirelmannDensity_le_of_subset {B : Set ℕ} [DecidablePred (· ∈ B)] (h : A ⊆ B) :
    schnirelmannDensity A ≤ schnirelmannDensity B :=
  ciInf_mono ⟨0, fun _ ⟨_, hx⟩ ↦ hx ▸ by positivity⟩ fun _ ↦ by gcongr

/-- The Schnirelmann density of `A` is `1` if and only if `A` contains all the positive naturals. -/
/-
**schnirelmannDensity_eq_one_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：schnirelmannDensity_eq_one_iff : schnirelmannDensity A = 1 ↔ {0}ᶜ subseteq
 A
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `le_antisymm_iff`：le_antisymm_iff : a = b ↔ a <= b ∧ b <= a
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用引理 `schnirelmannDensity_le_one`：schnirelmannDensity_le_one : schnirelmannDen
sity A <= 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_imp_not`：not_imp_not : ¬a -> ¬b ↔ b -> a
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用引理 `schnirelmannDensity_le_of_notMem`：schnirelmannDensity_le_of_notMem {k : 
Nat} (hk : k ∉ A) : schnirelmannDensity A <= 1 - (k⁻¹ : Real)
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `le_ciInf`：le_ciInf [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, c <=
 f x) : c <= iInf f
· 使用定理 `nonempty_gt`：∀ {α : Type u_1} [inst : LT α] [NoMaxOrder α] (a : α), None
mpty { x // a < x }
· 使用定理 `one_le_div`：one_le_div (hb : 0 < b) : 1 <= a / b ↔ b <= a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos`：cast_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRing 
α] [Nontrivial α] {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Finset.filter_true_of_mem`：∀ {α : Type u_1} {p : α → Prop} [inst : Decid
ablePred p] {s : Finset α}, (∀ x ∈ s, p x) → Finset.filter p s = s
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
The Schnirelmann density of `A` is `1` if and only if `A` contains all the posit
ive naturals.
-/
lemma schnirelmannDensity_eq_one_iff : schnirelmannDensity A = 1 ↔ {0}ᶜ ⊆ A := by
  rw [le_antisymm_iff, and_iff_right schnirelmannDensity_le_one]
  constructor
  · rw [← not_imp_not, not_le]
    simp only [Set.not_subset, forall_exists_index, and_imp]
    intro x hx hx'
    apply (schnirelmannDensity_le_of_notMem hx').trans_lt
    simpa only [one_div, sub_lt_self_iff, inv_pos, Nat.cast_pos, pos_iff_ne_zero] using! hx
  · intro h
    refine le_ciInf fun ⟨n, hn⟩ => ?_
    rw [one_le_div (Nat.cast_pos.2 hn), Nat.cast_le, filter_true_of_mem, Nat.card_Ioc, Nat.sub_zero]
    rintro x hx
    exact h (mem_Ioc.1 hx).1.ne'

/-- The Schnirelmann density of `A` containing `0` is `1` if and only if `A` is the naturals. -/
/-
**schnirelmannDensity_eq_one_iff_of_zero_mem** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：schnirelmannDensity_eq_one_iff_of_zero_mem (hA : 0 in A) : schnirelmannDen
sity A = 1 ↔ A = Set.univ
参数：hA : 0 in A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `schnirelmannDensity_eq_one_iff`：schnirelmannDensity_eq_one_iff : schnire
lmannDensity A = 1 ↔ {0}ᶜ subseteq A
· 使用定理 `Set.eq_univ_of_forall`：eq_univ_of_forall {s : Set α} : (forall x, x in s
) -> s = univ
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ

--- 原说明 ---
The Schnirelmann density of `A` containing `0` is `1` if and only if `A` is the 
naturals.
-/
lemma schnirelmannDensity_eq_one_iff_of_zero_mem (hA : 0 ∈ A) :
    schnirelmannDensity A = 1 ↔ A = Set.univ := by
  rw [schnirelmannDensity_eq_one_iff]
  constructor
  · refine fun h => Set.eq_univ_of_forall fun x => ?_
    rcases eq_or_ne x 0 with rfl | hx
    · exact hA
    · exact h hx
  · rintro rfl
    exact Set.subset_univ {0}ᶜ
/-
**le_schnirelmannDensity_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_schnirelmannDensity_iff {x : Real} : x <= schnirelmannDensity A ↔ foral
l n : Nat, 0 < n -> x <= #{a in Ioc 0 n | a in A} / n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `le_ciInf_iff`：le_ciInf_iff [Nonempty ι] {f : ι -> α} {a : α} (hf : BddBe
low (range f)) : a <= iInf f ↔ forall i, a <= f i
· 使用定理 `nonempty_gt`：∀ {α : Type u_1} [inst : LT α] [NoMaxOrder α] (a : α), None
mpty { x // a < x }
· 使用引理 `div_nonneg`：div_nonneg (ha : 0 <= a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Subtype.forall`：∀ {α : Sort u} {p : α → Prop} {q : { a // p a } → Prop},
 (∀ (x : { a // p a }), q x) ↔ ∀ (a : α) (b : p a), q ⟨a, b⟩
-/
lemma le_schnirelmannDensity_iff {x : ℝ} :
    x ≤ schnirelmannDensity A ↔ ∀ n : ℕ, 0 < n → x ≤ #{a ∈ Ioc 0 n | a ∈ A} / n :=
  (le_ciInf_iff ⟨0, fun _ ⟨_, hx⟩ => hx ▸ by positivity⟩).trans Subtype.forall
/-
**schnirelmannDensity_lt_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：schnirelmannDensity_lt_iff {x : Real} : schnirelmannDensity A < x ↔ exists
 n : Nat, 0 < n ∧ #{a in Ioc 0 n | a in A} / n < x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用引理 `le_schnirelmannDensity_iff`：le_schnirelmannDensity_iff {x : Real} : x <=
 schnirelmannDensity A ↔ forall n : Nat, 0 < n -> x <= #{a in Ioc 0 n | a in A} 
/ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma schnirelmannDensity_lt_iff {x : ℝ} :
    schnirelmannDensity A < x ↔ ∃ n : ℕ, 0 < n ∧ #{a ∈ Ioc 0 n | a ∈ A} / n < x := by
  rw [← not_le, le_schnirelmannDensity_iff]; simp
/-
**schnirelmannDensity_le_iff_forall** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：schnirelmannDensity_le_iff_forall {x : Real} : schnirelmannDensity A <= x 
↔ forall ε : Real, 0 < ε -> exists n : Nat, 0 < n ∧ #{a in Ioc 0 n | a in A} / n
 < x + ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_iff_forall_pos_lt_add`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : L
inearOrder α] [AddLeftMono α] {a b : α},   a ≤ b ↔ ∀ (ε : α), 0 < ε → a < b + ε
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma schnirelmannDensity_le_iff_forall {x : ℝ} :
    schnirelmannDensity A ≤ x ↔
      ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, 0 < n ∧ #{a ∈ Ioc 0 n | a ∈ A} / n < x + ε := by
  rw [le_iff_forall_pos_lt_add]
  simp only [schnirelmannDensity_lt_iff]
/-
**schnirelmannDensity_congr'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：schnirelmannDensity_congr' {B : Set Nat} [DecidablePred (· in B)] (h : for
all n > 0, n in A ↔ n in B) : schnirelmannDensity A = schnirelmannDensity B
参数：· in B；h : forall n > 0, n in A ↔ n in B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `schnirelmannDensity.eq_1`：∀ (A : Set ℕ) [inst : DecidablePred fun x => x
 ∈ A],   schnirelmannDensity A = ⨅ n, ↑{a ∈ Finset.Ioc 0 ↑n | a ∈ A}.card / ↑↑n
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma schnirelmannDensity_congr' {B : Set ℕ} [DecidablePred (· ∈ B)]
    (h : ∀ n > 0, n ∈ A ↔ n ∈ B) : schnirelmannDensity A = schnirelmannDensity B := by
  rw [schnirelmannDensity, schnirelmannDensity]; congr; ext ⟨n, hn⟩; congr 3; ext x; simp_all

/-- The Schnirelmann density is unaffected by adding `0`. -/
/-
**schnirelmannDensity_insert_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {A : Set ℕ} [inst : DecidablePred fun x => x ∈ A] [inst_1 : DecidablePre
d fun x => x ∈ insert 0 A],   schnirelmannDensity (insert 0 A) = schnirelmannDen
sity A
参数：insert 0 A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `schnirelmannDensity_congr'`：schnirelmannDensity_congr' {B : Set Nat} [De
cidablePred (· in B)] (h : forall n > 0, n in A ↔ n in B) : schnirelmannDensity 
A = schnirelmann…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The Schnirelmann density is unaffected by adding `0`.
-/
@[simp] lemma schnirelmannDensity_insert_zero [DecidablePred (· ∈ insert 0 A)] :
    schnirelmannDensity (insert 0 A) = schnirelmannDensity A :=
  schnirelmannDensity_congr' (by aesop)

/-- The Schnirelmann density is unaffected by removing `0`. -/
/-
**schnirelmannDensity_sdiff_singleton_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：schnirelmannDensity_sdiff_singleton_zero [DecidablePred (· in A \ {0})] : 
schnirelmannDensity (A \ {0}) = schnirelmannDensity A
参数：· in A \ {0}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `schnirelmannDensity_congr'`：schnirelmannDensity_congr' {B : Set Nat} [De
cidablePred (· in B)] (h : forall n > 0, n in A ↔ n in B) : schnirelmannDensity 
A = schnirelmann…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The Schnirelmann density is unaffected by removing `0`.
-/
lemma schnirelmannDensity_sdiff_singleton_zero [DecidablePred (· ∈ A \ {0})] :
    schnirelmannDensity (A \ {0}) = schnirelmannDensity A :=
  schnirelmannDensity_congr' (by aesop)

@[deprecated (since := "2026-06-03")]
alias schnirelmannDensity_diff_singleton_zero := schnirelmannDensity_sdiff_singleton_zero
/-
**schnirelmannDensity_congr** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：schnirelmannDensity_congr {B : Set Nat} [DecidablePred (· in B)] (h : A = 
B) : schnirelmannDensity A = schnirelmannDensity B
参数：· in B；h : A = B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `schnirelmannDensity_congr'`：schnirelmannDensity_congr' {B : Set Nat} [De
cidablePred (· in B)] (h : forall n > 0, n in A ↔ n in B) : schnirelmannDensity 
A = schnirelmann…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma schnirelmannDensity_congr {B : Set ℕ} [DecidablePred (· ∈ B)] (h : A = B) :
    schnirelmannDensity A = schnirelmannDensity B :=
  schnirelmannDensity_congr' (by simp_all)

/--
If the Schnirelmann density is `0`, there is a positive natural for which
`|A ∩ {1, ..., n}| / n < ε`, for any positive `ε`.
Note this cannot be improved to `∃ᶠ n : ℕ in atTop`, as can be seen by `A = {1}ᶜ`.
-/
/-
**exists_of_schnirelmannDensity_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：exists_of_schnirelmannDensity_eq_zero {ε : Real} (hε : 0 < ε) (hA : schnir
elmannDensity A = 0) : exists n, 0 < n ∧ #{a in Ioc 0 n | a in A} / n < ε
参数：hε : 0 < ε；hA : schnirelmannDensity A = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf_zero`：∀ {R : Type u_1} [inst :
 CommSemiring R] {a b : R} (x : R) (e : ℕ),   Mathlib.Meta.NormNum.IsNat (a + b)
 0 → Mathlib.Meta.NormNum.IsNat (x ^…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Linarith.add_lt_of_neg_of_le`：add_lt_of_neg_of_le [IsStri
ctOrderedRing α] {a b c : α} (ha : a < 0) (hbc : b <= c) : a + b < c
· 使用定理 `Mathlib.Tactic.Linarith.lt_of_lt_of_eq`：lt_of_lt_of_eq {a b : α} (ha : a
 < 0) (hb : b = 0) : a + b < 0
· 使用定理 `Mathlib.Tactic.Linarith.sub_neg_of_lt`：sub_neg_of_lt [IsOrderedRing α] {
a b : α} : a < b -> a - b < 0
（共 37 条，此处仅展示前 30 条）

--- 原说明 ---
If the Schnirelmann density is `0`, there is a positive natural for which
`|A ∩ {1, ..., n}| / n < ε`, for any positive `ε`.
Note this cannot be improved to `∃ᶠ n : ℕ in atTop`, as can be seen by `A = {1}ᶜ
`.
-/
lemma exists_of_schnirelmannDensity_eq_zero {ε : ℝ} (hε : 0 < ε) (hA : schnirelmannDensity A = 0) :
    ∃ n, 0 < n ∧ #{a ∈ Ioc 0 n | a ∈ A} / n < ε := by
  by_contra! h
  rw [← le_schnirelmannDensity_iff] at h
  linarith

end

/-
**schnirelmannDensity_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：schnirelmannDensity ∅ = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `schnirelmannDensity_eq_zero_of_one_notMem`：schnirelmannDensity_eq_zero_o
f_one_notMem (h : 1 ∉ A) : schnirelmannDensity A = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
@[simp] lemma schnirelmannDensity_empty : schnirelmannDensity ∅ = 0 :=
  schnirelmannDensity_eq_zero_of_one_notMem (by simp)

/-- The Schnirelmann density of any finset is `0`. -/
/-
**schnirelmannDensity_finset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：schnirelmannDensity_finset (A : Finset Nat) : schnirelmannDensity A = 0
参数：A : Finset Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用引理 `div_lt_iff₀`：div_lt_iff₀ (hc : 0 < c) : b / c < a ↔ b < a * c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos`：cast_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRing 
α] [Nontrivial α] {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `div_lt_iff₀'`：div_lt_iff₀' (hc : 0 < c) : b / c < a ↔ b < c * a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Nat.cast_add_one`：cast_add_one (n : Nat) : ((n + 1 : Nat) : R) = n + 1
· 使用定理 `LT.lt.trans_le'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b < a
 → c ≤ b → c < a
· 使用定理 `Nat.lt_floor_add_one`：lt_floor_add_one (a : R) : a < ⌊a⌋₊ + 1
· 使用引理 `div_le_div_of_nonneg_right`：div_le_div_of_nonneg_right (hab : a <= b) (h
c : 0 <= c) : a / c <= b / c
· 使用定理 `Nat.mono_cast`：mono_cast : Monotone (Nat.cast : Nat -> α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
（共 39 条，此处仅展示前 30 条）

--- 原说明 ---
The Schnirelmann density of any finset is `0`.
-/
lemma schnirelmannDensity_finset (A : Finset ℕ) : schnirelmannDensity A = 0 := by
  refine le_antisymm ?_ schnirelmannDensity_nonneg
  simp only [schnirelmannDensity_le_iff_forall, zero_add]
  intro ε hε
  wlog hε₁ : ε ≤ 1 generalizing ε
  · obtain ⟨n, hn, hn'⟩ := this 1 zero_lt_one le_rfl
    exact ⟨n, hn, hn'.trans_le (le_of_not_ge hε₁)⟩
  let n : ℕ := ⌊#A / ε⌋₊ + 1
  have hn : 0 < n := Nat.succ_pos _
  use n, hn
  rw [div_lt_iff₀ (Nat.cast_pos.2 hn), ← div_lt_iff₀' hε, Nat.cast_add_one]
  exact (Nat.lt_floor_add_one _).trans_le' <| by gcongr; simp [subset_iff]

/-- The Schnirelmann density of any finite set is `0`. -/
/-
**schnirelmannDensity_finite** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：schnirelmannDensity_finite {A : Set Nat} [DecidablePred (· in A)] (hA : A.
Finite) : schnirelmannDensity A = 0
参数：· in A；hA : A.Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `schnirelmannDensity.congr_simp`：∀ (A A_1 : Set ℕ),   A = A_1 →     ∀ {in
st : DecidablePred fun x => x ∈ A} [inst_1 : DecidablePred fun x => x ∈ A_1],   
    schnirelmannDens…
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用引理 `schnirelmannDensity_finset`：schnirelmannDensity_finset (A : Finset Nat) 
: schnirelmannDensity A = 0

--- 原说明 ---
The Schnirelmann density of any finite set is `0`.
-/
lemma schnirelmannDensity_finite {A : Set ℕ} [DecidablePred (· ∈ A)] (hA : A.Finite) :
    schnirelmannDensity A = 0 := by simpa using schnirelmannDensity_finset hA.toFinset
/-
**schnirelmannDensity_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：schnirelmannDensity Set.univ = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `schnirelmannDensity_eq_one_iff_of_zero_mem`：schnirelmannDensity_eq_one_i
ff_of_zero_mem (hA : 0 in A) : schnirelmannDensity A = 1 ↔ A = Set.univ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma schnirelmannDensity_univ : schnirelmannDensity Set.univ = 1 :=
  (schnirelmannDensity_eq_one_iff_of_zero_mem (by simp)).2 (by simp)
/-
**schnirelmannDensity_setOfPred_even** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：schnirelmannDensity_setOfPred_even : schnirelmannDensity (Set.ofPred Even)
 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `schnirelmannDensity_eq_zero_of_one_notMem`：schnirelmannDensity_eq_zero_o
f_one_notMem (h : 1 ∉ A) : schnirelmannDensity A = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma schnirelmannDensity_setOfPred_even : schnirelmannDensity (Set.ofPred Even) = 0 :=
  schnirelmannDensity_eq_zero_of_one_notMem <| by simp

@[deprecated (since := "2026-07-09")]
alias schnirelmannDensity_setOf_even := schnirelmannDensity_setOfPred_even
/-
**schnirelmannDensity_setOfPred_prime** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：schnirelmannDensity_setOfPred_prime : schnirelmannDensity (Set.ofPred Nat.
Prime) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `schnirelmannDensity_eq_zero_of_one_notMem`：schnirelmannDensity_eq_zero_o
f_one_notMem (h : 1 ∉ A) : schnirelmannDensity A = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma schnirelmannDensity_setOfPred_prime : schnirelmannDensity (Set.ofPred Nat.Prime) = 0 :=
  schnirelmannDensity_eq_zero_of_one_notMem <| by simp [Nat.not_prime_one]

@[deprecated (since := "2026-07-09")]
alias schnirelmannDensity_setOf_prime := schnirelmannDensity_setOfPred_prime

set_option backward.isDefEq.respectTransparency false in
/--
The Schnirelmann density of the set of naturals which are `1 mod m` is `m⁻¹`, for any `m ≠ 1`.

Note that if `m = 1`, this set is empty.
-/
/-
**schnirelmannDensity_setOfPred_mod_eq_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：schnirelmannDensity_setOfPred_mod_eq_one {m : Nat} (hm : m != 1) : schnire
lmannDensity {n | n % m = 1} = (m⁻¹ : Real)
参数：hm : m != 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用引理 `schnirelmannDensity_finite`：schnirelmannDensity_finite {A : Set Nat} [De
cidablePred (· in A)] (hA : A.Finite) : schnirelmannDensity A = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.mod_zero`：∀ (a : ℕ), a % 0 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `schnirelmannDensity_le_of_le`：schnirelmannDensity_le_of_le {x : Real} (n
 : Nat) (hn : n != 0) (hx : #{a in Ioc 0 n | a in A} / n <= x) : schnirelmannDen
sity A <= x
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `div_le_div_of_nonneg_right`：div_le_div_of_nonneg_right (hab : a <= b) (h
c : 0 <= c) : a / c <= b / c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Nat.mono_cast`：mono_cast : Monotone (Nat.cast : Nat -> α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_or_lt_of_le`：eq_or_lt_of_le (h : a <= b) : a = b ∨ a < b
· 使用定理 `Nat.mod_self`：∀ (n : ℕ), n % n = 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
（共 65 条，此处仅展示前 30 条）

--- 原说明 ---
The Schnirelmann density of the set of naturals which are `1 mod m` is `m⁻¹`, fo
r any `m ≠ 1`.

Note that if `m = 1`, this set is empty.
-/
lemma schnirelmannDensity_setOfPred_mod_eq_one {m : ℕ} (hm : m ≠ 1) :
    schnirelmannDensity {n | n % m = 1} = (m⁻¹ : ℝ) := by
  rcases m.eq_zero_or_pos with rfl | hm'
  · simp only [Nat.cast_zero, inv_zero]
    refine schnirelmannDensity_finite ?_
    simp
  apply le_antisymm (schnirelmannDensity_le_of_le m hm'.ne' _) _
  · rw [← one_div, ← @Nat.cast_one ℝ]
    gcongr
    simp only [Set.mem_ofPred_eq, card_le_one_iff_subset_singleton, subset_iff,
      mem_filter, mem_Ioc, mem_singleton, and_imp]
    use 1
    intro x _ hxm h
    rcases eq_or_lt_of_le hxm with rfl | hxm'
    · simp at h
    rwa [Nat.mod_eq_of_lt hxm'] at h
  rw [le_schnirelmannDensity_iff]
  intro n hn
  simp only [Set.mem_ofPred_eq]
  have : (Icc 0 ((n - 1) / m)).image (· * m + 1) ⊆ {x ∈ Ioc 0 n | x % m = 1} := by
    simp only [subset_iff, mem_image, forall_exists_index, mem_filter, mem_Ioc, mem_Icc, and_imp]
    rintro _ y _ hy' rfl
    have hm : 2 ≤ m := hm.lt_of_le' hm'
    simp only [Nat.mul_add_mod', Nat.mod_eq_of_lt hm, add_pos_iff, or_true, and_true, true_and,
      ← Nat.le_sub_iff_add_le hn, zero_lt_one]
    exact Nat.mul_le_of_le_div _ _ _ hy'
  rw [le_div_iff₀ (Nat.cast_pos.2 hn), mul_comm, ← div_eq_mul_inv]
  apply (Nat.cast_le.2 (card_le_card this)).trans'
  rw [card_image_of_injective, Nat.card_Icc, Nat.sub_zero, div_le_iff₀ (Nat.cast_pos.2 hm'),
    ← Nat.cast_mul, Nat.cast_le, add_one_mul (α := ℕ)]
  · have := @Nat.lt_div_mul_add n.pred m hm'
    rwa [← Nat.succ_le_iff, Nat.succ_pred hn.ne'] at this
  intro a b
  simp [hm'.ne']

@[deprecated (since := "2026-07-09")]
alias schnirelmannDensity_setOf_mod_eq_one := schnirelmannDensity_setOfPred_mod_eq_one
/-
**schnirelmannDensity_setOfPred_modeq_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：schnirelmannDensity_setOfPred_modeq_one {m : Nat} : schnirelmannDensity {n
 | n ≡ 1 [MOD m]} = (m⁻¹ : Real)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `schnirelmannDensity.congr_simp`：∀ (A A_1 : Set ℕ),   A = A_1 →     ∀ {in
st : DecidablePred fun x => x ∈ A} [inst_1 : DecidablePred fun x => x ∈ A_1],   
    schnirelmannDens…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `schnirelmannDensity_univ`：schnirelmannDensity Set.univ = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `schnirelmannDensity_setOfPred_mod_eq_one`：schnirelmannDensity_setOfPred_
mod_eq_one {m : Nat} (hm : m != 1) : schnirelmannDensity {n | n % m = 1} = (m⁻¹ 
: Real)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.one_mod_eq_one`：∀ {n : ℕ}, 1 % n = 1 ↔ n ≠ 1
-/
lemma schnirelmannDensity_setOfPred_modeq_one {m : ℕ} :
    schnirelmannDensity {n | n ≡ 1 [MOD m]} = (m⁻¹ : ℝ) := by
  rcases eq_or_ne m 1 with rfl | hm
  · simp [Nat.modEq_one]
  rw [← schnirelmannDensity_setOfPred_mod_eq_one hm]
  simp [Nat.ModEq, Nat.one_mod_eq_one.mpr hm]

@[deprecated (since := "2026-07-09")]
alias schnirelmannDensity_setOf_modeq_one := schnirelmannDensity_setOfPred_modeq_one
/-
**schnirelmannDensity_setOfPred_Odd** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：schnirelmannDensity_setOfPred_Odd : schnirelmannDensity (Set.ofPred Odd) =
 2⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用引理 `Nat.odd_iff`：odd_iff : Odd n ↔ n % 2 = 1
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `schnirelmannDensity.congr_simp`：∀ (A A_1 : Set ℕ),   A = A_1 →     ∀ {in
st : DecidablePred fun x => x ∈ A} [inst_1 : DecidablePred fun x => x ∈ A_1],   
    schnirelmannDens…
· 使用引理 `schnirelmannDensity_setOfPred_mod_eq_one`：schnirelmannDensity_setOfPred_
mod_eq_one {m : Nat} (hm : m != 1) : schnirelmannDensity {n | n % m = 1} = (m⁻¹ 
: Real)
· 使用定理 `Mathlib.Meta.NormNum.isNat_eq_false`：∀ {α : Type u_1} [inst : AddMonoidW
ithOne α] [CharZero α] {a b : α} {a' b' : ℕ},   Mathlib.Meta.NormNum.IsNat a a' 
→ Mathlib.Meta.NormNum.Is…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_two`：cast_two [NatCast R] : ((2 : Nat) : R) = (2 : R)
-/
lemma schnirelmannDensity_setOfPred_Odd : schnirelmannDensity (Set.ofPred Odd) = 2⁻¹ := by
  have h : Set.ofPred Odd = {n | n % 2 = 1} := Set.ext fun _ => Nat.odd_iff
  simp only [h]
  rw [schnirelmannDensity_setOfPred_mod_eq_one (by norm_num1), Nat.cast_two]

@[deprecated (since := "2026-07-09")]
alias schnirelmannDensity_setOf_Odd := schnirelmannDensity_setOfPred_Odd

open scoped Pointwise

/-- If two sets `A` and `B` have Schnirelmann densities with sum at least 1, and both sets
contain zero, then every natural number is sum of an element of `A` and an element of `B`.
Note that we cannot omit the assumption that both sets contain zero, as shown by the
counterexample `A = B = Odd`.
-/
/-
**add_eq_univ_of_one_le_schirelmannDensity_add_schnirelmannDensity** 是 Mathlib 中
的一个定理，位于命名空间 ``。
形式化陈述：add_eq_univ_of_one_le_schirelmannDensity_add_schnirelmannDensity {A B : Se
t Nat} [DecidablePred (· in A)] [DecidablePred (· in B)] (hA : 0 in A) (hB : 0 i
n B) (h : 1 <= schnirelmannDensity A + schnirelmannDensity B) : A + B = .univ
参数：· in A；· in B；hA : 0 in A；hB : 0 in B；h : 1 <= schnirelmannDensity A + schnir
elmannDensity B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.eq_univ_iff_forall`：eq_univ_iff_forall {s : Set α} : s = univ ↔ fora
ll x, x in s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
· 使用定理 `Nat.card_Ioo`：∀ (a b : ℕ), (Finset.Ioo a b).card = b - a - 1
· 使用定理 `tsub_zero`：tsub_zero (a : α) : a - 0 = a
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Finset.card_disjSum`：card_disjSum : (s.disjSum t).card = s.card + t.card
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Int.cast_add`：∀ {R : Type u} [inst : AddGroupWithOne R] (m n : ℤ), ↑(m +
 n) = ↑m + ↑n
· 使用定理 `Rat.cast_natCast`：cast_natCast (n : Nat) : ((n : Rat) : α) = n
· 使用定理 `Rat.cast_add`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p q
 : ℚ), ↑(p + q) = ↑p + ↑q
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
（共 79 条，此处仅展示前 30 条）

--- 原说明 ---
If two sets `A` and `B` have Schnirelmann densities with sum at least 1, and bot
h sets
contain zero, then every natural number is sum of an element of `A` and an eleme
nt of `B`.
Note that we cannot omit the assumption that both sets contain zero, as shown by
 the
counterexample `A = B = Odd`.
-/
theorem add_eq_univ_of_one_le_schirelmannDensity_add_schnirelmannDensity {A B : Set ℕ}
    [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)] (hA : 0 ∈ A) (hB : 0 ∈ B)
    (h : 1 ≤ schnirelmannDensity A + schnirelmannDensity B) : A + B = .univ := by
  rw [Set.eq_univ_iff_forall]
  rintro (_ | m)
  · exact ⟨0, hA, 0, ⟨hB, rfl⟩⟩
  set n := m + 1
  by_cases hnA : n ∈ A
  · exact ⟨n, by simp [hnA], 0, ⟨hB, rfl⟩⟩
  by_cases hnB : n ∈ B
  · exact ⟨0, hA, n, ⟨hnB, by simp⟩⟩
  let f : ℕ ⊕ ℕ → ℕ
    | .inl x => x
    | .inr y => n - y
  let sA := {a ∈ Ioc 0 n | a ∈ A}
  let sB := {b ∈ Ioc 0 n | b ∈ B}
  have hc : #(image f (disjSum sA sB)) < #(disjSum sA sB) := calc
    #(image f (disjSum sA sB)) ≤ #(Ioo 0 n) := by gcongr; grind [mem_disjSum]
    _ < n := by simp [Nat.card_Ioo, n]
    _ ≤ #(disjSum sA sB) := by
      rw [card_disjSum]
      rify
      nlinarith [@schnirelmannDensity_mul_le_card_filter A _ n,
        @schnirelmannDensity_mul_le_card_filter B _ n]
  obtain ⟨a | b, ha, a | b, hb, _, hxy⟩ := exists_ne_map_eq_of_card_image_lt hc <;>
  simp only [sA, sB, inl_mem_disjSum, mem_filter, mem_Ioc, inr_mem_disjSum] at ha hb <;>
  first | grind [inr_mem_disjSum] | exact ⟨a, by simp [*], b, by simp [*], by grind⟩
