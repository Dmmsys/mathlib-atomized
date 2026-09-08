/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Combinatorics.Enumerative.Partition.GenFun
public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors

/-!
# Glaisher's theorem

This file proves Glaisher's theorem: the number of partitions of an integer $n$ into parts not
divisible by $d$ is equal to the number of partitions in which no part is repeated $d$ or more
times.

## Main declarations
* `Nat.Partition.card_restricted_eq_card_countRestricted`: Glaisher's theorem.
* `Nat.Partition.card_odds_eq_card_distincts`: Euler's partition theorem, a special case
  of Glaisher's theorem when `m = 2`. This is also Theorem 45 from the
  [100 Theorems List](https://www.cs.ru.nl/~freek/100/).

## Proof outline

The proof is based on the generating functions for `restricted` and `countRestricted` partitions,
which turn out to be equal:

$$\prod_{i=1,i\nmid m}^\infty\frac{1}{1-X^i}=\prod_{i=0}^\infty (1+X^{i+1}+\cdots+X^{(m-1)(i+1)})$$

## References
https://en.wikipedia.org/wiki/Glaisher%27s_theorem
-/

public section

variable (R) [TopologicalSpace R] [T2Space R]

namespace Nat.Partition
open PowerSeries PowerSeries.WithPiTopology Finset

section Semiring
variable [CommSemiring R]

/-- The generating function of `Nat.Partition.restricted n p` is
$$
\prod_{i \in p} \sum_{j = 0}^{\infty} X^{ij}
$$ -/
/-
**Nat.Partition.hasProd_powerSeriesMk_card_restricted** 是 Mathlib 中的一个定理，位于命名空间 
`Nat.Partition`。
形式化陈述：hasProd_powerSeriesMk_card_restricted [IsTopologicalSemiring R] (p : Nat -
> Prop) [DecidablePred p] : HasProd (fun i => if p (i + 1) then ∑' j : Nat, X ^ 
((i + 1) * j) else 1) (PowerSeries.mk fun n => (#(restricted n p) : R))
参数：p : Nat -> Prop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `tsum_eq_zero_add'`：∀ {M : Type u_1} [inst : AddCommMonoid M] [inst_1 : T
opologicalSpace M] [T2Space M] [ContinuousAdd M] {f : ℕ → M},   (Summable fun n 
=> f (n…
· 使用定理 `PowerSeries.WithPiTopology.instT2Space`：instT2Space [T2Space R] : T2Spac
e (PowerSeries R)
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `PowerSeries.WithPiTopology.instIsTopologicalSemiring`：instIsTopologicalS
emiring [Semiring R] [IsTopologicalSemiring R] : IsTopologicalSemiring (PowerSer
ies R)
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `Summable.mul_right`：Summable.mul_right (a) (hf : Summable f L) : Summabl
e (fun i => f i * a) L
· 使用定理 `PowerSeries.WithPiTopology.summable_pow_of_constantCoeff_eq_zero`：summab
le_pow_of_constantCoeff_eq_zero {f : PowerSeries R} (h : f.constantCoeff = 0) : 
Summable (f ^ ·)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `PowerSeries.constantCoeff_X`：constantCoeff_X : constantCoeff (R
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
（共 43 条，此处仅展示前 30 条）

--- 原说明 ---
The generating function of `Nat.Partition.restricted n p` is
$$
\prod_{i \in p} \sum_{j = 0}^{\infty} X^{ij}
$$
-/
theorem hasProd_powerSeriesMk_card_restricted [IsTopologicalSemiring R]
    (p : ℕ → Prop) [DecidablePred p] :
    HasProd (fun i ↦ if p (i + 1) then ∑' j : ℕ, X ^ ((i + 1) * j) else 1)
    (PowerSeries.mk fun n ↦ (#(restricted n p) : R)) := by
  convert! hasProd_genFun (fun i c ↦ if p i then (1 : R) else 0) using 1
  · ext1 i
    split_ifs
    · rw [tsum_eq_zero_add' ?_]
      · simp
      simp_rw [pow_mul, pow_add]
      apply Summable.mul_right
      exact summable_pow_of_constantCoeff_eq_zero (by simp)
    · simp
  · simp_rw [genFun, restricted, card_filter, Finsupp.prod, prod_boole]
    simp
/-
**Nat.Partition.multipliable_powerSeriesMk_card_restricted** 是 Mathlib 中的一个定理，位于
命名空间 `Nat.Partition`。
形式化陈述：multipliable_powerSeriesMk_card_restricted [IsTopologicalSemiring R] (p : 
Nat -> Prop) [DecidablePred p] : Multipliable (fun i => if p (i + 1) then ∑' j :
 Nat, (X ^ ((i + 1) * j) : R⟦X⟧) else 1)
参数：p : Nat -> Prop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.multipliable`：HasProd.multipliable (h : HasProd f a L) : Multipl
iable f L
· 使用定理 `Nat.Partition.hasProd_powerSeriesMk_card_restricted`：hasProd_powerSeries
Mk_card_restricted [IsTopologicalSemiring R] (p : Nat -> Prop) [DecidablePred p]
 : HasProd (fun i => if p (i + 1) then ∑'…
-/
theorem multipliable_powerSeriesMk_card_restricted [IsTopologicalSemiring R]
    (p : ℕ → Prop) [DecidablePred p] :
    Multipliable (fun i ↦ if p (i + 1) then ∑' j : ℕ, (X ^ ((i + 1) * j) : R⟦X⟧) else 1) :=
  (hasProd_powerSeriesMk_card_restricted R p).multipliable
/-
**Nat.Partition.powerSeriesMk_card_restricted_eq_tprod** 是 Mathlib 中的一个定理，位于命名空间
 `Nat.Partition`。
形式化陈述：powerSeriesMk_card_restricted_eq_tprod [IsTopologicalSemiring R] (p : Nat 
-> Prop) [DecidablePred p] : PowerSeries.mk (fun n => (#(restricted n p) : R)) =
 ∏' i, if p (i + 1) then ∑' j : Nat, X ^ ((i + 1) * j) else 1
参数：p : Nat -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasProd.tprod_eq`：HasProd.tprod_eq (ha : HasProd f a L) : ∏'[L] b, f b =
 a
· 使用定理 `PowerSeries.WithPiTopology.instT2Space`：instT2Space [T2Space R] : T2Spac
e (PowerSeries R)
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `Nat.Partition.hasProd_powerSeriesMk_card_restricted`：hasProd_powerSeries
Mk_card_restricted [IsTopologicalSemiring R] (p : Nat -> Prop) [DecidablePred p]
 : HasProd (fun i => if p (i + 1) then ∑'…
-/
theorem powerSeriesMk_card_restricted_eq_tprod [IsTopologicalSemiring R]
    (p : ℕ → Prop) [DecidablePred p] :
    PowerSeries.mk (fun n ↦ (#(restricted n p) : R)) =
    ∏' i, if p (i + 1) then ∑' j : ℕ, X ^ ((i + 1) * j) else 1 :=
  (hasProd_powerSeriesMk_card_restricted R p).tprod_eq.symm

/-- The generating function of `Nat.Partition.countRestricted n m` is
$$
\prod_{i = 1}^{\infty} \sum_{j = 0}^{m - 1} X^{ij}
$$ -/
/-
**Nat.Partition.hasProd_powerSeriesMk_card_countRestricted** 是 Mathlib 中的一个定理，位于
命名空间 `Nat.Partition`。
形式化陈述：hasProd_powerSeriesMk_card_countRestricted {m : Nat} (hm : 0 < m) : HasPro
d (fun i => ∑ j in range m, X ^ ((i + 1) * j)) (PowerSeries.mk fun n => (#(count
Restricted n m) : R))
参数：hm : 0 < m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Subsingleton.eq_one`：Subsingleton.eq_one [One α] [Subsingleton α] (a : α
) : a = 1
· 使用定理 `PowerSeries.instSubsingleton`：∀ {R : Type u_1} [Semiring R] [Subsingleto
n R], Subsingleton (PowerSeries R)
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_range_eq_add_Ico`：∀ {M : Type u_3} [inst : AddCommMonoid M] (
f : ℕ → M) {n : ℕ},   0 < n → ∑ x ∈ Finset.range n, f x = f 0 + ∑ x ∈ Finset.Ico
 1 n, f x
· 使用定理 `Finset.sum_Ico_eq_sum_range`：∀ {M : Type u_3} [inst : AddCommMonoid M] (
f : ℕ → M) (m n : ℕ),   ∑ k ∈ Finset.Ico m n, f k = ∑ k ∈ Finset.range (n - m), 
f (m + k)
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `tsum_eq_sum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [i
nst_1 : TopologicalSpace α] {f : β → α}   {L : SummationFilter β} [L.LeAtTop] {s
 …
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用引理 `smul_eq_zero_of_left`：smul_eq_zero_of_left (h : a = 0) (b : A) : a • b =
 0
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `Finset.card_filter`：card_filter (p) [DecidablePred p] (s : Finset ι) : #
{i in s | p i} = ∑ i in s, ite (p i) 1 0
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用引理 `Finset.prod_boole`：prod_boole : ∏ i in s, (ite (p i) 1 0 : M₀) = ite (fo
rall i in s, p i) 1 0
· 使用定理 `Finset.sum_boole`：∀ {ι : Type u_1} {R : Type u_4} [inst : AddCommMonoidW
ithOne R] (p : ι → Prop) [inst_1 : DecidablePred p]   (s : Finset ι), (∑ x ∈ s, 
if p x…
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
The generating function of `Nat.Partition.countRestricted n m` is
$$
\prod_{i = 1}^{\infty} \sum_{j = 0}^{m - 1} X^{ij}
$$
-/
theorem hasProd_powerSeriesMk_card_countRestricted {m : ℕ} (hm : 0 < m) :
    HasProd (fun i ↦ ∑ j ∈ range m, X ^ ((i + 1) * j))
    (PowerSeries.mk fun n ↦ (#(countRestricted n m) : R)) := by
  nontriviality R using Subsingleton.eq_one (α := R⟦X⟧)
  convert! hasProd_genFun (fun i c ↦ if c < m then (1 : R) else 0) using 1
  · ext1 i
    rw [sum_range_eq_add_Ico _ hm, sum_Ico_eq_sum_range]
    congrm $(by simp) + ?_
    trans ∑ k ∈ range (m - 1), (if k + 1 < m then (1 : R) else 0) • X ^ ((i + 1) * (k + 1))
    · refine sum_congr rfl fun b hn ↦ ?_
      rw [add_comm 1 b]
      have : b + 1 < m := by grind
      simp [this]
    · exact (tsum_eq_sum (fun b hb ↦ smul_eq_zero_of_left (by simpa using hb) _)).symm
  · simp_rw [genFun, countRestricted, card_filter, Finsupp.prod, prod_boole]
    simp
/-
**Nat.Partition.multipliable_powerSeriesMk_card_countRestricted** 是 Mathlib 中的一个
定理，位于命名空间 `Nat.Partition`。
形式化陈述：multipliable_powerSeriesMk_card_countRestricted (m : Nat) : Multipliable f
un i => ∑ j in range m, (X ^ ((i + 1) * j) : R⟦X⟧)
参数：m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用引理 `multipliable_of_exists_eq_zero`：multipliable_of_exists_eq_zero (hf : exi
sts b, f b = 0) [L.LeAtTop] : Multipliable f L
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasProd.multipliable`：HasProd.multipliable (h : HasProd f a L) : Multipl
iable f L
· 使用定理 `Nat.Partition.hasProd_powerSeriesMk_card_countRestricted`：hasProd_powerS
eriesMk_card_countRestricted {m : Nat} (hm : 0 < m) : HasProd (fun i => ∑ j in r
ange m, X ^ ((i + 1) * j)) (PowerSeries.mk fun…
-/
theorem multipliable_powerSeriesMk_card_countRestricted (m : ℕ) :
    Multipliable fun i ↦ ∑ j ∈ range m, (X ^ ((i + 1) * j) : R⟦X⟧) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simpa using multipliable_of_exists_eq_zero ⟨0, rfl⟩
  · exact (hasProd_powerSeriesMk_card_countRestricted R hm).multipliable
/-
**Nat.Partition.powerSeriesMk_card_countRestricted_eq_tprod** 是 Mathlib 中的一个定理，位
于命名空间 `Nat.Partition`。
形式化陈述：powerSeriesMk_card_countRestricted_eq_tprod {m : Nat} (hm : 0 < m) : Power
Series.mk (fun n => (#(countRestricted n m) : R)) = ∏' i, ∑ j in range m, X ^ ((
i + 1) * j)
参数：hm : 0 < m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasProd.tprod_eq`：HasProd.tprod_eq (ha : HasProd f a L) : ∏'[L] b, f b =
 a
· 使用定理 `PowerSeries.WithPiTopology.instT2Space`：instT2Space [T2Space R] : T2Spac
e (PowerSeries R)
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `Nat.Partition.hasProd_powerSeriesMk_card_countRestricted`：hasProd_powerS
eriesMk_card_countRestricted {m : Nat} (hm : 0 < m) : HasProd (fun i => ∑ j in r
ange m, X ^ ((i + 1) * j)) (PowerSeries.mk fun…
-/
theorem powerSeriesMk_card_countRestricted_eq_tprod {m : ℕ} (hm : 0 < m) :
    PowerSeries.mk (fun n ↦ (#(countRestricted n m) : R)) =
    ∏' i, ∑ j ∈ range m, X ^ ((i + 1) * j) :=
  (hasProd_powerSeriesMk_card_countRestricted R hm).tprod_eq.symm

end Semiring

section Ring
variable [CommRing R] [NoZeroDivisors R]

/-
**Nat.Partition.aux_mul_one_sub_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Partition`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem aux_mul_one_sub_X_pow [IsTopologicalRing R] {m : ℕ} (hm : 0 < m) :
    (∏' i, if ¬m ∣ i + 1 then ∑' j, (X : R⟦X⟧) ^ ((i + 1) * j) else 1) * ∏' i, (1 - X ^ (i + 1)) =
    ∏' i, (1 - X ^ ((i + 1) * m)) := by
  nontriviality R
  rw [← (multipliable_powerSeriesMk_card_restricted R (¬ m ∣ ·)).tprod_mul
    (multipliable_one_sub_X_pow _)]
  simp_rw [ite_not, ite_mul, pow_mul]
  conv in fun b ↦ _ =>
    ext b
    rw [tsum_pow_mul_one_sub_of_constantCoeff_eq_zero (by simp)]
  refine tprod_eq_tprod_of_ne_one_bij (fun i ↦ (i.val + 1) * m - 1) ?_ ?_ ?_
  · intro a b h
    rw [tsub_left_inj (by nlinarith) (by nlinarith), mul_left_inj' (hm.ne.symm), add_left_inj] at h
    exact SetCoe.ext h
  · suffices ∀ (i : ℕ), m ∣ i + 1 → ∃ j ≠ 0, j * m - 1 = i by simpa
    intro i hi
    obtain ⟨j, hj⟩ := dvd_def.mp hi
    refine ⟨j, by grind, Nat.sub_eq_of_eq_add ?_⟩
    rw [hj, mul_comm m j]
  · intro i
    have : (i + 1) * m - 1 + 1 = (i + 1) * m := by grind
    simp [this, pow_mul]

omit [TopologicalSpace R] in
/-
**Nat.Partition.powerSeriesMk_card_restricted_eq_powerSeriesMk_card_countRestric
ted** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Partition`。
形式化陈述：powerSeriesMk_card_restricted_eq_powerSeriesMk_card_countRestricted {m : N
at} (hm : 0 < m) : (PowerSeries.mk fun n => (#(restricted n (¬ m ∣ ·)) : R)) = P
owerSeries.mk fun n => (#(countRestricted n m) : R)
参数：hm : 0 < m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `PowerSeries.instSubsingleton`：∀ {R : Type u_1} [Semiring R] [Subsingleto
n R], Subsingleton (PowerSeries R)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.Partition.powerSeriesMk_card_restricted_eq_tprod`：powerSeriesMk_card
_restricted_eq_tprod [IsTopologicalSemiring R] (p : Nat -> Prop) [DecidablePred 
p] : PowerSeries.mk (fun n => (#(restricte…
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `instT3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T0Space X] [R
egularSpace X], T3Space X
· 使用定理 `T1Space.t0Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T1Space X
], T0Space X
· 使用定理 `instT1SpaceOfDiscreteTopology`：∀ {X : Type u_1} [inst : TopologicalSpace
 X] [DiscreteTopology X], T1Space X
· 使用定理 `IsTopologicalAddGroup.regularSpace`：∀ (G : Type w) [inst : TopologicalSp
ace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], RegularSpace G
· 使用定理 `IsSemitopologicalRing.toIsTopologicalAddGroup`：∀ {R : Type u_1} [inst : 
NonUnitalNonAssocRing R] [inst_1 : TopologicalSpace R] [IsSemitopologicalRing R]
,   IsTopologicalAddGroup R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `DiscreteTopology.topologicalRing`：∀ {R : Type u_1} [inst : TopologicalSp
ace R] [inst_1 : NonUnitalNonAssocRing R] [DiscreteTopology R],   IsTopologicalR
ing R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `Nat.Partition.powerSeriesMk_card_countRestricted_eq_tprod`：powerSeriesMk
_card_countRestricted_eq_tprod {m : Nat} (hm : 0 < m) : PowerSeries.mk (fun n =>
 (#(countRestricted n m) : R)) = ∏' i, ∑ j in r…
· 使用定理 `mul_right_cancel₀`：mul_right_cancel₀ (hb : b != 0) (h : a * b = c * b) :
 a = c
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `NoZeroDivisors.to_isCancelMulZero`：∀ (R : Type u_3) [inst : NonUnitalNon
AssocRing R] [NoZeroDivisors R], IsCancelMulZero R
· 使用定理 `PowerSeries.instNoZeroDivisors`：∀ {R : Type u_1} [inst : Semiring R] [No
ZeroDivisors R], NoZeroDivisors (PowerSeries R)
· 使用定理 `PowerSeries.WithPiTopology.tprod_one_sub_X_pow_ne_zero`：tprod_one_sub_X_
pow_ne_zero [T2Space R] [Nontrivial R] : ∏' i, (1 - X ^ (i + 1)) != (0 : R⟦X⟧)
· 使用定理 `_private.Mathlib.Combinatorics.Enumerative.Partition.Glaisher.0.Nat.Part
ition.aux_mul_one_sub_X_pow`：∀ (R : Type u_1) [inst : TopologicalSpace R] [T2Spa
ce R] [inst_2 : CommRing R] [NoZeroDivisors R] [IsTopologicalRing R]   {m : ℕ}, 
  0 < m →…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multipliable.tprod_mul`：∀ {α : Type u_1} {β : Type u_2} [inst : CommMono
id α] [inst_1 : TopologicalSpace α] {f g : β → α}   {L : SummationFilter β} [T2S
pace α] [Con…
· 使用定理 `PowerSeries.WithPiTopology.instT2Space`：instT2Space [T2Space R] : T2Spac
e (PowerSeries R)
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `PowerSeries.WithPiTopology.instIsTopologicalSemiring`：instIsTopologicalS
emiring [Semiring R] [IsTopologicalSemiring R] : IsTopologicalSemiring (PowerSer
ies R)
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `Nat.Partition.multipliable_powerSeriesMk_card_countRestricted`：multiplia
ble_powerSeriesMk_card_countRestricted (m : Nat) : Multipliable fun i => ∑ j in 
range m, (X ^ ((i + 1) * j) : R⟦X⟧)
· 使用定理 `PowerSeries.WithPiTopology.multipliable_one_sub_X_pow`：multipliable_one_
sub_X_pow : Multipliable fun n => (1 : R⟦X⟧) - X ^ (n + 1)
（共 38 条，此处仅展示前 30 条）
-/
theorem powerSeriesMk_card_restricted_eq_powerSeriesMk_card_countRestricted {m : ℕ} (hm : 0 < m) :
    (PowerSeries.mk fun n ↦ (#(restricted n (¬ m ∣ ·)) : R)) =
    PowerSeries.mk fun n ↦ (#(countRestricted n m) : R) := by
  nontriviality R
  let _ : TopologicalSpace R := ⊥
  have _ : DiscreteTopology R := ⟨rfl⟩
  rw [powerSeriesMk_card_restricted_eq_tprod R (¬ m ∣ ·)]
  rw [powerSeriesMk_card_countRestricted_eq_tprod R hm]
  apply mul_right_cancel₀ (tprod_one_sub_X_pow_ne_zero R)
  rw [aux_mul_one_sub_X_pow R hm]
  rw [← (multipliable_powerSeriesMk_card_countRestricted R m).tprod_mul
    (multipliable_one_sub_X_pow _)]
  exact tprod_congr (fun i ↦ by simp_rw [pow_mul, geom_sum_mul_neg])

end Ring

/-
**Nat.Partition.card_restricted_eq_card_countRestricted** 是 Mathlib 中的一个定理，位于命名空
间 `Nat.Partition`。
形式化陈述：card_restricted_eq_card_countRestricted (n : Nat) {m : Nat} (hm : 0 < m) :
 #(restricted n (¬ m ∣ ·)) = #(countRestricted n m)
参数：n : Nat；hm : 0 < m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.coeff_mk`：coeff_mk (n : Nat) (f : Nat -> R) : coeff n (mk f)
 = f n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `PowerSeries.ext_iff`：∀ {R : Type u_1} [inst : Semiring R] {φ ψ : PowerSe
ries R},   φ = ψ ↔ ∀ (n : ℕ), (PowerSeries.coeff n) φ = (PowerSeries.coeff n) ψ
· 使用定理 `Nat.Partition.powerSeriesMk_card_restricted_eq_powerSeriesMk_card_countR
estricted`：powerSeriesMk_card_restricted_eq_powerSeriesMk_card_countRestricted {
m : Nat} (hm : 0 < m) : (PowerSeries.mk fun n => (#(restricted n (¬ m ∣…
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
-/
theorem card_restricted_eq_card_countRestricted (n : ℕ) {m : ℕ} (hm : 0 < m) :
    #(restricted n (¬ m ∣ ·)) = #(countRestricted n m) := by
  simpa using PowerSeries.ext_iff.mp
    (powerSeriesMk_card_restricted_eq_powerSeriesMk_card_countRestricted ℤ hm) n
/-
**Nat.Partition.card_odds_eq_card_distincts** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Parti
tion`。
形式化陈述：card_odds_eq_card_distincts (n : Nat) : #(odds n) = #(distincts n)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.Partition.restricted.congr_simp`：∀ (n : ℕ) (p p_1 : ℕ → Prop),   p =
 p_1 →     ∀ {inst : DecidablePred p} [inst_1 : DecidablePred p_1],       Nat.Pa
rtition.restricted n p = …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.Partition.card_restricted_eq_card_countRestricted`：card_restricted_e
q_card_countRestricted (n : Nat) {m : Nat} (hm : 0 < m) : #(restricted n (¬ m ∣ 
·)) = #(countRestricted n m)
· 使用定理 `Mathlib.Meta.NormNum.isNat_lt_true`：∀ {α : Type u_1} [inst : Semiring α]
 [inst_1 : PartialOrder α] [IsOrderedRing α] [CharZero α] {a b : α} {a' b' : ℕ},
   Mathlib.Meta.NormNum.…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
-/
theorem card_odds_eq_card_distincts (n : ℕ) : #(odds n) = #(distincts n) := by
  simp_rw [← countRestricted_two, odds, even_iff_two_dvd]
  exact card_restricted_eq_card_countRestricted n (by norm_num)

end Nat.Partition

