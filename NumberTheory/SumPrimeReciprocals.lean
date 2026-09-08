/-
Copyright (c) 2023 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Order.Group.Indicator
public import Mathlib.Analysis.PSeries
public import Mathlib.NumberTheory.SmoothNumbers

/-!
# The sum of the reciprocals of the primes diverges

We show that the sum of `1/p`, where `p` runs through the prime numbers, diverges.
We follow the elementary proof by Erdős that is reproduced in "Proofs from THE BOOK".
There are two versions of the main result: `not_summable_one_div_on_primes`, which
expresses the sum as a sub-sum of the harmonic series, and `Nat.Primes.not_summable_one_div`,
which writes it as a sum over `Nat.Primes`. We also show that the sum of `p^r` for `r : ℝ`
converges if and only if `r < -1`; see `Nat.Primes.summable_rpow`.

## References

See the sixth proof for the infinity of primes in Chapter 1 of [aigner1999proofs].
The proof is due to Erdős.
-/

public section

open Set Nat
open scoped Topology

section PrimeSums

variable {M : Type*} [CommMonoid M] [TopologicalSpace M] (f : ℕ → M)

omit [TopologicalSpace M] in
@[to_additive]
/-
**ite_prime_eq_mulIndicator** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma ite_prime_eq_mulIndicator :
    (fun n : ℕ ↦ if n.Prime then f n else 1) = {n | n.Prime}.mulIndicator f := by
  ext; simp [Set.mulIndicator_apply]

/-- Reindex a product over `Nat.Primes` as a product over `ℕ`, extending `f` by `1`. -/
@[to_additive /-- Reindex a sum over `Nat.Primes` as a sum over `ℕ`, extending `f` by `0`. -/]
/-
**Nat.Primes.tprod_eq_tprod_ite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nat.Primes.tprod_eq_tprod_ite : ∏' p : Primes, f p = ∏' n : Nat, if n.Prim
e then f n else 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.NumberTheory.SumPrimeReciprocals.0.ite_prime_eq_mulIndi
cator`：∀ {M : Type u_1} [inst : CommMonoid M] (f : ℕ → M),   (fun n => if Nat.Pr
ime n then f n else 1) = {n | Nat.Prime n}.mulIndicator f
· 使用定理 `tprod_subtype`：tprod_subtype (s : Set β) (f : β -> α) : ∏' x : s, f x = 
∏' x, s.mulIndicator f x

--- 原说明 ---
Reindex a product over `Nat.Primes` as a product over `ℕ`, extending `f` by `1`.
-/
theorem Nat.Primes.tprod_eq_tprod_ite :
    ∏' p : Primes, f p = ∏' n : ℕ, if n.Prime then f n else 1 := by
  rw [ite_prime_eq_mulIndicator]; exact tprod_subtype {n | n.Prime} f

/-- `Multipliable` over `Nat.Primes` iff over `ℕ` extending `f` by `1`. -/
@[to_additive /-- `Summable` over `Nat.Primes` iff over `ℕ` extending `f` by `0`. -/]
/-
**Nat.Primes.multipliable_iff_multipliable_ite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nat.Primes.multipliable_iff_multipliable_ite : Multipliable (fun p : Prime
s => f p) ↔ Multipliable fun n : Nat => if n.Prime then f n else 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.NumberTheory.SumPrimeReciprocals.0.ite_prime_eq_mulIndi
cator`：∀ {M : Type u_1} [inst : CommMonoid M] (f : ℕ → M),   (fun n => if Nat.Pr
ime n then f n else 1) = {n | Nat.Prime n}.mulIndicator f
· 使用定理 `multipliable_subtype_iff_mulIndicator`：multipliable_subtype_iff_mulIndic
ator {s : Set β} : Multipliable (f ∘ (↑) : s -> α) ↔ Multipliable (s.mulIndicato
r f)

--- 原说明 ---
`Multipliable` over `Nat.Primes` iff over `ℕ` extending `f` by `1`.
-/
theorem Nat.Primes.multipliable_iff_multipliable_ite :
    Multipliable (fun p : Primes ↦ f p) ↔ Multipliable fun n : ℕ ↦ if n.Prime then f n else 1 := by
  rw [ite_prime_eq_mulIndicator]; exact multipliable_subtype_iff_mulIndicator

/-- `HasProd` over `Nat.Primes` iff over `ℕ` extending `f` by `1`. -/
@[to_additive /-- `HasSum` over `Nat.Primes` iff over `ℕ` extending `f` by `0`. -/]
/-
**Nat.Primes.hasProd_iff_hasProd_ite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nat.Primes.hasProd_iff_hasProd_ite {a : M} : HasProd (fun p : Primes => f 
p) a ↔ HasProd (fun n : Nat => if n.Prime then f n else 1) a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.NumberTheory.SumPrimeReciprocals.0.ite_prime_eq_mulIndi
cator`：∀ {M : Type u_1} [inst : CommMonoid M] (f : ℕ → M),   (fun n => if Nat.Pr
ime n then f n else 1) = {n | Nat.Prime n}.mulIndicator f
· 使用定理 `hasProd_subtype_iff_mulIndicator`：hasProd_subtype_iff_mulIndicator {s : 
Set β} : HasProd (f ∘ (↑) : s -> α) a ↔ HasProd (s.mulIndicator f) a

--- 原说明 ---
`HasProd` over `Nat.Primes` iff over `ℕ` extending `f` by `1`.
-/
theorem Nat.Primes.hasProd_iff_hasProd_ite {a : M} :
    HasProd (fun p : Primes ↦ f p) a ↔ HasProd (fun n : ℕ ↦ if n.Prime then f n else 1) a := by
  rw [ite_prime_eq_mulIndicator]; exact hasProd_subtype_iff_mulIndicator

end PrimeSums

/-- The cardinality of the set of `k`-rough numbers `≤ N` is bounded by `N` times the sum
of `1/p` over the primes `k ≤ p ≤ N`. -/
-- This needs `Mathlib/Analysis/RCLike/Basic.lean`, so we put it here
-- instead of in `Mathlib/NumberTheory/SmoothNumbers.lean`.
/-
**Nat.roughNumbersUpTo_card_le'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Nat.roughNumbersUpTo_card_le' (N k : Nat) : (roughNumbersUpTo N k).card <=
 N * (N.succ.primesBelow \ k.primesBelow).sum (fun p => (1 : Real) / p)
参数：N k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `mul_one_div`：mul_one_div (x y : G) : x * (1 / y) = x / y
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `Nat.roughNumbersUpTo_card_le`：roughNumbersUpTo_card_le (N k : Nat) : #(r
oughNumbersUpTo N k) <= ((N + 1).primesBelow \ k.primesBelow).sum (fun p => N / 
p)
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `Nat.cast_div_le`：cast_div_le {m n : Nat} : ((m / n : Nat) : α) <= m / n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Nat.cast_sum`：cast_sum [AddCommMonoidWithOne R] (s : Finset ι) (f : ι ->
 Nat) : ↑(∑ x in s, f x : Nat) = ∑ x in s, (f x : R)
-/
lemma Nat.roughNumbersUpTo_card_le' (N k : ℕ) :
    (roughNumbersUpTo N k).card ≤
      N * (N.succ.primesBelow \ k.primesBelow).sum (fun p ↦ (1 : ℝ) / p) := by
  simp_rw [Finset.mul_sum, mul_one_div]
  exact (Nat.cast_le.mpr <| roughNumbersUpTo_card_le N k).trans <|
    cast_sum (R := ℝ) .. ▸ Finset.sum_le_sum fun n _ ↦ cast_div_le

/-- The sum over primes `k ≤ p ≤ 4^(π(k-1)+1)` over `1/p` (as a real number) is at least `1/2`. -/
/-
**one_half_le_sum_primes_ge_one_div** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：one_half_le_sum_primes_ge_one_div (k : Nat) : 1 / 2 <= ∑ p in (4 ^ (k.prim
esBelow.card + 1)).succ.primesBelow \ k.primesBelow, (1 / p : Real)
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `Nat.smoothNumbersUpTo_card_add_roughNumbersUpTo_card`：smoothNumbersUpTo_
card_add_roughNumbersUpTo_card (N k : Nat) : #(smoothNumbersUpTo N k) + #(roughN
umbersUpTo N k) = N
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.add_le_add_right`：∀ {n m : ℕ}, n ≤ m → ∀ (k : ℕ), n + k ≤ m + k
· 使用引理 `Nat.smoothNumbersUpTo_card_le`：smoothNumbersUpTo_card_le (N k : Nat) : #
(smoothNumbersUpTo N k) <= 2 ^ #k.primesBelow * N.sqrt
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `Nat.roughNumbersUpTo_card_le'`：Nat.roughNumbersUpTo_card_le' (N k : Nat)
 : (roughNumbersUpTo N k).card <= N * (N.succ.primesBelow \ k.primesBelow).sum (
fun p => (1 : Real)…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `mul_le_mul_iff_right₀`：mul_le_mul_iff_right₀ [PosMulMono α] [PosMulRefle
ctLE α] (a0 : 0 < a) : a * b <= a * c ↔ b <= c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
（共 98 条，此处仅展示前 30 条）

--- 原说明 ---
The sum over primes `k ≤ p ≤ 4^(π(k-1)+1)` over `1/p` (as a real number) is at l
east `1/2`.
-/
lemma one_half_le_sum_primes_ge_one_div (k : ℕ) :
    1 / 2 ≤ ∑ p ∈ (4 ^ (k.primesBelow.card + 1)).succ.primesBelow \ k.primesBelow,
      (1 / p : ℝ) := by
  set m : ℕ := 2 ^ k.primesBelow.card
  set N₀ : ℕ := 2 * m ^ 2 with hN₀
  let S : ℝ := ((2 * N₀).succ.primesBelow \ k.primesBelow).sum (fun p ↦ (1 / p : ℝ))
  suffices 1 / 2 ≤ S by
    convert! this using 5
    rw [show 4 = 2 ^ 2 by simp, pow_right_comm]
    ring
  suffices 2 * N₀ ≤ m * (2 * N₀).sqrt + 2 * N₀ * S by
    rwa [hN₀, ← mul_assoc, ← pow_two 2, ← mul_pow, sqrt_eq', ← sub_le_iff_le_add',
      cast_mul, cast_mul, cast_pow, cast_two,
      show (2 * (2 * m ^ 2) - m * (2 * m) : ℝ) = 2 * (2 * m ^ 2) * (1 / 2) by ring,
      mul_le_mul_iff_right₀ <| by positivity] at this
  calc (2 * N₀ : ℝ)
    _ = ((2 * N₀).smoothNumbersUpTo k).card + ((2 * N₀).roughNumbersUpTo k).card := by
        exact_mod_cast ((2 * N₀).smoothNumbersUpTo_card_add_roughNumbersUpTo_card k).symm
    _ ≤ m * (2 * N₀).sqrt + ((2 * N₀).roughNumbersUpTo k).card := by
        exact_mod_cast Nat.add_le_add_right ((2 * N₀).smoothNumbersUpTo_card_le k) _
    _ ≤ m * (2 * N₀).sqrt + 2 * N₀ * S := by grw [roughNumbersUpTo_card_le']; norm_cast

/-- The sum over the reciprocals of the primes diverges. -/
/-
**not_summable_one_div_on_primes** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_summable_one_div_on_primes : ¬ Summable (indicator {p | p.Prime} (fun 
n : Nat => (1 : Real) / n))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Summable.nat_tsum_vanishing`：∀ {G : Type u_2} [inst : AddCommGroup G] [i
nst_1 : TopologicalSpace G] [IsTopologicalAddGroup G] {f : ℕ → G},   Summable f 
→ ∀ ⦃e : Set G⦄, …
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Iio_mem_nhds`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Linea
rOrder α] [ClosedIciTopology α] {a b : α},   b < a → Set.Iio a ∈ nhds b
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `one_half_pos`：one_half_pos : (0 : α) < 1 / 2
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.indicator_indicator`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 (s t : Set α) (f : α → M),   s.indicator (t.indicator f) = (s ∩ t).indicator f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Summable.indicator`：∀ {α : Type u_1} {β : Type u_2} [inst : UniformSpace
 α] [inst_1 : AddCommGroup α] [IsUniformAddGroup α] {f : β → α}   [CompleteSpace
 α], Sum…
· 使用定理 `instIsUniformAddGroupReal`：IsUniformAddGroup ℝ
· 使用定理 `LT.lt.false`：∀ {α : Type u_2} [inst : Preorder α] {a : α}, a < a → False
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用引理 `one_half_le_sum_primes_ge_one_div`：one_half_le_sum_primes_ge_one_div (k 
: Nat) : 1 / 2 <= ∑ p in (4 ^ (k.primesBelow.card + 1)).succ.primesBelow \ k.pri
mesBelow, (1 / p : Real…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_sdiff`：mem_sdiff : a in s \ t ↔ a in s ∧ a ∉ t
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
（共 51 条，此处仅展示前 30 条）

--- 原说明 ---
The sum over the reciprocals of the primes diverges.
-/
theorem not_summable_one_div_on_primes :
    ¬ Summable (indicator {p | p.Prime} (fun n : ℕ ↦ (1 : ℝ) / n)) := by
  intro h
  obtain ⟨k, hk⟩ := h.nat_tsum_vanishing (Iio_mem_nhds one_half_pos : Iio (1 / 2 : ℝ) ∈ 𝓝 0)
  specialize hk ({p | Nat.Prime p} ∩ {p | k ≤ p}) inter_subset_right
  rw [tsum_subtype, indicator_indicator, inter_eq_left.mpr fun n hn ↦ hn.1, mem_Iio] at hk
  have h' : Summable (indicator ({p | Nat.Prime p} ∩ {p | k ≤ p}) fun n ↦ (1 : ℝ) / n) := by
    convert! h.indicator {n : ℕ | k ≤ n} using 1
    simp only [indicator_indicator, inter_comm]
  refine ((one_half_le_sum_primes_ge_one_div k).trans_lt <| LE.le.trans_lt ?_ hk).false
  convert!
    Summable.sum_le_tsum (primesBelow ((4 ^ (k.primesBelow.card + 1)).succ) \ primesBelow k)
      (fun n _ ↦ indicator_nonneg (fun p _ ↦ by positivity) _) h' using
    2 with p hp
  obtain ⟨hp₁, hp₂⟩ := mem_ofPred_eq ▸ Finset.mem_sdiff.mp hp
  have hpp := prime_of_mem_primesBelow hp₁
  refine (indicator_of_mem ?_ fun n : ℕ ↦ (1 / n : ℝ)).symm
  exact ⟨hpp, by simpa [primesBelow, hpp] using hp₂⟩

set_option backward.isDefEq.respectTransparency false in
/-- The sum over the reciprocals of the primes diverges. -/
/-
**Nat.Primes.not_summable_one_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nat.Primes.not_summable_one_div : ¬ Summable (fun p : Nat.Primes => (1 / p
 : Real))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `summable_subtype_iff_indicator`：∀ {α : Type u_1} {β : Type u_2} [inst : 
AddCommMonoid α] [inst_1 : TopologicalSpace α] {f : β → α} {s : Set β},   Summab
le (f ∘ Subtype.val)…
· 使用定理 `not_summable_one_div_on_primes`：not_summable_one_div_on_primes : ¬ Summa
ble (indicator {p | p.Prime} (fun n : Nat => (1 : Real) / n))

--- 原说明 ---
The sum over the reciprocals of the primes diverges.
-/
theorem Nat.Primes.not_summable_one_div : ¬ Summable (fun p : Nat.Primes ↦ (1 / p : ℝ)) := by
  convert! summable_subtype_iff_indicator.mp.mt not_summable_one_div_on_primes

/-- The series over `p^r` for primes `p` converges if and only if `r < -1`. -/
/-
**Nat.Primes.summable_rpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nat.Primes.summable_rpow {r : Real} : Summable (fun p : Nat.Primes => (p :
 Real) ^ r) ↔ r < -1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `Summable.subtype`：∀ {α : Type u_1} {β : Type u_2} [inst : UniformSpace α
] [inst_1 : AddCommGroup α] [IsUniformAddGroup α] {f : β → α}   [CompleteSpace α
], Sum…
· 使用定理 `instIsUniformAddGroupReal`：IsUniformAddGroup ℝ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Real.summable_nat_rpow`：summable_nat_rpow {p : Real} : Summable (fun n =
> (n : Real) ^ p : Nat -> Real) ↔ p < -1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `Nat.Primes.not_summable_one_div`：Nat.Primes.not_summable_one_div : ¬ Sum
mable (fun p : Nat.Primes => (1 / p : Real))
· 使用定理 `Summable.of_nonneg_of_le`：Summable.of_nonneg_of_le {f g : β -> Real} (hg
 : forall b, 0 <= g b) (hgf : forall b, g b <= f b) (hf : Summable f) : Summable
 g
· 使用引理 `Mathlib.Meta.Positivity.div_nonneg_of_pos_of_nonneg`：div_nonneg_of_pos_o
f_nonneg [PosMulReflectLT α] (ha : 0 < a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.rpow_neg_one`：rpow_neg_one (x : Real) : x ^ (-1 : Real) = x⁻¹
· 使用定理 `Real.rpow_le_rpow_of_exponent_le`：rpow_le_rpow_of_exponent_le (hx : 1 <=
 x) (hyz : y <= z) : x ^ y <= x ^ z
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
The series over `p^r` for primes `p` converges if and only if `r < -1`.
-/
theorem Nat.Primes.summable_rpow {r : ℝ} :
    Summable (fun p : Nat.Primes ↦ (p : ℝ) ^ r) ↔ r < -1 := by
  by_cases h : r < -1
  · -- case `r < -1`
    simp only [h, iff_true]
    exact (Real.summable_nat_rpow.mpr h).subtype _
  · -- case `-1 ≤ r`
    simp only [h, iff_false]
    refine fun H ↦ Nat.Primes.not_summable_one_div <| H.of_nonneg_of_le (fun _ ↦ by positivity) ?_
    intro p
    rw [one_div, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast p.prop.one_lt.le) <| not_lt.mp h
