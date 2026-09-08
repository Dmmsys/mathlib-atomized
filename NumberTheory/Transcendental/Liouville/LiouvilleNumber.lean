/-
Copyright (c) 2020 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa, Jujian Zhang
-/
module

public import Mathlib.NumberTheory.Transcendental.Liouville.Basic

/-!

# Liouville constants

This file contains a construction of a family of Liouville numbers, indexed by a natural number $m$.
The most important property is that they are examples of transcendental real numbers.
This fact is recorded in `transcendental_liouvilleNumber`.

More precisely, for a real number $m$, Liouville's constant is
$$
\sum_{i=0}^\infty\frac{1}{m^{i!}}.
$$
The series converges only for $1 < m$. However, there is no restriction on $m$, since,
if the series does not converge, then the sum of the series is defined to be zero.

We prove that, for $m \in \mathbb{N}$ satisfying $2 \le m$, Liouville's constant associated to $m$
is a transcendental number. Classically, the Liouville number for $m = 2$ is the one called
"Liouville's constant".

## Implementation notes

The indexing $m$ is eventually a natural number satisfying $2 ≤ m$. However, we prove the first few
lemmas for $m \in \mathbb{R}$.
-/

@[expose] public section


noncomputable section

open scoped Nat

open Real Finset

/-- For a real number `m`, Liouville's constant is
$$
\sum_{i=0}^\infty\frac{1}{m^{i!}}.
$$
The series converges only for `1 < m`. However, there is no restriction on `m`, since,
if the series does not converge, then the sum of the series is defined to be zero.
-/
/-
**liouvilleNumber** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：liouvilleNumber (m : Real) : Real
参数：m : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a real number `m`, Liouville's constant is
$$
\sum_{i=0}^\infty\frac{1}{m^{i!}}.
$$
The series converges only for `1 < m`. However, there is no restriction on `m`, 
since,
if the series does not converge, then the sum of the series is defined to be zer
o.
-/
def liouvilleNumber (m : ℝ) : ℝ :=
  ∑' i : ℕ, 1 / m ^ i !

namespace LiouvilleNumber

/-- `LiouvilleNumber.partialSum` is the sum of the first `k + 1` terms of Liouville's constant,
i.e.
$$
\sum_{i=0}^k\frac{1}{m^{i!}}.
$$
-/
/-
**LiouvilleNumber.partialSum** 是 Mathlib 中的一个定义，位于命名空间 `LiouvilleNumber`。
形式化陈述：partialSum (m : Real) (k : Nat) : Real
参数：m : Real；k : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`LiouvilleNumber.partialSum` is the sum of the first `k + 1` terms of Liouville'
s constant,
i.e.
$$
\sum_{i=0}^k\frac{1}{m^{i!}}.
$$
-/
def partialSum (m : ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ range (k + 1), 1 / m ^ i !

/-- `LiouvilleNumber.remainder` is the sum of the series of the terms in `liouvilleNumber m`
starting from `k+1`, i.e
$$
\sum_{i=k+1}^\infty\frac{1}{m^{i!}}.
$$
-/
/-
**LiouvilleNumber.remainder** 是 Mathlib 中的一个定义，位于命名空间 `LiouvilleNumber`。
形式化陈述：remainder (m : Real) (k : Nat) : Real
参数：m : Real；k : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`LiouvilleNumber.remainder` is the sum of the series of the terms in `liouvilleN
umber m`
starting from `k+1`, i.e
$$
\sum_{i=k+1}^\infty\frac{1}{m^{i!}}.
$$
-/
def remainder (m : ℝ) (k : ℕ) : ℝ :=
  ∑' i, 1 / m ^ (i + (k + 1))!

/-!
We start with simple observations.
-/


/-
**LiouvilleNumber.summable** 是 Mathlib 中的一个定理，位于命名空间 `LiouvilleNumber`。
形式化陈述：∀ {m : ℝ}, 1 < m → Summable fun i => 1 / m ^ i.factorial
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `summable_one_div_pow_of_le`：summable_one_div_pow_of_le {m : Real} {f : N
at -> Nat} (hm : 1 < m) (fi : forall i, i <= f i) : Summable fun i => 1 / m ^ f 
i
· 使用定理 `Nat.self_le_factorial`：∀ (n : ℕ), n ≤ n.factorial

--- 原说明 ---
We start with simple observations.
-/
protected theorem summable {m : ℝ} (hm : 1 < m) : Summable fun i : ℕ => 1 / m ^ i ! :=
  summable_one_div_pow_of_le hm Nat.self_le_factorial
/-
**LiouvilleNumber.remainder_summable** 是 Mathlib 中的一个定理，位于命名空间 `LiouvilleNumber`
。
形式化陈述：remainder_summable {m : Real} (hm : 1 < m) (k : Nat) : Summable fun i : Na
t => 1 / m ^ (i + (k + 1))!
参数：hm : 1 < m；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `summable_nat_add_iff`：∀ {G : Type u_2} [inst : AddCommGroup G] [inst_1 :
 TopologicalSpace G] [IsTopologicalAddGroup G] {f : ℕ → G} (k : ℕ),   (Summable 
fun n => f…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `LiouvilleNumber.summable`：∀ {m : ℝ}, 1 < m → Summable fun i => 1 / m ^ i
.factorial
-/
theorem remainder_summable {m : ℝ} (hm : 1 < m) (k : ℕ) :
    Summable fun i : ℕ => 1 / m ^ (i + (k + 1))! := by
  convert! (summable_nat_add_iff (k + 1)).2 (LiouvilleNumber.summable hm)
/-
**LiouvilleNumber.remainder_pos** 是 Mathlib 中的一个定理，位于命名空间 `LiouvilleNumber`。
形式化陈述：remainder_pos {m : Real} (hm : 1 < m) (k : Nat) : 0 < remainder m k
参数：hm : 1 < m；k : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.tsum_pos`：∀ {ι : Type u_1} {α : Type u_3} {L : SummationFilter 
ι} [inst : AddCommGroup α] [inst_1 : PartialOrder α]   [IsOrderedAddMonoid α] [i
nst_3 :…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `LiouvilleNumber.remainder_summable`：remainder_summable {m : Real} (hm : 
1 < m) (k : Nat) : Summable fun i : Nat => 1 / m ^ (i + (k + 1))!
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
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
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
-/
theorem remainder_pos {m : ℝ} (hm : 1 < m) (k : ℕ) : 0 < remainder m k :=
  (remainder_summable hm k).tsum_pos (fun _ => by positivity) 0 (by positivity)
/-
**LiouvilleNumber.partialSum_succ** 是 Mathlib 中的一个定理，位于命名空间 `LiouvilleNumber`。
形式化陈述：partialSum_succ (m : Real) (n : Nat) : partialSum m (n + 1) = partialSum m
 n + 1 / m ^ (n + 1)!
参数：m : Real；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_range_succ`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ 
→ M) (n : ℕ),   ∑ x ∈ Finset.range (n + 1), f x = ∑ x ∈ Finset.range n, f x + f 
n
-/
theorem partialSum_succ (m : ℝ) (n : ℕ) :
    partialSum m (n + 1) = partialSum m n + 1 / m ^ (n + 1)! :=
  sum_range_succ _ _

/-- Split the sum defining a Liouville number into the first `k` terms and the rest. -/
/-
**LiouvilleNumber.partialSum_add_remainder** 是 Mathlib 中的一个定理，位于命名空间 `LiouvilleN
umber`。
形式化陈述：partialSum_add_remainder {m : Real} (hm : 1 < m) (k : Nat) : partialSum m 
k + remainder m k = liouvilleNumber m
参数：hm : 1 < m；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.sum_add_tsum_nat_add`：∀ {G : Type u_2} [inst : AddCommGroup G] 
[inst_1 : TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G] {f : ℕ → G} 
  (k : ℕ), Summable…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `LiouvilleNumber.summable`：∀ {m : ℝ}, 1 < m → Summable fun i => 1 / m ^ i
.factorial

--- 原说明 ---
Split the sum defining a Liouville number into the first `k` terms and the rest.
-/
theorem partialSum_add_remainder {m : ℝ} (hm : 1 < m) (k : ℕ) :
    partialSum m k + remainder m k = liouvilleNumber m :=
  (LiouvilleNumber.summable hm).sum_add_tsum_nat_add _

/-! We now prove two useful inequalities, before collecting everything together. -/


/-- An upper estimate on the remainder. This estimate works with `m ∈ ℝ` satisfying `1 < m` and is
stronger than the estimate `LiouvilleNumber.remainder_lt` below. However, the latter estimate is
more useful for the proof. -/
/-
**LiouvilleNumber.remainder_lt'** 是 Mathlib 中的一个定理，位于命名空间 `LiouvilleNumber`。
形式化陈述：remainder_lt' (n : Nat) {m : Real} (m1 : 1 < m) : remainder m n < (1 - 1 /
 m)⁻¹ * (1 / m ^ (n + 1)!)
参数：n : Nat；m1 : 1 < m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `div_lt_one`：div_lt_one (hb : 0 < b) : a / b < 1 ↔ a < b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Summable.tsum_lt_tsum`：∀ {ι : Type u_1} {α : Type u_3} {L : SummationFil
ter ι} [inst : AddCommGroup α] [inst_1 : PartialOrder α]   [IsOrderedAddMonoid α
] [inst_3 :…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `one_div_pow_le_one_div_pow_of_le`：one_div_pow_le_one_div_pow_of_le (a1 :
 1 <= a) {m n : Nat} (mn : m <= n) : 1 / a ^ n <= 1 / a ^ m
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.add_factorial_succ_le_factorial_add_succ`：add_factorial_succ_le_fact
orial_add_succ (i : Nat) (n : Nat) : i + (n + 1)! <= (i + (n + 1))!
· 使用定理 `one_div_pow_strictAnti`：one_div_pow_strictAnti (a1 : 1 < a) : StrictAnti
 fun n : Nat => 1 / a ^ n
· 使用定理 `Nat.add_factorial_succ_lt_factorial_add_succ`：add_factorial_succ_lt_fact
orial_add_succ {i : Nat} (n : Nat) (hi : 2 <= i) : i + (n + 1)! < (i + n + 1)!
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `LiouvilleNumber.remainder_summable`：remainder_summable {m : Real} (hm : 
1 < m) (k : Nat) : Summable fun i : Nat => 1 / m ^ (i + (k + 1))!
· 使用定理 `summable_one_div_pow_of_le`：summable_one_div_pow_of_le {m : Real} {f : N
at -> Nat} (hm : 1 < m) (fi : forall i, i <= f i) : Summable fun i => 1 / m ^ f 
i
· 使用定理 `le_self_add`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ a + b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
（共 46 条，此处仅展示前 30 条）

--- 原说明 ---
An upper estimate on the remainder. This estimate works with `m ∈ ℝ` satisfying 
`1 < m` and is
stronger than the estimate `LiouvilleNumber.remainder_lt` below. However, the la
tter estimate is
more useful for the proof.
-/
theorem remainder_lt' (n : ℕ) {m : ℝ} (m1 : 1 < m) :
    remainder m n < (1 - 1 / m)⁻¹ * (1 / m ^ (n + 1)!) :=
  -- two useful inequalities
  have m0 : 0 < m := zero_lt_one.trans m1
  have mi : 1 / m < 1 := (div_lt_one m0).mpr m1
  -- to show the strict inequality between these series, we prove that:
  calc
    (∑' i, 1 / m ^ (i + (n + 1))!) < ∑' i, 1 / m ^ (i + (n + 1)!) :=
        -- 1. the second series dominates the first
        Summable.tsum_lt_tsum (fun b => one_div_pow_le_one_div_pow_of_le m1.le
          (b.add_factorial_succ_le_factorial_add_succ n))
        -- 2. the term with index `i = 2` of the first series is strictly smaller than
        -- the corresponding term of the second series
        (one_div_pow_strictAnti m1 (n.add_factorial_succ_lt_factorial_add_succ (i := 2) le_rfl))
        -- 3. the first series is summable
        (remainder_summable m1 n)
        -- 4. the second series is summable, since its terms grow quickly
        (summable_one_div_pow_of_le m1 fun _ => le_self_add)
    -- split the sum in the exponent and massage
    _ = ∑' i : ℕ, (1 / m) ^ i * (1 / m ^ (n + 1)!) := by
      simp only [pow_add, one_div, mul_inv, inv_pow]
    -- factor the constant `(1 / m ^ (n + 1)!)` out of the series
    _ = (∑' i, (1 / m) ^ i) * (1 / m ^ (n + 1)!) := tsum_mul_right
    -- the series is the geometric series
    _ = (1 - 1 / m)⁻¹ * (1 / m ^ (n + 1)!) := by rw [tsum_geometric_of_lt_one (by positivity) mi]
/-
**LiouvilleNumber.aux_calc** 是 Mathlib 中的一个定理，位于命名空间 `LiouvilleNumber`。
形式化陈述：aux_calc (n : Nat) {m : Real} (hm : 2 <= m) : (1 - 1 / m)⁻¹ * (1 / m ^ (n 
+ 1)!) <= 1 / (m ^ n !) ^ n
参数：n : Nat；hm : 2 <= m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `sub_one_div_inv_le_two`：sub_one_div_inv_le_two (a2 : 2 <= a) : (1 - 1 / 
a)⁻¹ <= 2
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `mul_one_div`：mul_one_div (x y : G) : x * (1 / y) = x / y
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用引理 `div_le_div_iff₀`：div_le_div_iff₀ (hb : 0 < b) (hd : 0 < d) : a / b <= c 
/ d ↔ a * d <= c * b
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_add_one`：mul_add_one [LeftDistribClass α] (a b : α) : a * (b + 1) = 
a * b + a
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
（共 36 条，此处仅展示前 30 条）
-/
theorem aux_calc (n : ℕ) {m : ℝ} (hm : 2 ≤ m) :
    (1 - 1 / m)⁻¹ * (1 / m ^ (n + 1)!) ≤ 1 / (m ^ n !) ^ n :=
  calc
    (1 - 1 / m)⁻¹ * (1 / m ^ (n + 1)!) ≤ 2 * (1 / m ^ (n + 1)!) := by
      -- the second factors coincide (and are non-negative),
      -- the first factors satisfy the inequality `sub_one_div_inv_le_two`
      gcongr; exact sub_one_div_inv_le_two hm
    _ = 2 / m ^ (n + 1)! := mul_one_div 2 _
    _ = 2 / m ^ (n ! * (n + 1)) := (congr_arg (2 / ·) (congr_arg (Pow.pow m) (mul_comm _ _)))
    _ ≤ 1 / (m ^ n !) ^ n := by
      -- Clear denominators and massage*
      rw [← pow_mul, div_le_div_iff₀, one_mul, mul_add_one, pow_add, mul_comm 2]
      · gcongr
        -- `2 ≤ m ^ n!` is a consequence of monotonicity of exponentiation at `2 ≤ m`.
        exact hm.trans <| le_self_pow₀ (one_le_two.trans hm) <| by positivity
      all_goals positivity

/-- An upper estimate on the remainder. This estimate works with `m ∈ ℝ` satisfying `2 ≤ m` and is
weaker than the estimate `LiouvilleNumber.remainder_lt'` above. However, this estimate is
more useful for the proof. -/
/-
**LiouvilleNumber.remainder_lt** 是 Mathlib 中的一个定理，位于命名空间 `LiouvilleNumber`。
形式化陈述：remainder_lt (n : Nat) {m : Real} (m2 : 2 <= m) : remainder m n < 1 / (m ^
 n !) ^ n
参数：n : Nat；m2 : 2 <= m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `LiouvilleNumber.remainder_lt'`：remainder_lt' (n : Nat) {m : Real} (m1 : 
1 < m) : remainder m n < (1 - 1 / m)⁻¹ * (1 / m ^ (n + 1)!)
· 使用引理 `one_lt_two`：one_lt_two [AddLeftStrictMono α] : (1 : α) < 2
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LiouvilleNumber.aux_calc`：aux_calc (n : Nat) {m : Real} (hm : 2 <= m) : 
(1 - 1 / m)⁻¹ * (1 / m ^ (n + 1)!) <= 1 / (m ^ n !) ^ n

--- 原说明 ---
An upper estimate on the remainder. This estimate works with `m ∈ ℝ` satisfying 
`2 ≤ m` and is
weaker than the estimate `LiouvilleNumber.remainder_lt'` above. However, this es
timate is
more useful for the proof.
-/
theorem remainder_lt (n : ℕ) {m : ℝ} (m2 : 2 ≤ m) : remainder m n < 1 / (m ^ n !) ^ n :=
  (remainder_lt' n <| one_lt_two.trans_le m2).trans_le (aux_calc _ m2)

/-! Starting from here, we specialize to the case in which `m` is a natural number. -/


/-- The sum of the `k` initial terms of the Liouville number to base `m` is a ratio of natural
numbers where the denominator is `m ^ k!`. -/
/-
**LiouvilleNumber.partialSum_eq_rat** 是 Mathlib 中的一个定理，位于命名空间 `LiouvilleNumber`。
形式化陈述：partialSum_eq_rat {m : Nat} (hm : 0 < m) (k : Nat) : exists p : Nat, parti
alSum m k = p / ((m ^ k ! :) : Real)
参数：hm : 0 < m；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LiouvilleNumber.partialSum.eq_1`：∀ (m : ℝ) (k : ℕ), LiouvilleNumber.part
ialSum m k = ∑ i ∈ Finset.range (k + 1), 1 / m ^ i.factorial
· 使用定理 `Finset.range_one`：range_one : range 1 = {0}
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.factorial.eq_1`：Nat.factorial 0 = 1
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `LiouvilleNumber.partialSum_succ`：partialSum_succ (m : Real) (n : Nat) : 
partialSum m (n + 1) = partialSum m n + 1 / m ^ (n + 1)!
· 使用定理 `div_add_div`：div_add_div (a : K) (c : K) (hb : b != 0) (hd : d != 0) : a
 / b + c / d = (a * d + b * c) / (b * d)
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos'`：cast_pos' {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用引理 `div_eq_div_iff`：div_eq_div_iff (hb : b != 0) (hd : d != 0) : a / b = c /
 d ↔ a * d = c * b
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Nat.factorial_succ`：factorial_succ (n : Nat) : (n + 1)! = (n + 1) * n !
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
The sum of the `k` initial terms of the Liouville number to base `m` is a ratio 
of natural
numbers where the denominator is `m ^ k!`.
-/
theorem partialSum_eq_rat {m : ℕ} (hm : 0 < m) (k : ℕ) :
    ∃ p : ℕ, partialSum m k = p / ((m ^ k ! :) : ℝ) := by
  induction k with
  | zero => exact ⟨1, by rw [partialSum, range_one, sum_singleton, Nat.cast_one, Nat.factorial,
      pow_one, pow_one]⟩
  | succ k h =>
    rcases h with ⟨p_k, h_k⟩
    use p_k * m ^ ((k + 1)! - k !) + 1
    rw [partialSum_succ, h_k, div_add_div, div_eq_div_iff, add_mul]
    · norm_cast
      rw [add_mul, one_mul, Nat.factorial_succ, add_mul, one_mul, add_tsub_cancel_right, pow_add]
      simp [mul_assoc]
    all_goals positivity

end LiouvilleNumber

open LiouvilleNumber

/-
**liouville_liouvilleNumber** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：liouville_liouvilleNumber {m : Nat} (hm : 2 <= m) : Liouville (liouvilleNu
mber m)
参数：hm : 2 <= m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `LiouvilleNumber.partialSum_eq_rat`：partialSum_eq_rat {m : Nat} (hm : 0 <
 m) (k : Nat) : exists p : Nat, partialSum m k = p / ((m ^ k ! :) : Real)
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `zero_lt_two`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Part
ialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `one_lt_pow₀`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preo
rder M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀],   1 < a → ∀ {n : ℕ}, n ≠ 
0…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Nat.factorial_ne_zero`：factorial_ne_zero (n : Nat) : n ! != 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Int.cast_pow`：∀ {R : Type u_1} [inst : Ring R] (n : ℤ) (m : ℕ), ↑(n ^ m)
 = ↑n ^ m
· 使用定理 `LiouvilleNumber.partialSum_add_remainder`：partialSum_add_remainder {m : 
Real} (hm : 1 < m) (k : Nat) : partialSum m k + remainder m k = liouvilleNumber 
m
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
· 使用定理 `LiouvilleNumber.remainder_pos`：remainder_pos {m : Real} (hm : 1 < m) (k 
: Nat) : 0 < remainder m k
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `abs_of_pos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], 0 < a → |a| = a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
（共 32 条，此处仅展示前 30 条）
-/
theorem liouville_liouvilleNumber {m : ℕ} (hm : 2 ≤ m) : Liouville (liouvilleNumber m) := by
  -- two useful inequalities
  have mZ1 : 1 < (m : ℤ) := by norm_cast
  have m1 : 1 < (m : ℝ) := by norm_cast
  intro n
  -- the first `n` terms sum to `p / m ^ k!`
  rcases partialSum_eq_rat (zero_lt_two.trans_le hm) n with ⟨p, hp⟩
  refine ⟨p, m ^ n !, one_lt_pow₀ mZ1 n.factorial_ne_zero, ?_⟩
  push_cast
  rw [Nat.cast_pow] at hp
  -- separate out the sum of the first `n` terms and the rest
  rw [← partialSum_add_remainder m1 n, ← hp]
  have hpos := remainder_pos m1 n
  simpa [abs_of_pos hpos, hpos.ne'] using @remainder_lt n m (by assumption_mod_cast)
/-
**transcendental_liouvilleNumber** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：transcendental_liouvilleNumber {m : Nat} (hm : 2 <= m) : Transcendental In
t (liouvilleNumber m)
参数：hm : 2 <= m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Liouville.transcendental`：∀ {x : ℝ}, Liouville x → Transcendental ℤ x
· 使用定理 `liouville_liouvilleNumber`：liouville_liouvilleNumber {m : Nat} (hm : 2 <
= m) : Liouville (liouvilleNumber m)
-/
theorem transcendental_liouvilleNumber {m : ℕ} (hm : 2 ≤ m) :
    Transcendental ℤ (liouvilleNumber m) :=
  (liouville_liouvilleNumber hm).transcendental
