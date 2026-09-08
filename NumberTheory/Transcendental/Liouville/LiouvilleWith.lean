/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.NumberTheory.Transcendental.Liouville.Basic
public import Mathlib.Topology.Instances.Irrational

/-!
# Liouville numbers with a given exponent

We say that a real number `x` is a Liouville number with exponent `p : ℝ` if there exists a real
number `C` such that for infinitely many denominators `n` there exists a numerator `m` such that
`x ≠ m / n` and `|x - m / n| < C / n ^ p`. A number is a Liouville number in the sense of
`Liouville` if it is `LiouvilleWith` any real exponent, see `forall_liouvilleWith_iff`.

* If `p ≤ 1`, then this condition is trivial.

* If `1 < p ≤ 2`, then this condition is equivalent to `Irrational x`. The forward implication
  does not require `p ≤ 2` and is formalized as `LiouvilleWith.irrational`; the other implication
  follows from approximations by continued fractions and is not formalized yet.

* If `p > 2`, then this is a non-trivial condition on irrational numbers. In particular,
  [Thue–Siegel–Roth theorem](https://en.wikipedia.org/wiki/Roth's_theorem) states that such numbers
  must be transcendental.

In this file we define the predicate `LiouvilleWith` and prove some basic facts about this
predicate.

## Tags

Liouville number, irrational, irrationality exponent
-/

@[expose] public section


open Filter Metric Real Set

open scoped Filter Topology

/-- We say that a real number `x` is a Liouville number with exponent `p : ℝ` if there exists a real
number `C` such that for infinitely many denominators `n` there exists a numerator `m` such that
`x ≠ m / n` and `|x - m / n| < C / n ^ p`.

A number is a Liouville number in the sense of `Liouville` if it is `LiouvilleWith` any real
exponent. -/
/-
**LiouvilleWith** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LiouvilleWith (p x : Real) : Prop
参数：p x : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that a real number `x` is a Liouville number with exponent `p : ℝ` if the
re exists a real
number `C` such that for infinitely many denominators `n` there exists a numerat
or `m` such that
`x ≠ m / n` and `|x - m / n| < C / n ^ p`.

A number is a Liouville number in the sense of `Liouville` if it is `LiouvilleWi
th` any real
exponent.
-/
def LiouvilleWith (p x : ℝ) : Prop :=
  ∃ C, ∃ᶠ n : ℕ in atTop, ∃ m : ℤ, x ≠ m / n ∧ |x - m / n| < C / n ^ p

/-- For `p = 1` (hence, for any `p ≤ 1`), the condition `LiouvilleWith p x` is trivial. -/
/-
**liouvilleWith_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：liouvilleWith_one (x : Real) : LiouvilleWith 1 x
参数：x : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Filter.Eventually.frequently`：∀ {α : Type u} {f : Filter α} [f.NeBot] {p
 : α → Prop}, (∀ᶠ (x : α) in f, p x) → ∃ᶠ (x : α) in f, p x
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.eventually_gt_atTop`：eventually_gt_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, a < x
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `lt_div_iff₀`：lt_div_iff₀ (hc : 0 < c) : a < b / c ↔ a * c < b
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Int.cast_add`：∀ {R : Type u} [inst : AddGroupWithOne R] (m n : ℤ), ↑(m +
 n) = ↑m + ↑n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `Int.lt_floor_add_one`：lt_floor_add_one (a : R) : a < ⌊a⌋ + 1
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `abs_sub_comm`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] 
(a b : α), |a - b| = |b - a|
· 使用定理 `abs_of_pos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], 0 < a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRightStr
ictMono α] {a b : α}, 0 < a - b ↔ b < a
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
（共 89 条，此处仅展示前 30 条）

--- 原说明 ---
For `p = 1` (hence, for any `p ≤ 1`), the condition `LiouvilleWith p x` is trivi
al.
-/
theorem liouvilleWith_one (x : ℝ) : LiouvilleWith 1 x := by
  use 2
  refine ((eventually_gt_atTop 0).mono fun n hn => ?_).frequently
  have hn' : (0 : ℝ) < n := by simpa
  have : x < ↑(⌊x * ↑n⌋ + 1) / ↑n := by
    rw [lt_div_iff₀ hn', Int.cast_add, Int.cast_one]
    exact Int.lt_floor_add_one _
  refine ⟨⌊x * n⌋ + 1, this.ne, ?_⟩
  rw [abs_sub_comm, abs_of_pos (sub_pos.2 this), rpow_one, sub_lt_iff_lt_add',
    add_div_eq_mul_add_div _ _ hn'.ne']
  gcongr
  calc _ ≤ x * n + 1 := by push_cast; gcongr; apply Int.floor_le
    _ < x * n + 2 := by linarith

namespace LiouvilleWith

variable {p q x : ℝ} {r : ℚ} {m : ℤ} {n : ℕ}

/-- The constant `C` provided by the definition of `LiouvilleWith` can be made positive.
We also add `1 ≤ n` to the list of assumptions about the denominator. While it is equivalent to
the original statement, the case `n = 0` breaks many arguments. -/
/-
**LiouvilleWith.exists_pos** 是 Mathlib 中的一个定理，位于命名空间 `LiouvilleWith`。
形式化陈述：exists_pos (h : LiouvilleWith p x) : exists (C : Real) (_h₀ : 0 < C), exis
tsᶠ n : Nat in atTop, 1 <= n ∧ exists m : Int, x != m / n ∧ |x - m / n| < C / n 
^ p
参数：h : LiouvilleWith p x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `Filter.Frequently.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∃ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.and_frequently`：∀ {α : Type u} {p q : α → Prop} {f : F
ilter α},   (∀ᶠ (x : α) in f, p x) → (∃ᶠ (x : α) in f, q x) → ∃ᶠ (x : α) in f, p
 x ∧ q x
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
· 使用引理 `div_le_div_of_nonneg_right`：div_le_div_of_nonneg_right (hab : a <= b) (h
c : 0 <= c) : a / c <= b / c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.rpow_pos_of_pos`：rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : 0 < x ^ y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos'`：cast_pos' {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n

--- 原说明 ---
The constant `C` provided by the definition of `LiouvilleWith` can be made posit
ive.
We also add `1 ≤ n` to the list of assumptions about the denominator. While it i
s equivalent to
the original statement, the case `n = 0` breaks many arguments.
-/
theorem exists_pos (h : LiouvilleWith p x) :
    ∃ (C : ℝ) (_h₀ : 0 < C),
      ∃ᶠ n : ℕ in atTop, 1 ≤ n ∧ ∃ m : ℤ, x ≠ m / n ∧ |x - m / n| < C / n ^ p := by
  rcases h with ⟨C, hC⟩
  refine ⟨max C 1, zero_lt_one.trans_le <| le_max_right _ _, ?_⟩
  refine ((eventually_ge_atTop 1).and_frequently hC).mono ?_
  rintro n ⟨hle, m, hne, hlt⟩
  refine ⟨hle, m, hne, hlt.trans_le ?_⟩
  gcongr
  apply le_max_left

/-- If a number is Liouville with exponent `p`, then it is Liouville with any smaller exponent. -/
/-
**LiouvilleWith.mono** 是 Mathlib 中的一个定理，位于命名空间 `LiouvilleWith`。
形式化陈述：mono (h : LiouvilleWith p x) (hle : q <= p) : LiouvilleWith q x
参数：h : LiouvilleWith p x；hle : q <= p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LiouvilleWith.exists_pos`：exists_pos (h : LiouvilleWith p x) : exists (C
 : Real) (_h₀ : 0 < C), existsᶠ n : Nat in atTop, 1 <= n ∧ exists m : Int, x != 
m / n ∧ |x - m…
· 使用定理 `Filter.Frequently.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∃ᶠ (x : α) in f, q x
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用引理 `div_le_div₀`：div_le_div₀ (hc : 0 <= c) (hac : a <= c) (hd : 0 < d) (hdb 
: d <= b) : a / b <= c / d
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Real.rpow_pos_of_pos`：rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : 0 < x ^ y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos'`：cast_pos' {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Real.rpow_le_rpow_of_exponent_le`：rpow_le_rpow_of_exponent_le (hx : 1 <=
 x) (hyz : y <= z) : x ^ y <= x ^ z
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1

--- 原说明 ---
If a number is Liouville with exponent `p`, then it is Liouville with any smalle
r exponent.
-/
theorem mono (h : LiouvilleWith p x) (hle : q ≤ p) : LiouvilleWith q x := by
  rcases h.exists_pos with ⟨C, hC₀, hC⟩
  refine ⟨C, hC.mono ?_⟩; rintro n ⟨hn, m, hne, hlt⟩
  refine ⟨m, hne, hlt.trans_le <| ?_⟩
  gcongr
  exact_mod_cast hn

/-- If `x` satisfies Liouville condition with exponent `p` and `q < p`, then `x`
satisfies Liouville condition with exponent `q` and constant `1`. -/
/-
**LiouvilleWith.frequently_lt_rpow_neg** 是 Mathlib 中的一个定理，位于命名空间 `LiouvilleWith`
。
形式化陈述：frequently_lt_rpow_neg (h : LiouvilleWith p x) (hlt : q < p) : existsᶠ n :
 Nat in atTop, exists m : Int, x != m / n ∧ |x - m / n| < n ^ (-q)
参数：h : LiouvilleWith p x；hlt : q < p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LiouvilleWith.exists_pos`：exists_pos (h : LiouvilleWith p x) : exists (C
 : Real) (_h₀ : 0 < C), existsᶠ n : Nat in atTop, 1 <= n ∧ exists m : Int, x != 
m / n ∧ |x - m…
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `tendsto_rpow_atTop`：tendsto_rpow_atTop {y : Real} (hy : 0 < y) : Tendsto
 (fun x : Real => x ^ y) atTop atTop
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRightStr
ictMono α] {a b : α}, 0 < a - b ↔ b < a
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
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
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `tendsto_natCast_atTop_atTop`：tendsto_natCast_atTop_atTop [Semiring R] [P
artialOrder R] [IsOrderedRing R] [Archimedean R] : Tendsto ((↑) : Nat -> R) atTo
p atTop
· 使用定理 `Filter.eventually_gt_atTop`：eventually_gt_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, a < x
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Filter.Frequently.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∃ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.and_frequently`：∀ {α : Type u} {p q : α → Prop} {f : F
ilter α},   (∀ᶠ (x : α) in f, p x) → (∃ᶠ (x : α) in f, q x) → ∃ᶠ (x : α) in f, p
 x ∧ q x
· 使用定理 `Nat.cast_pos`：cast_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRing 
α] [Nontrivial α] {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用引理 `div_lt_iff₀`：div_lt_iff₀ (hc : 0 < c) : b / c < a ↔ b < a * c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Real.rpow_pos_of_pos`：rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : 0 < x ^ y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.rpow_add`：rpow_add (hx : 0 < x) (y z : Real) : x ^ (y + z) = x ^ y 
* x ^ z
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
If `x` satisfies Liouville condition with exponent `p` and `q < p`, then `x`
satisfies Liouville condition with exponent `q` and constant `1`.
-/
theorem frequently_lt_rpow_neg (h : LiouvilleWith p x) (hlt : q < p) :
    ∃ᶠ n : ℕ in atTop, ∃ m : ℤ, x ≠ m / n ∧ |x - m / n| < n ^ (-q) := by
  rcases h.exists_pos with ⟨C, _hC₀, hC⟩
  have : ∀ᶠ n : ℕ in atTop, C < n ^ (p - q) := by
    simpa only [(· ∘ ·), neg_sub, one_div] using
      ((tendsto_rpow_atTop (sub_pos.2 hlt)).comp tendsto_natCast_atTop_atTop).eventually
        (eventually_gt_atTop C)
  refine (this.and_frequently hC).mono ?_
  rintro n ⟨hnC, hn, m, hne, hlt⟩
  replace hn : (0 : ℝ) < n := Nat.cast_pos.2 hn
  refine ⟨m, hne, hlt.trans <| (div_lt_iff₀ <| rpow_pos_of_pos hn _).2 ?_⟩
  rwa [mul_comm, ← rpow_add hn, ← sub_eq_add_neg]

/-- The product of a Liouville number and a nonzero rational number is again a Liouville number. -/
/-
**LiouvilleWith.mul_rat** 是 Mathlib 中的一个定理，位于命名空间 `LiouvilleWith`。
形式化陈述：mul_rat (h : LiouvilleWith p x) (hr : r != 0) : LiouvilleWith p (x * r)
参数：h : LiouvilleWith p x；hr : r != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LiouvilleWith.exists_pos`：exists_pos (h : LiouvilleWith p x) : exists (C
 : Real) (_h₀ : 0 < C), existsᶠ n : Nat in atTop, 1 <= n ∧ exists m : Int, x != 
m / n ∧ |x - m…
· 使用定理 `Filter.Tendsto.frequently`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∃ᶠ (x
 : α) in l₁, p …
· 使用定理 `Filter.Tendsto.nsmul_atTop`：∀ {α : Type u_1} {M : Type u_2} [inst : AddC
ommMonoid M] [inst_1 : Preorder M] [IsOrderedAddMonoid M] {l : Filter α}   {f : 
α → M}, Filter.T…
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `Rat.pos`：pos (a : Rat) : 0 < a.den
· 使用定理 `Filter.Frequently.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∃ᶠ (x : α) in f, q x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `Int.cast_mul`：cast_mul {α : Type*} [NonAssocRing α] : forall m n, ((m * 
n : Int) : α) = m * n
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Rat.cast_def`：cast_def (q : Rat) : (q : K) = q.num / q.den
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用引理 `abs_mul`：abs_mul (a b : α) : |a * b| = |a| * |b|
· 使用定理 `mul_lt_mul_of_pos_right`：mul_lt_mul_of_pos_right [MulPosStrictMono α] (h
bc : b < c) (ha : 0 < a) : b * a < c * a
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Mathlib.Meta.Positivity.abs_pos_of_ne_zero`：abs_pos_of_ne_zero {α : Type
*} [AddGroup α] [LinearOrder α] [AddLeftMono α] {a : α} : a != 0 -> 0 < |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
（共 45 条，此处仅展示前 30 条）

--- 原说明 ---
The product of a Liouville number and a nonzero rational number is again a Liouv
ille number.
-/
theorem mul_rat (h : LiouvilleWith p x) (hr : r ≠ 0) : LiouvilleWith p (x * r) := by
  rcases h.exists_pos with ⟨C, _hC₀, hC⟩
  refine ⟨r.den ^ p * (|r| * C), (tendsto_id.nsmul_atTop r.pos).frequently (hC.mono ?_)⟩
  rintro n ⟨_hn, m, hne, hlt⟩
  have A : (↑(r.num * m) : ℝ) / ↑(r.den • id n) = m / n * r := by
    simp [← div_mul_div_comm, ← r.cast_def, mul_comm]
  refine ⟨r.num * m, ?_, ?_⟩
  · rw [A]; simp [hne, hr]
  · rw [A, ← sub_mul, abs_mul]
    simp only [smul_eq_mul, id, Nat.cast_mul]
    calc _ < C / ↑n ^ p * |↑r| := by gcongr
      _ = ↑r.den ^ p * (↑|r| * C) / (↑r.den * ↑n) ^ p := ?_
    rw [mul_rpow, mul_div_mul_left, mul_comm, mul_div_assoc]
    · simp only [Rat.cast_abs]
    all_goals positivity

/-- The product `x * r`, `r : ℚ`, `r ≠ 0`, is a Liouville number with exponent `p` if and only if
`x` satisfies the same condition. -/
/-
**LiouvilleWith.mul_rat_iff** 是 Mathlib 中的一个定理，位于命名空间 `LiouvilleWith`。
形式化陈述：mul_rat_iff (hr : r != 0) : LiouvilleWith p (x * r) ↔ LiouvilleWith p x
参数：hr : r != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `Rat.cast_one`：cast_one : ((1 : Rat) : α) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `LiouvilleWith.mul_rat`：mul_rat (h : LiouvilleWith p x) (hr : r != 0) : L
iouvilleWith p (x * r)
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0

--- 原说明 ---
The product `x * r`, `r : ℚ`, `r ≠ 0`, is a Liouville number with exponent `p` i
f and only if
`x` satisfies the same condition.
-/
theorem mul_rat_iff (hr : r ≠ 0) : LiouvilleWith p (x * r) ↔ LiouvilleWith p x :=
  ⟨fun h => by
    simpa only [mul_assoc, ← Rat.cast_mul, mul_inv_cancel₀ hr, Rat.cast_one, mul_one] using
      h.mul_rat (inv_ne_zero hr),
    fun h => h.mul_rat hr⟩

/-- The product `r * x`, `r : ℚ`, `r ≠ 0`, is a Liouville number with exponent `p` if and only if
`x` satisfies the same condition. -/
/-
**LiouvilleWith.rat_mul_iff** 是 Mathlib 中的一个定理，位于命名空间 `LiouvilleWith`。
形式化陈述：rat_mul_iff (hr : r != 0) : LiouvilleWith p (r * x) ↔ LiouvilleWith p x
参数：hr : r != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `LiouvilleWith.mul_rat_iff`：mul_rat_iff (hr : r != 0) : LiouvilleWith p (
x * r) ↔ LiouvilleWith p x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
The product `r * x`, `r : ℚ`, `r ≠ 0`, is a Liouville number with exponent `p` i
f and only if
`x` satisfies the same condition.
-/
theorem rat_mul_iff (hr : r ≠ 0) : LiouvilleWith p (r * x) ↔ LiouvilleWith p x := by
  rw [mul_comm, mul_rat_iff hr]
/-
**LiouvilleWith.rat_mul** 是 Mathlib 中的一个定理，位于命名空间 `LiouvilleWith`。
形式化陈述：rat_mul (h : LiouvilleWith p x) (hr : r != 0) : LiouvilleWith p (r * x)
参数：h : LiouvilleWith p x；hr : r != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LiouvilleWith.rat_mul_iff`：rat_mul_iff (hr : r != 0) : LiouvilleWith p (
r * x) ↔ LiouvilleWith p x
-/
theorem rat_mul (h : LiouvilleWith p x) (hr : r ≠ 0) : LiouvilleWith p (r * x) :=
  (rat_mul_iff hr).2 h
/-
**LiouvilleWith.mul_int_iff** 是 Mathlib 中的一个定理，位于命名空间 `LiouvilleWith`。
形式化陈述：mul_int_iff (hm : m != 0) : LiouvilleWith p (x * m) ↔ LiouvilleWith p x
参数：hm : m != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.cast_intCast`：cast_intCast (n : Int) : ((n : Rat) : α) = n
· 使用定理 `LiouvilleWith.mul_rat_iff`：mul_rat_iff (hr : r != 0) : LiouvilleWith p (
x * r) ↔ LiouvilleWith p x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Int.cast_ne_zero`：cast_ne_zero : (n : α) != 0 ↔ n != 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mul_int_iff (hm : m ≠ 0) : LiouvilleWith p (x * m) ↔ LiouvilleWith p x := by
  rw [← Rat.cast_intCast, mul_rat_iff (Int.cast_ne_zero.2 hm)]
/-
**LiouvilleWith.mul_int** 是 Mathlib 中的一个定理，位于命名空间 `LiouvilleWith`。
形式化陈述：mul_int (h : LiouvilleWith p x) (hm : m != 0) : LiouvilleWith p (x * m)
参数：h : LiouvilleWith p x；hm : m != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LiouvilleWith.mul_int_iff`：mul_int_iff (hm : m != 0) : LiouvilleWith p (
x * m) ↔ LiouvilleWith p x
-/
theorem mul_int (h : LiouvilleWith p x) (hm : m ≠ 0) : LiouvilleWith p (x * m) :=
  (mul_int_iff hm).2 h
/-
**LiouvilleWith.int_mul_iff** 是 Mathlib 中的一个定理，位于命名空间 `LiouvilleWith`。
形式化陈述：int_mul_iff (hm : m != 0) : LiouvilleWith p (m * x) ↔ LiouvilleWith p x
参数：hm : m != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `LiouvilleWith.mul_int_iff`：mul_int_iff (hm : m != 0) : LiouvilleWith p (
x * m) ↔ LiouvilleWith p x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem int_mul_iff (hm : m ≠ 0) : LiouvilleWith p (m * x) ↔ LiouvilleWith p x := by
  rw [mul_comm, mul_int_iff hm]
/-
**LiouvilleWith.int_mul** 是 Mathlib 中的一个定理，位于命名空间 `LiouvilleWith`。
形式化陈述：int_mul (h : LiouvilleWith p x) (hm : m != 0) : LiouvilleWith p (m * x)
参数：h : LiouvilleWith p x；hm : m != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LiouvilleWith.int_mul_iff`：int_mul_iff (hm : m != 0) : LiouvilleWith p (
m * x) ↔ LiouvilleWith p x
-/
theorem int_mul (h : LiouvilleWith p x) (hm : m ≠ 0) : LiouvilleWith p (m * x) :=
  (int_mul_iff hm).2 h
/-
**LiouvilleWith.mul_nat_iff** 是 Mathlib 中的一个定理，位于命名空间 `LiouvilleWith`。
形式化陈述：mul_nat_iff (hn : n != 0) : LiouvilleWith p (x * n) ↔ LiouvilleWith p x
参数：hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.cast_natCast`：cast_natCast (n : Nat) : ((n : Rat) : α) = n
· 使用定理 `LiouvilleWith.mul_rat_iff`：mul_rat_iff (hr : r != 0) : LiouvilleWith p (
x * r) ↔ LiouvilleWith p x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mul_nat_iff (hn : n ≠ 0) : LiouvilleWith p (x * n) ↔ LiouvilleWith p x := by
  rw [← Rat.cast_natCast, mul_rat_iff (Nat.cast_ne_zero.2 hn)]
/-
**LiouvilleWith.mul_nat** 是 Mathlib 中的一个定理，位于命名空间 `LiouvilleWith`。
形式化陈述：mul_nat (h : LiouvilleWith p x) (hn : n != 0) : LiouvilleWith p (x * n)
参数：h : LiouvilleWith p x；hn : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LiouvilleWith.mul_nat_iff`：mul_nat_iff (hn : n != 0) : LiouvilleWith p (
x * n) ↔ LiouvilleWith p x
-/
theorem mul_nat (h : LiouvilleWith p x) (hn : n ≠ 0) : LiouvilleWith p (x * n) :=
  (mul_nat_iff hn).2 h
/-
**LiouvilleWith.nat_mul_iff** 是 Mathlib 中的一个定理，位于命名空间 `LiouvilleWith`。
形式化陈述：nat_mul_iff (hn : n != 0) : LiouvilleWith p (n * x) ↔ LiouvilleWith p x
参数：hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `LiouvilleWith.mul_nat_iff`：mul_nat_iff (hn : n != 0) : LiouvilleWith p (
x * n) ↔ LiouvilleWith p x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem nat_mul_iff (hn : n ≠ 0) : LiouvilleWith p (n * x) ↔ LiouvilleWith p x := by
  rw [mul_comm, mul_nat_iff hn]
/-
**LiouvilleWith.nat_mul** 是 Mathlib 中的一个定理，位于命名空间 `LiouvilleWith`。
形式化陈述：nat_mul (h : LiouvilleWith p x) (hn : n != 0) : LiouvilleWith p (n * x)
参数：h : LiouvilleWith p x；hn : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `LiouvilleWith.mul_nat`：mul_nat (h : LiouvilleWith p x) (hn : n != 0) : L
iouvilleWith p (x * n)
-/
theorem nat_mul (h : LiouvilleWith p x) (hn : n ≠ 0) : LiouvilleWith p (n * x) := by
  rw [mul_comm]; exact h.mul_nat hn
/-
**LiouvilleWith.add_rat** 是 Mathlib 中的一个定理，位于命名空间 `LiouvilleWith`。
形式化陈述：add_rat (h : LiouvilleWith p x) (r : Rat) : LiouvilleWith p (x + r)
参数：h : LiouvilleWith p x；r : Rat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LiouvilleWith.exists_pos`：exists_pos (h : LiouvilleWith p x) : exists (C
 : Real) (_h₀ : 0 < C), existsᶠ n : Nat in atTop, 1 <= n ∧ exists m : Int, x != 
m / n ∧ |x - m…
· 使用定理 `Filter.Tendsto.frequently`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∃ᶠ (x
 : α) in l₁, p …
· 使用定理 `Filter.Tendsto.nsmul_atTop`：∀ {α : Type u_1} {M : Type u_2} [inst : AddC
ommMonoid M] [inst_1 : Preorder M] [IsOrderedAddMonoid M] {l : Filter α}   {f : 
α → M}, Filter.T…
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `Rat.pos`：pos (a : Rat) : 0 < a.den
· 使用定理 `Filter.Frequently.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∃ᶠ (x : α) in f, q x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `id.eq_1`：∀ {α : Sort u} (a : α), id a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Rat.num_div_den`：num_div_den (r : Rat) : (r.num : Rat) / (r.den : Rat) =
 r
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Int.cast_add`：∀ {R : Type u} [inst : AddGroupWithOne R] (m n : ℤ), ↑(m +
 n) = ↑m + ↑n
· 使用引理 `Int.cast_mul`：cast_mul {α : Type*} [NonAssocRing α] : forall m n, ((m * 
n : Int) : α) = m * n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Rat.cast_div`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p q
 : ℚ), ↑(p / q) = ↑p / ↑q
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Rat.cast_intCast`：cast_intCast (n : Int) : ((n : Rat) : α) = n
· 使用定理 `Rat.cast_natCast`：cast_natCast (n : Nat) : ((n : Rat) : α) = n
· 使用定理 `add_div`：add_div (a b c : K) : (a + b) / c = a / c + b / c
· 使用引理 `mul_div_mul_left`：mul_div_mul_left (a b : G₀) (hc : c != 0) : c * a / (c
 * b) = a / b
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos'`：cast_pos' {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Rat.den_pos`：∀ (self : ℚ), 0 < self.den
· 使用引理 `mul_div_mul_right`：mul_div_mul_right (a b : G₀) (hc : c != 0) : a * c / 
(b * c) = a / b
（共 47 条，此处仅展示前 30 条）
-/
theorem add_rat (h : LiouvilleWith p x) (r : ℚ) : LiouvilleWith p (x + r) := by
  rcases h.exists_pos with ⟨C, _hC₀, hC⟩
  refine ⟨r.den ^ p * C, (tendsto_id.nsmul_atTop r.pos).frequently (hC.mono ?_)⟩
  rintro n ⟨hn, m, hne, hlt⟩
  have : (↑(r.den * m + r.num * n : ℤ) / ↑(r.den • id n) : ℝ) = m / n + r := by
    rw [smul_eq_mul, id]
    nth_rewrite 4 [← Rat.num_div_den r]
    push_cast
    rw [add_div, mul_div_mul_left _ _ (by positivity), mul_div_mul_right _ _ (by positivity)]
  refine ⟨r.den * m + r.num * n, ?_⟩; rw [this, add_sub_add_right_eq_sub]
  refine ⟨by simpa, hlt.trans_le (le_of_eq ?_)⟩
  have : (r.den ^ p : ℝ) ≠ 0 := by positivity
  simp [mul_rpow, mul_div_mul_left, this]

@[simp]
/-
**LiouvilleWith.add_rat_iff** 是 Mathlib 中的一个定理，位于命名空间 `LiouvilleWith`。
形式化陈述：add_rat_iff : LiouvilleWith p (x + r) ↔ LiouvilleWith p x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Rat.cast_neg`：∀ {α : Type u_3} [inst : DivisionRing α] (q : ℚ), ↑(-q) = 
-↑q
· 使用定理 `add_neg_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b + -b = a
· 使用定理 `LiouvilleWith.add_rat`：add_rat (h : LiouvilleWith p x) (r : Rat) : Liouv
illeWith p (x + r)
-/
theorem add_rat_iff : LiouvilleWith p (x + r) ↔ LiouvilleWith p x :=
  ⟨fun h => by simpa using h.add_rat (-r), fun h => h.add_rat r⟩

@[simp]
/-
**LiouvilleWith.rat_add_iff** 是 Mathlib 中的一个定理，位于命名空间 `LiouvilleWith`。
形式化陈述：rat_add_iff : LiouvilleWith p (r + x) ↔ LiouvilleWith p x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `LiouvilleWith.add_rat_iff`：add_rat_iff : LiouvilleWith p (x + r) ↔ Liouv
illeWith p x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem rat_add_iff : LiouvilleWith p (r + x) ↔ LiouvilleWith p x := by rw [add_comm, add_rat_iff]
/-
**LiouvilleWith.rat_add** 是 Mathlib 中的一个定理，位于命名空间 `LiouvilleWith`。
形式化陈述：rat_add (h : LiouvilleWith p x) (r : Rat) : LiouvilleWith p (r + x)
参数：h : LiouvilleWith p x；r : Rat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LiouvilleWith.add_rat`：add_rat (h : LiouvilleWith p x) (r : Rat) : Liouv
illeWith p (x + r)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem rat_add (h : LiouvilleWith p x) (r : ℚ) : LiouvilleWith p (r + x) :=
  add_comm x r ▸ h.add_rat r

@[simp]
/-
**LiouvilleWith.add_int_iff** 是 Mathlib 中的一个定理，位于命名空间 `LiouvilleWith`。
形式化陈述：add_int_iff : LiouvilleWith p (x + m) ↔ LiouvilleWith p x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.cast_intCast`：cast_intCast (n : Int) : ((n : Rat) : α) = n
· 使用定理 `LiouvilleWith.add_rat_iff`：add_rat_iff : LiouvilleWith p (x + r) ↔ Liouv
illeWith p x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem add_int_iff : LiouvilleWith p (x + m) ↔ LiouvilleWith p x := by
  rw [← Rat.cast_intCast m, add_rat_iff]

@[simp]
/-
**LiouvilleWith.int_add_iff** 是 Mathlib 中的一个定理，位于命名空间 `LiouvilleWith`。
形式化陈述：int_add_iff : LiouvilleWith p (m + x) ↔ LiouvilleWith p x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `LiouvilleWith.add_int_iff`：add_int_iff : LiouvilleWith p (x + m) ↔ Liouv
illeWith p x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem int_add_iff : LiouvilleWith p (m + x) ↔ LiouvilleWith p x := by rw [add_comm, add_int_iff]

@[simp]
/-
**LiouvilleWith.add_nat_iff** 是 Mathlib 中的一个定理，位于命名空间 `LiouvilleWith`。
形式化陈述：add_nat_iff : LiouvilleWith p (x + n) ↔ LiouvilleWith p x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.cast_natCast`：cast_natCast (n : Nat) : ((n : Rat) : α) = n
· 使用定理 `LiouvilleWith.add_rat_iff`：add_rat_iff : LiouvilleWith p (x + r) ↔ Liouv
illeWith p x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem add_nat_iff : LiouvilleWith p (x + n) ↔ LiouvilleWith p x := by
  rw [← Rat.cast_natCast n, add_rat_iff]

@[simp]
/-
**LiouvilleWith.nat_add_iff** 是 Mathlib 中的一个定理，位于命名空间 `LiouvilleWith`。
形式化陈述：nat_add_iff : LiouvilleWith p (n + x) ↔ LiouvilleWith p x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `LiouvilleWith.add_nat_iff`：add_nat_iff : LiouvilleWith p (x + n) ↔ Liouv
illeWith p x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem nat_add_iff : LiouvilleWith p (n + x) ↔ LiouvilleWith p x := by rw [add_comm, add_nat_iff]
/-
**LiouvilleWith.add_int** 是 Mathlib 中的一个定理，位于命名空间 `LiouvilleWith`。
形式化陈述：add_int (h : LiouvilleWith p x) (m : Int) : LiouvilleWith p (x + m)
参数：h : LiouvilleWith p x；m : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LiouvilleWith.add_int_iff`：add_int_iff : LiouvilleWith p (x + m) ↔ Liouv
illeWith p x
-/
theorem add_int (h : LiouvilleWith p x) (m : ℤ) : LiouvilleWith p (x + m) :=
  add_int_iff.2 h
/-
**LiouvilleWith.int_add** 是 Mathlib 中的一个定理，位于命名空间 `LiouvilleWith`。
形式化陈述：int_add (h : LiouvilleWith p x) (m : Int) : LiouvilleWith p (m + x)
参数：h : LiouvilleWith p x；m : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LiouvilleWith.int_add_iff`：int_add_iff : LiouvilleWith p (m + x) ↔ Liouv
illeWith p x
-/
theorem int_add (h : LiouvilleWith p x) (m : ℤ) : LiouvilleWith p (m + x) :=
  int_add_iff.2 h
/-
**LiouvilleWith.add_nat** 是 Mathlib 中的一个定理，位于命名空间 `LiouvilleWith`。
形式化陈述：add_nat (h : LiouvilleWith p x) (n : Nat) : LiouvilleWith p (x + n)
参数：h : LiouvilleWith p x；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LiouvilleWith.add_int`：add_int (h : LiouvilleWith p x) (m : Int) : Liouv
illeWith p (x + m)
-/
theorem add_nat (h : LiouvilleWith p x) (n : ℕ) : LiouvilleWith p (x + n) :=
  h.add_int n
/-
**LiouvilleWith.nat_add** 是 Mathlib 中的一个定理，位于命名空间 `LiouvilleWith`。
形式化陈述：nat_add (h : LiouvilleWith p x) (n : Nat) : LiouvilleWith p (n + x)
参数：h : LiouvilleWith p x；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LiouvilleWith.int_add`：int_add (h : LiouvilleWith p x) (m : Int) : Liouv
illeWith p (m + x)
-/
theorem nat_add (h : LiouvilleWith p x) (n : ℕ) : LiouvilleWith p (n + x) :=
  h.int_add n
/-
**LiouvilleWith.neg** 是 Mathlib 中的一个定理，位于命名空间 `LiouvilleWith`。
形式化陈述：∀ {p x : ℝ}, LiouvilleWith p x → LiouvilleWith p (-x)
参数：-x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Frequently.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∃ᶠ (x : α) in f, q x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用引理 `neg_div`：neg_div (a b : R) : -b / a = -(b / a)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `abs_sub_comm`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] 
(a b : α), |a - b| = |b - a|
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
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
· 使用定理 `Mathlib.Tactic.Ring.Common.div_pf`：∀ {R : Type u_2} [inst : Semifield R]
 {a b c d : R}, b⁻¹ = c → a * c = d → a / b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_single`：∀ {R : Type u_2} [inst : Semifiel
d R] {a b : R}, a⁻¹ = b → (a + 0)⁻¹ = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_mul`：∀ {R : Type u_2} [inst : Semifield R
] {a₁ : R} {a₂ : ℕ} {a₃ b₁ b₃ c : R},   a₁⁻¹ = b₁ → a₃⁻¹ = b₃ → b₃ * (b₁ ^ a₂ * 
Nat.rawCast 1) = c → (a₁…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_isNat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n 1 → Mathlib.Meta.NormNum
.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
（共 47 条，此处仅展示前 30 条）
-/
protected theorem neg (h : LiouvilleWith p x) : LiouvilleWith p (-x) := by
  rcases h with ⟨C, hC⟩
  refine ⟨C, hC.mono ?_⟩
  rintro n ⟨m, hne, hlt⟩
  refine ⟨-m, by simp [neg_div, hne], ?_⟩
  convert! hlt using 1
  rw [abs_sub_comm]
  congr! 1; push_cast; ring

@[simp]
/-
**LiouvilleWith.neg_iff** 是 Mathlib 中的一个定理，位于命名空间 `LiouvilleWith`。
形式化陈述：neg_iff : LiouvilleWith p (-x) ↔ LiouvilleWith p x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LiouvilleWith.neg`：∀ {p x : ℝ}, LiouvilleWith p x → LiouvilleWith p (-x)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
theorem neg_iff : LiouvilleWith p (-x) ↔ LiouvilleWith p x :=
  ⟨fun h => neg_neg x ▸ h.neg, LiouvilleWith.neg⟩

@[simp]
/-
**LiouvilleWith.sub_rat_iff** 是 Mathlib 中的一个定理，位于命名空间 `LiouvilleWith`。
形式化陈述：sub_rat_iff : LiouvilleWith p (x - r) ↔ LiouvilleWith p x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.cast_neg`：∀ {α : Type u_3} [inst : DivisionRing α] (q : ℚ), ↑(-q) = 
-↑q
· 使用定理 `LiouvilleWith.add_rat_iff`：add_rat_iff : LiouvilleWith p (x + r) ↔ Liouv
illeWith p x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sub_rat_iff : LiouvilleWith p (x - r) ↔ LiouvilleWith p x := by
  rw [sub_eq_add_neg, ← Rat.cast_neg, add_rat_iff]
/-
**LiouvilleWith.sub_rat** 是 Mathlib 中的一个定理，位于命名空间 `LiouvilleWith`。
形式化陈述：sub_rat (h : LiouvilleWith p x) (r : Rat) : LiouvilleWith p (x - r)
参数：h : LiouvilleWith p x；r : Rat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LiouvilleWith.sub_rat_iff`：sub_rat_iff : LiouvilleWith p (x - r) ↔ Liouv
illeWith p x
-/
theorem sub_rat (h : LiouvilleWith p x) (r : ℚ) : LiouvilleWith p (x - r) :=
  sub_rat_iff.2 h

@[simp]
/-
**LiouvilleWith.sub_int_iff** 是 Mathlib 中的一个定理，位于命名空间 `LiouvilleWith`。
形式化陈述：sub_int_iff : LiouvilleWith p (x - m) ↔ LiouvilleWith p x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.cast_intCast`：cast_intCast (n : Int) : ((n : Rat) : α) = n
· 使用定理 `LiouvilleWith.sub_rat_iff`：sub_rat_iff : LiouvilleWith p (x - r) ↔ Liouv
illeWith p x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sub_int_iff : LiouvilleWith p (x - m) ↔ LiouvilleWith p x := by
  rw [← Rat.cast_intCast, sub_rat_iff]
/-
**LiouvilleWith.sub_int** 是 Mathlib 中的一个定理，位于命名空间 `LiouvilleWith`。
形式化陈述：sub_int (h : LiouvilleWith p x) (m : Int) : LiouvilleWith p (x - m)
参数：h : LiouvilleWith p x；m : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LiouvilleWith.sub_int_iff`：sub_int_iff : LiouvilleWith p (x - m) ↔ Liouv
illeWith p x
-/
theorem sub_int (h : LiouvilleWith p x) (m : ℤ) : LiouvilleWith p (x - m) :=
  sub_int_iff.2 h

@[simp]
/-
**LiouvilleWith.sub_nat_iff** 是 Mathlib 中的一个定理，位于命名空间 `LiouvilleWith`。
形式化陈述：sub_nat_iff : LiouvilleWith p (x - n) ↔ LiouvilleWith p x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.cast_natCast`：cast_natCast (n : Nat) : ((n : Rat) : α) = n
· 使用定理 `LiouvilleWith.sub_rat_iff`：sub_rat_iff : LiouvilleWith p (x - r) ↔ Liouv
illeWith p x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sub_nat_iff : LiouvilleWith p (x - n) ↔ LiouvilleWith p x := by
  rw [← Rat.cast_natCast, sub_rat_iff]
/-
**LiouvilleWith.sub_nat** 是 Mathlib 中的一个定理，位于命名空间 `LiouvilleWith`。
形式化陈述：sub_nat (h : LiouvilleWith p x) (n : Nat) : LiouvilleWith p (x - n)
参数：h : LiouvilleWith p x；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LiouvilleWith.sub_nat_iff`：sub_nat_iff : LiouvilleWith p (x - n) ↔ Liouv
illeWith p x
-/
theorem sub_nat (h : LiouvilleWith p x) (n : ℕ) : LiouvilleWith p (x - n) :=
  sub_nat_iff.2 h

@[simp]
/-
**LiouvilleWith.rat_sub_iff** 是 Mathlib 中的一个定理，位于命名空间 `LiouvilleWith`。
形式化陈述：rat_sub_iff : LiouvilleWith p (r - x) ↔ LiouvilleWith p x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem rat_sub_iff : LiouvilleWith p (r - x) ↔ LiouvilleWith p x := by simp [sub_eq_add_neg]
/-
**LiouvilleWith.rat_sub** 是 Mathlib 中的一个定理，位于命名空间 `LiouvilleWith`。
形式化陈述：rat_sub (h : LiouvilleWith p x) (r : Rat) : LiouvilleWith p (r - x)
参数：h : LiouvilleWith p x；r : Rat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LiouvilleWith.rat_sub_iff`：rat_sub_iff : LiouvilleWith p (r - x) ↔ Liouv
illeWith p x
-/
theorem rat_sub (h : LiouvilleWith p x) (r : ℚ) : LiouvilleWith p (r - x) :=
  rat_sub_iff.2 h

@[simp]
/-
**LiouvilleWith.int_sub_iff** 是 Mathlib 中的一个定理，位于命名空间 `LiouvilleWith`。
形式化陈述：int_sub_iff : LiouvilleWith p (m - x) ↔ LiouvilleWith p x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem int_sub_iff : LiouvilleWith p (m - x) ↔ LiouvilleWith p x := by simp [sub_eq_add_neg]
/-
**LiouvilleWith.int_sub** 是 Mathlib 中的一个定理，位于命名空间 `LiouvilleWith`。
形式化陈述：int_sub (h : LiouvilleWith p x) (m : Int) : LiouvilleWith p (m - x)
参数：h : LiouvilleWith p x；m : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LiouvilleWith.int_sub_iff`：int_sub_iff : LiouvilleWith p (m - x) ↔ Liouv
illeWith p x
-/
theorem int_sub (h : LiouvilleWith p x) (m : ℤ) : LiouvilleWith p (m - x) :=
  int_sub_iff.2 h

@[simp]
/-
**LiouvilleWith.nat_sub_iff** 是 Mathlib 中的一个定理，位于命名空间 `LiouvilleWith`。
形式化陈述：nat_sub_iff : LiouvilleWith p (n - x) ↔ LiouvilleWith p x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem nat_sub_iff : LiouvilleWith p (n - x) ↔ LiouvilleWith p x := by simp [sub_eq_add_neg]
/-
**LiouvilleWith.nat_sub** 是 Mathlib 中的一个定理，位于命名空间 `LiouvilleWith`。
形式化陈述：nat_sub (h : LiouvilleWith p x) (n : Nat) : LiouvilleWith p (n - x)
参数：h : LiouvilleWith p x；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LiouvilleWith.nat_sub_iff`：nat_sub_iff : LiouvilleWith p (n - x) ↔ Liouv
illeWith p x
-/
theorem nat_sub (h : LiouvilleWith p x) (n : ℕ) : LiouvilleWith p (n - x) :=
  nat_sub_iff.2 h
/-
**LiouvilleWith.ne_cast_int** 是 Mathlib 中的一个定理，位于命名空间 `LiouvilleWith`。
形式化陈述：ne_cast_int (h : LiouvilleWith p x) (hp : 1 < p) (m : Int) : x != m
参数：h : LiouvilleWith p x；hp : 1 < p；m : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Frequently.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `Filter.Eventually.and_frequently`：∀ {α : Type u} {p q : α → Prop} {f : F
ilter α},   (∀ᶠ (x : α) in f, p x) → (∃ᶠ (x : α) in f, q x) → ∃ᶠ (x : α) in f, p
 x ∧ q x
· 使用定理 `Filter.eventually_gt_atTop`：eventually_gt_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, a < x
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `LiouvilleWith.frequently_lt_rpow_neg`：frequently_lt_rpow_neg (h : Liouvi
lleWith p x) (hlt : q < p) : existsᶠ n : Nat in atTop, exists m : Int, x != m / 
n ∧ |x - m / n| < n ^ (-q)
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_neg_one`：rpow_neg_one (x : Real) : x ^ (-1 : Real) = x⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `sub_div'`：sub_div' {a b c : K} (hc : c != 0) : b - a / c = (b * c - a) /
 c
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `abs_div`：abs_div (a b : α) : |a / b| = |a| / |b|
· 使用定理 `Nat.abs_cast`：abs_cast (n : Nat) : |(n : R)| = n
· 使用引理 `div_le_div_of_nonneg_right`：div_le_div_of_nonneg_right (hab : a <= b) (h
c : 0 <= c) : a / c <= b / c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Int.add_one_le_iff`：∀ {a b : ℤ}, a + 1 ≤ b ↔ a < b
· 使用定理 `abs_pos`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α] [
AddLeftMono α] {a : α}, 0 < |a| ↔ a ≠ 0
· 使用定理 `sub_ne_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b ≠ 0 ↔
 a ≠ b
· 使用引理 `eq_div_iff`：eq_div_iff (hb : b != 0) : c = a / b ↔ c * b = a
（共 34 条，此处仅展示前 30 条）
-/
theorem ne_cast_int (h : LiouvilleWith p x) (hp : 1 < p) (m : ℤ) : x ≠ m := by
  rintro rfl; rename' m => M
  rcases ((eventually_gt_atTop 0).and_frequently (h.frequently_lt_rpow_neg hp)).exists with
    ⟨n : ℕ, hn : 0 < n, m : ℤ, hne : (M : ℝ) ≠ m / n, hlt : |(M - m / n : ℝ)| < n ^ (-1 : ℝ)⟩
  refine hlt.not_ge ?_
  have hn' : (0 : ℝ) < n := by simpa
  rw [rpow_neg_one, ← one_div, sub_div' hn'.ne', abs_div, Nat.abs_cast]
  gcongr
  norm_cast
  rw [← zero_add (1 : ℤ), Int.add_one_le_iff, abs_pos, sub_ne_zero]
  rw [Ne, eq_div_iff hn'.ne'] at hne
  exact mod_cast hne

/-- A number satisfying the Liouville condition with exponent `p > 1` is an irrational number. -/
/-
**LiouvilleWith.irrational** 是 Mathlib 中的一个定理，位于命名空间 `LiouvilleWith`。
形式化陈述：∀ {p x : ℝ}, LiouvilleWith p x → 1 < p → Irrational x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `LiouvilleWith.ne_cast_int`：ne_cast_int (h : LiouvilleWith p x) (hp : 1 <
 p) (m : Int) : x != m
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.cast_zero`：cast_zero : ((0 : Rat) : α) = 0
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LiouvilleWith.mul_rat`：mul_rat (h : LiouvilleWith p x) (hr : r != 0) : L
iouvilleWith p (x * r)
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
· 使用定理 `Rat.cast_inv`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p :
 ℚ), ↑p⁻¹ = (↑p)⁻¹
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Rat.cast_ne_zero`：cast_ne_zero : (p : α) != 0 ↔ p != 0
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1

--- 原说明 ---
A number satisfying the Liouville condition with exponent `p > 1` is an irration
al number.
-/
protected theorem irrational (h : LiouvilleWith p x) (hp : 1 < p) : Irrational x := by
  rintro ⟨r, rfl⟩
  rcases eq_or_ne r 0 with (rfl | h0)
  · refine h.ne_cast_int hp 0 ?_; rw [Rat.cast_zero, Int.cast_zero]
  · refine (h.mul_rat (inv_ne_zero h0)).ne_cast_int hp 1 ?_
    rw [Rat.cast_inv, mul_inv_cancel₀]
    exacts [Int.cast_one.symm, Rat.cast_ne_zero.mpr h0]

end LiouvilleWith

namespace Liouville

variable {x : ℝ}

/-- If `x` is a Liouville number, then for any `n`, for infinitely many denominators `b` there
exists a numerator `a` such that `x ≠ a / b` and `|x - a / b| < 1 / b ^ n`. -/
/-
**Liouville.frequently_exists_num** 是 Mathlib 中的一个定理，位于命名空间 `Liouville`。
形式化陈述：frequently_exists_num (hx : Liouville x) (n : Nat) : existsᶠ b : Nat in at
Top, exists a : Int, x != a / b ∧ |x - a / b| < 1 / (b : Real) ^ n
参数：hx : Liouville x；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.one_lt_cast`：one_lt_cast : 1 < (n : α) ↔ 1 < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `tendsto_inv_atTop_zero`：tendsto_inv_atTop_zero : Tendsto (fun r : 𝕜 => r
⁻¹) atTop (𝓝 0)
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `tendsto_pow_atTop_atTop_of_one_lt`：tendsto_pow_atTop_atTop_of_one_lt [Se
miring α] [LinearOrder α] [IsStrictOrderedRing α] [ExistsAddOfLE α] [Archimedean
 α] {r : α} (h : 1 < r)…
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `Irrational.eventually_forall_le_dist_cast_div`：eventually_forall_le_dist
_cast_div (hx : Irrational x) (n : Nat) : forallᶠ ε : Real in 𝓝 0, forall m : In
t, ε <= dist x (m / n)
· 使用定理 `Liouville.irrational`：∀ {x : ℝ}, Liouville x → Irrational x
· 使用定理 `Set.Finite.eventually_all`：∀ {α : Type u} {ι : Type u_2} {I : Set ι},   
I.Finite → ∀ {l : Filter α} {p : ι → α → Prop}, (∀ᶠ (x : α) in l, ∀ i ∈ I, p i x
) ↔ ∀ i ∈ I, ∀ᶠ…
· 使用定理 `Set.finite_lt_nat`：finite_lt_nat (n : Nat) : Set.Finite { i | i < n }
· 使用定理 `Filter.eventually_imp_distrib_left`：eventually_imp_distrib_left {f : Fil
ter α} {p : Prop} {q : α -> Prop} : (forallᶠ x in f, p -> q x) ↔ p -> forallᶠ x 
in f, q x
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
（共 61 条，此处仅展示前 30 条）

--- 原说明 ---
If `x` is a Liouville number, then for any `n`, for infinitely many denominators
 `b` there
exists a numerator `a` such that `x ≠ a / b` and `|x - a / b| < 1 / b ^ n`.
-/
theorem frequently_exists_num (hx : Liouville x) (n : ℕ) :
    ∃ᶠ b : ℕ in atTop, ∃ a : ℤ, x ≠ a / b ∧ |x - a / b| < 1 / (b : ℝ) ^ n := by
  by_contra! H
  simp only [eventually_atTop] at H
  rcases H with ⟨N, hN⟩
  have : ∀ b > (1 : ℕ), ∀ᶠ m : ℕ in atTop, ∀ a : ℤ, 1 / (b : ℝ) ^ m ≤ |x - a / b| := by
    intro b hb
    replace hb : (1 : ℝ) < b := Nat.one_lt_cast.2 hb
    have H : Tendsto (fun m => 1 / (b : ℝ) ^ m : ℕ → ℝ) atTop (𝓝 0) := by
      simp only [one_div]
      exact tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt hb)
    refine (H.eventually (hx.irrational.eventually_forall_le_dist_cast_div b)).mono ?_
    exact fun m hm a => hm a
  have : ∀ᶠ m : ℕ in atTop, ∀ b < N, 1 < b → ∀ a : ℤ, 1 / (b : ℝ) ^ m ≤ |x - a / b| :=
    (finite_lt_nat N).eventually_all.2 fun b _hb => eventually_imp_distrib_left.2 (this b)
  rcases (this.and (eventually_ge_atTop n)).exists with ⟨m, hm, hnm⟩
  rcases hx m with ⟨a, b, hb, hne, hlt⟩
  lift b to ℕ using zero_le_one.trans hb.le; norm_cast at hb; push_cast at hne hlt
  rcases le_or_gt N b with h | h
  · refine (hN b h a hne).not_gt (hlt.trans_le ?_)
    gcongr
    exact_mod_cast hb.le
  · exact (hm b h hb _).not_gt hlt

/-- A Liouville number is a Liouville number with any real exponent. -/
/-
**Liouville.liouvilleWith** 是 Mathlib 中的一个定理，位于命名空间 `Liouville`。
形式化陈述：∀ {x : ℝ}, Liouville x → ∀ (p : ℝ), LiouvilleWith p x
参数：p : ℝ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Frequently.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∃ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.and_frequently`：∀ {α : Type u} {p q : α → Prop} {f : F
ilter α},   (∀ᶠ (x : α) in f, p x) → (∃ᶠ (x : α) in f, q x) → ∃ᶠ (x : α) in f, p
 x ∧ q x
· 使用定理 `Filter.eventually_gt_atTop`：eventually_gt_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, a < x
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `Liouville.frequently_exists_num`：frequently_exists_num (hx : Liouville x
) (n : Nat) : existsᶠ b : Nat in atTop, exists a : Int, x != a / b ∧ |x - a / b|
 < 1 / (b : Real) ^ n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_natCast`：rpow_natCast (x : Real) (n : Nat) : x ^ (n : Real) = 
x ^ n
· 使用定理 `LiouvilleWith.mono`：mono (h : LiouvilleWith p x) (hle : q <= p) : Liouvi
lleWith q x
· 使用定理 `Nat.le_ceil`：le_ceil (a : R) : a <= ⌈a⌉₊

--- 原说明 ---
A Liouville number is a Liouville number with any real exponent.
-/
protected theorem liouvilleWith (hx : Liouville x) (p : ℝ) : LiouvilleWith p x := by
  suffices LiouvilleWith ⌈p⌉₊ x from this.mono (Nat.le_ceil p)
  refine ⟨1, ((eventually_gt_atTop 1).and_frequently (hx.frequently_exists_num ⌈p⌉₊)).mono ?_⟩
  rintro b ⟨_hb, a, hne, hlt⟩
  refine ⟨a, hne, ?_⟩
  rwa [rpow_natCast]

end Liouville

/-- A number satisfies the Liouville condition with any exponent if and only if it is a Liouville
number. -/
/-
**forall_liouvilleWith_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：forall_liouvilleWith_iff {x : Real} : (forall p, LiouvilleWith p x) ↔ Liou
ville x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Frequently.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `Filter.Eventually.and_frequently`：∀ {α : Type u} {p q : α → Prop} {f : F
ilter α},   (∀ᶠ (x : α) in f, p x) → (∃ᶠ (x : α) in f, q x) → ∃ᶠ (x : α) in f, p
 x ∧ q x
· 使用定理 `Filter.eventually_gt_atTop`：eventually_gt_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, a < x
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `LiouvilleWith.frequently_lt_rpow_neg`：frequently_lt_rpow_neg (h : Liouvi
lleWith p x) (hlt : q < p) : existsᶠ n : Nat in atTop, exists m : Int, x != m / 
n ∧ |x - m / n| < n ^ (-q)
· 使用引理 `lt_add_one`：lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLE
OneClass α] [NeZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Real.rpow_neg`：rpow_neg {x : Real} (hx : 0 <= x) (y : Real) : x ^ (-y) =
 (x ^ y)⁻¹
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Real.rpow_natCast`：rpow_natCast (x : Real) (n : Nat) : x ^ (n : Real) = 
x ^ n
· 使用定理 `Liouville.liouvilleWith`：∀ {x : ℝ}, Liouville x → ∀ (p : ℝ), LiouvilleWi
th p x

--- 原说明 ---
A number satisfies the Liouville condition with any exponent if and only if it i
s a Liouville
number.
-/
theorem forall_liouvilleWith_iff {x : ℝ} : (∀ p, LiouvilleWith p x) ↔ Liouville x := by
  refine ⟨fun H n => ?_, Liouville.liouvilleWith⟩
  rcases ((eventually_gt_atTop 1).and_frequently
    ((H (n + 1)).frequently_lt_rpow_neg (lt_add_one (n : ℝ)))).exists
    with ⟨b, hb, a, hne, hlt⟩
  exact ⟨a, b, mod_cast hb, hne, by simpa [rpow_neg] using hlt⟩
