/-
Copyright (c) 2020 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
module

public import Mathlib.Algebra.ContinuedFractions.Determinant
public import Mathlib.Algebra.ContinuedFractions.Computation.CorrectnessTerminating
public import Mathlib.Algebra.Order.Ring.Basic
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Tactic.Monotonicity
public import Mathlib.Tactic.GCongr

/-!
# Approximations for Continued Fraction Computations (`GenContFract.of`)

## Summary

This file contains useful approximations for the values involved in the continued fractions
computation `GenContFract.of`. In particular, we show that the generalized continued fraction given
by `GenContFract.of` in fact is a (regular) continued fraction.

Moreover, we derive some upper bounds for the error term when computing a continued fraction up a
given position, i.e. bounds for the term
`|v - (GenContFract.of v).convs n|`. The derived bounds will show us that the error term indeed gets
smaller. As a corollary, we will be able to show that `(GenContFract.of v).convs` converges to `v`
in `Algebra.ContinuedFractions.Computation.ApproximationCorollaries`.

## Main Theorems

- `GenContFract.of_partNum_eq_one`: shows that all partial numerators `aᵢ` are
  equal to one.
- `GenContFract.exists_int_eq_of_partDen`: shows that all partial denominators
  `bᵢ` correspond to an integer.
- `GenContFract.of_one_le_get?_partDen`: shows that `1 ≤ bᵢ`.
- `ContFract.of` returns the regular continued fraction of a value.
- `GenContFract.succ_nth_fib_le_of_nthDen`: shows that the `n`th denominator
  `Bₙ` is greater than or equal to the `n + 1`th fibonacci number `Nat.fib (n + 1)`.
- `GenContFract.le_of_succ_get?_den`: shows that `bₙ * Bₙ ≤ Bₙ₊₁`, where `bₙ` is
  the `n`th partial denominator of the continued fraction.
- `GenContFract.abs_sub_convs_le`: shows that
  `|v - Aₙ / Bₙ| ≤ 1 / (Bₙ * Bₙ₊₁)`, where `Aₙ` is the `n`th partial numerator.

## References

- [*Hardy, GH and Wright, EM and Heath-Brown, Roger and Silverman, Joseph*][hardy2008introduction]

-/

@[expose] public section

open GenContFract

open GenContFract (of)

open Int

variable {K : Type*} {v : K} {n : ℕ} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

namespace GenContFract

namespace IntFractPair

/-!
We begin with some lemmas about the stream of `IntFractPair`s, which presumably are not
of great interest for the end user.
-/


/-- Shows that the fractional parts of the stream are in `[0,1)`. -/
/-
**GenContFract.IntFractPair.nth_stream_fr_nonneg_lt_one** 是 Mathlib 中的一个定理，位于命名空
间 `GenContFract.IntFractPair`。
形式化陈述：nth_stream_fr_nonneg_lt_one {ifp_n : IntFractPair K} (nth_stream_eq : IntF
ractPair.stream v n = some ifp_n) : 0 <= ifp_n.fr ∧ ifp_n.fr < 1
参数：nth_stream_eq : IntFractPair.stream v n = some ifp_n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.fract_nonneg`：fract_nonneg (a : R) : 0 <= fract a
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Int.fract_lt_one`：fract_lt_one (a : R) : fract a < 1
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `GenContFract.IntFractPair.succ_nth_stream_eq_some_iff`：succ_nth_stream_e
q_some_iff {ifp_succ_n : IntFractPair K} : IntFractPair.stream v (n + 1) = some 
ifp_succ_n ↔ exists ifp_n : IntFractPair K,…

--- 原说明 ---
Shows that the fractional parts of the stream are in `[0,1)`.
-/
theorem nth_stream_fr_nonneg_lt_one {ifp_n : IntFractPair K}
    (nth_stream_eq : IntFractPair.stream v n = some ifp_n) : 0 ≤ ifp_n.fr ∧ ifp_n.fr < 1 := by
  cases n with
  | zero =>
    obtain rfl : IntFractPair.of v = ifp_n := by injection nth_stream_eq
    exact ⟨fract_nonneg _, fract_lt_one _⟩
  | succ =>
    rcases succ_nth_stream_eq_some_iff.1 nth_stream_eq with ⟨_, _, _, rfl⟩
    exact ⟨fract_nonneg _, fract_lt_one _⟩

/-- Shows that the fractional parts of the stream are nonnegative. -/
/-
**GenContFract.IntFractPair.nth_stream_fr_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `GenC
ontFract.IntFractPair`。
形式化陈述：nth_stream_fr_nonneg {ifp_n : IntFractPair K} (nth_stream_eq : IntFractPai
r.stream v n = some ifp_n) : 0 <= ifp_n.fr
参数：nth_stream_eq : IntFractPair.stream v n = some ifp_n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `GenContFract.IntFractPair.nth_stream_fr_nonneg_lt_one`：nth_stream_fr_non
neg_lt_one {ifp_n : IntFractPair K} (nth_stream_eq : IntFractPair.stream v n = s
ome ifp_n) : 0 <= ifp_n.fr ∧ ifp_n.fr < 1

--- 原说明 ---
Shows that the fractional parts of the stream are nonnegative.
-/
theorem nth_stream_fr_nonneg {ifp_n : IntFractPair K}
    (nth_stream_eq : IntFractPair.stream v n = some ifp_n) : 0 ≤ ifp_n.fr :=
  (nth_stream_fr_nonneg_lt_one nth_stream_eq).left

/-- Shows that the fractional parts of the stream are smaller than one. -/
/-
**GenContFract.IntFractPair.nth_stream_fr_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `GenC
ontFract.IntFractPair`。
形式化陈述：nth_stream_fr_lt_one {ifp_n : IntFractPair K} (nth_stream_eq : IntFractPai
r.stream v n = some ifp_n) : ifp_n.fr < 1
参数：nth_stream_eq : IntFractPair.stream v n = some ifp_n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `GenContFract.IntFractPair.nth_stream_fr_nonneg_lt_one`：nth_stream_fr_non
neg_lt_one {ifp_n : IntFractPair K} (nth_stream_eq : IntFractPair.stream v n = s
ome ifp_n) : 0 <= ifp_n.fr ∧ ifp_n.fr < 1

--- 原说明 ---
Shows that the fractional parts of the stream are smaller than one.
-/
theorem nth_stream_fr_lt_one {ifp_n : IntFractPair K}
    (nth_stream_eq : IntFractPair.stream v n = some ifp_n) : ifp_n.fr < 1 :=
  (nth_stream_fr_nonneg_lt_one nth_stream_eq).right

/-- Shows that the integer parts of the stream are at least one. -/
/-
**GenContFract.IntFractPair.one_le_succ_nth_stream_b** 是 Mathlib 中的一个定理，位于命名空间 `
GenContFract.IntFractPair`。
形式化陈述：one_le_succ_nth_stream_b {ifp_succ_n : IntFractPair K} (succ_nth_stream_eq
 : IntFractPair.stream v (n + 1) = some ifp_succ_n) : 1 <= ifp_succ_n.b
参数：succ_nth_stream_eq : IntFractPair.stream v (n + 1) = some ifp_succ_n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `GenContFract.IntFractPair.succ_nth_stream_eq_some_iff`：succ_nth_stream_e
q_some_iff {ifp_succ_n : IntFractPair K} : IntFractPair.stream v (n + 1) = some 
ifp_succ_n ↔ exists ifp_n : IntFractPair K,…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GenContFract.IntFractPair.of.eq_1`：∀ {K : Type u_1} [inst : DivisionRing
 K] [inst_1 : LinearOrder K] [inst_2 : FloorRing K] (v : K),   GenContFract.IntF
ractPair.of v = { b := …
· 使用定理 `Int.le_floor`：le_floor : z <= ⌊a⌋ ↔ (z : α) <= a
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用引理 `one_le_inv₀`：one_le_inv₀ (ha : 0 < a) : 1 <= a⁻¹ ↔ a <= 1
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `LE.le.lt_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `GenContFract.IntFractPair.nth_stream_fr_nonneg`：nth_stream_fr_nonneg {if
p_n : IntFractPair K} (nth_stream_eq : IntFractPair.stream v n = some ifp_n) : 0
 <= ifp_n.fr
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `GenContFract.IntFractPair.nth_stream_fr_lt_one`：nth_stream_fr_lt_one {if
p_n : IntFractPair K} (nth_stream_eq : IntFractPair.stream v n = some ifp_n) : i
fp_n.fr < 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Shows that the integer parts of the stream are at least one.
-/
theorem one_le_succ_nth_stream_b {ifp_succ_n : IntFractPair K}
    (succ_nth_stream_eq : IntFractPair.stream v (n + 1) = some ifp_succ_n) : 1 ≤ ifp_succ_n.b := by
  obtain ⟨ifp_n, nth_stream_eq, stream_nth_fr_ne_zero, ⟨-⟩⟩ :
      ∃ ifp_n, IntFractPair.stream v n = some ifp_n ∧ ifp_n.fr ≠ 0
        ∧ IntFractPair.of ifp_n.fr⁻¹ = ifp_succ_n :=
    succ_nth_stream_eq_some_iff.1 succ_nth_stream_eq
  rw [IntFractPair.of, le_floor, cast_one, one_le_inv₀
    ((nth_stream_fr_nonneg nth_stream_eq).lt_of_ne' stream_nth_fr_ne_zero)]
  exact (nth_stream_fr_lt_one nth_stream_eq).le

omit [IsStrictOrderedRing K] in
/--
Shows that the `n + 1`th integer part `bₙ₊₁` of the stream is smaller or equal than the inverse of
the `n`th fractional part `frₙ` of the stream.
This result is straight-forward as `bₙ₊₁` is defined as the floor of `1 / frₙ`.
-/
/-
**GenContFract.IntFractPair.succ_nth_stream_b_le_nth_stream_fr_inv** 是 Mathlib 中
的一个定理，位于命名空间 `GenContFract.IntFractPair`。
形式化陈述：succ_nth_stream_b_le_nth_stream_fr_inv {ifp_n ifp_succ_n : IntFractPair K}
 (nth_stream_eq : IntFractPair.stream v n = some ifp_n) (succ_nth_stream_eq : In
tFractPair.stream v (n + 1) = some ifp_succ_n) : (ifp_succ_n.b : K) <= ifp_n.fr⁻
¹
参数：nth_stream_eq : IntFractPair.stream v n = some ifp_n；succ_nth_stream_eq : Int
FractPair.stream v (n + 1) = some ifp_succ_n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.floor_le`：floor_le (a : α) : (⌊a⌋ : α) <= a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Option.bind_congr'`：bind_congr' {f g : α -> Option β} {x y : Option α} (
hx : x = y) (hf : forall a in y, f a = g a) : x.bind f = y.bind g
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Shows that the `n + 1`th integer part `bₙ₊₁` of the stream is smaller or equal t
han the inverse of
the `n`th fractional part `frₙ` of the stream.
This result is straight-forward as `bₙ₊₁` is defined as the floor of `1 / frₙ`.
-/
theorem succ_nth_stream_b_le_nth_stream_fr_inv {ifp_n ifp_succ_n : IntFractPair K}
    (nth_stream_eq : IntFractPair.stream v n = some ifp_n)
    (succ_nth_stream_eq : IntFractPair.stream v (n + 1) = some ifp_succ_n) :
    (ifp_succ_n.b : K) ≤ ifp_n.fr⁻¹ := by
  suffices (⌊ifp_n.fr⁻¹⌋ : K) ≤ ifp_n.fr⁻¹ by
    obtain ⟨_, ifp_n_fr⟩ := ifp_n
    have : ifp_n_fr ≠ 0 := by
      intro h
      simp [h, IntFractPair.stream, nth_stream_eq] at succ_nth_stream_eq
    have : IntFractPair.of ifp_n_fr⁻¹ = ifp_succ_n := by
      simpa [this, IntFractPair.stream, nth_stream_eq, Option.coe_def] using succ_nth_stream_eq
    rwa [← this]
  exact floor_le ifp_n.fr⁻¹

end IntFractPair

/-!
Next we translate above results about the stream of `IntFractPair`s to the computed continued
fraction `GenContFract.of`.
-/


/-- Shows that the integer parts of the continued fraction are at least one. -/
/-
**GenContFract.of_one_le_get** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract`。
形式化陈述：of_one_le_get?_partDen {b : K} (nth_partDen_eq : (of v).partDens.get? n = 
some b) : 1 <= b
参数：nth_partDen_eq : (of v).partDens.get? n = some b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Shows that the integer parts of the continued fraction are at least one.
-/
theorem of_one_le_get?_partDen {b : K}
    (nth_partDen_eq : (of v).partDens.get? n = some b) : 1 ≤ b := by
  obtain ⟨gp_n, nth_s_eq, ⟨-⟩⟩ : ∃ gp_n, (of v).s.get? n = some gp_n ∧ gp_n.b = b :=
    exists_s_b_of_partDen nth_partDen_eq
  obtain ⟨ifp_n, succ_nth_stream_eq, ifp_n_b_eq_gp_n_b⟩ :
      ∃ ifp, IntFractPair.stream v (n + 1) = some ifp ∧ (ifp.b : K) = gp_n.b :=
    IntFractPair.exists_succ_get?_stream_of_gcf_of_get?_eq_some nth_s_eq
  rw [← ifp_n_b_eq_gp_n_b]
  exact mod_cast IntFractPair.one_le_succ_nth_stream_b succ_nth_stream_eq

omit [IsStrictOrderedRing K] in
/--
Shows that the partial numerators `aᵢ` of the continued fraction are equal to one and the partial
denominators `bᵢ` correspond to integers.
-/
/-
**GenContFract.of_partNum_eq_one_and_exists_int_partDen_eq** 是 Mathlib 中的一个定理，位于
命名空间 `GenContFract`。
形式化陈述：of_partNum_eq_one_and_exists_int_partDen_eq {gp : GenContFract.Pair K} (nt
h_s_eq : (of v).s.get? n = some gp) : gp.a = 1 ∧ exists z : Int, gp.b = (z : K)
参数：nth_s_eq : (of v).s.get? n = some gp。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GenContFract.IntFractPair.exists_succ_get?_stream_of_gcf_of_get?_eq_some
`：∀ {K : Type u_1} [inst : DivisionRing K] [inst_1 : LinearOrder K] [inst_2 : Fl
oorRing K] {v : K} {n : ℕ}   {gp_n : GenContFract.Pair K},   (…
· 使用定理 `GenContFract.get?_of_eq_some_of_succ_get?_intFractPair_stream`：∀ {K : Ty
pe u_1} [inst : DivisionRing K] [inst_1 : LinearOrder K] [inst_2 : FloorRing K] 
{v : K} {n : ℕ}   {ifp_succ_n : GenContFract.IntFra…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p

--- 原说明 ---
Shows that the partial numerators `aᵢ` of the continued fraction are equal to on
e and the partial
denominators `bᵢ` correspond to integers.
-/
theorem of_partNum_eq_one_and_exists_int_partDen_eq {gp : GenContFract.Pair K}
    (nth_s_eq : (of v).s.get? n = some gp) : gp.a = 1 ∧ ∃ z : ℤ, gp.b = (z : K) := by
  obtain ⟨ifp, stream_succ_nth_eq, -⟩ : ∃ ifp, IntFractPair.stream v (n + 1) = some ifp ∧ _ :=
    IntFractPair.exists_succ_get?_stream_of_gcf_of_get?_eq_some nth_s_eq
  have : gp = ⟨1, ifp.b⟩ := by
    have : (of v).s.get? n = some ⟨1, ifp.b⟩ :=
      get?_of_eq_some_of_succ_get?_intFractPair_stream stream_succ_nth_eq
    have : some gp = some ⟨1, ifp.b⟩ := by rwa [nth_s_eq] at this
    injection this
  simp [this]

omit [IsStrictOrderedRing K] in
/-- Shows that the partial numerators `aᵢ` are equal to one. -/
/-
**GenContFract.of_partNum_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract`。
形式化陈述：of_partNum_eq_one {a : K} (nth_partNum_eq : (of v).partNums.get? n = some 
a) : a = 1
参数：nth_partNum_eq : (of v).partNums.get? n = some a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GenContFract.exists_s_a_of_partNum`：exists_s_a_of_partNum {a : α} (nth_p
artNum_eq : g.partNums.get? n = some a) : exists gp, g.s.get? n = some gp ∧ gp.a
 = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `GenContFract.of_partNum_eq_one_and_exists_int_partDen_eq`：of_partNum_eq_
one_and_exists_int_partDen_eq {gp : GenContFract.Pair K} (nth_s_eq : (of v).s.ge
t? n = some gp) : gp.a = 1 ∧ exists z : Int, g…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
Shows that the partial numerators `aᵢ` are equal to one.
-/
theorem of_partNum_eq_one {a : K} (nth_partNum_eq : (of v).partNums.get? n = some a) :
    a = 1 := by
  obtain ⟨gp, nth_s_eq, gp_a_eq_a_n⟩ : ∃ gp, (of v).s.get? n = some gp ∧ gp.a = a :=
    exists_s_a_of_partNum nth_partNum_eq
  have : gp.a = 1 := (of_partNum_eq_one_and_exists_int_partDen_eq nth_s_eq).left
  rwa [gp_a_eq_a_n] at this

omit [IsStrictOrderedRing K] in
/-- Shows that the partial denominators `bᵢ` correspond to an integer. -/
/-
**GenContFract.exists_int_eq_of_partDen** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract`
。
形式化陈述：exists_int_eq_of_partDen {b : K} (nth_partDen_eq : (of v).partDens.get? n 
= some b) : exists z : Int, b = (z : K)
参数：nth_partDen_eq : (of v).partDens.get? n = some b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GenContFract.exists_s_b_of_partDen`：exists_s_b_of_partDen {b : α} (nth_p
artDen_eq : g.partDens.get? n = some b) : exists gp, g.s.get? n = some gp ∧ gp.b
 = b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `GenContFract.of_partNum_eq_one_and_exists_int_partDen_eq`：of_partNum_eq_
one_and_exists_int_partDen_eq {gp : GenContFract.Pair K} (nth_s_eq : (of v).s.ge
t? n = some gp) : gp.a = 1 ∧ exists z : Int, g…

--- 原说明 ---
Shows that the partial denominators `bᵢ` correspond to an integer.
-/
theorem exists_int_eq_of_partDen {b : K}
    (nth_partDen_eq : (of v).partDens.get? n = some b) : ∃ z : ℤ, b = (z : K) := by
  obtain ⟨_, nth_s_eq, rfl⟩ : ∃ gp, (of v).s.get? n = some gp ∧ gp.b = b :=
    exists_s_b_of_partDen nth_partDen_eq
  exact (of_partNum_eq_one_and_exists_int_partDen_eq nth_s_eq).right

end GenContFract

variable (v)

omit [IsStrictOrderedRing K] in
/-
**GenContFract.of_isSimpContFract** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：GenContFract.of_isSimpContFract : (of v).IsSimpContFract
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GenContFract.of_partNum_eq_one`：of_partNum_eq_one {a : K} (nth_partNum_e
q : (of v).partNums.get? n = some a) : a = 1
-/
theorem GenContFract.of_isSimpContFract :
    (of v).IsSimpContFract := fun _ _ nth_partNum_eq =>
  of_partNum_eq_one nth_partNum_eq

/-- Creates the simple continued fraction of a value. -/
/-
**SimpContFract.of** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：SimpContFract.of : SimpContFract K
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `GenContFract.of_isSimpContFract`：GenContFract.of_isSimpContFract : (of v
).IsSimpContFract

--- 原说明 ---
Creates the simple continued fraction of a value.
-/
def SimpContFract.of : SimpContFract K :=
  ⟨GenContFract.of v, GenContFract.of_isSimpContFract v⟩
/-
**SimpContFract.of_isContFract** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SimpContFract.of_isContFract : (SimpContFract.of v).IsContFract
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instZeroLEOneClass`：∀ {α : Type u_2} [inst : Semiring α] [
inst_1 : PartialOrder α] [FloorSemiring α], ZeroLEOneClass α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `GenContFract.of_one_le_get?_partDen`：∀ {K : Type u_1} {v : K} {n : ℕ} [i
nst : Field K] [inst_1 : LinearOrder K] [IsStrictOrderedRing K]   [inst_3 : Floo
rRing K] {b : K}, (GenCon…
-/
theorem SimpContFract.of_isContFract :
    (SimpContFract.of v).IsContFract := fun _ _ nth_partDen_eq =>
  lt_of_lt_of_le zero_lt_one (of_one_le_get?_partDen nth_partDen_eq)

/-- Creates the continued fraction of a value. -/
/-
**ContFract.of** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ContFract.of : ContFract K
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SimpContFract.of_isContFract`：SimpContFract.of_isContFract : (SimpContFr
act.of v).IsContFract

--- 原说明 ---
Creates the continued fraction of a value.
-/
def ContFract.of : ContFract K :=
  ⟨SimpContFract.of v, SimpContFract.of_isContFract v⟩

variable {v}

namespace GenContFract

/-!
One of our next goals is to show that `bₙ * Bₙ ≤ Bₙ₊₁`. For this, we first show that the partial
denominators `Bₙ` are bounded from below by the fibonacci sequence `Nat.fib`. This then implies that
`0 ≤ Bₙ` and hence `Bₙ₊₂ = bₙ₊₁ * Bₙ₊₁ + Bₙ ≥ bₙ₊₁ * Bₙ₊₁ + 0 = bₙ₊₁ * Bₙ₊₁`.
-/


-- open `Nat` as we will make use of fibonacci numbers.
open Nat

/-
**GenContFract.fib_le_of_contsAux_b** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract`。
形式化陈述：fib_le_of_contsAux_b : n <= 1 ∨ ¬(of v).TerminatedAt (n - 2) -> (fib n : K
) <= ((of v).contsAux n).b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.strong_induction_on`：∀ {p : ℕ → Prop} (n : ℕ), (∀ (n : ℕ), (∀ m < n,
 p m) → p n) → p n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Option.ne_none_iff_exists'`：∀ {α : Type u_1} {o : Option α}, o ≠ none ↔ 
∃ x, o = some x
· 使用定理 `Nat.add_assoc`：∀ (n m k : ℕ), n + m + k = n + (m + k)
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `GenContFract.terminated_stable`：terminated_stable (n_le_m : n <= m) (ter
minatedAt_n : g.TerminatedAt n) : g.TerminatedAt m
· 使用定理 `Nat.sub_le`：∀ (n m : ℕ), n - m ≤ n
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用定理 `Nat.lt_add_one`：∀ (n : ℕ), n < n + 1
· 使用定理 `GenContFract.of_one_le_get?_partDen`：∀ {K : Type u_1} {v : K} {n : ℕ} [i
nst : Field K] [inst_1 : LinearOrder K] [IsStrictOrderedRing K]   [inst_3 : Floo
rRing K] {b : K}, (GenCon…
· 使用定理 `GenContFract.partDen_eq_s_b`：partDen_eq_s_b {gp : Pair α} (s_nth_eq : g.
s.get? n = some gp) : g.partDens.get? n = some gp.b
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `FloorSemiring.instZeroLEOneClass`：∀ {α : Type u_2} [inst : Semiring α] [
inst_1 : PartialOrder α] [FloorSemiring α], ZeroLEOneClass α
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
（共 43 条，此处仅展示前 30 条）
-/
theorem fib_le_of_contsAux_b :
    n ≤ 1 ∨ ¬(of v).TerminatedAt (n - 2) → (fib n : K) ≤ ((of v).contsAux n).b :=
  Nat.strong_induction_on n
    (by
      intro n IH hyp
      rcases n with (_ | _ | n)
      · simp [contsAux] -- case n = 0
      · simp -- case n = 1
      · let g := of v -- case 2 ≤ n
        have : ¬n + 2 ≤ 1 := by lia
        have not_terminatedAt_n : ¬g.TerminatedAt n := Or.resolve_left hyp this
        obtain ⟨gp, s_ppred_nth_eq⟩ : ∃ gp, g.s.get? n = some gp :=
          Option.ne_none_iff_exists'.mp not_terminatedAt_n
        set pconts := g.contsAux (n + 1) with pconts_eq
        set ppconts := g.contsAux n with ppconts_eq
        -- use the recurrence of `contsAux`
        simp only [Nat.add_assoc, Nat.reduceAdd]
        suffices (fib n : K) + fib (n + 1) ≤ gp.a * ppconts.b + gp.b * pconts.b by
          simpa [g, fib_add_two, add_comm, contsAux_recurrence s_ppred_nth_eq ppconts_eq pconts_eq]
        -- make use of the fact that `gp.a = 1`
        suffices (fib n : K) + fib (n + 1) ≤ ppconts.b + gp.b * pconts.b by
          simpa [of_partNum_eq_one <| partNum_eq_s_a s_ppred_nth_eq]
        have not_terminatedAt_pred_n : ¬g.TerminatedAt (n - 1) :=
          mt (terminated_stable <| Nat.sub_le n 1) not_terminatedAt_n
        have not_terminatedAt_ppred_n : ¬TerminatedAt g (n - 2) :=
          mt (terminated_stable <| Nat.sub_le n 2) not_terminatedAt_n
        -- use the IH to get the inequalities for `pconts` and `ppconts`
        have ppred_nth_fib_le_ppconts_B : (fib n : K) ≤ ppconts.b :=
          IH n (lt_trans (Nat.lt_add_one n) <| Nat.lt_add_one <| n + 1)
            (Or.inr not_terminatedAt_ppred_n)
        suffices (fib (n + 1) : K) ≤ gp.b * pconts.b by gcongr
        -- finally use the fact that `1 ≤ gp.b` to solve the goal
        suffices 1 * (fib (n + 1) : K) ≤ gp.b * pconts.b by rwa [one_mul] at this
        have one_le_gp_b : (1 : K) ≤ gp.b :=
          of_one_le_get?_partDen (partDen_eq_s_b s_ppred_nth_eq)
        gcongr
        grind)

/-- Shows that the `n`th denominator is greater than or equal to the `n + 1`th fibonacci number,
that is `Nat.fib (n + 1) ≤ Bₙ`. -/
/-
**GenContFract.succ_nth_fib_le_of_nth_den** 是 Mathlib 中的一个定理，位于命名空间 `GenContFrac
t`。
形式化陈述：succ_nth_fib_le_of_nth_den (hyp : n = 0 ∨ ¬(of v).TerminatedAt (n - 1)) : 
(fib (n + 1) : K) <= (of v).dens n
参数：hyp : n = 0 ∨ ¬(of v).TerminatedAt (n - 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GenContFract.den_eq_conts_b`：den_eq_conts_b : g.dens n = (g.conts n).b
· 使用定理 `GenContFract.nth_cont_eq_succ_nth_contAux`：nth_cont_eq_succ_nth_contAux 
: g.conts n = g.contsAux (n + 1)
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
· 使用定理 `GenContFract.fib_le_of_contsAux_b`：fib_le_of_contsAux_b : n <= 1 ∨ ¬(of 
v).TerminatedAt (n - 2) -> (fib n : K) <= ((of v).contsAux n).b

--- 原说明 ---
Shows that the `n`th denominator is greater than or equal to the `n + 1`th fibon
acci number,
that is `Nat.fib (n + 1) ≤ Bₙ`.
-/
theorem succ_nth_fib_le_of_nth_den (hyp : n = 0 ∨ ¬(of v).TerminatedAt (n - 1)) :
    (fib (n + 1) : K) ≤ (of v).dens n := by
  rw [den_eq_conts_b, nth_cont_eq_succ_nth_contAux]
  have : n + 1 ≤ 1 ∨ ¬(of v).TerminatedAt (n - 1) := by
    cases n with
    | zero => exact Or.inl <| le_refl 1
    | succ n => exact Or.inr (Or.resolve_left hyp n.succ_ne_zero)
  exact fib_le_of_contsAux_b this

/-! As a simple consequence, we can now derive that all denominators are nonnegative. -/


/-
**GenContFract.zero_le_of_contsAux_b** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract`。
形式化陈述：zero_le_of_contsAux_b : 0 <= ((of v).contsAux n).b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Decidable.em`：∀ (p : Prop) [Decidable p], p ∨ ¬p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `FloorSemiring.instZeroLEOneClass`：∀ {α : Type u_2} [inst : Semiring α] [
inst_1 : PartialOrder α] [FloorSemiring α], ZeroLEOneClass α
· 使用定理 `GenContFract.contsAux_stable_step_of_terminated`：contsAux_stable_step_of
_terminated (terminatedAt_n : g.TerminatedAt n) : g.contsAux (n + 2) = g.contsAu
x (n + 1)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `GenContFract.fib_le_of_contsAux_b`：fib_le_of_contsAux_b : n <= 1 ∨ ¬(of 
v).TerminatedAt (n - 2) -> (fib n : K) <= ((of v).contsAux n).b

--- 原说明 ---
As a simple consequence, we can now derive that all denominators are nonnegative
.
-/
theorem zero_le_of_contsAux_b : 0 ≤ ((of v).contsAux n).b := by
  let g := of v
  induction n with
  | zero => rfl
  | succ n IH =>
    rcases Decidable.em <| g.TerminatedAt (n - 1) with terminated | not_terminated
    · -- terminating case
      rcases n with - | n
      · simp
      · have : g.contsAux (n + 2) = g.contsAux (n + 1) :=
          contsAux_stable_step_of_terminated terminated
        simp only [g, this, IH]
    · -- non-terminating case
      calc
        (0 : K) ≤ fib (n + 1) := mod_cast (n + 1).fib.zero_le
        _ ≤ ((of v).contsAux (n + 1)).b := fib_le_of_contsAux_b (Or.inr not_terminated)

/-- Shows that all denominators are nonnegative. -/
/-
**GenContFract.zero_le_of_den** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract`。
形式化陈述：zero_le_of_den : 0 <= (of v).dens n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GenContFract.den_eq_conts_b`：den_eq_conts_b : g.dens n = (g.conts n).b
· 使用定理 `GenContFract.nth_cont_eq_succ_nth_contAux`：nth_cont_eq_succ_nth_contAux 
: g.conts n = g.contsAux (n + 1)
· 使用定理 `GenContFract.zero_le_of_contsAux_b`：zero_le_of_contsAux_b : 0 <= ((of v)
.contsAux n).b

--- 原说明 ---
Shows that all denominators are nonnegative.
-/
theorem zero_le_of_den : 0 ≤ (of v).dens n := by
  rw [den_eq_conts_b, nth_cont_eq_succ_nth_contAux]; exact zero_le_of_contsAux_b
/-
**GenContFract.le_of_succ_succ_get** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract`。
形式化陈述：le_of_succ_succ_get?_contsAux_b {b : K} (nth_partDen_eq : (of v).partDens.
get? n = some b) : b * ((of v).contsAux <| n + 1).b <= ((of v).contsAux <| n + 2
).b
参数：nth_partDen_eq : (of v).partDens.get? n = some b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem le_of_succ_succ_get?_contsAux_b {b : K}
    (nth_partDen_eq : (of v).partDens.get? n = some b) :
    b * ((of v).contsAux <| n + 1).b ≤ ((of v).contsAux <| n + 2).b := by
  obtain ⟨gp_n, nth_s_eq, rfl⟩ : ∃ gp_n, (of v).s.get? n = some gp_n ∧ gp_n.b = b :=
    exists_s_b_of_partDen nth_partDen_eq
  simp [of_partNum_eq_one (partNum_eq_s_a nth_s_eq), zero_le_of_contsAux_b,
    GenContFract.contsAux_recurrence nth_s_eq rfl rfl]

/-- Shows that `bₙ * Bₙ ≤ Bₙ₊₁`, where `bₙ` is the `n`th partial denominator and `Bₙ₊₁` and `Bₙ` are
the `n + 1`th and `n`th denominator of the continued fraction. -/
/-
**GenContFract.le_of_succ_get** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract`。
形式化陈述：le_of_succ_get?_den {b : K} (nth_partDenom_eq : (of v).partDens.get? n = s
ome b) : b * (of v).dens n <= (of v).dens (n + 1)
参数：nth_partDenom_eq : (of v).partDens.get? n = some b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Shows that `bₙ * Bₙ ≤ Bₙ₊₁`, where `bₙ` is the `n`th partial denominator and `Bₙ
₊₁` and `Bₙ` are
the `n + 1`th and `n`th denominator of the continued fraction.
-/
theorem le_of_succ_get?_den {b : K}
    (nth_partDenom_eq : (of v).partDens.get? n = some b) :
    b * (of v).dens n ≤ (of v).dens (n + 1) := by
  rw [den_eq_conts_b, nth_cont_eq_succ_nth_contAux]
  exact le_of_succ_succ_get?_contsAux_b nth_partDenom_eq

/-- Shows that the sequence of denominators is monotone, that is `Bₙ ≤ Bₙ₊₁`. -/
/-
**GenContFract.of_den_mono** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract`。
形式化陈述：of_den_mono : (of v).dens n <= (of v).dens (n + 1)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.em`：∀ (p : Prop) [Decidable p], p ∨ ¬p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `GenContFract.terminatedAt_iff_partDen_none`：terminatedAt_iff_partDen_non
e : g.TerminatedAt n ↔ g.partDens.get? n = none
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Stream'.Seq.TerminatedAt.eq_1`：∀ {α : Type u} (s : Stream'.Seq α) (n : ℕ
), s.TerminatedAt n = (s.get? n = none)
· 使用定理 `GenContFract.dens_stable_of_terminated`：dens_stable_of_terminated (n_le_
m : n <= m) (terminatedAt_n : g.TerminatedAt n) : g.dens m = g.dens n
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Option.ne_none_iff_exists'`：∀ {α : Type u_1} {o : Option α}, o ≠ none ↔ 
∃ x, o = some x
· 使用定理 `GenContFract.of_one_le_get?_partDen`：∀ {K : Type u_1} {v : K} {n : ℕ} [i
nst : Field K] [inst_1 : LinearOrder K] [IsStrictOrderedRing K]   [inst_3 : Floo
rRing K] {b : K}, (GenCon…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `GenContFract.zero_le_of_den`：zero_le_of_den : 0 <= (of v).dens n
· 使用定理 `GenContFract.le_of_succ_get?_den`：∀ {K : Type u_1} {v : K} {n : ℕ} [inst
 : Field K] [inst_1 : LinearOrder K] [IsStrictOrderedRing K]   [inst_3 : FloorRi
ng K] {b : K},   (GenC…

--- 原说明 ---
Shows that the sequence of denominators is monotone, that is `Bₙ ≤ Bₙ₊₁`.
-/
theorem of_den_mono : (of v).dens n ≤ (of v).dens (n + 1) := by
  let g := of v
  rcases Decidable.em <| g.partDens.TerminatedAt n with terminated | not_terminated
  · have : g.TerminatedAt n :=
      terminatedAt_iff_partDen_none.2 (by rwa [Stream'.Seq.TerminatedAt] at terminated)
    have : g.dens (n + 1) = g.dens n :=
      dens_stable_of_terminated n.le_succ this
    rw [this]
  · obtain ⟨b, nth_partDen_eq⟩ : ∃ b, g.partDens.get? n = some b :=
      Option.ne_none_iff_exists'.mp not_terminated
    have : 1 ≤ b := of_one_le_get?_partDen nth_partDen_eq
    calc
      g.dens n ≤ b * g.dens n := by
        simpa using mul_le_mul_of_nonneg_right this zero_le_of_den
      _ ≤ g.dens (n + 1) := le_of_succ_get?_den nth_partDen_eq

section ErrorTerm

/-!
### Approximation of Error Term

Next we derive some approximations for the error term when computing a continued fraction up a given
position, i.e. bounds for the term `|v - (GenContFract.of v).convs n|`.
-/


/-- This lemma follows from the finite correctness proof, the determinant equality, and
by simplifying the difference. -/
/-
**GenContFract.sub_convs_eq** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract`。
形式化陈述：sub_convs_eq {ifp : IntFractPair K} (stream_nth_eq : IntFractPair.stream v
 n = some ifp) : let g
参数：stream_nth_eq : IntFractPair.stream v n = some ifp。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GenContFract.compExactValue_correctness_of_stream_eq_some`：compExactValu
e_correctness_of_stream_eq_some : forall {ifp_n : IntFractPair K}, IntFractPair.
stream v n = some ifp_n -> v = compExactValue (…
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `zero_tsub`：zero_tsub (a : α) : 0 - a = 0
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `GenContFract.of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none`
：of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none : (of v).TerminatedA
t n ↔ IntFractPair.stream v (n + 1) = none
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpContFract.determinant`：determinant (not_terminatedAt_n : ¬(↑s : GenC
ontFract K).TerminatedAt n) : (↑s : GenContFract K).nums n * (↑s : GenContFract 
K).dens (n + 1)…
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
（共 62 条，此处仅展示前 30 条）

--- 原说明 ---
This lemma follows from the finite correctness proof, the determinant equality, 
and
by simplifying the difference.
-/
theorem sub_convs_eq {ifp : IntFractPair K}
    (stream_nth_eq : IntFractPair.stream v n = some ifp) :
    let g := of v
    let B := (g.contsAux (n + 1)).b
    let pB := (g.contsAux n).b
    v - g.convs n = if ifp.fr = 0 then 0 else (-1) ^ n / (B * (ifp.fr⁻¹ * B + pB)) := by
  -- set up some shorthand notation
  let g := of v
  let conts := g.contsAux (n + 1)
  let pred_conts := g.contsAux n
  have g_finite_correctness :
      v = GenContFract.compExactValue pred_conts conts ifp.fr :=
    compExactValue_correctness_of_stream_eq_some stream_nth_eq
  obtain (ifp_fr_eq_zero | ifp_fr_ne_zero) := eq_or_ne ifp.fr 0
  · suffices v - g.convs n = 0 by simpa [ifp_fr_eq_zero]
    replace g_finite_correctness : v = g.convs n := by
      simpa [GenContFract.compExactValue, ifp_fr_eq_zero] using! g_finite_correctness
    exact sub_eq_zero.2 g_finite_correctness
  · -- more shorthand notation
    let A := conts.a
    let B := conts.b
    let pA := pred_conts.a
    let pB := pred_conts.b
    -- first, let's simplify the goal as `ifp.fr ≠ 0`
    suffices v - A / B = (-1) ^ n / (B * (ifp.fr⁻¹ * B + pB)) by simpa [ifp_fr_ne_zero]
    -- now we can unfold `g.compExactValue` to derive the following equality for `v`
    replace g_finite_correctness : v = (pA + ifp.fr⁻¹ * A) / (pB + ifp.fr⁻¹ * B) := by
      simpa [GenContFract.compExactValue, ifp_fr_ne_zero, nextConts, nextNum, nextDen, add_comm]
        using! g_finite_correctness
    -- let's rewrite this equality for `v` in our goal
    suffices
      (pA + ifp.fr⁻¹ * A) / (pB + ifp.fr⁻¹ * B) - A / B = (-1) ^ n / (B * (ifp.fr⁻¹ * B + pB)) by
      rwa [g_finite_correctness]
    -- To continue, we need use the determinant equality. So let's derive the needed hypothesis.
    have n_eq_zero_or_not_terminatedAt_pred_n : n = 0 ∨ ¬g.TerminatedAt (n - 1) := by
      rcases n with - | n'
      · simp
      · have : IntFractPair.stream v (n' + 1) ≠ none := by simp [stream_nth_eq]
        have : ¬g.TerminatedAt n' :=
          (not_congr of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none).2 this
        exact Or.inr this
    have determinant_eq : pA * B - pB * A = (-1) ^ n := by
      match hn : n with
      | 0 => subst n; simp [pA, pB, A, B, pred_conts, conts]
      | n' + 1 =>
        subst n
        simp only [succ_ne_zero, false_or] at n_eq_zero_or_not_terminatedAt_pred_n
        rw [add_tsub_cancel_right] at n_eq_zero_or_not_terminatedAt_pred_n
        exact (SimpContFract.of v).determinant n_eq_zero_or_not_terminatedAt_pred_n
    -- now all we got to do is to rewrite this equality in our goal and re-arrange terms;
    -- however, for this, we first have to derive quite a few tedious inequalities.
    have pB_ineq : (fib n : K) ≤ pB :=
      haveI : n ≤ 1 ∨ ¬g.TerminatedAt (n - 2) := by
        rcases n_eq_zero_or_not_terminatedAt_pred_n with n_eq_zero | not_terminatedAt_pred_n
        · simp [n_eq_zero]
        · exact Or.inr <| mt (terminated_stable (n - 1).pred_le) not_terminatedAt_pred_n
      fib_le_of_contsAux_b this
    have B_ineq : (fib (n + 1) : K) ≤ B :=
      haveI : n + 1 ≤ 1 ∨ ¬g.TerminatedAt (n + 1 - 2) := by
        rcases n_eq_zero_or_not_terminatedAt_pred_n with n_eq_zero | not_terminatedAt_pred_n
        · simp [n_eq_zero]
        · exact Or.inr not_terminatedAt_pred_n
      fib_le_of_contsAux_b this
    have zero_lt_B : 0 < B := B_ineq.trans_lt' <| cast_pos.2 <| fib_pos.2 n.succ_pos
    have : 0 ≤ pB := (Nat.cast_nonneg _).trans pB_ineq
    have : 0 < ifp.fr :=
      ifp_fr_ne_zero.lt_of_le' <| IntFractPair.nth_stream_fr_nonneg stream_nth_eq
    have : pB + ifp.fr⁻¹ * B ≠ 0 := by positivity
    grind

/-- Shows that `|v - Aₙ / Bₙ| ≤ 1 / (Bₙ * Bₙ₊₁)`. -/
/-
**GenContFract.abs_sub_convs_le** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract`。
形式化陈述：abs_sub_convs_le (not_terminatedAt_n : ¬(of v).TerminatedAt n) : |v - (of 
v).convs n| <= 1 / ((of v).dens n * ((of v).dens <| n + 1))
参数：not_terminatedAt_n : ¬(of v).TerminatedAt n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Option.ne_none_iff_exists'`：∀ {α : Type u_1} {o : Option α}, o ≠ none ↔ 
∃ x, o = some x
· 使用定理 `GenContFract.of_partNum_eq_one`：of_partNum_eq_one {a : K} (nth_partNum_e
q : (of v).partNums.get? n = some a) : a = 1
· 使用定理 `GenContFract.partNum_eq_s_a`：partNum_eq_s_a {gp : Pair α} (s_nth_eq : g.
s.get? n = some gp) : g.partNums.get? n = some gp.a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GenContFract.contsAux_recurrence`：contsAux_recurrence {gp ppred pred : P
air K} (nth_s_eq : g.s.get? n = some gp) (nth_contsAux_eq : g.contsAux n = ppred
) (succ_nth_contsAux_e…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `GenContFract.IntFractPair.exists_succ_get?_stream_of_gcf_of_get?_eq_some
`：∀ {K : Type u_1} [inst : DivisionRing K] [inst_1 : LinearOrder K] [inst_2 : Fl
oorRing K] {v : K} {n : ℕ}   {gp_n : GenContFract.Pair K},   (…
· 使用定理 `GenContFract.IntFractPair.succ_nth_stream_eq_some_iff`：succ_nth_stream_e
q_some_iff {ifp_succ_n : IntFractPair K} : IntFractPair.stream v (n + 1) = some 
ifp_succ_n ↔ exists ifp_n : IntFractPair K,…
· 使用定理 `GenContFract.fib_le_of_contsAux_b`：fib_le_of_contsAux_b : n <= 1 ∨ ¬(of 
v).TerminatedAt (n - 2) -> (fib n : K) <= ((of v).contsAux n).b
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `GenContFract.terminated_stable`：terminated_stable (n_le_m : n <= m) (ter
minatedAt_n : g.TerminatedAt n) : g.TerminatedAt m
· 使用定理 `Nat.pred_le`：∀ (n : ℕ), n.pred ≤ n
· 使用定理 `LE.le.trans_lt'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b ≤ a
 → c < b → c < a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `FloorSemiring.instZeroLEOneClass`：∀ {α : Type u_2} [inst : Semiring α] [
inst_1 : PartialOrder α] [FloorSemiring α], ZeroLEOneClass α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.fib_pos`：∀ {n : ℕ}, 0 < Nat.fib n ↔ 0 < n
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
（共 61 条，此处仅展示前 30 条）

--- 原说明 ---
Shows that `|v - Aₙ / Bₙ| ≤ 1 / (Bₙ * Bₙ₊₁)`.
-/
theorem abs_sub_convs_le (not_terminatedAt_n : ¬(of v).TerminatedAt n) :
    |v - (of v).convs n| ≤ 1 / ((of v).dens n * ((of v).dens <| n + 1)) := by
  -- shorthand notation
  let g := of v
  let nextConts := g.contsAux (n + 2)
  set conts := contsAux g (n + 1) with conts_eq
  set pred_conts := contsAux g n with pred_conts_eq
  -- change the goal to something more readable
  change |v - convs g n| ≤ 1 / (conts.b * nextConts.b)
  obtain ⟨gp, s_nth_eq⟩ : ∃ gp, g.s.get? n = some gp :=
    Option.ne_none_iff_exists'.1 not_terminatedAt_n
  have gp_a_eq_one : gp.a = 1 := of_partNum_eq_one (partNum_eq_s_a s_nth_eq)
  -- unfold the recurrence relation for `nextConts.b`
  have nextConts_b_eq : nextConts.b = pred_conts.b + gp.b * conts.b := by
    simp [nextConts, contsAux_recurrence s_nth_eq pred_conts_eq conts_eq, gp_a_eq_one,
      pred_conts_eq.symm, conts_eq.symm, add_comm]
  let den := conts.b * (pred_conts.b + gp.b * conts.b)
  obtain ⟨ifp_succ_n, succ_nth_stream_eq, ifp_succ_n_b_eq_gp_b⟩ :
      ∃ ifp_succ_n, IntFractPair.stream v (n + 1) = some ifp_succ_n ∧ (ifp_succ_n.b : K) = gp.b :=
    IntFractPair.exists_succ_get?_stream_of_gcf_of_get?_eq_some s_nth_eq
  obtain ⟨ifp_n, stream_nth_eq, stream_nth_fr_ne_zero, if_of_eq_ifp_succ_n⟩ :
    ∃ ifp_n, IntFractPair.stream v n = some ifp_n ∧ ifp_n.fr ≠ 0
      ∧ IntFractPair.of ifp_n.fr⁻¹ = ifp_succ_n :=
    IntFractPair.succ_nth_stream_eq_some_iff.1 succ_nth_stream_eq
  let den' := conts.b * (pred_conts.b + ifp_n.fr⁻¹ * conts.b)
  -- now we can use `sub_convs_eq` to simplify our goal
  suffices |(-1) ^ n / den'| ≤ 1 / den by grind [sub_convs_eq]
  -- derive some tedious inequalities that we need to rewrite our goal
  have nextConts_b_ineq : (fib (n + 2) : K) ≤ pred_conts.b + gp.b * conts.b := by
    have : (fib (n + 2) : K) ≤ nextConts.b :=
      fib_le_of_contsAux_b (Or.inr not_terminatedAt_n)
    rwa [nextConts_b_eq] at this
  have conts_b_ineq : (fib (n + 1) : K) ≤ conts.b :=
    haveI : ¬g.TerminatedAt (n - 1) := mt (terminated_stable n.pred_le) not_terminatedAt_n
    fib_le_of_contsAux_b <| Or.inr this
  have zero_lt_conts_b : 0 < conts.b :=
    conts_b_ineq.trans_lt' <| mod_cast fib_pos.2 n.succ_pos
  -- `den'` is positive, so we can remove `|⬝|` from our goal
  suffices 1 / den' ≤ 1 / den by
    have : |(-1) ^ n / den'| = 1 / den' := by
      suffices 1 / |den'| = 1 / den' by rwa [abs_div, abs_neg_one_pow n]
      have : 0 < den' := by
        have : 0 ≤ pred_conts.b :=
          haveI : (fib n : K) ≤ pred_conts.b :=
            haveI : ¬g.TerminatedAt (n - 2) :=
              mt (terminated_stable (n.sub_le 2)) not_terminatedAt_n
            fib_le_of_contsAux_b <| Or.inr this
          le_trans (mod_cast (fib n).zero_le) this
        have : 0 < ifp_n.fr⁻¹ :=
          haveI zero_le_ifp_n_fract : 0 ≤ ifp_n.fr :=
            IntFractPair.nth_stream_fr_nonneg stream_nth_eq
          inv_pos.2 (lt_of_le_of_ne zero_le_ifp_n_fract stream_nth_fr_ne_zero.symm)
        positivity
      rw [abs_of_pos this]
    rwa [this]
  suffices 0 < den ∧ den ≤ den' from div_le_div_of_nonneg_left zero_le_one this.1 this.2
  constructor
  · have : 0 < pred_conts.b + gp.b * conts.b :=
      nextConts_b_ineq.trans_lt' <| mod_cast fib_pos.2 <| succ_pos _
    solve_by_elim [mul_pos]
  · -- we can cancel multiplication by `conts.b` and addition with `pred_conts.b`
    suffices gp.b * conts.b ≤ ifp_n.fr⁻¹ * conts.b by
      simp only [den, den']; gcongr
    suffices (ifp_succ_n.b : K) * conts.b ≤ ifp_n.fr⁻¹ * conts.b by rwa [← ifp_succ_n_b_eq_gp_b]
    have : (ifp_succ_n.b : K) ≤ ifp_n.fr⁻¹ :=
      IntFractPair.succ_nth_stream_b_le_nth_stream_fr_inv stream_nth_eq succ_nth_stream_eq
    gcongr

/-- Shows that `|v - Aₙ / Bₙ| ≤ 1 / (bₙ * Bₙ * Bₙ)`. This bound is worse than the one shown in
`GenContFract.abs_sub_convs_le`, but sometimes it is easier to apply and
sufficient for one's use case.
-/
/-
**GenContFract.abs_sub_convergents_le'** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract`。
形式化陈述：abs_sub_convergents_le' {b : K} (nth_partDen_eq : (of v).partDens.get? n =
 some b) : |v - (of v).convs n| <= 1 / (b * (of v).dens n * (of v).dens n)
参数：nth_partDen_eq : (of v).partDens.get? n = some b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `GenContFract.abs_sub_convs_le`：abs_sub_convs_le (not_terminatedAt_n : ¬(
of v).TerminatedAt n) : |v - (of v).convs n| <= 1 / ((of v).dens n * ((of v).den
s <| n + 1))
· 使用定理 `LE.le.eq_or_lt'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, b ≤
 a → a = b ∨ b < a
· 使用定理 `GenContFract.zero_le_of_den`：zero_le_of_den : 0 <= (of v).dens n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `one_div_le_one_div_of_le`：one_div_le_one_div_of_le (ha : 0 < a) (h : a <
= b) : 1 / b <= 1 / a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instZeroLEOneClass`：∀ {α : Type u_2} [inst : Semiring α] [
inst_1 : PartialOrder α] [FloorSemiring α], ZeroLEOneClass α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `GenContFract.of_one_le_get?_partDen`：∀ {K : Type u_1} {v : K} {n : ℕ} [i
nst : Field K] [inst_1 : LinearOrder K] [IsStrictOrderedRing K]   [inst_3 : Floo
rRing K] {b : K}, (GenCon…
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `GenContFract.le_of_succ_get?_den`：∀ {K : Type u_1} {v : K} {n : ℕ} [inst
 : Field K] [inst_1 : LinearOrder K] [IsStrictOrderedRing K]   [inst_3 : FloorRi
ng K] {b : K},   (GenC…
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
Shows that `|v - Aₙ / Bₙ| ≤ 1 / (bₙ * Bₙ * Bₙ)`. This bound is worse than the on
e shown in
`GenContFract.abs_sub_convs_le`, but sometimes it is easier to apply and
sufficient for one's use case.
-/
theorem abs_sub_convergents_le' {b : K}
    (nth_partDen_eq : (of v).partDens.get? n = some b) :
    |v - (of v).convs n| ≤ 1 / (b * (of v).dens n * (of v).dens n) := by
  have not_terminatedAt_n : ¬(of v).TerminatedAt n := by
    simp [terminatedAt_iff_partDen_none, nth_partDen_eq]
  refine (abs_sub_convs_le not_terminatedAt_n).trans ?_
  -- One can show that `0 < (GenContFract.of v).dens n` but it's easier
  -- to consider the case `(GenContFract.of v).dens n = 0`.
  rcases (zero_le_of_den (K := K)).eq_or_lt' with
    ((hB : (GenContFract.of v).dens n = 0) | hB)
  · simp only [hB, mul_zero, zero_mul, div_zero, le_refl]
  · apply one_div_le_one_div_of_le
    · have : 0 < b := zero_lt_one.trans_le (of_one_le_get?_partDen nth_partDen_eq)
      apply_rules [mul_pos]
    · conv_rhs => rw [mul_comm]
      gcongr
      exact le_of_succ_get?_den nth_partDen_eq

end ErrorTerm

end GenContFract

