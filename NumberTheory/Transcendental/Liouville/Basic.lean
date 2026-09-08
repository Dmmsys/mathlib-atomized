/-
Copyright (c) 2020 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa, Jujian Zhang
-/
module

public import Mathlib.Algebra.Polynomial.DenomsClearable
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Algebra.Order.Interval.Set.Group

/-!

# Liouville's theorem

This file contains a proof of Liouville's theorem stating that all Liouville numbers are
transcendental.

To obtain this result, there is first a proof that Liouville numbers are irrational and two
technical lemmas.  These lemmas exploit the fact that a polynomial with integer coefficients
takes integer values at integers.  When evaluating at a rational number, we can clear denominators
and obtain precise inequalities that ultimately allow us to prove transcendence of
Liouville numbers.
-/

@[expose] public section


/-- A Liouville number is a real number `x` such that for every natural number `n`, there exist
`a, b ∈ ℤ` with `1 < b` such that `0 < |x - a/b| < 1/bⁿ`.
In the implementation, the condition `x ≠ a/b` replaces the traditional equivalent `0 < |x - a/b|`.
-/
/-
**Liouville** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Liouville (x : Real)
参数：x : Real。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Liouville number is a real number `x` such that for every natural number `n`, 
there exist
`a, b ∈ ℤ` with `1 < b` such that `0 < |x - a/b| < 1/bⁿ`.
In the implementation, the condition `x ≠ a/b` replaces the traditional equivale
nt `0 < |x - a/b|`.
-/
def Liouville (x : ℝ) :=
  ∀ n : ℕ, ∃ a b : ℤ, 1 < b ∧ x ≠ a / b ∧ |x - a / b| < 1 / (b : ℝ) ^ n

namespace Liouville

/-
**Liouville.irrational** 是 Mathlib 中的一个定理，位于命名空间 `Liouville`。
形式化陈述：∀ {x : ℝ}, Liouville x → Irrational x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Rat.mk'`：mk'_num_den (q : Rat) : mk' q.num q.den q.den_nz q.reduced = q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Rat.cast_mk'`：cast_mk' (a b h1 h2) : ((⟨a, b, h1, h2⟩ : Rat) : K) = a / 
b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.cast_pos`：∀ {R : Type u_1} [inst : AddCommGroupWithOne R] [inst_1 : 
PartialOrder R] [AddLeftMono R] [ZeroLEOneClass R] [NeZero 1]   {n : ℤ}, 0 < ↑n 
↔ …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `Int.instNeZeroOfNatOfNat`：∀ {n : ℕ} [NeZero n], NeZero (OfNat.ofNat n)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Nat.cast_pos`：cast_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRing 
α] [Nontrivial α] {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `abs_of_pos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], 0 < a → |a| = a
· 使用引理 `div_lt_div_iff₀`：div_lt_div_iff₀ (hb : 0 < b) (hd : 0 < d) : a / b < c /
 d ↔ a * d < c * b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `abs_pos`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α] [
AddLeftMono α] {a : α}, 0 < |a| ↔ a ≠ 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `abs_div`：abs_div (a b : α) : |a / b| = |a| / |b|
· 使用定理 `div_sub_div`：div_sub_div (a : K) {b : K} (c : K) {d : K} (hb : b != 0) (
hd : d != 0) : a / b - c / d = (a * d - b * c) / (b * d)
（共 45 条，此处仅展示前 30 条）
-/
protected theorem irrational {x : ℝ} (h : Liouville x) : Irrational x := by
  -- By contradiction, `x = a / b`, with `a ∈ ℤ`, `0 < b ∈ ℕ` is a Liouville number,
  rintro ⟨⟨a, b, bN0, cop⟩, rfl⟩
  -- clear up the mess of constructions of rationals
  rw [Rat.cast_mk'] at h
  -- Since `a / b` is a Liouville number, there are `p, q ∈ ℤ`, with `q1 : 1 < q`,∈
  -- `a0 : a / b ≠ p / q` and `a1 : |a / b - p / q| < 1 / q ^ (b + 1)`
  rcases h (b + 1) with ⟨p, q, q1, a0, a1⟩
  -- A few useful inequalities
  have qR0 : (0 : ℝ) < q := Int.cast_pos.mpr (zero_lt_one.trans q1)
  have b0 : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr bN0
  have bq0 : (0 : ℝ) < b * q := mul_pos (Nat.cast_pos.mpr bN0.bot_lt) qR0
  -- At a1, clear denominators...
  replace a1 : |a * q - b * p| * q ^ (b + 1) < b * q := by
    rw [div_sub_div _ _ b0 qR0.ne', abs_div, div_lt_div_iff₀ (abs_pos.mpr bq0.ne') (pow_pos qR0 _),
      abs_of_pos bq0, one_mul] at a1
    exact mod_cast a1
  -- At a0, clear denominators...
  replace a0 : a * q - ↑b * p ≠ 0 := by
    rw [Ne, div_eq_div_iff b0 qR0.ne', mul_comm (p : ℝ), ← sub_eq_zero] at a0
    exact mod_cast a0
  -- Actually, `q` is a natural number
  lift q to ℕ using (zero_lt_one.trans q1).le
  -- Looks innocuous, but we now have an integer with non-zero absolute value: this is at
  -- least one away from zero.  The gain here is what gets the proof going.
  have ap : 0 < |a * ↑q - ↑b * p| := abs_pos.mpr a0
  -- Actually, the absolute value of an integer is a natural number
  -- FIXME: This `lift` call duplicates the hypotheses `a1` and `ap`
  lift |a * ↑q - ↑b * p| to ℕ using abs_nonneg (a * ↑q - ↑b * p) with e he
  norm_cast at a1 ap q1
  -- Recall this is by contradiction: we obtained the inequality `b * q ≤ x * q ^ (b + 1)`, so
  -- we are done.
  exact not_le.mpr a1 (Nat.mul_lt_mul_pow_succ ap q1).le

open Polynomial Metric Set Real RingHom

open scoped Polynomial

/-- Let `Z, N` be types, let `R` be a metric space, let `α : R` be a point and let
`j : Z → N → R` be a function.  We aim to estimate how close we can get to `α`, while staying
in the image of `j`.  The points `j z a` of `R` in the image of `j` come with a "cost" equal to
`d a`.  As we get closer to `α` while staying in the image of `j`, we are interested in bounding
the quantity `d a * dist α (j z a)` from below by a strictly positive amount `1 / A`: the intuition
is that approximating well `α` with the points in the image of `j` should come at a high cost.  The
hypotheses on the function `f : R → R` provide us with sufficient conditions to ensure our goal.
The first hypothesis is that `f` is Lipschitz at `α`: this yields a bound on the distance.
The second hypothesis is specific to the Liouville argument and provides the missing bound
involving the cost function `d`.

This lemma collects the properties used in the proof of `exists_pos_real_of_irrational_root`.
It is stated in more general form than needed: in the intended application, `Z = ℤ`, `N = ℕ`,
`R = ℝ`, `d a = (a + 1) ^ f.nat_degree`, `j z a = z / (a + 1)`, `f ∈ ℤ[x]`, `α` is an irrational
root of `f`, `ε` is small, `M` is a bound on the Lipschitz constant of `f` near `α`, `n` is
the degree of the polynomial `f`.
-/
/-
**Liouville.exists_one_le_pow_mul_dist** 是 Mathlib 中的一个定理，位于命名空间 `Liouville`。
形式化陈述：exists_one_le_pow_mul_dist {Z N R : Type*} [PseudoMetricSpace R] {d : N ->
 Real} {j : Z -> N -> R} {f : R -> R} {α : R} {ε M : Real} -- denominators are p
ositive (d0 : forall a : N, 1 <= d a) (e0 : 0 < ε) -- function is Lipschitz at α
 (B : forall ⦃y : R⦄, y in closedBall α ε -> dist (f α) (f y) <= dist α y * M) -
- clear denominators (L : forall ⦃z : Z⦄, forall ⦃a : N⦄, j z a in closedBall α 
ε -> 1 <= d a * dist (f α) (f (j z a))) : exists A : Real, 0 < A ∧ forall z : Z,
 forall a : N, 1 <= d a * 
参数：d0 : forall a : N, 1 <= d a；e0 : 0 < ε；B : forall ⦃y : R⦄, y in closedBall α 
ε -> dist (f α) (f y) <= dist α y * M；L : forall ⦃z : Z⦄, forall ⦃a : N⦄, j z a 
in closedBall α ε -> 1 <= d a * dist (f α) (f (j z a))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `lt_max_iff`：lt_max_iff : a < max b c ↔ a < b ∨ a < c
· 使用引理 `one_div_pos`：one_div_pos : 0 < 1 / a ↔ 0 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `one_le_mul_of_one_le_of_one_le`：one_le_mul_of_one_le_of_one_le [ZeroLEOn
eClass M₀] [PosMulMono M₀] (ha : 1 <= a) (hb : 1 <= b) : (1 : M₀) <= a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.mem_closedBall'`：mem_closedBall' : y in closedBall x ε ↔ dist x y
 <= ε
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用引理 `le_div_iff₀`：le_div_iff₀ (hc : 0 < c) : a <= b / c ↔ a * c <= b
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `one_div_le`：one_div_le (ha : 0 < a) (hb : 0 < b) : 1 / a <= b ↔ 1 / b <=
 a
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1

--- 原说明 ---
Let `Z, N` be types, let `R` be a metric space, let `α : R` be a point and let
`j : Z → N → R` be a function.  We aim to estimate how close we can get to `α`, 
while staying
in the image of `j`.  The points `j z a` of `R` in the image of `j` come with a 
"cost" equal to
`d a`.  As we get closer to `α` while staying in the image of `j`, we are intere
sted in bounding
the quantity `d a * dist α (j z a)` from below by a strictly positive amount `1 
/ A`: the intuition
is that approximating well `α` with the points in the image of `j` should come a
t a high cost.  The
hypotheses on the function `f : R → R` provide us with sufficient conditions to 
ensure our goal.
The first hypothesis is that `f` is Lipschitz at `α`: this yields a bound on the
 distance.
The second hypothesis is specific to the Liouville argument and provides the mis
sing bound
involving the cost function `d`.

This lemma collects the properties used in the proof of `exists_pos_real_of_irra
tional_root`.
It is stated in more general form than needed: in the intended application, `Z =
 ℤ`, `N = ℕ`,
`R = ℝ`, `d a = (a + 1) ^ f.nat_degree`, `j z a = z / (a + 1)`, `f ∈ ℤ[x]`, `α` 
is an irrational
root of `f`, `ε` is small, `M` is a bound on the Lipschitz constant of `f` near 
`α`, `n` is
the degree of the polynomial `f`.
-/
theorem exists_one_le_pow_mul_dist {Z N R : Type*} [PseudoMetricSpace R] {d : N → ℝ}
    {j : Z → N → R} {f : R → R} {α : R} {ε M : ℝ}
    -- denominators are positive
    (d0 : ∀ a : N, 1 ≤ d a)
    (e0 : 0 < ε)
    -- function is Lipschitz at α
    (B : ∀ ⦃y : R⦄, y ∈ closedBall α ε → dist (f α) (f y) ≤ dist α y * M)
    -- clear denominators
    (L : ∀ ⦃z : Z⦄, ∀ ⦃a : N⦄, j z a ∈ closedBall α ε → 1 ≤ d a * dist (f α) (f (j z a))) :
    ∃ A : ℝ, 0 < A ∧ ∀ z : Z, ∀ a : N, 1 ≤ d a * (dist α (j z a) * A) := by
  -- A useful inequality to keep at hand
  have me0 : 0 < max (1 / ε) M := lt_max_iff.mpr (Or.inl (one_div_pos.mpr e0))
  -- The maximum between `1 / ε` and `M` works
  refine ⟨max (1 / ε) M, me0, fun z a => ?_⟩
  -- First, let's deal with the easy case in which we are far away from `α`
  by_cases dm1 : 1 ≤ dist α (j z a) * max (1 / ε) M
  · exact one_le_mul_of_one_le_of_one_le (d0 a) dm1
  · -- `j z a = z / (a + 1)`: we prove that this ratio is close to `α`
    have : j z a ∈ closedBall α ε := by
      refine mem_closedBall'.mp (le_trans ?_ ((one_div_le me0 e0).mpr (le_max_left _ _)))
      exact (le_div_iff₀ me0).mpr (not_le.mp dm1).le
    -- use the "separation from `1`" (assumption `L`) for numerators,
    refine (L this).trans ?_
    -- remove a common factor and use the Lipschitz assumption `B`
    gcongr
    · exact zero_le_one.trans (d0 a)
    · refine (B this).trans ?_
      gcongr
      apply le_max_right
/-
**Liouville.exists_pos_real_of_irrational_root** 是 Mathlib 中的一个定理，位于命名空间 `Liouvi
lle`。
形式化陈述：exists_pos_real_of_irrational_root {α : Real} (ha : Irrational α) {f : Int
[X]} (f0 : f != 0) (fa : eval α (map (algebraMap Int Real) f) = 0) : exists A : 
Real, 0 < A ∧ forall a : Int, forall b : Nat, (1 : Real) <= ((b : Real) + 1) ^ f
.natDegree * (|α - a / (b + 1)| * A)
参数：ha : Irrational α；f0 : f != 0；fa : eval α (map (algebraMap Int Real) f) = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_coe`：mem_coe {a : α} {s : Finset α} : a in (s : Set α) ↔ a in
 (s : Finset α)
· 使用定理 `Multiset.mem_toFinset`：mem_toFinset {a : α} {s : Multiset α} : a in s.to
Finset ↔ a in s
· 使用定理 `Polynomial.mem_roots`：mem_roots (hp : p != 0) : a in p.roots ↔ IsRoot p 
a
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `Polynomial.map_injective`：map_injective (hf : Function.Injective f) : Fu
nction.Injective (map f)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Int.cast_inj`：cast_inj : (m : α) = n ↔ m = n
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.map_zero`：∀ {R : Type u} {S : Type v} [inst : Semiring R] [in
st_1 : Semiring S] (f : R →+* S), Polynomial.map f 0 = 0
· 使用定理 `Polynomial.IsRoot.def`：∀ {R : Type u} {a : R} [inst : Semiring R] {p : P
olynomial R}, p.IsRoot a ↔ Polynomial.eval a p = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.exists_closedBall_inter_eq_singleton_of_discrete`：exists_closedBa
ll_inter_eq_singleton_of_discrete (hs : IsDiscrete s) {x : α} (hx : x in s) : ex
ists ε > 0, Metric.closedBall x ε inter s = {…
· 使用引理 `Set.Finite.isDiscrete`：Set.Finite.isDiscrete [T1Space X] {s : Set X} (hs
 : s.Finite) : IsDiscrete s
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `OrderTopology.t5Space`：∀ {X : Type u_1} [inst : LinearOrder X] [inst_1 :
 TopologicalSpace X] [OrderTopology X], T5Space X
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `IsCompact.exists_isMaxOn`：IsCompact.exists_isMaxOn [ClosedIciTopology α]
 {s : Set β} (hs : IsCompact s) (ne_s : s.Nonempty) {f : β -> α} (hf : Continuou
sOn f s) : exi…
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `CompactIccSpace.isCompact_Icc`：∀ {α : Type u_1} {inst : TopologicalSpace
 α} {inst_1 : Preorder α} [self : CompactIccSpace α] {a b : α},   IsCompact (Set
.Icc a b)
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `sub_lt_self`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeft
StrictMono α] (a : α) {b : α}, 0 < b → a - b < a
（共 79 条，此处仅展示前 30 条）
-/
theorem exists_pos_real_of_irrational_root {α : ℝ} (ha : Irrational α) {f : ℤ[X]} (f0 : f ≠ 0)
    (fa : eval α (map (algebraMap ℤ ℝ) f) = 0) :
    ∃ A : ℝ, 0 < A ∧ ∀ a : ℤ, ∀ b : ℕ,
      (1 : ℝ) ≤ ((b : ℝ) + 1) ^ f.natDegree * (|α - a / (b + 1)| * A) := by
  -- `fR` is `f` viewed as a polynomial with `ℝ` coefficients.
  set fR : ℝ[X] := map (algebraMap ℤ ℝ) f
  -- `fR` is non-zero, since `f` is non-zero.
  obtain fR0 : fR ≠ 0 := fun fR0 =>
    (map_injective (algebraMap ℤ ℝ) fun _ _ A => Int.cast_inj.mp A).ne f0
      (fR0.trans (Polynomial.map_zero _).symm)
  -- reformulating assumption `fa`: `α` is a root of `fR`.
  have ar : α ∈ (fR.roots.toFinset : Set ℝ) :=
    Finset.mem_coe.mpr (Multiset.mem_toFinset.mpr ((mem_roots fR0).mpr (IsRoot.def.mpr fa)))
  -- Since the polynomial `fR` has finitely many roots, there is a closed interval centered at `α`
  -- such that `α` is the only root of `fR` in the interval.
  obtain ⟨ζ, z0, U⟩ : ∃ ζ > 0, closedBall α ζ ∩ fR.roots.toFinset = {α} :=
    @exists_closedBall_inter_eq_singleton_of_discrete _ _ _ (toFinite _).isDiscrete _ ar
  -- Since `fR` is continuous, it is bounded on the interval above.
  obtain ⟨xm, -, hM⟩ : ∃ xm : ℝ, xm ∈ Icc (α - ζ) (α + ζ) ∧
      IsMaxOn (|fR.derivative.eval ·|) (Icc (α - ζ) (α + ζ)) xm :=
    IsCompact.exists_isMaxOn isCompact_Icc
      ⟨α, (sub_lt_self α z0).le, (lt_add_of_pos_right α z0).le⟩
      (continuous_abs.comp fR.derivative.continuous_aeval).continuousOn
  -- Use the key lemma `exists_one_le_pow_mul_dist`: we are left to show that ...
  refine
    @exists_one_le_pow_mul_dist ℤ ℕ ℝ _ _ _ (fun y => fR.eval y) α ζ |fR.derivative.eval xm| ?_ z0
      (fun y hy => ?_) fun z a hq => ?_
  -- 1: the denominators are positive -- essentially by definition;
  · exact fun a => one_le_pow₀ ((le_add_iff_nonneg_left 1).mpr a.cast_nonneg)
  -- 2: the polynomial `fR` is Lipschitz at `α` -- as its derivative continuous;
  · rw [mul_comm]
    rw [Real.closedBall_eq_Icc] at hy
    -- apply the Mean Value Theorem: the bound on the derivative comes from differentiability.
    refine
      Convex.norm_image_sub_le_of_norm_deriv_le (fun _ _ => fR.differentiableAt)
        (fun y h => by rw [fR.deriv]; exact hM h) (convex_Icc _ _) hy (mem_Icc_iff_abs_le.mp ?_)
    exact @mem_closedBall_self ℝ _ α ζ (le_of_lt z0)
  -- 3: the weird inequality of Liouville type with powers of the denominators.
  · change 1 ≤ (a + 1 : ℝ) ^ f.natDegree * |eval α fR - eval ((z : ℝ) / (a + 1)) fR|
    rw [fa, zero_sub, abs_neg]
    rw [show (a + 1 : ℝ) = ((a + 1 : ℕ) : ℤ) by norm_cast] at hq ⊢
    -- key observation: the right-hand side of the inequality is an *integer*.  Therefore,
    -- if its absolute value is not at least one, then it vanishes.  Proceed by contradiction
    refine one_le_pow_mul_abs_eval_div (Int.natCast_succ_pos a) fun hy => ?_
    -- As the evaluation of the polynomial vanishes, we found a root of `fR` that is rational.
    -- We know that `α` is the only root of `fR` in our interval, and `α` is irrational:
    -- follow your nose.
    refine ha.ne_rational z (a + 1) (mem_singleton_iff.mp ?_).symm
    refine U.subset ?_
    refine ⟨hq, Finset.mem_coe.mp (Multiset.mem_toFinset.mpr ?_)⟩
    exact (mem_roots fR0).mpr (IsRoot.def.mpr hy)

/-- **Liouville's Theorem** -/
/-
**Liouville.transcendental** 是 Mathlib 中的一个定理，位于命名空间 `Liouville`。
形式化陈述：∀ {x : ℝ}, Liouville x → Transcendental ℤ x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Polynomial.eval_map_algebraMap`：eval_map_algebraMap (P : R[X]) (b : B) :
 (map (algebraMap R B) P).eval b = aeval b P
· 使用定理 `Liouville.exists_pos_real_of_irrational_root`：exists_pos_real_of_irratio
nal_root {α : Real} (ha : Irrational α) {f : Int[X]} (f0 : f != 0) (fa : eval α 
(map (algebraMap Int Real) f) = 0)…
· 使用定理 `Liouville.irrational`：∀ {x : ℝ}, Liouville x → Irrational x
· 使用引理 `pow_unbounded_of_one_lt`：pow_unbounded_of_one_lt [ExistsAddOfLE R] (x : 
R) (hy1 : 1 < y) : exists n : Nat, x < y ^ n
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
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
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.cast_lt`：∀ {R : Type u_1} [inst : AddCommGroupWithOne R] [inst_1 : P
artialOrder R] [AddLeftMono R] [ZeroLEOneClass R] [NeZero 1]   {m n : ℤ}, ↑m < ↑
n…
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用引理 `lt_div_iff₀'`：lt_div_iff₀' (hc : 0 < c) : a < b / c ↔ c * a < b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
（共 63 条，此处仅展示前 30 条）

--- 原说明 ---
**Liouville's Theorem**
-/
protected theorem transcendental {x : ℝ} (lx : Liouville x) : Transcendental ℤ x := by
  -- Proceed by contradiction: if `x` is algebraic, then `x` is the root (`ef0`) of a
  -- non-zero (`f0`) polynomial `f`
  rintro ⟨f : ℤ[X], f0, ef0⟩
  -- Change `aeval x f = 0` to `eval (map _ f) = 0`, who knew.
  replace ef0 : (f.map (algebraMap ℤ ℝ)).eval x = 0 := by
    rwa [← eval_map_algebraMap] at ef0
  -- There is a "large" real number `A` such that `(b + 1) ^ (deg f) * |f (x - a / (b + 1))| * A`
  -- is at least one.  This is obtained from lemma `exists_pos_real_of_irrational_root`.
  obtain ⟨A, hA, h⟩ : ∃ A : ℝ, 0 < A ∧ ∀ (a : ℤ) (b : ℕ),
      (1 : ℝ) ≤ ((b : ℝ) + 1) ^ f.natDegree * (|x - a / (b + 1)| * A) :=
    exists_pos_real_of_irrational_root lx.irrational f0 ef0
  -- Since the real numbers are Archimedean, a power of `2` exceeds `A`: `hn : A < 2 ^ r`.
  rcases pow_unbounded_of_one_lt A (lt_add_one 1) with ⟨r, hn⟩
  -- Use the Liouville property, with exponent `r + deg f`.
  obtain ⟨a, b, b1, -, a1⟩ : ∃ a b : ℤ, 1 < b ∧ x ≠ a / b ∧
      |x - a / b| < 1 / (b : ℝ) ^ (r + f.natDegree) :=
    lx (r + f.natDegree)
  have b0 : (0 : ℝ) < b := zero_lt_one.trans (by rw [← Int.cast_one]; exact Int.cast_lt.mpr b1)
  -- Prove that `b ^ f.nat_degree * abs (x - a / b)` is strictly smaller than itself
  -- recall, this is a proof by contradiction!
  refine lt_irrefl ((b : ℝ) ^ f.natDegree * |x - ↑a / ↑b|) ?_
  -- clear denominators at `a1`
  rw [lt_div_iff₀' (pow_pos b0 _), pow_add, mul_assoc] at a1
  -- split the inequality via `1 / A`.
  refine (?_ : (b : ℝ) ^ f.natDegree * |x - a / b| < 1 / A).trans_le ?_
  -- This branch of the proof uses the Liouville condition and the Archimedean property
  · refine (lt_div_iff₀' hA).mpr ?_
    refine lt_of_le_of_lt ?_ a1
    gcongr
    refine hn.le.trans ?_
    rw [one_add_one_eq_two]
    gcongr
    norm_cast
  -- this branch of the proof exploits the "integrality" of evaluations of polynomials
  -- at ratios of integers.
  · lift b to ℕ using zero_le_one.trans b1.le
    specialize h a b.pred
    rwa [← Nat.cast_succ, Nat.succ_pred_eq_of_pos (zero_lt_one.trans _), ← mul_assoc, ←
      div_le_iff₀ hA] at h
    exact Int.ofNat_lt.mp b1

end Liouville

