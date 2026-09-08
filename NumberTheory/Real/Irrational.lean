/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Data.Nat.Prime.Int
public import Mathlib.Data.Rat.Sqrt
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Tactic.IntervalCases

/-!
# Irrational real numbers

In this file we define a predicate `Irrational` on `ℝ`, prove that the `n`-th root of an integer
number is irrational if it is not integer, and that `√(q : ℚ)` is irrational if and only if
`¬IsSquare q ∧ 0 ≤ q`.

We also provide dot-style constructors like `Irrational.add_ratCast`, `Irrational.ratCast_sub` etc.

With the `Decidable` instances in this file, is possible to prove `Irrational √n` using `decide`,
when `n` is a numeric literal or cast;
but this only works if you `unseal Nat.sqrt.iter in` before the theorem where you use this proof.
-/

@[expose] public section


open Rat Real

/-- A real number is irrational if it is not equal to any rational number. -/
@[wikidata Q607728]
/-
**Irrational** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Irrational (x : Real)
参数：x : Real。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A real number is irrational if it is not equal to any rational number.
-/
def Irrational (x : ℝ) :=
  x ∉ Set.range ((↑) : ℚ → ℝ)
/-
**irrational_iff_ne_rational** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：irrational_iff_ne_rational (x : Real) : Irrational x ↔ forall a b : Int, b
 != 0 -> x != a / b
参数：x : Real。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Rat.cast_div`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p q
 : ℚ), ↑(p / q) = ↑p / ↑q
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Rat.cast_intCast`：cast_intCast (n : Int) : ((n : Rat) : α) = n
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem irrational_iff_ne_rational (x : ℝ) : Irrational x ↔ ∀ a b : ℤ, b ≠ 0 → x ≠ a / b := by
  simp [Irrational, Rat.forall, eq_comm]
/-
**Irrational.ne_rational** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Irrational.ne_rational {x : Real} (hx : Irrational x) (a b : Int) : x != a
 / b
参数：hx : Irrational x；a b : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.cast_div`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p q
 : ℚ), ↑(p / q) = ↑p / ↑q
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Rat.cast_intCast`：cast_intCast (n : Int) : ((n : Rat) : α) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Irrational.ne_rational {x : ℝ} (hx : Irrational x) (a b : ℤ) : x ≠ a / b := by
  rintro rfl; exact hx ⟨a / b, by simp⟩
/-
**exists_rat_of_not_irrational** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_rat_of_not_irrational {x : Real} (hx : ¬ Irrational x) : exists (q 
: Rat), x = q
参数：hx : ¬ Irrational x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem exists_rat_of_not_irrational {x : ℝ} (hx : ¬ Irrational x) : ∃ (q : ℚ), x = q := by
  grind [Irrational]

/-- A transcendental real number is irrational. -/
/-
**Transcendental.irrational** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Transcendental.irrational {r : Real} (tr : Transcendental Rat r) : Irratio
nal r
参数：tr : Transcendental Rat r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `isAlgebraic_algebraMap`：isAlgebraic_algebraMap [Nontrivial R] (x : R) : 
IsAlgebraic R (algebraMap R A x)

--- 原说明 ---
A transcendental real number is irrational.
-/
theorem Transcendental.irrational {r : ℝ} (tr : Transcendental ℚ r) : Irrational r := by
  rintro ⟨a, rfl⟩
  exact tr (isAlgebraic_algebraMap a)

/-!
### Irrationality of roots of integer and rational numbers
-/


/-- If `x^n`, `n > 0`, is integer and is not the `n`-th power of an integer, then
`x` is irrational. -/
/-
**irrational_nrt_of_notint_nrt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：irrational_nrt_of_notint_nrt {x : Real} (n : Nat) (m : Int) (hxr : x ^ n =
 m) (hv : ¬exists y : Int, x = y) (hnpos : 0 < n) : Irrational x
参数：n : Nat；m : Int；hxr : x ^ n = m；hv : ¬exists y : Int, x = y；hnpos : 0 < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Rat.mk'`：mk'_num_den (q : Rat) : mk' q.num q.den q.den_nz q.reduced = q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Int.cast_ne_zero`：cast_ne_zero : (n : α) != 0 ↔ n != 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Int.natCast_ne_zero`：∀ {n : ℕ}, ↑n ≠ 0 ↔ n ≠ 0
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `Dvd.intro_left`：Dvd.intro_left (c : α) (h : c * a = b) : a ∣ b
· 使用引理 `Int.cast_inj`：cast_inj : (m : α) = n ↔ m = n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Int.cast_mul`：cast_mul {α : Type*} [NonAssocRing α] : forall m n, ((m * 
n : Int) : α) = m * n
· 使用定理 `Int.cast_pow`：∀ {R : Type u_1} [inst : Ring R] (n : ℤ) (m : ℕ), ↑(n ^ m)
 = ↑n ^ m
· 使用引理 `div_eq_iff_mul_eq`：div_eq_iff_mul_eq (hb : b != 0) : a / b = c ↔ c * b =
 a
· 使用引理 `div_pow`：div_pow (a b : α) (n : Nat) : (a / b) ^ n = a ^ n / b ^ n
· 使用定理 `Rat.cast_divInt`：cast_divInt (a b : Int) : (a /. b : α) = a / b
· 使用引理 `Rat.cast_pow`：cast_pow (p : Rat) (n : Nat) : ↑(p ^ n) = (p ^ n : α)
· 使用定理 `Rat.mk_eq_divInt`：∀ {num : ℤ} {den : ℕ} {nz : den ≠ 0} {c : num.natAbs.C
oprime den},   { num := num, den := den, den_nz := nz, reduced := c } = Rat.divI
nt num…
· 使用定理 `Int.ofNat_one`：↑1 = 1
· 使用定理 `Rat.divInt_one`：∀ (n : ℤ), Rat.divInt n 1 = ↑n
· 使用定理 `Rat.cast_intCast`：cast_intCast (n : Int) : ((n : Rat) : α) = n
· 使用定理 `Nat.gcd_eq_right`：∀ {m n : ℕ}, n ∣ m → m.gcd n = n
· 使用定理 `Nat.pow_dvd_pow_iff`：∀ {a b n : ℕ}, n ≠ 0 → (a ^ n ∣ b ^ n ↔ a ∣ b)
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Int.natAbs_pow`：∀ (n : ℤ) (k : ℕ), (n ^ k).natAbs = n.natAbs ^ k
· 使用定理 `Int.natCast_dvd_natCast`：∀ {m n : ℕ}, ↑m ∣ ↑n ↔ m ∣ n
· 使用定理 `Int.natCast_pow`：∀ (m n : ℕ), ↑(m ^ n) = ↑m ^ n
· 使用定理 `Int.dvd_natAbs`：∀ {a b : ℤ}, a ∣ ↑b.natAbs ↔ a ∣ b
· 使用定理 `Nat.Coprime.gcd_eq_one`：∀ {m n : ℕ}, m.Coprime n → m.gcd n = 1

--- 原说明 ---
If `x^n`, `n > 0`, is integer and is not the `n`-th power of an integer, then
`x` is irrational.
-/
theorem irrational_nrt_of_notint_nrt {x : ℝ} (n : ℕ) (m : ℤ) (hxr : x ^ n = m)
    (hv : ¬∃ y : ℤ, x = y) (hnpos : 0 < n) : Irrational x := by
  rintro ⟨⟨N, D, P, C⟩, rfl⟩
  rw [← cast_pow] at hxr
  have c1 : ((D : ℤ) : ℝ) ≠ 0 := by
    rw [Int.cast_ne_zero, Int.natCast_ne_zero]
    exact P
  have c2 : ((D : ℤ) : ℝ) ^ n ≠ 0 := pow_ne_zero _ c1
  rw [mk_eq_divInt, cast_pow, cast_divInt, div_pow, div_eq_iff_mul_eq c2, ← Int.cast_pow,
    ← Int.cast_pow, ← Int.cast_mul, Int.cast_inj] at hxr
  have hdivn : (D : ℤ) ^ n ∣ N ^ n := Dvd.intro_left m hxr
  rw [← Int.dvd_natAbs, ← Int.natCast_pow, Int.natCast_dvd_natCast, Int.natAbs_pow,
    Nat.pow_dvd_pow_iff hnpos.ne'] at hdivn
  obtain rfl : D = 1 := by rw [← Nat.gcd_eq_right hdivn, C.gcd_eq_one]
  refine hv ⟨N, ?_⟩
  rw [mk_eq_divInt, Int.ofNat_one, divInt_one, cast_intCast]

/-- If `x^n = m` is an integer and `n` does not divide the `multiplicity p m`, then `x`
is irrational. -/
/-
**irrational_nrt_of_n_not_dvd_multiplicity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：irrational_nrt_of_n_not_dvd_multiplicity {x : Real} (n : Nat) {m : Int} (h
m : m != 0) (p : Nat) [hp : Fact p.Prime] (hxr : x ^ n = m) (hv : multiplicity (
p : Int) m % n != 0) : Irrational x
参数：n : Nat；hm : m != 0；p : Nat；hxr : x ^ n = m；hv : multiplicity (p : Int) m % n
 != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Int.cast_inj`：cast_inj : (m : α) = n ↔ m = n
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `multiplicity_of_one_right`：multiplicity_of_one_right {a : α} (ha : ¬IsUn
it a) : multiplicity a 1 = 0
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isUnit_iff_dvd_one`：isUnit_iff_dvd_one {x : α} : IsUnit x ↔ x ∣ 1
· 使用定理 `Int.natCast_dvd_natCast`：∀ {m n : ℕ}, ↑m ∣ ↑n ↔ m ∣ n
· 使用定理 `Nat.Prime.not_dvd_one`：∀ {p : ℕ}, Nat.Prime p → ¬p ∣ 1
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Nat.mod_self`：∀ (n : ℕ), n % n = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `irrational_nrt_of_notint_nrt`：irrational_nrt_of_notint_nrt {x : Real} (n
 : Nat) (m : Int) (hxr : x ^ n = m) (hv : ¬exists y : Int, x = y) (hnpos : 0 < n
) : Irrational x
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Nat.mul_mod_right`：∀ (m n : ℕ), m * n % m = 0
· 使用定理 `FiniteMultiplicity.multiplicity_pow`：∀ {α : Type u_1} [inst : CommMonoid
WithZero α] [IsCancelMulZero α] {p a : α},   Prime p → FiniteMultiplicity p a → 
∀ {k : ℕ}, multiplicity p…
· 使用定理 `Int.instIsCancelMulZero`：IsCancelMulZero ℤ
· 使用定理 `Nat.prime_iff_prime_int`：prime_iff_prime_int {p : Nat} : p.Prime ↔ _root
_.Prime (p : Int)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.finiteMultiplicity_iff`：Int.finiteMultiplicity_iff {a b : Int} : Fin
iteMultiplicity a b ↔ a.natAbs != 1 ∧ b != 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
If `x^n = m` is an integer and `n` does not divide the `multiplicity p m`, then 
`x`
is irrational.
-/
theorem irrational_nrt_of_n_not_dvd_multiplicity {x : ℝ} (n : ℕ) {m : ℤ} (hm : m ≠ 0) (p : ℕ)
    [hp : Fact p.Prime] (hxr : x ^ n = m)
    (hv : multiplicity (p : ℤ) m % n ≠ 0) :
    Irrational x := by
  rcases Nat.eq_zero_or_pos n with (rfl | hnpos)
  · rw [eq_comm, pow_zero, ← Int.cast_one, Int.cast_inj] at hxr
    simp [hxr, multiplicity_of_one_right (mt isUnit_iff_dvd_one.1
      (mt Int.natCast_dvd_natCast.1 hp.1.not_dvd_one))] at hv
  refine irrational_nrt_of_notint_nrt _ _ hxr ?_ hnpos
  rintro ⟨y, rfl⟩
  rw [← Int.cast_pow, Int.cast_inj] at hxr
  subst m
  have : y ≠ 0 := by rintro rfl; rw [zero_pow hnpos.ne'] at hm; exact hm rfl
  rw [(Int.finiteMultiplicity_iff.2 ⟨by simp [hp.1.ne_one], this⟩).multiplicity_pow
    (Nat.prime_iff_prime_int.1 hp.1), Nat.mul_mod_right] at hv
  exact hv rfl
/-
**irrational_sqrt_of_multiplicity_odd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：irrational_sqrt_of_multiplicity_odd (m : Int) (hm : 0 < m) (p : Nat) [hp :
 Fact p.Prime] (Hpv : multiplicity (p : Int) m % 2 = 1) : Irrational (√m)
参数：m : Int；hm : 0 < m；p : Nat；Hpv : multiplicity (p : Int) m % 2 = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `irrational_nrt_of_n_not_dvd_multiplicity`：irrational_nrt_of_n_not_dvd_mu
ltiplicity {x : Real} (n : Nat) {m : Int} (hm : m != 0) (p : Nat) [hp : Fact p.P
rime] (hxr : x ^ n = m) (hv : …
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `Real.sq_sqrt`：sq_sqrt (h : 0 <= x) : √x ^ 2 = x
· 使用定理 `Int.cast_nonneg`：∀ {R : Type u_1} [inst : AddCommGroupWithOne R] [inst_1
 : PartialOrder R] [AddLeftMono R] [ZeroLEOneClass R] {n : ℤ},   0 ≤ n → 0 ≤ ↑n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem irrational_sqrt_of_multiplicity_odd (m : ℤ) (hm : 0 < m) (p : ℕ) [hp : Fact p.Prime]
    (Hpv : multiplicity (p : ℤ) m % 2 = 1) :
    Irrational (√m) :=
  @irrational_nrt_of_n_not_dvd_multiplicity _ 2 _ (Ne.symm (ne_of_lt hm)) p hp
    (sq_sqrt (Int.cast_nonneg hm.le)) (by rw [Hpv]; exact one_ne_zero)
/-
**not_irrational_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：¬Irrational 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_not_intro`：∀ {p : Prop}, p → ¬¬p
· 使用定理 `Rat.cast_zero`：cast_zero : ((0 : Rat) : α) = 0
-/
@[simp] theorem not_irrational_zero : ¬Irrational 0 := not_not_intro ⟨0, Rat.cast_zero⟩
/-
**not_irrational_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：¬Irrational 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_not_intro`：∀ {p : Prop}, p → ¬¬p
· 使用定理 `Rat.cast_one`：cast_one : ((1 : Rat) : α) = 1
-/
@[simp] theorem not_irrational_one : ¬Irrational 1 := not_not_intro ⟨1, Rat.cast_one⟩
/-
**irrational_sqrt_ratCast_iff_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：irrational_sqrt_ratCast_iff_of_nonneg {q : Rat} (hq : 0 <= q) : Irrational
 (√q) ↔ ¬IsSquare q
参数：hq : 0 <= q。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用引理 `Rat.cast_injective`：cast_injective : Injective ((↑) : Rat -> α) | ⟨n₁, d
₁, d₁0, c₁⟩, ⟨n₂, d₂, d₂0, c₂⟩, h => by have d₁a : (d₁ : α) != 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.cast_mul`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p q
 : ℚ), ↑(p * q) = ↑p * ↑q
· 使用定理 `Real.mul_self_sqrt`：mul_self_sqrt (h : 0 <= x) : √x * √x = x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Rat.cast_nonneg`：∀ {q : ℚ} {K : Type u_5} [inst : Field K] [inst_1 : Lin
earOrder K] [IsStrictOrderedRing K], 0 ≤ ↑q ↔ 0 ≤ q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.sqrt_mul_self_eq_abs`：sqrt_mul_self_eq_abs (x : Real) : √(x * x) = 
|x|
-/
theorem irrational_sqrt_ratCast_iff_of_nonneg {q : ℚ} (hq : 0 ≤ q) :
    Irrational (√q) ↔ ¬IsSquare q := by
  refine Iff.not (?_ : Exists _ ↔ Exists _)
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, Rat.cast_injective (α := ℝ) ?_⟩
    rw [Rat.cast_mul, hy, mul_self_sqrt (Rat.cast_nonneg.2 hq)]
  · rintro ⟨q', rfl⟩
    exact ⟨|q'|, mod_cast (sqrt_mul_self_eq_abs q').symm⟩
/-
**irrational_sqrt_ratCast_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：irrational_sqrt_ratCast_iff {q : Rat} : Irrational (√q) ↔ ¬IsSquare q ∧ 0 
<= q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `irrational_sqrt_ratCast_iff_of_nonneg`：irrational_sqrt_ratCast_iff_of_no
nneg {q : Rat} (hq : 0 <= q) : Irrational (√q) ↔ ¬IsSquare q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Real.sqrt_eq_zero_of_nonpos`：sqrt_eq_zero_of_nonpos (h : x <= 0) : √x = 
0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Rat.cast_nonpos`：∀ {q : ℚ} {K : Type u_5} [inst : Field K] [inst_1 : Lin
earOrder K] [IsStrictOrderedRing K], ↑q ≤ 0 ↔ q ≤ 0
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `false_iff`：∀ (p : Prop), (False ↔ p) = ¬p
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem irrational_sqrt_ratCast_iff {q : ℚ} :
    Irrational (√q) ↔ ¬IsSquare q ∧ 0 ≤ q := by
  obtain hq | hq := le_or_gt 0 q
  · simp_rw [irrational_sqrt_ratCast_iff_of_nonneg hq, and_iff_left hq]
  · rw [sqrt_eq_zero_of_nonpos (Rat.cast_nonpos.2 hq.le)]
    simp_rw [not_irrational_zero, false_iff, not_and, not_le, hq, implies_true]
/-
**irrational_sqrt_intCast_iff_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：irrational_sqrt_intCast_iff_of_nonneg {z : Int} (hz : 0 <= z) : Irrational
 (√z) ↔ ¬IsSquare z
参数：hz : 0 <= z。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.isSquare_intCast_iff`：isSquare_intCast_iff {z : Int} : IsSquare (z :
 Rat) ↔ IsSquare z
· 使用定理 `irrational_sqrt_ratCast_iff_of_nonneg`：irrational_sqrt_ratCast_iff_of_no
nneg {q : Rat} (hq : 0 <= q) : Irrational (√q) ↔ ¬IsSquare q
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ
· 使用定理 `Rat.cast_intCast`：cast_intCast (n : Int) : ((n : Rat) : α) = n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem irrational_sqrt_intCast_iff_of_nonneg {z : ℤ} (hz : 0 ≤ z) :
    Irrational (√z) ↔ ¬IsSquare z := by
  rw [← Rat.isSquare_intCast_iff, ← irrational_sqrt_ratCast_iff_of_nonneg (mod_cast hz),
    Rat.cast_intCast]
/-
**irrational_sqrt_intCast_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：irrational_sqrt_intCast_iff {z : Int} : Irrational (√z) ↔ ¬IsSquare z ∧ 0 
<= z
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.cast_intCast`：cast_intCast (n : Int) : ((n : Rat) : α) = n
· 使用定理 `irrational_sqrt_ratCast_iff`：irrational_sqrt_ratCast_iff {q : Rat} : Irr
ational (√q) ↔ ¬IsSquare q ∧ 0 <= q
· 使用定理 `Rat.isSquare_intCast_iff`：isSquare_intCast_iff {z : Int} : IsSquare (z :
 Rat) ↔ IsSquare z
· 使用定理 `Int.cast_nonneg_iff`：∀ {R : Type u_1} [inst : AddCommGroupWithOne R] [in
st_1 : PartialOrder R] [AddLeftMono R] [ZeroLEOneClass R] [NeZero 1]   {n : ℤ}, 
0 ≤ ↑n ↔ …
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem irrational_sqrt_intCast_iff {z : ℤ} :
    Irrational (√z) ↔ ¬IsSquare z ∧ 0 ≤ z := by
  rw [← Rat.cast_intCast, irrational_sqrt_ratCast_iff, Rat.isSquare_intCast_iff,
    Int.cast_nonneg_iff]
/-
**irrational_sqrt_natCast_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：irrational_sqrt_natCast_iff {n : Nat} : Irrational (√n) ↔ ¬IsSquare n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.isSquare_natCast_iff`：isSquare_natCast_iff {n : Nat} : IsSquare (n :
 Rat) ↔ IsSquare n
· 使用定理 `irrational_sqrt_ratCast_iff_of_nonneg`：irrational_sqrt_ratCast_iff_of_no
nneg {q : Rat} (hq : 0 <= q) : Irrational (√q) ↔ ¬IsSquare q
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Rat.cast_natCast`：cast_natCast (n : Nat) : ((n : Rat) : α) = n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem irrational_sqrt_natCast_iff {n : ℕ} : Irrational (√n) ↔ ¬IsSquare n := by
  rw [← Rat.isSquare_natCast_iff, ← irrational_sqrt_ratCast_iff_of_nonneg n.cast_nonneg,
    Rat.cast_natCast]
/-
**irrational_sqrt_ofNat_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：irrational_sqrt_ofNat_iff {n : Nat} [n.AtLeastTwo] : Irrational √(ofNat(n)
) ↔ ¬IsSquare ofNat(n)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `irrational_sqrt_natCast_iff`：irrational_sqrt_natCast_iff {n : Nat} : Irr
ational (√n) ↔ ¬IsSquare n
-/
theorem irrational_sqrt_ofNat_iff {n : ℕ} [n.AtLeastTwo] :
    Irrational √(ofNat(n)) ↔ ¬IsSquare ofNat(n) :=
  irrational_sqrt_natCast_iff
/-
**Nat.Prime.irrational_sqrt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nat.Prime.irrational_sqrt {p : Nat} (hp : Nat.Prime p) : Irrational (√p)
参数：hp : Nat.Prime p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `irrational_sqrt_natCast_iff`：irrational_sqrt_natCast_iff {n : Nat} : Irr
ational (√n) ↔ ¬IsSquare n
· 使用引理 `Irreducible.not_isSquare`：Irreducible.not_isSquare (ha : Irreducible x) 
: ¬IsSquare x
-/
theorem Nat.Prime.irrational_sqrt {p : ℕ} (hp : Nat.Prime p) : Irrational (√p) :=
  irrational_sqrt_natCast_iff.mpr hp.not_isSquare

/-- **Irrationality of the Square Root of 2** -/
/-
**irrational_sqrt_two** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：irrational_sqrt_two : Irrational (√2)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Prime.irrational_sqrt`：Nat.Prime.irrational_sqrt {p : Nat} (hp : Nat
.Prime p) : Irrational (√p)
· 使用定理 `Nat.prime_two`：prime_two : Prime 2

--- 原说明 ---
**Irrationality of the Square Root of 2**
-/
theorem irrational_sqrt_two : Irrational (√2) := by
  simpa using Nat.prime_two.irrational_sqrt

/--
This can be used as
```lean
unseal Nat.sqrt.iter in
example : Irrational √24 := by decide
```
-/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This can be used as
```lean
unseal Nat.sqrt.iter in
example : Irrational √24 := by decide
```
-/
instance {n : ℕ} [n.AtLeastTwo] : Decidable (Irrational √(ofNat(n))) :=
  decidable_of_iff' _ irrational_sqrt_ofNat_iff
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : ℕ) : Decidable (Irrational (√n)) :=
  decidable_of_iff' _ irrational_sqrt_natCast_iff
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (z : ℤ) : Decidable (Irrational (√z)) :=
  decidable_of_iff' _ irrational_sqrt_intCast_iff
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (q : ℚ) : Decidable (Irrational (√q)) :=
  decidable_of_iff' _ irrational_sqrt_ratCast_iff

/-!
### Dot-style operations on `Irrational`

#### Coercion of a rational/integer/natural number is not irrational
-/


namespace Irrational

variable {x : ℝ}

/-!
#### Irrational number is not equal to a rational/integer/natural number
-/


/-
**Irrational.ne_rat** 是 Mathlib 中的一个定理，位于命名空间 `Irrational`。
形式化陈述：ne_rat (h : Irrational x) (q : Rat) : x != q
参数：h : Irrational x；q : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
#### Irrational number is not equal to a rational/integer/natural number
-/
theorem ne_rat (h : Irrational x) (q : ℚ) : x ≠ q := fun hq => h ⟨q, hq.symm⟩
/-
**Irrational.ne_int** 是 Mathlib 中的一个定理，位于命名空间 `Irrational`。
形式化陈述：ne_int (h : Irrational x) (m : Int) : x != m
参数：h : Irrational x；m : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.cast_intCast`：cast_intCast (n : Int) : ((n : Rat) : α) = n
· 使用定理 `Irrational.ne_rat`：ne_rat (h : Irrational x) (q : Rat) : x != q
-/
theorem ne_int (h : Irrational x) (m : ℤ) : x ≠ m := by
  rw [← Rat.cast_intCast]
  exact h.ne_rat _
/-
**Irrational.ne_nat** 是 Mathlib 中的一个定理，位于命名空间 `Irrational`。
形式化陈述：ne_nat (h : Irrational x) (m : Nat) : x != m
参数：h : Irrational x；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irrational.ne_int`：ne_int (h : Irrational x) (m : Int) : x != m
-/
theorem ne_nat (h : Irrational x) (m : ℕ) : x ≠ m :=
  h.ne_int m
/-
**Irrational.ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Irrational`。
形式化陈述：ne_zero (h : Irrational x) : x != 0
参数：h : Irrational x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Irrational.ne_nat`：ne_nat (h : Irrational x) (m : Nat) : x != m
-/
theorem ne_zero (h : Irrational x) : x ≠ 0 := mod_cast h.ne_nat 0
/-
**Irrational.ne_one** 是 Mathlib 中的一个定理，位于命名空间 `Irrational`。
形式化陈述：ne_one (h : Irrational x) : x != 1
参数：h : Irrational x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Irrational.ne_nat`：ne_nat (h : Irrational x) (m : Nat) : x != m
-/
theorem ne_one (h : Irrational x) : x ≠ 1 := by simpa only [Nat.cast_one] using h.ne_nat 1
/-
**Irrational.ne_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Irrational`。
形式化陈述：∀ {x : ℝ}, Irrational x → ∀ (n : ℕ) [inst : n.AtLeastTwo], x ≠ OfNat.ofNat
 n
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irrational.ne_nat`：ne_nat (h : Irrational x) (m : Nat) : x != m
-/
@[simp] theorem ne_ofNat (h : Irrational x) (n : ℕ) [n.AtLeastTwo] : x ≠ ofNat(n) :=
  h.ne_nat n

end Irrational

@[simp]
/-
**Rat.not_irrational** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Rat.not_irrational (q : Rat) : ¬Irrational q
参数：q : Rat。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Rat.not_irrational (q : ℚ) : ¬Irrational q := fun h => h ⟨q, rfl⟩

@[simp]
/-
**Int.not_irrational** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Int.not_irrational (m : Int) : ¬Irrational m
参数：m : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irrational.ne_int`：ne_int (h : Irrational x) (m : Int) : x != m
-/
theorem Int.not_irrational (m : ℤ) : ¬Irrational m := fun h => h.ne_int m rfl

@[simp]
/-
**Nat.not_irrational** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nat.not_irrational (m : Nat) : ¬Irrational m
参数：m : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irrational.ne_nat`：ne_nat (h : Irrational x) (m : Nat) : x != m
-/
theorem Nat.not_irrational (m : ℕ) : ¬Irrational m := fun h => h.ne_nat m rfl
/-
**not_irrational_ofNat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ (n : ℕ) [inst : n.AtLeastTwo], ¬Irrational (OfNat.ofNat n)
参数：n : ℕ；OfNat.ofNat n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.not_irrational`：Nat.not_irrational (m : Nat) : ¬Irrational m
-/
@[simp] theorem not_irrational_ofNat (n : ℕ) [n.AtLeastTwo] : ¬Irrational ofNat(n) :=
  n.not_irrational
namespace Irrational

variable (q : ℚ) {x y : ℝ}

/-!
#### Addition of rational/integer/natural numbers
-/


/-- If `x + y` is irrational, then at least one of `x` and `y` is irrational. -/
/-
**Irrational.add_cases** 是 Mathlib 中的一个定理，位于命名空间 `Irrational`。
形式化陈述：add_cases : Irrational (x + y) -> Irrational x ∨ Irrational y
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.cast_add`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p q
 : ℚ), ↑(p + q) = ↑p + ↑q
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α

--- 原说明 ---
If `x + y` is irrational, then at least one of `x` and `y` is irrational.
-/
theorem add_cases : Irrational (x + y) → Irrational x ∨ Irrational y := by
  delta Irrational
  contrapose!
  rintro ⟨⟨rx, rfl⟩, ⟨ry, rfl⟩⟩
  exact ⟨rx + ry, cast_add rx ry⟩
/-
**Irrational.of_ratCast_add** 是 Mathlib 中的一个定理，位于命名空间 `Irrational`。
形式化陈述：of_ratCast_add (h : Irrational (q + x)) : Irrational x
参数：h : Irrational (q + x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Irrational.add_cases`：add_cases : Irrational (x + y) -> Irrational x ∨ I
rrational y
· 使用定理 `Rat.not_irrational`：Rat.not_irrational (q : Rat) : ¬Irrational q
-/
theorem of_ratCast_add (h : Irrational (q + x)) : Irrational x :=
  h.add_cases.resolve_left q.not_irrational
/-
**Irrational.ratCast_add** 是 Mathlib 中的一个定理，位于命名空间 `Irrational`。
形式化陈述：ratCast_add (h : Irrational x) : Irrational (q + x)
参数：h : Irrational x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irrational.of_ratCast_add`：of_ratCast_add (h : Irrational (q + x)) : Irr
ational x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.cast_neg`：∀ {α : Type u_3} [inst : DivisionRing α] (q : ℚ), ↑(-q) = 
-↑q
· 使用定理 `neg_add_cancel_left`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), -a 
+ (a + b) = b
-/
theorem ratCast_add (h : Irrational x) : Irrational (q + x) :=
  of_ratCast_add (-q) <| by rwa [cast_neg, neg_add_cancel_left]
/-
**Irrational.of_add_ratCast** 是 Mathlib 中的一个定理，位于命名空间 `Irrational`。
形式化陈述：of_add_ratCast : Irrational (x + q) -> Irrational x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irrational.of_ratCast_add`：of_ratCast_add (h : Irrational (q + x)) : Irr
ational x
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem of_add_ratCast : Irrational (x + q) → Irrational x :=
  add_comm (↑q) x ▸ of_ratCast_add q
/-
**Irrational.add_ratCast** 是 Mathlib 中的一个定理，位于命名空间 `Irrational`。
形式化陈述：add_ratCast (h : Irrational x) : Irrational (x + q)
参数：h : Irrational x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irrational.ratCast_add`：ratCast_add (h : Irrational x) : Irrational (q +
 x)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem add_ratCast (h : Irrational x) : Irrational (x + q) :=
  add_comm (↑q) x ▸ h.ratCast_add q
/-
**Irrational.of_intCast_add** 是 Mathlib 中的一个定理，位于命名空间 `Irrational`。
形式化陈述：of_intCast_add (m : Int) (h : Irrational (m + x)) : Irrational x
参数：m : Int；h : Irrational (m + x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irrational.of_ratCast_add`：of_ratCast_add (h : Irrational (q + x)) : Irr
ational x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.cast_intCast`：cast_intCast (n : Int) : ((n : Rat) : α) = n
-/
theorem of_intCast_add (m : ℤ) (h : Irrational (m + x)) : Irrational x := by
  rw [← cast_intCast] at h
  exact h.of_ratCast_add m
/-
**Irrational.of_add_intCast** 是 Mathlib 中的一个定理，位于命名空间 `Irrational`。
形式化陈述：of_add_intCast (m : Int) (h : Irrational (x + m)) : Irrational x
参数：m : Int；h : Irrational (x + m)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irrational.of_intCast_add`：of_intCast_add (m : Int) (h : Irrational (m +
 x)) : Irrational x
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem of_add_intCast (m : ℤ) (h : Irrational (x + m)) : Irrational x :=
  of_intCast_add m <| add_comm x m ▸ h
/-
**Irrational.intCast_add** 是 Mathlib 中的一个定理，位于命名空间 `Irrational`。
形式化陈述：intCast_add (h : Irrational x) (m : Int) : Irrational (m + x)
参数：h : Irrational x；m : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.cast_intCast`：cast_intCast (n : Int) : ((n : Rat) : α) = n
· 使用定理 `Irrational.ratCast_add`：ratCast_add (h : Irrational x) : Irrational (q +
 x)
-/
theorem intCast_add (h : Irrational x) (m : ℤ) : Irrational (m + x) := by
  rw [← cast_intCast]
  exact h.ratCast_add m
/-
**Irrational.add_intCast** 是 Mathlib 中的一个定理，位于命名空间 `Irrational`。
形式化陈述：add_intCast (h : Irrational x) (m : Int) : Irrational (x + m)
参数：h : Irrational x；m : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irrational.intCast_add`：intCast_add (h : Irrational x) (m : Int) : Irrat
ional (m + x)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem add_intCast (h : Irrational x) (m : ℤ) : Irrational (x + m) :=
  add_comm (↑m) x ▸ h.intCast_add m
/-
**Irrational.of_natCast_add** 是 Mathlib 中的一个定理，位于命名空间 `Irrational`。
形式化陈述：of_natCast_add (m : Nat) (h : Irrational (m + x)) : Irrational x
参数：m : Nat；h : Irrational (m + x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irrational.of_intCast_add`：of_intCast_add (m : Int) (h : Irrational (m +
 x)) : Irrational x
-/
theorem of_natCast_add (m : ℕ) (h : Irrational (m + x)) : Irrational x :=
  h.of_intCast_add m
/-
**Irrational.of_add_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Irrational`。
形式化陈述：of_add_natCast (m : Nat) (h : Irrational (x + m)) : Irrational x
参数：m : Nat；h : Irrational (x + m)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irrational.of_add_intCast`：of_add_intCast (m : Int) (h : Irrational (x +
 m)) : Irrational x
-/
theorem of_add_natCast (m : ℕ) (h : Irrational (x + m)) : Irrational x :=
  h.of_add_intCast m
/-
**Irrational.natCast_add** 是 Mathlib 中的一个定理，位于命名空间 `Irrational`。
形式化陈述：natCast_add (h : Irrational x) (m : Nat) : Irrational (m + x)
参数：h : Irrational x；m : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irrational.intCast_add`：intCast_add (h : Irrational x) (m : Int) : Irrat
ional (m + x)
-/
theorem natCast_add (h : Irrational x) (m : ℕ) : Irrational (m + x) :=
  h.intCast_add m
/-
**Irrational.add_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Irrational`。
形式化陈述：add_natCast (h : Irrational x) (m : Nat) : Irrational (x + m)
参数：h : Irrational x；m : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irrational.add_intCast`：add_intCast (h : Irrational x) (m : Int) : Irrat
ional (x + m)
-/
theorem add_natCast (h : Irrational x) (m : ℕ) : Irrational (x + m) :=
  h.add_intCast m
/-!
#### Negation
-/


/-
**Irrational.of_neg** 是 Mathlib 中的一个定理，位于命名空间 `Irrational`。
形式化陈述：of_neg (h : Irrational (-x)) : Irrational x
参数：h : Irrational (-x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.cast_neg`：∀ {α : Type u_3} [inst : DivisionRing α] (q : ℚ), ↑(-q) = 
-↑q

--- 原说明 ---
#### Negation
-/
theorem of_neg (h : Irrational (-x)) : Irrational x := fun ⟨q, hx⟩ => h ⟨-q, by rw [cast_neg, hx]⟩
/-
**Irrational.neg** 是 Mathlib 中的一个定理，位于命名空间 `Irrational`。
形式化陈述：∀ {x : ℝ}, Irrational x → Irrational (-x)
参数：-x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irrational.of_neg`：of_neg (h : Irrational (-x)) : Irrational x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
protected theorem neg (h : Irrational x) : Irrational (-x) :=
  of_neg <| by rwa [neg_neg]

/-!
#### Subtraction of rational/integer/natural numbers
-/


/-
**Irrational.sub_ratCast** 是 Mathlib 中的一个定理，位于命名空间 `Irrational`。
形式化陈述：sub_ratCast (h : Irrational x) : Irrational (x - q)
参数：h : Irrational x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Rat.cast_neg`：∀ {α : Type u_3} [inst : DivisionRing α] (q : ℚ), ↑(-q) = 
-↑q
· 使用定理 `Irrational.add_ratCast`：add_ratCast (h : Irrational x) : Irrational (x +
 q)

--- 原说明 ---
#### Subtraction of rational/integer/natural numbers
-/
theorem sub_ratCast (h : Irrational x) : Irrational (x - q) := by
  simpa only [sub_eq_add_neg, cast_neg] using h.add_ratCast (-q)
/-
**Irrational.ratCast_sub** 是 Mathlib 中的一个定理，位于命名空间 `Irrational`。
形式化陈述：ratCast_sub (h : Irrational x) : Irrational (q - x)
参数：h : Irrational x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Irrational.ratCast_add`：ratCast_add (h : Irrational x) : Irrational (q +
 x)
· 使用定理 `Irrational.neg`：∀ {x : ℝ}, Irrational x → Irrational (-x)
-/
theorem ratCast_sub (h : Irrational x) : Irrational (q - x) := by
  simpa only [sub_eq_add_neg] using h.neg.ratCast_add q
/-
**Irrational.of_sub_ratCast** 是 Mathlib 中的一个定理，位于命名空间 `Irrational`。
形式化陈述：of_sub_ratCast (h : Irrational (x - q)) : Irrational x
参数：h : Irrational (x - q)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irrational.of_add_ratCast`：of_add_ratCast : Irrational (x + q) -> Irrati
onal x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.cast_neg`：∀ {α : Type u_3} [inst : DivisionRing α] (q : ℚ), ↑(-q) = 
-↑q
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
-/
theorem of_sub_ratCast (h : Irrational (x - q)) : Irrational x :=
  of_add_ratCast (-q) <| by simpa only [cast_neg, sub_eq_add_neg] using h
/-
**Irrational.of_ratCast_sub** 是 Mathlib 中的一个定理，位于命名空间 `Irrational`。
形式化陈述：of_ratCast_sub (h : Irrational (q - x)) : Irrational x
参数：h : Irrational (q - x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irrational.of_neg`：of_neg (h : Irrational (-x)) : Irrational x
· 使用定理 `Irrational.of_ratCast_add`：of_ratCast_add (h : Irrational (q + x)) : Irr
ational x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
-/
theorem of_ratCast_sub (h : Irrational (q - x)) : Irrational x :=
  of_neg (of_ratCast_add q (by simpa only [sub_eq_add_neg] using h))
/-
**Irrational.sub_intCast** 是 Mathlib 中的一个定理，位于命名空间 `Irrational`。
形式化陈述：sub_intCast (h : Irrational x) (m : Int) : Irrational (x - m)
参数：h : Irrational x；m : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.cast_intCast`：cast_intCast (n : Int) : ((n : Rat) : α) = n
· 使用定理 `Irrational.sub_ratCast`：sub_ratCast (h : Irrational x) : Irrational (x -
 q)
-/
theorem sub_intCast (h : Irrational x) (m : ℤ) : Irrational (x - m) := by
  simpa only [Rat.cast_intCast] using h.sub_ratCast m
/-
**Irrational.intCast_sub** 是 Mathlib 中的一个定理，位于命名空间 `Irrational`。
形式化陈述：intCast_sub (h : Irrational x) (m : Int) : Irrational (m - x)
参数：h : Irrational x；m : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Rat.cast_intCast`：cast_intCast (n : Int) : ((n : Rat) : α) = n
· 使用定理 `Irrational.ratCast_sub`：ratCast_sub (h : Irrational x) : Irrational (q -
 x)
-/
theorem intCast_sub (h : Irrational x) (m : ℤ) : Irrational (m - x) := by
  simpa only [Rat.cast_intCast] using h.ratCast_sub m
/-
**Irrational.of_sub_intCast** 是 Mathlib 中的一个定理，位于命名空间 `Irrational`。
形式化陈述：of_sub_intCast (m : Int) (h : Irrational (x - m)) : Irrational x
参数：m : Int；h : Irrational (x - m)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irrational.of_sub_ratCast`：of_sub_ratCast (h : Irrational (x - q)) : Irr
ational x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.cast_intCast`：cast_intCast (n : Int) : ((n : Rat) : α) = n
-/
theorem of_sub_intCast (m : ℤ) (h : Irrational (x - m)) : Irrational x :=
  of_sub_ratCast m <| by rwa [Rat.cast_intCast]
/-
**Irrational.of_intCast_sub** 是 Mathlib 中的一个定理，位于命名空间 `Irrational`。
形式化陈述：of_intCast_sub (m : Int) (h : Irrational (m - x)) : Irrational x
参数：m : Int；h : Irrational (m - x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irrational.of_ratCast_sub`：of_ratCast_sub (h : Irrational (q - x)) : Irr
ational x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.cast_intCast`：cast_intCast (n : Int) : ((n : Rat) : α) = n
-/
theorem of_intCast_sub (m : ℤ) (h : Irrational (m - x)) : Irrational x :=
  of_ratCast_sub m <| by rwa [Rat.cast_intCast]
/-
**Irrational.sub_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Irrational`。
形式化陈述：sub_natCast (h : Irrational x) (m : Nat) : Irrational (x - m)
参数：h : Irrational x；m : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irrational.sub_intCast`：sub_intCast (h : Irrational x) (m : Int) : Irrat
ional (x - m)
-/
theorem sub_natCast (h : Irrational x) (m : ℕ) : Irrational (x - m) :=
  h.sub_intCast m
/-
**Irrational.natCast_sub** 是 Mathlib 中的一个定理，位于命名空间 `Irrational`。
形式化陈述：natCast_sub (h : Irrational x) (m : Nat) : Irrational (m - x)
参数：h : Irrational x；m : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irrational.intCast_sub`：intCast_sub (h : Irrational x) (m : Int) : Irrat
ional (m - x)
-/
theorem natCast_sub (h : Irrational x) (m : ℕ) : Irrational (m - x) :=
  h.intCast_sub m
/-
**Irrational.of_sub_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Irrational`。
形式化陈述：of_sub_natCast (m : Nat) (h : Irrational (x - m)) : Irrational x
参数：m : Nat；h : Irrational (x - m)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irrational.of_sub_intCast`：of_sub_intCast (m : Int) (h : Irrational (x -
 m)) : Irrational x
-/
theorem of_sub_natCast (m : ℕ) (h : Irrational (x - m)) : Irrational x :=
  h.of_sub_intCast m
/-
**Irrational.of_natCast_sub** 是 Mathlib 中的一个定理，位于命名空间 `Irrational`。
形式化陈述：of_natCast_sub (m : Nat) (h : Irrational (m - x)) : Irrational x
参数：m : Nat；h : Irrational (m - x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irrational.of_intCast_sub`：of_intCast_sub (m : Int) (h : Irrational (m -
 x)) : Irrational x
-/
theorem of_natCast_sub (m : ℕ) (h : Irrational (m - x)) : Irrational x :=
  h.of_intCast_sub m
/-!
#### Multiplication by rational numbers
-/


/-
**Irrational.mul_cases** 是 Mathlib 中的一个定理，位于命名空间 `Irrational`。
形式化陈述：mul_cases : Irrational (x * y) -> Irrational x ∨ Irrational y
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.cast_mul`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p q
 : ℚ), ↑(p * q) = ↑p * ↑q
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α

--- 原说明 ---
#### Multiplication by rational numbers
-/
theorem mul_cases : Irrational (x * y) → Irrational x ∨ Irrational y := by
  delta Irrational
  contrapose!
  rintro ⟨⟨rx, rfl⟩, ⟨ry, rfl⟩⟩
  exact ⟨rx * ry, cast_mul rx ry⟩
/-
**Irrational.of_mul_ratCast** 是 Mathlib 中的一个定理，位于命名空间 `Irrational`。
形式化陈述：of_mul_ratCast (h : Irrational (x * q)) : Irrational x
参数：h : Irrational (x * q)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `Irrational.mul_cases`：mul_cases : Irrational (x * y) -> Irrational x ∨ I
rrational y
· 使用定理 `Rat.not_irrational`：Rat.not_irrational (q : Rat) : ¬Irrational q
-/
theorem of_mul_ratCast (h : Irrational (x * q)) : Irrational x :=
  h.mul_cases.resolve_right q.not_irrational
/-
**Irrational.mul_ratCast** 是 Mathlib 中的一个定理，位于命名空间 `Irrational`。
形式化陈述：mul_ratCast (h : Irrational x) {q : Rat} (hq : q != 0) : Irrational (x * q
)
参数：h : Irrational x；hq : q != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irrational.of_mul_ratCast`：of_mul_ratCast (h : Irrational (x * q)) : Irr
ational x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.cast_mul`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p q
 : ℚ), ↑(p * q) = ↑p * ↑q
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `Rat.cast_one`：cast_one : ((1 : Rat) : α) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem mul_ratCast (h : Irrational x) {q : ℚ} (hq : q ≠ 0) : Irrational (x * q) :=
  of_mul_ratCast q⁻¹ <| by rwa [mul_assoc, ← cast_mul, mul_inv_cancel₀ hq, cast_one, mul_one]
/-
**Irrational.of_ratCast_mul** 是 Mathlib 中的一个定理，位于命名空间 `Irrational`。
形式化陈述：of_ratCast_mul : Irrational (q * x) -> Irrational x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irrational.of_mul_ratCast`：of_mul_ratCast (h : Irrational (x * q)) : Irr
ational x
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem of_ratCast_mul : Irrational (q * x) → Irrational x :=
  mul_comm x q ▸ of_mul_ratCast q
/-
**Irrational.ratCast_mul** 是 Mathlib 中的一个定理，位于命名空间 `Irrational`。
形式化陈述：ratCast_mul (h : Irrational x) {q : Rat} (hq : q != 0) : Irrational (q * x
)
参数：h : Irrational x；hq : q != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irrational.mul_ratCast`：mul_ratCast (h : Irrational x) {q : Rat} (hq : q
 != 0) : Irrational (x * q)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem ratCast_mul (h : Irrational x) {q : ℚ} (hq : q ≠ 0) : Irrational (q * x) :=
  mul_comm x q ▸ h.mul_ratCast hq
/-
**Irrational.of_mul_intCast** 是 Mathlib 中的一个定理，位于命名空间 `Irrational`。
形式化陈述：of_mul_intCast (m : Int) (h : Irrational (x * m)) : Irrational x
参数：m : Int；h : Irrational (x * m)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irrational.of_mul_ratCast`：of_mul_ratCast (h : Irrational (x * q)) : Irr
ational x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.cast_intCast`：cast_intCast (n : Int) : ((n : Rat) : α) = n
-/
theorem of_mul_intCast (m : ℤ) (h : Irrational (x * m)) : Irrational x :=
  of_mul_ratCast m <| by rwa [cast_intCast]
/-
**Irrational.of_intCast_mul** 是 Mathlib 中的一个定理，位于命名空间 `Irrational`。
形式化陈述：of_intCast_mul (m : Int) (h : Irrational (m * x)) : Irrational x
参数：m : Int；h : Irrational (m * x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irrational.of_ratCast_mul`：of_ratCast_mul : Irrational (q * x) -> Irrati
onal x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.cast_intCast`：cast_intCast (n : Int) : ((n : Rat) : α) = n
-/
theorem of_intCast_mul (m : ℤ) (h : Irrational (m * x)) : Irrational x :=
  of_ratCast_mul m <| by rwa [cast_intCast]
/-
**Irrational.mul_intCast** 是 Mathlib 中的一个定理，位于命名空间 `Irrational`。
形式化陈述：mul_intCast (h : Irrational x) {m : Int} (hm : m != 0) : Irrational (x * m
)
参数：h : Irrational x；hm : m != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.cast_intCast`：cast_intCast (n : Int) : ((n : Rat) : α) = n
· 使用定理 `Irrational.mul_ratCast`：mul_ratCast (h : Irrational x) {q : Rat} (hq : q
 != 0) : Irrational (x * q)
· 使用引理 `Int.cast_ne_zero`：cast_ne_zero : (n : α) != 0 ↔ n != 0
-/
theorem mul_intCast (h : Irrational x) {m : ℤ} (hm : m ≠ 0) : Irrational (x * m) := by
  rw [← cast_intCast]
  refine h.mul_ratCast ?_
  rwa [Int.cast_ne_zero]
/-
**Irrational.intCast_mul** 是 Mathlib 中的一个定理，位于命名空间 `Irrational`。
形式化陈述：intCast_mul (h : Irrational x) {m : Int} (hm : m != 0) : Irrational (m * x
)
参数：h : Irrational x；hm : m != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irrational.mul_intCast`：mul_intCast (h : Irrational x) {m : Int} (hm : m
 != 0) : Irrational (x * m)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem intCast_mul (h : Irrational x) {m : ℤ} (hm : m ≠ 0) : Irrational (m * x) :=
  mul_comm x m ▸ h.mul_intCast hm
/-
**Irrational.of_mul_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Irrational`。
形式化陈述：of_mul_natCast (m : Nat) (h : Irrational (x * m)) : Irrational x
参数：m : Nat；h : Irrational (x * m)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irrational.of_mul_intCast`：of_mul_intCast (m : Int) (h : Irrational (x *
 m)) : Irrational x
-/
theorem of_mul_natCast (m : ℕ) (h : Irrational (x * m)) : Irrational x :=
  h.of_mul_intCast m
/-
**Irrational.of_natCast_mul** 是 Mathlib 中的一个定理，位于命名空间 `Irrational`。
形式化陈述：of_natCast_mul (m : Nat) (h : Irrational (m * x)) : Irrational x
参数：m : Nat；h : Irrational (m * x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irrational.of_intCast_mul`：of_intCast_mul (m : Int) (h : Irrational (m *
 x)) : Irrational x
-/
theorem of_natCast_mul (m : ℕ) (h : Irrational (m * x)) : Irrational x :=
  h.of_intCast_mul m
/-
**Irrational.mul_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Irrational`。
形式化陈述：mul_natCast (h : Irrational x) {m : Nat} (hm : m != 0) : Irrational (x * m
)
参数：h : Irrational x；hm : m != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irrational.mul_intCast`：mul_intCast (h : Irrational x) {m : Int} (hm : m
 != 0) : Irrational (x * m)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.natCast_ne_zero`：∀ {n : ℕ}, ↑n ≠ 0 ↔ n ≠ 0
-/
theorem mul_natCast (h : Irrational x) {m : ℕ} (hm : m ≠ 0) : Irrational (x * m) :=
  h.mul_intCast <| Int.natCast_ne_zero.2 hm
/-
**Irrational.natCast_mul** 是 Mathlib 中的一个定理，位于命名空间 `Irrational`。
形式化陈述：natCast_mul (h : Irrational x) {m : Nat} (hm : m != 0) : Irrational (m * x
)
参数：h : Irrational x；hm : m != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irrational.intCast_mul`：intCast_mul (h : Irrational x) {m : Int} (hm : m
 != 0) : Irrational (m * x)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.natCast_ne_zero`：∀ {n : ℕ}, ↑n ≠ 0 ↔ n ≠ 0
-/
theorem natCast_mul (h : Irrational x) {m : ℕ} (hm : m ≠ 0) : Irrational (m * x) :=
  h.intCast_mul <| Int.natCast_ne_zero.2 hm
/-!
#### Inverse
-/


/-
**Irrational.of_inv** 是 Mathlib 中的一个定理，位于命名空间 `Irrational`。
形式化陈述：of_inv (h : Irrational x⁻¹) : Irrational x
参数：h : Irrational x⁻¹。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rat.cast_inv`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p :
 ℚ), ↑p⁻¹ = (↑p)⁻¹
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α

--- 原说明 ---
#### Inverse
-/
theorem of_inv (h : Irrational x⁻¹) : Irrational x := fun ⟨q, hq⟩ => h <| hq ▸ ⟨q⁻¹, q.cast_inv⟩
/-
**Irrational.inv** 是 Mathlib 中的一个定理，位于命名空间 `Irrational`。
形式化陈述：∀ {x : ℝ}, Irrational x → Irrational x⁻¹
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irrational.of_inv`：of_inv (h : Irrational x⁻¹) : Irrational x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
-/
protected theorem inv (h : Irrational x) : Irrational x⁻¹ :=
  of_inv <| by rwa [inv_inv]

/-!
#### Division
-/


/-
**Irrational.div_cases** 是 Mathlib 中的一个定理，位于命名空间 `Irrational`。
形式化陈述：div_cases (h : Irrational (x / y)) : Irrational x ∨ Irrational y
参数：h : Irrational (x / y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `Irrational.of_inv`：of_inv (h : Irrational x⁻¹) : Irrational x
· 使用定理 `Irrational.mul_cases`：mul_cases : Irrational (x * y) -> Irrational x ∨ I
rrational y

--- 原说明 ---
#### Division
-/
theorem div_cases (h : Irrational (x / y)) : Irrational x ∨ Irrational y :=
  h.mul_cases.imp id of_inv
/-
**Irrational.of_ratCast_div** 是 Mathlib 中的一个定理，位于命名空间 `Irrational`。
形式化陈述：of_ratCast_div (h : Irrational (q / x)) : Irrational x
参数：h : Irrational (q / x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irrational.of_inv`：of_inv (h : Irrational x⁻¹) : Irrational x
· 使用定理 `Irrational.of_ratCast_mul`：of_ratCast_mul : Irrational (q * x) -> Irrati
onal x
-/
theorem of_ratCast_div (h : Irrational (q / x)) : Irrational x :=
  (h.of_ratCast_mul q).of_inv
/-
**Irrational.of_div_ratCast** 是 Mathlib 中的一个定理，位于命名空间 `Irrational`。
形式化陈述：of_div_ratCast (h : Irrational (x / q)) : Irrational x
参数：h : Irrational (x / q)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `Irrational.div_cases`：div_cases (h : Irrational (x / y)) : Irrational x 
∨ Irrational y
· 使用定理 `Rat.not_irrational`：Rat.not_irrational (q : Rat) : ¬Irrational q
-/
theorem of_div_ratCast (h : Irrational (x / q)) : Irrational x :=
  h.div_cases.resolve_right q.not_irrational
/-
**Irrational.ratCast_div** 是 Mathlib 中的一个定理，位于命名空间 `Irrational`。
形式化陈述：ratCast_div (h : Irrational x) {q : Rat} (hq : q != 0) : Irrational (q / x
)
参数：h : Irrational x；hq : q != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irrational.ratCast_mul`：ratCast_mul (h : Irrational x) {q : Rat} (hq : q
 != 0) : Irrational (q * x)
· 使用定理 `Irrational.inv`：∀ {x : ℝ}, Irrational x → Irrational x⁻¹
-/
theorem ratCast_div (h : Irrational x) {q : ℚ} (hq : q ≠ 0) : Irrational (q / x) :=
  h.inv.ratCast_mul hq
/-
**Irrational.div_ratCast** 是 Mathlib 中的一个定理，位于命名空间 `Irrational`。
形式化陈述：div_ratCast (h : Irrational x) {q : Rat} (hq : q != 0) : Irrational (x / q
)
参数：h : Irrational x；hq : q != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.cast_inv`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p :
 ℚ), ↑p⁻¹ = (↑p)⁻¹
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Irrational.mul_ratCast`：mul_ratCast (h : Irrational x) {q : Rat} (hq : q
 != 0) : Irrational (x * q)
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
-/
theorem div_ratCast (h : Irrational x) {q : ℚ} (hq : q ≠ 0) : Irrational (x / q) := by
  rw [div_eq_mul_inv, ← cast_inv]
  exact h.mul_ratCast (inv_ne_zero hq)
/-
**Irrational.of_intCast_div** 是 Mathlib 中的一个定理，位于命名空间 `Irrational`。
形式化陈述：of_intCast_div (m : Int) (h : Irrational (m / x)) : Irrational x
参数：m : Int；h : Irrational (m / x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Irrational.div_cases`：div_cases (h : Irrational (x / y)) : Irrational x 
∨ Irrational y
· 使用定理 `Int.not_irrational`：Int.not_irrational (m : Int) : ¬Irrational m
-/
theorem of_intCast_div (m : ℤ) (h : Irrational (m / x)) : Irrational x :=
  h.div_cases.resolve_left m.not_irrational
/-
**Irrational.of_div_intCast** 是 Mathlib 中的一个定理，位于命名空间 `Irrational`。
形式化陈述：of_div_intCast (m : Int) (h : Irrational (x / m)) : Irrational x
参数：m : Int；h : Irrational (x / m)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `Irrational.div_cases`：div_cases (h : Irrational (x / y)) : Irrational x 
∨ Irrational y
· 使用定理 `Int.not_irrational`：Int.not_irrational (m : Int) : ¬Irrational m
-/
theorem of_div_intCast (m : ℤ) (h : Irrational (x / m)) : Irrational x :=
  h.div_cases.resolve_right m.not_irrational
/-
**Irrational.intCast_div** 是 Mathlib 中的一个定理，位于命名空间 `Irrational`。
形式化陈述：intCast_div (h : Irrational x) {m : Int} (hm : m != 0) : Irrational (m / x
)
参数：h : Irrational x；hm : m != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irrational.intCast_mul`：intCast_mul (h : Irrational x) {m : Int} (hm : m
 != 0) : Irrational (m * x)
· 使用定理 `Irrational.inv`：∀ {x : ℝ}, Irrational x → Irrational x⁻¹
-/
theorem intCast_div (h : Irrational x) {m : ℤ} (hm : m ≠ 0) : Irrational (m / x) :=
  h.inv.intCast_mul hm
/-
**Irrational.div_intCast** 是 Mathlib 中的一个定理，位于命名空间 `Irrational`。
形式化陈述：div_intCast (h : Irrational x) {m : Int} (hm : m != 0) : Irrational (x / m
)
参数：h : Irrational x；hm : m != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.cast_intCast`：cast_intCast (n : Int) : ((n : Rat) : α) = n
· 使用定理 `Irrational.div_ratCast`：div_ratCast (h : Irrational x) {q : Rat} (hq : q
 != 0) : Irrational (x / q)
· 使用引理 `Int.cast_ne_zero`：cast_ne_zero : (n : α) != 0 ↔ n != 0
-/
theorem div_intCast (h : Irrational x) {m : ℤ} (hm : m ≠ 0) : Irrational (x / m) := by
  rw [← cast_intCast]
  refine h.div_ratCast ?_
  rwa [Int.cast_ne_zero]
/-
**Irrational.of_natCast_div** 是 Mathlib 中的一个定理，位于命名空间 `Irrational`。
形式化陈述：of_natCast_div (m : Nat) (h : Irrational (m / x)) : Irrational x
参数：m : Nat；h : Irrational (m / x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irrational.of_intCast_div`：of_intCast_div (m : Int) (h : Irrational (m /
 x)) : Irrational x
-/
theorem of_natCast_div (m : ℕ) (h : Irrational (m / x)) : Irrational x :=
  h.of_intCast_div m
/-
**Irrational.of_div_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Irrational`。
形式化陈述：of_div_natCast (m : Nat) (h : Irrational (x / m)) : Irrational x
参数：m : Nat；h : Irrational (x / m)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irrational.of_div_intCast`：of_div_intCast (m : Int) (h : Irrational (x /
 m)) : Irrational x
-/
theorem of_div_natCast (m : ℕ) (h : Irrational (x / m)) : Irrational x :=
  h.of_div_intCast m
/-
**Irrational.natCast_div** 是 Mathlib 中的一个定理，位于命名空间 `Irrational`。
形式化陈述：natCast_div (h : Irrational x) {m : Nat} (hm : m != 0) : Irrational (m / x
)
参数：h : Irrational x；hm : m != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irrational.natCast_mul`：natCast_mul (h : Irrational x) {m : Nat} (hm : m
 != 0) : Irrational (m * x)
· 使用定理 `Irrational.inv`：∀ {x : ℝ}, Irrational x → Irrational x⁻¹
-/
theorem natCast_div (h : Irrational x) {m : ℕ} (hm : m ≠ 0) : Irrational (m / x) :=
  h.inv.natCast_mul hm
/-
**Irrational.div_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Irrational`。
形式化陈述：div_natCast (h : Irrational x) {m : Nat} (hm : m != 0) : Irrational (x / m
)
参数：h : Irrational x；hm : m != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irrational.div_intCast`：div_intCast (h : Irrational x) {m : Int} (hm : m
 != 0) : Irrational (x / m)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.natCast_ne_zero`：∀ {n : ℕ}, ↑n ≠ 0 ↔ n ≠ 0
-/
theorem div_natCast (h : Irrational x) {m : ℕ} (hm : m ≠ 0) : Irrational (x / m) :=
  h.div_intCast <| by rwa [Int.natCast_ne_zero]
/-
**Irrational.of_one_div** 是 Mathlib 中的一个定理，位于命名空间 `Irrational`。
形式化陈述：of_one_div (h : Irrational (1 / x)) : Irrational x
参数：h : Irrational (1 / x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irrational.of_ratCast_div`：of_ratCast_div (h : Irrational (q / x)) : Irr
ational x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.cast_one`：cast_one : ((1 : Rat) : α) = 1
-/
theorem of_one_div (h : Irrational (1 / x)) : Irrational x :=
  of_ratCast_div 1 <| by rwa [cast_one]

/-!
#### Natural and integer power
-/


/-
**Irrational.of_mul_self** 是 Mathlib 中的一个定理，位于命名空间 `Irrational`。
形式化陈述：of_mul_self (h : Irrational (x * x)) : Irrational x
参数：h : Irrational (x * x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Irrational.mul_cases`：mul_cases : Irrational (x * y) -> Irrational x ∨ I
rrational y

--- 原说明 ---
#### Natural and integer power
-/
theorem of_mul_self (h : Irrational (x * x)) : Irrational x :=
  h.mul_cases.elim id id
/-
**Irrational.of_pow** 是 Mathlib 中的一个定理，位于命名空间 `Irrational`。
形式化陈述：∀ {x : ℝ} (n : ℕ), Irrational (x ^ n) → Irrational x
参数：n : ℕ；x ^ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem of_pow : ∀ n : ℕ, Irrational (x ^ n) → Irrational x
  | 0 => fun h => by
    rw [pow_zero] at h
    exact (h ⟨1, cast_one⟩).elim
  | n + 1 => fun h => by
    rw [pow_succ] at h
    exact h.mul_cases.elim (of_pow n) id

open Int in
/-
**Irrational.of_zpow** 是 Mathlib 中的一个定理，位于命名空间 `Irrational`。
形式化陈述：∀ {x : ℝ} (m : ℤ), Irrational (x ^ m) → Irrational x
参数：m : ℤ；x ^ m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irrational.of_pow`：∀ {x : ℝ} (n : ℕ), Irrational (x ^ n) → Irrational x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `Irrational.of_inv`：of_inv (h : Irrational x⁻¹) : Irrational x
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
-/
theorem of_zpow : ∀ m : ℤ, Irrational (x ^ m) → Irrational x
  | (n : ℕ) => fun h => by
    rw [zpow_natCast] at h
    exact h.of_pow _
  | -[n+1] => fun h => by
    rw [zpow_negSucc] at h
    exact h.of_inv.of_pow _

end Irrational

section Polynomial

open Polynomial

variable (x : ℝ) (p : ℤ[X])

/-
**one_lt_natDegree_of_irrational_root** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：one_lt_natDegree_of_irrational_root (hx : Irrational x) (p_nonzero : p != 
0) (x_is_root : aeval x p = 0) : 1 < p.natDegree
参数：hx : Irrational x；p_nonzero : p != 0；x_is_root : aeval x p = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Polynomial.exists_eq_X_add_C_of_natDegree_le_one`：exists_eq_X_add_C_of_n
atDegree_le_one (h : natDegree p <= 1) : exists a b, p = C a * X + C b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_intCast`：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) 
(n : Int) : f n = n
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `map_intCast`：map_intCast [FunLike F α β] [RingHomClass F α β] (f : F) (n
 : Int) : f n = n
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用引理 `eq_div_iff_mul_eq`：eq_div_iff_mul_eq (hc : c != 0) : a = b / c ↔ a * c =
 b
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem one_lt_natDegree_of_irrational_root (hx : Irrational x) (p_nonzero : p ≠ 0)
    (x_is_root : aeval x p = 0) : 1 < p.natDegree := by
  by_contra rid
  rcases exists_eq_X_add_C_of_natDegree_le_one (not_lt.1 rid) with ⟨a, b, rfl⟩
  clear rid
  have : (a : ℝ) * x = -b := by simpa [eq_neg_iff_add_eq_zero] using x_is_root
  rcases em (a = 0) with (rfl | ha)
  · obtain rfl : b = 0 := by simpa
    simp at p_nonzero
  · rw [mul_comm, ← eq_div_iff_mul_eq, eq_comm] at this
    · refine hx ⟨-b / a, ?_⟩
      assumption_mod_cast
    · assumption_mod_cast

end Polynomial

section

variable {q : ℚ} {m : ℤ} {n : ℕ} {x : ℝ}

open Irrational

/-!
### Simplification lemmas about operations
-/


@[simp]
/-
**irrational_ratCast_add_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：irrational_ratCast_add_iff : Irrational (q + x) ↔ Irrational x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irrational.of_ratCast_add`：of_ratCast_add (h : Irrational (q + x)) : Irr
ational x
· 使用定理 `Irrational.ratCast_add`：ratCast_add (h : Irrational x) : Irrational (q +
 x)

--- 原说明 ---
### Simplification lemmas about operations
-/
theorem irrational_ratCast_add_iff : Irrational (q + x) ↔ Irrational x :=
  ⟨of_ratCast_add q, ratCast_add q⟩
@[simp]
/-
**irrational_intCast_add_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：irrational_intCast_add_iff : Irrational (m + x) ↔ Irrational x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irrational.of_intCast_add`：of_intCast_add (m : Int) (h : Irrational (m +
 x)) : Irrational x
· 使用定理 `Irrational.intCast_add`：intCast_add (h : Irrational x) (m : Int) : Irrat
ional (m + x)
-/
theorem irrational_intCast_add_iff : Irrational (m + x) ↔ Irrational x :=
  ⟨of_intCast_add m, fun h => h.intCast_add m⟩
@[simp]
/-
**irrational_natCast_add_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：irrational_natCast_add_iff : Irrational (n + x) ↔ Irrational x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irrational.of_natCast_add`：of_natCast_add (m : Nat) (h : Irrational (m +
 x)) : Irrational x
· 使用定理 `Irrational.natCast_add`：natCast_add (h : Irrational x) (m : Nat) : Irrat
ional (m + x)
-/
theorem irrational_natCast_add_iff : Irrational (n + x) ↔ Irrational x :=
  ⟨of_natCast_add n, fun h => h.natCast_add n⟩
@[simp]
/-
**irrational_add_ratCast_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：irrational_add_ratCast_iff : Irrational (x + q) ↔ Irrational x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irrational.of_add_ratCast`：of_add_ratCast : Irrational (x + q) -> Irrati
onal x
· 使用定理 `Irrational.add_ratCast`：add_ratCast (h : Irrational x) : Irrational (x +
 q)
-/
theorem irrational_add_ratCast_iff : Irrational (x + q) ↔ Irrational x :=
  ⟨of_add_ratCast q, add_ratCast q⟩
@[simp]
/-
**irrational_add_intCast_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：irrational_add_intCast_iff : Irrational (x + m) ↔ Irrational x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irrational.of_add_intCast`：of_add_intCast (m : Int) (h : Irrational (x +
 m)) : Irrational x
· 使用定理 `Irrational.add_intCast`：add_intCast (h : Irrational x) (m : Int) : Irrat
ional (x + m)
-/
theorem irrational_add_intCast_iff : Irrational (x + m) ↔ Irrational x :=
  ⟨of_add_intCast m, fun h => h.add_intCast m⟩
@[simp]
/-
**irrational_add_natCast_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：irrational_add_natCast_iff : Irrational (x + n) ↔ Irrational x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irrational.of_add_natCast`：of_add_natCast (m : Nat) (h : Irrational (x +
 m)) : Irrational x
· 使用定理 `Irrational.add_natCast`：add_natCast (h : Irrational x) (m : Nat) : Irrat
ional (x + m)
-/
theorem irrational_add_natCast_iff : Irrational (x + n) ↔ Irrational x :=
  ⟨of_add_natCast n, fun h => h.add_natCast n⟩
@[simp]
/-
**irrational_ratCast_sub_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：irrational_ratCast_sub_iff : Irrational (q - x) ↔ Irrational x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irrational.of_ratCast_sub`：of_ratCast_sub (h : Irrational (q - x)) : Irr
ational x
· 使用定理 `Irrational.ratCast_sub`：ratCast_sub (h : Irrational x) : Irrational (q -
 x)
-/
theorem irrational_ratCast_sub_iff : Irrational (q - x) ↔ Irrational x :=
  ⟨of_ratCast_sub q, ratCast_sub q⟩
@[simp]
/-
**irrational_intCast_sub_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：irrational_intCast_sub_iff : Irrational (m - x) ↔ Irrational x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irrational.of_intCast_sub`：of_intCast_sub (m : Int) (h : Irrational (m -
 x)) : Irrational x
· 使用定理 `Irrational.intCast_sub`：intCast_sub (h : Irrational x) (m : Int) : Irrat
ional (m - x)
-/
theorem irrational_intCast_sub_iff : Irrational (m - x) ↔ Irrational x :=
  ⟨of_intCast_sub m, fun h => h.intCast_sub m⟩
@[simp]
/-
**irrational_natCast_sub_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：irrational_natCast_sub_iff : Irrational (n - x) ↔ Irrational x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irrational.of_natCast_sub`：of_natCast_sub (m : Nat) (h : Irrational (m -
 x)) : Irrational x
· 使用定理 `Irrational.natCast_sub`：natCast_sub (h : Irrational x) (m : Nat) : Irrat
ional (m - x)
-/
theorem irrational_natCast_sub_iff : Irrational (n - x) ↔ Irrational x :=
  ⟨of_natCast_sub n, fun h => h.natCast_sub n⟩
@[simp]
/-
**irrational_sub_ratCast_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：irrational_sub_ratCast_iff : Irrational (x - q) ↔ Irrational x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irrational.of_sub_ratCast`：of_sub_ratCast (h : Irrational (x - q)) : Irr
ational x
· 使用定理 `Irrational.sub_ratCast`：sub_ratCast (h : Irrational x) : Irrational (x -
 q)
-/
theorem irrational_sub_ratCast_iff : Irrational (x - q) ↔ Irrational x :=
  ⟨of_sub_ratCast q, sub_ratCast q⟩
@[simp]
/-
**irrational_sub_intCast_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：irrational_sub_intCast_iff : Irrational (x - m) ↔ Irrational x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irrational.of_sub_intCast`：of_sub_intCast (m : Int) (h : Irrational (x -
 m)) : Irrational x
· 使用定理 `Irrational.sub_intCast`：sub_intCast (h : Irrational x) (m : Int) : Irrat
ional (x - m)
-/
theorem irrational_sub_intCast_iff : Irrational (x - m) ↔ Irrational x :=
  ⟨of_sub_intCast m, fun h => h.sub_intCast m⟩
@[simp]
/-
**irrational_sub_natCast_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：irrational_sub_natCast_iff : Irrational (x - n) ↔ Irrational x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irrational.of_sub_natCast`：of_sub_natCast (m : Nat) (h : Irrational (x -
 m)) : Irrational x
· 使用定理 `Irrational.sub_natCast`：sub_natCast (h : Irrational x) (m : Nat) : Irrat
ional (x - m)
-/
theorem irrational_sub_natCast_iff : Irrational (x - n) ↔ Irrational x :=
  ⟨of_sub_natCast n, fun h => h.sub_natCast n⟩
@[simp]
/-
**irrational_neg_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：irrational_neg_iff : Irrational (-x) ↔ Irrational x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irrational.of_neg`：of_neg (h : Irrational (-x)) : Irrational x
· 使用定理 `Irrational.neg`：∀ {x : ℝ}, Irrational x → Irrational (-x)
-/
theorem irrational_neg_iff : Irrational (-x) ↔ Irrational x :=
  ⟨of_neg, Irrational.neg⟩

@[simp]
/-
**irrational_inv_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：irrational_inv_iff : Irrational x⁻¹ ↔ Irrational x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irrational.of_inv`：of_inv (h : Irrational x⁻¹) : Irrational x
· 使用定理 `Irrational.inv`：∀ {x : ℝ}, Irrational x → Irrational x⁻¹
-/
theorem irrational_inv_iff : Irrational x⁻¹ ↔ Irrational x :=
  ⟨of_inv, Irrational.inv⟩

@[simp]
/-
**irrational_ratCast_mul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：irrational_ratCast_mul_iff : Irrational (q * x) ↔ q != 0 ∧ Irrational x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Rat.cast_ne_zero`：cast_ne_zero : (p : α) != 0 ↔ p != 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `left_ne_zero_of_mul`：left_ne_zero_of_mul : a * b != 0 -> a != 0
· 使用定理 `Irrational.ne_zero`：ne_zero (h : Irrational x) : x != 0
· 使用定理 `Irrational.of_ratCast_mul`：of_ratCast_mul : Irrational (q * x) -> Irrati
onal x
· 使用定理 `Irrational.ratCast_mul`：ratCast_mul (h : Irrational x) {q : Rat} (hq : q
 != 0) : Irrational (q * x)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem irrational_ratCast_mul_iff : Irrational (q * x) ↔ q ≠ 0 ∧ Irrational x :=
  ⟨fun h => ⟨Rat.cast_ne_zero.1 <| left_ne_zero_of_mul h.ne_zero, h.of_ratCast_mul q⟩, fun h =>
    h.2.ratCast_mul h.1⟩
@[simp]
/-
**irrational_mul_ratCast_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：irrational_mul_ratCast_iff : Irrational (x * q) ↔ q != 0 ∧ Irrational x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `irrational_ratCast_mul_iff`：irrational_ratCast_mul_iff : Irrational (q *
 x) ↔ q != 0 ∧ Irrational x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem irrational_mul_ratCast_iff : Irrational (x * q) ↔ q ≠ 0 ∧ Irrational x := by
  rw [mul_comm, irrational_ratCast_mul_iff]
@[simp]
/-
**irrational_intCast_mul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：irrational_intCast_mul_iff : Irrational (m * x) ↔ m != 0 ∧ Irrational x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.cast_intCast`：cast_intCast (n : Int) : ((n : Rat) : α) = n
· 使用定理 `irrational_ratCast_mul_iff`：irrational_ratCast_mul_iff : Irrational (q *
 x) ↔ q != 0 ∧ Irrational x
· 使用引理 `Int.cast_ne_zero`：cast_ne_zero : (n : α) != 0 ↔ n != 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem irrational_intCast_mul_iff : Irrational (m * x) ↔ m ≠ 0 ∧ Irrational x := by
  rw [← cast_intCast, irrational_ratCast_mul_iff, Int.cast_ne_zero]
@[simp]
/-
**irrational_mul_intCast_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：irrational_mul_intCast_iff : Irrational (x * m) ↔ m != 0 ∧ Irrational x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.cast_intCast`：cast_intCast (n : Int) : ((n : Rat) : α) = n
· 使用定理 `irrational_mul_ratCast_iff`：irrational_mul_ratCast_iff : Irrational (x *
 q) ↔ q != 0 ∧ Irrational x
· 使用引理 `Int.cast_ne_zero`：cast_ne_zero : (n : α) != 0 ↔ n != 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem irrational_mul_intCast_iff : Irrational (x * m) ↔ m ≠ 0 ∧ Irrational x := by
  rw [← cast_intCast, irrational_mul_ratCast_iff, Int.cast_ne_zero]
@[simp]
/-
**irrational_natCast_mul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：irrational_natCast_mul_iff : Irrational (n * x) ↔ n != 0 ∧ Irrational x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.cast_natCast`：cast_natCast (n : Nat) : ((n : Rat) : α) = n
· 使用定理 `irrational_ratCast_mul_iff`：irrational_ratCast_mul_iff : Irrational (q *
 x) ↔ q != 0 ∧ Irrational x
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem irrational_natCast_mul_iff : Irrational (n * x) ↔ n ≠ 0 ∧ Irrational x := by
  rw [← cast_natCast, irrational_ratCast_mul_iff, Nat.cast_ne_zero]
@[simp]
/-
**irrational_mul_natCast_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：irrational_mul_natCast_iff : Irrational (x * n) ↔ n != 0 ∧ Irrational x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.cast_natCast`：cast_natCast (n : Nat) : ((n : Rat) : α) = n
· 使用定理 `irrational_mul_ratCast_iff`：irrational_mul_ratCast_iff : Irrational (x *
 q) ↔ q != 0 ∧ Irrational x
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem irrational_mul_natCast_iff : Irrational (x * n) ↔ n ≠ 0 ∧ Irrational x := by
  rw [← cast_natCast, irrational_mul_ratCast_iff, Nat.cast_ne_zero]
@[simp]
/-
**irrational_ratCast_div_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：irrational_ratCast_div_iff : Irrational (q / x) ↔ q != 0 ∧ Irrational x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem irrational_ratCast_div_iff : Irrational (q / x) ↔ q ≠ 0 ∧ Irrational x := by
  simp [div_eq_mul_inv]
@[simp]
/-
**irrational_div_ratCast_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：irrational_div_ratCast_iff : Irrational (x / q) ↔ q != 0 ∧ Irrational x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.cast_inv`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p :
 ℚ), ↑p⁻¹ = (↑p)⁻¹
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `irrational_mul_ratCast_iff`：irrational_mul_ratCast_iff : Irrational (x *
 q) ↔ q != 0 ∧ Irrational x
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `inv_eq_zero`：inv_eq_zero {a : G₀} : a⁻¹ = 0 ↔ a = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem irrational_div_ratCast_iff : Irrational (x / q) ↔ q ≠ 0 ∧ Irrational x := by
  rw [div_eq_mul_inv, ← cast_inv, irrational_mul_ratCast_iff, Ne, inv_eq_zero]
@[simp]
/-
**irrational_intCast_div_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：irrational_intCast_div_iff : Irrational (m / x) ↔ m != 0 ∧ Irrational x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem irrational_intCast_div_iff : Irrational (m / x) ↔ m ≠ 0 ∧ Irrational x := by
  simp [div_eq_mul_inv]
@[simp]
/-
**irrational_div_intCast_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：irrational_div_intCast_iff : Irrational (x / m) ↔ m != 0 ∧ Irrational x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.cast_intCast`：cast_intCast (n : Int) : ((n : Rat) : α) = n
· 使用定理 `irrational_div_ratCast_iff`：irrational_div_ratCast_iff : Irrational (x /
 q) ↔ q != 0 ∧ Irrational x
· 使用引理 `Int.cast_ne_zero`：cast_ne_zero : (n : α) != 0 ↔ n != 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem irrational_div_intCast_iff : Irrational (x / m) ↔ m ≠ 0 ∧ Irrational x := by
  rw [← cast_intCast, irrational_div_ratCast_iff, Int.cast_ne_zero]
@[simp]
/-
**irrational_natCast_div_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：irrational_natCast_div_iff : Irrational (n / x) ↔ n != 0 ∧ Irrational x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem irrational_natCast_div_iff : Irrational (n / x) ↔ n ≠ 0 ∧ Irrational x := by
  simp [div_eq_mul_inv]
@[simp]
/-
**irrational_div_natCast_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：irrational_div_natCast_iff : Irrational (x / n) ↔ n != 0 ∧ Irrational x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.cast_natCast`：cast_natCast (n : Nat) : ((n : Rat) : α) = n
· 使用定理 `irrational_div_ratCast_iff`：irrational_div_ratCast_iff : Irrational (x /
 q) ↔ q != 0 ∧ Irrational x
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem irrational_div_natCast_iff : Irrational (x / n) ↔ n ≠ 0 ∧ Irrational x := by
  rw [← cast_natCast, irrational_div_ratCast_iff, Nat.cast_ne_zero]
/-- There is an irrational number `r` between any two reals `x < r < y`. -/
/-
**exists_irrational_btwn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_irrational_btwn {x y : Real} (h : x < y) : exists r, Irrational r ∧
 x < r ∧ r < y
参数：h : x < y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `exists_rat_btwn`：exists_rat_btwn {x y : K} (h : x < y) : exists q : Rat,
 x < q ∧ q < y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_lt_sub_iff_right`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α]
 [AddRightStrictMono α] {a b : α} (c : α), a - c < b - c ↔ a < b
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
· 使用定理 `Irrational.ratCast_add`：ratCast_add (h : Irrational x) : Irrational (q +
 x)
· 使用定理 `irrational_sqrt_two`：irrational_sqrt_two : Irrational (√2)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sub_lt_iff_lt_add`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [A
ddRightStrictMono α] {a b c : α}, a - c < b ↔ a < b + c
· 使用定理 `lt_sub_iff_add_lt`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [A
ddRightStrictMono α] {a b c : α}, a < c - b ↔ a + b < c

--- 原说明 ---
There is an irrational number `r` between any two reals `x < r < y`.
-/
theorem exists_irrational_btwn {x y : ℝ} (h : x < y) : ∃ r, Irrational r ∧ x < r ∧ r < y :=
  let ⟨q, ⟨hq1, hq2⟩⟩ := exists_rat_btwn ((sub_lt_sub_iff_right (√2)).mpr h)
  ⟨q + √2, irrational_sqrt_two.ratCast_add _, sub_lt_iff_lt_add.mp hq1, lt_sub_iff_add_lt.mp hq2⟩

end

