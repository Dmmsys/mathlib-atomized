/-
Copyright (c) 2024 Antoine Chambert-Loir & María-Inés de Frutos—Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María-Inés de Frutos—Fernández
-/
module

public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Combinatorics.Enumerative.Bell
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.RingTheory.Ideal.Maps

/-! # Divided powers

Let `A` be a commutative (semi)ring and `I` be an ideal of `A`.
A *divided power* structure on `I` is the datum of operations `a n ↦ dpow a n`
satisfying relations that model the intuitive formula `dpow n a = a ^ n / n !` and
collected by the structure `DividedPowers`. The list of axioms is embedded in the structure:
To avoid coercions, we rather consider `DividedPowers.dpow : ℕ → A → A`, extended by 0.

* `DividedPowers.dpow_null` asserts that `dpow n x = 0` for `x ∉ I`
* `DividedPowers.dpow_mem` : `dpow n x ∈ I` for `n ≠ 0`

For `x y : A` and `m n : ℕ` such that `x ∈ I` and `y ∈ I`, one has
* `DividedPowers.dpow_zero` : `dpow 0 x = 1`
* `DividedPowers.dpow_one` : `dpow 1 x = 1`
* `DividedPowers.dpow_add` :
  `dpow n (x + y) = (antidiagonal n).sum fun k ↦ dpow k.1 x * dpow k.2 y`,
  this is the binomial theorem without binomial coefficients.
* `DividedPowers.dpow_mul`: `dpow n (a * x) = a ^ n * dpow n x`
* `DividedPowers.mul_dpow` : `dpow m x * dpow n x = choose (m + n) m * dpow (m + n) x`
* `DividedPowers.dpow_comp` : `dpow m (dpow n x) = uniformBell m n * dpow (m * n) x`
* `DividedPowers.dividedPowersBot` : the trivial divided powers structure on the zero ideal
* `DividedPowers.prod_dpow`: a product of divided powers is a multinomial coefficient
  times a divided power
* `DividedPowers.dpow_sum`: the multinomial theorem for divided powers,
  without multinomial coefficients.
* `DividedPowers.ofRingEquiv`: transfer divided powers along `RingEquiv`
* `DividedPowers.equiv`: the equivalence `DividedPowers I ≃ DividedPowers J`,
  for `e : R ≃+* S`, and `I : Ideal R`, `J : Ideal S` such that `I.map e = J`
* `DividedPowers.exp`: the power series `Σ (dpow n a) X ^n`
* `DividedPowers.exp_add`: its multiplicativity

## References

* [P. Berthelot (1974), *Cohomologie cristalline des schémas de
  caractéristique $p$ > 0*][Berthelot-1974]

* [P. Berthelot and A. Ogus (1978), *Notes on crystalline
  cohomology*][BerthelotOgus-1978]

* [N. Roby (1963), *Lois polynomes et lois formelles en théorie des
  modules*][Roby-1963]

* [N. Roby (1965), *Les algèbres à puissances dividées*][Roby-1965]

## Discussion

* In practice, one often has a single such structure to handle on a given ideal,
  but several ideals of the same ring might be considered.
  Without any explicit mention of the ideal, it is not clear whether such structures
  should be provided as instances.

* We do not provide any notation such as `a ^[n]` for `dpow a n`.

-/

@[expose] public section

open Finset Nat Ideal

section DividedPowersDefinition
/- ## Definition of divided powers -/

variable {A : Type*} [CommSemiring A] (I : Ideal A)

/--
Definition of `DividedPowers` / `DividedPowers` 的定义

English:
structure DividedPowers
  parameters: where
  axioms and operations (9):
    - dpow : Nat -> A -> A
    - dpow_null : forall {n x} (_ : x ∉ I), dpow n x = 0
    - dpow_zero : forall {x} (_ : x in I), dpow 0 x = 1
    - dpow_one : forall {x} (_ : x in I), dpow 1 x = x
    - dpow_mem : forall {n x} (_ : n != 0) (_ : x in I), dpow n x in I
    - dpow_add : forall {n} {x y} (_ : x in I) (_ : y in I), dpow n (x + y) = (antidiagonal n).sum fun k => dpow k.1 x * dpow k.2 y
    - dpow_mul : forall {n} {a : A} {x} (_ : x in I), dpow n (a * x) = a ^ n * dpow n x
    - mul_dpow : forall {m n} {x} (_ : x in I), dpow m x * dpow n x = choose (m + n) m * dpow (m + n) x
    - dpow_comp : forall {m n x} (_ : n != 0) (_ : x in I), dpow m (dpow n x) = uniformBell m n * dpow (m * n) x

中文:
结构 DividedPowers
  参数: where
  公理与运算 (9 个):
    - dpow : 自然数 -> A -> A
    - dpow_null : 对任意 {n x} (_ : x ∉ I), dpow n x = 0
    - dpow_zero : 对任意 {x} (_ : x in I), dpow 0 x = 1
    - dpow_one : 对任意 {x} (_ : x in I), dpow 1 x = x
    - dpow_mem : 对任意 {n x} (_ : n != 0) (_ : x in I), dpow n x in I
    - dpow_add : 对任意 {n} {x y} (_ : x in I) (_ : y in I), dpow n (x + y) = (antidiagonal n).求和 fun k => dpow k.1 x * dpow k.2 y
    - dpow_mul : 对任意 {n} {a : A} {x} (_ : x in I), dpow n (a * x) = a ^ n * dpow n x
    - mul_dpow : 对任意 {m n} {x} (_ : x in I), dpow m x * dpow n x = choose (m + n) m * dpow (m + n) x
    - dpow_comp : 对任意 {m n x} (_ : n != 0) (_ : x in I), dpow m (dpow n x) = uniformBell m n * dpow (m * n) x
-/
structure DividedPowers where
  /-- The divided power function underlying a divided power structure -/
  dpow : Nat -> A -> A
  dpow_null : forall {n x} (_ : x ∉ I), dpow n x = 0
  dpow_zero : forall {x} (_ : x in I), dpow 0 x = 1
  dpow_one : forall {x} (_ : x in I), dpow 1 x = x
  dpow_mem : forall {n x} (_ : n != 0) (_ : x in I), dpow n x in I
  dpow_add : forall {n} {x y} (_ : x in I) (_ : y in I),
    dpow n (x + y) = (antidiagonal n).sum fun k => dpow k.1 x * dpow k.2 y
  dpow_mul : forall {n} {a : A} {x} (_ : x in I),
    dpow n (a * x) = a ^ n * dpow n x
  mul_dpow : forall {m n} {x} (_ : x in I),
    dpow m x * dpow n x = choose (m + n) m * dpow (m + n) x
  dpow_comp : forall {m n x} (_ : n != 0) (_ : x in I),
    dpow m (dpow n x) = uniformBell m n * dpow (m * n) x

variable (A) in
/--
Definition of `dividedPowersBot` / `dividedPowersBot` 的定义

English:
definition dividedPowersBot
  signature: : DividedPowers (⊥ : Ideal A) where
  body: open scoped Classical in ite (a = 0 ∧ n = 0) 1 0
  dpow_null {n a} ha := by
    simp only [mem_bot] at ha
    rw [if_neg]
    exact not_and_of_not_left (n = 0) ha
  dpow_zero ha := by
    rw [mem_bot.mp ha]
    simp only [and_self, ite_true]
  dpow_one ha := by
    simp [mem_bot.mp ha]
  dpow_mem {n a} hn _ := by
    simp only [mem_bot, ite_eq_right_iff, and_imp]
    exact fun _ a => False.elim (hn a)
  dpow_add ha hb := by
    rw [mem_bot.mp ha]; rw [mem_bot.mp hb]; rw [add_zero]
    simp only [true_and, mul_ite, mul_one, mul_zero]
    split_ifs with h
    · simp [h]
    · symm
      apply sum_eq_zero
      grind [mem_antidiagonal]
  dpow_mul {n} _ _ hx := by
    rw [mem_bot.mp hx]
    simp only [mul_zero, true_and, mul_ite, mul_one]
    by_cases hn : n = 0
    · rw [if_pos hn, hn, if_pos rfl, _root_.pow_zero]
    · simp only [if_neg hn]
  mul_dpow {m n x} hx := by
    rw [mem_bot.mp hx]
    simp only [true_and, mul_ite, mul_one, mul_zero, add_eq_zero]
    by_cases hn : n = 0
    · simp only [hn, ite_true, and_true, add_zero, choose_self, cast_one]
    · rw [if_neg hn, if_neg]
      exact not_and_of_not_right (m = 0) hn
  dpow_comp m {n a} hn ha := by
    rw [mem_bot.mp ha]
    simp only [true_and, ite_eq_right_iff, _root_.mul_eq_zero, mul_ite, mul_one, mul_zero]
    by_cases hm : m = 0
    · simp [hm, uniformBell_zero_left, hn]
    · simp only [hm, and_false, ite_false, false_or, if_neg hn]

中文:
定义 dividedPowersBot
  签名: : DividedPowers (⊥ : 理想 A) where
  定义体: open scoped Classical in ite (a = 0 ∧ n = 0) 1 0
  dpow_null {n a} ha := by
    simp only [mem_bot] at ha
    rw [if_neg]
    exact not_and_of_not_left (n = 0) ha
  dpow_zero ha := by
    rw [mem_bot.mp ha]
    simp only [and_self, ite_true]
  dpow_one ha := by
    simp [mem_bot.mp ha]
  dpow_mem {n a} hn _ := by
    simp only [mem_bot, ite_eq_right_iff, and_imp]
    exact fun _ a => False.elim (hn a)
  dpow_add ha hb := by
    rw [mem_bot.mp ha]; rw [mem_bot.mp hb]; rw [add_zero]
    simp only [true_and, mul_ite, mul_one, mul_zero]
    split_ifs with h
    · simp [h]
    · symm
      apply sum_eq_zero
      grind [mem_antidiagonal]
  dpow_mul {n} _ _ hx := by
    rw [mem_bot.mp hx]
    simp only [mul_zero, true_and, mul_ite, mul_one]
    by_cases hn : n = 0
    · rw [if_pos hn, hn, if_pos rfl, _root_.pow_zero]
    · simp only [if_neg hn]
  mul_dpow {m n x} hx := by
    rw [mem_bot.mp hx]
    simp only [true_and, mul_ite, mul_one, mul_zero, add_eq_zero]
    by_cases hn : n = 0
    · simp only [hn, ite_true, and_true, add_zero, choose_self, cast_one]
    · rw [if_neg hn, if_neg]
      exact not_and_of_not_right (m = 0) hn
  dpow_comp m {n a} hn ha := by
    rw [mem_bot.mp ha]
    simp only [true_and, ite_eq_right_iff, _root_.mul_eq_zero, mul_ite, mul_one, mul_zero]
    by_cases hm : m = 0
    · simp [hm, uniformBell_zero_left, hn]
    · simp only [hm, and_false, ite_false, false_or, if_neg hn]

Depends on / 依赖: Classical, scoped
-/
noncomputable def dividedPowersBot : DividedPowers (⊥ : Ideal A) where
  dpow n a := open scoped Classical in ite (a = 0 ∧ n = 0) 1 0
  dpow_null {n a} ha := by
    simp only [mem_bot] at ha
    rw [if_neg]
    exact not_and_of_not_left (n = 0) ha
  dpow_zero ha := by
    rw [mem_bot.mp ha]
    simp only [and_self, ite_true]
  dpow_one ha := by
    simp [mem_bot.mp ha]
  dpow_mem {n a} hn _ := by
    simp only [mem_bot, ite_eq_right_iff, and_imp]
    exact fun _ a => False.elim (hn a)
  dpow_add ha hb := by
    rw [mem_bot.mp ha]; rw [mem_bot.mp hb]; rw [add_zero]
    simp only [true_and, mul_ite, mul_one, mul_zero]
    split_ifs with h
    · simp [h]
    · symm
      apply sum_eq_zero
      grind [mem_antidiagonal]
  dpow_mul {n} _ _ hx := by
    rw [mem_bot.mp hx]
    simp only [mul_zero, true_and, mul_ite, mul_one]
    by_cases hn : n = 0
    · rw [if_pos hn, hn, if_pos rfl, _root_.pow_zero]
    · simp only [if_neg hn]
  mul_dpow {m n x} hx := by
    rw [mem_bot.mp hx]
    simp only [true_and, mul_ite, mul_one, mul_zero, add_eq_zero]
    by_cases hn : n = 0
    · simp only [hn, ite_true, and_true, add_zero, choose_self, cast_one]
    · rw [if_neg hn, if_neg]
      exact not_and_of_not_right (m = 0) hn
  dpow_comp m {n a} hn ha := by
    rw [mem_bot.mp ha]
    simp only [true_and, ite_eq_right_iff, _root_.mul_eq_zero, mul_ite, mul_one, mul_zero]
    by_cases hm : m = 0
    · simp [hm, uniformBell_zero_left, hn]
    · simp only [hm, and_false, ite_false, false_or, if_neg hn]

/--
lemma `dividedPowersBot_dpow_eq` / 引理 `dividedPowersBot_dpow_eq`

English:
lemma dividedPowersBot_dpow_eq
  given: [DecidableEq A] (n : Nat) (a : A)
  proof: by
  simp [dividedPowersBot]

中文:
引理 dividedPowersBot_dpow_eq
  条件: [DecidableEq A] (n : 自然数) (a : A)
  证明: by
  simp [dividedPowersBot]

Depends on / 依赖: dividedPowersBot
-/
lemma dividedPowersBot_dpow_eq [DecidableEq A] (n : Nat) (a : A) :
    (dividedPowersBot A).dpow n a =
      if a = 0 ∧ n = 0 then 1 else 0 := by
  simp [dividedPowersBot]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (DividedPowers (⊥ : Ideal A))
  body: ⟨dividedPowersBot A⟩

中文:
实例 :
  签名: 可居 (DividedPowers (⊥ : 理想 A))
  定义体: ⟨dividedPowersBot A⟩
-/
noncomputable instance : Inhabited (DividedPowers (⊥ : Ideal A)) :=
  ⟨dividedPowersBot A⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeFun (DividedPowers I) fun _ => Nat -> A -> A
  body: ⟨fun hI => hI.dpow⟩

中文:
实例 :
  签名: CoeFun (DividedPowers I) fun _ => 自然数 -> A -> A
  定义体: ⟨fun hI => hI.dpow⟩
-/
instance : CoeFun (DividedPowers I) fun _ => Nat -> A -> A := ⟨fun hI => hI.dpow⟩

variable {I} in
@[ext]
/--
theorem `DividedPowers.ext` / 定理 `DividedPowers.ext`

English:
theorem DividedPowers.ext
  statement: (hI : DividedPowers I) (hI' : DividedPowers I)
  proof: by
  obtain ⟨hI, h₀, _⟩ := hI
  obtain ⟨hI', h₀', _⟩ := hI'
  simp only [mk.injEq]
  grind

中文:
定理 DividedPowers.ext
  结论: (hI : DividedPowers I) (hI' : DividedPowers I)
  证明: by
  obtain ⟨hI, h₀, _⟩ := hI
  obtain ⟨hI', h₀', _⟩ := hI'
  simp only [mk.injEq]
  grind

Depends on / 依赖: mk.injEq
-/
theorem DividedPowers.ext (hI : DividedPowers I) (hI' : DividedPowers I)
    (h_eq : forall (n : Nat) {x : A} (_ : x in I), hI.dpow n x = hI'.dpow n x) :
    hI = hI' := by
  obtain ⟨hI, h₀, _⟩ := hI
  obtain ⟨hI', h₀', _⟩ := hI'
  simp only [mk.injEq]
  grind

/--
theorem `DividedPowers.coe_injective` / 定理 `DividedPowers.coe_injective`

English:
theorem DividedPowers.coe_injective
  proof: fun hI hI' h => by
  ext n x
  exact congr_fun (congr_fun h n) x

中文:
定理 DividedPowers.coe_injective
  证明: fun hI hI' h => by
  ext n x
  exact congr_fun (congr_fun h n) x

Depends on / 依赖: congr_fun
-/
theorem DividedPowers.coe_injective :
    Function.Injective (fun (h : DividedPowers I) => (h : Nat -> A -> A)) := fun hI hI' h => by
  ext n x
  exact congr_fun (congr_fun h n) x

end DividedPowersDefinition

namespace DividedPowers

section BasicLemmas

/- ## Basic lemmas for divided powers -/

variable {A : Type*} [CommSemiring A] {I : Ideal A} {a b : A}

/--
theorem `dpow_add'` / 定理 `dpow_add'`

English:
theorem dpow_add'
  given: (hI : DividedPowers I) {n : Nat} (ha : a in I) (hb : b in I)
  proof: by
  rw [hI.dpow_add ha hb]; rw [sum_antidiagonal_eq_sum_range_succ_mk]

中文:
定理 dpow_add'
  条件: (hI : DividedPowers I) {n : 自然数} (ha : a in I) (hb : b in I)
  证明: by
  rw [hI.dpow_add ha hb]; rw [sum_antidiagonal_eq_sum_range_succ_mk]

Depends on / 依赖: dpow_add, hI.dpow_add, sum_antidiagonal_eq_sum_range_succ_mk
-/
theorem dpow_add' (hI : DividedPowers I) {n : Nat} (ha : a in I) (hb : b in I) :
    hI.dpow n (a + b) = (range (n + 1)).sum fun k => hI.dpow k a * hI.dpow (n - k) b := by
  rw [hI.dpow_add ha hb]; rw [sum_antidiagonal_eq_sum_range_succ_mk]

/--
Definition of `exp` / `exp` 的定义

English:
definition exp
  signature: (hI : DividedPowers I) (a : A)
  body: PowerSeries.mk fun n => hI.dpow n a

中文:
定义 exp
  签名: (hI : DividedPowers I) (a : A)
  定义体: PowerSeries.mk fun n => hI.dpow n a

Depends on / 依赖: PowerSeries, PowerSeries.mk, hI.dpow
-/
def exp (hI : DividedPowers I) (a : A) : PowerSeries A :=
  PowerSeries.mk fun n => hI.dpow n a

/--
theorem `exp_add'` / 定理 `exp_add'`

English:
theorem exp_add'
  statement: (dp : Nat -> A -> A)
  proof: by
  ext n
  simp only [PowerSeries.coeff_mk, PowerSeries.coeff_mul, dp_add n,
    sum_antidiagonal_eq_sum_range_succ_mk]

中文:
定理 exp_add'
  结论: (dp : 自然数 -> A -> A)
  证明: by
  ext n
  simp only [PowerSeries.coeff_mk, PowerSeries.coeff_mul, dp_add n,
    sum_antidiagonal_eq_sum_range_succ_mk]

Depends on / 依赖: PowerSeries, PowerSeries.coeff_mk, PowerSeries.coeff_mul, coeff_mk, coeff_mul, dp_add, sum_antidiagonal_eq_sum_range_succ_mk
-/
theorem exp_add' (dp : Nat -> A -> A)
    (dp_add : forall n, dp n (a + b) = (antidiagonal n).sum fun k => dp k.1 a * dp k.2 b) :
    PowerSeries.mk (fun n => dp n (a + b)) =
      (PowerSeries.mk fun n => dp n a) * (PowerSeries.mk fun n => dp n b) := by
  ext n
  simp only [PowerSeries.coeff_mk, PowerSeries.coeff_mul, dp_add n,
    sum_antidiagonal_eq_sum_range_succ_mk]

/--
theorem `exp_add` / 定理 `exp_add`

English:
theorem exp_add
  given: (hI : DividedPowers I) (ha : a in I) (hb : b in I)
  proof: exp_add' _ (fun _ => hI.dpow_add ha hb)

中文:
定理 exp_add
  条件: (hI : DividedPowers I) (ha : a in I) (hb : b in I)
  证明: exp_add' _ (fun _ => hI.dpow_add ha hb)

Depends on / 依赖: dpow_add, exp_add, hI.dpow_add
-/
theorem exp_add (hI : DividedPowers I) (ha : a in I) (hb : b in I) :
    hI.exp (a + b) = hI.exp a * hI.exp b :=
  exp_add' _ (fun _ => hI.dpow_add ha hb)

variable (hI : DividedPowers I)


/--
theorem `dpow_smul` / 定理 `dpow_smul`

English:
theorem dpow_smul
  given: {n : Nat} (ha : a in I)
  proof: by
  simp only [smul_eq_mul, hI.dpow_mul, ha]

中文:
定理 dpow_smul
  条件: {n : 自然数} (ha : a in I)
  证明: by
  simp only [smul_eq_mul, hI.dpow_mul, ha]

Depends on / 依赖: dpow_mul, hI.dpow_mul, smul_eq_mul
-/
theorem dpow_smul {n : Nat} (ha : a in I) :
    hI.dpow n (b • a) = b ^ n • hI.dpow n a := by
  simp only [smul_eq_mul, hI.dpow_mul, ha]

/--
theorem `dpow_mul_right` / 定理 `dpow_mul_right`

English:
theorem dpow_mul_right
  given: {n : Nat} (ha : a in I)
  proof: by
  rw [mul_comm]; rw [hI.dpow_mul ha]; rw [mul_comm]

中文:
定理 dpow_mul_right
  条件: {n : 自然数} (ha : a in I)
  证明: by
  rw [mul_comm]; rw [hI.dpow_mul ha]; rw [mul_comm]

Depends on / 依赖: dpow_mul, hI.dpow_mul, mul_comm
-/
theorem dpow_mul_right {n : Nat} (ha : a in I) :
    hI.dpow n (a * b) = hI.dpow n a * b ^ n := by
  rw [mul_comm]; rw [hI.dpow_mul ha]; rw [mul_comm]

/--
theorem `dpow_smul_right` / 定理 `dpow_smul_right`

English:
theorem dpow_smul_right
  given: {n : Nat} (ha : a in I)
  proof: by
  rw [smul_eq_mul]; rw [hI.dpow_mul_right ha]; rw [smul_eq_mul]

中文:
定理 dpow_smul_right
  条件: {n : 自然数} (ha : a in I)
  证明: by
  rw [smul_eq_mul]; rw [hI.dpow_mul_right ha]; rw [smul_eq_mul]

Depends on / 依赖: dpow_mul_right, hI.dpow_mul_right, smul_eq_mul
-/
theorem dpow_smul_right {n : Nat} (ha : a in I) :
    hI.dpow n (a • b) = hI.dpow n a • b ^ n := by
  rw [smul_eq_mul]; rw [hI.dpow_mul_right ha]; rw [smul_eq_mul]

/--
theorem `factorial_mul_dpow_eq_pow` / 定理 `factorial_mul_dpow_eq_pow`

English:
theorem factorial_mul_dpow_eq_pow
  given: {n : Nat} (ha : a in I)
  proof: by
  induction n with
  | zero => rw [factorial_zero, cast_one, one_mul, pow_zero, hI.dpow_zero ha]
  | succ n ih =>
    rw [factorial_succ]; rw [mul_comm (n + 1)]
    nth_rewrite 1 [← (n + 1).choose_one_right]
    rw [← choose_symm_add]; rw [cast_mul]; rw [mul_assoc]; rw [← hI.mul_dpow ha]; rw [← mul_assoc]; rw [ih]; rw [hI.dpow_one ha]; rw [pow_succ]; rw [mul_comm]

中文:
定理 factorial_mul_dpow_eq_pow
  条件: {n : 自然数} (ha : a in I)
  证明: by
  induction n with
  | zero => rw [factorial_zero, cast_one, one_mul, pow_zero, hI.dpow_zero ha]
  | succ n ih =>
    rw [factorial_succ]; rw [mul_comm (n + 1)]
    nth_rewrite 1 [← (n + 1).choose_one_right]
    rw [← choose_symm_add]; rw [cast_mul]; rw [mul_assoc]; rw [← hI.mul_dpow ha]; rw [← mul_assoc]; rw [ih]; rw [hI.dpow_one ha]; rw [pow_succ]; rw [mul_comm]

Depends on / 依赖: cast_mul, cast_one, choose_one_right, choose_symm_add, dpow_one, dpow_zero, factorial_succ, factorial_zero, hI.dpow_one, hI.dpow_zero, hI.mul_dpow, mul_assoc, mul_comm, mul_dpow, nth_rewrite, one_mul, pow_succ, pow_zero
-/
theorem factorial_mul_dpow_eq_pow {n : Nat} (ha : a in I) :
    (n ! : A) * hI.dpow n a = a ^ n := by
  induction n with
  | zero => rw [factorial_zero, cast_one, one_mul, pow_zero, hI.dpow_zero ha]
  | succ n ih =>
    rw [factorial_succ]; rw [mul_comm (n + 1)]
    nth_rewrite 1 [← (n + 1).choose_one_right]
    rw [← choose_symm_add]; rw [cast_mul]; rw [mul_assoc]; rw [← hI.mul_dpow ha]; rw [← mul_assoc]; rw [ih]; rw [hI.dpow_one ha]; rw [pow_succ]; rw [mul_comm]

/--
theorem `dpow_eval_zero` / 定理 `dpow_eval_zero`

English:
theorem dpow_eval_zero
  given: {n : Nat} (hn : n != 0)
  statement: hI.dpow n 0 = 0
  proof: by
  rw [← MulZeroClass.mul_zero (0 : A)]; rw [hI.dpow_mul I.zero_mem]; rw [zero_pow hn]; rw [zero_mul]; rw [zero_mul]

中文:
定理 dpow_eval_zero
  条件: {n : 自然数} (hn : n != 0)
  结论: hI.dpow n 0 = 0
  证明: by
  rw [← MulZeroClass.mul_zero (0 : A)]; rw [hI.dpow_mul I.zero_mem]; rw [zero_pow hn]; rw [zero_mul]; rw [zero_mul]

Depends on / 依赖: I.zero_mem, MulZeroClass, MulZeroClass.mul_zero, dpow_mul, hI.dpow_mul, mul_zero, zero_mem, zero_mul, zero_pow
-/
theorem dpow_eval_zero {n : Nat} (hn : n != 0) : hI.dpow n 0 = 0 := by
  rw [← MulZeroClass.mul_zero (0 : A)]; rw [hI.dpow_mul I.zero_mem]; rw [zero_pow hn]; rw [zero_mul]; rw [zero_mul]

/--
theorem `nilpotent_of_mem_dpIdeal` / 定理 `nilpotent_of_mem_dpIdeal`

English:
theorem nilpotent_of_mem_dpIdeal
  statement: {n : Nat} (hn : n != 0) (hnI : forall {y}, y in I -> n • y = 0)
  proof: by
  have h_fac : (n ! : A) * hI.dpow n a = n • ((n - 1)! : A) * hI.dpow n a := by
    rw [nsmul_eq_mul]; rw [← cast_mul]; rw [mul_factorial_pred hn]
  rw [← hI.factorial_mul_dpow_eq_pow ha]; rw [h_fac]; rw [smul_mul_assoc]
  exact hnI (I.mul_mem_left ((n - 1)! : A) (hI.dpow_mem hn ha))

中文:
定理 nilpotent_of_mem_dpIdeal
  结论: {n : 自然数} (hn : n != 0) (hnI : 对任意 {y}, y in I -> n • y = 0)
  证明: by
  have h_fac : (n ! : A) * hI.dpow n a = n • ((n - 1)! : A) * hI.dpow n a := by
    rw [nsmul_eq_mul]; rw [← cast_mul]; rw [mul_factorial_pred hn]
  rw [← hI.factorial_mul_dpow_eq_pow ha]; rw [h_fac]; rw [smul_mul_assoc]
  exact hnI (I.mul_mem_left ((n - 1)! : A) (hI.dpow_mem hn ha))

Depends on / 依赖: I.mul_mem_left, cast_mul, dpow_mem, factorial_mul_dpow_eq_pow, hI.dpow, hI.dpow_mem, hI.factorial_mul_dpow_eq_pow, h_fac, mul_factorial_pred, mul_mem_left, nsmul_eq_mul, smul_mul_assoc
-/
theorem nilpotent_of_mem_dpIdeal {n : Nat} (hn : n != 0) (hnI : forall {y}, y in I -> n • y = 0)
    (hI : DividedPowers I) (ha : a in I) : a ^ n = 0 := by
  have h_fac : (n ! : A) * hI.dpow n a = n • ((n - 1)! : A) * hI.dpow n a := by
    rw [nsmul_eq_mul]; rw [← cast_mul]; rw [mul_factorial_pred hn]
  rw [← hI.factorial_mul_dpow_eq_pow ha]; rw [h_fac]; rw [smul_mul_assoc]
  exact hnI (I.mul_mem_left ((n - 1)! : A) (hI.dpow_mem hn ha))

/--
theorem `coincide_on_smul` / 定理 `coincide_on_smul`

English:
theorem coincide_on_smul
  given: {J : Ideal A} (hJ : DividedPowers J) {n : Nat} (ha : a in I • J)
  proof: by
  induction ha using Submodule.smul_induction_on' generalizing n with
  | smul a ha b hb =>
    rw [smul_eq_mul]; rw [hJ.dpow_mul hb]; rw [mul_comm a b]; rw [hI.dpow_mul ha]; rw [← hJ.factorial_mul_dpow_eq_pow hb]; rw [← hI.factorial_mul_dpow_eq_pow ha]
    ring
  | add x hx y hy hx' hy' =>
    rw [hI.dpow_add (mul_le_left hx) (mul_le_left hy)]; rw [hJ.dpow_add (mul_le_right hx) (mul_le_right hy)]
    apply sum_congr rfl
    intro k _
    rw [hx']; rw [hy']

中文:
定理 coincide_on_smul
  条件: {J : 理想 A} (hJ : DividedPowers J) {n : 自然数} (ha : a in I • J)
  证明: by
  induction ha using Submodule.smul_induction_on' generalizing n with
  | smul a ha b hb =>
    rw [smul_eq_mul]; rw [hJ.dpow_mul hb]; rw [mul_comm a b]; rw [hI.dpow_mul ha]; rw [← hJ.factorial_mul_dpow_eq_pow hb]; rw [← hI.factorial_mul_dpow_eq_pow ha]
    ring
  | add x hx y hy hx' hy' =>
    rw [hI.dpow_add (mul_le_left hx) (mul_le_left hy)]; rw [hJ.dpow_add (mul_le_right hx) (mul_le_right hy)]
    apply sum_congr rfl
    intro k _
    rw [hx']; rw [hy']

Depends on / 依赖: Submodule, Submodule.smul_induction_on, dpow_add, dpow_mul, factorial_mul_dpow_eq_pow, generalizing, hI.dpow_add, hI.dpow_mul, hI.factorial_mul_dpow_eq_pow, hJ.dpow_add, hJ.dpow_mul, hJ.factorial_mul_dpow_eq_pow, mul_comm, mul_le_left, mul_le_right, smul_eq_mul, smul_induction_on, sum_congr
-/
theorem coincide_on_smul {J : Ideal A} (hJ : DividedPowers J) {n : Nat} (ha : a in I • J) :
    hI.dpow n a = hJ.dpow n a := by
  induction ha using Submodule.smul_induction_on' generalizing n with
  | smul a ha b hb =>
    rw [smul_eq_mul]; rw [hJ.dpow_mul hb]; rw [mul_comm a b]; rw [hI.dpow_mul ha]; rw [← hJ.factorial_mul_dpow_eq_pow hb]; rw [← hI.factorial_mul_dpow_eq_pow ha]
    ring
  | add x hx y hy hx' hy' =>
    rw [hI.dpow_add (mul_le_left hx) (mul_le_left hy)]; rw [hJ.dpow_add (mul_le_right hx) (mul_le_right hy)]
    apply sum_congr rfl
    intro k _
    rw [hx']; rw [hy']

/--
theorem `prod_dpow` / 定理 `prod_dpow`

English:
theorem prod_dpow
  given: {ι : Type*} {s : Finset ι} {n : ι -> Nat} (ha : a in I)
  proof: by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [prod_empty, multinomial_empty, cast_one, sum_empty, one_mul]
    rw [hI.dpow_zero ha]
  | insert _ _ hi hrec =>
    rw [prod_insert hi]; rw [hrec]; rw [← mul_assoc]; rw [mul_comm (hI.dpow (n _) a)]; rw [mul_assoc]; rw [hI.mul_dpow ha]; rw [← sum_insert hi]; rw [← mul_assoc]
    apply congr_arg₂ _ _ rfl
    rw [multinomial_insert hi]; rw [mul_comm]; rw [cast_mul]; rw [sum_insert hi]

中文:
定理 prod_dpow
  条件: {ι : 类型} {s : 有限集 ι} {n : ι -> 自然数} (ha : a in I)
  证明: by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [prod_empty, multinomial_empty, cast_one, sum_empty, one_mul]
    rw [hI.dpow_zero ha]
  | insert _ _ hi hrec =>
    rw [prod_insert hi]; rw [hrec]; rw [← mul_assoc]; rw [mul_comm (hI.dpow (n _) a)]; rw [mul_assoc]; rw [hI.mul_dpow ha]; rw [← sum_insert hi]; rw [← mul_assoc]
    apply congr_arg₂ _ _ rfl
    rw [multinomial_insert hi]; rw [mul_comm]; rw [cast_mul]; rw [sum_insert hi]

Depends on / 依赖: Finset, Finset.induction, cast_mul, cast_one, classical, dpow_zero, hI.dpow, hI.dpow_zero, hI.mul_dpow, insert, mul_assoc, mul_comm, mul_dpow, multinomial_empty, multinomial_insert, one_mul, prod_empty, prod_insert, sum_empty, sum_insert
-/
theorem prod_dpow {ι : Type*} {s : Finset ι} {n : ι -> Nat} (ha : a in I) :
    (s.prod fun i => hI.dpow (n i) a) = multinomial s n * hI.dpow (s.sum n) a := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [prod_empty, multinomial_empty, cast_one, sum_empty, one_mul]
    rw [hI.dpow_zero ha]
  | insert _ _ hi hrec =>
    rw [prod_insert hi]; rw [hrec]; rw [← mul_assoc]; rw [mul_comm (hI.dpow (n _) a)]; rw [mul_assoc]; rw [hI.mul_dpow ha]; rw [← sum_insert hi]; rw [← mul_assoc]
    apply congr_arg₂ _ _ rfl
    rw [multinomial_insert hi]; rw [mul_comm]; rw [cast_mul]; rw [sum_insert hi]

-- TODO : can probably be simplified using `DividedPowers.exp`

/--
theorem `dpow_sum'` / 定理 `dpow_sum'`

English:
theorem dpow_sum'
  statement: {M : Type*} [AddCommMonoid M] {I : AddSubmonoid M} (dpow : Nat -> M -> A)
  proof: by
  simp only [sum_antidiagonal_eq_sum_range_succ_mk] at dpow_add
  induction s using Finset.induction generalizing n with
  | empty =>
    simp only [sum_empty, prod_empty, sum_const, nsmul_eq_mul, mul_one]
    by_cases hn : n = 0
    · rw [hn]
      rw [dpow_zero I.zero_mem]
      simp only [sym_zero, card_singleton, cast_one]
    · rw [dpow_eval_zero hn, eq_comm, ← cast_zero]
      apply congr_arg
      rw [card_eq_zero]; rw [sym_eq_empty]
      exact ⟨hn, rfl⟩
  | insert a s ha ih =>
    -- This should be golfable using `Finset.symInsertEquiv`
    have hx' : forall i, i in s -> x i in I := fun i hi => hx i (mem_insert_of_mem hi)
    simp_rw [sum_insert ha,
      dpow_add (hx a (mem_insert_self a s)) (I.sum_mem fun i => hx' i),
      sum_range, ih hx', mul_sum, sum_sigma', eq_comm]
    apply sum_bij'
      (fun m _ => m.filterNe a)
      (fun m _ => m.2.fill a m.1)
      (fun m hm => mem_sigma.2 ⟨mem_univ _, _⟩)
      (fun m hm => by
        simp only [succ_eq_add_one, mem_sym_iff, mem_insert, Sym.mem_fill_iff]
        simp only [mem_sigma, mem_univ, mem_sym_iff, true_and] at hm
        intro b
        apply Or.imp (fun h => h.2) (fun h => hm b h))
      (fun m _ => m.fill_filterNe a)
    · intro m hm
      simp only [mem_sigma, mem_univ, mem_sym_iff, true_and] at hm
      exact Sym.filter_ne_fill a m fun a_1 => ha (hm a a_1)
    · intro m hm
      simp only [mem_sym_iff, mem_insert] at hm
      rw [prod_insert ha]
      apply congr_arg₂ _ rfl
      apply prod_congr rfl
      intro i hi
      apply congr_arg₂ _ _ rfl
      conv_lhs => rw [← m.fill_filterNe a]
      exact Sym.count_coe_fill_of_ne (ne_of_mem_of_not_mem hi ha)
    · intro m hm
      convert! sym_filterNe_mem a hm
      rw [erase_insert ha]

中文:
定理 dpow_sum'
  结论: {M : 类型} [加法交换幺半群 M] {I : 加法子幺半群 M} (dpow : 自然数 -> M -> A)
  证明: by
  simp only [sum_antidiagonal_eq_sum_range_succ_mk] at dpow_add
  induction s using Finset.induction generalizing n with
  | empty =>
    simp only [sum_empty, prod_empty, sum_const, nsmul_eq_mul, mul_one]
    by_cases hn : n = 0
    · rw [hn]
      rw [dpow_zero I.zero_mem]
      simp only [sym_zero, card_singleton, cast_one]
    · rw [dpow_eval_zero hn, eq_comm, ← cast_zero]
      apply congr_arg
      rw [card_eq_zero]; rw [sym_eq_empty]
      exact ⟨hn, rfl⟩
  | insert a s ha ih =>
    -- This should be golfable using `Finset.symInsertEquiv`
    have hx' : forall i, i in s -> x i in I := fun i hi => hx i (mem_insert_of_mem hi)
    simp_rw [sum_insert ha,
      dpow_add (hx a (mem_insert_self a s)) (I.sum_mem fun i => hx' i),
      sum_range, ih hx', mul_sum, sum_sigma', eq_comm]
    apply sum_bij'
      (fun m _ => m.filterNe a)
      (fun m _ => m.2.fill a m.1)
      (fun m hm => mem_sigma.2 ⟨mem_univ _, _⟩)
      (fun m hm => by
        simp only [succ_eq_add_one, mem_sym_iff, mem_insert, Sym.mem_fill_iff]
        simp only [mem_sigma, mem_univ, mem_sym_iff, true_and] at hm
        intro b
        apply Or.imp (fun h => h.2) (fun h => hm b h))
      (fun m _ => m.fill_filterNe a)
    · intro m hm
      simp only [mem_sigma, mem_univ, mem_sym_iff, true_and] at hm
      exact Sym.filter_ne_fill a m fun a_1 => ha (hm a a_1)
    · intro m hm
      simp only [mem_sym_iff, mem_insert] at hm
      rw [prod_insert ha]
      apply congr_arg₂ _ rfl
      apply prod_congr rfl
      intro i hi
      apply congr_arg₂ _ _ rfl
      conv_lhs => rw [← m.fill_filterNe a]
      exact Sym.count_coe_fill_of_ne (ne_of_mem_of_not_mem hi ha)
    · intro m hm
      convert! sym_filterNe_mem a hm
      rw [erase_insert ha]

Depends on / 依赖: Finset, Finset.induction, I.zero_mem, card_eq_zero, card_singleton, cast_one, cast_zero, config, config.maxArgs.getD, congr_arg, dpow_add, dpow_eval_zero, dpow_zero, eq_comm, generalizing, insert, maxArgs, mul_one, nsmul_eq_mul, numArgs
-/
theorem dpow_sum' {M : Type*} [AddCommMonoid M] {I : AddSubmonoid M} (dpow : Nat -> M -> A)
    (dpow_zero : forall {x}, x in I -> dpow 0 x = 1)
    (dpow_add : forall {n x y}, x in I -> y in I ->
      dpow n (x + y) = (antidiagonal n).sum fun k => dpow k.1 x * dpow k.2 y)
    (dpow_eval_zero : forall {n : Nat}, n != 0 -> dpow n 0 = 0)
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {x : ι -> M} (hx : forall i in s, x i in I) {n : Nat} :
    dpow n (s.sum x) = (s.sym n).sum fun k => s.prod fun i => dpow (Multiset.count i k) (x i) := by
  simp only [sum_antidiagonal_eq_sum_range_succ_mk] at dpow_add
  induction s using Finset.induction generalizing n with
  | empty =>
    simp only [sum_empty, prod_empty, sum_const, nsmul_eq_mul, mul_one]
    by_cases hn : n = 0
    · rw [hn]
      rw [dpow_zero I.zero_mem]
      simp only [sym_zero, card_singleton, cast_one]
    · rw [dpow_eval_zero hn, eq_comm, ← cast_zero]
      apply congr_arg
      rw [card_eq_zero]; rw [sym_eq_empty]
      exact ⟨hn, rfl⟩
  | insert a s ha ih =>
    -- This should be golfable using `Finset.symInsertEquiv`
    have hx' : forall i, i in s -> x i in I := fun i hi => hx i (mem_insert_of_mem hi)
    simp_rw [sum_insert ha,
      dpow_add (hx a (mem_insert_self a s)) (I.sum_mem fun i => hx' i),
      sum_range, ih hx', mul_sum, sum_sigma', eq_comm]
    apply sum_bij'
      (fun m _ => m.filterNe a)
      (fun m _ => m.2.fill a m.1)
      (fun m hm => mem_sigma.2 ⟨mem_univ _, _⟩)
      (fun m hm => by
        simp only [succ_eq_add_one, mem_sym_iff, mem_insert, Sym.mem_fill_iff]
        simp only [mem_sigma, mem_univ, mem_sym_iff, true_and] at hm
        intro b
        apply Or.imp (fun h => h.2) (fun h => hm b h))
      (fun m _ => m.fill_filterNe a)
    · intro m hm
      simp only [mem_sigma, mem_univ, mem_sym_iff, true_and] at hm
      exact Sym.filter_ne_fill a m fun a_1 => ha (hm a a_1)
    · intro m hm
      simp only [mem_sym_iff, mem_insert] at hm
      rw [prod_insert ha]
      apply congr_arg₂ _ rfl
      apply prod_congr rfl
      intro i hi
      apply congr_arg₂ _ _ rfl
      conv_lhs => rw [← m.fill_filterNe a]
      exact Sym.count_coe_fill_of_ne (ne_of_mem_of_not_mem hi ha)
    · intro m hm
      convert! sym_filterNe_mem a hm
      rw [erase_insert ha]

variable {ι : Type*} [DecidableEq ι]

/--
theorem `dpow_sum` / 定理 `dpow_sum`

English:
theorem dpow_sum
  given: {s : Finset ι} {x : ι -> A} (hx : forall i in s, x i in I) {n : Nat}
  proof: dpow_sum' hI.dpow hI.dpow_zero hI.dpow_add hI.dpow_eval_zero hx

中文:
定理 dpow_sum
  条件: {s : 有限集 ι} {x : ι -> A} (hx : 对任意 i in s, x i in I) {n : 自然数}
  证明: dpow_sum' hI.dpow hI.dpow_zero hI.dpow_add hI.dpow_eval_zero hx

Depends on / 依赖: config, config.maxArgs.getD, dpow_add, dpow_eval_zero, dpow_sum, dpow_zero, hI.dpow, hI.dpow_add, hI.dpow_eval_zero, hI.dpow_zero, maxArgs, numArgs
-/
theorem dpow_sum {s : Finset ι} {x : ι -> A} (hx : forall i in s, x i in I) {n : Nat} :
    hI.dpow n (s.sum x) =
      (s.sym n).sum fun k => s.prod fun i => hI.dpow (Multiset.count i k) (x i) :=
  dpow_sum' hI.dpow hI.dpow_zero hI.dpow_add hI.dpow_eval_zero hx

/--
theorem `dpow_finsupp_sum` / 定理 `dpow_finsupp_sum`

English:
theorem dpow_finsupp_sum
  given: {x : ι ->₀ A} (hx : forall i, x i in I) {n : Nat}
  proof: by
  simp [Finsupp.sum, hI.dpow_sum (fun i _ => hx i), Finsupp.prod]

中文:
定理 dpow_finsupp_sum
  条件: {x : ι ->₀ A} (hx : 对任意 i, x i in I) {n : 自然数}
  证明: by
  simp [Finsupp.sum, hI.dpow_sum (fun i _ => hx i), Finsupp.prod]

Depends on / 依赖: Finsupp, Finsupp.prod, Finsupp.sum, dpow_sum, hI.dpow_sum
-/
theorem dpow_finsupp_sum {x : ι ->₀ A} (hx : forall i, x i in I) {n : Nat} :
    hI.dpow n (x.sum fun _ r => r) =
      ∑ k in (x.support.sym n), x.prod fun i r => hI.dpow (Multiset.count i k) r := by
  simp [Finsupp.sum, hI.dpow_sum (fun i _ => hx i), Finsupp.prod]

/--
theorem `dpow_linearCombination` / 定理 `dpow_linearCombination`

English:
theorem dpow_linearCombination
  statement: {S : Type*} [CommSemiring S] [Algebra A S] {J : Ideal S}
  proof: by
  rw [Finsupp.sum]; rw [hJ.dpow_sum (fun i hi => Submodule.smul_of_tower_mem J _ (hx i hi))]
  apply Finset.sum_congr rfl
  intros
  apply Finset.prod_congr rfl
  intro i hi
  rw [Algebra.smul_def]; rw [hJ.dpow_mul (hx i hi)]; rw [← map_pow]; rw [← Algebra.smul_def]

中文:
定理 dpow_linearCombination
  结论: {S : 类型} [交换半环 S] [代数 A S] {J : 理想 S}
  证明: by
  rw [Finsupp.sum]; rw [hJ.dpow_sum (fun i hi => Submodule.smul_of_tower_mem J _ (hx i hi))]
  apply Finset.sum_congr rfl
  intros
  apply Finset.prod_congr rfl
  intro i hi
  rw [Algebra.smul_def]; rw [hJ.dpow_mul (hx i hi)]; rw [← map_pow]; rw [← Algebra.smul_def]

Depends on / 依赖: Algebra, Algebra.smul_def, Finset, Finset.prod_congr, Finset.sum_congr, Finsupp, Finsupp.sum, Submodule, Submodule.smul_of_tower_mem, dpow_mul, dpow_sum, hJ.dpow_mul, hJ.dpow_sum, intros, map_pow, prod_congr, smul_def, smul_of_tower_mem, sum_congr
-/
theorem dpow_linearCombination {S : Type*} [CommSemiring S] [Algebra A S] {J : Ideal S}
    (hJ : DividedPowers J) {b : ι -> S} {x : ι ->₀ A} (hx : forall i in x.support, b i in J) {n : Nat} :
    hJ.dpow n (x.sum fun i r => r • (b i)) =
      ∑ k in x.support.sym n,
        x.prod fun i r => r ^ (Multiset.count i k) • hJ.dpow (Multiset.count i k) (b i) := by
  rw [Finsupp.sum]; rw [hJ.dpow_sum (fun i hi => Submodule.smul_of_tower_mem J _ (hx i hi))]
  apply Finset.sum_congr rfl
  intros
  apply Finset.prod_congr rfl
  intro i hi
  rw [Algebra.smul_def]; rw [hJ.dpow_mul (hx i hi)]; rw [← map_pow]; rw [← Algebra.smul_def]

/--
theorem `dpow_prod` / 定理 `dpow_prod`

English:
theorem dpow_prod
  statement: {ι : Type*} {r : ι -> A} {s : Finset ι} (hs : s.Nonempty)
  proof: by
  classical
  induction s using Finset.induction with
  | empty => simp_all
  | @insert a s has hrec =>
    rw [Finset.prod_insert has]
    by_cases h : s.Nonempty
    · rw [dpow_mul]
      · simp only [Finset.card_insert_of_notMem has, add_tsub_cancel_right, nsmul_eq_mul,
          Nat.cast_pow, Finset.prod_insert has,
          hrec h (fun i hi => hs' i (mem_insert_of_mem hi)), ← mul_assoc]
        apply congr_arg₂ _ _ rfl
        have : #s = #s - 1 + 1 := by grind
        nth_rewrite 2 [this]
        rw [mul_comm]; rw [pow_succ]; rw [mul_assoc]; rw [hI.factorial_mul_dpow_eq_pow]
        exact hs' a (mem_insert_self a s)
      · obtain ⟨j, hj⟩ := h
        rw [Finset.prod_eq_prod_sdiff_singleton_mul hj]
        exact I.mul_mem_left _ (hs' j (mem_insert_of_mem hj))
    · simp [not_nonempty_iff_eq_empty.mp h]

中文:
定理 dpow_prod
  结论: {ι : 类型} {r : ι -> A} {s : 有限集 ι} (hs : s.非空)
  证明: by
  classical
  induction s using Finset.induction with
  | empty => simp_all
  | @insert a s has hrec =>
    rw [Finset.prod_insert has]
    by_cases h : s.Nonempty
    · rw [dpow_mul]
      · simp only [Finset.card_insert_of_notMem has, add_tsub_cancel_right, nsmul_eq_mul,
          Nat.cast_pow, Finset.prod_insert has,
          hrec h (fun i hi => hs' i (mem_insert_of_mem hi)), ← mul_assoc]
        apply congr_arg₂ _ _ rfl
        have : #s = #s - 1 + 1 := by grind
        nth_rewrite 2 [this]
        rw [mul_comm]; rw [pow_succ]; rw [mul_assoc]; rw [hI.factorial_mul_dpow_eq_pow]
        exact hs' a (mem_insert_self a s)
      · obtain ⟨j, hj⟩ := h
        rw [Finset.prod_eq_prod_sdiff_singleton_mul hj]
        exact I.mul_mem_left _ (hs' j (mem_insert_of_mem hj))
    · simp [not_nonempty_iff_eq_empty.mp h]

Depends on / 依赖: Finset, Finset.card_insert_of_notMem, Finset.induction, Finset.prod_insert, Nat.cast_pow, Nonempty, add_tsub_cancel_right, card_insert_of_notMem, cast_pow, classical, dpow_mul, factorial_mul, hI.factorial_mul, insert, mem_insert_of_mem, mul_assoc, mul_comm, nsmul_eq_mul, nth_rewrite, pow_succ
-/
theorem dpow_prod {ι : Type*} {r : ι -> A} {s : Finset ι} (hs : s.Nonempty)
    (hs' : forall i in s, r i in I) {n : Nat} :
    hI.dpow n (∏ i in s, r i) = n.factorial ^ (s.card - 1) • (∏ i in s, hI.dpow n (r i)) := by
  classical
  induction s using Finset.induction with
  | empty => simp_all
  | @insert a s has hrec =>
    rw [Finset.prod_insert has]
    by_cases h : s.Nonempty
    · rw [dpow_mul]
      · simp only [Finset.card_insert_of_notMem has, add_tsub_cancel_right, nsmul_eq_mul,
          Nat.cast_pow, Finset.prod_insert has,
          hrec h (fun i hi => hs' i (mem_insert_of_mem hi)), ← mul_assoc]
        apply congr_arg₂ _ _ rfl
        have : #s = #s - 1 + 1 := by grind
        nth_rewrite 2 [this]
        rw [mul_comm]; rw [pow_succ]; rw [mul_assoc]; rw [hI.factorial_mul_dpow_eq_pow]
        exact hs' a (mem_insert_self a s)
      · obtain ⟨j, hj⟩ := h
        rw [Finset.prod_eq_prod_sdiff_singleton_mul hj]
        exact I.mul_mem_left _ (hs' j (mem_insert_of_mem hj))
    · simp [not_nonempty_iff_eq_empty.mp h]

end BasicLemmas

section Equiv
/- ## Relation of divided powers with ring equivalences -/

variable {A B : Type*} [CommSemiring A] {I : Ideal A} [CommSemiring B] {J : Ideal B}
  {e : A ≃+* B} (h : I.map e = J)

/--
Definition of `ofRingEquiv` / `ofRingEquiv` 的定义

English:
definition ofRingEquiv
  signature: (hI : DividedPowers I)
  body: e (hI.dpow n (e.symm b))
  dpow_null hx := by
    rw [EmbeddingLike.map_eq_zero_iff]; rw [hI.dpow_null]
    rwa [symm_apply_mem_of_equiv_iff, h]
  dpow_zero hx := by
    rw [EmbeddingLike.map_eq_one_iff]; rw [hI.dpow_zero]
    rwa [symm_apply_mem_of_equiv_iff, h]
  dpow_one hx := by
    rw [dpow_one]; rw [RingEquiv.apply_symm_apply]
    rwa [I.symm_apply_mem_of_equiv_iff, h]
  dpow_mem hn hx := by
    rw [← h]; rw [I.apply_mem_of_equiv_iff]
    apply hI.dpow_mem hn
    rwa [I.symm_apply_mem_of_equiv_iff, h]
  dpow_add hx hy := by
    simp only [map_add]
    rw [hI.dpow_add (symm_apply_mem_of_equiv_iff.mpr (h ▸ hx))
        (symm_apply_mem_of_equiv_iff.mpr (h ▸ hy))]
    simp only [map_sum, map_mul]
  dpow_mul hx := by
    simp only [map_mul]
    rw [hI.dpow_mul (symm_apply_mem_of_equiv_iff.mpr (h ▸ hx))]
    rw [map_mul]; rw [map_pow]
    simp only [RingEquiv.apply_symm_apply]
  mul_dpow hx := by
    rw [← map_mul]; rw [hI.mul_dpow]; rw [map_mul]
    · simp only [map_natCast]
    · rwa [symm_apply_mem_of_equiv_iff, h]
  dpow_comp hn hx := by
    simp only [RingEquiv.symm_apply_apply]
    rw [hI.dpow_comp hn]
    · simp only [map_mul, map_natCast]
    · rwa [symm_apply_mem_of_equiv_iff, h]

@[simp]

中文:
定义 ofRingEquiv
  签名: (hI : DividedPowers I)
  定义体: e (hI.dpow n (e.symm b))
  dpow_null hx := by
    rw [EmbeddingLike.map_eq_zero_iff]; rw [hI.dpow_null]
    rwa [symm_apply_mem_of_equiv_iff, h]
  dpow_zero hx := by
    rw [EmbeddingLike.map_eq_one_iff]; rw [hI.dpow_zero]
    rwa [symm_apply_mem_of_equiv_iff, h]
  dpow_one hx := by
    rw [dpow_one]; rw [RingEquiv.apply_symm_apply]
    rwa [I.symm_apply_mem_of_equiv_iff, h]
  dpow_mem hn hx := by
    rw [← h]; rw [I.apply_mem_of_equiv_iff]
    apply hI.dpow_mem hn
    rwa [I.symm_apply_mem_of_equiv_iff, h]
  dpow_add hx hy := by
    simp only [map_add]
    rw [hI.dpow_add (symm_apply_mem_of_equiv_iff.mpr (h ▸ hx))
        (symm_apply_mem_of_equiv_iff.mpr (h ▸ hy))]
    simp only [map_sum, map_mul]
  dpow_mul hx := by
    simp only [map_mul]
    rw [hI.dpow_mul (symm_apply_mem_of_equiv_iff.mpr (h ▸ hx))]
    rw [map_mul]; rw [map_pow]
    simp only [RingEquiv.apply_symm_apply]
  mul_dpow hx := by
    rw [← map_mul]; rw [hI.mul_dpow]; rw [map_mul]
    · simp only [map_natCast]
    · rwa [symm_apply_mem_of_equiv_iff, h]
  dpow_comp hn hx := by
    simp only [RingEquiv.symm_apply_apply]
    rw [hI.dpow_comp hn]
    · simp only [map_mul, map_natCast]
    · rwa [symm_apply_mem_of_equiv_iff, h]

@[simp]

Depends on / 依赖: e.symm, hI.dpow
-/
def ofRingEquiv (hI : DividedPowers I) : DividedPowers J where
  dpow n b := e (hI.dpow n (e.symm b))
  dpow_null hx := by
    rw [EmbeddingLike.map_eq_zero_iff]; rw [hI.dpow_null]
    rwa [symm_apply_mem_of_equiv_iff, h]
  dpow_zero hx := by
    rw [EmbeddingLike.map_eq_one_iff]; rw [hI.dpow_zero]
    rwa [symm_apply_mem_of_equiv_iff, h]
  dpow_one hx := by
    rw [dpow_one]; rw [RingEquiv.apply_symm_apply]
    rwa [I.symm_apply_mem_of_equiv_iff, h]
  dpow_mem hn hx := by
    rw [← h]; rw [I.apply_mem_of_equiv_iff]
    apply hI.dpow_mem hn
    rwa [I.symm_apply_mem_of_equiv_iff, h]
  dpow_add hx hy := by
    simp only [map_add]
    rw [hI.dpow_add (symm_apply_mem_of_equiv_iff.mpr (h ▸ hx))
        (symm_apply_mem_of_equiv_iff.mpr (h ▸ hy))]
    simp only [map_sum, map_mul]
  dpow_mul hx := by
    simp only [map_mul]
    rw [hI.dpow_mul (symm_apply_mem_of_equiv_iff.mpr (h ▸ hx))]
    rw [map_mul]; rw [map_pow]
    simp only [RingEquiv.apply_symm_apply]
  mul_dpow hx := by
    rw [← map_mul]; rw [hI.mul_dpow]; rw [map_mul]
    · simp only [map_natCast]
    · rwa [symm_apply_mem_of_equiv_iff, h]
  dpow_comp hn hx := by
    simp only [RingEquiv.symm_apply_apply]
    rw [hI.dpow_comp hn]
    · simp only [map_mul, map_natCast]
    · rwa [symm_apply_mem_of_equiv_iff, h]

@[simp]
/--
theorem `ofRingEquiv_dpow` / 定理 `ofRingEquiv_dpow`

English:
theorem ofRingEquiv_dpow
  given: (hI : DividedPowers I) {n : Nat} {b : B}
  proof: rfl

中文:
定理 ofRingEquiv_dpow
  条件: (hI : DividedPowers I) {n : 自然数} {b : B}
  证明: rfl
-/
theorem ofRingEquiv_dpow (hI : DividedPowers I) {n : Nat} {b : B} :
    (ofRingEquiv h hI).dpow n b = e (hI.dpow n (e.symm b)) := rfl

/--
theorem `ofRingEquiv_dpow_apply` / 定理 `ofRingEquiv_dpow_apply`

English:
theorem ofRingEquiv_dpow_apply
  given: (hI : DividedPowers I) {n : Nat} {a : A}
  proof: by
  simp

中文:
定理 ofRingEquiv_dpow_apply
  条件: (hI : DividedPowers I) {n : 自然数} {a : A}
  证明: by
  simp
-/
theorem ofRingEquiv_dpow_apply (hI : DividedPowers I) {n : Nat} {a : A} :
    (ofRingEquiv h hI).dpow n (e a) = e (hI.dpow n a) := by
  simp

/--
Definition of `equiv` / `equiv` 的定义

English:
definition equiv
  signature: : DividedPowers I ≃ DividedPowers J where
  body: ofRingEquiv h
  invFun := ofRingEquiv (show map e.symm J = I by rw [← h]; exact I.map_of_equiv e)
  left_inv := fun hI => by ext n a; simp [ofRingEquiv]
  right_inv := fun hJ => by ext n b; simp [ofRingEquiv]

中文:
定义 equiv
  签名: : DividedPowers I ≃ DividedPowers J where
  定义体: ofRingEquiv h
  invFun := ofRingEquiv (show map e.symm J = I by rw [← h]; exact I.map_of_equiv e)
  left_inv := fun hI => by ext n a; simp [ofRingEquiv]
  right_inv := fun hJ => by ext n b; simp [ofRingEquiv]

Depends on / 依赖: ofRingEquiv
-/
def equiv : DividedPowers I ≃ DividedPowers J where
  toFun := ofRingEquiv h
  invFun := ofRingEquiv (show map e.symm J = I by rw [← h]; exact I.map_of_equiv e)
  left_inv := fun hI => by ext n a; simp [ofRingEquiv]
  right_inv := fun hJ => by ext n b; simp [ofRingEquiv]

/--
theorem `equiv_apply` / 定理 `equiv_apply`

English:
theorem equiv_apply
  given: (hI : DividedPowers I) (n : Nat) (b : B)
  proof: rfl

中文:
定理 equiv_apply
  条件: (hI : DividedPowers I) (n : 自然数) (b : B)
  证明: rfl
-/
theorem equiv_apply (hI : DividedPowers I) (n : Nat) (b : B) :
    (equiv h hI).dpow n b = e (hI.dpow n (e.symm b)) := rfl

/--
theorem `equiv_apply'` / 定理 `equiv_apply'`

English:
theorem equiv_apply'
  given: (hI : DividedPowers I) {n : Nat} {a : A}
  proof: ofRingEquiv_dpow_apply h hI

中文:
定理 equiv_apply'
  条件: (hI : DividedPowers I) {n : 自然数} {a : A}
  证明: ofRingEquiv_dpow_apply h hI

Depends on / 依赖: ofRingEquiv_dpow_apply
-/
theorem equiv_apply' (hI : DividedPowers I) {n : Nat} {a : A} :
    (equiv h hI).dpow n (e a) = e (hI.dpow n a) :=
  ofRingEquiv_dpow_apply h hI

end Equiv

end DividedPowers
