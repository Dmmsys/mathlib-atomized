/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Yaël Dillies, Jineon Baek
-/
module

public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Algebra.GCDMonoid.Nat
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Statement of Fermat's Last Theorem

This file states Fermat's Last Theorem. We provide a statement over a general semiring with
specific exponent, along with the usual statement over the naturals.

## Main definitions

* `FermatLastTheoremWith R n`: The statement that only solutions to the Fermat
  equation `a^n + b^n = c^n` in the semiring `R` have `a = 0`, `b = 0` or `c = 0`.

  Note that this statement can certainly be false for certain values of `R` and `n`.
  For example `FermatLastTheoremWith ℝ 3` is false as `1^3 + 1^3 = (2^{1/3})^3`, and
  `FermatLastTheoremWith ℕ 2` is false, as 3^2 + 4^2 = 5^2.

* `FermatLastTheoremFor n` : The statement that the only solutions to `a^n + b^n = c^n` in `ℕ`
  have `a = 0`, `b = 0` or `c = 0`. Again, this statement is not always true, for
  example `FermatLastTheoremFor 1` is false because `2^1 + 2^1 = 4^1`.

* `FermatLastTheorem` : The statement of Fermat's Last Theorem, namely that the only solutions to
  `a^n + b^n = c^n` in `ℕ` when `n ≥ 3` have `a = 0`, `b = 0` or `c = 0`.

## History

Fermat's Last Theorem was an open problem in number theory for hundreds of years, until it was
finally solved by Andrew Wiles, assisted by Richard Taylor, in 1994 (see
[A. Wiles, *Modular elliptic curves and Fermat's last theorem*][Wiles-FLT] and
[R. Taylor and A. Wiles, *Ring-theoretic properties of certain Hecke algebras*][Taylor-Wiles-FLT]).
An ongoing Lean formalisation of the proof, using mathlib as a dependency, is taking place at
https://github.com/ImperialCollegeLondon/FLT .

-/

@[expose] public section

open List

/-- Statement of Fermat's Last Theorem over a given semiring with a specific exponent. -/
/-
**FermatLastTheoremWith** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：FermatLastTheoremWith (R : Type*) [Semiring R] (n : Nat) : Prop
参数：R : Type*；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Statement of Fermat's Last Theorem over a given semiring with a specific exponen
t.
-/
def FermatLastTheoremWith (R : Type*) [Semiring R] (n : ℕ) : Prop :=
  ∀ a b c : R, a ≠ 0 → b ≠ 0 → c ≠ 0 → a ^ n + b ^ n ≠ c ^ n

/-- Statement of Fermat's Last Theorem over the naturals for a given exponent. -/
/-
**FermatLastTheoremFor** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：FermatLastTheoremFor (n : Nat) : Prop
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Statement of Fermat's Last Theorem over the naturals for a given exponent.
-/
def FermatLastTheoremFor (n : ℕ) : Prop := FermatLastTheoremWith ℕ n

/-- Statement of Fermat's Last Theorem: `a ^ n + b ^ n = c ^ n` has no nontrivial natural solution
when `n ≥ 3`.

This is now a theorem of Wiles and Taylor--Wiles; see
https://github.com/ImperialCollegeLondon/FLT for an ongoing Lean formalisation of
a proof. -/
/-
**FermatLastTheorem** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：FermatLastTheorem : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Statement of Fermat's Last Theorem: `a ^ n + b ^ n = c ^ n` has no nontrivial na
tural solution
when `n ≥ 3`.

This is now a theorem of Wiles and Taylor--Wiles; see
https://github.com/ImperialCollegeLondon/FLT for an ongoing Lean formalisation o
f
a proof.
-/
def FermatLastTheorem : Prop := ∀ n ≥ 3, FermatLastTheoremFor n
/-
**fermatLastTheoremFor_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：fermatLastTheoremFor_zero : FermatLastTheoremFor 0
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma fermatLastTheoremFor_zero : FermatLastTheoremFor 0 :=
  fun _ _ _ _ _ _ ↦ by simp
/-
**not_fermatLastTheoremFor_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：not_fermatLastTheoremFor_one : ¬ FermatLastTheoremFor 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma not_fermatLastTheoremFor_one : ¬ FermatLastTheoremFor 1 :=
  fun h ↦ h 1 1 2 (by simp) (by simp) (by simp) (by simp)
/-
**not_fermatLastTheoremFor_two** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：not_fermatLastTheoremFor_two : ¬ FermatLastTheoremFor 2
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma not_fermatLastTheoremFor_two : ¬ FermatLastTheoremFor 2 :=
  fun h ↦ h 3 4 5 (by simp) (by simp) (by simp) (by simp)

variable {R : Type*} [Semiring R] [NoZeroDivisors R] {m n : ℕ}
/-
**FermatLastTheoremWith.mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：FermatLastTheoremWith.mono (hmn : m ∣ n) (hm : FermatLastTheoremWith R m) 
: FermatLastTheoremWith R n
参数：hmn : m ∣ n；hm : FermatLastTheoremWith R m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_mul'`：pow_mul' (a : M) (m n : Nat) : a ^ (m * n) = (a ^ n) ^ m
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma FermatLastTheoremWith.mono (hmn : m ∣ n) (hm : FermatLastTheoremWith R m) :
    FermatLastTheoremWith R n := by
  rintro a b c ha hb hc
  obtain ⟨k, rfl⟩ := hmn
  simp_rw [pow_mul']
  refine hm _ _ _ ?_ ?_ ?_ <;> exact pow_ne_zero _ ‹_›
/-
**FermatLastTheoremFor.mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：FermatLastTheoremFor.mono (hmn : m ∣ n) (hm : FermatLastTheoremFor m) : Fe
rmatLastTheoremFor n
参数：hmn : m ∣ n；hm : FermatLastTheoremFor m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `FermatLastTheoremWith.mono`：FermatLastTheoremWith.mono (hmn : m ∣ n) (hm
 : FermatLastTheoremWith R m) : FermatLastTheoremWith R n
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
-/
lemma FermatLastTheoremFor.mono (hmn : m ∣ n) (hm : FermatLastTheoremFor m) :
    FermatLastTheoremFor n := by
  exact FermatLastTheoremWith.mono hmn hm
/-
**fermatLastTheoremWith_nat_int_rat_tfae** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：fermatLastTheoremWith_nat_int_rat_tfae (n : Nat) : TFAE [FermatLastTheorem
With Nat n, FermatLastTheoremWith Int n, FermatLastTheoremWith Rat n]
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.even_or_odd`：even_or_odd (n : Nat) : Even n ∨ Odd n
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.natAbs_pos`：∀ {a : ℤ}, 0 < a.natAbs ↔ a ≠ 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Int.natCast_inj`：∀ {m n : ℕ}, ↑m = ↑n ↔ m = n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.natCast_natAbs`：∀ (n : ℤ), ↑n.natAbs = |n|
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `Even.pow_abs`：Even.pow_abs (hn : Even n) (a : α) : |a| ^ n = a ^ n
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a
· 使用定理 `abs_of_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], a < 0 → |a| = -a
· 使用引理 `neg_pow`：neg_pow (a : R) (n : Nat) : (-a) ^ n = (-1) ^ n * a ^ n
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `LT.lt.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 < a
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `Eq.trans_lt`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a = b → b < c →
 a < c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_neg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder α] 
[AddLeftStrictMono α] {a b : α},   a < 0 → b < 0 → a + b < 0
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
（共 61 条，此处仅展示前 30 条）
-/
lemma fermatLastTheoremWith_nat_int_rat_tfae (n : ℕ) :
    TFAE [FermatLastTheoremWith ℕ n, FermatLastTheoremWith ℤ n, FermatLastTheoremWith ℚ n] := by
  tfae_have 1 → 2
  | h, a, b, c, ha, hb, hc, habc => by
    obtain hn | hn := n.even_or_odd
    · refine h a.natAbs b.natAbs c.natAbs (by positivity) (by positivity) (by positivity)
        (Int.natCast_inj.1 ?_)
      push_cast
      simp only [hn.pow_abs, habc]
    obtain ha | ha := ha.lt_or_gt <;> obtain hb | hb := hb.lt_or_gt <;>
      obtain hc | hc := hc.lt_or_gt
    · refine h a.natAbs b.natAbs c.natAbs (by positivity) (by positivity) (by positivity)
        (Int.natCast_inj.1 ?_)
      push_cast
      simp only [abs_of_neg, neg_pow a, neg_pow b, neg_pow c, ← mul_add, *]
    · exact (by positivity : 0 < c ^ n).not_gt <| habc.symm.trans_lt <| add_neg (hn.pow_neg ha) <|
        hn.pow_neg hb
    · refine h b.natAbs c.natAbs a.natAbs (by positivity) (by positivity) (by positivity)
        (Int.natCast_inj.1 ?_)
      push_cast
      simp only [abs_of_pos, abs_of_neg, hn.neg_pow, add_neg_eq_iff_eq_add,
        eq_neg_add_iff_add_eq, *]
    · refine h a.natAbs c.natAbs b.natAbs (by positivity) (by positivity) (by positivity)
        (Int.natCast_inj.1 ?_)
      push_cast
      simp only [abs_of_pos, abs_of_neg, hn.neg_pow, neg_add_eq_iff_eq_add,
        *]
    · refine h c.natAbs a.natAbs b.natAbs (by positivity) (by positivity) (by positivity)
        (Int.natCast_inj.1 ?_)
      push_cast
      simp only [abs_of_pos, abs_of_neg, hn.neg_pow, neg_add_eq_iff_eq_add,
        eq_add_neg_iff_add_eq, *]
    · refine h c.natAbs b.natAbs a.natAbs (by positivity) (by positivity) (by positivity)
        (Int.natCast_inj.1 ?_)
      push_cast
      simp only [abs_of_pos, abs_of_neg, hn.neg_pow, add_neg_eq_iff_eq_add,
        *]
    · exact (by positivity : 0 < a ^ n + b ^ n).not_gt <| habc.trans_lt <| hn.pow_neg hc
    · refine h a.natAbs b.natAbs c.natAbs (by positivity) (by positivity) (by positivity)
        (Int.natCast_inj.1 ?_)
      push_cast
      simp only [abs_of_pos, *]
  tfae_have 2 → 3
  | h, a, b, c, ha, hb, hc, habc => by
    rw [← Rat.num_ne_zero] at ha hb hc
    refine h (a.num * b.den * c.den) (a.den * b.num * c.den) (a.den * b.den * c.num)
      (by positivity) (by positivity) (by positivity) ?_
    have : (a.den * b.den * c.den : ℚ) ^ n ≠ 0 := by positivity
    refine Int.cast_injective <| (div_left_inj' this).1 ?_
    push_cast
    simp only [add_div, ← div_pow, mul_div_mul_comm, div_self (by positivity : (a.den : ℚ) ≠ 0),
      div_self (by positivity : (b.den : ℚ) ≠ 0), div_self (by positivity : (c.den : ℚ) ≠ 0),
      one_mul, mul_one, Rat.num_div_den, habc]
  tfae_have 3 → 1
  | h, a, b, c => mod_cast h a b c
  tfae_finish
/-
**fermatLastTheoremFor_iff_nat** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：fermatLastTheoremFor_iff_nat {n : Nat} : FermatLastTheoremFor n ↔ FermatLa
stTheoremWith Nat n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma fermatLastTheoremFor_iff_nat {n : ℕ} : FermatLastTheoremFor n ↔ FermatLastTheoremWith ℕ n :=
  Iff.rfl
/-
**fermatLastTheoremFor_iff_int** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：fermatLastTheoremFor_iff_int {n : Nat} : FermatLastTheoremFor n ↔ FermatLa
stTheoremWith Int n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用引理 `fermatLastTheoremWith_nat_int_rat_tfae`：fermatLastTheoremWith_nat_int_ra
t_tfae (n : Nat) : TFAE [FermatLastTheoremWith Nat n, FermatLastTheoremWith Int 
n, FermatLastTheoremWith Rat…
-/
lemma fermatLastTheoremFor_iff_int {n : ℕ} : FermatLastTheoremFor n ↔ FermatLastTheoremWith ℤ n :=
  (fermatLastTheoremWith_nat_int_rat_tfae n).out 0 1
/-
**fermatLastTheoremFor_iff_rat** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：fermatLastTheoremFor_iff_rat {n : Nat} : FermatLastTheoremFor n ↔ FermatLa
stTheoremWith Rat n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用引理 `fermatLastTheoremWith_nat_int_rat_tfae`：fermatLastTheoremWith_nat_int_ra
t_tfae (n : Nat) : TFAE [FermatLastTheoremWith Nat n, FermatLastTheoremWith Int 
n, FermatLastTheoremWith Rat…
-/
lemma fermatLastTheoremFor_iff_rat {n : ℕ} : FermatLastTheoremFor n ↔ FermatLastTheoremWith ℚ n :=
  (fermatLastTheoremWith_nat_int_rat_tfae n).out 0 2

/--
A relaxed variant of Fermat's Last Theorem over a given commutative semiring with a specific
exponent, allowing nonzero solutions of units and their common multiples.

1. The variant `FermatLastTheoremWith' R` is weaker than `FermatLastTheoremWith R` in general.
   In particular, it holds trivially for `[Field R]`.
2. This variant is equivalent to the original `FermatLastTheoremWith R` for `R = ℕ` or `ℤ`.
   In general, they are equivalent if there is no solutions of units to the Fermat equation.
3. For a polynomial ring `R = k[X]`, the original `FermatLastTheoremWith R` is false but the weaker
   variant `FermatLastTheoremWith' R` is true. This polynomial variant of Fermat's Last Theorem
   can be shown elementarily using Mason--Stothers theorem.
-/
/-
**FermatLastTheoremWith'** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：FermatLastTheoremWith' (R : Type*) [CommSemiring R] (n : Nat) : Prop
参数：R : Type*；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A relaxed variant of Fermat's Last Theorem over a given commutative semiring wit
h a specific
exponent, allowing nonzero solutions of units and their common multiples.

1. The variant `FermatLastTheoremWith' R` is weaker than `FermatLastTheoremWith 
R` in general.
   In particular, it holds trivially for `[Field R]`.
2. This variant is equivalent to the original `FermatLastTheoremWith R` for `R =
 ℕ` or `ℤ`.
   In general, they are equivalent if there is no solutions of units to the Ferm
at equation.
3. For a polynomial ring `R = k[X]`, the original `FermatLastTheoremWith R` is f
alse but the weaker
   variant `FermatLastTheoremWith' R` is true. This polynomial variant of Fermat
's Last Theorem
   can be shown elementarily using Mason--Stothers theorem.
-/
def FermatLastTheoremWith' (R : Type*) [CommSemiring R] (n : ℕ) : Prop :=
  ∀ a b c : R, a ≠ 0 → b ≠ 0 → c ≠ 0 → a ^ n + b ^ n = c ^ n →
    ∃ d a' b' c', (a = a' * d ∧ b = b' * d ∧ c = c' * d) ∧ (IsUnit a' ∧ IsUnit b' ∧ IsUnit c')
/-
**FermatLastTheoremWith.fermatLastTheoremWith'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：FermatLastTheoremWith.fermatLastTheoremWith' {R : Type*} [CommSemiring R] 
{n : Nat} (h : FermatLastTheoremWith R n) : FermatLastTheoremWith' R n
参数：h : FermatLastTheoremWith R n。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma FermatLastTheoremWith.fermatLastTheoremWith' {R : Type*} [CommSemiring R] {n : ℕ}
    (h : FermatLastTheoremWith R n) : FermatLastTheoremWith' R n :=
  fun a b c _ _ _ _ ↦ by exfalso; apply h a b c <;> assumption
/-
**fermatLastTheoremWith'_of_semifield** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ (𝕜 : Type u_2) [inst : Semifield 𝕜] (n : ℕ), FermatLastTheoremWith' 𝕜 n
参数：𝕜 : Type u_2；n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Ne.isUnit`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 →
 IsUnit a
-/
lemma fermatLastTheoremWith'_of_semifield (𝕜 : Type*) [Semifield 𝕜] (n : ℕ) :
    FermatLastTheoremWith' 𝕜 n := fun a b c ha hb hc _ ↦
  ⟨1, a, b, c,
    ⟨(mul_one a).symm, (mul_one b).symm, (mul_one c).symm⟩,
    ⟨ha.isUnit, hb.isUnit, hc.isUnit⟩⟩
/-
**FermatLastTheoremWith'.fermatLastTheoremWith** 是 Mathlib 中的一个定理，位于命名空间 `Fermat
LastTheoremWith'`。
形式化陈述：∀ {R : Type u_2} [inst : CommSemiring R] [IsDomain R] {n : ℕ},   FermatLas
tTheoremWith' R n →     (∀ (a b c : R), IsUnit a → IsUnit b → IsUnit c → a ^ n +
 b ^ n ≠ c ^ n) → FermatLastTheoremWith R n
参数：∀ (a b c : R), IsUnit a → IsUnit b → IsUnit c → a ^ n + b ^ n ≠ c ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_right_cancel₀`：mul_right_cancel₀ (hb : b != 0) (h : a * b = c * b) :
 a = c
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `right_ne_zero_of_mul`：right_ne_zero_of_mul : a * b != 0 -> b != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
-/
lemma FermatLastTheoremWith'.fermatLastTheoremWith {R : Type*} [CommSemiring R] [IsDomain R]
    {n : ℕ} (h : FermatLastTheoremWith' R n)
    (hn : ∀ a b c : R, IsUnit a → IsUnit b → IsUnit c → a ^ n + b ^ n ≠ c ^ n) :
    FermatLastTheoremWith R n := by
  intro a b c ha hb hc heq
  rcases h a b c ha hb hc heq with ⟨d, a', b', c', ⟨rfl, rfl, rfl⟩, ⟨ua, ub, uc⟩⟩
  rw [mul_pow, mul_pow, mul_pow, ← add_mul] at heq
  exact hn _ _ _ ua ub uc <| mul_right_cancel₀ (pow_ne_zero _ (right_ne_zero_of_mul ha)) heq
/-
**fermatLastTheoremWith'_iff_fermatLastTheoremWith** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {R : Type u_2} [inst : CommSemiring R] [IsDomain R] {n : ℕ},   (∀ (a b c
 : R), IsUnit a → IsUnit b → IsUnit c → a ^ n + b ^ n ≠ c ^ n) →     (FermatLast
TheoremWith' R n ↔ FermatLastTheoremWith R n)
参数：∀ (a b c : R), IsUnit a → IsUnit b → IsUnit c → a ^ n + b ^ n ≠ c ^ n；FermatL
astTheoremWith' R n ↔ FermatLastTheoremWith R n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FermatLastTheoremWith'.fermatLastTheoremWith`：∀ {R : Type u_2} [inst : C
ommSemiring R] [IsDomain R] {n : ℕ},   FermatLastTheoremWith' R n →     (∀ (a b 
c : R), IsUnit a → IsUnit b → IsUn…
· 使用引理 `FermatLastTheoremWith.fermatLastTheoremWith'`：FermatLastTheoremWith.ferm
atLastTheoremWith' {R : Type*} [CommSemiring R] {n : Nat} (h : FermatLastTheorem
With R n) : FermatLastTheoremWith'…
-/
lemma fermatLastTheoremWith'_iff_fermatLastTheoremWith {R : Type*} [CommSemiring R] [IsDomain R]
    {n : ℕ} (hn : ∀ a b c : R, IsUnit a → IsUnit b → IsUnit c → a ^ n + b ^ n ≠ c ^ n) :
    FermatLastTheoremWith' R n ↔ FermatLastTheoremWith R n :=
  Iff.intro (fun h ↦ h.fermatLastTheoremWith hn) (fun h ↦ h.fermatLastTheoremWith')
/-
**fermatLastTheoremWith'_nat_int_tfae** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ (n : ℕ), [FermatLastTheoremFor n, FermatLastTheoremWith' ℕ n, FermatLast
TheoremWith' ℤ n].TFAE
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fermatLastTheoremWith'_iff_fermatLastTheoremWith`：∀ {R : Type u_2} [inst
 : CommSemiring R] [IsDomain R] {n : ℕ},   (∀ (a b c : R), IsUnit a → IsUnit b →
 IsUnit c → a ^ n + b ^ n ≠ c ^ n) →  …
· 使用定理 `Nat.instIsDomain`：IsDomain ℕ
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `fermatLastTheoremFor_iff_int`：fermatLastTheoremFor_iff_int {n : Nat} : F
ermatLastTheoremFor n ↔ FermatLastTheoremWith Int n
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Int.isUnit_iff`：isUnit_iff : IsUnit u ↔ u = 1 ∨ u = -1
· 使用定理 `isUnit_pow_iff`：∀ {M : Type u_1} [inst : Monoid M] {n : ℕ} {a : M}, n ≠ 
0 → (IsUnit (a ^ n) ↔ IsUnit a)
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `List.tfae_of_cycle`：tfae_of_cycle {a b} {l : List Prop} (h_chain : List.
IsChain (· -> ·) (a :: b :: l)) (h_last : getLastD l b -> a) : TFAE (a :: b :: l
)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
lemma fermatLastTheoremWith'_nat_int_tfae (n : ℕ) :
    TFAE [FermatLastTheoremFor n, FermatLastTheoremWith' ℕ n, FermatLastTheoremWith' ℤ n] := by
  tfae_have 2 ↔ 1 := by
    apply fermatLastTheoremWith'_iff_fermatLastTheoremWith
    simp only [Nat.isUnit_iff]
    intro _ _ _ ha hb hc
    rw [ha, hb, hc]
    simp only [one_pow, Nat.reduceAdd, ne_eq, OfNat.ofNat_ne_one, not_false_eq_true]
  tfae_have 3 ↔ 1 := by
    rw [fermatLastTheoremFor_iff_int]
    apply fermatLastTheoremWith'_iff_fermatLastTheoremWith
    intro a b c ha hb hc
    by_cases hn : n = 0
    · subst hn
      simp only [pow_zero, Int.reduceAdd, ne_eq, OfNat.ofNat_ne_one, not_false_eq_true]
    · rw [← isUnit_pow_iff hn, Int.isUnit_iff] at ha hb hc
      -- case division
      rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hc with hc | hc <;>
        rw [ha, hb, hc] <;> decide
  tfae_finish

open Finset in
/-- To prove Fermat Last Theorem in any semiring that is a `NormalizedGCDMonoid` one can assume
that the `gcd` of `{a, b, c}` is `1`. -/
/-
**fermatLastTheoremWith_of_fermatLastTheoremWith_coprime** 是 Mathlib 中的一个引理，位于命名
空间 ``。
形式化陈述：fermatLastTheoremWith_of_fermatLastTheoremWith_coprime {n : Nat} {R : Type
*} [CommSemiring R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] (hn : f
orall a b c : R, a != 0 -> b != 0 -> c != 0 -> ({a, b, c} : Finset R).gcd id = 1
 -> a ^ n + b ^ n != c ^ n) : FermatLastTheoremWith R n
参数：hn : forall a b c : R, a != 0 -> b != 0 -> c != 0 -> ({a, b, c} : Finset R).g
cd id = 1 -> a ^ n + b ^ n != c ^ n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.gcd_dvd`：gcd_dvd {b : β} (hb : b in s) : s.gcd f ∣ f b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.normalize_gcd`：normalize_gcd : normalize (s.gcd f) = s.gcd f
· 使用定理 `normalize_eq_one`：normalize_eq_one {x : α} : normalize x = 1 ↔ IsUnit x 
where mp hx
· 使用定理 `isUnit_of_associated_mul`：isUnit_of_associated_mul [CommMonoidWithZero M
] [IsCancelMulZero M] {p b : M} (h : Associated (p * b) p) (hp : p != 0) : IsUni
t b
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用引理 `Mathlib.Tactic.GCongr.rel_imp_rel`：rel_imp_rel (h₁ : r c a) (h₂ : r b d)
 : r a b -> r c d
· 使用定理 `Associated.instIsTrans`：∀ {M : Type u_1} [inst : Monoid M], IsTrans M As
sociated
· 使用定理 `Associated.symm`：∀ {M : Type u_1} [inst : Monoid M] {x y : M}, Associate
d x y → Associated y x
· 使用定理 `Finset.gcd_mul_left'`：∀ {α : Type u_2} {β : Type u_3} [inst : CommMonoid
WithZero α] [inst_1 : NormalizedGCDMonoid α] (s : Finset β)   (f : β → α) (a : α
), Associa…
· 使用定理 `Associated.refl`：∀ {M : Type u_1} [inst : Monoid M] (x : M), Associated 
x x
· 使用定理 `Finset.gcd_eq_gcd_image`：gcd_eq_gcd_image [DecidableEq α] : s.gcd f = (s
.image f).gcd id
· 使用定理 `Associated.of_eq`：Associated.of_eq [Monoid M] {a b : M} (h : a = b) : a 
~ᵤ b
· 使用定理 `Finset.image_insert`：image_insert [DecidableEq α] (f : α -> β) (a : α) (
s : Finset α) : (insert a s).image f = insert (f a) (s.image f)
· 使用定理 `Finset.image_singleton`：image_singleton (f : α -> β) (a : α) : image f {
a} = {f a}
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `mul_right_inj'`：mul_right_inj' (ha : a != 0) : a * b = a * c ↔ b = c
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
To prove Fermat Last Theorem in any semiring that is a `NormalizedGCDMonoid` one
 can assume
that the `gcd` of `{a, b, c}` is `1`.
-/
lemma fermatLastTheoremWith_of_fermatLastTheoremWith_coprime {n : ℕ} {R : Type*} [CommSemiring R]
    [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R]
    (hn : ∀ a b c : R, a ≠ 0 → b ≠ 0 → c ≠ 0 → ({a, b, c} : Finset R).gcd id = 1 →
      a ^ n + b ^ n ≠ c ^ n) :
    FermatLastTheoremWith R n := by
  intro a b c ha hb hc habc
  let s : Finset R := {a, b, c}; let d := s.gcd id
  obtain ⟨A, hA⟩ : d ∣ a := gcd_dvd (by simp [s])
  obtain ⟨B, hB⟩ : d ∣ b := gcd_dvd (by simp [s])
  obtain ⟨C, hC⟩ : d ∣ c := gcd_dvd (by simp [s])
  simp only [hA, hB, hC, mul_ne_zero_iff, mul_pow] at ha hb hc habc
  rw [← mul_add, mul_right_inj' (pow_ne_zero n ha.1)] at habc
  refine hn A B C ha.2 hb.2 hc.2 ?_ habc
  rw [← Finset.normalize_gcd, normalize_eq_one]
  refine isUnit_of_associated_mul ?_ ha.1
  grw [← Finset.gcd_mul_left', gcd_eq_gcd_image]
  refine .of_eq ?_; congr; simp [s, hA, hB, hC]
/-
**dvd_c_of_prime_of_dvd_a_of_dvd_b_of_FLT** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：dvd_c_of_prime_of_dvd_a_of_dvd_b_of_FLT {n : Nat} {p : Int} (hp : Prime p)
 {a b c : Int} (hpa : p ∣ a) (hpb : p ∣ b) (HF : a ^ n + b ^ n + c ^ n = 0) : p 
∣ c
参数：hp : Prime p；hpa : p ∣ a；hpb : p ∣ b；HF : a ^ n + b ^ n + c ^ n = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Prime.dvd_of_dvd_pow`：dvd_of_dvd_pow {a : M} {n : Nat} (h : p ∣ a ^ n) :
 p ∣ a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `dvd_neg`：dvd_neg : a ∣ -b ↔ a ∣ b
· 使用定理 `dvd_add`：dvd_add [LeftDistribClass α] {a b c : α} (h₁ : a ∣ b) (h₂ : a ∣
 c) : a ∣ b + c
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用引理 `dvd_pow`：dvd_pow (hab : a ∣ b) : forall {n : Nat} (_ : n != 0), a ∣ b ^ 
n | 0, hn => (hn rfl).elim | n + 1, _ => by rw [pow_succ']; exact hab.mul_rig…
· 使用定理 `add_eq_zero_iff_eq_neg`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, 
a + b = 0 ↔ a = -b
-/
lemma dvd_c_of_prime_of_dvd_a_of_dvd_b_of_FLT {n : ℕ} {p : ℤ} (hp : Prime p) {a b c : ℤ}
    (hpa : p ∣ a) (hpb : p ∣ b) (HF : a ^ n + b ^ n + c ^ n = 0) : p ∣ c := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp at HF
  refine hp.dvd_of_dvd_pow (n := n) (dvd_neg.1 ?_)
  rw [add_eq_zero_iff_eq_neg] at HF
  exact HF.symm ▸ dvd_add (dvd_pow hpa hn) (dvd_pow hpb hn)
/-
**isCoprime_of_gcd_eq_one_of_FLT** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isCoprime_of_gcd_eq_one_of_FLT {n : Nat} {a b c : Int} (Hgcd : Finset.gcd 
{a, b, c} id = 1) (HF : a ^ n + b ^ n + c ^ n = 0) : IsCoprime a b
参数：Hgcd : Finset.gcd {a, b, c} id = 1；HF : a ^ n + b ^ n + c ^ n = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isCoprime_of_prime_dvd`：isCoprime_of_prime_dvd {x y : R} (nonzero : ¬(x 
= 0 ∧ y = 0)) (H : forall z : R, Prime z -> z ∣ x -> ¬z ∣ y) : IsCoprime x y
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `Finset.insert_eq_of_mem`：insert_eq_of_mem (h : a in s) : insert a s = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.gcd_singleton`：gcd_singleton {b : β} : ({b} : Finset β).gcd f = n
ormalize (f b)
· 使用定理 `normalize_zero`：∀ {α : Type u_1} [inst : MonoidWithZero α] [inst_1 : Nor
malizationMonoid α], normalize 0 = 0
· 使用定理 `Int.instNeZeroOfNatOfNat`：∀ {n : ℕ} [NeZero n], NeZero (OfNat.ofNat n)
· 使用定理 `Prime.not_dvd_one`：not_dvd_one : ¬p ∣ 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.dvd_gcd_iff`：dvd_gcd_iff {a : α} : a ∣ s.gcd f ↔ forall b in s, a
 ∣ f b
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
（共 31 条，此处仅展示前 30 条）
-/
lemma isCoprime_of_gcd_eq_one_of_FLT {n : ℕ} {a b c : ℤ} (Hgcd : Finset.gcd {a, b, c} id = 1)
    (HF : a ^ n + b ^ n + c ^ n = 0) : IsCoprime a b := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [pow_zero, Int.reduceAdd, OfNat.ofNat_ne_zero] at HF
  refine isCoprime_of_prime_dvd ?_ <| (fun p hp hpa hpb ↦ hp.not_dvd_one ?_)
  · rintro ⟨rfl, rfl⟩
    simp only [ne_eq, hn, not_false_eq_true, zero_pow, add_zero, zero_add, pow_eq_zero_iff]
      at HF
    simp only [HF, Finset.mem_singleton, Finset.insert_eq_of_mem, Finset.gcd_singleton, id_eq,
      normalize_zero, zero_ne_one] at Hgcd
  · rw [← Hgcd]
    refine Finset.dvd_gcd_iff.mpr fun x hx ↦ ?_
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx | hx <;> simp only [id_eq, hx, hpa, hpb,
      dvd_c_of_prime_of_dvd_a_of_dvd_b_of_FLT hp hpa hpb HF]
