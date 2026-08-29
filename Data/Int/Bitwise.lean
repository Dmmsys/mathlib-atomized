/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
module

public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Nat.Size
public import Batteries.Data.Int
import all Init.Data.Nat.Bitwise.Basic -- for unfolding `Nat.bitwise`

/-!
# Bitwise operations on integers

Possibly only of archaeological significance.

## Recursors
* `Int.bitCasesOn`: Parity disjunction. Something is true/defined on `ℤ` if it's true/defined for
  even and for odd values.
-/

@[expose] public section

namespace Int

/--
Definition of `div2` / `div2` 的定义

English:
definition div2
  signature: : Int -> Int

中文:
定义 div2
  签名: : 整数 -> 整数
-/
def div2 : Int -> Int
  | (n : Nat) => n.div2
  | -[n+1] => negSucc n.div2

/--
Definition of `bodd` / `bodd` 的定义

English:
definition bodd
  signature: : Int -> Bool

中文:
定义 bodd
  签名: : 整数 -> 布尔值
-/
def bodd : Int -> Bool
  | (n : Nat) => n.bodd
  | -[n+1] => not (n.bodd)

/--
Definition of `bit` / `bit` 的定义

English:
definition bit
  signature: (b : Bool)
  body: cond b (2 * · + 1) (2 * ·)

中文:
定义 bit
  签名: (b : 布尔值)
  定义体: cond b (2 * · + 1) (2 * ·)
-/
def bit (b : Bool) : Int -> Int :=
  cond b (2 * · + 1) (2 * ·)

/--
Definition of `natBitwise` / `natBitwise` 的定义

English:
definition natBitwise
  signature: (f : Bool -> Bool -> Bool) (m n : Nat)
  body: cond (f false false) -[Nat.bitwise (fun x y => not (f x y)) m n+1] (Nat.bitwise f m n)

中文:
定义 natBitwise
  签名: (f : 布尔值 -> 布尔值 -> 布尔值) (m n : 自然数)
  定义体: cond (f false false) -[Nat.bitwise (fun x y => not (f x y)) m n+1] (Nat.bitwise f m n)

Depends on / 依赖: Nat.bitwise, bitwise
-/
def natBitwise (f : Bool -> Bool -> Bool) (m n : Nat) : Int :=
  cond (f false false) -[Nat.bitwise (fun x y => not (f x y)) m n+1] (Nat.bitwise f m n)

/--
Definition of `bitwise` / `bitwise` 的定义

English:
definition bitwise
  signature: (f : Bool -> Bool -> Bool)

中文:
定义 bitwise
  签名: (f : 布尔值 -> 布尔值 -> 布尔值)
-/
def bitwise (f : Bool -> Bool -> Bool) : Int -> Int -> Int
  | (m : Nat), (n : Nat) => natBitwise f m n
  | (m : Nat), -[n+1] => natBitwise (fun x y => f x (not y)) m n
  | -[m+1], (n : Nat) => natBitwise (fun x y => f (not x) y) m n
  | -[m+1], -[n+1] => natBitwise (fun x y => f (not x) (not y)) m n

/--
Definition of `lnot` / `lnot` 的定义

English:
definition lnot
  signature: : Int -> Int

中文:
定义 lnot
  签名: : 整数 -> 整数
-/
def lnot : Int -> Int
  | (m : Nat) => -[m+1]
  | -[m+1] => m

/--
Definition of `lor` / `lor` 的定义

English:
definition lor
  signature: : Int -> Int -> Int

中文:
定义 lor
  签名: : 整数 -> 整数 -> 整数
-/
def lor : Int -> Int -> Int
  | (m : Nat), (n : Nat) => m ||| n
  | (m : Nat), -[n+1] => -[Nat.ldiff n m+1]
  | -[m+1], (n : Nat) => -[Nat.ldiff m n+1]
  | -[m+1], -[n+1] => -[m &&& n+1]

/--
Definition of `land` / `land` 的定义

English:
definition land
  signature: : Int -> Int -> Int

中文:
定义 land
  签名: : 整数 -> 整数 -> 整数
-/
def land : Int -> Int -> Int
  | (m : Nat), (n : Nat) => m &&& n
  | (m : Nat), -[n+1] => Nat.ldiff m n
  | -[m+1], (n : Nat) => Nat.ldiff n m
  | -[m+1], -[n+1] => -[m ||| n+1]

/--
Definition of `ldiff` / `ldiff` 的定义

English:
definition ldiff
  signature: : Int -> Int -> Int

中文:
定义 ldiff
  签名: : 整数 -> 整数 -> 整数
-/
def ldiff : Int -> Int -> Int
  | (m : Nat), (n : Nat) => Nat.ldiff m n
  | (m : Nat), -[n+1] => m &&& n
  | -[m+1], (n : Nat) => -[m ||| n+1]
  | -[m+1], -[n+1] => Nat.ldiff n m

/--
Definition of `xor` / `xor` 的定义

English:
definition xor
  signature: : Int -> Int -> Int

中文:
定义 xor
  签名: : 整数 -> 整数 -> 整数
-/
protected def xor : Int -> Int -> Int
  | (m : Nat), (n : Nat) => (m ^^^ n)
  | (m : Nat), -[n+1] => -[(m ^^^ n)+1]
  | -[m+1], (n : Nat) => -[(m ^^^ n)+1]
  | -[m+1], -[n+1] => (m ^^^ n)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ShiftLeft Int

中文:
实例 :
  签名: ShiftLeft 整数
-/
instance : ShiftLeft Int where
  shiftLeft
  | (m : Nat), (n : Nat) => Nat.shiftLeft' false m n
  | (m : Nat), -[n+1] => m >>> (Nat.succ n)
  | -[m+1], (n : Nat) => -[Nat.shiftLeft' true m n+1]
  | -[m+1], -[n+1] => -[m >>> (Nat.succ n)+1]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ShiftRight Int
  body: m <<< (-n)

中文:
实例 :
  签名: ShiftRight 整数
  定义体: m <<< (-n)
-/
instance : ShiftRight Int where
  shiftRight m n := m <<< (-n)

/-! ### bitwise ops -/

@[simp]
/--
theorem `bodd_zero` / 定理 `bodd_zero`

English:
theorem bodd_zero
  statement: bodd 0 = false
  proof: rfl

@[simp]

中文:
定理 bodd_zero
  结论: bodd 0 = false
  证明: rfl

@[simp]
-/
theorem bodd_zero : bodd 0 = false :=
  rfl

@[simp]
/--
theorem `bodd_one` / 定理 `bodd_one`

English:
theorem bodd_one
  statement: bodd 1 = true
  proof: rfl

中文:
定理 bodd_one
  结论: bodd 1 = true
  证明: rfl
-/
theorem bodd_one : bodd 1 = true :=
  rfl

/--
theorem `bodd_two` / 定理 `bodd_two`

English:
theorem bodd_two
  statement: bodd 2 = false
  proof: rfl

@[simp, norm_cast]

中文:
定理 bodd_two
  结论: bodd 2 = false
  证明: rfl

@[simp, norm_cast]
-/
theorem bodd_two : bodd 2 = false :=
  rfl

@[simp, norm_cast]
/--
theorem `bodd_coe` / 定理 `bodd_coe`

English:
theorem bodd_coe
  given: (n : Nat)
  statement: Int.bodd n = Nat.bodd n
  proof: rfl

@[simp]

中文:
定理 bodd_coe
  条件: (n : 自然数)
  结论: 整数.bodd n = 自然数.bodd n
  证明: rfl

@[simp]
-/
theorem bodd_coe (n : Nat) : Int.bodd n = Nat.bodd n :=
  rfl

@[simp]
/--
theorem `bodd_subNatNat` / 定理 `bodd_subNatNat`

English:
theorem bodd_subNatNat
  given: (m n : Nat)
  statement: bodd (subNatNat m n) = xor m.bodd n.bodd
  proof: by
  apply subNatNat_elim m n fun m n i => bodd i = xor m.bodd n.bodd <;>
  intro i j <;>
  simp only [Int.bodd, Nat.bodd_add] <;>
  cases Nat.bodd i <;> simp

@[simp]

中文:
定理 bodd_sub自然数自然数
  条件: (m n : 自然数)
  结论: bodd (sub自然数自然数 m n) = xor m.bodd n.bodd
  证明: by
  apply subNatNat_elim m n fun m n i => bodd i = xor m.bodd n.bodd <;>
  intro i j <;>
  simp only [Int.bodd, Nat.bodd_add] <;>
  cases Nat.bodd i <;> simp

@[simp]

Depends on / 依赖: Int.bodd, Nat.bodd, Nat.bodd_add, bodd_add, m.bodd, n.bodd, subNatNat_elim
-/
theorem bodd_subNatNat (m n : Nat) : bodd (subNatNat m n) = xor m.bodd n.bodd := by
  apply subNatNat_elim m n fun m n i => bodd i = xor m.bodd n.bodd <;>
  intro i j <;>
  simp only [Int.bodd, Nat.bodd_add] <;>
  cases Nat.bodd i <;> simp

@[simp]
/--
theorem `bodd_negOfNat` / 定理 `bodd_negOfNat`

English:
theorem bodd_negOfNat
  given: (n : Nat)
  statement: bodd (negOfNat n) = n.bodd
  proof: by
  cases n <;> simp +decide
  rfl

@[simp]

中文:
定理 bodd_negOf自然数
  条件: (n : 自然数)
  结论: bodd (negOf自然数 n) = n.bodd
  证明: by
  cases n <;> simp +decide
  rfl

@[simp]
-/
theorem bodd_negOfNat (n : Nat) : bodd (negOfNat n) = n.bodd := by
  cases n <;> simp +decide
  rfl

@[simp]
/--
theorem `bodd_neg` / 定理 `bodd_neg`

English:
theorem bodd_neg
  given: (n : Int)
  statement: bodd (-n) = bodd n
  proof: by
  cases n <;> simp only [← negOfNat_eq, bodd_negOfNat, neg_negSucc] <;> simp [bodd]

@[simp]

中文:
定理 bodd_neg
  条件: (n : 整数)
  结论: bodd (-n) = bodd n
  证明: by
  cases n <;> simp only [← negOfNat_eq, bodd_negOfNat, neg_negSucc] <;> simp [bodd]

@[simp]

Depends on / 依赖: bodd_negOfNat, negOfNat_eq, neg_negSucc
-/
theorem bodd_neg (n : Int) : bodd (-n) = bodd n := by
  cases n <;> simp only [← negOfNat_eq, bodd_negOfNat, neg_negSucc] <;> simp [bodd]

@[simp]
/--
theorem `bodd_add` / 定理 `bodd_add`

English:
theorem bodd_add
  given: (m n : Int)
  statement: bodd (m + n) = xor (bodd m) (bodd n)
  proof: by
  rcases m with m | m <;>
  rcases n with n | n <;>
  simp only [ofNat_eq_natCast, ofNat_add_negSucc, negSucc_add_ofNat,
             negSucc_add_negSucc, bodd_subNatNat, ← Nat.cast_add] <;>
  simp [bodd, Bool.xor_comm]

@[simp]

中文:
定理 bodd_add
  条件: (m n : 整数)
  结论: bodd (m + n) = xor (bodd m) (bodd n)
  证明: by
  rcases m with m | m <;>
  rcases n with n | n <;>
  simp only [ofNat_eq_natCast, ofNat_add_negSucc, negSucc_add_ofNat,
             negSucc_add_negSucc, bodd_subNatNat, ← Nat.cast_add] <;>
  simp [bodd, Bool.xor_comm]

@[simp]

Depends on / 依赖: Bool.xor_comm, Nat.cast_add, bodd_subNatNat, cast_add, negSucc_add_negSucc, negSucc_add_ofNat, ofNat_add_negSucc, ofNat_eq_natCast, xor_comm
-/
theorem bodd_add (m n : Int) : bodd (m + n) = xor (bodd m) (bodd n) := by
  rcases m with m | m <;>
  rcases n with n | n <;>
  simp only [ofNat_eq_natCast, ofNat_add_negSucc, negSucc_add_ofNat,
             negSucc_add_negSucc, bodd_subNatNat, ← Nat.cast_add] <;>
  simp [bodd, Bool.xor_comm]

@[simp]
/--
theorem `bodd_mul` / 定理 `bodd_mul`

English:
theorem bodd_mul
  given: (m n : Int)
  statement: bodd (m * n) = (bodd m && bodd n)
  proof: by
  rcases m with m | m <;> rcases n with n | n <;>
  simp only [ofNat_eq_natCast, ofNat_mul_negSucc, negSucc_mul_ofNat, ofNat_mul_ofNat,
             negSucc_mul_negSucc] <;>
  simp only [negSucc_eq, ← Int.natCast_succ, bodd_neg, bodd_coe, Nat.bodd_mul]

中文:
定理 bodd_mul
  条件: (m n : 整数)
  结论: bodd (m * n) = (bodd m && bodd n)
  证明: by
  rcases m with m | m <;> rcases n with n | n <;>
  simp only [ofNat_eq_natCast, ofNat_mul_negSucc, negSucc_mul_ofNat, ofNat_mul_ofNat,
             negSucc_mul_negSucc] <;>
  simp only [negSucc_eq, ← Int.natCast_succ, bodd_neg, bodd_coe, Nat.bodd_mul]

Depends on / 依赖: Int.natCast_succ, Nat.bodd_mul, bodd_coe, bodd_mul, bodd_neg, natCast_succ, negSucc_eq, negSucc_mul_negSucc, negSucc_mul_ofNat, ofNat_eq_natCast, ofNat_mul_negSucc, ofNat_mul_ofNat
-/
theorem bodd_mul (m n : Int) : bodd (m * n) = (bodd m && bodd n) := by
  rcases m with m | m <;> rcases n with n | n <;>
  simp only [ofNat_eq_natCast, ofNat_mul_negSucc, negSucc_mul_ofNat, ofNat_mul_ofNat,
             negSucc_mul_negSucc] <;>
  simp only [negSucc_eq, ← Int.natCast_succ, bodd_neg, bodd_coe, Nat.bodd_mul]

/--
theorem `bodd_add_div2` / 定理 `bodd_add_div2`

English:
theorem bodd_add_div2
  statement: forall n, cond (bodd n) 1 0 + 2 * div2 n = n

中文:
定理 bodd_add_div2
  结论: 对任意 n, cond (bodd n) 1 0 + 2 * div2 n = n
-/
theorem bodd_add_div2 : forall n, cond (bodd n) 1 0 + 2 * div2 n = n
  | (n : Nat) => by
    rw [show (cond (bodd n) 1 0 : Int) = (cond (bodd n) 1 0 : Nat) by cases bodd n <;> rfl]
    exact congr_arg ofNat n.bodd_add_div2
  | -[n+1] => by
    refine Eq.trans ?_ (congr_arg negSucc n.bodd_add_div2)
    dsimp [bodd]; cases Nat.bodd n <;> dsimp [cond, not, div2, Int.mul]
    · change -[2 * Nat.div2 n+1] = _
      rw [zero_add]
    · rw [zero_add, add_comm]
      rfl

/--
theorem `div2_val` / 定理 `div2_val`

English:
theorem div2_val
  statement: forall n, div2 n = n / 2

中文:
定理 div2_val
  结论: 对任意 n, div2 n = n / 2
-/
theorem div2_val : forall n, div2 n = n / 2
  | (n : Nat) => congr_arg ofNat n.div2_val
  | -[n+1] => congr_arg negSucc n.div2_val

/--
theorem `bit_val` / 定理 `bit_val`

English:
theorem bit_val
  given: (b n)
  statement: bit b n = 2 * n + cond b 1 0
  proof: by
  cases b
  · apply (add_zero _).symm
  · rfl

中文:
定理 bit_val
  条件: (b n)
  结论: bit b n = 2 * n + cond b 1 0
  证明: by
  cases b
  · apply (add_zero _).symm
  · rfl

Depends on / 依赖: add_zero
-/
theorem bit_val (b n) : bit b n = 2 * n + cond b 1 0 := by
  cases b
  · apply (add_zero _).symm
  · rfl

/--
theorem `bit_decomp` / 定理 `bit_decomp`

English:
theorem bit_decomp
  given: (n : Int)
  statement: bit (bodd n) (div2 n) = n
  proof: (bit_val _ _).trans (add_comm _ _).trans bodd_add_div2 _

中文:
定理 bit_decomp
  条件: (n : 整数)
  结论: bit (bodd n) (div2 n) = n
  证明: (bit_val _ _).trans (add_comm _ _).trans bodd_add_div2 _

Depends on / 依赖: add_comm, bit_val, bodd_add_div2
-/
theorem bit_decomp (n : Int) : bit (bodd n) (div2 n) = n :=
(bit_val _ _).trans (add_comm _ _).trans bodd_add_div2 _

/--
Definition of `bitCasesOn.` / `bitCasesOn.` 的定义

English:
definition bitCasesOn.{u}
  signature: {C : Int -> Sort u} (n) (h : forall b n, C (bit b n))
  body: by
  rw [← bit_decomp n]
  apply h

@[simp]

中文:
定义 bitCasesOn.{u}
  签名: {C : 整数 -> 类型层 u} (n) (h : 对任意 b n, C (bit b n))
  定义体: by
  rw [← bit_decomp n]
  apply h

@[simp]

Depends on / 依赖: bit_decomp
-/
def bitCasesOn.{u} {C : Int -> Sort u} (n) (h : forall b n, C (bit b n)) : C n := by
  rw [← bit_decomp n]
  apply h

@[simp]
/--
theorem `bit_zero` / 定理 `bit_zero`

English:
theorem bit_zero
  statement: bit false 0 = 0
  proof: rfl

@[simp]

中文:
定理 bit_zero
  结论: bit false 0 = 0
  证明: rfl

@[simp]
-/
theorem bit_zero : bit false 0 = 0 :=
  rfl

@[simp]
/--
theorem `bit_coe_nat` / 定理 `bit_coe_nat`

English:
theorem bit_coe_nat
  given: (b) (n : Nat)
  statement: bit b n = Nat.bit b n
  proof: by
  rw [bit_val]; rw [Nat.bit_val]
  cases b <;> rfl

@[simp]

中文:
定理 bit_coe_nat
  条件: (b) (n : 自然数)
  结论: bit b n = 自然数.bit b n
  证明: by
  rw [bit_val]; rw [Nat.bit_val]
  cases b <;> rfl

@[simp]

Depends on / 依赖: Nat.bit_val, bit_val
-/
theorem bit_coe_nat (b) (n : Nat) : bit b n = Nat.bit b n := by
  rw [bit_val]; rw [Nat.bit_val]
  cases b <;> rfl

@[simp]
/--
theorem `bit_negSucc` / 定理 `bit_negSucc`

English:
theorem bit_negSucc
  given: (b) (n : Nat)
  statement: bit b -[n+1] = -[Nat.bit (not b) n+1]
  proof: by
  rw [bit_val]; rw [Nat.bit_val]
  cases b <;> rfl

@[simp]

中文:
定理 bit_negSucc
  条件: (b) (n : 自然数)
  结论: bit b -[n+1] = -[自然数.bit (not b) n+1]
  证明: by
  rw [bit_val]; rw [Nat.bit_val]
  cases b <;> rfl

@[simp]

Depends on / 依赖: Nat.bit_val, bit_val
-/
theorem bit_negSucc (b) (n : Nat) : bit b -[n+1] = -[Nat.bit (not b) n+1] := by
  rw [bit_val]; rw [Nat.bit_val]
  cases b <;> rfl

@[simp]
/--
theorem `bodd_bit` / 定理 `bodd_bit`

English:
theorem bodd_bit
  given: (b n)
  statement: bodd (bit b n) = b
  proof: by
  rw [bit_val]
  cases b <;> cases bodd n <;> simp [(show bodd 2 = false by rfl)]

@[simp]

中文:
定理 bodd_bit
  条件: (b n)
  结论: bodd (bit b n) = b
  证明: by
  rw [bit_val]
  cases b <;> cases bodd n <;> simp [(show bodd 2 = false by rfl)]

@[simp]

Depends on / 依赖: bit_val
-/
theorem bodd_bit (b n) : bodd (bit b n) = b := by
  rw [bit_val]
  cases b <;> cases bodd n <;> simp [(show bodd 2 = false by rfl)]

@[simp]
/--
theorem `testBit_bit_zero` / 定理 `testBit_bit_zero`

English:
theorem testBit_bit_zero
  given: (b)
  statement: forall n, testBit (bit b n) 0 = b

中文:
定理 testBit_bit_zero
  条件: (b)
  结论: 对任意 n, testBit (bit b n) 0 = b
-/
theorem testBit_bit_zero (b) : forall n, testBit (bit b n) 0 = b
  | (n : Nat) => by rw [bit_coe_nat]; apply Nat.testBit_bit_zero
  | -[n+1] => by
    rw [bit_negSucc]; dsimp [testBit]; rw [Nat.testBit_bit_zero, Bool.not_not]

@[simp]
/--
theorem `testBit_bit_succ` / 定理 `testBit_bit_succ`

English:
theorem testBit_bit_succ
  given: (m b)
  statement: forall n, testBit (bit b n) (Nat.succ m) = testBit n m

中文:
定理 testBit_bit_succ
  条件: (m b)
  结论: 对任意 n, testBit (bit b n) (自然数.succ m) = testBit n m
-/
theorem testBit_bit_succ (m b) : forall n, testBit (bit b n) (Nat.succ m) = testBit n m
  | (n : Nat) => by rw [bit_coe_nat]; apply Nat.testBit_bit_succ
  | -[n+1] => by
    dsimp only [testBit]
    simp only [bit_negSucc]
    cases b <;> simp only [Bool.not_false, Bool.not_true, Nat.testBit_bit_succ]

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11215): TODO
-- private unsafe def bitwise_tac : tactic Unit :=
-- sorry

-- Porting note: Was `bitwise_tac` in mathlib
/--
theorem `bitwise_or` / 定理 `bitwise_or`

English:
theorem bitwise_or
  statement: bitwise or = lor
  proof: by
  funext m n
  rcases m with m | m <;> rcases n with n | n <;> try {rfl}
    <;> simp only [bitwise, natBitwise, Bool.not_false, Bool.or_true, cond_true, lor, Nat.ldiff,
      negSucc.injEq, Bool.true_or]
  · rw [Nat.bitwise_swap, Function.swap]
    congr
    funext x y
    cases x <;> cases y <;

中文:
定理 bitwise_or
  结论: bitwise or = lor
  证明: by
  funext m n
  rcases m with m | m <;> rcases n with n | n <;> try {rfl}
    <;> simp only [bitwise, natBitwise, Bool.not_false, Bool.or_true, cond_true, lor, Nat.ldiff,
      negSucc.injEq, Bool.true_or]
  · rw [Nat.bitwise_swap, Function.swap]
    congr
    funext x y
    cases x <;> cases y <;

Depends on / 依赖: Bool.not_false, Bool.or_true, Bool.true_or, Function, Function.swap, Nat.bitwise_swap, Nat.ldiff, bitwise, bitwise_swap, cond_true, natBitwise, negSucc, negSucc.injEq, not_false, or_true, true_or
-/
theorem bitwise_or : bitwise or = lor := by
  funext m n
  rcases m with m | m <;> rcases n with n | n <;> try {rfl}
    <;> simp only [bitwise, natBitwise, Bool.not_false, Bool.or_true, cond_true, lor, Nat.ldiff,
      negSucc.injEq, Bool.true_or]
  · rw [Nat.bitwise_swap, Function.swap]
    congr
    funext x y
    cases x <;> cases y <;> rfl
  · simp
  · congr
    simp

-- Porting note: Was `bitwise_tac` in mathlib
/--
theorem `bitwise_and` / 定理 `bitwise_and`

English:
theorem bitwise_and
  statement: bitwise and = land
  proof: by
  funext m n
  rcases m with m | m <;> rcases n with n | n <;> try {rfl}
    <;> simp only [bitwise, natBitwise, Bool.not_false,
      cond_false, cond_true, Bool.and_true,
      Bool.and_false]
  · rw [Nat.bitwise_swap, Function.swap]
    congr
    funext x y
    cases x <;> cases y <;> rfl
  · 

中文:
定理 bitwise_and
  结论: bitwise and = land
  证明: by
  funext m n
  rcases m with m | m <;> rcases n with n | n <;> try {rfl}
    <;> simp only [bitwise, natBitwise, Bool.not_false,
      cond_false, cond_true, Bool.and_true,
      Bool.and_false]
  · rw [Nat.bitwise_swap, Function.swap]
    congr
    funext x y
    cases x <;> cases y <;> rfl
  · 

Depends on / 依赖: Bool.and_false, Bool.and_true, Bool.not_false, Function, Function.swap, Nat.bitwise_swap, and_false, and_true, bitwise, bitwise_swap, cond_false, cond_true, natBitwise, not_false
-/
theorem bitwise_and : bitwise and = land := by
  funext m n
  rcases m with m | m <;> rcases n with n | n <;> try {rfl}
    <;> simp only [bitwise, natBitwise, Bool.not_false,
      cond_false, cond_true, Bool.and_true,
      Bool.and_false]
  · rw [Nat.bitwise_swap, Function.swap]
    congr
    funext x y
    cases x <;> cases y <;> rfl
  · congr
    simp

-- Porting note: Was `bitwise_tac` in mathlib
/--
theorem `bitwise_diff` / 定理 `bitwise_diff`

English:
theorem bitwise_diff
  statement: (bitwise fun a b => a && not b) = ldiff
  proof: by
  funext m n
  rcases m with m | m <;> rcases n with n | n <;> try {rfl}
    <;> simp only [bitwise, natBitwise, Bool.not_false,
      cond_false, cond_true, Nat.ldiff, Bool.and_true, negSucc.injEq,
      Bool.and_false, Bool.not_true, ldiff]
  · congr
    simp
  · congr
    simp
  · rw [Nat.bitw

中文:
定理 bitwise_diff
  结论: (bitwise fun a b => a && not b) = ldiff
  证明: by
  funext m n
  rcases m with m | m <;> rcases n with n | n <;> try {rfl}
    <;> simp only [bitwise, natBitwise, Bool.not_false,
      cond_false, cond_true, Nat.ldiff, Bool.and_true, negSucc.injEq,
      Bool.and_false, Bool.not_true, ldiff]
  · congr
    simp
  · congr
    simp
  · rw [Nat.bitw

Depends on / 依赖: Bool.and_false, Bool.and_true, Bool.not_false, Bool.not_true, Function, Function.swap, Nat.bitwise_swap, Nat.ldiff, and_false, and_true, bitwise, bitwise_swap, cond_false, cond_true, natBitwise, negSucc, negSucc.injEq, not_false, not_true
-/
theorem bitwise_diff : (bitwise fun a b => a && not b) = ldiff := by
  funext m n
  rcases m with m | m <;> rcases n with n | n <;> try {rfl}
    <;> simp only [bitwise, natBitwise, Bool.not_false,
      cond_false, cond_true, Nat.ldiff, Bool.and_true, negSucc.injEq,
      Bool.and_false, Bool.not_true, ldiff]
  · congr
    simp
  · congr
    simp
  · rw [Nat.bitwise_swap, Function.swap]
    congr
    funext x y
    cases x <;> cases y <;> rfl

-- Porting note: Was `bitwise_tac` in mathlib
/--
theorem `bitwise_xor` / 定理 `bitwise_xor`

English:
theorem bitwise_xor
  statement: bitwise xor = Int.xor
  proof: by
  funext m n
  rcases m with m | m <;> rcases n with n | n <;> try {rfl}
    <;> simp only [bitwise, natBitwise, Bool.not_false, Bool.bne_eq_xor,
      cond_false, cond_true, negSucc.injEq, Bool.false_xor,
      Bool.true_xor, Bool.not_true,
      Int.xor, HXor.hXor, XorOp.xor, Nat.xor] <;> simp


中文:
定理 bitwise_xor
  结论: bitwise xor = 整数.xor
  证明: by
  funext m n
  rcases m with m | m <;> rcases n with n | n <;> try {rfl}
    <;> simp only [bitwise, natBitwise, Bool.not_false, Bool.bne_eq_xor,
      cond_false, cond_true, negSucc.injEq, Bool.false_xor,
      Bool.true_xor, Bool.not_true,
      Int.xor, HXor.hXor, XorOp.xor, Nat.xor] <;> simp


Depends on / 依赖: Bool.bne_eq_xor, Bool.false_xor, Bool.not_false, Bool.not_true, Bool.true_xor, HXor.hXor, Int.xor, Nat.xor, XorOp.xor, bitwise, bne_eq_xor, cond_false, cond_true, false_xor, natBitwise, negSucc, negSucc.injEq, not_false, not_true, true_xor
-/
theorem bitwise_xor : bitwise xor = Int.xor := by
  funext m n
  rcases m with m | m <;> rcases n with n | n <;> try {rfl}
    <;> simp only [bitwise, natBitwise, Bool.not_false, Bool.bne_eq_xor,
      cond_false, cond_true, negSucc.injEq, Bool.false_xor,
      Bool.true_xor, Bool.not_true,
      Int.xor, HXor.hXor, XorOp.xor, Nat.xor] <;> simp

@[simp]
/--
theorem `bitwise_bit` / 定理 `bitwise_bit`

English:
theorem bitwise_bit
  given: (f : Bool -> Bool -> Bool) (a m b n)
  proof: by
  rcases m with m | m <;> rcases n with n | n <;>
  simp [bitwise, ofNat_eq_natCast, bit_coe_nat, natBitwise, Bool.not_false,
    bit_negSucc]
  · by_cases h : f false false <;> simp +decide [h]
  · by_cases h : f false true <;> simp +decide [h]
  · by_cases h : f true false <;> simp +decide [h]


中文:
定理 bitwise_bit
  条件: (f : 布尔值 -> 布尔值 -> 布尔值) (a m b n)
  证明: by
  rcases m with m | m <;> rcases n with n | n <;>
  simp [bitwise, ofNat_eq_natCast, bit_coe_nat, natBitwise, Bool.not_false,
    bit_negSucc]
  · by_cases h : f false false <;> simp +decide [h]
  · by_cases h : f false true <;> simp +decide [h]
  · by_cases h : f true false <;> simp +decide [h]


Depends on / 依赖: Bool.not_false, bit_coe_nat, bit_negSucc, bitwise, natBitwise, not_false, ofNat_eq_natCast
-/
theorem bitwise_bit (f : Bool -> Bool -> Bool) (a m b n) :
    bitwise f (bit a m) (bit b n) = bit (f a b) (bitwise f m n) := by
  rcases m with m | m <;> rcases n with n | n <;>
  simp [bitwise, ofNat_eq_natCast, bit_coe_nat, natBitwise, Bool.not_false,
    bit_negSucc]
  · by_cases h : f false false <;> simp +decide [h]
  · by_cases h : f false true <;> simp +decide [h]
  · by_cases h : f true false <;> simp +decide [h]
  · by_cases h : f true true <;> simp +decide [h]

@[simp]
/--
theorem `lor_bit` / 定理 `lor_bit`

English:
theorem lor_bit
  given: (a m b n)
  statement: lor (bit a m) (bit b n) = bit (a || b) (lor m n)
  proof: by
  rw [← bitwise_or]; rw [bitwise_bit]

@[simp]

中文:
定理 lor_bit
  条件: (a m b n)
  结论: lor (bit a m) (bit b n) = bit (a || b) (lor m n)
  证明: by
  rw [← bitwise_or]; rw [bitwise_bit]

@[simp]

Depends on / 依赖: bitwise_bit, bitwise_or
-/
theorem lor_bit (a m b n) : lor (bit a m) (bit b n) = bit (a || b) (lor m n) := by
  rw [← bitwise_or]; rw [bitwise_bit]

@[simp]
/--
theorem `land_bit` / 定理 `land_bit`

English:
theorem land_bit
  given: (a m b n)
  statement: land (bit a m) (bit b n) = bit (a && b) (land m n)
  proof: by
  rw [← bitwise_and]; rw [bitwise_bit]

@[simp]

中文:
定理 land_bit
  条件: (a m b n)
  结论: land (bit a m) (bit b n) = bit (a && b) (land m n)
  证明: by
  rw [← bitwise_and]; rw [bitwise_bit]

@[simp]

Depends on / 依赖: bitwise_and, bitwise_bit
-/
theorem land_bit (a m b n) : land (bit a m) (bit b n) = bit (a && b) (land m n) := by
  rw [← bitwise_and]; rw [bitwise_bit]

@[simp]
/--
theorem `ldiff_bit` / 定理 `ldiff_bit`

English:
theorem ldiff_bit
  given: (a m b n)
  statement: ldiff (bit a m) (bit b n) = bit (a && not b) (ldiff m n)
  proof: by
  rw [← bitwise_diff]; rw [bitwise_bit]

@[simp]

中文:
定理 ldiff_bit
  条件: (a m b n)
  结论: ldiff (bit a m) (bit b n) = bit (a && not b) (ldiff m n)
  证明: by
  rw [← bitwise_diff]; rw [bitwise_bit]

@[simp]

Depends on / 依赖: bitwise_bit, bitwise_diff
-/
theorem ldiff_bit (a m b n) : ldiff (bit a m) (bit b n) = bit (a && not b) (ldiff m n) := by
  rw [← bitwise_diff]; rw [bitwise_bit]

@[simp]
/--
theorem `lxor_bit` / 定理 `lxor_bit`

English:
theorem lxor_bit
  given: (a m b n)
  statement: Int.xor (bit a m) (bit b n) = bit (xor a b) (Int.xor m n)
  proof: by
  rw [← bitwise_xor]; rw [bitwise_bit]

@[simp]

中文:
定理 lxor_bit
  条件: (a m b n)
  结论: 整数.xor (bit a m) (bit b n) = bit (xor a b) (整数.xor m n)
  证明: by
  rw [← bitwise_xor]; rw [bitwise_bit]

@[simp]

Depends on / 依赖: bitwise_bit, bitwise_xor
-/
theorem lxor_bit (a m b n) : Int.xor (bit a m) (bit b n) = bit (xor a b) (Int.xor m n) := by
  rw [← bitwise_xor]; rw [bitwise_bit]

@[simp]
/--
theorem `lnot_bit` / 定理 `lnot_bit`

English:
theorem lnot_bit
  given: (b)
  statement: forall n, lnot (bit b n) = bit (not b) (lnot n)

中文:
定理 lnot_bit
  条件: (b)
  结论: 对任意 n, lnot (bit b n) = bit (not b) (lnot n)
-/
theorem lnot_bit (b) : forall n, lnot (bit b n) = bit (not b) (lnot n)
  | (n : Nat) => by simp [lnot]
  | -[n+1] => by simp [lnot]

@[simp]
/--
theorem `testBit_bitwise` / 定理 `testBit_bitwise`

English:
theorem testBit_bitwise
  given: (f : Bool -> Bool -> Bool) (m n k)
  proof: by
  cases m <;> cases n <;> simp only [testBit, bitwise, natBitwise]
  · by_cases h : f false false <;> simp [h]
  · by_cases h : f false true <;> simp [h]
  · by_cases h : f true false <;> simp [h]
  · by_cases h : f true true <;> simp [h]

@[simp]

中文:
定理 testBit_bitwise
  条件: (f : 布尔值 -> 布尔值 -> 布尔值) (m n k)
  证明: by
  cases m <;> cases n <;> simp only [testBit, bitwise, natBitwise]
  · by_cases h : f false false <;> simp [h]
  · by_cases h : f false true <;> simp [h]
  · by_cases h : f true false <;> simp [h]
  · by_cases h : f true true <;> simp [h]

@[simp]

Depends on / 依赖: bitwise, natBitwise, testBit
-/
theorem testBit_bitwise (f : Bool -> Bool -> Bool) (m n k) :
    testBit (bitwise f m n) k = f (testBit m k) (testBit n k) := by
  cases m <;> cases n <;> simp only [testBit, bitwise, natBitwise]
  · by_cases h : f false false <;> simp [h]
  · by_cases h : f false true <;> simp [h]
  · by_cases h : f true false <;> simp [h]
  · by_cases h : f true true <;> simp [h]

@[simp]
/--
theorem `testBit_lor` / 定理 `testBit_lor`

English:
theorem testBit_lor
  given: (m n k)
  statement: testBit (lor m n) k = (testBit m k || testBit n k)
  proof: by
  rw [← bitwise_or]; rw [testBit_bitwise]

@[simp]

中文:
定理 testBit_lor
  条件: (m n k)
  结论: testBit (lor m n) k = (testBit m k || testBit n k)
  证明: by
  rw [← bitwise_or]; rw [testBit_bitwise]

@[simp]

Depends on / 依赖: bitwise_or, testBit_bitwise
-/
theorem testBit_lor (m n k) : testBit (lor m n) k = (testBit m k || testBit n k) := by
  rw [← bitwise_or]; rw [testBit_bitwise]

@[simp]
/--
theorem `testBit_land` / 定理 `testBit_land`

English:
theorem testBit_land
  given: (m n k)
  statement: testBit (land m n) k = (testBit m k && testBit n k)
  proof: by
  rw [← bitwise_and]; rw [testBit_bitwise]

@[simp]

中文:
定理 testBit_land
  条件: (m n k)
  结论: testBit (land m n) k = (testBit m k && testBit n k)
  证明: by
  rw [← bitwise_and]; rw [testBit_bitwise]

@[simp]

Depends on / 依赖: bitwise_and, testBit_bitwise
-/
theorem testBit_land (m n k) : testBit (land m n) k = (testBit m k && testBit n k) := by
  rw [← bitwise_and]; rw [testBit_bitwise]

@[simp]
/--
theorem `testBit_ldiff` / 定理 `testBit_ldiff`

English:
theorem testBit_ldiff
  given: (m n k)
  statement: testBit (ldiff m n) k = (testBit m k && not (testBit n k))
  proof: by
  rw [← bitwise_diff]; rw [testBit_bitwise]

@[simp]

中文:
定理 testBit_ldiff
  条件: (m n k)
  结论: testBit (ldiff m n) k = (testBit m k && not (testBit n k))
  证明: by
  rw [← bitwise_diff]; rw [testBit_bitwise]

@[simp]

Depends on / 依赖: bitwise_diff, testBit_bitwise
-/
theorem testBit_ldiff (m n k) : testBit (ldiff m n) k = (testBit m k && not (testBit n k)) := by
  rw [← bitwise_diff]; rw [testBit_bitwise]

@[simp]
/--
theorem `testBit_lxor` / 定理 `testBit_lxor`

English:
theorem testBit_lxor
  given: (m n k)
  statement: testBit (Int.xor m n) k = xor (testBit m k) (testBit n k)
  proof: by
  rw [← bitwise_xor]; rw [testBit_bitwise]

@[simp]

中文:
定理 testBit_lxor
  条件: (m n k)
  结论: testBit (整数.xor m n) k = xor (testBit m k) (testBit n k)
  证明: by
  rw [← bitwise_xor]; rw [testBit_bitwise]

@[simp]

Depends on / 依赖: bitwise_xor, testBit_bitwise
-/
theorem testBit_lxor (m n k) : testBit (Int.xor m n) k = xor (testBit m k) (testBit n k) := by
  rw [← bitwise_xor]; rw [testBit_bitwise]

@[simp]
/--
theorem `testBit_lnot` / 定理 `testBit_lnot`

English:
theorem testBit_lnot
  statement: forall n k, testBit (lnot n) k = not (testBit n k)

中文:
定理 testBit_lnot
  结论: 对任意 n k, testBit (lnot n) k = not (testBit n k)
-/
theorem testBit_lnot : forall n k, testBit (lnot n) k = not (testBit n k)
  | (n : Nat), k => by simp [lnot, testBit]
  | -[n+1], k => by simp [lnot, testBit]

@[simp]
/--
theorem `shiftLeft_neg` / 定理 `shiftLeft_neg`

English:
theorem shiftLeft_neg
  given: (m n : Int)
  statement: m <<< (-n) = m >>> n
  proof: rfl

@[simp]

中文:
定理 shiftLeft_neg
  条件: (m n : 整数)
  结论: m <<< (-n) = m >>> n
  证明: rfl

@[simp]
-/
theorem shiftLeft_neg (m n : Int) : m <<< (-n) = m >>> n :=
  rfl

@[simp]
/--
theorem `shiftRight_neg` / 定理 `shiftRight_neg`

English:
theorem shiftRight_neg
  given: (m n : Int)
  statement: m >>> (-n) = m <<< n
  proof: by rw [← shiftLeft_neg, neg_neg]

@[simp]

中文:
定理 shiftRight_neg
  条件: (m n : 整数)
  结论: m >>> (-n) = m <<< n
  证明: by rw [← shiftLeft_neg, neg_neg]

@[simp]

Depends on / 依赖: neg_neg, shiftLeft_neg
-/
theorem shiftRight_neg (m n : Int) : m >>> (-n) = m <<< n := by rw [← shiftLeft_neg, neg_neg]

@[simp]
/--
theorem `shiftLeft_natCast` / 定理 `shiftLeft_natCast`

English:
theorem shiftLeft_natCast
  given: (m n : Nat)
  statement: (m : Int) <<< (n : Int) = ↑(m <<< n)
  proof: by
  unfold_projs; simp

@[simp]

中文:
定理 shiftLeft_natCast
  条件: (m n : 自然数)
  结论: (m : 整数) <<< (n : 整数) = ↑(m <<< n)
  证明: by
  unfold_projs; simp

@[simp]

Depends on / 依赖: unfold_projs
-/
theorem shiftLeft_natCast (m n : Nat) : (m : Int) <<< (n : Int) = ↑(m <<< n) := by
  unfold_projs; simp

@[simp]
/--
theorem `shiftRight_natCast` / 定理 `shiftRight_natCast`

English:
theorem shiftRight_natCast
  given: (m n : Nat)
  statement: (m : Int) >>> (n : Int) = m >>> n
  proof: by cases n <;> rfl

@[simp]

中文:
定理 shiftRight_natCast
  条件: (m n : 自然数)
  结论: (m : 整数) >>> (n : 整数) = m >>> n
  证明: by cases n <;> rfl

@[simp]
-/
theorem shiftRight_natCast (m n : Nat) : (m : Int) >>> (n : Int) = m >>> n := by cases n <;> rfl

@[simp]
/--
theorem `shiftLeft_negSucc` / 定理 `shiftLeft_negSucc`

English:
theorem shiftLeft_negSucc
  given: (m n : Nat)
  statement: -[m+1] <<< (n : Int) = -[Nat.shiftLeft' true m n+1]
  proof: rfl

@[simp]

中文:
定理 shiftLeft_negSucc
  条件: (m n : 自然数)
  结论: -[m+1] <<< (n : 整数) = -[自然数.shiftLeft' true m n+1]
  证明: rfl

@[simp]
-/
theorem shiftLeft_negSucc (m n : Nat) : -[m+1] <<< (n : Int) = -[Nat.shiftLeft' true m n+1] :=
  rfl

@[simp]
/--
theorem `shiftRight_negSucc` / 定理 `shiftRight_negSucc`

English:
theorem shiftRight_negSucc
  given: (m n : Nat)
  statement: -[m+1] >>> (n : Int) = -[m >>> n+1]
  proof: by cases n <;> rfl

中文:
定理 shiftRight_negSucc
  条件: (m n : 自然数)
  结论: -[m+1] >>> (n : 整数) = -[m >>> n+1]
  证明: by cases n <;> rfl
-/
theorem shiftRight_negSucc (m n : Nat) : -[m+1] >>> (n : Int) = -[m >>> n+1] := by cases n <;> rfl

/--
theorem `shiftRight_add'` / 定理 `shiftRight_add'`

English:
theorem shiftRight_add'
  statement: forall (m : Int) (n k : Nat), m >>> (n + k : Int) = (m >>> (n : Int)) >>> (k : Int)

中文:
定理 shiftRight_add'
  结论: 对任意 (m : 整数) (n k : 自然数), m >>> (n + k : 整数) = (m >>> (n : 整数)) >>> (k : 整数)
-/
theorem shiftRight_add' : forall (m : Int) (n k : Nat), m >>> (n + k : Int) = (m >>> (n : Int)) >>> (k : Int)
  | (m : Nat), n, k => by
    rw [shiftRight_natCast]; rw [shiftRight_natCast]; rw [← Int.natCast_add]; rw [shiftRight_natCast]; rw [Nat.shiftRight_add]
  | -[m+1], n, k => by
    rw [shiftRight_negSucc]; rw [shiftRight_negSucc]; rw [← Int.natCast_add]; rw [shiftRight_negSucc]; rw [Nat.shiftRight_add]

/-! ### bitwise ops -/

/--
lemma `shiftLeft_natCast_right` / 引理 `shiftLeft_natCast_right`

English:
lemma shiftLeft_natCast_right
  given: (m : Int) (n : Nat)
  proof: by
  rw [Int.shiftLeft_eq']
  unfold_projs; cases m <;> simp only [Nat.shiftLeft'_false, natCast_shiftLeft, ofNat_eq_natCast,
    Nat.pow_eq, Int.natCast_pow, Nat.cast_ofNat, mul_def]
  · grind [Int.shiftLeft_eq']
  · simp only [negSucc_eq, ← natCast_add_one, Nat.shiftLeft'_true_eq_mul_pow]
    grin

中文:
引理 shiftLeft_natCast_right
  条件: (m : 整数) (n : 自然数)
  证明: by
  rw [Int.shiftLeft_eq']
  unfold_projs; cases m <;> simp only [Nat.shiftLeft'_false, natCast_shiftLeft, ofNat_eq_natCast,
    Nat.pow_eq, Int.natCast_pow, Nat.cast_ofNat, mul_def]
  · grind [Int.shiftLeft_eq']
  · simp only [negSucc_eq, ← natCast_add_one, Nat.shiftLeft'_true_eq_mul_pow]
    grin

Depends on / 依赖: Int.natCast_pow, Int.shiftLeft_eq, Nat.cast_ofNat, Nat.pow_eq, Nat.shiftLeft, _false, _true_eq_mul_pow, cast_ofNat, mul_def, natCast_add_one, natCast_pow, natCast_shiftLeft, negSucc_eq, ofNat_eq_natCast, pow_eq, shiftLeft, shiftLeft_eq, unfold_projs
-/
lemma shiftLeft_natCast_right (m : Int) (n : Nat) :
    m <<< (n : Int) = m <<< n := by
  rw [Int.shiftLeft_eq']
  unfold_projs; cases m <;> simp only [Nat.shiftLeft'_false, natCast_shiftLeft, ofNat_eq_natCast,
    Nat.pow_eq, Int.natCast_pow, Nat.cast_ofNat, mul_def]
  · grind [Int.shiftLeft_eq']
  · simp only [negSucc_eq, ← natCast_add_one, Nat.shiftLeft'_true_eq_mul_pow]
    grind

/--
lemma `shiftRight_natCast_right` / 引理 `shiftRight_natCast_right`

English:
lemma shiftRight_natCast_right
  given: (m : Int) (n : Nat)
  proof: by
  cases m <;> simp

中文:
引理 shiftRight_natCast_right
  条件: (m : 整数) (n : 自然数)
  证明: by
  cases m <;> simp
-/
lemma shiftRight_natCast_right (m : Int) (n : Nat) :
    m >>> (n : Int) = m >>> n := by
  cases m <;> simp

/--
theorem `shiftLeft_add'` / 定理 `shiftLeft_add'`

English:
theorem shiftLeft_add'
  statement: forall (m : Int) (n : Nat) (k : Int), m <<< (n + k) = (m <<< (n : Int)) <<< k

中文:
定理 shiftLeft_add'
  结论: 对任意 (m : 整数) (n : 自然数) (k : 整数), m <<< (n + k) = (m <<< (n : 整数)) <<< k
-/
theorem shiftLeft_add' : forall (m : Int) (n : Nat) (k : Int), m <<< (n + k) = (m <<< (n : Int)) <<< k
  | (m : Nat), n, (k : Nat) =>
    congr_arg ofNat (by simp [Nat.shiftLeft_eq, Nat.pow_add, mul_assoc])
  | -[_+1], _, (k : Nat) => congr_arg negSucc (Nat.shiftLeft'_add _ _ _ _)
  | (m : Nat), n, -[k+1] =>
    subNatNat_elim n k.succ (fun n k i => (↑m) <<< i = (Nat.shiftLeft' false m n) >>> k)
      (fun (i n : Nat) => by simp [← Nat.shiftLeft_sub _])
      fun i n => by
        simp_rw [negSucc_eq, shiftLeft_neg, Nat.shiftLeft'_false, Nat.shiftRight_add,
          ← Nat.shiftLeft_sub _ le_rfl, Nat.sub_self, Nat.shiftLeft_zero, ← shiftRight_natCast,
          ← shiftRight_add', Nat.cast_one]
  | -[m+1], n, -[k+1] =>
    subNatNat_elim n k.succ
      (fun n k i => -[m+1] <<< i = -[(Nat.shiftLeft' true m n) >>> k+1])
      (fun i n =>
congr_arg negSucc by
          rw [← Nat.shiftLeft'_sub]; rw [Nat.add_sub_cancel_left]; apply Nat.le_add_right)
      fun i n =>
congr_arg negSucc by rw [add_assoc, Nat.shiftRight_add, ← Nat.shiftLeft'_sub _ _ le_rfl,
          Nat.sub_self, Nat.shiftLeft']

/--
theorem `shiftLeft_sub` / 定理 `shiftLeft_sub`

English:
theorem shiftLeft_sub
  given: (m : Int) (n : Nat) (k : Int)
  statement: m <<< (n - k) = (m <<< (n : Int)) >>> k
  proof: shiftLeft_add' _ _ _

中文:
定理 shiftLeft_sub
  条件: (m : 整数) (n : 自然数) (k : 整数)
  结论: m <<< (n - k) = (m <<< (n : 整数)) >>> k
  证明: shiftLeft_add' _ _ _

Depends on / 依赖: shiftLeft_add
-/
theorem shiftLeft_sub (m : Int) (n : Nat) (k : Int) : m <<< (n - k) = (m <<< (n : Int)) >>> k :=
  shiftLeft_add' _ _ _

/--
theorem `shiftLeft_eq_mul_pow` / 定理 `shiftLeft_eq_mul_pow`

English:
theorem shiftLeft_eq_mul_pow
  statement: forall (m : Int) (n : Nat), m <<< (n : Int) = m * (2 ^ n : Nat)

中文:
定理 shiftLeft_eq_mul_pow
  结论: 对任意 (m : 整数) (n : 自然数), m <<< (n : 整数) = m * (2 ^ n : 自然数)
-/
theorem shiftLeft_eq_mul_pow : forall (m : Int) (n : Nat), m <<< (n : Int) = m * (2 ^ n : Nat)
  | (m : Nat), _ => congr_arg ((↑) : Nat -> Int) (by simp [Nat.shiftLeft_eq])
  | -[_+1], _ => @congr_arg Nat Int _ _ (fun i => -i) (Nat.shiftLeft'_true_eq_mul_pow _ _)

/--
theorem `one_shiftLeft` / 定理 `one_shiftLeft`

English:
theorem one_shiftLeft
  given: (n : Nat)
  statement: 1 <<< (n : Int) = (2 ^ n : Nat)
  proof: congr_arg ((↑) : Nat -> Int) (by simp [Nat.shiftLeft_eq])

中文:
定理 one_shiftLeft
  条件: (n : 自然数)
  结论: 1 <<< (n : 整数) = (2 ^ n : 自然数)
  证明: congr_arg ((↑) : Nat -> Int) (by simp [Nat.shiftLeft_eq])

Depends on / 依赖: Nat.shiftLeft_eq, congr_arg, shiftLeft_eq
-/
theorem one_shiftLeft (n : Nat) : 1 <<< (n : Int) = (2 ^ n : Nat) :=
  congr_arg ((↑) : Nat -> Int) (by simp [Nat.shiftLeft_eq])

/-- Compare with `Int.zero_shiftLeft`, which has `n : ℕ`. -/
@[simp]
/--
theorem `zero_shiftLeft'` / 定理 `zero_shiftLeft'`

English:
theorem zero_shiftLeft'
  statement: forall n : Int, 0 <<< n = 0

中文:
定理 zero_shiftLeft'
  结论: 对任意 n : 整数, 0 <<< n = 0
-/
theorem zero_shiftLeft' : forall n : Int, 0 <<< n = 0
  | (n : Nat) => congr_arg ((↑) : Nat -> Int) (by simp)
  | -[_+1] => congr_arg ((↑) : Nat -> Int) (by simp)

/-- Compare with `Int.zero_shiftRight`, which has `n : ℕ`. -/
@[simp]
/--
theorem `zero_shiftRight'` / 定理 `zero_shiftRight'`

English:
theorem zero_shiftRight'
  given: (n : Int)
  statement: 0 >>> n = 0
  proof: zero_shiftLeft' _

中文:
定理 zero_shiftRight'
  条件: (n : 整数)
  结论: 0 >>> n = 0
  证明: zero_shiftLeft' _

Depends on / 依赖: zero_shiftLeft
-/
theorem zero_shiftRight' (n : Int) : 0 >>> n = 0 :=
  zero_shiftLeft' _

end Int
