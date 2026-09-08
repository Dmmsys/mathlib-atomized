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
import all Init.Data.Nat.Bitwise.Basic  -- for unfolding `Nat.bitwise`

/-!
# Bitwise operations on integers

Possibly only of archaeological significance.

## Recursors
* `Int.bitCasesOn`: Parity disjunction. Something is true/defined on `ℤ` if it's true/defined for
  even and for odd values.
-/

@[expose] public section

namespace Int

/-- `div2 n = n/2` -/
/-
**Int.div2** 是 Mathlib 中的一个定义，位于命名空间 `Int`。
形式化陈述：ℤ → ℤ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`div2 n = n/2`
-/
def div2 : ℤ → ℤ
  | (n : ℕ) => n.div2
  | -[n+1] => negSucc n.div2

/-- `bodd n` returns `true` if `n` is odd -/
/-
**Int.bodd** 是 Mathlib 中的一个定义，位于命名空间 `Int`。
形式化陈述：ℤ → Bool
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`bodd n` returns `true` if `n` is odd
-/
def bodd : ℤ → Bool
  | (n : ℕ) => n.bodd
  | -[n+1] => not (n.bodd)

/-- `bit b` appends the digit `b` to the binary representation of
  its integer input. -/
/-
**Int.bit** 是 Mathlib 中的一个定义，位于命名空间 `Int`。
形式化陈述：bit (b : Bool) : Int -> Int
参数：b : Bool。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`bit b` appends the digit `b` to the binary representation of
  its integer input.
-/
def bit (b : Bool) : ℤ → ℤ :=
  cond b (2 * · + 1) (2 * ·)

/-- `Int.natBitwise` is an auxiliary definition for `Int.bitwise`. -/
/-
**Int.natBitwise** 是 Mathlib 中的一个定义，位于命名空间 `Int`。
形式化陈述：natBitwise (f : Bool -> Bool -> Bool) (m n : Nat) : Int
参数：f : Bool -> Bool -> Bool；m n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Int.natBitwise` is an auxiliary definition for `Int.bitwise`.
-/
def natBitwise (f : Bool → Bool → Bool) (m n : ℕ) : ℤ :=
  cond (f false false) -[Nat.bitwise (fun x y => not (f x y)) m n+1] (Nat.bitwise f m n)

/-- `Int.bitwise` applies the function `f` to pairs of bits in the same position in
  the binary representations of its inputs. -/
/-
**Int.bitwise** 是 Mathlib 中的一个定义，位于命名空间 `Int`。
形式化陈述：(Bool → Bool → Bool) → ℤ → ℤ → ℤ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Int.bitwise` applies the function `f` to pairs of bits in the same position in
  the binary representations of its inputs.
-/
def bitwise (f : Bool → Bool → Bool) : ℤ → ℤ → ℤ
  | (m : ℕ), (n : ℕ) => natBitwise f m n
  | (m : ℕ), -[n+1] => natBitwise (fun x y => f x (not y)) m n
  | -[m+1], (n : ℕ) => natBitwise (fun x y => f (not x) y) m n
  | -[m+1], -[n+1] => natBitwise (fun x y => f (not x) (not y)) m n

/-- `lnot` flips all the bits in the binary representation of its input -/
/-
**Int.lnot** 是 Mathlib 中的一个定义，位于命名空间 `Int`。
形式化陈述：ℤ → ℤ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`lnot` flips all the bits in the binary representation of its input
-/
def lnot : ℤ → ℤ
  | (m : ℕ) => -[m+1]
  | -[m+1] => m

/-- `lor` takes two integers and returns their bitwise `or` -/
/-
**Int.lor** 是 Mathlib 中的一个定义，位于命名空间 `Int`。
形式化陈述：ℤ → ℤ → ℤ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`lor` takes two integers and returns their bitwise `or`
-/
def lor : ℤ → ℤ → ℤ
  | (m : ℕ), (n : ℕ) => m ||| n
  | (m : ℕ), -[n+1] => -[Nat.ldiff n m+1]
  | -[m+1], (n : ℕ) => -[Nat.ldiff m n+1]
  | -[m+1], -[n+1] => -[m &&& n+1]

/-- `land` takes two integers and returns their bitwise `and` -/
/-
**Int.land** 是 Mathlib 中的一个定义，位于命名空间 `Int`。
形式化陈述：ℤ → ℤ → ℤ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`land` takes two integers and returns their bitwise `and`
-/
def land : ℤ → ℤ → ℤ
  | (m : ℕ), (n : ℕ) => m &&& n
  | (m : ℕ), -[n+1] => Nat.ldiff m n
  | -[m+1], (n : ℕ) => Nat.ldiff n m
  | -[m+1], -[n+1] => -[m ||| n+1]

/-- `ldiff a b` performs bitwise set difference. For each corresponding
  pair of bits taken as Booleans, say `aᵢ` and `bᵢ`, it applies the
  Boolean operation `aᵢ ∧ ¬bᵢ` to obtain the `iᵗʰ` bit of the result. -/
/-
**Int.ldiff** 是 Mathlib 中的一个定义，位于命名空间 `Int`。
形式化陈述：ℤ → ℤ → ℤ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ldiff a b` performs bitwise set difference. For each corresponding
  pair of bits taken as Booleans, say `aᵢ` and `bᵢ`, it applies the
  Boolean operation `aᵢ ∧ ¬bᵢ` to obtain the `iᵗʰ` bit of the result.
-/
def ldiff : ℤ → ℤ → ℤ
  | (m : ℕ), (n : ℕ) => Nat.ldiff m n
  | (m : ℕ), -[n+1] => m &&& n
  | -[m+1], (n : ℕ) => -[m ||| n+1]
  | -[m+1], -[n+1] => Nat.ldiff n m

/-- `xor` computes the bitwise `xor` of two natural numbers -/
/-
**Int.xor** 是 Mathlib 中的一个定义，位于命名空间 `Int`。
形式化陈述：ℤ → ℤ → ℤ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`xor` computes the bitwise `xor` of two natural numbers
-/
protected def xor : ℤ → ℤ → ℤ
  | (m : ℕ), (n : ℕ) => (m ^^^ n)
  | (m : ℕ), -[n+1] => -[(m ^^^ n)+1]
  | -[m+1], (n : ℕ) => -[(m ^^^ n)+1]
  | -[m+1], -[n+1] => (m ^^^ n)

/-- `m <<< n` produces an integer whose binary representation
  is obtained by left-shifting the binary representation of `m` by `n` places -/
/-
**Int.** 是 Mathlib 中的一个实例，位于命名空间 `Int`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`m <<< n` produces an integer whose binary representation
  is obtained by left-shifting the binary representation of `m` by `n` places
-/
instance : ShiftLeft ℤ where
  shiftLeft
  | (m : ℕ), (n : ℕ) => Nat.shiftLeft' false m n
  | (m : ℕ), -[n+1] => m >>> (Nat.succ n)
  | -[m+1], (n : ℕ) => -[Nat.shiftLeft' true m n+1]
  | -[m+1], -[n+1] => -[m >>> (Nat.succ n)+1]

/-- `m >>> n` produces an integer whose binary representation
  is obtained by right-shifting the binary representation of `m` by `n` places -/
/-
**Int.** 是 Mathlib 中的一个实例，位于命名空间 `Int`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`m >>> n` produces an integer whose binary representation
  is obtained by right-shifting the binary representation of `m` by `n` places
-/
instance : ShiftRight ℤ where
  shiftRight m n := m <<< (-n)

/-! ### bitwise ops -/

@[simp]
/-
**Int.bodd_zero** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：bodd_zero : bodd 0 = false
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### bitwise ops
-/
theorem bodd_zero : bodd 0 = false :=
  rfl

@[simp]
/-
**Int.bodd_one** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：bodd_one : bodd 1 = true
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bodd_one : bodd 1 = true :=
  rfl
/-
**Int.bodd_two** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：bodd_two : bodd 2 = false
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bodd_two : bodd 2 = false :=
  rfl

@[simp, norm_cast]
/-
**Int.bodd_coe** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：bodd_coe (n : Nat) : Int.bodd n = Nat.bodd n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bodd_coe (n : ℕ) : Int.bodd n = Nat.bodd n :=
  rfl

@[simp]
/-
**Int.bodd_subNatNat** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：bodd_subNatNat (m n : Nat) : bodd (subNatNat m n) = xor m.bodd n.bodd
参数：m n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.subNatNat_elim`：∀ (m n : ℕ) (motive : ℕ → ℕ → ℤ → Prop),   (∀ (i n :
 ℕ), motive (n + i) n ↑i) →     (∀ (i m : ℕ), motive m (m + i + 1) (Int.negSucc 
i)) → mo…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Nat.bodd_add`：bodd_add (m n : Nat) : bodd (m + n) = bxor (bodd m) (bodd 
n)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Bool.bne_false`：∀ (b : Bool), (b != false) = b
· 使用定理 `bne_self_eq_false`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] (a : α)
, (a != a) = false
· 使用定理 `instLawfulBEqBool`：LawfulBEq Bool
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Bool.bne_true`：∀ (b : Bool), (b != true) = !b
· 使用定理 `Bool.not_bne`：∀ (a b : Bool), ((!a) != b) = !a != b
· 使用定理 `Bool.not_false`：(!false) = true
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Nat.bodd_succ`：bodd_succ (n : Nat) : bodd (succ n) = not (bodd n)
· 使用定理 `Bool.bne_not`：∀ (a b : Bool), (a != !b) = !a != b
· 使用定理 `Bool.not_true`：(!true) = false
· 使用定理 `Bool.not_not`：∀ (b : Bool), (!!b) = b
-/
theorem bodd_subNatNat (m n : ℕ) : bodd (subNatNat m n) = xor m.bodd n.bodd := by
  apply subNatNat_elim m n fun m n i => bodd i = xor m.bodd n.bodd <;>
  intro i j <;>
  simp only [Int.bodd, Nat.bodd_add] <;>
  cases Nat.bodd i <;> simp

@[simp]
/-
**Int.bodd_negOfNat** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：bodd_negOfNat (n : Nat) : bodd (negOfNat n) = n.bodd
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true_of_decide`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.bodd_succ`：bodd_succ (n : Nat) : bodd (succ n) = not (bodd n)
-/
theorem bodd_negOfNat (n : ℕ) : bodd (negOfNat n) = n.bodd := by
  cases n <;> simp +decide
  rfl

@[simp]
/-
**Int.bodd_neg** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：bodd_neg (n : Int) : bodd (-n) = bodd n
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.bodd_negOfNat`：bodd_negOfNat (n : Nat) : bodd (negOfNat n) = n.bodd
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Nat.bodd_succ`：bodd_succ (n : Nat) : bodd (succ n) = not (bodd n)
-/
theorem bodd_neg (n : ℤ) : bodd (-n) = bodd n := by
  cases n <;> simp only [← negOfNat_eq, bodd_negOfNat, neg_negSucc] <;> simp [bodd]

@[simp]
/-
**Int.bodd_add** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：bodd_add (m n : Int) : bodd (m + n) = xor (bodd m) (bodd n)
参数：m n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Nat.bodd_add`：bodd_add (m n : Nat) : bodd (m + n) = bxor (bodd m) (bodd 
n)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Int.bodd_subNatNat`：bodd_subNatNat (m n : Nat) : bodd (subNatNat m n) = 
xor m.bodd n.bodd
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Nat.bodd_succ`：bodd_succ (n : Nat) : bodd (succ n) = not (bodd n)
· 使用定理 `Bool.bne_not`：∀ (a b : Bool), (a != !b) = !a != b
· 使用定理 `Bool.xor_comm`：∀ (x y : Bool), (x ^^ y) = (y ^^ x)
· 使用定理 `Bool.not_bne`：∀ (a b : Bool), ((!a) != b) = !a != b
· 使用定理 `Bool.not_not`：∀ (b : Bool), (!!b) = b
-/
theorem bodd_add (m n : ℤ) : bodd (m + n) = xor (bodd m) (bodd n) := by
  rcases m with m | m <;>
  rcases n with n | n <;>
  simp only [ofNat_eq_natCast, ofNat_add_negSucc, negSucc_add_ofNat,
             negSucc_add_negSucc, bodd_subNatNat, ← Nat.cast_add] <;>
  simp [bodd, Bool.xor_comm]

@[simp]
/-
**Int.bodd_mul** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：bodd_mul (m n : Int) : bodd (m * n) = (bodd m && bodd n)
参数：m n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.bodd_mul`：bodd_mul (m n : Nat) : bodd (m * n) = (bodd m && bodd n)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.bodd_neg`：bodd_neg (n : Int) : bodd (-n) = bodd n
-/
theorem bodd_mul (m n : ℤ) : bodd (m * n) = (bodd m && bodd n) := by
  rcases m with m | m <;> rcases n with n | n <;>
  simp only [ofNat_eq_natCast, ofNat_mul_negSucc, negSucc_mul_ofNat, ofNat_mul_ofNat,
             negSucc_mul_negSucc] <;>
  simp only [negSucc_eq, ← Int.natCast_succ, bodd_neg, bodd_coe, Nat.bodd_mul]
/-
**Int.bodd_add_div2** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：∀ (n : ℤ), (bif n.bodd then 1 else 0) + 2 * n.div2 = n
参数：n : ℤ；bif n.bodd then 1 else 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `Nat.bodd_add_div2`：bodd_add_div2 (n : Nat) : (bodd n).toNat + 2 * div2 n
 = n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem bodd_add_div2 : ∀ n, cond (bodd n) 1 0 + 2 * div2 n = n
  | (n : ℕ) => by
    rw [show (cond (bodd n) 1 0 : ℤ) = (cond (bodd n) 1 0 : ℕ) by cases bodd n <;> rfl]
    exact congr_arg ofNat n.bodd_add_div2
  | -[n+1] => by
    refine Eq.trans ?_ (congr_arg negSucc n.bodd_add_div2)
    dsimp [bodd]; cases Nat.bodd n <;> dsimp [cond, not, div2, Int.mul]
    · change -[2 * Nat.div2 n+1] = _
      rw [zero_add]
    · rw [zero_add, add_comm]
      rfl
/-
**Int.div2_val** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：∀ (n : ℤ), n.div2 = n / 2
参数：n : ℤ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Nat.div2_val`：div2_val (n : Nat) : div2 n = n / 2
-/
theorem div2_val : ∀ n, div2 n = n / 2
  | (n : ℕ) => congr_arg ofNat n.div2_val
  | -[n+1] => congr_arg negSucc n.div2_val
/-
**Int.bit_val** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：bit_val (b n) : bit b n = 2 * n + cond b 1 0
参数：b n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem bit_val (b n) : bit b n = 2 * n + cond b 1 0 := by
  cases b
  · apply (add_zero _).symm
  · rfl
/-
**Int.bit_decomp** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：bit_decomp (n : Int) : bit (bodd n) (div2 n) = n
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Int.bit_val`：bit_val (b n) : bit b n = 2 * n + cond b 1 0
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Int.bodd_add_div2`：∀ (n : ℤ), (bif n.bodd then 1 else 0) + 2 * n.div2 = 
n
-/
theorem bit_decomp (n : ℤ) : bit (bodd n) (div2 n) = n :=
  (bit_val _ _).trans <| (add_comm _ _).trans <| bodd_add_div2 _

/-- Defines a function from `ℤ` conditionally, if it is defined for odd and even integers separately
  using `bit`. -/
/-
**Int.bitCasesOn.** 是 Mathlib 中的一个定义，位于命名空间 `Int`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Defines a function from `ℤ` conditionally, if it is defined for odd and even int
egers separately
  using `bit`.
-/
def bitCasesOn.{u} {C : ℤ → Sort u} (n) (h : ∀ b n, C (bit b n)) : C n := by
  rw [← bit_decomp n]
  apply h

@[simp]
/-
**Int.bit_zero** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：bit_zero : bit false 0 = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bit_zero : bit false 0 = 0 :=
  rfl

@[simp]
/-
**Int.bit_coe_nat** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：bit_coe_nat (b) (n : Nat) : bit b n = Nat.bit b n
参数：b；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.bit_val`：bit_val (b n) : bit b n = 2 * n + cond b 1 0
· 使用定理 `Nat.bit_val`：bit_val (b n) : bit b n = 2 * n + b.toNat
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem bit_coe_nat (b) (n : ℕ) : bit b n = Nat.bit b n := by
  rw [bit_val, Nat.bit_val]
  cases b <;> rfl

@[simp]
/-
**Int.bit_negSucc** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：bit_negSucc (b) (n : Nat) : bit b -[n+1] = -[Nat.bit (not b) n+1]
参数：b；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.bit_val`：bit_val (b n) : bit b n = 2 * n + cond b 1 0
· 使用定理 `Nat.bit_val`：bit_val (b n) : bit b n = 2 * n + b.toNat
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem bit_negSucc (b) (n : ℕ) : bit b -[n+1] = -[Nat.bit (not b) n+1] := by
  rw [bit_val, Nat.bit_val]
  cases b <;> rfl

@[simp]
/-
**Int.bodd_bit** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：bodd_bit (b n) : bodd (bit b n) = b
参数：b n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.bit_val`：bit_val (b n) : bit b n = 2 * n + cond b 1 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Int.bodd_mul`：bodd_mul (m n : Int) : bodd (m * n) = (bodd m && bodd n)
· 使用定理 `Bool.false_and`：∀ (b : Bool), (false && b) = false
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.bodd_add`：bodd_add (m n : Int) : bodd (m + n) = xor (bodd m) (bodd n
)
· 使用定理 `Bool.bne_true`：∀ (b : Bool), (b != true) = !b
· 使用定理 `Bool.not_false`：(!false) = true
-/
theorem bodd_bit (b n) : bodd (bit b n) = b := by
  rw [bit_val]
  cases b <;> cases bodd n <;> simp [(show bodd 2 = false by rfl)]

@[simp]
/-
**Int.testBit_bit_zero** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：∀ (b : Bool) (n : ℤ), (Int.bit b n).testBit 0 = b
参数：b : Bool；n : ℤ；Int.bit b n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.bit_coe_nat`：bit_coe_nat (b) (n : Nat) : bit b n = Nat.bit b n
· 使用定理 `Nat.testBit_bit_zero`：testBit_bit_zero (b n) : (bit b n).testBit 0 = b
· 使用定理 `Int.bit_negSucc`：bit_negSucc (b) (n : Nat) : bit b -[n+1] = -[Nat.bit (n
ot b) n+1]
· 使用定理 `Bool.not_not`：∀ (b : Bool), (!!b) = b
-/
theorem testBit_bit_zero (b) : ∀ n, testBit (bit b n) 0 = b
  | (n : ℕ) => by rw [bit_coe_nat]; apply Nat.testBit_bit_zero
  | -[n+1] => by
    rw [bit_negSucc]; dsimp [testBit]; rw [Nat.testBit_bit_zero, Bool.not_not]

@[simp]
/-
**Int.testBit_bit_succ** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：testBit_bit_succ (m b) : forall n, testBit (bit b n) (Nat.succ m) = testBi
t n m | (n : Nat) => by rw [bit_coe_nat]; apply Nat.testBit_bit_succ | -[n+1] =>
 by dsimp only [testBit] simp only [bit_negSucc] cases b <;> simp only [Bool.not
_false, Bool.not_true, Nat.testBit_bit_succ]  -- Porting note (https://github.co
m/leanprover-community/mathlib4/issues/11215): TODO -- private unsafe def bitwis
e_tac : tactic Unit
参数：m b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.bit_coe_nat`：bit_coe_nat (b) (n : Nat) : bit b n = Nat.bit b n
· 使用引理 `Nat.testBit_bit_succ`：testBit_bit_succ (m b n) : testBit (bit b n) (succ
 m) = testBit n m
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.bit_negSucc`：bit_negSucc (b) (n : Nat) : bit b -[n+1] = -[Nat.bit (n
ot b) n+1]
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Bool.not_false`：(!false) = true
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Bool.not_true`：(!true) = false
-/
theorem testBit_bit_succ (m b) : ∀ n, testBit (bit b n) (Nat.succ m) = testBit n m
  | (n : ℕ) => by rw [bit_coe_nat]; apply Nat.testBit_bit_succ
  | -[n+1] => by
    dsimp only [testBit]
    simp only [bit_negSucc]
    cases b <;> simp only [Bool.not_false, Bool.not_true, Nat.testBit_bit_succ]

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11215): TODO
-- private unsafe def bitwise_tac : tactic Unit :=
--   sorry

-- Porting note: Was `bitwise_tac` in mathlib
/-
**Int.bitwise_or** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：bitwise_or : bitwise or = lor
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bool.not_false`：(!false) = true
· 使用定理 `Bool.or_true`：∀ (b : Bool), (b || true) = true
· 使用定理 `Int.negSucc.injEq`：∀ (a a_1 : ℕ), (Int.negSucc a = Int.negSucc a_1) = (a
 = a_1)
· 使用定理 `Nat.bitwise_swap`：bitwise_swap {f : Bool -> Bool -> Bool} : bitwise (Fun
ction.swap f) = Function.swap (bitwise f)
· 使用定理 `Function.swap.eq_1`：∀ {α : Sort u₁} {β : Sort u₂} {φ : α → β → Sort u₃} 
(f : (x : α) → (y : β) → φ x y) (y : β) (x : α),   Function.swap f y x = f x y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Bool.true_or`：∀ (b : Bool), (true || b) = true
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Bool.not_or`：∀ (x y : Bool), (!(x || y)) = (!x && !y)
· 使用定理 `Bool.not_not`：∀ (b : Bool), (!!b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
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
/-
**Int.bitwise_and** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：bitwise_and : bitwise and = land
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Bool.not_false`：(!false) = true
· 使用定理 `Bool.and_false`：∀ (b : Bool), (b && false) = false
· 使用定理 `Nat.bitwise_swap`：bitwise_swap {f : Bool -> Bool -> Bool} : bitwise (Fun
ction.swap f) = Function.swap (bitwise f)
· 使用定理 `Function.swap.eq_1`：∀ {α : Sort u₁} {β : Sort u₂} {φ : α → β → Sort u₃} 
(f : (x : α) → (y : β) → φ x y) (y : β) (x : α),   Function.swap f y x = f x y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Bool.and_true`：∀ (b : Bool), (b && true) = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Bool.not_and`：∀ (x y : Bool), (!(x && y)) = (!x || !y)
· 使用定理 `Bool.not_not`：∀ (b : Bool), (!!b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
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
/-
**Int.bitwise_diff** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：bitwise_diff : (bitwise fun a b => a && not b) = ldiff
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Bool.not_false`：(!false) = true
· 使用定理 `Bool.not_true`：(!true) = false
· 使用定理 `Bool.and_false`：∀ (b : Bool), (b && false) = false
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Bool.not_not`：∀ (b : Bool), (!!b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Bool.and_true`：∀ (b : Bool), (b && true) = b
· 使用定理 `Int.negSucc.injEq`：∀ (a a_1 : ℕ), (Int.negSucc a = Int.negSucc a_1) = (a
 = a_1)
· 使用定理 `Bool.not_and`：∀ (x y : Bool), (!(x && y)) = (!x || !y)
· 使用定理 `Nat.bitwise_swap`：bitwise_swap {f : Bool -> Bool -> Bool} : bitwise (Fun
ction.swap f) = Function.swap (bitwise f)
· 使用定理 `Function.swap.eq_1`：∀ {α : Sort u₁} {β : Sort u₂} {φ : α → β → Sort u₃} 
(f : (x : α) → (y : β) → φ x y) (y : β) (x : α),   Function.swap f y x = f x y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
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
/-
**Int.bitwise_xor** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：bitwise_xor : bitwise xor = Int.xor
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Bool.not_false`：(!false) = true
· 使用定理 `Bool.false_xor`：∀ (x : Bool), (false ^^ x) = x
· 使用定理 `Bool.bne_eq_xor`：bne_eq_xor : bne = xor
· 使用定理 `Int.negSucc.injEq`：∀ (a a_1 : ℕ), (Int.negSucc a = Int.negSucc a_1) = (a
 = a_1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Bool.bne_not`：∀ (a b : Bool), (a != !b) = !a != b
· 使用定理 `Bool.not_not`：∀ (b : Bool), (!!b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Bool.true_xor`：∀ (x : Bool), (true ^^ x) = !x
· 使用定理 `Bool.not_bne`：∀ (a b : Bool), ((!a) != b) = !a != b
· 使用定理 `Bool.not_true`：(!true) = false
-/
theorem bitwise_xor : bitwise xor = Int.xor := by
  funext m n
  rcases m with m | m <;> rcases n with n | n <;> try {rfl}
    <;> simp only [bitwise, natBitwise, Bool.not_false, Bool.bne_eq_xor,
      cond_false, cond_true, negSucc.injEq, Bool.false_xor,
      Bool.true_xor, Bool.not_true,
      Int.xor, HXor.hXor, XorOp.xor, Nat.xor] <;> simp

@[simp]
/-
**Int.bitwise_bit** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：bitwise_bit (f : Bool -> Bool -> Bool) (a m b n) : bitwise f (bit a m) (bi
t b n) = bit (f a b) (bitwise f m n)
参数：f : Bool -> Bool -> Bool；a m b n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.bit_coe_nat`：bit_coe_nat (b) (n : Nat) : bit b n = Nat.bit b n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Nat.bitwise_bit`：bitwise_bit {f : Bool -> Bool -> Bool} (h : f false fal
se = false
· 使用定理 `Bool.not_true`：(!true) = false
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Int.bit_negSucc`：bit_negSucc (b) (n : Nat) : bit b -[n+1] = -[Nat.bit (n
ot b) n+1]
· 使用定理 `Bool.of_not_eq_true`：∀ {b : Bool}, ¬b = true → b = false
· 使用定理 `Bool.not_false`：(!false) = true
· 使用定理 `Bool.not_not`：∀ (b : Bool), (!!b) = b
-/
theorem bitwise_bit (f : Bool → Bool → Bool) (a m b n) :
    bitwise f (bit a m) (bit b n) = bit (f a b) (bitwise f m n) := by
  rcases m with m | m <;> rcases n with n | n <;>
  simp [bitwise, ofNat_eq_natCast, bit_coe_nat, natBitwise, Bool.not_false,
    bit_negSucc]
  · by_cases h : f false false <;> simp +decide [h]
  · by_cases h : f false true <;> simp +decide [h]
  · by_cases h : f true false <;> simp +decide [h]
  · by_cases h : f true true <;> simp +decide [h]

@[simp]
/-
**Int.lor_bit** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：lor_bit (a m b n) : lor (bit a m) (bit b n) = bit (a || b) (lor m n)
参数：a m b n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.bitwise_or`：bitwise_or : bitwise or = lor
· 使用定理 `Int.bitwise_bit`：bitwise_bit (f : Bool -> Bool -> Bool) (a m b n) : bitw
ise f (bit a m) (bit b n) = bit (f a b) (bitwise f m n)
-/
theorem lor_bit (a m b n) : lor (bit a m) (bit b n) = bit (a || b) (lor m n) := by
  rw [← bitwise_or, bitwise_bit]

@[simp]
/-
**Int.land_bit** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：land_bit (a m b n) : land (bit a m) (bit b n) = bit (a && b) (land m n)
参数：a m b n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.bitwise_and`：bitwise_and : bitwise and = land
· 使用定理 `Int.bitwise_bit`：bitwise_bit (f : Bool -> Bool -> Bool) (a m b n) : bitw
ise f (bit a m) (bit b n) = bit (f a b) (bitwise f m n)
-/
theorem land_bit (a m b n) : land (bit a m) (bit b n) = bit (a && b) (land m n) := by
  rw [← bitwise_and, bitwise_bit]

@[simp]
/-
**Int.ldiff_bit** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：ldiff_bit (a m b n) : ldiff (bit a m) (bit b n) = bit (a && not b) (ldiff 
m n)
参数：a m b n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.bitwise_diff`：bitwise_diff : (bitwise fun a b => a && not b) = ldiff
· 使用定理 `Int.bitwise_bit`：bitwise_bit (f : Bool -> Bool -> Bool) (a m b n) : bitw
ise f (bit a m) (bit b n) = bit (f a b) (bitwise f m n)
-/
theorem ldiff_bit (a m b n) : ldiff (bit a m) (bit b n) = bit (a && not b) (ldiff m n) := by
  rw [← bitwise_diff, bitwise_bit]

@[simp]
/-
**Int.lxor_bit** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：lxor_bit (a m b n) : Int.xor (bit a m) (bit b n) = bit (xor a b) (Int.xor 
m n)
参数：a m b n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.bitwise_xor`：bitwise_xor : bitwise xor = Int.xor
· 使用定理 `Int.bitwise_bit`：bitwise_bit (f : Bool -> Bool -> Bool) (a m b n) : bitw
ise f (bit a m) (bit b n) = bit (f a b) (bitwise f m n)
-/
theorem lxor_bit (a m b n) : Int.xor (bit a m) (bit b n) = bit (xor a b) (Int.xor m n) := by
  rw [← bitwise_xor, bitwise_bit]

@[simp]
/-
**Int.lnot_bit** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：∀ (b : Bool) (n : ℤ), (Int.bit b n).lnot = Int.bit (!b) n.lnot
参数：b : Bool；n : ℤ；Int.bit b n；!b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.bit_coe_nat`：bit_coe_nat (b) (n : Nat) : bit b n = Nat.bit b n
· 使用定理 `Int.bit_negSucc`：bit_negSucc (b) (n : Nat) : bit b -[n+1] = -[Nat.bit (n
ot b) n+1]
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Bool.not_not`：∀ (b : Bool), (!!b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lnot_bit (b) : ∀ n, lnot (bit b n) = bit (not b) (lnot n)
  | (n : ℕ) => by simp [lnot]
  | -[n+1] => by simp [lnot]

@[simp]
/-
**Int.testBit_bitwise** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：testBit_bitwise (f : Bool -> Bool -> Bool) (m n k) : testBit (bitwise f m 
n) k = f (testBit m k) (testBit n k)
参数：f : Bool -> Bool -> Bool；m n k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.testBit_bitwise`：∀ {f : Bool → Bool → Bool},   f false false = false
 → ∀ (x y i : ℕ), (Nat.bitwise f x y).testBit i = f (x.testBit i) (y.testBit i)
· 使用定理 `Bool.not_true`：(!true) = false
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Bool.not_not`：∀ (b : Bool), (!!b) = b
· 使用定理 `Bool.of_not_eq_true`：∀ {b : Bool}, ¬b = true → b = false
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Bool.not_false`：(!false) = true
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
theorem testBit_bitwise (f : Bool → Bool → Bool) (m n k) :
    testBit (bitwise f m n) k = f (testBit m k) (testBit n k) := by
  cases m <;> cases n <;> simp only [testBit, bitwise, natBitwise]
  · by_cases h : f false false <;> simp [h]
  · by_cases h : f false true <;> simp [h]
  · by_cases h : f true false <;> simp [h]
  · by_cases h : f true true <;> simp [h]

@[simp]
/-
**Int.testBit_lor** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：testBit_lor (m n k) : testBit (lor m n) k = (testBit m k || testBit n k)
参数：m n k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.bitwise_or`：bitwise_or : bitwise or = lor
· 使用定理 `Int.testBit_bitwise`：testBit_bitwise (f : Bool -> Bool -> Bool) (m n k) 
: testBit (bitwise f m n) k = f (testBit m k) (testBit n k)
-/
theorem testBit_lor (m n k) : testBit (lor m n) k = (testBit m k || testBit n k) := by
  rw [← bitwise_or, testBit_bitwise]

@[simp]
/-
**Int.testBit_land** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：testBit_land (m n k) : testBit (land m n) k = (testBit m k && testBit n k)
参数：m n k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.bitwise_and`：bitwise_and : bitwise and = land
· 使用定理 `Int.testBit_bitwise`：testBit_bitwise (f : Bool -> Bool -> Bool) (m n k) 
: testBit (bitwise f m n) k = f (testBit m k) (testBit n k)
-/
theorem testBit_land (m n k) : testBit (land m n) k = (testBit m k && testBit n k) := by
  rw [← bitwise_and, testBit_bitwise]

@[simp]
/-
**Int.testBit_ldiff** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：testBit_ldiff (m n k) : testBit (ldiff m n) k = (testBit m k && not (testB
it n k))
参数：m n k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.bitwise_diff`：bitwise_diff : (bitwise fun a b => a && not b) = ldiff
· 使用定理 `Int.testBit_bitwise`：testBit_bitwise (f : Bool -> Bool -> Bool) (m n k) 
: testBit (bitwise f m n) k = f (testBit m k) (testBit n k)
-/
theorem testBit_ldiff (m n k) : testBit (ldiff m n) k = (testBit m k && not (testBit n k)) := by
  rw [← bitwise_diff, testBit_bitwise]

@[simp]
/-
**Int.testBit_lxor** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：testBit_lxor (m n k) : testBit (Int.xor m n) k = xor (testBit m k) (testBi
t n k)
参数：m n k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.bitwise_xor`：bitwise_xor : bitwise xor = Int.xor
· 使用定理 `Int.testBit_bitwise`：testBit_bitwise (f : Bool -> Bool -> Bool) (m n k) 
: testBit (bitwise f m n) k = f (testBit m k) (testBit n k)
-/
theorem testBit_lxor (m n k) : testBit (Int.xor m n) k = xor (testBit m k) (testBit n k) := by
  rw [← bitwise_xor, testBit_bitwise]

@[simp]
/-
**Int.testBit_lnot** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：∀ (n : ℤ) (k : ℕ), n.lnot.testBit k = !n.testBit k
参数：n : ℤ；k : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bool.not_not`：∀ (b : Bool), (!!b) = b
-/
theorem testBit_lnot : ∀ n k, testBit (lnot n) k = not (testBit n k)
  | (n : ℕ), k => by simp [lnot, testBit]
  | -[n+1], k => by simp [lnot, testBit]

@[simp]
/-
**Int.shiftLeft_neg** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：shiftLeft_neg (m n : Int) : m <<< (-n) = m >>> n
参数：m n : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem shiftLeft_neg (m n : ℤ) : m <<< (-n) = m >>> n :=
  rfl

@[simp]
/-
**Int.shiftRight_neg** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：shiftRight_neg (m n : Int) : m >>> (-n) = m <<< n
参数：m n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.shiftLeft_neg`：shiftLeft_neg (m n : Int) : m <<< (-n) = m >>> n
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
theorem shiftRight_neg (m n : ℤ) : m >>> (-n) = m <<< n := by rw [← shiftLeft_neg, neg_neg]

@[simp]
/-
**Int.shiftLeft_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：shiftLeft_natCast (m n : Nat) : (m : Int) <<< (n : Int) = ↑(m <<< n)
参数：m n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `Nat.shiftLeft'`：shiftLeft'_false : forall n, shiftLeft' false m n = m <<
< n | 0 => rfl | n + 1 => by have : 2 * (m * 2 ^ n) = 2 ^ (n + 1) * m
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.shiftLeft'_false`：∀ {m : ℕ} (n : ℕ), Nat.shiftLeft' false m n = m <<
< n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem shiftLeft_natCast (m n : ℕ) : (m : ℤ) <<< (n : ℤ) = ↑(m <<< n) := by
  unfold_projs; simp

@[simp]
/-
**Int.shiftRight_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：shiftRight_natCast (m n : Nat) : (m : Int) >>> (n : Int) = m >>> n
参数：m n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem shiftRight_natCast (m n : ℕ) : (m : ℤ) >>> (n : ℤ) = m >>> n := by cases n <;> rfl

@[simp]
/-
**Int.shiftLeft_negSucc** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：shiftLeft_negSucc (m n : Nat) : -[m+1] <<< (n : Int) = -[Nat.shiftLeft' tr
ue m n+1]
参数：m n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem shiftLeft_negSucc (m n : ℕ) : -[m+1] <<< (n : ℤ) = -[Nat.shiftLeft' true m n+1] :=
  rfl

@[simp]
/-
**Int.shiftRight_negSucc** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：shiftRight_negSucc (m n : Nat) : -[m+1] >>> (n : Int) = -[m >>> n+1]
参数：m n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem shiftRight_negSucc (m n : ℕ) : -[m+1] >>> (n : ℤ) = -[m >>> n+1] := by cases n <;> rfl

/-- Compare with `Int.shiftRight_add`, which doesn't have the coercions `ℕ → ℤ`. -/
/-
**Int.shiftRight_add'** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：∀ (m : ℤ) (n k : ℕ), m >>> (↑n + ↑k) = m >>> ↑n >>> ↑k
参数：m : ℤ；n k : ℕ；↑n + ↑k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.shiftRight_natCast`：shiftRight_natCast (m n : Nat) : (m : Int) >>> (
n : Int) = m >>> n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.natCast_add`：∀ (n m : ℕ), ↑(n + m) = ↑n + ↑m
· 使用定理 `Nat.shiftRight_add`：∀ (m n k : ℕ), m >>> (n + k) = m >>> n >>> k
· 使用定理 `Int.shiftRight_negSucc`：shiftRight_negSucc (m n : Nat) : -[m+1] >>> (n :
 Int) = -[m >>> n+1]

--- 原说明 ---
Compare with `Int.shiftRight_add`, which doesn't have the coercions `ℕ → ℤ`.
-/
theorem shiftRight_add' : ∀ (m : ℤ) (n k : ℕ), m >>> (n + k : ℤ) = (m >>> (n : ℤ)) >>> (k : ℤ)
  | (m : ℕ), n, k => by
    rw [shiftRight_natCast, shiftRight_natCast, ← Int.natCast_add, shiftRight_natCast,
      Nat.shiftRight_add]
  | -[m+1], n, k => by
    rw [shiftRight_negSucc, shiftRight_negSucc, ← Int.natCast_add, shiftRight_negSucc,
      Nat.shiftRight_add]

/-! ### bitwise ops -/

/-- Connection of `HShiftLeft Int Int Int` and `HShiftLeft Int Nat Int`. -/
/-
**Int.shiftLeft_natCast_right** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：shiftLeft_natCast_right (m : Int) (n : Nat) : m <<< (n : Int) = m <<< n
参数：m : Int；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.shiftLeft_eq'`：∀ (a : ℤ) (b : ℕ), a <<< b = a * ↑(2 ^ b)
· 使用引理 `Nat.shiftLeft'`：shiftLeft'_false : forall n, shiftLeft' false m n = m <<
< n | 0 => rfl | n + 1 => by have : 2 * (m * 2 ^ n) = 2 ^ (n + 1) * m
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.shiftLeft'_false`：∀ {m : ℕ} (n : ℕ), Nat.shiftLeft' false m n = m <<
< n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.shiftLeft'_true_eq_mul_pow`：∀ (m n : ℕ), Nat.shiftLeft' true m n + 1
 = (m + 1) * 2 ^ n

--- 原说明 ---
Connection of `HShiftLeft Int Int Int` and `HShiftLeft Int Nat Int`.
-/
lemma shiftLeft_natCast_right (m : ℤ) (n : ℕ) :
    m <<< (n : ℤ) = m <<< n := by
  rw [Int.shiftLeft_eq']
  unfold_projs; cases m <;> simp only [Nat.shiftLeft'_false, natCast_shiftLeft, ofNat_eq_natCast,
    Nat.pow_eq, Int.natCast_pow, Nat.cast_ofNat, mul_def]
  · grind [Int.shiftLeft_eq']
  · simp only [negSucc_eq, ← natCast_add_one, Nat.shiftLeft'_true_eq_mul_pow]
    grind

/-- Connection of `HShiftRight Int Int Int` and `HShiftRight Int Nat Int`. -/
/-
**Int.shiftRight_natCast_right** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：shiftRight_natCast_right (m : Int) (n : Nat) : m >>> (n : Int) = m >>> n
参数：m : Int；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.shiftRight_natCast`：shiftRight_natCast (m n : Nat) : (m : Int) >>> (
n : Int) = m >>> n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.shiftRight_negSucc`：shiftRight_negSucc (m n : Nat) : -[m+1] >>> (n :
 Int) = -[m >>> n+1]

--- 原说明 ---
Connection of `HShiftRight Int Int Int` and `HShiftRight Int Nat Int`.
-/
lemma shiftRight_natCast_right (m : ℤ) (n : ℕ) :
    m >>> (n : ℤ) = m >>> n := by
  cases m <;> simp
/-
**Int.shiftLeft_add'** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：∀ (m : ℤ) (n : ℕ) (k : ℤ), m <<< (↑n + k) = m <<< ↑n <<< k
参数：m : ℤ；n : ℕ；k : ℤ；↑n + k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `Nat.shiftLeft'`：shiftLeft'_false : forall n, shiftLeft' false m n = m <<
< n | 0 => rfl | n + 1 => by have : 2 * (m * 2 ^ n) = 2 ^ (n + 1) * m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.shiftLeft'_false`：∀ {m : ℕ} (n : ℕ), Nat.shiftLeft' false m n = m <<
< n
· 使用定理 `Nat.shiftLeft_eq`：∀ (a b : ℕ), a <<< b = a * 2 ^ b
· 使用定理 `Nat.pow_add`：∀ (a m n : ℕ), a ^ (m + n) = a ^ m * a ^ n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.shiftLeft'_add`：∀ (b : Bool) (m n k : ℕ), Nat.shiftLeft' b m (n + k)
 = Nat.shiftLeft' b (Nat.shiftLeft' b m n) k
· 使用定理 `Int.subNatNat_elim`：∀ (m n : ℕ) (motive : ℕ → ℕ → ℤ → Prop),   (∀ (i n :
 ℕ), motive (n + i) n ↑i) →     (∀ (i m : ℕ), motive m (m + i + 1) (Int.negSucc 
i)) → mo…
· 使用定理 `Int.shiftLeft_natCast`：shiftLeft_natCast (m n : Nat) : (m : Int) <<< (n 
: Int) = ↑(m <<< n)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Nat.shiftLeft_sub`：shiftLeft_sub : forall (m : Nat) {n k}, k <= n -> m <
<< (n - k) = (m <<< n) >>> k
· 使用定理 `Nat.add_sub_cancel_left`：∀ (n m : ℕ), n + m - n = m
· 使用定理 `Nat.shiftRight_add`：∀ (m n k : ℕ), m >>> (n + k) = m >>> n >>> k
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Nat.sub_self`：∀ (n : ℕ), n - n = 0
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.shiftLeft'_sub`：∀ (b : Bool) (m : ℕ) {n k : ℕ}, k ≤ n → Nat.shiftLef
t' b m (n - k) = Nat.shiftLeft' b m n >>> k
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Nat.shiftLeft'.eq_1`：∀ (b : Bool) (m : ℕ), Nat.shiftLeft' b m 0 = m
-/
theorem shiftLeft_add' : ∀ (m : ℤ) (n : ℕ) (k : ℤ), m <<< (n + k) = (m <<< (n : ℤ)) <<< k
  | (m : ℕ), n, (k : ℕ) =>
    congr_arg ofNat (by simp [Nat.shiftLeft_eq, Nat.pow_add, mul_assoc])
  | -[_+1], _, (k : ℕ) => congr_arg negSucc (Nat.shiftLeft'_add _ _ _ _)
  | (m : ℕ), n, -[k+1] =>
    subNatNat_elim n k.succ (fun n k i => (↑m) <<< i = (Nat.shiftLeft' false m n) >>> k)
      (fun (i n : ℕ) => by simp [← Nat.shiftLeft_sub _])
      fun i n => by
        simp_rw [negSucc_eq, shiftLeft_neg, Nat.shiftLeft'_false, Nat.shiftRight_add,
          ← Nat.shiftLeft_sub _ le_rfl, Nat.sub_self, Nat.shiftLeft_zero, ← shiftRight_natCast,
          ← shiftRight_add', Nat.cast_one]
  | -[m+1], n, -[k+1] =>
    subNatNat_elim n k.succ
      (fun n k i => -[m+1] <<< i = -[(Nat.shiftLeft' true m n) >>> k+1])
      (fun i n =>
        congr_arg negSucc <| by
          rw [← Nat.shiftLeft'_sub, Nat.add_sub_cancel_left]; apply Nat.le_add_right)
      fun i n =>
      congr_arg negSucc <| by rw [add_assoc, Nat.shiftRight_add, ← Nat.shiftLeft'_sub _ _ le_rfl,
          Nat.sub_self, Nat.shiftLeft']
/-
**Int.shiftLeft_sub** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：shiftLeft_sub (m : Int) (n : Nat) (k : Int) : m <<< (n - k) = (m <<< (n : 
Int)) >>> k
参数：m : Int；n : Nat；k : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.shiftLeft_add'`：∀ (m : ℤ) (n : ℕ) (k : ℤ), m <<< (↑n + k) = m <<< ↑n
 <<< k
-/
theorem shiftLeft_sub (m : ℤ) (n : ℕ) (k : ℤ) : m <<< (n - k) = (m <<< (n : ℤ)) >>> k :=
  shiftLeft_add' _ _ _
/-
**Int.shiftLeft_eq_mul_pow** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：∀ (m : ℤ) (n : ℕ), m <<< ↑n = m * ↑(2 ^ n)
参数：m : ℤ；n : ℕ；2 ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `Nat.shiftLeft'`：shiftLeft'_false : forall n, shiftLeft' false m n = m <<
< n | 0 => rfl | n + 1 => by have : 2 * (m * 2 ^ n) = 2 ^ (n + 1) * m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.shiftLeft'_false`：∀ {m : ℕ} (n : ℕ), Nat.shiftLeft' false m n = m <<
< n
· 使用定理 `Nat.shiftLeft_eq`：∀ (a b : ℕ), a <<< b = a * 2 ^ b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.shiftLeft'_true_eq_mul_pow`：∀ (m n : ℕ), Nat.shiftLeft' true m n + 1
 = (m + 1) * 2 ^ n
-/
theorem shiftLeft_eq_mul_pow : ∀ (m : ℤ) (n : ℕ), m <<< (n : ℤ) = m * (2 ^ n : ℕ)
  | (m : ℕ), _ => congr_arg ((↑) : ℕ → ℤ) (by simp [Nat.shiftLeft_eq])
  | -[_+1], _ => @congr_arg ℕ ℤ _ _ (fun i => -i) (Nat.shiftLeft'_true_eq_mul_pow _ _)
/-
**Int.one_shiftLeft** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：one_shiftLeft (n : Nat) : 1 <<< (n : Int) = (2 ^ n : Nat)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `Nat.shiftLeft'`：shiftLeft'_false : forall n, shiftLeft' false m n = m <<
< n | 0 => rfl | n + 1 => by have : 2 * (m * 2 ^ n) = 2 ^ (n + 1) * m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.shiftLeft'_false`：∀ {m : ℕ} (n : ℕ), Nat.shiftLeft' false m n = m <<
< n
· 使用定理 `Nat.shiftLeft_eq`：∀ (a b : ℕ), a <<< b = a * 2 ^ b
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem one_shiftLeft (n : ℕ) : 1 <<< (n : ℤ) = (2 ^ n : ℕ) :=
  congr_arg ((↑) : ℕ → ℤ) (by simp [Nat.shiftLeft_eq])

/-- Compare with `Int.zero_shiftLeft`, which has `n : ℕ`. -/
@[simp]
/-
**Int.zero_shiftLeft'** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：∀ (n : ℤ), 0 <<< n = 0
参数：n : ℤ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `Nat.shiftLeft'`：shiftLeft'_false : forall n, shiftLeft' false m n = m <<
< n | 0 => rfl | n + 1 => by have : 2 * (m * 2 ^ n) = 2 ^ (n + 1) * m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.shiftLeft'_false`：∀ {m : ℕ} (n : ℕ), Nat.shiftLeft' false m n = m <<
< n
· 使用定理 `Nat.zero_shiftLeft`：∀ (n : ℕ), 0 <<< n = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.zero_shiftRight`：∀ (n : ℕ), 0 >>> n = 0

--- 原说明 ---
Compare with `Int.zero_shiftLeft`, which has `n : ℕ`.
-/
theorem zero_shiftLeft' : ∀ n : ℤ, 0 <<< n = 0
  | (n : ℕ) => congr_arg ((↑) : ℕ → ℤ) (by simp)
  | -[_+1] => congr_arg ((↑) : ℕ → ℤ) (by simp)

/-- Compare with `Int.zero_shiftRight`, which has `n : ℕ`. -/
@[simp]
/-
**Int.zero_shiftRight'** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：zero_shiftRight' (n : Int) : 0 >>> n = 0
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.zero_shiftLeft'`：∀ (n : ℤ), 0 <<< n = 0

--- 原说明 ---
Compare with `Int.zero_shiftRight`, which has `n : ℕ`.
-/
theorem zero_shiftRight' (n : ℤ) : 0 >>> n = 0 :=
  zero_shiftLeft' _

end Int

