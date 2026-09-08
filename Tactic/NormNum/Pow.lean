/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Thomas Murrills
-/
module

public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Tactic.NormNum.Basic

/-!
## `norm_num` plugin for `^`.
-/

public meta section

assert_not_exists RelIso

namespace Mathlib
open Lean
open Meta

namespace Meta.NormNum
open Qq

variable {a b c : ℕ}

/-
**Mathlib.Meta.NormNum.natPow_zero** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.NormN
um`。
形式化陈述：natPow_zero : Nat.pow a (nat_lit 0) = nat_lit 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem natPow_zero : Nat.pow a (nat_lit 0) = nat_lit 1 := rfl
/-
**Mathlib.Meta.NormNum.natPow_one** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.NormNu
m`。
形式化陈述：natPow_one : Nat.pow a (nat_lit 1) = a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.pow_one`：∀ (a : ℕ), a ^ 1 = a
-/
theorem natPow_one : Nat.pow a (nat_lit 1) = a := Nat.pow_one _
/-
**Mathlib.Meta.NormNum.zero_natPow** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.NormN
um`。
形式化陈述：zero_natPow : Nat.pow (nat_lit 0) (Nat.succ b) = nat_lit 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_natPow : Nat.pow (nat_lit 0) (Nat.succ b) = nat_lit 0 := rfl
/-
**Mathlib.Meta.NormNum.one_natPow** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.NormNu
m`。
形式化陈述：one_natPow : Nat.pow (nat_lit 1) b = nat_lit 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.one_pow`：∀ (n : ℕ), 1 ^ n = 1
-/
theorem one_natPow : Nat.pow (nat_lit 1) b = nat_lit 1 := Nat.one_pow _

/-- This is an opaque wrapper around `Nat.pow` to prevent lean from unfolding the definition of
`Nat.pow` on numerals. The arbitrary precondition `p` is actually a formula of the form
`Nat.pow a' b' = c'` but we usually don't care to unfold this proposition so we just carry a
reference to it. -/
/-
**Mathlib.Meta.NormNum.IsNatPowT** 是 Mathlib 中的一个归纳类型，位于命名空间 `Mathlib.Meta.NormN
um`。
形式化陈述：Prop → ℕ → ℕ → ℕ → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is an opaque wrapper around `Nat.pow` to prevent lean from unfolding the de
finition of
`Nat.pow` on numerals. The arbitrary precondition `p` is actually a formula of t
he form
`Nat.pow a' b' = c'` but we usually don't care to unfold this proposition so we 
just carry a
reference to it.
-/
structure IsNatPowT (p : Prop) (a b c : Nat) : Prop where
  /-- Unfolds the assertion. -/
  run' : p → Nat.pow a b = c
/-
**Mathlib.Meta.NormNum.IsNatPowT.run** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.Nor
mNum.IsNatPowT`。
形式化陈述：∀ {a b c : ℕ}, Mathlib.Meta.NormNum.IsNatPowT (a.pow 1 = a) a b c → a.pow 
b = c
参数：a.pow 1 = a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Meta.NormNum.IsNatPowT.run'`：∀ {p : Prop} {a b c : ℕ}, Mathlib.M
eta.NormNum.IsNatPowT p a b c → p → a.pow b = c
· 使用定理 `Nat.pow_one`：∀ (a : ℕ), a ^ 1 = a
-/
theorem IsNatPowT.run
    (p : IsNatPowT (Nat.pow a (nat_lit 1) = a) a b c) : Nat.pow a b = c := p.run' (Nat.pow_one _)

/-- This is the key to making the proof proceed as a balanced tree of applications instead of
a linear sequence. It is just modus ponens after unwrapping the definitions. -/
/-
**Mathlib.Meta.NormNum.IsNatPowT.trans** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.N
ormNum.IsNatPowT`。
形式化陈述：∀ {a b c : ℕ} {p : Prop} {b' c' : ℕ},   Mathlib.Meta.NormNum.IsNatPowT p a
 b c →     Mathlib.Meta.NormNum.IsNatPowT (a.pow b = c) a b' c' → Mathlib.Meta.N
ormNum.IsNatPowT p a b' c'
参数：a.pow b = c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Meta.NormNum.IsNatPowT.run'`：∀ {p : Prop} {a b c : ℕ}, Mathlib.M
eta.NormNum.IsNatPowT p a b c → p → a.pow b = c

--- 原说明 ---
This is the key to making the proof proceed as a balanced tree of applications i
nstead of
a linear sequence. It is just modus ponens after unwrapping the definitions.
-/
theorem IsNatPowT.trans {p : Prop} {b' c' : ℕ} (h1 : IsNatPowT p a b c)
    (h2 : IsNatPowT (Nat.pow a b = c) a b' c') : IsNatPowT p a b' c' :=
  ⟨h2.run' ∘ h1.run'⟩
/-
**Mathlib.Meta.NormNum.IsNatPowT.bit0** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.No
rmNum.IsNatPowT`。
形式化陈述：∀ {a b c : ℕ}, Mathlib.Meta.NormNum.IsNatPowT (a.pow b = c) a (2 * b) (c.m
ul c)
参数：a.pow b = c；2 * b；c.mul c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsNatPowT.bit0 : IsNatPowT (Nat.pow a b = c) a (nat_lit 2 * b) (Nat.mul c c) :=
  ⟨fun h1 => by simp [two_mul, pow_add, ← h1]⟩
/-
**Mathlib.Meta.NormNum.IsNatPowT.bit1** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.No
rmNum.IsNatPowT`。
形式化陈述：∀ {a b c : ℕ}, Mathlib.Meta.NormNum.IsNatPowT (a.pow b = c) a (2 * b + 1) 
(c.mul (c.mul a))
参数：a.pow b = c；2 * b + 1；c.mul (c.mul a)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsNatPowT.bit1 :
    IsNatPowT (Nat.pow a b = c) a (nat_lit 2 * b + nat_lit 1) (Nat.mul c (Nat.mul c a)) :=
  ⟨fun h1 => by simp [two_mul, pow_add, mul_assoc, ← h1]⟩

/--
Proves `Nat.pow a b = c` where `a` and `b` are raw nat literals. This could be done by just
`rfl` but the kernel does not have a special case implementation for `Nat.pow` so this would
proceed by unary recursion on `b`, which is too slow and also leads to deep recursion.

We instead do the proof by binary recursion, but this can still lead to deep recursion,
so we use an additional trick to do binary subdivision on `log2 b`. As a result this produces
a proof of depth `log (log b)` which will essentially never overflow before the numbers involved
themselves exceed memory limits.
-/
/-
**Mathlib.Meta.NormNum.evalNatPow** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.NormNu
m`。
形式化陈述：(a b : Q(ℕ)) → OptionT CoreM ((c : Q(ℕ)) × Q(«$a».pow «$b» = «$c»))
参数：ℕ；c : Q(ℕ)；«$a».pow «$b» = «$c»。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Proves `Nat.pow a b = c` where `a` and `b` are raw nat literals. This could be d
one by just
`rfl` but the kernel does not have a special case implementation for `Nat.pow` s
o this would
proceed by unary recursion on `b`, which is too slow and also leads to deep recu
rsion.

We instead do the proof by binary recursion, but this can still lead to deep rec
ursion,
so we use an additional trick to do binary subdivision on `log2 b`. As a result 
this produces
a proof of depth `log (log b)` which will essentially never overflow before the 
numbers involved
themselves exceed memory limits.
-/
partial def evalNatPow (a b : Q(ℕ)) : OptionT CoreM ((c : Q(ℕ)) × Q(Nat.pow $a $b = $c)) := do
  if b.natLit! = 0 then
    haveI : $b =Q 0 := ⟨⟩
    return ⟨q(nat_lit 1), q(natPow_zero)⟩
  else if a.natLit! = 0 then
    haveI : $a =Q 0 := ⟨⟩
    have b' : Q(ℕ) := mkRawNatLit (b.natLit! - 1)
    haveI : $b =Q Nat.succ $b' := ⟨⟩
    return ⟨q(nat_lit 0), q(zero_natPow)⟩
  else if a.natLit! = 1 then
    haveI : $a =Q 1 := ⟨⟩
    return ⟨q(nat_lit 1), q(one_natPow)⟩
  else if b.natLit! = 1 then
    haveI : $b =Q 1 := ⟨⟩
    return ⟨a, q(natPow_one)⟩
  else
    guard <| ← Lean.checkExponent b.natLit!
    let ⟨c, p⟩ := go b.natLit!.log2 a q(nat_lit 1) a b _ .rfl
    return ⟨c, q(($p).run)⟩
where
  /-- Invariants: `a ^ b₀ = c₀`, `depth > 0`, `b >>> depth = b₀`, `p := Nat.pow $a $b₀ = $c₀` -/
  go (depth : Nat) (a b₀ c₀ b : Q(ℕ)) (p : Q(Prop)) (hp : $p =Q (Nat.pow $a $b₀ = $c₀)) :
      (c : Q(ℕ)) × Q(IsNatPowT $p $a $b $c) :=
    let b' := b.natLit!
    if depth ≤ 1 then
      let a' := a.natLit!
      let c₀' := c₀.natLit!
      if b' &&& 1 == 0 then
        have c : Q(ℕ) := mkRawNatLit (c₀' * c₀')
        haveI : $c =Q Nat.mul $c₀ $c₀ := ⟨⟩
        haveI : $b =Q 2 * $b₀ := ⟨⟩
        ⟨c, q(IsNatPowT.bit0)⟩
      else
        have c : Q(ℕ) := mkRawNatLit (c₀' * (c₀' * a'))
        haveI : $c =Q Nat.mul $c₀ (Nat.mul $c₀ $a) := ⟨⟩
        haveI : $b =Q 2 * $b₀ + 1 := ⟨⟩
        ⟨c, q(IsNatPowT.bit1)⟩
    else
      let d := depth >>> 1
      have hi : Q(ℕ) := mkRawNatLit (b' >>> d)
      let ⟨c1, p1⟩ := go (depth - d) a b₀ c₀ hi p (by exact hp)
      let ⟨c2, p2⟩ := go d a hi c1 b q(Nat.pow $a $hi = $c1) ⟨⟩
      ⟨c2, q(($p1).trans $p2)⟩
/-
**Mathlib.Meta.NormNum.intPow_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.Norm
Num`。
形式化陈述：intPow_ofNat (h1 : Nat.pow a b = c) : Int.pow (Int.ofNat a) b = Int.ofNat 
c
参数：h1 : Nat.pow a b = c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem intPow_ofNat (h1 : Nat.pow a b = c) :
    Int.pow (Int.ofNat a) b = Int.ofNat c := by simp [← h1]
/-
**Mathlib.Meta.NormNum.intPow_negOfNat_bit0** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.M
eta.NormNum`。
形式化陈述：intPow_negOfNat_bit0 {b' c' : Nat} (h1 : Nat.pow a b' = c') (hb : nat_lit 
2 * b' = b) (hc : c' * c' = c) : Int.pow (Int.negOfNat a) b = Int.ofNat c
参数：h1 : Nat.pow a b' = c'；hb : nat_lit 2 * b' = b；hc : c' * c' = c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.negOfNat_eq`：∀ {n : ℕ}, Int.negOfNat n = -Int.ofNat n
· 使用定理 `Int.pow_eq`：∀ (m : ℤ) (n : ℕ), m.pow n = m ^ n
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `neg_pow_two`：∀ {R : Type u} [inst : Monoid R] [inst_1 : HasDistribNeg R]
 (a : R), (-a) ^ 2 = a ^ 2
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem intPow_negOfNat_bit0 {b' c' : ℕ} (h1 : Nat.pow a b' = c')
    (hb : nat_lit 2 * b' = b) (hc : c' * c' = c) :
    Int.pow (Int.negOfNat a) b = Int.ofNat c := by
  rw [← hb, Int.negOfNat_eq, Int.pow_eq, pow_mul, neg_pow_two, ← pow_mul, two_mul, pow_add, ← hc,
    ← h1]
  simp
/-
**Mathlib.Meta.NormNum.intPow_negOfNat_bit1** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.M
eta.NormNum`。
形式化陈述：intPow_negOfNat_bit1 {b' c' : Nat} (h1 : Nat.pow a b' = c') (hb : nat_lit 
2 * b' + nat_lit 1 = b) (hc : c' * (c' * a) = c) : Int.pow (Int.negOfNat a) b = 
Int.negOfNat c
参数：h1 : Nat.pow a b' = c'；hb : nat_lit 2 * b' + nat_lit 1 = b；hc : c' * (c' * a)
 = c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.negOfNat_eq`：∀ {n : ℕ}, Int.negOfNat n = -Int.ofNat n
· 使用定理 `Int.pow_eq`：∀ (m : ℤ) (n : ℕ), m.pow n = m ^ n
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `neg_pow_two`：∀ {R : Type u} [inst : Monoid R] [inst_1 : HasDistribNeg R]
 (a : R), (-a) ^ 2 = a ^ 2
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem intPow_negOfNat_bit1 {b' c' : ℕ} (h1 : Nat.pow a b' = c')
    (hb : nat_lit 2 * b' + nat_lit 1 = b) (hc : c' * (c' * a) = c) :
    Int.pow (Int.negOfNat a) b = Int.negOfNat c := by
  rw [← hb, Int.negOfNat_eq, Int.negOfNat_eq, Int.pow_eq, pow_succ, pow_mul, neg_pow_two, ← pow_mul,
    two_mul, pow_add, ← hc, ← h1]
  simp [mul_comm, mul_left_comm]

/-- Evaluates `Int.pow a b = c` where `a` and `b` are raw integer literals. -/
/-
**Mathlib.Meta.NormNum.evalIntPow** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.NormNu
m`。
形式化陈述：ℤ → (a : Q(ℤ)) → (b : Q(ℕ)) → OptionT CoreM (ℤ × (c : Q(ℤ)) × Q(«$a».pow «
$b» = «$c»))
参数：a : Q(ℤ)；b : Q(ℕ)；ℤ × (c : Q(ℤ)) × Q(«$a».pow «$b» = «$c»)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluates `Int.pow a b = c` where `a` and `b` are raw integer literals.
-/
partial def evalIntPow (za : ℤ) (a : Q(ℤ)) (b : Q(ℕ)) :
    OptionT CoreM (ℤ × (c : Q(ℤ)) × Q(Int.pow $a $b = $c)) := do
  have a' : Q(ℕ) := a.appArg!
  if 0 ≤ za then
    have : $a =Q .ofNat $a' := ⟨⟩
    let ⟨c, p⟩ ← evalNatPow a' b
    return ⟨c.natLit!, q(.ofNat $c), q(intPow_ofNat $p)⟩
  else
    have : $a =Q .negOfNat $a' := ⟨⟩
    let b' := b.natLit!
    have b₀ : Q(ℕ) := mkRawNatLit (b' >>> 1)
    let ⟨c₀, p⟩ ← evalNatPow a' b₀
    let c' := c₀.natLit!
    if b' &&& 1 == 0 then
      have c : Q(ℕ) := mkRawNatLit (c' * c')
      have pc : Q($c₀ * $c₀ = $c) := (q(Eq.refl $c) : Expr)
      have pb : Q(2 * $b₀ = $b) := (q(Eq.refl $b) : Expr)
      return ⟨c.natLit!, q(.ofNat $c), q(intPow_negOfNat_bit0 $p $pb $pc)⟩
    else
      have c : Q(ℕ) := mkRawNatLit (c' * (c' * a'.natLit!))
      have pc : Q($c₀ * ($c₀ * $a') = $c) := (q(Eq.refl $c) : Expr)
      have pb : Q(2 * $b₀ + 1 = $b) := (q(Eq.refl $b) : Expr)
      return ⟨-c.natLit!, q(.negOfNat $c), q(intPow_negOfNat_bit1 $p $pb $pc)⟩

-- see note [norm_num lemma function equality]
/-
**Mathlib.Meta.NormNum.isNat_pow** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.NormNum
`。
形式化陈述：∀ {α : Type u_1} [inst : Semiring α] {f : α → ℕ → α} {a : α} {b a' b' c : 
ℕ},   f = HPow.hPow →     Mathlib.Meta.NormNum.IsNat a a' →       Mathlib.Meta.N
ormNum.IsNat b b' → a'.pow b' = c → Mathlib.Meta.NormNum.IsNat (f a b) c
参数：f a b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isNat_pow {α} [Semiring α] : ∀ {f : α → ℕ → α} {a : α} {b a' b' c : ℕ},
    f = HPow.hPow → IsNat a a' → IsNat b b' → Nat.pow a' b' = c → IsNat (f a b) c
  | _, _, _, _, _, _, rfl, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨by simp⟩

-- see note [norm_num lemma function equality]
/-
**Mathlib.Meta.NormNum.isInt_pow** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.NormNum
`。
形式化陈述：∀ {α : Type u_1} [inst : Ring α] {f : α → ℕ → α} {a : α} {b : ℕ} {a' : ℤ} 
{b' : ℕ} {c : ℤ},   f = HPow.hPow →     Mathlib.Meta.NormNum.IsInt a a' →       
Mathlib.Meta.NormNum.IsNat b b' → a'.pow b' = c → Mathlib.Meta.NormNum.IsInt (f 
a b) c
参数：f a b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_pow`：∀ {R : Type u_1} [inst : Ring R] (n : ℤ) (m : ℕ), ↑(n ^ m)
 = ↑n ^ m
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isInt_pow {α} [Ring α] : ∀ {f : α → ℕ → α} {a : α} {b : ℕ} {a' : ℤ} {b' : ℕ} {c : ℤ},
    f = HPow.hPow → IsInt a a' → IsNat b b' → Int.pow a' b' = c → IsInt (f a b) c
  | _, _, _, _, _, _, rfl, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨by simp⟩

-- see note [norm_num lemma function equality]
/-
**Mathlib.Meta.NormNum.isRat_pow** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.NormNum
`。
形式化陈述：isRat_pow {α} [Ring α] {f : α -> Nat -> α} {a : α} {an cn : Int} {ad b b' 
cd : Nat} : f = HPow.hPow -> IsRat a an ad -> IsNat b b' -> Int.pow an b' = cn -
> Nat.pow ad b' = cd -> IsRat (f a b) cn cd
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Commute.mul_pow`：∀ {M : Type u_2} [inst : Monoid M] {a b : M}, Commute a
 b → ∀ (n : ℕ), (a * b) ^ n = a ^ n * b ^ n
· 使用定理 `Int.cast_pow`：∀ {R : Type u_1} [inst : Ring R] (n : ℤ) (m : ℕ), ↑(n ^ m)
 = ↑n ^ m
· 使用定理 `Invertible.congr`：Invertible.congr [Invertible a] [Invertible b] (h : a 
= b) : ⅟a = ⅟b
· 使用引理 `invOf_pow`：invOf_pow (m : α) [Invertible m] (n : Nat) [Invertible (m ^ n
)] : ⅟(m ^ n) = ⅟m ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isRat_pow {α} [Ring α] {f : α → ℕ → α} {a : α} {an cn : ℤ} {ad b b' cd : ℕ} :
    f = HPow.hPow → IsRat a an ad → IsNat b b' →
    Int.pow an b' = cn → Nat.pow ad b' = cd →
    IsRat (f a b) cn cd := by
  rintro rfl ⟨_, rfl⟩ ⟨rfl⟩ (rfl : an ^ b = _) (rfl : ad ^ b = _)
  have := invertiblePow (ad:α) b
  rw [← Nat.cast_pow] at this
  use this; simp [invOf_pow, Commute.mul_pow]
/-
**Mathlib.Meta.NormNum.isNNRat_pow** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.NormN
um`。
形式化陈述：isNNRat_pow {α} [Semiring α] {f : α -> Nat -> α} {a : α} {an cn : Nat} {ad
 b b' cd : Nat} : f = HPow.hPow -> IsNNRat a an ad -> IsNat b b' -> Nat.pow an b
' = cn -> Nat.pow ad b' = cd -> IsNNRat (f a b) cn cd
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Commute.mul_pow`：∀ {M : Type u_2} [inst : Monoid M] {a b : M}, Commute a
 b → ∀ (n : ℕ), (a * b) ^ n = a ^ n * b ^ n
· 使用定理 `Invertible.congr`：Invertible.congr [Invertible a] [Invertible b] (h : a 
= b) : ⅟a = ⅟b
· 使用引理 `invOf_pow`：invOf_pow (m : α) [Invertible m] (n : Nat) [Invertible (m ^ n
)] : ⅟(m ^ n) = ⅟m ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isNNRat_pow {α} [Semiring α] {f : α → ℕ → α} {a : α} {an cn : ℕ} {ad b b' cd : ℕ} :
    f = HPow.hPow → IsNNRat a an ad → IsNat b b' →
    Nat.pow an b' = cn → Nat.pow ad b' = cd →
    IsNNRat (f a b) cn cd := by
  rintro rfl ⟨_, rfl⟩ ⟨rfl⟩ (rfl : an ^ b = _) (rfl : ad ^ b = _)
  have := invertiblePow (ad:α) b
  rw [← Nat.cast_pow] at this
  use this; simp [invOf_pow, Commute.mul_pow, Nat.cast_commute]

/-- Main part of `evalPow`. -/
/-
**Mathlib.Meta.NormNum.evalPow.core** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.Norm
Num.evalPow`。
形式化陈述：{u : Level} →   {α : Q(Type u)} →     (e : Q(«$α»)) →       Q(«$α» → ℕ → «
$α») →         (a : Q(«$α»)) →           (b nb : Q(ℕ)) →             Q(Mathlib.M
eta.NormNum.IsNat «$b» «$nb») →               Q(Semiring «$α») → Mathlib.Meta.No
rmNum.Result a → OptionT CoreM (Mathlib.Meta.NormNum.Result e)
参数：Type u；e : Q(«$α»)；«$α» → ℕ → «$α»；a : Q(«$α»)；b nb : Q(ℕ)；Mathlib.Meta.NormN
um.IsNat «$b» «$nb»；Semiring «$α»；Mathlib.Meta.NormNum.Result e。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Main part of `evalPow`.
-/
def evalPow.core {u : Level} {α : Q(Type u)} (e : Q(«$α»)) (f : Q(«$α» → ℕ → «$α»)) (a : Q(«$α»))
    (b nb : Q(ℕ)) (pb : Q(IsNat «$b» «$nb»)) (sα : Q(Semiring «$α»)) (ra : Result a) :
    OptionT CoreM (Result e) := do
  haveI' : $e =Q $a ^ $b := ⟨⟩
  haveI' : $f =Q HPow.hPow := ⟨⟩
  match ra with
  | .isBool .. => failure
  | .isNat sα na pa =>
    assumeInstancesCommute
    let ⟨c, r⟩ ← evalNatPow na nb
    return .isNat sα c q(isNat_pow (f := $f) (.refl $f) $pa $pb $r)
  | .isNegNat rα .. =>
    assumeInstancesCommute
    let ⟨za, na, pa⟩ ← OptionT.mk <| pure (ra.toInt rα)
    let ⟨zc, c, r⟩ ← evalIntPow za na nb
    return .isInt rα c zc q(isInt_pow (f := $f) (.refl $f) $pa $pb $r)
  | .isNNRat dα _qa na da pa =>
    assumeInstancesCommute
    let ⟨nc, r1⟩ ← evalNatPow na nb
    let ⟨dc, r2⟩ ← evalNatPow da nb
    let qc := mkRat nc.natLit! dc.natLit!
    return .isNNRat dα qc nc dc q(isNNRat_pow (f := $f) (.refl $f) $pa $pb $r1 $r2)
  | .isNegNNRat dα qa na da pa =>
    assumeInstancesCommute
    let ⟨zc, nc, r1⟩ ← evalIntPow qa.num q(Int.negOfNat $na) nb
    let ⟨dc, r2⟩ ← evalNatPow da nb
    let qc := mkRat zc dc.natLit!
    return .isRat dα qc nc dc q(isRat_pow (f := $f) (.refl $f) $pa $pb $r1 $r2)

/-- The `norm_num` extension which identifies expressions of the form `a ^ b`,
such that `norm_num` successfully recognises both `a` and `b`, with `b : ℕ`. -/
@[norm_num _ ^ (_ : ℕ)]
/-
**Mathlib.Meta.NormNum.evalPow** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.NormNum`。
形式化陈述：evalPow : NormNumExt where eval {u α} e
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `norm_num` extension which identifies expressions of the form `a ^ b`,
such that `norm_num` successfully recognises both `a` and `b`, with `b : ℕ`.
-/
def evalPow : NormNumExt where eval {u α} e := do
  let .app (.app (f : Q($α → ℕ → $α)) (a : Q($α))) (b : Q(ℕ)) ← whnfR e | failure
  let ⟨nb, pb⟩ ← deriveNat b q(Nat.instAddMonoidWithOne)
  let sα ← inferSemiring α
  let ra ← derive a
  guard <|← withDefault <| withNewMCtxDepth <| isDefEq f q(HPow.hPow (α := $α))
  haveI' : $e =Q $a ^ $b := ⟨⟩
  haveI' : $f =Q HPow.hPow := ⟨⟩
  let .some r ←
    liftM <| OptionT.run (evalPow.core q($e) q($f) q($a) q($b) q($nb) q($pb) q($sα) ra) | failure
  return r
/-
**Mathlib.Meta.NormNum.isNat_zpow_pos** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.No
rmNum`。
形式化陈述：isNat_zpow_pos {α : Type*} [DivisionSemiring α] {a : α} {b : Int} {nb ne :
 Nat} (pb : IsNat b nb) (pe' : IsNat (a ^ nb) ne) : IsNat (a ^ b) ne
参数：pb : IsNat b nb；pe' : IsNat (a ^ nb) ne。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Meta.NormNum.IsNat.out`：∀ {α : Type u} [inst : AddMonoidWithOne 
α] {a : α} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = ↑n
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
-/
theorem isNat_zpow_pos {α : Type*} [DivisionSemiring α] {a : α} {b : ℤ} {nb ne : ℕ}
    (pb : IsNat b nb) (pe' : IsNat (a ^ nb) ne) :
    IsNat (a ^ b) ne := by
  rwa [pb.out, zpow_natCast]
/-
**Mathlib.Meta.NormNum.isNat_zpow_neg** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.No
rmNum`。
形式化陈述：isNat_zpow_neg {α : Type*} [DivisionSemiring α] {a : α} {b : Int} {nb ne :
 Nat} (pb : IsInt b (Int.negOfNat nb)) (pe' : IsNat (a ^ nb)⁻¹ ne) : IsNat (a ^ 
b) ne
参数：pb : IsInt b (Int.negOfNat nb)；pe' : IsNat (a ^ nb)⁻¹ ne。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.out`：∀ {α : Type u} [inst : Ring α] {a : α} {
n : ℤ}, Mathlib.Meta.NormNum.IsInt a n → a = ↑n
· 使用定理 `Int.cast_negOfNat`：cast_negOfNat (n : Nat) : ((negOfNat n : Int) : R) = 
-n
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
-/
theorem isNat_zpow_neg {α : Type*} [DivisionSemiring α] {a : α} {b : ℤ} {nb ne : ℕ}
    (pb : IsInt b (Int.negOfNat nb)) (pe' : IsNat (a ^ nb)⁻¹ ne) :
    IsNat (a ^ b) ne := by
  rwa [pb.out, Int.cast_negOfNat, zpow_neg, zpow_natCast]
/-
**Mathlib.Meta.NormNum.isInt_zpow_pos** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.No
rmNum`。
形式化陈述：isInt_zpow_pos {α : Type*} [DivisionRing α] {a : α} {b : Int} {nb ne : Nat
} (pb : IsNat b nb) (pe' : IsInt (a ^ nb) (Int.negOfNat ne)) : IsInt (a ^ b) (In
t.negOfNat ne)
参数：pb : IsNat b nb；pe' : IsInt (a ^ nb) (Int.negOfNat ne)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Meta.NormNum.IsNat.out`：∀ {α : Type u} [inst : AddMonoidWithOne 
α] {a : α} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = ↑n
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
-/
theorem isInt_zpow_pos {α : Type*} [DivisionRing α] {a : α} {b : ℤ} {nb ne : ℕ}
    (pb : IsNat b nb) (pe' : IsInt (a ^ nb) (Int.negOfNat ne)) :
    IsInt (a ^ b) (Int.negOfNat ne) := by
  rwa [pb.out, zpow_natCast]
/-
**Mathlib.Meta.NormNum.isInt_zpow_neg** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.No
rmNum`。
形式化陈述：isInt_zpow_neg {α : Type*} [DivisionRing α] {a : α} {b : Int} {nb ne : Nat
} (pb : IsInt b (Int.negOfNat nb)) (pe' : IsInt (a ^ nb)⁻¹ (Int.negOfNat ne)) : 
IsInt (a ^ b) (Int.negOfNat ne)
参数：pb : IsInt b (Int.negOfNat nb)；pe' : IsInt (a ^ nb)⁻¹ (Int.negOfNat ne)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.out`：∀ {α : Type u} [inst : Ring α] {a : α} {
n : ℤ}, Mathlib.Meta.NormNum.IsInt a n → a = ↑n
· 使用定理 `Int.cast_negOfNat`：cast_negOfNat (n : Nat) : ((negOfNat n : Int) : R) = 
-n
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
-/
theorem isInt_zpow_neg {α : Type*} [DivisionRing α] {a : α} {b : ℤ} {nb ne : ℕ}
    (pb : IsInt b (Int.negOfNat nb)) (pe' : IsInt (a ^ nb)⁻¹ (Int.negOfNat ne)) :
    IsInt (a ^ b) (Int.negOfNat ne) := by
  rwa [pb.out, Int.cast_negOfNat, zpow_neg, zpow_natCast]
/-
**Mathlib.Meta.NormNum.isNNRat_zpow_pos** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.
NormNum`。
形式化陈述：isNNRat_zpow_pos {α : Type*} [DivisionSemiring α] {a : α} {b : Int} {nb : 
Nat} {num : Nat} {den : Nat} (pb : IsNat b nb) (pe' : IsNNRat (a ^ nb) num den) 
: IsNNRat (a^b) num den
参数：pb : IsNat b nb；pe' : IsNNRat (a ^ nb) num den。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Meta.NormNum.IsNat.out`：∀ {α : Type u} [inst : AddMonoidWithOne 
α] {a : α} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = ↑n
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
-/
theorem isNNRat_zpow_pos {α : Type*} [DivisionSemiring α] {a : α} {b : ℤ} {nb : ℕ}
    {num : ℕ} {den : ℕ}
    (pb : IsNat b nb) (pe' : IsNNRat (a ^ nb) num den) :
    IsNNRat (a^b) num den := by
  rwa [pb.out, zpow_natCast]
/-
**Mathlib.Meta.NormNum.isNNRat_zpow_neg** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.
NormNum`。
形式化陈述：isNNRat_zpow_neg {α : Type*} [DivisionSemiring α] {a : α} {b : Int} {nb : 
Nat} {num : Nat} {den : Nat} (pb : IsInt b (Int.negOfNat nb)) (pe' : IsNNRat ((a
 ^ nb)⁻¹) num den) : IsNNRat (a^b) num den
参数：pb : IsInt b (Int.negOfNat nb)；pe' : IsNNRat ((a ^ nb)⁻¹) num den。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.out`：∀ {α : Type u} [inst : Ring α] {a : α} {
n : ℤ}, Mathlib.Meta.NormNum.IsInt a n → a = ↑n
· 使用定理 `Int.cast_negOfNat`：cast_negOfNat (n : Nat) : ((negOfNat n : Int) : R) = 
-n
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
-/
theorem isNNRat_zpow_neg {α : Type*} [DivisionSemiring α] {a : α} {b : ℤ} {nb : ℕ}
    {num : ℕ} {den : ℕ}
    (pb : IsInt b (Int.negOfNat nb)) (pe' : IsNNRat ((a ^ nb)⁻¹) num den) :
    IsNNRat (a^b) num den := by
  rwa [pb.out, Int.cast_negOfNat, zpow_neg, zpow_natCast]
/-
**Mathlib.Meta.NormNum.isRat_zpow_pos** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.No
rmNum`。
形式化陈述：isRat_zpow_pos {α : Type*} [DivisionRing α] {a : α} {b : Int} {nb : Nat} {
num : Int} {den : Nat} (pb : IsNat b nb) (pe' : IsRat (a ^ nb) num den) : IsRat 
(a ^ b) num den
参数：pb : IsNat b nb；pe' : IsRat (a ^ nb) num den。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Meta.NormNum.IsNat.out`：∀ {α : Type u} [inst : AddMonoidWithOne 
α] {a : α} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = ↑n
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
-/
theorem isRat_zpow_pos {α : Type*} [DivisionRing α] {a : α} {b : ℤ} {nb : ℕ}
    {num : ℤ} {den : ℕ}
    (pb : IsNat b nb) (pe' : IsRat (a ^ nb) num den) :
    IsRat (a ^ b) num den := by
  rwa [pb.out, zpow_natCast]
/-
**Mathlib.Meta.NormNum.isRat_zpow_neg** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.No
rmNum`。
形式化陈述：isRat_zpow_neg {α : Type*} [DivisionRing α] {a : α} {b : Int} {nb : Nat} {
num : Int} {den : Nat} (pb : IsInt b (Int.negOfNat nb)) (pe' : IsRat ((a ^ nb)⁻¹
) num den) : IsRat (a ^ b) num den
参数：pb : IsInt b (Int.negOfNat nb)；pe' : IsRat ((a ^ nb)⁻¹) num den。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.out`：∀ {α : Type u} [inst : Ring α] {a : α} {
n : ℤ}, Mathlib.Meta.NormNum.IsInt a n → a = ↑n
· 使用定理 `Int.cast_negOfNat`：cast_negOfNat (n : Nat) : ((negOfNat n : Int) : R) = 
-n
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
-/
theorem isRat_zpow_neg {α : Type*} [DivisionRing α] {a : α} {b : ℤ} {nb : ℕ}
    {num : ℤ} {den : ℕ}
    (pb : IsInt b (Int.negOfNat nb)) (pe' : IsRat ((a ^ nb)⁻¹) num den) :
    IsRat (a ^ b) num den := by
  rwa [pb.out, Int.cast_negOfNat, zpow_neg, zpow_natCast]

#adaptation_note /-- https://github.com/leanprover/lean4/pull/4096
the two
```
have h : $e =Q (HPow.hPow (γ := $α) $a $b) := ⟨⟩
h.check
```
blocks below were not necessary: we just did it once outside the `match rb with` block.
-/
/-- The `norm_num` extension which identifies expressions of the form `a ^ b`,
such that `norm_num` successfully recognises both `a` and `b`, with `b : ℤ`. -/
@[norm_num _ ^ (_ : ℤ)]
/-
**Mathlib.Meta.NormNum.evalZPow** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.NormNum`
。
形式化陈述：evalZPow : NormNumExt where eval {u α} e
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `norm_num` extension which identifies expressions of the form `a ^ b`,
such that `norm_num` successfully recognises both `a` and `b`, with `b : ℤ`.
-/
def evalZPow : NormNumExt where eval {u α} e := do
  let .app (.app (f : Q($α → ℤ → $α)) (a : Q($α))) (b : Q(ℤ)) ← whnfR e | failure
  let _c ← synthInstanceQ q(DivisionSemiring $α)
  let rb ← derive (α := q(ℤ)) b
  match rb with
  | .isBool .. | .isNNRat _ .. | .isNegNNRat _ .. => failure
  | .isNat sβ nb pb =>
    have h : $e =Q (HPow.hPow (γ := $α) $a $b) := ⟨⟩
    h.check
    match ← derive q($a ^ $nb) with
    | .isBool .. => failure
    | .isNat sα' ne' pe' =>
      assumeInstancesCommute
      return .isNat sα' ne' q(isNat_zpow_pos $pb $pe')
    | .isNegNat sα' ne' pe' =>
      let _c ← synthInstanceQ q(DivisionRing $α)
      assumeInstancesCommute
      return .isNegNat sα' ne' q(isInt_zpow_pos $pb $pe')
    | .isNNRat dsα' qe' nume' dene' pe' =>
      assumeInstancesCommute
      return .isNNRat dsα' qe' nume' dene' q(isNNRat_zpow_pos $pb $pe')
    | .isNegNNRat dα' qe' nume' dene' pe' =>
      assumeInstancesCommute
      let proof := q(isRat_zpow_pos $pb $pe')
      return .isRat dα' qe' nume' dene' proof
  | .isNegNat sβ nb pb =>
    have h : $e =Q (HPow.hPow (γ := $α) $a $b) := ⟨⟩
    h.check
    match ← derive q(($a ^ $nb)⁻¹) with
    | .isBool .. => failure
    | .isNat sα' ne' pe' =>
      assumeInstancesCommute
      return .isNat sα' ne' q(isNat_zpow_neg $pb $pe')
    | .isNegNat sα' ne' pe' =>
      let _c ← synthInstanceQ q(DivisionRing $α)
      assumeInstancesCommute
      return .isNegNat sα' ne' q(isInt_zpow_neg $pb $pe')
    | .isNNRat dsα' qe' nume' dene' pe' =>
      assumeInstancesCommute
      return .isNNRat dsα' qe' nume' dene' q(isNNRat_zpow_neg $pb $pe')
    | .isNegNNRat dα' qe' nume' dene' pe' =>
      assumeInstancesCommute
      return .isRat dα' qe' q(.negOfNat $nume') dene' q(isRat_zpow_neg $pb $pe')

end NormNum

end Meta

end Mathlib

