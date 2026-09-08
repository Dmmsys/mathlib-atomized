/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Mario Carneiro
-/
module

public meta import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Tactic.NormNum

/-! # `norm_num` extension for `Nat.fib`

This `norm_num` extension uses a strategy parallel to that of `Nat.fastFib`, but it instead
produces proofs of what `Nat.fib` evaluates to.
-/

public meta section

namespace Mathlib.Meta.NormNum

open Qq Lean Elab.Tactic
open Nat

/-- Auxiliary definition for `proveFib` extension. -/
/-
**Mathlib.Meta.NormNum.IsFibAux** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.NormNum`
。
形式化陈述：IsFibAux (n a b : Nat)
参数：n a b : Nat。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `proveFib` extension.
-/
def IsFibAux (n a b : ℕ) :=
  fib n = a ∧ fib (n + 1) = b
/-
**Mathlib.Meta.NormNum.isFibAux_zero** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.Nor
mNum`。
形式化陈述：isFibAux_zero : IsFibAux 0 0 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.fib_zero`：fib_zero : fib 0 = 0
· 使用定理 `Nat.fib_one`：fib_one : fib 1 = 1
-/
theorem isFibAux_zero : IsFibAux 0 0 1 :=
  ⟨fib_zero, fib_one⟩
/-
**Mathlib.Meta.NormNum.isFibAux_one** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.Norm
Num`。
形式化陈述：isFibAux_one : IsFibAux 1 1 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.fib_one`：fib_one : fib 1 = 1
· 使用定理 `Nat.fib_two`：fib_two : fib 2 = 1
-/
theorem isFibAux_one : IsFibAux 1 1 1 :=
  ⟨fib_one, fib_two⟩
/-
**Mathlib.Meta.NormNum.isFibAux_two_mul** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.
NormNum`。
形式化陈述：isFibAux_two_mul {n a b n' a' b' : Nat} (H : IsFibAux n a b) (hn : 2 * n =
 n') (h1 : a * (2 * b - a) = a') (h2 : a * a + b * b = b') : IsFibAux n' a' b'
参数：H : IsFibAux n a b；hn : 2 * n = n'；h1 : a * (2 * b - a) = a'；h2 : a * a + b *
 b = b'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.fib_two_mul`：fib_two_mul (n : Nat) : fib (2 * n) = fib n * (2 * fib 
(n + 1) - fib n)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Nat.fib_two_mul_add_one`：fib_two_mul_add_one (n : Nat) : fib (2 * n + 1)
 = fib (n + 1) ^ 2 + fib n ^ 2
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem isFibAux_two_mul {n a b n' a' b' : ℕ} (H : IsFibAux n a b)
    (hn : 2 * n = n') (h1 : a * (2 * b - a) = a') (h2 : a * a + b * b = b') :
    IsFibAux n' a' b' :=
  ⟨by rw [← hn, fib_two_mul, H.1, H.2, ← h1],
   by rw [← hn, fib_two_mul_add_one, H.1, H.2, pow_two, pow_two, add_comm, h2]⟩
/-
**Mathlib.Meta.NormNum.isFibAux_two_mul_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Mathl
ib.Meta.NormNum`。
形式化陈述：isFibAux_two_mul_add_one {n a b n' a' b' : Nat} (H : IsFibAux n a b) (hn :
 2 * n + 1 = n') (h1 : a * a + b * b = a') (h2 : b * (2 * a + b) = b') : IsFibAu
x n' a' b'
参数：H : IsFibAux n a b；hn : 2 * n + 1 = n'；h1 : a * a + b * b = a'；h2 : b * (2 * 
a + b) = b'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.fib_two_mul_add_one`：fib_two_mul_add_one (n : Nat) : fib (2 * n + 1)
 = fib (n + 1) ^ 2 + fib n ^ 2
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Nat.fib_two_mul_add_two`：fib_two_mul_add_two (n : Nat) : fib (2 * n + 2)
 = fib (n + 1) * (2 * fib n + fib (n + 1))
-/
theorem isFibAux_two_mul_add_one {n a b n' a' b' : ℕ} (H : IsFibAux n a b)
    (hn : 2 * n + 1 = n') (h1 : a * a + b * b = a') (h2 : b * (2 * a + b) = b') :
    IsFibAux n' a' b' :=
  ⟨by rw [← hn, fib_two_mul_add_one, H.1, H.2, pow_two, pow_two, add_comm, h1],
   by rw [← hn, fib_two_mul_add_two, H.1, H.2, h2]⟩
/-
**Mathlib.Meta.NormNum.proveNatFibAux** 是 Mathlib 中的一个不透明定义，位于命名空间 `Mathlib.Meta
.NormNum`。
形式化陈述：(en' : Q(ℕ)) → (ea' : Q(ℕ)) × (eb' : Q(ℕ)) × Q(Mathlib.Meta.NormNum.IsFibA
ux «$en'» «$ea'» «$eb'»)
参数：ℕ；ℕ；ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
partial def proveNatFibAux (en' : Q(ℕ)) : (ea' eb' : Q(ℕ)) × Q(IsFibAux $en' $ea' $eb') :=
  match en'.natLit! with
  | 0 =>
    have : $en' =Q nat_lit 0 := ⟨⟩;
    ⟨q(nat_lit 0), q(nat_lit 1), q(isFibAux_zero)⟩
  | 1 =>
    have : $en' =Q nat_lit 1 := ⟨⟩;
    ⟨q(nat_lit 1), q(nat_lit 1), q(isFibAux_one)⟩
  | n' =>
    have en : Q(ℕ) := mkRawNatLit <| n' / 2
    let ⟨ea, eb, H⟩ := proveNatFibAux en
    let a := ea.natLit!
    let b := eb.natLit!
    if n' % 2 == 0 then
      have hn : Q(2 * $en = $en') := (q(Eq.refl $en') : Expr)
      have ea' : Q(ℕ) := mkRawNatLit <| a * (2 * b - a)
      have eb' : Q(ℕ) := mkRawNatLit <| a * a + b * b
      have h1 : Q($ea * (2 * $eb - $ea) = $ea') := (q(Eq.refl $ea') : Expr)
      have h2 : Q($ea * $ea + $eb * $eb = $eb') := (q(Eq.refl $eb') : Expr)
      ⟨ea', eb', q(isFibAux_two_mul $H $hn $h1 $h2)⟩
    else
      have hn : Q(2 * $en + 1 = $en') := (q(Eq.refl $en') : Expr)
      have ea' : Q(ℕ) := mkRawNatLit <| a * a + b * b
      have eb' : Q(ℕ) := mkRawNatLit <| b * (2 * a + b)
      have h1 : Q($ea * $ea + $eb * $eb = $ea') := (q(Eq.refl $ea') : Expr)
      have h2 : Q($eb * (2 * $ea + $eb) = $eb') := (q(Eq.refl $eb') : Expr)
      ⟨ea', eb', q(isFibAux_two_mul_add_one $H $hn $h1 $h2)⟩
/-
**Mathlib.Meta.NormNum.isFibAux_two_mul_done** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.
Meta.NormNum`。
形式化陈述：isFibAux_two_mul_done {n a b n' a' : Nat} (H : IsFibAux n a b) (hn : 2 * n
 = n') (h : a * (2 * b - a) = a') : fib n' = a'
参数：H : IsFibAux n a b；hn : 2 * n = n'；h : a * (2 * b - a) = a'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Mathlib.Meta.NormNum.isFibAux_two_mul`：isFibAux_two_mul {n a b n' a' b' 
: Nat} (H : IsFibAux n a b) (hn : 2 * n = n') (h1 : a * (2 * b - a) = a') (h2 : 
a * a + b * b = b') : IsFib…
-/
theorem isFibAux_two_mul_done {n a b n' a' : ℕ} (H : IsFibAux n a b)
    (hn : 2 * n = n') (h : a * (2 * b - a) = a') : fib n' = a' :=
  (isFibAux_two_mul H hn h rfl).1
/-
**Mathlib.Meta.NormNum.isFibAux_two_mul_add_one_done** 是 Mathlib 中的一个定理，位于命名空间 `
Mathlib.Meta.NormNum`。
形式化陈述：isFibAux_two_mul_add_one_done {n a b n' a' : Nat} (H : IsFibAux n a b) (hn
 : 2 * n + 1 = n') (h : a * a + b * b = a') : fib n' = a'
参数：H : IsFibAux n a b；hn : 2 * n + 1 = n'；h : a * a + b * b = a'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Mathlib.Meta.NormNum.isFibAux_two_mul_add_one`：isFibAux_two_mul_add_one 
{n a b n' a' b' : Nat} (H : IsFibAux n a b) (hn : 2 * n + 1 = n') (h1 : a * a + 
b * b = a') (h2 : b * (2 * a + b) =…
-/
theorem isFibAux_two_mul_add_one_done {n a b n' a' : ℕ} (H : IsFibAux n a b)
    (hn : 2 * n + 1 = n') (h : a * a + b * b = a') : fib n' = a' :=
  (isFibAux_two_mul_add_one H hn h rfl).1

/-- Given the natural number literal `ex`, returns `Nat.fib ex` as a natural number literal
and an equality proof. Panics if `ex` isn't a natural number literal. -/
/-
**Mathlib.Meta.NormNum.proveNatFib** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.NormN
um`。
形式化陈述：proveNatFib (en' : Q(Nat)) : (em : Q(Nat)) × Q(Nat.fib $en' = $em)
参数：en' : Q(Nat)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given the natural number literal `ex`, returns `Nat.fib ex` as a natural number 
literal
and an equality proof. Panics if `ex` isn't a natural number literal.
-/
def proveNatFib (en' : Q(ℕ)) : (em : Q(ℕ)) × Q(Nat.fib $en' = $em) :=
  match en'.natLit! with
  | 0 => have : $en' =Q nat_lit 0 := ⟨⟩; ⟨q(nat_lit 0), q(Nat.fib_zero)⟩
  | 1 => have : $en' =Q nat_lit 1 := ⟨⟩; ⟨q(nat_lit 1), q(Nat.fib_one)⟩
  | 2 => have : $en' =Q nat_lit 2 := ⟨⟩; ⟨q(nat_lit 1), q(Nat.fib_two)⟩
  | n' =>
    have en : Q(ℕ) := mkRawNatLit <| n' / 2
    let ⟨ea, eb, H⟩ := proveNatFibAux en
    let a := ea.natLit!
    let b := eb.natLit!
    if n' % 2 == 0 then
      have hn : Q(2 * $en = $en') := (q(Eq.refl $en') : Expr)
      have ea' : Q(ℕ) := mkRawNatLit <| a * (2 * b - a)
      have h1 : Q($ea * (2 * $eb - $ea) = $ea') := (q(Eq.refl $ea') : Expr)
      ⟨ea', q(isFibAux_two_mul_done $H $hn $h1)⟩
    else
      have hn : Q(2 * $en + 1 = $en') := (q(Eq.refl $en') : Expr)
      have ea' : Q(ℕ) := mkRawNatLit <| a * a + b * b
      have h1 : Q($ea * $ea + $eb * $eb = $ea') := (q(Eq.refl $ea') : Expr)
      ⟨ea', q(isFibAux_two_mul_add_one_done $H $hn $h1)⟩
/-
**Mathlib.Meta.NormNum.isNat_fib** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.NormNum
`。
形式化陈述：∀ {x nx z : ℕ}, Mathlib.Meta.NormNum.IsNat x nx → Nat.fib nx = z → Mathlib
.Meta.NormNum.IsNat (Nat.fib x) z
参数：Nat.fib x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isNat_fib : {x nx z : ℕ} → IsNat x nx → Nat.fib nx = z → IsNat (Nat.fib x) z
  | _, _, _, ⟨rfl⟩, rfl => ⟨rfl⟩

/-- Evaluates the `Nat.fib` function. -/
@[norm_num Nat.fib _]
/-
**Mathlib.Meta.NormNum.evalNatFib** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.NormNu
m`。
形式化陈述：evalNatFib : NormNumExt where eval {_ _} e
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluates the `Nat.fib` function.
-/
def evalNatFib : NormNumExt where eval {_ _} e := do
  let .app _ (x : Q(ℕ)) ← Meta.whnfR e | failure
  let sℕ : Q(AddMonoidWithOne ℕ) := q(Nat.instAddMonoidWithOne)
  let ⟨ex, p⟩ ← deriveNat x sℕ
  let ⟨ey, pf⟩ := proveNatFib ex
  let pf' : Q(IsNat (Nat.fib $x) $ey) := q(isNat_fib $p $pf)
  return .isNat sℕ ey pf'

end NormNum

end Meta

end Mathlib

