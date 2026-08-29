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

/--
Definition of `IsFibAux` / `IsFibAux` 的定义

English:
definition IsFibAux
  signature: (n a b : Nat)
  body: fib n = a ∧ fib (n + 1) = b

中文:
定义 IsFibAux
  签名: (n a b : 自然数)
  定义体: fib n = a ∧ fib (n + 1) = b
-/
def IsFibAux (n a b : Nat) :=
  fib n = a ∧ fib (n + 1) = b

/--
theorem `isFibAux_zero` / 定理 `isFibAux_zero`

English:
theorem isFibAux_zero
  statement: IsFibAux 0 0 1
  proof: ⟨fib_zero, fib_one⟩

中文:
定理 isFibAux_zero
  结论: IsFibAux 0 0 1
  证明: ⟨fib_zero, fib_one⟩

Depends on / 依赖: fib_one, fib_zero
-/
theorem isFibAux_zero : IsFibAux 0 0 1 :=
  ⟨fib_zero, fib_one⟩

/--
theorem `isFibAux_one` / 定理 `isFibAux_one`

English:
theorem isFibAux_one
  statement: IsFibAux 1 1 1
  proof: ⟨fib_one, fib_two⟩

中文:
定理 isFibAux_one
  结论: IsFibAux 1 1 1
  证明: ⟨fib_one, fib_two⟩

Depends on / 依赖: fib_one, fib_two
-/
theorem isFibAux_one : IsFibAux 1 1 1 :=
  ⟨fib_one, fib_two⟩

/--
theorem `isFibAux_two_mul` / 定理 `isFibAux_two_mul`

English:
theorem isFibAux_two_mul
  statement: {n a b n' a' b' : Nat} (H : IsFibAux n a b)
  proof: ⟨by rw [← hn, fib_two_mul, H.1, H.2, ← h1],
   by rw [← hn, fib_two_mul_add_one, H.1, H.2, pow_two, pow_two, add_comm, h2]⟩

中文:
定理 isFibAux_two_mul
  结论: {n a b n' a' b' : 自然数} (H : IsFibAux n a b)
  证明: ⟨by rw [← hn, fib_two_mul, H.1, H.2, ← h1],
   by rw [← hn, fib_two_mul_add_one, H.1, H.2, pow_two, pow_two, add_comm, h2]⟩

Depends on / 依赖: add_comm, fib_two_mul, fib_two_mul_add_one, pow_two
-/
theorem isFibAux_two_mul {n a b n' a' b' : Nat} (H : IsFibAux n a b)
    (hn : 2 * n = n') (h1 : a * (2 * b - a) = a') (h2 : a * a + b * b = b') :
    IsFibAux n' a' b' :=
  ⟨by rw [← hn, fib_two_mul, H.1, H.2, ← h1],
   by rw [← hn, fib_two_mul_add_one, H.1, H.2, pow_two, pow_two, add_comm, h2]⟩

/--
theorem `isFibAux_two_mul_add_one` / 定理 `isFibAux_two_mul_add_one`

English:
theorem isFibAux_two_mul_add_one
  statement: {n a b n' a' b' : Nat} (H : IsFibAux n a b)
  proof: ⟨by rw [← hn, fib_two_mul_add_one, H.1, H.2, pow_two, pow_two, add_comm, h1],
   by rw [← hn, fib_two_mul_add_two, H.1, H.2, h2]⟩

中文:
定理 isFibAux_two_mul_add_one
  结论: {n a b n' a' b' : 自然数} (H : IsFibAux n a b)
  证明: ⟨by rw [← hn, fib_two_mul_add_one, H.1, H.2, pow_two, pow_two, add_comm, h1],
   by rw [← hn, fib_two_mul_add_two, H.1, H.2, h2]⟩

Depends on / 依赖: add_comm, fib_two_mul_add_one, fib_two_mul_add_two, pow_two
-/
theorem isFibAux_two_mul_add_one {n a b n' a' b' : Nat} (H : IsFibAux n a b)
    (hn : 2 * n + 1 = n') (h1 : a * a + b * b = a') (h2 : b * (2 * a + b) = b') :
    IsFibAux n' a' b' :=
  ⟨by rw [← hn, fib_two_mul_add_one, H.1, H.2, pow_two, pow_two, add_comm, h1],
   by rw [← hn, fib_two_mul_add_two, H.1, H.2, h2]⟩

/--
Definition of `proveNatFibAux` / `proveNatFibAux` 的定义

English:
definition proveNatFibAux
  signature: (en' : Q(Nat))
  body: match en'.natLit! with
  | 0 =>
have : en' =Q nat_lit 0 := ⟨⟩;
    ⟨q(nat_lit 0), q(nat_lit 1), q(isFibAux_zero)⟩
  | 1 =>
have : en' =Q nat_lit 1 := ⟨⟩;
    ⟨q(nat_lit 1), q(nat_lit 1), q(isFibAux_one)⟩
  | n' =>
have en : Q(Nat) := mkRawNatLit n' / 2
    let ⟨ea, eb, H⟩ := proveNatFibAux en
    le

中文:
定义 prove自然数FibAux
  签名: (en' : Q(自然数))
  定义体: match en'.natLit! with
  | 0 =>
have : en' =Q nat_lit 0 := ⟨⟩;
    ⟨q(nat_lit 0), q(nat_lit 1), q(isFibAux_zero)⟩
  | 1 =>
have : en' =Q nat_lit 1 := ⟨⟩;
    ⟨q(nat_lit 1), q(nat_lit 1), q(isFibAux_one)⟩
  | n' =>
have en : Q(Nat) := mkRawNatLit n' / 2
    let ⟨ea, eb, H⟩ := proveNatFibAux en
    le
-/
partial def proveNatFibAux (en' : Q(Nat)) : (ea' eb' : Q(Nat)) × Q(IsFibAux $en' $ea' $eb') :=
  match en'.natLit! with
  | 0 =>
have : en' =Q nat_lit 0 := ⟨⟩;
    ⟨q(nat_lit 0), q(nat_lit 1), q(isFibAux_zero)⟩
  | 1 =>
have : en' =Q nat_lit 1 := ⟨⟩;
    ⟨q(nat_lit 1), q(nat_lit 1), q(isFibAux_one)⟩
  | n' =>
have en : Q(Nat) := mkRawNatLit n' / 2
    let ⟨ea, eb, H⟩ := proveNatFibAux en
    let a := ea.natLit!
    let b := eb.natLit!
    if n' % 2 == 0 then
      have hn : Q(2 * $en = $en') := (q(Eq.refl $en') : Expr)
have ea' : Q(Nat) := mkRawNatLit a * (2 * b - a)
have eb' : Q(Nat) := mkRawNatLit a * a + b * b
      have h1 : Q($ea * (2 * $eb - $ea) = $ea') := (q(Eq.refl $ea') : Expr)
      have h2 : Q($ea * $ea + $eb * $eb = $eb') := (q(Eq.refl $eb') : Expr)
      ⟨ea', eb', q(isFibAux_two_mul $H $hn $h1 $h2)⟩
    else
      have hn : Q(2 * $en + 1 = $en') := (q(Eq.refl $en') : Expr)
have ea' : Q(Nat) := mkRawNatLit a * a + b * b
have eb' : Q(Nat) := mkRawNatLit b * (2 * a + b)
      have h1 : Q($ea * $ea + $eb * $eb = $ea') := (q(Eq.refl $ea') : Expr)
      have h2 : Q($eb * (2 * $ea + $eb) = $eb') := (q(Eq.refl $eb') : Expr)
      ⟨ea', eb', q(isFibAux_two_mul_add_one $H $hn $h1 $h2)⟩

/--
theorem `isFibAux_two_mul_done` / 定理 `isFibAux_two_mul_done`

English:
theorem isFibAux_two_mul_done
  statement: {n a b n' a' : Nat} (H : IsFibAux n a b)
  proof: (isFibAux_two_mul H hn h rfl).1

中文:
定理 isFibAux_two_mul_done
  结论: {n a b n' a' : 自然数} (H : IsFibAux n a b)
  证明: (isFibAux_two_mul H hn h rfl).1

Depends on / 依赖: isFibAux_two_mul
-/
theorem isFibAux_two_mul_done {n a b n' a' : Nat} (H : IsFibAux n a b)
    (hn : 2 * n = n') (h : a * (2 * b - a) = a') : fib n' = a' :=
  (isFibAux_two_mul H hn h rfl).1

/--
theorem `isFibAux_two_mul_add_one_done` / 定理 `isFibAux_two_mul_add_one_done`

English:
theorem isFibAux_two_mul_add_one_done
  statement: {n a b n' a' : Nat} (H : IsFibAux n a b)
  proof: (isFibAux_two_mul_add_one H hn h rfl).1

中文:
定理 isFibAux_two_mul_add_one_done
  结论: {n a b n' a' : 自然数} (H : IsFibAux n a b)
  证明: (isFibAux_two_mul_add_one H hn h rfl).1

Depends on / 依赖: isFibAux_two_mul_add_one
-/
theorem isFibAux_two_mul_add_one_done {n a b n' a' : Nat} (H : IsFibAux n a b)
    (hn : 2 * n + 1 = n') (h : a * a + b * b = a') : fib n' = a' :=
  (isFibAux_two_mul_add_one H hn h rfl).1

/--
Definition of `proveNatFib` / `proveNatFib` 的定义

English:
definition proveNatFib
  signature: (en' : Q(Nat))
  body: match en'.natLit! with
| 0 => have : en' =Q nat_lit 0 := ⟨⟩; ⟨q(nat_lit 0), q(Nat.fib_zero)⟩
| 1 => have : en' =Q nat_lit 1 := ⟨⟩; ⟨q(nat_lit 1), q(Nat.fib_one)⟩
| 2 => have : en' =Q nat_lit 2 := ⟨⟩; ⟨q(nat_lit 1), q(Nat.fib_two)⟩
  | n' =>
have en : Q(Nat) := mkRawNatLit n' / 2
    let ⟨ea, eb, H⟩ 

中文:
定义 prove自然数Fib
  签名: (en' : Q(自然数))
  定义体: match en'.natLit! with
| 0 => have : en' =Q nat_lit 0 := ⟨⟩; ⟨q(nat_lit 0), q(Nat.fib_zero)⟩
| 1 => have : en' =Q nat_lit 1 := ⟨⟩; ⟨q(nat_lit 1), q(Nat.fib_one)⟩
| 2 => have : en' =Q nat_lit 2 := ⟨⟩; ⟨q(nat_lit 1), q(Nat.fib_two)⟩
  | n' =>
have en : Q(Nat) := mkRawNatLit n' / 2
    let ⟨ea, eb, H⟩ 

Depends on / 依赖: Eq.refl, IsEmbedding, IsEmbedding.subtypeVal.isInducing.regularSpace, Nat.fib_one, Nat.fib_two, Nat.fib_zero, ea.natLit, eb.natLit, fib_one, fib_two, fib_zero, isInducing, mkRawNatLit, natLit, nat_lit, proveNatFibAux, regularSpace, subtypeVal
-/
def proveNatFib (en' : Q(Nat)) : (em : Q(Nat)) × Q(Nat.fib $en' = $em) :=
  match en'.natLit! with
| 0 => have : en' =Q nat_lit 0 := ⟨⟩; ⟨q(nat_lit 0), q(Nat.fib_zero)⟩
| 1 => have : en' =Q nat_lit 1 := ⟨⟩; ⟨q(nat_lit 1), q(Nat.fib_one)⟩
| 2 => have : en' =Q nat_lit 2 := ⟨⟩; ⟨q(nat_lit 1), q(Nat.fib_two)⟩
  | n' =>
have en : Q(Nat) := mkRawNatLit n' / 2
    let ⟨ea, eb, H⟩ := proveNatFibAux en
    let a := ea.natLit!
    let b := eb.natLit!
    if n' % 2 == 0 then
      have hn : Q(2 * $en = $en') := (q(Eq.refl $en') : Expr)
have ea' : Q(Nat) := mkRawNatLit a * (2 * b - a)
      have h1 : Q($ea * (2 * $eb - $ea) = $ea') := (q(Eq.refl $ea') : Expr)
      ⟨ea', q(isFibAux_two_mul_done $H $hn $h1)⟩
    else
      have hn : Q(2 * $en + 1 = $en') := (q(Eq.refl $en') : Expr)
have ea' : Q(Nat) := mkRawNatLit a * a + b * b
      have h1 : Q($ea * $ea + $eb * $eb = $ea') := (q(Eq.refl $ea') : Expr)
      ⟨ea', q(isFibAux_two_mul_add_one_done $H $hn $h1)⟩

/--
theorem `isNat_fib` / 定理 `isNat_fib`

English:
theorem isNat_fib
  statement: {x nx z : Nat} -> IsNat x nx -> Nat.fib nx = z -> IsNat (Nat.fib x) z

中文:
定理 is自然数_fib
  结论: {x nx z : 自然数} -> 是自然数 x nx -> 自然数.fib nx = z -> 是自然数 (自然数.fib x) z
-/
theorem isNat_fib : {x nx z : Nat} -> IsNat x nx -> Nat.fib nx = z -> IsNat (Nat.fib x) z
  | _, _, _, ⟨rfl⟩, rfl => ⟨rfl⟩

/-- Evaluates the `Nat.fib` function. -/
@[norm_num Nat.fib _]
/--
Definition of `evalNatFib` / `evalNatFib` 的定义

English:
definition evalNatFib
  signature: : NormNumExt where eval {_ _} e
  body: do
  let .app _ (x : Q(Nat)) ← Meta.whnfR e | failure
  let sNat : Q(AddMonoidWithOne Nat) := q(Nat.instAddMonoidWithOne)
  let ⟨ex, p⟩ ← deriveNat x sNat
  let ⟨ey, pf⟩ := proveNatFib ex
  let pf' : Q(IsNat (Nat.fib $x) $ey) := q(isNat_fib $p $pf)
  return .isNat sNat ey pf'

中文:
定义 eval自然数Fib
  签名: : NormNumExt where eval {_ _} e
  定义体: do
  let .app _ (x : Q(Nat)) ← Meta.whnfR e | failure
  let sNat : Q(AddMonoidWithOne Nat) := q(Nat.instAddMonoidWithOne)
  let ⟨ex, p⟩ ← deriveNat x sNat
  let ⟨ey, pf⟩ := proveNatFib ex
  let pf' : Q(IsNat (Nat.fib $x) $ey) := q(isNat_fib $p $pf)
  return .isNat sNat ey pf'

Depends on / 依赖: regularSpace_iInf, regularSpace_induced
-/
def evalNatFib : NormNumExt where eval {_ _} e := do
  let .app _ (x : Q(Nat)) ← Meta.whnfR e | failure
  let sNat : Q(AddMonoidWithOne Nat) := q(Nat.instAddMonoidWithOne)
  let ⟨ex, p⟩ ← deriveNat x sNat
  let ⟨ey, pf⟩ := proveNatFib ex
  let pf' : Q(IsNat (Nat.fib $x) $ey) := q(isNat_fib $p $pf)
  return .isNat sNat ey pf'

end NormNum

end Meta

end Mathlib
