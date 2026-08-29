/-
Copyright (c) 2023 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.Tactic.NormNum.Pow

/-!
# `norm_num` handling for expressions of the form `a ^ b % m`.

These expressions can often be evaluated efficiently in cases where first evaluating `a ^ b` and
then reducing mod `m` is not feasible. We provide a function `evalNatPowMod` which is used by the
`reduce_mod_char` tactic to efficiently evaluate powers in rings with positive characteristic.

The approach taken here is identical to (and copied from) the development in
`Mathlib/Tactic/NormNum/Pow.lean`.

## TODO

* Adapt the `norm_num` extensions for `Nat.mod` and `Int.emod` to efficiently evaluate expressions
  of the form `a ^ b % m` using `evalNatPowMod`.

-/

public meta section

assert_not_exists RelIso

set_option autoImplicit true

namespace Mathlib
open Lean
open Meta

namespace Meta.NormNum
open Qq

/--
Definition of `IsNatPowModT` / `IsNatPowModT` 的定义

English:
structure IsNatPowModT
  parameters: (p : Prop) (a b m c : Nat)
  axioms and operations (1):
    - run' : p -> Nat.mod (Nat.pow a b) m = c

中文:
结构 是自然数PowModT
  参数: (p : 命题) (a b m c : 自然数)
  公理与运算 (1 个):
    - run' : p -> 自然数.mod (自然数.pow a b) m = c
-/
structure IsNatPowModT (p : Prop) (a b m c : Nat) : Prop where
  run' : p -> Nat.mod (Nat.pow a b) m = c

/--
theorem `IsNatPowModT.run` / 定理 `IsNatPowModT.run`

English:
theorem IsNatPowModT.run
  proof: p.run' (congr_arg (fun x => x % m) (Nat.pow_one a))

中文:
定理 是自然数PowModT.run
  证明: p.run' (congr_arg (fun x => x % m) (Nat.pow_one a))

Depends on / 依赖: Nat.pow_one, congr_arg, p.run, pow_one
-/
theorem IsNatPowModT.run
    (p : IsNatPowModT (Nat.mod (Nat.pow a (nat_lit 1)) m = Nat.mod a m) a b m c) :
    Nat.mod (Nat.pow a b) m = c := p.run' (congr_arg (fun x => x % m) (Nat.pow_one a))

/--
theorem `IsNatPowModT.trans` / 定理 `IsNatPowModT.trans`

English:
theorem IsNatPowModT.trans
  statement: (h1 : IsNatPowModT p a b m c)
  proof: ⟨h2.run' ∘ h1.run'⟩

中文:
定理 是自然数PowModT.trans
  结论: (h1 : 是自然数PowModT p a b m c)
  证明: ⟨h2.run' ∘ h1.run'⟩

Depends on / 依赖: h1.run, h2.run
-/
theorem IsNatPowModT.trans (h1 : IsNatPowModT p a b m c)
    (h2 : IsNatPowModT (Nat.mod (Nat.pow a b) m = c) a b' m c') : IsNatPowModT p a b' m c' :=
  ⟨h2.run' ∘ h1.run'⟩

/--
theorem `IsNatPowModT.bit0` / 定理 `IsNatPowModT.bit0`

English:
theorem IsNatPowModT.bit0
  proof: ⟨fun h1 => by simp only [two_mul, Nat.pow_eq, pow_add, ← h1, Nat.mul_eq]; exact Nat.mul_mod ..⟩

中文:
定理 是自然数PowModT.bit0
  证明: ⟨fun h1 => by simp only [two_mul, Nat.pow_eq, pow_add, ← h1, Nat.mul_eq]; exact Nat.mul_mod ..⟩

Depends on / 依赖: Nat.mul_eq, Nat.mul_mod, Nat.pow_eq, mul_eq, mul_mod, pow_add, pow_eq, two_mul
-/
theorem IsNatPowModT.bit0 :
    IsNatPowModT (Nat.mod (Nat.pow a b) m = c) a (nat_lit 2 * b) m (Nat.mod (Nat.mul c c) m) :=
  ⟨fun h1 => by simp only [two_mul, Nat.pow_eq, pow_add, ← h1, Nat.mul_eq]; exact Nat.mul_mod ..⟩

/--
theorem `natPow_zero_natMod_zero` / 定理 `natPow_zero_natMod_zero`

English:
theorem natPow_zero_natMod_zero
  statement: Nat.mod (Nat.pow a (nat_lit 0)) (nat_lit 0) = nat_lit 1
  proof: by
  simp [Nat.mod, Nat.modCore]

中文:
定理 natPow_zero_natMod_zero
  结论: 自然数.mod (自然数.pow a (nat_lit 0)) (nat_lit 0) = nat_lit 1
  证明: by
  simp [Nat.mod, Nat.modCore]

Depends on / 依赖: Nat.mod, Nat.modCore, modCore
-/
theorem natPow_zero_natMod_zero : Nat.mod (Nat.pow a (nat_lit 0)) (nat_lit 0) = nat_lit 1 := by
  simp [Nat.mod, Nat.modCore]

/--
theorem `natPow_zero_natMod_one` / 定理 `natPow_zero_natMod_one`

English:
theorem natPow_zero_natMod_one
  statement: Nat.mod (Nat.pow a (nat_lit 0)) (nat_lit 1) = nat_lit 0
  proof: by
  simp [Nat.mod, Nat.modCore_eq]

中文:
定理 natPow_zero_natMod_one
  结论: 自然数.mod (自然数.pow a (nat_lit 0)) (nat_lit 1) = nat_lit 0
  证明: by
  simp [Nat.mod, Nat.modCore_eq]

Depends on / 依赖: Nat.mod, Nat.modCore_eq, modCore_eq
-/
theorem natPow_zero_natMod_one : Nat.mod (Nat.pow a (nat_lit 0)) (nat_lit 1) = nat_lit 0 := by
  simp [Nat.mod, Nat.modCore_eq]

/--
theorem `natPow_zero_natMod_succ_succ` / 定理 `natPow_zero_natMod_succ_succ`

English:
theorem natPow_zero_natMod_succ_succ
  proof: by
  rfl

中文:
定理 natPow_zero_natMod_succ_succ
  证明: by
  rfl
-/
theorem natPow_zero_natMod_succ_succ :
    Nat.mod (Nat.pow a (nat_lit 0)) (Nat.succ (Nat.succ m)) = nat_lit 1 := by
  rfl

/--
theorem `natPow_one_natMod` / 定理 `natPow_one_natMod`

English:
theorem natPow_one_natMod
  statement: Nat.mod (Nat.pow a (nat_lit 1)) m = Nat.mod a m
  proof: by rw [natPow_one]

中文:
定理 natPow_one_natMod
  结论: 自然数.mod (自然数.pow a (nat_lit 1)) m = 自然数.mod a m
  证明: by rw [natPow_one]

Depends on / 依赖: natPow_one
-/
theorem natPow_one_natMod : Nat.mod (Nat.pow a (nat_lit 1)) m = Nat.mod a m := by rw [natPow_one]

/--
theorem `IsNatPowModT.bit1` / 定理 `IsNatPowModT.bit1`

English:
theorem IsNatPowModT.bit1
  proof: ⟨by
    rintro rfl
    change a ^ (2 * b + 1) % m = (a ^ b % m) * ((a ^ b % m * a) % m) % m
    rw [pow_add]; rw [two_mul]; rw [pow_add]; rw [pow_one]; rw [Nat.mul_mod (a ^ b % m) a]; rw [Nat.mod_mod]; rw [← Nat.mul_mod (a ^ b) a]; rw [← Nat.mul_mod]; rw [mul_assoc]⟩

中文:
定理 是自然数PowModT.bit1
  证明: ⟨by
    rintro rfl
    change a ^ (2 * b + 1) % m = (a ^ b % m) * ((a ^ b % m * a) % m) % m
    rw [pow_add]; rw [two_mul]; rw [pow_add]; rw [pow_one]; rw [Nat.mul_mod (a ^ b % m) a]; rw [Nat.mod_mod]; rw [← Nat.mul_mod (a ^ b) a]; rw [← Nat.mul_mod]; rw [mul_assoc]⟩

Depends on / 依赖: Nat.mod_mod, Nat.mul_mod, mod_mod, mul_assoc, mul_mod, pow_add, pow_one, two_mul
-/
theorem IsNatPowModT.bit1 :
    IsNatPowModT (Nat.mod (Nat.pow a b) m = c) a (nat_lit 2 * b + 1) m
      (Nat.mod (Nat.mul c (Nat.mod (Nat.mul c a) m)) m) :=
  ⟨by
    rintro rfl
    change a ^ (2 * b + 1) % m = (a ^ b % m) * ((a ^ b % m * a) % m) % m
    rw [pow_add]; rw [two_mul]; rw [pow_add]; rw [pow_one]; rw [Nat.mul_mod (a ^ b % m) a]; rw [Nat.mod_mod]; rw [← Nat.mul_mod (a ^ b) a]; rw [← Nat.mul_mod]; rw [mul_assoc]⟩

/--
Definition of `evalNatPowMod` / `evalNatPowMod` 的定义

English:
definition evalNatPowMod
  signature: (a b m : Q(Nat))
  body: if b.natLit! = 0 then
haveI : b =Q 0 := ⟨⟩
    if m.natLit! = 0 then -- a ^ 0 % 0 = 1
haveI : m =Q 0 := ⟨⟩
      ⟨q(nat_lit 1), q(natPow_zero_natMod_zero)⟩
    else
      have m' : Q(Nat) := mkRawNatLit (m.natLit! - 1)
      if m'.natLit! = 0 then -- a ^ 0 % 1 = 0
haveI : m =Q 1 := ⟨⟩
        ⟨q(nat

中文:
定义 eval自然数PowMod
  签名: (a b m : Q(自然数))
  定义体: if b.natLit! = 0 then
haveI : b =Q 0 := ⟨⟩
    if m.natLit! = 0 then -- a ^ 0 % 0 = 1
haveI : m =Q 0 := ⟨⟩
      ⟨q(nat_lit 1), q(natPow_zero_natMod_zero)⟩
    else
      have m' : Q(Nat) := mkRawNatLit (m.natLit! - 1)
      if m'.natLit! = 0 then -- a ^ 0 % 1 = 0
haveI : m =Q 1 := ⟨⟩
        ⟨q(nat
-/
partial def evalNatPowMod (a b m : Q(Nat)) : (c : Q(Nat)) × Q(Nat.mod (Nat.pow $a $b) $m = $c) :=
  if b.natLit! = 0 then
haveI : b =Q 0 := ⟨⟩
    if m.natLit! = 0 then -- a ^ 0 % 0 = 1
haveI : m =Q 0 := ⟨⟩
      ⟨q(nat_lit 1), q(natPow_zero_natMod_zero)⟩
    else
      have m' : Q(Nat) := mkRawNatLit (m.natLit! - 1)
      if m'.natLit! = 0 then -- a ^ 0 % 1 = 0
haveI : m =Q 1 := ⟨⟩
        ⟨q(nat_lit 0), q(natPow_zero_natMod_one)⟩
      else -- a ^ 0 % m = 1
        have m'' : Q(Nat) := mkRawNatLit (m'.natLit! - 1)
haveI : m =Q Nat.succ (Nat.succ $m'') := ⟨⟩
        ⟨q(nat_lit 1), q(natPow_zero_natMod_succ_succ)⟩
  else if b.natLit! = 1 then -- a ^ 1 % m = a % m
    have c : Q(Nat) := mkRawNatLit (a.natLit! % m.natLit!)
haveI : b =Q 1 := ⟨⟩
haveI : c =Q Nat.mod a m := ⟨⟩
    ⟨c, q(natPow_one_natMod)⟩
  else
    have c₀ : Q(Nat) := mkRawNatLit (a.natLit! % m.natLit!)
haveI : c₀ =Q Nat.mod a m := ⟨⟩
    let ⟨c, p⟩ := go b.natLit!.log2 a m q(nat_lit 1) c₀ b _ .rfl
    ⟨c, q(($p).run)⟩
where
  /-- Invariants: `a ^ b₀ % m = c₀`, `depth > 0`, `b >>> depth = b₀` -/
  go (depth : Nat) (a m b₀ c₀ b : Q(Nat))
      (p : Q(Prop)) (hp : $p =Q (Nat.mod (Nat.pow $a $b₀) $m = $c₀)) :
      (c : Q(Nat)) × Q(IsNatPowModT $p $a $b $m $c) :=
    let b' := b.natLit!
    let m' := m.natLit!
    if depth <= 1 then
      let a' := a.natLit!
      let c₀' := c₀.natLit!
      if b' &&& 1 == 0 then
        have c : Q(Nat) := mkRawNatLit ((c₀' * c₀') % m')
haveI : c =Q Nat.mod (Nat.mul $c₀ $c₀) m := ⟨⟩
haveI : b =Q 2 * b₀ := ⟨⟩
        ⟨c, q(IsNatPowModT.bit0)⟩
      else
        have c : Q(Nat) := mkRawNatLit ((c₀' * ((c₀' * a') % m')) % m')
haveI : c =Q Nat.mod (Nat.mul $c₀ (Nat.mod (Nat.mul $c₀ $a) $m)) m := ⟨⟩
haveI : b =Q 2 * b₀ + 1 := ⟨⟩
        ⟨c, q(IsNatPowModT.bit1)⟩
    else
      let d := depth >>> 1
      have hi : Q(Nat) := mkRawNatLit (b' >>> d)
      let ⟨c1, p1⟩ := go (depth - d) a m b₀ c₀ hi p (by exact hp)
      let ⟨c2, p2⟩ := go d a m hi c1 b q(Nat.mod (Nat.pow $a $hi) $m = $c1) ⟨⟩
      ⟨c2, q(($p1).trans $p2)⟩
end NormNum
end Meta
end Mathlib
