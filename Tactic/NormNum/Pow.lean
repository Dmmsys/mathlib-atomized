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

variable {a b c : Nat}

/--
theorem `natPow_zero` / 定理 `natPow_zero`

English:
theorem natPow_zero
  statement: Nat.pow a (nat_lit 0) = nat_lit 1
  proof: rfl

中文:
定理 natPow_zero
  结论: 自然数.pow a (nat_lit 0) = nat_lit 1
  证明: rfl
-/
theorem natPow_zero : Nat.pow a (nat_lit 0) = nat_lit 1 := rfl
/--
theorem `natPow_one` / 定理 `natPow_one`

English:
theorem natPow_one
  statement: Nat.pow a (nat_lit 1) = a
  proof: Nat.pow_one _

中文:
定理 natPow_one
  结论: 自然数.pow a (nat_lit 1) = a
  证明: Nat.pow_one _

Depends on / 依赖: Nat.pow_one, pow_one
-/
theorem natPow_one : Nat.pow a (nat_lit 1) = a := Nat.pow_one _
/--
theorem `zero_natPow` / 定理 `zero_natPow`

English:
theorem zero_natPow
  statement: Nat.pow (nat_lit 0) (Nat.succ b) = nat_lit 0
  proof: rfl

中文:
定理 zero_natPow
  结论: 自然数.pow (nat_lit 0) (自然数.succ b) = nat_lit 0
  证明: rfl
-/
theorem zero_natPow : Nat.pow (nat_lit 0) (Nat.succ b) = nat_lit 0 := rfl
/--
theorem `one_natPow` / 定理 `one_natPow`

English:
theorem one_natPow
  statement: Nat.pow (nat_lit 1) b = nat_lit 1
  proof: Nat.one_pow _

中文:
定理 one_natPow
  结论: 自然数.pow (nat_lit 1) b = nat_lit 1
  证明: Nat.one_pow _

Depends on / 依赖: Nat.one_pow, one_pow
-/
theorem one_natPow : Nat.pow (nat_lit 1) b = nat_lit 1 := Nat.one_pow _

/--
Definition of `IsNatPowT` / `IsNatPowT` 的定义

English:
structure IsNatPowT
  parameters: (p : Prop) (a b c : Nat)
  axioms and operations (1):
    - run' : p -> Nat.pow a b = c

中文:
结构 是自然数PowT
  参数: (p : 命题) (a b c : 自然数)
  公理与运算 (1 个):
    - run' : p -> 自然数.pow a b = c

Depends on / 依赖: CompletelyNormalSpace, CompletelyNormalSpace.of_regularSpace_secondCountableTopology, of_regularSpace_secondCountableTopology
-/
structure IsNatPowT (p : Prop) (a b c : Nat) : Prop where
  /-- Unfolds the assertion. -/
  run' : p -> Nat.pow a b = c

/--
theorem `IsNatPowT.run` / 定理 `IsNatPowT.run`

English:
theorem IsNatPowT.run
  proof: p.run' (Nat.pow_one _)

中文:
定理 是自然数PowT.run
  证明: p.run' (Nat.pow_one _)

Depends on / 依赖: Nat.pow_one, p.run, pow_one
-/
theorem IsNatPowT.run
    (p : IsNatPowT (Nat.pow a (nat_lit 1) = a) a b c) : Nat.pow a b = c := p.run' (Nat.pow_one _)

/--
theorem `IsNatPowT.trans` / 定理 `IsNatPowT.trans`

English:
theorem IsNatPowT.trans
  statement: {p : Prop} {b' c' : Nat} (h1 : IsNatPowT p a b c)
  proof: ⟨h2.run' ∘ h1.run'⟩

中文:
定理 是自然数PowT.trans
  结论: {p : 命题} {b' c' : 自然数} (h1 : 是自然数PowT p a b c)
  证明: ⟨h2.run' ∘ h1.run'⟩

Depends on / 依赖: T4Space, T5Space, T5Space.toT4Space, h1.run, h2.run, toT4Space
-/
theorem IsNatPowT.trans {p : Prop} {b' c' : Nat} (h1 : IsNatPowT p a b c)
    (h2 : IsNatPowT (Nat.pow a b = c) a b' c') : IsNatPowT p a b' c' :=
  ⟨h2.run' ∘ h1.run'⟩

/--
theorem `IsNatPowT.bit0` / 定理 `IsNatPowT.bit0`

English:
theorem IsNatPowT.bit0
  statement: IsNatPowT (Nat.pow a b = c) a (nat_lit 2 * b) (Nat.mul c c)
  proof: ⟨fun h1 => by simp [two_mul, pow_add, ← h1]⟩

中文:
定理 是自然数PowT.bit0
  结论: 是自然数PowT (自然数.pow a b = c) a (nat_lit 2 * b) (自然数.mul c c)
  证明: ⟨fun h1 => by simp [two_mul, pow_add, ← h1]⟩

Depends on / 依赖: pow_add, two_mul
-/
theorem IsNatPowT.bit0 : IsNatPowT (Nat.pow a b = c) a (nat_lit 2 * b) (Nat.mul c c) :=
  ⟨fun h1 => by simp [two_mul, pow_add, ← h1]⟩

/--
theorem `IsNatPowT.bit1` / 定理 `IsNatPowT.bit1`

English:
theorem IsNatPowT.bit1
  proof: ⟨fun h1 => by simp [two_mul, pow_add, mul_assoc, ← h1]⟩

中文:
定理 是自然数PowT.bit1
  证明: ⟨fun h1 => by simp [two_mul, pow_add, mul_assoc, ← h1]⟩

Depends on / 依赖: mul_assoc, pow_add, two_mul
-/
theorem IsNatPowT.bit1 :
    IsNatPowT (Nat.pow a b = c) a (nat_lit 2 * b + nat_lit 1) (Nat.mul c (Nat.mul c a)) :=
  ⟨fun h1 => by simp [two_mul, pow_add, mul_assoc, ← h1]⟩

/--
Definition of `evalNatPow` / `evalNatPow` 的定义

English:
definition evalNatPow
  signature: (a b : Q(Nat))
  body: do
  if b.natLit! = 0 then
haveI : b =Q 0 := ⟨⟩
    return ⟨q(nat_lit 1), q(natPow_zero)⟩
  else if a.natLit! = 0 then
haveI : a =Q 0 := ⟨⟩
    have b' : Q(Nat) := mkRawNatLit (b.natLit! - 1)
haveI : b =Q Nat.succ b' := ⟨⟩
    return ⟨q(nat_lit 0), q(zero_natPow)⟩
  else if a.natLit! = 1 then
haveI 

中文:
定义 eval自然数Pow
  签名: (a b : Q(自然数))
  定义体: do
  if b.natLit! = 0 then
haveI : b =Q 0 := ⟨⟩
    return ⟨q(nat_lit 1), q(natPow_zero)⟩
  else if a.natLit! = 0 then
haveI : a =Q 0 := ⟨⟩
    have b' : Q(Nat) := mkRawNatLit (b.natLit! - 1)
haveI : b =Q Nat.succ b' := ⟨⟩
    return ⟨q(nat_lit 0), q(zero_natPow)⟩
  else if a.natLit! = 1 then
haveI 
-/
partial def evalNatPow (a b : Q(Nat)) : OptionT CoreM ((c : Q(Nat)) × Q(Nat.pow $a $b = $c)) := do
  if b.natLit! = 0 then
haveI : b =Q 0 := ⟨⟩
    return ⟨q(nat_lit 1), q(natPow_zero)⟩
  else if a.natLit! = 0 then
haveI : a =Q 0 := ⟨⟩
    have b' : Q(Nat) := mkRawNatLit (b.natLit! - 1)
haveI : b =Q Nat.succ b' := ⟨⟩
    return ⟨q(nat_lit 0), q(zero_natPow)⟩
  else if a.natLit! = 1 then
haveI : a =Q 1 := ⟨⟩
    return ⟨q(nat_lit 1), q(one_natPow)⟩
  else if b.natLit! = 1 then
haveI : b =Q 1 := ⟨⟩
    return ⟨a, q(natPow_one)⟩
  else
guard ← Lean.checkExponent b.natLit!
    let ⟨c, p⟩ := go b.natLit!.log2 a q(nat_lit 1) a b _ .rfl
    return ⟨c, q(($p).run)⟩
where
  /-- Invariants: `a ^ b₀ = c₀`, `depth > 0`, `b >>> depth = b₀`, `p := Nat.pow $a $b₀ = $c₀` -/
  go (depth : Nat) (a b₀ c₀ b : Q(Nat)) (p : Q(Prop)) (hp : $p =Q (Nat.pow $a $b₀ = $c₀)) :
      (c : Q(Nat)) × Q(IsNatPowT $p $a $b $c) :=
    let b' := b.natLit!
    if depth <= 1 then
      let a' := a.natLit!
      let c₀' := c₀.natLit!
      if b' &&& 1 == 0 then
        have c : Q(Nat) := mkRawNatLit (c₀' * c₀')
haveI : c =Q Nat.mul c₀ c₀ := ⟨⟩
haveI : b =Q 2 * b₀ := ⟨⟩
        ⟨c, q(IsNatPowT.bit0)⟩
      else
        have c : Q(Nat) := mkRawNatLit (c₀' * (c₀' * a'))
haveI : c =Q Nat.mul c₀ (Nat.mul $c₀ $a) := ⟨⟩
haveI : b =Q 2 * b₀ + 1 := ⟨⟩
        ⟨c, q(IsNatPowT.bit1)⟩
    else
      let d := depth >>> 1
      have hi : Q(Nat) := mkRawNatLit (b' >>> d)
      let ⟨c1, p1⟩ := go (depth - d) a b₀ c₀ hi p (by exact hp)
      let ⟨c2, p2⟩ := go d a hi c1 b q(Nat.pow $a $hi = $c1) ⟨⟩
      ⟨c2, q(($p1).trans $p2)⟩

/--
theorem `intPow_ofNat` / 定理 `intPow_ofNat`

English:
theorem intPow_ofNat
  given: (h1 : Nat.pow a b = c)
  proof: by simp [← h1]

中文:
定理 intPow_of自然数
  条件: (h1 : 自然数.pow a b = c)
  证明: by simp [← h1]
-/
theorem intPow_ofNat (h1 : Nat.pow a b = c) :
    Int.pow (Int.ofNat a) b = Int.ofNat c := by simp [← h1]

/--
theorem `intPow_negOfNat_bit0` / 定理 `intPow_negOfNat_bit0`

English:
theorem intPow_negOfNat_bit0
  statement: {b' c' : Nat} (h1 : Nat.pow a b' = c')
  proof: by
  rw [← hb]; rw [Int.negOfNat_eq]; rw [Int.pow_eq]; rw [pow_mul]; rw [neg_pow_two]; rw [← pow_mul]; rw [two_mul]; rw [pow_add]; rw [← hc]; rw [← h1]
  simp

中文:
定理 intPow_negOf自然数_bit0
  结论: {b' c' : 自然数} (h1 : 自然数.pow a b' = c')
  证明: by
  rw [← hb]; rw [Int.negOfNat_eq]; rw [Int.pow_eq]; rw [pow_mul]; rw [neg_pow_two]; rw [← pow_mul]; rw [two_mul]; rw [pow_add]; rw [← hc]; rw [← h1]
  simp

Depends on / 依赖: Int.negOfNat_eq, Int.pow_eq, negOfNat_eq, neg_pow_two, pow_add, pow_eq, pow_mul, two_mul
-/
theorem intPow_negOfNat_bit0 {b' c' : Nat} (h1 : Nat.pow a b' = c')
    (hb : nat_lit 2 * b' = b) (hc : c' * c' = c) :
    Int.pow (Int.negOfNat a) b = Int.ofNat c := by
  rw [← hb]; rw [Int.negOfNat_eq]; rw [Int.pow_eq]; rw [pow_mul]; rw [neg_pow_two]; rw [← pow_mul]; rw [two_mul]; rw [pow_add]; rw [← hc]; rw [← h1]
  simp

/--
theorem `intPow_negOfNat_bit1` / 定理 `intPow_negOfNat_bit1`

English:
theorem intPow_negOfNat_bit1
  statement: {b' c' : Nat} (h1 : Nat.pow a b' = c')
  proof: by
  rw [← hb]; rw [Int.negOfNat_eq]; rw [Int.negOfNat_eq]; rw [Int.pow_eq]; rw [pow_succ]; rw [pow_mul]; rw [neg_pow_two]; rw [← pow_mul]; rw [two_mul]; rw [pow_add]; rw [← hc]; rw [← h1]
  simp [mul_comm, mul_left_comm]

中文:
定理 intPow_negOf自然数_bit1
  结论: {b' c' : 自然数} (h1 : 自然数.pow a b' = c')
  证明: by
  rw [← hb]; rw [Int.negOfNat_eq]; rw [Int.negOfNat_eq]; rw [Int.pow_eq]; rw [pow_succ]; rw [pow_mul]; rw [neg_pow_two]; rw [← pow_mul]; rw [two_mul]; rw [pow_add]; rw [← hc]; rw [← h1]
  simp [mul_comm, mul_left_comm]

Depends on / 依赖: Int.negOfNat_eq, Int.pow_eq, mul_comm, mul_left_comm, negOfNat_eq, neg_pow_two, pow_add, pow_eq, pow_mul, pow_succ, two_mul
-/
theorem intPow_negOfNat_bit1 {b' c' : Nat} (h1 : Nat.pow a b' = c')
    (hb : nat_lit 2 * b' + nat_lit 1 = b) (hc : c' * (c' * a) = c) :
    Int.pow (Int.negOfNat a) b = Int.negOfNat c := by
  rw [← hb]; rw [Int.negOfNat_eq]; rw [Int.negOfNat_eq]; rw [Int.pow_eq]; rw [pow_succ]; rw [pow_mul]; rw [neg_pow_two]; rw [← pow_mul]; rw [two_mul]; rw [pow_add]; rw [← hc]; rw [← h1]
  simp [mul_comm, mul_left_comm]

/--
Definition of `evalIntPow` / `evalIntPow` 的定义

English:
definition evalIntPow
  signature: (za : Int) (a : Q(Int)) (b : Q(Nat))
  body: do
  have a' : Q(Nat) := a.appArg!
  if 0 <= za then
have : a =Q .ofNat a' := ⟨⟩
    let ⟨c, p⟩ ← evalNatPow a' b
    return ⟨c.natLit!, q(.ofNat $c), q(intPow_ofNat $p)⟩
  else
have : a =Q .negOfNat a' := ⟨⟩
    let b' := b.natLit!
    have b₀ : Q(Nat) := mkRawNatLit (b' >>> 1)
    let ⟨c₀, p⟩ ← ev

中文:
定义 eval整数Pow
  签名: (za : 整数) (a : Q(整数)) (b : Q(自然数))
  定义体: do
  have a' : Q(Nat) := a.appArg!
  if 0 <= za then
have : a =Q .ofNat a' := ⟨⟩
    let ⟨c, p⟩ ← evalNatPow a' b
    return ⟨c.natLit!, q(.ofNat $c), q(intPow_ofNat $p)⟩
  else
have : a =Q .negOfNat a' := ⟨⟩
    let b' := b.natLit!
    have b₀ : Q(Nat) := mkRawNatLit (b' >>> 1)
    let ⟨c₀, p⟩ ← ev
-/
partial def evalIntPow (za : Int) (a : Q(Int)) (b : Q(Nat)) :
    OptionT CoreM (Int × (c : Q(Int)) × Q(Int.pow $a $b = $c)) := do
  have a' : Q(Nat) := a.appArg!
  if 0 <= za then
have : a =Q .ofNat a' := ⟨⟩
    let ⟨c, p⟩ ← evalNatPow a' b
    return ⟨c.natLit!, q(.ofNat $c), q(intPow_ofNat $p)⟩
  else
have : a =Q .negOfNat a' := ⟨⟩
    let b' := b.natLit!
    have b₀ : Q(Nat) := mkRawNatLit (b' >>> 1)
    let ⟨c₀, p⟩ ← evalNatPow a' b₀
    let c' := c₀.natLit!
    if b' &&& 1 == 0 then
      have c : Q(Nat) := mkRawNatLit (c' * c')
      have pc : Q($c₀ * $c₀ = $c) := (q(Eq.refl $c) : Expr)
      have pb : Q(2 * $b₀ = $b) := (q(Eq.refl $b) : Expr)
      return ⟨c.natLit!, q(.ofNat $c), q(intPow_negOfNat_bit0 $p $pb $pc)⟩
    else
      have c : Q(Nat) := mkRawNatLit (c' * (c' * a'.natLit!))
      have pc : Q($c₀ * ($c₀ * $a') = $c) := (q(Eq.refl $c) : Expr)
      have pb : Q(2 * $b₀ + 1 = $b) := (q(Eq.refl $b) : Expr)
      return ⟨-c.natLit!, q(.negOfNat $c), q(intPow_negOfNat_bit1 $p $pb $pc)⟩

-- see note [norm_num lemma function equality]
/--
theorem `isNat_pow` / 定理 `isNat_pow`

English:
theorem isNat_pow
  given: {α} [Semiring α]
  statement: forall {f : α -> Nat -> α} {a : α} {b a' b' c : Nat},

中文:
定理 is自然数_pow
  条件: {α} [半环 α]
  结论: 对任意 {f : α -> 自然数 -> α} {a : α} {b a' b' c : 自然数},
-/
theorem isNat_pow {α} [Semiring α] : forall {f : α -> Nat -> α} {a : α} {b a' b' c : Nat},
    f = HPow.hPow -> IsNat a a' -> IsNat b b' -> Nat.pow a' b' = c -> IsNat (f a b) c
  | _, _, _, _, _, _, rfl, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨by simp⟩

-- see note [norm_num lemma function equality]
/--
theorem `isInt_pow` / 定理 `isInt_pow`

English:
theorem isInt_pow
  given: {α} [Ring α]
  statement: forall {f : α -> Nat -> α} {a : α} {b : Nat} {a' : Int} {b' : Nat} {c : Int},

中文:
定理 is整数_pow
  条件: {α} [环 α]
  结论: 对任意 {f : α -> 自然数 -> α} {a : α} {b : 自然数} {a' : 整数} {b' : 自然数} {c : 整数},
-/
theorem isInt_pow {α} [Ring α] : forall {f : α -> Nat -> α} {a : α} {b : Nat} {a' : Int} {b' : Nat} {c : Int},
    f = HPow.hPow -> IsInt a a' -> IsNat b b' -> Int.pow a' b' = c -> IsInt (f a b) c
  | _, _, _, _, _, _, rfl, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨by simp⟩

-- see note [norm_num lemma function equality]
/--
theorem `isRat_pow` / 定理 `isRat_pow`

English:
theorem isRat_pow
  given: {α} [Ring α] {f : α -> Nat -> α} {a : α} {an cn : Int} {ad b b' cd : Nat}
  proof: by
  rintro rfl ⟨_, rfl⟩ ⟨rfl⟩ (rfl : an ^ b = _) (rfl : ad ^ b = _)
  have := invertiblePow (ad:α) b
  rw [← Nat.cast_pow] at this
  use this; simp [invOf_pow, Commute.mul_pow]

中文:
定理 isRat_pow
  条件: {α} [环 α] {f : α -> 自然数 -> α} {a : α} {an cn : 整数} {ad b b' cd : 自然数}
  证明: by
  rintro rfl ⟨_, rfl⟩ ⟨rfl⟩ (rfl : an ^ b = _) (rfl : ad ^ b = _)
  have := invertiblePow (ad:α) b
  rw [← Nat.cast_pow] at this
  use this; simp [invOf_pow, Commute.mul_pow]

Depends on / 依赖: Commute, Commute.mul_pow, Nat.cast_pow, cast_pow, invOf_pow, invertiblePow, mul_pow
-/
theorem isRat_pow {α} [Ring α] {f : α -> Nat -> α} {a : α} {an cn : Int} {ad b b' cd : Nat} :
    f = HPow.hPow -> IsRat a an ad -> IsNat b b' ->
    Int.pow an b' = cn -> Nat.pow ad b' = cd ->
    IsRat (f a b) cn cd := by
  rintro rfl ⟨_, rfl⟩ ⟨rfl⟩ (rfl : an ^ b = _) (rfl : ad ^ b = _)
  have := invertiblePow (ad:α) b
  rw [← Nat.cast_pow] at this
  use this; simp [invOf_pow, Commute.mul_pow]

/--
theorem `isNNRat_pow` / 定理 `isNNRat_pow`

English:
theorem isNNRat_pow
  given: {α} [Semiring α] {f : α -> Nat -> α} {a : α} {an cn : Nat} {ad b b' cd : Nat}
  proof: by
  rintro rfl ⟨_, rfl⟩ ⟨rfl⟩ (rfl : an ^ b = _) (rfl : ad ^ b = _)
  have := invertiblePow (ad:α) b
  rw [← Nat.cast_pow] at this
  use this; simp [invOf_pow, Commute.mul_pow, Nat.cast_commute]

中文:
定理 isNNRat_pow
  条件: {α} [半环 α] {f : α -> 自然数 -> α} {a : α} {an cn : 自然数} {ad b b' cd : 自然数}
  证明: by
  rintro rfl ⟨_, rfl⟩ ⟨rfl⟩ (rfl : an ^ b = _) (rfl : ad ^ b = _)
  have := invertiblePow (ad:α) b
  rw [← Nat.cast_pow] at this
  use this; simp [invOf_pow, Commute.mul_pow, Nat.cast_commute]

Depends on / 依赖: Commute, Commute.mul_pow, Nat.cast_commute, Nat.cast_pow, cast_commute, cast_pow, invOf_pow, invertiblePow, mul_pow
-/
theorem isNNRat_pow {α} [Semiring α] {f : α -> Nat -> α} {a : α} {an cn : Nat} {ad b b' cd : Nat} :
    f = HPow.hPow -> IsNNRat a an ad -> IsNat b b' ->
    Nat.pow an b' = cn -> Nat.pow ad b' = cd ->
    IsNNRat (f a b) cn cd := by
  rintro rfl ⟨_, rfl⟩ ⟨rfl⟩ (rfl : an ^ b = _) (rfl : ad ^ b = _)
  have := invertiblePow (ad:α) b
  rw [← Nat.cast_pow] at this
  use this; simp [invOf_pow, Commute.mul_pow, Nat.cast_commute]

/--
Definition of `evalPow.core` / `evalPow.core` 的定义

English:
definition evalPow.core
  signature: {u : Level} {α : Q(Type u)} (e : Q(«$α»)) (f : Q(«$α» -> Nat -> «$α»)) (a : Q(«$α»))
  body: do
haveI' : e =Q a ^ b := ⟨⟩
haveI' : f =Q HPow.hPow := ⟨⟩
  match ra with
  | .isBool .. => failure
  | .isNat sα na pa =>
    assumeInstancesCommute
    let ⟨c, r⟩ ← evalNatPow na nb
    return .isNat sα c q(isNat_pow (f := $f) (.refl $f) $pa $pb $r)
  | .isNegNat rα .. =>
    assumeInstancesCommu

中文:
定义 evalPow.core
  签名: {u : Level} {α : Q(类型u)} (e : Q(«$α»)) (f : Q(«$α» -> 自然数 -> «$α»)) (a : Q(«$α»))
  定义体: do
haveI' : e =Q a ^ b := ⟨⟩
haveI' : f =Q HPow.hPow := ⟨⟩
  match ra with
  | .isBool .. => failure
  | .isNat sα na pa =>
    assumeInstancesCommute
    let ⟨c, r⟩ ← evalNatPow na nb
    return .isNat sα c q(isNat_pow (f := $f) (.refl $f) $pa $pb $r)
  | .isNegNat rα .. =>
    assumeInstancesCommu
-/
def evalPow.core {u : Level} {α : Q(Type u)} (e : Q(«$α»)) (f : Q(«$α» -> Nat -> «$α»)) (a : Q(«$α»))
    (b nb : Q(Nat)) (pb : Q(IsNat «$b» «$nb»)) (sα : Q(Semiring «$α»)) (ra : Result a) :
    OptionT CoreM (Result e) := do
haveI' : e =Q a ^ b := ⟨⟩
haveI' : f =Q HPow.hPow := ⟨⟩
  match ra with
  | .isBool .. => failure
  | .isNat sα na pa =>
    assumeInstancesCommute
    let ⟨c, r⟩ ← evalNatPow na nb
    return .isNat sα c q(isNat_pow (f := $f) (.refl $f) $pa $pb $r)
  | .isNegNat rα .. =>
    assumeInstancesCommute
let ⟨za, na, pa⟩ ← OptionT.mk pure (ra.toInt rα)
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
@[norm_num _ ^ (_ : Nat)]
/--
Definition of `evalPow` / `evalPow` 的定义

English:
definition evalPow
  signature: : NormNumExt where eval {u α} e
  body: do
  let .app (.app (f : Q($α -> Nat -> $α)) (a : Q($α))) (b : Q(Nat)) ← whnfR e | failure
  let ⟨nb, pb⟩ ← deriveNat b q(Nat.instAddMonoidWithOne)
  let sα ← inferSemiring α
  let ra ← derive a
guard ← withDefault withNewMCtxDepth isDefEq f q(HPow.hPow (α := $α))
haveI' : e =Q a ^ b := ⟨⟩
haveI' : 

中文:
定义 evalPow
  签名: : NormNumExt where eval {u α} e
  定义体: do
  let .app (.app (f : Q($α -> Nat -> $α)) (a : Q($α))) (b : Q(Nat)) ← whnfR e | failure
  let ⟨nb, pb⟩ ← deriveNat b q(Nat.instAddMonoidWithOne)
  let sα ← inferSemiring α
  let ra ← derive a
guard ← withDefault withNewMCtxDepth isDefEq f q(HPow.hPow (α := $α))
haveI' : e =Q a ^ b := ⟨⟩
haveI' : 
-/
def evalPow : NormNumExt where eval {u α} e := do
  let .app (.app (f : Q($α -> Nat -> $α)) (a : Q($α))) (b : Q(Nat)) ← whnfR e | failure
  let ⟨nb, pb⟩ ← deriveNat b q(Nat.instAddMonoidWithOne)
  let sα ← inferSemiring α
  let ra ← derive a
guard ← withDefault withNewMCtxDepth isDefEq f q(HPow.hPow (α := $α))
haveI' : e =Q a ^ b := ⟨⟩
haveI' : f =Q HPow.hPow := ⟨⟩
  let .some r ←
liftM OptionT.run (evalPow.core q($e) q($f) q($a) q($b) q($nb) q($pb) q($sα) ra) | failure
  return r

/--
theorem `isNat_zpow_pos` / 定理 `isNat_zpow_pos`

English:
theorem isNat_zpow_pos
  statement: {α : Type*} [DivisionSemiring α] {a : α} {b : Int} {nb ne : Nat}
  proof: by
  rwa [pb.out, zpow_natCast]

中文:
定理 is自然数_zpow_pos
  结论: {α : 类型} [除半环 α] {a : α} {b : 整数} {nb ne : 自然数}
  证明: by
  rwa [pb.out, zpow_natCast]

Depends on / 依赖: pb.out, zpow_natCast
-/
theorem isNat_zpow_pos {α : Type*} [DivisionSemiring α] {a : α} {b : Int} {nb ne : Nat}
    (pb : IsNat b nb) (pe' : IsNat (a ^ nb) ne) :
    IsNat (a ^ b) ne := by
  rwa [pb.out, zpow_natCast]

/--
theorem `isNat_zpow_neg` / 定理 `isNat_zpow_neg`

English:
theorem isNat_zpow_neg
  statement: {α : Type*} [DivisionSemiring α] {a : α} {b : Int} {nb ne : Nat}
  proof: by
  rwa [pb.out, Int.cast_negOfNat, zpow_neg, zpow_natCast]

中文:
定理 is自然数_zpow_neg
  结论: {α : 类型} [除半环 α] {a : α} {b : 整数} {nb ne : 自然数}
  证明: by
  rwa [pb.out, Int.cast_negOfNat, zpow_neg, zpow_natCast]

Depends on / 依赖: Int.cast_negOfNat, cast_negOfNat, pb.out, zpow_natCast, zpow_neg
-/
theorem isNat_zpow_neg {α : Type*} [DivisionSemiring α] {a : α} {b : Int} {nb ne : Nat}
    (pb : IsInt b (Int.negOfNat nb)) (pe' : IsNat (a ^ nb)⁻¹ ne) :
    IsNat (a ^ b) ne := by
  rwa [pb.out, Int.cast_negOfNat, zpow_neg, zpow_natCast]

/--
theorem `isInt_zpow_pos` / 定理 `isInt_zpow_pos`

English:
theorem isInt_zpow_pos
  statement: {α : Type*} [DivisionRing α] {a : α} {b : Int} {nb ne : Nat}
  proof: by
  rwa [pb.out, zpow_natCast]

中文:
定理 is整数_zpow_pos
  结论: {α : 类型} [除环 α] {a : α} {b : 整数} {nb ne : 自然数}
  证明: by
  rwa [pb.out, zpow_natCast]

Depends on / 依赖: pb.out, zpow_natCast
-/
theorem isInt_zpow_pos {α : Type*} [DivisionRing α] {a : α} {b : Int} {nb ne : Nat}
    (pb : IsNat b nb) (pe' : IsInt (a ^ nb) (Int.negOfNat ne)) :
    IsInt (a ^ b) (Int.negOfNat ne) := by
  rwa [pb.out, zpow_natCast]

/--
theorem `isInt_zpow_neg` / 定理 `isInt_zpow_neg`

English:
theorem isInt_zpow_neg
  statement: {α : Type*} [DivisionRing α] {a : α} {b : Int} {nb ne : Nat}
  proof: by
  rwa [pb.out, Int.cast_negOfNat, zpow_neg, zpow_natCast]

中文:
定理 is整数_zpow_neg
  结论: {α : 类型} [除环 α] {a : α} {b : 整数} {nb ne : 自然数}
  证明: by
  rwa [pb.out, Int.cast_negOfNat, zpow_neg, zpow_natCast]

Depends on / 依赖: Int.cast_negOfNat, cast_negOfNat, pb.out, zpow_natCast, zpow_neg
-/
theorem isInt_zpow_neg {α : Type*} [DivisionRing α] {a : α} {b : Int} {nb ne : Nat}
    (pb : IsInt b (Int.negOfNat nb)) (pe' : IsInt (a ^ nb)⁻¹ (Int.negOfNat ne)) :
    IsInt (a ^ b) (Int.negOfNat ne) := by
  rwa [pb.out, Int.cast_negOfNat, zpow_neg, zpow_natCast]

/--
theorem `isNNRat_zpow_pos` / 定理 `isNNRat_zpow_pos`

English:
theorem isNNRat_zpow_pos
  statement: {α : Type*} [DivisionSemiring α] {a : α} {b : Int} {nb : Nat}
  proof: by
  rwa [pb.out, zpow_natCast]

中文:
定理 isNNRat_zpow_pos
  结论: {α : 类型} [除半环 α] {a : α} {b : 整数} {nb : 自然数}
  证明: by
  rwa [pb.out, zpow_natCast]

Depends on / 依赖: pb.out, zpow_natCast
-/
theorem isNNRat_zpow_pos {α : Type*} [DivisionSemiring α] {a : α} {b : Int} {nb : Nat}
    {num : Nat} {den : Nat}
    (pb : IsNat b nb) (pe' : IsNNRat (a ^ nb) num den) :
    IsNNRat (a^b) num den := by
  rwa [pb.out, zpow_natCast]

/--
theorem `isNNRat_zpow_neg` / 定理 `isNNRat_zpow_neg`

English:
theorem isNNRat_zpow_neg
  statement: {α : Type*} [DivisionSemiring α] {a : α} {b : Int} {nb : Nat}
  proof: by
  rwa [pb.out, Int.cast_negOfNat, zpow_neg, zpow_natCast]

中文:
定理 isNNRat_zpow_neg
  结论: {α : 类型} [除半环 α] {a : α} {b : 整数} {nb : 自然数}
  证明: by
  rwa [pb.out, Int.cast_negOfNat, zpow_neg, zpow_natCast]

Depends on / 依赖: Int.cast_negOfNat, cast_negOfNat, pb.out, zpow_natCast, zpow_neg
-/
theorem isNNRat_zpow_neg {α : Type*} [DivisionSemiring α] {a : α} {b : Int} {nb : Nat}
    {num : Nat} {den : Nat}
    (pb : IsInt b (Int.negOfNat nb)) (pe' : IsNNRat ((a ^ nb)⁻¹) num den) :
    IsNNRat (a^b) num den := by
  rwa [pb.out, Int.cast_negOfNat, zpow_neg, zpow_natCast]

/--
theorem `isRat_zpow_pos` / 定理 `isRat_zpow_pos`

English:
theorem isRat_zpow_pos
  statement: {α : Type*} [DivisionRing α] {a : α} {b : Int} {nb : Nat}
  proof: by
  rwa [pb.out, zpow_natCast]

中文:
定理 isRat_zpow_pos
  结论: {α : 类型} [除环 α] {a : α} {b : 整数} {nb : 自然数}
  证明: by
  rwa [pb.out, zpow_natCast]

Depends on / 依赖: pb.out, zpow_natCast
-/
theorem isRat_zpow_pos {α : Type*} [DivisionRing α] {a : α} {b : Int} {nb : Nat}
    {num : Int} {den : Nat}
    (pb : IsNat b nb) (pe' : IsRat (a ^ nb) num den) :
    IsRat (a ^ b) num den := by
  rwa [pb.out, zpow_natCast]

/--
theorem `isRat_zpow_neg` / 定理 `isRat_zpow_neg`

English:
theorem isRat_zpow_neg
  statement: {α : Type*} [DivisionRing α] {a : α} {b : Int} {nb : Nat}
  proof: by
  rwa [pb.out, Int.cast_negOfNat, zpow_neg, zpow_natCast]

#adaptation_note /-- https://github.com/leanprover/lean4/pull/4096
the two
```
have h : $e =Q (HPow.hPow (γ := $α) $a $b) := ⟨⟩
h.check
```
blocks below were not necessary: we just did it once outside the `match rb with` block.
-/

中文:
定理 isRat_zpow_neg
  结论: {α : 类型} [除环 α] {a : α} {b : 整数} {nb : 自然数}
  证明: by
  rwa [pb.out, Int.cast_negOfNat, zpow_neg, zpow_natCast]

#adaptation_note /-- https://github.com/leanprover/lean4/pull/4096
the two
```
have h : $e =Q (HPow.hPow (γ := $α) $a $b) := ⟨⟩
h.check
```
blocks below were not necessary: we just did it once outside the `match rb with` block.
-/

Depends on / 依赖: Int.cast_negOfNat, cast_negOfNat, pb.out, zpow_natCast, zpow_neg
-/
theorem isRat_zpow_neg {α : Type*} [DivisionRing α] {a : α} {b : Int} {nb : Nat}
    {num : Int} {den : Nat}
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
@[norm_num _ ^ (_ : Int)]
/--
Definition of `evalZPow` / `evalZPow` 的定义

English:
definition evalZPow
  signature: : NormNumExt where eval {u α} e
  body: do
  let .app (.app (f : Q($α -> Int -> $α)) (a : Q($α))) (b : Q(Int)) ← whnfR e | failure
  let _c ← synthInstanceQ q(DivisionSemiring $α)
  let rb ← derive (α := q(Int)) b
  match rb with
  | .isBool .. | .isNNRat _ .. | .isNegNNRat _ .. => failure
  | .isNat sβ nb pb =>
have h : e =Q (HPow.hPow (

中文:
定义 evalZPow
  签名: : NormNumExt where eval {u α} e
  定义体: do
  let .app (.app (f : Q($α -> Int -> $α)) (a : Q($α))) (b : Q(Int)) ← whnfR e | failure
  let _c ← synthInstanceQ q(DivisionSemiring $α)
  let rb ← derive (α := q(Int)) b
  match rb with
  | .isBool .. | .isNNRat _ .. | .isNegNNRat _ .. => failure
  | .isNat sβ nb pb =>
have h : e =Q (HPow.hPow (
-/
def evalZPow : NormNumExt where eval {u α} e := do
  let .app (.app (f : Q($α -> Int -> $α)) (a : Q($α))) (b : Q(Int)) ← whnfR e | failure
  let _c ← synthInstanceQ q(DivisionSemiring $α)
  let rb ← derive (α := q(Int)) b
  match rb with
  | .isBool .. | .isNNRat _ .. | .isNegNNRat _ .. => failure
  | .isNat sβ nb pb =>
have h : e =Q (HPow.hPow (γ := $α) $a $b) := ⟨⟩
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
have h : e =Q (HPow.hPow (γ := $α) $a $b) := ⟨⟩
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
