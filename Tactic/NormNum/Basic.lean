/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Thomas Murrills
-/
module

public import Mathlib.Algebra.Group.Invertible.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Commute
public import Mathlib.Tactic.HaveI
public import Mathlib.Tactic.NormNum.Core

/-!
# `norm_num` basic plugins

This file adds `norm_num` plugins for
* constructors and constants
* `Nat.cast`, `Int.cast`, and `mkRat`
* `+`, `-`, `*`, and `/`
* `Nat.succ`, `Nat.sub`, `Nat.mod`, and `Nat.div`.

See other files in this directory for many more plugins.
-/

public section

universe u

namespace Mathlib.Meta.NormNum

/-- If `b` divides `a` and `a` is invertible, then `b` is invertible. -/
@[instance_reducible]
/--
Definition of `invertibleOfMul` / `invertibleOfMul` 的定义

English:
definition invertibleOfMul
  signature: {α} [Semiring α] (k : Nat) (b : α)

中文:
定义 invertibleOfMul
  签名: {α} [Semiring α] (k : 自然数) (b : α)
-/
def invertibleOfMul {α} [Semiring α] (k : Nat) (b : α) :
    forall (a : α) [Invertible a], a = k * b -> Invertible b
  | _, ⟨c, hc1, hc2⟩, rfl => by
    rw [← mul_assoc] at hc1
    rw [Nat.cast_commute k]; rw [mul_assoc]; rw [Nat.cast_commute k] at hc2
    exact ⟨_, hc1, hc2⟩

/-- If `b` divides `a` and `a` is invertible, then `b` is invertible. -/
@[instance_reducible]
/--
Definition of `invertibleOfMul'` / `invertibleOfMul'` 的定义

English:
definition invertibleOfMul'
  signature: {α} [Semiring α] {a k b : Nat} [Invertible (a : α)]
  body: invertibleOfMul k (b:α) ↑a (by simp [h])

中文:
定义 invertibleOfMul'
  签名: {α} [Semiring α] {a k b : 自然数} [Invertible (a : α)]
  定义体: invertibleOfMul k (b:α) ↑a (by simp [h])

Depends on / 依赖: invertibleOfMul
-/
def invertibleOfMul' {α} [Semiring α] {a k b : Nat} [Invertible (a : α)]
    (h : a = k * b) : Invertible (b : α) := invertibleOfMul k (b:α) ↑a (by simp [h])

/--
theorem `IsInt.raw_refl` / 定理 `IsInt.raw_refl`

English:
theorem IsInt.raw_refl
  given: (n : Int)
  statement: IsInt n n
  proof: ⟨rfl⟩

meta section

中文:
定理 IsInt.raw_refl
  条件: (n : 整数)
  结论: Is整数 n n
  证明: ⟨rfl⟩

meta section
-/
theorem IsInt.raw_refl (n : Int) : IsInt n n := ⟨rfl⟩

meta section

open Lean Meta Qq


/--
theorem `isNat_zero` / 定理 `isNat_zero`

English:
theorem isNat_zero
  given: (α) [AddMonoidWithOne α]
  statement: IsNat (Zero.zero : α) (nat_lit 0)
  proof: ⟨Nat.cast_zero.symm⟩

中文:
定理 isNat_zero
  条件: (α) [AddMonoidWithOne α]
  结论: Is自然数 (Zero.zero : α) (nat_lit 0)
  证明: ⟨Nat.cast_zero.symm⟩

Depends on / 依赖: Nat.cast_zero.symm, cast_zero
-/
theorem isNat_zero (α) [AddMonoidWithOne α] : IsNat (Zero.zero : α) (nat_lit 0) :=
  ⟨Nat.cast_zero.symm⟩

/--
Definition of `evalZero` / `evalZero` 的定义

English:
definition evalZero
  signature: : NormNumExt where eval {u α} e
  body: do
  let sα ← inferAddMonoidWithOne α
  match e with
  | ~q(Zero.zero) => return .isNat sα q(nat_lit 0) q(isNat_zero $α)

中文:
定义 evalZero
  签名: : NormNumExt where eval {u α} e
  定义体: do
  let sα ← inferAddMonoidWithOne α
  match e with
  | ~q(Zero.zero) => return .isNat sα q(nat_lit 0) q(isNat_zero $α)
-/
@[norm_num Zero.zero] def evalZero : NormNumExt where eval {u α} e := do
  let sα ← inferAddMonoidWithOne α
  match e with
  | ~q(Zero.zero) => return .isNat sα q(nat_lit 0) q(isNat_zero $α)

/--
theorem `isNat_one` / 定理 `isNat_one`

English:
theorem isNat_one
  given: (α) [AddMonoidWithOne α]
  statement: IsNat (One.one : α) (nat_lit 1)
  proof: ⟨Nat.cast_one.symm⟩

中文:
定理 isNat_one
  条件: (α) [AddMonoidWithOne α]
  结论: Is自然数 (One.one : α) (nat_lit 1)
  证明: ⟨Nat.cast_one.symm⟩

Depends on / 依赖: Nat.cast_one.symm, cast_one
-/
theorem isNat_one (α) [AddMonoidWithOne α] : IsNat (One.one : α) (nat_lit 1) := ⟨Nat.cast_one.symm⟩

/--
Definition of `evalOne` / `evalOne` 的定义

English:
definition evalOne
  signature: : NormNumExt where eval {u α} e
  body: do
  let sα ← inferAddMonoidWithOne α
  match e with
  | ~q(One.one) => return .isNat sα q(nat_lit 1) q(isNat_one $α)

中文:
定义 evalOne
  签名: : NormNumExt where eval {u α} e
  定义体: do
  let sα ← inferAddMonoidWithOne α
  match e with
  | ~q(One.one) => return .isNat sα q(nat_lit 1) q(isNat_one $α)
-/
@[norm_num One.one] def evalOne : NormNumExt where eval {u α} e := do
  let sα ← inferAddMonoidWithOne α
  match e with
  | ~q(One.one) => return .isNat sα q(nat_lit 1) q(isNat_one $α)

/--
theorem `isNat_ofNat` / 定理 `isNat_ofNat`

English:
theorem isNat_ofNat
  statement: (α : Type u) [AddMonoidWithOne α] {a : α} {n : Nat}
  proof: ⟨h.symm⟩

中文:
定理 isNat_ofNat
  结论: (α : 类型u) [AddMonoidWithOne α] {a : α} {n : 自然数}
  证明: ⟨h.symm⟩

Depends on / 依赖: h.symm
-/
theorem isNat_ofNat (α : Type u) [AddMonoidWithOne α] {a : α} {n : Nat}
    (h : n = a) : IsNat a n := ⟨h.symm⟩

/--
Definition of `evalOfNat` / `evalOfNat` 的定义

English:
definition evalOfNat
  signature: : NormNumExt where eval {u α} e
  body: do
  let sα ← inferAddMonoidWithOne α
  match e with
  | ~q(@OfNat.ofNat _ $n $oα) =>
    let n : Q(Nat) ← whnf n
    guard n.isRawNatLit
    let ⟨a, (pa : Q($n = $e))⟩ ← mkOfNat α sα n
guard ← isDefEq a e
    return .isNat sα n q(isNat_ofNat $α $pa)

中文:
定义 evalOfNat
  签名: : NormNumExt where eval {u α} e
  定义体: do
  let sα ← inferAddMonoidWithOne α
  match e with
  | ~q(@OfNat.ofNat _ $n $oα) =>
    let n : Q(Nat) ← whnf n
    guard n.isRawNatLit
    let ⟨a, (pa : Q($n = $e))⟩ ← mkOfNat α sα n
guard ← isDefEq a e
    return .isNat sα n q(isNat_ofNat $α $pa)

Depends on / 依赖: R0Space, T1Space
-/
@[norm_num OfNat.ofNat _] def evalOfNat : NormNumExt where eval {u α} e := do
  let sα ← inferAddMonoidWithOne α
  match e with
  | ~q(@OfNat.ofNat _ $n $oα) =>
    let n : Q(Nat) ← whnf n
    guard n.isRawNatLit
    let ⟨a, (pa : Q($n = $e))⟩ ← mkOfNat α sα n
guard ← isDefEq a e
    return .isNat sα n q(isNat_ofNat $α $pa)

/--
theorem `isNat_intOfNat` / 定理 `isNat_intOfNat`

English:
theorem isNat_intOfNat
  statement: {n n' : Nat} -> IsNat n n' -> IsNat (Int.ofNat n) n'

中文:
定理 isNat_intOfNat
  结论: {n n' : 自然数} -> Is自然数 n n' -> Is自然数 (整数.of自然数 n) n'

Depends on / 依赖: R0Space, T0Space, T1Space
-/
theorem isNat_intOfNat : {n n' : Nat} -> IsNat n n' -> IsNat (Int.ofNat n) n'
  | _, _, ⟨rfl⟩ => ⟨rfl⟩

/--
Definition of `evalIntOfNat` / `evalIntOfNat` 的定义

English:
definition evalIntOfNat
  signature: : NormNumExt where eval {u α} e
  body: do
  let .app (.const ``Int.ofNat _) (n : Q(Nat)) ← whnfR e | failure
haveI' : u =QL 0 := ⟨⟩; haveI' : α =Q Int := ⟨⟩
  let sNat : Q(AddMonoidWithOne Nat) := q(Nat.instAddMonoidWithOne)
  let sInt : Q(AddMonoidWithOne Int) := q(instAddMonoidWithOne)
  let ⟨n', p⟩ ← deriveNat n sNat
haveI' x : e =Q I

中文:
定义 evalIntOfNat
  签名: : NormNumExt where eval {u α} e
  定义体: do
  let .app (.const ``Int.ofNat _) (n : Q(Nat)) ← whnfR e | failure
haveI' : u =QL 0 := ⟨⟩; haveI' : α =Q Int := ⟨⟩
  let sNat : Q(AddMonoidWithOne Nat) := q(Nat.instAddMonoidWithOne)
  let sInt : Q(AddMonoidWithOne Int) := q(instAddMonoidWithOne)
  let ⟨n', p⟩ ← deriveNat n sNat
haveI' x : e =Q I
-/
@[norm_num Int.ofNat _] def evalIntOfNat : NormNumExt where eval {u α} e := do
  let .app (.const ``Int.ofNat _) (n : Q(Nat)) ← whnfR e | failure
haveI' : u =QL 0 := ⟨⟩; haveI' : α =Q Int := ⟨⟩
  let sNat : Q(AddMonoidWithOne Nat) := q(Nat.instAddMonoidWithOne)
  let sInt : Q(AddMonoidWithOne Int) := q(instAddMonoidWithOne)
  let ⟨n', p⟩ ← deriveNat n sNat
haveI' x : e =Q Int.ofNat n := ⟨⟩
  return .isNat sInt n' q(isNat_intOfNat $p)

/--
theorem `isInt_negOfNat` / 定理 `isInt_negOfNat`

English:
theorem isInt_negOfNat
  given: (m n : Nat) (h : IsNat m n)
  statement: IsInt (Int.negOfNat m) (.negOfNat n)
  proof: ⟨congr_arg Int.negOfNat h.1⟩

中文:
定理 isInt_negOfNat
  条件: (m n : 自然数) (h : Is自然数 m n)
  结论: Is整数 (整数.negOf自然数 m) (.negOf自然数 n)
  证明: ⟨congr_arg Int.negOfNat h.1⟩

Depends on / 依赖: Int.negOfNat, congr_arg, negOfNat
-/
theorem isInt_negOfNat (m n : Nat) (h : IsNat m n) : IsInt (Int.negOfNat m) (.negOfNat n) :=
  ⟨congr_arg Int.negOfNat h.1⟩

/-- `norm_num` extension for `Int.negOfNat`.

It's useful for calling `derive` with the numerator of an `.isNegNNRat` branch. -/
@[norm_num Int.negOfNat _]
/--
Definition of `evalNegOfNat` / `evalNegOfNat` 的定义

English:
definition evalNegOfNat
  signature: : NormNumExt where eval {u αZ} e
  body: do
  match u, αZ, e with
  | 0, ~q(Int), ~q(Int.negOfNat $a) =>
    let ⟨n, pn⟩ ← deriveNat (u := 0) a q(inferInstance)
    return .isNegNat q(inferInstance) n q(isInt_negOfNat $a $n $pn)
  | _ => failure

中文:
定义 evalNegOfNat
  签名: : NormNumExt where eval {u αZ} e
  定义体: do
  match u, αZ, e with
  | 0, ~q(Int), ~q(Int.negOfNat $a) =>
    let ⟨n, pn⟩ ← deriveNat (u := 0) a q(inferInstance)
    return .isNegNat q(inferInstance) n q(isInt_negOfNat $a $n $pn)
  | _ => failure
-/
def evalNegOfNat : NormNumExt where eval {u αZ} e := do
  match u, αZ, e with
  | 0, ~q(Int), ~q(Int.negOfNat $a) =>
    let ⟨n, pn⟩ ← deriveNat (u := 0) a q(inferInstance)
    return .isNegNat q(inferInstance) n q(isInt_negOfNat $a $n $pn)
  | _ => failure

/--
theorem `isNat_natAbs_pos` / 定理 `isNat_natAbs_pos`

English:
theorem isNat_natAbs_pos
  statement: {n : Int} -> {a : Nat} -> IsNat n a -> IsNat n.natAbs a

中文:
定理 isNat_natAbs_pos
  结论: {n : 整数} -> {a : 自然数} -> Is自然数 n a -> Is自然数 n.natAbs a
-/
theorem isNat_natAbs_pos : {n : Int} -> {a : Nat} -> IsNat n a -> IsNat n.natAbs a
  | _, _, ⟨rfl⟩ => ⟨rfl⟩

/--
theorem `isNat_natAbs_neg` / 定理 `isNat_natAbs_neg`

English:
theorem isNat_natAbs_neg
  statement: {n : Int} -> {a : Nat} -> IsInt n (.negOfNat a) -> IsNat n.natAbs a

中文:
定理 isNat_natAbs_neg
  结论: {n : 整数} -> {a : 自然数} -> Is整数 n (.negOf自然数 a) -> Is自然数 n.natAbs a
-/
theorem isNat_natAbs_neg : {n : Int} -> {a : Nat} -> IsInt n (.negOfNat a) -> IsNat n.natAbs a
  | _, _, ⟨rfl⟩ => ⟨by simp⟩

/--
Definition of `evalIntNatAbs` / `evalIntNatAbs` 的定义

English:
definition evalIntNatAbs
  signature: : NormNumExt where eval {u α} e
  body: do
  let .app (.const ``Int.natAbs _) (x : Q(Int)) ← whnfR e | failure
haveI' : u =QL 0 := ⟨⟩; haveI' : α =Q Nat := ⟨⟩
haveI' : e =Q Int.natAbs x := ⟨⟩
  let sNat : Q(AddMonoidWithOne Nat) := q(Nat.instAddMonoidWithOne)
  match ← derive (u := .zero) x with
  | .isNat _ a p => assumeInstancesCommute;

中文:
定义 evalIntNatAbs
  签名: : NormNumExt where eval {u α} e
  定义体: do
  let .app (.const ``Int.natAbs _) (x : Q(Int)) ← whnfR e | failure
haveI' : u =QL 0 := ⟨⟩; haveI' : α =Q Nat := ⟨⟩
haveI' : e =Q Int.natAbs x := ⟨⟩
  let sNat : Q(AddMonoidWithOne Nat) := q(Nat.instAddMonoidWithOne)
  match ← derive (u := .zero) x with
  | .isNat _ a p => assumeInstancesCommute;
-/
@[norm_num Int.natAbs (_ : Int)] def evalIntNatAbs : NormNumExt where eval {u α} e := do
  let .app (.const ``Int.natAbs _) (x : Q(Int)) ← whnfR e | failure
haveI' : u =QL 0 := ⟨⟩; haveI' : α =Q Nat := ⟨⟩
haveI' : e =Q Int.natAbs x := ⟨⟩
  let sNat : Q(AddMonoidWithOne Nat) := q(Nat.instAddMonoidWithOne)
  match ← derive (u := .zero) x with
  | .isNat _ a p => assumeInstancesCommute; return .isNat sNat a q(isNat_natAbs_pos $p)
  | .isNegNat _ a p => assumeInstancesCommute; return .isNat sNat a q(isNat_natAbs_neg $p)
  | _ => failure


/--
theorem `isNat_natCast` / 定理 `isNat_natCast`

English:
theorem isNat_natCast
  given: {R} [AddMonoidWithOne R] (n m : Nat)
  proof: by rintro ⟨⟨⟩⟩; exact ⟨rfl⟩

中文:
定理 isNat_natCast
  条件: {R} [AddMonoidWithOne R] (n m : 自然数)
  证明: by rintro ⟨⟨⟩⟩; exact ⟨rfl⟩
-/
theorem isNat_natCast {R} [AddMonoidWithOne R] (n m : Nat) :
    IsNat n m -> IsNat (n : R) m := by rintro ⟨⟨⟩⟩; exact ⟨rfl⟩

/--
Definition of `evalNatCast` / `evalNatCast` 的定义

English:
definition evalNatCast
  signature: : NormNumExt where eval {u α} e
  body: do
  let sα ← inferAddMonoidWithOne α
  let .app n (a : Q(Nat)) ← whnfR e | failure
guard ← withNewMCtxDepth isDefEq n q(Nat.cast (R := $α))
  let ⟨na, pa⟩ ← deriveNat a q(Nat.instAddMonoidWithOne)
haveI' : e =Q a := ⟨⟩
  return .isNat sα na q(isNat_natCast $a $na $pa)

中文:
定义 evalNatCast
  签名: : NormNumExt where eval {u α} e
  定义体: do
  let sα ← inferAddMonoidWithOne α
  let .app n (a : Q(Nat)) ← whnfR e | failure
guard ← withNewMCtxDepth isDefEq n q(Nat.cast (R := $α))
  let ⟨na, pa⟩ ← deriveNat a q(Nat.instAddMonoidWithOne)
haveI' : e =Q a := ⟨⟩
  return .isNat sα na q(isNat_natCast $a $na $pa)

Depends on / 依赖: isClosed_set_pi, isClosed_singleton, univ_pi_singleton
-/
@[norm_num Nat.cast _, NatCast.natCast _] def evalNatCast : NormNumExt where eval {u α} e := do
  let sα ← inferAddMonoidWithOne α
  let .app n (a : Q(Nat)) ← whnfR e | failure
guard ← withNewMCtxDepth isDefEq n q(Nat.cast (R := $α))
  let ⟨na, pa⟩ ← deriveNat a q(Nat.instAddMonoidWithOne)
haveI' : e =Q a := ⟨⟩
  return .isNat sα na q(isNat_natCast $a $na $pa)

/--
theorem `isNat_intCast` / 定理 `isNat_intCast`

English:
theorem isNat_intCast
  given: {R} [Ring R] (n : Int) (m : Nat)
  proof: by rintro ⟨⟨⟩⟩; exact ⟨by simp⟩

中文:
定理 isNat_intCast
  条件: {R} [Ring R] (n : 整数) (m : 自然数)
  证明: by rintro ⟨⟨⟩⟩; exact ⟨by simp⟩
-/
theorem isNat_intCast {R} [Ring R] (n : Int) (m : Nat) :
    IsNat n m -> IsNat (n : R) m := by rintro ⟨⟨⟩⟩; exact ⟨by simp⟩

/--
theorem `isintCast` / 定理 `isintCast`

English:
theorem isintCast
  given: {R} [Ring R] (n m : Int)
  proof: by rintro ⟨⟨⟩⟩; exact ⟨rfl⟩

中文:
定理 isintCast
  条件: {R} [Ring R] (n m : 整数)
  证明: by rintro ⟨⟨⟩⟩; exact ⟨rfl⟩

Depends on / 依赖: T0Space, T1Space, T1Space.t0Space, t0Space
-/
theorem isintCast {R} [Ring R] (n m : Int) :
    IsInt n m -> IsInt (n : R) m := by rintro ⟨⟨⟩⟩; exact ⟨rfl⟩

/--
Definition of `evalIntCast` / `evalIntCast` 的定义

English:
definition evalIntCast
  signature: : NormNumExt where eval {u α} e
  body: do
  let rα ← inferRing α
  let .app i (a : Q(Int)) ← whnfR e | failure
guard ← withNewMCtxDepth isDefEq i q(Int.cast (R := $α))
  match ← derive (α := q(Int)) a with
  | .isNat _ na pa =>
    assumeInstancesCommute
haveI' : e =Q Int.cast a := ⟨⟩
    return .isNat _ na q(isNat_intCast $a $na $pa)
  

中文:
定义 evalIntCast
  签名: : NormNumExt where eval {u α} e
  定义体: do
  let rα ← inferRing α
  let .app i (a : Q(Int)) ← whnfR e | failure
guard ← withNewMCtxDepth isDefEq i q(Int.cast (R := $α))
  match ← derive (α := q(Int)) a with
  | .isNat _ na pa =>
    assumeInstancesCommute
haveI' : e =Q Int.cast a := ⟨⟩
    return .isNat _ na q(isNat_intCast $a $na $pa)
  
-/
@[norm_num Int.cast _, IntCast.intCast _] def evalIntCast : NormNumExt where eval {u α} e := do
  let rα ← inferRing α
  let .app i (a : Q(Int)) ← whnfR e | failure
guard ← withNewMCtxDepth isDefEq i q(Int.cast (R := $α))
  match ← derive (α := q(Int)) a with
  | .isNat _ na pa =>
    assumeInstancesCommute
haveI' : e =Q Int.cast a := ⟨⟩
    return .isNat _ na q(isNat_intCast $a $na $pa)
  | .isNegNat _ na pa =>
    assumeInstancesCommute
haveI' : e =Q Int.cast a := ⟨⟩
    return .isNegNat _ na q(isintCast $a (.negOfNat $na) $pa)
  | _ => failure


-- see note [norm_num lemma function equality]
/--
theorem `isNat_add` / 定理 `isNat_add`

English:
theorem isNat_add
  given: {α} [AddMonoidWithOne α]
  statement: forall {f : α -> α -> α} {a b : α} {a' b' c : Nat},

中文:
定理 isNat_add
  条件: {α} [AddMonoidWithOne α]
  结论: 对任意 {f : α -> α -> α} {a b : α} {a' b' c : 自然数},
-/
theorem isNat_add {α} [AddMonoidWithOne α] : forall {f : α -> α -> α} {a b : α} {a' b' c : Nat},
    f = HAdd.hAdd -> IsNat a a' -> IsNat b b' -> Nat.add a' b' = c -> IsNat (f a b) c
  | _, _, _, _, _, _, rfl, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨(Nat.cast_add _ _).symm⟩

-- see note [norm_num lemma function equality]
/--
theorem `isInt_add` / 定理 `isInt_add`

English:
theorem isInt_add
  given: {α} [Ring α]
  statement: forall {f : α -> α -> α} {a b : α} {a' b' c : Int},

中文:
定理 isInt_add
  条件: {α} [Ring α]
  结论: 对任意 {f : α -> α -> α} {a b : α} {a' b' c : 整数},
-/
theorem isInt_add {α} [Ring α] : forall {f : α -> α -> α} {a b : α} {a' b' c : Int},
    f = HAdd.hAdd -> IsInt a a' -> IsInt b b' -> Int.add a' b' = c -> IsInt (f a b) c
  | _, _, _, _, _, _, rfl, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨(Int.cast_add ..).symm⟩

-- see note [norm_num lemma function equality]
/--
theorem `isNNRat_add` / 定理 `isNNRat_add`

English:
theorem isNNRat_add
  given: {α} [Semiring α] {f : α -> α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat}
  proof: by
  rintro rfl ⟨_, rfl⟩ ⟨_, rfl⟩ (h₁ : na * db + nb * da = k * nc) (h₂ : da * db = k * dc)
  have : Invertible (↑(da * db) : α) := by simpa using invertibleMul (da:α) db
  have := invertibleOfMul' (α := α) h₂
  use this
  have H := (Nat.cast_commute (α := α) da db).invOf_left.invOf_right.right_comm

中文:
定理 isNNRat_add
  条件: {α} [Semiring α] {f : α -> α -> α} {a b : α} {na nb nc : 自然数} {da db dc k : 自然数}
  证明: by
  rintro rfl ⟨_, rfl⟩ ⟨_, rfl⟩ (h₁ : na * db + nb * da = k * nc) (h₂ : da * db = k * dc)
  have : Invertible (↑(da * db) : α) := by simpa using invertibleMul (da:α) db
  have := invertibleOfMul' (α := α) h₂
  use this
  have H := (Nat.cast_commute (α := α) da db).invOf_left.invOf_right.right_comm

Depends on / 依赖: Invertible, Nat.cast_add, Nat.cast_commute, Nat.cast_mul, add_mul, cast_add, cast_commute, cast_mul, congr_arg, invOf_left, invOf_left.invOf_right.right_comm, invOf_right, invertibleMul, invertibleOfMul, mul_assoc, mul_invOf_cancel_right, right_comm
-/
theorem isNNRat_add {α} [Semiring α] {f : α -> α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} :
    f = HAdd.hAdd -> IsNNRat a na da -> IsNNRat b nb db ->
    Nat.add (Nat.mul na db) (Nat.mul nb da) = Nat.mul k nc ->
    Nat.mul da db = Nat.mul k dc ->
    IsNNRat (f a b) nc dc := by
  rintro rfl ⟨_, rfl⟩ ⟨_, rfl⟩ (h₁ : na * db + nb * da = k * nc) (h₂ : da * db = k * dc)
  have : Invertible (↑(da * db) : α) := by simpa using invertibleMul (da:α) db
  have := invertibleOfMul' (α := α) h₂
  use this
  have H := (Nat.cast_commute (α := α) da db).invOf_left.invOf_right.right_comm
  have h₁ := congr_arg (↑· * (⅟↑da * ⅟↑db : α)) h₁
  simp only [Nat.cast_add, Nat.cast_mul, ← mul_assoc,
    add_mul, mul_invOf_cancel_right] at h₁
  have h₂ := congr_arg (↑nc * ↑· * (⅟↑da * ⅟↑db * ⅟↑dc : α)) h₂
  simp only [H, mul_invOf_cancel_right', Nat.cast_mul, ← mul_assoc] at h₁ h₂
  rw [h₁]; rw [h₂]; rw [Nat.cast_commute]
  simp only [mul_invOf_cancel_right,
    (Nat.cast_commute (α := α) da dc).invOf_left.invOf_right.right_comm,
    (Nat.cast_commute (α := α) db dc).invOf_left.invOf_right.right_comm]

-- TODO: clean up and move it somewhere in mathlib? It's a bit much for this file
-- see note [norm_num lemma function equality]
/--
theorem `isRat_add` / 定理 `isRat_add`

English:
theorem isRat_add
  given: {α} [Ring α] {f : α -> α -> α} {a b : α} {na nb nc : Int} {da db dc k : Nat}
  proof: by
  rintro rfl ⟨_, rfl⟩ ⟨_, rfl⟩ (h₁ : na * db + nb * da = k * nc) (h₂ : da * db = k * dc)
  have : Invertible (↑(da * db) : α) := by simpa using invertibleMul (da:α) db
  have := invertibleOfMul' (α := α) h₂
  use this
  have H := (Nat.cast_commute (α := α) da db).invOf_left.invOf_right.right_comm

中文:
定理 isRat_add
  条件: {α} [Ring α] {f : α -> α -> α} {a b : α} {na nb nc : 整数} {da db dc k : 自然数}
  证明: by
  rintro rfl ⟨_, rfl⟩ ⟨_, rfl⟩ (h₁ : na * db + nb * da = k * nc) (h₂ : da * db = k * dc)
  have : Invertible (↑(da * db) : α) := by simpa using invertibleMul (da:α) db
  have := invertibleOfMul' (α := α) h₂
  use this
  have H := (Nat.cast_commute (α := α) da db).invOf_left.invOf_right.right_comm

Depends on / 依赖: Int.cast_add, Int.cast_mul, Int.cast_natCast, Invertible, Nat.cast_commute, add_mul, cast_add, cast_commute, cast_mul, cast_natCast, congr_arg, invOf_left, invOf_left.invOf_right.right_comm, invOf_right, invertibleMul, invertibleOfMul, mul_assoc, mul_invOf_cancel_right, right_comm
-/
theorem isRat_add {α} [Ring α] {f : α -> α -> α} {a b : α} {na nb nc : Int} {da db dc k : Nat} :
    f = HAdd.hAdd -> IsRat a na da -> IsRat b nb db ->
    Int.add (Int.mul na db) (Int.mul nb da) = Int.mul k nc ->
    Nat.mul da db = Nat.mul k dc ->
    IsRat (f a b) nc dc := by
  rintro rfl ⟨_, rfl⟩ ⟨_, rfl⟩ (h₁ : na * db + nb * da = k * nc) (h₂ : da * db = k * dc)
  have : Invertible (↑(da * db) : α) := by simpa using invertibleMul (da:α) db
  have := invertibleOfMul' (α := α) h₂
  use this
  have H := (Nat.cast_commute (α := α) da db).invOf_left.invOf_right.right_comm
  have h₁ := congr_arg (↑· * (⅟↑da * ⅟↑db : α)) h₁
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ← mul_assoc,
    add_mul, mul_invOf_cancel_right] at h₁
  have h₂ := congr_arg (↑nc * ↑· * (⅟↑da * ⅟↑db * ⅟↑dc : α)) h₂
  simp only [H, mul_invOf_cancel_right', Nat.cast_mul, ← mul_assoc] at h₁ h₂
  rw [h₁]; rw [h₂]; rw [Nat.cast_commute]
  simp only [mul_invOf_cancel_right,
    (Nat.cast_commute (α := α) da dc).invOf_left.invOf_right.right_comm,
    (Nat.cast_commute (α := α) db dc).invOf_left.invOf_right.right_comm]

/-- Consider an `Option` as an object in the `MetaM` monad, by throwing an error on `none`. -/
@[expose, instance_reducible]
/--
Definition of `_root_.Mathlib.Meta.monadLiftOptionMetaM` / `_root_.Mathlib.Meta.monadLiftOptionMetaM` 的定义

English:
definition _root_.Mathlib.Meta.monadLiftOptionMetaM
  signature: : MonadLift Option MetaM where

中文:
定义 _root_.Mathlib.Meta.monadLiftOptionMetaM
  签名: : MonadLift Option MetaM where
-/
def _root_.Mathlib.Meta.monadLiftOptionMetaM : MonadLift Option MetaM where
  monadLift
  | none => failure
  | some e => pure e

attribute [local instance] monadLiftOptionMetaM in
/--
Definition of `Result.add` / `Result.add` 的定义

English:
definition Result.add
  signature: {u : Level} {α : Q(Type u)} {a b : Q($α)} (ra : Result q($a)) (rb : Result q($b))
  body: do
  let rec intArm (rα : Q(Ring $α)) := do
    assumeInstancesCommute
    let ⟨za, na, pa⟩ ← ra.toInt _; let ⟨zb, nb, pb⟩ ← rb.toInt _
    let zc := za + zb
    have c := mkRawIntLit zc
haveI' : Int.add na nb =Q c := ⟨⟩
    return .isInt rα c zc q(isInt_add (.refl _) $pa $pb (.refl $c))
  let rec n

中文:
定义 Result.add
  签名: {u : Level} {α : Q(类型u)} {a b : Q($α)} (ra : Result q($a)) (rb : Result q($b))
  定义体: do
  let rec intArm (rα : Q(Ring $α)) := do
    assumeInstancesCommute
    let ⟨za, na, pa⟩ ← ra.toInt _; let ⟨zb, nb, pb⟩ ← rb.toInt _
    let zc := za + zb
    have c := mkRawIntLit zc
haveI' : Int.add na nb =Q c := ⟨⟩
    return .isInt rα c zc q(isInt_add (.refl _) $pa $pb (.refl $c))
  let rec n

Depends on / 依赖: DivisionSemiring, Int.add, Result, assumeInstancesCommute, intArm, isInt_add, mkRawIntLit, nnratArm, ra.toInt, ra.toNNRat, rb.toInt, rb.toNNRa, return, toNNRa, toNNRat
-/
def Result.add {u : Level} {α : Q(Type u)} {a b : Q($α)} (ra : Result q($a)) (rb : Result q($b))
    (inst : Q(Add $α) := by exact q(delta% inferInstance)) :
    MetaM (Result q($a + $b)) := do
  let rec intArm (rα : Q(Ring $α)) := do
    assumeInstancesCommute
    let ⟨za, na, pa⟩ ← ra.toInt _; let ⟨zb, nb, pb⟩ ← rb.toInt _
    let zc := za + zb
    have c := mkRawIntLit zc
haveI' : Int.add na nb =Q c := ⟨⟩
    return .isInt rα c zc q(isInt_add (.refl _) $pa $pb (.refl $c))
  let rec nnratArm (dsα : Q(DivisionSemiring $α)) : MetaM (Result _) := do
    assumeInstancesCommute
    let ⟨qa, na, da, pa⟩ ← ra.toNNRat' dsα; let ⟨qb, nb, db, pb⟩ ← rb.toNNRat' dsα
    let qc := qa + qb
    let dd := qa.den * qb.den
    let k := dd / qc.den
    have t1 : Q(Nat) := mkRawNatLit (k * qc.num.toNat)
    have t2 : Q(Nat) := mkRawNatLit dd
    have nc : Q(Nat) := mkRawNatLit qc.num.toNat
    have dc : Q(Nat) := mkRawNatLit qc.den
    have k : Q(Nat) := mkRawNatLit k
    let r1 : Q(Nat.add (Nat.mul $na $db) (Nat.mul $nb $da) = Nat.mul $k $nc) :=
      (q(Eq.refl $t1) : Expr)
    let r2 : Q(Nat.mul $da $db = Nat.mul $k $dc) := (q(Eq.refl $t2) : Expr)
    return .isNNRat' dsα qc nc dc q(isNNRat_add (.refl _) $pa $pb $r1 $r2)
  let rec ratArm (dα : Q(DivisionRing $α)) : MetaM (Result _) := do
    assumeInstancesCommute
    let ⟨qa, na, da, pa⟩ ← ra.toRat' dα; let ⟨qb, nb, db, pb⟩ ← rb.toRat' dα
    let qc := qa + qb
    let dd := qa.den * qb.den
    let k := dd / qc.den
    have t1 : Q(Int) := mkRawIntLit (k * qc.num)
    have t2 : Q(Nat) := mkRawNatLit dd
    have nc : Q(Int) := mkRawIntLit qc.num
    have dc : Q(Nat) := mkRawNatLit qc.den
    have k : Q(Nat) := mkRawNatLit k
    let r1 : Q(Int.add (Int.mul $na $db) (Int.mul $nb $da) = Int.mul $k $nc) :=
      (q(Eq.refl $t1) : Expr)
    let r2 : Q(Nat.mul $da $db = Nat.mul $k $dc) := (q(Eq.refl $t2) : Expr)
    return .isRat dα qc nc dc q(isRat_add (.refl _) $pa $pb $r1 $r2)
  match ra, rb with
  | .isBool .., _ | _, .isBool .. => failure
  | .isNegNNRat dα .., _ | _, .isNegNNRat dα .. => ratArm dα
  -- mixing positive rationals and negative naturals means we need to use the full rat handler
  | .isNNRat _dsα .., .isNegNat _rα .. | .isNegNat _rα .., .isNNRat _dsα .. =>
    -- could alternatively try to combine `rα` and `dsα` here, but we'd have to do a defeq check
    -- so would still need to be in `MetaM`.
    let dα ← synthInstanceQ q(DivisionRing $α)
    assumeInstancesCommute
    ratArm q($dα)
  | .isNNRat dsα .., _ | _, .isNNRat dsα .. => nnratArm dsα
  | .isNegNat rα .., _ | _, .isNegNat rα .. => intArm rα
  | .isNat _ na pa, .isNat sα nb pb =>
    assumeInstancesCommute
    have c : Q(Nat) := mkRawNatLit (na.natLit! + nb.natLit!)
haveI' : Nat.add na nb =Q c := ⟨⟩
    return .isNat sα c q(isNat_add (.refl _) $pa $pb (.refl $c))

attribute [local instance] monadLiftOptionMetaM in
/--
Definition of `evalAdd` / `evalAdd` 的定义

English:
definition evalAdd
  signature: : NormNumExt where eval {u α} e
  body: do
  let .app (.app (f : Q($α -> $α -> $α)) (a : Q($α))) (b : Q($α)) ← whnfR e | failure
  let ra ← derive a; let rb ← derive b
  match ra, rb with
  | .isBool .., _ | _, .isBool .. => failure
  | .isNat _ .., .isNat _ .. | .isNat _ .., .isNegNat _ .. | .isNat _ .., .isNNRat _ ..
    | .isNat _ .., 

中文:
定义 evalAdd
  签名: : NormNumExt where eval {u α} e
  定义体: do
  let .app (.app (f : Q($α -> $α -> $α)) (a : Q($α))) (b : Q($α)) ← whnfR e | failure
  let ra ← derive a; let rb ← derive b
  match ra, rb with
  | .isBool .., _ | _, .isBool .. => failure
  | .isNat _ .., .isNat _ .. | .isNat _ .., .isNegNat _ .. | .isNat _ .., .isNNRat _ ..
    | .isNat _ .., 
-/
@[norm_num _ + _] def evalAdd : NormNumExt where eval {u α} e := do
  let .app (.app (f : Q($α -> $α -> $α)) (a : Q($α))) (b : Q($α)) ← whnfR e | failure
  let ra ← derive a; let rb ← derive b
  match ra, rb with
  | .isBool .., _ | _, .isBool .. => failure
  | .isNat _ .., .isNat _ .. | .isNat _ .., .isNegNat _ .. | .isNat _ .., .isNNRat _ ..
    | .isNat _ .., .isNegNNRat _ ..
  | .isNegNat _ .., .isNat _ .. | .isNegNat _ .., .isNegNat _ .. | .isNegNat _ .., .isNNRat _ ..
    | .isNegNat _ .., .isNegNNRat _ ..
  | .isNNRat _ .., .isNat _ .. | .isNNRat _ .., .isNegNat _ .. | .isNNRat _ .., .isNNRat _ ..
    | .isNNRat _ .., .isNegNNRat _ ..
  | .isNegNNRat _ .., .isNat _ .. | .isNegNNRat _ .., .isNegNat _ ..
    | .isNegNNRat _ .., .isNNRat _ .. | .isNegNNRat _ .., .isNegNNRat _ .. =>
guard ← withNewMCtxDepth isDefEq f q(HAdd.hAdd (α := $α))
    ra.add rb

-- see note [norm_num lemma function equality]
/--
theorem `isInt_neg` / 定理 `isInt_neg`

English:
theorem isInt_neg
  given: {α} [Ring α]
  statement: forall {f : α -> α} {a : α} {a' b : Int},

中文:
定理 isInt_neg
  条件: {α} [Ring α]
  结论: 对任意 {f : α -> α} {a : α} {a' b : 整数},
-/
theorem isInt_neg {α} [Ring α] : forall {f : α -> α} {a : α} {a' b : Int},
    f = Neg.neg -> IsInt a a' -> Int.neg a' = b -> IsInt (-a) b
  | _, _, _, _, rfl, ⟨rfl⟩, rfl => ⟨(Int.cast_neg ..).symm⟩

-- see note [norm_num lemma function equality]
/--
theorem `isRat_neg` / 定理 `isRat_neg`

English:
theorem isRat_neg
  given: {α} [Ring α]
  statement: forall {f : α -> α} {a : α} {n n' : Int} {d : Nat},

中文:
定理 isRat_neg
  条件: {α} [Ring α]
  结论: 对任意 {f : α -> α} {a : α} {n n' : 整数} {d : 自然数},
-/
theorem isRat_neg {α} [Ring α] : forall {f : α -> α} {a : α} {n n' : Int} {d : Nat},
    f = Neg.neg -> IsRat a n d -> Int.neg n = n' -> IsRat (-a) n' d
  | _, _, _, _, _, rfl, ⟨h, rfl⟩, rfl => ⟨h, by rw [← neg_mul, ← Int.cast_neg]; rfl⟩

attribute [local instance] monadLiftOptionMetaM in
/--
Definition of `Result.neg` / `Result.neg` 的定义

English:
definition Result.neg
  signature: {u : Level} {α : Q(Type u)} {a : Q($α)} (ra : Result q($a))
  body: do
  let intArm (rα : Q(Ring $α)) := do
    assumeInstancesCommute
    let ⟨za, na, pa⟩ ← ra.toInt rα
    let zb := -za
    have b := mkRawIntLit zb
haveI' : Int.neg na =Q b := ⟨⟩
    return .isInt rα b zb q(isInt_neg (.refl _) $pa (.refl $b))
  let ratArm (dα : Q(DivisionRing $α)) : Option (Result 

中文:
定义 Result.neg
  签名: {u : Level} {α : Q(类型u)} {a : Q($α)} (ra : Result q($a))
  定义体: do
  let intArm (rα : Q(Ring $α)) := do
    assumeInstancesCommute
    let ⟨za, na, pa⟩ ← ra.toInt rα
    let zb := -za
    have b := mkRawIntLit zb
haveI' : Int.neg na =Q b := ⟨⟩
    return .isInt rα b zb q(isInt_neg (.refl _) $pa (.refl $b))
  let ratArm (dα : Q(DivisionRing $α)) : Option (Result 

Depends on / 依赖: DivisionRing, Int.neg, Result, assumeInstancesCommute, intArm, isInt_neg, mkRawIntLit, qb.num, ra.toInt, ra.toRat, ratArm, return
-/
def Result.neg {u : Level} {α : Q(Type u)} {a : Q($α)} (ra : Result q($a))
    (rα : Q(Ring $α) := by exact q(delta% inferInstance)) :
    MetaM (Result q(-$a)) := do
  let intArm (rα : Q(Ring $α)) := do
    assumeInstancesCommute
    let ⟨za, na, pa⟩ ← ra.toInt rα
    let zb := -za
    have b := mkRawIntLit zb
haveI' : Int.neg na =Q b := ⟨⟩
    return .isInt rα b zb q(isInt_neg (.refl _) $pa (.refl $b))
  let ratArm (dα : Q(DivisionRing $α)) : Option (Result _) := do
    assumeInstancesCommute
    let ⟨qa, na, da, pa⟩ ← ra.toRat' dα
    let qb := -qa
    have nb := mkRawIntLit qb.num
haveI' : Int.neg na =Q nb := ⟨⟩
    return .isRat dα qb nb da q(isRat_neg (.refl _) $pa (.refl $nb))
  match ra with
  | .isBool _ .. => failure
  | .isNat _ .. => intArm rα
  | .isNegNat rα .. => intArm rα
  | .isNNRat _dsα .. => ratArm (← synthInstanceQ q(DivisionRing $α))
  | .isNegNNRat dα .. => ratArm dα

attribute [local instance] monadLiftOptionMetaM in
/--
Definition of `evalNeg` / `evalNeg` 的定义

English:
definition evalNeg
  signature: : NormNumExt where eval {u α} e
  body: do
  let .app (f : Q($α -> $α)) (a : Q($α)) ← whnfR e | failure
  let ra ← derive a
  let rα ← inferRing α
let ⟨(_f_eq : $f =Q Neg.neg)⟩ ← withNewMCtxDepth assertDefEqQ _ _
haveI' _e_eq : e =Q - a := ⟨⟩
  ra.neg

中文:
定义 evalNeg
  签名: : NormNumExt where eval {u α} e
  定义体: do
  let .app (f : Q($α -> $α)) (a : Q($α)) ← whnfR e | failure
  let ra ← derive a
  let rα ← inferRing α
let ⟨(_f_eq : $f =Q Neg.neg)⟩ ← withNewMCtxDepth assertDefEqQ _ _
haveI' _e_eq : e =Q - a := ⟨⟩
  ra.neg
-/
@[norm_num -_] def evalNeg : NormNumExt where eval {u α} e := do
  let .app (f : Q($α -> $α)) (a : Q($α)) ← whnfR e | failure
  let ra ← derive a
  let rα ← inferRing α
let ⟨(_f_eq : $f =Q Neg.neg)⟩ ← withNewMCtxDepth assertDefEqQ _ _
haveI' _e_eq : e =Q - a := ⟨⟩
  ra.neg

-- see note [norm_num lemma function equality]
/--
theorem `isInt_sub` / 定理 `isInt_sub`

English:
theorem isInt_sub
  given: {α} [Ring α]
  statement: forall {f : α -> α -> α} {a b : α} {a' b' c : Int},

中文:
定理 isInt_sub
  条件: {α} [Ring α]
  结论: 对任意 {f : α -> α -> α} {a b : α} {a' b' c : 整数},
-/
theorem isInt_sub {α} [Ring α] : forall {f : α -> α -> α} {a b : α} {a' b' c : Int},
    f = HSub.hSub -> IsInt a a' -> IsInt b b' -> Int.sub a' b' = c -> IsInt (f a b) c
  | _, _, _, _, _, _, rfl, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨(Int.cast_sub ..).symm⟩

-- see note [norm_num lemma function equality]
/--
theorem `isRat_sub` / 定理 `isRat_sub`

English:
theorem isRat_sub
  statement: {α} [Ring α] {f : α -> α -> α} {a b : α} {na nb nc : Int} {da db dc k : Nat}
  proof: by
  rw [hf]; rw [sub_eq_add_neg]
  refine isRat_add rfl ra (isRat_neg (n' := -nb) rfl rb rfl) (k := k) (nc := nc) ?_ h₂
  rw [show Int.mul (-nb) _ = _ from neg_mul ..]; exact h₁

中文:
定理 isRat_sub
  结论: {α} [Ring α] {f : α -> α -> α} {a b : α} {na nb nc : 整数} {da db dc k : 自然数}
  证明: by
  rw [hf]; rw [sub_eq_add_neg]
  refine isRat_add rfl ra (isRat_neg (n' := -nb) rfl rb rfl) (k := k) (nc := nc) ?_ h₂
  rw [show Int.mul (-nb) _ = _ from neg_mul ..]; exact h₁

Depends on / 依赖: Int.mul, isRat_add, isRat_neg, neg_mul, sub_eq_add_neg
-/
theorem isRat_sub {α} [Ring α] {f : α -> α -> α} {a b : α} {na nb nc : Int} {da db dc k : Nat}
    (hf : f = HSub.hSub) (ra : IsRat a na da) (rb : IsRat b nb db)
    (h₁ : Int.sub (Int.mul na db) (Int.mul nb da) = Int.mul k nc)
    (h₂ : Nat.mul da db = Nat.mul k dc) :
    IsRat (f a b) nc dc := by
  rw [hf]; rw [sub_eq_add_neg]
  refine isRat_add rfl ra (isRat_neg (n' := -nb) rfl rb rfl) (k := k) (nc := nc) ?_ h₂
  rw [show Int.mul (-nb) _ = _ from neg_mul ..]; exact h₁

attribute [local instance] monadLiftOptionMetaM in
/--
Definition of `Result.sub` / `Result.sub` 的定义

English:
definition Result.sub
  signature: {u : Level} {α : Q(Type u)} {a b : Q($α)} (ra : Result q($a)) (rb : Result q($b))
  body: do
  let intArm (rα : Q(Ring $α)) := do
    assumeInstancesCommute
    let ⟨za, na, pa⟩ ← ra.toInt rα; let ⟨zb, nb, pb⟩ ← rb.toInt rα
    let zc := za - zb
    have c := mkRawIntLit zc
haveI' : Int.sub na nb =Q c := ⟨⟩
    return Result.isInt rα c zc q(isInt_sub (.refl _) $pa $pb (.refl $c))
  let r

中文:
定义 Result.sub
  签名: {u : Level} {α : Q(类型u)} {a b : Q($α)} (ra : Result q($a)) (rb : Result q($b))
  定义体: do
  let intArm (rα : Q(Ring $α)) := do
    assumeInstancesCommute
    let ⟨za, na, pa⟩ ← ra.toInt rα; let ⟨zb, nb, pb⟩ ← rb.toInt rα
    let zc := za - zb
    have c := mkRawIntLit zc
haveI' : Int.sub na nb =Q c := ⟨⟩
    return Result.isInt rα c zc q(isInt_sub (.refl _) $pa $pb (.refl $c))
  let r

Depends on / 依赖: DivisionRing, Int.sub, Result, Result.isInt, assumeInstancesCommute, intArm, isInt_sub, mkRawIntLit, ra.toInt, ra.toRat, ratArm, rb.toInt, rb.toRat, return
-/
def Result.sub {u : Level} {α : Q(Type u)} {a b : Q($α)} (ra : Result q($a)) (rb : Result q($b))
    (inst : Q(Ring $α) := by exact q(delta% inferInstance)) :
    MetaM (Result q($a - $b)) := do
  let intArm (rα : Q(Ring $α)) := do
    assumeInstancesCommute
    let ⟨za, na, pa⟩ ← ra.toInt rα; let ⟨zb, nb, pb⟩ ← rb.toInt rα
    let zc := za - zb
    have c := mkRawIntLit zc
haveI' : Int.sub na nb =Q c := ⟨⟩
    return Result.isInt rα c zc q(isInt_sub (.refl _) $pa $pb (.refl $c))
  let ratArm (dα : Q(DivisionRing $α)) : MetaM (Result _) := do
    assumeInstancesCommute
    let ⟨qa, na, da, pa⟩ ← ra.toRat' dα; let ⟨qb, nb, db, pb⟩ ← rb.toRat' dα
    let qc := qa - qb
    let dd := qa.den * qb.den
    let k := dd / qc.den
    have t1 : Q(Int) := mkRawIntLit (k * qc.num)
    have t2 : Q(Nat) := mkRawNatLit dd
    have nc : Q(Int) := mkRawIntLit qc.num
    have dc : Q(Nat) := mkRawNatLit qc.den
    have k : Q(Nat) := mkRawNatLit k
    let r1 : Q(Int.sub (Int.mul $na $db) (Int.mul $nb $da) = Int.mul $k $nc) :=
      (q(Eq.refl $t1) : Expr)
    let r2 : Q(Nat.mul $da $db = Nat.mul $k $dc) := (q(Eq.refl $t2) : Expr)
    return .isRat dα qc nc dc q(isRat_sub (.refl _) $pa $pb $r1 $r2)
  match ra, rb with
  | .isBool .., _ | _, .isBool .. => failure
  | .isNegNNRat dα .., _ | _, .isNegNNRat dα .. =>
    ratArm dα
  | _, .isNNRat _dsα .. | .isNNRat _dsα .., _ =>
    ratArm (← synthInstanceQ q(DivisionRing $α))
  | .isNegNat _rα .., _ | _, .isNegNat _rα ..
  | .isNat _ .., .isNat _ .. =>
    intArm inst

attribute [local instance] monadLiftOptionMetaM in
/--
Definition of `evalSub` / `evalSub` 的定义

English:
definition evalSub
  signature: : NormNumExt where eval {u α} e
  body: do
  let .app (.app (f : Q($α -> $α -> $α)) (a : Q($α))) (b : Q($α)) ← whnfR e | failure
  let rα ← inferRing α
let ⟨(_f_eq : $f =Q HSub.hSub)⟩ ← withNewMCtxDepth assertDefEqQ _ _
  let ra ← derive a; let rb ← derive b
haveI' _e_eq : e =Q a - b := ⟨⟩
  ra.sub rb

中文:
定义 evalSub
  签名: : NormNumExt where eval {u α} e
  定义体: do
  let .app (.app (f : Q($α -> $α -> $α)) (a : Q($α))) (b : Q($α)) ← whnfR e | failure
  let rα ← inferRing α
let ⟨(_f_eq : $f =Q HSub.hSub)⟩ ← withNewMCtxDepth assertDefEqQ _ _
  let ra ← derive a; let rb ← derive b
haveI' _e_eq : e =Q a - b := ⟨⟩
  ra.sub rb
-/
@[norm_num _ - _] def evalSub : NormNumExt where eval {u α} e := do
  let .app (.app (f : Q($α -> $α -> $α)) (a : Q($α))) (b : Q($α)) ← whnfR e | failure
  let rα ← inferRing α
let ⟨(_f_eq : $f =Q HSub.hSub)⟩ ← withNewMCtxDepth assertDefEqQ _ _
  let ra ← derive a; let rb ← derive b
haveI' _e_eq : e =Q a - b := ⟨⟩
  ra.sub rb

-- see note [norm_num lemma function equality]
/--
theorem `isNat_mul` / 定理 `isNat_mul`

English:
theorem isNat_mul
  given: {α} [Semiring α]
  statement: forall {f : α -> α -> α} {a b : α} {a' b' c : Nat},

中文:
定理 isNat_mul
  条件: {α} [Semiring α]
  结论: 对任意 {f : α -> α -> α} {a b : α} {a' b' c : 自然数},
-/
theorem isNat_mul {α} [Semiring α] : forall {f : α -> α -> α} {a b : α} {a' b' c : Nat},
    f = HMul.hMul -> IsNat a a' -> IsNat b b' -> Nat.mul a' b' = c -> IsNat (a * b) c
  | _, _, _, _, _, _, rfl, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨(Nat.cast_mul ..).symm⟩

-- see note [norm_num lemma function equality]
/--
theorem `isInt_mul` / 定理 `isInt_mul`

English:
theorem isInt_mul
  given: {α} [Ring α]
  statement: forall {f : α -> α -> α} {a b : α} {a' b' c : Int},

中文:
定理 isInt_mul
  条件: {α} [Ring α]
  结论: 对任意 {f : α -> α -> α} {a b : α} {a' b' c : 整数},
-/
theorem isInt_mul {α} [Ring α] : forall {f : α -> α -> α} {a b : α} {a' b' c : Int},
    f = HMul.hMul -> IsInt a a' -> IsInt b b' -> Int.mul a' b' = c -> IsInt (a * b) c
  | _, _, _, _, _, _, rfl, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨(Int.cast_mul ..).symm⟩

/--
theorem `isNNRat_mul` / 定理 `isNNRat_mul`

English:
theorem isNNRat_mul
  given: {α} [Semiring α] {f : α -> α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat}
  proof: by
  rintro rfl ⟨_, rfl⟩ ⟨_, rfl⟩ (h₁ : na * nb = k * nc) (h₂ : da * db = k * dc)
  have : Invertible (↑(da * db) : α) := by simpa using invertibleMul (da:α) db
  have := invertibleOfMul' (α := α) h₂
  refine ⟨this, ?_⟩
  have H := (Nat.cast_commute (α := α) da db).invOf_left.invOf_right.right_comm


中文:
定理 isNNRat_mul
  条件: {α} [Semiring α] {f : α -> α -> α} {a b : α} {na nb nc : 自然数} {da db dc k : 自然数}
  证明: by
  rintro rfl ⟨_, rfl⟩ ⟨_, rfl⟩ (h₁ : na * nb = k * nc) (h₂ : da * db = k * dc)
  have : Invertible (↑(da * db) : α) := by simpa using invertibleMul (da:α) db
  have := invertibleOfMul' (α := α) h₂
  refine ⟨this, ?_⟩
  have H := (Nat.cast_commute (α := α) da db).invOf_left.invOf_right.right_comm


Depends on / 依赖: Invertible, Nat.cast, Nat.cast_commute, Nat.cast_mul, cast_commute, cast_mul, congr_arg, invOf_left, invOf_left.invOf_right.right_comm, invOf_left.right_comm, invOf_right, invertibleMul, invertibleOfMul, mul_assoc, right_comm
-/
theorem isNNRat_mul {α} [Semiring α] {f : α -> α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} :
    f = HMul.hMul -> IsNNRat a na da -> IsNNRat b nb db ->
    Nat.mul na nb = Nat.mul k nc ->
    Nat.mul da db = Nat.mul k dc ->
    IsNNRat (f a b) nc dc := by
  rintro rfl ⟨_, rfl⟩ ⟨_, rfl⟩ (h₁ : na * nb = k * nc) (h₂ : da * db = k * dc)
  have : Invertible (↑(da * db) : α) := by simpa using invertibleMul (da:α) db
  have := invertibleOfMul' (α := α) h₂
  refine ⟨this, ?_⟩
  have H := (Nat.cast_commute (α := α) da db).invOf_left.invOf_right.right_comm
  have h₁ := congr_arg (Nat.cast (R := α)) h₁
  simp only [Nat.cast_mul] at h₁
  simp only [← mul_assoc, (Nat.cast_commute (α := α) da nb).invOf_left.right_comm, h₁]
  have h₂ := congr_arg (↑nc * ↑· * (⅟↑da * ⅟↑db * ⅟↑dc : α)) h₂
  simp only [Nat.cast_mul, ← mul_assoc] at h₂; rw [H] at h₂
  simp only [mul_invOf_cancel_right'] at h₂; rw [h₂, Nat.cast_commute]
  simp only [mul_invOf_cancel_right',
    (Nat.cast_commute (α := α) da dc).invOf_left.invOf_right.right_comm,
    (Nat.cast_commute (α := α) db dc).invOf_left.invOf_right.right_comm]

/--
theorem `isRat_mul` / 定理 `isRat_mul`

English:
theorem isRat_mul
  given: {α} [Ring α] {f : α -> α -> α} {a b : α} {na nb nc : Int} {da db dc k : Nat}
  proof: by
  rintro rfl ⟨_, rfl⟩ ⟨_, rfl⟩ (h₁ : na * nb = k * nc) (h₂ : da * db = k * dc)
  have : Invertible (↑(da * db) : α) := by simpa using invertibleMul (da:α) db
  have := invertibleOfMul' (α := α) h₂
  refine ⟨this, ?_⟩
  have H := (Nat.cast_commute (α := α) da db).invOf_left.invOf_right.right_comm


中文:
定理 isRat_mul
  条件: {α} [Ring α] {f : α -> α -> α} {a b : α} {na nb nc : 整数} {da db dc k : 自然数}
  证明: by
  rintro rfl ⟨_, rfl⟩ ⟨_, rfl⟩ (h₁ : na * nb = k * nc) (h₂ : da * db = k * dc)
  have : Invertible (↑(da * db) : α) := by simpa using invertibleMul (da:α) db
  have := invertibleOfMul' (α := α) h₂
  refine ⟨this, ?_⟩
  have H := (Nat.cast_commute (α := α) da db).invOf_left.invOf_right.right_comm


Depends on / 依赖: Int.cast, Int.cast_mul, Int.cast_natCast, Invertible, Nat.cast_commute, cast_commute, cast_mul, cast_natCast, congr_arg, invOf_left, invOf_left.invOf_right.right_comm, invOf_left.right_comm, invOf_right, invertibleMul, invertibleOfMul, mul_assoc, right_comm
-/
theorem isRat_mul {α} [Ring α] {f : α -> α -> α} {a b : α} {na nb nc : Int} {da db dc k : Nat} :
    f = HMul.hMul -> IsRat a na da -> IsRat b nb db ->
    Int.mul na nb = Int.mul k nc ->
    Nat.mul da db = Nat.mul k dc ->
    IsRat (f a b) nc dc := by
  rintro rfl ⟨_, rfl⟩ ⟨_, rfl⟩ (h₁ : na * nb = k * nc) (h₂ : da * db = k * dc)
  have : Invertible (↑(da * db) : α) := by simpa using invertibleMul (da:α) db
  have := invertibleOfMul' (α := α) h₂
  refine ⟨this, ?_⟩
  have H := (Nat.cast_commute (α := α) da db).invOf_left.invOf_right.right_comm
  have h₁ := congr_arg (Int.cast (R := α)) h₁
  simp only [Int.cast_mul, Int.cast_natCast] at h₁
  simp only [← mul_assoc, (Nat.cast_commute (α := α) da nb).invOf_left.right_comm, h₁]
  have h₂ := congr_arg (↑nc * ↑· * (⅟↑da * ⅟↑db * ⅟↑dc : α)) h₂
  simp only [Nat.cast_mul, ← mul_assoc] at h₂; rw [H] at h₂
  simp only [mul_invOf_cancel_right'] at h₂; rw [h₂, Nat.cast_commute]
  simp only [mul_invOf_cancel_right,
    (Nat.cast_commute (α := α) da dc).invOf_left.invOf_right.right_comm,
    (Nat.cast_commute (α := α) db dc).invOf_left.invOf_right.right_comm]

attribute [local instance] monadLiftOptionMetaM in
/--
Definition of `Result.mul` / `Result.mul` 的定义

English:
definition Result.mul
  signature: {u : Level} {α : Q(Type u)} {a b : Q($α)} (ra : Result q($a)) (rb : Result q($b))
  body: do
  let intArm (rα : Q(Ring $α)) := do
    assumeInstancesCommute
    let ⟨za, na, pa⟩ ← ra.toInt rα; let ⟨zb, nb, pb⟩ ← rb.toInt rα
    let zc := za * zb
    have c := mkRawIntLit zc
haveI' : Int.mul na nb =Q c := ⟨⟩
    return .isInt rα c zc q(isInt_mul (.refl _) $pa $pb (.refl $c))
  let nnratAr

中文:
定义 Result.mul
  签名: {u : Level} {α : Q(类型u)} {a b : Q($α)} (ra : Result q($a)) (rb : Result q($b))
  定义体: do
  let intArm (rα : Q(Ring $α)) := do
    assumeInstancesCommute
    let ⟨za, na, pa⟩ ← ra.toInt rα; let ⟨zb, nb, pb⟩ ← rb.toInt rα
    let zc := za * zb
    have c := mkRawIntLit zc
haveI' : Int.mul na nb =Q c := ⟨⟩
    return .isInt rα c zc q(isInt_mul (.refl _) $pa $pb (.refl $c))
  let nnratAr

Depends on / 依赖: DivisionSemiring, Int.mul, Result, assumeInstancesCommute, intArm, isInt_mul, mkRawIntLit, nnratArm, ra.toInt, ra.toNNRat, rb.toInt, rb.toNNRat, return, toNNRat
-/
def Result.mul {u : Level} {α : Q(Type u)} {a b : Q($α)} (ra : Result q($a)) (rb : Result q($b))
    (inst : Q(Semiring $α) := by exact q(delta% inferInstance)) :
    MetaM (Result q($a * $b)) := do
  let intArm (rα : Q(Ring $α)) := do
    assumeInstancesCommute
    let ⟨za, na, pa⟩ ← ra.toInt rα; let ⟨zb, nb, pb⟩ ← rb.toInt rα
    let zc := za * zb
    have c := mkRawIntLit zc
haveI' : Int.mul na nb =Q c := ⟨⟩
    return .isInt rα c zc q(isInt_mul (.refl _) $pa $pb (.refl $c))
  let nnratArm (dsα : Q(DivisionSemiring $α)) : Option (Result _) := do
    assumeInstancesCommute
    let ⟨qa, na, da, pa⟩ ← ra.toNNRat' dsα; let ⟨qb, nb, db, pb⟩ ← rb.toNNRat' dsα
    let qc := qa * qb
    let dd := qa.den * qb.den
    let k := dd / qc.den
    have nc : Q(Nat) := mkRawNatLit qc.num.toNat
    have dc : Q(Nat) := mkRawNatLit qc.den
    have k : Q(Nat) := mkRawNatLit k
    let r1 : Q(Nat.mul $na $nb = Nat.mul $k $nc) :=
      (q(Eq.refl (Nat.mul $na $nb)) : Expr)
    have t2 : Q(Nat) := mkRawNatLit dd
    let r2 : Q(Nat.mul $da $db = Nat.mul $k $dc) := (q(Eq.refl $t2) : Expr)
    return .isNNRat' dsα qc nc dc q(isNNRat_mul (.refl _) $pa $pb $r1 $r2)
  let rec ratArm (dα : Q(DivisionRing $α)) : Option (Result _) := do
    assumeInstancesCommute
    let ⟨qa, na, da, pa⟩ ← ra.toRat' dα; let ⟨qb, nb, db, pb⟩ ← rb.toRat' dα
    let qc := qa * qb
    let dd := qa.den * qb.den
    let k := dd / qc.den
    have nc : Q(Int) := mkRawIntLit qc.num
    have dc : Q(Nat) := mkRawNatLit qc.den
    have k : Q(Nat) := mkRawNatLit k
    let r1 : Q(Int.mul $na $nb = Int.mul $k $nc) :=
      (q(Eq.refl (Int.mul $na $nb)) : Expr)
    have t2 : Q(Nat) := mkRawNatLit dd
    let r2 : Q(Nat.mul $da $db = Nat.mul $k $dc) := (q(Eq.refl $t2) : Expr)
    return .isRat dα qc nc dc q(isRat_mul (.refl _) $pa $pb $r1 $r2)
  match ra, rb with
  | .isBool .., _ | _, .isBool .. => failure
  | .isNegNNRat dα .., _ | _, .isNegNNRat dα .. =>
    ratArm dα
  -- mixing positive rationals and negative naturals means we need to use the full rat handler
  | .isNNRat dsα .., .isNegNat rα .. | .isNegNat rα .., .isNNRat dsα .. =>
    -- could alternatively try to combine `rα` and `dsα` here, but we'd have to do a defeq check
    -- so would still need to be in `MetaM`.
    ratArm (← synthInstanceQ q(DivisionRing $α))
  | .isNNRat dsα .., _ | _, .isNNRat dsα .. =>
    nnratArm dsα
  | .isNegNat rα .., _ | _, .isNegNat rα .. => intArm rα
  | .isNat mα' na pa, .isNat mα nb pb => do
haveI' : mα =Q by clear! mα mα'; apply AddCommMonoidWithOne.toAddMonoidWithOne := ⟨⟩
    assumeInstancesCommute
    have c : Q(Nat) := mkRawNatLit (na.natLit! * nb.natLit!)
haveI' : Nat.mul na nb =Q c := ⟨⟩
    return .isNat mα c q(isNat_mul (.refl _) $pa $pb (.refl $c))

/--
Definition of `evalMul` / `evalMul` 的定义

English:
definition evalMul
  signature: : NormNumExt where eval {u α} e
  body: do
  let .app (.app (f : Q($α -> $α -> $α)) (a : Q($α))) (b : Q($α)) ← whnfR e | failure
  let sα ← inferSemiring α
  let ra ← derive a; let rb ← derive b
guard ← withNewMCtxDepth isDefEq f q(HMul.hMul (α := $α))
haveI' : f =Q HMul.hMul := ⟨⟩
haveI' : e =Q a * b := ⟨⟩
  ra.mul rb

中文:
定义 evalMul
  签名: : NormNumExt where eval {u α} e
  定义体: do
  let .app (.app (f : Q($α -> $α -> $α)) (a : Q($α))) (b : Q($α)) ← whnfR e | failure
  let sα ← inferSemiring α
  let ra ← derive a; let rb ← derive b
guard ← withNewMCtxDepth isDefEq f q(HMul.hMul (α := $α))
haveI' : f =Q HMul.hMul := ⟨⟩
haveI' : e =Q a * b := ⟨⟩
  ra.mul rb
-/
@[norm_num _ * _] def evalMul : NormNumExt where eval {u α} e := do
  let .app (.app (f : Q($α -> $α -> $α)) (a : Q($α))) (b : Q($α)) ← whnfR e | failure
  let sα ← inferSemiring α
  let ra ← derive a; let rb ← derive b
guard ← withNewMCtxDepth isDefEq f q(HMul.hMul (α := $α))
haveI' : f =Q HMul.hMul := ⟨⟩
haveI' : e =Q a * b := ⟨⟩
  ra.mul rb

/--
theorem `isNNRat_div` / 定理 `isNNRat_div`

English:
theorem isNNRat_div
  given: {α : Type u} [DivisionSemiring α]
  statement: {a b : α} -> {cn : Nat} -> {cd : Nat} ->

中文:
定理 isNNRat_div
  条件: {α : 类型u} [DivisionSemiring α]
  结论: {a b : α} -> {cn : 自然数} -> {cd : 自然数} ->
-/
theorem isNNRat_div {α : Type u} [DivisionSemiring α] : {a b : α} -> {cn : Nat} -> {cd : Nat} ->
    IsNNRat (a * b⁻¹) cn cd -> IsNNRat (a / b) cn cd
  | _, _, _, _, h => by simpa [div_eq_mul_inv] using h

/--
theorem `isRat_div` / 定理 `isRat_div`

English:
theorem isRat_div
  given: {α : Type u} [DivisionRing α]
  statement: {a b : α} -> {cn : Int} -> {cd : Nat} ->

中文:
定理 isRat_div
  条件: {α : 类型u} [DivisionRing α]
  结论: {a b : α} -> {cn : 整数} -> {cd : 自然数} ->
-/
theorem isRat_div {α : Type u} [DivisionRing α] : {a b : α} -> {cn : Int} -> {cd : Nat} ->
    IsRat (a * b⁻¹) cn cd -> IsRat (a / b) cn cd
  | _, _, _, _, h => by simpa [div_eq_mul_inv] using h

/--
Definition of `inferDivisionSemiring` / `inferDivisionSemiring` 的定义

English:
definition inferDivisionSemiring
  signature: {u : Level} (α : Q(Type u))
  body: return ← synthInstanceQ q(DivisionSemiring $α) > throwError "not a division semiring"

中文:
定义 inferDivisionSemiring
  签名: {u : Level} (α : Q(类型u))
  定义体: return ← synthInstanceQ q(DivisionSemiring $α) > throwError "not a division semiring"

Depends on / 依赖: DivisionSemiring, division, return, semiring, synthInstanceQ, throwError
-/
def inferDivisionSemiring {u : Level} (α : Q(Type u)) : MetaM Q(DivisionSemiring $α) :=
return ← synthInstanceQ q(DivisionSemiring $α) > throwError "not a division semiring"

/--
Definition of `inferDivisionRing` / `inferDivisionRing` 的定义

English:
definition inferDivisionRing
  signature: {u : Level} (α : Q(Type u))
  body: return ← synthInstanceQ q(DivisionRing $α) > throwError "not a division ring"

中文:
定义 inferDivisionRing
  签名: {u : Level} (α : Q(类型u))
  定义体: return ← synthInstanceQ q(DivisionRing $α) > throwError "not a division ring"

Depends on / 依赖: DivisionRing, division, return, synthInstanceQ, throwError
-/
def inferDivisionRing {u : Level} (α : Q(Type u)) : MetaM Q(DivisionRing $α) :=
return ← synthInstanceQ q(DivisionRing $α) > throwError "not a division ring"

attribute [local instance] monadLiftOptionMetaM in
/--
Definition of `evalDiv` / `evalDiv` 的定义

English:
definition evalDiv
  signature: : NormNumExt where eval {u α} e
  body: do
  let .app (.app f (a : Q($α))) (b : Q($α)) ← whnfR e | failure
  let dsα ← inferDivisionSemiring α
haveI' : e =Q a / b := ⟨⟩
guard ← withNewMCtxDepth isDefEq f q(HDiv.hDiv (α := $α))
  let rab ← derive (q($a * $b⁻¹) : Q($α))
  if let some ⟨qa, na, da, pa⟩ := rab.toNNRat' dsα then
    assumeInsta

中文:
定义 evalDiv
  签名: : NormNumExt where eval {u α} e
  定义体: do
  let .app (.app f (a : Q($α))) (b : Q($α)) ← whnfR e | failure
  let dsα ← inferDivisionSemiring α
haveI' : e =Q a / b := ⟨⟩
guard ← withNewMCtxDepth isDefEq f q(HDiv.hDiv (α := $α))
  let rab ← derive (q($a * $b⁻¹) : Q($α))
  if let some ⟨qa, na, da, pa⟩ := rab.toNNRat' dsα then
    assumeInsta
-/
@[norm_num _ / _] def evalDiv : NormNumExt where eval {u α} e := do
  let .app (.app f (a : Q($α))) (b : Q($α)) ← whnfR e | failure
  let dsα ← inferDivisionSemiring α
haveI' : e =Q a / b := ⟨⟩
guard ← withNewMCtxDepth isDefEq f q(HDiv.hDiv (α := $α))
  let rab ← derive (q($a * $b⁻¹) : Q($α))
  if let some ⟨qa, na, da, pa⟩ := rab.toNNRat' dsα then
    assumeInstancesCommute
    return .isNNRat' dsα qa na da q(isNNRat_div $pa)
  else
    let dα ← inferDivisionRing α
    let ⟨qa, na, da, pa⟩ ← rab.toRat' dα
    assumeInstancesCommute
    return .isRat dα qa na da q(isRat_div $pa)

/-! ### Logic -/

/--
Definition of `evalTrue` / `evalTrue` 的定义

English:
definition evalTrue
  signature: : NormNumExt where eval {u α} e
  body: return (.isTrue q(True.intro) : Result q(True))

中文:
定义 evalTrue
  签名: : NormNumExt where eval {u α} e
  定义体: return (.isTrue q(True.intro) : Result q(True))
-/
@[norm_num True] def evalTrue : NormNumExt where eval {u α} e :=
  return (.isTrue q(True.intro) : Result q(True))

/--
Definition of `evalFalse` / `evalFalse` 的定义

English:
definition evalFalse
  signature: : NormNumExt where eval {u α} e
  body: return (.isFalse q(not_false) : Result q(False))

中文:
定义 evalFalse
  签名: : NormNumExt where eval {u α} e
  定义体: return (.isFalse q(not_false) : Result q(False))
-/
@[norm_num False] def evalFalse : NormNumExt where eval {u α} e :=
  return (.isFalse q(not_false) : Result q(False))

/--
Definition of `evalNot` / `evalNot` 的定义

English:
definition evalNot
  signature: : NormNumExt where eval {u α} e
  body: do
  let .app (.const ``Not _) (a : Q(Prop)) ← whnfR e | failure
guard ← withNewMCtxDepth isDefEq α q(Prop)
  let ⟨b, p⟩ ← deriveBool q($a)
  match b with
  | true => return .isFalse q(not_not_intro $p)
  | false => return .isTrue q($p)

中文:
定义 evalNot
  签名: : NormNumExt where eval {u α} e
  定义体: do
  let .app (.const ``Not _) (a : Q(Prop)) ← whnfR e | failure
guard ← withNewMCtxDepth isDefEq α q(Prop)
  let ⟨b, p⟩ ← deriveBool q($a)
  match b with
  | true => return .isFalse q(not_not_intro $p)
  | false => return .isTrue q($p)
-/
@[norm_num ¬_] def evalNot : NormNumExt where eval {u α} e := do
  let .app (.const ``Not _) (a : Q(Prop)) ← whnfR e | failure
guard ← withNewMCtxDepth isDefEq α q(Prop)
  let ⟨b, p⟩ ← deriveBool q($a)
  match b with
  | true => return .isFalse q(not_not_intro $p)
  | false => return .isTrue q($p)

/-! ### (In)equalities -/

variable {α : Type u}

/--
theorem `isNat_eq_true` / 定理 `isNat_eq_true`

English:
theorem isNat_eq_true
  given: [AddMonoidWithOne α]
  statement: {a b : α} -> {c : Nat} ->

中文:
定理 isNat_eq_true
  条件: [AddMonoidWithOne α]
  结论: {a b : α} -> {c : 自然数} ->
-/
theorem isNat_eq_true [AddMonoidWithOne α] : {a b : α} -> {c : Nat} ->
    IsNat a c -> IsNat b c -> a = b
  | _, _, _, ⟨rfl⟩, ⟨rfl⟩ => rfl

/--
theorem `ble_eq_false` / 定理 `ble_eq_false`

English:
theorem ble_eq_false
  given: {x y : Nat}
  statement: x.ble y = false ↔ y < x
  proof: by
  rw [← Nat.not_le]; rw [← Bool.not_eq_true]; rw [Nat.ble_eq]

中文:
定理 ble_eq_false
  条件: {x y : 自然数}
  结论: x.ble y = false ↔ y < x
  证明: by
  rw [← Nat.not_le]; rw [← Bool.not_eq_true]; rw [Nat.ble_eq]

Depends on / 依赖: Bool.not_eq_true, Nat.ble_eq, Nat.not_le, ble_eq, not_eq_true, not_le
-/
theorem ble_eq_false {x y : Nat} : x.ble y = false ↔ y < x := by
  rw [← Nat.not_le]; rw [← Bool.not_eq_true]; rw [Nat.ble_eq]

/--
theorem `isInt_eq_true` / 定理 `isInt_eq_true`

English:
theorem isInt_eq_true
  given: [Ring α]
  statement: {a b : α} -> {z : Int} -> IsInt a z -> IsInt b z -> a = b

中文:
定理 isInt_eq_true
  条件: [Ring α]
  结论: {a b : α} -> {z : 整数} -> Is整数 a z -> Is整数 b z -> a = b
-/
theorem isInt_eq_true [Ring α] : {a b : α} -> {z : Int} -> IsInt a z -> IsInt b z -> a = b
  | _, _, _, ⟨rfl⟩, ⟨rfl⟩ => rfl

/--
theorem `isNNRat_eq_true` / 定理 `isNNRat_eq_true`

English:
theorem isNNRat_eq_true
  given: [Semiring α]
  statement: {a b : α} -> {n : Nat} -> {d : Nat} ->

中文:
定理 isNNRat_eq_true
  条件: [Semiring α]
  结论: {a b : α} -> {n : 自然数} -> {d : 自然数} ->
-/
theorem isNNRat_eq_true [Semiring α] : {a b : α} -> {n : Nat} -> {d : Nat} ->
    IsNNRat a n d -> IsNNRat b n d -> a = b
  | _, _, _, _, ⟨_, rfl⟩, ⟨_, rfl⟩ => by congr; apply Subsingleton.elim

/--
theorem `isRat_eq_true` / 定理 `isRat_eq_true`

English:
theorem isRat_eq_true
  given: [Ring α]
  statement: {a b : α} -> {n : Int} -> {d : Nat} ->

中文:
定理 isRat_eq_true
  条件: [Ring α]
  结论: {a b : α} -> {n : 整数} -> {d : 自然数} ->
-/
theorem isRat_eq_true [Ring α] : {a b : α} -> {n : Int} -> {d : Nat} ->
    IsRat a n d -> IsRat b n d -> a = b
  | _, _, _, _, ⟨_, rfl⟩, ⟨_, rfl⟩ => by congr; apply Subsingleton.elim

/--
theorem `eq_of_true` / 定理 `eq_of_true`

English:
theorem eq_of_true
  given: {a b : Prop} (ha : a) (hb : b)
  statement: a = b
  proof: propext (iff_of_true ha hb)

中文:
定理 eq_of_true
  条件: {a b : 命题} (ha : a) (hb : b)
  结论: a = b
  证明: propext (iff_of_true ha hb)

Depends on / 依赖: iff_of_true, propext
-/
theorem eq_of_true {a b : Prop} (ha : a) (hb : b) : a = b := propext (iff_of_true ha hb)
/--
theorem `ne_of_false_of_true` / 定理 `ne_of_false_of_true`

English:
theorem ne_of_false_of_true
  given: {a b : Prop} (ha : ¬a) (hb : b)
  statement: a != b
  proof: mt (· ▸ hb) ha

中文:
定理 ne_of_false_of_true
  条件: {a b : 命题} (ha : ¬a) (hb : b)
  结论: a != b
  证明: mt (· ▸ hb) ha
-/
theorem ne_of_false_of_true {a b : Prop} (ha : ¬a) (hb : b) : a != b := mt (· ▸ hb) ha
/--
theorem `ne_of_true_of_false` / 定理 `ne_of_true_of_false`

English:
theorem ne_of_true_of_false
  given: {a b : Prop} (ha : a) (hb : ¬b)
  statement: a != b
  proof: mt (· ▸ ha) hb

中文:
定理 ne_of_true_of_false
  条件: {a b : 命题} (ha : a) (hb : ¬b)
  结论: a != b
  证明: mt (· ▸ ha) hb
-/
theorem ne_of_true_of_false {a b : Prop} (ha : a) (hb : ¬b) : a != b := mt (· ▸ ha) hb
/--
theorem `eq_of_false` / 定理 `eq_of_false`

English:
theorem eq_of_false
  given: {a b : Prop} (ha : ¬a) (hb : ¬b)
  statement: a = b
  proof: propext (iff_of_false ha hb)

中文:
定理 eq_of_false
  条件: {a b : 命题} (ha : ¬a) (hb : ¬b)
  结论: a = b
  证明: propext (iff_of_false ha hb)

Depends on / 依赖: iff_of_false, propext
-/
theorem eq_of_false {a b : Prop} (ha : ¬a) (hb : ¬b) : a = b := propext (iff_of_false ha hb)


/--
theorem `isNat_natSucc` / 定理 `isNat_natSucc`

English:
theorem isNat_natSucc
  statement: {a : Nat} -> {a' c : Nat} ->

中文:
定理 isNat_natSucc
  结论: {a : 自然数} -> {a' c : 自然数} ->
-/
theorem isNat_natSucc : {a : Nat} -> {a' c : Nat} ->
    IsNat a a' -> Nat.succ a' = c -> IsNat (a.succ) c
  | _, _,_, ⟨rfl⟩, rfl => ⟨by simp⟩

/--
Definition of `evalNatSucc` / `evalNatSucc` 的定义

English:
definition evalNatSucc
  signature: : NormNumExt where eval {u α} e
  body: do
  let .app f (a : Q(Nat)) ← whnfR e | failure
guard ← withNewMCtxDepth isDefEq f q(Nat.succ)
haveI' : u =QL 0 := ⟨⟩; haveI' : α =Q Nat := ⟨⟩
haveI' : e =Q Nat.succ a := ⟨⟩
  let sNat : Q(AddMonoidWithOne Nat) := q(Nat.instAddMonoidWithOne)
  let ⟨na, pa⟩ ← deriveNat a sNat
  have nc : Q(Nat) := m

中文:
定义 evalNatSucc
  签名: : NormNumExt where eval {u α} e
  定义体: do
  let .app f (a : Q(Nat)) ← whnfR e | failure
guard ← withNewMCtxDepth isDefEq f q(Nat.succ)
haveI' : u =QL 0 := ⟨⟩; haveI' : α =Q Nat := ⟨⟩
haveI' : e =Q Nat.succ a := ⟨⟩
  let sNat : Q(AddMonoidWithOne Nat) := q(Nat.instAddMonoidWithOne)
  let ⟨na, pa⟩ ← deriveNat a sNat
  have nc : Q(Nat) := m

Depends on / 依赖: DiscreteTopology, T1Space, isClosed_discrete
-/
@[norm_num Nat.succ _] def evalNatSucc : NormNumExt where eval {u α} e := do
  let .app f (a : Q(Nat)) ← whnfR e | failure
guard ← withNewMCtxDepth isDefEq f q(Nat.succ)
haveI' : u =QL 0 := ⟨⟩; haveI' : α =Q Nat := ⟨⟩
haveI' : e =Q Nat.succ a := ⟨⟩
  let sNat : Q(AddMonoidWithOne Nat) := q(Nat.instAddMonoidWithOne)
  let ⟨na, pa⟩ ← deriveNat a sNat
  have nc : Q(Nat) := mkRawNatLit (na.natLit!.succ)
haveI' : nc =Q ($na).succ := ⟨⟩
  return .isNat sNat nc q(isNat_natSucc $pa (.refl $nc))

/--
theorem `isNat_natSub` / 定理 `isNat_natSub`

English:
theorem isNat_natSub
  statement: {a b : Nat} -> {a' b' c : Nat} ->

中文:
定理 isNat_natSub
  结论: {a b : 自然数} -> {a' b' c : 自然数} ->
-/
theorem isNat_natSub : {a b : Nat} -> {a' b' c : Nat} ->
    IsNat a a' -> IsNat b b' -> Nat.sub a' b' = c -> IsNat (a - b) c
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨by simp⟩

/--
Definition of `evalNatSub` / `evalNatSub` 的定义

English:
definition evalNatSub
  signature: :
  body: do
  let .app (.app f (a : Q(Nat))) (b : Q(Nat)) ← whnfR e | failure
  -- We assert that the default instance for `HSub` is `Nat.sub` when the first parameter is `ℕ`.
guard ← withNewMCtxDepth isDefEq f q(HSub.hSub (α := Nat))
haveI' : u =QL 0 := ⟨⟩; haveI' : α =Q Nat := ⟨⟩
haveI' : e =Q a - b := ⟨⟩


中文:
定义 evalNatSub
  签名: :
  定义体: do
  let .app (.app f (a : Q(Nat))) (b : Q(Nat)) ← whnfR e | failure
  -- We assert that the default instance for `HSub` is `Nat.sub` when the first parameter is `ℕ`.
guard ← withNewMCtxDepth isDefEq f q(HSub.hSub (α := Nat))
haveI' : u =QL 0 := ⟨⟩; haveI' : α =Q Nat := ⟨⟩
haveI' : e =Q a - b := ⟨⟩

-/
@[norm_num (_ : Nat) - _] def evalNatSub :
    NormNumExt where eval {u α} e := do
  let .app (.app f (a : Q(Nat))) (b : Q(Nat)) ← whnfR e | failure
  -- We assert that the default instance for `HSub` is `Nat.sub` when the first parameter is `ℕ`.
guard ← withNewMCtxDepth isDefEq f q(HSub.hSub (α := Nat))
haveI' : u =QL 0 := ⟨⟩; haveI' : α =Q Nat := ⟨⟩
haveI' : e =Q a - b := ⟨⟩
  let sNat : Q(AddMonoidWithOne Nat) := q(Nat.instAddMonoidWithOne)
  let ⟨na, pa⟩ ← deriveNat a sNat; let ⟨nb, pb⟩ ← deriveNat b sNat
  have nc : Q(Nat) := mkRawNatLit (na.natLit! - nb.natLit!)
haveI' : Nat.sub na nb =Q nc := ⟨⟩
  return .isNat sNat nc q(isNat_natSub $pa $pb (.refl $nc))

/--
theorem `isNat_natMod` / 定理 `isNat_natMod`

English:
theorem isNat_natMod
  statement: {a b : Nat} -> {a' b' c : Nat} ->

中文:
定理 isNat_natMod
  结论: {a b : 自然数} -> {a' b' c : 自然数} ->
-/
theorem isNat_natMod : {a b : Nat} -> {a' b' c : Nat} ->
    IsNat a a' -> IsNat b b' -> Nat.mod a' b' = c -> IsNat (a % b) c
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨by aesop⟩

/--
Definition of `evalNatMod` / `evalNatMod` 的定义

English:
definition evalNatMod
  signature: :
  body: do
  let .app (.app f (a : Q(Nat))) (b : Q(Nat)) ← whnfR e | failure
haveI' : u =QL 0 := ⟨⟩; haveI' : α =Q Nat := ⟨⟩
haveI' : e =Q a % b := ⟨⟩
  -- We assert that the default instance for `HMod` is `Nat.mod` when the first parameter is `ℕ`.
guard ← withNewMCtxDepth isDefEq f q(HMod.hMod (α := Nat))


中文:
定义 evalNatMod
  签名: :
  定义体: do
  let .app (.app f (a : Q(Nat))) (b : Q(Nat)) ← whnfR e | failure
haveI' : u =QL 0 := ⟨⟩; haveI' : α =Q Nat := ⟨⟩
haveI' : e =Q a % b := ⟨⟩
  -- We assert that the default instance for `HMod` is `Nat.mod` when the first parameter is `ℕ`.
guard ← withNewMCtxDepth isDefEq f q(HMod.hMod (α := Nat))

-/
@[norm_num (_ : Nat) % _] def evalNatMod :
    NormNumExt where eval {u α} e := do
  let .app (.app f (a : Q(Nat))) (b : Q(Nat)) ← whnfR e | failure
haveI' : u =QL 0 := ⟨⟩; haveI' : α =Q Nat := ⟨⟩
haveI' : e =Q a % b := ⟨⟩
  -- We assert that the default instance for `HMod` is `Nat.mod` when the first parameter is `ℕ`.
guard ← withNewMCtxDepth isDefEq f q(HMod.hMod (α := Nat))
  let sNat : Q(AddMonoidWithOne Nat) := q(Nat.instAddMonoidWithOne)
  let ⟨na, pa⟩ ← deriveNat a sNat; let ⟨nb, pb⟩ ← deriveNat b sNat
  have nc : Q(Nat) := mkRawNatLit (na.natLit! % nb.natLit!)
haveI' : Nat.mod na nb =Q nc := ⟨⟩
  return .isNat sNat nc q(isNat_natMod $pa $pb (.refl $nc))

/--
theorem `isNat_natDiv` / 定理 `isNat_natDiv`

English:
theorem isNat_natDiv
  statement: {a b : Nat} -> {a' b' c : Nat} ->

中文:
定理 isNat_natDiv
  结论: {a b : 自然数} -> {a' b' c : 自然数} ->
-/
theorem isNat_natDiv : {a b : Nat} -> {a' b' c : Nat} ->
    IsNat a a' -> IsNat b b' -> Nat.div a' b' = c -> IsNat (a / b) c
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨by aesop⟩

/-- The `norm_num` extension which identifies expressions of the form `Nat.div a b`,
such that `norm_num` successfully recognises both `a` and `b`. -/
@[norm_num (_ : Nat) / _]
/--
Definition of `evalNatDiv` / `evalNatDiv` 的定义

English:
definition evalNatDiv
  signature: : NormNumExt where eval {u α} e
  body: do
  let .app (.app f (a : Q(Nat))) (b : Q(Nat)) ← whnfR e | failure
haveI' : u =QL 0 := ⟨⟩; haveI' : α =Q Nat := ⟨⟩
haveI' : e =Q a / b := ⟨⟩
  -- We assert that the default instance for `HDiv` is `Nat.div` when the first parameter is `ℕ`.
guard ← withNewMCtxDepth isDefEq f q(HDiv.hDiv (α := Nat))


中文:
定义 evalNatDiv
  签名: : NormNumExt where eval {u α} e
  定义体: do
  let .app (.app f (a : Q(Nat))) (b : Q(Nat)) ← whnfR e | failure
haveI' : u =QL 0 := ⟨⟩; haveI' : α =Q Nat := ⟨⟩
haveI' : e =Q a / b := ⟨⟩
  -- We assert that the default instance for `HDiv` is `Nat.div` when the first parameter is `ℕ`.
guard ← withNewMCtxDepth isDefEq f q(HDiv.hDiv (α := Nat))

-/
def evalNatDiv : NormNumExt where eval {u α} e := do
  let .app (.app f (a : Q(Nat))) (b : Q(Nat)) ← whnfR e | failure
haveI' : u =QL 0 := ⟨⟩; haveI' : α =Q Nat := ⟨⟩
haveI' : e =Q a / b := ⟨⟩
  -- We assert that the default instance for `HDiv` is `Nat.div` when the first parameter is `ℕ`.
guard ← withNewMCtxDepth isDefEq f q(HDiv.hDiv (α := Nat))
  let sNat : Q(AddMonoidWithOne Nat) := q(Nat.instAddMonoidWithOne)
  let ⟨na, pa⟩ ← deriveNat a sNat; let ⟨nb, pb⟩ ← deriveNat b sNat
  have nc : Q(Nat) := mkRawNatLit (na.natLit! / nb.natLit!)
haveI' : Nat.div na nb =Q nc := ⟨⟩
  return .isNat sNat nc q(isNat_natDiv $pa $pb (.refl $nc))

/--
theorem `isNat_dvd_true` / 定理 `isNat_dvd_true`

English:
theorem isNat_dvd_true
  statement: {a b : Nat} -> {a' b' : Nat} ->

中文:
定理 isNat_dvd_true
  结论: {a b : 自然数} -> {a' b' : 自然数} ->
-/
theorem isNat_dvd_true : {a b : Nat} -> {a' b' : Nat} ->
    IsNat a a' -> IsNat b b' -> Nat.mod b' a' = nat_lit 0 -> a ∣ b
  | _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, e => Nat.dvd_of_mod_eq_zero e

/--
theorem `isNat_dvd_false` / 定理 `isNat_dvd_false`

English:
theorem isNat_dvd_false
  statement: {a b : Nat} -> {a' b' c : Nat} ->

中文:
定理 isNat_dvd_false
  结论: {a b : 自然数} -> {a' b' c : 自然数} ->
-/
theorem isNat_dvd_false : {a b : Nat} -> {a' b' c : Nat} ->
    IsNat a a' -> IsNat b b' -> Nat.mod b' a' = Nat.succ c -> ¬a ∣ b
  | _, _, _, _, c, ⟨rfl⟩, ⟨rfl⟩, e => mt Nat.mod_eq_zero_of_dvd (e.symm ▸ Nat.succ_ne_zero c :)

/--
Definition of `evalNatDvd` / `evalNatDvd` 的定义

English:
definition evalNatDvd
  signature: : NormNumExt where eval {u α} e
  body: do
  let .app (.app f (a : Q(Nat))) (b : Q(Nat)) ← whnfR e | failure
  -- We assert that the default instance for `Dvd` is `Nat.dvd` when the first parameter is `ℕ`.
guard ← withNewMCtxDepth isDefEq f q(Dvd.dvd (α := Nat))
  let sNat : Q(AddMonoidWithOne Nat) := q(Nat.instAddMonoidWithOne)
  let ⟨na

中文:
定义 evalNatDvd
  签名: : NormNumExt where eval {u α} e
  定义体: do
  let .app (.app f (a : Q(Nat))) (b : Q(Nat)) ← whnfR e | failure
  -- We assert that the default instance for `Dvd` is `Nat.dvd` when the first parameter is `ℕ`.
guard ← withNewMCtxDepth isDefEq f q(Dvd.dvd (α := Nat))
  let sNat : Q(AddMonoidWithOne Nat) := q(Nat.instAddMonoidWithOne)
  let ⟨na
-/
@[norm_num (_ : Nat) ∣ _] def evalNatDvd : NormNumExt where eval {u α} e := do
  let .app (.app f (a : Q(Nat))) (b : Q(Nat)) ← whnfR e | failure
  -- We assert that the default instance for `Dvd` is `Nat.dvd` when the first parameter is `ℕ`.
guard ← withNewMCtxDepth isDefEq f q(Dvd.dvd (α := Nat))
  let sNat : Q(AddMonoidWithOne Nat) := q(Nat.instAddMonoidWithOne)
  let ⟨na, pa⟩ ← deriveNat a sNat; let ⟨nb, pb⟩ ← deriveNat b sNat
  match nb.natLit! % na.natLit! with
  | 0 =>
    have : Q(Nat.mod $nb $na = nat_lit 0) := (q(Eq.refl (nat_lit 0)) : Expr)
    return .isTrue q(isNat_dvd_true $pa $pb $this)
  | c+1 =>
    have nc : Q(Nat) := mkRawNatLit c
    have : Q(Nat.mod $nb $na = Nat.succ $nc) := (q(Eq.refl (Nat.succ $nc)) : Expr)
    return .isFalse q(isNat_dvd_false $pa $pb $this)

end

end Mathlib.Meta.NormNum
