/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.Tactic.NormNum.Basic

/-!
# `norm_num` plugins for `Rat.cast` and `⁻¹`.
-/

public meta section

variable {u : Lean.Level}

namespace Mathlib.Meta.NormNum

open Lean.Meta Qq

/--
Definition of `inferCharZeroOfRing` / `inferCharZeroOfRing` 的定义

English:
definition inferCharZeroOfRing
  signature: {α : Q(Type u)} (_i : Q(Ring $α) := by with_reducible assumption)
  body: return ← synthInstanceQ q(CharZero $α) >
    throwError "not a characteristic zero ring"

中文:
定义 inferCharZeroOfRing
  签名: {α : Q(类型u)} (_i : Q(环 $α) := by with_reducible assumption)
  定义体: return ← synthInstanceQ q(CharZero $α) >
    throwError "not a characteristic zero ring"

Depends on / 依赖: CharZero, characteristic, return, synthInstanceQ, throwError, with_reducible
-/
def inferCharZeroOfRing {α : Q(Type u)} (_i : Q(Ring $α) := by with_reducible assumption) :
    MetaM Q(CharZero $α) :=
return ← synthInstanceQ q(CharZero $α) >
    throwError "not a characteristic zero ring"

/--
Definition of `inferCharZeroOfRing?` / `inferCharZeroOfRing?` 的定义

English:
definition inferCharZeroOfRing?
  signature: {α : Q(Type u)} (_i : Q(Ring $α) := by with_reducible assumption)
  body: return (← trySynthInstanceQ q(CharZero $α)).toOption

中文:
定义 inferCharZeroOfRing?
  签名: {α : Q(类型u)} (_i : Q(环 $α) := by with_reducible assumption)
  定义体: return (← trySynthInstanceQ q(CharZero $α)).toOption
-/
def inferCharZeroOfRing? {α : Q(Type u)} (_i : Q(Ring $α) := by with_reducible assumption) :
    MetaM (Option Q(CharZero $α)) :=
  return (← trySynthInstanceQ q(CharZero $α)).toOption

/--
Definition of `inferCharZeroOfAddMonoidWithOne` / `inferCharZeroOfAddMonoidWithOne` 的定义

English:
definition inferCharZeroOfAddMonoidWithOne
  signature: {α : Q(Type u)}
  body: return ← synthInstanceQ q(CharZero $α) >
    throwError "not a characteristic zero AddMonoidWithOne"

中文:
定义 inferCharZeroOfAddMonoidWithOne
  签名: {α : Q(类型u)}
  定义体: return ← synthInstanceQ q(CharZero $α) >
    throwError "not a characteristic zero AddMonoidWithOne"

Depends on / 依赖: AddMonoidWithOne, CharZero, characteristic, return, synthInstanceQ, throwError, with_reducible
-/
def inferCharZeroOfAddMonoidWithOne {α : Q(Type u)}
    (_i : Q(AddMonoidWithOne $α) := by with_reducible assumption) : MetaM Q(CharZero $α) :=
return ← synthInstanceQ q(CharZero $α) >
    throwError "not a characteristic zero AddMonoidWithOne"

/--
Definition of `inferCharZeroOfAddMonoidWithOne?` / `inferCharZeroOfAddMonoidWithOne?` 的定义

English:
definition inferCharZeroOfAddMonoidWithOne?
  signature: {α : Q(Type u)}
  body: return (← trySynthInstanceQ q(CharZero $α)).toOption

中文:
定义 inferCharZeroOfAddMonoidWithOne?
  签名: {α : Q(类型u)}
  定义体: return (← trySynthInstanceQ q(CharZero $α)).toOption
-/
def inferCharZeroOfAddMonoidWithOne? {α : Q(Type u)}
    (_i : Q(AddMonoidWithOne $α) := by with_reducible assumption) :
      MetaM (Option Q(CharZero $α)) :=
  return (← trySynthInstanceQ q(CharZero $α)).toOption

/--
Definition of `inferCharZeroOfDivisionRing` / `inferCharZeroOfDivisionRing` 的定义

English:
definition inferCharZeroOfDivisionRing
  signature: {α : Q(Type u)}
  body: return ← synthInstanceQ q(CharZero $α) >
    throwError "not a characteristic zero division ring"

中文:
定义 inferCharZeroOfDivisionRing
  签名: {α : Q(类型u)}
  定义体: return ← synthInstanceQ q(CharZero $α) >
    throwError "not a characteristic zero division ring"

Depends on / 依赖: CharZero, characteristic, division, return, synthInstanceQ, throwError, with_reducible
-/
def inferCharZeroOfDivisionRing {α : Q(Type u)}
    (_i : Q(DivisionRing $α) := by with_reducible assumption) : MetaM Q(CharZero $α) :=
return ← synthInstanceQ q(CharZero $α) >
    throwError "not a characteristic zero division ring"

/--
Definition of `inferCharZeroOfDivisionSemiring?` / `inferCharZeroOfDivisionSemiring?` 的定义

English:
definition inferCharZeroOfDivisionSemiring?
  signature: {α : Q(Type u)}
  body: return (← trySynthInstanceQ (q(CharZero $α) : Q(Prop))).toOption

中文:
定义 inferCharZeroOfDivisionSemiring?
  签名: {α : Q(类型u)}
  定义体: return (← trySynthInstanceQ (q(CharZero $α) : Q(Prop))).toOption

Depends on / 依赖: CharZero, return, toOption, trySynthInstanceQ, with_reducible
-/
def inferCharZeroOfDivisionSemiring? {α : Q(Type u)}
    (_i : Q(DivisionSemiring $α) := by with_reducible assumption) : MetaM (Option Q(CharZero $α)) :=
  return (← trySynthInstanceQ (q(CharZero $α) : Q(Prop))).toOption

/--
Definition of `inferCharZeroOfDivisionRing?` / `inferCharZeroOfDivisionRing?` 的定义

English:
definition inferCharZeroOfDivisionRing?
  signature: {α : Q(Type u)}
  body: return (← trySynthInstanceQ q(CharZero $α)).toOption

中文:
定义 inferCharZeroOfDivisionRing?
  签名: {α : Q(类型u)}
  定义体: return (← trySynthInstanceQ q(CharZero $α)).toOption
-/
def inferCharZeroOfDivisionRing? {α : Q(Type u)}
    (_i : Q(DivisionRing $α) := by with_reducible assumption) : MetaM (Option Q(CharZero $α)) :=
  return (← trySynthInstanceQ q(CharZero $α)).toOption

/--
theorem `isRat_mkRat` / 定理 `isRat_mkRat`

English:
theorem isRat_mkRat
  statement: {a na n : Int} -> {b nb d : Nat} -> IsInt a na -> IsNat b nb ->

中文:
定理 isRat_mkRat
  结论: {a na n : 整数} -> {b nb d : 自然数} -> 是整数 a na -> 是自然数 b nb ->
-/
theorem isRat_mkRat : {a na n : Int} -> {b nb d : Nat} -> IsInt a na -> IsNat b nb ->
    IsRat (na / nb : Rat) n d -> IsRat (mkRat a b) n d
  | _, _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, ⟨_, h⟩ => by rw [Rat.mkRat_eq_div]; exact ⟨_, h⟩

/--
theorem `isNNRat_divNat` / 定理 `isNNRat_divNat`

English:
theorem isNNRat_divNat
  statement: {a na n : Nat} -> {b nb d : Nat} -> IsNat a na -> IsNat b nb ->

中文:
定理 isNNRat_div自然数
  结论: {a na n : 自然数} -> {b nb d : 自然数} -> 是自然数 a na -> 是自然数 b nb ->
-/
theorem isNNRat_divNat : {a na n : Nat} -> {b nb d : Nat} -> IsNat a na -> IsNat b nb ->
    IsNNRat (na / nb : Rat>=0) n d -> IsNNRat (NNRat.divNat a b) n d
  | _, _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, ⟨_, h⟩ => by rw [NNRat.divNat_eq_div]; exact ⟨_, h⟩

attribute [local instance] monadLiftOptionMetaM in
/-- The `norm_num` extension which identifies expressions of the form `mkRat a b`,
such that `norm_num` successfully recognises both `a` and `b`, and returns `a / b`. -/
@[norm_num mkRat _ _]
/--
Definition of `evalMkRat` / `evalMkRat` 的定义

English:
definition evalMkRat
  signature: : NormNumExt where eval {u α} (e : Q(Rat)) : MetaM (Result e)
  body: do
  let .app (.app (.const ``mkRat _) (a : Q(Int))) (b : Q(Nat)) ← whnfR e | failure
haveI' : e =Q mkRat a b := ⟨⟩
  let ra ← derive a
  let some ⟨_, na, pa⟩ := ra.toInt (q(Int.instRing) : Q(Ring Int)) | failure
  let ⟨nb, pb⟩ ← deriveNat q($b) q(AddCommMonoidWithOne.toAddMonoidWithOne)
  let rab ←

中文:
定义 evalMkRat
  签名: : NormNumExt where eval {u α} (e : Q(有理数)) : MetaM (Result e)
  定义体: do
  let .app (.app (.const ``mkRat _) (a : Q(Int))) (b : Q(Nat)) ← whnfR e | failure
haveI' : e =Q mkRat a b := ⟨⟩
  let ra ← derive a
  let some ⟨_, na, pa⟩ := ra.toInt (q(Int.instRing) : Q(Ring Int)) | failure
  let ⟨nb, pb⟩ ← deriveNat q($b) q(AddCommMonoidWithOne.toAddMonoidWithOne)
  let rab ←
-/
def evalMkRat : NormNumExt where eval {u α} (e : Q(Rat)) : MetaM (Result e) := do
  let .app (.app (.const ``mkRat _) (a : Q(Int))) (b : Q(Nat)) ← whnfR e | failure
haveI' : e =Q mkRat a b := ⟨⟩
  let ra ← derive a
  let some ⟨_, na, pa⟩ := ra.toInt (q(Int.instRing) : Q(Ring Int)) | failure
  let ⟨nb, pb⟩ ← deriveNat q($b) q(AddCommMonoidWithOne.toAddMonoidWithOne)
  let rab ← derive q($na / $nb : Rat)
  let ⟨q, n, d, p⟩ ← rab.toRat' q(Rat.instDivisionRing)
  return .isRat _ q n d q(isRat_mkRat $pa $pb $p)

/-- The `norm_num` extension which identifies expressions of the form `NNRat.divNat a b`,
such that `norm_num` successfully recognises both `a` and `b`, and returns `a / b`. -/
@[norm_num NNRat.divNat _ _]
/--
Definition of `evalNNRatDivNat` / `evalNNRatDivNat` 的定义

English:
definition evalNNRatDivNat
  signature: : NormNumExt where eval {u α} (e : Q(Rat>=0)) : MetaM (Result e)
  body: do
  let .app (.app (.const ``NNRat.divNat _) (a : Q(Nat))) (b : Q(Nat)) ← whnfR e | failure
haveI' : e =Q NNRat.divNat a b := ⟨⟩
  let ra ← derive q($a)
  let ⟨na, pa⟩ ← deriveNat q($a) q(AddCommMonoidWithOne.toAddMonoidWithOne)
  let ⟨nb, pb⟩ ← deriveNat q($b) q(AddCommMonoidWithOne.toAddMonoidWit

中文:
定义 evalNNRatDiv自然数
  签名: : NormNumExt where eval {u α} (e : Q(有理数>=0)) : MetaM (Result e)
  定义体: do
  let .app (.app (.const ``NNRat.divNat _) (a : Q(Nat))) (b : Q(Nat)) ← whnfR e | failure
haveI' : e =Q NNRat.divNat a b := ⟨⟩
  let ra ← derive q($a)
  let ⟨na, pa⟩ ← deriveNat q($a) q(AddCommMonoidWithOne.toAddMonoidWithOne)
  let ⟨nb, pb⟩ ← deriveNat q($b) q(AddCommMonoidWithOne.toAddMonoidWit
-/
def evalNNRatDivNat : NormNumExt where eval {u α} (e : Q(Rat>=0)) : MetaM (Result e) := do
  let .app (.app (.const ``NNRat.divNat _) (a : Q(Nat))) (b : Q(Nat)) ← whnfR e | failure
haveI' : e =Q NNRat.divNat a b := ⟨⟩
  let ra ← derive q($a)
  let ⟨na, pa⟩ ← deriveNat q($a) q(AddCommMonoidWithOne.toAddMonoidWithOne)
  let ⟨nb, pb⟩ ← deriveNat q($b) q(AddCommMonoidWithOne.toAddMonoidWithOne)
  let rab ← derive q($na / $nb : NNRat)
  let some ⟨q, n, d, p⟩ := rab.toNNRat' q(NNRat.instSemifield.toDivisionSemiring) | failure
  return .isNNRat _ q n d q(isNNRat_divNat $pa $pb $p)

/--
theorem `isNat_ratCast` / 定理 `isNat_ratCast`

English:
theorem isNat_ratCast
  given: {R : Type*} [DivisionRing R]
  statement: {q : Rat} -> {n : Nat} ->

中文:
定理 is自然数_ratCast
  条件: {R : 类型} [除环 R]
  结论: {q : 有理数} -> {n : 自然数} ->
-/
theorem isNat_ratCast {R : Type*} [DivisionRing R] : {q : Rat} -> {n : Nat} ->
    IsNat q n -> IsNat (q : R) n
  | _, _, ⟨rfl⟩ => ⟨by simp⟩

/--
theorem `isNat_nnratCast` / 定理 `isNat_nnratCast`

English:
theorem isNat_nnratCast
  given: {R : Type*} [DivisionSemiring R]
  statement: {q : Rat>=0} -> {n : Nat} ->

中文:
定理 is自然数_nnratCast
  条件: {R : 类型} [除半环 R]
  结论: {q : 有理数>=0} -> {n : 自然数} ->
-/
theorem isNat_nnratCast {R : Type*} [DivisionSemiring R] : {q : Rat>=0} -> {n : Nat} ->
    IsNat q n -> IsNat (q : R) n
  | _, _, ⟨rfl⟩ => ⟨by simp⟩

/--
theorem `isInt_ratCast` / 定理 `isInt_ratCast`

English:
theorem isInt_ratCast
  given: {R : Type*} [DivisionRing R]
  statement: {q : Rat} -> {n : Int} ->

中文:
定理 is整数_ratCast
  条件: {R : 类型} [除环 R]
  结论: {q : 有理数} -> {n : 整数} ->
-/
theorem isInt_ratCast {R : Type*} [DivisionRing R] : {q : Rat} -> {n : Int} ->
    IsInt q n -> IsInt (q : R) n
  | _, _, ⟨rfl⟩ => ⟨by simp⟩

/--
theorem `isNNRat_ratCast` / 定理 `isNNRat_ratCast`

English:
theorem isNNRat_ratCast
  given: {R : Type*} [DivisionRing R] [CharZero R]
  statement: {q : Rat} -> {n : Nat} -> {d : Nat} ->

中文:
定理 isNNRat_ratCast
  条件: {R : 类型} [除环 R] [特征零 R]
  结论: {q : 有理数} -> {n : 自然数} -> {d : 自然数} ->
-/
theorem isNNRat_ratCast {R : Type*} [DivisionRing R] [CharZero R] : {q : Rat} -> {n : Nat} -> {d : Nat} ->
    IsNNRat q n d -> IsNNRat (q : R) n d
  | _, _, _, ⟨⟨qi,_,_⟩, rfl⟩ => ⟨⟨qi, by norm_cast, by norm_cast⟩, by simp only; norm_cast⟩

/--
theorem `isNNRat_nnratCast` / 定理 `isNNRat_nnratCast`

English:
theorem isNNRat_nnratCast
  given: {R : Type*} [DivisionSemiring R] [CharZero R]
  statement: {q : Rat>=0} -> {n : Nat} ->

中文:
定理 isNNRat_nnratCast
  条件: {R : 类型} [除半环 R] [特征零 R]
  结论: {q : 有理数>=0} -> {n : 自然数} ->
-/
theorem isNNRat_nnratCast {R : Type*} [DivisionSemiring R] [CharZero R] : {q : Rat>=0} -> {n : Nat} ->
    {d : Nat} -> IsNNRat q n d -> IsNNRat (q : R) n d
  | _, _, _, ⟨⟨qi,_,_⟩, rfl⟩ => ⟨⟨qi, by norm_cast, by norm_cast⟩, by simp only; norm_cast⟩

/--
theorem `isRat_ratCast` / 定理 `isRat_ratCast`

English:
theorem isRat_ratCast
  given: {R : Type*} [DivisionRing R] [CharZero R]
  statement: {q : Rat} -> {n : Int} -> {d : Nat} ->

中文:
定理 isRat_ratCast
  条件: {R : 类型} [除环 R] [特征零 R]
  结论: {q : 有理数} -> {n : 整数} -> {d : 自然数} ->

Depends on / 依赖: DiscreteTopology, DiscreteTopology.toT2Space, toT2Space
-/
theorem isRat_ratCast {R : Type*} [DivisionRing R] [CharZero R] : {q : Rat} -> {n : Int} -> {d : Nat} ->
    IsRat q n d -> IsRat (q : R) n d
  | _, _, _, ⟨⟨qi,_,_⟩, rfl⟩ => ⟨⟨qi, by norm_cast, by norm_cast⟩, by simp only; norm_cast⟩

/--
Definition of `evalRatCast` / `evalRatCast` 的定义

English:
definition evalRatCast
  signature: : NormNumExt where eval {u α} e
  body: do
  let dα ← inferDivisionRing α
  let .app r (a : Q(Rat)) ← whnfR e | failure
guard ← withNewMCtxDepth isDefEq r q(Rat.cast (K := $α))
  let r ← derive q($a)
haveI' : e =Q Rat.cast a := ⟨⟩
  match r with
  | .isNat _ na pa =>
    assumeInstancesCommute
    return .isNat _ na q(isNat_ratCast $pa)
 

中文:
定义 evalRatCast
  签名: : NormNumExt where eval {u α} e
  定义体: do
  let dα ← inferDivisionRing α
  let .app r (a : Q(Rat)) ← whnfR e | failure
guard ← withNewMCtxDepth isDefEq r q(Rat.cast (K := $α))
  let r ← derive q($a)
haveI' : e =Q Rat.cast a := ⟨⟩
  match r with
  | .isNat _ na pa =>
    assumeInstancesCommute
    return .isNat _ na q(isNat_ratCast $pa)
 
-/
@[norm_num Rat.cast _, RatCast.ratCast _] def evalRatCast : NormNumExt where eval {u α} e := do
  let dα ← inferDivisionRing α
  let .app r (a : Q(Rat)) ← whnfR e | failure
guard ← withNewMCtxDepth isDefEq r q(Rat.cast (K := $α))
  let r ← derive q($a)
haveI' : e =Q Rat.cast a := ⟨⟩
  match r with
  | .isNat _ na pa =>
    assumeInstancesCommute
    return .isNat _ na q(isNat_ratCast $pa)
  | .isNegNat _ na pa =>
    assumeInstancesCommute
    return .isNegNat _ na q(isInt_ratCast $pa)
  | .isNNRat _ qa na da pa =>
    assumeInstancesCommute
    let i ← inferCharZeroOfDivisionRing dα
    return .isNNRat q(inferInstance) qa na da q(isNNRat_ratCast $pa)
  | .isNegNNRat _ qa na da pa =>
    assumeInstancesCommute
    let i ← inferCharZeroOfDivisionRing dα
    return .isNegNNRat dα qa na da q(isRat_ratCast $pa)
  | _ => failure

/-- The `norm_num` extension which identifies an expression `NNRat.cast q` where `norm_num`
recognizes `q`, returning the cast of `q`. -/
@[norm_num NNRat.cast _, NNRatCast.nnratCast _]
/--
Definition of `evalNNRatCast` / `evalNNRatCast` 的定义

English:
definition evalNNRatCast
  signature: : NormNumExt where eval {u α} e
  body: do
  let dα ← inferDivisionSemiring α
  let ~q(@NNRat.cast _ $dα' $a) := e | failure
guard ← matchesInstance dα' q(@DivisionSemiring.toNNRatCast _ $dα)
  match ← derive q($a) with
  | .isNat _ na pa =>
    assumeInstancesCommute
    return .isNat _ na q(isNat_nnratCast $pa)
  | .isNNRat _ qa na da p

中文:
定义 evalNNRatCast
  签名: : NormNumExt where eval {u α} e
  定义体: do
  let dα ← inferDivisionSemiring α
  let ~q(@NNRat.cast _ $dα' $a) := e | failure
guard ← matchesInstance dα' q(@DivisionSemiring.toNNRatCast _ $dα)
  match ← derive q($a) with
  | .isNat _ na pa =>
    assumeInstancesCommute
    return .isNat _ na q(isNat_nnratCast $pa)
  | .isNNRat _ qa na da p
-/
def evalNNRatCast : NormNumExt where eval {u α} e := do
  let dα ← inferDivisionSemiring α
  let ~q(@NNRat.cast _ $dα' $a) := e | failure
guard ← matchesInstance dα' q(@DivisionSemiring.toNNRatCast _ $dα)
  match ← derive q($a) with
  | .isNat _ na pa =>
    assumeInstancesCommute
    return .isNat _ na q(isNat_nnratCast $pa)
  | .isNNRat _ qa na da pa =>
    assumeInstancesCommute
    let some _ ← inferCharZeroOfDivisionSemiring? dα | failure
    return .isNNRat q(inferInstance) qa na da q(isNNRat_nnratCast $pa)
  | _ => failure

/--
theorem `isNNRat_inv_pos` / 定理 `isNNRat_inv_pos`

English:
theorem isNNRat_inv_pos
  given: {α} [DivisionSemiring α] [CharZero α] {a : α} {n d : Nat}
  proof: by
  rintro ⟨_, rfl⟩
  have := invertibleOfNonzero (α := α) (Nat.cast_ne_zero.2 (Nat.succ_ne_zero n))
  exact ⟨this, by simp⟩

中文:
定理 isNNRat_inv_pos
  条件: {α} [除半环 α] [特征零 α] {a : α} {n d : 自然数}
  证明: by
  rintro ⟨_, rfl⟩
  have := invertibleOfNonzero (α := α) (Nat.cast_ne_zero.2 (Nat.succ_ne_zero n))
  exact ⟨this, by simp⟩

Depends on / 依赖: Nat.cast_ne_zero, Nat.succ_ne_zero, cast_ne_zero, invertibleOfNonzero, succ_ne_zero
-/
theorem isNNRat_inv_pos {α} [DivisionSemiring α] [CharZero α] {a : α} {n d : Nat} :
    IsNNRat a (Nat.succ n) d -> IsNNRat a⁻¹ d (Nat.succ n) := by
  rintro ⟨_, rfl⟩
  have := invertibleOfNonzero (α := α) (Nat.cast_ne_zero.2 (Nat.succ_ne_zero n))
  exact ⟨this, by simp⟩

/--
theorem `isRat_inv_pos` / 定理 `isRat_inv_pos`

English:
theorem isRat_inv_pos
  given: {α} [DivisionRing α] [CharZero α] {a : α} {n d : Nat}
  proof: by
  rintro ⟨_, rfl⟩
  have := invertibleOfNonzero (α := α) (Nat.cast_ne_zero.2 (Nat.succ_ne_zero n))
  exact ⟨this, by simp⟩

中文:
定理 isRat_inv_pos
  条件: {α} [除环 α] [特征零 α] {a : α} {n d : 自然数}
  证明: by
  rintro ⟨_, rfl⟩
  have := invertibleOfNonzero (α := α) (Nat.cast_ne_zero.2 (Nat.succ_ne_zero n))
  exact ⟨this, by simp⟩

Depends on / 依赖: Nat.cast_ne_zero, Nat.succ_ne_zero, cast_ne_zero, invertibleOfNonzero, succ_ne_zero
-/
theorem isRat_inv_pos {α} [DivisionRing α] [CharZero α] {a : α} {n d : Nat} :
    IsRat a (.ofNat (Nat.succ n)) d -> IsRat a⁻¹ (.ofNat d) (Nat.succ n) := by
  rintro ⟨_, rfl⟩
  have := invertibleOfNonzero (α := α) (Nat.cast_ne_zero.2 (Nat.succ_ne_zero n))
  exact ⟨this, by simp⟩

/--
theorem `isNat_inv_one` / 定理 `isNat_inv_one`

English:
theorem isNat_inv_one
  given: {α} [DivisionSemiring α]
  statement: {a : α} ->

中文:
定理 is自然数_inv_one
  条件: {α} [除半环 α]
  结论: {a : α} ->
-/
theorem isNat_inv_one {α} [DivisionSemiring α] : {a : α} ->
    IsNat a (nat_lit 1) -> IsNat a⁻¹ (nat_lit 1)
  | _, ⟨rfl⟩ => ⟨by simp⟩

/--
theorem `isNat_inv_zero` / 定理 `isNat_inv_zero`

English:
theorem isNat_inv_zero
  given: {α} [DivisionSemiring α]
  statement: {a : α} ->

中文:
定理 is自然数_inv_zero
  条件: {α} [除半环 α]
  结论: {a : α} ->
-/
theorem isNat_inv_zero {α} [DivisionSemiring α] : {a : α} ->
    IsNat a (nat_lit 0) -> IsNat a⁻¹ (nat_lit 0)
  | _, ⟨rfl⟩ => ⟨by simp⟩

/--
theorem `isInt_inv_neg_one` / 定理 `isInt_inv_neg_one`

English:
theorem isInt_inv_neg_one
  given: {α} [DivisionRing α]
  statement: {a : α} ->

中文:
定理 is整数_inv_neg_one
  条件: {α} [除环 α]
  结论: {a : α} ->
-/
theorem isInt_inv_neg_one {α} [DivisionRing α] : {a : α} ->
    IsInt a (.negOfNat (nat_lit 1)) -> IsInt a⁻¹ (.negOfNat (nat_lit 1))
  | _, ⟨rfl⟩ => ⟨by simp⟩

/--
theorem `isRat_inv_neg` / 定理 `isRat_inv_neg`

English:
theorem isRat_inv_neg
  given: {α} [DivisionRing α] [CharZero α] {a : α} {n d : Nat}
  proof: by
  rintro ⟨_, rfl⟩
  simp only [Int.negOfNat_eq]
  have := invertibleOfNonzero (α := α) (Nat.cast_ne_zero.2 (Nat.succ_ne_zero n))
  generalize Nat.succ n = n at *
  use this; simp only [Int.ofNat_eq_natCast, Int.cast_neg,
    Int.cast_natCast, invOf_eq_inv, inv_neg, neg_mul, mul_inv_rev, inv_inv]

中文:
定理 isRat_inv_neg
  条件: {α} [除环 α] [特征零 α] {a : α} {n d : 自然数}
  证明: by
  rintro ⟨_, rfl⟩
  simp only [Int.negOfNat_eq]
  have := invertibleOfNonzero (α := α) (Nat.cast_ne_zero.2 (Nat.succ_ne_zero n))
  generalize Nat.succ n = n at *
  use this; simp only [Int.ofNat_eq_natCast, Int.cast_neg,
    Int.cast_natCast, invOf_eq_inv, inv_neg, neg_mul, mul_inv_rev, inv_inv]

Depends on / 依赖: Int.cast_natCast, Int.cast_neg, Int.negOfNat_eq, Int.ofNat_eq_natCast, Nat.cast_ne_zero, Nat.succ, Nat.succ_ne_zero, cast_natCast, cast_ne_zero, cast_neg, generalize, invOf_eq_inv, inv_inv, inv_neg, invertibleOfNonzero, mul_inv_rev, negOfNat_eq, neg_mul, ofNat_eq_natCast, succ_ne_zero
-/
theorem isRat_inv_neg {α} [DivisionRing α] [CharZero α] {a : α} {n d : Nat} :
    IsRat a (.negOfNat (Nat.succ n)) d -> IsRat a⁻¹ (.negOfNat d) (Nat.succ n) := by
  rintro ⟨_, rfl⟩
  simp only [Int.negOfNat_eq]
  have := invertibleOfNonzero (α := α) (Nat.cast_ne_zero.2 (Nat.succ_ne_zero n))
  generalize Nat.succ n = n at *
  use this; simp only [Int.ofNat_eq_natCast, Int.cast_neg,
    Int.cast_natCast, invOf_eq_inv, inv_neg, neg_mul, mul_inv_rev, inv_inv]

open Lean

attribute [local instance] monadLiftOptionMetaM in
/--
Definition of `Result.inv` / `Result.inv` 的定义

English:
definition Result.inv
  signature: {u : Level} {α : Q(Type u)} {a : Q($α)} (ra : Result a)
  body: do
  if let .some ⟨qa, na, da, pa⟩ := ra.toNNRat' dsα then
    let qb := qa⁻¹
    if qa > 0 then
      if let some _i := czα? then
        have lit2 : Q(Nat) := mkRawNatLit (na.natLit! - 1)
haveI : na =Q ($lit2).succ := ⟨⟩
        return .isNNRat' dsα qb q($da) q($na) q(isNNRat_inv_pos $pa)
      el

中文:
定义 Result.inv
  签名: {u : Level} {α : Q(类型u)} {a : Q($α)} (ra : Result a)
  定义体: do
  if let .some ⟨qa, na, da, pa⟩ := ra.toNNRat' dsα then
    let qb := qa⁻¹
    if qa > 0 then
      if let some _i := czα? then
        have lit2 : Q(Nat) := mkRawNatLit (na.natLit! - 1)
haveI : na =Q ($lit2).succ := ⟨⟩
        return .isNNRat' dsα qb q($da) q($na) q(isNNRat_inv_pos $pa)
      el
-/
def Result.inv {u : Level} {α : Q(Type u)} {a : Q($α)} (ra : Result a)
    (dsα : Q(DivisionSemiring $α)) (czα? : Option Q(CharZero $α)) :
    MetaM (Result q($a⁻¹)) := do
  if let .some ⟨qa, na, da, pa⟩ := ra.toNNRat' dsα then
    let qb := qa⁻¹
    if qa > 0 then
      if let some _i := czα? then
        have lit2 : Q(Nat) := mkRawNatLit (na.natLit! - 1)
haveI : na =Q ($lit2).succ := ⟨⟩
        return .isNNRat' dsα qb q($da) q($na) q(isNNRat_inv_pos $pa)
      else
        guard (qa = 1)
        let .isNat inst n pa := ra | failure
haveI' : n =Q nat_lit 1 := ⟨⟩
        assumeInstancesCommute
        return .isNat inst n q(isNat_inv_one $pa)
    else
      let .isNat inst n pa := ra | failure
haveI' : n =Q nat_lit 0 := ⟨⟩
      assumeInstancesCommute
      return .isNat inst n q(isNat_inv_zero $pa)
  else
    let dα ← inferDivisionRing α
    assertInstancesCommute
    let ⟨qa, na, da, pa⟩ ← ra.toRat' dα
    let qb := qa⁻¹
guard qa < 0
    if let some _i := czα? then
      have lit : Q(Nat) := na.appArg!
haveI : na =Q Int.negOfNat lit := ⟨⟩
      have lit2 : Q(Nat) := mkRawNatLit (lit.natLit! - 1)
haveI : lit =Q ($lit2).succ := ⟨⟩
      return .isRat dα qb q(.negOfNat $da) lit q(isRat_inv_neg $pa)
    else
      guard (qa = -1)
      let .isNegNat inst n pa := ra | failure
haveI' : n =Q nat_lit 1 := ⟨⟩
      assumeInstancesCommute
      return .isNegNat inst n q(isInt_inv_neg_one $pa)

/--
Definition of `evalInv` / `evalInv` 的定义

English:
definition evalInv
  signature: : NormNumExt where eval {u α} e
  body: do
  let .app f (a : Q($α)) ← whnfR e | failure
  let ra ← derive a
  let dsα ← inferDivisionSemiring α
guard ← withNewMCtxDepth isDefEq f q(Inv.inv (α := $α))
haveI' : e =Q a⁻¹ := ⟨⟩
  assumeInstancesCommute
  ra.inv q($dsα) (← inferCharZeroOfDivisionSemiring? dsα)

中文:
定义 evalInv
  签名: : NormNumExt where eval {u α} e
  定义体: do
  let .app f (a : Q($α)) ← whnfR e | failure
  let ra ← derive a
  let dsα ← inferDivisionSemiring α
guard ← withNewMCtxDepth isDefEq f q(Inv.inv (α := $α))
haveI' : e =Q a⁻¹ := ⟨⟩
  assumeInstancesCommute
  ra.inv q($dsα) (← inferCharZeroOfDivisionSemiring? dsα)
-/
@[norm_num _⁻¹] def evalInv : NormNumExt where eval {u α} e := do
  let .app f (a : Q($α)) ← whnfR e | failure
  let ra ← derive a
  let dsα ← inferDivisionSemiring α
guard ← withNewMCtxDepth isDefEq f q(Inv.inv (α := $α))
haveI' : e =Q a⁻¹ := ⟨⟩
  assumeInstancesCommute
  ra.inv q($dsα) (← inferCharZeroOfDivisionSemiring? dsα)

end Mathlib.Meta.NormNum
