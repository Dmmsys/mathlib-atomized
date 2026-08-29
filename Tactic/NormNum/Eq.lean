/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Tactic.NormNum.Inv

/-!
# `norm_num` extension for equalities
-/

public meta section

variable {α : Type*}

open Lean Meta Qq

namespace Mathlib.Meta.NormNum

/--
theorem `isNat_eq_false` / 定理 `isNat_eq_false`

English:
theorem isNat_eq_false
  given: [AddMonoidWithOne α] [CharZero α]
  statement: {a b : α} -> {a' b' : Nat} ->

中文:
定理 is自然数_eq_false
  条件: [加法带幺幺半群 α] [特征零 α]
  结论: {a b : α} -> {a' b' : 自然数} ->
-/
theorem isNat_eq_false [AddMonoidWithOne α] [CharZero α] : {a b : α} -> {a' b' : Nat} ->
    IsNat a a' -> IsNat b b' -> Nat.beq a' b' = false -> ¬a = b
  | _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, h => by simpa using Nat.ne_of_beq_eq_false h

/--
theorem `isInt_eq_false` / 定理 `isInt_eq_false`

English:
theorem isInt_eq_false
  given: [Ring α] [CharZero α]
  statement: {a b : α} -> {a' b' : Int} ->

中文:
定理 is整数_eq_false
  条件: [环 α] [特征零 α]
  结论: {a b : α} -> {a' b' : 整数} ->

Depends on / 依赖: TotallyDisconnectedSpace, TotallyDisconnectedSpace.t1Space, t1Space
-/
theorem isInt_eq_false [Ring α] [CharZero α] : {a b : α} -> {a' b' : Int} ->
    IsInt a a' -> IsInt b b' -> decide (a' = b') = false -> ¬a = b
  | _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, h => by simpa using of_decide_eq_false h

/--
theorem `NNRat.invOf_denom_swap` / 定理 `NNRat.invOf_denom_swap`

English:
theorem NNRat.invOf_denom_swap
  statement: [Semiring α] (n₁ n₂ : Nat) (a₁ a₂ : α)
  proof: by
  rw [mul_invOf_eq_iff_eq_mul_right]; rw [← Nat.commute_cast]; rw [mul_assoc]; rw [← mul_left_eq_iff_eq_invOf_mul]; rw [Nat.commute_cast]

中文:
定理 NNRat.invOf_denom_swap
  结论: [半环 α] (n₁ n₂ : 自然数) (a₁ a₂ : α)
  证明: by
  rw [mul_invOf_eq_iff_eq_mul_right]; rw [← Nat.commute_cast]; rw [mul_assoc]; rw [← mul_left_eq_iff_eq_invOf_mul]; rw [Nat.commute_cast]

Depends on / 依赖: Nat.commute_cast, commute_cast, mul_assoc, mul_invOf_eq_iff_eq_mul_right, mul_left_eq_iff_eq_invOf_mul
-/
theorem NNRat.invOf_denom_swap [Semiring α] (n₁ n₂ : Nat) (a₁ a₂ : α)
    [Invertible a₁] [Invertible a₂] : n₁ * ⅟a₁ = n₂ * ⅟a₂ ↔ n₁ * a₂ = n₂ * a₁ := by
  rw [mul_invOf_eq_iff_eq_mul_right]; rw [← Nat.commute_cast]; rw [mul_assoc]; rw [← mul_left_eq_iff_eq_invOf_mul]; rw [Nat.commute_cast]

/--
theorem `isNNRat_eq_false` / 定理 `isNNRat_eq_false`

English:
theorem isNNRat_eq_false
  given: [Semiring α] [CharZero α]
  statement: {a b : α} -> {na nb : Nat} -> {da db : Nat} ->

中文:
定理 isNNRat_eq_false
  条件: [半环 α] [特征零 α]
  结论: {a b : α} -> {na nb : 自然数} -> {da db : 自然数} ->
-/
theorem isNNRat_eq_false [Semiring α] [CharZero α] : {a b : α} -> {na nb : Nat} -> {da db : Nat} ->
    IsNNRat a na da -> IsNNRat b nb db ->
    decide (Nat.mul na db = Nat.mul nb da) = false -> ¬a = b
  | _, _, _, _, _, _, ⟨_, rfl⟩, ⟨_, rfl⟩, h => by
    rw [NNRat.invOf_denom_swap]; exact mod_cast of_decide_eq_false h

/--
theorem `Rat.invOf_denom_swap` / 定理 `Rat.invOf_denom_swap`

English:
theorem Rat.invOf_denom_swap
  statement: [Ring α] (n₁ n₂ : Int) (a₁ a₂ : α)
  proof: by
  rw [mul_invOf_eq_iff_eq_mul_right]; rw [← Int.commute_cast]; rw [mul_assoc]; rw [← mul_left_eq_iff_eq_invOf_mul]; rw [Int.commute_cast]

中文:
定理 有理数.invOf_denom_swap
  结论: [环 α] (n₁ n₂ : 整数) (a₁ a₂ : α)
  证明: by
  rw [mul_invOf_eq_iff_eq_mul_right]; rw [← Int.commute_cast]; rw [mul_assoc]; rw [← mul_left_eq_iff_eq_invOf_mul]; rw [Int.commute_cast]

Depends on / 依赖: Int.commute_cast, commute_cast, mul_assoc, mul_invOf_eq_iff_eq_mul_right, mul_left_eq_iff_eq_invOf_mul
-/
theorem Rat.invOf_denom_swap [Ring α] (n₁ n₂ : Int) (a₁ a₂ : α)
    [Invertible a₁] [Invertible a₂] : n₁ * ⅟a₁ = n₂ * ⅟a₂ ↔ n₁ * a₂ = n₂ * a₁ := by
  rw [mul_invOf_eq_iff_eq_mul_right]; rw [← Int.commute_cast]; rw [mul_assoc]; rw [← mul_left_eq_iff_eq_invOf_mul]; rw [Int.commute_cast]

/--
theorem `isRat_eq_false` / 定理 `isRat_eq_false`

English:
theorem isRat_eq_false
  given: [Ring α] [CharZero α]
  statement: {a b : α} -> {na nb : Int} -> {da db : Nat} ->

中文:
定理 isRat_eq_false
  条件: [环 α] [特征零 α]
  结论: {a b : α} -> {na nb : 整数} -> {da db : 自然数} ->
-/
theorem isRat_eq_false [Ring α] [CharZero α] : {a b : α} -> {na nb : Int} -> {da db : Nat} ->
    IsRat a na da -> IsRat b nb db ->
    decide (Int.mul na (.ofNat db) = Int.mul nb (.ofNat da)) = false -> ¬a = b
  | _, _, _, _, _, _, ⟨_, rfl⟩, ⟨_, rfl⟩, h => by
    rw [Rat.invOf_denom_swap]; exact mod_cast of_decide_eq_false h

attribute [local instance] monadLiftOptionMetaM in
/--
Definition of `evalEq` / `evalEq` 的定义

English:
definition evalEq
  signature: : NormNumExt where eval {v β} e
  body: do
haveI' : v =QL 0 := ⟨⟩; haveI' : β =Q Prop := ⟨⟩
  let .app (.app f a) b ← whnfR e | failure
  let ⟨u, α, a⟩ ← inferTypeQ' a
  have b : Q($α) := b
haveI' : e =Q ($a = $b) := ⟨⟩
guard ← withNewMCtxDepth isDefEq f q(Eq (α := $α))
  let ra ← derive a; let rb ← derive b
  let rec intArm (rα : Q(Ring 

中文:
定义 evalEq
  签名: : NormNumExt where eval {v β} e
  定义体: do
haveI' : v =QL 0 := ⟨⟩; haveI' : β =Q Prop := ⟨⟩
  let .app (.app f a) b ← whnfR e | failure
  let ⟨u, α, a⟩ ← inferTypeQ' a
  have b : Q($α) := b
haveI' : e =Q ($a = $b) := ⟨⟩
guard ← withNewMCtxDepth isDefEq f q(Eq (α := $α))
  let ra ← derive a; let rb ← derive b
  let rec intArm (rα : Q(Ring 

Depends on / 依赖: ConnectedSpace, ConnectedSpace.neBot_nhdsWithin_compl_of_nontrivial_of_t1space, neBot_nhdsWithin_compl_of_nontrivial_of_t1space
-/
@[norm_num _ = _] def evalEq : NormNumExt where eval {v β} e := do
haveI' : v =QL 0 := ⟨⟩; haveI' : β =Q Prop := ⟨⟩
  let .app (.app f a) b ← whnfR e | failure
  let ⟨u, α, a⟩ ← inferTypeQ' a
  have b : Q($α) := b
haveI' : e =Q ($a = $b) := ⟨⟩
guard ← withNewMCtxDepth isDefEq f q(Eq (α := $α))
  let ra ← derive a; let rb ← derive b
  let rec intArm (rα : Q(Ring $α)) := do
    let ⟨za, na, pa⟩ ← ra.toInt rα; let ⟨zb, nb, pb⟩ ← rb.toInt rα
    if za = zb then
haveI' : na =Q nb := ⟨⟩
      return .isTrue q(isInt_eq_true $pa $pb)
    else if let some _i ← inferCharZeroOfRing? rα then
      let r : Q(decide ($na = $nb) = false) := (q(Eq.refl false) : Expr)
      return .isFalse q(isInt_eq_false $pa $pb $r)
    else
      failure --TODO: nonzero characteristic ≠
  let rec nnratArm (dsα : Q(DivisionSemiring $α)) := do
    let ⟨qa, na, da, pa⟩ ← ra.toNNRat' dsα; let ⟨qb, nb, db, pb⟩ ← rb.toNNRat' dsα
    if qa = qb then
haveI' : na =Q nb := ⟨⟩
haveI' : da =Q db := ⟨⟩
      return .isTrue q(isNNRat_eq_true $pa $pb)
    else if let some _i ← inferCharZeroOfDivisionSemiring? dsα then
      let r : Q(decide (Nat.mul $na $db = Nat.mul $nb $da) = false) :=
        (q(Eq.refl false) : Expr)
      return .isFalse q(isNNRat_eq_false $pa $pb $r)
    else
      failure --TODO: nonzero characteristic ≠
  let rec ratArm (dα : Q(DivisionRing $α)) := do
    let ⟨qa, na, da, pa⟩ ← ra.toRat' dα; let ⟨qb, nb, db, pb⟩ ← rb.toRat' dα
    if qa = qb then
haveI' : na =Q nb := ⟨⟩
haveI' : da =Q db := ⟨⟩
      return .isTrue q(isRat_eq_true $pa $pb)
    else if let some _i ← inferCharZeroOfDivisionRing? dα then
      let r : Q(decide (Int.mul $na (.ofNat $db) = Int.mul $nb (.ofNat $da)) = false) :=
        (q(Eq.refl false) : Expr)
      return .isFalse q(isRat_eq_false $pa $pb $r)
    else
      failure --TODO: nonzero characteristic ≠
  match ra, rb with
  | .isBool b₁ p₁, .isBool b₂ p₂ =>
    have a : Q(Prop) := a; have b : Q(Prop) := b
    match b₁, p₁, b₂, p₂ with
    | true, (p₁ : Q($a)), true, (p₂ : Q($b)) =>
      return .isTrue q(eq_of_true $p₁ $p₂)
    | false, (p₁ : Q(¬$a)), false, (p₂ : Q(¬$b)) =>
      return .isTrue q(eq_of_false $p₁ $p₂)
    | false, (p₁ : Q(¬$a)), true, (p₂ : Q($b)) =>
      return .isFalse q(ne_of_false_of_true $p₁ $p₂)
    | true, (p₁ : Q($a)), false, (p₂ : Q(¬$b)) =>
      return .isFalse q(ne_of_true_of_false $p₁ $p₂)
  | .isBool .., _ | _, .isBool .. => failure
  | .isNegNNRat dα .., _ | _, .isNegNNRat dα .. => ratArm dα
  -- mixing positive rationals and negative naturals means we need to use the full rat handler
  | .isNNRat dsα .., .isNegNat rα .. | .isNegNat rα .., .isNNRat dsα .. =>
    -- could alternatively try to combine `rα` and `dsα` here, but we'd have to do a defeq check
    -- so would still need to be in `MetaM`.
    ratArm (← synthInstanceQ q(DivisionRing $α))
  | .isNNRat dsα .., _ | _, .isNNRat dsα .. => nnratArm dsα
  | .isNegNat rα .., _ | _, .isNegNat rα .. => intArm rα
  | .isNat _ na pa, .isNat mα nb pb =>
    assumeInstancesCommute
    if na.natLit! = nb.natLit! then
haveI' : na =Q nb := ⟨⟩
      return .isTrue q(isNat_eq_true $pa $pb)
    else if let some _i ← inferCharZeroOfAddMonoidWithOne? mα then
      let r : Q(Nat.beq $na $nb = false) := (q(Eq.refl false) : Expr)
      return .isFalse q(isNat_eq_false $pa $pb $r)
    else
      failure --TODO: nonzero characteristic ≠

end Mathlib.Meta.NormNum
