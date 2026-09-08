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

/-
**Mathlib.Meta.NormNum.isNat_eq_false** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.No
rmNum`。
形式化陈述：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [CharZero α] {a b : α} {a' b'
 : ℕ},   Mathlib.Meta.NormNum.IsNat a a' → Mathlib.Meta.NormNum.IsNat b b' → a'.
beq b' = false → ¬a = b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.ne_of_beq_eq_false`：∀ {n m : ℕ}, n.beq m = false → ¬n = m
-/
theorem isNat_eq_false [AddMonoidWithOne α] [CharZero α] : {a b : α} → {a' b' : ℕ} →
    IsNat a a' → IsNat b b' → Nat.beq a' b' = false → ¬a = b
  | _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, h => by simpa using Nat.ne_of_beq_eq_false h
/-
**Mathlib.Meta.NormNum.isInt_eq_false** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.No
rmNum`。
形式化陈述：∀ {α : Type u_1} [inst : Ring α] [CharZero α] {a b : α} {a' b' : ℤ},   Mat
hlib.Meta.NormNum.IsInt a a' → Mathlib.Meta.NormNum.IsInt b b' → decide (a' = b'
) = false → ¬a = b
参数：a' = b'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_decide_eq_false`：∀ {p : Prop} [inst : Decidable p], decide p = false 
→ ¬p
-/
theorem isInt_eq_false [Ring α] [CharZero α] : {a b : α} → {a' b' : ℤ} →
    IsInt a a' → IsInt b b' → decide (a' = b') = false → ¬a = b
  | _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, h => by simpa using of_decide_eq_false h
/-
**Mathlib.Meta.NormNum.NNRat.invOf_denom_swap** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib
.Meta.NormNum.NNRat`。
形式化陈述：∀ {α : Type u_1} [inst : Semiring α] (n₁ n₂ : ℕ) (a₁ a₂ : α) [inst_1 : Inv
ertible a₁] [inst_2 : Invertible a₂],   ↑n₁ * ⅟a₁ = ↑n₂ * ⅟a₂ ↔ ↑n₁ * a₂ = ↑n₂ *
 a₁
参数：n₁ n₂ : ℕ；a₁ a₂ : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_invOf_eq_iff_eq_mul_right`：mul_invOf_eq_iff_eq_mul_right : a * ⅟c = 
b ↔ a = b * c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.commute_cast`：commute_cast (x : α) (n : Nat) : Commute x n
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_left_eq_iff_eq_invOf_mul`：mul_left_eq_iff_eq_invOf_mul : c * a = b ↔
 a = ⅟c * b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem NNRat.invOf_denom_swap [Semiring α] (n₁ n₂ : ℕ) (a₁ a₂ : α)
    [Invertible a₁] [Invertible a₂] : n₁ * ⅟a₁ = n₂ * ⅟a₂ ↔ n₁ * a₂ = n₂ * a₁ := by
  rw [mul_invOf_eq_iff_eq_mul_right, ← Nat.commute_cast, mul_assoc,
    ← mul_left_eq_iff_eq_invOf_mul, Nat.commute_cast]
/-
**Mathlib.Meta.NormNum.isNNRat_eq_false** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.
NormNum`。
形式化陈述：∀ {α : Type u_1} [inst : Semiring α] [CharZero α] {a b : α} {na nb da db :
 ℕ},   Mathlib.Meta.NormNum.IsNNRat a na da →     Mathlib.Meta.NormNum.IsNNRat b
 nb db → decide (na.mul db = nb.mul da) = false → ¬a = b
参数：na.mul db = nb.mul da。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Meta.NormNum.NNRat.invOf_denom_swap`：∀ {α : Type u_1} [inst : Se
miring α] (n₁ n₂ : ℕ) (a₁ a₂ : α) [inst_1 : Invertible a₁] [inst_2 : Invertible 
a₂],   ↑n₁ * ⅟a₁ = ↑n₂ * ⅟a₂ ↔ ↑n…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `of_decide_eq_false`：∀ {p : Prop} [inst : Decidable p], decide p = false 
→ ¬p
-/
theorem isNNRat_eq_false [Semiring α] [CharZero α] : {a b : α} → {na nb : ℕ} → {da db : ℕ} →
    IsNNRat a na da → IsNNRat b nb db →
    decide (Nat.mul na db = Nat.mul nb da) = false → ¬a = b
  | _, _, _, _, _, _, ⟨_, rfl⟩, ⟨_, rfl⟩, h => by
    rw [NNRat.invOf_denom_swap]; exact mod_cast of_decide_eq_false h
/-
**Mathlib.Meta.NormNum.Rat.invOf_denom_swap** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.M
eta.NormNum.Rat`。
形式化陈述：∀ {α : Type u_1} [inst : Ring α] (n₁ n₂ : ℤ) (a₁ a₂ : α) [inst_1 : Inverti
ble a₁] [inst_2 : Invertible a₂],   ↑n₁ * ⅟a₁ = ↑n₂ * ⅟a₂ ↔ ↑n₁ * a₂ = ↑n₂ * a₁
参数：n₁ n₂ : ℤ；a₁ a₂ : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_invOf_eq_iff_eq_mul_right`：mul_invOf_eq_iff_eq_mul_right : a * ⅟c = 
b ↔ a = b * c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Int.commute_cast`：commute_cast (a : α) (n : Int) : Commute a n
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_left_eq_iff_eq_invOf_mul`：mul_left_eq_iff_eq_invOf_mul : c * a = b ↔
 a = ⅟c * b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Rat.invOf_denom_swap [Ring α] (n₁ n₂ : ℤ) (a₁ a₂ : α)
    [Invertible a₁] [Invertible a₂] : n₁ * ⅟a₁ = n₂ * ⅟a₂ ↔ n₁ * a₂ = n₂ * a₁ := by
  rw [mul_invOf_eq_iff_eq_mul_right, ← Int.commute_cast, mul_assoc,
    ← mul_left_eq_iff_eq_invOf_mul, Int.commute_cast]
/-
**Mathlib.Meta.NormNum.isRat_eq_false** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.No
rmNum`。
形式化陈述：∀ {α : Type u_1} [inst : Ring α] [CharZero α] {a b : α} {na nb : ℤ} {da db
 : ℕ},   Mathlib.Meta.NormNum.IsRat a na da →     Mathlib.Meta.NormNum.IsRat b n
b db → decide (na.mul (Int.ofNat db) = nb.mul (Int.ofNat da)) = false → ¬a = b
参数：na.mul (Int.ofNat db) = nb.mul (Int.ofNat da)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Meta.NormNum.Rat.invOf_denom_swap`：∀ {α : Type u_1} [inst : Ring
 α] (n₁ n₂ : ℤ) (a₁ a₂ : α) [inst_1 : Invertible a₁] [inst_2 : Invertible a₂],  
 ↑n₁ * ⅟a₁ = ↑n₂ * ⅟a₂ ↔ ↑n₁ * …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `of_decide_eq_false`：∀ {p : Prop} [inst : Decidable p], decide p = false 
→ ¬p
-/
theorem isRat_eq_false [Ring α] [CharZero α] : {a b : α} → {na nb : ℤ} → {da db : ℕ} →
    IsRat a na da → IsRat b nb db →
    decide (Int.mul na (.ofNat db) = Int.mul nb (.ofNat da)) = false → ¬a = b
  | _, _, _, _, _, _, ⟨_, rfl⟩, ⟨_, rfl⟩, h => by
    rw [Rat.invOf_denom_swap]; exact mod_cast of_decide_eq_false h

attribute [local instance] monadLiftOptionMetaM in
/-- The `norm_num` extension which identifies expressions of the form `a = b`,
such that `norm_num` successfully recognises both `a` and `b`. -/
/-
**Mathlib.Meta.NormNum.evalEq** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.NormNum`。
形式化陈述：Mathlib.Meta.NormNum.NormNumExt
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `norm_num` extension which identifies expressions of the form `a = b`,
such that `norm_num` successfully recognises both `a` and `b`.
-/
@[norm_num _ = _] def evalEq : NormNumExt where eval {v β} e := do
  haveI' : v =QL 0 := ⟨⟩; haveI' : $β =Q Prop := ⟨⟩
  let .app (.app f a) b ← whnfR e | failure
  let ⟨u, α, a⟩ ← inferTypeQ' a
  have b : Q($α) := b
  haveI' : $e =Q ($a = $b) := ⟨⟩
  guard <|← withNewMCtxDepth <| isDefEq f q(Eq (α := $α))
  let ra ← derive a; let rb ← derive b
  let rec intArm (rα : Q(Ring $α)) := do
    let ⟨za, na, pa⟩ ← ra.toInt rα; let ⟨zb, nb, pb⟩ ← rb.toInt rα
    if za = zb then
      haveI' : $na =Q $nb := ⟨⟩
      return .isTrue q(isInt_eq_true $pa $pb)
    else if let some _i ← inferCharZeroOfRing? rα then
      let r : Q(decide ($na = $nb) = false) := (q(Eq.refl false) : Expr)
      return .isFalse q(isInt_eq_false $pa $pb $r)
    else
      failure --TODO: nonzero characteristic ≠
  let rec nnratArm (dsα : Q(DivisionSemiring $α)) := do
    let ⟨qa, na, da, pa⟩ ← ra.toNNRat' dsα; let ⟨qb, nb, db, pb⟩ ← rb.toNNRat' dsα
    if qa = qb then
      haveI' : $na =Q $nb := ⟨⟩
      haveI' : $da =Q $db := ⟨⟩
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
      haveI' : $na =Q $nb := ⟨⟩
      haveI' : $da =Q $db := ⟨⟩
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
      haveI' : $na =Q $nb := ⟨⟩
      return .isTrue q(isNat_eq_true $pa $pb)
    else if let some _i ← inferCharZeroOfAddMonoidWithOne? mα then
      let r : Q(Nat.beq $na $nb = false) := (q(Eq.refl false) : Expr)
      return .isFalse q(isNat_eq_false $pa $pb $r)
    else
      failure --TODO: nonzero characteristic ≠

end Mathlib.Meta.NormNum

