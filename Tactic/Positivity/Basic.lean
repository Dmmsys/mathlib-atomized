/-
Copyright (c) 2022 Mario Carneiro, Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Heather Macbeth, Yaël Dillies
-/
module

public meta import Qq
public import Mathlib.Algebra.Order.Group.PosPart  -- shake: keep (Qq dependency)
public import Mathlib.Data.Nat.Factorial.Basic  -- shake: keep (Qq dependency)
public import Mathlib.Data.Int.CharZero  -- shake: keep (Qq dependency)
public import Mathlib.Data.PNat.Defs  -- shake: keep (Qq dependency)
public import Mathlib.Algebra.Order.Ring.Basic  -- shake: keep (Qq dependency)
public import Mathlib.Algebra.Order.Hom.Basic
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Tactic.Positivity.Core

/-!
## `positivity` core extensions

This file sets up the basic `positivity` extensions tagged with the `@[positivity]` attribute.
-/

public meta section

variable {α : Type*}

namespace Mathlib.Meta.Positivity
open Lean Meta Qq Function

section ite
variable [Zero α] (p : Prop) [Decidable p] {a b : α}

/-
**Mathlib.Meta.Positivity.ite_pos** 是 Mathlib 中的一个引理，位于命名空间 `Mathlib.Meta.Positi
vity`。
形式化陈述：ite_pos [LT α] (ha : 0 < a) (hb : 0 < b) : 0 < ite p a b
参数：ha : 0 < a；hb : 0 < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
-/
lemma ite_pos [LT α] (ha : 0 < a) (hb : 0 < b) : 0 < ite p a b := by
  by_cases p <;> simp [*]
/-
**Mathlib.Meta.Positivity.ite_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Mathlib.Meta.Pos
itivity`。
形式化陈述：ite_nonneg [LE α] (ha : 0 <= a) (hb : 0 <= b) : 0 <= ite p a b
参数：ha : 0 <= a；hb : 0 <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
-/
lemma ite_nonneg [LE α] (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ ite p a b := by
  by_cases p <;> simp [*]
/-
**Mathlib.Meta.Positivity.ite_nonneg_of_pos_of_nonneg** 是 Mathlib 中的一个引理，位于命名空间 
`Mathlib.Meta.Positivity`。
形式化陈述：ite_nonneg_of_pos_of_nonneg [Preorder α] (ha : 0 < a) (hb : 0 <= b) : 0 <=
 ite p a b
参数：ha : 0 < a；hb : 0 <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Meta.Positivity.ite_nonneg`：ite_nonneg [LE α] (ha : 0 <= a) (hb 
: 0 <= b) : 0 <= ite p a b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma ite_nonneg_of_pos_of_nonneg [Preorder α] (ha : 0 < a) (hb : 0 ≤ b) : 0 ≤ ite p a b :=
  ite_nonneg _ ha.le hb
/-
**Mathlib.Meta.Positivity.ite_nonneg_of_nonneg_of_pos** 是 Mathlib 中的一个引理，位于命名空间 
`Mathlib.Meta.Positivity`。
形式化陈述：ite_nonneg_of_nonneg_of_pos [Preorder α] (ha : 0 <= a) (hb : 0 < b) : 0 <=
 ite p a b
参数：ha : 0 <= a；hb : 0 < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Meta.Positivity.ite_nonneg`：ite_nonneg [LE α] (ha : 0 <= a) (hb 
: 0 <= b) : 0 <= ite p a b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma ite_nonneg_of_nonneg_of_pos [Preorder α] (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ ite p a b :=
  ite_nonneg _ ha hb.le
/-
**Mathlib.Meta.Positivity.ite_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Mathlib.Meta.Po
sitivity`。
形式化陈述：ite_ne_zero (ha : a != 0) (hb : b != 0) : ite p a b != 0
参数：ha : a != 0；hb : b != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
-/
lemma ite_ne_zero (ha : a ≠ 0) (hb : b ≠ 0) : ite p a b ≠ 0 := by by_cases p <;> simp [*]
/-
**Mathlib.Meta.Positivity.ite_ne_zero_of_pos_of_ne_zero** 是 Mathlib 中的一个引理，位于命名空
间 `Mathlib.Meta.Positivity`。
形式化陈述：ite_ne_zero_of_pos_of_ne_zero [Preorder α] (ha : 0 < a) (hb : b != 0) : it
e p a b != 0
参数：ha : 0 < a；hb : b != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Meta.Positivity.ite_ne_zero`：ite_ne_zero (ha : a != 0) (hb : b !
= 0) : ite p a b != 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
-/
lemma ite_ne_zero_of_pos_of_ne_zero [Preorder α] (ha : 0 < a) (hb : b ≠ 0) :
    ite p a b ≠ 0 :=
  ite_ne_zero _ ha.ne' hb
/-
**Mathlib.Meta.Positivity.ite_ne_zero_of_ne_zero_of_pos** 是 Mathlib 中的一个引理，位于命名空
间 `Mathlib.Meta.Positivity`。
形式化陈述：ite_ne_zero_of_ne_zero_of_pos [Preorder α] (ha : a != 0) (hb : 0 < b) : it
e p a b != 0
参数：ha : a != 0；hb : 0 < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Meta.Positivity.ite_ne_zero`：ite_ne_zero (ha : a != 0) (hb : b !
= 0) : ite p a b != 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
-/
lemma ite_ne_zero_of_ne_zero_of_pos [Preorder α] (ha : a ≠ 0) (hb : 0 < b) :
    ite p a b ≠ 0 :=
  ite_ne_zero _ ha hb.ne'

end ite

/-- The `positivity` extension which identifies expressions of the form `ite p a b`,
such that `positivity` successfully recognises both `a` and `b`. -/
/-
**Mathlib.Meta.Positivity.evalIte** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.Positi
vity`。
形式化陈述：Mathlib.Meta.Positivity.PositivityExt
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `positivity` extension which identifies expressions of the form `ite p a b`,
such that `positivity` successfully recognises both `a` and `b`.
-/
@[positivity ite _ _ _] def evalIte : PositivityExt where eval {u α} zα pα? e := do
  let .app (.app (.app (.app f (p : Q(Prop))) (_ : Q(Decidable $p))) (a : Q($α))) (b : Q($α))
    ← whnfR e | throwError "not ite"
  haveI' : $e =Q ite $p $a $b := ⟨⟩
  let ra ← core zα pα? a; let rb ← core zα pα? b
  guard <|← withDefault <| withNewMCtxDepth <| isDefEq f q(ite (α := $α))
  id <|
  match ra, rb with
  | .positive pa, .positive pb => pure (.positive q(ite_pos $p $pa $pb))
  | .positive pa, .nonnegative pb => pure (.nonnegative q(ite_nonneg_of_pos_of_nonneg $p $pa $pb))
  | .nonnegative pa, .positive pb => pure (.nonnegative q(ite_nonneg_of_nonneg_of_pos $p $pa $pb))
  | .nonnegative pa, .nonnegative pb => pure (.nonnegative q(ite_nonneg $p $pa $pb))
  | .positive pa, .nonzero pb => pure (.nonzero q(ite_ne_zero_of_pos_of_ne_zero $p $pa $pb))
  | .nonzero pa, .positive pb => pure (.nonzero q(ite_ne_zero_of_ne_zero_of_pos $p $pa $pb))
  | .nonzero pa, .nonzero pb => pure (.nonzero q(ite_ne_zero $p $pa $pb))
  | _, _ => pure .none

section LinearOrder
variable {R : Type*} [LinearOrder R] {a b c : R}

/-
**Mathlib.Meta.Positivity.le_min_of_lt_of_le** 是 Mathlib 中的一个引理，位于命名空间 `Mathlib.
Meta.Positivity`。
形式化陈述：le_min_of_lt_of_le (ha : a < b) (hb : a <= c) : a <= min b c
参数：ha : a < b；hb : a <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_min`：le_min (h₁ : c <= a) (h₂ : c <= b) : c <= min a b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma le_min_of_lt_of_le (ha : a < b) (hb : a ≤ c) : a ≤ min b c := le_min ha.le hb
/-
**Mathlib.Meta.Positivity.le_min_of_le_of_lt** 是 Mathlib 中的一个引理，位于命名空间 `Mathlib.
Meta.Positivity`。
形式化陈述：le_min_of_le_of_lt (ha : a <= b) (hb : a < c) : a <= min b c
参数：ha : a <= b；hb : a < c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_min`：le_min (h₁ : c <= a) (h₂ : c <= b) : c <= min a b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma le_min_of_le_of_lt (ha : a ≤ b) (hb : a < c) : a ≤ min b c := le_min ha hb.le
/-
**Mathlib.Meta.Positivity.min_ne** 是 Mathlib 中的一个引理，位于命名空间 `Mathlib.Meta.Positiv
ity`。
形式化陈述：min_ne (ha : a != c) (hb : b != c) : min a b != c
参数：ha : a != c；hb : b != c。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma min_ne (ha : a ≠ c) (hb : b ≠ c) : min a b ≠ c := by grind
/-
**Mathlib.Meta.Positivity.min_ne_of_ne_of_lt** 是 Mathlib 中的一个引理，位于命名空间 `Mathlib.
Meta.Positivity`。
形式化陈述：min_ne_of_ne_of_lt (ha : a != c) (hb : c < b) : min a b != c
参数：ha : a != c；hb : c < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Meta.Positivity.min_ne`：min_ne (ha : a != c) (hb : b != c) : min
 a b != c
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
-/
lemma min_ne_of_ne_of_lt (ha : a ≠ c) (hb : c < b) : min a b ≠ c := min_ne ha hb.ne'
/-
**Mathlib.Meta.Positivity.min_ne_of_lt_of_ne** 是 Mathlib 中的一个引理，位于命名空间 `Mathlib.
Meta.Positivity`。
形式化陈述：min_ne_of_lt_of_ne (ha : c < a) (hb : b != c) : min a b != c
参数：ha : c < a；hb : b != c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Meta.Positivity.min_ne`：min_ne (ha : a != c) (hb : b != c) : min
 a b != c
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
-/
lemma min_ne_of_lt_of_ne (ha : c < a) (hb : b ≠ c) : min a b ≠ c := min_ne ha.ne' hb
/-
**Mathlib.Meta.Positivity.max_ne** 是 Mathlib 中的一个引理，位于命名空间 `Mathlib.Meta.Positiv
ity`。
形式化陈述：max_ne (ha : a != c) (hb : b != c) : max a b != c
参数：ha : a != c；hb : b != c。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma max_ne (ha : a ≠ c) (hb : b ≠ c) : max a b ≠ c := by grind

end LinearOrder

/-- The `positivity` extension which identifies expressions of the form `min a b`,
such that `positivity` successfully recognises both `a` and `b`. -/
/-
**Mathlib.Meta.Positivity.evalMin** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.Positi
vity`。
形式化陈述：Mathlib.Meta.Positivity.PositivityExt
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `positivity` extension which identifies expressions of the form `min a b`,
such that `positivity` successfully recognises both `a` and `b`.
-/
@[positivity min _ _] def evalMin : PositivityExt where eval {u α} zα pα? e := do
  let .app (.app (f : Q($α → $α → $α)) (a : Q($α))) (b : Q($α)) ← whnfR e | throwError "not min"
  let _e_eq : $e =Q $f $a $b := ⟨⟩
  let _a ← synthInstanceQ q(LinearOrder $α)
  let ⟨_f_eq⟩ ← withDefault <| withNewMCtxDepth <| assertDefEqQ q($f) q(min)
  assumeInstancesCommute
  match (dependent := true) ← core zα pα? a, ← core zα pα? b with
  | .positive (pα := pα') pa, .positive pb =>
    assumeInstancesCommute
    pure (.positive q(lt_min $pa $pb))
  | .positive (pα := pα') pa, .nonnegative pb =>
    assumeInstancesCommute
    pure (.nonnegative q(le_min_of_lt_of_le $pa $pb))
  | .nonnegative (pα := pα') pa, .positive pb =>
    assumeInstancesCommute
    pure (.nonnegative q(le_min_of_le_of_lt $pa $pb))
  | .nonnegative pa (pα := pα'), .nonnegative pb =>
    assumeInstancesCommute
    pure (.nonnegative q(le_min $pa $pb))
  | .positive pa, .nonzero pb =>
    assumeInstancesCommute
    pure (.nonzero q(min_ne_of_lt_of_ne $pa $pb))
  | .nonzero pa, .positive pb =>
    assumeInstancesCommute
    pure (.nonzero q(min_ne_of_ne_of_lt $pa $pb))
  | .nonzero pa, .nonzero pb => do
    pure (.nonzero q(min_ne $pa $pb))
  | _, _ => pure .none

/-- Extension for the `max` operator. The `max` of two numbers is nonnegative if at least one
is nonnegative, strictly positive if at least one is positive, and nonzero if both are nonzero. -/
/-
**Mathlib.Meta.Positivity.evalMax** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.Positi
vity`。
形式化陈述：Mathlib.Meta.Positivity.PositivityExt
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extension for the `max` operator. The `max` of two numbers is nonnegative if at 
least one
is nonnegative, strictly positive if at least one is positive, and nonzero if bo
th are nonzero.
-/
@[positivity max _ _] def evalMax : PositivityExt where eval {u α} zα pα? e := do
  let .app (.app (f : Q($α → $α → $α)) (a : Q($α))) (b : Q($α)) ← whnfR e | throwError "not max"
  let _e_eq : $e =Q $f $a $b := ⟨⟩
  let _a ← synthInstanceQ q(LinearOrder $α)
  let ⟨_f_eq⟩ ← withDefault <| withNewMCtxDepth <| assertDefEqQ q($f) q(max)
  let result : Strictness zα e pα? ← catchNone do
    let ra ← core zα pα? a
    match (dependent := true) ra with
    | .positive pa =>
      assumeInstancesCommute
      pure (.positive q(lt_max_of_lt_left $pa))
    | .nonnegative pa =>
      assumeInstancesCommute
      pure (.nonnegative q(le_max_of_le_left $pa))
    -- If `a ≠ 0`, we might prove `max a b ≠ 0` if `b ≠ 0` but we don't want to evaluate
    -- `b` before having ruled out `0 < a`, for performance. So we do that in the second branch
    -- of the `orElse'`.
    | _ => pure .none
  orElse result do
    let rb ← core zα pα? b
    match (dependent := true) rb with
    | .positive pb =>
      assumeInstancesCommute
      pure (.positive q(lt_max_of_lt_right $pb))
    | .nonnegative pb =>
      assumeInstancesCommute
      pure (.nonnegative q(le_max_of_le_right $pb))
    | .nonzero pb => do
      match ← core zα pα? a with
      | .nonzero pa => pure (.nonzero q(max_ne $pa $pb))
      | _ => pure .none
    | _ => pure .none

/-- The `positivity` extension which identifies expressions of the form `a + b`,
such that `positivity` successfully recognises both `a` and `b`. -/
/-
**Mathlib.Meta.Positivity.evalAdd** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.Positi
vity`。
形式化陈述：Mathlib.Meta.Positivity.PositivityExt
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `positivity` extension which identifies expressions of the form `a + b`,
such that `positivity` successfully recognises both `a` and `b`.
-/
@[positivity _ + _] def evalAdd : PositivityExt where eval {u α} zα pα? e :=
  match pα? with | none => pure .none | some pα => do
  let .app (.app (f : Q($α → $α → $α)) (a : Q($α))) (b : Q($α)) ← whnfR e | throwError "not +"
  let _e_eq : $e =Q $f $a $b := ⟨⟩
  let _a ← synthInstanceQ q(AddZeroClass $α)
  assumeInstancesCommute
  let ⟨_f_eq⟩ ← withDefault <| withNewMCtxDepth <| assertDefEqQ q($f) q(HAdd.hAdd)
  let ra ← core zα pα a; let rb ← core zα pα b
  match ra, rb with
  | .positive pa, .positive pb =>
    let _a ← synthInstanceQ q(AddLeftMono $α)
    pure (.positive q(add_pos' $pa $pb))
  | .positive pa, .nonnegative pb =>
    let _a ← synthInstanceQ q(AddLeftMono $α)
    pure (.positive q(add_pos_of_pos_of_nonneg $pa $pb))
  | .nonnegative pa, .positive pb =>
    let _a ← synthInstanceQ q(AddRightMono $α)
    pure (.positive q(Right.add_pos_of_nonneg_of_pos $pa $pb))
  | .nonnegative pa, .nonnegative pb =>
    let _a ← synthInstanceQ q(AddLeftMono $α)
    pure (.nonnegative q(add_nonneg $pa $pb))
  | _, _ => failure

/-- The `positivity` extension which identifies expressions of the form `a - b`,
such that there is a local hypothesis `b < a`, `b ≤ a`, `a ≠ b` or `b ≠ a`. -/
/-
**Mathlib.Meta.Positivity.evalSub** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.Positi
vity`。
形式化陈述：Mathlib.Meta.Positivity.PositivityExt
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `positivity` extension which identifies expressions of the form `a - b`,
such that there is a local hypothesis `b < a`, `b ≤ a`, `a ≠ b` or `b ≠ a`.
-/
@[positivity _ - _] def evalSub : PositivityExt where eval {u α} _zα pα? e := do
  let .app (.app (f : Q($α → $α → $α)) (a : Q($α))) (b : Q($α)) ← whnfR e | throwError "not -"
  let _e_eq : $e =Q $f $a $b := ⟨⟩
  let _a ← synthInstanceQ q(AddGroup $α)
  assumeInstancesCommute
  let ⟨_f_eq⟩ ← withDefault <| withNewMCtxDepth <| assertDefEqQ q($f) q(HSub.hSub)
  id <|
  match pα? with
  | some pα => do
    let mut result := .none
    for decl in ← getLCtx do
      unless decl.isImplementationDetail do
        have e' : Q(Prop) := decl.type
        have p : Q($e') := .fvar decl.fvarId
        result ← orElse result do
          match e' with
          | ~q(@LE.le.{u} $β $le $lo $hi) =>
            let .defEq (_ : $α =Q $β) ← isDefEqQ α β | return .none
            let .defEq _ ← isDefEqQ q($le) q(($pα).toLE) | return .none
            let .defEq (_ : $a =Q $hi) ← isDefEqQ a hi | return .none
            let .defEq (_ : $b =Q $lo) ← isDefEqQ b lo | return .none
            let _ ← synthInstanceQ q(AddRightMono $α)
            return .nonnegative q(sub_nonneg_of_le $p)
          | ~q(@LT.lt.{u} $β $lt $lo $hi) =>
            let .defEq (_ : $α =Q $β) ← isDefEqQ α β | return .none
            let .defEq _ ← isDefEqQ q($lt) q(($pα).toLT) | return .none
            let .defEq (_ : $a =Q $hi) ← isDefEqQ a hi | return .none
            let .defEq (_ : $b =Q $lo) ← isDefEqQ b lo | return .none
            let _i ← synthInstanceQ q(AddRightStrictMono $α)
            assumeInstancesCommute
            return .positive (q(sub_pos_of_lt $p):)
          | ~q(@Ne.{u + 1} $β $lhs $rhs) =>
            let .defEq (_ : $α =Q $β) ← isDefEqQ α β | return .none
            if let .defEq (_ : $a =Q $lhs) ← isDefEqQ a lhs then
              let .defEq (_ : $b =Q $rhs) ← isDefEqQ b rhs | return .none
              return .nonzero (q(sub_ne_zero_of_ne $p):)
            if let .defEq _ ← isDefEqQ a rhs then
              let .defEq _ ← isDefEqQ b lhs | return .none
              return .nonzero (q(sub_ne_zero_of_ne ($p).symm):)
            return .none
          | _ => return .none
    return result
  | none => do
    let mut result := .none
    for decl in ← getLCtx do
      unless decl.isImplementationDetail do
        have e' : Q(Prop) := decl.type
        have p : Q($e') := .fvar decl.fvarId
        result ← orElse result do
          match e' with
          | ~q(@Ne.{u + 1} $β $lhs $rhs) =>
            let .defEq (_ : $α =Q $β) ← isDefEqQ α β | return .none
            if let .defEq (_ : $a =Q $lhs) ← isDefEqQ a lhs then
              let .defEq (_ : $b =Q $rhs) ← isDefEqQ b rhs | return .none
              return .nonzero (q(sub_ne_zero_of_ne $p):)
            if let .defEq _ ← isDefEqQ a rhs then
              let .defEq _ ← isDefEqQ b lhs | return .none
              return .nonzero (q(sub_ne_zero_of_ne ($p).symm):)
            return .none
          | _ => return .none
    return result

/-- The `positivity` extension which identifies expressions of the form `a * b`,
such that `positivity` successfully recognises both `a` and `b`. -/
/-
**Mathlib.Meta.Positivity.evalMul** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.Positi
vity`。
形式化陈述：Mathlib.Meta.Positivity.PositivityExt
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `positivity` extension which identifies expressions of the form `a * b`,
such that `positivity` successfully recognises both `a` and `b`.
-/
@[positivity _ * _] def evalMul : PositivityExt where eval {u α} zα pα? e := do
  let .app (.app (f : Q($α → $α → $α)) (a : Q($α))) (b : Q($α)) ← whnfR e | throwError "not *"
  let _e_eq : $e =Q $f $a $b := ⟨⟩
  let _a ← synthInstanceQ q(Mul $α)
  let ⟨_f_eq⟩ ← withDefault <| withNewMCtxDepth <| assertDefEqQ q($f) q(HMul.hMul)
  let ra ← core zα pα? a; let rb ← core zα pα? b
  let tryProveNonzero (pα? : Option Q(PartialOrder $α))
      (pa? : Option Q($a ≠ 0)) (pb? : Option Q($b ≠ 0)) : MetaM (Strictness zα e pα?) := do
    let pa ← liftOption pa?
    let pb ← liftOption pb?
    let _a ← synthInstanceQ q(NoZeroDivisors $α)
    pure (.nonzero q(mul_ne_zero $pa $pb))
  let tryProveNonneg (pα : Q(PartialOrder $α)) (pa? : Option Q(0 ≤ $a)) (pb? : Option Q(0 ≤ $b)) :
      MetaM (Strictness zα e pα) := do
    let pa ← liftOption pa?
    let pb ← liftOption pb?
    let _a ← synthInstanceQ q(MulZeroClass $α)
    let _a ← synthInstanceQ q(PosMulMono $α)
    assumeInstancesCommute
    pure (.nonnegative q(mul_nonneg $pa $pb))
  let tryProvePositive (pα : Q(PartialOrder $α)) (pa? : Option Q(0 < $a)) (pb? : Option Q(0 < $b)) :
      MetaM (Strictness zα e pα) := do
    let pa ← liftOption pa?
    let pb ← liftOption pb?
    let _a ← synthInstanceQ q(MulZeroClass $α)
    let _a ← synthInstanceQ q(PosMulStrictMono $α)
    assumeInstancesCommute
    pure (.positive q(mul_pos $pa $pb))
  id <|
  match pα? with
  | some pα => do
    let mut result : Strictness zα e (some pα) := .none
    result ← orElse result (tryProvePositive pα ra.toPositive rb.toPositive)
    result ← orElse result (tryProveNonneg pα ra.toNonneg rb.toNonneg)
    result ← orElse result (tryProveNonzero pα ra.toNonzero rb.toNonzero)
    return result
  | none =>
    return ← catchNone <| tryProveNonzero .none ra.toNonzero rb.toNonzero
/-
**Mathlib.Meta.Positivity.int_div_self_pos** 是 Mathlib 中的一个引理，位于命名空间 `Mathlib.Me
ta.Positivity`。
形式化陈述：int_div_self_pos {a : Int} (ha : 0 < a) : 0 < a / a
参数：ha : 0 < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.ediv_self`：∀ {a : ℤ}, a ≠ 0 → a / a = 1
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `Int.instNeZeroOfNatOfNat`：∀ {n : ℕ} [NeZero n], NeZero (OfNat.ofNat n)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma int_div_self_pos {a : ℤ} (ha : 0 < a) : 0 < a / a := by
  rw [Int.ediv_self ha.ne']; exact zero_lt_one
/-
**Mathlib.Meta.Positivity.int_div_nonneg_of_pos_of_nonneg** 是 Mathlib 中的一个引理，位于命
名空间 `Mathlib.Meta.Positivity`。
形式化陈述：int_div_nonneg_of_pos_of_nonneg {a b : Int} (ha : 0 < a) (hb : 0 <= b) : 0
 <= a / b
参数：ha : 0 < a；hb : 0 <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.ediv_nonneg`：∀ {a b : ℤ}, 0 ≤ a → 0 ≤ b → 0 ≤ a / b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma int_div_nonneg_of_pos_of_nonneg {a b : ℤ} (ha : 0 < a) (hb : 0 ≤ b) : 0 ≤ a / b :=
  Int.ediv_nonneg ha.le hb
/-
**Mathlib.Meta.Positivity.int_div_nonneg_of_nonneg_of_pos** 是 Mathlib 中的一个引理，位于命
名空间 `Mathlib.Meta.Positivity`。
形式化陈述：int_div_nonneg_of_nonneg_of_pos {a b : Int} (ha : 0 <= a) (hb : 0 < b) : 0
 <= a / b
参数：ha : 0 <= a；hb : 0 < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.ediv_nonneg`：∀ {a b : ℤ}, 0 ≤ a → 0 ≤ b → 0 ≤ a / b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma int_div_nonneg_of_nonneg_of_pos {a b : ℤ} (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ a / b :=
  Int.ediv_nonneg ha hb.le
/-
**Mathlib.Meta.Positivity.int_div_nonneg_of_pos_of_pos** 是 Mathlib 中的一个引理，位于命名空间
 `Mathlib.Meta.Positivity`。
形式化陈述：int_div_nonneg_of_pos_of_pos {a b : Int} (ha : 0 < a) (hb : 0 < b) : 0 <= 
a / b
参数：ha : 0 < a；hb : 0 < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.ediv_nonneg`：∀ {a b : ℤ}, 0 ≤ a → 0 ≤ b → 0 ≤ a / b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma int_div_nonneg_of_pos_of_pos {a b : ℤ} (ha : 0 < a) (hb : 0 < b) : 0 ≤ a / b :=
  Int.ediv_nonneg ha.le hb.le

/-- The `positivity` extension which identifies expressions of the form `a / b`,
where `a` and `b` are integers. -/
/-
**Mathlib.Meta.Positivity.evalIntDiv** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.Pos
itivity`。
形式化陈述：Mathlib.Meta.Positivity.PositivityExt
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `positivity` extension which identifies expressions of the form `a / b`,
where `a` and `b` are integers.
-/
@[positivity (_ : ℤ) / (_ : ℤ)] def evalIntDiv : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ℤ), ~q($a / $b) =>
    let ra ← core q(inferInstance) (some q(inferInstance)) a
    let rb ← core q(inferInstance) (some q(inferInstance)) b
    assertInstancesCommute
    match ra, rb with
    | .positive (pa : Q(0 < $a)), .positive (pb : Q(0 < $b)) =>
      -- Only attempts to prove `0 < a / a`, otherwise falls back to `0 ≤ a / b`
      let _ := q(int_div_self_pos $pa)
      match ← isDefEqQ a b with
      | .defEq _ => pure (.positive q(int_div_self_pos $pa))
      | .notDefEq => pure (.nonnegative q(int_div_nonneg_of_pos_of_pos $pa $pb))
    | .positive (pa : Q(0 < $a)), .nonnegative (pb : Q(0 ≤ $b)) =>
      pure (.nonnegative q(int_div_nonneg_of_pos_of_nonneg $pa $pb))
    | .nonnegative (pa : Q(0 ≤ $a)), .positive (pb : Q(0 < $b)) =>
      pure (.nonnegative q(int_div_nonneg_of_nonneg_of_pos $pa $pb))
    | .nonnegative (pa : Q(0 ≤ $a)), .nonnegative (pb : Q(0 ≤ $b)) =>
      pure (.nonnegative q(Int.ediv_nonneg $pa $pb))
    | _, _ => pure .none
  | _, _, _ => throwError "not /"
/-
**Mathlib.Meta.Positivity.pow_zero_pos** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.P
ositivity`。
形式化陈述：pow_zero_pos [Semiring α] [PartialOrder α] [IsOrderedRing α] [Nontrivial α
] (a : α) : 0 < a ^ 0
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
-/
theorem pow_zero_pos [Semiring α] [PartialOrder α] [IsOrderedRing α] [Nontrivial α]
    (a : α) : 0 < a ^ 0 :=
  zero_lt_one.trans_le (pow_zero a).ge
/-
**Mathlib.Meta.Positivity.pow_zero_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Me
ta.Positivity`。
形式化陈述：pow_zero_ne_zero [Semiring α] [Nontrivial α] (a : α) : a ^ 0 != 0
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
-/
theorem pow_zero_ne_zero [Semiring α] [Nontrivial α] (a : α) : a ^ 0 ≠ 0 :=
  pow_zero a ▸ one_ne_zero

/-- The `positivity` extension which identifies expressions of the form `a ^ (0 : ℕ)`.
This extension is run in addition to the general `a ^ b` extension (they are overlapping). -/
@[positivity _ ^ (0 : ℕ)]
meta def evalPowZeroNat : PositivityExt where eval {u α} _zα pα? e := do
  let .app (.app _ (a : Q($α))) _ ← whnfR e | throwError "not ^"
  let _a ← synthInstanceQ q(Semiring $α)
  assumeInstancesCommute
  haveI' : $e =Q $a ^ 0 := ⟨⟩
  let _a ← synthInstanceQ q(Nontrivial $α)
  match (dependent := true) pα? with
  | some _pα =>
    let _a ← synthInstanceQ q(IsOrderedRing $α)
    pure (.positive q(pow_zero_pos $a))
  | none => pure (.nonzero q(pow_zero_ne_zero $a))

/-- The `positivity` extension which identifies expressions of the form `a ^ (b : ℕ)`,
such that `positivity` successfully recognises both `a` and `b`. -/
@[positivity _ ^ (_ : ℕ)]
meta def evalPow : PositivityExt where eval {u α} zα pα? e := do
  let .app (.app _ (a : Q($α))) (b : Q(ℕ)) ← whnfR e | throwError "not ^"
  match (dependent := true) pα? with
  | none =>
    let _a ← synthInstanceQ q(MonoidWithZero $α)
    let _a ← synthInstanceQ q(NoZeroDivisors $α)
    assumeInstancesCommute
    haveI' : $e =Q $a ^ $b := ⟨⟩
    let .nonzero nza ← core zα .none a | pure .none
    pure (.nonzero q(pow_ne_zero $b $nza))
  | some pα =>
    let result : Strictness zα e pα ← catchNone do
      let _a ← synthInstanceQ q(Ring $α)
      let _a ← synthInstanceQ q(LinearOrder $α)
      let _a ← synthInstanceQ q(IsStrictOrderedRing $α)
      assumeInstancesCommute
      let .true := b.isAppOfArity ``OfNat.ofNat 3 | throwError "not a ^ n where n is a literal"
      let some n := (b.getRevArg! 1).rawNatLit? | throwError "not a ^ n where n is a literal"
      guard (n % 2 = 0)
      have m : Q(ℕ) := mkRawNatLit (n / 2)
      haveI' : $b =Q 2 * $m := ⟨⟩
      haveI' : $e =Q $a ^ $b := ⟨⟩
      pure (.nonnegative q((even_two_mul $m).pow_nonneg $a))
    orElse result do
      let ra ← core zα pα a
      let ofNonneg (pa : Q(0 ≤ $a)) (_rα : Q(Semiring $α)) (_oα : Q(IsOrderedRing $α)) :
          MetaM (Strictness zα e (some pα)) := do
        haveI' : $e =Q $a ^ $b := ⟨⟩
        assumeInstancesCommute
        pure (.nonnegative q(pow_nonneg $pa $b))
      let ofNonzero (pa : Q($a ≠ 0)) (_rα : Q(Semiring $α)) (_oα : Q(IsOrderedRing $α)) :
          MetaM (Strictness zα e (some pα)) := do
        haveI' : $e =Q $a ^ $b := ⟨⟩
        assumeInstancesCommute
        let _a ← synthInstanceQ q(NoZeroDivisors $α)
        pure (.nonzero q(pow_ne_zero $b $pa))
      match ra with
      | .positive pa =>
        try
          let _a ← synthInstanceQ q(Semiring $α)
          let _a ← synthInstanceQ q(IsStrictOrderedRing $α)
          assumeInstancesCommute
          haveI' : $e =Q $a ^ $b := ⟨⟩
          pure (.positive q(pow_pos $pa $b))
        catch e : Exception =>
          trace[Tactic.positivity.failure] "{e.toMessageData}"
          let rα ← synthInstanceQ q(Semiring $α)
          let oα ← synthInstanceQ q(IsOrderedRing $α)
          orElse (← catchNone (ofNonneg q(le_of_lt $pa) rα oα)) (ofNonzero q(ne_of_gt $pa) rα oα)
      | .nonnegative pa =>
          let sα ← synthInstanceQ q(Semiring $α)
          let oα ← synthInstanceQ q(IsOrderedRing $α)
          ofNonneg q($pa) q($sα) q($oα)
      | .nonzero pa =>
          let sα ← synthInstanceQ q(Semiring $α)
          let oα ← synthInstanceQ q(IsOrderedRing $α)
          ofNonzero q($pa) q($sα) q($oα)
      | .none => pure .none

/-
**Mathlib.Meta.Positivity.abs_pos_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.
Meta.Positivity`。
形式化陈述：abs_pos_of_ne_zero {α : Type*} [AddGroup α] [LinearOrder α] [AddLeftMono α
] {a : α} : a != 0 -> 0 < |a|
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `abs_pos`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α] [
AddLeftMono α] {a : α}, 0 < |a| ↔ a ≠ 0
-/
theorem abs_pos_of_ne_zero {α : Type*} [AddGroup α] [LinearOrder α]
    [AddLeftMono α] {a : α} : a ≠ 0 → 0 < |a| := abs_pos.mpr

/-- The `positivity` extension which identifies expressions of the form `|a|`. -/
@[positivity |_|]
meta def evalAbs : PositivityExt where eval {_u} (α zα pα?) (e : Q($α)) :=
  match pα? with | none => pure .none | some pα' => do
  let ~q(@abs _ (_) (_) $a) := e | throwError "not |·|"
  try
    match ← core zα (some pα') a with
    | .positive pa =>
      let pa' ← mkAppM ``abs_pos_of_pos #[pa]
      pure (.positive (pα := pα') pa')
    | .nonzero pa =>
      let pa' ← mkAppM ``abs_pos_of_ne_zero #[pa]
      pure (.positive (pα := pα') pa')
    | _ => throwError "goto catch"
  catch _ => do
    let pa' ← mkAppM ``abs_nonneg #[a]
    pure (.nonnegative (pα := pα') pa')

/-
**Mathlib.Meta.Positivity.int_natAbs_pos** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta
.Positivity`。
形式化陈述：int_natAbs_pos {n : Int} (hn : 0 < n) : 0 < n.natAbs
参数：hn : 0 < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.natAbs_pos`：∀ {a : ℤ}, 0 < a.natAbs ↔ a ≠ 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
-/
theorem int_natAbs_pos {n : ℤ} (hn : 0 < n) : 0 < n.natAbs :=
  Int.natAbs_pos.mpr hn.ne'

/-- Extension for the `positivity` tactic: `Int.natAbs` is positive when its input is.
Since the output type of `Int.natAbs` is `ℕ`, the nonnegative case is handled by the default
`positivity` tactic.
-/
@[positivity Int.natAbs _]
meta def evalNatAbs : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ℕ), ~q(Int.natAbs $a) =>
    let zα' : Q(Zero Int) := q(inferInstance)
    let pα' : Q(PartialOrder Int) := q(inferInstance)
    assertInstancesCommute
    let ra ← core zα' pα' a
    match ra with
    | .positive pa =>
      pure (.positive q(int_natAbs_pos $pa))
    | .nonzero pa =>
      pure (.positive q(Int.natAbs_pos.mpr $pa))
    | .nonnegative _pa =>
      pure .none
    | .none =>
      pure .none
  | _, _, _ => throwError "not Int.natAbs"

/-- Extension for the `positivity` tactic: `Nat.cast` is always non-negative,
and positive when its input is. -/
@[positivity Nat.cast _]
meta def evalNatCast : PositivityExt where eval {u α} _zα pα? e := do
  let ~q(@Nat.cast _ (_) ($a : ℕ)) := e | throwError "not Nat.cast"
  let zα' : Q(Zero Nat) := q(inferInstance)
  let (_i1 : Q(AddMonoidWithOne $α)) ← synthInstanceQ q(AddMonoidWithOne $α)
  match (dependent := true) pα? with
  | none =>
    let (_cz : Q(CharZero $α)) ← synthInstanceQ q(CharZero $α)
    assumeInstancesCommute
    match ← core zα' .none a with
    | .nonzero nza => pure (.nonzero q(Nat.cast_ne_zero.2 $nza))
    | _ => pure .none
  | some _pα =>
    let pα' : Q(PartialOrder Nat) := q(inferInstance)
    let (_i2 : Q(AddLeftMono $α)) ← synthInstanceQ q(AddLeftMono $α)
    let (_i3 : Q(ZeroLEOneClass $α)) ← synthInstanceQ q(ZeroLEOneClass $α)
    assumeInstancesCommute
    match ← core zα' pα' a with
    | .positive pa =>
      try
        let _nz ← synthInstanceQ q(NeZero (1 : $α))
        pure (.positive q(Nat.cast_pos'.2 $pa))
      catch _ =>
        pure (.nonnegative q(Nat.cast_nonneg' _))
    | _ =>
      pure (.nonnegative q(Nat.cast_nonneg' _))

/-- Extension for the `positivity` tactic: `Int.cast` is positive (resp. non-negative)
if its input is. -/
@[positivity Int.cast _]
meta def evalIntCast : PositivityExt where eval {u α} _zα pα? e := do
  let ~q(@Int.cast _ (_) ($a : ℤ)) := e | throwError "not Int.cast"
  let zα' : Q(Zero Int) := q(inferInstance)
  let pα' : Q(PartialOrder Int) := q(inferInstance)
  let ra ← core zα' pα' a
  match (dependent := true) ra, pα? with
  | .positive pa, some _ =>
    let _rα ← synthInstanceQ q(Ring $α)
    let _oα ← synthInstanceQ q(IsOrderedRing $α)
    let _nt ← synthInstanceQ q(Nontrivial $α)
    assumeInstancesCommute
    pure (.positive q(Int.cast_pos.mpr $pa))
  | .nonnegative pa, some _ =>
    let _rα ← synthInstanceQ q(Ring $α)
    let _oα ← synthInstanceQ q(IsOrderedRing $α)
    let _nt ← synthInstanceQ q(Nontrivial $α)
    assumeInstancesCommute
    pure (.nonnegative q(Int.cast_nonneg $pa))
  | .nonzero pa, _ =>
    let _oα ← synthInstanceQ q(AddGroupWithOne $α)
    let _nt ← synthInstanceQ q(CharZero $α)
    assumeInstancesCommute
    pure (.nonzero q(Int.cast_ne_zero.mpr $pa))
  | _ , _ =>
    pure .none

/-- Extension for `Nat.succ`. -/
@[positivity Nat.succ _]
meta def evalNatSucc : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with | none => throwError "not PartialOrder ℕ" | some _ => do
  match u, α, e with
  | 0, ~q(ℕ), ~q(Nat.succ $a) =>
    assertInstancesCommute
    pure (.positive q(Nat.succ_pos $a))
  | _, _, _ => throwError "not Nat.succ"

/-- Extension for `PNat.val`. -/
@[positivity PNat.val _]
meta def evalPNatVal : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with | none => throwError "not PartialOrder ℕ" | some _ => do
  match u, α, e with
  | 0, ~q(ℕ), ~q(PNat.val $a) =>
    assertInstancesCommute
    pure (.positive q(PNat.pos $a))
  | _, _, _ => throwError "not PNat.val"

/-- Extension for `Nat.factorial`. -/
@[positivity Nat.factorial _]
meta def evalFactorial : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => throwError "not PartialOrder ℕ" | some _ => do
  match u, α, e with
  | 0, ~q(ℕ), ~q(Nat.factorial $a) =>
    assertInstancesCommute
    pure (.positive q(Nat.factorial_pos $a))
  | _, _, _ => throwError "failed to match Nat.factorial"

/-- Extension for `Nat.ascFactorial`. -/
@[positivity Nat.ascFactorial _ _]
meta def evalAscFactorial : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => throwError "not PartialOrder ℕ" | some _ => do
  match u, α, e with
  | 0, ~q(ℕ), ~q(Nat.ascFactorial ($n + 1) $k) =>
    assertInstancesCommute
    pure (.positive q(Nat.ascFactorial_pos $n $k))
  | _, _, _ => throwError "failed to match Nat.ascFactorial"

/-- Extension for `Nat.gcd`.
Uses positivity of the left term, if available, then tries the right term.

The implementation relies on the fact that `Positivity.core` on `ℕ` never returns `nonzero`. -/
@[positivity Nat.gcd _ _]
meta def evalNatGCD : PositivityExt where eval {u α} z p e :=
  match p with | none => throwError "not PartialOrder ℕ" | some p => do
  match u, α, e with
  | 0, ~q(ℕ), ~q(Nat.gcd $a $b) =>
    assertInstancesCommute
    match ← core z p a with
    | .positive pa =>
      assertInstancesCommute
      return .positive q(Nat.gcd_pos_of_pos_left $b $pa)
    | _ =>
      match ← core z p b with
      | .positive pb =>
        assertInstancesCommute
        return .positive q(Nat.gcd_pos_of_pos_right $a $pb)
      | _ => failure
  | _, _, _ => throwError "not Nat.gcd"

/-- Extension for `Nat.lcm`. -/
@[positivity Nat.lcm _ _]
meta def evalNatLCM : PositivityExt where eval {u α} z p e :=
  match p with | none => throwError "not PartialOrder ℕ" | some p => do
  match u, α, e with
  | 0, ~q(ℕ), ~q(Nat.lcm $a $b) =>
    match ← core z p a with
    | .positive pa =>
      assertInstancesCommute
      match ← core z p b with
      | .positive pb =>
        assertInstancesCommute
        return .positive q(Nat.lcm_pos $pa $pb)
      | _ => failure
    | _ => failure
  | _, _, _ => throwError "not Nat.lcm"

/-- Extension for `Nat.sqrt`. -/
@[positivity Nat.sqrt _]
meta def evalNatSqrt : PositivityExt where eval {u α} z p e :=
  match p with | none => throwError "not PartialOrder ℕ" | some p => do
  match u, α, e with
  | 0, ~q(ℕ), ~q(Nat.sqrt $n) =>
    match ← core z p n with
    | .positive pa =>
      assumeInstancesCommute
      return .positive q(Nat.sqrt_pos.mpr $pa)
    | _ => failure
  | _, _, _ => throwError "not Nat.sqrt"

/-- Extension for `Int.gcd`.
Uses positivity of the left term, if available, then tries the right term. -/
@[positivity Int.gcd _ _]
meta def evalIntGCD : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => throwError "not PartialOrder ℕ" | some _ => do
  match u, α, e with
  | 0, ~q(ℕ), ~q(Int.gcd $a $b) =>
    let z ← synthInstanceQ (q(Zero ℤ) : Q(Type))
    let p ← synthInstanceQ (q(PartialOrder ℤ) : Q(Type))
    assertInstancesCommute
    match (← catchNone (core z (some p) a)).toNonzero z with
    | some na => return .positive q(Int.gcd_pos_of_ne_zero_left $b $na)
    | none =>
      match (← core z (some p) b).toNonzero z with
      | some nb => return .positive q(Int.gcd_pos_of_ne_zero_right $a $nb)
      | none => failure
  | _, _, _ => throwError "not Int.gcd"

/-- Extension for `Int.lcm`. -/
@[positivity Int.lcm _ _]
meta def evalIntLCM : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => throwError "not PartialOrder ℕ" | some _ => do
  match u, α, e with
  | 0, ~q(ℕ), ~q(Int.lcm $a $b) =>
    let z ← synthInstanceQ (q(Zero ℤ) : Q(Type))
    let p ← synthInstanceQ (q(PartialOrder ℤ) : Q(Type))
    assertInstancesCommute
    match (← core z (some p) a).toNonzero z with
    | some na =>
      match (← core z (some p) b).toNonzero z with
      | some nb => return .positive q(Int.lcm_pos $na $nb)
      | _ => failure
    | _ => failure
  | _, _, _ => throwError "not Int.lcm"

section NNRat
open NNRat

alias ⟨_, NNRat.num_pos_of_pos⟩ := num_pos
alias ⟨_, NNRat.num_ne_zero_of_ne_zero⟩ := num_ne_zero

/-- The `positivity` extension which identifies expressions of the form `NNRat.num q`,
such that `positivity` successfully recognises `q`. -/
@[positivity NNRat.num _]
meta def evalNNRatNum : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => throwError "not PartialOrder ℕ" | some _ => do
  match u, α, e with
  | 0, ~q(ℕ), ~q(NNRat.num $a) =>
    let zα : Q(Zero ℚ≥0) := q(inferInstance)
    let pα : Q(PartialOrder ℚ≥0) := q(inferInstance)
    trace[Tactic.positivity] "I'm evalNNRatNum: {e}"
    assumeInstancesCommute
    match ← core zα pα a with
    | .positive pa =>
      return .positive q(NNRat.num_pos_of_pos $pa)
    | .nonzero pa => return .nonzero q(NNRat.num_ne_zero_of_ne_zero $pa)
    | _ => return .none
  | _, _, _ => throwError "not NNRat.num"

/-- The `positivity` extension which identifies expressions of the form `Rat.den a`. -/
@[positivity NNRat.den _]
meta def evalNNRatDen : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => throwError "not PartialOrder ℕ" | some _ => do
  match u, α, e with
  | 0, ~q(ℕ), ~q(NNRat.den $a) =>
    assumeInstancesCommute
    return .positive q(den_pos $a)
  | _, _, _ => throwError "not NNRat.den"

variable {q : ℚ≥0}

/-
**Mathlib.Meta.Positivity.** 是 Mathlib 中的一个示例，位于命名空间 `Mathlib.Meta.Positivity`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example (hq : 0 < q) : 0 < q.num := by positivity
/-
**Mathlib.Meta.Positivity.** 是 Mathlib 中的一个示例，位于命名空间 `Mathlib.Meta.Positivity`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example (hq : q ≠ 0) : q.num ≠ 0 := by positivity
/-
**Mathlib.Meta.Positivity.** 是 Mathlib 中的一个示例，位于命名空间 `Mathlib.Meta.Positivity`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : 0 < q.den := by positivity

end NNRat

open Rat

alias ⟨_, num_pos_of_pos⟩ := num_pos
alias ⟨_, num_nonneg_of_nonneg⟩ := num_nonneg
alias ⟨_, num_ne_zero_of_ne_zero⟩ := num_ne_zero

/-- The `positivity` extension which identifies expressions of the form `Rat.num a`,
such that `positivity` successfully recognises `a`. -/
@[positivity Rat.num _]
meta def evalRatNum : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => throwError "not PartialOrder ℤ" | some _ => do
  match u, α, e with
  | 0, ~q(ℤ), ~q(Rat.num $a) =>
    let zα : Q(Zero ℚ) := q(inferInstance)
    let pα : Q(PartialOrder ℚ) := q(inferInstance)
    assumeInstancesCommute
    match ← core zα pα a with
    | .positive pa =>
      pure <| .positive q(num_pos_of_pos $pa)
    | .nonnegative pa =>
      pure <| .nonnegative q(num_nonneg_of_nonneg $pa)
    | .nonzero pa => pure <| .nonzero q(num_ne_zero_of_ne_zero $pa)
    | .none => pure .none
  | _, _ => throwError "not Rat.num"

/-- The `positivity` extension which identifies expressions of the form `Rat.den a`. -/
@[positivity Rat.den _]
meta def evalRatDen : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => throwError "not PartialOrder ℕ" | some _ => do
  match u, α, e with
  | 0, ~q(ℕ), ~q(Rat.den $a) =>
    assumeInstancesCommute
    pure <| .positive q(den_pos $a)
  | _, _ => throwError "not Rat.num"

/-- Extension for `posPart`. `a⁺` is always nonnegative, and positive if `a` is. -/
@[positivity _⁺]
meta def evalPosPart : PositivityExt where eval {u α} zα pα? e :=
  match pα? with | none => pure .none | some pα => do
  match e with
  | ~q(@posPart _ $instαpospart $a) =>
    let _instαlat ← synthInstanceQ q(Lattice $α)
    let _instαgrp ← synthInstanceQ q(AddGroup $α)
    assertInstancesCommute
    -- FIXME: There seems to be a bug in `Positivity.core` that makes it fail (instead of returning
    -- `.none`) here sometimes. See e.g. the first test for `posPart`. This is why we need
    -- `catchNone`
    match ← catchNone (core zα pα a) with
    | .positive pf =>
      return .positive q(posPart_pos $pf)
    | _ => return .nonnegative q(posPart_nonneg $a)
  | _ => throwError "not `posPart`"

/-- Extension for `negPart`. `a⁻` is always nonnegative. -/
@[positivity _⁻]
meta def evalNegPart : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => pure .none | some _ => do
  match e with
  | ~q(@negPart _ $instαnegpart $a) =>
    let _instαlat ← synthInstanceQ q(Lattice $α)
    let _instαgrp ← synthInstanceQ q(AddGroup $α)
    assertInstancesCommute
    return .nonnegative q(negPart_nonneg $a)
  | _ => throwError "not `negPart`"

/-- Extension for the `positivity` tactic: nonnegative maps take nonnegative values. -/
@[positivity DFunLike.coe _ _]
meta def evalMap : PositivityExt where eval {_ β} _ pβ? e :=
  match pβ? with | none => pure .none | some _ => do
  let .app (.app _ f) a ← whnfR e
    | throwError "not ↑f · where f is of NonnegHomClass"
  let pa ← mkAppOptM ``apply_nonneg #[none, none, β, none, none, none, none, f, a]
  pure (.nonnegative pa)

end Positivity

end Meta

end Mathlib

