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

/-- Helper function to synthesize a typed `CharZero α` expression given `Ring α`. -/
/-
**Mathlib.Meta.NormNum.inferCharZeroOfRing** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Me
ta.NormNum`。
形式化陈述：inferCharZeroOfRing {α : Q(Type u)} (_i : Q(Ring $α)
参数：Type u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Helper function to synthesize a typed `CharZero α` expression given `Ring α`.
-/
def inferCharZeroOfRing {α : Q(Type u)} (_i : Q(Ring $α) := by with_reducible assumption) :
    MetaM Q(CharZero $α) :=
  return ← synthInstanceQ q(CharZero $α) <|>
    throwError "not a characteristic zero ring"

/-- Helper function to synthesize a typed `CharZero α` expression given `Ring α`, if it exists. -/
/-
**Mathlib.Meta.NormNum.inferCharZeroOfRing** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Me
ta.NormNum`。
形式化陈述：inferCharZeroOfRing {α : Q(Type u)} (_i : Q(Ring $α)
参数：Type u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Helper function to synthesize a typed `CharZero α` expression given `Ring α`, if
 it exists.
-/
def inferCharZeroOfRing? {α : Q(Type u)} (_i : Q(Ring $α) := by with_reducible assumption) :
    MetaM (Option Q(CharZero $α)) :=
  return (← trySynthInstanceQ q(CharZero $α)).toOption

/-- Helper function to synthesize a typed `CharZero α` expression given `AddMonoidWithOne α`. -/
/-
**Mathlib.Meta.NormNum.inferCharZeroOfAddMonoidWithOne** 是 Mathlib 中的一个定义，位于命名空间
 `Mathlib.Meta.NormNum`。
形式化陈述：inferCharZeroOfAddMonoidWithOne {α : Q(Type u)} (_i : Q(AddMonoidWithOne $
α)
参数：Type u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Helper function to synthesize a typed `CharZero α` expression given `AddMonoidWi
thOne α`.
-/
def inferCharZeroOfAddMonoidWithOne {α : Q(Type u)}
    (_i : Q(AddMonoidWithOne $α) := by with_reducible assumption) : MetaM Q(CharZero $α) :=
  return ← synthInstanceQ q(CharZero $α) <|>
    throwError "not a characteristic zero AddMonoidWithOne"

/-- Helper function to synthesize a typed `CharZero α` expression given `AddMonoidWithOne α`, if it
exists. -/
/-
**Mathlib.Meta.NormNum.inferCharZeroOfAddMonoidWithOne** 是 Mathlib 中的一个定义，位于命名空间
 `Mathlib.Meta.NormNum`。
形式化陈述：inferCharZeroOfAddMonoidWithOne {α : Q(Type u)} (_i : Q(AddMonoidWithOne $
α)
参数：Type u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Helper function to synthesize a typed `CharZero α` expression given `AddMonoidWi
thOne α`, if it
exists.
-/
def inferCharZeroOfAddMonoidWithOne? {α : Q(Type u)}
    (_i : Q(AddMonoidWithOne $α) := by with_reducible assumption) :
      MetaM (Option Q(CharZero $α)) :=
  return (← trySynthInstanceQ q(CharZero $α)).toOption

/-- Helper function to synthesize a typed `CharZero α` expression given `DivisionRing α`. -/
/-
**Mathlib.Meta.NormNum.inferCharZeroOfDivisionRing** 是 Mathlib 中的一个定义，位于命名空间 `Ma
thlib.Meta.NormNum`。
形式化陈述：inferCharZeroOfDivisionRing {α : Q(Type u)} (_i : Q(DivisionRing $α)
参数：Type u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Helper function to synthesize a typed `CharZero α` expression given `DivisionRin
g α`.
-/
def inferCharZeroOfDivisionRing {α : Q(Type u)}
    (_i : Q(DivisionRing $α) := by with_reducible assumption) : MetaM Q(CharZero $α) :=
  return ← synthInstanceQ q(CharZero $α) <|>
    throwError "not a characteristic zero division ring"

/-- Helper function to synthesize a typed `CharZero α` expression given `Divisionsemiring α`, if it
exists. -/
/-
**Mathlib.Meta.NormNum.inferCharZeroOfDivisionSemiring** 是 Mathlib 中的一个定义，位于命名空间
 `Mathlib.Meta.NormNum`。
形式化陈述：inferCharZeroOfDivisionSemiring? {α : Q(Type u)} (_i : Q(DivisionSemiring 
$α)
参数：Type u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Helper function to synthesize a typed `CharZero α` expression given `Divisionsem
iring α`, if it
exists.
-/
def inferCharZeroOfDivisionSemiring? {α : Q(Type u)}
    (_i : Q(DivisionSemiring $α) := by with_reducible assumption) : MetaM (Option Q(CharZero $α)) :=
  return (← trySynthInstanceQ (q(CharZero $α) : Q(Prop))).toOption

/-- Helper function to synthesize a typed `CharZero α` expression given `DivisionRing α`, if it
exists. -/
/-
**Mathlib.Meta.NormNum.inferCharZeroOfDivisionRing** 是 Mathlib 中的一个定义，位于命名空间 `Ma
thlib.Meta.NormNum`。
形式化陈述：inferCharZeroOfDivisionRing {α : Q(Type u)} (_i : Q(DivisionRing $α)
参数：Type u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Helper function to synthesize a typed `CharZero α` expression given `DivisionRin
g α`, if it
exists.
-/
def inferCharZeroOfDivisionRing? {α : Q(Type u)}
    (_i : Q(DivisionRing $α) := by with_reducible assumption) : MetaM (Option Q(CharZero $α)) :=
  return (← trySynthInstanceQ q(CharZero $α)).toOption
/-
**Mathlib.Meta.NormNum.isRat_mkRat** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.NormN
um`。
形式化陈述：∀ {a na n : ℤ} {b nb d : ℕ},   Mathlib.Meta.NormNum.IsInt a na →     Mathl
ib.Meta.NormNum.IsNat b nb →       Mathlib.Meta.NormNum.IsRat (↑na / ↑nb) n d → 
Mathlib.Meta.NormNum.IsRat (mkRat a b) n d
参数：↑na / ↑nb；mkRat a b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.mkRat_eq_div`：∀ (a : ℤ) (b : ℕ), mkRat a b = ↑a / ↑b
-/
theorem isRat_mkRat : {a na n : ℤ} → {b nb d : ℕ} → IsInt a na → IsNat b nb →
    IsRat (na / nb : ℚ) n d → IsRat (mkRat a b) n d
  | _, _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, ⟨_, h⟩ => by rw [Rat.mkRat_eq_div]; exact ⟨_, h⟩
/-
**Mathlib.Meta.NormNum.isNNRat_divNat** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.No
rmNum`。
形式化陈述：∀ {a na n b nb d : ℕ},   Mathlib.Meta.NormNum.IsNat a na →     Mathlib.Met
a.NormNum.IsNat b nb →       Mathlib.Meta.NormNum.IsNNRat (↑na / ↑nb) n d → Math
lib.Meta.NormNum.IsNNRat (NNRat.divNat a b) n d
参数：↑na / ↑nb；NNRat.divNat a b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNRat.divNat_eq_div`：divNat_eq_div (a b : Nat) : divNat a b = a / b
-/
theorem isNNRat_divNat : {a na n : ℕ} → {b nb d : ℕ} → IsNat a na → IsNat b nb →
    IsNNRat (na / nb : ℚ≥0) n d → IsNNRat (NNRat.divNat a b) n d
  | _, _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, ⟨_, h⟩ => by rw [NNRat.divNat_eq_div]; exact ⟨_, h⟩

attribute [local instance] monadLiftOptionMetaM in
/-- The `norm_num` extension which identifies expressions of the form `mkRat a b`,
such that `norm_num` successfully recognises both `a` and `b`, and returns `a / b`. -/
@[norm_num mkRat _ _]
/-
**Mathlib.Meta.NormNum.evalMkRat** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.NormNum
`。
形式化陈述：evalMkRat : NormNumExt where eval {u α} (e : Q(Rat)) : MetaM (Result e)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `norm_num` extension which identifies expressions of the form `mkRat a b`,
such that `norm_num` successfully recognises both `a` and `b`, and returns `a / 
b`.
-/
def evalMkRat : NormNumExt where eval {u α} (e : Q(ℚ)) : MetaM (Result e) := do
  let .app (.app (.const ``mkRat _) (a : Q(ℤ))) (b : Q(ℕ)) ← whnfR e | failure
  haveI' : $e =Q mkRat $a $b := ⟨⟩
  let ra ← derive a
  let some ⟨_, na, pa⟩ := ra.toInt (q(Int.instRing) : Q(Ring Int)) | failure
  let ⟨nb, pb⟩ ← deriveNat q($b) q(AddCommMonoidWithOne.toAddMonoidWithOne)
  let rab ← derive q($na / $nb : Rat)
  let ⟨q, n, d, p⟩ ← rab.toRat' q(Rat.instDivisionRing)
  return .isRat _ q n d q(isRat_mkRat $pa $pb $p)

/-- The `norm_num` extension which identifies expressions of the form `NNRat.divNat a b`,
such that `norm_num` successfully recognises both `a` and `b`, and returns `a / b`. -/
@[norm_num NNRat.divNat _ _]
/-
**Mathlib.Meta.NormNum.evalNNRatDivNat** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.N
ormNum`。
形式化陈述：evalNNRatDivNat : NormNumExt where eval {u α} (e : Q(Rat>=0)) : MetaM (Res
ult e)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `norm_num` extension which identifies expressions of the form `NNRat.divNat 
a b`,
such that `norm_num` successfully recognises both `a` and `b`, and returns `a / 
b`.
-/
def evalNNRatDivNat : NormNumExt where eval {u α} (e : Q(ℚ≥0)) : MetaM (Result e) := do
  let .app (.app (.const ``NNRat.divNat _) (a : Q(ℕ))) (b : Q(ℕ)) ← whnfR e | failure
  haveI' : $e =Q NNRat.divNat $a $b := ⟨⟩
  let ra ← derive q($a)
  let ⟨na, pa⟩ ← deriveNat q($a) q(AddCommMonoidWithOne.toAddMonoidWithOne)
  let ⟨nb, pb⟩ ← deriveNat q($b) q(AddCommMonoidWithOne.toAddMonoidWithOne)
  let rab ← derive q($na / $nb : NNRat)
  let some ⟨q, n, d, p⟩ := rab.toNNRat' q(NNRat.instSemifield.toDivisionSemiring) | failure
  return .isNNRat _ q n d q(isNNRat_divNat $pa $pb $p)
/-
**Mathlib.Meta.NormNum.isNat_ratCast** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.Nor
mNum`。
形式化陈述：∀ {R : Type u_1} [inst : DivisionRing R] {q : ℚ} {n : ℕ},   Mathlib.Meta.N
ormNum.IsNat q n → Mathlib.Meta.NormNum.IsNat (↑q) n
参数：↑q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.cast_natCast`：cast_natCast (n : Nat) : ((n : Rat) : α) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isNat_ratCast {R : Type*} [DivisionRing R] : {q : ℚ} → {n : ℕ} →
    IsNat q n → IsNat (q : R) n
  | _, _, ⟨rfl⟩ => ⟨by simp⟩
/-
**Mathlib.Meta.NormNum.isNat_nnratCast** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.N
ormNum`。
形式化陈述：∀ {R : Type u_1} [inst : DivisionSemiring R] {q : ℚ≥0} {n : ℕ},   Mathlib.
Meta.NormNum.IsNat q n → Mathlib.Meta.NormNum.IsNat (↑q) n
参数：↑q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNRat.cast_natCast`：∀ {α : Type u_3} [inst : DivisionSemiring α] (n : ℕ)
, ↑↑n = ↑n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isNat_nnratCast {R : Type*} [DivisionSemiring R] : {q : ℚ≥0} → {n : ℕ} →
    IsNat q n → IsNat (q : R) n
  | _, _, ⟨rfl⟩ => ⟨by simp⟩
/-
**Mathlib.Meta.NormNum.isInt_ratCast** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.Nor
mNum`。
形式化陈述：∀ {R : Type u_1} [inst : DivisionRing R] {q : ℚ} {n : ℤ},   Mathlib.Meta.N
ormNum.IsInt q n → Mathlib.Meta.NormNum.IsInt (↑q) n
参数：↑q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.cast_intCast`：cast_intCast (n : Int) : ((n : Rat) : α) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isInt_ratCast {R : Type*} [DivisionRing R] : {q : ℚ} → {n : ℤ} →
    IsInt q n → IsInt (q : R) n
  | _, _, ⟨rfl⟩ => ⟨by simp⟩
/-
**Mathlib.Meta.NormNum.isNNRat_ratCast** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.N
ormNum`。
形式化陈述：∀ {R : Type u_1} [inst : DivisionRing R] [CharZero R] {q : ℚ} {n d : ℕ},  
 Mathlib.Meta.NormNum.IsNNRat q n d → Mathlib.Meta.NormNum.IsNNRat (↑q) n d
参数：↑q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Rat.cast_natCast`：cast_natCast (n : Nat) : ((n : Rat) : α) = n
· 使用定理 `Rat.cast_one`：cast_one : ((1 : Rat) : α) = 1
-/
theorem isNNRat_ratCast {R : Type*} [DivisionRing R] [CharZero R] : {q : ℚ} → {n : ℕ} → {d : ℕ} →
    IsNNRat q n d → IsNNRat (q : R) n d
  | _, _, _, ⟨⟨qi,_,_⟩, rfl⟩ => ⟨⟨qi, by norm_cast, by norm_cast⟩, by simp only; norm_cast⟩
/-
**Mathlib.Meta.NormNum.isNNRat_nnratCast** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta
.NormNum`。
形式化陈述：∀ {R : Type u_1} [inst : DivisionSemiring R] [CharZero R] {q : ℚ≥0} {n d :
 ℕ},   Mathlib.Meta.NormNum.IsNNRat q n d → Mathlib.Meta.NormNum.IsNNRat (↑q) n 
d
参数：↑q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NNRat.cast_natCast`：∀ {α : Type u_3} [inst : DivisionSemiring α] (n : ℕ)
, ↑↑n = ↑n
· 使用定理 `NNRat.cast_one`：∀ {α : Type u_3} [inst : DivisionSemiring α], ↑1 = 1
-/
theorem isNNRat_nnratCast {R : Type*} [DivisionSemiring R] [CharZero R] : {q : ℚ≥0} → {n : ℕ} →
    {d : ℕ} → IsNNRat q n d → IsNNRat (q : R) n d
  | _, _, _, ⟨⟨qi,_,_⟩, rfl⟩ => ⟨⟨qi, by norm_cast, by norm_cast⟩, by simp only; norm_cast⟩
/-
**Mathlib.Meta.NormNum.isRat_ratCast** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.Nor
mNum`。
形式化陈述：∀ {R : Type u_1} [inst : DivisionRing R] [CharZero R] {q : ℚ} {n : ℤ} {d :
 ℕ},   Mathlib.Meta.NormNum.IsRat q n d → Mathlib.Meta.NormNum.IsRat (↑q) n d
参数：↑q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Rat.cast_natCast`：cast_natCast (n : Nat) : ((n : Rat) : α) = n
· 使用定理 `Rat.cast_one`：cast_one : ((1 : Rat) : α) = 1
· 使用定理 `Rat.cast_intCast`：cast_intCast (n : Int) : ((n : Rat) : α) = n
-/
theorem isRat_ratCast {R : Type*} [DivisionRing R] [CharZero R] : {q : ℚ} → {n : ℤ} → {d : ℕ} →
    IsRat q n d → IsRat (q : R) n d
  | _, _, _, ⟨⟨qi,_,_⟩, rfl⟩ => ⟨⟨qi, by norm_cast, by norm_cast⟩, by simp only; norm_cast⟩

/-- The `norm_num` extension which identifies an expression `RatCast.ratCast q` where `norm_num`
recognizes `q`, returning the cast of `q`. -/
/-
**Mathlib.Meta.NormNum.evalRatCast** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.NormN
um`。
形式化陈述：Mathlib.Meta.NormNum.NormNumExt
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `norm_num` extension which identifies an expression `RatCast.ratCast q` wher
e `norm_num`
recognizes `q`, returning the cast of `q`.
-/
@[norm_num Rat.cast _, RatCast.ratCast _] def evalRatCast : NormNumExt where eval {u α} e := do
  let dα ← inferDivisionRing α
  let .app r (a : Q(ℚ)) ← whnfR e | failure
  guard <|← withNewMCtxDepth <| isDefEq r q(Rat.cast (K := $α))
  let r ← derive q($a)
  haveI' : $e =Q Rat.cast $a := ⟨⟩
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
/-
**Mathlib.Meta.NormNum.evalNNRatCast** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.Nor
mNum`。
形式化陈述：evalNNRatCast : NormNumExt where eval {u α} e
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `norm_num` extension which identifies an expression `NNRat.cast q` where `no
rm_num`
recognizes `q`, returning the cast of `q`.
-/
def evalNNRatCast : NormNumExt where eval {u α} e := do
  let dα ← inferDivisionSemiring α
  let ~q(@NNRat.cast _ $dα' $a) := e | failure
  guard <| ← matchesInstance dα' q(@DivisionSemiring.toNNRatCast _ $dα)
  match ← derive q($a) with
  | .isNat _ na pa =>
    assumeInstancesCommute
    return .isNat _ na q(isNat_nnratCast $pa)
  | .isNNRat _ qa na da pa =>
    assumeInstancesCommute
    let some _ ← inferCharZeroOfDivisionSemiring? dα | failure
    return .isNNRat q(inferInstance) qa na da q(isNNRat_nnratCast $pa)
  | _ => failure
/-
**Mathlib.Meta.NormNum.isNNRat_inv_pos** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.N
ormNum`。
形式化陈述：isNNRat_inv_pos {α} [DivisionSemiring α] [CharZero α] {a : α} {n d : Nat} 
: IsNNRat a (Nat.succ n) d -> IsNNRat a⁻¹ d (Nat.succ n)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `invOf_eq_inv`：invOf_eq_inv (a : α) [Invertible a] : ⅟a = a⁻¹
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem isNNRat_inv_pos {α} [DivisionSemiring α] [CharZero α] {a : α} {n d : ℕ} :
    IsNNRat a (Nat.succ n) d → IsNNRat a⁻¹ d (Nat.succ n) := by
  rintro ⟨_, rfl⟩
  have := invertibleOfNonzero (α := α) (Nat.cast_ne_zero.2 (Nat.succ_ne_zero n))
  exact ⟨this, by simp⟩
/-
**Mathlib.Meta.NormNum.isRat_inv_pos** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.Nor
mNum`。
形式化陈述：isRat_inv_pos {α} [DivisionRing α] [CharZero α] {a : α} {n d : Nat} : IsRa
t a (.ofNat (Nat.succ n)) d -> IsRat a⁻¹ (.ofNat d) (Nat.succ n)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Int.cast_add`：∀ {R : Type u} [inst : AddGroupWithOne R] (m n : ℤ), ↑(m +
 n) = ↑m + ↑n
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `invOf_eq_inv`：invOf_eq_inv (a : α) [Invertible a] : ⅟a = a⁻¹
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem isRat_inv_pos {α} [DivisionRing α] [CharZero α] {a : α} {n d : ℕ} :
    IsRat a (.ofNat (Nat.succ n)) d → IsRat a⁻¹ (.ofNat d) (Nat.succ n) := by
  rintro ⟨_, rfl⟩
  have := invertibleOfNonzero (α := α) (Nat.cast_ne_zero.2 (Nat.succ_ne_zero n))
  exact ⟨this, by simp⟩
/-
**Mathlib.Meta.NormNum.isNat_inv_one** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.Nor
mNum`。
形式化陈述：∀ {α : Type u_1} [inst : DivisionSemiring α] {a : α}, Mathlib.Meta.NormNum
.IsNat a 1 → Mathlib.Meta.NormNum.IsNat a⁻¹ 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isNat_inv_one {α} [DivisionSemiring α] : {a : α} →
    IsNat a (nat_lit 1) → IsNat a⁻¹ (nat_lit 1)
  | _, ⟨rfl⟩ => ⟨by simp⟩
/-
**Mathlib.Meta.NormNum.isNat_inv_zero** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.No
rmNum`。
形式化陈述：∀ {α : Type u_1} [inst : DivisionSemiring α] {a : α}, Mathlib.Meta.NormNum
.IsNat a 0 → Mathlib.Meta.NormNum.IsNat a⁻¹ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isNat_inv_zero {α} [DivisionSemiring α] : {a : α} →
    IsNat a (nat_lit 0) → IsNat a⁻¹ (nat_lit 0)
  | _, ⟨rfl⟩ => ⟨by simp⟩
/-
**Mathlib.Meta.NormNum.isInt_inv_neg_one** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta
.NormNum`。
形式化陈述：∀ {α : Type u_1} [inst : DivisionRing α] {a : α},   Mathlib.Meta.NormNum.I
sInt a (Int.negOfNat 1) → Mathlib.Meta.NormNum.IsInt a⁻¹ (Int.negOfNat 1)
参数：Int.negOfNat 1；Int.negOfNat 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_negOfNat`：cast_negOfNat (n : Nat) : ((negOfNat n : Int) : R) = 
-n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `inv_neg`：inv_neg : (-a)⁻¹ = -a⁻¹
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isInt_inv_neg_one {α} [DivisionRing α] : {a : α} →
    IsInt a (.negOfNat (nat_lit 1)) → IsInt a⁻¹ (.negOfNat (nat_lit 1))
  | _, ⟨rfl⟩ => ⟨by simp⟩
/-
**Mathlib.Meta.NormNum.isRat_inv_neg** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.Nor
mNum`。
形式化陈述：isRat_inv_neg {α} [DivisionRing α] [CharZero α] {a : α} {n d : Nat} : IsRa
t a (.negOfNat (Nat.succ n)) d -> IsRat a⁻¹ (.negOfNat d) (Nat.succ n)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `invOf_eq_inv`：invOf_eq_inv (a : α) [Invertible a] : ⅟a = a⁻¹
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用引理 `inv_neg`：inv_neg : (-a)⁻¹ = -a⁻¹
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem isRat_inv_neg {α} [DivisionRing α] [CharZero α] {a : α} {n d : ℕ} :
    IsRat a (.negOfNat (Nat.succ n)) d → IsRat a⁻¹ (.negOfNat d) (Nat.succ n) := by
  rintro ⟨_, rfl⟩
  simp only [Int.negOfNat_eq]
  have := invertibleOfNonzero (α := α) (Nat.cast_ne_zero.2 (Nat.succ_ne_zero n))
  generalize Nat.succ n = n at *
  use this; simp only [Int.ofNat_eq_natCast, Int.cast_neg,
    Int.cast_natCast, invOf_eq_inv, inv_neg, neg_mul, mul_inv_rev, inv_inv]

open Lean

attribute [local instance] monadLiftOptionMetaM in
/-- The result of inverting a `norm_num` result. -/
/-
**Mathlib.Meta.NormNum.Result.inv** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.NormNu
m.Result`。
形式化陈述：{u : Level} →   {α : Q(Type u)} →     {a : Q(«$α»)} →       Mathlib.Meta.N
ormNum.Result a →         (dsα : Q(DivisionSemiring «$α»)) → Option Q(CharZero «
$α») → MetaM (Mathlib.Meta.NormNum.Result q(«$a»⁻¹))
参数：Type u；«$α»；dsα : Q(DivisionSemiring «$α»)；CharZero «$α»；Mathlib.Meta.NormNum
.Result q(«$a»⁻¹)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The result of inverting a `norm_num` result.
-/
def Result.inv {u : Level} {α : Q(Type u)} {a : Q($α)} (ra : Result a)
    (dsα : Q(DivisionSemiring $α)) (czα? : Option Q(CharZero $α)) :
    MetaM (Result q($a⁻¹)) := do
  if let .some ⟨qa, na, da, pa⟩ := ra.toNNRat' dsα then
    let qb := qa⁻¹
    if qa > 0 then
      if let some _i := czα? then
        have lit2 : Q(ℕ) := mkRawNatLit (na.natLit! - 1)
        haveI : $na =Q ($lit2).succ := ⟨⟩
        return .isNNRat' dsα qb q($da) q($na) q(isNNRat_inv_pos $pa)
      else
        guard (qa = 1)
        let .isNat inst n pa := ra | failure
        haveI' : $n =Q nat_lit 1 := ⟨⟩
        assumeInstancesCommute
        return .isNat inst n q(isNat_inv_one $pa)
    else
      let .isNat inst n pa := ra | failure
      haveI' : $n =Q nat_lit 0 := ⟨⟩
      assumeInstancesCommute
      return .isNat inst n q(isNat_inv_zero $pa)
  else
    let dα ← inferDivisionRing α
    assertInstancesCommute
    let ⟨qa, na, da, pa⟩ ← ra.toRat' dα
    let qb := qa⁻¹
    guard <| qa < 0
    if let some _i := czα? then
      have lit : Q(ℕ) := na.appArg!
      haveI : $na =Q Int.negOfNat $lit := ⟨⟩
      have lit2 : Q(ℕ) := mkRawNatLit (lit.natLit! - 1)
      haveI : $lit =Q ($lit2).succ := ⟨⟩
      return .isRat dα qb q(.negOfNat $da) lit q(isRat_inv_neg $pa)
    else
      guard (qa = -1)
      let .isNegNat inst n pa := ra | failure
      haveI' : $n =Q nat_lit 1 := ⟨⟩
      assumeInstancesCommute
      return .isNegNat inst n q(isInt_inv_neg_one $pa)

/-- The `norm_num` extension which identifies expressions of the form `a⁻¹`,
such that `norm_num` successfully recognises `a`. -/
/-
**Mathlib.Meta.NormNum.evalInv** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.NormNum`。
形式化陈述：Mathlib.Meta.NormNum.NormNumExt
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `norm_num` extension which identifies expressions of the form `a⁻¹`,
such that `norm_num` successfully recognises `a`.
-/
@[norm_num _⁻¹] def evalInv : NormNumExt where eval {u α} e := do
  let .app f (a : Q($α)) ← whnfR e | failure
  let ra ← derive a
  let dsα ← inferDivisionSemiring α
  guard <| ← withNewMCtxDepth <| isDefEq f q(Inv.inv (α := $α))
  haveI' : $e =Q $a⁻¹ := ⟨⟩
  assumeInstancesCommute
  ra.inv q($dsα) (← inferCharZeroOfDivisionSemiring? dsα)

end Mathlib.Meta.NormNum

