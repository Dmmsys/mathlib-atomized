/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.Ring.Divisibility.Basic
public import Mathlib.Data.Ordering.Lemmas
public import Mathlib.Data.PNat.Basic
public import Mathlib.SetTheory.Ordinal.Principal
public import Mathlib.Tactic.NormNum

/-!
# Ordinal notation

Constructive ordinal arithmetic for ordinals below `ε₀`.

We define a type `ONote`, with constructors `0 : ONote` and `ONote.oadd e n a` representing
`ω ^ e * n + a`.
We say that `o` is in Cantor normal form - `ONote.NF o` - if either `o = 0` or
`o = ω ^ e * n + a` with `a < ω ^ e` and `a` in Cantor normal form.

The type `NONote` is the type of ordinals below `ε₀` in Cantor normal form.
Various operations (addition, subtraction, multiplication, exponentiation)
are defined on `ONote` and `NONote`.
-/

@[expose] public section

open Ordinal Order

-- The generated theorem `ONote.zero.sizeOf_spec` is flagged by `simpNF`,
-- and we don't otherwise need it.
set_option genSizeOfSpec false in
/-- Recursive definition of an ordinal notation. `zero` denotes the ordinal 0, and `oadd e n a` is
intended to refer to `ω ^ e * n + a`. For this to be a valid Cantor normal form, we must have the
exponents decrease to the right, but we can't state this condition until we've defined `repr`, so we
make it a separate definition `NF`. -/
/-
**ONote** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Recursive definition of an ordinal notation. `zero` denotes the ordinal 0, and `
oadd e n a` is
intended to refer to `ω ^ e * n + a`. For this to be a valid Cantor normal form,
 we must have the
exponents decrease to the right, but we can't state this condition until we've d
efined `repr`, so we
make it a separate definition `NF`.
-/
inductive ONote : Type
  | zero : ONote
  | oadd : ONote → ℕ+ → ONote → ONote
  deriving DecidableEq

compile_inductive% ONote

namespace ONote

/-- Notation for 0 -/
/-
**ONote.** 是 Mathlib 中的一个实例，位于命名空间 `ONote`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Notation for 0
-/
instance : Zero ONote :=
  ⟨zero⟩

@[simp]
/-
**ONote.zero_def** 是 Mathlib 中的一个定理，位于命名空间 `ONote`。
形式化陈述：zero_def : zero = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_def : zero = 0 :=
  rfl
/-
**ONote.** 是 Mathlib 中的一个实例，位于命名空间 `ONote`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited ONote :=
  ⟨0⟩

/-- Notation for 1 -/
/-
**ONote.** 是 Mathlib 中的一个实例，位于命名空间 `ONote`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Notation for 1
-/
instance : One ONote :=
  ⟨oadd 0 1 0⟩

/-- Notation for ω -/
/-
**ONote.omega** 是 Mathlib 中的一个定义，位于命名空间 `ONote`。
形式化陈述：omega : ONote
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Notation for ω
-/
def omega : ONote :=
  oadd 1 1 0

/-- The ordinal denoted by a notation -/
/-
**ONote.repr** 是 Mathlib 中的一个定义，位于命名空间 `ONote`。
形式化陈述：ONote → Ordinal.{0}
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ordinal denoted by a notation
-/
noncomputable def repr : ONote → Ordinal.{0}
  | 0 => 0
  | oadd e n a => ω ^ repr e * n + repr a
/-
**ONote.repr_zero** 是 Mathlib 中的一个定理，位于命名空间 `ONote`。
形式化陈述：ONote.repr 0 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem repr_zero : repr 0 = 0 := rfl
attribute [simp] repr.eq_1 repr.eq_2

set_option backward.privateInPublic true in
/-- Print `ω^s*n`, omitting `s` if `e = 0` or `e = 1`, and omitting `n` if `n = 1` -/
/-
**ONote.toStringAux** 是 Mathlib 中的一个定义，位于命名空间 `ONote`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Print `ω^s*n`, omitting `s` if `e = 0` or `e = 1`, and omitting `n` if `n = 1`
-/
private def toStringAux (e : ONote) (n : ℕ) (s : String) : String :=
  if e = 0 then toString n
  else (if e = 1 then "ω" else "ω^(" ++ s ++ ")") ++ if n = 1 then "" else "*" ++ toString n

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Print an ordinal notation -/
/-
**ONote.toString** 是 Mathlib 中的一个定义，位于命名空间 `ONote`。
形式化陈述：ONote → String
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Print an ordinal notation
-/
def toString : ONote → String
  | zero => "0"
  | oadd e n 0 => toStringAux e n (toString e)
  | oadd e n a => toStringAux e n (toString e) ++ " + " ++ toString a

open Lean in
/-- Print an ordinal notation -/
/-
**ONote.repr'** 是 Mathlib 中的一个定义，位于命名空间 `ONote`。
形式化陈述：ℕ → ONote → Format
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Print an ordinal notation
-/
def repr' (prec : ℕ) : ONote → Format
  | zero => "0"
  | oadd e n a =>
    Repr.addAppParen
      ("oadd " ++ (repr' max_prec e) ++ " " ++ Nat.repr (n : ℕ) ++ " " ++ (repr' max_prec a))
      prec
/-
**ONote.** 是 Mathlib 中的一个实例，位于命名空间 `ONote`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ToString ONote :=
  ⟨toString⟩
/-
**ONote.** 是 Mathlib 中的一个实例，位于命名空间 `ONote`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Repr ONote where
  reprPrec o prec := repr' prec o
/-
**ONote.** 是 Mathlib 中的一个实例，位于命名空间 `ONote`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Preorder ONote where
  le x y := repr x ≤ repr y
  lt x y := repr x < repr y
  le_refl _ := @le_refl Ordinal _ _
  le_trans _ _ _ := @le_trans Ordinal _ _ _ _
  lt_iff_le_not_ge _ _ := @lt_iff_le_not_ge Ordinal _ _ _
/-
**ONote.lt_def** 是 Mathlib 中的一个定理，位于命名空间 `ONote`。
形式化陈述：lt_def {x y : ONote} : x < y ↔ repr x < repr y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lt_def {x y : ONote} : x < y ↔ repr x < repr y :=
  Iff.rfl
/-
**ONote.le_def** 是 Mathlib 中的一个定理，位于命名空间 `ONote`。
形式化陈述：le_def {x y : ONote} : x <= y ↔ repr x <= repr y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_def {x y : ONote} : x ≤ y ↔ repr x ≤ repr y :=
  Iff.rfl

@[gcongr] alias ⟨repr_le_repr, _⟩ := le_def
@[gcongr] alias ⟨repr_lt_repr, _⟩ := lt_def
/-
**ONote.** 是 Mathlib 中的一个实例，位于命名空间 `ONote`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : WellFoundedRelation ONote :=
  ⟨(· < ·), InvImage.wf repr Ordinal.lt_wf⟩

/-- Convert a `Nat` into an ordinal -/
/-
**ONote.ofNat** 是 Mathlib 中的一个定义，位于命名空间 `ONote`。
形式化陈述：ℕ → ONote
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Convert a `Nat` into an ordinal
-/
@[coe] def ofNat : ℕ → ONote
  | 0 => 0
  | Nat.succ n => oadd 0 n.succPNat 0
/-
**ONote.ofNat_zero** 是 Mathlib 中的一个定理，位于命名空间 `ONote`。
形式化陈述：↑0 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem ofNat_zero : ofNat 0 = 0 :=
  rfl
/-
**ONote.ofNat_succ** 是 Mathlib 中的一个定理，位于命名空间 `ONote`。
形式化陈述：∀ (n : ℕ), ↑n.succ = ONote.oadd 0 n.succPNat 0
参数：n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem ofNat_succ (n) : ofNat (Nat.succ n) = oadd 0 n.succPNat 0 :=
  rfl
/-
**ONote.** 是 Mathlib 中的一个实例，位于命名空间 `ONote`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) nat (n : ℕ) : OfNat ONote n where
  ofNat := ofNat n
/-
**ONote.ofNat_one** 是 Mathlib 中的一个定理，位于命名空间 `ONote`。
形式化陈述：↑1 = 1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp 1200] theorem ofNat_one : ofNat 1 = 1 := rfl
/-
**ONote.repr_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `ONote`。
形式化陈述：∀ (n : ℕ), (↑n).repr = ↑n
参数：n : ℕ；↑n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ONote.repr.eq_2`：∀ (e : ONote) (n : ℕ+) (a : ONote), (e.oadd n a).repr =
 Ordinal.omega0 ^ e.repr * ↑↑n + a.repr
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ordinal.opow_zero`：opow_zero (a : Ordinal) : a ^ (0 : Ordinal) = 1
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
@[simp] theorem repr_ofNat (n : ℕ) : repr (ofNat n) = n := by cases n <;> simp
/-
**ONote.repr_one** 是 Mathlib 中的一个定理，位于命名空间 `ONote`。
形式化陈述：ONote.repr 1 = ↑1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ONote.repr_ofNat`：∀ (n : ℕ), (↑n).repr = ↑n
-/
@[simp] theorem repr_one : repr 1 = (1 : ℕ) := repr_ofNat 1
/-
**ONote.omega0_le_oadd** 是 Mathlib 中的一个定理，位于命名空间 `ONote`。
形式化陈述：omega0_le_oadd (e n a) : ω ^ repr e <= repr (oadd e n a)
参数：e n a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mul_le_mul_iff_right₀`：mul_le_mul_iff_right₀ [PosMulMono α] [PosMulRefle
ctLE α] (a0 : 0 < a) : a * b <= a * c ↔ b <= c
· 使用定理 `PosMulStrictMono.toPosMulMono`：∀ {α : Type u_1} [inst : MulZeroClass α] 
[inst_1 : PartialOrder α] [PosMulStrictMono α], PosMulMono α
· 使用定理 `Ordinal.instPosMulStrictMono`：PosMulStrictMono Ordinal.{u_4}
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `Ordinal.opow_pos`：opow_pos {a : Ordinal} (b : Ordinal) (a0 : 0 < a) : 0 
< a ^ b
· 使用定理 `Ordinal.omega0_pos`：omega0_pos : 0 < ω
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `instZeroLEOneClassOfIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α] [inst
_1 : Zero α] [inst_2 : One α] [IsBotZeroClass α], ZeroLEOneClass α
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `le_self_add`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ a + b
-/
theorem omega0_le_oadd (e n a) : ω ^ repr e ≤ repr (oadd e n a) := by
  refine le_trans ?_ le_self_add
  simpa using! (mul_le_mul_iff_right₀ <| opow_pos (repr e) omega0_pos).2 (Nat.cast_le.2 n.2)
/-
**ONote.oadd_pos** 是 Mathlib 中的一个定理，位于命名空间 `ONote`。
形式化陈述：oadd_pos (e n a) : 0 < oadd e n a
参数：e n a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Ordinal.opow_pos`：opow_pos {a : Ordinal} (b : Ordinal) (a0 : 0 < a) : 0 
< a ^ b
· 使用定理 `Ordinal.omega0_pos`：omega0_pos : 0 < ω
· 使用定理 `ONote.omega0_le_oadd`：omega0_le_oadd (e n a) : ω ^ repr e <= repr (oadd 
e n a)
-/
theorem oadd_pos (e n a) : 0 < oadd e n a :=
  @lt_of_lt_of_le _ _ _ (ω ^ repr e) _ (opow_pos (repr e) omega0_pos) (omega0_le_oadd e n a)

/-- Comparison of ordinal notations:

`ω ^ e₁ * n₁ + a₁` is less than `ω ^ e₂ * n₂ + a₂` when either `e₁ < e₂`, or `e₁ = e₂` and
`n₁ < n₂`, or `e₁ = e₂`, `n₁ = n₂`, and `a₁ < a₂`. -/
/-
**ONote.cmp** 是 Mathlib 中的一个定义，位于命名空间 `ONote`。
形式化陈述：ONote → ONote → Ordering
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Comparison of ordinal notations:

`ω ^ e₁ * n₁ + a₁` is less than `ω ^ e₂ * n₂ + a₂` when either `e₁ < e₂`, or `e₁
 = e₂` and
`n₁ < n₂`, or `e₁ = e₂`, `n₁ = n₂`, and `a₁ < a₂`.
-/
def cmp : ONote → ONote → Ordering
  | 0, 0 => Ordering.eq
  | _, 0 => Ordering.gt
  | 0, _ => Ordering.lt
  | _o₁@(oadd e₁ n₁ a₁), _o₂@(oadd e₂ n₂ a₂) =>
    (cmp e₁ e₂).then <| (_root_.cmp (n₁ : ℕ) n₂).then (cmp a₁ a₂)
/-
**ONote.eq_of_cmp_eq** 是 Mathlib 中的一个定理，位于命名空间 `ONote`。
形式化陈述：eq_of_cmp_eq : forall {o₁ o₂}, cmp o₁ o₂ = Ordering.eq -> o₁ = o₂ | 0, 0, 
_ => rfl | oadd e n a, 0, h => by injection h | 0, oadd e n a, h => by injection
 h | oadd e₁ n₁ a₁, oadd e₂ n₂ a₂, h => by revert h; simp only [cmp] cases h₁ : 
cmp e₁ e₂ <;> intro h <;> try cases h obtain rfl
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eq_of_cmp_eq : ∀ {o₁ o₂}, cmp o₁ o₂ = Ordering.eq → o₁ = o₂
  | 0, 0, _ => rfl
  | oadd e n a, 0, h => by injection h
  | 0, oadd e n a, h => by injection h
  | oadd e₁ n₁ a₁, oadd e₂ n₂ a₂, h => by
    revert h; simp only [cmp]
    cases h₁ : cmp e₁ e₂ <;> intro h <;> try cases h
    obtain rfl := eq_of_cmp_eq h₁
    revert h; cases h₂ : _root_.cmp (n₁ : ℕ) n₂ <;> intro h <;> try cases h
    obtain rfl := eq_of_cmp_eq h
    rw [_root_.cmp, cmpUsing_eq_eq, not_lt, not_lt, ← le_antisymm_iff] at h₂
    obtain rfl := Subtype.ext h₂
    simp
/-
**ONote.zero_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `ONote`。
形式化陈述：0 < 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ONote.repr_one`：ONote.repr 1 = ↑1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `instZeroLEOneClassOfIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α] [inst
_1 : Zero α] [inst_2 : One α] [IsBotZeroClass α], ZeroLEOneClass α
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
-/
protected theorem zero_lt_one : (0 : ONote) < 1 := by
  simp only [lt_def, repr_zero, repr_one, Nat.cast_one, zero_lt_one]

/-- `NFBelow o b` says that `o` is a normal form ordinal notation satisfying `repr o < ω ^ b`. -/
/-
**ONote.NFBelow** 是 Mathlib 中的一个归纳类型，位于命名空间 `ONote`。
形式化陈述：ONote → Ordinal.{0} → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`NFBelow o b` says that `o` is a normal form ordinal notation satisfying `repr o
 < ω ^ b`.
-/
inductive NFBelow : ONote → Ordinal.{0} → Prop
  | zero {b} : NFBelow 0 b
  | oadd' {e n a eb b} : NFBelow e eb → NFBelow a (repr e) → repr e < b → NFBelow (oadd e n a) b

/-- A normal form ordinal notation has the form

`ω ^ a₁ * n₁ + ω ^ a₂ * n₂ + ⋯ + ω ^ aₖ * nₖ`

where `a₁ > a₂ > ⋯ > aₖ` and all the `aᵢ` are also in normal form.

We will essentially only be interested in normal form ordinal notations, but to avoid complicating
the algorithms, we define everything over general ordinal notations and only prove correctness with
normal form as an invariant. -/
/-
**ONote.NF** 是 Mathlib 中的一个归纳类型，位于命名空间 `ONote`。
形式化陈述：ONote → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A normal form ordinal notation has the form

`ω ^ a₁ * n₁ + ω ^ a₂ * n₂ + ⋯ + ω ^ aₖ * nₖ`

where `a₁ > a₂ > ⋯ > aₖ` and all the `aᵢ` are also in normal form.

We will essentially only be interested in normal form ordinal notations, but to 
avoid complicating
the algorithms, we define everything over general ordinal notations and only pro
ve correctness with
normal form as an invariant.
-/
class NF (o : ONote) : Prop where
  out : Exists (NFBelow o)
/-
**ONote.NF.zero** 是 Mathlib 中的一个定理，位于命名空间 `ONote.NF`。
形式化陈述：ONote.NF 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance NF.zero : NF 0 :=
  ⟨⟨0, NFBelow.zero⟩⟩
/-
**ONote.NFBelow.oadd** 是 Mathlib 中的一个定理，位于命名空间 `ONote.NFBelow`。
形式化陈述：∀ {e : ONote} {n : ℕ+} {a : ONote} {b : Ordinal.{0}}, e.NF → a.NFBelow e.r
epr → e.repr < b → (e.oadd n a).NFBelow b
参数：e.oadd n a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem NFBelow.oadd {e n a b} : NF e → NFBelow a (repr e) → repr e < b → NFBelow (oadd e n a) b
  | ⟨⟨_, h⟩⟩ => NFBelow.oadd' h
/-
**ONote.NFBelow.fst** 是 Mathlib 中的一个定理，位于命名空间 `ONote.NFBelow`。
形式化陈述：∀ {e : ONote} {n : ℕ+} {a : ONote} {b : Ordinal.{0}}, (e.oadd n a).NFBelow
 b → e.NF
参数：e.oadd n a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem NFBelow.fst {e n a b} (h : NFBelow (ONote.oadd e n a) b) : NF e := by
  obtain - | ⟨h₁, h₂, h₃⟩ := h; exact ⟨⟨_, h₁⟩⟩
/-
**ONote.NF.fst** 是 Mathlib 中的一个定理，位于命名空间 `ONote.NF`。
形式化陈述：∀ {e : ONote} {n : ℕ+} {a : ONote}, (e.oadd n a).NF → e.NF
参数：e.oadd n a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ONote.NFBelow.fst`：∀ {e : ONote} {n : ℕ+} {a : ONote} {b : Ordinal.{0}},
 (e.oadd n a).NFBelow b → e.NF
-/
theorem NF.fst {e n a} : NF (oadd e n a) → NF e
  | ⟨⟨_, h⟩⟩ => h.fst
/-
**ONote.NFBelow.snd** 是 Mathlib 中的一个定理，位于命名空间 `ONote.NFBelow`。
形式化陈述：∀ {e : ONote} {n : ℕ+} {a : ONote} {b : Ordinal.{0}}, (e.oadd n a).NFBelow
 b → a.NFBelow e.repr
参数：e.oadd n a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem NFBelow.snd {e n a b} (h : NFBelow (ONote.oadd e n a) b) : NFBelow a (repr e) := by
  obtain - | ⟨h₁, h₂, h₃⟩ := h; exact h₂
/-
**ONote.NF.snd'** 是 Mathlib 中的一个定理，位于命名空间 `ONote.NF`。
形式化陈述：∀ {e : ONote} {n : ℕ+} {a : ONote}, (e.oadd n a).NF → a.NFBelow e.repr
参数：e.oadd n a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ONote.NFBelow.snd`：∀ {e : ONote} {n : ℕ+} {a : ONote} {b : Ordinal.{0}},
 (e.oadd n a).NFBelow b → a.NFBelow e.repr
-/
theorem NF.snd' {e n a} : NF (oadd e n a) → NFBelow a (repr e)
  | ⟨⟨_, h⟩⟩ => h.snd
/-
**ONote.NF.snd** 是 Mathlib 中的一个定理，位于命名空间 `ONote.NF`。
形式化陈述：∀ {e : ONote} {n : ℕ+} {a : ONote}, (e.oadd n a).NF → a.NF
参数：e.oadd n a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ONote.NF.snd'`：∀ {e : ONote} {n : ℕ+} {a : ONote}, (e.oadd n a).NF → a.N
FBelow e.repr
-/
theorem NF.snd {e n a} (h : NF (oadd e n a)) : NF a :=
  ⟨⟨_, h.snd'⟩⟩
/-
**ONote.NF.oadd** 是 Mathlib 中的一个定理，位于命名空间 `ONote.NF`。
形式化陈述：∀ {e a : ONote}, e.NF → ∀ (n : ℕ+), a.NFBelow e.repr → (e.oadd n a).NF
参数：n : ℕ+；e.oadd n a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ONote.NFBelow.oadd`：∀ {e : ONote} {n : ℕ+} {a : ONote} {b : Ordinal.{0}}
, e.NF → a.NFBelow e.repr → e.repr < b → (e.oadd n a).NFBelow b
· 使用定理 `Order.lt_succ`：lt_succ (a : α) : a < succ a
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
-/
theorem NF.oadd {e a} (h₁ : NF e) (n) (h₂ : NFBelow a (repr e)) : NF (oadd e n a) :=
  ⟨⟨_, NFBelow.oadd h₁ h₂ (lt_succ _)⟩⟩
/-
**ONote.NF.oadd_zero** 是 Mathlib 中的一个定理，位于命名空间 `ONote.NF`。
形式化陈述：∀ (e : ONote) (n : ℕ+) [h : e.NF], (e.oadd n 0).NF
参数：e : ONote；n : ℕ+；e.oadd n 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ONote.NF.oadd`：∀ {e a : ONote}, e.NF → ∀ (n : ℕ+), a.NFBelow e.repr → (e
.oadd n a).NF
-/
instance NF.oadd_zero (e n) [h : NF e] : NF (ONote.oadd e n 0) :=
  h.oadd _ NFBelow.zero
/-
**ONote.NFBelow.lt** 是 Mathlib 中的一个定理，位于命名空间 `ONote.NFBelow`。
形式化陈述：∀ {e : ONote} {n : ℕ+} {a : ONote} {b : Ordinal.{0}}, (e.oadd n a).NFBelow
 b → e.repr < b
参数：e.oadd n a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem NFBelow.lt {e n a b} (h : NFBelow (ONote.oadd e n a) b) : repr e < b := by
  obtain - | ⟨h₁, h₂, h₃⟩ := h; exact h₃
/-
**ONote.NFBelow_zero** 是 Mathlib 中的一个定理，位于命名空间 `ONote`。
形式化陈述：∀ {o : ONote}, o.NFBelow 0 ↔ o = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `ONote.NFBelow.lt`：∀ {e : ONote} {n : ℕ+} {a : ONote} {b : Ordinal.{0}}, 
(e.oadd n a).NFBelow b → e.repr < b
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem NFBelow_zero : ∀ {o}, NFBelow o 0 ↔ o = 0
  | 0 => ⟨fun _ => rfl, fun _ => NFBelow.zero⟩
  | oadd _ _ _ =>
    ⟨fun h => (not_le_of_gt h.lt).elim zero_le, fun e => e.symm ▸ NFBelow.zero⟩
/-
**ONote.NF.zero_of_zero** 是 Mathlib 中的一个定理，位于命名空间 `ONote.NF`。
形式化陈述：∀ {e : ONote} {n : ℕ+} {a : ONote}, (e.oadd n a).NF → e = 0 → a = 0
参数：e.oadd n a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ONote.NF.snd'`：∀ {e : ONote} {n : ℕ+} {a : ONote}, (e.oadd n a).NF → a.N
FBelow e.repr
-/
theorem NF.zero_of_zero {e n a} (h : NF (ONote.oadd e n a)) (e0 : e = 0) : a = 0 := by
  simpa [e0, NFBelow_zero] using h.snd'
/-
**ONote.NFBelow.repr_lt** 是 Mathlib 中的一个定理，位于命名空间 `ONote.NFBelow`。
形式化陈述：∀ {o : ONote} {b : Ordinal.{0}}, o.NFBelow b → o.repr < Ordinal.omega0 ^ b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.opow_pos`：opow_pos {a : Ordinal} (b : Ordinal) (a0 : 0 < a) : 0 
< a ^ b
· 使用定理 `Ordinal.omega0_pos`：omega0_pos : 0 < ω
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ONote.repr.eq_2`：∀ (e : ONote) (n : ℕ+) (a : ONote), (e.oadd n a).repr =
 Ordinal.omega0 ^ e.repr * ↑↑n + a.repr
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `add_lt_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [AddLe
ftStrictMono α] {b c : α}, b < c → ∀ (a : α), a + b < a + c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.mul_succ`：mul_succ (a b : Ordinal) : a * succ b = a * b + a
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Order.succ_le_of_lt`：succ_le_of_lt {a b : α} : a < b -> succ a <= b
· 使用定理 `Ordinal.natCast_lt_omega0`：natCast_lt_omega0 (n : Nat) : ↑n < ω
· 使用定理 `Ordinal.opow_succ`：opow_succ (a b : Ordinal) : a ^ succ b = a ^ b * a
· 使用定理 `Ordinal.opow_le_opow`：opow_le_opow {a b c d : Ordinal} (hac : a <= c) (h
bd : b <= d) (hc : 0 < c) : a ^ b <= c ^ d
-/
theorem NFBelow.repr_lt {o b} (h : NFBelow o b) : repr o < ω ^ b := by
  induction h with
  | zero => exact opow_pos _ omega0_pos
  | oadd' _ _ h₃ _ IH =>
    rw [repr]
    apply (add_lt_add_right IH _).trans_le
    grw [← mul_succ, succ_le_of_lt (natCast_lt_omega0 _), ← opow_succ, succ_le_of_lt h₃]
    exact omega0_pos
/-
**ONote.NFBelow.mono** 是 Mathlib 中的一个定理，位于命名空间 `ONote.NFBelow`。
形式化陈述：∀ {o : ONote} {b₁ b₂ : Ordinal.{0}}, b₁ ≤ b₂ → o.NFBelow b₁ → o.NFBelow b₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
-/
theorem NFBelow.mono {o b₁ b₂} (bb : b₁ ≤ b₂) (h : NFBelow o b₁) : NFBelow o b₂ := by
  induction h with
  | zero => exact zero
  | oadd' h₁ h₂ h₃ _ _ => constructor; exacts [h₁, h₂, lt_of_lt_of_le h₃ bb]
/-
**ONote.NF.below_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `ONote.NF`。
形式化陈述：∀ {e : ONote} {n : ℕ+} {a : ONote} {b : Ordinal.{0}}, e.repr < b → (e.oadd
 n a).NF → (e.oadd n a).NFBelow b
参数：e.oadd n a；e.oadd n a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem NF.below_of_lt {e n a b} (H : repr e < b) :
    NF (ONote.oadd e n a) → NFBelow (ONote.oadd e n a) b
  | ⟨⟨b', h⟩⟩ => by (obtain - | ⟨h₁, h₂, h₃⟩ := h; exact NFBelow.oadd' h₁ h₂ H)
/-
**ONote.NF.below_of_lt'** 是 Mathlib 中的一个定理，位于命名空间 `ONote.NF`。
形式化陈述：∀ {o : ONote} {b : Ordinal.{0}}, o.repr < Ordinal.omega0 ^ b → o.NF → o.NF
Below b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ONote.NF.below_of_lt`：∀ {e : ONote} {n : ℕ+} {a : ONote} {b : Ordinal.{0
}}, e.repr < b → (e.oadd n a).NF → (e.oadd n a).NFBelow b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ordinal.opow_lt_opow_iff_right`：opow_lt_opow_iff_right {a b c : Ordinal}
 (a1 : 1 < a) : a ^ b < a ^ c ↔ b < c
· 使用定理 `Ordinal.one_lt_omega0`：one_lt_omega0 : 1 < ω
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `ONote.omega0_le_oadd`：omega0_le_oadd (e n a) : ω ^ repr e <= repr (oadd 
e n a)
-/
theorem NF.below_of_lt' : ∀ {o b}, repr o < ω ^ b → NF o → NFBelow o b
  | 0, _, _, _ => NFBelow.zero
  | ONote.oadd _ _ _, _, H, h =>
    h.below_of_lt <|
      (opow_lt_opow_iff_right one_lt_omega0).1 <| lt_of_le_of_lt (omega0_le_oadd _ _ _) H
/-
**ONote.nfBelow_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `ONote`。
形式化陈述：∀ (n : ℕ), (↑n).NFBelow 1
参数：n : ℕ；↑n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ONote.NFBelow.oadd`：∀ {e : ONote} {n : ℕ+} {a : ONote} {b : Ordinal.{0}}
, e.NF → a.NFBelow e.repr → e.repr < b → (e.oadd n a).NFBelow b
· 使用定理 `ONote.NF.zero`：ONote.NF 0
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `instZeroLEOneClassOfIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α] [inst
_1 : Zero α] [inst_2 : One α] [IsBotZeroClass α], ZeroLEOneClass α
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
-/
theorem nfBelow_ofNat : ∀ n, NFBelow (ofNat n) 1
  | 0 => NFBelow.zero
  | Nat.succ _ => NFBelow.oadd NF.zero NFBelow.zero zero_lt_one
/-
**ONote.nf_ofNat** 是 Mathlib 中的一个实例，位于命名空间 `ONote`。
形式化陈述：nf_ofNat (n) : NF (ofNat n)
参数：n。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ONote.nfBelow_ofNat`：∀ (n : ℕ), (↑n).NFBelow 1
-/
instance nf_ofNat (n) : NF (ofNat n) :=
  ⟨⟨_, nfBelow_ofNat n⟩⟩
/-
**ONote.nf_one** 是 Mathlib 中的一个实例，位于命名空间 `ONote`。
形式化陈述：nf_one : NF 1
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ONote.ofNat_one`：↑1 = 1
-/
instance nf_one : NF 1 := by rw [← ofNat_one]; infer_instance
/-
**ONote.oadd_lt_oadd_1** 是 Mathlib 中的一个定理，位于命名空间 `ONote`。
形式化陈述：oadd_lt_oadd_1 {e₁ n₁ o₁ e₂ n₂ o₂} (h₁ : NF (oadd e₁ n₁ o₁)) (h : e₁ < e₂)
 : oadd e₁ n₁ o₁ < oadd e₂ n₂ o₂
参数：h₁ : NF (oadd e₁ n₁ o₁)；h : e₁ < e₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `ONote.NFBelow.repr_lt`：∀ {o : ONote} {b : Ordinal.{0}}, o.NFBelow b → o.
repr < Ordinal.omega0 ^ b
· 使用定理 `ONote.NF.below_of_lt`：∀ {e : ONote} {n : ℕ+} {a : ONote} {b : Ordinal.{0
}}, e.repr < b → (e.oadd n a).NF → (e.oadd n a).NFBelow b
· 使用定理 `ONote.omega0_le_oadd`：omega0_le_oadd (e n a) : ω ^ repr e <= repr (oadd 
e n a)
-/
theorem oadd_lt_oadd_1 {e₁ n₁ o₁ e₂ n₂ o₂} (h₁ : NF (oadd e₁ n₁ o₁)) (h : e₁ < e₂) :
    oadd e₁ n₁ o₁ < oadd e₂ n₂ o₂ :=
  @lt_of_lt_of_le _ _ (repr (oadd e₁ n₁ o₁)) _ _
    (NF.below_of_lt h h₁).repr_lt (omega0_le_oadd e₂ n₂ o₂)
/-
**ONote.oadd_lt_oadd_2** 是 Mathlib 中的一个定理，位于命名空间 `ONote`。
形式化陈述：oadd_lt_oadd_2 {e o₁ o₂ : ONote} {n₁ n₂ : Nat+} (h₁ : NF (oadd e n₁ o₁)) (
h : (n₁ : Nat) < n₂) : oadd e n₁ o₁ < oadd e n₂ o₂
参数：h₁ : NF (oadd e n₁ o₁)；h : (n₁ : Nat) < n₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `add_lt_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [AddLe
ftStrictMono α] {b c : α}, b < c → ∀ (a : α), a + b < a + c
· 使用定理 `ONote.NFBelow.repr_lt`：∀ {o : ONote} {b : Ordinal.{0}}, o.NFBelow b → o.
repr < Ordinal.omega0 ^ b
· 使用定理 `ONote.NF.snd'`：∀ {e : ONote} {n : ℕ+} {a : ONote}, (e.oadd n a).NF → a.N
FBelow e.repr
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `le_self_add`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ a + b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.mul_succ`：mul_succ (a b : Ordinal) : a * succ b = a * b + a
· 使用定理 `mul_le_mul_iff_right₀`：mul_le_mul_iff_right₀ [PosMulMono α] [PosMulRefle
ctLE α] (a0 : 0 < a) : a * b <= a * c ↔ b <= c
· 使用定理 `PosMulStrictMono.toPosMulMono`：∀ {α : Type u_1} [inst : MulZeroClass α] 
[inst_1 : PartialOrder α] [PosMulStrictMono α], PosMulMono α
· 使用定理 `Ordinal.instPosMulStrictMono`：PosMulStrictMono Ordinal.{u_4}
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `Ordinal.opow_pos`：opow_pos {a : Ordinal} (b : Ordinal) (a0 : 0 < a) : 0 
< a ^ b
· 使用定理 `Ordinal.omega0_pos`：omega0_pos : 0 < ω
· 使用定理 `Order.succ_le_iff`：succ_le_iff : succ a <= b ↔ a < b
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `Nat.cast_lt`：cast_lt : (m : α) < n ↔ m < n
· 使用定理 `instZeroLEOneClassOfIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α] [inst
_1 : Zero α] [inst_2 : One α] [IsBotZeroClass α], ZeroLEOneClass α
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
-/
theorem oadd_lt_oadd_2 {e o₁ o₂ : ONote} {n₁ n₂ : ℕ+} (h₁ : NF (oadd e n₁ o₁)) (h : (n₁ : ℕ) < n₂) :
    oadd e n₁ o₁ < oadd e n₂ o₂ := by
  simp only [lt_def, repr]
  grw [h₁.snd'.repr_lt, ← le_self_add]
  rwa [← mul_succ, mul_le_mul_iff_right₀ (opow_pos _ omega0_pos), succ_le_iff, Nat.cast_lt]
/-
**ONote.oadd_lt_oadd_3** 是 Mathlib 中的一个定理，位于命名空间 `ONote`。
形式化陈述：oadd_lt_oadd_3 {e n a₁ a₂} (h : a₁ < a₂) : oadd e n a₁ < oadd e n a₂
参数：h : a₁ < a₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ONote.lt_def`：lt_def {x y : ONote} : x < y ↔ repr x < repr y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ONote.repr.eq_def`：∀ (x : ONote),   x.repr =     match x with     | ONot
e.zero => 0     | e.oadd n a => Ordinal.omega0 ^ e.repr * ↑↑n + a.repr
· 使用定理 `add_lt_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [AddLe
ftStrictMono α] {b c : α}, b < c → ∀ (a : α), a + b < a + c
· 使用定理 `ONote.repr_lt_repr`：∀ {x y : ONote}, x < y → x.repr < y.repr
-/
theorem oadd_lt_oadd_3 {e n a₁ a₂} (h : a₁ < a₂) : oadd e n a₁ < oadd e n a₂ := by
  rw [lt_def]; unfold repr; gcongr
/-
**ONote.cmp_compares** 是 Mathlib 中的一个定理，位于命名空间 `ONote`。
形式化陈述：cmp_compares : forall (a b : ONote) [NF a] [NF b], (cmp a b).Compares a b 
| 0, 0, _, _ => rfl | oadd _ _ _, 0, _, _ => oadd_pos _ _ _ | 0, oadd _ _ _, _, 
_ => oadd_pos _ _ _ | o₁@(oadd e₁ n₁ a₁), o₂@(oadd e₂ n₂ a₂), h₁, h₂ => by -- TO
DO: golf rw [cmp] have IHe
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cmp_compares : ∀ (a b : ONote) [NF a] [NF b], (cmp a b).Compares a b
  | 0, 0, _, _ => rfl
  | oadd _ _ _, 0, _, _ => oadd_pos _ _ _
  | 0, oadd _ _ _, _, _ => oadd_pos _ _ _
  | o₁@(oadd e₁ n₁ a₁), o₂@(oadd e₂ n₂ a₂), h₁, h₂ => by -- TODO: golf
    rw [cmp]
    have IHe := @cmp_compares _ _ h₁.fst h₂.fst
    simp only [Ordering.Compares, gt_iff_lt] at IHe; revert IHe
    cases cmp e₁ e₂
    case lt => intro IHe; exact oadd_lt_oadd_1 h₁ IHe
    case gt => intro IHe; exact oadd_lt_oadd_1 h₂ IHe
    case eq =>
      intro IHe; dsimp at IHe; subst IHe
      unfold _root_.cmp; cases nh : cmpUsing (· < ·) (n₁ : ℕ) n₂ <;>
      rw [cmpUsing, ite_eq_iff, not_lt] at nh
      case lt =>
        rcases nh with nh | nh
        · exact oadd_lt_oadd_2 h₁ nh.left
        · rw [ite_eq_iff] at nh; rcases nh.right with nh | nh <;> cases nh <;> contradiction
      case gt =>
        rcases nh with nh | nh
        · cases nh; contradiction
        · obtain ⟨_, nh⟩ := nh
          rw [ite_eq_iff] at nh; rcases nh with nh | nh
          · exact oadd_lt_oadd_2 h₂ nh.left
          · cases nh; contradiction
      rcases nh with nh | nh
      · cases nh; contradiction
      obtain ⟨nhl, nhr⟩ := nh
      rw [ite_eq_iff] at nhr
      rcases nhr with nhr | nhr
      · cases nhr; contradiction
      obtain rfl := Subtype.ext (nhl.eq_of_not_lt nhr.1)
      have IHa := @cmp_compares _ _ h₁.snd h₂.snd
      revert IHa; cases cmp a₁ a₂ <;> intro IHa <;> dsimp at IHa
      case lt => exact oadd_lt_oadd_3 IHa
      case gt => exact oadd_lt_oadd_3 IHa
      subst IHa; exact rfl
/-
**ONote.repr_inj** 是 Mathlib 中的一个定理，位于命名空间 `ONote`。
形式化陈述：repr_inj {a b} [NF a] [NF b] : repr a = repr b ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ONote.cmp_compares`：cmp_compares : forall (a b : ONote) [NF a] [NF b], (
cmp a b).Compares a b | 0, 0, _, _ => rfl | oadd _ _ _, 0, _, _ => oadd_pos _ _ 
_ | 0, o…
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem repr_inj {a b} [NF a] [NF b] : repr a = repr b ↔ a = b :=
  ⟨fun e => match cmp a b, cmp_compares a b with
    | Ordering.lt, (h : repr a < repr b) => (ne_of_lt h e).elim
    | Ordering.gt, (h : repr a > repr b)=> (ne_of_gt h e).elim
    | Ordering.eq, h => h,
    congr_arg _⟩
/-
**ONote.NF.of_dvd_omega0_opow** 是 Mathlib 中的一个定理，位于命名空间 `ONote.NF`。
形式化陈述：∀ {b : Ordinal.{0}} {e : ONote} {n : ℕ+} {a : ONote},   (e.oadd n a).NF → 
Ordinal.omega0 ^ b ∣ (e.oadd n a).repr → b ≤ e.repr ∧ Ordinal.omega0 ^ b ∣ a.rep
r
参数：e.oadd n a；e.oadd n a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ONote.repr_inj`：repr_inj {a b} [NF a] [NF b] : repr a = repr b ↔ a = b
· 使用定理 `ONote.NF.zero`：ONote.NF 0
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `ONote.NFBelow.repr_lt`：∀ {o : ONote} {b : Ordinal.{0}}, o.NFBelow b → o.
repr < Ordinal.omega0 ^ b
· 使用定理 `ONote.NF.below_of_lt`：∀ {e : ONote} {n : ℕ+} {a : ONote} {b : Ordinal.{0
}}, e.repr < b → (e.oadd n a).NF → (e.oadd n a).NFBelow b
· 使用定理 `Ordinal.le_of_dvd`：le_of_dvd {a b : Ordinal} (b0 : b != 0) (h : a ∣ b) :
 a <= b
· 使用定理 `Ordinal.dvd_add_iff`：∀ {a b c : Ordinal.{u_4}}, a ∣ b → (a ∣ b + c ↔ a ∣
 c)
· 使用定理 `Dvd.dvd.mul_right`：∀ {α : Type u_1} [inst : Semigroup α] {a b : α}, a ∣ 
b → ∀ (c : α), a ∣ b * c
· 使用定理 `Ordinal.opow_dvd_opow`：opow_dvd_opow (a : Ordinal) {b c : Ordinal} (h : 
b <= c) : a ^ b ∣ a ^ c
-/
theorem NF.of_dvd_omega0_opow {b e n a} (h : NF (ONote.oadd e n a))
    (d : ω ^ b ∣ repr (ONote.oadd e n a)) :
    b ≤ repr e ∧ ω ^ b ∣ repr a := by
  have := mt repr_inj.1 (fun h => by injection h : ONote.oadd e n a ≠ 0)
  have L := le_of_not_gt fun l => not_le_of_gt (h.below_of_lt l).repr_lt (le_of_dvd this d)
  simp only [repr] at d
  exact ⟨L, (dvd_add_iff <| (opow_dvd_opow _ L).mul_right _).1 d⟩
/-
**ONote.NF.of_dvd_omega0** 是 Mathlib 中的一个定理，位于命名空间 `ONote.NF`。
形式化陈述：∀ {e : ONote} {n : ℕ+} {a : ONote},   (e.oadd n a).NF → Ordinal.omega0 ∣ (
e.oadd n a).repr → e.repr ≠ 0 ∧ Ordinal.omega0 ∣ a.repr
参数：e.oadd n a；e.oadd n a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.opow_one`：opow_one (a : Ordinal) : a ^ (1 : Ordinal) = a
· 使用定理 `Order.one_le_iff_ne_zero`：one_le_iff_ne_zero [AddMonoidWithOne α] [NeZer
o (1 : α)] [SuccAddOrder α] [IsBotZeroClass α] : 1 <= x ↔ x != 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ONote.NF.of_dvd_omega0_opow`：∀ {b : Ordinal.{0}} {e : ONote} {n : ℕ+} {a
 : ONote},   (e.oadd n a).NF → Ordinal.omega0 ^ b ∣ (e.oadd n a).repr → b ≤ e.re
pr ∧ Ordinal.omeg…
-/
theorem NF.of_dvd_omega0 {e n a} (h : NF (ONote.oadd e n a)) :
    ω ∣ repr (ONote.oadd e n a) → repr e ≠ 0 ∧ ω ∣ repr a := by
  (rw [← opow_one ω, ← one_le_iff_ne_zero]; exact h.of_dvd_omega0_opow)

/-- `TopBelow b o` asserts that the largest exponent in `o`, if it exists, is less than `b`. This is
an auxiliary definition for decidability of `NF`. -/
/-
**ONote.TopBelow** 是 Mathlib 中的一个定义，位于命名空间 `ONote`。
形式化陈述：ONote → ONote → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`TopBelow b o` asserts that the largest exponent in `o`, if it exists, is less t
han `b`. This is
an auxiliary definition for decidability of `NF`.
-/
def TopBelow (b : ONote) : ONote → Prop
  | 0 => True
  | oadd e _ _ => cmp e b = Ordering.lt
/-
**ONote.decidableTopBelow** 是 Mathlib 中的一个实例，位于命名空间 `ONote`。
形式化陈述：decidableTopBelow : DecidableRel TopBelow
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
instance decidableTopBelow : DecidableRel TopBelow := by
  intro b o
  cases o <;> delta TopBelow <;> infer_instance
/-
**ONote.nfBelow_iff_topBelow** 是 Mathlib 中的一个定理，位于命名空间 `ONote`。
形式化陈述：∀ {b : ONote} [b.NF] {o : ONote}, o.NFBelow b.repr ↔ o.NF ∧ b.TopBelow o
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ordering.Compares.eq_lt`：∀ {α : Type u_1} [inst : Preorder α] {o : Order
ing} {a b : α}, o.Compares a b → (o = Ordering.lt ↔ a < b)
· 使用定理 `ONote.cmp_compares`：cmp_compares : forall (a b : ONote) [NF a] [NF b], (
cmp a b).Compares a b | 0, 0, _, _ => rfl | oadd _ _ _, 0, _, _ => oadd_pos _ _ 
_ | 0, o…
· 使用定理 `ONote.NFBelow.fst`：∀ {e : ONote} {n : ℕ+} {a : ONote} {b : Ordinal.{0}},
 (e.oadd n a).NFBelow b → e.NF
· 使用定理 `ONote.NFBelow.lt`：∀ {e : ONote} {n : ℕ+} {a : ONote} {b : Ordinal.{0}}, 
(e.oadd n a).NFBelow b → e.repr < b
· 使用定理 `ONote.NF.below_of_lt`：∀ {e : ONote} {n : ℕ+} {a : ONote} {b : Ordinal.{0
}}, e.repr < b → (e.oadd n a).NF → (e.oadd n a).NFBelow b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ONote.NF.fst`：∀ {e : ONote} {n : ℕ+} {a : ONote}, (e.oadd n a).NF → e.NF
-/
theorem nfBelow_iff_topBelow {b} [NF b] : ∀ {o}, NFBelow o (repr b) ↔ NF o ∧ TopBelow b o
  | 0 => ⟨fun h => ⟨⟨⟨_, h⟩⟩, trivial⟩, fun _ => NFBelow.zero⟩
  | oadd _ _ _ =>
    ⟨fun h => ⟨⟨⟨_, h⟩⟩, (@cmp_compares _ b h.fst _).eq_lt.2 h.lt⟩, fun ⟨h₁, h₂⟩ =>
      h₁.below_of_lt <| (@cmp_compares _ b h₁.fst _).eq_lt.1 h₂⟩
/-
**ONote.decidableNF** 是 Mathlib 中的一个实例，位于命名空间 `ONote`。
形式化陈述：decidableNF : DecidablePred NF | 0 => isTrue NF.zero | oadd e n a => by ha
ve
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableNF : DecidablePred NF
  | 0 => isTrue NF.zero
  | oadd e n a => by
    have := decidableNF e
    have := decidableNF a
    apply decidable_of_iff (NF e ∧ NF a ∧ TopBelow e a)
    rw [← and_congr_right fun h => @nfBelow_iff_topBelow _ h _]
    exact ⟨fun ⟨h₁, h₂⟩ => NF.oadd h₁ n h₂, fun h => ⟨h.fst, h.snd'⟩⟩

/-- Auxiliary definition for `add` -/
/-
**ONote.addAux** 是 Mathlib 中的一个定义，位于命名空间 `ONote`。
形式化陈述：addAux (e : ONote) (n : Nat+) (o : ONote) : ONote
参数：e : ONote；n : Nat+；o : ONote。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `add`
-/
def addAux (e : ONote) (n : ℕ+) (o : ONote) : ONote :=
    match o with
    | 0 => oadd e n 0
    | o'@(oadd e' n' a') =>
      match cmp e e' with
      | Ordering.lt => o'
      | Ordering.eq => oadd e (n + n') a'
      | Ordering.gt => oadd e n o'

/-- Addition of ordinal notations (correct only for normal input) -/
/-
**ONote.add** 是 Mathlib 中的一个定义，位于命名空间 `ONote`。
形式化陈述：ONote → ONote → ONote
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Addition of ordinal notations (correct only for normal input)
-/
def add : ONote → ONote → ONote
  | 0, o => o
  | oadd e n a, o => addAux e n (add a o)
/-
**ONote.** 是 Mathlib 中的一个实例，位于命名空间 `ONote`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Add ONote :=
  ⟨add⟩

@[simp]
/-
**ONote.zero_add** 是 Mathlib 中的一个定理，位于命名空间 `ONote`。
形式化陈述：zero_add (o : ONote) : 0 + o = o
参数：o : ONote。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_add (o : ONote) : 0 + o = o :=
  rfl
/-
**ONote.oadd_add** 是 Mathlib 中的一个定理，位于命名空间 `ONote`。
形式化陈述：oadd_add (e n a o) : oadd e n a + o = addAux e n (a + o)
参数：e n a o。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem oadd_add (e n a o) : oadd e n a + o = addAux e n (a + o) :=
  rfl

/-- Subtraction of ordinal notations (correct only for normal input) -/
/-
**ONote.sub** 是 Mathlib 中的一个定义，位于命名空间 `ONote`。
形式化陈述：ONote → ONote → ONote
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Subtraction of ordinal notations (correct only for normal input)
-/
def sub : ONote → ONote → ONote
  | 0, _ => 0
  | o, 0 => o
  | o₁@(oadd e₁ n₁ a₁), oadd e₂ n₂ a₂ =>
    match cmp e₁ e₂ with
    | Ordering.lt => 0
    | Ordering.gt => o₁
    | Ordering.eq =>
      match (n₁ : ℕ) - n₂ with
      | 0 => if n₁ = n₂ then sub a₁ a₂ else 0
      | Nat.succ k => oadd e₁ k.succPNat a₁
/-
**ONote.** 是 Mathlib 中的一个实例，位于命名空间 `ONote`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Sub ONote :=
  ⟨sub⟩
/-
**ONote.add_nfBelow** 是 Mathlib 中的一个定理，位于命名空间 `ONote`。
形式化陈述：add_nfBelow {b} : forall {o₁ o₂}, NFBelow o₁ b -> NFBelow o₂ b -> NFBelow 
(o₁ + o₂) b | 0, _, _, h₂ => h₂ | oadd e n a, o, h₁, h₂ => by have h'
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem add_nfBelow {b} : ∀ {o₁ o₂}, NFBelow o₁ b → NFBelow o₂ b → NFBelow (o₁ + o₂) b
  | 0, _, _, h₂ => h₂
  | oadd e n a, o, h₁, h₂ => by
    have h' := add_nfBelow (h₁.snd.mono <| le_of_lt h₁.lt) h₂
    simp only [oadd_add]; revert h'; obtain - | ⟨e', n', a'⟩ := a + o <;> intro h'
    · exact NFBelow.oadd h₁.fst NFBelow.zero h₁.lt
    have : ((e.cmp e').Compares e e') := @cmp_compares _ _ h₁.fst h'.fst
    cases h : cmp e e' <;> dsimp [addAux] <;> simp only [h]
    · exact h'
    · simp only [h] at this
      subst e'
      exact NFBelow.oadd h'.fst h'.snd h'.lt
    · simp only [h] at this
      exact NFBelow.oadd h₁.fst (NF.below_of_lt this ⟨⟨_, h'⟩⟩) h₁.lt
/-
**ONote.add_nf** 是 Mathlib 中的一个定理，位于命名空间 `ONote`。
形式化陈述：∀ (o₁ o₂ : ONote) [o₁.NF] [o₂.NF], (o₁ + o₂).NF
参数：o₁ o₂ : ONote；o₁ + o₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `ONote.add_nfBelow`：add_nfBelow {b} : forall {o₁ o₂}, NFBelow o₁ b -> NFB
elow o₂ b -> NFBelow (o₁ + o₂) b | 0, _, _, h₂ => h₂ | oadd e n a, o, h₁, h₂ => 
by have…
· 使用定理 `ONote.NFBelow.mono`：∀ {o : ONote} {b₁ b₂ : Ordinal.{0}}, b₁ ≤ b₂ → o.NFB
elow b₁ → o.NFBelow b₂
-/
instance add_nf (o₁ o₂) : ∀ [NF o₁] [NF o₂], NF (o₁ + o₂)
  | ⟨⟨b₁, h₁⟩⟩, ⟨⟨b₂, h₂⟩⟩ =>
    ⟨(le_total b₁ b₂).elim (fun h => ⟨b₂, add_nfBelow (h₁.mono h) h₂⟩) fun h =>
        ⟨b₁, add_nfBelow h₁ (h₂.mono h)⟩⟩

@[simp]
/-
**ONote.repr_add** 是 Mathlib 中的一个定理，位于命名空间 `ONote`。
形式化陈述：repr_add : forall (o₁ o₂) [NF o₁] [NF o₂], repr (o₁ + o₂) = repr o₁ + repr
 o₂ | 0, o, _, _ => by simp | oadd e n a, o, h₁, h₂ => by have
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem repr_add : ∀ (o₁ o₂) [NF o₁] [NF o₂], repr (o₁ + o₂) = repr o₁ + repr o₂
  | 0, o, _, _ => by simp
  | oadd e n a, o, h₁, h₂ => by
    have := h₁.snd; have h' := repr_add a o
    conv_lhs at h' => simp [HAdd.hAdd, Add.add]
    have nf := ONote.add_nf a o
    conv at nf => simp [HAdd.hAdd, Add.add]
    conv in _ + o => simp [HAdd.hAdd, Add.add]
    rcases h : add a o with - | ⟨e', n', a'⟩ <;>
      simp only [add, addAux, h'.symm, h, add_assoc, repr] at nf h₁ ⊢
    have := h₁.fst; have := nf.fst; have ee := cmp_compares e e'
    cases he : cmp e e' <;> simp only [he, Ordering.compares_gt, Ordering.compares_lt,
        Ordering.compares_eq, repr, gt_iff_lt, PNat.add_coe, Nat.cast_add] at ee ⊢
    · rw [← add_assoc, @add_of_omega0_opow_le _ (repr e') (ω ^ repr e' * (n' : ℕ))]
      · have := (h₁.below_of_lt ee).repr_lt
        simp only [repr] at this
        cases he' : e' <;>
          simp only [he', zero_def, opow_zero, repr, repr_zero, gt_iff_lt] at this ⊢ <;>
          exact lt_of_le_of_lt le_self_add this
      · simpa using (mul_le_mul_iff_right₀ <| opow_pos (repr e') omega0_pos).2
          (Nat.cast_le.2 n'.pos)
    · rw [ee, ← add_assoc, ← mul_add]
/-
**ONote.sub_nfBelow** 是 Mathlib 中的一个定理，位于命名空间 `ONote`。
形式化陈述：sub_nfBelow : forall {o₁ o₂ b}, NFBelow o₁ b -> NF o₂ -> NFBelow (o₁ - o₂)
 b | 0, o, b, _, h₂ => by cases o <;> exact NFBelow.zero | oadd _ _ _, 0, _, h₁,
 _ => h₁ | oadd e₁ n₁ a₁, oadd e₂ n₂ a₂, b, h₁, h₂ => by have h'
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sub_nfBelow : ∀ {o₁ o₂ b}, NFBelow o₁ b → NF o₂ → NFBelow (o₁ - o₂) b
  | 0, o, b, _, h₂ => by cases o <;> exact NFBelow.zero
  | oadd _ _ _, 0, _, h₁, _ => h₁
  | oadd e₁ n₁ a₁, oadd e₂ n₂ a₂, b, h₁, h₂ => by
    have h' := sub_nfBelow h₁.snd h₂.snd
    simp only [HSub.hSub, Sub.sub, sub] at h' ⊢
    have := @cmp_compares _ _ h₁.fst h₂.fst
    cases h : cmp e₁ e₂
    · apply NFBelow.zero
    · rw [Nat.sub_eq]
      simp only [h, Ordering.compares_eq] at this
      subst e₂
      cases (n₁ : ℕ) - n₂
      · by_cases en : n₁ = n₂ <;> simp only [en, ↓reduceIte]
        · exact h'.mono (le_of_lt h₁.lt)
        · exact NFBelow.zero
      · exact NFBelow.oadd h₁.fst h₁.snd h₁.lt
    · exact h₁
/-
**ONote.sub_nf** 是 Mathlib 中的一个定理，位于命名空间 `ONote`。
形式化陈述：∀ (o₁ o₂ : ONote) [o₁.NF] [o₂.NF], (o₁ - o₂).NF
参数：o₁ o₂ : ONote；o₁ - o₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ONote.sub_nfBelow`：sub_nfBelow : forall {o₁ o₂ b}, NFBelow o₁ b -> NF o₂
 -> NFBelow (o₁ - o₂) b | 0, o, b, _, h₂ => by cases o <;> exact NFBelow.zero | 
oadd _ …
-/
instance sub_nf (o₁ o₂) : ∀ [NF o₁] [NF o₂], NF (o₁ - o₂)
  | ⟨⟨b₁, h₁⟩⟩, h₂ => ⟨⟨b₁, sub_nfBelow h₁ h₂⟩⟩

@[simp]
/-
**ONote.repr_sub** 是 Mathlib 中的一个定理，位于命名空间 `ONote`。
形式化陈述：repr_sub : forall (o₁ o₂) [NF o₁] [NF o₂], repr (o₁ - o₂) = repr o₁ - repr
 o₂ | 0, o, _, h₂ => by cases o <;> exact (Ordinal.zero_sub _).symm | oadd _ _ _
, 0, _, _ => (Ordinal.sub_zero _).symm | oadd e₁ n₁ a₁, oadd e₂ n₂ a₂, h₁, h₂ =>
 by have
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem repr_sub : ∀ (o₁ o₂) [NF o₁] [NF o₂], repr (o₁ - o₂) = repr o₁ - repr o₂
  | 0, o, _, h₂ => by cases o <;> exact (Ordinal.zero_sub _).symm
  | oadd _ _ _, 0, _, _ => (Ordinal.sub_zero _).symm
  | oadd e₁ n₁ a₁, oadd e₂ n₂ a₂, h₁, h₂ => by
    have := h₁.snd; have := h₂.snd; have h' := repr_sub a₁ a₂
    conv_lhs at h' => dsimp [HSub.hSub, Sub.sub, sub]
    conv_lhs => dsimp only [HSub.hSub, Sub.sub]; dsimp only [sub]
    have ee := @cmp_compares _ _ h₁.fst h₂.fst
    cases h : cmp e₁ e₂ <;> simp only [h] at ee
    · rw [Ordinal.sub_eq_zero_iff_le.2]
      · rfl
      exact le_of_lt (oadd_lt_oadd_1 h₁ ee)
    · change e₁ = e₂ at ee
      subst e₂
      dsimp only
      cases mn : (n₁ : ℕ) - n₂ <;> dsimp only
      · by_cases en : n₁ = n₂
        · simpa [en]
        · simp only [en, ite_false]
          exact
            (Ordinal.sub_eq_zero_iff_le.2 <|
                le_of_lt <|
                  oadd_lt_oadd_2 h₁ <|
                    lt_of_le_of_ne (tsub_eq_zero_iff_le.1 mn) (mt PNat.eq en)).symm
      · simp only [Nat.succPNat, Nat.succ_eq_add_one, repr, PNat.mk_coe, ← succ_eq_add_one]
        rw [(tsub_eq_iff_eq_add_of_le <| le_of_lt <| Nat.lt_of_sub_eq_succ mn).1 mn, add_comm,
          Nat.cast_add, mul_add, add_assoc, add_sub_add_cancel]
        refine
          (Ordinal.sub_eq_of_add_eq <|
              add_of_omega0_opow_le h₂.snd'.repr_lt <| le_trans ?_ le_self_add).symm
        exact Ordinal.le_mul_left _ (Nat.cast_lt.2 <| Nat.succ_pos _)
    · exact
        (Ordinal.sub_eq_of_add_eq <|
            add_of_omega0_opow_le (h₂.below_of_lt ee).repr_lt <| omega0_le_oadd _ _ _).symm

/-- Multiplication of ordinal notations (correct only for normal input) -/
/-
**ONote.mul** 是 Mathlib 中的一个定义，位于命名空间 `ONote`。
形式化陈述：ONote → ONote → ONote
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multiplication of ordinal notations (correct only for normal input)
-/
def mul : ONote → ONote → ONote
  | 0, _ => 0
  | _, 0 => 0
  | o₁@(oadd e₁ n₁ a₁), oadd e₂ n₂ a₂ =>
    if e₂ = 0 then oadd e₁ (n₁ * n₂) a₁ else oadd (e₁ + e₂) n₂ (mul o₁ a₂)
/-
**ONote.** 是 Mathlib 中的一个实例，位于命名空间 `ONote`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mul ONote :=
  ⟨mul⟩
/-
**ONote.** 是 Mathlib 中的一个实例，位于命名空间 `ONote`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MulZeroClass ONote where
  zero_mul o := by cases o <;> rfl
  mul_zero o := by cases o <;> rfl
/-
**ONote.oadd_mul** 是 Mathlib 中的一个定理，位于命名空间 `ONote`。
形式化陈述：oadd_mul (e₁ n₁ a₁ e₂ n₂ a₂) : oadd e₁ n₁ a₁ * oadd e₂ n₂ a₂ = if e₂ = 0 t
hen oadd e₁ (n₁ * n₂) a₁ else oadd (e₁ + e₂) n₂ (oadd e₁ n₁ a₁ * a₂)
参数：e₁ n₁ a₁ e₂ n₂ a₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem oadd_mul (e₁ n₁ a₁ e₂ n₂ a₂) :
    oadd e₁ n₁ a₁ * oadd e₂ n₂ a₂ =
      if e₂ = 0 then oadd e₁ (n₁ * n₂) a₁ else oadd (e₁ + e₂) n₂ (oadd e₁ n₁ a₁ * a₂) :=
  rfl
/-
**ONote.oadd_mul_nfBelow** 是 Mathlib 中的一个定理，位于命名空间 `ONote`。
形式化陈述：oadd_mul_nfBelow {e₁ n₁ a₁ b₁} (h₁ : NFBelow (oadd e₁ n₁ a₁) b₁) : forall 
{o₂ b₂}, NFBelow o₂ b₂ -> NFBelow (oadd e₁ n₁ a₁ * o₂) (repr e₁ + b₂) | 0, _, _ 
=> NFBelow.zero | oadd e₂ n₂ a₂, b₂, h₂ => by have IH
参数：h₁ : NFBelow (oadd e₁ n₁ a₁) b₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem oadd_mul_nfBelow {e₁ n₁ a₁ b₁} (h₁ : NFBelow (oadd e₁ n₁ a₁) b₁) :
    ∀ {o₂ b₂}, NFBelow o₂ b₂ → NFBelow (oadd e₁ n₁ a₁ * o₂) (repr e₁ + b₂)
  | 0, _, _ => NFBelow.zero
  | oadd e₂ n₂ a₂, b₂, h₂ => by
    have IH := oadd_mul_nfBelow h₁ h₂.snd
    by_cases e0 : e₂ = 0 <;> simp only [e0, oadd_mul, ↓reduceIte]
    · apply NFBelow.oadd h₁.fst h₁.snd
      grw [← h₂.lt.pos, add_zero]
    · have := h₁.fst
      have := h₂.fst
      apply NFBelow.oadd
      · infer_instance
      · rwa [repr_add]
      · grw [repr_add, h₂.lt]
/-
**ONote.mul_nf** 是 Mathlib 中的一个定理，位于命名空间 `ONote`。
形式化陈述：∀ (o₁ o₂ : ONote) [o₁.NF] [o₂.NF], (o₁ * o₂).NF
参数：o₁ o₂ : ONote；o₁ * o₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ONote.NF.zero`：ONote.NF 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ONote.oadd_mul_nfBelow`：oadd_mul_nfBelow {e₁ n₁ a₁ b₁} (h₁ : NFBelow (oa
dd e₁ n₁ a₁) b₁) : forall {o₂ b₂}, NFBelow o₂ b₂ -> NFBelow (oadd e₁ n₁ a₁ * o₂)
 (repr e₁ + …
-/
instance mul_nf : ∀ (o₁ o₂) [NF o₁] [NF o₂], NF (o₁ * o₂)
  | 0, o, _, h₂ => by cases o <;> exact NF.zero
  | oadd _ _ _, _, ⟨⟨_, hb₁⟩⟩, ⟨⟨_, hb₂⟩⟩ => ⟨⟨_, oadd_mul_nfBelow hb₁ hb₂⟩⟩

@[simp]
/-
**ONote.repr_mul** 是 Mathlib 中的一个定理，位于命名空间 `ONote`。
形式化陈述：repr_mul : forall (o₁ o₂) [NF o₁] [NF o₂], repr (o₁ * o₂) = repr o₁ * repr
 o₂ | 0, o, _, h₂ => by cases o <;> exact (zero_mul _).symm | oadd _ _ _, 0, _, 
_ => (mul_zero _).symm | oadd e₁ n₁ a₁, oadd e₂ n₂ a₂, h₁, h₂ => by have IH : re
pr (mul _ _) = _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem repr_mul : ∀ (o₁ o₂) [NF o₁] [NF o₂], repr (o₁ * o₂) = repr o₁ * repr o₂
  | 0, o, _, h₂ => by cases o <;> exact (zero_mul _).symm
  | oadd _ _ _, 0, _, _ => (mul_zero _).symm
  | oadd e₁ n₁ a₁, oadd e₂ n₂ a₂, h₁, h₂ => by
    have IH : repr (mul _ _) = _ := @repr_mul _ _ h₁ h₂.snd
    conv =>
      lhs
      simp [(· * ·)]
    have ao : repr a₁ + ω ^ repr e₁ * (n₁ : ℕ) = ω ^ repr e₁ * (n₁ : ℕ) := by
      apply add_of_omega0_opow_le h₁.snd'.repr_lt
      simpa using! (mul_le_mul_iff_right₀ <| opow_pos _ omega0_pos).2 (Nat.cast_le.2 n₁.2)
    by_cases e0 : e₂ = 0
    · obtain ⟨x, xe⟩ := Nat.exists_eq_succ_of_ne_zero n₂.ne_zero
      simp only [Mul.mul, mul, e0, ↓reduceIte, repr, repr_zero, PNat.mul_coe, natCast_mul,
        opow_zero, one_mul]
      simp only [xe, h₂.zero_of_zero e0, repr_zero, add_zero]
      rw [Nat.cast_add_one x, add_mul_add_one _ ao, mul_assoc]
    · simp only [repr]
      have := h₁.fst
      have := h₂.fst
      simp only [Mul.mul, mul, e0, ite_false, repr.eq_2, repr_add, opow_add, IH, repr, mul_add]
      rw [← mul_assoc]
      congr 2
      have := mt repr_inj.1 e0
      rw [add_mul_of_isSuccLimit ao (isSuccLimit_opow_left isSuccLimit_omega0 this), mul_assoc,
        mul_omega0_dvd (Nat.cast_pos'.2 n₁.pos) (natCast_lt_omega0 _)]
      simpa using! opow_dvd_opow ω (one_le_iff_ne_zero.2 this)

/-- Calculate division and remainder of `o` mod `ω`:

`split' o = (a, n)` means `o = ω * a + n`. -/
/-
**ONote.split'** 是 Mathlib 中的一个定义，位于命名空间 `ONote`。
形式化陈述：split' : ONote -> ONote × Nat | 0 => (0, 0) | oadd e n a => if e = 0 then 
(0, n) else let (a', m)
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Calculate division and remainder of `o` mod `ω`:

`split' o = (a, n)` means `o = ω * a + n`.
-/
def split' : ONote → ONote × ℕ
  | 0 => (0, 0)
  | oadd e n a =>
    if e = 0 then (0, n)
    else
      let (a', m) := split' a
      (oadd (e - 1) n a', m)

/-- Calculate division and remainder of `o` mod `ω`:

`split o = (a, n)` means `o = a + n`, where `ω ∣ a`. -/
/-
**ONote.split** 是 Mathlib 中的一个定义，位于命名空间 `ONote`。
形式化陈述：split : ONote -> ONote × Nat | 0 => (0, 0) | oadd e n a => if e = 0 then (
0, n) else let (a', m)
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Calculate division and remainder of `o` mod `ω`:

`split o = (a, n)` means `o = a + n`, where `ω ∣ a`.
-/
def split : ONote → ONote × ℕ
  | 0 => (0, 0)
  | oadd e n a =>
    if e = 0 then (0, n)
    else
      let (a', m) := split a
      (oadd e n a', m)

/-- `scale x o` is the ordinal notation for `ω ^ x * o`. -/
/-
**ONote.scale** 是 Mathlib 中的一个定义，位于命名空间 `ONote`。
形式化陈述：ONote → ONote → ONote
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`scale x o` is the ordinal notation for `ω ^ x * o`.
-/
def scale (x : ONote) : ONote → ONote
  | 0 => 0
  | oadd e n a => oadd (x + e) n (scale x a)

/-- `mulNat o n` is the ordinal notation for `o * n`. -/
/-
**ONote.mulNat** 是 Mathlib 中的一个定义，位于命名空间 `ONote`。
形式化陈述：ONote → ℕ → ONote
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`mulNat o n` is the ordinal notation for `o * n`.
-/
def mulNat : ONote → ℕ → ONote
  | 0, _ => 0
  | _, 0 => 0
  | oadd e n a, m + 1 => oadd e (n * m.succPNat) a

/-- Auxiliary definition to compute the ordinal notation for the ordinal exponentiation in `opow` -/
/-
**ONote.opowAux** 是 Mathlib 中的一个定义，位于命名空间 `ONote`。
形式化陈述：ONote → ONote → ONote → ℕ → ℕ → ONote
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition to compute the ordinal notation for the ordinal exponentiat
ion in `opow`
-/
def opowAux (e a0 a : ONote) : ℕ → ℕ → ONote
  | _, 0 => 0
  | 0, m + 1 => oadd e m.succPNat 0
  | k + 1, m => scale (e + mulNat a0 k) a + (opowAux e a0 a k m)

/-- Auxiliary definition to compute the ordinal notation for the ordinal exponentiation in `opow` -/
/-
**ONote.opowAux2** 是 Mathlib 中的一个定义，位于命名空间 `ONote`。
形式化陈述：opowAux2 (o₂ : ONote) (o₁ : ONote × Nat) : ONote
参数：o₂ : ONote；o₁ : ONote × Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition to compute the ordinal notation for the ordinal exponentiat
ion in `opow`
-/
def opowAux2 (o₂ : ONote) (o₁ : ONote × ℕ) : ONote :=
  match o₁ with
  | (0, 0) => if o₂ = 0 then 1 else 0
  | (0, 1) => 1
  | (0, m + 1) =>
    let (b', k) := split' o₂
    oadd b' (m.succPNat ^ k) 0
  | (a@(oadd a0 _ _), m) =>
    match split o₂ with
    | (b, 0) => oadd (a0 * b) 1 0
    | (b, k + 1) =>
      let eb := a0 * b
      scale (eb + mulNat a0 k) a + opowAux eb a0 (mulNat a m) k m

/-- `opow o₁ o₂` calculates the ordinal notation for the ordinal exponential `o₁ ^ o₂`. -/
/-
**ONote.opow** 是 Mathlib 中的一个定义，位于命名空间 `ONote`。
形式化陈述：opow (o₁ o₂ : ONote) : ONote
参数：o₁ o₂ : ONote。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`opow o₁ o₂` calculates the ordinal notation for the ordinal exponential `o₁ ^ o
₂`.
-/
def opow (o₁ o₂ : ONote) : ONote := opowAux2 o₂ (split o₁)
/-
**ONote.** 是 Mathlib 中的一个实例，位于命名空间 `ONote`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Pow ONote ONote :=
  ⟨opow⟩
/-
**ONote.opow_def** 是 Mathlib 中的一个定理，位于命名空间 `ONote`。
形式化陈述：opow_def (o₁ o₂ : ONote) : o₁ ^ o₂ = opowAux2 o₂ (split o₁)
参数：o₁ o₂ : ONote。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem opow_def (o₁ o₂ : ONote) : o₁ ^ o₂ = opowAux2 o₂ (split o₁) :=
  rfl
/-
**ONote.split_eq_scale_split'** 是 Mathlib 中的一个定理，位于命名空间 `ONote`。
形式化陈述：split_eq_scale_split' : forall {o o' m} [NF o], split' o = (o', m) -> spli
t o = (scale 1 o', m) | 0, o', m, _, p => by injection p; subst o' m; rfl | oadd
 e n a, o', m, h, p => by by_cases e0 : e = 0 <;> simp only [split', e0, ↓reduce
Ite, Prod.mk.injEq, split] at p ⊢ · rcases p with ⟨rfl, rfl⟩ exact ⟨rfl, rfl⟩ · 
revert p rcases h' : split' a with ⟨a', m'⟩ have
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem split_eq_scale_split' : ∀ {o o' m} [NF o], split' o = (o', m) → split o = (scale 1 o', m)
  | 0, o', m, _, p => by injection p; subst o' m; rfl
  | oadd e n a, o', m, h, p => by
    by_cases e0 : e = 0 <;> simp only [split', e0, ↓reduceIte, Prod.mk.injEq, split] at p ⊢
    · rcases p with ⟨rfl, rfl⟩
      exact ⟨rfl, rfl⟩
    · revert p
      rcases h' : split' a with ⟨a', m'⟩
      have := h.fst
      have := h.snd
      simp only [split_eq_scale_split' h', and_imp]
      have : 1 + (e - 1) = e := by
        refine repr_inj.1 ?_
        simp only [repr_add, repr_one, Nat.cast_one, repr_sub]
        have := mt repr_inj.1 e0
        exact Ordinal.add_sub_cancel_of_le <| one_le_iff_ne_zero.2 this
      intros
      subst o' m
      simp [scale, this]
/-
**ONote.nf_repr_split'** 是 Mathlib 中的一个定理，位于命名空间 `ONote`。
形式化陈述：nf_repr_split' : forall {o o' m} [NF o], split' o = (o', m) -> NF o' ∧ rep
r o = ω * repr o' + m | 0, o', m, _, p => by injection p; subst o' m; simp [NF.z
ero] | oadd e n a, o', m, h, p => by by_cases e0 : e = 0 <;> simp only [split', 
e0, ↓reduceIte, Prod.mk.injEq, repr, repr_zero, opow_zero, one_mul] at p ⊢ · rca
ses p with ⟨rfl, rfl⟩ simp [h.zero_of_zero e0, NF.zero] · revert p rcases h' : s
plit' a with ⟨a', m'⟩ have
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nf_repr_split' : ∀ {o o' m} [NF o], split' o = (o', m) → NF o' ∧ repr o = ω * repr o' + m
  | 0, o', m, _, p => by injection p; subst o' m; simp [NF.zero]
  | oadd e n a, o', m, h, p => by
    by_cases e0 : e = 0 <;>
      simp only [split', e0, ↓reduceIte, Prod.mk.injEq, repr, repr_zero, opow_zero, one_mul] at p ⊢
    · rcases p with ⟨rfl, rfl⟩
      simp [h.zero_of_zero e0, NF.zero]
    · revert p
      rcases h' : split' a with ⟨a', m'⟩
      have := h.fst
      have := h.snd
      obtain ⟨IH₁, IH₂⟩ := nf_repr_split' h'
      simp only [IH₂, and_imp]
      intros
      subst o' m
      have : (ω : Ordinal.{0}) ^ repr e = ω ^ (1 : Ordinal.{0}) * ω ^ (repr e - 1) := by
        have := mt repr_inj.1 e0
        rw [← opow_add, Ordinal.add_sub_cancel_of_le (one_le_iff_ne_zero.2 this)]
      refine ⟨NF.oadd (by infer_instance) _ ?_, ?_⟩
      · simp only [opow_one, repr_sub, repr_one, Nat.cast_one] at this ⊢
        refine IH₁.below_of_lt' <| (mul_lt_mul_iff_right₀ omega0_pos).1 <|
          (le_self_add (α := Ordinal) (b := m')).trans_lt ?_
        rw [← this, ← IH₂]
        exact h.snd'.repr_lt
      · rw [this]
        simp [mul_add, mul_assoc, add_assoc]
/-
**ONote.scale_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 `ONote`。
形式化陈述：scale_eq_mul (x) [NF x] : forall (o) [NF o], scale x o = oadd x 1 0 * o | 
0, _ => rfl | oadd e n a, h => by simp only [HMul.hMul]; simp only [scale] have
参数：x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem scale_eq_mul (x) [NF x] : ∀ (o) [NF o], scale x o = oadd x 1 0 * o
  | 0, _ => rfl
  | oadd e n a, h => by
    simp only [HMul.hMul]; simp only [scale]
    have := h.snd
    by_cases e0 : e = 0
    · simp_rw [scale_eq_mul]
      simp [Mul.mul, mul, e0, h.zero_of_zero,
        show x + 0 = x from repr_inj.1 (by simp)]
    · simp [e0, Mul.mul, mul, scale_eq_mul, (· * ·)]
/-
**ONote.nf_scale** 是 Mathlib 中的一个实例，位于命名空间 `ONote`。
形式化陈述：nf_scale (x) [NF x] (o) [NF o] : NF (scale x o)
参数：x；o。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ONote.scale_eq_mul`：scale_eq_mul (x) [NF x] : forall (o) [NF o], scale x
 o = oadd x 1 0 * o | 0, _ => rfl | oadd e n a, h => by simp only [HMul.hMul]; s
imp only…
· 使用定理 `ONote.mul_nf`：∀ (o₁ o₂ : ONote) [o₁.NF] [o₂.NF], (o₁ * o₂).NF
· 使用定理 `ONote.NF.oadd_zero`：∀ (e : ONote) (n : ℕ+) [h : e.NF], (e.oadd n 0).NF
-/
instance nf_scale (x) [NF x] (o) [NF o] : NF (scale x o) := by
  rw [scale_eq_mul]
  infer_instance

@[simp]
/-
**ONote.repr_scale** 是 Mathlib 中的一个定理，位于命名空间 `ONote`。
形式化陈述：repr_scale (x) [NF x] (o) [NF o] : repr (scale x o) = ω ^ repr x * repr o
参数：x；o。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ONote.scale_eq_mul`：scale_eq_mul (x) [NF x] : forall (o) [NF o], scale x
 o = oadd x 1 0 * o | 0, _ => rfl | oadd e n a, h => by simp only [HMul.hMul]; s
imp only…
· 使用定理 `ONote.repr_mul`：repr_mul : forall (o₁ o₂) [NF o₁] [NF o₂], repr (o₁ * o₂
) = repr o₁ * repr o₂ | 0, o, _, h₂ => by cases o <;> exact (zero_mul _).symm | 
oadd…
· 使用定理 `ONote.NF.oadd_zero`：∀ (e : ONote) (n : ℕ+) [h : e.NF], (e.oadd n 0).NF
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem repr_scale (x) [NF x] (o) [NF o] : repr (scale x o) = ω ^ repr x * repr o := by
  simp only [scale_eq_mul, repr_mul, repr, PNat.one_coe, Nat.cast_one, mul_one, add_zero]
/-
**ONote.nf_repr_split** 是 Mathlib 中的一个定理，位于命名空间 `ONote`。
形式化陈述：nf_repr_split {o o' m} [NF o] (h : split o = (o', m)) : NF o' ∧ repr o = r
epr o' + m
参数：h : split o = (o', m)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ONote.nf_repr_split'`：nf_repr_split' : forall {o o' m} [NF o], split' o 
= (o', m) -> NF o' ∧ repr o = ω * repr o' + m | 0, o', m, _, p => by injection p
; subst o'…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ONote.split_eq_scale_split'`：split_eq_scale_split' : forall {o o' m} [NF
 o], split' o = (o', m) -> split o = (scale 1 o', m) | 0, o', m, _, p => by inje
ction p; subst o'…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ONote.repr_scale`：repr_scale (x) [NF x] (o) [NF o] : repr (scale x o) = 
ω ^ repr x * repr o
· 使用定理 `ONote.repr_one`：ONote.repr 1 = ↑1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Ordinal.opow_one`：opow_one (a : Ordinal) : a ^ (1 : Ordinal) = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem nf_repr_split {o o' m} [NF o] (h : split o = (o', m)) : NF o' ∧ repr o = repr o' + m := by
  rcases e : split' o with ⟨a, n⟩
  obtain ⟨s₁, s₂⟩ := nf_repr_split' e
  rw [split_eq_scale_split' e] at h
  injection h; subst o' n
  simp only [repr_scale, repr_one, Nat.cast_one, opow_one, ← s₂, and_true]
  infer_instance
/-
**ONote.split_dvd** 是 Mathlib 中的一个定理，位于命名空间 `ONote`。
形式化陈述：split_dvd {o o' m} [NF o] (h : split o = (o', m)) : ω ∣ repr o'
参数：h : split o = (o', m)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ONote.split_eq_scale_split'`：split_eq_scale_split' : forall {o o' m} [NF
 o], split' o = (o', m) -> split o = (scale 1 o', m) | 0, o', m, _, p => by inje
ction p; subst o'…
· 使用定理 `ONote.nf_repr_split'`：nf_repr_split' : forall {o o' m} [NF o], split' o 
= (o', m) -> NF o' ∧ repr o = ω * repr o' + m | 0, o', m, _, p => by injection p
; subst o'…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ONote.repr_scale`：repr_scale (x) [NF x] (o) [NF o] : repr (scale x o) = 
ω ^ repr x * repr o
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ONote.repr_one`：ONote.repr 1 = ↑1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Ordinal.opow_one`：opow_one (a : Ordinal) : a ^ (1 : Ordinal) = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem split_dvd {o o' m} [NF o] (h : split o = (o', m)) : ω ∣ repr o' := by
  rcases e : split' o with ⟨a, n⟩
  rw [split_eq_scale_split' e] at h
  injection h; subst o'
  cases nf_repr_split' e; simp
/-
**ONote.split_add_lt** 是 Mathlib 中的一个定理，位于命名空间 `ONote`。
形式化陈述：split_add_lt {o e n a m} [NF o] (h : split o = (oadd e n a, m)) : repr a +
 m < ω ^ repr e
参数：h : split o = (oadd e n a, m)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ONote.nf_repr_split`：nf_repr_split {o o' m} [NF o] (h : split o = (o', m
)) : NF o' ∧ repr o = repr o' + m
· 使用定理 `ONote.NF.of_dvd_omega0`：∀ {e : ONote} {n : ℕ+} {a : ONote},   (e.oadd n 
a).NF → Ordinal.omega0 ∣ (e.oadd n a).repr → e.repr ≠ 0 ∧ Ordinal.omega0 ∣ a.rep
r
· 使用定理 `ONote.split_dvd`：split_dvd {o o' m} [NF o] (h : split o = (o', m)) : ω ∣
 repr o'
· 使用定理 `Ordinal.isPrincipal_add_omega0_opow`：isPrincipal_add_omega0_opow (o : Or
dinal) : IsPrincipal (· + ·) (ω ^ o)
· 使用定理 `ONote.NFBelow.repr_lt`：∀ {o : ONote} {b : Ordinal.{0}}, o.NFBelow b → o.
repr < Ordinal.omega0 ^ b
· 使用定理 `ONote.NF.snd'`：∀ {e : ONote} {n : ℕ+} {a : ONote}, (e.oadd n a).NF → a.N
FBelow e.repr
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Ordinal.natCast_lt_omega0`：natCast_lt_omega0 (n : Nat) : ↑n < ω
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.opow_one`：opow_one (a : Ordinal) : a ^ (1 : Ordinal) = a
· 使用定理 `Ordinal.opow_le_opow_right`：opow_le_opow_right {a b c : Ordinal} (h₁ : 0
 < a) (h₂ : b <= c) : a ^ b <= a ^ c
· 使用定理 `Ordinal.omega0_pos`：omega0_pos : 0 < ω
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Order.one_le_iff_ne_zero`：one_le_iff_ne_zero [AddMonoidWithOne α] [NeZer
o (1 : α)] [SuccAddOrder α] [IsBotZeroClass α] : 1 <= x ↔ x != 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
-/
theorem split_add_lt {o e n a m} [NF o] (h : split o = (oadd e n a, m)) :
    repr a + m < ω ^ repr e := by
  obtain ⟨h₁, h₂⟩ := nf_repr_split h
  obtain ⟨e0, d⟩ := h₁.of_dvd_omega0 (split_dvd h)
  apply isPrincipal_add_omega0_opow _ h₁.snd'.repr_lt (lt_of_lt_of_le (natCast_lt_omega0 _) _)
  simpa using opow_le_opow_right omega0_pos (one_le_iff_ne_zero.2 e0)

@[simp]
/-
**ONote.mulNat_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 `ONote`。
形式化陈述：mulNat_eq_mul (n o) : mulNat o n = o * ofNat n
参数：n o。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem mulNat_eq_mul (n o) : mulNat o n = o * ofNat n := by cases o <;> cases n <;> rfl
/-
**ONote.nf_mulNat** 是 Mathlib 中的一个实例，位于命名空间 `ONote`。
形式化陈述：nf_mulNat (o) [NF o] (n) : NF (mulNat o n)
参数：o；n。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ONote.mulNat_eq_mul`：mulNat_eq_mul (n o) : mulNat o n = o * ofNat n
· 使用定理 `ONote.mul_nf`：∀ (o₁ o₂ : ONote) [o₁.NF] [o₂.NF], (o₁ * o₂).NF
-/
instance nf_mulNat (o) [NF o] (n) : NF (mulNat o n) := by simpa using ONote.mul_nf o (ofNat n)
/-
**ONote.nf_opowAux** 是 Mathlib 中的一个实例，位于命名空间 `ONote`。
形式化陈述：nf_opowAux (e a0 a) [NF e] [NF a0] [NF a] : forall k m, NF (opowAux e a0 a
 k m)
参数：e a0 a。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ONote.nf_opowAux._unary`：∀ (e a0 a : ONote) [e.NF] [a0.NF] [a.NF] (_x : 
(_ : ℕ) ×' ℕ), (e.opowAux a0 a _x.1 _x.2).NF
-/
instance nf_opowAux (e a0 a) [NF e] [NF a0] [NF a] : ∀ k m, NF (opowAux e a0 a k m) := by
  intro k m
  unfold opowAux
  cases m with
  | zero => cases k <;> exact NF.zero
  | succ m =>
    cases k with
    | zero => exact NF.oadd_zero _ _
    | succ k =>
      have := nf_opowAux e a0 a k
      simp only [mulNat_eq_mul]; infer_instance
/-
**ONote.nf_opow** 是 Mathlib 中的一个实例，位于命名空间 `ONote`。
形式化陈述：nf_opow (o₁ o₂) [NF o₁] [NF o₂] : NF (o₁ ^ o₂)
参数：o₁ o₂。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ONote.nf_repr_split`：nf_repr_split {o o' m} [NF o] (h : split o = (o', m
)) : NF o' ∧ repr o = repr o' + m
· 使用定理 `ONote.nf_repr_split'`：nf_repr_split' : forall {o o' m} [NF o], split' o 
= (o', m) -> NF o' ∧ repr o = ω * repr o' + m | 0, o', m, _, p => by injection p
; subst o'…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ONote.zero_def`：zero_def : zero = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `ONote.NF.zero`：ONote.NF 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `_private.Mathlib.SetTheory.Ordinal.Notation.0.ONote.opowAux2.match_3.eq_
2`：∀ (motive : ONote × ℕ → Sort u_1) (h_1 : Unit → motive (ONote.zero, 0)) (h_2 
: Unit → motive (ONote.zero, 1))   (h_3 : (m : ℕ) → motive (ONo…
· 使用定理 `_private.Mathlib.SetTheory.Ordinal.Notation.0.ONote.opowAux2.match_3.eq_
3`：∀ (motive : ONote × ℕ → Sort u_1) (m : ℕ) (h_1 : Unit → motive (ONote.zero, 0
)) (h_2 : Unit → motive (ONote.zero, 1))   (h_3 : (m : ℕ) → mot…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ONote.NF.oadd_zero`：∀ (e : ONote) (n : ℕ+) [h : e.NF], (e.oadd n 0).NF
· 使用定理 `ONote.split_eq_scale_split'`：split_eq_scale_split' : forall {o o' m} [NF
 o], split' o = (o', m) -> split o = (scale 1 o', m) | 0, o', m, _, p => by inje
ction p; subst o'…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ONote.mulNat_eq_mul`：mulNat_eq_mul (n o) : mulNat o n = o * ofNat n
· 使用定理 `ONote.NF.fst`：∀ {e : ONote} {n : ℕ+} {a : ONote}, (e.oadd n a).NF → e.NF
· 使用定理 `ONote.mul_nf`：∀ (o₁ o₂ : ONote) [o₁.NF] [o₂.NF], (o₁ * o₂).NF
· 使用定理 `ONote.add_nf`：∀ (o₁ o₂ : ONote) [o₁.NF] [o₂.NF], (o₁ + o₂).NF
-/
instance nf_opow (o₁ o₂) [NF o₁] [NF o₂] : NF (o₁ ^ o₂) := by
  rcases e₁ : split o₁ with ⟨a, m⟩
  have na := (nf_repr_split e₁).1
  rcases e₂ : split' o₂ with ⟨b', k⟩
  have := (nf_repr_split' e₂).1
  obtain - | ⟨a0, n, a'⟩ := a
  #adaptation_note /-- Proof repaired after leanprover/lean4#13363.
  The next branch was previously
  ```
  · rcases m with - | m
    · by_cases o₂ = 0 <;> simp only [(· ^ ·), Pow.pow, opow, opowAux2, *] <;> decide
    · by_cases m = 0
      · simp only [(· ^ ·), Pow.pow, opow, opowAux2, *, zero_def]
        decide
      · simp only [(· ^ ·), Pow.pow, opow, opowAux2, *]
        infer_instance
  ```
  The replacement proof is a short-term fix, and we request that the authors/maintainers of
  this file review the proof, and either approve it by removing this note, revise
  the proof or the prerequisites appropriately, or minimize a problem in lean4 that still
  needs addressing. -/
  · rcases m with - | m
    · by_cases h : o₂ = 0
      · subst h
        simp only [(· ^ ·), Pow.pow, opow, opowAux2, e₁, OfNat.ofNat, Zero.zero, One.one]
        decide
      · have h' : o₂ ≠ zero := fun he => h (he ▸ zero_def ▸ rfl)
        simp only [(· ^ ·), Pow.pow, opow, opowAux2, e₁, OfNat.ofNat, Zero.zero, One.one,
          h', ite_false]
        exact NF.zero
    · by_cases h : m = 0
      · simp only [(· ^ ·), Pow.pow, opow, opowAux2, OfNat.ofNat, Zero.zero, One.one, *]
        decide
      · simp only [(· ^ ·), Pow.pow, opow, opowAux2, OfNat.ofNat, Zero.zero, *]
        change NF (oadd _ _ 0)
        infer_instance
  · simp only [(· ^ ·), Pow.pow, opow, opowAux2, e₁, split_eq_scale_split' e₂, mulNat_eq_mul]
    have := na.fst
    rcases k with - | k
    · infer_instance
    · cases k <;> cases m <;> infer_instance
/-
**ONote.scale_opowAux** 是 Mathlib 中的一个定理，位于命名空间 `ONote`。
形式化陈述：∀ (e a0 a : ONote) [e.NF] [a0.NF] [a.NF] (k m : ℕ),   (e.opowAux a0 a k m)
.repr = Ordinal.omega0 ^ e.repr * (ONote.opowAux 0 a0 a k m).repr
参数：e a0 a : ONote；k m : ℕ；e.opowAux a0 a k m；ONote.opowAux 0 a0 a k m。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem scale_opowAux (e a0 a : ONote) [NF e] [NF a0] [NF a] :
    ∀ k m, repr (opowAux e a0 a k m) = ω ^ repr e * repr (opowAux 0 a0 a k m)
  | 0, m => by cases m <;> simp [opowAux]
  | k + 1, m => by
    by_cases h : m = 0 <;> simp only [h, opowAux, mulNat_eq_mul, repr_add, repr_scale, repr_mul,
      repr_ofNat, zero_add, mul_add, repr_zero, mul_zero, scale_opowAux e, opow_add, mul_assoc]
/-
**ONote.repr_opow_aux** 是 Mathlib 中的一个定理，位于命名空间 `ONote`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem repr_opow_aux₁ {e a} [Ne : NF e] [Na : NF a] {a' : Ordinal} (e0 : repr e ≠ 0)
    (h : a' < (ω : Ordinal.{0}) ^ repr e) (aa : repr a = a') (n : ℕ+) :
    ((ω : Ordinal.{0}) ^ repr e * (n : ℕ) + a') ^ (ω : Ordinal.{0}) =
      (ω ^ repr e) ^ (ω : Ordinal.{0}) := by
  subst aa
  have No := Ne.oadd n (Na.below_of_lt' h)
  have := omega0_le_oadd e n a
  rw [repr] at this
  refine le_antisymm ?_ (opow_le_opow_left _ this)
  apply (opow_le_of_isSuccLimit ((opow_pos _ omega0_pos).trans_le this).ne' isSuccLimit_omega0).2
  intro b l
  have := (No.below_of_lt (lt_succ _)).repr_lt
  rw [repr] at this
  apply (opow_le_opow_left b <| this.le).trans
  rw [← opow_mul, ← opow_mul]
  rcases le_or_gt ω (repr e) with h | h
  · grw [le_succ b, succ_eq_add_one, add_mul_succ _ (one_add_of_omega0_le h)]
    · gcongr
      · exact omega0_pos
      · exact succ_le_iff.2 <| by gcongr; exact isSuccLimit_omega0.succ_lt l
    · exact omega0_pos
  · grw [show _ * _ < _ from isPrincipal_mul_omega0 (isSuccLimit_omega0.succ_lt h) l]
    · simpa using mul_le_mul_left (one_le_iff_ne_zero.2 e0) ω
    · exact omega0_pos

section

/-
**ONote.repr_opow_aux** 是 Mathlib 中的一个定理，位于命名空间 `ONote`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem repr_opow_aux₂ {a0 a'} [N0 : NF a0] [Na' : NF a'] (m : ℕ) (d : ω ∣ repr a')
    (e0 : repr a0 ≠ 0) (h : repr a' + m < (ω ^ repr a0)) (n : ℕ+) (k : ℕ) :
    let R := repr (opowAux 0 a0 (oadd a0 n a' * ofNat m) k m)
    (k ≠ 0 → R < ((ω ^ repr a0) ^ succ (k : Ordinal))) ∧
      ((ω ^ repr a0) ^ (k : Ordinal)) * ((ω ^ repr a0) * (n : ℕ) + repr a') + R =
        ((ω ^ repr a0) * (n : ℕ) + repr a' + m) ^ succ (k : Ordinal) := by
  intro R'
  have No : NF (oadd a0 n a') :=
    N0.oadd n (Na'.below_of_lt' <| lt_of_le_of_lt le_self_add h)
  induction k with
  | zero => cases m <;> simp [R', opowAux]
  | succ k IH =>
  -- rename R => R'
  let R := repr (opowAux 0 a0 (oadd a0 n a' * ofNat m) k m)
  let ω0 := ω ^ repr a0
  let α' := ω0 * n + repr a'
  change (k ≠ 0 → R < (ω0 ^ succ (k : Ordinal))) ∧ (ω0 ^ (k : Ordinal)) * α' + R
    = (α' + m) ^ (succ ↑k : Ordinal) at IH
  have RR : R' = ω0 ^ (k : Ordinal) * (α' * m) + R := by
    by_cases h : m = 0
    · simp only [R, R', h, ONote.ofNat, Nat.cast_zero, ONote.repr_zero,
        mul_zero, ONote.opowAux, add_zero]
    · simp only [α', ω0, R, R', ONote.repr_scale, ONote.repr,
        ONote.mulNat_eq_mul, ONote.opowAux, ONote.repr_ofNat, ONote.repr_mul, ONote.repr_add,
        Ordinal.opow_mul, ONote.zero_add]
  have α0 : 0 < α' := by simpa [lt_def, repr] using oadd_pos a0 n a'
  have ω00 : 0 < ω0 ^ (k : Ordinal) := opow_pos _ (opow_pos _ omega0_pos)
  have Rl : R < ω ^ (repr a0 * succ ↑k) := by
    by_cases k0 : k = 0
    · simp only [k0, Nat.cast_zero, succ_eq_add_one, _root_.zero_add, mul_one, R]
      refine lt_of_lt_of_le ?_ (opow_le_opow_right omega0_pos (one_le_iff_ne_zero.2 e0))
      rcases m with - | m
      · simp [opowAux, omega0_pos]
      · simpa [opowAux] using natCast_lt_omega0 (m + 1)
    · rw [opow_mul]
      exact IH.1 k0
  refine ⟨fun _ => ?_, ?_⟩
  · rw [RR, ← opow_mul _ _ (succ k.succ)]
    have e0 := pos_iff_ne_zero.2 e0
    have rr0 : 0 < repr a0 + repr a0 := lt_of_lt_of_le e0 le_add_self
    apply isPrincipal_add_omega0_opow
    · simp only [Nat.cast_add_one, opow_add_one, opow_mul, opow_succ, mul_assoc]
      gcongr ?_ * ?_
      rw [← Ordinal.opow_add]
      have : _ < ω ^ (repr a0 + repr a0) := (No.below_of_lt ?_).repr_lt
      · exact mul_lt_omega0_opow rr0 this (natCast_lt_omega0 _)
      · simpa using (add_lt_add_iff_left (repr a0)).2 e0
    · exact
        lt_of_lt_of_le Rl
          (opow_le_opow_right omega0_pos <|
            mul_le_mul_right (succ_le_succ_iff.2 (Nat.cast_le.2 (le_of_lt k.lt_succ_self))) _)
  calc
    (ω0 ^ (k.succ : Ordinal)) * α' + R'
    _ = (ω0 ^ succ (k : Ordinal)) * α' + ((ω0 ^ (k : Ordinal)) * α' * m + R) := by
        rw [Nat.cast_add_one, RR, ← mul_assoc, succ_eq_add_one]
    _ = ((ω0 ^ (k : Ordinal)) * α' + R) * α' + ((ω0 ^ (k : Ordinal)) * α' + R) * m := ?_
    _ = (α' + m) ^ succ (k.succ : Ordinal) := by
        rw [← mul_add, opow_succ, Nat.cast_add_one, IH.2, succ_eq_add_one]
  congr 1
  · have αd : ω ∣ α' :=
      dvd_add (dvd_mul_of_dvd_left (by simpa using opow_dvd_opow ω (one_le_iff_ne_zero.2 e0)) _) d
    have α0 : ¬IsMin α' := by
      rw [isMin_iff_eq_bot]
      exact α0.ne'
    rw [mul_add (ω0 ^ (k : Ordinal)), add_assoc, ← mul_assoc, ← opow_succ,
      add_mul_of_isSuccLimit _ ⟨α0, isSuccPrelimit_iff_omega0_dvd.2 αd⟩, mul_assoc,
      @mul_omega0_dvd n (Nat.cast_pos'.2 n.pos) (natCast_lt_omega0 _) _ αd]
    apply @add_of_omega0_opow_le _ (repr a0 * succ ↑k)
    · refine isPrincipal_add_omega0_opow _ ?_ Rl
      rw [opow_mul, opow_succ]
      gcongr
      exact No.snd'.repr_lt
    · have := mul_le_mul_right (one_le_iff_pos.2 <| Nat.cast_pos'.2 n.pos) (ω0 ^ succ (k : Ordinal))
      rw [opow_mul]
      simpa
  · cases m
    · have : R = 0 := by cases k <;> simp [R, opowAux]
      simp [this]
    · rw [Nat.cast_add_one, ← succ_eq_add_one, add_mul_succ]
      apply add_of_omega0_opow_le Rl
      rw [opow_mul, opow_succ]
      gcongr
      simpa [repr] using omega0_le_oadd a0 n a'

end

set_option linter.flexible false in -- simp used on two different goals
/-
**ONote.repr_opow** 是 Mathlib 中的一个定理，位于命名空间 `ONote`。
形式化陈述：repr_opow (o₁ o₂) [NF o₁] [NF o₂] : repr (o₁ ^ o₂) = repr o₁ ^ repr o₂
参数：o₁ o₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ONote.nf_repr_split`：nf_repr_split {o o' m} [NF o] (h : split o = (o', m
)) : NF o' ∧ repr o = repr o' + m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ONote.repr_one`：ONote.repr 1 = ↑1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `ONote.repr.eq_1`：ONote.zero.repr = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Ordinal.opow_zero`：opow_zero (a : Ordinal) : a ^ (0 : Ordinal) = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ONote.repr_inj`：repr_inj {a b} [NF a] [NF b] : repr a = repr b ↔ a = b
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ordinal.zero_opow`：zero_opow {a : Ordinal} (a0 : a != 0) : (0 : Ordinal)
 ^ a = 0
· 使用定理 `ONote.nf_repr_split'`：nf_repr_split' : forall {o o' m} [NF o], split' o 
= (o', m) -> NF o' ∧ repr o = ω * repr o' + m | 0, o', m, _, p => by injection p
; subst o'…
· 使用定理 `instIsWellOrderEmptyRelationOfSubsingleton`：∀ {α : Type u} [Subsingleton
 α], IsWellOrder α emptyRelation
· 使用定理 `instSubsingletonPEmpty`：Subsingleton PEmpty.{u_1}
· 使用定理 `_private.Mathlib.SetTheory.Ordinal.Notation.0.ONote.opowAux2.match_3.eq_
2`：∀ (motive : ONote × ℕ → Sort u_1) (h_1 : Unit → motive (ONote.zero, 0)) (h_2 
: Unit → motive (ONote.zero, 1))   (h_3 : (m : ℕ) → motive (ONo…
· 使用定理 `Ordinal.type_fintype`：type_fintype [IsWellOrder α r] [Fintype α] : type 
r = Fintype.card α
· 使用定理 `Fintype.card_eq_zero`：∀ {α : Type u_1} [inst : Fintype α] [IsEmpty α], F
intype.card α = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Ordinal.opow_add`：opow_add (a b c : Ordinal) : a ^ (b + c) = a ^ b * a ^
 c
（共 66 条，此处仅展示前 30 条）
-/
theorem repr_opow (o₁ o₂) [NF o₁] [NF o₂] : repr (o₁ ^ o₂) = repr o₁ ^ repr o₂ := by
  rcases e₁ : split o₁ with ⟨a, m⟩
  obtain ⟨N₁, r₁⟩ := nf_repr_split e₁
  obtain - | ⟨a0, n, a'⟩ := a
  #adaptation_note /-- Proof repaired after leanprover/lean4#13363.
  The next block was previously
  ```
  · rcases m with - | m
    · by_cases h : o₂ = 0
      · simp [opow_def, opowAux2, e₁, h, r₁]
      · simpa [opow_def, opowAux2, e₁, h, r₁, eqComm] using mt repr_inj.1 h
    · rcases e₂ : split' o₂ with ⟨b', k⟩
      obtain ⟨_, r₂⟩ := nf_repr_split' e₂
      by_cases h : m = 0
      · simp [opowAux2, opow_def, e₁, h, r₁, r₂]
      simp only [opow_def, opowAux2, e₁, r₁, e₂, r₂, repr,
          Nat.cast_succ, _root_.zero_add,
          add_zero]
  ```
  The replacement proof is a short-term fix, and we request that the authors/maintainers of
  this file review the proof, and either approve it by removing this note, revise
  the proof or the prerequisites appropriately, or minimize a problem in lean4 that still
  needs addressing. -/
  · rcases m with - | m
    · have hzero : (0 : ONote) = zero := rfl
      by_cases h : o₂ = 0
      · subst h; simp [-zero_def, opow_def, opowAux2, e₁, r₁, hzero]
      · have h' := mt repr_inj.1 h
        have hne : o₂ ≠ zero := fun he => h (he ▸ rfl)
        simp [-zero_def, opow_def, opowAux2, e₁, r₁, hne, hzero]
        exact (zero_opow h').symm
    · rcases e₂ : split' o₂ with ⟨b', k⟩
      obtain ⟨_, r₂⟩ := nf_repr_split' e₂
      by_cases h : m = 0
      · simp only [opowAux2, opow_def, e₁, h, r₁, r₂, OfNat.ofNat, Zero.zero, One.one,
          repr]
        simp [opow_add, opow_mul]
      simp only [opow_def, opowAux2, e₁, r₁, e₂, r₂, repr,
          Nat.cast_succ, _root_.zero_add, add_zero]
      rw [opow_add, opow_mul, opow_omega0]
      · simp
      · simpa [Nat.one_le_iff_ne_zero]
      · rw [← Nat.cast_succ, lt_omega0]
        exact ⟨_, rfl⟩
  · have := N₁.fst
    have := N₁.snd
    obtain ⟨a00, ad⟩ := N₁.of_dvd_omega0 (split_dvd e₁)
    have al := split_add_lt e₁
    have aa : repr (a' + ofNat m) = repr a' + m := by
      simp only [ONote.repr_ofNat, ONote.repr_add]
    rcases e₂ : split' o₂ with ⟨b', k⟩
    obtain ⟨_, r₂⟩ := nf_repr_split' e₂
    simp only [opow_def, e₁, r₁, split_eq_scale_split' e₂, opowAux2, repr]
    rcases k with - | k
    · simp [r₂, opow_mul, repr_opow_aux₁ a00 al aa, add_assoc]
    · simp [r₂, opow_add, opow_mul, mul_assoc, add_assoc, repr_one]
      rw [repr_opow_aux₁ a00 al aa, scale_opowAux]
      simp only [repr_mul, repr_scale, repr_one,
        Nat.cast_one, opow_one, opow_mul]
      rw [← mul_add, ← add_assoc ((ω : Ordinal.{0}) ^ repr a0 * (n : ℕ))]
      congr 1
      rw [← pow_succ, ← opow_natCast, ← opow_natCast]
      exact (repr_opow_aux₂ _ ad a00 al _ _).2

/-- Given an ordinal, returns:

* `inl none` for `0`
* `inl (some a)` for `a + 1`
* `inr f` for a limit ordinal `a`, where `f i` is a sequence converging to `a` -/
/-
**ONote.fundamentalSequence** 是 Mathlib 中的一个定义，位于命名空间 `ONote`。
形式化陈述：fundamentalSequence : ONote -> (Option ONote) oplus (Nat -> ONote) | zero 
=> Sum.inl none | oadd a m b => match fundamentalSequence b with | Sum.inr f => 
Sum.inr fun i => oadd a m (f i) | Sum.inl (some b') => Sum.inl (some (oadd a m b
')) | Sum.inl none => match fundamentalSequence a, m.natPred with | Sum.inl none
, 0 => Sum.inl (some zero) | Sum.inl none, m + 1 => Sum.inl (some (oadd zero m.s
uccPNat zero)) | Sum.inl (some a'), 0 => Sum.inr fun i => oadd a' i.succPNat zer
o | Sum.inl (some a'), m +
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an ordinal, returns:

* `inl none` for `0`
* `inl (some a)` for `a + 1`
* `inr f` for a limit ordinal `a`, where `f i` is a sequence converging to `a`
-/
def fundamentalSequence : ONote → (Option ONote) ⊕ (ℕ → ONote)
  | zero => Sum.inl none
  | oadd a m b =>
    match fundamentalSequence b with
    | Sum.inr f => Sum.inr fun i => oadd a m (f i)
    | Sum.inl (some b') => Sum.inl (some (oadd a m b'))
    | Sum.inl none =>
      match fundamentalSequence a, m.natPred with
      | Sum.inl none, 0 => Sum.inl (some zero)
      | Sum.inl none, m + 1 => Sum.inl (some (oadd zero m.succPNat zero))
      | Sum.inl (some a'), 0 => Sum.inr fun i => oadd a' i.succPNat zero
      | Sum.inl (some a'), m + 1 => Sum.inr fun i => oadd a m.succPNat (oadd a' i.succPNat zero)
      | Sum.inr f, 0 => Sum.inr fun i => oadd (f i) 1 zero
      | Sum.inr f, m + 1 => Sum.inr fun i => oadd a m.succPNat (oadd (f i) 1 zero)
/-
**ONote.exists_lt_add** 是 Mathlib 中的一个定理，位于命名空间 `ONote`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem exists_lt_add {α} [hα : Nonempty α] {o : Ordinal} {f : α → Ordinal}
    (H : ∀ ⦃a⦄, a < o → ∃ i, a < f i) {b : Ordinal} ⦃a⦄ (h : a < b + o) : ∃ i, a < b + f i := by
  rcases lt_or_ge a b with h | h'
  · obtain ⟨i⟩ := id hα
    exact ⟨i, h.trans_le le_self_add⟩
  · rw [← Ordinal.add_sub_cancel_of_le h', add_lt_add_iff_left] at h
    refine (H h).imp fun i H => ?_
    rwa [← Ordinal.add_sub_cancel_of_le h', add_lt_add_iff_left]
/-
**ONote.exists_lt_mul_omega0'** 是 Mathlib 中的一个定理，位于命名空间 `ONote`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem exists_lt_mul_omega0' {o : Ordinal} ⦃a⦄ (h : a < o * ω) :
    ∃ i : ℕ, a < o * ↑i + o := by
  obtain ⟨i, hi, h'⟩ := (lt_mul_iff_of_isSuccLimit isSuccLimit_omega0).1 h
  obtain ⟨i, rfl⟩ := lt_omega0.1 hi
  exact ⟨i, h'.trans_le le_self_add⟩
/-
**ONote.exists_lt_omega0_opow'** 是 Mathlib 中的一个定理，位于命名空间 `ONote`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem exists_lt_omega0_opow' {α} {o b : Ordinal} (hb : 1 < b) (ho : IsSuccLimit o)
    {f : α → Ordinal} (H : ∀ ⦃a⦄, a < o → ∃ i, a < f i) ⦃a⦄ (h : a < b ^ o) :
        ∃ i, a < b ^ f i := by
  obtain ⟨d, hd, h'⟩ := (lt_opow_of_isSuccLimit (zero_lt_one.trans hb).ne' ho).1 h
  exact (H hd).imp fun i hi => h'.trans <| (opow_lt_opow_iff_right hb).2 hi

/-- The property satisfied by `fundamentalSequence o`:

* `inl none` means `o = 0`
* `inl (some a)` means `o = succ a`
* `inr f` means `o` is a limit ordinal and `f` is a strictly increasing sequence which converges to
  `o` -/
/-
**ONote.FundamentalSequenceProp** 是 Mathlib 中的一个定义，位于命名空间 `ONote`。
形式化陈述：ONote → Option ONote ⊕ (ℕ → ONote) → Prop
参数：ℕ → ONote。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property satisfied by `fundamentalSequence o`:

* `inl none` means `o = 0`
* `inl (some a)` means `o = succ a`
* `inr f` means `o` is a limit ordinal and `f` is a strictly increasing sequence
 which converges to
  `o`
-/
def FundamentalSequenceProp (o : ONote) : (Option ONote) ⊕ (ℕ → ONote) → Prop
  | Sum.inl none => o = 0
  | Sum.inl (some a) => o.repr = succ a.repr ∧ (o.NF → a.NF)
  | Sum.inr f =>
    IsSuccLimit o.repr ∧
      (∀ i, f i < f (i + 1) ∧ f i < o ∧ (o.NF → (f i).NF)) ∧ ∀ a, a < o.repr → ∃ i, a < (f i).repr
/-
**ONote.fundamentalSequenceProp_inl_none** 是 Mathlib 中的一个定理，位于命名空间 `ONote`。
形式化陈述：fundamentalSequenceProp_inl_none (o) : FundamentalSequenceProp o (Sum.inl 
none) ↔ o = 0
参数：o。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem fundamentalSequenceProp_inl_none (o) :
    FundamentalSequenceProp o (Sum.inl none) ↔ o = 0 :=
  Iff.rfl
/-
**ONote.fundamentalSequenceProp_inl_some** 是 Mathlib 中的一个定理，位于命名空间 `ONote`。
形式化陈述：fundamentalSequenceProp_inl_some (o a) : FundamentalSequenceProp o (Sum.in
l (some a)) ↔ o.repr = succ a.repr ∧ (o.NF -> a.NF)
参数：o a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem fundamentalSequenceProp_inl_some (o a) :
    FundamentalSequenceProp o (Sum.inl (some a)) ↔ o.repr = succ a.repr ∧ (o.NF → a.NF) :=
  Iff.rfl
/-
**ONote.fundamentalSequenceProp_inr** 是 Mathlib 中的一个定理，位于命名空间 `ONote`。
形式化陈述：fundamentalSequenceProp_inr (o f) : FundamentalSequenceProp o (Sum.inr f) 
↔ IsSuccLimit o.repr ∧ (forall i, f i < f (i + 1) ∧ f i < o ∧ (o.NF -> (f i).NF)
) ∧ forall a, a < o.repr -> exists i, a < (f i).repr
参数：o f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem fundamentalSequenceProp_inr (o f) :
    FundamentalSequenceProp o (Sum.inr f) ↔
      IsSuccLimit o.repr ∧
        (∀ i, f i < f (i + 1) ∧ f i < o ∧ (o.NF → (f i).NF)) ∧
        ∀ a, a < o.repr → ∃ i, a < (f i).repr :=
  Iff.rfl
/-
**ONote.fundamentalSequence_has_prop** 是 Mathlib 中的一个定理，位于命名空间 `ONote`。
形式化陈述：fundamentalSequence_has_prop (o) : FundamentalSequenceProp o (fundamentalS
equence o)
参数：o。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ONote.fundamentalSequence.eq_2`：∀ (e : ONote) (n : ℕ+) (a : ONote),   (e
.oadd n a).fundamentalSequence =     match a.fundamentalSequence with     | Sum.
inr f => Sum.inr fun…
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `PNat.natPred_add_one`：natPred_add_one (n : Nat+) : n.natPred + 1 = n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `PNat.coe_inj`：coe_inj {m n : Nat+} : (m : Nat) = n ↔ m = n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ONote.FundamentalSequenceProp.eq_1`：∀ (o : ONote), o.FundamentalSequence
Prop (Sum.inl none) = (o = 0)
· 使用定理 `Ordinal.opow_zero`：opow_zero (a : Ordinal) : a ^ (0 : Ordinal) = 1
· 使用定理 `Nat.cast_succ`：cast_succ (n : Nat) : ((succ n : Nat) : R) = n + 1
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Nat.succPNat_coe`：succPNat_coe (n : Nat) : (succPNat n : Nat) = succ n
· 使用定理 `Nat.add_one`：∀ (n : ℕ), n + 1 = n.succ
· 使用定理 `mul_add_one`：mul_add_one [LeftDistribClass α] (a b : α) : a * (b + 1) = 
a * b + a
· 使用定理 `ONote.NF.oadd_zero`：∀ (e : ONote) (n : ℕ+) [h : e.NF], (e.oadd n 0).NF
· 使用定理 `ONote.NF.zero`：ONote.NF 0
· 使用定理 `ONote.FundamentalSequenceProp.eq_2`：∀ (o a : ONote), o.FundamentalSequen
ceProp (Sum.inl (some a)) = (o.repr = Order.succ a.repr ∧ (o.NF → a.NF))
· 使用定理 `Ordinal.opow_succ`：opow_succ (a b : Ordinal) : a ^ succ b = a ^ b * a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
（共 66 条，此处仅展示前 30 条）
-/
theorem fundamentalSequence_has_prop (o) : FundamentalSequenceProp o (fundamentalSequence o) := by
  induction o with
  | zero => exact rfl
  | oadd a m b iha ihb
  rw [fundamentalSequence]
  rcases e : b.fundamentalSequence with (⟨_ | b'⟩ | f) <;>
    simp only [FundamentalSequenceProp] <;>
    rw [e, FundamentalSequenceProp] at ihb
  · rcases e : a.fundamentalSequence with (⟨_ | a'⟩ | f) <;> rcases e' : m.natPred with - | m' <;>
      simp only <;>
      rw [e, FundamentalSequenceProp] at iha <;>
      (try rw [show m = 1 by
            have := PNat.natPred_add_one m; rw [e'] at this; exact PNat.coe_inj.1 this.symm]) <;>
      (try rw [show m = (m' + 1).succPNat by
              rw [← e', ← PNat.coe_inj, Nat.succPNat_coe, ← Nat.add_one, PNat.natPred_add_one]]) <;>
      simp only [repr, repr_zero, iha, ihb, opow_lt_opow_iff_right one_lt_omega0,
        add_lt_add_iff_left, add_zero, lt_add_iff_pos_right, lt_def, mul_one, Nat.cast_zero,
        Nat.cast_succ, Nat.succPNat_coe, opow_succ, opow_zero, mul_add_one, PNat.one_coe,
        _root_.zero_add, zero_def]
    · constructor
      · simp
      · decide
    · exact ⟨rfl, inferInstance⟩
    · have := opow_pos (repr a') omega0_pos
      refine
        ⟨isSuccLimit_mul_right this isSuccLimit_omega0, fun i =>
          ⟨this, ?_, fun H => @NF.oadd_zero _ _ (iha.2 H.fst)⟩, exists_lt_mul_omega0'⟩
      rw [← mul_add_one, ← Nat.cast_add_one]
      gcongr
      apply natCast_lt_omega0
    · have := opow_pos (repr a') omega0_pos
      refine
        ⟨isSuccLimit_add _ (isSuccLimit_mul_right this isSuccLimit_omega0), fun i => ⟨this, ?_, ?_⟩,
          exists_lt_add exists_lt_mul_omega0'⟩
      · rw [← mul_add_one, ← Nat.cast_add_one]
        gcongr
        apply natCast_lt_omega0
      · refine fun H => H.fst.oadd _ (NF.below_of_lt' ?_ (@NF.oadd_zero _ _ (iha.2 H.fst)))
        rw [repr, repr_zero, add_zero, iha.1, opow_succ]
        gcongr
        apply natCast_lt_omega0
    · rcases iha with ⟨h1, h2, h3⟩
      refine ⟨isSuccLimit_opow one_lt_omega0 h1, fun i => ?_,
        exists_lt_omega0_opow' one_lt_omega0 h1 h3⟩
      obtain ⟨h4, h5, h6⟩ := h2 i
      exact ⟨h4, h5, fun H => @NF.oadd_zero _ _ (h6 H.fst)⟩
    · rcases iha with ⟨h1, h2, h3⟩
      refine
        ⟨isSuccLimit_add _ (isSuccLimit_opow one_lt_omega0 h1), fun i => ?_,
          exists_lt_add (exists_lt_omega0_opow' one_lt_omega0 h1 h3)⟩
      obtain ⟨h4, h5, h6⟩ := h2 i
      refine ⟨h4, h5, fun H => H.fst.oadd _ (NF.below_of_lt' ?_ (@NF.oadd_zero _ _ (h6 H.fst)))⟩
      rwa [repr, repr_zero, add_zero, PNat.one_coe, Nat.cast_one, mul_one,
        opow_lt_opow_iff_right one_lt_omega0]
  · refine ⟨?_, fun H ↦ H.fst.oadd _ (NF.below_of_lt' ?_ (ihb.2 H.snd))⟩
    · rw [repr, ihb.1, succ_eq_add_one, succ_eq_add_one, ← add_assoc, repr]
    have := H.snd'.repr_lt
    rw [ihb.1] at this
    exact (lt_succ _).trans this
  · rcases ihb with ⟨h1, h2, h3⟩
    simp only [repr]
    exact
      ⟨isSuccLimit_add _ h1, fun i =>
        ⟨oadd_lt_oadd_3 (h2 i).1, oadd_lt_oadd_3 (h2 i).2.1, fun H =>
          H.fst.oadd _ (NF.below_of_lt' (lt_trans (h2 i).2.1 H.snd'.repr_lt) ((h2 i).2.2 H.snd))⟩,
        exists_lt_add h3⟩

/-- The fast growing hierarchy for ordinal notations `< ε₀`. This is a sequence of functions `ℕ → ℕ`
indexed by ordinals, with the definition:

* `f_0(n) = n + 1`
* `f_(α + 1)(n) = f_α^[n](n)`
* `f_α(n) = f_(α[n])(n)` where `α` is a limit ordinal and `α[i]` is the fundamental sequence
  converging to `α` -/
/-
**ONote.fastGrowing** 是 Mathlib 中的一个定义，位于命名空间 `ONote`。
形式化陈述：fastGrowing : ONote -> Nat -> Nat | o => match fundamentalSequence o, fund
amentalSequence_has_prop o with | Sum.inl none, _ => Nat.succ | Sum.inl (some a)
, h => have : a < o
该定义给出了一等式。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ONote.fundamentalSequence_has_prop`：fundamentalSequence_has_prop (o) : F
undamentalSequenceProp o (fundamentalSequence o)

--- 原说明 ---
The fast growing hierarchy for ordinal notations `< ε₀`. This is a sequence of f
unctions `ℕ → ℕ`
indexed by ordinals, with the definition:

* `f_0(n) = n + 1`
* `f_(α + 1)(n) = f_α^[n](n)`
* `f_α(n) = f_(α[n])(n)` where `α` is a limit ordinal and `α[i]` is the fundamen
tal sequence
  converging to `α`
-/
def fastGrowing : ONote → ℕ → ℕ
  | o =>
    match fundamentalSequence o, fundamentalSequence_has_prop o with
    | Sum.inl none, _ => Nat.succ
    | Sum.inl (some a), h =>
      have : a < o := by rw [lt_def, h.1]; apply lt_succ
      fun i => (fastGrowing a)^[i] i
    | Sum.inr f, h => fun i =>
      have : f i < o := (h.2.1 i).2.1
      fastGrowing (f i) i
  termination_by o => o
/-
**ONote.fastGrowing_def** 是 Mathlib 中的一个定理，位于命名空间 `ONote`。
形式化陈述：fastGrowing_def {o : ONote} {x} (e : fundamentalSequence o = x) : fastGrow
ing o = match (motive
参数：e : fundamentalSequence o = x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ONote.fundamentalSequence_has_prop`：fundamentalSequence_has_prop (o) : F
undamentalSequenceProp o (fundamentalSequence o)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ONote.fastGrowing.eq_1`：∀ (x : ONote),   x.fastGrowing =     match (moti
ve := (x_1 : Option ONote ⊕ (ℕ → ONote)) → x.FundamentalSequenceProp x_1 → ℕ → ℕ
) x.fundamen…
-/
theorem fastGrowing_def {o : ONote} {x} (e : fundamentalSequence o = x) :
    fastGrowing o =
      match
        (motive := (x : Option ONote ⊕ (ℕ → ONote)) → FundamentalSequenceProp o x → ℕ → ℕ)
        x, e ▸ fundamentalSequence_has_prop o with
      | Sum.inl none, _ => Nat.succ
      | Sum.inl (some a), _ =>
        fun i => (fastGrowing a)^[i] i
      | Sum.inr f, _ => fun i =>
        fastGrowing (f i) i := by
  subst x
  rw [fastGrowing]
/-
**ONote.fastGrowing_zero'** 是 Mathlib 中的一个定理，位于命名空间 `ONote`。
形式化陈述：fastGrowing_zero' (o : ONote) (h : fundamentalSequence o = Sum.inl none) :
 fastGrowing o = Nat.succ
参数：o : ONote；h : fundamentalSequence o = Sum.inl none。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ONote.fundamentalSequence_has_prop`：fundamentalSequence_has_prop (o) : F
undamentalSequenceProp o (fundamentalSequence o)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ONote.fastGrowing_def`：fastGrowing_def {o : ONote} {x} (e : fundamentalS
equence o = x) : fastGrowing o = match (motive
-/
theorem fastGrowing_zero' (o : ONote) (h : fundamentalSequence o = Sum.inl none) :
    fastGrowing o = Nat.succ := by
  rw [fastGrowing_def h]
/-
**ONote.fastGrowing_succ** 是 Mathlib 中的一个定理，位于命名空间 `ONote`。
形式化陈述：fastGrowing_succ (o) {a} (h : fundamentalSequence o = Sum.inl (some a)) : 
fastGrowing o = fun i => (fastGrowing a)^[i] i
参数：o；h : fundamentalSequence o = Sum.inl (some a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ONote.fundamentalSequence_has_prop`：fundamentalSequence_has_prop (o) : F
undamentalSequenceProp o (fundamentalSequence o)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ONote.fastGrowing_def`：fastGrowing_def {o : ONote} {x} (e : fundamentalS
equence o = x) : fastGrowing o = match (motive
-/
theorem fastGrowing_succ (o) {a} (h : fundamentalSequence o = Sum.inl (some a)) :
    fastGrowing o = fun i => (fastGrowing a)^[i] i := by
  rw [fastGrowing_def h]
/-
**ONote.fastGrowing_limit** 是 Mathlib 中的一个定理，位于命名空间 `ONote`。
形式化陈述：fastGrowing_limit (o) {f} (h : fundamentalSequence o = Sum.inr f) : fastGr
owing o = fun i => fastGrowing (f i) i
参数：o；h : fundamentalSequence o = Sum.inr f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ONote.fundamentalSequence_has_prop`：fundamentalSequence_has_prop (o) : F
undamentalSequenceProp o (fundamentalSequence o)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ONote.fastGrowing_def`：fastGrowing_def {o : ONote} {x} (e : fundamentalS
equence o = x) : fastGrowing o = match (motive
-/
theorem fastGrowing_limit (o) {f} (h : fundamentalSequence o = Sum.inr f) :
    fastGrowing o = fun i => fastGrowing (f i) i := by
  rw [fastGrowing_def h]

@[simp]
/-
**ONote.fastGrowing_zero** 是 Mathlib 中的一个定理，位于命名空间 `ONote`。
形式化陈述：fastGrowing_zero : fastGrowing 0 = Nat.succ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ONote.fastGrowing_zero'`：fastGrowing_zero' (o : ONote) (h : fundamentalS
equence o = Sum.inl none) : fastGrowing o = Nat.succ
-/
theorem fastGrowing_zero : fastGrowing 0 = Nat.succ :=
  fastGrowing_zero' _ rfl

@[simp]
/-
**ONote.fastGrowing_one** 是 Mathlib 中的一个定理，位于命名空间 `ONote`。
形式化陈述：fastGrowing_one : fastGrowing 1 = fun n => 2 * n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ONote.fastGrowing_succ`：fastGrowing_succ (o) {a} (h : fundamentalSequenc
e o = Sum.inl (some a)) : fastGrowing o = fun i => (fastGrowing a)^[i] i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `ONote.fastGrowing_zero`：fastGrowing_zero : fastGrowing 0 = Nat.succ
· 使用定理 `Nat.succ_iterate`：∀ (a n : ℕ), Nat.succ^[n] a = a + n
-/
theorem fastGrowing_one : fastGrowing 1 = fun n => 2 * n := by
  rw [@fastGrowing_succ 1 0 rfl]; funext i; rw [two_mul, fastGrowing_zero]
  exact Nat.succ_iterate _ _

@[simp]
/-
**ONote.fastGrowing_two** 是 Mathlib 中的一个定理，位于命名空间 `ONote`。
形式化陈述：fastGrowing_two : fastGrowing 2 = fun n => (2 ^ n) * n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ONote.fastGrowing_succ`：fastGrowing_succ (o) {a} (h : fundamentalSequenc
e o = Sum.inl (some a)) : fastGrowing o = fun i => (fastGrowing a)^[i] i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ONote.fastGrowing_one`：fastGrowing_one : fastGrowing 1 = fun n => 2 * n
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `mul_left_iterate`：∀ {M : Type u_4} [inst : Monoid M] (a : M) (n : ℕ), (f
un x => a * x)^[n] = fun x => a ^ n * x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fastGrowing_two : fastGrowing 2 = fun n => (2 ^ n) * n := by
  rw [@fastGrowing_succ 2 1 rfl]
  simp

/-- We can extend the fast growing hierarchy one more step to `ε₀` itself, using `ω ^ (ω ^ (⋯ ^ ω))`
as the fundamental sequence converging to `ε₀` (which is not an `ONote`). Extending the fast
growing hierarchy beyond this requires a definition of fundamental sequence for larger ordinals. -/
/-
**ONote.fastGrowing** 是 Mathlib 中的一个定义，位于命名空间 `ONote`。
形式化陈述：fastGrowing : ONote -> Nat -> Nat | o => match fundamentalSequence o, fund
amentalSequence_has_prop o with | Sum.inl none, _ => Nat.succ | Sum.inl (some a)
, h => have : a < o
该定义给出了一等式。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ONote.fundamentalSequence_has_prop`：fundamentalSequence_has_prop (o) : F
undamentalSequenceProp o (fundamentalSequence o)

--- 原说明 ---
We can extend the fast growing hierarchy one more step to `ε₀` itself, using `ω 
^ (ω ^ (⋯ ^ ω))`
as the fundamental sequence converging to `ε₀` (which is not an `ONote`). Extend
ing the fast
growing hierarchy beyond this requires a definition of fundamental sequence for 
larger ordinals.
-/
def fastGrowingε₀ (i : ℕ) : ℕ :=
  fastGrowing ((fun a => a.oadd 1 0)^[i] 0) i
/-
**ONote.fastGrowing** 是 Mathlib 中的一个定义，位于命名空间 `ONote`。
形式化陈述：fastGrowing : ONote -> Nat -> Nat | o => match fundamentalSequence o, fund
amentalSequence_has_prop o with | Sum.inl none, _ => Nat.succ | Sum.inl (some a)
, h => have : a < o
该定义给出了一等式。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ONote.fundamentalSequence_has_prop`：fundamentalSequence_has_prop (o) : F
undamentalSequenceProp o (fundamentalSequence o)
-/
theorem fastGrowingε₀_zero : fastGrowingε₀ 0 = 1 := by simp [fastGrowingε₀]
/-
**ONote.fastGrowing** 是 Mathlib 中的一个定义，位于命名空间 `ONote`。
形式化陈述：fastGrowing : ONote -> Nat -> Nat | o => match fundamentalSequence o, fund
amentalSequence_has_prop o with | Sum.inl none, _ => Nat.succ | Sum.inl (some a)
, h => have : a < o
该定义给出了一等式。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ONote.fundamentalSequence_has_prop`：fundamentalSequence_has_prop (o) : F
undamentalSequenceProp o (fundamentalSequence o)
-/
theorem fastGrowingε₀_one : fastGrowingε₀ 1 = 2 := by
  simp [fastGrowingε₀, show oadd 0 1 0 = 1 from rfl]
/-
**ONote.fastGrowing** 是 Mathlib 中的一个定义，位于命名空间 `ONote`。
形式化陈述：fastGrowing : ONote -> Nat -> Nat | o => match fundamentalSequence o, fund
amentalSequence_has_prop o with | Sum.inl none, _ => Nat.succ | Sum.inl (some a)
, h => have : a < o
该定义给出了一等式。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ONote.fundamentalSequence_has_prop`：fundamentalSequence_has_prop (o) : F
undamentalSequenceProp o (fundamentalSequence o)
-/
theorem fastGrowingε₀_two : fastGrowingε₀ 2 = 2048 := by
  norm_num [fastGrowingε₀, show oadd 0 1 0 = 1 from rfl, @fastGrowing_limit (oadd 1 1 0) _ rfl,
    show oadd 0 (2 : Nat).succPNat 0 = 3 from rfl, @fastGrowing_succ 3 2 rfl]

end ONote

/-- The type of normal ordinal notations.

It would have been nicer to define this right in the inductive type, but `NF o` requires `repr`
which requires `ONote`, so all these things would have to be defined at once, which messes up the VM
representation. -/
/-
**NONote** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：NONote
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of normal ordinal notations.

It would have been nicer to define this right in the inductive type, but `NF o` 
requires `repr`
which requires `ONote`, so all these things would have to be defined at once, wh
ich messes up the VM
representation.
-/
def NONote :=
  { o : ONote // o.NF }
deriving DecidableEq

namespace NONote

open ONote

/-
**NONote.NF** 是 Mathlib 中的一个实例，位于命名空间 `NONote`。
形式化陈述：NF (o : NONote) : NF o.1
参数：o : NONote。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
instance NF (o : NONote) : NF o.1 :=
  o.2

/-- Construct a `NONote` from an ordinal notation (and infer normality) -/
/-
**NONote.mk** 是 Mathlib 中的一个定义，位于命名空间 `NONote`。
形式化陈述：mk (o : ONote) [h : ONote.NF o] : NONote
参数：o : ONote。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a `NONote` from an ordinal notation (and infer normality)
-/
def mk (o : ONote) [h : ONote.NF o] : NONote :=
  ⟨o, h⟩

/-- The ordinal represented by an ordinal notation.

This function is noncomputable because ordinal arithmetic is noncomputable. In computational
applications `NONote` can be used exclusively without reference to `Ordinal`, but this function
allows for correctness results to be stated. -/
/-
**NONote.repr** 是 Mathlib 中的一个定义，位于命名空间 `NONote`。
形式化陈述：repr (o : NONote) : Ordinal
参数：o : NONote。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ordinal represented by an ordinal notation.

This function is noncomputable because ordinal arithmetic is noncomputable. In c
omputational
applications `NONote` can be used exclusively without reference to `Ordinal`, bu
t this function
allows for correctness results to be stated.
-/
noncomputable def repr (o : NONote) : Ordinal :=
  o.1.repr
/-
**NONote.** 是 Mathlib 中的一个实例，位于命名空间 `NONote`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ToString NONote :=
  ⟨fun x => x.1.toString⟩
/-
**NONote.** 是 Mathlib 中的一个实例，位于命名空间 `NONote`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Repr NONote :=
  ⟨fun x prec => x.1.repr' prec⟩
/-
**NONote.** 是 Mathlib 中的一个实例，位于命名空间 `NONote`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Preorder NONote where
  le x y := repr x ≤ repr y
  lt x y := repr x < repr y
  le_refl _ := @le_refl Ordinal _ _
  le_trans _ _ _ := @le_trans Ordinal _ _ _ _
  lt_iff_le_not_ge _ _ := @lt_iff_le_not_ge Ordinal _ _ _
/-
**NONote.** 是 Mathlib 中的一个实例，位于命名空间 `NONote`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero NONote :=
  ⟨⟨0, NF.zero⟩⟩
/-
**NONote.** 是 Mathlib 中的一个实例，位于命名空间 `NONote`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited NONote :=
  ⟨0⟩
/-
**NONote.lt_wf** 是 Mathlib 中的一个定理，位于命名空间 `NONote`。
形式化陈述：lt_wf : @WellFounded NONote (· < ·)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InvImage.wf`：∀ {α : Sort u} {β : Sort v} {r : β → β → Prop} (f : α → β),
 WellFounded r → WellFounded (InvImage r f)
· 使用定理 `Ordinal.lt_wf`：lt_wf : @WellFounded Ordinal (· < ·)
-/
theorem lt_wf : @WellFounded NONote (· < ·) :=
  InvImage.wf repr Ordinal.lt_wf
/-
**NONote.** 是 Mathlib 中的一个实例，位于命名空间 `NONote`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : WellFoundedLT NONote :=
  ⟨lt_wf⟩
/-
**NONote.** 是 Mathlib 中的一个实例，位于命名空间 `NONote`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : WellFoundedRelation NONote :=
  ⟨(· < ·), lt_wf⟩

/-- Convert a natural number to an ordinal notation -/
/-
**NONote.ofNat** 是 Mathlib 中的一个定义，位于命名空间 `NONote`。
形式化陈述：ofNat (n : Nat) : NONote
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Convert a natural number to an ordinal notation
-/
def ofNat (n : ℕ) : NONote :=
  ⟨ONote.ofNat n, ⟨⟨_, nfBelow_ofNat _⟩⟩⟩

/-- Compare ordinal notations -/
/-
**NONote.cmp** 是 Mathlib 中的一个定义，位于命名空间 `NONote`。
形式化陈述：cmp (a b : NONote) : Ordering
参数：a b : NONote。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Compare ordinal notations
-/
def cmp (a b : NONote) : Ordering :=
  ONote.cmp a.1 b.1
/-
**NONote.cmp_compares** 是 Mathlib 中的一个定理，位于命名空间 `NONote`。
形式化陈述：cmp_compares : forall a b : NONote, (cmp a b).Compares a b | ⟨a, ha⟩, ⟨b, 
hb⟩ => by dsimp [cmp] have
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ONote.cmp_compares`：cmp_compares : forall (a b : ONote) [NF a] [NF b], (
cmp a b).Compares a b | 0, 0, _, _ => rfl | oadd _ _ _, 0, _, _ => oadd_pos _ _ 
_ | 0, o…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subtype.mk_eq_mk`：mk_eq_mk {a h a' h'} : @mk α p a h = @mk α p a' h' ↔ a
 = a'
-/
theorem cmp_compares : ∀ a b : NONote, (cmp a b).Compares a b
  | ⟨a, ha⟩, ⟨b, hb⟩ => by
    dsimp [cmp]
    have := ONote.cmp_compares a b
    cases h : ONote.cmp a b <;> simp only [h] at this <;> try exact this
    exact Subtype.mk_eq_mk.2 this
/-
**NONote.** 是 Mathlib 中的一个实例，位于命名空间 `NONote`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LinearOrder NONote :=
  linearOrderOfCompares cmp cmp_compares

/-- Asserts that `repr a < ω ^ repr b`. Used in `NONote.recOn`. -/
/-
**NONote.below** 是 Mathlib 中的一个定义，位于命名空间 `NONote`。
形式化陈述：below (a b : NONote) : Prop
参数：a b : NONote。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Asserts that `repr a < ω ^ repr b`. Used in `NONote.recOn`.
-/
def below (a b : NONote) : Prop :=
  NFBelow a.1 (repr b)

/-- The `oadd` pseudo-constructor for `NONote` -/
/-
**NONote.oadd** 是 Mathlib 中的一个定义，位于命名空间 `NONote`。
形式化陈述：oadd (e : NONote) (n : Nat+) (a : NONote) (h : below a e) : NONote
参数：e : NONote；n : Nat+；a : NONote；h : below a e。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `oadd` pseudo-constructor for `NONote`
-/
def oadd (e : NONote) (n : ℕ+) (a : NONote) (h : below a e) : NONote :=
  ⟨_, NF.oadd e.2 n h⟩

/-- This is a recursor-like theorem for `NONote` suggesting an inductive definition, which can't
actually be defined this way due to conflicting dependencies. -/
@[elab_as_elim]
/-
**NONote.recOn** 是 Mathlib 中的一个定义，位于命名空间 `NONote`。
形式化陈述：recOn {C : NONote -> Sort*} (o : NONote) (H0 : C 0) (H1 : forall e n a h, 
C e -> C a -> C (oadd e n a h)) : C o
参数：o : NONote；H0 : C 0；H1 : forall e n a h, C e -> C a -> C (oadd e n a h)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ONote.NF.fst`：∀ {e : ONote} {n : ℕ+} {a : ONote}, (e.oadd n a).NF → e.NF
· 使用定理 `ONote.NF.snd`：∀ {e : ONote} {n : ℕ+} {a : ONote}, (e.oadd n a).NF → a.NF
· 使用定理 `ONote.NF.snd'`：∀ {e : ONote} {n : ℕ+} {a : ONote}, (e.oadd n a).NF → a.N
FBelow e.repr

--- 原说明 ---
This is a recursor-like theorem for `NONote` suggesting an inductive definition,
 which can't
actually be defined this way due to conflicting dependencies.
-/
def recOn {C : NONote → Sort*} (o : NONote) (H0 : C 0)
    (H1 : ∀ e n a h, C e → C a → C (oadd e n a h)) : C o := by
  obtain ⟨o, h⟩ := o; induction o with
  | zero => exact H0
  | oadd e n a IHe IHa => exact H1 ⟨e, h.fst⟩ n ⟨a, h.snd⟩ h.snd' (IHe _) (IHa _)

/-- Addition of ordinal notations -/
/-
**NONote.** 是 Mathlib 中的一个实例，位于命名空间 `NONote`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Addition of ordinal notations
-/
instance : Add NONote :=
  ⟨fun x y => mk (x.1 + y.1)⟩
/-
**NONote.repr_add** 是 Mathlib 中的一个定理，位于命名空间 `NONote`。
形式化陈述：repr_add (a b) : repr (a + b) = repr a + repr b
参数：a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ONote.repr_add`：repr_add : forall (o₁ o₂) [NF o₁] [NF o₂], repr (o₁ + o₂
) = repr o₁ + repr o₂ | 0, o, _, _ => by simp | oadd e n a, o, h₁, h₂ => by have
-/
theorem repr_add (a b) : repr (a + b) = repr a + repr b :=
  ONote.repr_add a.1 b.1

/-- Subtraction of ordinal notations -/
/-
**NONote.** 是 Mathlib 中的一个实例，位于命名空间 `NONote`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Subtraction of ordinal notations
-/
instance : Sub NONote :=
  ⟨fun x y => mk (x.1 - y.1)⟩
/-
**NONote.repr_sub** 是 Mathlib 中的一个定理，位于命名空间 `NONote`。
形式化陈述：repr_sub (a b) : repr (a - b) = repr a - repr b
参数：a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ONote.repr_sub`：repr_sub : forall (o₁ o₂) [NF o₁] [NF o₂], repr (o₁ - o₂
) = repr o₁ - repr o₂ | 0, o, _, h₂ => by cases o <;> exact (Ordinal.zero_sub _)
.sym…
-/
theorem repr_sub (a b) : repr (a - b) = repr a - repr b :=
  ONote.repr_sub a.1 b.1

/-- Multiplication of ordinal notations -/
/-
**NONote.** 是 Mathlib 中的一个实例，位于命名空间 `NONote`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multiplication of ordinal notations
-/
instance : Mul NONote :=
  ⟨fun x y => mk (x.1 * y.1)⟩
/-
**NONote.repr_mul** 是 Mathlib 中的一个定理，位于命名空间 `NONote`。
形式化陈述：repr_mul (a b) : repr (a * b) = repr a * repr b
参数：a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ONote.repr_mul`：repr_mul : forall (o₁ o₂) [NF o₁] [NF o₂], repr (o₁ * o₂
) = repr o₁ * repr o₂ | 0, o, _, h₂ => by cases o <;> exact (zero_mul _).symm | 
oadd…
-/
theorem repr_mul (a b) : repr (a * b) = repr a * repr b :=
  ONote.repr_mul a.1 b.1

/-- Exponentiation of ordinal notations -/
/-
**NONote.opow** 是 Mathlib 中的一个定义，位于命名空间 `NONote`。
形式化陈述：opow (x y : NONote)
参数：x y : NONote。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Exponentiation of ordinal notations
-/
def opow (x y : NONote) :=
  mk (x.1 ^ y.1)
/-
**NONote.repr_opow** 是 Mathlib 中的一个定理，位于命名空间 `NONote`。
形式化陈述：repr_opow (a b) : repr (opow a b) = repr a ^ repr b
参数：a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ONote.repr_opow`：repr_opow (o₁ o₂) [NF o₁] [NF o₂] : repr (o₁ ^ o₂) = re
pr o₁ ^ repr o₂
-/
theorem repr_opow (a b) : repr (opow a b) = repr a ^ repr b :=
  ONote.repr_opow a.1 b.1

end NONote

