/-
Copyright (c) 2024 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Andreas Gittis
-/
module

public meta import Mathlib.Data.Nat.Log
public import Mathlib.Data.Nat.Log
public import Mathlib.Tactic.NormNum

/-! # `norm_num` extensions for `Nat.log` and `Nat.clog`

This module defines `norm_num` extensions for `Nat.log` and `Nat.clog`.
-/

public meta section

namespace Mathlib.Meta.NormNum

open Qq Lean Elab.Tactic

/-
**Mathlib.Meta.NormNum.nat_log_zero** 是 Mathlib 中的一个引理，位于命名空间 `Mathlib.Meta.Norm
Num`。
形式化陈述：nat_log_zero (n : Nat) : Nat.log 0 n = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.log_zero_left`：∀ (n : ℕ), Nat.log 0 n = 0
-/
lemma nat_log_zero (n : Nat) : Nat.log 0 n = 0 := Nat.log_zero_left n
/-
**Mathlib.Meta.NormNum.nat_log_one** 是 Mathlib 中的一个引理，位于命名空间 `Mathlib.Meta.NormN
um`。
形式化陈述：nat_log_one (n : Nat) : Nat.log 1 n = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.log_one_left`：log_one_left : forall n, log 1 n = 0
-/
lemma nat_log_one (n : Nat) : Nat.log 1 n = 0 := Nat.log_one_left n
/-
**Mathlib.Meta.NormNum.nat_log_helper0** 是 Mathlib 中的一个引理，位于命名空间 `Mathlib.Meta.N
ormNum`。
形式化陈述：nat_log_helper0 (b n : Nat) (hl : Nat.blt n b = true) : Nat.log b n = 0
参数：b n : Nat；hl : Nat.blt n b = true。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Nat.blt_eq`：∀ {x y : ℕ}, (x.blt y = true) = (x < y)
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
lemma nat_log_helper0 (b n : Nat) (hl : Nat.blt n b = true) :
    Nat.log b n = 0 := by
  rw [Nat.blt_eq] at hl
  simp [hl]
/-
**Mathlib.Meta.NormNum.nat_log_helper** 是 Mathlib 中的一个引理，位于命名空间 `Mathlib.Meta.No
rmNum`。
形式化陈述：nat_log_helper (b n k : Nat) (hl : Nat.ble (b ^ k) n = true) (hh : Nat.blt
 n (b ^ (k + 1)) = true) : Nat.log b n = k
参数：b n k : Nat；hl : Nat.ble (b ^ k) n = true；hh : Nat.blt n (b ^ (k + 1)) = true
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.log_eq_of_pow_le_of_lt_pow`：log_eq_of_pow_le_of_lt_pow {b m n : Nat}
 (h₁ : b ^ m <= n) (h₂ : n < b ^ (m + 1)) : log b n = m
· 使用定理 `Nat.le_of_ble_eq_true`：∀ {n m : ℕ}, n.ble m = true → n ≤ m
-/
lemma nat_log_helper (b n k : Nat)
    (hl : Nat.ble (b ^ k) n = true) (hh : Nat.blt n (b ^ (k + 1)) = true) :
    Nat.log b n = k :=
  Nat.log_eq_of_pow_le_of_lt_pow (Nat.le_of_ble_eq_true hl) (Nat.le_of_ble_eq_true hh)
/-
**Mathlib.Meta.NormNum.isNat_log** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.NormNum
`。
形式化陈述：∀ {b nb n nn k : ℕ},   Mathlib.Meta.NormNum.IsNat b nb →     Mathlib.Meta.
NormNum.IsNat n nn → Nat.log nb nn = k → Mathlib.Meta.NormNum.IsNat (Nat.log b n
) k
参数：Nat.log b n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isNat_log : {b nb n nn k : ℕ} → IsNat b nb → IsNat n nn →
    Nat.log nb nn = k → IsNat (Nat.log b n) k
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨rfl⟩

/--
Given the natural number literals `eb` and `en`, returns `Nat.log eb en`
as a natural number literal and an equality proof.
Panics if `ex` or `en` aren't natural number literals.
-/
/-
**Mathlib.Meta.NormNum.proveNatLog** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.NormN
um`。
形式化陈述：proveNatLog (eb en : Q(Nat)) : (ek : Q(Nat)) × Q(Nat.log $eb $en = $ek)
参数：eb en : Q(Nat)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given the natural number literals `eb` and `en`, returns `Nat.log eb en`
as a natural number literal and an equality proof.
Panics if `ex` or `en` aren't natural number literals.
-/
def proveNatLog (eb en : Q(ℕ)) : (ek : Q(ℕ)) × Q(Nat.log $eb $en = $ek) :=
  match eb.natLit!, en.natLit! with
  | 0, _ => have : $eb =Q nat_lit 0 := ⟨⟩; ⟨q(nat_lit 0), q(nat_log_zero $en)⟩
  | 1, _ => have : $eb =Q nat_lit 1 := ⟨⟩; ⟨q(nat_lit 0), q(nat_log_one $en)⟩
  | b, n =>
    if n < b then
      have hh : Q(Nat.blt $en $eb = true) := (q(Eq.refl true) : Expr)
      ⟨q(nat_lit 0), q(nat_log_helper0 $eb $en $hh)⟩
    else
      let k := Nat.log b n
      have ek : Q(ℕ) := mkRawNatLit k
      have hl : Q(Nat.ble ($eb ^ $ek) $en = true) := (q(Eq.refl true) : Expr)
      have hh : Q(Nat.blt $en ($eb ^ ($ek + 1)) = true) := (q(Eq.refl true) : Expr)
      ⟨ek, q(nat_log_helper $eb $en $ek $hl $hh)⟩

/--
Evaluates the `Nat.log` function.
-/
@[norm_num Nat.log _ _]
/-
**Mathlib.Meta.NormNum.evalNatLog** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.NormNu
m`。
形式化陈述：evalNatLog : NormNumExt where eval {u α} e
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluates the `Nat.log` function.
-/
def evalNatLog : NormNumExt where eval {u α} e := do
  let mkApp2 _ (b : Q(ℕ)) (n : Q(ℕ)) ← Meta.whnfR e | failure
  let sℕ : Q(AddMonoidWithOne ℕ) := q(Nat.instAddMonoidWithOne)
  let ⟨eb, pb⟩ ← deriveNat b sℕ
  let ⟨en, pn⟩ ← deriveNat n sℕ
  let ⟨ek, pf⟩ := proveNatLog eb en
  let pf' : Q(IsNat (Nat.log $b $n) $ek) := q(isNat_log $pb $pn $pf)
  return .isNat sℕ ek pf'
/-
**Mathlib.Meta.NormNum.nat_clog_zero_left** 是 Mathlib 中的一个引理，位于命名空间 `Mathlib.Met
a.NormNum`。
形式化陈述：nat_clog_zero_left (b n : Nat) (hb : Nat.ble b 1 = true) : Nat.clog b n = 
0
参数：b n : Nat；hb : Nat.ble b 1 = true。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.clog_of_left_le_one`：clog_of_left_le_one {b : Nat} (hb : b <= 1) (n 
: Nat) : clog b n = 0
· 使用定理 `Nat.le_of_ble_eq_true`：∀ {n m : ℕ}, n.ble m = true → n ≤ m
-/
lemma nat_clog_zero_left (b n : Nat) (hb : Nat.ble b 1 = true) :
    Nat.clog b n = 0 := Nat.clog_of_left_le_one (Nat.le_of_ble_eq_true hb) n
/-
**Mathlib.Meta.NormNum.nat_clog_zero_right** 是 Mathlib 中的一个引理，位于命名空间 `Mathlib.Me
ta.NormNum`。
形式化陈述：nat_clog_zero_right (b n : Nat) (hn : Nat.ble n 1 = true) : Nat.clog b n =
 0
参数：b n : Nat；hn : Nat.ble n 1 = true。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.clog_of_right_le_one`：clog_of_right_le_one {n : Nat} (hn : n <= 1) (
b : Nat) : clog b n = 0
· 使用定理 `Nat.le_of_ble_eq_true`：∀ {n m : ℕ}, n.ble m = true → n ≤ m
-/
lemma nat_clog_zero_right (b n : Nat) (hn : Nat.ble n 1 = true) :
    Nat.clog b n = 0 := Nat.clog_of_right_le_one (Nat.le_of_ble_eq_true hn) b
/-
**Mathlib.Meta.NormNum.nat_clog_helper** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.N
ormNum`。
形式化陈述：nat_clog_helper {b m n : Nat} (hb : Nat.blt 1 b = true) (h₁ : Nat.blt (b ^
 m) n = true) (h₂ : Nat.ble n (b ^ (m + 1)) = true) : Nat.clog b n = m + 1
参数：hb : Nat.blt 1 b = true；h₁ : Nat.blt (b ^ m) n = true；h₂ : Nat.ble n (b ^ (m 
+ 1)) = true。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.lt_clog_iff_pow_lt`：lt_clog_iff_pow_lt {b : Nat} (hb : 1 < b) {x y :
 Nat} : y < clog b x ↔ b ^ y < x
· 使用定理 `Nat.blt_eq`：∀ {x y : ℕ}, (x.blt y = true) = (x < y)
· 使用定理 `Nat.clog_le_iff_le_pow`：clog_le_iff_le_pow {b : Nat} (hb : 1 < b) {x y :
 Nat} : clog b x <= y ↔ x <= b ^ y
· 使用定理 `Nat.ble_eq`：∀ {x y : ℕ}, (x.ble y = true) = (x ≤ y)
-/
theorem nat_clog_helper {b m n : ℕ} (hb : Nat.blt 1 b = true)
    (h₁ : Nat.blt (b ^ m) n = true) (h₂ : Nat.ble n (b ^ (m + 1)) = true) :
    Nat.clog b n = m + 1 := by
  rw [Nat.blt_eq] at hb
  rw [Nat.blt_eq, ← Nat.lt_clog_iff_pow_lt hb] at h₁
  rw [Nat.ble_eq, ← Nat.clog_le_iff_le_pow hb] at h₂
  lia
/-
**Mathlib.Meta.NormNum.isNat_clog** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.NormNu
m`。
形式化陈述：∀ {b nb n nn k : ℕ},   Mathlib.Meta.NormNum.IsNat b nb →     Mathlib.Meta.
NormNum.IsNat n nn → Nat.clog nb nn = k → Mathlib.Meta.NormNum.IsNat (Nat.clog b
 n) k
参数：Nat.clog b n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isNat_clog : {b nb n nn k : ℕ} → IsNat b nb → IsNat n nn →
    Nat.clog nb nn = k → IsNat (Nat.clog b n) k
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨rfl⟩

/--
Given the natural number literals `eb` and `en`, returns `Nat.clog eb en`
as a natural number literal and an equality proof.
Panics if `ex` or `en` aren't natural number literals.
-/
/-
**Mathlib.Meta.NormNum.proveNatClog** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.Norm
Num`。
形式化陈述：proveNatClog (eb en : Q(Nat)) : (ek : Q(Nat)) × Q(Nat.clog $eb $en = $ek)
参数：eb en : Q(Nat)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given the natural number literals `eb` and `en`, returns `Nat.clog eb en`
as a natural number literal and an equality proof.
Panics if `ex` or `en` aren't natural number literals.
-/
def proveNatClog (eb en : Q(ℕ)) : (ek : Q(ℕ)) × Q(Nat.clog $eb $en = $ek) :=
  let b := eb.natLit!
  let n := en.natLit!
  if _ : b ≤ 1 then
    have h : Q(Nat.ble $eb 1 = true) := reflBoolTrue
    ⟨q(nat_lit 0), q(nat_clog_zero_left $eb $en $h)⟩
  else if _ : n ≤ 1 then
    have h : Q(Nat.ble $en 1 = true) := reflBoolTrue
    ⟨q(nat_lit 0), q(nat_clog_zero_right $eb $en $h)⟩
  else
    match h : Nat.clog b n with
    | 0 => False.elim <|
      Nat.ne_of_gt (Nat.clog_pos (by lia) (by lia)) h
    | k + 1 =>
      have ek : Q(ℕ) := mkRawNatLit k
      have ek1 : Q(ℕ) := mkRawNatLit (k + 1)
      have _ : $ek1 =Q $ek + 1 := ⟨⟩
      have hb : Q(Nat.blt 1 $eb = true) := reflBoolTrue
      have hl : Q(Nat.blt ($eb ^ $ek) $en = true) := reflBoolTrue
      have hh : Q(Nat.ble $en ($eb ^ ($ek + 1)) = true) := reflBoolTrue
      ⟨ek1, q(nat_clog_helper $hb $hl $hh)⟩

/--
Evaluates the `Nat.clog` function.
-/
@[norm_num Nat.clog _ _]
/-
**Mathlib.Meta.NormNum.evalNatClog** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.NormN
um`。
形式化陈述：evalNatClog : NormNumExt where eval {u α} e
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluates the `Nat.clog` function.
-/
def evalNatClog : NormNumExt where eval {u α} e := do
  let mkApp2 _ (b : Q(ℕ)) (n : Q(ℕ)) ← Meta.whnfR e | failure
  let sℕ : Q(AddMonoidWithOne ℕ) := q(Nat.instAddMonoidWithOne)
  let ⟨eb, pb⟩ ← deriveNat b sℕ
  let ⟨en, pn⟩ ← deriveNat n sℕ
  let ⟨ek, pf⟩ := proveNatClog eb en
  let pf' : Q(IsNat (Nat.clog $b $n) $ek) := q(isNat_clog $pb $pn $pf)
  return .isNat sℕ ek pf'

end Mathlib.Meta.NormNum

