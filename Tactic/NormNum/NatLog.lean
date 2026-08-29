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

/--
lemma `nat_log_zero` / 引理 `nat_log_zero`

English:
lemma nat_log_zero
  given: (n : Nat)
  statement: Nat.log 0 n = 0
  proof: Nat.log_zero_left n

中文:
引理 nat_log_zero
  条件: (n : 自然数)
  结论: 自然数.log 0 n = 0
  证明: Nat.log_zero_left n

Depends on / 依赖: Nat.log_zero_left, log_zero_left
-/
lemma nat_log_zero (n : Nat) : Nat.log 0 n = 0 := Nat.log_zero_left n
/--
lemma `nat_log_one` / 引理 `nat_log_one`

English:
lemma nat_log_one
  given: (n : Nat)
  statement: Nat.log 1 n = 0
  proof: Nat.log_one_left n

中文:
引理 nat_log_one
  条件: (n : 自然数)
  结论: 自然数.log 1 n = 0
  证明: Nat.log_one_left n

Depends on / 依赖: Nat.log_one_left, log_one_left
-/
lemma nat_log_one (n : Nat) : Nat.log 1 n = 0 := Nat.log_one_left n

/--
lemma `nat_log_helper0` / 引理 `nat_log_helper0`

English:
lemma nat_log_helper0
  given: (b n : Nat) (hl : Nat.blt n b = true)
  proof: by
  rw [Nat.blt_eq] at hl
  simp [hl]

中文:
引理 nat_log_helper0
  条件: (b n : 自然数) (hl : 自然数.blt n b = true)
  证明: by
  rw [Nat.blt_eq] at hl
  simp [hl]

Depends on / 依赖: Nat.blt_eq, blt_eq
-/
lemma nat_log_helper0 (b n : Nat) (hl : Nat.blt n b = true) :
    Nat.log b n = 0 := by
  rw [Nat.blt_eq] at hl
  simp [hl]

/--
lemma `nat_log_helper` / 引理 `nat_log_helper`

English:
lemma nat_log_helper
  statement: (b n k : Nat)
  proof: Nat.log_eq_of_pow_le_of_lt_pow (Nat.le_of_ble_eq_true hl) (Nat.le_of_ble_eq_true hh)

中文:
引理 nat_log_helper
  结论: (b n k : 自然数)
  证明: Nat.log_eq_of_pow_le_of_lt_pow (Nat.le_of_ble_eq_true hl) (Nat.le_of_ble_eq_true hh)

Depends on / 依赖: Nat.le_of_ble_eq_true, Nat.log_eq_of_pow_le_of_lt_pow, le_of_ble_eq_true, log_eq_of_pow_le_of_lt_pow
-/
lemma nat_log_helper (b n k : Nat)
    (hl : Nat.ble (b ^ k) n = true) (hh : Nat.blt n (b ^ (k + 1)) = true) :
    Nat.log b n = k :=
  Nat.log_eq_of_pow_le_of_lt_pow (Nat.le_of_ble_eq_true hl) (Nat.le_of_ble_eq_true hh)

/--
theorem `isNat_log` / 定理 `isNat_log`

English:
theorem isNat_log
  statement: {b nb n nn k : Nat} -> IsNat b nb -> IsNat n nn ->

中文:
定理 is自然数_log
  结论: {b nb n nn k : 自然数} -> 是自然数 b nb -> 是自然数 n nn ->
-/
theorem isNat_log : {b nb n nn k : Nat} -> IsNat b nb -> IsNat n nn ->
    Nat.log nb nn = k -> IsNat (Nat.log b n) k
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨rfl⟩

/--
Definition of `proveNatLog` / `proveNatLog` 的定义

English:
definition proveNatLog
  signature: (eb en : Q(Nat))
  body: match eb.natLit!, en.natLit! with
| 0, _ => have : eb =Q nat_lit 0 := ⟨⟩; ⟨q(nat_lit 0), q(nat_log_zero $en)⟩
| 1, _ => have : eb =Q nat_lit 1 := ⟨⟩; ⟨q(nat_lit 0), q(nat_log_one $en)⟩
  | b, n =>
    if n < b then
      have hh : Q(Nat.blt $en $eb = true) := (q(Eq.refl true) : Expr)
      ⟨q(nat_lit 0), q(nat_log_helper0 $eb $en $hh)⟩
    else
      let k := Nat.log b n
      have ek : Q(Nat) := mkRawNatLit k
      have hl : Q(Nat.ble ($eb ^ $ek) $en = true) := (q(Eq.refl true) : Expr)
      have hh : Q(Nat.blt $en ($eb ^ ($ek + 1)) = true) := (q(Eq.refl true) : Expr)
      ⟨ek, q(nat_log_helper $eb $en $ek $hl $hh)⟩

中文:
定义 prove自然数Log
  签名: (eb en : Q(自然数))
  定义体: match eb.natLit!, en.natLit! with
| 0, _ => have : eb =Q nat_lit 0 := ⟨⟩; ⟨q(nat_lit 0), q(nat_log_zero $en)⟩
| 1, _ => have : eb =Q nat_lit 1 := ⟨⟩; ⟨q(nat_lit 0), q(nat_log_one $en)⟩
  | b, n =>
    if n < b then
      have hh : Q(Nat.blt $en $eb = true) := (q(Eq.refl true) : Expr)
      ⟨q(nat_lit 0), q(nat_log_helper0 $eb $en $hh)⟩
    else
      let k := Nat.log b n
      have ek : Q(Nat) := mkRawNatLit k
      have hl : Q(Nat.ble ($eb ^ $ek) $en = true) := (q(Eq.refl true) : Expr)
      have hh : Q(Nat.blt $en ($eb ^ ($ek + 1)) = true) := (q(Eq.refl true) : Expr)
      ⟨ek, q(nat_log_helper $eb $en $ek $hl $hh)⟩

Depends on / 依赖: Eq.refl, Nat.ble, Nat.blt, Nat.log, eb.natLit, en.natLit, mkRawNatLit, natLit, nat_lit, nat_log_helper0, nat_log_one, nat_log_zero
-/
def proveNatLog (eb en : Q(Nat)) : (ek : Q(Nat)) × Q(Nat.log $eb $en = $ek) :=
  match eb.natLit!, en.natLit! with
| 0, _ => have : eb =Q nat_lit 0 := ⟨⟩; ⟨q(nat_lit 0), q(nat_log_zero $en)⟩
| 1, _ => have : eb =Q nat_lit 1 := ⟨⟩; ⟨q(nat_lit 0), q(nat_log_one $en)⟩
  | b, n =>
    if n < b then
      have hh : Q(Nat.blt $en $eb = true) := (q(Eq.refl true) : Expr)
      ⟨q(nat_lit 0), q(nat_log_helper0 $eb $en $hh)⟩
    else
      let k := Nat.log b n
      have ek : Q(Nat) := mkRawNatLit k
      have hl : Q(Nat.ble ($eb ^ $ek) $en = true) := (q(Eq.refl true) : Expr)
      have hh : Q(Nat.blt $en ($eb ^ ($ek + 1)) = true) := (q(Eq.refl true) : Expr)
      ⟨ek, q(nat_log_helper $eb $en $ek $hl $hh)⟩

/--
Evaluates the `Nat.log` function.
-/
@[norm_num Nat.log _ _]
/--
Definition of `evalNatLog` / `evalNatLog` 的定义

English:
definition evalNatLog
  signature: : NormNumExt where eval {u α} e
  body: do
  let mkApp2 _ (b : Q(Nat)) (n : Q(Nat)) ← Meta.whnfR e | failure
  let sNat : Q(AddMonoidWithOne Nat) := q(Nat.instAddMonoidWithOne)
  let ⟨eb, pb⟩ ← deriveNat b sNat
  let ⟨en, pn⟩ ← deriveNat n sNat
  let ⟨ek, pf⟩ := proveNatLog eb en
  let pf' : Q(IsNat (Nat.log $b $n) $ek) := q(isNat_log $pb $pn $pf)
  return .isNat sNat ek pf'

中文:
定义 eval自然数Log
  签名: : NormNumExt where eval {u α} e
  定义体: do
  let mkApp2 _ (b : Q(Nat)) (n : Q(Nat)) ← Meta.whnfR e | failure
  let sNat : Q(AddMonoidWithOne Nat) := q(Nat.instAddMonoidWithOne)
  let ⟨eb, pb⟩ ← deriveNat b sNat
  let ⟨en, pn⟩ ← deriveNat n sNat
  let ⟨ek, pf⟩ := proveNatLog eb en
  let pf' : Q(IsNat (Nat.log $b $n) $ek) := q(isNat_log $pb $pn $pf)
  return .isNat sNat ek pf'
-/
def evalNatLog : NormNumExt where eval {u α} e := do
  let mkApp2 _ (b : Q(Nat)) (n : Q(Nat)) ← Meta.whnfR e | failure
  let sNat : Q(AddMonoidWithOne Nat) := q(Nat.instAddMonoidWithOne)
  let ⟨eb, pb⟩ ← deriveNat b sNat
  let ⟨en, pn⟩ ← deriveNat n sNat
  let ⟨ek, pf⟩ := proveNatLog eb en
  let pf' : Q(IsNat (Nat.log $b $n) $ek) := q(isNat_log $pb $pn $pf)
  return .isNat sNat ek pf'

/--
lemma `nat_clog_zero_left` / 引理 `nat_clog_zero_left`

English:
lemma nat_clog_zero_left
  given: (b n : Nat) (hb : Nat.ble b 1 = true)
  proof: Nat.clog_of_left_le_one (Nat.le_of_ble_eq_true hb) n

中文:
引理 nat_clog_zero_left
  条件: (b n : 自然数) (hb : 自然数.ble b 1 = true)
  证明: Nat.clog_of_left_le_one (Nat.le_of_ble_eq_true hb) n

Depends on / 依赖: Nat.clog_of_left_le_one, Nat.le_of_ble_eq_true, clog_of_left_le_one, le_of_ble_eq_true
-/
lemma nat_clog_zero_left (b n : Nat) (hb : Nat.ble b 1 = true) :
    Nat.clog b n = 0 := Nat.clog_of_left_le_one (Nat.le_of_ble_eq_true hb) n
/--
lemma `nat_clog_zero_right` / 引理 `nat_clog_zero_right`

English:
lemma nat_clog_zero_right
  given: (b n : Nat) (hn : Nat.ble n 1 = true)
  proof: Nat.clog_of_right_le_one (Nat.le_of_ble_eq_true hn) b

中文:
引理 nat_clog_zero_right
  条件: (b n : 自然数) (hn : 自然数.ble n 1 = true)
  证明: Nat.clog_of_right_le_one (Nat.le_of_ble_eq_true hn) b

Depends on / 依赖: Nat.clog_of_right_le_one, Nat.le_of_ble_eq_true, T25Space, T25Space.t2Space, T2Space, clog_of_right_le_one, le_of_ble_eq_true, t2Space
-/
lemma nat_clog_zero_right (b n : Nat) (hn : Nat.ble n 1 = true) :
    Nat.clog b n = 0 := Nat.clog_of_right_le_one (Nat.le_of_ble_eq_true hn) b

/--
theorem `nat_clog_helper` / 定理 `nat_clog_helper`

English:
theorem nat_clog_helper
  statement: {b m n : Nat} (hb : Nat.blt 1 b = true)
  proof: by
  rw [Nat.blt_eq] at hb
  rw [Nat.blt_eq]; rw [← Nat.lt_clog_iff_pow_lt hb] at h₁
  rw [Nat.ble_eq]; rw [← Nat.clog_le_iff_le_pow hb] at h₂
  lia

中文:
定理 nat_clog_helper
  结论: {b m n : 自然数} (hb : 自然数.blt 1 b = true)
  证明: by
  rw [Nat.blt_eq] at hb
  rw [Nat.blt_eq]; rw [← Nat.lt_clog_iff_pow_lt hb] at h₁
  rw [Nat.ble_eq]; rw [← Nat.clog_le_iff_le_pow hb] at h₂
  lia

Depends on / 依赖: Nat.ble_eq, Nat.blt_eq, Nat.clog_le_iff_le_pow, Nat.lt_clog_iff_pow_lt, ble_eq, blt_eq, clog_le_iff_le_pow, lt_clog_iff_pow_lt
-/
theorem nat_clog_helper {b m n : Nat} (hb : Nat.blt 1 b = true)
    (h₁ : Nat.blt (b ^ m) n = true) (h₂ : Nat.ble n (b ^ (m + 1)) = true) :
    Nat.clog b n = m + 1 := by
  rw [Nat.blt_eq] at hb
  rw [Nat.blt_eq]; rw [← Nat.lt_clog_iff_pow_lt hb] at h₁
  rw [Nat.ble_eq]; rw [← Nat.clog_le_iff_le_pow hb] at h₂
  lia

/--
theorem `isNat_clog` / 定理 `isNat_clog`

English:
theorem isNat_clog
  statement: {b nb n nn k : Nat} -> IsNat b nb -> IsNat n nn ->

中文:
定理 is自然数_clog
  结论: {b nb n nn k : 自然数} -> 是自然数 b nb -> 是自然数 n nn ->
-/
theorem isNat_clog : {b nb n nn k : Nat} -> IsNat b nb -> IsNat n nn ->
    Nat.clog nb nn = k -> IsNat (Nat.clog b n) k
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨rfl⟩

/--
Definition of `proveNatClog` / `proveNatClog` 的定义

English:
definition proveNatClog
  signature: (eb en : Q(Nat))
  body: let b := eb.natLit!
  let n := en.natLit!
  if _ : b <= 1 then
    have h : Q(Nat.ble $eb 1 = true) := reflBoolTrue
    ⟨q(nat_lit 0), q(nat_clog_zero_left $eb $en $h)⟩
  else if _ : n <= 1 then
    have h : Q(Nat.ble $en 1 = true) := reflBoolTrue
    ⟨q(nat_lit 0), q(nat_clog_zero_right $eb $en $h)⟩
  else
    match h : Nat.clog b n with
| 0 => False.elim
      Nat.ne_of_gt (Nat.clog_pos (by lia) (by lia)) h
    | k + 1 =>
      have ek : Q(Nat) := mkRawNatLit k
      have ek1 : Q(Nat) := mkRawNatLit (k + 1)
have _ : ek1 =Q ek + 1 := ⟨⟩
      have hb : Q(Nat.blt 1 $eb = true) := reflBoolTrue
      have hl : Q(Nat.blt ($eb ^ $ek) $en = true) := reflBoolTrue
      have hh : Q(Nat.ble $en ($eb ^ ($ek + 1)) = true) := reflBoolTrue
      ⟨ek1, q(nat_clog_helper $hb $hl $hh)⟩

中文:
定义 prove自然数Clog
  签名: (eb en : Q(自然数))
  定义体: let b := eb.natLit!
  let n := en.natLit!
  if _ : b <= 1 then
    have h : Q(Nat.ble $eb 1 = true) := reflBoolTrue
    ⟨q(nat_lit 0), q(nat_clog_zero_left $eb $en $h)⟩
  else if _ : n <= 1 then
    have h : Q(Nat.ble $en 1 = true) := reflBoolTrue
    ⟨q(nat_lit 0), q(nat_clog_zero_right $eb $en $h)⟩
  else
    match h : Nat.clog b n with
| 0 => False.elim
      Nat.ne_of_gt (Nat.clog_pos (by lia) (by lia)) h
    | k + 1 =>
      have ek : Q(Nat) := mkRawNatLit k
      have ek1 : Q(Nat) := mkRawNatLit (k + 1)
have _ : ek1 =Q ek + 1 := ⟨⟩
      have hb : Q(Nat.blt 1 $eb = true) := reflBoolTrue
      have hl : Q(Nat.blt ($eb ^ $ek) $en = true) := reflBoolTrue
      have hh : Q(Nat.ble $en ($eb ^ ($ek + 1)) = true) := reflBoolTrue
      ⟨ek1, q(nat_clog_helper $hb $hl $hh)⟩

Depends on / 依赖: False.elim, Nat.ble, Nat.clog, Nat.clog_pos, Nat.ne_of_gt, clog_pos, eb.natLit, en.natLit, mkRawNatLit, natLit, nat_clog_zero_left, nat_clog_zero_right, nat_lit, ne_of_gt, reflBoolTrue
-/
def proveNatClog (eb en : Q(Nat)) : (ek : Q(Nat)) × Q(Nat.clog $eb $en = $ek) :=
  let b := eb.natLit!
  let n := en.natLit!
  if _ : b <= 1 then
    have h : Q(Nat.ble $eb 1 = true) := reflBoolTrue
    ⟨q(nat_lit 0), q(nat_clog_zero_left $eb $en $h)⟩
  else if _ : n <= 1 then
    have h : Q(Nat.ble $en 1 = true) := reflBoolTrue
    ⟨q(nat_lit 0), q(nat_clog_zero_right $eb $en $h)⟩
  else
    match h : Nat.clog b n with
| 0 => False.elim
      Nat.ne_of_gt (Nat.clog_pos (by lia) (by lia)) h
    | k + 1 =>
      have ek : Q(Nat) := mkRawNatLit k
      have ek1 : Q(Nat) := mkRawNatLit (k + 1)
have _ : ek1 =Q ek + 1 := ⟨⟩
      have hb : Q(Nat.blt 1 $eb = true) := reflBoolTrue
      have hl : Q(Nat.blt ($eb ^ $ek) $en = true) := reflBoolTrue
      have hh : Q(Nat.ble $en ($eb ^ ($ek + 1)) = true) := reflBoolTrue
      ⟨ek1, q(nat_clog_helper $hb $hl $hh)⟩

/--
Evaluates the `Nat.clog` function.
-/
@[norm_num Nat.clog _ _]
/--
Definition of `evalNatClog` / `evalNatClog` 的定义

English:
definition evalNatClog
  signature: : NormNumExt where eval {u α} e
  body: do
  let mkApp2 _ (b : Q(Nat)) (n : Q(Nat)) ← Meta.whnfR e | failure
  let sNat : Q(AddMonoidWithOne Nat) := q(Nat.instAddMonoidWithOne)
  let ⟨eb, pb⟩ ← deriveNat b sNat
  let ⟨en, pn⟩ ← deriveNat n sNat
  let ⟨ek, pf⟩ := proveNatClog eb en
  let pf' : Q(IsNat (Nat.clog $b $n) $ek) := q(isNat_clog $pb $pn $pf)
  return .isNat sNat ek pf'

中文:
定义 eval自然数Clog
  签名: : NormNumExt where eval {u α} e
  定义体: do
  let mkApp2 _ (b : Q(Nat)) (n : Q(Nat)) ← Meta.whnfR e | failure
  let sNat : Q(AddMonoidWithOne Nat) := q(Nat.instAddMonoidWithOne)
  let ⟨eb, pb⟩ ← deriveNat b sNat
  let ⟨en, pn⟩ ← deriveNat n sNat
  let ⟨ek, pf⟩ := proveNatClog eb en
  let pf' : Q(IsNat (Nat.clog $b $n) $ek) := q(isNat_clog $pb $pn $pf)
  return .isNat sNat ek pf'
-/
def evalNatClog : NormNumExt where eval {u α} e := do
  let mkApp2 _ (b : Q(Nat)) (n : Q(Nat)) ← Meta.whnfR e | failure
  let sNat : Q(AddMonoidWithOne Nat) := q(Nat.instAddMonoidWithOne)
  let ⟨eb, pb⟩ ← deriveNat b sNat
  let ⟨en, pn⟩ ← deriveNat n sNat
  let ⟨ek, pf⟩ := proveNatClog eb en
  let pf' : Q(IsNat (Nat.clog $b $n) $ek) := q(isNat_clog $pb $pn $pf)
  return .isNat sNat ek pf'

end Mathlib.Meta.NormNum
