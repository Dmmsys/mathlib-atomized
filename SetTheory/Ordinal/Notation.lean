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
/--
Inductive type `ONote` / 归纳类型 `ONote`

English:
inductive ONote
  parameters: : Type
  constructors (2):
    - zero: ONote
    - oadd: ONote -> Nat+ -> ONote -> ONote

中文:
归纳类型 ONote
  参数: : 类型
  构造子 (2 个):
    - zero: ONote
    - oadd: ONote -> 自然数+ -> ONote -> ONote
-/
inductive ONote : Type
  | zero : ONote
  | oadd : ONote -> Nat+ -> ONote -> ONote
  deriving DecidableEq

compile_inductive% ONote

namespace ONote

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero ONote
  body: ⟨zero⟩

@[simp]

中文:
实例 :
  签名: 零 ONote
  定义体: ⟨zero⟩

@[simp]
-/
instance : Zero ONote :=
  ⟨zero⟩

@[simp]
/--
theorem `zero_def` / 定理 `zero_def`

English:
theorem zero_def
  statement: zero = 0
  proof: rfl

中文:
定理 zero_def
  结论: zero = 0
  证明: rfl
-/
theorem zero_def : zero = 0 :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited ONote
  body: ⟨0⟩

中文:
实例 :
  签名: 可居 ONote
  定义体: ⟨0⟩
-/
instance : Inhabited ONote :=
  ⟨0⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One ONote
  body: ⟨oadd 0 1 0⟩

中文:
实例 :
  签名: 幺 ONote
  定义体: ⟨oadd 0 1 0⟩
-/
instance : One ONote :=
  ⟨oadd 0 1 0⟩

/--
Definition of `omega` / `omega` 的定义

English:
definition omega
  signature: : ONote
  body: oadd 1 1 0

中文:
定义 omega
  签名: : ONote
  定义体: oadd 1 1 0
-/
def omega : ONote :=
  oadd 1 1 0

/--
Definition of `repr` / `repr` 的定义

English:
definition repr
  signature: : ONote -> Ordinal.{0}

中文:
定义 repr
  签名: : ONote -> 序数.{0}
-/
noncomputable def repr : ONote -> Ordinal.{0}
  | 0 => 0
  | oadd e n a => ω ^ repr e * n + repr a
/--
theorem `repr_zero` / 定理 `repr_zero`

English:
theorem repr_zero
  statement: repr 0 = 0
  proof: rfl

中文:
定理 repr_zero
  结论: repr 0 = 0
  证明: rfl
-/
@[simp] theorem repr_zero : repr 0 = 0 := rfl
attribute [simp] repr.eq_1 repr.eq_2

set_option backward.privateInPublic true in
/--
Definition of `toStringAux` / `toStringAux` 的定义

English:
definition toStringAux
  signature: (e : ONote) (n : Nat) (s : String)
  body: if e = 0 then toString n
  else (if e = 1 then "ω" else "ω^(" ++ s ++ ")") ++ if n = 1 then "" else "*" ++ toString n

中文:
定义 toStringAux
  签名: (e : ONote) (n : 自然数) (s : String)
  定义体: if e = 0 then toString n
  else (if e = 1 then "ω" else "ω^(" ++ s ++ ")") ++ if n = 1 then "" else "*" ++ toString n
-/
private def toStringAux (e : ONote) (n : Nat) (s : String) : String :=
  if e = 0 then toString n
  else (if e = 1 then "ω" else "ω^(" ++ s ++ ")") ++ if n = 1 then "" else "*" ++ toString n

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Definition of `toString` / `toString` 的定义

English:
definition toString
  signature: : ONote -> String

中文:
定义 toString
  签名: : ONote -> String
-/
def toString : ONote -> String
  | zero => "0"
  | oadd e n 0 => toStringAux e n (toString e)
  | oadd e n a => toStringAux e n (toString e) ++ " + " ++ toString a

open Lean in
/--
Definition of `repr'` / `repr'` 的定义

English:
definition repr'
  signature: (prec : Nat)

中文:
定义 repr'
  签名: (prec : 自然数)
-/
def repr' (prec : Nat) : ONote -> Format
  | zero => "0"
  | oadd e n a =>
    Repr.addAppParen
      ("oadd " ++ (repr' max_prec e) ++ " " ++ Nat.repr (n : Nat) ++ " " ++ (repr' max_prec a))
      prec

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ToString ONote
  body: ⟨toString⟩

中文:
实例 :
  签名: ToString ONote
  定义体: ⟨toString⟩

Depends on / 依赖: toString
-/
instance : ToString ONote :=
  ⟨toString⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Repr ONote
  body: repr' prec o

中文:
实例 :
  签名: Repr ONote
  定义体: repr' prec o
-/
instance : Repr ONote where
  reprPrec o prec := repr' prec o

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Preorder ONote
  body: repr x <= repr y
  lt x y := repr x < repr y
  le_refl _ := @le_refl Ordinal _ _
  le_trans _ _ _ := @le_trans Ordinal _ _ _ _
  lt_iff_le_not_ge _ _ := @lt_iff_le_not_ge Ordinal _ _ _

中文:
实例 :
  签名: 预序 ONote
  定义体: repr x <= repr y
  lt x y := repr x < repr y
  le_refl _ := @le_refl Ordinal _ _
  le_trans _ _ _ := @le_trans Ordinal _ _ _ _
  lt_iff_le_not_ge _ _ := @lt_iff_le_not_ge Ordinal _ _ _
-/
instance : Preorder ONote where
  le x y := repr x <= repr y
  lt x y := repr x < repr y
  le_refl _ := @le_refl Ordinal _ _
  le_trans _ _ _ := @le_trans Ordinal _ _ _ _
  lt_iff_le_not_ge _ _ := @lt_iff_le_not_ge Ordinal _ _ _

/--
theorem `lt_def` / 定理 `lt_def`

English:
theorem lt_def
  given: {x y : ONote}
  statement: x < y ↔ repr x < repr y
  proof: Iff.rfl

中文:
定理 lt_def
  条件: {x y : ONote}
  结论: x < y ↔ repr x < repr y
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem lt_def {x y : ONote} : x < y ↔ repr x < repr y :=
  Iff.rfl

/--
theorem `le_def` / 定理 `le_def`

English:
theorem le_def
  given: {x y : ONote}
  statement: x <= y ↔ repr x <= repr y
  proof: Iff.rfl

@[gcongr] alias ⟨repr_le_repr, _⟩ := le_def
@[gcongr] alias ⟨repr_lt_repr, _⟩ := lt_def

中文:
定理 le_def
  条件: {x y : ONote}
  结论: x <= y ↔ repr x <= repr y
  证明: Iff.rfl

@[gcongr] alias ⟨repr_le_repr, _⟩ := le_def
@[gcongr] alias ⟨repr_lt_repr, _⟩ := lt_def

Depends on / 依赖: Iff.rfl
-/
theorem le_def {x y : ONote} : x <= y ↔ repr x <= repr y :=
  Iff.rfl

@[gcongr] alias ⟨repr_le_repr, _⟩ := le_def
@[gcongr] alias ⟨repr_lt_repr, _⟩ := lt_def

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: WellFoundedRelation ONote
  body: ⟨(· < ·), InvImage.wf repr Ordinal.lt_wf⟩

中文:
实例 :
  签名: 良基关系 ONote
  定义体: ⟨(· < ·), InvImage.wf repr Ordinal.lt_wf⟩

Depends on / 依赖: InvImage, InvImage.wf, Ordinal, Ordinal.lt_wf, lt_wf
-/
instance : WellFoundedRelation ONote :=
  ⟨(· < ·), InvImage.wf repr Ordinal.lt_wf⟩

/--
Definition of `ofNat` / `ofNat` 的定义

English:
definition ofNat
  signature: : Nat -> ONote

中文:
定义 of自然数
  签名: : 自然数 -> ONote
-/
@[coe] def ofNat : Nat -> ONote
  | 0 => 0
  | Nat.succ n => oadd 0 n.succPNat 0

/--
theorem `ofNat_zero` / 定理 `ofNat_zero`

English:
theorem ofNat_zero
  statement: ofNat 0 = 0
  proof: rfl

中文:
定理 of自然数_zero
  结论: of自然数 0 = 0
  证明: rfl
-/
@[simp] theorem ofNat_zero : ofNat 0 = 0 :=
  rfl

/--
theorem `ofNat_succ` / 定理 `ofNat_succ`

English:
theorem ofNat_succ
  given: (n)
  statement: ofNat (Nat.succ n) = oadd 0 n.succPNat 0
  proof: rfl

中文:
定理 of自然数_succ
  条件: (n)
  结论: of自然数 (自然数.succ n) = oadd 0 n.succP自然数 0
  证明: rfl
-/
@[simp] theorem ofNat_succ (n) : ofNat (Nat.succ n) = oadd 0 n.succPNat 0 :=
  rfl

instance (priority := low) nat (n : Nat) : OfNat ONote n where
  ofNat := ofNat n

/--
theorem `ofNat_one` / 定理 `ofNat_one`

English:
theorem ofNat_one
  statement: ofNat 1 = 1
  proof: rfl

中文:
定理 of自然数_one
  结论: of自然数 1 = 1
  证明: rfl
-/
@[simp 1200] theorem ofNat_one : ofNat 1 = 1 := rfl

/--
theorem `repr_ofNat` / 定理 `repr_ofNat`

English:
theorem repr_ofNat
  given: (n : Nat)
  statement: repr (ofNat n) = n
  proof: by cases n <;> simp

中文:
定理 repr_of自然数
  条件: (n : 自然数)
  结论: repr (of自然数 n) = n
  证明: by cases n <;> simp
-/
@[simp] theorem repr_ofNat (n : Nat) : repr (ofNat n) = n := by cases n <;> simp

/--
theorem `repr_one` / 定理 `repr_one`

English:
theorem repr_one
  statement: repr 1 = (1 : Nat)
  proof: repr_ofNat 1

中文:
定理 repr_one
  结论: repr 1 = (1 : 自然数)
  证明: repr_ofNat 1
-/
@[simp] theorem repr_one : repr 1 = (1 : Nat) := repr_ofNat 1

/--
theorem `omega0_le_oadd` / 定理 `omega0_le_oadd`

English:
theorem omega0_le_oadd
  given: (e n a)
  statement: ω ^ repr e <= repr (oadd e n a)
  proof: by
  refine le_trans ?_ le_self_add
  simpa using! (mul_le_mul_iff_right₀ <| opow_pos (repr e) omega0_pos).2 (Nat.cast_le.2 n.2)

中文:
定理 omega0_le_oadd
  条件: (e n a)
  结论: ω ^ repr e <= repr (oadd e n a)
  证明: by
  refine le_trans ?_ le_self_add
  simpa using! (mul_le_mul_iff_right₀ <| opow_pos (repr e) omega0_pos).2 (Nat.cast_le.2 n.2)

Depends on / 依赖: Nat.cast_le, cast_le, le_self_add, le_trans, omega0_pos, opow_pos
-/
theorem omega0_le_oadd (e n a) : ω ^ repr e <= repr (oadd e n a) := by
  refine le_trans ?_ le_self_add
  simpa using! (mul_le_mul_iff_right₀ <| opow_pos (repr e) omega0_pos).2 (Nat.cast_le.2 n.2)

/--
theorem `oadd_pos` / 定理 `oadd_pos`

English:
theorem oadd_pos
  given: (e n a)
  statement: 0 < oadd e n a
  proof: @lt_of_lt_of_le _ _ _ (ω ^ repr e) _ (opow_pos (repr e) omega0_pos) (omega0_le_oadd e n a)

中文:
定理 oadd_pos
  条件: (e n a)
  结论: 0 < oadd e n a
  证明: @lt_of_lt_of_le _ _ _ (ω ^ repr e) _ (opow_pos (repr e) omega0_pos) (omega0_le_oadd e n a)

Depends on / 依赖: lt_of_lt_of_le, omega0_le_oadd, omega0_pos, opow_pos
-/
theorem oadd_pos (e n a) : 0 < oadd e n a :=
  @lt_of_lt_of_le _ _ _ (ω ^ repr e) _ (opow_pos (repr e) omega0_pos) (omega0_le_oadd e n a)

/--
Definition of `cmp` / `cmp` 的定义

English:
definition cmp
  signature: : ONote -> ONote -> Ordering

中文:
定义 cmp
  签名: : ONote -> ONote -> Ordering
-/
def cmp : ONote -> ONote -> Ordering
  | 0, 0 => Ordering.eq
  | _, 0 => Ordering.gt
  | 0, _ => Ordering.lt
  | _o₁@(oadd e₁ n₁ a₁), _o₂@(oadd e₂ n₂ a₂) =>
(cmp e₁ e₂).then (_root_.cmp (n₁ : Nat) n₂).then (cmp a₁ a₂)

/--
theorem `eq_of_cmp_eq` / 定理 `eq_of_cmp_eq`

English:
theorem eq_of_cmp_eq
  statement: forall {o₁ o₂}, cmp o₁ o₂ = Ordering.eq -> o₁ = o₂
  proof: eq_of_cmp_eq h₁
    revert h; cases h₂ : _root_.cmp (n₁ : Nat) n₂ <;> intro h <;> try cases h
    obtain rfl := eq_of_cmp_eq h
    rw [_root_.cmp]; rw [cmpUsing_eq_eq]; rw [not_lt]; rw [not_lt]; rw [← le_antisymm_iff] at h₂
    obtain rfl := Subtype.ext h₂
    simp

中文:
定理 eq_of_cmp_eq
  结论: 对任意 {o₁ o₂}, cmp o₁ o₂ = Ordering.eq -> o₁ = o₂
  证明: eq_of_cmp_eq h₁
    revert h; cases h₂ : _root_.cmp (n₁ : Nat) n₂ <;> intro h <;> try cases h
    obtain rfl := eq_of_cmp_eq h
    rw [_root_.cmp]; rw [cmpUsing_eq_eq]; rw [not_lt]; rw [not_lt]; rw [← le_antisymm_iff] at h₂
    obtain rfl := Subtype.ext h₂
    simp

Depends on / 依赖: eq_of_cmp_eq
-/
theorem eq_of_cmp_eq : forall {o₁ o₂}, cmp o₁ o₂ = Ordering.eq -> o₁ = o₂
  | 0, 0, _ => rfl
  | oadd e n a, 0, h => by injection h
  | 0, oadd e n a, h => by injection h
  | oadd e₁ n₁ a₁, oadd e₂ n₂ a₂, h => by
    revert h; simp only [cmp]
    cases h₁ : cmp e₁ e₂ <;> intro h <;> try cases h
    obtain rfl := eq_of_cmp_eq h₁
    revert h; cases h₂ : _root_.cmp (n₁ : Nat) n₂ <;> intro h <;> try cases h
    obtain rfl := eq_of_cmp_eq h
    rw [_root_.cmp]; rw [cmpUsing_eq_eq]; rw [not_lt]; rw [not_lt]; rw [← le_antisymm_iff] at h₂
    obtain rfl := Subtype.ext h₂
    simp

/--
theorem `zero_lt_one` / 定理 `zero_lt_one`

English:
theorem zero_lt_one
  statement: (0 : ONote) < 1
  proof: by
  simp only [lt_def, repr_zero, repr_one, Nat.cast_one, zero_lt_one]

中文:
定理 zero_lt_one
  结论: (0 : ONote) < 1
  证明: by
  simp only [lt_def, repr_zero, repr_one, Nat.cast_one, zero_lt_one]
-/
protected theorem zero_lt_one : (0 : ONote) < 1 := by
  simp only [lt_def, repr_zero, repr_one, Nat.cast_one, zero_lt_one]

/--
Inductive type `NFBelow` / 归纳类型 `NFBelow`

English:
inductive NFBelow
  parameters: : ONote -> Ordinal.{0} -> Prop
  constructors (2):
    - zero: {b} : NFBelow 0 b
    - oadd': {e n a eb b} : NFBelow e eb -> NFBelow a (repr e) -> repr e < b -> NFBelow (oadd e n a) b

中文:
归纳类型 NFBelow
  参数: : ONote -> 序数.{0} -> 命题
  构造子 (2 个):
    - zero: {b} : NFBelow 0 b
    - oadd': {e n a eb b} : NFBelow e eb -> NFBelow a (repr e) -> repr e < b -> NFBelow (oadd e n a) b
-/
inductive NFBelow : ONote -> Ordinal.{0} -> Prop
  | zero {b} : NFBelow 0 b
  | oadd' {e n a eb b} : NFBelow e eb -> NFBelow a (repr e) -> repr e < b -> NFBelow (oadd e n a) b

/--
Definition of `NF` / `NF` 的定义

English:
class NF
  parameters: (o : ONote)
  axioms and operations (1):
    - out : Exists (NFBelow o)

中文:
类 NF
  参数: (o : ONote)
  公理与运算 (1 个):
    - out : 存在 (NFBelow o)
-/
class NF (o : ONote) : Prop where
  out : Exists (NFBelow o)

/--
Instance `NF.zero` / 实例 `NF.zero`

English:
instance NF.zero
  signature: : NF 0
  body: ⟨⟨0, NFBelow.zero⟩⟩

中文:
实例 NF.zero
  签名: : NF 0
  定义体: ⟨⟨0, NFBelow.zero⟩⟩

Depends on / 依赖: NFBelow, NFBelow.zero
-/
instance NF.zero : NF 0 :=
  ⟨⟨0, NFBelow.zero⟩⟩

/--
theorem `NFBelow.oadd` / 定理 `NFBelow.oadd`

English:
theorem NFBelow.oadd
  given: {e n a b}
  statement: NF e -> NFBelow a (repr e) -> repr e < b -> NFBelow (oadd e n a) b

中文:
定理 NFBelow.oadd
  条件: {e n a b}
  结论: NF e -> NFBelow a (repr e) -> repr e < b -> NFBelow (oadd e n a) b
-/
theorem NFBelow.oadd {e n a b} : NF e -> NFBelow a (repr e) -> repr e < b -> NFBelow (oadd e n a) b
  | ⟨⟨_, h⟩⟩ => NFBelow.oadd' h

/--
theorem `NFBelow.fst` / 定理 `NFBelow.fst`

English:
theorem NFBelow.fst
  given: {e n a b} (h : NFBelow (ONote.oadd e n a) b)
  statement: NF e
  proof: by
  obtain - | ⟨h₁, h₂, h₃⟩ := h; exact ⟨⟨_, h₁⟩⟩

中文:
定理 NFBelow.fst
  条件: {e n a b} (h : NFBelow (ONote.oadd e n a) b)
  结论: NF e
  证明: by
  obtain - | ⟨h₁, h₂, h₃⟩ := h; exact ⟨⟨_, h₁⟩⟩
-/
theorem NFBelow.fst {e n a b} (h : NFBelow (ONote.oadd e n a) b) : NF e := by
  obtain - | ⟨h₁, h₂, h₃⟩ := h; exact ⟨⟨_, h₁⟩⟩

/--
theorem `NF.fst` / 定理 `NF.fst`

English:
theorem NF.fst
  given: {e n a}
  statement: NF (oadd e n a) -> NF e

中文:
定理 NF.fst
  条件: {e n a}
  结论: NF (oadd e n a) -> NF e
-/
theorem NF.fst {e n a} : NF (oadd e n a) -> NF e
  | ⟨⟨_, h⟩⟩ => h.fst

/--
theorem `NFBelow.snd` / 定理 `NFBelow.snd`

English:
theorem NFBelow.snd
  given: {e n a b} (h : NFBelow (ONote.oadd e n a) b)
  statement: NFBelow a (repr e)
  proof: by
  obtain - | ⟨h₁, h₂, h₃⟩ := h; exact h₂

中文:
定理 NFBelow.snd
  条件: {e n a b} (h : NFBelow (ONote.oadd e n a) b)
  结论: NFBelow a (repr e)
  证明: by
  obtain - | ⟨h₁, h₂, h₃⟩ := h; exact h₂
-/
theorem NFBelow.snd {e n a b} (h : NFBelow (ONote.oadd e n a) b) : NFBelow a (repr e) := by
  obtain - | ⟨h₁, h₂, h₃⟩ := h; exact h₂

/--
theorem `NF.snd'` / 定理 `NF.snd'`

English:
theorem NF.snd'
  given: {e n a}
  statement: NF (oadd e n a) -> NFBelow a (repr e)

中文:
定理 NF.snd'
  条件: {e n a}
  结论: NF (oadd e n a) -> NFBelow a (repr e)
-/
theorem NF.snd' {e n a} : NF (oadd e n a) -> NFBelow a (repr e)
  | ⟨⟨_, h⟩⟩ => h.snd

/--
theorem `NF.snd` / 定理 `NF.snd`

English:
theorem NF.snd
  given: {e n a} (h : NF (oadd e n a))
  statement: NF a
  proof: ⟨⟨_, h.snd'⟩⟩

中文:
定理 NF.snd
  条件: {e n a} (h : NF (oadd e n a))
  结论: NF a
  证明: ⟨⟨_, h.snd'⟩⟩

Depends on / 依赖: h.snd
-/
theorem NF.snd {e n a} (h : NF (oadd e n a)) : NF a :=
  ⟨⟨_, h.snd'⟩⟩

/--
theorem `NF.oadd` / 定理 `NF.oadd`

English:
theorem NF.oadd
  given: {e a} (h₁ : NF e) (n) (h₂ : NFBelow a (repr e))
  statement: NF (oadd e n a)
  proof: ⟨⟨_, NFBelow.oadd h₁ h₂ (lt_succ _)⟩⟩

中文:
定理 NF.oadd
  条件: {e a} (h₁ : NF e) (n) (h₂ : NFBelow a (repr e))
  结论: NF (oadd e n a)
  证明: ⟨⟨_, NFBelow.oadd h₁ h₂ (lt_succ _)⟩⟩

Depends on / 依赖: NFBelow, NFBelow.oadd, lt_succ
-/
theorem NF.oadd {e a} (h₁ : NF e) (n) (h₂ : NFBelow a (repr e)) : NF (oadd e n a) :=
  ⟨⟨_, NFBelow.oadd h₁ h₂ (lt_succ _)⟩⟩

/--
Instance `NF.oadd_zero` / 实例 `NF.oadd_zero`

English:
instance NF.oadd_zero
  signature: (e n) [h : NF e]
  body: h.oadd _ NFBelow.zero

中文:
实例 NF.oadd_zero
  签名: (e n) [h : NF e]
  定义体: h.oadd _ NFBelow.zero

Depends on / 依赖: NFBelow, NFBelow.zero, h.oadd
-/
instance NF.oadd_zero (e n) [h : NF e] : NF (ONote.oadd e n 0) :=
  h.oadd _ NFBelow.zero

/--
theorem `NFBelow.lt` / 定理 `NFBelow.lt`

English:
theorem NFBelow.lt
  given: {e n a b} (h : NFBelow (ONote.oadd e n a) b)
  statement: repr e < b
  proof: by
  obtain - | ⟨h₁, h₂, h₃⟩ := h; exact h₃

中文:
定理 NFBelow.lt
  条件: {e n a b} (h : NFBelow (ONote.oadd e n a) b)
  结论: repr e < b
  证明: by
  obtain - | ⟨h₁, h₂, h₃⟩ := h; exact h₃
-/
theorem NFBelow.lt {e n a b} (h : NFBelow (ONote.oadd e n a) b) : repr e < b := by
  obtain - | ⟨h₁, h₂, h₃⟩ := h; exact h₃

/--
theorem `NFBelow_zero` / 定理 `NFBelow_zero`

English:
theorem NFBelow_zero
  statement: forall {o}, NFBelow o 0 ↔ o = 0

中文:
定理 NFBelow_zero
  结论: 对任意 {o}, NFBelow o 0 ↔ o = 0
-/
theorem NFBelow_zero : forall {o}, NFBelow o 0 ↔ o = 0
  | 0 => ⟨fun _ => rfl, fun _ => NFBelow.zero⟩
  | oadd _ _ _ =>
    ⟨fun h => (not_le_of_gt h.lt).elim zero_le, fun e => e.symm ▸ NFBelow.zero⟩

/--
theorem `NF.zero_of_zero` / 定理 `NF.zero_of_zero`

English:
theorem NF.zero_of_zero
  given: {e n a} (h : NF (ONote.oadd e n a)) (e0 : e = 0)
  statement: a = 0
  proof: by
  simpa [e0, NFBelow_zero] using h.snd'

中文:
定理 NF.zero_of_zero
  条件: {e n a} (h : NF (ONote.oadd e n a)) (e0 : e = 0)
  结论: a = 0
  证明: by
  simpa [e0, NFBelow_zero] using h.snd'

Depends on / 依赖: NFBelow_zero, h.snd
-/
theorem NF.zero_of_zero {e n a} (h : NF (ONote.oadd e n a)) (e0 : e = 0) : a = 0 := by
  simpa [e0, NFBelow_zero] using h.snd'

/--
theorem `NFBelow.repr_lt` / 定理 `NFBelow.repr_lt`

English:
theorem NFBelow.repr_lt
  given: {o b} (h : NFBelow o b)
  statement: repr o < ω ^ b
  proof: by
  induction h with
  | zero => exact opow_pos _ omega0_pos
  | oadd' _ _ h₃ _ IH =>
    rw [repr]
    apply (add_lt_add_right IH _).trans_le
    grw [← mul_succ, succ_le_of_lt (natCast_lt_omega0 _), ← opow_succ, succ_le_of_lt h₃]
    exact omega0_pos

中文:
定理 NFBelow.repr_lt
  条件: {o b} (h : NFBelow o b)
  结论: repr o < ω ^ b
  证明: by
  induction h with
  | zero => exact opow_pos _ omega0_pos
  | oadd' _ _ h₃ _ IH =>
    rw [repr]
    apply (add_lt_add_right IH _).trans_le
    grw [← mul_succ, succ_le_of_lt (natCast_lt_omega0 _), ← opow_succ, succ_le_of_lt h₃]
    exact omega0_pos

Depends on / 依赖: add_lt_add_right, mul_succ, natCast_lt_omega0, omega0_pos, opow_pos, opow_succ, succ_le_of_lt, trans_le
-/
theorem NFBelow.repr_lt {o b} (h : NFBelow o b) : repr o < ω ^ b := by
  induction h with
  | zero => exact opow_pos _ omega0_pos
  | oadd' _ _ h₃ _ IH =>
    rw [repr]
    apply (add_lt_add_right IH _).trans_le
    grw [← mul_succ, succ_le_of_lt (natCast_lt_omega0 _), ← opow_succ, succ_le_of_lt h₃]
    exact omega0_pos

/--
theorem `NFBelow.mono` / 定理 `NFBelow.mono`

English:
theorem NFBelow.mono
  given: {o b₁ b₂} (bb : b₁ <= b₂) (h : NFBelow o b₁)
  statement: NFBelow o b₂
  proof: by
  induction h with
  | zero => exact zero
  | oadd' h₁ h₂ h₃ _ _ => constructor; exacts [h₁, h₂, lt_of_lt_of_le h₃ bb]

中文:
定理 NFBelow.mono
  条件: {o b₁ b₂} (bb : b₁ <= b₂) (h : NFBelow o b₁)
  结论: NFBelow o b₂
  证明: by
  induction h with
  | zero => exact zero
  | oadd' h₁ h₂ h₃ _ _ => constructor; exacts [h₁, h₂, lt_of_lt_of_le h₃ bb]

Depends on / 依赖: exacts, lt_of_lt_of_le
-/
theorem NFBelow.mono {o b₁ b₂} (bb : b₁ <= b₂) (h : NFBelow o b₁) : NFBelow o b₂ := by
  induction h with
  | zero => exact zero
  | oadd' h₁ h₂ h₃ _ _ => constructor; exacts [h₁, h₂, lt_of_lt_of_le h₃ bb]

/--
theorem `NF.below_of_lt` / 定理 `NF.below_of_lt`

English:
theorem NF.below_of_lt
  given: {e n a b} (H : repr e < b)

中文:
定理 NF.below_of_lt
  条件: {e n a b} (H : repr e < b)

Depends on / 依赖: NFBelow, NFBelow.oadd
-/
theorem NF.below_of_lt {e n a b} (H : repr e < b) :
    NF (ONote.oadd e n a) -> NFBelow (ONote.oadd e n a) b
  | ⟨⟨b', h⟩⟩ => by (obtain - | ⟨h₁, h₂, h₃⟩ := h; exact NFBelow.oadd' h₁ h₂ H)

/--
theorem `NF.below_of_lt'` / 定理 `NF.below_of_lt'`

English:
theorem NF.below_of_lt'
  statement: forall {o b}, repr o < ω ^ b -> NF o -> NFBelow o b

中文:
定理 NF.below_of_lt'
  结论: 对任意 {o b}, repr o < ω ^ b -> NF o -> NFBelow o b
-/
theorem NF.below_of_lt' : forall {o b}, repr o < ω ^ b -> NF o -> NFBelow o b
  | 0, _, _, _ => NFBelow.zero
  | ONote.oadd _ _ _, _, H, h =>
h.below_of_lt
(opow_lt_opow_iff_right one_lt_omega0).1 lt_of_le_of_lt (omega0_le_oadd _ _ _) H

/--
theorem `nfBelow_ofNat` / 定理 `nfBelow_ofNat`

English:
theorem nfBelow_ofNat
  statement: forall n, NFBelow (ofNat n) 1

中文:
定理 nfBelow_of自然数
  结论: 对任意 n, NFBelow (of自然数 n) 1
-/
theorem nfBelow_ofNat : forall n, NFBelow (ofNat n) 1
  | 0 => NFBelow.zero
  | Nat.succ _ => NFBelow.oadd NF.zero NFBelow.zero zero_lt_one

/--
Instance `nf_ofNat` / 实例 `nf_ofNat`

English:
instance nf_ofNat
  signature: (n)
  body: ⟨⟨_, nfBelow_ofNat n⟩⟩

中文:
实例 nf_of自然数
  签名: (n)
  定义体: ⟨⟨_, nfBelow_ofNat n⟩⟩

Depends on / 依赖: nfBelow_ofNat
-/
instance nf_ofNat (n) : NF (ofNat n) :=
  ⟨⟨_, nfBelow_ofNat n⟩⟩

/--
Instance `nf_one` / 实例 `nf_one`

English:
instance nf_one
  signature: : NF 1
  body: by rw [← ofNat_one]; infer_instance

中文:
实例 nf_one
  签名: : NF 1
  定义体: by rw [← ofNat_one]; infer_instance

Depends on / 依赖: infer_instance, ofNat_one
-/
instance nf_one : NF 1 := by rw [← ofNat_one]; infer_instance

/--
theorem `oadd_lt_oadd_1` / 定理 `oadd_lt_oadd_1`

English:
theorem oadd_lt_oadd_1
  given: {e₁ n₁ o₁ e₂ n₂ o₂} (h₁ : NF (oadd e₁ n₁ o₁)) (h : e₁ < e₂)
  proof: @lt_of_lt_of_le _ _ (repr (oadd e₁ n₁ o₁)) _ _
    (NF.below_of_lt h h₁).repr_lt (omega0_le_oadd e₂ n₂ o₂)

中文:
定理 oadd_lt_oadd_1
  条件: {e₁ n₁ o₁ e₂ n₂ o₂} (h₁ : NF (oadd e₁ n₁ o₁)) (h : e₁ < e₂)
  证明: @lt_of_lt_of_le _ _ (repr (oadd e₁ n₁ o₁)) _ _
    (NF.below_of_lt h h₁).repr_lt (omega0_le_oadd e₂ n₂ o₂)

Depends on / 依赖: NF.below_of_lt, below_of_lt, lt_of_lt_of_le, omega0_le_oadd, repr_lt
-/
theorem oadd_lt_oadd_1 {e₁ n₁ o₁ e₂ n₂ o₂} (h₁ : NF (oadd e₁ n₁ o₁)) (h : e₁ < e₂) :
    oadd e₁ n₁ o₁ < oadd e₂ n₂ o₂ :=
  @lt_of_lt_of_le _ _ (repr (oadd e₁ n₁ o₁)) _ _
    (NF.below_of_lt h h₁).repr_lt (omega0_le_oadd e₂ n₂ o₂)

/--
theorem `oadd_lt_oadd_2` / 定理 `oadd_lt_oadd_2`

English:
theorem oadd_lt_oadd_2
  given: {e o₁ o₂ : ONote} {n₁ n₂ : Nat+} (h₁ : NF (oadd e n₁ o₁)) (h : (n₁ : Nat) < n₂)
  proof: by
  simp only [lt_def, repr]
  grw [h₁.snd'.repr_lt, ← le_self_add]
  rwa [← mul_succ, mul_le_mul_iff_right₀ (opow_pos _ omega0_pos), succ_le_iff, Nat.cast_lt]

中文:
定理 oadd_lt_oadd_2
  条件: {e o₁ o₂ : ONote} {n₁ n₂ : 自然数+} (h₁ : NF (oadd e n₁ o₁)) (h : (n₁ : 自然数) < n₂)
  证明: by
  simp only [lt_def, repr]
  grw [h₁.snd'.repr_lt, ← le_self_add]
  rwa [← mul_succ, mul_le_mul_iff_right₀ (opow_pos _ omega0_pos), succ_le_iff, Nat.cast_lt]

Depends on / 依赖: Nat.cast_lt, cast_lt, le_self_add, lt_def, mul_succ, omega0_pos, opow_pos, repr_lt, succ_le_iff
-/
theorem oadd_lt_oadd_2 {e o₁ o₂ : ONote} {n₁ n₂ : Nat+} (h₁ : NF (oadd e n₁ o₁)) (h : (n₁ : Nat) < n₂) :
    oadd e n₁ o₁ < oadd e n₂ o₂ := by
  simp only [lt_def, repr]
  grw [h₁.snd'.repr_lt, ← le_self_add]
  rwa [← mul_succ, mul_le_mul_iff_right₀ (opow_pos _ omega0_pos), succ_le_iff, Nat.cast_lt]

/--
theorem `oadd_lt_oadd_3` / 定理 `oadd_lt_oadd_3`

English:
theorem oadd_lt_oadd_3
  given: {e n a₁ a₂} (h : a₁ < a₂)
  statement: oadd e n a₁ < oadd e n a₂
  proof: by
  rw [lt_def]; unfold repr; gcongr

中文:
定理 oadd_lt_oadd_3
  条件: {e n a₁ a₂} (h : a₁ < a₂)
  结论: oadd e n a₁ < oadd e n a₂
  证明: by
  rw [lt_def]; unfold repr; gcongr

Depends on / 依赖: lt_def
-/
theorem oadd_lt_oadd_3 {e n a₁ a₂} (h : a₁ < a₂) : oadd e n a₁ < oadd e n a₂ := by
  rw [lt_def]; unfold repr; gcongr

/--
theorem `cmp_compares` / 定理 `cmp_compares`

English:
theorem cmp_compares
  statement: forall (a b : ONote) [NF a] [NF b], (cmp a b).Compares a b
  proof: @cmp_compares _ _ h₁.fst h₂.fst
    simp only [Ordering.Compares, gt_iff_lt] at IHe; revert IHe
    cases cmp e₁ e₂
    case lt => intro IHe; exact oadd_lt_oadd_1 h₁ IHe
    case gt => intro IHe; exact oadd_lt_oadd_1 h₂ IHe
    case eq =>
      intro IHe; dsimp at IHe; subst IHe
      unfold _root_.cmp; cases nh : cmpUsing (· < ·) (n₁ : Nat) n₂ <;>
      rw [cmpUsing]; rw [ite_eq_iff]; rw [not_lt] at nh
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

中文:
定理 cmp_compares
  结论: 对任意 (a b : ONote) [NF a] [NF b], (cmp a b).Compares a b
  证明: @cmp_compares _ _ h₁.fst h₂.fst
    simp only [Ordering.Compares, gt_iff_lt] at IHe; revert IHe
    cases cmp e₁ e₂
    case lt => intro IHe; exact oadd_lt_oadd_1 h₁ IHe
    case gt => intro IHe; exact oadd_lt_oadd_1 h₂ IHe
    case eq =>
      intro IHe; dsimp at IHe; subst IHe
      unfold _root_.cmp; cases nh : cmpUsing (· < ·) (n₁ : Nat) n₂ <;>
      rw [cmpUsing]; rw [ite_eq_iff]; rw [not_lt] at nh
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

Depends on / 依赖: cmp_compares
-/
theorem cmp_compares : forall (a b : ONote) [NF a] [NF b], (cmp a b).Compares a b
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
      unfold _root_.cmp; cases nh : cmpUsing (· < ·) (n₁ : Nat) n₂ <;>
      rw [cmpUsing]; rw [ite_eq_iff]; rw [not_lt] at nh
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

/--
theorem `repr_inj` / 定理 `repr_inj`

English:
theorem repr_inj
  given: {a b} [NF a] [NF b]
  statement: repr a = repr b ↔ a = b
  proof: ⟨fun e => match cmp a b, cmp_compares a b with
    | Ordering.lt, (h : repr a < repr b) => (ne_of_lt h e).elim
    | Ordering.gt, (h : repr a > repr b)=> (ne_of_gt h e).elim
    | Ordering.eq, h => h,
    congr_arg _⟩

中文:
定理 repr_inj
  条件: {a b} [NF a] [NF b]
  结论: repr a = repr b ↔ a = b
  证明: ⟨fun e => match cmp a b, cmp_compares a b with
    | Ordering.lt, (h : repr a < repr b) => (ne_of_lt h e).elim
    | Ordering.gt, (h : repr a > repr b)=> (ne_of_gt h e).elim
    | Ordering.eq, h => h,
    congr_arg _⟩

Depends on / 依赖: Ordering, Ordering.eq, Ordering.gt, Ordering.lt, cmp_compares, congr_arg, ne_of_gt, ne_of_lt
-/
theorem repr_inj {a b} [NF a] [NF b] : repr a = repr b ↔ a = b :=
  ⟨fun e => match cmp a b, cmp_compares a b with
    | Ordering.lt, (h : repr a < repr b) => (ne_of_lt h e).elim
    | Ordering.gt, (h : repr a > repr b)=> (ne_of_gt h e).elim
    | Ordering.eq, h => h,
    congr_arg _⟩

/--
theorem `NF.of_dvd_omega0_opow` / 定理 `NF.of_dvd_omega0_opow`

English:
theorem NF.of_dvd_omega0_opow
  statement: {b e n a} (h : NF (ONote.oadd e n a))
  proof: by
  have := mt repr_inj.1 (fun h => by injection h : ONote.oadd e n a != 0)
  have L := le_of_not_gt fun l => not_le_of_gt (h.below_of_lt l).repr_lt (le_of_dvd this d)
  simp only [repr] at d
  exact ⟨L, (dvd_add_iff <| (opow_dvd_opow _ L).mul_right _).1 d⟩

中文:
定理 NF.of_dvd_omega0_opow
  结论: {b e n a} (h : NF (ONote.oadd e n a))
  证明: by
  have := mt repr_inj.1 (fun h => by injection h : ONote.oadd e n a != 0)
  have L := le_of_not_gt fun l => not_le_of_gt (h.below_of_lt l).repr_lt (le_of_dvd this d)
  simp only [repr] at d
  exact ⟨L, (dvd_add_iff <| (opow_dvd_opow _ L).mul_right _).1 d⟩

Depends on / 依赖: ONote.oadd, below_of_lt, dvd_add_iff, h.below_of_lt, injection, le_of_dvd, le_of_not_gt, mul_right, not_le_of_gt, opow_dvd_opow, repr_inj, repr_lt
-/
theorem NF.of_dvd_omega0_opow {b e n a} (h : NF (ONote.oadd e n a))
    (d : ω ^ b ∣ repr (ONote.oadd e n a)) :
    b <= repr e ∧ ω ^ b ∣ repr a := by
  have := mt repr_inj.1 (fun h => by injection h : ONote.oadd e n a != 0)
  have L := le_of_not_gt fun l => not_le_of_gt (h.below_of_lt l).repr_lt (le_of_dvd this d)
  simp only [repr] at d
  exact ⟨L, (dvd_add_iff <| (opow_dvd_opow _ L).mul_right _).1 d⟩

/--
theorem `NF.of_dvd_omega0` / 定理 `NF.of_dvd_omega0`

English:
theorem NF.of_dvd_omega0
  given: {e n a} (h : NF (ONote.oadd e n a))
  proof: by
  (rw [← opow_one ω, ← one_le_iff_ne_zero]; exact h.of_dvd_omega0_opow)

中文:
定理 NF.of_dvd_omega0
  条件: {e n a} (h : NF (ONote.oadd e n a))
  证明: by
  (rw [← opow_one ω, ← one_le_iff_ne_zero]; exact h.of_dvd_omega0_opow)

Depends on / 依赖: h.of_dvd_omega0_opow, of_dvd_omega0_opow, one_le_iff_ne_zero, opow_one
-/
theorem NF.of_dvd_omega0 {e n a} (h : NF (ONote.oadd e n a)) :
    ω ∣ repr (ONote.oadd e n a) -> repr e != 0 ∧ ω ∣ repr a := by
  (rw [← opow_one ω, ← one_le_iff_ne_zero]; exact h.of_dvd_omega0_opow)

/--
Definition of `TopBelow` / `TopBelow` 的定义

English:
definition TopBelow
  signature: (b : ONote)

中文:
定义 TopBelow
  签名: (b : ONote)
-/
def TopBelow (b : ONote) : ONote -> Prop
  | 0 => True
  | oadd e _ _ => cmp e b = Ordering.lt

/--
Instance `decidableTopBelow` / 实例 `decidableTopBelow`

English:
instance decidableTopBelow
  signature: : DecidableRel TopBelow
  body: by
  intro b o
  cases o <;> delta TopBelow <;> infer_instance

中文:
实例 decidableTopBelow
  签名: : DecidableRel TopBelow
  定义体: by
  intro b o
  cases o <;> delta TopBelow <;> infer_instance

Depends on / 依赖: TopBelow, infer_instance
-/
instance decidableTopBelow : DecidableRel TopBelow := by
  intro b o
  cases o <;> delta TopBelow <;> infer_instance

/--
theorem `nfBelow_iff_topBelow` / 定理 `nfBelow_iff_topBelow`

English:
theorem nfBelow_iff_topBelow
  given: {b} [NF b]
  statement: forall {o}, NFBelow o (repr b) ↔ NF o ∧ TopBelow b o

中文:
定理 nfBelow_iff_topBelow
  条件: {b} [NF b]
  结论: 对任意 {o}, NFBelow o (repr b) ↔ NF o ∧ TopBelow b o
-/
theorem nfBelow_iff_topBelow {b} [NF b] : forall {o}, NFBelow o (repr b) ↔ NF o ∧ TopBelow b o
  | 0 => ⟨fun h => ⟨⟨⟨_, h⟩⟩, trivial⟩, fun _ => NFBelow.zero⟩
  | oadd _ _ _ =>
    ⟨fun h => ⟨⟨⟨_, h⟩⟩, (@cmp_compares _ b h.fst _).eq_lt.2 h.lt⟩, fun ⟨h₁, h₂⟩ =>
h₁.below_of_lt (@cmp_compares _ b h₁.fst _).eq_lt.1 h₂⟩

/--
Instance `decidableNF` / 实例 `decidableNF`

English:
instance decidableNF
  signature: : DecidablePred NF
  body: decidableNF e
    have := decidableNF a
    apply decidable_of_iff (NF e ∧ NF a ∧ TopBelow e a)
    rw [← and_congr_right fun h => @nfBelow_iff_topBelow _ h _]
    exact ⟨fun ⟨h₁, h₂⟩ => NF.oadd h₁ n h₂, fun h => ⟨h.fst, h.snd'⟩⟩

中文:
实例 decidableNF
  签名: : DecidablePred NF
  定义体: decidableNF e
    have := decidableNF a
    apply decidable_of_iff (NF e ∧ NF a ∧ TopBelow e a)
    rw [← and_congr_right fun h => @nfBelow_iff_topBelow _ h _]
    exact ⟨fun ⟨h₁, h₂⟩ => NF.oadd h₁ n h₂, fun h => ⟨h.fst, h.snd'⟩⟩

Depends on / 依赖: decidableNF
-/
instance decidableNF : DecidablePred NF
  | 0 => isTrue NF.zero
  | oadd e n a => by
    have := decidableNF e
    have := decidableNF a
    apply decidable_of_iff (NF e ∧ NF a ∧ TopBelow e a)
    rw [← and_congr_right fun h => @nfBelow_iff_topBelow _ h _]
    exact ⟨fun ⟨h₁, h₂⟩ => NF.oadd h₁ n h₂, fun h => ⟨h.fst, h.snd'⟩⟩

/--
Definition of `addAux` / `addAux` 的定义

English:
definition addAux
  signature: (e : ONote) (n : Nat+) (o : ONote)
  body: match o with
    | 0 => oadd e n 0
    | o'@(oadd e' n' a') =>
      match cmp e e' with
      | Ordering.lt => o'
      | Ordering.eq => oadd e (n + n') a'
      | Ordering.gt => oadd e n o'

中文:
定义 addAux
  签名: (e : ONote) (n : 自然数+) (o : ONote)
  定义体: match o with
    | 0 => oadd e n 0
    | o'@(oadd e' n' a') =>
      match cmp e e' with
      | Ordering.lt => o'
      | Ordering.eq => oadd e (n + n') a'
      | Ordering.gt => oadd e n o'

Depends on / 依赖: Ordering, Ordering.eq, Ordering.gt, Ordering.lt
-/
def addAux (e : ONote) (n : Nat+) (o : ONote) : ONote :=
    match o with
    | 0 => oadd e n 0
    | o'@(oadd e' n' a') =>
      match cmp e e' with
      | Ordering.lt => o'
      | Ordering.eq => oadd e (n + n') a'
      | Ordering.gt => oadd e n o'

/--
Definition of `add` / `add` 的定义

English:
definition add
  signature: : ONote -> ONote -> ONote

中文:
定义 add
  签名: : ONote -> ONote -> ONote
-/
def add : ONote -> ONote -> ONote
  | 0, o => o
  | oadd e n a, o => addAux e n (add a o)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add ONote
  body: ⟨add⟩

@[simp]

中文:
实例 :
  签名: 加法 ONote
  定义体: ⟨add⟩

@[simp]
-/
instance : Add ONote :=
  ⟨add⟩

@[simp]
/--
theorem `zero_add` / 定理 `zero_add`

English:
theorem zero_add
  given: (o : ONote)
  statement: 0 + o = o
  proof: rfl

中文:
定理 zero_add
  条件: (o : ONote)
  结论: 0 + o = o
  证明: rfl
-/
theorem zero_add (o : ONote) : 0 + o = o :=
  rfl

/--
theorem `oadd_add` / 定理 `oadd_add`

English:
theorem oadd_add
  given: (e n a o)
  statement: oadd e n a + o = addAux e n (a + o)
  proof: rfl

中文:
定理 oadd_add
  条件: (e n a o)
  结论: oadd e n a + o = addAux e n (a + o)
  证明: rfl
-/
theorem oadd_add (e n a o) : oadd e n a + o = addAux e n (a + o) :=
  rfl

/--
Definition of `sub` / `sub` 的定义

English:
definition sub
  signature: : ONote -> ONote -> ONote

中文:
定义 sub
  签名: : ONote -> ONote -> ONote
-/
def sub : ONote -> ONote -> ONote
  | 0, _ => 0
  | o, 0 => o
  | o₁@(oadd e₁ n₁ a₁), oadd e₂ n₂ a₂ =>
    match cmp e₁ e₂ with
    | Ordering.lt => 0
    | Ordering.gt => o₁
    | Ordering.eq =>
      match (n₁ : Nat) - n₂ with
      | 0 => if n₁ = n₂ then sub a₁ a₂ else 0
      | Nat.succ k => oadd e₁ k.succPNat a₁

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Sub ONote
  body: ⟨sub⟩

中文:
实例 :
  签名: 减法 ONote
  定义体: ⟨sub⟩
-/
instance : Sub ONote :=
  ⟨sub⟩

/--
theorem `add_nfBelow` / 定理 `add_nfBelow`

English:
theorem add_nfBelow
  given: {b}
  statement: forall {o₁ o₂}, NFBelow o₁ b -> NFBelow o₂ b -> NFBelow (o₁ + o₂) b
  proof: add_nfBelow (h₁.snd.mono <| le_of_lt h₁.lt) h₂
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

中文:
定理 add_nfBelow
  条件: {b}
  结论: 对任意 {o₁ o₂}, NFBelow o₁ b -> NFBelow o₂ b -> NFBelow (o₁ + o₂) b
  证明: add_nfBelow (h₁.snd.mono <| le_of_lt h₁.lt) h₂
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

Depends on / 依赖: add_nfBelow, le_of_lt, snd.mono
-/
theorem add_nfBelow {b} : forall {o₁ o₂}, NFBelow o₁ b -> NFBelow o₂ b -> NFBelow (o₁ + o₂) b
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

/--
Instance `add_nf` / 实例 `add_nf`

English:
instance add_nf
  signature: (o₁ o₂)

中文:
实例 add_nf
  签名: (o₁ o₂)
-/
instance add_nf (o₁ o₂) : forall [NF o₁] [NF o₂], NF (o₁ + o₂)
  | ⟨⟨b₁, h₁⟩⟩, ⟨⟨b₂, h₂⟩⟩ =>
    ⟨(le_total b₁ b₂).elim (fun h => ⟨b₂, add_nfBelow (h₁.mono h) h₂⟩) fun h =>
        ⟨b₁, add_nfBelow h₁ (h₂.mono h)⟩⟩

@[simp]
/--
theorem `repr_add` / 定理 `repr_add`

English:
theorem repr_add
  statement: forall (o₁ o₂) [NF o₁] [NF o₂], repr (o₁ + o₂) = repr o₁ + repr o₂
  proof: h₁.snd; have h' := repr_add a o
    conv_lhs at h' => simp [HAdd.hAdd, Add.add]
    have nf := ONote.add_nf a o
    conv at nf => simp [HAdd.hAdd, Add.add]
    conv in _ + o => simp [HAdd.hAdd, Add.add]
    rcases h : add a o with - | ⟨e', n', a'⟩ <;>
      simp only [add, addAux, h'.symm, h, add_assoc, repr] at nf h₁ ⊢
    have := h₁.fst; have := nf.fst; have ee := cmp_compares e e'
    cases he : cmp e e' <;> simp only [he, Ordering.compares_gt, Ordering.compares_lt,
        Ordering.compares_eq, repr, gt_iff_lt, PNat.add_coe, Nat.cast_add] at ee ⊢
    · rw [← add_assoc, @add_of_omega0_opow_le _ (repr e') (ω ^ repr e' * (n' : Nat))]
      · have := (h₁.below_of_lt ee).repr_lt
        simp only [repr] at this
        cases he' : e' <;>
          simp only [he', zero_def, opow_zero, repr, repr_zero, gt_iff_lt] at this ⊢ <;>
          exact lt_of_le_of_lt le_self_add this
      · simpa using (mul_le_mul_iff_right₀ <| opow_pos (repr e') omega0_pos).2
          (Nat.cast_le.2 n'.pos)
    · rw [ee, ← add_assoc, ← mul_add]

中文:
定理 repr_add
  结论: 对任意 (o₁ o₂) [NF o₁] [NF o₂], repr (o₁ + o₂) = repr o₁ + repr o₂
  证明: h₁.snd; have h' := repr_add a o
    conv_lhs at h' => simp [HAdd.hAdd, Add.add]
    have nf := ONote.add_nf a o
    conv at nf => simp [HAdd.hAdd, Add.add]
    conv in _ + o => simp [HAdd.hAdd, Add.add]
    rcases h : add a o with - | ⟨e', n', a'⟩ <;>
      simp only [add, addAux, h'.symm, h, add_assoc, repr] at nf h₁ ⊢
    have := h₁.fst; have := nf.fst; have ee := cmp_compares e e'
    cases he : cmp e e' <;> simp only [he, Ordering.compares_gt, Ordering.compares_lt,
        Ordering.compares_eq, repr, gt_iff_lt, PNat.add_coe, Nat.cast_add] at ee ⊢
    · rw [← add_assoc, @add_of_omega0_opow_le _ (repr e') (ω ^ repr e' * (n' : Nat))]
      · have := (h₁.below_of_lt ee).repr_lt
        simp only [repr] at this
        cases he' : e' <;>
          simp only [he', zero_def, opow_zero, repr, repr_zero, gt_iff_lt] at this ⊢ <;>
          exact lt_of_le_of_lt le_self_add this
      · simpa using (mul_le_mul_iff_right₀ <| opow_pos (repr e') omega0_pos).2
          (Nat.cast_le.2 n'.pos)
    · rw [ee, ← add_assoc, ← mul_add]

Depends on / 依赖: repr_add
-/
theorem repr_add : forall (o₁ o₂) [NF o₁] [NF o₂], repr (o₁ + o₂) = repr o₁ + repr o₂
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
    · rw [← add_assoc, @add_of_omega0_opow_le _ (repr e') (ω ^ repr e' * (n' : Nat))]
      · have := (h₁.below_of_lt ee).repr_lt
        simp only [repr] at this
        cases he' : e' <;>
          simp only [he', zero_def, opow_zero, repr, repr_zero, gt_iff_lt] at this ⊢ <;>
          exact lt_of_le_of_lt le_self_add this
      · simpa using (mul_le_mul_iff_right₀ <| opow_pos (repr e') omega0_pos).2
          (Nat.cast_le.2 n'.pos)
    · rw [ee, ← add_assoc, ← mul_add]

/--
theorem `sub_nfBelow` / 定理 `sub_nfBelow`

English:
theorem sub_nfBelow
  statement: forall {o₁ o₂ b}, NFBelow o₁ b -> NF o₂ -> NFBelow (o₁ - o₂) b
  proof: sub_nfBelow h₁.snd h₂.snd
    simp only [HSub.hSub, Sub.sub, sub] at h' ⊢
    have := @cmp_compares _ _ h₁.fst h₂.fst
    cases h : cmp e₁ e₂
    · apply NFBelow.zero
    · rw [Nat.sub_eq]
      simp only [h, Ordering.compares_eq] at this
      subst e₂
      cases (n₁ : Nat) - n₂
      · by_cases en : n₁ = n₂ <;> simp only [en, ↓reduceIte]
        · exact h'.mono (le_of_lt h₁.lt)
        · exact NFBelow.zero
      · exact NFBelow.oadd h₁.fst h₁.snd h₁.lt
    · exact h₁

中文:
定理 sub_nfBelow
  结论: 对任意 {o₁ o₂ b}, NFBelow o₁ b -> NF o₂ -> NFBelow (o₁ - o₂) b
  证明: sub_nfBelow h₁.snd h₂.snd
    simp only [HSub.hSub, Sub.sub, sub] at h' ⊢
    have := @cmp_compares _ _ h₁.fst h₂.fst
    cases h : cmp e₁ e₂
    · apply NFBelow.zero
    · rw [Nat.sub_eq]
      simp only [h, Ordering.compares_eq] at this
      subst e₂
      cases (n₁ : Nat) - n₂
      · by_cases en : n₁ = n₂ <;> simp only [en, ↓reduceIte]
        · exact h'.mono (le_of_lt h₁.lt)
        · exact NFBelow.zero
      · exact NFBelow.oadd h₁.fst h₁.snd h₁.lt
    · exact h₁

Depends on / 依赖: sub_nfBelow
-/
theorem sub_nfBelow : forall {o₁ o₂ b}, NFBelow o₁ b -> NF o₂ -> NFBelow (o₁ - o₂) b
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
      cases (n₁ : Nat) - n₂
      · by_cases en : n₁ = n₂ <;> simp only [en, ↓reduceIte]
        · exact h'.mono (le_of_lt h₁.lt)
        · exact NFBelow.zero
      · exact NFBelow.oadd h₁.fst h₁.snd h₁.lt
    · exact h₁

/--
Instance `sub_nf` / 实例 `sub_nf`

English:
instance sub_nf
  signature: (o₁ o₂)

中文:
实例 sub_nf
  签名: (o₁ o₂)
-/
instance sub_nf (o₁ o₂) : forall [NF o₁] [NF o₂], NF (o₁ - o₂)
  | ⟨⟨b₁, h₁⟩⟩, h₂ => ⟨⟨b₁, sub_nfBelow h₁ h₂⟩⟩

@[simp]
/--
theorem `repr_sub` / 定理 `repr_sub`

English:
theorem repr_sub
  statement: forall (o₁ o₂) [NF o₁] [NF o₂], repr (o₁ - o₂) = repr o₁ - repr o₂
  proof: h₁.snd; have := h₂.snd; have h' := repr_sub a₁ a₂
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
      cases mn : (n₁ : Nat) - n₂ <;> dsimp only
      · by_cases en : n₁ = n₂
        · simpa [en]
        · simp only [en, ite_false]
          exact
            (Ordinal.sub_eq_zero_iff_le.2 <|
le_of_lt
oadd_lt_oadd_2 h₁
                    lt_of_le_of_ne (tsub_eq_zero_iff_le.1 mn) (mt PNat.eq en)).symm
      · simp only [Nat.succPNat, Nat.succ_eq_add_one, repr, PNat.mk_coe, ← succ_eq_add_one]
        rw [(tsub_eq_iff_eq_add_of_le <| le_of_lt <| Nat.lt_of_sub_eq_succ mn).1 mn]; rw [add_comm]; rw [Nat.cast_add]; rw [mul_add]; rw [add_assoc]; rw [add_sub_add_cancel]
        refine
          (Ordinal.sub_eq_of_add_eq <|
add_of_omega0_opow_le h₂.snd'.repr_lt le_trans ?_ le_self_add).symm
        exact Ordinal.le_mul_left _ (Nat.cast_lt.2 <| Nat.succ_pos _)
    · exact
        (Ordinal.sub_eq_of_add_eq <|
add_of_omega0_opow_le (h₂.below_of_lt ee).repr_lt omega0_le_oadd _ _ _).symm

中文:
定理 repr_sub
  结论: 对任意 (o₁ o₂) [NF o₁] [NF o₂], repr (o₁ - o₂) = repr o₁ - repr o₂
  证明: h₁.snd; have := h₂.snd; have h' := repr_sub a₁ a₂
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
      cases mn : (n₁ : Nat) - n₂ <;> dsimp only
      · by_cases en : n₁ = n₂
        · simpa [en]
        · simp only [en, ite_false]
          exact
            (Ordinal.sub_eq_zero_iff_le.2 <|
le_of_lt
oadd_lt_oadd_2 h₁
                    lt_of_le_of_ne (tsub_eq_zero_iff_le.1 mn) (mt PNat.eq en)).symm
      · simp only [Nat.succPNat, Nat.succ_eq_add_one, repr, PNat.mk_coe, ← succ_eq_add_one]
        rw [(tsub_eq_iff_eq_add_of_le <| le_of_lt <| Nat.lt_of_sub_eq_succ mn).1 mn]; rw [add_comm]; rw [Nat.cast_add]; rw [mul_add]; rw [add_assoc]; rw [add_sub_add_cancel]
        refine
          (Ordinal.sub_eq_of_add_eq <|
add_of_omega0_opow_le h₂.snd'.repr_lt le_trans ?_ le_self_add).symm
        exact Ordinal.le_mul_left _ (Nat.cast_lt.2 <| Nat.succ_pos _)
    · exact
        (Ordinal.sub_eq_of_add_eq <|
add_of_omega0_opow_le (h₂.below_of_lt ee).repr_lt omega0_le_oadd _ _ _).symm

Depends on / 依赖: repr_sub
-/
theorem repr_sub : forall (o₁ o₂) [NF o₁] [NF o₂], repr (o₁ - o₂) = repr o₁ - repr o₂
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
      cases mn : (n₁ : Nat) - n₂ <;> dsimp only
      · by_cases en : n₁ = n₂
        · simpa [en]
        · simp only [en, ite_false]
          exact
            (Ordinal.sub_eq_zero_iff_le.2 <|
le_of_lt
oadd_lt_oadd_2 h₁
                    lt_of_le_of_ne (tsub_eq_zero_iff_le.1 mn) (mt PNat.eq en)).symm
      · simp only [Nat.succPNat, Nat.succ_eq_add_one, repr, PNat.mk_coe, ← succ_eq_add_one]
        rw [(tsub_eq_iff_eq_add_of_le <| le_of_lt <| Nat.lt_of_sub_eq_succ mn).1 mn]; rw [add_comm]; rw [Nat.cast_add]; rw [mul_add]; rw [add_assoc]; rw [add_sub_add_cancel]
        refine
          (Ordinal.sub_eq_of_add_eq <|
add_of_omega0_opow_le h₂.snd'.repr_lt le_trans ?_ le_self_add).symm
        exact Ordinal.le_mul_left _ (Nat.cast_lt.2 <| Nat.succ_pos _)
    · exact
        (Ordinal.sub_eq_of_add_eq <|
add_of_omega0_opow_le (h₂.below_of_lt ee).repr_lt omega0_le_oadd _ _ _).symm

/--
Definition of `mul` / `mul` 的定义

English:
definition mul
  signature: : ONote -> ONote -> ONote

中文:
定义 mul
  签名: : ONote -> ONote -> ONote
-/
def mul : ONote -> ONote -> ONote
  | 0, _ => 0
  | _, 0 => 0
  | o₁@(oadd e₁ n₁ a₁), oadd e₂ n₂ a₂ =>
    if e₂ = 0 then oadd e₁ (n₁ * n₂) a₁ else oadd (e₁ + e₂) n₂ (mul o₁ a₂)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mul ONote
  body: ⟨mul⟩

中文:
实例 :
  签名: 乘法 ONote
  定义体: ⟨mul⟩
-/
instance : Mul ONote :=
  ⟨mul⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulZeroClass ONote
  body: by cases o <;> rfl
  mul_zero o := by cases o <;> rfl

中文:
实例 :
  签名: 乘零类 ONote
  定义体: by cases o <;> rfl
  mul_zero o := by cases o <;> rfl

Depends on / 依赖: mul_zero
-/
instance : MulZeroClass ONote where
  zero_mul o := by cases o <;> rfl
  mul_zero o := by cases o <;> rfl

/--
theorem `oadd_mul` / 定理 `oadd_mul`

English:
theorem oadd_mul
  given: (e₁ n₁ a₁ e₂ n₂ a₂)
  proof: rfl

中文:
定理 oadd_mul
  条件: (e₁ n₁ a₁ e₂ n₂ a₂)
  证明: rfl
-/
theorem oadd_mul (e₁ n₁ a₁ e₂ n₂ a₂) :
    oadd e₁ n₁ a₁ * oadd e₂ n₂ a₂ =
      if e₂ = 0 then oadd e₁ (n₁ * n₂) a₁ else oadd (e₁ + e₂) n₂ (oadd e₁ n₁ a₁ * a₂) :=
  rfl

/--
theorem `oadd_mul_nfBelow` / 定理 `oadd_mul_nfBelow`

English:
theorem oadd_mul_nfBelow
  given: {e₁ n₁ a₁ b₁} (h₁ : NFBelow (oadd e₁ n₁ a₁) b₁)
  proof: oadd_mul_nfBelow h₁ h₂.snd
    by_cases e0 : e₂ = 0 <;> simp only [e0, oadd_mul, ↓reduceIte]
    · apply NFBelow.oadd h₁.fst h₁.snd
      grw [← h₂.lt.pos, add_zero]
    · have := h₁.fst
      have := h₂.fst
      apply NFBelow.oadd
      · infer_instance
      · rwa [repr_add]
      · grw [repr_add, h₂.lt]

中文:
定理 oadd_mul_nfBelow
  条件: {e₁ n₁ a₁ b₁} (h₁ : NFBelow (oadd e₁ n₁ a₁) b₁)
  证明: oadd_mul_nfBelow h₁ h₂.snd
    by_cases e0 : e₂ = 0 <;> simp only [e0, oadd_mul, ↓reduceIte]
    · apply NFBelow.oadd h₁.fst h₁.snd
      grw [← h₂.lt.pos, add_zero]
    · have := h₁.fst
      have := h₂.fst
      apply NFBelow.oadd
      · infer_instance
      · rwa [repr_add]
      · grw [repr_add, h₂.lt]

Depends on / 依赖: oadd_mul_nfBelow
-/
theorem oadd_mul_nfBelow {e₁ n₁ a₁ b₁} (h₁ : NFBelow (oadd e₁ n₁ a₁) b₁) :
    forall {o₂ b₂}, NFBelow o₂ b₂ -> NFBelow (oadd e₁ n₁ a₁ * o₂) (repr e₁ + b₂)
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

/--
Instance `mul_nf` / 实例 `mul_nf`

English:
instance mul_nf
  signature: : forall (o₁ o₂) [NF o₁] [NF o₂], NF (o₁ * o₂)

中文:
实例 mul_nf
  签名: : 对任意 (o₁ o₂) [NF o₁] [NF o₂], NF (o₁ * o₂)
-/
instance mul_nf : forall (o₁ o₂) [NF o₁] [NF o₂], NF (o₁ * o₂)
  | 0, o, _, h₂ => by cases o <;> exact NF.zero
  | oadd _ _ _, _, ⟨⟨_, hb₁⟩⟩, ⟨⟨_, hb₂⟩⟩ => ⟨⟨_, oadd_mul_nfBelow hb₁ hb₂⟩⟩

@[simp]
/--
theorem `repr_mul` / 定理 `repr_mul`

English:
theorem repr_mul
  statement: forall (o₁ o₂) [NF o₁] [NF o₂], repr (o₁ * o₂) = repr o₁ * repr o₂
  proof: @repr_mul _ _ h₁ h₂.snd
    conv =>
      lhs
      simp [(· * ·)]
    have ao : repr a₁ + ω ^ repr e₁ * (n₁ : Nat) = ω ^ repr e₁ * (n₁ : Nat) := by
      apply add_of_omega0_opow_le h₁.snd'.repr_lt
      simpa using! (mul_le_mul_iff_right₀ <| opow_pos _ omega0_pos).2 (Nat.cast_le.2 n₁.2)
    by_cases e0 : e₂ = 0
    · obtain ⟨x, xe⟩ := Nat.exists_eq_succ_of_ne_zero n₂.ne_zero
      simp only [Mul.mul, mul, e0, ↓reduceIte, repr, repr_zero, PNat.mul_coe, natCast_mul,
        opow_zero, one_mul]
      simp only [xe, h₂.zero_of_zero e0, repr_zero, add_zero]
      rw [Nat.cast_add_one x]; rw [add_mul_add_one _ ao]; rw [mul_assoc]
    · simp only [repr]
      have := h₁.fst
      have := h₂.fst
      simp only [Mul.mul, mul, e0, ite_false, repr.eq_2, repr_add, opow_add, IH, repr, mul_add]
      rw [← mul_assoc]
      congr 2
      have := mt repr_inj.1 e0
      rw [add_mul_of_isSuccLimit ao (isSuccLimit_opow_left isSuccLimit_omega0 this)]; rw [mul_assoc]; rw [mul_omega0_dvd (Nat.cast_pos'.2 n₁.pos) (natCast_lt_omega0 _)]
      simpa using! opow_dvd_opow ω (one_le_iff_ne_zero.2 this)

中文:
定理 repr_mul
  结论: 对任意 (o₁ o₂) [NF o₁] [NF o₂], repr (o₁ * o₂) = repr o₁ * repr o₂
  证明: @repr_mul _ _ h₁ h₂.snd
    conv =>
      lhs
      simp [(· * ·)]
    have ao : repr a₁ + ω ^ repr e₁ * (n₁ : Nat) = ω ^ repr e₁ * (n₁ : Nat) := by
      apply add_of_omega0_opow_le h₁.snd'.repr_lt
      simpa using! (mul_le_mul_iff_right₀ <| opow_pos _ omega0_pos).2 (Nat.cast_le.2 n₁.2)
    by_cases e0 : e₂ = 0
    · obtain ⟨x, xe⟩ := Nat.exists_eq_succ_of_ne_zero n₂.ne_zero
      simp only [Mul.mul, mul, e0, ↓reduceIte, repr, repr_zero, PNat.mul_coe, natCast_mul,
        opow_zero, one_mul]
      simp only [xe, h₂.zero_of_zero e0, repr_zero, add_zero]
      rw [Nat.cast_add_one x]; rw [add_mul_add_one _ ao]; rw [mul_assoc]
    · simp only [repr]
      have := h₁.fst
      have := h₂.fst
      simp only [Mul.mul, mul, e0, ite_false, repr.eq_2, repr_add, opow_add, IH, repr, mul_add]
      rw [← mul_assoc]
      congr 2
      have := mt repr_inj.1 e0
      rw [add_mul_of_isSuccLimit ao (isSuccLimit_opow_left isSuccLimit_omega0 this)]; rw [mul_assoc]; rw [mul_omega0_dvd (Nat.cast_pos'.2 n₁.pos) (natCast_lt_omega0 _)]
      simpa using! opow_dvd_opow ω (one_le_iff_ne_zero.2 this)

Depends on / 依赖: repr_mul
-/
theorem repr_mul : forall (o₁ o₂) [NF o₁] [NF o₂], repr (o₁ * o₂) = repr o₁ * repr o₂
  | 0, o, _, h₂ => by cases o <;> exact (zero_mul _).symm
  | oadd _ _ _, 0, _, _ => (mul_zero _).symm
  | oadd e₁ n₁ a₁, oadd e₂ n₂ a₂, h₁, h₂ => by
    have IH : repr (mul _ _) = _ := @repr_mul _ _ h₁ h₂.snd
    conv =>
      lhs
      simp [(· * ·)]
    have ao : repr a₁ + ω ^ repr e₁ * (n₁ : Nat) = ω ^ repr e₁ * (n₁ : Nat) := by
      apply add_of_omega0_opow_le h₁.snd'.repr_lt
      simpa using! (mul_le_mul_iff_right₀ <| opow_pos _ omega0_pos).2 (Nat.cast_le.2 n₁.2)
    by_cases e0 : e₂ = 0
    · obtain ⟨x, xe⟩ := Nat.exists_eq_succ_of_ne_zero n₂.ne_zero
      simp only [Mul.mul, mul, e0, ↓reduceIte, repr, repr_zero, PNat.mul_coe, natCast_mul,
        opow_zero, one_mul]
      simp only [xe, h₂.zero_of_zero e0, repr_zero, add_zero]
      rw [Nat.cast_add_one x]; rw [add_mul_add_one _ ao]; rw [mul_assoc]
    · simp only [repr]
      have := h₁.fst
      have := h₂.fst
      simp only [Mul.mul, mul, e0, ite_false, repr.eq_2, repr_add, opow_add, IH, repr, mul_add]
      rw [← mul_assoc]
      congr 2
      have := mt repr_inj.1 e0
      rw [add_mul_of_isSuccLimit ao (isSuccLimit_opow_left isSuccLimit_omega0 this)]; rw [mul_assoc]; rw [mul_omega0_dvd (Nat.cast_pos'.2 n₁.pos) (natCast_lt_omega0 _)]
      simpa using! opow_dvd_opow ω (one_le_iff_ne_zero.2 this)

/--
Definition of `split'` / `split'` 的定义

English:
definition split'
  signature: : ONote -> ONote × Nat
  body: split' a
      (oadd (e - 1) n a', m)

中文:
定义 split'
  签名: : ONote -> ONote × 自然数
  定义体: split' a
      (oadd (e - 1) n a', m)
-/
def split' : ONote -> ONote × Nat
  | 0 => (0, 0)
  | oadd e n a =>
    if e = 0 then (0, n)
    else
      let (a', m) := split' a
      (oadd (e - 1) n a', m)

/--
Definition of `split` / `split` 的定义

English:
definition split
  signature: : ONote -> ONote × Nat
  body: split a
      (oadd e n a', m)

中文:
定义 split
  签名: : ONote -> ONote × 自然数
  定义体: split a
      (oadd e n a', m)
-/
def split : ONote -> ONote × Nat
  | 0 => (0, 0)
  | oadd e n a =>
    if e = 0 then (0, n)
    else
      let (a', m) := split a
      (oadd e n a', m)

/--
Definition of `scale` / `scale` 的定义

English:
definition scale
  signature: (x : ONote)

中文:
定义 scale
  签名: (x : ONote)
-/
def scale (x : ONote) : ONote -> ONote
  | 0 => 0
  | oadd e n a => oadd (x + e) n (scale x a)

/--
Definition of `mulNat` / `mulNat` 的定义

English:
definition mulNat
  signature: : ONote -> Nat -> ONote

中文:
定义 mul自然数
  签名: : ONote -> 自然数 -> ONote
-/
def mulNat : ONote -> Nat -> ONote
  | 0, _ => 0
  | _, 0 => 0
  | oadd e n a, m + 1 => oadd e (n * m.succPNat) a

/--
Definition of `opowAux` / `opowAux` 的定义

English:
definition opowAux
  signature: (e a0 a : ONote)

中文:
定义 opowAux
  签名: (e a0 a : ONote)
-/
def opowAux (e a0 a : ONote) : Nat -> Nat -> ONote
  | _, 0 => 0
  | 0, m + 1 => oadd e m.succPNat 0
  | k + 1, m => scale (e + mulNat a0 k) a + (opowAux e a0 a k m)

/--
Definition of `opowAux2` / `opowAux2` 的定义

English:
definition opowAux2
  signature: (o₂ : ONote) (o₁ : ONote × Nat)
  body: match o₁ with
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

中文:
定义 opowAux2
  签名: (o₂ : ONote) (o₁ : ONote × 自然数)
  定义体: match o₁ with
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

Depends on / 依赖: m.succPNat, mulNat, opowAux, succPNat
-/
def opowAux2 (o₂ : ONote) (o₁ : ONote × Nat) : ONote :=
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

/--
Definition of `opow` / `opow` 的定义

English:
definition opow
  signature: (o₁ o₂ : ONote)
  body: opowAux2 o₂ (split o₁)

中文:
定义 opow
  签名: (o₁ o₂ : ONote)
  定义体: opowAux2 o₂ (split o₁)

Depends on / 依赖: opowAux2
-/
def opow (o₁ o₂ : ONote) : ONote := opowAux2 o₂ (split o₁)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Pow ONote ONote
  body: ⟨opow⟩

中文:
实例 :
  签名: 幂 ONote ONote
  定义体: ⟨opow⟩
-/
instance : Pow ONote ONote :=
  ⟨opow⟩

/--
theorem `opow_def` / 定理 `opow_def`

English:
theorem opow_def
  given: (o₁ o₂ : ONote)
  statement: o₁ ^ o₂ = opowAux2 o₂ (split o₁)
  proof: rfl

中文:
定理 opow_def
  条件: (o₁ o₂ : ONote)
  结论: o₁ ^ o₂ = opowAux2 o₂ (split o₁)
  证明: rfl
-/
theorem opow_def (o₁ o₂ : ONote) : o₁ ^ o₂ = opowAux2 o₂ (split o₁) :=
  rfl

/--
theorem `split_eq_scale_split'` / 定理 `split_eq_scale_split'`

English:
theorem split_eq_scale_split'
  statement: forall {o o' m} [NF o], split' o = (o', m) -> split o = (scale 1 o', m)
  proof: h.fst
      have := h.snd
      simp only [split_eq_scale_split' h', and_imp]
      have : 1 + (e - 1) = e := by
        refine repr_inj.1 ?_
        simp only [repr_add, repr_one, Nat.cast_one, repr_sub]
        have := mt repr_inj.1 e0
exact Ordinal.add_sub_cancel_of_le one_le_iff_ne_zero.2 this
      intros
      subst o' m
      simp [scale, this]

中文:
定理 split_eq_scale_split'
  结论: 对任意 {o o' m} [NF o], split' o = (o', m) -> split o = (scale 1 o', m)
  证明: h.fst
      have := h.snd
      simp only [split_eq_scale_split' h', and_imp]
      have : 1 + (e - 1) = e := by
        refine repr_inj.1 ?_
        simp only [repr_add, repr_one, Nat.cast_one, repr_sub]
        have := mt repr_inj.1 e0
exact Ordinal.add_sub_cancel_of_le one_le_iff_ne_zero.2 this
      intros
      subst o' m
      simp [scale, this]

Depends on / 依赖: h.fst
-/
theorem split_eq_scale_split' : forall {o o' m} [NF o], split' o = (o', m) -> split o = (scale 1 o', m)
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
exact Ordinal.add_sub_cancel_of_le one_le_iff_ne_zero.2 this
      intros
      subst o' m
      simp [scale, this]

/--
theorem `nf_repr_split'` / 定理 `nf_repr_split'`

English:
theorem nf_repr_split'
  statement: forall {o o' m} [NF o], split' o = (o', m) -> NF o' ∧ repr o = ω * repr o' + m
  proof: h.fst
      have := h.snd
      obtain ⟨IH₁, IH₂⟩ := nf_repr_split' h'
      simp only [IH₂, and_imp]
      intros
      subst o' m
      have : (ω : Ordinal.{0}) ^ repr e = ω ^ (1 : Ordinal.{0}) * ω ^ (repr e - 1) := by
        have := mt repr_inj.1 e0
        rw [← opow_add]; rw [Ordinal.add_sub_cancel_of_le (one_le_iff_ne_zero.2 this)]
      refine ⟨NF.oadd (by infer_instance) _ ?_, ?_⟩
      · simp only [opow_one, repr_sub, repr_one, Nat.cast_one] at this ⊢
refine IH₁.below_of_lt' (mul_lt_mul_iff_right₀ omega0_pos).1
          (le_self_add (α := Ordinal) (b := m')).trans_lt ?_
        rw [← this]; rw [← IH₂]
        exact h.snd'.repr_lt
      · rw [this]
        simp [mul_add, mul_assoc, add_assoc]

中文:
定理 nf_repr_split'
  结论: 对任意 {o o' m} [NF o], split' o = (o', m) -> NF o' ∧ repr o = ω * repr o' + m
  证明: h.fst
      have := h.snd
      obtain ⟨IH₁, IH₂⟩ := nf_repr_split' h'
      simp only [IH₂, and_imp]
      intros
      subst o' m
      have : (ω : Ordinal.{0}) ^ repr e = ω ^ (1 : Ordinal.{0}) * ω ^ (repr e - 1) := by
        have := mt repr_inj.1 e0
        rw [← opow_add]; rw [Ordinal.add_sub_cancel_of_le (one_le_iff_ne_zero.2 this)]
      refine ⟨NF.oadd (by infer_instance) _ ?_, ?_⟩
      · simp only [opow_one, repr_sub, repr_one, Nat.cast_one] at this ⊢
refine IH₁.below_of_lt' (mul_lt_mul_iff_right₀ omega0_pos).1
          (le_self_add (α := Ordinal) (b := m')).trans_lt ?_
        rw [← this]; rw [← IH₂]
        exact h.snd'.repr_lt
      · rw [this]
        simp [mul_add, mul_assoc, add_assoc]

Depends on / 依赖: h.fst
-/
theorem nf_repr_split' : forall {o o' m} [NF o], split' o = (o', m) -> NF o' ∧ repr o = ω * repr o' + m
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
        rw [← opow_add]; rw [Ordinal.add_sub_cancel_of_le (one_le_iff_ne_zero.2 this)]
      refine ⟨NF.oadd (by infer_instance) _ ?_, ?_⟩
      · simp only [opow_one, repr_sub, repr_one, Nat.cast_one] at this ⊢
refine IH₁.below_of_lt' (mul_lt_mul_iff_right₀ omega0_pos).1
          (le_self_add (α := Ordinal) (b := m')).trans_lt ?_
        rw [← this]; rw [← IH₂]
        exact h.snd'.repr_lt
      · rw [this]
        simp [mul_add, mul_assoc, add_assoc]

/--
theorem `scale_eq_mul` / 定理 `scale_eq_mul`

English:
theorem scale_eq_mul
  given: (x) [NF x]
  statement: forall (o) [NF o], scale x o = oadd x 1 0 * o
  proof: h.snd
    by_cases e0 : e = 0
    · simp_rw [scale_eq_mul]
      simp [Mul.mul, mul, e0, h.zero_of_zero,
        show x + 0 = x from repr_inj.1 (by simp)]
    · simp [e0, Mul.mul, mul, scale_eq_mul, (· * ·)]

中文:
定理 scale_eq_mul
  条件: (x) [NF x]
  结论: 对任意 (o) [NF o], scale x o = oadd x 1 0 * o
  证明: h.snd
    by_cases e0 : e = 0
    · simp_rw [scale_eq_mul]
      simp [Mul.mul, mul, e0, h.zero_of_zero,
        show x + 0 = x from repr_inj.1 (by simp)]
    · simp [e0, Mul.mul, mul, scale_eq_mul, (· * ·)]

Depends on / 依赖: h.snd
-/
theorem scale_eq_mul (x) [NF x] : forall (o) [NF o], scale x o = oadd x 1 0 * o
  | 0, _ => rfl
  | oadd e n a, h => by
    simp only [HMul.hMul]; simp only [scale]
    have := h.snd
    by_cases e0 : e = 0
    · simp_rw [scale_eq_mul]
      simp [Mul.mul, mul, e0, h.zero_of_zero,
        show x + 0 = x from repr_inj.1 (by simp)]
    · simp [e0, Mul.mul, mul, scale_eq_mul, (· * ·)]

/--
Instance `nf_scale` / 实例 `nf_scale`

English:
instance nf_scale
  signature: (x) [NF x] (o) [NF o]
  body: by
  rw [scale_eq_mul]
  infer_instance

@[simp]

中文:
实例 nf_scale
  签名: (x) [NF x] (o) [NF o]
  定义体: by
  rw [scale_eq_mul]
  infer_instance

@[simp]

Depends on / 依赖: infer_instance, scale_eq_mul
-/
instance nf_scale (x) [NF x] (o) [NF o] : NF (scale x o) := by
  rw [scale_eq_mul]
  infer_instance

@[simp]
/--
theorem `repr_scale` / 定理 `repr_scale`

English:
theorem repr_scale
  given: (x) [NF x] (o) [NF o]
  statement: repr (scale x o) = ω ^ repr x * repr o
  proof: by
  simp only [scale_eq_mul, repr_mul, repr, PNat.one_coe, Nat.cast_one, mul_one, add_zero]

中文:
定理 repr_scale
  条件: (x) [NF x] (o) [NF o]
  结论: repr (scale x o) = ω ^ repr x * repr o
  证明: by
  simp only [scale_eq_mul, repr_mul, repr, PNat.one_coe, Nat.cast_one, mul_one, add_zero]

Depends on / 依赖: Nat.cast_one, PNat.one_coe, add_zero, cast_one, mul_one, one_coe, repr_mul, scale_eq_mul
-/
theorem repr_scale (x) [NF x] (o) [NF o] : repr (scale x o) = ω ^ repr x * repr o := by
  simp only [scale_eq_mul, repr_mul, repr, PNat.one_coe, Nat.cast_one, mul_one, add_zero]

/--
theorem `nf_repr_split` / 定理 `nf_repr_split`

English:
theorem nf_repr_split
  given: {o o' m} [NF o] (h : split o = (o', m))
  statement: NF o' ∧ repr o = repr o' + m
  proof: by
  rcases e : split' o with ⟨a, n⟩
  obtain ⟨s₁, s₂⟩ := nf_repr_split' e
  rw [split_eq_scale_split' e] at h
  injection h; subst o' n
  simp only [repr_scale, repr_one, Nat.cast_one, opow_one, ← s₂, and_true]
  infer_instance

中文:
定理 nf_repr_split
  条件: {o o' m} [NF o] (h : split o = (o', m))
  结论: NF o' ∧ repr o = repr o' + m
  证明: by
  rcases e : split' o with ⟨a, n⟩
  obtain ⟨s₁, s₂⟩ := nf_repr_split' e
  rw [split_eq_scale_split' e] at h
  injection h; subst o' n
  simp only [repr_scale, repr_one, Nat.cast_one, opow_one, ← s₂, and_true]
  infer_instance

Depends on / 依赖: Nat.cast_one, and_true, cast_one, infer_instance, injection, nf_repr_split, opow_one, repr_one, repr_scale, split_eq_scale_split
-/
theorem nf_repr_split {o o' m} [NF o] (h : split o = (o', m)) : NF o' ∧ repr o = repr o' + m := by
  rcases e : split' o with ⟨a, n⟩
  obtain ⟨s₁, s₂⟩ := nf_repr_split' e
  rw [split_eq_scale_split' e] at h
  injection h; subst o' n
  simp only [repr_scale, repr_one, Nat.cast_one, opow_one, ← s₂, and_true]
  infer_instance

/--
theorem `split_dvd` / 定理 `split_dvd`

English:
theorem split_dvd
  given: {o o' m} [NF o] (h : split o = (o', m))
  statement: ω ∣ repr o'
  proof: by
  rcases e : split' o with ⟨a, n⟩
  rw [split_eq_scale_split' e] at h
  injection h; subst o'
  cases nf_repr_split' e; simp

中文:
定理 split_dvd
  条件: {o o' m} [NF o] (h : split o = (o', m))
  结论: ω ∣ repr o'
  证明: by
  rcases e : split' o with ⟨a, n⟩
  rw [split_eq_scale_split' e] at h
  injection h; subst o'
  cases nf_repr_split' e; simp

Depends on / 依赖: injection, nf_repr_split, split_eq_scale_split
-/
theorem split_dvd {o o' m} [NF o] (h : split o = (o', m)) : ω ∣ repr o' := by
  rcases e : split' o with ⟨a, n⟩
  rw [split_eq_scale_split' e] at h
  injection h; subst o'
  cases nf_repr_split' e; simp

/--
theorem `split_add_lt` / 定理 `split_add_lt`

English:
theorem split_add_lt
  given: {o e n a m} [NF o] (h : split o = (oadd e n a, m))
  proof: by
  obtain ⟨h₁, h₂⟩ := nf_repr_split h
  obtain ⟨e0, d⟩ := h₁.of_dvd_omega0 (split_dvd h)
  apply isPrincipal_add_omega0_opow _ h₁.snd'.repr_lt (lt_of_lt_of_le (natCast_lt_omega0 _) _)
  simpa using opow_le_opow_right omega0_pos (one_le_iff_ne_zero.2 e0)

@[simp]

中文:
定理 split_add_lt
  条件: {o e n a m} [NF o] (h : split o = (oadd e n a, m))
  证明: by
  obtain ⟨h₁, h₂⟩ := nf_repr_split h
  obtain ⟨e0, d⟩ := h₁.of_dvd_omega0 (split_dvd h)
  apply isPrincipal_add_omega0_opow _ h₁.snd'.repr_lt (lt_of_lt_of_le (natCast_lt_omega0 _) _)
  simpa using opow_le_opow_right omega0_pos (one_le_iff_ne_zero.2 e0)

@[simp]

Depends on / 依赖: isPrincipal_add_omega0_opow, lt_of_lt_of_le, natCast_lt_omega0, nf_repr_split, of_dvd_omega0, omega0_pos, one_le_iff_ne_zero, opow_le_opow_right, repr_lt, split_dvd
-/
theorem split_add_lt {o e n a m} [NF o] (h : split o = (oadd e n a, m)) :
    repr a + m < ω ^ repr e := by
  obtain ⟨h₁, h₂⟩ := nf_repr_split h
  obtain ⟨e0, d⟩ := h₁.of_dvd_omega0 (split_dvd h)
  apply isPrincipal_add_omega0_opow _ h₁.snd'.repr_lt (lt_of_lt_of_le (natCast_lt_omega0 _) _)
  simpa using opow_le_opow_right omega0_pos (one_le_iff_ne_zero.2 e0)

@[simp]
/--
theorem `mulNat_eq_mul` / 定理 `mulNat_eq_mul`

English:
theorem mulNat_eq_mul
  given: (n o)
  statement: mulNat o n = o * ofNat n
  proof: by cases o <;> cases n <;> rfl

中文:
定理 mul自然数_eq_mul
  条件: (n o)
  结论: mul自然数 o n = o * of自然数 n
  证明: by cases o <;> cases n <;> rfl
-/
theorem mulNat_eq_mul (n o) : mulNat o n = o * ofNat n := by cases o <;> cases n <;> rfl

/--
Instance `nf_mulNat` / 实例 `nf_mulNat`

English:
instance nf_mulNat
  signature: (o) [NF o] (n)
  body: by simpa using ONote.mul_nf o (ofNat n)

中文:
实例 nf_mul自然数
  签名: (o) [NF o] (n)
  定义体: by simpa using ONote.mul_nf o (ofNat n)

Depends on / 依赖: ONote.mul_nf, mul_nf
-/
instance nf_mulNat (o) [NF o] (n) : NF (mulNat o n) := by simpa using ONote.mul_nf o (ofNat n)

/--
Instance `nf_opowAux` / 实例 `nf_opowAux`

English:
instance nf_opowAux
  signature: (e a0 a) [NF e] [NF a0] [NF a]
  body: by
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

中文:
实例 nf_opowAux
  签名: (e a0 a) [NF e] [NF a0] [NF a]
  定义体: by
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

Depends on / 依赖: NF.oadd_zero, NF.zero, infer_instance, mulNat_eq_mul, nf_opowAux, oadd_zero, opowAux
-/
instance nf_opowAux (e a0 a) [NF e] [NF a0] [NF a] : forall k m, NF (opowAux e a0 a k m) := by
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

/--
Instance `nf_opow` / 实例 `nf_opow`

English:
instance nf_opow
  signature: (o₁ o₂) [NF o₁] [NF o₂]
  body: by
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
      · have h' : o₂ != zero := fun he => h (he ▸ zero_def ▸ rfl)
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

中文:
实例 nf_opow
  签名: (o₁ o₂) [NF o₁] [NF o₂]
  定义体: by
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
      · have h' : o₂ != zero := fun he => h (he ▸ zero_def ▸ rfl)
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

Depends on / 依赖: Pow.pow, adaptation_note, branch, leanprover, nf_repr_split, opowAux2, previously, repaired, zero_def
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
      · have h' : o₂ != zero := fun he => h (he ▸ zero_def ▸ rfl)
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

/--
theorem `scale_opowAux` / 定理 `scale_opowAux`

English:
theorem scale_opowAux
  given: (e a0 a : ONote) [NF e] [NF a0] [NF a]

中文:
定理 scale_opowAux
  条件: (e a0 a : ONote) [NF e] [NF a0] [NF a]
-/
theorem scale_opowAux (e a0 a : ONote) [NF e] [NF a0] [NF a] :
    forall k m, repr (opowAux e a0 a k m) = ω ^ repr e * repr (opowAux 0 a0 a k m)
  | 0, m => by cases m <;> simp [opowAux]
  | k + 1, m => by
    by_cases h : m = 0 <;> simp only [h, opowAux, mulNat_eq_mul, repr_add, repr_scale, repr_mul,
      repr_ofNat, zero_add, mul_add, repr_zero, mul_zero, scale_opowAux e, opow_add, mul_assoc]

/--
theorem `repr_opow_aux₁` / 定理 `repr_opow_aux₁`

English:
theorem repr_opow_aux₁
  statement: {e a} [Ne : NF e] [Na : NF a] {a' : Ordinal} (e0 : repr e != 0)
  proof: by
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
  rw [← opow_mul]; rw [← opow_mul]
  rcases le_or_gt ω (repr e) with h | h
  · grw [le_succ b, succ_eq_add_one, add_mul_succ _ (one_add_of_omega0_le h)]
    · gcongr
      · exact omega0_pos
· exact succ_le_iff.2 by gcongr; exact isSuccLimit_omega0.succ_lt l
    · exact omega0_pos
  · grw [show _ * _ < _ from isPrincipal_mul_omega0 (isSuccLimit_omega0.succ_lt h) l]
    · simpa using mul_le_mul_left (one_le_iff_ne_zero.2 e0) ω
    · exact omega0_pos

中文:
定理 repr_opow_aux₁
  结论: {e a} [不等 : NF e] [Na : NF a] {a' : 序数} (e0 : repr e != 0)
  证明: by
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
  rw [← opow_mul]; rw [← opow_mul]
  rcases le_or_gt ω (repr e) with h | h
  · grw [le_succ b, succ_eq_add_one, add_mul_succ _ (one_add_of_omega0_le h)]
    · gcongr
      · exact omega0_pos
· exact succ_le_iff.2 by gcongr; exact isSuccLimit_omega0.succ_lt l
    · exact omega0_pos
  · grw [show _ * _ < _ from isPrincipal_mul_omega0 (isSuccLimit_omega0.succ_lt h) l]
    · simpa using mul_le_mul_left (one_le_iff_ne_zero.2 e0) ω
    · exact omega0_pos

Depends on / 依赖: Na.below_of_lt, Ne.oadd, No.below_of_lt, add_mul_succ, below_of_lt, isSuccLimit_omega0, le_antisymm, le_or_gt, le_succ, lt_succ, omega0_le_oadd, omega0_pos, one_add_of_omeg, opow_le_of_isSuccLimit, opow_le_opow_left, opow_mul, opow_pos, repr_lt, succ_eq_add_one, this.le
-/
theorem repr_opow_aux₁ {e a} [Ne : NF e] [Na : NF a] {a' : Ordinal} (e0 : repr e != 0)
    (h : a' < (ω : Ordinal.{0}) ^ repr e) (aa : repr a = a') (n : Nat+) :
    ((ω : Ordinal.{0}) ^ repr e * (n : Nat) + a') ^ (ω : Ordinal.{0}) =
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
  rw [← opow_mul]; rw [← opow_mul]
  rcases le_or_gt ω (repr e) with h | h
  · grw [le_succ b, succ_eq_add_one, add_mul_succ _ (one_add_of_omega0_le h)]
    · gcongr
      · exact omega0_pos
· exact succ_le_iff.2 by gcongr; exact isSuccLimit_omega0.succ_lt l
    · exact omega0_pos
  · grw [show _ * _ < _ from isPrincipal_mul_omega0 (isSuccLimit_omega0.succ_lt h) l]
    · simpa using mul_le_mul_left (one_le_iff_ne_zero.2 e0) ω
    · exact omega0_pos

section

/--
theorem `repr_opow_aux₂` / 定理 `repr_opow_aux₂`

English:
theorem repr_opow_aux₂
  statement: {a0 a'} [N0 : NF a0] [Na' : NF a'] (m : Nat) (d : ω ∣ repr a')
  proof: repr (opowAux 0 a0 (oadd a0 n a' * ofNat m) k m)
    (k != 0 -> R < ((ω ^ repr a0) ^ succ (k : Ordinal))) ∧
      ((ω ^ repr a0) ^ (k : Ordinal)) * ((ω ^ repr a0) * (n : Nat) + repr a') + R =
        ((ω ^ repr a0) * (n : Nat) + repr a' + m) ^ succ (k : Ordinal) := by
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
  change (k != 0 -> R < (ω0 ^ succ (k : Ordinal))) ∧ (ω0 ^ (k : Ordinal)) * α' + R
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
        rw [Nat.cast_add_one]; rw [RR]; rw [← mul_assoc]; rw [succ_eq_add_one]
    _ = ((ω0 ^ (k : Ordinal)) * α' + R) * α' + ((ω0 ^ (k : Ordinal)) * α' + R) * m := ?_
    _ = (α' + m) ^ succ (k.succ : Ordinal) := by
        rw [← mul_add]; rw [opow_succ]; rw [Nat.cast_add_one]; rw [IH.2]; rw [succ_eq_add_one]
  congr 1
  · have αd : ω ∣ α' :=
      dvd_add (dvd_mul_of_dvd_left (by simpa using opow_dvd_opow ω (one_le_iff_ne_zero.2 e0)) _) d
    have α0 : ¬IsMin α' := by
      rw [isMin_iff_eq_bot]
      exact α0.ne'
    rw [mul_add (ω0 ^ (k : Ordinal))]; rw [add_assoc]; rw [← mul_assoc]; rw [← opow_succ]; rw [add_mul_of_isSuccLimit _ ⟨α0]; rw [isSuccPrelimit_iff_omega0_dvd.2 αd⟩]; rw [mul_assoc]; rw [@mul_omega0_dvd n (Nat.cast_pos'.2 n.pos) (natCast_lt_omega0 _) _ αd]
    apply @add_of_omega0_opow_le _ (repr a0 * succ ↑k)
    · refine isPrincipal_add_omega0_opow _ ?_ Rl
      rw [opow_mul]; rw [opow_succ]
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
      rw [opow_mul]; rw [opow_succ]
      gcongr
      simpa [repr] using omega0_le_oadd a0 n a'

中文:
定理 repr_opow_aux₂
  结论: {a0 a'} [N0 : NF a0] [Na' : NF a'] (m : 自然数) (d : ω ∣ repr a')
  证明: repr (opowAux 0 a0 (oadd a0 n a' * ofNat m) k m)
    (k != 0 -> R < ((ω ^ repr a0) ^ succ (k : Ordinal))) ∧
      ((ω ^ repr a0) ^ (k : Ordinal)) * ((ω ^ repr a0) * (n : Nat) + repr a') + R =
        ((ω ^ repr a0) * (n : Nat) + repr a' + m) ^ succ (k : Ordinal) := by
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
  change (k != 0 -> R < (ω0 ^ succ (k : Ordinal))) ∧ (ω0 ^ (k : Ordinal)) * α' + R
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
        rw [Nat.cast_add_one]; rw [RR]; rw [← mul_assoc]; rw [succ_eq_add_one]
    _ = ((ω0 ^ (k : Ordinal)) * α' + R) * α' + ((ω0 ^ (k : Ordinal)) * α' + R) * m := ?_
    _ = (α' + m) ^ succ (k.succ : Ordinal) := by
        rw [← mul_add]; rw [opow_succ]; rw [Nat.cast_add_one]; rw [IH.2]; rw [succ_eq_add_one]
  congr 1
  · have αd : ω ∣ α' :=
      dvd_add (dvd_mul_of_dvd_left (by simpa using opow_dvd_opow ω (one_le_iff_ne_zero.2 e0)) _) d
    have α0 : ¬IsMin α' := by
      rw [isMin_iff_eq_bot]
      exact α0.ne'
    rw [mul_add (ω0 ^ (k : Ordinal))]; rw [add_assoc]; rw [← mul_assoc]; rw [← opow_succ]; rw [add_mul_of_isSuccLimit _ ⟨α0]; rw [isSuccPrelimit_iff_omega0_dvd.2 αd⟩]; rw [mul_assoc]; rw [@mul_omega0_dvd n (Nat.cast_pos'.2 n.pos) (natCast_lt_omega0 _) _ αd]
    apply @add_of_omega0_opow_le _ (repr a0 * succ ↑k)
    · refine isPrincipal_add_omega0_opow _ ?_ Rl
      rw [opow_mul]; rw [opow_succ]
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
      rw [opow_mul]; rw [opow_succ]
      gcongr
      simpa [repr] using omega0_le_oadd a0 n a'

Depends on / 依赖: opowAux
-/
theorem repr_opow_aux₂ {a0 a'} [N0 : NF a0] [Na' : NF a'] (m : Nat) (d : ω ∣ repr a')
    (e0 : repr a0 != 0) (h : repr a' + m < (ω ^ repr a0)) (n : Nat+) (k : Nat) :
    let R := repr (opowAux 0 a0 (oadd a0 n a' * ofNat m) k m)
    (k != 0 -> R < ((ω ^ repr a0) ^ succ (k : Ordinal))) ∧
      ((ω ^ repr a0) ^ (k : Ordinal)) * ((ω ^ repr a0) * (n : Nat) + repr a') + R =
        ((ω ^ repr a0) * (n : Nat) + repr a' + m) ^ succ (k : Ordinal) := by
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
  change (k != 0 -> R < (ω0 ^ succ (k : Ordinal))) ∧ (ω0 ^ (k : Ordinal)) * α' + R
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
        rw [Nat.cast_add_one]; rw [RR]; rw [← mul_assoc]; rw [succ_eq_add_one]
    _ = ((ω0 ^ (k : Ordinal)) * α' + R) * α' + ((ω0 ^ (k : Ordinal)) * α' + R) * m := ?_
    _ = (α' + m) ^ succ (k.succ : Ordinal) := by
        rw [← mul_add]; rw [opow_succ]; rw [Nat.cast_add_one]; rw [IH.2]; rw [succ_eq_add_one]
  congr 1
  · have αd : ω ∣ α' :=
      dvd_add (dvd_mul_of_dvd_left (by simpa using opow_dvd_opow ω (one_le_iff_ne_zero.2 e0)) _) d
    have α0 : ¬IsMin α' := by
      rw [isMin_iff_eq_bot]
      exact α0.ne'
    rw [mul_add (ω0 ^ (k : Ordinal))]; rw [add_assoc]; rw [← mul_assoc]; rw [← opow_succ]; rw [add_mul_of_isSuccLimit _ ⟨α0]; rw [isSuccPrelimit_iff_omega0_dvd.2 αd⟩]; rw [mul_assoc]; rw [@mul_omega0_dvd n (Nat.cast_pos'.2 n.pos) (natCast_lt_omega0 _) _ αd]
    apply @add_of_omega0_opow_le _ (repr a0 * succ ↑k)
    · refine isPrincipal_add_omega0_opow _ ?_ Rl
      rw [opow_mul]; rw [opow_succ]
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
      rw [opow_mul]; rw [opow_succ]
      gcongr
      simpa [repr] using omega0_le_oadd a0 n a'

end

set_option linter.flexible false in -- simp used on two different goals
/--
theorem `repr_opow` / 定理 `repr_opow`

English:
theorem repr_opow
  given: (o₁ o₂) [NF o₁] [NF o₂]
  statement: repr (o₁ ^ o₂) = repr o₁ ^ repr o₂
  proof: by
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
        have hne : o₂ != zero := fun he => h (he ▸ rfl)
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
      rw [opow_add]; rw [opow_mul]; rw [opow_omega0]
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
      rw [repr_opow_aux₁ a00 al aa]; rw [scale_opowAux]
      simp only [repr_mul, repr_scale, repr_one,
        Nat.cast_one, opow_one, opow_mul]
      rw [← mul_add]; rw [← add_assoc ((ω : Ordinal.{0}) ^ repr a0 * (n : Nat))]
      congr 1
      rw [← pow_succ]; rw [← opow_natCast]; rw [← opow_natCast]
      exact (repr_opow_aux₂ _ ad a00 al _ _).2

中文:
定理 repr_opow
  条件: (o₁ o₂) [NF o₁] [NF o₂]
  结论: repr (o₁ ^ o₂) = repr o₁ ^ repr o₂
  证明: by
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
        have hne : o₂ != zero := fun he => h (he ▸ rfl)
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
      rw [opow_add]; rw [opow_mul]; rw [opow_omega0]
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
      rw [repr_opow_aux₁ a00 al aa]; rw [scale_opowAux]
      simp only [repr_mul, repr_scale, repr_one,
        Nat.cast_one, opow_one, opow_mul]
      rw [← mul_add]; rw [← add_assoc ((ω : Ordinal.{0}) ^ repr a0 * (n : Nat))]
      congr 1
      rw [← pow_succ]; rw [← opow_natCast]; rw [← opow_natCast]
      exact (repr_opow_aux₂ _ ad a00 al _ _).2

Depends on / 依赖: adaptation_note, eqComm, leanprover, nf_repr_split, opowAux2, opow_def, previously, repaired, repr_inj
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
        have hne : o₂ != zero := fun he => h (he ▸ rfl)
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
      rw [opow_add]; rw [opow_mul]; rw [opow_omega0]
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
      rw [repr_opow_aux₁ a00 al aa]; rw [scale_opowAux]
      simp only [repr_mul, repr_scale, repr_one,
        Nat.cast_one, opow_one, opow_mul]
      rw [← mul_add]; rw [← add_assoc ((ω : Ordinal.{0}) ^ repr a0 * (n : Nat))]
      congr 1
      rw [← pow_succ]; rw [← opow_natCast]; rw [← opow_natCast]
      exact (repr_opow_aux₂ _ ad a00 al _ _).2

/--
Definition of `fundamentalSequence` / `fundamentalSequence` 的定义

English:
definition fundamentalSequence
  signature: : ONote -> (Option ONote) oplus (Nat -> ONote)

中文:
定义 fundamentalSequence
  签名: : ONote -> (选项类型 ONote) oplus (自然数 -> ONote)

Depends on / 依赖: Ordinal, Ordinal.add_sub_cancel_of_le, add_lt_add_iff_left, add_sub_cancel_of_le, h.trans_le, le_self_add, lt_or_ge, trans_le
-/
def fundamentalSequence : ONote -> (Option ONote) oplus (Nat -> ONote)
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

/--
theorem `exists_lt_add` / 定理 `exists_lt_add`

English:
theorem exists_lt_add
  statement: {α} [hα : Nonempty α] {o : Ordinal} {f : α -> Ordinal}
  proof: by
  rcases lt_or_ge a b with h | h'
  · obtain ⟨i⟩ := id hα
    exact ⟨i, h.trans_le le_self_add⟩
  · rw [← Ordinal.add_sub_cancel_of_le h', add_lt_add_iff_left] at h
    refine (H h).imp fun i H => ?_
    rwa [← Ordinal.add_sub_cancel_of_le h', add_lt_add_iff_left]

中文:
定理 存在_lt_add
  结论: {α} [hα : 非空 α] {o : 序数} {f : α -> 序数}
  证明: by
  rcases lt_or_ge a b with h | h'
  · obtain ⟨i⟩ := id hα
    exact ⟨i, h.trans_le le_self_add⟩
  · rw [← Ordinal.add_sub_cancel_of_le h', add_lt_add_iff_left] at h
    refine (H h).imp fun i H => ?_
    rwa [← Ordinal.add_sub_cancel_of_le h', add_lt_add_iff_left]
-/
private theorem exists_lt_add {α} [hα : Nonempty α] {o : Ordinal} {f : α -> Ordinal}
    (H : forall ⦃a⦄, a < o -> exists i, a < f i) {b : Ordinal} ⦃a⦄ (h : a < b + o) : exists i, a < b + f i := by
  rcases lt_or_ge a b with h | h'
  · obtain ⟨i⟩ := id hα
    exact ⟨i, h.trans_le le_self_add⟩
  · rw [← Ordinal.add_sub_cancel_of_le h', add_lt_add_iff_left] at h
    refine (H h).imp fun i H => ?_
    rwa [← Ordinal.add_sub_cancel_of_le h', add_lt_add_iff_left]

/--
theorem `exists_lt_mul_omega0'` / 定理 `exists_lt_mul_omega0'`

English:
theorem exists_lt_mul_omega0'
  given: {o : Ordinal} ⦃a⦄ (h : a < o * ω)
  proof: by
  obtain ⟨i, hi, h'⟩ := (lt_mul_iff_of_isSuccLimit isSuccLimit_omega0).1 h
  obtain ⟨i, rfl⟩ := lt_omega0.1 hi
  exact ⟨i, h'.trans_le le_self_add⟩

中文:
定理 存在_lt_mul_omega0'
  条件: {o : 序数} ⦃a⦄ (h : a < o * ω)
  证明: by
  obtain ⟨i, hi, h'⟩ := (lt_mul_iff_of_isSuccLimit isSuccLimit_omega0).1 h
  obtain ⟨i, rfl⟩ := lt_omega0.1 hi
  exact ⟨i, h'.trans_le le_self_add⟩
-/
private theorem exists_lt_mul_omega0' {o : Ordinal} ⦃a⦄ (h : a < o * ω) :
    exists i : Nat, a < o * ↑i + o := by
  obtain ⟨i, hi, h'⟩ := (lt_mul_iff_of_isSuccLimit isSuccLimit_omega0).1 h
  obtain ⟨i, rfl⟩ := lt_omega0.1 hi
  exact ⟨i, h'.trans_le le_self_add⟩

/--
theorem `exists_lt_omega0_opow'` / 定理 `exists_lt_omega0_opow'`

English:
theorem exists_lt_omega0_opow'
  statement: {α} {o b : Ordinal} (hb : 1 < b) (ho : IsSuccLimit o)
  proof: by
  obtain ⟨d, hd, h'⟩ := (lt_opow_of_isSuccLimit (zero_lt_one.trans hb).ne' ho).1 h
exact (H hd).imp fun i hi => h'.trans (opow_lt_opow_iff_right hb).2 hi

中文:
定理 存在_lt_omega0_opow'
  结论: {α} {o b : 序数} (hb : 1 < b) (ho : 是SuccLimit o)
  证明: by
  obtain ⟨d, hd, h'⟩ := (lt_opow_of_isSuccLimit (zero_lt_one.trans hb).ne' ho).1 h
exact (H hd).imp fun i hi => h'.trans (opow_lt_opow_iff_right hb).2 hi
-/
private theorem exists_lt_omega0_opow' {α} {o b : Ordinal} (hb : 1 < b) (ho : IsSuccLimit o)
    {f : α -> Ordinal} (H : forall ⦃a⦄, a < o -> exists i, a < f i) ⦃a⦄ (h : a < b ^ o) :
        exists i, a < b ^ f i := by
  obtain ⟨d, hd, h'⟩ := (lt_opow_of_isSuccLimit (zero_lt_one.trans hb).ne' ho).1 h
exact (H hd).imp fun i hi => h'.trans (opow_lt_opow_iff_right hb).2 hi

/--
Definition of `FundamentalSequenceProp` / `FundamentalSequenceProp` 的定义

English:
definition FundamentalSequenceProp
  signature: (o : ONote)

中文:
定义 FundamentalSequenceProp
  签名: (o : ONote)
-/
def FundamentalSequenceProp (o : ONote) : (Option ONote) oplus (Nat -> ONote) -> Prop
  | Sum.inl none => o = 0
  | Sum.inl (some a) => o.repr = succ a.repr ∧ (o.NF -> a.NF)
  | Sum.inr f =>
    IsSuccLimit o.repr ∧
      (forall i, f i < f (i + 1) ∧ f i < o ∧ (o.NF -> (f i).NF)) ∧ forall a, a < o.repr -> exists i, a < (f i).repr

/--
theorem `fundamentalSequenceProp_inl_none` / 定理 `fundamentalSequenceProp_inl_none`

English:
theorem fundamentalSequenceProp_inl_none
  given: (o)
  proof: Iff.rfl

中文:
定理 fundamentalSequenceProp_inl_none
  条件: (o)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem fundamentalSequenceProp_inl_none (o) :
    FundamentalSequenceProp o (Sum.inl none) ↔ o = 0 :=
  Iff.rfl

/--
theorem `fundamentalSequenceProp_inl_some` / 定理 `fundamentalSequenceProp_inl_some`

English:
theorem fundamentalSequenceProp_inl_some
  given: (o a)
  proof: Iff.rfl

中文:
定理 fundamentalSequenceProp_inl_some
  条件: (o a)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem fundamentalSequenceProp_inl_some (o a) :
    FundamentalSequenceProp o (Sum.inl (some a)) ↔ o.repr = succ a.repr ∧ (o.NF -> a.NF) :=
  Iff.rfl

/--
theorem `fundamentalSequenceProp_inr` / 定理 `fundamentalSequenceProp_inr`

English:
theorem fundamentalSequenceProp_inr
  given: (o f)
  proof: Iff.rfl

中文:
定理 fundamentalSequenceProp_inr
  条件: (o f)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem fundamentalSequenceProp_inr (o f) :
    FundamentalSequenceProp o (Sum.inr f) ↔
      IsSuccLimit o.repr ∧
        (forall i, f i < f (i + 1) ∧ f i < o ∧ (o.NF -> (f i).NF)) ∧
        forall a, a < o.repr -> exists i, a < (f i).repr :=
  Iff.rfl

/--
theorem `fundamentalSequence_has_prop` / 定理 `fundamentalSequence_has_prop`

English:
theorem fundamentalSequence_has_prop
  given: (o)
  statement: FundamentalSequenceProp o (fundamentalSequence o)
  proof: by
  induction o with
  | zero => exact rfl
  | oadd a m b iha ihb
  rw [fundamentalSequence]
  rcases e : b.fundamentalSequence with (⟨_ | b'⟩ | f) <;>
    simp only [FundamentalSequenceProp] <;>
    rw [e]; rw [FundamentalSequenceProp] at ihb
  · rcases e : a.fundamentalSequence with (⟨_ | a'⟩ | f) <;> rcases e' : m.natPred with - | m' <;>
      simp only <;>
      rw [e]; rw [FundamentalSequenceProp] at iha <;>
      (try rw [show m = 1 by
            have := PNat.natPred_add_one m; rw [e'] at this; exact PNat.coe_inj.1 this.symm]) <;>
      (try rw [show m = (m' + 1).succPNat by
              rw [← e']; rw [← PNat.coe_inj]; rw [Nat.succPNat_coe]; rw [← Nat.add_one]; rw [PNat.natPred_add_one]]) <;>
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
      rw [← mul_add_one]; rw [← Nat.cast_add_one]
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
        rw [repr]; rw [repr_zero]; rw [add_zero]; rw [iha.1]; rw [opow_succ]
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
  · refine ⟨?_, fun H => H.fst.oadd _ (NF.below_of_lt' ?_ (ihb.2 H.snd))⟩
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

中文:
定理 fundamentalSequence_has_prop
  条件: (o)
  结论: FundamentalSequenceProp o (fundamentalSequence o)
  证明: by
  induction o with
  | zero => exact rfl
  | oadd a m b iha ihb
  rw [fundamentalSequence]
  rcases e : b.fundamentalSequence with (⟨_ | b'⟩ | f) <;>
    simp only [FundamentalSequenceProp] <;>
    rw [e]; rw [FundamentalSequenceProp] at ihb
  · rcases e : a.fundamentalSequence with (⟨_ | a'⟩ | f) <;> rcases e' : m.natPred with - | m' <;>
      simp only <;>
      rw [e]; rw [FundamentalSequenceProp] at iha <;>
      (try rw [show m = 1 by
            have := PNat.natPred_add_one m; rw [e'] at this; exact PNat.coe_inj.1 this.symm]) <;>
      (try rw [show m = (m' + 1).succPNat by
              rw [← e']; rw [← PNat.coe_inj]; rw [Nat.succPNat_coe]; rw [← Nat.add_one]; rw [PNat.natPred_add_one]]) <;>
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
      rw [← mul_add_one]; rw [← Nat.cast_add_one]
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
        rw [repr]; rw [repr_zero]; rw [add_zero]; rw [iha.1]; rw [opow_succ]
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
  · refine ⟨?_, fun H => H.fst.oadd _ (NF.below_of_lt' ?_ (ihb.2 H.snd))⟩
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

Depends on / 依赖: FundamentalSequenceProp, PNat.coe_inj, PNat.natPred_add_one, a.fundamentalSequence, b.fundamentalSequence, coe_inj, fundamentalSequence, m.natPred, natPred, natPred_add_one, this.symm
-/
theorem fundamentalSequence_has_prop (o) : FundamentalSequenceProp o (fundamentalSequence o) := by
  induction o with
  | zero => exact rfl
  | oadd a m b iha ihb
  rw [fundamentalSequence]
  rcases e : b.fundamentalSequence with (⟨_ | b'⟩ | f) <;>
    simp only [FundamentalSequenceProp] <;>
    rw [e]; rw [FundamentalSequenceProp] at ihb
  · rcases e : a.fundamentalSequence with (⟨_ | a'⟩ | f) <;> rcases e' : m.natPred with - | m' <;>
      simp only <;>
      rw [e]; rw [FundamentalSequenceProp] at iha <;>
      (try rw [show m = 1 by
            have := PNat.natPred_add_one m; rw [e'] at this; exact PNat.coe_inj.1 this.symm]) <;>
      (try rw [show m = (m' + 1).succPNat by
              rw [← e']; rw [← PNat.coe_inj]; rw [Nat.succPNat_coe]; rw [← Nat.add_one]; rw [PNat.natPred_add_one]]) <;>
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
      rw [← mul_add_one]; rw [← Nat.cast_add_one]
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
        rw [repr]; rw [repr_zero]; rw [add_zero]; rw [iha.1]; rw [opow_succ]
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
  · refine ⟨?_, fun H => H.fst.oadd _ (NF.below_of_lt' ?_ (ihb.2 H.snd))⟩
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

/--
Definition of `fastGrowing` / `fastGrowing` 的定义

English:
definition fastGrowing
  signature: : ONote -> Nat -> Nat
  body: by rw [lt_def, h.1]; apply lt_succ
      fun i => (fastGrowing a)^[i] i
    | Sum.inr f, h => fun i =>
      have : f i < o := (h.2.1 i).2.1
      fastGrowing (f i) i
  termination_by o => o

中文:
定义 fastGrowing
  签名: : ONote -> 自然数 -> 自然数
  定义体: by rw [lt_def, h.1]; apply lt_succ
      fun i => (fastGrowing a)^[i] i
    | Sum.inr f, h => fun i =>
      have : f i < o := (h.2.1 i).2.1
      fastGrowing (f i) i
  termination_by o => o

Depends on / 依赖: Sum.inr, fastGrowing, lt_def, lt_succ, termination_by
-/
def fastGrowing : ONote -> Nat -> Nat
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

/--
theorem `fastGrowing_def` / 定理 `fastGrowing_def`

English:
theorem fastGrowing_def
  given: {o : ONote} {x} (e : fundamentalSequence o = x)
  proof: by
  subst x
  rw [fastGrowing]

中文:
定理 fastGrowing_def
  条件: {o : ONote} {x} (e : fundamentalSequence o = x)
  证明: by
  subst x
  rw [fastGrowing]

Depends on / 依赖: FundamentalSequenceProp
-/
theorem fastGrowing_def {o : ONote} {x} (e : fundamentalSequence o = x) :
    fastGrowing o =
      match
        (motive := (x : Option ONote oplus (Nat -> ONote)) -> FundamentalSequenceProp o x -> Nat -> Nat)
        x, e ▸ fundamentalSequence_has_prop o with
      | Sum.inl none, _ => Nat.succ
      | Sum.inl (some a), _ =>
        fun i => (fastGrowing a)^[i] i
      | Sum.inr f, _ => fun i =>
        fastGrowing (f i) i := by
  subst x
  rw [fastGrowing]

/--
theorem `fastGrowing_zero'` / 定理 `fastGrowing_zero'`

English:
theorem fastGrowing_zero'
  given: (o : ONote) (h : fundamentalSequence o = Sum.inl none)
  proof: by
  rw [fastGrowing_def h]

中文:
定理 fastGrowing_zero'
  条件: (o : ONote) (h : fundamentalSequence o = 和.inl none)
  证明: by
  rw [fastGrowing_def h]

Depends on / 依赖: fastGrowing_def
-/
theorem fastGrowing_zero' (o : ONote) (h : fundamentalSequence o = Sum.inl none) :
    fastGrowing o = Nat.succ := by
  rw [fastGrowing_def h]

/--
theorem `fastGrowing_succ` / 定理 `fastGrowing_succ`

English:
theorem fastGrowing_succ
  given: (o) {a} (h : fundamentalSequence o = Sum.inl (some a))
  proof: by
  rw [fastGrowing_def h]

中文:
定理 fastGrowing_succ
  条件: (o) {a} (h : fundamentalSequence o = 和.inl (some a))
  证明: by
  rw [fastGrowing_def h]

Depends on / 依赖: fastGrowing_def
-/
theorem fastGrowing_succ (o) {a} (h : fundamentalSequence o = Sum.inl (some a)) :
    fastGrowing o = fun i => (fastGrowing a)^[i] i := by
  rw [fastGrowing_def h]

/--
theorem `fastGrowing_limit` / 定理 `fastGrowing_limit`

English:
theorem fastGrowing_limit
  given: (o) {f} (h : fundamentalSequence o = Sum.inr f)
  proof: by
  rw [fastGrowing_def h]

@[simp]

中文:
定理 fastGrowing_limit
  条件: (o) {f} (h : fundamentalSequence o = 和.inr f)
  证明: by
  rw [fastGrowing_def h]

@[simp]

Depends on / 依赖: fastGrowing_def
-/
theorem fastGrowing_limit (o) {f} (h : fundamentalSequence o = Sum.inr f) :
    fastGrowing o = fun i => fastGrowing (f i) i := by
  rw [fastGrowing_def h]

@[simp]
/--
theorem `fastGrowing_zero` / 定理 `fastGrowing_zero`

English:
theorem fastGrowing_zero
  statement: fastGrowing 0 = Nat.succ
  proof: fastGrowing_zero' _ rfl

@[simp]

中文:
定理 fastGrowing_zero
  结论: fastGrowing 0 = 自然数.succ
  证明: fastGrowing_zero' _ rfl

@[simp]

Depends on / 依赖: fastGrowing_zero
-/
theorem fastGrowing_zero : fastGrowing 0 = Nat.succ :=
  fastGrowing_zero' _ rfl

@[simp]
/--
theorem `fastGrowing_one` / 定理 `fastGrowing_one`

English:
theorem fastGrowing_one
  statement: fastGrowing 1 = fun n => 2 * n
  proof: by
  rw [@fastGrowing_succ 1 0 rfl]; funext i; rw [two_mul, fastGrowing_zero]
  exact Nat.succ_iterate _ _

@[simp]

中文:
定理 fastGrowing_one
  结论: fastGrowing 1 = fun n => 2 * n
  证明: by
  rw [@fastGrowing_succ 1 0 rfl]; funext i; rw [two_mul, fastGrowing_zero]
  exact Nat.succ_iterate _ _

@[simp]

Depends on / 依赖: Nat.succ_iterate, fastGrowing_succ, fastGrowing_zero, succ_iterate, two_mul
-/
theorem fastGrowing_one : fastGrowing 1 = fun n => 2 * n := by
  rw [@fastGrowing_succ 1 0 rfl]; funext i; rw [two_mul, fastGrowing_zero]
  exact Nat.succ_iterate _ _

@[simp]
/--
theorem `fastGrowing_two` / 定理 `fastGrowing_two`

English:
theorem fastGrowing_two
  statement: fastGrowing 2 = fun n => (2 ^ n) * n
  proof: by
  rw [@fastGrowing_succ 2 1 rfl]
  simp

中文:
定理 fastGrowing_two
  结论: fastGrowing 2 = fun n => (2 ^ n) * n
  证明: by
  rw [@fastGrowing_succ 2 1 rfl]
  simp

Depends on / 依赖: fastGrowing_succ
-/
theorem fastGrowing_two : fastGrowing 2 = fun n => (2 ^ n) * n := by
  rw [@fastGrowing_succ 2 1 rfl]
  simp

/--
Definition of `fastGrowingε₀` / `fastGrowingε₀` 的定义

English:
definition fastGrowingε₀
  signature: (i : Nat)
  body: fastGrowing ((fun a => a.oadd 1 0)^[i] 0) i

中文:
定义 fastGrowingε₀
  签名: (i : 自然数)
  定义体: fastGrowing ((fun a => a.oadd 1 0)^[i] 0) i

Depends on / 依赖: a.oadd, fastGrowing
-/
def fastGrowingε₀ (i : Nat) : Nat :=
  fastGrowing ((fun a => a.oadd 1 0)^[i] 0) i

/--
theorem `fastGrowingε₀_zero` / 定理 `fastGrowingε₀_zero`

English:
theorem fastGrowingε₀_zero
  statement: fastGrowingε₀ 0 = 1
  proof: by simp [fastGrowingε₀]

中文:
定理 fastGrowingε₀_zero
  结论: fastGrowingε₀ 0 = 1
  证明: by simp [fastGrowingε₀]
-/
theorem fastGrowingε₀_zero : fastGrowingε₀ 0 = 1 := by simp [fastGrowingε₀]

/--
theorem `fastGrowingε₀_one` / 定理 `fastGrowingε₀_one`

English:
theorem fastGrowingε₀_one
  statement: fastGrowingε₀ 1 = 2
  proof: by
  simp [fastGrowingε₀, show oadd 0 1 0 = 1 from rfl]

中文:
定理 fastGrowingε₀_one
  结论: fastGrowingε₀ 1 = 2
  证明: by
  simp [fastGrowingε₀, show oadd 0 1 0 = 1 from rfl]
-/
theorem fastGrowingε₀_one : fastGrowingε₀ 1 = 2 := by
  simp [fastGrowingε₀, show oadd 0 1 0 = 1 from rfl]

/--
theorem `fastGrowingε₀_two` / 定理 `fastGrowingε₀_two`

English:
theorem fastGrowingε₀_two
  statement: fastGrowingε₀ 2 = 2048
  proof: by
  norm_num [fastGrowingε₀, show oadd 0 1 0 = 1 from rfl, @fastGrowing_limit (oadd 1 1 0) _ rfl,
    show oadd 0 (2 : Nat).succPNat 0 = 3 from rfl, @fastGrowing_succ 3 2 rfl]

中文:
定理 fastGrowingε₀_two
  结论: fastGrowingε₀ 2 = 2048
  证明: by
  norm_num [fastGrowingε₀, show oadd 0 1 0 = 1 from rfl, @fastGrowing_limit (oadd 1 1 0) _ rfl,
    show oadd 0 (2 : Nat).succPNat 0 = 3 from rfl, @fastGrowing_succ 3 2 rfl]

Depends on / 依赖: fastGrowing_limit, fastGrowing_succ, succPNat
-/
theorem fastGrowingε₀_two : fastGrowingε₀ 2 = 2048 := by
  norm_num [fastGrowingε₀, show oadd 0 1 0 = 1 from rfl, @fastGrowing_limit (oadd 1 1 0) _ rfl,
    show oadd 0 (2 : Nat).succPNat 0 = 3 from rfl, @fastGrowing_succ 3 2 rfl]

end ONote

/--
Definition of `NONote` / `NONote` 的定义

English:
definition NONote
  body: { o : ONote // o.NF }
deriving DecidableEq

中文:
定义 NONote
  定义体: { o : ONote // o.NF }
deriving DecidableEq

Depends on / 依赖: o.NF
-/
def NONote :=
  { o : ONote // o.NF }
deriving DecidableEq

namespace NONote

open ONote

/--
Instance `NF` / 实例 `NF`

English:
instance NF
  signature: (o : NONote)
  body: o.2

中文:
实例 NF
  签名: (o : NONote)
  定义体: o.2
-/
instance NF (o : NONote) : NF o.1 :=
  o.2

/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: (o : ONote) [h : ONote.NF o]
  body: ⟨o, h⟩

中文:
定义 mk
  签名: (o : ONote) [h : ONote.NF o]
  定义体: ⟨o, h⟩
-/
def mk (o : ONote) [h : ONote.NF o] : NONote :=
  ⟨o, h⟩

/--
Definition of `repr` / `repr` 的定义

English:
definition repr
  signature: (o : NONote)
  body: o.1.repr

中文:
定义 repr
  签名: (o : NONote)
  定义体: o.1.repr
-/
noncomputable def repr (o : NONote) : Ordinal :=
  o.1.repr

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ToString NONote
  body: ⟨fun x => x.1.toString⟩

中文:
实例 :
  签名: ToString NONote
  定义体: ⟨fun x => x.1.toString⟩

Depends on / 依赖: toString
-/
instance : ToString NONote :=
  ⟨fun x => x.1.toString⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Repr NONote
  body: ⟨fun x prec => x.1.repr' prec⟩

中文:
实例 :
  签名: Repr NONote
  定义体: ⟨fun x prec => x.1.repr' prec⟩
-/
instance : Repr NONote :=
  ⟨fun x prec => x.1.repr' prec⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Preorder NONote
  body: repr x <= repr y
  lt x y := repr x < repr y
  le_refl _ := @le_refl Ordinal _ _
  le_trans _ _ _ := @le_trans Ordinal _ _ _ _
  lt_iff_le_not_ge _ _ := @lt_iff_le_not_ge Ordinal _ _ _

中文:
实例 :
  签名: 预序 NONote
  定义体: repr x <= repr y
  lt x y := repr x < repr y
  le_refl _ := @le_refl Ordinal _ _
  le_trans _ _ _ := @le_trans Ordinal _ _ _ _
  lt_iff_le_not_ge _ _ := @lt_iff_le_not_ge Ordinal _ _ _
-/
instance : Preorder NONote where
  le x y := repr x <= repr y
  lt x y := repr x < repr y
  le_refl _ := @le_refl Ordinal _ _
  le_trans _ _ _ := @le_trans Ordinal _ _ _ _
  lt_iff_le_not_ge _ _ := @lt_iff_le_not_ge Ordinal _ _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero NONote
  body: ⟨⟨0, NF.zero⟩⟩

中文:
实例 :
  签名: 零 NONote
  定义体: ⟨⟨0, NF.zero⟩⟩

Depends on / 依赖: NF.zero
-/
instance : Zero NONote :=
  ⟨⟨0, NF.zero⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited NONote
  body: ⟨0⟩

中文:
实例 :
  签名: 可居 NONote
  定义体: ⟨0⟩
-/
instance : Inhabited NONote :=
  ⟨0⟩

/--
theorem `lt_wf` / 定理 `lt_wf`

English:
theorem lt_wf
  statement: @WellFounded NONote (· < ·)
  proof: InvImage.wf repr Ordinal.lt_wf

中文:
定理 lt_wf
  结论: @良基 NONote (· < ·)
  证明: InvImage.wf repr Ordinal.lt_wf

Depends on / 依赖: InvImage, InvImage.wf, Ordinal, Ordinal.lt_wf, lt_wf
-/
theorem lt_wf : @WellFounded NONote (· < ·) :=
  InvImage.wf repr Ordinal.lt_wf

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: WellFoundedLT NONote
  body: ⟨lt_wf⟩

中文:
实例 :
  签名: WellFoundedLT NONote
  定义体: ⟨lt_wf⟩

Depends on / 依赖: lt_wf
-/
instance : WellFoundedLT NONote :=
  ⟨lt_wf⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: WellFoundedRelation NONote
  body: ⟨(· < ·), lt_wf⟩

中文:
实例 :
  签名: 良基关系 NONote
  定义体: ⟨(· < ·), lt_wf⟩

Depends on / 依赖: lt_wf
-/
instance : WellFoundedRelation NONote :=
  ⟨(· < ·), lt_wf⟩

/--
Definition of `ofNat` / `ofNat` 的定义

English:
definition ofNat
  signature: (n : Nat)
  body: ⟨ONote.ofNat n, ⟨⟨_, nfBelow_ofNat _⟩⟩⟩

中文:
定义 of自然数
  签名: (n : 自然数)
  定义体: ⟨ONote.ofNat n, ⟨⟨_, nfBelow_ofNat _⟩⟩⟩

Depends on / 依赖: ONote.ofNat, nfBelow_ofNat
-/
def ofNat (n : Nat) : NONote :=
  ⟨ONote.ofNat n, ⟨⟨_, nfBelow_ofNat _⟩⟩⟩

/--
Definition of `cmp` / `cmp` 的定义

English:
definition cmp
  signature: (a b : NONote)
  body: ONote.cmp a.1 b.1

中文:
定义 cmp
  签名: (a b : NONote)
  定义体: ONote.cmp a.1 b.1

Depends on / 依赖: ONote.cmp
-/
def cmp (a b : NONote) : Ordering :=
  ONote.cmp a.1 b.1

/--
theorem `cmp_compares` / 定理 `cmp_compares`

English:
theorem cmp_compares
  statement: forall a b : NONote, (cmp a b).Compares a b
  proof: ONote.cmp_compares a b
    cases h : ONote.cmp a b <;> simp only [h] at this <;> try exact this
    exact Subtype.mk_eq_mk.2 this

中文:
定理 cmp_compares
  结论: 对任意 a b : NONote, (cmp a b).Compares a b
  证明: ONote.cmp_compares a b
    cases h : ONote.cmp a b <;> simp only [h] at this <;> try exact this
    exact Subtype.mk_eq_mk.2 this

Depends on / 依赖: ONote.cmp_compares, cmp_compares
-/
theorem cmp_compares : forall a b : NONote, (cmp a b).Compares a b
  | ⟨a, ha⟩, ⟨b, hb⟩ => by
    dsimp [cmp]
    have := ONote.cmp_compares a b
    cases h : ONote.cmp a b <;> simp only [h] at this <;> try exact this
    exact Subtype.mk_eq_mk.2 this

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LinearOrder NONote
  body: linearOrderOfCompares cmp cmp_compares

中文:
实例 :
  签名: 线性序 NONote
  定义体: linearOrderOfCompares cmp cmp_compares

Depends on / 依赖: cmp_compares, linearOrderOfCompares
-/
instance : LinearOrder NONote :=
  linearOrderOfCompares cmp cmp_compares

/--
Definition of `below` / `below` 的定义

English:
definition below
  signature: (a b : NONote)
  body: NFBelow a.1 (repr b)

中文:
定义 below
  签名: (a b : NONote)
  定义体: NFBelow a.1 (repr b)

Depends on / 依赖: NFBelow
-/
def below (a b : NONote) : Prop :=
  NFBelow a.1 (repr b)

/--
Definition of `oadd` / `oadd` 的定义

English:
definition oadd
  signature: (e : NONote) (n : Nat+) (a : NONote) (h : below a e)
  body: ⟨_, NF.oadd e.2 n h⟩

中文:
定义 oadd
  签名: (e : NONote) (n : 自然数+) (a : NONote) (h : below a e)
  定义体: ⟨_, NF.oadd e.2 n h⟩

Depends on / 依赖: NF.oadd
-/
def oadd (e : NONote) (n : Nat+) (a : NONote) (h : below a e) : NONote :=
  ⟨_, NF.oadd e.2 n h⟩

/-- This is a recursor-like theorem for `NONote` suggesting an inductive definition, which can't
actually be defined this way due to conflicting dependencies. -/
@[elab_as_elim]
/--
Definition of `recOn` / `recOn` 的定义

English:
definition recOn
  signature: {C : NONote -> Sort*} (o : NONote) (H0 : C 0)
  body: by
  obtain ⟨o, h⟩ := o; induction o with
  | zero => exact H0
  | oadd e n a IHe IHa => exact H1 ⟨e, h.fst⟩ n ⟨a, h.snd⟩ h.snd' (IHe _) (IHa _)

中文:
定义 recOn
  签名: {C : NONote -> 类型层*} (o : NONote) (H0 : C 0)
  定义体: by
  obtain ⟨o, h⟩ := o; induction o with
  | zero => exact H0
  | oadd e n a IHe IHa => exact H1 ⟨e, h.fst⟩ n ⟨a, h.snd⟩ h.snd' (IHe _) (IHa _)

Depends on / 依赖: h.fst, h.snd
-/
def recOn {C : NONote -> Sort*} (o : NONote) (H0 : C 0)
    (H1 : forall e n a h, C e -> C a -> C (oadd e n a h)) : C o := by
  obtain ⟨o, h⟩ := o; induction o with
  | zero => exact H0
  | oadd e n a IHe IHa => exact H1 ⟨e, h.fst⟩ n ⟨a, h.snd⟩ h.snd' (IHe _) (IHa _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add NONote
  body: ⟨fun x y => mk (x.1 + y.1)⟩

中文:
实例 :
  签名: 加法 NONote
  定义体: ⟨fun x y => mk (x.1 + y.1)⟩
-/
instance : Add NONote :=
  ⟨fun x y => mk (x.1 + y.1)⟩

/--
theorem `repr_add` / 定理 `repr_add`

English:
theorem repr_add
  given: (a b)
  statement: repr (a + b) = repr a + repr b
  proof: ONote.repr_add a.1 b.1

中文:
定理 repr_add
  条件: (a b)
  结论: repr (a + b) = repr a + repr b
  证明: ONote.repr_add a.1 b.1

Depends on / 依赖: ONote.repr_add, repr_add
-/
theorem repr_add (a b) : repr (a + b) = repr a + repr b :=
  ONote.repr_add a.1 b.1

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Sub NONote
  body: ⟨fun x y => mk (x.1 - y.1)⟩

中文:
实例 :
  签名: 减法 NONote
  定义体: ⟨fun x y => mk (x.1 - y.1)⟩
-/
instance : Sub NONote :=
  ⟨fun x y => mk (x.1 - y.1)⟩

/--
theorem `repr_sub` / 定理 `repr_sub`

English:
theorem repr_sub
  given: (a b)
  statement: repr (a - b) = repr a - repr b
  proof: ONote.repr_sub a.1 b.1

中文:
定理 repr_sub
  条件: (a b)
  结论: repr (a - b) = repr a - repr b
  证明: ONote.repr_sub a.1 b.1

Depends on / 依赖: ONote.repr_sub, repr_sub
-/
theorem repr_sub (a b) : repr (a - b) = repr a - repr b :=
  ONote.repr_sub a.1 b.1

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mul NONote
  body: ⟨fun x y => mk (x.1 * y.1)⟩

中文:
实例 :
  签名: 乘法 NONote
  定义体: ⟨fun x y => mk (x.1 * y.1)⟩
-/
instance : Mul NONote :=
  ⟨fun x y => mk (x.1 * y.1)⟩

/--
theorem `repr_mul` / 定理 `repr_mul`

English:
theorem repr_mul
  given: (a b)
  statement: repr (a * b) = repr a * repr b
  proof: ONote.repr_mul a.1 b.1

中文:
定理 repr_mul
  条件: (a b)
  结论: repr (a * b) = repr a * repr b
  证明: ONote.repr_mul a.1 b.1

Depends on / 依赖: ONote.repr_mul, repr_mul
-/
theorem repr_mul (a b) : repr (a * b) = repr a * repr b :=
  ONote.repr_mul a.1 b.1

/--
Definition of `opow` / `opow` 的定义

English:
definition opow
  signature: (x y : NONote)
  body: mk (x.1 ^ y.1)

中文:
定义 opow
  签名: (x y : NONote)
  定义体: mk (x.1 ^ y.1)
-/
def opow (x y : NONote) :=
  mk (x.1 ^ y.1)

/--
theorem `repr_opow` / 定理 `repr_opow`

English:
theorem repr_opow
  given: (a b)
  statement: repr (opow a b) = repr a ^ repr b
  proof: ONote.repr_opow a.1 b.1

中文:
定理 repr_opow
  条件: (a b)
  结论: repr (opow a b) = repr a ^ repr b
  证明: ONote.repr_opow a.1 b.1

Depends on / 依赖: ONote.repr_opow, repr_opow
-/
theorem repr_opow (a b) : repr (opow a b) = repr a ^ repr b :=
  ONote.repr_opow a.1 b.1

end NONote
