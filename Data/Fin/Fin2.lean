/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Nat.Notation
public import Mathlib.Logic.Function.Basic

/-!
# Inductive type variant of `Fin`

`Fin` is defined as a subtype of `ℕ`. This file defines an equivalent type, `Fin2`, which is
defined inductively. This is useful for its induction principle and different definitional
equalities.

## Main declarations

* `Fin2 n`: Inductive type variant of `Fin n`. `fz` corresponds to `0` and `fs n` corresponds to
  `n`.
* `Fin2.toNat`, `Fin2.optOfNat`, `Fin2.ofNat'`: Conversions to and from `ℕ`. `ofNat' m` takes a
  proof that `m < n` through the class `Fin2.IsLT`.
* `Fin2.add k`: Takes `i : Fin2 n` to `i + k : Fin2 (n + k)`.
* `Fin2.left`: Embeds `Fin2 n` into `Fin2 (n + k)`.
* `Fin2.insertPerm a`: Permutation of `Fin2 n` which cycles `0, ..., a - 1` and leaves
  `a, ..., n - 1` unchanged.
* `Fin2.remapLeft f`: Function `Fin2 (m + k) → Fin2 (n + k)` by applying `f : Fin m → Fin n` to
  `0, ..., m - 1` and sending `m + i` to `n + i`.
-/

@[expose] public section

open Nat

universe u

/--
Inductive type `Fin2` / 归纳类型 `Fin2`

English:
inductive Fin2
  parameters: : Nat -> Type
  constructors (2):
    - fz: {n} : Fin2 (n + 1)
    - fs: {n} : Fin2 n -> Fin2 (n + 1)

中文:
归纳类型 Fin2
  参数: : 自然数 -> Type
  构造子 (2 个):
    - fz: {n} : Fin2 (n + 1)
    - fs: {n} : Fin2 n -> Fin2 (n + 1)
-/
inductive Fin2 : Nat -> Type
  /-- `0` as a member of `Fin (n + 1)` (`Fin 0` is empty) -/
  | fz {n} : Fin2 (n + 1)
  /-- `n` as a member of `Fin (n + 1)` -/
  | fs {n} : Fin2 n -> Fin2 (n + 1)

namespace Fin2

/-- Define a dependent function on `Fin2 (succ n)` by giving its value at
zero (`H1`) and by giving a dependent function on the rest (`H2`). -/
@[elab_as_elim]
/--
Definition of `cases'` / `cases'` 的定义

English:
definition cases'
  signature: {n} {C : Fin2 (succ n) -> Sort u} (H1 : C fz) (H2 : forall n, C (fs n))

中文:
定义 cases'
  签名: {n} {C : Fin2 (succ n) -> Sort u} (H1 : C fz) (H2 : 对任意 n, C (fs n))
-/
protected def cases' {n} {C : Fin2 (succ n) -> Sort u} (H1 : C fz) (H2 : forall n, C (fs n)) :
    forall i : Fin2 (succ n), C i
  | fz => H1
  | fs n => H2 n

/--
Definition of `elim0` / `elim0` 的定义

English:
definition elim0
  signature: {C : Fin2 0 -> Sort u}
  body: nofun

中文:
定义 elim0
  签名: {C : Fin2 0 -> Sort u}
  定义体: nofun
-/
def elim0 {C : Fin2 0 -> Sort u} : forall i : Fin2 0, C i := nofun

/--
Definition of `toNat` / `toNat` 的定义

English:
definition toNat
  signature: : forall {n}, Fin2 n -> Nat

中文:
定义 toNat
  签名: : 对任意 {n}, Fin2 n -> 自然数
-/
def toNat : forall {n}, Fin2 n -> Nat
  | _, @fz _ => 0
  | _, @fs _ i => succ (toNat i)

/--
Definition of `optOfNat` / `optOfNat` 的定义

English:
definition optOfNat
  signature: : forall {n}, Nat -> Option (Fin2 n)

中文:
定义 optOfNat
  签名: : 对任意 {n}, 自然数 -> Option (Fin2 n)
-/
def optOfNat : forall {n}, Nat -> Option (Fin2 n)
  | 0, _ => none
  | succ _, 0 => some fz
| succ m, succ k => fs < > @optOfNat m k

/--
Definition of `add` / `add` 的定义

English:
definition add
  signature: {n} (i : Fin2 n)

中文:
定义 add
  签名: {n} (i : Fin2 n)
-/
def add {n} (i : Fin2 n) : forall k, Fin2 (n + k)
  | 0 => i
  | succ k => fs (add i k)

/--
Definition of `left` / `left` 的定义

English:
definition left
  signature: (k)

中文:
定义 left
  签名: (k)
-/
def left (k) : forall {n}, Fin2 n -> Fin2 (k + n)
  | _, @fz _ => fz
  | _, @fs _ i => fs (left k i)

/--
Definition of `insertPerm` / `insertPerm` 的定义

English:
definition insertPerm
  signature: : forall {n}, Fin2 n -> Fin2 n -> Fin2 n

中文:
定义 insertPerm
  签名: : 对任意 {n}, Fin2 n -> Fin2 n -> Fin2 n
-/
def insertPerm : forall {n}, Fin2 n -> Fin2 n -> Fin2 n
  | _, @fz _, @fz _ => fz
  | _, @fz _, @fs _ j => fs j
  | _, @fs (succ _) _, @fz _ => fs fz
  | _, @fs (succ _) i, @fs _ j =>
    match insertPerm i j with
    | fz => fz
    | fs k => fs (fs k)

/--
Definition of `remapLeft` / `remapLeft` 的定义

English:
definition remapLeft
  signature: {m n} (f : Fin2 m -> Fin2 n)

中文:
定义 remapLeft
  签名: {m n} (f : Fin2 m -> Fin2 n)
-/
def remapLeft {m n} (f : Fin2 m -> Fin2 n) : forall k, Fin2 (m + k) -> Fin2 (n + k)
  | 0, i => f i
  | _k + 1, @fz _ => fz
  | _k + 1, @fs _ i => fs (remapLeft f _ i)

/--
Definition of `IsLT` / `IsLT` 的定义

English:
class IsLT
  parameters: (m n : Nat)
  axioms and operations (1):
    - h : m < n

中文:
类 IsLT
  参数: (m n : 自然数)
  公理与运算 (1 个):
    - h : m < n
-/
class IsLT (m n : Nat) : Prop where
  /-- The unique field of `Fin2.IsLT`, a proof that `m < n`. -/
  h : m < n

/--
Instance `IsLT.zero` / 实例 `IsLT.zero`

English:
instance IsLT.zero
  signature: (n)
  body: ⟨succ_pos _⟩

中文:
实例 IsLT.zero
  签名: (n)
  定义体: ⟨succ_pos _⟩

Depends on / 依赖: succ_pos
-/
instance IsLT.zero (n) : IsLT 0 (succ n) :=
  ⟨succ_pos _⟩

/--
Instance `IsLT.succ` / 实例 `IsLT.succ`

English:
instance IsLT.succ
  signature: (m n) [l : IsLT m n]
  body: ⟨succ_lt_succ l.h⟩

中文:
实例 IsLT.succ
  签名: (m n) [l : IsLT m n]
  定义体: ⟨succ_lt_succ l.h⟩

Depends on / 依赖: succ_lt_succ
-/
instance IsLT.succ (m n) [l : IsLT m n] : IsLT (succ m) (succ n) :=
  ⟨succ_lt_succ l.h⟩

/--
Definition of `ofNat'` / `ofNat'` 的定义

English:
definition ofNat'
  signature: : forall {n} (m) [IsLT m n], Fin2 n

中文:
定义 ofNat'
  签名: : 对任意 {n} (m) [IsLT m n], Fin2 n
-/
def ofNat' : forall {n} (m) [IsLT m n], Fin2 n
  | 0, _, h => absurd h.h (Nat.not_lt_zero _)
  | succ _, 0, _ => fz
  | succ n, succ m, h => fs (@ofNat' n m ⟨lt_of_succ_lt_succ h.h⟩)

/--
Definition of `castSucc` / `castSucc` 的定义

English:
definition castSucc
  signature: {n}

中文:
定义 castSucc
  签名: {n}
-/
def castSucc {n} : Fin2 n -> Fin2 (n + 1)
  | fz => fz
| fs k => fs castSucc k

/--
Definition of `last` / `last` 的定义

English:
definition last
  signature: : {n : Nat} -> Fin2 (n + 1)

中文:
定义 last
  签名: : {n : 自然数} -> Fin2 (n + 1)
-/
def last : {n : Nat} -> Fin2 (n + 1)
  | 0 => fz
  | n + 1 => fs (@last n)

/--
Definition of `rev` / `rev` 的定义

English:
definition rev
  signature: {n : Nat}

中文:
定义 rev
  签名: {n : 自然数}
-/
def rev {n : Nat} : Fin2 n -> Fin2 n
  | .fz => last
  | .fs i => i.rev.castSucc

/--
lemma `rev_last` / 引理 `rev_last`

English:
lemma rev_last
  given: {n}
  statement: rev (@last n) = fz
  proof: by
  induction n <;> simp_all [rev, castSucc, last]

中文:
引理 rev_last
  条件: {n}
  结论: rev (@last n) = fz
  证明: by
  induction n <;> simp_all [rev, castSucc, last]
-/
@[simp] lemma rev_last {n} : rev (@last n) = fz := by
  induction n <;> simp_all [rev, castSucc, last]

/--
lemma `rev_castSucc` / 引理 `rev_castSucc`

English:
lemma rev_castSucc
  given: {n} (i : Fin2 n)
  statement: rev (castSucc i) = fs (rev i)
  proof: by
  induction i <;> simp_all [rev, castSucc, last]

中文:
引理 rev_castSucc
  条件: {n} (i : Fin2 n)
  结论: rev (castSucc i) = fs (rev i)
  证明: by
  induction i <;> simp_all [rev, castSucc, last]
-/
@[simp] lemma rev_castSucc {n} (i : Fin2 n) : rev (castSucc i) = fs (rev i) := by
  induction i <;> simp_all [rev, castSucc, last]

/--
lemma `rev_rev` / 引理 `rev_rev`

English:
lemma rev_rev
  given: {n} (i : Fin2 n)
  statement: i.rev.rev = i
  proof: by
  induction i <;> simp_all [rev]

中文:
引理 rev_rev
  条件: {n} (i : Fin2 n)
  结论: i.rev.rev = i
  证明: by
  induction i <;> simp_all [rev]
-/
@[simp] lemma rev_rev {n} (i : Fin2 n) : i.rev.rev = i := by
  induction i <;> simp_all [rev]

/--
theorem `rev_involutive` / 定理 `rev_involutive`

English:
theorem rev_involutive
  given: {n}
  statement: Function.Involutive (@rev n)
  proof: rev_rev

@[inherit_doc] local prefix:arg "&" => ofNat'

中文:
定理 rev_involutive
  条件: {n}
  结论: Function.Involutive (@rev n)
  证明: rev_rev

@[inherit_doc] local prefix:arg "&" => ofNat'

Depends on / 依赖: rev_rev
-/
theorem rev_involutive {n} : Function.Involutive (@rev n) := rev_rev

@[inherit_doc] local prefix:arg "&" => ofNat'

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Fin2 1)
  body: ⟨fz⟩

中文:
实例 :
  签名: Inhabited (Fin2 1)
  定义体: ⟨fz⟩
-/
instance : Inhabited (Fin2 1) :=
  ⟨fz⟩

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.whitespace false in -- manual alignment is not recognised
/--
Instance `instFintype` / 实例 `instFintype`

English:
instance instFintype
  signature: : forall n, Fintype (Fin2 n)
  body: instFintype n
    { elems := elems.map ⟨Fin2.fs, @fs.inj _⟩ |>.cons .fz (by simp)
      complete := by rintro (_ | i) <;> simp [compl] }

中文:
实例 instFintype
  签名: : 对任意 n, Fintype (Fin2 n)
  定义体: instFintype n
    { elems := elems.map ⟨Fin2.fs, @fs.inj _⟩ |>.cons .fz (by simp)
      complete := by rintro (_ | i) <;> simp [compl] }

Depends on / 依赖: instFintype
-/
instance instFintype : forall n, Fintype (Fin2 n)
  | 0 => ⟨∅, Fin2.elim0⟩
  | n + 1 =>
    let ⟨elems, compl⟩ := instFintype n
    { elems := elems.map ⟨Fin2.fs, @fs.inj _⟩ |>.cons .fz (by simp)
      complete := by rintro (_ | i) <;> simp [compl] }

/--
Definition of `toFin` / `toFin` 的定义

English:
definition toFin
  signature: {n : Nat} (i : Fin2 n)
  body: match i with
  | fz => 0
  | fs i => i.toFin.succ

@[simp]

中文:
定义 toFin
  签名: {n : 自然数} (i : Fin2 n)
  定义体: match i with
  | fz => 0
  | fs i => i.toFin.succ

@[simp]

Depends on / 依赖: i.toFin.succ
-/
def toFin {n : Nat} (i : Fin2 n) : Fin n :=
  match i with
  | fz => 0
  | fs i => i.toFin.succ

@[simp]
/--
theorem `toFin_fz` / 定理 `toFin_fz`

English:
theorem toFin_fz
  given: (n : Nat)
  statement: toFin (@fz n) = 0
  proof: rfl

@[simp]

中文:
定理 toFin_fz
  条件: (n : 自然数)
  结论: toFin (@fz n) = 0
  证明: rfl

@[simp]
-/
theorem toFin_fz (n : Nat) : toFin (@fz n) = 0 := rfl

@[simp]
/--
theorem `toFin_fs` / 定理 `toFin_fs`

English:
theorem toFin_fs
  given: {n : Nat} (i : Fin2 n)
  statement: toFin (fs i) = (toFin i).succ
  proof: rfl

中文:
定理 toFin_fs
  条件: {n : 自然数} (i : Fin2 n)
  结论: toFin (fs i) = (toFin i).succ
  证明: rfl
-/
theorem toFin_fs {n : Nat} (i : Fin2 n) : toFin (fs i) = (toFin i).succ := rfl

/--
Definition of `ofFin` / `ofFin` 的定义

English:
definition ofFin
  signature: {n : Nat} (i : Fin n)
  body: i.succRec (fun _ => fz) (fun _ _ => fs)

@[simp]

中文:
定义 ofFin
  签名: {n : 自然数} (i : Fin n)
  定义体: i.succRec (fun _ => fz) (fun _ _ => fs)

@[simp]

Depends on / 依赖: i.succRec, succRec
-/
def ofFin {n : Nat} (i : Fin n) : Fin2 n :=
  i.succRec (fun _ => fz) (fun _ _ => fs)

@[simp]
/--
theorem `ofFin_zero` / 定理 `ofFin_zero`

English:
theorem ofFin_zero
  given: (n : Nat)
  statement: ofFin 0 = @fz n
  proof: rfl

@[simp]

中文:
定理 ofFin_zero
  条件: (n : 自然数)
  结论: ofFin 0 = @fz n
  证明: rfl

@[simp]
-/
theorem ofFin_zero (n : Nat) : ofFin 0 = @fz n := rfl

@[simp]
/--
theorem `ofFin_succ` / 定理 `ofFin_succ`

English:
theorem ofFin_succ
  given: {n : Nat} (i : Fin n)
  statement: ofFin i.succ = fs (ofFin i)
  proof: rfl

@[simp]

中文:
定理 ofFin_succ
  条件: {n : 自然数} (i : Fin n)
  结论: ofFin i.succ = fs (ofFin i)
  证明: rfl

@[simp]
-/
theorem ofFin_succ {n : Nat} (i : Fin n) : ofFin i.succ = fs (ofFin i) := rfl

@[simp]
/--
theorem `toFin_ofFin` / 定理 `toFin_ofFin`

English:
theorem toFin_ofFin
  given: {n : Nat} (i : Fin n)
  statement: toFin (ofFin i) = i
  proof: i.succRec (fun _ => rfl) (fun _ _ ih => congrArg Fin.succ ih)

@[simp]

中文:
定理 toFin_ofFin
  条件: {n : 自然数} (i : Fin n)
  结论: toFin (ofFin i) = i
  证明: i.succRec (fun _ => rfl) (fun _ _ ih => congrArg Fin.succ ih)

@[simp]

Depends on / 依赖: Fin.succ, i.succRec, succRec
-/
theorem toFin_ofFin {n : Nat} (i : Fin n) : toFin (ofFin i) = i :=
  i.succRec (fun _ => rfl) (fun _ _ ih => congrArg Fin.succ ih)

@[simp]
/--
theorem `ofFin_toFin` / 定理 `ofFin_toFin`

English:
theorem ofFin_toFin
  given: {n : Nat} (i : Fin2 n)
  statement: ofFin (toFin i) = i
  proof: by
  induction i with
  | fz => rfl
  | fs _ ih => exact congrArg fs ih

中文:
定理 ofFin_toFin
  条件: {n : 自然数} (i : Fin2 n)
  结论: ofFin (toFin i) = i
  证明: by
  induction i with
  | fz => rfl
  | fs _ ih => exact congrArg fs ih
-/
theorem ofFin_toFin {n : Nat} (i : Fin2 n) : ofFin (toFin i) = i := by
  induction i with
  | fz => rfl
  | fs _ ih => exact congrArg fs ih

/-- `Fin2` is equivalent to the usual encoding of `Fin` as a subtype of `ℕ`. -/
@[simps]
/--
Definition of `equivFin` / `equivFin` 的定义

English:
definition equivFin
  signature: (n : Nat)
  body: toFin
  invFun := ofFin
  left_inv := ofFin_toFin
  right_inv := toFin_ofFin

中文:
定义 equivFin
  签名: (n : 自然数)
  定义体: toFin
  invFun := ofFin
  left_inv := ofFin_toFin
  right_inv := toFin_ofFin
-/
def equivFin (n : Nat) : Fin2 n ≃ Fin n where
  toFun := toFin
  invFun := ofFin
  left_inv := ofFin_toFin
  right_inv := toFin_ofFin

end Fin2
