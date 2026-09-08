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

/-- An alternate definition of `Fin n` defined as an inductive type instead of a subtype of `ℕ`. -/
/-
**Fin2** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：ℕ → Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An alternate definition of `Fin n` defined as an inductive type instead of a sub
type of `ℕ`.
-/
inductive Fin2 : ℕ → Type
  /-- `0` as a member of `Fin (n + 1)` (`Fin 0` is empty) -/
  | fz {n} : Fin2 (n + 1)
  /-- `n` as a member of `Fin (n + 1)` -/
  | fs {n} : Fin2 n → Fin2 (n + 1)

namespace Fin2

/-- Define a dependent function on `Fin2 (succ n)` by giving its value at
zero (`H1`) and by giving a dependent function on the rest (`H2`). -/
@[elab_as_elim]
/-
**Fin2.cases'** 是 Mathlib 中的一个定义，位于命名空间 `Fin2`。
形式化陈述：{n : ℕ} → {C : Fin2 n.succ → Sort u} → C Fin2.fz → ((n_1 : Fin2 n) → C n_1
.fs) → (i : Fin2 n.succ) → C i
参数：(n_1 : Fin2 n) → C n_1.fs；i : Fin2 n.succ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Define a dependent function on `Fin2 (succ n)` by giving its value at
zero (`H1`) and by giving a dependent function on the rest (`H2`).
-/
protected def cases' {n} {C : Fin2 (succ n) → Sort u} (H1 : C fz) (H2 : ∀ n, C (fs n)) :
    ∀ i : Fin2 (succ n), C i
  | fz => H1
  | fs n => H2 n

/-- Ex falso. The dependent eliminator for the empty `Fin2 0` type. -/
/-
**Fin2.elim0** 是 Mathlib 中的一个定义，位于命名空间 `Fin2`。
形式化陈述：elim0 {C : Fin2 0 -> Sort u} : forall i : Fin2 0, C i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Ex falso. The dependent eliminator for the empty `Fin2 0` type.
-/
def elim0 {C : Fin2 0 → Sort u} : ∀ i : Fin2 0, C i := nofun

/-- Converts a `Fin2` into a natural. -/
/-
**Fin2.toNat** 是 Mathlib 中的一个定义，位于命名空间 `Fin2`。
形式化陈述：{n : ℕ} → Fin2 n → ℕ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Converts a `Fin2` into a natural.
-/
def toNat : ∀ {n}, Fin2 n → ℕ
  | _, @fz _ => 0
  | _, @fs _ i => succ (toNat i)

/-- Converts a natural into a `Fin2` if it is in range -/
/-
**Fin2.optOfNat** 是 Mathlib 中的一个定义，位于命名空间 `Fin2`。
形式化陈述：{n : ℕ} → ℕ → Option (Fin2 n)
参数：Fin2 n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Converts a natural into a `Fin2` if it is in range
-/
def optOfNat : ∀ {n}, ℕ → Option (Fin2 n)
  | 0, _ => none
  | succ _, 0 => some fz
  | succ m, succ k => fs <$> @optOfNat m k

/-- `i + k : Fin2 (n + k)` when `i : Fin2 n` and `k : ℕ` -/
/-
**Fin2.add** 是 Mathlib 中的一个定义，位于命名空间 `Fin2`。
形式化陈述：{n : ℕ} → Fin2 n → (k : ℕ) → Fin2 (n + k)
参数：k : ℕ；n + k。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`i + k : Fin2 (n + k)` when `i : Fin2 n` and `k : ℕ`
-/
def add {n} (i : Fin2 n) : ∀ k, Fin2 (n + k)
  | 0 => i
  | succ k => fs (add i k)

/-- `left k` is the embedding `Fin2 n → Fin2 (k + n)` -/
/-
**Fin2.left** 是 Mathlib 中的一个定义，位于命名空间 `Fin2`。
形式化陈述：(k : ℕ) → {n : ℕ} → Fin2 n → Fin2 (k + n)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`left k` is the embedding `Fin2 n → Fin2 (k + n)`
-/
def left (k) : ∀ {n}, Fin2 n → Fin2 (k + n)
  | _, @fz _ => fz
  | _, @fs _ i => fs (left k i)

/-- `insertPerm a` is a permutation of `Fin2 n` with the following properties:
  * `insertPerm a i = i+1` if `i < a`
  * `insertPerm a a = 0`
  * `insertPerm a i = i` if `i > a` -/
/-
**Fin2.insertPerm** 是 Mathlib 中的一个定义，位于命名空间 `Fin2`。
形式化陈述：{n : ℕ} → Fin2 n → Fin2 n → Fin2 n
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`insertPerm a` is a permutation of `Fin2 n` with the following properties:
  * `insertPerm a i = i+1` if `i < a`
  * `insertPerm a a = 0`
  * `insertPerm a i = i` if `i > a`
-/
def insertPerm : ∀ {n}, Fin2 n → Fin2 n → Fin2 n
  | _, @fz _, @fz _ => fz
  | _, @fz _, @fs _ j => fs j
  | _, @fs (succ _) _, @fz _ => fs fz
  | _, @fs (succ _) i, @fs _ j =>
    match insertPerm i j with
    | fz => fz
    | fs k => fs (fs k)

/-- `remapLeft f k : Fin2 (m + k) → Fin2 (n + k)` applies the function
  `f : Fin2 m → Fin2 n` to inputs less than `m`, and leaves the right part
  on the right (that is, `remapLeft f k (m + i) = n + i`). -/
/-
**Fin2.remapLeft** 是 Mathlib 中的一个定义，位于命名空间 `Fin2`。
形式化陈述：{m n : ℕ} → (Fin2 m → Fin2 n) → (k : ℕ) → Fin2 (m + k) → Fin2 (n + k)
参数：Fin2 m → Fin2 n；k : ℕ；m + k；n + k。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`remapLeft f k : Fin2 (m + k) → Fin2 (n + k)` applies the function
  `f : Fin2 m → Fin2 n` to inputs less than `m`, and leaves the right part
  on the right (that is, `remapLeft f k (m + i) = n + i`).
-/
def remapLeft {m n} (f : Fin2 m → Fin2 n) : ∀ k, Fin2 (m + k) → Fin2 (n + k)
  | 0, i => f i
  | _k + 1, @fz _ => fz
  | _k + 1, @fs _ i => fs (remapLeft f _ i)

/-- This is a simple type class inference prover for proof obligations
  of the form `m < n` where `m n : ℕ`. -/
/-
**Fin2.IsLT** 是 Mathlib 中的一个归纳类型，位于命名空间 `Fin2`。
形式化陈述：ℕ → ℕ → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is a simple type class inference prover for proof obligations
  of the form `m < n` where `m n : ℕ`.
-/
class IsLT (m n : ℕ) : Prop where
  /-- The unique field of `Fin2.IsLT`, a proof that `m < n`. -/
  h : m < n
/-
**Fin2.IsLT.zero** 是 Mathlib 中的一个定理，位于命名空间 `Fin2.IsLT`。
形式化陈述：∀ (n : ℕ), Fin2.IsLT 0 n.succ
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
-/
instance IsLT.zero (n) : IsLT 0 (succ n) :=
  ⟨succ_pos _⟩
/-
**Fin2.IsLT.succ** 是 Mathlib 中的一个定理，位于命名空间 `Fin2.IsLT`。
形式化陈述：∀ (m n : ℕ) [l : Fin2.IsLT m n], Fin2.IsLT m.succ n.succ
参数：m n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.succ_lt_succ`：∀ {n m : ℕ}, n < m → n.succ < m.succ
· 使用定理 `Fin2.IsLT.h`：∀ {m n : ℕ} [self : Fin2.IsLT m n], m < n
-/
instance IsLT.succ (m n) [l : IsLT m n] : IsLT (succ m) (succ n) :=
  ⟨succ_lt_succ l.h⟩

/-- Use type class inference to infer the boundedness proof, so that we can directly convert a
`Nat` into a `Fin2 n`. This supports notation like `&1 : Fin 3`. -/
/-
**Fin2.ofNat'** 是 Mathlib 中的一个定义，位于命名空间 `Fin2`。
形式化陈述：{n : ℕ} → (m : ℕ) → [Fin2.IsLT m n] → Fin2 n
参数：m : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Use type class inference to infer the boundedness proof, so that we can directly
 convert a
`Nat` into a `Fin2 n`. This supports notation like `&1 : Fin 3`.
-/
def ofNat' : ∀ {n} (m) [IsLT m n], Fin2 n
  | 0, _, h => absurd h.h (Nat.not_lt_zero _)
  | succ _, 0, _ => fz
  | succ n, succ m, h => fs (@ofNat' n m ⟨lt_of_succ_lt_succ h.h⟩)

/-- `castSucc i` embeds `i : Fin2 n` in `Fin2 (n+1)`. -/
/-
**Fin2.castSucc** 是 Mathlib 中的一个定义，位于命名空间 `Fin2`。
形式化陈述：{n : ℕ} → Fin2 n → Fin2 (n + 1)
参数：n + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`castSucc i` embeds `i : Fin2 n` in `Fin2 (n+1)`.
-/
def castSucc {n} : Fin2 n → Fin2 (n + 1)
  | fz => fz
  | fs k => fs <| castSucc k

/-- The greatest value of `Fin2 (n+1)`. -/
/-
**Fin2.last** 是 Mathlib 中的一个定义，位于命名空间 `Fin2`。
形式化陈述：{n : ℕ} → Fin2 (n + 1)
参数：n + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The greatest value of `Fin2 (n+1)`.
-/
def last : {n : Nat} → Fin2 (n + 1)
  | 0 => fz
  | n + 1 => fs (@last n)

/-- Maps `0` to `n-1`, `1` to `n-2`, ..., `n-1` to `0`. -/
/-
**Fin2.rev** 是 Mathlib 中的一个定义，位于命名空间 `Fin2`。
形式化陈述：{n : ℕ} → Fin2 n → Fin2 n
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Maps `0` to `n-1`, `1` to `n-2`, ..., `n-1` to `0`.
-/
def rev {n : Nat} : Fin2 n → Fin2 n
  | .fz => last
  | .fs i => i.rev.castSucc
/-
**Fin2.rev_last** 是 Mathlib 中的一个定理，位于命名空间 `Fin2`。
形式化陈述：∀ {n : ℕ}, Fin2.last.rev = Fin2.fz
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin2.rev.eq_1`：∀ (n_1 : ℕ), Fin2.fz.rev = Fin2.last
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Fin2.rev.eq_2`：∀ (n_1 : ℕ) (i : Fin2 n_1), i.fs.rev = i.rev.castSucc
· 使用定理 `Fin2.castSucc.eq_1`：∀ (n_1 : ℕ), Fin2.fz.castSucc = Fin2.fz
-/
@[simp] lemma rev_last {n} : rev (@last n) = fz := by
  induction n <;> simp_all [rev, castSucc, last]
/-
**Fin2.rev_castSucc** 是 Mathlib 中的一个定理，位于命名空间 `Fin2`。
形式化陈述：∀ {n : ℕ} (i : Fin2 n), i.castSucc.rev = i.rev.fs
参数：i : Fin2 n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin2.rev.eq_1`：∀ (n_1 : ℕ), Fin2.fz.rev = Fin2.last
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Fin2.rev.eq_2`：∀ (n_1 : ℕ) (i : Fin2 n_1), i.fs.rev = i.rev.castSucc
· 使用定理 `Fin2.castSucc.eq_2`：∀ (n_1 : ℕ) (i : Fin2 n_1), i.fs.castSucc = i.castSu
cc.fs
-/
@[simp] lemma rev_castSucc {n} (i : Fin2 n) : rev (castSucc i) = fs (rev i) := by
  induction i <;> simp_all [rev, castSucc, last]
/-
**Fin2.rev_rev** 是 Mathlib 中的一个定理，位于命名空间 `Fin2`。
形式化陈述：∀ {n : ℕ} (i : Fin2 n), i.rev.rev = i
参数：i : Fin2 n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin2.rev_last`：∀ {n : ℕ}, Fin2.last.rev = Fin2.fz
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Fin2.rev_castSucc`：∀ {n : ℕ} (i : Fin2 n), i.castSucc.rev = i.rev.fs
-/
@[simp] lemma rev_rev {n} (i : Fin2 n) : i.rev.rev = i := by
  induction i <;> simp_all [rev]
/-
**Fin2.rev_involutive** 是 Mathlib 中的一个定理，位于命名空间 `Fin2`。
形式化陈述：rev_involutive {n} : Function.Involutive (@rev n)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin2.rev_rev`：∀ {n : ℕ} (i : Fin2 n), i.rev.rev = i
-/
theorem rev_involutive {n} : Function.Involutive (@rev n) := rev_rev

@[inherit_doc] local prefix:arg "&" => ofNat'
/-
**Fin2.** 是 Mathlib 中的一个实例，位于命名空间 `Fin2`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Fin2 1) :=
  ⟨fz⟩

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.whitespace false in -- manual alignment is not recognised
/-
**Fin2.instFintype** 是 Mathlib 中的一个实例，位于命名空间 `Fin2`。
形式化陈述：instFintype : forall n, Fintype (Fin2 n) | 0 => ⟨∅, Fin2.elim0⟩ | n + 1 =>
 let ⟨elems, compl⟩
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instFintype : ∀ n, Fintype (Fin2 n)
  | 0 => ⟨∅, Fin2.elim0⟩
  | n + 1 =>
    let ⟨elems, compl⟩ := instFintype n
    { elems    := elems.map ⟨Fin2.fs, @fs.inj _⟩ |>.cons .fz (by simp)
      complete := by rintro (_ | i) <;> simp [compl] }

/-- Converts a `Fin2` into a `Fin`. -/
/-
**Fin2.toFin** 是 Mathlib 中的一个定义，位于命名空间 `Fin2`。
形式化陈述：toFin {n : Nat} (i : Fin2 n) : Fin n
参数：i : Fin2 n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Converts a `Fin2` into a `Fin`.
-/
def toFin {n : Nat} (i : Fin2 n) : Fin n :=
  match i with
  | fz => 0
  | fs i => i.toFin.succ

@[simp]
/-
**Fin2.toFin_fz** 是 Mathlib 中的一个定理，位于命名空间 `Fin2`。
形式化陈述：toFin_fz (n : Nat) : toFin (@fz n) = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFin_fz (n : Nat) : toFin (@fz n) = 0 := rfl

@[simp]
/-
**Fin2.toFin_fs** 是 Mathlib 中的一个定理，位于命名空间 `Fin2`。
形式化陈述：toFin_fs {n : Nat} (i : Fin2 n) : toFin (fs i) = (toFin i).succ
参数：i : Fin2 n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFin_fs {n : Nat} (i : Fin2 n) : toFin (fs i) = (toFin i).succ := rfl

/-- Converts a `Fin` into a `Fin2`. -/
/-
**Fin2.ofFin** 是 Mathlib 中的一个定义，位于命名空间 `Fin2`。
形式化陈述：ofFin {n : Nat} (i : Fin n) : Fin2 n
参数：i : Fin n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Converts a `Fin` into a `Fin2`.
-/
def ofFin {n : Nat} (i : Fin n) : Fin2 n :=
  i.succRec (fun _ => fz) (fun _ _ => fs)

@[simp]
/-
**Fin2.ofFin_zero** 是 Mathlib 中的一个定理，位于命名空间 `Fin2`。
形式化陈述：ofFin_zero (n : Nat) : ofFin 0 = @fz n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem ofFin_zero (n : Nat) : ofFin 0 = @fz n := rfl

@[simp]
/-
**Fin2.ofFin_succ** 是 Mathlib 中的一个定理，位于命名空间 `Fin2`。
形式化陈述：ofFin_succ {n : Nat} (i : Fin n) : ofFin i.succ = fs (ofFin i)
参数：i : Fin n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofFin_succ {n : Nat} (i : Fin n) : ofFin i.succ = fs (ofFin i) := rfl

@[simp]
/-
**Fin2.toFin_ofFin** 是 Mathlib 中的一个定理，位于命名空间 `Fin2`。
形式化陈述：toFin_ofFin {n : Nat} (i : Fin n) : toFin (ofFin i) = i
参数：i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.lt_of_succ_lt_succ`：∀ {n m : ℕ}, n.succ < m.succ → n < m
· 使用定理 `Nat.succ_lt_succ`：∀ {n m : ℕ}, n < m → n.succ < m.succ
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
-/
theorem toFin_ofFin {n : Nat} (i : Fin n) : toFin (ofFin i) = i :=
  i.succRec (fun _ => rfl) (fun _ _ ih => congrArg Fin.succ ih)

@[simp]
/-
**Fin2.ofFin_toFin** 是 Mathlib 中的一个定理，位于命名空间 `Fin2`。
形式化陈述：ofFin_toFin {n : Nat} (i : Fin2 n) : ofFin (toFin i) = i
参数：i : Fin2 n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.lt_of_succ_lt_succ`：∀ {n m : ℕ}, n.succ < m.succ → n < m
· 使用定理 `Nat.succ_lt_succ`：∀ {n m : ℕ}, n < m → n.succ < m.succ
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
-/
theorem ofFin_toFin {n : Nat} (i : Fin2 n) : ofFin (toFin i) = i := by
  induction i with
  | fz => rfl
  | fs _ ih => exact congrArg fs ih

/-- `Fin2` is equivalent to the usual encoding of `Fin` as a subtype of `ℕ`. -/
@[simps]
/-
**Fin2.equivFin** 是 Mathlib 中的一个定义，位于命名空间 `Fin2`。
形式化陈述：equivFin (n : Nat) : Fin2 n ≃ Fin n where toFun
参数：n : Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Fin2.ofFin_toFin`：ofFin_toFin {n : Nat} (i : Fin2 n) : ofFin (toFin i) =
 i
· 使用定理 `Fin2.toFin_ofFin`：toFin_ofFin {n : Nat} (i : Fin n) : toFin (ofFin i) = 
i

--- 原说明 ---
`Fin2` is equivalent to the usual encoding of `Fin` as a subtype of `ℕ`.
-/
def equivFin (n : Nat) : Fin2 n ≃ Fin n where
  toFun := toFin
  invFun := ofFin
  left_inv := ofFin_toFin
  right_inv := toFin_ofFin

end Fin2

