/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Shing Tak Lam, Mario Carneiro
-/
module

public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Ring.Defs
import all Init.Data.Repr -- for exposing `toDigitsCore`

/-!
# Digits of a natural number

This provides a basic API for extracting the digits of a natural number in a given base,
and reconstructing numbers from their digits.

We also prove some divisibility tests based on digits, in particular completing
Theorem #85 from https://www.cs.ru.nl/~freek/100/.

Also included is a bound on the length of `Nat.toDigits` from core.

## TODO

A basic `norm_digits` tactic for proving goals of the form `Nat.digits a b = l` where `a` and `b`
are numerals is not yet ported.
-/

@[expose] public section

assert_not_exists Finset

namespace Nat

variable {n : Nat}

/--
Definition of `digitsAux0` / `digitsAux0` 的定义

English:
definition digitsAux0
  signature: : Nat -> List Nat

中文:
定义 digitsAux0
  签名: : 自然数 -> 列表 自然数
-/
def digitsAux0 : Nat -> List Nat
  | 0 => []
  | n + 1 => [n+1]

/--
Definition of `digitsAux1` / `digitsAux1` 的定义

English:
definition digitsAux1
  signature: (n : Nat)
  body: List.replicate n 1

中文:
定义 digitsAux1
  签名: (n : 自然数)
  定义体: List.replicate n 1

Depends on / 依赖: List.replicate, replicate
-/
def digitsAux1 (n : Nat) : List Nat :=
  List.replicate n 1

/--
Definition of `digitsAux` / `digitsAux` 的定义

English:
definition digitsAux
  signature: (b : Nat) (h : 2 <= b)

中文:
定义 digitsAux
  签名: (b : 自然数) (h : 2 <= b)
-/
@[semireducible] def digitsAux (b : Nat) (h : 2 <= b) : Nat -> List Nat
  | 0 => []
  | n + 1 =>
    ((n + 1) % b) :: digitsAux b h ((n + 1) / b)
decreasing_by exact Nat.div_lt_self (Nat.succ_pos _) h

@[simp]
/--
theorem `digitsAux_zero` / 定理 `digitsAux_zero`

English:
theorem digitsAux_zero
  given: (b : Nat) (h : 2 <= b)
  statement: digitsAux b h 0 = []
  proof: rfl

中文:
定理 digitsAux_zero
  条件: (b : 自然数) (h : 2 <= b)
  结论: digitsAux b h 0 = []
  证明: rfl
-/
theorem digitsAux_zero (b : Nat) (h : 2 <= b) : digitsAux b h 0 = [] := rfl

/--
theorem `digitsAux_def` / 定理 `digitsAux_def`

English:
theorem digitsAux_def
  given: (b : Nat) (h : 2 <= b) (n : Nat) (w : 0 < n)
  proof: by
  cases n
  · cases w
  · rw [digitsAux]

中文:
定理 digitsAux_def
  条件: (b : 自然数) (h : 2 <= b) (n : 自然数) (w : 0 < n)
  证明: by
  cases n
  · cases w
  · rw [digitsAux]

Depends on / 依赖: digitsAux
-/
theorem digitsAux_def (b : Nat) (h : 2 <= b) (n : Nat) (w : 0 < n) :
    digitsAux b h n = (n % b) :: digitsAux b h (n / b) := by
  cases n
  · cases w
  · rw [digitsAux]

/--
Definition of `digits` / `digits` 的定义

English:
definition digits
  signature: : Nat -> Nat -> List Nat

中文:
定义 digits
  签名: : 自然数 -> 自然数 -> 列表 自然数
-/
def digits : Nat -> Nat -> List Nat
  | 0 => digitsAux0
  | 1 => digitsAux1
  | b + 2 => digitsAux (b + 2) (by simp)

@[simp]
/--
theorem `digits_zero` / 定理 `digits_zero`

English:
theorem digits_zero
  given: (b : Nat)
  statement: digits b 0 = []
  proof: by
  rcases b with (_ | ⟨_ | ⟨_⟩⟩) <;> simp [digits, digitsAux0, digitsAux1]

中文:
定理 digits_zero
  条件: (b : 自然数)
  结论: digits b 0 = []
  证明: by
  rcases b with (_ | ⟨_ | ⟨_⟩⟩) <;> simp [digits, digitsAux0, digitsAux1]

Depends on / 依赖: digits, digitsAux0, digitsAux1
-/
theorem digits_zero (b : Nat) : digits b 0 = [] := by
  rcases b with (_ | ⟨_ | ⟨_⟩⟩) <;> simp [digits, digitsAux0, digitsAux1]

/--
theorem `digits_zero_zero` / 定理 `digits_zero_zero`

English:
theorem digits_zero_zero
  statement: digits 0 0 = []
  proof: rfl

@[simp]

中文:
定理 digits_zero_zero
  结论: digits 0 0 = []
  证明: rfl

@[simp]
-/
theorem digits_zero_zero : digits 0 0 = [] :=
  rfl

@[simp]
/--
theorem `digits_zero_succ` / 定理 `digits_zero_succ`

English:
theorem digits_zero_succ
  given: (n : Nat)
  statement: digits 0 n.succ = [n+1]
  proof: rfl

中文:
定理 digits_zero_succ
  条件: (n : 自然数)
  结论: digits 0 n.succ = [n+1]
  证明: rfl
-/
theorem digits_zero_succ (n : Nat) : digits 0 n.succ = [n+1] :=
  rfl

/--
theorem `digits_zero_succ'` / 定理 `digits_zero_succ'`

English:
theorem digits_zero_succ'
  statement: forall {n : Nat}, n != 0 -> digits 0 n = [n]

中文:
定理 digits_zero_succ'
  结论: 对任意 {n : 自然数}, n != 0 -> digits 0 n = [n]
-/
theorem digits_zero_succ' : forall {n : Nat}, n != 0 -> digits 0 n = [n]
  | 0, h => (h rfl).elim
  | _ + 1, _ => rfl

@[simp]
/--
theorem `digits_one` / 定理 `digits_one`

English:
theorem digits_one
  given: (n : Nat)
  statement: digits 1 n = List.replicate n 1
  proof: rfl

中文:
定理 digits_one
  条件: (n : 自然数)
  结论: digits 1 n = 列表.replicate n 1
  证明: rfl
-/
theorem digits_one (n : Nat) : digits 1 n = List.replicate n 1 :=
  rfl

-- no `@[simp]`: dsimp can prove this
/--
theorem `digits_one_succ` / 定理 `digits_one_succ`

English:
theorem digits_one_succ
  given: (n : Nat)
  statement: digits 1 (n + 1) = 1 :: digits 1 n
  proof: rfl

中文:
定理 digits_one_succ
  条件: (n : 自然数)
  结论: digits 1 (n + 1) = 1 :: digits 1 n
  证明: rfl
-/
theorem digits_one_succ (n : Nat) : digits 1 (n + 1) = 1 :: digits 1 n :=
  rfl

/--
theorem `digits_add_two_add_one` / 定理 `digits_add_two_add_one`

English:
theorem digits_add_two_add_one
  given: (b n : Nat)
  proof: by
  simp [digits, digitsAux_def]

@[simp]

中文:
定理 digits_add_two_add_one
  条件: (b n : 自然数)
  证明: by
  simp [digits, digitsAux_def]

@[simp]

Depends on / 依赖: digits, digitsAux_def
-/
theorem digits_add_two_add_one (b n : Nat) :
    digits (b + 2) (n + 1) = ((n + 1) % (b + 2)) :: digits (b + 2) ((n + 1) / (b + 2)) := by
  simp [digits, digitsAux_def]

@[simp]
/--
lemma `digits_of_two_le_of_pos` / 引理 `digits_of_two_le_of_pos`

English:
lemma digits_of_two_le_of_pos
  given: {b : Nat} (hb : 2 <= b) (hn : 0 < n)
  proof: by
  rw [Nat.eq_add_of_sub_eq hb rfl]; rw [Nat.eq_add_of_sub_eq hn rfl]; rw [Nat.digits_add_two_add_one]

中文:
引理 digits_of_two_le_of_pos
  条件: {b : 自然数} (hb : 2 <= b) (hn : 0 < n)
  证明: by
  rw [Nat.eq_add_of_sub_eq hb rfl]; rw [Nat.eq_add_of_sub_eq hn rfl]; rw [Nat.digits_add_two_add_one]

Depends on / 依赖: Nat.digits_add_two_add_one, Nat.eq_add_of_sub_eq, digits_add_two_add_one, eq_add_of_sub_eq
-/
lemma digits_of_two_le_of_pos {b : Nat} (hb : 2 <= b) (hn : 0 < n) :
    Nat.digits b n = n % b :: Nat.digits b (n / b) := by
  rw [Nat.eq_add_of_sub_eq hb rfl]; rw [Nat.eq_add_of_sub_eq hn rfl]; rw [Nat.digits_add_two_add_one]

/--
theorem `digits_def'` / 定理 `digits_def'`

English:
theorem digits_def'

中文:
定理 digits_def'
-/
theorem digits_def' :
    forall {b : Nat} (_ : 1 < b) {n : Nat} (_ : 0 < n), digits b n = (n % b) :: digits b (n / b)
  | 0, h => absurd h (by decide)
  | 1, h => absurd h (by decide)
  | b + 2, _ => digitsAux_def _ (by simp) _

@[simp]
/--
theorem `digits_of_lt` / 定理 `digits_of_lt`

English:
theorem digits_of_lt
  given: (b x : Nat) (hx : x != 0) (hxb : x < b)
  statement: digits b x = [x]
  proof: by
  rcases exists_eq_succ_of_ne_zero hx with ⟨x, rfl⟩
  rcases Nat.exists_eq_add_of_le' ((Nat.le_add_left 1 x).trans_lt hxb) with ⟨b, rfl⟩
  rw [digits_add_two_add_one]; rw [div_eq_of_lt hxb]; rw [digits_zero]; rw [mod_eq_of_lt hxb]

中文:
定理 digits_of_lt
  条件: (b x : 自然数) (hx : x != 0) (hxb : x < b)
  结论: digits b x = [x]
  证明: by
  rcases exists_eq_succ_of_ne_zero hx with ⟨x, rfl⟩
  rcases Nat.exists_eq_add_of_le' ((Nat.le_add_left 1 x).trans_lt hxb) with ⟨b, rfl⟩
  rw [digits_add_two_add_one]; rw [div_eq_of_lt hxb]; rw [digits_zero]; rw [mod_eq_of_lt hxb]

Depends on / 依赖: Nat.exists_eq_add_of_le, Nat.le_add_left, digits_add_two_add_one, digits_zero, div_eq_of_lt, exists_eq_add_of_le, exists_eq_succ_of_ne_zero, le_add_left, mod_eq_of_lt, trans_lt
-/
theorem digits_of_lt (b x : Nat) (hx : x != 0) (hxb : x < b) : digits b x = [x] := by
  rcases exists_eq_succ_of_ne_zero hx with ⟨x, rfl⟩
  rcases Nat.exists_eq_add_of_le' ((Nat.le_add_left 1 x).trans_lt hxb) with ⟨b, rfl⟩
  rw [digits_add_two_add_one]; rw [div_eq_of_lt hxb]; rw [digits_zero]; rw [mod_eq_of_lt hxb]

/--
theorem `digits_add` / 定理 `digits_add`

English:
theorem digits_add
  given: (b : Nat) (h : 1 < b) (x y : Nat) (hxb : x < b) (hxy : x != 0 ∨ y != 0)
  proof: by
  rcases Nat.exists_eq_add_of_le' h with ⟨b, rfl : _ = _ + 2⟩
  cases y
  · simp [hxb, hxy.resolve_right (absurd rfl)]
  dsimp [digits]
  rw [digitsAux_def]
  · congr
    · simp [Nat.add_mod, mod_eq_of_lt hxb]
    · simp [add_mul_div_left, div_eq_of_lt hxb]
  · apply Nat.succ_pos

中文:
定理 digits_add
  条件: (b : 自然数) (h : 1 < b) (x y : 自然数) (hxb : x < b) (hxy : x != 0 ∨ y != 0)
  证明: by
  rcases Nat.exists_eq_add_of_le' h with ⟨b, rfl : _ = _ + 2⟩
  cases y
  · simp [hxb, hxy.resolve_right (absurd rfl)]
  dsimp [digits]
  rw [digitsAux_def]
  · congr
    · simp [Nat.add_mod, mod_eq_of_lt hxb]
    · simp [add_mul_div_left, div_eq_of_lt hxb]
  · apply Nat.succ_pos

Depends on / 依赖: Nat.add_mod, Nat.exists_eq_add_of_le, Nat.succ_pos, absurd, add_mod, add_mul_div_left, digits, digitsAux_def, div_eq_of_lt, exists_eq_add_of_le, hxy.resolve_right, mod_eq_of_lt, resolve_right, succ_pos
-/
theorem digits_add (b : Nat) (h : 1 < b) (x y : Nat) (hxb : x < b) (hxy : x != 0 ∨ y != 0) :
    digits b (x + b * y) = x :: digits b y := by
  rcases Nat.exists_eq_add_of_le' h with ⟨b, rfl : _ = _ + 2⟩
  cases y
  · simp [hxb, hxy.resolve_right (absurd rfl)]
  dsimp [digits]
  rw [digitsAux_def]
  · congr
    · simp [Nat.add_mod, mod_eq_of_lt hxb]
    · simp [add_mul_div_left, div_eq_of_lt hxb]
  · apply Nat.succ_pos

-- If we had a function converting a list into a polynomial,
-- and appropriate lemmas about that function,
-- we could rewrite this in terms of that.
/--
Definition of `ofDigits` / `ofDigits` 的定义

English:
definition ofDigits
  signature: {α : Type*} [Semiring α] (b : α)

中文:
定义 ofDigits
  签名: {α : 类型} [半环 α] (b : α)
-/
def ofDigits {α : Type*} [Semiring α] (b : α) : List Nat -> α
  | [] => 0
  | h :: t => h + b * ofDigits b t

/--
theorem `ofDigits_eq_foldr` / 定理 `ofDigits_eq_foldr`

English:
theorem ofDigits_eq_foldr
  given: {α : Type*} [Semiring α] (b : α) (L : List Nat)
  proof: by
  induction L with
  | nil => rfl
  | cons d L ih => dsimp [ofDigits]; rw [ih]

@[simp]

中文:
定理 ofDigits_eq_foldr
  条件: {α : 类型} [半环 α] (b : α) (L : 列表 自然数)
  证明: by
  induction L with
  | nil => rfl
  | cons d L ih => dsimp [ofDigits]; rw [ih]

@[simp]

Depends on / 依赖: ofDigits
-/
theorem ofDigits_eq_foldr {α : Type*} [Semiring α] (b : α) (L : List Nat) :
    ofDigits b L = List.foldr (fun x y => ↑x + b * y) 0 L := by
  induction L with
  | nil => rfl
  | cons d L ih => dsimp [ofDigits]; rw [ih]

@[simp]
/--
theorem `ofDigits_nil` / 定理 `ofDigits_nil`

English:
theorem ofDigits_nil
  given: {b : Nat}
  statement: ofDigits b [] = 0
  proof: rfl

@[simp]

中文:
定理 ofDigits_nil
  条件: {b : 自然数}
  结论: ofDigits b [] = 0
  证明: rfl

@[simp]
-/
theorem ofDigits_nil {b : Nat} : ofDigits b [] = 0 := rfl

@[simp]
/--
theorem `ofDigits_singleton` / 定理 `ofDigits_singleton`

English:
theorem ofDigits_singleton
  given: {b n : Nat}
  statement: ofDigits b [n] = n
  proof: by simp [ofDigits]

@[simp]

中文:
定理 ofDigits_singleton
  条件: {b n : 自然数}
  结论: ofDigits b [n] = n
  证明: by simp [ofDigits]

@[simp]

Depends on / 依赖: ofDigits
-/
theorem ofDigits_singleton {b n : Nat} : ofDigits b [n] = n := by simp [ofDigits]

@[simp]
/--
theorem `ofDigits_one_cons` / 定理 `ofDigits_one_cons`

English:
theorem ofDigits_one_cons
  given: {α : Type*} [Semiring α] (h : Nat) (L : List Nat)
  proof: by simp [ofDigits]

中文:
定理 ofDigits_one_cons
  条件: {α : 类型} [半环 α] (h : 自然数) (L : 列表 自然数)
  证明: by simp [ofDigits]

Depends on / 依赖: ofDigits
-/
theorem ofDigits_one_cons {α : Type*} [Semiring α] (h : Nat) (L : List Nat) :
    ofDigits (1 : α) (h :: L) = h + ofDigits 1 L := by simp [ofDigits]

/--
theorem `ofDigits_cons` / 定理 `ofDigits_cons`

English:
theorem ofDigits_cons
  given: {b hd} {tl : List Nat}
  proof: rfl

中文:
定理 ofDigits_cons
  条件: {b hd} {tl : 列表 自然数}
  证明: rfl
-/
theorem ofDigits_cons {b hd} {tl : List Nat} :
    ofDigits b (hd :: tl) = hd + b * ofDigits b tl := rfl

/--
theorem `ofDigits_append` / 定理 `ofDigits_append`

English:
theorem ofDigits_append
  given: {b : Nat} {l1 l2 : List Nat}
  proof: by
  induction l1 with
  | nil => simp [ofDigits]
  | cons hd tl IH =>
    rw [ofDigits]; rw [List.cons_append]; rw [ofDigits]; rw [IH]; rw [List.length_cons]; rw [pow_succ']
    ring

@[simp]

中文:
定理 ofDigits_append
  条件: {b : 自然数} {l1 l2 : 列表 自然数}
  证明: by
  induction l1 with
  | nil => simp [ofDigits]
  | cons hd tl IH =>
    rw [ofDigits]; rw [List.cons_append]; rw [ofDigits]; rw [IH]; rw [List.length_cons]; rw [pow_succ']
    ring

@[simp]

Depends on / 依赖: List.cons_append, List.length_cons, cons_append, length_cons, ofDigits, pow_succ
-/
theorem ofDigits_append {b : Nat} {l1 l2 : List Nat} :
    ofDigits b (l1 ++ l2) = ofDigits b l1 + b ^ l1.length * ofDigits b l2 := by
  induction l1 with
  | nil => simp [ofDigits]
  | cons hd tl IH =>
    rw [ofDigits]; rw [List.cons_append]; rw [ofDigits]; rw [IH]; rw [List.length_cons]; rw [pow_succ']
    ring

@[simp]
/--
theorem `ofDigits_append_zero` / 定理 `ofDigits_append_zero`

English:
theorem ofDigits_append_zero
  given: {b : Nat} (l : List Nat)
  proof: by
  rw [ofDigits_append]; rw [ofDigits_singleton]; rw [mul_zero]; rw [add_zero]

@[simp]

中文:
定理 ofDigits_append_zero
  条件: {b : 自然数} (l : 列表 自然数)
  证明: by
  rw [ofDigits_append]; rw [ofDigits_singleton]; rw [mul_zero]; rw [add_zero]

@[simp]

Depends on / 依赖: add_zero, mul_zero, ofDigits_append, ofDigits_singleton
-/
theorem ofDigits_append_zero {b : Nat} (l : List Nat) :
    ofDigits b (l ++ [0]) = ofDigits b l := by
  rw [ofDigits_append]; rw [ofDigits_singleton]; rw [mul_zero]; rw [add_zero]

@[simp]
/--
theorem `ofDigits_replicate_zero` / 定理 `ofDigits_replicate_zero`

English:
theorem ofDigits_replicate_zero
  given: {b k : Nat}
  statement: ofDigits b (List.replicate k 0) = 0
  proof: by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate, ofDigits_cons, ih]

@[simp]

中文:
定理 ofDigits_replicate_zero
  条件: {b k : 自然数}
  结论: ofDigits b (列表.replicate k 0) = 0
  证明: by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate, ofDigits_cons, ih]

@[simp]

Depends on / 依赖: List.replicate, ofDigits_cons, replicate
-/
theorem ofDigits_replicate_zero {b k : Nat} : ofDigits b (List.replicate k 0) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate, ofDigits_cons, ih]

@[simp]
/--
theorem `ofDigits_append_replicate_zero` / 定理 `ofDigits_append_replicate_zero`

English:
theorem ofDigits_append_replicate_zero
  given: {b k : Nat} (l : List Nat)
  proof: by
  rw [ofDigits_append]
  simp

中文:
定理 ofDigits_append_replicate_zero
  条件: {b k : 自然数} (l : 列表 自然数)
  证明: by
  rw [ofDigits_append]
  simp

Depends on / 依赖: ofDigits_append
-/
theorem ofDigits_append_replicate_zero {b k : Nat} (l : List Nat) :
    ofDigits b (l ++ List.replicate k 0) = ofDigits b l := by
  rw [ofDigits_append]
  simp

/--
theorem `ofDigits_reverse_cons` / 定理 `ofDigits_reverse_cons`

English:
theorem ofDigits_reverse_cons
  given: {b : Nat} (l : List Nat) (d : Nat)
  proof: by
  simp only [List.reverse_cons]
  rw [ofDigits_append]
  simp

中文:
定理 ofDigits_reverse_cons
  条件: {b : 自然数} (l : 列表 自然数) (d : 自然数)
  证明: by
  simp only [List.reverse_cons]
  rw [ofDigits_append]
  simp

Depends on / 依赖: List.reverse_cons, ofDigits_append, reverse_cons
-/
theorem ofDigits_reverse_cons {b : Nat} (l : List Nat) (d : Nat) :
    ofDigits b (d :: l).reverse = ofDigits b l.reverse + b ^ l.length * d := by
  simp only [List.reverse_cons]
  rw [ofDigits_append]
  simp

/--
theorem `ofDigits_reverse_zero_cons` / 定理 `ofDigits_reverse_zero_cons`

English:
theorem ofDigits_reverse_zero_cons
  given: {b : Nat} (l : List Nat)
  proof: by
  simp only [List.reverse_cons, ofDigits_append_zero]

@[norm_cast]

中文:
定理 ofDigits_reverse_zero_cons
  条件: {b : 自然数} (l : 列表 自然数)
  证明: by
  simp only [List.reverse_cons, ofDigits_append_zero]

@[norm_cast]

Depends on / 依赖: List.reverse_cons, ofDigits_append_zero, reverse_cons
-/
theorem ofDigits_reverse_zero_cons {b : Nat} (l : List Nat) :
    ofDigits b (0 :: l).reverse = ofDigits b l.reverse := by
  simp only [List.reverse_cons, ofDigits_append_zero]

@[norm_cast]
/--
theorem `coe_ofDigits` / 定理 `coe_ofDigits`

English:
theorem coe_ofDigits
  given: (α : Type*) [Semiring α] (b : Nat) (L : List Nat)
  proof: by
  induction L with
  | nil => simp [ofDigits]
  | cons d L ih => dsimp [ofDigits]; push_cast; rw [ih]

中文:
定理 coe_ofDigits
  条件: (α : 类型) [半环 α] (b : 自然数) (L : 列表 自然数)
  证明: by
  induction L with
  | nil => simp [ofDigits]
  | cons d L ih => dsimp [ofDigits]; push_cast; rw [ih]

Depends on / 依赖: ofDigits
-/
theorem coe_ofDigits (α : Type*) [Semiring α] (b : Nat) (L : List Nat) :
    ((ofDigits b L : Nat) : α) = ofDigits (b : α) L := by
  induction L with
  | nil => simp [ofDigits]
  | cons d L ih => dsimp [ofDigits]; push_cast; rw [ih]

/--
theorem `digits_zero_of_eq_zero` / 定理 `digits_zero_of_eq_zero`

English:
theorem digits_zero_of_eq_zero
  given: {b : Nat} (h : b != 0)

中文:
定理 digits_zero_of_eq_zero
  条件: {b : 自然数} (h : b != 0)
-/
theorem digits_zero_of_eq_zero {b : Nat} (h : b != 0) :
    forall {L : List Nat} (_ : ofDigits b L = 0), forall l in L, l = 0
  | _ :: _, h0, _, List.Mem.head .. => Nat.eq_zero_of_add_eq_zero_right h0
  | _ :: _, h0, _, List.Mem.tail _ hL =>
    digits_zero_of_eq_zero h (mul_right_injective₀ h (Nat.eq_zero_of_add_eq_zero_left h0)) _ hL

/--
theorem `digits_ofDigits` / 定理 `digits_ofDigits`

English:
theorem digits_ofDigits
  statement: (b : Nat) (h : 1 < b) (L : List Nat) (w₁ : forall l in L, l < b)
  proof: by
  induction L with
  | nil => simp
  | cons d L ih =>
    dsimp [ofDigits]
    replace w₂ := w₂ (by simp)
    rw [digits_add b h]
    · rw [ih]
      · intro l m
        apply w₁
        exact List.mem_cons_of_mem _ m
      · intro h
        rw [List.getLast_cons h] at w₂
        convert! w₂
    

中文:
定理 digits_ofDigits
  结论: (b : 自然数) (h : 1 < b) (L : 列表 自然数) (w₁ : 对任意 l in L, l < b)
  证明: by
  induction L with
  | nil => simp
  | cons d L ih =>
    dsimp [ofDigits]
    replace w₂ := w₂ (by simp)
    rw [digits_add b h]
    · rw [ih]
      · intro l m
        apply w₁
        exact List.mem_cons_of_mem _ m
      · intro h
        rw [List.getLast_cons h] at w₂
        convert! w₂
    

Depends on / 依赖: List.getLast_cons, List.getLast_mem, List.mem_cons_of_mem, List.mem_cons_self, contrapose, convert, digits_add, digits_zero_of_eq_zero, getLast_cons, getLast_mem, h.ne_bot, mem_cons_of_mem, mem_cons_self, ne_bot, ofDigits, replace
-/
theorem digits_ofDigits (b : Nat) (h : 1 < b) (L : List Nat) (w₁ : forall l in L, l < b)
    (w₂ : forall h : L != [], L.getLast h != 0) : digits b (ofDigits b L) = L := by
  induction L with
  | nil => simp
  | cons d L ih =>
    dsimp [ofDigits]
    replace w₂ := w₂ (by simp)
    rw [digits_add b h]
    · rw [ih]
      · intro l m
        apply w₁
        exact List.mem_cons_of_mem _ m
      · intro h
        rw [List.getLast_cons h] at w₂
        convert! w₂
    · exact w₁ d List.mem_cons_self
    · by_cases h' : L = []
      · rcases h' with rfl
        left
        simpa using w₂
      · right
        contrapose w₂
        refine digits_zero_of_eq_zero h.ne_bot w₂ _ ?_
        rw [List.getLast_cons h']
        exact List.getLast_mem h'

/--
theorem `ofDigits_digits` / 定理 `ofDigits_digits`

English:
theorem ofDigits_digits
  given: (b n : Nat)
  statement: ofDigits b (digits b n) = n
  proof: by
  rcases b with - | b
  · rcases n with - | n
    · rfl
    · simp
  · rcases b with - | b
    · induction n with
      | zero => rfl
      | succ n ih =>
        rw [Nat.zero_add] at ih ⊢
        simp only [ih, add_comm 1, ofDigits_one_cons, Nat.cast_id, digits_one_succ]
    · induction n using 

中文:
定理 ofDigits_digits
  条件: (b n : 自然数)
  结论: ofDigits b (digits b n) = n
  证明: by
  rcases b with - | b
  · rcases n with - | n
    · rfl
    · simp
  · rcases b with - | b
    · induction n with
      | zero => rfl
      | succ n ih =>
        rw [Nat.zero_add] at ih ⊢
        simp only [ih, add_comm 1, ofDigits_one_cons, Nat.cast_id, digits_one_succ]
    · induction n using 

Depends on / 依赖: Nat.cast_id, Nat.div_lt_self, Nat.mod_add_div, Nat.strongRecOn, Nat.zero_add, add_comm, cast_id, digits_add_two_add_one, digits_one_succ, digits_zero, div_lt_self, mod_add_div, ofDigits, ofDigits_one_cons, strongRecOn, zero_add
-/
theorem ofDigits_digits (b n : Nat) : ofDigits b (digits b n) = n := by
  rcases b with - | b
  · rcases n with - | n
    · rfl
    · simp
  · rcases b with - | b
    · induction n with
      | zero => rfl
      | succ n ih =>
        rw [Nat.zero_add] at ih ⊢
        simp only [ih, add_comm 1, ofDigits_one_cons, Nat.cast_id, digits_one_succ]
    · induction n using Nat.strongRecOn with | ind n h => ?_
      cases n
      · rw [digits_zero]
        rfl
      · simp only [digits_add_two_add_one]
        dsimp [ofDigits]
        rw [h _ (Nat.div_lt_self' _ b)]
        rw [Nat.mod_add_div]

/--
theorem `ofDigits_one` / 定理 `ofDigits_one`

English:
theorem ofDigits_one
  given: (L : List Nat)
  statement: ofDigits 1 L = L.sum
  proof: by
  induction L with
  | nil => rfl
  | cons _ _ ih => simp [ofDigits, List.sum_cons, ih]

中文:
定理 ofDigits_one
  条件: (L : 列表 自然数)
  结论: ofDigits 1 L = L.求和
  证明: by
  induction L with
  | nil => rfl
  | cons _ _ ih => simp [ofDigits, List.sum_cons, ih]

Depends on / 依赖: List.sum_cons, ofDigits, sum_cons
-/
theorem ofDigits_one (L : List Nat) : ofDigits 1 L = L.sum := by
  induction L with
  | nil => rfl
  | cons _ _ ih => simp [ofDigits, List.sum_cons, ih]



/--
theorem `digits_eq_nil_iff_eq_zero` / 定理 `digits_eq_nil_iff_eq_zero`

English:
theorem digits_eq_nil_iff_eq_zero
  given: {b n : Nat}
  statement: digits b n = [] ↔ n = 0
  proof: by
  constructor
  · intro h
    have : ofDigits b (digits b n) = ofDigits b [] := by rw [h]
    convert! this
    rw [ofDigits_digits]
  · rintro rfl
    simp

中文:
定理 digits_eq_nil_iff_eq_zero
  条件: {b n : 自然数}
  结论: digits b n = [] ↔ n = 0
  证明: by
  constructor
  · intro h
    have : ofDigits b (digits b n) = ofDigits b [] := by rw [h]
    convert! this
    rw [ofDigits_digits]
  · rintro rfl
    simp

Depends on / 依赖: convert, digits, ofDigits, ofDigits_digits
-/
theorem digits_eq_nil_iff_eq_zero {b n : Nat} : digits b n = [] ↔ n = 0 := by
  constructor
  · intro h
    have : ofDigits b (digits b n) = ofDigits b [] := by rw [h]
    convert! this
    rw [ofDigits_digits]
  · rintro rfl
    simp

/--
theorem `digits_ne_nil_iff_ne_zero` / 定理 `digits_ne_nil_iff_ne_zero`

English:
theorem digits_ne_nil_iff_ne_zero
  given: {b n : Nat}
  statement: digits b n != [] ↔ n != 0
  proof: not_congr digits_eq_nil_iff_eq_zero

中文:
定理 digits_ne_nil_iff_ne_zero
  条件: {b n : 自然数}
  结论: digits b n != [] ↔ n != 0
  证明: not_congr digits_eq_nil_iff_eq_zero

Depends on / 依赖: digits_eq_nil_iff_eq_zero, not_congr
-/
theorem digits_ne_nil_iff_ne_zero {b n : Nat} : digits b n != [] ↔ n != 0 :=
  not_congr digits_eq_nil_iff_eq_zero

/--
theorem `digits_eq_cons_digits_div` / 定理 `digits_eq_cons_digits_div`

English:
theorem digits_eq_cons_digits_div
  given: {b n : Nat} (h : 1 < b) (w : n != 0)
  proof: digits_def' h (Nat.pos_of_ne_zero w)

中文:
定理 digits_eq_cons_digits_div
  条件: {b n : 自然数} (h : 1 < b) (w : n != 0)
  证明: digits_def' h (Nat.pos_of_ne_zero w)

Depends on / 依赖: Nat.pos_of_ne_zero, digits_def, pos_of_ne_zero
-/
theorem digits_eq_cons_digits_div {b n : Nat} (h : 1 < b) (w : n != 0) :
    digits b n = (n % b) :: digits b (n / b) :=
  digits_def' h (Nat.pos_of_ne_zero w)

/--
theorem `digits_getLast` / 定理 `digits_getLast`

English:
theorem digits_getLast
  given: {b : Nat} (m : Nat) (h : 1 < b) (p q)
  proof: by
  by_cases hm : m = 0
  · simp [hm]
  simp only [digits_eq_cons_digits_div h hm]
  rw [List.getLast_cons]

中文:
定理 digits_getLast
  条件: {b : 自然数} (m : 自然数) (h : 1 < b) (p q)
  证明: by
  by_cases hm : m = 0
  · simp [hm]
  simp only [digits_eq_cons_digits_div h hm]
  rw [List.getLast_cons]

Depends on / 依赖: List.getLast_cons, digits_eq_cons_digits_div, getLast_cons
-/
theorem digits_getLast {b : Nat} (m : Nat) (h : 1 < b) (p q) :
    (digits b m).getLast p = (digits b (m / b)).getLast q := by
  by_cases hm : m = 0
  · simp [hm]
  simp only [digits_eq_cons_digits_div h hm]
  rw [List.getLast_cons]

/--
theorem `digits.injective` / 定理 `digits.injective`

English:
theorem digits.injective
  given: (b : Nat)
  statement: Function.Injective b.digits
  proof: Function.LeftInverse.injective (ofDigits_digits b)

@[simp]

中文:
定理 digits.injective
  条件: (b : 自然数)
  结论: 函数.单射 b.digits
  证明: Function.LeftInverse.injective (ofDigits_digits b)

@[simp]

Depends on / 依赖: Function, Function.LeftInverse.injective, LeftInverse, injective, ofDigits_digits
-/
theorem digits.injective (b : Nat) : Function.Injective b.digits :=
  Function.LeftInverse.injective (ofDigits_digits b)

@[simp]
/--
theorem `digits_inj_iff` / 定理 `digits_inj_iff`

English:
theorem digits_inj_iff
  given: {b n m : Nat}
  statement: b.digits n = b.digits m ↔ n = m
  proof: (digits.injective b).eq_iff

中文:
定理 digits_inj_iff
  条件: {b n m : 自然数}
  结论: b.digits n = b.digits m ↔ n = m
  证明: (digits.injective b).eq_iff

Depends on / 依赖: digits, digits.injective, eq_iff, injective
-/
theorem digits_inj_iff {b n m : Nat} : b.digits n = b.digits m ↔ n = m :=
  (digits.injective b).eq_iff

/--
theorem `mul_ofDigits` / 定理 `mul_ofDigits`

English:
theorem mul_ofDigits
  given: (n : Nat) {b : Nat} {l : List Nat}
  proof: by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    rw [List.map_cons]; rw [ofDigits_cons]; rw [ofDigits_cons]; rw [← ih]
    ring

中文:
定理 mul_ofDigits
  条件: (n : 自然数) {b : 自然数} {l : 列表 自然数}
  证明: by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    rw [List.map_cons]; rw [ofDigits_cons]; rw [ofDigits_cons]; rw [← ih]
    ring

Depends on / 依赖: List.map_cons, map_cons, ofDigits_cons
-/
theorem mul_ofDigits (n : Nat) {b : Nat} {l : List Nat} :
    n * ofDigits b l = ofDigits b (l.map (n * ·)) := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    rw [List.map_cons]; rw [ofDigits_cons]; rw [ofDigits_cons]; rw [← ih]
    ring

/--
lemma `ofDigits_inj_of_len_eq` / 引理 `ofDigits_inj_of_len_eq`

English:
lemma ofDigits_inj_of_len_eq
  statement: {b : Nat} (hb : 1 < b) {L1 L2 : List Nat}
  proof: by
  induction L1 generalizing L2 with
  | nil =>
    simp only [List.length_nil] at len
    exact (List.length_eq_zero_iff.mp len.symm).symm
  | cons D L ih => ?_
  obtain ⟨d, l, rfl⟩ := List.exists_cons_of_length_eq_add_one len.symm
  simp only [List.length_cons, add_left_inj] at len
  simp only [

中文:
引理 ofDigits_inj_of_len_eq
  结论: {b : 自然数} (hb : 1 < b) {L1 L2 : 列表 自然数}
  证明: by
  induction L1 generalizing L2 with
  | nil =>
    simp only [List.length_nil] at len
    exact (List.length_eq_zero_iff.mp len.symm).symm
  | cons D L ih => ?_
  obtain ⟨d, l, rfl⟩ := List.exists_cons_of_length_eq_add_one len.symm
  simp only [List.length_cons, add_left_inj] at len
  simp only [

Depends on / 依赖: List.exists_cons_of_length_eq_add_one, List.length_cons, List.length_eq_zero_iff.mp, List.length_nil, List.mem_cons_self, add_left_inj, exists_cons_of_length_eq_add_one, generalizing, len.symm, length_cons, length_eq_zero_iff, length_nil, mem_cons_self, mod_eq_of_lt, ofDigits, ofDigits_cons
-/
lemma ofDigits_inj_of_len_eq {b : Nat} (hb : 1 < b) {L1 L2 : List Nat}
    (len : L1.length = L2.length) (w1 : forall l in L1, l < b) (w2 : forall l in L2, l < b)
    (h : ofDigits b L1 = ofDigits b L2) : L1 = L2 := by
  induction L1 generalizing L2 with
  | nil =>
    simp only [List.length_nil] at len
    exact (List.length_eq_zero_iff.mp len.symm).symm
  | cons D L ih => ?_
  obtain ⟨d, l, rfl⟩ := List.exists_cons_of_length_eq_add_one len.symm
  simp only [List.length_cons, add_left_inj] at len
  simp only [ofDigits_cons] at h
  have eqd : D = d := by
    have H : (D + b * ofDigits b L) % b = (d + b * ofDigits b l) % b := by rw [h]
    simpa [mod_eq_of_lt (w2 d List.mem_cons_self),
      mod_eq_of_lt (w1 D List.mem_cons_self)] using H
  simp only [eqd, add_right_inj, mul_left_cancel_iff_of_pos (zero_lt_of_lt hb)] at h
  have := ih len (fun a ha => w1 a <| List.mem_cons_of_mem D ha)
    (fun a ha => w2 a <| List.mem_cons_of_mem d ha) h
  rw [eqd]; rw [this]

/--
theorem `ofDigits_add_ofDigits_eq_ofDigits_zipWith_of_length_eq` / 定理 `ofDigits_add_ofDigits_eq_ofDigits_zipWith_of_length_eq`

English:
theorem ofDigits_add_ofDigits_eq_ofDigits_zipWith_of_length_eq
  statement: {b : Nat} {l1 l2 : List Nat}
  proof: by
  induction l1 generalizing l2 with
  | nil => simp_all [eq_comm, List.length_eq_zero_iff, ofDigits]
  | cons hd₁ tl₁ ih₁ =>
    induction l2 generalizing tl₁ with
    | nil => simp_all
    | cons hd₂ tl₂ ih₂ =>
      simp_all only [List.length_cons, ofDigits_cons, add_left_inj,
        eq_comm, 

中文:
定理 ofDigits_add_ofDigits_eq_ofDigits_zipWith_of_length_eq
  结论: {b : 自然数} {l1 l2 : 列表 自然数}
  证明: by
  induction l1 generalizing l2 with
  | nil => simp_all [eq_comm, List.length_eq_zero_iff, ofDigits]
  | cons hd₁ tl₁ ih₁ =>
    induction l2 generalizing tl₁ with
    | nil => simp_all
    | cons hd₂ tl₂ ih₂ =>
      simp_all only [List.length_cons, ofDigits_cons, add_left_inj,
        eq_comm, 

Depends on / 依赖: List.length_cons, List.length_eq_zero_iff, List.zipWith_cons_cons, add_left_inj, eq_comm, generalizing, h.symm, length_cons, length_eq_zero_iff, mul_add, ofDigits, ofDigits_cons, zipWith_cons_cons
-/
theorem ofDigits_add_ofDigits_eq_ofDigits_zipWith_of_length_eq {b : Nat} {l1 l2 : List Nat}
    (h : l1.length = l2.length) :
    ofDigits b l1 + ofDigits b l2 = ofDigits b (l1.zipWith (· + ·) l2) := by
  induction l1 generalizing l2 with
  | nil => simp_all [eq_comm, List.length_eq_zero_iff, ofDigits]
  | cons hd₁ tl₁ ih₁ =>
    induction l2 generalizing tl₁ with
    | nil => simp_all
    | cons hd₂ tl₂ ih₂ =>
      simp_all only [List.length_cons, ofDigits_cons, add_left_inj,
        eq_comm, List.zipWith_cons_cons]
      rw [← ih₁ h.symm]; rw [mul_add]
      ac_rfl

/--
theorem `digits_lt_base'` / 定理 `digits_lt_base'`

English:
theorem digits_lt_base'
  given: {b m : Nat}
  statement: forall {d}, d in digits (b + 2) m -> d < b + 2
  proof: by
  induction m using Nat.strongRecOn with | ind n IH => ?_
  intro d hd
  rcases n with - | n
  · rw [digits_zero] at hd
    cases hd
  -- base b+2 expansion of 0 has no digits
  rw [digits_add_two_add_one] at hd
  cases hd
  · exact n.succ.mod_lt (by linarith)
  · apply IH ((n + 1) / (b + 2))
   

中文:
定理 digits_lt_base'
  条件: {b m : 自然数}
  结论: 对任意 {d}, d in digits (b + 2) m -> d < b + 2
  证明: by
  induction m using Nat.strongRecOn with | ind n IH => ?_
  intro d hd
  rcases n with - | n
  · rw [digits_zero] at hd
    cases hd
  -- base b+2 expansion of 0 has no digits
  rw [digits_add_two_add_one] at hd
  cases hd
  · exact n.succ.mod_lt (by linarith)
  · apply IH ((n + 1) / (b + 2))
   

Depends on / 依赖: Nat.strongRecOn, digits_zero, strongRecOn
-/
theorem digits_lt_base' {b m : Nat} : forall {d}, d in digits (b + 2) m -> d < b + 2 := by
  induction m using Nat.strongRecOn with | ind n IH => ?_
  intro d hd
  rcases n with - | n
  · rw [digits_zero] at hd
    cases hd
  -- base b+2 expansion of 0 has no digits
  rw [digits_add_two_add_one] at hd
  cases hd
  · exact n.succ.mod_lt (by linarith)
  · apply IH ((n + 1) / (b + 2))
    · apply Nat.div_lt_self <;> lia
    · assumption

/--
theorem `digits_lt_base` / 定理 `digits_lt_base`

English:
theorem digits_lt_base
  given: {b m d : Nat} (hb : 1 < b) (hd : d in digits b m)
  statement: d < b
  proof: by
  rcases b with (_ | _ | b) <;> simp_all [@digits_lt_base' _ m d]

中文:
定理 digits_lt_base
  条件: {b m d : 自然数} (hb : 1 < b) (hd : d in digits b m)
  结论: d < b
  证明: by
  rcases b with (_ | _ | b) <;> simp_all [@digits_lt_base' _ m d]

Depends on / 依赖: digits_lt_base
-/
theorem digits_lt_base {b m d : Nat} (hb : 1 < b) (hd : d in digits b m) : d < b := by
  rcases b with (_ | _ | b) <;> simp_all [@digits_lt_base' _ m d]

/--
theorem `ofDigits_lt_base_pow_length'` / 定理 `ofDigits_lt_base_pow_length'`

English:
theorem ofDigits_lt_base_pow_length'
  given: {b : Nat} {l : List Nat} (hl : forall x in l, x < b + 2)
  proof: by
  induction l with
  | nil => simp [ofDigits]
  | cons hd tl IH =>
    rw [ofDigits]; rw [List.length_cons]; rw [pow_succ]
    have : (ofDigits (b + 2) tl + 1) * (b + 2) <= (b + 2) ^ tl.length * (b + 2) :=
      mul_le_mul (IH fun x hx => hl _ (List.mem_cons_of_mem _ hx)) (by rfl) (by simp only [

中文:
定理 ofDigits_lt_base_pow_length'
  条件: {b : 自然数} {l : 列表 自然数} (hl : 对任意 x in l, x < b + 2)
  证明: by
  induction l with
  | nil => simp [ofDigits]
  | cons hd tl IH =>
    rw [ofDigits]; rw [List.length_cons]; rw [pow_succ]
    have : (ofDigits (b + 2) tl + 1) * (b + 2) <= (b + 2) ^ tl.length * (b + 2) :=
      mul_le_mul (IH fun x hx => hl _ (List.mem_cons_of_mem _ hx)) (by rfl) (by simp only [

Depends on / 依赖: List.length_cons, List.mem_cons_of_mem, List.mem_cons_self, Nat.zero_le, length, length_cons, mem_cons_of_mem, mem_cons_self, mul_le_mul, ofDigits, pow_succ, tl.length, zero_le
-/
theorem ofDigits_lt_base_pow_length' {b : Nat} {l : List Nat} (hl : forall x in l, x < b + 2) :
    ofDigits (b + 2) l < (b + 2) ^ l.length := by
  induction l with
  | nil => simp [ofDigits]
  | cons hd tl IH =>
    rw [ofDigits]; rw [List.length_cons]; rw [pow_succ]
    have : (ofDigits (b + 2) tl + 1) * (b + 2) <= (b + 2) ^ tl.length * (b + 2) :=
      mul_le_mul (IH fun x hx => hl _ (List.mem_cons_of_mem _ hx)) (by rfl) (by simp only [zero_le])
        (Nat.zero_le _)
    suffices ↑hd < b + 2 by linarith
    exact hl hd List.mem_cons_self

/--
theorem `ofDigits_lt_base_pow_length` / 定理 `ofDigits_lt_base_pow_length`

English:
theorem ofDigits_lt_base_pow_length
  given: {b : Nat} {l : List Nat} (hb : 1 < b) (hl : forall x in l, x < b)
  proof: by
  rcases b with (_ | _ | b) <;> simp_all [ofDigits_lt_base_pow_length']

中文:
定理 ofDigits_lt_base_pow_length
  条件: {b : 自然数} {l : 列表 自然数} (hb : 1 < b) (hl : 对任意 x in l, x < b)
  证明: by
  rcases b with (_ | _ | b) <;> simp_all [ofDigits_lt_base_pow_length']

Depends on / 依赖: ofDigits_lt_base_pow_length
-/
theorem ofDigits_lt_base_pow_length {b : Nat} {l : List Nat} (hb : 1 < b) (hl : forall x in l, x < b) :
    ofDigits b l < b ^ l.length := by
  rcases b with (_ | _ | b) <;> simp_all [ofDigits_lt_base_pow_length']

/--
theorem `lt_base_pow_length_digits'` / 定理 `lt_base_pow_length_digits'`

English:
theorem lt_base_pow_length_digits'
  given: {b m : Nat}
  statement: m < (b + 2) ^ (digits (b + 2) m).length
  proof: by
  convert! @ofDigits_lt_base_pow_length' b (digits (b + 2) m) fun _ => digits_lt_base'
  rw [ofDigits_digits (b + 2) m]

中文:
定理 lt_base_pow_length_digits'
  条件: {b m : 自然数}
  结论: m < (b + 2) ^ (digits (b + 2) m).length
  证明: by
  convert! @ofDigits_lt_base_pow_length' b (digits (b + 2) m) fun _ => digits_lt_base'
  rw [ofDigits_digits (b + 2) m]

Depends on / 依赖: convert, digits, digits_lt_base, ofDigits_digits, ofDigits_lt_base_pow_length
-/
theorem lt_base_pow_length_digits' {b m : Nat} : m < (b + 2) ^ (digits (b + 2) m).length := by
  convert! @ofDigits_lt_base_pow_length' b (digits (b + 2) m) fun _ => digits_lt_base'
  rw [ofDigits_digits (b + 2) m]

/--
theorem `lt_base_pow_length_digits` / 定理 `lt_base_pow_length_digits`

English:
theorem lt_base_pow_length_digits
  given: {b m : Nat} (hb : 1 < b)
  statement: m < b ^ (digits b m).length
  proof: by
  rcases b with (_ | _ | b) <;> simp_all [lt_base_pow_length_digits']

中文:
定理 lt_base_pow_length_digits
  条件: {b m : 自然数} (hb : 1 < b)
  结论: m < b ^ (digits b m).length
  证明: by
  rcases b with (_ | _ | b) <;> simp_all [lt_base_pow_length_digits']

Depends on / 依赖: lt_base_pow_length_digits
-/
theorem lt_base_pow_length_digits {b m : Nat} (hb : 1 < b) : m < b ^ (digits b m).length := by
  rcases b with (_ | _ | b) <;> simp_all [lt_base_pow_length_digits']

/--
theorem `digits_base_mul` / 定理 `digits_base_mul`

English:
theorem digits_base_mul
  given: {b m : Nat} (hb : 1 < b) (hm : 0 < m)
  proof: by
  rw [digits_def' hb (by positivity)]
  simp [mul_div_right m (by positivity)]

中文:
定理 digits_base_mul
  条件: {b m : 自然数} (hb : 1 < b) (hm : 0 < m)
  证明: by
  rw [digits_def' hb (by positivity)]
  simp [mul_div_right m (by positivity)]

Depends on / 依赖: digits_def, mul_div_right
-/
theorem digits_base_mul {b m : Nat} (hb : 1 < b) (hm : 0 < m) :
    b.digits (b * m) = 0 :: b.digits m := by
  rw [digits_def' hb (by positivity)]
  simp [mul_div_right m (by positivity)]

/--
theorem `digits_base_pow_mul` / 定理 `digits_base_pow_mul`

English:
theorem digits_base_pow_mul
  given: {b k m : Nat} (hb : 1 < b) (hm : 0 < m)
  proof: by
  induction k generalizing m with
  | zero => simp
  | succ k ih =>
    rw [pow_succ']; rw [mul_assoc]; rw [digits_base_mul hb (by positivity)]; rw [ih hm]; rw [List.replicate_succ]; rw [List.cons_append]

中文:
定理 digits_base_pow_mul
  条件: {b k m : 自然数} (hb : 1 < b) (hm : 0 < m)
  证明: by
  induction k generalizing m with
  | zero => simp
  | succ k ih =>
    rw [pow_succ']; rw [mul_assoc]; rw [digits_base_mul hb (by positivity)]; rw [ih hm]; rw [List.replicate_succ]; rw [List.cons_append]

Depends on / 依赖: List.cons_append, List.replicate_succ, cons_append, digits_base_mul, generalizing, mul_assoc, pow_succ, replicate_succ
-/
theorem digits_base_pow_mul {b k m : Nat} (hb : 1 < b) (hm : 0 < m) :
    digits b (b ^ k * m) = List.replicate k 0 ++ digits b m := by
  induction k generalizing m with
  | zero => simp
  | succ k ih =>
    rw [pow_succ']; rw [mul_assoc]; rw [digits_base_mul hb (by positivity)]; rw [ih hm]; rw [List.replicate_succ]; rw [List.cons_append]

/--
theorem `ofDigits_digits_append_digits` / 定理 `ofDigits_digits_append_digits`

English:
theorem ofDigits_digits_append_digits
  given: {b m n : Nat}
  proof: by
  rw [ofDigits_append]; rw [ofDigits_digits]; rw [ofDigits_digits]

@[gcongr, mono]

中文:
定理 ofDigits_digits_append_digits
  条件: {b m n : 自然数}
  证明: by
  rw [ofDigits_append]; rw [ofDigits_digits]; rw [ofDigits_digits]

@[gcongr, mono]

Depends on / 依赖: ofDigits_append, ofDigits_digits
-/
theorem ofDigits_digits_append_digits {b m n : Nat} :
    ofDigits b (digits b n ++ digits b m) = n + b ^ (digits b n).length * m := by
  rw [ofDigits_append]; rw [ofDigits_digits]; rw [ofDigits_digits]

@[gcongr, mono]
/--
theorem `ofDigits_monotone` / 定理 `ofDigits_monotone`

English:
theorem ofDigits_monotone
  given: {p q : Nat} (L : List Nat) (h : p <= q)
  statement: ofDigits p L <= ofDigits q L
  proof: by
  induction L with
  | nil => rfl
  | cons _ _ hi =>
    simp only [ofDigits, cast_id, add_le_add_iff_left]
    exact Nat.mul_le_mul h hi

中文:
定理 ofDigits_monotone
  条件: {p q : 自然数} (L : 列表 自然数) (h : p <= q)
  结论: ofDigits p L <= ofDigits q L
  证明: by
  induction L with
  | nil => rfl
  | cons _ _ hi =>
    simp only [ofDigits, cast_id, add_le_add_iff_left]
    exact Nat.mul_le_mul h hi

Depends on / 依赖: Nat.mul_le_mul, add_le_add_iff_left, cast_id, mul_le_mul, ofDigits
-/
theorem ofDigits_monotone {p q : Nat} (L : List Nat) (h : p <= q) : ofDigits p L <= ofDigits q L := by
  induction L with
  | nil => rfl
  | cons _ _ hi =>
    simp only [ofDigits, cast_id, add_le_add_iff_left]
    exact Nat.mul_le_mul h hi

/--
theorem `sum_le_ofDigits` / 定理 `sum_le_ofDigits`

English:
theorem sum_le_ofDigits
  given: {p : Nat} (L : List Nat) (h : 1 <= p)
  statement: L.sum <= ofDigits p L
  proof: (ofDigits_one L).symm ▸ ofDigits_monotone L h

中文:
定理 sum_le_ofDigits
  条件: {p : 自然数} (L : 列表 自然数) (h : 1 <= p)
  结论: L.求和 <= ofDigits p L
  证明: (ofDigits_one L).symm ▸ ofDigits_monotone L h

Depends on / 依赖: ofDigits_monotone, ofDigits_one
-/
theorem sum_le_ofDigits {p : Nat} (L : List Nat) (h : 1 <= p) : L.sum <= ofDigits p L :=
  (ofDigits_one L).symm ▸ ofDigits_monotone L h

/--
theorem `digit_sum_le` / 定理 `digit_sum_le`

English:
theorem digit_sum_le
  given: (p n : Nat)
  statement: List.sum (digits p n) <= n
  proof: by
  induction n with
  | zero => exact digits_zero _ ▸ Nat.le_refl (List.sum [])
  | succ n =>
    induction p with
    | zero => rw [digits_zero_succ, List.sum_cons, List.sum_nil, add_zero]
    | succ p =>
      nth_rw 2 [← ofDigits_digits p.succ (n + 1)]
      rw [← ofDigits_one <| digits p.succ 

中文:
定理 digit_sum_le
  条件: (p n : 自然数)
  结论: 列表.求和 (digits p n) <= n
  证明: by
  induction n with
  | zero => exact digits_zero _ ▸ Nat.le_refl (List.sum [])
  | succ n =>
    induction p with
    | zero => rw [digits_zero_succ, List.sum_cons, List.sum_nil, add_zero]
    | succ p =>
      nth_rw 2 [← ofDigits_digits p.succ (n + 1)]
      rw [← ofDigits_one <| digits p.succ 

Depends on / 依赖: List.sum, List.sum_cons, List.sum_nil, Nat.le_refl, Nat.succ_pos, add_zero, digits, digits_zero, digits_zero_succ, le_refl, n.succ, nth_rw, ofDigits_digits, ofDigits_monotone, ofDigits_one, p.succ, succ_pos, sum_cons, sum_nil
-/
theorem digit_sum_le (p n : Nat) : List.sum (digits p n) <= n := by
  induction n with
  | zero => exact digits_zero _ ▸ Nat.le_refl (List.sum [])
  | succ n =>
    induction p with
    | zero => rw [digits_zero_succ, List.sum_cons, List.sum_nil, add_zero]
    | succ p =>
      nth_rw 2 [← ofDigits_digits p.succ (n + 1)]
      rw [← ofDigits_one <| digits p.succ n.succ]
exact ofDigits_monotone (digits p.succ n.succ) Nat.succ_pos p

/--
lemma `ofDigits_div_eq_ofDigits_tail` / 引理 `ofDigits_div_eq_ofDigits_tail`

English:
lemma ofDigits_div_eq_ofDigits_tail
  statement: {p : Nat} (hpos : 0 < p) (digits : List Nat)
  proof: by
  induction digits with
  | nil => simp [ofDigits]
  | cons hd tl =>
    refine Eq.trans (add_mul_div_left hd _ hpos) ?_
    rw [Nat.div_eq_of_lt <| w₁ _ List.mem_cons_self]; rw [zero_add]; rw [List.tail_cons]

中文:
引理 ofDigits_div_eq_ofDigits_tail
  结论: {p : 自然数} (hpos : 0 < p) (digits : 列表 自然数)
  证明: by
  induction digits with
  | nil => simp [ofDigits]
  | cons hd tl =>
    refine Eq.trans (add_mul_div_left hd _ hpos) ?_
    rw [Nat.div_eq_of_lt <| w₁ _ List.mem_cons_self]; rw [zero_add]; rw [List.tail_cons]

Depends on / 依赖: Eq.trans, List.mem_cons_self, List.tail_cons, Nat.div_eq_of_lt, add_mul_div_left, digits, div_eq_of_lt, mem_cons_self, ofDigits, tail_cons, zero_add
-/
lemma ofDigits_div_eq_ofDigits_tail {p : Nat} (hpos : 0 < p) (digits : List Nat)
    (w₁ : forall l in digits, l < p) : ofDigits p digits / p = ofDigits p digits.tail := by
  induction digits with
  | nil => simp [ofDigits]
  | cons hd tl =>
    refine Eq.trans (add_mul_div_left hd _ hpos) ?_
    rw [Nat.div_eq_of_lt <| w₁ _ List.mem_cons_self]; rw [zero_add]; rw [List.tail_cons]

/--
lemma `ofDigits_div_pow_eq_ofDigits_drop` / 引理 `ofDigits_div_pow_eq_ofDigits_drop`

English:
lemma ofDigits_div_pow_eq_ofDigits_drop
  proof: by
  induction i with
  | zero => simp
  | succ i hi =>
    rw [Nat.pow_succ]; rw [← Nat.div_div_eq_div_mul]; rw [hi]; rw [ofDigits_div_eq_ofDigits_tail hpos
(List.drop i digits) fun x hx => w₁ x List.mem_of_mem_drop hx]; rw [← List.drop_one]; rw [List.drop_drop]; rw [add_comm]

中文:
引理 ofDigits_div_pow_eq_ofDigits_drop
  证明: by
  induction i with
  | zero => simp
  | succ i hi =>
    rw [Nat.pow_succ]; rw [← Nat.div_div_eq_div_mul]; rw [hi]; rw [ofDigits_div_eq_ofDigits_tail hpos
(List.drop i digits) fun x hx => w₁ x List.mem_of_mem_drop hx]; rw [← List.drop_one]; rw [List.drop_drop]; rw [add_comm]

Depends on / 依赖: List.drop, List.drop_drop, List.drop_one, List.mem_of_mem_drop, Nat.div_div_eq_div_mul, Nat.pow_succ, add_comm, digits, div_div_eq_div_mul, drop_drop, drop_one, mem_of_mem_drop, ofDigits_div_eq_ofDigits_tail, pow_succ
-/
lemma ofDigits_div_pow_eq_ofDigits_drop
    {p : Nat} (i : Nat) (hpos : 0 < p) (digits : List Nat) (w₁ : forall l in digits, l < p) :
    ofDigits p digits / p ^ i = ofDigits p (digits.drop i) := by
  induction i with
  | zero => simp
  | succ i hi =>
    rw [Nat.pow_succ]; rw [← Nat.div_div_eq_div_mul]; rw [hi]; rw [ofDigits_div_eq_ofDigits_tail hpos
(List.drop i digits) fun x hx => w₁ x List.mem_of_mem_drop hx]; rw [← List.drop_one]; rw [List.drop_drop]; rw [add_comm]

/--
lemma `self_div_pow_eq_ofDigits_drop` / 引理 `self_div_pow_eq_ofDigits_drop`

English:
lemma self_div_pow_eq_ofDigits_drop
  given: {p : Nat} (i n : Nat) (h : 2 <= p)
  proof: by
  convert!
    ofDigits_div_pow_eq_ofDigits_drop i (zero_lt_of_lt h) (p.digits n)
      (fun l hl => digits_lt_base h hl)
  exact (ofDigits_digits p n).symm

中文:
引理 self_div_pow_eq_ofDigits_drop
  条件: {p : 自然数} (i n : 自然数) (h : 2 <= p)
  证明: by
  convert!
    ofDigits_div_pow_eq_ofDigits_drop i (zero_lt_of_lt h) (p.digits n)
      (fun l hl => digits_lt_base h hl)
  exact (ofDigits_digits p n).symm

Depends on / 依赖: convert, digits, digits_lt_base, ofDigits_digits, ofDigits_div_pow_eq_ofDigits_drop, p.digits, zero_lt_of_lt
-/
lemma self_div_pow_eq_ofDigits_drop {p : Nat} (i n : Nat) (h : 2 <= p) :
    n / p ^ i = ofDigits p ((p.digits n).drop i) := by
  convert!
    ofDigits_div_pow_eq_ofDigits_drop i (zero_lt_of_lt h) (p.digits n)
      (fun l hl => digits_lt_base h hl)
  exact (ofDigits_digits p n).symm

/--
lemma `ofDigits_mod_pow_eq_ofDigits_take` / 引理 `ofDigits_mod_pow_eq_ofDigits_take`

English:
lemma ofDigits_mod_pow_eq_ofDigits_take
  proof: by
  induction i generalizing digits with
  | zero => simp [mod_one]
  | succ i ih =>
    cases digits with
    | nil => simp
    | cons hd tl =>
      rw [List.take_succ_cons]; rw [ofDigits_cons]; rw [ofDigits_cons]; rw [← ih _ fun x hx => w₁ x List.mem_cons_of_mem hd hx]; rw [add_mod]; rw [mod_eq_

中文:
引理 ofDigits_mod_pow_eq_ofDigits_take
  证明: by
  induction i generalizing digits with
  | zero => simp [mod_one]
  | succ i ih =>
    cases digits with
    | nil => simp
    | cons hd tl =>
      rw [List.take_succ_cons]; rw [ofDigits_cons]; rw [ofDigits_cons]; rw [← ih _ fun x hx => w₁ x List.mem_cons_of_mem hd hx]; rw [add_mod]; rw [mod_eq_

Depends on / 依赖: List.mem_cons_of_mem, List.mem_cons_self, List.take_succ_cons, add_lt_of_lt_sub, add_mod, add_one_pos, digits, generalizing, le_pow, lt_of_lt_of_le, mem_cons_of_mem, mem_cons_self, mod_eq_of_lt, mod_one, mul_mod_mul_left, ofDigits_cons, pow_succ, take_succ_cons
-/
lemma ofDigits_mod_pow_eq_ofDigits_take
    {p : Nat} (i : Nat) (hpos : 0 < p) (digits : List Nat) (w₁ : forall l in digits, l < p) :
    ofDigits p digits % p ^ i = ofDigits p (digits.take i) := by
  induction i generalizing digits with
  | zero => simp [mod_one]
  | succ i ih =>
    cases digits with
    | nil => simp
    | cons hd tl =>
      rw [List.take_succ_cons]; rw [ofDigits_cons]; rw [ofDigits_cons]; rw [← ih _ fun x hx => w₁ x List.mem_cons_of_mem hd hx]; rw [add_mod]; rw [mod_eq_of_lt lt_of_lt_of_le (w₁ hd List.mem_cons_self) (le_pow <| add_one_pos i)]; rw [pow_succ']; rw [mul_mod_mul_left]; rw [mod_eq_of_lt]
      apply add_lt_of_lt_sub
      apply lt_of_lt_of_le (b := p)
      · exact w₁ hd List.mem_cons_self
      · rw [← Nat.mul_sub]
exact Nat.le_mul_of_pos_right _ Nat.sub_pos_of_lt mod_lt _ pow_pos hpos i

/--
lemma `self_mod_pow_eq_ofDigits_take` / 引理 `self_mod_pow_eq_ofDigits_take`

English:
lemma self_mod_pow_eq_ofDigits_take
  given: {p : Nat} (i n : Nat) (h : 2 <= p)
  proof: by
  convert!
    ofDigits_mod_pow_eq_ofDigits_take i (zero_lt_of_lt h) (p.digits n)
      (fun l hl => digits_lt_base h hl)
  exact (ofDigits_digits p n).symm

中文:
引理 self_mod_pow_eq_ofDigits_take
  条件: {p : 自然数} (i n : 自然数) (h : 2 <= p)
  证明: by
  convert!
    ofDigits_mod_pow_eq_ofDigits_take i (zero_lt_of_lt h) (p.digits n)
      (fun l hl => digits_lt_base h hl)
  exact (ofDigits_digits p n).symm

Depends on / 依赖: convert, digits, digits_lt_base, ofDigits_digits, ofDigits_mod_pow_eq_ofDigits_take, p.digits, zero_lt_of_lt
-/
lemma self_mod_pow_eq_ofDigits_take {p : Nat} (i n : Nat) (h : 2 <= p) :
    n % p ^ i = ofDigits p ((p.digits n).take i) := by
  convert!
    ofDigits_mod_pow_eq_ofDigits_take i (zero_lt_of_lt h) (p.digits n)
      (fun l hl => digits_lt_base h hl)
  exact (ofDigits_digits p n).symm


/--
lemma `toDigitsCore_lens_eq_aux` / 引理 `toDigitsCore_lens_eq_aux`

English:
lemma toDigitsCore_lens_eq_aux
  given: (b f : Nat)
  proof: by
  induction f with (simp only [Nat.toDigitsCore]; intro n l1 l2 hlen)
  | zero => assumption
  | succ f ih =>
    if hx : n / b = 0 then
      simp only [hx, if_true, List.length, congrArg (fun l => l + 1) hlen]
    else
      simp only [hx, if_false]
      specialize ih (n / b) (Nat.digitChar (n

中文:
引理 toDigitsCore_lens_eq_aux
  条件: (b f : 自然数)
  证明: by
  induction f with (simp only [Nat.toDigitsCore]; intro n l1 l2 hlen)
  | zero => assumption
  | succ f ih =>
    if hx : n / b = 0 then
      simp only [hx, if_true, List.length, congrArg (fun l => l + 1) hlen]
    else
      simp only [hx, if_false]
      specialize ih (n / b) (Nat.digitChar (n

Depends on / 依赖: List.length, Nat.digitChar, Nat.toDigitsCore, digitChar, if_false, if_true, length, specialize, toDigitsCore
-/
lemma toDigitsCore_lens_eq_aux (b f : Nat) :
    forall (n : Nat) (l1 l2 : List Char), l1.length = l2.length ->
    (Nat.toDigitsCore b f n l1).length = (Nat.toDigitsCore b f n l2).length := by
  induction f with (simp only [Nat.toDigitsCore]; intro n l1 l2 hlen)
  | zero => assumption
  | succ f ih =>
    if hx : n / b = 0 then
      simp only [hx, if_true, List.length, congrArg (fun l => l + 1) hlen]
    else
      simp only [hx, if_false]
      specialize ih (n / b) (Nat.digitChar (n % b) :: l1) (Nat.digitChar (n % b) :: l2)
      simp only [List.length, congrArg (fun l => l + 1) hlen] at ih
      exact ih trivial

/--
lemma `toDigitsCore_lens_eq` / 引理 `toDigitsCore_lens_eq`

English:
lemma toDigitsCore_lens_eq
  given: (b f : Nat)
  statement: forall (n : Nat) (c : Char) (tl : List Char),
  proof: by
  induction f with (intro n c tl; simp only [Nat.toDigitsCore, List.length])
  | succ f ih =>
    grind

中文:
引理 toDigitsCore_lens_eq
  条件: (b f : 自然数)
  结论: 对任意 (n : 自然数) (c : Char) (tl : 列表 Char),
  证明: by
  induction f with (intro n c tl; simp only [Nat.toDigitsCore, List.length])
  | succ f ih =>
    grind

Depends on / 依赖: List.length, Nat.toDigitsCore, length, toDigitsCore
-/
lemma toDigitsCore_lens_eq (b f : Nat) : forall (n : Nat) (c : Char) (tl : List Char),
    (Nat.toDigitsCore b f n (c :: tl)).length = (Nat.toDigitsCore b f n tl).length + 1 := by
  induction f with (intro n c tl; simp only [Nat.toDigitsCore, List.length])
  | succ f ih =>
    grind

/--
lemma `nat_repr_len_aux` / 引理 `nat_repr_len_aux`

English:
lemma nat_repr_len_aux
  given: (n b e : Nat) (h_b_pos : 0 < b)
  statement: n < b ^ e.succ -> n / b < b ^ e
  proof: by
  simp only [Nat.pow_succ]
  exact (@Nat.div_lt_iff_lt_mul b n (b ^ e) h_b_pos).mpr

中文:
引理 nat_repr_len_aux
  条件: (n b e : 自然数) (h_b_pos : 0 < b)
  结论: n < b ^ e.succ -> n / b < b ^ e
  证明: by
  simp only [Nat.pow_succ]
  exact (@Nat.div_lt_iff_lt_mul b n (b ^ e) h_b_pos).mpr

Depends on / 依赖: Nat.div_lt_iff_lt_mul, Nat.pow_succ, div_lt_iff_lt_mul, h_b_pos, pow_succ
-/
lemma nat_repr_len_aux (n b e : Nat) (h_b_pos : 0 < b) : n < b ^ e.succ -> n / b < b ^ e := by
  simp only [Nat.pow_succ]
  exact (@Nat.div_lt_iff_lt_mul b n (b ^ e) h_b_pos).mpr

/--
lemma `toDigitsCore_length` / 引理 `toDigitsCore_length`

English:
lemma toDigitsCore_length
  given: (b f n e : Nat) (h_e_pos : 0 < e) (hlt : n < b ^ e)
  proof: by
  induction f generalizing n e hlt h_e_pos with
  | zero => simp only [toDigitsCore, List.length, zero_le]
  | succ f ih =>
    simp only [toDigitsCore]
    cases e with
    | zero => exact False.elim (Nat.lt_irrefl 0 h_e_pos)
    | succ e =>
      cases e with
      | zero =>
        rw [zero_ad

中文:
引理 toDigitsCore_length
  条件: (b f n e : 自然数) (h_e_pos : 0 < e) (hlt : n < b ^ e)
  证明: by
  induction f generalizing n e hlt h_e_pos with
  | zero => simp only [toDigitsCore, List.length, zero_le]
  | succ f ih =>
    simp only [toDigitsCore]
    cases e with
    | zero => exact False.elim (Nat.lt_irrefl 0 h_e_pos)
    | succ e =>
      cases e with
      | zero =>
        rw [zero_ad

Depends on / 依赖: False.elim, List.length, Nat.digitChar, Nat.div_eq_of_lt, Nat.div_lt_of_lt_mul, Nat.lt_irrefl, add_one_pos, digitChar, div_eq_of_lt, div_lt_of_lt_mul, generalizing, h_e_pos, length, lt_irrefl, pow_add_one, pow_one, specialize, split_ifs, toDigitsCore, toDigitsCore_lens_eq
-/
lemma toDigitsCore_length (b f n e : Nat) (h_e_pos : 0 < e) (hlt : n < b ^ e) :
    (Nat.toDigitsCore b f n []).length <= e := by
  induction f generalizing n e hlt h_e_pos with
  | zero => simp only [toDigitsCore, List.length, zero_le]
  | succ f ih =>
    simp only [toDigitsCore]
    cases e with
    | zero => exact False.elim (Nat.lt_irrefl 0 h_e_pos)
    | succ e =>
      cases e with
      | zero =>
        rw [zero_add]; rw [pow_one] at hlt
        simp [Nat.div_eq_of_lt hlt]
      | succ e =>
        specialize ih (n / b) _ (add_one_pos e) (Nat.div_lt_of_lt_mul <| by rwa [← pow_add_one'])
        split_ifs
        · simp
        · simp only [toDigitsCore_lens_eq b f (n / b) (Nat.digitChar <| n % b),
            Nat.succ_le_succ_iff, ih]

/--
lemma `toDigits_length` / 引理 `toDigits_length`

English:
lemma toDigits_length
  given: (b n e : Nat)
  statement: 0 < e -> n < b ^ e -> (Nat.toDigits b n).length <= e
  proof: toDigitsCore_length _ _ _ _

中文:
引理 toDigits_length
  条件: (b n e : 自然数)
  结论: 0 < e -> n < b ^ e -> (自然数.toDigits b n).length <= e
  证明: toDigitsCore_length _ _ _ _

Depends on / 依赖: toDigitsCore_length
-/
lemma toDigits_length (b n e : Nat) : 0 < e -> n < b ^ e -> (Nat.toDigits b n).length <= e :=
  toDigitsCore_length _ _ _ _

/--
lemma `repr_length` / 引理 `repr_length`

English:
lemma repr_length
  given: (n e : Nat)
  statement: 0 < e -> n < 10 ^ e -> (Nat.repr n).length <= e
  proof: by
  simpa [Nat.repr] using toDigits_length _ _ _

中文:
引理 repr_length
  条件: (n e : 自然数)
  结论: 0 < e -> n < 10 ^ e -> (自然数.repr n).length <= e
  证明: by
  simpa [Nat.repr] using toDigits_length _ _ _

Depends on / 依赖: Nat.repr, toDigits_length
-/
lemma repr_length (n e : Nat) : 0 < e -> n < 10 ^ e -> (Nat.repr n).length <= e := by
  simpa [Nat.repr] using toDigits_length _ _ _

end Nat
