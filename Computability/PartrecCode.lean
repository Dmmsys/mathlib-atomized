/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Computability.Partrec
public import Mathlib.Data.Option.Basic

/-!
# Gödel Numbering for Partial Recursive Functions.

This file defines `Nat.Partrec.Code`, an inductive datatype describing code for partial
recursive functions on ℕ. It defines an encoding for these codes, and proves that the constructors
are primitive recursive with respect to the encoding.

It also defines the evaluation of these codes as partial functions using `PFun`, and proves that a
function is partially recursive (as defined by `Nat.Partrec`) if and only if it is the evaluation
of some code.

## Main Definitions

* `Nat.Partrec.Code`: Inductive datatype for partial recursive codes.
* `Nat.Partrec.Code.encodeCode`: A (computable) encoding of codes as natural numbers.
* `Nat.Partrec.Code.ofNatCode`: The inverse of this encoding.
* `Nat.Partrec.Code.eval`: The interpretation of a `Nat.Partrec.Code` as a partial function.

## Main Results

* `Nat.Partrec.Code.primrec_recOn`: Recursion on `Nat.Partrec.Code` is primitive recursive.
* `Nat.Partrec.Code.computable_recOn`: Recursion on `Nat.Partrec.Code` is computable.
* `Nat.Partrec.Code.smn`: The $S_n^m$ theorem.
* `Nat.Partrec.Code.exists_code`: Partial recursiveness is equivalent to being the eval of a code.
* `Nat.Partrec.Code.primrec_evaln`: `evaln` is primitive recursive.
* `Nat.Partrec.Code.fixed_point`: Roger's fixed point theorem.
* `Nat.Partrec.Code.fixed_point₂`: Kleene's second recursion theorem.

## References

* [Mario Carneiro, *Formalizing computability theory via partial recursive functions*][carneiro2019]

-/

@[expose] public section

open Encodable Denumerable

namespace Nat.Partrec

/--
theorem `rfind'` / 定理 `rfind'`

English:
theorem rfind'
  given: {f} (hf : Nat.Partrec f)
  proof: Partrec₂.unpaired'.2 by
    refine
      Partrec.map
        ((@Partrec₂.unpaired' fun a b : Nat =>
Nat.rfind fun n => (fun m => m = 0) < > f (Nat.pair a (n + b))).1
          ?_)
        (Primrec.nat_add.comp Primrec.snd <| Primrec.snd.comp Primrec.fst).to_comp.to₂
    have : Nat.Partrec (fun a => 

中文:
定理 rfind'
  条件: {f} (hf : 自然数.Partrec f)
  证明: Partrec₂.unpaired'.2 by
    refine
      Partrec.map
        ((@Partrec₂.unpaired' fun a b : Nat =>
Nat.rfind fun n => (fun m => m = 0) < > f (Nat.pair a (n + b))).1
          ?_)
        (Primrec.nat_add.comp Primrec.snd <| Primrec.snd.comp Primrec.fst).to_comp.to₂
    have : Nat.Partrec (fun a => 

Depends on / 依赖: Nat.Partrec, Nat.pair, Nat.rfind, Nat.unpair, Nat.unpaired, Partrec, Partrec.map, Partrec.nat_iff, Pi.lex_le_iff_of_unique, Primrec, Primrec.fst, Primrec.fst.c, Primrec.nat_add.comp, Primrec.snd, Primrec.snd.comp, lex_le_iff_of_unique, nat_add, nat_iff, pair.comp, to_comp
-/
theorem rfind' {f} (hf : Nat.Partrec f) :
    Nat.Partrec
      (Nat.unpaired fun a m =>
        (Nat.rfind fun n => (fun m => m = 0) <$> f (Nat.pair a (n + m))).map (· + m)) :=
Partrec₂.unpaired'.2 by
    refine
      Partrec.map
        ((@Partrec₂.unpaired' fun a b : Nat =>
Nat.rfind fun n => (fun m => m = 0) < > f (Nat.pair a (n + b))).1
          ?_)
        (Primrec.nat_add.comp Primrec.snd <| Primrec.snd.comp Primrec.fst).to_comp.to₂
    have : Nat.Partrec (fun a => Nat.rfind (fun n => (fun m => decide (m = 0)) <$>
      Nat.unpaired (fun a b => f (Nat.pair (Nat.unpair a).1 (b + (Nat.unpair a).2)))
        (Nat.pair a n))) :=
      rfind
        (Partrec₂.unpaired'.2
          ((Partrec.nat_iff.2 hf).comp
              (Primrec₂.pair.comp (Primrec.fst.comp <| Primrec.unpair.comp Primrec.fst)
                  (Primrec.nat_add.comp Primrec.snd
                    (Primrec.snd.comp <| Primrec.unpair.comp Primrec.fst))).to_comp))
    simpa

/--
Inductive type `Code` / 归纳类型 `Code`

English:
inductive Code
  parameters: : Type
  constructors (8):
    - zero: Code
    - succ: Code
    - left: Code
    - right: Code
    - pair: Code -> Code -> Code
    - comp: Code -> Code -> Code
    - prec: Code -> Code -> Code
    - rfind': Code -> Code

中文:
归纳类型 Code
  参数: : Type
  构造子 (8 个):
    - zero: Code
    - succ: Code
    - left: Code
    - right: Code
    - pair: Code -> Code -> Code
    - comp: Code -> Code -> Code
    - prec: Code -> Code -> Code
    - rfind': Code -> Code

Depends on / 依赖: Lex.le_iff_of_unique, le_iff_of_unique
-/
inductive Code : Type
  | zero : Code
  | succ : Code
  | left : Code
  | right : Code
  | pair : Code -> Code -> Code
  | comp : Code -> Code -> Code
  | prec : Code -> Code -> Code
  | rfind' : Code -> Code

compile_inductive% Code

end Nat.Partrec

namespace Nat.Partrec.Code

/--
Instance `instInhabited` / 实例 `instInhabited`

English:
instance instInhabited
  signature: : Inhabited Code
  body: ⟨zero⟩

中文:
实例 instInhabited
  签名: : Inhabited Code
  定义体: ⟨zero⟩
-/
instance instInhabited : Inhabited Code :=
  ⟨zero⟩

/--
Definition of `const` / `const` 的定义

English:
definition const
  signature: : Nat -> Code

中文:
定义 const
  签名: : 自然数 -> Code
-/
protected def const : Nat -> Code
  | 0 => zero
  | n + 1 => comp succ (Code.const n)

/--
theorem `const_inj` / 定理 `const_inj`

English:
theorem const_inj
  statement: forall {n₁ n₂}, Nat.Partrec.Code.const n₁ = Nat.Partrec.Code.const n₂ -> n₁ = n₂

中文:
定理 const_inj
  结论: 对任意 {n₁ n₂}, 自然数.Partrec.Code.const n₁ = 自然数.Partrec.Code.const n₂ -> n₁ = n₂
-/
theorem const_inj : forall {n₁ n₂}, Nat.Partrec.Code.const n₁ = Nat.Partrec.Code.const n₂ -> n₁ = n₂
  | 0, 0, _ => by simp
  | n₁ + 1, n₂ + 1, h => by
    dsimp [Nat.Partrec.Code.const] at h
    injection h with h₁ h₂
    simp only [const_inj h₂]

/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : Code
  body: pair left right

中文:
定义 id
  签名: : Code
  定义体: pair left right
-/
protected def id : Code :=
  pair left right

/--
Definition of `curry` / `curry` 的定义

English:
definition curry
  signature: (c : Code) (n : Nat)
  body: comp c (pair (Code.const n) Code.id)

中文:
定义 curry
  签名: (c : Code) (n : 自然数)
  定义体: comp c (pair (Code.const n) Code.id)

Depends on / 依赖: Code.const, Code.id
-/
def curry (c : Code) (n : Nat) : Code :=
  comp c (pair (Code.const n) Code.id)

/--
Definition of `encodeCode` / `encodeCode` 的定义

English:
definition encodeCode
  signature: : Code -> Nat

中文:
定义 encodeCode
  签名: : Code -> 自然数
-/
def encodeCode : Code -> Nat
  | zero => 0
  | succ => 1
  | left => 2
  | right => 3
  | pair cf cg => 2 * (2 * Nat.pair (encodeCode cf) (encodeCode cg)) + 4
  | comp cf cg => 2 * (2 * Nat.pair (encodeCode cf) (encodeCode cg) + 1) + 4
  | prec cf cg => (2 * (2 * Nat.pair (encodeCode cf) (encodeCode cg)) + 1) + 4
  | rfind' cf => (2 * (2 * encodeCode cf + 1) + 1) + 4

/--
Definition of `ofNatCode` / `ofNatCode` 的定义

English:
definition ofNatCode
  signature: : Nat -> Code
  body: n.div2.div2
    have hm : m < n + 4 := by
      simp only [m, div2_val]
      exact
        lt_of_le_of_lt (le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _))
          (Nat.succ_le_succ (Nat.le_add_right _ _))
    have _m1 : m.unpair.1 < n + 4 := lt_of_le_of_lt m.unpair_left_le hm
    have _m2 :

中文:
定义 ofNatCode
  签名: : 自然数 -> Code
  定义体: n.div2.div2
    have hm : m < n + 4 := by
      simp only [m, div2_val]
      exact
        lt_of_le_of_lt (le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _))
          (Nat.succ_le_succ (Nat.le_add_right _ _))
    have _m1 : m.unpair.1 < n + 4 := lt_of_le_of_lt m.unpair_left_le hm
    have _m2 :

Depends on / 依赖: n.div2.div2
-/
def ofNatCode : Nat -> Code
  | 0 => zero
  | 1 => succ
  | 2 => left
  | 3 => right
  | n + 4 =>
    let m := n.div2.div2
    have hm : m < n + 4 := by
      simp only [m, div2_val]
      exact
        lt_of_le_of_lt (le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _))
          (Nat.succ_le_succ (Nat.le_add_right _ _))
    have _m1 : m.unpair.1 < n + 4 := lt_of_le_of_lt m.unpair_left_le hm
    have _m2 : m.unpair.2 < n + 4 := lt_of_le_of_lt m.unpair_right_le hm
    match n.bodd, n.div2.bodd with
    | false, false => pair (ofNatCode m.unpair.1) (ofNatCode m.unpair.2)
    | false, true => comp (ofNatCode m.unpair.1) (ofNatCode m.unpair.2)
    | true, false => prec (ofNatCode m.unpair.1) (ofNatCode m.unpair.2)
    | true, true => rfind' (ofNatCode m)

set_option backward.privateInPublic true in
/--
theorem `encode_ofNatCode` / 定理 `encode_ofNatCode`

English:
theorem encode_ofNatCode
  statement: forall n, encodeCode (ofNatCode n) = n
  proof: n.div2.div2
    have hm : m < n + 4 := by
      simp only [m, div2_val]
      exact
        lt_of_le_of_lt (le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _))
          (Nat.succ_le_succ (Nat.le_add_right _ _))
    have _m1 : m.unpair.1 < n + 4 := lt_of_le_of_lt m.unpair_left_le hm
    have _m2 :

中文:
定理 encode_ofNatCode
  结论: 对任意 n, encodeCode (of自然数Code n) = n
  证明: n.div2.div2
    have hm : m < n + 4 := by
      simp only [m, div2_val]
      exact
        lt_of_le_of_lt (le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _))
          (Nat.succ_le_succ (Nat.le_add_right _ _))
    have _m1 : m.unpair.1 < n + 4 := lt_of_le_of_lt m.unpair_left_le hm
    have _m2 :
-/
private theorem encode_ofNatCode : forall n, encodeCode (ofNatCode n) = n
  | 0 => by simp [ofNatCode, encodeCode]
  | 1 => by simp [ofNatCode, encodeCode]
  | 2 => by simp [ofNatCode, encodeCode]
  | 3 => by simp [ofNatCode, encodeCode]
  | n + 4 => by
    let m := n.div2.div2
    have hm : m < n + 4 := by
      simp only [m, div2_val]
      exact
        lt_of_le_of_lt (le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _))
          (Nat.succ_le_succ (Nat.le_add_right _ _))
    have _m1 : m.unpair.1 < n + 4 := lt_of_le_of_lt m.unpair_left_le hm
    have _m2 : m.unpair.2 < n + 4 := lt_of_le_of_lt m.unpair_right_le hm
    have IH := encode_ofNatCode m
    have IH1 := encode_ofNatCode m.unpair.1
    have IH2 := encode_ofNatCode m.unpair.2
    conv_rhs => rw [← Nat.bit_bodd_div2 n, ← Nat.bit_bodd_div2 n.div2]
    simp only [ofNatCode.eq_5]
    cases n.bodd <;> cases n.div2.bodd <;>
      simp [m, encodeCode, IH, IH1, IH2, Nat.bit_val]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `instDenumerable` / 实例 `instDenumerable`

English:
instance instDenumerable
  signature: : Denumerable Code
  body: mk'
    ⟨encodeCode, ofNatCode, fun c => by
        induction c <;> simp [encodeCode, ofNatCode, Nat.div2_val, *],
      encode_ofNatCode⟩

中文:
实例 instDenumerable
  签名: : Denumerable Code
  定义体: mk'
    ⟨encodeCode, ofNatCode, fun c => by
        induction c <;> simp [encodeCode, ofNatCode, Nat.div2_val, *],
      encode_ofNatCode⟩

Depends on / 依赖: Nat.div2_val, add_lt_add_right, congr_arg, div2_val, encodeCode, encode_ofNatCode, ofNatCode
-/
instance instDenumerable : Denumerable Code :=
  mk'
    ⟨encodeCode, ofNatCode, fun c => by
        induction c <;> simp [encodeCode, ofNatCode, Nat.div2_val, *],
      encode_ofNatCode⟩

/--
theorem `encodeCode_eq` / 定理 `encodeCode_eq`

English:
theorem encodeCode_eq
  statement: encode = encodeCode
  proof: rfl

中文:
定理 encodeCode_eq
  结论: encode = encodeCode
  证明: rfl

Depends on / 依赖: Lex.addLeftStrictMono, addLeftStrictMono
-/
theorem encodeCode_eq : encode = encodeCode :=
  rfl

/--
theorem `ofNatCode_eq` / 定理 `ofNatCode_eq`

English:
theorem ofNatCode_eq
  statement: ofNat Code = ofNatCode
  proof: rfl

中文:
定理 ofNatCode_eq
  结论: of自然数 Code = of自然数Code
  证明: rfl

Depends on / 依赖: addLeftMono_of_addLeftStrictMono
-/
theorem ofNatCode_eq : ofNat Code = ofNatCode :=
  rfl

/--
theorem `encode_lt_pair` / 定理 `encode_lt_pair`

English:
theorem encode_lt_pair
  given: (cf cg)
  proof: by
  simp only [encodeCode_eq, encodeCode]
  have := Nat.mul_le_mul_right (Nat.pair cf.encodeCode cg.encodeCode) (by decide : 1 <= 2 * 2)
  rw [one_mul]; rw [mul_assoc] at this
  have := lt_of_le_of_lt this (lt_add_of_pos_right _ (by decide : 0 < 4))
  exact ⟨lt_of_le_of_lt (Nat.left_le_pair _ _) th

中文:
定理 encode_lt_pair
  条件: (cf cg)
  证明: by
  simp only [encodeCode_eq, encodeCode]
  have := Nat.mul_le_mul_right (Nat.pair cf.encodeCode cg.encodeCode) (by decide : 1 <= 2 * 2)
  rw [one_mul]; rw [mul_assoc] at this
  have := lt_of_le_of_lt this (lt_add_of_pos_right _ (by decide : 0 < 4))
  exact ⟨lt_of_le_of_lt (Nat.left_le_pair _ _) th

Depends on / 依赖: Nat.left_le_pair, Nat.mul_le_mul_right, Nat.pair, Nat.right_le_pair, addLeftMono_of_addLeftStrictMono, cf.encodeCode, cg.encodeCode, encodeCode, encodeCode_eq, left_le_pair, lt_add_of_pos_right, lt_of_le_of_lt, mul_assoc, mul_le_mul_right, one_mul, right_le_pair
-/
theorem encode_lt_pair (cf cg) :
    encode cf < encode (pair cf cg) ∧ encode cg < encode (pair cf cg) := by
  simp only [encodeCode_eq, encodeCode]
  have := Nat.mul_le_mul_right (Nat.pair cf.encodeCode cg.encodeCode) (by decide : 1 <= 2 * 2)
  rw [one_mul]; rw [mul_assoc] at this
  have := lt_of_le_of_lt this (lt_add_of_pos_right _ (by decide : 0 < 4))
  exact ⟨lt_of_le_of_lt (Nat.left_le_pair _ _) this, lt_of_le_of_lt (Nat.right_le_pair _ _) this⟩

/--
theorem `encode_lt_comp` / 定理 `encode_lt_comp`

English:
theorem encode_lt_comp
  given: (cf cg)
  proof: by
  have : encode (pair cf cg) < encode (comp cf cg) := by simp [encodeCode_eq, encodeCode]
  exact (encode_lt_pair cf cg).imp (fun h => lt_trans h this) fun h => lt_trans h this

中文:
定理 encode_lt_comp
  条件: (cf cg)
  证明: by
  have : encode (pair cf cg) < encode (comp cf cg) := by simp [encodeCode_eq, encodeCode]
  exact (encode_lt_pair cf cg).imp (fun h => lt_trans h this) fun h => lt_trans h this

Depends on / 依赖: add_lt_add_left, encode, encodeCode, encodeCode_eq, encode_lt_pair, lt_trans
-/
theorem encode_lt_comp (cf cg) :
    encode cf < encode (comp cf cg) ∧ encode cg < encode (comp cf cg) := by
  have : encode (pair cf cg) < encode (comp cf cg) := by simp [encodeCode_eq, encodeCode]
  exact (encode_lt_pair cf cg).imp (fun h => lt_trans h this) fun h => lt_trans h this

/--
theorem `encode_lt_prec` / 定理 `encode_lt_prec`

English:
theorem encode_lt_prec
  given: (cf cg)
  proof: by
  have : encode (pair cf cg) < encode (prec cf cg) := by simp [encodeCode_eq, encodeCode]
  exact (encode_lt_pair cf cg).imp (fun h => lt_trans h this) fun h => lt_trans h this

中文:
定理 encode_lt_prec
  条件: (cf cg)
  证明: by
  have : encode (pair cf cg) < encode (prec cf cg) := by simp [encodeCode_eq, encodeCode]
  exact (encode_lt_pair cf cg).imp (fun h => lt_trans h this) fun h => lt_trans h this

Depends on / 依赖: Lex.addRightStrictMono, addRightStrictMono, encode, encodeCode, encodeCode_eq, encode_lt_pair, lt_trans
-/
theorem encode_lt_prec (cf cg) :
    encode cf < encode (prec cf cg) ∧ encode cg < encode (prec cf cg) := by
  have : encode (pair cf cg) < encode (prec cf cg) := by simp [encodeCode_eq, encodeCode]
  exact (encode_lt_pair cf cg).imp (fun h => lt_trans h this) fun h => lt_trans h this

/--
theorem `encode_lt_rfind'` / 定理 `encode_lt_rfind'`

English:
theorem encode_lt_rfind'
  given: (cf)
  statement: encode cf < encode (rfind' cf)
  proof: by
  simp only [encodeCode_eq, encodeCode]
  lia

中文:
定理 encode_lt_rfind'
  条件: (cf)
  结论: encode cf < encode (rfind' cf)
  证明: by
  simp only [encodeCode_eq, encodeCode]
  lia

Depends on / 依赖: addRightMono_of_addRightStrictMono, encodeCode, encodeCode_eq
-/
theorem encode_lt_rfind' (cf) : encode cf < encode (rfind' cf) := by
  simp only [encodeCode_eq, encodeCode]
  lia

end Nat.Partrec.Code

section
open Primrec
namespace Nat.Partrec.Code

/--
theorem `primrec₂_pair` / 定理 `primrec₂_pair`

English:
theorem primrec₂_pair
  statement: Primrec₂ pair
  proof: Primrec₂.ofNat_iff.2
Primrec₂.encode_iff.1
      nat_add.comp
        (nat_double.comp <|
nat_double.comp
            Primrec₂.natPair.comp (encode_iff.2 <| (Primrec.ofNat Code).comp fst)
              (encode_iff.2 <| (Primrec.ofNat Code).comp snd))
        (Primrec₂.const 4)

中文:
定理 primrec₂_pair
  结论: Primrec₂ pair
  证明: Primrec₂.ofNat_iff.2
Primrec₂.encode_iff.1
      nat_add.comp
        (nat_double.comp <|
nat_double.comp
            Primrec₂.natPair.comp (encode_iff.2 <| (Primrec.ofNat Code).comp fst)
              (encode_iff.2 <| (Primrec.ofNat Code).comp snd))
        (Primrec₂.const 4)

Depends on / 依赖: Primrec, Primrec.ofNat, addRightMono_of_addRightStrictMono, encode_iff, natPair, natPair.comp, nat_add, nat_add.comp, nat_double, nat_double.comp, ofNat_iff
-/
theorem primrec₂_pair : Primrec₂ pair :=
Primrec₂.ofNat_iff.2
Primrec₂.encode_iff.1
      nat_add.comp
        (nat_double.comp <|
nat_double.comp
            Primrec₂.natPair.comp (encode_iff.2 <| (Primrec.ofNat Code).comp fst)
              (encode_iff.2 <| (Primrec.ofNat Code).comp snd))
        (Primrec₂.const 4)

/--
theorem `primrec₂_comp` / 定理 `primrec₂_comp`

English:
theorem primrec₂_comp
  statement: Primrec₂ comp
  proof: Primrec₂.ofNat_iff.2
Primrec₂.encode_iff.1
      nat_add.comp
        (nat_double.comp <|
nat_double_succ.comp
            Primrec₂.natPair.comp (encode_iff.2 <| (Primrec.ofNat Code).comp fst)
              (encode_iff.2 <| (Primrec.ofNat Code).comp snd))
        (Primrec₂.const 4)

中文:
定理 primrec₂_comp
  结论: Primrec₂ comp
  证明: Primrec₂.ofNat_iff.2
Primrec₂.encode_iff.1
      nat_add.comp
        (nat_double.comp <|
nat_double_succ.comp
            Primrec₂.natPair.comp (encode_iff.2 <| (Primrec.ofNat Code).comp fst)
              (encode_iff.2 <| (Primrec.ofNat Code).comp snd))
        (Primrec₂.const 4)

Depends on / 依赖: Primrec, Primrec.ofNat, encode_iff, natPair, natPair.comp, nat_add, nat_add.comp, nat_double, nat_double.comp, nat_double_succ, nat_double_succ.comp, ofNat_iff
-/
theorem primrec₂_comp : Primrec₂ comp :=
Primrec₂.ofNat_iff.2
Primrec₂.encode_iff.1
      nat_add.comp
        (nat_double.comp <|
nat_double_succ.comp
            Primrec₂.natPair.comp (encode_iff.2 <| (Primrec.ofNat Code).comp fst)
              (encode_iff.2 <| (Primrec.ofNat Code).comp snd))
        (Primrec₂.const 4)

/--
theorem `primrec₂_prec` / 定理 `primrec₂_prec`

English:
theorem primrec₂_prec
  statement: Primrec₂ prec
  proof: Primrec₂.ofNat_iff.2
Primrec₂.encode_iff.1
      nat_add.comp
        (nat_double_succ.comp <|
nat_double.comp
            Primrec₂.natPair.comp (encode_iff.2 <| (Primrec.ofNat Code).comp fst)
              (encode_iff.2 <| (Primrec.ofNat Code).comp snd))
        (Primrec₂.const 4)

中文:
定理 primrec₂_prec
  结论: Primrec₂ prec
  证明: Primrec₂.ofNat_iff.2
Primrec₂.encode_iff.1
      nat_add.comp
        (nat_double_succ.comp <|
nat_double.comp
            Primrec₂.natPair.comp (encode_iff.2 <| (Primrec.ofNat Code).comp fst)
              (encode_iff.2 <| (Primrec.ofNat Code).comp snd))
        (Primrec₂.const 4)

Depends on / 依赖: Primrec, Primrec.ofNat, encode_iff, isBot_bot, natPair, natPair.comp, nat_add, nat_add.comp, nat_double, nat_double.comp, nat_double_succ, nat_double_succ.comp, ofNat_iff
-/
theorem primrec₂_prec : Primrec₂ prec :=
Primrec₂.ofNat_iff.2
Primrec₂.encode_iff.1
      nat_add.comp
        (nat_double_succ.comp <|
nat_double.comp
            Primrec₂.natPair.comp (encode_iff.2 <| (Primrec.ofNat Code).comp fst)
              (encode_iff.2 <| (Primrec.ofNat Code).comp snd))
        (Primrec₂.const 4)

/--
theorem `primrec_rfind'` / 定理 `primrec_rfind'`

English:
theorem primrec_rfind'
  statement: Primrec rfind'
  proof: ofNat_iff.2
encode_iff.1
      nat_add.comp
        (nat_double_succ.comp <| nat_double_succ.comp <|
encode_iff.2 Primrec.ofNat Code)
        (const 4)

中文:
定理 primrec_rfind'
  结论: Primrec rfind'
  证明: ofNat_iff.2
encode_iff.1
      nat_add.comp
        (nat_double_succ.comp <| nat_double_succ.comp <|
encode_iff.2 Primrec.ofNat Code)
        (const 4)

Depends on / 依赖: Primrec, Primrec.ofNat, encode_iff, nat_add, nat_add.comp, nat_double_succ, nat_double_succ.comp, ofNat_iff
-/
theorem primrec_rfind' : Primrec rfind' :=
ofNat_iff.2
encode_iff.1
      nat_add.comp
        (nat_double_succ.comp <| nat_double_succ.comp <|
encode_iff.2 Primrec.ofNat Code)
        (const 4)

set_option linter.flexible false in -- TODO: revisit this after #13791 is merged
/--
theorem `primrec_recOn'` / 定理 `primrec_recOn'`

English:
theorem primrec_recOn'
  statement: {α σ}
  proof: pr a (cf, cg, hf, hg)
    let CO (a) cf cg hf hg := co a (cf, cg, hf, hg)
    let PC (a) cf cg hf hg := pc a (cf, cg, hf, hg)
    let RF (a) cf hf := rf a (cf, hf)
    let F (a : α) (c : Code) : σ :=
      Nat.Partrec.Code.recOn c (z a) (s a) (l a) (r a) (PR a) (CO a) (PC a) (RF a)
    Primrec (fun 

中文:
定理 primrec_recOn'
  结论: {α σ}
  证明: pr a (cf, cg, hf, hg)
    let CO (a) cf cg hf hg := co a (cf, cg, hf, hg)
    let PC (a) cf cg hf hg := pc a (cf, cg, hf, hg)
    let RF (a) cf hf := rf a (cf, hf)
    let F (a : α) (c : Code) : σ :=
      Nat.Partrec.Code.recOn c (z a) (s a) (l a) (r a) (PR a) (CO a) (PC a) (RF a)
    Primrec (fun 

Depends on / 依赖: isBot_bot
-/
theorem primrec_recOn' {α σ}
    [Primcodable α] [Primcodable σ] {c : α -> Code} (hc : Primrec c) {z : α -> σ}
    (hz : Primrec z) {s : α -> σ} (hs : Primrec s) {l : α -> σ} (hl : Primrec l) {r : α -> σ}
    (hr : Primrec r) {pr : α -> Code × Code × σ × σ -> σ} (hpr : Primrec₂ pr)
    {co : α -> Code × Code × σ × σ -> σ} (hco : Primrec₂ co) {pc : α -> Code × Code × σ × σ -> σ}
    (hpc : Primrec₂ pc) {rf : α -> Code × σ -> σ} (hrf : Primrec₂ rf) :
    let PR (a) cf cg hf hg := pr a (cf, cg, hf, hg)
    let CO (a) cf cg hf hg := co a (cf, cg, hf, hg)
    let PC (a) cf cg hf hg := pc a (cf, cg, hf, hg)
    let RF (a) cf hf := rf a (cf, hf)
    let F (a : α) (c : Code) : σ :=
      Nat.Partrec.Code.recOn c (z a) (s a) (l a) (r a) (PR a) (CO a) (PC a) (RF a)
    Primrec (fun a => F a (c a) : α -> σ) := by
  intro _ _ _ _ F
  let G₁ : (α × List σ) × Nat × Nat -> Option σ := fun p =>
    letI a := p.1.1; letI IH := p.1.2; letI n := p.2.1; letI m := p.2.2
    IH[m]?.bind fun s =>
    IH[m.unpair.1]?.bind fun s₁ =>
    IH[m.unpair.2]?.map fun s₂ =>
    cond n.bodd
      (cond n.div2.bodd (rf a (ofNat Code m, s))
        (pc a (ofNat Code m.unpair.1, ofNat Code m.unpair.2, s₁, s₂)))
      (cond n.div2.bodd (co a (ofNat Code m.unpair.1, ofNat Code m.unpair.2, s₁, s₂))
        (pr a (ofNat Code m.unpair.1, ofNat Code m.unpair.2, s₁, s₂)))
  have : Primrec G₁ :=
option_bind (list_getElem?.comp (snd.comp fst) (snd.comp snd)) .mk
    option_bind ((list_getElem?.comp (snd.comp fst)
      (fst.comp <| Primrec.unpair.comp (snd.comp snd))).comp fst) <| .mk <|
    option_map ((list_getElem?.comp (snd.comp fst)
      (snd.comp <| Primrec.unpair.comp (snd.comp snd))).comp <| fst.comp fst) <| .mk <|
    have a := fst.comp (fst.comp <| fst.comp <| fst.comp fst)
    have n := fst.comp (snd.comp <| fst.comp <| fst.comp fst)
    have m := snd.comp (snd.comp <| fst.comp <| fst.comp fst)
    have m₁ := fst.comp (Primrec.unpair.comp m)
    have m₂ := snd.comp (Primrec.unpair.comp m)
    have s := snd.comp (fst.comp fst)
    have s₁ := snd.comp fst
    have s₂ := snd
    (nat_bodd.comp n).cond
      ((nat_bodd.comp <| nat_div2.comp n).cond
        (hrf.comp a (((Primrec.ofNat Code).comp m).pair s))
        (hpc.comp a (((Primrec.ofNat Code).comp m₁).pair <|
((Primrec.ofNat Code).comp m₂).pair s₁.pair s₂)))
      (Primrec.cond (nat_bodd.comp <| nat_div2.comp n)
        (hco.comp a (((Primrec.ofNat Code).comp m₁).pair <|
((Primrec.ofNat Code).comp m₂).pair s₁.pair s₂))
        (hpr.comp a (((Primrec.ofNat Code).comp m₁).pair <|
((Primrec.ofNat Code).comp m₂).pair s₁.pair s₂)))
  let G : α -> List σ -> Option σ := fun a IH =>
    IH.length.casesOn (some (z a)) fun n =>
    n.casesOn (some (s a)) fun n =>
    n.casesOn (some (l a)) fun n =>
    n.casesOn (some (r a)) fun n =>
    G₁ ((a, IH), n, n.div2.div2)
have : Primrec₂ G := .mk
nat_casesOn (list_length.comp snd) (option_some_iff.2 (hz.comp fst)) .mk
nat_casesOn snd (option_some_iff.2 (hs.comp (fst.comp fst))) .mk
nat_casesOn snd (option_some_iff.2 (hl.comp (fst.comp <| fst.comp fst))) .mk
nat_casesOn snd (option_some_iff.2 (hr.comp (fst.comp <| fst.comp <| fst.comp fst))) .mk
this.comp
((fst.pair snd).comp <| fst.comp <| fst.comp <| fst.comp <| fst).pair
snd.pair nat_div2.comp nat_div2.comp snd
  refine (nat_strong_rec (fun a n => F a (ofNat Code n)) this.to₂ fun a n => ?_)
.of_eq fun a => by simp .comp .id (encode_iff.2 hc)
  iterate 4 rcases n with - | n; · simp [ofNatCode_eq, ofNatCode]; rfl
  simp only [G]; rw [List.length_map, List.length_range]
  let m := n.div2.div2
  change G₁ ((a, (List.range (n + 4)).map fun n => F a (ofNat Code n)), n, m)
    = some (F a (ofNat Code (n + 4)))
  have hm : m < n + 4 := by
    simp only [m, div2_val]
    exact lt_of_le_of_lt
      (le_trans (Nat.div_le_self ..) (Nat.div_le_self ..))
      (Nat.succ_le_succ (Nat.le_add_right ..))
  have m1 : m.unpair.1 < n + 4 := lt_of_le_of_lt m.unpair_left_le hm
  have m2 : m.unpair.2 < n + 4 := lt_of_le_of_lt m.unpair_right_le hm
  simp [G₁, m, hm, m1, m2]
  rw [show ofNat Code (n + 4) = ofNatCode (n + 4) from rfl]
  simp [ofNatCode]
  cases n.bodd <;> cases n.div2.bodd <;> rfl

/--
theorem `primrec_recOn` / 定理 `primrec_recOn`

English:
theorem primrec_recOn
  statement: {α σ}
  proof: Nat.Partrec.Code.recOn c (z a) (s a) (l a) (r a) (pr a) (co a) (pc a) (rf a)
    Primrec fun a => F a (c a) :=
  primrec_recOn' hc hz hs hl hr
    (pr := fun a b => pr a b.1 b.2.1 b.2.2.1 b.2.2.2) (.mk hpr)
    (co := fun a b => co a b.1 b.2.1 b.2.2.1 b.2.2.2) (.mk hco)
    (pc := fun a b => pc a b.

中文:
定理 primrec_recOn
  结论: {α σ}
  证明: Nat.Partrec.Code.recOn c (z a) (s a) (l a) (r a) (pr a) (co a) (pc a) (rf a)
    Primrec fun a => F a (c a) :=
  primrec_recOn' hc hz hs hl hr
    (pr := fun a b => pr a b.1 b.2.1 b.2.2.1 b.2.2.2) (.mk hpr)
    (co := fun a b => co a b.1 b.2.1 b.2.2.1 b.2.2.2) (.mk hco)
    (pc := fun a b => pc a b.

Depends on / 依赖: Nat.Partrec.Code.recOn, Partrec, Primrec, add_le_add_left, primrec_recOn
-/
theorem primrec_recOn {α σ}
    [Primcodable α] [Primcodable σ] {c : α -> Code} (hc : Primrec c) {z : α -> σ}
    (hz : Primrec z) {s : α -> σ} (hs : Primrec s) {l : α -> σ} (hl : Primrec l) {r : α -> σ}
    (hr : Primrec r) {pr : α -> Code -> Code -> σ -> σ -> σ}
    (hpr : Primrec fun a : α × Code × Code × σ × σ => pr a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2)
    {co : α -> Code -> Code -> σ -> σ -> σ}
    (hco : Primrec fun a : α × Code × Code × σ × σ => co a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2)
    {pc : α -> Code -> Code -> σ -> σ -> σ}
    (hpc : Primrec fun a : α × Code × Code × σ × σ => pc a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2)
    {rf : α -> Code -> σ -> σ} (hrf : Primrec fun a : α × Code × σ => rf a.1 a.2.1 a.2.2) :
    let F (a : α) (c : Code) : σ :=
      Nat.Partrec.Code.recOn c (z a) (s a) (l a) (r a) (pr a) (co a) (pc a) (rf a)
    Primrec fun a => F a (c a) :=
  primrec_recOn' hc hz hs hl hr
    (pr := fun a b => pr a b.1 b.2.1 b.2.2.1 b.2.2.2) (.mk hpr)
    (co := fun a b => co a b.1 b.2.1 b.2.2.1 b.2.2.2) (.mk hco)
    (pc := fun a b => pc a b.1 b.2.1 b.2.2.1 b.2.2.2) (.mk hpc)
    (rf := fun a b => rf a b.1 b.2) (.mk hrf)

end Nat.Partrec.Code
end

namespace Nat.Partrec.Code
section

open Computable

set_option linter.flexible false in -- TODO: revisit this after #13791 is merged
/--
theorem `computable_recOn` / 定理 `computable_recOn`

English:
theorem computable_recOn
  statement: {α σ} [Primcodable α] [Primcodable σ] {c : α -> Code} (hc : Computable c)
  proof: pr a (cf, cg, hf, hg)
    let CO (a) cf cg hf hg := co a (cf, cg, hf, hg)
    let PC (a) cf cg hf hg := pc a (cf, cg, hf, hg)
    let RF (a) cf hf := rf a (cf, hf)
    let F (a : α) (c : Code) : σ :=
      Nat.Partrec.Code.recOn c (z a) (s a) (l a) (r a) (PR a) (CO a) (PC a) (RF a)
    Computable fu

中文:
定理 computable_recOn
  结论: {α σ} [Primcodable α] [Primcodable σ] {c : α -> Code} (hc : Computable c)
  证明: pr a (cf, cg, hf, hg)
    let CO (a) cf cg hf hg := co a (cf, cg, hf, hg)
    let PC (a) cf cg hf hg := pc a (cf, cg, hf, hg)
    let RF (a) cf hf := rf a (cf, hf)
    let F (a : α) (c : Code) : σ :=
      Nat.Partrec.Code.recOn c (z a) (s a) (l a) (r a) (PR a) (CO a) (PC a) (RF a)
    Computable fu

Depends on / 依赖: Lex.isOrderedCancelAddMonoid, isOrderedCancelAddMonoid
-/
theorem computable_recOn {α σ} [Primcodable α] [Primcodable σ] {c : α -> Code} (hc : Computable c)
    {z : α -> σ} (hz : Computable z) {s : α -> σ} (hs : Computable s) {l : α -> σ} (hl : Computable l)
    {r : α -> σ} (hr : Computable r) {pr : α -> Code × Code × σ × σ -> σ} (hpr : Computable₂ pr)
    {co : α -> Code × Code × σ × σ -> σ} (hco : Computable₂ co) {pc : α -> Code × Code × σ × σ -> σ}
    (hpc : Computable₂ pc) {rf : α -> Code × σ -> σ} (hrf : Computable₂ rf) :
    let PR (a) cf cg hf hg := pr a (cf, cg, hf, hg)
    let CO (a) cf cg hf hg := co a (cf, cg, hf, hg)
    let PC (a) cf cg hf hg := pc a (cf, cg, hf, hg)
    let RF (a) cf hf := rf a (cf, hf)
    let F (a : α) (c : Code) : σ :=
      Nat.Partrec.Code.recOn c (z a) (s a) (l a) (r a) (PR a) (CO a) (PC a) (RF a)
    Computable fun a => F a (c a) := by
  -- TODO(Mario): less copy-paste from previous proof
  intro _ _ _ _ F
  let G₁ : (α × List σ) × Nat × Nat -> Option σ := fun p =>
    letI a := p.1.1; letI IH := p.1.2; letI n := p.2.1; letI m := p.2.2
    IH[m]?.bind fun s =>
    IH[m.unpair.1]?.bind fun s₁ =>
    IH[m.unpair.2]?.map fun s₂ =>
    cond n.bodd
      (cond n.div2.bodd (rf a (ofNat Code m, s))
        (pc a (ofNat Code m.unpair.1, ofNat Code m.unpair.2, s₁, s₂)))
      (cond n.div2.bodd (co a (ofNat Code m.unpair.1, ofNat Code m.unpair.2, s₁, s₂))
        (pr a (ofNat Code m.unpair.1, ofNat Code m.unpair.2, s₁, s₂)))
  have : Computable G₁ := by
refine option_bind (list_getElem?.comp (snd.comp fst) (snd.comp snd)) .mk ?_
    refine option_bind ((list_getElem?.comp (snd.comp fst)
      (fst.comp <| Computable.unpair.comp (snd.comp snd))).comp fst) <| .mk ?_
    refine option_map ((list_getElem?.comp (snd.comp fst)
      (snd.comp <| Computable.unpair.comp (snd.comp snd))).comp <| fst.comp fst) <| .mk ?_
    exact
      have a := fst.comp (fst.comp <| fst.comp <| fst.comp fst)
      have n := fst.comp (snd.comp <| fst.comp <| fst.comp fst)
      have m := snd.comp (snd.comp <| fst.comp <| fst.comp fst)
      have m₁ := fst.comp (Computable.unpair.comp m)
      have m₂ := snd.comp (Computable.unpair.comp m)
      have s := snd.comp (fst.comp fst)
      have s₁ := snd.comp fst
      have s₂ := snd
      (nat_bodd.comp n).cond
        ((nat_bodd.comp <| nat_div2.comp n).cond
          (hrf.comp a (((Computable.ofNat Code).comp m).pair s))
          (hpc.comp a (((Computable.ofNat Code).comp m₁).pair <|
((Computable.ofNat Code).comp m₂).pair s₁.pair s₂)))
        (Computable.cond (nat_bodd.comp <| nat_div2.comp n)
          (hco.comp a (((Computable.ofNat Code).comp m₁).pair <|
((Computable.ofNat Code).comp m₂).pair s₁.pair s₂))
          (hpr.comp a (((Computable.ofNat Code).comp m₁).pair <|
((Computable.ofNat Code).comp m₂).pair s₁.pair s₂)))
  let G : α -> List σ -> Option σ := fun a IH =>
    IH.length.casesOn (some (z a)) fun n =>
    n.casesOn (some (s a)) fun n =>
    n.casesOn (some (l a)) fun n =>
    n.casesOn (some (r a)) fun n =>
    G₁ ((a, IH), n, n.div2.div2)
have : Computable₂ G := .mk
nat_casesOn (list_length.comp snd) (option_some_iff.2 (hz.comp fst)) .mk
nat_casesOn snd (option_some_iff.2 (hs.comp (fst.comp fst))) .mk
nat_casesOn snd (option_some_iff.2 (hl.comp (fst.comp <| fst.comp fst))) .mk
nat_casesOn snd (option_some_iff.2 (hr.comp (fst.comp <| fst.comp <| fst.comp fst))) .mk
this.comp
((fst.pair snd).comp <| fst.comp <| fst.comp <| fst.comp <| fst).pair
snd.pair nat_div2.comp nat_div2.comp snd
  refine (nat_strong_rec (fun a n => F a (ofNat Code n)) this.to₂ fun a n => ?_)
.of_eq fun a => by simp .comp .id (encode_iff.2 hc)
  iterate 4 rcases n with - | n; · simp [ofNatCode_eq, ofNatCode]; rfl
  simp only [G]; rw [List.length_map, List.length_range]
  let m := n.div2.div2
  change G₁ ((a, (List.range (n + 4)).map fun n => F a (ofNat Code n)), n, m)
    = some (F a (ofNat Code (n + 4)))
  have hm : m < n + 4 := by
    simp only [m, div2_val]
    exact lt_of_le_of_lt
      (le_trans (Nat.div_le_self ..) (Nat.div_le_self ..))
      (Nat.succ_le_succ (Nat.le_add_right ..))
  have m1 : m.unpair.1 < n + 4 := lt_of_le_of_lt m.unpair_left_le hm
  have m2 : m.unpair.2 < n + 4 := lt_of_le_of_lt m.unpair_right_le hm
  simp [G₁, m, hm, m1, m2]
  rw [show ofNat Code (n + 4) = ofNatCode (n + 4) from rfl]
  simp [ofNatCode]
  cases n.bodd <;> cases n.div2.bodd <;> rfl

end

/--
Definition of `eval` / `eval` 的定义

English:
definition eval
  signature: : Code -> Nat ->. Nat

中文:
定义 eval
  签名: : Code -> 自然数 ->. 自然数
-/
def eval : Code -> Nat ->. Nat
  | zero => pure 0
  | succ => Nat.succ
  | left => ↑fun n : Nat => n.unpair.1
  | right => ↑fun n : Nat => n.unpair.2
| pair cf cg => fun n => Nat.pair < > eval cf n <*> eval cg n
  | comp cf cg => fun n => eval cg n >>= eval cf
  | prec cf cg =>
    Nat.unpaired fun a n =>
      n.rec (eval cf a) fun y IH => do
        let i ← IH
        eval cg (Nat.pair a (Nat.pair y i))
  | rfind' cf =>
    Nat.unpaired fun a m =>
      (Nat.rfind fun n => (fun m => m = 0) <$> eval cf (Nat.pair a (n + m))).map (· + m)

/-- Helper lemma for the evaluation of `prec` in the base case. -/
@[simp]
/--
theorem `eval_prec_zero` / 定理 `eval_prec_zero`

English:
theorem eval_prec_zero
  given: (cf cg : Code) (a : Nat)
  statement: eval (prec cf cg) (Nat.pair a 0) = eval cf a
  proof: by
  rw [eval]; rw [Nat.unpaired]; rw [Nat.unpair_pair]
  rw [Nat.rec_zero]

中文:
定理 eval_prec_zero
  条件: (cf cg : Code) (a : 自然数)
  结论: eval (prec cf cg) (自然数.pair a 0) = eval cf a
  证明: by
  rw [eval]; rw [Nat.unpaired]; rw [Nat.unpair_pair]
  rw [Nat.rec_zero]

Depends on / 依赖: Nat.rec_zero, Nat.unpair_pair, Nat.unpaired, rec_zero, unpair_pair, unpaired
-/
theorem eval_prec_zero (cf cg : Code) (a : Nat) : eval (prec cf cg) (Nat.pair a 0) = eval cf a := by
  rw [eval]; rw [Nat.unpaired]; rw [Nat.unpair_pair]
  rw [Nat.rec_zero]

/--
theorem `eval_prec_succ` / 定理 `eval_prec_succ`

English:
theorem eval_prec_succ
  given: (cf cg : Code) (a k : Nat)
  proof: by
  rw [eval]; rw [Nat.unpaired]; rw [Part.bind_eq_bind]; rw [Nat.unpair_pair]
  simp

中文:
定理 eval_prec_succ
  条件: (cf cg : Code) (a k : 自然数)
  证明: by
  rw [eval]; rw [Nat.unpaired]; rw [Part.bind_eq_bind]; rw [Nat.unpair_pair]
  simp

Depends on / 依赖: Nat.unpair_pair, Nat.unpaired, Part.bind_eq_bind, bind_eq_bind, unpair_pair, unpaired
-/
theorem eval_prec_succ (cf cg : Code) (a k : Nat) :
    eval (prec cf cg) (Nat.pair a (Nat.succ k)) =
      do {let ih ← eval (prec cf cg) (Nat.pair a k); eval cg (Nat.pair a (Nat.pair k ih))} := by
  rw [eval]; rw [Nat.unpaired]; rw [Part.bind_eq_bind]; rw [Nat.unpair_pair]
  simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Membership (Nat ->. Nat) Code
  body: ⟨fun c f => eval c = f⟩

中文:
实例 :
  签名: Membership (自然数 ->. 自然数) Code
  定义体: ⟨fun c f => eval c = f⟩
-/
instance : Membership (Nat ->. Nat) Code :=
  ⟨fun c f => eval c = f⟩

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `eval_const` / 定理 `eval_const`

English:
theorem eval_const
  statement: forall n m, eval (Code.const n) m = Part.some n

中文:
定理 eval_const
  结论: 对任意 n m, eval (Code.const n) m = Part.some n
-/
theorem eval_const : forall n m, eval (Code.const n) m = Part.some n
  | 0, _ => rfl
  | n + 1, m => by simp! [eval_const n m]

@[simp]
/--
theorem `eval_id` / 定理 `eval_id`

English:
theorem eval_id
  given: (n)
  statement: eval Code.id n = Part.some n
  proof: by simp! [Seq.seq, Code.id]

中文:
定理 eval_id
  条件: (n)
  结论: eval Code.id n = Part.some n
  证明: by simp! [Seq.seq, Code.id]

Depends on / 依赖: Code.id, Seq.seq
-/
theorem eval_id (n) : eval Code.id n = Part.some n := by simp! [Seq.seq, Code.id]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `eval_curry` / 定理 `eval_curry`

English:
theorem eval_curry
  given: (c n x)
  statement: eval (curry c n) x = eval c (Nat.pair n x)
  proof: by simp! [Seq.seq, curry]

中文:
定理 eval_curry
  条件: (c n x)
  结论: eval (curry c n) x = eval c (自然数.pair n x)
  证明: by simp! [Seq.seq, curry]

Depends on / 依赖: Seq.seq
-/
theorem eval_curry (c n x) : eval (curry c n) x = eval c (Nat.pair n x) := by simp! [Seq.seq, curry]

/--
theorem `primrec_const` / 定理 `primrec_const`

English:
theorem primrec_const
  statement: Primrec Code.const
  proof: (_root_.Primrec.id.nat_iterate (_root_.Primrec.const zero)
    (primrec₂_comp.comp (_root_.Primrec.const succ) Primrec.snd).to₂).of_eq
    fun n => by simp; induction n <;>
      simp [*, Code.const, Function.iterate_succ', -Function.iterate_succ]

中文:
定理 primrec_const
  结论: Primrec Code.const
  证明: (_root_.Primrec.id.nat_iterate (_root_.Primrec.const zero)
    (primrec₂_comp.comp (_root_.Primrec.const succ) Primrec.snd).to₂).of_eq
    fun n => by simp; induction n <;>
      simp [*, Code.const, Function.iterate_succ', -Function.iterate_succ]

Depends on / 依赖: Code.const, Function, Function.iterate_succ, Primrec, Primrec.snd, _comp.comp, _root_, _root_.Primrec.const, _root_.Primrec.id.nat_iterate, iterate_succ, nat_iterate, of_eq
-/
theorem primrec_const : Primrec Code.const :=
  (_root_.Primrec.id.nat_iterate (_root_.Primrec.const zero)
    (primrec₂_comp.comp (_root_.Primrec.const succ) Primrec.snd).to₂).of_eq
    fun n => by simp; induction n <;>
      simp [*, Code.const, Function.iterate_succ', -Function.iterate_succ]

/--
theorem `primrec₂_curry` / 定理 `primrec₂_curry`

English:
theorem primrec₂_curry
  statement: Primrec₂ curry
  proof: primrec₂_comp.comp Primrec.fst primrec₂_pair.comp (primrec_const.comp Primrec.snd)
    (_root_.Primrec.const Code.id)

中文:
定理 primrec₂_curry
  结论: Primrec₂ curry
  证明: primrec₂_comp.comp Primrec.fst primrec₂_pair.comp (primrec_const.comp Primrec.snd)
    (_root_.Primrec.const Code.id)

Depends on / 依赖: Code.id, Primrec, Primrec.fst, Primrec.snd, _comp.comp, _pair.comp, _root_, _root_.Primrec.const, primrec_const, primrec_const.comp
-/
theorem primrec₂_curry : Primrec₂ curry :=
primrec₂_comp.comp Primrec.fst primrec₂_pair.comp (primrec_const.comp Primrec.snd)
    (_root_.Primrec.const Code.id)

/--
theorem `curry_inj` / 定理 `curry_inj`

English:
theorem curry_inj
  given: {c₁ c₂ n₁ n₂} (h : curry c₁ n₁ = curry c₂ n₂)
  statement: c₁ = c₂ ∧ n₁ = n₂
  proof: ⟨by injection h, by
    injection h with h₁ h₂
    injection h₂ with h₃ h₄
    exact const_inj h₃⟩

中文:
定理 curry_inj
  条件: {c₁ c₂ n₁ n₂} (h : curry c₁ n₁ = curry c₂ n₂)
  结论: c₁ = c₂ ∧ n₁ = n₂
  证明: ⟨by injection h, by
    injection h with h₁ h₂
    injection h₂ with h₃ h₄
    exact const_inj h₃⟩

Depends on / 依赖: const_inj, injection
-/
theorem curry_inj {c₁ c₂ n₁ n₂} (h : curry c₁ n₁ = curry c₂ n₂) : c₁ = c₂ ∧ n₁ = n₂ :=
  ⟨by injection h, by
    injection h with h₁ h₂
    injection h₂ with h₃ h₄
    exact const_inj h₃⟩

/--
theorem `smn` / 定理 `smn`

English:
theorem smn
  proof: ⟨curry, Primrec₂.to_comp primrec₂_curry, eval_curry⟩

中文:
定理 smn
  证明: ⟨curry, Primrec₂.to_comp primrec₂_curry, eval_curry⟩

Depends on / 依赖: eval_curry, to_comp
-/
theorem smn :
    exists f : Code -> Nat -> Code, Computable₂ f ∧ forall c n x, eval (f c n) x = eval c (Nat.pair n x) :=
  ⟨curry, Primrec₂.to_comp primrec₂_curry, eval_curry⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `exists_code` / 定理 `exists_code`

English:
theorem exists_code
  given: {f : Nat ->. Nat}
  statement: Nat.Partrec f ↔ exists c : Code, eval c = f
  proof: by
  refine ⟨fun h => ?_, ?_⟩
  · induction h with
    | zero => exact ⟨zero, rfl⟩
    | succ => exact ⟨succ, rfl⟩
    | left => exact ⟨left, rfl⟩
    | right => exact ⟨right, rfl⟩
    | pair pf pg hf hg =>
      rcases hf with ⟨cf, rfl⟩; rcases hg with ⟨cg, rfl⟩
      exact ⟨pair cf cg, rfl⟩
    | 

中文:
定理 exists_code
  条件: {f : 自然数 ->. 自然数}
  结论: 自然数.Partrec f ↔ 存在 c : Code, eval c = f
  证明: by
  refine ⟨fun h => ?_, ?_⟩
  · induction h with
    | zero => exact ⟨zero, rfl⟩
    | succ => exact ⟨succ, rfl⟩
    | left => exact ⟨left, rfl⟩
    | right => exact ⟨right, rfl⟩
    | pair pf pg hf hg =>
      rcases hf with ⟨cf, rfl⟩; rcases hg with ⟨cg, rfl⟩
      exact ⟨pair cf cg, rfl⟩
    | 
-/
theorem exists_code {f : Nat ->. Nat} : Nat.Partrec f ↔ exists c : Code, eval c = f := by
  refine ⟨fun h => ?_, ?_⟩
  · induction h with
    | zero => exact ⟨zero, rfl⟩
    | succ => exact ⟨succ, rfl⟩
    | left => exact ⟨left, rfl⟩
    | right => exact ⟨right, rfl⟩
    | pair pf pg hf hg =>
      rcases hf with ⟨cf, rfl⟩; rcases hg with ⟨cg, rfl⟩
      exact ⟨pair cf cg, rfl⟩
    | comp pf pg hf hg =>
      rcases hf with ⟨cf, rfl⟩; rcases hg with ⟨cg, rfl⟩
      exact ⟨comp cf cg, rfl⟩
    | prec pf pg hf hg =>
      rcases hf with ⟨cf, rfl⟩; rcases hg with ⟨cg, rfl⟩
      exact ⟨prec cf cg, rfl⟩
    | rfind pf hf =>
      rcases hf with ⟨cf, rfl⟩
      refine ⟨comp (rfind' cf) (pair Code.id zero), ?_⟩
      simp [eval, Seq.seq, pure, PFun.pure, Part.map_id']
  · rintro ⟨c, rfl⟩
    induction c with
    | zero => exact Nat.Partrec.zero
    | succ => exact Nat.Partrec.succ
    | left => exact Nat.Partrec.left
    | right => exact Nat.Partrec.right
    | pair cf cg pf pg => exact pf.pair pg
    | comp cf cg pf pg => exact pf.comp pg
    | prec cf cg pf pg => exact pf.prec pg
    | rfind' cf pf => exact pf.rfind'

/--
Definition of `evaln` / `evaln` 的定义

English:
definition evaln
  signature: : Nat -> Code -> Nat -> Option Nat

中文:
定义 evaln
  签名: : 自然数 -> Code -> 自然数 -> Option 自然数
-/
def evaln : Nat -> Code -> Nat -> Option Nat
  | 0, _ => fun _ => Option.none
  | k + 1, zero => fun n => do
    guard (n <= k)
    return 0
  | k + 1, succ => fun n => do
    guard (n <= k)
    return (Nat.succ n)
  | k + 1, left => fun n => do
    guard (n <= k)
    return n.unpair.1
  | k + 1, right => fun n => do
    guard (n <= k)
    pure n.unpair.2
  | k + 1, pair cf cg => fun n => do
    guard (n <= k)
Nat.pair < > evaln (k + 1) cf n <*> evaln (k + 1) cg n
  | k + 1, comp cf cg => fun n => do
    guard (n <= k)
    let x ← evaln (k + 1) cg n
    evaln (k + 1) cf x
  | k + 1, prec cf cg => fun n => do
    guard (n <= k)
    n.unpaired fun a n =>
      n.casesOn (evaln (k + 1) cf a) fun y => do
        let i ← evaln k (prec cf cg) (Nat.pair a y)
        evaln (k + 1) cg (Nat.pair a (Nat.pair y i))
  | k + 1, rfind' cf => fun n => do
    guard (n <= k)
    n.unpaired fun a m => do
      let x ← evaln (k + 1) cf (Nat.pair a m)
      if x = 0 then
        pure m
      else
        evaln k (rfind' cf) (Nat.pair a (m + 1))

/--
theorem `evaln_bound` / 定理 `evaln_bound`

English:
theorem evaln_bound
  statement: forall {k c n x}, x in evaln k c n -> n < k

中文:
定理 evaln_bound
  结论: 对任意 {k c n x}, x in evaln k c n -> n < k
-/
theorem evaln_bound : forall {k c n x}, x in evaln k c n -> n < k
  | 0, c, n, x, h => by simp [evaln] at h
  | k + 1, c, n, x, h => by
    suffices forall {o : Option Nat}, x in do { guard (n <= k); o } -> n < k + 1 by
      cases c <;> rw [evaln] at h <;> exact this h
    simpa [Option.bind_eq_some_iff] using Nat.lt_succ_of_le

set_option linter.flexible false in -- TODO: revisit this after #13791 is merged
/--
theorem `evaln_mono` / 定理 `evaln_mono`

English:
theorem evaln_mono
  statement: forall {k₁ k₂ c n x}, k₁ <= k₂ -> x in evaln k₁ c n -> x in evaln k₂ c n
  proof: Nat.le_of_succ_le_succ hl
    have :
      forall {k k₂ n x : Nat} {o₁ o₂ : Option Nat},
        k <= k₂ -> (x in o₁ -> x in o₂) ->
          x in do { guard (n <= k); o₁ } -> x in do { guard (n <= k₂); o₂ } := by
      simp only [Option.mem_def, bind, Option.bind_eq_some_iff, Option.guard_eq_some',

中文:
定理 evaln_mono
  结论: 对任意 {k₁ k₂ c n x}, k₁ <= k₂ -> x in evaln k₁ c n -> x in evaln k₂ c n
  证明: Nat.le_of_succ_le_succ hl
    have :
      forall {k k₂ n x : Nat} {o₁ o₂ : Option Nat},
        k <= k₂ -> (x in o₁ -> x in o₂) ->
          x in do { guard (n <= k); o₁ } -> x in do { guard (n <= k₂); o₂ } := by
      simp only [Option.mem_def, bind, Option.bind_eq_some_iff, Option.guard_eq_some',

Depends on / 依赖: Nat.le_of_succ_le_succ, le_of_succ_le_succ
-/
theorem evaln_mono : forall {k₁ k₂ c n x}, k₁ <= k₂ -> x in evaln k₁ c n -> x in evaln k₂ c n
  | 0, k₂, c, n, x, _, h => by simp [evaln] at h
  | k + 1, k₂ + 1, c, n, x, hl, h => by
    have hl' := Nat.le_of_succ_le_succ hl
    have :
      forall {k k₂ n x : Nat} {o₁ o₂ : Option Nat},
        k <= k₂ -> (x in o₁ -> x in o₂) ->
          x in do { guard (n <= k); o₁ } -> x in do { guard (n <= k₂); o₂ } := by
      simp only [Option.mem_def, bind, Option.bind_eq_some_iff, Option.guard_eq_some',
        exists_and_left, exists_const, and_imp]
      introv h h₁ h₂ h₃
      exact ⟨le_trans h₂ h, h₁ h₃⟩
    simp? at h ⊢ says simp only [Option.mem_def] at h ⊢
    induction c generalizing x n <;> rw [evaln] at h ⊢ <;> refine this hl' (fun h => ?_) h
    iterate 4 exact h
    case pair cf cg hf hg _ =>
      simp? [Seq.seq, Option.bind_eq_some_iff] at h ⊢ says
        simp only [Seq.seq, Option.map_eq_map, Option.mem_def, Option.bind_eq_some_iff,
          Option.map_eq_some_iff, exists_exists_and_eq_and] at h ⊢
exact h.imp fun a => And.imp (hf _ _) Exists.imp fun b => And.imp_left (hg _ _)
    case comp cf cg hf hg _ =>
      simp? [Bind.bind, Option.bind_eq_some_iff] at h ⊢ says
        simp only [bind, Option.mem_def, Option.bind_eq_some_iff] at h ⊢
      exact h.imp fun a => And.imp (hg _ _) (hf _ _)
    case prec cf cg hf hg _ =>
      revert h
      simp only [unpaired, bind, Option.mem_def]
      induction n.unpair.2 <;> simp [Option.bind_eq_some_iff]
      · apply hf
      · exact fun y h₁ h₂ => ⟨y, evaln_mono hl' h₁, hg _ _ h₂⟩
    case rfind' cf hf _ =>
      simp? [Bind.bind, Option.bind_eq_some_iff] at h ⊢ says
        simp only [unpaired, bind, pair_unpair, Option.pure_def, Option.mem_def,
          Option.bind_eq_some_iff] at h ⊢
      refine h.imp fun x => And.imp (hf _ _) ?_
      by_cases x0 : x = 0 <;> simp [x0]
      exact evaln_mono hl'

set_option backward.isDefEq.respectTransparency false in
set_option linter.flexible false in -- TODO: revisit this after #13791 is merged
/--
theorem `evaln_sound` / 定理 `evaln_sound`

English:
theorem evaln_sound
  statement: forall {k c n x}, x in evaln k c n -> x in eval c n
  proof: h
    iterate 4 simpa [pure, PFun.pure, eq_comm] using h
    case pair cf cg hf hg _ =>
      rcases h with ⟨y, ef, z, eg, rfl⟩
      exact ⟨_, hf _ _ ef, _, hg _ _ eg, rfl⟩
    case comp cf cg hf hg _ =>
      rcases h with ⟨y, eg, ef⟩
      exact ⟨_, hg _ _ eg, hf _ _ ef⟩
    case prec cf cg hf hg

中文:
定理 evaln_sound
  结论: 对任意 {k c n x}, x in evaln k c n -> x in eval c n
  证明: h
    iterate 4 simpa [pure, PFun.pure, eq_comm] using h
    case pair cf cg hf hg _ =>
      rcases h with ⟨y, ef, z, eg, rfl⟩
      exact ⟨_, hf _ _ ef, _, hg _ _ eg, rfl⟩
    case comp cf cg hf hg _ =>
      rcases h with ⟨y, eg, ef⟩
      exact ⟨_, hg _ _ eg, hf _ _ ef⟩
    case prec cf cg hf hg
-/
theorem evaln_sound : forall {k c n x}, x in evaln k c n -> x in eval c n
  | 0, _, n, x, h => by simp [evaln] at h
  | k + 1, c, n, x, h => by
    induction c generalizing x n <;> simp [eval, evaln, Option.bind_eq_some_iff, Seq.seq] at h ⊢ <;>
      obtain ⟨_, h⟩ := h
    iterate 4 simpa [pure, PFun.pure, eq_comm] using h
    case pair cf cg hf hg _ =>
      rcases h with ⟨y, ef, z, eg, rfl⟩
      exact ⟨_, hf _ _ ef, _, hg _ _ eg, rfl⟩
    case comp cf cg hf hg _ =>
      rcases h with ⟨y, eg, ef⟩
      exact ⟨_, hg _ _ eg, hf _ _ ef⟩
    case prec cf cg hf hg _ =>
      revert h
      induction n.unpair.2 generalizing x with simp [Option.bind_eq_some_iff]
      | zero => apply hf
      | succ m IH =>
        refine fun y h₁ h₂ => ⟨y, IH _ ?_, ?_⟩
        · have := evaln_mono k.le_succ h₁
          simp [evaln, Option.bind_eq_some_iff] at this
          exact this.2
        · exact hg _ _ h₂
    case rfind' cf hf _ =>
      rcases h with ⟨m, h₁, h₂⟩
      by_cases m0 : m = 0 <;> simp [m0] at h₂
      · exact
          ⟨0, ⟨by simpa [m0] using hf _ _ h₁, fun {m} => (Nat.not_lt_zero _).elim⟩, by simp [h₂]⟩
      · have := evaln_sound h₂
        simp [eval] at this
        rcases this with ⟨y, ⟨hy₁, hy₂⟩, rfl⟩
        refine
          ⟨y + 1, ⟨by simpa [add_comm, add_left_comm] using hy₁, fun {i} im => ?_⟩, by
            simp [add_comm, add_left_comm]⟩
        rcases i with - | i
        · exact ⟨m, by simpa using hf _ _ h₁, m0⟩
        · rcases hy₂ (Nat.lt_of_succ_lt_succ im) with ⟨z, hz, z0⟩
          exact ⟨z, by simpa [add_comm, add_left_comm] using hz, z0⟩

set_option backward.isDefEq.respectTransparency false in
set_option linter.flexible false in -- TODO: revisit this after #13791 is merged
/--
theorem `evaln_complete` / 定理 `evaln_complete`

English:
theorem evaln_complete
  given: {c n x}
  statement: x in eval c n ↔ exists k, x in evaln k c n
  proof: by
  refine ⟨fun h => ?_, fun ⟨k, h⟩ => evaln_sound h⟩
  rsuffices ⟨k, h⟩ : exists k, x in evaln (k + 1) c n
  · exact ⟨k + 1, h⟩
  induction c generalizing n x with
      simp [eval, evaln, pure, PFun.pure, Seq.seq, Option.bind_eq_some_iff] at h ⊢
  | pair cf cg hf hg =>
    rcases h with ⟨x, hx, y

中文:
定理 evaln_complete
  条件: {c n x}
  结论: x in eval c n ↔ 存在 k, x in evaln k c n
  证明: by
  refine ⟨fun h => ?_, fun ⟨k, h⟩ => evaln_sound h⟩
  rsuffices ⟨k, h⟩ : exists k, x in evaln (k + 1) c n
  · exact ⟨k + 1, h⟩
  induction c generalizing n x with
      simp [eval, evaln, pure, PFun.pure, Seq.seq, Option.bind_eq_some_iff] at h ⊢
  | pair cf cg hf hg =>
    rcases h with ⟨x, hx, y

Depends on / 依赖: Nat.le_of_lt_succ, Nat.succ_le_succ, Option.bind_eq_some_iff, PFun.pure, Seq.seq, bind_eq_some_iff, evaln_bound, evaln_mo, evaln_mono, evaln_sound, generalizing, le_max_left, le_max_of_le_left, le_of_lt_succ, rsuffices, succ_le_succ
-/
theorem evaln_complete {c n x} : x in eval c n ↔ exists k, x in evaln k c n := by
  refine ⟨fun h => ?_, fun ⟨k, h⟩ => evaln_sound h⟩
  rsuffices ⟨k, h⟩ : exists k, x in evaln (k + 1) c n
  · exact ⟨k + 1, h⟩
  induction c generalizing n x with
      simp [eval, evaln, pure, PFun.pure, Seq.seq, Option.bind_eq_some_iff] at h ⊢
  | pair cf cg hf hg =>
    rcases h with ⟨x, hx, y, hy, rfl⟩
    rcases hf hx with ⟨k₁, hk₁⟩; rcases hg hy with ⟨k₂, hk₂⟩
    refine ⟨max k₁ k₂, ?_⟩
    refine
⟨le_max_of_le_left Nat.le_of_lt_succ evaln_bound hk₁, _,
        evaln_mono (Nat.succ_le_succ <| le_max_left _ _) hk₁, _,
        evaln_mono (Nat.succ_le_succ <| le_max_right _ _) hk₂, rfl⟩
  | comp cf cg hf hg =>
    rcases h with ⟨y, hy, hx⟩
    rcases hg hy with ⟨k₁, hk₁⟩; rcases hf hx with ⟨k₂, hk₂⟩
    refine ⟨max k₁ k₂, ?_⟩
    exact
⟨le_max_of_le_left Nat.le_of_lt_succ evaln_bound hk₁, _,
        evaln_mono (Nat.succ_le_succ <| le_max_left _ _) hk₁,
        evaln_mono (Nat.succ_le_succ <| le_max_right _ _) hk₂⟩
  | prec cf cg hf hg =>
    revert h
    generalize n.unpair.1 = n₁; generalize n.unpair.2 = n₂
    induction n₂ generalizing x n with simp [Option.bind_eq_some_iff]
    | zero =>
      intro h
      rcases hf h with ⟨k, hk⟩
      exact ⟨_, le_max_left _ _, evaln_mono (Nat.succ_le_succ <| le_max_right _ _) hk⟩
    | succ m IH =>
      intro y hy hx
      rcases IH hy with ⟨k₁, nk₁, hk₁⟩
      rcases hg hx with ⟨k₂, hk₂⟩
      refine
        ⟨(max k₁ k₂).succ,
Nat.le_succ_of_le le_max_of_le_left
            le_trans (le_max_left _ (Nat.pair n₁ m)) nk₁, y,
          evaln_mono (Nat.succ_le_succ <| le_max_left _ _) ?_,
          evaln_mono (Nat.succ_le_succ <| Nat.le_succ_of_le <| le_max_right _ _) hk₂⟩
      simp only [evaln.eq_8, bind, unpaired, unpair_pair, Option.mem_def, Option.bind_eq_some_iff,
        Option.guard_eq_some', exists_and_left, exists_const]
      exact ⟨le_trans (le_max_right _ _) nk₁, hk₁⟩
  | rfind' cf hf =>
    rcases h with ⟨y, ⟨hy₁, hy₂⟩, rfl⟩
    suffices exists k, y + n.unpair.2 in evaln (k + 1) (rfind' cf) (Nat.pair n.unpair.1 n.unpair.2) by
      simpa [evaln, Option.bind_eq_some_iff]
    revert hy₁ hy₂
    generalize n.unpair.2 = m
    intro hy₁ hy₂
    induction y generalizing m with simp [evaln, Option.bind_eq_some_iff]
    | zero =>
      simp at hy₁
      rcases hf hy₁ with ⟨k, hk⟩
exact ⟨_, Nat.le_of_lt_succ evaln_bound hk, _, hk, by simp⟩
    | succ y IH =>
      rcases hy₂ (Nat.succ_pos _) with ⟨a, ha, a0⟩
      rcases hf ha with ⟨k₁, hk₁⟩
      rcases IH m.succ (by simpa [Nat.succ_eq_add_one, add_comm, add_left_comm] using hy₁)
          fun {i} hi => by
          simpa [Nat.succ_eq_add_one, add_comm, add_left_comm] using
            hy₂ (Nat.succ_lt_succ hi) with
        ⟨k₂, hk₂⟩
      use (max k₁ k₂).succ
      rw [zero_add] at hk₁
use Nat.le_succ_of_le le_max_of_le_left Nat.le_of_lt_succ evaln_bound hk₁
      use a
      use evaln_mono (Nat.succ_le_succ <| Nat.le_succ_of_le <| le_max_left _ _) hk₁
      simpa [a0, add_comm, add_left_comm] using
        evaln_mono (Nat.succ_le_succ <| le_max_right _ _) hk₂
  | _ => exact ⟨⟨_, le_rfl⟩, h.symm⟩

section

/--
Definition of `lup` / `lup` 的定义

English:
definition lup
  signature: (L : List (List (Option Nat))) (p : Nat × Code) (n : Nat)
  body: do
  let l ← L[encode p]?
  let o ← l[n]?
  o

中文:
定义 lup
  签名: (L : List (List (Option 自然数))) (p : 自然数 × Code) (n : 自然数)
  定义体: do
  let l ← L[encode p]?
  let o ← l[n]?
  o
-/
private def lup (L : List (List (Option Nat))) (p : Nat × Code) (n : Nat) := do
  let l ← L[encode p]?
  let o ← l[n]?
  o

/--
theorem `hlup` / 定理 `hlup`

English:
theorem hlup
  statement: Primrec fun p : _ × (_ × _) × _ => lup p.1 p.2.1 p.2.2
  proof: Primrec.option_bind
    (Primrec.list_getElem?.comp Primrec.fst (Primrec.encode.comp <| Primrec.fst.comp Primrec.snd))
    (Primrec.option_bind (Primrec.list_getElem?.comp Primrec.snd <| Primrec.snd.comp <|
      Primrec.snd.comp Primrec.fst) Primrec.snd)

中文:
定理 hlup
  结论: Primrec fun p : _ × (_ × _) × _ => lup p.1 p.2.1 p.2.2
  证明: Primrec.option_bind
    (Primrec.list_getElem?.comp Primrec.fst (Primrec.encode.comp <| Primrec.fst.comp Primrec.snd))
    (Primrec.option_bind (Primrec.list_getElem?.comp Primrec.snd <| Primrec.snd.comp <|
      Primrec.snd.comp Primrec.fst) Primrec.snd)
-/
private theorem hlup : Primrec fun p : _ × (_ × _) × _ => lup p.1 p.2.1 p.2.2 :=
  Primrec.option_bind
    (Primrec.list_getElem?.comp Primrec.fst (Primrec.encode.comp <| Primrec.fst.comp Primrec.snd))
    (Primrec.option_bind (Primrec.list_getElem?.comp Primrec.snd <| Primrec.snd.comp <|
      Primrec.snd.comp Primrec.fst) Primrec.snd)

/--
Definition of `G` / `G` 的定义

English:
definition G
  signature: (L : List (List (Option Nat)))
  body: Option.some
    let a := ofNat (Nat × Code) L.length
    let k := a.1
    let c := a.2
    (List.range k).map fun n =>
      k.casesOn Option.none fun k' =>
        Nat.Partrec.Code.recOn c
          (some 0) -- zero
          (some (Nat.succ n))
          (some n.unpair.1)
          (some n.unpair.

中文:
定义 G
  签名: (L : List (List (Option 自然数)))
  定义体: Option.some
    let a := ofNat (Nat × Code) L.length
    let k := a.1
    let c := a.2
    (List.range k).map fun n =>
      k.casesOn Option.none fun k' =>
        Nat.Partrec.Code.recOn c
          (some 0) -- zero
          (some (Nat.succ n))
          (some n.unpair.1)
          (some n.unpair.
-/
private def G (L : List (List (Option Nat))) : Option (List (Option Nat)) :=
Option.some
    let a := ofNat (Nat × Code) L.length
    let k := a.1
    let c := a.2
    (List.range k).map fun n =>
      k.casesOn Option.none fun k' =>
        Nat.Partrec.Code.recOn c
          (some 0) -- zero
          (some (Nat.succ n))
          (some n.unpair.1)
          (some n.unpair.2)
          (fun cf cg _ _ => do
            let x ← lup L (k, cf) n
            let y ← lup L (k, cg) n
            some (Nat.pair x y))
          (fun cf cg _ _ => do
            let x ← lup L (k, cg) n
            lup L (k, cf) x)
          (fun cf cg _ _ =>
            let z := n.unpair.1
            n.unpair.2.casesOn (lup L (k, cf) z) fun y => do
              let i ← lup L (k', c) (Nat.pair z y)
              lup L (k, cg) (Nat.pair z (Nat.pair y i)))
          (fun cf _ =>
            let z := n.unpair.1
            let m := n.unpair.2
            do
              let x ← lup L (k, cf) (Nat.pair z m)
              x.casesOn (some m) fun _ => lup L (k', c) (Nat.pair z (m + 1)))

/--
theorem `hG` / 定理 `hG`

English:
theorem hG
  statement: Primrec G
  proof: by
  have a := (Primrec.ofNat (Nat × Code)).comp (Primrec.list_length (α := List (Option Nat)))
  have k := Primrec.fst.comp a
  refine Primrec.option_some.comp (Primrec.list_map (Primrec.list_range.comp k) (?_ : Primrec _))
  replace k := k.comp (Primrec.fst (β := Nat))
  have n := Primrec.snd (α :

中文:
定理 hG
  结论: Primrec G
  证明: by
  have a := (Primrec.ofNat (Nat × Code)).comp (Primrec.list_length (α := List (Option Nat)))
  have k := Primrec.fst.comp a
  refine Primrec.option_some.comp (Primrec.list_map (Primrec.list_range.comp k) (?_ : Primrec _))
  replace k := k.comp (Primrec.fst (β := Nat))
  have n := Primrec.snd (α :

Depends on / 依赖: add_le_add_iff_left, add_le_add_left
-/
private theorem hG : Primrec G := by
  have a := (Primrec.ofNat (Nat × Code)).comp (Primrec.list_length (α := List (Option Nat)))
  have k := Primrec.fst.comp a
  refine Primrec.option_some.comp (Primrec.list_map (Primrec.list_range.comp k) (?_ : Primrec _))
  replace k := k.comp (Primrec.fst (β := Nat))
  have n := Primrec.snd (α := List (List (Option Nat))) (β := Nat)
  refine Primrec.nat_casesOn k (_root_.Primrec.const Option.none) (?_ : Primrec _)
  have k := k.comp (Primrec.fst (β := Nat))
  have n := n.comp (Primrec.fst (β := Nat))
  have k' := Primrec.snd (α := List (List (Option Nat)) × Nat) (β := Nat)
  have c := Primrec.snd.comp (a.comp <| (Primrec.fst (β := Nat)).comp (Primrec.fst (β := Nat)))
  apply
    Nat.Partrec.Code.primrec_recOn c
      (_root_.Primrec.const (some 0))
      (Primrec.option_some.comp (_root_.Primrec.succ.comp n))
      (Primrec.option_some.comp (Primrec.fst.comp <| Primrec.unpair.comp n))
      (Primrec.option_some.comp (Primrec.snd.comp <| Primrec.unpair.comp n))
  · have L := (Primrec.fst.comp Primrec.fst).comp
      (Primrec.fst (α := (List (List (Option Nat)) × Nat) × Nat)
        (β := Code × Code × Option Nat × Option Nat))
    have k := k.comp (Primrec.fst (β := Code × Code × Option Nat × Option Nat))
    have n := n.comp (Primrec.fst (β := Code × Code × Option Nat × Option Nat))
    have cf := Primrec.fst.comp (Primrec.snd (α := (List (List (Option Nat)) × Nat) × Nat)
        (β := Code × Code × Option Nat × Option Nat))
    have cg := (Primrec.fst.comp Primrec.snd).comp
      (Primrec.snd (α := (List (List (Option Nat)) × Nat) × Nat)
        (β := Code × Code × Option Nat × Option Nat))
    refine Primrec.option_bind (hlup.comp <| L.pair <| (k.pair cf).pair n) ?_
    unfold Primrec₂
    conv =>
      congr
      · ext p
        dsimp only
        erw [Option.bind_eq_bind, ← Option.map_eq_bind]
    refine Primrec.option_map ((hlup.comp <| L.pair <| (k.pair cg).pair n).comp Primrec.fst) ?_
    unfold Primrec₂
    exact Primrec₂.natPair.comp (Primrec.snd.comp Primrec.fst) Primrec.snd
  · have L := (Primrec.fst.comp Primrec.fst).comp
      (Primrec.fst (α := (List (List (Option Nat)) × Nat) × Nat)
        (β := Code × Code × Option Nat × Option Nat))
    have k := k.comp (Primrec.fst (β := Code × Code × Option Nat × Option Nat))
    have n := n.comp (Primrec.fst (β := Code × Code × Option Nat × Option Nat))
    have cf := Primrec.fst.comp (Primrec.snd (α := (List (List (Option Nat)) × Nat) × Nat)
        (β := Code × Code × Option Nat × Option Nat))
    have cg := (Primrec.fst.comp Primrec.snd).comp
      (Primrec.snd (α := (List (List (Option Nat)) × Nat) × Nat)
        (β := Code × Code × Option Nat × Option Nat))
    refine Primrec.option_bind (hlup.comp <| L.pair <| (k.pair cg).pair n) ?_
    unfold Primrec₂
    have h :=
      hlup.comp ((L.comp Primrec.fst).pair <| ((k.pair cf).comp Primrec.fst).pair Primrec.snd)
    exact h
  · have L := (Primrec.fst.comp Primrec.fst).comp
      (Primrec.fst (α := (List (List (Option Nat)) × Nat) × Nat)
        (β := Code × Code × Option Nat × Option Nat))
    have k := k.comp (Primrec.fst (β := Code × Code × Option Nat × Option Nat))
    have n := n.comp (Primrec.fst (β := Code × Code × Option Nat × Option Nat))
    have cf := Primrec.fst.comp (Primrec.snd (α := (List (List (Option Nat)) × Nat) × Nat)
        (β := Code × Code × Option Nat × Option Nat))
    have cg := (Primrec.fst.comp Primrec.snd).comp
      (Primrec.snd (α := (List (List (Option Nat)) × Nat) × Nat)
        (β := Code × Code × Option Nat × Option Nat))
    have z := Primrec.fst.comp (Primrec.unpair.comp n)
    refine
      Primrec.nat_casesOn (Primrec.snd.comp (Primrec.unpair.comp n))
        (hlup.comp <| L.pair <| (k.pair cf).pair z)
        (?_ : Primrec _)
    have L := L.comp (Primrec.fst (β := Nat))
    have z := z.comp (Primrec.fst (β := Nat))
    have y := Primrec.snd
      (α := ((List (List (Option Nat)) × Nat) × Nat) × Code × Code × Option Nat × Option Nat) (β := Nat)
have h₁ := hlup.comp L.pair (((k'.pair c).comp Primrec.fst).comp Primrec.fst).pair
      (Primrec₂.natPair.comp z y)
    refine Primrec.option_bind h₁ (?_ : Primrec _)
    have z := z.comp (Primrec.fst (β := Nat))
    have y := y.comp (Primrec.fst (β := Nat))
    have i := Primrec.snd
      (α := (((List (List (Option Nat)) × Nat) × Nat) × Code × Code × Option Nat × Option Nat) × Nat)
      (β := Nat)
    have h₂ := hlup.comp ((L.comp Primrec.fst).pair <|
((k.pair cg).comp <| Primrec.fst.comp Primrec.fst).pair
Primrec₂.natPair.comp z Primrec₂.natPair.comp y i)
    exact h₂
  · have L := (Primrec.fst.comp Primrec.fst).comp
      (Primrec.fst (α := (List (List (Option Nat)) × Nat) × Nat)
        (β := Code × Option Nat))
    have k := k.comp (Primrec.fst (β := Code × Option Nat))
    have n := n.comp (Primrec.fst (β := Code × Option Nat))
    have cf := Primrec.fst.comp (Primrec.snd (α := (List (List (Option Nat)) × Nat) × Nat)
        (β := Code × Option Nat))
    have z := Primrec.fst.comp (Primrec.unpair.comp n)
    have m := Primrec.snd.comp (Primrec.unpair.comp n)
have h₁ := hlup.comp L.pair (k.pair cf).pair (Primrec₂.natPair.comp z m)
    refine Primrec.option_bind h₁ (?_ : Primrec _)
    have m := m.comp (Primrec.fst (β := Nat))
    refine Primrec.nat_casesOn Primrec.snd (Primrec.option_some.comp m) ?_
    unfold Primrec₂
    exact (hlup.comp ((L.comp Primrec.fst).pair <|
      ((k'.pair c).comp <| Primrec.fst.comp Primrec.fst).pair
        (Primrec₂.natPair.comp (z.comp Primrec.fst) (_root_.Primrec.succ.comp m)))).comp
      Primrec.fst

/--
theorem `evaln_map` / 定理 `evaln_map`

English:
theorem evaln_map
  given: (k c n)
  proof: by
  by_cases kn : n < k
  · simp [List.getElem?_range kn]
  · rw [List.getElem?_eq_none]
    · cases e : evaln k c n
      · rfl
      exact kn.elim (evaln_bound e)
    simpa using kn

中文:
定理 evaln_map
  条件: (k c n)
  证明: by
  by_cases kn : n < k
  · simp [List.getElem?_range kn]
  · rw [List.getElem?_eq_none]
    · cases e : evaln k c n
      · rfl
      exact kn.elim (evaln_bound e)
    simpa using kn
-/
private theorem evaln_map (k c n) :
    ((List.range k)[n]?.bind fun a => evaln k c a) = evaln k c n := by
  by_cases kn : n < k
  · simp [List.getElem?_range kn]
  · rw [List.getElem?_eq_none]
    · cases e : evaln k c n
      · rfl
      exact kn.elim (evaln_bound e)
    simpa using kn

set_option linter.flexible false in -- TODO: revisit this after #13791 is merged
/--
theorem `primrec_evaln` / 定理 `primrec_evaln`

English:
theorem primrec_evaln
  statement: Primrec fun a : (Nat × Code) × Nat => evaln a.1.1 a.1.2 a.2
  proof: have :
    Primrec₂ fun (_ : Unit) (n : Nat) =>
      let a := ofNat (Nat × Code) n
      (List.range a.1).map (evaln a.1 a.2) :=
    Primrec.nat_strong_rec _ (hG.comp Primrec.snd).to₂ fun _ p => by
      simp only [G, prod_ofNat_val, ofNat_nat, List.length_map, List.length_range,
        Nat.pair_u

中文:
定理 primrec_evaln
  结论: Primrec fun a : (自然数 × Code) × 自然数 => evaln a.1.1 a.1.2 a.2
  证明: have :
    Primrec₂ fun (_ : Unit) (n : Nat) =>
      let a := ofNat (Nat × Code) n
      (List.range a.1).map (evaln a.1 a.2) :=
    Primrec.nat_strong_rec _ (hG.comp Primrec.snd).to₂ fun _ p => by
      simp only [G, prod_ofNat_val, ofNat_nat, List.length_map, List.length_range,
        Nat.pair_u

Depends on / 依赖: List.length_map, List.length_range, List.map_congr_left, List.range, Nat.pair, Nat.pair_unpair, Option.some_inj, Primrec, Primrec.nat_strong_rec, Primrec.snd, encode, generalize, hG.comp, length_map, length_range, map_congr_left, nat_strong_rec, ofNat_nat, p.unpair, pair_unpair
-/
theorem primrec_evaln : Primrec fun a : (Nat × Code) × Nat => evaln a.1.1 a.1.2 a.2 :=
  have :
    Primrec₂ fun (_ : Unit) (n : Nat) =>
      let a := ofNat (Nat × Code) n
      (List.range a.1).map (evaln a.1 a.2) :=
    Primrec.nat_strong_rec _ (hG.comp Primrec.snd).to₂ fun _ p => by
      simp only [G, prod_ofNat_val, ofNat_nat, List.length_map, List.length_range,
        Nat.pair_unpair, Option.some_inj]
      refine List.map_congr_left fun n => ?_
      have : List.range p = List.range (Nat.pair p.unpair.1 (encode (ofNat Code p.unpair.2))) := by
        simp
      rw [this]
      generalize p.unpair.1 = k
      generalize ofNat Code p.unpair.2 = c
      intro nk
      rcases k with - | k'
      · simp [evaln]
      let k := k' + 1
      simp only
      simp only [List.mem_range, Nat.lt_succ_iff] at nk
      have hg :
        forall {k' c' n},
          Nat.pair k' (encode c') < Nat.pair k (encode c) ->
            lup ((List.range (Nat.pair k (encode c))).map fun n =>
              (List.range n.unpair.1).map (evaln n.unpair.1 (ofNat Code n.unpair.2))) (k', c') n =
            evaln k' c' n := by
        intro k₁ c₁ n₁ hl
        simp [lup, List.getElem?_range hl, evaln_map, Bind.bind, Option.bind_map]
      obtain - | - | - | - | ⟨cf, cg⟩ | ⟨cf, cg⟩ | ⟨cf, cg⟩ | cf := c <;>
        simp [evaln, nk, Bind.bind, Functor.map, Seq.seq, pure]
      · obtain ⟨lf, lg⟩ := encode_lt_pair cf cg
        rw [hg (Nat.pair_lt_pair_right _ lf)]; rw [hg (Nat.pair_lt_pair_right _ lg)]
        cases evaln k cf n
        · rfl
        cases evaln k cg n <;> rfl
      · obtain ⟨lf, lg⟩ := encode_lt_comp cf cg
        rw [hg (Nat.pair_lt_pair_right _ lg)]
        cases evaln k cg n
        · rfl
        simp [k, hg (Nat.pair_lt_pair_right _ lf)]
      · obtain ⟨lf, lg⟩ := encode_lt_prec cf cg
        rw [hg (Nat.pair_lt_pair_right _ lf)]
        cases n.unpair.2
        · rfl
        simp only
        rw [hg (Nat.pair_lt_pair_left _ k'.lt_succ_self)]
        cases evaln k' _ _
        · rfl
        simp [k, hg (Nat.pair_lt_pair_right _ lg)]
      · have lf := encode_lt_rfind' cf
        rw [hg (Nat.pair_lt_pair_right _ lf)]
        rcases evaln k cf n with - | x
        · rfl
        simp only [Option.bind_some]
        cases x <;> simp
        rw [hg (Nat.pair_lt_pair_left _ k'.lt_succ_self)]
  (Primrec.option_bind
    (Primrec.list_getElem?.comp (this.comp (_root_.Primrec.const ())
      (Primrec.encode_iff.2 Primrec.fst)) Primrec.snd) Primrec.snd.to₂).of_eq
    fun ⟨⟨k, c⟩, n⟩ => by simp [evaln_map, Option.bind_map]

end

section

open Computable

/--
theorem `eval_eq_rfindOpt` / 定理 `eval_eq_rfindOpt`

English:
theorem eval_eq_rfindOpt
  given: (c n)
  statement: eval c n = Nat.rfindOpt fun k => evaln k c n
  proof: Part.ext fun x => by
    refine evaln_complete.trans (Nat.rfindOpt_mono ?_).symm
    intro a m n hl; apply evaln_mono hl

中文:
定理 eval_eq_rfindOpt
  条件: (c n)
  结论: eval c n = 自然数.rfindOpt fun k => evaln k c n
  证明: Part.ext fun x => by
    refine evaln_complete.trans (Nat.rfindOpt_mono ?_).symm
    intro a m n hl; apply evaln_mono hl

Depends on / 依赖: Nat.rfindOpt_mono, Part.ext, evaln_complete, evaln_complete.trans, evaln_mono, rfindOpt_mono
-/
theorem eval_eq_rfindOpt (c n) : eval c n = Nat.rfindOpt fun k => evaln k c n :=
  Part.ext fun x => by
    refine evaln_complete.trans (Nat.rfindOpt_mono ?_).symm
    intro a m n hl; apply evaln_mono hl

/--
theorem `eval_part` / 定理 `eval_part`

English:
theorem eval_part
  statement: Partrec₂ eval
  proof: (Partrec.rfindOpt
    (primrec_evaln.to_comp.comp
      ((Computable.snd.pair (fst.comp fst)).pair (snd.comp fst))).to₂).of_eq
    fun a => by simp [eval_eq_rfindOpt]

中文:
定理 eval_part
  结论: Partrec₂ eval
  证明: (Partrec.rfindOpt
    (primrec_evaln.to_comp.comp
      ((Computable.snd.pair (fst.comp fst)).pair (snd.comp fst))).to₂).of_eq
    fun a => by simp [eval_eq_rfindOpt]

Depends on / 依赖: Computable, Computable.snd.pair, Partrec, Partrec.rfindOpt, eval_eq_rfindOpt, fst.comp, of_eq, primrec_evaln, primrec_evaln.to_comp.comp, rfindOpt, snd.comp, to_comp
-/
theorem eval_part : Partrec₂ eval :=
  (Partrec.rfindOpt
    (primrec_evaln.to_comp.comp
      ((Computable.snd.pair (fst.comp fst)).pair (snd.comp fst))).to₂).of_eq
    fun a => by simp [eval_eq_rfindOpt]

/--
theorem `fixed_point` / 定理 `fixed_point`

English:
theorem fixed_point
  given: {f : Code -> Code} (hf : Computable f)
  statement: exists c : Code, eval (f c) = eval c
  proof: let g (x y : Nat) : Part Nat := eval (ofNat Code x) x >>= fun b => eval (ofNat Code b) y
  have : Partrec₂ g :=
    (eval_part.comp ((Computable.ofNat _).comp fst) fst).bind
      (eval_part.comp ((Computable.ofNat _).comp snd) (snd.comp fst)).to₂
  let ⟨cg, eg⟩ := exists_code.1 this
  have eg' : fo

中文:
定理 fixed_point
  条件: {f : Code -> Code} (hf : Computable f)
  结论: 存在 c : Code, eval (f c) = eval c
  证明: let g (x y : Nat) : Part Nat := eval (ofNat Code x) x >>= fun b => eval (ofNat Code b) y
  have : Partrec₂ g :=
    (eval_part.comp ((Computable.ofNat _).comp fst) fst).bind
      (eval_part.comp ((Computable.ofNat _).comp snd) (snd.comp fst)).to₂
  let ⟨cg, eg⟩ := exists_code.1 this
  have eg' : fo

Depends on / 依赖: Computable, Computable.ofNat, Nat.pair, Part.map, Primrec, _curry.comp, _root_, _root_.Primrec.const, _root_.Primrec.id, encode, eval_part, eval_part.comp, exists_code, hf.comp, snd.comp
-/
theorem fixed_point {f : Code -> Code} (hf : Computable f) : exists c : Code, eval (f c) = eval c :=
  let g (x y : Nat) : Part Nat := eval (ofNat Code x) x >>= fun b => eval (ofNat Code b) y
  have : Partrec₂ g :=
    (eval_part.comp ((Computable.ofNat _).comp fst) fst).bind
      (eval_part.comp ((Computable.ofNat _).comp snd) (snd.comp fst)).to₂
  let ⟨cg, eg⟩ := exists_code.1 this
  have eg' : forall a n, eval cg (Nat.pair a n) = Part.map encode (g a n) := by simp [eg]
  let F (x : Nat) : Code := f (curry cg x)
  have : Computable F :=
    hf.comp (primrec₂_curry.comp (_root_.Primrec.const cg) _root_.Primrec.id).to_comp
  let ⟨cF, eF⟩ := exists_code.1 this
  have eF' : eval cF (encode cF) = Part.some (encode (F (encode cF))) := by simp [eF]
  ⟨curry cg (encode cF),
    funext fun n =>
      show eval (f (curry cg (encode cF))) n = eval (curry cg (encode cF)) n by
        simp [F, g, eg', eF', Part.map_id']⟩

/--
theorem `fixed_point₂` / 定理 `fixed_point₂`

English:
theorem fixed_point₂
  given: {f : Code -> Nat ->. Nat} (hf : Partrec₂ f)
  statement: exists c : Code, eval c = f c
  proof: let ⟨cf, ef⟩ := exists_code.1 hf
  (fixed_point (primrec₂_curry.comp (_root_.Primrec.const cf) Primrec.encode).to_comp).imp
    fun c e => funext fun n => by simp [e.symm, ef, Part.map_id']

中文:
定理 fixed_point₂
  条件: {f : Code -> 自然数 ->. 自然数} (hf : Partrec₂ f)
  结论: 存在 c : Code, eval c = f c
  证明: let ⟨cf, ef⟩ := exists_code.1 hf
  (fixed_point (primrec₂_curry.comp (_root_.Primrec.const cf) Primrec.encode).to_comp).imp
    fun c e => funext fun n => by simp [e.symm, ef, Part.map_id']

Depends on / 依赖: Part.map_id, Primrec, Primrec.encode, _curry.comp, _root_, _root_.Primrec.const, e.symm, encode, exists_code, fixed_point, map_id, to_comp
-/
theorem fixed_point₂ {f : Code -> Nat ->. Nat} (hf : Partrec₂ f) : exists c : Code, eval c = f c :=
  let ⟨cf, ef⟩ := exists_code.1 hf
  (fixed_point (primrec₂_curry.comp (_root_.Primrec.const cf) Primrec.encode).to_comp).imp
    fun c e => funext fun n => by simp [e.symm, ef, Part.map_id']

end

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Countable {f : Nat ->. Nat // Partrec f}
  body: by
  apply Function.Surjective.countable (f := fun c => ⟨eval c, eval_part.comp (.const c) .id⟩)
  intro ⟨f, hf⟩; simpa using! exists_code.1 hf

中文:
实例 :
  签名: Countable {f : 自然数 ->. 自然数 // Partrec f}
  定义体: by
  apply Function.Surjective.countable (f := fun c => ⟨eval c, eval_part.comp (.const c) .id⟩)
  intro ⟨f, hf⟩; simpa using! exists_code.1 hf

Depends on / 依赖: Function, Function.Surjective.countable, Surjective, countable, eval_part, eval_part.comp, exists_code
-/
instance : Countable {f : Nat ->. Nat // Partrec f} := by
  apply Function.Surjective.countable (f := fun c => ⟨eval c, eval_part.comp (.const c) .id⟩)
  intro ⟨f, hf⟩; simpa using! exists_code.1 hf

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Countable {f : Nat -> Nat // Computable f}
  body: @Function.Injective.countable {f : Nat -> Nat // Computable f} {f : Nat ->. Nat // Partrec f} _
    (fun f => ⟨f.val, f.2⟩)
    (fun _ _ h => Subtype.val_inj.1 (PFun.lift_injective (by simpa using h)))

中文:
实例 :
  签名: Countable {f : 自然数 -> 自然数 // Computable f}
  定义体: @Function.Injective.countable {f : Nat -> Nat // Computable f} {f : Nat ->. Nat // Partrec f} _
    (fun f => ⟨f.val, f.2⟩)
    (fun _ _ h => Subtype.val_inj.1 (PFun.lift_injective (by simpa using h)))

Depends on / 依赖: Computable, Function, Function.Injective.countable, Injective, PFun.lift_injective, Partrec, Subtype, Subtype.val_inj, countable, f.val, lift_injective, val_inj
-/
instance : Countable {f : Nat -> Nat // Computable f} :=
  @Function.Injective.countable {f : Nat -> Nat // Computable f} {f : Nat ->. Nat // Partrec f} _
    (fun f => ⟨f.val, f.2⟩)
    (fun _ _ h => Subtype.val_inj.1 (PFun.lift_injective (by simpa using h)))

end Nat.Partrec.Code
