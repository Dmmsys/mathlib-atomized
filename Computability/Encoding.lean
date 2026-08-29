/-
Copyright (c) 2020 Pim Spelier, Daan van Gent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pim Spelier, Daan van Gent
-/
module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Num.Lemmas
public import Mathlib.Data.Option.Basic
public import Mathlib.SetTheory.Cardinal.Basic
public import Mathlib.Tactic.DeriveFintype

/-!
# Encodings

This file contains the definition of an encoding, a map from a type to
strings in an alphabet, used in defining computability by Turing machines.
It also contains several examples:

## Examples

- `encodingNatBool` : a binary encoding of `ℕ` in a simple alphabet.
- `encodingNatΓ'` : a binary encoding of `ℕ` in the alphabet used for TM's.
- `unaryEncodingNat` : a unary encoding of `ℕ`
- `encodingBoolBool` : an encoding of `Bool`.
- `encodingList` : an encoding of `List α` in the alphabet `α`.
- `encodingProd` : an encoding of `α × β` from encodings of `α` and `β`.
-/

@[expose] public section

universe u v

open Cardinal

namespace Computability

/--
Definition of `Encoding` / `Encoding` 的定义

English:
structure Encoding
  parameters: (α : Type u) (Γ : Type v)
  axioms and operations (3):
    - encode : α -> List Γ
    - decode : List Γ -> Option α
    - decode_encode : forall x, decode (encode x) = some x

中文:
结构 Encoding
  参数: (α : 类型u) (Γ : 类型v)
  公理与运算 (3 个):
    - encode : α -> 列表 Γ
    - decode : 列表 Γ -> 选项类型 α
    - decode_encode : 对任意 x, decode (encode x) = some x

Depends on / 依赖: eq_of_forall_ge_iff, forall_comm
-/
structure Encoding (α : Type u) (Γ : Type v) where
  /-- The encoding function -/
  encode : α -> List Γ
  /-- The decoding function -/
  decode : List Γ -> Option α
  /-- Decoding and encoding are inverses of each other. -/
  decode_encode : forall x, decode (encode x) = some x

attribute [simp] Encoding.decode_encode

/--
theorem `Encoding.encode_injective` / 定理 `Encoding.encode_injective`

English:
theorem Encoding.encode_injective
  given: {α Γ} (e : Encoding α Γ)
  statement: Function.Injective e.encode
  proof: by
  refine fun _ _ h => Option.some_injective _ ?_
  rw [← e.decode_encode]; rw [← e.decode_encode]; rw [h]

中文:
定理 Encoding.encode_injective
  条件: {α Γ} (e : Encoding α Γ)
  结论: 函数.单射 e.encode
  证明: by
  refine fun _ _ h => Option.some_injective _ ?_
  rw [← e.decode_encode]; rw [← e.decode_encode]; rw [h]

Depends on / 依赖: Option.some_injective, _biUnion, decode_encode, e.decode_encode, some_injective
-/
theorem Encoding.encode_injective {α Γ} (e : Encoding α Γ) : Function.Injective e.encode := by
  refine fun _ _ h => Option.some_injective _ ?_
  rw [← e.decode_encode]; rw [← e.decode_encode]; rw [h]

/--
Inductive type `Γ'` / 归纳类型 `Γ'`

English:
inductive Γ'
  constructors (5):
    - blank: 
    - bit: (b : Bool)
    - bra: 
    - ket: 
    - comma: 

中文:
归纳类型 Γ'
  构造子 (5 个):
    - blank: 
    - bit: (b : 布尔值)
    - bra: 
    - ket: 
    - comma: 
-/
inductive Γ'
  | blank
  | bit (b : Bool)
  | bra
  | ket
  | comma
  deriving DecidableEq, Fintype

/--
Instance `inhabitedΓ'` / 实例 `inhabitedΓ'`

English:
instance inhabitedΓ'
  signature: : Inhabited Γ'
  body: ⟨Γ'.blank⟩

中文:
实例 inhabitedΓ'
  签名: : 可居 Γ'
  定义体: ⟨Γ'.blank⟩
-/
instance inhabitedΓ' : Inhabited Γ' :=
  ⟨Γ'.blank⟩

/--
Definition of `inclusionBoolΓ'` / `inclusionBoolΓ'` 的定义

English:
definition inclusionBoolΓ'
  signature: : Bool -> Γ'
  body: Γ'.bit

中文:
定义 inclusion布尔Γ'
  签名: : 布尔值 -> Γ'
  定义体: Γ'.bit
-/
def inclusionBoolΓ' : Bool -> Γ' :=
  Γ'.bit

/--
Definition of `sectionΓ'Bool` / `sectionΓ'Bool` 的定义

English:
definition sectionΓ'Bool
  signature: : Γ' -> Bool

中文:
定义 sectionΓ'布尔值
  签名: : Γ' -> 布尔值
-/
def sectionΓ'Bool : Γ' -> Bool
  | Γ'.bit b => b
  | _ => Inhabited.default

@[simp]
/--
theorem `sectionΓ'Bool_inclusionBoolΓ'` / 定理 `sectionΓ'Bool_inclusionBoolΓ'`

English:
theorem sectionΓ'Bool_inclusionBoolΓ'
  given: {b}
  statement: sectionΓ'Bool (inclusionBoolΓ' b) = b
  proof: by
  cases b <;> rfl

中文:
定理 sectionΓ'布尔_inclusion布尔Γ'
  条件: {b}
  结论: sectionΓ'布尔值 (inclusion布尔Γ' b) = b
  证明: by
  cases b <;> rfl
-/
theorem sectionΓ'Bool_inclusionBoolΓ' {b} : sectionΓ'Bool (inclusionBoolΓ' b) = b := by
  cases b <;> rfl

/--
theorem `inclusionBoolΓ'_injective` / 定理 `inclusionBoolΓ'_injective`

English:
theorem inclusionBoolΓ'_injective
  statement: Function.Injective inclusionBoolΓ'
  proof: Function.HasLeftInverse.injective ⟨_, (fun _ => sectionΓ'Bool_inclusionBoolΓ')⟩

中文:
定理 inclusion布尔Γ'_injective
  结论: 函数.单射 inclusion布尔Γ'
  证明: Function.HasLeftInverse.injective ⟨_, (fun _ => sectionΓ'Bool_inclusionBoolΓ')⟩
-/
theorem inclusionBoolΓ'_injective : Function.Injective inclusionBoolΓ' :=
  Function.HasLeftInverse.injective ⟨_, (fun _ => sectionΓ'Bool_inclusionBoolΓ')⟩

/--
Definition of `encodePosNum` / `encodePosNum` 的定义

English:
definition encodePosNum
  signature: : PosNum -> List Bool

中文:
定义 encodePosNum
  签名: : PosNum -> 列表 布尔值
-/
def encodePosNum : PosNum -> List Bool
  | PosNum.one => [true]
  | PosNum.bit0 n => false :: encodePosNum n
  | PosNum.bit1 n => true :: encodePosNum n

/--
Definition of `encodeNum` / `encodeNum` 的定义

English:
definition encodeNum
  signature: : Num -> List Bool

中文:
定义 encodeNum
  签名: : Num -> 列表 布尔值
-/
def encodeNum : Num -> List Bool
  | Num.zero => []
  | Num.pos n => encodePosNum n

/--
Definition of `encodeNat` / `encodeNat` 的定义

English:
definition encodeNat
  signature: (n : Nat)
  body: encodeNum n

中文:
定义 encode自然数
  签名: (n : 自然数)
  定义体: encodeNum n

Depends on / 依赖: encodeNum
-/
def encodeNat (n : Nat) : List Bool :=
  encodeNum n

/--
Definition of `decodePosNum` / `decodePosNum` 的定义

English:
definition decodePosNum
  signature: : List Bool -> PosNum

中文:
定义 decodePosNum
  签名: : 列表 布尔值 -> PosNum
-/
def decodePosNum : List Bool -> PosNum
  | false :: l => PosNum.bit0 (decodePosNum l)
  | true :: l => ite (l = []) PosNum.one (PosNum.bit1 (decodePosNum l))
  | _ => PosNum.one

/--
Definition of `decodeNum` / `decodeNum` 的定义

English:
definition decodeNum
  signature: : List Bool -> Num
  body: fun l => ite (l = []) Num.zero decodePosNum l

中文:
定义 decodeNum
  签名: : 列表 布尔值 -> Num
  定义体: fun l => ite (l = []) Num.zero decodePosNum l

Depends on / 依赖: Num.zero, decodePosNum
-/
def decodeNum : List Bool -> Num := fun l => ite (l = []) Num.zero decodePosNum l

/--
Definition of `decodeNat` / `decodeNat` 的定义

English:
definition decodeNat
  signature: : List Bool -> Nat
  body: fun l => decodeNum l

中文:
定义 decode自然数
  签名: : 列表 布尔值 -> 自然数
  定义体: fun l => decodeNum l

Depends on / 依赖: decodeNum
-/
def decodeNat : List Bool -> Nat := fun l => decodeNum l

/--
theorem `encodePosNum_nonempty` / 定理 `encodePosNum_nonempty`

English:
theorem encodePosNum_nonempty
  given: (n : PosNum)
  statement: encodePosNum n != []
  proof: PosNum.casesOn n (List.cons_ne_nil _ _) (fun _m => List.cons_ne_nil _ _) fun _m =>
    List.cons_ne_nil _ _

中文:
定理 encodePosNum_nonempty
  条件: (n : PosNum)
  结论: encodePosNum n != []
  证明: PosNum.casesOn n (List.cons_ne_nil _ _) (fun _m => List.cons_ne_nil _ _) fun _m =>
    List.cons_ne_nil _ _

Depends on / 依赖: List.cons_ne_nil, PosNum, PosNum.casesOn, casesOn, cons_ne_nil
-/
theorem encodePosNum_nonempty (n : PosNum) : encodePosNum n != [] :=
  PosNum.casesOn n (List.cons_ne_nil _ _) (fun _m => List.cons_ne_nil _ _) fun _m =>
    List.cons_ne_nil _ _

/--
theorem `decode_encodePosNum` / 定理 `decode_encodePosNum`

English:
theorem decode_encodePosNum
  given: (n)
  statement: decodePosNum (encodePosNum n) = n
  proof: by
  induction n with unfold encodePosNum decodePosNum
  | one => rfl
  | bit1 m hm =>
    rw [hm]
    exact if_neg (encodePosNum_nonempty m)
  | bit0 m hm => exact congr_arg PosNum.bit0 hm

中文:
定理 decode_encodePosNum
  条件: (n)
  结论: decodePosNum (encodePosNum n) = n
  证明: by
  induction n with unfold encodePosNum decodePosNum
  | one => rfl
  | bit1 m hm =>
    rw [hm]
    exact if_neg (encodePosNum_nonempty m)
  | bit0 m hm => exact congr_arg PosNum.bit0 hm
-/
@[simp] theorem decode_encodePosNum (n) : decodePosNum (encodePosNum n) = n := by
  induction n with unfold encodePosNum decodePosNum
  | one => rfl
  | bit1 m hm =>
    rw [hm]
    exact if_neg (encodePosNum_nonempty m)
  | bit0 m hm => exact congr_arg PosNum.bit0 hm

/--
theorem `decode_encodeNum` / 定理 `decode_encodeNum`

English:
theorem decode_encodeNum
  given: (n)
  statement: decodeNum (encodeNum n) = n
  proof: by
  obtain - | n := n <;> unfold encodeNum decodeNum
  · rfl
  rw [decode_encodePosNum n]
  rw [PosNum.cast_to_num]
  exact if_neg (encodePosNum_nonempty n)

中文:
定理 decode_encodeNum
  条件: (n)
  结论: decodeNum (encodeNum n) = n
  证明: by
  obtain - | n := n <;> unfold encodeNum decodeNum
  · rfl
  rw [decode_encodePosNum n]
  rw [PosNum.cast_to_num]
  exact if_neg (encodePosNum_nonempty n)
-/
@[simp] theorem decode_encodeNum (n) : decodeNum (encodeNum n) = n := by
  obtain - | n := n <;> unfold encodeNum decodeNum
  · rfl
  rw [decode_encodePosNum n]
  rw [PosNum.cast_to_num]
  exact if_neg (encodePosNum_nonempty n)

/--
theorem `decode_encodeNat` / 定理 `decode_encodeNat`

English:
theorem decode_encodeNat
  given: (n)
  statement: decodeNat (encodeNat n) = n
  proof: by
  conv_rhs => rw [← Num.to_of_nat n]
  exact congr_arg ((↑) : Num -> Nat) (decode_encodeNum n)

中文:
定理 decode_encode自然数
  条件: (n)
  结论: decode自然数 (encode自然数 n) = n
  证明: by
  conv_rhs => rw [← Num.to_of_nat n]
  exact congr_arg ((↑) : Num -> Nat) (decode_encodeNum n)
-/
@[simp] theorem decode_encodeNat (n) : decodeNat (encodeNat n) = n := by
  conv_rhs => rw [← Num.to_of_nat n]
  exact congr_arg ((↑) : Num -> Nat) (decode_encodeNum n)

/--
Definition of `encodingNatBool` / `encodingNatBool` 的定义

English:
definition encodingNatBool
  signature: : Encoding Nat Bool where
  body: encodeNat
  decode n := some (decodeNat n)
  decode_encode n := congr_arg _ (decode_encodeNat n)

中文:
定义 encoding自然数布尔
  签名: : Encoding 自然数 布尔值 where
  定义体: encodeNat
  decode n := some (decodeNat n)
  decode_encode n := congr_arg _ (decode_encodeNat n)

Depends on / 依赖: encodeNat
-/
def encodingNatBool : Encoding Nat Bool where
  encode := encodeNat
  decode n := some (decodeNat n)
  decode_encode n := congr_arg _ (decode_encodeNat n)

/--
Definition of `encodingNatΓ'` / `encodingNatΓ'` 的定义

English:
definition encodingNatΓ'
  signature: : Encoding Nat Γ' where
  body: List.map inclusionBoolΓ' (encodeNat x)
  decode x := some (decodeNat (List.map sectionΓ'Bool x))
decode_encode x := congr_arg _ by simp [Function.comp_def]

中文:
定义 encoding自然数Γ'
  签名: : Encoding 自然数 Γ' where
  定义体: List.map inclusionBoolΓ' (encodeNat x)
  decode x := some (decodeNat (List.map sectionΓ'Bool x))
decode_encode x := congr_arg _ by simp [Function.comp_def]

Depends on / 依赖: List.map, encodeNat
-/
def encodingNatΓ' : Encoding Nat Γ' where
  encode x := List.map inclusionBoolΓ' (encodeNat x)
  decode x := some (decodeNat (List.map sectionΓ'Bool x))
decode_encode x := congr_arg _ by simp [Function.comp_def]

/--
Definition of `unaryEncodeNat` / `unaryEncodeNat` 的定义

English:
definition unaryEncodeNat
  signature: : Nat -> List Bool

中文:
定义 unaryEncode自然数
  签名: : 自然数 -> 列表 布尔值
-/
def unaryEncodeNat : Nat -> List Bool
  | 0 => []
  | n + 1 => true :: unaryEncodeNat n

/--
Definition of `unaryDecodeNat` / `unaryDecodeNat` 的定义

English:
definition unaryDecodeNat
  signature: : List Bool -> Nat
  body: List.length

中文:
定义 unaryDecode自然数
  签名: : 列表 布尔值 -> 自然数
  定义体: List.length

Depends on / 依赖: List.length, length
-/
def unaryDecodeNat : List Bool -> Nat :=
  List.length

/--
theorem `unary_decode_encode_nat` / 定理 `unary_decode_encode_nat`

English:
theorem unary_decode_encode_nat
  statement: forall n, unaryDecodeNat (unaryEncodeNat n) = n
  proof: fun n =>
  Nat.rec rfl (fun (_m : Nat) hm => (congr_arg Nat.succ hm.symm).symm) n

中文:
定理 unary_decode_encode_nat
  结论: 对任意 n, unaryDecode自然数 (unaryEncode自然数 n) = n
  证明: fun n =>
  Nat.rec rfl (fun (_m : Nat) hm => (congr_arg Nat.succ hm.symm).symm) n
-/
@[simp] theorem unary_decode_encode_nat : forall n, unaryDecodeNat (unaryEncodeNat n) = n := fun n =>
  Nat.rec rfl (fun (_m : Nat) hm => (congr_arg Nat.succ hm.symm).symm) n

/--
Definition of `unaryEncodingNat` / `unaryEncodingNat` 的定义

English:
definition unaryEncodingNat
  signature: : Encoding Nat Bool where
  body: unaryEncodeNat
  decode n := some (unaryDecodeNat n)
  decode_encode n := congr_arg _ (unary_decode_encode_nat n)

中文:
定义 unaryEncoding自然数
  签名: : Encoding 自然数 布尔值 where
  定义体: unaryEncodeNat
  decode n := some (unaryDecodeNat n)
  decode_encode n := congr_arg _ (unary_decode_encode_nat n)

Depends on / 依赖: unaryEncodeNat
-/
def unaryEncodingNat : Encoding Nat Bool where
  encode := unaryEncodeNat
  decode n := some (unaryDecodeNat n)
  decode_encode n := congr_arg _ (unary_decode_encode_nat n)

/--
Definition of `encodeBool` / `encodeBool` 的定义

English:
definition encodeBool
  signature: : Bool -> List Bool
  body: pure

中文:
定义 encode布尔
  签名: : 布尔值 -> 列表 布尔值
  定义体: pure
-/
def encodeBool : Bool -> List Bool := pure

/--
Definition of `decodeBool` / `decodeBool` 的定义

English:
definition decodeBool
  signature: : List Bool -> Bool

中文:
定义 decode布尔
  签名: : 列表 布尔值 -> 布尔值
-/
def decodeBool : List Bool -> Bool
  | b :: _ => b
  | _ => Inhabited.default

/--
theorem `decode_encodeBool` / 定理 `decode_encodeBool`

English:
theorem decode_encodeBool
  given: (b : Bool)
  statement: decodeBool (encodeBool b) = b
  proof: rfl

中文:
定理 decode_encode布尔
  条件: (b : 布尔值)
  结论: decode布尔 (encode布尔 b) = b
  证明: rfl
-/
@[simp] theorem decode_encodeBool (b : Bool) : decodeBool (encodeBool b) = b := rfl

/--
Definition of `encodingBoolBool` / `encodingBoolBool` 的定义

English:
definition encodingBoolBool
  signature: : Encoding Bool Bool where
  body: encodeBool
  decode x := some (decodeBool x)
  decode_encode x := congr_arg _ (decode_encodeBool x)

中文:
定义 encoding布尔布尔
  签名: : Encoding 布尔值 布尔值 where
  定义体: encodeBool
  decode x := some (decodeBool x)
  decode_encode x := congr_arg _ (decode_encodeBool x)

Depends on / 依赖: encodeBool
-/
def encodingBoolBool : Encoding Bool Bool where
  encode := encodeBool
  decode x := some (decodeBool x)
  decode_encode x := congr_arg _ (decode_encodeBool x)

/--
Instance `inhabitedEncoding` / 实例 `inhabitedEncoding`

English:
instance inhabitedEncoding
  signature: : Inhabited (Encoding Bool Bool)
  body: ⟨encodingBoolBool⟩

中文:
实例 inhabitedEncoding
  签名: : 可居 (Encoding 布尔值 布尔值)
  定义体: ⟨encodingBoolBool⟩

Depends on / 依赖: encodingBoolBool
-/
instance inhabitedEncoding : Inhabited (Encoding Bool Bool) :=
  ⟨encodingBoolBool⟩

/--
theorem `Encoding.card_le_card_list` / 定理 `Encoding.card_le_card_list`

English:
theorem Encoding.card_le_card_list
  given: {α : Type u} {Γ : Type v} (e : Encoding α Γ)
  proof: Cardinal.lift_mk_le'.2 ⟨⟨e.encode, e.encode_injective⟩⟩

中文:
定理 Encoding.card_le_card_list
  条件: {α : 类型u} {Γ : 类型v} (e : Encoding α Γ)
  证明: Cardinal.lift_mk_le'.2 ⟨⟨e.encode, e.encode_injective⟩⟩

Depends on / 依赖: Cardinal, Cardinal.lift_mk_le, e.encode, e.encode_injective, encode, encode_injective, lift_mk_le
-/
theorem Encoding.card_le_card_list {α : Type u} {Γ : Type v} (e : Encoding α Γ) :
    Cardinal.lift.{v} #α <= Cardinal.lift.{u} #(List Γ) :=
  Cardinal.lift_mk_le'.2 ⟨⟨e.encode, e.encode_injective⟩⟩

/--
theorem `Encoding.card_le_aleph0` / 定理 `Encoding.card_le_aleph0`

English:
theorem Encoding.card_le_aleph0
  given: {α Γ} (e : Encoding α Γ) [Countable Γ]
  proof: haveI : Countable α := e.encode_injective.countable
  Cardinal.mk_le_aleph0

中文:
定理 Encoding.card_le_aleph0
  条件: {α Γ} (e : Encoding α Γ) [可数 Γ]
  证明: haveI : Countable α := e.encode_injective.countable
  Cardinal.mk_le_aleph0

Depends on / 依赖: Cardinal, Cardinal.mk_le_aleph0, Countable, countable, e.encode_injective.countable, encode_injective, mk_le_aleph0
-/
theorem Encoding.card_le_aleph0 {α Γ} (e : Encoding α Γ) [Countable Γ] :
    #α <= ℵ₀ :=
  haveI : Countable α := e.encode_injective.countable
  Cardinal.mk_le_aleph0

/--
Definition of `encodingList` / `encodingList` 的定义

English:
definition encodingList
  signature: (α : Type)
  body: id
  decode := Option.some
  decode_encode _ := rfl

中文:
定义 encodingList
  签名: (α : 类型)
  定义体: id
  decode := Option.some
  decode_encode _ := rfl
-/
def encodingList (α : Type) : Encoding (List α) α where
  encode := id
  decode := Option.some
  decode_encode _ := rfl

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `encodingProd` / `encodingProd` 的定义

English:
definition encodingProd
  signature: {α β Γ₁ Γ₂ : Type*} (ea : Encoding α Γ₁) (eb : Encoding β Γ₂)
  body: (ea.encode x.1).map .inl ++ (eb.encode x.2).map .inr
  decode x := Option.map₂ Prod.mk (ea.decode (x.filterMap Sum.getLeft?))
      (eb.decode (x.filterMap Sum.getRight?))
  decode_encode x := by simp

中文:
定义 encodingProd
  签名: {α β Γ₁ Γ₂ : 类型} (ea : Encoding α Γ₁) (eb : Encoding β Γ₂)
  定义体: (ea.encode x.1).map .inl ++ (eb.encode x.2).map .inr
  decode x := Option.map₂ Prod.mk (ea.decode (x.filterMap Sum.getLeft?))
      (eb.decode (x.filterMap Sum.getRight?))
  decode_encode x := by simp

Depends on / 依赖: ea.encode, eb.encode, encode
-/
def encodingProd {α β Γ₁ Γ₂ : Type*} (ea : Encoding α Γ₁) (eb : Encoding β Γ₂) :
    Encoding (α × β) (Γ₁ oplus Γ₂) where
  encode x := (ea.encode x.1).map .inl ++ (eb.encode x.2).map .inr
  decode x := Option.map₂ Prod.mk (ea.decode (x.filterMap Sum.getLeft?))
      (eb.decode (x.filterMap Sum.getRight?))
  decode_encode x := by simp

/-! ### Deprecated aliases for `FinEncoding` and unbundled `Γ` -/

/-- Deprecated: Use `Encoding α Γ` along with `[Fintype Γ]` instead. -/
@[reducible, nolint unusedArguments,
  deprecated "Use `Encoding α Γ` along with `[Fintype Γ]` instead" (since := "2026-05-07")]
/--
Definition of `FinEncoding` / `FinEncoding` 的定义

English:
definition FinEncoding
  signature: (α : Type u) {Γ : Type v} [Fintype Γ]
  body: Encoding α Γ

中文:
定义 FinEncoding
  签名: (α : 类型u) {Γ : 类型v} [有限类型 Γ]
  定义体: Encoding α Γ

Depends on / 依赖: Encoding
-/
def FinEncoding (α : Type u) {Γ : Type v} [Fintype Γ] := Encoding α Γ

/-- Deprecated: `Γ` is now an explicit parameter of `Encoding`. -/
@[reducible, nolint unusedArguments,
  deprecated "Γ is now an explicit parameter of `Encoding`" (since := "2026-05-07")]
/--
Definition of `Encoding.Γ` / `Encoding.Γ` 的定义

English:
definition Encoding.Γ
  signature: {α : Type u} {Γ : Type v} (_ : Encoding α Γ)
  body: Γ

中文:
定义 Encoding.Γ
  签名: {α : 类型u} {Γ : 类型v} (_ : Encoding α Γ)
  定义体: Γ
-/
def Encoding.Γ {α : Type u} {Γ : Type v} (_ : Encoding α Γ) : Type v := Γ

/-- Deprecated: Use `inferInstanceAs (Fintype Γ)` instead. -/
@[reducible, nolint unusedArguments,
  deprecated "Use `inferInstanceAs (Fintype Γ)` instead" (since := "2026-05-07")]
/--
Definition of `FinEncoding.ΓFin` / `FinEncoding.ΓFin` 的定义

English:
definition FinEncoding.ΓFin
  signature: {α : Type u} {Γ : Type v} [h : Fintype Γ]
  body: h

中文:
定义 FinEncoding.ΓFin
  签名: {α : 类型u} {Γ : 类型v} [h : 有限类型 Γ]
  定义体: h
-/
def FinEncoding.ΓFin {α : Type u} {Γ : Type v} [h : Fintype Γ]
    (_ : Encoding α Γ) : Fintype Γ := h

/-- Deprecated: Use the encoding directly. -/
@[reducible, nolint unusedArguments,
  deprecated "Use the encoding directly" (since := "2026-05-07")]
/--
Definition of `FinEncoding.toEncoding` / `FinEncoding.toEncoding` 的定义

English:
definition FinEncoding.toEncoding
  signature: {α : Type u} {Γ : Type v} [Fintype Γ]
  body: e

中文:
定义 FinEncoding.toEncoding
  签名: {α : 类型u} {Γ : 类型v} [有限类型 Γ]
  定义体: e
-/
def FinEncoding.toEncoding {α : Type u} {Γ : Type v} [Fintype Γ]
    (e : Encoding α Γ) : Encoding α Γ := e

/-- Deprecated alias for `encodingNatBool`. -/
@[deprecated encodingNatBool (since := "2026-05-07")]
/--
Definition of `finEncodingNatBool` / `finEncodingNatBool` 的定义

English:
abbreviation finEncodingNatBool
  body: encodingNatBool

中文:
缩写 finEncoding自然数布尔
  定义体: encodingNatBool

Depends on / 依赖: encodingNatBool
-/
abbrev finEncodingNatBool := encodingNatBool

/-- Deprecated alias for `encodingNatΓ'`. -/
@[deprecated encodingNatΓ' (since := "2026-05-07")]
/--
Definition of `finEncodingNatΓ'` / `finEncodingNatΓ'` 的定义

English:
abbreviation finEncodingNatΓ'
  body: encodingNatΓ'

中文:
缩写 finEncoding自然数Γ'
  定义体: encodingNatΓ'
-/
abbrev finEncodingNatΓ' := encodingNatΓ'

/-- Deprecated alias for `unaryEncodingNat`. -/
@[deprecated unaryEncodingNat (since := "2026-05-07")]
/--
Definition of `unaryFinEncodingNat` / `unaryFinEncodingNat` 的定义

English:
abbreviation unaryFinEncodingNat
  body: unaryEncodingNat

中文:
缩写 unaryFinEncoding自然数
  定义体: unaryEncodingNat

Depends on / 依赖: unaryEncodingNat
-/
abbrev unaryFinEncodingNat := unaryEncodingNat

/-- Deprecated alias for `encodingBoolBool`. -/
@[deprecated encodingBoolBool (since := "2026-05-07")]
/--
Definition of `finEncodingBoolBool` / `finEncodingBoolBool` 的定义

English:
abbreviation finEncodingBoolBool
  body: encodingBoolBool

中文:
缩写 finEncoding布尔布尔
  定义体: encodingBoolBool

Depends on / 依赖: encodingBoolBool
-/
abbrev finEncodingBoolBool := encodingBoolBool

/-- Deprecated alias for `encodingList`. -/
@[reducible, nolint unusedArguments,
  deprecated encodingList (since := "2026-05-07")]
/--
Definition of `finEncodingList` / `finEncodingList` 的定义

English:
definition finEncodingList
  signature: (α : Type) [Fintype α]
  body: encodingList α

中文:
定义 finEncodingList
  签名: (α : 类型) [有限类型 α]
  定义体: encodingList α

Depends on / 依赖: encodingList
-/
def finEncodingList (α : Type) [Fintype α] := encodingList α

/-- Deprecated alias for `encodingProd`. -/
@[reducible, nolint unusedArguments,
  deprecated encodingProd (since := "2026-05-07")]
/--
Definition of `finEncodingPair` / `finEncodingPair` 的定义

English:
definition finEncodingPair
  signature: {α β Γ₁ Γ₂ : Type*} [Fintype Γ₁] [Fintype Γ₂]
  body: encodingProd ea eb

中文:
定义 finEncodingPair
  签名: {α β Γ₁ Γ₂ : 类型} [有限类型 Γ₁] [有限类型 Γ₂]
  定义体: encodingProd ea eb

Depends on / 依赖: encodingProd
-/
def finEncodingPair {α β Γ₁ Γ₂ : Type*} [Fintype Γ₁] [Fintype Γ₂]
    (ea : Encoding α Γ₁) (eb : Encoding β Γ₂) :=
  encodingProd ea eb

/-- Deprecated alias for `Encoding.card_le_aleph0`. -/
@[deprecated Encoding.card_le_aleph0 (since := "2026-05-07")]
/--
theorem `FinEncoding.card_le_aleph0` / 定理 `FinEncoding.card_le_aleph0`

English:
theorem FinEncoding.card_le_aleph0
  given: {α Γ} [Countable Γ] (e : Encoding α Γ)
  statement: #α <= ℵ₀
  proof: e.card_le_aleph0

中文:
定理 FinEncoding.card_le_aleph0
  条件: {α Γ} [可数 Γ] (e : Encoding α Γ)
  结论: #α <= ℵ₀
  证明: e.card_le_aleph0

Depends on / 依赖: card_le_aleph0, e.card_le_aleph0
-/
theorem FinEncoding.card_le_aleph0 {α Γ} [Countable Γ] (e : Encoding α Γ) : #α <= ℵ₀ :=
  e.card_le_aleph0

end Computability
