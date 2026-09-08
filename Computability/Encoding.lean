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

- `encodingNatBool`  : a binary encoding of `ℕ` in a simple alphabet.
- `encodingNatΓ'`    : a binary encoding of `ℕ` in the alphabet used for TM's.
- `unaryEncodingNat` : a unary encoding of `ℕ`
- `encodingBoolBool` : an encoding of `Bool`.
- `encodingList`     : an encoding of `List α` in the alphabet `α`.
- `encodingProd`     : an encoding of `α × β` from encodings of `α` and `β`.
-/

@[expose] public section

universe u v

open Cardinal

namespace Computability

/-- An encoding of a type in a certain alphabet, together with a decoding. -/
/-
**Computability.Encoding** 是 Mathlib 中的一个归纳类型，位于命名空间 `Computability`。
形式化陈述：Type u → Type v → Type (max u v)
参数：max u v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An encoding of a type in a certain alphabet, together with a decoding.
-/
structure Encoding (α : Type u) (Γ : Type v) where
  /-- The encoding function -/
  encode : α → List Γ
  /-- The decoding function -/
  decode : List Γ → Option α
  /-- Decoding and encoding are inverses of each other. -/
  decode_encode : ∀ x, decode (encode x) = some x

attribute [simp] Encoding.decode_encode
/-
**Computability.Encoding.encode_injective** 是 Mathlib 中的一个定理，位于命名空间 `Computabili
ty.Encoding`。
形式化陈述：∀ {α : Type u_1} {Γ : Type u_2} (e : Computability.Encoding α Γ), Function
.Injective e.encode
参数：e : Computability.Encoding α Γ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Option.some_injective`：some_injective (α : Type*) : Function.Injective (
@some α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Computability.Encoding.decode_encode`：∀ {α : Type u} {Γ : Type v} (self 
: Computability.Encoding α Γ) (x : α), self.decode (self.encode x) = some x
-/
theorem Encoding.encode_injective {α Γ} (e : Encoding α Γ) : Function.Injective e.encode := by
  refine fun _ _ h => Option.some_injective _ ?_
  rw [← e.decode_encode, ← e.decode_encode, h]

/-- A standard Turing machine alphabet, consisting of blank,bit0,bit1,bra,ket,comma. -/
/-
**Computability.** 是 Mathlib 中的一个归纳类型，位于命名空间 `Computability`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A standard Turing machine alphabet, consisting of blank,bit0,bit1,bra,ket,comma.
-/
inductive Γ'
  | blank
  | bit (b : Bool)
  | bra
  | ket
  | comma
  deriving DecidableEq, Fintype
/-
**Computability.inhabited** 是 Mathlib 中的一个实例，位于命名空间 `Computability`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inhabitedΓ' : Inhabited Γ' :=
  ⟨Γ'.blank⟩

/-- The natural inclusion of `Bool` in `Γ'`. -/
/-
**Computability.inclusionBool** 是 Mathlib 中的一个定义，位于命名空间 `Computability`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural inclusion of `Bool` in `Γ'`.
-/
def inclusionBoolΓ' : Bool → Γ' :=
  Γ'.bit

/-- An arbitrary section of the natural inclusion of `Bool` in `Γ'`. -/
/-
**Computability.section** 是 Mathlib 中的一个定义，位于命名空间 `Computability`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An arbitrary section of the natural inclusion of `Bool` in `Γ'`.
-/
def sectionΓ'Bool : Γ' → Bool
  | Γ'.bit b => b
  | _ => Inhabited.default

@[simp]
/-
**Computability.section** 是 Mathlib 中的一个定理，位于命名空间 `Computability`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sectionΓ'Bool_inclusionBoolΓ' {b} : sectionΓ'Bool (inclusionBoolΓ' b) = b := by
  cases b <;> rfl
/-
**Computability.inclusionBool** 是 Mathlib 中的一个定理，位于命名空间 `Computability`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inclusionBoolΓ'_injective : Function.Injective inclusionBoolΓ' :=
  Function.HasLeftInverse.injective ⟨_, (fun _ => sectionΓ'Bool_inclusionBoolΓ')⟩

/-- An encoding function of the positive binary numbers in `Bool`. -/
/-
**Computability.encodePosNum** 是 Mathlib 中的一个定义，位于命名空间 `Computability`。
形式化陈述：PosNum → List Bool
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An encoding function of the positive binary numbers in `Bool`.
-/
def encodePosNum : PosNum → List Bool
  | PosNum.one => [true]
  | PosNum.bit0 n => false :: encodePosNum n
  | PosNum.bit1 n => true :: encodePosNum n

/-- An encoding function of the binary numbers in `Bool`. -/
/-
**Computability.encodeNum** 是 Mathlib 中的一个定义，位于命名空间 `Computability`。
形式化陈述：Num → List Bool
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An encoding function of the binary numbers in `Bool`.
-/
def encodeNum : Num → List Bool
  | Num.zero => []
  | Num.pos n => encodePosNum n

/-- An encoding function of `ℕ` in `Bool`. -/
/-
**Computability.encodeNat** 是 Mathlib 中的一个定义，位于命名空间 `Computability`。
形式化陈述：encodeNat (n : Nat) : List Bool
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An encoding function of `ℕ` in `Bool`.
-/
def encodeNat (n : ℕ) : List Bool :=
  encodeNum n

/-- A decoding function from `List Bool` to the positive binary numbers. -/
/-
**Computability.decodePosNum** 是 Mathlib 中的一个定义，位于命名空间 `Computability`。
形式化陈述：List Bool → PosNum
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A decoding function from `List Bool` to the positive binary numbers.
-/
def decodePosNum : List Bool → PosNum
  | false :: l => PosNum.bit0 (decodePosNum l)
  | true  :: l => ite (l = []) PosNum.one (PosNum.bit1 (decodePosNum l))
  | _ => PosNum.one

/-- A decoding function from `List Bool` to the binary numbers. -/
/-
**Computability.decodeNum** 是 Mathlib 中的一个定义，位于命名空间 `Computability`。
形式化陈述：decodeNum : List Bool -> Num
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A decoding function from `List Bool` to the binary numbers.
-/
def decodeNum : List Bool → Num := fun l => ite (l = []) Num.zero <| decodePosNum l

/-- A decoding function from `List Bool` to `ℕ`. -/
/-
**Computability.decodeNat** 是 Mathlib 中的一个定义，位于命名空间 `Computability`。
形式化陈述：decodeNat : List Bool -> Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A decoding function from `List Bool` to `ℕ`.
-/
def decodeNat : List Bool → Nat := fun l => decodeNum l
/-
**Computability.encodePosNum_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Computability`。
形式化陈述：encodePosNum_nonempty (n : PosNum) : encodePosNum n != []
参数：n : PosNum。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.cons_ne_nil`：∀ {α : Type u_1} (a : α) (l : List α), a :: l ≠ []
-/
theorem encodePosNum_nonempty (n : PosNum) : encodePosNum n ≠ [] :=
  PosNum.casesOn n (List.cons_ne_nil _ _) (fun _m => List.cons_ne_nil _ _) fun _m =>
    List.cons_ne_nil _ _
/-
**Computability.decode_encodePosNum** 是 Mathlib 中的一个定理，位于命名空间 `Computability`。
形式化陈述：∀ (n : PosNum), Computability.decodePosNum (Computability.encodePosNum n) 
= n
参数：n : PosNum；Computability.encodePosNum n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Computability.encodePosNum.eq_def`：∀ (x : PosNum),   Computability.encod
ePosNum x =     match x with     | PosNum.one => [true]     | n.bit0 => false ::
 Computability.encodePo…
· 使用定理 `Computability.decodePosNum.eq_def`：∀ (x : List Bool),   Computability.de
codePosNum x =     match x with     | false :: l => (Computability.decodePosNum 
l).bit0     | true :: l…
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Computability.encodePosNum_nonempty`：encodePosNum_nonempty (n : PosNum) 
: encodePosNum n != []
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
@[simp] theorem decode_encodePosNum (n) : decodePosNum (encodePosNum n) = n := by
  induction n with unfold encodePosNum decodePosNum
  | one => rfl
  | bit1 m hm =>
    rw [hm]
    exact if_neg (encodePosNum_nonempty m)
  | bit0 m hm => exact congr_arg PosNum.bit0 hm
/-
**Computability.decode_encodeNum** 是 Mathlib 中的一个定理，位于命名空间 `Computability`。
形式化陈述：∀ (n : Num), Computability.decodeNum (Computability.encodeNum n) = n
参数：n : Num；Computability.encodeNum n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Computability.decode_encodePosNum`：∀ (n : PosNum), Computability.decodeP
osNum (Computability.encodePosNum n) = n
· 使用定理 `PosNum.cast_to_num`：cast_to_num (n : PosNum) : ↑n = Num.pos n
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Computability.encodePosNum_nonempty`：encodePosNum_nonempty (n : PosNum) 
: encodePosNum n != []
-/
@[simp] theorem decode_encodeNum (n) : decodeNum (encodeNum n) = n := by
  obtain - | n := n <;> unfold encodeNum decodeNum
  · rfl
  rw [decode_encodePosNum n]
  rw [PosNum.cast_to_num]
  exact if_neg (encodePosNum_nonempty n)
/-
**Computability.decode_encodeNat** 是 Mathlib 中的一个定理，位于命名空间 `Computability`。
形式化陈述：∀ (n : ℕ), Computability.decodeNat (Computability.encodeNat n) = n
参数：n : ℕ；Computability.encodeNat n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Num.to_of_nat`：∀ (n : ℕ), ↑↑n = n
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Computability.decode_encodeNum`：∀ (n : Num), Computability.decodeNum (Co
mputability.encodeNum n) = n
-/
@[simp] theorem decode_encodeNat (n) : decodeNat (encodeNat n) = n := by
  conv_rhs => rw [← Num.to_of_nat n]
  exact congr_arg ((↑) : Num → ℕ) (decode_encodeNum n)

/-- A binary `Encoding` of `ℕ` in `Bool`. -/
/-
**Computability.encodingNatBool** 是 Mathlib 中的一个定义，位于命名空间 `Computability`。
形式化陈述：encodingNatBool : Encoding Nat Bool where encode
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A binary `Encoding` of `ℕ` in `Bool`.
-/
def encodingNatBool : Encoding ℕ Bool where
  encode := encodeNat
  decode n := some (decodeNat n)
  decode_encode n := congr_arg _ (decode_encodeNat n)

/-- A binary `Encoding` of `ℕ` in `Γ'`. -/
/-
**Computability.encodingNat** 是 Mathlib 中的一个定义，位于命名空间 `Computability`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A binary `Encoding` of `ℕ` in `Γ'`.
-/
def encodingNatΓ' : Encoding ℕ Γ' where
  encode x := List.map inclusionBoolΓ' (encodeNat x)
  decode x := some (decodeNat (List.map sectionΓ'Bool x))
  decode_encode x := congr_arg _ <| by simp [Function.comp_def]

/-- A unary encoding function of `ℕ` in `Bool`. -/
/-
**Computability.unaryEncodeNat** 是 Mathlib 中的一个定义，位于命名空间 `Computability`。
形式化陈述：ℕ → List Bool
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A unary encoding function of `ℕ` in `Bool`.
-/
def unaryEncodeNat : Nat → List Bool
  | 0 => []
  | n + 1 => true :: unaryEncodeNat n

/-- A unary decoding function from `List Bool` to `ℕ`. -/
/-
**Computability.unaryDecodeNat** 是 Mathlib 中的一个定义，位于命名空间 `Computability`。
形式化陈述：unaryDecodeNat : List Bool -> Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A unary decoding function from `List Bool` to `ℕ`.
-/
def unaryDecodeNat : List Bool → Nat :=
  List.length
/-
**Computability.unary_decode_encode_nat** 是 Mathlib 中的一个定理，位于命名空间 `Computability
`。
形式化陈述：∀ (n : ℕ), Computability.unaryDecodeNat (Computability.unaryEncodeNat n) =
 n
参数：n : ℕ；Computability.unaryEncodeNat n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
@[simp] theorem unary_decode_encode_nat : ∀ n, unaryDecodeNat (unaryEncodeNat n) = n := fun n =>
  Nat.rec rfl (fun (_m : ℕ) hm => (congr_arg Nat.succ hm.symm).symm) n

/-- A unary `Encoding` of `ℕ` in `Bool`. -/
/-
**Computability.unaryEncodingNat** 是 Mathlib 中的一个定义，位于命名空间 `Computability`。
形式化陈述：unaryEncodingNat : Encoding Nat Bool where encode
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A unary `Encoding` of `ℕ` in `Bool`.
-/
def unaryEncodingNat : Encoding ℕ Bool where
  encode := unaryEncodeNat
  decode n := some (unaryDecodeNat n)
  decode_encode n := congr_arg _ (unary_decode_encode_nat n)

/-- An encoding function of `Bool` in `Bool`. -/
/-
**Computability.encodeBool** 是 Mathlib 中的一个定义，位于命名空间 `Computability`。
形式化陈述：encodeBool : Bool -> List Bool
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An encoding function of `Bool` in `Bool`.
-/
def encodeBool : Bool → List Bool := pure

/-- A decoding function from `List Bool` to `Bool`. -/
/-
**Computability.decodeBool** 是 Mathlib 中的一个定义，位于命名空间 `Computability`。
形式化陈述：List Bool → Bool
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A decoding function from `List Bool` to `Bool`.
-/
def decodeBool : List Bool → Bool
  | b :: _ => b
  | _ => Inhabited.default
/-
**Computability.decode_encodeBool** 是 Mathlib 中的一个定理，位于命名空间 `Computability`。
形式化陈述：∀ (b : Bool), Computability.decodeBool (Computability.encodeBool b) = b
参数：b : Bool；Computability.encodeBool b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem decode_encodeBool (b : Bool) : decodeBool (encodeBool b) = b := rfl

/-- An `Encoding` of `Bool` in `Bool`. -/
/-
**Computability.encodingBoolBool** 是 Mathlib 中的一个定义，位于命名空间 `Computability`。
形式化陈述：encodingBoolBool : Encoding Bool Bool where encode
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `Encoding` of `Bool` in `Bool`.
-/
def encodingBoolBool : Encoding Bool Bool where
  encode := encodeBool
  decode x := some (decodeBool x)
  decode_encode x := congr_arg _ (decode_encodeBool x)
/-
**Computability.inhabitedEncoding** 是 Mathlib 中的一个实例，位于命名空间 `Computability`。
形式化陈述：inhabitedEncoding : Inhabited (Encoding Bool Bool)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inhabitedEncoding : Inhabited (Encoding Bool Bool) :=
  ⟨encodingBoolBool⟩
/-
**Computability.Encoding.card_le_card_list** 是 Mathlib 中的一个定理，位于命名空间 `Computabil
ity.Encoding`。
形式化陈述：∀ {α : Type u} {Γ : Type v} (e : Computability.Encoding α Γ),   Cardinal.l
ift.{v, u} (Cardinal.mk α) ≤ Cardinal.lift.{u, v} (Cardinal.mk (List Γ))
参数：e : Computability.Encoding α Γ；Cardinal.mk α；Cardinal.mk (List Γ)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.lift_mk_le'`：lift_mk_le' {α : Type u} {β : Type v} : lift.{v} #
α <= lift.{u} #β ↔ Nonempty (α ↪ β)
· 使用定理 `Computability.Encoding.encode_injective`：∀ {α : Type u_1} {Γ : Type u_2}
 (e : Computability.Encoding α Γ), Function.Injective e.encode
-/
theorem Encoding.card_le_card_list {α : Type u} {Γ : Type v} (e : Encoding α Γ) :
    Cardinal.lift.{v} #α ≤ Cardinal.lift.{u} #(List Γ) :=
  Cardinal.lift_mk_le'.2 ⟨⟨e.encode, e.encode_injective⟩⟩
/-
**Computability.Encoding.card_le_aleph0** 是 Mathlib 中的一个定理，位于命名空间 `Computability
.Encoding`。
形式化陈述：∀ {α : Type u_1} {Γ : Type u_2} (e : Computability.Encoding α Γ) [Countabl
e Γ], Cardinal.mk α ≤ Cardinal.aleph0
参数：e : Computability.Encoding α Γ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_le_aleph0`：mk_le_aleph0 [Countable α] : #α <= ℵ₀
· 使用定理 `Function.Injective.countable`：∀ {α : Sort u} {β : Sort v} [Countable β] 
{f : α → β}, Function.Injective f → Countable α
· 使用定理 `List.countable`：∀ {α : Type u_2} [Countable α], Countable (List α)
· 使用定理 `Computability.Encoding.encode_injective`：∀ {α : Type u_1} {Γ : Type u_2}
 (e : Computability.Encoding α Γ), Function.Injective e.encode
-/
theorem Encoding.card_le_aleph0 {α Γ} (e : Encoding α Γ) [Countable Γ] :
    #α ≤ ℵ₀ :=
  haveI : Countable α := e.encode_injective.countable
  Cardinal.mk_le_aleph0

/-- An `Encoding` of a `List α` in alphabet `α`, encoded directly. -/
/-
**Computability.encodingList** 是 Mathlib 中的一个定义，位于命名空间 `Computability`。
形式化陈述：encodingList (α : Type) : Encoding (List α) α where encode
参数：α : Type。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `Encoding` of a `List α` in alphabet `α`, encoded directly.
-/
def encodingList (α : Type) : Encoding (List α) α where
  encode := id
  decode := Option.some
  decode_encode _ := rfl

set_option backward.isDefEq.respectTransparency false in
/--
Given an `Encoding` of `α` and `β`,
constructs an `Encoding` of `α × β` by concatenating the encodings,
mapping the symbols from the first encoding with `Sum.inl`
and those from the second with `Sum.inr`.
-/
/-
**Computability.encodingProd** 是 Mathlib 中的一个定义，位于命名空间 `Computability`。
形式化陈述：encodingProd {α β Γ₁ Γ₂ : Type*} (ea : Encoding α Γ₁) (eb : Encoding β Γ₂)
 : Encoding (α × β) (Γ₁ oplus Γ₂) where encode x
参数：ea : Encoding α Γ₁；eb : Encoding β Γ₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an `Encoding` of `α` and `β`,
constructs an `Encoding` of `α × β` by concatenating the encodings,
mapping the symbols from the first encoding with `Sum.inl`
and those from the second with `Sum.inr`.
-/
def encodingProd {α β Γ₁ Γ₂ : Type*} (ea : Encoding α Γ₁) (eb : Encoding β Γ₂) :
    Encoding (α × β) (Γ₁ ⊕ Γ₂) where
  encode x := (ea.encode x.1).map .inl ++ (eb.encode x.2).map .inr
  decode x := Option.map₂ Prod.mk (ea.decode (x.filterMap Sum.getLeft?))
      (eb.decode (x.filterMap Sum.getRight?))
  decode_encode x := by simp

/-! ### Deprecated aliases for `FinEncoding` and unbundled `Γ` -/

/-- Deprecated: Use `Encoding α Γ` along with `[Fintype Γ]` instead. -/
@[reducible, nolint unusedArguments,
  deprecated "Use `Encoding α Γ` along with `[Fintype Γ]` instead" (since := "2026-05-07")]
/-
**Computability.FinEncoding** 是 Mathlib 中的一个定义，位于命名空间 `Computability`。
形式化陈述：FinEncoding (α : Type u) {Γ : Type v} [Fintype Γ]
参数：α : Type u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def FinEncoding (α : Type u) {Γ : Type v} [Fintype Γ] := Encoding α Γ

/-- Deprecated: `Γ` is now an explicit parameter of `Encoding`. -/
@[reducible, nolint unusedArguments,
  deprecated "Γ is now an explicit parameter of `Encoding`" (since := "2026-05-07")]
/-
**Computability.Encoding.** 是 Mathlib 中的一个定义，位于命名空间 `Computability`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Encoding.Γ {α : Type u} {Γ : Type v} (_ : Encoding α Γ) : Type v := Γ

/-- Deprecated: Use `inferInstanceAs (Fintype Γ)` instead. -/
@[reducible, nolint unusedArguments,
  deprecated "Use `inferInstanceAs (Fintype Γ)` instead" (since := "2026-05-07")]
/-
**Computability.FinEncoding.** 是 Mathlib 中的一个定义，位于命名空间 `Computability`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def FinEncoding.ΓFin {α : Type u} {Γ : Type v} [h : Fintype Γ]
    (_ : Encoding α Γ) : Fintype Γ := h

/-- Deprecated: Use the encoding directly. -/
@[reducible, nolint unusedArguments,
  deprecated "Use the encoding directly" (since := "2026-05-07")]
/-
**Computability.FinEncoding.toEncoding** 是 Mathlib 中的一个定义，位于命名空间 `Computability.
FinEncoding`。
形式化陈述：{α : Type u} → {Γ : Type v} → [Fintype Γ] → Computability.Encoding α Γ → C
omputability.Encoding α Γ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def FinEncoding.toEncoding {α : Type u} {Γ : Type v} [Fintype Γ]
    (e : Encoding α Γ) : Encoding α Γ := e

/-- Deprecated alias for `encodingNatBool`. -/
@[deprecated encodingNatBool (since := "2026-05-07")]
/-
**Computability.finEncodingNatBool** 是 Mathlib 中的一个缩写定义，位于命名空间 `Computability`。
形式化陈述：finEncodingNatBool
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Deprecated alias for `encodingNatBool`.
-/
abbrev finEncodingNatBool := encodingNatBool

/-- Deprecated alias for `encodingNatΓ'`. -/
@[deprecated encodingNatΓ' (since := "2026-05-07")]
/-
**Computability.finEncodingNat** 是 Mathlib 中的一个缩写定义，位于命名空间 `Computability`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Deprecated alias for `encodingNatΓ'`.
-/
abbrev finEncodingNatΓ' := encodingNatΓ'

/-- Deprecated alias for `unaryEncodingNat`. -/
@[deprecated unaryEncodingNat (since := "2026-05-07")]
/-
**Computability.unaryFinEncodingNat** 是 Mathlib 中的一个缩写定义，位于命名空间 `Computability`。
形式化陈述：unaryFinEncodingNat
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Deprecated alias for `unaryEncodingNat`.
-/
abbrev unaryFinEncodingNat := unaryEncodingNat

/-- Deprecated alias for `encodingBoolBool`. -/
@[deprecated encodingBoolBool (since := "2026-05-07")]
/-
**Computability.finEncodingBoolBool** 是 Mathlib 中的一个缩写定义，位于命名空间 `Computability`。
形式化陈述：finEncodingBoolBool
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Deprecated alias for `encodingBoolBool`.
-/
abbrev finEncodingBoolBool := encodingBoolBool

/-- Deprecated alias for `encodingList`. -/
@[reducible, nolint unusedArguments,
  deprecated encodingList (since := "2026-05-07")]
/-
**Computability.finEncodingList** 是 Mathlib 中的一个定义，位于命名空间 `Computability`。
形式化陈述：finEncodingList (α : Type) [Fintype α]
参数：α : Type。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def finEncodingList (α : Type) [Fintype α] := encodingList α

/-- Deprecated alias for `encodingProd`. -/
@[reducible, nolint unusedArguments,
  deprecated encodingProd (since := "2026-05-07")]
/-
**Computability.finEncodingPair** 是 Mathlib 中的一个定义，位于命名空间 `Computability`。
形式化陈述：finEncodingPair {α β Γ₁ Γ₂ : Type*} [Fintype Γ₁] [Fintype Γ₂] (ea : Encodi
ng α Γ₁) (eb : Encoding β Γ₂)
参数：ea : Encoding α Γ₁；eb : Encoding β Γ₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def finEncodingPair {α β Γ₁ Γ₂ : Type*} [Fintype Γ₁] [Fintype Γ₂]
    (ea : Encoding α Γ₁) (eb : Encoding β Γ₂) :=
  encodingProd ea eb

/-- Deprecated alias for `Encoding.card_le_aleph0`. -/
@[deprecated Encoding.card_le_aleph0 (since := "2026-05-07")]
/-
**Computability.FinEncoding.card_le_aleph0** 是 Mathlib 中的一个定理，位于命名空间 `Computabil
ity.FinEncoding`。
形式化陈述：∀ {α : Type u_1} {Γ : Type u_2} [Countable Γ] (e : Computability.Encoding 
α Γ), Cardinal.mk α ≤ Cardinal.aleph0
参数：e : Computability.Encoding α Γ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computability.Encoding.card_le_aleph0`：∀ {α : Type u_1} {Γ : Type u_2} (
e : Computability.Encoding α Γ) [Countable Γ], Cardinal.mk α ≤ Cardinal.aleph0

--- 原说明 ---
Deprecated alias for `Encoding.card_le_aleph0`.
-/
theorem FinEncoding.card_le_aleph0 {α Γ} [Countable Γ] (e : Encoding α Γ) : #α ≤ ℵ₀ :=
  e.card_le_aleph0

end Computability

