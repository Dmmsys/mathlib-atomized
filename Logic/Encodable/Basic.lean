/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
module

public import Mathlib.Data.Countable.Defs
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Nat.Find
public import Mathlib.Data.PNat.Equiv
public import Mathlib.Logic.Equiv.Nat
public import Mathlib.Order.Directed
public import Mathlib.Order.RelIso.Basic

/-!
# Encodable types

This file defines encodable (constructively countable) types as a typeclass.
This is used to provide explicit encode/decode functions from and to `ℕ`, with the information that
those functions are inverses of each other.
The difference with `Denumerable` is that finite types are encodable. For infinite types,
`Encodable` and `Denumerable` agree.

## Main declarations

* `Encodable α`: States that there exists an explicit encoding function `encode : α → ℕ` with a
  partial inverse `decode : ℕ → Option α`.
* `decode₂`: Version of `decode` that is equal to `none` outside of the range of `encode`. Useful as
  we do not require this in the definition of `decode`.
* `ULower α`: Any encodable type has an equivalent type living in the lowest universe, namely a
  subtype of `ℕ`. `ULower α` finds it.

## Implementation notes

The point of asking for an explicit partial inverse `decode : ℕ → Option α` to `encode : α → ℕ` is
to make the range of `encode` decidable even when the finiteness of `α` is not.
-/

@[expose] public section

assert_not_exists Monoid

-- We want the theorems in this file to be constructive.
set_option linter.unusedDecidableInType false

open Option List Nat Function

/--
Definition of `Encodable` / `Encodable` 的定义

English:
class Encodable
  parameters: (α : Type*)
  axioms and operations (3):
    - encode : α -> Nat
    - decode : Nat -> Option α
    - encodek : forall a, decode (encode a) = some a

中文:
类 Encodable
  参数: (α : 类型)
  公理与运算 (3 个):
    - encode : α -> 自然数
    - decode : 自然数 -> Option α
    - encodek : 对任意 a, decode (encode a) = some a
-/
class Encodable (α : Type*) where
  /-- Encoding from Type α to ℕ -/
  encode : α -> Nat
  /-- Decoding from ℕ to Option α -/
  decode : Nat -> Option α
  /-- Invariant relationship between encoding and decoding -/
  encodek : forall a, decode (encode a) = some a

attribute [simp] Encodable.encodek

namespace Encodable

variable {α : Type*} {β : Type*}

universe u

/--
theorem `encode_injective` / 定理 `encode_injective`

English:
theorem encode_injective
  given: [Encodable α]
  statement: Function.Injective (@encode α _)

中文:
定理 encode_injective
  条件: [Encodable α]
  结论: Function.Injective (@encode α _)
-/
theorem encode_injective [Encodable α] : Function.Injective (@encode α _)
| x, y, e => Option.some.inj by rw [← encodek, e, encodek]

@[simp]
/--
theorem `encode_inj` / 定理 `encode_inj`

English:
theorem encode_inj
  given: [Encodable α] {a b : α}
  statement: encode a = encode b ↔ a = b
  proof: encode_injective.eq_iff

中文:
定理 encode_inj
  条件: [Encodable α] {a b : α}
  结论: encode a = encode b ↔ a = b
  证明: encode_injective.eq_iff

Depends on / 依赖: encode_injective, encode_injective.eq_iff, eq_iff
-/
theorem encode_inj [Encodable α] {a b : α} : encode a = encode b ↔ a = b :=
  encode_injective.eq_iff

-- The priority of the instance below is less than the priorities of `Subtype.Countable`
-- and `Quotient.Countable`
instance (priority := 400) countable [Encodable α] : Countable α where
  exists_injective_nat' := ⟨_,encode_injective⟩

/--
theorem `surjective_decode_getD` / 定理 `surjective_decode_getD`

English:
theorem surjective_decode_getD
  given: (α : Type*) [Encodable α] (d : α)
  proof: fun x =>
  ⟨Encodable.encode x, by simp_rw [Encodable.encodek]; rfl⟩

@[deprecated surjective_decode_getD (since := "2026-01-05")]

中文:
定理 surjective_decode_getD
  条件: (α : 类型) [Encodable α] (d : α)
  证明: fun x =>
  ⟨Encodable.encode x, by simp_rw [Encodable.encodek]; rfl⟩

@[deprecated surjective_decode_getD (since := "2026-01-05")]
-/
theorem surjective_decode_getD (α : Type*) [Encodable α] (d : α) :
    Surjective fun n => (Encodable.decode n).getD d := fun x =>
  ⟨Encodable.encode x, by simp_rw [Encodable.encodek]; rfl⟩

@[deprecated surjective_decode_getD (since := "2026-01-05")]
/--
theorem `surjective_decode_iget` / 定理 `surjective_decode_iget`

English:
theorem surjective_decode_iget
  given: (α : Type*) [Encodable α] [Inhabited α]
  proof: surjective_decode_getD α default

中文:
定理 surjective_decode_iget
  条件: (α : 类型) [Encodable α] [Inhabited α]
  证明: surjective_decode_getD α default

Depends on / 依赖: surjective_decode_getD
-/
theorem surjective_decode_iget (α : Type*) [Encodable α] [Inhabited α] :
    Surjective fun n => ((Encodable.decode n).getD default : α) :=
  surjective_decode_getD α default

/-- An encodable type has decidable equality. Not set as an instance because this is usually not the
best way to infer decidability. -/
@[instance_reducible]
/--
Definition of `decidableEqOfEncodable` / `decidableEqOfEncodable` 的定义

English:
definition decidableEqOfEncodable
  signature: (α) [Encodable α]

中文:
定义 decidableEqOfEncodable
  签名: (α) [Encodable α]
-/
def decidableEqOfEncodable (α) [Encodable α] : DecidableEq α
  | _, _ => decidable_of_iff _ encode_inj

/-- If `α` is encodable and there is an injection `f : β → α`, then `β` is encodable as well. -/
@[instance_reducible]
/--
Definition of `ofLeftInjection` / `ofLeftInjection` 的定义

English:
definition ofLeftInjection
  signature: [Encodable α] (f : β -> α) (finv : α -> Option β)
  body: ⟨fun b => encode (f b), fun n => (decode n).bind finv, fun b => by
    simp [Encodable.encodek, linv]⟩

中文:
定义 ofLeftInjection
  签名: [Encodable α] (f : β -> α) (finv : α -> Option β)
  定义体: ⟨fun b => encode (f b), fun n => (decode n).bind finv, fun b => by
    simp [Encodable.encodek, linv]⟩

Depends on / 依赖: Encodable, Encodable.encodek, decode, encode, encodek
-/
def ofLeftInjection [Encodable α] (f : β -> α) (finv : α -> Option β)
    (linv : forall b, finv (f b) = some b) : Encodable β :=
  ⟨fun b => encode (f b), fun n => (decode n).bind finv, fun b => by
    simp [Encodable.encodek, linv]⟩

/-- If `α` is encodable and `f : β → α` is invertible, then `β` is encodable as well. -/
@[instance_reducible]
/--
Definition of `ofLeftInverse` / `ofLeftInverse` 的定义

English:
definition ofLeftInverse
  signature: [Encodable α] (f : β -> α) (finv : α -> β) (linv : forall b, finv (f b) = b)
  body: ofLeftInjection f (some ∘ finv) fun b => congr_arg some (linv b)

中文:
定义 ofLeftInverse
  签名: [Encodable α] (f : β -> α) (finv : α -> β) (linv : 对任意 b, finv (f b) = b)
  定义体: ofLeftInjection f (some ∘ finv) fun b => congr_arg some (linv b)

Depends on / 依赖: congr_arg, ofLeftInjection
-/
def ofLeftInverse [Encodable α] (f : β -> α) (finv : α -> β) (linv : forall b, finv (f b) = b) :
    Encodable β :=
  ofLeftInjection f (some ∘ finv) fun b => congr_arg some (linv b)

/-- Encodability is preserved by equivalence. -/
@[instance_reducible]
/--
Definition of `ofEquiv` / `ofEquiv` 的定义

English:
definition ofEquiv
  signature: (α) [Encodable α] (e : β ≃ α)
  body: ofLeftInverse e e.symm e.left_inv

中文:
定义 ofEquiv
  签名: (α) [Encodable α] (e : β ≃ α)
  定义体: ofLeftInverse e e.symm e.left_inv

Depends on / 依赖: e.left_inv, e.symm, left_inv, ofLeftInverse
-/
def ofEquiv (α) [Encodable α] (e : β ≃ α) : Encodable β :=
  ofLeftInverse e e.symm e.left_inv

/--
theorem `encode_ofEquiv` / 定理 `encode_ofEquiv`

English:
theorem encode_ofEquiv
  given: {α β} [Encodable α] (e : β ≃ α) (b : β)
  proof: rfl

中文:
定理 encode_ofEquiv
  条件: {α β} [Encodable α] (e : β ≃ α) (b : β)
  证明: rfl
-/
theorem encode_ofEquiv {α β} [Encodable α] (e : β ≃ α) (b : β) :
    @encode _ (ofEquiv _ e) b = encode (e b) :=
  rfl

/--
theorem `decode_ofEquiv` / 定理 `decode_ofEquiv`

English:
theorem decode_ofEquiv
  given: {α β} [Encodable α] (e : β ≃ α) (n : Nat)
  proof: show Option.bind _ _ = Option.map _ _
  by rw [Option.map_eq_bind]

中文:
定理 decode_ofEquiv
  条件: {α β} [Encodable α] (e : β ≃ α) (n : 自然数)
  证明: show Option.bind _ _ = Option.map _ _
  by rw [Option.map_eq_bind]

Depends on / 依赖: Option.bind, Option.map, Option.map_eq_bind, map_eq_bind
-/
theorem decode_ofEquiv {α β} [Encodable α] (e : β ≃ α) (n : Nat) :
    @decode _ (ofEquiv _ e) n = (decode n).map e.symm :=
  show Option.bind _ _ = Option.map _ _
  by rw [Option.map_eq_bind]

/--
Instance `_root_.Nat.encodable` / 实例 `_root_.Nat.encodable`

English:
instance _root_.Nat.encodable
  signature: : Encodable Nat
  body: ⟨id, some, fun _ => rfl⟩

@[simp]

中文:
实例 _root_.Nat.encodable
  签名: : Encodable 自然数
  定义体: ⟨id, some, fun _ => rfl⟩

@[simp]
-/
instance _root_.Nat.encodable : Encodable Nat :=
  ⟨id, some, fun _ => rfl⟩

@[simp]
/--
theorem `encode_nat` / 定理 `encode_nat`

English:
theorem encode_nat
  given: (n : Nat)
  statement: encode n = n
  proof: rfl

@[simp 1100]

中文:
定理 encode_nat
  条件: (n : 自然数)
  结论: encode n = n
  证明: rfl

@[simp 1100]
-/
theorem encode_nat (n : Nat) : encode n = n :=
  rfl

@[simp 1100]
/--
theorem `decode_nat` / 定理 `decode_nat`

English:
theorem decode_nat
  given: (n : Nat)
  statement: decode n = some n
  proof: rfl

中文:
定理 decode_nat
  条件: (n : 自然数)
  结论: decode n = some n
  证明: rfl
-/
theorem decode_nat (n : Nat) : decode n = some n :=
  rfl

instance (priority := 100) _root_.IsEmpty.toEncodable [IsEmpty α] : Encodable α :=
  ⟨isEmptyElim, fun _ => none, isEmptyElim⟩

/--
Instance `_root_.PUnit.encodable` / 实例 `_root_.PUnit.encodable`

English:
instance _root_.PUnit.encodable
  signature: : Encodable PUnit
  body: ⟨fun _ => 0, fun n => Nat.casesOn n (some PUnit.unit) fun _ => none, fun _ => by simp⟩

@[simp]

中文:
实例 _root_.PUnit.encodable
  签名: : Encodable PUnit
  定义体: ⟨fun _ => 0, fun n => Nat.casesOn n (some PUnit.unit) fun _ => none, fun _ => by simp⟩

@[simp]

Depends on / 依赖: Nat.casesOn, PUnit.unit, casesOn
-/
instance _root_.PUnit.encodable : Encodable PUnit :=
  ⟨fun _ => 0, fun n => Nat.casesOn n (some PUnit.unit) fun _ => none, fun _ => by simp⟩

@[simp]
/--
theorem `encode_star` / 定理 `encode_star`

English:
theorem encode_star
  statement: encode PUnit.unit = 0
  proof: rfl

@[simp]

中文:
定理 encode_star
  结论: encode PUnit.unit = 0
  证明: rfl

@[simp]
-/
theorem encode_star : encode PUnit.unit = 0 :=
  rfl

@[simp]
/--
theorem `decode_unit_zero` / 定理 `decode_unit_zero`

English:
theorem decode_unit_zero
  statement: decode 0 = some PUnit.unit
  proof: rfl

@[simp]

中文:
定理 decode_unit_zero
  结论: decode 0 = some PUnit.unit
  证明: rfl

@[simp]
-/
theorem decode_unit_zero : decode 0 = some PUnit.unit :=
  rfl

@[simp]
/--
theorem `decode_unit_succ` / 定理 `decode_unit_succ`

English:
theorem decode_unit_succ
  given: (n)
  statement: decode (succ n) = (none : Option PUnit)
  proof: rfl

中文:
定理 decode_unit_succ
  条件: (n)
  结论: decode (succ n) = (none : Option PUnit)
  证明: rfl
-/
theorem decode_unit_succ (n) : decode (succ n) = (none : Option PUnit) :=
  rfl

/--
Instance `_root_.Option.encodable` / 实例 `_root_.Option.encodable`

English:
instance _root_.Option.encodable
  signature: {α : Type*} [h : Encodable α]
  body: ⟨fun o => Option.casesOn o Nat.zero fun a => succ (encode a), fun n =>
    Nat.casesOn n (some none) fun m => (decode m).map some, fun o => by
    cases o <;> simp [encodek]⟩

@[simp]

中文:
实例 _root_.Option.encodable
  签名: {α : 类型} [h : Encodable α]
  定义体: ⟨fun o => Option.casesOn o Nat.zero fun a => succ (encode a), fun n =>
    Nat.casesOn n (some none) fun m => (decode m).map some, fun o => by
    cases o <;> simp [encodek]⟩

@[simp]

Depends on / 依赖: Nat.casesOn, Nat.zero, Option.casesOn, casesOn, decode, encode, encodek
-/
instance _root_.Option.encodable {α : Type*} [h : Encodable α] : Encodable (Option α) :=
  ⟨fun o => Option.casesOn o Nat.zero fun a => succ (encode a), fun n =>
    Nat.casesOn n (some none) fun m => (decode m).map some, fun o => by
    cases o <;> simp [encodek]⟩

@[simp]
/--
theorem `encode_none` / 定理 `encode_none`

English:
theorem encode_none
  given: [Encodable α]
  statement: encode (@none α) = 0
  proof: rfl

@[simp]

中文:
定理 encode_none
  条件: [Encodable α]
  结论: encode (@none α) = 0
  证明: rfl

@[simp]
-/
theorem encode_none [Encodable α] : encode (@none α) = 0 :=
  rfl

@[simp]
/--
theorem `encode_some` / 定理 `encode_some`

English:
theorem encode_some
  given: [Encodable α] (a : α)
  statement: encode (some a) = succ (encode a)
  proof: rfl

@[simp]

中文:
定理 encode_some
  条件: [Encodable α] (a : α)
  结论: encode (some a) = succ (encode a)
  证明: rfl

@[simp]

Depends on / 依赖: Constants, Constants.term, zeroFunc
-/
theorem encode_some [Encodable α] (a : α) : encode (some a) = succ (encode a) :=
  rfl

@[simp]
/--
theorem `decode_option_zero` / 定理 `decode_option_zero`

English:
theorem decode_option_zero
  given: [Encodable α]
  statement: (decode 0 : Option (Option α)) = some none
  proof: rfl

@[simp]

中文:
定理 decode_option_zero
  条件: [Encodable α]
  结论: (decode 0 : Option (Option α)) = some none
  证明: rfl

@[simp]
-/
theorem decode_option_zero [Encodable α] : (decode 0 : Option (Option α)) = some none :=
  rfl

@[simp]
/--
theorem `decode_option_succ` / 定理 `decode_option_succ`

English:
theorem decode_option_succ
  given: [Encodable α] (n)
  proof: rfl

中文:
定理 decode_option_succ
  条件: [Encodable α] (n)
  证明: rfl

Depends on / 依赖: Constants, Constants.term, oneFunc
-/
theorem decode_option_succ [Encodable α] (n) :
    (decode (succ n) : Option (Option α)) = (decode n).map some :=
  rfl

/--
Definition of `decode₂` / `decode₂` 的定义

English:
definition decode₂
  signature: (α) [Encodable α] (n : Nat)
  body: (decode n).bind (Option.guard fun a => encode a = n)

中文:
定义 decode₂
  签名: (α) [Encodable α] (n : 自然数)
  定义体: (decode n).bind (Option.guard fun a => encode a = n)

Depends on / 依赖: Option.guard, decode, encode
-/
def decode₂ (α) [Encodable α] (n : Nat) : Option α :=
  (decode n).bind (Option.guard fun a => encode a = n)

/--
theorem `mem_decode₂'` / 定理 `mem_decode₂'`

English:
theorem mem_decode₂'
  given: [Encodable α] {n : Nat} {a : α}
  proof: by
  simp [decode₂, Option.bind_eq_some_iff]

中文:
定理 mem_decode₂'
  条件: [Encodable α] {n : 自然数} {a : α}
  证明: by
  simp [decode₂, Option.bind_eq_some_iff]

Depends on / 依赖: Option.bind_eq_some_iff, addFunc, addFunc.apply, bind_eq_some_iff
-/
theorem mem_decode₂' [Encodable α] {n : Nat} {a : α} :
    a in decode₂ α n ↔ a in decode n ∧ encode a = n := by
  simp [decode₂, Option.bind_eq_some_iff]

/--
theorem `mem_decode₂` / 定理 `mem_decode₂`

English:
theorem mem_decode₂
  given: [Encodable α] {n : Nat} {a : α}
  statement: a in decode₂ α n ↔ encode a = n
  proof: mem_decode₂'.trans (and_iff_right_of_imp fun e => e ▸ encodek _)

中文:
定理 mem_decode₂
  条件: [Encodable α] {n : 自然数} {a : α}
  结论: a in decode₂ α n ↔ encode a = n
  证明: mem_decode₂'.trans (and_iff_right_of_imp fun e => e ▸ encodek _)

Depends on / 依赖: and_iff_right_of_imp, encodek
-/
theorem mem_decode₂ [Encodable α] {n : Nat} {a : α} : a in decode₂ α n ↔ encode a = n :=
  mem_decode₂'.trans (and_iff_right_of_imp fun e => e ▸ encodek _)

/--
theorem `decode₂_eq_some` / 定理 `decode₂_eq_some`

English:
theorem decode₂_eq_some
  given: [Encodable α] {n : Nat} {a : α}
  statement: decode₂ α n = some a ↔ encode a = n
  proof: mem_decode₂

@[simp]

中文:
定理 decode₂_eq_some
  条件: [Encodable α] {n : 自然数} {a : α}
  结论: decode₂ α n = some a ↔ encode a = n
  证明: mem_decode₂

@[simp]

Depends on / 依赖: mulFunc, mulFunc.apply
-/
theorem decode₂_eq_some [Encodable α] {n : Nat} {a : α} : decode₂ α n = some a ↔ encode a = n :=
  mem_decode₂

@[simp]
/--
theorem `decode₂_encode` / 定理 `decode₂_encode`

English:
theorem decode₂_encode
  given: [Encodable α] (a : α)
  statement: decode₂ α (encode a) = some a
  proof: by
  simp [decode₂_eq_some]

中文:
定理 decode₂_encode
  条件: [Encodable α] (a : α)
  结论: decode₂ α (encode a) = some a
  证明: by
  simp [decode₂_eq_some]
-/
theorem decode₂_encode [Encodable α] (a : α) : decode₂ α (encode a) = some a := by
  simp [decode₂_eq_some]

/--
theorem `decode₂_ne_none_iff` / 定理 `decode₂_ne_none_iff`

English:
theorem decode₂_ne_none_iff
  given: [Encodable α] {n : Nat}
  proof: by
  simp_rw [Set.range, Set.mem_ofPred_eq, Ne, Option.eq_none_iff_forall_not_mem,
    Encodable.mem_decode₂, not_forall, not_not]

中文:
定理 decode₂_ne_none_iff
  条件: [Encodable α] {n : 自然数}
  证明: by
  simp_rw [Set.range, Set.mem_ofPred_eq, Ne, Option.eq_none_iff_forall_not_mem,
    Encodable.mem_decode₂, not_forall, not_not]

Depends on / 依赖: Encodable, Encodable.mem_decode, Option.eq_none_iff_forall_not_mem, Set.mem_ofPred_eq, Set.range, eq_none_iff_forall_not_mem, mem_ofPred_eq, negFunc, negFunc.apply, not_forall, not_not, simp_rw
-/
theorem decode₂_ne_none_iff [Encodable α] {n : Nat} :
    decode₂ α n != none ↔ n in Set.range (encode : α -> Nat) := by
  simp_rw [Set.range, Set.mem_ofPred_eq, Ne, Option.eq_none_iff_forall_not_mem,
    Encodable.mem_decode₂, not_forall, not_not]

/--
theorem `decode₂_isPartialInv` / 定理 `decode₂_isPartialInv`

English:
theorem decode₂_isPartialInv
  given: [Encodable α]
  statement: IsPartialInv encode (decode₂ α)
  proof: fun _ _ =>
  mem_decode₂

@[deprecated (since := "2026-03-11")] alias decode₂_is_partial_inv := decode₂_isPartialInv

中文:
定理 decode₂_isPartialInv
  条件: [Encodable α]
  结论: IsPartialInv encode (decode₂ α)
  证明: fun _ _ =>
  mem_decode₂

@[deprecated (since := "2026-03-11")] alias decode₂_is_partial_inv := decode₂_isPartialInv
-/
theorem decode₂_isPartialInv [Encodable α] : IsPartialInv encode (decode₂ α) := fun _ _ =>
  mem_decode₂

@[deprecated (since := "2026-03-11")] alias decode₂_is_partial_inv := decode₂_isPartialInv

/--
theorem `decode₂_inj` / 定理 `decode₂_inj`

English:
theorem decode₂_inj
  statement: [Encodable α] {n : Nat} {a₁ a₂ : α} (h₁ : a₁ in decode₂ α n)
  proof: encode_injective (mem_decode₂.1 h₁).trans (mem_decode₂.1 h₂).symm

中文:
定理 decode₂_inj
  结论: [Encodable α] {n : 自然数} {a₁ a₂ : α} (h₁ : a₁ in decode₂ α n)
  证明: encode_injective (mem_decode₂.1 h₁).trans (mem_decode₂.1 h₂).symm

Depends on / 依赖: encode_injective
-/
theorem decode₂_inj [Encodable α] {n : Nat} {a₁ a₂ : α} (h₁ : a₁ in decode₂ α n)
    (h₂ : a₂ in decode₂ α n) : a₁ = a₂ :=
encode_injective (mem_decode₂.1 h₁).trans (mem_decode₂.1 h₂).symm

/--
theorem `encodek₂` / 定理 `encodek₂`

English:
theorem encodek₂
  given: [Encodable α] (a : α)
  statement: decode₂ α (encode a) = some a
  proof: mem_decode₂.2 rfl

中文:
定理 encodek₂
  条件: [Encodable α] (a : α)
  结论: decode₂ α (encode a) = some a
  证明: mem_decode₂.2 rfl
-/
theorem encodek₂ [Encodable α] (a : α) : decode₂ α (encode a) = some a :=
  mem_decode₂.2 rfl

/-- The encoding function has decidable range. -/
@[instance_reducible]
/--
Definition of `decidableRangeEncode` / `decidableRangeEncode` 的定义

English:
definition decidableRangeEncode
  signature: (α : Type*) [Encodable α]
  body: fun x =>
  decidable_of_iff (Option.isSome (decode₂ α x))
    ⟨fun h => ⟨Option.get _ h, by rw [← decode₂_isPartialInv (Option.get _ h), Option.some_get]⟩,
      fun ⟨n, hn⟩ => by rw [← hn, encodek₂]; exact rfl⟩

中文:
定义 decidableRangeEncode
  签名: (α : 类型) [Encodable α]
  定义体: fun x =>
  decidable_of_iff (Option.isSome (decode₂ α x))
    ⟨fun h => ⟨Option.get _ h, by rw [← decode₂_isPartialInv (Option.get _ h), Option.some_get]⟩,
      fun ⟨n, hn⟩ => by rw [← hn, encodek₂]; exact rfl⟩

Depends on / 依赖: Option.get, Option.isSome, Option.some_get, decidable_of_iff, isSome, some_get
-/
def decidableRangeEncode (α : Type*) [Encodable α] : DecidablePred (· in Set.range (@encode α _)) :=
  fun x =>
  decidable_of_iff (Option.isSome (decode₂ α x))
    ⟨fun h => ⟨Option.get _ h, by rw [← decode₂_isPartialInv (Option.get _ h), Option.some_get]⟩,
      fun ⟨n, hn⟩ => by rw [← hn, encodek₂]; exact rfl⟩

/--
Definition of `equivRangeEncode` / `equivRangeEncode` 的定义

English:
definition equivRangeEncode
  signature: (α : Type*) [Encodable α]
  body: ⟨encode a, Set.mem_range_self _⟩
  invFun n :=
    Option.get _
      (show isSome (decode₂ α n.1) by obtain ⟨x, hx⟩ := n.2; rw [← hx, encodek₂]; exact rfl)
  left_inv _ := by dsimp; rw [← Option.some_inj, Option.some_get, encodek₂]
right_inv _ := Subtype.ext decode₂_isPartialInv.get_eq _ _

中文:
定义 equivRangeEncode
  签名: (α : 类型) [Encodable α]
  定义体: ⟨encode a, Set.mem_range_self _⟩
  invFun n :=
    Option.get _
      (show isSome (decode₂ α n.1) by obtain ⟨x, hx⟩ := n.2; rw [← hx, encodek₂]; exact rfl)
  left_inv _ := by dsimp; rw [← Option.some_inj, Option.some_get, encodek₂]
right_inv _ := Subtype.ext decode₂_isPartialInv.get_eq _ _

Depends on / 依赖: Set.mem_range_self, encode, mem_range_self
-/
def equivRangeEncode (α : Type*) [Encodable α] : α ≃ Set.range (@encode α _) where
  toFun a := ⟨encode a, Set.mem_range_self _⟩
  invFun n :=
    Option.get _
      (show isSome (decode₂ α n.1) by obtain ⟨x, hx⟩ := n.2; rw [← hx, encodek₂]; exact rfl)
  left_inv _ := by dsimp; rw [← Option.some_inj, Option.some_get, encodek₂]
right_inv _ := Subtype.ext decode₂_isPartialInv.get_eq _ _

/-- A type with unique element is encodable. This is not an instance to avoid diamonds. -/
@[instance_reducible]
/--
Definition of `_root_.Unique.encodable` / `_root_.Unique.encodable` 的定义

English:
definition _root_.Unique.encodable
  signature: [Unique α]
  body: ⟨fun _ => 0, fun _ => some default, Unique.forall_iff.2 rfl⟩

中文:
定义 _root_.Unique.encodable
  签名: [Unique α]
  定义体: ⟨fun _ => 0, fun _ => some default, Unique.forall_iff.2 rfl⟩

Depends on / 依赖: Unique, Unique.forall_iff, forall_iff
-/
def _root_.Unique.encodable [Unique α] : Encodable α :=
  ⟨fun _ => 0, fun _ => some default, Unique.forall_iff.2 rfl⟩

section Sum

variable [Encodable α] [Encodable β]

/--
Definition of `encodeSum` / `encodeSum` 的定义

English:
definition encodeSum
  signature: : α oplus β -> Nat

中文:
定义 encodeSum
  签名: : α oplus β -> 自然数
-/
def encodeSum : α oplus β -> Nat
  | Sum.inl a => 2 * encode a
  | Sum.inr b => 2 * encode b + 1

/--
Definition of `decodeSum` / `decodeSum` 的定义

English:
definition decodeSum
  signature: (n : Nat)
  body: match bodd n, div2 n with
  | false, m => (decode m : Option α).map Sum.inl
  | _, m => (decode m : Option β).map Sum.inr

中文:
定义 decodeSum
  签名: (n : 自然数)
  定义体: match bodd n, div2 n with
  | false, m => (decode m : Option α).map Sum.inl
  | _, m => (decode m : Option β).map Sum.inr

Depends on / 依赖: Sum.inl, Sum.inr, decode
-/
def decodeSum (n : Nat) : Option (α oplus β) :=
  match bodd n, div2 n with
  | false, m => (decode m : Option α).map Sum.inl
  | _, m => (decode m : Option β).map Sum.inr

/--
Instance `_root_.Sum.encodable` / 实例 `_root_.Sum.encodable`

English:
instance _root_.Sum.encodable
  signature: : Encodable (α oplus β)
  body: ⟨encodeSum, decodeSum, fun s => by cases s <;> simp [encodeSum, div2_val, decodeSum, encodek]⟩

@[simp]

中文:
实例 _root_.Sum.encodable
  签名: : Encodable (α oplus β)
  定义体: ⟨encodeSum, decodeSum, fun s => by cases s <;> simp [encodeSum, div2_val, decodeSum, encodek]⟩

@[simp]

Depends on / 依赖: decodeSum, div2_val, encodeSum, encodek
-/
instance _root_.Sum.encodable : Encodable (α oplus β) :=
  ⟨encodeSum, decodeSum, fun s => by cases s <;> simp [encodeSum, div2_val, decodeSum, encodek]⟩

@[simp]
/--
theorem `encode_inl` / 定理 `encode_inl`

English:
theorem encode_inl
  given: (a : α)
  statement: @encode (α oplus β) _ (Sum.inl a) = 2 * (encode a)
  proof: rfl

@[simp]

中文:
定理 encode_inl
  条件: (a : α)
  结论: @encode (α oplus β) _ (Sum.inl a) = 2 * (encode a)
  证明: rfl

@[simp]
-/
theorem encode_inl (a : α) : @encode (α oplus β) _ (Sum.inl a) = 2 * (encode a) :=
  rfl

@[simp]
/--
theorem `encode_inr` / 定理 `encode_inr`

English:
theorem encode_inr
  given: (b : β)
  statement: @encode (α oplus β) _ (Sum.inr b) = 2 * (encode b) + 1
  proof: rfl

@[simp]

中文:
定理 encode_inr
  条件: (b : β)
  结论: @encode (α oplus β) _ (Sum.inr b) = 2 * (encode b) + 1
  证明: rfl

@[simp]
-/
theorem encode_inr (b : β) : @encode (α oplus β) _ (Sum.inr b) = 2 * (encode b) + 1 :=
  rfl

@[simp]
/--
theorem `decode_sum_val` / 定理 `decode_sum_val`

English:
theorem decode_sum_val
  given: (n : Nat)
  statement: (decode n : Option (α oplus β)) = decodeSum n
  proof: rfl

中文:
定理 decode_sum_val
  条件: (n : 自然数)
  结论: (decode n : Option (α oplus β)) = decodeSum n
  证明: rfl
-/
theorem decode_sum_val (n : Nat) : (decode n : Option (α oplus β)) = decodeSum n :=
  rfl

end Sum

/--
Instance `_root_.Bool.encodable` / 实例 `_root_.Bool.encodable`

English:
instance _root_.Bool.encodable
  signature: : Encodable Bool
  body: ofEquiv (Unit oplus Unit) Equiv.boolEquivPUnitSumPUnit

@[simp]

中文:
实例 _root_.Bool.encodable
  签名: : Encodable 布尔
  定义体: ofEquiv (Unit oplus Unit) Equiv.boolEquivPUnitSumPUnit

@[simp]

Depends on / 依赖: Equiv.boolEquivPUnitSumPUnit, boolEquivPUnitSumPUnit, ofEquiv
-/
instance _root_.Bool.encodable : Encodable Bool :=
  ofEquiv (Unit oplus Unit) Equiv.boolEquivPUnitSumPUnit

@[simp]
/--
theorem `encode_true` / 定理 `encode_true`

English:
theorem encode_true
  statement: encode true = 1
  proof: rfl

@[simp]

中文:
定理 encode_true
  结论: encode true = 1
  证明: rfl

@[simp]
-/
theorem encode_true : encode true = 1 :=
  rfl

@[simp]
/--
theorem `encode_false` / 定理 `encode_false`

English:
theorem encode_false
  statement: encode false = 0
  proof: rfl

@[simp]

中文:
定理 encode_false
  结论: encode false = 0
  证明: rfl

@[simp]
-/
theorem encode_false : encode false = 0 :=
  rfl

@[simp]
/--
theorem `decode_zero` / 定理 `decode_zero`

English:
theorem decode_zero
  statement: (decode 0 : Option Bool) = some false
  proof: rfl

@[simp]

中文:
定理 decode_zero
  结论: (decode 0 : Option 布尔) = some false
  证明: rfl

@[simp]
-/
theorem decode_zero : (decode 0 : Option Bool) = some false :=
  rfl

@[simp]
/--
theorem `decode_one` / 定理 `decode_one`

English:
theorem decode_one
  statement: (decode 1 : Option Bool) = some true
  proof: rfl

中文:
定理 decode_one
  结论: (decode 1 : Option 布尔) = some true
  证明: rfl
-/
theorem decode_one : (decode 1 : Option Bool) = some true :=
  rfl

/--
theorem `decode_ge_two` / 定理 `decode_ge_two`

English:
theorem decode_ge_two
  given: (n) (h : 2 <= n)
  statement: (decode n : Option Bool) = none
  proof: by
  suffices decodeSum n = none by
    change (decodeSum n).bind _ = none
    rw [this]
    rfl
  have : 1 <= n / 2 := by
    rw [Nat.le_div_iff_mul_le]
    exacts [h, by decide]
  obtain ⟨m, e⟩ := exists_eq_succ_of_ne_zero (_root_.ne_of_gt this)
  simp only [decodeSum, div2_val]; cases bodd n <;> 

中文:
定理 decode_ge_two
  条件: (n) (h : 2 <= n)
  结论: (decode n : Option 布尔) = none
  证明: by
  suffices decodeSum n = none by
    change (decodeSum n).bind _ = none
    rw [this]
    rfl
  have : 1 <= n / 2 := by
    rw [Nat.le_div_iff_mul_le]
    exacts [h, by decide]
  obtain ⟨m, e⟩ := exists_eq_succ_of_ne_zero (_root_.ne_of_gt this)
  simp only [decodeSum, div2_val]; cases bodd n <;> 

Depends on / 依赖: Nat.le_div_iff_mul_le, _root_, _root_.ne_of_gt, decodeSum, div2_val, exacts, exists_eq_succ_of_ne_zero, le_div_iff_mul_le, ne_of_gt
-/
theorem decode_ge_two (n) (h : 2 <= n) : (decode n : Option Bool) = none := by
  suffices decodeSum n = none by
    change (decodeSum n).bind _ = none
    rw [this]
    rfl
  have : 1 <= n / 2 := by
    rw [Nat.le_div_iff_mul_le]
    exacts [h, by decide]
  obtain ⟨m, e⟩ := exists_eq_succ_of_ne_zero (_root_.ne_of_gt this)
  simp only [decodeSum, div2_val]; cases bodd n <;> simp [e]

/--
Instance `_root_.Prop.encodable` / 实例 `_root_.Prop.encodable`

English:
instance _root_.Prop.encodable
  signature: : Encodable Prop
  body: ofEquiv Bool Equiv.propEquivBool

中文:
实例 _root_.Prop.encodable
  签名: : Encodable 命题
  定义体: ofEquiv Bool Equiv.propEquivBool

Depends on / 依赖: Equiv.propEquivBool, ofEquiv, propEquivBool
-/
noncomputable instance _root_.Prop.encodable : Encodable Prop :=
  ofEquiv Bool Equiv.propEquivBool

section Sigma

variable {γ : α -> Type*} [Encodable α] [forall a, Encodable (γ a)]

/--
Definition of `encodeSigma` / `encodeSigma` 的定义

English:
definition encodeSigma
  signature: : Sigma γ -> Nat

中文:
定义 encodeSigma
  签名: : Sigma γ -> 自然数
-/
def encodeSigma : Sigma γ -> Nat
  | ⟨a, b⟩ => pair (encode a) (encode b)

/--
Definition of `decodeSigma` / `decodeSigma` 的定义

English:
definition decodeSigma
  signature: (n : Nat)
  body: let (n₁, n₂) := unpair n
(decode n₁).bind fun a => (decode n₂).map Sigma.mk a

中文:
定义 decodeSigma
  签名: (n : 自然数)
  定义体: let (n₁, n₂) := unpair n
(decode n₁).bind fun a => (decode n₂).map Sigma.mk a

Depends on / 依赖: Sigma.mk, decode, unpair
-/
def decodeSigma (n : Nat) : Option (Sigma γ) :=
  let (n₁, n₂) := unpair n
(decode n₁).bind fun a => (decode n₂).map Sigma.mk a

/--
Instance `_root_.Sigma.encodable` / 实例 `_root_.Sigma.encodable`

English:
instance _root_.Sigma.encodable
  signature: : Encodable (Sigma γ)
  body: ⟨encodeSigma, decodeSigma, fun ⟨a, b⟩ => by
    simp [encodeSigma, decodeSigma, unpair_pair, encodek]⟩

@[simp]

中文:
实例 _root_.Sigma.encodable
  签名: : Encodable (Sigma γ)
  定义体: ⟨encodeSigma, decodeSigma, fun ⟨a, b⟩ => by
    simp [encodeSigma, decodeSigma, unpair_pair, encodek]⟩

@[simp]

Depends on / 依赖: decodeSigma, encodeSigma, encodek, unpair_pair
-/
instance _root_.Sigma.encodable : Encodable (Sigma γ) :=
  ⟨encodeSigma, decodeSigma, fun ⟨a, b⟩ => by
    simp [encodeSigma, decodeSigma, unpair_pair, encodek]⟩

@[simp]
/--
theorem `decode_sigma_val` / 定理 `decode_sigma_val`

English:
theorem decode_sigma_val
  given: (n : Nat)
  proof: rfl

@[simp]

中文:
定理 decode_sigma_val
  条件: (n : 自然数)
  证明: rfl

@[simp]
-/
theorem decode_sigma_val (n : Nat) :
    (decode n : Option (Sigma γ)) =
(decode n.unpair.1).bind fun a => (decode n.unpair.2).map Sigma.mk a :=
  rfl

@[simp]
/--
theorem `encode_sigma_val` / 定理 `encode_sigma_val`

English:
theorem encode_sigma_val
  given: (a b)
  statement: @encode (Sigma γ) _ ⟨a, b⟩ = pair (encode a) (encode b)
  proof: rfl

中文:
定理 encode_sigma_val
  条件: (a b)
  结论: @encode (Sigma γ) _ ⟨a, b⟩ = pair (encode a) (encode b)
  证明: rfl
-/
theorem encode_sigma_val (a b) : @encode (Sigma γ) _ ⟨a, b⟩ = pair (encode a) (encode b) :=
  rfl

end Sigma

section Prod

variable [Encodable α] [Encodable β]

/--
Instance `Prod.encodable` / 实例 `Prod.encodable`

English:
instance Prod.encodable
  signature: : Encodable (α × β)
  body: ofEquiv _ (Equiv.sigmaEquivProd α β).symm

@[simp]

中文:
实例 Prod.encodable
  签名: : Encodable (α × β)
  定义体: ofEquiv _ (Equiv.sigmaEquivProd α β).symm

@[simp]

Depends on / 依赖: Equiv.sigmaEquivProd, ofEquiv, sigmaEquivProd
-/
instance Prod.encodable : Encodable (α × β) :=
  ofEquiv _ (Equiv.sigmaEquivProd α β).symm

@[simp]
/--
theorem `decode_prod_val` / 定理 `decode_prod_val`

English:
theorem decode_prod_val
  given: (n : Nat)
  proof: by
  simp only [decode_ofEquiv, Equiv.symm_symm, decode_sigma_val]
  cases (decode n.unpair.1 : Option α) <;> cases (decode n.unpair.2 : Option β)
  <;> rfl

@[simp]

中文:
定理 decode_prod_val
  条件: (n : 自然数)
  证明: by
  simp only [decode_ofEquiv, Equiv.symm_symm, decode_sigma_val]
  cases (decode n.unpair.1 : Option α) <;> cases (decode n.unpair.2 : Option β)
  <;> rfl

@[simp]

Depends on / 依赖: Equiv.symm_symm, decode, decode_ofEquiv, decode_sigma_val, n.unpair, symm_symm, unpair
-/
theorem decode_prod_val (n : Nat) :
    (@decode (α × β) _ n : Option (α × β))
= (decode n.unpair.1).bind fun a => (decode n.unpair.2).map Prod.mk a := by
  simp only [decode_ofEquiv, Equiv.symm_symm, decode_sigma_val]
  cases (decode n.unpair.1 : Option α) <;> cases (decode n.unpair.2 : Option β)
  <;> rfl

@[simp]
/--
theorem `encode_prod_val` / 定理 `encode_prod_val`

English:
theorem encode_prod_val
  given: (a b)
  statement: @encode (α × β) _ (a, b) = pair (encode a) (encode b)
  proof: rfl

中文:
定理 encode_prod_val
  条件: (a b)
  结论: @encode (α × β) _ (a, b) = pair (encode a) (encode b)
  证明: rfl
-/
theorem encode_prod_val (a b) : @encode (α × β) _ (a, b) = pair (encode a) (encode b) :=
  rfl

end Prod

section Subtype

open Subtype Decidable

variable {P : α -> Prop} [encA : Encodable α] [decP : DecidablePred P]

/--
Definition of `encodeSubtype` / `encodeSubtype` 的定义

English:
definition encodeSubtype
  signature: : { a : α // P a } -> Nat

中文:
定义 encodeSubtype
  签名: : { a : α // P a } -> 自然数
-/
def encodeSubtype : { a : α // P a } -> Nat
  | ⟨v,_⟩ => encode v

/--
Definition of `decodeSubtype` / `decodeSubtype` 的定义

English:
definition decodeSubtype
  signature: (v : Nat)
  body: (decode v).bind fun a => if h : P a then some ⟨a, h⟩ else none

中文:
定义 decodeSubtype
  签名: (v : 自然数)
  定义体: (decode v).bind fun a => if h : P a then some ⟨a, h⟩ else none

Depends on / 依赖: decode
-/
def decodeSubtype (v : Nat) : Option { a : α // P a } :=
  (decode v).bind fun a => if h : P a then some ⟨a, h⟩ else none

/--
Instance `_root_.Subtype.encodable` / 实例 `_root_.Subtype.encodable`

English:
instance _root_.Subtype.encodable
  signature: : Encodable { a : α // P a }
  body: ⟨encodeSubtype, decodeSubtype, fun ⟨v, h⟩ => by simp [encodeSubtype, decodeSubtype, encodek, h]⟩

中文:
实例 _root_.Subtype.encodable
  签名: : Encodable { a : α // P a }
  定义体: ⟨encodeSubtype, decodeSubtype, fun ⟨v, h⟩ => by simp [encodeSubtype, decodeSubtype, encodek, h]⟩

Depends on / 依赖: decodeSubtype, encodeSubtype, encodek
-/
instance _root_.Subtype.encodable : Encodable { a : α // P a } :=
  ⟨encodeSubtype, decodeSubtype, fun ⟨v, h⟩ => by simp [encodeSubtype, decodeSubtype, encodek, h]⟩

/--
theorem `Subtype.encode_eq` / 定理 `Subtype.encode_eq`

English:
theorem Subtype.encode_eq
  given: (a : Subtype P)
  statement: encode a = encode a.val
  proof: by cases a; rfl

中文:
定理 Subtype.encode_eq
  条件: (a : Subtype P)
  结论: encode a = encode a.val
  证明: by cases a; rfl
-/
theorem Subtype.encode_eq (a : Subtype P) : encode a = encode a.val := by cases a; rfl

end Subtype

/--
Instance `_root_.Fin.encodable` / 实例 `_root_.Fin.encodable`

English:
instance _root_.Fin.encodable
  signature: (n)
  body: ofEquiv _ Fin.equivSubtype

中文:
实例 _root_.Fin.encodable
  签名: (n)
  定义体: ofEquiv _ Fin.equivSubtype

Depends on / 依赖: Fin.equivSubtype, equivSubtype, ofEquiv
-/
instance _root_.Fin.encodable (n) : Encodable (Fin n) :=
  ofEquiv _ Fin.equivSubtype

/--
Instance `_root_.Int.encodable` / 实例 `_root_.Int.encodable`

English:
instance _root_.Int.encodable
  signature: : Encodable Int
  body: ofEquiv _ Equiv.intEquivNat

中文:
实例 _root_.Int.encodable
  签名: : Encodable 整数
  定义体: ofEquiv _ Equiv.intEquivNat

Depends on / 依赖: Equiv.intEquivNat, intEquivNat, ofEquiv
-/
instance _root_.Int.encodable : Encodable Int :=
  ofEquiv _ Equiv.intEquivNat

/--
Instance `_root_.PNat.encodable` / 实例 `_root_.PNat.encodable`

English:
instance _root_.PNat.encodable
  signature: : Encodable Nat+
  body: ofEquiv _ Equiv.pnatEquivNat

中文:
实例 _root_.PNat.encodable
  签名: : Encodable 自然数+
  定义体: ofEquiv _ Equiv.pnatEquivNat

Depends on / 依赖: Equiv.pnatEquivNat, ofEquiv, pnatEquivNat
-/
instance _root_.PNat.encodable : Encodable Nat+ :=
  ofEquiv _ Equiv.pnatEquivNat

/--
Instance `_root_.ULift.encodable` / 实例 `_root_.ULift.encodable`

English:
instance _root_.ULift.encodable
  signature: [Encodable α]
  body: ofEquiv _ Equiv.ulift

中文:
实例 _root_.ULift.encodable
  签名: [Encodable α]
  定义体: ofEquiv _ Equiv.ulift

Depends on / 依赖: Equiv.ulift, ofEquiv
-/
instance _root_.ULift.encodable [Encodable α] : Encodable (ULift α) :=
  ofEquiv _ Equiv.ulift

/--
Instance `_root_.PLift.encodable` / 实例 `_root_.PLift.encodable`

English:
instance _root_.PLift.encodable
  signature: [Encodable α]
  body: ofEquiv _ Equiv.plift

中文:
实例 _root_.PLift.encodable
  签名: [Encodable α]
  定义体: ofEquiv _ Equiv.plift

Depends on / 依赖: Equiv.plift, ofEquiv
-/
instance _root_.PLift.encodable [Encodable α] : Encodable (PLift α) :=
  ofEquiv _ Equiv.plift

/-- If `β` is encodable and there is an injection `f : α → β`, then `α` is encodable as well. -/
@[instance_reducible]
/--
Definition of `ofInj` / `ofInj` 的定义

English:
definition ofInj
  signature: [Encodable β] (f : α -> β) (hf : Injective f)
  body: ofLeftInjection f (partialInv f) hf.isPartialInv.eq

中文:
定义 ofInj
  签名: [Encodable β] (f : α -> β) (hf : Injective f)
  定义体: ofLeftInjection f (partialInv f) hf.isPartialInv.eq

Depends on / 依赖: hf.isPartialInv.eq, isPartialInv, ofLeftInjection, partialInv
-/
noncomputable def ofInj [Encodable β] (f : α -> β) (hf : Injective f) : Encodable α :=
  ofLeftInjection f (partialInv f) hf.isPartialInv.eq

/-- If `α` is countable, then it has a (non-canonical) `Encodable` structure. -/
@[no_expose, instance_reducible]
/--
Definition of `ofCountable` / `ofCountable` 的定义

English:
definition ofCountable
  signature: (α : Type*) [Countable α]
  body: Nonempty.some
    let ⟨f, hf⟩ := exists_injective_nat α
    ⟨ofInj f hf⟩

@[simp]

中文:
定义 ofCountable
  签名: (α : 类型) [Countable α]
  定义体: Nonempty.some
    let ⟨f, hf⟩ := exists_injective_nat α
    ⟨ofInj f hf⟩

@[simp]

Depends on / 依赖: Nonempty, Nonempty.some, exists_injective_nat
-/
noncomputable def ofCountable (α : Type*) [Countable α] : Encodable α :=
Nonempty.some
    let ⟨f, hf⟩ := exists_injective_nat α
    ⟨ofInj f hf⟩

@[simp]
/--
theorem `nonempty_encodable` / 定理 `nonempty_encodable`

English:
theorem nonempty_encodable
  statement: Nonempty (Encodable α) ↔ Countable α
  proof: ⟨fun ⟨h⟩ => @Encodable.countable α h, fun h => ⟨@ofCountable _ h⟩⟩

中文:
定理 nonempty_encodable
  结论: Nonempty (Encodable α) ↔ Countable α
  证明: ⟨fun ⟨h⟩ => @Encodable.countable α h, fun h => ⟨@ofCountable _ h⟩⟩

Depends on / 依赖: Encodable, Encodable.countable, countable, ofCountable
-/
theorem nonempty_encodable : Nonempty (Encodable α) ↔ Countable α :=
  ⟨fun ⟨h⟩ => @Encodable.countable α h, fun h => ⟨@ofCountable _ h⟩⟩

end Encodable

/--
theorem `nonempty_encodable` / 定理 `nonempty_encodable`

English:
theorem nonempty_encodable
  given: (α : Type*) [Countable α]
  statement: Nonempty (Encodable α)
  proof: ⟨Encodable.ofCountable _⟩

中文:
定理 nonempty_encodable
  条件: (α : 类型) [Countable α]
  结论: Nonempty (Encodable α)
  证明: ⟨Encodable.ofCountable _⟩

Depends on / 依赖: Encodable, Encodable.ofCountable, ofCountable
-/
theorem nonempty_encodable (α : Type*) [Countable α] : Nonempty (Encodable α) :=
  ⟨Encodable.ofCountable _⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Countable Nat+
  body: by delta PNat; infer_instance

中文:
实例 :
  签名: Countable 自然数+
  定义体: by delta PNat; infer_instance
-/
instance : Countable Nat+ := by delta PNat; infer_instance

-- short-circuit instance search
section ULower

attribute [local instance] Encodable.decidableRangeEncode

/--
Definition of `ULower` / `ULower` 的定义

English:
definition ULower
  signature: (α : Type*) [Encodable α]
  body: Set.range (Encodable.encode : α -> Nat)

中文:
定义 ULower
  签名: (α : 类型) [Encodable α]
  定义体: Set.range (Encodable.encode : α -> Nat)

Depends on / 依赖: Encodable, Encodable.encode, Set.range, encode
-/
def ULower (α : Type*) [Encodable α] : Type :=
  Set.range (Encodable.encode : α -> Nat)

instance {α : Type*} [Encodable α] : DecidableEq (ULower α) := by
  delta ULower; exact Encodable.decidableEqOfEncodable _

instance {α : Type*} [Encodable α] : Encodable (ULower α) := by
  delta ULower; infer_instance

end ULower

namespace ULower

variable (α : Type*) [Encodable α]

/--
Definition of `equiv` / `equiv` 的定义

English:
definition equiv
  signature: : α ≃ ULower α
  body: Encodable.equivRangeEncode α

中文:
定义 equiv
  签名: : α ≃ ULower α
  定义体: Encodable.equivRangeEncode α

Depends on / 依赖: Encodable, Encodable.equivRangeEncode, equivRangeEncode
-/
def equiv : α ≃ ULower α :=
  Encodable.equivRangeEncode α

variable {α}

/--
Definition of `down` / `down` 的定义

English:
definition down
  signature: (a : α)
  body: equiv α a

中文:
定义 down
  签名: (a : α)
  定义体: equiv α a
-/
def down (a : α) : ULower α :=
  equiv α a

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: α] : Inhabited (ULower α)
  body: ⟨down default⟩

中文:
实例 [Inhabited
  签名: α] : Inhabited (ULower α)
  定义体: ⟨down default⟩
-/
instance [Inhabited α] : Inhabited (ULower α) :=
  ⟨down default⟩

/--
Definition of `up` / `up` 的定义

English:
definition up
  signature: (a : ULower α)
  body: (equiv α).symm a

@[simp]

中文:
定义 up
  签名: (a : ULower α)
  定义体: (equiv α).symm a

@[simp]
-/
def up (a : ULower α) : α :=
  (equiv α).symm a

@[simp]
/--
theorem `down_up` / 定理 `down_up`

English:
theorem down_up
  given: {a : ULower α}
  statement: down a.up = a
  proof: Equiv.right_inv _ _

@[simp]

中文:
定理 down_up
  条件: {a : ULower α}
  结论: down a.up = a
  证明: Equiv.right_inv _ _

@[simp]

Depends on / 依赖: Equiv.right_inv, right_inv
-/
theorem down_up {a : ULower α} : down a.up = a :=
  Equiv.right_inv _ _

@[simp]
/--
theorem `up_down` / 定理 `up_down`

English:
theorem up_down
  given: {a : α}
  statement: (down a).up = a
  proof: by
  simp [up, down, Equiv.symm_apply_apply]

@[simp]

中文:
定理 up_down
  条件: {a : α}
  结论: (down a).up = a
  证明: by
  simp [up, down, Equiv.symm_apply_apply]

@[simp]

Depends on / 依赖: Equiv.symm_apply_apply, symm_apply_apply
-/
theorem up_down {a : α} : (down a).up = a := by
  simp [up, down, Equiv.symm_apply_apply]

@[simp]
/--
theorem `up_eq_up` / 定理 `up_eq_up`

English:
theorem up_eq_up
  given: {a b : ULower α}
  statement: a.up = b.up ↔ a = b
  proof: Equiv.apply_eq_iff_eq _

@[simp]

中文:
定理 up_eq_up
  条件: {a b : ULower α}
  结论: a.up = b.up ↔ a = b
  证明: Equiv.apply_eq_iff_eq _

@[simp]

Depends on / 依赖: Equiv.apply_eq_iff_eq, apply_eq_iff_eq
-/
theorem up_eq_up {a b : ULower α} : a.up = b.up ↔ a = b :=
  Equiv.apply_eq_iff_eq _

@[simp]
/--
theorem `down_eq_down` / 定理 `down_eq_down`

English:
theorem down_eq_down
  given: {a b : α}
  statement: down a = down b ↔ a = b
  proof: Equiv.apply_eq_iff_eq _

@[ext]

中文:
定理 down_eq_down
  条件: {a b : α}
  结论: down a = down b ↔ a = b
  证明: Equiv.apply_eq_iff_eq _

@[ext]

Depends on / 依赖: Equiv.apply_eq_iff_eq, apply_eq_iff_eq
-/
theorem down_eq_down {a b : α} : down a = down b ↔ a = b :=
  Equiv.apply_eq_iff_eq _

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {a b : ULower α}
  statement: a.up = b.up -> a = b
  proof: up_eq_up.1

中文:
定理 ext
  条件: {a b : ULower α}
  结论: a.up = b.up -> a = b
  证明: up_eq_up.1
-/
protected theorem ext {a b : ULower α} : a.up = b.up -> a = b :=
  up_eq_up.1

end ULower

/-
Choice function for encodable types and decidable predicates.
We provide the following API

choose {α : Type*} {p : α → Prop} [c : encodable α] [d : decidable_pred p] : (∃ x, p x) → α :=
choose_spec {α : Type*} {p : α → Prop} [c : encodable α] [d : decidable_pred p] (ex : ∃ x, p x) :
  p (choose ex) :=
-/
namespace Encodable

section FindA

variable {α : Type*} (p : α -> Prop) [Encodable α] [DecidablePred p]

set_option backward.privateInPublic true in
/--
Definition of `good` / `good` 的定义

English:
definition good
  signature: : Option α -> Prop

中文:
定义 good
  签名: : Option α -> 命题
-/
private def good : Option α -> Prop
  | some a => p a
  | none => False

set_option backward.privateInPublic true in
private local instance decidable_good : DecidablePred (good p)
| some a => inferInstanceAs Decidable (p a)
| none => inferInstanceAs Decidable False

open Encodable

variable {p}

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Definition of `chooseX` / `chooseX` 的定义

English:
definition chooseX
  signature: (h : exists x, p x)
  body: have : exists n, good p (decode n) :=
    let ⟨w, pw⟩ := h
    ⟨encode w, by simp [good, encodek, pw]⟩
  match (motive := forall o, good p o -> { a // p a }) _, Nat.find_spec this with
  | some a, h => ⟨a, h⟩

中文:
定义 chooseX
  签名: (h : 存在 x, p x)
  定义体: have : exists n, good p (decode n) :=
    let ⟨w, pw⟩ := h
    ⟨encode w, by simp [good, encodek, pw]⟩
  match (motive := forall o, good p o -> { a // p a }) _, Nat.find_spec this with
  | some a, h => ⟨a, h⟩

Depends on / 依赖: Nat.find_spec, decode, encode, encodek, find_spec, motive
-/
def chooseX (h : exists x, p x) : { a : α // p a } :=
  have : exists n, good p (decode n) :=
    let ⟨w, pw⟩ := h
    ⟨encode w, by simp [good, encodek, pw]⟩
  match (motive := forall o, good p o -> { a // p a }) _, Nat.find_spec this with
  | some a, h => ⟨a, h⟩

/--
Definition of `choose` / `choose` 的定义

English:
definition choose
  signature: (h : exists x, p x)
  body: (chooseX h).1

中文:
定义 choose
  签名: (h : 存在 x, p x)
  定义体: (chooseX h).1

Depends on / 依赖: chooseX
-/
def choose (h : exists x, p x) : α :=
  (chooseX h).1

/--
theorem `choose_spec` / 定理 `choose_spec`

English:
theorem choose_spec
  given: (h : exists x, p x)
  statement: p (choose h)
  proof: (chooseX h).2

中文:
定理 choose_spec
  条件: (h : 存在 x, p x)
  结论: p (choose h)
  证明: (chooseX h).2

Depends on / 依赖: chooseX
-/
theorem choose_spec (h : exists x, p x) : p (choose h) :=
  (chooseX h).2

end FindA

/--
theorem `axiom_of_choice` / 定理 `axiom_of_choice`

English:
theorem axiom_of_choice
  statement: {α : Type*} {β : α -> Type*} {R : forall x, β x -> Prop} [forall a, Encodable (β a)]
  proof: ⟨fun x => choose (H x), fun x => choose_spec (H x)⟩

中文:
定理 axiom_of_choice
  结论: {α : 类型} {β : α -> 类型} {R : 对任意 x, β x -> 命题} [对任意 a, Encodable (β a)]
  证明: ⟨fun x => choose (H x), fun x => choose_spec (H x)⟩

Depends on / 依赖: choose_spec
-/
theorem axiom_of_choice {α : Type*} {β : α -> Type*} {R : forall x, β x -> Prop} [forall a, Encodable (β a)]
    [forall x y, Decidable (R x y)] (H : forall x, exists y, R x y) : exists f : forall a, β a, forall x, R x (f x) :=
  ⟨fun x => choose (H x), fun x => choose_spec (H x)⟩

/--
theorem `skolem` / 定理 `skolem`

English:
theorem skolem
  statement: {α : Type*} {β : α -> Type*} {P : forall x, β x -> Prop} [forall a, Encodable (β a)]
  proof: ⟨axiom_of_choice, fun ⟨_, H⟩ x => ⟨_, H x⟩⟩

中文:
定理 skolem
  结论: {α : 类型} {β : α -> 类型} {P : 对任意 x, β x -> 命题} [对任意 a, Encodable (β a)]
  证明: ⟨axiom_of_choice, fun ⟨_, H⟩ x => ⟨_, H x⟩⟩

Depends on / 依赖: axiom_of_choice
-/
theorem skolem {α : Type*} {β : α -> Type*} {P : forall x, β x -> Prop} [forall a, Encodable (β a)]
    [forall x y, Decidable (P x y)] : (forall x, exists y, P x y) ↔ exists f : forall a, β a, forall x, P x (f x) :=
  ⟨axiom_of_choice, fun ⟨_, H⟩ x => ⟨_, H x⟩⟩

/-
There is a total ordering on the elements of an encodable type, induced by the map to ℕ.
-/
/--
Definition of `encode'` / `encode'` 的定义

English:
definition encode'
  signature: (α) [Encodable α]
  body: ⟨Encodable.encode, Encodable.encode_injective⟩

中文:
定义 encode'
  签名: (α) [Encodable α]
  定义体: ⟨Encodable.encode, Encodable.encode_injective⟩

Depends on / 依赖: Encodable, Encodable.encode, Encodable.encode_injective, encode, encode_injective
-/
def encode' (α) [Encodable α] : α ↪ Nat :=
  ⟨Encodable.encode, Encodable.encode_injective⟩

instance {α} [Encodable α] : Std.Antisymm (Encodable.encode' α ⁻¹'o (· <= ·)) :=
  (RelEmbedding.preimage _ _).antisymm

instance {α} [Encodable α] : Std.Total (Encodable.encode' α ⁻¹'o (· <= ·)) :=
  (RelEmbedding.preimage _ _).total

end Encodable

namespace Directed

open Encodable

variable {α : Type*} {β : Type*} [Encodable α] [Inhabited α]

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def sequence {r : β -> β -> Prop} (f : α -> β) (hf : Directed r f)
  body: Directed.sequence f hf n
    match (decode n : Option α) with
    | none => Classical.choose (hf p p)
    | some a => Classical.choose (hf p a)

中文:
定义 noncomputable
  签名: def sequence {r : β -> β -> 命题} (f : α -> β) (hf : Directed r f)
  定义体: Directed.sequence f hf n
    match (decode n : Option α) with
    | none => Classical.choose (hf p p)
    | some a => Classical.choose (hf p a)
-/
protected noncomputable def sequence {r : β -> β -> Prop} (f : α -> β) (hf : Directed r f) : Nat -> α
  | 0 => default
  | n + 1 =>
    let p := Directed.sequence f hf n
    match (decode n : Option α) with
    | none => Classical.choose (hf p p)
    | some a => Classical.choose (hf p a)

/--
theorem `sequence_mono_nat` / 定理 `sequence_mono_nat`

English:
theorem sequence_mono_nat
  given: {r : β -> β -> Prop} {f : α -> β} (hf : Directed r f) (n : Nat)
  proof: by
  dsimp [Directed.sequence]
  generalize hf.sequence f n = p
  rcases (decode n : Option α) with - | a
  · exact (Classical.choose_spec (hf p p)).1
  · exact (Classical.choose_spec (hf p a)).1

中文:
定理 sequence_mono_nat
  条件: {r : β -> β -> 命题} {f : α -> β} (hf : Directed r f) (n : 自然数)
  证明: by
  dsimp [Directed.sequence]
  generalize hf.sequence f n = p
  rcases (decode n : Option α) with - | a
  · exact (Classical.choose_spec (hf p p)).1
  · exact (Classical.choose_spec (hf p a)).1

Depends on / 依赖: Classical, Classical.choose_spec, Directed, Directed.sequence, choose_spec, decode, generalize, hf.sequence, sequence
-/
theorem sequence_mono_nat {r : β -> β -> Prop} {f : α -> β} (hf : Directed r f) (n : Nat) :
    r (f (hf.sequence f n)) (f (hf.sequence f (n + 1))) := by
  dsimp [Directed.sequence]
  generalize hf.sequence f n = p
  rcases (decode n : Option α) with - | a
  · exact (Classical.choose_spec (hf p p)).1
  · exact (Classical.choose_spec (hf p a)).1

/--
theorem `rel_sequence` / 定理 `rel_sequence`

English:
theorem rel_sequence
  given: {r : β -> β -> Prop} {f : α -> β} (hf : Directed r f) (a : α)
  proof: by
  simp only [Directed.sequence, encodek]
  exact (Classical.choose_spec (hf _ a)).2

中文:
定理 rel_sequence
  条件: {r : β -> β -> 命题} {f : α -> β} (hf : Directed r f) (a : α)
  证明: by
  simp only [Directed.sequence, encodek]
  exact (Classical.choose_spec (hf _ a)).2

Depends on / 依赖: Classical, Classical.choose_spec, Directed, Directed.sequence, choose_spec, encodek, sequence
-/
theorem rel_sequence {r : β -> β -> Prop} {f : α -> β} (hf : Directed r f) (a : α) :
    r (f a) (f (hf.sequence f (encode a + 1))) := by
  simp only [Directed.sequence, encodek]
  exact (Classical.choose_spec (hf _ a)).2

variable [Preorder β] {f : α -> β}

section

variable (hf : Directed (· <= ·) f)

/--
theorem `sequence_mono` / 定理 `sequence_mono`

English:
theorem sequence_mono
  statement: Monotone (f ∘ hf.sequence f)
  proof: monotone_nat_of_le_succ hf.sequence_mono_nat

中文:
定理 sequence_mono
  结论: Monotone (f ∘ hf.sequence f)
  证明: monotone_nat_of_le_succ hf.sequence_mono_nat

Depends on / 依赖: hf.sequence_mono_nat, monotone_nat_of_le_succ, sequence_mono_nat
-/
theorem sequence_mono : Monotone (f ∘ hf.sequence f) :=
monotone_nat_of_le_succ hf.sequence_mono_nat

/--
theorem `le_sequence` / 定理 `le_sequence`

English:
theorem le_sequence
  given: (a : α)
  statement: f a <= f (hf.sequence f (encode a + 1))
  proof: hf.rel_sequence a

中文:
定理 le_sequence
  条件: (a : α)
  结论: f a <= f (hf.sequence f (encode a + 1))
  证明: hf.rel_sequence a

Depends on / 依赖: hf.rel_sequence, rel_sequence
-/
theorem le_sequence (a : α) : f a <= f (hf.sequence f (encode a + 1)) :=
  hf.rel_sequence a

end

section

variable (hf : Directed (· >= ·) f)

/--
theorem `sequence_anti` / 定理 `sequence_anti`

English:
theorem sequence_anti
  statement: Antitone (f ∘ hf.sequence f)
  proof: antitone_nat_of_succ_le hf.sequence_mono_nat

中文:
定理 sequence_anti
  结论: Antitone (f ∘ hf.sequence f)
  证明: antitone_nat_of_succ_le hf.sequence_mono_nat

Depends on / 依赖: antitone_nat_of_succ_le, hf.sequence_mono_nat, sequence_mono_nat
-/
theorem sequence_anti : Antitone (f ∘ hf.sequence f) :=
antitone_nat_of_succ_le hf.sequence_mono_nat

/--
theorem `sequence_le` / 定理 `sequence_le`

English:
theorem sequence_le
  given: (a : α)
  statement: f (hf.sequence f (Encodable.encode a + 1)) <= f a
  proof: hf.rel_sequence a

中文:
定理 sequence_le
  条件: (a : α)
  结论: f (hf.sequence f (Encodable.encode a + 1)) <= f a
  证明: hf.rel_sequence a

Depends on / 依赖: hf.rel_sequence, rel_sequence
-/
theorem sequence_le (a : α) : f (hf.sequence f (Encodable.encode a + 1)) <= f a :=
  hf.rel_sequence a

end

end Directed

section Quotient

open Encodable Quotient

variable {α : Type*} {s : Setoid α} [DecidableRel (α := α) (· ≈ ·)] [Encodable α]

/--
Definition of `Quotient.rep` / `Quotient.rep` 的定义

English:
definition Quotient.rep
  signature: (q : Quotient s)
  body: choose (exists_rep q)

中文:
定义 Quotient.rep
  签名: (q : Quotient s)
  定义体: choose (exists_rep q)

Depends on / 依赖: exists_rep
-/
def Quotient.rep (q : Quotient s) : α :=
  choose (exists_rep q)

/--
theorem `Quotient.rep_spec` / 定理 `Quotient.rep_spec`

English:
theorem Quotient.rep_spec
  given: (q : Quotient s)
  statement: ⟦q.rep⟧ = q
  proof: choose_spec (exists_rep q)

中文:
定理 Quotient.rep_spec
  条件: (q : Quotient s)
  结论: ⟦q.rep⟧ = q
  证明: choose_spec (exists_rep q)

Depends on / 依赖: choose_spec, exists_rep
-/
theorem Quotient.rep_spec (q : Quotient s) : ⟦q.rep⟧ = q :=
  choose_spec (exists_rep q)

/-- The quotient of an encodable space by a decidable equivalence relation is encodable. -/
@[instance_reducible]
/--
Definition of `encodableQuotient` / `encodableQuotient` 的定义

English:
definition encodableQuotient
  signature: : Encodable (Quotient s)
  body: ⟨fun q => encode q.rep, fun n => Quotient.mk'' < > decode n, by
    rintro ⟨l⟩; dsimp; rw [encodek]; exact congr_arg some ⟦l⟧.rep_spec⟩

中文:
定义 encodableQuotient
  签名: : Encodable (Quotient s)
  定义体: ⟨fun q => encode q.rep, fun n => Quotient.mk'' < > decode n, by
    rintro ⟨l⟩; dsimp; rw [encodek]; exact congr_arg some ⟦l⟧.rep_spec⟩

Depends on / 依赖: Quotient, Quotient.mk, congr_arg, decode, encode, encodek, q.rep, rep_spec
-/
def encodableQuotient : Encodable (Quotient s) :=
⟨fun q => encode q.rep, fun n => Quotient.mk'' < > decode n, by
    rintro ⟨l⟩; dsimp; rw [encodek]; exact congr_arg some ⟦l⟧.rep_spec⟩

end Quotient
