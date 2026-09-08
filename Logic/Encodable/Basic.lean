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

/-- Constructively countable type. Made from an explicit injection `encode : α → ℕ` and a partial
inverse `decode : ℕ → Option α`. Note that finite types *are* countable. See `Denumerable` if you
wish to enforce infiniteness. -/
/-
**Encodable** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_1 → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructively countable type. Made from an explicit injection `encode : α → ℕ` 
and a partial
inverse `decode : ℕ → Option α`. Note that finite types *are* countable. See `De
numerable` if you
wish to enforce infiniteness.
-/
class Encodable (α : Type*) where
  /-- Encoding from Type α to ℕ -/
  encode : α → ℕ
  /-- Decoding from ℕ to Option α -/
  decode : ℕ → Option α
  /-- Invariant relationship between encoding and decoding -/
  encodek : ∀ a, decode (encode a) = some a

attribute [simp] Encodable.encodek

namespace Encodable

variable {α : Type*} {β : Type*}

universe u

/-
**Encodable.encode_injective** 是 Mathlib 中的一个定理，位于命名空间 `Encodable`。
形式化陈述：∀ {α : Type u_1} [inst : Encodable α], Function.Injective Encodable.encode
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Option.some.inj`：∀ {α : Type u} {val val_1 : α}, some val = some val_1 →
 val = val_1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Encodable.encodek`：∀ {α : Type u_1} [self : Encodable α] (a : α), Encoda
ble.decode (Encodable.encode a) = some a
-/
theorem encode_injective [Encodable α] : Function.Injective (@encode α _)
  | x, y, e => Option.some.inj <| by rw [← encodek, e, encodek]

@[simp]
/-
**Encodable.encode_inj** 是 Mathlib 中的一个定理，位于命名空间 `Encodable`。
形式化陈述：encode_inj [Encodable α] {a b : α} : encode a = encode b ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Encodable.encode_injective`：∀ {α : Type u_1} [inst : Encodable α], Funct
ion.Injective Encodable.encode
-/
theorem encode_inj [Encodable α] {a b : α} : encode a = encode b ↔ a = b :=
  encode_injective.eq_iff

-- The priority of the instance below is less than the priorities of `Subtype.Countable`
-- and `Quotient.Countable`
/-
**Encodable.** 是 Mathlib 中的一个实例，位于命名空间 `Encodable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 400) countable [Encodable α] : Countable α where
  exists_injective_nat' := ⟨_,encode_injective⟩
/-
**Encodable.surjective_decode_getD** 是 Mathlib 中的一个定理，位于命名空间 `Encodable`。
形式化陈述：surjective_decode_getD (α : Type*) [Encodable α] (d : α) : Surjective fun 
n => (Encodable.decode n).getD d
参数：α : Type*；d : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Encodable.encodek`：∀ {α : Type u_1} [self : Encodable α] (a : α), Encoda
ble.decode (Encodable.encode a) = some a
-/
theorem surjective_decode_getD (α : Type*) [Encodable α] (d : α) :
    Surjective fun n => (Encodable.decode n).getD d := fun x =>
  ⟨Encodable.encode x, by simp_rw [Encodable.encodek]; rfl⟩

@[deprecated surjective_decode_getD (since := "2026-01-05")]
/-
**Encodable.surjective_decode_iget** 是 Mathlib 中的一个定理，位于命名空间 `Encodable`。
形式化陈述：surjective_decode_iget (α : Type*) [Encodable α] [Inhabited α] : Surjectiv
e fun n => ((Encodable.decode n).getD default : α)
参数：α : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Encodable.surjective_decode_getD`：surjective_decode_getD (α : Type*) [En
codable α] (d : α) : Surjective fun n => (Encodable.decode n).getD d
-/
theorem surjective_decode_iget (α : Type*) [Encodable α] [Inhabited α] :
    Surjective fun n => ((Encodable.decode n).getD default : α) :=
  surjective_decode_getD α default

/-- An encodable type has decidable equality. Not set as an instance because this is usually not the
best way to infer decidability. -/
@[instance_reducible]
/-
**Encodable.decidableEqOfEncodable** 是 Mathlib 中的一个定义，位于命名空间 `Encodable`。
形式化陈述：(α : Type u_3) → [Encodable α] → DecidableEq α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Encodable.encode_inj`：encode_inj [Encodable α] {a b : α} : encode a = en
code b ↔ a = b

--- 原说明 ---
An encodable type has decidable equality. Not set as an instance because this is
 usually not the
best way to infer decidability.
-/
def decidableEqOfEncodable (α) [Encodable α] : DecidableEq α
  | _, _ => decidable_of_iff _ encode_inj

/-- If `α` is encodable and there is an injection `f : β → α`, then `β` is encodable as well. -/
@[instance_reducible]
/-
**Encodable.ofLeftInjection** 是 Mathlib 中的一个定义，位于命名空间 `Encodable`。
形式化陈述：ofLeftInjection [Encodable α] (f : β -> α) (finv : α -> Option β) (linv : 
forall b, finv (f b) = some b) : Encodable β
参数：f : β -> α；finv : α -> Option β；linv : forall b, finv (f b) = some b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `α` is encodable and there is an injection `f : β → α`, then `β` is encodable
 as well.
-/
def ofLeftInjection [Encodable α] (f : β → α) (finv : α → Option β)
    (linv : ∀ b, finv (f b) = some b) : Encodable β :=
  ⟨fun b => encode (f b), fun n => (decode n).bind finv, fun b => by
    simp [Encodable.encodek, linv]⟩

/-- If `α` is encodable and `f : β → α` is invertible, then `β` is encodable as well. -/
@[instance_reducible]
/-
**Encodable.ofLeftInverse** 是 Mathlib 中的一个定义，位于命名空间 `Encodable`。
形式化陈述：ofLeftInverse [Encodable α] (f : β -> α) (finv : α -> β) (linv : forall b,
 finv (f b) = b) : Encodable β
参数：f : β -> α；finv : α -> β；linv : forall b, finv (f b) = b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `α` is encodable and `f : β → α` is invertible, then `β` is encodable as well
.
-/
def ofLeftInverse [Encodable α] (f : β → α) (finv : α → β) (linv : ∀ b, finv (f b) = b) :
    Encodable β :=
  ofLeftInjection f (some ∘ finv) fun b => congr_arg some (linv b)

/-- Encodability is preserved by equivalence. -/
@[instance_reducible]
/-
**Encodable.ofEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Encodable`。
形式化陈述：ofEquiv (α) [Encodable α] (e : β ≃ α) : Encodable β
参数：α；e : β ≃ α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun

--- 原说明 ---
Encodability is preserved by equivalence.
-/
def ofEquiv (α) [Encodable α] (e : β ≃ α) : Encodable β :=
  ofLeftInverse e e.symm e.left_inv
/-
**Encodable.encode_ofEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Encodable`。
形式化陈述：encode_ofEquiv {α β} [Encodable α] (e : β ≃ α) (b : β) : @encode _ (ofEqui
v _ e) b = encode (e b)
参数：e : β ≃ α；b : β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem encode_ofEquiv {α β} [Encodable α] (e : β ≃ α) (b : β) :
    @encode _ (ofEquiv _ e) b = encode (e b) :=
  rfl
/-
**Encodable.decode_ofEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Encodable`。
形式化陈述：decode_ofEquiv {α β} [Encodable α] (e : β ≃ α) (n : Nat) : @decode _ (ofEq
uiv _ e) n = (decode n).map e.symm
参数：e : β ≃ α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Option.map_eq_bind`：∀ {α : Type u_1} {α_1 : Type u_2} {f : α → α_1} {x :
 Option α}, Option.map f x = x.bind (some ∘ f)
-/
theorem decode_ofEquiv {α β} [Encodable α] (e : β ≃ α) (n : ℕ) :
    @decode _ (ofEquiv _ e) n = (decode n).map e.symm :=
  show Option.bind _ _ = Option.map _ _
  by rw [Option.map_eq_bind]
/-
**Encodable._root_.Nat.encodable** 是 Mathlib 中的一个实例，位于命名空间 `Encodable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.Nat.encodable : Encodable ℕ :=
  ⟨id, some, fun _ => rfl⟩

@[simp]
/-
**Encodable.encode_nat** 是 Mathlib 中的一个定理，位于命名空间 `Encodable`。
形式化陈述：encode_nat (n : Nat) : encode n = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem encode_nat (n : ℕ) : encode n = n :=
  rfl

@[simp 1100]
/-
**Encodable.decode_nat** 是 Mathlib 中的一个定理，位于命名空间 `Encodable`。
形式化陈述：decode_nat (n : Nat) : decode n = some n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem decode_nat (n : ℕ) : decode n = some n :=
  rfl
/-
**Encodable.** 是 Mathlib 中的一个实例，位于命名空间 `Encodable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) _root_.IsEmpty.toEncodable [IsEmpty α] : Encodable α :=
  ⟨isEmptyElim, fun _ => none, isEmptyElim⟩
/-
**Encodable._root_.PUnit.encodable** 是 Mathlib 中的一个实例，位于命名空间 `Encodable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.PUnit.encodable : Encodable PUnit :=
  ⟨fun _ => 0, fun n => Nat.casesOn n (some PUnit.unit) fun _ => none, fun _ => by simp⟩

@[simp]
/-
**Encodable.encode_star** 是 Mathlib 中的一个定理，位于命名空间 `Encodable`。
形式化陈述：encode_star : encode PUnit.unit = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem encode_star : encode PUnit.unit = 0 :=
  rfl

@[simp]
/-
**Encodable.decode_unit_zero** 是 Mathlib 中的一个定理，位于命名空间 `Encodable`。
形式化陈述：decode_unit_zero : decode 0 = some PUnit.unit
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem decode_unit_zero : decode 0 = some PUnit.unit :=
  rfl

@[simp]
/-
**Encodable.decode_unit_succ** 是 Mathlib 中的一个定理，位于命名空间 `Encodable`。
形式化陈述：decode_unit_succ (n) : decode (succ n) = (none : Option PUnit)
参数：n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem decode_unit_succ (n) : decode (succ n) = (none : Option PUnit) :=
  rfl

/-- If `α` is encodable, then so is `Option α`. -/
/-
**Encodable._root_.Option.encodable** 是 Mathlib 中的一个实例，位于命名空间 `Encodable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `α` is encodable, then so is `Option α`.
-/
instance _root_.Option.encodable {α : Type*} [h : Encodable α] : Encodable (Option α) :=
  ⟨fun o => Option.casesOn o Nat.zero fun a => succ (encode a), fun n =>
    Nat.casesOn n (some none) fun m => (decode m).map some, fun o => by
    cases o <;> simp [encodek]⟩

@[simp]
/-
**Encodable.encode_none** 是 Mathlib 中的一个定理，位于命名空间 `Encodable`。
形式化陈述：encode_none [Encodable α] : encode (@none α) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem encode_none [Encodable α] : encode (@none α) = 0 :=
  rfl

@[simp]
/-
**Encodable.encode_some** 是 Mathlib 中的一个定理，位于命名空间 `Encodable`。
形式化陈述：encode_some [Encodable α] (a : α) : encode (some a) = succ (encode a)
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem encode_some [Encodable α] (a : α) : encode (some a) = succ (encode a) :=
  rfl

@[simp]
/-
**Encodable.decode_option_zero** 是 Mathlib 中的一个定理，位于命名空间 `Encodable`。
形式化陈述：decode_option_zero [Encodable α] : (decode 0 : Option (Option α)) = some n
one
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem decode_option_zero [Encodable α] : (decode 0 : Option (Option α)) = some none :=
  rfl

@[simp]
/-
**Encodable.decode_option_succ** 是 Mathlib 中的一个定理，位于命名空间 `Encodable`。
形式化陈述：decode_option_succ [Encodable α] (n) : (decode (succ n) : Option (Option α
)) = (decode n).map some
参数：n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem decode_option_succ [Encodable α] (n) :
    (decode (succ n) : Option (Option α)) = (decode n).map some :=
  rfl

/-- Failsafe variant of `decode`. `decode₂ α n` returns the preimage of `n` under `encode` if it
exists, and returns `none` if it doesn't. This requirement could be imposed directly on `decode` but
is not to help make the definition easier to use. -/
/-
**Encodable.decode** 是 Mathlib 中的一个定义，位于命名空间 `Encodable`。
形式化陈述：{α : Type u_1} → [self : Encodable α] → ℕ → Option α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Failsafe variant of `decode`. `decode₂ α n` returns the preimage of `n` under `e
ncode` if it
exists, and returns `none` if it doesn't. This requirement could be imposed dire
ctly on `decode` but
is not to help make the definition easier to use.
-/
def decode₂ (α) [Encodable α] (n : ℕ) : Option α :=
  (decode n).bind (Option.guard fun a => encode a = n)
/-
**Encodable.mem_decode** 是 Mathlib 中的一个定理，位于命名空间 `Encodable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_decode₂' [Encodable α] {n : ℕ} {a : α} :
    a ∈ decode₂ α n ↔ a ∈ decode n ∧ encode a = n := by
  simp [decode₂, Option.bind_eq_some_iff]
/-
**Encodable.mem_decode** 是 Mathlib 中的一个定理，位于命名空间 `Encodable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_decode₂ [Encodable α] {n : ℕ} {a : α} : a ∈ decode₂ α n ↔ encode a = n :=
  mem_decode₂'.trans (and_iff_right_of_imp fun e => e ▸ encodek _)
/-
**Encodable.decode** 是 Mathlib 中的一个定义，位于命名空间 `Encodable`。
形式化陈述：{α : Type u_1} → [self : Encodable α] → ℕ → Option α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem decode₂_eq_some [Encodable α] {n : ℕ} {a : α} : decode₂ α n = some a ↔ encode a = n :=
  mem_decode₂

@[simp]
/-
**Encodable.decode** 是 Mathlib 中的一个定义，位于命名空间 `Encodable`。
形式化陈述：{α : Type u_1} → [self : Encodable α] → ℕ → Option α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem decode₂_encode [Encodable α] (a : α) : decode₂ α (encode a) = some a := by
  simp [decode₂_eq_some]
/-
**Encodable.decode** 是 Mathlib 中的一个定义，位于命名空间 `Encodable`。
形式化陈述：{α : Type u_1} → [self : Encodable α] → ℕ → Option α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem decode₂_ne_none_iff [Encodable α] {n : ℕ} :
    decode₂ α n ≠ none ↔ n ∈ Set.range (encode : α → ℕ) := by
  simp_rw [Set.range, Set.mem_ofPred_eq, Ne, Option.eq_none_iff_forall_not_mem,
    Encodable.mem_decode₂, not_forall, not_not]
/-
**Encodable.decode** 是 Mathlib 中的一个定义，位于命名空间 `Encodable`。
形式化陈述：{α : Type u_1} → [self : Encodable α] → ℕ → Option α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem decode₂_isPartialInv [Encodable α] : IsPartialInv encode (decode₂ α) := fun _ _ =>
  mem_decode₂

@[deprecated (since := "2026-03-11")] alias decode₂_is_partial_inv := decode₂_isPartialInv
/-
**Encodable.decode** 是 Mathlib 中的一个定义，位于命名空间 `Encodable`。
形式化陈述：{α : Type u_1} → [self : Encodable α] → ℕ → Option α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem decode₂_inj [Encodable α] {n : ℕ} {a₁ a₂ : α} (h₁ : a₁ ∈ decode₂ α n)
    (h₂ : a₂ ∈ decode₂ α n) : a₁ = a₂ :=
  encode_injective <| (mem_decode₂.1 h₁).trans (mem_decode₂.1 h₂).symm
/-
**Encodable.encodek** 是 Mathlib 中的一个定理，位于命名空间 `Encodable`。
形式化陈述：∀ {α : Type u_1} [self : Encodable α] (a : α), Encodable.decode (Encodable
.encode a) = some a
参数：a : α；Encodable.encode a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem encodek₂ [Encodable α] (a : α) : decode₂ α (encode a) = some a :=
  mem_decode₂.2 rfl

/-- The encoding function has decidable range. -/
@[instance_reducible]
/-
**Encodable.decidableRangeEncode** 是 Mathlib 中的一个定义，位于命名空间 `Encodable`。
形式化陈述：decidableRangeEncode (α : Type*) [Encodable α] : DecidablePred (· in Set.r
ange (@encode α _))
参数：α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The encoding function has decidable range.
-/
def decidableRangeEncode (α : Type*) [Encodable α] : DecidablePred (· ∈ Set.range (@encode α _)) :=
  fun x =>
  decidable_of_iff (Option.isSome (decode₂ α x))
    ⟨fun h => ⟨Option.get _ h, by rw [← decode₂_isPartialInv (Option.get _ h), Option.some_get]⟩,
      fun ⟨n, hn⟩ => by rw [← hn, encodek₂]; exact rfl⟩

/-- An encodable type is equivalent to the range of its encoding function. -/
/-
**Encodable.equivRangeEncode** 是 Mathlib 中的一个定义，位于命名空间 `Encodable`。
形式化陈述：equivRangeEncode (α : Type*) [Encodable α] : α ≃ Set.range (@encode α _) w
here toFun a
参数：α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An encodable type is equivalent to the range of its encoding function.
-/
def equivRangeEncode (α : Type*) [Encodable α] : α ≃ Set.range (@encode α _) where
  toFun a := ⟨encode a, Set.mem_range_self _⟩
  invFun n :=
    Option.get _
      (show isSome (decode₂ α n.1) by obtain ⟨x, hx⟩ := n.2; rw [← hx, encodek₂]; exact rfl)
  left_inv _ := by dsimp; rw [← Option.some_inj, Option.some_get, encodek₂]
  right_inv _ := Subtype.ext <| decode₂_isPartialInv.get_eq _ _

/-- A type with unique element is encodable. This is not an instance to avoid diamonds. -/
@[instance_reducible]
/-
**Encodable._root_.Unique.encodable** 是 Mathlib 中的一个定义，位于命名空间 `Encodable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type with unique element is encodable. This is not an instance to avoid diamon
ds.
-/
def _root_.Unique.encodable [Unique α] : Encodable α :=
  ⟨fun _ => 0, fun _ => some default, Unique.forall_iff.2 rfl⟩

section Sum

variable [Encodable α] [Encodable β]

/-- Explicit encoding function for the sum of two encodable types. -/
/-
**Encodable.encodeSum** 是 Mathlib 中的一个定义，位于命名空间 `Encodable`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → [Encodable α] → [Encodable β] → α ⊕ β → 
ℕ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Explicit encoding function for the sum of two encodable types.
-/
def encodeSum : α ⊕ β → ℕ
  | Sum.inl a => 2 * encode a
  | Sum.inr b => 2 * encode b + 1

/-- Explicit decoding function for the sum of two encodable types. -/
/-
**Encodable.decodeSum** 是 Mathlib 中的一个定义，位于命名空间 `Encodable`。
形式化陈述：decodeSum (n : Nat) : Option (α oplus β)
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Explicit decoding function for the sum of two encodable types.
-/
def decodeSum (n : ℕ) : Option (α ⊕ β) :=
  match bodd n, div2 n with
  | false, m => (decode m : Option α).map Sum.inl
  | _, m => (decode m : Option β).map Sum.inr

/-- If `α` and `β` are encodable, then so is their sum. -/
/-
**Encodable._root_.Sum.encodable** 是 Mathlib 中的一个实例，位于命名空间 `Encodable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `α` and `β` are encodable, then so is their sum.
-/
instance _root_.Sum.encodable : Encodable (α ⊕ β) :=
  ⟨encodeSum, decodeSum, fun s => by cases s <;> simp [encodeSum, div2_val, decodeSum, encodek]⟩

@[simp]
/-
**Encodable.encode_inl** 是 Mathlib 中的一个定理，位于命名空间 `Encodable`。
形式化陈述：encode_inl (a : α) : @encode (α oplus β) _ (Sum.inl a) = 2 * (encode a)
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem encode_inl (a : α) : @encode (α ⊕ β) _ (Sum.inl a) = 2 * (encode a) :=
  rfl

@[simp]
/-
**Encodable.encode_inr** 是 Mathlib 中的一个定理，位于命名空间 `Encodable`。
形式化陈述：encode_inr (b : β) : @encode (α oplus β) _ (Sum.inr b) = 2 * (encode b) + 
1
参数：b : β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem encode_inr (b : β) : @encode (α ⊕ β) _ (Sum.inr b) = 2 * (encode b) + 1 :=
  rfl

@[simp]
/-
**Encodable.decode_sum_val** 是 Mathlib 中的一个定理，位于命名空间 `Encodable`。
形式化陈述：decode_sum_val (n : Nat) : (decode n : Option (α oplus β)) = decodeSum n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem decode_sum_val (n : ℕ) : (decode n : Option (α ⊕ β)) = decodeSum n :=
  rfl

end Sum

/-
**Encodable._root_.Bool.encodable** 是 Mathlib 中的一个实例，位于命名空间 `Encodable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.Bool.encodable : Encodable Bool :=
  ofEquiv (Unit ⊕ Unit) Equiv.boolEquivPUnitSumPUnit

@[simp]
/-
**Encodable.encode_true** 是 Mathlib 中的一个定理，位于命名空间 `Encodable`。
形式化陈述：encode_true : encode true = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem encode_true : encode true = 1 :=
  rfl

@[simp]
/-
**Encodable.encode_false** 是 Mathlib 中的一个定理，位于命名空间 `Encodable`。
形式化陈述：encode_false : encode false = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem encode_false : encode false = 0 :=
  rfl

@[simp]
/-
**Encodable.decode_zero** 是 Mathlib 中的一个定理，位于命名空间 `Encodable`。
形式化陈述：decode_zero : (decode 0 : Option Bool) = some false
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem decode_zero : (decode 0 : Option Bool) = some false :=
  rfl

@[simp]
/-
**Encodable.decode_one** 是 Mathlib 中的一个定理，位于命名空间 `Encodable`。
形式化陈述：decode_one : (decode 1 : Option Bool) = some true
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem decode_one : (decode 1 : Option Bool) = some true :=
  rfl
/-
**Encodable.decode_ge_two** 是 Mathlib 中的一个定理，位于命名空间 `Encodable`。
形式化陈述：decode_ge_two (n) (h : 2 <= n) : (decode n : Option Bool) = none
参数：n；h : 2 <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.le_div_iff_mul_le`：∀ {k x y : ℕ}, 0 < k → (x ≤ y / k ↔ x * k ≤ y)
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Nat.exists_eq_succ_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → ∃ k, n = k.succ
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem decode_ge_two (n) (h : 2 ≤ n) : (decode n : Option Bool) = none := by
  suffices decodeSum n = none by
    change (decodeSum n).bind _ = none
    rw [this]
    rfl
  have : 1 ≤ n / 2 := by
    rw [Nat.le_div_iff_mul_le]
    exacts [h, by decide]
  obtain ⟨m, e⟩ := exists_eq_succ_of_ne_zero (_root_.ne_of_gt this)
  simp only [decodeSum, div2_val]; cases bodd n <;> simp [e]
/-
**Encodable._root_.Prop.encodable** 是 Mathlib 中的一个实例，位于命名空间 `Encodable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance _root_.Prop.encodable : Encodable Prop :=
  ofEquiv Bool Equiv.propEquivBool

section Sigma

variable {γ : α → Type*} [Encodable α] [∀ a, Encodable (γ a)]

/-- Explicit encoding function for `Sigma γ` -/
/-
**Encodable.encodeSigma** 是 Mathlib 中的一个定义，位于命名空间 `Encodable`。
形式化陈述：{α : Type u_1} → {γ : α → Type u_3} → [Encodable α] → [(a : α) → Encodable
 (γ a)] → Sigma γ → ℕ
参数：a : α；γ a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Explicit encoding function for `Sigma γ`
-/
def encodeSigma : Sigma γ → ℕ
  | ⟨a, b⟩ => pair (encode a) (encode b)

/-- Explicit decoding function for `Sigma γ` -/
/-
**Encodable.decodeSigma** 是 Mathlib 中的一个定义，位于命名空间 `Encodable`。
形式化陈述：decodeSigma (n : Nat) : Option (Sigma γ)
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Explicit decoding function for `Sigma γ`
-/
def decodeSigma (n : ℕ) : Option (Sigma γ) :=
  let (n₁, n₂) := unpair n
  (decode n₁).bind fun a => (decode n₂).map <| Sigma.mk a
/-
**Encodable._root_.Sigma.encodable** 是 Mathlib 中的一个实例，位于命名空间 `Encodable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.Sigma.encodable : Encodable (Sigma γ) :=
  ⟨encodeSigma, decodeSigma, fun ⟨a, b⟩ => by
    simp [encodeSigma, decodeSigma, unpair_pair, encodek]⟩

@[simp]
/-
**Encodable.decode_sigma_val** 是 Mathlib 中的一个定理，位于命名空间 `Encodable`。
形式化陈述：decode_sigma_val (n : Nat) : (decode n : Option (Sigma γ)) = (decode n.unp
air.1).bind fun a => (decode n.unpair.2).map Sigma.mk a
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem decode_sigma_val (n : ℕ) :
    (decode n : Option (Sigma γ)) =
      (decode n.unpair.1).bind fun a => (decode n.unpair.2).map <| Sigma.mk a :=
  rfl

@[simp]
/-
**Encodable.encode_sigma_val** 是 Mathlib 中的一个定理，位于命名空间 `Encodable`。
形式化陈述：encode_sigma_val (a b) : @encode (Sigma γ) _ ⟨a, b⟩ = pair (encode a) (enc
ode b)
参数：a b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem encode_sigma_val (a b) : @encode (Sigma γ) _ ⟨a, b⟩ = pair (encode a) (encode b) :=
  rfl

end Sigma

section Prod

variable [Encodable α] [Encodable β]

/-- If `α` and `β` are encodable, then so is their product. -/
/-
**Encodable.Prod.encodable** 是 Mathlib 中的一个定义，位于命名空间 `Encodable.Prod`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → [Encodable α] → [Encodable β] → Encodabl
e (α × β)
参数：α × β。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If `α` and `β` are encodable, then so is their product.
-/
instance Prod.encodable : Encodable (α × β) :=
  ofEquiv _ (Equiv.sigmaEquivProd α β).symm

@[simp]
/-
**Encodable.decode_prod_val** 是 Mathlib 中的一个定理，位于命名空间 `Encodable`。
形式化陈述：decode_prod_val (n : Nat) : (@decode (α × β) _ n : Option (α × β)) = (deco
de n.unpair.1).bind fun a => (decode n.unpair.2).map Prod.mk a
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Encodable.decode_ofEquiv`：decode_ofEquiv {α β} [Encodable α] (e : β ≃ α)
 (n : Nat) : @decode _ (ofEquiv _ e) n = (decode n).map e.symm
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem decode_prod_val (n : ℕ) :
    (@decode (α × β) _ n : Option (α × β))
      = (decode n.unpair.1).bind fun a => (decode n.unpair.2).map <| Prod.mk a := by
  simp only [decode_ofEquiv, Equiv.symm_symm, decode_sigma_val]
  cases (decode n.unpair.1 : Option α) <;> cases (decode n.unpair.2 : Option β)
  <;> rfl

@[simp]
/-
**Encodable.encode_prod_val** 是 Mathlib 中的一个定理，位于命名空间 `Encodable`。
形式化陈述：encode_prod_val (a b) : @encode (α × β) _ (a, b) = pair (encode a) (encode
 b)
参数：a b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem encode_prod_val (a b) : @encode (α × β) _ (a, b) = pair (encode a) (encode b) :=
  rfl

end Prod

section Subtype

open Subtype Decidable

variable {P : α → Prop} [encA : Encodable α] [decP : DecidablePred P]

/-- Explicit encoding function for a decidable subtype of an encodable type -/
/-
**Encodable.encodeSubtype** 是 Mathlib 中的一个定义，位于命名空间 `Encodable`。
形式化陈述：{α : Type u_1} → {P : α → Prop} → [encA : Encodable α] → { a // P a } → ℕ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Explicit encoding function for a decidable subtype of an encodable type
-/
def encodeSubtype : { a : α // P a } → ℕ
  | ⟨v,_⟩ => encode v

/-- Explicit decoding function for a decidable subtype of an encodable type -/
/-
**Encodable.decodeSubtype** 是 Mathlib 中的一个定义，位于命名空间 `Encodable`。
形式化陈述：decodeSubtype (v : Nat) : Option { a : α // P a }
参数：v : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Explicit decoding function for a decidable subtype of an encodable type
-/
def decodeSubtype (v : ℕ) : Option { a : α // P a } :=
  (decode v).bind fun a => if h : P a then some ⟨a, h⟩ else none

/-- A decidable subtype of an encodable type is encodable. -/
/-
**Encodable._root_.Subtype.encodable** 是 Mathlib 中的一个实例，位于命名空间 `Encodable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A decidable subtype of an encodable type is encodable.
-/
instance _root_.Subtype.encodable : Encodable { a : α // P a } :=
  ⟨encodeSubtype, decodeSubtype, fun ⟨v, h⟩ => by simp [encodeSubtype, decodeSubtype, encodek, h]⟩
/-
**Encodable.Subtype.encode_eq** 是 Mathlib 中的一个定理，位于命名空间 `Encodable.Subtype`。
形式化陈述：∀ {α : Type u_1} {P : α → Prop} [encA : Encodable α] [decP : DecidablePred
 P] (a : Subtype P),   Encodable.encode a = Encodable.encode ↑a
参数：a : Subtype P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Subtype.encode_eq (a : Subtype P) : encode a = encode a.val := by cases a; rfl

end Subtype

/-
**Encodable._root_.Fin.encodable** 是 Mathlib 中的一个实例，位于命名空间 `Encodable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.Fin.encodable (n) : Encodable (Fin n) :=
  ofEquiv _ Fin.equivSubtype
/-
**Encodable._root_.Int.encodable** 是 Mathlib 中的一个实例，位于命名空间 `Encodable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.Int.encodable : Encodable ℤ :=
  ofEquiv _ Equiv.intEquivNat
/-
**Encodable._root_.PNat.encodable** 是 Mathlib 中的一个实例，位于命名空间 `Encodable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.PNat.encodable : Encodable ℕ+ :=
  ofEquiv _ Equiv.pnatEquivNat

/-- The lift of an encodable type is encodable -/
/-
**Encodable._root_.ULift.encodable** 是 Mathlib 中的一个实例，位于命名空间 `Encodable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The lift of an encodable type is encodable
-/
instance _root_.ULift.encodable [Encodable α] : Encodable (ULift α) :=
  ofEquiv _ Equiv.ulift

/-- The lift of an encodable type is encodable. -/
/-
**Encodable._root_.PLift.encodable** 是 Mathlib 中的一个实例，位于命名空间 `Encodable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The lift of an encodable type is encodable.
-/
instance _root_.PLift.encodable [Encodable α] : Encodable (PLift α) :=
  ofEquiv _ Equiv.plift

/-- If `β` is encodable and there is an injection `f : α → β`, then `α` is encodable as well. -/
@[instance_reducible]
/-
**Encodable.ofInj** 是 Mathlib 中的一个定义，位于命名空间 `Encodable`。
形式化陈述：ofInj [Encodable β] (f : α -> β) (hf : Injective f) : Encodable α
参数：f : α -> β；hf : Injective f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `β` is encodable and there is an injection `f : α → β`, then `α` is encodable
 as well.
-/
noncomputable def ofInj [Encodable β] (f : α → β) (hf : Injective f) : Encodable α :=
  ofLeftInjection f (partialInv f) hf.isPartialInv.eq

/-- If `α` is countable, then it has a (non-canonical) `Encodable` structure. -/
@[no_expose, instance_reducible]
/-
**Encodable.ofCountable** 是 Mathlib 中的一个定义，位于命名空间 `Encodable`。
形式化陈述：ofCountable (α : Type*) [Countable α] : Encodable α
参数：α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `α` is countable, then it has a (non-canonical) `Encodable` structure.
-/
noncomputable def ofCountable (α : Type*) [Countable α] : Encodable α :=
  Nonempty.some <|
    let ⟨f, hf⟩ := exists_injective_nat α
    ⟨ofInj f hf⟩

@[simp]
/-
**Encodable.nonempty_encodable** 是 Mathlib 中的一个定理，位于命名空间 `Encodable`。
形式化陈述：nonempty_encodable : Nonempty (Encodable α) ↔ Countable α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Encodable.countable`：∀ {α : Type u_1} [Encodable α], Countable α
-/
theorem nonempty_encodable : Nonempty (Encodable α) ↔ Countable α :=
  ⟨fun ⟨h⟩ => @Encodable.countable α h, fun h => ⟨@ofCountable _ h⟩⟩

end Encodable

/-- See also `nonempty_fintype`, `nonempty_denumerable`. -/
/-
**nonempty_encodable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nonempty_encodable (α : Type*) [Countable α] : Nonempty (Encodable α)
参数：α : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See also `nonempty_fintype`, `nonempty_denumerable`.
-/
theorem nonempty_encodable (α : Type*) [Countable α] : Nonempty (Encodable α) :=
  ⟨Encodable.ofCountable _⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Countable ℕ+ := by delta PNat; infer_instance

-- short-circuit instance search
section ULower

attribute [local instance] Encodable.decidableRangeEncode

/-- `ULower α : Type` is an equivalent type in the lowest universe, given `Encodable α`. -/
/-
**ULower** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ULower (α : Type*) [Encodable α] : Type
参数：α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ULower α : Type` is an equivalent type in the lowest universe, given `Encodable
 α`.
-/
def ULower (α : Type*) [Encodable α] : Type :=
  Set.range (Encodable.encode : α → ℕ)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α : Type*} [Encodable α] : DecidableEq (ULower α) := by
  delta ULower; exact Encodable.decidableEqOfEncodable _
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α : Type*} [Encodable α] : Encodable (ULower α) := by
  delta ULower; infer_instance

end ULower

namespace ULower

variable (α : Type*) [Encodable α]

/-- The equivalence between the encodable type `α` and `ULower α : Type`. -/
/-
**ULower.equiv** 是 Mathlib 中的一个定义，位于命名空间 `ULower`。
形式化陈述：equiv : α ≃ ULower α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between the encodable type `α` and `ULower α : Type`.
-/
def equiv : α ≃ ULower α :=
  Encodable.equivRangeEncode α

variable {α}

/-- Lowers an `a : α` into `ULower α`. -/
/-
**ULower.down** 是 Mathlib 中的一个定义，位于命名空间 `ULower`。
形式化陈述：down (a : α) : ULower α
参数：a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lowers an `a : α` into `ULower α`.
-/
def down (a : α) : ULower α :=
  equiv α a
/-
**ULower.** 是 Mathlib 中的一个实例，位于命名空间 `ULower`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inhabited α] : Inhabited (ULower α) :=
  ⟨down default⟩

/-- Lifts an `a : ULower α` into `α`. -/
/-
**ULower.up** 是 Mathlib 中的一个定义，位于命名空间 `ULower`。
形式化陈述：up (a : ULower α) : α
参数：a : ULower α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Lifts an `a : ULower α` into `α`.
-/
def up (a : ULower α) : α :=
  (equiv α).symm a

@[simp]
/-
**ULower.down_up** 是 Mathlib 中的一个定理，位于命名空间 `ULower`。
形式化陈述：down_up {a : ULower α} : down a.up = a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun
-/
theorem down_up {a : ULower α} : down a.up = a :=
  Equiv.right_inv _ _

@[simp]
/-
**ULower.up_down** 是 Mathlib 中的一个定理，位于命名空间 `ULower`。
形式化陈述：up_down {a : α} : (down a).up = a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem up_down {a : α} : (down a).up = a := by
  simp [up, down, Equiv.symm_apply_apply]

@[simp]
/-
**ULower.up_eq_up** 是 Mathlib 中的一个定理，位于命名空间 `ULower`。
形式化陈述：up_eq_up {a b : ULower α} : a.up = b.up ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.apply_eq_iff_eq`：apply_eq_iff_eq (f : α ≃ β) {x y : α} : f x = f y
 ↔ x = y
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem up_eq_up {a b : ULower α} : a.up = b.up ↔ a = b :=
  Equiv.apply_eq_iff_eq _

@[simp]
/-
**ULower.down_eq_down** 是 Mathlib 中的一个定理，位于命名空间 `ULower`。
形式化陈述：down_eq_down {a b : α} : down a = down b ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.apply_eq_iff_eq`：apply_eq_iff_eq (f : α ≃ β) {x y : α} : f x = f y
 ↔ x = y
-/
theorem down_eq_down {a b : α} : down a = down b ↔ a = b :=
  Equiv.apply_eq_iff_eq _

@[ext]
/-
**ULower.ext** 是 Mathlib 中的一个定理，位于命名空间 `ULower`。
形式化陈述：∀ {α : Type u_1} [inst : Encodable α] {a b : ULower α}, a.up = b.up → a = 
b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ULower.up_eq_up`：up_eq_up {a b : ULower α} : a.up = b.up ↔ a = b
-/
protected theorem ext {a b : ULower α} : a.up = b.up → a = b :=
  up_eq_up.1

end ULower

/-
Choice function for encodable types and decidable predicates.
We provide the following API

choose      {α : Type*} {p : α → Prop} [c : encodable α] [d : decidable_pred p] : (∃ x, p x) → α :=
choose_spec {α : Type*} {p : α → Prop} [c : encodable α] [d : decidable_pred p] (ex : ∃ x, p x) :
  p (choose ex) :=
-/
namespace Encodable

section FindA

variable {α : Type*} (p : α → Prop) [Encodable α] [DecidablePred p]

set_option backward.privateInPublic true in
/-
**Encodable.good** 是 Mathlib 中的一个定义，位于命名空间 `Encodable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def good : Option α → Prop
  | some a => p a
  | none => False

set_option backward.privateInPublic true in
private local instance decidable_good : DecidablePred (good p)
  | some a => inferInstanceAs <| Decidable (p a)
  | none => inferInstanceAs <| Decidable False

open Encodable

variable {p}

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Constructive choice function for a decidable subtype of an encodable type. -/
/-
**Encodable.chooseX** 是 Mathlib 中的一个定义，位于命名空间 `Encodable`。
形式化陈述：chooseX (h : exists x, p x) : { a : α // p a }
参数：h : exists x, p x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructive choice function for a decidable subtype of an encodable type.
-/
def chooseX (h : ∃ x, p x) : { a : α // p a } :=
  have : ∃ n, good p (decode n) :=
    let ⟨w, pw⟩ := h
    ⟨encode w, by simp [good, encodek, pw]⟩
  match (motive := ∀ o, good p o → { a // p a }) _, Nat.find_spec this with
  | some a, h => ⟨a, h⟩

/-- Constructive choice function for a decidable predicate over an encodable type. -/
/-
**Encodable.choose** 是 Mathlib 中的一个定义，位于命名空间 `Encodable`。
形式化陈述：choose (h : exists x, p x) : α
参数：h : exists x, p x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructive choice function for a decidable predicate over an encodable type.
-/
def choose (h : ∃ x, p x) : α :=
  (chooseX h).1
/-
**Encodable.choose_spec** 是 Mathlib 中的一个定理，位于命名空间 `Encodable`。
形式化陈述：choose_spec (h : exists x, p x) : p (choose h)
参数：h : exists x, p x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem choose_spec (h : ∃ x, p x) : p (choose h) :=
  (chooseX h).2

end FindA

/-- A constructive version of `Classical.axiom_of_choice` for `Encodable` types. -/
/-
**Encodable.axiom_of_choice** 是 Mathlib 中的一个定理，位于命名空间 `Encodable`。
形式化陈述：axiom_of_choice {α : Type*} {β : α -> Type*} {R : forall x, β x -> Prop} [
forall a, Encodable (β a)] [forall x y, Decidable (R x y)] (H : forall x, exists
 y, R x y) : exists f : forall a, β a, forall x, R x (f x)
参数：β a；R x y；H : forall x, exists y, R x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Encodable.choose_spec`：choose_spec (h : exists x, p x) : p (choose h)

--- 原说明 ---
A constructive version of `Classical.axiom_of_choice` for `Encodable` types.
-/
theorem axiom_of_choice {α : Type*} {β : α → Type*} {R : ∀ x, β x → Prop} [∀ a, Encodable (β a)]
    [∀ x y, Decidable (R x y)] (H : ∀ x, ∃ y, R x y) : ∃ f : ∀ a, β a, ∀ x, R x (f x) :=
  ⟨fun x => choose (H x), fun x => choose_spec (H x)⟩

/-- A constructive version of `Classical.skolem` for `Encodable` types. -/
/-
**Encodable.skolem** 是 Mathlib 中的一个定理，位于命名空间 `Encodable`。
形式化陈述：skolem {α : Type*} {β : α -> Type*} {P : forall x, β x -> Prop} [forall a,
 Encodable (β a)] [forall x y, Decidable (P x y)] : (forall x, exists y, P x y) 
↔ exists f : forall a, β a, forall x, P x (f x)
参数：β a；P x y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Encodable.axiom_of_choice`：axiom_of_choice {α : Type*} {β : α -> Type*} 
{R : forall x, β x -> Prop} [forall a, Encodable (β a)] [forall x y, Decidable (
R x y)] (H : fo…

--- 原说明 ---
A constructive version of `Classical.skolem` for `Encodable` types.
-/
theorem skolem {α : Type*} {β : α → Type*} {P : ∀ x, β x → Prop} [∀ a, Encodable (β a)]
    [∀ x y, Decidable (P x y)] : (∀ x, ∃ y, P x y) ↔ ∃ f : ∀ a, β a, ∀ x, P x (f x) :=
  ⟨axiom_of_choice, fun ⟨_, H⟩ x => ⟨_, H x⟩⟩

/-
There is a total ordering on the elements of an encodable type, induced by the map to ℕ.
-/
/-- The `encode` function, viewed as an embedding. -/
/-
**Encodable.encode'** 是 Mathlib 中的一个定义，位于命名空间 `Encodable`。
形式化陈述：encode' (α) [Encodable α] : α ↪ Nat
参数：α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Encodable.encode_injective`：∀ {α : Type u_1} [inst : Encodable α], Funct
ion.Injective Encodable.encode

--- 原说明 ---
The `encode` function, viewed as an embedding.
-/
def encode' (α) [Encodable α] : α ↪ ℕ :=
  ⟨Encodable.encode, Encodable.encode_injective⟩
/-
**Encodable.** 是 Mathlib 中的一个实例，位于命名空间 `Encodable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α} [Encodable α] : Std.Antisymm (Encodable.encode' α ⁻¹'o (· ≤ ·)) :=
  (RelEmbedding.preimage _ _).antisymm
/-
**Encodable.** 是 Mathlib 中的一个实例，位于命名空间 `Encodable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α} [Encodable α] : Std.Total (Encodable.encode' α ⁻¹'o (· ≤ ·)) :=
  (RelEmbedding.preimage _ _).total

end Encodable

namespace Directed

open Encodable

variable {α : Type*} {β : Type*} [Encodable α] [Inhabited α]

/-- Given a `Directed r` function `f : α → β` defined on an encodable inhabited type,
construct a noncomputable sequence such that `r (f (x n)) (f (x (n + 1)))`
and `r (f a) (f (x (encode a + 1))`. -/
/-
**Directed.sequence** 是 Mathlib 中的一个定义，位于命名空间 `Directed`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} → [Encodable α] → [Inhabited α] → {r : β
 → β → Prop} → (f : α → β) → Directed r f → ℕ → α
参数：f : α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a `Directed r` function `f : α → β` defined on an encodable inhabited type
,
construct a noncomputable sequence such that `r (f (x n)) (f (x (n + 1)))`
and `r (f a) (f (x (encode a + 1))`.
-/
protected noncomputable def sequence {r : β → β → Prop} (f : α → β) (hf : Directed r f) : ℕ → α
  | 0 => default
  | n + 1 =>
    let p := Directed.sequence f hf n
    match (decode n : Option α) with
    | none => Classical.choose (hf p p)
    | some a => Classical.choose (hf p a)
/-
**Directed.sequence_mono_nat** 是 Mathlib 中的一个定理，位于命名空间 `Directed`。
形式化陈述：sequence_mono_nat {r : β -> β -> Prop} {f : α -> β} (hf : Directed r f) (n
 : Nat) : r (f (hf.sequence f n)) (f (hf.sequence f (n + 1)))
参数：hf : Directed r f；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem sequence_mono_nat {r : β → β → Prop} {f : α → β} (hf : Directed r f) (n : ℕ) :
    r (f (hf.sequence f n)) (f (hf.sequence f (n + 1))) := by
  dsimp [Directed.sequence]
  generalize hf.sequence f n = p
  rcases (decode n : Option α) with - | a
  · exact (Classical.choose_spec (hf p p)).1
  · exact (Classical.choose_spec (hf p a)).1
/-
**Directed.rel_sequence** 是 Mathlib 中的一个定理，位于命名空间 `Directed`。
形式化陈述：rel_sequence {r : β -> β -> Prop} {f : α -> β} (hf : Directed r f) (a : α)
 : r (f a) (f (hf.sequence f (encode a + 1)))
参数：hf : Directed r f；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Encodable.encodek`：∀ {α : Type u_1} [self : Encodable α] (a : α), Encoda
ble.decode (Encodable.encode a) = some a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem rel_sequence {r : β → β → Prop} {f : α → β} (hf : Directed r f) (a : α) :
    r (f a) (f (hf.sequence f (encode a + 1))) := by
  simp only [Directed.sequence, encodek]
  exact (Classical.choose_spec (hf _ a)).2

variable [Preorder β] {f : α → β}

section

variable (hf : Directed (· ≤ ·) f)

/-
**Directed.sequence_mono** 是 Mathlib 中的一个定理，位于命名空间 `Directed`。
形式化陈述：sequence_mono : Monotone (f ∘ hf.sequence f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `monotone_nat_of_le_succ`：monotone_nat_of_le_succ {f : Nat -> α} (hf : fo
rall n, f n <= f (n + 1)) : Monotone f
· 使用定理 `Directed.sequence_mono_nat`：sequence_mono_nat {r : β -> β -> Prop} {f : 
α -> β} (hf : Directed r f) (n : Nat) : r (f (hf.sequence f n)) (f (hf.sequence 
f (n + 1)))
-/
theorem sequence_mono : Monotone (f ∘ hf.sequence f) :=
  monotone_nat_of_le_succ <| hf.sequence_mono_nat
/-
**Directed.le_sequence** 是 Mathlib 中的一个定理，位于命名空间 `Directed`。
形式化陈述：le_sequence (a : α) : f a <= f (hf.sequence f (encode a + 1))
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Directed.rel_sequence`：rel_sequence {r : β -> β -> Prop} {f : α -> β} (h
f : Directed r f) (a : α) : r (f a) (f (hf.sequence f (encode a + 1)))
-/
theorem le_sequence (a : α) : f a ≤ f (hf.sequence f (encode a + 1)) :=
  hf.rel_sequence a

end

section

variable (hf : Directed (· ≥ ·) f)

/-
**Directed.sequence_anti** 是 Mathlib 中的一个定理，位于命名空间 `Directed`。
形式化陈述：sequence_anti : Antitone (f ∘ hf.sequence f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `antitone_nat_of_succ_le`：antitone_nat_of_succ_le {f : Nat -> α} (hf : fo
rall n, f (n + 1) <= f n) : Antitone f
· 使用定理 `Directed.sequence_mono_nat`：sequence_mono_nat {r : β -> β -> Prop} {f : 
α -> β} (hf : Directed r f) (n : Nat) : r (f (hf.sequence f n)) (f (hf.sequence 
f (n + 1)))
-/
theorem sequence_anti : Antitone (f ∘ hf.sequence f) :=
  antitone_nat_of_succ_le <| hf.sequence_mono_nat
/-
**Directed.sequence_le** 是 Mathlib 中的一个定理，位于命名空间 `Directed`。
形式化陈述：sequence_le (a : α) : f (hf.sequence f (Encodable.encode a + 1)) <= f a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Directed.rel_sequence`：rel_sequence {r : β -> β -> Prop} {f : α -> β} (h
f : Directed r f) (a : α) : r (f a) (f (hf.sequence f (encode a + 1)))
-/
theorem sequence_le (a : α) : f (hf.sequence f (Encodable.encode a + 1)) ≤ f a :=
  hf.rel_sequence a

end

end Directed

section Quotient

open Encodable Quotient

variable {α : Type*} {s : Setoid α} [DecidableRel (α := α) (· ≈ ·)] [Encodable α]

/-- Representative of an equivalence class. This is a computable version of `Quot.out` for a setoid
on an encodable type. -/
/-
**Quotient.rep** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Quotient.rep (q : Quotient s) : α
参数：q : Quotient s。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.exists_rep`：∀ {α : Sort u} {s : Setoid α} (q : Quotient s), ∃ a
, ⟦a⟧ = q

--- 原说明 ---
Representative of an equivalence class. This is a computable version of `Quot.ou
t` for a setoid
on an encodable type.
-/
def Quotient.rep (q : Quotient s) : α :=
  choose (exists_rep q)
/-
**Quotient.rep_spec** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Quotient.rep_spec (q : Quotient s) : ⟦q.rep⟧ = q
参数：q : Quotient s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Encodable.choose_spec`：choose_spec (h : exists x, p x) : p (choose h)
· 使用定理 `Quotient.exists_rep`：∀ {α : Sort u} {s : Setoid α} (q : Quotient s), ∃ a
, ⟦a⟧ = q
-/
theorem Quotient.rep_spec (q : Quotient s) : ⟦q.rep⟧ = q :=
  choose_spec (exists_rep q)

/-- The quotient of an encodable space by a decidable equivalence relation is encodable. -/
@[instance_reducible]
/-
**encodableQuotient** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：encodableQuotient : Encodable (Quotient s)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)

--- 原说明 ---
The quotient of an encodable space by a decidable equivalence relation is encoda
ble.
-/
def encodableQuotient : Encodable (Quotient s) :=
  ⟨fun q => encode q.rep, fun n => Quotient.mk'' <$> decode n, by
    rintro ⟨l⟩; dsimp; rw [encodek]; exact congr_arg some ⟦l⟧.rep_spec⟩

end Quotient

