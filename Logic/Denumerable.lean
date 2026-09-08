/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.List.MinMax
public import Mathlib.Data.Nat.Order.Lemmas
public import Mathlib.Logic.Encodable.Basic

/-!
# Denumerable types

This file defines denumerable (countably infinite) types as a typeclass extending `Encodable`. This
is used to provide explicit encode/decode functions from and to `ℕ`, with the information that those
functions are inverses of each other.

## Implementation notes

This property already has a name, namely `α ≃ ℕ`, but here we are interested in using it as a
typeclass.
-/

@[expose] public section

assert_not_exists Monoid

variable {α β : Type*}

/-- A denumerable type is (constructively) bijective with `ℕ`. Typeclass equivalent of `α ≃ ℕ`. -/
/-
**Denumerable** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_3 → Type u_3
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A denumerable type is (constructively) bijective with `ℕ`. Typeclass equivalent 
of `α ≃ ℕ`.
-/
class Denumerable (α : Type*) extends Encodable α where
  /-- `decode` and `encode` are inverses. -/
  decode_inv : ∀ n, ∃ a ∈ decode n, encode a = n

open Finset Nat

namespace Denumerable

section

variable [Denumerable α] [Denumerable β]

open Encodable

/-
**Denumerable.decode_isSome** 是 Mathlib 中的一个定理，位于命名空间 `Denumerable`。
形式化陈述：decode_isSome (α) [Denumerable α] (n : Nat) : (decode (α
参数：α；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Option.isSome_iff_exists`：∀ {α : Type u_1} {x : Option α}, x.isSome = tr
ue ↔ ∃ a, x = some a
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Denumerable.decode_inv`：∀ {α : Type u_3} [self : Denumerable α] (n : ℕ),
 ∃ a ∈ Encodable.decode n, Encodable.encode a = n
-/
theorem decode_isSome (α) [Denumerable α] (n : ℕ) : (decode (α := α) n).isSome :=
  Option.isSome_iff_exists.2 <| (decode_inv n).imp fun _ => And.left

/-- Returns the `n`-th element of `α` indexed by the decoding. -/
/-
**Denumerable.ofNat** 是 Mathlib 中的一个定义，位于命名空间 `Denumerable`。
形式化陈述：ofNat (α) [Denumerable α] (n : Nat) : α
参数：α；n : Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Denumerable.decode_isSome`：decode_isSome (α) [Denumerable α] (n : Nat) :
 (decode (α

--- 原说明 ---
Returns the `n`-th element of `α` indexed by the decoding.
-/
def ofNat (α) [Denumerable α] (n : ℕ) : α :=
  Option.get _ (decode_isSome α n)

@[simp]
/-
**Denumerable.decode_eq_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Denumerable`。
形式化陈述：decode_eq_ofNat (α) [Denumerable α] (n : Nat) : decode (α
参数：α；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Option.eq_some_of_isSome`：∀ {α : Type u_1} {o : Option α} (h : o.isSome 
= true), o = some (o.get h)
· 使用定理 `Denumerable.decode_isSome`：decode_isSome (α) [Denumerable α] (n : Nat) :
 (decode (α
-/
theorem decode_eq_ofNat (α) [Denumerable α] (n : ℕ) : decode (α := α) n = some (ofNat α n) :=
  Option.eq_some_of_isSome _
/-
**Denumerable.ofNat_of_decode** 是 Mathlib 中的一个定理，位于命名空间 `Denumerable`。
形式化陈述：ofNat_of_decode {n b} (h : decode (α
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Denumerable.decode_eq_ofNat`：decode_eq_ofNat (α) [Denumerable α] (n : Na
t) : decode (α
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
-/
theorem ofNat_of_decode {n b} (h : decode (α := α) n = some b) : ofNat (α := α) n = b := by
  simpa using h

@[simp]
/-
**Denumerable.encode_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Denumerable`。
形式化陈述：encode_ofNat (n) : encode (ofNat α n) = n
参数：n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Denumerable.decode_inv`：∀ {α : Type u_3} [self : Denumerable α] (n : ℕ),
 ∃ a ∈ Encodable.decode n, Encodable.encode a = n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Denumerable.ofNat_of_decode`：ofNat_of_decode {n b} (h : decode (α
-/
theorem encode_ofNat (n) : encode (ofNat α n) = n := by
  obtain ⟨a, h, e⟩ := decode_inv (α := α) n
  rwa [ofNat_of_decode h]

@[simp]
/-
**Denumerable.ofNat_encode** 是 Mathlib 中的一个定理，位于命名空间 `Denumerable`。
形式化陈述：ofNat_encode (a) : ofNat α (encode a) = a
参数：a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Denumerable.ofNat_of_decode`：ofNat_of_decode {n b} (h : decode (α
· 使用定理 `Encodable.encodek`：∀ {α : Type u_1} [self : Encodable α] (a : α), Encoda
ble.decode (Encodable.encode a) = some a
-/
theorem ofNat_encode (a) : ofNat α (encode a) = a :=
  ofNat_of_decode (encodek _)

/-- A denumerable type is equivalent to `ℕ`. -/
/-
**Denumerable.eqv** 是 Mathlib 中的一个定义，位于命名空间 `Denumerable`。
形式化陈述：eqv (α) [Denumerable α] : α ≃ Nat
参数：α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Denumerable.ofNat_encode`：ofNat_encode (a) : ofNat α (encode a) = a
· 使用定理 `Denumerable.encode_ofNat`：encode_ofNat (n) : encode (ofNat α n) = n

--- 原说明 ---
A denumerable type is equivalent to `ℕ`.
-/
def eqv (α) [Denumerable α] : α ≃ ℕ :=
  ⟨encode, ofNat α, ofNat_encode, encode_ofNat⟩

-- See Note [lower instance priority]
/-
**Denumerable.** 是 Mathlib 中的一个实例，位于命名空间 `Denumerable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) : Infinite α :=
  Infinite.of_surjective _ (eqv α).surjective

/-- A type equivalent to `ℕ` is denumerable. -/
@[instance_reducible]
/-
**Denumerable.mk'** 是 Mathlib 中的一个定义，位于命名空间 `Denumerable`。
形式化陈述：mk' {α} (e : α ≃ Nat) : Denumerable α where encode
参数：e : α ≃ Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
A type equivalent to `ℕ` is denumerable.
-/
def mk' {α} (e : α ≃ ℕ) : Denumerable α where
  encode := e
  decode := some ∘ e.symm
  encodek _ := congr_arg some (e.symm_apply_apply _)
  decode_inv _ := ⟨_, rfl, e.apply_symm_apply _⟩

/-- Denumerability is conserved by equivalences. This is transitivity of equivalence the denumerable
way. -/
@[instance_reducible]
/-
**Denumerable.ofEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Denumerable`。
形式化陈述：ofEquiv (α) {β} [Denumerable α] (e : β ≃ α) : Denumerable β
参数：α；e : β ≃ α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Denumerability is conserved by equivalences. This is transitivity of equivalence
 the denumerable
way.
-/
def ofEquiv (α) {β} [Denumerable α] (e : β ≃ α) : Denumerable β :=
  { Encodable.ofEquiv _ e with
    decode_inv := fun n => by
      simp [decode_ofEquiv, encode_ofEquiv] }

@[simp]
/-
**Denumerable.ofEquiv_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Denumerable`。
形式化陈述：ofEquiv_ofNat (α) {β} [Denumerable α] (e : β ≃ α) (n) : @ofNat β (ofEquiv 
_ e) n = e.symm (ofNat α n)
参数：α；e : β ≃ α；n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Denumerable.ofNat_of_decode`：ofNat_of_decode {n b} (h : decode (α
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Encodable.decode_ofEquiv`：decode_ofEquiv {α β} [Encodable α] (e : β ≃ α)
 (n : Nat) : @decode _ (ofEquiv _ e) n = (decode n).map e.symm
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Denumerable.decode_eq_ofNat`：decode_eq_ofNat (α) [Denumerable α] (n : Na
t) : decode (α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofEquiv_ofNat (α) {β} [Denumerable α] (e : β ≃ α) (n) :
    @ofNat β (ofEquiv _ e) n = e.symm (ofNat α n) := by
  let := ofEquiv _ e
  refine ofNat_of_decode ?_
  rw [decode_ofEquiv e]
  simp

/-- All denumerable types are equivalent. -/
/-
**Denumerable.equiv** 是 Mathlib 中的一个定义，位于命名空间 `Denumerable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
All denumerable types are equivalent.
-/
def equiv₂ (α β) [Denumerable α] [Denumerable β] : α ≃ β :=
  (eqv α).trans (eqv β).symm
/-
**Denumerable.nat** 是 Mathlib 中的一个实例，位于命名空间 `Denumerable`。
形式化陈述：nat : Denumerable Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance nat : Denumerable ℕ :=
  ⟨fun _ => ⟨_, rfl, rfl⟩⟩

@[simp]
/-
**Denumerable.ofNat_nat** 是 Mathlib 中的一个定理，位于命名空间 `Denumerable`。
形式化陈述：ofNat_nat (n) : ofNat Nat n = n
参数：n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofNat_nat (n) : ofNat ℕ n = n :=
  rfl

/-- If `α` is denumerable, then so is `Option α`. -/
/-
**Denumerable.option** 是 Mathlib 中的一个实例，位于命名空间 `Denumerable`。
形式化陈述：option : Denumerable (Option α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `α` is denumerable, then so is `Option α`.
-/
instance option : Denumerable (Option α) :=
  ⟨fun n => by
    cases n with
    | zero =>
      refine ⟨none, ?_, encode_none⟩
      rw [decode_option_zero, Option.mem_def]
    | succ n =>
      refine ⟨some (ofNat α n), ?_, ?_⟩
      · rw [decode_option_succ, decode_eq_ofNat, Option.map_some, Option.mem_def]
      rw [encode_some, encode_ofNat]⟩

/-- If `α` and `β` are denumerable, then so is their sum. -/
/-
**Denumerable.sum** 是 Mathlib 中的一个实例，位于命名空间 `Denumerable`。
形式化陈述：sum : Denumerable (α oplus β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `α` and `β` are denumerable, then so is their sum.
-/
instance sum : Denumerable (α ⊕ β) :=
  ⟨fun n => by
    suffices ∃ a ∈ @decodeSum α β _ _ n, encodeSum a = bit (bodd n) (div2 n) by
      simpa [bit_bodd_div2]
    simp only [decodeSum, decode_eq_ofNat, Option.map_some, Sum.exists]
    cases bodd n <;> simp [bit_val, encodeSum]⟩

section Sigma

variable {γ : α → Type*} [∀ a, Denumerable (γ a)]

/-- A denumerable collection of denumerable types is denumerable. -/
/-
**Denumerable.sigma** 是 Mathlib 中的一个实例，位于命名空间 `Denumerable`。
形式化陈述：sigma : Denumerable (Sigma γ)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A denumerable collection of denumerable types is denumerable.
-/
instance sigma : Denumerable (Sigma γ) :=
  ⟨fun n => by simp⟩

@[simp]
/-
**Denumerable.sigma_ofNat_val** 是 Mathlib 中的一个定理，位于命名空间 `Denumerable`。
形式化陈述：sigma_ofNat_val (n : Nat) : ofNat (Sigma γ) n = ⟨ofNat α (unpair n).1, ofN
at (γ _) (unpair n).2⟩
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Option.some.inj`：∀ {α : Type u} {val val_1 : α}, some val = some val_1 →
 val = val_1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Denumerable.decode_eq_ofNat`：decode_eq_ofNat (α) [Denumerable α] (n : Na
t) : decode (α
· 使用定理 `Encodable.decode_sigma_val`：decode_sigma_val (n : Nat) : (decode n : Opt
ion (Sigma γ)) = (decode n.unpair.1).bind fun a => (decode n.unpair.2).map Sigma
.mk a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Option.bind_congr'`：bind_congr' {f g : α -> Option β} {x y : Option α} (
hx : x = y) (hf : forall a in y, f a = g a) : x.bind f = y.bind g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sigma_ofNat_val (n : ℕ) :
    ofNat (Sigma γ) n = ⟨ofNat α (unpair n).1, ofNat (γ _) (unpair n).2⟩ :=
  Option.some.inj <| by rw [← decode_eq_ofNat, decode_sigma_val]; simp

end Sigma

/-- If `α` and `β` are denumerable, then so is their product. -/
/-
**Denumerable.prod** 是 Mathlib 中的一个实例，位于命名空间 `Denumerable`。
形式化陈述：prod : Denumerable (α × β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If `α` and `β` are denumerable, then so is their product.
-/
instance prod : Denumerable (α × β) :=
  ofEquiv _ (Equiv.sigmaEquivProd α β).symm
/-
**Denumerable.prod_ofNat_val** 是 Mathlib 中的一个定理，位于命名空间 `Denumerable`。
形式化陈述：prod_ofNat_val (n : Nat) : ofNat (α × β) n = (ofNat α (unpair n).1, ofNat 
β (unpair n).2)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Denumerable.ofEquiv_ofNat`：ofEquiv_ofNat (α) {β} [Denumerable α] (e : β 
≃ α) (n) : @ofNat β (ofEquiv _ e) n = e.symm (ofNat α n)
· 使用定理 `Denumerable.sigma_ofNat_val`：sigma_ofNat_val (n : Nat) : ofNat (Sigma γ)
 n = ⟨ofNat α (unpair n).1, ofNat (γ _) (unpair n).2⟩
· 使用定理 `Equiv.sigmaEquivProd_apply`：∀ (α : Type u_1) (β : Type u_2) (a : (_ : α)
 × β), (Equiv.sigmaEquivProd α β) a = (a.fst, a.snd)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_ofNat_val (n : ℕ) :
    ofNat (α × β) n = (ofNat α (unpair n).1, ofNat β (unpair n).2) := by simp

@[simp]
/-
**Denumerable.prod_nat_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Denumerable`。
形式化陈述：prod_nat_ofNat : ofNat (Nat × Nat) = unpair
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Denumerable.ofEquiv_ofNat`：ofEquiv_ofNat (α) {β} [Denumerable α] (e : β 
≃ α) (n) : @ofNat β (ofEquiv _ e) n = e.symm (ofNat α n)
· 使用定理 `Denumerable.sigma_ofNat_val`：sigma_ofNat_val (n : Nat) : ofNat (Sigma γ)
 n = ⟨ofNat α (unpair n).1, ofNat (γ _) (unpair n).2⟩
· 使用定理 `Equiv.sigmaEquivProd_apply`：∀ (α : Type u_1) (β : Type u_2) (a : (_ : α)
 × β), (Equiv.sigmaEquivProd α β) a = (a.fst, a.snd)
· 使用定理 `Prod.mk.eta`：∀ {α : Type u_1} {β : Type u_2} {p : α × β}, (p.1, p.2) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_nat_ofNat : ofNat (ℕ × ℕ) = unpair := by funext; simp
/-
**Denumerable.int** 是 Mathlib 中的一个实例，位于命名空间 `Denumerable`。
形式化陈述：int : Denumerable Int
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance int : Denumerable ℤ :=
  fast_instance% Denumerable.mk' Equiv.intEquivNat
/-
**Denumerable.pnat** 是 Mathlib 中的一个实例，位于命名空间 `Denumerable`。
形式化陈述：pnat : Denumerable Nat+
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance pnat : Denumerable ℕ+ :=
  fast_instance% Denumerable.mk' Equiv.pnatEquivNat

/-- The lift of a denumerable type is denumerable. -/
/-
**Denumerable.ulift** 是 Mathlib 中的一个实例，位于命名空间 `Denumerable`。
形式化陈述：ulift : Denumerable (ULift α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The lift of a denumerable type is denumerable.
-/
instance ulift : Denumerable (ULift α) :=
  ofEquiv _ Equiv.ulift

/-- The lift of a denumerable type is denumerable. -/
/-
**Denumerable.plift** 是 Mathlib 中的一个实例，位于命名空间 `Denumerable`。
形式化陈述：plift : Denumerable (PLift α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The lift of a denumerable type is denumerable.
-/
instance plift : Denumerable (PLift α) :=
  ofEquiv _ Equiv.plift

/-- If `α` is denumerable, then `α × α` and `α` are equivalent. -/
/-
**Denumerable.pair** 是 Mathlib 中的一个定义，位于命名空间 `Denumerable`。
形式化陈述：pair : α × α ≃ α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `α` is denumerable, then `α × α` and `α` are equivalent.
-/
def pair : α × α ≃ α :=
  equiv₂ _ _

end

end Denumerable

namespace Nat.Subtype

open Function Encodable

/-! ### Subsets of `ℕ` -/

variable {s : Set ℕ} [Infinite s]

section Classical

/-
**Nat.Subtype.exists_succ** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Subtype`。
形式化陈述：exists_succ (x : s) : exists n, (x : Nat) + n + 1 in s
参数：x : s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.add_right_comm`：∀ (n m k : ℕ), n + m + k = n + k + m
· 使用定理 `Nat.add_sub_cancel'`：∀ {n m : ℕ}, m ≤ n → m + (n - m) = n
· 使用定理 `Fintype.false`：∀ {α : Type u_1} [Infinite α] (_h : Fintype α), False
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
theorem exists_succ (x : s) : ∃ n, (x : ℕ) + n + 1 ∈ s := by
  by_contra h
  have (a : ℕ) (ha : a ∈ s) : a < x + 1 :=
    lt_of_not_ge fun hax => h ⟨a - (x + 1), by rwa [Nat.add_right_comm, Nat.add_sub_cancel' hax]⟩
  classical
  exact Fintype.false
    ⟨(((Multiset.range (succ x)).filter (· ∈ s)).pmap
      (fun (y : ℕ) (hy : y ∈ s) => Subtype.mk y hy) (by simp [-Multiset.range_succ])).toFinset,
      by simpa [Subtype.ext_iff, Multiset.mem_filter, -Multiset.range_succ] ⟩

end Classical

variable [DecidablePred (· ∈ s)]

/-- Returns the next natural in a set, according to the usual ordering of `ℕ`. -/
/-
**Nat.Subtype.succ** 是 Mathlib 中的一个定义，位于命名空间 `Nat.Subtype`。
形式化陈述：succ (x : s) : s
参数：x : s。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Subtype.exists_succ`：exists_succ (x : s) : exists n, (x : Nat) + n +
 1 in s

--- 原说明 ---
Returns the next natural in a set, according to the usual ordering of `ℕ`.
-/
def succ (x : s) : s :=
  have h : ∃ m, (x : ℕ) + m + 1 ∈ s := exists_succ x
  ⟨↑x + Nat.find h + 1, Nat.find_spec h⟩
/-
**Nat.Subtype.succ_le_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Subtype`。
形式化陈述：succ_le_of_lt {x y : s} (h : y < x) : succ y <= x
参数：h : y < x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Subtype.exists_succ`：exists_succ (x : s) : exists n, (x : Nat) + n +
 1 in s
· 使用定理 `Nat.exists_eq_add_of_lt`：∀ {m n : ℕ}, m < n → ∃ k, n = m + k + 1
· 使用定理 `Nat.find_min'`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n) 
{m : ℕ}, p m → Nat.find H ≤ m
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem succ_le_of_lt {x y : s} (h : y < x) : succ y ≤ x :=
  have hx : ∃ m, (y : ℕ) + m + 1 ∈ s := exists_succ _
  let ⟨k, hk⟩ := Nat.exists_eq_add_of_lt h
  have : Nat.find hx ≤ k := Nat.find_min' _ (hk ▸ x.2)
  show (y : ℕ) + Nat.find hx + 1 ≤ x by lia
/-
**Nat.Subtype.le_succ_of_forall_lt_le** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Subtype`。
形式化陈述：le_succ_of_forall_lt_le {x y : s} (h : forall z < x, z <= y) : x <= succ y
参数：h : forall z < x, z <= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Subtype.exists_succ`：exists_succ (x : s) : exists n, (x : Nat) + n +
 1 in s
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `Nat.find_spec`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n),
 p (Nat.find H)
-/
theorem le_succ_of_forall_lt_le {x y : s} (h : ∀ z < x, z ≤ y) : x ≤ succ y :=
  have hx : ∃ m, (y : ℕ) + m + 1 ∈ s := exists_succ _
  show (x : ℕ) ≤ (y : ℕ) + Nat.find hx + 1 from
    le_of_not_gt fun hxy =>
      (h ⟨_, Nat.find_spec hx⟩ hxy).not_gt <|
        (by lia : (y : ℕ) < (y : ℕ) + Nat.find hx + 1)
/-
**Nat.Subtype.lt_succ_self** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Subtype`。
形式化陈述：lt_succ_self (x : s) : x < succ x
参数：x : s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Subtype.exists_succ`：exists_succ (x : s) : exists n, (x : Nat) + n +
 1 in s
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
-/
theorem lt_succ_self (x : s) : x < succ x :=
  calc
    (x : ℕ) ≤ (x + _) := le_add_right ..
    _ < (succ x) := Nat.lt_succ_self (x + _)
/-
**Nat.Subtype.lt_succ_iff_le** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Subtype`。
形式化陈述：lt_succ_iff_le {x y : s} : x < succ y ↔ x <= y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Nat.Subtype.succ_le_of_lt`：succ_le_of_lt {x y : s} (h : y < x) : succ y 
<= x
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Nat.Subtype.lt_succ_self`：lt_succ_self (x : s) : x < succ x
-/
theorem lt_succ_iff_le {x y : s} : x < succ y ↔ x ≤ y :=
  ⟨fun h => le_of_not_gt fun h' => not_le_of_gt h (succ_le_of_lt h'), fun h =>
    lt_of_le_of_lt h (lt_succ_self _)⟩

/-- Returns the `n`-th element of a set, according to the usual ordering of `ℕ`. -/
/-
**Nat.Subtype.ofNat** 是 Mathlib 中的一个定义，位于命名空间 `Nat.Subtype`。
形式化陈述：(s : Set ℕ) → [DecidablePred fun x => x ∈ s] → [Infinite ↑s] → ℕ → ↑s
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Returns the `n`-th element of a set, according to the usual ordering of `ℕ`.
-/
def ofNat (s : Set ℕ) [DecidablePred (· ∈ s)] [Infinite s] : ℕ → s
  | 0 => ⊥
  | n + 1 => succ (ofNat s n)
/-
**Nat.Subtype.ofNat_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Subtype`。
形式化陈述：ofNat_surjective : Surjective (ofNat s) | ⟨x, hx⟩ => by set t : List s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `decide_eq_true_eq`：∀ {p : Prop} [inst : Decidable p], (decide p = true) 
= p
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.mem_filter`：∀ {α : Type u_1} {p : α → Bool} {as : List α} {x : α}, 
x ∈ List.filter p as ↔ x ∈ as ∧ p x = true
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `Infinite.instNontrivial`：∀ (α : Type u_4) [Infinite α], Nontrivial α
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `List.not_mem_nil`：∀ {α : Type u_1} {a : α}, a ∉ []
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.maximum_eq_bot`：maximum_eq_bot {l : List α} : l.maximum = ⊥ ↔ l = [
]
· 使用定理 `List.maximum_mem`：maximum_mem {l : List α} {m : α} : (maximum l : WithTo
p α) = m -> m in l
· 使用定理 `Nat.Subtype.succ_le_of_lt`：succ_le_of_lt {x y : s} (h : y < x) : succ y 
<= x
· 使用定理 `Nat.Subtype.le_succ_of_forall_lt_le`：le_succ_of_forall_lt_le {x y : s} (
h : forall z < x, z <= y) : x <= succ y
· 使用定理 `List.le_maximum_of_mem`：le_maximum_of_mem : a in l -> (maximum l : WithB
ot α) = m -> a <= m
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem ofNat_surjective : Surjective (ofNat s)
  | ⟨x, hx⟩ => by
    set t : List s :=
      ((List.range x).filter fun y => y ∈ s).pmap
        (fun (y : ℕ) (hy : y ∈ s) => ⟨y, hy⟩)
        (by intro a ha; simpa using! (List.mem_filter.mp ha).2) with ht
    have hmt : ∀ {y : s}, y ∈ t ↔ y < ⟨x, hx⟩ := by
      simp [List.mem_filter, Subtype.ext_iff, ht]
    cases hmax : List.maximum t with
    | bot =>
      refine ⟨0, le_antisymm bot_le (le_of_not_gt fun h => List.not_mem_nil (a := (⊥ : s)) ?_)⟩
      rwa [← List.maximum_eq_bot.1 hmax, hmt]
    | coe m =>
      have wf : ↑m < x := by simpa using! hmt.mp (List.maximum_mem hmax)
      rcases ofNat_surjective m with ⟨a, rfl⟩
      refine ⟨a + 1, le_antisymm (succ_le_of_lt wf) ?_⟩
      exact le_succ_of_forall_lt_le fun z hz => List.le_maximum_of_mem (hmt.2 hz) hmax
  termination_by n => n.val

@[simp]
/-
**Nat.Subtype.ofNat_range** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Subtype`。
形式化陈述：ofNat_range : Set.range (ofNat s) = Set.univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.range_eq`：∀ {α : Type u_1} {ι : Sort u_4} {f : ι → α
}, Function.Surjective f → Set.range f = Set.univ
· 使用定理 `Nat.Subtype.ofNat_surjective`：ofNat_surjective : Surjective (ofNat s) | 
⟨x, hx⟩ => by set t : List s
-/
theorem ofNat_range : Set.range (ofNat s) = Set.univ :=
  ofNat_surjective.range_eq

@[simp]
/-
**Nat.Subtype.coe_comp_ofNat_range** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Subtype`。
形式化陈述：coe_comp_ofNat_range : Set.range ((↑) ∘ ofNat s : Nat -> Nat) = s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `Nat.Subtype.ofNat_range`：ofNat_range : Set.range (ofNat s) = Set.univ
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s
-/
theorem coe_comp_ofNat_range : Set.range ((↑) ∘ ofNat s : ℕ → ℕ) = s := by
  rw [Set.range_comp Subtype.val, ofNat_range, Set.image_univ, Subtype.range_coe]

set_option backward.privateInPublic true in
/-
**Nat.Subtype.toFunAux** 是 Mathlib 中的一个定义，位于命名空间 `Nat.Subtype`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def toFunAux (x : s) : ℕ :=
  (List.range x).countP (· ∈ s)
/-
**Nat.Subtype.toFunAux_eq** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Subtype`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem toFunAux_eq {s : Set ℕ} [DecidablePred (· ∈ s)] (x : s) :
    toFunAux x = #{y ∈ Finset.range x | y ∈ s} := by
  rw [toFunAux, List.countP_eq_length_filter]
  rfl

set_option backward.privateInPublic true in
/-
**Nat.Subtype.right_inverse_aux** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Subtype`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem right_inverse_aux : ∀ n, toFunAux (ofNat s n) = n
  | 0 => by
    rw [toFunAux_eq, card_eq_zero, eq_empty_iff_forall_notMem]
    rintro n hn
    rw [mem_filter, ofNat, mem_range] at hn
    exact bot_le.not_gt (show (⟨n, hn.2⟩ : s) < ⊥ from hn.1)
  | n + 1 => by
    have ih : toFunAux (ofNat s n) = n := right_inverse_aux n
    have h₁ : (ofNat s n : ℕ) ∉ {x ∈ range (ofNat s n) | x ∈ s} := by simp
    have h₂ : {x ∈ range (succ (ofNat s n)) | x ∈ s} =
        insert ↑(ofNat s n) {x ∈ range (ofNat s n) | x ∈ s} := by
      simp only [Finset.ext_iff, mem_insert, mem_range, mem_filter]
      exact fun m =>
        ⟨fun h => by
          simp only [h.2, and_true]
          exact Or.symm (lt_or_eq_of_le ((@lt_succ_iff_le _ _ _ ⟨m, h.2⟩ _).1 h.1)),
         fun h =>
          h.elim (fun h => h.symm ▸ ⟨lt_succ_self _, (ofNat s n).prop⟩) fun h =>
            ⟨h.1.trans (lt_succ_self _), h.2⟩⟩
    simp only [toFunAux_eq, ofNat] at ih ⊢
    conv =>
      rhs
      rw [← ih, ← card_insert_of_notMem h₁, ← h₂]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Any infinite set of naturals is denumerable. -/
@[instance_reducible]
/-
**Nat.Subtype.denumerable** 是 Mathlib 中的一个定义，位于命名空间 `Nat.Subtype`。
形式化陈述：denumerable (s : Set Nat) [DecidablePred (· in s)] [Infinite s] : Denumera
ble s
参数：s : Set Nat；· in s。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Logic.Denumerable.0.Nat.Subtype.right_inverse_aux`：∀ {s
 : Set ℕ} [inst : Infinite ↑s] [inst_1 : DecidablePred fun x => x ∈ s] (n : ℕ), 
  Nat.Subtype.toFunAux✝ (Nat.Subtype.ofNat s n) = n

--- 原说明 ---
Any infinite set of naturals is denumerable.
-/
def denumerable (s : Set ℕ) [DecidablePred (· ∈ s)] [Infinite s] : Denumerable s :=
  Denumerable.ofEquiv ℕ
    { toFun := toFunAux
      invFun := ofNat s
      left_inv := leftInverse_of_surjective_of_rightInverse ofNat_surjective right_inverse_aux
      right_inv := right_inverse_aux }

end Nat.Subtype

namespace Denumerable

open Encodable

/-- An infinite encodable type is denumerable. -/
@[instance_reducible]
/-
**Denumerable.ofEncodableOfInfinite** 是 Mathlib 中的一个定义，位于命名空间 `Denumerable`。
形式化陈述：ofEncodableOfInfinite (α : Type*) [Encodable α] [Infinite α] : Denumerable
 α
参数：α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An infinite encodable type is denumerable.
-/
def ofEncodableOfInfinite (α : Type*) [Encodable α] [Infinite α] : Denumerable α := by
  letI := @decidableRangeEncode α _
  letI : Infinite (Set.range (@encode α _)) :=
    Infinite.of_injective _ (Equiv.ofInjective _ encode_injective).injective
  letI := Nat.Subtype.denumerable (Set.range (@encode α _))
  exact Denumerable.ofEquiv (Set.range (@encode α _)) (equivRangeEncode α)

end Denumerable

/-- See also `nonempty_encodable`, `nonempty_fintype`. -/
/-
**nonempty_denumerable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nonempty_denumerable (α : Type*) [Countable α] [Infinite α] : Nonempty (De
numerable α)
参数：α : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
· 使用定理 `nonempty_encodable`：nonempty_encodable (α : Type*) [Countable α] : Nonem
pty (Encodable α)

--- 原说明 ---
See also `nonempty_encodable`, `nonempty_fintype`.
-/
theorem nonempty_denumerable (α : Type*) [Countable α] [Infinite α] : Nonempty (Denumerable α) :=
  (nonempty_encodable α).map fun h => @Denumerable.ofEncodableOfInfinite _ h _
/-
**nonempty_denumerable_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nonempty_denumerable_iff {α : Type*} : Nonempty (Denumerable α) ↔ Countabl
e α ∧ Infinite α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Encodable.countable`：∀ {α : Type u_1} [Encodable α], Countable α
· 使用定理 `Denumerable.instInfinite`：∀ {α : Type u_1} [Denumerable α], Infinite α
· 使用定理 `nonempty_denumerable`：nonempty_denumerable (α : Type*) [Countable α] [In
finite α] : Nonempty (Denumerable α)
-/
theorem nonempty_denumerable_iff {α : Type*} :
    Nonempty (Denumerable α) ↔ Countable α ∧ Infinite α :=
  ⟨fun ⟨_⟩ ↦ ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ ↦ nonempty_denumerable _⟩
/-
**nonempty_equiv_of_countable** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：nonempty_equiv_of_countable [Countable α] [Infinite α] [Countable β] [Infi
nite β] : Nonempty (α ≃ β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_denumerable`：nonempty_denumerable (α : Type*) [Countable α] [In
finite α] : Nonempty (Denumerable α)
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
instance nonempty_equiv_of_countable [Countable α] [Infinite α] [Countable β] [Infinite β] :
    Nonempty (α ≃ β) := by
  cases nonempty_denumerable α
  cases nonempty_denumerable β
  exact ⟨(Denumerable.eqv _).trans (Denumerable.eqv _).symm⟩
