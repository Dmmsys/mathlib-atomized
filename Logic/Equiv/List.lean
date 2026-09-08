/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Logic.Denumerable

/-!
# Equivalences involving `List`-like types

This file defines some additional constructive equivalences using `Encodable` and the pairing
function on `ℕ`.
-/

@[expose] public section

assert_not_exists Monoid Multiset.sort

open List
open Nat

namespace Equiv

/-- An equivalence between `α` and `β` generates an equivalence between `List α` and `List β`. -/
/-
**Equiv.listEquivOfEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：listEquivOfEquiv {α β} (e : α ≃ β) : List α ≃ List β where toFun
参数：e : α ≃ β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
An equivalence between `α` and `β` generates an equivalence between `List α` and
 `List β`.
-/
def listEquivOfEquiv {α β} (e : α ≃ β) : List α ≃ List β where
  toFun := List.map e
  invFun := List.map e.symm
  left_inv l := by rw [List.map_map, e.symm_comp_self, List.map_id]
  right_inv l := by rw [List.map_map, e.self_comp_symm, List.map_id]

end Equiv

namespace Encodable

variable {α : Type*}

section List

variable [Encodable α]

/-- Explicit encoding function for `List α` -/
/-
**Encodable.encodeList** 是 Mathlib 中的一个定义，位于命名空间 `Encodable`。
形式化陈述：{α : Type u_1} → [Encodable α] → List α → ℕ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Explicit encoding function for `List α`
-/
def encodeList : List α → ℕ
  | [] => 0
  | a :: l => succ (pair (encode a) (encodeList l))

/-- Explicit decoding function for `List α` -/
/-
**Encodable.decodeList** 是 Mathlib 中的一个定义，位于命名空间 `Encodable`。
形式化陈述：decodeList : Nat -> Option (List α) | 0 => some [] | succ v => match unpai
r v, unpair_right_le v with | (v₁, v₂), h => have : v₂ < succ v
该定义给出了一等式。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.unpair_right_le`：unpair_right_le (n : Nat) : (unpair n).2 <= n
· 使用定理 `Nat.lt_succ_of_le`：∀ {n m : ℕ}, n ≤ m → n < m.succ

--- 原说明 ---
Explicit decoding function for `List α`
-/
def decodeList : ℕ → Option (List α)
  | 0 => some []
  | succ v =>
    match unpair v, unpair_right_le v with
    | (v₁, v₂), h =>
      have : v₂ < succ v := lt_succ_of_le h
      (· :: ·) <$> decode (α := α) v₁ <*> decodeList v₂

@[simp]
/-
**Encodable.decodeList_encodeList_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Encodable`。
形式化陈述：decodeList_encodeList_eq_self (l : List α) : decodeList (encodeList l) = s
ome l
参数：l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Encodable.decodeList.eq_1`：∀ {α : Type u_1} [inst : Encodable α], Encoda
ble.decodeList 0 = some []
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.unpair_right_le`：unpair_right_le (n : Nat) : (unpair n).2 <= n
· 使用定理 `Nat.lt_succ_of_le`：∀ {n m : ℕ}, n ≤ m → n < m.succ
· 使用定理 `Encodable.decodeList.eq_2`：∀ {α : Type u_1} [inst : Encodable α] (v : ℕ)
,   Encodable.decodeList v.succ =     match Nat.unpair v, ⋯ with     | (v₁, v₂),
 h =>       hav…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.unpair_pair`：unpair_pair (a b : Nat) : unpair (pair a b) = (a, b)
· 使用定理 `Encodable.encodek`：∀ {α : Type u_1} [self : Encodable α] (a : α), Encoda
ble.decode (Encodable.encode a) = some a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem decodeList_encodeList_eq_self (l : List α) : decodeList (encodeList l) = some l := by
  induction l <;> simp [encodeList, decodeList, unpair_pair, encodek, *]

/-- If `α` is encodable, then so is `List α`. This uses the `pair` and `unpair` functions from
`Data.Nat.Pairing`. -/
/-
**Encodable._root_.List.encodable** 是 Mathlib 中的一个实例，位于命名空间 `Encodable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `α` is encodable, then so is `List α`. This uses the `pair` and `unpair` func
tions from
`Data.Nat.Pairing`.
-/
instance _root_.List.encodable : Encodable (List α) :=
  ⟨encodeList, decodeList, decodeList_encodeList_eq_self⟩
/-
**Encodable._root_.List.countable** 是 Mathlib 中的一个实例，位于命名空间 `Encodable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.List.countable {α : Type*} [Countable α] : Countable (List α) := by
  have := Encodable.ofCountable α
  infer_instance

@[simp]
/-
**Encodable.encode_list_nil** 是 Mathlib 中的一个定理，位于命名空间 `Encodable`。
形式化陈述：encode_list_nil : encode (@nil α) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem encode_list_nil : encode (@nil α) = 0 :=
  rfl

@[simp]
/-
**Encodable.encode_list_cons** 是 Mathlib 中的一个定理，位于命名空间 `Encodable`。
形式化陈述：encode_list_cons (a : α) (l : List α) : encode (a :: l) = succ (pair (enco
de a) (encode l))
参数：a : α；l : List α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem encode_list_cons (a : α) (l : List α) :
    encode (a :: l) = succ (pair (encode a) (encode l)) :=
  rfl

@[simp]
/-
**Encodable.decode_list_zero** 是 Mathlib 中的一个定理，位于命名空间 `Encodable`。
形式化陈述：decode_list_zero : decode (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Encodable.decodeList.eq_1`：∀ {α : Type u_1} [inst : Encodable α], Encoda
ble.decodeList 0 = some []
-/
theorem decode_list_zero : decode (α := List α) 0 = some [] :=
  show decodeList 0 = some [] by rw [decodeList]

@[simp]
/-
**Encodable.decode_list_succ** 是 Mathlib 中的一个定理，位于命名空间 `Encodable`。
形式化陈述：decode_list_succ (v : Nat) : decode (α
参数：v : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.unpair_right_le`：unpair_right_le (n : Nat) : (unpair n).2 <= n
· 使用定理 `Nat.lt_succ_of_le`：∀ {n m : ℕ}, n ≤ m → n < m.succ
· 使用定理 `Encodable.decodeList.eq_2`：∀ {α : Type u_1} [inst : Encodable α] (v : ℕ)
,   Encodable.decodeList v.succ =     match Nat.unpair v, ⋯ with     | (v₁, v₂),
 h =>       hav…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem decode_list_succ (v : ℕ) :
    decode (α := List α) (succ v) =
      (· :: ·) <$> decode (α := α) v.unpair.1 <*> decode (α := List α) v.unpair.2 :=
  show decodeList (succ v) = _ by
    rcases e : unpair v with ⟨v₁, v₂⟩
    simp [decodeList, e]; rfl
/-
**Encodable.length_le_encode** 是 Mathlib 中的一个定理，位于命名空间 `Encodable`。
形式化陈述：∀ {α : Type u_1} [inst : Encodable α] (l : List α), l.length ≤ Encodable.e
ncode l
参数：l : List α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem length_le_encode : ∀ l : List α, length l ≤ encode l
  | [] => Nat.zero_le _
  | _ :: l => succ_le_succ <| (length_le_encode l).trans (right_le_pair _ _)

end List

/-! These two lemmas are not about lists, but are convenient to keep here and don't
require `Finset.sort`. -/

/-- If `α` is countable, then so is `Multiset α`. -/
/-
**Encodable._root_.Multiset.countable** 是 Mathlib 中的一个实例，位于命名空间 `Encodable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `α` is countable, then so is `Multiset α`.
-/
instance _root_.Multiset.countable [Countable α] : Countable (Multiset α) :=
  Quotient.countable

/-- If `α` is countable, then so is `Finset α`. -/
/-
**Encodable._root_.Finset.countable** 是 Mathlib 中的一个实例，位于命名空间 `Encodable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `α` is countable, then so is `Finset α`.
-/
instance _root_.Finset.countable [Countable α] : Countable (Finset α) :=
  Finset.val_injective.countable

/-- A listable type with decidable equality is encodable. -/
@[instance_reducible]
/-
**Encodable.encodableOfList** 是 Mathlib 中的一个定义，位于命名空间 `Encodable`。
形式化陈述：encodableOfList [DecidableEq α] (l : List α) (H : forall x, x in l) : Enco
dable α
参数：l : List α；H : forall x, x in l。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A listable type with decidable equality is encodable.
-/
def encodableOfList [DecidableEq α] (l : List α) (H : ∀ x, x ∈ l) : Encodable α :=
  ⟨fun a => idxOf a l, (l[·]?), fun _ => getElem?_idxOf (H _)⟩

/-- A finite type is encodable. Because the encoding is not unique, we wrap it in `Trunc` to
preserve computability. -/
/-
**Encodable._root_.Fintype.truncEncodable** 是 Mathlib 中的一个定义，位于命名空间 `Encodable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A finite type is encodable. Because the encoding is not unique, we wrap it in `T
runc` to
preserve computability.
-/
def _root_.Fintype.truncEncodable (α : Type*) [DecidableEq α] [Fintype α] : Trunc (Encodable α) :=
  @Quot.recOnSubsingleton _ _ (fun s : Multiset α => (∀ x : α, x ∈ s) → Trunc (Encodable α)) _
    Finset.univ.1 (fun l H => Trunc.mk <| encodableOfList l H) Finset.mem_univ

/-- A noncomputable way to arbitrarily choose an ordering on a finite type.
It is not made into a global instance, since it involves an arbitrary choice.
This can be locally made into an instance with `attribute [local instance] Fintype.toEncodable`. -/
@[instance_reducible]
/-
**Encodable._root_.Fintype.toEncodable** 是 Mathlib 中的一个定义，位于命名空间 `Encodable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A noncomputable way to arbitrarily choose an ordering on a finite type.
It is not made into a global instance, since it involves an arbitrary choice.
This can be locally made into an instance with `attribute [local instance] Finty
pe.toEncodable`.
-/
noncomputable def _root_.Fintype.toEncodable (α : Type*) [Fintype α] : Encodable α := by
  classical exact (Fintype.truncEncodable α).out

end Encodable

namespace Denumerable

variable {α : Type*} {β : Type*} [Denumerable α] [Denumerable β]

open Encodable

section List

/-
**Denumerable.denumerable_list_aux** 是 Mathlib 中的一个定理，位于命名空间 `Denumerable`。
形式化陈述：denumerable_list_aux : forall n : Nat, exists a in @decodeList α _ n, enco
deList a = n | 0 => by rw [decodeList]; exact ⟨_, rfl, rfl⟩ | succ v => by rcase
s e : unpair v with ⟨v₁, v₂⟩ have h
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Encodable.decodeList.eq_1`：∀ {α : Type u_1} [inst : Encodable α], Encoda
ble.decodeList 0 = some []
· 使用定理 `Nat.unpair_right_le`：unpair_right_le (n : Nat) : (unpair n).2 <= n
· 使用定理 `Nat.lt_succ_of_le`：∀ {n m : ℕ}, n ≤ m → n < m.succ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Encodable.decodeList.eq_2`：∀ {α : Type u_1} [inst : Encodable α] (v : ℕ)
,   Encodable.decodeList v.succ =     match Nat.unpair v, ⋯ with     | (v₁, v₂),
 h =>       hav…
· 使用定理 `Denumerable.decode_eq_ofNat`：decode_eq_ofNat (α) [Denumerable α] (n : Na
t) : decode (α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Option.mem_def`：∀ {α : Type u_1} {a : α} {b : Option α}, a ∈ b ↔ b = som
e a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Denumerable.encode_ofNat`：encode_ofNat (n) : encode (ofNat α n) = n
· 使用定理 `Nat.pair_eq_of_unpair_eq`：pair_eq_of_unpair_eq {n a b} (H : unpair n = (
a, b)) : pair a b = n
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem denumerable_list_aux : ∀ n : ℕ, ∃ a ∈ @decodeList α _ n, encodeList a = n
  | 0 => by rw [decodeList]; exact ⟨_, rfl, rfl⟩
  | succ v => by
    rcases e : unpair v with ⟨v₁, v₂⟩
    have h := unpair_right_le v
    rw [e] at h
    rcases have : v₂ < succ v := lt_succ_of_le h
      denumerable_list_aux v₂ with
      ⟨a, h₁, h₂⟩
    rw [Option.mem_def] at h₁
    use ofNat α v₁ :: a
    simp [decodeList, e, h₂, h₁, encodeList, pair_eq_of_unpair_eq e]

/-- If `α` is denumerable, then so is `List α`. -/
/-
**Denumerable.denumerableList** 是 Mathlib 中的一个实例，位于命名空间 `Denumerable`。
形式化陈述：denumerableList : Denumerable (List α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Denumerable.denumerable_list_aux`：denumerable_list_aux : forall n : Nat,
 exists a in @decodeList α _ n, encodeList a = n | 0 => by rw [decodeList]; exac
t ⟨_, rfl, rfl⟩ | succ…

--- 原说明 ---
If `α` is denumerable, then so is `List α`.
-/
instance denumerableList : Denumerable (List α) :=
  ⟨denumerable_list_aux⟩

@[simp]
/-
**Denumerable.list_ofNat_zero** 是 Mathlib 中的一个定理，位于命名空间 `Denumerable`。
形式化陈述：list_ofNat_zero : ofNat (List α) 0 = []
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Encodable.encode_list_nil`：encode_list_nil : encode (@nil α) = 0
· 使用定理 `Denumerable.ofNat_encode`：ofNat_encode (a) : ofNat α (encode a) = a
-/
theorem list_ofNat_zero : ofNat (List α) 0 = [] := by rw [← @encode_list_nil α, ofNat_encode]

@[simp]
/-
**Denumerable.list_ofNat_succ** 是 Mathlib 中的一个定理，位于命名空间 `Denumerable`。
形式化陈述：list_ofNat_succ (v : Nat) : ofNat (List α) (succ v) = ofNat α v.unpair.1 :
: ofNat (List α) v.unpair.2
参数：v : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Denumerable.ofNat_of_decode`：ofNat_of_decode {n b} (h : decode (α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.unpair_right_le`：unpair_right_le (n : Nat) : (unpair n).2 <= n
· 使用定理 `Nat.lt_succ_of_le`：∀ {n m : ℕ}, n ≤ m → n < m.succ
· 使用定理 `Encodable.decodeList.eq_2`：∀ {α : Type u_1} [inst : Encodable α] (v : ℕ)
,   Encodable.decodeList v.succ =     match Nat.unpair v, ⋯ with     | (v₁, v₂),
 h =>       hav…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Denumerable.decode_eq_ofNat`：decode_eq_ofNat (α) [Denumerable α] (n : Na
t) : decode (α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem list_ofNat_succ (v : ℕ) :
    ofNat (List α) (succ v) = ofNat α v.unpair.1 :: ofNat (List α) v.unpair.2 :=
  ofNat_of_decode <|
    show decodeList (succ v) = _ by
      rcases e : unpair v with ⟨v₁, v₂⟩
      simp [decodeList, e, show decodeList v₂ = decode (α := List α) v₂ from rfl]

end List

end Denumerable

namespace Equiv

/-- A list on a unique type is equivalent to ℕ by sending each list to its length. -/
@[simps!]
/-
**Equiv.listUniqueEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：listUniqueEquiv (α : Type*) [Unique α] : List α ≃ Nat where toFun
参数：α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A list on a unique type is equivalent to ℕ by sending each list to its length.
-/
def listUniqueEquiv (α : Type*) [Unique α] : List α ≃ ℕ where
  toFun := List.length
  invFun n := List.replicate n default
  left_inv u := List.length_injective (by simp)
  right_inv n := List.length_replicate

/-- `List ℕ` is equivalent to `ℕ`. -/
/-
**Equiv.listNatEquivNat** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：listNatEquivNat : List Nat ≃ Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`List ℕ` is equivalent to `ℕ`.
-/
def listNatEquivNat : List ℕ ≃ ℕ :=
  Denumerable.eqv _

/-- If `α` is equivalent to `ℕ`, then `List α` is equivalent to `α`. -/
/-
**Equiv.listEquivSelfOfEquivNat** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：listEquivSelfOfEquivNat {α : Type*} (e : α ≃ Nat) : List α ≃ α
参数：e : α ≃ Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If `α` is equivalent to `ℕ`, then `List α` is equivalent to `α`.
-/
def listEquivSelfOfEquivNat {α : Type*} (e : α ≃ ℕ) : List α ≃ α :=
  calc
    List α ≃ List ℕ := listEquivOfEquiv e
    _ ≃ ℕ := listNatEquivNat
    _ ≃ α := e.symm

end Equiv

