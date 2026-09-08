/-
Copyright (c) 2025 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak
-/
module

public import Mathlib.Data.Fintype.Card

/-!
# Pigeonhole-like results for Fin

This adapts Pigeonhole-like results from `Mathlib.Data.Fintype.Card` to the setting where the map
has the type `f : Fin m → Fin n`.
-/

public section

namespace Fin

variable {m n : ℕ}

/--
If we have an injective map from `Fin m` to `Fin n`, then `m ≤ n`.
See also `Fintype.card_le_of_injective` for the generalisation to arbitrary finite types.
-/
/-
**Fin.le_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：le_of_injective (f : Fin m -> Fin n) (hf : f.Injective) : m <= n
参数：f : Fin m -> Fin n；hf : f.Injective。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Fintype.card_le_of_injective`：card_le_of_injective (f : α -> β) (hf : Fu
nction.Injective f) : card α <= card β

--- 原说明 ---
If we have an injective map from `Fin m` to `Fin n`, then `m ≤ n`.
See also `Fintype.card_le_of_injective` for the generalisation to arbitrary fini
te types.
-/
theorem le_of_injective (f : Fin m → Fin n) (hf : f.Injective) : m ≤ n := by
  simpa using Fintype.card_le_of_injective f hf

/--
If we have an embedding from `Fin m` to `Fin n`, then `m ≤ n`.
See also `Fintype.card_le_of_embedding` for the generalisation to arbitrary finite types.
-/
/-
**Fin.le_of_embedding** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：le_of_embedding (f : Fin m ↪ Fin n) : m <= n
参数：f : Fin m ↪ Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Fintype.card_le_of_embedding`：card_le_of_embedding (f : α ↪ β) : card α 
<= card β

--- 原说明 ---
If we have an embedding from `Fin m` to `Fin n`, then `m ≤ n`.
See also `Fintype.card_le_of_embedding` for the generalisation to arbitrary fini
te types.
-/
theorem le_of_embedding (f : Fin m ↪ Fin n) : m ≤ n := by
  simpa using Fintype.card_le_of_embedding f

/--
If we have an injective map from `Fin m` to `Fin n` whose image does not contain everything,
then `m < n`. See also `Fintype.card_lt_of_injective_of_notMem` for the generalisation to
arbitrary finite types.
-/
/-
**Fin.lt_of_injective_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：lt_of_injective_of_notMem (f : Fin m -> Fin n) (hf : f.Injective) {b : Fin
 n} (hb : b ∉ Set.range f) : m < n
参数：f : Fin m -> Fin n；hf : f.Injective；hb : b ∉ Set.range f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Fintype.card_lt_of_injective_of_notMem`：card_lt_of_injective_of_notMem (
f : α -> β) (h : Function.Injective f) {b : β} (w : b ∉ Set.range f) : card α < 
card β

--- 原说明 ---
If we have an injective map from `Fin m` to `Fin n` whose image does not contain
 everything,
then `m < n`. See also `Fintype.card_lt_of_injective_of_notMem` for the generali
sation to
arbitrary finite types.
-/
theorem lt_of_injective_of_notMem (f : Fin m → Fin n) (hf : f.Injective) {b : Fin n}
    (hb : b ∉ Set.range f) : m < n := by
  simpa using Fintype.card_lt_of_injective_of_notMem f hf hb

/--
If we have a surjective map from `Fin m` to `Fin n`, then `m ≥ n`.
See also `Fintype.card_le_of_surjective` for the generalisation to arbitrary finite types.
-/
/-
**Fin.le_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：le_of_surjective (f : Fin m -> Fin n) (hf : Function.Surjective f) : n <= 
m
参数：f : Fin m -> Fin n；hf : Function.Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Fintype.card_le_of_surjective`：card_le_of_surjective (f : α -> β) (h : F
unction.Surjective f) : card β <= card α

--- 原说明 ---
If we have a surjective map from `Fin m` to `Fin n`, then `m ≥ n`.
See also `Fintype.card_le_of_surjective` for the generalisation to arbitrary fin
ite types.
-/
theorem le_of_surjective (f : Fin m → Fin n) (hf : Function.Surjective f) : n ≤ m := by
  simpa using Fintype.card_le_of_surjective f hf

/--
Any map from `Fin m` reaches at most `m` different values.
See also `Fintype.card_range_le` for the generalisation to an arbitrary finite type.
-/
/-
**Fin.card_range_le** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：card_range_le {α : Type*} [Fintype α] [DecidableEq α] (f : Fin m -> α) : F
intype.card (Set.range f) <= m
参数：f : Fin m -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Fintype.card_ofFinset`：card_ofFinset {p : Set α} (s : Finset α) (H : for
all x, x in s ↔ x in p) : @Fintype.card p (ofFinset s H) = #s
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Finset.univ_filter_exists`：univ_filter_exists (f : α -> β) [Fintype β] [
DecidablePred fun y => exists x, f x = y] [DecidableEq β] : (Finset.univ.filter 
fun y => exists…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Fintype.card_range_le`：card_range_le {α β : Type*} (f : α -> β) [Fintype
 α] [Fintype (Set.range f)] : Fintype.card (Set.range f) <= Fintype.card α

--- 原说明 ---
Any map from `Fin m` reaches at most `m` different values.
See also `Fintype.card_range_le` for the generalisation to an arbitrary finite t
ype.
-/
theorem card_range_le {α : Type*} [Fintype α] [DecidableEq α] (f : Fin m → α) :
    Fintype.card (Set.range f) ≤ m := by
  simpa using Fintype.card_range_le f

end Fin

