/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Data.PNat.Defs

/-!
# Finite intervals of positive naturals

This file proves that `ℕ+` is a `LocallyFiniteOrder` and calculates the cardinality of its
intervals as finsets and fintypes.
-/

public section


open Finset Function PNat

namespace PNat

variable (a b : ℕ+)

/-
**PNat.instLocallyFiniteOrder** 是 Mathlib 中的一个实例，位于命名空间 `PNat`。
形式化陈述：instLocallyFiniteOrder : LocallyFiniteOrder Nat+
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instLocallyFiniteOrder : LocallyFiniteOrder ℕ+ :=
  inferInstanceAs <| LocallyFiniteOrder (Subtype _)
/-
**PNat.Icc_eq_finset_subtype** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：Icc_eq_finset_subtype : Icc a b = (Icc (a : Nat) b).subtype fun n : Nat =>
 0 < n
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Icc_eq_finset_subtype : Icc a b = (Icc (a : ℕ) b).subtype fun n : ℕ => 0 < n :=
  rfl
/-
**PNat.Ico_eq_finset_subtype** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：Ico_eq_finset_subtype : Ico a b = (Ico (a : Nat) b).subtype fun n : Nat =>
 0 < n
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ico_eq_finset_subtype : Ico a b = (Ico (a : ℕ) b).subtype fun n : ℕ => 0 < n :=
  rfl
/-
**PNat.Ioc_eq_finset_subtype** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：Ioc_eq_finset_subtype : Ioc a b = (Ioc (a : Nat) b).subtype fun n : Nat =>
 0 < n
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ioc_eq_finset_subtype : Ioc a b = (Ioc (a : ℕ) b).subtype fun n : ℕ => 0 < n :=
  rfl
/-
**PNat.Ioo_eq_finset_subtype** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：Ioo_eq_finset_subtype : Ioo a b = (Ioo (a : Nat) b).subtype fun n : Nat =>
 0 < n
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ioo_eq_finset_subtype : Ioo a b = (Ioo (a : ℕ) b).subtype fun n : ℕ => 0 < n :=
  rfl
/-
**PNat.uIcc_eq_finset_subtype** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：uIcc_eq_finset_subtype : uIcc a b = (uIcc (a : Nat) b).subtype fun n : Nat
 => 0 < n
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem uIcc_eq_finset_subtype : uIcc a b = (uIcc (a : ℕ) b).subtype fun n : ℕ => 0 < n := rfl
/-
**PNat.map_subtype_embedding_Icc** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：map_subtype_embedding_Icc : (Icc a b).map (Embedding.subtype _) = Icc ↑a ↑
b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.map_subtype_embedding_Icc`：map_subtype_embedding_Icc (hp : forall
 ⦃a b x⦄, a <= x -> x <= b -> p a -> p b -> p x) : (Icc a b).map (Embedding.subt
ype p) = (Icc a b : Fi…
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
-/
theorem map_subtype_embedding_Icc : (Icc a b).map (Embedding.subtype _) = Icc ↑a ↑b :=
  Finset.map_subtype_embedding_Icc _ _ _ fun _c _ _x hx _ hc _ => hc.trans_le hx
/-
**PNat.map_subtype_embedding_Ico** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：map_subtype_embedding_Ico : (Ico a b).map (Embedding.subtype _) = Ico ↑a ↑
b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.map_subtype_embedding_Ico`：map_subtype_embedding_Ico (hp : forall
 ⦃a b x⦄, a <= x -> x <= b -> p a -> p b -> p x) : (Ico a b).map (Embedding.subt
ype p) = (Ico a b : Fi…
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
-/
theorem map_subtype_embedding_Ico : (Ico a b).map (Embedding.subtype _) = Ico ↑a ↑b :=
  Finset.map_subtype_embedding_Ico _ _ _ fun _c _ _x hx _ hc _ => hc.trans_le hx
/-
**PNat.map_subtype_embedding_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：map_subtype_embedding_Ioc : (Ioc a b).map (Embedding.subtype _) = Ioc ↑a ↑
b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.map_subtype_embedding_Ioc`：map_subtype_embedding_Ioc (hp : forall
 ⦃a b x⦄, a <= x -> x <= b -> p a -> p b -> p x) : (Ioc a b).map (Embedding.subt
ype p) = (Ioc a b : Fi…
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
-/
theorem map_subtype_embedding_Ioc : (Ioc a b).map (Embedding.subtype _) = Ioc ↑a ↑b :=
  Finset.map_subtype_embedding_Ioc _ _ _ fun _c _ _x hx _ hc _ => hc.trans_le hx
/-
**PNat.map_subtype_embedding_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：map_subtype_embedding_Ioo : (Ioo a b).map (Embedding.subtype _) = Ioo ↑a ↑
b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.map_subtype_embedding_Ioo`：map_subtype_embedding_Ioo (hp : forall
 ⦃a b x⦄, a <= x -> x <= b -> p a -> p b -> p x) : (Ioo a b).map (Embedding.subt
ype p) = (Ioo a b : Fi…
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
-/
theorem map_subtype_embedding_Ioo : (Ioo a b).map (Embedding.subtype _) = Ioo ↑a ↑b :=
  Finset.map_subtype_embedding_Ioo _ _ _ fun _c _ _x hx _ hc _ => hc.trans_le hx
/-
**PNat.map_subtype_embedding_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：map_subtype_embedding_uIcc : (uIcc a b).map (Embedding.subtype _) = uIcc ↑
a ↑b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PNat.map_subtype_embedding_Icc`：map_subtype_embedding_Icc : (Icc a b).ma
p (Embedding.subtype _) = Icc ↑a ↑b
-/
theorem map_subtype_embedding_uIcc : (uIcc a b).map (Embedding.subtype _) = uIcc ↑a ↑b :=
  map_subtype_embedding_Icc _ _

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**PNat.card_Icc** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：card_Icc : #(Icc a b) = b + 1 - a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.card_Icc`：∀ (a b : ℕ), (Finset.Icc a b).card = b + 1 - a
· 使用定理 `PNat.map_subtype_embedding_Icc`：map_subtype_embedding_Icc : (Icc a b).ma
p (Embedding.subtype _) = Icc ↑a ↑b
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
-/
theorem card_Icc : #(Icc a b) = b + 1 - a := by
  rw [← Nat.card_Icc, ← map_subtype_embedding_Icc, card_map]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**PNat.card_Ico** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：card_Ico : #(Ico a b) = b - a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.card_Ico`：∀ (a b : ℕ), (Finset.Ico a b).card = b - a
· 使用定理 `PNat.map_subtype_embedding_Ico`：map_subtype_embedding_Ico : (Ico a b).ma
p (Embedding.subtype _) = Ico ↑a ↑b
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
-/
theorem card_Ico : #(Ico a b) = b - a := by
  rw [← Nat.card_Ico, ← map_subtype_embedding_Ico, card_map]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**PNat.card_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：card_Ioc : #(Ioc a b) = b - a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.card_Ioc`：∀ (a b : ℕ), (Finset.Ioc a b).card = b - a
· 使用定理 `PNat.map_subtype_embedding_Ioc`：map_subtype_embedding_Ioc : (Ioc a b).ma
p (Embedding.subtype _) = Ioc ↑a ↑b
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
-/
theorem card_Ioc : #(Ioc a b) = b - a := by
  rw [← Nat.card_Ioc, ← map_subtype_embedding_Ioc, card_map]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**PNat.card_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：card_Ioo : #(Ioo a b) = b - a - 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.card_Ioo`：∀ (a b : ℕ), (Finset.Ioo a b).card = b - a - 1
· 使用定理 `PNat.map_subtype_embedding_Ioo`：map_subtype_embedding_Ioo : (Ioo a b).ma
p (Embedding.subtype _) = Ioo ↑a ↑b
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
-/
theorem card_Ioo : #(Ioo a b) = b - a - 1 := by
  rw [← Nat.card_Ioo, ← map_subtype_embedding_Ioo, card_map]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**PNat.card_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：card_uIcc : #(uIcc a b) = (b - a : Int).natAbs + 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.card_uIcc`：card_uIcc : #(uIcc a b) = (b - a : Int).natAbs + 1
· 使用定理 `PNat.map_subtype_embedding_uIcc`：map_subtype_embedding_uIcc : (uIcc a b)
.map (Embedding.subtype _) = uIcc ↑a ↑b
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
-/
theorem card_uIcc : #(uIcc a b) = (b - a : ℤ).natAbs + 1 := by
  rw [← Nat.card_uIcc, ← map_subtype_embedding_uIcc, card_map]

set_option backward.isDefEq.respectTransparency false in
/-
**PNat.card_fintype_Icc** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：card_fintype_Icc : Fintype.card (Set.Icc a b) = b + 1 - a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PNat.card_Icc`：card_Icc : #(Icc a b) = b + 1 - a
· 使用定理 `Fintype.card_ofFinset`：card_ofFinset {p : Set α} (s : Finset α) (H : for
all x, x in s ↔ x in p) : @Fintype.card p (ofFinset s H) = #s
-/
theorem card_fintype_Icc : Fintype.card (Set.Icc a b) = b + 1 - a := by
  rw [← card_Icc, Fintype.card_ofFinset]

set_option backward.isDefEq.respectTransparency false in
/-
**PNat.card_fintype_Ico** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：card_fintype_Ico : Fintype.card (Set.Ico a b) = b - a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PNat.card_Ico`：card_Ico : #(Ico a b) = b - a
· 使用定理 `Fintype.card_ofFinset`：card_ofFinset {p : Set α} (s : Finset α) (H : for
all x, x in s ↔ x in p) : @Fintype.card p (ofFinset s H) = #s
-/
theorem card_fintype_Ico : Fintype.card (Set.Ico a b) = b - a := by
  rw [← card_Ico, Fintype.card_ofFinset]

set_option backward.isDefEq.respectTransparency false in
/-
**PNat.card_fintype_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：card_fintype_Ioc : Fintype.card (Set.Ioc a b) = b - a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PNat.card_Ioc`：card_Ioc : #(Ioc a b) = b - a
· 使用定理 `Fintype.card_ofFinset`：card_ofFinset {p : Set α} (s : Finset α) (H : for
all x, x in s ↔ x in p) : @Fintype.card p (ofFinset s H) = #s
-/
theorem card_fintype_Ioc : Fintype.card (Set.Ioc a b) = b - a := by
  rw [← card_Ioc, Fintype.card_ofFinset]

set_option backward.isDefEq.respectTransparency false in
/-
**PNat.card_fintype_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：card_fintype_Ioo : Fintype.card (Set.Ioo a b) = b - a - 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PNat.card_Ioo`：card_Ioo : #(Ioo a b) = b - a - 1
· 使用定理 `Fintype.card_ofFinset`：card_ofFinset {p : Set α} (s : Finset α) (H : for
all x, x in s ↔ x in p) : @Fintype.card p (ofFinset s H) = #s
-/
theorem card_fintype_Ioo : Fintype.card (Set.Ioo a b) = b - a - 1 := by
  rw [← card_Ioo, Fintype.card_ofFinset]

set_option backward.isDefEq.respectTransparency false in
/-
**PNat.card_fintype_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：card_fintype_uIcc : Fintype.card (Set.uIcc a b) = (b - a : Int).natAbs + 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PNat.card_uIcc`：card_uIcc : #(uIcc a b) = (b - a : Int).natAbs + 1
· 使用定理 `Finset.mem_uIcc`：mem_uIcc : x in uIcc a b ↔ a ⊓ b <= x ∧ x <= a ⊔ b
· 使用定理 `Fintype.card_ofFinset`：card_ofFinset {p : Set α} (s : Finset α) (H : for
all x, x in s ↔ x in p) : @Fintype.card p (ofFinset s H) = #s
-/
theorem card_fintype_uIcc : Fintype.card (Set.uIcc a b) = (b - a : ℤ).natAbs + 1 := by
  rw [← card_uIcc, Fintype.card_ofFinset]

end PNat

