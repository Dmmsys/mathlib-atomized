/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Data.Vector.Basic

/-!
# The structure of `Fintype (Fin n)`

This file contains some basic results about the `Fintype` instance for `Fin`,
especially properties of `Finset.univ : Finset (Fin n)`.
-/

public section

open List (Vector)

open Finset

open Fintype

namespace Fin

variable {α β : Type*} {n : ℕ}

/-
**Fin.map_valEmbedding_univ** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n : ℕ}, Finset.map Fin.valEmbedding Finset.univ = Finset.Iio n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Fin.valEmbedding_apply`：∀ {n : ℕ}, ⇑Fin.valEmbedding = Fin.val
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Function.Surjective.exists`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Surjective f → ∀ {p : β → Prop}, (∃ y, p y) ↔ ∃ x, p (f x)
· 使用定理 `OrderIso.surjective`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α] [inst
_1 : LE β] (e : α ≃o β), Function.Surjective ⇑e
· 使用定理 `Fin.orderIsoSubtype_symm_apply`：∀ {n : ℕ} (a : { i // i < n }), (RelIso.
symm Fin.orderIsoSubtype) a = ⟨↑a, ⋯⟩
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] theorem map_valEmbedding_univ :
    (Finset.univ : Finset (Fin n)).map Fin.valEmbedding = Iio n := by
  ext
  simp [orderIsoSubtype.symm.surjective.exists, OrderIso.symm]

@[simp]
/-
**Fin.Ioi_zero_eq_map** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：Ioi_zero_eq_map : Ioi (0 : Fin n.succ) = univ.map (Fin.succEmb _)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_Ioi`：coe_Ioi (a : α) : (Ioi a : Set α) = Set.Ioi a
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Fin.range_succ`：∀ (n : ℕ), Set.range Fin.succ = {0}ᶜ
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Ioi_zero_eq_map : Ioi (0 : Fin n.succ) = univ.map (Fin.succEmb _) :=
  coe_injective <| by ext; simp [pos_iff_ne_zero]

@[simp]
/-
**Fin.Iio_last_eq_map** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：Iio_last_eq_map : Iio (Fin.last n) = Finset.univ.map Fin.castSuccEmb
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_Iio`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] (a : α), ↑(Finset.Iio a) = Set.Iio a
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Fin.range_castSucc`：range_castSucc {n : Nat} : Set.range (castSucc : Fin
 n -> Fin n.succ) = ({ i | (i : Nat) < n } : Set (Fin n.succ))
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Iio_last_eq_map : Iio (Fin.last n) = Finset.univ.map Fin.castSuccEmb :=
  coe_injective <| by ext; simp [lt_def]
/-
**Fin.Ioi_succ** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：Ioi_succ (i : Fin n) : Ioi i.succ = (Ioi i).map (Fin.succEmb _)
参数：i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.map_succEmb_Ioi`：map_succEmb_Ioi (i : Fin n) : (Ioi i).map (succEmb 
n) = Ioi i.succ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Ioi_succ (i : Fin n) : Ioi i.succ = (Ioi i).map (Fin.succEmb _) := by simp
/-
**Fin.Iio_castSucc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：Iio_castSucc (i : Fin n) : Iio (castSucc i) = (Iio i).map Fin.castSuccEmb
参数：i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.map_castSuccEmb_Iio`：map_castSuccEmb_Iio (i : Fin n) : (Iio i).map c
astSuccEmb = Iio i.castSucc
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Iio_castSucc (i : Fin n) : Iio (castSucc i) = (Iio i).map Fin.castSuccEmb := by simp
/-
**Fin.card_filter_val_lt** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：card_filter_val_lt {m : Nat} : #{i : Fin n | i < m} = min n m
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用引理 `Finset.map_filter'`：map_filter' (p : α -> Prop) [DecidablePred p] (f : α
 ↪ β) (s : Finset α) [DecidablePred (exists a, p a ∧ f a = ·)] : (s.filter p).ma
p f = (s…
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Fin.valEmbedding_apply`：∀ {n : ℕ}, ⇑Fin.valEmbedding = Fin.val
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Finset.filter.congr_simp`：∀ {α : Type u_1} (p p_1 : α → Prop),   p = p_1
 →     ∀ {inst : DecidablePred p} [inst_1 : DecidablePred p_1] (s s_1 : Finset α
),       s = s…
· 使用定理 `Fin.map_valEmbedding_univ`：∀ {n : ℕ}, Finset.map Fin.valEmbedding Finset
.univ = Finset.Iio n
· 使用定理 `Finset.Iio_filter_lt`：Iio_filter_lt {α} [LinearOrder α] [LocallyFiniteOr
derBot α] (a b : α) : {x in Iio a | x < b} = Iio (min a b)
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `Nat.card_Iio`：card_Iio : #(Iio b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem card_filter_val_lt {m : ℕ} : #{i : Fin n | i < m} = min n m := by
  simp [← card_map valEmbedding, ← filter_filter, exists_iff, map_filter']
/-
**Fin.card_filter_univ_succ** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：card_filter_univ_succ (p : Fin (n + 1) -> Prop) [DecidablePred p] : #{x | 
p x} = if p 0 then #{x | p (.succ x)} + 1 else #{x | p (.succ x)}
参数：p : Fin (n + 1) -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Fin.succ_injective`：succ_injective (n : Nat) : Injective (@Fin.succ n)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.univ_succ`：Fin.univ_succ (n : Nat) : (univ : Finset (Fin (n + 1))) =
 Finset.cons 0 (univ.map ⟨Fin.succ, Fin.succ_injective _⟩) (by simp [map_eq_imag
e])
· 使用定理 `Function.mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Finset.mem_of_mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : Decida
blePred p] {s : Finset α}, ∀ x ∈ Finset.filter p s, x ∈ s
· 使用定理 `Finset.filter_cons`：filter_cons {a : α} (s : Finset α) (ha : a ∉ s) : (s
.cons a ha).filter p = if p a then (s.filter p).cons a ((mem_of_mem_filter _).mt
 ha) els…
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `Finset.card_cons`：card_cons (h : a ∉ s) : #(s.cons a h) = #s + 1
· 使用定理 `Finset.filter_map`：filter_map {p : β -> Prop} [DecidablePred p] : (s.map
 f).filter p = (s.filter (p ∘ f)).map f
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
-/
theorem card_filter_univ_succ (p : Fin (n + 1) → Prop) [DecidablePred p] :
    #{x | p x} = if p 0 then #{x | p (.succ x)} + 1 else #{x | p (.succ x)} := by
  rw [Fin.univ_succ, filter_cons, apply_ite Finset.card, card_cons, filter_map, card_map]; rfl
/-
**Fin.card_filter_univ_succ'** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：card_filter_univ_succ' (p : Fin (n + 1) -> Prop) [DecidablePred p] : #{x |
 p x} = ite (p 0) 1 0 + #{x | p (.succ x)}
参数：p : Fin (n + 1) -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.card_filter_univ_succ`：card_filter_univ_succ (p : Fin (n + 1) -> Pro
p) [DecidablePred p] : #{x | p x} = if p 0 then #{x | p (.succ x)} + 1 else #{x 
| p (.succ x)}
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem card_filter_univ_succ' (p : Fin (n + 1) → Prop) [DecidablePred p] :
    #{x | p x} = ite (p 0) 1 0 + #{x | p (.succ x)} := by
  rw [card_filter_univ_succ]; split_ifs <;> simp [add_comm]
/-
**Fin.card_filter_univ_eq_vector_get_eq_count** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：card_filter_univ_eq_vector_get_eq_count [DecidableEq α] (a : α) (v : List.
Vector α n) : #{i | v.get i = a} = v.toList.count a
参数：a : α；v : List.Vector α n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.filter.congr_simp`：∀ {α : Type u_1} (p p_1 : α → Prop),   p = p_1
 →     ∀ {inst : DecidablePred p} [inst_1 : DecidablePred p_1] (s s_1 : Finset α
),       s = s…
· 使用定理 `Finset.univ_eq_empty`：univ_eq_empty [IsEmpty α] : (univ : Finset α) = ∅
· 使用定理 `Finset.filter_empty`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidablePr
ed p], Finset.filter p ∅ = ∅
· 使用定理 `List.Vector.toList_empty`：toList_empty (v : Vector α 0) : v.toList = []
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fin.card_filter_univ_succ'`：card_filter_univ_succ' (p : Fin (n + 1) -> P
rop) [DecidablePred p] : #{x | p x} = ite (p 0) 1 0 + #{x | p (.succ x)}
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `List.Vector.get_cons_zero`：get_cons_zero (a : α) (v : Vector α n) : get 
(a ::ᵥ v) 0 = a
· 使用定理 `List.Vector.toList_cons`：toList_cons (a : α) (v : Vector α n) : toList (
cons a v) = a :: toList v
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `List.Vector.get_cons_succ`：get_cons_succ (a : α) (v : Vector α n) (i : F
in n) : get (a ::ᵥ v) i.succ = get v i
· 使用定理 `List.count_cons`：∀ {α : Type u_1} [inst : BEq α] {a b : α} {l : List α},
   List.count a (b :: l) = List.count a l + if (b == a) = true then 1 else 0
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
-/
theorem card_filter_univ_eq_vector_get_eq_count [DecidableEq α] (a : α) (v : List.Vector α n) :
    #{i | v.get i = a} = v.toList.count a := by
  induction v with
  | nil => simp
  | @cons n x xs hxs =>
    simp_rw [card_filter_univ_succ', Vector.get_cons_zero, Vector.toList_cons, Vector.get_cons_succ,
      hxs, List.count_cons, add_comm (ite (x = a) 1 0), beq_iff_eq]

/--
Given a "downward-closed" predicate `p` on `Fin n` (which could be spelt `Antitone p`),
then `p` holds for more than `j` elements iff it holds for `p` itself.
-/
/-
**Fin.lt_card_filter_univ_iff_apply_of_imp** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：lt_card_filter_univ_iff_apply_of_imp {j : Fin n} (p : Fin n -> Prop) [Deci
dablePred p] (hp : forall i j, j <= i -> p i -> p j) : j < #{i | p i} ↔ p j
参数：p : Fin n -> Prop；hp : forall i j, j <= i -> p i -> p j。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.card_Iio`：card_Iio : #(Iio b) = b
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Finset.eq_of_subset_of_card_le`：eq_of_subset_of_card_le (h : s subseteq 
t) (h₂ : #t <= #s) : s = t
· 使用定理 `Fin.card_filter_val_lt`：card_filter_val_lt {m : Nat} : #{i : Fin n | i <
 m} = min n m

--- 原说明 ---
Given a "downward-closed" predicate `p` on `Fin n` (which could be spelt `Antito
ne p`),
then `p` holds for more than `j` elements iff it holds for `p` itself.
-/
theorem lt_card_filter_univ_iff_apply_of_imp {j : Fin n} (p : Fin n → Prop) [DecidablePred p]
    (hp : ∀ i j, j ≤ i → p i → p j) :
    j < #{i | p i} ↔ p j := by
  have h1 (k : Fin n) (hk : ¬ p k) : #{i | p i} ≤ k := by
    rw [← Fin.card_Iio]
    exact card_le_card (by grind)
  refine ⟨by grind, fun h ↦ ?_⟩
  by_contra! hc
  let q : Fin n → Prop := (· < #{i | p i})
  have : univ.filter q = univ.filter p :=
    eq_of_subset_of_card_le (by grind) (by rw [card_filter_val_lt]; grind)
  have : j ∈ univ.filter p := by grind
  grind
/-
**Fin._root_.Finset.image_fin_univ** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Finset.image_fin_univ {n : ℕ} :
    (Finset.univ (α := Fin n)).image Fin.val = Finset.range n := by
  ext
  simp [Fin.exists_iff]

@[simp]
/-
**Fin._root_.Finset.sup_fin_univ** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Finset.sup_fin_univ [SemilatticeSup α] [OrderBot α] {n : ℕ} (f : ℕ → α) :
    (Finset.univ (α := Fin n)).sup (fun n ↦ f n) = (Finset.range n).sup f := by
  rw [← image_fin_univ, sup_image, Function.comp_def]

end Fin

