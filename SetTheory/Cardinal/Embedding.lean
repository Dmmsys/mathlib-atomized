/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Fin.Tuple.Embedding
public import Mathlib.Data.Set.Card
public import Mathlib.SetTheory.Cardinal.NatCard

/-! # Existence of embeddings from finite types

Let `s : Set α` be a finite set.

* `Fin.Embedding.exists_embedding_disjoint_range_of_add_le_ENat_card`
  If `s.ncard + n ≤ ENat.card α`,
  then there exists an embedding `Fin n ↪ α`
  whose range is disjoint from `s`.

* `Fin.Embedding.exists_embedding_disjoint_range_of_add_le_Nat_card`
  If `α` is finite and `s.ncard + n ≤ Nat.card α`,
  then there exists an embedding `Fin n ↪ α`
  whose range is disjoint from `s`.

* `Fin.Embedding.restrictSurjective_of_add_le_ENatCard`
  If `m + n ≤ ENat.card α`, then the restriction map
  from `Fin (m + n) ↪ α` to `Fin m ↪ α` is surjective.

* `Fin.Embedding.restrictSurjective_of_add_le_natCard`
  If `α` is finite and `m + n ≤ Nat.card α`, then the restriction
  map from `Fin (m + n) ↪ α` to `Fin m ↪ α` is surjective.
-/

public section

open Set Fin Function Function.Embedding

namespace Fin.Embedding

variable {α : Type*} {m n : ℕ} {s : Set α}

/-
**Fin.Embedding.exists_embedding_disjoint_range_of_add_le_ENat_card** 是 Mathlib 
中的一个定理，位于命名空间 `Fin.Embedding`。
形式化陈述：exists_embedding_disjoint_range_of_add_le_ENat_card [Finite s] (hs : s.nca
rd + n <= ENat.card α) : exists y : Fin n ↪ α, Disjoint s (range y)
参数：hs : s.ncard + n <= ENat.card α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finite_or_infinite`：finite_or_infinite (α : Sort*) : Finite α ∨ Infinite
 α
· 使用定理 `Function.Embedding.nonempty_of_card_le`：nonempty_of_card_le [Fintype α] 
[Fintype β] (h : Fintype.card α <= Fintype.card β) : Nonempty (α ↪ β)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_le_add_iff_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [Ad
dLeftMono α] [AddLeftReflectLE α] (a : α) {b c : α},   a + b ≤ a + c ↔ b ≤ c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Nat.card_coe_set_eq`：∀ {α : Type u_1} (s : Set α), Nat.card ↑s = s.ncard
· 使用定理 `Set.ncard_add_ncard_compl`：ncard_add_ncard_compl (s : Set α) (hs : s.Fin
ite
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用引理 `ENat.natCast_le_natCast`：natCast_le_natCast {n m : Nat} : (n : Nat∞) <= 
(m : Nat∞) ↔ n <= m
· 使用定理 `ENat.card_eq_coe_natCard`：card_eq_coe_natCard (α : Type*) [Finite α] : c
ard α = Nat.card α
· 使用定理 `ENat.natCast_add`：natCast_add (m n : Nat) : ↑(m + n) = (m + n : Nat∞)
· 使用定理 `Set.Infinite.to_subtype`：∀ {α : Type u} {s : Set α}, s.Infinite → Infini
te ↑s
· 使用定理 `Set.Finite.infinite_compl`：∀ {α : Type u} [Infinite α] {s : Set α}, s.Fi
nite → sᶜ.Infinite
· 使用定理 `Set.disjoint_right`：disjoint_right : Disjoint s t ↔ forall ⦃a⦄, a in t -
> a ∉ s
· 使用定理 `Subtype.coe_prop`：coe_prop {S : Set α} (a : { a // a in S }) : ↑a in S
-/
theorem exists_embedding_disjoint_range_of_add_le_ENat_card
    [Finite s] (hs : s.ncard + n ≤ ENat.card α) :
    ∃ y : Fin n ↪ α, Disjoint s (range y) := by
  rsuffices ⟨y⟩ : Nonempty (Fin n ↪ (sᶜ : Set α))
  · use y.trans (subtype _)
    rw [Set.disjoint_right]
    rintro _ ⟨i, rfl⟩
    simpa only [← mem_compl_iff] using! Subtype.coe_prop (y i)
  rcases finite_or_infinite α with hα | hα
  · let _ : Fintype α := Fintype.ofFinite α
    classical
    apply nonempty_of_card_le
    rwa [Fintype.card_fin, ← add_le_add_iff_left s.ncard,
      ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq,
        ncard_add_ncard_compl, ← ENat.natCast_le_natCast,
        ← ENat.card_eq_coe_natCard, ENat.natCast_add]
  · exact ⟨valEmbedding.trans s.toFinite.infinite_compl.to_subtype.natEmbedding⟩
/-
**Fin.Embedding.exists_embedding_disjoint_range_of_add_le_Nat_card** 是 Mathlib 中
的一个定理，位于命名空间 `Fin.Embedding`。
形式化陈述：exists_embedding_disjoint_range_of_add_le_Nat_card [Finite α] (hs : s.ncar
d + n <= Nat.card α) : exists y : Fin n ↪ α, Disjoint s (range y)
参数：hs : s.ncard + n <= Nat.card α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.Embedding.exists_embedding_disjoint_range_of_add_le_ENat_card`：exist
s_embedding_disjoint_range_of_add_le_ENat_card [Finite s] (hs : s.ncard + n <= E
Nat.card α) : exists y : Fin n ↪ α, Disjoint s (range y…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENat.natCast_add`：natCast_add (m n : Nat) : ↑(m + n) = (m + n : Nat∞)
· 使用定理 `ENat.card_eq_coe_natCard`：card_eq_coe_natCard (α : Type*) [Finite α] : c
ard α = Nat.card α
· 使用引理 `ENat.natCast_le_natCast`：natCast_le_natCast {n m : Nat} : (n : Nat∞) <= 
(m : Nat∞) ↔ n <= m
-/
theorem exists_embedding_disjoint_range_of_add_le_Nat_card
    [Finite α] (hs : s.ncard + n ≤ Nat.card α) :
    ∃ y : Fin n ↪ α, Disjoint s (range y) := by
  apply exists_embedding_disjoint_range_of_add_le_ENat_card
  rwa [← ENat.natCast_add, ENat.card_eq_coe_natCard, ENat.natCast_le_natCast]
/-
**Fin.Embedding.restrictSurjective_of_add_le_ENatCard** 是 Mathlib 中的一个定理，位于命名空间 
`Fin.Embedding`。
形式化陈述：restrictSurjective_of_add_le_ENatCard (hn : m + n <= ENat.card α) : Surjec
tive (fun (x : Fin (m + n) ↪ α) => (Fin.castAddEmb n).trans x)
参数：hn : m + n <= ENat.card α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.Embedding.exists_embedding_disjoint_range_of_add_le_ENat_card`：exist
s_embedding_disjoint_range_of_add_le_ENat_card [Finite s] (hs : s.ncard + n <= E
Nat.card α) : exists y : Fin n ↪ α, Disjoint s (range y…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Nat.card_range_of_injective`：card_range_of_injective {f : α -> β} (hf : 
Injective f) : Nat.card (range f) = Nat.card α
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Function.Embedding.ext`：ext {α β} {f g : Embedding α β} (h : forall x, f
 x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Function.Embedding.trans_apply`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sor
t u_3} (f : α ↪ β) (g : β ↪ γ) (a : α), (f.trans g) a = g (f a)
· 使用定理 `Fin.append_left`：append_left (u : Fin m -> α) (v : Fin n -> α) (i : Fin 
m) : append u v (Fin.castAdd n i) = u i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem restrictSurjective_of_add_le_ENatCard (hn : m + n ≤ ENat.card α) :
    Surjective (fun (x : Fin (m + n) ↪ α) ↦ (Fin.castAddEmb n).trans x) := by
  intro x
  obtain ⟨y, hxy⟩ :=
    exists_embedding_disjoint_range_of_add_le_ENat_card (s := range x)
      (by simpa [← Nat.card_coe_set_eq, Nat.card_range_of_injective x.injective])
  use append hxy
  ext i
  simp [trans_apply, coe_castAddEmb, append]
/-
**Fin.Embedding.restrictSurjective_of_le_ENatCard** 是 Mathlib 中的一个定理，位于命名空间 `Fin
.Embedding`。
形式化陈述：restrictSurjective_of_le_ENatCard (hmn : m <= n) (hn : n <= ENat.card α) :
 Function.Surjective (fun x : Fin n ↪ α => (castLEEmb hmn).trans x)
参数：hmn : m <= n；hn : n <= ENat.card α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.exists_eq_add_of_le`：∀ {m n : ℕ}, m ≤ n → ∃ k, n = m + k
· 使用定理 `Fin.Embedding.restrictSurjective_of_add_le_ENatCard`：restrictSurjective_
of_add_le_ENatCard (hn : m + n <= ENat.card α) : Surjective (fun (x : Fin (m + n
) ↪ α) => (Fin.castAddEmb n).trans x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem restrictSurjective_of_le_ENatCard (hmn : m ≤ n) (hn : n ≤ ENat.card α) :
    Function.Surjective (fun x : Fin n ↪ α ↦ (castLEEmb hmn).trans x) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  exact Fin.Embedding.restrictSurjective_of_add_le_ENatCard hn
/-
**Fin.Embedding.restrictSurjective_of_add_le_natCard** 是 Mathlib 中的一个定理，位于命名空间 `
Fin.Embedding`。
形式化陈述：restrictSurjective_of_add_le_natCard [Finite α] (hn : m + n <= Nat.card α)
 : Surjective (fun x : Fin (m + n) ↪ α => (castAddEmb n).trans x)
参数：hn : m + n <= Nat.card α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.Embedding.restrictSurjective_of_add_le_ENatCard`：restrictSurjective_
of_add_le_ENatCard (hn : m + n <= ENat.card α) : Surjective (fun (x : Fin (m + n
) ↪ α) => (Fin.castAddEmb n).trans x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENat.natCast_add`：natCast_add (m n : Nat) : ↑(m + n) = (m + n : Nat∞)
· 使用定理 `ENat.card_eq_coe_natCard`：card_eq_coe_natCard (α : Type*) [Finite α] : c
ard α = Nat.card α
· 使用引理 `ENat.natCast_le_natCast`：natCast_le_natCast {n m : Nat} : (n : Nat∞) <= 
(m : Nat∞) ↔ n <= m
-/
theorem restrictSurjective_of_add_le_natCard [Finite α] (hn : m + n ≤ Nat.card α) :
    Surjective (fun x : Fin (m + n) ↪ α ↦ (castAddEmb n).trans x) := by
  apply restrictSurjective_of_add_le_ENatCard
  rwa [← ENat.natCast_add, ENat.card_eq_coe_natCard, ENat.natCast_le_natCast]
/-
**Fin.Embedding.restrictSurjective_of_le_natCard** 是 Mathlib 中的一个定理，位于命名空间 `Fin.
Embedding`。
形式化陈述：restrictSurjective_of_le_natCard [Finite α] (hmn : m <= n) (hn : n <= Nat.
card α) : Function.Surjective (fun x : Fin n ↪ α => (castLEEmb hmn).trans x)
参数：hmn : m <= n；hn : n <= Nat.card α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.exists_eq_add_of_le`：∀ {m n : ℕ}, m ≤ n → ∃ k, n = m + k
· 使用定理 `Fin.Embedding.restrictSurjective_of_add_le_natCard`：restrictSurjective_o
f_add_le_natCard [Finite α] (hn : m + n <= Nat.card α) : Surjective (fun x : Fin
 (m + n) ↪ α => (castAddEmb n).trans x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem restrictSurjective_of_le_natCard [Finite α] (hmn : m ≤ n) (hn : n ≤ Nat.card α) :
    Function.Surjective (fun x : Fin n ↪ α ↦ (castLEEmb hmn).trans x) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  exact Fin.Embedding.restrictSurjective_of_add_le_natCard hn

end Fin.Embedding

