/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.EquivFin

/-!
# fintype instance for `Set α`, when `α` is a fintype
-/

public section


variable {α : Type*}

open Finset

/-
**Finset.fintype** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Finset.fintype [Fintype α] : Fintype (Finset α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Finset.fintype [Fintype α] : Fintype (Finset α) :=
  ⟨univ.powerset, fun _ => Finset.mem_powerset.2 (Finset.subset_univ _)⟩

@[simp]
/-
**Fintype.card_finset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.card_finset [Fintype α] : Fintype.card (Finset α) = 2 ^ Fintype.ca
rd α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_powerset`：card_powerset (s : Finset α) : card (powerset s) =
 2 ^ card s
-/
theorem Fintype.card_finset [Fintype α] : Fintype.card (Finset α) = 2 ^ Fintype.card α :=
  Finset.card_powerset Finset.univ

namespace Finset
variable [Fintype α] {s : Finset α} {k : ℕ}

/-
**Finset.powerset_univ** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : Fintype α], Finset.univ.powerset = Finset.univ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_powerset`：coe_powerset (s : Finset α) : (s.powerset : Set (Fi
nset α)) = ((↑) : Finset α -> Set α) ⁻¹' (s : Set α).powerset
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `Set.powerset_univ`：powerset_univ : 𝒫 (univ : Set α) = univ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma powerset_univ : (univ : Finset α).powerset = univ :=
  coe_injective <| by simp [-coe_eq_univ]
/-
**Finset.filter_subset_univ** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：filter_subset_univ [DecidableEq α] (s : Finset α) : ({t | t subseteq s} : 
Finset _) = powerset s
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma filter_subset_univ [DecidableEq α] (s : Finset α) :
    ({t | t ⊆ s} : Finset _) = powerset s := by ext; simp
/-
**Finset.powerset_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : Fintype α] {s : Finset α}, s.powerset = Finset.un
iv ↔ s = Finset.univ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.powerset_univ`：∀ {α : Type u_1} [inst : Fintype α], Finset.univ.p
owerset = Finset.univ
· 使用定理 `Finset.powerset_inj`：powerset_inj : powerset s = powerset t ↔ s = t
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma powerset_eq_univ : s.powerset = univ ↔ s = univ := by
  rw [← Finset.powerset_univ, powerset_inj]
/-
**Finset.mem_powersetCard_univ** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：mem_powersetCard_univ : s in powersetCard k (univ : Finset α) ↔ #s = k
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Finset.mem_powersetCard`：∀ {α : Type u_1} {n : ℕ} {s t : Finset α}, s ∈ 
Finset.powersetCard n t ↔ s ⊆ t ∧ s.card = n
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `Finset.subset_univ`：subset_univ (s : Finset α) : s subseteq univ
-/
lemma mem_powersetCard_univ : s ∈ powersetCard k (univ : Finset α) ↔ #s = k :=
  mem_powersetCard.trans <| and_iff_right <| subset_univ _

variable (α)
/-
**Finset.univ_filter_card_eq** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ (α : Type u_1) [inst : Fintype α] (k : ℕ), {s | s.card = k} = Finset.pow
ersetCard k Finset.univ
参数：α : Type u_1；k : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma univ_filter_card_eq (k : ℕ) :
    ({s | #s = k} : Finset (Finset α)) = univ.powersetCard k := by ext; simp

end Finset

@[simp]
/-
**Fintype.card_finset_len** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.card_finset_len [Fintype α] (k : Nat) : Fintype.card { s : Finset 
α // #s = k } = Nat.choose (Fintype.card α) k
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.subtype_card`：subtype_card {p : α -> Prop} (s : Finset α) (H : f
orall x : α, x in s ↔ p x) : @card { x // p x } (Fintype.subtype s H) = #s
· 使用定理 `Finset.univ_filter_card_eq`：∀ (α : Type u_1) [inst : Fintype α] (k : ℕ),
 {s | s.card = k} = Finset.powersetCard k Finset.univ
· 使用定理 `Finset.card_powersetCard`：card_powersetCard (n : Nat) (s : Finset α) : c
ard (powersetCard n s) = Nat.choose (card s) n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Fintype.card_finset_len [Fintype α] (k : ℕ) :
    Fintype.card { s : Finset α // #s = k } = Nat.choose (Fintype.card α) k := by
  simp [Fintype.subtype_card, Finset.card_univ]
/-
**Set.fintype** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Set.fintype [Fintype α] : Fintype (Set α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Set.fintype [Fintype α] : Fintype (Set α) :=
  ⟨(@Finset.univ (Finset α) _).map coeEmb.1, fun s => by
    classical
    refine mem_map.2 ⟨({a | a ∈ s} : Finset _), Finset.mem_univ _, (coe_filter _ _).trans ?_⟩
    simp⟩

-- Not to be confused with `Set.Finite`, the predicate
/-
**Set.instFinite** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Set.instFinite [Finite α] : Finite (Set α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
instance Set.instFinite [Finite α] : Finite (Set α) := by
  cases nonempty_fintype α
  infer_instance

@[simp]
/-
**Fintype.card_set** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.card_set [Fintype α] : Fintype.card (Set α) = 2 ^ Fintype.card α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用定理 `Finset.card_powerset`：card_powerset (s : Finset α) : card (powerset s) =
 2 ^ card s
-/
theorem Fintype.card_set [Fintype α] : Fintype.card (Set α) = 2 ^ Fintype.card α :=
  (Finset.card_map _).trans (Finset.card_powerset _)
