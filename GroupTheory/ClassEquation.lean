/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Eric Rodriguez
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Group.ConjFinite
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Data.Set.Card
public import Mathlib.GroupTheory.Subgroup.Center

/-!
# Class Equation

This file establishes the class equation for finite groups.

## Main statements

* `Group.card_center_add_sum_card_noncenter_eq_card`: The **class equation** for finite groups.
  The cardinality of a group is equal to the size of its center plus the sum of the size of all its
  nontrivial conjugacy classes. Also `Group.nat_card_center_add_sum_card_noncenter_eq_card`.

-/

public section

open MulAction ConjClasses

variable (G : Type*) [Group G]

/-- Conjugacy classes form a partition of G, stated in terms of cardinality. -/
/-
**sum_conjClasses_card_eq_card** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sum_conjClasses_card_eq_card [Fintype <| ConjClasses G] [Fintype G] [foral
l x : ConjClasses G, Fintype x.carrier] : ∑ x : ConjClasses G, x.carrier.toFinse
t.card = Fintype.card G
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ConjClasses.carrier_eq_preimage_mk`：carrier_eq_preimage_mk {a : ConjClas
ses α} : a.carrier = ConjClasses.mk ⁻¹' {a}
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.toFinset_card`：toFinset_card {α : Type*} (s : Set α) [Fintype s] : s
.toFinset.card = Fintype.card s
· 使用定理 `Set.fintypeCard_eq_ncard`：fintypeCard_eq_ncard [Fintype s] : Fintype.car
d s = s.ncard
· 使用定理 `Fintype.card_sigma`：∀ {ι : Type u_8} {α : ι → Type u_7} [inst : Fintype 
ι] [inst_1 : (i : ι) → Fintype (α i)],   Fintype.card (Sigma α) = ∑ i, Fintype.c
ard (α i…
· 使用定理 `Fintype.card_congr`：card_congr {α β} [Fintype α] [Fintype β] (f : α ≃ β)
 : card α = card β

--- 原说明 ---
Conjugacy classes form a partition of G, stated in terms of cardinality.
-/
theorem sum_conjClasses_card_eq_card [Fintype <| ConjClasses G] [Fintype G]
    [∀ x : ConjClasses G, Fintype x.carrier] :
    ∑ x : ConjClasses G, x.carrier.toFinset.card = Fintype.card G := by
  suffices (Σ x : ConjClasses G, x.carrier) ≃ G by simpa using! (Fintype.card_congr this)
  simpa [carrier_eq_preimage_mk] using! Equiv.sigmaFiberEquiv ConjClasses.mk

/-- Conjugacy classes form a partition of G, stated in terms of cardinality. -/
/-
**Group.sum_card_conj_classes_eq_card** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Group.sum_card_conj_classes_eq_card [Finite G] : ∑ᶠ x : ConjClasses G, x.c
arrier.ncard = Nat.card G
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finsum_eq_sum_of_fintype`：∀ {α : Type u_1} {M : Type u_5} [inst : AddCom
mMonoid M] [inst_1 : Fintype α] (f : α → M), ∑ᶠ (i : α), f i = ∑ i, f i
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Set.toFinset_card`：toFinset_card {α : Type*} (s : Set α) [Fintype s] : s
.toFinset.card = Fintype.card s
· 使用定理 `Set.fintypeCard_eq_ncard`：fintypeCard_eq_ncard [Fintype s] : Fintype.car
d s = s.ncard
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Conjugacy classes form a partition of G, stated in terms of cardinality.
-/
theorem Group.sum_card_conj_classes_eq_card [Finite G] :
    ∑ᶠ x : ConjClasses G, x.carrier.ncard = Nat.card G := by
  classical
  cases nonempty_fintype G
  simp [← sum_conjClasses_card_eq_card, finsum_eq_sum_of_fintype]

set_option backward.isDefEq.respectTransparency false in
/-- The **class equation** for finite groups. The cardinality of a group is equal to the size
of its center plus the sum of the size of all its nontrivial conjugacy classes. -/
/-
**Group.nat_card_center_add_sum_card_noncenter_eq_card** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：Group.nat_card_center_add_sum_card_noncenter_eq_card [Finite G] : Nat.card
 (Subgroup.center G) + ∑ᶠ x in noncenter G, Nat.card x.carrier = Nat.card G
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sum_conjClasses_card_eq_card`：sum_conjClasses_card_eq_card [Fintype <| C
onjClasses G] [Fintype G] [forall x : ConjClasses G, Fintype x.carrier] : ∑ x : 
ConjClasses G, x.c…
· 使用定理 `Finset.sum_sdiff`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   s₁ ⊆ s₂ → ∑ x ∈ s₂
 \ s₁,…
· 使用定理 `Finset.subset_univ`：subset_univ (s : Finset α) : s subseteq univ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `finsum_congr_Prop`：∀ {M : Type u_2} [inst : AddCommMonoid M] {p q : Prop
} {f : p → M} {g : q → M} (hpq : p = q),   (∀ (h : q), f ⋯ = g h) → finsum f = f
insum g
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Set.toFinset_card`：toFinset_card {α : Type*} (s : Set α) [Fintype s] : s
.toFinset.card = Fintype.card s
· 使用定理 `Fintype.card_congr`：card_congr {α β} [Fintype α] [Fintype β] (f : α ≃ β)
 : card α = card β
· 使用定理 `ConjClasses.mk_bijOn`：mk_bijOn (G : Type*) [Group G] : Set.BijOn ConjCla
sses.mk (↑(Subgroup.center G)) (noncenter G)ᶜ
· 使用定理 `Set.toFinset_compl`：toFinset_compl [Fintype α] [Fintype (sᶜ : Set _)] : 
sᶜ.toFinset = s.toFinsetᶜ
· 使用定理 `Finset.compl_eq_univ_sdiff`：compl_eq_univ_sdiff (s : Finset α) : sᶜ = un
iv \ s
· 使用引理 `Finset.card_eq_sum_ones`：card_eq_sum_ones (s : Finset ι) : #s = ∑ _ in s
, 1
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Finset.card_eq_one`：card_eq_one : #s = 1 ↔ exists a, s = {a}
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `Set.coe_toFinset`：coe_toFinset (s : Set α) [Fintype s] : (↑s.toFinset : 
Set α) = s
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `Set.Subsingleton.eq_singleton_of_mem`：∀ {α : Type u} {s : Set α}, s.Subs
ingleton → ∀ {x : α}, x ∈ s → s = {x}
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.toFinset_ofPred`：toFinset_ofPred [Fintype α] (p : α -> Prop) [Decida
blePred p] [Fintype { x | p x }] : Set.toFinset {x | p x} = Finset.univ.filter p
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `ConjClasses.mem_carrier_mk`：mem_carrier_mk {a : α} : a in carrier (ConjC
lasses.mk a)
· 使用定理 `finsum_cond_eq_sum_of_cond_iff`：∀ {α : Type u_1} {M : Type u_5} [inst : 
AddCommMonoid M] (f : α → M) {p : α → Prop} {t : Finset α},   (∀ {x : α}, f x ≠ 
0 → (p x ↔ x ∈ t)) →…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
The **class equation** for finite groups. The cardinality of a group is equal to
 the size
of its center plus the sum of the size of all its nontrivial conjugacy classes.
-/
theorem Group.nat_card_center_add_sum_card_noncenter_eq_card [Finite G] :
    Nat.card (Subgroup.center G) + ∑ᶠ x ∈ noncenter G, Nat.card x.carrier = Nat.card G := by
  classical
  cases nonempty_fintype G
  rw [@Nat.card_eq_fintype_card G, ← sum_conjClasses_card_eq_card, ←
    Finset.sum_sdiff (ConjClasses.noncenter G).toFinset.subset_univ]
  simp only [Nat.card_eq_fintype_card, Set.toFinset_card]
  congr 1
  swap
  · convert! finsum_cond_eq_sum_of_cond_iff _ _
    simp [Set.mem_toFinset]
  calc
    Fintype.card (Subgroup.center G) = Fintype.card ((noncenter G)ᶜ : Set _) :=
      Fintype.card_congr ((mk_bijOn G).equiv _)
    _ = Finset.card (Finset.univ \ (noncenter G).toFinset) := by
      rw [← Set.toFinset_card, Set.toFinset_compl, Finset.compl_eq_univ_sdiff]
    _ = _ := ?_
  rw [Finset.card_eq_sum_ones]
  refine Finset.sum_congr rfl ?_
  rintro ⟨g⟩ hg
  simp only [noncenter, Set.toFinset_ofPred, Finset.mem_univ, true_and,
             Finset.mem_sdiff, Finset.mem_filter, Set.not_nontrivial_iff] at hg
  rw [eq_comm, ← Set.toFinset_card, Finset.card_eq_one]
  exact ⟨g, Finset.coe_injective <| by simpa using hg.eq_singleton_of_mem mem_carrier_mk⟩
/-
**Group.card_center_add_sum_card_noncenter_eq_card** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Group.card_center_add_sum_card_noncenter_eq_card (G) [Group G] [forall x :
 ConjClasses G, Fintype x.carrier] [Fintype G] [Fintype <| Subgroup.center G] [F
intype <| noncenter G] : Fintype.card (Subgroup.center G) + ∑ x in (noncenter G)
.toFinset, x.carrier.toFinset.card = Fintype.card G
参数：G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `finsum_set_coe_eq_finsum_mem`：∀ {α : Type u_1} {M : Type u_5} [inst : Ad
dCommMonoid M] {f : α → M} (s : Set α),   ∑ᶠ (j : ↑s), f ↑j = ∑ᶠ (i : α) (_ : i 
∈ s), f i
· 使用定理 `finsum_eq_sum_of_fintype`：∀ {α : Type u_1} {M : Type u_5} [inst : AddCom
mMonoid M] [inst_1 : Fintype α] (f : α → M), ∑ᶠ (i : α), f i = ∑ i, f i
· 使用定理 `Finset.sum_set_coe`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoi
d M] {f : ι → M} (s : Set ι) [inst_1 : Fintype ↑s],   ∑ i, f ↑i = ∑ i ∈ s.toFins
et, f i
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Set.toFinset_card`：toFinset_card {α : Type*} (s : Set α) [Fintype s] : s
.toFinset.card = Fintype.card s
· 使用定理 `Set.fintypeCard_eq_ncard`：fintypeCard_eq_ncard [Fintype s] : Fintype.car
d s = s.ncard
· 使用定理 `Group.nat_card_center_add_sum_card_noncenter_eq_card`：Group.nat_card_cen
ter_add_sum_card_noncenter_eq_card [Finite G] : Nat.card (Subgroup.center G) + ∑
ᶠ x in noncenter G, Nat.card x.carrier = N…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
theorem Group.card_center_add_sum_card_noncenter_eq_card (G) [Group G]
    [∀ x : ConjClasses G, Fintype x.carrier] [Fintype G] [Fintype <| Subgroup.center G]
    [Fintype <| noncenter G] : Fintype.card (Subgroup.center G) +
    ∑ x ∈ (noncenter G).toFinset, x.carrier.toFinset.card = Fintype.card G := by
  convert! Group.nat_card_center_add_sum_card_noncenter_eq_card G using 2
  · simp
  · rw [← finsum_set_coe_eq_finsum_mem (noncenter G), finsum_eq_sum_of_fintype,
      ← Finset.sum_set_coe]
    simp
  · simp
