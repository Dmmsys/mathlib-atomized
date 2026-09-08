/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Thomas Browning
-/
module

public import Mathlib.Algebra.Group.ConjFinite
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Properties of group actions involving quotient groups

This file proves cardinality properties of group actions which use the quotient group construction,
notably
* the class formula `MulAction.card_eq_sum_card_group_div_card_stabilizer'`
* `card_comm_eq_card_conjClasses_mul_card`

as well as their analogues for additive groups.

See `Mathlib/GroupTheory/GroupAction/Quotient.lean` for the construction of isomorphisms used to
prove these cardinality properties.
These lemmas are separate because they require the development of cardinals.
-/

public section

variable {α β : Type*}

open Function

namespace MulAction

variable (α β)
variable [Group α] [MulAction α β]

local notation "Ω" => Quotient <| orbitRel α β

/-- **Class formula** for a finite group acting on a finite type. See
`MulAction.card_eq_sum_card_group_div_card_stabilizer` for a specialized version using
`Quotient.out`. -/
@[to_additive
      /-- **Class formula** for a finite group acting on a finite type. See
      `AddAction.card_eq_sum_card_addGroup_div_card_stabilizer` for a specialized version using
      `Quotient.out`. -/]
/-
**MulAction.card_eq_sum_card_group_div_card_stabilizer'** 是 Mathlib 中的一个定理，位于命名空
间 `MulAction`。
形式化陈述：card_eq_sum_card_group_div_card_stabilizer' [Fintype α] [Fintype β] [Finty
pe Ω] [forall b : β, Fintype <| stabilizer α b] {φ : Ω -> β} (hφ : LeftInverse Q
uotient.mk'' φ) : Fintype.card β = ∑ ω : Ω, Fintype.card α / Fintype.card (stabi
lizer α (φ ω))
参数：hφ : LeftInverse Quotient.mk'' φ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_congr`：card_congr {α β} [Fintype α] [Fintype β] (f : α ≃ β)
 : card α = card β
· 使用定理 `Fintype.card_prod`：Fintype.card_prod (α β : Type*) [Fintype α] [Fintype 
β] : Fintype.card (α × β) = Fintype.card α * Fintype.card β
· 使用定理 `Nat.mul_div_cancel`：∀ (m : ℕ) {n : ℕ}, 0 < n → m * n / n = m
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fintype.card_pos_iff`：card_pos_iff : 0 < card α ↔ Nonempty α
· 使用定理 `One.instNonempty`：∀ {α : Type u} [One α], Nonempty α
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem card_eq_sum_card_group_div_card_stabilizer' [Fintype α] [Fintype β] [Fintype Ω]
    [∀ b : β, Fintype <| stabilizer α b] {φ : Ω → β} (hφ : LeftInverse Quotient.mk'' φ) :
    Fintype.card β = ∑ ω : Ω, Fintype.card α / Fintype.card (stabilizer α (φ ω)) := by
  classical
    have : ∀ ω : Ω, Fintype.card α / Fintype.card (stabilizer α (φ ω)) =
        Fintype.card (α ⧸ stabilizer α (φ ω)) := by
      intro ω
      rw [Fintype.card_congr (@Subgroup.groupEquivQuotientProdSubgroup α _ (stabilizer α <| φ ω)),
        Fintype.card_prod, Nat.mul_div_cancel]
      exact Fintype.card_pos_iff.mpr (by infer_instance)
    simp_rw [this, ← Fintype.card_sigma,
      Fintype.card_congr (selfEquivSigmaOrbitsQuotientStabilizer' α β hφ)]

/-- **Class formula** for a finite group acting on a finite type. -/
@[to_additive /-- **Class formula** for a finite group acting on a finite type. -/]
/-
**MulAction.card_eq_sum_card_group_div_card_stabilizer** 是 Mathlib 中的一个定理，位于命名空间
 `MulAction`。
形式化陈述：card_eq_sum_card_group_div_card_stabilizer [Fintype α] [Fintype β] [Fintyp
e Ω] [forall b : β, Fintype <| stabilizer α b] : Fintype.card β = ∑ ω : Ω, Finty
pe.card α / Fintype.card (stabilizer α ω.out)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulAction.card_eq_sum_card_group_div_card_stabilizer'`：card_eq_sum_card_
group_div_card_stabilizer' [Fintype α] [Fintype β] [Fintype Ω] [forall b : β, Fi
ntype <| stabilizer α b] {φ : Ω -> β} (hφ :…
· 使用定理 `Quotient.out_eq'`：out_eq' (q : Quotient s₁) : Quotient.mk'' q.out = q

--- 原说明 ---
**Class formula** for a finite group acting on a finite type.
-/
theorem card_eq_sum_card_group_div_card_stabilizer [Fintype α] [Fintype β] [Fintype Ω]
    [∀ b : β, Fintype <| stabilizer α b] :
    Fintype.card β = ∑ ω : Ω, Fintype.card α / Fintype.card (stabilizer α ω.out) :=
  card_eq_sum_card_group_div_card_stabilizer' α β Quotient.out_eq'

end MulAction

set_option backward.isDefEq.respectTransparency false in
/-
**instInfiniteProdSubtypeCommute** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：instInfiniteProdSubtypeCommute [Mul α] [Infinite α] : Infinite { p : α × α
 // Commute p.1 p.2 }
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Infinite.of_injective`：of_injective {α β} [Infinite β] (f : β -> α) (hf 
: Injective f) : Infinite α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
instance instInfiniteProdSubtypeCommute [Mul α] [Infinite α] :
    Infinite { p : α × α // Commute p.1 p.2 } :=
  Infinite.of_injective (fun a => ⟨⟨a, a⟩, rfl⟩) (by intro; simp)

open Fintype
/-
**card_comm_eq_card_conjClasses_mul_card** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：card_comm_eq_card_conjClasses_mul_card (G : Type*) [Group G] : Nat.card { 
p : G × G // Commute p.1 p.2 } = Nat.card (ConjClasses G) * Nat.card G
参数：G : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Fintype.card_congr`：card_congr {α β} [Fintype α] [Fintype β] (f : α ≃ β)
 : card α = card β
· 使用定理 `Fintype.card_sigma`：∀ {ι : Type u_8} {α : ι → Type u_7} [inst : Fintype 
ι] [inst_1 : (i : ι) → Fintype (α i)],   Fintype.card (Sigma α) = ∑ i, Fintype.c
ard (α i…
· 使用定理 `Fintype.sum_equiv`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst 
: Fintype ι] [inst_1 : Fintype κ] [inst_2 : AddCommMonoid M]   (e : ι ≃ κ) (f : 
ι → M) …
· 使用定理 `Fintype.card_congr'`：card_congr' {α β} [Fintype α] [Fintype β] (h : α = 
β) : card α = card β
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `mul_inv_eq_iff_eq_mul`：mul_inv_eq_iff_eq_mul : a * b⁻¹ = c ↔ a = c * b
· 使用定理 `MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group`：sum_card_fixed
By_eq_card_orbits_mul_card_group [Fintype G] [forall g : G, Fintype <| fixedBy X
 g] [Fintype Ω] : (∑ g : G, Fintype.card (fixe…
· 使用定理 `Setoid.ext`：ext {α : Sort*} : forall {s t : Setoid α}, (forall a b, s a 
b ↔ t a b) -> s = t | ⟨r, _⟩, ⟨p, _⟩, Eq => by have : r = p
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Setoid.comm'`：comm' (s : Setoid α) {x y} : s x y ↔ s y x
· 使用定理 `isConj_iff`：isConj_iff {a b : α} : IsConj a b ↔ exists c : α, c * a * c⁻
¹ = b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Nat.card_eq_zero_of_infinite`：∀ {α : Type u_1} [Infinite α], Nat.card α 
= 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
theorem card_comm_eq_card_conjClasses_mul_card (G : Type*) [Group G] :
    Nat.card { p : G × G // Commute p.1 p.2 } = Nat.card (ConjClasses G) * Nat.card G := by
  classical
  rcases fintypeOrInfinite G; swap
  · rw [mul_comm, Nat.card_eq_zero_of_infinite, Nat.card_eq_zero_of_infinite, zero_mul]
  simp only [Nat.card_eq_fintype_card]
  calc card { p : G × G // Commute p.1 p.2 }
      _ = card ((a : G) × { b // Commute a b }) :=
            card_congr (Equiv.subtypeProdEquivSigmaSubtype Commute)
      _ = ∑ i, card { b // Commute i b } := card_sigma
      _ = ∑ x, card (MulAction.fixedBy G x) :=
            sum_equiv ConjAct.toConjAct.toEquiv (fun a ↦ card { b // Commute a b })
              (fun g ↦ card (MulAction.fixedBy G g))
              fun g ↦ card_congr' <| congr_arg _ <| funext fun h ↦ mul_inv_eq_iff_eq_mul.symm.eq
      _ = card (Quotient (MulAction.orbitRel (ConjAct G) G)) * card (ConjAct G) :=
             MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group _ _
      _ = card (ConjClasses G) * card G := by
             congr 1; apply card_congr'; congr; ext
             exact (Setoid.comm' _).trans isConj_iff.symm
