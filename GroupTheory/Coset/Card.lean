/-
Copyright (c) 2018 Mitchell Rowett. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Rowett, Kim Morrison
-/
module

public import Mathlib.GroupTheory.Coset.Basic
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Lagrange's theorem: the order of a subgroup divides the order of the group.

* `Subgroup.card_subgroup_dvd_card`: Lagrange's theorem (for multiplicative groups);
  there is an analogous version for additive groups

-/

public section

assert_not_exists Field

open scoped Pointwise

variable {α : Type*} [Group α] {s : Subgroup α}

namespace QuotientGroup

@[to_additive]
/-
**QuotientGroup.fintype** 是 Mathlib 中的一个实例，位于命名空间 `QuotientGroup`。
形式化陈述：fintype [Fintype α] (s : Subgroup α) [DecidableRel (leftRel s).r] : Fintyp
e (α ⧸ s)
参数：s : Subgroup α；leftRel s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance fintype [Fintype α] (s : Subgroup α) [DecidableRel (leftRel s).r] : Fintype (α ⧸ s) :=
  Quotient.fintype (leftRel s)

@[to_additive]
/-
**QuotientGroup.** 是 Mathlib 中的一个实例，位于命名空间 `QuotientGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) finite [Finite α] : Finite (α ⧸ s) :=
  Quotient.finite _

@[to_additive]
/-
**QuotientGroup.fintypeQuotientRightRel** 是 Mathlib 中的一个实例，位于命名空间 `QuotientGroup
`。
形式化陈述：fintypeQuotientRightRel [Fintype (α ⧸ s)] : Fintype (Quotient (QuotientGro
up.rightRel s))
参数：α ⧸ s。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
instance fintypeQuotientRightRel [Fintype (α ⧸ s)] :
    Fintype (Quotient (QuotientGroup.rightRel s)) :=
  .ofEquiv (α ⧸ s) (QuotientGroup.quotientRightRelEquivQuotientLeftRel s).symm

variable (s) in
@[to_additive]
/-
**QuotientGroup.card_quotient_rightRel** 是 Mathlib 中的一个引理，位于命名空间 `QuotientGroup`
。
形式化陈述：card_quotient_rightRel [Fintype (α ⧸ s)] : Fintype.card (Quotient (Quotien
tGroup.rightRel s)) = Fintype.card (α ⧸ s)
参数：α ⧸ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.ofEquiv_card`：ofEquiv_card [Fintype α] (f : α ≃ β) : @card β (of
Equiv α f) = card α
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma card_quotient_rightRel [Fintype (α ⧸ s)] :
    Fintype.card (Quotient (QuotientGroup.rightRel s)) = Fintype.card (α ⧸ s) :=
  Fintype.ofEquiv_card (QuotientGroup.quotientRightRelEquivQuotientLeftRel s).symm

end QuotientGroup

namespace Subgroup

@[to_additive AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup]
/-
**Subgroup.card_eq_card_quotient_mul_card_subgroup** 是 Mathlib 中的一个定理，位于命名空间 `Su
bgroup`。
形式化陈述：card_eq_card_quotient_mul_card_subgroup (s : Subgroup α) : Nat.card α = Na
t.card (α ⧸ s) * Nat.card s
参数：s : Subgroup α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.card_prod`：card_prod (α β : Type*) : Nat.card (α × β) = Nat.card α *
 Nat.card β
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
-/
theorem card_eq_card_quotient_mul_card_subgroup (s : Subgroup α) :
    Nat.card α = Nat.card (α ⧸ s) * Nat.card s := by
  rw [← Nat.card_prod]; exact Nat.card_congr Subgroup.groupEquivQuotientProdSubgroup

@[to_additive]
/-
**Subgroup.card_mul_eq_card_subgroup_mul_card_quotient** 是 Mathlib 中的一个引理，位于命名空间
 `Subgroup`。
形式化陈述：card_mul_eq_card_subgroup_mul_card_quotient (s : Subgroup α) (t : Set α) :
 Nat.card (t * s : Set α) = Nat.card s * Nat.card (t.image (↑) : Set (α ⧸ s))
参数：s : Subgroup α；t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.card_prod`：card_prod (α β : Type*) : Nat.card (α × β) = Nat.card α *
 Nat.card β
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `QuotientGroup.preimage_image_mk`：preimage_image_mk (N : Subgroup α) (s :
 Set α) : mk ⁻¹' ((mk : α -> α ⧸ N) '' s) = ⋃ x : N, (· * (x : α)) ⁻¹' s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `InvMemClass.inv_mem`：∀ {S : Type u_3} {G : outParam (Type u_4)} {inst : 
Inv G} {inst_1 : SetLike S G} [self : InvMemClass S G] {s : S}   {x : G}, x ∈ s 
→ x⁻¹ ∈ s
· 使用定理 `SubgroupClass.toInvMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4)} 
{inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   Inv
MemClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `mul_inv_cancel_right`：mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
-/
lemma card_mul_eq_card_subgroup_mul_card_quotient (s : Subgroup α) (t : Set α) :
    Nat.card (t * s : Set α) = Nat.card s * Nat.card (t.image (↑) : Set (α ⧸ s)) := by
  rw [← Nat.card_prod, Nat.card_congr]
  apply Equiv.trans _ (QuotientGroup.preimageMkEquivSubgroupProdSet _ _)
  rw [QuotientGroup.preimage_image_mk]
  convert! Equiv.refl ↑(t * s)
  aesop (add simp [Set.mem_mul])

/-- **Lagrange's Theorem**: The order of a subgroup divides the order of its ambient group. -/
@[to_additive (attr := wikidata Q505798) /-- **Lagrange's Theorem**: The order of an additive
subgroup divides the order of its ambient additive group. -/]
/-
**Subgroup.card_subgroup_dvd_card** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：card_subgroup_dvd_card (s : Subgroup α) : Nat.card s ∣ Nat.card α
参数：s : Subgroup α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.card_eq_card_quotient_mul_card_subgroup`：card_eq_card_quotient_
mul_card_subgroup (s : Subgroup α) : Nat.card α = Nat.card (α ⧸ s) * Nat.card s
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `dvd_mul_left`：dvd_mul_left (a b : α) : a ∣ b * a
-/
theorem card_subgroup_dvd_card (s : Subgroup α) : Nat.card s ∣ Nat.card α := by
  simp [card_eq_card_quotient_mul_card_subgroup s, @dvd_mul_left ℕ]

@[to_additive]
/-
**Subgroup.card_quotient_dvd_card** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：card_quotient_dvd_card (s : Subgroup α) : Nat.card (α ⧸ s) ∣ Nat.card α
参数：s : Subgroup α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.card_eq_card_quotient_mul_card_subgroup`：card_eq_card_quotient_
mul_card_subgroup (s : Subgroup α) : Nat.card α = Nat.card (α ⧸ s) * Nat.card s
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `dvd_mul_right`：dvd_mul_right (a b : α) : a ∣ a * b
-/
theorem card_quotient_dvd_card (s : Subgroup α) : Nat.card (α ⧸ s) ∣ Nat.card α := by
  simp [card_eq_card_quotient_mul_card_subgroup s, @dvd_mul_right ℕ]

variable {H : Type*} [Group H]

@[to_additive]
/-
**Subgroup.card_dvd_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：card_dvd_of_injective (f : α ->* H) (hf : Function.Injective f) : Nat.card
 α ∣ Nat.card H
参数：f : α ->* H；hf : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
· 使用定理 `Subgroup.card_subgroup_dvd_card`：card_subgroup_dvd_card (s : Subgroup α)
 : Nat.card s ∣ Nat.card α
-/
theorem card_dvd_of_injective (f : α →* H) (hf : Function.Injective f) :
    Nat.card α ∣ Nat.card H := by
  calc
      Nat.card α = Nat.card (f.range : Subgroup H) := Nat.card_congr (Equiv.ofInjective f hf)
      _ ∣ Nat.card H := card_subgroup_dvd_card _

@[to_additive]
/-
**Subgroup.card_dvd_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：card_dvd_of_le {H K : Subgroup α} (hHK : H <= K) : Nat.card H ∣ Nat.card K
参数：hHK : H <= K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.card_dvd_of_injective`：card_dvd_of_injective (f : α ->* H) (hf 
: Function.Injective f) : Nat.card α ∣ Nat.card H
· 使用定理 `Subgroup.inclusion_injective`：inclusion_injective {H K : Subgroup G} (h 
: H <= K) : Function.Injective inclusion h
-/
theorem card_dvd_of_le {H K : Subgroup α} (hHK : H ≤ K) : Nat.card H ∣ Nat.card K :=
  card_dvd_of_injective (inclusion hHK) (inclusion_injective hHK)

@[to_additive]
/-
**Subgroup.card_comap_dvd_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：card_comap_dvd_of_injective (K : Subgroup H) (f : α ->* H) (hf : Function.
Injective f) : Nat.card (K.comap f) ∣ Nat.card K
参数：K : Subgroup H；f : α ->* H；hf : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
· 使用定理 `Subgroup.card_dvd_of_le`：card_dvd_of_le {H K : Subgroup α} (hHK : H <= K
) : Nat.card H ∣ Nat.card K
· 使用定理 `Subgroup.map_comap_le`：map_comap_le (H : Subgroup N) : map f (comap f H)
 <= H
-/
theorem card_comap_dvd_of_injective (K : Subgroup H) (f : α →* H)
    (hf : Function.Injective f) : Nat.card (K.comap f) ∣ Nat.card K :=
  calc Nat.card (K.comap f) = Nat.card ((K.comap f).map f) :=
      Nat.card_congr (equivMapOfInjective _ _ hf).toEquiv
    _ ∣ Nat.card K := card_dvd_of_le (map_comap_le _ _)

end Subgroup

