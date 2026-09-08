/-
Copyright (c) 2020 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import Mathlib.Algebra.Group.Submonoid.Finite
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Subgroups

This file provides some result on multiplicative and additive subgroups in the finite context.

## Tags
subgroup, subgroups
-/

public section

assert_not_exists Field

variable {G : Type*} [Group G]
variable {A : Type*} [AddGroup A]

namespace Subgroup

@[to_additive]
/-
**Subgroup.** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (K : Subgroup G) [DecidablePred (· ∈ K)] [Fintype G] : Fintype K :=
  show Fintype { g : G // g ∈ K } from inferInstance

@[to_additive]
/-
**Subgroup.** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (K : Subgroup G) [Finite G] : Finite K :=
  Subtype.finite

end Subgroup

/-!
### Conversion to/from `Additive`/`Multiplicative`
-/


namespace Subgroup

variable (H K : Subgroup G)

/-- Product of a list of elements in a subgroup is in the subgroup. -/
@[to_additive /-- Sum of a list of elements in an `AddSubgroup` is in the `AddSubgroup`. -/]
/-
**Subgroup.list_prod_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] (K : Subgroup G) {l : List G}, (∀ x ∈ l,
 x ∈ K) → l.prod ∈ K
参数：K : Subgroup G；∀ x ∈ l, x ∈ K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `list_prod_mem`：list_prod_mem {l : List M} (hl : forall x in l, x in S) :
 l.prod in S
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G

--- 原说明 ---
Product of a list of elements in a subgroup is in the subgroup.
-/
protected theorem list_prod_mem {l : List G} : (∀ x ∈ l, x ∈ K) → l.prod ∈ K :=
  list_prod_mem

/-- Product of a multiset of elements in a subgroup of a `CommGroup` is in the subgroup. -/
@[to_additive /-- Sum of a multiset of elements in an `AddSubgroup` of an `AddCommGroup` is in
the `AddSubgroup`. -/]
/-
**Subgroup.multiset_prod_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：∀ {G : Type u_3} [inst : CommGroup G] (K : Subgroup G) (g : Multiset G), (
∀ a ∈ g, a ∈ K) → g.prod ∈ K
参数：K : Subgroup G；g : Multiset G；∀ a ∈ g, a ∈ K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `multiset_prod_mem`：multiset_prod_mem {M} [CommMonoid M] [SetLike B M] [S
ubmonoidClass B M] (m : Multiset M) (hm : forall a in m, a in S) : m.prod in S
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
-/
protected theorem multiset_prod_mem {G} [CommGroup G] (K : Subgroup G) (g : Multiset G) :
    (∀ a ∈ g, a ∈ K) → g.prod ∈ K :=
  multiset_prod_mem g

@[to_additive]
/-
**Subgroup.multiset_noncommProd_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：multiset_noncommProd_mem (K : Subgroup G) (g : Multiset G) (comm) : (foral
l a in g, a in K) -> g.noncommProd comm in K
参数：K : Subgroup G；g : Multiset G；comm。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.multiset_noncommProd_mem`：multiset_noncommProd_mem (S : Submon
oid M) (m : Multiset M) (comm) (h : forall x in m, x in S) : m.noncommProd comm 
in S
-/
theorem multiset_noncommProd_mem (K : Subgroup G) (g : Multiset G) (comm) :
    (∀ a ∈ g, a ∈ K) → g.noncommProd comm ∈ K :=
  K.toSubmonoid.multiset_noncommProd_mem g comm

/-- Product of elements of a subgroup of a `CommGroup` indexed by a `Finset` is in the
    subgroup. -/
@[to_additive /-- Sum of elements in an `AddSubgroup` of an `AddCommGroup` indexed by a `Finset`
is in the `AddSubgroup`. -/]
/-
**Subgroup.prod_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：∀ {G : Type u_3} [inst : CommGroup G] (K : Subgroup G) {ι : Type u_4} {t :
 Finset ι} {f : ι → G},   (∀ c ∈ t, f c ∈ K) → ∏ c ∈ t, f c ∈ K
参数：K : Subgroup G；∀ c ∈ t, f c ∈ K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `prod_mem`：prod_mem {M : Type*} [CommMonoid M] [SetLike B M] [SubmonoidCl
ass B M] {ι : Type*} {t : Finset ι} {f : ι -> M} (h : forall c in t, f c in S)…
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
-/
protected theorem prod_mem {G : Type*} [CommGroup G] (K : Subgroup G) {ι : Type*} {t : Finset ι}
    {f : ι → G} (h : ∀ c ∈ t, f c ∈ K) : (∏ c ∈ t, f c) ∈ K :=
  prod_mem h

@[to_additive]
/-
**Subgroup.noncommProd_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：noncommProd_mem (K : Subgroup G) {ι : Type*} {t : Finset ι} {f : ι -> G} (
comm) : (forall c in t, f c in K) -> t.noncommProd f comm in K
参数：K : Subgroup G；comm。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.noncommProd_mem`：noncommProd_mem (S : Submonoid M) {ι : Type*}
 (t : Finset ι) (f : ι -> M) (comm) (h : forall c in t, f c in S) : t.noncommPro
d f comm in S
-/
theorem noncommProd_mem (K : Subgroup G) {ι : Type*} {t : Finset ι} {f : ι → G} (comm) :
    (∀ c ∈ t, f c ∈ K) → t.noncommProd f comm ∈ K :=
  K.toSubmonoid.noncommProd_mem t f comm

@[to_additive (attr := simp 1100, norm_cast)]
/-
**Subgroup.val_list_prod** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：val_list_prod (l : List H) : (l.prod : G) = (l.map Subtype.val).prod
参数：l : List H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubmonoidClass.coe_list_prod`：coe_list_prod (l : List S) : (l.prod : M) 
= (l.map (↑)).prod
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
-/
theorem val_list_prod (l : List H) : (l.prod : G) = (l.map Subtype.val).prod :=
  SubmonoidClass.coe_list_prod l

@[to_additive (attr := simp 1100, norm_cast)]
/-
**Subgroup.val_multiset_prod** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：val_multiset_prod {G} [CommGroup G] (H : Subgroup G) (m : Multiset H) : (m
.prod : G) = (m.map Subtype.val).prod
参数：H : Subgroup G；m : Multiset H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubmonoidClass.coe_multiset_prod`：coe_multiset_prod {M} [CommMonoid M] [
SetLike B M] [SubmonoidClass B M] (m : Multiset S) : (m.prod : M) = (m.map (↑)).
prod
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
-/
theorem val_multiset_prod {G} [CommGroup G] (H : Subgroup G) (m : Multiset H) :
    (m.prod : G) = (m.map Subtype.val).prod :=
  SubmonoidClass.coe_multiset_prod m

@[to_additive (attr := simp 1100, norm_cast)]
/-
**Subgroup.val_finsetProd** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：val_finsetProd {ι G} [CommGroup G] (H : Subgroup G) (f : ι -> H) (s : Fins
et ι) : ↑(∏ i in s, f i) = (∏ i in s, f i : G)
参数：H : Subgroup G；f : ι -> H；s : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubmonoidClass.coe_finsetProd`：coe_finsetProd {ι M} [CommMonoid M] [SetL
ike B M] [SubmonoidClass B M] (f : ι -> S) (s : Finset ι) : ↑(∏ i in s, f i) = (
∏ i in s, f i : M)
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
-/
theorem val_finsetProd {ι G} [CommGroup G] (H : Subgroup G) (f : ι → H) (s : Finset ι) :
    ↑(∏ i ∈ s, f i) = (∏ i ∈ s, f i : G) :=
  SubmonoidClass.coe_finsetProd f s

@[deprecated (since := "2026-04-08")]
alias _root_.AddSubgroup.val_finset_sum := _root_.AddSubgroup.val_finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias val_finset_prod := val_finsetProd

@[to_additive]
/-
**Subgroup.fintypeBot** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
形式化陈述：fintypeBot : Fintype (⊥ : Subgroup G)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance fintypeBot : Fintype (⊥ : Subgroup G) :=
  ⟨{1}, by
    rintro ⟨x, ⟨hx⟩⟩
    exact Finset.mem_singleton_self _⟩

@[to_additive]
/-
**Subgroup.card_bot** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：card_bot : Nat.card (⊥ : Subgroup G) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Fintype.card_unique`：card_unique [Unique α] [h : Fintype α] : Fintype.ca
rd α = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem card_bot : Nat.card (⊥ : Subgroup G) = 1 := by simp

@[to_additive]
/-
**Subgroup.card_top** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：card_top : Nat.card (⊤ : Subgroup G) = Nat.card G
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
-/
theorem card_top : Nat.card (⊤ : Subgroup G) = Nat.card G :=
  Nat.card_congr Subgroup.topEquiv.toEquiv

@[to_additive]
/-
**Subgroup.eq_of_le_of_card_ge** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：eq_of_le_of_card_ge {H K : Subgroup G} [Finite K] (hle : H <= K) (hcard : 
Nat.card K <= Nat.card H) : H = K
参数：hle : H <= K；hcard : Nat.card K <= Nat.card H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.Finite.eq_of_subset_of_card_le`：eq_of_subset_of_card_le (ht : t.Fini
te) (hsub : s subseteq t) (hcard : Nat.card t <= Nat.card s) : s = t
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
-/
theorem eq_of_le_of_card_ge {H K : Subgroup G} [Finite K] (hle : H ≤ K)
    (hcard : Nat.card K ≤ Nat.card H) :
    H = K :=
  SetLike.coe_injective <| Set.Finite.eq_of_subset_of_card_le (Set.toFinite _) hle hcard

@[to_additive]
/-
**Subgroup.eq_top_of_le_card** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：eq_top_of_le_card [Finite G] (h : Nat.card G <= Nat.card H) : H = ⊤
参数：h : Nat.card G <= Nat.card H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.eq_of_le_of_card_ge`：eq_of_le_of_card_ge {H K : Subgroup G} [Fi
nite K] (hle : H <= K) (hcard : Nat.card K <= Nat.card H) : H = K
· 使用定理 `Subgroup.instFiniteSubtypeMem`：∀ {G : Type u_1} [inst : Group G] (K : Su
bgroup G) [Finite G], Finite ↥K
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
-/
theorem eq_top_of_le_card [Finite G] (h : Nat.card G ≤ Nat.card H) : H = ⊤ :=
  eq_of_le_of_card_ge le_top (Nat.card_congr (Equiv.Set.univ G) ▸ h)

@[to_additive]
/-
**Subgroup.eq_top_of_card_eq** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：eq_top_of_card_eq [Finite H] (h : Nat.card H = Nat.card G) : H = ⊤
参数：h : Nat.card H = Nat.card G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.finite_of_card_ne_zero`：finite_of_card_ne_zero (h : Nat.card α != 0)
 : Finite α
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Nat.card_pos`：∀ {α : Type u_1} [Nonempty α] [Finite α], 0 < Nat.card α
· 使用定理 `One.instNonempty`：∀ {α : Type u} [One α], Nonempty α
· 使用定理 `Subgroup.eq_top_of_le_card`：eq_top_of_le_card [Finite G] (h : Nat.card G
 <= Nat.card H) : H = ⊤
· 使用定理 `Nat.le_of_eq`：∀ {n m : ℕ}, n = m → n ≤ m
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem eq_top_of_card_eq [Finite H] (h : Nat.card H = Nat.card G) : H = ⊤ := by
  have : Finite G := Nat.finite_of_card_ne_zero (h ▸ Nat.card_pos.ne')
  exact eq_top_of_le_card _ (Nat.le_of_eq h.symm)

@[to_additive (attr := simp)]
/-
**Subgroup.card_eq_iff_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：card_eq_iff_eq_top [Finite H] : Nat.card H = Nat.card G ↔ H = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.eq_top_of_card_eq`：eq_top_of_card_eq [Finite H] (h : Nat.card H
 = Nat.card G) : H = ⊤
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subgroup.card_top`：card_top : Nat.card (⊤ : Subgroup G) = Nat.card G
-/
theorem card_eq_iff_eq_top [Finite H] : Nat.card H = Nat.card G ↔ H = ⊤ :=
  Iff.intro (eq_top_of_card_eq H) (fun h ↦ by simpa only [h] using card_top)

@[to_additive]
/-
**Subgroup.eq_bot_of_card_le** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：eq_bot_of_card_le [Finite H] (h : Nat.card H <= 1) : H = ⊥
参数：h : Nat.card H <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finite.card_le_one_iff_subsingleton`：card_le_one_iff_subsingleton [Finit
e α] : Nat.card α <= 1 ↔ Subsingleton α
· 使用定理 `Subgroup.eq_bot_of_subsingleton`：eq_bot_of_subsingleton [Subsingleton H]
 : H = ⊥
-/
theorem eq_bot_of_card_le [Finite H] (h : Nat.card H ≤ 1) : H = ⊥ :=
  let _ := Finite.card_le_one_iff_subsingleton.mp h
  eq_bot_of_subsingleton H

@[to_additive]
/-
**Subgroup.eq_bot_of_card_eq** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：eq_bot_of_card_eq (h : Nat.card H = 1) : H = ⊥
参数：h : Nat.card H = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.card_eq_one_iff_unique`：card_eq_one_iff_unique : Nat.card α = 1 ↔ Su
bsingleton α ∧ Nonempty α
· 使用定理 `Subgroup.eq_bot_of_subsingleton`：eq_bot_of_subsingleton [Subsingleton H]
 : H = ⊥
-/
theorem eq_bot_of_card_eq (h : Nat.card H = 1) : H = ⊥ :=
  let _ := (Nat.card_eq_one_iff_unique.mp h).1
  eq_bot_of_subsingleton H

@[to_additive card_le_one_iff_eq_bot]
/-
**Subgroup.card_le_one_iff_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：card_le_one_iff_eq_bot [Finite H] : Nat.card H <= 1 ↔ H = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.eq_bot_of_card_le`：eq_bot_of_card_le [Finite H] (h : Nat.card H
 <= 1) : H = ⊥
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Fintype.card_unique`：card_unique [Unique α] [h : Fintype α] : Fintype.ca
rd α = 1
-/
theorem card_le_one_iff_eq_bot [Finite H] : Nat.card H ≤ 1 ↔ H = ⊥ :=
  ⟨H.eq_bot_of_card_le, fun h => by simp [h]⟩
/-
**Subgroup.eq_bot_iff_card** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G), H = ⊥ ↔ Nat.card ↥H = 
1
参数：H : Subgroup G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.card_bot`：card_bot : Nat.card (⊥ : Subgroup G) = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.eq_bot_of_card_eq`：eq_bot_of_card_eq (h : Nat.card H = 1) : H =
 ⊥
-/
@[to_additive] lemma eq_bot_iff_card : H = ⊥ ↔ Nat.card H = 1 :=
  ⟨by rintro rfl; exact card_bot, eq_bot_of_card_eq _⟩

@[to_additive one_lt_card_iff_ne_bot]
/-
**Subgroup.one_lt_card_iff_ne_bot** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：one_lt_card_iff_ne_bot [Finite H] : 1 < Nat.card H ↔ H != ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `lt_iff_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a < b 
↔ ¬b ≤ a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Subgroup.card_le_one_iff_eq_bot`：card_le_one_iff_eq_bot [Finite H] : Nat
.card H <= 1 ↔ H = ⊥
-/
theorem one_lt_card_iff_ne_bot [Finite H] : 1 < Nat.card H ↔ H ≠ ⊥ :=
  lt_iff_not_ge.trans H.card_le_one_iff_eq_bot.not

@[to_additive]
/-
**Subgroup.card_le_card_group** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：card_le_card_group [Finite G] : Nat.card H <= Nat.card G
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.card_le_card_of_injective`：card_le_card_of_injective {α : Type u} {β
 : Type v} [Finite β] (f : α -> β) (hf : Injective f) : Nat.card α <= Nat.card β
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
theorem card_le_card_group [Finite G] : Nat.card H ≤ Nat.card G :=
  Nat.card_le_card_of_injective _ Subtype.coe_injective

@[to_additive]
/-
**Subgroup.card_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：card_le_of_le {H K : Subgroup G} [Finite K] (h : H <= K) : Nat.card H <= N
at.card K
参数：h : H <= K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.card_le_card_of_injective`：card_le_card_of_injective {α : Type u} {β
 : Type v} [Finite β] (f : α -> β) (hf : Injective f) : Nat.card α <= Nat.card β
· 使用定理 `Subgroup.inclusion_injective`：inclusion_injective {H K : Subgroup G} (h 
: H <= K) : Function.Injective inclusion h
-/
theorem card_le_of_le {H K : Subgroup G} [Finite K] (h : H ≤ K) : Nat.card H ≤ Nat.card K :=
  Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective h)

@[to_additive]
/-
**Subgroup.card_map_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：card_map_of_injective {H : Type*} [Group H] {K : Subgroup G} {f : G ->* H}
 (hf : Function.Injective f) : Nat.card (map f K) = Nat.card K
参数：hf : Function.Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.card_image_of_injective`：card_image_of_injective {f : α -> β} (hf : 
Injective f) (s : Set α) : Nat.card (f '' s) = Nat.card s
-/
theorem card_map_of_injective {H : Type*} [Group H] {K : Subgroup G} {f : G →* H}
    (hf : Function.Injective f) :
    Nat.card (map f K) = Nat.card K := by
  apply Nat.card_image_of_injective hf

@[to_additive]
/-
**Subgroup.card_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：card_subtype (K : Subgroup G) (L : Subgroup K) : Nat.card (map K.subtype L
) = Nat.card L
参数：K : Subgroup G；L : Subgroup K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.card_map_of_injective`：card_map_of_injective {H : Type*} [Group
 H] {K : Subgroup G} {f : G ->* H} (hf : Function.Injective f) : Nat.card (map f
 K) = Nat.card K
· 使用引理 `Subgroup.subtype_injective`：subtype_injective (s : Subgroup G) : Functio
n.Injective s.subtype
-/
theorem card_subtype (K : Subgroup G) (L : Subgroup K) :
    Nat.card (map K.subtype L) = Nat.card L :=
  card_map_of_injective K.subtype_injective

@[to_additive]
/-
**Subgroup.card_mapSubgroup** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：card_mapSubgroup {G' : Type*} [Group G'] (e : G ≃* G') : Nat.card (e.mapSu
bgroup H) = Nat.card H
参数：e : G ≃* G'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.card_map_of_injective`：card_map_of_injective {H : Type*} [Group
 H] {K : Subgroup G} {f : G ->* H} (hf : Function.Injective f) : Nat.card (map f
 K) = Nat.card K
· 使用定理 `MulEquiv.injective`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [inst
_1 : Mul N] (e : M ≃* N), Function.Injective ⇑e
-/
theorem card_mapSubgroup {G' : Type*} [Group G'] (e : G ≃* G') :
    Nat.card (e.mapSubgroup H) = Nat.card H :=
  Subgroup.card_map_of_injective e.injective

end Subgroup

namespace Subgroup

section Pi

open Set

variable {η : Type*} {f : η → Type*} [∀ i, Group (f i)]

@[to_additive]
/-
**Subgroup.pi_mem_of_mulSingle_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：pi_mem_of_mulSingle_mem [Finite η] [DecidableEq η] {H : Subgroup (forall i
, f i)} (x : forall i, f i) (h : forall i, Pi.mulSingle i (x i) in H) : x in H
参数：forall i, f i；x : forall i, f i；h : forall i, Pi.mulSingle i (x i) in H。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.pi_mem_of_mulSingle_mem`：pi_mem_of_mulSingle_mem [Finite η] [D
ecidableEq η] {H : S} (x : Π i, f i) (h : forall i, Pi.mulSingle i (x i) in H) :
 x in H
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
-/
theorem pi_mem_of_mulSingle_mem [Finite η] [DecidableEq η] {H : Subgroup (∀ i, f i)} (x : ∀ i, f i)
    (h : ∀ i, Pi.mulSingle i (x i) ∈ H) : x ∈ H :=
  Submonoid.pi_mem_of_mulSingle_mem x h

/-- For finite index types, the `Subgroup.pi` is generated by the embeddings of the groups. -/
@[to_additive /-- For finite index types, the `Subgroup.pi` is generated by the embeddings of the
additive groups. -/]
/-
**Subgroup.pi_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：pi_le_iff [DecidableEq η] [Finite η] {H : forall i, Subgroup (f i)} {J : S
ubgroup (forall i, f i)} : pi univ H <= J ↔ forall i : η, map (MonoidHom.mulSing
le f i) (H i) <= J
参数：f i；forall i, f i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.pi_le_iff`：pi_le_iff [Finite η] [DecidableEq η] {H : Π i, Subm
onoid (f i)} {J : Submonoid (Π i, f i)} : pi univ H <= J ↔ forall i : η, map (Mo
noidHom.m…
-/
theorem pi_le_iff [DecidableEq η] [Finite η] {H : ∀ i, Subgroup (f i)} {J : Subgroup (∀ i, f i)} :
    pi univ H ≤ J ↔ ∀ i : η, map (MonoidHom.mulSingle f i) (H i) ≤ J :=
  Submonoid.pi_le_iff

@[to_additive]
/-
**Subgroup.closure_pi** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：closure_pi [Finite η] {s : Π i, Set (f i)} (hs : forall i, 1 in s i) : clo
sure (univ.pi fun i => s i) = pi univ fun i => closure (s i)
参数：f i；hs : forall i, 1 in s i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subgroup.closure_le`：closure_le : closure k <= K ↔ k subseteq K
· 使用定理 `Set.pi_subset_pi_iff`：pi_subset_pi_iff : pi s t₁ subseteq pi s t₂ ↔ (for
all i in s, t₁ i subseteq t₂ i) ∨ pi s t₁ = ∅
· 使用定理 `Subgroup.subset_closure`：subset_closure : k subseteq closure k
· 使用定理 `Subgroup.pi_le_iff`：pi_le_iff [DecidableEq η] [Finite η] {H : forall i, 
Subgroup (f i)} {J : Subgroup (forall i, f i)} : pi univ H <= J ↔ forall i : η, 
map (Mon…
· 使用定理 `GaloisConnection.l_le`：l_le {a : α} {b : β} : a <= u b -> l a <= b
· 使用定理 `Subgroup.gc_map_comap`：gc_map_comap (f : G ->* N) : GaloisConnection (ma
p f) (comap f)
· 使用定理 `Set.mem_univ_pi`：mem_univ_pi : f in pi univ t ↔ forall i, f i in t i
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Pi.mulSingle_eq_same`：mulSingle_eq_same (i : ι) (x : M i) : mulSingle i 
x i = x
· 使用引理 `Pi.mulSingle_eq_of_ne`：mulSingle_eq_of_ne {i i' : ι} (h : i' != i) (x : 
M i) : mulSingle i x i' = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem closure_pi [Finite η] {s : Π i, Set (f i)} (hs : ∀ i, 1 ∈ s i) :
    closure (univ.pi fun i => s i) = pi univ fun i => closure (s i) :=
  le_antisymm
    ((closure_le _).2 <| pi_subset_pi_iff.2 <| .inl fun _ _ => subset_closure)
    (by
      classical
      exact pi_le_iff.mpr fun i => (gc_map_comap _).l_le <| (closure_le _).2 fun _x hx =>
          subset_closure <| mem_univ_pi.mpr fun j => by
        by_cases H : j = i
        · subst H
          simpa
        · simpa [H] using hs _)

end Pi

section Normalizer

/-
**Subgroup.mem_normalizer_fintype** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：mem_normalizer_fintype {S : Set G} [Finite S] {x : G} (h : forall n, n in 
S -> x * n * x⁻¹ in S) : x in Subgroup.normalizer S
参数：h : forall n, n in S -> x * n * x⁻¹ in S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Set.eq_of_subset_of_card_le`：eq_of_subset_of_card_le {s t : Set α} [Fint
ype s] [Fintype t] (hsub : s subseteq t) (hcard : Fintype.card t <= Fintype.card
 s) : s = t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.card_image_of_injective`：card_image_of_injective (s : Set α) [Fintyp
e s] {f : α -> β} [Fintype (f '' s)] (H : Function.Injective f) : Fintype.card (
f '' s) = Fintype…
· 使用定理 `conj_injective`：conj_injective {x : α} : Function.Injective fun g : α =>
 x * g * x⁻¹
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem mem_normalizer_fintype {S : Set G} [Finite S] {x : G} (h : ∀ n, n ∈ S → x * n * x⁻¹ ∈ S) :
    x ∈ Subgroup.normalizer S := by
  have := Classical.propDecidable; cases nonempty_fintype S
  exact fun n =>
    ⟨h n, fun h₁ =>
      have heq : (fun n => x * n * x⁻¹) '' S = S :=
        Set.eq_of_subset_of_card_le (fun n ⟨y, hy⟩ => hy.2 ▸ h y hy.1)
          (by rw [Set.card_image_of_injective S conj_injective])
      have : x * n * x⁻¹ ∈ (fun n => x * n * x⁻¹) '' S := heq.symm ▸ h₁
      let ⟨y, hy⟩ := this
      conj_injective hy.2 ▸ hy.1⟩

end Normalizer

end Subgroup

namespace MonoidHom

variable {N : Type*} [Group N]

open Subgroup

@[to_additive]
/-
**MonoidHom.decidableMemRange** 是 Mathlib 中的一个实例，位于命名空间 `MonoidHom`。
形式化陈述：decidableMemRange (f : G ->* N) [Fintype G] [DecidableEq N] : DecidablePre
d (· in f.range)
参数：f : G ->* N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableMemRange (f : G →* N) [Fintype G] [DecidableEq N] : DecidablePred (· ∈ f.range) :=
  fun _ => Fintype.decidableExistsFintype

-- this instance can't go just after the definition of `mrange` because `Fintype` is
-- not imported at that stage
/-- The range of a finite monoid under a monoid homomorphism is finite.
Note: this instance can form a diamond with `Subtype.fintype` in the
presence of `Fintype N`. -/
@[to_additive /-- The range of a finite additive monoid under an additive monoid homomorphism is
finite.

Note: this instance can form a diamond with `Subtype.fintype` or `Subgroup.fintype` in the presence
of `Fintype N`. -/]
/-
**MonoidHom.fintypeMrange** 是 Mathlib 中的一个实例，位于命名空间 `MonoidHom`。
形式化陈述：fintypeMrange {M N : Type*} [Monoid M] [Monoid N] [Fintype M] [DecidableEq
 N] (f : M ->* N) : Fintype (mrange f)
参数：f : M ->* N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance fintypeMrange {M N : Type*} [Monoid M] [Monoid N] [Fintype M] [DecidableEq N]
    (f : M →* N) : Fintype (mrange f) :=
  Set.fintypeRange f

/-- The range of a finite group under a group homomorphism is finite.

Note: this instance can form a diamond with `Subtype.fintype` or `Subgroup.fintype` in the
presence of `Fintype N`. -/
@[to_additive
/-- The range of a finite additive group under an additive group homomorphism is finite.

Note: this instance can form a diamond with `Subtype.fintype` or `Subgroup.fintype` in the
presence of `Fintype N`. -/]
/-
**MonoidHom.fintypeRange** 是 Mathlib 中的一个实例，位于命名空间 `MonoidHom`。
形式化陈述：fintypeRange [Fintype G] [DecidableEq N] (f : G ->* N) : Fintype (range f)
参数：f : G ->* N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance fintypeRange [Fintype G] [DecidableEq N] (f : G →* N) : Fintype (range f) :=
  Set.fintypeRange f
/-
**MonoidHom._root_.Fintype.card_coeSort_mrange** 是 Mathlib 中的一个引理，位于命名空间 `Monoid
Hom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Fintype.card_coeSort_mrange {M N : Type*} [Monoid M] [Monoid N] [Fintype M]
    [DecidableEq N] {f : M →* N} (hf : Function.Injective f) :
    Fintype.card (mrange f) = Fintype.card M :=
  Set.card_range_of_injective hf
/-
**MonoidHom._root_.Fintype.card_coeSort_range** 是 Mathlib 中的一个引理，位于命名空间 `MonoidH
om`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Fintype.card_coeSort_range [Fintype G] [DecidableEq N] {f : G →* N}
    (hf : Function.Injective f) :
    Fintype.card (range f) = Fintype.card G :=
  Set.card_range_of_injective hf

end MonoidHom

