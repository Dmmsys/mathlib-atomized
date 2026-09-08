/-
Copyright (c) 2021 Jordan Brown, Thomas Browning, Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jordan Brown, Thomas Browning, Patrick Lutz
-/
module

public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Rank
public import Mathlib.GroupTheory.Index

/-!
The commutator of a finite direct product is contained in the direct product of the commutators.
-/

public section

variable {G : Type*} [Group G]

namespace Subgroup

/-- The commutator of a finite direct product is contained in the direct product of the commutators.
-/
@[to_additive /-- The commutator of a finite direct product is contained in the direct product of
the commutators. -/]
/-
**Subgroup.commutator_pi_pi_of_finite** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：commutator_pi_pi_of_finite {η : Type*} [Finite η] {Gs : η -> Type*} [foral
l i, Group (Gs i)] (H K : forall i, Subgroup (Gs i)) : ⁅Subgroup.pi Set.univ H, 
Subgroup.pi Set.univ K⁆ = Subgroup.pi Set.univ fun i => ⁅H i, K i⁆
参数：Gs i；H K : forall i, Subgroup (Gs i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Subgroup.commutator_pi_pi_le`：commutator_pi_pi_le {η : Type*} {Gs : η ->
 Type*} [forall i, Group (Gs i)] (H K : forall i, Subgroup (Gs i)) : ⁅Subgroup.p
i Set.univ H, Subg…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.pi_le_iff`：pi_le_iff [DecidableEq η] [Finite η] {H : forall i, 
Subgroup (f i)} {J : Subgroup (forall i, f i)} : pi univ H <= J ↔ forall i : η, 
map (Mon…
· 使用定理 `Subgroup.map_commutator`：map_commutator (f : G ->* G') : map f ⁅H₁, H₂⁆ 
= ⁅map f H₁, map f H₂⁆
· 使用定理 `Subgroup.commutator_mono`：commutator_mono (h₁ : H₁ <= K₁) (h₂ : H₂ <= K₂
) : ⁅H₁, H₂⁆ <= ⁅K₁, K₂⁆
· 使用定理 `Subgroup.le_pi_iff`：le_pi_iff {I : Set η} {H : forall i, Subgroup (f i)}
 {J : Subgroup (forall i, f i)} : J <= pi I H ↔ forall i in I, J <= comap (Pi.ev
alMonoid…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Pi.evalMonoidHom_apply`：∀ {I : Type u} (f : I → Type v) [inst : (i : I) 
→ MulOneClass (f i)] (i : I) (g : (i : I) → f i),   (Pi.evalMonoidHom f i) g = g
 i
· 使用引理 `Pi.mulSingle_eq_same`：mulSingle_eq_same (i : ι) (x : M i) : mulSingle i 
x i = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `Pi.mulSingle_eq_of_ne`：mulSingle_eq_of_ne {i i' : ι} (h : i' != i) (x : 
M i) : mulSingle i x i' = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
-/
theorem commutator_pi_pi_of_finite {η : Type*} [Finite η] {Gs : η → Type*} [∀ i, Group (Gs i)]
    (H K : ∀ i, Subgroup (Gs i)) : ⁅Subgroup.pi Set.univ H, Subgroup.pi Set.univ K⁆ =
    Subgroup.pi Set.univ fun i => ⁅H i, K i⁆ := by
  classical
    apply le_antisymm (commutator_pi_pi_le H K)
    rw [pi_le_iff]
    intro i hi
    rw [map_commutator]
    apply commutator_mono <;>
      · rw [le_pi_iff]
        intro j _hj
        rintro _ ⟨x, hx, rfl⟩
        by_cases h : j = i
        · subst h
          simpa using hx
        · simp [h, one_mem]

variable [Finite (commutatorSet G)]
/-
**Subgroup.** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Group.FG (_root_.commutator G) := by
  rw [commutator_eq_closure]; apply Group.closure_finite_fg

variable (G) in
/-
**Subgroup.rank_commutator_le_card** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：rank_commutator_le_card : Group.rank (_root_.commutator G) <= Nat.card (co
mmutatorSet G)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.instFGSubtypeMemCommutator`：∀ {G : Type u_1} [inst : Group G] [
Finite ↑(commutatorSet G)], Group.FG ↥(commutator G)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Subgroup.rank_congr`：rank_congr {H K : Subgroup G} [Group.FG H] [Group.F
G K] (h : H = K) : rank H = rank K
· 使用引理 `commutator_eq_closure`：commutator_eq_closure : commutator G = Subgroup.c
losure (commutatorSet G)
· 使用引理 `Subgroup.rank_closure_finite_le_nat_card`：rank_closure_finite_le_nat_car
d (s : Set G) [Finite s] : rank (closure s) <= Nat.card s
-/
lemma rank_commutator_le_card : Group.rank (_root_.commutator G) ≤ Nat.card (commutatorSet G) := by
  rw [Subgroup.rank_congr (commutator_eq_closure G)]
  apply Subgroup.rank_closure_finite_le_nat_card

variable [Group.FG G]
/-
**Subgroup.finiteIndex_center** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
形式化陈述：finiteIndex_center : FiniteIndex (center G)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `Group.rank_spec`：rank_spec [h : FG G] : exists S : Finset G, S.card = ra
nk G ∧ .closure S = (⊤ : Subgroup G)
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Finite.card_eq_zero_of_embedding`：card_eq_zero_of_embedding [Nonempty α]
 (f : α ↪ β) (h : Nat.card α = 0) : Nat.card β = 0
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Finite.card_pos`：Finite.card_pos [Finite α] [h : Nonempty α] : 0 < Nat.c
ard α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Pi.instNonempty`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Nonempty (β
 a)], Nonempty ((a : α) → β a)
· 使用定理 `instNonemptyElemCommutatorSet`：∀ (G : Type u_1) [inst : Group G], Nonemp
ty ↑(commutatorSet G)
-/
instance finiteIndex_center : FiniteIndex (center G) := by
  obtain ⟨S, -, hS⟩ := Group.rank_spec G
  exact ⟨mt (Finite.card_eq_zero_of_embedding (quotientCenterEmbedding hS)) Finite.card_pos.ne'⟩

variable (G) in
/-
**Subgroup.index_center_le_pow** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：index_center_le_pow : (center G).index <= Nat.card (commutatorSet G) ^ Gro
up.rank G
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Group.rank_spec`：rank_spec [h : FG G] : exists S : Finset G, S.card = ra
nk G ∧ .closure S = (⊤ : Subgroup G)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.card_coe`：Fintype.card_coe (s : Finset α) [Fintype s] : Fintype.
card s = #s
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Finset.coe_sort_coe`：coe_sort_coe (s : Finset α) : ((s : Set α) : Sort _
) = s
· 使用定理 `Nat.card_fun`：card_fun [Finite α] : Nat.card (α -> β) = Nat.card β ^ Nat
.card α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Finite.card_le_of_embedding`：card_le_of_embedding [Finite β] (f : α ↪ β)
 : Nat.card α <= Nat.card β
-/
lemma index_center_le_pow : (center G).index ≤ Nat.card (commutatorSet G) ^ Group.rank G := by
  obtain ⟨S, hS1, hS2⟩ := Group.rank_spec G
  rw [← hS1, ← Fintype.card_coe, ← Nat.card_eq_fintype_card, ← Finset.coe_sort_coe, ← Nat.card_fun]
  exact Finite.card_le_of_embedding (quotientCenterEmbedding hS2)

end Subgroup

section commutatorRepresentatives

open Subgroup

/-
**card_commutatorSet_closureCommutatorRepresentatives** 是 Mathlib 中的一个引理，位于命名空间 
``。
形式化陈述：card_commutatorSet_closureCommutatorRepresentatives : Nat.card (commutator
Set (closureCommutatorRepresentatives G)) = Nat.card (commutatorSet G)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `image_commutatorSet_closureCommutatorRepresentatives`：image_commutatorSe
t_closureCommutatorRepresentatives : (closureCommutatorRepresentatives G).subtyp
e '' commutatorSet (closureCommutatorRepre…
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
· 使用引理 `Subgroup.subtype_injective`：subtype_injective (s : Subgroup G) : Functio
n.Injective s.subtype
-/
lemma card_commutatorSet_closureCommutatorRepresentatives :
    Nat.card (commutatorSet (closureCommutatorRepresentatives G)) = Nat.card (commutatorSet G) := by
  rw [← image_commutatorSet_closureCommutatorRepresentatives G]
  exact Nat.card_congr (Equiv.Set.image _ _ (subtype_injective _))
/-
**card_commutator_closureCommutatorRepresentatives** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：card_commutator_closureCommutatorRepresentatives : Nat.card (commutator (c
losureCommutatorRepresentatives G)) = Nat.card (commutator G)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `commutator_eq_closure`：commutator_eq_closure : commutator G = Subgroup.c
losure (commutatorSet G)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `image_commutatorSet_closureCommutatorRepresentatives`：image_commutatorSe
t_closureCommutatorRepresentatives : (closureCommutatorRepresentatives G).subtyp
e '' commutatorSet (closureCommutatorRepre…
· 使用定理 `MonoidHom.map_closure`：map_closure (f : G ->* N) (s : Set G) : (closure 
s).map f = closure (f '' s)
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
· 使用引理 `Subgroup.subtype_injective`：subtype_injective (s : Subgroup G) : Functio
n.Injective s.subtype
-/
lemma card_commutator_closureCommutatorRepresentatives :
    Nat.card (commutator (closureCommutatorRepresentatives G)) = Nat.card (commutator G) := by
  rw [commutator_eq_closure G, ← image_commutatorSet_closureCommutatorRepresentatives, ←
    MonoidHom.map_closure, ← commutator_eq_closure]
  exact Nat.card_congr (Equiv.Set.image _ _ (subtype_injective _))

variable [Finite (commutatorSet G)]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Finite (commutatorRepresentatives G) := Set.finite_coe_iff.mpr (Set.finite_range _)
/-
**closureCommutatorRepresentatives_fg** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：closureCommutatorRepresentatives_fg : Group.FG (closureCommutatorRepresent
atives G)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `instFiniteElemProdCommutatorRepresentatives`：∀ {G : Type u_1} [inst : Gr
oup G] [Finite ↑(commutatorSet G)], Finite ↑(commutatorRepresentatives G)
-/
instance closureCommutatorRepresentatives_fg : Group.FG (closureCommutatorRepresentatives G) :=
  Group.closure_finite_fg _

variable (G) in
/-
**rank_closureCommutatorRepresentatives_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：rank_closureCommutatorRepresentatives_le : Group.rank (closureCommutatorRe
presentatives G) <= 2 * Nat.card (commutatorSet G)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `instFiniteElemProdCommutatorRepresentatives`：∀ {G : Type u_1} [inst : Gr
oup G] [Finite ↑(commutatorSet G)], Finite ↑(commutatorRepresentatives G)
· 使用引理 `Subgroup.rank_closure_finite_le_nat_card`：rank_closure_finite_le_nat_car
d (s : Set G) [Finite s] : rank (closure s) <= Nat.card s
· 使用定理 `Set.card_union_le`：card_union_le (s t : Set α) : Nat.card (↥(s union t))
 <= Nat.card s + Nat.card t
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Finite.card_image_le`：card_image_le {s : Set α} [Finite s] (f : α -> β) 
: Nat.card (f '' s) <= Nat.card s
· 使用定理 `Finite.card_range_le`：card_range_le [Finite α] (f : α -> β) : Nat.card (
Set.range f) <= Nat.card α
-/
lemma rank_closureCommutatorRepresentatives_le :
    Group.rank (closureCommutatorRepresentatives G) ≤ 2 * Nat.card (commutatorSet G) := by
  rw [two_mul]
  exact
    (Subgroup.rank_closure_finite_le_nat_card _).trans
      ((Set.card_union_le _ _).trans
        (add_le_add ((Finite.card_image_le _).trans (Finite.card_range_le _))
          ((Finite.card_image_le _).trans (Finite.card_range_le _))))
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Finite (commutatorSet (closureCommutatorRepresentatives G)) := by
  apply Nat.finite_of_card_ne_zero
  rw [card_commutatorSet_closureCommutatorRepresentatives]
  exact Finite.card_pos.ne'

end commutatorRepresentatives

