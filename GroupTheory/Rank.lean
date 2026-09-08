/-
Copyright (c) 2025 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.GroupTheory.Finiteness
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Rank of a group

This file defines the rank of a group, namely the minimum size of a generating set.

## TODO

Should we define `erank G : ℕ∞` the rank of a not necessarily finitely generated group `G`,
then redefine `rank G` as `(erank G).toNat`? Maybe a `Cardinal`-valued version too?
-/

@[expose] public section

open Function Group

variable {G H : Type*} [Group G] [Group H]

namespace Group

variable (G) in
/-- The minimum number of generators of a group. -/
@[to_additive /-- The minimum number of generators of an additive group. -/]
/-
**Group.rank** 是 Mathlib 中的一个定义，位于命名空间 `Group`。
形式化陈述：rank [h : FG G] : Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The minimum number of generators of a group.
-/
noncomputable def rank [h : FG G] : ℕ := @Nat.find _ (Classical.decPred _) (fg_iff'.mp h)

variable (G) in
@[to_additive]
/-
**Group.rank_spec** 是 Mathlib 中的一个引理，位于命名空间 `Group`。
形式化陈述：rank_spec [h : FG G] : exists S : Finset G, S.card = rank G ∧ .closure S =
 (⊤ : Subgroup G)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.find_spec`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n),
 p (Nat.find H)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Group.fg_iff'`：Group.fg_iff' : Group.FG G ↔ exists (n : _) (S : Finset G
), S.card = n ∧ Subgroup.closure (S : Set G) = ⊤
-/
lemma rank_spec [h : FG G] : ∃ S : Finset G, S.card = rank G ∧ .closure S = (⊤ : Subgroup G) :=
  @Nat.find_spec _ (Classical.decPred _) (fg_iff'.mp h)

@[to_additive]
/-
**Group.rank_le** 是 Mathlib 中的一个引理，位于命名空间 `Group`。
形式化陈述：rank_le [h : FG G] {S : Finset G} (hS : .closure S = (⊤ : Subgroup G)) : r
ank G <= S.card
参数：hS : .closure S = (⊤ : Subgroup G)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.find_le`：find_le {h : exists n, p n} (hn : p n) : Nat.find h <= n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Group.fg_iff'`：Group.fg_iff' : Group.FG G ↔ exists (n : _) (S : Finset G
), S.card = n ∧ Subgroup.closure (S : Set G) = ⊤
-/
lemma rank_le [h : FG G] {S : Finset G} (hS : .closure S = (⊤ : Subgroup G)) : rank G ≤ S.card :=
  @Nat.find_le _ _ (Classical.decPred _) (fg_iff'.mp h) ⟨S, rfl, hS⟩

variable (G) in
@[to_additive (attr := nontriviality)]
/-
**Group.rank_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Group`。
形式化陈述：rank_eq_zero [Subsingleton G] : rank G = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Group.fg_of_finite`：∀ {G : Type u_3} [inst : Group G] [Finite G], Group.
FG G
· 使用定理 `Finite.of_subsingleton`：Finite.of_subsingleton [Subsingleton α] (s : Set
 α) : s.Finite
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_zero_iff`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_1 : 
Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Finset.card_empty`：card_empty : #(∅ : Finset α) = 0
· 使用引理 `Group.rank_le`：rank_le [h : FG G] {S : Finset G} (hS : .closure S = (⊤ :
 Subgroup G)) : rank G <= S.card
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
theorem rank_eq_zero [Subsingleton G] : rank G = 0 := by
  rw [← le_zero_iff, ← Finset.card_empty]
  exact rank_le (Subsingleton.elim _ _)

@[to_additive]
/-
**Group.rank_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Group`。
形式化陈述：rank_eq_zero_iff [FG G] : rank G = 0 ↔ Subsingleton G
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Group.rank_spec`：rank_spec [h : FG G] : exists S : Finset G, S.card = ra
nk G ∧ .closure S = (⊤ : Subgroup G)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_eq_zero`：∀ {α : Type u_1} {s : Finset α}, s.card = 0 ↔ s = ∅
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
· 使用定理 `Subgroup.closure_empty`：closure_empty : closure (∅ : Set G) = ⊥
· 使用定理 `Group.rank_eq_zero`：rank_eq_zero [Subsingleton G] : rank G = 0
-/
theorem rank_eq_zero_iff [FG G] : rank G = 0 ↔ Subsingleton G := by
  refine ⟨fun h ↦ ?_, fun _ ↦ rank_eq_zero G⟩
  obtain ⟨s, hs, hs'⟩ := rank_spec G
  rw [h, Finset.card_eq_zero] at hs
  simpa [hs, subsingleton_iff_bot_eq_top] using hs'

variable (G) in
@[to_additive]
/-
**Group.rank_pos** 是 Mathlib 中的一个定理，位于命名空间 `Group`。
形式化陈述：rank_pos [Nontrivial G] [FG G] : 0 < rank G
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Group.rank_eq_zero_iff`：rank_eq_zero_iff [FG G] : rank G = 0 ↔ Subsingle
ton G
· 使用引理 `not_subsingleton_iff_nontrivial`：not_subsingleton_iff_nontrivial : ¬Subs
ingleton α ↔ Nontrivial α
-/
theorem rank_pos [Nontrivial G] [FG G] : 0 < rank G := by
  rwa [pos_iff_ne_zero, ne_eq, rank_eq_zero_iff, not_subsingleton_iff_nontrivial]

-- TODO: Prove monotonicity of `rank` along injective homomorphisms of abelian groups. This could
-- potentially be deduced from a (yet unproved) analogous statement for `Submodule.spanRank`.
@[to_additive]
/-
**Group.rank_le_of_surjective** 是 Mathlib 中的一个引理，位于命名空间 `Group`。
形式化陈述：rank_le_of_surjective [FG G] [FG H] (f : G ->* H) (hf : Surjective f) : ra
nk H <= rank G
参数：f : G ->* H；hf : Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Group.rank_spec`：rank_spec [h : FG G] : exists S : Finset G, S.card = ra
nk G ∧ .closure S = (⊤ : Subgroup G)
· 使用引理 `Group.rank_le`：rank_le [h : FG G] {S : Finset G} (hS : .closure S = (⊤ :
 Subgroup G)) : rank G <= S.card
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonoidHom.map_closure`：map_closure (f : G ->* N) (s : Set G) : (closure 
s).map f = closure (f '' s)
· 使用定理 `Subgroup.map_top_of_surjective`：map_top_of_surjective (f : G ->* N) (h :
 Function.Surjective f) : Subgroup.map f ⊤ = ⊤
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Finset.card_image_le`：card_image_le [DecidableEq β] : #(s.image f) <= #s
-/
lemma rank_le_of_surjective [FG G] [FG H] (f : G →* H) (hf : Surjective f) : rank H ≤ rank G := by
  classical
  obtain ⟨S, hS1, hS2⟩ := rank_spec G
  trans (S.image f).card
  · apply rank_le
    rw [Finset.coe_image, ← MonoidHom.map_closure, hS2, Subgroup.map_top_of_surjective f hf]
  · exact Finset.card_image_le.trans_eq hS1

@[to_additive]
/-
**Group.rank_range_le** 是 Mathlib 中的一个引理，位于命名空间 `Group`。
形式化陈述：rank_range_le [FG G] {f : G ->* H} : rank f.range <= rank G
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Group.rank_le_of_surjective`：rank_le_of_surjective [FG G] [FG H] (f : G 
->* H) (hf : Surjective f) : rank H <= rank G
· 使用定理 `MonoidHom.rangeRestrict_surjective`：rangeRestrict_surjective (f : G ->* 
N) : Function.Surjective f.rangeRestrict
-/
lemma rank_range_le [FG G] {f : G →* H} : rank f.range ≤ rank G :=
  rank_le_of_surjective f.rangeRestrict f.rangeRestrict_surjective

@[to_additive]
/-
**Group.rank_congr** 是 Mathlib 中的一个引理，位于命名空间 `Group`。
形式化陈述：rank_congr [FG G] [FG H] (e : G ≃* H) : rank G = rank H
参数：e : G ≃* H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `Group.rank_le_of_surjective`：rank_le_of_surjective [FG G] [FG H] (f : G 
->* H) (hf : Surjective f) : rank H <= rank G
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `MulEquiv.surjective`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [ins
t_1 : Mul N] (e : M ≃* N), Function.Surjective ⇑e
-/
lemma rank_congr [FG G] [FG H] (e : G ≃* H) : rank G = rank H :=
  le_antisymm (rank_le_of_surjective e.symm e.symm.surjective)
    (rank_le_of_surjective e e.surjective)

end Group

namespace Subgroup

@[to_additive]
/-
**Subgroup.rank_congr** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：rank_congr {H K : Subgroup G} [Group.FG H] [Group.FG K] (h : H = K) : rank
 H = rank K
参数：h : H = K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma rank_congr {H K : Subgroup G} [Group.FG H] [Group.FG K] (h : H = K) : rank H = rank K := by
  subst h; rfl

@[to_additive]
/-
**Subgroup.rank_closure_finset_le_card** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：rank_closure_finset_le_card (s : Finset G) : rank (closure (s : Set G)) <=
 s.card
参数：s : Finset G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_preimage`：coe_preimage {f : α -> β} (s : Finset β) (hf : Set.
InjOn f (f ⁻¹' ↑s)) : (↑(preimage s f hf) : Set α) = f ⁻¹' ↑s
· 使用定理 `Subgroup.closure_preimage_eq_top`：closure_preimage_eq_top (s : Set G) : 
closure ((closure s).subtype ⁻¹' s) = ⊤
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Group.rank_le`：rank_le [h : FG G] {S : Finset G} (hS : .closure S = (⊤ :
 Subgroup G)) : rank G <= S.card
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_image_of_injOn`：card_image_of_injOn [DecidableEq β] (H : Set
.InjOn f s) : #(s.image f) = #s
· 使用定理 `Finset.image_preimage`：image_preimage [DecidableEq β] (f : α -> β) (s : 
Finset β) [forall x, Decidable (x in Set.range f)] (hf : Set.InjOn f (f ⁻¹' ↑s))
 : image f …
· 使用定理 `Finset.card_filter_le`：card_filter_le (s : Finset α) (p : α -> Prop) [De
cidablePred p] : #(s.filter p) <= #s
-/
lemma rank_closure_finset_le_card (s : Finset G) : rank (closure (s : Set G)) ≤ s.card := by
  classical
  let t : Finset (closure (s : Set G)) := s.preimage Subtype.val Subtype.coe_injective.injOn
  have ht : closure (t : Set (closure (s : Set G))) = ⊤ := by
    rw [Finset.coe_preimage]
    exact closure_preimage_eq_top (s : Set G)
  apply (rank_le ht).trans
  suffices H : Set.InjOn Subtype.val (t : Set (closure (s : Set G))) by
    rw [← Finset.card_image_of_injOn H, Finset.image_preimage]
    apply Finset.card_filter_le
  apply Subtype.coe_injective.injOn

@[to_additive]
/-
**Subgroup.rank_closure_finite_le_nat_card** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：rank_closure_finite_le_nat_card (s : Set G) [Finite s] : rank (closure s) 
<= Nat.card s
参数：s : Set G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.toFinset_card`：toFinset_card {α : Type*} (s : Set α) [Fintype s] : s
.toFinset.card = Fintype.card s
· 使用引理 `Subgroup.rank_congr`：rank_congr {H K : Subgroup G} [Group.FG H] [Group.F
G K] (h : H = K) : rank H = rank K
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Set.coe_toFinset`：coe_toFinset (s : Set α) [Fintype s] : (↑s.toFinset : 
Set α) = s
· 使用引理 `Subgroup.rank_closure_finset_le_card`：rank_closure_finset_le_card (s : F
inset G) : rank (closure (s : Set G)) <= s.card
-/
lemma rank_closure_finite_le_nat_card (s : Set G) [Finite s] : rank (closure s) ≤ Nat.card s := by
  have := Fintype.ofFinite s
  rw [Nat.card_eq_fintype_card, ← s.toFinset_card, ← rank_congr (congr_arg _ s.coe_toFinset)]
  exact rank_closure_finset_le_card s.toFinset
/-
**Subgroup.nat_card_centralizer_nat_card_stabilizer** 是 Mathlib 中的一个引理，位于命名空间 `S
ubgroup`。
形式化陈述：nat_card_centralizer_nat_card_stabilizer (g : G) : Nat.card (centralizer {
g}) = Nat.card (MulAction.stabilizer (ConjAct G) g)
参数：g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.centralizer_eq_comap_stabilizer`：∀ {G : Type u_3} [inst : Group
 G] (g : G),   Subgroup.centralizer {g} = Subgroup.comap ConjAct.toConjAct.toMon
oidHom (MulAction.stabilizer (…
-/
lemma nat_card_centralizer_nat_card_stabilizer (g : G) :
    Nat.card (centralizer {g}) = Nat.card (MulAction.stabilizer (ConjAct G) g) := by
  rw [centralizer_eq_comap_stabilizer]; rfl

end Subgroup

