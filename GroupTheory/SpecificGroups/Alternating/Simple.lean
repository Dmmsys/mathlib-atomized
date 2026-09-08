/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module


public import Mathlib.GroupTheory.GroupAction.Iwasawa
public import Mathlib.GroupTheory.GroupAction.SubMulAction.Combination
public import Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour

/-! # The alternating group is simple

## Main results

* `Equiv.Perm.alternatingGroup_le_of_normal`:
  If `α` has at least 5 elements, then a nontrivial normal subgroup
  of `Equiv.Perm α` contains the alternating group.

* `alternatingGroup.normal_subgroup_eq_bot_or_eq_top`:
  If `α` has at least 5 elements, then a nontrivial normal subgroup of `alternatingGroup` is `⊤`.

* `alternatingGroup.isSimpleGroup`:
  If `α` has at least 5 elements, then `alternatingGroup α` is a simple group.

## Main definitions

The proofs of the above results follow from the Iwasawa criterion
applied to the following Iwasawa structures. Their definitions are similar:
the groups `Equiv.Perm α` and `alternatingGroup α` act on `α` hence
they act on `Set.powersetCard α n`, for any natural number `n`.
For `n = 2`, this gives an Iwaswa structure of `Equiv.Perm α`,
for `n = 3` or `n = 4`, this gives an Iwasawa structure of `alternatingGroup α`.

* `Equiv.Perm.iwasawaStructure_two`:
  the natural `IwasawaStructure` of `Equiv.Perm α` acting on `Set.powersetCard α 2`.
  Its commutative subgroups consist of the permutations with support in a given element
  of `Set.powersetCard α 2`. They are cyclic of order 2.

* `alternatingGroup.iwasawaStructure_three`:
  the natural `IwasawaStructure` of `alternatingGroup α` acting on `Set.powersetCard α 3`.

  Its commutative subgroups consist of the permutations with support
  in a given element of `Set.powersetCard α 2`. They are cyclic of order 3.

* `alternatingGroup.iwasawaStructure_four`:
  the natural `IwasawaStructure` of `alternatingGroup α` acting on `Set.powersetCard α 4`

  Its commutative subgroups consist of the permutations of cycleType (2, 2) with support
  in a given element of `Set.powersetCard α 2`. They have order 4 and exponent 2 (`IsKleinFour`).

## TODO

This file contains one uncomfortable use of `convert`: on line 78, to identify `MulAut.conj`
and `ConjAct.toConjAct`.

-/

@[expose] public section

open scoped Pointwise

open MulAction Equiv.Perm Equiv Set.powersetCard Subgroup

namespace Equiv.Perm

variable {α : Type*} [Finite α] [DecidableEq α]

set_option backward.isDefEq.respectTransparency.types false in
/-- The Iwasawa structure of `Perm α` acting on `Set.powersetCard α 2`. -/
/-
**Equiv.Perm.iwasawaStructure_two** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Perm`。
形式化陈述：iwasawaStructure_two [forall s : Set α, DecidablePred fun x => x in s] : I
wasawaStructure (Perm α) (Set.powersetCard α 2) where T s
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Iwasawa structure of `Perm α` acting on `Set.powersetCard α 2`.
-/
def iwasawaStructure_two [∀ s : Set α, DecidablePred fun x ↦ x ∈ s] :
    IwasawaStructure (Perm α) (Set.powersetCard α 2) where
  T s := (ofSubtype : Perm (s : Set α) →* Perm α).range
  is_comm s := by
    have : IsMulCommutative (Perm s) := isMulCommutative_iff_card_le_two.mpr (by simp)
    infer_instance
  is_conj g s := by
    convert! (conj_smul_range_ofSubtype g s).symm
  is_generator := by
    rw [eq_top_iff, ← Equiv.Perm.closure_isSwap, Subgroup.closure_le]
    rintro g ⟨a, b, hab, rfl⟩
    apply Subgroup.mem_iSup_of_mem ⟨{a, b}, Finset.card_pair hab⟩
    exact ⟨swap ⟨a, by simp⟩ ⟨b, by simp⟩, Equiv.Perm.ofSubtype_swap_eq _ _⟩

/-- If `α` has at least 5 elements, then any nontrivial
normal subgroup of `Equiv.Perm α` contains `alternatingGroup α`. -/
/-
**Equiv.Perm.alternatingGroup_le_of_normal** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm
`。
形式化陈述：alternatingGroup_le_of_normal {α : Type*} [DecidableEq α] [Fintype α] (hα 
: 5 <= Nat.card α) {N : Subgroup (Perm α)} [N.Normal] (ntN : Nontrivial N) : alt
ernatingGroup α <= N
参数：hα : 5 <= Nat.card α；Perm α；ntN : Nontrivial N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `alternatingGroup.commutator_perm_eq`：alternatingGroup.commutator_perm_eq
 (h5 : 5 <= Nat.card α) : commutator (Perm α) = alternatingGroup α
· 使用定理 `Set.powersetCard.isPreprimitive_perm`：isPreprimitive_perm {n : Nat} (h_o
ne_le : 1 <= n) (hn : n < Nat.card α) (hα : Nat.card α != 2 * n) : IsPreprimitiv
e (Perm α) (powersetCard α…
· 使用定理 `MulAction.IwasawaStructure.commutator_le`：commutator_le (IwaS : IwasawaS
tructure M α) [IsQuasiPreprimitive M α] (N : Subgroup M) [nN : N.Normal] (hNX : 
MulAction.fixedPoints N α != .…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `MulAction.IsPreprimitive.isQuasiPreprimitive`：∀ {M : Type u_3} [inst : G
roup M] {α : Type u_4} [inst_1 : MulAction M α] [MulAction.IsPreprimitive M α], 
  MulAction.IsQuasiPreprimitive M …
· 使用定理 `Set.powersetCard.fixedPoints_ne_univ_of_faithfulSMul`：fixedPoints_ne_uni
v_of_faithfulSMul [Nontrivial G] [FaithfulSMul G α] {n : Nat} (hn : 0 < n) (hn' 
: n < Nat.card α) : fixedPoints G (powerse…
· 使用定理 `Subgroup.instFaithfulSMulSubtypeMem`：∀ {G : Type u_1} {α : Type u_2} [in
st : Group G] [inst_1 : MulAction G α] [FaithfulSMul G α] (S : Subgroup G),   Fa
ithfulSMul (↥S) α
· 使用定理 `Mathlib.Meta.NormNum.isNat_lt_true`：∀ {α : Type u_1} [inst : Semiring α]
 [inst_1 : PartialOrder α] [IsOrderedRing α] [CharZero α] {a b : α} {a' b' : ℕ},
   Mathlib.Meta.NormNum.…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n

--- 原说明 ---
If `α` has at least 5 elements, then any nontrivial
normal subgroup of `Equiv.Perm α` contains `alternatingGroup α`.
-/
theorem alternatingGroup_le_of_normal
    {α : Type*} [DecidableEq α] [Fintype α] (hα : 5 ≤ Nat.card α)
    {N : Subgroup (Perm α)} [N.Normal] (ntN : Nontrivial N) :
    alternatingGroup α ≤ N := by
  rw [← alternatingGroup.commutator_perm_eq hα]
  have : IsPreprimitive (Perm α) (Set.powersetCard α 2) := by
    apply Set.powersetCard.isPreprimitive_perm <;> grind
  classical
  apply iwasawaStructure_two.commutator_le
  exact fixedPoints_ne_univ_of_faithfulSMul (by norm_num) (by grind)

end Equiv.Perm

namespace alternatingGroup

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- The Iwasawa structure of `alternatingGroup α` acting on `Set.powersetCard α 3`. -/
/-
**alternatingGroup.iwasawaStructure_three** 是 Mathlib 中的一个定义，位于命名空间 `alternating
Group`。
形式化陈述：iwasawaStructure_three : IwasawaStructure (alternatingGroup α) (Set.powers
etCard α 3) where T s
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Iwasawa structure of `alternatingGroup α` acting on `Set.powersetCard α 3`.
-/
def iwasawaStructure_three : IwasawaStructure (alternatingGroup α) (Set.powersetCard α 3) where
  T s := (alternatingGroup.ofSubtype s).range
  is_comm s := by
    have : IsMulCommutative (alternatingGroup s) := isMulCommutative_of_card_le_three (by simp)
    infer_instance
  is_conj g s := (conj_smul_range_ofSubtype s g).symm
  is_generator := by
    rw [eq_top_iff, ← closure_isThreeCycles_eq_top, Subgroup.closure_le]
    intro g hg
    apply Subgroup.mem_iSup_of_mem ⟨(g : Perm α).support, hg.card_support⟩
    rw [mem_range_ofSubtype_iff]

/-- If `α` has at least 5 elements, but not 6,
then the only nontrivial normal subgroup of `alternatingGroup α`
is `⊤`. -/
/-
**alternatingGroup.normal_subgroup_eq_bot_or_eq_top_of_card_ne_six** 是 Mathlib 中
的一个定理，位于命名空间 `alternatingGroup`。
形式化陈述：normal_subgroup_eq_bot_or_eq_top_of_card_ne_six (hα : 5 <= Nat.card α) (hα
' : Nat.card α != 6) {N : Subgroup (alternatingGroup α)} [N.Normal] : N = ⊥ ∨ N 
= ⊤
参数：hα : 5 <= Nat.card α；hα' : Nat.card α != 6；alternatingGroup α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Subgroup.nontrivial_iff_ne_bot`：nontrivial_iff_ne_bot (H : Subgroup G) :
 Nontrivial H ↔ H != ⊥
· 使用定理 `Set.powersetCard.isPreprimitive_alternatingGroup`：isPreprimitive_alterna
tingGroup [Fintype α] {n : Nat} (h_three_le : 3 <= n) (hn : n < Nat.card α) (hα 
: Nat.card α != 2 * n) : IsPreprimitiv…
· 使用定理 `Mathlib.Meta.NormNum.isNat_le_true`：∀ {α : Type u_1} [inst : Semiring α]
 [inst_1 : PartialOrder α] [IsOrderedRing α] {a b : α} {a' b' : ℕ},   Mathlib.Me
ta.NormNum.IsNat a a' → …
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Mathlib.Meta.NormNum.isNat_lt_true`：∀ {α : Type u_1} [inst : Semiring α]
 [inst_1 : PartialOrder α] [IsOrderedRing α] [CharZero α] {a b : α} {a' b' : ℕ},
   Mathlib.Meta.NormNum.…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `commutator_alternatingGroup_eq_top`：commutator_alternatingGroup_eq_top (
h5 : 5 <= Nat.card α) : commutator (alternatingGroup α) = ⊤
· 使用定理 `MulAction.IwasawaStructure.commutator_le`：commutator_le (IwaS : IwasawaS
tructure M α) [IsQuasiPreprimitive M α] (N : Subgroup M) [nN : N.Normal] (hNX : 
MulAction.fixedPoints N α != .…
· 使用定理 `MulAction.IsPreprimitive.isQuasiPreprimitive`：∀ {M : Type u_3} [inst : G
roup M] {α : Type u_4} [inst_1 : MulAction M α] [MulAction.IsPreprimitive M α], 
  MulAction.IsQuasiPreprimitive M …
· 使用定理 `Set.powersetCard.fixedPoints_ne_univ_of_faithfulSMul`：fixedPoints_ne_uni
v_of_faithfulSMul [Nontrivial G] [FaithfulSMul G α] {n : Nat} (hn : 0 < n) (hn' 
: n < Nat.card α) : fixedPoints G (powerse…
· 使用定理 `Subgroup.instFaithfulSMulSubtypeMem`：∀ {G : Type u_1} {α : Type u_2} [in
st : Group G] [inst_1 : MulAction G α] [FaithfulSMul G α] (S : Subgroup G),   Fa
ithfulSMul (↥S) α

--- 原说明 ---
If `α` has at least 5 elements, but not 6,
then the only nontrivial normal subgroup of `alternatingGroup α`
is `⊤`.
-/
theorem normal_subgroup_eq_bot_or_eq_top_of_card_ne_six
    (hα : 5 ≤ Nat.card α) (hα' : Nat.card α ≠ 6)
    {N : Subgroup (alternatingGroup α)} [N.Normal] :
    N = ⊥ ∨ N = ⊤ := by
  rw [or_iff_not_imp_left, ← ne_eq, ← Subgroup.nontrivial_iff_ne_bot]
  intro hN
  have : IsPreprimitive (alternatingGroup α) (Set.powersetCard α 3) := by
    refine Set.powersetCard.isPreprimitive_alternatingGroup (by norm_num) ?_ ?_
    · exact lt_of_lt_of_le (by norm_num) hα
    · simpa using hα'
  rw [eq_top_iff, ← commutator_alternatingGroup_eq_top (by simpa using hα)]
  apply iwasawaStructure_three.commutator_le
  exact fixedPoints_ne_univ_of_faithfulSMul (by norm_num) (by grind)
/-
**alternatingGroup.mem_map_kleinFour_ofSubtype** 是 Mathlib 中的一个定理，位于命名空间 `altern
atingGroup`。
形式化陈述：mem_map_kleinFour_ofSubtype {s : Finset α} (hs : s.card = 4) (k : alternat
ingGroup α) : k in (kleinFour s).map (ofSubtype s) ↔ (k : Perm α).support subset
eq s ∧ ((k : Perm α) = 1 ∨ (k : Perm α).cycleType = {2, 2})
参数：hs : s.card = 4；k : alternatingGroup α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Fintype.card_coe`：Fintype.card_coe (s : Finset α) [Fintype s] : Fintype.
card s = #s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `alternatingGroup.mem_range_ofSubtype_iff`：mem_range_ofSubtype_iff (s : F
inset α) (k : alternatingGroup α) : k in (ofSubtype s).range ↔ (k : Perm α).supp
ort subseteq s
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `alternatingGroup.coe_kleinFour_of_card_eq_four`：coe_kleinFour_of_card_eq
_four (hα4 : Nat.card α = 4) : (kleinFour α : Set (alternatingGroup α)) = {1} un
ion {g : alternatingGroup α | (g : E…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `alternatingGroup.coe_ofSubtype`：coe_ofSubtype (s : Finset α) (k : altern
atingGroup s) : (ofSubtype s k : Equiv.Perm α) = Equiv.Perm.ofSubtype k.1
· 使用定理 `map_eq_one_iff`：map_eq_one_iff [OneHomClass F M N] (f : F) (hf : Functio
n.Injective f) {x : M} : f x = 1 ↔ x = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `Equiv.Perm.ofSubtype_injective`：ofSubtype_injective : Function.Injective
 (ofSubtype : Perm (Subtype p) -> Perm α)
· 使用定理 `Equiv.Perm.cycleType.congr_simp`：∀ {α : Type u_1} [inst : Fintype α] {in
st_1 : DecidableEq α} [inst_2 : DecidableEq α] (σ σ_1 : Equiv.Perm α),   σ = σ_1
 → σ.cycleType = σ_1.…
· 使用定理 `Equiv.Perm.cycleType_ofSubtype`：cycleType_ofSubtype {p : α -> Prop} [Dec
idablePred p] [Fintype (Subtype p)] {g : Perm (Subtype p)} : cycleType (ofSubtyp
e g) = cycleType g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
（共 33 条，此处仅展示前 30 条）
-/
theorem mem_map_kleinFour_ofSubtype {s : Finset α} (hs : s.card = 4) (k : alternatingGroup α) :
    k ∈ (kleinFour s).map (ofSubtype s) ↔
      (k : Perm α).support ⊆ s ∧ ((k : Perm α) = 1 ∨ (k : Perm α).cycleType = {2, 2}) := by
  have hs : Nat.card s = 4 := by simpa
  by_cases hk : (k : Perm α).support ⊆ s
  · obtain ⟨σ, rfl⟩ := (mem_range_ofSubtype_iff s k).mpr hk
    simp_rw [and_iff_right hk, Subgroup.mem_map, ofSubtype_inj, existsAndEq, and_true,
      ← SetLike.mem_coe, coe_kleinFour_of_card_eq_four hs]
    simp [cycleType_ofSubtype, coe_ofSubtype, map_eq_one_iff _ Perm.ofSubtype_injective]
  · simp_rw [hk, false_and, iff_false]
    contrapose! hk
    exact (mem_range_ofSubtype_iff s k).mp (Subgroup.map_le_range _ _ hk)
/-
**alternatingGroup.map_kleinFour_conj** 是 Mathlib 中的一个定理，位于命名空间 `alternatingGrou
p`。
形式化陈述：map_kleinFour_conj (s : Finset α) (hs : s.card = 4) (g : alternatingGroup 
α) : (kleinFour _).map (ofSubtype (g • s)) = MulAut.conj g • ((kleinFour s).map 
(ofSubtype s))
参数：s : Finset α；hs : s.card = 4；g : alternatingGroup α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `alternatingGroup.mem_map_kleinFour_ofSubtype`：mem_map_kleinFour_ofSubtyp
e {s : Finset α} (hs : s.card = 4) (k : alternatingGroup α) : k in (kleinFour s)
.map (ofSubtype s) ↔ (k : Perm α).…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulAut.inv_apply`：∀ (M : Type u_2) [inst : Mul M] (e : MulAut M) (m : M)
, e⁻¹ m = (MulEquiv.symm e) m
· 使用定理 `Equiv.Perm.cycleType.congr_simp`：∀ {α : Type u_1} [inst : Fintype α] {in
st_1 : DecidableEq α} [inst_2 : DecidableEq α] (σ σ_1 : Equiv.Perm α),   σ = σ_1
 → σ.cycleType = σ_1.…
· 使用定理 `Equiv.Perm.support_toConjAct_eq_smul_support`：support_toConjAct_eq_smul_
support (k g : Perm α) : (ConjAct.toConjAct k • g).support = k • g.support
· 使用定理 `Finset.card_smul_finset`：card_smul_finset (a : α) (s : Finset β) : (a • 
s).card = s.card
· 使用定理 `Equiv.Perm.cycleType_conj`：cycleType_conj {σ τ : Perm α} : (τ * σ * τ⁻¹)
.cycleType = σ.cycleType
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem map_kleinFour_conj (s : Finset α) (hs : s.card = 4) (g : alternatingGroup α) :
    (kleinFour _).map (ofSubtype (g • s)) = MulAut.conj g • ((kleinFour s).map (ofSubtype s)) := by
  rcases g with ⟨g, hg⟩
  ext ⟨k, hk⟩
  simp_rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, mem_map_kleinFour_ofSubtype hs,
    Subgroup.mk_smul, MulAut.smul_def, MulAut.inv_apply, MulAut.conj_symm_apply, Subgroup.coe_mul,
    Subgroup.coe_inv, ← ConjAct.toConjAct_inv_smul, Equiv.Perm.support_toConjAct_eq_smul_support,
    mem_map_kleinFour_ofSubtype (s := g • s) (by simpa), Finset.subset_smul_finset_iff,
    ConjAct.toConjAct_smul, cycleType_conj, mul_inv_eq_one, mul_eq_left]

/-- The Iwasawa structure of `alternatingGroup α` acting on `Set.powersetCard α 4`,
provided `α` has at least 5 elements. -/
/-
**alternatingGroup.iwasawaStructure_four** 是 Mathlib 中的一个定义，位于命名空间 `alternatingG
roup`。
形式化陈述：iwasawaStructure_four (h5 : 5 <= Nat.card α) : IwasawaStructure (alternati
ngGroup α) (Set.powersetCard α 4) where T s
参数：h5 : 5 <= Nat.card α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Iwasawa structure of `alternatingGroup α` acting on `Set.powersetCard α 4`,
provided `α` has at least 5 elements.
-/
def iwasawaStructure_four (h5 : 5 ≤ Nat.card α) :
    IwasawaStructure (alternatingGroup α) (Set.powersetCard α 4) where
  T s := (kleinFour s).map (ofSubtype s)
  is_comm s := by
    have : IsMulCommutative (kleinFour s) :=
      (kleinFour_isKleinFour (by simp)).isMulCommutative
    infer_instance
  is_conj g s := map_kleinFour_conj s.val s.prop g
  is_generator := by
    rw [eq_top_iff, ← closure_cycleType_eq_two_two_eq_top h5, Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_ofPred_eq] at hg
    apply Subgroup.mem_iSup_of_mem ⟨(g : Perm α).support, by simp [← sum_cycleType, hg]⟩
    rw [mem_map_kleinFour_ofSubtype] <;> simp [hg, ← sum_cycleType]

/-- If `α` has at least 5 elements, but not 8,
then the only nontrivial normal subgroup of `alternatingGroup α`
is `⊤`. -/
/-
**alternatingGroup.normal_subgroup_eq_bot_or_eq_top_of_card_ne_eight** 是 Mathlib
 中的一个定理，位于命名空间 `alternatingGroup`。
形式化陈述：normal_subgroup_eq_bot_or_eq_top_of_card_ne_eight (hα : 5 <= Nat.card α) (
hα' : Nat.card α != 8) {N : Subgroup (alternatingGroup α)} [N.Normal] : N = ⊥ ∨ 
N = ⊤
参数：hα : 5 <= Nat.card α；hα' : Nat.card α != 8；alternatingGroup α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Subgroup.nontrivial_iff_ne_bot`：nontrivial_iff_ne_bot (H : Subgroup G) :
 Nontrivial H ↔ H != ⊥
· 使用定理 `Set.powersetCard.isPreprimitive_alternatingGroup`：isPreprimitive_alterna
tingGroup [Fintype α] {n : Nat} (h_three_le : 3 <= n) (hn : n < Nat.card α) (hα 
: Nat.card α != 2 * n) : IsPreprimitiv…
· 使用定理 `Mathlib.Meta.NormNum.isNat_le_true`：∀ {α : Type u_1} [inst : Semiring α]
 [inst_1 : PartialOrder α] [IsOrderedRing α] {a b : α} {a' b' : ℕ},   Mathlib.Me
ta.NormNum.IsNat a a' → …
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `commutator_alternatingGroup_eq_top`：commutator_alternatingGroup_eq_top (
h5 : 5 <= Nat.card α) : commutator (alternatingGroup α) = ⊤
· 使用定理 `MulAction.IwasawaStructure.commutator_le`：commutator_le (IwaS : IwasawaS
tructure M α) [IsQuasiPreprimitive M α] (N : Subgroup M) [nN : N.Normal] (hNX : 
MulAction.fixedPoints N α != .…
· 使用定理 `MulAction.IsPreprimitive.isQuasiPreprimitive`：∀ {M : Type u_3} [inst : G
roup M] {α : Type u_4} [inst_1 : MulAction M α] [MulAction.IsPreprimitive M α], 
  MulAction.IsQuasiPreprimitive M …
· 使用定理 `Set.powersetCard.fixedPoints_ne_univ_of_faithfulSMul`：fixedPoints_ne_uni
v_of_faithfulSMul [Nontrivial G] [FaithfulSMul G α] {n : Nat} (hn : 0 < n) (hn' 
: n < Nat.card α) : fixedPoints G (powerse…
· 使用定理 `Subgroup.instFaithfulSMulSubtypeMem`：∀ {G : Type u_1} {α : Type u_2} [in
st : Group G] [inst_1 : MulAction G α] [FaithfulSMul G α] (S : Subgroup G),   Fa
ithfulSMul (↥S) α
· 使用定理 `Mathlib.Meta.NormNum.isNat_lt_true`：∀ {α : Type u_1} [inst : Semiring α]
 [inst_1 : PartialOrder α] [IsOrderedRing α] [CharZero α] {a b : α} {a' b' : ℕ},
   Mathlib.Meta.NormNum.…

--- 原说明 ---
If `α` has at least 5 elements, but not 8,
then the only nontrivial normal subgroup of `alternatingGroup α`
is `⊤`.
-/
theorem normal_subgroup_eq_bot_or_eq_top_of_card_ne_eight
    (hα : 5 ≤ Nat.card α) (hα' : Nat.card α ≠ 8)
    {N : Subgroup (alternatingGroup α)} [N.Normal] :
    N = ⊥ ∨ N = ⊤ := by
  rw [or_iff_not_imp_left, ← ne_eq, ← Subgroup.nontrivial_iff_ne_bot]
  intro hN
  have : IsPreprimitive (alternatingGroup α) (Set.powersetCard α 4) := by
    apply Set.powersetCard.isPreprimitive_alternatingGroup (by norm_num) <;> grind
  rw [eq_top_iff, ← commutator_alternatingGroup_eq_top hα]
  apply (iwasawaStructure_four hα).commutator_le
  exact fixedPoints_ne_univ_of_faithfulSMul (by norm_num) (by grind)

/- If `α` has at least 5 elements,
then the only nontrivial normal subgroup of `alternatingGroup α`
is `⊤`. -/
/-
**alternatingGroup.normal_subgroup_eq_bot_or_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `a
lternatingGroup`。
形式化陈述：normal_subgroup_eq_bot_or_eq_top (hα : 5 <= Nat.card α) {N : Subgroup (alt
ernatingGroup α)} [N.Normal] : N = ⊥ ∨ N = ⊤
参数：hα : 5 <= Nat.card α；alternatingGroup α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `alternatingGroup.normal_subgroup_eq_bot_or_eq_top_of_card_ne_eight`：norm
al_subgroup_eq_bot_or_eq_top_of_card_ne_eight (hα : 5 <= Nat.card α) (hα' : Nat.
card α != 8) {N : Subgroup (alternatingGroup α)} [N.Norm…
· 使用定理 `alternatingGroup.normal_subgroup_eq_bot_or_eq_top_of_card_ne_six`：normal
_subgroup_eq_bot_or_eq_top_of_card_ne_six (hα : 5 <= Nat.card α) (hα' : Nat.card
 α != 6) {N : Subgroup (alternatingGroup α)} [N.Normal…

--- 原说明 ---
If `α` has at least 5 elements,
then the only nontrivial normal subgroup of `alternatingGroup α`
is `⊤`.
-/
theorem normal_subgroup_eq_bot_or_eq_top
    (hα : 5 ≤ Nat.card α)
    {N : Subgroup (alternatingGroup α)} [N.Normal] :
    N = ⊥ ∨ N = ⊤ := by
  by_cases hα' : Nat.card α = 6
  · apply normal_subgroup_eq_bot_or_eq_top_of_card_ne_eight hα (by grind)
  · apply normal_subgroup_eq_bot_or_eq_top_of_card_ne_six hα hα'

/-- When `α` has at least 5 elements, then `alternatingGroup α` is a simple group. -/
/-
**alternatingGroup.isSimpleGroup** 是 Mathlib 中的一个定理，位于命名空间 `alternatingGroup`。
形式化陈述：isSimpleGroup (hα : 5 <= Nat.card α) : IsSimpleGroup (alternatingGroup α) 
where exists_pair_ne
参数：hα : 5 <= Nat.card α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nontrivial_iff`：nontrivial_iff : Nontrivial α ↔ exists x y : α, x != y
· 使用定理 `alternatingGroup.nontrivial_of_three_le_card`：nontrivial_of_three_le_car
d (h3 : 3 <= Nat.card α) : Nontrivial (alternatingGroup α)
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Mathlib.Meta.NormNum.isNat_le_true`：∀ {α : Type u_1} [inst : Semiring α]
 [inst_1 : PartialOrder α] [IsOrderedRing α] {a b : α} {a' b' : ℕ},   Mathlib.Me
ta.NormNum.IsNat a a' → …
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `alternatingGroup.normal_subgroup_eq_bot_or_eq_top`：normal_subgroup_eq_bo
t_or_eq_top (hα : 5 <= Nat.card α) {N : Subgroup (alternatingGroup α)} [N.Normal
] : N = ⊥ ∨ N = ⊤

--- 原说明 ---
When `α` has at least 5 elements, then `alternatingGroup α` is a simple group.
-/
theorem isSimpleGroup (hα : 5 ≤ Nat.card α) :
    IsSimpleGroup (alternatingGroup α) where
  exists_pair_ne := by
    rw [← _root_.nontrivial_iff]
    refine nontrivial_of_three_le_card ?_
    simpa using le_trans (by norm_num) hα
  eq_bot_or_eq_top_of_normal H _ := normal_subgroup_eq_bot_or_eq_top hα

@[deprecated "Use `alternatingGroup.isSimpleGroup` instead." (since := "2026-04-28")]
/-
**alternatingGroup._root_.Equiv.Perm.IsThreeCycle.alternating_normalClosure** 是 
Mathlib 中的一个定理，位于命名空间 `alternatingGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Equiv.Perm.IsThreeCycle.alternating_normalClosure
    (h5 : 5 ≤ Nat.card α) {f : Perm α} (hf : IsThreeCycle f) :
    normalClosure ({⟨f, hf.mem_alternatingGroup⟩} : Set (alternatingGroup α)) = ⊤ := by
  have : IsSimpleGroup (alternatingGroup α) := isSimpleGroup h5
  apply normalClosure_normal.eq_bot_or_eq_top.resolve_left
  simp [hf.ne_one]

@[deprecated "Use `alternatingGroup.isSimpleGroup` instead." (since := "2026-04-28")]
/-
**alternatingGroup.normalClosure_finRotate_five** 是 Mathlib 中的一个定理，位于命名空间 `alter
natingGroup`。
形式化陈述：normalClosure_finRotate_five : normalClosure ({⟨finRotate 5, finRotate_bit
1_mem_alternatingGroup (n
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `alternatingGroup.isSimpleGroup`：isSimpleGroup (hα : 5 <= Nat.card α) : I
sSimpleGroup (alternatingGroup α) where exists_pair_ne
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Equiv.Perm.finRotate_bit1_mem_alternatingGroup`：finRotate_bit1_mem_alter
natingGroup {n : Nat} : finRotate (2 * n + 1) in alternatingGroup (Fin (2 * n + 
1))
· 使用定理 `Subgroup.Normal.eq_bot_or_eq_top`：Subgroup.Normal.eq_bot_or_eq_top [IsSi
mpleGroup G] {H : Subgroup G} (Hn : H.Normal) : H = ⊥ ∨ H = ⊤
· 使用定理 `eq_false_of_decide`：∀ {p : Prop} {x : Decidable p}, decide p = false → p
 = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem normalClosure_finRotate_five : normalClosure ({⟨finRotate 5,
    finRotate_bit1_mem_alternatingGroup (n := 2)⟩} : Set (alternatingGroup (Fin 5))) = ⊤ := by
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := isSimpleGroup (by simp)
  apply normalClosure_normal.eq_bot_or_eq_top.resolve_left
  simp +decide

@[deprecated "Use `alternatingGroup.isSimpleGroup` instead." (since := "2026-04-28")]
/-
**alternatingGroup.normalClosure_swap_mul_swap_five** 是 Mathlib 中的一个定理，位于命名空间 `a
lternatingGroup`。
形式化陈述：normalClosure_swap_mul_swap_five : normalClosure ({⟨swap 0 4 * swap 1 3, m
em_alternatingGroup.2 (by decide)⟩} : Set (alternatingGroup (Fin 5))) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `alternatingGroup.isSimpleGroup`：isSimpleGroup (hα : 5 <= Nat.card α) : I
sSimpleGroup (alternatingGroup α) where exists_pair_ne
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.Perm.mem_alternatingGroup`：mem_alternatingGroup {f : Perm α} : f i
n alternatingGroup α ↔ sign f = 1
· 使用定理 `Subgroup.Normal.eq_bot_or_eq_top`：Subgroup.Normal.eq_bot_or_eq_top [IsSi
mpleGroup G] {H : Subgroup G} (Hn : H.Normal) : H = ⊥ ∨ H = ⊤
· 使用定理 `eq_false_of_decide`：∀ {p : Prop} {x : Decidable p}, decide p = false → p
 = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem normalClosure_swap_mul_swap_five : normalClosure ({⟨swap 0 4 * swap 1 3,
    mem_alternatingGroup.2 (by decide)⟩} : Set (alternatingGroup (Fin 5))) = ⊤ := by
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := isSimpleGroup (by simp)
  apply normalClosure_normal.eq_bot_or_eq_top.resolve_left
  simp +decide

@[deprecated "Use `alternatingGroup.isSimpleGroup` instead." (since := "2026-04-28")]
/-
**alternatingGroup.isSimpleGroup_five** 是 Mathlib 中的一个实例，位于命名空间 `alternatingGrou
p`。
形式化陈述：isSimpleGroup_five : IsSimpleGroup (alternatingGroup (Fin 5))
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `alternatingGroup.isSimpleGroup`：isSimpleGroup (hα : 5 <= Nat.card α) : I
sSimpleGroup (alternatingGroup α) where exists_pair_ne
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
-/
instance isSimpleGroup_five : IsSimpleGroup (alternatingGroup (Fin 5)) :=
  isSimpleGroup (by simp)

end alternatingGroup

