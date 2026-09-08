/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Card
public import Mathlib.Data.Set.Card
public import Mathlib.GroupTheory.GroupAction.MultiplePrimitivity

/-! # Theorems of Jordan

A proof of theorems of Jordan regarding primitive permutation groups.

This mostly follows the book [Wielandt, *Finite permutation groups*][Wielandt-1964].

- `MulAction.IsPreprimitive.is_two_pretransitive` and
  `MulAction.IsPreprimitive.is_two_preprimitive` are technical lemmas
  that prove 2-pretransitivity / 2-preprimitivity for some group
  primitive actions given the transitivity / primitivity of
  `ofFixingSubgroup G s` (Wielandt, 13.1)

- `MulAction.IsPreprimitive.isMultiplyPreprimitive`:
  A multiple preprimitivity criterion of Jordan (1871) for a preprimitive
  action: the hypothesis is the preprimitivity of the `SubMulAction`
  of `fixingSubgroup s` on `ofFixingSubgroup G s` (Wielandt, 13.2)

- `Equiv.Perm.eq_top_of_isPreprimitive_of_isSwap_mem` :
  a primitive subgroup of a permutation group that contains a
  swap is equal to the full permutation group (Wielandt, 13.3)

- `Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem` :
  a primitive subgroup of a permutation group that contains a 3-cycle
  contains the alternating group (Wielandt, 13.3)

## TODO

- Prove `Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isCycle_mem`:
  a primitive subgroup of a permutation group that contains
  a cycle of *prime* order contains the alternating group (Wielandt, 13.9).

- Prove the stronger versions of the technical lemmas of Jordan (Wielandt, 13.1').

-/

public section

open MulAction SubMulAction Subgroup

open scoped Pointwise

section Jordan

variable {G α : Type*} [Group G] [MulAction G α]

/-- In a 2-transitive action, the normal closure of stabilizers is the full group. -/
/-
**normalClosure_of_stabilizer_eq_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：normalClosure_of_stabilizer_eq_top (hsn' : 2 < ENat.card α) (hG' : IsMulti
plyPretransitive G α 2) {a : α} : normalClosure ((stabilizer G a) : Set G) = ⊤
参数：hsn' : 2 < ENat.card α；hG' : IsMultiplyPretransitive G α 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulAction.is_one_pretransitive_iff`：is_one_pretransitive_iff : IsMultipl
yPretransitive G α 1 ↔ IsPretransitive G α
· 使用定理 `MulAction.isMultiplyPretransitive_of_le'`：isMultiplyPretransitive_of_le'
 {m n : Nat} [IsMultiplyPretransitive G α n] (hmn : m <= n) (hα : n <= ENat.card
 α) : IsMultiplyPretransitive …
· 使用引理 `one_le_two`：one_le_two [LE α] [ZeroLEOneClass α] [AddLeftMono α] : (1 : 
α) <= 2
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `ENat.one_lt_card_iff_nontrivial`：one_lt_card_iff_nontrivial (α : Type*) 
: 1 < card α ↔ Nontrivial α
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用定理 `Mathlib.Meta.NormNum.isNat_lt_true`：∀ {α : Type u_1} [inst : Semiring α]
 [inst_1 : PartialOrder α] [IsOrderedRing α] [CharZero α] {a b : α} {a' b' : ℕ},
   Mathlib.Meta.NormNum.…
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `MulAction.isCoatom_stabilizer_iff_preprimitive`：isCoatom_stabilizer_iff_
preprimitive [IsPretransitive G X] [Nontrivial X] (a : X) : IsCoatom (stabilizer
 G a) ↔ IsPreprimitive G X
· 使用定理 `MulAction.isPreprimitive_of_is_two_pretransitive`：isPreprimitive_of_is_t
wo_pretransitive (h2 : IsMultiplyPretransitive G α 2) : IsPreprimitive G α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subgroup.le_normalClosure`：le_normalClosure {H : Subgroup G} : H <= norm
alClosure ↑H
· 使用定理 `lt_of_add_lt_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] 
[i : AddRightReflectLT α] {a b c : α}, b + a < c + a → b < c
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用引理 `SubMulAction.ENat_card_ofStabilizer_add_one_eq`：ENat_card_ofStabilizer_a
dd_one_eq (a : α) : ENat.card (ofStabilizer G a) + 1 = ENat.card α
· 使用定理 `nontrivial_iff`：nontrivial_iff : Nontrivial α ↔ exists x y : α, x != y
· 使用定理 `SubMulAction.ofStabilizer.isMultiplyPretransitive`：isMultiplyPretransiti
ve [IsPretransitive G α] {n : Nat} {a : α} : IsMultiplyPretransitive G α n.succ 
↔ IsMultiplyPretransitive (stabilizer G…
· 使用引理 `MulAction.exists_smul_eq`：exists_smul_eq (x y : α) : exists m : M, m • x
 = y
· 使用定理 `SetLike.coe_eq_coe`：coe_eq_coe {x y : p} : (x : B) = y ↔ x = y
· 使用定理 `SubMulAction.instSMulMemClass`：∀ {R : Type u} {M : Type v} [inst : SMul 
R M], SMulMemClass (SubMulAction R M) R M
（共 37 条，此处仅展示前 30 条）

--- 原说明 ---
In a 2-transitive action, the normal closure of stabilizers is the full group.
-/
theorem normalClosure_of_stabilizer_eq_top (hsn' : 2 < ENat.card α)
    (hG' : IsMultiplyPretransitive G α 2) {a : α} :
    normalClosure ((stabilizer G a) : Set G) = ⊤ := by
  have : IsPretransitive G α := by
    rw [← is_one_pretransitive_iff]
    exact isMultiplyPretransitive_of_le' (one_le_two) (le_of_lt hsn')
  have : Nontrivial α := by
    rw [← ENat.one_lt_card_iff_nontrivial]
    exact lt_trans (by norm_num) hsn'
  have hGa : IsCoatom (stabilizer G a) := by
    rw [isCoatom_stabilizer_iff_preprimitive]
    exact isPreprimitive_of_is_two_pretransitive hG'
  apply hGa.right
  -- Remains to prove: (stabilizer G a) < Subgroup.normalClosure (stabilizer G a)
  constructor
  · apply le_normalClosure
  · intro hyp
    have : Nontrivial (ofStabilizer G a) := by
      rw [← ENat.one_lt_card_iff_nontrivial]
      apply lt_of_add_lt_add_right
      rwa [ENat_card_ofStabilizer_add_one_eq]
    rw [nontrivial_iff] at this
    obtain ⟨b, c, hbc⟩ := this
    have : IsPretransitive (stabilizer G a) (ofStabilizer G a) := by
      rw [← is_one_pretransitive_iff]
      rwa [← ofStabilizer.isMultiplyPretransitive]
    -- get g ∈ stabilizer G a, g • b = c,
    obtain ⟨⟨g, hg⟩, hgbc⟩ := exists_smul_eq (stabilizer G a) b c
    apply hbc
    rw [← SetLike.coe_eq_coe] at hgbc ⊢
    obtain ⟨h, hinvab⟩ := exists_smul_eq G (b : α) a
    rw [eq_comm, ← inv_smul_eq_iff] at hinvab
    rw [← hgbc, SetLike.val_smul, ← hinvab, inv_smul_eq_iff, eq_comm]
    simp only [subgroup_smul_def, smul_smul, ← mul_assoc, ← mem_stabilizer_iff]
    exact hyp (normalClosure_normal.conj_mem g (le_normalClosure hg) h)

-- Wielandt claims that this is proved by the same method as above.
proof_wanted IsPreprimitive.is_two_pretransitive'
    (hG : IsPreprimitive G α)
    {s : Set α} {n : ℕ} (hsn : Nat.card s = n + 1) (hsn' : n + 1 < Nat.card α)
    (hs_trans : IsPretransitive (fixingSubgroup G s) (SubMulAction.ofFixingSubgroup G s)) :
    IsMultiplyPretransitive (Subgroup.normalClosure (fixingSubgroup G s : Set G)) α 2

open MulAction.IsPreprimitive

open scoped Pointwise

/-- Simultaneously prove `MulAction.IsPreprimitive.is_two_pretransitive`
and `MulAction.IsPreprimitive.is_two_preprimitive`. -/
/-
**MulAction.IsPreprimitive.is_two_motive_of_is_motive** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：MulAction.IsPreprimitive.is_two_motive_of_is_motive (hG : IsPreprimitive G
 α) {s : Set α} {n : Nat} (hsn : s.ncard = n + 1) (hsn' : n + 2 < Nat.card α) : 
(IsPretransitive (fixingSubgroup G s) (ofFixingSubgroup G s) -> IsMultiplyPretra
nsitive G α 2) ∧ (IsPreprimitive (fixingSubgroup G s) (ofFixingSubgroup G s) -> 
IsMultiplyPreprimitive G α 2)
参数：hG : IsPreprimitive G α；hsn : s.ncard = n + 1；hsn' : n + 2 < Nat.card α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.strong_induction_on`：∀ {p : ℕ → Prop} (n : ℕ), (∀ (n : ℕ), (∀ m < n,
 p m) → p n) → p n
· 使用定理 `Nat.finite_of_card_ne_zero`：finite_of_card_ne_zero (h : Nat.card α != 0)
 : Finite α
· 使用定理 `ne_zero_of_lt`：∀ {α : Type u_1} {a b : α} [inst : Preorder α] [inst_1 : 
Zero α] [IsBotZeroClass α], a < b → b ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ncard_univ`：∀ (α : Type u_3), Set.univ.ncard = Nat.card α
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ncard_pos`：ncard_pos (hs : s.Finite
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `Nat.lt_or_ge`：∀ (n m : ℕ), n < m ∨ n ≥ m
· 使用定理 `Nat.lt_one_iff`：∀ {n : ℕ}, n < 1 ↔ n = 0
· 使用定理 `Nat.succ_lt_succ_iff`：∀ {a b : ℕ}, a.succ < b.succ ↔ a < b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `SubMulAction.ofStabilizer.isMultiplyPretransitive`：isMultiplyPretransiti
ve [IsPretransitive G α] {n : Nat} {a : α} : IsMultiplyPretransitive G α n.succ 
↔ IsMultiplyPretransitive (stabilizer G…
（共 85 条，此处仅展示前 30 条）

--- 原说明 ---
Simultaneously prove `MulAction.IsPreprimitive.is_two_pretransitive`
and `MulAction.IsPreprimitive.is_two_preprimitive`.
-/
theorem MulAction.IsPreprimitive.is_two_motive_of_is_motive
    (hG : IsPreprimitive G α) {s : Set α} {n : ℕ}
    (hsn : s.ncard = n + 1) (hsn' : n + 2 < Nat.card α) :
    (IsPretransitive (fixingSubgroup G s) (ofFixingSubgroup G s)
      → IsMultiplyPretransitive G α 2)
    ∧ (IsPreprimitive (fixingSubgroup G s) (ofFixingSubgroup G s)
      → IsMultiplyPreprimitive G α 2) := by
  induction n using Nat.strong_induction_on generalizing α G with
  | h n hrec =>
  have : Finite α := Nat.finite_of_card_ne_zero <| ne_zero_of_lt hsn'
  have hs_ne_univ : s ≠ Set.univ := by
    intro hs
    rw [hs, Set.ncard_univ] at hsn
    simp only [hsn, add_lt_add_iff_left, Nat.not_ofNat_lt_one] at hsn'
  have hs_nonempty : s.Nonempty := by
    simp [← Set.ncard_pos s.toFinite, hsn]
  -- The result is assumed by induction for sets of ncard ≤ n
  rcases Nat.lt_or_ge (n + 1) 2 with hn | hn
  · -- When n + 1 < 2 (imposes n = 0)
    have hn : n = 0 := by
      rwa [Nat.succ_lt_succ_iff, Nat.lt_one_iff] at hn
    simp only [hn, zero_add, Set.ncard_eq_one] at hsn
    obtain ⟨a, hsa⟩ := hsn
    suffices IsPretransitive (fixingSubgroup G s) (ofFixingSubgroup G s) →
      IsMultiplyPretransitive G α 2 by
      refine ⟨this, fun hs_prim ↦ ?_⟩
      rw [hsa] at hs_prim
      rw [isMultiplyPreprimitive_succ_iff_ofStabilizer G α le_rfl (a := a),
        is_one_preprimitive_iff]
      exact IsPreprimitive.of_surjective
          ofFixingSubgroup_of_singleton_bijective.surjective
    rw [hsa]
    rw [ofStabilizer.isMultiplyPretransitive (a := a)]
    rw [is_one_pretransitive_iff]
    exact IsPretransitive.of_surjective_map
      ofFixingSubgroup_of_singleton_bijective.surjective
  rcases Nat.lt_or_ge (2 * (n + 1)) (Nat.card α) with hn1 | hn2
  · -- CASE where 2 * s.ncard < Nat.card α
    -- get a, b ∈ s, a ≠ b
    have : 1 < s.ncard := by rwa [hsn]
    rw [Set.one_lt_ncard] at this
    obtain ⟨a, ha, b, hb, hab⟩ := this
    -- apply Rudio to get g ∈ G such that a ∈ g • s, b ∉ g • s
    obtain ⟨g, hga, hgb⟩ :=
      exists_mem_smul_and_notMem_smul (G := G) s.toFinite hs_nonempty hs_ne_univ hab
    let t := s ∩ g • s
    have ht : t.Finite := s.toFinite.inter_of_left (g • s)
    have htm : t.ncard = t.ncard - 1 + 1 := by
      apply (Nat.sub_eq_iff_eq_add ?_).mp rfl
      rw [Nat.one_le_iff_ne_zero]
      apply Set.ncard_ne_zero_of_mem (a := a) _ ht
      exact ⟨ha, hga⟩
    have hmn : t.ncard - 1 < n := by
      rw [Nat.lt_iff_add_one_le, ← htm, Nat.le_iff_lt_add_one, ← hsn]
      apply Set.ncard_lt_ncard _
      exact ⟨Set.inter_subset_left, fun h ↦ hgb (Set.inter_subset_right (h hb))⟩
    have htm' : t.ncard - 1 + 2 < Nat.card α := lt_trans (Nat.add_lt_add_right hmn 2) hsn'
    suffices IsPretransitive ↥(fixingSubgroup G s) ↥(ofFixingSubgroup G s) →
      IsMultiplyPretransitive G α 2 by
      refine ⟨this, fun hs_prim ↦ ?_⟩
      have ht_prim : IsPreprimitive (fixingSubgroup G t) (ofFixingSubgroup G t) := by
        apply IsPreprimitive.isPreprimitive_ofFixingSubgroup_inter hs_prim
        apply Set.union_ne_univ_of_ncard_add_ncard_lt
        rwa [Set.ncard_smul_set, hsn, ← two_mul]
      apply (hrec (t.ncard - 1) hmn hG htm htm').2 ht_prim
    intro hs_trans
    have ht_trans : IsPretransitive (fixingSubgroup G t) (ofFixingSubgroup G t) :=
      IsPretransitive.isPretransitive_ofFixingSubgroup_inter hs_trans (by
        apply Set.union_ne_univ_of_ncard_add_ncard_lt
        rwa [Set.ncard_smul_set, hsn, ← two_mul])
    apply (hrec (t.ncard - 1) hmn hG htm ?_).1 ht_trans
    apply lt_trans _ hsn'
    exact Nat.add_lt_add_right hmn 2
  · -- CASE : 2 * s.ncard ≥ Nat.card α
    have : Set.Nontrivial sᶜ := by
      rwa [← Set.one_lt_encard_iff_nontrivial, ← sᶜ.toFinite.cast_ncard_eq, Nat.one_lt_cast,
        ← Nat.add_lt_add_iff_left, Set.ncard_add_ncard_compl, add_comm, hsn, add_comm]
    -- get a, b ∈ sᶜ, a ≠ b
    obtain ⟨a, ha : a ∈ sᶜ, b, hb : b ∈ sᶜ, hab⟩ := this
    -- apply Rudio to get g ∈ G such that a ∈ g • sᶜ, b ∉ g • sᶜ
    obtain ⟨g, hga, hgb⟩ := exists_mem_smul_and_notMem_smul (G := G)
      sᶜ.toFinite (Set.nonempty_of_mem ha)
      (by simpa [Set.nonempty_iff_ne_empty] using hs_nonempty)
      hab
    let t := s ∩ g • s
    have ha : a ∉ s ∪ g • s := by
      simp only [Set.smul_set_compl, Set.mem_compl_iff] at hga ha
      simp [ha, hga]
    have htm : t.ncard = t.ncard - 1 + 1 := by
      apply (Nat.sub_eq_iff_eq_add ?_).mp rfl
      rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, Set.ncard_pos]
      apply Set.nonempty_inter_of_le_ncard_add_ncard
      · rw [Set.ncard_smul_set, ← two_mul, hsn]; exact hn2
      · exact fun h ↦ ha (by rw [h]; trivial)
    have hmn : t.ncard - 1 < n := by
      rw [Nat.lt_iff_add_one_le, ← htm, Nat.le_iff_lt_add_one, ← hsn]
      apply Set.ncard_lt_ncard _
      refine ⟨Set.inter_subset_left, fun h ↦ hb ?_⟩
      suffices s = g • s by
        rw [this]
        simpa only [Set.smul_set_compl, Set.mem_compl_iff, Set.not_notMem] using hgb
      apply Set.eq_of_subset_of_ncard_le _ _ (g • s).toFinite
      · exact subset_trans h Set.inter_subset_right
      · rw [Set.ncard_smul_set]
    have htm' : t.ncard - 1 + 2 < Nat.card α := lt_trans (Nat.add_lt_add_right hmn 2) hsn'
    have hsgs_ne_top : s ∪ g • s ≠ ⊤ := fun h ↦ ha (h ▸ Set.mem_univ a)
    suffices IsPretransitive ↥(fixingSubgroup G s) ↥(ofFixingSubgroup G s) →
      IsMultiplyPretransitive G α 2 by
      refine ⟨this, fun hs_prim ↦ ?_⟩
      apply (hrec _ hmn hG htm htm').2
      exact IsPreprimitive.isPreprimitive_ofFixingSubgroup_inter
          hs_prim hsgs_ne_top
    intro hs_trans
    apply (hrec _ hmn hG htm htm').1
    exact IsPretransitive.isPretransitive_ofFixingSubgroup_inter hs_trans hsgs_ne_top

/-- A criterion due to Jordan for being 2-pretransitive (Wielandt, 13.1) -/
/-
**MulAction.IsPreprimitive.is_two_pretransitive** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MulAction.IsPreprimitive.is_two_pretransitive (hG : IsPreprimitive G α) {s
 : Set α} {n : Nat} (hsn : s.ncard = n + 1) (hsn' : n + 2 < Nat.card α) (hs_tran
s : IsPretransitive (fixingSubgroup G s) (SubMulAction.ofFixingSubgroup G s)) : 
IsMultiplyPretransitive G α 2
参数：hG : IsPreprimitive G α；hsn : s.ncard = n + 1；hsn' : n + 2 < Nat.card α；hs_tr
ans : IsPretransitive (fixingSubgroup G s) (SubMulAction.ofFixingSubgroup G s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MulAction.IsPreprimitive.is_two_motive_of_is_motive`：MulAction.IsPreprim
itive.is_two_motive_of_is_motive (hG : IsPreprimitive G α) {s : Set α} {n : Nat}
 (hsn : s.ncard = n + 1) (hsn' : n + 2 < …

--- 原说明 ---
A criterion due to Jordan for being 2-pretransitive (Wielandt, 13.1)
-/
theorem MulAction.IsPreprimitive.is_two_pretransitive
    (hG : IsPreprimitive G α) {s : Set α} {n : ℕ}
    (hsn : s.ncard = n + 1) (hsn' : n + 2 < Nat.card α)
    (hs_trans : IsPretransitive (fixingSubgroup G s) (SubMulAction.ofFixingSubgroup G s)) :
    IsMultiplyPretransitive G α 2 :=
  (hG.is_two_motive_of_is_motive hsn hsn').1 hs_trans

/-- A criterion due to Jordan for being 2-preprimitive (Wielandt, 13.1) -/
/-
**MulAction.IsPreprimitive.is_two_preprimitive** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MulAction.IsPreprimitive.is_two_preprimitive (hG : IsPreprimitive G α) {s 
: Set α} {n : Nat} (hsn : s.ncard = n + 1) (hsn' : n + 2 < Nat.card α) (hs_prim 
: IsPreprimitive (fixingSubgroup G s) (SubMulAction.ofFixingSubgroup G s)) : IsM
ultiplyPreprimitive G α 2
参数：hG : IsPreprimitive G α；hsn : s.ncard = n + 1；hsn' : n + 2 < Nat.card α；hs_pr
im : IsPreprimitive (fixingSubgroup G s) (SubMulAction.ofFixingSubgroup G s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MulAction.IsPreprimitive.is_two_motive_of_is_motive`：MulAction.IsPreprim
itive.is_two_motive_of_is_motive (hG : IsPreprimitive G α) {s : Set α} {n : Nat}
 (hsn : s.ncard = n + 1) (hsn' : n + 2 < …

--- 原说明 ---
A criterion due to Jordan for being 2-preprimitive (Wielandt, 13.1)
-/
theorem MulAction.IsPreprimitive.is_two_preprimitive
    (hG : IsPreprimitive G α) {s : Set α} {n : ℕ}
    (hsn : s.ncard = n + 1) (hsn' : n + 2 < Nat.card α)
    (hs_prim : IsPreprimitive (fixingSubgroup G s) (SubMulAction.ofFixingSubgroup G s)) :
    IsMultiplyPreprimitive G α 2 :=
  (hG.is_two_motive_of_is_motive hsn hsn').2 hs_prim

-- Wielandt claims that this stronger version is proved in the same way
proof_wanted is_two_preprimitive_strong_jordan
    (hG : IsPreprimitive G α)
    {s : Set α} {n : ℕ} (hsn : s.ncard = n + 1) (hsn' : n + 2 < Nat.card α)
    (hs_prim : IsPreprimitive (fixingSubgroup G s) (ofFixingSubgroup G s)) :
    IsMultiplyPreprimitive (Subgroup.normalClosure (fixingSubgroup G s : Set G)) α 2

/-- Jordan's multiple primitivity criterion (Wielandt, 13.3) -/
/-
**MulAction.IsPreprimitive.isMultiplyPreprimitive** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MulAction.IsPreprimitive.isMultiplyPreprimitive (hG : IsPreprimitive G α) 
{s : Set α} {n : Nat} (hsn : s.ncard = n + 1) (hsn' : n + 2 < Nat.card α) (hprim
 : IsPreprimitive (fixingSubgroup G s) (ofFixingSubgroup G s)) : IsMultiplyPrepr
imitive G α (n + 2)
参数：hG : IsPreprimitive G α；hsn : s.ncard = n + 1；hsn' : n + 2 < Nat.card α；hprim
 : IsPreprimitive (fixingSubgroup G s) (ofFixingSubgroup G s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `finite_or_infinite`：finite_or_infinite (α : Sort*) : Finite α ∨ Infinite
 α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_eq_zero_of_infinite`：∀ {α : Type u_1} [Infinite α], Nat.card α 
= 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `MulAction.IsPreprimitive.is_two_preprimitive`：MulAction.IsPreprimitive.i
s_two_preprimitive (hG : IsPreprimitive G α) {s : Set α} {n : Nat} (hsn : s.ncar
d = n + 1) (hsn' : n + 2 < Nat.car…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ncard_pos`：ncard_pos (hs : s.Finite
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `Set.mem_image`：mem_image (f : α -> β) (s : Set α) (y : β) : y in f '' s 
↔ exists x in s, f x = y
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
（共 52 条，此处仅展示前 30 条）

--- 原说明 ---
Jordan's multiple primitivity criterion (Wielandt, 13.3)
-/
theorem MulAction.IsPreprimitive.isMultiplyPreprimitive
    (hG : IsPreprimitive G α) {s : Set α} {n : ℕ}
    (hsn : s.ncard = n + 1) (hsn' : n + 2 < Nat.card α)
    (hprim : IsPreprimitive (fixingSubgroup G s) (ofFixingSubgroup G s)) :
    IsMultiplyPreprimitive G α (n + 2) := by
  have hα : Finite α := Or.resolve_right (finite_or_infinite α) (fun _ ↦ by
    simp [Nat.card_eq_zero_of_infinite] at hsn')
  induction n generalizing α hα G with
  -- case n = 0
  | zero => simpa using is_two_preprimitive hG hsn hsn' hprim
  -- Induction step
  | succ n hrec =>
    suffices ∃ (a : α) (t : Set (SubMulAction.ofStabilizer G a)),
      a ∈ s ∧ s = insert a (Subtype.val '' t) by
      obtain ⟨a, t, _, hst⟩ := this
      have ha' : a ∉ Subtype.val '' t := by
        intro h; rw [Set.mem_image] at h; obtain ⟨x, hx⟩ := h
        apply x.prop; rw [hx.right]; exact Set.mem_singleton a
      have ht_prim : IsPreprimitive (stabilizer G a) (SubMulAction.ofStabilizer G a) := by
        rw [← is_one_preprimitive_iff]
        rw [← isMultiplyPreprimitive_succ_iff_ofStabilizer]
        · apply is_two_preprimitive hG hsn hsn' hprim
        · norm_num
      have : IsPreprimitive ↥(fixingSubgroup G (insert a (Subtype.val '' t)))
          (ofFixingSubgroup G (insert a (Subtype.val '' t))) :=
        IsPreprimitive.of_surjective
          (ofFixingSubgroup_of_eq_bijective (hst := hst)).surjective
      have hGs' : IsPreprimitive (fixingSubgroup (stabilizer G a) t)
        (ofFixingSubgroup (stabilizer G a) t) :=
        IsPreprimitive.of_surjective
          ofFixingSubgroup_insert_map_bijective.surjective
      rw [isMultiplyPreprimitive_succ_iff_ofStabilizer G (a := a) _ (Nat.le_add_left 1 (n + 1))]
      refine hrec ht_prim ?_ ?_ hGs' Subtype.finite
      · -- t.card = Nat.succ n
        rw [← Set.ncard_image_of_injective t Subtype.val_injective]
        apply Nat.add_right_cancel
        rw [← Set.ncard_insert_of_notMem ha', ← hst, hsn]
      · -- n + 2 < Nat.card (SubMulAction.ofStabilizer G α a)
        rw [← Nat.add_lt_add_iff_right, nat_card_ofStabilizer_add_one_eq]
        exact hsn'
    -- ∃ a t, a ∈ s ∧ s = insert a (Subtype.val '' t)
    suffices s.Nonempty by
      obtain ⟨a, ha⟩ := this
      use a, Subtype.val ⁻¹' s, ha
      ext x
      by_cases hx : x = a <;> simp [hx, mem_ofStabilizer_iff, ha]
    rw [← Set.ncard_pos, hsn]; apply Nat.succ_pos

end Jordan

section Subgroups

namespace Equiv.Perm

open Equiv

variable {α : Type*}

variable {G : Subgroup (Perm α)}

/-
**Equiv.Perm.subgroup_eq_top_of_nontrivial** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm
`。
形式化陈述：subgroup_eq_top_of_nontrivial [Finite α] (hα : Nat.card α <= 2) (hG : Nont
rivial G) : G = (⊤ : Subgroup (Perm α))
参数：hα : Nat.card α <= 2；hG : Nontrivial G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.eq_top_of_le_card`：eq_top_of_le_card [Finite G] (h : Nat.card G
 <= Nat.card H) : H = ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_perm`：card_perm : Nat.card (Perm α) = (Nat.card α)!
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Nat.factorial_le`：factorial_le {m n} (h : m <= n) : m ! <= n !
· 使用定理 `Nat.factorial_two`：Nat.factorial 2 = 2
· 使用定理 `Nat.succ_le_iff`：∀ {m n : ℕ}, m.succ ≤ n ↔ m < n
· 使用定理 `Subgroup.one_lt_card_iff_ne_bot`：one_lt_card_iff_ne_bot [Finite H] : 1 <
 Nat.card H ↔ H != ⊥
· 使用定理 `Subgroup.instFiniteSubtypeMem`：∀ {G : Type u_1} [inst : Group G] (K : Su
bgroup G) [Finite G], Finite ↥K
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.nontrivial_iff_ne_bot`：nontrivial_iff_ne_bot (H : Subgroup G) :
 Nontrivial H ↔ H != ⊥
-/
theorem subgroup_eq_top_of_nontrivial [Finite α] (hα : Nat.card α ≤ 2) (hG : Nontrivial G) :
    G = (⊤ : Subgroup (Perm α)) := by
  apply Subgroup.eq_top_of_le_card
  rw [Nat.card_perm]
  apply (Nat.factorial_le hα).trans
  rwa [Nat.factorial_two, Nat.succ_le_iff, one_lt_card_iff_ne_bot, ← nontrivial_iff_ne_bot]
/-
**Equiv.Perm.isMultiplyPretransitive_of_nontrivial** 是 Mathlib 中的一个定理，位于命名空间 `Eq
uiv.Perm`。
形式化陈述：isMultiplyPretransitive_of_nontrivial {K : Type*} [Group K] [MulAction K α
] (hα : Nat.card α = 2) (hK : fixedPoints K α != .univ) (n : Nat) : IsMultiplyPr
etransitive K α n
参数：hα : Nat.card α = 2；hK : fixedPoints K α != .univ；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `finite_or_infinite`：finite_or_infinite (α : Sort*) : Finite α ∨ Infinite
 α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_eq_zero_of_infinite`：∀ {α : Type u_1} [Infinite α], Nat.card α 
= 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Function.bijective_id`：bijective_id : Bijective (@id α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonoidHom.range_eq_top`：range_eq_top {N} [Group N] {f : G ->* N} : f.ran
ge = (⊤ : Subgroup N) ↔ Function.Surjective f
· 使用定理 `Subgroup.eq_top_of_card_eq`：eq_top_of_card_eq [Finite H] (h : Nat.card H
 = Nat.card G) : H = ⊤
· 使用定理 `Subgroup.instFiniteSubtypeMem`：∀ {G : Type u_1} [inst : Group G] (K : Su
bgroup G) [Finite G], Finite ↥K
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Subgroup.card_le_card_group`：card_le_card_group [Finite G] : Nat.card H 
<= Nat.card G
· 使用定理 `Nat.card_perm`：card_perm : Nat.card (Perm α) = (Nat.card α)!
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Set.eq_univ_of_univ_subset`：∀ {α : Type u} {s : Set α}, Set.univ ⊆ s → s
 = Set.univ
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulAction.toPermHom_apply`：∀ (G : Type u_1) (α : Type u_5) [inst : Group
 G] [inst_1 : MulAction G α] (a : G),   (MulAction.toPermHom G α) a = MulAction.
toPerm a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MulAction.IsPretransitive.of_embedding_congr`：∀ {G : Type u_1} {α : Type
 u_2} [inst : Group G] [inst_1 : MulAction G α] {H : Type u_3} {β : Type u_4}   
[inst_2 : Group H] [inst_3 : MulAc…
· 使用定理 `Equiv.Perm.isMultiplyPretransitive`：∀ (α : Type u_1) (n : ℕ), MulAction.
IsMultiplyPretransitive (Equiv.Perm α) α n
· 使用定理 `MulAction.isMultiplyPretransitive_of_le'`：isMultiplyPretransitive_of_le'
 {m n : Nat} [IsMultiplyPretransitive G α n] (hmn : m <= n) (hα : n <= ENat.card
 α) : IsMultiplyPretransitive …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
（共 36 条，此处仅展示前 30 条）
-/
theorem isMultiplyPretransitive_of_nontrivial {K : Type*} [Group K] [MulAction K α]
    (hα : Nat.card α = 2) (hK : fixedPoints K α ≠ .univ) (n : ℕ) :
    IsMultiplyPretransitive K α n := by
  have : Finite α := Or.resolve_right (finite_or_infinite α) (fun _ ↦ by
    simp [Nat.card_eq_zero_of_infinite] at hα)
  have : Fintype α := Fintype.ofFinite α
  suffices h2 : IsMultiplyPretransitive K α 2 by
    by_cases hn : n ≤ 2
    · apply MulAction.isMultiplyPretransitive_of_le' hn
      simp [← hα]
    · suffices (IsEmpty (Fin n ↪ α)) by infer_instance
      rwa [← not_nonempty_iff, Function.Embedding.nonempty_iff_card_le, Fintype.card_fin,
        ← Nat.card_eq_fintype_card, hα]
  let φ := MulAction.toPermHom K α
  let f : α →ₑ[φ] α :=
    { toFun := id
      map_smul' := fun _ _ ↦ rfl }
  have hf : Function.Bijective f := Function.bijective_id
  suffices Function.Surjective φ by
    unfold IsMultiplyPretransitive
    rw [IsPretransitive.of_embedding_congr this hf (n := Fin 2), ← hα]
    apply Perm.isMultiplyPretransitive
  rw [← MonoidHom.range_eq_top]
  apply Subgroup.eq_top_of_card_eq
  apply le_antisymm (card_le_card_group φ.range)
  simp only [Nat.card_perm, hα, Nat.factorial_two]
  by_contra H
  simp only [not_le, Nat.lt_succ_iff, Finite.card_le_one_iff_subsingleton] at H
  apply hK
  apply Set.eq_univ_of_univ_subset
  intro a _ g
  suffices φ g = φ 1 by
    conv_rhs => rw [← one_smul K a]
    simp only [← toPerm_apply, ← toPermHom_apply K α g]
    exact congrFun (congrArg DFunLike.coe this) a
  simpa [← Subtype.coe_inj] using H.elim ⟨_, ⟨g, rfl⟩⟩ ⟨_, ⟨1, rfl⟩⟩

variable [Fintype α] [DecidableEq α]
/-
**Equiv.Perm.isPretransitive_of_isCycle_mem** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Per
m`。
形式化陈述：isPretransitive_of_isCycle_mem {g : Perm α} (hgc : g.IsCycle) (hg : g in G
) : IsPretransitive (fixingSubgroup G (g.support : Set α)ᶜ) (SubMulAction.ofFixi
ngSubgroup G (g.support : Set α)ᶜ)
参数：hgc : g.IsCycle；hg : g in G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `mem_fixingSubgroup_iff`：mem_fixingSubgroup_iff {s : Set α} {m : M} : m i
n fixingSubgroup M s ↔ forall y in s, m • y = y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulAction.isPretransitive_iff`：∀ (M : Type u_5) (α : Type u_6) [inst : S
Mul M α], MulAction.IsPretransitive M α ↔ ∀ (x y : α), ∃ g, g • x = y
· 使用定理 `SetLike.coe_eq_coe`：coe_eq_coe {x y : p} : (x : B) = y ↔ x = y
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `inv_mul_cancel_right`：inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a
-/
theorem isPretransitive_of_isCycle_mem {g : Perm α}
    (hgc : g.IsCycle) (hg : g ∈ G) :
    IsPretransitive (fixingSubgroup G (g.support : Set α)ᶜ)
      (SubMulAction.ofFixingSubgroup G (g.support : Set α)ᶜ) := by
  obtain ⟨a, _, hgc⟩ := hgc
  have hs : ∀ x : α, g • x ≠ x ↔
    x ∈ SubMulAction.ofFixingSubgroup G ((↑g.support : Set α)ᶜ) := by
    intro x
    simp [SubMulAction.mem_ofFixingSubgroup_iff]
  suffices ∀ x ∈ SubMulAction.ofFixingSubgroup G ((↑g.support : Set α)ᶜ),
      ∃ k : fixingSubgroup G ((↑g.support : Set α)ᶜ), x = k • a by
    rw [isPretransitive_iff]
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    obtain ⟨k, hk⟩ := this x hx
    obtain ⟨k', hk'⟩ := this y hy
    use k' * k⁻¹
    rw [← SetLike.coe_eq_coe]
    simp only [SetLike.mk_smul_mk]
    rw [hk, hk', smul_smul, inv_mul_cancel_right]
  intro x hx
  have hg' : (⟨g, hg⟩ : ↥G) ∈ fixingSubgroup G ((↑g.support : Set α)ᶜ) := by
    simp_rw [mem_fixingSubgroup_iff G]
    intro y hy
    simpa only [Set.mem_compl_iff, Finset.mem_coe, notMem_support] using! hy
  let g' : fixingSubgroup (↥G) ((↑g.support : Set α)ᶜ) := ⟨(⟨g, hg⟩ : ↥G), hg'⟩
  obtain ⟨i, hi⟩ := hgc ((hs x).mpr hx)
  exact ⟨g' ^ i, hi.symm⟩

set_option backward.isDefEq.respectTransparency false in
omit [Fintype α] in variable [Finite α] in
/-- A primitive subgroup of `Equiv.Perm α` that contains a swap
is the full permutation group (Jordan). -/
/-
**Equiv.Perm.subgroup_eq_top_of_isPreprimitive_of_isSwap_mem** 是 Mathlib 中的一个定理，
位于命名空间 `Equiv.Perm`。
形式化陈述：subgroup_eq_top_of_isPreprimitive_of_isSwap_mem (hG : IsPreprimitive G α) 
(g : Perm α) (h2g : IsSwap g) (hg : g in G) : G = ⊤
参数：hG : IsPreprimitive G α；g : Perm α；h2g : IsSwap g；hg : g in G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.lt_or_ge`：∀ (n m : ℕ), n < m ∨ n ≥ m
· 使用定理 `Subgroup.eq_top_of_card_eq`：eq_top_of_card_eq [Finite H] (h : Nat.card H
 = Nat.card G) : H = ⊤
· 使用定理 `Subgroup.instFiniteSubtypeMem`：∀ {G : Type u_1} [inst : Group G] (K : Su
bgroup G) [Finite G], Finite ↥K
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Fintype.card_subtype_le`：Fintype.card_subtype_le [Fintype α] (p : α -> P
rop) [Fintype {a // p a}] : Fintype.card { x // p x } <= Fintype.card α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.card_perm`：card_perm : Nat.card (Perm α) = (Nat.card α)!
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Nat.factorial_le`：factorial_le {m n} (h : m <= n) : m ! <= n !
· 使用定理 `Nat.lt_succ_iff`：∀ {m n : ℕ}, m < n.succ ↔ m ≤ n
· 使用定理 `Nat.factorial_two`：Nat.factorial 2 = 2
· 使用定理 `One.instNonempty`：∀ {α : Type u} [One α], Nonempty α
· 使用定理 `Nat.le_of_dvd`：∀ {m n : ℕ}, 0 < n → m ∣ n → m ≤ n
· 使用定理 `Fintype.card_pos`：card_pos [h : Nonempty α] : 0 < card α
· 使用定理 `Equiv.Perm.IsSwap.orderOf`：∀ {α : Type u_1} [inst : DecidableEq α] [Fini
te α] {σ : Equiv.Perm α}, σ.IsSwap → orderOf σ = 2
· 使用定理 `orderOf_submonoid`：orderOf_submonoid {H : Submonoid G} (y : H) : orderOf
 (y : G) = orderOf y
· 使用定理 `orderOf_dvd_card`：orderOf_dvd_card : orderOf x ∣ Fintype.card G
· 使用定理 `Nat.exists_eq_add_of_le'`：∀ {m n : ℕ}, m ≤ n → ∃ k, n = k + m
· 使用定理 `Nat.add_left_cancel`：∀ {n m k : ℕ}, n + m = n + k → m = k
· 使用定理 `Set.ncard_add_ncard_compl`：ncard_add_ncard_compl (s : Set α) (hs : s.Fin
ite
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Set.ncard_coe_finset`：∀ {α : Type u_1} (s : Finset α), (↑s).ncard = s.ca
rd
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.Perm.card_support_eq_two`：card_support_eq_two {f : Perm α} : #f.su
pport = 2 ↔ IsSwap f
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Equiv.Perm.eq_top_of_isMultiplyPretransitive`：∀ {α : Type u_1} [Finite α
] {G : Subgroup (Equiv.Perm α)},   MulAction.IsMultiplyPretransitive (↥G) α (Nat
.card α - 1) → G = ⊤
· 使用定理 `MulAction.IsPreprimitive.isMultiplyPreprimitive`：MulAction.IsPreprimitiv
e.isMultiplyPreprimitive (hG : IsPreprimitive G α) {s : Set α} {n : Nat} (hsn : 
s.ncard = n + 1) (hsn' : n + 2 < Nat.…
（共 47 条，此处仅展示前 30 条）

--- 原说明 ---
A primitive subgroup of `Equiv.Perm α` that contains a swap
is the full permutation group (Jordan).
-/
theorem subgroup_eq_top_of_isPreprimitive_of_isSwap_mem
    (hG : IsPreprimitive G α) (g : Perm α) (h2g : IsSwap g) (hg : g ∈ G) :
    G = ⊤ := by
  classical
  have := Fintype.ofFinite α
  rcases Nat.lt_or_ge (Nat.card α) 3 with hα3 | hα3
  · -- trivial case : Nat.card α ≤ 2
    rw [Nat.lt_succ_iff] at hα3
    apply Subgroup.eq_top_of_card_eq
    simp only [Nat.card_eq_fintype_card]
    apply le_antisymm (Fintype.card_subtype_le _)
    rw [← Nat.card_eq_fintype_card, Nat.card_perm]
    refine le_trans (Nat.factorial_le hα3) ?_
    rw [Nat.factorial_two]
    have : Nonempty G := One.instNonempty
    apply Nat.le_of_dvd Fintype.card_pos
    rw [← h2g.orderOf, orderOf_submonoid ⟨g, hg⟩]
    exact orderOf_dvd_card
  -- important case : Nat.card α ≥ 3
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le' hα3
  have hsc : Set.ncard ((g.support)ᶜ : Set α) = n + 1 := by
    apply Nat.add_left_cancel
    rw [Set.ncard_add_ncard_compl, Set.ncard_coe_finset,
      card_support_eq_two.mpr h2g, add_comm, hn]
  apply eq_top_of_isMultiplyPretransitive
  suffices IsMultiplyPreprimitive G α (Nat.card α - 1) by
    apply IsMultiplyPreprimitive.isMultiplyPretransitive
  rw [show Nat.card α - 1 = n + 2 by grind]
  apply hG.isMultiplyPreprimitive hsc
  · rw [hn]; apply Nat.lt_add_one
  have := isPretransitive_of_isCycle_mem h2g.isCycle hg
  apply IsPreprimitive.of_prime_card
  convert! Nat.prime_two
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, ← card_support_eq_two.mpr h2g]
  simp [SubMulAction.mem_ofFixingSubgroup_iff, support]

/-- A primitive subgroup of `Equiv.Perm α` that contains a 3-cycle
contains the alternating group (Jordan). -/
/-
**Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem** 是 Mathl
ib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem (hG : IsPreprimi
tive G α) {g : Perm α} (h3g : IsThreeCycle g) (hg : g in G) : alternatingGroup α
 <= G
参数：hG : IsPreprimitive G α；h3g : IsThreeCycle g；hg : g in G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.lt_or_ge`：∀ (n m : ℕ), n < m ∨ n ≥ m
· 使用定理 `Equiv.Perm.alternatingGroup_le_of_index_le_two`：alternatingGroup_le_of_i
ndex_le_two {G : Subgroup (Equiv.Perm α)} (hG : G.index <= 2) : alternatingGroup
 α <= G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.mul_le_mul_right_iff`：∀ {n m k : ℕ}, 0 < k → (n * k ≤ m * k ↔ n ≤ m)
· 使用定理 `Nat.card_pos`：∀ {α : Type u_1} [Nonempty α] [Finite α], 0 < Nat.card α
· 使用定理 `One.instNonempty`：∀ {α : Type u} [One α], Nonempty α
· 使用定理 `Subgroup.instFiniteSubtypeMem`：∀ {G : Type u_1} [inst : Group G] (K : Su
bgroup G) [Finite G], Finite ↥K
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Subgroup.index_mul_card`：index_mul_card : H.index * Nat.card H = Nat.car
d G
· 使用定理 `Nat.card_perm`：card_perm : Nat.card (Perm α) = (Nat.card α)!
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Nat.factorial_le`：factorial_le {m n} (h : m <= n) : m ! <= n !
· 使用定理 `Nat.lt_succ_iff`：∀ {m n : ℕ}, m < n.succ ↔ m ≤ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `Nat.le_of_dvd`：∀ {m n : ℕ}, 0 < n → m ∣ n → m ≤ n
· 使用引理 `Subgroup.orderOf_mk`：orderOf_mk (a : G) (ha) : orderOf (⟨a, ha⟩ : H) = o
rderOf a
· 使用定理 `Equiv.Perm.IsThreeCycle.orderOf`：orderOf {g : Perm α} (ht : IsThreeCycle
 g) : orderOf g = 3
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `orderOf_dvd_card`：orderOf_dvd_card : orderOf x ∣ Fintype.card G
· 使用定理 `Nat.exists_eq_add_of_le'`：∀ {m n : ℕ}, m ≤ n → ∃ k, n = k + m
（共 52 条，此处仅展示前 30 条）

--- 原说明 ---
A primitive subgroup of `Equiv.Perm α` that contains a 3-cycle
contains the alternating group (Jordan).
-/
theorem alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem
    (hG : IsPreprimitive G α) {g : Perm α} (h3g : IsThreeCycle g) (hg : g ∈ G) :
    alternatingGroup α ≤ G := by
  classical
  rcases Nat.lt_or_ge (Nat.card α) 4 with hα4 | hα4
  · -- trivial case : Fintype.card α ≤ 3
    rw [Nat.lt_succ_iff] at hα4
    apply alternatingGroup_le_of_index_le_two
    rw [← Nat.mul_le_mul_right_iff (k := Nat.card G) (Nat.card_pos),
      Subgroup.index_mul_card, Nat.card_perm]
    apply le_trans (Nat.factorial_le hα4)
    rw [show Nat.factorial 3 = 2 * 3 by simp [Nat.factorial]]
    simp only [mul_le_mul_iff_right₀, Nat.succ_pos]
    apply Nat.le_of_dvd Nat.card_pos
    suffices 3 = orderOf (⟨g, hg⟩ : G) by
      rw [this, Nat.card_eq_fintype_card]
      exact orderOf_dvd_card
    simp only [orderOf_mk, h3g.orderOf]
    -- important case : Nat.card α ≥ 4
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le' hα4
  apply IsMultiplyPretransitive.alternatingGroup_le
  suffices IsMultiplyPreprimitive G α (Nat.card α - 2) from
    IsMultiplyPreprimitive.isMultiplyPretransitive ..
  rw [show Nat.card α - 2 = n + 2 by grind]
  apply hG.isMultiplyPreprimitive (s := (g.supportᶜ : Set α))
  · apply Nat.add_left_cancel
    rw [Set.ncard_add_ncard_compl, Set.ncard_coe_finset,
      h3g.card_support, add_comm, hn]
  · grind
  have := isPretransitive_of_isCycle_mem h3g.isCycle hg
  apply IsPreprimitive.of_prime_card
  convert! Nat.prime_three
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, ← h3g.card_support]
  apply congr_arg
  ext x
  simp [SubMulAction.mem_ofFixingSubgroup_iff]

/-- A primitive subgroup of `Equiv.Perm α` that contains a cycle of prime order
contains the alternating group. -/
proof_wanted alternatingGroup_le_of_isPreprimitive_of_isCycle_mem
  (hG : IsPreprimitive G α)
  {p : ℕ} (hp : p.Prime) (hp' : p + 3 ≤ Nat.card α)
  {g : Perm α} (hgc : g.IsCycle) (hgp : g.support.card = p)
  (hg : g ∈ G) : alternatingGroup α ≤ G

end Equiv.Perm

end Subgroups

