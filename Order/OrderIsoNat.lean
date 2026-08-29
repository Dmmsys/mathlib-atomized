/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Set.Subsingleton
public import Mathlib.Logic.Denumerable
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Lattice.Nat

/-!
# Relation embeddings from the naturals

This file allows translation from monotone functions `ℕ → α` to order embeddings `ℕ ↪ α` and
defines the limit value of an eventually-constant sequence.

## Main declarations

* `natLT`/`natGT`: Make an order embedding `Nat ↪ α` from
  an increasing/decreasing function `Nat → α`.
* `Infinite.exists_strictMono_or_strictAnti`: Every infinite linear order contains a strictly
  increasing or strictly decreasing sequence indexed by `ℕ`.
* `Finite.of_wellFoundedLT_wellFoundedGT`: A linear order that is well-founded in both directions
  is finite.
* `monotonicSequenceLimit`: The limit of an eventually-constant monotone sequence `Nat →o α`.
* `monotonicSequenceLimitIndex`: The index of the first occurrence of `monotonicSequenceLimit`
  in the sequence.
-/

@[expose] public section


variable {α : Type*}

namespace RelEmbedding

variable {r : α -> α -> Prop} [IsStrictOrder α r]

/--
Definition of `natLT` / `natLT` 的定义

English:
definition natLT
  signature: (f : Nat -> α) (H : forall n : Nat, r (f n) (f (n + 1)))
  body: ofMonotone f Nat.rel_of_forall_rel_succ_of_lt r H

@[simp]

中文:
定义 natLT
  签名: (f : 自然数 -> α) (H : 对任意 n : 自然数, r (f n) (f (n + 1)))
  定义体: ofMonotone f Nat.rel_of_forall_rel_succ_of_lt r H

@[simp]

Depends on / 依赖: Nat.rel_of_forall_rel_succ_of_lt, ofMonotone, rel_of_forall_rel_succ_of_lt
-/
def natLT (f : Nat -> α) (H : forall n : Nat, r (f n) (f (n + 1))) : ((· < ·) : Nat -> Nat -> Prop) ↪r r :=
ofMonotone f Nat.rel_of_forall_rel_succ_of_lt r H

@[simp]
/--
theorem `coe_natLT` / 定理 `coe_natLT`

English:
theorem coe_natLT
  given: {f : Nat -> α} {H : forall n : Nat, r (f n) (f (n + 1))}
  statement: ⇑(natLT f H) = f
  proof: rfl

中文:
定理 coe_natLT
  条件: {f : 自然数 -> α} {H : 对任意 n : 自然数, r (f n) (f (n + 1))}
  结论: ⇑(natLT f H) = f
  证明: rfl
-/
theorem coe_natLT {f : Nat -> α} {H : forall n : Nat, r (f n) (f (n + 1))} : ⇑(natLT f H) = f :=
  rfl

/--
Definition of `natGT` / `natGT` 的定义

English:
definition natGT
  signature: (f : Nat -> α) (H : forall n : Nat, r (f (n + 1)) (f n))
  body: RelEmbedding.swap (natLT f H)

@[simp]

中文:
定义 natGT
  签名: (f : 自然数 -> α) (H : 对任意 n : 自然数, r (f (n + 1)) (f n))
  定义体: RelEmbedding.swap (natLT f H)

@[simp]

Depends on / 依赖: RelEmbedding, RelEmbedding.swap
-/
def natGT (f : Nat -> α) (H : forall n : Nat, r (f (n + 1)) (f n)) : ((· > ·) : Nat -> Nat -> Prop) ↪r r :=
  RelEmbedding.swap (natLT f H)

@[simp]
/--
theorem `coe_natGT` / 定理 `coe_natGT`

English:
theorem coe_natGT
  given: {f : Nat -> α} {H : forall n : Nat, r (f (n + 1)) (f n)}
  statement: ⇑(natGT f H) = f
  proof: rfl

中文:
定理 coe_natGT
  条件: {f : 自然数 -> α} {H : 对任意 n : 自然数, r (f (n + 1)) (f n)}
  结论: ⇑(natGT f H) = f
  证明: rfl
-/
theorem coe_natGT {f : Nat -> α} {H : forall n : Nat, r (f (n + 1)) (f n)} : ⇑(natGT f H) = f :=
  rfl

/--
theorem `acc_iff_isEmpty_subtype_mem_range` / 定理 `acc_iff_isEmpty_subtype_mem_range`

English:
theorem acc_iff_isEmpty_subtype_mem_range
  given: {x}
  proof: .mk fun ⟨f, k, hk⟩ => not_acc_iff_exists_descending_chain.mpr
    ⟨(f <| k + ·), hk, fun _n => f.map_rel_iff.2 (Nat.lt_succ_self _)⟩ acc
  mpr h := of_not_not fun nacc =>
    have ⟨f, hf⟩ := not_acc_iff_exists_descending_chain.mp nacc
    h.elim ⟨natGT f hf.2, 0, hf.1⟩

中文:
定理 acc_iff_isEmpty_subtype_mem_range
  条件: {x}
  证明: .mk fun ⟨f, k, hk⟩ => not_acc_iff_exists_descending_chain.mpr
    ⟨(f <| k + ·), hk, fun _n => f.map_rel_iff.2 (Nat.lt_succ_self _)⟩ acc
  mpr h := of_not_not fun nacc =>
    have ⟨f, hf⟩ := not_acc_iff_exists_descending_chain.mp nacc
    h.elim ⟨natGT f hf.2, 0, hf.1⟩

Depends on / 依赖: not_acc_iff_exists_descending_chain, not_acc_iff_exists_descending_chain.mpr
-/
theorem acc_iff_isEmpty_subtype_mem_range {x} :
    Acc r x ↔ IsEmpty { f : ((· > ·) : Nat -> Nat -> Prop) ↪r r // x in Set.range f } where
  mp acc := .mk fun ⟨f, k, hk⟩ => not_acc_iff_exists_descending_chain.mpr
    ⟨(f <| k + ·), hk, fun _n => f.map_rel_iff.2 (Nat.lt_succ_self _)⟩ acc
  mpr h := of_not_not fun nacc =>
    have ⟨f, hf⟩ := not_acc_iff_exists_descending_chain.mp nacc
    h.elim ⟨natGT f hf.2, 0, hf.1⟩

/--
theorem `not_acc` / 定理 `not_acc`

English:
theorem not_acc
  given: (f : ((· > ·) : Nat -> Nat -> Prop) ↪r r) (k : Nat)
  statement: ¬Acc r (f k)
  proof: by
  rw [acc_iff_isEmpty_subtype_mem_range]; rw [not_isEmpty_iff]
  exact ⟨⟨f, k, rfl⟩⟩

中文:
定理 not_acc
  条件: (f : ((· > ·) : 自然数 -> 自然数 -> 命题) ↪r r) (k : 自然数)
  结论: ¬Acc r (f k)
  证明: by
  rw [acc_iff_isEmpty_subtype_mem_range]; rw [not_isEmpty_iff]
  exact ⟨⟨f, k, rfl⟩⟩

Depends on / 依赖: acc_iff_isEmpty_subtype_mem_range, not_isEmpty_iff
-/
theorem not_acc (f : ((· > ·) : Nat -> Nat -> Prop) ↪r r) (k : Nat) : ¬Acc r (f k) := by
  rw [acc_iff_isEmpty_subtype_mem_range]; rw [not_isEmpty_iff]
  exact ⟨⟨f, k, rfl⟩⟩

/--
theorem `wellFounded_iff_isEmpty` / 定理 `wellFounded_iff_isEmpty`

English:
theorem wellFounded_iff_isEmpty
  proof: fun ⟨h⟩ => ⟨fun f => f.not_acc 0 (h _)⟩
  mpr _ := ⟨fun _x => acc_iff_isEmpty_subtype_mem_range.2 inferInstance⟩

中文:
定理 wellFounded_iff_isEmpty
  证明: fun ⟨h⟩ => ⟨fun f => f.not_acc 0 (h _)⟩
  mpr _ := ⟨fun _x => acc_iff_isEmpty_subtype_mem_range.2 inferInstance⟩

Depends on / 依赖: f.not_acc, not_acc
-/
theorem wellFounded_iff_isEmpty :
    WellFounded r ↔ IsEmpty (((· > ·) : Nat -> Nat -> Prop) ↪r r) where
  mp := fun ⟨h⟩ => ⟨fun f => f.not_acc 0 (h _)⟩
  mpr _ := ⟨fun _x => acc_iff_isEmpty_subtype_mem_range.2 inferInstance⟩

/--
theorem `not_wellFounded` / 定理 `not_wellFounded`

English:
theorem not_wellFounded
  given: (f : ((· > ·) : Nat -> Nat -> Prop) ↪r r)
  statement: ¬WellFounded r
  proof: by
  rw [wellFounded_iff_isEmpty]; rw [not_isEmpty_iff]
  exact ⟨f⟩

中文:
定理 not_wellFounded
  条件: (f : ((· > ·) : 自然数 -> 自然数 -> 命题) ↪r r)
  结论: ¬良基 r
  证明: by
  rw [wellFounded_iff_isEmpty]; rw [not_isEmpty_iff]
  exact ⟨f⟩

Depends on / 依赖: not_isEmpty_iff, wellFounded_iff_isEmpty
-/
theorem not_wellFounded (f : ((· > ·) : Nat -> Nat -> Prop) ↪r r) : ¬WellFounded r := by
  rw [wellFounded_iff_isEmpty]; rw [not_isEmpty_iff]
  exact ⟨f⟩

end RelEmbedding

/--
theorem `not_strictAnti_of_wellFoundedLT` / 定理 `not_strictAnti_of_wellFoundedLT`

English:
theorem not_strictAnti_of_wellFoundedLT
  given: [Preorder α] [WellFoundedLT α] (f : Nat -> α)
  proof: fun hf =>
  (RelEmbedding.natGT f (fun n => hf (by simp))).not_wellFounded wellFounded_lt

中文:
定理 not_strictAnti_of_wellFoundedLT
  条件: [预序 α] [WellFoundedLT α] (f : 自然数 -> α)
  证明: fun hf =>
  (RelEmbedding.natGT f (fun n => hf (by simp))).not_wellFounded wellFounded_lt
-/
theorem not_strictAnti_of_wellFoundedLT [Preorder α] [WellFoundedLT α] (f : Nat -> α) :
    ¬ StrictAnti f := fun hf =>
  (RelEmbedding.natGT f (fun n => hf (by simp))).not_wellFounded wellFounded_lt

/--
theorem `not_strictMono_of_wellFoundedGT` / 定理 `not_strictMono_of_wellFoundedGT`

English:
theorem not_strictMono_of_wellFoundedGT
  given: [Preorder α] [WellFoundedGT α] (f : Nat -> α)
  proof: not_strictAnti_of_wellFoundedLT (α := αᵒᵈ) f

中文:
定理 not_strictMono_of_wellFoundedGT
  条件: [预序 α] [WellFoundedGT α] (f : 自然数 -> α)
  证明: not_strictAnti_of_wellFoundedLT (α := αᵒᵈ) f

Depends on / 依赖: not_strictAnti_of_wellFoundedLT
-/
theorem not_strictMono_of_wellFoundedGT [Preorder α] [WellFoundedGT α] (f : Nat -> α) :
    ¬ StrictMono f :=
  not_strictAnti_of_wellFoundedLT (α := αᵒᵈ) f

namespace Nat

variable (s : Set Nat) [Infinite s]

/--
Definition of `orderEmbeddingOfSet` / `orderEmbeddingOfSet` 的定义

English:
definition orderEmbeddingOfSet
  signature: [DecidablePred (· in s)]
  body: (RelEmbedding.orderEmbeddingOfLTEmbedding
    (RelEmbedding.natLT (Nat.Subtype.ofNat s) fun _ => Nat.Subtype.lt_succ_self _)).trans
    (OrderEmbedding.subtype (· in s))

中文:
定义 orderEmbeddingOfSet
  签名: [DecidablePred (· in s)]
  定义体: (RelEmbedding.orderEmbeddingOfLTEmbedding
    (RelEmbedding.natLT (Nat.Subtype.ofNat s) fun _ => Nat.Subtype.lt_succ_self _)).trans
    (OrderEmbedding.subtype (· in s))

Depends on / 依赖: IsArtinianRing, IsJacobsonRing, Nat.Subtype.lt_succ_self, Nat.Subtype.ofNat, OrderEmbedding, OrderEmbedding.subtype, RelEmbedding, RelEmbedding.natLT, RelEmbedding.orderEmbeddingOfLTEmbedding, Subtype, lt_succ_self, orderEmbeddingOfLTEmbedding, subtype
-/
def orderEmbeddingOfSet [DecidablePred (· in s)] : Nat ↪o Nat :=
  (RelEmbedding.orderEmbeddingOfLTEmbedding
    (RelEmbedding.natLT (Nat.Subtype.ofNat s) fun _ => Nat.Subtype.lt_succ_self _)).trans
    (OrderEmbedding.subtype (· in s))

/--
Definition of `Subtype.orderIsoOfNat` / `Subtype.orderIsoOfNat` 的定义

English:
definition Subtype.orderIsoOfNat
  signature: : Nat ≃o s
  body: by
  classical
  exact
    RelIso.ofSurjective
      (RelEmbedding.orderEmbeddingOfLTEmbedding
        (RelEmbedding.natLT (Nat.Subtype.ofNat s) fun n => Nat.Subtype.lt_succ_self _))
      Nat.Subtype.ofNat_surjective

中文:
定义 子类型.orderIsoOf自然数
  签名: : 自然数 ≃o s
  定义体: by
  classical
  exact
    RelIso.ofSurjective
      (RelEmbedding.orderEmbeddingOfLTEmbedding
        (RelEmbedding.natLT (Nat.Subtype.ofNat s) fun n => Nat.Subtype.lt_succ_self _))
      Nat.Subtype.ofNat_surjective

Depends on / 依赖: Nat.Subtype.lt_succ_self, Nat.Subtype.ofNat, Nat.Subtype.ofNat_surjective, RelEmbedding, RelEmbedding.natLT, RelEmbedding.orderEmbeddingOfLTEmbedding, RelIso, RelIso.ofSurjective, Subtype, classical, lt_succ_self, ofNat_surjective, ofSurjective, orderEmbeddingOfLTEmbedding
-/
noncomputable def Subtype.orderIsoOfNat : Nat ≃o s := by
  classical
  exact
    RelIso.ofSurjective
      (RelEmbedding.orderEmbeddingOfLTEmbedding
        (RelEmbedding.natLT (Nat.Subtype.ofNat s) fun n => Nat.Subtype.lt_succ_self _))
      Nat.Subtype.ofNat_surjective

variable {s}

@[simp]
/--
theorem `coe_orderEmbeddingOfSet` / 定理 `coe_orderEmbeddingOfSet`

English:
theorem coe_orderEmbeddingOfSet
  given: [DecidablePred (· in s)]
  proof: rfl

中文:
定理 coe_orderEmbeddingOfSet
  条件: [DecidablePred (· in s)]
  证明: rfl

Depends on / 依赖: IsJacobsonRing, isJacobsonRing_quotient
-/
theorem coe_orderEmbeddingOfSet [DecidablePred (· in s)] :
    ⇑(orderEmbeddingOfSet s) = (↑) ∘ Subtype.ofNat s :=
  rfl

/--
theorem `orderEmbeddingOfSet_apply` / 定理 `orderEmbeddingOfSet_apply`

English:
theorem orderEmbeddingOfSet_apply
  given: [DecidablePred (· in s)] {n : Nat}
  proof: rfl

中文:
定理 orderEmbeddingOfSet_apply
  条件: [DecidablePred (· in s)] {n : 自然数}
  证明: rfl
-/
theorem orderEmbeddingOfSet_apply [DecidablePred (· in s)] {n : Nat} :
    orderEmbeddingOfSet s n = Subtype.ofNat s n :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `Subtype.orderIsoOfNat_apply` / 定理 `Subtype.orderIsoOfNat_apply`

English:
theorem Subtype.orderIsoOfNat_apply
  given: [dP : DecidablePred (· in s)] {n : Nat}
  proof: by
  simp only [orderIsoOfNat, RelIso.ofSurjective_apply,
    RelEmbedding.orderEmbeddingOfLTEmbedding_apply, RelEmbedding.coe_natLT]
  congr!

中文:
定理 子类型.orderIsoOf自然数_apply
  条件: [dP : DecidablePred (· in s)] {n : 自然数}
  证明: by
  simp only [orderIsoOfNat, RelIso.ofSurjective_apply,
    RelEmbedding.orderEmbeddingOfLTEmbedding_apply, RelEmbedding.coe_natLT]
  congr!

Depends on / 依赖: RelEmbedding, RelEmbedding.coe_natLT, RelEmbedding.orderEmbeddingOfLTEmbedding_apply, RelIso, RelIso.ofSurjective_apply, coe_natLT, ofSurjective_apply, orderEmbeddingOfLTEmbedding_apply, orderIsoOfNat
-/
theorem Subtype.orderIsoOfNat_apply [dP : DecidablePred (· in s)] {n : Nat} :
    Subtype.orderIsoOfNat s n = Subtype.ofNat s n := by
  simp only [orderIsoOfNat, RelIso.ofSurjective_apply,
    RelEmbedding.orderEmbeddingOfLTEmbedding_apply, RelEmbedding.coe_natLT]
  congr!

variable (s)

/--
theorem `orderEmbeddingOfSet_range` / 定理 `orderEmbeddingOfSet_range`

English:
theorem orderEmbeddingOfSet_range
  given: [DecidablePred (· in s)]
  proof: Subtype.coe_comp_ofNat_range

中文:
定理 orderEmbeddingOfSet_range
  条件: [DecidablePred (· in s)]
  证明: Subtype.coe_comp_ofNat_range

Depends on / 依赖: Subtype, Subtype.coe_comp_ofNat_range, coe_comp_ofNat_range
-/
theorem orderEmbeddingOfSet_range [DecidablePred (· in s)] :
    Set.range (Nat.orderEmbeddingOfSet s) = s :=
  Subtype.coe_comp_ofNat_range

/--
theorem `exists_subseq_of_forall_mem_union` / 定理 `exists_subseq_of_forall_mem_union`

English:
theorem exists_subseq_of_forall_mem_union
  given: {s t : Set α} (e : Nat -> α) (he : forall n, e n in s union t)
  proof: by
  classical
    have : Infinite (e ⁻¹' s) ∨ Infinite (e ⁻¹' t) := by
      simp only [Set.infinite_coe_iff, ← Set.infinite_union, ← Set.preimage_union,
        Set.eq_univ_of_forall fun n => Set.mem_preimage.2 (he n), Set.infinite_univ]
    cases this
    exacts [⟨Nat.orderEmbeddingOfSet (e ⁻¹' s), Or.inl fun n => (Nat.Subtype.ofNat (e ⁻¹' s) _).2⟩,
      ⟨Nat.orderEmbeddingOfSet (e ⁻¹' t), Or.inr fun n => (Nat.Subtype.ofNat (e ⁻¹' t) _).2⟩]

中文:
定理 存在_subseq_of_对任意_mem_union
  条件: {s t : 集合 α} (e : 自然数 -> α) (he : 对任意 n, e n in s union t)
  证明: by
  classical
    have : Infinite (e ⁻¹' s) ∨ Infinite (e ⁻¹' t) := by
      simp only [Set.infinite_coe_iff, ← Set.infinite_union, ← Set.preimage_union,
        Set.eq_univ_of_forall fun n => Set.mem_preimage.2 (he n), Set.infinite_univ]
    cases this
    exacts [⟨Nat.orderEmbeddingOfSet (e ⁻¹' s), Or.inl fun n => (Nat.Subtype.ofNat (e ⁻¹' s) _).2⟩,
      ⟨Nat.orderEmbeddingOfSet (e ⁻¹' t), Or.inr fun n => (Nat.Subtype.ofNat (e ⁻¹' t) _).2⟩]

Depends on / 依赖: Infinite, Nat.Subtype.ofNat, Nat.orderEmbeddingOfSet, Or.inl, Or.inr, Set.eq_univ_of_forall, Set.infinite_coe_iff, Set.infinite_union, Set.infinite_univ, Set.mem_preimage, Set.preimage_union, Subtype, classical, eq_univ_of_forall, exacts, infinite_coe_iff, infinite_union, infinite_univ, mem_preimage, orderEmbeddingOfSet
-/
theorem exists_subseq_of_forall_mem_union {s t : Set α} (e : Nat -> α) (he : forall n, e n in s union t) :
    exists g : Nat ↪o Nat, (forall n, e (g n) in s) ∨ forall n, e (g n) in t := by
  classical
    have : Infinite (e ⁻¹' s) ∨ Infinite (e ⁻¹' t) := by
      simp only [Set.infinite_coe_iff, ← Set.infinite_union, ← Set.preimage_union,
        Set.eq_univ_of_forall fun n => Set.mem_preimage.2 (he n), Set.infinite_univ]
    cases this
    exacts [⟨Nat.orderEmbeddingOfSet (e ⁻¹' s), Or.inl fun n => (Nat.Subtype.ofNat (e ⁻¹' s) _).2⟩,
      ⟨Nat.orderEmbeddingOfSet (e ⁻¹' t), Or.inr fun n => (Nat.Subtype.ofNat (e ⁻¹' t) _).2⟩]

end Nat

/--
theorem `exists_increasing_or_nonincreasing_subseq'` / 定理 `exists_increasing_or_nonincreasing_subseq'`

English:
theorem exists_increasing_or_nonincreasing_subseq'
  given: (r : α -> α -> Prop) (f : Nat -> α)
  proof: by
  classical
    let bad : Set Nat := { m | forall n, m < n -> ¬r (f m) (f n) }
    by_cases hbad : Infinite bad
    · refine ⟨Nat.orderEmbeddingOfSet bad, Or.intro_right _ fun m n mn => ?_⟩
      have h := @Set.mem_range_self _ _ ↑(Nat.orderEmbeddingOfSet bad) m
      rw [Nat.orderEmbeddingOfSet_range bad] at h
      exact h _ ((OrderEmbedding.lt_iff_lt _).2 mn)
    · rw [Set.infinite_coe_iff, Set.Infinite, not_not] at hbad
      obtain ⟨m, hm⟩ : exists m, forall n, m <= n -> n ∉ bad := by
        by_cases he : hbad.toFinset.Nonempty
        · refine
            ⟨(hbad.toFinset.max' he).succ, fun n hn nbad =>
              Nat.not_succ_le_self _
                (hn.trans (hbad.toFinset.le_max' n (hbad.mem_toFinset.2 nbad)))⟩
        · exact ⟨0, fun n _ nbad => he ⟨n, hbad.mem_toFinset.2 nbad⟩⟩
      have h : forall n : Nat, exists n' : Nat, n < n' ∧ r (f (n + m)) (f (n' + m)) := by
        intro n
        have h := hm _ (Nat.le_add_left m n)
        simp only [bad, exists_prop, not_not, Set.mem_ofPred_eq, not_forall] at h
        obtain ⟨n', hn1, hn2⟩ := h
        refine ⟨n + n' - n - m, by lia, ?_⟩
        convert! hn2
        lia
      let g' : Nat -> Nat := @Nat.rec (fun _ => Nat) m fun n gn => Nat.find (h gn)
      exact
        ⟨(RelEmbedding.natLT (fun n => g' n + m) fun n =>
              Nat.add_lt_add_right (Nat.find_spec (h (g' n))).1 m).orderEmbeddingOfLTEmbedding,
          Or.intro_left _ fun n => (Nat.find_spec (h (g' n))).2⟩

中文:
定理 存在_increasing_or_nonincreasing_subseq'
  条件: (r : α -> α -> 命题) (f : 自然数 -> α)
  证明: by
  classical
    let bad : Set Nat := { m | forall n, m < n -> ¬r (f m) (f n) }
    by_cases hbad : Infinite bad
    · refine ⟨Nat.orderEmbeddingOfSet bad, Or.intro_right _ fun m n mn => ?_⟩
      have h := @Set.mem_range_self _ _ ↑(Nat.orderEmbeddingOfSet bad) m
      rw [Nat.orderEmbeddingOfSet_range bad] at h
      exact h _ ((OrderEmbedding.lt_iff_lt _).2 mn)
    · rw [Set.infinite_coe_iff, Set.Infinite, not_not] at hbad
      obtain ⟨m, hm⟩ : exists m, forall n, m <= n -> n ∉ bad := by
        by_cases he : hbad.toFinset.Nonempty
        · refine
            ⟨(hbad.toFinset.max' he).succ, fun n hn nbad =>
              Nat.not_succ_le_self _
                (hn.trans (hbad.toFinset.le_max' n (hbad.mem_toFinset.2 nbad)))⟩
        · exact ⟨0, fun n _ nbad => he ⟨n, hbad.mem_toFinset.2 nbad⟩⟩
      have h : forall n : Nat, exists n' : Nat, n < n' ∧ r (f (n + m)) (f (n' + m)) := by
        intro n
        have h := hm _ (Nat.le_add_left m n)
        simp only [bad, exists_prop, not_not, Set.mem_ofPred_eq, not_forall] at h
        obtain ⟨n', hn1, hn2⟩ := h
        refine ⟨n + n' - n - m, by lia, ?_⟩
        convert! hn2
        lia
      let g' : Nat -> Nat := @Nat.rec (fun _ => Nat) m fun n gn => Nat.find (h gn)
      exact
        ⟨(RelEmbedding.natLT (fun n => g' n + m) fun n =>
              Nat.add_lt_add_right (Nat.find_spec (h (g' n))).1 m).orderEmbeddingOfLTEmbedding,
          Or.intro_left _ fun n => (Nat.find_spec (h (g' n))).2⟩

Depends on / 依赖: Infinite, Nat.orderEmbeddingOfSet, Nat.orderEmbeddingOfSet_range, Nonempty, Or.intro_right, OrderEmbedding, OrderEmbedding.lt_iff_lt, Set.Infinite, Set.infinite_coe_iff, Set.mem_range_self, classical, hbad.toFinset.Nonempty, infinite_coe_iff, intro_right, lt_iff_lt, mem_range_self, not_not, orderEmbeddingOfSet, orderEmbeddingOfSet_range, toFinset
-/
theorem exists_increasing_or_nonincreasing_subseq' (r : α -> α -> Prop) (f : Nat -> α) :
    exists g : Nat ↪o Nat,
      (forall n : Nat, r (f (g n)) (f (g (n + 1)))) ∨ forall m n : Nat, m < n -> ¬r (f (g m)) (f (g n)) := by
  classical
    let bad : Set Nat := { m | forall n, m < n -> ¬r (f m) (f n) }
    by_cases hbad : Infinite bad
    · refine ⟨Nat.orderEmbeddingOfSet bad, Or.intro_right _ fun m n mn => ?_⟩
      have h := @Set.mem_range_self _ _ ↑(Nat.orderEmbeddingOfSet bad) m
      rw [Nat.orderEmbeddingOfSet_range bad] at h
      exact h _ ((OrderEmbedding.lt_iff_lt _).2 mn)
    · rw [Set.infinite_coe_iff, Set.Infinite, not_not] at hbad
      obtain ⟨m, hm⟩ : exists m, forall n, m <= n -> n ∉ bad := by
        by_cases he : hbad.toFinset.Nonempty
        · refine
            ⟨(hbad.toFinset.max' he).succ, fun n hn nbad =>
              Nat.not_succ_le_self _
                (hn.trans (hbad.toFinset.le_max' n (hbad.mem_toFinset.2 nbad)))⟩
        · exact ⟨0, fun n _ nbad => he ⟨n, hbad.mem_toFinset.2 nbad⟩⟩
      have h : forall n : Nat, exists n' : Nat, n < n' ∧ r (f (n + m)) (f (n' + m)) := by
        intro n
        have h := hm _ (Nat.le_add_left m n)
        simp only [bad, exists_prop, not_not, Set.mem_ofPred_eq, not_forall] at h
        obtain ⟨n', hn1, hn2⟩ := h
        refine ⟨n + n' - n - m, by lia, ?_⟩
        convert! hn2
        lia
      let g' : Nat -> Nat := @Nat.rec (fun _ => Nat) m fun n gn => Nat.find (h gn)
      exact
        ⟨(RelEmbedding.natLT (fun n => g' n + m) fun n =>
              Nat.add_lt_add_right (Nat.find_spec (h (g' n))).1 m).orderEmbeddingOfLTEmbedding,
          Or.intro_left _ fun n => (Nat.find_spec (h (g' n))).2⟩

/--
theorem `exists_increasing_or_nonincreasing_subseq` / 定理 `exists_increasing_or_nonincreasing_subseq`

English:
theorem exists_increasing_or_nonincreasing_subseq
  given: (r : α -> α -> Prop) [IsTrans α r] (f : Nat -> α)
  proof: by
  obtain ⟨g, hr | hnr⟩ := exists_increasing_or_nonincreasing_subseq' r f
  · refine ⟨g, Or.intro_left _ fun m n mn => ?_⟩
    obtain ⟨x, rfl⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_iff.2 mn)
    induction x with
    | zero => apply hr
    | succ x ih =>
      apply IsTrans.trans _ _ _ _ (hr _)
      exact ih (lt_of_lt_of_le m.lt_succ_self (Nat.le_add_right _ _))
  · exact ⟨g, Or.intro_right _ hnr⟩

中文:
定理 存在_increasing_or_nonincreasing_subseq
  条件: (r : α -> α -> 命题) [是Trans α r] (f : 自然数 -> α)
  证明: by
  obtain ⟨g, hr | hnr⟩ := exists_increasing_or_nonincreasing_subseq' r f
  · refine ⟨g, Or.intro_left _ fun m n mn => ?_⟩
    obtain ⟨x, rfl⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_iff.2 mn)
    induction x with
    | zero => apply hr
    | succ x ih =>
      apply IsTrans.trans _ _ _ _ (hr _)
      exact ih (lt_of_lt_of_le m.lt_succ_self (Nat.le_add_right _ _))
  · exact ⟨g, Or.intro_right _ hnr⟩

Depends on / 依赖: IsTrans, IsTrans.trans, Nat.exists_eq_add_of_le, Nat.le_add_right, Nat.succ_le_iff, Or.intro_left, Or.intro_right, exists_eq_add_of_le, exists_increasing_or_nonincreasing_subseq, intro_left, intro_right, le_add_right, lt_of_lt_of_le, lt_succ_self, m.lt_succ_self, succ_le_iff
-/
theorem exists_increasing_or_nonincreasing_subseq (r : α -> α -> Prop) [IsTrans α r] (f : Nat -> α) :
    exists g : Nat ↪o Nat,
      (forall m n : Nat, m < n -> r (f (g m)) (f (g n))) ∨ forall m n : Nat, m < n -> ¬r (f (g m)) (f (g n)) := by
  obtain ⟨g, hr | hnr⟩ := exists_increasing_or_nonincreasing_subseq' r f
  · refine ⟨g, Or.intro_left _ fun m n mn => ?_⟩
    obtain ⟨x, rfl⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_iff.2 mn)
    induction x with
    | zero => apply hr
    | succ x ih =>
      apply IsTrans.trans _ _ _ _ (hr _)
      exact ih (lt_of_lt_of_le m.lt_succ_self (Nat.le_add_right _ _))
  · exact ⟨g, Or.intro_right _ hnr⟩

/--
theorem `Infinite.exists_strictMono_or_strictAnti` / 定理 `Infinite.exists_strictMono_or_strictAnti`

English:
theorem Infinite.exists_strictMono_or_strictAnti
  given: (α : Type*) [LinearOrder α] [Infinite α]
  proof: by
  let f := Infinite.natEmbedding α
  obtain ⟨g, hg⟩ := exists_increasing_or_nonincreasing_subseq (· < ·) f
  refine ⟨f ∘ g, ?_⟩
  rcases hg with hIncreasing | hNonincreasing
  · exact Or.inl hIncreasing
· refine Or.inr fun m n hmn => lt_of_le_of_ne ?_ ((f.injective.comp g.injective).ne ?_)
    · grind
    · grind

中文:
定理 无限.存在_strictMono_or_strictAnti
  条件: (α : 类型) [线性序 α] [无限 α]
  证明: by
  let f := Infinite.natEmbedding α
  obtain ⟨g, hg⟩ := exists_increasing_or_nonincreasing_subseq (· < ·) f
  refine ⟨f ∘ g, ?_⟩
  rcases hg with hIncreasing | hNonincreasing
  · exact Or.inl hIncreasing
· refine Or.inr fun m n hmn => lt_of_le_of_ne ?_ ((f.injective.comp g.injective).ne ?_)
    · grind
    · grind

Depends on / 依赖: Infinite, Infinite.natEmbedding, Or.inl, Or.inr, exists_increasing_or_nonincreasing_subseq, f.injective.comp, g.injective, hIncreasing, hNonincreasing, injective, lt_of_le_of_ne, natEmbedding
-/
theorem Infinite.exists_strictMono_or_strictAnti (α : Type*) [LinearOrder α] [Infinite α] :
    exists f : Nat -> α, StrictMono f ∨ StrictAnti f := by
  let f := Infinite.natEmbedding α
  obtain ⟨g, hg⟩ := exists_increasing_or_nonincreasing_subseq (· < ·) f
  refine ⟨f ∘ g, ?_⟩
  rcases hg with hIncreasing | hNonincreasing
  · exact Or.inl hIncreasing
· refine Or.inr fun m n hmn => lt_of_le_of_ne ?_ ((f.injective.comp g.injective).ne ?_)
    · grind
    · grind

/--
theorem `Finite.of_wellFoundedLT_wellFoundedGT` / 定理 `Finite.of_wellFoundedLT_wellFoundedGT`

English:
theorem Finite.of_wellFoundedLT_wellFoundedGT
  statement: (α : Type*) [LinearOrder α]
  proof: by
  apply Finite.of_not_infinite
  intro
  obtain ⟨f, hStrictMono | hStrictAnti⟩ := Infinite.exists_strictMono_or_strictAnti α
  · exact not_strictMono_of_wellFoundedGT f hStrictMono
  · exact not_strictAnti_of_wellFoundedLT f hStrictAnti

中文:
定理 有限.of_wellFoundedLT_wellFoundedGT
  结论: (α : 类型) [线性序 α]
  证明: by
  apply Finite.of_not_infinite
  intro
  obtain ⟨f, hStrictMono | hStrictAnti⟩ := Infinite.exists_strictMono_or_strictAnti α
  · exact not_strictMono_of_wellFoundedGT f hStrictMono
  · exact not_strictAnti_of_wellFoundedLT f hStrictAnti

Depends on / 依赖: Finite, Finite.of_not_infinite, Infinite, Infinite.exists_strictMono_or_strictAnti, exists_strictMono_or_strictAnti, hStrictAnti, hStrictMono, not_strictAnti_of_wellFoundedLT, not_strictMono_of_wellFoundedGT, of_not_infinite
-/
theorem Finite.of_wellFoundedLT_wellFoundedGT (α : Type*) [LinearOrder α]
    [WellFoundedLT α] [WellFoundedGT α] : Finite α := by
  apply Finite.of_not_infinite
  intro
  obtain ⟨f, hStrictMono | hStrictAnti⟩ := Infinite.exists_strictMono_or_strictAnti α
  · exact not_strictMono_of_wellFoundedGT f hStrictMono
  · exact not_strictAnti_of_wellFoundedLT f hStrictAnti

/--
theorem `wellFoundedGT_iff_monotone_chain_condition'` / 定理 `wellFoundedGT_iff_monotone_chain_condition'`

English:
theorem wellFoundedGT_iff_monotone_chain_condition'
  given: [Preorder α]
  proof: by
  refine ⟨fun h a => ?_, fun h => ?_⟩
  · obtain ⟨x, ⟨n, rfl⟩, H⟩ := h.wf.has_min _ (Set.range_nonempty a)
    exact ⟨n, fun m _ => H _ (Set.mem_range_self _)⟩
  · rw [WellFoundedGT, isWellFounded_iff, RelEmbedding.wellFounded_iff_isEmpty]
    refine ⟨fun a => ?_⟩
    obtain ⟨n, hn⟩ := h (a.swap : _ ->r _).toOrderHom
    exact hn n.succ n.lt_succ_self.le ((RelEmbedding.map_rel_iff _).2 n.lt_succ_self)

中文:
定理 wellFoundedGT_iff_monotone_chain_condition'
  条件: [预序 α]
  证明: by
  refine ⟨fun h a => ?_, fun h => ?_⟩
  · obtain ⟨x, ⟨n, rfl⟩, H⟩ := h.wf.has_min _ (Set.range_nonempty a)
    exact ⟨n, fun m _ => H _ (Set.mem_range_self _)⟩
  · rw [WellFoundedGT, isWellFounded_iff, RelEmbedding.wellFounded_iff_isEmpty]
    refine ⟨fun a => ?_⟩
    obtain ⟨n, hn⟩ := h (a.swap : _ ->r _).toOrderHom
    exact hn n.succ n.lt_succ_self.le ((RelEmbedding.map_rel_iff _).2 n.lt_succ_self)

Depends on / 依赖: RelEmbedding, RelEmbedding.map_rel_iff, RelEmbedding.wellFounded_iff_isEmpty, Set.mem_range_self, Set.range_nonempty, WellFoundedGT, a.swap, h.wf.has_min, has_min, isWellFounded_iff, lt_succ_self, map_rel_iff, mem_range_self, n.lt_succ_self, n.lt_succ_self.le, n.succ, range_nonempty, toOrderHom, wellFounded_iff_isEmpty
-/
theorem wellFoundedGT_iff_monotone_chain_condition' [Preorder α] :
    WellFoundedGT α ↔ forall a : Nat ->o α, exists n, forall m, n <= m -> ¬a n < a m := by
  refine ⟨fun h a => ?_, fun h => ?_⟩
  · obtain ⟨x, ⟨n, rfl⟩, H⟩ := h.wf.has_min _ (Set.range_nonempty a)
    exact ⟨n, fun m _ => H _ (Set.mem_range_self _)⟩
  · rw [WellFoundedGT, isWellFounded_iff, RelEmbedding.wellFounded_iff_isEmpty]
    refine ⟨fun a => ?_⟩
    obtain ⟨n, hn⟩ := h (a.swap : _ ->r _).toOrderHom
    exact hn n.succ n.lt_succ_self.le ((RelEmbedding.map_rel_iff _).2 n.lt_succ_self)

/--
theorem `WellFoundedGT.monotone_chain_condition'` / 定理 `WellFoundedGT.monotone_chain_condition'`

English:
theorem WellFoundedGT.monotone_chain_condition'
  given: [Preorder α] [h : WellFoundedGT α] (a : Nat ->o α)
  proof: wellFoundedGT_iff_monotone_chain_condition'.1 h a

中文:
定理 WellFoundedGT.monotone_chain_condition'
  条件: [预序 α] [h : WellFoundedGT α] (a : 自然数 ->o α)
  证明: wellFoundedGT_iff_monotone_chain_condition'.1 h a

Depends on / 依赖: wellFoundedGT_iff_monotone_chain_condition
-/
theorem WellFoundedGT.monotone_chain_condition' [Preorder α] [h : WellFoundedGT α] (a : Nat ->o α) :
    exists n, forall m, n <= m -> ¬a n < a m :=
  wellFoundedGT_iff_monotone_chain_condition'.1 h a

/--
theorem `wellFoundedGT_iff_monotone_chain_condition` / 定理 `wellFoundedGT_iff_monotone_chain_condition`

English:
theorem wellFoundedGT_iff_monotone_chain_condition
  given: [PartialOrder α]
  proof: wellFoundedGT_iff_monotone_chain_condition'.trans by
  congrm forall a, exists n, forall m h, ?_
  rw [lt_iff_le_and_ne]
  simp [a.mono h]

中文:
定理 wellFoundedGT_iff_monotone_chain_condition
  条件: [偏序 α]
  证明: wellFoundedGT_iff_monotone_chain_condition'.trans by
  congrm forall a, exists n, forall m h, ?_
  rw [lt_iff_le_and_ne]
  simp [a.mono h]

Depends on / 依赖: a.mono, congrm, lt_iff_le_and_ne, wellFoundedGT_iff_monotone_chain_condition
-/
theorem wellFoundedGT_iff_monotone_chain_condition [PartialOrder α] :
    WellFoundedGT α ↔ forall a : Nat ->o α, exists n, forall m, n <= m -> a n = a m :=
wellFoundedGT_iff_monotone_chain_condition'.trans by
  congrm forall a, exists n, forall m h, ?_
  rw [lt_iff_le_and_ne]
  simp [a.mono h]

/--
theorem `WellFoundedGT.monotone_chain_condition` / 定理 `WellFoundedGT.monotone_chain_condition`

English:
theorem WellFoundedGT.monotone_chain_condition
  given: [PartialOrder α] [h : WellFoundedGT α] (a : Nat ->o α)
  proof: wellFoundedGT_iff_monotone_chain_condition.1 h a

中文:
定理 WellFoundedGT.monotone_chain_condition
  条件: [偏序 α] [h : WellFoundedGT α] (a : 自然数 ->o α)
  证明: wellFoundedGT_iff_monotone_chain_condition.1 h a

Depends on / 依赖: wellFoundedGT_iff_monotone_chain_condition
-/
theorem WellFoundedGT.monotone_chain_condition [PartialOrder α] [h : WellFoundedGT α] (a : Nat ->o α) :
    exists n, forall m, n <= m -> a n = a m :=
  wellFoundedGT_iff_monotone_chain_condition.1 h a

/--
theorem `WellFoundedLT.antitone_chain_condition` / 定理 `WellFoundedLT.antitone_chain_condition`

English:
theorem WellFoundedLT.antitone_chain_condition
  statement: [PartialOrder α] [WellFoundedLT α]
  proof: WellFoundedGT.monotone_chain_condition ⟨OrderDual.toDual ∘ f, hf⟩

中文:
定理 WellFoundedLT.antitone_chain_condition
  结论: [偏序 α] [WellFoundedLT α]
  证明: WellFoundedGT.monotone_chain_condition ⟨OrderDual.toDual ∘ f, hf⟩

Depends on / 依赖: OrderDual, OrderDual.toDual, WellFoundedGT, WellFoundedGT.monotone_chain_condition, monotone_chain_condition, toDual
-/
theorem WellFoundedLT.antitone_chain_condition [PartialOrder α] [WellFoundedLT α]
    {f : Nat -> α} (hf : Antitone f) : exists n, forall m, n <= m -> f n = f m :=
  WellFoundedGT.monotone_chain_condition ⟨OrderDual.toDual ∘ f, hf⟩

/--
Definition of `monotonicSequenceLimitIndex` / `monotonicSequenceLimitIndex` 的定义

English:
definition monotonicSequenceLimitIndex
  signature: [Preorder α] (a : Nat ->o α)
  body: sInf { n | forall m, n <= m -> a n = a m }

中文:
定义 monotonicSequenceLimitIndex
  签名: [预序 α] (a : 自然数 ->o α)
  定义体: sInf { n | forall m, n <= m -> a n = a m }
-/
noncomputable def monotonicSequenceLimitIndex [Preorder α] (a : Nat ->o α) : Nat :=
  sInf { n | forall m, n <= m -> a n = a m }

/--
Definition of `monotonicSequenceLimit` / `monotonicSequenceLimit` 的定义

English:
definition monotonicSequenceLimit
  signature: [Preorder α] (a : Nat ->o α)
  body: a (monotonicSequenceLimitIndex a)

中文:
定义 monotonicSequenceLimit
  签名: [预序 α] (a : 自然数 ->o α)
  定义体: a (monotonicSequenceLimitIndex a)

Depends on / 依赖: monotonicSequenceLimitIndex
-/
noncomputable def monotonicSequenceLimit [Preorder α] (a : Nat ->o α) :=
  a (monotonicSequenceLimitIndex a)

/--
theorem `le_monotonicSequenceLimit` / 定理 `le_monotonicSequenceLimit`

English:
theorem le_monotonicSequenceLimit
  given: [PartialOrder α] [WellFoundedGT α] (a : Nat ->o α) (m : Nat)
  proof: by
  rcases le_or_gt m (monotonicSequenceLimitIndex a) with hm | hm
  · exact a.monotone hm
  · obtain h := WellFoundedGT.monotone_chain_condition a
    exact (Nat.sInf_mem (s := {n | forall m, n <= m -> a n = a m}) h m hm.le).ge

中文:
定理 le_monotonicSequenceLimit
  条件: [偏序 α] [WellFoundedGT α] (a : 自然数 ->o α) (m : 自然数)
  证明: by
  rcases le_or_gt m (monotonicSequenceLimitIndex a) with hm | hm
  · exact a.monotone hm
  · obtain h := WellFoundedGT.monotone_chain_condition a
    exact (Nat.sInf_mem (s := {n | forall m, n <= m -> a n = a m}) h m hm.le).ge

Depends on / 依赖: Nat.sInf_mem, WellFoundedGT, WellFoundedGT.monotone_chain_condition, a.monotone, hm.le, le_or_gt, monotone, monotone_chain_condition, monotonicSequenceLimitIndex, sInf_mem
-/
theorem le_monotonicSequenceLimit [PartialOrder α] [WellFoundedGT α] (a : Nat ->o α) (m : Nat) :
    a m <= monotonicSequenceLimit a := by
  rcases le_or_gt m (monotonicSequenceLimitIndex a) with hm | hm
  · exact a.monotone hm
  · obtain h := WellFoundedGT.monotone_chain_condition a
    exact (Nat.sInf_mem (s := {n | forall m, n <= m -> a n = a m}) h m hm.le).ge

/--
theorem `WellFoundedGT.iSup_eq_monotonicSequenceLimit` / 定理 `WellFoundedGT.iSup_eq_monotonicSequenceLimit`

English:
theorem WellFoundedGT.iSup_eq_monotonicSequenceLimit
  statement: [CompleteLattice α]
  proof: (iSup_le (le_monotonicSequenceLimit a)).antisymm (le_iSup a _)

中文:
定理 WellFoundedGT.iSup_eq_monotonicSequenceLimit
  结论: [完备格 α]
  证明: (iSup_le (le_monotonicSequenceLimit a)).antisymm (le_iSup a _)

Depends on / 依赖: antisymm, iSup_le, le_iSup, le_monotonicSequenceLimit
-/
theorem WellFoundedGT.iSup_eq_monotonicSequenceLimit [CompleteLattice α]
    [WellFoundedGT α] (a : Nat ->o α) : iSup a = monotonicSequenceLimit a :=
  (iSup_le (le_monotonicSequenceLimit a)).antisymm (le_iSup a _)

/--
theorem `WellFoundedGT.ciSup_eq_monotonicSequenceLimit` / 定理 `WellFoundedGT.ciSup_eq_monotonicSequenceLimit`

English:
theorem WellFoundedGT.ciSup_eq_monotonicSequenceLimit
  statement: [ConditionallyCompleteLattice α]
  proof: (ciSup_le (le_monotonicSequenceLimit a)).antisymm (le_ciSup ha _)

中文:
定理 WellFoundedGT.ciSup_eq_monotonicSequenceLimit
  结论: [条件完备格 α]
  证明: (ciSup_le (le_monotonicSequenceLimit a)).antisymm (le_ciSup ha _)

Depends on / 依赖: antisymm, ciSup_le, le_ciSup, le_monotonicSequenceLimit
-/
theorem WellFoundedGT.ciSup_eq_monotonicSequenceLimit [ConditionallyCompleteLattice α]
    [WellFoundedGT α] (a : Nat ->o α) (ha : BddAbove (Set.range a)) :
    iSup a = monotonicSequenceLimit a :=
  (ciSup_le (le_monotonicSequenceLimit a)).antisymm (le_ciSup ha _)

/--
theorem `exists_covBy_seq_of_wellFoundedLT_wellFoundedGT` / 定理 `exists_covBy_seq_of_wellFoundedLT_wellFoundedGT`

English:
theorem exists_covBy_seq_of_wellFoundedLT_wellFoundedGT
  statement: (α) [Preorder α]
  proof: by
  choose next hnext using exists_covBy_of_wellFoundedLT (α := α)
  have hα := Set.nonempty_iff_univ_nonempty.mp ‹_›
  classical
  let a : Nat -> α := Nat.rec (wfl.wf.min _ hα) fun _n a => if ha : IsMax a then a else next ha
  refine ⟨a, isMin_iff_forall_not_lt.mpr fun _ => wfl.wf.not_lt_min _ (Set.mem_univ _), ?_⟩
  have cov n (hn : ¬ IsMax (a n)) : a n ⋖ a (n + 1) := by
    change a n ⋖ if ha : IsMax (a n) then a n else _
    rw [dif_neg hn]
    exact hnext hn
  have H : exists n, IsMax (a n) := by
    by_contra!
    exact (RelEmbedding.natGT a fun n => (cov n (this n)).1).not_wellFounded wfg.wf
  exact ⟨_, wellFounded_lt.min_mem _ H, fun i h => cov _ (wellFounded_lt.not_lt_min _ · h)⟩

中文:
定理 存在_covBy_seq_of_wellFoundedLT_wellFoundedGT
  结论: (α) [预序 α]
  证明: by
  choose next hnext using exists_covBy_of_wellFoundedLT (α := α)
  have hα := Set.nonempty_iff_univ_nonempty.mp ‹_›
  classical
  let a : Nat -> α := Nat.rec (wfl.wf.min _ hα) fun _n a => if ha : IsMax a then a else next ha
  refine ⟨a, isMin_iff_forall_not_lt.mpr fun _ => wfl.wf.not_lt_min _ (Set.mem_univ _), ?_⟩
  have cov n (hn : ¬ IsMax (a n)) : a n ⋖ a (n + 1) := by
    change a n ⋖ if ha : IsMax (a n) then a n else _
    rw [dif_neg hn]
    exact hnext hn
  have H : exists n, IsMax (a n) := by
    by_contra!
    exact (RelEmbedding.natGT a fun n => (cov n (this n)).1).not_wellFounded wfg.wf
  exact ⟨_, wellFounded_lt.min_mem _ H, fun i h => cov _ (wellFounded_lt.not_lt_min _ · h)⟩

Depends on / 依赖: Nat.rec, Set.mem_univ, Set.nonempty_iff_univ_nonempty.mp, classical, dif_neg, exists_covBy_of_wellFoundedLT, isMin_iff_forall_not_lt, isMin_iff_forall_not_lt.mpr, mem_univ, nonempty_iff_univ_nonempty, not_lt_min, wfl.wf.min, wfl.wf.not_lt_min
-/
theorem exists_covBy_seq_of_wellFoundedLT_wellFoundedGT (α) [Preorder α]
    [Nonempty α] [wfl : WellFoundedLT α] [wfg : WellFoundedGT α] :
    exists a : Nat -> α, IsMin (a 0) ∧ exists n, IsMax (a n) ∧ forall i < n, a i ⋖ a (i + 1) := by
  choose next hnext using exists_covBy_of_wellFoundedLT (α := α)
  have hα := Set.nonempty_iff_univ_nonempty.mp ‹_›
  classical
  let a : Nat -> α := Nat.rec (wfl.wf.min _ hα) fun _n a => if ha : IsMax a then a else next ha
  refine ⟨a, isMin_iff_forall_not_lt.mpr fun _ => wfl.wf.not_lt_min _ (Set.mem_univ _), ?_⟩
  have cov n (hn : ¬ IsMax (a n)) : a n ⋖ a (n + 1) := by
    change a n ⋖ if ha : IsMax (a n) then a n else _
    rw [dif_neg hn]
    exact hnext hn
  have H : exists n, IsMax (a n) := by
    by_contra!
    exact (RelEmbedding.natGT a fun n => (cov n (this n)).1).not_wellFounded wfg.wf
  exact ⟨_, wellFounded_lt.min_mem _ H, fun i h => cov _ (wellFounded_lt.not_lt_min _ · h)⟩

/--
theorem `exists_covBy_seq_of_wellFoundedLT_wellFoundedGT_of_le` / 定理 `exists_covBy_seq_of_wellFoundedLT_wellFoundedGT_of_le`

English:
theorem exists_covBy_seq_of_wellFoundedLT_wellFoundedGT_of_le
  statement: {α : Type*} [PartialOrder α]
  proof: by
  let S := Set.Icc x y
  let hS : BoundedOrder S :=
    { top := ⟨y, h, le_rfl⟩, le_top x := x.2.2, bot := ⟨x, le_rfl, h⟩, bot_le x := x.2.1 }
  obtain ⟨a, h₁, n, h₂, e⟩ := exists_covBy_seq_of_wellFoundedLT_wellFoundedGT S
  simp only [isMin_iff_eq_bot, Subtype.ext_iff, isMax_iff_eq_top] at h₁ h₂
  exact ⟨Subtype.val ∘ a, h₁, n, h₂, fun i hi => ⟨(e i hi).1, fun c hc h => (e i hi).2
    (c := ⟨c, (a i).2.1.trans hc.le, h.le.trans (a _).2.2⟩) hc h⟩⟩

中文:
定理 存在_covBy_seq_of_wellFoundedLT_wellFoundedGT_of_le
  结论: {α : 类型} [偏序 α]
  证明: by
  let S := Set.Icc x y
  let hS : BoundedOrder S :=
    { top := ⟨y, h, le_rfl⟩, le_top x := x.2.2, bot := ⟨x, le_rfl, h⟩, bot_le x := x.2.1 }
  obtain ⟨a, h₁, n, h₂, e⟩ := exists_covBy_seq_of_wellFoundedLT_wellFoundedGT S
  simp only [isMin_iff_eq_bot, Subtype.ext_iff, isMax_iff_eq_top] at h₁ h₂
  exact ⟨Subtype.val ∘ a, h₁, n, h₂, fun i hi => ⟨(e i hi).1, fun c hc h => (e i hi).2
    (c := ⟨c, (a i).2.1.trans hc.le, h.le.trans (a _).2.2⟩) hc h⟩⟩

Depends on / 依赖: BoundedOrder, Set.Icc, Subtype, Subtype.ext_iff, Subtype.val, bot_le, exists_covBy_seq_of_wellFoundedLT_wellFoundedGT, ext_iff, h.le.trans, hc.le, isMax_iff_eq_top, isMin_iff_eq_bot, le_rfl, le_top
-/
theorem exists_covBy_seq_of_wellFoundedLT_wellFoundedGT_of_le {α : Type*} [PartialOrder α]
    [wfl : WellFoundedLT α] [wfg : WellFoundedGT α] {x y : α} (h : x <= y) :
    exists a : Nat -> α, a 0 = x ∧ exists n, a n = y ∧ forall i < n, a i ⋖ a (i + 1) := by
  let S := Set.Icc x y
  let hS : BoundedOrder S :=
    { top := ⟨y, h, le_rfl⟩, le_top x := x.2.2, bot := ⟨x, le_rfl, h⟩, bot_le x := x.2.1 }
  obtain ⟨a, h₁, n, h₂, e⟩ := exists_covBy_seq_of_wellFoundedLT_wellFoundedGT S
  simp only [isMin_iff_eq_bot, Subtype.ext_iff, isMax_iff_eq_top] at h₁ h₂
  exact ⟨Subtype.val ∘ a, h₁, n, h₂, fun i hi => ⟨(e i hi).1, fun c hc h => (e i hi).2
    (c := ⟨c, (a i).2.1.trans hc.le, h.le.trans (a _).2.2⟩) hc h⟩⟩
