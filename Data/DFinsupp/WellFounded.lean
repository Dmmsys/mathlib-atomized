/-
Copyright (c) 2022 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.Data.DFinsupp.Lex
public import Mathlib.Order.Antisymmetrization
public import Mathlib.Order.GameAdd
public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.Tactic.AdaptationNote

/-!
# Well-foundedness of the lexicographic and product orders on `DFinsupp` and `Pi`

The primary results are `DFinsupp.Lex.wellFounded` and the two variants that follow it,
which essentially say that if `(· > ·)` is a well order on `ι`, `(· < ·)` is well-founded on each
`α i`, and `0` is a bottom element in `α i`, then the lexicographic `(· < ·)` is well-founded
on `Π₀ i, α i`. The proof is modelled on the proof of `WellFounded.cutExpand`.

The results are used to prove `Pi.Lex.wellFounded` and two variants, which say that if
`ι` is finite and equipped with a linear order and `(· < ·)` is well-founded on each `α i`,
then the lexicographic `(· < ·)` is well-founded on `Π i, α i`, and the same is true for
`Π₀ i, α i` (`DFinsupp.Lex.wellFounded_of_finite`), because `DFinsupp` is order-isomorphic
to `pi` when `ι` is finite.

Finally, we deduce `DFinsupp.wellFoundedLT`, `Pi.wellFoundedLT`,
`DFinsupp.wellFoundedLT_of_finite` and variants, which concern the product order
rather than the lexicographic one. An order on `ι` is not required in these results,
but we deduce them from the well-foundedness of the lexicographic order by choosing
a well order on `ι` so that the product order `(· < ·)` becomes a subrelation
of the lexicographic `(· < ·)`.

All results are provided in two forms whenever possible: a general form where the relations
can be arbitrary (not the `(· < ·)` of a preorder, or not even transitive, etc.) and a specialized
form provided as `WellFoundedLT` instances where the `(d)Finsupp/pi` type (or their `Lex`
type synonyms) carries a natural `(· < ·)`.

Notice that the definition of `DFinsupp.Lex` says that `x < y` according to `DFinsupp.Lex r s`
iff there exists a coordinate `i : ι` such that `x i < y i` according to `s i`, and at all
`r`-smaller coordinates `j` (i.e. satisfying `r j i`), `x` remains unchanged relative to `y`;
in other words, coordinates `j` such that `¬ r j i` and `j ≠ i` are exactly where changes
can happen arbitrarily. This explains the appearance of `rᶜ ⊓ (≠)` in
`dfinsupp.acc_single` and `dfinsupp.well_founded`. When `r` is trichotomous (e.g. the `(· < ·)`
of a linear order), `¬ r j i ∧ j ≠ i` implies `r i j`, so it suffices to require `r.swap`
to be well-founded.
-/

public section


variable {ι : Type*} {α : ι -> Type*}

namespace DFinsupp

open Relation Prod

section Zero

variable [forall i, Zero (α i)] (r : ι -> ι -> Prop) (s : forall i, α i -> α i -> Prop)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `lex_fibration` / 定理 `lex_fibration`

English:
theorem lex_fibration
  given: [forall (i) (s : Set ι), Decidable (i in s)]
  proof: by
  rintro ⟨p, x₁, x₂⟩ x ⟨i, hr, hs⟩
  simp_rw [piecewise_apply] at hs hr
  split_ifs at hs with hp
  · refine ⟨⟨{ j | r j i -> j in p }, piecewise x₁ x { j | r j i }, x₂⟩,
      .fst ⟨i, fun j hj => ?_, ?_⟩, ?_⟩ <;> simp only [piecewise_apply, Set.mem_ofPred_eq]
    · simp only [if_pos hj]
    · split_ifs with hi
      · rwa [hr i hi, if_pos hp] at hs
      · assumption
    · ext1 j
      simp only [piecewise_apply, Set.mem_ofPred_eq]
      split_ifs with h₁ h₂ <;> try rfl
      · rw [hr j h₂, if_pos (h₁ h₂)]
      · rw [Classical.not_imp] at h₁
        rw [hr j h₁.1]; rw [if_neg h₁.2]
  · refine ⟨⟨{ j | r j i ∧ j in p }, x₁, piecewise x₂ x { j | r j i }⟩,
      .snd ⟨i, fun j hj => ?_, ?_⟩, ?_⟩ <;> simp only [piecewise_apply, Set.mem_ofPred_eq]
    · exact if_pos hj
    · split_ifs with hi
      · rwa [hr i hi, if_neg hp] at hs
      · assumption
    · ext1 j
      simp only [piecewise_apply, Set.mem_ofPred_eq]
      split_ifs with h₁ h₂ <;> try rfl
      · rw [hr j h₁.1, if_pos h₁.2]
      · rw [hr j h₂, if_neg]
        simpa [h₂] using h₁

中文:
定理 lex_fibration
  条件: [对任意 (i) (s : 集合 ι), 可判定 (i in s)]
  证明: by
  rintro ⟨p, x₁, x₂⟩ x ⟨i, hr, hs⟩
  simp_rw [piecewise_apply] at hs hr
  split_ifs at hs with hp
  · refine ⟨⟨{ j | r j i -> j in p }, piecewise x₁ x { j | r j i }, x₂⟩,
      .fst ⟨i, fun j hj => ?_, ?_⟩, ?_⟩ <;> simp only [piecewise_apply, Set.mem_ofPred_eq]
    · simp only [if_pos hj]
    · split_ifs with hi
      · rwa [hr i hi, if_pos hp] at hs
      · assumption
    · ext1 j
      simp only [piecewise_apply, Set.mem_ofPred_eq]
      split_ifs with h₁ h₂ <;> try rfl
      · rw [hr j h₂, if_pos (h₁ h₂)]
      · rw [Classical.not_imp] at h₁
        rw [hr j h₁.1]; rw [if_neg h₁.2]
  · refine ⟨⟨{ j | r j i ∧ j in p }, x₁, piecewise x₂ x { j | r j i }⟩,
      .snd ⟨i, fun j hj => ?_, ?_⟩, ?_⟩ <;> simp only [piecewise_apply, Set.mem_ofPred_eq]
    · exact if_pos hj
    · split_ifs with hi
      · rwa [hr i hi, if_neg hp] at hs
      · assumption
    · ext1 j
      simp only [piecewise_apply, Set.mem_ofPred_eq]
      split_ifs with h₁ h₂ <;> try rfl
      · rw [hr j h₁.1, if_pos h₁.2]
      · rw [hr j h₂, if_neg]
        simpa [h₂] using h₁

Depends on / 依赖: Classical, Classical.not_imp, Set.mem_ofPred_eq, if_pos, mem_ofPred_eq, not_imp, piecewise, piecewise_apply, simp_rw, split_ifs
-/
theorem lex_fibration [forall (i) (s : Set ι), Decidable (i in s)] :
    Fibration (InvImage (GameAdd (DFinsupp.Lex r s) (DFinsupp.Lex r s)) snd) (DFinsupp.Lex r s)
      fun x => piecewise x.2.1 x.2.2 x.1 := by
  rintro ⟨p, x₁, x₂⟩ x ⟨i, hr, hs⟩
  simp_rw [piecewise_apply] at hs hr
  split_ifs at hs with hp
  · refine ⟨⟨{ j | r j i -> j in p }, piecewise x₁ x { j | r j i }, x₂⟩,
      .fst ⟨i, fun j hj => ?_, ?_⟩, ?_⟩ <;> simp only [piecewise_apply, Set.mem_ofPred_eq]
    · simp only [if_pos hj]
    · split_ifs with hi
      · rwa [hr i hi, if_pos hp] at hs
      · assumption
    · ext1 j
      simp only [piecewise_apply, Set.mem_ofPred_eq]
      split_ifs with h₁ h₂ <;> try rfl
      · rw [hr j h₂, if_pos (h₁ h₂)]
      · rw [Classical.not_imp] at h₁
        rw [hr j h₁.1]; rw [if_neg h₁.2]
  · refine ⟨⟨{ j | r j i ∧ j in p }, x₁, piecewise x₂ x { j | r j i }⟩,
      .snd ⟨i, fun j hj => ?_, ?_⟩, ?_⟩ <;> simp only [piecewise_apply, Set.mem_ofPred_eq]
    · exact if_pos hj
    · split_ifs with hi
      · rwa [hr i hi, if_neg hp] at hs
      · assumption
    · ext1 j
      simp only [piecewise_apply, Set.mem_ofPred_eq]
      split_ifs with h₁ h₂ <;> try rfl
      · rw [hr j h₁.1, if_pos h₁.2]
      · rw [hr j h₂, if_neg]
        simpa [h₂] using h₁

variable {r s}

/--
theorem `Lex.acc_of_single_erase` / 定理 `Lex.acc_of_single_erase`

English:
theorem Lex.acc_of_single_erase
  statement: [DecidableEq ι] {x : Π₀ i, α i} (i : ι)
  proof: by
  classical
    convert! ←
      @Acc.of_fibration _ _ _ _ _ (lex_fibration r s) ⟨{ i }, _⟩
        (InvImage.accessible snd <| hs.prod_gameAdd hu)
    convert! piecewise_single_erase x i

中文:
定理 Lex.acc_of_single_erase
  结论: [DecidableEq ι] {x : Π₀ i, α i} (i : ι)
  证明: by
  classical
    convert! ←
      @Acc.of_fibration _ _ _ _ _ (lex_fibration r s) ⟨{ i }, _⟩
        (InvImage.accessible snd <| hs.prod_gameAdd hu)
    convert! piecewise_single_erase x i

Depends on / 依赖: Acc.of_fibration, InvImage, InvImage.accessible, accessible, classical, convert, hs.prod_gameAdd, lex_fibration, of_fibration, piecewise_single_erase, prod_gameAdd
-/
theorem Lex.acc_of_single_erase [DecidableEq ι] {x : Π₀ i, α i} (i : ι)
    (hs : Acc (DFinsupp.Lex r s) <| single i (x i)) (hu : Acc (DFinsupp.Lex r s) <| x.erase i) :
    Acc (DFinsupp.Lex r s) x := by
  classical
    convert! ←
      @Acc.of_fibration _ _ _ _ _ (lex_fibration r s) ⟨{ i }, _⟩
        (InvImage.accessible snd <| hs.prod_gameAdd hu)
    convert! piecewise_single_erase x i

/--
theorem `Lex.acc_zero` / 定理 `Lex.acc_zero`

English:
theorem Lex.acc_zero
  given: (hbot : forall ⦃i a⦄, ¬s i a 0)
  statement: Acc (DFinsupp.Lex r s) 0
  proof: Acc.intro 0 fun _ ⟨_, _, h⟩ => (hbot h).elim

中文:
定理 Lex.acc_zero
  条件: (hbot : 对任意 ⦃i a⦄, ¬s i a 0)
  结论: Acc (直和有限支撑.Lex r s) 0
  证明: Acc.intro 0 fun _ ⟨_, _, h⟩ => (hbot h).elim

Depends on / 依赖: Acc.intro
-/
theorem Lex.acc_zero (hbot : forall ⦃i a⦄, ¬s i a 0) : Acc (DFinsupp.Lex r s) 0 :=
  Acc.intro 0 fun _ ⟨_, _, h⟩ => (hbot h).elim

/--
theorem `Lex.acc_of_single` / 定理 `Lex.acc_of_single`

English:
theorem Lex.acc_of_single
  statement: (hbot : forall ⦃i a⦄, ¬s i a 0) [DecidableEq ι]
  proof: by
  generalize ht : x.support = t; revert x
  classical
    induction t using Finset.induction with
    | empty =>
      intro x ht
      rw [support_eq_empty.1 ht]
      exact fun _ => Lex.acc_zero hbot
    | insert b t hb ih =>
      refine fun x ht h => Lex.acc_of_single_erase b (h b <| t.mem_insert_self b) ?_
      refine ih _ (by rw [support_erase, ht, Finset.erase_insert hb]) fun a ha => ?_
      rw [erase_ne (ha.ne_of_notMem hb)]
      exact h a (Finset.mem_insert_of_mem ha)

中文:
定理 Lex.acc_of_single
  结论: (hbot : 对任意 ⦃i a⦄, ¬s i a 0) [DecidableEq ι]
  证明: by
  generalize ht : x.support = t; revert x
  classical
    induction t using Finset.induction with
    | empty =>
      intro x ht
      rw [support_eq_empty.1 ht]
      exact fun _ => Lex.acc_zero hbot
    | insert b t hb ih =>
      refine fun x ht h => Lex.acc_of_single_erase b (h b <| t.mem_insert_self b) ?_
      refine ih _ (by rw [support_erase, ht, Finset.erase_insert hb]) fun a ha => ?_
      rw [erase_ne (ha.ne_of_notMem hb)]
      exact h a (Finset.mem_insert_of_mem ha)

Depends on / 依赖: Finset, Finset.erase_insert, Finset.induction, Finset.mem_insert_of_mem, Lex.acc_of_single_erase, Lex.acc_zero, acc_of_single_erase, acc_zero, classical, erase_insert, erase_ne, generalize, ha.ne_of_notMem, insert, mem_insert_of_mem, mem_insert_self, ne_of_notMem, revert, support, support_eq_empty
-/
theorem Lex.acc_of_single (hbot : forall ⦃i a⦄, ¬s i a 0) [DecidableEq ι]
    [forall (i) (x : α i), Decidable (x != 0)] (x : Π₀ i, α i) :
    (forall i in x.support, Acc (DFinsupp.Lex r s) <| single i (x i)) -> Acc (DFinsupp.Lex r s) x := by
  generalize ht : x.support = t; revert x
  classical
    induction t using Finset.induction with
    | empty =>
      intro x ht
      rw [support_eq_empty.1 ht]
      exact fun _ => Lex.acc_zero hbot
    | insert b t hb ih =>
      refine fun x ht h => Lex.acc_of_single_erase b (h b <| t.mem_insert_self b) ?_
      refine ih _ (by rw [support_erase, ht, Finset.erase_insert hb]) fun a ha => ?_
      rw [erase_ne (ha.ne_of_notMem hb)]
      exact h a (Finset.mem_insert_of_mem ha)

/--
theorem `Lex.acc_single` / 定理 `Lex.acc_single`

English:
theorem Lex.acc_single
  statement: (hbot : forall ⦃i a⦄, ¬s i a 0) (hs : forall i, WellFounded (s i))
  proof: by
  induction hi with | _ i _ ih
  refine fun a => WellFounded.induction (hs i)
    (C := fun x => Acc (DFinsupp.Lex r s) (single i x)) a fun a ha => ?_
  refine Acc.intro _ fun x => ?_
  rintro ⟨k, hr, hs⟩
  rw [single_apply] at hs
  split_ifs at hs with hik
  swap
  · exact (hbot hs).elim
  subst hik
  classical
    refine Lex.acc_of_single hbot x fun j hj => ?_
    obtain rfl | hij := eq_or_ne j i
    · exact ha _ hs
    by_cases h : r j i
    · rw [hr j h, single_eq_of_ne hij, single_zero]
      exact Lex.acc_zero hbot
    · exact ih _ ⟨h, hij⟩ _

中文:
定理 Lex.acc_single
  结论: (hbot : 对任意 ⦃i a⦄, ¬s i a 0) (hs : 对任意 i, 良基 (s i))
  证明: by
  induction hi with | _ i _ ih
  refine fun a => WellFounded.induction (hs i)
    (C := fun x => Acc (DFinsupp.Lex r s) (single i x)) a fun a ha => ?_
  refine Acc.intro _ fun x => ?_
  rintro ⟨k, hr, hs⟩
  rw [single_apply] at hs
  split_ifs at hs with hik
  swap
  · exact (hbot hs).elim
  subst hik
  classical
    refine Lex.acc_of_single hbot x fun j hj => ?_
    obtain rfl | hij := eq_or_ne j i
    · exact ha _ hs
    by_cases h : r j i
    · rw [hr j h, single_eq_of_ne hij, single_zero]
      exact Lex.acc_zero hbot
    · exact ih _ ⟨h, hij⟩ _

Depends on / 依赖: Acc.intro, DFinsupp, DFinsupp.Lex, Lex.acc_of_single, Lex.acc_zero, WellFounded, WellFounded.induction, acc_of_single, acc_zero, classical, eq_or_ne, single, single_apply, single_eq_of_ne, single_zero, split_ifs
-/
theorem Lex.acc_single (hbot : forall ⦃i a⦄, ¬s i a 0) (hs : forall i, WellFounded (s i))
    [DecidableEq ι] {i : ι} (hi : Acc (rᶜ ⊓ (· != ·)) i) :
    forall a, Acc (DFinsupp.Lex r s) (single i a) := by
  induction hi with | _ i _ ih
  refine fun a => WellFounded.induction (hs i)
    (C := fun x => Acc (DFinsupp.Lex r s) (single i x)) a fun a ha => ?_
  refine Acc.intro _ fun x => ?_
  rintro ⟨k, hr, hs⟩
  rw [single_apply] at hs
  split_ifs at hs with hik
  swap
  · exact (hbot hs).elim
  subst hik
  classical
    refine Lex.acc_of_single hbot x fun j hj => ?_
    obtain rfl | hij := eq_or_ne j i
    · exact ha _ hs
    by_cases h : r j i
    · rw [hr j h, single_eq_of_ne hij, single_zero]
      exact Lex.acc_zero hbot
    · exact ih _ ⟨h, hij⟩ _

/--
theorem `Lex.acc` / 定理 `Lex.acc`

English:
theorem Lex.acc
  statement: (hbot : forall ⦃i a⦄, ¬s i a 0) (hs : forall i, WellFounded (s i))
  proof: Lex.acc_of_single hbot x fun i hi => Lex.acc_single hbot hs (h i hi) _

中文:
定理 Lex.acc
  结论: (hbot : 对任意 ⦃i a⦄, ¬s i a 0) (hs : 对任意 i, 良基 (s i))
  证明: Lex.acc_of_single hbot x fun i hi => Lex.acc_single hbot hs (h i hi) _

Depends on / 依赖: Lex.acc_of_single, Lex.acc_single, acc_of_single, acc_single
-/
theorem Lex.acc (hbot : forall ⦃i a⦄, ¬s i a 0) (hs : forall i, WellFounded (s i))
    [DecidableEq ι] [forall (i) (x : α i), Decidable (x != 0)] (x : Π₀ i, α i)
    (h : forall i in x.support, Acc (rᶜ ⊓ (· != ·)) i) : Acc (DFinsupp.Lex r s) x :=
  Lex.acc_of_single hbot x fun i hi => Lex.acc_single hbot hs (h i hi) _

/--
theorem `Lex.wellFounded` / 定理 `Lex.wellFounded`

English:
theorem Lex.wellFounded
  statement: (hbot : forall ⦃i a⦄, ¬s i a 0) (hs : forall i, WellFounded (s i))
  proof: ⟨fun x => by classical exact Lex.acc hbot hs x fun i _ => hr.apply i⟩

中文:
定理 Lex.wellFounded
  结论: (hbot : 对任意 ⦃i a⦄, ¬s i a 0) (hs : 对任意 i, 良基 (s i))
  证明: ⟨fun x => by classical exact Lex.acc hbot hs x fun i _ => hr.apply i⟩

Depends on / 依赖: Lex.acc, classical, hr.apply
-/
theorem Lex.wellFounded (hbot : forall ⦃i a⦄, ¬s i a 0) (hs : forall i, WellFounded (s i))
    (hr : WellFounded <| rᶜ ⊓ (· != ·)) : WellFounded (DFinsupp.Lex r s) :=
  ⟨fun x => by classical exact Lex.acc hbot hs x fun i _ => hr.apply i⟩

/--
theorem `Lex.wellFounded'` / 定理 `Lex.wellFounded'`

English:
theorem Lex.wellFounded'
  statement: (hbot : forall ⦃i a⦄, ¬s i a 0) (hs : forall i, WellFounded (s i))
  proof: Lex.wellFounded hbot hs Subrelation.wf
    (fun {i j} h => Not.imp_symm (@Std.Trichotomous.trichotomous ι r _ i j h.left) h.right) hr

中文:
定理 Lex.wellFounded'
  结论: (hbot : 对任意 ⦃i a⦄, ¬s i a 0) (hs : 对任意 i, 良基 (s i))
  证明: Lex.wellFounded hbot hs Subrelation.wf
    (fun {i j} h => Not.imp_symm (@Std.Trichotomous.trichotomous ι r _ i j h.left) h.right) hr

Depends on / 依赖: Lex.wellFounded, Not.imp_symm, Std.Trichotomous.trichotomous, Subrelation, Subrelation.wf, Trichotomous, h.left, h.right, imp_symm, trichotomous, wellFounded
-/
theorem Lex.wellFounded' (hbot : forall ⦃i a⦄, ¬s i a 0) (hs : forall i, WellFounded (s i))
    [Std.Trichotomous r] (hr : WellFounded (Function.swap r)) : WellFounded (DFinsupp.Lex r s) :=
Lex.wellFounded hbot hs Subrelation.wf
    (fun {i j} h => Not.imp_symm (@Std.Trichotomous.trichotomous ι r _ i j h.left) h.right) hr

end Zero

/--
Instance `Lex.wellFoundedLT` / 实例 `Lex.wellFoundedLT`

English:
instance Lex.wellFoundedLT
  signature: [LT ι] [@Std.Trichotomous ι (· < ·)] [hι : WellFoundedGT ι]
  body: ⟨Lex.wellFounded' (fun _ _ => not_lt_zero) (fun i => (hα i).wf) hι.wf⟩

中文:
实例 Lex.wellFoundedLT
  签名: [LT ι] [@Std.三歧 ι (· < ·)] [hι : WellFoundedGT ι]
  定义体: ⟨Lex.wellFounded' (fun _ _ => not_lt_zero) (fun i => (hα i).wf) hι.wf⟩

Depends on / 依赖: Lex.wellFounded, not_lt_zero, wellFounded
-/
instance Lex.wellFoundedLT [LT ι] [@Std.Trichotomous ι (· < ·)] [hι : WellFoundedGT ι]
    [forall i, AddMonoid (α i)] [forall i, PartialOrder (α i)] [forall i, IsBotZeroClass (α i)]
    [hα : forall i, WellFoundedLT (α i)] :
    WellFoundedLT (Lex (Π₀ i, α i)) :=
  ⟨Lex.wellFounded' (fun _ _ => not_lt_zero) (fun i => (hα i).wf) hι.wf⟩

set_option backward.isDefEq.respectTransparency false in
/--
Instance `Colex.wellFoundedLT` / 实例 `Colex.wellFoundedLT`

English:
instance Colex.wellFoundedLT
  signature: [LT ι] [@Std.Trichotomous ι (· < ·)] [WellFoundedLT ι]
  body: Lex.wellFoundedLT (ι := ιᵒᵈ)

中文:
实例 Colex.wellFoundedLT
  签名: [LT ι] [@Std.三歧 ι (· < ·)] [WellFoundedLT ι]
  定义体: Lex.wellFoundedLT (ι := ιᵒᵈ)

Depends on / 依赖: Lex.wellFoundedLT, wellFoundedLT
-/
instance Colex.wellFoundedLT [LT ι] [@Std.Trichotomous ι (· < ·)] [WellFoundedLT ι]
    [forall i, AddMonoid (α i)] [forall i, PartialOrder (α i)] [forall i, IsBotZeroClass (α i)]
    [forall i, WellFoundedLT (α i)] :
    WellFoundedLT (Colex (Π₀ i, α i)) :=
  Lex.wellFoundedLT (ι := ιᵒᵈ)

end DFinsupp

open DFinsupp

variable (r : ι -> ι -> Prop) {s : forall i, α i -> α i -> Prop}

/--
theorem `Pi.Lex.wellFounded` / 定理 `Pi.Lex.wellFounded`

English:
theorem Pi.Lex.wellFounded
  given: [IsStrictTotalOrder ι r] [Finite ι] (hs : forall i, WellFounded (s i))
  proof: by
  obtain h | ⟨⟨x⟩⟩ := isEmpty_or_nonempty (forall i, α i)
  · convert! emptyWf.wf
  let : forall i, Zero (α i) := fun i => ⟨(hs i).min ⊤ ⟨x i, trivial⟩⟩
  have := Fintype.ofFinite ι
  refine InvImage.wf equivFunOnFintype.symm (Lex.wellFounded' (fun i a => ?_) hs ?_)
  exacts [(hs i).not_lt_min ⊤ trivial, Finite.wellFounded_of_trans_of_irrefl (Function.swap r)]

中文:
定理 依赖函数类型.Lex.wellFounded
  条件: [是StrictTotal序 ι r] [有限 ι] (hs : 对任意 i, 良基 (s i))
  证明: by
  obtain h | ⟨⟨x⟩⟩ := isEmpty_or_nonempty (forall i, α i)
  · convert! emptyWf.wf
  let : forall i, Zero (α i) := fun i => ⟨(hs i).min ⊤ ⟨x i, trivial⟩⟩
  have := Fintype.ofFinite ι
  refine InvImage.wf equivFunOnFintype.symm (Lex.wellFounded' (fun i a => ?_) hs ?_)
  exacts [(hs i).not_lt_min ⊤ trivial, Finite.wellFounded_of_trans_of_irrefl (Function.swap r)]

Depends on / 依赖: Finite, Finite.wellFounded_of_trans_of_irrefl, Fintype, Fintype.ofFinite, Function, Function.swap, InvImage, InvImage.wf, Lex.wellFounded, convert, emptyWf, emptyWf.wf, equivFunOnFintype, equivFunOnFintype.symm, exacts, isEmpty_or_nonempty, not_lt_min, ofFinite, wellFounded, wellFounded_of_trans_of_irrefl
-/
theorem Pi.Lex.wellFounded [IsStrictTotalOrder ι r] [Finite ι] (hs : forall i, WellFounded (s i)) :
    WellFounded (Pi.Lex r (fun {i} => s i)) := by
  obtain h | ⟨⟨x⟩⟩ := isEmpty_or_nonempty (forall i, α i)
  · convert! emptyWf.wf
  let : forall i, Zero (α i) := fun i => ⟨(hs i).min ⊤ ⟨x i, trivial⟩⟩
  have := Fintype.ofFinite ι
  refine InvImage.wf equivFunOnFintype.symm (Lex.wellFounded' (fun i a => ?_) hs ?_)
  exacts [(hs i).not_lt_min ⊤ trivial, Finite.wellFounded_of_trans_of_irrefl (Function.swap r)]

/--
Instance `Pi.Lex.wellFoundedLT` / 实例 `Pi.Lex.wellFoundedLT`

English:
instance Pi.Lex.wellFoundedLT
  signature: [LinearOrder ι] [Finite ι] [forall i, LT (α i)]
  body: ⟨Pi.Lex.wellFounded (· < ·) fun i => (hwf i).1⟩

中文:
实例 依赖函数类型.Lex.wellFoundedLT
  签名: [线性序 ι] [有限 ι] [对任意 i, LT (α i)]
  定义体: ⟨Pi.Lex.wellFounded (· < ·) fun i => (hwf i).1⟩

Depends on / 依赖: Pi.Lex.wellFounded, wellFounded
-/
instance Pi.Lex.wellFoundedLT [LinearOrder ι] [Finite ι] [forall i, LT (α i)]
    [hwf : forall i, WellFoundedLT (α i)] : WellFoundedLT (Lex (forall i, α i)) :=
  ⟨Pi.Lex.wellFounded (· < ·) fun i => (hwf i).1⟩

set_option backward.isDefEq.respectTransparency false in
/--
Instance `Pi.Colex.wellFoundedLT` / 实例 `Pi.Colex.wellFoundedLT`

English:
instance Pi.Colex.wellFoundedLT
  signature: [LinearOrder ι] [Finite ι] [forall i, LT (α i)]
  body: Pi.Lex.wellFoundedLT (ι := ιᵒᵈ)

中文:
实例 依赖函数类型.Colex.wellFoundedLT
  签名: [线性序 ι] [有限 ι] [对任意 i, LT (α i)]
  定义体: Pi.Lex.wellFoundedLT (ι := ιᵒᵈ)

Depends on / 依赖: Pi.Lex.wellFoundedLT, wellFoundedLT
-/
instance Pi.Colex.wellFoundedLT [LinearOrder ι] [Finite ι] [forall i, LT (α i)]
    [forall i, WellFoundedLT (α i)] : WellFoundedLT (Colex (forall i, α i)) :=
  Pi.Lex.wellFoundedLT (ι := ιᵒᵈ)

/--
Instance `Function.Lex.wellFoundedLT` / 实例 `Function.Lex.wellFoundedLT`

English:
instance Function.Lex.wellFoundedLT
  signature: {α} [LinearOrder ι] [Finite ι] [LT α] [WellFoundedLT α]
  body: Pi.Lex.wellFoundedLT

中文:
实例 函数.Lex.wellFoundedLT
  签名: {α} [线性序 ι] [有限 ι] [LT α] [WellFoundedLT α]
  定义体: Pi.Lex.wellFoundedLT

Depends on / 依赖: Pi.Lex.wellFoundedLT, wellFoundedLT
-/
instance Function.Lex.wellFoundedLT {α} [LinearOrder ι] [Finite ι] [LT α] [WellFoundedLT α] :
    WellFoundedLT (Lex (ι -> α)) :=
  Pi.Lex.wellFoundedLT

/--
theorem `DFinsupp.Lex.wellFounded_of_finite` / 定理 `DFinsupp.Lex.wellFounded_of_finite`

English:
theorem DFinsupp.Lex.wellFounded_of_finite
  statement: [IsStrictTotalOrder ι r] [Finite ι] [forall i, Zero (α i)]
  proof: have := Fintype.ofFinite ι
  InvImage.wf equivFunOnFintype (Pi.Lex.wellFounded r hs)

中文:
定理 直和有限支撑.Lex.wellFounded_of_finite
  结论: [是StrictTotal序 ι r] [有限 ι] [对任意 i, 零 (α i)]
  证明: have := Fintype.ofFinite ι
  InvImage.wf equivFunOnFintype (Pi.Lex.wellFounded r hs)

Depends on / 依赖: Fintype, Fintype.ofFinite, InvImage, InvImage.wf, Pi.Lex.wellFounded, equivFunOnFintype, ofFinite, wellFounded
-/
theorem DFinsupp.Lex.wellFounded_of_finite [IsStrictTotalOrder ι r] [Finite ι] [forall i, Zero (α i)]
    (hs : forall i, WellFounded (s i)) : WellFounded (DFinsupp.Lex r s) :=
  have := Fintype.ofFinite ι
  InvImage.wf equivFunOnFintype (Pi.Lex.wellFounded r hs)

/--
Instance `DFinsupp.Lex.wellFoundedLT_of_finite` / 实例 `DFinsupp.Lex.wellFoundedLT_of_finite`

English:
instance DFinsupp.Lex.wellFoundedLT_of_finite
  signature: [LinearOrder ι] [Finite ι] [forall i, Zero (α i)]
  body: ⟨DFinsupp.Lex.wellFounded_of_finite (· < ·) fun i => (hwf i).1⟩

中文:
实例 直和有限支撑.Lex.wellFoundedLT_of_finite
  签名: [线性序 ι] [有限 ι] [对任意 i, 零 (α i)]
  定义体: ⟨DFinsupp.Lex.wellFounded_of_finite (· < ·) fun i => (hwf i).1⟩

Depends on / 依赖: DFinsupp, DFinsupp.Lex.wellFounded_of_finite, wellFounded_of_finite
-/
instance DFinsupp.Lex.wellFoundedLT_of_finite [LinearOrder ι] [Finite ι] [forall i, Zero (α i)]
    [forall i, LT (α i)] [hwf : forall i, WellFoundedLT (α i)] : WellFoundedLT (Lex (Π₀ i, α i)) :=
  ⟨DFinsupp.Lex.wellFounded_of_finite (· < ·) fun i => (hwf i).1⟩

set_option backward.isDefEq.respectTransparency false in
/--
Instance `DFinsupp.Colex.wellFoundedLT_of_finite` / 实例 `DFinsupp.Colex.wellFoundedLT_of_finite`

English:
instance DFinsupp.Colex.wellFoundedLT_of_finite
  signature: [LinearOrder ι] [Finite ι] [forall i, Zero (α i)]
  body: DFinsupp.Lex.wellFoundedLT_of_finite (ι := ιᵒᵈ)

中文:
实例 直和有限支撑.Colex.wellFoundedLT_of_finite
  签名: [线性序 ι] [有限 ι] [对任意 i, 零 (α i)]
  定义体: DFinsupp.Lex.wellFoundedLT_of_finite (ι := ιᵒᵈ)

Depends on / 依赖: DFinsupp, DFinsupp.Lex.wellFoundedLT_of_finite, wellFoundedLT_of_finite
-/
instance DFinsupp.Colex.wellFoundedLT_of_finite [LinearOrder ι] [Finite ι] [forall i, Zero (α i)]
    [forall i, LT (α i)] [hwf : forall i, WellFoundedLT (α i)] : WellFoundedLT (Colex (Π₀ i, α i)) :=
  DFinsupp.Lex.wellFoundedLT_of_finite (ι := ιᵒᵈ)

/--
theorem `DFinsupp.wellFoundedLT` / 定理 `DFinsupp.wellFoundedLT`

English:
theorem DFinsupp.wellFoundedLT
  statement: [forall i, Zero (α i)] [forall i, Preorder (α i)]
  proof: ⟨by
    set β := fun i => Antisymmetrization (α i) (· <= ·)
    set e : (i : ι) -> α i -> β i := fun i => toAntisymmetrization (· <= ·)
    let _ : forall i, Zero (β i) := fun i => ⟨e i 0⟩
    have : WellFounded (DFinsupp.Lex (Function.swap <| @WellOrderingRel ι)
        (fun _ => (· < ·) : (i : ι) -> β i -> β i -> Prop)) := by
      refine Lex.wellFounded' ?_ (fun i => IsWellFounded.wf) ?_
      · rintro i ⟨a⟩
        apply hbot
      · simp +unfoldPartialApp only [Function.swap]
        exact IsWellFounded.wf
refine Subrelation.wf (fun h => ?_) InvImage.wf (mapRange e fun _ => rfl) this
    obtain ⟨i, he, hl⟩ := lex_lt_of_lt_of_preorder (Function.swap WellOrderingRel) h
    exact ⟨i, fun j hj => Quot.sound (he j hj), hl⟩⟩

中文:
定理 直和有限支撑.wellFoundedLT
  结论: [对任意 i, 零 (α i)] [对任意 i, 预序 (α i)]
  证明: ⟨by
    set β := fun i => Antisymmetrization (α i) (· <= ·)
    set e : (i : ι) -> α i -> β i := fun i => toAntisymmetrization (· <= ·)
    let _ : forall i, Zero (β i) := fun i => ⟨e i 0⟩
    have : WellFounded (DFinsupp.Lex (Function.swap <| @WellOrderingRel ι)
        (fun _ => (· < ·) : (i : ι) -> β i -> β i -> Prop)) := by
      refine Lex.wellFounded' ?_ (fun i => IsWellFounded.wf) ?_
      · rintro i ⟨a⟩
        apply hbot
      · simp +unfoldPartialApp only [Function.swap]
        exact IsWellFounded.wf
refine Subrelation.wf (fun h => ?_) InvImage.wf (mapRange e fun _ => rfl) this
    obtain ⟨i, he, hl⟩ := lex_lt_of_lt_of_preorder (Function.swap WellOrderingRel) h
    exact ⟨i, fun j hj => Quot.sound (he j hj), hl⟩⟩
-/
protected theorem DFinsupp.wellFoundedLT [forall i, Zero (α i)] [forall i, Preorder (α i)]
    [forall i, WellFoundedLT (α i)] (hbot : forall ⦃i⦄ ⦃a : α i⦄, ¬a < 0) : WellFoundedLT (Π₀ i, α i) :=
  ⟨by
    set β := fun i => Antisymmetrization (α i) (· <= ·)
    set e : (i : ι) -> α i -> β i := fun i => toAntisymmetrization (· <= ·)
    let _ : forall i, Zero (β i) := fun i => ⟨e i 0⟩
    have : WellFounded (DFinsupp.Lex (Function.swap <| @WellOrderingRel ι)
        (fun _ => (· < ·) : (i : ι) -> β i -> β i -> Prop)) := by
      refine Lex.wellFounded' ?_ (fun i => IsWellFounded.wf) ?_
      · rintro i ⟨a⟩
        apply hbot
      · simp +unfoldPartialApp only [Function.swap]
        exact IsWellFounded.wf
refine Subrelation.wf (fun h => ?_) InvImage.wf (mapRange e fun _ => rfl) this
    obtain ⟨i, he, hl⟩ := lex_lt_of_lt_of_preorder (Function.swap WellOrderingRel) h
    exact ⟨i, fun j hj => Quot.sound (he j hj), hl⟩⟩

/--
Instance `DFinsupp.wellFoundedLT'` / 实例 `DFinsupp.wellFoundedLT'`

English:
instance DFinsupp.wellFoundedLT'
  body: DFinsupp.wellFoundedLT fun _ _ => not_lt_zero

中文:
实例 直和有限支撑.wellFoundedLT'
  定义体: DFinsupp.wellFoundedLT fun _ _ => not_lt_zero

Depends on / 依赖: DFinsupp, DFinsupp.wellFoundedLT, not_lt_zero, wellFoundedLT
-/
instance DFinsupp.wellFoundedLT'
    [forall i, AddMonoid (α i)] [forall i, PartialOrder (α i)] [forall i, IsBotZeroClass (α i)]
    [forall i, WellFoundedLT (α i)] : WellFoundedLT (Π₀ i, α i) :=
  DFinsupp.wellFoundedLT fun _ _ => not_lt_zero

/--
Instance `Pi.wellFoundedLT` / 实例 `Pi.wellFoundedLT`

English:
instance Pi.wellFoundedLT
  signature: [Finite ι] [forall i, Preorder (α i)] [hw : forall i, WellFoundedLT (α i)]
  body: ⟨by
    obtain h | ⟨⟨x⟩⟩ := isEmpty_or_nonempty (forall i, α i)
    · convert! emptyWf.wf
    let : forall i, Zero (α i) := fun i => ⟨(hw i).wf.min ⊤ ⟨x i, trivial⟩⟩
    have := Fintype.ofFinite ι
    refine InvImage.wf equivFunOnFintype.symm (DFinsupp.wellFoundedLT fun i a => ?_).wf
    exact (hw i).wf.not_lt_min ⊤ trivial⟩

中文:
实例 依赖函数类型.wellFoundedLT
  签名: [有限 ι] [对任意 i, 预序 (α i)] [hw : 对任意 i, WellFoundedLT (α i)]
  定义体: ⟨by
    obtain h | ⟨⟨x⟩⟩ := isEmpty_or_nonempty (forall i, α i)
    · convert! emptyWf.wf
    let : forall i, Zero (α i) := fun i => ⟨(hw i).wf.min ⊤ ⟨x i, trivial⟩⟩
    have := Fintype.ofFinite ι
    refine InvImage.wf equivFunOnFintype.symm (DFinsupp.wellFoundedLT fun i a => ?_).wf
    exact (hw i).wf.not_lt_min ⊤ trivial⟩

Depends on / 依赖: DFinsupp, DFinsupp.wellFoundedLT, Fintype, Fintype.ofFinite, InvImage, InvImage.wf, convert, emptyWf, emptyWf.wf, equivFunOnFintype, equivFunOnFintype.symm, isEmpty_or_nonempty, not_lt_min, ofFinite, wellFoundedLT, wf.min, wf.not_lt_min
-/
instance Pi.wellFoundedLT [Finite ι] [forall i, Preorder (α i)] [hw : forall i, WellFoundedLT (α i)] :
    WellFoundedLT (forall i, α i) :=
  ⟨by
    obtain h | ⟨⟨x⟩⟩ := isEmpty_or_nonempty (forall i, α i)
    · convert! emptyWf.wf
    let : forall i, Zero (α i) := fun i => ⟨(hw i).wf.min ⊤ ⟨x i, trivial⟩⟩
    have := Fintype.ofFinite ι
    refine InvImage.wf equivFunOnFintype.symm (DFinsupp.wellFoundedLT fun i a => ?_).wf
    exact (hw i).wf.not_lt_min ⊤ trivial⟩

/--
Instance `Function.wellFoundedLT` / 实例 `Function.wellFoundedLT`

English:
instance Function.wellFoundedLT
  signature: {α} [Finite ι] [Preorder α] [WellFoundedLT α]
  body: Pi.wellFoundedLT

中文:
实例 函数.wellFoundedLT
  签名: {α} [有限 ι] [预序 α] [WellFoundedLT α]
  定义体: Pi.wellFoundedLT

Depends on / 依赖: Pi.wellFoundedLT, wellFoundedLT
-/
instance Function.wellFoundedLT {α} [Finite ι] [Preorder α] [WellFoundedLT α] :
    WellFoundedLT (ι -> α) :=
  Pi.wellFoundedLT

/--
Instance `DFinsupp.wellFoundedLT_of_finite` / 实例 `DFinsupp.wellFoundedLT_of_finite`

English:
instance DFinsupp.wellFoundedLT_of_finite
  signature: [Finite ι] [forall i, Zero (α i)] [forall i, Preorder (α i)]
  body: have := Fintype.ofFinite ι
  ⟨InvImage.wf equivFunOnFintype Pi.wellFoundedLT.wf⟩

中文:
实例 直和有限支撑.wellFoundedLT_of_finite
  签名: [有限 ι] [对任意 i, 零 (α i)] [对任意 i, 预序 (α i)]
  定义体: have := Fintype.ofFinite ι
  ⟨InvImage.wf equivFunOnFintype Pi.wellFoundedLT.wf⟩

Depends on / 依赖: Fintype, Fintype.ofFinite, InvImage, InvImage.wf, Pi.wellFoundedLT.wf, equivFunOnFintype, ofFinite, wellFoundedLT
-/
instance DFinsupp.wellFoundedLT_of_finite [Finite ι] [forall i, Zero (α i)] [forall i, Preorder (α i)]
    [forall i, WellFoundedLT (α i)] : WellFoundedLT (Π₀ i, α i) :=
  have := Fintype.ofFinite ι
  ⟨InvImage.wf equivFunOnFintype Pi.wellFoundedLT.wf⟩
