/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Eric Wieser
-/
module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Nonunits
public import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# Characteristic of quotient rings
-/

public section

/--
theorem `CharP.ker_intAlgebraMap_eq_span` / 定理 `CharP.ker_intAlgebraMap_eq_span`

English:
theorem CharP.ker_intAlgebraMap_eq_span
  proof: by
  ext a
  simp [CharP.intCast_eq_zero_iff R p, Ideal.mem_span_singleton]

中文:
定理 特征p.ker_intAlgebraMap_eq_span
  证明: by
  ext a
  simp [CharP.intCast_eq_zero_iff R p, Ideal.mem_span_singleton]

Depends on / 依赖: CharP.intCast_eq_zero_iff, Ideal.mem_span_singleton, intCast_eq_zero_iff, mem_span_singleton
-/
theorem CharP.ker_intAlgebraMap_eq_span
    {R : Type*} [Ring R] (p : Nat) [CharP R p] :
    RingHom.ker (algebraMap Int R) = Ideal.span {(p : Int)} := by
  ext a
  simp [CharP.intCast_eq_zero_iff R p, Ideal.mem_span_singleton]

variable {R : Type*} [CommRing R]

namespace CharP

variable (R) in
/--
theorem `quotient` / 定理 `quotient`

English:
theorem quotient
  given: (p : Nat) [hp1 : Fact p.Prime] (hp2 : ↑p in nonunits R)
  proof: have hp0 : (p : R ⧸ (Ideal.span {(p : R)} : Ideal R)) = 0 :=
    map_natCast (Ideal.Quotient.mk (Ideal.span {(p : R)} : Ideal R)) p ▸
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span <| Set.mem_singleton _)
ringChar.of_eq
    Or.resolve_left ((Nat.dvd_prime hp1.1).1 <| ringChar.dvd hp0) fun

中文:
定理 quotient
  条件: (p : 自然数) [hp1 : Fact p.素] (hp2 : ↑p in nonunits R)
  证明: have hp0 : (p : R ⧸ (Ideal.span {(p : R)} : Ideal R)) = 0 :=
    map_natCast (Ideal.Quotient.mk (Ideal.span {(p : R)} : Ideal R)) p ▸
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span <| Set.mem_singleton _)
ringChar.of_eq
    Or.resolve_left ((Nat.dvd_prime hp1.1).1 <| ringChar.dvd hp0) fun

Depends on / 依赖: CharOne, CharOne.subsingleton, Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.mk, Ideal.mem_span_singleton, Ideal.span, Ideal.subset_span, Nat.dvd_prime, Or.resolve_left, Quotient, Set.mem_singleton, Subsingleton, Subsingleton.elim, dvd_prime, eq_zero_iff_mem, isUnit_iff_dvd_one, map_natCast, mem_singleton, mem_span_singleton, of_eq
-/
theorem quotient (p : Nat) [hp1 : Fact p.Prime] (hp2 : ↑p in nonunits R) :
    CharP (R ⧸ (Ideal.span ({(p : R)} : Set R) : Ideal R)) p :=
  have hp0 : (p : R ⧸ (Ideal.span {(p : R)} : Ideal R)) = 0 :=
    map_natCast (Ideal.Quotient.mk (Ideal.span {(p : R)} : Ideal R)) p ▸
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span <| Set.mem_singleton _)
ringChar.of_eq
    Or.resolve_left ((Nat.dvd_prime hp1.1).1 <| ringChar.dvd hp0) fun h1 =>
hp2
isUnit_iff_dvd_one.2
Ideal.mem_span_singleton.1
Ideal.Quotient.eq_zero_iff_mem.1
              @Subsingleton.elim _ (@CharOne.subsingleton _ _ (ringChar.of_eq h1)) _ _

/--
theorem `quotient'` / 定理 `quotient'`

English:
theorem quotient'
  given: (p : Nat) [CharP R p] (I : Ideal R) (h : forall x : Nat, (x : R) in I -> (x : R) = 0)
  proof: by
    rw [← cast_eq_zero_iff R p x]; rw [← map_natCast (Ideal.Quotient.mk I)]
    refine Ideal.Quotient.eq.trans (?_ : ↑x - 0 in I ↔ _)
    rw [sub_zero]
    exact ⟨h x, fun h' => h'.symm ▸ I.zero_mem⟩

中文:
定理 quotient'
  条件: (p : 自然数) [特征p R p] (I : 理想 R) (h : 对任意 x : 自然数, (x : R) in I -> (x : R) = 0)
  证明: by
    rw [← cast_eq_zero_iff R p x]; rw [← map_natCast (Ideal.Quotient.mk I)]
    refine Ideal.Quotient.eq.trans (?_ : ↑x - 0 in I ↔ _)
    rw [sub_zero]
    exact ⟨h x, fun h' => h'.symm ▸ I.zero_mem⟩

Depends on / 依赖: FilteredColimits, FilteredColimits.nontrivial, I.zero_mem, Ideal.Quotient.eq.trans, Ideal.Quotient.mk, Quotient, cast_eq_zero_iff, getColimitCocone, map_natCast, nontrivial, sub_zero, zero_mem
-/
theorem quotient' (p : Nat) [CharP R p] (I : Ideal R) (h : forall x : Nat, (x : R) in I -> (x : R) = 0) :
    CharP (R ⧸ I) p where
  cast_eq_zero_iff x := by
    rw [← cast_eq_zero_iff R p x]; rw [← map_natCast (Ideal.Quotient.mk I)]
    refine Ideal.Quotient.eq.trans (?_ : ↑x - 0 in I ↔ _)
    rw [sub_zero]
    exact ⟨h x, fun h' => h'.symm ▸ I.zero_mem⟩

/--
theorem `quotient_iff` / 定理 `quotient_iff`

English:
theorem quotient_iff
  given: (n : Nat) [CharP R n] (I : Ideal R)
  proof: by
  refine ⟨fun _ x hx => ?_, CharP.quotient' n I⟩
  rw [CharP.cast_eq_zero_iff R n]; rw [← CharP.cast_eq_zero_iff (R ⧸ I) n _]
  exact (Submodule.Quotient.mk_eq_zero I).mpr hx

中文:
定理 quotient_iff
  条件: (n : 自然数) [特征p R n] (I : 理想 R)
  证明: by
  refine ⟨fun _ x hx => ?_, CharP.quotient' n I⟩
  rw [CharP.cast_eq_zero_iff R n]; rw [← CharP.cast_eq_zero_iff (R ⧸ I) n _]
  exact (Submodule.Quotient.mk_eq_zero I).mpr hx

Depends on / 依赖: CharP.cast_eq_zero_iff, CharP.quotient, Quotient, Submodule, Submodule.Quotient.mk_eq_zero, cast_eq_zero_iff, mk_eq_zero, quotient
-/
theorem quotient_iff (n : Nat) [CharP R n] (I : Ideal R) :
    CharP (R ⧸ I) n ↔ forall x : Nat, ↑x in I -> (x : R) = 0 := by
  refine ⟨fun _ x hx => ?_, CharP.quotient' n I⟩
  rw [CharP.cast_eq_zero_iff R n]; rw [← CharP.cast_eq_zero_iff (R ⧸ I) n _]
  exact (Submodule.Quotient.mk_eq_zero I).mpr hx

/--
theorem `quotient_iff_le_ker_natCast` / 定理 `quotient_iff_le_ker_natCast`

English:
theorem quotient_iff_le_ker_natCast
  given: (n : Nat) [CharP R n] (I : Ideal R)
  proof: by
  rw [CharP.quotient_iff]; rw [RingHom.ker_eq_comap_bot]; rfl

中文:
定理 quotient_iff_le_ker_natCast
  条件: (n : 自然数) [特征p R n] (I : 理想 R)
  证明: by
  rw [CharP.quotient_iff]; rw [RingHom.ker_eq_comap_bot]; rfl

Depends on / 依赖: CharP.quotient_iff, RingHom, RingHom.ker_eq_comap_bot, ker_eq_comap_bot, quotient_iff
-/
theorem quotient_iff_le_ker_natCast (n : Nat) [CharP R n] (I : Ideal R) :
    CharP (R ⧸ I) n ↔ I.comap (Nat.castRingHom R) <= RingHom.ker (Nat.castRingHom R) := by
  rw [CharP.quotient_iff]; rw [RingHom.ker_eq_comap_bot]; rfl

end CharP

/--
lemma `Ideal.natCast_mem_of_charP_quotient` / 引理 `Ideal.natCast_mem_of_charP_quotient`

English:
lemma Ideal.natCast_mem_of_charP_quotient
  given: (p : Nat) (I : Ideal R) [CharP (R ⧸ I) p]
  proof: Ideal.Quotient.eq_zero_iff_mem.mp by simp

中文:
引理 理想.natCast_mem_of_charP_quotient
  条件: (p : 自然数) (I : 理想 R) [特征p (R ⧸ I) p]
  证明: Ideal.Quotient.eq_zero_iff_mem.mp by simp

Depends on / 依赖: Ideal.Quotient.eq_zero_iff_mem.mp, Quotient, eq_zero_iff_mem
-/
lemma Ideal.natCast_mem_of_charP_quotient (p : Nat) (I : Ideal R) [CharP (R ⧸ I) p] :
    (p : R) in I :=
Ideal.Quotient.eq_zero_iff_mem.mp by simp

/--
theorem `Ideal.Quotient.index_eq_zero` / 定理 `Ideal.Quotient.index_eq_zero`

English:
theorem Ideal.Quotient.index_eq_zero
  given: (I : Ideal R)
  statement: (↑I.toAddSubgroup.index : R ⧸ I) = 0
  proof: by
  rw [AddSubgroup.index]; rw [Nat.card_eq]
  split_ifs with hq; swap
  · simp
  let : Fintype (R ⧸ I) := @Fintype.ofFinite _ hq
  exact Nat.cast_card_eq_zero (R ⧸ I)

中文:
定理 理想.商.index_eq_zero
  条件: (I : 理想 R)
  结论: (↑I.toAddSubgroup.index : R ⧸ I) = 0
  证明: by
  rw [AddSubgroup.index]; rw [Nat.card_eq]
  split_ifs with hq; swap
  · simp
  let : Fintype (R ⧸ I) := @Fintype.ofFinite _ hq
  exact Nat.cast_card_eq_zero (R ⧸ I)

Depends on / 依赖: AddSubgroup, AddSubgroup.index, Fintype, Fintype.ofFinite, Nat.card_eq, Nat.cast_card_eq_zero, card_eq, cast_card_eq_zero, ofFinite, split_ifs
-/
theorem Ideal.Quotient.index_eq_zero (I : Ideal R) : (↑I.toAddSubgroup.index : R ⧸ I) = 0 := by
  rw [AddSubgroup.index]; rw [Nat.card_eq]
  split_ifs with hq; swap
  · simp
  let : Fintype (R ⧸ I) := @Fintype.ofFinite _ hq
  exact Nat.cast_card_eq_zero (R ⧸ I)
