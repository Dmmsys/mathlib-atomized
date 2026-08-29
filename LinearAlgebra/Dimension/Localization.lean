/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Group.Pointwise.Finset.Scalar
public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.LinearAlgebra.Dimension.DivisionRing
public import Mathlib.LinearAlgebra.LinearIndependent.Algebra
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.OreLocalization.OreSet

/-!
# Rank of localization

## Main statements

- `IsLocalizedModule.lift_rank_eq`: `rank_Rₚ Mₚ = rank R M`.
- `rank_quotient_add_rank_of_isDomain`: The **rank-nullity theorem** for commutative domains.
-/

public section

open Cardinal Module nonZeroDivisors

section CommRing

universe uR uS uT uM uN uP

variable {R : Type uR} (S : Type uS) {M : Type uM} {N : Type uN}
variable [CommRing R] [CommRing S] [AddCommGroup M] [AddCommGroup N]
variable [Module R M] [Module R N] [Algebra R S] [Module S N] [IsScalarTower R S N]
variable (p : Submonoid R) [IsLocalization p S] (f : M ->ₗ[R] N) [IsLocalizedModule p f]
variable (hp : p <= R⁰)

section
include hp

section
include f

/--
lemma `IsLocalizedModule.lift_rank_eq` / 引理 `IsLocalizedModule.lift_rank_eq`

English:
lemma IsLocalizedModule.lift_rank_eq
  proof: by
  cases subsingleton_or_nontrivial R
  · simp only [rank_subsingleton, lift_one]
  apply le_antisymm <;>
    rw [Module.rank_def]; rw [lift_iSup bddAbove_of_small] <;>
    apply ciSup_le' <;>
    intro ⟨s, hs⟩
  exacts [(IsLocalizedModule.linearIndependent_lift p f hs).choose_spec.cardinal_lift_le_rank,
    hs.of_isLocalizedModule_of_isRegular p f (le_nonZeroDivisors_iff_isRegular.mp hp)
.cardinal_lift_le_rank]

中文:
引理 是Localized模.lift_rank_eq
  证明: by
  cases subsingleton_or_nontrivial R
  · simp only [rank_subsingleton, lift_one]
  apply le_antisymm <;>
    rw [Module.rank_def]; rw [lift_iSup bddAbove_of_small] <;>
    apply ciSup_le' <;>
    intro ⟨s, hs⟩
  exacts [(IsLocalizedModule.linearIndependent_lift p f hs).choose_spec.cardinal_lift_le_rank,
    hs.of_isLocalizedModule_of_isRegular p f (le_nonZeroDivisors_iff_isRegular.mp hp)
.cardinal_lift_le_rank]

Depends on / 依赖: IsLocalizedModule, IsLocalizedModule.linearIndependent_lift, Module, Module.rank_def, bddAbove_of_small, cardinal_lift_le_rank, choose_spec, choose_spec.cardinal_lift_le_rank, ciSup_le, exacts, hs.of_isLocalizedModule_of_isRegular, le_antisymm, le_nonZeroDivisors_iff_isRegular, le_nonZeroDivisors_iff_isRegular.mp, lift_iSup, lift_one, linearIndependent_lift, of_isLocalizedModule_of_isRegular, rank_def, rank_subsingleton
-/
lemma IsLocalizedModule.lift_rank_eq :
    Cardinal.lift.{uM} (Module.rank R N) = Cardinal.lift.{uN} (Module.rank R M) := by
  cases subsingleton_or_nontrivial R
  · simp only [rank_subsingleton, lift_one]
  apply le_antisymm <;>
    rw [Module.rank_def]; rw [lift_iSup bddAbove_of_small] <;>
    apply ciSup_le' <;>
    intro ⟨s, hs⟩
  exacts [(IsLocalizedModule.linearIndependent_lift p f hs).choose_spec.cardinal_lift_le_rank,
    hs.of_isLocalizedModule_of_isRegular p f (le_nonZeroDivisors_iff_isRegular.mp hp)
.cardinal_lift_le_rank]

/--
lemma `IsLocalizedModule.finrank_eq` / 引理 `IsLocalizedModule.finrank_eq`

English:
lemma IsLocalizedModule.finrank_eq
  statement: finrank R N = finrank R M
  proof: by
  simpa using! congr_arg toNat (lift_rank_eq p f hp)

中文:
引理 是Localized模.finrank_eq
  结论: finrank R N = finrank R M
  证明: by
  simpa using! congr_arg toNat (lift_rank_eq p f hp)

Depends on / 依赖: congr_arg, lift_rank_eq
-/
lemma IsLocalizedModule.finrank_eq : finrank R N = finrank R M := by
  simpa using! congr_arg toNat (lift_rank_eq p f hp)

end

/--
lemma `IsLocalizedModule.rank_eq` / 引理 `IsLocalizedModule.rank_eq`

English:
lemma IsLocalizedModule.rank_eq
  statement: {N : Type uM} [AddCommGroup N] [Module R N] (f : M ->ₗ[R] N)
  proof: by
  simpa using lift_rank_eq p f hp

中文:
引理 是Localized模.rank_eq
  结论: {N : 类型uM} [加法交换群 N] [模 R N] (f : M ->ₗ[R] N)
  证明: by
  simpa using lift_rank_eq p f hp

Depends on / 依赖: lift_rank_eq
-/
lemma IsLocalizedModule.rank_eq {N : Type uM} [AddCommGroup N] [Module R N] (f : M ->ₗ[R] N)
    [IsLocalizedModule p f] : Module.rank R N = Module.rank R M := by
  simpa using lift_rank_eq p f hp

/--
lemma `IsLocalization.rank_eq` / 引理 `IsLocalization.rank_eq`

English:
lemma IsLocalization.rank_eq
  statement: Module.rank S N = Module.rank R N
  proof: by
  cases subsingleton_or_nontrivial R
  · have := (algebraMap R S).codomain_trivial; simp only [rank_subsingleton]
  have inj := IsLocalization.injective S hp
  apply le_antisymm <;> (rw [Module.rank]; apply ciSup_le'; intro ⟨s, hs⟩)
  · have := (faithfulSMul_iff_algebraMap_injective R S).mpr inj
    exact (hs.restrict_scalars' R).cardinal_le_rank
  · have := inj.nontrivial
    exact (hs.localization S p).cardinal_le_rank

中文:
引理 是Localization.rank_eq
  结论: 模.rank S N = 模.rank R N
  证明: by
  cases subsingleton_or_nontrivial R
  · have := (algebraMap R S).codomain_trivial; simp only [rank_subsingleton]
  have inj := IsLocalization.injective S hp
  apply le_antisymm <;> (rw [Module.rank]; apply ciSup_le'; intro ⟨s, hs⟩)
  · have := (faithfulSMul_iff_algebraMap_injective R S).mpr inj
    exact (hs.restrict_scalars' R).cardinal_le_rank
  · have := inj.nontrivial
    exact (hs.localization S p).cardinal_le_rank

Depends on / 依赖: IsLocalization, IsLocalization.injective, Module, Module.rank, algebraMap, cardinal_le_rank, ciSup_le, codomain_trivial, faithfulSMul_iff_algebraMap_injective, hs.localization, hs.restrict_scalars, inj.nontrivial, injective, le_antisymm, localization, nontrivial, rank_subsingleton, restrict_scalars, subsingleton_or_nontrivial
-/
lemma IsLocalization.rank_eq : Module.rank S N = Module.rank R N := by
  cases subsingleton_or_nontrivial R
  · have := (algebraMap R S).codomain_trivial; simp only [rank_subsingleton]
  have inj := IsLocalization.injective S hp
  apply le_antisymm <;> (rw [Module.rank]; apply ciSup_le'; intro ⟨s, hs⟩)
  · have := (faithfulSMul_iff_algebraMap_injective R S).mpr inj
    exact (hs.restrict_scalars' R).cardinal_le_rank
  · have := inj.nontrivial
    exact (hs.localization S p).cardinal_le_rank

/--
theorem `IsLocalization.finrank_eq` / 定理 `IsLocalization.finrank_eq`

English:
theorem IsLocalization.finrank_eq
  statement: finrank S N = finrank R N
  proof: by
  simp_rw [finrank, rank_eq S p hp]

中文:
定理 是Localization.finrank_eq
  结论: finrank S N = finrank R N
  证明: by
  simp_rw [finrank, rank_eq S p hp]

Depends on / 依赖: finrank, rank_eq, simp_rw
-/
theorem IsLocalization.finrank_eq : finrank S N = finrank R N := by
  simp_rw [finrank, rank_eq S p hp]

end

variable {S} in
/--
theorem `IsLocalization.linearIndepOn_finsetIntegerMultiple` / 定理 `IsLocalization.linearIndepOn_finsetIntegerMultiple`

English:
theorem IsLocalization.linearIndepOn_finsetIntegerMultiple
  statement: {A : Type*} [CommRing A] [Algebra S A]
  proof: by
  classical
  rw [← LinearIndepOn.id_image_algebraMap_iff (A := A)]; rw [finsetIntegerMultiple_image]; rw [← s.coe_smul_finset]
  rw [linearIndepOn_finset_iff] at hs ⊢
  intro f h
  rw [s.smul_finset_def]; rw [s.forall_mem_image]
  apply hs
  have inj := (IsLocalization.smul_bijective A (commonDenomOfFinset M s)).injective
  rw [← inj.eq_iff]; rw [smul_zero]; rw [s.smul_sum]; rw [← h]; rw [s.smul_finset_def]; rw [s.sum_image inj.injOn]
  exact s.sum_congr rfl fun x hx => smul_comm ..

中文:
定理 是Localization.linearIndepOn_finset整数egerMultiple
  结论: {A : 类型} [交换环 A] [代数 S A]
  证明: by
  classical
  rw [← LinearIndepOn.id_image_algebraMap_iff (A := A)]; rw [finsetIntegerMultiple_image]; rw [← s.coe_smul_finset]
  rw [linearIndepOn_finset_iff] at hs ⊢
  intro f h
  rw [s.smul_finset_def]; rw [s.forall_mem_image]
  apply hs
  have inj := (IsLocalization.smul_bijective A (commonDenomOfFinset M s)).injective
  rw [← inj.eq_iff]; rw [smul_zero]; rw [s.smul_sum]; rw [← h]; rw [s.smul_finset_def]; rw [s.sum_image inj.injOn]
  exact s.sum_congr rfl fun x hx => smul_comm ..

Depends on / 依赖: IsLocalization, IsLocalization.smul_bijective, LinearIndepOn, LinearIndepOn.id_image_algebraMap_iff, classical, coe_smul_finset, commonDenomOfFinset, eq_iff, finsetIntegerMultiple_image, forall_mem_image, id_image_algebraMap_iff, inj.eq_iff, inj.injOn, injective, linearIndepOn_finset_iff, s.coe_smul_finset, s.forall_mem_image, s.smul_finset_def, s.smul_sum, s.sum_congr
-/
theorem IsLocalization.linearIndepOn_finsetIntegerMultiple {A : Type*} [CommRing A] [Algebra S A]
    [Algebra R A] [IsScalarTower R S A] (M : Submonoid S) [IsLocalization M A] [FaithfulSMul S A]
    {s : Finset A} (hs : LinearIndepOn R id (s : Set A)) [DecidableEq S] :
    LinearIndepOn R id (finsetIntegerMultiple M s : Set S) := by
  classical
  rw [← LinearIndepOn.id_image_algebraMap_iff (A := A)]; rw [finsetIntegerMultiple_image]; rw [← s.coe_smul_finset]
  rw [linearIndepOn_finset_iff] at hs ⊢
  intro f h
  rw [s.smul_finset_def]; rw [s.forall_mem_image]
  apply hs
  have inj := (IsLocalization.smul_bijective A (commonDenomOfFinset M s)).injective
  rw [← inj.eq_iff]; rw [smul_zero]; rw [s.smul_sum]; rw [← h]; rw [s.smul_finset_def]; rw [s.sum_image inj.injOn]
  exact s.sum_congr rfl fun x hx => smul_comm ..

section

variable (R N) [IsFractionRing R S]

/--
theorem `IsFractionRing.rank_right_eq` / 定理 `IsFractionRing.rank_right_eq`

English:
theorem IsFractionRing.rank_right_eq
  statement: Module.rank S N = Module.rank R N
  proof: IsLocalization.rank_eq S R⁰ le_rfl

中文:
定理 IsFractionRing.rank_right_eq
  结论: 模.rank S N = 模.rank R N
  证明: IsLocalization.rank_eq S R⁰ le_rfl

Depends on / 依赖: IsLocalization, IsLocalization.rank_eq, le_rfl, rank_eq
-/
theorem IsFractionRing.rank_right_eq : Module.rank S N = Module.rank R N :=
  IsLocalization.rank_eq S R⁰ le_rfl

/--
theorem `IsFractionRing.finrank_right_eq` / 定理 `IsFractionRing.finrank_right_eq`

English:
theorem IsFractionRing.finrank_right_eq
  statement: finrank S N = finrank R N
  proof: IsLocalization.finrank_eq S R⁰ le_rfl

中文:
定理 IsFractionRing.finrank_right_eq
  结论: finrank S N = finrank R N
  证明: IsLocalization.finrank_eq S R⁰ le_rfl

Depends on / 依赖: IsLocalization, IsLocalization.finrank_eq, finrank_eq, le_rfl
-/
theorem IsFractionRing.finrank_right_eq : finrank S N = finrank R N :=
  IsLocalization.finrank_eq S R⁰ le_rfl

end

variable (R) in
open IsLocalization in
/--
theorem `IsFractionRing.finrank_left_eq` / 定理 `IsFractionRing.finrank_left_eq`

English:
theorem IsFractionRing.finrank_left_eq
  statement: (A : Type*) [CommRing A] [Algebra S A] [Algebra R A]
  proof: by
  nontriviality R
  classical
  apply Cardinal.toNat_eq_of_forall_le_iff
  intro n
  simp_rw [Module.le_rank_iff_exists_finset, LinearIndepOn]
  constructor
  · rintro ⟨s, rfl, hs⟩
    let f : S ↪ A := ⟨algebraMap S A, FaithfulSMul.algebraMap_injective S A⟩
    exact ⟨s.map f, s.card_map f,
      (linearIndependent_equiv (s.equivMap f)).mp (LinearIndependent.algebraMap_comp_iff.mpr hs)⟩
  · rintro ⟨s, rfl, hs⟩
    exact ⟨finsetIntegerMultiple S⁰ s, card_finsetIntegerMultiple S⁰ s,
      linearIndepOn_finsetIntegerMultiple S⁰ hs⟩

中文:
定理 IsFractionRing.finrank_left_eq
  结论: (A : 类型) [交换环 A] [代数 S A] [代数 R A]
  证明: by
  nontriviality R
  classical
  apply Cardinal.toNat_eq_of_forall_le_iff
  intro n
  simp_rw [Module.le_rank_iff_exists_finset, LinearIndepOn]
  constructor
  · rintro ⟨s, rfl, hs⟩
    let f : S ↪ A := ⟨algebraMap S A, FaithfulSMul.algebraMap_injective S A⟩
    exact ⟨s.map f, s.card_map f,
      (linearIndependent_equiv (s.equivMap f)).mp (LinearIndependent.algebraMap_comp_iff.mpr hs)⟩
  · rintro ⟨s, rfl, hs⟩
    exact ⟨finsetIntegerMultiple S⁰ s, card_finsetIntegerMultiple S⁰ s,
      linearIndepOn_finsetIntegerMultiple S⁰ hs⟩

Depends on / 依赖: Cardinal, Cardinal.toNat_eq_of_forall_le_iff, FaithfulSMul, FaithfulSMul.algebraMap_injective, LinearIndepOn, LinearIndependent, LinearIndependent.algebraMap_comp_iff.mpr, Module, Module.le_rank_iff_exists_finset, algebraMap, algebraMap_comp_iff, algebraMap_injective, card_finsetIntegerMultiple, card_map, classical, equivMap, finsetIntegerMultiple, le_rank_iff_exists_finset, linearIndepOn_finsetIntegerMultiple, linearIndependent_equiv
-/
theorem IsFractionRing.finrank_left_eq (A : Type*) [CommRing A] [Algebra S A] [Algebra R A]
    [IsScalarTower R S A] [IsFractionRing S A] : Module.finrank R S = Module.finrank R A := by
  nontriviality R
  classical
  apply Cardinal.toNat_eq_of_forall_le_iff
  intro n
  simp_rw [Module.le_rank_iff_exists_finset, LinearIndepOn]
  constructor
  · rintro ⟨s, rfl, hs⟩
    let f : S ↪ A := ⟨algebraMap S A, FaithfulSMul.algebraMap_injective S A⟩
    exact ⟨s.map f, s.card_map f,
      (linearIndependent_equiv (s.equivMap f)).mp (LinearIndependent.algebraMap_comp_iff.mpr hs)⟩
  · rintro ⟨s, rfl, hs⟩
    exact ⟨finsetIntegerMultiple S⁰ s, card_finsetIntegerMultiple S⁰ s,
      linearIndepOn_finsetIntegerMultiple S⁰ hs⟩

/--
theorem `IsFractionRing.finrank_eq` / 定理 `IsFractionRing.finrank_eq`

English:
theorem IsFractionRing.finrank_eq
  statement: (A K B L : Type*)
  proof: (finrank_right_eq A K L).trans (finrank_left_eq A B L).symm

中文:
定理 IsFractionRing.finrank_eq
  结论: (A K B L : 类型)
  证明: (finrank_right_eq A K L).trans (finrank_left_eq A B L).symm
-/
protected theorem IsFractionRing.finrank_eq (A K B L : Type*)
    [CommRing A] [CommRing K] [CommRing B] [CommRing L] [Algebra A B] [Module K L]
    [Algebra A K] [Algebra B L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
    [IsFractionRing A K] [IsFractionRing B L] : Module.finrank K L = Module.finrank A B :=
  (finrank_right_eq A K L).trans (finrank_left_eq A B L).symm

variable (R M) in
/--
theorem `exists_set_linearIndependent_of_isDomain` / 定理 `exists_set_linearIndependent_of_isDomain`

English:
theorem exists_set_linearIndependent_of_isDomain
  given: [IsDomain R]
  proof: by
  obtain ⟨w, hw⟩ :=
IsLocalizedModule.linearIndependent_lift R⁰ (LocalizedModule.mkLinearMap R⁰ M)
      Module.Free.chooseBasis (FractionRing R) (LocalizedModule R⁰ M)
.linearIndependent.restrict_scalars' _
  refine ⟨Set.range w, ?_, (linearIndepOn_id_range_iff hw.injective).mpr hw⟩
  apply Cardinal.lift_injective.{max uR uM}
  rw [Cardinal.mk_range_eq_of_injective hw.injective]; rw [← Module.Free.rank_eq_card_chooseBasisIndex]; rw [IsLocalization.rank_eq (FractionRing R) R⁰ le_rfl]; rw [IsLocalizedModule.lift_rank_eq R⁰ (LocalizedModule.mkLinearMap R⁰ M) le_rfl]

中文:
定理 存在_set_linearIndependent_of_isDomain
  条件: [是整环 R]
  证明: by
  obtain ⟨w, hw⟩ :=
IsLocalizedModule.linearIndependent_lift R⁰ (LocalizedModule.mkLinearMap R⁰ M)
      Module.Free.chooseBasis (FractionRing R) (LocalizedModule R⁰ M)
.linearIndependent.restrict_scalars' _
  refine ⟨Set.range w, ?_, (linearIndepOn_id_range_iff hw.injective).mpr hw⟩
  apply Cardinal.lift_injective.{max uR uM}
  rw [Cardinal.mk_range_eq_of_injective hw.injective]; rw [← Module.Free.rank_eq_card_chooseBasisIndex]; rw [IsLocalization.rank_eq (FractionRing R) R⁰ le_rfl]; rw [IsLocalizedModule.lift_rank_eq R⁰ (LocalizedModule.mkLinearMap R⁰ M) le_rfl]

Depends on / 依赖: Cardinal, Cardinal.lift_injective, Cardinal.mk_range_eq_of_injective, FractionRing, IsLocalization, IsLocalization.rank_eq, IsLocalizedModule, IsLocalizedModule.linearIndependent_lift, LocalizedModule, LocalizedModule.mkLinearMap, Module, Module.Free.chooseBasis, Module.Free.rank_eq_card_chooseBasisIndex, Set.range, chooseBasis, hw.injective, injective, le_rfl, lift_injective, linearIndepOn_id_range_iff
-/
theorem exists_set_linearIndependent_of_isDomain [IsDomain R] :
    exists s : Set M, #s = Module.rank R M ∧ LinearIndepOn R id s := by
  obtain ⟨w, hw⟩ :=
IsLocalizedModule.linearIndependent_lift R⁰ (LocalizedModule.mkLinearMap R⁰ M)
      Module.Free.chooseBasis (FractionRing R) (LocalizedModule R⁰ M)
.linearIndependent.restrict_scalars' _
  refine ⟨Set.range w, ?_, (linearIndepOn_id_range_iff hw.injective).mpr hw⟩
  apply Cardinal.lift_injective.{max uR uM}
  rw [Cardinal.mk_range_eq_of_injective hw.injective]; rw [← Module.Free.rank_eq_card_chooseBasisIndex]; rw [IsLocalization.rank_eq (FractionRing R) R⁰ le_rfl]; rw [IsLocalizedModule.lift_rank_eq R⁰ (LocalizedModule.mkLinearMap R⁰ M) le_rfl]

/--
theorem `rank_quotient_add_rank_of_isDomain` / 定理 `rank_quotient_add_rank_of_isDomain`

English:
theorem rank_quotient_add_rank_of_isDomain
  given: [IsDomain R] (M' : Submodule R M)
  proof: by
  apply lift_injective.{max uR uM}
  simp_rw [lift_add, ← IsLocalizedModule.lift_rank_eq R⁰ (M'.toLocalized R⁰) le_rfl,
    ← IsLocalizedModule.lift_rank_eq R⁰ (LocalizedModule.mkLinearMap R⁰ M) le_rfl,
    ← IsLocalizedModule.lift_rank_eq R⁰ (M'.toLocalizedQuotient R⁰) le_rfl,
    ← IsLocalization.rank_eq (FractionRing R) R⁰ le_rfl,
    ← lift_add, rank_quotient_add_rank_of_divisionRing]

universe w in

中文:
定理 rank_quotient_add_rank_of_isDomain
  条件: [是整环 R] (M' : 子模 R M)
  证明: by
  apply lift_injective.{max uR uM}
  simp_rw [lift_add, ← IsLocalizedModule.lift_rank_eq R⁰ (M'.toLocalized R⁰) le_rfl,
    ← IsLocalizedModule.lift_rank_eq R⁰ (LocalizedModule.mkLinearMap R⁰ M) le_rfl,
    ← IsLocalizedModule.lift_rank_eq R⁰ (M'.toLocalizedQuotient R⁰) le_rfl,
    ← IsLocalization.rank_eq (FractionRing R) R⁰ le_rfl,
    ← lift_add, rank_quotient_add_rank_of_divisionRing]

universe w in

Depends on / 依赖: FractionRing, IsLocalization, IsLocalization.rank_eq, IsLocalizedModule, IsLocalizedModule.lift_rank_eq, LocalizedModule, LocalizedModule.mkLinearMap, le_rfl, lift_add, lift_injective, lift_rank_eq, mkLinearMap, rank_eq, rank_quotient_add_rank_of_divisionRing, simp_rw, toLocalized, toLocalizedQuotient
-/
theorem rank_quotient_add_rank_of_isDomain [IsDomain R] (M' : Submodule R M) :
    Module.rank R (M ⧸ M') + Module.rank R M' = Module.rank R M := by
  apply lift_injective.{max uR uM}
  simp_rw [lift_add, ← IsLocalizedModule.lift_rank_eq R⁰ (M'.toLocalized R⁰) le_rfl,
    ← IsLocalizedModule.lift_rank_eq R⁰ (LocalizedModule.mkLinearMap R⁰ M) le_rfl,
    ← IsLocalizedModule.lift_rank_eq R⁰ (M'.toLocalizedQuotient R⁰) le_rfl,
    ← IsLocalization.rank_eq (FractionRing R) R⁰ le_rfl,
    ← lift_add, rank_quotient_add_rank_of_divisionRing]

universe w in
/--
Instance `IsDomain.hasRankNullity` / 实例 `IsDomain.hasRankNullity`

English:
instance IsDomain.hasRankNullity
  signature: [IsDomain R]
  body: rank_quotient_add_rank_of_isDomain
  exists_set_linearIndependent M := exists_set_linearIndependent_of_isDomain R M

中文:
实例 是整环.hasRankNullity
  签名: [是整环 R]
  定义体: rank_quotient_add_rank_of_isDomain
  exists_set_linearIndependent M := exists_set_linearIndependent_of_isDomain R M

Depends on / 依赖: rank_quotient_add_rank_of_isDomain
-/
instance IsDomain.hasRankNullity [IsDomain R] : HasRankNullity.{w} R where
  rank_quotient_add_rank := rank_quotient_add_rank_of_isDomain
  exists_set_linearIndependent M := exists_set_linearIndependent_of_isDomain R M

namespace IsBaseChange

open Cardinal TensorProduct

section

variable {p} [Free S N] [StrongRankCondition S] {T : Type uT} [CommRing T] [Algebra R T]
  (hpT : Algebra.algebraMapSubmonoid T p <= T⁰) [StrongRankCondition (S otimes[R] T)]
  {P : Type uP} [AddCommGroup P] [Module R P] [Module T P] [IsScalarTower R T P]
  {g : M ->ₗ[R] P} (bc : IsBaseChange T g)

include S hp hpT f bc

/--
theorem `lift_rank_eq_of_le_nonZeroDivisors` / 定理 `lift_rank_eq_of_le_nonZeroDivisors`

English:
theorem lift_rank_eq_of_le_nonZeroDivisors
  proof: by
  rw [← lift_inj.{_]; rw [max uS uT uN}]; rw [lift_lift]; rw [lift_lift]
  let ST := S otimes[R] T
  conv_rhs => rw [← lift_lift.{uN, max uS uT uP}, ← IsLocalizedModule.lift_rank_eq p f hp,
    ← IsLocalization.rank_eq S p hp, lift_lift, ← lift_lift.{max uS uT, max uM uP},
    ← rank_baseChange (R := ST), ← lift_id'.{max uS uT, max uS uT uN} (Module.rank ..),
    lift_lift, ← lift_lift.{max uS uT uP, uM}]
  let _ : Algebra T ST := Algebra.TensorProduct.rightAlgebra
  set pT := Algebra.algebraMapSubmonoid T p
  rw [← lift_lift.{max uS uT]; rw [max uM uN}]; rw [← lift_umax.{uP}]; rw [← IsLocalizedModule.lift_rank_eq pT (mk T ST P 1) hpT]; rw [← IsLocalization.rank_eq ST pT hpT]; rw [lift_id'.{uP]; rw [max uS uT}]; rw [← lift_id'.{max uS uT]; rw [max uS uT uP} (Module.rank ..)]; rw [lift_lift]; rw [← lift_lift.{max uS uT uN]; rw [uM}]; rw [lift_inj]
exact LinearEquiv.lift_rank_eq AlgebraTensorModule.congr (.refl ST ST) bc.equiv.symm ≪≫ₗ
    AlgebraTensorModule.cancelBaseChange .. ≪≫ₗ (AlgebraTensorModule.cancelBaseChange ..).symm ≪≫ₗ
    AlgebraTensorModule.congr (.refl ..) ((isLocalizedModule_iff_isBaseChange p S f).mp ‹_›).equiv

中文:
定理 lift_rank_eq_of_le_nonZeroDivisors
  证明: by
  rw [← lift_inj.{_]; rw [max uS uT uN}]; rw [lift_lift]; rw [lift_lift]
  let ST := S otimes[R] T
  conv_rhs => rw [← lift_lift.{uN, max uS uT uP}, ← IsLocalizedModule.lift_rank_eq p f hp,
    ← IsLocalization.rank_eq S p hp, lift_lift, ← lift_lift.{max uS uT, max uM uP},
    ← rank_baseChange (R := ST), ← lift_id'.{max uS uT, max uS uT uN} (Module.rank ..),
    lift_lift, ← lift_lift.{max uS uT uP, uM}]
  let _ : Algebra T ST := Algebra.TensorProduct.rightAlgebra
  set pT := Algebra.algebraMapSubmonoid T p
  rw [← lift_lift.{max uS uT]; rw [max uM uN}]; rw [← lift_umax.{uP}]; rw [← IsLocalizedModule.lift_rank_eq pT (mk T ST P 1) hpT]; rw [← IsLocalization.rank_eq ST pT hpT]; rw [lift_id'.{uP]; rw [max uS uT}]; rw [← lift_id'.{max uS uT]; rw [max uS uT uP} (Module.rank ..)]; rw [lift_lift]; rw [← lift_lift.{max uS uT uN]; rw [uM}]; rw [lift_inj]
exact LinearEquiv.lift_rank_eq AlgebraTensorModule.congr (.refl ST ST) bc.equiv.symm ≪≫ₗ
    AlgebraTensorModule.cancelBaseChange .. ≪≫ₗ (AlgebraTensorModule.cancelBaseChange ..).symm ≪≫ₗ
    AlgebraTensorModule.congr (.refl ..) ((isLocalizedModule_iff_isBaseChange p S f).mp ‹_›).equiv

Depends on / 依赖: Algebra, Algebra.TensorProduct.rightAlgebra, Algebra.algebraMapSubmonoid, IsLocalization, IsLocalization.rank_eq, IsLocalizedModule, IsLocalizedModule.lift_rank_eq, Module, Module.rank, TensorProduct, algebraMapSubmonoid, conv_rhs, lift_id, lift_inj, lift_lift, lift_rank_eq, otimes, rank_baseChange, rank_eq, rightAlgebra
-/
theorem lift_rank_eq_of_le_nonZeroDivisors :
    Cardinal.lift.{uM} (Module.rank T P) = Cardinal.lift.{uP} (Module.rank R M) := by
  rw [← lift_inj.{_]; rw [max uS uT uN}]; rw [lift_lift]; rw [lift_lift]
  let ST := S otimes[R] T
  conv_rhs => rw [← lift_lift.{uN, max uS uT uP}, ← IsLocalizedModule.lift_rank_eq p f hp,
    ← IsLocalization.rank_eq S p hp, lift_lift, ← lift_lift.{max uS uT, max uM uP},
    ← rank_baseChange (R := ST), ← lift_id'.{max uS uT, max uS uT uN} (Module.rank ..),
    lift_lift, ← lift_lift.{max uS uT uP, uM}]
  let _ : Algebra T ST := Algebra.TensorProduct.rightAlgebra
  set pT := Algebra.algebraMapSubmonoid T p
  rw [← lift_lift.{max uS uT]; rw [max uM uN}]; rw [← lift_umax.{uP}]; rw [← IsLocalizedModule.lift_rank_eq pT (mk T ST P 1) hpT]; rw [← IsLocalization.rank_eq ST pT hpT]; rw [lift_id'.{uP]; rw [max uS uT}]; rw [← lift_id'.{max uS uT]; rw [max uS uT uP} (Module.rank ..)]; rw [lift_lift]; rw [← lift_lift.{max uS uT uN]; rw [uM}]; rw [lift_inj]
exact LinearEquiv.lift_rank_eq AlgebraTensorModule.congr (.refl ST ST) bc.equiv.symm ≪≫ₗ
    AlgebraTensorModule.cancelBaseChange .. ≪≫ₗ (AlgebraTensorModule.cancelBaseChange ..).symm ≪≫ₗ
    AlgebraTensorModule.congr (.refl ..) ((isLocalizedModule_iff_isBaseChange p S f).mp ‹_›).equiv

/--
theorem `finrank_eq_of_le_nonZeroDivisors` / 定理 `finrank_eq_of_le_nonZeroDivisors`

English:
theorem finrank_eq_of_le_nonZeroDivisors
  statement: finrank T P = finrank R M
  proof: by
  simpa using! congr_arg toNat (lift_rank_eq_of_le_nonZeroDivisors S f hp hpT bc)

omit bc

中文:
定理 finrank_eq_of_le_nonZeroDivisors
  结论: finrank T P = finrank R M
  证明: by
  simpa using! congr_arg toNat (lift_rank_eq_of_le_nonZeroDivisors S f hp hpT bc)

omit bc

Depends on / 依赖: congr_arg, lift_rank_eq_of_le_nonZeroDivisors
-/
theorem finrank_eq_of_le_nonZeroDivisors : finrank T P = finrank R M := by
  simpa using! congr_arg toNat (lift_rank_eq_of_le_nonZeroDivisors S f hp hpT bc)

omit bc
/--
theorem `rank_eq_of_le_nonZeroDivisors` / 定理 `rank_eq_of_le_nonZeroDivisors`

English:
theorem rank_eq_of_le_nonZeroDivisors
  statement: {P : Type uM} [AddCommGroup P] [Module R P] [Module T P]
  proof: by
  simpa using lift_rank_eq_of_le_nonZeroDivisors S f hp hpT bc

中文:
定理 rank_eq_of_le_nonZeroDivisors
  结论: {P : 类型uM} [加法交换群 P] [模 R P] [模 T P]
  证明: by
  simpa using lift_rank_eq_of_le_nonZeroDivisors S f hp hpT bc

Depends on / 依赖: lift_rank_eq_of_le_nonZeroDivisors
-/
theorem rank_eq_of_le_nonZeroDivisors {P : Type uM} [AddCommGroup P] [Module R P] [Module T P]
    [IsScalarTower R T P] {g : M ->ₗ[R] P} (bc : IsBaseChange T g) :
    Module.rank T P = Module.rank R M := by
  simpa using lift_rank_eq_of_le_nonZeroDivisors S f hp hpT bc

end

variable {p} {T : Type uT} [CommRing T] [NoZeroDivisors T] [Algebra R T] [FaithfulSMul R T]
  {P : Type uP} [AddCommGroup P] [Module R P] [Module T P] [IsScalarTower R T P]
  {g : M ->ₗ[R] P} (bc : IsBaseChange T g)

include bc

/--
theorem `lift_rank_eq` / 定理 `lift_rank_eq`

English:
theorem lift_rank_eq
  proof: by
  have inj := FaithfulSMul.algebraMap_injective R T
  have := inj.noZeroDivisors _ (map_zero _) (map_mul _)
  cases subsingleton_or_nontrivial R
  · have := (algebraMap R T).codomain_trivial; simp only [rank_subsingleton, lift_one]
  have := (isDomain_iff_noZeroDivisors_and_nontrivial T).mpr
    ⟨‹_›, (FaithfulSMul.algebraMap_injective R T).nontrivial⟩
  let FR := FractionRing R
  let FT := FractionRing T
  replace inj : Function.Injective (algebraMap R FT) := (IsFractionRing.injective T _).comp inj
  let g := TensorProduct.mk T FT P 1
  have : IsLocalizedModule R⁰ (TensorProduct.mk R FR FT 1) := inferInstance
  let _ : Algebra FT (FR otimes[R] FT) := Algebra.TensorProduct.rightAlgebra
.symm.isField .atUnits _ _ ?_ let _ := isLocalizedModule_iff_isLocalization.mp this
.toField (Field.toIsField FT)
  on_goal 2 => rintro _ ⟨_, mem, rfl⟩; exact (map_ne_zero_of_mem_nonZeroDivisors _ inj mem).isUnit
  have := bc.comp_iff.2 ((isLocalizedModule_iff_isBaseChange T⁰ FT g).1 inferInstance)
  rw [← lift_inj.{_]; rw [max uT uP}]; rw [lift_lift]; rw [lift_lift]; rw [← lift_lift.{max uT uP]; rw [uM}]; rw [← IsLocalizedModule.lift_rank_eq T⁰ g le_rfl]; rw [lift_lift]; rw [← lift_lift.{uM}]; rw [← IsLocalization.rank_eq FT T⁰ le_rfl]; rw [lift_rank_eq_of_le_nonZeroDivisors FR (LocalizedModule.mkLinearMap R⁰ M) le_rfl
      (map_le_nonZeroDivisors_of_injective _ inj le_rfl) this]; rw [lift_lift]

中文:
定理 lift_rank_eq
  证明: by
  have inj := FaithfulSMul.algebraMap_injective R T
  have := inj.noZeroDivisors _ (map_zero _) (map_mul _)
  cases subsingleton_or_nontrivial R
  · have := (algebraMap R T).codomain_trivial; simp only [rank_subsingleton, lift_one]
  have := (isDomain_iff_noZeroDivisors_and_nontrivial T).mpr
    ⟨‹_›, (FaithfulSMul.algebraMap_injective R T).nontrivial⟩
  let FR := FractionRing R
  let FT := FractionRing T
  replace inj : Function.Injective (algebraMap R FT) := (IsFractionRing.injective T _).comp inj
  let g := TensorProduct.mk T FT P 1
  have : IsLocalizedModule R⁰ (TensorProduct.mk R FR FT 1) := inferInstance
  let _ : Algebra FT (FR otimes[R] FT) := Algebra.TensorProduct.rightAlgebra
.symm.isField .atUnits _ _ ?_ let _ := isLocalizedModule_iff_isLocalization.mp this
.toField (Field.toIsField FT)
  on_goal 2 => rintro _ ⟨_, mem, rfl⟩; exact (map_ne_zero_of_mem_nonZeroDivisors _ inj mem).isUnit
  have := bc.comp_iff.2 ((isLocalizedModule_iff_isBaseChange T⁰ FT g).1 inferInstance)
  rw [← lift_inj.{_]; rw [max uT uP}]; rw [lift_lift]; rw [lift_lift]; rw [← lift_lift.{max uT uP]; rw [uM}]; rw [← IsLocalizedModule.lift_rank_eq T⁰ g le_rfl]; rw [lift_lift]; rw [← lift_lift.{uM}]; rw [← IsLocalization.rank_eq FT T⁰ le_rfl]; rw [lift_rank_eq_of_le_nonZeroDivisors FR (LocalizedModule.mkLinearMap R⁰ M) le_rfl
      (map_le_nonZeroDivisors_of_injective _ inj le_rfl) this]; rw [lift_lift]

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, FractionRing, Function, Function.Injective, Injective, IsFractionRing, IsFractionRing.injective, algebraMap, algebraMap_injective, codomain_trivial, inj.noZeroDivisors, injective, isDomain_iff_noZeroDivisors_and_nontrivial, lift_one, map_mul, map_zero, noZeroDivisors, nontrivial, rank_subsingleton
-/
theorem lift_rank_eq :
    Cardinal.lift.{uM} (Module.rank T P) = Cardinal.lift.{uP} (Module.rank R M) := by
  have inj := FaithfulSMul.algebraMap_injective R T
  have := inj.noZeroDivisors _ (map_zero _) (map_mul _)
  cases subsingleton_or_nontrivial R
  · have := (algebraMap R T).codomain_trivial; simp only [rank_subsingleton, lift_one]
  have := (isDomain_iff_noZeroDivisors_and_nontrivial T).mpr
    ⟨‹_›, (FaithfulSMul.algebraMap_injective R T).nontrivial⟩
  let FR := FractionRing R
  let FT := FractionRing T
  replace inj : Function.Injective (algebraMap R FT) := (IsFractionRing.injective T _).comp inj
  let g := TensorProduct.mk T FT P 1
  have : IsLocalizedModule R⁰ (TensorProduct.mk R FR FT 1) := inferInstance
  let _ : Algebra FT (FR otimes[R] FT) := Algebra.TensorProduct.rightAlgebra
.symm.isField .atUnits _ _ ?_ let _ := isLocalizedModule_iff_isLocalization.mp this
.toField (Field.toIsField FT)
  on_goal 2 => rintro _ ⟨_, mem, rfl⟩; exact (map_ne_zero_of_mem_nonZeroDivisors _ inj mem).isUnit
  have := bc.comp_iff.2 ((isLocalizedModule_iff_isBaseChange T⁰ FT g).1 inferInstance)
  rw [← lift_inj.{_]; rw [max uT uP}]; rw [lift_lift]; rw [lift_lift]; rw [← lift_lift.{max uT uP]; rw [uM}]; rw [← IsLocalizedModule.lift_rank_eq T⁰ g le_rfl]; rw [lift_lift]; rw [← lift_lift.{uM}]; rw [← IsLocalization.rank_eq FT T⁰ le_rfl]; rw [lift_rank_eq_of_le_nonZeroDivisors FR (LocalizedModule.mkLinearMap R⁰ M) le_rfl
      (map_le_nonZeroDivisors_of_injective _ inj le_rfl) this]; rw [lift_lift]

/--
theorem `finrank_eq` / 定理 `finrank_eq`

English:
theorem finrank_eq
  statement: finrank T P = finrank R M
  proof: by simpa using! congr_arg toNat bc.lift_rank_eq

omit bc

中文:
定理 finrank_eq
  结论: finrank T P = finrank R M
  证明: by simpa using! congr_arg toNat bc.lift_rank_eq

omit bc

Depends on / 依赖: bc.lift_rank_eq, congr_arg, lift_rank_eq
-/
theorem finrank_eq : finrank T P = finrank R M := by simpa using! congr_arg toNat bc.lift_rank_eq

omit bc
/--
theorem `rank_eq` / 定理 `rank_eq`

English:
theorem rank_eq
  statement: {P : Type uM} [AddCommGroup P] [Module R P] [Module T P] [IsScalarTower R T P]
  proof: by
  simpa using bc.lift_rank_eq

中文:
定理 rank_eq
  结论: {P : 类型uM} [加法交换群 P] [模 R P] [模 T P] [标量塔 R T P]
  证明: by
  simpa using bc.lift_rank_eq

Depends on / 依赖: bc.lift_rank_eq, lift_rank_eq
-/
theorem rank_eq {P : Type uM} [AddCommGroup P] [Module R P] [Module T P] [IsScalarTower R T P]
    {g : M ->ₗ[R] P} (bc : IsBaseChange T g) : Module.rank T P = Module.rank R M := by
  simpa using bc.lift_rank_eq

end IsBaseChange

end CommRing

section Ring

variable {R} [Ring R] [IsDomain R]

/--
lemma `aleph0_le_rank_of_isEmpty_oreSet` / 引理 `aleph0_le_rank_of_isEmpty_oreSet`

English:
lemma aleph0_le_rank_of_isEmpty_oreSet
  given: (hS : IsEmpty (OreLocalization.OreSet R⁰))
  proof: by
  rw [← not_nonempty_iff]; rw [OreLocalization.nonempty_oreSet_iff_of_noZeroDivisors] at hS
  push Not at hS
  obtain ⟨r, s, h⟩ := hS
  refine Cardinal.aleph0_le.mpr fun n => ?_
  suffices LinearIndependent R (fun (i : Fin n) => r * s ^ (i : Nat)) by
    simpa using this.cardinal_lift_le_rank
  suffices forall (g : Nat -> R) (x), (∑ i in Finset.range n, g i • (r * s ^ (i + x))) = 0 ->
      forall i < n, g i = 0 by
    refine Fintype.linearIndependent_iff.mpr fun g hg i => ?_
    simpa only [dif_pos i.prop] using this (fun i => if h : i < n then g ⟨i, h⟩ else 0) 0
      (by simp [← Fin.sum_univ_eq_sum_range, ← hg]) i i.prop
  intro g x hg i hin
  induction n generalizing g x i with
  | zero => contradiction
  | succ n IH =>
    rw [Finset.sum_range_succ'] at hg
    by_cases hg0 : g 0 = 0
    · simp only [hg0, zero_smul, add_zero, add_assoc] at hg
      cases i; exacts [hg0, IH _ _ hg _ (Nat.succ_lt_succ_iff.mp hin)]
    simp only [zero_add, pow_add _ _ x,
      ← mul_assoc, pow_succ, ← Finset.sum_mul, smul_eq_mul] at hg
    rw [← neg_eq_iff_add_eq_zero]; rw [← neg_mul]; rw [← neg_mul] at hg
    have := mul_right_cancel₀ (mem_nonZeroDivisors_iff_ne_zero.mp (s ^ x).prop) hg
    exact (h _ ⟨(g 0), mem_nonZeroDivisors_iff_ne_zero.mpr (by simpa)⟩ this.symm).elim

中文:
引理 aleph0_le_rank_of_isEmpty_oreSet
  条件: (hS : 是空 (OreLocalization.OreSet R⁰))
  证明: by
  rw [← not_nonempty_iff]; rw [OreLocalization.nonempty_oreSet_iff_of_noZeroDivisors] at hS
  push Not at hS
  obtain ⟨r, s, h⟩ := hS
  refine Cardinal.aleph0_le.mpr fun n => ?_
  suffices LinearIndependent R (fun (i : Fin n) => r * s ^ (i : Nat)) by
    simpa using this.cardinal_lift_le_rank
  suffices forall (g : Nat -> R) (x), (∑ i in Finset.range n, g i • (r * s ^ (i + x))) = 0 ->
      forall i < n, g i = 0 by
    refine Fintype.linearIndependent_iff.mpr fun g hg i => ?_
    simpa only [dif_pos i.prop] using this (fun i => if h : i < n then g ⟨i, h⟩ else 0) 0
      (by simp [← Fin.sum_univ_eq_sum_range, ← hg]) i i.prop
  intro g x hg i hin
  induction n generalizing g x i with
  | zero => contradiction
  | succ n IH =>
    rw [Finset.sum_range_succ'] at hg
    by_cases hg0 : g 0 = 0
    · simp only [hg0, zero_smul, add_zero, add_assoc] at hg
      cases i; exacts [hg0, IH _ _ hg _ (Nat.succ_lt_succ_iff.mp hin)]
    simp only [zero_add, pow_add _ _ x,
      ← mul_assoc, pow_succ, ← Finset.sum_mul, smul_eq_mul] at hg
    rw [← neg_eq_iff_add_eq_zero]; rw [← neg_mul]; rw [← neg_mul] at hg
    have := mul_right_cancel₀ (mem_nonZeroDivisors_iff_ne_zero.mp (s ^ x).prop) hg
    exact (h _ ⟨(g 0), mem_nonZeroDivisors_iff_ne_zero.mpr (by simpa)⟩ this.symm).elim

Depends on / 依赖: Cardinal, Cardinal.aleph0_le.mpr, Finset, Finset.range, Fintype, Fintype.linearIndependent_iff.mpr, LinearIndependent, OreLocalization, OreLocalization.nonempty_oreSet_iff_of_noZeroDivisors, aleph0_le, cardinal_lift_le_rank, dif_pos, i.prop, linearIndependent_iff, nonempty_oreSet_iff_of_noZeroDivisors, not_nonempty_iff, this.cardinal_lift_le_rank
-/
lemma aleph0_le_rank_of_isEmpty_oreSet (hS : IsEmpty (OreLocalization.OreSet R⁰)) :
    ℵ₀ <= Module.rank R R := by
  rw [← not_nonempty_iff]; rw [OreLocalization.nonempty_oreSet_iff_of_noZeroDivisors] at hS
  push Not at hS
  obtain ⟨r, s, h⟩ := hS
  refine Cardinal.aleph0_le.mpr fun n => ?_
  suffices LinearIndependent R (fun (i : Fin n) => r * s ^ (i : Nat)) by
    simpa using this.cardinal_lift_le_rank
  suffices forall (g : Nat -> R) (x), (∑ i in Finset.range n, g i • (r * s ^ (i + x))) = 0 ->
      forall i < n, g i = 0 by
    refine Fintype.linearIndependent_iff.mpr fun g hg i => ?_
    simpa only [dif_pos i.prop] using this (fun i => if h : i < n then g ⟨i, h⟩ else 0) 0
      (by simp [← Fin.sum_univ_eq_sum_range, ← hg]) i i.prop
  intro g x hg i hin
  induction n generalizing g x i with
  | zero => contradiction
  | succ n IH =>
    rw [Finset.sum_range_succ'] at hg
    by_cases hg0 : g 0 = 0
    · simp only [hg0, zero_smul, add_zero, add_assoc] at hg
      cases i; exacts [hg0, IH _ _ hg _ (Nat.succ_lt_succ_iff.mp hin)]
    simp only [zero_add, pow_add _ _ x,
      ← mul_assoc, pow_succ, ← Finset.sum_mul, smul_eq_mul] at hg
    rw [← neg_eq_iff_add_eq_zero]; rw [← neg_mul]; rw [← neg_mul] at hg
    have := mul_right_cancel₀ (mem_nonZeroDivisors_iff_ne_zero.mp (s ^ x).prop) hg
    exact (h _ ⟨(g 0), mem_nonZeroDivisors_iff_ne_zero.mpr (by simpa)⟩ this.symm).elim

-- TODO: Upgrade this to an iff. See [lam_1999] Exercise 10.21
/--
lemma `nonempty_oreSet_of_strongRankCondition` / 引理 `nonempty_oreSet_of_strongRankCondition`

English:
lemma nonempty_oreSet_of_strongRankCondition
  given: [StrongRankCondition R]
  proof: by
  by_contra! h
  have := aleph0_le_rank_of_isEmpty_oreSet h
  rw [rank_self] at this
  exact this.not_gt one_lt_aleph0

中文:
引理 nonempty_oreSet_of_strongRankCondition
  条件: [StrongRankCondition R]
  证明: by
  by_contra! h
  have := aleph0_le_rank_of_isEmpty_oreSet h
  rw [rank_self] at this
  exact this.not_gt one_lt_aleph0

Depends on / 依赖: aleph0_le_rank_of_isEmpty_oreSet, not_gt, one_lt_aleph0, rank_self, this.not_gt
-/
lemma nonempty_oreSet_of_strongRankCondition [StrongRankCondition R] :
    Nonempty (OreLocalization.OreSet R⁰) := by
  by_contra! h
  have := aleph0_le_rank_of_isEmpty_oreSet h
  rw [rank_self] at this
  exact this.not_gt one_lt_aleph0

end Ring
