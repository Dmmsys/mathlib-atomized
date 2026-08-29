/-
Copyright (c) 2024 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.GroupTheory.Abelianization.Finite
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.SchurZassenhaus
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# Z-Groups

A Z-group is a group whose Sylow subgroups are all cyclic.

## Main definitions

* `IsZGroup G`: a predicate stating that all Sylow subgroups of `G` are cyclic.

## Main results

* `IsZGroup.isCyclic_abelianization`: a finite Z-group has cyclic abelianization.
* `IsZGroup.isCyclic_commutator`: a finite Z-group has cyclic commutator subgroup.
* `IsZGroup.coprime_commutator_index`: the commutator subgroup of a finite Z-group is a
  Hall-subgroup (the commutator subgroup has cardinality coprime to its index).
* `isZGroup_iff_exists_mulEquiv`: a finite group `G` is a Z-group if and only if `G` is isomorphic
  to a semidirect product of two cyclic subgroups of coprime order.

-/

public section

variable (G G' G'' : Type*) [Group G] [Group G'] [Group G''] (f : G ->* G') (f' : G' ->* G'')

/--
Definition of `IsZGroup` / `IsZGroup` 的定义

English:
class IsZGroup
  parameters: : Prop where
  axioms and operations (1):
    - isZGroup : forall p : Nat, p.Prime -> forall P : Sylow p G, IsCyclic P

中文:
类 IsZGroup
  参数: : 命题 where
  公理与运算 (1 个):
    - isZGroup : 对任意 p : 自然数, p.Prime -> 对任意 P : Sylow p G, IsCyclic P
-/
@[mk_iff] class IsZGroup : Prop where
  isZGroup : forall p : Nat, p.Prime -> forall P : Sylow p G, IsCyclic P

variable {G G' G'' f f'}

namespace IsZGroup

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsCyclic
  signature: G] : IsZGroup G
  body: ⟨inferInstance⟩

中文:
实例 [IsCyclic
  签名: G] : IsZGroup G
  定义体: ⟨inferInstance⟩
-/
instance [IsCyclic G] : IsZGroup G :=
  ⟨inferInstance⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsZGroup
  signature: G] {p
  body: isZGroup p Fact.out P

中文:
实例 [IsZGroup
  签名: G] {p
  定义体: isZGroup p Fact.out P

Depends on / 依赖: Fact.out, isZGroup
-/
instance [IsZGroup G] {p : Nat} [Fact p.Prime] (P : Sylow p G) : IsCyclic P :=
  isZGroup p Fact.out P

/--
theorem `_root_.IsPGroup.isCyclic_of_isZGroup` / 定理 `_root_.IsPGroup.isCyclic_of_isZGroup`

English:
theorem _root_.IsPGroup.isCyclic_of_isZGroup
  statement: [IsZGroup G] {p : Nat} [Fact p.Prime]
  proof: by
  obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
  exact Subgroup.isCyclic_of_le hQ

中文:
定理 _root_.IsPGroup.isCyclic_of_isZGroup
  结论: [IsZGroup G] {p : 自然数} [Fact p.Prime]
  证明: by
  obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
  exact Subgroup.isCyclic_of_le hQ

Depends on / 依赖: Subgroup, Subgroup.isCyclic_of_le, exists_le_sylow, hP.exists_le_sylow, isCyclic_of_le
-/
theorem _root_.IsPGroup.isCyclic_of_isZGroup [IsZGroup G] {p : Nat} [Fact p.Prime]
    {P : Subgroup G} (hP : IsPGroup p P) : IsCyclic P := by
  obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
  exact Subgroup.isCyclic_of_le hQ

/--
theorem `of_squarefree` / 定理 `of_squarefree`

English:
theorem of_squarefree
  given: (hG : Squarefree (Nat.card G))
  statement: IsZGroup G
  proof: by
  have : Finite G := Nat.finite_of_card_ne_zero hG.ne_zero
  refine ⟨fun p hp P => ?_⟩
  have := Fact.mk hp
  obtain ⟨k, hk⟩ := P.2.exists_card_eq
  exact isCyclic_of_card_dvd_prime ((hk ▸ hG.pow_dvd_of_pow_dvd) P.card_subgroup_dvd_card)

中文:
定理 of_squarefree
  条件: (hG : Squarefree (自然数.card G))
  结论: IsZGroup G
  证明: by
  have : Finite G := Nat.finite_of_card_ne_zero hG.ne_zero
  refine ⟨fun p hp P => ?_⟩
  have := Fact.mk hp
  obtain ⟨k, hk⟩ := P.2.exists_card_eq
  exact isCyclic_of_card_dvd_prime ((hk ▸ hG.pow_dvd_of_pow_dvd) P.card_subgroup_dvd_card)

Depends on / 依赖: Fact.mk, Finite, Nat.finite_of_card_ne_zero, P.card_subgroup_dvd_card, card_subgroup_dvd_card, exists_card_eq, finite_of_card_ne_zero, hG.ne_zero, hG.pow_dvd_of_pow_dvd, isCyclic_of_card_dvd_prime, ne_zero, pow_dvd_of_pow_dvd
-/
theorem of_squarefree (hG : Squarefree (Nat.card G)) : IsZGroup G := by
  have : Finite G := Nat.finite_of_card_ne_zero hG.ne_zero
  refine ⟨fun p hp P => ?_⟩
  have := Fact.mk hp
  obtain ⟨k, hk⟩ := P.2.exists_card_eq
  exact isCyclic_of_card_dvd_prime ((hk ▸ hG.pow_dvd_of_pow_dvd) P.card_subgroup_dvd_card)

/--
theorem `of_injective` / 定理 `of_injective`

English:
theorem of_injective
  given: [hG' : IsZGroup G'] (hf : Function.Injective f)
  statement: IsZGroup G
  proof: by
  rw [isZGroup_iff] at hG' ⊢
  intro p hp P
  obtain ⟨Q, hQ⟩ := P.exists_comap_eq_of_injective hf
  specialize hG' p hp Q
  have h : Subgroup.map f P <= Q := hQ ▸ Subgroup.map_comap_le f ↑Q
  have := isCyclic_of_surjective _ (Subgroup.subgroupOfEquivOfLe h).surjective
  exact isCyclic_of_surjecti

中文:
定理 of_injective
  条件: [hG' : IsZGroup G'] (hf : Function.Injective f)
  结论: IsZGroup G
  证明: by
  rw [isZGroup_iff] at hG' ⊢
  intro p hp P
  obtain ⟨Q, hQ⟩ := P.exists_comap_eq_of_injective hf
  specialize hG' p hp Q
  have h : Subgroup.map f P <= Q := hQ ▸ Subgroup.map_comap_le f ↑Q
  have := isCyclic_of_surjective _ (Subgroup.subgroupOfEquivOfLe h).surjective
  exact isCyclic_of_surjecti

Depends on / 依赖: P.exists_comap_eq_of_injective, Subgroup, Subgroup.equivMapOfInjective, Subgroup.map, Subgroup.map_comap_le, Subgroup.subgroupOfEquivOfLe, equivMapOfInjective, exists_comap_eq_of_injective, isCyclic_of_surjective, isZGroup_iff, map_comap_le, specialize, subgroupOfEquivOfLe, surjective, symm.surjective
-/
theorem of_injective [hG' : IsZGroup G'] (hf : Function.Injective f) : IsZGroup G := by
  rw [isZGroup_iff] at hG' ⊢
  intro p hp P
  obtain ⟨Q, hQ⟩ := P.exists_comap_eq_of_injective hf
  specialize hG' p hp Q
  have h : Subgroup.map f P <= Q := hQ ▸ Subgroup.map_comap_le f ↑Q
  have := isCyclic_of_surjective _ (Subgroup.subgroupOfEquivOfLe h).surjective
  exact isCyclic_of_surjective _ (Subgroup.equivMapOfInjective P f hf).symm.surjective

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsZGroup
  signature: G] (H
  body: of_injective H.subtype_injective

中文:
实例 [IsZGroup
  签名: G] (H
  定义体: of_injective H.subtype_injective

Depends on / 依赖: H.subtype_injective, of_injective, subtype_injective
-/
instance [IsZGroup G] (H : Subgroup G) : IsZGroup H := of_injective H.subtype_injective

/--
theorem `of_surjective` / 定理 `of_surjective`

English:
theorem of_surjective
  given: [Finite G] [hG : IsZGroup G] (hf : Function.Surjective f)
  statement: IsZGroup G'
  proof: by
  rw [isZGroup_iff] at hG ⊢
  intro p hp P
  have := Fact.mk hp
  obtain ⟨Q, rfl⟩ := Sylow.mapSurjective_surjective hf p P
  specialize hG p hp Q
  exact isCyclic_of_surjective _ (f.subgroupMap_surjective Q)

中文:
定理 of_surjective
  条件: [Finite G] [hG : IsZGroup G] (hf : Function.Surjective f)
  结论: IsZGroup G'
  证明: by
  rw [isZGroup_iff] at hG ⊢
  intro p hp P
  have := Fact.mk hp
  obtain ⟨Q, rfl⟩ := Sylow.mapSurjective_surjective hf p P
  specialize hG p hp Q
  exact isCyclic_of_surjective _ (f.subgroupMap_surjective Q)

Depends on / 依赖: Fact.mk, Sylow.mapSurjective_surjective, f.subgroupMap_surjective, isCyclic_of_surjective, isZGroup_iff, mapSurjective_surjective, specialize, subgroupMap_surjective
-/
theorem of_surjective [Finite G] [hG : IsZGroup G] (hf : Function.Surjective f) : IsZGroup G' := by
  rw [isZGroup_iff] at hG ⊢
  intro p hp P
  have := Fact.mk hp
  obtain ⟨Q, rfl⟩ := Sylow.mapSurjective_surjective hf p P
  specialize hG p hp Q
  exact isCyclic_of_surjective _ (f.subgroupMap_surjective Q)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Finite
  signature: G] [IsZGroup G] (H
  body: of_surjective (QuotientGroup.mk'_surjective H)

中文:
实例 [Finite
  签名: G] [IsZGroup G] (H
  定义体: of_surjective (QuotientGroup.mk'_surjective H)

Depends on / 依赖: QuotientGroup, QuotientGroup.mk, _surjective, of_surjective
-/
instance [Finite G] [IsZGroup G] (H : Subgroup G) [H.Normal] : IsZGroup (G ⧸ H) :=
  of_surjective (QuotientGroup.mk'_surjective H)

section Solvable

open scoped IsMulCommutative in
variable (G) in
/--
theorem `commutator_lt` / 定理 `commutator_lt`

English:
theorem commutator_lt
  given: [Finite G] [IsZGroup G] [Nontrivial G]
  statement: commutator G < ⊤
  proof: by
  let p := (Nat.card G).minFac
  have hp : p.Prime := Nat.minFac_prime Finite.one_lt_card.ne'
  have := Fact.mk hp
  let P : Sylow p G := default
  have hP := isZGroup p hp P
  let f := MonoidHom.transferSylow P (hP.normalizer_le_centralizer rfl)
  refine lt_of_le_of_lt (Abelianization.commutator

中文:
定理 commutator_lt
  条件: [Finite G] [IsZGroup G] [Nontrivial G]
  结论: commutator G < ⊤
  证明: by
  let p := (Nat.card G).minFac
  have hp : p.Prime := Nat.minFac_prime Finite.one_lt_card.ne'
  have := Fact.mk hp
  let P : Sylow p G := default
  have hP := isZGroup p hp P
  let f := MonoidHom.transferSylow P (hP.normalizer_le_centralizer rfl)
  refine lt_of_le_of_lt (Abelianization.commutator

Depends on / 依赖: Abelianization, Abelianization.commutator_subset_ker, Fact.mk, Finite, Finite.one_lt_card.ne, MonoidHom, MonoidHom.transferSylow, Nat.card, Nat.minFac_prime, P.ne_bot_of_dvd_card, Subgroup, Subgroup.isComplement, _top_left, commutator_subset_ker, contrapose, hP.isComplement, hP.normalizer_le_centralizer, isComplement, isZGroup, lt_of_le_of_lt
-/
theorem commutator_lt [Finite G] [IsZGroup G] [Nontrivial G] : commutator G < ⊤ := by
  let p := (Nat.card G).minFac
  have hp : p.Prime := Nat.minFac_prime Finite.one_lt_card.ne'
  have := Fact.mk hp
  let P : Sylow p G := default
  have hP := isZGroup p hp P
  let f := MonoidHom.transferSylow P (hP.normalizer_le_centralizer rfl)
  refine lt_of_le_of_lt (Abelianization.commutator_subset_ker f) ?_
  have h := P.ne_bot_of_dvd_card (Nat.card G).minFac_dvd
  contrapose h
  rw [← Subgroup.isComplement'_top_left]; rw [← (not_lt_top_iff.mp h)]
  exact hP.isComplement' rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Finite
  signature: G] [IsZGroup G] : Group.IsSolvable G
  body: by
  rw [Group.isSolvable_iff_commutator_lt]
  intro H h
  rw [← H.nontrivial_iff_ne_bot] at h
  rw [← H.range_subtype]; rw [MonoidHom.range_eq_map]; rw [← Subgroup.map_commutator]; rw [Subgroup.map_subtype_lt_map_subtype]
  exact commutator_lt H

中文:
实例 [Finite
  签名: G] [IsZGroup G] : Group.IsSolvable G
  定义体: by
  rw [Group.isSolvable_iff_commutator_lt]
  intro H h
  rw [← H.nontrivial_iff_ne_bot] at h
  rw [← H.range_subtype]; rw [MonoidHom.range_eq_map]; rw [← Subgroup.map_commutator]; rw [Subgroup.map_subtype_lt_map_subtype]
  exact commutator_lt H

Depends on / 依赖: Group.isSolvable_iff_commutator_lt, H.nontrivial_iff_ne_bot, H.range_subtype, MonoidHom, MonoidHom.range_eq_map, Subgroup, Subgroup.map_commutator, Subgroup.map_subtype_lt_map_subtype, commutator_lt, isSolvable_iff_commutator_lt, map_commutator, map_subtype_lt_map_subtype, nontrivial_iff_ne_bot, range_eq_map, range_subtype
-/
instance [Finite G] [IsZGroup G] : Group.IsSolvable G := by
  rw [Group.isSolvable_iff_commutator_lt]
  intro H h
  rw [← H.nontrivial_iff_ne_bot] at h
  rw [← H.range_subtype]; rw [MonoidHom.range_eq_map]; rw [← Subgroup.map_commutator]; rw [Subgroup.map_subtype_lt_map_subtype]
  exact commutator_lt H

end Solvable

section Nilpotent

variable (G) in
/--
theorem `exponent_eq_card` / 定理 `exponent_eq_card`

English:
theorem exponent_eq_card
  given: [Finite G] [IsZGroup G]
  statement: Monoid.exponent G = Nat.card G
  proof: by
  refine dvd_antisymm Group.exponent_dvd_nat_card ?_
  rw [← Nat.factorization_prime_le_iff_dvd Nat.card_pos.ne' Monoid.exponent_ne_zero_of_finite]
  intro p hp
  have := Fact.mk hp
  let P : Sylow p G := default
  rw [← hp.pow_dvd_iff_le_factorization Monoid.exponent_ne_zero_of_finite]; rw [← P.

中文:
定理 exponent_eq_card
  条件: [Finite G] [IsZGroup G]
  结论: Monoid.exponent G = 自然数.card G
  证明: by
  refine dvd_antisymm Group.exponent_dvd_nat_card ?_
  rw [← Nat.factorization_prime_le_iff_dvd Nat.card_pos.ne' Monoid.exponent_ne_zero_of_finite]
  intro p hp
  have := Fact.mk hp
  let P : Sylow p G := default
  rw [← hp.pow_dvd_iff_le_factorization Monoid.exponent_ne_zero_of_finite]; rw [← P.

Depends on / 依赖: Fact.mk, Group.exponent_dvd_nat_card, Monoid, Monoid.exponent_dvd_of_monoidHom, Monoid.exponent_ne_zero_of_finite, Nat.card_pos.ne, Nat.factorization_prime_le_iff_dvd, P.card_eq_multiplicity, card_eq_multiplicity, card_pos, dvd_antisymm, exponent_dvd_nat_card, exponent_dvd_of_monoidHom, exponent_eq_card, exponent_ne_zero_of_finite, factorization_prime_le_iff_dvd, hp.pow_dvd_iff_le_factorization, isZGroup, pow_dvd_iff_le_factorization, subtype
-/
theorem exponent_eq_card [Finite G] [IsZGroup G] : Monoid.exponent G = Nat.card G := by
  refine dvd_antisymm Group.exponent_dvd_nat_card ?_
  rw [← Nat.factorization_prime_le_iff_dvd Nat.card_pos.ne' Monoid.exponent_ne_zero_of_finite]
  intro p hp
  have := Fact.mk hp
  let P : Sylow p G := default
  rw [← hp.pow_dvd_iff_le_factorization Monoid.exponent_ne_zero_of_finite]; rw [← P.card_eq_multiplicity]; rw [← (isZGroup p hp P).exponent_eq_card]
  exact Monoid.exponent_dvd_of_monoidHom P.1.subtype P.1.subtype_injective

open scoped IsMulCommutative in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Finite
  signature: G] [IsZGroup G] [hG
  body: by
  have (p : { x // x in (Nat.card G).primeFactors }) : Fact p.1.Prime :=
    ⟨Nat.prime_of_mem_primeFactors p.2⟩
  obtain ⟨ϕ⟩ := ((Group.isNilpotent_of_finite_tfae (G := G)).out 0 4).mp hG
  let _ : CommGroup G :=
    ⟨fun g h => by rw [← ϕ.symm.injective.eq_iff, map_mul, mul_comm, ← map_mul]⟩
  

中文:
实例 [Finite
  签名: G] [IsZGroup G] [hG
  定义体: by
  have (p : { x // x in (Nat.card G).primeFactors }) : Fact p.1.Prime :=
    ⟨Nat.prime_of_mem_primeFactors p.2⟩
  obtain ⟨ϕ⟩ := ((Group.isNilpotent_of_finite_tfae (G := G)).out 0 4).mp hG
  let _ : CommGroup G :=
    ⟨fun g h => by rw [← ϕ.symm.injective.eq_iff, map_mul, mul_comm, ← map_mul]⟩
  

Depends on / 依赖: CommGroup, Group.isNilpotent_of_finite_tfae, IsCyclic, IsCyclic.of_exponent_eq_card, Nat.card, Nat.prime_of_mem_primeFactors, eq_iff, exponent_eq_card, injective, isNilpotent_of_finite_tfae, map_mul, mul_comm, of_exponent_eq_card, primeFactors, prime_of_mem_primeFactors, symm.injective.eq_iff
-/
instance [Finite G] [IsZGroup G] [hG : Group.IsNilpotent G] : IsCyclic G := by
  have (p : { x // x in (Nat.card G).primeFactors }) : Fact p.1.Prime :=
    ⟨Nat.prime_of_mem_primeFactors p.2⟩
  obtain ⟨ϕ⟩ := ((Group.isNilpotent_of_finite_tfae (G := G)).out 0 4).mp hG
  let _ : CommGroup G :=
    ⟨fun g h => by rw [← ϕ.symm.injective.eq_iff, map_mul, mul_comm, ← map_mul]⟩
  exact IsCyclic.of_exponent_eq_card (exponent_eq_card G)

/--
Instance `isCyclic_abelianization` / 实例 `isCyclic_abelianization`

English:
instance isCyclic_abelianization
  signature: [Finite G] [IsZGroup G]
  body: let _ : IsZGroup (Abelianization G) := inferInstanceAs (IsZGroup (G ⧸ commutator G))
  inferInstance

中文:
实例 isCyclic_abelianization
  签名: [Finite G] [IsZGroup G]
  定义体: let _ : IsZGroup (Abelianization G) := inferInstanceAs (IsZGroup (G ⧸ commutator G))
  inferInstance

Depends on / 依赖: Abelianization, IsZGroup, commutator
-/
instance isCyclic_abelianization [Finite G] [IsZGroup G] : IsCyclic (Abelianization G) :=
  let _ : IsZGroup (Abelianization G) := inferInstanceAs (IsZGroup (G ⧸ commutator G))
  inferInstance

end Nilpotent

section Commutator

variable (G) in
/--
theorem `isCyclic_commutator` / 定理 `isCyclic_commutator`

English:
theorem isCyclic_commutator
  given: [Finite G] [IsZGroup G]
  statement: IsCyclic (commutator G)
  proof: by
  rw [commutator_def]
  induction (⊤ : Subgroup G) using WellFoundedLT.induction with | ind H hH
  rcases eq_or_ne H ⊥ with rfl | h
  · rw [Subgroup.commutator_bot_left]
    infer_instance
  · specialize hH ⁅H, H⁆ (Group.IsSolvable.commutator_lt_of_ne_bot h)
    replace hH : IsCyclic (⁅commutator

中文:
定理 isCyclic_commutator
  条件: [Finite G] [IsZGroup G]
  结论: IsCyclic (commutator G)
  证明: by
  rw [commutator_def]
  induction (⊤ : Subgroup G) using WellFoundedLT.induction with | ind H hH
  rcases eq_or_ne H ⊥ with rfl | h
  · rw [Subgroup.commutator_bot_left]
    infer_instance
  · specialize hH ⁅H, H⁆ (Group.IsSolvable.commutator_lt_of_ne_bot h)
    replace hH : IsCyclic (⁅commutator

Depends on / 依赖: Group.IsSolvable.commutator_lt_of_ne_bot, H.subtype_injective, IsCyclic, IsSolvable, Subgroup, Subgroup.commutator_bot_left, Subgroup.equivMapOfInjective, Subgroup.map_commutator, Subgroup.map_subtype_commutator, WellFoundedLT, WellFoundedLT.induction, commutator, commutator_bot_left, commutator_def, commutator_lt_of_ne_bot, eq_or_ne, equivMapOfInjective, infer_instance, isCyclic_of_s, map_commutator
-/
theorem isCyclic_commutator [Finite G] [IsZGroup G] : IsCyclic (commutator G) := by
  rw [commutator_def]
  induction (⊤ : Subgroup G) using WellFoundedLT.induction with | ind H hH
  rcases eq_or_ne H ⊥ with rfl | h
  · rw [Subgroup.commutator_bot_left]
    infer_instance
  · specialize hH ⁅H, H⁆ (Group.IsSolvable.commutator_lt_of_ne_bot h)
    replace hH : IsCyclic (⁅commutator H, commutator H⁆ : Subgroup H) := by
      let f := Subgroup.equivMapOfInjective ⁅commutator H, commutator H⁆ _ H.subtype_injective
      rw [Subgroup.map_commutator]; rw [Subgroup.map_subtype_commutator] at f
      exact isCyclic_of_surjective f.symm f.symm.surjective
    suffices IsCyclic (commutator H) by
      let f := Subgroup.equivMapOfInjective (commutator H) _ H.subtype_injective
      rw [Subgroup.map_subtype_commutator] at f
      exact isCyclic_of_surjective f f.surjective
    suffices h : commutator (commutator H) <= Subgroup.center (commutator H) by
      rw [← Abelianization.ker_of (commutator H)] at h
      let _ := commGroupOfCyclicCenterQuotient Abelianization.of h
      infer_instance
    suffices h : (commutator (commutator H)).map (commutator H).subtype <=
        Subgroup.centralizer (commutator H) by
      simpa [SetLike.le_def, Subgroup.mem_center_iff, Subgroup.mem_centralizer_iff] using h
    rw [Subgroup.map_subtype_commutator]; rw [Subgroup.le_centralizer_iff]
    let _ := (hH.mulAutMulEquiv _).toMonoidHom.commGroupOfInjective (hH.mulAutMulEquiv _).injective
    have h := Abelianization.commutator_subset_ker ⁅commutator H, commutator H⁆.normalizerMonoidHom
    rwa [Subgroup.normalizerMonoidHom_ker, Subgroup.normalizer_eq_top,
      ← Subgroup.map_subtype_le_map_subtype, Subgroup.map_subtype_commutator,
        Subgroup.map_subgroupOf_eq_of_le le_top] at h

end Commutator

end IsZGroup

section Hall

variable {p : Nat} [Fact p.Prime]

namespace IsPGroup

/--
theorem `smul_mul_inv_trivial_or_surjective` / 定理 `smul_mul_inv_trivial_or_surjective`

English:
theorem smul_mul_inv_trivial_or_surjective
  statement: [IsCyclic G] (hG : IsPGroup p G)
  proof: by
  by_cases hc : Nat.card G = 0
  · rw [hc, Nat.coprime_zero_left, Nat.card_eq_one_iff_unique] at hGK
    simp [← hGK.1.elim 1]
  have := Nat.finite_of_card_ne_zero hc
  let ϕ := MulDistribMulAction.toMonoidHomZModOfIsCyclic G K rfl
  have h (g : G) (k : K) (n : Int) (h : ϕ k - 1 = n) : k • g * g⁻

中文:
定理 smul_mul_inv_trivial_or_surjective
  结论: [IsCyclic G] (hG : IsPGroup p G)
  证明: by
  by_cases hc : Nat.card G = 0
  · rw [hc, Nat.coprime_zero_left, Nat.card_eq_one_iff_unique] at hGK
    simp [← hGK.1.elim 1]
  have := Nat.finite_of_card_ne_zero hc
  let ϕ := MulDistribMulAction.toMonoidHomZModOfIsCyclic G K rfl
  have h (g : G) (k : K) (n : Int) (h : ϕ k - 1 = n) : k • g * g⁻

Depends on / 依赖: Int.cast_add, Int.cast_one, MulDistribMulAction, MulDistribMulAction.toMonoidHomZModOfIsCyclic, MulDistribMulAction.toMonoidHomZModOfIsCyclic_apply, Nat.card, Nat.card_eq_one_iff_unique, Nat.coprime_zero_left, Nat.finite_of_card_ne_zero, card_eq_one_iff_unique, cast_add, cast_one, coprime_zero_left, finite_of_card_ne_zero, mul_inv_cancel_right, replace, sub_eq_iff_eq_add, toMonoidHomZModOfIsCyclic, toMonoidHomZModOfIsCyclic_apply, zpow_add_one
-/
theorem smul_mul_inv_trivial_or_surjective [IsCyclic G] (hG : IsPGroup p G)
    {K : Type*} [Group K] [MulDistribMulAction K G] (hGK : (Nat.card G).Coprime (Nat.card K)) :
    (forall g : G, forall k : K, k • g * g⁻¹ = 1) ∨ (forall g : G, exists k : K, exists q : G, k • q * q⁻¹ = g) := by
  by_cases hc : Nat.card G = 0
  · rw [hc, Nat.coprime_zero_left, Nat.card_eq_one_iff_unique] at hGK
    simp [← hGK.1.elim 1]
  have := Nat.finite_of_card_ne_zero hc
  let ϕ := MulDistribMulAction.toMonoidHomZModOfIsCyclic G K rfl
  have h (g : G) (k : K) (n : Int) (h : ϕ k - 1 = n) : k • g * g⁻¹ = g ^ n := by
    rw [sub_eq_iff_eq_add]; rw [← Int.cast_one]; rw [← Int.cast_add] at h
    rw [MulDistribMulAction.toMonoidHomZModOfIsCyclic_apply rfl k g (n + 1) h]; rw [zpow_add_one]; rw [mul_inv_cancel_right]
  replace hG k : ϕ k = 1 ∨ IsUnit (ϕ k - 1) := by
    obtain ⟨n, hn⟩ := hG.exists_card_eq
    exact ZMod.eq_one_or_isUnit_sub_one hn (ϕ k)
      (hGK.symm.coprime_dvd_left ((orderOf_map_dvd ϕ k).trans (orderOf_dvd_natCard k)))
  rcases forall_or_exists_not (fun k : K => ϕ k = 1) with hϕ | ⟨k, hk⟩
  · exact Or.inl fun p k => by rw [h p k 0 (by rw [hϕ, sub_self, Int.cast_zero]), zpow_zero]
  · obtain ⟨⟨u, v, -, hvu⟩, hu : u = ϕ k - 1⟩ := (hG k).resolve_left hk
    rw [← u.intCast_zmod_cast] at hu hvu
    rw [← v.intCast_zmod_cast]; rw [← Int.cast_mul]; rw [← Int.cast_one]; rw [ZMod.intCast_eq_intCast_iff] at hvu
    refine Or.inr fun p => zpow_one p ▸ ⟨k, p ^ (v.cast : Int), ?_⟩
    rw [h (p ^ v.cast) k u.cast hu.symm]; rw [← zpow_mul]; rw [zpow_eq_zpow_iff_modEq]
    exact hvu.of_dvd (Int.natCast_dvd_natCast.mpr (orderOf_dvd_natCard p))

/--
theorem `commutator_eq_bot_or_commutator_eq_self` / 定理 `commutator_eq_bot_or_commutator_eq_self`

English:
theorem commutator_eq_bot_or_commutator_eq_self
  statement: {P K : Subgroup G} [IsCyclic P]
  proof: by
  let _ := MulDistribMulAction.compHom P (P.normalizerMonoidHom.comp (Subgroup.inclusion hKP))
  refine (smul_mul_inv_trivial_or_surjective hP hPK).imp (fun h => ?_) fun h => ?_
  · rw [eq_bot_iff, Subgroup.commutator_le]
    exact fun k hk g hg => Subtype.ext_iff.mp (h ⟨g, hg⟩ ⟨k, hk⟩)
  · rw [l

中文:
定理 commutator_eq_bot_or_commutator_eq_self
  结论: {P K : Subgroup G} [IsCyclic P]
  证明: by
  let _ := MulDistribMulAction.compHom P (P.normalizerMonoidHom.comp (Subgroup.inclusion hKP))
  refine (smul_mul_inv_trivial_or_surjective hP hPK).imp (fun h => ?_) fun h => ?_
  · rw [eq_bot_iff, Subgroup.commutator_le]
    exact fun k hk g hg => Subtype.ext_iff.mp (h ⟨g, hg⟩ ⟨k, hk⟩)
  · rw [l

Depends on / 依赖: MulDistribMulAction, MulDistribMulAction.compHom, P.inv_mem, P.mul_mem, P.normalizerMonoidHom.comp, Subgroup, Subgroup.commutator_le, Subgroup.inclusion, Subtype, Subtype.coe_mk, Subtype.ext_iff.mp, coe_mk, commutator_le, compHom, eq_bot_iff, ext_iff, inclusion, inv_mem, le_antisymm_iff, mul_mem
-/
theorem commutator_eq_bot_or_commutator_eq_self {P K : Subgroup G} [IsCyclic P]
    (hP : IsPGroup p P) (hKP : K <= Subgroup.normalizer P)
    (hPK : (Nat.card P).Coprime (Nat.card K)) : ⁅K, P⁆ = ⊥ ∨ ⁅K, P⁆ = P := by
  let _ := MulDistribMulAction.compHom P (P.normalizerMonoidHom.comp (Subgroup.inclusion hKP))
  refine (smul_mul_inv_trivial_or_surjective hP hPK).imp (fun h => ?_) fun h => ?_
  · rw [eq_bot_iff, Subgroup.commutator_le]
    exact fun k hk g hg => Subtype.ext_iff.mp (h ⟨g, hg⟩ ⟨k, hk⟩)
  · rw [le_antisymm_iff, Subgroup.commutator_le]
    refine ⟨fun k hk g hg => P.mul_mem ((hKP hk g).mp hg) (P.inv_mem hg), fun g hg => ?_⟩
    obtain ⟨k, q, hkq⟩ := h ⟨g, hg⟩
    rw [← Subtype.coe_mk g hg]; rw [← hkq]
    exact Subgroup.commutator_mem_commutator k.2 q.2

end IsPGroup

namespace Sylow

variable [Finite G] (P : Sylow p G) [IsCyclic P]

/--
theorem `commutator_eq_bot_or_commutator_eq_self` / 定理 `commutator_eq_bot_or_commutator_eq_self`

English:
theorem commutator_eq_bot_or_commutator_eq_self
  statement: [P.Normal] {K : Subgroup G}
  proof: P.2.commutator_eq_bot_or_commutator_eq_self (P.normalizer_eq_top ▸ le_top)
    (h.index_eq_card ▸ P.card_coprime_index)

中文:
定理 commutator_eq_bot_or_commutator_eq_self
  结论: [P.Normal] {K : Subgroup G}
  证明: P.2.commutator_eq_bot_or_commutator_eq_self (P.normalizer_eq_top ▸ le_top)
    (h.index_eq_card ▸ P.card_coprime_index)

Depends on / 依赖: P.card_coprime_index, P.normalizer_eq_top, card_coprime_index, commutator_eq_bot_or_commutator_eq_self, h.index_eq_card, index_eq_card, le_top, normalizer_eq_top
-/
theorem commutator_eq_bot_or_commutator_eq_self [P.Normal] {K : Subgroup G}
    (h : K.IsComplement' P) : ⁅K, P.1⁆ = ⊥ ∨ ⁅K, P.1⁆ = P :=
  P.2.commutator_eq_bot_or_commutator_eq_self (P.normalizer_eq_top ▸ le_top)
    (h.index_eq_card ▸ P.card_coprime_index)

/--
theorem `le_center_or_le_commutator` / 定理 `le_center_or_le_commutator`

English:
theorem le_center_or_le_commutator
  given: [P.Normal]
  statement: P <= Subgroup.center G ∨ P <= commutator G
  proof: by
  obtain ⟨K, hK⟩ := Subgroup.exists_left_complement'_of_coprime P.card_coprime_index
  refine (commutator_eq_bot_or_commutator_eq_self P hK).imp (fun h => ?_) (fun h => ?_)
  · replace h := sup_le (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h) P.le_centralizer
    rwa [hK.sup_eq_top, top_le

中文:
定理 le_center_or_le_commutator
  条件: [P.Normal]
  结论: P <= Subgroup.center G ∨ P <= commutator G
  证明: by
  obtain ⟨K, hK⟩ := Subgroup.exists_left_complement'_of_coprime P.card_coprime_index
  refine (commutator_eq_bot_or_commutator_eq_self P hK).imp (fun h => ?_) (fun h => ?_)
  · replace h := sup_le (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h) P.le_centralizer
    rwa [hK.sup_eq_top, top_le

Depends on / 依赖: P.card_coprime_index, P.le_centralizer, Subgroup, Subgroup.centralizer_eq_top_iff_subset, Subgroup.commutator_eq_bot_iff_le_centralizer.mp, Subgroup.commutator_mono, Subgroup.exists_left_complement, _of_coprime, card_coprime_index, centralizer_eq_top_iff_subset, commutator_def, commutator_eq_bot_iff_le_centralizer, commutator_eq_bot_or_commutator_eq_self, commutator_mono, exists_left_complement, hK.sup_eq_top, le_centralizer, le_top, replace, sup_eq_top
-/
theorem le_center_or_le_commutator [P.Normal] : P <= Subgroup.center G ∨ P <= commutator G := by
  obtain ⟨K, hK⟩ := Subgroup.exists_left_complement'_of_coprime P.card_coprime_index
  refine (commutator_eq_bot_or_commutator_eq_self P hK).imp (fun h => ?_) (fun h => ?_)
  · replace h := sup_le (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h) P.le_centralizer
    rwa [hK.sup_eq_top, top_le_iff, Subgroup.centralizer_eq_top_iff_subset] at h
  · rw [← h, commutator_def]
    exact Subgroup.commutator_mono le_top le_top

/--
theorem `normalizer_le_centralizer_or_le_commutator` / 定理 `normalizer_le_centralizer_or_le_commutator`

English:
theorem normalizer_le_centralizer_or_le_commutator
  proof: by
  let Q : Sylow p (Subgroup.normalizer P) := P.subtype P.le_normalizer
  have : Q.Normal := P.normal_in_normalizer
  have : IsCyclic Q :=
    isCyclic_of_surjective _ (Subgroup.subgroupOfEquivOfLe P.le_normalizer).symm.surjective
  refine (le_center_or_le_commutator Q).imp (fun h => ?_) (fun h =>

中文:
定理 normalizer_le_centralizer_or_le_commutator
  证明: by
  let Q : Sylow p (Subgroup.normalizer P) := P.subtype P.le_normalizer
  have : Q.Normal := P.normal_in_normalizer
  have : IsCyclic Q :=
    isCyclic_of_surjective _ (Subgroup.subgroupOfEquivOfLe P.le_normalizer).symm.surjective
  refine (le_center_or_le_commutator Q).imp (fun h => ?_) (fun h =>

Depends on / 依赖: IsCyclic, MonoidHom, MonoidHom.range_eq_map, Normal, P.le_normalizer, P.normal_in_normalizer, P.subtype, Q.Normal, SetLike, SetLike.coe_subset_coe, Subgroup, Subgroup.centralizer_eq_top_iff_subset, Subgroup.map_subtype_le_map_subtype, Subgroup.normalizer, Subgroup.subgroupOfEquivOfLe, centralizer_eq_top_iff_subset, coe_subset_coe, eq_top_iff, infer_instance, isCyclic_of_surjective
-/
theorem normalizer_le_centralizer_or_le_commutator :
    Subgroup.normalizer P <= Subgroup.centralizer (P : Set G) ∨ P <= commutator G := by
  let Q : Sylow p (Subgroup.normalizer P) := P.subtype P.le_normalizer
  have : Q.Normal := P.normal_in_normalizer
  have : IsCyclic Q :=
    isCyclic_of_surjective _ (Subgroup.subgroupOfEquivOfLe P.le_normalizer).symm.surjective
  refine (le_center_or_le_commutator Q).imp (fun h => ?_) (fun h => ?_)
  · rw [← SetLike.coe_subset_coe, ← Subgroup.centralizer_eq_top_iff_subset, eq_top_iff,
      ← Subgroup.map_subtype_le_map_subtype, ← MonoidHom.range_eq_map,
      (Subgroup.normalizer (P : Set G)).range_subtype] at h
    replace h := h.trans (Subgroup.map_centralizer_le_centralizer_image _ _)
    rwa [← Subgroup.coe_map, P.coe_subtype, ← P.coe_coe,
      Subgroup.map_subgroupOf_eq_of_le P.le_normalizer] at h
  · rw [P.coe_subtype, ← Subgroup.map_subtype_le_map_subtype, ← P.coe_coe,
      Subgroup.map_subgroupOf_eq_of_le P.le_normalizer, Subgroup.map_subtype_commutator] at h
    exact h.trans (Subgroup.commutator_mono le_top le_top)

open scoped IsMulCommutative in
include P in
/--
theorem `not_dvd_card_commutator_or_not_dvd_index_commutator` / 定理 `not_dvd_card_commutator_or_not_dvd_index_commutator`

English:
theorem not_dvd_card_commutator_or_not_dvd_index_commutator
  proof: by
  refine (normalizer_le_centralizer_or_le_commutator P).imp ?_ ?_ <;>
      refine fun hP h => P.not_dvd_index (h.trans ?_)
  · rw [(MonoidHom.ker_transferSylow_isComplement' P hP).index_eq_card]
    exact Subgroup.card_dvd_of_le (Abelianization.commutator_subset_ker _)
  · exact Subgroup.index_d

中文:
定理 not_dvd_card_commutator_or_not_dvd_index_commutator
  证明: by
  refine (normalizer_le_centralizer_or_le_commutator P).imp ?_ ?_ <;>
      refine fun hP h => P.not_dvd_index (h.trans ?_)
  · rw [(MonoidHom.ker_transferSylow_isComplement' P hP).index_eq_card]
    exact Subgroup.card_dvd_of_le (Abelianization.commutator_subset_ker _)
  · exact Subgroup.index_d

Depends on / 依赖: Abelianization, Abelianization.commutator_subset_ker, MonoidHom, MonoidHom.ker_transferSylow_isComplement, P.not_dvd_index, Subgroup, Subgroup.card_dvd_of_le, Subgroup.index_dvd_of_le, card_dvd_of_le, commutator_subset_ker, h.trans, index_dvd_of_le, index_eq_card, ker_transferSylow_isComplement, normalizer_le_centralizer_or_le_commutator, not_dvd_index
-/
theorem not_dvd_card_commutator_or_not_dvd_index_commutator :
    ¬ p ∣ Nat.card (commutator G) ∨ ¬ p ∣ (commutator G).index := by
  refine (normalizer_le_centralizer_or_le_commutator P).imp ?_ ?_ <;>
      refine fun hP h => P.not_dvd_index (h.trans ?_)
  · rw [(MonoidHom.ker_transferSylow_isComplement' P hP).index_eq_card]
    exact Subgroup.card_dvd_of_le (Abelianization.commutator_subset_ker _)
  · exact Subgroup.index_dvd_of_le hP

end Sylow

variable (G) in
/--
theorem `IsZGroup.coprime_commutator_index` / 定理 `IsZGroup.coprime_commutator_index`

English:
theorem IsZGroup.coprime_commutator_index
  given: [Finite G] [IsZGroup G]
  proof: by
  suffices h : forall p, p.Prime -> (¬ p ∣ Nat.card (commutator G) ∨ ¬ p ∣ (commutator G).index) by
    contrapose! h
    exact Nat.Prime.not_coprime_iff_dvd.mp h
  intro p hp
  have := Fact.mk hp
  exact Sylow.not_dvd_card_commutator_or_not_dvd_index_commutator default

中文:
定理 IsZGroup.coprime_commutator_index
  条件: [Finite G] [IsZGroup G]
  证明: by
  suffices h : forall p, p.Prime -> (¬ p ∣ Nat.card (commutator G) ∨ ¬ p ∣ (commutator G).index) by
    contrapose! h
    exact Nat.Prime.not_coprime_iff_dvd.mp h
  intro p hp
  have := Fact.mk hp
  exact Sylow.not_dvd_card_commutator_or_not_dvd_index_commutator default

Depends on / 依赖: Encodable, Encodable.decidableEqOfEncodable, Fact.mk, Nat.Prime.not_coprime_iff_dvd.mp, Nat.card, Sylow.not_dvd_card_commutator_or_not_dvd_index_commutator, ULower, commutator, contrapose, decidableEqOfEncodable, not_coprime_iff_dvd, not_dvd_card_commutator_or_not_dvd_index_commutator, p.Prime
-/
theorem IsZGroup.coprime_commutator_index [Finite G] [IsZGroup G] :
    (Nat.card (commutator G)).Coprime (commutator G).index := by
  suffices h : forall p, p.Prime -> (¬ p ∣ Nat.card (commutator G) ∨ ¬ p ∣ (commutator G).index) by
    contrapose! h
    exact Nat.Prime.not_coprime_iff_dvd.mp h
  intro p hp
  have := Fact.mk hp
  exact Sylow.not_dvd_card_commutator_or_not_dvd_index_commutator default

end Hall

section Classification

/--
theorem `isZGroup_of_coprime` / 定理 `isZGroup_of_coprime`

English:
theorem isZGroup_of_coprime
  statement: [Finite G] [IsZGroup G] [IsZGroup G'']
  proof: by
  refine ⟨fun p hp P => ?_⟩
  have := Fact.mk hp
  replace h_cop := (h_cop.of_dvd ((Subgroup.card_dvd_of_le h_le).trans
    (Subgroup.card_range_dvd f)) (Subgroup.index_ker f' ▸ f'.range.card_subgroup_dvd_card))
  rcases P.2.le_or_disjoint_of_coprime h_cop with h | h
  · replace h_le : P <= f.ran

中文:
定理 isZGroup_of_coprime
  结论: [Finite G] [IsZGroup G] [IsZGroup G'']
  证明: by
  refine ⟨fun p hp P => ?_⟩
  have := Fact.mk hp
  replace h_cop := (h_cop.of_dvd ((Subgroup.card_dvd_of_le h_le).trans
    (Subgroup.card_range_dvd f)) (Subgroup.index_ker f' ▸ f'.range.card_subgroup_dvd_card))
  rcases P.2.le_or_disjoint_of_coprime h_cop with h | h
  · replace h_le : P <= f.ran

Depends on / 依赖: Fact.mk, IsCyclic, P.subgroupOf, Subgroup, Subgroup.card_dvd_of_le, Subgroup.card_range_dvd, Subgroup.index_ker, Subgroup.subgroupOfEquivOfLe, Sylow.mapSurjective_surjective, ULower, card_dvd_of_le, card_range_dvd, card_subgroup_dvd_card, f.range, f.rangeR, h.trans, h_cop, h_cop.of_dvd, h_le, index_ker
-/
theorem isZGroup_of_coprime [Finite G] [IsZGroup G] [IsZGroup G'']
    (h_le : f'.ker <= f.range) (h_cop : (Nat.card G).Coprime (Nat.card G'')) :
    IsZGroup G' := by
  refine ⟨fun p hp P => ?_⟩
  have := Fact.mk hp
  replace h_cop := (h_cop.of_dvd ((Subgroup.card_dvd_of_le h_le).trans
    (Subgroup.card_range_dvd f)) (Subgroup.index_ker f' ▸ f'.range.card_subgroup_dvd_card))
  rcases P.2.le_or_disjoint_of_coprime h_cop with h | h
  · replace h_le : P <= f.range := h.trans h_le
    suffices IsCyclic (P.subgroupOf f.range) by
      have key := Subgroup.subgroupOfEquivOfLe h_le
      exact isCyclic_of_surjective key key.surjective
    obtain ⟨Q, hQ⟩ := Sylow.mapSurjective_surjective f.rangeRestrict_surjective p (P.subtype h_le)
    rw [Sylow.ext_iff]; rw [Sylow.coe_mapSurjective]; rw [Sylow.coe_subtype] at hQ
    exact hQ ▸ isCyclic_of_surjective _ (f.rangeRestrict.subgroupMap_surjective Q)
  · have := (P.2.map f').isCyclic_of_isZGroup
    apply isCyclic_of_injective (f'.subgroupMap P)
    rwa [← MonoidHom.ker_eq_bot_iff, P.ker_subgroupMap f', Subgroup.subgroupOf_eq_bot]

/--
theorem `isZGroup_iff_exists_mulEquiv` / 定理 `isZGroup_iff_exists_mulEquiv`

English:
theorem isZGroup_iff_exists_mulEquiv
  given: [Finite G]
  proof: by
  refine ⟨fun hG => ?_, ?_⟩
  · obtain ⟨H, hH⟩ := Subgroup.exists_right_complement'_of_coprime hG.coprime_commutator_index
    have h1 : Abelianization G ≃* H := hH.symm.QuotientMulEquiv
    refine ⟨commutator G, H, _, (SemidirectProduct.mulEquivSubgroup hH).symm,
      isCyclic_of_surjective _ h

中文:
定理 isZGroup_iff_exists_mulEquiv
  条件: [Finite G]
  证明: by
  refine ⟨fun hG => ?_, ?_⟩
  · obtain ⟨H, hH⟩ := Subgroup.exists_right_complement'_of_coprime hG.coprime_commutator_index
    have h1 : Abelianization G ≃* H := hH.symm.QuotientMulEquiv
    refine ⟨commutator G, H, _, (SemidirectProduct.mulEquivSubgroup hH).symm,
      isCyclic_of_surjective _ h

Depends on / 依赖: Abelianization, IsZGroup, Nat.card_congr, QuotientMulEquiv, SemidirectProduct, SemidirectProduct.mulEquivSubgroup, SemidirectProduct.range_inl_e, Subgroup, Subgroup.exists_right_complement, _of_coprime, card_congr, commutator, coprime_commutator_index, exists_right_complement, h1.surjective, h1.toEquiv, hG.coprime_commutator_index, hG.isCyclic_commutator, hH.symm.QuotientMulEquiv, isCyclic_commutator
-/
theorem isZGroup_iff_exists_mulEquiv [Finite G] :
    IsZGroup G ↔ exists (N H : Subgroup G) (φ : H ->* MulAut N) (_ : G ≃* N ⋊[φ] H),
      IsCyclic H ∧ IsCyclic N ∧ (Nat.card N).Coprime (Nat.card H) := by
  refine ⟨fun hG => ?_, ?_⟩
  · obtain ⟨H, hH⟩ := Subgroup.exists_right_complement'_of_coprime hG.coprime_commutator_index
    have h1 : Abelianization G ≃* H := hH.symm.QuotientMulEquiv
    refine ⟨commutator G, H, _, (SemidirectProduct.mulEquivSubgroup hH).symm,
      isCyclic_of_surjective _ h1.surjective, hG.isCyclic_commutator, ?_⟩
    exact Nat.card_congr h1.toEquiv ▸ hG.coprime_commutator_index
  · rintro ⟨N, H, φ, e, hH, hN, hHN⟩
    have : IsZGroup (N ⋊[φ] H) :=
      isZGroup_of_coprime SemidirectProduct.range_inl_eq_ker_rightHom.ge hHN
    exact IsZGroup.of_injective (f := e.toMonoidHom) e.injective

end Classification
