/-
Copyright (c) 2025 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.IsGaloisGroup.Basic

/-!
# Galois Groups of Fields

Given an action of a group `G` on an extension of fields `L/K`, the predicate `IsGaloisGroup G K L`
states that `G` acts faithfully on `L` with fixed field `K`. In particular, we do not assume that
`L` is an algebraic extension of `K`.

## Implementation notes

We actually define `IsGaloisGroup G A B` for extensions of rings `B/A`, with the same definition
(faithful action on `B` with fixed ring `A`). This definition turns out to axiomatize a common
setup in algebraic number theory where a Galois group `Gal(L/K)` acts on an extension of subrings
`B/A` (e.g., rings of integers). In particular, there are theorems in algebraic number theory that
naturally assume `[IsGaloisGroup G A B]` and whose statements would otherwise require assuming
`(K L : Type*) [Field K] [Field L] [Algebra K L] [IsGalois K L]` (along with predicates relating
`K` and `L` to the rings `A` and `B`) despite `K` and `L` not appearing in the conclusion.

Unfortunately, this definition of `IsGaloisGroup G A B` for extensions of rings `B/A` is
nonstandard and clashes with other notions such as the étale fundamental group. In particular, if
`G` is finite and `A` is integrally closed, then `IsGaloisGroup G A B` is equivalent to `B/A`
being integral and the fields of fractions `Frac(B)/Frac(A)` being Galois with Galois group `G`
(see `IsGaloisGroup.iff_isFractionRing`), rather than `B/A` being étale for instance.

But in the absence of a more suitable name, the utility of the predicate `IsGaloisGroup G A B` for
extensions of rings `B/A` seems to outweigh these terminological issues.
-/

@[expose] public section

open Module

section Field

open NumberField

instance (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    (G : Type*) [Group G] [MulSemiringAction G L] [IsGaloisGroup G K L] :
    IsGaloisGroup G (𝓞 K) (𝓞 L) :=
  IsGaloisGroup.of_isFractionRing G (𝓞 K) (𝓞 L) K L

instance (L : Type*) [Field L] [NumberField L]
    (G : Type*) [Group G] [MulSemiringAction G L] [IsGaloisGroup G Rat L] :
    IsGaloisGroup G Int (𝓞 L) :=
  IsGaloisGroup.of_isFractionRing G Int (𝓞 L) Rat L

end Field

variable (G G' K L : Type*) [Group G] [Group G'] [Field K] [Field L] [Algebra K L]
  [MulSemiringAction G L] [MulSemiringAction G' L]

namespace IsGaloisGroup

attribute [instance low] commutes isInvariant

/--
theorem `fixedPoints_eq_bot` / 定理 `fixedPoints_eq_bot`

English:
theorem fixedPoints_eq_bot
  given: [IsGaloisGroup G K L]
  proof: by
  rw [eq_bot_iff]
  exact Algebra.IsInvariant.isInvariant

中文:
定理 fixedPoints_eq_bot
  条件: [是Galois群 G K L]
  证明: by
  rw [eq_bot_iff]
  exact Algebra.IsInvariant.isInvariant

Depends on / 依赖: Algebra, Algebra.IsInvariant.isInvariant, IsInvariant, eq_bot_iff, isInvariant
-/
theorem fixedPoints_eq_bot [IsGaloisGroup G K L] :
    FixedPoints.intermediateField G = (⊥ : IntermediateField K L) := by
  rw [eq_bot_iff]
  exact Algebra.IsInvariant.isInvariant

/--
theorem `isGalois` / 定理 `isGalois`

English:
theorem isGalois
  given: [Finite G] [IsGaloisGroup G K L]
  statement: IsGalois K L
  proof: by
  rw [← isGalois_iff_isGalois_bot]; rw [← fixedPoints_eq_bot G]
  exact IsGalois.of_fixed_field L G

中文:
定理 isGalois
  条件: [有限 G] [是Galois群 G K L]
  结论: 是Galois K L
  证明: by
  rw [← isGalois_iff_isGalois_bot]; rw [← fixedPoints_eq_bot G]
  exact IsGalois.of_fixed_field L G

Depends on / 依赖: IsGalois, IsGalois.of_fixed_field, fixedPoints_eq_bot, isGalois_iff_isGalois_bot, of_fixed_field
-/
theorem isGalois [Finite G] [IsGaloisGroup G K L] : IsGalois K L := by
  rw [← isGalois_iff_isGalois_bot]; rw [← fixedPoints_eq_bot G]
  exact IsGalois.of_fixed_field L G

/--
Instance `of_isGalois` / 实例 `of_isGalois`

English:
instance of_isGalois
  signature: [IsGalois K L]
  body: inferInstance
  commutes := inferInstance
  isInvariant := ⟨fun x => (InfiniteGalois.mem_bot_iff_fixed x).mpr⟩

中文:
实例 of_isGalois
  签名: [是Galois K L]
  定义体: inferInstance
  commutes := inferInstance
  isInvariant := ⟨fun x => (InfiniteGalois.mem_bot_iff_fixed x).mpr⟩
-/
instance of_isGalois [IsGalois K L] : IsGaloisGroup Gal(L/K) K L where
  faithful := inferInstance
  commutes := inferInstance
  isInvariant := ⟨fun x => (InfiniteGalois.mem_bot_iff_fixed x).mpr⟩

/--
theorem `card_eq_finrank` / 定理 `card_eq_finrank`

English:
theorem card_eq_finrank
  given: [IsGaloisGroup G K L]
  statement: Nat.card G = Module.finrank K L
  proof: by
  rcases fintypeOrInfinite G with _ | hG
  · have : FaithfulSMul G L := faithful K
    rw [← IntermediateField.finrank_bot']; rw [← fixedPoints_eq_bot G]; rw [Nat.card_eq_fintype_card]
    exact (FixedPoints.finrank_eq_card G L).symm
  · rw [Nat.card_eq_zero_of_infinite, eq_comm]
    contrapose! 

中文:
定理 card_eq_finrank
  条件: [是Galois群 G K L]
  结论: 自然数.card G = 模.finrank K L
  证明: by
  rcases fintypeOrInfinite G with _ | hG
  · have : FaithfulSMul G L := faithful K
    rw [← IntermediateField.finrank_bot']; rw [← fixedPoints_eq_bot G]; rw [Nat.card_eq_fintype_card]
    exact (FixedPoints.finrank_eq_card G L).symm
  · rw [Nat.card_eq_zero_of_infinite, eq_comm]
    contrapose! 

Depends on / 依赖: DFunLike, DFunLike.ext_if, FaithfulSMul, Finite, Finite.of_injective, FiniteDimensional, FiniteDimensional.of_finrank_pos, FixedPoints, FixedPoints.finrank_eq_card, IntermediateField, IntermediateField.finrank_bot, MulSemiringAction, MulSemiringAction.toAlgAut, Nat.card_eq_fintype_card, Nat.card_eq_zero_of_infinite, Nat.zero_lt_of_ne_zero, card_eq_fintype_card, card_eq_zero_of_infinite, contrapose, eq_comm
-/
theorem card_eq_finrank [IsGaloisGroup G K L] : Nat.card G = Module.finrank K L := by
  rcases fintypeOrInfinite G with _ | hG
  · have : FaithfulSMul G L := faithful K
    rw [← IntermediateField.finrank_bot']; rw [← fixedPoints_eq_bot G]; rw [Nat.card_eq_fintype_card]
    exact (FixedPoints.finrank_eq_card G L).symm
  · rw [Nat.card_eq_zero_of_infinite, eq_comm]
    contrapose! hG
    have : FiniteDimensional K L := FiniteDimensional.of_finrank_pos (Nat.zero_lt_of_ne_zero hG)
    exact Finite.of_injective (MulSemiringAction.toAlgAut G K L)
      (fun _ _ => (faithful K).eq_of_smul_eq_smul ∘ DFunLike.ext_iff.mp)

/--
theorem `finiteDimensional` / 定理 `finiteDimensional`

English:
theorem finiteDimensional
  given: [Finite G] [IsGaloisGroup G K L]
  statement: FiniteDimensional K L
  proof: FiniteDimensional.of_finrank_pos (card_eq_finrank G K L ▸ Nat.card_pos)

中文:
定理 finiteDimensional
  条件: [有限 G] [是Galois群 G K L]
  结论: 有限维 K L
  证明: FiniteDimensional.of_finrank_pos (card_eq_finrank G K L ▸ Nat.card_pos)

Depends on / 依赖: FiniteDimensional, FiniteDimensional.of_finrank_pos, Nat.card_pos, card_eq_finrank, card_pos, of_finrank_pos
-/
theorem finiteDimensional [Finite G] [IsGaloisGroup G K L] : FiniteDimensional K L :=
  FiniteDimensional.of_finrank_pos (card_eq_finrank G K L ▸ Nat.card_pos)

/--
theorem `finite` / 定理 `finite`

English:
theorem finite
  statement: (R B : Type*) [CommRing R] [CommRing B] [Algebra R B] [Module.Finite R B]
  proof: by
  let A : Subring B := (algebraMap R B).range
  let := FractionRing.liftAlgebra A (FractionRing B)
  let := IsFractionRing.mulSemiringAction G B (FractionRing B)
  let : Algebra R A := (algebraMap R B).rangeRestrict.toAlgebra
  have : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' rfl
  h

中文:
定理 finite
  结论: (R B : 类型) [交换环 R] [交换环 B] [代数 R B] [模.有限 R B]
  证明: by
  let A : Subring B := (algebraMap R B).range
  let := FractionRing.liftAlgebra A (FractionRing B)
  let := IsFractionRing.mulSemiringAction G B (FractionRing B)
  let : Algebra R A := (algebraMap R B).rangeRestrict.toAlgebra
  have : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' rfl
  h
-/
protected theorem finite (R B : Type*) [CommRing R] [CommRing B] [Algebra R B] [Module.Finite R B]
    [IsDomain B] [MulSemiringAction G B] [IsGaloisGroup G R B] : Finite G := by
  let A : Subring B := (algebraMap R B).range
  let := FractionRing.liftAlgebra A (FractionRing B)
  let := IsFractionRing.mulSemiringAction G B (FractionRing B)
  let : Algebra R A := (algebraMap R B).rangeRestrict.toAlgebra
  have : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' rfl
  have : Module.Finite A B := Module.Finite.of_restrictScalars_finite R A B
  have := IsGaloisGroup.to_isFractionRing_of_isIntegral G A B (FractionRing A) (FractionRing B)
  apply Nat.finite_of_card_ne_zero
  rw [card_eq_finrank G (FractionRing A) (FractionRing B)]
  exact Module.finrank_pos.ne'

section IsDomain

variable (A B : Type*) [CommRing A] [CommRing B] [IsDomain B] [Algebra A B] [FaithfulSMul A B]
  [MulSemiringAction G B] [MulSemiringAction G' B] [IsGaloisGroup G A B] [IsGaloisGroup G' A B]
  [Finite G] [Finite G']

/--
theorem `card_eq_finrank'` / 定理 `card_eq_finrank'`

English:
theorem card_eq_finrank'
  statement: Nat.card G = Module.finrank A B
  proof: by
  have := IsDomain.of_faithfulSMul A B
  let := FractionRing.liftAlgebra A (FractionRing B)
  let := IsFractionRing.mulSemiringAction G B (FractionRing B)
  rw [IsGaloisGroup.card_eq_finrank G (FractionRing A) (FractionRing B)]; rw [IsFractionRing.finrank_eq A (FractionRing A) B (FractionRing B)]

中文:
定理 card_eq_finrank'
  结论: 自然数.card G = 模.finrank A B
  证明: by
  have := IsDomain.of_faithfulSMul A B
  let := FractionRing.liftAlgebra A (FractionRing B)
  let := IsFractionRing.mulSemiringAction G B (FractionRing B)
  rw [IsGaloisGroup.card_eq_finrank G (FractionRing A) (FractionRing B)]; rw [IsFractionRing.finrank_eq A (FractionRing A) B (FractionRing B)]

Depends on / 依赖: FractionRing, FractionRing.liftAlgebra, IsDomain, IsDomain.of_faithfulSMul, IsFractionRing, IsFractionRing.finrank_eq, IsFractionRing.mulSemiringAction, IsGaloisGroup, IsGaloisGroup.card_eq_finrank, card_eq_finrank, finrank_eq, liftAlgebra, mulSemiringAction, of_faithfulSMul
-/
theorem card_eq_finrank' : Nat.card G = Module.finrank A B := by
  have := IsDomain.of_faithfulSMul A B
  let := FractionRing.liftAlgebra A (FractionRing B)
  let := IsFractionRing.mulSemiringAction G B (FractionRing B)
  rw [IsGaloisGroup.card_eq_finrank G (FractionRing A) (FractionRing B)]; rw [IsFractionRing.finrank_eq A (FractionRing A) B (FractionRing B)]

@[simp]
/--
theorem `map_mulEquivAlgEquiv_fixingSubgroup` / 定理 `map_mulEquivAlgEquiv_fixingSubgroup`

English:
theorem map_mulEquivAlgEquiv_fixingSubgroup
  given: [IsGaloisGroup G K L] (F : IntermediateField K L)
  proof: by
  ext g
  obtain ⟨g, rfl⟩ := (mulEquivAlgEquiv G K L).surjective g
  simp [mem_fixingSubgroup_iff]

中文:
定理 map_mulEquivAlgEquiv_fixingSubgroup
  条件: [是Galois群 G K L] (F : 中间域 K L)
  证明: by
  ext g
  obtain ⟨g, rfl⟩ := (mulEquivAlgEquiv G K L).surjective g
  simp [mem_fixingSubgroup_iff]

Depends on / 依赖: mem_fixingSubgroup_iff, mulEquivAlgEquiv, surjective
-/
theorem map_mulEquivAlgEquiv_fixingSubgroup [IsGaloisGroup G K L] (F : IntermediateField K L) :
    (fixingSubgroup G (F : Set L)).map (mulEquivAlgEquiv G K L) = F.fixingSubgroup := by
  ext g
  obtain ⟨g, rfl⟩ := (mulEquivAlgEquiv G K L).surjective g
  simp [mem_fixingSubgroup_iff]

/--
Definition of `mulEquivCongr` / `mulEquivCongr` 的定义

English:
definition mulEquivCongr
  signature: : G ≃* G'
  body: (mulEquivAlgEquiv G A B).trans (mulEquivAlgEquiv G' A B).symm

@[simp]

中文:
定义 mulEquivCongr
  签名: : G ≃* G'
  定义体: (mulEquivAlgEquiv G A B).trans (mulEquivAlgEquiv G' A B).symm

@[simp]

Depends on / 依赖: mulEquivAlgEquiv
-/
noncomputable def mulEquivCongr : G ≃* G' :=
  (mulEquivAlgEquiv G A B).trans (mulEquivAlgEquiv G' A B).symm

@[simp]
/--
theorem `mulEquivCongr_apply_smul` / 定理 `mulEquivCongr_apply_smul`

English:
theorem mulEquivCongr_apply_smul
  given: (g : G) (x : B)
  statement: mulEquivCongr G G' A B g • x = g • x
  proof: AlgEquiv.ext_iff.mp ((mulEquivAlgEquiv G' A B).apply_symm_apply (mulEquivAlgEquiv G A B g)) x

@[simp]

中文:
定理 mulEquivCongr_apply_smul
  条件: (g : G) (x : B)
  结论: mulEquivCongr G G' A B g • x = g • x
  证明: AlgEquiv.ext_iff.mp ((mulEquivAlgEquiv G' A B).apply_symm_apply (mulEquivAlgEquiv G A B g)) x

@[simp]

Depends on / 依赖: AlgEquiv, AlgEquiv.ext_iff.mp, apply_symm_apply, ext_iff, mulEquivAlgEquiv
-/
theorem mulEquivCongr_apply_smul (g : G) (x : B) : mulEquivCongr G G' A B g • x = g • x :=
  AlgEquiv.ext_iff.mp ((mulEquivAlgEquiv G' A B).apply_symm_apply (mulEquivAlgEquiv G A B g)) x

@[simp]
/--
theorem `mulEquivCongr_symm_apply_smul` / 定理 `mulEquivCongr_symm_apply_smul`

English:
theorem mulEquivCongr_symm_apply_smul
  given: (g : G') (x : B)
  proof: by
  rw [← mulEquivCongr_apply_smul G G' A B]; rw [MulEquiv.apply_symm_apply]

@[deprecated (since := "2026-06-19")] alias mulEquivCongr' := mulEquivCongr
@[deprecated (since := "2026-06-19")] alias mulEquivCongr'_apply_smul := mulEquivCongr_apply_smul

中文:
定理 mulEquivCongr_symm_apply_smul
  条件: (g : G') (x : B)
  证明: by
  rw [← mulEquivCongr_apply_smul G G' A B]; rw [MulEquiv.apply_symm_apply]

@[deprecated (since := "2026-06-19")] alias mulEquivCongr' := mulEquivCongr
@[deprecated (since := "2026-06-19")] alias mulEquivCongr'_apply_smul := mulEquivCongr_apply_smul

Depends on / 依赖: MulEquiv, MulEquiv.apply_symm_apply, apply_symm_apply, mulEquivCongr_apply_smul
-/
theorem mulEquivCongr_symm_apply_smul (g : G') (x : B) :
    (mulEquivCongr G G' A B).symm g • x = g • x := by
  rw [← mulEquivCongr_apply_smul G G' A B]; rw [MulEquiv.apply_symm_apply]

@[deprecated (since := "2026-06-19")] alias mulEquivCongr' := mulEquivCongr
@[deprecated (since := "2026-06-19")] alias mulEquivCongr'_apply_smul := mulEquivCongr_apply_smul

/--
theorem `mulEquivCongr_mapSubgroup_fixingSubgroup` / 定理 `mulEquivCongr_mapSubgroup_fixingSubgroup`

English:
theorem mulEquivCongr_mapSubgroup_fixingSubgroup
  given: (S : Set B)
  proof: by
  ext g
  simp [Subgroup.map_equiv_eq_comap_symm, mem_fixingSubgroup_iff]

中文:
定理 mulEquivCongr_mapSubgroup_fixingSubgroup
  条件: (S : 集合 B)
  证明: by
  ext g
  simp [Subgroup.map_equiv_eq_comap_symm, mem_fixingSubgroup_iff]

Depends on / 依赖: Subgroup, Subgroup.map_equiv_eq_comap_symm, map_equiv_eq_comap_symm, mem_fixingSubgroup_iff
-/
theorem mulEquivCongr_mapSubgroup_fixingSubgroup (S : Set B) :
    (fixingSubgroup G S).map (mulEquivCongr G G' A B) = fixingSubgroup G' S := by
  ext g
  simp [Subgroup.map_equiv_eq_comap_symm, mem_fixingSubgroup_iff]

end IsDomain

variable (H H' : Subgroup G) (F F' : IntermediateField K L)

/--
Instance `subgroup` / 实例 `subgroup`

English:
instance subgroup
  signature: [hGKL : IsGaloisGroup G K L]
  body: inferInstanceAs (IsGaloisGroup H (FixedPoints.subalgebra K L H) L)

中文:
实例 subgroup
  签名: [hGKL : 是Galois群 G K L]
  定义体: inferInstanceAs (IsGaloisGroup H (FixedPoints.subalgebra K L H) L)

Depends on / 依赖: FixedPoints, FixedPoints.subalgebra, IsGaloisGroup, subalgebra
-/
instance subgroup [hGKL : IsGaloisGroup G K L] :
    IsGaloisGroup H (FixedPoints.intermediateField H : IntermediateField K L) L :=
  inferInstanceAs (IsGaloisGroup H (FixedPoints.subalgebra K L H) L)

open IntermediateField in
/--
theorem `fixedPoints_of_isGaloisGroup` / 定理 `fixedPoints_of_isGaloisGroup`

English:
theorem fixedPoints_of_isGaloisGroup
  given: [hGKL : IsGaloisGroup G K L] [hHFL : IsGaloisGroup H F L]
  proof: by
  refine IntermediateField.ext_iff.mpr fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · obtain ⟨a, rfl⟩ := hHFL.isInvariant.isInvariant x hx
    exact a.prop
· have := congr_arg (restrictScalars K) IsGaloisGroup.fixedPoints_eq_bot H F L
    rw [restrictScalars_bot_eq_self] at this
    rwa [← this] at hx

中文:
定理 fixedPoints_of_isGaloisGroup
  条件: [hGKL : 是Galois群 G K L] [hHFL : 是Galois群 H F L]
  证明: by
  refine IntermediateField.ext_iff.mpr fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · obtain ⟨a, rfl⟩ := hHFL.isInvariant.isInvariant x hx
    exact a.prop
· have := congr_arg (restrictScalars K) IsGaloisGroup.fixedPoints_eq_bot H F L
    rw [restrictScalars_bot_eq_self] at this
    rwa [← this] at hx

Depends on / 依赖: IntermediateField, IntermediateField.ext_iff.mpr, IsGaloisGroup, IsGaloisGroup.fixedPoints_eq_bot, a.prop, congr_arg, ext_iff, fixedPoints_eq_bot, hHFL.isInvariant.isInvariant, isInvariant, restrictScalars, restrictScalars_bot_eq_self
-/
theorem fixedPoints_of_isGaloisGroup [hGKL : IsGaloisGroup G K L] [hHFL : IsGaloisGroup H F L] :
    FixedPoints.intermediateField H = F := by
  refine IntermediateField.ext_iff.mpr fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · obtain ⟨a, rfl⟩ := hHFL.isInvariant.isInvariant x hx
    exact a.prop
· have := congr_arg (restrictScalars K) IsGaloisGroup.fixedPoints_eq_bot H F L
    rw [restrictScalars_bot_eq_self] at this
    rwa [← this] at hx

/--
theorem `of_fixedPoints_eq` / 定理 `of_fixedPoints_eq`

English:
theorem of_fixedPoints_eq
  given: [hGKL : IsGaloisGroup G K L] (hF : FixedPoints.intermediateField H = F)
  proof: by
  rw [eq_comm] at hF
  convert! IsGaloisGroup.subgroup G K L H

中文:
定理 of_fixedPoints_eq
  条件: [hGKL : 是Galois群 G K L] (hF : FixedPoints.intermediateField H = F)
  证明: by
  rw [eq_comm] at hF
  convert! IsGaloisGroup.subgroup G K L H

Depends on / 依赖: IsGaloisGroup, IsGaloisGroup.subgroup, convert, eq_comm, subgroup
-/
theorem of_fixedPoints_eq [hGKL : IsGaloisGroup G K L] (hF : FixedPoints.intermediateField H = F) :
    IsGaloisGroup H F L := by
  rw [eq_comm] at hF
  convert! IsGaloisGroup.subgroup G K L H

variable {G K L H F} in
/--
theorem `subgroup_iff` / 定理 `subgroup_iff`

English:
theorem subgroup_iff
  given: [hGKL : IsGaloisGroup G K L]
  proof: ⟨fun _ => fixedPoints_of_isGaloisGroup G K L H F, fun h => of_fixedPoints_eq G K L H F h⟩

@[simp]

中文:
定理 subgroup_iff
  条件: [hGKL : 是Galois群 G K L]
  证明: ⟨fun _ => fixedPoints_of_isGaloisGroup G K L H F, fun h => of_fixedPoints_eq G K L H F h⟩

@[simp]

Depends on / 依赖: fixedPoints_of_isGaloisGroup, of_fixedPoints_eq
-/
theorem subgroup_iff [hGKL : IsGaloisGroup G K L] :
    IsGaloisGroup H F L ↔ FixedPoints.intermediateField H = F :=
  ⟨fun _ => fixedPoints_of_isGaloisGroup G K L H F, fun h => of_fixedPoints_eq G K L H F h⟩

@[simp]
/--
theorem `finrank_fixedPoints_eq_card_subgroup` / 定理 `finrank_fixedPoints_eq_card_subgroup`

English:
theorem finrank_fixedPoints_eq_card_subgroup
  given: [IsGaloisGroup G K L]
  proof: (card_eq_finrank H (FixedPoints.intermediateField H) L).symm

中文:
定理 finrank_fixedPoints_eq_card_subgroup
  条件: [是Galois群 G K L]
  证明: (card_eq_finrank H (FixedPoints.intermediateField H) L).symm

Depends on / 依赖: FixedPoints, FixedPoints.intermediateField, card_eq_finrank, intermediateField
-/
theorem finrank_fixedPoints_eq_card_subgroup [IsGaloisGroup G K L] :
    Module.finrank (FixedPoints.intermediateField H : IntermediateField K L) L = Nat.card H :=
  (card_eq_finrank H (FixedPoints.intermediateField H) L).symm

variable {G K L} in
/--
theorem `of_mulEquiv_algEquiv` / 定理 `of_mulEquiv_algEquiv`

English:
theorem of_mulEquiv_algEquiv
  given: [IsGalois K L] (e : G ≃* Gal(L/K)) (he : forall g x, e g x = g • x)
  proof: .of_mulEquiv e he

中文:
定理 of_mulEquiv_algEquiv
  条件: [是Galois K L] (e : G ≃* Gal(L/K)) (he : 对任意 g x, e g x = g • x)
  证明: .of_mulEquiv e he

Depends on / 依赖: of_mulEquiv
-/
theorem of_mulEquiv_algEquiv [IsGalois K L] (e : G ≃* Gal(L/K)) (he : forall g x, e g x = g • x) :
    IsGaloisGroup G K L := .of_mulEquiv e he

/--
Instance `fixedPoints` / 实例 `fixedPoints`

English:
instance fixedPoints
  signature: [Finite G] [FaithfulSMul G L]
  body: of_mulEquiv_algEquiv (FixedPoints.toAlgAutMulEquiv _ _) fun _ _ => rfl

中文:
实例 fixedPoints
  签名: [有限 G] [忠实标量乘法 G L]
  定义体: of_mulEquiv_algEquiv (FixedPoints.toAlgAutMulEquiv _ _) fun _ _ => rfl

Depends on / 依赖: FixedPoints, FixedPoints.toAlgAutMulEquiv, of_mulEquiv_algEquiv, toAlgAutMulEquiv
-/
instance fixedPoints [Finite G] [FaithfulSMul G L] :
    IsGaloisGroup G (FixedPoints.subfield G L) L :=
  of_mulEquiv_algEquiv (FixedPoints.toAlgAutMulEquiv _ _) fun _ _ => rfl

/--
Instance `intermediateField` / 实例 `intermediateField`

English:
instance intermediateField
  signature: [Finite G] [hGKL : IsGaloisGroup G K L]
  body: let e := ((mulEquivAlgEquiv G K L).subgroupMap (fixingSubgroup G (F : Set L))).trans
(MulEquiv.subgroupCongr (map_mulEquivAlgEquiv_fixingSubgroup ..)).trans
    IntermediateField.fixingSubgroupEquiv F
  have := hGKL.isGalois
  .of_mulEquiv_algEquiv e fun _ _ => rfl

include K in

中文:
实例 intermediateField
  签名: [有限 G] [hGKL : 是Galois群 G K L]
  定义体: let e := ((mulEquivAlgEquiv G K L).subgroupMap (fixingSubgroup G (F : Set L))).trans
(MulEquiv.subgroupCongr (map_mulEquivAlgEquiv_fixingSubgroup ..)).trans
    IntermediateField.fixingSubgroupEquiv F
  have := hGKL.isGalois
  .of_mulEquiv_algEquiv e fun _ _ => rfl

include K in

Depends on / 依赖: IntermediateField, IntermediateField.fixingSubgroupEquiv, MulEquiv, MulEquiv.subgroupCongr, fixingSubgroup, fixingSubgroupEquiv, hGKL.isGalois, isGalois, map_mulEquivAlgEquiv_fixingSubgroup, mulEquivAlgEquiv, of_mulEquiv_algEquiv, subgroupCongr, subgroupMap
-/
instance intermediateField [Finite G] [hGKL : IsGaloisGroup G K L] :
    IsGaloisGroup (fixingSubgroup G (F : Set L)) F L :=
let e := ((mulEquivAlgEquiv G K L).subgroupMap (fixingSubgroup G (F : Set L))).trans
(MulEquiv.subgroupCongr (map_mulEquivAlgEquiv_fixingSubgroup ..)).trans
    IntermediateField.fixingSubgroupEquiv F
  have := hGKL.isGalois
  .of_mulEquiv_algEquiv e fun _ _ => rfl

include K in
/--
theorem `of_isScalarTower` / 定理 `of_isScalarTower`

English:
theorem of_isScalarTower
  statement: [Finite G] [IsGaloisGroup G K L] (E : Type*) [Field E] [Algebra K E]
  proof: by
  rw [← IsScalarTower.toAlgHom_fieldRange K E L]
  refine IsGaloisGroup.of_ringEquiv _ _ _ L
    (AlgHom.equivFieldRange (IsScalarTower.toAlgHom K E L)).toRingEquiv.symm fun ⟨_, ⟨x, rfl⟩⟩ => ?_
  simp [AlgEquiv.symm_apply_eq, Subtype.ext_iff]

@[simp]

中文:
定理 of_isScalarTower
  结论: [有限 G] [是Galois群 G K L] (E : 类型) [域 E] [代数 K E]
  证明: by
  rw [← IsScalarTower.toAlgHom_fieldRange K E L]
  refine IsGaloisGroup.of_ringEquiv _ _ _ L
    (AlgHom.equivFieldRange (IsScalarTower.toAlgHom K E L)).toRingEquiv.symm fun ⟨_, ⟨x, rfl⟩⟩ => ?_
  simp [AlgEquiv.symm_apply_eq, Subtype.ext_iff]

@[simp]

Depends on / 依赖: AlgEquiv, AlgEquiv.symm_apply_eq, AlgHom, AlgHom.equivFieldRange, IsGaloisGroup, IsGaloisGroup.of_ringEquiv, IsScalarTower, IsScalarTower.toAlgHom, IsScalarTower.toAlgHom_fieldRange, Subtype, Subtype.ext_iff, equivFieldRange, ext_iff, of_ringEquiv, symm_apply_eq, toAlgHom, toAlgHom_fieldRange, toRingEquiv, toRingEquiv.symm
-/
theorem of_isScalarTower [Finite G] [IsGaloisGroup G K L] (E : Type*) [Field E] [Algebra K E]
    [Algebra E L] [IsScalarTower K E L] :
    IsGaloisGroup (fixingSubgroup G (Set.range (algebraMap E L))) E L := by
  rw [← IsScalarTower.toAlgHom_fieldRange K E L]
  refine IsGaloisGroup.of_ringEquiv _ _ _ L
    (AlgHom.equivFieldRange (IsScalarTower.toAlgHom K E L)).toRingEquiv.symm fun ⟨_, ⟨x, rfl⟩⟩ => ?_
  simp [AlgEquiv.symm_apply_eq, Subtype.ext_iff]

@[simp]
/--
theorem `card_fixingSubgroup_eq_finrank` / 定理 `card_fixingSubgroup_eq_finrank`

English:
theorem card_fixingSubgroup_eq_finrank
  given: [Finite G] [IsGaloisGroup G K L]
  proof: card_eq_finrank ..

中文:
定理 card_fixingSubgroup_eq_finrank
  条件: [有限 G] [是Galois群 G K L]
  证明: card_eq_finrank ..

Depends on / 依赖: card_eq_finrank
-/
theorem card_fixingSubgroup_eq_finrank [Finite G] [IsGaloisGroup G K L] :
    Nat.card (fixingSubgroup G (F : Set L)) = Module.finrank F L :=
  card_eq_finrank ..

section GaloisCorrespondence

/--
theorem `fixingSubgroup_le_of_le` / 定理 `fixingSubgroup_le_of_le`

English:
theorem fixingSubgroup_le_of_le
  given: (h : F <= F')
  proof: fun _ hσ ⟨x, hx⟩ => hσ ⟨x, h hx⟩

中文:
定理 fixingSubgroup_le_of_le
  条件: (h : F <= F')
  证明: fun _ hσ ⟨x, hx⟩ => hσ ⟨x, h hx⟩
-/
theorem fixingSubgroup_le_of_le (h : F <= F') :
    fixingSubgroup G (F' : Set L) <= fixingSubgroup G (F : Set L) :=
  fun _ hσ ⟨x, hx⟩ => hσ ⟨x, h hx⟩

section SMulCommClass

variable [SMulCommClass G K L]

@[simp]
/--
theorem `fixingSubgroup_bot` / 定理 `fixingSubgroup_bot`

English:
theorem fixingSubgroup_bot
  statement: fixingSubgroup G ((⊥ : IntermediateField K L) : Set L) = ⊤
  proof: by
  simp [Subgroup.ext_iff, mem_fixingSubgroup_iff, IntermediateField.mem_bot]

@[simp]

中文:
定理 fixingSubgroup_bot
  结论: fixingSubgroup G ((⊥ : 中间域 K L) : 集合 L) = ⊤
  证明: by
  simp [Subgroup.ext_iff, mem_fixingSubgroup_iff, IntermediateField.mem_bot]

@[simp]

Depends on / 依赖: IntermediateField, IntermediateField.mem_bot, Subgroup, Subgroup.ext_iff, ext_iff, mem_bot, mem_fixingSubgroup_iff
-/
theorem fixingSubgroup_bot : fixingSubgroup G ((⊥ : IntermediateField K L) : Set L) = ⊤ := by
  simp [Subgroup.ext_iff, mem_fixingSubgroup_iff, IntermediateField.mem_bot]

@[simp]
/--
theorem `fixedPoints_bot` / 定理 `fixedPoints_bot`

English:
theorem fixedPoints_bot
  proof: by
  simp [IntermediateField.ext_iff]

中文:
定理 fixedPoints_bot
  证明: by
  simp [IntermediateField.ext_iff]

Depends on / 依赖: IntermediateField, IntermediateField.ext_iff, ext_iff
-/
theorem fixedPoints_bot :
    (FixedPoints.intermediateField (⊥ : Subgroup G) : IntermediateField K L) = ⊤ := by
  simp [IntermediateField.ext_iff]

/--
theorem `le_fixedPoints_iff_le_fixingSubgroup` / 定理 `le_fixedPoints_iff_le_fixingSubgroup`

English:
theorem le_fixedPoints_iff_le_fixingSubgroup
  proof: ⟨fun h g hg x => h x.2 ⟨g, hg⟩, fun h x hx g => h g.2 ⟨x, hx⟩⟩

中文:
定理 le_fixedPoints_iff_le_fixingSubgroup
  证明: ⟨fun h g hg x => h x.2 ⟨g, hg⟩, fun h x hx g => h g.2 ⟨x, hx⟩⟩
-/
theorem le_fixedPoints_iff_le_fixingSubgroup :
    F <= FixedPoints.intermediateField H ↔ H <= fixingSubgroup G (F : Set L) :=
  ⟨fun h g hg x => h x.2 ⟨g, hg⟩, fun h x hx g => h g.2 ⟨x, hx⟩⟩

/--
theorem `fixedPoints_le_of_le` / 定理 `fixedPoints_le_of_le`

English:
theorem fixedPoints_le_of_le
  given: (h : H <= H')
  proof: fun _ hσ ⟨x, hx⟩ => hσ ⟨x, h hx⟩

中文:
定理 fixedPoints_le_of_le
  条件: (h : H <= H')
  证明: fun _ hσ ⟨x, hx⟩ => hσ ⟨x, h hx⟩
-/
theorem fixedPoints_le_of_le (h : H <= H') :
    FixedPoints.intermediateField H' <= (FixedPoints.intermediateField H : IntermediateField K L) :=
  fun _ hσ ⟨x, hx⟩ => hσ ⟨x, h hx⟩

end SMulCommClass

section IsGaloisGroup

variable [hGKL : IsGaloisGroup G K L]

-- this can't be a simp-lemma since the left-hand side is not in simp normal form
-- and if the theorem was `fixingSubgroup G Set.univ = ⊥` then `K` couldn't be inferred
/--
theorem `fixingSubgroup_top` / 定理 `fixingSubgroup_top`

English:
theorem fixingSubgroup_top
  statement: fixingSubgroup G ((⊤ : IntermediateField K L) : Set L) = ⊥
  proof: by
  have := hGKL.faithful
  ext; simpa [mem_fixingSubgroup_iff, Set.ext_iff] using MulAction.fixedBy_eq_univ_iff_eq_one

@[simp]

中文:
定理 fixingSubgroup_top
  结论: fixingSubgroup G ((⊤ : 中间域 K L) : 集合 L) = ⊥
  证明: by
  have := hGKL.faithful
  ext; simpa [mem_fixingSubgroup_iff, Set.ext_iff] using MulAction.fixedBy_eq_univ_iff_eq_one

@[simp]

Depends on / 依赖: MulAction, MulAction.fixedBy_eq_univ_iff_eq_one, Set.ext_iff, ext_iff, faithful, fixedBy_eq_univ_iff_eq_one, hGKL.faithful, mem_fixingSubgroup_iff
-/
theorem fixingSubgroup_top : fixingSubgroup G ((⊤ : IntermediateField K L) : Set L) = ⊥ := by
  have := hGKL.faithful
  ext; simpa [mem_fixingSubgroup_iff, Set.ext_iff] using MulAction.fixedBy_eq_univ_iff_eq_one

@[simp]
/--
theorem `fixedPoints_top` / 定理 `fixedPoints_top`

English:
theorem fixedPoints_top
  proof: by
  convert! IsGaloisGroup.fixedPoints_eq_bot G K L
  ext; simp

中文:
定理 fixedPoints_top
  证明: by
  convert! IsGaloisGroup.fixedPoints_eq_bot G K L
  ext; simp

Depends on / 依赖: IsGaloisGroup, IsGaloisGroup.fixedPoints_eq_bot, convert, fixedPoints_eq_bot
-/
theorem fixedPoints_top :
    (FixedPoints.intermediateField (⊤ : Subgroup G) : IntermediateField K L) = ⊥ := by
  convert! IsGaloisGroup.fixedPoints_eq_bot G K L
  ext; simp

/--
Definition of `intermediateFieldEquivSubgroup` / `intermediateFieldEquivSubgroup` 的定义

English:
definition intermediateFieldEquivSubgroup
  signature: [Finite G]
  body: have := isGalois G K L
  have := finiteDimensional G K L
IsGalois.intermediateFieldEquivSubgroup.trans (mulEquivAlgEquiv G K L).comapSubgroup.dual

中文:
定义 intermediateFieldEquivSubgroup
  签名: [有限 G]
  定义体: have := isGalois G K L
  have := finiteDimensional G K L
IsGalois.intermediateFieldEquivSubgroup.trans (mulEquivAlgEquiv G K L).comapSubgroup.dual

Depends on / 依赖: IsGalois, IsGalois.intermediateFieldEquivSubgroup.trans, comapSubgroup, comapSubgroup.dual, finiteDimensional, intermediateFieldEquivSubgroup, isGalois, mulEquivAlgEquiv
-/
noncomputable def intermediateFieldEquivSubgroup [Finite G] :
    IntermediateField K L ≃o (Subgroup G)ᵒᵈ :=
  have := isGalois G K L
  have := finiteDimensional G K L
IsGalois.intermediateFieldEquivSubgroup.trans (mulEquivAlgEquiv G K L).comapSubgroup.dual

/--
theorem `intermediateFieldEquivSubgroup_apply` / 定理 `intermediateFieldEquivSubgroup_apply`

English:
theorem intermediateFieldEquivSubgroup_apply
  given: [Finite G] {F}
  proof: rfl

中文:
定理 intermediateFieldEquivSubgroup_apply
  条件: [有限 G] {F}
  证明: rfl
-/
@[simp] theorem intermediateFieldEquivSubgroup_apply [Finite G] {F} :
    intermediateFieldEquivSubgroup G K L F = .toDual (fixingSubgroup G (F : Set L)) := rfl

/--
theorem `ofDual_intermediateFieldEquivSubgroup_apply` / 定理 `ofDual_intermediateFieldEquivSubgroup_apply`

English:
theorem ofDual_intermediateFieldEquivSubgroup_apply
  given: [Finite G] {F}
  proof: rfl

中文:
定理 ofDual_intermediateFieldEquivSubgroup_apply
  条件: [有限 G] {F}
  证明: rfl
-/
theorem ofDual_intermediateFieldEquivSubgroup_apply [Finite G] {F} :
    (intermediateFieldEquivSubgroup G K L F).ofDual = fixingSubgroup G (F : Set L) := rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `intermediateFieldEquivSubgroup_symm_apply` / 定理 `intermediateFieldEquivSubgroup_symm_apply`

English:
theorem intermediateFieldEquivSubgroup_symm_apply
  given: [Finite G] {H}
  proof: by
  obtain ⟨H, rfl⟩ := OrderDual.toDual.surjective H
  simp [IntermediateField.ext_iff, intermediateFieldEquivSubgroup,
    (mulEquivAlgEquiv G K L).surjective.forall, -mulEquivAlgEquiv_symm_apply]

中文:
定理 intermediateFieldEquivSubgroup_symm_apply
  条件: [有限 G] {H}
  证明: by
  obtain ⟨H, rfl⟩ := OrderDual.toDual.surjective H
  simp [IntermediateField.ext_iff, intermediateFieldEquivSubgroup,
    (mulEquivAlgEquiv G K L).surjective.forall, -mulEquivAlgEquiv_symm_apply]
-/
@[simp] theorem intermediateFieldEquivSubgroup_symm_apply [Finite G] {H} :
    (intermediateFieldEquivSubgroup G K L).symm H = FixedPoints.intermediateField H.ofDual := by
  obtain ⟨H, rfl⟩ := OrderDual.toDual.surjective H
  simp [IntermediateField.ext_iff, intermediateFieldEquivSubgroup,
    (mulEquivAlgEquiv G K L).surjective.forall, -mulEquivAlgEquiv_symm_apply]

/--
theorem `intermediateFieldEquivSubgroup_symm_apply_toDual` / 定理 `intermediateFieldEquivSubgroup_symm_apply_toDual`

English:
theorem intermediateFieldEquivSubgroup_symm_apply_toDual
  given: [Finite G] {H}
  proof: intermediateFieldEquivSubgroup_symm_apply ..

@[simp]

中文:
定理 intermediateFieldEquivSubgroup_symm_apply_toDual
  条件: [有限 G] {H}
  证明: intermediateFieldEquivSubgroup_symm_apply ..

@[simp]

Depends on / 依赖: intermediateFieldEquivSubgroup_symm_apply
-/
theorem intermediateFieldEquivSubgroup_symm_apply_toDual [Finite G] {H} :
    (intermediateFieldEquivSubgroup G K L).symm (.toDual H) = FixedPoints.intermediateField H :=
  intermediateFieldEquivSubgroup_symm_apply ..

@[simp]
/--
theorem `fixingSubgroup_fixedPoints` / 定理 `fixingSubgroup_fixedPoints`

English:
theorem fixingSubgroup_fixedPoints
  given: [Finite G]
  proof: by
  rw [← intermediateFieldEquivSubgroup_symm_apply_toDual]; rw [← ofDual_intermediateFieldEquivSubgroup_apply]; rw [OrderIso.apply_symm_apply]; rw [OrderDual.ofDual_toDual]

@[simp]

中文:
定理 fixingSubgroup_fixedPoints
  条件: [有限 G]
  证明: by
  rw [← intermediateFieldEquivSubgroup_symm_apply_toDual]; rw [← ofDual_intermediateFieldEquivSubgroup_apply]; rw [OrderIso.apply_symm_apply]; rw [OrderDual.ofDual_toDual]

@[simp]

Depends on / 依赖: DecidableEq, DecidableRel, OrderDual, OrderDual.ofDual_toDual, OrderIso, OrderIso.apply_symm_apply, SameCycle, apply_symm_apply, intermediateFieldEquivSubgroup_symm_apply_toDual, ofDual_intermediateFieldEquivSubgroup_apply, ofDual_toDual
-/
theorem fixingSubgroup_fixedPoints [Finite G] :
    fixingSubgroup G ((FixedPoints.intermediateField H : IntermediateField K L) : Set L) = H := by
  rw [← intermediateFieldEquivSubgroup_symm_apply_toDual]; rw [← ofDual_intermediateFieldEquivSubgroup_apply]; rw [OrderIso.apply_symm_apply]; rw [OrderDual.ofDual_toDual]

@[simp]
/--
theorem `fixedPoints_fixingSubgroup` / 定理 `fixedPoints_fixingSubgroup`

English:
theorem fixedPoints_fixingSubgroup
  given: [Finite G]
  proof: by
  rw [← ofDual_intermediateFieldEquivSubgroup_apply]; rw [← intermediateFieldEquivSubgroup_symm_apply]; rw [OrderIso.symm_apply_apply]

中文:
定理 fixedPoints_fixingSubgroup
  条件: [有限 G]
  证明: by
  rw [← ofDual_intermediateFieldEquivSubgroup_apply]; rw [← intermediateFieldEquivSubgroup_symm_apply]; rw [OrderIso.symm_apply_apply]

Depends on / 依赖: OrderIso, OrderIso.symm_apply_apply, intermediateFieldEquivSubgroup_symm_apply, ofDual_intermediateFieldEquivSubgroup_apply, symm_apply_apply
-/
theorem fixedPoints_fixingSubgroup [Finite G] :
    FixedPoints.intermediateField (fixingSubgroup G (F : Set L)) = F := by
  rw [← ofDual_intermediateFieldEquivSubgroup_apply]; rw [← intermediateFieldEquivSubgroup_symm_apply]; rw [OrderIso.symm_apply_apply]

/--
theorem `fixedPoints_eq_range_algebraMap` / 定理 `fixedPoints_eq_range_algebraMap`

English:
theorem fixedPoints_eq_range_algebraMap
  statement: (B : Type*)
  proof: by
  ext
  rw [SetLike.mem_coe]; rw [FixedPoints.mem_intermediateField_iff]; rw [Set.mem_range]
  refine ⟨IsGaloisGroup.isInvariant.isInvariant _, ?_⟩
  rintro ⟨x, rfl⟩ h
  exact smul_algebraMap h x

include K in

中文:
定理 fixedPoints_eq_range_algebraMap
  结论: (B : 类型)
  证明: by
  ext
  rw [SetLike.mem_coe]; rw [FixedPoints.mem_intermediateField_iff]; rw [Set.mem_range]
  refine ⟨IsGaloisGroup.isInvariant.isInvariant _, ?_⟩
  rintro ⟨x, rfl⟩ h
  exact smul_algebraMap h x

include K in

Depends on / 依赖: FixedPoints, FixedPoints.mem_intermediateField_iff, IsGaloisGroup, IsGaloisGroup.isInvariant.isInvariant, Set.mem_range, SetLike, SetLike.mem_coe, isInvariant, mem_coe, mem_intermediateField_iff, mem_range, smul_algebraMap
-/
theorem fixedPoints_eq_range_algebraMap (B : Type*)
    [CommSemiring B] [Algebra B L] [IsGaloisGroup H B L] :
    (FixedPoints.intermediateField H : IntermediateField K L) = Set.range (algebraMap B L) := by
  ext
  rw [SetLike.mem_coe]; rw [FixedPoints.mem_intermediateField_iff]; rw [Set.mem_range]
  refine ⟨IsGaloisGroup.isInvariant.isInvariant _, ?_⟩
  rintro ⟨x, rfl⟩ h
  exact smul_algebraMap h x

include K in
/--
theorem `fixingSubgroup_range_algebraMap'` / 定理 `fixingSubgroup_range_algebraMap'`

English:
theorem fixingSubgroup_range_algebraMap'
  statement: [Finite G] (B : Type*) [CommSemiring B] [Algebra B L]
  proof: by
  rw [← fixedPoints_eq_range_algebraMap G K L H]; rw [fixingSubgroup_fixedPoints]

中文:
定理 fixingSubgroup_range_algebraMap'
  结论: [有限 G] (B : 类型) [交换半环 B] [代数 B L]
  证明: by
  rw [← fixedPoints_eq_range_algebraMap G K L H]; rw [fixingSubgroup_fixedPoints]

Depends on / 依赖: fixedPoints_eq_range_algebraMap, fixingSubgroup_fixedPoints
-/
theorem fixingSubgroup_range_algebraMap' [Finite G] (B : Type*) [CommSemiring B] [Algebra B L]
    [IsGaloisGroup H B L] :
    fixingSubgroup G (Set.range (algebraMap B L)) = H := by
  rw [← fixedPoints_eq_range_algebraMap G K L H]; rw [fixingSubgroup_fixedPoints]

attribute [local instance] FractionRing.liftAlgebra in
/--
theorem `fixingSubgroup_range_algebraMap` / 定理 `fixingSubgroup_range_algebraMap`

English:
theorem fixingSubgroup_range_algebraMap
  statement: [Finite G] (A B C : Type*) (H : Subgroup G)
  proof: by
  have : IsDomain B := (FaithfulSMul.algebraMap_injective B C).isDomain
  have : IsDomain A := (FaithfulSMul.algebraMap_injective A C).isDomain
  let K := FractionRing A
  let L := FractionRing C
  let : MulSemiringAction G L := IsFractionRing.mulSemiringAction G C L
  have : IsGaloisGroup H (Fra

中文:
定理 fixingSubgroup_range_algebraMap
  结论: [有限 G] (A B C : 类型) (H : 子群 G)
  证明: by
  have : IsDomain B := (FaithfulSMul.algebraMap_injective B C).isDomain
  have : IsDomain A := (FaithfulSMul.algebraMap_injective A C).isDomain
  let K := FractionRing A
  let L := FractionRing C
  let : MulSemiringAction G L := IsFractionRing.mulSemiringAction G C L
  have : IsGaloisGroup H (Fra

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, FractionRing, IsDomain, IsFractionRing, IsFractionRing.mulSemiringAction, IsGaloisGroup, IsGaloisGroup.toFractionRing, MulSemiringAction, Set.mem_range, algebraMap_injective, fixingSubgroup_range_algebraMap, isDomain, mem_fixingSubgroup_iff, mem_range, mulSemiringAction, toFractionRing
-/
theorem fixingSubgroup_range_algebraMap [Finite G] (A B C : Type*) (H : Subgroup G)
    [CommRing A] [CommRing B] [CommRing C] [IsDomain C]
    [Algebra A C] [FaithfulSMul A C] [MulSemiringAction G C] [hGAC : IsGaloisGroup G A C]
    [Algebra B C] [FaithfulSMul B C] [hH : IsGaloisGroup H B C] :
    fixingSubgroup G (Set.range (algebraMap B C)) = H := by
  have : IsDomain B := (FaithfulSMul.algebraMap_injective B C).isDomain
  have : IsDomain A := (FaithfulSMul.algebraMap_injective A C).isDomain
  let K := FractionRing A
  let L := FractionRing C
  let : MulSemiringAction G L := IsFractionRing.mulSemiringAction G C L
  have : IsGaloisGroup H (FractionRing B) L := IsGaloisGroup.toFractionRing H B C
  rw [← fixingSubgroup_range_algebraMap' G K L H (FractionRing B)]
  ext g
  simp only [mem_fixingSubgroup_iff, Set.mem_range]
  refine ⟨?_, ?_⟩
  · rintro h _ ⟨x, rfl⟩
    have {x} : g • (algebraMap B L) x = (algebraMap B L) x := by
      rw [IsScalarTower.algebraMap_apply B C L]; rw [← algebraMap.smul']; rw [h _ ⟨x]; rw [rfl⟩]
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective B x
    simp only [map_div₀, ← IsScalarTower.algebraMap_apply, smul_div₀', this]
  · rintro h _ ⟨x, rfl⟩
    apply FaithfulSMul.algebraMap_injective C L
    rw [algebraMap.smul']
    apply h
    use algebraMap B (FractionRing B) x
    rw [← IsScalarTower.algebraMap_apply]; rw [← IsScalarTower.algebraMap_apply]

open Pointwise in
/--
theorem `normal_of_isGalois` / 定理 `normal_of_isGalois`

English:
theorem normal_of_isGalois
  statement: (E : Type*) [Field E] [Algebra K E] [Algebra E L] [IsScalarTower K E L]
  proof: by
  let F := (IsScalarTower.toAlgHom K E L).fieldRange
  have : IsGalois K F := .of_algEquiv (IsScalarTower.toAlgHom K E L).equivFieldRange
  have hFL : IsGaloisGroup H F L := inferInstanceAs (IsGaloisGroup H (algebraMap E L).range L)
  have := isGalois G K L
  have : Finite Gal(L/K) := Finite.of_e

中文:
定理 normal_of_isGalois
  结论: (E : 类型) [域 E] [代数 K E] [代数 E L] [标量塔 K E L]
  证明: by
  let F := (IsScalarTower.toAlgHom K E L).fieldRange
  have : IsGalois K F := .of_algEquiv (IsScalarTower.toAlgHom K E L).equivFieldRange
  have hFL : IsGaloisGroup H F L := inferInstanceAs (IsGaloisGroup H (algebraMap E L).range L)
  have := isGalois G K L
  have : Finite Gal(L/K) := Finite.of_e

Depends on / 依赖: Finite, Finite.of_equiv, IsGalois, IsGaloisGroup, IsScalarTower, IsScalarTower.toAlgHom, MulEquiv, MulEquiv.normal_map_iff, algebraMap, equivFieldRange, fieldRange, fixingSubgroup_fixedPoints, isGalois, mulEquivAlgEquiv, mulEquivCongr_mapSubgroup_fixingSubgroup, normal_map_iff, of_algEquiv, of_equiv, subgroup_iff, subgroup_iff.mp
-/
theorem normal_of_isGalois (E : Type*) [Field E] [Algebra K E] [Algebra E L] [IsScalarTower K E L]
    [Finite G] [IsGaloisGroup H E L] [IsGalois K E] : H.Normal := by
  let F := (IsScalarTower.toAlgHom K E L).fieldRange
  have : IsGalois K F := .of_algEquiv (IsScalarTower.toAlgHom K E L).equivFieldRange
  have hFL : IsGaloisGroup H F L := inferInstanceAs (IsGaloisGroup H (algebraMap E L).range L)
  have := isGalois G K L
  have : Finite Gal(L/K) := Finite.of_equiv _ (mulEquivAlgEquiv G K L).toEquiv
  rw [← fixingSubgroup_fixedPoints G K L H]; rw [subgroup_iff.mp hFL]; rw [← mulEquivCongr_mapSubgroup_fixingSubgroup Gal(L/K) G K]; rw [MulEquiv.normal_map_iff]
  exact IsGalois.fixingSubgroup_normal_of_isGalois F

end IsGaloisGroup

end GaloisCorrespondence

section Quotient

section Domain

variable (A B C : Type*) [CommRing A] [CommRing B] [CommRing C] [IsDomain C] [Algebra A B]
    [Algebra A C] [Algebra B C] [FaithfulSMul A B] [FaithfulSMul B C] [IsScalarTower A B C]

/--
theorem `quotient` / 定理 `quotient`

English:
theorem quotient
  statement: [Finite G] (N : Subgroup G) [N.Normal] [MulSemiringAction G C]
  proof: fun {g₁} {g₂} => Quotient.inductionOn₂' g₁ g₂ fun g₁ g₂ h => by
    have : FaithfulSMul A C := FaithfulSMul.trans A B C
    have h' : forall g : G, (forall x : B, g • x = x) -> g in N := by
      simp [← fixingSubgroup_range_algebraMap G A B C N, mem_fixingSubgroup_iff, ← algebraMap.smul',
        (

中文:
定理 quotient
  结论: [有限 G] (N : 子群 G) [N.正规] [MulSemiring作用 G C]
  证明: fun {g₁} {g₂} => Quotient.inductionOn₂' g₁ g₂ fun g₁ g₂ h => by
    have : FaithfulSMul A C := FaithfulSMul.trans A B C
    have h' : forall g : G, (forall x : B, g • x = x) -> g in N := by
      simp [← fixingSubgroup_range_algebraMap G A B C N, mem_fixingSubgroup_iff, ← algebraMap.smul',
        (

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, FaithfulSMul.trans, MulAction, MulAction.coe_quotien, Quotient, Quotient.inductionOn, Quotient.mk, QuotientGroup, QuotientGroup.mk, _apply, algebraMap, algebraMap.smul, algebraMap_injective, coe_quotien, eq_iff, fixingSubgroup_range_algebraMap, inv_smul_eq_iff, map_inv, map_mul
-/
theorem quotient [Finite G] (N : Subgroup G) [N.Normal] [MulSemiringAction G C]
    [hG : IsGaloisGroup G A C] [MulSemiringAction G B] [MulSemiringAction (G ⧸ N) B]
    [SMulCommClass (G ⧸ N) A B] [SMulDistribClass G B C] [IsScalarTower G (G ⧸ N) B]
    [IsGaloisGroup N B C] :
    IsGaloisGroup (G ⧸ N) A B where
  faithful.eq_of_smul_eq_smul := fun {g₁} {g₂} => Quotient.inductionOn₂' g₁ g₂ fun g₁ g₂ h => by
    have : FaithfulSMul A C := FaithfulSMul.trans A B C
    have h' : forall g : G, (forall x : B, g • x = x) -> g in N := by
      simp [← fixingSubgroup_range_algebraMap G A B C N, mem_fixingSubgroup_iff, ← algebraMap.smul',
        (FaithfulSMul.algebraMap_injective B C).eq_iff]
    have {g : G} : Quotient.mk'' g = QuotientGroup.mk' N g := rfl
    simp_rw [← inv_smul_eq_iff, this, ← map_inv, smul_smul, ← map_mul,
      QuotientGroup.mk'_apply, MulAction.coe_quotient_smul] at h
    have := h' _ h
    rwa [QuotientGroup.eq, ← Subgroup.inv_mem_iff, mul_inv_rev, inv_inv]
  commutes := inferInstance
  isInvariant.isInvariant x h := by
    simp_rw [← (FaithfulSMul.algebraMap_injective B C).eq_iff, ← IsScalarTower.algebraMap_apply]
    apply hG.isInvariant.isInvariant (algebraMap B C x)
    intro g
have := (FaithfulSMul.algebraMap_injective B C).eq_iff.mpr h g
    rwa [MulAction.coe_quotient_smul, algebraMap.smul'] at this

/--
Definition of `quotientMulEquiv` / `quotientMulEquiv` 的定义

English:
definition quotientMulEquiv
  signature: [Finite G] [Finite G'] (N : Subgroup G) [N.Normal]
  body: haveI : IsDomain B := (FaithfulSMul.algebraMap_injective B C).isDomain
  letI := mulSemiringActionOfNormal G B C N
  letI := mulSemiringActionQuotient G B C N
  haveI := smulCommClassQuotient G A B C N
  haveI := quotient G A B C N
  mulEquivCongr (G ⧸ N) G' A B

@[simp]

中文:
定义 quotientMulEquiv
  签名: [有限 G] [有限 G'] (N : 子群 G) [N.正规]
  定义体: haveI : IsDomain B := (FaithfulSMul.algebraMap_injective B C).isDomain
  letI := mulSemiringActionOfNormal G B C N
  letI := mulSemiringActionQuotient G B C N
  haveI := smulCommClassQuotient G A B C N
  haveI := quotient G A B C N
  mulEquivCongr (G ⧸ N) G' A B

@[simp]

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, IsDomain, algebraMap_injective, isDomain, mulEquivCongr, mulSemiringActionOfNormal, mulSemiringActionQuotient, quotient, smulCommClassQuotient
-/
noncomputable def quotientMulEquiv [Finite G] [Finite G'] (N : Subgroup G) [N.Normal]
    [MulSemiringAction G C] [IsGaloisGroup G A C] [IsGaloisGroup N B C] [MulSemiringAction G' B]
    [IsGaloisGroup G' A B] :
    G ⧸ N ≃* G' :=
  haveI : IsDomain B := (FaithfulSMul.algebraMap_injective B C).isDomain
  letI := mulSemiringActionOfNormal G B C N
  letI := mulSemiringActionQuotient G B C N
  haveI := smulCommClassQuotient G A B C N
  haveI := quotient G A B C N
  mulEquivCongr (G ⧸ N) G' A B

@[simp]
/--
theorem `algebraMap_quotientMulEquiv_smul` / 定理 `algebraMap_quotientMulEquiv_smul`

English:
theorem algebraMap_quotientMulEquiv_smul
  statement: [Finite G] [Finite G'] (N : Subgroup G) [N.Normal]
  proof: by
  have : IsDomain B := (FaithfulSMul.algebraMap_injective B C).isDomain
  let := mulSemiringActionOfNormal G B C N
  let := mulSemiringActionQuotient G B C N
  have := smulCommClassQuotient G A B C N
  have := quotient G A B C N
  rw [← algebraMap_smulOfNormal G B C N g x]
  congr
  apply mulEqui

中文:
定理 algebraMap_quotientMulEquiv_smul
  结论: [有限 G] [有限 G'] (N : 子群 G) [N.正规]
  证明: by
  have : IsDomain B := (FaithfulSMul.algebraMap_injective B C).isDomain
  let := mulSemiringActionOfNormal G B C N
  let := mulSemiringActionQuotient G B C N
  have := smulCommClassQuotient G A B C N
  have := quotient G A B C N
  rw [← algebraMap_smulOfNormal G B C N g x]
  congr
  apply mulEqui

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, IsDomain, algebraMap_injective, algebraMap_smulOfNormal, isDomain, mulEquivCongr_apply_smul, mulSemiringActionOfNormal, mulSemiringActionQuotient, quotient, smulCommClassQuotient
-/
theorem algebraMap_quotientMulEquiv_smul [Finite G] [Finite G'] (N : Subgroup G) [N.Normal]
    [MulSemiringAction G C] [IsGaloisGroup G A C] [IsGaloisGroup N B C] [MulSemiringAction G' B]
    [IsGaloisGroup G' A B] (g : G) (x : B) :
    algebraMap B C (quotientMulEquiv G G' A B C N g • x) = g • algebraMap B C x := by
  have : IsDomain B := (FaithfulSMul.algebraMap_injective B C).isDomain
  let := mulSemiringActionOfNormal G B C N
  let := mulSemiringActionQuotient G B C N
  have := smulCommClassQuotient G A B C N
  have := quotient G A B C N
  rw [← algebraMap_smulOfNormal G B C N g x]
  congr
  apply mulEquivCongr_apply_smul

attribute [local instance] FractionRing.liftAlgebra in
/--
Definition of `restrictHom` / `restrictHom` 的定义

English:
definition restrictHom
  signature: [Finite G] [Finite G'] [MulSemiringAction G C] [IsGaloisGroup G A C]
  body: haveI : IsDomain B := IsDomain.of_faithfulSMul B C
  haveI : IsDomain A := IsDomain.of_faithfulSMul A B
  haveI : FaithfulSMul A C := FaithfulSMul.trans A B C
  letI : MulSemiringAction G (FractionRing C) :=
    IsFractionRing.mulSemiringAction G C (FractionRing C)
  letI N := fixingSubgroup G (Set.

中文:
定义 restrictHom
  签名: [有限 G] [有限 G'] [MulSemiring作用 G C] [是Galois群 G A C]
  定义体: haveI : IsDomain B := IsDomain.of_faithfulSMul B C
  haveI : IsDomain A := IsDomain.of_faithfulSMul A B
  haveI : FaithfulSMul A C := FaithfulSMul.trans A B C
  letI : MulSemiringAction G (FractionRing C) :=
    IsFractionRing.mulSemiringAction G C (FractionRing C)
  letI N := fixingSubgroup G (Set.

Depends on / 依赖: FaithfulSMul, FaithfulSMul.trans, FractionRing, IsDomain, IsDomain.of_faithfulSMul, IsFractionRing, IsFractionRing.mulSemiringAction, IsGaloisGroup, MulSemiringAction, Set.range, algebraMap, fixingSubgroup, mulSemiringAction, of_faithfulSMul, of_isScalarTower
-/
noncomputable def restrictHom [Finite G] [Finite G'] [MulSemiringAction G C] [IsGaloisGroup G A C]
    [MulSemiringAction G' B] [IsGaloisGroup G' A B] :
    G ->* G' :=
  haveI : IsDomain B := IsDomain.of_faithfulSMul B C
  haveI : IsDomain A := IsDomain.of_faithfulSMul A B
  haveI : FaithfulSMul A C := FaithfulSMul.trans A B C
  letI : MulSemiringAction G (FractionRing C) :=
    IsFractionRing.mulSemiringAction G C (FractionRing C)
  letI N := fixingSubgroup G (Set.range (algebraMap (FractionRing B) (FractionRing C)))
  haveI : IsGaloisGroup N (FractionRing B) (FractionRing C) :=
    of_isScalarTower G (FractionRing A) (FractionRing C) (FractionRing B)
  letI : MulSemiringAction G' (FractionRing B) :=
    IsFractionRing.mulSemiringAction G' B (FractionRing B)
  haveI := isGalois G' (FractionRing A) (FractionRing B)
  haveI : N.Normal := normal_of_isGalois G (FractionRing A) (FractionRing C) N (FractionRing B)
  (quotientMulEquiv G G' (FractionRing A) (FractionRing B) (FractionRing C) N).toMonoidHom.comp
    (QuotientGroup.mk' N)

attribute [local instance] FractionRing.liftAlgebra in
@[simp]
/--
theorem `algebraMap_restrictHom_smul` / 定理 `algebraMap_restrictHom_smul`

English:
theorem algebraMap_restrictHom_smul
  statement: [Finite G] [Finite G'] [MulSemiringAction G C]
  proof: by
  have : IsDomain B := IsDomain.of_faithfulSMul B C
  have : IsDomain A := IsDomain.of_faithfulSMul A B
  have : FaithfulSMul A C := FaithfulSMul.trans A B C
  let : MulSemiringAction G (FractionRing C) :=
    IsFractionRing.mulSemiringAction G C (FractionRing C)
  let : MulSemiringAction G' (Fra

中文:
定理 algebraMap_restrictHom_smul
  结论: [有限 G] [有限 G'] [MulSemiring作用 G C]
  证明: by
  have : IsDomain B := IsDomain.of_faithfulSMul B C
  have : IsDomain A := IsDomain.of_faithfulSMul A B
  have : FaithfulSMul A C := FaithfulSMul.trans A B C
  let : MulSemiringAction G (FractionRing C) :=
    IsFractionRing.mulSemiringAction G C (FractionRing C)
  let : MulSemiringAction G' (Fra

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, FaithfulSMul.trans, Fractio, FractionRing, IsDomain, IsDomain.of_faithfulSMul, IsFractionRing, IsFractionRing.mulSemiringAction, IsScalarTower, IsScalarTower.algebraMap_apply, MulSemiringAction, algebraMap_apply, algebraMap_injective, mulSemiringAction, of_faithfulSMul
-/
theorem algebraMap_restrictHom_smul [Finite G] [Finite G'] [MulSemiringAction G C]
    [IsGaloisGroup G A C] [MulSemiringAction G' B] [IsGaloisGroup G' A B] (g : G) (x : B) :
    algebraMap B C (restrictHom G G' A B C g • x) = g • algebraMap B C x := by
  have : IsDomain B := IsDomain.of_faithfulSMul B C
  have : IsDomain A := IsDomain.of_faithfulSMul A B
  have : FaithfulSMul A C := FaithfulSMul.trans A B C
  let : MulSemiringAction G (FractionRing C) :=
    IsFractionRing.mulSemiringAction G C (FractionRing C)
  let : MulSemiringAction G' (FractionRing B) :=
    IsFractionRing.mulSemiringAction G' B (FractionRing B)
  apply FaithfulSMul.algebraMap_injective C (FractionRing C)
  rw [← IsScalarTower.algebraMap_apply]; rw [IsScalarTower.algebraMap_apply B (FractionRing B) (FractionRing C)]
  simp only [restrictHom, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_comp, MonoidHom.coe_coe,
    QuotientGroup.coe_mk', Function.comp_apply]
  rw [algebraMap.smul']; rw [algebraMap_quotientMulEquiv_smul]; rw [← IsScalarTower.algebraMap_apply]; rw [algebraMap.smul']; rw [← IsScalarTower.algebraMap_apply]

attribute [local instance] FractionRing.liftAlgebra in
/--
theorem `restrictHom_surjective` / 定理 `restrictHom_surjective`

English:
theorem restrictHom_surjective
  statement: [Finite G] [Finite G'] [MulSemiringAction G C]
  proof: by
  simpa [restrictHom] using QuotientGroup.mk_surjective

中文:
定理 restrictHom_surjective
  结论: [有限 G] [有限 G'] [MulSemiring作用 G C]
  证明: by
  simpa [restrictHom] using QuotientGroup.mk_surjective

Depends on / 依赖: QuotientGroup, QuotientGroup.mk_surjective, mk_surjective, restrictHom
-/
theorem restrictHom_surjective [Finite G] [Finite G'] [MulSemiringAction G C]
    [IsGaloisGroup G A C] [MulSemiringAction G' B] [IsGaloisGroup G' A B] :
    Function.Surjective (restrictHom G G' A B C) := by
  simpa [restrictHom] using QuotientGroup.mk_surjective

open Pointwise in
/--
theorem `restrictHom_smul_under` / 定理 `restrictHom_smul_under`

English:
theorem restrictHom_smul_under
  statement: [Finite G] [Finite G'] [MulSemiringAction G C]
  proof: by
  simp [Ideal.ext_iff, Ideal.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv]

中文:
定理 restrictHom_smul_under
  结论: [有限 G] [有限 G'] [MulSemiring作用 G C]
  证明: by
  simp [Ideal.ext_iff, Ideal.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv]

Depends on / 依赖: Ideal.ext_iff, Ideal.mem_pointwise_smul_iff_inv_smul_mem, ext_iff, map_inv, mem_pointwise_smul_iff_inv_smul_mem
-/
theorem restrictHom_smul_under [Finite G] [Finite G'] [MulSemiringAction G C]
    [IsGaloisGroup G A C] [MulSemiringAction G' B] [IsGaloisGroup G' A B] (g : G) (I : Ideal C) :
    restrictHom G G' A B C g • I.under B = (g • I).under B := by
  simp [Ideal.ext_iff, Ideal.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv]

end Domain

noncomputable section IntermediateField

variable (N : Subgroup G) [N.Normal] [IsGaloisGroup N F L]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Finite
  signature: G] [IsGaloisGroup G K L] : IsGaloisGroup (G ⧸ N) K F
  body: letI := smulOfNormal G F L N
  haveI := smulDistribClass_smulOfNormal G F L N
  letI := mulSemiringActionOfSmulDistribClass F L G
  quotient G K F L N

中文:
实例 [有限
  签名: G] [是Galois群 G K L] : 是Galois群 (G ⧸ N) K F
  定义体: letI := smulOfNormal G F L N
  haveI := smulDistribClass_smulOfNormal G F L N
  letI := mulSemiringActionOfSmulDistribClass F L G
  quotient G K F L N

Depends on / 依赖: mulSemiringActionOfSmulDistribClass, quotient, smulDistribClass_smulOfNormal, smulOfNormal
-/
instance [Finite G] [IsGaloisGroup G K L] : IsGaloisGroup (G ⧸ N) K F :=
  letI := smulOfNormal G F L N
  haveI := smulDistribClass_smulOfNormal G F L N
  letI := mulSemiringActionOfSmulDistribClass F L G
  quotient G K F L N

variable (E : IntermediateField K L) [hE : IsGaloisGroup H E L]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `map_quotientMk'` / 定理 `map_quotientMk'`

English:
theorem map_quotientMk'
  given: [Finite G] [IsGaloisGroup G K L] (h : E <= F)
  proof: (IntermediateField.inclusion h).toAlgebra
    IsGaloisGroup (H.map (QuotientGroup.mk' N)) E F :=
  let : Algebra E F := (IntermediateField.inclusion h).toAlgebra
  let : SMul G F := smulOfNormal G F L N
  have : SMulDistribClass G F L := smulDistribClass_smulOfNormal G F L N
  let := mulSemiringActi

中文:
定理 map_quotientMk'
  条件: [有限 G] [是Galois群 G K L] (h : E <= F)
  证明: (IntermediateField.inclusion h).toAlgebra
    IsGaloisGroup (H.map (QuotientGroup.mk' N)) E F :=
  let : Algebra E F := (IntermediateField.inclusion h).toAlgebra
  let : SMul G F := smulOfNormal G F L N
  have : SMulDistribClass G F L := smulDistribClass_smulOfNormal G F L N
  let := mulSemiringActi

Depends on / 依赖: IntermediateField, IntermediateField.inclusion, inclusion, toAlgebra
-/
theorem map_quotientMk' [Finite G] [IsGaloisGroup G K L] (h : E <= F) :
    letI : Algebra E F := (IntermediateField.inclusion h).toAlgebra
    IsGaloisGroup (H.map (QuotientGroup.mk' N)) E F :=
  let : Algebra E F := (IntermediateField.inclusion h).toAlgebra
  let : SMul G F := smulOfNormal G F L N
  have : SMulDistribClass G F L := smulDistribClass_smulOfNormal G F L N
  let := mulSemiringActionOfSmulDistribClass F L G
  have : IsScalarTower E F L := IsScalarTower.of_algebraMap_eq' rfl
  { faithful := have := (inferInstance : IsGaloisGroup (G ⧸ N) K F).faithful; inferInstance
    commutes := ⟨by
      intro ⟨_, g, hg, rfl⟩ x y
      apply FaithfulSMul.algebraMap_injective F L
      simpa [MulAction.subgroup_smul_def, algebraMap.coe_smul', algebraMap.coe_smul]
        using hE.commutes.smul_comm ⟨g, hg⟩ x (y : L)⟩
    isInvariant := ⟨fun x h => by
      obtain ⟨a, ha⟩ := hE.isInvariant.isInvariant (algebraMap F L x) (by
        rintro ⟨g, hg⟩
        rw [MulAction.subgroup_smul_def]; rw [← algebraMap.smul']
exact congr_arg (algebraMap F L) h ⟨g, ⟨g, hg, rfl⟩⟩)
      exact ⟨a, FaithfulSMul.algebraMap_injective F L
        (by rw [← IsScalarTower.algebraMap_apply, ha])⟩⟩ }

@[deprecated (since := "2026-04-21")] alias quotientMap := map_quotientMk'

end IntermediateField

end Quotient

end IsGaloisGroup
