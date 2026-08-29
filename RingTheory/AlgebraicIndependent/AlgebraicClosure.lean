/-
Copyright (c) 2024 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.AlgebraicIndependent.Transcendental

/-!
# Algebraic independence persists to the algebraic closure

## Main results

* `AlgebraicIndependent.extendScalars`: if A/S/R is a tower of algebras with S/R algebraic,
  then a family of elements in A that are algebraically independent over R remains algebraically
  independent over S, provided that S has no zero divisors.

* `AlgebraicIndependent.algebraicClosure`: an algebraically independent family remains
  algebraically independent over the algebraic closure.
-/

public section

open Function Algebra

section

variable {ι R S A : Type*} {x : ι -> A} (S)
variable [CommRing R] [CommRing S] [CommRing A]
variable [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
variable [NoZeroDivisors S] (hx : AlgebraicIndependent R x)
include hx

namespace AlgebraicIndependent

/--
theorem `extendScalars` / 定理 `extendScalars`

English:
theorem extendScalars
  given: [alg : Algebra.IsAlgebraic R S]
  statement: AlgebraicIndependent S x
  proof: by
  refine algebraicIndependent_of_finite_type'
    (Algebra.IsAlgebraic.injective_tower_top S hx.algebraMap_injective) fun t fin ind i hi => ?_
  let Rt := adjoin R (x '' t)
  let St := adjoin S (x '' t)
  let _ : Algebra Rt St :=
    (Rt.inclusion (T := St.restrictScalars R) <| adjoin_le <| by ex

中文:
定理 extendScalars
  条件: [alg : 代数.是代数 R S]
  结论: AlgebraicIndependent S x
  证明: by
  refine algebraicIndependent_of_finite_type'
    (Algebra.IsAlgebraic.injective_tower_top S hx.algebraMap_injective) fun t fin ind i hi => ?_
  let Rt := adjoin R (x '' t)
  let St := adjoin S (x '' t)
  let _ : Algebra Rt St :=
    (Rt.inclusion (T := St.restrictScalars R) <| adjoin_le <| by ex

Depends on / 依赖: Algebra, Algebra.IsAlgebraic.injective_tower_top, IsAlgebraic, IsScalarTower, NoZeroDivisors, Rt.inclusion, Set.image_eq_range, St.restrictScalars, adjoin, adjoin_le, aevalEquiv, algebraMap_injective, algebraicIndependent_of_finite_type, hx.algebraMap_injective, image_eq_range, inclusion, ind.aevalEquiv, injective, injective_tower_top, noZeroDivisors
-/
theorem extendScalars [alg : Algebra.IsAlgebraic R S] : AlgebraicIndependent S x := by
  refine algebraicIndependent_of_finite_type'
    (Algebra.IsAlgebraic.injective_tower_top S hx.algebraMap_injective) fun t fin ind i hi => ?_
  let Rt := adjoin R (x '' t)
  let St := adjoin S (x '' t)
  let _ : Algebra Rt St :=
    (Rt.inclusion (T := St.restrictScalars R) <| adjoin_le <| by exact subset_adjoin).toAlgebra
  have : IsScalarTower Rt St A := .of_algebraMap_eq fun ⟨y, _⟩ => show y = y from rfl
  have : NoZeroDivisors St := (Set.image_eq_range _ _ ▸ ind.aevalEquiv)
.symm.injective.noZeroDivisors _ (map_zero _) (map_mul _)
  have : NoZeroDivisors Rt := (Subalgebra.inclusion_injective _).noZeroDivisors
    (algebraMap Rt St) (map_zero _) (map_mul _)
  have : Algebra.IsAlgebraic Rt St := ⟨fun ⟨y, hy⟩ => by
    rw [← isAlgebraic_algHom_iff (IsScalarTower.toAlgHom Rt St A) Subtype.val_injective]
    change IsAlgebraic Rt y
    have := Algebra.IsAlgebraic.nontrivial R S
    have := hx.algebraMap_injective.nontrivial
    exact adjoin_induction (fun _ h => isAlgebraic_algebraMap (⟨_, subset_adjoin h⟩ : Rt))
      (fun z => ((alg.1 z).algHom (IsScalarTower.toAlgHom R S A)).extendScalars fun _ _ eq => by
        exact hx.algebraMap_injective congr($eq.1)) (fun _ _ _ _ => .add) (fun _ _ _ _ => .mul) hy⟩
  change Transcendental St (x i)
  exact (hx.transcendental_adjoin hi).extendScalars _

/--
theorem `extendScalars_of_isIntegral` / 定理 `extendScalars_of_isIntegral`

English:
theorem extendScalars_of_isIntegral
  given: [Algebra.IsIntegral R S]
  statement: AlgebraicIndependent S x
  proof: by
  nontriviality S
  have := Module.nontrivial R S
  exact hx.extendScalars S

中文:
定理 extendScalars_of_is整数egral
  条件: [代数.是整 R S]
  结论: AlgebraicIndependent S x
  证明: by
  nontriviality S
  have := Module.nontrivial R S
  exact hx.extendScalars S

Depends on / 依赖: Module, Module.nontrivial, extendScalars, hx.extendScalars, nontrivial, nontriviality
-/
theorem extendScalars_of_isIntegral [Algebra.IsIntegral R S] : AlgebraicIndependent S x := by
  nontriviality S
  have := Module.nontrivial R S
  exact hx.extendScalars S

/--
theorem `subalgebraAlgebraicClosure` / 定理 `subalgebraAlgebraicClosure`

English:
theorem subalgebraAlgebraicClosure
  given: [IsDomain R] [NoZeroDivisors A]
  proof: hx.extendScalars _

中文:
定理 subalgebraAlgebraicClosure
  条件: [是整环 R] [无零因子 A]
  证明: hx.extendScalars _

Depends on / 依赖: extendScalars, hx.extendScalars
-/
theorem subalgebraAlgebraicClosure [IsDomain R] [NoZeroDivisors A] :
    AlgebraicIndependent (Subalgebra.algebraicClosure R A) x :=
  hx.extendScalars _

/--
theorem `integralClosure` / 定理 `integralClosure`

English:
theorem integralClosure
  given: [NoZeroDivisors A]
  proof: hx.extendScalars_of_isIntegral _

omit hx in

中文:
定理 integralClosure
  条件: [无零因子 A]
  证明: hx.extendScalars_of_isIntegral _

omit hx in
-/
protected theorem integralClosure [NoZeroDivisors A] :
    AlgebraicIndependent (integralClosure R A) x :=
  hx.extendScalars_of_isIntegral _

omit hx in
/--
theorem `algebraicClosure` / 定理 `algebraicClosure`

English:
theorem algebraicClosure
  statement: {F E : Type*} [Field F] [Field E] [Algebra F E] {x : ι -> E}
  proof: hx.extendScalars _

中文:
定理 algebraicClosure
  结论: {F E : 类型} [域 F] [域 E] [代数 F E] {x : ι -> E}
  证明: hx.extendScalars _
-/
protected theorem algebraicClosure {F E : Type*} [Field F] [Field E] [Algebra F E] {x : ι -> E}
    (hx : AlgebraicIndependent F x) : AlgebraicIndependent (algebraicClosure F E) x :=
  hx.extendScalars _

end AlgebraicIndependent

namespace Algebra

variable (R) [FaithfulSMul R S]
omit hx

/--
theorem `IsIntegral.algebraicIndependent_iff` / 定理 `IsIntegral.algebraicIndependent_iff`

English:
theorem IsIntegral.algebraicIndependent_iff
  given: [Algebra.IsIntegral R S]
  proof: ⟨(·.extendScalars_of_isIntegral _),
    (·.restrictScalars (FaithfulSMul.algebraMap_injective R S))⟩

中文:
定理 是整.algebraicIndependent_iff
  条件: [代数.是整 R S]
  证明: ⟨(·.extendScalars_of_isIntegral _),
    (·.restrictScalars (FaithfulSMul.algebraMap_injective R S))⟩
-/
protected theorem IsIntegral.algebraicIndependent_iff [Algebra.IsIntegral R S] :
    AlgebraicIndependent R x ↔ AlgebraicIndependent S x :=
  ⟨(·.extendScalars_of_isIntegral _),
    (·.restrictScalars (FaithfulSMul.algebraMap_injective R S))⟩

/--
theorem `IsIntegral.isTranscendenceBasis_iff` / 定理 `IsIntegral.isTranscendenceBasis_iff`

English:
theorem IsIntegral.isTranscendenceBasis_iff
  given: [Algebra.IsIntegral R S]
  proof: by
  simp_rw [IsTranscendenceBasis, IsIntegral.algebraicIndependent_iff R S]

中文:
定理 是整.isTranscendenceBasis_iff
  条件: [代数.是整 R S]
  证明: by
  simp_rw [IsTranscendenceBasis, IsIntegral.algebraicIndependent_iff R S]
-/
protected theorem IsIntegral.isTranscendenceBasis_iff [Algebra.IsIntegral R S] :
    IsTranscendenceBasis R x ↔ IsTranscendenceBasis S x := by
  simp_rw [IsTranscendenceBasis, IsIntegral.algebraicIndependent_iff R S]

/--
theorem `IsAlgebraic.algebraicIndependent_iff` / 定理 `IsAlgebraic.algebraicIndependent_iff`

English:
theorem IsAlgebraic.algebraicIndependent_iff
  given: [Algebra.IsAlgebraic R S]
  proof: ⟨(·.extendScalars _), (·.restrictScalars (FaithfulSMul.algebraMap_injective R S))⟩

中文:
定理 是代数.algebraicIndependent_iff
  条件: [代数.是代数 R S]
  证明: ⟨(·.extendScalars _), (·.restrictScalars (FaithfulSMul.algebraMap_injective R S))⟩
-/
protected theorem IsAlgebraic.algebraicIndependent_iff [Algebra.IsAlgebraic R S] :
    AlgebraicIndependent R x ↔ AlgebraicIndependent S x :=
  ⟨(·.extendScalars _), (·.restrictScalars (FaithfulSMul.algebraMap_injective R S))⟩

/--
theorem `IsAlgebraic.isTranscendenceBasis_iff` / 定理 `IsAlgebraic.isTranscendenceBasis_iff`

English:
theorem IsAlgebraic.isTranscendenceBasis_iff
  given: [Algebra.IsAlgebraic R S]
  proof: by
  simp_rw [IsTranscendenceBasis, IsAlgebraic.algebraicIndependent_iff R S]

中文:
定理 是代数.isTranscendenceBasis_iff
  条件: [代数.是代数 R S]
  证明: by
  simp_rw [IsTranscendenceBasis, IsAlgebraic.algebraicIndependent_iff R S]
-/
protected theorem IsAlgebraic.isTranscendenceBasis_iff [Algebra.IsAlgebraic R S] :
    IsTranscendenceBasis R x ↔ IsTranscendenceBasis S x := by
  simp_rw [IsTranscendenceBasis, IsAlgebraic.algebraicIndependent_iff R S]

end Algebra

end

namespace IntermediateField

variable {ι F E R S : Type*} {s : Set E}
variable [Field F] [Field E] [Algebra F E]
variable [CommRing R] [Algebra R F] [Algebra R E] [IsScalarTower R F E]

open scoped algebraAdjoinAdjoin

section Ring

variable [Ring S] [Algebra E S]

/--
theorem `isAlgebraic_adjoin_iff` / 定理 `isAlgebraic_adjoin_iff`

English:
theorem isAlgebraic_adjoin_iff
  given: {x : S}
  proof: (IsAlgebraic.isAlgebraic_iff ..).symm

中文:
定理 isAlgebraic_adjoin_iff
  条件: {x : S}
  证明: (IsAlgebraic.isAlgebraic_iff ..).symm

Depends on / 依赖: IsAlgebraic, IsAlgebraic.isAlgebraic_iff, isAlgebraic_iff
-/
theorem isAlgebraic_adjoin_iff {x : S} :
    IsAlgebraic (adjoin F s) x ↔ IsAlgebraic (Algebra.adjoin F s) x :=
  (IsAlgebraic.isAlgebraic_iff ..).symm

/--
theorem `isAlgebraic_adjoin_iff_top` / 定理 `isAlgebraic_adjoin_iff_top`

English:
theorem isAlgebraic_adjoin_iff_top
  proof: (IsAlgebraic.isAlgebraic_iff_top ..).symm

中文:
定理 isAlgebraic_adjoin_iff_top
  证明: (IsAlgebraic.isAlgebraic_iff_top ..).symm

Depends on / 依赖: IsAlgebraic, IsAlgebraic.isAlgebraic_iff_top, isAlgebraic_iff_top
-/
theorem isAlgebraic_adjoin_iff_top :
    Algebra.IsAlgebraic (adjoin F s) S ↔ Algebra.IsAlgebraic (Algebra.adjoin F s) S :=
  (IsAlgebraic.isAlgebraic_iff_top ..).symm

/--
theorem `isAlgebraic_adjoin_iff_bot` / 定理 `isAlgebraic_adjoin_iff_bot`

English:
theorem isAlgebraic_adjoin_iff_bot
  proof: IsAlgebraic.isAlgebraic_iff_bot ..

中文:
定理 isAlgebraic_adjoin_iff_bot
  证明: IsAlgebraic.isAlgebraic_iff_bot ..

Depends on / 依赖: IsAlgebraic, IsAlgebraic.isAlgebraic_iff_bot, isAlgebraic_iff_bot
-/
theorem isAlgebraic_adjoin_iff_bot :
    Algebra.IsAlgebraic R (adjoin F s) ↔ Algebra.IsAlgebraic R (Algebra.adjoin F s) :=
  IsAlgebraic.isAlgebraic_iff_bot ..

/--
theorem `transcendental_adjoin_iff` / 定理 `transcendental_adjoin_iff`

English:
theorem transcendental_adjoin_iff
  given: {x : S}
  proof: (IsAlgebraic.transcendental_iff ..).symm

中文:
定理 transcendental_adjoin_iff
  条件: {x : S}
  证明: (IsAlgebraic.transcendental_iff ..).symm

Depends on / 依赖: IsAlgebraic, IsAlgebraic.transcendental_iff, transcendental_iff
-/
theorem transcendental_adjoin_iff {x : S} :
    Transcendental (adjoin F s) x ↔ Transcendental (Algebra.adjoin F s) x :=
  (IsAlgebraic.transcendental_iff ..).symm

end Ring

variable [CommRing S] [Algebra E S]

/--
theorem `algebraicIndependent_adjoin_iff` / 定理 `algebraicIndependent_adjoin_iff`

English:
theorem algebraicIndependent_adjoin_iff
  given: {x : ι -> S}
  proof: (Algebra.IsAlgebraic.algebraicIndependent_iff ..).symm

中文:
定理 algebraicIndependent_adjoin_iff
  条件: {x : ι -> S}
  证明: (Algebra.IsAlgebraic.algebraicIndependent_iff ..).symm

Depends on / 依赖: Algebra, Algebra.IsAlgebraic.algebraicIndependent_iff, IsAlgebraic, algebraicIndependent_iff
-/
theorem algebraicIndependent_adjoin_iff {x : ι -> S} :
    AlgebraicIndependent (adjoin F s) x ↔ AlgebraicIndependent (Algebra.adjoin F s) x :=
  (Algebra.IsAlgebraic.algebraicIndependent_iff ..).symm

/--
theorem `isTranscendenceBasis_adjoin_iff` / 定理 `isTranscendenceBasis_adjoin_iff`

English:
theorem isTranscendenceBasis_adjoin_iff
  given: {x : ι -> S}
  proof: (Algebra.IsAlgebraic.isTranscendenceBasis_iff ..).symm

中文:
定理 isTranscendenceBasis_adjoin_iff
  条件: {x : ι -> S}
  证明: (Algebra.IsAlgebraic.isTranscendenceBasis_iff ..).symm

Depends on / 依赖: Algebra, Algebra.IsAlgebraic.isTranscendenceBasis_iff, IsAlgebraic, isTranscendenceBasis_iff
-/
theorem isTranscendenceBasis_adjoin_iff {x : ι -> S} :
    IsTranscendenceBasis (adjoin F s) x ↔ IsTranscendenceBasis (Algebra.adjoin F s) x :=
  (Algebra.IsAlgebraic.isTranscendenceBasis_iff ..).symm

end IntermediateField
