/-
Copyright (c) 2024 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu, Jiedong Jiang
-/
module

public import Mathlib.FieldTheory.Normal.Closure
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Relative Algebraic Closure

In this file we construct the relative algebraic closure of a field extension.

## Main Definitions

- `algebraicClosure F E` is the relative algebraic closure (i.e. the maximal algebraic subextension)
  of the field extension `E / F`, which is defined to be the integral closure of `F` in `E`.

-/

@[expose] public section
noncomputable section

open Polynomial FiniteDimensional IntermediateField Field

variable (F E : Type*) [Field F] [Field E] [Algebra F E]
variable {K : Type*} [Field K] [Algebra F K]

/--
The *relative algebraic closure* of a field `F` in a field extension `E`,
also called the *maximal algebraic subextension* of `E / F`,
is defined to be the subalgebra `integralClosure F E`
upgraded to an intermediate field (since `F` and `E` are both fields).
This is exactly the intermediate field of `E / F` consisting of all integral/algebraic elements.
-/
@[stacks 09GI]
/--
Definition of `algebraicClosure` / `algebraicClosure` 的定义

English:
definition algebraicClosure
  signature: : IntermediateField F E
  body: Algebra.IsAlgebraic.toIntermediateField (integralClosure F E)

中文:
定义 algebraicClosure
  签名: : 整数ermediateField F E
  定义体: Algebra.IsAlgebraic.toIntermediateField (integralClosure F E)

Depends on / 依赖: Algebra, Algebra.IsAlgebraic.toIntermediateField, IsAlgebraic, integralClosure, toIntermediateField
-/
def algebraicClosure : IntermediateField F E :=
  Algebra.IsAlgebraic.toIntermediateField (integralClosure F E)

variable {F E}

/--
theorem `algebraicClosure_toSubalgebra` / 定理 `algebraicClosure_toSubalgebra`

English:
theorem algebraicClosure_toSubalgebra
  statement: (algebraicClosure F E).toSubalgebra = integralClosure F E
  proof: rfl

中文:
定理 algebraicClosure_toSubalgebra
  结论: (algebraicClosure F E).toSubalgebra = integralClosure F E
  证明: rfl
-/
theorem algebraicClosure_toSubalgebra : (algebraicClosure F E).toSubalgebra = integralClosure F E :=
  rfl

/--
theorem `mem_algebraicClosure_iff'` / 定理 `mem_algebraicClosure_iff'`

English:
theorem mem_algebraicClosure_iff'
  given: {x : E}
  proof: Iff.rfl

中文:
定理 mem_algebraicClosure_iff'
  条件: {x : E}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_algebraicClosure_iff' {x : E} :
    x in algebraicClosure F E ↔ IsIntegral F x := Iff.rfl

/--
theorem `mem_algebraicClosure_iff` / 定理 `mem_algebraicClosure_iff`

English:
theorem mem_algebraicClosure_iff
  given: {x : E}
  proof: isAlgebraic_iff_isIntegral.symm

中文:
定理 mem_algebraicClosure_iff
  条件: {x : E}
  证明: isAlgebraic_iff_isIntegral.symm

Depends on / 依赖: isAlgebraic_iff_isIntegral, isAlgebraic_iff_isIntegral.symm
-/
theorem mem_algebraicClosure_iff {x : E} :
    x in algebraicClosure F E ↔ IsAlgebraic F x := isAlgebraic_iff_isIntegral.symm

/--
theorem `map_mem_algebraicClosure_iff` / 定理 `map_mem_algebraicClosure_iff`

English:
theorem map_mem_algebraicClosure_iff
  given: (i : E ->ₐ[F] K) {x : E}
  proof: by
  simp_rw [mem_algebraicClosure_iff', ← minpoly.ne_zero_iff, minpoly.algHom_eq i i.injective]

中文:
定理 map_mem_algebraicClosure_iff
  条件: (i : E ->ₐ[F] K) {x : E}
  证明: by
  simp_rw [mem_algebraicClosure_iff', ← minpoly.ne_zero_iff, minpoly.algHom_eq i i.injective]

Depends on / 依赖: algHom_eq, i.injective, injective, mem_algebraicClosure_iff, minpoly, minpoly.algHom_eq, minpoly.ne_zero_iff, ne_zero_iff, simp_rw
-/
theorem map_mem_algebraicClosure_iff (i : E ->ₐ[F] K) {x : E} :
    i x in algebraicClosure F K ↔ x in algebraicClosure F E := by
  simp_rw [mem_algebraicClosure_iff', ← minpoly.ne_zero_iff, minpoly.algHom_eq i i.injective]

namespace algebraicClosure

/--
theorem `comap_eq_of_algHom` / 定理 `comap_eq_of_algHom`

English:
theorem comap_eq_of_algHom
  given: (i : E ->ₐ[F] K)
  proof: by
  ext x
  exact map_mem_algebraicClosure_iff i

中文:
定理 comap_eq_of_algHom
  条件: (i : E ->ₐ[F] K)
  证明: by
  ext x
  exact map_mem_algebraicClosure_iff i

Depends on / 依赖: map_mem_algebraicClosure_iff
-/
theorem comap_eq_of_algHom (i : E ->ₐ[F] K) :
    (algebraicClosure F K).comap i = algebraicClosure F E := by
  ext x
  exact map_mem_algebraicClosure_iff i

/--
theorem `map_le_of_algHom` / 定理 `map_le_of_algHom`

English:
theorem map_le_of_algHom
  given: (i : E ->ₐ[F] K)
  proof: map_le_iff_le_comap.2 (comap_eq_of_algHom i).ge

中文:
定理 map_le_of_algHom
  条件: (i : E ->ₐ[F] K)
  证明: map_le_iff_le_comap.2 (comap_eq_of_algHom i).ge

Depends on / 依赖: comap_eq_of_algHom, map_le_iff_le_comap
-/
theorem map_le_of_algHom (i : E ->ₐ[F] K) :
    (algebraicClosure F E).map i <= algebraicClosure F K :=
  map_le_iff_le_comap.2 (comap_eq_of_algHom i).ge

variable (F) in
/--
theorem `map_eq_of_algebraicClosure_eq_bot` / 定理 `map_eq_of_algebraicClosure_eq_bot`

English:
theorem map_eq_of_algebraicClosure_eq_bot
  statement: [Algebra E K] [IsScalarTower F E K]
  proof: by
  refine le_antisymm (map_le_of_algHom _) (fun x hx => ?_)
obtain ⟨y, rfl⟩ := mem_bot.1 h ▸ mem_algebraicClosure_iff'.2
    (IsIntegral.tower_top <| mem_algebraicClosure_iff'.1 hx)
  exact ⟨y, (map_mem_algebraicClosure_iff <| IsScalarTower.toAlgHom F E K).mp hx, rfl⟩

中文:
定理 map_eq_of_algebraicClosure_eq_bot
  结论: [Algebra E K] [IsScalarTower F E K]
  证明: by
  refine le_antisymm (map_le_of_algHom _) (fun x hx => ?_)
obtain ⟨y, rfl⟩ := mem_bot.1 h ▸ mem_algebraicClosure_iff'.2
    (IsIntegral.tower_top <| mem_algebraicClosure_iff'.1 hx)
  exact ⟨y, (map_mem_algebraicClosure_iff <| IsScalarTower.toAlgHom F E K).mp hx, rfl⟩

Depends on / 依赖: IsIntegral, IsIntegral.tower_top, IsScalarTower, IsScalarTower.toAlgHom, le_antisymm, map_le_of_algHom, map_mem_algebraicClosure_iff, mem_algebraicClosure_iff, mem_bot, toAlgHom, tower_top
-/
theorem map_eq_of_algebraicClosure_eq_bot [Algebra E K] [IsScalarTower F E K]
    (h : algebraicClosure E K = ⊥) :
    (algebraicClosure F E).map (IsScalarTower.toAlgHom F E K) = algebraicClosure F K := by
  refine le_antisymm (map_le_of_algHom _) (fun x hx => ?_)
obtain ⟨y, rfl⟩ := mem_bot.1 h ▸ mem_algebraicClosure_iff'.2
    (IsIntegral.tower_top <| mem_algebraicClosure_iff'.1 hx)
  exact ⟨y, (map_mem_algebraicClosure_iff <| IsScalarTower.toAlgHom F E K).mp hx, rfl⟩

/--
theorem `map_eq_of_algEquiv` / 定理 `map_eq_of_algEquiv`

English:
theorem map_eq_of_algEquiv
  given: (i : E ≃ₐ[F] K)
  proof: (map_le_of_algHom i.toAlgHom).antisymm
    (fun x h => ⟨_, (map_mem_algebraicClosure_iff i.symm).2 h, by simp⟩)

中文:
定理 map_eq_of_algEquiv
  条件: (i : E ≃ₐ[F] K)
  证明: (map_le_of_algHom i.toAlgHom).antisymm
    (fun x h => ⟨_, (map_mem_algebraicClosure_iff i.symm).2 h, by simp⟩)

Depends on / 依赖: antisymm, i.symm, i.toAlgHom, map_le_of_algHom, map_mem_algebraicClosure_iff, toAlgHom
-/
theorem map_eq_of_algEquiv (i : E ≃ₐ[F] K) :
    (algebraicClosure F E).map i = algebraicClosure F K :=
  (map_le_of_algHom i.toAlgHom).antisymm
    (fun x h => ⟨_, (map_mem_algebraicClosure_iff i.symm).2 h, by simp⟩)

/--
Definition of `algEquivOfAlgEquiv` / `algEquivOfAlgEquiv` 的定义

English:
definition algEquivOfAlgEquiv
  signature: (i : E ≃ₐ[F] K)
  body: (intermediateFieldMap i _).trans (equivOfEq (map_eq_of_algEquiv i))

alias _root_.AlgEquiv.algebraicClosure := algEquivOfAlgEquiv

中文:
定义 algEquivOfAlgEquiv
  签名: (i : E ≃ₐ[F] K)
  定义体: (intermediateFieldMap i _).trans (equivOfEq (map_eq_of_algEquiv i))

alias _root_.AlgEquiv.algebraicClosure := algEquivOfAlgEquiv

Depends on / 依赖: equivOfEq, intermediateFieldMap, map_eq_of_algEquiv
-/
def algEquivOfAlgEquiv (i : E ≃ₐ[F] K) :
    algebraicClosure F E ≃ₐ[F] algebraicClosure F K :=
  (intermediateFieldMap i _).trans (equivOfEq (map_eq_of_algEquiv i))

alias _root_.AlgEquiv.algebraicClosure := algEquivOfAlgEquiv

variable (F E K)

/--
Instance `isAlgebraic` / 实例 `isAlgebraic`

English:
instance isAlgebraic
  signature: : Algebra.IsAlgebraic F (algebraicClosure F E)
  body: ⟨fun x => isAlgebraic_iff.mpr x.2.isAlgebraic⟩

中文:
实例 isAlgebraic
  签名: : Algebra.IsAlgebraic F (algebraicClosure F E)
  定义体: ⟨fun x => isAlgebraic_iff.mpr x.2.isAlgebraic⟩

Depends on / 依赖: isAlgebraic, isAlgebraic_iff, isAlgebraic_iff.mpr
-/
instance isAlgebraic : Algebra.IsAlgebraic F (algebraicClosure F E) :=
  ⟨fun x => isAlgebraic_iff.mpr x.2.isAlgebraic⟩

/--
Instance `isIntegralClosure` / 实例 `isIntegralClosure`

English:
instance isIntegralClosure
  signature: : IsIntegralClosure (algebraicClosure F E) F E
  body: inferInstanceAs (IsIntegralClosure (integralClosure F E) F E)

中文:
实例 isIntegralClosure
  签名: : Is整数egralClosure (algebraicClosure F E) F E
  定义体: inferInstanceAs (IsIntegralClosure (integralClosure F E) F E)

Depends on / 依赖: IsIntegralClosure, integralClosure
-/
instance isIntegralClosure : IsIntegralClosure (algebraicClosure F E) F E :=
  inferInstanceAs (IsIntegralClosure (integralClosure F E) F E)

end algebraicClosure

/--
theorem `Transcendental.algebraicClosure` / 定理 `Transcendental.algebraicClosure`

English:
theorem Transcendental.algebraicClosure
  given: {a : E} (ha : Transcendental F a)
  proof: ha.extendScalars _

中文:
定理 Transcendental.algebraicClosure
  条件: {a : E} (ha : Transcendental F a)
  证明: ha.extendScalars _
-/
protected theorem Transcendental.algebraicClosure {a : E} (ha : Transcendental F a) :
    Transcendental (algebraicClosure F E) a :=
  ha.extendScalars _

variable (F E K)

/--
theorem `le_algebraicClosure'` / 定理 `le_algebraicClosure'`

English:
theorem le_algebraicClosure'
  given: {L : IntermediateField F E} (hs : forall x : L, IsAlgebraic F x)
  proof: fun x h => by
  simpa only [mem_algebraicClosure_iff, IsAlgebraic, ne_eq, ← aeval_algebraMap_eq_zero_iff E,
    Algebra.algebraMap_self, RingHom.id_apply, IntermediateField.algebraMap_apply] using hs ⟨x, h⟩

中文:
定理 le_algebraicClosure'
  条件: {L : 整数ermediateField F E} (hs : 对任意 x : L, IsAlgebraic F x)
  证明: fun x h => by
  simpa only [mem_algebraicClosure_iff, IsAlgebraic, ne_eq, ← aeval_algebraMap_eq_zero_iff E,
    Algebra.algebraMap_self, RingHom.id_apply, IntermediateField.algebraMap_apply] using hs ⟨x, h⟩

Depends on / 依赖: Algebra, Algebra.algebraMap_self, IntermediateField, IntermediateField.algebraMap_apply, IsAlgebraic, RingHom, RingHom.id_apply, aeval_algebraMap_eq_zero_iff, algebraMap_apply, algebraMap_self, id_apply, mem_algebraicClosure_iff, ne_eq
-/
theorem le_algebraicClosure' {L : IntermediateField F E} (hs : forall x : L, IsAlgebraic F x) :
    L <= algebraicClosure F E := fun x h => by
  simpa only [mem_algebraicClosure_iff, IsAlgebraic, ne_eq, ← aeval_algebraMap_eq_zero_iff E,
    Algebra.algebraMap_self, RingHom.id_apply, IntermediateField.algebraMap_apply] using hs ⟨x, h⟩

/--
theorem `le_algebraicClosure` / 定理 `le_algebraicClosure`

English:
theorem le_algebraicClosure
  given: (L : IntermediateField F E) [Algebra.IsAlgebraic F L]
  proof: le_algebraicClosure' F E (Algebra.IsAlgebraic.isAlgebraic)

中文:
定理 le_algebraicClosure
  条件: (L : 整数ermediateField F E) [Algebra.IsAlgebraic F L]
  证明: le_algebraicClosure' F E (Algebra.IsAlgebraic.isAlgebraic)

Depends on / 依赖: Algebra, Algebra.IsAlgebraic.isAlgebraic, IsAlgebraic, isAlgebraic, le_algebraicClosure
-/
theorem le_algebraicClosure (L : IntermediateField F E) [Algebra.IsAlgebraic F L] :
    L <= algebraicClosure F E := le_algebraicClosure' F E (Algebra.IsAlgebraic.isAlgebraic)

/--
theorem `le_algebraicClosure_iff` / 定理 `le_algebraicClosure_iff`

English:
theorem le_algebraicClosure_iff
  given: (L : IntermediateField F E)
  proof: ⟨fun h => ⟨fun x => by simpa only [IsAlgebraic, ne_eq, ← aeval_algebraMap_eq_zero_iff E,
    IntermediateField.algebraMap_apply,
    Algebra.algebraMap_self, RingHomCompTriple.comp_apply, mem_algebraicClosure_iff] using h x.2⟩,
    fun _ => le_algebraicClosure _ _ _⟩

中文:
定理 le_algebraicClosure_iff
  条件: (L : 整数ermediateField F E)
  证明: ⟨fun h => ⟨fun x => by simpa only [IsAlgebraic, ne_eq, ← aeval_algebraMap_eq_zero_iff E,
    IntermediateField.algebraMap_apply,
    Algebra.algebraMap_self, RingHomCompTriple.comp_apply, mem_algebraicClosure_iff] using h x.2⟩,
    fun _ => le_algebraicClosure _ _ _⟩

Depends on / 依赖: Algebra, Algebra.algebraMap_self, IntermediateField, IntermediateField.algebraMap_apply, IsAlgebraic, RingHomCompTriple, RingHomCompTriple.comp_apply, aeval_algebraMap_eq_zero_iff, algebraMap_apply, algebraMap_self, comp_apply, le_algebraicClosure, mem_algebraicClosure_iff, ne_eq
-/
theorem le_algebraicClosure_iff (L : IntermediateField F E) :
    L <= algebraicClosure F E ↔ Algebra.IsAlgebraic F L :=
  ⟨fun h => ⟨fun x => by simpa only [IsAlgebraic, ne_eq, ← aeval_algebraMap_eq_zero_iff E,
    IntermediateField.algebraMap_apply,
    Algebra.algebraMap_self, RingHomCompTriple.comp_apply, mem_algebraicClosure_iff] using h x.2⟩,
    fun _ => le_algebraicClosure _ _ _⟩

namespace algebraicClosure

/--
theorem `algebraicClosure_eq_bot` / 定理 `algebraicClosure_eq_bot`

English:
theorem algebraicClosure_eq_bot
  proof: bot_unique fun x hx => mem_bot.2
    ⟨⟨x, isIntegral_trans x (mem_algebraicClosure_iff'.1 hx)⟩, rfl⟩

中文:
定理 algebraicClosure_eq_bot
  证明: bot_unique fun x hx => mem_bot.2
    ⟨⟨x, isIntegral_trans x (mem_algebraicClosure_iff'.1 hx)⟩, rfl⟩

Depends on / 依赖: bot_unique, isIntegral_trans, mem_algebraicClosure_iff, mem_bot
-/
theorem algebraicClosure_eq_bot :
    algebraicClosure (algebraicClosure F E) E = ⊥ :=
  bot_unique fun x hx => mem_bot.2
    ⟨⟨x, isIntegral_trans x (mem_algebraicClosure_iff'.1 hx)⟩, rfl⟩

/--
theorem `normalClosure_eq_self` / 定理 `normalClosure_eq_self`

English:
theorem normalClosure_eq_self
  proof: le_antisymm (normalClosure_le_iff.2 fun i =>
    haveI : Algebra.IsAlgebraic F i.fieldRange := (AlgEquiv.ofInjectiveField i).isAlgebraic
    le_algebraicClosure F E _) (le_normalClosure _)

中文:
定理 normalClosure_eq_self
  证明: le_antisymm (normalClosure_le_iff.2 fun i =>
    haveI : Algebra.IsAlgebraic F i.fieldRange := (AlgEquiv.ofInjectiveField i).isAlgebraic
    le_algebraicClosure F E _) (le_normalClosure _)

Depends on / 依赖: AlgEquiv, AlgEquiv.ofInjectiveField, Algebra, Algebra.IsAlgebraic, IsAlgebraic, fieldRange, i.fieldRange, isAlgebraic, le_algebraicClosure, le_antisymm, le_normalClosure, normalClosure_le_iff, ofInjectiveField
-/
theorem normalClosure_eq_self :
    normalClosure F (algebraicClosure F E) E = algebraicClosure F E :=
  le_antisymm (normalClosure_le_iff.2 fun i =>
    haveI : Algebra.IsAlgebraic F i.fieldRange := (AlgEquiv.ofInjectiveField i).isAlgebraic
    le_algebraicClosure F E _) (le_normalClosure _)

end algebraicClosure

/--
theorem `IsAlgClosed.algebraicClosure_eq_bot_iff` / 定理 `IsAlgClosed.algebraicClosure_eq_bot_iff`

English:
theorem IsAlgClosed.algebraicClosure_eq_bot_iff
  given: [IsAlgClosed E]
  proof: by
  refine ⟨fun h => IsAlgClosed.of_exists_root _ fun p hmon hirr => ?_,
    fun _ => IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic _⟩
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_aeval_eq_zero E p (degree_pos_of_irreducible hirr).ne'
  obtain ⟨x, rfl⟩ := h ▸ mem_algebraicClosure_iff'.2 (minpoly

中文:
定理 IsAlgClosed.algebraicClosure_eq_bot_iff
  条件: [IsAlgClosed E]
  证明: by
  refine ⟨fun h => IsAlgClosed.of_exists_root _ fun p hmon hirr => ?_,
    fun _ => IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic _⟩
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_aeval_eq_zero E p (degree_pos_of_irreducible hirr).ne'
  obtain ⟨x, rfl⟩ := h ▸ mem_algebraicClosure_iff'.2 (minpoly

Depends on / 依赖: Algebra, Algebra.ofId_apply, IntermediateField, IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic, IsAlgClosed, IsAlgClosed.exists_aeval_eq_zero, IsAlgClosed.of_exists_root, degree_pos_of_irreducible, eq_bot_of_isAlgClosed_of_isAlgebraic, exists_aeval_eq_zero, hmon.ne_zero, mem_algebraicClosure_iff, minpoly, minpoly.dvd, minpoly.ne_zero_iff, ne_zero, ne_zero_iff, ne_zero_of_dvd_ne_zero, ofId_apply, of_exists_root
-/
theorem IsAlgClosed.algebraicClosure_eq_bot_iff [IsAlgClosed E] :
    algebraicClosure F E = ⊥ ↔ IsAlgClosed F := by
  refine ⟨fun h => IsAlgClosed.of_exists_root _ fun p hmon hirr => ?_,
    fun _ => IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic _⟩
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_aeval_eq_zero E p (degree_pos_of_irreducible hirr).ne'
  obtain ⟨x, rfl⟩ := h ▸ mem_algebraicClosure_iff'.2 (minpoly.ne_zero_iff.1 <|
    ne_zero_of_dvd_ne_zero hmon.ne_zero (minpoly.dvd _ x hx))
  exact ⟨x, by simpa [Algebra.ofId_apply] using hx⟩

/--
theorem `IntermediateField.isAlgebraic_adjoin_iff_isAlgebraic` / 定理 `IntermediateField.isAlgebraic_adjoin_iff_isAlgebraic`

English:
theorem IntermediateField.isAlgebraic_adjoin_iff_isAlgebraic
  given: {S : Set E}
  proof: ((le_algebraicClosure_iff F E _).symm.trans (adjoin_le_iff.trans <| forall_congr' <|
    fun _ => Iff.imp Iff.rfl mem_algebraicClosure_iff))

中文:
定理 IntermediateField.isAlgebraic_adjoin_iff_isAlgebraic
  条件: {S : Set E}
  证明: ((le_algebraicClosure_iff F E _).symm.trans (adjoin_le_iff.trans <| forall_congr' <|
    fun _ => Iff.imp Iff.rfl mem_algebraicClosure_iff))

Depends on / 依赖: Iff.imp, Iff.rfl, adjoin_le_iff, adjoin_le_iff.trans, forall_congr, le_algebraicClosure_iff, mem_algebraicClosure_iff, symm.trans
-/
theorem IntermediateField.isAlgebraic_adjoin_iff_isAlgebraic {S : Set E} :
    Algebra.IsAlgebraic F (adjoin F S) ↔ forall x in S, IsAlgebraic F x :=
  ((le_algebraicClosure_iff F E _).symm.trans (adjoin_le_iff.trans <| forall_congr' <|
    fun _ => Iff.imp Iff.rfl mem_algebraicClosure_iff))

namespace algebraicClosure

/--
Instance `isAlgClosure` / 实例 `isAlgClosure`

English:
instance isAlgClosure
  signature: [IsAlgClosed E]
  body: ⟨(IsAlgClosed.algebraicClosure_eq_bot_iff _ E).mp (algebraicClosure_eq_bot F E),
    isAlgebraic F E⟩

中文:
实例 isAlgClosure
  签名: [IsAlgClosed E]
  定义体: ⟨(IsAlgClosed.algebraicClosure_eq_bot_iff _ E).mp (algebraicClosure_eq_bot F E),
    isAlgebraic F E⟩

Depends on / 依赖: IsAlgClosed, IsAlgClosed.algebraicClosure_eq_bot_iff, algebraicClosure_eq_bot, algebraicClosure_eq_bot_iff, isAlgebraic
-/
instance isAlgClosure [IsAlgClosed E] : IsAlgClosure F (algebraicClosure F E) :=
  ⟨(IsAlgClosed.algebraicClosure_eq_bot_iff _ E).mp (algebraicClosure_eq_bot F E),
    isAlgebraic F E⟩

/--
theorem `eq_top_iff` / 定理 `eq_top_iff`

English:
theorem eq_top_iff
  statement: algebraicClosure F E = ⊤ ↔ Algebra.IsAlgebraic F E
  proof: ⟨fun h => ⟨fun _ => mem_algebraicClosure_iff.1 (h ▸ mem_top)⟩,
    fun _ => top_unique fun x _ => mem_algebraicClosure_iff.2 (Algebra.IsAlgebraic.isAlgebraic x)⟩

中文:
定理 eq_top_iff
  结论: algebraicClosure F E = ⊤ ↔ Algebra.IsAlgebraic F E
  证明: ⟨fun h => ⟨fun _ => mem_algebraicClosure_iff.1 (h ▸ mem_top)⟩,
    fun _ => top_unique fun x _ => mem_algebraicClosure_iff.2 (Algebra.IsAlgebraic.isAlgebraic x)⟩

Depends on / 依赖: Algebra, Algebra.IsAlgebraic.isAlgebraic, IsAlgebraic, isAlgebraic, mem_algebraicClosure_iff, mem_top, top_unique
-/
theorem eq_top_iff : algebraicClosure F E = ⊤ ↔ Algebra.IsAlgebraic F E :=
  ⟨fun h => ⟨fun _ => mem_algebraicClosure_iff.1 (h ▸ mem_top)⟩,
    fun _ => top_unique fun x _ => mem_algebraicClosure_iff.2 (Algebra.IsAlgebraic.isAlgebraic x)⟩

/--
theorem `le_restrictScalars` / 定理 `le_restrictScalars`

English:
theorem le_restrictScalars
  given: [Algebra E K] [IsScalarTower F E K]
  proof: fun _ h => mem_algebraicClosure_iff.2 IsAlgebraic.tower_top E (mem_algebraicClosure_iff.1 h)

中文:
定理 le_restrictScalars
  条件: [Algebra E K] [IsScalarTower F E K]
  证明: fun _ h => mem_algebraicClosure_iff.2 IsAlgebraic.tower_top E (mem_algebraicClosure_iff.1 h)

Depends on / 依赖: IsAlgebraic, IsAlgebraic.tower_top, mem_algebraicClosure_iff, tower_top
-/
theorem le_restrictScalars [Algebra E K] [IsScalarTower F E K] :
    algebraicClosure F K <= (algebraicClosure E K).restrictScalars F :=
fun _ h => mem_algebraicClosure_iff.2 IsAlgebraic.tower_top E (mem_algebraicClosure_iff.1 h)

/--
theorem `eq_restrictScalars_of_isAlgebraic` / 定理 `eq_restrictScalars_of_isAlgebraic`

English:
theorem eq_restrictScalars_of_isAlgebraic
  statement: [Algebra E K] [IsScalarTower F E K]
  proof: (algebraicClosure.le_restrictScalars F E K).antisymm fun _ h =>
    isIntegral_trans _ h

中文:
定理 eq_restrictScalars_of_isAlgebraic
  结论: [Algebra E K] [IsScalarTower F E K]
  证明: (algebraicClosure.le_restrictScalars F E K).antisymm fun _ h =>
    isIntegral_trans _ h

Depends on / 依赖: algebraicClosure, algebraicClosure.le_restrictScalars, antisymm, isIntegral_trans, le_restrictScalars
-/
theorem eq_restrictScalars_of_isAlgebraic [Algebra E K] [IsScalarTower F E K]
    [Algebra.IsAlgebraic F E] : algebraicClosure F K = (algebraicClosure E K).restrictScalars F :=
  (algebraicClosure.le_restrictScalars F E K).antisymm fun _ h =>
    isIntegral_trans _ h

/--
theorem `adjoin_le` / 定理 `adjoin_le`

English:
theorem adjoin_le
  given: [Algebra E K] [IsScalarTower F E K]
  proof: adjoin_le_iff.2 le_restrictScalars F E K

中文:
定理 adjoin_le
  条件: [Algebra E K] [IsScalarTower F E K]
  证明: adjoin_le_iff.2 le_restrictScalars F E K

Depends on / 依赖: adjoin_le_iff, le_restrictScalars
-/
theorem adjoin_le [Algebra E K] [IsScalarTower F E K] :
    adjoin E (algebraicClosure F K) <= algebraicClosure E K :=
adjoin_le_iff.2 le_restrictScalars F E K

end algebraicClosure

variable {F}
/--
theorem `Splits.algebraicClosure` / 定理 `Splits.algebraicClosure`

English:
theorem Splits.algebraicClosure
  given: {p : F[X]} (h : (p.map (algebraMap F E)).Splits)
  proof: splits_of_splits h fun _ hx => (isAlgebraic_of_mem_rootSet hx).isIntegral

中文:
定理 Splits.algebraicClosure
  条件: {p : F[X]} (h : (p.map (algebraMap F E)).Splits)
  证明: splits_of_splits h fun _ hx => (isAlgebraic_of_mem_rootSet hx).isIntegral

Depends on / 依赖: isAlgebraic_of_mem_rootSet, isIntegral, splits_of_splits
-/
theorem Splits.algebraicClosure {p : F[X]} (h : (p.map (algebraMap F E)).Splits) :
    (p.map (algebraMap F (algebraicClosure F E))).Splits :=
  splits_of_splits h fun _ hx => (isAlgebraic_of_mem_rootSet hx).isIntegral
