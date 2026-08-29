/-
Copyright (c) 2023 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.FieldTheory.SeparableDegree
public import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure

/-!

# Separable closure

This file contains basics about the (relative) separable closure of a field extension.

## Main definitions

- `separableClosure`: the relative separable closure of `F` in `E`, or called maximal separable
  subextension of `E / F`, is defined to be the intermediate field of `E / F` consisting of all
  separable elements.

- `SeparableClosure`: the absolute separable closure, defined to be the relative separable
  closure inside the algebraic closure.

- `Field.sepDegree F E`: the (infinite) separable degree $[E:F]_s$ of an algebraic extension
  `E / F` of fields, defined to be the degree of `separableClosure F E / F`. Later we will show
  that (`Field.finSepDegree_eq`, not in this file), if `Field.Emb F E` is finite, then this
  coincides with `Field.finSepDegree F E`.

- `Field.insepDegree F E`: the (infinite) inseparable degree $[E:F]_i$ of an algebraic extension
  `E / F` of fields, defined to be the degree of `E / separableClosure F E`.

- `Field.finInsepDegree F E`: the finite inseparable degree $[E:F]_i$ of an algebraic extension
  `E / F` of fields, defined to be the degree of `E / separableClosure F E` as a natural number.
  It is zero if such field extension is not finite.

## Main results

- `le_separableClosure_iff`: an intermediate field of `E / F` is contained in the
  separable closure of `F` in `E` if and only if it is separable over `F`.

- `separableClosure.normalClosure_eq_self`: the normal closure of the separable
  closure of `F` in `E` is equal to itself.

- `separableClosure.isGalois`: the separable closure in a normal extension is Galois
  (namely, normal and separable).

- `separableClosure.isSepClosure`: the separable closure in a separably closed extension
  is a separable closure of the base field.

- `IntermediateField.isSeparable_adjoin_iff_isSeparable`: `F(S) / F` is a separable extension if and
  only if all elements of `S` are separable elements.

- `separableClosure.eq_top_iff`: the separable closure of `F` in `E` is equal to `E`
  if and only if `E / F` is separable.

## Tags

separable degree, degree, separable closure

-/

@[expose] public section

assert_not_exists IsGalois

open Module Polynomial IntermediateField Field

noncomputable section

universe u v w

variable (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]
variable (K : Type w) [Field K] [Algebra F K]

section separableClosure

/-- The (relative) separable closure of `F` in `E`, or called maximal separable subextension
of `E / F`, is defined to be the intermediate field of `E / F` consisting of all separable
elements. The previous results prove that these elements are closed under field operations. -/
@[stacks 09HC]
/--
Definition of `separableClosure` / `separableClosure` 的定义

English:
definition separableClosure
  signature: : IntermediateField F E where
  body: {x | IsSeparable F x}
  mul_mem' := isSeparable_mul
  add_mem' := isSeparable_add
  algebraMap_mem' := isSeparable_algebraMap
  inv_mem' _ := isSeparable_inv

中文:
定义 separableClosure
  签名: : 中间域 F E where
  定义体: {x | IsSeparable F x}
  mul_mem' := isSeparable_mul
  add_mem' := isSeparable_add
  algebraMap_mem' := isSeparable_algebraMap
  inv_mem' _ := isSeparable_inv

Depends on / 依赖: IsSeparable
-/
def separableClosure : IntermediateField F E where
  carrier := {x | IsSeparable F x}
  mul_mem' := isSeparable_mul
  add_mem' := isSeparable_add
  algebraMap_mem' := isSeparable_algebraMap
  inv_mem' _ := isSeparable_inv

variable {F E K}

/--
theorem `mem_separableClosure_iff` / 定理 `mem_separableClosure_iff`

English:
theorem mem_separableClosure_iff
  given: {x : E}
  proof: Iff.rfl

中文:
定理 mem_separableClosure_iff
  条件: {x : E}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_separableClosure_iff {x : E} :
    x in separableClosure F E ↔ IsSeparable F x := Iff.rfl

/--
theorem `map_mem_separableClosure_iff` / 定理 `map_mem_separableClosure_iff`

English:
theorem map_mem_separableClosure_iff
  given: (i : E ->ₐ[F] K) {x : E}
  proof: by
  simp_rw [mem_separableClosure_iff, IsSeparable, minpoly.algHom_eq i i.injective]

中文:
定理 map_mem_separableClosure_iff
  条件: (i : E ->ₐ[F] K) {x : E}
  证明: by
  simp_rw [mem_separableClosure_iff, IsSeparable, minpoly.algHom_eq i i.injective]

Depends on / 依赖: IsSeparable, algHom_eq, i.injective, injective, mem_separableClosure_iff, minpoly, minpoly.algHom_eq, simp_rw
-/
theorem map_mem_separableClosure_iff (i : E ->ₐ[F] K) {x : E} :
    i x in separableClosure F K ↔ x in separableClosure F E := by
  simp_rw [mem_separableClosure_iff, IsSeparable, minpoly.algHom_eq i i.injective]

/--
theorem `separableClosure.comap_eq_of_algHom` / 定理 `separableClosure.comap_eq_of_algHom`

English:
theorem separableClosure.comap_eq_of_algHom
  given: (i : E ->ₐ[F] K)
  proof: by
  ext x
  exact map_mem_separableClosure_iff i

中文:
定理 separableClosure.comap_eq_of_algHom
  条件: (i : E ->ₐ[F] K)
  证明: by
  ext x
  exact map_mem_separableClosure_iff i

Depends on / 依赖: map_mem_separableClosure_iff
-/
theorem separableClosure.comap_eq_of_algHom (i : E ->ₐ[F] K) :
    (separableClosure F K).comap i = separableClosure F E := by
  ext x
  exact map_mem_separableClosure_iff i

/--
theorem `separableClosure.map_le_of_algHom` / 定理 `separableClosure.map_le_of_algHom`

English:
theorem separableClosure.map_le_of_algHom
  given: (i : E ->ₐ[F] K)
  proof: map_le_iff_le_comap.2 (comap_eq_of_algHom i).ge

中文:
定理 separableClosure.map_le_of_algHom
  条件: (i : E ->ₐ[F] K)
  证明: map_le_iff_le_comap.2 (comap_eq_of_algHom i).ge

Depends on / 依赖: comap_eq_of_algHom, map_le_iff_le_comap
-/
theorem separableClosure.map_le_of_algHom (i : E ->ₐ[F] K) :
    (separableClosure F E).map i <= separableClosure F K :=
  map_le_iff_le_comap.2 (comap_eq_of_algHom i).ge

variable (F) in
/--
theorem `separableClosure.map_eq_of_separableClosure_eq_bot` / 定理 `separableClosure.map_eq_of_separableClosure_eq_bot`

English:
theorem separableClosure.map_eq_of_separableClosure_eq_bot
  statement: [Algebra E K] [IsScalarTower F E K]
  proof: by
  refine le_antisymm (map_le_of_algHom _) (fun x hx => ?_)
obtain ⟨y, rfl⟩ := mem_bot.1 h ▸ mem_separableClosure_iff.2
    (IsSeparable.tower_top E <| mem_separableClosure_iff.1 hx)
  exact ⟨y, (map_mem_separableClosure_iff <| IsScalarTower.toAlgHom F E K).mp hx, rfl⟩

中文:
定理 separableClosure.map_eq_of_separableClosure_eq_bot
  结论: [代数 E K] [标量塔 F E K]
  证明: by
  refine le_antisymm (map_le_of_algHom _) (fun x hx => ?_)
obtain ⟨y, rfl⟩ := mem_bot.1 h ▸ mem_separableClosure_iff.2
    (IsSeparable.tower_top E <| mem_separableClosure_iff.1 hx)
  exact ⟨y, (map_mem_separableClosure_iff <| IsScalarTower.toAlgHom F E K).mp hx, rfl⟩

Depends on / 依赖: IsScalarTower, IsScalarTower.toAlgHom, IsSeparable, IsSeparable.tower_top, le_antisymm, map_le_of_algHom, map_mem_separableClosure_iff, mem_bot, mem_separableClosure_iff, toAlgHom, tower_top
-/
theorem separableClosure.map_eq_of_separableClosure_eq_bot [Algebra E K] [IsScalarTower F E K]
    (h : separableClosure E K = ⊥) :
    (separableClosure F E).map (IsScalarTower.toAlgHom F E K) = separableClosure F K := by
  refine le_antisymm (map_le_of_algHom _) (fun x hx => ?_)
obtain ⟨y, rfl⟩ := mem_bot.1 h ▸ mem_separableClosure_iff.2
    (IsSeparable.tower_top E <| mem_separableClosure_iff.1 hx)
  exact ⟨y, (map_mem_separableClosure_iff <| IsScalarTower.toAlgHom F E K).mp hx, rfl⟩

/--
theorem `separableClosure.map_eq_of_algEquiv` / 定理 `separableClosure.map_eq_of_algEquiv`

English:
theorem separableClosure.map_eq_of_algEquiv
  given: (i : E ≃ₐ[F] K)
  proof: (map_le_of_algHom i.toAlgHom).antisymm
    (fun x h => ⟨_, (map_mem_separableClosure_iff i.symm).2 h, by simp⟩)

中文:
定理 separableClosure.map_eq_of_algEquiv
  条件: (i : E ≃ₐ[F] K)
  证明: (map_le_of_algHom i.toAlgHom).antisymm
    (fun x h => ⟨_, (map_mem_separableClosure_iff i.symm).2 h, by simp⟩)

Depends on / 依赖: antisymm, i.symm, i.toAlgHom, map_le_of_algHom, map_mem_separableClosure_iff, toAlgHom
-/
theorem separableClosure.map_eq_of_algEquiv (i : E ≃ₐ[F] K) :
    (separableClosure F E).map i = separableClosure F K :=
  (map_le_of_algHom i.toAlgHom).antisymm
    (fun x h => ⟨_, (map_mem_separableClosure_iff i.symm).2 h, by simp⟩)

/--
Definition of `separableClosure.algEquivOfAlgEquiv` / `separableClosure.algEquivOfAlgEquiv` 的定义

English:
definition separableClosure.algEquivOfAlgEquiv
  signature: (i : E ≃ₐ[F] K)
  body: (intermediateFieldMap i _).trans (equivOfEq (map_eq_of_algEquiv i))

alias AlgEquiv.separableClosure := separableClosure.algEquivOfAlgEquiv

中文:
定义 separableClosure.algEquivOfAlgEquiv
  签名: (i : E ≃ₐ[F] K)
  定义体: (intermediateFieldMap i _).trans (equivOfEq (map_eq_of_algEquiv i))

alias AlgEquiv.separableClosure := separableClosure.algEquivOfAlgEquiv

Depends on / 依赖: equivOfEq, intermediateFieldMap, map_eq_of_algEquiv
-/
def separableClosure.algEquivOfAlgEquiv (i : E ≃ₐ[F] K) :
    separableClosure F E ≃ₐ[F] separableClosure F K :=
  (intermediateFieldMap i _).trans (equivOfEq (map_eq_of_algEquiv i))

alias AlgEquiv.separableClosure := separableClosure.algEquivOfAlgEquiv

variable (F E K)

/--
Instance `separableClosure.isAlgebraic` / 实例 `separableClosure.isAlgebraic`

English:
instance separableClosure.isAlgebraic
  signature: : Algebra.IsAlgebraic F (separableClosure F E)
  body: ⟨fun x => isAlgebraic_iff.2 (IsSeparable.isIntegral x.2).isAlgebraic⟩

中文:
实例 separableClosure.isAlgebraic
  签名: : 代数.是代数 F (separableClosure F E)
  定义体: ⟨fun x => isAlgebraic_iff.2 (IsSeparable.isIntegral x.2).isAlgebraic⟩

Depends on / 依赖: IsSeparable, IsSeparable.isIntegral, isAlgebraic, isAlgebraic_iff, isIntegral
-/
instance separableClosure.isAlgebraic : Algebra.IsAlgebraic F (separableClosure F E) :=
  ⟨fun x => isAlgebraic_iff.2 (IsSeparable.isIntegral x.2).isAlgebraic⟩

/-- The separable closure of `F` in `E` is separable over `F`. -/
@[stacks 030K "$E_{sep}/F$ is separable"]
/--
Instance `separableClosure.isSeparable` / 实例 `separableClosure.isSeparable`

English:
instance separableClosure.isSeparable
  signature: : Algebra.IsSeparable F (separableClosure F E)
  body: ⟨fun x => by simpa only [IsSeparable, minpoly_eq] using! x.2⟩

中文:
实例 separableClosure.isSeparable
  签名: : 代数.是可分 F (separableClosure F E)
  定义体: ⟨fun x => by simpa only [IsSeparable, minpoly_eq] using! x.2⟩

Depends on / 依赖: IsSeparable, minpoly_eq
-/
instance separableClosure.isSeparable : Algebra.IsSeparable F (separableClosure F E) :=
  ⟨fun x => by simpa only [IsSeparable, minpoly_eq] using! x.2⟩

/--
theorem `le_separableClosure'` / 定理 `le_separableClosure'`

English:
theorem le_separableClosure'
  given: {L : IntermediateField F E} (hs : forall x : L, IsSeparable F x)
  proof: fun x h => by simpa only [IsSeparable, minpoly_eq] using! hs ⟨x, h⟩

中文:
定理 le_separableClosure'
  条件: {L : 中间域 F E} (hs : 对任意 x : L, 是可分 F x)
  证明: fun x h => by simpa only [IsSeparable, minpoly_eq] using! hs ⟨x, h⟩

Depends on / 依赖: IsSeparable, minpoly_eq
-/
theorem le_separableClosure' {L : IntermediateField F E} (hs : forall x : L, IsSeparable F x) :
    L <= separableClosure F E := fun x h => by simpa only [IsSeparable, minpoly_eq] using! hs ⟨x, h⟩

/--
theorem `le_separableClosure` / 定理 `le_separableClosure`

English:
theorem le_separableClosure
  given: (L : IntermediateField F E) [Algebra.IsSeparable F L]
  proof: le_separableClosure' F E (Algebra.IsSeparable.isSeparable F)

中文:
定理 le_separableClosure
  条件: (L : 中间域 F E) [代数.是可分 F L]
  证明: le_separableClosure' F E (Algebra.IsSeparable.isSeparable F)

Depends on / 依赖: Algebra, Algebra.IsSeparable.isSeparable, IsSeparable, isSeparable, le_separableClosure
-/
theorem le_separableClosure (L : IntermediateField F E) [Algebra.IsSeparable F L] :
    L <= separableClosure F E := le_separableClosure' F E (Algebra.IsSeparable.isSeparable F)

/--
theorem `le_separableClosure_iff` / 定理 `le_separableClosure_iff`

English:
theorem le_separableClosure_iff
  given: (L : IntermediateField F E)
  proof: Subalgebra.isSeparable_iff.symm

中文:
定理 le_separableClosure_iff
  条件: (L : 中间域 F E)
  证明: Subalgebra.isSeparable_iff.symm

Depends on / 依赖: Subalgebra, Subalgebra.isSeparable_iff.symm, isSeparable_iff
-/
theorem le_separableClosure_iff (L : IntermediateField F E) :
    L <= separableClosure F E ↔ Algebra.IsSeparable F L :=
  Subalgebra.isSeparable_iff.symm

/--
theorem `separableClosure.separableClosure_eq_bot` / 定理 `separableClosure.separableClosure_eq_bot`

English:
theorem separableClosure.separableClosure_eq_bot
  proof: bot_unique fun x hx => mem_bot.2
    ⟨⟨x, IsSeparable.of_algebra_isSeparable_of_isSeparable F (mem_separableClosure_iff.1 hx)⟩, rfl⟩

中文:
定理 separableClosure.separableClosure_eq_bot
  证明: bot_unique fun x hx => mem_bot.2
    ⟨⟨x, IsSeparable.of_algebra_isSeparable_of_isSeparable F (mem_separableClosure_iff.1 hx)⟩, rfl⟩

Depends on / 依赖: IsSeparable, IsSeparable.of_algebra_isSeparable_of_isSeparable, bot_unique, mem_bot, mem_separableClosure_iff, of_algebra_isSeparable_of_isSeparable
-/
theorem separableClosure.separableClosure_eq_bot :
    separableClosure (separableClosure F E) E = ⊥ :=
  bot_unique fun x hx => mem_bot.2
    ⟨⟨x, IsSeparable.of_algebra_isSeparable_of_isSeparable F (mem_separableClosure_iff.1 hx)⟩, rfl⟩

/--
theorem `separableClosure.normalClosure_eq_self` / 定理 `separableClosure.normalClosure_eq_self`

English:
theorem separableClosure.normalClosure_eq_self
  proof: le_antisymm (normalClosure_le_iff.2 fun i =>
    have : Algebra.IsSeparable F i.fieldRange :=
      (AlgEquiv.Algebra.isSeparable (AlgEquiv.ofInjectiveField i))
    le_separableClosure F E _) (le_normalClosure _)

中文:
定理 separableClosure.normalClosure_eq_self
  证明: le_antisymm (normalClosure_le_iff.2 fun i =>
    have : Algebra.IsSeparable F i.fieldRange :=
      (AlgEquiv.Algebra.isSeparable (AlgEquiv.ofInjectiveField i))
    le_separableClosure F E _) (le_normalClosure _)

Depends on / 依赖: AlgEquiv, AlgEquiv.Algebra.isSeparable, AlgEquiv.ofInjectiveField, Algebra, Algebra.IsSeparable, IsSeparable, fieldRange, i.fieldRange, isSeparable, le_antisymm, le_normalClosure, le_separableClosure, normalClosure_le_iff, ofInjectiveField
-/
theorem separableClosure.normalClosure_eq_self :
    normalClosure F (separableClosure F E) E = separableClosure F E :=
  le_antisymm (normalClosure_le_iff.2 fun i =>
    have : Algebra.IsSeparable F i.fieldRange :=
      (AlgEquiv.Algebra.isSeparable (AlgEquiv.ofInjectiveField i))
    le_separableClosure F E _) (le_normalClosure _)

/--
theorem `IntermediateField.isSeparable_adjoin_iff_isSeparable` / 定理 `IntermediateField.isSeparable_adjoin_iff_isSeparable`

English:
theorem IntermediateField.isSeparable_adjoin_iff_isSeparable
  given: {S : Set E}
  proof: (le_separableClosure_iff F E _).symm.trans adjoin_le_iff

中文:
定理 中间域.isSeparable_adjoin_iff_isSeparable
  条件: {S : 集合 E}
  证明: (le_separableClosure_iff F E _).symm.trans adjoin_le_iff

Depends on / 依赖: adjoin_le_iff, le_separableClosure_iff, symm.trans
-/
theorem IntermediateField.isSeparable_adjoin_iff_isSeparable {S : Set E} :
    Algebra.IsSeparable F (adjoin F S) ↔ forall x in S, IsSeparable F x :=
  (le_separableClosure_iff F E _).symm.trans adjoin_le_iff

/--
theorem `Algebra.isSeparable_of_separable_splitting_field` / 定理 `Algebra.isSeparable_of_separable_splitting_field`

English:
theorem Algebra.isSeparable_of_separable_splitting_field
  statement: {p : F[X]}
  proof: by
  rw [← isSeparable_top]; rw [← (isSplittingField_iff_intermediateField.mp sp).2]; rw [isSeparable_adjoin_iff_isSeparable]
  exact fun x hx => hp.of_dvd (minpoly.dvd F x (aeval_eq_zero_of_mem_rootSet hx))

中文:
定理 代数.isSeparable_of_separable_splitting_field
  结论: {p : F[X]}
  证明: by
  rw [← isSeparable_top]; rw [← (isSplittingField_iff_intermediateField.mp sp).2]; rw [isSeparable_adjoin_iff_isSeparable]
  exact fun x hx => hp.of_dvd (minpoly.dvd F x (aeval_eq_zero_of_mem_rootSet hx))

Depends on / 依赖: aeval_eq_zero_of_mem_rootSet, hp.of_dvd, isSeparable_adjoin_iff_isSeparable, isSeparable_top, isSplittingField_iff_intermediateField, isSplittingField_iff_intermediateField.mp, minpoly, minpoly.dvd, of_dvd
-/
theorem Algebra.isSeparable_of_separable_splitting_field {p : F[X]}
    [sp : p.IsSplittingField F E] (hp : p.Separable) : Algebra.IsSeparable F E := by
  rw [← isSeparable_top]; rw [← (isSplittingField_iff_intermediateField.mp sp).2]; rw [isSeparable_adjoin_iff_isSeparable]
  exact fun x hx => hp.of_dvd (minpoly.dvd F x (aeval_eq_zero_of_mem_rootSet hx))

/--
theorem `separableClosure.eq_top_iff` / 定理 `separableClosure.eq_top_iff`

English:
theorem separableClosure.eq_top_iff
  statement: separableClosure F E = ⊤ ↔ Algebra.IsSeparable F E
  proof: ⟨fun h => ⟨fun _ => mem_separableClosure_iff.1 (h ▸ mem_top)⟩,
    fun _ => top_unique fun x _ => mem_separableClosure_iff.2 (Algebra.IsSeparable.isSeparable _ x)⟩

中文:
定理 separableClosure.eq_top_iff
  结论: separableClosure F E = ⊤ ↔ 代数.是可分 F E
  证明: ⟨fun h => ⟨fun _ => mem_separableClosure_iff.1 (h ▸ mem_top)⟩,
    fun _ => top_unique fun x _ => mem_separableClosure_iff.2 (Algebra.IsSeparable.isSeparable _ x)⟩

Depends on / 依赖: Algebra, Algebra.IsSeparable.isSeparable, IsSeparable, isSeparable, mem_separableClosure_iff, mem_top, top_unique
-/
theorem separableClosure.eq_top_iff : separableClosure F E = ⊤ ↔ Algebra.IsSeparable F E :=
  ⟨fun h => ⟨fun _ => mem_separableClosure_iff.1 (h ▸ mem_top)⟩,
    fun _ => top_unique fun x _ => mem_separableClosure_iff.2 (Algebra.IsSeparable.isSeparable _ x)⟩

/--
theorem `separableClosure.le_restrictScalars` / 定理 `separableClosure.le_restrictScalars`

English:
theorem separableClosure.le_restrictScalars
  given: [Algebra E K] [IsScalarTower F E K]
  proof: fun _ => IsSeparable.tower_top E

中文:
定理 separableClosure.le_restrictScalars
  条件: [代数 E K] [标量塔 F E K]
  证明: fun _ => IsSeparable.tower_top E

Depends on / 依赖: IsSeparable, IsSeparable.tower_top, tower_top
-/
theorem separableClosure.le_restrictScalars [Algebra E K] [IsScalarTower F E K] :
    separableClosure F K <= (separableClosure E K).restrictScalars F :=
  fun _ => IsSeparable.tower_top E

/--
theorem `separableClosure.eq_restrictScalars_of_isSeparable` / 定理 `separableClosure.eq_restrictScalars_of_isSeparable`

English:
theorem separableClosure.eq_restrictScalars_of_isSeparable
  statement: [Algebra E K] [IsScalarTower F E K]
  proof: (separableClosure.le_restrictScalars F E K).antisymm fun _ h =>
    IsSeparable.of_algebra_isSeparable_of_isSeparable F h

中文:
定理 separableClosure.eq_restrictScalars_of_isSeparable
  结论: [代数 E K] [标量塔 F E K]
  证明: (separableClosure.le_restrictScalars F E K).antisymm fun _ h =>
    IsSeparable.of_algebra_isSeparable_of_isSeparable F h

Depends on / 依赖: IsSeparable, IsSeparable.of_algebra_isSeparable_of_isSeparable, antisymm, le_restrictScalars, of_algebra_isSeparable_of_isSeparable, separableClosure, separableClosure.le_restrictScalars
-/
theorem separableClosure.eq_restrictScalars_of_isSeparable [Algebra E K] [IsScalarTower F E K]
    [Algebra.IsSeparable F E] : separableClosure F K = (separableClosure E K).restrictScalars F :=
  (separableClosure.le_restrictScalars F E K).antisymm fun _ h =>
    IsSeparable.of_algebra_isSeparable_of_isSeparable F h

/--
theorem `separableClosure.adjoin_le` / 定理 `separableClosure.adjoin_le`

English:
theorem separableClosure.adjoin_le
  given: [Algebra E K] [IsScalarTower F E K]
  proof: adjoin_le_iff.2 le_restrictScalars F E K

中文:
定理 separableClosure.adjoin_le
  条件: [代数 E K] [标量塔 F E K]
  证明: adjoin_le_iff.2 le_restrictScalars F E K

Depends on / 依赖: adjoin_le_iff, le_restrictScalars
-/
theorem separableClosure.adjoin_le [Algebra E K] [IsScalarTower F E K] :
    adjoin E (separableClosure F K) <= separableClosure E K :=
adjoin_le_iff.2 le_restrictScalars F E K

/--
Instance `IntermediateField.isSeparable_sup` / 实例 `IntermediateField.isSeparable_sup`

English:
instance IntermediateField.isSeparable_sup
  signature: (L1 L2 : IntermediateField F E)
  body: by
  rw [← le_separableClosure_iff] at h1 h2 ⊢
  exact sup_le h1 h2

中文:
实例 中间域.isSeparable_sup
  签名: (L1 L2 : 中间域 F E)
  定义体: by
  rw [← le_separableClosure_iff] at h1 h2 ⊢
  exact sup_le h1 h2

Depends on / 依赖: le_separableClosure_iff, sup_le
-/
instance IntermediateField.isSeparable_sup (L1 L2 : IntermediateField F E)
    [h1 : Algebra.IsSeparable F L1] [h2 : Algebra.IsSeparable F L2] :
    Algebra.IsSeparable F (L1 ⊔ L2 : IntermediateField F E) := by
  rw [← le_separableClosure_iff] at h1 h2 ⊢
  exact sup_le h1 h2

/--
Instance `IntermediateField.isSeparable_iSup` / 实例 `IntermediateField.isSeparable_iSup`

English:
instance IntermediateField.isSeparable_iSup
  signature: {ι : Type*} {t : ι -> IntermediateField F E}
  body: by
  simp_rw [← le_separableClosure_iff] at h ⊢
  exact iSup_le h

中文:
实例 中间域.isSeparable_iSup
  签名: {ι : 类型} {t : ι -> 中间域 F E}
  定义体: by
  simp_rw [← le_separableClosure_iff] at h ⊢
  exact iSup_le h

Depends on / 依赖: iSup_le, le_separableClosure_iff, simp_rw
-/
instance IntermediateField.isSeparable_iSup {ι : Type*} {t : ι -> IntermediateField F E}
    [h : forall i, Algebra.IsSeparable F (t i)] :
    Algebra.IsSeparable F (⨆ i, t i : IntermediateField F E) := by
  simp_rw [← le_separableClosure_iff] at h ⊢
  exact iSup_le h

variable {F E} in
/--
theorem `le_restrictScalars_separableClosure` / 定理 `le_restrictScalars_separableClosure`

English:
theorem le_restrictScalars_separableClosure
  given: (L : IntermediateField F E)
  proof: fun x hx => isSeparable_algebraMap (F := L) ⟨x, hx⟩

中文:
定理 le_restrictScalars_separableClosure
  条件: (L : 中间域 F E)
  证明: fun x hx => isSeparable_algebraMap (F := L) ⟨x, hx⟩

Depends on / 依赖: isSeparable_algebraMap
-/
theorem le_restrictScalars_separableClosure (L : IntermediateField F E) :
    L <= (separableClosure L E).restrictScalars F :=
  fun x hx => isSeparable_algebraMap (F := L) ⟨x, hx⟩

/--
Definition of `separableClosureOperator` / `separableClosureOperator` 的定义

English:
abbreviation separableClosureOperator
  signature: : ClosureOperator (IntermediateField F E)
  body: by
  refine .mk' (fun K => (separableClosure K E).restrictScalars F) (fun K L le x hx => ?_)
    le_restrictScalars_separableClosure fun K x hx => ?_
  · let _ := (inclusion le).toAlgebra
    have : IsScalarTower K L E := .of_algebraMap_eq' rfl
    exact hx.tower_top _
  · obtain ⟨x, rfl⟩ := (separa

中文:
缩写 separableClosureOperator
  签名: : 闭包算子 (中间域 F E)
  定义体: by
  refine .mk' (fun K => (separableClosure K E).restrictScalars F) (fun K L le x hx => ?_)
    le_restrictScalars_separableClosure fun K x hx => ?_
  · let _ := (inclusion le).toAlgebra
    have : IsScalarTower K L E := .of_algebraMap_eq' rfl
    exact hx.tower_top _
  · obtain ⟨x, rfl⟩ := (separa

Depends on / 依赖: IsScalarTower, hx.tower_top, inclusion, le_restrictScalars_separableClosure, of_algebraMap_eq, restrictScalars, separableClosure, separableClosure.separableClosure_eq_bot, separableClosure_eq_bot, toAlgebra, tower_top
-/
abbrev separableClosureOperator : ClosureOperator (IntermediateField F E) := by
  refine .mk' (fun K => (separableClosure K E).restrictScalars F) (fun K L le x hx => ?_)
    le_restrictScalars_separableClosure fun K x hx => ?_
  · let _ := (inclusion le).toAlgebra
    have : IsScalarTower K L E := .of_algebraMap_eq' rfl
    exact hx.tower_top _
  · obtain ⟨x, rfl⟩ := (separableClosure.separableClosure_eq_bot K E).le hx
    exact x.2

/--
lemma `isClosed_restrictScalars_separableClosure` / 引理 `isClosed_restrictScalars_separableClosure`

English:
lemma isClosed_restrictScalars_separableClosure
  given: [Algebra K E] [IsScalarTower F K E]
  proof: ClosureOperator.isClosed_iff_closure_le.mpr fun x hx => by
    obtain ⟨x, rfl⟩ := (separableClosure.separableClosure_eq_bot K E).le hx
    exact x.2

中文:
引理 isClosed_restrictScalars_separableClosure
  条件: [代数 K E] [标量塔 F K E]
  证明: ClosureOperator.isClosed_iff_closure_le.mpr fun x hx => by
    obtain ⟨x, rfl⟩ := (separableClosure.separableClosure_eq_bot K E).le hx
    exact x.2

Depends on / 依赖: ClosureOperator, ClosureOperator.isClosed_iff_closure_le.mpr, isClosed_iff_closure_le, separableClosure, separableClosure.separableClosure_eq_bot, separableClosure_eq_bot
-/
lemma isClosed_restrictScalars_separableClosure [Algebra K E] [IsScalarTower F K E] :
    (separableClosureOperator F E).IsClosed ((separableClosure K E).restrictScalars F) :=
  ClosureOperator.isClosed_iff_closure_le.mpr fun x hx => by
    obtain ⟨x, rfl⟩ := (separableClosure.separableClosure_eq_bot K E).le hx
    exact x.2

/--
lemma `separableClosure_le_separableClosure_iff` / 引理 `separableClosure_le_separableClosure_iff`

English:
lemma separableClosure_le_separableClosure_iff
  proof: (isClosed_restrictScalars_separableClosure F E K).closure_le_iff

中文:
引理 separableClosure_le_separableClosure_iff
  证明: (isClosed_restrictScalars_separableClosure F E K).closure_le_iff

Depends on / 依赖: closure_le_iff, isClosed_restrictScalars_separableClosure
-/
lemma separableClosure_le_separableClosure_iff
    [Algebra K E] [IsScalarTower F K E] {L : IntermediateField F E} :
    (separableClosure L E).restrictScalars F <= (separableClosure K E).restrictScalars F ↔
      L <= (separableClosure K E).restrictScalars F :=
  (isClosed_restrictScalars_separableClosure F E K).closure_le_iff

end separableClosure

namespace Field

/-- The (infinite) separable degree for a general field extension `E / F` is defined
to be the degree of `separableClosure F E / F`. -/
@[stacks 030L "Part 1"]
/--
Definition of `sepDegree` / `sepDegree` 的定义

English:
definition sepDegree
  body: Module.rank F (separableClosure F E)

中文:
定义 sepDegree
  定义体: Module.rank F (separableClosure F E)

Depends on / 依赖: Module, Module.rank, separableClosure
-/
def sepDegree := Module.rank F (separableClosure F E)

/-- The (infinite) inseparable degree for a general field extension `E / F` is defined
to be the degree of `E / separableClosure F E`. -/
@[stacks 030L "Part 2"]
/--
Definition of `insepDegree` / `insepDegree` 的定义

English:
definition insepDegree
  body: Module.rank (separableClosure F E) E

中文:
定义 insepDegree
  定义体: Module.rank (separableClosure F E) E

Depends on / 依赖: Module, Module.rank, separableClosure
-/
def insepDegree := Module.rank (separableClosure F E) E

/--
Definition of `finInsepDegree` / `finInsepDegree` 的定义

English:
definition finInsepDegree
  signature: : Nat
  body: finrank (separableClosure F E) E

中文:
定义 finInsepDegree
  签名: : 自然数
  定义体: finrank (separableClosure F E) E

Depends on / 依赖: finrank, separableClosure
-/
def finInsepDegree : Nat := finrank (separableClosure F E) E

/--
theorem `finInsepDegree_def'` / 定理 `finInsepDegree_def'`

English:
theorem finInsepDegree_def'
  statement: finInsepDegree F E = Cardinal.toNat (insepDegree F E)
  proof: rfl

中文:
定理 finInsepDegree_def'
  结论: finInsepDegree F E = 基数.to自然数 (insepDegree F E)
  证明: rfl
-/
theorem finInsepDegree_def' : finInsepDegree F E = Cardinal.toNat (insepDegree F E) := rfl

/--
Instance `instNeZeroSepDegree` / 实例 `instNeZeroSepDegree`

English:
instance instNeZeroSepDegree
  signature: : NeZero (sepDegree F E)
  body: ⟨rank_pos.ne'⟩

中文:
实例 instNeZeroSepDegree
  签名: : NeZero (sepDegree F E)
  定义体: ⟨rank_pos.ne'⟩

Depends on / 依赖: rank_pos, rank_pos.ne
-/
instance instNeZeroSepDegree : NeZero (sepDegree F E) := ⟨rank_pos.ne'⟩

/--
Instance `instNeZeroInsepDegree` / 实例 `instNeZeroInsepDegree`

English:
instance instNeZeroInsepDegree
  signature: : NeZero (insepDegree F E)
  body: ⟨rank_pos.ne'⟩

中文:
实例 instNeZeroInsepDegree
  签名: : NeZero (insepDegree F E)
  定义体: ⟨rank_pos.ne'⟩

Depends on / 依赖: rank_pos, rank_pos.ne
-/
instance instNeZeroInsepDegree : NeZero (insepDegree F E) := ⟨rank_pos.ne'⟩

/--
Instance `instNeZeroFinInsepDegree` / 实例 `instNeZeroFinInsepDegree`

English:
instance instNeZeroFinInsepDegree
  signature: [FiniteDimensional F E]
  body: ⟨finrank_pos.ne'⟩

中文:
实例 instNeZeroFinInsepDegree
  签名: [有限维 F E]
  定义体: ⟨finrank_pos.ne'⟩

Depends on / 依赖: finrank_pos, finrank_pos.ne
-/
instance instNeZeroFinInsepDegree [FiniteDimensional F E] :
    NeZero (finInsepDegree F E) := ⟨finrank_pos.ne'⟩

/--
theorem `lift_sepDegree_eq_of_equiv` / 定理 `lift_sepDegree_eq_of_equiv`

English:
theorem lift_sepDegree_eq_of_equiv
  given: (i : E ≃ₐ[F] K)
  proof: i.separableClosure.toLinearEquiv.lift_rank_eq

中文:
定理 lift_sepDegree_eq_of_equiv
  条件: (i : E ≃ₐ[F] K)
  证明: i.separableClosure.toLinearEquiv.lift_rank_eq

Depends on / 依赖: i.separableClosure.toLinearEquiv.lift_rank_eq, lift_rank_eq, separableClosure, toLinearEquiv
-/
theorem lift_sepDegree_eq_of_equiv (i : E ≃ₐ[F] K) :
    Cardinal.lift.{w} (sepDegree F E) = Cardinal.lift.{v} (sepDegree F K) :=
  i.separableClosure.toLinearEquiv.lift_rank_eq

/--
theorem `sepDegree_eq_of_equiv` / 定理 `sepDegree_eq_of_equiv`

English:
theorem sepDegree_eq_of_equiv
  given: (K : Type v) [Field K] [Algebra F K] (i : E ≃ₐ[F] K)
  proof: i.separableClosure.toLinearEquiv.rank_eq

中文:
定理 sepDegree_eq_of_equiv
  条件: (K : 类型v) [域 K] [代数 F K] (i : E ≃ₐ[F] K)
  证明: i.separableClosure.toLinearEquiv.rank_eq

Depends on / 依赖: i.separableClosure.toLinearEquiv.rank_eq, rank_eq, separableClosure, toLinearEquiv
-/
theorem sepDegree_eq_of_equiv (K : Type v) [Field K] [Algebra F K] (i : E ≃ₐ[F] K) :
    sepDegree F E = sepDegree F K :=
  i.separableClosure.toLinearEquiv.rank_eq

/--
theorem `sepDegree_mul_insepDegree` / 定理 `sepDegree_mul_insepDegree`

English:
theorem sepDegree_mul_insepDegree
  statement: sepDegree F E * insepDegree F E = Module.rank F E
  proof: rank_mul_rank F (separableClosure F E) E

中文:
定理 sepDegree_mul_insepDegree
  结论: sepDegree F E * insepDegree F E = 模.rank F E
  证明: rank_mul_rank F (separableClosure F E) E

Depends on / 依赖: rank_mul_rank, separableClosure
-/
theorem sepDegree_mul_insepDegree : sepDegree F E * insepDegree F E = Module.rank F E :=
  rank_mul_rank F (separableClosure F E) E

/--
theorem `sepDegree_le_rank` / 定理 `sepDegree_le_rank`

English:
theorem sepDegree_le_rank
  statement: sepDegree F E <= Module.rank F E
  proof: Module.rank_bot_le_rank_of_isScalarTower _ _ _

中文:
定理 sepDegree_le_rank
  结论: sepDegree F E <= 模.rank F E
  证明: Module.rank_bot_le_rank_of_isScalarTower _ _ _

Depends on / 依赖: Module, Module.rank_bot_le_rank_of_isScalarTower, rank_bot_le_rank_of_isScalarTower
-/
theorem sepDegree_le_rank : sepDegree F E <= Module.rank F E :=
  Module.rank_bot_le_rank_of_isScalarTower _ _ _

/--
theorem `insepDegree_le_rank` / 定理 `insepDegree_le_rank`

English:
theorem insepDegree_le_rank
  statement: insepDegree F E <= Module.rank F E
  proof: Module.rank_top_le_rank_of_isScalarTower _ _ _

中文:
定理 insepDegree_le_rank
  结论: insepDegree F E <= 模.rank F E
  证明: Module.rank_top_le_rank_of_isScalarTower _ _ _

Depends on / 依赖: Module, Module.rank_top_le_rank_of_isScalarTower, rank_top_le_rank_of_isScalarTower
-/
theorem insepDegree_le_rank : insepDegree F E <= Module.rank F E :=
  Module.rank_top_le_rank_of_isScalarTower _ _ _

/--
theorem `lift_insepDegree_eq_of_equiv` / 定理 `lift_insepDegree_eq_of_equiv`

English:
theorem lift_insepDegree_eq_of_equiv
  given: (i : E ≃ₐ[F] K)
  proof: Algebra.lift_rank_eq_of_equiv_equiv i.separableClosure i rfl

中文:
定理 lift_insepDegree_eq_of_equiv
  条件: (i : E ≃ₐ[F] K)
  证明: Algebra.lift_rank_eq_of_equiv_equiv i.separableClosure i rfl

Depends on / 依赖: Algebra, Algebra.lift_rank_eq_of_equiv_equiv, i.separableClosure, lift_rank_eq_of_equiv_equiv, separableClosure
-/
theorem lift_insepDegree_eq_of_equiv (i : E ≃ₐ[F] K) :
    Cardinal.lift.{w} (insepDegree F E) = Cardinal.lift.{v} (insepDegree F K) :=
  Algebra.lift_rank_eq_of_equiv_equiv i.separableClosure i rfl

/--
theorem `insepDegree_eq_of_equiv` / 定理 `insepDegree_eq_of_equiv`

English:
theorem insepDegree_eq_of_equiv
  given: (K : Type v) [Field K] [Algebra F K] (i : E ≃ₐ[F] K)
  proof: Algebra.rank_eq_of_equiv_equiv i.separableClosure i rfl

中文:
定理 insepDegree_eq_of_equiv
  条件: (K : 类型v) [域 K] [代数 F K] (i : E ≃ₐ[F] K)
  证明: Algebra.rank_eq_of_equiv_equiv i.separableClosure i rfl

Depends on / 依赖: Algebra, Algebra.rank_eq_of_equiv_equiv, i.separableClosure, rank_eq_of_equiv_equiv, separableClosure
-/
theorem insepDegree_eq_of_equiv (K : Type v) [Field K] [Algebra F K] (i : E ≃ₐ[F] K) :
    insepDegree F E = insepDegree F K :=
  Algebra.rank_eq_of_equiv_equiv i.separableClosure i rfl

/--
theorem `finInsepDegree_eq_of_equiv` / 定理 `finInsepDegree_eq_of_equiv`

English:
theorem finInsepDegree_eq_of_equiv
  given: (i : E ≃ₐ[F] K)
  proof: by
  simpa only [Cardinal.toNat_lift] using! congr_arg Cardinal.toNat
    (lift_insepDegree_eq_of_equiv F E K i)

@[simp]

中文:
定理 finInsepDegree_eq_of_equiv
  条件: (i : E ≃ₐ[F] K)
  证明: by
  simpa only [Cardinal.toNat_lift] using! congr_arg Cardinal.toNat
    (lift_insepDegree_eq_of_equiv F E K i)

@[simp]

Depends on / 依赖: Cardinal, Cardinal.toNat, Cardinal.toNat_lift, congr_arg, lift_insepDegree_eq_of_equiv, toNat_lift
-/
theorem finInsepDegree_eq_of_equiv (i : E ≃ₐ[F] K) :
    finInsepDegree F E = finInsepDegree F K := by
  simpa only [Cardinal.toNat_lift] using! congr_arg Cardinal.toNat
    (lift_insepDegree_eq_of_equiv F E K i)

@[simp]
/--
theorem `sepDegree_self` / 定理 `sepDegree_self`

English:
theorem sepDegree_self
  statement: sepDegree F F = 1
  proof: by
  rw [sepDegree]; rw [Subsingleton.elim (separableClosure F F) ⊥]; rw [IntermediateField.rank_bot]

@[simp]

中文:
定理 sepDegree_self
  结论: sepDegree F F = 1
  证明: by
  rw [sepDegree]; rw [Subsingleton.elim (separableClosure F F) ⊥]; rw [IntermediateField.rank_bot]

@[simp]

Depends on / 依赖: IntermediateField, IntermediateField.rank_bot, Subsingleton, Subsingleton.elim, rank_bot, sepDegree, separableClosure
-/
theorem sepDegree_self : sepDegree F F = 1 := by
  rw [sepDegree]; rw [Subsingleton.elim (separableClosure F F) ⊥]; rw [IntermediateField.rank_bot]

@[simp]
/--
theorem `insepDegree_self` / 定理 `insepDegree_self`

English:
theorem insepDegree_self
  statement: insepDegree F F = 1
  proof: by
  rw [insepDegree]; rw [Subsingleton.elim (separableClosure F F) ⊤]; rw [IntermediateField.rank_top]

@[simp]

中文:
定理 insepDegree_self
  结论: insepDegree F F = 1
  证明: by
  rw [insepDegree]; rw [Subsingleton.elim (separableClosure F F) ⊤]; rw [IntermediateField.rank_top]

@[simp]

Depends on / 依赖: IntermediateField, IntermediateField.rank_top, Subsingleton, Subsingleton.elim, insepDegree, rank_top, separableClosure
-/
theorem insepDegree_self : insepDegree F F = 1 := by
  rw [insepDegree]; rw [Subsingleton.elim (separableClosure F F) ⊤]; rw [IntermediateField.rank_top]

@[simp]
/--
theorem `finInsepDegree_self` / 定理 `finInsepDegree_self`

English:
theorem finInsepDegree_self
  statement: finInsepDegree F F = 1
  proof: by
  rw [finInsepDegree_def']; rw [insepDegree_self]; rw [Cardinal.one_toNat]

中文:
定理 finInsepDegree_self
  结论: finInsepDegree F F = 1
  证明: by
  rw [finInsepDegree_def']; rw [insepDegree_self]; rw [Cardinal.one_toNat]

Depends on / 依赖: Cardinal, Cardinal.one_toNat, finInsepDegree_def, insepDegree_self, one_toNat
-/
theorem finInsepDegree_self : finInsepDegree F F = 1 := by
  rw [finInsepDegree_def']; rw [insepDegree_self]; rw [Cardinal.one_toNat]

end Field

namespace IntermediateField

/--
lemma `exists_finset_maximalFor_isTranscendenceBasis_separableClosure` / 引理 `exists_finset_maximalFor_isTranscendenceBasis_separableClosure`

English:
lemma exists_finset_maximalFor_isTranscendenceBasis_separableClosure
  proof: by
  let d (s : Finset E) := Field.finInsepDegree (adjoin F (s : Set E)) E
  have Hexists : {s : Finset E | IsTranscendenceBasis F ((↑) : s -> E)}.Nonempty := by
    have ⟨s, hs⟩ := IntermediateField.fg_top F E
    have : Algebra.IsAlgebraic (Algebra.adjoin F (s : Set E)) E := by
      rw [← isAlgeb

中文:
引理 存在_finset_maximalFor_isTranscendenceBasis_separableClosure
  证明: by
  let d (s : Finset E) := Field.finInsepDegree (adjoin F (s : Set E)) E
  have Hexists : {s : Finset E | IsTranscendenceBasis F ((↑) : s -> E)}.Nonempty := by
    have ⟨s, hs⟩ := IntermediateField.fg_top F E
    have : Algebra.IsAlgebraic (Algebra.adjoin F (s : Set E)) E := by
      rw [← isAlgeb

Depends on / 依赖: Algebra, Algebra.IsAlgebraic, Algebra.adjoin, Algebra.isAlgebraic_iff_isIntegral, Algebra.isIntegral_of_surjective, Field.finInsepDegree, Finset, Hexists, IntermediateField, IntermediateField.fg_top, IsAlgebraic, IsTranscendenceBasis, Nonempty, adjoin, exists_isTranscendenceBasis_subset, fg_top, finInsepDegree, isAlgebraic_adjoin_iff_top, isAlgebraic_iff_isIntegral, isIntegral_of_surjective
-/
lemma exists_finset_maximalFor_isTranscendenceBasis_separableClosure
    [Algebra.EssFiniteType F E] :
    exists s : Finset E, MaximalFor (fun t : Set E => IsTranscendenceBasis F ((↑) : t -> E))
      (fun t => (separableClosure (adjoin F t) E).restrictScalars F) s := by
  let d (s : Finset E) := Field.finInsepDegree (adjoin F (s : Set E)) E
  have Hexists : {s : Finset E | IsTranscendenceBasis F ((↑) : s -> E)}.Nonempty := by
    have ⟨s, hs⟩ := IntermediateField.fg_top F E
    have : Algebra.IsAlgebraic (Algebra.adjoin F (s : Set E)) E := by
      rw [← isAlgebraic_adjoin_iff_top]; rw [hs]; rw [Algebra.isAlgebraic_iff_isIntegral]
      refine Algebra.isIntegral_of_surjective topEquiv.surjective
    have ⟨t, hts, ht⟩ := exists_isTranscendenceBasis_subset (R := F) (s : Set E)
    lift t to Finset E using s.finite_toSet.subset hts
    exact ⟨t, ht⟩
  let s := d.argminOn _ Hexists
  have hs := d.argminOn_mem _ Hexists
  refine ⟨s, hs, fun t ht => not_lt_iff_le_imp_ge.mp fun H => ?_⟩
  have : t.Finite := by
    simp [Set.Finite, ← Cardinal.mk_lt_aleph0_iff, ht.cardinalMk_eq hs, Cardinal.natCast_lt_aleph0]
  lift t to Finset E using this
  have : Module.Finite (adjoin F (s : Set E)) E := by
    apply +allowSynthFailures Algebra.finite_of_essFiniteType_of_isAlgebraic
    · exact .of_comp F _ _
    · convert! hs.isAlgebraic_field <;> simp [s]
  have : Module.Finite ((separableClosure (adjoin F (s : Set E)) E).restrictScalars F) E :=
inferInstanceAs Module.Finite (separableClosure (adjoin F (s : Set E)) E) E
  exact d.not_lt_argminOn _ ht (by apply finrank_lt_of_gt H)

@[simp]
/--
theorem `sepDegree_bot` / 定理 `sepDegree_bot`

English:
theorem sepDegree_bot
  statement: sepDegree F (⊥ : IntermediateField F E) = 1
  proof: by
  have := lift_sepDegree_eq_of_equiv _ _ _ (botEquiv F E)
  rwa [sepDegree_self, Cardinal.lift_one, ← Cardinal.lift_one.{v, u}, Cardinal.lift_inj] at this

@[simp]

中文:
定理 sepDegree_bot
  结论: sepDegree F (⊥ : 中间域 F E) = 1
  证明: by
  have := lift_sepDegree_eq_of_equiv _ _ _ (botEquiv F E)
  rwa [sepDegree_self, Cardinal.lift_one, ← Cardinal.lift_one.{v, u}, Cardinal.lift_inj] at this

@[simp]

Depends on / 依赖: Cardinal, Cardinal.lift_inj, Cardinal.lift_one, botEquiv, lift_inj, lift_one, lift_sepDegree_eq_of_equiv, sepDegree_self
-/
theorem sepDegree_bot : sepDegree F (⊥ : IntermediateField F E) = 1 := by
  have := lift_sepDegree_eq_of_equiv _ _ _ (botEquiv F E)
  rwa [sepDegree_self, Cardinal.lift_one, ← Cardinal.lift_one.{v, u}, Cardinal.lift_inj] at this

@[simp]
/--
theorem `insepDegree_bot` / 定理 `insepDegree_bot`

English:
theorem insepDegree_bot
  statement: insepDegree F (⊥ : IntermediateField F E) = 1
  proof: by
  have := lift_insepDegree_eq_of_equiv _ _ _ (botEquiv F E)
  rwa [insepDegree_self, Cardinal.lift_one, ← Cardinal.lift_one.{v, u}, Cardinal.lift_inj] at this

@[simp]

中文:
定理 insepDegree_bot
  结论: insepDegree F (⊥ : 中间域 F E) = 1
  证明: by
  have := lift_insepDegree_eq_of_equiv _ _ _ (botEquiv F E)
  rwa [insepDegree_self, Cardinal.lift_one, ← Cardinal.lift_one.{v, u}, Cardinal.lift_inj] at this

@[simp]

Depends on / 依赖: Cardinal, Cardinal.lift_inj, Cardinal.lift_one, botEquiv, insepDegree_self, lift_inj, lift_insepDegree_eq_of_equiv, lift_one
-/
theorem insepDegree_bot : insepDegree F (⊥ : IntermediateField F E) = 1 := by
  have := lift_insepDegree_eq_of_equiv _ _ _ (botEquiv F E)
  rwa [insepDegree_self, Cardinal.lift_one, ← Cardinal.lift_one.{v, u}, Cardinal.lift_inj] at this

@[simp]
/--
theorem `finInsepDegree_bot` / 定理 `finInsepDegree_bot`

English:
theorem finInsepDegree_bot
  statement: finInsepDegree F (⊥ : IntermediateField F E) = 1
  proof: by
  rw [finInsepDegree_eq_of_equiv _ _ _ (botEquiv F E)]; rw [finInsepDegree_self]

中文:
定理 finInsepDegree_bot
  结论: finInsepDegree F (⊥ : 中间域 F E) = 1
  证明: by
  rw [finInsepDegree_eq_of_equiv _ _ _ (botEquiv F E)]; rw [finInsepDegree_self]

Depends on / 依赖: botEquiv, finInsepDegree_eq_of_equiv, finInsepDegree_self
-/
theorem finInsepDegree_bot : finInsepDegree F (⊥ : IntermediateField F E) = 1 := by
  rw [finInsepDegree_eq_of_equiv _ _ _ (botEquiv F E)]; rw [finInsepDegree_self]

section Tower

variable [Algebra E K] [IsScalarTower F E K]

/--
theorem `lift_sepDegree_bot'` / 定理 `lift_sepDegree_bot'`

English:
theorem lift_sepDegree_bot'
  statement: Cardinal.lift.{v} (sepDegree F (⊥ : IntermediateField E K)) =
  proof: lift_sepDegree_eq_of_equiv _ _ _ ((botEquiv E K).restrictScalars F)

中文:
定理 lift_sepDegree_bot'
  结论: 基数.lift.{v} (sepDegree F (⊥ : 中间域 E K)) =
  证明: lift_sepDegree_eq_of_equiv _ _ _ ((botEquiv E K).restrictScalars F)

Depends on / 依赖: botEquiv, lift_sepDegree_eq_of_equiv, restrictScalars
-/
theorem lift_sepDegree_bot' : Cardinal.lift.{v} (sepDegree F (⊥ : IntermediateField E K)) =
    Cardinal.lift.{w} (sepDegree F E) :=
  lift_sepDegree_eq_of_equiv _ _ _ ((botEquiv E K).restrictScalars F)

/--
theorem `lift_insepDegree_bot'` / 定理 `lift_insepDegree_bot'`

English:
theorem lift_insepDegree_bot'
  statement: Cardinal.lift.{v} (insepDegree F (⊥ : IntermediateField E K)) =
  proof: lift_insepDegree_eq_of_equiv _ _ _ ((botEquiv E K).restrictScalars F)

中文:
定理 lift_insepDegree_bot'
  结论: 基数.lift.{v} (insepDegree F (⊥ : 中间域 E K)) =
  证明: lift_insepDegree_eq_of_equiv _ _ _ ((botEquiv E K).restrictScalars F)

Depends on / 依赖: botEquiv, lift_insepDegree_eq_of_equiv, restrictScalars
-/
theorem lift_insepDegree_bot' : Cardinal.lift.{v} (insepDegree F (⊥ : IntermediateField E K)) =
    Cardinal.lift.{w} (insepDegree F E) :=
  lift_insepDegree_eq_of_equiv _ _ _ ((botEquiv E K).restrictScalars F)

variable {F}

@[simp]
/--
theorem `finInsepDegree_bot'` / 定理 `finInsepDegree_bot'`

English:
theorem finInsepDegree_bot'
  proof: by
  simpa only [Cardinal.toNat_lift] using! congr_arg Cardinal.toNat (lift_insepDegree_bot' F E K)

@[simp]

中文:
定理 finInsepDegree_bot'
  证明: by
  simpa only [Cardinal.toNat_lift] using! congr_arg Cardinal.toNat (lift_insepDegree_bot' F E K)

@[simp]

Depends on / 依赖: Cardinal, Cardinal.toNat, Cardinal.toNat_lift, congr_arg, lift_insepDegree_bot, toNat_lift
-/
theorem finInsepDegree_bot' :
    finInsepDegree F (⊥ : IntermediateField E K) = finInsepDegree F E := by
  simpa only [Cardinal.toNat_lift] using! congr_arg Cardinal.toNat (lift_insepDegree_bot' F E K)

@[simp]
/--
theorem `sepDegree_top` / 定理 `sepDegree_top`

English:
theorem sepDegree_top
  statement: sepDegree F (⊤ : IntermediateField E K) = sepDegree F K
  proof: sepDegree_eq_of_equiv _ _ _ ((topEquiv (F := E) (E := K)).restrictScalars F)

@[simp]

中文:
定理 sepDegree_top
  结论: sepDegree F (⊤ : 中间域 E K) = sepDegree F K
  证明: sepDegree_eq_of_equiv _ _ _ ((topEquiv (F := E) (E := K)).restrictScalars F)

@[simp]

Depends on / 依赖: restrictScalars, sepDegree_eq_of_equiv, topEquiv
-/
theorem sepDegree_top : sepDegree F (⊤ : IntermediateField E K) = sepDegree F K :=
  sepDegree_eq_of_equiv _ _ _ ((topEquiv (F := E) (E := K)).restrictScalars F)

@[simp]
/--
theorem `insepDegree_top` / 定理 `insepDegree_top`

English:
theorem insepDegree_top
  statement: insepDegree F (⊤ : IntermediateField E K) = insepDegree F K
  proof: insepDegree_eq_of_equiv _ _ _ ((topEquiv (F := E) (E := K)).restrictScalars F)

@[simp]

中文:
定理 insepDegree_top
  结论: insepDegree F (⊤ : 中间域 E K) = insepDegree F K
  证明: insepDegree_eq_of_equiv _ _ _ ((topEquiv (F := E) (E := K)).restrictScalars F)

@[simp]

Depends on / 依赖: insepDegree_eq_of_equiv, restrictScalars, topEquiv
-/
theorem insepDegree_top : insepDegree F (⊤ : IntermediateField E K) = insepDegree F K :=
  insepDegree_eq_of_equiv _ _ _ ((topEquiv (F := E) (E := K)).restrictScalars F)

@[simp]
/--
theorem `finInsepDegree_top` / 定理 `finInsepDegree_top`

English:
theorem finInsepDegree_top
  statement: finInsepDegree F (⊤ : IntermediateField E K) = finInsepDegree F K
  proof: by
  rw [finInsepDegree_def']; rw [insepDegree_top]; rw [← finInsepDegree_def']

中文:
定理 finInsepDegree_top
  结论: finInsepDegree F (⊤ : 中间域 E K) = finInsepDegree F K
  证明: by
  rw [finInsepDegree_def']; rw [insepDegree_top]; rw [← finInsepDegree_def']

Depends on / 依赖: finInsepDegree_def, insepDegree_top
-/
theorem finInsepDegree_top : finInsepDegree F (⊤ : IntermediateField E K) = finInsepDegree F K := by
  rw [finInsepDegree_def']; rw [insepDegree_top]; rw [← finInsepDegree_def']

variable (K : Type v) [Field K] [Algebra F K] [Algebra E K] [IsScalarTower F E K]

@[simp]
/--
theorem `sepDegree_bot'` / 定理 `sepDegree_bot'`

English:
theorem sepDegree_bot'
  statement: sepDegree F (⊥ : IntermediateField E K) = sepDegree F E
  proof: sepDegree_eq_of_equiv _ _ _ ((botEquiv E K).restrictScalars F)

@[simp]

中文:
定理 sepDegree_bot'
  结论: sepDegree F (⊥ : 中间域 E K) = sepDegree F E
  证明: sepDegree_eq_of_equiv _ _ _ ((botEquiv E K).restrictScalars F)

@[simp]

Depends on / 依赖: botEquiv, restrictScalars, sepDegree_eq_of_equiv
-/
theorem sepDegree_bot' : sepDegree F (⊥ : IntermediateField E K) = sepDegree F E :=
  sepDegree_eq_of_equiv _ _ _ ((botEquiv E K).restrictScalars F)

@[simp]
/--
theorem `insepDegree_bot'` / 定理 `insepDegree_bot'`

English:
theorem insepDegree_bot'
  statement: insepDegree F (⊥ : IntermediateField E K) = insepDegree F E
  proof: insepDegree_eq_of_equiv _ _ _ ((botEquiv E K).restrictScalars F)

中文:
定理 insepDegree_bot'
  结论: insepDegree F (⊥ : 中间域 E K) = insepDegree F E
  证明: insepDegree_eq_of_equiv _ _ _ ((botEquiv E K).restrictScalars F)

Depends on / 依赖: botEquiv, insepDegree_eq_of_equiv, restrictScalars
-/
theorem insepDegree_bot' : insepDegree F (⊥ : IntermediateField E K) = insepDegree F E :=
  insepDegree_eq_of_equiv _ _ _ ((botEquiv E K).restrictScalars F)

variable (F) in
/--
lemma `_root_.Field.insepDegree_top_le_insepDegree_of_isScalarTower` / 引理 `_root_.Field.insepDegree_top_le_insepDegree_of_isScalarTower`

English:
lemma _root_.Field.insepDegree_top_le_insepDegree_of_isScalarTower
  proof: by
  let := (IntermediateField.inclusion (separableClosure.le_restrictScalars F E K)).toAlgebra
  have : IsScalarTower (separableClosure F K) ((separableClosure E K).restrictScalars F) K :=
    .of_algebraMap_eq' rfl
  exact Module.rank_top_le_rank_of_isScalarTower
    (separableClosure F K) ((separ

中文:
引理 _root_.域.insepDegree_top_le_insepDegree_of_isScalarTower
  证明: by
  let := (IntermediateField.inclusion (separableClosure.le_restrictScalars F E K)).toAlgebra
  have : IsScalarTower (separableClosure F K) ((separableClosure E K).restrictScalars F) K :=
    .of_algebraMap_eq' rfl
  exact Module.rank_top_le_rank_of_isScalarTower
    (separableClosure F K) ((separ

Depends on / 依赖: IntermediateField, IntermediateField.inclusion, IsScalarTower, Module, Module.rank_top_le_rank_of_isScalarTower, inclusion, le_restrictScalars, of_algebraMap_eq, rank_top_le_rank_of_isScalarTower, restrictScalars, separableClosure, separableClosure.le_restrictScalars, toAlgebra
-/
lemma _root_.Field.insepDegree_top_le_insepDegree_of_isScalarTower :
    insepDegree E K <= insepDegree F K := by
  let := (IntermediateField.inclusion (separableClosure.le_restrictScalars F E K)).toAlgebra
  have : IsScalarTower (separableClosure F K) ((separableClosure E K).restrictScalars F) K :=
    .of_algebraMap_eq' rfl
  exact Module.rank_top_le_rank_of_isScalarTower
    (separableClosure F K) ((separableClosure E K).restrictScalars F) K

variable {K} in
/--
lemma `_root_.Field.insepDegree_le_of_left_le` / 引理 `_root_.Field.insepDegree_le_of_left_le`

English:
lemma _root_.Field.insepDegree_le_of_left_le
  given: {E₁ E₂ : IntermediateField F K} (H : E₁ <= E₂)
  proof: by
  let := (IntermediateField.inclusion H).toAlgebra
  have : IsScalarTower E₁ E₂ K := .of_algebraMap_eq' rfl
  exact insepDegree_top_le_insepDegree_of_isScalarTower _ _ _

中文:
引理 _root_.域.insepDegree_le_of_left_le
  条件: {E₁ E₂ : 中间域 F K} (H : E₁ <= E₂)
  证明: by
  let := (IntermediateField.inclusion H).toAlgebra
  have : IsScalarTower E₁ E₂ K := .of_algebraMap_eq' rfl
  exact insepDegree_top_le_insepDegree_of_isScalarTower _ _ _

Depends on / 依赖: IntermediateField, IntermediateField.inclusion, IsScalarTower, inclusion, insepDegree_top_le_insepDegree_of_isScalarTower, of_algebraMap_eq, toAlgebra
-/
lemma _root_.Field.insepDegree_le_of_left_le {E₁ E₂ : IntermediateField F K} (H : E₁ <= E₂) :
    insepDegree E₂ K <= insepDegree E₁ K := by
  let := (IntermediateField.inclusion H).toAlgebra
  have : IsScalarTower E₁ E₂ K := .of_algebraMap_eq' rfl
  exact insepDegree_top_le_insepDegree_of_isScalarTower _ _ _

variable (F) in
/--
lemma `_root_.Field.finInsepDegree_top_le_finInsepDegree_of_isScalarTower` / 引理 `_root_.Field.finInsepDegree_top_le_finInsepDegree_of_isScalarTower`

English:
lemma _root_.Field.finInsepDegree_top_le_finInsepDegree_of_isScalarTower
  given: [Module.Finite F K]
  proof: by
  let := (IntermediateField.inclusion (separableClosure.le_restrictScalars F E K)).toAlgebra
  have : IsScalarTower (separableClosure F K) ((separableClosure E K).restrictScalars F) K :=
    .of_algebraMap_eq' rfl
  exact Module.finrank_top_le_finrank_of_isScalarTower
    (separableClosure F K) (

中文:
引理 _root_.域.finInsepDegree_top_le_finInsepDegree_of_isScalarTower
  条件: [模.有限 F K]
  证明: by
  let := (IntermediateField.inclusion (separableClosure.le_restrictScalars F E K)).toAlgebra
  have : IsScalarTower (separableClosure F K) ((separableClosure E K).restrictScalars F) K :=
    .of_algebraMap_eq' rfl
  exact Module.finrank_top_le_finrank_of_isScalarTower
    (separableClosure F K) (

Depends on / 依赖: IntermediateField, IntermediateField.inclusion, IsScalarTower, Module, Module.finrank_top_le_finrank_of_isScalarTower, finrank_top_le_finrank_of_isScalarTower, inclusion, le_restrictScalars, of_algebraMap_eq, restrictScalars, separableClosure, separableClosure.le_restrictScalars, toAlgebra
-/
lemma _root_.Field.finInsepDegree_top_le_finInsepDegree_of_isScalarTower [Module.Finite F K] :
    finInsepDegree E K <= finInsepDegree F K := by
  let := (IntermediateField.inclusion (separableClosure.le_restrictScalars F E K)).toAlgebra
  have : IsScalarTower (separableClosure F K) ((separableClosure E K).restrictScalars F) K :=
    .of_algebraMap_eq' rfl
  exact Module.finrank_top_le_finrank_of_isScalarTower
    (separableClosure F K) ((separableClosure E K).restrictScalars F) K

variable {K} in
/--
lemma `finInsepDegree_le_of_left_le` / 引理 `finInsepDegree_le_of_left_le`

English:
lemma finInsepDegree_le_of_left_le
  statement: {E₁ E₂ : IntermediateField F K} (H : E₁ <= E₂)
  proof: by
  let := (IntermediateField.inclusion H).toAlgebra
  have : IsScalarTower E₁ E₂ K := .of_algebraMap_eq' rfl
  exact finInsepDegree_top_le_finInsepDegree_of_isScalarTower _ _ _

中文:
引理 finInsepDegree_le_of_left_le
  结论: {E₁ E₂ : 中间域 F K} (H : E₁ <= E₂)
  证明: by
  let := (IntermediateField.inclusion H).toAlgebra
  have : IsScalarTower E₁ E₂ K := .of_algebraMap_eq' rfl
  exact finInsepDegree_top_le_finInsepDegree_of_isScalarTower _ _ _

Depends on / 依赖: IntermediateField, IntermediateField.inclusion, IsScalarTower, finInsepDegree_top_le_finInsepDegree_of_isScalarTower, inclusion, of_algebraMap_eq, toAlgebra
-/
lemma finInsepDegree_le_of_left_le {E₁ E₂ : IntermediateField F K} (H : E₁ <= E₂)
    [Module.Finite E₁ K] : finInsepDegree E₂ K <= finInsepDegree E₁ K := by
  let := (IntermediateField.inclusion H).toAlgebra
  have : IsScalarTower E₁ E₂ K := .of_algebraMap_eq' rfl
  exact finInsepDegree_top_le_finInsepDegree_of_isScalarTower _ _ _

end Tower

end IntermediateField

/--
theorem `Algebra.IsSeparable.sepDegree_eq` / 定理 `Algebra.IsSeparable.sepDegree_eq`

English:
theorem Algebra.IsSeparable.sepDegree_eq
  given: [Algebra.IsSeparable F E]
  proof: by
  rw [sepDegree]; rw [(separableClosure.eq_top_iff F E).2 ‹_›]; rw [IntermediateField.rank_top']

中文:
定理 代数.是可分.sepDegree_eq
  条件: [代数.是可分 F E]
  证明: by
  rw [sepDegree]; rw [(separableClosure.eq_top_iff F E).2 ‹_›]; rw [IntermediateField.rank_top']

Depends on / 依赖: IntermediateField, IntermediateField.rank_top, eq_top_iff, rank_top, sepDegree, separableClosure, separableClosure.eq_top_iff
-/
theorem Algebra.IsSeparable.sepDegree_eq [Algebra.IsSeparable F E] :
    sepDegree F E = Module.rank F E := by
  rw [sepDegree]; rw [(separableClosure.eq_top_iff F E).2 ‹_›]; rw [IntermediateField.rank_top']

/--
theorem `Algebra.IsSeparable.insepDegree_eq` / 定理 `Algebra.IsSeparable.insepDegree_eq`

English:
theorem Algebra.IsSeparable.insepDegree_eq
  given: [Algebra.IsSeparable F E]
  statement: insepDegree F E = 1
  proof: by
  rw [insepDegree]; rw [(separableClosure.eq_top_iff F E).2 ‹_›]; rw [IntermediateField.rank_top]

中文:
定理 代数.是可分.insepDegree_eq
  条件: [代数.是可分 F E]
  结论: insepDegree F E = 1
  证明: by
  rw [insepDegree]; rw [(separableClosure.eq_top_iff F E).2 ‹_›]; rw [IntermediateField.rank_top]

Depends on / 依赖: IntermediateField, IntermediateField.rank_top, eq_top_iff, insepDegree, rank_top, separableClosure, separableClosure.eq_top_iff
-/
theorem Algebra.IsSeparable.insepDegree_eq [Algebra.IsSeparable F E] : insepDegree F E = 1 := by
  rw [insepDegree]; rw [(separableClosure.eq_top_iff F E).2 ‹_›]; rw [IntermediateField.rank_top]

/--
theorem `Algebra.IsSeparable.finInsepDegree_eq` / 定理 `Algebra.IsSeparable.finInsepDegree_eq`

English:
theorem Algebra.IsSeparable.finInsepDegree_eq
  given: [Algebra.IsSeparable F E]
  statement: finInsepDegree F E = 1
  proof: Cardinal.one_toNat ▸ congr(Cardinal.toNat $(insepDegree_eq F E))

中文:
定理 代数.是可分.finInsepDegree_eq
  条件: [代数.是可分 F E]
  结论: finInsepDegree F E = 1
  证明: Cardinal.one_toNat ▸ congr(Cardinal.toNat $(insepDegree_eq F E))

Depends on / 依赖: Cardinal, Cardinal.one_toNat, Cardinal.toNat, insepDegree_eq, one_toNat
-/
theorem Algebra.IsSeparable.finInsepDegree_eq [Algebra.IsSeparable F E] : finInsepDegree F E = 1 :=
  Cardinal.one_toNat ▸ congr(Cardinal.toNat $(insepDegree_eq F E))
