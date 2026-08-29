/-
Copyright (c) 2020 Thomas Browning, Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Patrick Lutz
-/
module

public import Mathlib.FieldTheory.Finiteness
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.FieldTheory.IntermediateField.Algebraic
public import Mathlib.RingTheory.Adjoin.Singleton
public import Mathlib.RingTheory.EssentialFiniteness

/-!
# Adjoining Elements to Fields

This file relates `IntermediateField.adjoin` to `Algebra.adjoin`.
-/

public section

open Module Polynomial

namespace IntermediateField

section AdjoinDef

variable (F : Type*) [Field F] {E : Type*} [Field E] [Algebra F E] (S : Set E)

/--
theorem `algebra_adjoin_le_adjoin` / 定理 `algebra_adjoin_le_adjoin`

English:
theorem algebra_adjoin_le_adjoin
  statement: Algebra.adjoin F S <= (adjoin F S).toSubalgebra
  proof: Algebra.adjoin_le (subset_adjoin _ _)

中文:
定理 algebra_adjoin_le_adjoin
  结论: Algebra.adjoin F S <= (adjoin F S).toSubalgebra
  证明: Algebra.adjoin_le (subset_adjoin _ _)

Depends on / 依赖: Algebra, Algebra.adjoin_le, adjoin_le, subset_adjoin
-/
theorem algebra_adjoin_le_adjoin : Algebra.adjoin F S <= (adjoin F S).toSubalgebra :=
  Algebra.adjoin_le (subset_adjoin _ _)

namespace algebraAdjoinAdjoin

/-- `IntermediateField.adjoin` as an algebra over `Algebra.adjoin`. -/
scoped instance : Algebra (Algebra.adjoin F S) (adjoin F S) :=
  (Subalgebra.inclusion <| algebra_adjoin_le_adjoin F S).toAlgebra

@[simp]
/--
theorem `coe_algebraMap` / 定理 `coe_algebraMap`

English:
theorem coe_algebraMap
  given: (x : Algebra.adjoin F S)
  proof: rfl

@[simp]

中文:
定理 coe_algebraMap
  条件: (x : Algebra.adjoin F S)
  证明: rfl

@[simp]
-/
theorem coe_algebraMap (x : Algebra.adjoin F S) :
    (algebraMap (Algebra.adjoin F S) (adjoin F S) x : E) = x := rfl

@[simp]
/--
theorem `algebraMap_eq_gen_self` / 定理 `algebraMap_eq_gen_self`

English:
theorem algebraMap_eq_gen_self
  given: {x : E}
  proof: rfl

scoped instance (X) [SMul X F] [SMul X E] [IsScalarTower X F E] :
    IsScalarTower X (Algebra.adjoin F S) (adjoin F S) :=
  Subalgebra.inclusion.isScalarTower_left (algebra_adjoin_le_adjoin F S) _

scoped instance (X) [MulAction E X] : IsScalarTower (Algebra.adjoin F S) (adjoin F S) X :=
  Sub

中文:
定理 algebraMap_eq_gen_self
  条件: {x : E}
  证明: rfl

scoped instance (X) [SMul X F] [SMul X E] [IsScalarTower X F E] :
    IsScalarTower X (Algebra.adjoin F S) (adjoin F S) :=
  Subalgebra.inclusion.isScalarTower_left (algebra_adjoin_le_adjoin F S) _

scoped instance (X) [MulAction E X] : IsScalarTower (Algebra.adjoin F S) (adjoin F S) X :=
  Sub
-/
theorem algebraMap_eq_gen_self {x : E} :
    algebraMap (Algebra.adjoin F {x}) F⟮x⟯ ⟨x, Algebra.self_mem_adjoin_singleton F x⟩ =
    AdjoinSimple.gen F x := rfl

scoped instance (X) [SMul X F] [SMul X E] [IsScalarTower X F E] :
    IsScalarTower X (Algebra.adjoin F S) (adjoin F S) :=
  Subalgebra.inclusion.isScalarTower_left (algebra_adjoin_le_adjoin F S) _

scoped instance (X) [MulAction E X] : IsScalarTower (Algebra.adjoin F S) (adjoin F S) X :=
  Subalgebra.inclusion.isScalarTower_right (algebra_adjoin_le_adjoin F S) _

scoped instance : FaithfulSMul (Algebra.adjoin F S) (adjoin F S) :=
  Subalgebra.inclusion.faithfulSMul (algebra_adjoin_le_adjoin F S)

scoped instance : IsFractionRing (Algebra.adjoin F S) (adjoin F S) :=
  .of_field _ _ fun ⟨_, h⟩ => have ⟨x, hx, y, hy, eq⟩ := mem_adjoin_iff_div.mp h
    ⟨⟨x, hx⟩, ⟨y, hy⟩, Subtype.ext eq⟩

scoped instance : Algebra.IsAlgebraic (Algebra.adjoin F S) (adjoin F S) :=
  IsLocalization.isAlgebraic _ (nonZeroDivisors (Algebra.adjoin F S))

end algebraAdjoinAdjoin

/--
theorem `adjoin_eq_algebra_adjoin` / 定理 `adjoin_eq_algebra_adjoin`

English:
theorem adjoin_eq_algebra_adjoin
  given: (inv_mem : forall x in Algebra.adjoin F S, x⁻¹ in Algebra.adjoin F S)
  proof: le_antisymm
    (show adjoin F S <=
        { Algebra.adjoin F S with
          inv_mem' := inv_mem }
      from adjoin_le_iff.mpr Algebra.subset_adjoin)
    (algebra_adjoin_le_adjoin _ _)

中文:
定理 adjoin_eq_algebra_adjoin
  条件: (inv_mem : 对任意 x in Algebra.adjoin F S, x⁻¹ in Algebra.adjoin F S)
  证明: le_antisymm
    (show adjoin F S <=
        { Algebra.adjoin F S with
          inv_mem' := inv_mem }
      from adjoin_le_iff.mpr Algebra.subset_adjoin)
    (algebra_adjoin_le_adjoin _ _)

Depends on / 依赖: Algebra, Algebra.adjoin, Algebra.subset_adjoin, adjoin, adjoin_le_iff, adjoin_le_iff.mpr, algebra_adjoin_le_adjoin, inv_mem, le_antisymm, subset_adjoin
-/
theorem adjoin_eq_algebra_adjoin (inv_mem : forall x in Algebra.adjoin F S, x⁻¹ in Algebra.adjoin F S) :
    (adjoin F S).toSubalgebra = Algebra.adjoin F S :=
  le_antisymm
    (show adjoin F S <=
        { Algebra.adjoin F S with
          inv_mem' := inv_mem }
      from adjoin_le_iff.mpr Algebra.subset_adjoin)
    (algebra_adjoin_le_adjoin _ _)

/--
theorem `eq_adjoin_of_eq_algebra_adjoin` / 定理 `eq_adjoin_of_eq_algebra_adjoin`

English:
theorem eq_adjoin_of_eq_algebra_adjoin
  statement: (K : IntermediateField F E)
  proof: by
  apply toSubalgebra_injective
  rw [h]
  refine (adjoin_eq_algebra_adjoin F _ fun x => ?_).symm
  rw [← h]
  exact K.inv_mem

中文:
定理 eq_adjoin_of_eq_algebra_adjoin
  结论: (K : 整数ermediateField F E)
  证明: by
  apply toSubalgebra_injective
  rw [h]
  refine (adjoin_eq_algebra_adjoin F _ fun x => ?_).symm
  rw [← h]
  exact K.inv_mem

Depends on / 依赖: K.inv_mem, adjoin_eq_algebra_adjoin, inv_mem, toSubalgebra_injective
-/
theorem eq_adjoin_of_eq_algebra_adjoin (K : IntermediateField F E)
    (h : K.toSubalgebra = Algebra.adjoin F S) : K = adjoin F S := by
  apply toSubalgebra_injective
  rw [h]
  refine (adjoin_eq_algebra_adjoin F _ fun x => ?_).symm
  rw [← h]
  exact K.inv_mem

/--
theorem `adjoin_eq_top_of_algebra` / 定理 `adjoin_eq_top_of_algebra`

English:
theorem adjoin_eq_top_of_algebra
  given: (hS : Algebra.adjoin F S = ⊤)
  statement: adjoin F S = ⊤
  proof: top_le_iff.mp (hS.symm.trans_le <| algebra_adjoin_le_adjoin F S)

中文:
定理 adjoin_eq_top_of_algebra
  条件: (hS : Algebra.adjoin F S = ⊤)
  结论: adjoin F S = ⊤
  证明: top_le_iff.mp (hS.symm.trans_le <| algebra_adjoin_le_adjoin F S)

Depends on / 依赖: algebra_adjoin_le_adjoin, hS.symm.trans_le, top_le_iff, top_le_iff.mp, trans_le
-/
theorem adjoin_eq_top_of_algebra (hS : Algebra.adjoin F S = ⊤) : adjoin F S = ⊤ :=
  top_le_iff.mp (hS.symm.trans_le <| algebra_adjoin_le_adjoin F S)

section FG

variable {F}

open scoped algebraAdjoinAdjoin in
/--
lemma `fg_top_iff` / 引理 `fg_top_iff`

English:
lemma fg_top_iff
  proof: by
  constructor
  · intro ⟨s, hs⟩
    have : Algebra.FiniteType F (Algebra.adjoin F (s : Set E)) := .adjoin_of_finite s.finite_toSet
    have : Algebra.EssFiniteType (Algebra.adjoin F (s : Set E)) (adjoin F (s : Set E)) :=
      .of_isLocalization _ (nonZeroDivisors _)
    have : Algebra.EssFiniteT

中文:
引理 fg_top_iff
  证明: by
  constructor
  · intro ⟨s, hs⟩
    have : Algebra.FiniteType F (Algebra.adjoin F (s : Set E)) := .adjoin_of_finite s.finite_toSet
    have : Algebra.EssFiniteType (Algebra.adjoin F (s : Set E)) (adjoin F (s : Set E)) :=
      .of_isLocalization _ (nonZeroDivisors _)
    have : Algebra.EssFiniteT

Depends on / 依赖: Algebra, Algebra.EssFiniteType, Algebra.EssFiniteType.fi, Algebra.FiniteType, Algebra.adjoin, EssFiniteType, FiniteType, IntermediateField, IntermediateField.topEquiv.surjective, IntermediateField.topEquiv.toAlgHom, adjoin, adjoin_of_finite, finite_toSet, nonZeroDivisors, of_isLocalization, of_surjective, s.finite_toSet, surjective, toAlgHom, topEquiv
-/
lemma fg_top_iff :
    (⊤ : IntermediateField F E).FG ↔ Algebra.EssFiniteType F E := by
  constructor
  · intro ⟨s, hs⟩
    have : Algebra.FiniteType F (Algebra.adjoin F (s : Set E)) := .adjoin_of_finite s.finite_toSet
    have : Algebra.EssFiniteType (Algebra.adjoin F (s : Set E)) (adjoin F (s : Set E)) :=
      .of_isLocalization _ (nonZeroDivisors _)
    have : Algebra.EssFiniteType F (adjoin F (s : Set E)) :=
      .comp _ (Algebra.adjoin F (s : Set E)) _
    rw [hs] at this
    exact .of_surjective IntermediateField.topEquiv.toAlgHom IntermediateField.topEquiv.surjective
  · intro _
    use Algebra.EssFiniteType.finset F E
    refine top_le_iff.mp fun x _ => ?_
    obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq (Algebra.EssFiniteType.submonoid F E) x
    have hs : s.1.1 != 0 := (IsLocalization.map_units E s).ne_zero
    have H : IsLocalization.mk' E x s = x / s := by
      simp [IsLocalization.mk'_eq_iff_eq_mul, hs]
    rw [H]
    exact div_mem (IntermediateField.algebra_adjoin_le_adjoin _ _ x.2)
      (IntermediateField.algebra_adjoin_le_adjoin _ _ s.1.2)

variable (F E) in
/--
lemma `fg_top` / 引理 `fg_top`

English:
lemma fg_top
  given: [Algebra.EssFiniteType F E]
  statement: (⊤ : IntermediateField F E).FG
  proof: by
  rwa [fg_top_iff]

中文:
引理 fg_top
  条件: [Algebra.EssFiniteType F E]
  结论: (⊤ : 整数ermediateField F E).FG
  证明: by
  rwa [fg_top_iff]

Depends on / 依赖: fg_top_iff
-/
lemma fg_top [Algebra.EssFiniteType F E] : (⊤ : IntermediateField F E).FG := by
  rwa [fg_top_iff]

/--
lemma `essFiniteType_iff` / 引理 `essFiniteType_iff`

English:
lemma essFiniteType_iff
  given: {K : IntermediateField F E}
  proof: by
  suffices (exists s : Finset E, (s : Set E) subseteq K ∧ adjoin F ↑s = K) ↔
      exists t : Finset E, adjoin F ↑t = K by
    simpa [IntermediateField.FG, (Equiv.finsetSubtypeComm _).exists_congr_left,
      ← (IntermediateField.map_injective K.val).eq_iff, ← IntermediateField.fg_top_iff,
      

中文:
引理 essFiniteType_iff
  条件: {K : 整数ermediateField F E}
  证明: by
  suffices (exists s : Finset E, (s : Set E) subseteq K ∧ adjoin F ↑s = K) ↔
      exists t : Finset E, adjoin F ↑t = K by
    simpa [IntermediateField.FG, (Equiv.finsetSubtypeComm _).exists_congr_left,
      ← (IntermediateField.map_injective K.val).eq_iff, ← IntermediateField.fg_top_iff,
      

Depends on / 依赖: AlgHom, AlgHom.fieldRange_eq_map, Equiv.finsetSubtypeComm, Finset, Function, Function.comp_def, IntermediateField, IntermediateField.FG, IntermediateField.fg_top_iff, IntermediateField.map_injective, K.val, Set.range_comp, adjoin, adjoin_map, comp_def, eq_iff, exists_congr_left, fg_top_iff, fieldRange_eq_map, finsetSubtypeComm
-/
lemma essFiniteType_iff {K : IntermediateField F E} :
    Algebra.EssFiniteType F K ↔ K.FG := by
  suffices (exists s : Finset E, (s : Set E) subseteq K ∧ adjoin F ↑s = K) ↔
      exists t : Finset E, adjoin F ↑t = K by
    simpa [IntermediateField.FG, (Equiv.finsetSubtypeComm _).exists_congr_left,
      ← (IntermediateField.map_injective K.val).eq_iff, ← IntermediateField.fg_top_iff,
      adjoin_map, ← Set.range_comp, Function.comp_def, ← AlgHom.fieldRange_eq_map] using! this
  exact ⟨fun ⟨s, _, hs⟩ => ⟨s, hs⟩, fun ⟨s, hs⟩ => ⟨s, hs ▸ subset_adjoin _ _, hs⟩⟩

/--
theorem `_root_.Field.fg_iff_essFiniteType` / 定理 `_root_.Field.fg_iff_essFiniteType`

English:
theorem _root_.Field.fg_iff_essFiniteType
  statement: Field.FG F ↔ Algebra.EssFiniteType (⊥ : Subfield F) F
  proof: Field.fg_iff_fg_top_bot.trans fg_top_iff

中文:
定理 _root_.Field.fg_iff_essFiniteType
  结论: Field.FG F ↔ Algebra.EssFiniteType (⊥ : Subfield F) F
  证明: Field.fg_iff_fg_top_bot.trans fg_top_iff

Depends on / 依赖: Field.fg_iff_fg_top_bot.trans, fg_iff_fg_top_bot, fg_top_iff
-/
theorem _root_.Field.fg_iff_essFiniteType : Field.FG F ↔ Algebra.EssFiniteType (⊥ : Subfield F) F :=
  Field.fg_iff_fg_top_bot.trans fg_top_iff

end FG

section AdjoinSimple

open Algebra

variable (α : E)

@[simp]
/--
theorem `AdjoinSimple.isIntegral_gen` / 定理 `AdjoinSimple.isIntegral_gen`

English:
theorem AdjoinSimple.isIntegral_gen
  statement: IsIntegral F (AdjoinSimple.gen F α) ↔ IsIntegral F α
  proof: by
  conv_rhs => rw [← AdjoinSimple.algebraMap_gen F α]
  rw [isIntegral_algebraMap_iff (algebraMap F⟮α⟯ E).injective]

中文:
定理 AdjoinSimple.isIntegral_gen
  结论: Is整数egral F (AdjoinSimple.gen F α) ↔ Is整数egral F α
  证明: by
  conv_rhs => rw [← AdjoinSimple.algebraMap_gen F α]
  rw [isIntegral_algebraMap_iff (algebraMap F⟮α⟯ E).injective]

Depends on / 依赖: AdjoinSimple, AdjoinSimple.algebraMap_gen, algebraMap, algebraMap_gen, conv_rhs, injective, isIntegral_algebraMap_iff
-/
theorem AdjoinSimple.isIntegral_gen : IsIntegral F (AdjoinSimple.gen F α) ↔ IsIntegral F α := by
  conv_rhs => rw [← AdjoinSimple.algebraMap_gen F α]
  rw [isIntegral_algebraMap_iff (algebraMap F⟮α⟯ E).injective]

variable {F} {α}

/--
theorem `adjoin_toSubalgebra_of_isAlgebraic` / 定理 `adjoin_toSubalgebra_of_isAlgebraic`

English:
theorem adjoin_toSubalgebra_of_isAlgebraic
  given: {S : Set E} (hS : forall x in S, IsAlgebraic F x)
  proof: adjoin_eq_algebra_adjoin _ _ fun _ =>
    (Algebra.IsIntegral.adjoin fun x hx => (hS x hx).isIntegral).inv_mem

中文:
定理 adjoin_toSubalgebra_of_isAlgebraic
  条件: {S : Set E} (hS : 对任意 x in S, IsAlgebraic F x)
  证明: adjoin_eq_algebra_adjoin _ _ fun _ =>
    (Algebra.IsIntegral.adjoin fun x hx => (hS x hx).isIntegral).inv_mem

Depends on / 依赖: Algebra, Algebra.IsIntegral.adjoin, IsIntegral, adjoin, adjoin_eq_algebra_adjoin, inv_mem, isIntegral
-/
theorem adjoin_toSubalgebra_of_isAlgebraic {S : Set E} (hS : forall x in S, IsAlgebraic F x) :
    (adjoin F S).toSubalgebra = Algebra.adjoin F S :=
  adjoin_eq_algebra_adjoin _ _ fun _ =>
    (Algebra.IsIntegral.adjoin fun x hx => (hS x hx).isIntegral).inv_mem

/--
theorem `adjoin_simple_toSubalgebra_of_isAlgebraic` / 定理 `adjoin_simple_toSubalgebra_of_isAlgebraic`

English:
theorem adjoin_simple_toSubalgebra_of_isAlgebraic
  given: (hα : IsAlgebraic F α)
  proof: adjoin_toSubalgebra_of_isAlgebraic by simpa

@[simp]

中文:
定理 adjoin_simple_toSubalgebra_of_isAlgebraic
  条件: (hα : IsAlgebraic F α)
  证明: adjoin_toSubalgebra_of_isAlgebraic by simpa

@[simp]

Depends on / 依赖: adjoin_toSubalgebra_of_isAlgebraic
-/
theorem adjoin_simple_toSubalgebra_of_isAlgebraic (hα : IsAlgebraic F α) :
    F⟮α⟯.toSubalgebra = F[α] :=
adjoin_toSubalgebra_of_isAlgebraic by simpa

@[simp]
/--
theorem `adjoin_toSubalgebra` / 定理 `adjoin_toSubalgebra`

English:
theorem adjoin_toSubalgebra
  given: [Algebra.IsAlgebraic F E] (S : Set E)
  proof: adjoin_toSubalgebra_of_isAlgebraic fun x _ => Algebra.IsAlgebraic.isAlgebraic x

中文:
定理 adjoin_toSubalgebra
  条件: [Algebra.IsAlgebraic F E] (S : Set E)
  证明: adjoin_toSubalgebra_of_isAlgebraic fun x _ => Algebra.IsAlgebraic.isAlgebraic x

Depends on / 依赖: Algebra, Algebra.IsAlgebraic.isAlgebraic, IsAlgebraic, adjoin_toSubalgebra_of_isAlgebraic, isAlgebraic
-/
theorem adjoin_toSubalgebra [Algebra.IsAlgebraic F E] (S : Set E) :
    (adjoin F S).toSubalgebra = Algebra.adjoin F S :=
  adjoin_toSubalgebra_of_isAlgebraic fun x _ => Algebra.IsAlgebraic.isAlgebraic x

/--
theorem `adjoin_eq_top_iff_of_isAlgebraic` / 定理 `adjoin_eq_top_iff_of_isAlgebraic`

English:
theorem adjoin_eq_top_iff_of_isAlgebraic
  given: {S : Set E} (hS : forall x in S, IsAlgebraic F x)
  proof: by
  rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic hS]; rw [← IntermediateField.toSubalgebra_inj]; rw [IntermediateField.top_toSubalgebra]

alias ⟨_root_.Algebra.adjoin_eq_top_of_intermediateField, _⟩ := adjoin_eq_top_iff_of_isAlgebraic

中文:
定理 adjoin_eq_top_iff_of_isAlgebraic
  条件: {S : Set E} (hS : 对任意 x in S, IsAlgebraic F x)
  证明: by
  rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic hS]; rw [← IntermediateField.toSubalgebra_inj]; rw [IntermediateField.top_toSubalgebra]

alias ⟨_root_.Algebra.adjoin_eq_top_of_intermediateField, _⟩ := adjoin_eq_top_iff_of_isAlgebraic

Depends on / 依赖: IntermediateField, IntermediateField.adjoin_toSubalgebra_of_isAlgebraic, IntermediateField.toSubalgebra_inj, IntermediateField.top_toSubalgebra, adjoin_toSubalgebra_of_isAlgebraic, toSubalgebra_inj, top_toSubalgebra
-/
theorem adjoin_eq_top_iff_of_isAlgebraic {S : Set E} (hS : forall x in S, IsAlgebraic F x) :
    adjoin F S = ⊤ ↔ Algebra.adjoin F S = ⊤ := by
  rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic hS]; rw [← IntermediateField.toSubalgebra_inj]; rw [IntermediateField.top_toSubalgebra]

alias ⟨_root_.Algebra.adjoin_eq_top_of_intermediateField, _⟩ := adjoin_eq_top_iff_of_isAlgebraic

/--
theorem `adjoin_simple_eq_top_iff_of_isAlgebraic` / 定理 `adjoin_simple_eq_top_iff_of_isAlgebraic`

English:
theorem adjoin_simple_eq_top_iff_of_isAlgebraic
  given: {x : E} (hx : IsAlgebraic F x)
  proof: adjoin_eq_top_iff_of_isAlgebraic (by simp [hx])

alias ⟨_root_.Algebra.adjoin_eq_top_of_primitive_element, _⟩ :=
  adjoin_simple_eq_top_iff_of_isAlgebraic

@[simp]

中文:
定理 adjoin_simple_eq_top_iff_of_isAlgebraic
  条件: {x : E} (hx : IsAlgebraic F x)
  证明: adjoin_eq_top_iff_of_isAlgebraic (by simp [hx])

alias ⟨_root_.Algebra.adjoin_eq_top_of_primitive_element, _⟩ :=
  adjoin_simple_eq_top_iff_of_isAlgebraic

@[simp]

Depends on / 依赖: adjoin_eq_top_iff_of_isAlgebraic
-/
theorem adjoin_simple_eq_top_iff_of_isAlgebraic {x : E} (hx : IsAlgebraic F x) :
    F⟮x⟯ = ⊤ ↔ F[x] = ⊤ := adjoin_eq_top_iff_of_isAlgebraic (by simp [hx])

alias ⟨_root_.Algebra.adjoin_eq_top_of_primitive_element, _⟩ :=
  adjoin_simple_eq_top_iff_of_isAlgebraic

@[simp]
/--
theorem `adjoin_eq_top_iff` / 定理 `adjoin_eq_top_iff`

English:
theorem adjoin_eq_top_iff
  given: [Algebra.IsAlgebraic F E] {S : Set E}
  proof: adjoin_eq_top_iff_of_isAlgebraic (fun x _ => Algebra.IsAlgebraic.isAlgebraic x)

中文:
定理 adjoin_eq_top_iff
  条件: [Algebra.IsAlgebraic F E] {S : Set E}
  证明: adjoin_eq_top_iff_of_isAlgebraic (fun x _ => Algebra.IsAlgebraic.isAlgebraic x)

Depends on / 依赖: Algebra, Algebra.IsAlgebraic.isAlgebraic, IsAlgebraic, adjoin_eq_top_iff_of_isAlgebraic, isAlgebraic
-/
theorem adjoin_eq_top_iff [Algebra.IsAlgebraic F E] {S : Set E} :
    adjoin F S = ⊤ ↔ Algebra.adjoin F S = ⊤ :=
  adjoin_eq_top_iff_of_isAlgebraic (fun x _ => Algebra.IsAlgebraic.isAlgebraic x)

/--
lemma `_root_.Algebra.finite_of_essFiniteType_of_isAlgebraic` / 引理 `_root_.Algebra.finite_of_essFiniteType_of_isAlgebraic`

English:
lemma _root_.Algebra.finite_of_essFiniteType_of_isAlgebraic
  proof: by
  obtain ⟨s, hs⟩ := fg_top F E
  have : Algebra.FiniteType F E := by
    use s
    rw [← adjoin_toSubalgebra_of_isAlgebraic fun x hx => Algebra.IsAlgebraic.isAlgebraic x]
    simpa [← toSubalgebra_inj] using hs
  exact Algebra.IsIntegral.finite

中文:
引理 _root_.Algebra.finite_of_essFiniteType_of_isAlgebraic
  证明: by
  obtain ⟨s, hs⟩ := fg_top F E
  have : Algebra.FiniteType F E := by
    use s
    rw [← adjoin_toSubalgebra_of_isAlgebraic fun x hx => Algebra.IsAlgebraic.isAlgebraic x]
    simpa [← toSubalgebra_inj] using hs
  exact Algebra.IsIntegral.finite

Depends on / 依赖: Algebra, Algebra.FiniteType, Algebra.IsAlgebraic.isAlgebraic, Algebra.IsIntegral.finite, FiniteType, IsAlgebraic, IsIntegral, adjoin_toSubalgebra_of_isAlgebraic, fg_top, finite, isAlgebraic, toSubalgebra_inj
-/
lemma _root_.Algebra.finite_of_essFiniteType_of_isAlgebraic
    [Algebra.EssFiniteType F E] [Algebra.IsAlgebraic F E] :
    Module.Finite F E := by
  obtain ⟨s, hs⟩ := fg_top F E
  have : Algebra.FiniteType F E := by
    use s
    rw [← adjoin_toSubalgebra_of_isAlgebraic fun x hx => Algebra.IsAlgebraic.isAlgebraic x]
    simpa [← toSubalgebra_inj] using hs
  exact Algebra.IsIntegral.finite

section RingHom

variable {A B C : Type*} [Field A] [CommSemiring B] [Field C] [Algebra A B]
  [Algebra B C] [Algebra A C] [IsScalarTower A B C] (b : B)

/--
Definition of `RingHom.adjoinAlgebraMapOfAlgebra` / `RingHom.adjoinAlgebraMapOfAlgebra` 的定义

English:
definition RingHom.adjoinAlgebraMapOfAlgebra
  signature: :
  body: RingHom.comp (Subalgebra.inclusion <|
    algebra_adjoin_le_adjoin A {((algebraMap B C) b)}).toRingHom
    (Algebra.RingHom.adjoinAlgebraMap b)

中文:
定义 RingHom.adjoinAlgebraMapOfAlgebra
  签名: :
  定义体: RingHom.comp (Subalgebra.inclusion <|
    algebra_adjoin_le_adjoin A {((algebraMap B C) b)}).toRingHom
    (Algebra.RingHom.adjoinAlgebraMap b)

Depends on / 依赖: Algebra, Algebra.RingHom.adjoinAlgebraMap, RingHom, RingHom.comp, Subalgebra, Subalgebra.inclusion, adjoinAlgebraMap, algebraMap, algebra_adjoin_le_adjoin, inclusion, toRingHom
-/
noncomputable def RingHom.adjoinAlgebraMapOfAlgebra :
    A[b] ->+* A⟮((algebraMap B C) b)⟯ :=
  RingHom.comp (Subalgebra.inclusion <|
    algebra_adjoin_le_adjoin A {((algebraMap B C) b)}).toRingHom
    (Algebra.RingHom.adjoinAlgebraMap b)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Algebra (A[b]) A⟮(algebraMap B C) b⟯
  body: RingHom.toAlgebra (RingHom.adjoinAlgebraMapOfAlgebra _)

中文:
实例 :
  签名: Algebra (A[b]) A⟮(algebraMap B C) b⟯
  定义体: RingHom.toAlgebra (RingHom.adjoinAlgebraMapOfAlgebra _)

Depends on / 依赖: RingHom, RingHom.adjoinAlgebraMapOfAlgebra, RingHom.toAlgebra, adjoinAlgebraMapOfAlgebra, toAlgebra
-/
noncomputable instance : Algebra (A[b]) A⟮(algebraMap B C) b⟯ :=
  RingHom.toAlgebra (RingHom.adjoinAlgebraMapOfAlgebra _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsScalarTower (A[b]) A⟮(algebraMap B C) b⟯ C
  body: IsScalarTower.of_algebraMap_eq' rfl

中文:
实例 :
  签名: IsScalarTower (A[b]) A⟮(algebraMap B C) b⟯ C
  定义体: IsScalarTower.of_algebraMap_eq' rfl

Depends on / 依赖: IsScalarTower, IsScalarTower.of_algebraMap_eq, of_algebraMap_eq
-/
instance : IsScalarTower (A[b]) A⟮(algebraMap B C) b⟯ C :=
  IsScalarTower.of_algebraMap_eq' rfl

end RingHom

section Supremum

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (E1 E2 : IntermediateField K L)

/--
theorem `le_sup_toSubalgebra` / 定理 `le_sup_toSubalgebra`

English:
theorem le_sup_toSubalgebra
  statement: E1.toSubalgebra ⊔ E2.toSubalgebra <= (E1 ⊔ E2).toSubalgebra
  proof: sup_le (show E1 <= E1 ⊔ E2 from le_sup_left) (show E2 <= E1 ⊔ E2 from le_sup_right)

中文:
定理 le_sup_toSubalgebra
  结论: E1.toSubalgebra ⊔ E2.toSubalgebra <= (E1 ⊔ E2).toSubalgebra
  证明: sup_le (show E1 <= E1 ⊔ E2 from le_sup_left) (show E2 <= E1 ⊔ E2 from le_sup_right)

Depends on / 依赖: le_sup_left, le_sup_right, sup_le
-/
theorem le_sup_toSubalgebra : E1.toSubalgebra ⊔ E2.toSubalgebra <= (E1 ⊔ E2).toSubalgebra :=
  sup_le (show E1 <= E1 ⊔ E2 from le_sup_left) (show E2 <= E1 ⊔ E2 from le_sup_right)

/--
theorem `sup_toSubalgebra_of_isAlgebraic_right` / 定理 `sup_toSubalgebra_of_isAlgebraic_right`

English:
theorem sup_toSubalgebra_of_isAlgebraic_right
  given: [Algebra.IsAlgebraic K E2]
  proof: by
  have : (adjoin E1 (E2 : Set L)).toSubalgebra = _ := adjoin_toSubalgebra_of_isAlgebraic fun x h =>
    IsAlgebraic.tower_top _ (isAlgebraic_iff.mp (Algebra.IsAlgebraic.isAlgebraic (⟨x, h⟩ : E2)))
  apply_fun Subalgebra.restrictScalars K at this
  rw [← restrictScalars_toSubalgebra]; rw [restrict

中文:
定理 sup_toSubalgebra_of_isAlgebraic_right
  条件: [Algebra.IsAlgebraic K E2]
  证明: by
  have : (adjoin E1 (E2 : Set L)).toSubalgebra = _ := adjoin_toSubalgebra_of_isAlgebraic fun x h =>
    IsAlgebraic.tower_top _ (isAlgebraic_iff.mp (Algebra.IsAlgebraic.isAlgebraic (⟨x, h⟩ : E2)))
  apply_fun Subalgebra.restrictScalars K at this
  rw [← restrictScalars_toSubalgebra]; rw [restrict

Depends on / 依赖: Algebra, Algebra.IsAlgebraic.isAlgebraic, IsAlgebraic, IsAlgebraic.tower_top, Subalgebra, Subalgebra.restrictScalars, adjoin, adjoin_toSubalgebra_of_isAlgebraic, apply_fun, isAlgebraic, isAlgebraic_iff, isAlgebraic_iff.mp, restrictScalars, restrictScalars_adjoin, restrictScalars_toSubalgebra, toSubalgebra, tower_top
-/
theorem sup_toSubalgebra_of_isAlgebraic_right [Algebra.IsAlgebraic K E2] :
    (E1 ⊔ E2).toSubalgebra = E1.toSubalgebra ⊔ E2.toSubalgebra := by
  have : (adjoin E1 (E2 : Set L)).toSubalgebra = _ := adjoin_toSubalgebra_of_isAlgebraic fun x h =>
    IsAlgebraic.tower_top _ (isAlgebraic_iff.mp (Algebra.IsAlgebraic.isAlgebraic (⟨x, h⟩ : E2)))
  apply_fun Subalgebra.restrictScalars K at this
  rw [← restrictScalars_toSubalgebra]; rw [restrictScalars_adjoin] at this
  -- TODO: rather than using `← coe_type_toSubalgebra` here, perhaps we should restate another
  -- version of `Algebra.restrictScalars_adjoin` for intermediate fields?
  simp only [← coe_type_toSubalgebra] at this
  rw [Algebra.restrictScalars_adjoin] at this
  exact this

/--
theorem `sup_toSubalgebra_of_isAlgebraic_left` / 定理 `sup_toSubalgebra_of_isAlgebraic_left`

English:
theorem sup_toSubalgebra_of_isAlgebraic_left
  given: [Algebra.IsAlgebraic K E1]
  proof: by
  have := sup_toSubalgebra_of_isAlgebraic_right E2 E1
  rwa [sup_comm (a := E1), sup_comm (a := E1.toSubalgebra)]

中文:
定理 sup_toSubalgebra_of_isAlgebraic_left
  条件: [Algebra.IsAlgebraic K E1]
  证明: by
  have := sup_toSubalgebra_of_isAlgebraic_right E2 E1
  rwa [sup_comm (a := E1), sup_comm (a := E1.toSubalgebra)]

Depends on / 依赖: E1.toSubalgebra, sup_comm, sup_toSubalgebra_of_isAlgebraic_right, toSubalgebra
-/
theorem sup_toSubalgebra_of_isAlgebraic_left [Algebra.IsAlgebraic K E1] :
    (E1 ⊔ E2).toSubalgebra = E1.toSubalgebra ⊔ E2.toSubalgebra := by
  have := sup_toSubalgebra_of_isAlgebraic_right E2 E1
  rwa [sup_comm (a := E1), sup_comm (a := E1.toSubalgebra)]

/--
theorem `sup_toSubalgebra_of_isAlgebraic` / 定理 `sup_toSubalgebra_of_isAlgebraic`

English:
theorem sup_toSubalgebra_of_isAlgebraic
  proof: halg.elim (fun _ => sup_toSubalgebra_of_isAlgebraic_left E1 E2)
    (fun _ => sup_toSubalgebra_of_isAlgebraic_right E1 E2)

中文:
定理 sup_toSubalgebra_of_isAlgebraic
  证明: halg.elim (fun _ => sup_toSubalgebra_of_isAlgebraic_left E1 E2)
    (fun _ => sup_toSubalgebra_of_isAlgebraic_right E1 E2)

Depends on / 依赖: halg.elim, sup_toSubalgebra_of_isAlgebraic_left, sup_toSubalgebra_of_isAlgebraic_right
-/
theorem sup_toSubalgebra_of_isAlgebraic
    (halg : Algebra.IsAlgebraic K E1 ∨ Algebra.IsAlgebraic K E2) :
    (E1 ⊔ E2).toSubalgebra = E1.toSubalgebra ⊔ E2.toSubalgebra :=
  halg.elim (fun _ => sup_toSubalgebra_of_isAlgebraic_left E1 E2)
    (fun _ => sup_toSubalgebra_of_isAlgebraic_right E1 E2)

/--
theorem `sup_toSubalgebra_of_left` / 定理 `sup_toSubalgebra_of_left`

English:
theorem sup_toSubalgebra_of_left
  given: [FiniteDimensional K E1]
  proof: sup_toSubalgebra_of_isAlgebraic_left E1 E2

中文:
定理 sup_toSubalgebra_of_left
  条件: [FiniteDimensional K E1]
  证明: sup_toSubalgebra_of_isAlgebraic_left E1 E2

Depends on / 依赖: sup_toSubalgebra_of_isAlgebraic_left
-/
theorem sup_toSubalgebra_of_left [FiniteDimensional K E1] :
    (E1 ⊔ E2).toSubalgebra = E1.toSubalgebra ⊔ E2.toSubalgebra :=
  sup_toSubalgebra_of_isAlgebraic_left E1 E2

/--
theorem `sup_toSubalgebra_of_right` / 定理 `sup_toSubalgebra_of_right`

English:
theorem sup_toSubalgebra_of_right
  given: [FiniteDimensional K E2]
  proof: sup_toSubalgebra_of_isAlgebraic_right E1 E2

中文:
定理 sup_toSubalgebra_of_right
  条件: [FiniteDimensional K E2]
  证明: sup_toSubalgebra_of_isAlgebraic_right E1 E2

Depends on / 依赖: sup_toSubalgebra_of_isAlgebraic_right
-/
theorem sup_toSubalgebra_of_right [FiniteDimensional K E2] :
    (E1 ⊔ E2).toSubalgebra = E1.toSubalgebra ⊔ E2.toSubalgebra :=
  sup_toSubalgebra_of_isAlgebraic_right E1 E2

end Supremum

section Tower

variable (E)
variable {K : Type*} [Field K] [Algebra F K] [Algebra E K] [IsScalarTower F E K]

/--
theorem `adjoin_intermediateField_toSubalgebra_of_isAlgebraic` / 定理 `adjoin_intermediateField_toSubalgebra_of_isAlgebraic`

English:
theorem adjoin_intermediateField_toSubalgebra_of_isAlgebraic
  statement: (L : IntermediateField F K)
  proof: by
  let i := IsScalarTower.toAlgHom F E K
  let E' := i.fieldRange
  let i' : E ≃ₐ[F] E' := AlgEquiv.ofInjectiveField i
  have hi : algebraMap E K = (algebraMap E' K) ∘ i' := by ext x; rfl
  apply_fun _ using Subalgebra.restrictScalars_injective F
  rw [← restrictScalars_toSubalgebra]; rw [restrict

中文:
定理 adjoin_intermediateField_toSubalgebra_of_isAlgebraic
  结论: (L : 整数ermediateField F K)
  证明: by
  let i := IsScalarTower.toAlgHom F E K
  let E' := i.fieldRange
  let i' : E ≃ₐ[F] E' := AlgEquiv.ofInjectiveField i
  have hi : algebraMap E K = (algebraMap E' K) ∘ i' := by ext x; rfl
  apply_fun _ using Subalgebra.restrictScalars_injective F
  rw [← restrictScalars_toSubalgebra]; rw [restrict

Depends on / 依赖: AlgEquiv, AlgEquiv.ofInjectiveField, Algebra, Algebra.restrictScalars_adjoin, Algebra.restrictScalars_adjoin_of_algEquiv, IsScalarTower, IsScalarTower.toAlgHom, Subalgebra, Subalgebra.restrictScalars_injective, algebraMap, apply_fun, coe_type_toSubalgebra, fieldRange, i.fieldRange, ofInjectiveField, restrictScalars_adjoin, restrictScalars_adjoin_of_algEquiv, restrictScalars_injective, restrictScalars_toSubalgebra, toAlgHom
-/
theorem adjoin_intermediateField_toSubalgebra_of_isAlgebraic (L : IntermediateField F K)
    (halg : Algebra.IsAlgebraic F E ∨ Algebra.IsAlgebraic F L) :
    (adjoin E (L : Set K)).toSubalgebra = Algebra.adjoin E (L : Set K) := by
  let i := IsScalarTower.toAlgHom F E K
  let E' := i.fieldRange
  let i' : E ≃ₐ[F] E' := AlgEquiv.ofInjectiveField i
  have hi : algebraMap E K = (algebraMap E' K) ∘ i' := by ext x; rfl
  apply_fun _ using Subalgebra.restrictScalars_injective F
  rw [← restrictScalars_toSubalgebra]; rw [restrictScalars_adjoin_of_algEquiv i' hi]; rw [Algebra.restrictScalars_adjoin_of_algEquiv i' hi]; rw [restrictScalars_adjoin]
  dsimp only [← E'.coe_type_toSubalgebra]
  rw [Algebra.restrictScalars_adjoin F E'.toSubalgebra]
  exact E'.sup_toSubalgebra_of_isAlgebraic L (halg.imp
    (fun (_ : Algebra.IsAlgebraic F E) => i'.isAlgebraic) id)

/--
theorem `adjoin_intermediateField_toSubalgebra_of_isAlgebraic_left` / 定理 `adjoin_intermediateField_toSubalgebra_of_isAlgebraic_left`

English:
theorem adjoin_intermediateField_toSubalgebra_of_isAlgebraic_left
  statement: (L : IntermediateField F K)
  proof: adjoin_intermediateField_toSubalgebra_of_isAlgebraic E L (Or.inl halg)

中文:
定理 adjoin_intermediateField_toSubalgebra_of_isAlgebraic_left
  结论: (L : 整数ermediateField F K)
  证明: adjoin_intermediateField_toSubalgebra_of_isAlgebraic E L (Or.inl halg)

Depends on / 依赖: Or.inl, adjoin_intermediateField_toSubalgebra_of_isAlgebraic
-/
theorem adjoin_intermediateField_toSubalgebra_of_isAlgebraic_left (L : IntermediateField F K)
    [halg : Algebra.IsAlgebraic F E] :
    (adjoin E (L : Set K)).toSubalgebra = Algebra.adjoin E (L : Set K) :=
  adjoin_intermediateField_toSubalgebra_of_isAlgebraic E L (Or.inl halg)

/--
theorem `adjoin_intermediateField_toSubalgebra_of_isAlgebraic_right` / 定理 `adjoin_intermediateField_toSubalgebra_of_isAlgebraic_right`

English:
theorem adjoin_intermediateField_toSubalgebra_of_isAlgebraic_right
  statement: (L : IntermediateField F K)
  proof: adjoin_intermediateField_toSubalgebra_of_isAlgebraic E L (Or.inr halg)

中文:
定理 adjoin_intermediateField_toSubalgebra_of_isAlgebraic_right
  结论: (L : 整数ermediateField F K)
  证明: adjoin_intermediateField_toSubalgebra_of_isAlgebraic E L (Or.inr halg)

Depends on / 依赖: Or.inr, adjoin_intermediateField_toSubalgebra_of_isAlgebraic
-/
theorem adjoin_intermediateField_toSubalgebra_of_isAlgebraic_right (L : IntermediateField F K)
    [halg : Algebra.IsAlgebraic F L] :
    (adjoin E (L : Set K)).toSubalgebra = Algebra.adjoin E (L : Set K) :=
  adjoin_intermediateField_toSubalgebra_of_isAlgebraic E L (Or.inr halg)

end Tower

end AdjoinSimple

end AdjoinDef

section Induction

variable {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E]

/--
theorem `fg_of_fg_toSubalgebra` / 定理 `fg_of_fg_toSubalgebra`

English:
theorem fg_of_fg_toSubalgebra
  given: (S : IntermediateField F E) (h : S.toSubalgebra.FG)
  statement: S.FG
  proof: by
  obtain ⟨t, ht⟩ := h
  exact ⟨t, (eq_adjoin_of_eq_algebra_adjoin _ _ _ ht.symm).symm⟩

中文:
定理 fg_of_fg_toSubalgebra
  条件: (S : 整数ermediateField F E) (h : S.toSubalgebra.FG)
  结论: S.FG
  证明: by
  obtain ⟨t, ht⟩ := h
  exact ⟨t, (eq_adjoin_of_eq_algebra_adjoin _ _ _ ht.symm).symm⟩

Depends on / 依赖: eq_adjoin_of_eq_algebra_adjoin, ht.symm
-/
theorem fg_of_fg_toSubalgebra (S : IntermediateField F E) (h : S.toSubalgebra.FG) : S.FG := by
  obtain ⟨t, ht⟩ := h
  exact ⟨t, (eq_adjoin_of_eq_algebra_adjoin _ _ _ ht.symm).symm⟩

/--
theorem `fg_of_noetherian` / 定理 `fg_of_noetherian`

English:
theorem fg_of_noetherian
  given: (S : IntermediateField F E) [IsNoetherian F E]
  statement: S.FG
  proof: S.fg_of_fg_toSubalgebra S.toSubalgebra.fg_of_noetherian

中文:
定理 fg_of_noetherian
  条件: (S : 整数ermediateField F E) [IsNoetherian F E]
  结论: S.FG
  证明: S.fg_of_fg_toSubalgebra S.toSubalgebra.fg_of_noetherian

Depends on / 依赖: S.fg_of_fg_toSubalgebra, S.toSubalgebra.fg_of_noetherian, fg_of_fg_toSubalgebra, fg_of_noetherian, toSubalgebra
-/
theorem fg_of_noetherian (S : IntermediateField F E) [IsNoetherian F E] : S.FG :=
  S.fg_of_fg_toSubalgebra S.toSubalgebra.fg_of_noetherian

/--
theorem `induction_on_adjoin` / 定理 `induction_on_adjoin`

English:
theorem induction_on_adjoin
  statement: [FiniteDimensional F E] (P : IntermediateField F E -> Prop)
  proof: letI : IsNoetherian F E := IsNoetherian.iff_fg.2 inferInstance
  induction_on_adjoin_fg P base ih K K.fg_of_noetherian

中文:
定理 induction_on_adjoin
  结论: [FiniteDimensional F E] (P : 整数ermediateField F E -> 命题)
  证明: letI : IsNoetherian F E := IsNoetherian.iff_fg.2 inferInstance
  induction_on_adjoin_fg P base ih K K.fg_of_noetherian

Depends on / 依赖: IsNoetherian, IsNoetherian.iff_fg, K.fg_of_noetherian, fg_of_noetherian, iff_fg, induction_on_adjoin_fg
-/
theorem induction_on_adjoin [FiniteDimensional F E] (P : IntermediateField F E -> Prop)
    (base : P ⊥) (ih : forall (K : IntermediateField F E) (x : E), P K -> P (K⟮x⟯.restrictScalars F))
    (K : IntermediateField F E) : P K :=
  letI : IsNoetherian F E := IsNoetherian.iff_fg.2 inferInstance
  induction_on_adjoin_fg P base ih K K.fg_of_noetherian

end Induction

end IntermediateField

namespace IsFractionRing

variable {F A K L : Type*} [Field F] [CommRing A] [Algebra F A]
  [Field K] [Algebra F K] [Algebra A K] [IsFractionRing A K] [Field L] [Algebra F L]
  {g : A ->ₐ[F] L} {f : K ->ₐ[F] L}

/--
theorem `algHom_fieldRange_eq_of_comp_eq` / 定理 `algHom_fieldRange_eq_of_comp_eq`

English:
theorem algHom_fieldRange_eq_of_comp_eq
  given: (h : RingHom.comp f (algebraMap A K) = (g : A ->+* L))
  proof: by
  apply IntermediateField.toSubfield_injective
  simp_rw [AlgHom.fieldRange_toSubfield, IntermediateField.adjoin_toSubfield]
  convert! ringHom_fieldRange_eq_of_comp_eq h using 2
  exact Set.union_eq_self_of_subset_left fun _ ⟨x, hx⟩ => ⟨algebraMap F A x, by simp [← hx]⟩

中文:
定理 algHom_fieldRange_eq_of_comp_eq
  条件: (h : RingHom.comp f (algebraMap A K) = (g : A ->+* L))
  证明: by
  apply IntermediateField.toSubfield_injective
  simp_rw [AlgHom.fieldRange_toSubfield, IntermediateField.adjoin_toSubfield]
  convert! ringHom_fieldRange_eq_of_comp_eq h using 2
  exact Set.union_eq_self_of_subset_left fun _ ⟨x, hx⟩ => ⟨algebraMap F A x, by simp [← hx]⟩

Depends on / 依赖: AlgHom, AlgHom.fieldRange_toSubfield, IntermediateField, IntermediateField.adjoin_toSubfield, IntermediateField.toSubfield_injective, Set.union_eq_self_of_subset_left, adjoin_toSubfield, algebraMap, convert, fieldRange_toSubfield, ringHom_fieldRange_eq_of_comp_eq, simp_rw, toSubfield_injective, union_eq_self_of_subset_left
-/
theorem algHom_fieldRange_eq_of_comp_eq (h : RingHom.comp f (algebraMap A K) = (g : A ->+* L)) :
    f.fieldRange = IntermediateField.adjoin F g.range := by
  apply IntermediateField.toSubfield_injective
  simp_rw [AlgHom.fieldRange_toSubfield, IntermediateField.adjoin_toSubfield]
  convert! ringHom_fieldRange_eq_of_comp_eq h using 2
  exact Set.union_eq_self_of_subset_left fun _ ⟨x, hx⟩ => ⟨algebraMap F A x, by simp [← hx]⟩

/--
theorem `algHom_fieldRange_eq_of_comp_eq_of_range_eq` / 定理 `algHom_fieldRange_eq_of_comp_eq_of_range_eq`

English:
theorem algHom_fieldRange_eq_of_comp_eq_of_range_eq
  proof: by
  apply IntermediateField.toSubfield_injective
  simp_rw [AlgHom.fieldRange_toSubfield, IntermediateField.adjoin_toSubfield]
  refine ringHom_fieldRange_eq_of_comp_eq_of_range_eq h ?_
  rw [← Algebra.adjoin_eq_ring_closure]; rw [← hs]; rfl

中文:
定理 algHom_fieldRange_eq_of_comp_eq_of_range_eq
  证明: by
  apply IntermediateField.toSubfield_injective
  simp_rw [AlgHom.fieldRange_toSubfield, IntermediateField.adjoin_toSubfield]
  refine ringHom_fieldRange_eq_of_comp_eq_of_range_eq h ?_
  rw [← Algebra.adjoin_eq_ring_closure]; rw [← hs]; rfl

Depends on / 依赖: AlgHom, AlgHom.fieldRange_toSubfield, Algebra, Algebra.adjoin_eq_ring_closure, IntermediateField, IntermediateField.adjoin_toSubfield, IntermediateField.toSubfield_injective, adjoin_eq_ring_closure, adjoin_toSubfield, fieldRange_toSubfield, ringHom_fieldRange_eq_of_comp_eq_of_range_eq, simp_rw, toSubfield_injective
-/
theorem algHom_fieldRange_eq_of_comp_eq_of_range_eq
    (h : RingHom.comp f (algebraMap A K) = (g : A ->+* L))
    {s : Set L} (hs : g.range = Algebra.adjoin F s) :
    f.fieldRange = IntermediateField.adjoin F s := by
  apply IntermediateField.toSubfield_injective
  simp_rw [AlgHom.fieldRange_toSubfield, IntermediateField.adjoin_toSubfield]
  refine ringHom_fieldRange_eq_of_comp_eq_of_range_eq h ?_
  rw [← Algebra.adjoin_eq_ring_closure]; rw [← hs]; rfl

variable [IsScalarTower F A K]

/--
theorem `liftAlgHom_fieldRange` / 定理 `liftAlgHom_fieldRange`

English:
theorem liftAlgHom_fieldRange
  given: (hg : Function.Injective g)
  proof: algHom_fieldRange_eq_of_comp_eq (by ext; simp)

中文:
定理 liftAlgHom_fieldRange
  条件: (hg : Function.Injective g)
  证明: algHom_fieldRange_eq_of_comp_eq (by ext; simp)

Depends on / 依赖: algHom_fieldRange_eq_of_comp_eq
-/
theorem liftAlgHom_fieldRange (hg : Function.Injective g) :
    (liftAlgHom hg : K ->ₐ[F] L).fieldRange = IntermediateField.adjoin F g.range :=
  algHom_fieldRange_eq_of_comp_eq (by ext; simp)

/--
theorem `liftAlgHom_fieldRange_eq_of_range_eq` / 定理 `liftAlgHom_fieldRange_eq_of_range_eq`

English:
theorem liftAlgHom_fieldRange_eq_of_range_eq
  statement: (hg : Function.Injective g)
  proof: algHom_fieldRange_eq_of_comp_eq_of_range_eq (by ext; simp) hs

中文:
定理 liftAlgHom_fieldRange_eq_of_range_eq
  结论: (hg : Function.Injective g)
  证明: algHom_fieldRange_eq_of_comp_eq_of_range_eq (by ext; simp) hs

Depends on / 依赖: algHom_fieldRange_eq_of_comp_eq_of_range_eq
-/
theorem liftAlgHom_fieldRange_eq_of_range_eq (hg : Function.Injective g)
    {s : Set L} (hs : g.range = Algebra.adjoin F s) :
    (liftAlgHom hg : K ->ₐ[F] L).fieldRange = IntermediateField.adjoin F s :=
  algHom_fieldRange_eq_of_comp_eq_of_range_eq (by ext; simp) hs

end IsFractionRing
