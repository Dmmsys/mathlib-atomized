/-
Copyright (c) 2024 Paul Reichert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.IsConnected
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.HomCongr

/-!
# Colimits of connected index categories

This file proves two characterizations of connected categories by means of colimits.

## Characterization of connected categories by means of the unit-valued functor

First, it is proved that a category `C` is connected if and only if `colim F` is a singleton,
where `F : C ⥤ Type w` and `F.obj _ = PUnit` (for arbitrary `w`).

See `isConnected_iff_colimit_constPUnitFunctor_iso_pUnit` for the proof of this characterization and
`constPUnitFunctor` for the definition of the constant functor used in the statement. A formulation
based on `IsColimit` instead of `colimit` is given in `isConnected_iff_isColimit_pUnitCocone`.

The `if` direction is also available directly in several formulations:
For connected index categories `C`, `PUnit.{w}` is a colimit of the `constPUnitFunctor`, where `w`
is arbitrary. See `instHasColimitConstPUnitFunctor`, `isColimitPUnitCocone` and
`colimitConstPUnitIsoPUnit`.

## Final functors preserve connectedness of categories (in both directions)

`isConnected_iff_of_final` proves that the domain of a final functor is connected if and only if
its codomain is connected.

## Tags

unit-valued, singleton, colimit
-/

@[expose] public section

universe w v u

namespace CategoryTheory

namespace Limits.Types

variable (C : Type u) [Category.{v} C]

/--
Definition of `constPUnitFunctor` / `constPUnitFunctor` 的定义

English:
definition constPUnitFunctor
  signature: : C ⥤ Type w
  body: (Functor.const C).obj PUnit.{w + 1}

中文:
定义 constPUnitFunctor
  签名: : C ⥤ 类型 w
  定义体: (Functor.const C).obj PUnit.{w + 1}

Depends on / 依赖: Functor, Functor.const
-/
def constPUnitFunctor : C ⥤ Type w := (Functor.const C).obj PUnit.{w + 1}

/-- The cocone on `constPUnitFunctor` with cone point `PUnit`. -/
@[simps]
/--
Definition of `pUnitCocone` / `pUnitCocone` 的定义

English:
definition pUnitCocone
  signature: : Cocone (constPUnitFunctor.{w} C) where
  body: PUnit
  ι := 𝟙 _

中文:
定义 pUnitCocone
  签名: : 余锥 (constPUnitFunctor.{w} C) where
  定义体: PUnit
  ι := 𝟙 _
-/
def pUnitCocone : Cocone (constPUnitFunctor.{w} C) where
  pt := PUnit
  ι := 𝟙 _

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isColimitPUnitCocone` / `isColimitPUnitCocone` 的定义

English:
definition isColimitPUnitCocone
  signature: [IsConnected C]
  body: s.ι.app Classical.ofNonempty
  fac s j := by
    ext ⟨⟩
    refine constant_of_preserves_morphisms (α := s.pt)
      (fun (k : C) => s.ι.app k PUnit.unit) ?_ Classical.ofNonempty j
    intro X Y f
    exact ConcreteCategory.congr_hom (s.ι.naturality f).symm PUnit.unit
  uniq s m h := by
    ext ⟨⟩
    simp [← h Classical.ofNonempty]

中文:
定义 isColimitPUnitCocone
  签名: [是连通 C]
  定义体: s.ι.app Classical.ofNonempty
  fac s j := by
    ext ⟨⟩
    refine constant_of_preserves_morphisms (α := s.pt)
      (fun (k : C) => s.ι.app k PUnit.unit) ?_ Classical.ofNonempty j
    intro X Y f
    exact ConcreteCategory.congr_hom (s.ι.naturality f).symm PUnit.unit
  uniq s m h := by
    ext ⟨⟩
    simp [← h Classical.ofNonempty]

Depends on / 依赖: Classical, Classical.ofNonempty, ofNonempty
-/
noncomputable def isColimitPUnitCocone [IsConnected C] : IsColimit (pUnitCocone.{w} C) where
  desc s := s.ι.app Classical.ofNonempty
  fac s j := by
    ext ⟨⟩
    refine constant_of_preserves_morphisms (α := s.pt)
      (fun (k : C) => s.ι.app k PUnit.unit) ?_ Classical.ofNonempty j
    intro X Y f
    exact ConcreteCategory.congr_hom (s.ι.naturality f).symm PUnit.unit
  uniq s m h := by
    ext ⟨⟩
    simp [← h Classical.ofNonempty]

/--
Instance `instHasColimitConstPUnitFunctor` / 实例 `instHasColimitConstPUnitFunctor`

English:
instance instHasColimitConstPUnitFunctor
  signature: [IsConnected C]
  body: ⟨_, isColimitPUnitCocone _⟩

中文:
实例 instHasColimitConstPUnitFunctor
  签名: [是连通 C]
  定义体: ⟨_, isColimitPUnitCocone _⟩

Depends on / 依赖: isColimitPUnitCocone
-/
instance instHasColimitConstPUnitFunctor [IsConnected C] : HasColimit (constPUnitFunctor.{w} C) :=
  ⟨_, isColimitPUnitCocone _⟩

/--
Instance `instSubsingletonColimitPUnit` / 实例 `instSubsingletonColimitPUnit`

English:
instance instSubsingletonColimitPUnit
  body: by
    obtain ⟨c, ⟨⟩, rfl⟩ := jointly_surjective' a
    obtain ⟨d, ⟨⟩, rfl⟩ := jointly_surjective' b
    apply constant_of_preserves_morphisms (colimit.ι (constPUnitFunctor C) · PUnit.unit)
    exact fun c d f => colimit_sound f rfl

中文:
实例 instSubsingletonColimitPUnit
  定义体: by
    obtain ⟨c, ⟨⟩, rfl⟩ := jointly_surjective' a
    obtain ⟨d, ⟨⟩, rfl⟩ := jointly_surjective' b
    apply constant_of_preserves_morphisms (colimit.ι (constPUnitFunctor C) · PUnit.unit)
    exact fun c d f => colimit_sound f rfl

Depends on / 依赖: PUnit.unit, colimit, colimit_sound, constPUnitFunctor, constant_of_preserves_morphisms, jointly_surjective
-/
instance instSubsingletonColimitPUnit
    [IsPreconnected C] [HasColimit (constPUnitFunctor.{w} C)] :
Subsingleton colimit (constPUnitFunctor.{w} C) where
  allEq a b := by
    obtain ⟨c, ⟨⟩, rfl⟩ := jointly_surjective' a
    obtain ⟨d, ⟨⟩, rfl⟩ := jointly_surjective' b
    apply constant_of_preserves_morphisms (colimit.ι (constPUnitFunctor C) · PUnit.unit)
    exact fun c d f => colimit_sound f rfl

/--
Definition of `colimitConstPUnitIsoPUnit` / `colimitConstPUnitIsoPUnit` 的定义

English:
definition colimitConstPUnitIsoPUnit
  signature: [IsConnected C]
  body: IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) (isColimitPUnitCocone.{w} C)

中文:
定义 colimitConstPUnitIsoPUnit
  签名: [是连通 C]
  定义体: IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) (isColimitPUnitCocone.{w} C)

Depends on / 依赖: Functor, Functor.additive_of_iso, IsColimit, IsColimit.coconePointUniqueUpToIso, Localization, Localization.functor_additive_iff, W.Q.commShiftIso, additive_of_iso, coconePointUniqueUpToIso, colimit, colimit.isColimit, commShiftIso, functor_additive_iff, isColimit, isColimitPUnitCocone
-/
noncomputable def colimitConstPUnitIsoPUnit [IsConnected C] :
    colimit (constPUnitFunctor.{w} C) ≅ PUnit.{w + 1} :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) (isColimitPUnitCocone.{w} C)

/--
theorem `zigzag_of_eqvGen_colimitTypeRel` / 定理 `zigzag_of_eqvGen_colimitTypeRel`

English:
theorem zigzag_of_eqvGen_colimitTypeRel
  statement: (F : C ⥤ Type w) (c d : Σ j, F.obj j)
  proof: by
  induction h with
| rel _ _ h => exact Zigzag.of_hom Exists.choose h
  | refl _ => exact Zigzag.refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

中文:
定理 zigzag_of_eqvGen_colimitTypeRel
  结论: (F : C ⥤ 类型 w) (c d : Σ j, F.obj j)
  证明: by
  induction h with
| rel _ _ h => exact Zigzag.of_hom Exists.choose h
  | refl _ => exact Zigzag.refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

Depends on / 依赖: Exists, Exists.choose, Zigzag, Zigzag.of_hom, Zigzag.refl, ih.symm, of_hom
-/
theorem zigzag_of_eqvGen_colimitTypeRel (F : C ⥤ Type w) (c d : Σ j, F.obj j)
    (h : Relation.EqvGen F.ColimitTypeRel c d) : Zigzag c.1 d.1 := by
  induction h with
| rel _ _ h => exact Zigzag.of_hom Exists.choose h
  | refl _ => exact Zigzag.refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/--
theorem `isConnected_iff_colimit_constPUnitFunctor_iso_pUnit` / 定理 `isConnected_iff_colimit_constPUnitFunctor_iso_pUnit`

English:
theorem isConnected_iff_colimit_constPUnitFunctor_iso_pUnit
  proof: by
  refine ⟨fun _ => ⟨colimitConstPUnitIsoPUnit.{w} C⟩, fun ⟨h⟩ => ?_⟩
have : Nonempty C := nonempty_of_nonempty_colimit Nonempty.map h.inv inferInstance
refine zigzag_isConnected fun c d => ?_
  refine zigzag_of_eqvGen_colimitTypeRel _ (constPUnitFunctor C) ⟨c, PUnit.unit⟩ ⟨d, PUnit.unit⟩ ?_
exact colimit_eq h.toEquiv.injective rfl

中文:
定理 isConnected_iff_colimit_constPUnitFunctor_iso_pUnit
  证明: by
  refine ⟨fun _ => ⟨colimitConstPUnitIsoPUnit.{w} C⟩, fun ⟨h⟩ => ?_⟩
have : Nonempty C := nonempty_of_nonempty_colimit Nonempty.map h.inv inferInstance
refine zigzag_isConnected fun c d => ?_
  refine zigzag_of_eqvGen_colimitTypeRel _ (constPUnitFunctor C) ⟨c, PUnit.unit⟩ ⟨d, PUnit.unit⟩ ?_
exact colimit_eq h.toEquiv.injective rfl

Depends on / 依赖: Nonempty, Nonempty.map, PUnit.unit, colimitConstPUnitIsoPUnit, colimit_eq, constPUnitFunctor, h.inv, h.toEquiv.injective, injective, nonempty_of_nonempty_colimit, toEquiv, zigzag_isConnected, zigzag_of_eqvGen_colimitTypeRel
-/
theorem isConnected_iff_colimit_constPUnitFunctor_iso_pUnit
    [HasColimit (constPUnitFunctor.{w} C)] :
    IsConnected C ↔ Nonempty (colimit (constPUnitFunctor.{w} C) ≅ PUnit) := by
  refine ⟨fun _ => ⟨colimitConstPUnitIsoPUnit.{w} C⟩, fun ⟨h⟩ => ?_⟩
have : Nonempty C := nonempty_of_nonempty_colimit Nonempty.map h.inv inferInstance
refine zigzag_isConnected fun c d => ?_
  refine zigzag_of_eqvGen_colimitTypeRel _ (constPUnitFunctor C) ⟨c, PUnit.unit⟩ ⟨d, PUnit.unit⟩ ?_
exact colimit_eq h.toEquiv.injective rfl

/--
theorem `isConnected_iff_isColimit_pUnitCocone` / 定理 `isConnected_iff_isColimit_pUnitCocone`

English:
theorem isConnected_iff_isColimit_pUnitCocone
  proof: by
  refine ⟨fun inst => ⟨isColimitPUnitCocone C⟩, fun ⟨h⟩ => ?_⟩
  let colimitCocone : ColimitCocone (constPUnitFunctor C) := ⟨pUnitCocone.{w} C, h⟩
  have : HasColimit (constPUnitFunctor.{w} C) := ⟨⟨colimitCocone⟩⟩
  simp only [isConnected_iff_colimit_constPUnitFunctor_iso_pUnit.{w} C]
  exact ⟨colimit.isoColimitCocone colimitCocone⟩

中文:
定理 isConnected_iff_isColimit_pUnitCocone
  证明: by
  refine ⟨fun inst => ⟨isColimitPUnitCocone C⟩, fun ⟨h⟩ => ?_⟩
  let colimitCocone : ColimitCocone (constPUnitFunctor C) := ⟨pUnitCocone.{w} C, h⟩
  have : HasColimit (constPUnitFunctor.{w} C) := ⟨⟨colimitCocone⟩⟩
  simp only [isConnected_iff_colimit_constPUnitFunctor_iso_pUnit.{w} C]
  exact ⟨colimit.isoColimitCocone colimitCocone⟩

Depends on / 依赖: ColimitCocone, Functor, Functor.additive_of_iso, HasColimit, Localization, Localization.functor_additive_iff, additive_of_iso, colimit, colimit.isoColimitCocone, colimitCocone, commShiftIso, constPUnitFunctor, functor_additive_iff, isColimitPUnitCocone, isConnected_iff_colimit_constPUnitFunctor_iso_pUnit, isoColimitCocone, pUnitCocone
-/
theorem isConnected_iff_isColimit_pUnitCocone :
    IsConnected C ↔ Nonempty (IsColimit (pUnitCocone.{w} C)) := by
  refine ⟨fun inst => ⟨isColimitPUnitCocone C⟩, fun ⟨h⟩ => ?_⟩
  let colimitCocone : ColimitCocone (constPUnitFunctor C) := ⟨pUnitCocone.{w} C, h⟩
  have : HasColimit (constPUnitFunctor.{w} C) := ⟨⟨colimitCocone⟩⟩
  simp only [isConnected_iff_colimit_constPUnitFunctor_iso_pUnit.{w} C]
  exact ⟨colimit.isoColimitCocone colimitCocone⟩

end Limits.Types

namespace Functor

open Limits.Types

universe v₂ u₂

variable {C : Type u} [Category.{v} C] {D : Type u₂} [Category.{v₂} D]

/--
theorem `isConnected_iff_of_final` / 定理 `isConnected_iff_of_final`

English:
theorem isConnected_iff_of_final
  given: (F : C ⥤ D) [F.Final]
  statement: IsConnected C ↔ IsConnected D
  proof: by
  rw [isConnected_iff_colimit_constPUnitFunctor_iso_pUnit.{max v u v₂ u₂} C]; rw [isConnected_iff_colimit_constPUnitFunctor_iso_pUnit.{max v u v₂ u₂} D]
exact Equiv.nonempty_congr Iso.isoCongrLeft
CategoryTheory.Functor.Final.colimitIso F constPUnitFunctor.{max u v u₂ v₂} D

中文:
定理 isConnected_iff_of_final
  条件: (F : C ⥤ D) [F.终]
  结论: 是连通 C ↔ 是连通 D
  证明: by
  rw [isConnected_iff_colimit_constPUnitFunctor_iso_pUnit.{max v u v₂ u₂} C]; rw [isConnected_iff_colimit_constPUnitFunctor_iso_pUnit.{max v u v₂ u₂} D]
exact Equiv.nonempty_congr Iso.isoCongrLeft
CategoryTheory.Functor.Final.colimitIso F constPUnitFunctor.{max u v u₂ v₂} D

Depends on / 依赖: CategoryTheory, CategoryTheory.Functor.Final.colimitIso, Equiv.nonempty_congr, Functor, Iso.isoCongrLeft, colimitIso, constPUnitFunctor, isConnected_iff_colimit_constPUnitFunctor_iso_pUnit, isoCongrLeft, nonempty_congr
-/
theorem isConnected_iff_of_final (F : C ⥤ D) [F.Final] : IsConnected C ↔ IsConnected D := by
  rw [isConnected_iff_colimit_constPUnitFunctor_iso_pUnit.{max v u v₂ u₂} C]; rw [isConnected_iff_colimit_constPUnitFunctor_iso_pUnit.{max v u v₂ u₂} D]
exact Equiv.nonempty_congr Iso.isoCongrLeft
CategoryTheory.Functor.Final.colimitIso F constPUnitFunctor.{max u v u₂ v₂} D

/--
theorem `isConnected_iff_of_initial` / 定理 `isConnected_iff_of_initial`

English:
theorem isConnected_iff_of_initial
  given: (F : C ⥤ D) [F.Initial]
  statement: IsConnected C ↔ IsConnected D
  proof: by
  rw [← isConnected_op_iff_isConnected C]; rw [← isConnected_op_iff_isConnected D]
  exact isConnected_iff_of_final F.op

中文:
定理 isConnected_iff_of_initial
  条件: (F : C ⥤ D) [F.初始]
  结论: 是连通 C ↔ 是连通 D
  证明: by
  rw [← isConnected_op_iff_isConnected C]; rw [← isConnected_op_iff_isConnected D]
  exact isConnected_iff_of_final F.op

Depends on / 依赖: F.op, isConnected_iff_of_final, isConnected_op_iff_isConnected
-/
theorem isConnected_iff_of_initial (F : C ⥤ D) [F.Initial] : IsConnected C ↔ IsConnected D := by
  rw [← isConnected_op_iff_isConnected C]; rw [← isConnected_op_iff_isConnected D]
  exact isConnected_iff_of_final F.op

end Functor

section

variable (C : Type*) [Category* C]

/--
lemma `isConnected_of_isInitial` / 引理 `isConnected_of_isInitial`

English:
lemma isConnected_of_isInitial
  given: {x : C} (h : Limits.IsInitial x)
  statement: IsConnected C
  proof: by
  let : Nonempty C := ⟨x⟩
  apply isConnected_of_zigzag
  intro j₁ j₂
  use [x, j₂]
  simp only [List.isChain_cons_cons, List.isChain_singleton, and_true, ne_eq,
    reduceCtorEq, not_false_eq_true, List.getLast_cons, List.cons_ne_self, List.getLast_singleton]
exact ⟨Zag.symm Zag.of_hom h.to _, Zag.of_hom h.to _⟩

中文:
引理 isConnected_of_isInitial
  条件: {x : C} (h : Limits.IsInitial x)
  结论: 是连通 C
  证明: by
  let : Nonempty C := ⟨x⟩
  apply isConnected_of_zigzag
  intro j₁ j₂
  use [x, j₂]
  simp only [List.isChain_cons_cons, List.isChain_singleton, and_true, ne_eq,
    reduceCtorEq, not_false_eq_true, List.getLast_cons, List.cons_ne_self, List.getLast_singleton]
exact ⟨Zag.symm Zag.of_hom h.to _, Zag.of_hom h.to _⟩

Depends on / 依赖: List.cons_ne_self, List.getLast_cons, List.getLast_singleton, List.isChain_cons_cons, List.isChain_singleton, Nonempty, Zag.of_hom, Zag.symm, and_true, cons_ne_self, getLast_cons, getLast_singleton, h.to, isChain_cons_cons, isChain_singleton, isConnected_of_zigzag, ne_eq, not_false_eq_true, of_hom, reduceCtorEq
-/
lemma isConnected_of_isInitial {x : C} (h : Limits.IsInitial x) : IsConnected C := by
  let : Nonempty C := ⟨x⟩
  apply isConnected_of_zigzag
  intro j₁ j₂
  use [x, j₂]
  simp only [List.isChain_cons_cons, List.isChain_singleton, and_true, ne_eq,
    reduceCtorEq, not_false_eq_true, List.getLast_cons, List.cons_ne_self, List.getLast_singleton]
exact ⟨Zag.symm Zag.of_hom h.to _, Zag.of_hom h.to _⟩

/--
lemma `isConnected_of_isTerminal` / 引理 `isConnected_of_isTerminal`

English:
lemma isConnected_of_isTerminal
  given: {x : C} (h : Limits.IsTerminal x)
  statement: IsConnected C
  proof: by
  let : Nonempty C := ⟨x⟩
  apply isConnected_of_zigzag
  intro j₁ j₂
  use [x, j₂]
  simp only [List.isChain_cons_cons, List.isChain_singleton, and_true, ne_eq,
    reduceCtorEq, not_false_eq_true, List.getLast_cons, List.cons_ne_self, List.getLast_singleton]
exact ⟨Zag.of_hom h.from _, Zag.symm Zag.of_hom h.from _⟩

中文:
引理 isConnected_of_isTerminal
  条件: {x : C} (h : Limits.是终止 x)
  结论: 是连通 C
  证明: by
  let : Nonempty C := ⟨x⟩
  apply isConnected_of_zigzag
  intro j₁ j₂
  use [x, j₂]
  simp only [List.isChain_cons_cons, List.isChain_singleton, and_true, ne_eq,
    reduceCtorEq, not_false_eq_true, List.getLast_cons, List.cons_ne_self, List.getLast_singleton]
exact ⟨Zag.of_hom h.from _, Zag.symm Zag.of_hom h.from _⟩

Depends on / 依赖: List.cons_ne_self, List.getLast_cons, List.getLast_singleton, List.isChain_cons_cons, List.isChain_singleton, Nonempty, Zag.of_hom, Zag.symm, and_true, cons_ne_self, getLast_cons, getLast_singleton, h.from, isChain_cons_cons, isChain_singleton, isConnected_of_zigzag, ne_eq, not_false_eq_true, of_hom, reduceCtorEq
-/
lemma isConnected_of_isTerminal {x : C} (h : Limits.IsTerminal x) : IsConnected C := by
  let : Nonempty C := ⟨x⟩
  apply isConnected_of_zigzag
  intro j₁ j₂
  use [x, j₂]
  simp only [List.isChain_cons_cons, List.isChain_singleton, and_true, ne_eq,
    reduceCtorEq, not_false_eq_true, List.getLast_cons, List.cons_ne_self, List.getLast_singleton]
exact ⟨Zag.of_hom h.from _, Zag.symm Zag.of_hom h.from _⟩

-- note : it seems making the following two as instances breaks things, so these are lemmas.
/--
lemma `isConnected_of_hasInitial` / 引理 `isConnected_of_hasInitial`

English:
lemma isConnected_of_hasInitial
  given: [Limits.HasInitial C]
  statement: IsConnected C
  proof: isConnected_of_isInitial C Limits.initialIsInitial

中文:
引理 isConnected_of_hasInitial
  条件: [Limits.HasInitial C]
  结论: 是连通 C
  证明: isConnected_of_isInitial C Limits.initialIsInitial

Depends on / 依赖: Limits, Limits.initialIsInitial, initialIsInitial, isConnected_of_isInitial
-/
lemma isConnected_of_hasInitial [Limits.HasInitial C] : IsConnected C :=
  isConnected_of_isInitial C Limits.initialIsInitial

/--
lemma `isConnected_of_hasTerminal` / 引理 `isConnected_of_hasTerminal`

English:
lemma isConnected_of_hasTerminal
  given: [Limits.HasTerminal C]
  statement: IsConnected C
  proof: isConnected_of_isTerminal C Limits.terminalIsTerminal

中文:
引理 isConnected_of_hasTerminal
  条件: [Limits.有终止 C]
  结论: 是连通 C
  证明: isConnected_of_isTerminal C Limits.terminalIsTerminal

Depends on / 依赖: Limits, Limits.terminalIsTerminal, isConnected_of_isTerminal, terminalIsTerminal
-/
lemma isConnected_of_hasTerminal [Limits.HasTerminal C] : IsConnected C :=
  isConnected_of_isTerminal C Limits.terminalIsTerminal

end

end CategoryTheory
