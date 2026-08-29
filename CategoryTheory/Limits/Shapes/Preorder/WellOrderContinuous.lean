/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.IsLimit
public import Mathlib.CategoryTheory.Limits.Shapes.Preorder.PrincipalSeg
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.Data.Nat.SuccPred
public import Mathlib.Data.Fin.SuccPredOrder
public import Mathlib.Order.Interval.Set.InitialSeg
public import Mathlib.Order.Interval.Set.Limit
public import Mathlib.Order.SuccPred.InitialSeg
public import Mathlib.Order.SuccPred.Limit
public import Mathlib.Order.SuccPred.LinearLocallyFinite

/-!
# Continuity of functors from well-ordered types

Let `F : J ⥤ C` be a functor from a well-ordered type `J`.
We introduce the typeclass `F.IsWellOrderContinuous`
to say that if `m` is a limit element, then `F.obj m`
is the colimit of the `F.obj j` for `j < m`.

-/

@[expose] public section

universe w w' v u

namespace CategoryTheory.Functor

open Category Limits

variable {C : Type u} [Category.{v} C] {J : Type w} [PartialOrder J]

/--
Definition of `IsWellOrderContinuous` / `IsWellOrderContinuous` 的定义

English:
class IsWellOrderContinuous
  parameters: (F : J ⥤ C)
  axioms and operations (1):
    - nonempty_isColimit((m : J) (hm : Order.IsSuccLimit m)) : Nonempty (IsColimit ((Set.principalSegIio m).cocone F))

中文:
类 是WellOrderContinuous
  参数: (F : J ⥤ C)
  公理与运算 (1 个):
    - nonempty_isColimit((m : J) (hm : Order.是SuccLimit m)) : 非空 (是余极限 ((集合.principalSegIio m).cocone F))
-/
class IsWellOrderContinuous (F : J ⥤ C) : Prop where
  nonempty_isColimit (m : J) (hm : Order.IsSuccLimit m) :
    Nonempty (IsColimit ((Set.principalSegIio m).cocone F))

/--
Definition of `isColimitOfIsWellOrderContinuous` / `isColimitOfIsWellOrderContinuous` 的定义

English:
definition isColimitOfIsWellOrderContinuous
  signature: (F : J ⥤ C) [F.IsWellOrderContinuous]
  body: (IsWellOrderContinuous.nonempty_isColimit m hm).some

中文:
定义 isColimitOfIsWellOrderContinuous
  签名: (F : J ⥤ C) [F.是WellOrderContinuous]
  定义体: (IsWellOrderContinuous.nonempty_isColimit m hm).some

Depends on / 依赖: IsWellOrderContinuous, IsWellOrderContinuous.nonempty_isColimit, nonempty_isColimit
-/
noncomputable def isColimitOfIsWellOrderContinuous (F : J ⥤ C) [F.IsWellOrderContinuous]
    (m : J) (hm : Order.IsSuccLimit m) :
    IsColimit ((Set.principalSegIio m).cocone F) :=
      (IsWellOrderContinuous.nonempty_isColimit m hm).some

/--
Definition of `isColimitOfIsWellOrderContinuous'` / `isColimitOfIsWellOrderContinuous'` 的定义

English:
definition isColimitOfIsWellOrderContinuous'
  signature: (F : J ⥤ C) [F.IsWellOrderContinuous]
  body: (F.isColimitOfIsWellOrderContinuous f.top hα).whiskerEquivalence
    f.orderIsoIio.equivalence

中文:
定义 isColimitOfIsWellOrderContinuous'
  签名: (F : J ⥤ C) [F.是WellOrderContinuous]
  定义体: (F.isColimitOfIsWellOrderContinuous f.top hα).whiskerEquivalence
    f.orderIsoIio.equivalence

Depends on / 依赖: F.isColimitOfIsWellOrderContinuous, equivalence, f.orderIsoIio.equivalence, f.top, isColimitOfIsWellOrderContinuous, orderIsoIio, whiskerEquivalence
-/
noncomputable def isColimitOfIsWellOrderContinuous' (F : J ⥤ C) [F.IsWellOrderContinuous]
    {α : Type*} [PartialOrder α] (f : α <i J) (hα : Order.IsSuccLimit f.top) :
    IsColimit (f.cocone F) :=
  (F.isColimitOfIsWellOrderContinuous f.top hα).whiskerEquivalence
    f.orderIsoIio.equivalence

instance (F : Nat ⥤ C) : F.IsWellOrderContinuous where
  nonempty_isColimit m hm := by simp at hm

instance {n : Nat} (F : Fin n ⥤ C) : F.IsWellOrderContinuous where
  nonempty_isColimit _ hj := (Order.not_isSuccLimit_of_isSuccArchimedean hj).elim

set_option backward.defeqAttrib.useBackward true in
/--
lemma `isWellOrderContinuous_of_iso` / 引理 `isWellOrderContinuous_of_iso`

English:
lemma isWellOrderContinuous_of_iso
  given: {F G : J ⥤ C} (e : F ≅ G) [F.IsWellOrderContinuous]
  proof: ⟨(IsColimit.precomposeHomEquiv (isoWhiskerLeft _ e) _).1
      (IsColimit.ofIsoColimit (F.isColimitOfIsWellOrderContinuous m hm)
        (Cocone.ext (e.app _)))⟩

中文:
引理 isWellOrderContinuous_of_iso
  条件: {F G : J ⥤ C} (e : F ≅ G) [F.是WellOrderContinuous]
  证明: ⟨(IsColimit.precomposeHomEquiv (isoWhiskerLeft _ e) _).1
      (IsColimit.ofIsoColimit (F.isColimitOfIsWellOrderContinuous m hm)
        (Cocone.ext (e.app _)))⟩

Depends on / 依赖: Cocone, Cocone.ext, F.isColimitOfIsWellOrderContinuous, IsColimit, IsColimit.ofIsoColimit, IsColimit.precomposeHomEquiv, e.app, isColimitOfIsWellOrderContinuous, isoWhiskerLeft, ofIsoColimit, precomposeHomEquiv
-/
lemma isWellOrderContinuous_of_iso {F G : J ⥤ C} (e : F ≅ G) [F.IsWellOrderContinuous] :
    G.IsWellOrderContinuous where
  nonempty_isColimit (m : J) (hm : Order.IsSuccLimit m) :=
    ⟨(IsColimit.precomposeHomEquiv (isoWhiskerLeft _ e) _).1
      (IsColimit.ofIsoColimit (F.isColimitOfIsWellOrderContinuous m hm)
        (Cocone.ext (e.app _)))⟩

instance (F : J ⥤ C) {J' : Type w'} [PartialOrder J'] (f : J' <=i J)
    [F.IsWellOrderContinuous] :
    (f.monotone.functor ⋙ F).IsWellOrderContinuous where
  nonempty_isColimit m' hm' := ⟨F.isColimitOfIsWellOrderContinuous'
    ((Set.principalSegIio m').transInitial f) (by simpa)⟩

instance (F : J ⥤ C) {J' : Type w'} [PartialOrder J'] (e : J' ≃o J)
    [F.IsWellOrderContinuous] :
    (e.equivalence.functor ⋙ F).IsWellOrderContinuous :=
  inferInstanceAs (e.toInitialSeg.monotone.functor ⋙ F).IsWellOrderContinuous

/--
Instance `IsWellOrderContinuous.restriction_setIci` / 实例 `IsWellOrderContinuous.restriction_setIci`

English:
instance IsWellOrderContinuous.restriction_setIci
  body: ⟨by
    let f : Set.Iio m -> Set.Iio m.1 := fun ⟨⟨a, ha⟩, ha'⟩ => ⟨a, ha'⟩
    have hf : Monotone f := fun _ _ h => h
    have : hf.functor.Final := by
      rw [Monotone.final_functor_iff]
      rintro ⟨j', hj'⟩
      push _ in _ at hj'
      dsimp only [f]
      by_cases! h : j' <= j
      · refine ⟨⟨⟨j, le_refl j⟩, ?_⟩, h⟩
        by_contra h'
        simp only [Set.mem_Iio, not_lt] at h'
        apply hm.1
        rintro ⟨k, hk⟩ hkm
        exact h'.trans hk
      · exact ⟨⟨⟨j', h.le⟩, hj'⟩, by rfl⟩
    exact (Functor.Final.isColimitWhiskerEquiv (F := hf.functor) _).2
      (F.isColimitOfIsWellOrderContinuous m.1 (Set.Ici.isSuccLimit_coe m hm))⟩

中文:
实例 是WellOrderContinuous.restriction_setIci
  定义体: ⟨by
    let f : Set.Iio m -> Set.Iio m.1 := fun ⟨⟨a, ha⟩, ha'⟩ => ⟨a, ha'⟩
    have hf : Monotone f := fun _ _ h => h
    have : hf.functor.Final := by
      rw [Monotone.final_functor_iff]
      rintro ⟨j', hj'⟩
      push _ in _ at hj'
      dsimp only [f]
      by_cases! h : j' <= j
      · refine ⟨⟨⟨j, le_refl j⟩, ?_⟩, h⟩
        by_contra h'
        simp only [Set.mem_Iio, not_lt] at h'
        apply hm.1
        rintro ⟨k, hk⟩ hkm
        exact h'.trans hk
      · exact ⟨⟨⟨j', h.le⟩, hj'⟩, by rfl⟩
    exact (Functor.Final.isColimitWhiskerEquiv (F := hf.functor) _).2
      (F.isColimitOfIsWellOrderContinuous m.1 (Set.Ici.isSuccLimit_coe m hm))⟩

Depends on / 依赖: F.isColimitOfIsWel, Functor, Functor.Final.isColimitWhiskerEquiv, Monotone, Monotone.final_functor_iff, Set.Iio, Set.mem_Iio, final_functor_iff, functor, h.le, hf.functor, hf.functor.Final, isColimitOfIsWel, isColimitWhiskerEquiv, le_refl, mem_Iio, not_lt
-/
instance IsWellOrderContinuous.restriction_setIci
    {J : Type w} [LinearOrder J]
    {F : J ⥤ C} [F.IsWellOrderContinuous] (j : J) :
    ((Subtype.mono_coe (· in Set.Ici j)).functor ⋙ F).IsWellOrderContinuous where
  nonempty_isColimit m hm := ⟨by
    let f : Set.Iio m -> Set.Iio m.1 := fun ⟨⟨a, ha⟩, ha'⟩ => ⟨a, ha'⟩
    have hf : Monotone f := fun _ _ h => h
    have : hf.functor.Final := by
      rw [Monotone.final_functor_iff]
      rintro ⟨j', hj'⟩
      push _ in _ at hj'
      dsimp only [f]
      by_cases! h : j' <= j
      · refine ⟨⟨⟨j, le_refl j⟩, ?_⟩, h⟩
        by_contra h'
        simp only [Set.mem_Iio, not_lt] at h'
        apply hm.1
        rintro ⟨k, hk⟩ hkm
        exact h'.trans hk
      · exact ⟨⟨⟨j', h.le⟩, hj'⟩, by rfl⟩
    exact (Functor.Final.isColimitWhiskerEquiv (F := hf.functor) _).2
      (F.isColimitOfIsWellOrderContinuous m.1 (Set.Ici.isSuccLimit_coe m hm))⟩

end CategoryTheory.Functor
