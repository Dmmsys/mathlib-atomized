/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Discrete.StructuredArrow

/-!
# Characterization of connected categories using initial/final functors

A category `C` is connected iff the constant functor `C ⥤ Discrete PUnit`
is final (or initial).

We deduce that the projection `C × D ⥤ C` is final (or initial) if `D` is connected.

-/

public section

universe w v v' u u'

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {T : Type w} [Unique T]

/--
lemma `isConnected_iff_final_of_unique` / 引理 `isConnected_iff_final_of_unique`

English:
lemma isConnected_iff_final_of_unique
  given: (F : C ⥤ Discrete T)
  proof: by
  rw [← isConnected_iff_of_equivalence
    (Discrete.structuredArrowEquivalenceOfUnique F default)]
  refine ⟨fun _ => ⟨?_⟩, fun _ => inferInstance⟩
  rintro ⟨d⟩
  obtain rfl := Subsingleton.elim d default
  infer_instance

中文:
引理 isConnected_iff_final_of_unique
  条件: (F : C ⥤ 离散 T)
  证明: by
  rw [← isConnected_iff_of_equivalence
    (Discrete.structuredArrowEquivalenceOfUnique F default)]
  refine ⟨fun _ => ⟨?_⟩, fun _ => inferInstance⟩
  rintro ⟨d⟩
  obtain rfl := Subsingleton.elim d default
  infer_instance

Depends on / 依赖: Discrete, Discrete.structuredArrowEquivalenceOfUnique, Subsingleton, Subsingleton.elim, infer_instance, isConnected_iff_of_equivalence, structuredArrowEquivalenceOfUnique
-/
lemma isConnected_iff_final_of_unique (F : C ⥤ Discrete T) :
    IsConnected C ↔ F.Final := by
  rw [← isConnected_iff_of_equivalence
    (Discrete.structuredArrowEquivalenceOfUnique F default)]
  refine ⟨fun _ => ⟨?_⟩, fun _ => inferInstance⟩
  rintro ⟨d⟩
  obtain rfl := Subsingleton.elim d default
  infer_instance

/--
lemma `isConnected_iff_initial_of_unique` / 引理 `isConnected_iff_initial_of_unique`

English:
lemma isConnected_iff_initial_of_unique
  given: (F : C ⥤ Discrete T)
  proof: by
  rw [← isConnected_iff_of_equivalence
    (Discrete.costructuredArrowEquivalenceOfUnique F default)]
  refine ⟨fun _ => ⟨?_⟩, fun _ => inferInstance⟩
  rintro ⟨d⟩
  obtain rfl := Subsingleton.elim d default
  infer_instance

中文:
引理 isConnected_iff_initial_of_unique
  条件: (F : C ⥤ 离散 T)
  证明: by
  rw [← isConnected_iff_of_equivalence
    (Discrete.costructuredArrowEquivalenceOfUnique F default)]
  refine ⟨fun _ => ⟨?_⟩, fun _ => inferInstance⟩
  rintro ⟨d⟩
  obtain rfl := Subsingleton.elim d default
  infer_instance

Depends on / 依赖: Discrete, Discrete.costructuredArrowEquivalenceOfUnique, Subsingleton, Subsingleton.elim, costructuredArrowEquivalenceOfUnique, infer_instance, isConnected_iff_of_equivalence
-/
lemma isConnected_iff_initial_of_unique (F : C ⥤ Discrete T) :
    IsConnected C ↔ F.Initial := by
  rw [← isConnected_iff_of_equivalence
    (Discrete.costructuredArrowEquivalenceOfUnique F default)]
  refine ⟨fun _ => ⟨?_⟩, fun _ => inferInstance⟩
  rintro ⟨d⟩
  obtain rfl := Subsingleton.elim d default
  infer_instance

instance (F : C ⥤ Discrete T) [IsConnected C] : F.Final := by
  rwa [← isConnected_iff_final_of_unique F]

instance (F : C ⥤ Discrete T) [IsConnected C] : F.Initial := by
  rwa [← isConnected_iff_initial_of_unique F]

/--
Instance `final_fst` / 实例 `final_fst`

English:
instance final_fst
  signature: [IsConnected D]
  body: inferInstanceAs (Functor.prod (𝟭 C) ((Functor.const _).obj (Discrete.mk .unit)) ⋙
    (prod.rightUnitorEquivalence.{0} C).functor).Final

中文:
实例 final_fst
  签名: [是连通 D]
  定义体: inferInstanceAs (Functor.prod (𝟭 C) ((Functor.const _).obj (Discrete.mk .unit)) ⋙
    (prod.rightUnitorEquivalence.{0} C).functor).Final

Depends on / 依赖: Discrete, Discrete.mk, Functor, Functor.const, Functor.prod, functor, prod.rightUnitorEquivalence, rightUnitorEquivalence
-/
instance final_fst [IsConnected D] : (Prod.fst C D).Final :=
  inferInstanceAs (Functor.prod (𝟭 C) ((Functor.const _).obj (Discrete.mk .unit)) ⋙
    (prod.rightUnitorEquivalence.{0} C).functor).Final

/--
Instance `final_snd` / 实例 `final_snd`

English:
instance final_snd
  signature: [IsConnected C]
  body: inferInstanceAs ((Prod.braiding C D).functor ⋙ Prod.fst D C).Final

中文:
实例 final_snd
  签名: [是连通 C]
  定义体: inferInstanceAs ((Prod.braiding C D).functor ⋙ Prod.fst D C).Final

Depends on / 依赖: Prod.braiding, Prod.fst, braiding, functor
-/
instance final_snd [IsConnected C] : (Prod.snd C D).Final :=
  inferInstanceAs ((Prod.braiding C D).functor ⋙ Prod.fst D C).Final

/--
Instance `initial_fst` / 实例 `initial_fst`

English:
instance initial_fst
  signature: [IsConnected D]
  body: inferInstanceAs (Functor.prod (𝟭 C) ((Functor.const _).obj (Discrete.mk .unit)) ⋙
    (prod.rightUnitorEquivalence.{0} C).functor).Initial

中文:
实例 initial_fst
  签名: [是连通 D]
  定义体: inferInstanceAs (Functor.prod (𝟭 C) ((Functor.const _).obj (Discrete.mk .unit)) ⋙
    (prod.rightUnitorEquivalence.{0} C).functor).Initial

Depends on / 依赖: Discrete, Discrete.mk, Functor, Functor.const, Functor.prod, Initial, functor, prod.rightUnitorEquivalence, rightUnitorEquivalence
-/
instance initial_fst [IsConnected D] : (Prod.fst C D).Initial :=
  inferInstanceAs (Functor.prod (𝟭 C) ((Functor.const _).obj (Discrete.mk .unit)) ⋙
    (prod.rightUnitorEquivalence.{0} C).functor).Initial

/--
Instance `initial_snd` / 实例 `initial_snd`

English:
instance initial_snd
  signature: [IsConnected C]
  body: inferInstanceAs ((Prod.braiding C D).functor ⋙ Prod.fst D C).Initial

中文:
实例 initial_snd
  签名: [是连通 C]
  定义体: inferInstanceAs ((Prod.braiding C D).functor ⋙ Prod.fst D C).Initial

Depends on / 依赖: Initial, Prod.braiding, Prod.fst, braiding, functor
-/
instance initial_snd [IsConnected C] : (Prod.snd C D).Initial :=
  inferInstanceAs ((Prod.braiding C D).functor ⋙ Prod.fst D C).Initial

end CategoryTheory
