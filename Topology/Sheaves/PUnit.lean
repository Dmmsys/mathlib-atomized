/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
module

public import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# Presheaves on `PUnit`

Presheaves on `PUnit` satisfy sheaf condition iff its value at empty set is a terminal object.
-/

public section


namespace TopCat.Presheaf

universe u v w

open CategoryTheory CategoryTheory.Limits TopCat Opposite

variable {C : Type u} [Category.{v} C]

/--
theorem `isSheaf_of_isTerminal_of_indiscrete` / 定理 `isSheaf_of_isTerminal_of_indiscrete`

English:
theorem isSheaf_of_isTerminal_of_indiscrete
  statement: {X : TopCat.{w}} (hind : X.str = ⊤) (F : Presheaf C X)
  proof: fun c U s hs => by
  have : IndiscreteTopology X := ⟨hind⟩
  obtain rfl | hne := eq_or_ne U ⊥
  · intro _ _
    rw [@existsUnique_iff_exists _ ⟨fun _ _ => _⟩]
    · refine ⟨it.from _, fun U hU hs => IsTerminal.hom_ext ?_ _ _⟩
      rwa [le_bot_iff.1 hU.le]
    · apply it.hom_ext
  · convert! Presieve.isSheafFor_top (F ⋙ coyoneda.obj (@op C c))
    rw [Sieve.arrows_eq_top_iff]; rw [← Sieve.id_mem_iff_eq_top]
    have := U.eq_bot_or_top.resolve_left hne
    subst this
    obtain he | ⟨⟨x⟩⟩ := isEmpty_or_nonempty X
    · exact (hne <| SetLike.ext'_iff.2 <| Set.univ_eq_empty_iff.2 he).elim
    obtain ⟨U, f, hf, hm⟩ := hs x _root_.trivial
    obtain rfl | rfl := U.eq_bot_or_top
    · cases hm
    · convert! hf

中文:
定理 isSheaf_of_isTerminal_of_indiscrete
  结论: {X : 顶元素范畴.{w}} (hind : X.str = ⊤) (F : 预层 C X)
  证明: fun c U s hs => by
  have : IndiscreteTopology X := ⟨hind⟩
  obtain rfl | hne := eq_or_ne U ⊥
  · intro _ _
    rw [@existsUnique_iff_exists _ ⟨fun _ _ => _⟩]
    · refine ⟨it.from _, fun U hU hs => IsTerminal.hom_ext ?_ _ _⟩
      rwa [le_bot_iff.1 hU.le]
    · apply it.hom_ext
  · convert! Presieve.isSheafFor_top (F ⋙ coyoneda.obj (@op C c))
    rw [Sieve.arrows_eq_top_iff]; rw [← Sieve.id_mem_iff_eq_top]
    have := U.eq_bot_or_top.resolve_left hne
    subst this
    obtain he | ⟨⟨x⟩⟩ := isEmpty_or_nonempty X
    · exact (hne <| SetLike.ext'_iff.2 <| Set.univ_eq_empty_iff.2 he).elim
    obtain ⟨U, f, hf, hm⟩ := hs x _root_.trivial
    obtain rfl | rfl := U.eq_bot_or_top
    · cases hm
    · convert! hf

Depends on / 依赖: IndiscreteTopology, IsTerminal, IsTerminal.hom_ext, Presieve, Presieve.isSheafFor_top, SetLike, Sieve.arrows_eq_top_iff, Sieve.id_mem_iff_eq_top, U.eq_bot_or_top.resolve_left, arrows_eq_top_iff, convert, coyoneda, coyoneda.obj, eq_bot_or_top, eq_or_ne, existsUnique_iff_exists, hU.le, hom_ext, id_mem_iff_eq_top, isEmpty_or_nonempty
-/
theorem isSheaf_of_isTerminal_of_indiscrete {X : TopCat.{w}} (hind : X.str = ⊤) (F : Presheaf C X)
    (it : IsTerminal <| F.obj <| op ⊥) : F.IsSheaf := fun c U s hs => by
  have : IndiscreteTopology X := ⟨hind⟩
  obtain rfl | hne := eq_or_ne U ⊥
  · intro _ _
    rw [@existsUnique_iff_exists _ ⟨fun _ _ => _⟩]
    · refine ⟨it.from _, fun U hU hs => IsTerminal.hom_ext ?_ _ _⟩
      rwa [le_bot_iff.1 hU.le]
    · apply it.hom_ext
  · convert! Presieve.isSheafFor_top (F ⋙ coyoneda.obj (@op C c))
    rw [Sieve.arrows_eq_top_iff]; rw [← Sieve.id_mem_iff_eq_top]
    have := U.eq_bot_or_top.resolve_left hne
    subst this
    obtain he | ⟨⟨x⟩⟩ := isEmpty_or_nonempty X
    · exact (hne <| SetLike.ext'_iff.2 <| Set.univ_eq_empty_iff.2 he).elim
    obtain ⟨U, f, hf, hm⟩ := hs x _root_.trivial
    obtain rfl | rfl := U.eq_bot_or_top
    · cases hm
    · convert! hf

/--
theorem `isSheaf_iff_isTerminal_of_indiscrete` / 定理 `isSheaf_iff_isTerminal_of_indiscrete`

English:
theorem isSheaf_iff_isTerminal_of_indiscrete
  statement: {X : TopCat.{w}} (hind : X.str = ⊤)
  proof: ⟨fun h => ⟨Sheaf.isTerminalOfEmpty ⟨F, h⟩⟩, fun ⟨it⟩ =>
    isSheaf_of_isTerminal_of_indiscrete hind F it⟩

中文:
定理 isSheaf_iff_isTerminal_of_indiscrete
  结论: {X : 顶元素范畴.{w}} (hind : X.str = ⊤)
  证明: ⟨fun h => ⟨Sheaf.isTerminalOfEmpty ⟨F, h⟩⟩, fun ⟨it⟩ =>
    isSheaf_of_isTerminal_of_indiscrete hind F it⟩

Depends on / 依赖: Sheaf.isTerminalOfEmpty, isSheaf_of_isTerminal_of_indiscrete, isTerminalOfEmpty
-/
theorem isSheaf_iff_isTerminal_of_indiscrete {X : TopCat.{w}} (hind : X.str = ⊤)
    (F : Presheaf C X) : F.IsSheaf ↔ Nonempty (IsTerminal <| F.obj <| op ⊥) :=
  ⟨fun h => ⟨Sheaf.isTerminalOfEmpty ⟨F, h⟩⟩, fun ⟨it⟩ =>
    isSheaf_of_isTerminal_of_indiscrete hind F it⟩

/--
theorem `isSheaf_on_punit_of_isTerminal` / 定理 `isSheaf_on_punit_of_isTerminal`

English:
theorem isSheaf_on_punit_of_isTerminal
  statement: (F : Presheaf C (TopCat.of PUnit))
  proof: isSheaf_of_isTerminal_of_indiscrete (@Subsingleton.elim (TopologicalSpace PUnit) _ _ _) F it

中文:
定理 isSheaf_on_punit_of_isTerminal
  结论: (F : 预层 C (顶元素范畴.of 命题单元))
  证明: isSheaf_of_isTerminal_of_indiscrete (@Subsingleton.elim (TopologicalSpace PUnit) _ _ _) F it

Depends on / 依赖: Subsingleton, Subsingleton.elim, TopologicalSpace, isSheaf_of_isTerminal_of_indiscrete
-/
theorem isSheaf_on_punit_of_isTerminal (F : Presheaf C (TopCat.of PUnit))
    (it : IsTerminal <| F.obj <| op ⊥) : F.IsSheaf :=
  isSheaf_of_isTerminal_of_indiscrete (@Subsingleton.elim (TopologicalSpace PUnit) _ _ _) F it

/--
theorem `isSheaf_on_punit_iff_isTerminal` / 定理 `isSheaf_on_punit_iff_isTerminal`

English:
theorem isSheaf_on_punit_iff_isTerminal
  given: (F : Presheaf C (TopCat.of PUnit))
  proof: ⟨fun h => ⟨Sheaf.isTerminalOfEmpty ⟨F, h⟩⟩, fun ⟨it⟩ => isSheaf_on_punit_of_isTerminal F it⟩

中文:
定理 isSheaf_on_punit_iff_isTerminal
  条件: (F : 预层 C (顶元素范畴.of 命题单元))
  证明: ⟨fun h => ⟨Sheaf.isTerminalOfEmpty ⟨F, h⟩⟩, fun ⟨it⟩ => isSheaf_on_punit_of_isTerminal F it⟩

Depends on / 依赖: Sheaf.isTerminalOfEmpty, isSheaf_on_punit_of_isTerminal, isTerminalOfEmpty
-/
theorem isSheaf_on_punit_iff_isTerminal (F : Presheaf C (TopCat.of PUnit)) :
    F.IsSheaf ↔ Nonempty (IsTerminal <| F.obj <| op ⊥) :=
  ⟨fun h => ⟨Sheaf.isTerminalOfEmpty ⟨F, h⟩⟩, fun ⟨it⟩ => isSheaf_on_punit_of_isTerminal F it⟩

end TopCat.Presheaf
