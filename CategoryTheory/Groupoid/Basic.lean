/-
Copyright (c) 2022 Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémi Bottinelli
-/
module

public import Mathlib.CategoryTheory.Groupoid
public import Mathlib.Combinatorics.Quiver.Basic

/-!
This file defines a few basic properties of groupoids.
-/

@[expose] public section

namespace CategoryTheory

namespace Groupoid

variable (C : Type*) [Groupoid C]

section Thin

/--
theorem `isThin_iff` / 定理 `isThin_iff`

English:
theorem isThin_iff
  statement: Quiver.IsThin C ↔ forall c : C, Subsingleton (c ⟶ c)
  proof: by
  refine ⟨fun h c => h c c, fun h c d => Subsingleton.intro fun f g => ?_⟩
  have := h d
  calc
    f = f ≫ inv g ≫ g := by simp only [inv_eq_inv, IsIso.inv_hom_id, Category.comp_id]
    _ = f ≫ inv f ≫ g := by congr 1
                            simp only [inv_eq_inv, IsIso.inv_hom_id, eq_iff_true_of_subsingleton]
    _ = g := by simp only [inv_eq_inv, IsIso.hom_inv_id_assoc]

中文:
定理 isThin_iff
  结论: 箭图.IsThin C ↔ 对任意 c : C, 子单例 (c ⟶ c)
  证明: by
  refine ⟨fun h c => h c c, fun h c d => Subsingleton.intro fun f g => ?_⟩
  have := h d
  calc
    f = f ≫ inv g ≫ g := by simp only [inv_eq_inv, IsIso.inv_hom_id, Category.comp_id]
    _ = f ≫ inv f ≫ g := by congr 1
                            simp only [inv_eq_inv, IsIso.inv_hom_id, eq_iff_true_of_subsingleton]
    _ = g := by simp only [inv_eq_inv, IsIso.hom_inv_id_assoc]

Depends on / 依赖: Category, Category.comp_id, IsIso.hom_inv_id_assoc, IsIso.inv_hom_id, Subsingleton, Subsingleton.intro, comp_id, eq_iff_true_of_subsingleton, hom_inv_id_assoc, inv_eq_inv, inv_hom_id
-/
theorem isThin_iff : Quiver.IsThin C ↔ forall c : C, Subsingleton (c ⟶ c) := by
  refine ⟨fun h c => h c c, fun h c d => Subsingleton.intro fun f g => ?_⟩
  have := h d
  calc
    f = f ≫ inv g ≫ g := by simp only [inv_eq_inv, IsIso.inv_hom_id, Category.comp_id]
    _ = f ≫ inv f ≫ g := by congr 1
                            simp only [inv_eq_inv, IsIso.inv_hom_id, eq_iff_true_of_subsingleton]
    _ = g := by simp only [inv_eq_inv, IsIso.hom_inv_id_assoc]

end Thin

section Disconnected

/--
Definition of `IsTotallyDisconnected` / `IsTotallyDisconnected` 的定义

English:
definition IsTotallyDisconnected
  body: forall c d : C, (c ⟶ d) -> c = d

中文:
定义 IsTotallyDisconnected
  定义体: forall c d : C, (c ⟶ d) -> c = d
-/
def IsTotallyDisconnected :=
  forall c d : C, (c ⟶ d) -> c = d

end Disconnected

end Groupoid

end CategoryTheory
