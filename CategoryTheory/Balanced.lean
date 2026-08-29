/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.EpiMono

/-!
# Balanced categories

A category is called balanced if any morphism that is both monic and epic is an isomorphism.

Balanced categories arise frequently. For example, categories in which every monomorphism
(or epimorphism) is strong are balanced. Examples of this are abelian categories and toposes, such
as the category of types.

-/

public section


universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

variable (C) in
/--
Definition of `Balanced` / `Balanced` 的定义

English:
class Balanced
  parameters: : Prop where
  axioms and operations (1):
    - isIso_of_mono_of_epi : forall {X Y : C} (f : X ⟶ Y) [Mono f] [Epi f], IsIso f

中文:
类 Balanced
  参数: : 命题 where
  公理与运算 (1 个):
    - isIso_of_mono_of_epi : 对任意 {X Y : C} (f : X ⟶ Y) [Mono f] [Epi f], IsIso f

Depends on / 依赖: Balanced, Balanced.isIso_of_mono_of_epi, isIso_of_mono_of_epi
-/
class Balanced : Prop where
  isIso_of_mono_of_epi : forall {X Y : C} (f : X ⟶ Y) [Mono f] [Epi f], IsIso f

attribute [to_dual self (reorder := X Y, 7 8)] Balanced.isIso_of_mono_of_epi
attribute [to_dual self (reorder := isIso_of_mono_of_epi (X Y, 4 5))] Balanced.mk

@[to_dual self (reorder := X Y, 7 8)]
/--
theorem `isIso_of_mono_of_epi` / 定理 `isIso_of_mono_of_epi`

English:
theorem isIso_of_mono_of_epi
  given: [Balanced C] {X Y : C} (f : X ⟶ Y) [Mono f] [Epi f]
  statement: IsIso f
  proof: Balanced.isIso_of_mono_of_epi _

@[to_dual isIso_iff_epi_and_mono]

中文:
定理 isIso_of_mono_of_epi
  条件: [Balanced C] {X Y : C} (f : X ⟶ Y) [Mono f] [Epi f]
  结论: IsIso f
  证明: Balanced.isIso_of_mono_of_epi _

@[to_dual isIso_iff_epi_and_mono]

Depends on / 依赖: Balanced, Balanced.isIso_of_mono_of_epi, isIso_of_mono_of_epi
-/
theorem isIso_of_mono_of_epi [Balanced C] {X Y : C} (f : X ⟶ Y) [Mono f] [Epi f] : IsIso f :=
  Balanced.isIso_of_mono_of_epi _

@[to_dual isIso_iff_epi_and_mono]
/--
theorem `isIso_iff_mono_and_epi` / 定理 `isIso_iff_mono_and_epi`

English:
theorem isIso_iff_mono_and_epi
  given: [Balanced C] {X Y : C} (f : X ⟶ Y)
  statement: IsIso f ↔ Mono f ∧ Epi f
  proof: ⟨fun _ => ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ => isIso_of_mono_of_epi _⟩

中文:
定理 isIso_iff_mono_and_epi
  条件: [Balanced C] {X Y : C} (f : X ⟶ Y)
  结论: IsIso f ↔ Mono f ∧ Epi f
  证明: ⟨fun _ => ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ => isIso_of_mono_of_epi _⟩

Depends on / 依赖: isIso_of_mono_of_epi
-/
theorem isIso_iff_mono_and_epi [Balanced C] {X Y : C} (f : X ⟶ Y) : IsIso f ↔ Mono f ∧ Epi f :=
  ⟨fun _ => ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ => isIso_of_mono_of_epi _⟩

section

attribute [local instance] isIso_of_mono_of_epi

/--
Instance `balanced_opposite` / 实例 `balanced_opposite`

English:
instance balanced_opposite
  signature: [Balanced C]
  body: { isIso_of_mono_of_epi := fun f fmono fepi => by
      rw [← Quiver.Hom.op_unop f]
      exact isIso_of_op _ }

中文:
实例 balanced_opposite
  签名: [Balanced C]
  定义体: { isIso_of_mono_of_epi := fun f fmono fepi => by
      rw [← Quiver.Hom.op_unop f]
      exact isIso_of_op _ }

Depends on / 依赖: Quiver, Quiver.Hom.op_unop, isIso_of_mono_of_epi, isIso_of_op, op_unop
-/
instance balanced_opposite [Balanced C] : Balanced Cᵒᵖ :=
  { isIso_of_mono_of_epi := fun f fmono fepi => by
      rw [← Quiver.Hom.op_unop f]
      exact isIso_of_op _ }

end

end CategoryTheory
