/-
Copyright (c) 2026 Blake Farman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Blake Farman
-/
module
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Subobject.MonoOver
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# Preradicals

A **preradical** on an abelian category `C` is a monomorphism in the functor category `C ⥤ C`
with codomain `𝟭 C`, i.e. an element of `MonoOver (𝟭 C)`.

## Main definitions

* `Preradical C`: The type of preradicals on `C`.
* `Preradical.r`: The underlying endofunctor of a `Preradical`.
* `Preradical.ι`: The structure morphism of a `Preradical`.
* `Preradical.IsIdempotent`: The predicate expressing idempotence.

## References

* [Bo Stenström, *Rings and Modules of Quotients*][stenstrom1971]
* [Bo Stenström, *Rings of Quotients*][stenstrom1975]

## Tags

category theory, preradical, torsion theory
-/

public section

universe v u

namespace CategoryTheory.Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]

variable (C) in
/-- A preradical on an abelian category `C` is a monomorphism in `C ⥤ C` with codomain `𝟭 C`. -/
/-
**CategoryTheory.Abelian.Preradical** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.
Abelian`。
形式化陈述：Preradical
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A preradical on an abelian category `C` is a monomorphism in `C ⥤ C` with codoma
in `𝟭 C`.
-/
abbrev Preradical := MonoOver (𝟭 C)

namespace Preradical

variable (Φ : Preradical C)

/-- The underlying endofunctor `r : C ⥤ C` of a preradical `Φ`. -/
/-
**CategoryTheory.Abelian.Preradical.r** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheor
y.Abelian.Preradical`。
形式化陈述：r : C ⥤ C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The underlying endofunctor `r : C ⥤ C` of a preradical `Φ`.
-/
abbrev r : C ⥤ C := Φ.obj.left

/-- The structure morphism `Φ.r ⟶ 𝟭 C` of a preradical `Φ`. -/
/-
**CategoryTheory.Abelian.Preradical.** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory
.Abelian.Preradical`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The structure morphism `Φ.r ⟶ 𝟭 C` of a preradical `Φ`.
-/
abbrev ι : Φ.r ⟶ 𝟭 C := Φ.obj.hom

@[simp]
/-
**CategoryTheory.Abelian.Preradical.r_map_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.Abelian.Preradical`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma r_map_ι_app (X : C) : Φ.r.map (Φ.ι.app X) = Φ.ι.app (Φ.r.obj X) := by
  rw [← cancel_mono (Φ.ι.app X)]
  exact Φ.ι.naturality (Φ.ι.app X)

/-- A preradical `Φ` is idempotent if `Φ.r ⋙ Φ.r ≅ Φ.r`. -/
/-
**CategoryTheory.Abelian.Preradical.IsIdempotent** 是 Mathlib 中的一个归纳类型，位于命名空间 `Ca
tegoryTheory.Abelian.Preradical`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → CategoryTheory.
Abelian.Preradical C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A preradical `Φ` is idempotent if `Φ.r ⋙ Φ.r ≅ Φ.r`.
-/
class IsIdempotent : Prop where
  isIso_whiskerLeft_r_ι : IsIso (Functor.whiskerLeft Φ.r Φ.ι)

attribute [instance] IsIdempotent.isIso_whiskerLeft_r_ι
/-
**CategoryTheory.Abelian.Preradical.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.A
belian.Preradical`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Φ.IsIdempotent] (X : C) :
    IsIso (Φ.ι.app (Φ.r.obj X)) :=
  inferInstanceAs (IsIso ((Functor.whiskerLeft Φ.r Φ.ι).app X))
/-
**CategoryTheory.Abelian.Preradical.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.A
belian.Preradical`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Φ.IsIdempotent] (X : C) :
    IsIso (Φ.r.map (Φ.ι.app X)) := by
  rw [r_map_ι_app]
  infer_instance

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Abelian.Preradical.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.A
belian.Preradical`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {D : Type*} [Category* D] (F : D ⥤ C) :
    Mono (Functor.whiskerLeft F Φ.ι) := by
  rw [NatTrans.mono_iff_mono_app]
  intro
  dsimp
  infer_instance

end Preradical

end CategoryTheory.Abelian

