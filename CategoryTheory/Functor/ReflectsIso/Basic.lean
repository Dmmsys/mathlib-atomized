/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Iso
public import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# Functors which reflect isomorphisms

A functor `F` reflects isomorphisms if whenever `F.map f` is an isomorphism, `f` was too.

It is formalized as a `Prop`-valued typeclass `ReflectsIsomorphisms F`.

Any fully faithful functor reflects isomorphisms.
-/

public section

namespace CategoryTheory

open CategoryTheory.Functor

variable {C : Type*} [Category* C]
  {D : Type*} [Category* D]
  {E : Type*} [Category* E]

section ReflectsIso

/-- Define what it means for a functor `F : C ⥤ D` to reflect isomorphisms: for any
morphism `f : A ⟶ B`, if `F.map f` is an isomorphism then `f` is as well.
Note that we do not assume or require that `F` is faithful.
-/
/-
**CategoryTheory.Functor.ReflectsIsomorphisms** 是 Mathlib 中的一个归纳类型，位于命名空间 `Categ
oryTheory.Functor`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {D 
: Type u_2} → [inst_1 : CategoryTheory.Category.{v_2, u_2} D] → CategoryTheory.F
unctor C D → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Define what it means for a functor `F : C ⥤ D` to reflect isomorphisms: for any
morphism `f : A ⟶ B`, if `F.map f` is an isomorphism then `f` is as well.
Note that we do not assume or require that `F` is faithful.
-/
class Functor.ReflectsIsomorphisms (F : C ⥤ D) : Prop where
  /-- For any `f`, if `F.map f` is an iso, then so was `f`. -/
  reflects : ∀ {A B : C} (f : A ⟶ B) [IsIso (F.map f)], IsIso f

attribute [to_dual self] Functor.ReflectsIsomorphisms.reflects Functor.ReflectsIsomorphisms.mk

/-- If `F` reflects isos and `F.map f` is an iso, then `f` is an iso. -/
/-
**CategoryTheory.isIso_of_reflects_iso** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
`。
形式化陈述：isIso_of_reflects_iso {A B : C} (f : A ⟶ B) (F : C ⥤ D) [IsIso (F.map f)] 
[F.ReflectsIsomorphisms] : IsIso f
参数：f : A ⟶ B；F : C ⥤ D；F.map f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.ReflectsIsomorphisms.reflects`：∀ {C : Type u_1} {
inst : CategoryTheory.Category.{v_1, u_1} C} {D : Type u_2}   {inst_1 : Category
Theory.Category.{v_2, u_2} D} (F : Categor…

--- 原说明 ---
If `F` reflects isos and `F.map f` is an iso, then `f` is an iso.
-/
theorem isIso_of_reflects_iso {A B : C} (f : A ⟶ B) (F : C ⥤ D) [IsIso (F.map f)]
    [F.ReflectsIsomorphisms] : IsIso f :=
  ReflectsIsomorphisms.reflects F f
/-
**CategoryTheory.isIso_iff_of_reflects_iso** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory`。
形式化陈述：isIso_iff_of_reflects_iso {A B : C} (f : A ⟶ B) (F : C ⥤ D) [F.ReflectsIso
morphisms] : IsIso (F.map f) ↔ IsIso f
参数：f : A ⟶ B；F : C ⥤ D。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.isIso_of_reflects_iso`：isIso_of_reflects_iso {A B : C} (f
 : A ⟶ B) (F : C ⥤ D) [IsIso (F.map f)] [F.ReflectsIsomorphisms] : IsIso f
-/
lemma isIso_iff_of_reflects_iso {A B : C} (f : A ⟶ B) (F : C ⥤ D) [F.ReflectsIsomorphisms] :
    IsIso (F.map f) ↔ IsIso f :=
  ⟨fun _ => isIso_of_reflects_iso f F, fun _ => inferInstance⟩
/-
**CategoryTheory.Functor.FullyFaithful.reflectsIsomorphisms** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.Functor.FullyFaithful`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u
_2}   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] {F : CategoryTheory.Functo
r C D} (hF : F.FullyFaithful),   F.ReflectsIsomorphisms
参数：hF : F.FullyFaithful。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.FullyFaithful.isIso_of_isIso_map`：isIso_of_isIso_
map {X Y : C} (f : X ⟶ Y) [IsIso (F.map f)] : IsIso f
-/
lemma Functor.FullyFaithful.reflectsIsomorphisms {F : C ⥤ D} (hF : F.FullyFaithful) :
    F.ReflectsIsomorphisms where
  reflects _ _ := hF.isIso_of_isIso_map _
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) reflectsIsomorphisms_of_full_and_faithful
    (F : C ⥤ D) [F.Full] [F.Faithful] :
    F.ReflectsIsomorphisms :=
  (Functor.FullyFaithful.ofFullyFaithful F).reflectsIsomorphisms
/-
**CategoryTheory.reflectsIsomorphisms_comp** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTh
eory`。
形式化陈述：reflectsIsomorphisms_comp (F : C ⥤ D) (G : D ⥤ E) [F.ReflectsIsomorphisms]
 [G.ReflectsIsomorphisms] : (F ⋙ G).ReflectsIsomorphisms
参数：F : C ⥤ D；G : D ⥤ E。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.isIso_of_reflects_iso`：isIso_of_reflects_iso {A B : C} (f
 : A ⟶ B) (F : C ⥤ D) [IsIso (F.map f)] [F.ReflectsIsomorphisms] : IsIso f
-/
instance reflectsIsomorphisms_comp (F : C ⥤ D) (G : D ⥤ E)
    [F.ReflectsIsomorphisms] [G.ReflectsIsomorphisms] :
    (F ⋙ G).ReflectsIsomorphisms :=
  ⟨fun f (hf : IsIso (G.map _)) => by
    have := isIso_of_reflects_iso (F.map f) G
    exact isIso_of_reflects_iso f F⟩

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.reflectsIsomorphisms_of_comp** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory`。
形式化陈述：reflectsIsomorphisms_of_comp (F : C ⥤ D) (G : D ⥤ E) [(F ⋙ G).ReflectsIsom
orphisms] : F.ReflectsIsomorphisms where reflects f _
参数：F : C ⥤ D；G : D ⥤ E；F ⋙ G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.isIso_iff_of_reflects_iso`：isIso_iff_of_reflects_iso {A B
 : C} (f : A ⟶ B) (F : C ⥤ D) [F.ReflectsIsomorphisms] : IsIso (F.map f) ↔ IsIso
 f
-/
lemma reflectsIsomorphisms_of_comp (F : C ⥤ D) (G : D ⥤ E)
    [(F ⋙ G).ReflectsIsomorphisms] : F.ReflectsIsomorphisms where
  reflects f _ := by
    rw [← isIso_iff_of_reflects_iso _ (F ⋙ G)]
    dsimp
    infer_instance
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : D ⥤ E) [F.ReflectsIsomorphisms] :
    ((whiskeringRight C D E).obj F).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro Z
    rw [← isIso_iff_of_reflects_iso _ F]
    change IsIso ((((whiskeringRight C D E).obj F).map f).app Z)
    infer_instance
/-
**CategoryTheory.reflectsIsomorphisms_of_iso** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory`。
形式化陈述：reflectsIsomorphisms_of_iso {F G : C ⥤ D} (α : F ≅ G) [F.ReflectsIsomorphi
sms] : G.ReflectsIsomorphisms where reflects f _
参数：α : F ≅ G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.isIso_iff_of_reflects_iso`：isIso_iff_of_reflects_iso {A B
 : C} (f : A ⟶ B) (F : C ⥤ D) [F.ReflectsIsomorphisms] : IsIso (F.map f) ↔ IsIso
 f
· 使用定理 `CategoryTheory.NatIso.naturality_2`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.NatIso.hom_app_isIso`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.NatIso.inv_app_isIso`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
-/
lemma reflectsIsomorphisms_of_iso {F G : C ⥤ D} (α : F ≅ G) [F.ReflectsIsomorphisms] :
    G.ReflectsIsomorphisms where
  reflects f _ := by
    rw [← isIso_iff_of_reflects_iso _ F, ← NatIso.naturality_2 α f]
    infer_instance
/-
**CategoryTheory.reflectsIsomorphisms_iso_iff** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory`。
形式化陈述：reflectsIsomorphisms_iso_iff {F G : C ⥤ D} (α : F ≅ G) : F.ReflectsIsomorp
hisms ↔ G.ReflectsIsomorphisms
参数：α : F ≅ G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.reflectsIsomorphisms_of_iso`：reflectsIsomorphisms_of_iso 
{F G : C ⥤ D} (α : F ≅ G) [F.ReflectsIsomorphisms] : G.ReflectsIsomorphisms wher
e reflects f _
-/
lemma reflectsIsomorphisms_iso_iff {F G : C ⥤ D} (α : F ≅ G) :
    F.ReflectsIsomorphisms ↔ G.ReflectsIsomorphisms :=
  ⟨fun _ => reflectsIsomorphisms_of_iso α,
  fun _ => reflectsIsomorphisms_of_iso α.symm⟩

end ReflectsIso

end CategoryTheory

