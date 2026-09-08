/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Triangulated.TStructure.Basic
public import Mathlib.CategoryTheory.Triangulated.Subcategory

/-!
# Truncations for a t-structure

Let `t` be a t-structure on a (pre)triangulated category `C`.
In this file, for any `n : ℤ`, we construct truncation functors `t.truncLT n : C ⥤ C`,
`t.truncGE n : C ⥤ C` and natural transformations `t.truncLTι n : t.truncLT n ⟶ 𝟭 C`,
`t.truncGEπ n : 𝟭 C ⟶ t.truncGE n` and
`t.truncGEδLT n : t.truncGE n ⟶ t.truncLT n ⋙ shiftFunctor C (1 : ℤ)` which are
part of a distinguished triangle
`(t.truncLT n).obj X ⟶ X ⟶ (t.truncGE n).obj X ⟶ ((t.truncLT n).obj X)⟦1⟧` for any `X : C`,
with `(t.truncLT n).obj X < n` and `(t.truncGE n).obj X ≥ n`.

We obtain various properties of these truncation functors.
Variants `truncGT` and `truncLE` are introduced in the file
`Mathlib/CategoryTheory/Triangulated/TStucture/TruncLEGT.lean`.
Extensions to indices in `EInt` instead of `ℤ` are introduced in the file
`Mathlib/CategoryTheory/Triangulated/TStucture/ETrunc.lean`.
The spectral object attached to an object `X : C` is constructed in the file
`Mathlib/CategoryTheory/Triangulated/TStucture/SpectralObject.lean`.

-/

universe v u

namespace CategoryTheory

open Limits Pretriangulated ZeroObject

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

namespace Triangulated

namespace TStructure

variable (t : TStructure C)

set_option backward.isDefEq.respectTransparency false in
/-- Two morphisms `T ⟶ T'` between distinguished triangles must coincide when
they coincide on the middle object, and there are integers `a ≤ b` such that
for a t-structure, we have `T.obj₁ ≤ a` and `T'.obj₃ ≥ b`. -/
public lemma triangle_map_ext {T T' : Triangle C} {f₁ f₂ : T ⟶ T'}
    (hT : T ∈ distTriang C) (hT' : T' ∈ distTriang C) (a b : ℤ)
    (h₀ : t.IsLE T.obj₁ a) (h₁ : t.IsGE T'.obj₃ b)
    (H : f₁.hom₂ = f₂.hom₂ := by cat_disch)
    (hab : a ≤ b := by lia) : f₁ = f₂ := by
  suffices ∀ (f : T ⟶ T'), f.hom₂ = 0 → f = 0 by rw [← sub_eq_zero]; cat_disch
  intro f hf
  ext
  · obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₂ _ (inv_rot_of_distTriang _ hT')
      f.hom₁ (by simp [← f.comm₁, hf])
    simp [hg, t.zero_of_isLE_of_isGE g a (b + 1) (by lia)
      h₀ (t.isGE_shift _ b (-1) (b + 1))]
  · simp [hf]
  · obtain ⟨g, hg⟩ := T.yoneda_exact₃ hT f.hom₃ (by cat_disch)
    simp [hg, t.zero_of_isLE_of_isGE g (a - 1) b (by lia)
      (t.isLE_shift _ a 1 (a - 1)) inferInstance]

/-- If `a < b`, then a morphism `T.obj₂ ⟶ T'.obj₂` extends to a morphism `T ⟶ T'`
of distinguished triangles when for a t-structure `T.obj₁ ≤ a` and `T'.obj₃ ≥ b`. -/
public lemma triangle_map_exists {T T' : Triangle C}
    (hT : T ∈ distTriang C) (hT' : T' ∈ distTriang C)
    (φ : T.obj₂ ⟶ T'.obj₂) (a b : ℤ)
    (h₀ : t.IsLE T.obj₁ a) (h₁' : t.IsGE T'.obj₃ b) (h : a < b := by lia) :
    ∃ (f : T ⟶ T'), f.hom₂ = φ := by
  obtain ⟨a, comm₁⟩ := T'.coyoneda_exact₂ hT' (T.mor₁ ≫ φ) (t.zero _ a b)
  obtain ⟨c, comm₂, comm₃⟩ := complete_distinguished_triangle_morphism _ _ hT hT' a φ comm₁
  exact ⟨{ hom₁ := a, hom₂ := φ, hom₃ := c }, rfl⟩

/-- If `a < b`, then an isomorphism `T.obj₂ ≅ T'.obj₂` extends to an isomorphism `T ≅ T'`
of distinguished triangles when for a t-structure, both `T.obj₁` and `T'.obj₁` are `≤ a` and
both `T.obj₃` and `T'.obj₃` are `≥ b`. -/
public lemma triangle_iso_exists {T T' : Triangle C}
    (hT : T ∈ distTriang C) (hT' : T' ∈ distTriang C) (e : T.obj₂ ≅ T'.obj₂)
    (a b : ℤ) (h₀ : t.IsLE T.obj₁ a) (h₁ : t.IsGE T.obj₃ b)
    (h₀' : t.IsLE T'.obj₁ a) (h₁' : t.IsGE T'.obj₃ b) (h : a < b := by lia) :
    ∃ (e' : T ≅ T'), e'.hom.hom₂ = e.hom := by
  obtain ⟨hom, hhom⟩ := triangle_map_exists t hT hT' e.hom _ _ h₀ h₁'
  obtain ⟨inv, _⟩ := triangle_map_exists t hT' hT e.inv _ _ h₀' h₁
  exact
    ⟨{hom := hom
      inv := inv
      hom_inv_id := triangle_map_ext t hT hT a b h₀ h₁
      inv_hom_id := triangle_map_ext t hT' hT' a b h₀' h₁' }, hhom⟩

namespace TruncAux
/-! The private definitions in the namespace `TStructure.TruncAux` are part of the
implementation of the truncation functors `truncLT`, `truncGE` and the
distinguished triangles they fit in. -/

variable (n : ℤ) (X : C)

/-- Given a t-structure `t` on `C`, `X : C` and `n : ℤ`, this is a distinguished
triangle `obj₁ ⟶ X ⟶ obj₃ ⟶ obj₁⟦1⟧` where `obj₁` is `< n` and `obj₃` is `≥ n`.
(This should not be used directly: use `truncLT` and `truncGE` instead.) -/
@[simps! obj₂]
/-
**CategoryTheory.Triangulated.TStructure.TruncAux.triangle** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.Triangulated.TStructure.TruncAux`。
形式化陈述：triangle : Triangle C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a t-structure `t` on `C`, `X : C` and `n : ℤ`, this is a distinguished
triangle `obj₁ ⟶ X ⟶ obj₃ ⟶ obj₁⟦1⟧` where `obj₁` is `< n` and `obj₃` is `≥ n`.
(This should not be used directly: use `truncLT` and `truncGE` instead.)
-/
noncomputable def triangle : Triangle C :=
  Triangle.mk
    (t.exists_triangle X (n - 1) n
      (by lia)).choose_spec.choose_spec.choose_spec.choose_spec.choose
    (t.exists_triangle X (n - 1) n
      (by lia)).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose
    (t.exists_triangle X (n - 1) n
      (by lia)).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose
/-
**CategoryTheory.Triangulated.TStructure.TruncAux.triangle_distinguished** 是 Mat
hlib 中的一个引理，位于命名空间 `CategoryTheory.Triangulated.TStructure.TruncAux`。
形式化陈述：triangle_distinguished : triangle t n X in distTriang C
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma triangle_distinguished :
    triangle t n X ∈ distTriang C :=
  (t.exists_triangle X (n - 1) n
    (by lia)).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec
/-
**CategoryTheory.Triangulated.TStructure.TruncAux.triangle_obj** 是 Mathlib 中的一个实
例，位于命名空间 `CategoryTheory.Triangulated.TStructure.TruncAux`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance triangle_obj₁_isLE (n : ℤ) :
    t.IsLE (triangle t n X).obj₁ (n - 1) :=
  ⟨(t.exists_triangle X (n - 1) n (by lia)).choose_spec.choose_spec.choose⟩
/-
**CategoryTheory.Triangulated.TStructure.TruncAux.triangle_obj** 是 Mathlib 中的一个实
例，位于命名空间 `CategoryTheory.Triangulated.TStructure.TruncAux`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance triangle_obj₃_isGE :
    t.IsGE (triangle t n X).obj₃ n :=
  ⟨(t.exists_triangle X (n - 1) n (by lia)).choose_spec.choose_spec.choose_spec.choose⟩

variable {X} {Y : C} (φ : X ⟶ Y)

/-- Version of `TStructure.triangle_map_ext` that is specialized for the auxiliary
definition `TruncAux.triangle`. -/
@[ext]
/-
**CategoryTheory.Triangulated.TStructure.TruncAux.triangle_map_ext'** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.Triangulated.TStructure.TruncAux`。
形式化陈述：triangle_map_ext' (f₁ f₂ : triangle t n X ⟶ triangle t n Y) (H : f₁.hom₂ =
 f₂.hom₂
参数：f₁ f₂ : triangle t n X ⟶ triangle t n Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Version of `TStructure.triangle_map_ext` that is specialized for the auxiliary
definition `TruncAux.triangle`.
-/
lemma triangle_map_ext' (f₁ f₂ : triangle t n X ⟶ triangle t n Y)
    (H : f₁.hom₂ = f₂.hom₂ := by cat_disch) : f₁ = f₂ :=
  triangle_map_ext t (triangle_distinguished t n X) (triangle_distinguished t n Y) (n - 1) n
    inferInstance inferInstance H (by lia)

/-- Auxiliary definition for `triangleFunctor`. -/
@[simps hom₂]
/-
**CategoryTheory.Triangulated.TStructure.TruncAux.triangleMap** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.Triangulated.TStructure.TruncAux`。
形式化陈述：triangleMap : triangle t n X ⟶ triangle t n Y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `triangleFunctor`.
-/
noncomputable def triangleMap : triangle t n X ⟶ triangle t n Y :=
  have H := triangle_map_exists t (triangle_distinguished t n X)
    (triangle_distinguished t n Y) φ (n - 1) n inferInstance inferInstance (by lia)
  { hom₁ := H.choose.hom₁
    hom₂ := φ
    hom₃ := H.choose.hom₃
    comm₁ := by rw [← H.choose.comm₁, H.choose_spec]
    comm₂ := by rw [H.choose.comm₂, H.choose_spec]
    comm₃ := H.choose.comm₃ }

/-- Given a t-structure `t` on `C` and `n : ℤ`, this is the
functorial (distinguished) triangle `obj₁ ⟶ X ⟶ obj₃ ⟶ obj₁⟦1⟧` for any `X : C`,
where `obj₁` is `< n` and `obj₃` is `≥ n`.
(This should not be used directly: use `triangleLTGE` instead.) -/
@[simps]
/-
**CategoryTheory.Triangulated.TStructure.TruncAux.triangleFunctor** 是 Mathlib 中的
一个定义，位于命名空间 `CategoryTheory.Triangulated.TStructure.TruncAux`。
形式化陈述：triangleFunctor : C ⥤ Triangle C where obj
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a t-structure `t` on `C` and `n : ℤ`, this is the
functorial (distinguished) triangle `obj₁ ⟶ X ⟶ obj₃ ⟶ obj₁⟦1⟧` for any `X : C`,
where `obj₁` is `< n` and `obj₃` is `≥ n`.
(This should not be used directly: use `triangleLTGE` instead.)
-/
noncomputable def triangleFunctor : C ⥤ Triangle C where
  obj := triangle t n
  map φ := triangleMap t n φ

variable (A)
/-
**CategoryTheory.Triangulated.TStructure.TruncAux.triangleFunctor_obj_distinguis
hed** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Triangulated.TStructure.TruncAux`。
形式化陈述：triangleFunctor_obj_distinguished : (triangleFunctor t n).obj A in distTri
ang C
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma triangleFunctor_obj_distinguished :
    (triangleFunctor t n).obj A ∈ distTriang C :=
  triangle_distinguished t n A
/-
**CategoryTheory.Triangulated.TStructure.TruncAux.isLE_triangleFunctor_obj_obj**
 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Triangulated.TStructure.TruncAux`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isLE_triangleFunctor_obj_obj₁ :
    t.IsLE ((triangleFunctor t n).obj A).obj₁ (n - 1) := by
  dsimp [triangleFunctor]
  infer_instance
/-
**CategoryTheory.Triangulated.TStructure.TruncAux.isGE_triangleFunctor_obj_obj**
 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Triangulated.TStructure.TruncAux`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isGE_triangleFunctor_obj_obj₃ :
    t.IsGE ((triangleFunctor t n).obj A).obj₃ n := by
  dsimp [triangleFunctor]
  infer_instance
/-
**CategoryTheory.Triangulated.TStructure.TruncAux.triangleMapOfLE** 是 Mathlib 中的
一个定义，位于命名空间 `CategoryTheory.Triangulated.TStructure.TruncAux`。
形式化陈述：triangleMapOfLE (a b : Int) (h : a <= b) : triangle t a A ⟶ triangle t b A
参数：a b : Int；h : a <= b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def triangleMapOfLE (a b : ℤ) (h : a ≤ b) : triangle t a A ⟶ triangle t b A :=
  have H := triangle_map_exists t (triangle_distinguished t a A)
    (triangle_distinguished t b A) (𝟙 _) (a - 1) b inferInstance inferInstance
  { hom₁ := H.choose.hom₁
    hom₂ := 𝟙 _
    hom₃ := H.choose.hom₃
    comm₁ := by rw [← H.choose.comm₁, H.choose_spec]
    comm₂ := by rw [H.choose.comm₂, H.choose_spec]
    comm₃ := H.choose.comm₃ }

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Triangulated.TStructure.TruncAux.triangleFunctorNatTransOfLE** 
是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Triangulated.TStructure.TruncAux`。
形式化陈述：triangleFunctorNatTransOfLE (a b : Int) (h : a <= b) : triangleFunctor t a
 ⟶ triangleFunctor t b where app X
参数：a b : Int；h : a <= b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def triangleFunctorNatTransOfLE (a b : ℤ) (h : a ≤ b) :
    triangleFunctor t a ⟶ triangleFunctor t b where
  app X := triangleMapOfLE t X a b h
  naturality _ _ _ :=
    triangle_map_ext t (triangleFunctor_obj_distinguished _ _ _)
      (triangleFunctor_obj_distinguished _ _ _) (a - 1) b inferInstance inferInstance
        (by simp [triangleMapOfLE])

@[simp]
/-
**CategoryTheory.Triangulated.TStructure.TruncAux.triangleFunctorNatTransOfLE_ap
p_hom** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Triangulated.TStructure.TruncAux
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma triangleFunctorNatTransOfLE_app_hom₂ (a b : ℤ) (h : a ≤ b) (X : C) :
    ((triangleFunctorNatTransOfLE t a b h).app X).hom₂ = 𝟙 X := rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Triangulated.TStructure.TruncAux.triangleFunctorNatTransOfLE_tr
ans** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Triangulated.TStructure.TruncAux`。
形式化陈述：triangleFunctorNatTransOfLE_trans (a b c : Int) (hab : a <= b) (hbc : b <=
 c) : triangleFunctorNatTransOfLE t a b hab ≫ triangleFunctorNatTransOfLE t b c 
hbc = triangleFunctorNatTransOfLE t a c (hab.trans hbc)
参数：a b c : Int；hab : a <= b；hbc : b <= c。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma triangleFunctorNatTransOfLE_trans (a b c : ℤ) (hab : a ≤ b) (hbc : b ≤ c) :
    triangleFunctorNatTransOfLE t a b hab ≫ triangleFunctorNatTransOfLE t b c hbc =
      triangleFunctorNatTransOfLE t a c (hab.trans hbc) := by
  apply NatTrans.ext
  ext1 X
  exact triangle_map_ext t (triangleFunctor_obj_distinguished _ _ _)
    (triangleFunctor_obj_distinguished _ _ _) (a - 1) c inferInstance inferInstance (by simp)

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Triangulated.TStructure.TruncAux.triangleFunctorNatTransOfLE_re
fl** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Triangulated.TStructure.TruncAux`。
形式化陈述：triangleFunctorNatTransOfLE_refl (a : Int) : triangleFunctorNatTransOfLE t
 a a (by rfl) = 𝟙 _
参数：a : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma triangleFunctorNatTransOfLE_refl (a : ℤ) :
    triangleFunctorNatTransOfLE t a a (by rfl) = 𝟙 _ := by
  apply NatTrans.ext
  ext1 X
  exact triangle_map_ext t (triangleFunctor_obj_distinguished _ _ _)
    (triangleFunctor_obj_distinguished _ _ _) (a - 1) a inferInstance inferInstance (by simp)

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Triangulated.TStructure.TruncAux.** 是 Mathlib 中的一个实例，位于命名空间 `Ca
tegoryTheory.Triangulated.TStructure.TruncAux`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (triangleFunctor t n).Additive where

end TruncAux

public section

/-- Given a t-structure `t` on a pretriangulated category `C` and `n : ℤ`, this
is the `< n`-truncation functor. See also the natural transformation `truncLTι`. -/
/-
**CategoryTheory.Triangulated.TStructure.truncLT** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Triangulated.TStructure`。
形式化陈述：truncLT (n : Int) : C ⥤ C
参数：n : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a t-structure `t` on a pretriangulated category `C` and `n : ℤ`, this
is the `< n`-truncation functor. See also the natural transformation `truncLTι`.
-/
noncomputable def truncLT (n : ℤ) : C ⥤ C :=
  TruncAux.triangleFunctor t n ⋙ Triangle.π₁

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Triangulated.TStructure.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : ℤ) : (t.truncLT n).Additive where
  map_add {_ _ _ _} := by
    dsimp only [truncLT, Functor.comp_map]
    rw [Functor.map_add]
    dsimp

/-- The natural transformation `t.truncLT n ⟶ 𝟭 C` when `t` is a t-structure
on a category `C` and `n : ℤ`. -/
/-
**CategoryTheory.Triangulated.TStructure.truncLT** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Triangulated.TStructure`。
形式化陈述：truncLT (n : Int) : C ⥤ C
参数：n : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural transformation `t.truncLT n ⟶ 𝟭 C` when `t` is a t-structure
on a category `C` and `n : ℤ`.
-/
noncomputable def truncLTι (n : ℤ) : t.truncLT n ⟶ 𝟭 _ :=
  Functor.whiskerLeft (TruncAux.triangleFunctor t n) Triangle.π₁Toπ₂

/-- Given a t-structure `t` on a pretriangulated category `C` and `n : ℤ`, this
is the `≥ n`-truncation functor. See also the natural transformation `truncGEπ`. -/
/-
**CategoryTheory.Triangulated.TStructure.truncGE** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Triangulated.TStructure`。
形式化陈述：truncGE (n : Int) : C ⥤ C
参数：n : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a t-structure `t` on a pretriangulated category `C` and `n : ℤ`, this
is the `≥ n`-truncation functor. See also the natural transformation `truncGEπ`.
-/
noncomputable def truncGE (n : ℤ) : C ⥤ C :=
  TruncAux.triangleFunctor t n ⋙ Triangle.π₃

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Triangulated.TStructure.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : ℤ) : (t.truncGE n).Additive where
  map_add {_ _ _ _} := by
    dsimp only [truncGE, Functor.comp_map]
    rw [Functor.map_add]
    dsimp

/-- The natural transformation `𝟭 C ⟶ t.truncGE n` when `t` is a t-structure
on a category `C` and `n : ℤ`. -/
/-
**CategoryTheory.Triangulated.TStructure.truncGE** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Triangulated.TStructure`。
形式化陈述：truncGE (n : Int) : C ⥤ C
参数：n : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural transformation `𝟭 C ⟶ t.truncGE n` when `t` is a t-structure
on a category `C` and `n : ℤ`.
-/
noncomputable def truncGEπ (n : ℤ) : 𝟭 _ ⟶ t.truncGE n :=
  Functor.whiskerLeft (TruncAux.triangleFunctor t n) Triangle.π₂Toπ₃

@[reassoc (attr := simp)]
/-
**CategoryTheory.Triangulated.TStructure.truncGE** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Triangulated.TStructure`。
形式化陈述：truncGE (n : Int) : C ⥤ C
参数：n : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma truncGEπ_naturality (n : ℤ) {X Y : C} (f : X ⟶ Y) :
    (t.truncGEπ n).app X ≫ (t.truncGE n).map f = f ≫ (t.truncGEπ n).app Y :=
  ((t.truncGEπ n).naturality f).symm

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Triangulated.TStructure.isLE_truncLT_obj** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：isLE_truncLT_obj (X : C) (a b : Int) (hn : a <= b + 1
参数：X : C；a b : Int。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE.0.Cate
goryTheory.Triangulated.TStructure.TruncAux.triangle_obj₁_isLE`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]
   [inst_2 : CategoryTheory.Limits.HasZeroOb…
· 使用引理 `CategoryTheory.Triangulated.TStructure.isLE_of_le`：isLE_of_le (X : C) (p
 q : Int) (hpq : p <= q
-/
lemma isLE_truncLT_obj (X : C) (a b : ℤ) (hn : a ≤ b + 1 := by lia) :
    t.IsLE ((t.truncLT a).obj X) b := by
  have : t.IsLE ((t.truncLT a).obj X) (a - 1) := by dsimp [truncLT]; infer_instance
  exact t.isLE_of_le _ (a - 1) _ (by lia)
/-
**CategoryTheory.Triangulated.TStructure.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : C) (n : ℤ) : t.IsLE ((t.truncLT n).obj X) (n - 1) :=
  t.isLE_truncLT_obj ..
/-
**CategoryTheory.Triangulated.TStructure.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : C) (n : ℤ) : t.IsLE ((t.truncLT (n + 1)).obj X) n :=
  t.isLE_truncLT_obj ..

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Triangulated.TStructure.isGE_truncGE_obj** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：isGE_truncGE_obj (X : C) (a b : Int) (hn : b <= a
参数：X : C；a b : Int。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE.0.Cate
goryTheory.Triangulated.TStructure.TruncAux.triangle_obj₃_isGE`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]
   [inst_2 : CategoryTheory.Limits.HasZeroOb…
· 使用引理 `CategoryTheory.Triangulated.TStructure.isGE_of_ge`：isGE_of_ge (X : C) (p
 q : Int) (hpq : p <= q
-/
lemma isGE_truncGE_obj (X : C) (a b : ℤ) (hn : b ≤ a := by lia) :
    t.IsGE ((t.truncGE a).obj X) b := by
  have : t.IsGE ((t.truncGE a).obj X) a := by dsimp [truncGE]; infer_instance
  exact t.isGE_of_ge _ _ a (by lia)
/-
**CategoryTheory.Triangulated.TStructure.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : C) (n : ℤ) : t.IsGE ((t.truncGE n).obj X) n :=
  t.isGE_truncGE_obj ..

/-- The connecting morphism `t.truncGE n ⟶ t.truncLT n ⋙ shiftFunctor C (1 : ℤ)`
when `t` is a t-structure on a pretriangulated category and `n : ℤ`. -/
/-
**CategoryTheory.Triangulated.TStructure.truncGE** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Triangulated.TStructure`。
形式化陈述：truncGE (n : Int) : C ⥤ C
参数：n : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The connecting morphism `t.truncGE n ⟶ t.truncLT n ⋙ shiftFunctor C (1 : ℤ)`
when `t` is a t-structure on a pretriangulated category and `n : ℤ`.
-/
noncomputable def truncGEδLT (n : ℤ) :
    t.truncGE n ⟶ t.truncLT n ⋙ shiftFunctor C (1 : ℤ) :=
  Functor.whiskerLeft (TruncAux.triangleFunctor t n) Triangle.π₃Toπ₁

/-- The distinguished triangle `(t.truncLT n).obj A ⟶ A ⟶ (t.truncGE n).obj A ⟶ ...`
as a functor `C ⥤ Triangle C` when `t` is a `t`-structure on a pretriangulated
category `C` and `n : ℤ`. -/
@[expose, simps!]
/-
**CategoryTheory.Triangulated.TStructure.triangleLTGE** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Triangulated.TStructure`。
形式化陈述：triangleLTGE (n : Int) : C ⥤ Triangle C
参数：n : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The distinguished triangle `(t.truncLT n).obj A ⟶ A ⟶ (t.truncGE n).obj A ⟶ ...`
as a functor `C ⥤ Triangle C` when `t` is a `t`-structure on a pretriangulated
category `C` and `n : ℤ`.
-/
noncomputable def triangleLTGE (n : ℤ) : C ⥤ Triangle C :=
  Triangle.functorMk (t.truncLTι n) (t.truncGEπ n) (t.truncGEδLT n)
/-
**CategoryTheory.Triangulated.TStructure.triangleLTGE_distinguished** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：triangleLTGE_distinguished (n : Int) (X : C) : (t.triangleLTGE n).obj X in
 distTriang C
参数：n : Int；X : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE.0.Cate
goryTheory.Triangulated.TStructure.TruncAux.triangleFunctor_obj_distinguished`：∀
 {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory
.Preadditive C]   [inst_2 : CategoryTheory.Limits.HasZeroOb…
-/
lemma triangleLTGE_distinguished (n : ℤ) (X : C) :
    (t.triangleLTGE n).obj X ∈ distTriang C :=
  TruncAux.triangleFunctor_obj_distinguished t n X

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Triangulated.TStructure.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : C) (n : ℤ) : t.IsLE ((t.triangleLTGE n).obj X).obj₁ (n - 1) := by
  dsimp
  infer_instance

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Triangulated.TStructure.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : C) (n : ℤ) : t.IsGE ((t.triangleLTGE n).obj X).obj₃ n := by
  dsimp
  infer_instance

@[reassoc (attr := simp)]
/-
**CategoryTheory.Triangulated.TStructure.truncLT** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Triangulated.TStructure`。
形式化陈述：truncLT (n : Int) : C ⥤ C
参数：n : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma truncLTι_comp_truncGEπ_app (n : ℤ) (X : C) :
    (t.truncLTι n).app X ≫ (t.truncGEπ n).app X = 0 :=
  comp_distTriang_mor_zero₁₂ _ (t.triangleLTGE_distinguished n X)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Triangulated.TStructure.truncGE** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Triangulated.TStructure`。
形式化陈述：truncGE (n : Int) : C ⥤ C
参数：n : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma truncGEπ_comp_truncGEδLT_app (n : ℤ) (X : C) :
    (t.truncGEπ n).app X ≫ (t.truncGEδLT n).app X = 0 :=
  comp_distTriang_mor_zero₂₃ _ (t.triangleLTGE_distinguished n X)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Triangulated.TStructure.truncGE** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Triangulated.TStructure`。
形式化陈述：truncGE (n : Int) : C ⥤ C
参数：n : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma truncGEδLT_comp_truncLTι_app (n : ℤ) (X : C) :
    (t.truncGEδLT n).app X ≫ ((t.truncLTι n).app X)⟦(1 : ℤ)⟧' = 0 :=
  comp_distTriang_mor_zero₃₁ _ (t.triangleLTGE_distinguished n X)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Triangulated.TStructure.truncLT** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Triangulated.TStructure`。
形式化陈述：truncLT (n : Int) : C ⥤ C
参数：n : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma truncLTι_comp_truncGEπ (n : ℤ) :
    t.truncLTι n ≫ t.truncGEπ n = 0 := by
  cat_disch

@[reassoc (attr := simp)]
/-
**CategoryTheory.Triangulated.TStructure.truncGE** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Triangulated.TStructure`。
形式化陈述：truncGE (n : Int) : C ⥤ C
参数：n : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma truncGEπ_comp_truncGEδLT (n : ℤ) :
    t.truncGEπ n ≫ t.truncGEδLT n = 0 := by cat_disch

@[reassoc (attr := simp)]
/-
**CategoryTheory.Triangulated.TStructure.truncGE** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Triangulated.TStructure`。
形式化陈述：truncGE (n : Int) : C ⥤ C
参数：n : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma truncGEδLT_comp_truncLTι (n : ℤ) :
    t.truncGEδLT n ≫ Functor.whiskerRight (t.truncLTι n) (shiftFunctor C (1 : ℤ)) = 0 := by
  cat_disch

/-- The natural transformation `t.truncLT a ⟶ t.truncLT b` when `a ≤ b`. -/
/-
**CategoryTheory.Triangulated.TStructure.natTransTruncLTOfLE** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：natTransTruncLTOfLE (a b : Int) (h : a <= b) : t.truncLT a ⟶ t.truncLT b
参数：a b : Int；h : a <= b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural transformation `t.truncLT a ⟶ t.truncLT b` when `a ≤ b`.
-/
noncomputable def natTransTruncLTOfLE (a b : ℤ) (h : a ≤ b) :
    t.truncLT a ⟶ t.truncLT b :=
  Functor.whiskerRight (TruncAux.triangleFunctorNatTransOfLE t a b h) Triangle.π₁

/-- The natural transformation `t.truncGE a ⟶ t.truncGE b` when `a ≤ b`. -/
/-
**CategoryTheory.Triangulated.TStructure.natTransTruncGEOfLE** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：natTransTruncGEOfLE (a b : Int) (h : a <= b) : t.truncGE a ⟶ t.truncGE b
参数：a b : Int；h : a <= b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural transformation `t.truncGE a ⟶ t.truncGE b` when `a ≤ b`.
-/
noncomputable def natTransTruncGEOfLE (a b : ℤ) (h : a ≤ b) :
    t.truncGE a ⟶ t.truncGE b :=
  Functor.whiskerRight (TruncAux.triangleFunctorNatTransOfLE t a b h) Triangle.π₃

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Triangulated.TStructure.natTransTruncLTOfLE_** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma natTransTruncLTOfLE_ι_app (a b : ℤ) (h : a ≤ b) (X : C) :
    (t.natTransTruncLTOfLE a b h).app X ≫ (t.truncLTι b).app X = (t.truncLTι a).app X := by
  simpa using! ((TruncAux.triangleFunctorNatTransOfLE t a b h).app X).comm₁.symm

@[reassoc (attr := simp)]
/-
**CategoryTheory.Triangulated.TStructure.natTransTruncLTOfLE_** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma natTransTruncLTOfLE_ι (a b : ℤ) (h : a ≤ b) :
    t.natTransTruncLTOfLE a b h ≫ t.truncLTι b = t.truncLTι a := by
  cat_disch

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Triangulated.TStructure.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma π_natTransTruncGEOfLE_app (a b : ℤ) (h : a ≤ b) (X : C) :
    (t.truncGEπ a).app X ≫ (t.natTransTruncGEOfLE a b h).app X = (t.truncGEπ b).app X := by
  simpa only [TruncAux.triangleFunctor_obj, TruncAux.triangle_obj₂,
    TruncAux.triangleFunctorNatTransOfLE_app_hom₂, Category.id_comp] using!
    ((TruncAux.triangleFunctorNatTransOfLE t a b h).app X).comm₂

@[reassoc]
/-
**CategoryTheory.Triangulated.TStructure.truncGE** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Triangulated.TStructure`。
形式化陈述：truncGE (n : Int) : C ⥤ C
参数：n : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma truncGEδLT_comp_natTransTruncLTOfLE_app (a b : ℤ) (h : a ≤ b) (X : C) :
  (t.truncGEδLT a).app X ≫ ((natTransTruncLTOfLE t a b h).app X)⟦(1 : ℤ)⟧' =
    (t.natTransTruncGEOfLE a b h).app X ≫ (t.truncGEδLT b).app X :=
  ((TruncAux.triangleFunctorNatTransOfLE t a b h).app X).comm₃

@[reassoc]
/-
**CategoryTheory.Triangulated.TStructure.truncGE** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Triangulated.TStructure`。
形式化陈述：truncGE (n : Int) : C ⥤ C
参数：n : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma truncGEδLT_comp_whiskerRight_natTransTruncLTOfLE (a b : ℤ) (h : a ≤ b) :
  t.truncGEδLT a ≫ Functor.whiskerRight (natTransTruncLTOfLE t a b h) (shiftFunctor C (1 : ℤ)) =
    t.natTransTruncGEOfLE a b h ≫ t.truncGEδLT b := by
  ext X
  exact t.truncGEδLT_comp_natTransTruncLTOfLE_app a b h X

@[reassoc (attr := simp)]
/-
**CategoryTheory.Triangulated.TStructure.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma π_natTransTruncGEOfLE (a b : ℤ) (h : a ≤ b) :
    t.truncGEπ a ≫ t.natTransTruncGEOfLE a b h = t.truncGEπ b := by
  cat_disch

/-- The natural transformation `t.triangleLTGE a ⟶ t.triangleLTGE b`
when `a ≤ b`. -/
/-
**CategoryTheory.Triangulated.TStructure.natTransTriangleLTGEOfLE** 是 Mathlib 中的
一个定义，位于命名空间 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：natTransTriangleLTGEOfLE (a b : Int) (h : a <= b) : t.triangleLTGE a ⟶ t.t
riangleLTGE b
参数：a b : Int；h : a <= b。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Triangulated.TStructure.truncGEδLT_comp_whiskerRight_natT
ransTruncLTOfLE`：truncGEδLT_comp_whiskerRight_natTransTruncLTOfLE (a b : Int) (h
 : a <= b) : t.truncGEδLT a ≫ Functor.whiskerRight (natTransTruncLTOfLE t a b…

--- 原说明 ---
The natural transformation `t.triangleLTGE a ⟶ t.triangleLTGE b`
when `a ≤ b`.
-/
noncomputable def natTransTriangleLTGEOfLE (a b : ℤ) (h : a ≤ b) :
    t.triangleLTGE a ⟶ t.triangleLTGE b :=
  Triangle.functorHomMk' (t.natTransTruncLTOfLE a b h) (𝟙 _)
    ((t.natTransTruncGEOfLE a b h)) (by simp) (by simp)
    (t.truncGEδLT_comp_whiskerRight_natTransTruncLTOfLE a b h)

@[simp]
/-
**CategoryTheory.Triangulated.TStructure.natTransTriangleLTGEOfLE_refl** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：natTransTriangleLTGEOfLE_refl (a : Int) : t.natTransTriangleLTGEOfLE a a (
by rfl) = 𝟙 _
参数：a : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE.0.Cate
goryTheory.Triangulated.TStructure.TruncAux.triangleFunctorNatTransOfLE_refl`：∀ 
{C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.
Preadditive C]   [inst_2 : CategoryTheory.Limits.HasZeroOb…
-/
lemma natTransTriangleLTGEOfLE_refl (a : ℤ) :
    t.natTransTriangleLTGEOfLE a a (by rfl) = 𝟙 _ :=
  TruncAux.triangleFunctorNatTransOfLE_refl t a
/-
**CategoryTheory.Triangulated.TStructure.natTransTriangleLTGEOfLE_trans** 是 Math
lib 中的一个引理，位于命名空间 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：natTransTriangleLTGEOfLE_trans (a b c : Int) (hab : a <= b) (hbc : b <= c)
 : t.natTransTriangleLTGEOfLE a b hab ≫ t.natTransTriangleLTGEOfLE b c hbc = t.n
atTransTriangleLTGEOfLE a c (hab.trans hbc)
参数：a b c : Int；hab : a <= b；hbc : b <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE.0.Cate
goryTheory.Triangulated.TStructure.TruncAux.triangleFunctorNatTransOfLE_trans`：∀
 {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory
.Preadditive C]   [inst_2 : CategoryTheory.Limits.HasZeroOb…
-/
lemma natTransTriangleLTGEOfLE_trans (a b c : ℤ) (hab : a ≤ b) (hbc : b ≤ c) :
    t.natTransTriangleLTGEOfLE a b hab ≫ t.natTransTriangleLTGEOfLE b c hbc =
      t.natTransTriangleLTGEOfLE a c (hab.trans hbc) :=
  TruncAux.triangleFunctorNatTransOfLE_trans t a b c hab hbc

@[simp]
/-
**CategoryTheory.Triangulated.TStructure.natTransTruncLTOfLE_refl** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：natTransTruncLTOfLE_refl (a : Int) : t.natTransTruncLTOfLE a a (by rfl) = 
𝟙 _
参数：a : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `CategoryTheory.Triangulated.TStructure.natTransTriangleLTGEOfLE_refl`：na
tTransTriangleLTGEOfLE_refl (a : Int) : t.natTransTriangleLTGEOfLE a a (by rfl) 
= 𝟙 _
-/
lemma natTransTruncLTOfLE_refl (a : ℤ) :
    t.natTransTruncLTOfLE a a (by rfl) = 𝟙 _ :=
  congr_arg (fun x ↦ Functor.whiskerRight x (Triangle.π₁)) (t.natTransTriangleLTGEOfLE_refl a)

@[simp]
/-
**CategoryTheory.Triangulated.TStructure.natTransTruncLTOfLE_trans** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：natTransTruncLTOfLE_trans (a b c : Int) (hab : a <= b) (hbc : b <= c) : t.
natTransTruncLTOfLE a b hab ≫ t.natTransTruncLTOfLE b c hbc = t.natTransTruncLTO
fLE a c (hab.trans hbc)
参数：a b c : Int；hab : a <= b；hbc : b <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `CategoryTheory.Triangulated.TStructure.natTransTriangleLTGEOfLE_trans`：n
atTransTriangleLTGEOfLE_trans (a b c : Int) (hab : a <= b) (hbc : b <= c) : t.na
tTransTriangleLTGEOfLE a b hab ≫ t.natTransTriangleLTGEOfLE…
-/
lemma natTransTruncLTOfLE_trans (a b c : ℤ) (hab : a ≤ b) (hbc : b ≤ c) :
    t.natTransTruncLTOfLE a b hab ≫ t.natTransTruncLTOfLE b c hbc =
      t.natTransTruncLTOfLE a c (hab.trans hbc) :=
  congr_arg (fun x ↦ Functor.whiskerRight x Triangle.π₁)
    (t.natTransTriangleLTGEOfLE_trans a b c hab hbc)

@[simp]
/-
**CategoryTheory.Triangulated.TStructure.natTransTruncGEOfLE_refl** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：natTransTruncGEOfLE_refl (a : Int) : t.natTransTruncGEOfLE a a (by rfl) = 
𝟙 _
参数：a : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `CategoryTheory.Triangulated.TStructure.natTransTriangleLTGEOfLE_refl`：na
tTransTriangleLTGEOfLE_refl (a : Int) : t.natTransTriangleLTGEOfLE a a (by rfl) 
= 𝟙 _
-/
lemma natTransTruncGEOfLE_refl (a : ℤ) :
    t.natTransTruncGEOfLE a a (by rfl) = 𝟙 _ :=
  congr_arg (fun x ↦ Functor.whiskerRight x (Triangle.π₃)) (t.natTransTriangleLTGEOfLE_refl a)

@[simp]
/-
**CategoryTheory.Triangulated.TStructure.natTransTruncGEOfLE_trans** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：natTransTruncGEOfLE_trans (a b c : Int) (hab : a <= b) (hbc : b <= c) : t.
natTransTruncGEOfLE a b hab ≫ t.natTransTruncGEOfLE b c hbc = t.natTransTruncGEO
fLE a c (hab.trans hbc)
参数：a b c : Int；hab : a <= b；hbc : b <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `CategoryTheory.Triangulated.TStructure.natTransTriangleLTGEOfLE_trans`：n
atTransTriangleLTGEOfLE_trans (a b c : Int) (hab : a <= b) (hbc : b <= c) : t.na
tTransTriangleLTGEOfLE a b hab ≫ t.natTransTriangleLTGEOfLE…
-/
lemma natTransTruncGEOfLE_trans (a b c : ℤ) (hab : a ≤ b) (hbc : b ≤ c) :
    t.natTransTruncGEOfLE a b hab ≫ t.natTransTruncGEOfLE b c hbc =
      t.natTransTruncGEOfLE a c (hab.trans hbc) :=
  congr_arg (fun x ↦ Functor.whiskerRight x Triangle.π₃)
    (t.natTransTriangleLTGEOfLE_trans a b c hab hbc)
/-
**CategoryTheory.Triangulated.TStructure.natTransTruncLTOfLE_refl_app** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：natTransTruncLTOfLE_refl_app (a : Int) (X : C) : (t.natTransTruncLTOfLE a 
a (by rfl)).app X = 𝟙 _
参数：a : Int；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.congr_app`：congr_app {F G : C ⥤ D} {α β : NatTrans F G} (
h : α = β) (X : C) : α.app X = β.app X
· 使用引理 `CategoryTheory.Triangulated.TStructure.natTransTruncLTOfLE_refl`：natTran
sTruncLTOfLE_refl (a : Int) : t.natTransTruncLTOfLE a a (by rfl) = 𝟙 _
-/
lemma natTransTruncLTOfLE_refl_app (a : ℤ) (X : C) :
    (t.natTransTruncLTOfLE a a (by rfl)).app X = 𝟙 _ :=
  congr_app (t.natTransTruncLTOfLE_refl a) X
/-
**CategoryTheory.Triangulated.TStructure.natTransTruncLTOfLE_trans_app** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：natTransTruncLTOfLE_trans_app (a b c : Int) (hab : a <= b) (hbc : b <= c) 
(X : C) : (t.natTransTruncLTOfLE a b hab).app X ≫ (t.natTransTruncLTOfLE b c hbc
).app X = (t.natTransTruncLTOfLE a c (hab.trans hbc)).app X
参数：a b c : Int；hab : a <= b；hbc : b <= c；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.congr_app`：congr_app {F G : C ⥤ D} {α β : NatTrans F G} (
h : α = β) (X : C) : α.app X = β.app X
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `CategoryTheory.Triangulated.TStructure.natTransTruncLTOfLE_trans`：natTra
nsTruncLTOfLE_trans (a b c : Int) (hab : a <= b) (hbc : b <= c) : t.natTransTrun
cLTOfLE a b hab ≫ t.natTransTruncLTOfLE b c hbc = t.na…
-/
lemma natTransTruncLTOfLE_trans_app (a b c : ℤ) (hab : a ≤ b) (hbc : b ≤ c) (X : C) :
    (t.natTransTruncLTOfLE a b hab).app X ≫ (t.natTransTruncLTOfLE b c hbc).app X =
      (t.natTransTruncLTOfLE a c (hab.trans hbc)).app X :=
  congr_app (t.natTransTruncLTOfLE_trans a b c hab hbc) X
/-
**CategoryTheory.Triangulated.TStructure.natTransTruncGEOfLE_refl_app** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：natTransTruncGEOfLE_refl_app (a : Int) (X : C) : (t.natTransTruncGEOfLE a 
a (by rfl)).app X = 𝟙 _
参数：a : Int；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.congr_app`：congr_app {F G : C ⥤ D} {α β : NatTrans F G} (
h : α = β) (X : C) : α.app X = β.app X
· 使用引理 `CategoryTheory.Triangulated.TStructure.natTransTruncGEOfLE_refl`：natTran
sTruncGEOfLE_refl (a : Int) : t.natTransTruncGEOfLE a a (by rfl) = 𝟙 _
-/
lemma natTransTruncGEOfLE_refl_app (a : ℤ) (X : C) :
    (t.natTransTruncGEOfLE a a (by rfl)).app X = 𝟙 _ :=
  congr_app (t.natTransTruncGEOfLE_refl a) X
/-
**CategoryTheory.Triangulated.TStructure.natTransTruncGEOfLE_trans_app** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：natTransTruncGEOfLE_trans_app (a b c : Int) (hab : a <= b) (hbc : b <= c) 
(X : C) : (t.natTransTruncGEOfLE a b hab).app X ≫ (t.natTransTruncGEOfLE b c hbc
).app X = (t.natTransTruncGEOfLE a c (hab.trans hbc)).app X
参数：a b c : Int；hab : a <= b；hbc : b <= c；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.congr_app`：congr_app {F G : C ⥤ D} {α β : NatTrans F G} (
h : α = β) (X : C) : α.app X = β.app X
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `CategoryTheory.Triangulated.TStructure.natTransTruncGEOfLE_trans`：natTra
nsTruncGEOfLE_trans (a b c : Int) (hab : a <= b) (hbc : b <= c) : t.natTransTrun
cGEOfLE a b hab ≫ t.natTransTruncGEOfLE b c hbc = t.na…
-/
lemma natTransTruncGEOfLE_trans_app (a b c : ℤ) (hab : a ≤ b) (hbc : b ≤ c) (X : C) :
    (t.natTransTruncGEOfLE a b hab).app X ≫ (t.natTransTruncGEOfLE b c hbc).app X =
      (t.natTransTruncGEOfLE a c (hab.trans hbc)).app X :=
  congr_app (t.natTransTruncGEOfLE_trans a b c hab hbc) X
/-
**CategoryTheory.Triangulated.TStructure.isLE_of_isZero** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：isLE_of_isZero {X : C} (hX : IsZero X) (n : Int) : t.IsLE X n
参数：hX : IsZero X；n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Triangulated.TStructure.isLE_of_iso`：isLE_of_iso {X Y : C
} (e : X ≅ Y) (n : Int) [t.IsLE X n] : t.IsLE Y n where le
· 使用引理 `CategoryTheory.Functor.map_isZero`：map_isZero (F : C ⥤ D) [PreservesZero
Morphisms F] {X : C} (hX : IsZero X) : IsZero (F.obj X)
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Triangulated.TStructure.instAdditiveTruncLT`：∀ {C : Type 
u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditiv
e C]   [inst_2 : CategoryTheory.Limits.HasZeroOb…
· 使用定理 `CategoryTheory.Triangulated.TStructure.instIsLEObjTruncLTHAddIntOfNat`：∀
 {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory
.Preadditive C]   [inst_2 : CategoryTheory.Limits.HasZeroOb…
-/
lemma isLE_of_isZero {X : C} (hX : IsZero X) (n : ℤ) : t.IsLE X n :=
  t.isLE_of_iso (((t.truncLT (n + 1)).map_isZero hX).isoZero ≪≫ hX.isoZero.symm) n
/-
**CategoryTheory.Triangulated.TStructure.isGE_of_isZero** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：isGE_of_isZero {X : C} (hX : IsZero X) (n : Int) : t.IsGE X n
参数：hX : IsZero X；n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Triangulated.TStructure.isGE_of_iso`：isGE_of_iso {X Y : C
} (e : X ≅ Y) (n : Int) [t.IsGE X n] : t.IsGE Y n where ge
· 使用引理 `CategoryTheory.Functor.map_isZero`：map_isZero (F : C ⥤ D) [PreservesZero
Morphisms F] {X : C} (hX : IsZero X) : IsZero (F.obj X)
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Triangulated.TStructure.instAdditiveTruncGE`：∀ {C : Type 
u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditiv
e C]   [inst_2 : CategoryTheory.Limits.HasZeroOb…
· 使用定理 `CategoryTheory.Triangulated.TStructure.instIsGEObjTruncGE`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive
 C]   [inst_2 : CategoryTheory.Limits.HasZeroOb…
-/
lemma isGE_of_isZero {X : C} (hX : IsZero X) (n : ℤ) : t.IsGE X n :=
  t.isGE_of_iso (((t.truncGE n).map_isZero hX).isoZero ≪≫ hX.isoZero.symm) n
/-
**CategoryTheory.Triangulated.TStructure.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : ℤ) : t.IsLE (0 : C) n := t.isLE_of_isZero (isZero_zero C) n
/-
**CategoryTheory.Triangulated.TStructure.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : ℤ) : t.IsGE (0 : C) n := t.isGE_of_isZero (isZero_zero C) n

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Triangulated.TStructure.isLE_iff_isIso_truncLT** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isLE_iff_isIso_truncLTι_app (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (X : C) :
    t.IsLE X n₀ ↔ IsIso (((t.truncLTι n₁)).app X) := by
  subst h
  refine ⟨fun _ ↦ ?_,
    fun _ ↦ t.isLE_of_iso (asIso (((t.truncLTι (n₀ + 1))).app X)) n₀⟩
  obtain ⟨e, he⟩ := t.triangle_iso_exists
    (contractible_distinguished X) (t.triangleLTGE_distinguished (n₀ + 1) X)
    (Iso.refl X) n₀ (n₀ + 1)
    (by dsimp; infer_instance) (by dsimp; infer_instance)
    (by dsimp; infer_instance) (by dsimp; infer_instance)
  have he' : e.inv.hom₂ = 𝟙 X := by
    rw [← cancel_mono e.hom.hom₂, ← comp_hom₂, e.inv_hom_id, he]
    simp
  have : (t.truncLTι (n₀ + 1)).app X = e.inv.hom₁ := by
    simpa [he'] using e.inv.comm₁
  rw [this]
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Triangulated.TStructure.isGE_iff_isIso_truncGE** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isGE_iff_isIso_truncGEπ_app (n : ℤ) (X : C) :
    t.IsGE X n ↔ IsIso ((t.truncGEπ n).app X) := by
  constructor
  · intro h
    obtain ⟨e, he⟩ := t.triangle_iso_exists
      (inv_rot_of_distTriang _ (contractible_distinguished X))
      (t.triangleLTGE_distinguished n X) (Iso.refl X) (n - 1) n
      (t.isLE_of_iso (shiftFunctor C (-1 : ℤ)).mapZeroObject.symm _)
      (by dsimp; infer_instance) (by dsimp; infer_instance) (by dsimp; infer_instance)
    dsimp at he
    have : (truncGEπ t n).app X = e.hom.hom₃ := by
      have := e.hom.comm₂
      dsimp at this
      rw [← cancel_epi e.hom.hom₂, ← this, he]
    rw [this]
    infer_instance
  · intro
    exact t.isGE_of_iso (asIso ((truncGEπ t n).app X)).symm n
/-
**CategoryTheory.Triangulated.TStructure.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : C) (n : ℤ) [t.IsGE X n] : IsIso ((t.truncGEπ n).app X) := by
  rw [← isGE_iff_isIso_truncGEπ_app]
  infer_instance
/-
**CategoryTheory.Triangulated.TStructure.isGE_iff_isZero_truncLT_obj** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：isGE_iff_isZero_truncLT_obj (n : Int) (X : C) : t.IsGE X n ↔ IsZero ((t.tr
uncLT n).obj X)
参数：n : Int；X : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Triangulated.TStructure.isGE_iff_isIso_truncGEπ_app`：isGE
_iff_isIso_truncGEπ_app (n : Int) (X : C) : t.IsGE X n ↔ IsIso ((t.truncGEπ n).a
pp X)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `CategoryTheory.Pretriangulated.Triangle.isZero₁_iff_isIso₂`：isZero₁_iff_
isIso₂ : IsZero T.obj₁ ↔ IsIso T.mor₂
· 使用引理 `CategoryTheory.Triangulated.TStructure.triangleLTGE_distinguished`：trian
gleLTGE_distinguished (n : Int) (X : C) : (t.triangleLTGE n).obj X in distTriang
 C
-/
lemma isGE_iff_isZero_truncLT_obj (n : ℤ) (X : C) :
    t.IsGE X n ↔ IsZero ((t.truncLT n).obj X) := by
  rw [t.isGE_iff_isIso_truncGEπ_app n X]
  exact (Triangle.isZero₁_iff_isIso₂ _ (t.triangleLTGE_distinguished n X)).symm
/-
**CategoryTheory.Triangulated.TStructure.isLE_iff_isZero_truncGE_obj** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：isLE_iff_isZero_truncGE_obj (n₀ n₁ : Int) (h : n₀ + 1 = n₁) (X : C) : t.Is
LE X n₀ ↔ IsZero ((t.truncGE n₁).obj X)
参数：n₀ n₁ : Int；h : n₀ + 1 = n₁；X : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Triangulated.TStructure.isLE_iff_isIso_truncLTι_app`：isLE
_iff_isIso_truncLTι_app (n₀ n₁ : Int) (h : n₀ + 1 = n₁) (X : C) : t.IsLE X n₀ ↔ 
IsIso (((t.truncLTι n₁)).app X)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `CategoryTheory.Pretriangulated.Triangle.isZero₃_iff_isIso₁`：isZero₃_iff_
isIso₁ : IsZero T.obj₃ ↔ IsIso T.mor₁
· 使用引理 `CategoryTheory.Triangulated.TStructure.triangleLTGE_distinguished`：trian
gleLTGE_distinguished (n : Int) (X : C) : (t.triangleLTGE n).obj X in distTriang
 C
-/
lemma isLE_iff_isZero_truncGE_obj (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (X : C) :
    t.IsLE X n₀ ↔ IsZero ((t.truncGE n₁).obj X) := by
  rw [t.isLE_iff_isIso_truncLTι_app n₀ n₁ h X]
  exact (Triangle.isZero₃_iff_isIso₁ _ (t.triangleLTGE_distinguished n₁ X)).symm
/-
**CategoryTheory.Triangulated.TStructure.isZero_truncLT_obj_of_isGE** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：isZero_truncLT_obj_of_isGE (n : Int) (X : C) [t.IsGE X n] : IsZero ((t.tru
ncLT n).obj X)
参数：n : Int；X : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Triangulated.TStructure.isGE_iff_isZero_truncLT_obj`：isGE
_iff_isZero_truncLT_obj (n : Int) (X : C) : t.IsGE X n ↔ IsZero ((t.truncLT n).o
bj X)
-/
lemma isZero_truncLT_obj_of_isGE (n : ℤ) (X : C) [t.IsGE X n] :
    IsZero ((t.truncLT n).obj X) := by
  rw [← isGE_iff_isZero_truncLT_obj]
  infer_instance
/-
**CategoryTheory.Triangulated.TStructure.isZero_truncGE_obj_of_isLE** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：isZero_truncGE_obj_of_isLE (n₀ n₁ : Int) (h : n₀ + 1 = n₁) (X : C) [t.IsLE
 X n₀] : IsZero ((t.truncGE n₁).obj X)
参数：n₀ n₁ : Int；h : n₀ + 1 = n₁；X : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Triangulated.TStructure.isLE_iff_isZero_truncGE_obj`：isLE
_iff_isZero_truncGE_obj (n₀ n₁ : Int) (h : n₀ + 1 = n₁) (X : C) : t.IsLE X n₀ ↔ 
IsZero ((t.truncGE n₁).obj X)
-/
lemma isZero_truncGE_obj_of_isLE (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (X : C) [t.IsLE X n₀] :
    IsZero ((t.truncGE n₁).obj X) := by
  rw [← t.isLE_iff_isZero_truncGE_obj _ _ h X]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Triangulated.TStructure.from_truncGE_obj_ext** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：from_truncGE_obj_ext {n : Int} {X : C} {Y : C} {f₁ f₂ : (t.truncGE n).obj 
X ⟶ Y} (h : (t.truncGEπ n).app X ≫ f₁ = (t.truncGEπ n).app X ≫ f₂) [t.IsGE Y n] 
: f₁ = f₂
参数：t.truncGE n；h : (t.truncGEπ n).app X ≫ f₁ = (t.truncGEπ n).app X ≫ f₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Pretriangulated.Triangle.yoneda_exact₃`：yoneda_exact₃ {X 
: C} (f : T.obj₃ ⟶ X) (hf : T.mor₂ ≫ f = 0) : exists (g : T.obj₁⟦(1 : Int)⟧ ⟶ X)
, f = T.mor₃ ≫ g
· 使用引理 `CategoryTheory.Triangulated.TStructure.triangleLTGE_distinguished`：trian
gleLTGE_distinguished (n : Int) (X : C) : (t.triangleLTGE n).obj X in distTriang
 C
· 使用引理 `CategoryTheory.Triangulated.TStructure.zero_of_isLE_of_isGE`：zero_of_isL
E_of_isGE {X Y : C} (f : X ⟶ Y) (n₀ n₁ : Int) (h : n₀ < n₁) (_ : t.IsLE X n₀) (_
 : t.IsGE Y n₁) : f = 0
· 使用引理 `CategoryTheory.Triangulated.TStructure.isLE_shift`：isLE_shift (X : C) (n
 a n' : Int) (hn' : a + n' = n
· 使用定理 `CategoryTheory.Triangulated.TStructure.instIsLEObj₁ObjTriangleTriangleLT
GEHSubIntOfNat`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1
 : CategoryTheory.Preadditive C]   [inst_2 : CategoryTheory.Limits.HasZeroOb…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Preadditive.comp_sub`：comp_sub : f ≫ (g - g') = f ≫ g - f
 ≫ g'
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma from_truncGE_obj_ext {n : ℤ} {X : C} {Y : C}
    {f₁ f₂ : (t.truncGE n).obj X ⟶ Y} (h : (t.truncGEπ n).app X ≫ f₁ = (t.truncGEπ n).app X ≫ f₂)
    [t.IsGE Y n] :
    f₁ = f₂ := by
  suffices ∀ (f : (t.truncGE n).obj X ⟶ Y), (t.truncGEπ n).app X ≫ f = 0 → f = 0 by
    rw [← sub_eq_zero, this (f₁ - f₂) (by cat_disch)]
  intro f hf
  obtain ⟨g, hg⟩ := Triangle.yoneda_exact₃ _
    (t.triangleLTGE_distinguished n X) f hf
  have hg' := t.zero_of_isLE_of_isGE g (n-2) n (by lia)
    (by exact t.isLE_shift _ (n-1) 1 (n-2) (by lia)) inferInstance
  rw [hg, hg', comp_zero]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Triangulated.TStructure.to_truncLT_obj_ext** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：to_truncLT_obj_ext {n : Int} {Y : C} {X : C} {f₁ f₂ : Y ⟶ (t.truncLT n).ob
j X} (h : f₁ ≫ (t.truncLTι n).app X = f₂ ≫ (t.truncLTι n).app X) [t.IsLE Y (n - 
1)] : f₁ = f₂
参数：t.truncLT n；h : f₁ ≫ (t.truncLTι n).app X = f₂ ≫ (t.truncLTι n).app X；n - 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Pretriangulated.Triangle.coyoneda_exact₂`：coyoneda_exact₂
 {X : C} (f : X ⟶ T.obj₂) (hf : f ≫ T.mor₂ = 0) : exists (g : X ⟶ T.obj₁), f = g
 ≫ T.mor₁
· 使用定理 `CategoryTheory.Pretriangulated.inv_rot_of_distTriang`：inv_rot_of_distTri
ang (T : Triangle C) (H : T in distTriang C) : T.invRotate in distTriang C
· 使用引理 `CategoryTheory.Triangulated.TStructure.triangleLTGE_distinguished`：trian
gleLTGE_distinguished (n : Int) (X : C) : (t.triangleLTGE n).obj X in distTriang
 C
· 使用引理 `CategoryTheory.Triangulated.TStructure.zero_of_isLE_of_isGE`：zero_of_isL
E_of_isGE {X Y : C} (f : X ⟶ Y) (n₀ n₁ : Int) (h : n₀ < n₁) (_ : t.IsLE X n₀) (_
 : t.IsGE Y n₁) : f = 0
· 使用引理 `CategoryTheory.Triangulated.TStructure.isGE_shift`：isGE_shift (X : C) (n
 a n' : Int) (hn' : a + n' = n
· 使用定理 `CategoryTheory.Triangulated.TStructure.instIsGEObjTruncGE`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive
 C]   [inst_2 : CategoryTheory.Limits.HasZeroOb…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Preadditive.sub_comp`：sub_comp : (f - f') ≫ g = f ≫ g - f
' ≫ g
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma to_truncLT_obj_ext {n : ℤ} {Y : C} {X : C}
    {f₁ f₂ : Y ⟶ (t.truncLT n).obj X}
    (h : f₁ ≫ (t.truncLTι n).app X = f₂ ≫ (t.truncLTι n).app X)
    [t.IsLE Y (n - 1)] :
    f₁ = f₂ := by
  suffices ∀ (f : Y ⟶ (t.truncLT n).obj X) (_ : f ≫ (t.truncLTι n).app X = 0), f = 0 by
    rw [← sub_eq_zero, this (f₁ - f₂) (by cat_disch)]
  intro f hf
  obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₂ _ (inv_rot_of_distTriang _
    (t.triangleLTGE_distinguished n X)) f hf
  have hg' := t.zero_of_isLE_of_isGE g (n - 1) (n + 1) (by lia) inferInstance
    (by dsimp; apply (t.isGE_shift _ n (-1) (n + 1) (by lia)))
  rw [hg, hg', zero_comp]

@[reassoc]
/-
**CategoryTheory.Triangulated.TStructure.truncLT_map_truncLT** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma truncLT_map_truncLTι_app (n : ℤ) (X : C) :
    (t.truncLT n).map ((t.truncLTι n).app X) = (t.truncLTι n).app ((t.truncLT n).obj X) :=
  t.to_truncLT_obj_ext (by simp)

@[reassoc]
/-
**CategoryTheory.Triangulated.TStructure.truncGE_map_truncGE** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma truncGE_map_truncGEπ_app (n : ℤ) (X : C) :
    (t.truncGE n).map ((t.truncGEπ n).app X) = (t.truncGEπ n).app ((t.truncGE n).obj X) :=
  t.from_truncGE_obj_ext (by simp)

section

variable {X Y : C} (f : X ⟶ Y) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) [t.IsLE X n₀]

set_option backward.defeqAttrib.useBackward true in
include h in
/-
**CategoryTheory.Triangulated.TStructure.liftTruncLT_aux** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：liftTruncLT_aux : exists (f' : X ⟶ (t.truncLT n₁).obj Y), f = f' ≫ (t.trun
cLTι n₁).app Y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Pretriangulated.Triangle.coyoneda_exact₂`：coyoneda_exact₂
 {X : C} (f : X ⟶ T.obj₂) (hf : f ≫ T.mor₂ = 0) : exists (g : X ⟶ T.obj₁), f = g
 ≫ T.mor₁
· 使用引理 `CategoryTheory.Triangulated.TStructure.triangleLTGE_distinguished`：trian
gleLTGE_distinguished (n : Int) (X : C) : (t.triangleLTGE n).obj X in distTriang
 C
· 使用引理 `CategoryTheory.Triangulated.TStructure.zero_of_isLE_of_isGE`：zero_of_isL
E_of_isGE {X Y : C} (f : X ⟶ Y) (n₀ n₁ : Int) (h : n₀ < n₁) (_ : t.IsLE X n₀) (_
 : t.IsGE Y n₁) : f = 0
· 使用定理 `CategoryTheory.Triangulated.TStructure.instIsGEObjTruncGE`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive
 C]   [inst_2 : CategoryTheory.Limits.HasZeroOb…
-/
lemma liftTruncLT_aux :
    ∃ (f' : X ⟶ (t.truncLT n₁).obj Y), f = f' ≫ (t.truncLTι n₁).app Y :=
  Triangle.coyoneda_exact₂ _ (t.triangleLTGE_distinguished n₁ Y) f
    (t.zero_of_isLE_of_isGE _ n₀ n₁ (by lia) inferInstance (by dsimp; infer_instance))

/-- Constructor for morphisms to `(t.truncLT n₁).obj Y`. -/
/-
**CategoryTheory.Triangulated.TStructure.liftTruncLT** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Triangulated.TStructure`。
形式化陈述：liftTruncLT {X Y : C} (f : X ⟶ Y) (n₀ n₁ : Int) (h : n₀ + 1 = n₁) [t.IsLE 
X n₀] : X ⟶ (t.truncLT n₁).obj Y
参数：f : X ⟶ Y；n₀ n₁ : Int；h : n₀ + 1 = n₁。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Triangulated.TStructure.liftTruncLT_aux`：liftTruncLT_aux 
: exists (f' : X ⟶ (t.truncLT n₁).obj Y), f = f' ≫ (t.truncLTι n₁).app Y

--- 原说明 ---
Constructor for morphisms to `(t.truncLT n₁).obj Y`.
-/
noncomputable def liftTruncLT {X Y : C} (f : X ⟶ Y) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) [t.IsLE X n₀] :
    X ⟶ (t.truncLT n₁).obj Y :=
  (t.liftTruncLT_aux f n₀ n₁ h).choose

@[reassoc (attr := simp)]
/-
**CategoryTheory.Triangulated.TStructure.liftTruncLT_** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma liftTruncLT_ι {X Y : C} (f : X ⟶ Y) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) [t.IsLE X n₀] :
    t.liftTruncLT f n₀ n₁ h ≫ (t.truncLTι n₁).app Y = f :=
  (t.liftTruncLT_aux f n₀ n₁ h).choose_spec.symm

end

section

variable {X Y : C} (f : X ⟶ Y) (n : ℤ) [t.IsGE Y n]

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Triangulated.TStructure.descTruncGE_aux** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：descTruncGE_aux : exists (f' : (t.truncGE n).obj X ⟶ Y), f = (t.truncGEπ n
).app X ≫ f'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Pretriangulated.Triangle.yoneda_exact₂`：yoneda_exact₂ {X 
: C} (f : T.obj₂ ⟶ X) (hf : T.mor₁ ≫ f = 0) : exists (g : T.obj₃ ⟶ X), f = T.mor
₂ ≫ g
· 使用引理 `CategoryTheory.Triangulated.TStructure.triangleLTGE_distinguished`：trian
gleLTGE_distinguished (n : Int) (X : C) : (t.triangleLTGE n).obj X in distTriang
 C
· 使用引理 `CategoryTheory.Triangulated.TStructure.zero_of_isLE_of_isGE`：zero_of_isL
E_of_isGE {X Y : C} (f : X ⟶ Y) (n₀ n₁ : Int) (h : n₀ < n₁) (_ : t.IsLE X n₀) (_
 : t.IsGE Y n₁) : f = 0
· 使用定理 `CategoryTheory.Triangulated.TStructure.instIsLEObjTruncLTHSubIntOfNat`：∀
 {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory
.Preadditive C]   [inst_2 : CategoryTheory.Limits.HasZeroOb…
-/
lemma descTruncGE_aux :
  ∃ (f' : (t.truncGE n).obj X ⟶ Y), f = (t.truncGEπ n).app X ≫ f' :=
  Triangle.yoneda_exact₂ _ (t.triangleLTGE_distinguished n X) f
    (t.zero_of_isLE_of_isGE _ (n-1) n (by lia) (by dsimp; infer_instance) inferInstance)

/-- Constructor for morphisms from `(t.truncGE n).obj X`. -/
/-
**CategoryTheory.Triangulated.TStructure.descTruncGE** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Triangulated.TStructure`。
形式化陈述：descTruncGE : (t.truncGE n).obj X ⟶ Y
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Triangulated.TStructure.descTruncGE_aux`：descTruncGE_aux 
: exists (f' : (t.truncGE n).obj X ⟶ Y), f = (t.truncGEπ n).app X ≫ f'

--- 原说明 ---
Constructor for morphisms from `(t.truncGE n).obj X`.
-/
noncomputable def descTruncGE :
    (t.truncGE n).obj X ⟶ Y :=
  (t.descTruncGE_aux f n).choose

@[reassoc (attr := simp)]
/-
**CategoryTheory.Triangulated.TStructure.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma π_descTruncGE {X Y : C} (f : X ⟶ Y) (n : ℤ) [t.IsGE Y n] :
    (t.truncGEπ n).app X ≫ t.descTruncGE f n = f :=
  (t.descTruncGE_aux f n).choose_spec.symm

end

/-
**CategoryTheory.Triangulated.TStructure.isLE_iff_orthogonal** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：isLE_iff_orthogonal (n₀ n₁ : Int) (h : n₀ + 1 = n₁) (X : C) : t.IsLE X n₀ 
↔ forall (Y : C) (f : X ⟶ Y) (_ : t.IsGE Y n₁), f = 0
参数：n₀ n₁ : Int；h : n₀ + 1 = n₁；X : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Triangulated.TStructure.zero`：zero {X Y : C} (f : X ⟶ Y) 
(n₀ n₁ : Int) (h : n₀ < n₁
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Triangulated.TStructure.isLE_iff_isZero_truncGE_obj`：isLE
_iff_isZero_truncGE_obj (n₀ n₁ : Int) (h : n₀ + 1 = n₁) (X : C) : t.IsLE X n₀ ↔ 
IsZero ((t.truncGE n₁).obj X)
· 使用定理 `CategoryTheory.Limits.IsZero.iff_id_eq_zero`：iff_id_eq_zero (X : C) : Is
Zero X ↔ 𝟙 X = 0
· 使用引理 `CategoryTheory.Triangulated.TStructure.from_truncGE_obj_ext`：from_truncG
E_obj_ext {n : Int} {X : C} {Y : C} {f₁ f₂ : (t.truncGE n).obj X ⟶ Y} (h : (t.tr
uncGEπ n).app X ≫ f₁ = (t.truncGEπ n).app X ≫ f₂)…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Triangulated.TStructure.instIsGEObjTruncGE`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive
 C]   [inst_2 : CategoryTheory.Limits.HasZeroOb…
-/
lemma isLE_iff_orthogonal (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (X : C) :
    t.IsLE X n₀ ↔ ∀ (Y : C) (f : X ⟶ Y) (_ : t.IsGE Y n₁), f = 0 := by
  refine ⟨fun _ Y f _ ↦ t.zero f n₀ n₁ (by lia), fun hX ↦ ?_⟩
  rw [t.isLE_iff_isZero_truncGE_obj n₀ n₁ h, IsZero.iff_id_eq_zero]
  exact t.from_truncGE_obj_ext (by simpa using hX _ _ inferInstance)
/-
**CategoryTheory.Triangulated.TStructure.isGE_iff_orthogonal** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：isGE_iff_orthogonal (n₀ n₁ : Int) (h : n₀ + 1 = n₁) (X : C) : t.IsGE X n₁ 
↔ forall (Y : C) (f : Y ⟶ X) (_ : t.IsLE Y n₀), f = 0
参数：n₀ n₁ : Int；h : n₀ + 1 = n₁；X : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Triangulated.TStructure.zero`：zero {X Y : C} (f : X ⟶ Y) 
(n₀ n₁ : Int) (h : n₀ < n₁
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Triangulated.TStructure.isGE_iff_isZero_truncLT_obj`：isGE
_iff_isZero_truncLT_obj (n : Int) (X : C) : t.IsGE X n ↔ IsZero ((t.truncLT n).o
bj X)
· 使用定理 `CategoryTheory.Limits.IsZero.iff_id_eq_zero`：iff_id_eq_zero (X : C) : Is
Zero X ↔ 𝟙 X = 0
· 使用引理 `CategoryTheory.Triangulated.TStructure.to_truncLT_obj_ext`：to_truncLT_ob
j_ext {n : Int} {Y : C} {X : C} {f₁ f₂ : Y ⟶ (t.truncLT n).obj X} (h : f₁ ≫ (t.t
runcLTι n).app X = f₂ ≫ (t.truncLTι n).app X) […
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Triangulated.TStructure.instIsLEObjTruncLTHAddIntOfNat`：∀
 {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory
.Preadditive C]   [inst_2 : CategoryTheory.Limits.HasZeroOb…
· 使用定理 `CategoryTheory.Triangulated.TStructure.instIsLEObjTruncLTHSubIntOfNat`：∀
 {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory
.Preadditive C]   [inst_2 : CategoryTheory.Limits.HasZeroOb…
-/
lemma isGE_iff_orthogonal (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (X : C) :
    t.IsGE X n₁ ↔ ∀ (Y : C) (f : Y ⟶ X) (_ : t.IsLE Y n₀), f = 0 := by
  refine ⟨fun _ Y f _ ↦ t.zero f n₀ n₁ (by lia), fun hX ↦ ?_⟩
  rw [t.isGE_iff_isZero_truncLT_obj n₁ X, IsZero.iff_id_eq_zero]
  exact t.to_truncLT_obj_ext (by simpa using hX _ _ (by rw [← h]; infer_instance))
/-
**CategoryTheory.Triangulated.TStructure.isLE** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isLE₂ (T : Triangle C) (hT : T ∈ distTriang C) (n : ℤ) (h₁ : t.IsLE T.obj₁ n)
    (h₃ : t.IsLE T.obj₃ n) : t.IsLE T.obj₂ n := by
  rw [t.isLE_iff_orthogonal n (n + 1) rfl]
  intro Y f hY
  obtain ⟨f', hf'⟩ := Triangle.yoneda_exact₂ _ hT f
    (t.zero _ n (n + 1) (by lia))
  rw [hf', t.zero f' n (n + 1) (by lia), comp_zero]
/-
**CategoryTheory.Triangulated.TStructure.isGE** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isGE₂ (T : Triangle C) (hT : T ∈ distTriang C) (n : ℤ) (h₁ : t.IsGE T.obj₁ n)
    (h₃ : t.IsGE T.obj₃ n) : t.IsGE T.obj₂ n := by
  rw [t.isGE_iff_orthogonal (n-1) n (by lia)]
  intro Y f hY
  obtain ⟨f', hf'⟩ := Triangle.coyoneda_exact₂ _ hT f (t.zero _ (n-1) n (by lia))
  rw [hf', t.zero f' (n-1) n (by lia), zero_comp]
/-
**CategoryTheory.Triangulated.TStructure.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : t.minus.IsTriangulated where
  exists_zero := ⟨0, isZero_zero C, 0, inferInstance⟩
  toIsTriangulatedClosed₂ := .mk' (fun T hT ↦ by
    rintro ⟨i₁, hi₁⟩ ⟨i₃, hi₃⟩
    exact ⟨max i₁ i₃, t.isLE₂ T hT _ (t.isLE_of_le _ _ _ (le_max_left i₁ i₃))
      (t.isLE_of_le _ _ _ (le_max_right i₁ i₃))⟩)
/-
**CategoryTheory.Triangulated.TStructure.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : t.plus.IsTriangulated where
  exists_zero := ⟨0, isZero_zero C, 0, inferInstance⟩
  toIsTriangulatedClosed₂ := .mk' (fun T hT ↦ by
    rintro ⟨i₁, hi₁⟩ ⟨i₃, hi₃⟩
    exact ⟨min i₁ i₃, t.isGE₂ T hT _ (t.isGE_of_ge _ _ _ (min_le_left i₁ i₃))
      (t.isGE_of_ge _ _ _ (min_le_right i₁ i₃))⟩)
/-
**CategoryTheory.Triangulated.TStructure.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : t.bounded.IsTriangulated := by
  dsimp [bounded]
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Triangulated.TStructure.isIso_truncLT_map_iff** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：isIso_truncLT_map_iff {X Y : C} (f : X ⟶ Y) (n : Int) : IsIso ((t.truncLT 
n).map f) ↔ exists (Z : C) (g : Y ⟶ Z) (h : Z ⟶ ((t.truncLT n).obj X)⟦1⟧) (_ : T
riangle.mk ((t.truncLTι n).app X ≫ f) g h in distTriang _), t.IsGE Z n
参数：f : X ⟶ Y；n : Int。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Pretriangulated.isomorphic_distinguished`：∀ {C : Type u} 
{inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZer
oObject C}   {inst_2 : CategoryTheory.HasShif…
· 使用引理 `CategoryTheory.Triangulated.TStructure.triangleLTGE_distinguished`：trian
gleLTGE_distinguished (n : Int) (X : C) : (t.triangleLTGE n).obj X in distTriang
 C
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_inv`：map_inv (F : C ⥤ D) {X Y : C} (f : X ⟶ Y
) [IsIso f] : F.map (inv f) = inv (F.map f)
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
· 使用定理 `CategoryTheory.Triangulated.TStructure.instIsGEObjTruncGE`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive
 C]   [inst_2 : CategoryTheory.Limits.HasZeroOb…
· 使用定理 `CategoryTheory.Triangulated.TStructure.triangle_iso_exists`：∀ {C : Type 
u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditiv
e C]   [inst_2 : CategoryTheory.Limits.HasZeroOb…
· 使用定理 `CategoryTheory.Triangulated.TStructure.instIsLEObjTruncLTHSubIntOfNat`：∀
 {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory
.Preadditive C]   [inst_2 : CategoryTheory.Limits.HasZeroOb…
· 使用引理 `CategoryTheory.Triangulated.TStructure.to_truncLT_obj_ext`：to_truncLT_ob
j_ext {n : Int} {Y : C} {X : C} {f₁ f₂ : Y ⟶ (t.truncLT n).obj X} (h : f₁ ≫ (t.t
runcLTι n).app X = f₂ ≫ (t.truncLTι n).app X) […
· 使用定理 `CategoryTheory.Pretriangulated.TriangleMorphism.comm₁`：∀ {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.HasShift C ℤ]  
 {T₁ T₂ : CategoryTheory.Pretriangulated.Tr…
· 使用定理 `CategoryTheory.Pretriangulated.Triangle.instIsIsoHom₁`：∀ {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.HasShift C ℤ]  
 {A B : CategoryTheory.Pretriangulated.Tria…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
lemma isIso_truncLT_map_iff {X Y : C} (f : X ⟶ Y) (n : ℤ) :
    IsIso ((t.truncLT n).map f) ↔
      ∃ (Z : C) (g : Y ⟶ Z) (h : Z ⟶ ((t.truncLT n).obj X)⟦1⟧)
        (_ : Triangle.mk ((t.truncLTι n).app X ≫ f) g h ∈ distTriang _), t.IsGE Z n := by
  refine ⟨fun hf ↦ ?_, fun ⟨Z, g, h, mem, _⟩ ↦ ?_⟩
  · refine ⟨(t.truncGE n).obj Y, (t.truncGEπ n).app Y,
      (t.truncGEδLT n).app Y ≫ (inv ((t.truncLT n).map f))⟦1⟧',
      isomorphic_distinguished _ (t.triangleLTGE_distinguished n Y) _ ?_, inferInstance⟩
    exact Triangle.isoMk _ _ (asIso ((t.truncLT n).map f)) (Iso.refl _) (Iso.refl _)
  · obtain ⟨e, he⟩ := t.triangle_iso_exists
      mem (t.triangleLTGE_distinguished n Y) (Iso.refl _) (n - 1) n
      (by dsimp; infer_instance) (by dsimp; infer_instance)
      (by dsimp; infer_instance) (by dsimp; infer_instance)
    suffices ((t.truncLT n).map f) = e.hom.hom₁ by rw [this]; infer_instance
    exact t.to_truncLT_obj_ext (Eq.trans (by cat_disch) e.hom.comm₁)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Triangulated.TStructure.isIso_truncGE_map_iff** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：isIso_truncGE_map_iff {Y Z : C} (g : Y ⟶ Z) (n₀ n₁ : Int) (hn : n₀ + 1 = n
₁) : IsIso ((t.truncGE n₁).map g) ↔ exists (X : C) (f : X ⟶ Y) (h : ((t.truncGE 
n₁).obj Z) ⟶ X⟦(1 : Int)⟧) (_ : Triangle.mk f (g ≫ (t.truncGEπ n₁).app Z) h in d
istTriang _), t.IsLE X n₀
参数：g : Y ⟶ Z；n₀ n₁ : Int；hn : n₀ + 1 = n₁。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Pretriangulated.isomorphic_distinguished`：∀ {C : Type u} 
{inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZer
oObject C}   {inst_2 : CategoryTheory.HasShif…
· 使用引理 `CategoryTheory.Triangulated.TStructure.triangleLTGE_distinguished`：trian
gleLTGE_distinguished (n : Int) (X : C) : (t.triangleLTGE n).obj X in distTriang
 C
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.Triangulated.TStructure.truncGEπ_naturality`：truncGEπ_nat
urality (n : Int) {X Y : C} (f : X ⟶ Y) : (t.truncGEπ n).app X ≫ (t.truncGE n).m
ap f = f ≫ (t.truncGEπ n).app Y
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.IsIso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [I : CategoryTheory.IsIso f] {Z : 
C}   (h : X ⟶ Z), CategoryT…
· 使用定理 `CategoryTheory.Triangulated.TStructure.instIsLEObjTruncLTHAddIntOfNat`：∀
 {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory
.Preadditive C]   [inst_2 : CategoryTheory.Limits.HasZeroOb…
· 使用定理 `CategoryTheory.Triangulated.TStructure.triangle_iso_exists`：∀ {C : Type 
u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditiv
e C]   [inst_2 : CategoryTheory.Limits.HasZeroOb…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Triangulated.TStructure.instIsGEObjTruncGE`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive
 C]   [inst_2 : CategoryTheory.Limits.HasZeroOb…
· 使用引理 `CategoryTheory.Triangulated.TStructure.from_truncGE_obj_ext`：from_truncG
E_obj_ext {n : Int} {X : C} {Y : C} {f₁ f₂ : (t.truncGE n).obj X ⟶ Y} (h : (t.tr
uncGEπ n).app X ≫ f₁ = (t.truncGEπ n).app X ≫ f₂)…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Pretriangulated.TriangleMorphism.comm₂`：∀ {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.HasShift C ℤ]  
 {T₁ T₂ : CategoryTheory.Pretriangulated.Tr…
· 使用定理 `CategoryTheory.Pretriangulated.Triangle.instIsIsoHom₃`：∀ {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.HasShift C ℤ]  
 {A B : CategoryTheory.Pretriangulated.Tria…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
lemma isIso_truncGE_map_iff {Y Z : C} (g : Y ⟶ Z) (n₀ n₁ : ℤ) (hn : n₀ + 1 = n₁) :
    IsIso ((t.truncGE n₁).map g) ↔
      ∃ (X : C) (f : X ⟶ Y) (h : ((t.truncGE n₁).obj Z) ⟶ X⟦(1 : ℤ)⟧)
        (_ : Triangle.mk f (g ≫ (t.truncGEπ n₁).app Z) h ∈ distTriang _), t.IsLE X n₀ := by
  refine ⟨fun hf ↦ ?_, fun ⟨X, f, h, mem, _⟩ ↦ ?_⟩
  · refine ⟨_, (t.truncLTι n₁).app Y, inv ((t.truncGE n₁).map g) ≫ (t.truncGEδLT n₁).app Y,
      isomorphic_distinguished _ (t.triangleLTGE_distinguished n₁ Y) _ ?_,
      by subst hn; infer_instance⟩
    exact Iso.symm (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
      (asIso ((t.truncGE n₁).map g)) (by simp) (by simp) (by simp))
  · obtain ⟨e, he⟩ :=
      t.triangle_iso_exists (t.triangleLTGE_distinguished n₁ Y) mem (Iso.refl _) n₀ n₁
        (by dsimp; rw [← hn]; infer_instance) (by dsimp; infer_instance)
        (by dsimp; infer_instance) (by dsimp; infer_instance)
    suffices ((t.truncGE n₁).map g) = e.hom.hom₃ by rw [this]; infer_instance
    exact t.from_truncGE_obj_ext (Eq.trans (by cat_disch) e.hom.comm₂.symm)
/-
**CategoryTheory.Triangulated.TStructure.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : C) (a b : ℤ) [t.IsLE X b] : t.IsLE ((t.truncLT a).obj X) b := by
  by_cases h : a ≤ b + 1
  · exact t.isLE_truncLT_obj ..
  · have := (t.isLE_iff_isIso_truncLTι_app (a - 1) a (by lia) X).1 (t.isLE_of_le _ b _ (by lia))
    exact t.isLE_of_iso (show X ≅ _ from (asIso ((t.truncLTι a).app X)).symm) _
/-
**CategoryTheory.Triangulated.TStructure.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : C) (a b : ℤ) [t.IsGE X a] : t.IsGE ((t.truncGE b).obj X) a := by
  by_cases h : a ≤ b
  · exact t.isGE_truncGE_obj ..
  · have : t.IsGE X b := t.isGE_of_ge X b a (by lia)
    exact t.isGE_of_iso (show X ≅ _ from asIso ((t.truncGEπ b).app X)) _

/-- The composition `t.truncLT b ⋙ t.truncGE a`. -/
/-
**CategoryTheory.Triangulated.TStructure.truncGELT** 是 Mathlib 中的一个缩写定义，位于命名空间 `
CategoryTheory.Triangulated.TStructure`。
形式化陈述：truncGELT (a b : Int) : C ⥤ C
参数：a b : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition `t.truncLT b ⋙ t.truncGE a`.
-/
noncomputable abbrev truncGELT (a b : ℤ) : C ⥤ C := t.truncLT b ⋙ t.truncGE a

/-- The composition `t.truncGE b ⋙ t.truncLT a`. -/
/-
**CategoryTheory.Triangulated.TStructure.truncLTGE** 是 Mathlib 中的一个缩写定义，位于命名空间 `
CategoryTheory.Triangulated.TStructure`。
形式化陈述：truncLTGE (a b : Int) : C ⥤ C
参数：a b : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition `t.truncGE b ⋙ t.truncLT a`.
-/
noncomputable abbrev truncLTGE (a b : ℤ) : C ⥤ C := t.truncGE a ⋙ t.truncLT b

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Triangulated.TStructure.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : C) (a b : ℤ) : t.IsGE ((t.truncGELT a b).obj X) a := by
  dsimp; infer_instance

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Triangulated.TStructure.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : C) (a b : ℤ) : t.IsLE ((t.truncLTGE a b).obj X) (b - 1) := by
  dsimp; infer_instance

section

variable [IsTriangulated C]

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Triangulated.TStructure.isIso** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isIso₁_truncLT_map_of_isGE (T : Triangle C) (hT : T ∈ distTriang C)
    (n : ℤ) (h₃ : t.IsGE T.obj₃ n) :
    IsIso ((t.truncLT n).map T.mor₁) := by
  rw [isIso_truncLT_map_iff]
  obtain ⟨Z, g, k, mem⟩ := distinguished_cocone_triangle ((t.truncLTι n).app T.obj₁ ≫ T.mor₁)
  refine ⟨_, _, _, mem, ?_⟩
  let H := someOctahedron rfl (t.triangleLTGE_distinguished n T.obj₁) hT mem
  exact t.isGE₂ _ H.mem n (by dsimp; infer_instance) (by dsimp; infer_instance)
/-
**CategoryTheory.Triangulated.TStructure.isIso** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isIso₂_truncGE_map_of_isLE (T : Triangle C) (hT : T ∈ distTriang C)
    (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (h₁ : t.IsLE T.obj₁ n₀) :
    IsIso ((t.truncGE n₁).map T.mor₂) := by
  rw [isIso_truncGE_map_iff _ _ _ _ h]
  obtain ⟨X, f, k, mem⟩ := distinguished_cocone_triangle₁ (T.mor₂ ≫ (t.truncGEπ n₁).app T.obj₃)
  refine ⟨_, _, _, mem, ?_⟩
  subst h
  have H := someOctahedron rfl (rot_of_distTriang _ hT)
    (rot_of_distTriang _ (t.triangleLTGE_distinguished (n₀ + 1) T.obj₃))
    (rot_of_distTriang _ mem)
  have : t.IsLE (X⟦(1 : ℤ)⟧) (n₀ - 1) :=
    t.isLE₂ _ H.mem (n₀ - 1) (t.isLE_shift T.obj₁ n₀ 1 (n₀ - 1) (by lia))
      (t.isLE_shift ((t.truncLT (n₀ + 1)).obj T.obj₃) n₀ 1 (n₀-1) (by lia))
  exact t.isLE_of_shift X n₀ 1 (n₀ - 1) (by lia)

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Triangulated.TStructure.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : C) (a b : ℤ) [t.IsGE X a] :
    t.IsGE ((t.truncLT b).obj X) a := by
  rw [t.isGE_iff_isZero_truncLT_obj]
  have := t.isIso₁_truncLT_map_of_isGE _ ((t.triangleLTGE_distinguished b X)) a
    (by dsimp; infer_instance)
  dsimp at this
  refine IsZero.of_iso ?_ (asIso ((t.truncLT a).map ((t.truncLTι b).app X)))
  rwa [← isGE_iff_isZero_truncLT_obj]

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Triangulated.TStructure.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : C) (a b : ℤ) [t.IsLE X b] : t.IsLE ((t.truncGE a).obj X) b := by
  rw [t.isLE_iff_isZero_truncGE_obj b (b + 1) rfl]
  have := t.isIso₂_truncGE_map_of_isLE _ (t.triangleLTGE_distinguished a X) b _ rfl
    (by dsimp; infer_instance)
  dsimp at this
  refine IsZero.of_iso ?_ (asIso ((t.truncGE (b + 1)).map ((t.truncGEπ a).app X))).symm
  rwa [← isLE_iff_isZero_truncGE_obj _ _ _ rfl]

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Triangulated.TStructure.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : C) (a b : ℤ) :
    t.IsLE ((t.truncGELT a b).obj X) (b - 1) := by
  dsimp; infer_instance

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Triangulated.TStructure.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : C) (a b : ℤ) :
    t.IsGE ((t.truncLTGE a b).obj X) a := by
  dsimp; infer_instance
/-
**CategoryTheory.Triangulated.TStructure.isIso_truncGE_map_truncGE** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isIso_truncGE_map_truncGEπ_app (a b : ℤ) (h : b ≤ a) (X : C) :
    IsIso ((t.truncGE a).map ((t.truncGEπ b).app X)) :=
  t.isIso₂_truncGE_map_of_isLE _ (t.triangleLTGE_distinguished b X)
    (a - 1) a (by lia) (t.isLE_truncLT_obj _ _ _ (by simpa))
/-
**CategoryTheory.Triangulated.TStructure.isIso_truncLT_map_truncLT** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isIso_truncLT_map_truncLTι_app (a b : ℤ) (h : a ≤ b) (X : C) :
    IsIso ((t.truncLT a).map ((t.truncLTι b).app X)) :=
  t.isIso₁_truncLT_map_of_isGE _ (t.triangleLTGE_distinguished b X) a
    (t.isGE_of_ge ((t.truncGE b).obj X) a b (by lia))
/-
**CategoryTheory.Triangulated.TStructure.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : C) (n : ℤ) : IsIso ((t.truncLT n).map ((t.truncLTι n).app X)) :=
  isIso_truncLT_map_truncLTι_app t _ _ (by rfl) X
/-
**CategoryTheory.Triangulated.TStructure.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : C) (n : ℤ) : IsIso ((t.truncGE n).map ((t.truncGEπ n).app X)) :=
  t.isIso_truncGE_map_truncGEπ_app _ _ (by rfl) _
/-
**CategoryTheory.Triangulated.TStructure.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (a b : ℤ) (X : C) :
    IsIso ((t.truncLTι b).app ((t.truncGE a).obj ((t.truncLT b).obj X))) := by
  rw [← t.isLE_iff_isIso_truncLTι_app (b - 1) b (by lia)]
  infer_instance

/-- The natural transformation `t.truncGELT a b ⟶ t.truncLTGE a b`
(which is an isomorphism, see `truncGELTIsoLTGE`.) -/
/-
**CategoryTheory.Triangulated.TStructure.truncGELTToLTGE** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：truncGELTToLTGE (a b : Int) : t.truncGELT a b ⟶ t.truncLTGE a b where app 
X
参数：a b : Int。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Triangulated.TStructure.instIsGEObjTruncGE`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive
 C]   [inst_2 : CategoryTheory.Limits.HasZeroOb…

--- 原说明 ---
The natural transformation `t.truncGELT a b ⟶ t.truncLTGE a b`
(which is an isomorphism, see `truncGELTIsoLTGE`.)
-/
noncomputable def truncGELTToLTGE (a b : ℤ) :
    t.truncGELT a b ⟶ t.truncLTGE a b where
  app X := t.liftTruncLT (t.descTruncGE
    ((t.truncLTι b).app X ≫ (t.truncGEπ a).app X) a) (b - 1) b (by lia)
  naturality _ _ _ :=
    t.to_truncLT_obj_ext (by dsimp; exact t.from_truncGE_obj_ext (by simp))

@[reassoc (attr := simp)]
/-
**CategoryTheory.Triangulated.TStructure.truncGELTToLTGE_app_pentagon** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：truncGELTToLTGE_app_pentagon (a b : Int) (X : C) : (t.truncGEπ a).app _ ≫ 
(t.truncGELTToLTGE a b).app X ≫ (t.truncLTι b).app _ = (t.truncLTι b).app X ≫ (t
.truncGEπ a).app X
参数：a b : Int；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Triangulated.TStructure.instIsGEObjTruncGE`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive
 C]   [inst_2 : CategoryTheory.Limits.HasZeroOb…
· 使用引理 `CategoryTheory.Triangulated.TStructure.liftTruncLT_ι`：liftTruncLT_ι {X Y
 : C} (f : X ⟶ Y) (n₀ n₁ : Int) (h : n₀ + 1 = n₁) [t.IsLE X n₀] : t.liftTruncLT 
f n₀ n₁ h ≫ (t.truncLTι n₁).app Y = f
· 使用引理 `CategoryTheory.Triangulated.TStructure.π_descTruncGE`：π_descTruncGE {X Y
 : C} (f : X ⟶ Y) (n : Int) [t.IsGE Y n] : (t.truncGEπ n).app X ≫ t.descTruncGE 
f n = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma truncGELTToLTGE_app_pentagon (a b : ℤ) (X : C) :
    (t.truncGEπ a).app _ ≫ (t.truncGELTToLTGE a b).app X ≫ (t.truncLTι b).app _ =
      (t.truncLTι b).app X ≫ (t.truncGEπ a).app X := by
  simp [truncGELTToLTGE]
/-
**CategoryTheory.Triangulated.TStructure.truncGELTToLTGE_app_pentagon_uniqueness
** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：truncGELTToLTGE_app_pentagon_uniqueness {a b : Int} {X : C} (φ : (t.truncG
ELT a b).obj X ⟶ (t.truncLTGE a b).obj X) (hφ : (t.truncGEπ a).app _ ≫ φ ≫ (t.tr
uncLTι b).app _ = (t.truncLTι b).app X ≫ (t.truncGEπ a).app X) : (t.truncGELTToL
TGE a b).app X = φ
参数：φ : (t.truncGELT a b).obj X ⟶ (t.truncLTGE a b).obj X；hφ : (t.truncGEπ a).app
 _ ≫ φ ≫ (t.truncLTι b).app _ = (t.truncLTι b).app X ≫ (t.truncGEπ a).app X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Triangulated.TStructure.to_truncLT_obj_ext`：to_truncLT_ob
j_ext {n : Int} {Y : C} {X : C} {f₁ f₂ : Y ⟶ (t.truncLT n).obj X} (h : f₁ ≫ (t.t
runcLTι n).app X = f₂ ≫ (t.truncLTι n).app X) […
· 使用引理 `CategoryTheory.Triangulated.TStructure.from_truncGE_obj_ext`：from_truncG
E_obj_ext {n : Int} {X : C} {Y : C} {f₁ f₂ : (t.truncGE n).obj X ⟶ Y} (h : (t.tr
uncGEπ n).app X ≫ f₁ = (t.truncGEπ n).app X ≫ f₂)…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Triangulated.TStructure.truncGELTToLTGE_app_pentagon`：tru
ncGELTToLTGE_app_pentagon (a b : Int) (X : C) : (t.truncGEπ a).app _ ≫ (t.truncG
ELTToLTGE a b).app X ≫ (t.truncLTι b).app _ = (t.truncLTι…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Triangulated.TStructure.instIsGEObjTruncGE`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive
 C]   [inst_2 : CategoryTheory.Limits.HasZeroOb…
· 使用定理 `CategoryTheory.Triangulated.TStructure.instIsLEObjTruncGELTHSubIntOfNat`
：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheo
ry.Preadditive C]   [inst_2 : CategoryTheory.Limits.HasZeroOb…
-/
lemma truncGELTToLTGE_app_pentagon_uniqueness {a b : ℤ} {X : C}
    (φ : (t.truncGELT a b).obj X ⟶ (t.truncLTGE a b).obj X)
    (hφ : (t.truncGEπ a).app _ ≫ φ ≫ (t.truncLTι b).app _ =
      (t.truncLTι b).app X ≫ (t.truncGEπ a).app X) :
    (t.truncGELTToLTGE a b).app X = φ :=
  t.to_truncLT_obj_ext (by dsimp; exact t.from_truncGE_obj_ext (by cat_disch))

@[reassoc]
/-
**CategoryTheory.Triangulated.TStructure.truncLT_map_truncGE_map_truncLT** 是 Mat
hlib 中的一个引理，位于命名空间 `CategoryTheory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma truncLT_map_truncGE_map_truncLTι_app_fac (a b : ℤ) (X : C) :
    (t.truncLTι b).app ((t.truncGE a).obj ((t.truncLT b).obj X)) ≫
        (t.truncGELTToLTGE a b).app X =
    (t.truncLT b).map ((t.truncGE a).map ((t.truncLTι b).app X)) := by
  rw [← cancel_epi (inv ((t.truncLTι b).app ((t.truncGE a).obj ((t.truncLT b).obj X)))),
    IsIso.inv_hom_id_assoc]
  exact t.truncGELTToLTGE_app_pentagon_uniqueness _ (by simp)

/-- The connecting homomorphism
`(t.truncGELT a b).obj X ⟶ ((t.truncLT a).obj X)⟦1⟧`,
as a natural transformation. -/
@[expose, simps!]
/-
**CategoryTheory.Triangulated.TStructure.truncGELT** 是 Mathlib 中的一个缩写定义，位于命名空间 `
CategoryTheory.Triangulated.TStructure`。
形式化陈述：truncGELT (a b : Int) : C ⥤ C
参数：a b : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The connecting homomorphism
`(t.truncGELT a b).obj X ⟶ ((t.truncLT a).obj X)⟦1⟧`,
as a natural transformation.
-/
noncomputable def truncGELTδLT (a b : ℤ) :
    t.truncGELT a b ⟶ t.truncLT a ⋙ shiftFunctor C (1 : ℤ) :=
  Functor.whiskerLeft (t.truncLT b) (t.truncGEδLT a) ≫
    Functor.whiskerRight (t.truncLTι b) (t.truncLT a ⋙ shiftFunctor C (1 : ℤ))

/-- The functorial (distinguished) triangle
`(t.truncLT a).obj X ⟶ (t.truncLT b).obj X ⟶ (t.truncGELT a b).obj X ⟶ ...`
when `a ≤ b`. -/
@[expose, simps!]
/-
**CategoryTheory.Triangulated.TStructure.triangleLTLTGELT** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：triangleLTLTGELT (a b : Int) (h : a <= b) : C ⥤ Triangle C
参数：a b : Int；h : a <= b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functorial (distinguished) triangle
`(t.truncLT a).obj X ⟶ (t.truncLT b).obj X ⟶ (t.truncGELT a b).obj X ⟶ ...`
when `a ≤ b`.
-/
noncomputable def triangleLTLTGELT (a b : ℤ) (h : a ≤ b) : C ⥤ Triangle C :=
  Triangle.functorMk (t.natTransTruncLTOfLE a b h)
    (Functor.whiskerLeft (t.truncLT b) (t.truncGEπ a)) (t.truncGELTδLT a b)

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Triangulated.TStructure.triangleLTLTGELT_distinguished** 是 Math
lib 中的一个引理，位于命名空间 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：triangleLTLTGELT_distinguished (a b : Int) (h : a <= b) (X : C) : (t.trian
gleLTLTGELT a b h).obj X in distTriang C
参数：a b : Int；h : a <= b；X : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Triangulated.TStructure.isIso_truncLT_map_truncLTι_app`：i
sIso_truncLT_map_truncLTι_app (a b : Int) (h : a <= b) (X : C) : IsIso ((t.trunc
LT a).map ((t.truncLTι b).app X))
· 使用定理 `CategoryTheory.Pretriangulated.isomorphic_distinguished`：∀ {C : Type u} 
{inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZer
oObject C}   {inst_2 : CategoryTheory.HasShif…
· 使用引理 `CategoryTheory.Triangulated.TStructure.triangleLTGE_distinguished`：trian
gleLTGE_distinguished (n : Int) (X : C) : (t.triangleLTGE n).obj X in distTriang
 C
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `CategoryTheory.Triangulated.TStructure.to_truncLT_obj_ext`：to_truncLT_ob
j_ext {n : Int} {Y : C} {X : C} {f₁ f₂ : Y ⟶ (t.truncLT n).obj X} (h : f₁ ≫ (t.t
runcLTι n).app X = f₂ ≫ (t.truncLTι n).app X) […
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Triangulated.TStructure.natTransTruncLTOfLE_ι_app_assoc`：
∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheor
y.Preadditive C]   [inst_2 : CategoryTheory.Limits.HasZeroOb…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Triangulated.TStructure.instIsLEObjTruncLT`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive
 C]   [inst_2 : CategoryTheory.Limits.HasZeroOb…
· 使用定理 `CategoryTheory.Triangulated.TStructure.instIsLEObjTruncLTHSubIntOfNat`：∀
 {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory
.Preadditive C]   [inst_2 : CategoryTheory.Limits.HasZeroOb…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Functor.map_inv`：map_inv (F : C ⥤ D) {X Y : C} (f : X ⟶ Y
) [IsIso f] : F.map (inv f) = inv (F.map f)
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
-/
lemma triangleLTLTGELT_distinguished (a b : ℤ) (h : a ≤ b) (X : C) :
    (t.triangleLTLTGELT a b h).obj X ∈ distTriang C := by
  have := t.isIso_truncLT_map_truncLTι_app a b h X
  refine isomorphic_distinguished _ (t.triangleLTGE_distinguished a ((t.truncLT b).obj X)) _ ?_
  refine Triangle.isoMk _ _ ((asIso ((t.truncLT a).map ((t.truncLTι b).app X))).symm)
    (Iso.refl _) (Iso.refl _) ?_ (by simp) (by simp)
  dsimp
  simp only [Category.comp_id, IsIso.eq_inv_comp]
  exact t.to_truncLT_obj_ext (by simp)

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Triangulated.TStructure.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (a b : ℤ) : IsIso (t.truncGELTToLTGE a b) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  by_cases h : a ≤ b
  · let u₁₂ := (t.natTransTruncLTOfLE a b h).app X
    let u₂₃ : (t.truncLT b).obj X ⟶ X := (t.truncLTι b).app X
    let u₁₃ : _ ⟶ X := (t.truncLTι a).app X
    have eq : u₁₂ ≫ u₂₃ = u₁₃ := by simp [u₁₂, u₂₃, u₁₃]
    have H := someOctahedron eq (t.triangleLTLTGELT_distinguished a b h X)
      (t.triangleLTGE_distinguished b X) (t.triangleLTGE_distinguished a X)
    let m₁ : (t.truncGELT a b).obj X ⟶ _ := H.m₁
    have : IsIso ((t.truncLT b).map H.m₁) :=
      t.isIso₁_truncLT_map_of_isGE _ H.mem b (by dsimp; infer_instance)
    have eq' : t.liftTruncLT m₁ (b - 1) b (by lia) = (t.truncGELTToLTGE a b).app X :=
      t.to_truncLT_obj_ext
        (by dsimp; exact t.from_truncGE_obj_ext (by simpa using H.comm₁))
    rw [← eq']
    have fac : (t.truncLTι b).app ((t.truncGE a).obj ((t.truncLT b).obj X)) ≫
        t.liftTruncLT m₁ (b - 1) b (by lia) = (t.truncLT b).map m₁ :=
      t.to_truncLT_obj_ext (by simp [truncGELT])
    exact IsIso.of_isIso_fac_left fac
  · simp at h
    refine ⟨0, ?_, ?_⟩
    all_goals exact IsZero.eq_of_src (t.isZero _ (b-1) a (by lia)) _ _
/-
**CategoryTheory.Triangulated.TStructure.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (a b : ℤ) (X : C) :
    IsIso ((t.truncLT b).map ((t.truncGE a).map ((t.truncLTι b).app X))) := by
  rw [← t.truncLT_map_truncGE_map_truncLTι_app_fac a b X]
  infer_instance

/-- The natural transformation `t.truncGELT a b ≅ t.truncLTGE a b`. -/
/-
**CategoryTheory.Triangulated.TStructure.truncGELTIsoLTGE** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：truncGELTIsoLTGE (a b : Int) : t.truncGELT a b ≅ t.truncLTGE a b
参数：a b : Int。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Triangulated.TStructure.instIsIsoFunctorTruncGELTToLTGE`：
∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheor
y.Preadditive C]   [inst_2 : CategoryTheory.Limits.HasZeroOb…

--- 原说明 ---
The natural transformation `t.truncGELT a b ≅ t.truncLTGE a b`.
-/
noncomputable def truncGELTIsoLTGE (a b : ℤ) : t.truncGELT a b ≅ t.truncLTGE a b :=
  asIso (t.truncGELTToLTGE a b)

end

end

end TStructure

end Triangulated

end CategoryTheory

