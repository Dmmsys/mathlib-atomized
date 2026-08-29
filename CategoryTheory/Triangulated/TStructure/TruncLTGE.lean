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

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C Int]
  [forall (n : Int), (shiftFunctor C n).Additive] [Pretriangulated C]

namespace Triangulated

namespace TStructure

variable (t : TStructure C)

set_option backward.isDefEq.respectTransparency false in
/-- Two morphisms `T ⟶ T'` between distinguished triangles must coincide when
they coincide on the middle object, and there are integers `a ≤ b` such that
for a t-structure, we have `T.obj₁ ≤ a` and `T'.obj₃ ≥ b`. -/
public lemma triangle_map_ext {T T' : Triangle C} {f₁ f₂ : T ⟶ T'}
    (hT : T in distTriang C) (hT' : T' in distTriang C) (a b : Int)
    (h₀ : t.IsLE T.obj₁ a) (h₁ : t.IsGE T'.obj₃ b)
    (H : f₁.hom₂ = f₂.hom₂ := by cat_disch)
    (hab : a <= b := by lia) : f₁ = f₂ := by
  suffices forall (f : T ⟶ T'), f.hom₂ = 0 -> f = 0 by rw [← sub_eq_zero]; cat_disch
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
    (hT : T in distTriang C) (hT' : T' in distTriang C)
    (φ : T.obj₂ ⟶ T'.obj₂) (a b : Int)
    (h₀ : t.IsLE T.obj₁ a) (h₁' : t.IsGE T'.obj₃ b) (h : a < b := by lia) :
    exists (f : T ⟶ T'), f.hom₂ = φ := by
  obtain ⟨a, comm₁⟩ := T'.coyoneda_exact₂ hT' (T.mor₁ ≫ φ) (t.zero _ a b)
  obtain ⟨c, comm₂, comm₃⟩ := complete_distinguished_triangle_morphism _ _ hT hT' a φ comm₁
  exact ⟨{ hom₁ := a, hom₂ := φ, hom₃ := c }, rfl⟩

/-- If `a < b`, then an isomorphism `T.obj₂ ≅ T'.obj₂` extends to an isomorphism `T ≅ T'`
of distinguished triangles when for a t-structure, both `T.obj₁` and `T'.obj₁` are `≤ a` and
both `T.obj₃` and `T'.obj₃` are `≥ b`. -/
public lemma triangle_iso_exists {T T' : Triangle C}
    (hT : T in distTriang C) (hT' : T' in distTriang C) (e : T.obj₂ ≅ T'.obj₂)
    (a b : Int) (h₀ : t.IsLE T.obj₁ a) (h₁ : t.IsGE T.obj₃ b)
    (h₀' : t.IsLE T'.obj₁ a) (h₁' : t.IsGE T'.obj₃ b) (h : a < b := by lia) :
    exists (e' : T ≅ T'), e'.hom.hom₂ = e.hom := by
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

variable (n : Int) (X : C)

/-- Given a t-structure `t` on `C`, `X : C` and `n : ℤ`, this is a distinguished
triangle `obj₁ ⟶ X ⟶ obj₃ ⟶ obj₁⟦1⟧` where `obj₁` is `< n` and `obj₃` is `≥ n`.
(This should not be used directly: use `truncLT` and `truncGE` instead.) -/
@[simps! obj₂]
/--
Definition of `triangle` / `triangle` 的定义

English:
definition triangle
  signature: : Triangle C
  body: Triangle.mk
    (t.exists_triangle X (n - 1) n
      (by lia)).choose_spec.choose_spec.choose_spec.choose_spec.choose
    (t.exists_triangle X (n - 1) n
      (by lia)).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose
    (t.exists_triangle X (n - 1) n
      (by lia)).choose_spec.c

中文:
定义 triangle
  签名: : Triangle C
  定义体: Triangle.mk
    (t.exists_triangle X (n - 1) n
      (by lia)).choose_spec.choose_spec.choose_spec.choose_spec.choose
    (t.exists_triangle X (n - 1) n
      (by lia)).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose
    (t.exists_triangle X (n - 1) n
      (by lia)).choose_spec.c

Depends on / 依赖: Triangle, Triangle.mk, choose_spec, choose_spec.choose_spec.choose_spec.choose_spec.choose, choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose, choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose, exists_triangle, t.exists_triangle
-/
noncomputable def triangle : Triangle C :=
  Triangle.mk
    (t.exists_triangle X (n - 1) n
      (by lia)).choose_spec.choose_spec.choose_spec.choose_spec.choose
    (t.exists_triangle X (n - 1) n
      (by lia)).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose
    (t.exists_triangle X (n - 1) n
      (by lia)).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose

/--
lemma `triangle_distinguished` / 引理 `triangle_distinguished`

English:
lemma triangle_distinguished
  proof: (t.exists_triangle X (n - 1) n
    (by lia)).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec

中文:
引理 triangle_distinguished
  证明: (t.exists_triangle X (n - 1) n
    (by lia)).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec

Depends on / 依赖: choose_spec, choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec, exists_triangle, t.exists_triangle
-/
lemma triangle_distinguished :
    triangle t n X in distTriang C :=
  (t.exists_triangle X (n - 1) n
    (by lia)).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec

/--
Instance `triangle_obj₁_isLE` / 实例 `triangle_obj₁_isLE`

English:
instance triangle_obj₁_isLE
  signature: (n : Int)
  body: ⟨(t.exists_triangle X (n - 1) n (by lia)).choose_spec.choose_spec.choose⟩

中文:
实例 triangle_obj₁_isLE
  签名: (n : 整数)
  定义体: ⟨(t.exists_triangle X (n - 1) n (by lia)).choose_spec.choose_spec.choose⟩

Depends on / 依赖: choose_spec, choose_spec.choose_spec.choose, exists_triangle, t.exists_triangle
-/
instance triangle_obj₁_isLE (n : Int) :
    t.IsLE (triangle t n X).obj₁ (n - 1) :=
  ⟨(t.exists_triangle X (n - 1) n (by lia)).choose_spec.choose_spec.choose⟩

/--
Instance `triangle_obj₃_isGE` / 实例 `triangle_obj₃_isGE`

English:
instance triangle_obj₃_isGE
  signature: :
  body: ⟨(t.exists_triangle X (n - 1) n (by lia)).choose_spec.choose_spec.choose_spec.choose⟩

中文:
实例 triangle_obj₃_isGE
  签名: :
  定义体: ⟨(t.exists_triangle X (n - 1) n (by lia)).choose_spec.choose_spec.choose_spec.choose⟩

Depends on / 依赖: choose_spec, choose_spec.choose_spec.choose_spec.choose, exists_triangle, t.exists_triangle
-/
instance triangle_obj₃_isGE :
    t.IsGE (triangle t n X).obj₃ n :=
  ⟨(t.exists_triangle X (n - 1) n (by lia)).choose_spec.choose_spec.choose_spec.choose⟩

variable {X} {Y : C} (φ : X ⟶ Y)

/-- Version of `TStructure.triangle_map_ext` that is specialized for the auxiliary
definition `TruncAux.triangle`. -/
@[ext]
/--
lemma `triangle_map_ext'` / 引理 `triangle_map_ext'`

English:
lemma triangle_map_ext'
  statement: (f₁ f₂ : triangle t n X ⟶ triangle t n Y)
  proof: triangle_map_ext t (triangle_distinguished t n X) (triangle_distinguished t n Y) (n - 1) n
    inferInstance inferInstance H (by lia)

中文:
引理 triangle_map_ext'
  结论: (f₁ f₂ : triangle t n X ⟶ triangle t n Y)
  证明: triangle_map_ext t (triangle_distinguished t n X) (triangle_distinguished t n Y) (n - 1) n
    inferInstance inferInstance H (by lia)

Depends on / 依赖: cat_disch, triangle_distinguished, triangle_map_ext
-/
lemma triangle_map_ext' (f₁ f₂ : triangle t n X ⟶ triangle t n Y)
    (H : f₁.hom₂ = f₂.hom₂ := by cat_disch) : f₁ = f₂ :=
  triangle_map_ext t (triangle_distinguished t n X) (triangle_distinguished t n Y) (n - 1) n
    inferInstance inferInstance H (by lia)

/-- Auxiliary definition for `triangleFunctor`. -/
@[simps hom₂]
/--
Definition of `triangleMap` / `triangleMap` 的定义

English:
definition triangleMap
  signature: : triangle t n X ⟶ triangle t n Y
  body: have H := triangle_map_exists t (triangle_distinguished t n X)
    (triangle_distinguished t n Y) φ (n - 1) n inferInstance inferInstance (by lia)
  { hom₁ := H.choose.hom₁
    hom₂ := φ
    hom₃ := H.choose.hom₃
    comm₁ := by rw [← H.choose.comm₁, H.choose_spec]
    comm₂ := by rw [H.choose.comm₂

中文:
定义 triangleMap
  签名: : triangle t n X ⟶ triangle t n Y
  定义体: have H := triangle_map_exists t (triangle_distinguished t n X)
    (triangle_distinguished t n Y) φ (n - 1) n inferInstance inferInstance (by lia)
  { hom₁ := H.choose.hom₁
    hom₂ := φ
    hom₃ := H.choose.hom₃
    comm₁ := by rw [← H.choose.comm₁, H.choose_spec]
    comm₂ := by rw [H.choose.comm₂

Depends on / 依赖: H.choose.comm, H.choose.hom, H.choose_spec, choose_spec, triangle_distinguished, triangle_map_exists
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
/--
Definition of `triangleFunctor` / `triangleFunctor` 的定义

English:
definition triangleFunctor
  signature: : C ⥤ Triangle C where
  body: triangle t n
  map φ := triangleMap t n φ

中文:
定义 triangleFunctor
  签名: : C ⥤ Triangle C where
  定义体: triangle t n
  map φ := triangleMap t n φ

Depends on / 依赖: triangle
-/
noncomputable def triangleFunctor : C ⥤ Triangle C where
  obj := triangle t n
  map φ := triangleMap t n φ

variable (A)

/--
lemma `triangleFunctor_obj_distinguished` / 引理 `triangleFunctor_obj_distinguished`

English:
lemma triangleFunctor_obj_distinguished
  proof: triangle_distinguished t n A

中文:
引理 triangleFunctor_obj_distinguished
  证明: triangle_distinguished t n A

Depends on / 依赖: triangle_distinguished
-/
lemma triangleFunctor_obj_distinguished :
    (triangleFunctor t n).obj A in distTriang C :=
  triangle_distinguished t n A

/--
Instance `isLE_triangleFunctor_obj_obj₁` / 实例 `isLE_triangleFunctor_obj_obj₁`

English:
instance isLE_triangleFunctor_obj_obj₁
  signature: :
  body: by
  dsimp [triangleFunctor]
  infer_instance

中文:
实例 isLE_triangleFunctor_obj_obj₁
  签名: :
  定义体: by
  dsimp [triangleFunctor]
  infer_instance

Depends on / 依赖: infer_instance, triangleFunctor
-/
instance isLE_triangleFunctor_obj_obj₁ :
    t.IsLE ((triangleFunctor t n).obj A).obj₁ (n - 1) := by
  dsimp [triangleFunctor]
  infer_instance

/--
Instance `isGE_triangleFunctor_obj_obj₃` / 实例 `isGE_triangleFunctor_obj_obj₃`

English:
instance isGE_triangleFunctor_obj_obj₃
  signature: :
  body: by
  dsimp [triangleFunctor]
  infer_instance

中文:
实例 isGE_triangleFunctor_obj_obj₃
  签名: :
  定义体: by
  dsimp [triangleFunctor]
  infer_instance

Depends on / 依赖: infer_instance, triangleFunctor
-/
instance isGE_triangleFunctor_obj_obj₃ :
    t.IsGE ((triangleFunctor t n).obj A).obj₃ n := by
  dsimp [triangleFunctor]
  infer_instance

/--
Definition of `triangleMapOfLE` / `triangleMapOfLE` 的定义

English:
definition triangleMapOfLE
  signature: (a b : Int) (h : a <= b)
  body: have H := triangle_map_exists t (triangle_distinguished t a A)
    (triangle_distinguished t b A) (𝟙 _) (a - 1) b inferInstance inferInstance
  { hom₁ := H.choose.hom₁
    hom₂ := 𝟙 _
    hom₃ := H.choose.hom₃
    comm₁ := by rw [← H.choose.comm₁, H.choose_spec]
    comm₂ := by rw [H.choose.comm₂, H

中文:
定义 triangleMapOfLE
  签名: (a b : 整数) (h : a <= b)
  定义体: have H := triangle_map_exists t (triangle_distinguished t a A)
    (triangle_distinguished t b A) (𝟙 _) (a - 1) b inferInstance inferInstance
  { hom₁ := H.choose.hom₁
    hom₂ := 𝟙 _
    hom₃ := H.choose.hom₃
    comm₁ := by rw [← H.choose.comm₁, H.choose_spec]
    comm₂ := by rw [H.choose.comm₂, H

Depends on / 依赖: H.choose.comm, H.choose.hom, H.choose_spec, choose_spec, triangle_distinguished, triangle_map_exists
-/
noncomputable def triangleMapOfLE (a b : Int) (h : a <= b) : triangle t a A ⟶ triangle t b A :=
  have H := triangle_map_exists t (triangle_distinguished t a A)
    (triangle_distinguished t b A) (𝟙 _) (a - 1) b inferInstance inferInstance
  { hom₁ := H.choose.hom₁
    hom₂ := 𝟙 _
    hom₃ := H.choose.hom₃
    comm₁ := by rw [← H.choose.comm₁, H.choose_spec]
    comm₂ := by rw [H.choose.comm₂, H.choose_spec]
    comm₃ := H.choose.comm₃ }

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `triangleFunctorNatTransOfLE` / `triangleFunctorNatTransOfLE` 的定义

English:
definition triangleFunctorNatTransOfLE
  signature: (a b : Int) (h : a <= b)
  body: triangleMapOfLE t X a b h
  naturality _ _ _ :=
    triangle_map_ext t (triangleFunctor_obj_distinguished _ _ _)
      (triangleFunctor_obj_distinguished _ _ _) (a - 1) b inferInstance inferInstance
        (by simp [triangleMapOfLE])

@[simp]

中文:
定义 triangleFunctorNatTransOfLE
  签名: (a b : 整数) (h : a <= b)
  定义体: triangleMapOfLE t X a b h
  naturality _ _ _ :=
    triangle_map_ext t (triangleFunctor_obj_distinguished _ _ _)
      (triangleFunctor_obj_distinguished _ _ _) (a - 1) b inferInstance inferInstance
        (by simp [triangleMapOfLE])

@[simp]

Depends on / 依赖: triangleMapOfLE
-/
noncomputable def triangleFunctorNatTransOfLE (a b : Int) (h : a <= b) :
    triangleFunctor t a ⟶ triangleFunctor t b where
  app X := triangleMapOfLE t X a b h
  naturality _ _ _ :=
    triangle_map_ext t (triangleFunctor_obj_distinguished _ _ _)
      (triangleFunctor_obj_distinguished _ _ _) (a - 1) b inferInstance inferInstance
        (by simp [triangleMapOfLE])

@[simp]
/--
lemma `triangleFunctorNatTransOfLE_app_hom₂` / 引理 `triangleFunctorNatTransOfLE_app_hom₂`

English:
lemma triangleFunctorNatTransOfLE_app_hom₂
  given: (a b : Int) (h : a <= b) (X : C)
  proof: rfl

中文:
引理 triangleFunctorNatTransOfLE_app_hom₂
  条件: (a b : 整数) (h : a <= b) (X : C)
  证明: rfl
-/
lemma triangleFunctorNatTransOfLE_app_hom₂ (a b : Int) (h : a <= b) (X : C) :
    ((triangleFunctorNatTransOfLE t a b h).app X).hom₂ = 𝟙 X := rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `triangleFunctorNatTransOfLE_trans` / 引理 `triangleFunctorNatTransOfLE_trans`

English:
lemma triangleFunctorNatTransOfLE_trans
  given: (a b c : Int) (hab : a <= b) (hbc : b <= c)
  proof: by
  apply NatTrans.ext
  ext1 X
  exact triangle_map_ext t (triangleFunctor_obj_distinguished _ _ _)
    (triangleFunctor_obj_distinguished _ _ _) (a - 1) c inferInstance inferInstance (by simp)

中文:
引理 triangleFunctorNatTransOfLE_trans
  条件: (a b c : 整数) (hab : a <= b) (hbc : b <= c)
  证明: by
  apply NatTrans.ext
  ext1 X
  exact triangle_map_ext t (triangleFunctor_obj_distinguished _ _ _)
    (triangleFunctor_obj_distinguished _ _ _) (a - 1) c inferInstance inferInstance (by simp)

Depends on / 依赖: NatTrans, NatTrans.ext, triangleFunctor_obj_distinguished, triangle_map_ext
-/
lemma triangleFunctorNatTransOfLE_trans (a b c : Int) (hab : a <= b) (hbc : b <= c) :
    triangleFunctorNatTransOfLE t a b hab ≫ triangleFunctorNatTransOfLE t b c hbc =
      triangleFunctorNatTransOfLE t a c (hab.trans hbc) := by
  apply NatTrans.ext
  ext1 X
  exact triangle_map_ext t (triangleFunctor_obj_distinguished _ _ _)
    (triangleFunctor_obj_distinguished _ _ _) (a - 1) c inferInstance inferInstance (by simp)

set_option backward.defeqAttrib.useBackward true in
/--
lemma `triangleFunctorNatTransOfLE_refl` / 引理 `triangleFunctorNatTransOfLE_refl`

English:
lemma triangleFunctorNatTransOfLE_refl
  given: (a : Int)
  proof: by
  apply NatTrans.ext
  ext1 X
  exact triangle_map_ext t (triangleFunctor_obj_distinguished _ _ _)
    (triangleFunctor_obj_distinguished _ _ _) (a - 1) a inferInstance inferInstance (by simp)

中文:
引理 triangleFunctorNatTransOfLE_refl
  条件: (a : 整数)
  证明: by
  apply NatTrans.ext
  ext1 X
  exact triangle_map_ext t (triangleFunctor_obj_distinguished _ _ _)
    (triangleFunctor_obj_distinguished _ _ _) (a - 1) a inferInstance inferInstance (by simp)

Depends on / 依赖: NatTrans, NatTrans.ext, triangleFunctor_obj_distinguished, triangle_map_ext
-/
lemma triangleFunctorNatTransOfLE_refl (a : Int) :
    triangleFunctorNatTransOfLE t a a (by rfl) = 𝟙 _ := by
  apply NatTrans.ext
  ext1 X
  exact triangle_map_ext t (triangleFunctor_obj_distinguished _ _ _)
    (triangleFunctor_obj_distinguished _ _ _) (a - 1) a inferInstance inferInstance (by simp)

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (triangleFunctor t n).Additive

中文:
实例 :
  签名: (triangleFunctor t n).Additive
-/
instance : (triangleFunctor t n).Additive where

end TruncAux

public section

/--
Definition of `truncLT` / `truncLT` 的定义

English:
definition truncLT
  signature: (n : Int)
  body: TruncAux.triangleFunctor t n ⋙ Triangle.π₁

中文:
定义 truncLT
  签名: (n : 整数)
  定义体: TruncAux.triangleFunctor t n ⋙ Triangle.π₁

Depends on / 依赖: Triangle, TruncAux, TruncAux.triangleFunctor, triangleFunctor
-/
noncomputable def truncLT (n : Int) : C ⥤ C :=
  TruncAux.triangleFunctor t n ⋙ Triangle.π₁

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance (n : Int) : (t.truncLT n).Additive where
  map_add {_ _ _ _} := by
    dsimp only [truncLT, Functor.comp_map]
    rw [Functor.map_add]
    dsimp

/--
Definition of `truncLTι` / `truncLTι` 的定义

English:
definition truncLTι
  signature: (n : Int)
  body: Functor.whiskerLeft (TruncAux.triangleFunctor t n) Triangle.π₁Toπ₂

中文:
定义 truncLTι
  签名: (n : 整数)
  定义体: Functor.whiskerLeft (TruncAux.triangleFunctor t n) Triangle.π₁Toπ₂

Depends on / 依赖: Functor, Functor.whiskerLeft, Triangle, TruncAux, TruncAux.triangleFunctor, triangleFunctor, whiskerLeft
-/
noncomputable def truncLTι (n : Int) : t.truncLT n ⟶ 𝟭 _ :=
  Functor.whiskerLeft (TruncAux.triangleFunctor t n) Triangle.π₁Toπ₂

/--
Definition of `truncGE` / `truncGE` 的定义

English:
definition truncGE
  signature: (n : Int)
  body: TruncAux.triangleFunctor t n ⋙ Triangle.π₃

中文:
定义 truncGE
  签名: (n : 整数)
  定义体: TruncAux.triangleFunctor t n ⋙ Triangle.π₃

Depends on / 依赖: Triangle, TruncAux, TruncAux.triangleFunctor, triangleFunctor
-/
noncomputable def truncGE (n : Int) : C ⥤ C :=
  TruncAux.triangleFunctor t n ⋙ Triangle.π₃

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance (n : Int) : (t.truncGE n).Additive where
  map_add {_ _ _ _} := by
    dsimp only [truncGE, Functor.comp_map]
    rw [Functor.map_add]
    dsimp

/--
Definition of `truncGEπ` / `truncGEπ` 的定义

English:
definition truncGEπ
  signature: (n : Int)
  body: Functor.whiskerLeft (TruncAux.triangleFunctor t n) Triangle.π₂Toπ₃

@[reassoc (attr := simp)]

中文:
定义 truncGEπ
  签名: (n : 整数)
  定义体: Functor.whiskerLeft (TruncAux.triangleFunctor t n) Triangle.π₂Toπ₃

@[reassoc (attr := simp)]

Depends on / 依赖: Functor, Functor.whiskerLeft, Triangle, TruncAux, TruncAux.triangleFunctor, triangleFunctor, whiskerLeft
-/
noncomputable def truncGEπ (n : Int) : 𝟭 _ ⟶ t.truncGE n :=
  Functor.whiskerLeft (TruncAux.triangleFunctor t n) Triangle.π₂Toπ₃

@[reassoc (attr := simp)]
/--
lemma `truncGEπ_naturality` / 引理 `truncGEπ_naturality`

English:
lemma truncGEπ_naturality
  given: (n : Int) {X Y : C} (f : X ⟶ Y)
  proof: ((t.truncGEπ n).naturality f).symm

中文:
引理 truncGEπ_naturality
  条件: (n : 整数) {X Y : C} (f : X ⟶ Y)
  证明: ((t.truncGEπ n).naturality f).symm

Depends on / 依赖: naturality, t.truncGE
-/
lemma truncGEπ_naturality (n : Int) {X Y : C} (f : X ⟶ Y) :
    (t.truncGEπ n).app X ≫ (t.truncGE n).map f = f ≫ (t.truncGEπ n).app Y :=
  ((t.truncGEπ n).naturality f).symm

set_option backward.defeqAttrib.useBackward true in
/--
lemma `isLE_truncLT_obj` / 引理 `isLE_truncLT_obj`

English:
lemma isLE_truncLT_obj
  given: (X : C) (a b : Int) (hn : a <= b + 1 := by lia)
  proof: by
  have : t.IsLE ((t.truncLT a).obj X) (a - 1) := by dsimp [truncLT]; infer_instance
  exact t.isLE_of_le _ (a - 1) _ (by lia)

中文:
引理 isLE_truncLT_obj
  条件: (X : C) (a b : 整数) (hn : a <= b + 1 := by lia)
  证明: by
  have : t.IsLE ((t.truncLT a).obj X) (a - 1) := by dsimp [truncLT]; infer_instance
  exact t.isLE_of_le _ (a - 1) _ (by lia)

Depends on / 依赖: infer_instance, isLE_of_le, t.IsLE, t.isLE_of_le, t.truncLT, truncLT
-/
lemma isLE_truncLT_obj (X : C) (a b : Int) (hn : a <= b + 1 := by lia) :
    t.IsLE ((t.truncLT a).obj X) b := by
  have : t.IsLE ((t.truncLT a).obj X) (a - 1) := by dsimp [truncLT]; infer_instance
  exact t.isLE_of_le _ (a - 1) _ (by lia)

instance (X : C) (n : Int) : t.IsLE ((t.truncLT n).obj X) (n - 1) :=
  t.isLE_truncLT_obj ..

instance (X : C) (n : Int) : t.IsLE ((t.truncLT (n + 1)).obj X) n :=
  t.isLE_truncLT_obj ..

set_option backward.defeqAttrib.useBackward true in
/--
lemma `isGE_truncGE_obj` / 引理 `isGE_truncGE_obj`

English:
lemma isGE_truncGE_obj
  given: (X : C) (a b : Int) (hn : b <= a := by lia)
  proof: by
  have : t.IsGE ((t.truncGE a).obj X) a := by dsimp [truncGE]; infer_instance
  exact t.isGE_of_ge _ _ a (by lia)

中文:
引理 isGE_truncGE_obj
  条件: (X : C) (a b : 整数) (hn : b <= a := by lia)
  证明: by
  have : t.IsGE ((t.truncGE a).obj X) a := by dsimp [truncGE]; infer_instance
  exact t.isGE_of_ge _ _ a (by lia)

Depends on / 依赖: infer_instance, isGE_of_ge, t.IsGE, t.isGE_of_ge, t.truncGE, truncGE
-/
lemma isGE_truncGE_obj (X : C) (a b : Int) (hn : b <= a := by lia) :
    t.IsGE ((t.truncGE a).obj X) b := by
  have : t.IsGE ((t.truncGE a).obj X) a := by dsimp [truncGE]; infer_instance
  exact t.isGE_of_ge _ _ a (by lia)

instance (X : C) (n : Int) : t.IsGE ((t.truncGE n).obj X) n :=
  t.isGE_truncGE_obj ..

/--
Definition of `truncGEδLT` / `truncGEδLT` 的定义

English:
definition truncGEδLT
  signature: (n : Int)
  body: Functor.whiskerLeft (TruncAux.triangleFunctor t n) Triangle.π₃Toπ₁

中文:
定义 truncGEδLT
  签名: (n : 整数)
  定义体: Functor.whiskerLeft (TruncAux.triangleFunctor t n) Triangle.π₃Toπ₁

Depends on / 依赖: Functor, Functor.whiskerLeft, Triangle, TruncAux, TruncAux.triangleFunctor, triangleFunctor, whiskerLeft
-/
noncomputable def truncGEδLT (n : Int) :
    t.truncGE n ⟶ t.truncLT n ⋙ shiftFunctor C (1 : Int) :=
  Functor.whiskerLeft (TruncAux.triangleFunctor t n) Triangle.π₃Toπ₁

/-- The distinguished triangle `(t.truncLT n).obj A ⟶ A ⟶ (t.truncGE n).obj A ⟶ ...`
as a functor `C ⥤ Triangle C` when `t` is a `t`-structure on a pretriangulated
category `C` and `n : ℤ`. -/
@[expose, simps!]
/--
Definition of `triangleLTGE` / `triangleLTGE` 的定义

English:
definition triangleLTGE
  signature: (n : Int)
  body: Triangle.functorMk (t.truncLTι n) (t.truncGEπ n) (t.truncGEδLT n)

中文:
定义 triangleLTGE
  签名: (n : 整数)
  定义体: Triangle.functorMk (t.truncLTι n) (t.truncGEπ n) (t.truncGEδLT n)

Depends on / 依赖: Triangle, Triangle.functorMk, functorMk, t.truncGE, t.truncLT
-/
noncomputable def triangleLTGE (n : Int) : C ⥤ Triangle C :=
  Triangle.functorMk (t.truncLTι n) (t.truncGEπ n) (t.truncGEδLT n)

/--
lemma `triangleLTGE_distinguished` / 引理 `triangleLTGE_distinguished`

English:
lemma triangleLTGE_distinguished
  given: (n : Int) (X : C)
  proof: TruncAux.triangleFunctor_obj_distinguished t n X

中文:
引理 triangleLTGE_distinguished
  条件: (n : 整数) (X : C)
  证明: TruncAux.triangleFunctor_obj_distinguished t n X

Depends on / 依赖: TruncAux, TruncAux.triangleFunctor_obj_distinguished, triangleFunctor_obj_distinguished
-/
lemma triangleLTGE_distinguished (n : Int) (X : C) :
    (t.triangleLTGE n).obj X in distTriang C :=
  TruncAux.triangleFunctor_obj_distinguished t n X

set_option backward.defeqAttrib.useBackward true in
instance (X : C) (n : Int) : t.IsLE ((t.triangleLTGE n).obj X).obj₁ (n - 1) := by
  dsimp
  infer_instance

set_option backward.defeqAttrib.useBackward true in
instance (X : C) (n : Int) : t.IsGE ((t.triangleLTGE n).obj X).obj₃ n := by
  dsimp
  infer_instance

@[reassoc (attr := simp)]
/--
lemma `truncLTι_comp_truncGEπ_app` / 引理 `truncLTι_comp_truncGEπ_app`

English:
lemma truncLTι_comp_truncGEπ_app
  given: (n : Int) (X : C)
  proof: comp_distTriang_mor_zero₁₂ _ (t.triangleLTGE_distinguished n X)

@[reassoc (attr := simp)]

中文:
引理 truncLTι_comp_truncGEπ_app
  条件: (n : 整数) (X : C)
  证明: comp_distTriang_mor_zero₁₂ _ (t.triangleLTGE_distinguished n X)

@[reassoc (attr := simp)]

Depends on / 依赖: t.triangleLTGE_distinguished, triangleLTGE_distinguished
-/
lemma truncLTι_comp_truncGEπ_app (n : Int) (X : C) :
    (t.truncLTι n).app X ≫ (t.truncGEπ n).app X = 0 :=
  comp_distTriang_mor_zero₁₂ _ (t.triangleLTGE_distinguished n X)

@[reassoc (attr := simp)]
/--
lemma `truncGEπ_comp_truncGEδLT_app` / 引理 `truncGEπ_comp_truncGEδLT_app`

English:
lemma truncGEπ_comp_truncGEδLT_app
  given: (n : Int) (X : C)
  proof: comp_distTriang_mor_zero₂₃ _ (t.triangleLTGE_distinguished n X)

@[reassoc (attr := simp)]

中文:
引理 truncGEπ_comp_truncGEδLT_app
  条件: (n : 整数) (X : C)
  证明: comp_distTriang_mor_zero₂₃ _ (t.triangleLTGE_distinguished n X)

@[reassoc (attr := simp)]

Depends on / 依赖: t.triangleLTGE_distinguished, triangleLTGE_distinguished
-/
lemma truncGEπ_comp_truncGEδLT_app (n : Int) (X : C) :
    (t.truncGEπ n).app X ≫ (t.truncGEδLT n).app X = 0 :=
  comp_distTriang_mor_zero₂₃ _ (t.triangleLTGE_distinguished n X)

@[reassoc (attr := simp)]
/--
lemma `truncGEδLT_comp_truncLTι_app` / 引理 `truncGEδLT_comp_truncLTι_app`

English:
lemma truncGEδLT_comp_truncLTι_app
  given: (n : Int) (X : C)
  proof: comp_distTriang_mor_zero₃₁ _ (t.triangleLTGE_distinguished n X)

@[reassoc (attr := simp)]

中文:
引理 truncGEδLT_comp_truncLTι_app
  条件: (n : 整数) (X : C)
  证明: comp_distTriang_mor_zero₃₁ _ (t.triangleLTGE_distinguished n X)

@[reassoc (attr := simp)]

Depends on / 依赖: t.triangleLTGE_distinguished, triangleLTGE_distinguished
-/
lemma truncGEδLT_comp_truncLTι_app (n : Int) (X : C) :
    (t.truncGEδLT n).app X ≫ ((t.truncLTι n).app X)⟦(1 : Int)⟧' = 0 :=
  comp_distTriang_mor_zero₃₁ _ (t.triangleLTGE_distinguished n X)

@[reassoc (attr := simp)]
/--
lemma `truncLTι_comp_truncGEπ` / 引理 `truncLTι_comp_truncGEπ`

English:
lemma truncLTι_comp_truncGEπ
  given: (n : Int)
  proof: by
  cat_disch

@[reassoc (attr := simp)]

中文:
引理 truncLTι_comp_truncGEπ
  条件: (n : 整数)
  证明: by
  cat_disch

@[reassoc (attr := simp)]

Depends on / 依赖: cat_disch
-/
lemma truncLTι_comp_truncGEπ (n : Int) :
    t.truncLTι n ≫ t.truncGEπ n = 0 := by
  cat_disch

@[reassoc (attr := simp)]
/--
lemma `truncGEπ_comp_truncGEδLT` / 引理 `truncGEπ_comp_truncGEδLT`

English:
lemma truncGEπ_comp_truncGEδLT
  given: (n : Int)
  proof: by cat_disch

@[reassoc (attr := simp)]

中文:
引理 truncGEπ_comp_truncGEδLT
  条件: (n : 整数)
  证明: by cat_disch

@[reassoc (attr := simp)]

Depends on / 依赖: cat_disch
-/
lemma truncGEπ_comp_truncGEδLT (n : Int) :
    t.truncGEπ n ≫ t.truncGEδLT n = 0 := by cat_disch

@[reassoc (attr := simp)]
/--
lemma `truncGEδLT_comp_truncLTι` / 引理 `truncGEδLT_comp_truncLTι`

English:
lemma truncGEδLT_comp_truncLTι
  given: (n : Int)
  proof: by
  cat_disch

中文:
引理 truncGEδLT_comp_truncLTι
  条件: (n : 整数)
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
lemma truncGEδLT_comp_truncLTι (n : Int) :
    t.truncGEδLT n ≫ Functor.whiskerRight (t.truncLTι n) (shiftFunctor C (1 : Int)) = 0 := by
  cat_disch

/--
Definition of `natTransTruncLTOfLE` / `natTransTruncLTOfLE` 的定义

English:
definition natTransTruncLTOfLE
  signature: (a b : Int) (h : a <= b)
  body: Functor.whiskerRight (TruncAux.triangleFunctorNatTransOfLE t a b h) Triangle.π₁

中文:
定义 natTransTruncLTOfLE
  签名: (a b : 整数) (h : a <= b)
  定义体: Functor.whiskerRight (TruncAux.triangleFunctorNatTransOfLE t a b h) Triangle.π₁

Depends on / 依赖: Functor, Functor.whiskerRight, Triangle, TruncAux, TruncAux.triangleFunctorNatTransOfLE, triangleFunctorNatTransOfLE, whiskerRight
-/
noncomputable def natTransTruncLTOfLE (a b : Int) (h : a <= b) :
    t.truncLT a ⟶ t.truncLT b :=
  Functor.whiskerRight (TruncAux.triangleFunctorNatTransOfLE t a b h) Triangle.π₁

/--
Definition of `natTransTruncGEOfLE` / `natTransTruncGEOfLE` 的定义

English:
definition natTransTruncGEOfLE
  signature: (a b : Int) (h : a <= b)
  body: Functor.whiskerRight (TruncAux.triangleFunctorNatTransOfLE t a b h) Triangle.π₃

中文:
定义 natTransTruncGEOfLE
  签名: (a b : 整数) (h : a <= b)
  定义体: Functor.whiskerRight (TruncAux.triangleFunctorNatTransOfLE t a b h) Triangle.π₃

Depends on / 依赖: Functor, Functor.whiskerRight, Triangle, TruncAux, TruncAux.triangleFunctorNatTransOfLE, triangleFunctorNatTransOfLE, whiskerRight
-/
noncomputable def natTransTruncGEOfLE (a b : Int) (h : a <= b) :
    t.truncGE a ⟶ t.truncGE b :=
  Functor.whiskerRight (TruncAux.triangleFunctorNatTransOfLE t a b h) Triangle.π₃

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
lemma `natTransTruncLTOfLE_ι_app` / 引理 `natTransTruncLTOfLE_ι_app`

English:
lemma natTransTruncLTOfLE_ι_app
  given: (a b : Int) (h : a <= b) (X : C)
  proof: by
  simpa using! ((TruncAux.triangleFunctorNatTransOfLE t a b h).app X).comm₁.symm

@[reassoc (attr := simp)]

中文:
引理 natTransTruncLTOfLE_ι_app
  条件: (a b : 整数) (h : a <= b) (X : C)
  证明: by
  simpa using! ((TruncAux.triangleFunctorNatTransOfLE t a b h).app X).comm₁.symm

@[reassoc (attr := simp)]

Depends on / 依赖: TruncAux, TruncAux.triangleFunctorNatTransOfLE, triangleFunctorNatTransOfLE
-/
lemma natTransTruncLTOfLE_ι_app (a b : Int) (h : a <= b) (X : C) :
    (t.natTransTruncLTOfLE a b h).app X ≫ (t.truncLTι b).app X = (t.truncLTι a).app X := by
  simpa using! ((TruncAux.triangleFunctorNatTransOfLE t a b h).app X).comm₁.symm

@[reassoc (attr := simp)]
/--
lemma `natTransTruncLTOfLE_ι` / 引理 `natTransTruncLTOfLE_ι`

English:
lemma natTransTruncLTOfLE_ι
  given: (a b : Int) (h : a <= b)
  proof: by
  cat_disch

中文:
引理 natTransTruncLTOfLE_ι
  条件: (a b : 整数) (h : a <= b)
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
lemma natTransTruncLTOfLE_ι (a b : Int) (h : a <= b) :
    t.natTransTruncLTOfLE a b h ≫ t.truncLTι b = t.truncLTι a := by
  cat_disch

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
lemma `π_natTransTruncGEOfLE_app` / 引理 `π_natTransTruncGEOfLE_app`

English:
lemma π_natTransTruncGEOfLE_app
  given: (a b : Int) (h : a <= b) (X : C)
  proof: by
  simpa only [TruncAux.triangleFunctor_obj, TruncAux.triangle_obj₂,
    TruncAux.triangleFunctorNatTransOfLE_app_hom₂, Category.id_comp] using!
    ((TruncAux.triangleFunctorNatTransOfLE t a b h).app X).comm₂

@[reassoc]

中文:
引理 π_natTransTruncGEOfLE_app
  条件: (a b : 整数) (h : a <= b) (X : C)
  证明: by
  simpa only [TruncAux.triangleFunctor_obj, TruncAux.triangle_obj₂,
    TruncAux.triangleFunctorNatTransOfLE_app_hom₂, Category.id_comp] using!
    ((TruncAux.triangleFunctorNatTransOfLE t a b h).app X).comm₂

@[reassoc]

Depends on / 依赖: Category, Category.id_comp, TruncAux, TruncAux.triangleFunctorNatTransOfLE, TruncAux.triangleFunctorNatTransOfLE_app_hom, TruncAux.triangleFunctor_obj, TruncAux.triangle_obj, id_comp, triangleFunctorNatTransOfLE, triangleFunctor_obj
-/
lemma π_natTransTruncGEOfLE_app (a b : Int) (h : a <= b) (X : C) :
    (t.truncGEπ a).app X ≫ (t.natTransTruncGEOfLE a b h).app X = (t.truncGEπ b).app X := by
  simpa only [TruncAux.triangleFunctor_obj, TruncAux.triangle_obj₂,
    TruncAux.triangleFunctorNatTransOfLE_app_hom₂, Category.id_comp] using!
    ((TruncAux.triangleFunctorNatTransOfLE t a b h).app X).comm₂

@[reassoc]
/--
lemma `truncGEδLT_comp_natTransTruncLTOfLE_app` / 引理 `truncGEδLT_comp_natTransTruncLTOfLE_app`

English:
lemma truncGEδLT_comp_natTransTruncLTOfLE_app
  given: (a b : Int) (h : a <= b) (X : C)
  proof: ((TruncAux.triangleFunctorNatTransOfLE t a b h).app X).comm₃

@[reassoc]

中文:
引理 truncGEδLT_comp_natTransTruncLTOfLE_app
  条件: (a b : 整数) (h : a <= b) (X : C)
  证明: ((TruncAux.triangleFunctorNatTransOfLE t a b h).app X).comm₃

@[reassoc]

Depends on / 依赖: TruncAux, TruncAux.triangleFunctorNatTransOfLE, triangleFunctorNatTransOfLE
-/
lemma truncGEδLT_comp_natTransTruncLTOfLE_app (a b : Int) (h : a <= b) (X : C) :
  (t.truncGEδLT a).app X ≫ ((natTransTruncLTOfLE t a b h).app X)⟦(1 : Int)⟧' =
    (t.natTransTruncGEOfLE a b h).app X ≫ (t.truncGEδLT b).app X :=
  ((TruncAux.triangleFunctorNatTransOfLE t a b h).app X).comm₃

@[reassoc]
/--
lemma `truncGEδLT_comp_whiskerRight_natTransTruncLTOfLE` / 引理 `truncGEδLT_comp_whiskerRight_natTransTruncLTOfLE`

English:
lemma truncGEδLT_comp_whiskerRight_natTransTruncLTOfLE
  given: (a b : Int) (h : a <= b)
  proof: by
  ext X
  exact t.truncGEδLT_comp_natTransTruncLTOfLE_app a b h X

@[reassoc (attr := simp)]

中文:
引理 truncGEδLT_comp_whiskerRight_natTransTruncLTOfLE
  条件: (a b : 整数) (h : a <= b)
  证明: by
  ext X
  exact t.truncGEδLT_comp_natTransTruncLTOfLE_app a b h X

@[reassoc (attr := simp)]

Depends on / 依赖: t.truncGE
-/
lemma truncGEδLT_comp_whiskerRight_natTransTruncLTOfLE (a b : Int) (h : a <= b) :
  t.truncGEδLT a ≫ Functor.whiskerRight (natTransTruncLTOfLE t a b h) (shiftFunctor C (1 : Int)) =
    t.natTransTruncGEOfLE a b h ≫ t.truncGEδLT b := by
  ext X
  exact t.truncGEδLT_comp_natTransTruncLTOfLE_app a b h X

@[reassoc (attr := simp)]
/--
lemma `π_natTransTruncGEOfLE` / 引理 `π_natTransTruncGEOfLE`

English:
lemma π_natTransTruncGEOfLE
  given: (a b : Int) (h : a <= b)
  proof: by
  cat_disch

中文:
引理 π_natTransTruncGEOfLE
  条件: (a b : 整数) (h : a <= b)
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
lemma π_natTransTruncGEOfLE (a b : Int) (h : a <= b) :
    t.truncGEπ a ≫ t.natTransTruncGEOfLE a b h = t.truncGEπ b := by
  cat_disch

/--
Definition of `natTransTriangleLTGEOfLE` / `natTransTriangleLTGEOfLE` 的定义

English:
definition natTransTriangleLTGEOfLE
  signature: (a b : Int) (h : a <= b)
  body: Triangle.functorHomMk' (t.natTransTruncLTOfLE a b h) (𝟙 _)
    ((t.natTransTruncGEOfLE a b h)) (by simp) (by simp)
    (t.truncGEδLT_comp_whiskerRight_natTransTruncLTOfLE a b h)

@[simp]

中文:
定义 natTransTriangleLTGEOfLE
  签名: (a b : 整数) (h : a <= b)
  定义体: Triangle.functorHomMk' (t.natTransTruncLTOfLE a b h) (𝟙 _)
    ((t.natTransTruncGEOfLE a b h)) (by simp) (by simp)
    (t.truncGEδLT_comp_whiskerRight_natTransTruncLTOfLE a b h)

@[simp]

Depends on / 依赖: Triangle, Triangle.functorHomMk, functorHomMk, natTransTruncGEOfLE, natTransTruncLTOfLE, t.natTransTruncGEOfLE, t.natTransTruncLTOfLE, t.truncGE
-/
noncomputable def natTransTriangleLTGEOfLE (a b : Int) (h : a <= b) :
    t.triangleLTGE a ⟶ t.triangleLTGE b :=
  Triangle.functorHomMk' (t.natTransTruncLTOfLE a b h) (𝟙 _)
    ((t.natTransTruncGEOfLE a b h)) (by simp) (by simp)
    (t.truncGEδLT_comp_whiskerRight_natTransTruncLTOfLE a b h)

@[simp]
/--
lemma `natTransTriangleLTGEOfLE_refl` / 引理 `natTransTriangleLTGEOfLE_refl`

English:
lemma natTransTriangleLTGEOfLE_refl
  given: (a : Int)
  proof: TruncAux.triangleFunctorNatTransOfLE_refl t a

中文:
引理 natTransTriangleLTGEOfLE_refl
  条件: (a : 整数)
  证明: TruncAux.triangleFunctorNatTransOfLE_refl t a

Depends on / 依赖: TruncAux, TruncAux.triangleFunctorNatTransOfLE_refl, triangleFunctorNatTransOfLE_refl
-/
lemma natTransTriangleLTGEOfLE_refl (a : Int) :
    t.natTransTriangleLTGEOfLE a a (by rfl) = 𝟙 _ :=
  TruncAux.triangleFunctorNatTransOfLE_refl t a

/--
lemma `natTransTriangleLTGEOfLE_trans` / 引理 `natTransTriangleLTGEOfLE_trans`

English:
lemma natTransTriangleLTGEOfLE_trans
  given: (a b c : Int) (hab : a <= b) (hbc : b <= c)
  proof: TruncAux.triangleFunctorNatTransOfLE_trans t a b c hab hbc

@[simp]

中文:
引理 natTransTriangleLTGEOfLE_trans
  条件: (a b c : 整数) (hab : a <= b) (hbc : b <= c)
  证明: TruncAux.triangleFunctorNatTransOfLE_trans t a b c hab hbc

@[simp]

Depends on / 依赖: TruncAux, TruncAux.triangleFunctorNatTransOfLE_trans, triangleFunctorNatTransOfLE_trans
-/
lemma natTransTriangleLTGEOfLE_trans (a b c : Int) (hab : a <= b) (hbc : b <= c) :
    t.natTransTriangleLTGEOfLE a b hab ≫ t.natTransTriangleLTGEOfLE b c hbc =
      t.natTransTriangleLTGEOfLE a c (hab.trans hbc) :=
  TruncAux.triangleFunctorNatTransOfLE_trans t a b c hab hbc

@[simp]
/--
lemma `natTransTruncLTOfLE_refl` / 引理 `natTransTruncLTOfLE_refl`

English:
lemma natTransTruncLTOfLE_refl
  given: (a : Int)
  proof: congr_arg (fun x => Functor.whiskerRight x (Triangle.π₁)) (t.natTransTriangleLTGEOfLE_refl a)

@[simp]

中文:
引理 natTransTruncLTOfLE_refl
  条件: (a : 整数)
  证明: congr_arg (fun x => Functor.whiskerRight x (Triangle.π₁)) (t.natTransTriangleLTGEOfLE_refl a)

@[simp]

Depends on / 依赖: Functor, Functor.whiskerRight, Triangle, congr_arg, natTransTriangleLTGEOfLE_refl, t.natTransTriangleLTGEOfLE_refl, whiskerRight
-/
lemma natTransTruncLTOfLE_refl (a : Int) :
    t.natTransTruncLTOfLE a a (by rfl) = 𝟙 _ :=
  congr_arg (fun x => Functor.whiskerRight x (Triangle.π₁)) (t.natTransTriangleLTGEOfLE_refl a)

@[simp]
/--
lemma `natTransTruncLTOfLE_trans` / 引理 `natTransTruncLTOfLE_trans`

English:
lemma natTransTruncLTOfLE_trans
  given: (a b c : Int) (hab : a <= b) (hbc : b <= c)
  proof: congr_arg (fun x => Functor.whiskerRight x Triangle.π₁)
    (t.natTransTriangleLTGEOfLE_trans a b c hab hbc)

@[simp]

中文:
引理 natTransTruncLTOfLE_trans
  条件: (a b c : 整数) (hab : a <= b) (hbc : b <= c)
  证明: congr_arg (fun x => Functor.whiskerRight x Triangle.π₁)
    (t.natTransTriangleLTGEOfLE_trans a b c hab hbc)

@[simp]

Depends on / 依赖: Functor, Functor.whiskerRight, Triangle, congr_arg, natTransTriangleLTGEOfLE_trans, t.natTransTriangleLTGEOfLE_trans, whiskerRight
-/
lemma natTransTruncLTOfLE_trans (a b c : Int) (hab : a <= b) (hbc : b <= c) :
    t.natTransTruncLTOfLE a b hab ≫ t.natTransTruncLTOfLE b c hbc =
      t.natTransTruncLTOfLE a c (hab.trans hbc) :=
  congr_arg (fun x => Functor.whiskerRight x Triangle.π₁)
    (t.natTransTriangleLTGEOfLE_trans a b c hab hbc)

@[simp]
/--
lemma `natTransTruncGEOfLE_refl` / 引理 `natTransTruncGEOfLE_refl`

English:
lemma natTransTruncGEOfLE_refl
  given: (a : Int)
  proof: congr_arg (fun x => Functor.whiskerRight x (Triangle.π₃)) (t.natTransTriangleLTGEOfLE_refl a)

@[simp]

中文:
引理 natTransTruncGEOfLE_refl
  条件: (a : 整数)
  证明: congr_arg (fun x => Functor.whiskerRight x (Triangle.π₃)) (t.natTransTriangleLTGEOfLE_refl a)

@[simp]

Depends on / 依赖: Functor, Functor.whiskerRight, Triangle, congr_arg, natTransTriangleLTGEOfLE_refl, t.natTransTriangleLTGEOfLE_refl, whiskerRight
-/
lemma natTransTruncGEOfLE_refl (a : Int) :
    t.natTransTruncGEOfLE a a (by rfl) = 𝟙 _ :=
  congr_arg (fun x => Functor.whiskerRight x (Triangle.π₃)) (t.natTransTriangleLTGEOfLE_refl a)

@[simp]
/--
lemma `natTransTruncGEOfLE_trans` / 引理 `natTransTruncGEOfLE_trans`

English:
lemma natTransTruncGEOfLE_trans
  given: (a b c : Int) (hab : a <= b) (hbc : b <= c)
  proof: congr_arg (fun x => Functor.whiskerRight x Triangle.π₃)
    (t.natTransTriangleLTGEOfLE_trans a b c hab hbc)

中文:
引理 natTransTruncGEOfLE_trans
  条件: (a b c : 整数) (hab : a <= b) (hbc : b <= c)
  证明: congr_arg (fun x => Functor.whiskerRight x Triangle.π₃)
    (t.natTransTriangleLTGEOfLE_trans a b c hab hbc)

Depends on / 依赖: Functor, Functor.whiskerRight, Triangle, congr_arg, natTransTriangleLTGEOfLE_trans, t.natTransTriangleLTGEOfLE_trans, whiskerRight
-/
lemma natTransTruncGEOfLE_trans (a b c : Int) (hab : a <= b) (hbc : b <= c) :
    t.natTransTruncGEOfLE a b hab ≫ t.natTransTruncGEOfLE b c hbc =
      t.natTransTruncGEOfLE a c (hab.trans hbc) :=
  congr_arg (fun x => Functor.whiskerRight x Triangle.π₃)
    (t.natTransTriangleLTGEOfLE_trans a b c hab hbc)

/--
lemma `natTransTruncLTOfLE_refl_app` / 引理 `natTransTruncLTOfLE_refl_app`

English:
lemma natTransTruncLTOfLE_refl_app
  given: (a : Int) (X : C)
  proof: congr_app (t.natTransTruncLTOfLE_refl a) X

中文:
引理 natTransTruncLTOfLE_refl_app
  条件: (a : 整数) (X : C)
  证明: congr_app (t.natTransTruncLTOfLE_refl a) X

Depends on / 依赖: congr_app, natTransTruncLTOfLE_refl, t.natTransTruncLTOfLE_refl
-/
lemma natTransTruncLTOfLE_refl_app (a : Int) (X : C) :
    (t.natTransTruncLTOfLE a a (by rfl)).app X = 𝟙 _ :=
  congr_app (t.natTransTruncLTOfLE_refl a) X

/--
lemma `natTransTruncLTOfLE_trans_app` / 引理 `natTransTruncLTOfLE_trans_app`

English:
lemma natTransTruncLTOfLE_trans_app
  given: (a b c : Int) (hab : a <= b) (hbc : b <= c) (X : C)
  proof: congr_app (t.natTransTruncLTOfLE_trans a b c hab hbc) X

中文:
引理 natTransTruncLTOfLE_trans_app
  条件: (a b c : 整数) (hab : a <= b) (hbc : b <= c) (X : C)
  证明: congr_app (t.natTransTruncLTOfLE_trans a b c hab hbc) X

Depends on / 依赖: congr_app, natTransTruncLTOfLE_trans, t.natTransTruncLTOfLE_trans
-/
lemma natTransTruncLTOfLE_trans_app (a b c : Int) (hab : a <= b) (hbc : b <= c) (X : C) :
    (t.natTransTruncLTOfLE a b hab).app X ≫ (t.natTransTruncLTOfLE b c hbc).app X =
      (t.natTransTruncLTOfLE a c (hab.trans hbc)).app X :=
  congr_app (t.natTransTruncLTOfLE_trans a b c hab hbc) X

/--
lemma `natTransTruncGEOfLE_refl_app` / 引理 `natTransTruncGEOfLE_refl_app`

English:
lemma natTransTruncGEOfLE_refl_app
  given: (a : Int) (X : C)
  proof: congr_app (t.natTransTruncGEOfLE_refl a) X

中文:
引理 natTransTruncGEOfLE_refl_app
  条件: (a : 整数) (X : C)
  证明: congr_app (t.natTransTruncGEOfLE_refl a) X

Depends on / 依赖: congr_app, natTransTruncGEOfLE_refl, t.natTransTruncGEOfLE_refl
-/
lemma natTransTruncGEOfLE_refl_app (a : Int) (X : C) :
    (t.natTransTruncGEOfLE a a (by rfl)).app X = 𝟙 _ :=
  congr_app (t.natTransTruncGEOfLE_refl a) X

/--
lemma `natTransTruncGEOfLE_trans_app` / 引理 `natTransTruncGEOfLE_trans_app`

English:
lemma natTransTruncGEOfLE_trans_app
  given: (a b c : Int) (hab : a <= b) (hbc : b <= c) (X : C)
  proof: congr_app (t.natTransTruncGEOfLE_trans a b c hab hbc) X

中文:
引理 natTransTruncGEOfLE_trans_app
  条件: (a b c : 整数) (hab : a <= b) (hbc : b <= c) (X : C)
  证明: congr_app (t.natTransTruncGEOfLE_trans a b c hab hbc) X

Depends on / 依赖: congr_app, natTransTruncGEOfLE_trans, t.natTransTruncGEOfLE_trans
-/
lemma natTransTruncGEOfLE_trans_app (a b c : Int) (hab : a <= b) (hbc : b <= c) (X : C) :
    (t.natTransTruncGEOfLE a b hab).app X ≫ (t.natTransTruncGEOfLE b c hbc).app X =
      (t.natTransTruncGEOfLE a c (hab.trans hbc)).app X :=
  congr_app (t.natTransTruncGEOfLE_trans a b c hab hbc) X

/--
lemma `isLE_of_isZero` / 引理 `isLE_of_isZero`

English:
lemma isLE_of_isZero
  given: {X : C} (hX : IsZero X) (n : Int)
  statement: t.IsLE X n
  proof: t.isLE_of_iso (((t.truncLT (n + 1)).map_isZero hX).isoZero ≪≫ hX.isoZero.symm) n

中文:
引理 isLE_of_isZero
  条件: {X : C} (hX : IsZero X) (n : 整数)
  结论: t.IsLE X n
  证明: t.isLE_of_iso (((t.truncLT (n + 1)).map_isZero hX).isoZero ≪≫ hX.isoZero.symm) n

Depends on / 依赖: hX.isoZero.symm, isLE_of_iso, isoZero, map_isZero, t.isLE_of_iso, t.truncLT, truncLT
-/
lemma isLE_of_isZero {X : C} (hX : IsZero X) (n : Int) : t.IsLE X n :=
  t.isLE_of_iso (((t.truncLT (n + 1)).map_isZero hX).isoZero ≪≫ hX.isoZero.symm) n

/--
lemma `isGE_of_isZero` / 引理 `isGE_of_isZero`

English:
lemma isGE_of_isZero
  given: {X : C} (hX : IsZero X) (n : Int)
  statement: t.IsGE X n
  proof: t.isGE_of_iso (((t.truncGE n).map_isZero hX).isoZero ≪≫ hX.isoZero.symm) n

中文:
引理 isGE_of_isZero
  条件: {X : C} (hX : IsZero X) (n : 整数)
  结论: t.IsGE X n
  证明: t.isGE_of_iso (((t.truncGE n).map_isZero hX).isoZero ≪≫ hX.isoZero.symm) n

Depends on / 依赖: hX.isoZero.symm, isGE_of_iso, isoZero, map_isZero, t.isGE_of_iso, t.truncGE, truncGE
-/
lemma isGE_of_isZero {X : C} (hX : IsZero X) (n : Int) : t.IsGE X n :=
  t.isGE_of_iso (((t.truncGE n).map_isZero hX).isoZero ≪≫ hX.isoZero.symm) n

instance (n : Int) : t.IsLE (0 : C) n := t.isLE_of_isZero (isZero_zero C) n

instance (n : Int) : t.IsGE (0 : C) n := t.isGE_of_isZero (isZero_zero C) n

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `isLE_iff_isIso_truncLTι_app` / 引理 `isLE_iff_isIso_truncLTι_app`

English:
lemma isLE_iff_isIso_truncLTι_app
  given: (n₀ n₁ : Int) (h : n₀ + 1 = n₁) (X : C)
  proof: by
  subst h
  refine ⟨fun _ => ?_,
    fun _ => t.isLE_of_iso (asIso (((t.truncLTι (n₀ + 1))).app X)) n₀⟩
  obtain ⟨e, he⟩ := t.triangle_iso_exists
    (contractible_distinguished X) (t.triangleLTGE_distinguished (n₀ + 1) X)
    (Iso.refl X) n₀ (n₀ + 1)
    (by dsimp; infer_instance) (by dsimp; inf

中文:
引理 isLE_iff_isIso_truncLTι_app
  条件: (n₀ n₁ : 整数) (h : n₀ + 1 = n₁) (X : C)
  证明: by
  subst h
  refine ⟨fun _ => ?_,
    fun _ => t.isLE_of_iso (asIso (((t.truncLTι (n₀ + 1))).app X)) n₀⟩
  obtain ⟨e, he⟩ := t.triangle_iso_exists
    (contractible_distinguished X) (t.triangleLTGE_distinguished (n₀ + 1) X)
    (Iso.refl X) n₀ (n₀ + 1)
    (by dsimp; infer_instance) (by dsimp; inf

Depends on / 依赖: Iso.refl, cancel_mono, contractible_distinguished, e.hom.hom, e.inv.hom, e.inv_hom_id, infer_instance, inv_hom_id, isLE_of_iso, t.isLE_of_iso, t.triangleLTGE_distinguished, t.triangle_iso_exists, t.truncLT, triangleLTGE_distinguished, triangle_iso_exists
-/
lemma isLE_iff_isIso_truncLTι_app (n₀ n₁ : Int) (h : n₀ + 1 = n₁) (X : C) :
    t.IsLE X n₀ ↔ IsIso (((t.truncLTι n₁)).app X) := by
  subst h
  refine ⟨fun _ => ?_,
    fun _ => t.isLE_of_iso (asIso (((t.truncLTι (n₀ + 1))).app X)) n₀⟩
  obtain ⟨e, he⟩ := t.triangle_iso_exists
    (contractible_distinguished X) (t.triangleLTGE_distinguished (n₀ + 1) X)
    (Iso.refl X) n₀ (n₀ + 1)
    (by dsimp; infer_instance) (by dsimp; infer_instance)
    (by dsimp; infer_instance) (by dsimp; infer_instance)
  have he' : e.inv.hom₂ = 𝟙 X := by
    rw [← cancel_mono e.hom.hom₂]; rw [← comp_hom₂]; rw [e.inv_hom_id]; rw [he]
    simp
  have : (t.truncLTι (n₀ + 1)).app X = e.inv.hom₁ := by
    simpa [he'] using e.inv.comm₁
  rw [this]
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `isGE_iff_isIso_truncGEπ_app` / 引理 `isGE_iff_isIso_truncGEπ_app`

English:
lemma isGE_iff_isIso_truncGEπ_app
  given: (n : Int) (X : C)
  proof: by
  constructor
  · intro h
    obtain ⟨e, he⟩ := t.triangle_iso_exists
      (inv_rot_of_distTriang _ (contractible_distinguished X))
      (t.triangleLTGE_distinguished n X) (Iso.refl X) (n - 1) n
      (t.isLE_of_iso (shiftFunctor C (-1 : Int)).mapZeroObject.symm _)
      (by dsimp; infer_instan

中文:
引理 isGE_iff_isIso_truncGEπ_app
  条件: (n : 整数) (X : C)
  证明: by
  constructor
  · intro h
    obtain ⟨e, he⟩ := t.triangle_iso_exists
      (inv_rot_of_distTriang _ (contractible_distinguished X))
      (t.triangleLTGE_distinguished n X) (Iso.refl X) (n - 1) n
      (t.isLE_of_iso (shiftFunctor C (-1 : Int)).mapZeroObject.symm _)
      (by dsimp; infer_instan

Depends on / 依赖: Iso.refl, cancel_epi, contractible_distinguished, e.hom.comm, e.hom.hom, infer_instance, inv_rot_of_distTriang, isLE_of_iso, mapZeroObject, mapZeroObject.symm, shiftFunctor, t.isLE_of_iso, t.triangleLTGE_distinguished, t.triangle_iso_exists, triangleLTGE_distinguished, triangle_iso_exists
-/
lemma isGE_iff_isIso_truncGEπ_app (n : Int) (X : C) :
    t.IsGE X n ↔ IsIso ((t.truncGEπ n).app X) := by
  constructor
  · intro h
    obtain ⟨e, he⟩ := t.triangle_iso_exists
      (inv_rot_of_distTriang _ (contractible_distinguished X))
      (t.triangleLTGE_distinguished n X) (Iso.refl X) (n - 1) n
      (t.isLE_of_iso (shiftFunctor C (-1 : Int)).mapZeroObject.symm _)
      (by dsimp; infer_instance) (by dsimp; infer_instance) (by dsimp; infer_instance)
    dsimp at he
    have : (truncGEπ t n).app X = e.hom.hom₃ := by
      have := e.hom.comm₂
      dsimp at this
      rw [← cancel_epi e.hom.hom₂]; rw [← this]; rw [he]
    rw [this]
    infer_instance
  · intro
    exact t.isGE_of_iso (asIso ((truncGEπ t n).app X)).symm n

instance (X : C) (n : Int) [t.IsGE X n] : IsIso ((t.truncGEπ n).app X) := by
  rw [← isGE_iff_isIso_truncGEπ_app]
  infer_instance

/--
lemma `isGE_iff_isZero_truncLT_obj` / 引理 `isGE_iff_isZero_truncLT_obj`

English:
lemma isGE_iff_isZero_truncLT_obj
  given: (n : Int) (X : C)
  proof: by
  rw [t.isGE_iff_isIso_truncGEπ_app n X]
  exact (Triangle.isZero₁_iff_isIso₂ _ (t.triangleLTGE_distinguished n X)).symm

中文:
引理 isGE_iff_isZero_truncLT_obj
  条件: (n : 整数) (X : C)
  证明: by
  rw [t.isGE_iff_isIso_truncGEπ_app n X]
  exact (Triangle.isZero₁_iff_isIso₂ _ (t.triangleLTGE_distinguished n X)).symm

Depends on / 依赖: Triangle, Triangle.isZero, t.isGE_iff_isIso_truncGE, t.triangleLTGE_distinguished, triangleLTGE_distinguished
-/
lemma isGE_iff_isZero_truncLT_obj (n : Int) (X : C) :
    t.IsGE X n ↔ IsZero ((t.truncLT n).obj X) := by
  rw [t.isGE_iff_isIso_truncGEπ_app n X]
  exact (Triangle.isZero₁_iff_isIso₂ _ (t.triangleLTGE_distinguished n X)).symm

/--
lemma `isLE_iff_isZero_truncGE_obj` / 引理 `isLE_iff_isZero_truncGE_obj`

English:
lemma isLE_iff_isZero_truncGE_obj
  given: (n₀ n₁ : Int) (h : n₀ + 1 = n₁) (X : C)
  proof: by
  rw [t.isLE_iff_isIso_truncLTι_app n₀ n₁ h X]
  exact (Triangle.isZero₃_iff_isIso₁ _ (t.triangleLTGE_distinguished n₁ X)).symm

中文:
引理 isLE_iff_isZero_truncGE_obj
  条件: (n₀ n₁ : 整数) (h : n₀ + 1 = n₁) (X : C)
  证明: by
  rw [t.isLE_iff_isIso_truncLTι_app n₀ n₁ h X]
  exact (Triangle.isZero₃_iff_isIso₁ _ (t.triangleLTGE_distinguished n₁ X)).symm

Depends on / 依赖: Triangle, Triangle.isZero, t.isLE_iff_isIso_truncLT, t.triangleLTGE_distinguished, triangleLTGE_distinguished
-/
lemma isLE_iff_isZero_truncGE_obj (n₀ n₁ : Int) (h : n₀ + 1 = n₁) (X : C) :
    t.IsLE X n₀ ↔ IsZero ((t.truncGE n₁).obj X) := by
  rw [t.isLE_iff_isIso_truncLTι_app n₀ n₁ h X]
  exact (Triangle.isZero₃_iff_isIso₁ _ (t.triangleLTGE_distinguished n₁ X)).symm

/--
lemma `isZero_truncLT_obj_of_isGE` / 引理 `isZero_truncLT_obj_of_isGE`

English:
lemma isZero_truncLT_obj_of_isGE
  given: (n : Int) (X : C) [t.IsGE X n]
  proof: by
  rw [← isGE_iff_isZero_truncLT_obj]
  infer_instance

中文:
引理 isZero_truncLT_obj_of_isGE
  条件: (n : 整数) (X : C) [t.IsGE X n]
  证明: by
  rw [← isGE_iff_isZero_truncLT_obj]
  infer_instance

Depends on / 依赖: infer_instance, isGE_iff_isZero_truncLT_obj
-/
lemma isZero_truncLT_obj_of_isGE (n : Int) (X : C) [t.IsGE X n] :
    IsZero ((t.truncLT n).obj X) := by
  rw [← isGE_iff_isZero_truncLT_obj]
  infer_instance

/--
lemma `isZero_truncGE_obj_of_isLE` / 引理 `isZero_truncGE_obj_of_isLE`

English:
lemma isZero_truncGE_obj_of_isLE
  given: (n₀ n₁ : Int) (h : n₀ + 1 = n₁) (X : C) [t.IsLE X n₀]
  proof: by
  rw [← t.isLE_iff_isZero_truncGE_obj _ _ h X]
  infer_instance

中文:
引理 isZero_truncGE_obj_of_isLE
  条件: (n₀ n₁ : 整数) (h : n₀ + 1 = n₁) (X : C) [t.IsLE X n₀]
  证明: by
  rw [← t.isLE_iff_isZero_truncGE_obj _ _ h X]
  infer_instance

Depends on / 依赖: infer_instance, isLE_iff_isZero_truncGE_obj, t.isLE_iff_isZero_truncGE_obj
-/
lemma isZero_truncGE_obj_of_isLE (n₀ n₁ : Int) (h : n₀ + 1 = n₁) (X : C) [t.IsLE X n₀] :
    IsZero ((t.truncGE n₁).obj X) := by
  rw [← t.isLE_iff_isZero_truncGE_obj _ _ h X]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/--
lemma `from_truncGE_obj_ext` / 引理 `from_truncGE_obj_ext`

English:
lemma from_truncGE_obj_ext
  statement: {n : Int} {X : C} {Y : C}
  proof: by
  suffices forall (f : (t.truncGE n).obj X ⟶ Y), (t.truncGEπ n).app X ≫ f = 0 -> f = 0 by
    rw [← sub_eq_zero]; rw [this (f₁ - f₂) (by cat_disch)]
  intro f hf
  obtain ⟨g, hg⟩ := Triangle.yoneda_exact₃ _
    (t.triangleLTGE_distinguished n X) f hf
  have hg' := t.zero_of_isLE_of_isGE g (n-2) n

中文:
引理 from_truncGE_obj_ext
  结论: {n : 整数} {X : C} {Y : C}
  证明: by
  suffices forall (f : (t.truncGE n).obj X ⟶ Y), (t.truncGEπ n).app X ≫ f = 0 -> f = 0 by
    rw [← sub_eq_zero]; rw [this (f₁ - f₂) (by cat_disch)]
  intro f hf
  obtain ⟨g, hg⟩ := Triangle.yoneda_exact₃ _
    (t.triangleLTGE_distinguished n X) f hf
  have hg' := t.zero_of_isLE_of_isGE g (n-2) n

Depends on / 依赖: Triangle, Triangle.yoneda_exact, cat_disch, comp_zero, isLE_shift, sub_eq_zero, t.isLE_shift, t.triangleLTGE_distinguished, t.truncGE, t.zero_of_isLE_of_isGE, triangleLTGE_distinguished, truncGE, zero_of_isLE_of_isGE
-/
lemma from_truncGE_obj_ext {n : Int} {X : C} {Y : C}
    {f₁ f₂ : (t.truncGE n).obj X ⟶ Y} (h : (t.truncGEπ n).app X ≫ f₁ = (t.truncGEπ n).app X ≫ f₂)
    [t.IsGE Y n] :
    f₁ = f₂ := by
  suffices forall (f : (t.truncGE n).obj X ⟶ Y), (t.truncGEπ n).app X ≫ f = 0 -> f = 0 by
    rw [← sub_eq_zero]; rw [this (f₁ - f₂) (by cat_disch)]
  intro f hf
  obtain ⟨g, hg⟩ := Triangle.yoneda_exact₃ _
    (t.triangleLTGE_distinguished n X) f hf
  have hg' := t.zero_of_isLE_of_isGE g (n-2) n (by lia)
    (by exact t.isLE_shift _ (n-1) 1 (n-2) (by lia)) inferInstance
  rw [hg]; rw [hg']; rw [comp_zero]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `to_truncLT_obj_ext` / 引理 `to_truncLT_obj_ext`

English:
lemma to_truncLT_obj_ext
  statement: {n : Int} {Y : C} {X : C}
  proof: by
  suffices forall (f : Y ⟶ (t.truncLT n).obj X) (_ : f ≫ (t.truncLTι n).app X = 0), f = 0 by
    rw [← sub_eq_zero]; rw [this (f₁ - f₂) (by cat_disch)]
  intro f hf
  obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₂ _ (inv_rot_of_distTriang _
    (t.triangleLTGE_distinguished n X)) f hf
  have hg' := t

中文:
引理 to_truncLT_obj_ext
  结论: {n : 整数} {Y : C} {X : C}
  证明: by
  suffices forall (f : Y ⟶ (t.truncLT n).obj X) (_ : f ≫ (t.truncLTι n).app X = 0), f = 0 by
    rw [← sub_eq_zero]; rw [this (f₁ - f₂) (by cat_disch)]
  intro f hf
  obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₂ _ (inv_rot_of_distTriang _
    (t.triangleLTGE_distinguished n X)) f hf
  have hg' := t

Depends on / 依赖: Triangle, Triangle.coyoneda_exact, cat_disch, inv_rot_of_distTriang, isGE_shift, sub_eq_zero, t.isGE_shift, t.triangleLTGE_distinguished, t.truncLT, t.zero_of_isLE_of_isGE, triangleLTGE_distinguished, truncLT, zero_comp, zero_of_isLE_of_isGE
-/
lemma to_truncLT_obj_ext {n : Int} {Y : C} {X : C}
    {f₁ f₂ : Y ⟶ (t.truncLT n).obj X}
    (h : f₁ ≫ (t.truncLTι n).app X = f₂ ≫ (t.truncLTι n).app X)
    [t.IsLE Y (n - 1)] :
    f₁ = f₂ := by
  suffices forall (f : Y ⟶ (t.truncLT n).obj X) (_ : f ≫ (t.truncLTι n).app X = 0), f = 0 by
    rw [← sub_eq_zero]; rw [this (f₁ - f₂) (by cat_disch)]
  intro f hf
  obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₂ _ (inv_rot_of_distTriang _
    (t.triangleLTGE_distinguished n X)) f hf
  have hg' := t.zero_of_isLE_of_isGE g (n - 1) (n + 1) (by lia) inferInstance
    (by dsimp; apply (t.isGE_shift _ n (-1) (n + 1) (by lia)))
  rw [hg]; rw [hg']; rw [zero_comp]

@[reassoc]
/--
lemma `truncLT_map_truncLTι_app` / 引理 `truncLT_map_truncLTι_app`

English:
lemma truncLT_map_truncLTι_app
  given: (n : Int) (X : C)
  proof: t.to_truncLT_obj_ext (by simp)

@[reassoc]

中文:
引理 truncLT_map_truncLTι_app
  条件: (n : 整数) (X : C)
  证明: t.to_truncLT_obj_ext (by simp)

@[reassoc]

Depends on / 依赖: t.to_truncLT_obj_ext, to_truncLT_obj_ext
-/
lemma truncLT_map_truncLTι_app (n : Int) (X : C) :
    (t.truncLT n).map ((t.truncLTι n).app X) = (t.truncLTι n).app ((t.truncLT n).obj X) :=
  t.to_truncLT_obj_ext (by simp)

@[reassoc]
/--
lemma `truncGE_map_truncGEπ_app` / 引理 `truncGE_map_truncGEπ_app`

English:
lemma truncGE_map_truncGEπ_app
  given: (n : Int) (X : C)
  proof: t.from_truncGE_obj_ext (by simp)

中文:
引理 truncGE_map_truncGEπ_app
  条件: (n : 整数) (X : C)
  证明: t.from_truncGE_obj_ext (by simp)

Depends on / 依赖: from_truncGE_obj_ext, t.from_truncGE_obj_ext
-/
lemma truncGE_map_truncGEπ_app (n : Int) (X : C) :
    (t.truncGE n).map ((t.truncGEπ n).app X) = (t.truncGEπ n).app ((t.truncGE n).obj X) :=
  t.from_truncGE_obj_ext (by simp)

section

variable {X Y : C} (f : X ⟶ Y) (n₀ n₁ : Int) (h : n₀ + 1 = n₁) [t.IsLE X n₀]

set_option backward.defeqAttrib.useBackward true in
include h in
/--
lemma `liftTruncLT_aux` / 引理 `liftTruncLT_aux`

English:
lemma liftTruncLT_aux
  proof: Triangle.coyoneda_exact₂ _ (t.triangleLTGE_distinguished n₁ Y) f
    (t.zero_of_isLE_of_isGE _ n₀ n₁ (by lia) inferInstance (by dsimp; infer_instance))

中文:
引理 liftTruncLT_aux
  证明: Triangle.coyoneda_exact₂ _ (t.triangleLTGE_distinguished n₁ Y) f
    (t.zero_of_isLE_of_isGE _ n₀ n₁ (by lia) inferInstance (by dsimp; infer_instance))

Depends on / 依赖: Triangle, Triangle.coyoneda_exact, infer_instance, t.triangleLTGE_distinguished, t.zero_of_isLE_of_isGE, triangleLTGE_distinguished, zero_of_isLE_of_isGE
-/
lemma liftTruncLT_aux :
    exists (f' : X ⟶ (t.truncLT n₁).obj Y), f = f' ≫ (t.truncLTι n₁).app Y :=
  Triangle.coyoneda_exact₂ _ (t.triangleLTGE_distinguished n₁ Y) f
    (t.zero_of_isLE_of_isGE _ n₀ n₁ (by lia) inferInstance (by dsimp; infer_instance))

/--
Definition of `liftTruncLT` / `liftTruncLT` 的定义

English:
definition liftTruncLT
  signature: {X Y : C} (f : X ⟶ Y) (n₀ n₁ : Int) (h : n₀ + 1 = n₁) [t.IsLE X n₀]
  body: (t.liftTruncLT_aux f n₀ n₁ h).choose

@[reassoc (attr := simp)]

中文:
定义 liftTruncLT
  签名: {X Y : C} (f : X ⟶ Y) (n₀ n₁ : 整数) (h : n₀ + 1 = n₁) [t.IsLE X n₀]
  定义体: (t.liftTruncLT_aux f n₀ n₁ h).choose

@[reassoc (attr := simp)]

Depends on / 依赖: liftTruncLT_aux, t.liftTruncLT_aux
-/
noncomputable def liftTruncLT {X Y : C} (f : X ⟶ Y) (n₀ n₁ : Int) (h : n₀ + 1 = n₁) [t.IsLE X n₀] :
    X ⟶ (t.truncLT n₁).obj Y :=
  (t.liftTruncLT_aux f n₀ n₁ h).choose

@[reassoc (attr := simp)]
/--
lemma `liftTruncLT_ι` / 引理 `liftTruncLT_ι`

English:
lemma liftTruncLT_ι
  given: {X Y : C} (f : X ⟶ Y) (n₀ n₁ : Int) (h : n₀ + 1 = n₁) [t.IsLE X n₀]
  proof: (t.liftTruncLT_aux f n₀ n₁ h).choose_spec.symm

中文:
引理 liftTruncLT_ι
  条件: {X Y : C} (f : X ⟶ Y) (n₀ n₁ : 整数) (h : n₀ + 1 = n₁) [t.IsLE X n₀]
  证明: (t.liftTruncLT_aux f n₀ n₁ h).choose_spec.symm

Depends on / 依赖: choose_spec, choose_spec.symm, liftTruncLT_aux, t.liftTruncLT_aux
-/
lemma liftTruncLT_ι {X Y : C} (f : X ⟶ Y) (n₀ n₁ : Int) (h : n₀ + 1 = n₁) [t.IsLE X n₀] :
    t.liftTruncLT f n₀ n₁ h ≫ (t.truncLTι n₁).app Y = f :=
  (t.liftTruncLT_aux f n₀ n₁ h).choose_spec.symm

end

section

variable {X Y : C} (f : X ⟶ Y) (n : Int) [t.IsGE Y n]

set_option backward.defeqAttrib.useBackward true in
/--
lemma `descTruncGE_aux` / 引理 `descTruncGE_aux`

English:
lemma descTruncGE_aux
  proof: Triangle.yoneda_exact₂ _ (t.triangleLTGE_distinguished n X) f
    (t.zero_of_isLE_of_isGE _ (n-1) n (by lia) (by dsimp; infer_instance) inferInstance)

中文:
引理 descTruncGE_aux
  证明: Triangle.yoneda_exact₂ _ (t.triangleLTGE_distinguished n X) f
    (t.zero_of_isLE_of_isGE _ (n-1) n (by lia) (by dsimp; infer_instance) inferInstance)

Depends on / 依赖: Triangle, Triangle.yoneda_exact, infer_instance, t.triangleLTGE_distinguished, t.zero_of_isLE_of_isGE, triangleLTGE_distinguished, zero_of_isLE_of_isGE
-/
lemma descTruncGE_aux :
  exists (f' : (t.truncGE n).obj X ⟶ Y), f = (t.truncGEπ n).app X ≫ f' :=
  Triangle.yoneda_exact₂ _ (t.triangleLTGE_distinguished n X) f
    (t.zero_of_isLE_of_isGE _ (n-1) n (by lia) (by dsimp; infer_instance) inferInstance)

/--
Definition of `descTruncGE` / `descTruncGE` 的定义

English:
definition descTruncGE
  signature: :
  body: (t.descTruncGE_aux f n).choose

@[reassoc (attr := simp)]

中文:
定义 descTruncGE
  签名: :
  定义体: (t.descTruncGE_aux f n).choose

@[reassoc (attr := simp)]

Depends on / 依赖: descTruncGE_aux, t.descTruncGE_aux
-/
noncomputable def descTruncGE :
    (t.truncGE n).obj X ⟶ Y :=
  (t.descTruncGE_aux f n).choose

@[reassoc (attr := simp)]
/--
lemma `π_descTruncGE` / 引理 `π_descTruncGE`

English:
lemma π_descTruncGE
  given: {X Y : C} (f : X ⟶ Y) (n : Int) [t.IsGE Y n]
  proof: (t.descTruncGE_aux f n).choose_spec.symm

中文:
引理 π_descTruncGE
  条件: {X Y : C} (f : X ⟶ Y) (n : 整数) [t.IsGE Y n]
  证明: (t.descTruncGE_aux f n).choose_spec.symm

Depends on / 依赖: choose_spec, choose_spec.symm, descTruncGE_aux, t.descTruncGE_aux
-/
lemma π_descTruncGE {X Y : C} (f : X ⟶ Y) (n : Int) [t.IsGE Y n] :
    (t.truncGEπ n).app X ≫ t.descTruncGE f n = f :=
  (t.descTruncGE_aux f n).choose_spec.symm

end

/--
lemma `isLE_iff_orthogonal` / 引理 `isLE_iff_orthogonal`

English:
lemma isLE_iff_orthogonal
  given: (n₀ n₁ : Int) (h : n₀ + 1 = n₁) (X : C)
  proof: by
  refine ⟨fun _ Y f _ => t.zero f n₀ n₁ (by lia), fun hX => ?_⟩
  rw [t.isLE_iff_isZero_truncGE_obj n₀ n₁ h]; rw [IsZero.iff_id_eq_zero]
  exact t.from_truncGE_obj_ext (by simpa using hX _ _ inferInstance)

中文:
引理 isLE_iff_orthogonal
  条件: (n₀ n₁ : 整数) (h : n₀ + 1 = n₁) (X : C)
  证明: by
  refine ⟨fun _ Y f _ => t.zero f n₀ n₁ (by lia), fun hX => ?_⟩
  rw [t.isLE_iff_isZero_truncGE_obj n₀ n₁ h]; rw [IsZero.iff_id_eq_zero]
  exact t.from_truncGE_obj_ext (by simpa using hX _ _ inferInstance)

Depends on / 依赖: IsZero, IsZero.iff_id_eq_zero, from_truncGE_obj_ext, iff_id_eq_zero, isLE_iff_isZero_truncGE_obj, t.from_truncGE_obj_ext, t.isLE_iff_isZero_truncGE_obj, t.zero
-/
lemma isLE_iff_orthogonal (n₀ n₁ : Int) (h : n₀ + 1 = n₁) (X : C) :
    t.IsLE X n₀ ↔ forall (Y : C) (f : X ⟶ Y) (_ : t.IsGE Y n₁), f = 0 := by
  refine ⟨fun _ Y f _ => t.zero f n₀ n₁ (by lia), fun hX => ?_⟩
  rw [t.isLE_iff_isZero_truncGE_obj n₀ n₁ h]; rw [IsZero.iff_id_eq_zero]
  exact t.from_truncGE_obj_ext (by simpa using hX _ _ inferInstance)

/--
lemma `isGE_iff_orthogonal` / 引理 `isGE_iff_orthogonal`

English:
lemma isGE_iff_orthogonal
  given: (n₀ n₁ : Int) (h : n₀ + 1 = n₁) (X : C)
  proof: by
  refine ⟨fun _ Y f _ => t.zero f n₀ n₁ (by lia), fun hX => ?_⟩
  rw [t.isGE_iff_isZero_truncLT_obj n₁ X]; rw [IsZero.iff_id_eq_zero]
  exact t.to_truncLT_obj_ext (by simpa using hX _ _ (by rw [← h]; infer_instance))

中文:
引理 isGE_iff_orthogonal
  条件: (n₀ n₁ : 整数) (h : n₀ + 1 = n₁) (X : C)
  证明: by
  refine ⟨fun _ Y f _ => t.zero f n₀ n₁ (by lia), fun hX => ?_⟩
  rw [t.isGE_iff_isZero_truncLT_obj n₁ X]; rw [IsZero.iff_id_eq_zero]
  exact t.to_truncLT_obj_ext (by simpa using hX _ _ (by rw [← h]; infer_instance))

Depends on / 依赖: IsZero, IsZero.iff_id_eq_zero, iff_id_eq_zero, infer_instance, isGE_iff_isZero_truncLT_obj, t.isGE_iff_isZero_truncLT_obj, t.to_truncLT_obj_ext, t.zero, to_truncLT_obj_ext
-/
lemma isGE_iff_orthogonal (n₀ n₁ : Int) (h : n₀ + 1 = n₁) (X : C) :
    t.IsGE X n₁ ↔ forall (Y : C) (f : Y ⟶ X) (_ : t.IsLE Y n₀), f = 0 := by
  refine ⟨fun _ Y f _ => t.zero f n₀ n₁ (by lia), fun hX => ?_⟩
  rw [t.isGE_iff_isZero_truncLT_obj n₁ X]; rw [IsZero.iff_id_eq_zero]
  exact t.to_truncLT_obj_ext (by simpa using hX _ _ (by rw [← h]; infer_instance))

/--
lemma `isLE₂` / 引理 `isLE₂`

English:
lemma isLE₂
  statement: (T : Triangle C) (hT : T in distTriang C) (n : Int) (h₁ : t.IsLE T.obj₁ n)
  proof: by
  rw [t.isLE_iff_orthogonal n (n + 1) rfl]
  intro Y f hY
  obtain ⟨f', hf'⟩ := Triangle.yoneda_exact₂ _ hT f
    (t.zero _ n (n + 1) (by lia))
  rw [hf']; rw [t.zero f' n (n + 1) (by lia)]; rw [comp_zero]

中文:
引理 isLE₂
  结论: (T : Triangle C) (hT : T in distTriang C) (n : 整数) (h₁ : t.IsLE T.obj₁ n)
  证明: by
  rw [t.isLE_iff_orthogonal n (n + 1) rfl]
  intro Y f hY
  obtain ⟨f', hf'⟩ := Triangle.yoneda_exact₂ _ hT f
    (t.zero _ n (n + 1) (by lia))
  rw [hf']; rw [t.zero f' n (n + 1) (by lia)]; rw [comp_zero]

Depends on / 依赖: Triangle, Triangle.yoneda_exact, comp_zero, isLE_iff_orthogonal, t.isLE_iff_orthogonal, t.zero
-/
lemma isLE₂ (T : Triangle C) (hT : T in distTriang C) (n : Int) (h₁ : t.IsLE T.obj₁ n)
    (h₃ : t.IsLE T.obj₃ n) : t.IsLE T.obj₂ n := by
  rw [t.isLE_iff_orthogonal n (n + 1) rfl]
  intro Y f hY
  obtain ⟨f', hf'⟩ := Triangle.yoneda_exact₂ _ hT f
    (t.zero _ n (n + 1) (by lia))
  rw [hf']; rw [t.zero f' n (n + 1) (by lia)]; rw [comp_zero]

/--
lemma `isGE₂` / 引理 `isGE₂`

English:
lemma isGE₂
  statement: (T : Triangle C) (hT : T in distTriang C) (n : Int) (h₁ : t.IsGE T.obj₁ n)
  proof: by
  rw [t.isGE_iff_orthogonal (n-1) n (by lia)]
  intro Y f hY
  obtain ⟨f', hf'⟩ := Triangle.coyoneda_exact₂ _ hT f (t.zero _ (n-1) n (by lia))
  rw [hf']; rw [t.zero f' (n-1) n (by lia)]; rw [zero_comp]

中文:
引理 isGE₂
  结论: (T : Triangle C) (hT : T in distTriang C) (n : 整数) (h₁ : t.IsGE T.obj₁ n)
  证明: by
  rw [t.isGE_iff_orthogonal (n-1) n (by lia)]
  intro Y f hY
  obtain ⟨f', hf'⟩ := Triangle.coyoneda_exact₂ _ hT f (t.zero _ (n-1) n (by lia))
  rw [hf']; rw [t.zero f' (n-1) n (by lia)]; rw [zero_comp]

Depends on / 依赖: Triangle, Triangle.coyoneda_exact, isGE_iff_orthogonal, t.isGE_iff_orthogonal, t.zero, zero_comp
-/
lemma isGE₂ (T : Triangle C) (hT : T in distTriang C) (n : Int) (h₁ : t.IsGE T.obj₁ n)
    (h₃ : t.IsGE T.obj₃ n) : t.IsGE T.obj₂ n := by
  rw [t.isGE_iff_orthogonal (n-1) n (by lia)]
  intro Y f hY
  obtain ⟨f', hf'⟩ := Triangle.coyoneda_exact₂ _ hT f (t.zero _ (n-1) n (by lia))
  rw [hf']; rw [t.zero f' (n-1) n (by lia)]; rw [zero_comp]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: t.minus.IsTriangulated
  body: ⟨0, isZero_zero C, 0, inferInstance⟩
  toIsTriangulatedClosed₂ := .mk' (fun T hT => by
    rintro ⟨i₁, hi₁⟩ ⟨i₃, hi₃⟩
    exact ⟨max i₁ i₃, t.isLE₂ T hT _ (t.isLE_of_le _ _ _ (le_max_left i₁ i₃))
      (t.isLE_of_le _ _ _ (le_max_right i₁ i₃))⟩)

中文:
实例 :
  签名: t.minus.IsTriangulated
  定义体: ⟨0, isZero_zero C, 0, inferInstance⟩
  toIsTriangulatedClosed₂ := .mk' (fun T hT => by
    rintro ⟨i₁, hi₁⟩ ⟨i₃, hi₃⟩
    exact ⟨max i₁ i₃, t.isLE₂ T hT _ (t.isLE_of_le _ _ _ (le_max_left i₁ i₃))
      (t.isLE_of_le _ _ _ (le_max_right i₁ i₃))⟩)

Depends on / 依赖: isZero_zero
-/
instance : t.minus.IsTriangulated where
  exists_zero := ⟨0, isZero_zero C, 0, inferInstance⟩
  toIsTriangulatedClosed₂ := .mk' (fun T hT => by
    rintro ⟨i₁, hi₁⟩ ⟨i₃, hi₃⟩
    exact ⟨max i₁ i₃, t.isLE₂ T hT _ (t.isLE_of_le _ _ _ (le_max_left i₁ i₃))
      (t.isLE_of_le _ _ _ (le_max_right i₁ i₃))⟩)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: t.plus.IsTriangulated
  body: ⟨0, isZero_zero C, 0, inferInstance⟩
  toIsTriangulatedClosed₂ := .mk' (fun T hT => by
    rintro ⟨i₁, hi₁⟩ ⟨i₃, hi₃⟩
    exact ⟨min i₁ i₃, t.isGE₂ T hT _ (t.isGE_of_ge _ _ _ (min_le_left i₁ i₃))
      (t.isGE_of_ge _ _ _ (min_le_right i₁ i₃))⟩)

中文:
实例 :
  签名: t.plus.IsTriangulated
  定义体: ⟨0, isZero_zero C, 0, inferInstance⟩
  toIsTriangulatedClosed₂ := .mk' (fun T hT => by
    rintro ⟨i₁, hi₁⟩ ⟨i₃, hi₃⟩
    exact ⟨min i₁ i₃, t.isGE₂ T hT _ (t.isGE_of_ge _ _ _ (min_le_left i₁ i₃))
      (t.isGE_of_ge _ _ _ (min_le_right i₁ i₃))⟩)

Depends on / 依赖: isZero_zero
-/
instance : t.plus.IsTriangulated where
  exists_zero := ⟨0, isZero_zero C, 0, inferInstance⟩
  toIsTriangulatedClosed₂ := .mk' (fun T hT => by
    rintro ⟨i₁, hi₁⟩ ⟨i₃, hi₃⟩
    exact ⟨min i₁ i₃, t.isGE₂ T hT _ (t.isGE_of_ge _ _ _ (min_le_left i₁ i₃))
      (t.isGE_of_ge _ _ _ (min_le_right i₁ i₃))⟩)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: t.bounded.IsTriangulated
  body: by
  dsimp [bounded]
  infer_instance

中文:
实例 :
  签名: t.bounded.IsTriangulated
  定义体: by
  dsimp [bounded]
  infer_instance

Depends on / 依赖: bounded, infer_instance
-/
instance : t.bounded.IsTriangulated := by
  dsimp [bounded]
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `isIso_truncLT_map_iff` / 引理 `isIso_truncLT_map_iff`

English:
lemma isIso_truncLT_map_iff
  given: {X Y : C} (f : X ⟶ Y) (n : Int)
  proof: by
  refine ⟨fun hf => ?_, fun ⟨Z, g, h, mem, _⟩ => ?_⟩
  · refine ⟨(t.truncGE n).obj Y, (t.truncGEπ n).app Y,
      (t.truncGEδLT n).app Y ≫ (inv ((t.truncLT n).map f))⟦1⟧',
      isomorphic_distinguished _ (t.triangleLTGE_distinguished n Y) _ ?_, inferInstance⟩
    exact Triangle.isoMk _ _ (asIso 

中文:
引理 isIso_truncLT_map_iff
  条件: {X Y : C} (f : X ⟶ Y) (n : 整数)
  证明: by
  refine ⟨fun hf => ?_, fun ⟨Z, g, h, mem, _⟩ => ?_⟩
  · refine ⟨(t.truncGE n).obj Y, (t.truncGEπ n).app Y,
      (t.truncGEδLT n).app Y ≫ (inv ((t.truncLT n).map f))⟦1⟧',
      isomorphic_distinguished _ (t.triangleLTGE_distinguished n Y) _ ?_, inferInstance⟩
    exact Triangle.isoMk _ _ (asIso 

Depends on / 依赖: Iso.refl, Triangle, Triangle.isoMk, infer_instance, isomorphic_distinguished, t.triangleLTGE_distinguished, t.triangle_iso_exists, t.truncGE, t.truncLT, triangleLTGE_distinguished, triangle_iso_exists, truncGE, truncLT
-/
lemma isIso_truncLT_map_iff {X Y : C} (f : X ⟶ Y) (n : Int) :
    IsIso ((t.truncLT n).map f) ↔
      exists (Z : C) (g : Y ⟶ Z) (h : Z ⟶ ((t.truncLT n).obj X)⟦1⟧)
        (_ : Triangle.mk ((t.truncLTι n).app X ≫ f) g h in distTriang _), t.IsGE Z n := by
  refine ⟨fun hf => ?_, fun ⟨Z, g, h, mem, _⟩ => ?_⟩
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
/--
lemma `isIso_truncGE_map_iff` / 引理 `isIso_truncGE_map_iff`

English:
lemma isIso_truncGE_map_iff
  given: {Y Z : C} (g : Y ⟶ Z) (n₀ n₁ : Int) (hn : n₀ + 1 = n₁)
  proof: by
  refine ⟨fun hf => ?_, fun ⟨X, f, h, mem, _⟩ => ?_⟩
  · refine ⟨_, (t.truncLTι n₁).app Y, inv ((t.truncGE n₁).map g) ≫ (t.truncGEδLT n₁).app Y,
      isomorphic_distinguished _ (t.triangleLTGE_distinguished n₁ Y) _ ?_,
      by subst hn; infer_instance⟩
    exact Iso.symm (Triangle.isoMk _ _ (Is

中文:
引理 isIso_truncGE_map_iff
  条件: {Y Z : C} (g : Y ⟶ Z) (n₀ n₁ : 整数) (hn : n₀ + 1 = n₁)
  证明: by
  refine ⟨fun hf => ?_, fun ⟨X, f, h, mem, _⟩ => ?_⟩
  · refine ⟨_, (t.truncLTι n₁).app Y, inv ((t.truncGE n₁).map g) ≫ (t.truncGEδLT n₁).app Y,
      isomorphic_distinguished _ (t.triangleLTGE_distinguished n₁ Y) _ ?_,
      by subst hn; infer_instance⟩
    exact Iso.symm (Triangle.isoMk _ _ (Is

Depends on / 依赖: Iso.refl, Iso.symm, Triangle, Triangle.isoMk, infer_instan, infer_instance, isomorphic_distinguished, t.triangleLTGE_distinguished, t.triangle_iso_exists, t.truncGE, t.truncLT, triangleLTGE_distinguished, triangle_iso_exists, truncGE
-/
lemma isIso_truncGE_map_iff {Y Z : C} (g : Y ⟶ Z) (n₀ n₁ : Int) (hn : n₀ + 1 = n₁) :
    IsIso ((t.truncGE n₁).map g) ↔
      exists (X : C) (f : X ⟶ Y) (h : ((t.truncGE n₁).obj Z) ⟶ X⟦(1 : Int)⟧)
        (_ : Triangle.mk f (g ≫ (t.truncGEπ n₁).app Z) h in distTriang _), t.IsLE X n₀ := by
  refine ⟨fun hf => ?_, fun ⟨X, f, h, mem, _⟩ => ?_⟩
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

instance (X : C) (a b : Int) [t.IsLE X b] : t.IsLE ((t.truncLT a).obj X) b := by
  by_cases h : a <= b + 1
  · exact t.isLE_truncLT_obj ..
  · have := (t.isLE_iff_isIso_truncLTι_app (a - 1) a (by lia) X).1 (t.isLE_of_le _ b _ (by lia))
    exact t.isLE_of_iso (show X ≅ _ from (asIso ((t.truncLTι a).app X)).symm) _

instance (X : C) (a b : Int) [t.IsGE X a] : t.IsGE ((t.truncGE b).obj X) a := by
  by_cases h : a <= b
  · exact t.isGE_truncGE_obj ..
  · have : t.IsGE X b := t.isGE_of_ge X b a (by lia)
    exact t.isGE_of_iso (show X ≅ _ from asIso ((t.truncGEπ b).app X)) _

/--
Definition of `truncGELT` / `truncGELT` 的定义

English:
abbreviation truncGELT
  signature: (a b : Int)
  body: t.truncLT b ⋙ t.truncGE a

中文:
缩写 truncGELT
  签名: (a b : 整数)
  定义体: t.truncLT b ⋙ t.truncGE a

Depends on / 依赖: t.truncGE, t.truncLT, truncGE, truncLT
-/
noncomputable abbrev truncGELT (a b : Int) : C ⥤ C := t.truncLT b ⋙ t.truncGE a

/--
Definition of `truncLTGE` / `truncLTGE` 的定义

English:
abbreviation truncLTGE
  signature: (a b : Int)
  body: t.truncGE a ⋙ t.truncLT b

中文:
缩写 truncLTGE
  签名: (a b : 整数)
  定义体: t.truncGE a ⋙ t.truncLT b

Depends on / 依赖: t.truncGE, t.truncLT, truncGE, truncLT
-/
noncomputable abbrev truncLTGE (a b : Int) : C ⥤ C := t.truncGE a ⋙ t.truncLT b

set_option backward.defeqAttrib.useBackward true in
instance (X : C) (a b : Int) : t.IsGE ((t.truncGELT a b).obj X) a := by
  dsimp; infer_instance

set_option backward.defeqAttrib.useBackward true in
instance (X : C) (a b : Int) : t.IsLE ((t.truncLTGE a b).obj X) (b - 1) := by
  dsimp; infer_instance

section

variable [IsTriangulated C]

set_option backward.defeqAttrib.useBackward true in
/--
lemma `isIso₁_truncLT_map_of_isGE` / 引理 `isIso₁_truncLT_map_of_isGE`

English:
lemma isIso₁_truncLT_map_of_isGE
  statement: (T : Triangle C) (hT : T in distTriang C)
  proof: by
  rw [isIso_truncLT_map_iff]
  obtain ⟨Z, g, k, mem⟩ := distinguished_cocone_triangle ((t.truncLTι n).app T.obj₁ ≫ T.mor₁)
  refine ⟨_, _, _, mem, ?_⟩
  let H := someOctahedron rfl (t.triangleLTGE_distinguished n T.obj₁) hT mem
  exact t.isGE₂ _ H.mem n (by dsimp; infer_instance) (by dsimp; infer

中文:
引理 isIso₁_truncLT_map_of_isGE
  结论: (T : Triangle C) (hT : T in distTriang C)
  证明: by
  rw [isIso_truncLT_map_iff]
  obtain ⟨Z, g, k, mem⟩ := distinguished_cocone_triangle ((t.truncLTι n).app T.obj₁ ≫ T.mor₁)
  refine ⟨_, _, _, mem, ?_⟩
  let H := someOctahedron rfl (t.triangleLTGE_distinguished n T.obj₁) hT mem
  exact t.isGE₂ _ H.mem n (by dsimp; infer_instance) (by dsimp; infer

Depends on / 依赖: H.mem, T.mor, T.obj, distinguished_cocone_triangle, infer_instance, isIso_truncLT_map_iff, someOctahedron, t.isGE, t.triangleLTGE_distinguished, t.truncLT, triangleLTGE_distinguished
-/
lemma isIso₁_truncLT_map_of_isGE (T : Triangle C) (hT : T in distTriang C)
    (n : Int) (h₃ : t.IsGE T.obj₃ n) :
    IsIso ((t.truncLT n).map T.mor₁) := by
  rw [isIso_truncLT_map_iff]
  obtain ⟨Z, g, k, mem⟩ := distinguished_cocone_triangle ((t.truncLTι n).app T.obj₁ ≫ T.mor₁)
  refine ⟨_, _, _, mem, ?_⟩
  let H := someOctahedron rfl (t.triangleLTGE_distinguished n T.obj₁) hT mem
  exact t.isGE₂ _ H.mem n (by dsimp; infer_instance) (by dsimp; infer_instance)

/--
lemma `isIso₂_truncGE_map_of_isLE` / 引理 `isIso₂_truncGE_map_of_isLE`

English:
lemma isIso₂_truncGE_map_of_isLE
  statement: (T : Triangle C) (hT : T in distTriang C)
  proof: by
  rw [isIso_truncGE_map_iff _ _ _ _ h]
  obtain ⟨X, f, k, mem⟩ := distinguished_cocone_triangle₁ (T.mor₂ ≫ (t.truncGEπ n₁).app T.obj₃)
  refine ⟨_, _, _, mem, ?_⟩
  subst h
  have H := someOctahedron rfl (rot_of_distTriang _ hT)
    (rot_of_distTriang _ (t.triangleLTGE_distinguished (n₀ + 1) T.ob

中文:
引理 isIso₂_truncGE_map_of_isLE
  结论: (T : Triangle C) (hT : T in distTriang C)
  证明: by
  rw [isIso_truncGE_map_iff _ _ _ _ h]
  obtain ⟨X, f, k, mem⟩ := distinguished_cocone_triangle₁ (T.mor₂ ≫ (t.truncGEπ n₁).app T.obj₃)
  refine ⟨_, _, _, mem, ?_⟩
  subst h
  have H := someOctahedron rfl (rot_of_distTriang _ hT)
    (rot_of_distTriang _ (t.triangleLTGE_distinguished (n₀ + 1) T.ob

Depends on / 依赖: H.mem, T.mor, T.obj, isIso_truncGE_map_iff, isLE_shift, rot_of_distTriang, someOctahedron, t.IsLE, t.isLE, t.isLE_shift, t.triangleLTGE_distinguished, t.truncGE, t.truncLT, triangleLTGE_distinguished, truncLT
-/
lemma isIso₂_truncGE_map_of_isLE (T : Triangle C) (hT : T in distTriang C)
    (n₀ n₁ : Int) (h : n₀ + 1 = n₁) (h₁ : t.IsLE T.obj₁ n₀) :
    IsIso ((t.truncGE n₁).map T.mor₂) := by
  rw [isIso_truncGE_map_iff _ _ _ _ h]
  obtain ⟨X, f, k, mem⟩ := distinguished_cocone_triangle₁ (T.mor₂ ≫ (t.truncGEπ n₁).app T.obj₃)
  refine ⟨_, _, _, mem, ?_⟩
  subst h
  have H := someOctahedron rfl (rot_of_distTriang _ hT)
    (rot_of_distTriang _ (t.triangleLTGE_distinguished (n₀ + 1) T.obj₃))
    (rot_of_distTriang _ mem)
  have : t.IsLE (X⟦(1 : Int)⟧) (n₀ - 1) :=
    t.isLE₂ _ H.mem (n₀ - 1) (t.isLE_shift T.obj₁ n₀ 1 (n₀ - 1) (by lia))
      (t.isLE_shift ((t.truncLT (n₀ + 1)).obj T.obj₃) n₀ 1 (n₀-1) (by lia))
  exact t.isLE_of_shift X n₀ 1 (n₀ - 1) (by lia)

set_option backward.defeqAttrib.useBackward true in
instance (X : C) (a b : Int) [t.IsGE X a] :
    t.IsGE ((t.truncLT b).obj X) a := by
  rw [t.isGE_iff_isZero_truncLT_obj]
  have := t.isIso₁_truncLT_map_of_isGE _ ((t.triangleLTGE_distinguished b X)) a
    (by dsimp; infer_instance)
  dsimp at this
  refine IsZero.of_iso ?_ (asIso ((t.truncLT a).map ((t.truncLTι b).app X)))
  rwa [← isGE_iff_isZero_truncLT_obj]

set_option backward.defeqAttrib.useBackward true in
instance (X : C) (a b : Int) [t.IsLE X b] : t.IsLE ((t.truncGE a).obj X) b := by
  rw [t.isLE_iff_isZero_truncGE_obj b (b + 1) rfl]
  have := t.isIso₂_truncGE_map_of_isLE _ (t.triangleLTGE_distinguished a X) b _ rfl
    (by dsimp; infer_instance)
  dsimp at this
  refine IsZero.of_iso ?_ (asIso ((t.truncGE (b + 1)).map ((t.truncGEπ a).app X))).symm
  rwa [← isLE_iff_isZero_truncGE_obj _ _ _ rfl]

set_option backward.defeqAttrib.useBackward true in
instance (X : C) (a b : Int) :
    t.IsLE ((t.truncGELT a b).obj X) (b - 1) := by
  dsimp; infer_instance

set_option backward.defeqAttrib.useBackward true in
instance (X : C) (a b : Int) :
    t.IsGE ((t.truncLTGE a b).obj X) a := by
  dsimp; infer_instance

/--
lemma `isIso_truncGE_map_truncGEπ_app` / 引理 `isIso_truncGE_map_truncGEπ_app`

English:
lemma isIso_truncGE_map_truncGEπ_app
  given: (a b : Int) (h : b <= a) (X : C)
  proof: t.isIso₂_truncGE_map_of_isLE _ (t.triangleLTGE_distinguished b X)
    (a - 1) a (by lia) (t.isLE_truncLT_obj _ _ _ (by simpa))

中文:
引理 isIso_truncGE_map_truncGEπ_app
  条件: (a b : 整数) (h : b <= a) (X : C)
  证明: t.isIso₂_truncGE_map_of_isLE _ (t.triangleLTGE_distinguished b X)
    (a - 1) a (by lia) (t.isLE_truncLT_obj _ _ _ (by simpa))

Depends on / 依赖: isLE_truncLT_obj, t.isIso, t.isLE_truncLT_obj, t.triangleLTGE_distinguished, triangleLTGE_distinguished
-/
lemma isIso_truncGE_map_truncGEπ_app (a b : Int) (h : b <= a) (X : C) :
    IsIso ((t.truncGE a).map ((t.truncGEπ b).app X)) :=
  t.isIso₂_truncGE_map_of_isLE _ (t.triangleLTGE_distinguished b X)
    (a - 1) a (by lia) (t.isLE_truncLT_obj _ _ _ (by simpa))

/--
lemma `isIso_truncLT_map_truncLTι_app` / 引理 `isIso_truncLT_map_truncLTι_app`

English:
lemma isIso_truncLT_map_truncLTι_app
  given: (a b : Int) (h : a <= b) (X : C)
  proof: t.isIso₁_truncLT_map_of_isGE _ (t.triangleLTGE_distinguished b X) a
    (t.isGE_of_ge ((t.truncGE b).obj X) a b (by lia))

中文:
引理 isIso_truncLT_map_truncLTι_app
  条件: (a b : 整数) (h : a <= b) (X : C)
  证明: t.isIso₁_truncLT_map_of_isGE _ (t.triangleLTGE_distinguished b X) a
    (t.isGE_of_ge ((t.truncGE b).obj X) a b (by lia))

Depends on / 依赖: isGE_of_ge, t.isGE_of_ge, t.isIso, t.triangleLTGE_distinguished, t.truncGE, triangleLTGE_distinguished, truncGE
-/
lemma isIso_truncLT_map_truncLTι_app (a b : Int) (h : a <= b) (X : C) :
    IsIso ((t.truncLT a).map ((t.truncLTι b).app X)) :=
  t.isIso₁_truncLT_map_of_isGE _ (t.triangleLTGE_distinguished b X) a
    (t.isGE_of_ge ((t.truncGE b).obj X) a b (by lia))

instance (X : C) (n : Int) : IsIso ((t.truncLT n).map ((t.truncLTι n).app X)) :=
  isIso_truncLT_map_truncLTι_app t _ _ (by rfl) X

instance (X : C) (n : Int) : IsIso ((t.truncGE n).map ((t.truncGEπ n).app X)) :=
  t.isIso_truncGE_map_truncGEπ_app _ _ (by rfl) _

instance (a b : Int) (X : C) :
    IsIso ((t.truncLTι b).app ((t.truncGE a).obj ((t.truncLT b).obj X))) := by
  rw [← t.isLE_iff_isIso_truncLTι_app (b - 1) b (by lia)]
  infer_instance

/--
Definition of `truncGELTToLTGE` / `truncGELTToLTGE` 的定义

English:
definition truncGELTToLTGE
  signature: (a b : Int)
  body: t.liftTruncLT (t.descTruncGE
    ((t.truncLTι b).app X ≫ (t.truncGEπ a).app X) a) (b - 1) b (by lia)
  naturality _ _ _ :=
    t.to_truncLT_obj_ext (by dsimp; exact t.from_truncGE_obj_ext (by simp))

@[reassoc (attr := simp)]

中文:
定义 truncGELTToLTGE
  签名: (a b : 整数)
  定义体: t.liftTruncLT (t.descTruncGE
    ((t.truncLTι b).app X ≫ (t.truncGEπ a).app X) a) (b - 1) b (by lia)
  naturality _ _ _ :=
    t.to_truncLT_obj_ext (by dsimp; exact t.from_truncGE_obj_ext (by simp))

@[reassoc (attr := simp)]

Depends on / 依赖: descTruncGE, liftTruncLT, t.descTruncGE, t.liftTruncLT
-/
noncomputable def truncGELTToLTGE (a b : Int) :
    t.truncGELT a b ⟶ t.truncLTGE a b where
  app X := t.liftTruncLT (t.descTruncGE
    ((t.truncLTι b).app X ≫ (t.truncGEπ a).app X) a) (b - 1) b (by lia)
  naturality _ _ _ :=
    t.to_truncLT_obj_ext (by dsimp; exact t.from_truncGE_obj_ext (by simp))

@[reassoc (attr := simp)]
/--
lemma `truncGELTToLTGE_app_pentagon` / 引理 `truncGELTToLTGE_app_pentagon`

English:
lemma truncGELTToLTGE_app_pentagon
  given: (a b : Int) (X : C)
  proof: by
  simp [truncGELTToLTGE]

中文:
引理 truncGELTToLTGE_app_pentagon
  条件: (a b : 整数) (X : C)
  证明: by
  simp [truncGELTToLTGE]

Depends on / 依赖: truncGELTToLTGE
-/
lemma truncGELTToLTGE_app_pentagon (a b : Int) (X : C) :
    (t.truncGEπ a).app _ ≫ (t.truncGELTToLTGE a b).app X ≫ (t.truncLTι b).app _ =
      (t.truncLTι b).app X ≫ (t.truncGEπ a).app X := by
  simp [truncGELTToLTGE]

/--
lemma `truncGELTToLTGE_app_pentagon_uniqueness` / 引理 `truncGELTToLTGE_app_pentagon_uniqueness`

English:
lemma truncGELTToLTGE_app_pentagon_uniqueness
  statement: {a b : Int} {X : C}
  proof: t.to_truncLT_obj_ext (by dsimp; exact t.from_truncGE_obj_ext (by cat_disch))

@[reassoc]

中文:
引理 truncGELTToLTGE_app_pentagon_uniqueness
  结论: {a b : 整数} {X : C}
  证明: t.to_truncLT_obj_ext (by dsimp; exact t.from_truncGE_obj_ext (by cat_disch))

@[reassoc]

Depends on / 依赖: cat_disch, from_truncGE_obj_ext, t.from_truncGE_obj_ext, t.to_truncLT_obj_ext, to_truncLT_obj_ext
-/
lemma truncGELTToLTGE_app_pentagon_uniqueness {a b : Int} {X : C}
    (φ : (t.truncGELT a b).obj X ⟶ (t.truncLTGE a b).obj X)
    (hφ : (t.truncGEπ a).app _ ≫ φ ≫ (t.truncLTι b).app _ =
      (t.truncLTι b).app X ≫ (t.truncGEπ a).app X) :
    (t.truncGELTToLTGE a b).app X = φ :=
  t.to_truncLT_obj_ext (by dsimp; exact t.from_truncGE_obj_ext (by cat_disch))

@[reassoc]
/--
lemma `truncLT_map_truncGE_map_truncLTι_app_fac` / 引理 `truncLT_map_truncGE_map_truncLTι_app_fac`

English:
lemma truncLT_map_truncGE_map_truncLTι_app_fac
  given: (a b : Int) (X : C)
  proof: by
  rw [← cancel_epi (inv ((t.truncLTι b).app ((t.truncGE a).obj ((t.truncLT b).obj X))))]; rw [IsIso.inv_hom_id_assoc]
  exact t.truncGELTToLTGE_app_pentagon_uniqueness _ (by simp)

中文:
引理 truncLT_map_truncGE_map_truncLTι_app_fac
  条件: (a b : 整数) (X : C)
  证明: by
  rw [← cancel_epi (inv ((t.truncLTι b).app ((t.truncGE a).obj ((t.truncLT b).obj X))))]; rw [IsIso.inv_hom_id_assoc]
  exact t.truncGELTToLTGE_app_pentagon_uniqueness _ (by simp)

Depends on / 依赖: IsIso.inv_hom_id_assoc, cancel_epi, inv_hom_id_assoc, t.truncGE, t.truncGELTToLTGE_app_pentagon_uniqueness, t.truncLT, truncGE, truncGELTToLTGE_app_pentagon_uniqueness, truncLT
-/
lemma truncLT_map_truncGE_map_truncLTι_app_fac (a b : Int) (X : C) :
    (t.truncLTι b).app ((t.truncGE a).obj ((t.truncLT b).obj X)) ≫
        (t.truncGELTToLTGE a b).app X =
    (t.truncLT b).map ((t.truncGE a).map ((t.truncLTι b).app X)) := by
  rw [← cancel_epi (inv ((t.truncLTι b).app ((t.truncGE a).obj ((t.truncLT b).obj X))))]; rw [IsIso.inv_hom_id_assoc]
  exact t.truncGELTToLTGE_app_pentagon_uniqueness _ (by simp)

/-- The connecting homomorphism
`(t.truncGELT a b).obj X ⟶ ((t.truncLT a).obj X)⟦1⟧`,
as a natural transformation. -/
@[expose, simps!]
/--
Definition of `truncGELTδLT` / `truncGELTδLT` 的定义

English:
definition truncGELTδLT
  signature: (a b : Int)
  body: Functor.whiskerLeft (t.truncLT b) (t.truncGEδLT a) ≫
    Functor.whiskerRight (t.truncLTι b) (t.truncLT a ⋙ shiftFunctor C (1 : Int))

中文:
定义 truncGELTδLT
  签名: (a b : 整数)
  定义体: Functor.whiskerLeft (t.truncLT b) (t.truncGEδLT a) ≫
    Functor.whiskerRight (t.truncLTι b) (t.truncLT a ⋙ shiftFunctor C (1 : Int))

Depends on / 依赖: Functor, Functor.whiskerLeft, Functor.whiskerRight, shiftFunctor, t.truncGE, t.truncLT, truncLT, whiskerLeft, whiskerRight
-/
noncomputable def truncGELTδLT (a b : Int) :
    t.truncGELT a b ⟶ t.truncLT a ⋙ shiftFunctor C (1 : Int) :=
  Functor.whiskerLeft (t.truncLT b) (t.truncGEδLT a) ≫
    Functor.whiskerRight (t.truncLTι b) (t.truncLT a ⋙ shiftFunctor C (1 : Int))

/-- The functorial (distinguished) triangle
`(t.truncLT a).obj X ⟶ (t.truncLT b).obj X ⟶ (t.truncGELT a b).obj X ⟶ ...`
when `a ≤ b`. -/
@[expose, simps!]
/--
Definition of `triangleLTLTGELT` / `triangleLTLTGELT` 的定义

English:
definition triangleLTLTGELT
  signature: (a b : Int) (h : a <= b)
  body: Triangle.functorMk (t.natTransTruncLTOfLE a b h)
    (Functor.whiskerLeft (t.truncLT b) (t.truncGEπ a)) (t.truncGELTδLT a b)

中文:
定义 triangleLTLTGELT
  签名: (a b : 整数) (h : a <= b)
  定义体: Triangle.functorMk (t.natTransTruncLTOfLE a b h)
    (Functor.whiskerLeft (t.truncLT b) (t.truncGEπ a)) (t.truncGELTδLT a b)

Depends on / 依赖: Functor, Functor.whiskerLeft, Triangle, Triangle.functorMk, functorMk, natTransTruncLTOfLE, t.natTransTruncLTOfLE, t.truncGE, t.truncGELT, t.truncLT, truncLT, whiskerLeft
-/
noncomputable def triangleLTLTGELT (a b : Int) (h : a <= b) : C ⥤ Triangle C :=
  Triangle.functorMk (t.natTransTruncLTOfLE a b h)
    (Functor.whiskerLeft (t.truncLT b) (t.truncGEπ a)) (t.truncGELTδLT a b)

set_option backward.defeqAttrib.useBackward true in
/--
lemma `triangleLTLTGELT_distinguished` / 引理 `triangleLTLTGELT_distinguished`

English:
lemma triangleLTLTGELT_distinguished
  given: (a b : Int) (h : a <= b) (X : C)
  proof: by
  have := t.isIso_truncLT_map_truncLTι_app a b h X
  refine isomorphic_distinguished _ (t.triangleLTGE_distinguished a ((t.truncLT b).obj X)) _ ?_
  refine Triangle.isoMk _ _ ((asIso ((t.truncLT a).map ((t.truncLTι b).app X))).symm)
    (Iso.refl _) (Iso.refl _) ?_ (by simp) (by simp)
  dsimp
  s

中文:
引理 triangleLTLTGELT_distinguished
  条件: (a b : 整数) (h : a <= b) (X : C)
  证明: by
  have := t.isIso_truncLT_map_truncLTι_app a b h X
  refine isomorphic_distinguished _ (t.triangleLTGE_distinguished a ((t.truncLT b).obj X)) _ ?_
  refine Triangle.isoMk _ _ ((asIso ((t.truncLT a).map ((t.truncLTι b).app X))).symm)
    (Iso.refl _) (Iso.refl _) ?_ (by simp) (by simp)
  dsimp
  s

Depends on / 依赖: Category, Category.comp_id, IsIso.eq_inv_comp, Iso.refl, Triangle, Triangle.isoMk, comp_id, eq_inv_comp, isomorphic_distinguished, t.isIso_truncLT_map_truncLT, t.to_truncLT_obj_ext, t.triangleLTGE_distinguished, t.truncLT, to_truncLT_obj_ext, triangleLTGE_distinguished, truncLT
-/
lemma triangleLTLTGELT_distinguished (a b : Int) (h : a <= b) (X : C) :
    (t.triangleLTLTGELT a b h).obj X in distTriang C := by
  have := t.isIso_truncLT_map_truncLTι_app a b h X
  refine isomorphic_distinguished _ (t.triangleLTGE_distinguished a ((t.truncLT b).obj X)) _ ?_
  refine Triangle.isoMk _ _ ((asIso ((t.truncLT a).map ((t.truncLTι b).app X))).symm)
    (Iso.refl _) (Iso.refl _) ?_ (by simp) (by simp)
  dsimp
  simp only [Category.comp_id, IsIso.eq_inv_comp]
  exact t.to_truncLT_obj_ext (by simp)

set_option backward.defeqAttrib.useBackward true in
instance (a b : Int) : IsIso (t.truncGELTToLTGE a b) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  by_cases h : a <= b
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

instance (a b : Int) (X : C) :
    IsIso ((t.truncLT b).map ((t.truncGE a).map ((t.truncLTι b).app X))) := by
  rw [← t.truncLT_map_truncGE_map_truncLTι_app_fac a b X]
  infer_instance

/--
Definition of `truncGELTIsoLTGE` / `truncGELTIsoLTGE` 的定义

English:
definition truncGELTIsoLTGE
  signature: (a b : Int)
  body: asIso (t.truncGELTToLTGE a b)

中文:
定义 truncGELTIsoLTGE
  签名: (a b : 整数)
  定义体: asIso (t.truncGELTToLTGE a b)

Depends on / 依赖: t.truncGELTToLTGE, truncGELTToLTGE
-/
noncomputable def truncGELTIsoLTGE (a b : Int) : t.truncGELT a b ≅ t.truncLTGE a b :=
  asIso (t.truncGELTToLTGE a b)

end

end

end TStructure

end Triangulated

end CategoryTheory
