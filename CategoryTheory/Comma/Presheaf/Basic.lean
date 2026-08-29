/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.HomCongr
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.Tactic.CategoryTheory.Elementwise

/-!
# Computation of `Over A` for a presheaf `A`

Let `A : Cᵒᵖ ⥤ Type v` be a presheaf. In this file, we construct an equivalence
`e : Over A ≌ (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v` and show that there is a quasi-commutative
diagram

```
CostructuredArrow yoneda A ⥤ Over A

                             ⇘ ⥥

                               PSh(CostructuredArrow yoneda A)
```

where the top arrow is the forgetful functor forgetting the yoneda-costructure, the right arrow is
the aforementioned equivalence and the diagonal arrow is the Yoneda embedding.

In the notation of Kashiwara-Schapira, the type of the equivalence is written `C^ₐ ≌ Cₐ^`, where
`·ₐ` is `CostructuredArrow` (with the functor `S` being either the identity or the Yoneda
embedding) and `^` is taking presheaves. The equivalence is a key ingredient in various results in
Kashiwara-Schapira.

The proof is somewhat long and technical, in part due to the construction inherently involving a
sigma type which comes with the usual DTT issues. However, a user of this result should not need
to interact with the actual construction, the mere existence of the equivalence and the commutative
triangle should generally be sufficient.

## Main results
* `overEquivPresheafCostructuredArrow`:
  the equivalence `Over A ≌ (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v`
* `CostructuredArrow.toOverCompOverEquivPresheafCostructuredArrow`: the natural isomorphism
  `CostructuredArrow.toOver yoneda A ⋙ (overEquivPresheafCostructuredArrow A).functor ≅ yoneda`

## Implementation details

The proof needs to introduce "correction terms" in various places in order to overcome DTT issues,
and these need to be canceled against each other when appropriate. It is important to deal with
these in a structured manner, otherwise you get large goals containing many correction terms which
are very tedious to manipulate. We avoid this blowup by carefully controlling which definitions
`(d)simp` is allowed to unfold and stating many lemmas explicitly before they are required. This
leads to manageable goals containing only a small number of correction terms. Generally, we use
the form `F.map (eqToHom _)` for these correction terms and try to push them as far outside as
possible.

## Future work
* If needed, it should be possible to show that the equivalence is natural in `A`.

## References
* [M. Kashiwara, P. Schapira, *Categories and Sheaves*][Kashiwara2006], Lemma 1.4.12

## Tags
presheaf, over category, coyoneda

-/

@[expose] public section

namespace CategoryTheory

open Category Opposite

universe w v u

variable {C : Type u} [Category.{v} C] {A : Cᵒᵖ ⥤ Type v}

namespace OverPresheafAux

/-! ### Construction of the forward functor `Over A ⥤ (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v` -/

/--
Definition of `MakesOverArrow` / `MakesOverArrow` 的定义

English:
structure MakesOverArrow
  parameters: {F : Cᵒᵖ ⥤ Type v} (η : F ⟶ A) {X : C} (s : yoneda.obj X ⟶ A)
  axioms and operations (1):
    - app : η.app (op X) u = yonedaEquiv s

中文:
结构 MakesOverArrow
  参数: {F : Cᵒᵖ ⥤ 类型v} (η : F ⟶ A) {X : C} (s : yoneda.obj X ⟶ A)
  公理与运算 (1 个):
    - app : η.app (op X) u = yonedaEquiv s
-/
structure MakesOverArrow {F : Cᵒᵖ ⥤ Type v} (η : F ⟶ A) {X : C} (s : yoneda.obj X ⟶ A)
    (u : F.obj (op X)) : Prop where
  app : η.app (op X) u = yonedaEquiv s

namespace MakesOverArrow

/--
lemma `map₁` / 引理 `map₁`

English:
lemma map₁
  statement: {F G : Cᵒᵖ ⥤ Type v} {η : F ⟶ A} {μ : G ⟶ A} {ε : F ⟶ G}
  proof: ⟨by rw [← comp_apply, ← NatTrans.comp_app, hε, h.app]⟩

中文:
引理 map₁
  结论: {F G : Cᵒᵖ ⥤ 类型v} {η : F ⟶ A} {μ : G ⟶ A} {ε : F ⟶ G}
  证明: ⟨by rw [← comp_apply, ← NatTrans.comp_app, hε, h.app]⟩

Depends on / 依赖: NatTrans, NatTrans.comp_app, comp_app, comp_apply, h.app
-/
lemma map₁ {F G : Cᵒᵖ ⥤ Type v} {η : F ⟶ A} {μ : G ⟶ A} {ε : F ⟶ G}
    (hε : ε ≫ μ = η) {X : C} {s : yoneda.obj X ⟶ A} {u : F.obj (op X)}
    (h : MakesOverArrow η s u) : MakesOverArrow μ s (ε.app _ u) :=
  ⟨by rw [← comp_apply, ← NatTrans.comp_app, hε, h.app]⟩

/--
lemma `map₂` / 引理 `map₂`

English:
lemma map₂
  statement: {F : Cᵒᵖ ⥤ Type v} {η : F ⟶ A} {X Y : C} (f : X ⟶ Y)
  proof: ⟨by simp [h.app, yonedaEquiv_naturality, hst]⟩

中文:
引理 map₂
  结论: {F : Cᵒᵖ ⥤ 类型v} {η : F ⟶ A} {X Y : C} (f : X ⟶ Y)
  证明: ⟨by simp [h.app, yonedaEquiv_naturality, hst]⟩

Depends on / 依赖: h.app, yonedaEquiv_naturality
-/
lemma map₂ {F : Cᵒᵖ ⥤ Type v} {η : F ⟶ A} {X Y : C} (f : X ⟶ Y)
    {s : yoneda.obj X ⟶ A} {t : yoneda.obj Y ⟶ A} (hst : yoneda.map f ≫ t = s)
    {u : F.obj (op Y)} (h : MakesOverArrow η t u) : MakesOverArrow η s (F.map f.op u) :=
  ⟨by simp [h.app, yonedaEquiv_naturality, hst]⟩

/--
lemma `of_arrow` / 引理 `of_arrow`

English:
lemma of_arrow
  statement: {F : Cᵒᵖ ⥤ Type v} {η : F ⟶ A} {X : C} {s : yoneda.obj X ⟶ A}
  proof: ⟨hf ▸ rfl⟩

中文:
引理 of_arrow
  结论: {F : Cᵒᵖ ⥤ 类型v} {η : F ⟶ A} {X : C} {s : yoneda.obj X ⟶ A}
  证明: ⟨hf ▸ rfl⟩
-/
lemma of_arrow {F : Cᵒᵖ ⥤ Type v} {η : F ⟶ A} {X : C} {s : yoneda.obj X ⟶ A}
    {f : yoneda.obj X ⟶ F} (hf : f ≫ η = s) : MakesOverArrow η s (yonedaEquiv f) :=
  ⟨hf ▸ rfl⟩

/--
lemma `of_yoneda_arrow` / 引理 `of_yoneda_arrow`

English:
lemma of_yoneda_arrow
  statement: {Y : C} {η : yoneda.obj Y ⟶ A} {X : C} {s : yoneda.obj X ⟶ A} {f : X ⟶ Y}
  proof: by
  simpa only [yonedaEquiv_yoneda_map f] using of_arrow hf

中文:
引理 of_yoneda_arrow
  结论: {Y : C} {η : yoneda.obj Y ⟶ A} {X : C} {s : yoneda.obj X ⟶ A} {f : X ⟶ Y}
  证明: by
  simpa only [yonedaEquiv_yoneda_map f] using of_arrow hf

Depends on / 依赖: of_arrow, yonedaEquiv_yoneda_map
-/
lemma of_yoneda_arrow {Y : C} {η : yoneda.obj Y ⟶ A} {X : C} {s : yoneda.obj X ⟶ A} {f : X ⟶ Y}
    (hf : yoneda.map f ≫ η = s) : MakesOverArrow η s f := by
  simpa only [yonedaEquiv_yoneda_map f] using of_arrow hf

end MakesOverArrow

/--
Definition of `OverArrows` / `OverArrows` 的定义

English:
definition OverArrows
  signature: {F : Cᵒᵖ ⥤ Type v} (η : F ⟶ A) {X : C} (s : yoneda.obj X ⟶ A)
  body: Subtype (MakesOverArrow η s)

中文:
定义 OverArrows
  签名: {F : Cᵒᵖ ⥤ 类型v} (η : F ⟶ A) {X : C} (s : yoneda.obj X ⟶ A)
  定义体: Subtype (MakesOverArrow η s)

Depends on / 依赖: MakesOverArrow, Subtype
-/
def OverArrows {F : Cᵒᵖ ⥤ Type v} (η : F ⟶ A) {X : C} (s : yoneda.obj X ⟶ A) : Type v :=
  Subtype (MakesOverArrow η s)

namespace OverArrows
/--
Definition of `val` / `val` 的定义

English:
definition val
  signature: {F : Cᵒᵖ ⥤ Type v} {η : F ⟶ A} {X : C} {s : yoneda.obj X ⟶ A}
  body: Subtype.val

@[simp]

中文:
定义 val
  签名: {F : Cᵒᵖ ⥤ 类型v} {η : F ⟶ A} {X : C} {s : yoneda.obj X ⟶ A}
  定义体: Subtype.val

@[simp]

Depends on / 依赖: Subtype, Subtype.val
-/
def val {F : Cᵒᵖ ⥤ Type v} {η : F ⟶ A} {X : C} {s : yoneda.obj X ⟶ A} :
    OverArrows η s -> F.obj (op X) :=
  Subtype.val

@[simp]
/--
lemma `val_mk` / 引理 `val_mk`

English:
lemma val_mk
  statement: {F : Cᵒᵖ ⥤ Type v} (η : F ⟶ A) {X : C} (s : yoneda.obj X ⟶ A) (u : F.obj (op X))
  proof: rfl

@[ext]

中文:
引理 val_mk
  结论: {F : Cᵒᵖ ⥤ 类型v} (η : F ⟶ A) {X : C} (s : yoneda.obj X ⟶ A) (u : F.obj (op X))
  证明: rfl

@[ext]
-/
lemma val_mk {F : Cᵒᵖ ⥤ Type v} (η : F ⟶ A) {X : C} (s : yoneda.obj X ⟶ A) (u : F.obj (op X))
    (h : MakesOverArrow η s u) : val ⟨u, h⟩ = u :=
  rfl

@[ext]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  statement: {F : Cᵒᵖ ⥤ Type v} {η : F ⟶ A} {X : C} {s : yoneda.obj X ⟶ A}
  proof: Subtype.ext

中文:
引理 ext
  结论: {F : Cᵒᵖ ⥤ 类型v} {η : F ⟶ A} {X : C} {s : yoneda.obj X ⟶ A}
  证明: Subtype.ext

Depends on / 依赖: Subtype, Subtype.ext
-/
lemma ext {F : Cᵒᵖ ⥤ Type v} {η : F ⟶ A} {X : C} {s : yoneda.obj X ⟶ A}
    {u v : OverArrows η s} : u.val = v.val -> u = v :=
  Subtype.ext

/--
lemma `app_val` / 引理 `app_val`

English:
lemma app_val
  statement: {F : Cᵒᵖ ⥤ Type v} {η : F ⟶ A} {X : C} {s : yoneda.obj X ⟶ A}
  proof: p.prop.app

中文:
引理 app_val
  结论: {F : Cᵒᵖ ⥤ 类型v} {η : F ⟶ A} {X : C} {s : yoneda.obj X ⟶ A}
  证明: p.prop.app

Depends on / 依赖: p.prop.app
-/
lemma app_val {F : Cᵒᵖ ⥤ Type v} {η : F ⟶ A} {X : C} {s : yoneda.obj X ⟶ A}
    (p : OverArrows η s) : η.app (op X) p.val = yonedaEquiv s :=
  p.prop.app

/-- In the special case `F = yoneda.obj Y`, the element `p.val` for `p : OverArrows η s` is itself
a morphism `X ⟶ Y`. -/
@[simp]
/--
lemma `map_val` / 引理 `map_val`

English:
lemma map_val
  statement: {Y : C} {η : yoneda.obj Y ⟶ A} {X : C} {s : yoneda.obj X ⟶ A}
  proof: by
  rw [← yonedaEquiv.injective.eq_iff]; rw [yonedaEquiv_comp]; rw [yonedaEquiv_yoneda_map]
  simp only [unop_op, p.app_val]

中文:
引理 map_val
  结论: {Y : C} {η : yoneda.obj Y ⟶ A} {X : C} {s : yoneda.obj X ⟶ A}
  证明: by
  rw [← yonedaEquiv.injective.eq_iff]; rw [yonedaEquiv_comp]; rw [yonedaEquiv_yoneda_map]
  simp only [unop_op, p.app_val]

Depends on / 依赖: app_val, eq_iff, injective, p.app_val, unop_op, yonedaEquiv, yonedaEquiv.injective.eq_iff, yonedaEquiv_comp, yonedaEquiv_yoneda_map
-/
lemma map_val {Y : C} {η : yoneda.obj Y ⟶ A} {X : C} {s : yoneda.obj X ⟶ A}
    (p : OverArrows η s) : yoneda.map p.val ≫ η = s := by
  rw [← yonedaEquiv.injective.eq_iff]; rw [yonedaEquiv_comp]; rw [yonedaEquiv_yoneda_map]
  simp only [unop_op, p.app_val]

/--
Definition of `map₁` / `map₁` 的定义

English:
definition map₁
  signature: {F G : Cᵒᵖ ⥤ Type v} {η : F ⟶ A} {μ : G ⟶ A} {X : C} {s : yoneda.obj X ⟶ A}
  body: ⟨ε.app _ u.val, MakesOverArrow.map₁ hε u.2⟩

@[simp]

中文:
定义 map₁
  签名: {F G : Cᵒᵖ ⥤ 类型v} {η : F ⟶ A} {μ : G ⟶ A} {X : C} {s : yoneda.obj X ⟶ A}
  定义体: ⟨ε.app _ u.val, MakesOverArrow.map₁ hε u.2⟩

@[simp]

Depends on / 依赖: MakesOverArrow, MakesOverArrow.map, u.val
-/
def map₁ {F G : Cᵒᵖ ⥤ Type v} {η : F ⟶ A} {μ : G ⟶ A} {X : C} {s : yoneda.obj X ⟶ A}
    (u : OverArrows η s) (ε : F ⟶ G) (hε : ε ≫ μ = η) : OverArrows μ s :=
  ⟨ε.app _ u.val, MakesOverArrow.map₁ hε u.2⟩

@[simp]
/--
lemma `map₁_val` / 引理 `map₁_val`

English:
lemma map₁_val
  statement: {F G : Cᵒᵖ ⥤ Type v} {η : F ⟶ A} {μ : G ⟶ A} {X : C}
  proof: rfl

中文:
引理 map₁_val
  结论: {F G : Cᵒᵖ ⥤ 类型v} {η : F ⟶ A} {μ : G ⟶ A} {X : C}
  证明: rfl
-/
lemma map₁_val {F G : Cᵒᵖ ⥤ Type v} {η : F ⟶ A} {μ : G ⟶ A} {X : C}
    (s : yoneda.obj X ⟶ A) (u : OverArrows η s) (ε : F ⟶ G) (hε : ε ≫ μ = η) :
    (u.map₁ ε hε).val = ε.app _ u.val :=
  rfl

/--
Definition of `map₂` / `map₂` 的定义

English:
definition map₂
  signature: {F : Cᵒᵖ ⥤ Type v} {η : F ⟶ A} {X Y : C} {s : yoneda.obj X ⟶ A}
  body: ⟨F.map f.op u.val, MakesOverArrow.map₂ f hst u.2⟩

@[simp]

中文:
定义 map₂
  签名: {F : Cᵒᵖ ⥤ 类型v} {η : F ⟶ A} {X Y : C} {s : yoneda.obj X ⟶ A}
  定义体: ⟨F.map f.op u.val, MakesOverArrow.map₂ f hst u.2⟩

@[simp]

Depends on / 依赖: F.map, MakesOverArrow, MakesOverArrow.map, f.op, u.val
-/
def map₂ {F : Cᵒᵖ ⥤ Type v} {η : F ⟶ A} {X Y : C} {s : yoneda.obj X ⟶ A}
    {t : yoneda.obj Y ⟶ A} (u : OverArrows η t) (f : X ⟶ Y) (hst : yoneda.map f ≫ t = s) :
    OverArrows η s :=
  ⟨F.map f.op u.val, MakesOverArrow.map₂ f hst u.2⟩

@[simp]
/--
lemma `map₂_val` / 引理 `map₂_val`

English:
lemma map₂_val
  statement: {F : Cᵒᵖ ⥤ Type v} {η : F ⟶ A} {X Y : C} (f : X ⟶ Y)
  proof: rfl

@[simp]

中文:
引理 map₂_val
  结论: {F : Cᵒᵖ ⥤ 类型v} {η : F ⟶ A} {X Y : C} (f : X ⟶ Y)
  证明: rfl

@[simp]
-/
lemma map₂_val {F : Cᵒᵖ ⥤ Type v} {η : F ⟶ A} {X Y : C} (f : X ⟶ Y)
    {s : yoneda.obj X ⟶ A} {t : yoneda.obj Y ⟶ A} (hst : yoneda.map f ≫ t = s)
    (u : OverArrows η t) : (u.map₂ f hst).val = F.map f.op u.val :=
  rfl

@[simp]
/--
lemma `map₁_map₂` / 引理 `map₁_map₂`

English:
lemma map₁_map₂
  statement: {F G : Cᵒᵖ ⥤ Type v} {η : F ⟶ A} {μ : G ⟶ A} (ε : F ⟶ G)
  proof: OverArrows.ext (elementwise_of% (ε.naturality f.op).symm) u.val

中文:
引理 map₁_map₂
  结论: {F G : Cᵒᵖ ⥤ 类型v} {η : F ⟶ A} {μ : G ⟶ A} (ε : F ⟶ G)
  证明: OverArrows.ext (elementwise_of% (ε.naturality f.op).symm) u.val

Depends on / 依赖: OverArrows, OverArrows.ext, elementwise_of, f.op, naturality, u.val
-/
lemma map₁_map₂ {F G : Cᵒᵖ ⥤ Type v} {η : F ⟶ A} {μ : G ⟶ A} (ε : F ⟶ G)
    (hε : ε ≫ μ = η) {X Y : C} {s : yoneda.obj X ⟶ A} {t : yoneda.obj Y ⟶ A} (f : X ⟶ Y)
    (hf : yoneda.map f ≫ t = s) (u : OverArrows η t) :
    (u.map₁ ε hε).map₂ f hf = (u.map₂ f hf).map₁ ε hε :=
OverArrows.ext (elementwise_of% (ε.naturality f.op).symm) u.val

/--
Definition of `yonedaArrow` / `yonedaArrow` 的定义

English:
definition yonedaArrow
  signature: {Y : C} {η : yoneda.obj Y ⟶ A} {X : C} {s : yoneda.obj X ⟶ A} (f : X ⟶ Y)
  body: ⟨f, .of_yoneda_arrow hf⟩

@[simp]

中文:
定义 yonedaArrow
  签名: {Y : C} {η : yoneda.obj Y ⟶ A} {X : C} {s : yoneda.obj X ⟶ A} (f : X ⟶ Y)
  定义体: ⟨f, .of_yoneda_arrow hf⟩

@[simp]

Depends on / 依赖: of_yoneda_arrow
-/
def yonedaArrow {Y : C} {η : yoneda.obj Y ⟶ A} {X : C} {s : yoneda.obj X ⟶ A} (f : X ⟶ Y)
    (hf : yoneda.map f ≫ η = s) : OverArrows η s :=
  ⟨f, .of_yoneda_arrow hf⟩

@[simp]
/--
lemma `yonedaArrow_val` / 引理 `yonedaArrow_val`

English:
lemma yonedaArrow_val
  statement: {Y : C} {η : yoneda.obj Y ⟶ A} {X : C} {s : yoneda.obj X ⟶ A} {f : X ⟶ Y}
  proof: rfl

中文:
引理 yonedaArrow_val
  结论: {Y : C} {η : yoneda.obj Y ⟶ A} {X : C} {s : yoneda.obj X ⟶ A} {f : X ⟶ Y}
  证明: rfl
-/
lemma yonedaArrow_val {Y : C} {η : yoneda.obj Y ⟶ A} {X : C} {s : yoneda.obj X ⟶ A} {f : X ⟶ Y}
    (hf : yoneda.map f ≫ η = s) : (yonedaArrow f hf).val = f :=
  rfl

/--
Definition of `costructuredArrowIso` / `costructuredArrowIso` 的定义

English:
definition costructuredArrowIso
  signature: (s t : CostructuredArrow yoneda A)
  body: ↾fun p => CostructuredArrow.homMk p.val (by simp)
  inv := ↾fun f => yonedaArrow f.left f.w

中文:
定义 costructuredArrowIso
  签名: (s t : CostructuredArrow yoneda A)
  定义体: ↾fun p => CostructuredArrow.homMk p.val (by simp)
  inv := ↾fun f => yonedaArrow f.left f.w

Depends on / 依赖: CostructuredArrow, CostructuredArrow.homMk, Over.opEquivOpUnder, hasFiniteLimits_of_hasLimitsLimits_of_createsFiniteLimits, hasFiniteLimits_opposite_iff, inverse, opEquivOpUnder, p.val
-/
def costructuredArrowIso (s t : CostructuredArrow yoneda A) :
    (OverArrows s.hom t.hom) ≅ (t ⟶ s) where
  hom := ↾fun p => CostructuredArrow.homMk p.val (by simp)
  inv := ↾fun f => yonedaArrow f.left f.w

end OverArrows

/-- This is basically just `yoneda.obj η : (Over A)ᵒᵖ ⥤ Type (max u v)` restricted along the
forgetful functor `CostructuredArrow yoneda A ⥤ Over A`, but done in a way that we land in a
smaller universe. -/
@[simps]
/--
Definition of `restrictedYonedaObj` / `restrictedYonedaObj` 的定义

English:
definition restrictedYonedaObj
  signature: {F : Cᵒᵖ ⥤ Type v} (η : F ⟶ A)
  body: OverArrows η s.unop.hom
  map f := ↾fun u => u.map₂ f.unop.left f.unop.w

中文:
定义 restrictedYonedaObj
  签名: {F : Cᵒᵖ ⥤ 类型v} (η : F ⟶ A)
  定义体: OverArrows η s.unop.hom
  map f := ↾fun u => u.map₂ f.unop.left f.unop.w

Depends on / 依赖: Over.opEquivOpUnder, OverArrows, hasLimitsOfSize_opposite_iff, hasLimits_of_hasLimits_createsLimits, inverse, opEquivOpUnder, s.unop.hom
-/
def restrictedYonedaObj {F : Cᵒᵖ ⥤ Type v} (η : F ⟶ A) :
    (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v where
  obj s := OverArrows η s.unop.hom
  map f := ↾fun u => u.map₂ f.unop.left f.unop.w

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Functoriality of `restrictedYonedaObj η` in `η`. -/
@[simps]
/--
Definition of `restrictedYonedaObjMap₁` / `restrictedYonedaObjMap₁` 的定义

English:
definition restrictedYonedaObjMap₁
  signature: {F G : Cᵒᵖ ⥤ Type v} {η : F ⟶ A} {μ : G ⟶ A} (ε : F ⟶ G)
  body: ↾fun u => u.map₁ ε hε

中文:
定义 restrictedYonedaObjMap₁
  签名: {F G : Cᵒᵖ ⥤ 类型v} {η : F ⟶ A} {μ : G ⟶ A} (ε : F ⟶ G)
  定义体: ↾fun u => u.map₁ ε hε

Depends on / 依赖: u.map
-/
def restrictedYonedaObjMap₁ {F G : Cᵒᵖ ⥤ Type v} {η : F ⟶ A} {μ : G ⟶ A} (ε : F ⟶ G)
    (hε : ε ≫ μ = η) : restrictedYonedaObj η ⟶ restrictedYonedaObj μ where
  app _ := ↾fun u => u.map₁ ε hε

set_option backward.isDefEq.respectTransparency.types false in
/--
This is basically just `yoneda : Over A ⥤ (Over A)ᵒᵖ ⥤ Type (max u v)` restricted in the second
argument along the forgetful functor `CostructuredArrow yoneda A ⥤ Over A`, but done in a way
that we land in a smaller universe.

This is one direction of the equivalence we're constructing. -/
@[simps]
/--
Definition of `restrictedYoneda` / `restrictedYoneda` 的定义

English:
definition restrictedYoneda
  signature: (A : Cᵒᵖ ⥤ Type v)
  body: restrictedYonedaObj η.hom
  map ε := restrictedYonedaObjMap₁ ε.left ε.w

中文:
定义 restrictedYoneda
  签名: (A : Cᵒᵖ ⥤ 类型v)
  定义体: restrictedYonedaObj η.hom
  map ε := restrictedYonedaObjMap₁ ε.left ε.w

Depends on / 依赖: restrictedYonedaObj
-/
def restrictedYoneda (A : Cᵒᵖ ⥤ Type v) :
    Over A ⥤ (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v where
  obj η := restrictedYonedaObj η.hom
  map ε := restrictedYonedaObjMap₁ ε.left ε.w

/--
Definition of `toOverYonedaCompRestrictedYoneda` / `toOverYonedaCompRestrictedYoneda` 的定义

English:
definition toOverYonedaCompRestrictedYoneda
  signature: (A : Cᵒᵖ ⥤ Type v)
  body: NatIso.ofComponents
    (fun s => NatIso.ofComponents (fun _ => OverArrows.costructuredArrowIso _ _) (by cat_disch))
    (by cat_disch)

中文:
定义 toOverYonedaCompRestrictedYoneda
  签名: (A : Cᵒᵖ ⥤ 类型v)
  定义体: NatIso.ofComponents
    (fun s => NatIso.ofComponents (fun _ => OverArrows.costructuredArrowIso _ _) (by cat_disch))
    (by cat_disch)

Depends on / 依赖: NatIso, NatIso.ofComponents, OverArrows, OverArrows.costructuredArrowIso, cat_disch, costructuredArrowIso, ofComponents
-/
def toOverYonedaCompRestrictedYoneda (A : Cᵒᵖ ⥤ Type v) :
    CostructuredArrow.toOver yoneda A ⋙ restrictedYoneda A ≅ yoneda :=
  NatIso.ofComponents
    (fun s => NatIso.ofComponents (fun _ => OverArrows.costructuredArrowIso _ _) (by cat_disch))
    (by cat_disch)


/--
lemma `map_mkPrecomp_eqToHom` / 引理 `map_mkPrecomp_eqToHom`

English:
lemma map_mkPrecomp_eqToHom
  statement: {F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v} {X Y : C} {f : X ⟶ Y}
  proof: by
  cat_disch

中文:
引理 map_mkPrecomp_eqToHom
  结论: {F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ 类型v} {X Y : C} {f : X ⟶ Y}
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
lemma map_mkPrecomp_eqToHom {F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v} {X Y : C} {f : X ⟶ Y}
    {g g' : yoneda.obj Y ⟶ A} (h : g = g')
    {x : F.obj (op (CostructuredArrow.mk g'))} :
    F.map (CostructuredArrow.mkPrecomp g f).op (F.map (eqToHom (by rw [h])) x) =
      F.map (eqToHom (by rw [h])) (F.map (CostructuredArrow.mkPrecomp g' f).op x) := by
  cat_disch

attribute [local simp] map_mkPrecomp_eqToHom

/--
Definition of `YonedaCollection` / `YonedaCollection` 的定义

English:
definition YonedaCollection
  signature: (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v) (X : C)
  body: Σ s : A.obj (op X), F.obj (op (CostructuredArrow.mk (yonedaEquiv.symm s)))

中文:
定义 YonedaCollection
  签名: (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ 类型v) (X : C)
  定义体: Σ s : A.obj (op X), F.obj (op (CostructuredArrow.mk (yonedaEquiv.symm s)))

Depends on / 依赖: A.obj, CostructuredArrow, CostructuredArrow.mk, F.obj, yonedaEquiv, yonedaEquiv.symm
-/
def YonedaCollection (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v) (X : C) : Type v :=
  Σ s : A.obj (op X), F.obj (op (CostructuredArrow.mk (yonedaEquiv.symm s)))

namespace YonedaCollection

variable {F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v} {X : C}

/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: (s : yoneda.obj X ⟶ A) (x : F.obj (op (CostructuredArrow.mk s)))
  body: ⟨yonedaEquiv s, F.map (eqToHom <| by rw [Equiv.symm_apply_apply]) x⟩

中文:
定义 mk
  签名: (s : yoneda.obj X ⟶ A) (x : F.obj (op (CostructuredArrow.mk s)))
  定义体: ⟨yonedaEquiv s, F.map (eqToHom <| by rw [Equiv.symm_apply_apply]) x⟩

Depends on / 依赖: Equiv.symm_apply_apply, F.map, eqToHom, symm_apply_apply, yonedaEquiv
-/
def mk (s : yoneda.obj X ⟶ A) (x : F.obj (op (CostructuredArrow.mk s))) : YonedaCollection F X :=
  ⟨yonedaEquiv s, F.map (eqToHom <| by rw [Equiv.symm_apply_apply]) x⟩

/--
Definition of `fst` / `fst` 的定义

English:
definition fst
  signature: (p : YonedaCollection F X)
  body: yonedaEquiv.symm p.1

中文:
定义 fst
  签名: (p : YonedaCollection F X)
  定义体: yonedaEquiv.symm p.1

Depends on / 依赖: yonedaEquiv, yonedaEquiv.symm
-/
def fst (p : YonedaCollection F X) : yoneda.obj X ⟶ A :=
  yonedaEquiv.symm p.1

/--
Definition of `snd` / `snd` 的定义

English:
definition snd
  signature: (p : YonedaCollection F X)
  body: p.2

中文:
定义 snd
  签名: (p : YonedaCollection F X)
  定义体: p.2
-/
def snd (p : YonedaCollection F X) : F.obj (op (CostructuredArrow.mk p.fst)) :=
  p.2

/--
Definition of `yonedaEquivFst` / `yonedaEquivFst` 的定义

English:
definition yonedaEquivFst
  signature: (p : YonedaCollection F X)
  body: yonedaEquiv p.fst

中文:
定义 yonedaEquivFst
  签名: (p : YonedaCollection F X)
  定义体: yonedaEquiv p.fst

Depends on / 依赖: p.fst, yonedaEquiv
-/
def yonedaEquivFst (p : YonedaCollection F X) : A.obj (op X) :=
  yonedaEquiv p.fst

/--
lemma `yonedaEquivFst_eq` / 引理 `yonedaEquivFst_eq`

English:
lemma yonedaEquivFst_eq
  given: (p : YonedaCollection F X)
  statement: p.yonedaEquivFst = yonedaEquiv p.fst
  proof: rfl

@[simp]

中文:
引理 yonedaEquivFst_eq
  条件: (p : YonedaCollection F X)
  结论: p.yonedaEquivFst = yonedaEquiv p.fst
  证明: rfl

@[simp]

Depends on / 依赖: StructuredArrow, StructuredArrow.proj, hasColimit_of_created
-/
lemma yonedaEquivFst_eq (p : YonedaCollection F X) : p.yonedaEquivFst = yonedaEquiv p.fst :=
  rfl

@[simp]
/--
lemma `mk_fst` / 引理 `mk_fst`

English:
lemma mk_fst
  given: (s : yoneda.obj X ⟶ A) (x : F.obj (op (CostructuredArrow.mk s)))
  statement: (mk s x).fst = s
  proof: Equiv.apply_symm_apply _ _

@[simp]

中文:
引理 mk_fst
  条件: (s : yoneda.obj X ⟶ A) (x : F.obj (op (CostructuredArrow.mk s)))
  结论: (mk s x).fst = s
  证明: Equiv.apply_symm_apply _ _

@[simp]

Depends on / 依赖: Equiv.apply_symm_apply, apply_symm_apply
-/
lemma mk_fst (s : yoneda.obj X ⟶ A) (x : F.obj (op (CostructuredArrow.mk s))) : (mk s x).fst = s :=
  Equiv.apply_symm_apply _ _

@[simp]
/--
lemma `mk_snd` / 引理 `mk_snd`

English:
lemma mk_snd
  given: (s : yoneda.obj X ⟶ A) (x : F.obj (op (CostructuredArrow.mk s)))
  proof: rfl

中文:
引理 mk_snd
  条件: (s : yoneda.obj X ⟶ A) (x : F.obj (op (CostructuredArrow.mk s)))
  证明: rfl
-/
lemma mk_snd (s : yoneda.obj X ⟶ A) (x : F.obj (op (CostructuredArrow.mk s))) :
    (mk s x).snd = F.map (eqToHom <| by rw [YonedaCollection.mk_fst]) x :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[ext (iff := false)]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  statement: {p q : YonedaCollection F X} (h : p.fst = q.fst)
  proof: by
  rcases p with ⟨p, p'⟩
  rcases q with ⟨q, q'⟩
  obtain rfl : p = q := yonedaEquiv.symm.injective h
  exact Sigma.ext rfl (by simpa [snd] using! h'.symm)

中文:
引理 ext
  结论: {p q : YonedaCollection F X} (h : p.fst = q.fst)
  证明: by
  rcases p with ⟨p, p'⟩
  rcases q with ⟨q, q'⟩
  obtain rfl : p = q := yonedaEquiv.symm.injective h
  exact Sigma.ext rfl (by simpa [snd] using! h'.symm)

Depends on / 依赖: Sigma.ext, injective, yonedaEquiv, yonedaEquiv.symm.injective
-/
lemma ext {p q : YonedaCollection F X} (h : p.fst = q.fst)
    (h' : F.map (eqToHom <| by rw [h]) q.snd = p.snd) : p = q := by
  rcases p with ⟨p, p'⟩
  rcases q with ⟨q, q'⟩
  obtain rfl : p = q := yonedaEquiv.symm.injective h
  exact Sigma.ext rfl (by simpa [snd] using! h'.symm)

/--
Definition of `map₁` / `map₁` 的定义

English:
definition map₁
  signature: {G : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v} (η : F ⟶ G)
  body: fun p => YonedaCollection.mk p.fst (η.app _ p.snd)

@[simp]

中文:
定义 map₁
  签名: {G : (CostructuredArrow yoneda A)ᵒᵖ ⥤ 类型v} (η : F ⟶ G)
  定义体: fun p => YonedaCollection.mk p.fst (η.app _ p.snd)

@[simp]

Depends on / 依赖: YonedaCollection, YonedaCollection.mk, p.fst, p.snd
-/
def map₁ {G : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v} (η : F ⟶ G) :
    YonedaCollection F X -> YonedaCollection G X :=
  fun p => YonedaCollection.mk p.fst (η.app _ p.snd)

@[simp]
/--
lemma `map₁_fst` / 引理 `map₁_fst`

English:
lemma map₁_fst
  statement: {G : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v} (η : F ⟶ G)
  proof: by
  simp [map₁]

@[simp]

中文:
引理 map₁_fst
  结论: {G : (CostructuredArrow yoneda A)ᵒᵖ ⥤ 类型v} (η : F ⟶ G)
  证明: by
  simp [map₁]

@[simp]
-/
lemma map₁_fst {G : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v} (η : F ⟶ G)
    (p : YonedaCollection F X) : (YonedaCollection.map₁ η p).fst = p.fst := by
  simp [map₁]

@[simp]
/--
lemma `map₁_yonedaEquivFst` / 引理 `map₁_yonedaEquivFst`

English:
lemma map₁_yonedaEquivFst
  statement: {G : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v} (η : F ⟶ G)
  proof: by
  simp only [YonedaCollection.yonedaEquivFst_eq, map₁_fst]

中文:
引理 map₁_yonedaEquivFst
  结论: {G : (CostructuredArrow yoneda A)ᵒᵖ ⥤ 类型v} (η : F ⟶ G)
  证明: by
  simp only [YonedaCollection.yonedaEquivFst_eq, map₁_fst]

Depends on / 依赖: YonedaCollection, YonedaCollection.yonedaEquivFst_eq, yonedaEquivFst_eq
-/
lemma map₁_yonedaEquivFst {G : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v} (η : F ⟶ G)
    (p : YonedaCollection F X) :
    (YonedaCollection.map₁ η p).yonedaEquivFst = p.yonedaEquivFst := by
  simp only [YonedaCollection.yonedaEquivFst_eq, map₁_fst]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `map₁_snd` / 引理 `map₁_snd`

English:
lemma map₁_snd
  statement: {G : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v} (η : F ⟶ G)
  proof: by
  simp [map₁]

中文:
引理 map₁_snd
  结论: {G : (CostructuredArrow yoneda A)ᵒᵖ ⥤ 类型v} (η : F ⟶ G)
  证明: by
  simp [map₁]

Depends on / 依赖: CostructuredArrow, CostructuredArrow.proj, CostructuredArrow.toOver, Limits, Limits.preservesLimit_of_reflects_of_preserves, Over.forget, PreservesLimit, forget, preservesLimit_of_reflects_of_preserves, toOver
-/
lemma map₁_snd {G : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v} (η : F ⟶ G)
    (p : YonedaCollection F X) : (YonedaCollection.map₁ η p).snd =
      G.map (eqToHom (by rw [YonedaCollection.map₁_fst])) (η.app _ p.snd) := by
  simp [map₁]

/--
Definition of `map₂` / `map₂` 的定义

English:
definition map₂
  signature: (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v) {Y : C} (f : X ⟶ Y)
  body: YonedaCollection.mk (yoneda.map f ≫ p.fst) F.map (CostructuredArrow.mkPrecomp p.fst f).op p.snd

@[simp]

中文:
定义 map₂
  签名: (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ 类型v) {Y : C} (f : X ⟶ Y)
  定义体: YonedaCollection.mk (yoneda.map f ≫ p.fst) F.map (CostructuredArrow.mkPrecomp p.fst f).op p.snd

@[simp]

Depends on / 依赖: CostructuredArrow, CostructuredArrow.mkPrecomp, F.map, YonedaCollection, YonedaCollection.mk, mkPrecomp, p.fst, p.snd, yoneda, yoneda.map
-/
def map₂ (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v) {Y : C} (f : X ⟶ Y)
    (p : YonedaCollection F Y) : YonedaCollection F X :=
YonedaCollection.mk (yoneda.map f ≫ p.fst) F.map (CostructuredArrow.mkPrecomp p.fst f).op p.snd

@[simp]
/--
lemma `map₂_fst` / 引理 `map₂_fst`

English:
lemma map₂_fst
  given: {Y : C} (f : X ⟶ Y) (p : YonedaCollection F Y)
  proof: by
  simp [map₂]

@[simp]

中文:
引理 map₂_fst
  条件: {Y : C} (f : X ⟶ Y) (p : YonedaCollection F Y)
  证明: by
  simp [map₂]

@[simp]
-/
lemma map₂_fst {Y : C} (f : X ⟶ Y) (p : YonedaCollection F Y) :
    (YonedaCollection.map₂ F f p).fst = yoneda.map f ≫ p.fst := by
  simp [map₂]

@[simp]
/--
lemma `map₂_yonedaEquivFst` / 引理 `map₂_yonedaEquivFst`

English:
lemma map₂_yonedaEquivFst
  given: {Y : C} (f : X ⟶ Y) (p : YonedaCollection F Y)
  proof: by
  simp only [YonedaCollection.yonedaEquivFst_eq, map₂_fst, yonedaEquiv_naturality]

中文:
引理 map₂_yonedaEquivFst
  条件: {Y : C} (f : X ⟶ Y) (p : YonedaCollection F Y)
  证明: by
  simp only [YonedaCollection.yonedaEquivFst_eq, map₂_fst, yonedaEquiv_naturality]

Depends on / 依赖: YonedaCollection, YonedaCollection.yonedaEquivFst_eq, yonedaEquivFst_eq, yonedaEquiv_naturality
-/
lemma map₂_yonedaEquivFst {Y : C} (f : X ⟶ Y) (p : YonedaCollection F Y) :
    (YonedaCollection.map₂ F f p).yonedaEquivFst = A.map f.op p.yonedaEquivFst := by
  simp only [YonedaCollection.yonedaEquivFst_eq, map₂_fst, yonedaEquiv_naturality]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `map₂_snd` / 引理 `map₂_snd`

English:
lemma map₂_snd
  given: {Y : C} (f : X ⟶ Y) (p : YonedaCollection F Y)
  proof: by
  simp [map₂]

中文:
引理 map₂_snd
  条件: {Y : C} (f : X ⟶ Y) (p : YonedaCollection F Y)
  证明: by
  simp [map₂]

Depends on / 依赖: Limits, Limits.preservesColimit_of_reflects_of_preserves, PreservesColimit, StructuredArrow, StructuredArrow.proj, StructuredArrow.toUnder, Under.forget, forget, preservesColimit_of_reflects_of_preserves, toUnder
-/
lemma map₂_snd {Y : C} (f : X ⟶ Y) (p : YonedaCollection F Y) :
    (YonedaCollection.map₂ F f p).snd = F.map ((CostructuredArrow.mkPrecomp p.fst f).op ≫
      eqToHom (by rw [YonedaCollection.map₂_fst f])) p.snd := by
  simp [map₂]

attribute [local simp] CostructuredArrow.mkPrecomp_id CostructuredArrow.mkPrecomp_comp

@[simp]
/--
lemma `map₁_id` / 引理 `map₁_id`

English:
lemma map₁_id
  statement: YonedaCollection.map₁ (𝟙 F) (X := X) = id
  proof: by
  cat_disch

中文:
引理 map₁_id
  结论: YonedaCollection.map₁ (𝟙 F) (X := X) = id
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
lemma map₁_id : YonedaCollection.map₁ (𝟙 F) (X := X) = id := by
  cat_disch

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `map₁_comp` / 引理 `map₁_comp`

English:
lemma map₁_comp
  given: {G H : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v} (η : F ⟶ G) (μ : G ⟶ H)
  proof: by
  ext; all_goals simp

中文:
引理 map₁_comp
  条件: {G H : (CostructuredArrow yoneda A)ᵒᵖ ⥤ 类型v} (η : F ⟶ G) (μ : G ⟶ H)
  证明: by
  ext; all_goals simp
-/
lemma map₁_comp {G H : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v} (η : F ⟶ G) (μ : G ⟶ H) :
    YonedaCollection.map₁ (η ≫ μ) (X := X) =
      YonedaCollection.map₁ μ (X := X) ∘ YonedaCollection.map₁ η (X := X) := by
  ext; all_goals simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `map₂_id` / 引理 `map₂_id`

English:
lemma map₂_id
  statement: YonedaCollection.map₂ F (𝟙 X) = id
  proof: by
  ext; all_goals simp

中文:
引理 map₂_id
  结论: YonedaCollection.map₂ F (𝟙 X) = id
  证明: by
  ext; all_goals simp

Depends on / 依赖: all_goals
-/
lemma map₂_id : YonedaCollection.map₂ F (𝟙 X) = id := by
  ext; all_goals simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `map₂_comp` / 引理 `map₂_comp`

English:
lemma map₂_comp
  given: {Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: by
  ext; all_goals simp

@[simp]

中文:
引理 map₂_comp
  条件: {Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: by
  ext; all_goals simp

@[simp]

Depends on / 依赖: all_goals
-/
lemma map₂_comp {Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    YonedaCollection.map₂ F (f ≫ g) = YonedaCollection.map₂ F f ∘ YonedaCollection.map₂ F g := by
  ext; all_goals simp

@[simp]
/--
lemma `map₁_map₂` / 引理 `map₁_map₂`

English:
lemma map₁_map₂
  statement: {G : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v} (η : F ⟶ G) {Y : C} (f : X ⟶ Y)
  proof: by
  ext; all_goals simp

中文:
引理 map₁_map₂
  结论: {G : (CostructuredArrow yoneda A)ᵒᵖ ⥤ 类型v} (η : F ⟶ G) {Y : C} (f : X ⟶ Y)
  证明: by
  ext; all_goals simp

Depends on / 依赖: all_goals
-/
lemma map₁_map₂ {G : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v} (η : F ⟶ G) {Y : C} (f : X ⟶ Y)
    (p : YonedaCollection F Y) :
    YonedaCollection.map₂ G f (YonedaCollection.map₁ η p) =
      YonedaCollection.map₁ η (YonedaCollection.map₂ F f p) := by
  ext; all_goals simp

end YonedaCollection

/-- Given `F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v`, this is the presheaf that is given by
`YonedaCollection F X` on objects. -/
@[simps]
/--
Definition of `yonedaCollectionPresheaf` / `yonedaCollectionPresheaf` 的定义

English:
definition yonedaCollectionPresheaf
  signature: (A : Cᵒᵖ ⥤ Type v) (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v)
  body: YonedaCollection F X.unop
  map f := ↾(YonedaCollection.map₂ F f.unop)

中文:
定义 yonedaCollectionPresheaf
  签名: (A : Cᵒᵖ ⥤ 类型v) (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ 类型v)
  定义体: YonedaCollection F X.unop
  map f := ↾(YonedaCollection.map₂ F f.unop)

Depends on / 依赖: X.unop, YonedaCollection
-/
def yonedaCollectionPresheaf (A : Cᵒᵖ ⥤ Type v) (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v) :
    Cᵒᵖ ⥤ Type v where
  obj X := YonedaCollection F X.unop
  map f := ↾(YonedaCollection.map₂ F f.unop)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Functoriality of `yonedaCollectionPresheaf A F` in `F`. -/
@[simps]
/--
Definition of `yonedaCollectionPresheafMap₁` / `yonedaCollectionPresheafMap₁` 的定义

English:
definition yonedaCollectionPresheafMap₁
  signature: {F G : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v} (η : F ⟶ G)
  body: ↾(YonedaCollection.map₁ η)
  naturality := by
    intros
    ext
    simp

中文:
定义 yonedaCollectionPresheafMap₁
  签名: {F G : (CostructuredArrow yoneda A)ᵒᵖ ⥤ 类型v} (η : F ⟶ G)
  定义体: ↾(YonedaCollection.map₁ η)
  naturality := by
    intros
    ext
    simp

Depends on / 依赖: YonedaCollection, YonedaCollection.map
-/
def yonedaCollectionPresheafMap₁ {F G : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v} (η : F ⟶ G) :
    yonedaCollectionPresheaf A F ⟶ yonedaCollectionPresheaf A G where
  app _ := ↾(YonedaCollection.map₁ η)
  naturality := by
    intros
    ext
    simp

/-- This is the functor `F ↦ X ↦ YonedaCollection F X`. -/
@[simps]
/--
Definition of `yonedaCollectionFunctor` / `yonedaCollectionFunctor` 的定义

English:
definition yonedaCollectionFunctor
  signature: (A : Cᵒᵖ ⥤ Type v)
  body: yonedaCollectionPresheaf A
  map η := yonedaCollectionPresheafMap₁ η

中文:
定义 yonedaCollectionFunctor
  签名: (A : Cᵒᵖ ⥤ 类型v)
  定义体: yonedaCollectionPresheaf A
  map η := yonedaCollectionPresheafMap₁ η

Depends on / 依赖: yonedaCollectionPresheaf
-/
def yonedaCollectionFunctor (A : Cᵒᵖ ⥤ Type v) :
    ((CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v) ⥤ Cᵒᵖ ⥤ Type v where
  obj := yonedaCollectionPresheaf A
  map η := yonedaCollectionPresheafMap₁ η

set_option backward.defeqAttrib.useBackward true in
/-- The Yoneda lemma yields a natural transformation `yonedaCollectionPresheaf A F ⟶ A`. -/
@[simps]
/--
Definition of `yonedaCollectionPresheafToA` / `yonedaCollectionPresheafToA` 的定义

English:
definition yonedaCollectionPresheafToA
  signature: (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v)
  body: ↾(YonedaCollection.yonedaEquivFst)

中文:
定义 yonedaCollectionPresheafToA
  签名: (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ 类型v)
  定义体: ↾(YonedaCollection.yonedaEquivFst)

Depends on / 依赖: YonedaCollection, YonedaCollection.yonedaEquivFst, yonedaEquivFst
-/
def yonedaCollectionPresheafToA (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v) :
    yonedaCollectionPresheaf A F ⟶ A where
  app _ := ↾(YonedaCollection.yonedaEquivFst)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- This is the reverse direction of the equivalence we're constructing. -/
@[simps! obj map]
/--
Definition of `costructuredArrowPresheafToOver` / `costructuredArrowPresheafToOver` 的定义

English:
definition costructuredArrowPresheafToOver
  signature: (A : Cᵒᵖ ⥤ Type v)
  body: (yonedaCollectionFunctor A).toOver _ (yonedaCollectionPresheafToA) (by cat_disch)

中文:
定义 costructuredArrowPresheafToOver
  签名: (A : Cᵒᵖ ⥤ 类型v)
  定义体: (yonedaCollectionFunctor A).toOver _ (yonedaCollectionPresheafToA) (by cat_disch)

Depends on / 依赖: cat_disch, toOver, yonedaCollectionFunctor, yonedaCollectionPresheafToA
-/
def costructuredArrowPresheafToOver (A : Cᵒᵖ ⥤ Type v) :
    ((CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v) ⥤ Over A :=
  (yonedaCollectionFunctor A).toOver _ (yonedaCollectionPresheafToA) (by cat_disch)

section unit

/-! ### Construction of the unit -/

/--
Definition of `unitForward` / `unitForward` 的定义

English:
definition unitForward
  signature: {F : Cᵒᵖ ⥤ Type v} (η : F ⟶ A) (X : C)
  body: fun p => p.snd.val

中文:
定义 unitForward
  签名: {F : Cᵒᵖ ⥤ 类型v} (η : F ⟶ A) (X : C)
  定义体: fun p => p.snd.val

Depends on / 依赖: p.snd.val
-/
def unitForward {F : Cᵒᵖ ⥤ Type v} (η : F ⟶ A) (X : C) :
    YonedaCollection (restrictedYonedaObj η) X -> F.obj (op X) :=
  fun p => p.snd.val

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `unitForward_naturality₁` / 引理 `unitForward_naturality₁`

English:
lemma unitForward_naturality₁
  statement: {F G : Cᵒᵖ ⥤ Type v} {η : F ⟶ A} {μ : G ⟶ A} (ε : F ⟶ G)
  proof: by
  simp [unitForward]

中文:
引理 unitForward_naturality₁
  结论: {F G : Cᵒᵖ ⥤ 类型v} {η : F ⟶ A} {μ : G ⟶ A} (ε : F ⟶ G)
  证明: by
  simp [unitForward]

Depends on / 依赖: unitForward
-/
lemma unitForward_naturality₁ {F G : Cᵒᵖ ⥤ Type v} {η : F ⟶ A} {μ : G ⟶ A} (ε : F ⟶ G)
    (hε : ε ≫ μ = η) (X : C) (p : YonedaCollection (restrictedYonedaObj η) X) :
    unitForward μ X (p.map₁ (restrictedYonedaObjMap₁ ε hε)) = ε.app _ (unitForward η X p) := by
  simp [unitForward]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `unitForward_naturality₂` / 引理 `unitForward_naturality₂`

English:
lemma unitForward_naturality₂
  statement: {F : Cᵒᵖ ⥤ Type v} (η : F ⟶ A) (X Y : C) (f : X ⟶ Y)
  proof: by
  simp [unitForward]

@[simp]

中文:
引理 unitForward_naturality₂
  结论: {F : Cᵒᵖ ⥤ 类型v} (η : F ⟶ A) (X Y : C) (f : X ⟶ Y)
  证明: by
  simp [unitForward]

@[simp]

Depends on / 依赖: unitForward
-/
lemma unitForward_naturality₂ {F : Cᵒᵖ ⥤ Type v} (η : F ⟶ A) (X Y : C) (f : X ⟶ Y)
    (p : YonedaCollection (restrictedYonedaObj η) Y) :
    unitForward η X (YonedaCollection.map₂ (restrictedYonedaObj η) f p) =
      F.map f.op (unitForward η Y p) := by
  simp [unitForward]

@[simp]
/--
lemma `app_unitForward` / 引理 `app_unitForward`

English:
lemma app_unitForward
  statement: {F : Cᵒᵖ ⥤ Type v} (η : F ⟶ A) (X : Cᵒᵖ)
  proof: by
  simpa [unitForward] using! p.snd.app_val

中文:
引理 app_unitForward
  结论: {F : Cᵒᵖ ⥤ 类型v} (η : F ⟶ A) (X : Cᵒᵖ)
  证明: by
  simpa [unitForward] using! p.snd.app_val

Depends on / 依赖: app_val, p.snd.app_val, unitForward
-/
lemma app_unitForward {F : Cᵒᵖ ⥤ Type v} (η : F ⟶ A) (X : Cᵒᵖ)
    (p : YonedaCollection (restrictedYonedaObj η) X.unop) :
    η.app X (unitForward η X.unop p) = p.yonedaEquivFst := by
  simpa [unitForward] using! p.snd.app_val

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `unitBackward` / `unitBackward` 的定义

English:
definition unitBackward
  signature: {F : Cᵒᵖ ⥤ Type v} (η : F ⟶ A) (X : C)
  body: fun x => YonedaCollection.mk (yonedaEquiv.symm (η.app _ x)) ⟨x, ⟨by simp⟩⟩

中文:
定义 unitBackward
  签名: {F : Cᵒᵖ ⥤ 类型v} (η : F ⟶ A) (X : C)
  定义体: fun x => YonedaCollection.mk (yonedaEquiv.symm (η.app _ x)) ⟨x, ⟨by simp⟩⟩

Depends on / 依赖: YonedaCollection, YonedaCollection.mk, yonedaEquiv, yonedaEquiv.symm
-/
def unitBackward {F : Cᵒᵖ ⥤ Type v} (η : F ⟶ A) (X : C) :
    F.obj (op X) -> YonedaCollection (restrictedYonedaObj η) X :=
  fun x => YonedaCollection.mk (yonedaEquiv.symm (η.app _ x)) ⟨x, ⟨by simp⟩⟩

set_option backward.isDefEq.respectTransparency false in
/--
lemma `unitForward_unitBackward` / 引理 `unitForward_unitBackward`

English:
lemma unitForward_unitBackward
  given: {F : Cᵒᵖ ⥤ Type v} (η : F ⟶ A) (X : C)
  proof: funext fun x => by simp [unitForward, unitBackward]

中文:
引理 unitForward_unitBackward
  条件: {F : Cᵒᵖ ⥤ 类型v} (η : F ⟶ A) (X : C)
  证明: funext fun x => by simp [unitForward, unitBackward]

Depends on / 依赖: unitBackward, unitForward
-/
lemma unitForward_unitBackward {F : Cᵒᵖ ⥤ Type v} (η : F ⟶ A) (X : C) :
    unitForward η X ∘ unitBackward η X = id :=
  funext fun x => by simp [unitForward, unitBackward]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `unitBackward_unitForward` / 引理 `unitBackward_unitForward`

English:
lemma unitBackward_unitForward
  given: {F : Cᵒᵖ ⥤ Type v} (η : F ⟶ A) (X : C)
  proof: by
  refine funext fun p => YonedaCollection.ext ?_ (OverArrows.ext ?_)
  · simpa [unitForward, unitBackward] using congrArg yonedaEquiv.symm p.snd.app_val
  · simp [unitForward, unitBackward]

中文:
引理 unitBackward_unitForward
  条件: {F : Cᵒᵖ ⥤ 类型v} (η : F ⟶ A) (X : C)
  证明: by
  refine funext fun p => YonedaCollection.ext ?_ (OverArrows.ext ?_)
  · simpa [unitForward, unitBackward] using congrArg yonedaEquiv.symm p.snd.app_val
  · simp [unitForward, unitBackward]

Depends on / 依赖: OverArrows, OverArrows.ext, YonedaCollection, YonedaCollection.ext, app_val, p.snd.app_val, unitBackward, unitForward, yonedaEquiv, yonedaEquiv.symm
-/
lemma unitBackward_unitForward {F : Cᵒᵖ ⥤ Type v} (η : F ⟶ A) (X : C) :
    unitBackward η X ∘ unitForward η X = id := by
  refine funext fun p => YonedaCollection.ext ?_ (OverArrows.ext ?_)
  · simpa [unitForward, unitBackward] using congrArg yonedaEquiv.symm p.snd.app_val
  · simp [unitForward, unitBackward]

/-- Intermediate stage of assembling the unit. -/
@[simps]
/--
Definition of `unitAuxAuxAux` / `unitAuxAuxAux` 的定义

English:
definition unitAuxAuxAux
  signature: {F : Cᵒᵖ ⥤ Type v} (η : F ⟶ A) (X : C)
  body: ↾(unitForward η X)
  inv := ↾(unitBackward η X)
  hom_inv_id := ConcreteCategory.ext (TypeCat.Fun.ext (unitBackward_unitForward η X))
  inv_hom_id := ConcreteCategory.ext (TypeCat.Fun.ext (unitForward_unitBackward η X))

中文:
定义 unitAuxAuxAux
  签名: {F : Cᵒᵖ ⥤ 类型v} (η : F ⟶ A) (X : C)
  定义体: ↾(unitForward η X)
  inv := ↾(unitBackward η X)
  hom_inv_id := ConcreteCategory.ext (TypeCat.Fun.ext (unitBackward_unitForward η X))
  inv_hom_id := ConcreteCategory.ext (TypeCat.Fun.ext (unitForward_unitBackward η X))

Depends on / 依赖: unitForward
-/
def unitAuxAuxAux {F : Cᵒᵖ ⥤ Type v} (η : F ⟶ A) (X : C) :
    YonedaCollection (restrictedYonedaObj η) X ≅ F.obj (op X) where
  hom := ↾(unitForward η X)
  inv := ↾(unitBackward η X)
  hom_inv_id := ConcreteCategory.ext (TypeCat.Fun.ext (unitBackward_unitForward η X))
  inv_hom_id := ConcreteCategory.ext (TypeCat.Fun.ext (unitForward_unitBackward η X))

set_option backward.defeqAttrib.useBackward true in
/-- Intermediate stage of assembling the unit. -/
@[simps! inv_app hom_app]
/--
Definition of `unitAuxAux` / `unitAuxAux` 的定义

English:
definition unitAuxAux
  signature: {F : Cᵒᵖ ⥤ Type v} (η : F ⟶ A)
  body: NatIso.ofComponents (fun X => unitAuxAuxAux η X.unop)

中文:
定义 unitAuxAux
  签名: {F : Cᵒᵖ ⥤ 类型v} (η : F ⟶ A)
  定义体: NatIso.ofComponents (fun X => unitAuxAuxAux η X.unop)

Depends on / 依赖: NatIso, NatIso.ofComponents, X.unop, ofComponents, unitAuxAuxAux
-/
def unitAuxAux {F : Cᵒᵖ ⥤ Type v} (η : F ⟶ A) :
    yonedaCollectionPresheaf A (restrictedYonedaObj η) ≅ F :=
  NatIso.ofComponents (fun X => unitAuxAuxAux η X.unop)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Intermediate stage of assembling the unit. -/
@[simps! hom_left]
/--
Definition of `unitAux` / `unitAux` 的定义

English:
definition unitAux
  signature: (η : Over A)
  body: Over.isoMk (unitAuxAux η.hom)

中文:
定义 unitAux
  签名: (η : Over A)
  定义体: Over.isoMk (unitAuxAux η.hom)

Depends on / 依赖: Over.isoMk, unitAuxAux
-/
def unitAux (η : Over A) : (restrictedYoneda A ⋙ costructuredArrowPresheafToOver A).obj η ≅ η :=
  Over.isoMk (unitAuxAux η.hom)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `unit` / `unit` 的定义

English:
definition unit
  signature: (A : Cᵒᵖ ⥤ Type v)
  body: Iso.symm NatIso.ofComponents unitAux

中文:
定义 unit
  签名: (A : Cᵒᵖ ⥤ 类型v)
  定义体: Iso.symm NatIso.ofComponents unitAux

Depends on / 依赖: Iso.symm, NatIso, NatIso.ofComponents, ofComponents, unitAux
-/
def unit (A : Cᵒᵖ ⥤ Type v) : 𝟭 (Over A) ≅ restrictedYoneda A ⋙ costructuredArrowPresheafToOver A :=
Iso.symm NatIso.ofComponents unitAux

end unit

/-! ### Construction of the counit -/

section counit

variable {F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v} {X : C}

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `OverArrows.yonedaCollectionPresheafToA_val_fst` / 引理 `OverArrows.yonedaCollectionPresheafToA_val_fst`

English:
lemma OverArrows.yonedaCollectionPresheafToA_val_fst
  statement: (s : yoneda.obj X ⟶ A)
  proof: by
  simpa [YonedaCollection.yonedaEquivFst_eq] using p.app_val

中文:
引理 OverArrows.yonedaCollectionPresheafToA_val_fst
  结论: (s : yoneda.obj X ⟶ A)
  证明: by
  simpa [YonedaCollection.yonedaEquivFst_eq] using p.app_val

Depends on / 依赖: YonedaCollection, YonedaCollection.yonedaEquivFst_eq, app_val, p.app_val, yonedaEquivFst_eq
-/
lemma OverArrows.yonedaCollectionPresheafToA_val_fst (s : yoneda.obj X ⟶ A)
    (p : OverArrows (yonedaCollectionPresheafToA F) s) : p.val.fst = s := by
  simpa [YonedaCollection.yonedaEquivFst_eq] using p.app_val

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `counitForward` / `counitForward` 的定义

English:
definition counitForward
  signature: (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v)
  body: fun x => ⟨YonedaCollection.mk s.hom x, ⟨by simp [YonedaCollection.yonedaEquivFst_eq]⟩⟩

中文:
定义 counitForward
  签名: (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ 类型v)
  定义体: fun x => ⟨YonedaCollection.mk s.hom x, ⟨by simp [YonedaCollection.yonedaEquivFst_eq]⟩⟩

Depends on / 依赖: YonedaCollection, YonedaCollection.mk, YonedaCollection.yonedaEquivFst_eq, s.hom, yonedaEquivFst_eq
-/
def counitForward (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v)
    (s : CostructuredArrow yoneda A) :
    F.obj (op s) -> OverArrows (yonedaCollectionPresheafToA F) s.hom :=
  fun x => ⟨YonedaCollection.mk s.hom x, ⟨by simp [YonedaCollection.yonedaEquivFst_eq]⟩⟩

/--
lemma `counitForward_val_fst` / 引理 `counitForward_val_fst`

English:
lemma counitForward_val_fst
  given: (s : CostructuredArrow yoneda A) (x : F.obj (op s))
  proof: by
  simp

@[simp]

中文:
引理 counitForward_val_fst
  条件: (s : CostructuredArrow yoneda A) (x : F.obj (op s))
  证明: by
  simp

@[simp]
-/
lemma counitForward_val_fst (s : CostructuredArrow yoneda A) (x : F.obj (op s)) :
    (counitForward F s x).val.fst = s.hom := by
  simp

@[simp]
/--
lemma `counitForward_val_snd` / 引理 `counitForward_val_snd`

English:
lemma counitForward_val_snd
  given: (s : CostructuredArrow yoneda A) (x : F.obj (op s))
  proof: YonedaCollection.mk_snd _ _

中文:
引理 counitForward_val_snd
  条件: (s : CostructuredArrow yoneda A) (x : F.obj (op s))
  证明: YonedaCollection.mk_snd _ _

Depends on / 依赖: YonedaCollection, YonedaCollection.mk_snd, mk_snd
-/
lemma counitForward_val_snd (s : CostructuredArrow yoneda A) (x : F.obj (op s)) :
    (counitForward F s x).val.snd = F.map (eqToHom (by simp [← CostructuredArrow.eq_mk])) x :=
  YonedaCollection.mk_snd _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `counitForward_naturality₁` / 引理 `counitForward_naturality₁`

English:
lemma counitForward_naturality₁
  statement: {G : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v} (η : F ⟶ G)
  proof: OverArrows.ext YonedaCollection.ext (by simp) (by simp)

中文:
引理 counitForward_naturality₁
  结论: {G : (CostructuredArrow yoneda A)ᵒᵖ ⥤ 类型v} (η : F ⟶ G)
  证明: OverArrows.ext YonedaCollection.ext (by simp) (by simp)

Depends on / 依赖: OverArrows, OverArrows.ext, YonedaCollection, YonedaCollection.ext
-/
lemma counitForward_naturality₁ {G : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v} (η : F ⟶ G)
    (s : (CostructuredArrow yoneda A)ᵒᵖ) (x : F.obj s) : counitForward G s.unop (η.app s x) =
      OverArrows.map₁ (counitForward F s.unop x) (yonedaCollectionPresheafMap₁ η) (by cat_disch) :=
OverArrows.ext YonedaCollection.ext (by simp) (by simp)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `counitForward_naturality₂` / 引理 `counitForward_naturality₂`

English:
lemma counitForward_naturality₂
  given: (s t : (CostructuredArrow yoneda A)ᵒᵖ) (f : t ⟶ s) (x : F.obj t)
  proof: by
refine OverArrows.ext YonedaCollection.ext (by simp) ?_
  have : (CostructuredArrow.mkPrecomp t.unop.hom f.unop.left).op =
      f ≫ eqToHom (by simp [← CostructuredArrow.eq_mk]) := by
    apply Quiver.Hom.unop_inj
    simp
  have : F.map (CostructuredArrow.mkPrecomp
      (YonedaCollection.fst (

中文:
引理 counitForward_naturality₂
  条件: (s t : (CostructuredArrow yoneda A)ᵒᵖ) (f : t ⟶ s) (x : F.obj t)
  证明: by
refine OverArrows.ext YonedaCollection.ext (by simp) ?_
  have : (CostructuredArrow.mkPrecomp t.unop.hom f.unop.left).op =
      f ≫ eqToHom (by simp [← CostructuredArrow.eq_mk]) := by
    apply Quiver.Hom.unop_inj
    simp
  have : F.map (CostructuredArrow.mkPrecomp
      (YonedaCollection.fst (

Depends on / 依赖: CostructuredArrow, CostructuredArrow.eq_mk, CostructuredArrow.mkPrecomp, F.map, OverArrows, OverArrows.ext, Quiver, Quiver.Hom.unop_inj, YonedaCollection, YonedaCollection.ext, YonedaCollection.fst, cat_disch, counitForward, eqToHom, eq_mk, f.unop.left, map_mkPrecomp_eqToHom, mkPrecomp, t.unop.hom, unop_inj
-/
lemma counitForward_naturality₂ (s t : (CostructuredArrow yoneda A)ᵒᵖ) (f : t ⟶ s) (x : F.obj t) :
    counitForward F s.unop (F.map f x) =
      OverArrows.map₂ (counitForward F t.unop x) f.unop.left (by simp) := by
refine OverArrows.ext YonedaCollection.ext (by simp) ?_
  have : (CostructuredArrow.mkPrecomp t.unop.hom f.unop.left).op =
      f ≫ eqToHom (by simp [← CostructuredArrow.eq_mk]) := by
    apply Quiver.Hom.unop_inj
    simp
  have : F.map (CostructuredArrow.mkPrecomp
      (YonedaCollection.fst (counitForward F (unop t) x).val) f.unop.left).op
      (F.map (eqToHom (by simp; rfl)) x) = _ :=
    map_mkPrecomp_eqToHom (h := by simp)
  cat_disch

/--
Definition of `counitBackward` / `counitBackward` 的定义

English:
definition counitBackward
  signature: (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v)
  body: fun p => F.map (eqToHom (by simp [← CostructuredArrow.eq_mk])) p.val.snd

中文:
定义 counitBackward
  签名: (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ 类型v)
  定义体: fun p => F.map (eqToHom (by simp [← CostructuredArrow.eq_mk])) p.val.snd

Depends on / 依赖: CostructuredArrow, CostructuredArrow.eq_mk, F.map, eqToHom, eq_mk, isConnected_iff_final_of_unique, p.val.snd
-/
def counitBackward (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v)
    (s : CostructuredArrow yoneda A) :
    OverArrows (yonedaCollectionPresheafToA F) s.hom -> F.obj (op s) :=
  fun p => F.map (eqToHom (by simp [← CostructuredArrow.eq_mk])) p.val.snd

set_option backward.isDefEq.respectTransparency false in
/--
lemma `counitForward_counitBackward` / 引理 `counitForward_counitBackward`

English:
lemma counitForward_counitBackward
  statement: (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v)
  proof: funext fun p => OverArrows.ext YonedaCollection.ext (by simp) (by simp [counitBackward])

中文:
引理 counitForward_counitBackward
  结论: (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ 类型v)
  证明: funext fun p => OverArrows.ext YonedaCollection.ext (by simp) (by simp [counitBackward])

Depends on / 依赖: OverArrows, OverArrows.ext, YonedaCollection, YonedaCollection.ext, counitBackward, isConnected_iff_initial_of_unique
-/
lemma counitForward_counitBackward (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v)
    (s : CostructuredArrow yoneda A) : counitForward F s ∘ counitBackward F s = id :=
funext fun p => OverArrows.ext YonedaCollection.ext (by simp) (by simp [counitBackward])

/--
lemma `counitBackward_counitForward` / 引理 `counitBackward_counitForward`

English:
lemma counitBackward_counitForward
  statement: (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v)
  proof: funext fun x => by simp [counitBackward]

中文:
引理 counitBackward_counitForward
  结论: (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ 类型v)
  证明: funext fun x => by simp [counitBackward]

Depends on / 依赖: counitBackward
-/
lemma counitBackward_counitForward (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v)
    (s : CostructuredArrow yoneda A) : counitBackward F s ∘ counitForward F s = id :=
  funext fun x => by simp [counitBackward]

/-- Intermediate stage of assembling the counit. -/
@[simps]
/--
Definition of `counitAuxAux` / `counitAuxAux` 的定义

English:
definition counitAuxAux
  signature: (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v)
  body: ↾(counitForward F s)
  inv := ↾(counitBackward F s)
  hom_inv_id := ConcreteCategory.ext (TypeCat.Fun.ext (counitBackward_counitForward F s))
  inv_hom_id := ConcreteCategory.ext (TypeCat.Fun.ext (counitForward_counitBackward F s))

中文:
定义 counitAuxAux
  签名: (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ 类型v)
  定义体: ↾(counitForward F s)
  inv := ↾(counitBackward F s)
  hom_inv_id := ConcreteCategory.ext (TypeCat.Fun.ext (counitBackward_counitForward F s))
  inv_hom_id := ConcreteCategory.ext (TypeCat.Fun.ext (counitForward_counitBackward F s))

Depends on / 依赖: counitForward
-/
def counitAuxAux (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v)
    (s : CostructuredArrow yoneda A) :
    F.obj (op s) ≅ OverArrows (yonedaCollectionPresheafToA F) s.hom where
  hom := ↾(counitForward F s)
  inv := ↾(counitBackward F s)
  hom_inv_id := ConcreteCategory.ext (TypeCat.Fun.ext (counitBackward_counitForward F s))
  inv_hom_id := ConcreteCategory.ext (TypeCat.Fun.ext (counitForward_counitBackward F s))

set_option backward.defeqAttrib.useBackward true in
/-- Intermediate stage of assembling the counit. -/
@[simps! hom]
/--
Definition of `counitAux` / `counitAux` 的定义

English:
definition counitAux
  signature: (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v)
  body: NatIso.ofComponents (fun s => counitAuxAux F s.unop) (by cat_disch)

中文:
定义 counitAux
  签名: (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ 类型v)
  定义体: NatIso.ofComponents (fun s => counitAuxAux F s.unop) (by cat_disch)

Depends on / 依赖: NatIso, NatIso.ofComponents, cat_disch, counitAuxAux, ofComponents, s.unop
-/
def counitAux (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v) :
    F ≅ restrictedYonedaObj (yonedaCollectionPresheafToA F) :=
  NatIso.ofComponents (fun s => counitAuxAux F s.unop) (by cat_disch)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `counit` / `counit` 的定义

English:
definition counit
  signature: (A : Cᵒᵖ ⥤ Type v)
  body: Iso.symm NatIso.ofComponents counitAux (by cat_disch)

中文:
定义 counit
  签名: (A : Cᵒᵖ ⥤ 类型v)
  定义体: Iso.symm NatIso.ofComponents counitAux (by cat_disch)

Depends on / 依赖: Iso.symm, NatIso, NatIso.ofComponents, cat_disch, counitAux, ofComponents
-/
def counit (A : Cᵒᵖ ⥤ Type v) :
    (costructuredArrowPresheafToOver A ⋙ restrictedYoneda A) ≅ 𝟭 _ :=
Iso.symm NatIso.ofComponents counitAux (by cat_disch)

end counit

end OverPresheafAux

open OverPresheafAux

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `overEquivPresheafCostructuredArrow` / `overEquivPresheafCostructuredArrow` 的定义

English:
definition overEquivPresheafCostructuredArrow
  signature: (A : Cᵒᵖ ⥤ Type v)
  body: .mk (restrictedYoneda A) (costructuredArrowPresheafToOver A) (unit A) (counit A)

中文:
定义 overEquivPresheafCostructuredArrow
  签名: (A : Cᵒᵖ ⥤ 类型v)
  定义体: .mk (restrictedYoneda A) (costructuredArrowPresheafToOver A) (unit A) (counit A)

Depends on / 依赖: costructuredArrowPresheafToOver, counit, restrictedYoneda
-/
def overEquivPresheafCostructuredArrow (A : Cᵒᵖ ⥤ Type v) :
    Over A ≌ ((CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v) :=
  .mk (restrictedYoneda A) (costructuredArrowPresheafToOver A) (unit A) (counit A)

/--
Definition of `CostructuredArrow.toOverCompOverEquivPresheafCostructuredArrow` / `CostructuredArrow.toOverCompOverEquivPresheafCostructuredArrow` 的定义

English:
definition CostructuredArrow.toOverCompOverEquivPresheafCostructuredArrow
  signature: (A : Cᵒᵖ ⥤ Type v)
  body: toOverYonedaCompRestrictedYoneda A

中文:
定义 CostructuredArrow.toOverCompOverEquivPresheafCostructuredArrow
  签名: (A : Cᵒᵖ ⥤ 类型v)
  定义体: toOverYonedaCompRestrictedYoneda A

Depends on / 依赖: toOverYonedaCompRestrictedYoneda
-/
def CostructuredArrow.toOverCompOverEquivPresheafCostructuredArrow (A : Cᵒᵖ ⥤ Type v) :
    CostructuredArrow.toOver yoneda A ⋙ (overEquivPresheafCostructuredArrow A).functor ≅ yoneda :=
  toOverYonedaCompRestrictedYoneda A

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `CostructuredArrow.toOverCompYoneda` / `CostructuredArrow.toOverCompYoneda` 的定义

English:
definition CostructuredArrow.toOverCompYoneda
  signature: (A : Cᵒᵖ ⥤ Type v) (T : Over A)
  body: NatIso.ofComponents (fun X =>
    (overEquivPresheafCostructuredArrow A).fullyFaithfulFunctor.homEquiv.toIso ≪≫
      (Iso.homCongr
        ((CostructuredArrow.toOverCompOverEquivPresheafCostructuredArrow A).app X.unop)
        (Iso.refl _)).toIso)
    (by cat_disch)

中文:
定义 CostructuredArrow.toOverCompYoneda
  签名: (A : Cᵒᵖ ⥤ 类型v) (T : Over A)
  定义体: NatIso.ofComponents (fun X =>
    (overEquivPresheafCostructuredArrow A).fullyFaithfulFunctor.homEquiv.toIso ≪≫
      (Iso.homCongr
        ((CostructuredArrow.toOverCompOverEquivPresheafCostructuredArrow A).app X.unop)
        (Iso.refl _)).toIso)
    (by cat_disch)

Depends on / 依赖: CostructuredArrow, CostructuredArrow.toOverCompOverEquivPresheafCostructuredArrow, Iso.homCongr, Iso.refl, NatIso, NatIso.ofComponents, X.unop, cat_disch, fullyFaithfulFunctor, fullyFaithfulFunctor.homEquiv.toIso, homCongr, homEquiv, ofComponents, overEquivPresheafCostructuredArrow, toOverCompOverEquivPresheafCostructuredArrow
-/
def CostructuredArrow.toOverCompYoneda (A : Cᵒᵖ ⥤ Type v) (T : Over A) :
    (CostructuredArrow.toOver yoneda A).op ⋙ yoneda.obj T ≅
      yoneda.op ⋙ yoneda.obj ((overEquivPresheafCostructuredArrow A).functor.obj T) :=
  NatIso.ofComponents (fun X =>
    (overEquivPresheafCostructuredArrow A).fullyFaithfulFunctor.homEquiv.toIso ≪≫
      (Iso.homCongr
        ((CostructuredArrow.toOverCompOverEquivPresheafCostructuredArrow A).app X.unop)
        (Iso.refl _)).toIso)
    (by cat_disch)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `CostructuredArrow.overEquivPresheafCostructuredArrow_inverse_map_toOverCompYoneda` / 定理 `CostructuredArrow.overEquivPresheafCostructuredArrow_inverse_map_toOverCompYoneda`

English:
theorem CostructuredArrow.overEquivPresheafCostructuredArrow_inverse_map_toOverCompYoneda
  proof: by
  simp [CostructuredArrow.toOverCompYoneda]

中文:
定理 CostructuredArrow.overEquivPresheafCostructuredArrow_inverse_map_toOverCompYoneda
  证明: by
  simp [CostructuredArrow.toOverCompYoneda]

Depends on / 依赖: CostructuredArrow, CostructuredArrow.toOverCompYoneda, toOverCompYoneda
-/
theorem CostructuredArrow.overEquivPresheafCostructuredArrow_inverse_map_toOverCompYoneda
    {A : Cᵒᵖ ⥤ Type v} {T : Over A} {X : CostructuredArrow yoneda A}
    (f : (CostructuredArrow.toOver yoneda A).obj X ⟶ T) :
    dsimp% (overEquivPresheafCostructuredArrow A).inverse.map
      ((CostructuredArrow.toOverCompYoneda A T).hom.app (op X) f) =
      (CostructuredArrow.toOverCompOverEquivPresheafCostructuredArrow A).isoCompInverse.inv.app X ≫
        f ≫ (overEquivPresheafCostructuredArrow A).unit.app T := by
  simp [CostructuredArrow.toOverCompYoneda]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `CostructuredArrow.overEquivPresheafCostructuredArrow_functor_map_toOverCompYoneda` / 定理 `CostructuredArrow.overEquivPresheafCostructuredArrow_functor_map_toOverCompYoneda`

English:
theorem CostructuredArrow.overEquivPresheafCostructuredArrow_functor_map_toOverCompYoneda
  proof: by
  simp [CostructuredArrow.toOverCompYoneda]

中文:
定理 CostructuredArrow.overEquivPresheafCostructuredArrow_functor_map_toOverCompYoneda
  证明: by
  simp [CostructuredArrow.toOverCompYoneda]

Depends on / 依赖: CostructuredArrow, CostructuredArrow.toOverCompYoneda, toOverCompYoneda
-/
theorem CostructuredArrow.overEquivPresheafCostructuredArrow_functor_map_toOverCompYoneda
    {A : Cᵒᵖ ⥤ Type v} {T : Over A} {X : CostructuredArrow yoneda A}
    (f : yoneda.obj X ⟶ (overEquivPresheafCostructuredArrow A).functor.obj T) :
    dsimp% (overEquivPresheafCostructuredArrow A).functor.map
      (((CostructuredArrow.toOverCompYoneda A T).inv.app (op X) f)) =
      (CostructuredArrow.toOverCompOverEquivPresheafCostructuredArrow A).hom.app X ≫ f := by
  simp [CostructuredArrow.toOverCompYoneda]

/--
Definition of `CostructuredArrow.toOverCompCoyoneda` / `CostructuredArrow.toOverCompCoyoneda` 的定义

English:
definition CostructuredArrow.toOverCompCoyoneda
  signature: (A : Cᵒᵖ ⥤ Type v)
  body: NatIso.ofComponents (fun X => NatIso.ofComponents (fun Y =>
    (overEquivPresheafCostructuredArrow A).fullyFaithfulFunctor.homEquiv.toIso ≪≫
      (Iso.homCongr
        ((CostructuredArrow.toOverCompOverEquivPresheafCostructuredArrow A).app X.unop)
        (Iso.refl _)).toIso)) (by cat_disch)

中文:
定义 CostructuredArrow.toOverCompCoyoneda
  签名: (A : Cᵒᵖ ⥤ 类型v)
  定义体: NatIso.ofComponents (fun X => NatIso.ofComponents (fun Y =>
    (overEquivPresheafCostructuredArrow A).fullyFaithfulFunctor.homEquiv.toIso ≪≫
      (Iso.homCongr
        ((CostructuredArrow.toOverCompOverEquivPresheafCostructuredArrow A).app X.unop)
        (Iso.refl _)).toIso)) (by cat_disch)

Depends on / 依赖: CostructuredArrow, CostructuredArrow.toOverCompOverEquivPresheafCostructuredArrow, Iso.homCongr, Iso.refl, NatIso, NatIso.ofComponents, X.unop, cat_disch, fullyFaithfulFunctor, fullyFaithfulFunctor.homEquiv.toIso, homCongr, homEquiv, ofComponents, overEquivPresheafCostructuredArrow, toOverCompOverEquivPresheafCostructuredArrow
-/
def CostructuredArrow.toOverCompCoyoneda (A : Cᵒᵖ ⥤ Type v) :
    (CostructuredArrow.toOver yoneda A).op ⋙ coyoneda ≅
    yoneda.op ⋙ coyoneda ⋙
      (Functor.whiskeringLeft _ _ _).obj (overEquivPresheafCostructuredArrow A).functor :=
  NatIso.ofComponents (fun X => NatIso.ofComponents (fun Y =>
    (overEquivPresheafCostructuredArrow A).fullyFaithfulFunctor.homEquiv.toIso ≪≫
      (Iso.homCongr
        ((CostructuredArrow.toOverCompOverEquivPresheafCostructuredArrow A).app X.unop)
        (Iso.refl _)).toIso)) (by cat_disch)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `CostructuredArrow.overEquivPresheafCostructuredArrow_inverse_map_toOverCompCoyoneda` / 定理 `CostructuredArrow.overEquivPresheafCostructuredArrow_inverse_map_toOverCompCoyoneda`

English:
theorem CostructuredArrow.overEquivPresheafCostructuredArrow_inverse_map_toOverCompCoyoneda
  proof: by
  simp [CostructuredArrow.toOverCompCoyoneda]

中文:
定理 CostructuredArrow.overEquivPresheafCostructuredArrow_inverse_map_toOverCompCoyoneda
  证明: by
  simp [CostructuredArrow.toOverCompCoyoneda]

Depends on / 依赖: CostructuredArrow, CostructuredArrow.toOverCompCoyoneda, toOverCompCoyoneda
-/
theorem CostructuredArrow.overEquivPresheafCostructuredArrow_inverse_map_toOverCompCoyoneda
    {A : Cᵒᵖ ⥤ Type v} {T : Over A} {X : CostructuredArrow yoneda A}
    (f : (CostructuredArrow.toOver yoneda A).obj X ⟶ T) :
    dsimp% (overEquivPresheafCostructuredArrow A).inverse.map
      (((CostructuredArrow.toOverCompCoyoneda A).hom.app (op X)).app T f) =
      (CostructuredArrow.toOverCompOverEquivPresheafCostructuredArrow A).isoCompInverse.inv.app X ≫
        f ≫ (overEquivPresheafCostructuredArrow A).unit.app T := by
  simp [CostructuredArrow.toOverCompCoyoneda]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `CostructuredArrow.overEquivPresheafCostructuredArrow_functor_map_toOverCompCoyoneda` / 定理 `CostructuredArrow.overEquivPresheafCostructuredArrow_functor_map_toOverCompCoyoneda`

English:
theorem CostructuredArrow.overEquivPresheafCostructuredArrow_functor_map_toOverCompCoyoneda
  proof: by
  simp [CostructuredArrow.toOverCompCoyoneda]

中文:
定理 CostructuredArrow.overEquivPresheafCostructuredArrow_functor_map_toOverCompCoyoneda
  证明: by
  simp [CostructuredArrow.toOverCompCoyoneda]

Depends on / 依赖: CostructuredArrow, CostructuredArrow.toOverCompCoyoneda, toOverCompCoyoneda
-/
theorem CostructuredArrow.overEquivPresheafCostructuredArrow_functor_map_toOverCompCoyoneda
    {A : Cᵒᵖ ⥤ Type v} {T : Over A} {X : CostructuredArrow yoneda A}
    (f : yoneda.obj X ⟶ (overEquivPresheafCostructuredArrow A).functor.obj T) :
    dsimp% (overEquivPresheafCostructuredArrow A).functor.map
      (((CostructuredArrow.toOverCompCoyoneda A).inv.app (op X)).app T f) =
      (CostructuredArrow.toOverCompOverEquivPresheafCostructuredArrow A).hom.app X ≫ f := by
  simp [CostructuredArrow.toOverCompCoyoneda]

end CategoryTheory
