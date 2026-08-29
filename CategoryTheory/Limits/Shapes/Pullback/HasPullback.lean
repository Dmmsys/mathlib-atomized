/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Markus Himmel, Bhavik Mehta, Andrew Yang, Emily Riehl, Calle Sönne
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone

/-!
# HasPullback

`HasPullback f g` and `pullback f g` provides API for `HasLimit` and `limit` in the case of
pullbacks.

## Main definitions

* `HasPullback f g`: this is an abbreviation for `HasLimit (cospan f g)`, and is a typeclass used to
  express the fact that a given pair of morphisms has a pullback.

* `HasPullbacks`: expresses the fact that `C` admits all pullbacks, it is implemented as an
  abbreviation for `HasLimitsOfShape WalkingCospan C`

* `pullback f g`: Given a `HasPullback f g` instance, this function returns the choice of a limit
  object corresponding to the pullback of `f` and `g`. It fits into the following diagram:
  ```
    pullback f g ---pullback.fst f g---> X
        | |
        | |
  pullback.snd f g f
        | |
        v v
        Y --------------g--------------> Z
  ```

* `HasPushout f g`: this is an abbreviation for `HasColimit (span f g)`, and is a typeclass used to
  express the fact that a given pair of morphisms has a pushout.
* `HasPushouts`: expresses the fact that `C` admits all pushouts, it is implemented as an
  abbreviation for `HasColimitsOfShape WalkingSpan C`
* `pushout f g`: Given a `HasPushout f g` instance, this function returns the choice of a colimit
  object corresponding to the pushout of `f` and `g`. It fits into the following diagram:
  ```
      X --------------f--------------> Y
      | |
      g pushout.inl f g
      | |
      v v
      Z ---pushout.inr f g---> pushout f g
  ```

## Main results & API
* The following API is available for using the universal property of `pullback f g`:
  `lift`, `lift_fst`, `lift_snd`, `lift'`, `hom_ext` (for uniqueness).

* `pullback.map` is the induced map between pullbacks `W ×ₛ X ⟶ Y ×ₜ Z` given pointwise
  (compatible) maps `W ⟶ Y`, `X ⟶ Z` and `S ⟶ T`.

* `pullbackComparison`: Given a functor `G`, this is the natural morphism
  `G.obj (pullback f g) ⟶ pullback (G.map f) (G.map g)`

* `pullbackSymmetry` provides the natural isomorphism `pullback f g ≅ pullback g f`

(The dual results for pushouts are also available)

## References
* [Stacks: Fibre products](https://stacks.math.columbia.edu/tag/001U)
* [Stacks: Pushouts](https://stacks.math.columbia.edu/tag/0025)
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe w v₁ v₂ v u u₂

namespace CategoryTheory.Limits

open WalkingSpan.Hom WalkingCospan.Hom WidePullbackShape.Hom WidePushoutShape.Hom

variable {C : Type u} [Category.{v} C] {W X Y Z : C}

/--
Definition of `HasPullback` / `HasPullback` 的定义

English:
abbreviation HasPullback
  signature: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
  body: HasLimit (cospan f g)

中文:
缩写 HasPullback
  签名: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
  定义体: HasLimit (cospan f g)

Depends on / 依赖: HasLimit, cospan
-/
abbrev HasPullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :=
  HasLimit (cospan f g)

/--
Definition of `HasPushout` / `HasPushout` 的定义

English:
abbreviation HasPushout
  signature: {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z)
  body: HasColimit (span f g)

中文:
缩写 HasPushout
  签名: {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z)
  定义体: HasColimit (span f g)

Depends on / 依赖: HasColimit
-/
abbrev HasPushout {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) :=
  HasColimit (span f g)

/--
Definition of `pullback` / `pullback` 的定义

English:
abbreviation pullback
  signature: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
  body: limit (cospan f g)

中文:
缩写 pullback
  签名: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
  定义体: limit (cospan f g)

Depends on / 依赖: cospan
-/
abbrev pullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] :=
  limit (cospan f g)

/--
Definition of `pullback.cone` / `pullback.cone` 的定义

English:
abbreviation pullback.cone
  signature: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
  body: limit.cone (cospan f g)

中文:
缩写 pullback.cone
  签名: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
  定义体: limit.cone (cospan f g)

Depends on / 依赖: cospan, limit.cone
-/
abbrev pullback.cone {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] : PullbackCone f g :=
  limit.cone (cospan f g)

/--
Definition of `pushout` / `pushout` 的定义

English:
abbreviation pushout
  signature: {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g]
  body: colimit (span f g)

中文:
缩写 pushout
  签名: {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g]
  定义体: colimit (span f g)

Depends on / 依赖: colimit
-/
abbrev pushout {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] :=
  colimit (span f g)

/--
Definition of `pushout.cocone` / `pushout.cocone` 的定义

English:
abbreviation pushout.cocone
  signature: {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g]
  body: colimit.cocone (span f g)

中文:
缩写 pushout.cocone
  签名: {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g]
  定义体: colimit.cocone (span f g)

Depends on / 依赖: cocone, colimit, colimit.cocone
-/
abbrev pushout.cocone {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] : PushoutCocone f g :=
  colimit.cocone (span f g)

/--
Definition of `pullback.fst` / `pullback.fst` 的定义

English:
abbreviation pullback.fst
  signature: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
  body: limit.π (cospan f g) WalkingCospan.left

中文:
缩写 pullback.fst
  签名: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
  定义体: limit.π (cospan f g) WalkingCospan.left

Depends on / 依赖: WalkingCospan, WalkingCospan.left, cospan
-/
abbrev pullback.fst {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] : pullback f g ⟶ X :=
  limit.π (cospan f g) WalkingCospan.left

/--
Definition of `pullback.snd` / `pullback.snd` 的定义

English:
abbreviation pullback.snd
  signature: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
  body: limit.π (cospan f g) WalkingCospan.right

中文:
缩写 pullback.snd
  签名: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
  定义体: limit.π (cospan f g) WalkingCospan.right

Depends on / 依赖: WalkingCospan, WalkingCospan.right, cospan
-/
abbrev pullback.snd {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] : pullback f g ⟶ Y :=
  limit.π (cospan f g) WalkingCospan.right

/--
Definition of `pushout.inl` / `pushout.inl` 的定义

English:
abbreviation pushout.inl
  signature: {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g]
  body: colimit.ι (span f g) WalkingSpan.left

中文:
缩写 pushout.inl
  签名: {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g]
  定义体: colimit.ι (span f g) WalkingSpan.left

Depends on / 依赖: WalkingSpan, WalkingSpan.left, colimit, iSup_ofHoms, infer_instance, isSmall_iff_eq_ofHoms
-/
abbrev pushout.inl {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] : Y ⟶ pushout f g :=
  colimit.ι (span f g) WalkingSpan.left

/--
Definition of `pushout.inr` / `pushout.inr` 的定义

English:
abbreviation pushout.inr
  signature: {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g]
  body: colimit.ι (span f g) WalkingSpan.right

中文:
缩写 pushout.inr
  签名: {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g]
  定义体: colimit.ι (span f g) WalkingSpan.right

Depends on / 依赖: WalkingSpan, WalkingSpan.right, colimit
-/
abbrev pushout.inr {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] : Z ⟶ pushout f g :=
  colimit.ι (span f g) WalkingSpan.right

/--
Definition of `pullback.lift` / `pullback.lift` 的定义

English:
abbreviation pullback.lift
  signature: {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] (h : W ⟶ X)
  body: limit.lift _ (PullbackCone.mk h k w)

中文:
缩写 pullback.lift
  签名: {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] (h : W ⟶ X)
  定义体: limit.lift _ (PullbackCone.mk h k w)

Depends on / 依赖: PullbackCone, PullbackCone.mk, cat_disch, limit.lift, pullback
-/
abbrev pullback.lift {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] (h : W ⟶ X)
    (k : W ⟶ Y) (w : h ≫ f = k ≫ g := by cat_disch) : W ⟶ pullback f g :=
  limit.lift _ (PullbackCone.mk h k w)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `pullback.exists_lift` / 引理 `pullback.exists_lift`

English:
lemma pullback.exists_lift
  statement: {W X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
  proof: ⟨pullback.lift h k, by simp⟩

中文:
引理 pullback.exists_lift
  结论: {W X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
  证明: ⟨pullback.lift h k, by simp⟩

Depends on / 依赖: cat_disch, pullback, pullback.fst, pullback.lift, pullback.snd
-/
lemma pullback.exists_lift {W X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
    (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g := by cat_disch) :
    exists (l : W ⟶ pullback f g), l ≫ pullback.fst f g = h ∧ l ≫ pullback.snd f g = k :=
  ⟨pullback.lift h k, by simp⟩

/--
Definition of `pushout.desc` / `pushout.desc` 的定义

English:
abbreviation pushout.desc
  signature: {W X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] (h : Y ⟶ W) (k : Z ⟶ W)
  body: colimit.desc _ (PushoutCocone.mk h k w)

中文:
缩写 pushout.desc
  签名: {W X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] (h : Y ⟶ W) (k : Z ⟶ W)
  定义体: colimit.desc _ (PushoutCocone.mk h k w)

Depends on / 依赖: PushoutCocone, PushoutCocone.mk, cat_disch, colimit, colimit.desc, pushout
-/
abbrev pushout.desc {W X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] (h : Y ⟶ W) (k : Z ⟶ W)
    (w : f ≫ h = g ≫ k := by cat_disch) : pushout f g ⟶ W :=
  colimit.desc _ (PushoutCocone.mk h k w)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `pushout.exists_desc` / 引理 `pushout.exists_desc`

English:
lemma pushout.exists_desc
  statement: {W X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g]
  proof: ⟨pushout.desc h k, by simp⟩

中文:
引理 pushout.exists_desc
  结论: {W X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g]
  证明: ⟨pushout.desc h k, by simp⟩

Depends on / 依赖: cat_disch, pushout, pushout.desc, pushout.inl, pushout.inr
-/
lemma pushout.exists_desc {W X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g]
    (h : Y ⟶ W) (k : Z ⟶ W) (w : f ≫ h = g ≫ k := by cat_disch) :
    exists (l : pushout f g ⟶ W), pushout.inl f g ≫ l = h ∧ pushout.inr f g ≫ l = k :=
  ⟨pushout.desc h k, by simp⟩

/--
Definition of `pullback.isLimit` / `pullback.isLimit` 的定义

English:
abbreviation pullback.isLimit
  signature: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
  body: limit.isLimit (cospan f g)

中文:
缩写 pullback.isLimit
  签名: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
  定义体: limit.isLimit (cospan f g)

Depends on / 依赖: cospan, isLimit, limit.isLimit
-/
abbrev pullback.isLimit {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] :
    IsLimit (pullback.cone f g) :=
  limit.isLimit (cospan f g)

/--
Definition of `pushout.isColimit` / `pushout.isColimit` 的定义

English:
abbreviation pushout.isColimit
  signature: {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g]
  body: colimit.isColimit (span f g)

@[simp]

中文:
缩写 pushout.isColimit
  签名: {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g]
  定义体: colimit.isColimit (span f g)

@[simp]

Depends on / 依赖: colimit, colimit.isColimit, isColimit
-/
abbrev pushout.isColimit {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] :
    IsColimit (pushout.cocone f g) :=
  colimit.isColimit (span f g)

@[simp]
/--
theorem `PullbackCone.fst_limit_cone` / 定理 `PullbackCone.fst_limit_cone`

English:
theorem PullbackCone.fst_limit_cone
  given: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasLimit (cospan f g)]
  proof: rfl

@[simp]

中文:
定理 PullbackCone.fst_limit_cone
  条件: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasLimit (cospan f g)]
  证明: rfl

@[simp]
-/
theorem PullbackCone.fst_limit_cone {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasLimit (cospan f g)] :
    PullbackCone.fst (limit.cone (cospan f g)) = pullback.fst f g := rfl

@[simp]
/--
theorem `PullbackCone.snd_limit_cone` / 定理 `PullbackCone.snd_limit_cone`

English:
theorem PullbackCone.snd_limit_cone
  given: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasLimit (cospan f g)]
  proof: rfl

中文:
定理 PullbackCone.snd_limit_cone
  条件: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasLimit (cospan f g)]
  证明: rfl
-/
theorem PullbackCone.snd_limit_cone {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasLimit (cospan f g)] :
    PullbackCone.snd (limit.cone (cospan f g)) = pullback.snd f g := rfl

/--
theorem `PushoutCocone.inl_colimit_cocone` / 定理 `PushoutCocone.inl_colimit_cocone`

English:
theorem PushoutCocone.inl_colimit_cocone
  statement: {X Y Z : C} (f : Z ⟶ X) (g : Z ⟶ Y)
  proof: rfl

中文:
定理 PushoutCocone.inl_colimit_cocone
  结论: {X Y Z : C} (f : Z ⟶ X) (g : Z ⟶ Y)
  证明: rfl
-/
theorem PushoutCocone.inl_colimit_cocone {X Y Z : C} (f : Z ⟶ X) (g : Z ⟶ Y)
    [HasColimit (span f g)] : PushoutCocone.inl (colimit.cocone (span f g)) = pushout.inl _ _ := rfl

/--
theorem `PushoutCocone.inr_colimit_cocone` / 定理 `PushoutCocone.inr_colimit_cocone`

English:
theorem PushoutCocone.inr_colimit_cocone
  statement: {X Y Z : C} (f : Z ⟶ X) (g : Z ⟶ Y)
  proof: rfl

@[reassoc]

中文:
定理 PushoutCocone.inr_colimit_cocone
  结论: {X Y Z : C} (f : Z ⟶ X) (g : Z ⟶ Y)
  证明: rfl

@[reassoc]
-/
theorem PushoutCocone.inr_colimit_cocone {X Y Z : C} (f : Z ⟶ X) (g : Z ⟶ Y)
    [HasColimit (span f g)] : PushoutCocone.inr (colimit.cocone (span f g)) = pushout.inr _ _ := rfl

@[reassoc]
/--
theorem `pullback.lift_fst` / 定理 `pullback.lift_fst`

English:
theorem pullback.lift_fst
  statement: {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] (h : W ⟶ X)
  proof: limit.lift_π _ _

@[reassoc]

中文:
定理 pullback.lift_fst
  结论: {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] (h : W ⟶ X)
  证明: limit.lift_π _ _

@[reassoc]

Depends on / 依赖: limit.lift_
-/
theorem pullback.lift_fst {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] (h : W ⟶ X)
    (k : W ⟶ Y) (w : h ≫ f = k ≫ g) : pullback.lift h k w ≫ pullback.fst f g = h :=
  limit.lift_π _ _

@[reassoc]
/--
theorem `pullback.lift_snd` / 定理 `pullback.lift_snd`

English:
theorem pullback.lift_snd
  statement: {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] (h : W ⟶ X)
  proof: limit.lift_π _ _

@[reassoc]

中文:
定理 pullback.lift_snd
  结论: {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] (h : W ⟶ X)
  证明: limit.lift_π _ _

@[reassoc]

Depends on / 依赖: limit.lift_
-/
theorem pullback.lift_snd {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] (h : W ⟶ X)
    (k : W ⟶ Y) (w : h ≫ f = k ≫ g) : pullback.lift h k w ≫ pullback.snd f g = k :=
  limit.lift_π _ _

@[reassoc]
/--
theorem `pushout.inl_desc` / 定理 `pushout.inl_desc`

English:
theorem pushout.inl_desc
  statement: {W X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] (h : Y ⟶ W)
  proof: colimit.ι_desc _ _

@[reassoc]

中文:
定理 pushout.inl_desc
  结论: {W X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] (h : Y ⟶ W)
  证明: colimit.ι_desc _ _

@[reassoc]

Depends on / 依赖: colimit
-/
theorem pushout.inl_desc {W X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] (h : Y ⟶ W)
    (k : Z ⟶ W) (w : f ≫ h = g ≫ k) : pushout.inl _ _ ≫ pushout.desc h k w = h :=
  colimit.ι_desc _ _

@[reassoc]
/--
theorem `pushout.inr_desc` / 定理 `pushout.inr_desc`

English:
theorem pushout.inr_desc
  statement: {W X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] (h : Y ⟶ W)
  proof: colimit.ι_desc _ _

中文:
定理 pushout.inr_desc
  结论: {W X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] (h : Y ⟶ W)
  证明: colimit.ι_desc _ _

Depends on / 依赖: colimit
-/
theorem pushout.inr_desc {W X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] (h : Y ⟶ W)
    (k : Z ⟶ W) (w : f ≫ h = g ≫ k) : pushout.inr _ _ ≫ pushout.desc h k w = k :=
  colimit.ι_desc _ _

/--
Definition of `pullback.lift'` / `pullback.lift'` 的定义

English:
definition pullback.lift'
  signature: {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] (h : W ⟶ X) (k : W ⟶ Y)
  body: ⟨pullback.lift h k w, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

中文:
定义 pullback.lift'
  签名: {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] (h : W ⟶ X) (k : W ⟶ Y)
  定义体: ⟨pullback.lift h k w, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

Depends on / 依赖: lift_fst, lift_snd, pullback, pullback.lift, pullback.lift_fst, pullback.lift_snd
-/
def pullback.lift' {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] (h : W ⟶ X) (k : W ⟶ Y)
    (w : h ≫ f = k ≫ g) :
    { l : W ⟶ pullback f g // l ≫ pullback.fst f g = h ∧ l ≫ pullback.snd f g = k } :=
  ⟨pullback.lift h k w, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

/--
Definition of `pushout.desc'` / `pushout.desc'` 的定义

English:
definition pushout.desc'
  signature: {W X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] (h : Y ⟶ W) (k : Z ⟶ W)
  body: ⟨pushout.desc h k w, pushout.inl_desc _ _ _, pushout.inr_desc _ _ _⟩

@[deprecated (since := "2026-06-25")] alias pullback.desc' := pushout.desc'

@[reassoc]

中文:
定义 pushout.desc'
  签名: {W X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] (h : Y ⟶ W) (k : Z ⟶ W)
  定义体: ⟨pushout.desc h k w, pushout.inl_desc _ _ _, pushout.inr_desc _ _ _⟩

@[deprecated (since := "2026-06-25")] alias pullback.desc' := pushout.desc'

@[reassoc]

Depends on / 依赖: inl_desc, inr_desc, pushout, pushout.desc, pushout.inl_desc, pushout.inr_desc
-/
def pushout.desc' {W X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] (h : Y ⟶ W) (k : Z ⟶ W)
    (w : f ≫ h = g ≫ k) :
    { l : pushout f g ⟶ W // pushout.inl _ _ ≫ l = h ∧ pushout.inr _ _ ≫ l = k } :=
  ⟨pushout.desc h k w, pushout.inl_desc _ _ _, pushout.inr_desc _ _ _⟩

@[deprecated (since := "2026-06-25")] alias pullback.desc' := pushout.desc'

@[reassoc]
/--
theorem `pullback.condition` / 定理 `pullback.condition`

English:
theorem pullback.condition
  given: {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g]
  proof: PullbackCone.condition _

@[reassoc]

中文:
定理 pullback.condition
  条件: {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g]
  证明: PullbackCone.condition _

@[reassoc]

Depends on / 依赖: PullbackCone, PullbackCone.condition, condition
-/
theorem pullback.condition {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] :
    pullback.fst f g ≫ f = pullback.snd f g ≫ g :=
  PullbackCone.condition _

@[reassoc]
/--
theorem `pushout.condition` / 定理 `pushout.condition`

English:
theorem pushout.condition
  given: {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g]
  proof: PushoutCocone.condition _

中文:
定理 pushout.condition
  条件: {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g]
  证明: PushoutCocone.condition _

Depends on / 依赖: PushoutCocone, PushoutCocone.condition, condition
-/
theorem pushout.condition {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] :
    f ≫ (pushout.inl f g) = g ≫ pushout.inr _ _ :=
  PushoutCocone.condition _

/-- Two morphisms into a pullback are equal if their compositions with the pullback morphisms are
equal -/
@[ext 1100]
/--
theorem `pullback.hom_ext` / 定理 `pullback.hom_ext`

English:
theorem pullback.hom_ext
  statement: {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] {W : C}
  proof: limit.hom_ext PullbackCone.equalizer_ext _ h₀ h₁

中文:
定理 pullback.hom_ext
  结论: {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] {W : C}
  证明: limit.hom_ext PullbackCone.equalizer_ext _ h₀ h₁

Depends on / 依赖: PullbackCone, PullbackCone.equalizer_ext, equalizer_ext, hom_ext, limit.hom_ext
-/
theorem pullback.hom_ext {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] {W : C}
    {k l : W ⟶ pullback f g} (h₀ : k ≫ pullback.fst f g = l ≫ pullback.fst f g)
    (h₁ : k ≫ pullback.snd f g = l ≫ pullback.snd f g) : k = l :=
limit.hom_ext PullbackCone.equalizer_ext _ h₀ h₁

/--
Definition of `pullbackIsPullback` / `pullbackIsPullback` 的定义

English:
definition pullbackIsPullback
  signature: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
  body: PullbackCone.mkSelfIsLimit pullback.isLimit f g

中文:
定义 pullbackIsPullback
  签名: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
  定义体: PullbackCone.mkSelfIsLimit pullback.isLimit f g

Depends on / 依赖: PullbackCone, PullbackCone.mkSelfIsLimit, isLimit, mkSelfIsLimit, pullback, pullback.isLimit
-/
def pullbackIsPullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] :
    IsLimit (PullbackCone.mk (pullback.fst f g) (pullback.snd f g) pullback.condition) :=
PullbackCone.mkSelfIsLimit pullback.isLimit f g

/-- Two morphisms out of a pushout are equal if their compositions with the pushout morphisms are
equal -/
@[ext 1100]
/--
theorem `pushout.hom_ext` / 定理 `pushout.hom_ext`

English:
theorem pushout.hom_ext
  statement: {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] {W : C}
  proof: colimit.hom_ext PushoutCocone.coequalizer_ext _ h₀ h₁

中文:
定理 pushout.hom_ext
  结论: {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] {W : C}
  证明: colimit.hom_ext PushoutCocone.coequalizer_ext _ h₀ h₁

Depends on / 依赖: PushoutCocone, PushoutCocone.coequalizer_ext, coequalizer_ext, colimit, colimit.hom_ext, hom_ext
-/
theorem pushout.hom_ext {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] {W : C}
    {k l : pushout f g ⟶ W} (h₀ : pushout.inl _ _ ≫ k = pushout.inl _ _ ≫ l)
    (h₁ : pushout.inr _ _ ≫ k = pushout.inr _ _ ≫ l) : k = l :=
colimit.hom_ext PushoutCocone.coequalizer_ext _ h₀ h₁

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `pushoutIsPushout` / `pushoutIsPushout` 的定义

English:
definition pushoutIsPushout
  signature: {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g]
  body: PushoutCocone.IsColimit.mk _ (fun s => pushout.desc s.inl s.inr s.condition) (by simp) (by simp)
    (by cat_disch)

中文:
定义 pushoutIsPushout
  签名: {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g]
  定义体: PushoutCocone.IsColimit.mk _ (fun s => pushout.desc s.inl s.inr s.condition) (by simp) (by simp)
    (by cat_disch)

Depends on / 依赖: IsColimit, PushoutCocone, PushoutCocone.IsColimit.mk, cat_disch, condition, pushout, pushout.desc, s.condition, s.inl, s.inr
-/
def pushoutIsPushout {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] :
    IsColimit (PushoutCocone.mk (pushout.inl f g) (pushout.inr _ _) pushout.condition) :=
  PushoutCocone.IsColimit.mk _ (fun s => pushout.desc s.inl s.inr s.condition) (by simp) (by simp)
    (by cat_disch)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `pullback.lift_fst_snd` / 引理 `pullback.lift_fst_snd`

English:
lemma pullback.lift_fst_snd
  given: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
  proof: by
  apply hom_ext <;> simp

中文:
引理 pullback.lift_fst_snd
  条件: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
  证明: by
  apply hom_ext <;> simp

Depends on / 依赖: hom_ext
-/
lemma pullback.lift_fst_snd {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] :
    lift (fst f g) (snd f g) condition = 𝟙 (pullback f g) := by
  apply hom_ext <;> simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `pushout.desc_inl_inr` / 引理 `pushout.desc_inl_inr`

English:
lemma pushout.desc_inl_inr
  given: {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g]
  proof: by
  apply hom_ext <;> simp

中文:
引理 pushout.desc_inl_inr
  条件: {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g]
  证明: by
  apply hom_ext <;> simp

Depends on / 依赖: hom_ext
-/
lemma pushout.desc_inl_inr {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] :
    desc (inl f g) (inr f g) condition = 𝟙 (pushout f g) := by
  apply hom_ext <;> simp

/--
Definition of `pullback.map` / `pullback.map` 的定义

English:
abbreviation pullback.map
  signature: {W X Y Z S T : C} (f₁ : W ⟶ S) (f₂ : X ⟶ S) [HasPullback f₁ f₂] (g₁ : Y ⟶ T)
  body: pullback.lift (pullback.fst f₁ f₂ ≫ i₁) (pullback.snd f₁ f₂ ≫ i₂)
    (by simp only [Category.assoc, ← eq₁, ← eq₂, pullback.condition_assoc])

中文:
缩写 pullback.map
  签名: {W X Y Z S T : C} (f₁ : W ⟶ S) (f₂ : X ⟶ S) [HasPullback f₁ f₂] (g₁ : Y ⟶ T)
  定义体: pullback.lift (pullback.fst f₁ f₂ ≫ i₁) (pullback.snd f₁ f₂ ≫ i₂)
    (by simp only [Category.assoc, ← eq₁, ← eq₂, pullback.condition_assoc])

Depends on / 依赖: Category, Category.assoc, condition_assoc, pullback, pullback.condition_assoc, pullback.fst, pullback.lift, pullback.snd
-/
abbrev pullback.map {W X Y Z S T : C} (f₁ : W ⟶ S) (f₂ : X ⟶ S) [HasPullback f₁ f₂] (g₁ : Y ⟶ T)
    (g₂ : Z ⟶ T) [HasPullback g₁ g₂] (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T)
    (eq₁ : f₁ ≫ i₃ = i₁ ≫ g₁) (eq₂ : f₂ ≫ i₃ = i₂ ≫ g₂) : pullback f₁ f₂ ⟶ pullback g₁ g₂ :=
  pullback.lift (pullback.fst f₁ f₂ ≫ i₁) (pullback.snd f₁ f₂ ≫ i₂)
    (by simp only [Category.assoc, ← eq₁, ← eq₂, pullback.condition_assoc])

/--
Definition of `pullback.mapDesc` / `pullback.mapDesc` 的定义

English:
abbreviation pullback.mapDesc
  signature: {X Y S T : C} (f : X ⟶ S) (g : Y ⟶ S) (i : S ⟶ T) [HasPullback f g]
  body: pullback.map f g (f ≫ i) (g ≫ i) (𝟙 _) (𝟙 _) i (Category.id_comp _).symm (Category.id_comp _).symm

中文:
缩写 pullback.mapDesc
  签名: {X Y S T : C} (f : X ⟶ S) (g : Y ⟶ S) (i : S ⟶ T) [HasPullback f g]
  定义体: pullback.map f g (f ≫ i) (g ≫ i) (𝟙 _) (𝟙 _) i (Category.id_comp _).symm (Category.id_comp _).symm

Depends on / 依赖: Category, Category.id_comp, id_comp, pullback, pullback.map
-/
abbrev pullback.mapDesc {X Y S T : C} (f : X ⟶ S) (g : Y ⟶ S) (i : S ⟶ T) [HasPullback f g]
    [HasPullback (f ≫ i) (g ≫ i)] : pullback f g ⟶ pullback (f ≫ i) (g ≫ i) :=
  pullback.map f g (f ≫ i) (g ≫ i) (𝟙 _) (𝟙 _) i (Category.id_comp _).symm (Category.id_comp _).symm

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `pullback.map_comp` / 引理 `pullback.map_comp`

English:
lemma pullback.map_comp
  statement: {X Y Z X' Y' Z' X'' Y'' Z'' : C}
  proof: by ext <;> simp

中文:
引理 pullback.map_comp
  结论: {X Y Z X' Y' Z' X'' Y'' Z'' : C}
  证明: by ext <;> simp
-/
lemma pullback.map_comp {X Y Z X' Y' Z' X'' Y'' Z'' : C}
    {f : X ⟶ Z} {g : Y ⟶ Z} {f' : X' ⟶ Z'} {g' : Y' ⟶ Z'} {f'' : X'' ⟶ Z''} {g'' : Y'' ⟶ Z''}
    (i₁ : X ⟶ X') (j₁ : X' ⟶ X'') (i₂ : Y ⟶ Y') (j₂ : Y' ⟶ Y'') (i₃ : Z ⟶ Z') (j₃ : Z' ⟶ Z'')
    [HasPullback f g] [HasPullback f' g'] [HasPullback f'' g'']
    (e₁ e₂ e₃ e₄) :
    pullback.map f g f' g' i₁ i₂ i₃ e₁ e₂ ≫ pullback.map f' g' f'' g'' j₁ j₂ j₃ e₃ e₄ =
      pullback.map f g f'' g'' (i₁ ≫ j₁) (i₂ ≫ j₂) (i₃ ≫ j₃)
        (by rw [reassoc_of% e₁, e₃, Category.assoc])
        (by rw [reassoc_of% e₂, e₄, Category.assoc]) := by ext <;> simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `pullback.map_id` / 引理 `pullback.map_id`

English:
lemma pullback.map_id
  statement: {X Y Z : C}
  proof: by ext <;> simp

中文:
引理 pullback.map_id
  结论: {X Y Z : C}
  证明: by ext <;> simp
-/
lemma pullback.map_id {X Y Z : C}
    {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] :
    pullback.map f g f g (𝟙 _) (𝟙 _) (𝟙 _) (by simp) (by simp) = 𝟙 _ := by ext <;> simp

/--
Definition of `pushout.map` / `pushout.map` 的定义

English:
abbreviation pushout.map
  signature: {W X Y Z S T : C} (f₁ : S ⟶ W) (f₂ : S ⟶ X) [HasPushout f₁ f₂] (g₁ : T ⟶ Y)
  body: pushout.desc (i₁ ≫ pushout.inl _ _) (i₂ ≫ pushout.inr _ _)
    (by simp only [reassoc_of% eq₁, reassoc_of% eq₂, condition])

中文:
缩写 pushout.map
  签名: {W X Y Z S T : C} (f₁ : S ⟶ W) (f₂ : S ⟶ X) [HasPushout f₁ f₂] (g₁ : T ⟶ Y)
  定义体: pushout.desc (i₁ ≫ pushout.inl _ _) (i₂ ≫ pushout.inr _ _)
    (by simp only [reassoc_of% eq₁, reassoc_of% eq₂, condition])

Depends on / 依赖: condition, pushout, pushout.desc, pushout.inl, pushout.inr, reassoc_of
-/
abbrev pushout.map {W X Y Z S T : C} (f₁ : S ⟶ W) (f₂ : S ⟶ X) [HasPushout f₁ f₂] (g₁ : T ⟶ Y)
    (g₂ : T ⟶ Z) [HasPushout g₁ g₂] (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T) (eq₁ : f₁ ≫ i₁ = i₃ ≫ g₁)
    (eq₂ : f₂ ≫ i₂ = i₃ ≫ g₂) : pushout f₁ f₂ ⟶ pushout g₁ g₂ :=
  pushout.desc (i₁ ≫ pushout.inl _ _) (i₂ ≫ pushout.inr _ _)
    (by simp only [reassoc_of% eq₁, reassoc_of% eq₂, condition])

/--
Definition of `pushout.mapLift` / `pushout.mapLift` 的定义

English:
abbreviation pushout.mapLift
  signature: {X Y S T : C} (f : T ⟶ X) (g : T ⟶ Y) (i : S ⟶ T) [HasPushout f g]
  body: pushout.map (i ≫ f) (i ≫ g) f g (𝟙 _) (𝟙 _) i (Category.comp_id _) (Category.comp_id _)

中文:
缩写 pushout.mapLift
  签名: {X Y S T : C} (f : T ⟶ X) (g : T ⟶ Y) (i : S ⟶ T) [HasPushout f g]
  定义体: pushout.map (i ≫ f) (i ≫ g) f g (𝟙 _) (𝟙 _) i (Category.comp_id _) (Category.comp_id _)

Depends on / 依赖: Category, Category.comp_id, comp_id, pushout, pushout.map
-/
abbrev pushout.mapLift {X Y S T : C} (f : T ⟶ X) (g : T ⟶ Y) (i : S ⟶ T) [HasPushout f g]
    [HasPushout (i ≫ f) (i ≫ g)] : pushout (i ≫ f) (i ≫ g) ⟶ pushout f g :=
  pushout.map (i ≫ f) (i ≫ g) f g (𝟙 _) (𝟙 _) i (Category.comp_id _) (Category.comp_id _)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `pushout.map_comp` / 引理 `pushout.map_comp`

English:
lemma pushout.map_comp
  statement: {X Y Z X' Y' Z' X'' Y'' Z'' : C}
  proof: by ext <;> simp

中文:
引理 pushout.map_comp
  结论: {X Y Z X' Y' Z' X'' Y'' Z'' : C}
  证明: by ext <;> simp
-/
lemma pushout.map_comp {X Y Z X' Y' Z' X'' Y'' Z'' : C}
    {f : X ⟶ Y} {g : X ⟶ Z} {f' : X' ⟶ Y'} {g' : X' ⟶ Z'} {f'' : X'' ⟶ Y''} {g'' : X'' ⟶ Z''}
    (i₁ : X ⟶ X') (j₁ : X' ⟶ X'') (i₂ : Y ⟶ Y') (j₂ : Y' ⟶ Y'') (i₃ : Z ⟶ Z') (j₃ : Z' ⟶ Z'')
    [HasPushout f g] [HasPushout f' g'] [HasPushout f'' g'']
    (e₁ e₂ e₃ e₄) :
    pushout.map f g f' g' i₂ i₃ i₁ e₁ e₂ ≫ pushout.map f' g' f'' g'' j₂ j₃ j₁ e₃ e₄ =
      pushout.map f g f'' g'' (i₂ ≫ j₂) (i₃ ≫ j₃) (i₁ ≫ j₁)
        (by rw [reassoc_of% e₁, e₃, Category.assoc])
        (by rw [reassoc_of% e₂, e₄, Category.assoc]) := by ext <;> simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `pushout.map_id` / 引理 `pushout.map_id`

English:
lemma pushout.map_id
  statement: {X Y Z : C}
  proof: by ext <;> simp

中文:
引理 pushout.map_id
  结论: {X Y Z : C}
  证明: by ext <;> simp
-/
lemma pushout.map_id {X Y Z : C}
    {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] :
    pushout.map f g f g (𝟙 _) (𝟙 _) (𝟙 _) (by simp) (by simp) = 𝟙 _ := by ext <;> simp

set_option backward.isDefEq.respectTransparency false in
/--
Instance `pullback.map_isIso` / 实例 `pullback.map_isIso`

English:
instance pullback.map_isIso
  signature: {W X Y Z S T : C} (f₁ : W ⟶ S) (f₂ : X ⟶ S) [HasPullback f₁ f₂]
  body: by
  refine ⟨⟨pullback.map _ _ _ _ (inv i₁) (inv i₂) (inv i₃) ?_ ?_, ?_, ?_⟩⟩
  · rw [IsIso.comp_inv_eq, Category.assoc, eq₁, IsIso.inv_hom_id_assoc]
  · rw [IsIso.comp_inv_eq, Category.assoc, eq₂, IsIso.inv_hom_id_assoc]
  · cat_disch
  · cat_disch

中文:
实例 pullback.map_isIso
  签名: {W X Y Z S T : C} (f₁ : W ⟶ S) (f₂ : X ⟶ S) [HasPullback f₁ f₂]
  定义体: by
  refine ⟨⟨pullback.map _ _ _ _ (inv i₁) (inv i₂) (inv i₃) ?_ ?_, ?_, ?_⟩⟩
  · rw [IsIso.comp_inv_eq, Category.assoc, eq₁, IsIso.inv_hom_id_assoc]
  · rw [IsIso.comp_inv_eq, Category.assoc, eq₂, IsIso.inv_hom_id_assoc]
  · cat_disch
  · cat_disch

Depends on / 依赖: Category, Category.assoc, IsIso.comp_inv_eq, IsIso.inv_hom_id_assoc, cat_disch, comp_inv_eq, inv_hom_id_assoc, pullback, pullback.map
-/
instance pullback.map_isIso {W X Y Z S T : C} (f₁ : W ⟶ S) (f₂ : X ⟶ S) [HasPullback f₁ f₂]
    (g₁ : Y ⟶ T) (g₂ : Z ⟶ T) [HasPullback g₁ g₂] (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T)
    (eq₁ : f₁ ≫ i₃ = i₁ ≫ g₁) (eq₂ : f₂ ≫ i₃ = i₂ ≫ g₂) [IsIso i₁] [IsIso i₂] [IsIso i₃] :
    IsIso (pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ eq₁ eq₂) := by
  refine ⟨⟨pullback.map _ _ _ _ (inv i₁) (inv i₂) (inv i₃) ?_ ?_, ?_, ?_⟩⟩
  · rw [IsIso.comp_inv_eq, Category.assoc, eq₁, IsIso.inv_hom_id_assoc]
  · rw [IsIso.comp_inv_eq, Category.assoc, eq₂, IsIso.inv_hom_id_assoc]
  · cat_disch
  · cat_disch

/-- If `f₁ = f₂` and `g₁ = g₂`, we may construct a canonical
isomorphism `pullback f₁ g₁ ≅ pullback f₂ g₂` -/
@[simps! hom]
/--
Definition of `pullback.congrHom` / `pullback.congrHom` 的定义

English:
definition pullback.congrHom
  signature: {X Y Z : C} {f₁ f₂ : X ⟶ Z} {g₁ g₂ : Y ⟶ Z} (h₁ : f₁ = f₂) (h₂ : g₁ = g₂)
  body: asIso pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) (by simp [h₁]) (by simp [h₂])

中文:
定义 pullback.congrHom
  签名: {X Y Z : C} {f₁ f₂ : X ⟶ Z} {g₁ g₂ : Y ⟶ Z} (h₁ : f₁ = f₂) (h₂ : g₁ = g₂)
  定义体: asIso pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) (by simp [h₁]) (by simp [h₂])

Depends on / 依赖: pullback, pullback.map
-/
def pullback.congrHom {X Y Z : C} {f₁ f₂ : X ⟶ Z} {g₁ g₂ : Y ⟶ Z} (h₁ : f₁ = f₂) (h₂ : g₁ = g₂)
    [HasPullback f₁ g₁] [HasPullback f₂ g₂] : pullback f₁ g₁ ≅ pullback f₂ g₂ :=
asIso pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) (by simp [h₁]) (by simp [h₂])

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `pullback.congrHom_inv` / 定理 `pullback.congrHom_inv`

English:
theorem pullback.congrHom_inv
  statement: {X Y Z : C} {f₁ f₂ : X ⟶ Z} {g₁ g₂ : Y ⟶ Z} (h₁ : f₁ = f₂)
  proof: by
  ext <;> simp [Iso.inv_comp_eq]

中文:
定理 pullback.congrHom_inv
  结论: {X Y Z : C} {f₁ f₂ : X ⟶ Z} {g₁ g₂ : Y ⟶ Z} (h₁ : f₁ = f₂)
  证明: by
  ext <;> simp [Iso.inv_comp_eq]

Depends on / 依赖: Iso.inv_comp_eq, inv_comp_eq
-/
theorem pullback.congrHom_inv {X Y Z : C} {f₁ f₂ : X ⟶ Z} {g₁ g₂ : Y ⟶ Z} (h₁ : f₁ = f₂)
    (h₂ : g₁ = g₂) [HasPullback f₁ g₁] [HasPullback f₂ g₂] :
    (pullback.congrHom h₁ h₂).inv =
      pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) (by simp [h₁]) (by simp [h₂]) := by
  ext <;> simp [Iso.inv_comp_eq]

set_option backward.isDefEq.respectTransparency false in
/--
Instance `pushout.map_isIso` / 实例 `pushout.map_isIso`

English:
instance pushout.map_isIso
  signature: {W X Y Z S T : C} (f₁ : S ⟶ W) (f₂ : S ⟶ X) [HasPushout f₁ f₂]
  body: by
  refine ⟨⟨pushout.map _ _ _ _ (inv i₁) (inv i₂) (inv i₃) ?_ ?_, ?_, ?_⟩⟩
  · rw [IsIso.comp_inv_eq, Category.assoc, eq₁, IsIso.inv_hom_id_assoc]
  · rw [IsIso.comp_inv_eq, Category.assoc, eq₂, IsIso.inv_hom_id_assoc]
  · cat_disch
  · cat_disch

中文:
实例 pushout.map_isIso
  签名: {W X Y Z S T : C} (f₁ : S ⟶ W) (f₂ : S ⟶ X) [HasPushout f₁ f₂]
  定义体: by
  refine ⟨⟨pushout.map _ _ _ _ (inv i₁) (inv i₂) (inv i₃) ?_ ?_, ?_, ?_⟩⟩
  · rw [IsIso.comp_inv_eq, Category.assoc, eq₁, IsIso.inv_hom_id_assoc]
  · rw [IsIso.comp_inv_eq, Category.assoc, eq₂, IsIso.inv_hom_id_assoc]
  · cat_disch
  · cat_disch

Depends on / 依赖: Category, Category.assoc, IsIso.comp_inv_eq, IsIso.inv_hom_id_assoc, cat_disch, comp_inv_eq, inv_hom_id_assoc, pushout, pushout.map
-/
instance pushout.map_isIso {W X Y Z S T : C} (f₁ : S ⟶ W) (f₂ : S ⟶ X) [HasPushout f₁ f₂]
    (g₁ : T ⟶ Y) (g₂ : T ⟶ Z) [HasPushout g₁ g₂] (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T)
    (eq₁ : f₁ ≫ i₁ = i₃ ≫ g₁) (eq₂ : f₂ ≫ i₂ = i₃ ≫ g₂) [IsIso i₁] [IsIso i₂] [IsIso i₃] :
    IsIso (pushout.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ eq₁ eq₂) := by
  refine ⟨⟨pushout.map _ _ _ _ (inv i₁) (inv i₂) (inv i₃) ?_ ?_, ?_, ?_⟩⟩
  · rw [IsIso.comp_inv_eq, Category.assoc, eq₁, IsIso.inv_hom_id_assoc]
  · rw [IsIso.comp_inv_eq, Category.assoc, eq₂, IsIso.inv_hom_id_assoc]
  · cat_disch
  · cat_disch

set_option backward.isDefEq.respectTransparency false in
/--
theorem `pullback.mapDesc_comp` / 定理 `pullback.mapDesc_comp`

English:
theorem pullback.mapDesc_comp
  statement: {X Y S T S' : C} (f : X ⟶ T) (g : Y ⟶ T) (i : T ⟶ S) (i' : S ⟶ S')
  proof: by
  cat_disch

中文:
定理 pullback.mapDesc_comp
  结论: {X Y S T S' : C} (f : X ⟶ T) (g : Y ⟶ T) (i : T ⟶ S) (i' : S ⟶ S')
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
theorem pullback.mapDesc_comp {X Y S T S' : C} (f : X ⟶ T) (g : Y ⟶ T) (i : T ⟶ S) (i' : S ⟶ S')
    [HasPullback f g] [HasPullback (f ≫ i) (g ≫ i)] [HasPullback (f ≫ i ≫ i') (g ≫ i ≫ i')]
    [HasPullback ((f ≫ i) ≫ i') ((g ≫ i) ≫ i')] :
    pullback.mapDesc f g (i ≫ i') = pullback.mapDesc f g i ≫ pullback.mapDesc _ _ i' ≫
    (pullback.congrHom (Category.assoc _ _ _) (Category.assoc _ _ _)).hom := by
  cat_disch

/-- If `f₁ = f₂` and `g₁ = g₂`, we may construct a canonical
isomorphism `pushout f₁ g₁ ≅ pullback f₂ g₂` -/
@[simps! hom]
/--
Definition of `pushout.congrHom` / `pushout.congrHom` 的定义

English:
definition pushout.congrHom
  signature: {X Y Z : C} {f₁ f₂ : X ⟶ Y} {g₁ g₂ : X ⟶ Z} (h₁ : f₁ = f₂) (h₂ : g₁ = g₂)
  body: asIso pushout.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) (by simp [h₁]) (by simp [h₂])

中文:
定义 pushout.congrHom
  签名: {X Y Z : C} {f₁ f₂ : X ⟶ Y} {g₁ g₂ : X ⟶ Z} (h₁ : f₁ = f₂) (h₂ : g₁ = g₂)
  定义体: asIso pushout.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) (by simp [h₁]) (by simp [h₂])

Depends on / 依赖: pushout, pushout.map
-/
def pushout.congrHom {X Y Z : C} {f₁ f₂ : X ⟶ Y} {g₁ g₂ : X ⟶ Z} (h₁ : f₁ = f₂) (h₂ : g₁ = g₂)
    [HasPushout f₁ g₁] [HasPushout f₂ g₂] : pushout f₁ g₁ ≅ pushout f₂ g₂ :=
asIso pushout.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) (by simp [h₁]) (by simp [h₂])

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `pushout.congrHom_inv` / 定理 `pushout.congrHom_inv`

English:
theorem pushout.congrHom_inv
  statement: {X Y Z : C} {f₁ f₂ : X ⟶ Y} {g₁ g₂ : X ⟶ Z} (h₁ : f₁ = f₂)
  proof: by
  ext <;> simp [Iso.comp_inv_eq]

中文:
定理 pushout.congrHom_inv
  结论: {X Y Z : C} {f₁ f₂ : X ⟶ Y} {g₁ g₂ : X ⟶ Z} (h₁ : f₁ = f₂)
  证明: by
  ext <;> simp [Iso.comp_inv_eq]

Depends on / 依赖: Iso.comp_inv_eq, comp_inv_eq
-/
theorem pushout.congrHom_inv {X Y Z : C} {f₁ f₂ : X ⟶ Y} {g₁ g₂ : X ⟶ Z} (h₁ : f₁ = f₂)
    (h₂ : g₁ = g₂) [HasPushout f₁ g₁] [HasPushout f₂ g₂] :
    (pushout.congrHom h₁ h₂).inv =
      pushout.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) (by simp [h₁]) (by simp [h₂]) := by
  ext <;> simp [Iso.comp_inv_eq]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `pushout.mapLift_comp` / 定理 `pushout.mapLift_comp`

English:
theorem pushout.mapLift_comp
  statement: {X Y S T S' : C} (f : T ⟶ X) (g : T ⟶ Y) (i : S ⟶ T) (i' : S' ⟶ S)
  proof: by
  cat_disch

中文:
定理 pushout.mapLift_comp
  结论: {X Y S T S' : C} (f : T ⟶ X) (g : T ⟶ Y) (i : S ⟶ T) (i' : S' ⟶ S)
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
theorem pushout.mapLift_comp {X Y S T S' : C} (f : T ⟶ X) (g : T ⟶ Y) (i : S ⟶ T) (i' : S' ⟶ S)
    [HasPushout f g] [HasPushout (i ≫ f) (i ≫ g)] [HasPushout (i' ≫ i ≫ f) (i' ≫ i ≫ g)]
    [HasPushout ((i' ≫ i) ≫ f) ((i' ≫ i) ≫ g)] :
    pushout.mapLift f g (i' ≫ i) =
      (pushout.congrHom (Category.assoc _ _ _) (Category.assoc _ _ _)).hom ≫
        pushout.mapLift _ _ i' ≫ pushout.mapLift f g i := by
  cat_disch

section

variable {D : Type u₂} [Category.{v₂} D] (G : C ⥤ D)

/--
Definition of `pullbackComparison` / `pullbackComparison` 的定义

English:
definition pullbackComparison
  signature: (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] [HasPullback (G.map f) (G.map g)]
  body: pullback.lift (G.map (pullback.fst f g)) (G.map (pullback.snd f g))
    (by simp only [← G.map_comp, pullback.condition])

@[reassoc (attr := simp)]

中文:
定义 pullbackComparison
  签名: (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] [HasPullback (G.map f) (G.map g)]
  定义体: pullback.lift (G.map (pullback.fst f g)) (G.map (pullback.snd f g))
    (by simp only [← G.map_comp, pullback.condition])

@[reassoc (attr := simp)]

Depends on / 依赖: G.map, G.map_comp, condition, map_comp, pullback, pullback.condition, pullback.fst, pullback.lift, pullback.snd
-/
def pullbackComparison (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] [HasPullback (G.map f) (G.map g)] :
    G.obj (pullback f g) ⟶ pullback (G.map f) (G.map g) :=
  pullback.lift (G.map (pullback.fst f g)) (G.map (pullback.snd f g))
    (by simp only [← G.map_comp, pullback.condition])

@[reassoc (attr := simp)]
/--
theorem `pullbackComparison_comp_fst` / 定理 `pullbackComparison_comp_fst`

English:
theorem pullbackComparison_comp_fst
  statement: (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
  proof: pullback.lift_fst _ _ _

@[reassoc (attr := simp)]

中文:
定理 pullbackComparison_comp_fst
  结论: (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
  证明: pullback.lift_fst _ _ _

@[reassoc (attr := simp)]

Depends on / 依赖: lift_fst, pullback, pullback.lift_fst
-/
theorem pullbackComparison_comp_fst (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
    [HasPullback (G.map f) (G.map g)] :
    pullbackComparison G f g ≫ pullback.fst _ _ = G.map (pullback.fst f g) :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
/--
theorem `pullbackComparison_comp_snd` / 定理 `pullbackComparison_comp_snd`

English:
theorem pullbackComparison_comp_snd
  statement: (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
  proof: pullback.lift_snd _ _ _

中文:
定理 pullbackComparison_comp_snd
  结论: (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
  证明: pullback.lift_snd _ _ _

Depends on / 依赖: lift_snd, pullback, pullback.lift_snd
-/
theorem pullbackComparison_comp_snd (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
    [HasPullback (G.map f) (G.map g)] :
    pullbackComparison G f g ≫ pullback.snd _ _ = G.map (pullback.snd f g) :=
  pullback.lift_snd _ _ _

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `map_lift_pullbackComparison` / 定理 `map_lift_pullbackComparison`

English:
theorem map_lift_pullbackComparison
  statement: (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
  proof: by
  ext <;> simp [← G.map_comp]

中文:
定理 map_lift_pullbackComparison
  结论: (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
  证明: by
  ext <;> simp [← G.map_comp]

Depends on / 依赖: G.map_comp, map_comp
-/
theorem map_lift_pullbackComparison (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
    [HasPullback (G.map f) (G.map g)] {W : C} {h : W ⟶ X} {k : W ⟶ Y} (w : h ≫ f = k ≫ g) :
    G.map (pullback.lift _ _ w) ≫ pullbackComparison G f g =
      pullback.lift (G.map h) (G.map k) (by simp only [← G.map_comp, w]) := by
  ext <;> simp [← G.map_comp]

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/--
lemma `pullbackComparison_comp` / 引理 `pullbackComparison_comp`

English:
lemma pullbackComparison_comp
  statement: {E : Type*} [Category* E] (F : C ⥤ D) (G : D ⥤ E) {X Y S : C}
  proof: by
  ext
  · rw [pullbackComparison_comp_fst]
    simp [← Functor.map_comp]
  · rw [pullbackComparison_comp_snd]
    simp [← Functor.map_comp]

中文:
引理 pullbackComparison_comp
  结论: {E : 类型} [Category* E] (F : C ⥤ D) (G : D ⥤ E) {X Y S : C}
  证明: by
  ext
  · rw [pullbackComparison_comp_fst]
    simp [← Functor.map_comp]
  · rw [pullbackComparison_comp_snd]
    simp [← Functor.map_comp]

Depends on / 依赖: Functor, Functor.map_comp, map_comp, pullbackComparison_comp_fst, pullbackComparison_comp_snd
-/
lemma pullbackComparison_comp {E : Type*} [Category* E] (F : C ⥤ D) (G : D ⥤ E) {X Y S : C}
    (f : X ⟶ S) (g : Y ⟶ S) [HasPullback f g] [HasPullback (F.map f) (F.map g)]
    [HasPullback (G.map (F.map f)) (G.map (F.map g))]
    [HasPullback ((F ⋙ G).map f) ((F ⋙ G).map g)] :
    pullbackComparison (F ⋙ G) f g = G.map (pullbackComparison F f g) ≫
      pullbackComparison G (F.map f) (F.map g) := by
  ext
  · rw [pullbackComparison_comp_fst]
    simp [← Functor.map_comp]
  · rw [pullbackComparison_comp_snd]
    simp [← Functor.map_comp]

/--
Definition of `pushoutComparison` / `pushoutComparison` 的定义

English:
definition pushoutComparison
  signature: (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] [HasPushout (G.map f) (G.map g)]
  body: pushout.desc (G.map (pushout.inl _ _)) (G.map (pushout.inr _ _))
    (by simp only [← G.map_comp, pushout.condition])

@[reassoc (attr := simp)]

中文:
定义 pushoutComparison
  签名: (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] [HasPushout (G.map f) (G.map g)]
  定义体: pushout.desc (G.map (pushout.inl _ _)) (G.map (pushout.inr _ _))
    (by simp only [← G.map_comp, pushout.condition])

@[reassoc (attr := simp)]

Depends on / 依赖: G.map, G.map_comp, condition, map_comp, pushout, pushout.condition, pushout.desc, pushout.inl, pushout.inr
-/
def pushoutComparison (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] [HasPushout (G.map f) (G.map g)] :
    pushout (G.map f) (G.map g) ⟶ G.obj (pushout f g) :=
  pushout.desc (G.map (pushout.inl _ _)) (G.map (pushout.inr _ _))
    (by simp only [← G.map_comp, pushout.condition])

@[reassoc (attr := simp)]
/--
theorem `inl_comp_pushoutComparison` / 定理 `inl_comp_pushoutComparison`

English:
theorem inl_comp_pushoutComparison
  statement: (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g]
  proof: pushout.inl_desc _ _ _

@[reassoc (attr := simp)]

中文:
定理 inl_comp_pushoutComparison
  结论: (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g]
  证明: pushout.inl_desc _ _ _

@[reassoc (attr := simp)]

Depends on / 依赖: inl_desc, pushout, pushout.inl_desc
-/
theorem inl_comp_pushoutComparison (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g]
    [HasPushout (G.map f) (G.map g)] : pushout.inl _ _ ≫ pushoutComparison G f g =
      G.map (pushout.inl _ _) :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
/--
theorem `inr_comp_pushoutComparison` / 定理 `inr_comp_pushoutComparison`

English:
theorem inr_comp_pushoutComparison
  statement: (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g]
  proof: pushout.inr_desc _ _ _

中文:
定理 inr_comp_pushoutComparison
  结论: (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g]
  证明: pushout.inr_desc _ _ _

Depends on / 依赖: inr_desc, pushout, pushout.inr_desc
-/
theorem inr_comp_pushoutComparison (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g]
    [HasPushout (G.map f) (G.map g)] : pushout.inr _ _ ≫ pushoutComparison G f g =
      G.map (pushout.inr _ _) :=
  pushout.inr_desc _ _ _

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `pushoutComparison_map_desc` / 定理 `pushoutComparison_map_desc`

English:
theorem pushoutComparison_map_desc
  statement: (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g]
  proof: by
  ext <;> simp [← G.map_comp]

中文:
定理 pushoutComparison_map_desc
  结论: (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g]
  证明: by
  ext <;> simp [← G.map_comp]

Depends on / 依赖: G.map_comp, map_comp
-/
theorem pushoutComparison_map_desc (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g]
    [HasPushout (G.map f) (G.map g)] {W : C} {h : Y ⟶ W} {k : Z ⟶ W} (w : f ≫ h = g ≫ k) :
    pushoutComparison G f g ≫ G.map (pushout.desc _ _ w) =
      pushout.desc (G.map h) (G.map k) (by simp only [← G.map_comp, w]) := by
  ext <;> simp [← G.map_comp]

end

section PullbackSymmetry

open WalkingCospan

variable (f : X ⟶ Z) (g : Y ⟶ Z)

/--
theorem `hasPullback_symmetry` / 定理 `hasPullback_symmetry`

English:
theorem hasPullback_symmetry
  given: [HasPullback f g]
  statement: HasPullback g f
  proof: ⟨⟨⟨_, PullbackCone.flipIsLimit (pullbackIsPullback f g)⟩⟩⟩

中文:
定理 hasPullback_symmetry
  条件: [HasPullback f g]
  结论: HasPullback g f
  证明: ⟨⟨⟨_, PullbackCone.flipIsLimit (pullbackIsPullback f g)⟩⟩⟩

Depends on / 依赖: PullbackCone, PullbackCone.flipIsLimit, flipIsLimit, pullbackIsPullback
-/
theorem hasPullback_symmetry [HasPullback f g] : HasPullback g f :=
  ⟨⟨⟨_, PullbackCone.flipIsLimit (pullbackIsPullback f g)⟩⟩⟩

attribute [local instance] hasPullback_symmetry

/--
Definition of `pullbackSymmetry` / `pullbackSymmetry` 的定义

English:
definition pullbackSymmetry
  signature: [HasPullback f g]
  body: IsLimit.conePointUniqueUpToIso
    (PullbackCone.flipIsLimit (pullbackIsPullback f g)) (limit.isLimit _)

中文:
定义 pullbackSymmetry
  签名: [HasPullback f g]
  定义体: IsLimit.conePointUniqueUpToIso
    (PullbackCone.flipIsLimit (pullbackIsPullback f g)) (limit.isLimit _)

Depends on / 依赖: IsLimit, IsLimit.conePointUniqueUpToIso, PullbackCone, PullbackCone.flipIsLimit, conePointUniqueUpToIso, flipIsLimit, isLimit, limit.isLimit, pullbackIsPullback
-/
def pullbackSymmetry [HasPullback f g] : pullback f g ≅ pullback g f :=
  IsLimit.conePointUniqueUpToIso
    (PullbackCone.flipIsLimit (pullbackIsPullback f g)) (limit.isLimit _)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `pullbackSymmetry_hom_comp_fst` / 定理 `pullbackSymmetry_hom_comp_fst`

English:
theorem pullbackSymmetry_hom_comp_fst
  given: [HasPullback f g]
  proof: by simp [pullbackSymmetry]

中文:
定理 pullbackSymmetry_hom_comp_fst
  条件: [HasPullback f g]
  证明: by simp [pullbackSymmetry]

Depends on / 依赖: IsStableUnderBaseChange, IsStableUnderBaseChange.respectsIso, pullbackSymmetry, respectsIso
-/
theorem pullbackSymmetry_hom_comp_fst [HasPullback f g] :
    (pullbackSymmetry f g).hom ≫ pullback.fst g f = pullback.snd f g := by simp [pullbackSymmetry]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `pullbackSymmetry_hom_comp_snd` / 定理 `pullbackSymmetry_hom_comp_snd`

English:
theorem pullbackSymmetry_hom_comp_snd
  given: [HasPullback f g]
  proof: by simp [pullbackSymmetry]

@[reassoc (attr := simp)]

中文:
定理 pullbackSymmetry_hom_comp_snd
  条件: [HasPullback f g]
  证明: by simp [pullbackSymmetry]

@[reassoc (attr := simp)]

Depends on / 依赖: pullbackSymmetry
-/
theorem pullbackSymmetry_hom_comp_snd [HasPullback f g] :
    (pullbackSymmetry f g).hom ≫ pullback.snd g f = pullback.fst f g := by simp [pullbackSymmetry]

@[reassoc (attr := simp)]
/--
theorem `pullbackSymmetry_inv_comp_fst` / 定理 `pullbackSymmetry_inv_comp_fst`

English:
theorem pullbackSymmetry_inv_comp_fst
  given: [HasPullback f g]
  proof: by simp [Iso.inv_comp_eq]

@[reassoc (attr := simp)]

中文:
定理 pullbackSymmetry_inv_comp_fst
  条件: [HasPullback f g]
  证明: by simp [Iso.inv_comp_eq]

@[reassoc (attr := simp)]

Depends on / 依赖: Iso.inv_comp_eq, inv_comp_eq
-/
theorem pullbackSymmetry_inv_comp_fst [HasPullback f g] :
    (pullbackSymmetry f g).inv ≫ pullback.fst f g = pullback.snd g f := by simp [Iso.inv_comp_eq]

@[reassoc (attr := simp)]
/--
theorem `pullbackSymmetry_inv_comp_snd` / 定理 `pullbackSymmetry_inv_comp_snd`

English:
theorem pullbackSymmetry_inv_comp_snd
  given: [HasPullback f g]
  proof: by simp [Iso.inv_comp_eq]

中文:
定理 pullbackSymmetry_inv_comp_snd
  条件: [HasPullback f g]
  证明: by simp [Iso.inv_comp_eq]

Depends on / 依赖: Iso.inv_comp_eq, inv_comp_eq
-/
theorem pullbackSymmetry_inv_comp_snd [HasPullback f g] :
    (pullbackSymmetry f g).inv ≫ pullback.snd f g = pullback.fst g f := by simp [Iso.inv_comp_eq]

end PullbackSymmetry

section PushoutSymmetry

open WalkingCospan

variable (f : X ⟶ Y) (g : X ⟶ Z)

/--
theorem `hasPushout_symmetry` / 定理 `hasPushout_symmetry`

English:
theorem hasPushout_symmetry
  given: [HasPushout f g]
  statement: HasPushout g f
  proof: ⟨⟨⟨_, PushoutCocone.flipIsColimit (pushoutIsPushout f g)⟩⟩⟩

中文:
定理 hasPushout_symmetry
  条件: [HasPushout f g]
  结论: HasPushout g f
  证明: ⟨⟨⟨_, PushoutCocone.flipIsColimit (pushoutIsPushout f g)⟩⟩⟩

Depends on / 依赖: PushoutCocone, PushoutCocone.flipIsColimit, flipIsColimit, pushoutIsPushout
-/
theorem hasPushout_symmetry [HasPushout f g] : HasPushout g f :=
  ⟨⟨⟨_, PushoutCocone.flipIsColimit (pushoutIsPushout f g)⟩⟩⟩

attribute [local instance] hasPushout_symmetry

/--
Definition of `pushoutSymmetry` / `pushoutSymmetry` 的定义

English:
definition pushoutSymmetry
  signature: [HasPushout f g]
  body: IsColimit.coconePointUniqueUpToIso
    (PushoutCocone.flipIsColimit (pushoutIsPushout f g)) (colimit.isColimit _)

@[reassoc (attr := simp)]

中文:
定义 pushoutSymmetry
  签名: [HasPushout f g]
  定义体: IsColimit.coconePointUniqueUpToIso
    (PushoutCocone.flipIsColimit (pushoutIsPushout f g)) (colimit.isColimit _)

@[reassoc (attr := simp)]

Depends on / 依赖: IsColimit, IsColimit.coconePointUniqueUpToIso, PushoutCocone, PushoutCocone.flipIsColimit, coconePointUniqueUpToIso, colimit, colimit.isColimit, flipIsColimit, isColimit, pushoutIsPushout
-/
def pushoutSymmetry [HasPushout f g] : pushout f g ≅ pushout g f :=
  IsColimit.coconePointUniqueUpToIso
    (PushoutCocone.flipIsColimit (pushoutIsPushout f g)) (colimit.isColimit _)

@[reassoc (attr := simp)]
/--
theorem `inl_comp_pushoutSymmetry_hom` / 定理 `inl_comp_pushoutSymmetry_hom`

English:
theorem inl_comp_pushoutSymmetry_hom
  given: [HasPushout f g]
  proof: (colimit.isColimit (span f g)).comp_coconePointUniqueUpToIso_hom
    (PushoutCocone.flipIsColimit (pushoutIsPushout g f)) _

@[reassoc (attr := simp)]

中文:
定理 inl_comp_pushoutSymmetry_hom
  条件: [HasPushout f g]
  证明: (colimit.isColimit (span f g)).comp_coconePointUniqueUpToIso_hom
    (PushoutCocone.flipIsColimit (pushoutIsPushout g f)) _

@[reassoc (attr := simp)]

Depends on / 依赖: PushoutCocone, PushoutCocone.flipIsColimit, colimit, colimit.isColimit, comp_coconePointUniqueUpToIso_hom, flipIsColimit, isColimit, pushoutIsPushout
-/
theorem inl_comp_pushoutSymmetry_hom [HasPushout f g] :
    pushout.inl _ _ ≫ (pushoutSymmetry f g).hom = pushout.inr _ _ :=
  (colimit.isColimit (span f g)).comp_coconePointUniqueUpToIso_hom
    (PushoutCocone.flipIsColimit (pushoutIsPushout g f)) _

@[reassoc (attr := simp)]
/--
theorem `inr_comp_pushoutSymmetry_hom` / 定理 `inr_comp_pushoutSymmetry_hom`

English:
theorem inr_comp_pushoutSymmetry_hom
  given: [HasPushout f g]
  proof: (colimit.isColimit (span f g)).comp_coconePointUniqueUpToIso_hom
    (PushoutCocone.flipIsColimit (pushoutIsPushout g f)) _

@[reassoc (attr := simp)]

中文:
定理 inr_comp_pushoutSymmetry_hom
  条件: [HasPushout f g]
  证明: (colimit.isColimit (span f g)).comp_coconePointUniqueUpToIso_hom
    (PushoutCocone.flipIsColimit (pushoutIsPushout g f)) _

@[reassoc (attr := simp)]

Depends on / 依赖: PushoutCocone, PushoutCocone.flipIsColimit, colimit, colimit.isColimit, comp_coconePointUniqueUpToIso_hom, flipIsColimit, isColimit, pushoutIsPushout
-/
theorem inr_comp_pushoutSymmetry_hom [HasPushout f g] :
    pushout.inr _ _ ≫ (pushoutSymmetry f g).hom = pushout.inl _ _ :=
  (colimit.isColimit (span f g)).comp_coconePointUniqueUpToIso_hom
    (PushoutCocone.flipIsColimit (pushoutIsPushout g f)) _

@[reassoc (attr := simp)]
/--
theorem `inl_comp_pushoutSymmetry_inv` / 定理 `inl_comp_pushoutSymmetry_inv`

English:
theorem inl_comp_pushoutSymmetry_inv
  given: [HasPushout f g]
  proof: by simp [Iso.comp_inv_eq]

@[reassoc (attr := simp)]

中文:
定理 inl_comp_pushoutSymmetry_inv
  条件: [HasPushout f g]
  证明: by simp [Iso.comp_inv_eq]

@[reassoc (attr := simp)]

Depends on / 依赖: Iso.comp_inv_eq, comp_inv_eq
-/
theorem inl_comp_pushoutSymmetry_inv [HasPushout f g] :
    pushout.inl _ _ ≫ (pushoutSymmetry f g).inv = pushout.inr _ _ := by simp [Iso.comp_inv_eq]

@[reassoc (attr := simp)]
/--
theorem `inr_comp_pushoutSymmetry_inv` / 定理 `inr_comp_pushoutSymmetry_inv`

English:
theorem inr_comp_pushoutSymmetry_inv
  given: [HasPushout f g]
  proof: by simp [Iso.comp_inv_eq]

中文:
定理 inr_comp_pushoutSymmetry_inv
  条件: [HasPushout f g]
  证明: by simp [Iso.comp_inv_eq]

Depends on / 依赖: Iso.comp_inv_eq, comp_inv_eq
-/
theorem inr_comp_pushoutSymmetry_inv [HasPushout f g] :
    pushout.inr _ _ ≫ (pushoutSymmetry f g).inv = pushout.inl _ _ := by simp [Iso.comp_inv_eq]

end PushoutSymmetry

/--
Definition of `HasPullbacksAlong` / `HasPullbacksAlong` 的定义

English:
abbreviation HasPullbacksAlong
  signature: (f : X ⟶ Y)
  body: forall {W} (h : W ⟶ Y), HasPullback h f

中文:
缩写 HasPullbacksAlong
  签名: (f : X ⟶ Y)
  定义体: forall {W} (h : W ⟶ Y), HasPullback h f

Depends on / 依赖: HasPullback
-/
abbrev HasPullbacksAlong (f : X ⟶ Y) : Prop := forall {W} (h : W ⟶ Y), HasPullback h f

/--
Definition of `HasPushoutsAlong` / `HasPushoutsAlong` 的定义

English:
abbreviation HasPushoutsAlong
  signature: (f : X ⟶ Y)
  body: forall {W} (h : X ⟶ W), HasPushout h f

中文:
缩写 HasPushoutsAlong
  签名: (f : X ⟶ Y)
  定义体: forall {W} (h : X ⟶ W), HasPushout h f

Depends on / 依赖: HasPushout
-/
abbrev HasPushoutsAlong (f : X ⟶ Y) : Prop := forall {W} (h : X ⟶ W), HasPushout h f

variable (C)

/-- A category `HasPullbacks` if it has all limits of shape `WalkingCospan`, i.e. if it has a
pullback for every pair of morphisms with the same codomain. -/
@[stacks 001W]
/--
Definition of `HasPullbacks` / `HasPullbacks` 的定义

English:
abbreviation HasPullbacks
  body: HasLimitsOfShape WalkingCospan C

中文:
缩写 HasPullbacks
  定义体: HasLimitsOfShape WalkingCospan C

Depends on / 依赖: HasLimitsOfShape, WalkingCospan
-/
abbrev HasPullbacks :=
  HasLimitsOfShape WalkingCospan C

/--
Definition of `HasPushouts` / `HasPushouts` 的定义

English:
abbreviation HasPushouts
  body: HasColimitsOfShape WalkingSpan C

中文:
缩写 HasPushouts
  定义体: HasColimitsOfShape WalkingSpan C

Depends on / 依赖: HasColimitsOfShape, WalkingSpan
-/
abbrev HasPushouts :=
  HasColimitsOfShape WalkingSpan C

/--
theorem `hasPullbacks_of_hasLimit_cospan` / 定理 `hasPullbacks_of_hasLimit_cospan`

English:
theorem hasPullbacks_of_hasLimit_cospan
  proof: { has_limit := fun F => hasLimit_of_iso (diagramIsoCospan F).symm }

中文:
定理 hasPullbacks_of_hasLimit_cospan
  证明: { has_limit := fun F => hasLimit_of_iso (diagramIsoCospan F).symm }

Depends on / 依赖: diagramIsoCospan, hasLimit_of_iso, has_limit
-/
theorem hasPullbacks_of_hasLimit_cospan
    [forall {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}, HasLimit (cospan f g)] : HasPullbacks C :=
  { has_limit := fun F => hasLimit_of_iso (diagramIsoCospan F).symm }

/--
theorem `hasPushouts_of_hasColimit_span` / 定理 `hasPushouts_of_hasColimit_span`

English:
theorem hasPushouts_of_hasColimit_span
  proof: { has_colimit := fun F => hasColimit_of_iso (diagramIsoSpan F) }

中文:
定理 hasPushouts_of_hasColimit_span
  证明: { has_colimit := fun F => hasColimit_of_iso (diagramIsoSpan F) }

Depends on / 依赖: diagramIsoSpan, hasColimit_of_iso, has_colimit
-/
theorem hasPushouts_of_hasColimit_span
    [forall {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}, HasColimit (span f g)] : HasPushouts C :=
  { has_colimit := fun F => hasColimit_of_iso (diagramIsoSpan F) }

/-- The duality equivalence `WalkingSpanᵒᵖ ≌ WalkingCospan` -/
@[simps!]
/--
Definition of `walkingSpanOpEquiv` / `walkingSpanOpEquiv` 的定义

English:
definition walkingSpanOpEquiv
  signature: : WalkingSpanᵒᵖ ≌ WalkingCospan
  body: widePushoutShapeOpEquiv _

中文:
定义 walkingSpanOpEquiv
  签名: : WalkingSpanᵒᵖ ≌ WalkingCospan
  定义体: widePushoutShapeOpEquiv _

Depends on / 依赖: widePushoutShapeOpEquiv
-/
def walkingSpanOpEquiv : WalkingSpanᵒᵖ ≌ WalkingCospan :=
  widePushoutShapeOpEquiv _

/-- The duality equivalence `WalkingCospanᵒᵖ ≌ WalkingSpan` -/
@[simps!]
/--
Definition of `walkingCospanOpEquiv` / `walkingCospanOpEquiv` 的定义

English:
definition walkingCospanOpEquiv
  signature: : WalkingCospanᵒᵖ ≌ WalkingSpan
  body: widePullbackShapeOpEquiv _

中文:
定义 walkingCospanOpEquiv
  签名: : WalkingCospanᵒᵖ ≌ WalkingSpan
  定义体: widePullbackShapeOpEquiv _

Depends on / 依赖: widePullbackShapeOpEquiv
-/
def walkingCospanOpEquiv : WalkingCospanᵒᵖ ≌ WalkingSpan :=
  widePullbackShapeOpEquiv _

-- see Note [lower instance priority]
/-- Having wide pullback at any universe level implies having binary pullbacks. -/
instance (priority := 100) hasPullbacks_of_hasWidePullbacks (D : Type u) [Category.{v} D]
    [HasWidePullbacks.{w} D] : HasPullbacks.{v, u} D :=
  hasWidePullbacks_shrink WalkingPair

-- see Note [lower instance priority]
/-- Having wide pushout at any universe level implies having binary pushouts. -/
instance (priority := 100) hasPushouts_of_hasWidePushouts (D : Type u) [Category.{v} D]
    [HasWidePushouts.{w} D] : HasPushouts.{v, u} D :=
  hasWidePushouts_shrink WalkingPair

/--
theorem `hasPullback_symmetry_of_hasPullbacksAlong` / 定理 `hasPullback_symmetry_of_hasPullbacksAlong`

English:
theorem hasPullback_symmetry_of_hasPullbacksAlong
  statement: {S X Y : C} {f : X ⟶ S} [HasPullbacksAlong f]
  proof: hasPullback_symmetry g f

中文:
定理 hasPullback_symmetry_of_hasPullbacksAlong
  结论: {S X Y : C} {f : X ⟶ S} [HasPullbacksAlong f]
  证明: hasPullback_symmetry g f

Depends on / 依赖: hasPullback_symmetry
-/
theorem hasPullback_symmetry_of_hasPullbacksAlong {S X Y : C} {f : X ⟶ S} [HasPullbacksAlong f]
    {g : Y ⟶ S} : HasPullback f g :=
  hasPullback_symmetry g f

/--
theorem `hasPushouts_symmetry_of_hasPushoutsAlong` / 定理 `hasPushouts_symmetry_of_hasPushoutsAlong`

English:
theorem hasPushouts_symmetry_of_hasPushoutsAlong
  statement: {S X Y : C} {f : S ⟶ X} [HasPushoutsAlong f]
  proof: hasPushout_symmetry g f

中文:
定理 hasPushouts_symmetry_of_hasPushoutsAlong
  结论: {S X Y : C} {f : S ⟶ X} [HasPushoutsAlong f]
  证明: hasPushout_symmetry g f

Depends on / 依赖: hasPushout_symmetry
-/
theorem hasPushouts_symmetry_of_hasPushoutsAlong {S X Y : C} {f : S ⟶ X} [HasPushoutsAlong f]
    {g : S ⟶ Y} : HasPushout f g :=
  hasPushout_symmetry g f

section Products

variable {C}

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `pullbackProdFstIsoProd` / `pullbackProdFstIsoProd` 的定义

English:
definition pullbackProdFstIsoProd
  signature: {X Y : C} (f : X ⟶ Y) (Z : C)
  body: prod.lift (pullback.fst _ _) (pullback.snd _ _ ≫ prod.snd)
  inv := pullback.lift prod.fst (prod.map f (𝟙 Z))
  hom_inv_id := by
    apply pullback.hom_ext
    · simp
    · apply prod.hom_ext <;> simp [pullback.condition]

中文:
定义 pullbackProdFstIsoProd
  签名: {X Y : C} (f : X ⟶ Y) (Z : C)
  定义体: prod.lift (pullback.fst _ _) (pullback.snd _ _ ≫ prod.snd)
  inv := pullback.lift prod.fst (prod.map f (𝟙 Z))
  hom_inv_id := by
    apply pullback.hom_ext
    · simp
    · apply prod.hom_ext <;> simp [pullback.condition]

Depends on / 依赖: prod.lift, prod.snd, pullback, pullback.fst, pullback.snd
-/
noncomputable def pullbackProdFstIsoProd {X Y : C} (f : X ⟶ Y) (Z : C)
    [HasBinaryProduct Y Z] [HasBinaryProduct X Z] [HasPullback f (prod.fst : Y ⨯ Z ⟶ _)] :
    pullback f (prod.fst : Y ⨯ Z ⟶ _) ≅ X ⨯ Z where
  hom := prod.lift (pullback.fst _ _) (pullback.snd _ _ ≫ prod.snd)
  inv := pullback.lift prod.fst (prod.map f (𝟙 Z))
  hom_inv_id := by
    apply pullback.hom_ext
    · simp
    · apply prod.hom_ext <;> simp [pullback.condition]

section

variable {X Y : C} (f : X ⟶ Y) (Z : C) [HasBinaryProduct Y Z] [HasBinaryProduct X Z]
  [HasPullback f (prod.fst : Y ⨯ Z ⟶ _)]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `pullbackProdFstIsoProd_hom_fst` / 引理 `pullbackProdFstIsoProd_hom_fst`

English:
lemma pullbackProdFstIsoProd_hom_fst
  proof: by
  simp [pullbackProdFstIsoProd]

中文:
引理 pullbackProdFstIsoProd_hom_fst
  证明: by
  simp [pullbackProdFstIsoProd]

Depends on / 依赖: pullbackProdFstIsoProd
-/
lemma pullbackProdFstIsoProd_hom_fst :
    (pullbackProdFstIsoProd f Z).hom ≫ prod.fst = pullback.fst _ _ := by
  simp [pullbackProdFstIsoProd]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `pullbackProdFstIsoProd_hom_snd` / 引理 `pullbackProdFstIsoProd_hom_snd`

English:
lemma pullbackProdFstIsoProd_hom_snd
  proof: by
  simp [pullbackProdFstIsoProd]

中文:
引理 pullbackProdFstIsoProd_hom_snd
  证明: by
  simp [pullbackProdFstIsoProd]

Depends on / 依赖: pullbackProdFstIsoProd
-/
lemma pullbackProdFstIsoProd_hom_snd :
    (pullbackProdFstIsoProd f Z).hom ≫ prod.snd = pullback.snd _ _ ≫ prod.snd := by
  simp [pullbackProdFstIsoProd]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `pullbackProdFstIsoProd_inv_fst` / 引理 `pullbackProdFstIsoProd_inv_fst`

English:
lemma pullbackProdFstIsoProd_inv_fst
  proof: by
  simp [pullbackProdFstIsoProd]

中文:
引理 pullbackProdFstIsoProd_inv_fst
  证明: by
  simp [pullbackProdFstIsoProd]

Depends on / 依赖: pullbackProdFstIsoProd
-/
lemma pullbackProdFstIsoProd_inv_fst :
    (pullbackProdFstIsoProd f Z).inv ≫ pullback.fst _ _ = prod.fst := by
  simp [pullbackProdFstIsoProd]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `pullbackProdFstIsoProd_inv_snd_fst` / 引理 `pullbackProdFstIsoProd_inv_snd_fst`

English:
lemma pullbackProdFstIsoProd_inv_snd_fst
  proof: by
  simp [pullbackProdFstIsoProd]

中文:
引理 pullbackProdFstIsoProd_inv_snd_fst
  证明: by
  simp [pullbackProdFstIsoProd]

Depends on / 依赖: pullbackProdFstIsoProd
-/
lemma pullbackProdFstIsoProd_inv_snd_fst :
    (pullbackProdFstIsoProd f Z).inv ≫ pullback.snd _ _ ≫ prod.fst = prod.fst ≫ f := by
  simp [pullbackProdFstIsoProd]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `pullbackProdFstIsoProd_inv_snd_snd` / 引理 `pullbackProdFstIsoProd_inv_snd_snd`

English:
lemma pullbackProdFstIsoProd_inv_snd_snd
  proof: by
  simp [pullbackProdFstIsoProd]

中文:
引理 pullbackProdFstIsoProd_inv_snd_snd
  证明: by
  simp [pullbackProdFstIsoProd]

Depends on / 依赖: pullbackProdFstIsoProd
-/
lemma pullbackProdFstIsoProd_inv_snd_snd :
    (pullbackProdFstIsoProd f Z).inv ≫ pullback.snd _ _ ≫ prod.snd = prod.snd := by
  simp [pullbackProdFstIsoProd]

end

section

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `pullbackProdSndIsoProd` / `pullbackProdSndIsoProd` 的定义

English:
definition pullbackProdSndIsoProd
  signature: {X Y : C} (f : X ⟶ Y) (Z : C)
  body: prod.lift (pullback.fst _ _ ≫ prod.fst) (pullback.snd _ _)
  inv := pullback.lift (prod.map (𝟙 Z) f) prod.snd
  hom_inv_id := by
    apply pullback.hom_ext
    · apply prod.hom_ext <;> simp [pullback.condition]
    · simp

中文:
定义 pullbackProdSndIsoProd
  签名: {X Y : C} (f : X ⟶ Y) (Z : C)
  定义体: prod.lift (pullback.fst _ _ ≫ prod.fst) (pullback.snd _ _)
  inv := pullback.lift (prod.map (𝟙 Z) f) prod.snd
  hom_inv_id := by
    apply pullback.hom_ext
    · apply prod.hom_ext <;> simp [pullback.condition]
    · simp

Depends on / 依赖: prod.fst, prod.lift, pullback, pullback.fst, pullback.snd
-/
noncomputable def pullbackProdSndIsoProd {X Y : C} (f : X ⟶ Y) (Z : C)
    [HasBinaryProduct Z Y] [HasBinaryProduct Z X] [HasPullback (prod.snd : Z ⨯ Y ⟶ Y) f] :
    pullback (prod.snd : Z ⨯ Y ⟶ Y) f ≅ Z ⨯ X where
  hom := prod.lift (pullback.fst _ _ ≫ prod.fst) (pullback.snd _ _)
  inv := pullback.lift (prod.map (𝟙 Z) f) prod.snd
  hom_inv_id := by
    apply pullback.hom_ext
    · apply prod.hom_ext <;> simp [pullback.condition]
    · simp

variable {X Y : C} (f : X ⟶ Y) (Z : C) [HasBinaryProduct Z Y] [HasBinaryProduct Z X]
  [HasPullback (prod.snd : Z ⨯ Y ⟶ Y) f]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `pullbackProdSndIsoProd_hom_fst` / 引理 `pullbackProdSndIsoProd_hom_fst`

English:
lemma pullbackProdSndIsoProd_hom_fst
  proof: by
  simp [pullbackProdSndIsoProd]

中文:
引理 pullbackProdSndIsoProd_hom_fst
  证明: by
  simp [pullbackProdSndIsoProd]

Depends on / 依赖: pullbackProdSndIsoProd
-/
lemma pullbackProdSndIsoProd_hom_fst :
    (pullbackProdSndIsoProd f Z).hom ≫ prod.fst = pullback.fst _ _ ≫ prod.fst := by
  simp [pullbackProdSndIsoProd]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `pullbackProdSndIsoProd_hom_snd` / 引理 `pullbackProdSndIsoProd_hom_snd`

English:
lemma pullbackProdSndIsoProd_hom_snd
  proof: by
  simp [pullbackProdSndIsoProd]

中文:
引理 pullbackProdSndIsoProd_hom_snd
  证明: by
  simp [pullbackProdSndIsoProd]

Depends on / 依赖: pullbackProdSndIsoProd
-/
lemma pullbackProdSndIsoProd_hom_snd :
    (pullbackProdSndIsoProd f Z).hom ≫ prod.snd = pullback.snd _ _ := by
  simp [pullbackProdSndIsoProd]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `pullbackProdSndIsoProd_inv_fst_fst` / 引理 `pullbackProdSndIsoProd_inv_fst_fst`

English:
lemma pullbackProdSndIsoProd_inv_fst_fst
  proof: by
  simp [pullbackProdSndIsoProd]

中文:
引理 pullbackProdSndIsoProd_inv_fst_fst
  证明: by
  simp [pullbackProdSndIsoProd]

Depends on / 依赖: pullbackProdSndIsoProd
-/
lemma pullbackProdSndIsoProd_inv_fst_fst :
    (pullbackProdSndIsoProd f Z).inv ≫ pullback.fst _ _ ≫ prod.fst = prod.fst := by
  simp [pullbackProdSndIsoProd]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `pullbackProdSndIsoProd_inv_fst_snd` / 引理 `pullbackProdSndIsoProd_inv_fst_snd`

English:
lemma pullbackProdSndIsoProd_inv_fst_snd
  proof: by
  simp [pullbackProdSndIsoProd]

中文:
引理 pullbackProdSndIsoProd_inv_fst_snd
  证明: by
  simp [pullbackProdSndIsoProd]

Depends on / 依赖: pullbackProdSndIsoProd
-/
lemma pullbackProdSndIsoProd_inv_fst_snd :
    (pullbackProdSndIsoProd f Z).inv ≫ pullback.fst _ _ ≫ prod.snd = prod.snd ≫ f := by
  simp [pullbackProdSndIsoProd]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `pullbackProdSndIsoProd_inv_snd` / 引理 `pullbackProdSndIsoProd_inv_snd`

English:
lemma pullbackProdSndIsoProd_inv_snd
  proof: by
  simp [pullbackProdSndIsoProd]

中文:
引理 pullbackProdSndIsoProd_inv_snd
  证明: by
  simp [pullbackProdSndIsoProd]

Depends on / 依赖: pullbackProdSndIsoProd
-/
lemma pullbackProdSndIsoProd_inv_snd :
    (pullbackProdSndIsoProd f Z).inv ≫ pullback.snd _ _ = prod.snd := by
  simp [pullbackProdSndIsoProd]

end

end Products

end CategoryTheory.Limits
