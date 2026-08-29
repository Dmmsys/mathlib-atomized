/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.Square
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Square
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.CategoryTheory.Sites.Sheafification

/-!
# Mayer-Vietoris squares

The purpose of this file is to allow the formalization of long exact
Mayer-Vietoris sequences in sheaf cohomology. If `X₄` is an open subset
of a topological space that is covered by two open subsets `X₂` and `X₃`,
it is known that there is a long exact sequence
`... ⟶ H^q(X₄) ⟶ H^q(X₂) ⊞ H^q(X₃) ⟶ H^q(X₁) ⟶ H^{q+1}(X₄) ⟶ ...`
where `X₁` is the intersection of `X₂` and `X₃`, and `H^q` are the
cohomology groups with values in an abelian sheaf.

In this file, we introduce a structure
`GrothendieckTopology.MayerVietorisSquare` which extends `Square C`,
and asserts properties which shall imply the existence of long
exact Mayer-Vietoris sequences in sheaf cohomology (TODO).
We require that the map `X₁ ⟶ X₃` is a monomorphism and
that the square in `C` becomes a pushout square in
the category of sheaves after the application of the
functor `yoneda ⋙ presheafToSheaf J _`. Note that in the
standard case of a covering by two open subsets, all
the morphisms in the square would be monomorphisms,
but this dissymmetry allows the example of Nisnevich distinguished
squares in the case of the Nisnevich topology on schemes (in which case
`f₂₄ : X₂ ⟶ X₄` shall be an open immersion and
`f₃₄ : X₃ ⟶ X₄` an étale map that is an isomorphism over
the closed (reduced) subscheme `X₄ - X₂`,
and `X₁` shall be the pullback of `f₂₄` and `f₃₄`.).

Given a Mayer-Vietoris square `S` and a presheaf `P` on `C`,
we introduce a sheaf condition `S.SheafCondition P` and show
that it is indeed satisfied by sheaves.

## References
* https://stacks.math.columbia.edu/tag/08GL

-/

@[expose] public section
universe v v' u u'

namespace CategoryTheory

open Limits Opposite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `Sheaf.isPullback_square_op_map_yoneda_presheafToSheaf_yoneda_iff` / 引理 `Sheaf.isPullback_square_op_map_yoneda_presheafToSheaf_yoneda_iff`

English:
lemma Sheaf.isPullback_square_op_map_yoneda_presheafToSheaf_yoneda_iff
  proof: by
  refine Square.IsPullback.iff_of_equiv _ _
    (((sheafificationAdjunction J (Type v)).homEquiv _ _).trans yonedaEquiv)
    (((sheafificationAdjunction J (Type v)).homEquiv _ _).trans yonedaEquiv)
    (((sheafificationAdjunction J (Type v)).homEquiv _ _).trans yonedaEquiv)
    (((sheafificationA

中文:
引理 Sheaf.isPullback_square_op_map_yoneda_presheafToSheaf_yoneda_iff
  证明: by
  refine Square.IsPullback.iff_of_equiv _ _
    (((sheafificationAdjunction J (Type v)).homEquiv _ _).trans yonedaEquiv)
    (((sheafificationAdjunction J (Type v)).homEquiv _ _).trans yonedaEquiv)
    (((sheafificationAdjunction J (Type v)).homEquiv _ _).trans yonedaEquiv)
    (((sheafificationA

Depends on / 依赖: Adjunction, Adjunction.homEquiv, IsPullback, Square, Square.IsPullback.iff_of_equiv, all_goals, homEquiv, iff_of_equiv, sheafificationAdjunction, yonedaEquiv, yonedaEquiv_naturality
-/
lemma Sheaf.isPullback_square_op_map_yoneda_presheafToSheaf_yoneda_iff
    [HasWeakSheafify J (Type v)]
    (F : Sheaf J (Type v)) (sq : Square C) :
    (sq.op.map ((yoneda ⋙ presheafToSheaf J _).op ⋙ yoneda.obj F)).IsPullback ↔
      (sq.op.map F.obj).IsPullback := by
  refine Square.IsPullback.iff_of_equiv _ _
    (((sheafificationAdjunction J (Type v)).homEquiv _ _).trans yonedaEquiv)
    (((sheafificationAdjunction J (Type v)).homEquiv _ _).trans yonedaEquiv)
    (((sheafificationAdjunction J (Type v)).homEquiv _ _).trans yonedaEquiv)
    (((sheafificationAdjunction J (Type v)).homEquiv _ _).trans yonedaEquiv) ?_ ?_ ?_ ?_
  all_goals
    ext x
    simp [Adjunction.homEquiv, yonedaEquiv_naturality]

namespace GrothendieckTopology

variable (J)

/--
Definition of `MayerVietorisSquare` / `MayerVietorisSquare` 的定义

English:
structure MayerVietorisSquare
  parameters: [HasWeakSheafify J (Type v)]
  extends: Square C
  axioms and operations (2):
    - mono_f₁₃ : Mono toSquare.f₁₃  [default: by infer_instance]
    - isPushout : (toSquare.map (yoneda ⋙ presheafToSheaf J _)).IsPushout

中文:
结构 MayerVietorisSquare
  参数: [HasWeakSheafify J (类型v)]
  继承: Square C
  公理与运算 (2 个):
    - mono_f₁₃ : Mono toSquare.f₁₃  [默认: by infer_instance]
    - isPushout : (toSquare.map (yoneda ⋙ presheafToSheaf J _)).IsPushout

Depends on / 依赖: infer_instance
-/
structure MayerVietorisSquare [HasWeakSheafify J (Type v)] extends Square C where
  mono_f₁₃ : Mono toSquare.f₁₃ := by infer_instance
  /-- the square becomes a pushout square in the category of sheaves of types -/
  isPushout : (toSquare.map (yoneda ⋙ presheafToSheaf J _)).IsPushout

namespace MayerVietorisSquare

attribute [instance] mono_f₁₃

variable {J}

section

variable [HasWeakSheafify J (Type v)]

/-- Constructor for Mayer-Vietoris squares taking as an input
a square `sq` such that `sq.f₁₃` is a mono and that for every
sheaf of types `F`, the square `sq.op.map F.val` is a pullback square. -/
@[simps toSquare]
/--
Definition of `mk'` / `mk'` 的定义

English:
definition mk'
  signature: (sq : Square C) [Mono sq.f₁₃]
  body: sq
  isPushout := by
    rw [Square.isPushout_iff_op_map_yoneda_isPullback]
    intro F
    exact (F.isPullback_square_op_map_yoneda_presheafToSheaf_yoneda_iff sq).2 (H F)

中文:
定义 mk'
  签名: (sq : Square C) [Mono sq.f₁₃]
  定义体: sq
  isPushout := by
    rw [Square.isPushout_iff_op_map_yoneda_isPullback]
    intro F
    exact (F.isPullback_square_op_map_yoneda_presheafToSheaf_yoneda_iff sq).2 (H F)
-/
noncomputable def mk' (sq : Square C) [Mono sq.f₁₃]
    (H : forall (F : Sheaf J (Type v)), (sq.op.map F.obj).IsPullback) :
    J.MayerVietorisSquare where
  toSquare := sq
  isPushout := by
    rw [Square.isPushout_iff_op_map_yoneda_isPullback]
    intro F
    exact (F.isPullback_square_op_map_yoneda_presheafToSheaf_yoneda_iff sq).2 (H F)

set_option backward.isDefEq.respectTransparency false in
/-- Constructor for Mayer-Vietoris squares taking as an input
a pullback square `sq` such that `sq.f₂₄` and `sq.f₃₄` are two monomorphisms
which form a covering of `S.X₄`. -/
@[simps! toSquare]
/--
Definition of `mk_of_isPullback` / `mk_of_isPullback` 的定义

English:
definition mk_of_isPullback
  signature: (sq : Square C) [Mono sq.f₂₄] [Mono sq.f₃₄]
  body: have : Mono sq.f₁₃ := h₁.mono_f₁₃
  mk' sq (fun F => by
    apply Square.IsPullback.mk
    refine PullbackCone.IsLimit.mk _
      (fun s => F.2.amalgamateOfArrows _ h₂
        (fun j => WalkingPair.casesOn j s.fst s.snd)
        (fun W => by
          rintro (_ | _) (_ | _) a b fac
          · obtai

中文:
定义 mk_of_isPullback
  签名: (sq : Square C) [Mono sq.f₂₄] [Mono sq.f₃₄]
  定义体: have : Mono sq.f₁₃ := h₁.mono_f₁₃
  mk' sq (fun F => by
    apply Square.IsPullback.mk
    refine PullbackCone.IsLimit.mk _
      (fun s => F.2.amalgamateOfArrows _ h₂
        (fun j => WalkingPair.casesOn j s.fst s.snd)
        (fun W => by
          rintro (_ | _) (_ | _) a b fac
          · obtai

Depends on / 依赖: F.obj.map, IsLimit, IsPullback, PullbackCone, PullbackCone.IsLimit.lift, PullbackCone.IsLimit.mk, Square, Square.IsPullback.mk, WalkingPair, WalkingPair.casesOn, amalgamateOfArrows, cancel_mono, casesOn, condition, isLimit, s.condition, s.fst, s.snd, sq.f
-/
noncomputable def mk_of_isPullback (sq : Square C) [Mono sq.f₂₄] [Mono sq.f₃₄]
    (h₁ : sq.IsPullback) (h₂ : Sieve.ofTwoArrows sq.f₂₄ sq.f₃₄ in J sq.X₄) :
    J.MayerVietorisSquare :=
  have : Mono sq.f₁₃ := h₁.mono_f₁₃
  mk' sq (fun F => by
    apply Square.IsPullback.mk
    refine PullbackCone.IsLimit.mk _
      (fun s => F.2.amalgamateOfArrows _ h₂
        (fun j => WalkingPair.casesOn j s.fst s.snd)
        (fun W => by
          rintro (_ | _) (_ | _) a b fac
          · obtain rfl : a = b := by simpa only [← cancel_mono sq.f₂₄] using fac
            rfl
          · obtain ⟨φ, rfl, rfl⟩ := PullbackCone.IsLimit.lift' h₁.isLimit _ _ fac
            simpa using s.condition =≫ F.obj.map φ.op
          · obtain ⟨φ, rfl, rfl⟩ := PullbackCone.IsLimit.lift' h₁.isLimit _ _ fac.symm
            simpa using s.condition.symm =≫ F.obj.map φ.op
          · obtain rfl : a = b := by simpa only [← cancel_mono sq.f₃₄] using fac
            rfl)) (fun _ => ?_) (fun _ => ?_) (fun s m hm₁ hm₂ => ?_)
    · exact F.2.amalgamateOfArrows_map _ _ _ _ WalkingPair.left
    · exact F.2.amalgamateOfArrows_map _ _ _ _ WalkingPair.right
    · apply F.2.hom_ext_ofArrows _ h₂
      rintro (_ | _)
      · rw [F.2.amalgamateOfArrows_map _ _ _ _ WalkingPair.left]
        exact hm₁
      · rw [F.2.amalgamateOfArrows_map _ _ _ _ WalkingPair.right]
        exact hm₂)

variable (S : J.MayerVietorisSquare)

/--
lemma `isPushoutAddCommGrpFreeSheaf` / 引理 `isPushoutAddCommGrpFreeSheaf`

English:
lemma isPushoutAddCommGrpFreeSheaf
  given: [HasWeakSheafify J AddCommGrpCat.{v}]
  proof: (S.isPushout.map (Sheaf.composeAndSheafify J AddCommGrpCat.free)).of_iso
    ((Square.mapFunctor.mapIso
      (presheafToSheafCompComposeAndSheafifyIso J AddCommGrpCat.free)).app
        (S.map yoneda))

中文:
引理 isPushoutAddCommGrpFreeSheaf
  条件: [HasWeakSheafify J AddCommGrpCat.{v}]
  证明: (S.isPushout.map (Sheaf.composeAndSheafify J AddCommGrpCat.free)).of_iso
    ((Square.mapFunctor.mapIso
      (presheafToSheafCompComposeAndSheafifyIso J AddCommGrpCat.free)).app
        (S.map yoneda))

Depends on / 依赖: AddCommGrpCat, AddCommGrpCat.free, S.isPushout.map, S.map, Sheaf.composeAndSheafify, Square, Square.mapFunctor.mapIso, composeAndSheafify, isPushout, mapFunctor, mapIso, of_iso, presheafToSheafCompComposeAndSheafifyIso, yoneda
-/
lemma isPushoutAddCommGrpFreeSheaf [HasWeakSheafify J AddCommGrpCat.{v}] :
    (S.map (yoneda ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
      presheafToSheaf J _)).IsPushout :=
  (S.isPushout.map (Sheaf.composeAndSheafify J AddCommGrpCat.free)).of_iso
    ((Square.mapFunctor.mapIso
      (presheafToSheafCompComposeAndSheafifyIso J AddCommGrpCat.free)).app
        (S.map yoneda))

/--
Definition of `SheafCondition` / `SheafCondition` 的定义

English:
definition SheafCondition
  signature: {A : Type u'} [Category.{v'} A] (P : Cᵒᵖ ⥤ A)
  body: (S.toSquare.op.map P).IsPullback

中文:
定义 SheafCondition
  签名: {A : 类型u'} [Category.{v'} A] (P : Cᵒᵖ ⥤ A)
  定义体: (S.toSquare.op.map P).IsPullback

Depends on / 依赖: IsPullback, S.toSquare.op.map, toSquare
-/
def SheafCondition {A : Type u'} [Category.{v'} A] (P : Cᵒᵖ ⥤ A) : Prop :=
  (S.toSquare.op.map P).IsPullback

/--
lemma `sheafCondition_iff_comp_coyoneda` / 引理 `sheafCondition_iff_comp_coyoneda`

English:
lemma sheafCondition_iff_comp_coyoneda
  given: {A : Type u'} [Category.{v'} A] (P : Cᵒᵖ ⥤ A)
  proof: Square.isPullback_iff_map_coyoneda_isPullback (S.op.map P)

中文:
引理 sheafCondition_iff_comp_coyoneda
  条件: {A : 类型u'} [Category.{v'} A] (P : Cᵒᵖ ⥤ A)
  证明: Square.isPullback_iff_map_coyoneda_isPullback (S.op.map P)

Depends on / 依赖: S.op.map, Square, Square.isPullback_iff_map_coyoneda_isPullback, isPullback_iff_map_coyoneda_isPullback
-/
lemma sheafCondition_iff_comp_coyoneda {A : Type u'} [Category.{v'} A] (P : Cᵒᵖ ⥤ A) :
    S.SheafCondition P ↔ forall (X : Aᵒᵖ), S.SheafCondition (P ⋙ coyoneda.obj X) :=
  Square.isPullback_iff_map_coyoneda_isPullback (S.op.map P)

/--
Definition of `toPullbackObj` / `toPullbackObj` 的定义

English:
abbreviation toPullbackObj
  signature: (P : Cᵒᵖ ⥤ Type v')
  body: (S.toSquare.op.map P).pullbackCone.toPullbackObj

中文:
缩写 toPullbackObj
  签名: (P : Cᵒᵖ ⥤ 类型v')
  定义体: (S.toSquare.op.map P).pullbackCone.toPullbackObj

Depends on / 依赖: S.toSquare.op.map, pullbackCone, pullbackCone.toPullbackObj, toPullbackObj, toSquare
-/
abbrev toPullbackObj (P : Cᵒᵖ ⥤ Type v') :
    P.obj (op S.X₄) -> Types.PullbackObj (P.map S.f₁₂.op) (P.map S.f₁₃.op) :=
  (S.toSquare.op.map P).pullbackCone.toPullbackObj

/--
lemma `sheafCondition_iff_bijective_toPullbackObj` / 引理 `sheafCondition_iff_bijective_toPullbackObj`

English:
lemma sheafCondition_iff_bijective_toPullbackObj
  given: (P : Cᵒᵖ ⥤ Type v')
  proof: by
  have := (S.toSquare.op.map P).pullbackCone.isLimitEquivBijective
  exact ⟨fun h => this h.isLimit, fun h => Square.IsPullback.mk _ (this.symm h)⟩

中文:
引理 sheafCondition_iff_bijective_toPullbackObj
  条件: (P : Cᵒᵖ ⥤ 类型v')
  证明: by
  have := (S.toSquare.op.map P).pullbackCone.isLimitEquivBijective
  exact ⟨fun h => this h.isLimit, fun h => Square.IsPullback.mk _ (this.symm h)⟩

Depends on / 依赖: IsPullback, S.toSquare.op.map, Square, Square.IsPullback.mk, h.isLimit, isLimit, isLimitEquivBijective, pullbackCone, pullbackCone.isLimitEquivBijective, this.symm, toSquare
-/
lemma sheafCondition_iff_bijective_toPullbackObj (P : Cᵒᵖ ⥤ Type v') :
    S.SheafCondition P ↔ Function.Bijective (S.toPullbackObj P) := by
  have := (S.toSquare.op.map P).pullbackCone.isLimitEquivBijective
  exact ⟨fun h => this h.isLimit, fun h => Square.IsPullback.mk _ (this.symm h)⟩

namespace SheafCondition

variable {S}
variable {P : Cᵒᵖ ⥤ Type v'} (h : S.SheafCondition P)
include h

/--
lemma `bijective_toPullbackObj` / 引理 `bijective_toPullbackObj`

English:
lemma bijective_toPullbackObj
  statement: Function.Bijective (S.toPullbackObj P)
  proof: by
  rwa [← sheafCondition_iff_bijective_toPullbackObj]

中文:
引理 bijective_toPullbackObj
  结论: Function.Bijective (S.toPullbackObj P)
  证明: by
  rwa [← sheafCondition_iff_bijective_toPullbackObj]

Depends on / 依赖: sheafCondition_iff_bijective_toPullbackObj
-/
lemma bijective_toPullbackObj : Function.Bijective (S.toPullbackObj P) := by
  rwa [← sheafCondition_iff_bijective_toPullbackObj]

/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  statement: {x y : P.obj (op S.X₄)}
  proof: h.bijective_toPullbackObj.injective (by ext <;> assumption)

中文:
引理 ext
  结论: {x y : P.obj (op S.X₄)}
  证明: h.bijective_toPullbackObj.injective (by ext <;> assumption)

Depends on / 依赖: bijective_toPullbackObj, h.bijective_toPullbackObj.injective, injective
-/
lemma ext {x y : P.obj (op S.X₄)}
    (h₁ : P.map S.f₂₄.op x = P.map S.f₂₄.op y)
    (h₂ : P.map S.f₃₄.op x = P.map S.f₃₄.op y) : x = y :=
  h.bijective_toPullbackObj.injective (by ext <;> assumption)

variable (u : P.obj (op S.X₂)) (v : P.obj (op S.X₃))
  (huv : P.map S.f₁₂.op u = P.map S.f₁₃.op v)

/--
Definition of `glue` / `glue` 的定义

English:
definition glue
  signature: : P.obj (op S.X₄)
  body: (PullbackCone.IsLimit.equivPullbackObj h.isLimit).symm ⟨⟨u, v⟩, huv⟩

@[simp]

中文:
定义 glue
  签名: : P.obj (op S.X₄)
  定义体: (PullbackCone.IsLimit.equivPullbackObj h.isLimit).symm ⟨⟨u, v⟩, huv⟩

@[simp]

Depends on / 依赖: IsLimit, PullbackCone, PullbackCone.IsLimit.equivPullbackObj, equivPullbackObj, h.isLimit, isLimit
-/
noncomputable def glue : P.obj (op S.X₄) :=
  (PullbackCone.IsLimit.equivPullbackObj h.isLimit).symm ⟨⟨u, v⟩, huv⟩

@[simp]
/--
lemma `map_f₂₄_op_glue` / 引理 `map_f₂₄_op_glue`

English:
lemma map_f₂₄_op_glue
  statement: P.map S.f₂₄.op (h.glue u v huv) = u
  proof: PullbackCone.IsLimit.equivPullbackObj_symm_apply_fst h.isLimit _

@[simp]

中文:
引理 map_f₂₄_op_glue
  结论: P.map S.f₂₄.op (h.glue u v huv) = u
  证明: PullbackCone.IsLimit.equivPullbackObj_symm_apply_fst h.isLimit _

@[simp]

Depends on / 依赖: IsLimit, PullbackCone, PullbackCone.IsLimit.equivPullbackObj_symm_apply_fst, equivPullbackObj_symm_apply_fst, h.isLimit, isLimit
-/
lemma map_f₂₄_op_glue : P.map S.f₂₄.op (h.glue u v huv) = u :=
  PullbackCone.IsLimit.equivPullbackObj_symm_apply_fst h.isLimit _

@[simp]
/--
lemma `map_f₃₄_op_glue` / 引理 `map_f₃₄_op_glue`

English:
lemma map_f₃₄_op_glue
  statement: P.map S.f₃₄.op (h.glue u v huv) = v
  proof: PullbackCone.IsLimit.equivPullbackObj_symm_apply_snd h.isLimit _

中文:
引理 map_f₃₄_op_glue
  结论: P.map S.f₃₄.op (h.glue u v huv) = v
  证明: PullbackCone.IsLimit.equivPullbackObj_symm_apply_snd h.isLimit _

Depends on / 依赖: IsLimit, PullbackCone, PullbackCone.IsLimit.equivPullbackObj_symm_apply_snd, equivPullbackObj_symm_apply_snd, h.isLimit, isLimit
-/
lemma map_f₃₄_op_glue : P.map S.f₃₄.op (h.glue u v huv) = v :=
  PullbackCone.IsLimit.equivPullbackObj_symm_apply_snd h.isLimit _

end SheafCondition

/--
lemma `sheafCondition_of_sheaf` / 引理 `sheafCondition_of_sheaf`

English:
lemma sheafCondition_of_sheaf
  statement: {A : Type u'} [Category.{v} A]
  proof: by
  rw [sheafCondition_iff_comp_coyoneda]
  intro X
  exact (Sheaf.isPullback_square_op_map_yoneda_presheafToSheaf_yoneda_iff _ S.toSquare).1
    (S.isPushout.op.map
      (yoneda.obj ⟨_, (isSheaf_iff_isSheaf_of_type _ _).2 (F.property X.unop)⟩))

中文:
引理 sheafCondition_of_sheaf
  结论: {A : 类型u'} [Category.{v} A]
  证明: by
  rw [sheafCondition_iff_comp_coyoneda]
  intro X
  exact (Sheaf.isPullback_square_op_map_yoneda_presheafToSheaf_yoneda_iff _ S.toSquare).1
    (S.isPushout.op.map
      (yoneda.obj ⟨_, (isSheaf_iff_isSheaf_of_type _ _).2 (F.property X.unop)⟩))

Depends on / 依赖: F.property, S.isPushout.op.map, S.toSquare, Sheaf.isPullback_square_op_map_yoneda_presheafToSheaf_yoneda_iff, X.unop, isPullback_square_op_map_yoneda_presheafToSheaf_yoneda_iff, isPushout, isSheaf_iff_isSheaf_of_type, property, sheafCondition_iff_comp_coyoneda, toSquare, yoneda, yoneda.obj
-/
lemma sheafCondition_of_sheaf {A : Type u'} [Category.{v} A]
    (F : Sheaf J A) : S.SheafCondition F.obj := by
  rw [sheafCondition_iff_comp_coyoneda]
  intro X
  exact (Sheaf.isPullback_square_op_map_yoneda_presheafToSheaf_yoneda_iff _ S.toSquare).1
    (S.isPushout.op.map
      (yoneda.obj ⟨_, (isSheaf_iff_isSheaf_of_type _ _).2 (F.property X.unop)⟩))

end

variable [HasWeakSheafify J (Type v)] [HasSheafify J AddCommGrpCat.{v}]
  (S : J.MayerVietorisSquare)

/-- The short complex of abelian sheaves
`ℤ[S.X₁] ⟶ ℤ[S.X₂] ⊞ ℤ[S.X₃] ⟶ ℤ[S.X₄]`
where the left map is a difference and the right map a sum. -/
@[simps]
/--
Definition of `shortComplex` / `shortComplex` 的定义

English:
definition shortComplex
  signature: :
  body: (presheafToSheaf J _).obj (yoneda.obj S.X₁ ⋙ AddCommGrpCat.free)
  X₂ := (presheafToSheaf J _).obj (yoneda.obj S.X₂ ⋙ AddCommGrpCat.free) ⊞
    (presheafToSheaf J _).obj (yoneda.obj S.X₃ ⋙ AddCommGrpCat.free)
  X₃ := (presheafToSheaf J _).obj (yoneda.obj S.X₄ ⋙ AddCommGrpCat.free)
  f :=
    biprod.

中文:
定义 shortComplex
  签名: :
  定义体: (presheafToSheaf J _).obj (yoneda.obj S.X₁ ⋙ AddCommGrpCat.free)
  X₂ := (presheafToSheaf J _).obj (yoneda.obj S.X₂ ⋙ AddCommGrpCat.free) ⊞
    (presheafToSheaf J _).obj (yoneda.obj S.X₃ ⋙ AddCommGrpCat.free)
  X₃ := (presheafToSheaf J _).obj (yoneda.obj S.X₄ ⋙ AddCommGrpCat.free)
  f :=
    biprod.

Depends on / 依赖: AddCommGrpCat, AddCommGrpCat.free, presheafToSheaf, yoneda, yoneda.obj
-/
noncomputable def shortComplex :
    ShortComplex (Sheaf J AddCommGrpCat.{v}) where
  X₁ := (presheafToSheaf J _).obj (yoneda.obj S.X₁ ⋙ AddCommGrpCat.free)
  X₂ := (presheafToSheaf J _).obj (yoneda.obj S.X₂ ⋙ AddCommGrpCat.free) ⊞
    (presheafToSheaf J _).obj (yoneda.obj S.X₃ ⋙ AddCommGrpCat.free)
  X₃ := (presheafToSheaf J _).obj (yoneda.obj S.X₄ ⋙ AddCommGrpCat.free)
  f :=
    biprod.lift
      ((presheafToSheaf J _).map (Functor.whiskerRight (yoneda.map S.f₁₂) _))
      (-(presheafToSheaf J _).map (Functor.whiskerRight (yoneda.map S.f₁₃) _))
  g :=
    biprod.desc
      ((presheafToSheaf J _).map (Functor.whiskerRight (yoneda.map S.f₂₄) _))
      ((presheafToSheaf J _).map (Functor.whiskerRight (yoneda.map S.f₃₄) _))
  zero := (S.map (yoneda ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
      presheafToSheaf J _)).cokernelCofork.condition

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mono S.shortComplex.f
  body: by
  have : Mono (S.shortComplex.f ≫ biprod.snd) := by
    dsimp
    simp only [biprod.lift_snd]
    infer_instance
  exact mono_of_mono _ biprod.snd

中文:
实例 :
  签名: Mono S.shortComplex.f
  定义体: by
  have : Mono (S.shortComplex.f ≫ biprod.snd) := by
    dsimp
    simp only [biprod.lift_snd]
    infer_instance
  exact mono_of_mono _ biprod.snd

Depends on / 依赖: S.shortComplex.f, biprod, biprod.lift_snd, biprod.snd, infer_instance, lift_snd, mono_of_mono, shortComplex
-/
instance : Mono S.shortComplex.f := by
  have : Mono (S.shortComplex.f ≫ biprod.snd) := by
    dsimp
    simp only [biprod.lift_snd]
    infer_instance
  exact mono_of_mono _ biprod.snd

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Epi S.shortComplex.g
  body: (S.shortComplex.exact_and_epi_g_iff_g_is_cokernel.2
    ⟨S.isPushoutAddCommGrpFreeSheaf.isColimitCokernelCofork⟩).2

中文:
实例 :
  签名: Epi S.shortComplex.g
  定义体: (S.shortComplex.exact_and_epi_g_iff_g_is_cokernel.2
    ⟨S.isPushoutAddCommGrpFreeSheaf.isColimitCokernelCofork⟩).2

Depends on / 依赖: S.isPushoutAddCommGrpFreeSheaf.isColimitCokernelCofork, S.shortComplex.exact_and_epi_g_iff_g_is_cokernel, exact_and_epi_g_iff_g_is_cokernel, isColimitCokernelCofork, isPushoutAddCommGrpFreeSheaf, shortComplex
-/
instance : Epi S.shortComplex.g :=
  (S.shortComplex.exact_and_epi_g_iff_g_is_cokernel.2
    ⟨S.isPushoutAddCommGrpFreeSheaf.isColimitCokernelCofork⟩).2

/--
lemma `shortComplex_exact` / 引理 `shortComplex_exact`

English:
lemma shortComplex_exact
  statement: S.shortComplex.Exact
  proof: ShortComplex.exact_of_g_is_cokernel _
    S.isPushoutAddCommGrpFreeSheaf.isColimitCokernelCofork

中文:
引理 shortComplex_exact
  结论: S.shortComplex.Exact
  证明: ShortComplex.exact_of_g_is_cokernel _
    S.isPushoutAddCommGrpFreeSheaf.isColimitCokernelCofork

Depends on / 依赖: S.isPushoutAddCommGrpFreeSheaf.isColimitCokernelCofork, ShortComplex, ShortComplex.exact_of_g_is_cokernel, exact_of_g_is_cokernel, isColimitCokernelCofork, isPushoutAddCommGrpFreeSheaf
-/
lemma shortComplex_exact : S.shortComplex.Exact :=
  ShortComplex.exact_of_g_is_cokernel _
    S.isPushoutAddCommGrpFreeSheaf.isColimitCokernelCofork

/--
lemma `shortComplex_shortExact` / 引理 `shortComplex_shortExact`

English:
lemma shortComplex_shortExact
  statement: S.shortComplex.ShortExact where
  proof: S.shortComplex_exact

中文:
引理 shortComplex_shortExact
  结论: S.shortComplex.ShortExact where
  证明: S.shortComplex_exact

Depends on / 依赖: S.shortComplex_exact, shortComplex_exact
-/
lemma shortComplex_shortExact : S.shortComplex.ShortExact where
  exact := S.shortComplex_exact

end MayerVietorisSquare

end GrothendieckTopology

end CategoryTheory
