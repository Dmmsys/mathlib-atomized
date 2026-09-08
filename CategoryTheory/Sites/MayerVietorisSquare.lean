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
/-
**CategoryTheory.Sheaf.isPullback_square_op_map_yoneda_presheafToSheaf_yoneda_if
f** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Sheaf`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheo
ry.GrothendieckTopology C}   [inst_1 : CategoryTheory.HasWeakSheafify J (Type v)
] (F : CategoryTheory.Sheaf J (Type v))   (sq : CategoryTheory.Square C),   (sq.
op.map         ((CategoryTheory.yoneda.comp (CategoryTheory.presheafToSheaf J (T
ype v))).op.comp           (CategoryTheory.yoneda.obj F))).IsPullback ↔     (sq.
op.map F.obj).IsPullback
参数：Type v；F : CategoryTheory.Sheaf J (Type v)；sq : CategoryTheory.Square C；sq.op
.map         ((CategoryTheory.yoneda.comp (CategoryTheory.presheafToSheaf J (Typ
e v))).op.comp           (CategoryTheory.yoneda.obj F))；sq.op.map F.obj。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Square.IsPullback.iff_of_equiv`：∀ (sq₁ : CategoryTheory.S
quare (Type v)) (sq₂ : CategoryTheory.Square (Type u)) (e₁ : sq₁.X₁ ≃ sq₂.X₁)   
(e₂ : sq₁.X₂ ≃ sq₂.X₂) (e₃ : sq₁.X₃…
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.yonedaEquiv_naturality`：yonedaEquiv_naturality {X Y : C} 
{F : Cᵒᵖ ⥤ Type v₁} (f : yoneda.obj X ⟶ F) (g : Y ⟶ X) : F.map g.op (yonedaEquiv
 f) = yonedaEquiv (yoneda.m…
· 使用定理 `CategoryTheory.toSheafify_naturality_assoc`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] (J : CategoryTheory.GrothendieckTopology C) {D :
 Type u_1}   [inst_1 : CategoryT…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
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

/-- A Mayer-Vietoris square in a category `C` equipped with a Grothendieck
topology consists of a commutative square `f₁₂ ≫ f₂₄ = f₁₃ ≫ f₃₄` in `C`
such that `f₁₃` is a monomorphism and that the square becomes a
pushout square in the category of sheaves of sets. -/
/-
**CategoryTheory.GrothendieckTopology.MayerVietorisSquare** 是 Mathlib 中的一个结构，位于命
名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：MayerVietorisSquare [HasWeakSheafify J (Type v)] extends Square C where mo
no_f₁₃ : Mono toSquare.f₁₃
参数：Type v。
继承自：Square C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Mayer-Vietoris square in a category `C` equipped with a Grothendieck
topology consists of a commutative square `f₁₂ ≫ f₂₄ = f₁₃ ≫ f₃₄` in `C`
such that `f₁₃` is a monomorphism and that the square becomes a
pushout square in the category of sheaves of sets.
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
/-
**CategoryTheory.GrothendieckTopology.MayerVietorisSquare.mk'** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.GrothendieckTopology.MayerVietorisSquare`。
形式化陈述：mk' (sq : Square C) [Mono sq.f₁₃] (H : forall (F : Sheaf J (Type v)), (sq.
op.map F.obj).IsPullback) : J.MayerVietorisSquare where toSquare
参数：sq : Square C；H : forall (F : Sheaf J (Type v)), (sq.op.map F.obj).IsPullback
。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for Mayer-Vietoris squares taking as an input
a square `sq` such that `sq.f₁₃` is a mono and that for every
sheaf of types `F`, the square `sq.op.map F.val` is a pullback square.
-/
noncomputable def mk' (sq : Square C) [Mono sq.f₁₃]
    (H : ∀ (F : Sheaf J (Type v)), (sq.op.map F.obj).IsPullback) :
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
/-
**CategoryTheory.GrothendieckTopology.MayerVietorisSquare.mk_of_isPullback** 是 M
athlib 中的一个定义，位于命名空间 `CategoryTheory.GrothendieckTopology.MayerVietorisSquare`。
形式化陈述：mk_of_isPullback (sq : Square C) [Mono sq.f₂₄] [Mono sq.f₃₄] (h₁ : sq.IsPu
llback) (h₂ : Sieve.ofTwoArrows sq.f₂₄ sq.f₃₄ in J sq.X₄) : J.MayerVietorisSquar
e
参数：sq : Square C；h₁ : sq.IsPullback；h₂ : Sieve.ofTwoArrows sq.f₂₄ sq.f₃₄ in J sq
.X₄。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Square.IsPullback.mono_f₁₃`：mono_f₁₃ [Mono sq.f₂₄] : Mono
 sq.f₁₃

--- 原说明 ---
Constructor for Mayer-Vietoris squares taking as an input
a pullback square `sq` such that `sq.f₂₄` and `sq.f₃₄` are two monomorphisms
which form a covering of `S.X₄`.
-/
noncomputable def mk_of_isPullback (sq : Square C) [Mono sq.f₂₄] [Mono sq.f₃₄]
    (h₁ : sq.IsPullback) (h₂ : Sieve.ofTwoArrows sq.f₂₄ sq.f₃₄ ∈ J sq.X₄) :
    J.MayerVietorisSquare :=
  have : Mono sq.f₁₃ := h₁.mono_f₁₃
  mk' sq (fun F ↦ by
    apply Square.IsPullback.mk
    refine PullbackCone.IsLimit.mk _
      (fun s ↦ F.2.amalgamateOfArrows _ h₂
        (fun j ↦ WalkingPair.casesOn j s.fst s.snd)
        (fun W ↦ by
          rintro (_ | _) (_ | _) a b fac
          · obtain rfl : a = b := by simpa only [← cancel_mono sq.f₂₄] using fac
            rfl
          · obtain ⟨φ, rfl, rfl⟩ := PullbackCone.IsLimit.lift' h₁.isLimit _ _ fac
            simpa using s.condition =≫ F.obj.map φ.op
          · obtain ⟨φ, rfl, rfl⟩ := PullbackCone.IsLimit.lift' h₁.isLimit _ _ fac.symm
            simpa using s.condition.symm =≫ F.obj.map φ.op
          · obtain rfl : a = b := by simpa only [← cancel_mono sq.f₃₄] using fac
            rfl)) (fun _ ↦ ?_) (fun _ ↦ ?_) (fun s m hm₁ hm₂ ↦ ?_)
    · exact F.2.amalgamateOfArrows_map _ _ _ _ WalkingPair.left
    · exact F.2.amalgamateOfArrows_map _ _ _ _ WalkingPair.right
    · apply F.2.hom_ext_ofArrows _ h₂
      rintro (_ | _)
      · rw [F.2.amalgamateOfArrows_map _ _ _ _ WalkingPair.left]
        exact hm₁
      · rw [F.2.amalgamateOfArrows_map _ _ _ _ WalkingPair.right]
        exact hm₂)

variable (S : J.MayerVietorisSquare)
/-
**CategoryTheory.GrothendieckTopology.MayerVietorisSquare.isPushoutAddCommGrpFre
eSheaf** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology.MayerVieto
risSquare`。
形式化陈述：isPushoutAddCommGrpFreeSheaf [HasWeakSheafify J AddCommGrpCat.{v}] : (S.ma
p (yoneda ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙ presheafToS
heaf J _)).IsPushout
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Square.IsPushout.of_iso`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {sq₁ sq₂ : CategoryTheory.Square C},   sq₁.IsPushout → 
∀ (e : sq₁ ≅ sq₂), sq₂.IsPus…
· 使用定理 `CategoryTheory.Square.IsPushout.map`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {D : Type u'} [inst_1 : CategoryTheory.Category.{v', u'} D
]   {sq : CategoryTheory.…
· 使用定理 `CategoryTheory.GrothendieckTopology.MayerVietorisSquare.isPushout`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheory.Grothend
ieckTopology C}   [inst_1 : CategoryTheory.HasWeakSheaf…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Functor.instPreservesColimitsOfShapeOfIsLeftAdjoint`：∀ {J
 : Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1,
 u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Sheaf.instIsLeftAdjointComposeAndSheafify`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] (J : CategoryTheory.GrothendieckTo
pology C) {D : Type u₂}   [inst_1 : CategoryTh…
· 使用定理 `AddCommGrpCat.instIsLeftAdjointFree`：AddCommGrpCat.free.IsLeftAdjoint
· 使用定理 `CategoryTheory.Sheaf.instPreservesSheafificationOfIsLeftAdjoint`：∀ {C : 
Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] (J : CategoryTheory.Grothen
dieckTopology C) {D : Type u₂}   [inst_1 : CategoryTh…
-/
lemma isPushoutAddCommGrpFreeSheaf [HasWeakSheafify J AddCommGrpCat.{v}] :
    (S.map (yoneda ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
      presheafToSheaf J _)).IsPushout :=
  (S.isPushout.map (Sheaf.composeAndSheafify J AddCommGrpCat.free)).of_iso
    ((Square.mapFunctor.mapIso
      (presheafToSheafCompComposeAndSheafifyIso J AddCommGrpCat.free)).app
        (S.map yoneda))

/-- The condition that a Mayer-Vietoris square becomes a pullback square
when we evaluate a presheaf on it. -/
/-
**CategoryTheory.GrothendieckTopology.MayerVietorisSquare.SheafCondition** 是 Mat
hlib 中的一个定义，位于命名空间 `CategoryTheory.GrothendieckTopology.MayerVietorisSquare`。
形式化陈述：SheafCondition {A : Type u'} [Category.{v'} A] (P : Cᵒᵖ ⥤ A) : Prop
参数：P : Cᵒᵖ ⥤ A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The condition that a Mayer-Vietoris square becomes a pullback square
when we evaluate a presheaf on it.
-/
def SheafCondition {A : Type u'} [Category.{v'} A] (P : Cᵒᵖ ⥤ A) : Prop :=
  (S.toSquare.op.map P).IsPullback
/-
**CategoryTheory.GrothendieckTopology.MayerVietorisSquare.sheafCondition_iff_com
p_coyoneda** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology.MayerV
ietorisSquare`。
形式化陈述：sheafCondition_iff_comp_coyoneda {A : Type u'} [Category.{v'} A] (P : Cᵒᵖ 
⥤ A) : S.SheafCondition P ↔ forall (X : Aᵒᵖ), S.SheafCondition (P ⋙ coyoneda.obj
 X)
参数：P : Cᵒᵖ ⥤ A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Square.isPullback_iff_map_coyoneda_isPullback`：isPullback
_iff_map_coyoneda_isPullback : sq.IsPullback ↔ forall (X : Cᵒᵖ), (sq.map (coyone
da.obj X)).IsPullback
-/
lemma sheafCondition_iff_comp_coyoneda {A : Type u'} [Category.{v'} A] (P : Cᵒᵖ ⥤ A) :
    S.SheafCondition P ↔ ∀ (X : Aᵒᵖ), S.SheafCondition (P ⋙ coyoneda.obj X) :=
  Square.isPullback_iff_map_coyoneda_isPullback (S.op.map P)

/-- Given a Mayer-Vietoris square `S` and a presheaf of types, this is the
map from `P.obj (op S.X₄)` to the explicit fibre product of
`P.map S.f₁₂.op` and `P.map S.f₁₃.op`. -/
/-
**CategoryTheory.GrothendieckTopology.MayerVietorisSquare.toPullbackObj** 是 Math
lib 中的一个缩写定义，位于命名空间 `CategoryTheory.GrothendieckTopology.MayerVietorisSquare`。
形式化陈述：toPullbackObj (P : Cᵒᵖ ⥤ Type v') : P.obj (op S.X₄) -> Types.PullbackObj (
P.map S.f₁₂.op) (P.map S.f₁₃.op)
参数：P : Cᵒᵖ ⥤ Type v'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a Mayer-Vietoris square `S` and a presheaf of types, this is the
map from `P.obj (op S.X₄)` to the explicit fibre product of
`P.map S.f₁₂.op` and `P.map S.f₁₃.op`.
-/
abbrev toPullbackObj (P : Cᵒᵖ ⥤ Type v') :
    P.obj (op S.X₄) → Types.PullbackObj (P.map S.f₁₂.op) (P.map S.f₁₃.op) :=
  (S.toSquare.op.map P).pullbackCone.toPullbackObj
/-
**CategoryTheory.GrothendieckTopology.MayerVietorisSquare.sheafCondition_iff_bij
ective_toPullbackObj** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopol
ogy.MayerVietorisSquare`。
形式化陈述：sheafCondition_iff_bijective_toPullbackObj (P : Cᵒᵖ ⥤ Type v') : S.SheafCo
ndition P ↔ Function.Bijective (S.toPullbackObj P)
参数：P : Cᵒᵖ ⥤ Type v'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Square.IsPullback.mk`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] (sq : CategoryTheory.Square C)   (h : CategoryTheory.Limit
s.IsLimit sq.pullbackCone…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma sheafCondition_iff_bijective_toPullbackObj (P : Cᵒᵖ ⥤ Type v') :
    S.SheafCondition P ↔ Function.Bijective (S.toPullbackObj P) := by
  have := (S.toSquare.op.map P).pullbackCone.isLimitEquivBijective
  exact ⟨fun h ↦ this h.isLimit, fun h ↦ Square.IsPullback.mk _ (this.symm h)⟩

namespace SheafCondition

variable {S}
variable {P : Cᵒᵖ ⥤ Type v'} (h : S.SheafCondition P)
include h

/-
**CategoryTheory.GrothendieckTopology.MayerVietorisSquare.SheafCondition.bijecti
ve_toPullbackObj** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology.
MayerVietorisSquare.SheafCondition`。
形式化陈述：bijective_toPullbackObj : Function.Bijective (S.toPullbackObj P)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.GrothendieckTopology.MayerVietorisSquare.sheafCondition_i
ff_bijective_toPullbackObj`：sheafCondition_iff_bijective_toPullbackObj (P : Cᵒᵖ 
⥤ Type v') : S.SheafCondition P ↔ Function.Bijective (S.toPullbackObj P)
-/
lemma bijective_toPullbackObj : Function.Bijective (S.toPullbackObj P) := by
  rwa [← sheafCondition_iff_bijective_toPullbackObj]
/-
**CategoryTheory.GrothendieckTopology.MayerVietorisSquare.SheafCondition.ext** 是
 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology.MayerVietorisSquare.
SheafCondition`。
形式化陈述：ext {x y : P.obj (op S.X₄)} (h₁ : P.map S.f₂₄.op x = P.map S.f₂₄.op y) (h₂
 : P.map S.f₃₄.op x = P.map S.f₃₄.op y) : x = y
参数：op S.X₄；h₁ : P.map S.f₂₄.op x = P.map S.f₂₄.op y；h₂ : P.map S.f₃₄.op x = P.ma
p S.f₃₄.op y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用引理 `CategoryTheory.GrothendieckTopology.MayerVietorisSquare.SheafCondition.b
ijective_toPullbackObj`：bijective_toPullbackObj : Function.Bijective (S.toPullba
ckObj P)
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
-/
lemma ext {x y : P.obj (op S.X₄)}
    (h₁ : P.map S.f₂₄.op x = P.map S.f₂₄.op y)
    (h₂ : P.map S.f₃₄.op x = P.map S.f₃₄.op y) : x = y :=
  h.bijective_toPullbackObj.injective (by ext <;> assumption)

variable (u : P.obj (op S.X₂)) (v : P.obj (op S.X₃))
  (huv : P.map S.f₁₂.op u = P.map S.f₁₃.op v)

/-- If `S` is a Mayer-Vietoris square, and `P` is a presheaf
which satisfies the sheaf condition with respect to `S`, then
elements of `P` over `S.X₂` and `S.X₃` can be glued if the
coincide over `S.X₁`. -/
/-
**CategoryTheory.GrothendieckTopology.MayerVietorisSquare.SheafCondition.glue** 
是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.GrothendieckTopology.MayerVietorisSquare
.SheafCondition`。
形式化陈述：glue : P.obj (op S.X₄)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If `S` is a Mayer-Vietoris square, and `P` is a presheaf
which satisfies the sheaf condition with respect to `S`, then
elements of `P` over `S.X₂` and `S.X₃` can be glued if the
coincide over `S.X₁`.
-/
noncomputable def glue : P.obj (op S.X₄) :=
  (PullbackCone.IsLimit.equivPullbackObj h.isLimit).symm ⟨⟨u, v⟩, huv⟩

@[simp]
/-
**CategoryTheory.GrothendieckTopology.MayerVietorisSquare.SheafCondition.map_f**
 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology.MayerVietorisSquar
e.SheafCondition`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_f₂₄_op_glue : P.map S.f₂₄.op (h.glue u v huv) = u :=
  PullbackCone.IsLimit.equivPullbackObj_symm_apply_fst h.isLimit _

@[simp]
/-
**CategoryTheory.GrothendieckTopology.MayerVietorisSquare.SheafCondition.map_f**
 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology.MayerVietorisSquar
e.SheafCondition`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_f₃₄_op_glue : P.map S.f₃₄.op (h.glue u v huv) = v :=
  PullbackCone.IsLimit.equivPullbackObj_symm_apply_snd h.isLimit _

end SheafCondition

/-
**CategoryTheory.GrothendieckTopology.MayerVietorisSquare.sheafCondition_of_shea
f** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology.MayerVietorisSq
uare`。
形式化陈述：sheafCondition_of_sheaf {A : Type u'} [Category.{v} A] (F : Sheaf J A) : S
.SheafCondition F.obj
参数：F : Sheaf J A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.GrothendieckTopology.MayerVietorisSquare.sheafCondition_i
ff_comp_coyoneda`：sheafCondition_iff_comp_coyoneda {A : Type u'} [Category.{v'} 
A] (P : Cᵒᵖ ⥤ A) : S.SheafCondition P ↔ forall (X : Aᵒᵖ), S.SheafCondition (P …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.isSheaf_iff_isSheaf_of_type`：isSheaf_iff_isSheaf_of_type 
(P : Cᵒᵖ ⥤ Type w) : Presheaf.IsSheaf J P ↔ Presieve.IsSheaf J P
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.property`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C}  
 (self : P.FullSubcategory), P self.obj
· 使用定理 `CategoryTheory.Sheaf.isPullback_square_op_map_yoneda_presheafToSheaf_yon
eda_iff`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : CategoryT
heory.GrothendieckTopology C}   [inst_1 : CategoryTheory.HasWeakSheaf…
· 使用定理 `CategoryTheory.Square.IsPullback.map`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {D : Type u'} [inst_1 : CategoryTheory.Category.{v', u'} 
D]   {sq : CategoryTheory.…
· 使用定理 `CategoryTheory.Square.IsPushout.op`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {sq : CategoryTheory.Square C}, sq.IsPushout → sq.op.IsPull
back
· 使用定理 `CategoryTheory.GrothendieckTopology.MayerVietorisSquare.isPushout`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheory.Grothend
ieckTopology C}   [inst_1 : CategoryTheory.HasWeakSheaf…
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
/-
**CategoryTheory.GrothendieckTopology.MayerVietorisSquare.shortComplex** 是 Mathl
ib 中的一个定义，位于命名空间 `CategoryTheory.GrothendieckTopology.MayerVietorisSquare`。
形式化陈述：shortComplex : ShortComplex (Sheaf J AddCommGrpCat.{v}) where X₁
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instHasWeakSheafifyOfHasSheafify`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] (J : CategoryTheory.GrothendieckTopology C)
 (A : Type u₂)   [inst_1 : CategoryTh…

--- 原说明 ---
The short complex of abelian sheaves
`ℤ[S.X₁] ⟶ ℤ[S.X₂] ⊞ ℤ[S.X₃] ⟶ ℤ[S.X₄]`
where the left map is a difference and the right map a sum.
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
/-
**CategoryTheory.GrothendieckTopology.MayerVietorisSquare.** 是 Mathlib 中的一个实例，位于
命名空间 `CategoryTheory.GrothendieckTopology.MayerVietorisSquare`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mono S.shortComplex.f := by
  have : Mono (S.shortComplex.f ≫ biprod.snd) := by
    dsimp
    simp only [biprod.lift_snd]
    infer_instance
  exact mono_of_mono _ biprod.snd
/-
**CategoryTheory.GrothendieckTopology.MayerVietorisSquare.** 是 Mathlib 中的一个实例，位于
命名空间 `CategoryTheory.GrothendieckTopology.MayerVietorisSquare`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Epi S.shortComplex.g :=
  (S.shortComplex.exact_and_epi_g_iff_g_is_cokernel.2
    ⟨S.isPushoutAddCommGrpFreeSheaf.isColimitCokernelCofork⟩).2
/-
**CategoryTheory.GrothendieckTopology.MayerVietorisSquare.shortComplex_exact** 是
 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology.MayerVietorisSquare`
。
形式化陈述：shortComplex_exact : S.shortComplex.Exact
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.exact_of_g_is_cokernel`：exact_of_g_is_cokern
el (hS : IsColimit (CokernelCofork.ofπ S.g S.zero)) [S.HasHomology] : S.Exact
· 使用定理 `CategoryTheory.instHasWeakSheafifyOfHasSheafify`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] (J : CategoryTheory.GrothendieckTopology C)
 (A : Type u₂)   [inst_1 : CategoryTh…
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproducts.has_binary_biproduct`：∀ {C : T
ype uC} {inst : CategoryTheory.Category.{uC', uC} C} {inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C}   [self : CategoryTheory.Li…
· 使用定理 `CategoryTheory.Abelian.hasBinaryBiproducts`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   CategoryTheo
ry.Limits.HasBinaryBiproducts C
· 使用引理 `CategoryTheory.GrothendieckTopology.MayerVietorisSquare.isPushoutAddComm
GrpFreeSheaf`：isPushoutAddCommGrpFreeSheaf [HasWeakSheafify J AddCommGrpCat.{v}]
 : (S.map (yoneda ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free…
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
-/
lemma shortComplex_exact : S.shortComplex.Exact :=
  ShortComplex.exact_of_g_is_cokernel _
    S.isPushoutAddCommGrpFreeSheaf.isColimitCokernelCofork
/-
**CategoryTheory.GrothendieckTopology.MayerVietorisSquare.shortComplex_shortExac
t** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology.MayerVietorisSq
uare`。
形式化陈述：shortComplex_shortExact : S.shortComplex.ShortExact where exact
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.GrothendieckTopology.MayerVietorisSquare.shortComplex_exa
ct`：shortComplex_exact : S.shortComplex.Exact
· 使用定理 `CategoryTheory.GrothendieckTopology.MayerVietorisSquare.instMonoSheafAdd
CommGrpCatFShortComplex`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C
] {J : CategoryTheory.GrothendieckTopology C}   [inst_1 : CategoryTheory.HasWeak
Sheaf…
· 使用定理 `CategoryTheory.GrothendieckTopology.MayerVietorisSquare.instEpiSheafAddC
ommGrpCatGShortComplex`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C]
 {J : CategoryTheory.GrothendieckTopology C}   [inst_1 : CategoryTheory.HasWeakS
heaf…
-/
lemma shortComplex_shortExact : S.shortComplex.ShortExact where
  exact := S.shortComplex_exact

end MayerVietorisSquare

end GrothendieckTopology

end CategoryTheory

