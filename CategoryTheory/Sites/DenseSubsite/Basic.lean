/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Joël Riou
-/
module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Sites.LocallyFullyFaithful

/-!
# Dense subsites

We define `IsCoverDense` functors into sites as functors such that there exists a covering sieve
that factors through images of the functor for each object in `D`.

## Main results

- `CategoryTheory.Functor.IsCoverDense.Types.presheafHom`: If `G : C ⥤ (D, K)` is locally-full
  and cover-dense, then given any presheaf `ℱ` and sheaf `ℱ'` on `D`,
  and a morphism `α : G ⋙ ℱ ⟶ G ⋙ ℱ'`, we may glue them together to obtain
  a morphism of presheaves `ℱ ⟶ ℱ'`.
- `CategoryTheory.Functor.IsCoverDense.sheafIso`: If `ℱ` above is a sheaf and `α` is an iso,
  then the result is also an iso.
- `CategoryTheory.Functor.IsCoverDense.iso_of_restrict_iso`: If `G : C ⥤ (D, K)` is locally-full
  and cover-dense, then given any sheaves `ℱ, ℱ'` on `D`, and a morphism `α : ℱ ⟶ ℱ'`,
  then `α` is an iso if `G ⋙ ℱ ⟶ G ⋙ ℱ'` is iso.
- `CategoryTheory.Functor.IsDenseSubsite`:
  The functor `G : C ⥤ D` exhibits `(C, J)` as a dense subsite of `(D, K)` if `G` is cover-dense,
  locally fully-faithful, and `S` is a cover of `C` iff the image of `S` in `D` is a cover.
- `CategoryTheory.Functor.IsDenseSubsite.sheafEquiv`: the equivalence of
  categories `Sheaf J A ≌ Sheaf K A` when `(C, J)` is a dense subsite of `(D, K)` and
  the pushforward functor `Sheaf K A ⥤ Sheaf J A` is an equivalence, which we show
  in two situations:
  * the sites are small and `A` has suitable limits (see the file
    `Mathlib/CategoryTheory/Sites/DenseSubsite/SheafEquiv.lean`).
  * the category `A` has limits of size `w` and `G` is `1`-hypercover cover dense
    relatively to the universe `w` (see the file
    `Mathlib/CategoryTheory/Sites/DenseSubsite/OneHypercoverDense.lean`).

## References

* [Elephant]: *Sketches of an Elephant*, ℱ. T. Johnstone: C2.2.
* https://ncatlab.org/nlab/show/dense+sub-site
* https://ncatlab.org/nlab/show/comparison+lemma

-/

@[expose] public section

universe w v u

namespace CategoryTheory

variable {C : Type*} [Category* C] {D : Type*} [Category* D] {E : Type*} [Category* E]
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable {L : GrothendieckTopology E}

/--
Definition of `Presieve.CoverByImageStructure` / `Presieve.CoverByImageStructure` 的定义

English:
structure Presieve.CoverByImageStructure
  parameters: (G : C ⥤ D) {V U : D} (f : V ⟶ U)
  axioms and operations (4):
    - obj : C
    - lift : V ⟶ G.obj obj
    - map : G.obj obj ⟶ U
    - fac : lift ≫ map = f  [default: by cat_disch]

中文:
结构 Presieve.余verByImageStructure
  参数: (G : C ⥤ D) {V U : D} (f : V ⟶ U)
  公理与运算 (4 个):
    - obj : C
    - lift : V ⟶ G.obj obj
    - map : G.obj obj ⟶ U
    - fac : lift ≫ map = f  [默认: by cat_disch]

Depends on / 依赖: CoverByImageStructure, Presieve, Presieve.CoverByImageStructure.fac, Presieve.CoverByImageStructure.lift, Presieve.CoverByImageStructure.map, Presieve.CoverByImageStructure.obj, attribute, cat_disch, docBlame, nolint
-/
structure Presieve.CoverByImageStructure (G : C ⥤ D) {V U : D} (f : V ⟶ U) where
  obj : C
  lift : V ⟶ G.obj obj
  map : G.obj obj ⟶ U
  fac : lift ≫ map = f := by cat_disch
attribute [nolint docBlame] Presieve.CoverByImageStructure.obj Presieve.CoverByImageStructure.lift
  Presieve.CoverByImageStructure.map Presieve.CoverByImageStructure.fac

attribute [reassoc (attr := simp)] Presieve.CoverByImageStructure.fac

/--
Definition of `Presieve.coverByImage` / `Presieve.coverByImage` 的定义

English:
definition Presieve.coverByImage
  signature: (G : C ⥤ D) (U : D)
  body: fun _ f =>
  Nonempty (Presieve.CoverByImageStructure G f)

中文:
定义 Presieve.coverByImage
  签名: (G : C ⥤ D) (U : D)
  定义体: fun _ f =>
  Nonempty (Presieve.CoverByImageStructure G f)
-/
def Presieve.coverByImage (G : C ⥤ D) (U : D) : Presieve U := fun _ f =>
  Nonempty (Presieve.CoverByImageStructure G f)

/--
Definition of `Sieve.coverByImage` / `Sieve.coverByImage` 的定义

English:
definition Sieve.coverByImage
  signature: (G : C ⥤ D) (U : D)
  body: ⟨Presieve.coverByImage G U, fun ⟨⟨Z, f₁, f₂, (e : _ = _)⟩⟩ g =>
    ⟨⟨Z, g ≫ f₁, f₂, show (g ≫ f₁) ≫ f₂ = g ≫ _ by rw [Category.assoc, ← e]⟩⟩⟩

中文:
定义 筛.coverByImage
  签名: (G : C ⥤ D) (U : D)
  定义体: ⟨Presieve.coverByImage G U, fun ⟨⟨Z, f₁, f₂, (e : _ = _)⟩⟩ g =>
    ⟨⟨Z, g ≫ f₁, f₂, show (g ≫ f₁) ≫ f₂ = g ≫ _ by rw [Category.assoc, ← e]⟩⟩⟩

Depends on / 依赖: Category, Category.assoc, Presieve, Presieve.coverByImage, coverByImage
-/
def Sieve.coverByImage (G : C ⥤ D) (U : D) : Sieve U :=
  ⟨Presieve.coverByImage G U, fun ⟨⟨Z, f₁, f₂, (e : _ = _)⟩⟩ g =>
    ⟨⟨Z, g ≫ f₁, f₂, show (g ≫ f₁) ≫ f₂ = g ≫ _ by rw [Category.assoc, ← e]⟩⟩⟩

/--
theorem `Presieve.in_coverByImage` / 定理 `Presieve.in_coverByImage`

English:
theorem Presieve.in_coverByImage
  given: (G : C ⥤ D) {X : D} {Y : C} (f : G.obj Y ⟶ X)
  proof: ⟨⟨Y, 𝟙 _, f, by simp⟩⟩

中文:
定理 Presieve.in_coverByImage
  条件: (G : C ⥤ D) {X : D} {Y : C} (f : G.obj Y ⟶ X)
  证明: ⟨⟨Y, 𝟙 _, f, by simp⟩⟩
-/
theorem Presieve.in_coverByImage (G : C ⥤ D) {X : D} {Y : C} (f : G.obj Y ⟶ X) :
    Presieve.coverByImage G X f :=
  ⟨⟨Y, 𝟙 _, f, by simp⟩⟩

/--
Definition of `Functor.IsCoverDense` / `Functor.IsCoverDense` 的定义

English:
class Functor.IsCoverDense
  parameters: (G : C ⥤ D) (K : GrothendieckTopology D)
  axioms and operations (1):
    - is_cover : forall U : D, Sieve.coverByImage G U in K U

中文:
类 函子.是余verDense
  参数: (G : C ⥤ D) (K : Grothendieck拓扑 D)
  公理与运算 (1 个):
    - is_cover : 对任意 U : D, 筛.coverByImage G U in K U
-/
class Functor.IsCoverDense (G : C ⥤ D) (K : GrothendieckTopology D) : Prop where
  is_cover : forall U : D, Sieve.coverByImage G U in K U

/--
lemma `Functor.is_cover_of_isCoverDense` / 引理 `Functor.is_cover_of_isCoverDense`

English:
lemma Functor.is_cover_of_isCoverDense
  statement: (G : C ⥤ D) (K : GrothendieckTopology D)
  proof: by
  apply Functor.IsCoverDense.is_cover

中文:
引理 函子.is_cover_of_isCoverDense
  结论: (G : C ⥤ D) (K : Grothendieck拓扑 D)
  证明: by
  apply Functor.IsCoverDense.is_cover

Depends on / 依赖: Functor, Functor.IsCoverDense.is_cover, IsCoverDense, is_cover
-/
lemma Functor.is_cover_of_isCoverDense (G : C ⥤ D) (K : GrothendieckTopology D)
    [G.IsCoverDense K] (U : D) : Sieve.coverByImage G U in K U := by
  apply Functor.IsCoverDense.is_cover

/--
lemma `Functor.isCoverDense_of_generate_singleton_functor_π_mem` / 引理 `Functor.isCoverDense_of_generate_singleton_functor_π_mem`

English:
lemma Functor.isCoverDense_of_generate_singleton_functor_π_mem
  statement: (G : C ⥤ D)
  proof: by
    obtain ⟨X, f, h⟩ := h B
    refine K.superset_covering ?_ h
    intro Y f ⟨Z, g, _, h, w⟩
    cases h
    exact ⟨⟨_, g, _, w⟩⟩

中文:
引理 函子.isCoverDense_of_generate_singleton_functor_π_mem
  结论: (G : C ⥤ D)
  证明: by
    obtain ⟨X, f, h⟩ := h B
    refine K.superset_covering ?_ h
    intro Y f ⟨Z, g, _, h, w⟩
    cases h
    exact ⟨⟨_, g, _, w⟩⟩

Depends on / 依赖: K.superset_covering, superset_covering
-/
lemma Functor.isCoverDense_of_generate_singleton_functor_π_mem (G : C ⥤ D)
    (K : GrothendieckTopology D)
    (h : forall B, exists (X : C) (f : G.obj X ⟶ B), Sieve.generate (Presieve.singleton f) in K B) :
    G.IsCoverDense K where
  is_cover B := by
    obtain ⟨X, f, h⟩ := h B
    refine K.superset_covering ?_ h
    intro Y f ⟨Z, g, _, h, w⟩
    cases h
    exact ⟨⟨_, g, _, w⟩⟩

attribute [nolint docBlame] CategoryTheory.Functor.IsCoverDense.is_cover

open Presieve Opposite

namespace Functor

namespace IsCoverDense

variable {K}
variable {A : Type*} [Category* A] (G : C ⥤ D)

-- this is not marked with `@[ext]` because `H` cannot be inferred from the type
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  statement: [G.IsCoverDense K] (ℱ : Sheaf K Type*) (X : D) {s t : ℱ.obj.obj (op X)}
  proof: by
  apply ((isSheaf_iff_isSheaf_of_type _ _).1 ℱ.property
    (Sieve.coverByImage G X) (G.is_cover_of_isCoverDense K X)).isSeparatedFor.ext
  rintro Y _ ⟨Z, f₁, f₂, ⟨rfl⟩⟩
  simp [h f₂]

中文:
定理 ext
  结论: [G.是余verDense K] (ℱ : 层 K 类型) (X : D) {s t : ℱ.obj.obj (op X)}
  证明: by
  apply ((isSheaf_iff_isSheaf_of_type _ _).1 ℱ.property
    (Sieve.coverByImage G X) (G.is_cover_of_isCoverDense K X)).isSeparatedFor.ext
  rintro Y _ ⟨Z, f₁, f₂, ⟨rfl⟩⟩
  simp [h f₂]

Depends on / 依赖: G.is_cover_of_isCoverDense, Sieve.coverByImage, coverByImage, isSeparatedFor, isSeparatedFor.ext, isSheaf_iff_isSheaf_of_type, is_cover_of_isCoverDense, property
-/
theorem ext [G.IsCoverDense K] (ℱ : Sheaf K Type*) (X : D) {s t : ℱ.obj.obj (op X)}
    (h : forall ⦃Y : C⦄ (f : G.obj Y ⟶ X), ℱ.obj.map f.op s = ℱ.obj.map f.op t) : s = t := by
  apply ((isSheaf_iff_isSheaf_of_type _ _).1 ℱ.property
    (Sieve.coverByImage G X) (G.is_cover_of_isCoverDense K X)).isSeparatedFor.ext
  rintro Y _ ⟨Z, f₁, f₂, ⟨rfl⟩⟩
  simp [h f₂]

variable {G}

/--
theorem `functorPullback_pushforward_covering` / 定理 `functorPullback_pushforward_covering`

English:
theorem functorPullback_pushforward_covering
  statement: [G.IsCoverDense K] [G.IsLocallyFull K] {X : C}
  proof: by
  refine K.transitive T.2 _ fun Y iYX hiYX => ?_
  apply K.transitive (G.is_cover_of_isCoverDense _ _) _
  rintro W _ ⟨Z, iWZ, iZY, rfl⟩
  rw [Sieve.pullback_comp]; apply K.pullback_stable; clear W iWZ
  apply K.superset_covering ?_ (G.functorPushforward_imageSieve_mem _ (iZY ≫ iYX))
  rintro W _ ⟨V, iVZ, iWV, ⟨iVX, e⟩, rfl⟩
  exact ⟨_, iVX, iWV, by simpa [e] using T.1.downward_closed hiYX (G.map iVZ ≫ iZY), by simp [e]⟩

中文:
定理 functorPullback_pushforward_covering
  结论: [G.是余verDense K] [G.是LocallyFull K] {X : C}
  证明: by
  refine K.transitive T.2 _ fun Y iYX hiYX => ?_
  apply K.transitive (G.is_cover_of_isCoverDense _ _) _
  rintro W _ ⟨Z, iWZ, iZY, rfl⟩
  rw [Sieve.pullback_comp]; apply K.pullback_stable; clear W iWZ
  apply K.superset_covering ?_ (G.functorPushforward_imageSieve_mem _ (iZY ≫ iYX))
  rintro W _ ⟨V, iVZ, iWV, ⟨iVX, e⟩, rfl⟩
  exact ⟨_, iVX, iWV, by simpa [e] using T.1.downward_closed hiYX (G.map iVZ ≫ iZY), by simp [e]⟩

Depends on / 依赖: G.functorPushforward_imageSieve_mem, G.is_cover_of_isCoverDense, G.map, K.pullback_stable, K.superset_covering, K.transitive, Sieve.pullback_comp, downward_closed, functorPushforward_imageSieve_mem, is_cover_of_isCoverDense, pullback_comp, pullback_stable, superset_covering, transitive
-/
theorem functorPullback_pushforward_covering [G.IsCoverDense K] [G.IsLocallyFull K] {X : C}
    (T : K (G.obj X)) : (T.val.functorPullback G).functorPushforward G in K (G.obj X) := by
  refine K.transitive T.2 _ fun Y iYX hiYX => ?_
  apply K.transitive (G.is_cover_of_isCoverDense _ _) _
  rintro W _ ⟨Z, iWZ, iZY, rfl⟩
  rw [Sieve.pullback_comp]; apply K.pullback_stable; clear W iWZ
  apply K.superset_covering ?_ (G.functorPushforward_imageSieve_mem _ (iZY ≫ iYX))
  rintro W _ ⟨V, iVZ, iWV, ⟨iVX, e⟩, rfl⟩
  exact ⟨_, iVX, iWV, by simpa [e] using T.1.downward_closed hiYX (G.map iVZ ≫ iZY), by simp [e]⟩

/-- (Implementation). Given a hom between the pullbacks of two sheaves, we can whisker it with
`coyoneda` to obtain a hom between the pullbacks of the sheaves of maps from `X`.
-/
@[simps! app]
/--
Definition of `homOver` / `homOver` 的定义

English:
definition homOver
  signature: {ℱ : Dᵒᵖ ⥤ A} {ℱ' : Sheaf K A} (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.obj) (X : A)
  body: whiskerRight α (coyoneda.obj (op X))

中文:
定义 homOver
  签名: {ℱ : Dᵒᵖ ⥤ A} {ℱ' : 层 K A} (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.obj) (X : A)
  定义体: whiskerRight α (coyoneda.obj (op X))

Depends on / 依赖: coyoneda, coyoneda.obj, whiskerRight
-/
def homOver {ℱ : Dᵒᵖ ⥤ A} {ℱ' : Sheaf K A} (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.obj) (X : A) :
    G.op ⋙ ℱ ⋙ coyoneda.obj (op X) ⟶ G.op ⋙ (sheafOver ℱ' X).obj :=
  whiskerRight α (coyoneda.obj (op X))

/-- (Implementation). Given an iso between the pullbacks of two sheaves, we can whisker it with
`coyoneda` to obtain an iso between the pullbacks of the sheaves of maps from `X`.
-/
@[simps! +dsimpLhs]
/--
Definition of `isoOver` / `isoOver` 的定义

English:
definition isoOver
  signature: {ℱ ℱ' : Sheaf K A} (α : G.op ⋙ ℱ.obj ≅ G.op ⋙ ℱ'.obj) (X : A)
  body: isoWhiskerRight α (coyoneda.obj (op X))

中文:
定义 isoOver
  签名: {ℱ ℱ' : 层 K A} (α : G.op ⋙ ℱ.obj ≅ G.op ⋙ ℱ'.obj) (X : A)
  定义体: isoWhiskerRight α (coyoneda.obj (op X))

Depends on / 依赖: coyoneda, coyoneda.obj, isoWhiskerRight
-/
def isoOver {ℱ ℱ' : Sheaf K A} (α : G.op ⋙ ℱ.obj ≅ G.op ⋙ ℱ'.obj) (X : A) :
    G.op ⋙ (sheafOver ℱ X).obj ≅ G.op ⋙ (sheafOver ℱ' X).obj :=
  isoWhiskerRight α (coyoneda.obj (op X))

/--
theorem `sheaf_eq_amalgamation` / 定理 `sheaf_eq_amalgamation`

English:
theorem sheaf_eq_amalgamation
  statement: (ℱ : Sheaf K A) {X : A} {U : D} {T : Sieve U} (hT)
  proof: (ℱ.property X T hT).isSeparatedFor x t _ h ((ℱ.property X T hT).isAmalgamation hx)

中文:
定理 sheaf_eq_amalgamation
  结论: (ℱ : 层 K A) {X : A} {U : D} {T : 筛 U} (hT)
  证明: (ℱ.property X T hT).isSeparatedFor x t _ h ((ℱ.property X T hT).isAmalgamation hx)

Depends on / 依赖: isAmalgamation, isSeparatedFor, property
-/
theorem sheaf_eq_amalgamation (ℱ : Sheaf K A) {X : A} {U : D} {T : Sieve U} (hT)
    (x : FamilyOfElements _ T) (hx) (t) (h : x.IsAmalgamation t) :
    t = (ℱ.property X T hT).amalgamate x hx :=
  (ℱ.property X T hT).isSeparatedFor x t _ h ((ℱ.property X T hT).isAmalgamation hx)

namespace Types

variable {ℱ : Dᵒᵖ ⥤ Type v} {ℱ' : Sheaf K (Type v)} (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.obj)

/--
theorem `naturality_apply` / 定理 `naturality_apply`

English:
theorem naturality_apply
  given: [G.IsLocallyFull K] {X Y : C} (i : G.obj X ⟶ G.obj Y) (x)
  proof: by
  have {X Y} (i : X ⟶ Y) (x) :
      ℱ'.1.map (G.map i).op (α.app _ x) = α.app _ (ℱ.map (G.map i).op x) := by
    exact ConcreteCategory.congr_hom (α.naturality i.op).symm x
  refine IsLocallyFull.ext G _ i fun V iVX iVY e => ?_
  simp only [← Functor.map_comp_apply, ← op_comp, ← e, this]

#adaptation_note

中文:
定理 naturality_apply
  条件: [G.是LocallyFull K] {X Y : C} (i : G.obj X ⟶ G.obj Y) (x)
  证明: by
  have {X Y} (i : X ⟶ Y) (x) :
      ℱ'.1.map (G.map i).op (α.app _ x) = α.app _ (ℱ.map (G.map i).op x) := by
    exact ConcreteCategory.congr_hom (α.naturality i.op).symm x
  refine IsLocallyFull.ext G _ i fun V iVX iVY e => ?_
  simp only [← Functor.map_comp_apply, ← op_comp, ← e, this]

#adaptation_note

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, Functor, Functor.map_comp_apply, G.map, IsLocallyFull, IsLocallyFull.ext, congr_hom, i.op, map_comp_apply, naturality, op_comp
-/
theorem naturality_apply [G.IsLocallyFull K] {X Y : C} (i : G.obj X ⟶ G.obj Y) (x) :
    ℱ'.1.map i.op (α.app _ x) = α.app _ (ℱ.map i.op x) := by
  have {X Y} (i : X ⟶ Y) (x) :
      ℱ'.1.map (G.map i).op (α.app _ x) = α.app _ (ℱ.map (G.map i).op x) := by
    exact ConcreteCategory.congr_hom (α.naturality i.op).symm x
  refine IsLocallyFull.ext G _ i fun V iVX iVY e => ?_
  simp only [← Functor.map_comp_apply, ← op_comp, ← e, this]

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/--
theorem `naturality` / 定理 `naturality`

English:
theorem naturality
  given: [G.IsLocallyFull K] {X Y : C} (i : G.obj X ⟶ G.obj Y)
  proof: by ext; exact naturality_apply α i _

中文:
定理 naturality
  条件: [G.是LocallyFull K] {X Y : C} (i : G.obj X ⟶ G.obj Y)
  证明: by ext; exact naturality_apply α i _

Depends on / 依赖: naturality_apply
-/
theorem naturality [G.IsLocallyFull K] {X Y : C} (i : G.obj X ⟶ G.obj Y) :
    α.app _ ≫ ℱ'.1.map i.op = ℱ.map i.op ≫ α.app _ := by ext; exact naturality_apply α i _

/--
Definition of `pushforwardFamily` / `pushforwardFamily` 的定义

English:
definition pushforwardFamily
  signature: {X} (x : ℱ.obj (op X))
  body: fun _ _ hf =>
ℱ'.obj.map hf.some.lift.op α.app (op _) (ℱ.map hf.some.map.op x)

中文:
定义 pushforwardFamily
  签名: {X} (x : ℱ.obj (op X))
  定义体: fun _ _ hf =>
ℱ'.obj.map hf.some.lift.op α.app (op _) (ℱ.map hf.some.map.op x)
-/
noncomputable def pushforwardFamily {X} (x : ℱ.obj (op X)) :
    FamilyOfElements ℱ'.obj (coverByImage G X) := fun _ _ hf =>
ℱ'.obj.map hf.some.lift.op α.app (op _) (ℱ.map hf.some.map.op x)

/--
theorem `pushforwardFamily_def` / 定理 `pushforwardFamily_def`

English:
theorem pushforwardFamily_def
  given: {X} (x : ℱ.obj (op X))
  proof: rfl

中文:
定理 pushforwardFamily_def
  条件: {X} (x : ℱ.obj (op X))
  证明: rfl
-/
@[simp] theorem pushforwardFamily_def {X} (x : ℱ.obj (op X)) :
    pushforwardFamily α x = fun _ _ hf =>
ℱ'.obj.map hf.some.lift.op α.app (op _) (ℱ.map hf.some.map.op x) := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `pushforwardFamily_apply` / 定理 `pushforwardFamily_apply`

English:
theorem pushforwardFamily_apply
  statement: [G.IsLocallyFull K]
  proof: by
  simp only [pushforwardFamily_def, op_obj]
  generalize Nonempty.some (Presieve.in_coverByImage G f) = l
  obtain ⟨W, iYW, iWX, rfl⟩ := l
  simp only [← op_comp, ← Functor.map_comp_apply, naturality_apply]

中文:
定理 pushforwardFamily_apply
  结论: [G.是LocallyFull K]
  证明: by
  simp only [pushforwardFamily_def, op_obj]
  generalize Nonempty.some (Presieve.in_coverByImage G f) = l
  obtain ⟨W, iYW, iWX, rfl⟩ := l
  simp only [← op_comp, ← Functor.map_comp_apply, naturality_apply]

Depends on / 依赖: Functor, Functor.map_comp_apply, Nonempty, Nonempty.some, Presieve, Presieve.in_coverByImage, generalize, in_coverByImage, map_comp_apply, naturality_apply, op_comp, op_obj, pushforwardFamily_def
-/
theorem pushforwardFamily_apply [G.IsLocallyFull K]
    {X} (x : ℱ.obj (op X)) {Y : C} (f : G.obj Y ⟶ X) :
    pushforwardFamily α x f (Presieve.in_coverByImage G f) = α.app (op Y) (ℱ.map f.op x) := by
  simp only [pushforwardFamily_def, op_obj]
  generalize Nonempty.some (Presieve.in_coverByImage G f) = l
  obtain ⟨W, iYW, iWX, rfl⟩ := l
  simp only [← op_comp, ← Functor.map_comp_apply, naturality_apply]

variable [G.IsCoverDense K] [G.IsLocallyFull K]

/--
theorem `pushforwardFamily_compatible` / 定理 `pushforwardFamily_compatible`

English:
theorem pushforwardFamily_compatible
  given: {X} (x : ℱ.obj (op X))
  proof: by
  suffices forall {Z W₁ W₂} (iWX₁ : G.obj W₁ ⟶ X) (iWX₂ : G.obj W₂ ⟶ X) (iZW₁ : Z ⟶ G.obj W₁)
      (iZW₂ : Z ⟶ G.obj W₂), iZW₁ ≫ iWX₁ = iZW₂ ≫ iWX₂ ->
      ℱ'.1.map iZW₁.op (α.app _ (ℱ.map iWX₁.op x)) = ℱ'.1.map iZW₂.op (α.app _ (ℱ.map iWX₂.op x)) by
    rintro Y₁ Y₂ Z iZY₁ iZY₂ f₁ f₂ h₁ h₂ e
    simp only [pushforwardFamily, ← Functor.map_comp_apply, ← op_comp]
    generalize Nonempty.some h₁ = l₁
    generalize Nonempty.some h₂ = l₂
    obtain ⟨W₁, iYW₁, iWX₁, rfl⟩ := l₁
    obtain ⟨W₂, iYW₂, iWX₂, rfl⟩ := l₂
    exact this _ _ _ _ (by simpa only [Category.assoc] using e)
  introv e
  refine ext G _ _ fun V iVZ => ?_
  simp only [← op_comp, ← Functor.map_comp_apply, naturality_apply,
    Category.assoc, e]

中文:
定理 pushforwardFamily_compatible
  条件: {X} (x : ℱ.obj (op X))
  证明: by
  suffices forall {Z W₁ W₂} (iWX₁ : G.obj W₁ ⟶ X) (iWX₂ : G.obj W₂ ⟶ X) (iZW₁ : Z ⟶ G.obj W₁)
      (iZW₂ : Z ⟶ G.obj W₂), iZW₁ ≫ iWX₁ = iZW₂ ≫ iWX₂ ->
      ℱ'.1.map iZW₁.op (α.app _ (ℱ.map iWX₁.op x)) = ℱ'.1.map iZW₂.op (α.app _ (ℱ.map iWX₂.op x)) by
    rintro Y₁ Y₂ Z iZY₁ iZY₂ f₁ f₂ h₁ h₂ e
    simp only [pushforwardFamily, ← Functor.map_comp_apply, ← op_comp]
    generalize Nonempty.some h₁ = l₁
    generalize Nonempty.some h₂ = l₂
    obtain ⟨W₁, iYW₁, iWX₁, rfl⟩ := l₁
    obtain ⟨W₂, iYW₂, iWX₂, rfl⟩ := l₂
    exact this _ _ _ _ (by simpa only [Category.assoc] using e)
  introv e
  refine ext G _ _ fun V iVZ => ?_
  simp only [← op_comp, ← Functor.map_comp_apply, naturality_apply,
    Category.assoc, e]

Depends on / 依赖: Functor, Functor.map_comp_apply, G.obj, Nonempty, Nonempty.some, generalize, map_comp_apply, op_comp, pushforwardFamily
-/
theorem pushforwardFamily_compatible {X} (x : ℱ.obj (op X)) :
    (pushforwardFamily α x).Compatible := by
  suffices forall {Z W₁ W₂} (iWX₁ : G.obj W₁ ⟶ X) (iWX₂ : G.obj W₂ ⟶ X) (iZW₁ : Z ⟶ G.obj W₁)
      (iZW₂ : Z ⟶ G.obj W₂), iZW₁ ≫ iWX₁ = iZW₂ ≫ iWX₂ ->
      ℱ'.1.map iZW₁.op (α.app _ (ℱ.map iWX₁.op x)) = ℱ'.1.map iZW₂.op (α.app _ (ℱ.map iWX₂.op x)) by
    rintro Y₁ Y₂ Z iZY₁ iZY₂ f₁ f₂ h₁ h₂ e
    simp only [pushforwardFamily, ← Functor.map_comp_apply, ← op_comp]
    generalize Nonempty.some h₁ = l₁
    generalize Nonempty.some h₂ = l₂
    obtain ⟨W₁, iYW₁, iWX₁, rfl⟩ := l₁
    obtain ⟨W₂, iYW₂, iWX₂, rfl⟩ := l₂
    exact this _ _ _ _ (by simpa only [Category.assoc] using e)
  introv e
  refine ext G _ _ fun V iVZ => ?_
  simp only [← op_comp, ← Functor.map_comp_apply, naturality_apply,
    Category.assoc, e]

/--
Definition of `appHom` / `appHom` 的定义

English:
definition appHom
  signature: (X : D)
  body: ↾fun x =>
  ((isSheaf_iff_isSheaf_of_type _ _).1 ℱ'.property _
    (G.is_cover_of_isCoverDense _ X)).amalgamate (pushforwardFamily α x)
      (pushforwardFamily_compatible α x)

@[simp]

中文:
定义 appHom
  签名: (X : D)
  定义体: ↾fun x =>
  ((isSheaf_iff_isSheaf_of_type _ _).1 ℱ'.property _
    (G.is_cover_of_isCoverDense _ X)).amalgamate (pushforwardFamily α x)
      (pushforwardFamily_compatible α x)

@[simp]
-/
noncomputable def appHom (X : D) : ℱ.obj (op X) ⟶ ℱ'.obj.obj (op X) := ↾fun x =>
  ((isSheaf_iff_isSheaf_of_type _ _).1 ℱ'.property _
    (G.is_cover_of_isCoverDense _ X)).amalgamate (pushforwardFamily α x)
      (pushforwardFamily_compatible α x)

@[simp]
/--
theorem `appHom_restrict` / 定理 `appHom_restrict`

English:
theorem appHom_restrict
  given: {X : D} {Y : C} (f : op X ⟶ op (G.obj Y)) (x)
  proof: (((isSheaf_iff_isSheaf_of_type _ _).1 ℱ'.property _ (G.is_cover_of_isCoverDense _ X)).valid_glue
      (pushforwardFamily_compatible α x) f.unop
          (Presieve.in_coverByImage G f.unop)).trans (pushforwardFamily_apply _ _ _)

@[simp]

中文:
定理 appHom_restrict
  条件: {X : D} {Y : C} (f : op X ⟶ op (G.obj Y)) (x)
  证明: (((isSheaf_iff_isSheaf_of_type _ _).1 ℱ'.property _ (G.is_cover_of_isCoverDense _ X)).valid_glue
      (pushforwardFamily_compatible α x) f.unop
          (Presieve.in_coverByImage G f.unop)).trans (pushforwardFamily_apply _ _ _)

@[simp]

Depends on / 依赖: G.is_cover_of_isCoverDense, Presieve, Presieve.in_coverByImage, f.unop, in_coverByImage, isSheaf_iff_isSheaf_of_type, is_cover_of_isCoverDense, property, pushforwardFamily_apply, pushforwardFamily_compatible, valid_glue
-/
theorem appHom_restrict {X : D} {Y : C} (f : op X ⟶ op (G.obj Y)) (x) :
    ℱ'.obj.map f (appHom α X x) = α.app (op Y) (ℱ.map f x) :=
  (((isSheaf_iff_isSheaf_of_type _ _).1 ℱ'.property _ (G.is_cover_of_isCoverDense _ X)).valid_glue
      (pushforwardFamily_compatible α x) f.unop
          (Presieve.in_coverByImage G f.unop)).trans (pushforwardFamily_apply _ _ _)

@[simp]
/--
theorem `appHom_valid_glue` / 定理 `appHom_valid_glue`

English:
theorem appHom_valid_glue
  given: {X : D} {Y : C} (f : op X ⟶ op (G.obj Y))
  proof: by
  ext
  apply appHom_restrict

unif_hint {J J' C : Type*} [Category* J] [Category* J'] [Category* C]
    (G G' : J' ⥤ J) (F F' : Jᵒᵖ ⥤ C) (j j' : J') where
  G ≟ G'
  F ≟ F'
  j ≟ j' ⊢ (G.op ⋙ F).obj (op j) ≟ F'.obj (op (G'.obj j')) in

中文:
定理 appHom_valid_glue
  条件: {X : D} {Y : C} (f : op X ⟶ op (G.obj Y))
  证明: by
  ext
  apply appHom_restrict

unif_hint {J J' C : Type*} [Category* J] [Category* J'] [Category* C]
    (G G' : J' ⥤ J) (F F' : Jᵒᵖ ⥤ C) (j j' : J') where
  G ≟ G'
  F ≟ F'
  j ≟ j' ⊢ (G.op ⋙ F).obj (op j) ≟ F'.obj (op (G'.obj j')) in

Depends on / 依赖: appHom_restrict
-/
theorem appHom_valid_glue {X : D} {Y : C} (f : op X ⟶ op (G.obj Y)) :
    appHom α X ≫ ℱ'.obj.map f = ℱ.map f ≫ α.app (op Y) := by
  ext
  apply appHom_restrict

unif_hint {J J' C : Type*} [Category* J] [Category* J'] [Category* C]
    (G G' : J' ⥤ J) (F F' : Jᵒᵖ ⥤ C) (j j' : J') where
  G ≟ G'
  F ≟ F'
  j ≟ j' ⊢ (G.op ⋙ F).obj (op j) ≟ F'.obj (op (G'.obj j')) in
/--
(Implementation). The maps given in `appIso` is inverse to each other and gives a `ℱ(X) ≅ ℱ'(X)`.
-/
@[simps]
/--
Definition of `appIso` / `appIso` 的定义

English:
definition appIso
  signature: {ℱ ℱ' : Sheaf K (Type v)} (i : G.op ⋙ ℱ.obj ≅ G.op ⋙ ℱ'.obj)
  body: appHom i.hom X
  inv := appHom i.inv X
  hom_inv_id := by
    ext x
    apply Functor.IsCoverDense.ext G
    intro Y f
    simp
  inv_hom_id := by
    ext x
    apply Functor.IsCoverDense.ext G
    intro Y f
    simp

中文:
定义 appIso
  签名: {ℱ ℱ' : 层 K (类型v)} (i : G.op ⋙ ℱ.obj ≅ G.op ⋙ ℱ'.obj)
  定义体: appHom i.hom X
  inv := appHom i.inv X
  hom_inv_id := by
    ext x
    apply Functor.IsCoverDense.ext G
    intro Y f
    simp
  inv_hom_id := by
    ext x
    apply Functor.IsCoverDense.ext G
    intro Y f
    simp

Depends on / 依赖: appHom, i.hom
-/
noncomputable def appIso {ℱ ℱ' : Sheaf K (Type v)} (i : G.op ⋙ ℱ.obj ≅ G.op ⋙ ℱ'.obj)
    (X : D) : ℱ.obj.obj (op X) ≅ ℱ'.obj.obj (op X) where
  hom := appHom i.hom X
  inv := appHom i.inv X
  hom_inv_id := by
    ext x
    apply Functor.IsCoverDense.ext G
    intro Y f
    simp
  inv_hom_id := by
    ext x
    apply Functor.IsCoverDense.ext G
    intro Y f
    simp

/--
Given a natural transformation `G ⋙ ℱ ⟶ G ⋙ ℱ'` between presheaves of types,
where `G` is locally-full and cover-dense, and `ℱ'` is a sheaf,
we may obtain a natural transformation between sheaves.
-/
@[simps]
/--
Definition of `presheafHom` / `presheafHom` 的定义

English:
definition presheafHom
  signature: (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.obj)
  body: appHom α (unop X)
  naturality X Y f := by
    ext x
    apply Functor.IsCoverDense.ext G
    intro Y' f'
    simp only [TypeCat.Fun.toFun_apply, types_comp_apply, ← map_comp_apply]
    rw [appHom_restrict]; rw [appHom_restrict]
    simp

中文:
定义 presheafHom
  签名: (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.obj)
  定义体: appHom α (unop X)
  naturality X Y f := by
    ext x
    apply Functor.IsCoverDense.ext G
    intro Y' f'
    simp only [TypeCat.Fun.toFun_apply, types_comp_apply, ← map_comp_apply]
    rw [appHom_restrict]; rw [appHom_restrict]
    simp

Depends on / 依赖: appHom
-/
noncomputable def presheafHom (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.obj) : ℱ ⟶ ℱ'.obj where
  app X := appHom α (unop X)
  naturality X Y f := by
    ext x
    apply Functor.IsCoverDense.ext G
    intro Y' f'
    simp only [TypeCat.Fun.toFun_apply, types_comp_apply, ← map_comp_apply]
    rw [appHom_restrict]; rw [appHom_restrict]
    simp

/--
Given a natural isomorphism `G ⋙ ℱ ≅ G ⋙ ℱ'` between presheaves of types,
where `G` is locally-full and cover-dense, and `ℱ, ℱ'` are sheaves,
we may obtain a natural isomorphism between presheaves.
-/
@[simps!]
/--
Definition of `presheafIso` / `presheafIso` 的定义

English:
definition presheafIso
  signature: {ℱ ℱ' : Sheaf K (Type v)} (i : G.op ⋙ ℱ.obj ≅ G.op ⋙ ℱ'.obj)
  body: NatIso.ofComponents (fun X => appIso i (unop X)) @(presheafHom i.hom).naturality

中文:
定义 presheafIso
  签名: {ℱ ℱ' : 层 K (类型v)} (i : G.op ⋙ ℱ.obj ≅ G.op ⋙ ℱ'.obj)
  定义体: NatIso.ofComponents (fun X => appIso i (unop X)) @(presheafHom i.hom).naturality

Depends on / 依赖: NatIso, NatIso.ofComponents, appIso, i.hom, naturality, ofComponents, presheafHom
-/
noncomputable def presheafIso {ℱ ℱ' : Sheaf K (Type v)} (i : G.op ⋙ ℱ.obj ≅ G.op ⋙ ℱ'.obj) :
    ℱ.obj ≅ ℱ'.obj :=
  NatIso.ofComponents (fun X => appIso i (unop X)) @(presheafHom i.hom).naturality

/--
Given a natural isomorphism `G ⋙ ℱ ≅ G ⋙ ℱ'` between presheaves of types,
where `G` is locally-full and cover-dense, and `ℱ, ℱ'` are sheaves,
we may obtain a natural isomorphism between sheaves.
-/
@[simps! hom_hom inv_hom]
/--
Definition of `sheafIso` / `sheafIso` 的定义

English:
definition sheafIso
  signature: {ℱ ℱ' : Sheaf K (Type v)} (i : G.op ⋙ ℱ.obj ≅ G.op ⋙ ℱ'.obj)
  body: (fullyFaithfulSheafToPresheaf _ _).preimageIso (presheafIso i)

中文:
定义 sheafIso
  签名: {ℱ ℱ' : 层 K (类型v)} (i : G.op ⋙ ℱ.obj ≅ G.op ⋙ ℱ'.obj)
  定义体: (fullyFaithfulSheafToPresheaf _ _).preimageIso (presheafIso i)

Depends on / 依赖: fullyFaithfulSheafToPresheaf, preimageIso, presheafIso
-/
noncomputable def sheafIso {ℱ ℱ' : Sheaf K (Type v)} (i : G.op ⋙ ℱ.obj ≅ G.op ⋙ ℱ'.obj) :
    ℱ ≅ ℱ' :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso (presheafIso i)

end Types

open IsCoverDense.Types

variable [G.IsCoverDense K] [G.IsLocallyFull K] {ℱ : Dᵒᵖ ⥤ A} {ℱ' : Sheaf K A}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- (Implementation). The sheaf map given in `types.sheaf_hom` is natural in terms of `X`. -/
@[simps]
/--
Definition of `sheafCoyonedaHom` / `sheafCoyonedaHom` 的定义

English:
definition sheafCoyonedaHom
  signature: (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.obj)
  body: presheafHom (homOver α (unop X))
  naturality X Y f := by
    ext U x
    change
      appHom (homOver α (unop Y)) (unop U) (f.unop ≫ x) =
        f.unop ≫ appHom (homOver α (unop X)) (unop U) x
    symm
    apply sheaf_eq_amalgamation
    · apply G.is_cover_of_isCoverDense
    -- Porting note: the following line closes a goal which didn't exist before reenableeta
    · exact pushforwardFamily_compatible (homOver α Y.unop) (f.unop ≫ x)
    intro Y' f' hf'
    dsimp
    simp only [Category.assoc]
    congr 1
    conv_lhs => rw [← hf'.some.fac]
    simp only [← Category.assoc, op_comp, Functor.map_comp]
    congr 1
    exact (appHom_restrict (homOver α (unop X)) hf'.some.map.op x).trans (by simp)

中文:
定义 sheafCoyonedaHom
  签名: (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.obj)
  定义体: presheafHom (homOver α (unop X))
  naturality X Y f := by
    ext U x
    change
      appHom (homOver α (unop Y)) (unop U) (f.unop ≫ x) =
        f.unop ≫ appHom (homOver α (unop X)) (unop U) x
    symm
    apply sheaf_eq_amalgamation
    · apply G.is_cover_of_isCoverDense
    -- Porting note: the following line closes a goal which didn't exist before reenableeta
    · exact pushforwardFamily_compatible (homOver α Y.unop) (f.unop ≫ x)
    intro Y' f' hf'
    dsimp
    simp only [Category.assoc]
    congr 1
    conv_lhs => rw [← hf'.some.fac]
    simp only [← Category.assoc, op_comp, Functor.map_comp]
    congr 1
    exact (appHom_restrict (homOver α (unop X)) hf'.some.map.op x).trans (by simp)

Depends on / 依赖: homOver, presheafHom
-/
noncomputable def sheafCoyonedaHom (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.obj) :
    coyoneda ⋙ (whiskeringLeft Dᵒᵖ A (Type _)).obj ℱ ⟶
      coyoneda ⋙ (whiskeringLeft Dᵒᵖ A (Type _)).obj ℱ'.obj where
  app X := presheafHom (homOver α (unop X))
  naturality X Y f := by
    ext U x
    change
      appHom (homOver α (unop Y)) (unop U) (f.unop ≫ x) =
        f.unop ≫ appHom (homOver α (unop X)) (unop U) x
    symm
    apply sheaf_eq_amalgamation
    · apply G.is_cover_of_isCoverDense
    -- Porting note: the following line closes a goal which didn't exist before reenableeta
    · exact pushforwardFamily_compatible (homOver α Y.unop) (f.unop ≫ x)
    intro Y' f' hf'
    dsimp
    simp only [Category.assoc]
    congr 1
    conv_lhs => rw [← hf'.some.fac]
    simp only [← Category.assoc, op_comp, Functor.map_comp]
    congr 1
    exact (appHom_restrict (homOver α (unop X)) hf'.some.map.op x).trans (by simp)

/--
Definition of `sheafYonedaHom` / `sheafYonedaHom` 的定义

English:
definition sheafYonedaHom
  signature: (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.obj)
  body: let α := (sheafCoyonedaHom α)
    { app := fun X => (α.app X).app U
      naturality := fun X Y f => by simpa using! congr_app (α.naturality f) U }
  naturality U V i := by
    ext X x
    exact ConcreteCategory.congr_hom (((sheafCoyonedaHom α).app X).naturality i) x

中文:
定义 sheafYonedaHom
  签名: (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.obj)
  定义体: let α := (sheafCoyonedaHom α)
    { app := fun X => (α.app X).app U
      naturality := fun X Y f => by simpa using! congr_app (α.naturality f) U }
  naturality U V i := by
    ext X x
    exact ConcreteCategory.congr_hom (((sheafCoyonedaHom α).app X).naturality i) x

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, congr_app, congr_hom, naturality, sheafCoyonedaHom
-/
noncomputable def sheafYonedaHom (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.obj) :
    ℱ ⋙ yoneda ⟶ ℱ'.obj ⋙ yoneda where
  app U :=
    let α := (sheafCoyonedaHom α)
    { app := fun X => (α.app X).app U
      naturality := fun X Y f => by simpa using! congr_app (α.naturality f) U }
  naturality U V i := by
    ext X x
    exact ConcreteCategory.congr_hom (((sheafCoyonedaHom α).app X).naturality i) x

/--
Definition of `sheafHom` / `sheafHom` 的定义

English:
definition sheafHom
  signature: (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.obj)
  body: let α' := sheafYonedaHom α
  { app := fun X => yoneda.preimage (α'.app X)
    naturality := fun X Y f => yoneda.map_injective (by simpa using! α'.naturality f) }

中文:
定义 sheafHom
  签名: (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.obj)
  定义体: let α' := sheafYonedaHom α
  { app := fun X => yoneda.preimage (α'.app X)
    naturality := fun X Y f => yoneda.map_injective (by simpa using! α'.naturality f) }

Depends on / 依赖: map_injective, naturality, preimage, sheafYonedaHom, yoneda, yoneda.map_injective, yoneda.preimage
-/
noncomputable def sheafHom (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.obj) : ℱ ⟶ ℱ'.obj :=
  let α' := sheafYonedaHom α
  { app := fun X => yoneda.preimage (α'.app X)
    naturality := fun X Y f => yoneda.map_injective (by simpa using! α'.naturality f) }

/--
Given a natural isomorphism `G ⋙ ℱ ≅ G ⋙ ℱ'` between presheaves of arbitrary category,
where `G` is locally-full and cover-dense, and `ℱ', ℱ` are sheaves,
we may obtain a natural isomorphism between presheaves.
-/
@[simps!]
/--
Definition of `presheafIso` / `presheafIso` 的定义

English:
definition presheafIso
  signature: {ℱ ℱ' : Sheaf K A} (i : G.op ⋙ ℱ.obj ≅ G.op ⋙ ℱ'.obj)
  body: by
  have : forall X : Dᵒᵖ, IsIso ((sheafHom i.hom).app X) := by
    intro X
    rw [← isIso_iff_of_reflects_iso _ yoneda]
    use (sheafYonedaHom i.inv).app X
    constructor <;> ext x : 2 <;>
      simp only [sheafHom, NatTrans.comp_app, NatTrans.id_app, Functor.map_preimage]
    · exact ((Types.presheafIso (isoOver i (unop x))).app X).hom_inv_id
    · exact ((Types.presheafIso (isoOver i (unop x))).app X).inv_hom_id
  haveI : IsIso (sheafHom i.hom) := by apply NatIso.isIso_of_isIso_app
  apply asIso (sheafHom i.hom)

中文:
定义 presheafIso
  签名: {ℱ ℱ' : 层 K A} (i : G.op ⋙ ℱ.obj ≅ G.op ⋙ ℱ'.obj)
  定义体: by
  have : forall X : Dᵒᵖ, IsIso ((sheafHom i.hom).app X) := by
    intro X
    rw [← isIso_iff_of_reflects_iso _ yoneda]
    use (sheafYonedaHom i.inv).app X
    constructor <;> ext x : 2 <;>
      simp only [sheafHom, NatTrans.comp_app, NatTrans.id_app, Functor.map_preimage]
    · exact ((Types.presheafIso (isoOver i (unop x))).app X).hom_inv_id
    · exact ((Types.presheafIso (isoOver i (unop x))).app X).inv_hom_id
  haveI : IsIso (sheafHom i.hom) := by apply NatIso.isIso_of_isIso_app
  apply asIso (sheafHom i.hom)

Depends on / 依赖: Functor, Functor.map_preimage, NatIso, NatIso.isIso_of_isIso_app, NatTrans, NatTrans.comp_app, NatTrans.id_app, Types.presheafIso, comp_app, hom_inv_id, i.hom, i.inv, id_app, inv_hom_id, isIso_iff_of_reflects_iso, isIso_of_isIso_app, isoOver, map_preimage, presheafIso, sheafHom
-/
noncomputable def presheafIso {ℱ ℱ' : Sheaf K A} (i : G.op ⋙ ℱ.obj ≅ G.op ⋙ ℱ'.obj) :
    ℱ.obj ≅ ℱ'.obj := by
  have : forall X : Dᵒᵖ, IsIso ((sheafHom i.hom).app X) := by
    intro X
    rw [← isIso_iff_of_reflects_iso _ yoneda]
    use (sheafYonedaHom i.inv).app X
    constructor <;> ext x : 2 <;>
      simp only [sheafHom, NatTrans.comp_app, NatTrans.id_app, Functor.map_preimage]
    · exact ((Types.presheafIso (isoOver i (unop x))).app X).hom_inv_id
    · exact ((Types.presheafIso (isoOver i (unop x))).app X).inv_hom_id
  haveI : IsIso (sheafHom i.hom) := by apply NatIso.isIso_of_isIso_app
  apply asIso (sheafHom i.hom)

/--
Given a natural isomorphism `G ⋙ ℱ ≅ G ⋙ ℱ'` between presheaves of arbitrary category,
where `G` is locally-full and cover-dense, and `ℱ', ℱ` are sheaves,
we may obtain a natural isomorphism between presheaves.
-/
@[simps! hom_hom inv_hom]
/--
Definition of `sheafIso` / `sheafIso` 的定义

English:
definition sheafIso
  signature: {ℱ ℱ' : Sheaf K A} (i : G.op ⋙ ℱ.obj ≅ G.op ⋙ ℱ'.obj)
  body: (fullyFaithfulSheafToPresheaf _ _).preimageIso (presheafIso i)

中文:
定义 sheafIso
  签名: {ℱ ℱ' : 层 K A} (i : G.op ⋙ ℱ.obj ≅ G.op ⋙ ℱ'.obj)
  定义体: (fullyFaithfulSheafToPresheaf _ _).preimageIso (presheafIso i)

Depends on / 依赖: fullyFaithfulSheafToPresheaf, preimageIso, presheafIso
-/
noncomputable def sheafIso {ℱ ℱ' : Sheaf K A} (i : G.op ⋙ ℱ.obj ≅ G.op ⋙ ℱ'.obj) : ℱ ≅ ℱ' :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso (presheafIso i)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `sheafHom_restrict_eq` / 定理 `sheafHom_restrict_eq`

English:
theorem sheafHom_restrict_eq
  given: (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.obj)
  proof: by
  ext X
  apply yoneda.map_injective
  ext U
  dsimp [sheafHom, -yoneda_obj_obj, -yoneda_map_app]
  rw [yoneda.map_preimage]
  symm
  change (show (ℱ'.obj ⋙ coyoneda.obj (op (unop U))).obj (op (G.obj (unop X))) from _) = _
  apply sheaf_eq_amalgamation ℱ' (G.is_cover_of_isCoverDense _ _)
  -- Porting note: next line was not needed in mathlib3
  · exact (pushforwardFamily_compatible _ _)
  intro Y f hf
  conv_lhs => rw [← hf.some.fac]
  dsimp
  simp only [Functor.map_comp, ← Category.assoc]
  congr 1
  simp only [Category.assoc]
  congr 1
  simpa using naturality_apply (G := G) (ℱ := ℱ ⋙ coyoneda.obj (op <| (G.op ⋙ ℱ).obj X))
    (ℱ' := ⟨_, Presheaf.isSheaf_comp_of_isSheaf K ℱ'.obj
      (coyoneda.obj (op ((G.op ⋙ ℱ).obj X))) ℱ'.property⟩)
    (whiskerRight α (coyoneda.obj _)) hf.some.map (𝟙 _)

中文:
定理 sheafHom_restrict_eq
  条件: (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.obj)
  证明: by
  ext X
  apply yoneda.map_injective
  ext U
  dsimp [sheafHom, -yoneda_obj_obj, -yoneda_map_app]
  rw [yoneda.map_preimage]
  symm
  change (show (ℱ'.obj ⋙ coyoneda.obj (op (unop U))).obj (op (G.obj (unop X))) from _) = _
  apply sheaf_eq_amalgamation ℱ' (G.is_cover_of_isCoverDense _ _)
  -- Porting note: next line was not needed in mathlib3
  · exact (pushforwardFamily_compatible _ _)
  intro Y f hf
  conv_lhs => rw [← hf.some.fac]
  dsimp
  simp only [Functor.map_comp, ← Category.assoc]
  congr 1
  simp only [Category.assoc]
  congr 1
  simpa using naturality_apply (G := G) (ℱ := ℱ ⋙ coyoneda.obj (op <| (G.op ⋙ ℱ).obj X))
    (ℱ' := ⟨_, Presheaf.isSheaf_comp_of_isSheaf K ℱ'.obj
      (coyoneda.obj (op ((G.op ⋙ ℱ).obj X))) ℱ'.property⟩)
    (whiskerRight α (coyoneda.obj _)) hf.some.map (𝟙 _)

Depends on / 依赖: G.is_cover_of_isCoverDense, G.obj, coyoneda, coyoneda.obj, is_cover_of_isCoverDense, map_injective, map_preimage, sheafHom, sheaf_eq_amalgamation, yoneda, yoneda.map_injective, yoneda.map_preimage, yoneda_map_app, yoneda_obj_obj
-/
theorem sheafHom_restrict_eq (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.obj) :
    whiskerLeft G.op (sheafHom α) = α := by
  ext X
  apply yoneda.map_injective
  ext U
  dsimp [sheafHom, -yoneda_obj_obj, -yoneda_map_app]
  rw [yoneda.map_preimage]
  symm
  change (show (ℱ'.obj ⋙ coyoneda.obj (op (unop U))).obj (op (G.obj (unop X))) from _) = _
  apply sheaf_eq_amalgamation ℱ' (G.is_cover_of_isCoverDense _ _)
  -- Porting note: next line was not needed in mathlib3
  · exact (pushforwardFamily_compatible _ _)
  intro Y f hf
  conv_lhs => rw [← hf.some.fac]
  dsimp
  simp only [Functor.map_comp, ← Category.assoc]
  congr 1
  simp only [Category.assoc]
  congr 1
  simpa using naturality_apply (G := G) (ℱ := ℱ ⋙ coyoneda.obj (op <| (G.op ⋙ ℱ).obj X))
    (ℱ' := ⟨_, Presheaf.isSheaf_comp_of_isSheaf K ℱ'.obj
      (coyoneda.obj (op ((G.op ⋙ ℱ).obj X))) ℱ'.property⟩)
    (whiskerRight α (coyoneda.obj _)) hf.some.map (𝟙 _)

set_option backward.defeqAttrib.useBackward true in
variable (G) in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `sheafHom_eq` / 定理 `sheafHom_eq`

English:
theorem sheafHom_eq
  given: (α : ℱ ⟶ ℱ'.obj)
  statement: sheafHom (whiskerLeft G.op α) = α
  proof: by
  ext X
  apply yoneda.map_injective
  ext U
  dsimp [sheafHom, -yoneda_obj_obj, -yoneda_map_app]
  rw [yoneda.map_preimage]
  symm
  change (show (ℱ'.obj ⋙ coyoneda.obj (op (unop U))).obj (op (unop X)) from _) = _
  apply sheaf_eq_amalgamation ℱ' (G.is_cover_of_isCoverDense _ _)
  -- Porting note: next line was not needed in mathlib3
  · exact (pushforwardFamily_compatible _ _)
  intro Y f hf
  conv_lhs => rw [← hf.some.fac]
  dsimp; simp

中文:
定理 sheafHom_eq
  条件: (α : ℱ ⟶ ℱ'.obj)
  结论: sheafHom (whiskerLeft G.op α) = α
  证明: by
  ext X
  apply yoneda.map_injective
  ext U
  dsimp [sheafHom, -yoneda_obj_obj, -yoneda_map_app]
  rw [yoneda.map_preimage]
  symm
  change (show (ℱ'.obj ⋙ coyoneda.obj (op (unop U))).obj (op (unop X)) from _) = _
  apply sheaf_eq_amalgamation ℱ' (G.is_cover_of_isCoverDense _ _)
  -- Porting note: next line was not needed in mathlib3
  · exact (pushforwardFamily_compatible _ _)
  intro Y f hf
  conv_lhs => rw [← hf.some.fac]
  dsimp; simp

Depends on / 依赖: G.is_cover_of_isCoverDense, coyoneda, coyoneda.obj, is_cover_of_isCoverDense, map_injective, map_preimage, sheafHom, sheaf_eq_amalgamation, yoneda, yoneda.map_injective, yoneda.map_preimage, yoneda_map_app, yoneda_obj_obj
-/
theorem sheafHom_eq (α : ℱ ⟶ ℱ'.obj) : sheafHom (whiskerLeft G.op α) = α := by
  ext X
  apply yoneda.map_injective
  ext U
  dsimp [sheafHom, -yoneda_obj_obj, -yoneda_map_app]
  rw [yoneda.map_preimage]
  symm
  change (show (ℱ'.obj ⋙ coyoneda.obj (op (unop U))).obj (op (unop X)) from _) = _
  apply sheaf_eq_amalgamation ℱ' (G.is_cover_of_isCoverDense _ _)
  -- Porting note: next line was not needed in mathlib3
  · exact (pushforwardFamily_compatible _ _)
  intro Y f hf
  conv_lhs => rw [← hf.some.fac]
  dsimp; simp

/--
Definition of `restrictHomEquivHom` / `restrictHomEquivHom` 的定义

English:
definition restrictHomEquivHom
  signature: : (G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.obj) ≃ (ℱ ⟶ ℱ'.obj) where
  body: sheafHom
  invFun := whiskerLeft G.op
  left_inv := sheafHom_restrict_eq
  right_inv := sheafHom_eq _

@[reassoc]

中文:
定义 restrictHomEquivHom
  签名: : (G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.obj) ≃ (ℱ ⟶ ℱ'.obj) where
  定义体: sheafHom
  invFun := whiskerLeft G.op
  left_inv := sheafHom_restrict_eq
  right_inv := sheafHom_eq _

@[reassoc]

Depends on / 依赖: sheafHom
-/
noncomputable def restrictHomEquivHom : (G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.obj) ≃ (ℱ ⟶ ℱ'.obj) where
  toFun := sheafHom
  invFun := whiskerLeft G.op
  left_inv := sheafHom_restrict_eq
  right_inv := sheafHom_eq _

@[reassoc]
/--
lemma `restrictHomEquivHom_naturality_right_symm` / 引理 `restrictHomEquivHom_naturality_right_symm`

English:
lemma restrictHomEquivHom_naturality_right_symm
  proof: rfl

@[reassoc]

中文:
引理 restrictHomEquivHom_naturality_right_symm
  证明: rfl

@[reassoc]

Depends on / 依赖: g.hom
-/
lemma restrictHomEquivHom_naturality_right_symm
    (f : ℱ ⟶ ℱ'.obj) {𝒢'} (g : ℱ' ⟶ 𝒢') :
    (restrictHomEquivHom (G := G)).symm (f ≫ g.hom) =
      restrictHomEquivHom.symm f ≫ whiskerLeft _ g.hom := rfl

@[reassoc]
/--
lemma `restrictHomEquivHom_naturality_right` / 引理 `restrictHomEquivHom_naturality_right`

English:
lemma restrictHomEquivHom_naturality_right
  proof: by
  apply (restrictHomEquivHom (G := G)).symm.injective
  simpa only [Equiv.symm_apply_apply] using
    (restrictHomEquivHom_naturality_right_symm (G := G) (restrictHomEquivHom f) g).symm

@[reassoc]

中文:
引理 restrictHomEquivHom_naturality_right
  证明: by
  apply (restrictHomEquivHom (G := G)).symm.injective
  simpa only [Equiv.symm_apply_apply] using
    (restrictHomEquivHom_naturality_right_symm (G := G) (restrictHomEquivHom f) g).symm

@[reassoc]

Depends on / 依赖: Equiv.symm_apply_apply, injective, restrictHomEquivHom, restrictHomEquivHom_naturality_right_symm, symm.injective, symm_apply_apply
-/
lemma restrictHomEquivHom_naturality_right
    (f : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.obj) {𝒢'} (g : ℱ' ⟶ 𝒢') :
    restrictHomEquivHom (f ≫ whiskerLeft G.op g.hom) =
      restrictHomEquivHom f ≫ g.hom := by
  apply (restrictHomEquivHom (G := G)).symm.injective
  simpa only [Equiv.symm_apply_apply] using
    (restrictHomEquivHom_naturality_right_symm (G := G) (restrictHomEquivHom f) g).symm

@[reassoc]
/--
lemma `restrictHomEquivHom_naturality_left_symm` / 引理 `restrictHomEquivHom_naturality_left_symm`

English:
lemma restrictHomEquivHom_naturality_left_symm
  proof: rfl

@[reassoc]

中文:
引理 restrictHomEquivHom_naturality_left_symm
  证明: rfl

@[reassoc]
-/
lemma restrictHomEquivHom_naturality_left_symm
    {𝒢} (f : 𝒢 ⟶ ℱ) (g : ℱ ⟶ ℱ'.obj) :
    (restrictHomEquivHom (G := G)).symm (f ≫ g) =
      whiskerLeft G.op f ≫ restrictHomEquivHom.symm g := rfl

@[reassoc]
/--
lemma `restrictHomEquivHom_naturality_left` / 引理 `restrictHomEquivHom_naturality_left`

English:
lemma restrictHomEquivHom_naturality_left
  proof: by
  apply (restrictHomEquivHom (G := G)).symm.injective
  simpa only [Equiv.symm_apply_apply] using
    (restrictHomEquivHom_naturality_left_symm (G := G) (f := f)
      (g := restrictHomEquivHom g)).symm

中文:
引理 restrictHomEquivHom_naturality_left
  证明: by
  apply (restrictHomEquivHom (G := G)).symm.injective
  simpa only [Equiv.symm_apply_apply] using
    (restrictHomEquivHom_naturality_left_symm (G := G) (f := f)
      (g := restrictHomEquivHom g)).symm

Depends on / 依赖: Equiv.symm_apply_apply, injective, restrictHomEquivHom, restrictHomEquivHom_naturality_left_symm, symm.injective, symm_apply_apply
-/
lemma restrictHomEquivHom_naturality_left
    {𝒢} (f : 𝒢 ⟶ ℱ) (g : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.obj) :
    restrictHomEquivHom (whiskerLeft _ f ≫ g) =
      f ≫ restrictHomEquivHom g := by
  apply (restrictHomEquivHom (G := G)).symm.injective
  simpa only [Equiv.symm_apply_apply] using
    (restrictHomEquivHom_naturality_left_symm (G := G) (f := f)
      (g := restrictHomEquivHom g)).symm

/--
theorem `iso_of_restrict_iso` / 定理 `iso_of_restrict_iso`

English:
theorem iso_of_restrict_iso
  given: {ℱ ℱ' : Sheaf K A} (α : ℱ ⟶ ℱ') (i : IsIso (whiskerLeft G.op α.hom))
  proof: by
  convert! (sheafIso (asIso (whiskerLeft G.op α.hom))).isIso_hom using 1
  ext1
  apply (sheafHom_eq _ _).symm

中文:
定理 iso_of_restrict_iso
  条件: {ℱ ℱ' : 层 K A} (α : ℱ ⟶ ℱ') (i : 是同构 (whiskerLeft G.op α.hom))
  证明: by
  convert! (sheafIso (asIso (whiskerLeft G.op α.hom))).isIso_hom using 1
  ext1
  apply (sheafHom_eq _ _).symm

Depends on / 依赖: G.op, convert, isIso_hom, sheafHom_eq, sheafIso, whiskerLeft
-/
theorem iso_of_restrict_iso {ℱ ℱ' : Sheaf K A} (α : ℱ ⟶ ℱ') (i : IsIso (whiskerLeft G.op α.hom)) :
    IsIso α := by
  convert! (sheafIso (asIso (whiskerLeft G.op α.hom))).isIso_hom using 1
  ext1
  apply (sheafHom_eq _ _).symm

variable (G K)

/--
lemma `compatiblePreserving` / 引理 `compatiblePreserving`

English:
lemma compatiblePreserving
  given: [G.IsLocallyFaithful K]
  statement: CompatiblePreserving K G
  proof: by
  constructor
  intro ℱ Z T x hx Y₁ Y₂ X f₁ f₂ g₁ g₂ hg₁ hg₂ eq
  apply Functor.IsCoverDense.ext G
  intro W i
  refine IsLocallyFull.ext G _ (i ≫ f₁) fun V₁ iVW iV₁Y₁ e₁ => ?_
  refine IsLocallyFull.ext G _ (G.map iVW ≫ i ≫ f₂) fun V₂ iV₂V₁ iV₂Y₂ e₂ => ?_
  refine IsLocallyFaithful.ext G _ (iV₂V₁ ≫ iV₁Y₁ ≫ g₁) (iV₂Y₂ ≫ g₂) (by simp [e₁, e₂, eq]) ?_
  intro V₃ iV₃ e₄
  simp only [← op_comp, ← Functor.map_comp_apply, ← e₁, ← e₂, ← Functor.map_comp]
  apply hx
  simpa using e₄

中文:
引理 compatiblePreserving
  条件: [G.是LocallyFaithful K]
  结论: 余mpatiblePreserving K G
  证明: by
  constructor
  intro ℱ Z T x hx Y₁ Y₂ X f₁ f₂ g₁ g₂ hg₁ hg₂ eq
  apply Functor.IsCoverDense.ext G
  intro W i
  refine IsLocallyFull.ext G _ (i ≫ f₁) fun V₁ iVW iV₁Y₁ e₁ => ?_
  refine IsLocallyFull.ext G _ (G.map iVW ≫ i ≫ f₂) fun V₂ iV₂V₁ iV₂Y₂ e₂ => ?_
  refine IsLocallyFaithful.ext G _ (iV₂V₁ ≫ iV₁Y₁ ≫ g₁) (iV₂Y₂ ≫ g₂) (by simp [e₁, e₂, eq]) ?_
  intro V₃ iV₃ e₄
  simp only [← op_comp, ← Functor.map_comp_apply, ← e₁, ← e₂, ← Functor.map_comp]
  apply hx
  simpa using e₄

Depends on / 依赖: Functor, Functor.IsCoverDense.ext, Functor.map_comp, Functor.map_comp_apply, G.map, IsCoverDense, IsLocallyFaithful, IsLocallyFaithful.ext, IsLocallyFull, IsLocallyFull.ext, map_comp, map_comp_apply, op_comp
-/
lemma compatiblePreserving [G.IsLocallyFaithful K] : CompatiblePreserving K G := by
  constructor
  intro ℱ Z T x hx Y₁ Y₂ X f₁ f₂ g₁ g₂ hg₁ hg₂ eq
  apply Functor.IsCoverDense.ext G
  intro W i
  refine IsLocallyFull.ext G _ (i ≫ f₁) fun V₁ iVW iV₁Y₁ e₁ => ?_
  refine IsLocallyFull.ext G _ (G.map iVW ≫ i ≫ f₂) fun V₂ iV₂V₁ iV₂Y₂ e₂ => ?_
  refine IsLocallyFaithful.ext G _ (iV₂V₁ ≫ iV₁Y₁ ≫ g₁) (iV₂Y₂ ≫ g₂) (by simp [e₁, e₂, eq]) ?_
  intro V₃ iV₃ e₄
  simp only [← op_comp, ← Functor.map_comp_apply, ← e₁, ← e₂, ← Functor.map_comp]
  apply hx
  simpa using e₄

/--
lemma `isContinuous` / 引理 `isContinuous`

English:
lemma isContinuous
  given: [G.IsLocallyFaithful K] (Hp : CoverPreserving J K G)
  statement: G.IsContinuous J K
  proof: isContinuous_of_coverPreserving (compatiblePreserving K G) Hp

中文:
引理 isContinuous
  条件: [G.是LocallyFaithful K] (Hp : 余verPreserving J K G)
  结论: G.是连续 J K
  证明: isContinuous_of_coverPreserving (compatiblePreserving K G) Hp

Depends on / 依赖: compatiblePreserving, isContinuous_of_coverPreserving
-/
lemma isContinuous [G.IsLocallyFaithful K] (Hp : CoverPreserving J K G) : G.IsContinuous J K :=
  isContinuous_of_coverPreserving (compatiblePreserving K G) Hp

/--
Instance `full_sheafPushforwardContinuous` / 实例 `full_sheafPushforwardContinuous`

English:
instance full_sheafPushforwardContinuous
  signature: [G.IsContinuous J K]
  body: ⟨⟨sheafHom α.hom⟩, Sheaf.hom_ext sheafHom_restrict_eq α.hom⟩

中文:
实例 full_sheafPushforwardContinuous
  签名: [G.是连续 J K]
  定义体: ⟨⟨sheafHom α.hom⟩, Sheaf.hom_ext sheafHom_restrict_eq α.hom⟩

Depends on / 依赖: Sheaf.hom_ext, hom_ext, sheafHom, sheafHom_restrict_eq
-/
instance full_sheafPushforwardContinuous [G.IsContinuous J K] :
    Full (G.sheafPushforwardContinuous A J K) where
map_surjective α := ⟨⟨sheafHom α.hom⟩, Sheaf.hom_ext sheafHom_restrict_eq α.hom⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Instance `faithful_sheafPushforwardContinuous` / 实例 `faithful_sheafPushforwardContinuous`

English:
instance faithful_sheafPushforwardContinuous
  signature: [G.IsContinuous J K]
  body: by
    intro ℱ ℱ' α β e
    ext1
    apply_fun fun e => e.hom at e
    dsimp [sheafPushforwardContinuous] at e
    rw [← sheafHom_eq G α.hom]; rw [← sheafHom_eq G β.hom]; rw [e]

中文:
实例 faithful_sheafPushforwardContinuous
  签名: [G.是连续 J K]
  定义体: by
    intro ℱ ℱ' α β e
    ext1
    apply_fun fun e => e.hom at e
    dsimp [sheafPushforwardContinuous] at e
    rw [← sheafHom_eq G α.hom]; rw [← sheafHom_eq G β.hom]; rw [e]

Depends on / 依赖: apply_fun, e.hom, sheafHom_eq, sheafPushforwardContinuous
-/
instance faithful_sheafPushforwardContinuous [G.IsContinuous J K] :
    Faithful (G.sheafPushforwardContinuous A J K) where
  map_injective := by
    intro ℱ ℱ' α β e
    ext1
    apply_fun fun e => e.hom at e
    dsimp [sheafPushforwardContinuous] at e
    rw [← sheafHom_eq G α.hom]; rw [← sheafHom_eq G β.hom]; rw [e]

end IsCoverDense

/--
lemma `whiskerLeft_obj_map_bijective_of_isCoverDense` / 引理 `whiskerLeft_obj_map_bijective_of_isCoverDense`

English:
lemma whiskerLeft_obj_map_bijective_of_isCoverDense
  statement: (G : C ⥤ D)
  proof: (IsCoverDense.restrictHomEquivHom (ℱ' := ⟨Q, hQ⟩)).symm.bijective

中文:
引理 whiskerLeft_obj_map_bijective_of_isCoverDense
  结论: (G : C ⥤ D)
  证明: (IsCoverDense.restrictHomEquivHom (ℱ' := ⟨Q, hQ⟩)).symm.bijective

Depends on / 依赖: IsCoverDense, IsCoverDense.restrictHomEquivHom, bijective, restrictHomEquivHom, symm.bijective
-/
lemma whiskerLeft_obj_map_bijective_of_isCoverDense (G : C ⥤ D)
    [G.IsCoverDense K] [G.IsLocallyFull K] {A : Type*} [Category* A]
    (P Q : Dᵒᵖ ⥤ A) (hQ : Presheaf.IsSheaf K Q) :
    Function.Bijective (((whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj G.op).map : (P ⟶ Q) -> _) :=
  (IsCoverDense.restrictHomEquivHom (ℱ' := ⟨Q, hQ⟩)).symm.bijective

variable (G : C ⥤ D) {A : Type*} [Category* A]

/--
Definition of `IsDenseSubsite` / `IsDenseSubsite` 的定义

English:
class IsDenseSubsite
  parameters: : Prop where
  axioms and operations (4):
    - isCoverDense' : G.IsCoverDense K  [default: by infer_instance]
    - isLocallyFull' : G.IsLocallyFull K  [default: by infer_instance]
    - isLocallyFaithful' : G.IsLocallyFaithful K  [default: by infer_instance]
    - functorPushforward_mem_iff : forall {X : C} {S : Sieve X}, S.functorPushforward G in K _ ↔ S in J _

中文:
类 是DenseSubsite
  参数: : 命题 where
  公理与运算 (4 个):
    - isCoverDense' : G.是余verDense K  [默认: by infer_instance]
    - isLocallyFull' : G.是LocallyFull K  [默认: by infer_instance]
    - isLocallyFaithful' : G.是LocallyFaithful K  [默认: by infer_instance]
    - functorPushforward_mem_iff : 对任意 {X : C} {S : 筛 X}, S.functorPushforward G in K _ ↔ S in J _

Depends on / 依赖: G.IsLocallyFaithful, G.IsLocallyFull, IsLocallyFaithful, IsLocallyFull, S.functorPushforward, functorPushforward, functorPushforward_mem_iff, infer_instance, isLocallyFaithful, isLocallyFull
-/
class IsDenseSubsite : Prop where
  isCoverDense' : G.IsCoverDense K := by infer_instance
  isLocallyFull' : G.IsLocallyFull K := by infer_instance
  isLocallyFaithful' : G.IsLocallyFaithful K := by infer_instance
  functorPushforward_mem_iff : forall {X : C} {S : Sieve X}, S.functorPushforward G in K _ ↔ S in J _

/--
lemma `functorPushforward_mem_iff` / 引理 `functorPushforward_mem_iff`

English:
lemma functorPushforward_mem_iff
  given: {X : C} {S : Sieve X} [G.IsDenseSubsite J K]
  proof: IsDenseSubsite.functorPushforward_mem_iff

中文:
引理 functorPushforward_mem_iff
  条件: {X : C} {S : 筛 X} [G.是DenseSubsite J K]
  证明: IsDenseSubsite.functorPushforward_mem_iff

Depends on / 依赖: IsDenseSubsite, IsDenseSubsite.functorPushforward_mem_iff, functorPushforward_mem_iff
-/
lemma functorPushforward_mem_iff {X : C} {S : Sieve X} [G.IsDenseSubsite J K] :
    S.functorPushforward G in K _ ↔ S in J _ := IsDenseSubsite.functorPushforward_mem_iff

namespace IsDenseSubsite

variable [G.IsDenseSubsite J K]

include J K

/--
lemma `isCoverDense` / 引理 `isCoverDense`

English:
lemma isCoverDense
  statement: G.IsCoverDense K
  proof: isCoverDense' J

中文:
引理 isCoverDense
  结论: G.是余verDense K
  证明: isCoverDense' J

Depends on / 依赖: isCoverDense
-/
lemma isCoverDense : G.IsCoverDense K := isCoverDense' J
/--
lemma `isLocallyFull` / 引理 `isLocallyFull`

English:
lemma isLocallyFull
  statement: G.IsLocallyFull K
  proof: isLocallyFull' J

中文:
引理 isLocallyFull
  结论: G.是LocallyFull K
  证明: isLocallyFull' J

Depends on / 依赖: isLocallyFull
-/
lemma isLocallyFull : G.IsLocallyFull K := isLocallyFull' J
/--
lemma `isLocallyFaithful` / 引理 `isLocallyFaithful`

English:
lemma isLocallyFaithful
  statement: G.IsLocallyFaithful K
  proof: isLocallyFaithful' J

中文:
引理 isLocallyFaithful
  结论: G.是LocallyFaithful K
  证明: isLocallyFaithful' J

Depends on / 依赖: isLocallyFaithful
-/
lemma isLocallyFaithful : G.IsLocallyFaithful K := isLocallyFaithful' J

/--
lemma `coverPreserving` / 引理 `coverPreserving`

English:
lemma coverPreserving
  statement: CoverPreserving J K G
  proof: ⟨functorPushforward_mem_iff.mpr⟩

中文:
引理 coverPreserving
  结论: 余verPreserving J K G
  证明: ⟨functorPushforward_mem_iff.mpr⟩

Depends on / 依赖: functorPushforward_mem_iff, functorPushforward_mem_iff.mpr
-/
lemma coverPreserving : CoverPreserving J K G :=
  ⟨functorPushforward_mem_iff.mpr⟩

instance (priority := 900) : G.IsContinuous J K :=
  letI := IsDenseSubsite.isCoverDense J K G
  letI := IsDenseSubsite.isLocallyFull J K G
  letI := IsDenseSubsite.isLocallyFaithful J K G
  IsCoverDense.isContinuous J K G (IsDenseSubsite.coverPreserving J K G)

instance (priority := 900) : G.IsCocontinuous J K where
  cover_lift hS :=
    letI := IsDenseSubsite.isCoverDense J K G
    letI := IsDenseSubsite.isLocallyFull J K G
    IsDenseSubsite.functorPushforward_mem_iff.mp
      (IsCoverDense.functorPullback_pushforward_covering ⟨_, hS⟩)

/--
Instance `full_sheafPushforwardContinuous` / 实例 `full_sheafPushforwardContinuous`

English:
instance full_sheafPushforwardContinuous
  signature: :
  body: letI := IsDenseSubsite.isCoverDense J K G
  letI := IsDenseSubsite.isLocallyFull J K G
  inferInstance

中文:
实例 full_sheafPushforwardContinuous
  签名: :
  定义体: letI := IsDenseSubsite.isCoverDense J K G
  letI := IsDenseSubsite.isLocallyFull J K G
  inferInstance

Depends on / 依赖: IsDenseSubsite, IsDenseSubsite.isCoverDense, IsDenseSubsite.isLocallyFull, isCoverDense, isLocallyFull
-/
instance full_sheafPushforwardContinuous :
    Full (G.sheafPushforwardContinuous A J K) :=
  letI := IsDenseSubsite.isCoverDense J K G
  letI := IsDenseSubsite.isLocallyFull J K G
  inferInstance

/--
Instance `faithful_sheafPushforwardContinuous` / 实例 `faithful_sheafPushforwardContinuous`

English:
instance faithful_sheafPushforwardContinuous
  signature: :
  body: letI := IsDenseSubsite.isCoverDense J K G
  letI := IsDenseSubsite.isLocallyFull J K G
  inferInstance

中文:
实例 faithful_sheafPushforwardContinuous
  签名: :
  定义体: letI := IsDenseSubsite.isCoverDense J K G
  letI := IsDenseSubsite.isLocallyFull J K G
  inferInstance

Depends on / 依赖: IsDenseSubsite, IsDenseSubsite.isCoverDense, IsDenseSubsite.isLocallyFull, isCoverDense, isLocallyFull
-/
instance faithful_sheafPushforwardContinuous :
    Faithful (G.sheafPushforwardContinuous A J K) :=
  letI := IsDenseSubsite.isCoverDense J K G
  letI := IsDenseSubsite.isLocallyFull J K G
  inferInstance

/--
lemma `imageSieve_mem` / 引理 `imageSieve_mem`

English:
lemma imageSieve_mem
  given: {U V} (f : G.obj U ⟶ G.obj V)
  proof: letI := IsDenseSubsite.isLocallyFull J K G
  IsDenseSubsite.functorPushforward_mem_iff.mp (G.functorPushforward_imageSieve_mem K f)

中文:
引理 imageSieve_mem
  条件: {U V} (f : G.obj U ⟶ G.obj V)
  证明: letI := IsDenseSubsite.isLocallyFull J K G
  IsDenseSubsite.functorPushforward_mem_iff.mp (G.functorPushforward_imageSieve_mem K f)

Depends on / 依赖: G.functorPushforward_imageSieve_mem, IsDenseSubsite, IsDenseSubsite.functorPushforward_mem_iff.mp, IsDenseSubsite.isLocallyFull, functorPushforward_imageSieve_mem, functorPushforward_mem_iff, isLocallyFull
-/
lemma imageSieve_mem {U V} (f : G.obj U ⟶ G.obj V) :
    G.imageSieve f in J _ :=
  letI := IsDenseSubsite.isLocallyFull J K G
  IsDenseSubsite.functorPushforward_mem_iff.mp (G.functorPushforward_imageSieve_mem K f)

/--
lemma `equalizer_mem` / 引理 `equalizer_mem`

English:
lemma equalizer_mem
  given: {U V} (f₁ f₂ : U ⟶ V) (e : G.map f₁ = G.map f₂)
  proof: letI := IsDenseSubsite.isLocallyFaithful J K G
  IsDenseSubsite.functorPushforward_mem_iff.mp (G.functorPushforward_equalizer_mem K f₁ f₂ e)

中文:
引理 equalizer_mem
  条件: {U V} (f₁ f₂ : U ⟶ V) (e : G.map f₁ = G.map f₂)
  证明: letI := IsDenseSubsite.isLocallyFaithful J K G
  IsDenseSubsite.functorPushforward_mem_iff.mp (G.functorPushforward_equalizer_mem K f₁ f₂ e)

Depends on / 依赖: G.functorPushforward_equalizer_mem, IsDenseSubsite, IsDenseSubsite.functorPushforward_mem_iff.mp, IsDenseSubsite.isLocallyFaithful, functorPushforward_equalizer_mem, functorPushforward_mem_iff, isLocallyFaithful
-/
lemma equalizer_mem {U V} (f₁ f₂ : U ⟶ V) (e : G.map f₁ = G.map f₂) :
    Sieve.equalizer f₁ f₂ in J _ :=
  letI := IsDenseSubsite.isLocallyFaithful J K G
  IsDenseSubsite.functorPushforward_mem_iff.mp (G.functorPushforward_equalizer_mem K f₁ f₂ e)

variable {J} (F : Sheaf J A)

set_option backward.defeqAttrib.useBackward true in
/--
lemma `map_eq_of_eq` / 引理 `map_eq_of_eq`

English:
lemma map_eq_of_eq
  statement: {X Y : C} (f₁ f₂ : X ⟶ Y)
  proof: Presheaf.IsSheaf.hom_ext F.property
    ⟨_, IsDenseSubsite.equalizer_mem J K G _ _ h⟩ _ _ (by
      rintro ⟨W₀, a, ha⟩
      dsimp at ha ⊢
      simp only [← Functor.map_comp, ← op_comp, ha])

中文:
引理 map_eq_of_eq
  结论: {X Y : C} (f₁ f₂ : X ⟶ Y)
  证明: Presheaf.IsSheaf.hom_ext F.property
    ⟨_, IsDenseSubsite.equalizer_mem J K G _ _ h⟩ _ _ (by
      rintro ⟨W₀, a, ha⟩
      dsimp at ha ⊢
      simp only [← Functor.map_comp, ← op_comp, ha])

Depends on / 依赖: F.property, Functor, Functor.map_comp, IsDenseSubsite, IsDenseSubsite.equalizer_mem, IsSheaf, Presheaf, Presheaf.IsSheaf.hom_ext, equalizer_mem, hom_ext, map_comp, op_comp, property
-/
lemma map_eq_of_eq {X Y : C} (f₁ f₂ : X ⟶ Y)
    (h : G.map f₁ = G.map f₂) :
    F.obj.map f₁.op = F.obj.map f₂.op :=
  Presheaf.IsSheaf.hom_ext F.property
    ⟨_, IsDenseSubsite.equalizer_mem J K G _ _ h⟩ _ _ (by
      rintro ⟨W₀, a, ha⟩
      dsimp at ha ⊢
      simp only [← Functor.map_comp, ← op_comp, ha])

/--
Definition of `mapPreimage` / `mapPreimage` 的定义

English:
definition mapPreimage
  signature: {X Y : C} (f : G.obj X ⟶ G.obj Y)
  body: F.property.amalgamate
    ⟨_, imageSieve_mem J K G f⟩ (fun ⟨W₀, a, ha⟩ => F.obj.map ha.choose.op) (by
      rintro ⟨W₀, a, ha⟩ ⟨W₀', a', ha'⟩ ⟨T₀, p₁, p₂, fac⟩
      rw [← Functor.map_comp]; rw [← Functor.map_comp]; rw [← op_comp]; rw [← op_comp]
      apply map_eq_of_eq K G
      rw [Functor.map_comp]; rw [Functor.map_comp]; rw [ha.choose_spec]; rw [ha'.choose_spec]; rw [← Functor.map_comp_assoc]; rw [← Functor.map_comp_assoc]; rw [fac])

中文:
定义 mapPreimage
  签名: {X Y : C} (f : G.obj X ⟶ G.obj Y)
  定义体: F.property.amalgamate
    ⟨_, imageSieve_mem J K G f⟩ (fun ⟨W₀, a, ha⟩ => F.obj.map ha.choose.op) (by
      rintro ⟨W₀, a, ha⟩ ⟨W₀', a', ha'⟩ ⟨T₀, p₁, p₂, fac⟩
      rw [← Functor.map_comp]; rw [← Functor.map_comp]; rw [← op_comp]; rw [← op_comp]
      apply map_eq_of_eq K G
      rw [Functor.map_comp]; rw [Functor.map_comp]; rw [ha.choose_spec]; rw [ha'.choose_spec]; rw [← Functor.map_comp_assoc]; rw [← Functor.map_comp_assoc]; rw [fac])

Depends on / 依赖: F.obj.map, F.property.amalgamate, Functor, Functor.map_comp, Functor.map_comp_assoc, amalgamate, choose_spec, ha.choose.op, ha.choose_spec, imageSieve_mem, map_comp, map_comp_assoc, map_eq_of_eq, op_comp, property
-/
noncomputable def mapPreimage {X Y : C} (f : G.obj X ⟶ G.obj Y) :
    F.obj.obj (op Y) ⟶ F.obj.obj (op X) :=
  F.property.amalgamate
    ⟨_, imageSieve_mem J K G f⟩ (fun ⟨W₀, a, ha⟩ => F.obj.map ha.choose.op) (by
      rintro ⟨W₀, a, ha⟩ ⟨W₀', a', ha'⟩ ⟨T₀, p₁, p₂, fac⟩
      rw [← Functor.map_comp]; rw [← Functor.map_comp]; rw [← op_comp]; rw [← op_comp]
      apply map_eq_of_eq K G
      rw [Functor.map_comp]; rw [Functor.map_comp]; rw [ha.choose_spec]; rw [ha'.choose_spec]; rw [← Functor.map_comp_assoc]; rw [← Functor.map_comp_assoc]; rw [fac])

/--
lemma `mapPreimage_map_of_fac` / 引理 `mapPreimage_map_of_fac`

English:
lemma mapPreimage_map_of_fac
  statement: {X Y Z : C} (f : G.obj X ⟶ G.obj Y)
  proof: Presheaf.IsSheaf.hom_ext F.property
    ⟨_, J.pullback_stable p (imageSieve_mem J K G f)⟩ _ _ (by
      rintro ⟨W₀, a, ha⟩
      dsimp at ha ⊢
      rw [Category.assoc]; rw [← Functor.map_comp]; rw [← op_comp]; rw [mapPreimage]
      rw [F.2.amalgamate_map ⟨_]; rw [imageSieve_mem J K G f⟩
        (fun ⟨W₀]; rw [a]; rw [ha⟩ => F.obj.map ha.choose.op) _ ⟨W₀]; rw [a ≫ p]; rw [ha⟩]; rw [← Functor.map_comp]; rw [← op_comp]
      apply map_eq_of_eq K G
      rw [ha.choose_spec]; rw [Functor.map_comp_assoc]; rw [Functor.map_comp]; rw [fac])

中文:
引理 mapPreimage_map_of_fac
  结论: {X Y Z : C} (f : G.obj X ⟶ G.obj Y)
  证明: Presheaf.IsSheaf.hom_ext F.property
    ⟨_, J.pullback_stable p (imageSieve_mem J K G f)⟩ _ _ (by
      rintro ⟨W₀, a, ha⟩
      dsimp at ha ⊢
      rw [Category.assoc]; rw [← Functor.map_comp]; rw [← op_comp]; rw [mapPreimage]
      rw [F.2.amalgamate_map ⟨_]; rw [imageSieve_mem J K G f⟩
        (fun ⟨W₀]; rw [a]; rw [ha⟩ => F.obj.map ha.choose.op) _ ⟨W₀]; rw [a ≫ p]; rw [ha⟩]; rw [← Functor.map_comp]; rw [← op_comp]
      apply map_eq_of_eq K G
      rw [ha.choose_spec]; rw [Functor.map_comp_assoc]; rw [Functor.map_comp]; rw [fac])

Depends on / 依赖: Category, Category.assoc, F.obj.map, F.property, Functor, Functor.map_comp, Functor.map_comp_assoc, IsSheaf, J.pullback_stable, Presheaf, Presheaf.IsSheaf.hom_ext, amalgamate_map, choose_spec, ha.choose.op, ha.choose_spec, hom_ext, imageSieve_mem, mapPreimage, map_comp, map_comp_assoc
-/
lemma mapPreimage_map_of_fac {X Y Z : C} (f : G.obj X ⟶ G.obj Y)
    (p : Z ⟶ X) (g : Z ⟶ Y) (fac : G.map p ≫ f = G.map g) :
    mapPreimage K G F f ≫ F.obj.map p.op = F.obj.map g.op :=
  Presheaf.IsSheaf.hom_ext F.property
    ⟨_, J.pullback_stable p (imageSieve_mem J K G f)⟩ _ _ (by
      rintro ⟨W₀, a, ha⟩
      dsimp at ha ⊢
      rw [Category.assoc]; rw [← Functor.map_comp]; rw [← op_comp]; rw [mapPreimage]
      rw [F.2.amalgamate_map ⟨_]; rw [imageSieve_mem J K G f⟩
        (fun ⟨W₀]; rw [a]; rw [ha⟩ => F.obj.map ha.choose.op) _ ⟨W₀]; rw [a ≫ p]; rw [ha⟩]; rw [← Functor.map_comp]; rw [← op_comp]
      apply map_eq_of_eq K G
      rw [ha.choose_spec]; rw [Functor.map_comp_assoc]; rw [Functor.map_comp]; rw [fac])

/--
lemma `mapPreimage_of_eq` / 引理 `mapPreimage_of_eq`

English:
lemma mapPreimage_of_eq
  statement: {X Y : C} (f : G.obj X ⟶ G.obj Y)
  proof: by
  simpa using mapPreimage_map_of_fac K G F f (𝟙 _) g (by simpa using h.symm)

@[simp]

中文:
引理 mapPreimage_of_eq
  结论: {X Y : C} (f : G.obj X ⟶ G.obj Y)
  证明: by
  simpa using mapPreimage_map_of_fac K G F f (𝟙 _) g (by simpa using h.symm)

@[simp]

Depends on / 依赖: h.symm, mapPreimage_map_of_fac
-/
lemma mapPreimage_of_eq {X Y : C} (f : G.obj X ⟶ G.obj Y)
    (g : X ⟶ Y) (h : G.map g = f) :
    mapPreimage K G F f = F.obj.map g.op := by
  simpa using mapPreimage_map_of_fac K G F f (𝟙 _) g (by simpa using h.symm)

@[simp]
/--
lemma `mapPreimage_map` / 引理 `mapPreimage_map`

English:
lemma mapPreimage_map
  given: {X Y : C} (f : X ⟶ Y)
  proof: mapPreimage_of_eq K G F (G.map f) f rfl

@[simp]

中文:
引理 mapPreimage_map
  条件: {X Y : C} (f : X ⟶ Y)
  证明: mapPreimage_of_eq K G F (G.map f) f rfl

@[simp]

Depends on / 依赖: G.map, mapPreimage_of_eq
-/
lemma mapPreimage_map {X Y : C} (f : X ⟶ Y) :
    mapPreimage K G F (G.map f) = F.obj.map f.op :=
  mapPreimage_of_eq K G F (G.map f) f rfl

@[simp]
/--
lemma `mapPreimage_id` / 引理 `mapPreimage_id`

English:
lemma mapPreimage_id
  given: (X : C)
  proof: by
  rw [← G.map_id]; rw [mapPreimage_map]; rw [op_id]; rw [map_id]

@[reassoc]

中文:
引理 mapPreimage_id
  条件: (X : C)
  证明: by
  rw [← G.map_id]; rw [mapPreimage_map]; rw [op_id]; rw [map_id]

@[reassoc]

Depends on / 依赖: G.map_id, mapPreimage_map, map_id, op_id
-/
lemma mapPreimage_id (X : C) :
    mapPreimage K G F (𝟙 (G.obj X)) = 𝟙 _ := by
  rw [← G.map_id]; rw [mapPreimage_map]; rw [op_id]; rw [map_id]

@[reassoc]
/--
lemma `mapPreimage_comp` / 引理 `mapPreimage_comp`

English:
lemma mapPreimage_comp
  statement: {X Y Z : C} (f : G.obj X ⟶ G.obj Y)
  proof: Presheaf.IsSheaf.hom_ext F.property
    ⟨_, imageSieve_mem J K G f⟩ _ _ (by
      rintro ⟨T₀, a, ⟨b, fac₁⟩⟩
      apply Presheaf.IsSheaf.hom_ext F.property
        ⟨_, J.pullback_stable b (imageSieve_mem J K G g)⟩
      rintro ⟨U₀, c, ⟨d, fac₂⟩⟩
      dsimp
      simp only [Category.assoc, ← Functor.map_comp, ← op_comp]
      rw [mapPreimage_map_of_fac K G F (f ≫ g) (c ≫ a) d]; rw [mapPreimage_map_of_fac K G F f (c ≫ a) (c ≫ b)]; rw [mapPreimage_map_of_fac K G F g (c ≫ b) d]
      all_goals
        simp only [Functor.map_comp, Category.assoc, fac₁, fac₂])

@[reassoc]

中文:
引理 mapPreimage_comp
  结论: {X Y Z : C} (f : G.obj X ⟶ G.obj Y)
  证明: Presheaf.IsSheaf.hom_ext F.property
    ⟨_, imageSieve_mem J K G f⟩ _ _ (by
      rintro ⟨T₀, a, ⟨b, fac₁⟩⟩
      apply Presheaf.IsSheaf.hom_ext F.property
        ⟨_, J.pullback_stable b (imageSieve_mem J K G g)⟩
      rintro ⟨U₀, c, ⟨d, fac₂⟩⟩
      dsimp
      simp only [Category.assoc, ← Functor.map_comp, ← op_comp]
      rw [mapPreimage_map_of_fac K G F (f ≫ g) (c ≫ a) d]; rw [mapPreimage_map_of_fac K G F f (c ≫ a) (c ≫ b)]; rw [mapPreimage_map_of_fac K G F g (c ≫ b) d]
      all_goals
        simp only [Functor.map_comp, Category.assoc, fac₁, fac₂])

@[reassoc]

Depends on / 依赖: Category, Category.assoc, F.property, Functor, Functor.map_comp, IsSheaf, J.pullback_stable, Presheaf, Presheaf.IsSheaf.hom_ext, all_goals, hom_ext, imageSieve_mem, mapPreimage_map_of_fac, map_comp, op_comp, property, pullback_stable
-/
lemma mapPreimage_comp {X Y Z : C} (f : G.obj X ⟶ G.obj Y)
    (g : G.obj Y ⟶ G.obj Z) :
    mapPreimage K G F (f ≫ g) = mapPreimage K G F g ≫ mapPreimage K G F f :=
  Presheaf.IsSheaf.hom_ext F.property
    ⟨_, imageSieve_mem J K G f⟩ _ _ (by
      rintro ⟨T₀, a, ⟨b, fac₁⟩⟩
      apply Presheaf.IsSheaf.hom_ext F.property
        ⟨_, J.pullback_stable b (imageSieve_mem J K G g)⟩
      rintro ⟨U₀, c, ⟨d, fac₂⟩⟩
      dsimp
      simp only [Category.assoc, ← Functor.map_comp, ← op_comp]
      rw [mapPreimage_map_of_fac K G F (f ≫ g) (c ≫ a) d]; rw [mapPreimage_map_of_fac K G F f (c ≫ a) (c ≫ b)]; rw [mapPreimage_map_of_fac K G F g (c ≫ b) d]
      all_goals
        simp only [Functor.map_comp, Category.assoc, fac₁, fac₂])

@[reassoc]
/--
lemma `mapPreimage_comp_map` / 引理 `mapPreimage_comp_map`

English:
lemma mapPreimage_comp_map
  statement: {X Y Z : C} (f : G.obj X ⟶ G.obj Y)
  proof: by
  rw [mapPreimage_comp]; rw [mapPreimage_map]

中文:
引理 mapPreimage_comp_map
  结论: {X Y Z : C} (f : G.obj X ⟶ G.obj Y)
  证明: by
  rw [mapPreimage_comp]; rw [mapPreimage_map]

Depends on / 依赖: mapPreimage_comp, mapPreimage_map
-/
lemma mapPreimage_comp_map {X Y Z : C} (f : G.obj X ⟶ G.obj Y)
    (g : Z ⟶ X) :
    mapPreimage K G F f ≫ F.obj.map g.op =
      mapPreimage K G F (G.map g ≫ f) := by
  rw [mapPreimage_comp]; rw [mapPreimage_map]

section

variable (J) [IsEquivalence (sheafPushforwardContinuous G A J K)]

section

variable [HasWeakSheafify J A]

variable (A) in
/--
Definition of `sheafifyOfIsEquivalence` / `sheafifyOfIsEquivalence` 的定义

English:
definition sheafifyOfIsEquivalence
  signature: :
  body: (whiskeringLeft _ _ _).obj G.op ⋙ presheafToSheaf J A ⋙
    inv (G.sheafPushforwardContinuous A J K)

中文:
定义 sheafifyOfIsEquivalence
  签名: :
  定义体: (whiskeringLeft _ _ _).obj G.op ⋙ presheafToSheaf J A ⋙
    inv (G.sheafPushforwardContinuous A J K)

Depends on / 依赖: G.op, G.sheafPushforwardContinuous, presheafToSheaf, sheafPushforwardContinuous, whiskeringLeft
-/
noncomputable def sheafifyOfIsEquivalence :
    (Dᵒᵖ ⥤ A) ⥤ Sheaf K A :=
  (whiskeringLeft _ _ _).obj G.op ⋙ presheafToSheaf J A ⋙
    inv (G.sheafPushforwardContinuous A J K)

variable (A) in
/--
Definition of `sheafifyOfIsEquivalenceCompIso` / `sheafifyOfIsEquivalenceCompIso` 的定义

English:
definition sheafifyOfIsEquivalenceCompIso
  signature: :
  body: associator _ _ _ ≪≫ isoWhiskerLeft _ (associator _ _ _) ≪≫
    isoWhiskerLeft _ (isoWhiskerLeft _
      (sheafPushforwardContinuous G A J K).asEquivalence.counitIso ≪≫ Functor.rightUnitor _)

中文:
定义 sheafifyOfIsEquivalenceCompIso
  签名: :
  定义体: associator _ _ _ ≪≫ isoWhiskerLeft _ (associator _ _ _) ≪≫
    isoWhiskerLeft _ (isoWhiskerLeft _
      (sheafPushforwardContinuous G A J K).asEquivalence.counitIso ≪≫ Functor.rightUnitor _)

Depends on / 依赖: Functor, Functor.rightUnitor, asEquivalence, asEquivalence.counitIso, associator, counitIso, isoWhiskerLeft, rightUnitor, sheafPushforwardContinuous
-/
noncomputable def sheafifyOfIsEquivalenceCompIso :
    sheafifyOfIsEquivalence J K G A ⋙ G.sheafPushforwardContinuous A J K ≅
      (whiskeringLeft _ _ _).obj G.op ⋙ presheafToSheaf J A :=
  associator _ _ _ ≪≫ isoWhiskerLeft _ (associator _ _ _) ≪≫
    isoWhiskerLeft _ (isoWhiskerLeft _
      (sheafPushforwardContinuous G A J K).asEquivalence.counitIso ≪≫ Functor.rightUnitor _)

/--
Definition of `sheafifyHomEquivOfIsEquivalence` / `sheafifyHomEquivOfIsEquivalence` 的定义

English:
definition sheafifyHomEquivOfIsEquivalence
  body: haveI := IsDenseSubsite.isLocallyFull J K G
  haveI := IsDenseSubsite.isCoverDense J K G
  ((G.sheafPushforwardContinuous A J K).asEquivalence.symm.toAdjunction.homEquiv _ _).trans
    (((sheafificationAdjunction J A).homEquiv _ _).trans IsCoverDense.restrictHomEquivHom)

中文:
定义 sheafifyHomEquivOfIsEquivalence
  定义体: haveI := IsDenseSubsite.isLocallyFull J K G
  haveI := IsDenseSubsite.isCoverDense J K G
  ((G.sheafPushforwardContinuous A J K).asEquivalence.symm.toAdjunction.homEquiv _ _).trans
    (((sheafificationAdjunction J A).homEquiv _ _).trans IsCoverDense.restrictHomEquivHom)

Depends on / 依赖: G.sheafPushforwardContinuous, IsCoverDense, IsCoverDense.restrictHomEquivHom, IsDenseSubsite, IsDenseSubsite.isCoverDense, IsDenseSubsite.isLocallyFull, asEquivalence, asEquivalence.symm.toAdjunction.homEquiv, homEquiv, isCoverDense, isLocallyFull, restrictHomEquivHom, sheafPushforwardContinuous, sheafificationAdjunction, toAdjunction
-/
noncomputable def sheafifyHomEquivOfIsEquivalence
    {P : Dᵒᵖ ⥤ A} {Q : Sheaf K A} :
    ((sheafifyOfIsEquivalence J K G A).obj P ⟶ Q) ≃ (P ⟶ Q.obj) :=
  haveI := IsDenseSubsite.isLocallyFull J K G
  haveI := IsDenseSubsite.isCoverDense J K G
  ((G.sheafPushforwardContinuous A J K).asEquivalence.symm.toAdjunction.homEquiv _ _).trans
    (((sheafificationAdjunction J A).homEquiv _ _).trans IsCoverDense.restrictHomEquivHom)

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/--
lemma `sheafifyHomEquivOfIsEquivalence_naturality_left` / 引理 `sheafifyHomEquivOfIsEquivalence_naturality_left`

English:
lemma sheafifyHomEquivOfIsEquivalence_naturality_left
  proof: by
  have := IsDenseSubsite.isLocallyFull J K G
  have := IsDenseSubsite.isCoverDense J K G
  let adj₁ := (G.sheafPushforwardContinuous A J K).asEquivalence.symm.toAdjunction
  let adj₂ := sheafificationAdjunction J A
  change IsCoverDense.restrictHomEquivHom (adj₂.homEquiv _ _ (adj₁.homEquiv _ _
    ((sheafifyOfIsEquivalence J K G A).map f ≫ g))) =
      f ≫ IsCoverDense.restrictHomEquivHom (adj₂.homEquiv _ _ (adj₁.homEquiv _ _ g))
  rw [← IsCoverDense.restrictHomEquivHom_naturality_left]
  congr 2
  trans adj₂.homEquiv _ _ ((presheafToSheaf J A).map (G.op.whiskerLeft f) ≫
    (adj₁.homEquiv _ _) g)
  · congr 1
    apply adj₁.homEquiv_naturality_left
  · apply adj₂.homEquiv_naturality_left

中文:
引理 sheafifyHomEquivOfIsEquivalence_naturality_left
  证明: by
  have := IsDenseSubsite.isLocallyFull J K G
  have := IsDenseSubsite.isCoverDense J K G
  let adj₁ := (G.sheafPushforwardContinuous A J K).asEquivalence.symm.toAdjunction
  let adj₂ := sheafificationAdjunction J A
  change IsCoverDense.restrictHomEquivHom (adj₂.homEquiv _ _ (adj₁.homEquiv _ _
    ((sheafifyOfIsEquivalence J K G A).map f ≫ g))) =
      f ≫ IsCoverDense.restrictHomEquivHom (adj₂.homEquiv _ _ (adj₁.homEquiv _ _ g))
  rw [← IsCoverDense.restrictHomEquivHom_naturality_left]
  congr 2
  trans adj₂.homEquiv _ _ ((presheafToSheaf J A).map (G.op.whiskerLeft f) ≫
    (adj₁.homEquiv _ _) g)
  · congr 1
    apply adj₁.homEquiv_naturality_left
  · apply adj₂.homEquiv_naturality_left

Depends on / 依赖: G.sheafPushforwardContinuous, IsCoverDense, IsCoverDense.restrictHomEquivHom, IsCoverDense.restrictHomEquivHom_naturality_left, IsDenseSubsite, IsDenseSubsite.isCoverDense, IsDenseSubsite.isLocallyFull, asEquivalence, asEquivalence.symm.toAdjunction, homEquiv, isCoverDense, isLocallyFull, restrictHomEquivHom, restrictHomEquivHom_naturality_left, sheafPushforwardContinuous, sheafificationAdjunction, sheafifyOfIsEquivalence, toAdjunction
-/
lemma sheafifyHomEquivOfIsEquivalence_naturality_left
    {P₁ P₂ : Dᵒᵖ ⥤ A} (f : P₁ ⟶ P₂) {Q : Sheaf K A}
    (g : (sheafifyOfIsEquivalence J K G A).obj P₂ ⟶ Q) :
      sheafifyHomEquivOfIsEquivalence J K G
        ((sheafifyOfIsEquivalence J K G A).map f ≫ g) =
        f ≫ sheafifyHomEquivOfIsEquivalence J K G g := by
  have := IsDenseSubsite.isLocallyFull J K G
  have := IsDenseSubsite.isCoverDense J K G
  let adj₁ := (G.sheafPushforwardContinuous A J K).asEquivalence.symm.toAdjunction
  let adj₂ := sheafificationAdjunction J A
  change IsCoverDense.restrictHomEquivHom (adj₂.homEquiv _ _ (adj₁.homEquiv _ _
    ((sheafifyOfIsEquivalence J K G A).map f ≫ g))) =
      f ≫ IsCoverDense.restrictHomEquivHom (adj₂.homEquiv _ _ (adj₁.homEquiv _ _ g))
  rw [← IsCoverDense.restrictHomEquivHom_naturality_left]
  congr 2
  trans adj₂.homEquiv _ _ ((presheafToSheaf J A).map (G.op.whiskerLeft f) ≫
    (adj₁.homEquiv _ _) g)
  · congr 1
    apply adj₁.homEquiv_naturality_left
  · apply adj₂.homEquiv_naturality_left

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/--
lemma `sheafifyHomEquivOfIsEquivalence_naturality_right` / 引理 `sheafifyHomEquivOfIsEquivalence_naturality_right`

English:
lemma sheafifyHomEquivOfIsEquivalence_naturality_right
  proof: by
  have := IsDenseSubsite.isLocallyFull J K G
  have := IsDenseSubsite.isCoverDense J K G
  let adj₁ := (G.sheafPushforwardContinuous A J K).asEquivalence.symm.toAdjunction
  let adj₂ := sheafificationAdjunction J A
  change IsCoverDense.restrictHomEquivHom (adj₂.homEquiv _ _ (adj₁.homEquiv _ _ (f ≫ g))) =
    IsCoverDense.restrictHomEquivHom (adj₂.homEquiv _ _ (adj₁.homEquiv _ _ f)) ≫ g.hom
  rw [adj₁.homEquiv_naturality_right]; rw [adj₂.homEquiv_naturality_right]
  apply IsCoverDense.restrictHomEquivHom_naturality_right

中文:
引理 sheafifyHomEquivOfIsEquivalence_naturality_right
  证明: by
  have := IsDenseSubsite.isLocallyFull J K G
  have := IsDenseSubsite.isCoverDense J K G
  let adj₁ := (G.sheafPushforwardContinuous A J K).asEquivalence.symm.toAdjunction
  let adj₂ := sheafificationAdjunction J A
  change IsCoverDense.restrictHomEquivHom (adj₂.homEquiv _ _ (adj₁.homEquiv _ _ (f ≫ g))) =
    IsCoverDense.restrictHomEquivHom (adj₂.homEquiv _ _ (adj₁.homEquiv _ _ f)) ≫ g.hom
  rw [adj₁.homEquiv_naturality_right]; rw [adj₂.homEquiv_naturality_right]
  apply IsCoverDense.restrictHomEquivHom_naturality_right

Depends on / 依赖: G.sheafPushforwardContinuous, IsCoverDense, IsCoverDense.restrictHomEquivHom, IsCoverDense.restrictHomEquivHom_natur, IsDenseSubsite, IsDenseSubsite.isCoverDense, IsDenseSubsite.isLocallyFull, asEquivalence, asEquivalence.symm.toAdjunction, g.hom, homEquiv, homEquiv_naturality_right, isCoverDense, isLocallyFull, restrictHomEquivHom, restrictHomEquivHom_natur, sheafPushforwardContinuous, sheafificationAdjunction, toAdjunction
-/
lemma sheafifyHomEquivOfIsEquivalence_naturality_right
    {P : Dᵒᵖ ⥤ A} {Q₁ Q₂ : Sheaf K A}
    (f : (sheafifyOfIsEquivalence J K G A).obj P ⟶ Q₁) (g : Q₁ ⟶ Q₂) :
      sheafifyHomEquivOfIsEquivalence J K G (f ≫ g) =
        sheafifyHomEquivOfIsEquivalence J K G f ≫ g.hom := by
  have := IsDenseSubsite.isLocallyFull J K G
  have := IsDenseSubsite.isCoverDense J K G
  let adj₁ := (G.sheafPushforwardContinuous A J K).asEquivalence.symm.toAdjunction
  let adj₂ := sheafificationAdjunction J A
  change IsCoverDense.restrictHomEquivHom (adj₂.homEquiv _ _ (adj₁.homEquiv _ _ (f ≫ g))) =
    IsCoverDense.restrictHomEquivHom (adj₂.homEquiv _ _ (adj₁.homEquiv _ _ f)) ≫ g.hom
  rw [adj₁.homEquiv_naturality_right]; rw [adj₂.homEquiv_naturality_right]
  apply IsCoverDense.restrictHomEquivHom_naturality_right

variable (A)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `sheafifyAdjunctionOfIsEquivalence` / `sheafifyAdjunctionOfIsEquivalence` 的定义

English:
definition sheafifyAdjunctionOfIsEquivalence
  signature: :
  body: Adjunction.mkOfHomEquiv
    { homEquiv := fun P Q => sheafifyHomEquivOfIsEquivalence J K G
      homEquiv_naturality_left_symm := fun {P₁ P₂ Q} f g =>
        (sheafifyHomEquivOfIsEquivalence J K G).injective (by
          simp [sheafifyHomEquivOfIsEquivalence_naturality_left _ _ _ f])
      homEquiv_naturality_right :=
        sheafifyHomEquivOfIsEquivalence_naturality_right J K G }

include G K in

中文:
定义 sheafifyAdjunctionOfIsEquivalence
  签名: :
  定义体: Adjunction.mkOfHomEquiv
    { homEquiv := fun P Q => sheafifyHomEquivOfIsEquivalence J K G
      homEquiv_naturality_left_symm := fun {P₁ P₂ Q} f g =>
        (sheafifyHomEquivOfIsEquivalence J K G).injective (by
          simp [sheafifyHomEquivOfIsEquivalence_naturality_left _ _ _ f])
      homEquiv_naturality_right :=
        sheafifyHomEquivOfIsEquivalence_naturality_right J K G }

include G K in

Depends on / 依赖: Adjunction, Adjunction.mkOfHomEquiv, homEquiv, homEquiv_naturality_left_symm, homEquiv_naturality_right, injective, mkOfHomEquiv, sheafifyHomEquivOfIsEquivalence, sheafifyHomEquivOfIsEquivalence_naturality_left, sheafifyHomEquivOfIsEquivalence_naturality_right
-/
noncomputable def sheafifyAdjunctionOfIsEquivalence :
    sheafifyOfIsEquivalence J K G A ⊣ sheafToPresheaf K A :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun P Q => sheafifyHomEquivOfIsEquivalence J K G
      homEquiv_naturality_left_symm := fun {P₁ P₂ Q} f g =>
        (sheafifyHomEquivOfIsEquivalence J K G).injective (by
          simp [sheafifyHomEquivOfIsEquivalence_naturality_left _ _ _ f])
      homEquiv_naturality_right :=
        sheafifyHomEquivOfIsEquivalence_naturality_right J K G }

include G K in
/--
lemma `hasWeakSheafify_of_isEquivalence` / 引理 `hasWeakSheafify_of_isEquivalence`

English:
lemma hasWeakSheafify_of_isEquivalence
  proof: ⟨_, ⟨sheafifyAdjunctionOfIsEquivalence J K G A⟩⟩

中文:
引理 hasWeakSheafify_of_isEquivalence
  证明: ⟨_, ⟨sheafifyAdjunctionOfIsEquivalence J K G A⟩⟩

Depends on / 依赖: sheafifyAdjunctionOfIsEquivalence
-/
lemma hasWeakSheafify_of_isEquivalence :
    HasWeakSheafify K A := ⟨_, ⟨sheafifyAdjunctionOfIsEquivalence J K G A⟩⟩

end

open Limits in
include G in
/--
lemma `hasSheafify_of_isEquivalence` / 引理 `hasSheafify_of_isEquivalence`

English:
lemma hasSheafify_of_isEquivalence
  given: [HasSheafify J A] [HasFiniteLimits A]
  proof: by
  have : PreservesFiniteLimits (presheafToSheaf J A ⋙
    (G.sheafPushforwardContinuous A J K).inv) := by
    apply comp_preservesFiniteLimits
  have : PreservesFiniteLimits (sheafifyOfIsEquivalence J K G A) := by
    apply comp_preservesFiniteLimits
  exact HasSheafify.mk' _ _ (sheafifyAdjunctionOfIsEquivalence J K G A)

中文:
引理 hasSheafify_of_isEquivalence
  条件: [有Sheafify J A] [有有限极限 A]
  证明: by
  have : PreservesFiniteLimits (presheafToSheaf J A ⋙
    (G.sheafPushforwardContinuous A J K).inv) := by
    apply comp_preservesFiniteLimits
  have : PreservesFiniteLimits (sheafifyOfIsEquivalence J K G A) := by
    apply comp_preservesFiniteLimits
  exact HasSheafify.mk' _ _ (sheafifyAdjunctionOfIsEquivalence J K G A)

Depends on / 依赖: G.sheafPushforwardContinuous, HasSheafify, HasSheafify.mk, PreservesFiniteLimits, comp_preservesFiniteLimits, presheafToSheaf, sheafPushforwardContinuous, sheafifyAdjunctionOfIsEquivalence, sheafifyOfIsEquivalence
-/
lemma hasSheafify_of_isEquivalence [HasSheafify J A] [HasFiniteLimits A] :
    HasSheafify K A := by
  have : PreservesFiniteLimits (presheafToSheaf J A ⋙
    (G.sheafPushforwardContinuous A J K).inv) := by
    apply comp_preservesFiniteLimits
  have : PreservesFiniteLimits (sheafifyOfIsEquivalence J K G A) := by
    apply comp_preservesFiniteLimits
  exact HasSheafify.mk' _ _ (sheafifyAdjunctionOfIsEquivalence J K G A)

end

section

variable (J A) [IsEquivalence (sheafPushforwardContinuous G A J K)]

/--
If `G : C ⥤ D` exhibits `(C, J)` as a dense subsite of `(D, K)`, and the
pushforward functor `Sheaf K A ⥤ Sheaf J A` is an equivalence, then this
is the equivalence `Sheaf K A ≌ Sheaf J A`. -/
@[simps! inverse]
/--
Definition of `sheafEquiv` / `sheafEquiv` 的定义

English:
definition sheafEquiv
  signature: : Sheaf J A ≌ Sheaf K A
  body: (sheafPushforwardContinuous G A J K).asEquivalence.symm

中文:
定义 sheafEquiv
  签名: : 层 J A ≌ 层 K A
  定义体: (sheafPushforwardContinuous G A J K).asEquivalence.symm

Depends on / 依赖: asEquivalence, asEquivalence.symm, sheafPushforwardContinuous
-/
noncomputable def sheafEquiv : Sheaf J A ≌ Sheaf K A :=
  (sheafPushforwardContinuous G A J K).asEquivalence.symm

variable [HasWeakSheafify J A] [HasWeakSheafify K A]

/-- The natural isomorphism exhibiting the compatibility of
`IsDenseSubsite.sheafEquiv` with sheafification. -/
noncomputable
/--
Definition of `sheafEquivSheafificationCompatibility` / `sheafEquivSheafificationCompatibility` 的定义

English:
definition sheafEquivSheafificationCompatibility
  signature: :
  body: (sheafifyOfIsEquivalenceCompIso _ _ _ _).symm ≪≫
    isoWhiskerRight
      ((sheafifyAdjunctionOfIsEquivalence J K G A).leftAdjointUniq
        (sheafificationAdjunction K A)) _

中文:
定义 sheafEquivSheafificationCompatibility
  签名: :
  定义体: (sheafifyOfIsEquivalenceCompIso _ _ _ _).symm ≪≫
    isoWhiskerRight
      ((sheafifyAdjunctionOfIsEquivalence J K G A).leftAdjointUniq
        (sheafificationAdjunction K A)) _

Depends on / 依赖: isoWhiskerRight, leftAdjointUniq, sheafificationAdjunction, sheafifyAdjunctionOfIsEquivalence, sheafifyOfIsEquivalenceCompIso
-/
def sheafEquivSheafificationCompatibility :
    (whiskeringLeft _ _ A).obj G.op ⋙ presheafToSheaf J A ≅
      presheafToSheaf K A ⋙ (sheafEquiv J K G A).inverse :=
  (sheafifyOfIsEquivalenceCompIso _ _ _ _).symm ≪≫
    isoWhiskerRight
      ((sheafifyAdjunctionOfIsEquivalence J K G A).leftAdjointUniq
        (sheafificationAdjunction K A)) _

end

end IsDenseSubsite

end Functor

end CategoryTheory
