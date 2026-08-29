/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Preorder
public import Mathlib.CategoryTheory.Presentable.LocallyPresentable
public import Mathlib.Order.Category.PartOrdEmb

/-!
# The κ-accessible category of κ-directed posets

Given a regular cardinal `κ : Cardinal.{u}`, we define the
category `CardinalDirectedPoset κ` of `κ`-directed partially ordered
types (with order embeddings as morphisms), and we show that it is
a `κ`-accessible category.

The notion of `κ`-directed partially ordered type is implemented
using the categorial notion `IsCardinalFiltered`: we may consider
"`κ`-directed" and "`κ`-filtered" as synonyms.

If `κ ≤ κ'` where `κ'` is also a regular cardinal, we characterize
the `κ'`-presentable objects of `CardinalDirectedPoset κ` as
the objects `J` such that the underlying type `J.obj` has
cardinality `< κ'`.

## References
* [Adámek, J. and Rosický, J., *Locally presentable and accessible categories*][Adamek_Rosicky_1994]

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace PartOrdEmb

variable (κ : Cardinal.{u}) [Fact κ.IsRegular]

/--
Definition of `isCardinalFiltered` / `isCardinalFiltered` 的定义

English:
abbreviation isCardinalFiltered
  signature: : ObjectProperty PartOrdEmb.{u}
  body: fun X => IsCardinalFiltered X κ

@[simp]

中文:
缩写 isCardinalFiltered
  签名: : ObjectProperty PartOrdEmb.{u}
  定义体: fun X => IsCardinalFiltered X κ

@[simp]

Depends on / 依赖: IsCardinalFiltered
-/
abbrev isCardinalFiltered : ObjectProperty PartOrdEmb.{u} :=
  fun X => IsCardinalFiltered X κ

@[simp]
/--
lemma `isCardinalFiltered_iff` / 引理 `isCardinalFiltered_iff`

English:
lemma isCardinalFiltered_iff
  given: (X : PartOrdEmb.{u})
  proof: Iff.rfl

中文:
引理 isCardinalFiltered_iff
  条件: (X : PartOrdEmb.{u})
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma isCardinalFiltered_iff (X : PartOrdEmb.{u}) :
    isCardinalFiltered κ X ↔ IsCardinalFiltered X κ := Iff.rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (isCardinalFiltered κ).IsClosedUnderIsomorphisms
  body: .of_equivalence κ (orderIsoOfIso e).equivalence

中文:
实例 :
  签名: (isCardinalFiltered κ).在同构下封闭
  定义体: .of_equivalence κ (orderIsoOfIso e).equivalence

Depends on / 依赖: equivalence, of_equivalence, orderIsoOfIso
-/
instance : (isCardinalFiltered κ).IsClosedUnderIsomorphisms where
  of_iso e _ := .of_equivalence κ (orderIsoOfIso e).equivalence

namespace Limits.CoconePt

variable {κ} {J : Type u} [SmallCategory J] [IsCardinalFiltered J κ]
  {F : J ⥤ PartOrdEmb.{u}} {c : Cocone (F ⋙ forget _)} (hc : IsColimit c)

/--
lemma `isCardinalFiltered_pt` / 引理 `isCardinalFiltered_pt`

English:
lemma isCardinalFiltered_pt
  given: (hF : forall j, IsCardinalFiltered (F.obj j) κ)
  proof: isFiltered_of_isCardinalFiltered J κ
    IsCardinalFiltered (CoconePt hc) κ := by
  have := isFiltered_of_isCardinalFiltered J κ
  refine isCardinalFiltered_preorder _ _ (fun K f hK => ?_)
  rw [← hasCardinalLT_iff_cardinal_mk_lt] at hK
  choose j₀ x₀ hx₀ using fun k => Types.jointly_surjective_of_i

中文:
引理 isCardinalFiltered_pt
  条件: (hF : 对任意 j, 是CardinalFiltered (F.obj j) κ)
  证明: isFiltered_of_isCardinalFiltered J κ
    IsCardinalFiltered (CoconePt hc) κ := by
  have := isFiltered_of_isCardinalFiltered J κ
  refine isCardinalFiltered_preorder _ _ (fun K f hK => ?_)
  rw [← hasCardinalLT_iff_cardinal_mk_lt] at hK
  choose j₀ x₀ hx₀ using fun k => Types.jointly_surjective_of_i

Depends on / 依赖: isFiltered_of_isCardinalFiltered
-/
lemma isCardinalFiltered_pt (hF : forall j, IsCardinalFiltered (F.obj j) κ) :
    haveI := isFiltered_of_isCardinalFiltered J κ
    IsCardinalFiltered (CoconePt hc) κ := by
  have := isFiltered_of_isCardinalFiltered J κ
  refine isCardinalFiltered_preorder _ _ (fun K f hK => ?_)
  rw [← hasCardinalLT_iff_cardinal_mk_lt] at hK
  choose j₀ x₀ hx₀ using fun k => Types.jointly_surjective_of_isColimit hc (f k)
  let j := IsCardinalFiltered.max j₀ hK
  let x₁ (k : K) : F.obj j := F.map (IsCardinalFiltered.toMax j₀ hK k) (x₀ k)
  have hx₁ (k : K) : c.ι.app j (x₁ k) = c.ι.app (j₀ k) (x₀ k) :=
    ConcreteCategory.congr_hom (c.w (IsCardinalFiltered.toMax j₀ hK k)) _
  refine ⟨(cocone hc).ι.app j (IsCardinalFiltered.max x₁ hK),
    fun k => ?_⟩
  rw [← hx₀]; rw [← hx₁]
  exact ((cocone hc).ι.app j).hom.monotone
    (leOfHom (IsCardinalFiltered.toMax x₁ hK k))

end Limits.CoconePt

instance (J : Type u) [SmallCategory J] [IsCardinalFiltered J κ] :
    (isCardinalFiltered κ).IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := by
    have := isFiltered_of_isCardinalFiltered J κ
    rintro X ⟨p⟩
    simp only [(isCardinalFiltered κ).prop_iff_of_iso
      (p.isColimit.coconePointUniqueUpToIso
        (Limits.isColimitCocone (colimit.isColimit (p.diag ⋙ forget PartOrdEmb)))),
      isCardinalFiltered_iff]
    exact Limits.CoconePt.isCardinalFiltered_pt _ p.prop_diag_obj

end PartOrdEmb

namespace CategoryTheory

variable (κ : Cardinal.{u}) [Fact κ.IsRegular]

/--
Definition of `CardinalDirectedPoset` / `CardinalDirectedPoset` 的定义

English:
abbreviation CardinalDirectedPoset
  body: (PartOrdEmb.isCardinalFiltered κ).FullSubcategory

中文:
缩写 CardinalDirectedPoset
  定义体: (PartOrdEmb.isCardinalFiltered κ).FullSubcategory

Depends on / 依赖: FullSubcategory, PartOrdEmb, PartOrdEmb.isCardinalFiltered, isCardinalFiltered
-/
abbrev CardinalDirectedPoset :=
  (PartOrdEmb.isCardinalFiltered κ).FullSubcategory

variable {κ}

/--
Definition of `CardinalDirectedPoset.ι` / `CardinalDirectedPoset.ι` 的定义

English:
abbreviation CardinalDirectedPoset.ι
  signature: : CardinalDirectedPoset κ ⥤ PartOrdEmb
  body: ObjectProperty.ι _

中文:
缩写 CardinalDirectedPoset.ι
  签名: : CardinalDirectedPoset κ ⥤ PartOrdEmb
  定义体: ObjectProperty.ι _

Depends on / 依赖: ObjectProperty
-/
abbrev CardinalDirectedPoset.ι : CardinalDirectedPoset κ ⥤ PartOrdEmb :=
  ObjectProperty.ι _

namespace CardinalDirectedPoset

/--
Definition of `of` / `of` 的定义

English:
abbreviation of
  signature: (J : PartOrdEmb.{u}) [IsCardinalFiltered J κ]
  body: J
  property := inferInstance

中文:
缩写 of
  签名: (J : PartOrdEmb.{u}) [是CardinalFiltered J κ]
  定义体: J
  property := inferInstance
-/
abbrev of (J : PartOrdEmb.{u}) [IsCardinalFiltered J κ] : CardinalDirectedPoset κ where
  obj := J
  property := inferInstance

/--
lemma `Hom.injective` / 引理 `Hom.injective`

English:
lemma Hom.injective
  given: {J₁ J₂ : CardinalDirectedPoset κ} (f : J₁ ⟶ J₂)
  proof: f.hom.injective

中文:
引理 态射.injective
  条件: {J₁ J₂ : CardinalDirectedPoset κ} (f : J₁ ⟶ J₂)
  证明: f.hom.injective

Depends on / 依赖: f.hom.injective, injective
-/
lemma Hom.injective {J₁ J₂ : CardinalDirectedPoset κ} (f : J₁ ⟶ J₂) :
    Function.Injective f := f.hom.injective

/--
lemma `Hom.le_iff_le` / 引理 `Hom.le_iff_le`

English:
lemma Hom.le_iff_le
  given: {J₁ J₂ : CardinalDirectedPoset κ} (f : J₁ ⟶ J₂) (x₁ x₂ : J₁.obj)
  proof: f.hom.hom.le_iff_le

中文:
引理 态射.le_iff_le
  条件: {J₁ J₂ : CardinalDirectedPoset κ} (f : J₁ ⟶ J₂) (x₁ x₂ : J₁.obj)
  证明: f.hom.hom.le_iff_le

Depends on / 依赖: f.hom.hom.le_iff_le, le_iff_le
-/
lemma Hom.le_iff_le {J₁ J₂ : CardinalDirectedPoset κ} (f : J₁ ⟶ J₂) (x₁ x₂ : J₁.obj) :
    f x₁ <= f x₂ ↔ x₁ <= x₂ :=
  f.hom.hom.le_iff_le

instance (J : CardinalDirectedPoset κ) : IsCardinalFiltered J.obj κ := J.property

instance (J : CardinalDirectedPoset κ) : IsFiltered J.obj :=
  isFiltered_of_isCardinalFiltered _ κ

instance (J : CardinalDirectedPoset κ) : Nonempty J.obj := IsFiltered.nonempty

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasCardinalFilteredColimits (CardinalDirectedPoset κ) κ
  body: by
    have := isFiltered_of_isCardinalFiltered J κ
    infer_instance

中文:
实例 :
  签名: 有CardinalFilteredColimits (CardinalDirectedPoset κ) κ
  定义体: by
    have := isFiltered_of_isCardinalFiltered J κ
    infer_instance

Depends on / 依赖: infer_instance, isFiltered_of_isCardinalFiltered
-/
instance : HasCardinalFilteredColimits (CardinalDirectedPoset κ) κ where
  hasColimitsOfShape J _ _ := by
    have := isFiltered_of_isCardinalFiltered J κ
    infer_instance

instance (A : Type u) [SmallCategory A] [IsCardinalFiltered A κ] :
    PreservesColimitsOfShape A (forget (CardinalDirectedPoset κ)) := by
  have := isFiltered_of_isCardinalFiltered A κ
  change PreservesColimitsOfShape A (CardinalDirectedPoset.ι ⋙ forget _)
  infer_instance

instance (J : CardinalDirectedPoset κ) (κ' : Cardinal.{u}) [Fact κ'.IsRegular] :
    IsCardinalFiltered (WithTop (J.obj)) κ' :=
  isCardinalFiltered_of_hasTerminal _ _

/--
Definition of `withTop` / `withTop` 的定义

English:
abbreviation withTop
  signature: (J : CardinalDirectedPoset κ)
  body: .of (.of (WithTop J.obj))

中文:
缩写 withTop
  签名: (J : CardinalDirectedPoset κ)
  定义体: .of (.of (WithTop J.obj))

Depends on / 依赖: J.obj, WithTop
-/
abbrev withTop (J : CardinalDirectedPoset κ) : CardinalDirectedPoset κ :=
  .of (.of (WithTop J.obj))

section

variable {J : CardinalDirectedPoset κ} (P : Set J.obj -> Prop)
  [IsDirectedOrder (Subtype P)] [Nonempty (Subtype P)]
  [forall (S : Subtype P), IsCardinalFiltered S.val κ]

set_option backward.defeqAttrib.useBackward true in
/-- Given a predicate `P : Set J.obj → Prop` on the underlying type
of `J : CardinalDirectedPoset κ` such that all the subsets satisfying `P`
are `κ`-filtered, this is the functor `Subtype P ⥤ CardinalDirectedPoset κ`
which sends a subset `S` of `J` satisfying `P` to the induced
partially ordered type `J`, as an object in `CardinalDirectedPoset κ`. -/
@[simps!]
/--
Definition of `functorOfPredicateSet` / `functorOfPredicateSet` 的定义

English:
definition functorOfPredicateSet
  signature: : Subtype P ⥤ CardinalDirectedPoset κ
  body: ObjectProperty.lift _ (PartOrdEmb.functorOfPredicateSet P)
    (fun S => by dsimp; infer_instance)

中文:
定义 functorOfPredicateSet
  签名: : 子类型 P ⥤ CardinalDirectedPoset κ
  定义体: ObjectProperty.lift _ (PartOrdEmb.functorOfPredicateSet P)
    (fun S => by dsimp; infer_instance)

Depends on / 依赖: ObjectProperty, ObjectProperty.lift, PartOrdEmb, PartOrdEmb.functorOfPredicateSet, functorOfPredicateSet, infer_instance
-/
def functorOfPredicateSet : Subtype P ⥤ CardinalDirectedPoset κ :=
  ObjectProperty.lift _ (PartOrdEmb.functorOfPredicateSet P)
    (fun S => by dsimp; infer_instance)

/-- Given a predicate `P : Set J.obj → Prop` on the underlying type
of `J : CardinalDirectedPoset κ` such that all the subsets satisfying `P`
are `κ`-filtered, this is the cocone with point `J` given
by all the inclusions of the subsets satisfying `P`. -/
@[simps]
/--
Definition of `coconeOfPredicateSet` / `coconeOfPredicateSet` 的定义

English:
definition coconeOfPredicateSet
  signature: : Cocone (functorOfPredicateSet P) where
  body: J
  ι.app j := ObjectProperty.homMk ((PartOrdEmb.coconeOfPredicateSet P).ι.app j)

中文:
定义 coconeOfPredicateSet
  签名: : 余锥 (functorOfPredicateSet P) where
  定义体: J
  ι.app j := ObjectProperty.homMk ((PartOrdEmb.coconeOfPredicateSet P).ι.app j)
-/
def coconeOfPredicateSet : Cocone (functorOfPredicateSet P) where
  pt := J
  ι.app j := ObjectProperty.homMk ((PartOrdEmb.coconeOfPredicateSet P).ι.app j)

/--
Definition of `isColimitCoconeOfPredicateSet` / `isColimitCoconeOfPredicateSet` 的定义

English:
definition isColimitCoconeOfPredicateSet
  body: isColimitOfReflects CardinalDirectedPoset.ι
    (PartOrdEmb.isColimitOfPredicateSet P hP)

中文:
定义 isColimitCoconeOfPredicateSet
  定义体: isColimitOfReflects CardinalDirectedPoset.ι
    (PartOrdEmb.isColimitOfPredicateSet P hP)

Depends on / 依赖: CardinalDirectedPoset, PartOrdEmb, PartOrdEmb.isColimitOfPredicateSet, isColimitOfPredicateSet, isColimitOfReflects
-/
noncomputable def isColimitCoconeOfPredicateSet
    (hP : forall (a : J.obj), exists (S : Set J.obj), P S ∧ a in S) :
    IsColimit (coconeOfPredicateSet P) :=
  isColimitOfReflects CardinalDirectedPoset.ι
    (PartOrdEmb.isColimitOfPredicateSet P hP)

end

variable (κ) in
/--
Definition of `hasCardinalLTWithTerminal` / `hasCardinalLTWithTerminal` 的定义

English:
definition hasCardinalLTWithTerminal
  signature: : ObjectProperty (CardinalDirectedPoset κ)
  body: fun J => HasCardinalLT J.obj κ ∧ HasTerminal J.obj

中文:
定义 hasCardinalLTWithTerminal
  签名: : ObjectProperty (CardinalDirectedPoset κ)
  定义体: fun J => HasCardinalLT J.obj κ ∧ HasTerminal J.obj

Depends on / 依赖: HasCardinalLT, HasTerminal, J.obj
-/
def hasCardinalLTWithTerminal : ObjectProperty (CardinalDirectedPoset κ) :=
  fun J => HasCardinalLT J.obj κ ∧ HasTerminal J.obj

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ObjectProperty.EssentiallySmall.{u} (hasCardinalLTWithTerminal κ)
  body: by
    obtain ⟨X, hX⟩ : exists (X : Type u), Cardinal.mk X = κ := ⟨κ.ord.ToType, by simp⟩
    let α : Type u := Σ (S : Set X) (_ : PartialOrder S),
      ULift.{u} (PLift (IsCardinalFiltered S κ))
    let (a : α) : PartialOrder a.1 := a.2.1
    let ι (a : α) : CardinalDirectedPoset κ :=
      { obj 

中文:
实例 :
  签名: ObjectProperty.EssentiallySmall.{u} (hasCardinalLTWithTerminal κ)
  定义体: by
    obtain ⟨X, hX⟩ : exists (X : Type u), Cardinal.mk X = κ := ⟨κ.ord.ToType, by simp⟩
    let α : Type u := Σ (S : Set X) (_ : PartialOrder S),
      ULift.{u} (PLift (IsCardinalFiltered S κ))
    let (a : α) : PartialOrder a.1 := a.2.1
    let ι (a : α) : CardinalDirectedPoset κ :=
      { obj 

Depends on / 依赖: Cardinal, Cardinal.mk, CardinalDirectedPoset, IsCardinalFiltered, J.obj, PartialOrder, ToType, down.down, hasCardinalLT_iff_cardinal_mk_lt, ord.ToType, property
-/
instance : ObjectProperty.EssentiallySmall.{u} (hasCardinalLTWithTerminal κ) where
  exists_small_le' := by
    obtain ⟨X, hX⟩ : exists (X : Type u), Cardinal.mk X = κ := ⟨κ.ord.ToType, by simp⟩
    let α : Type u := Σ (S : Set X) (_ : PartialOrder S),
      ULift.{u} (PLift (IsCardinalFiltered S κ))
    let (a : α) : PartialOrder a.1 := a.2.1
    let ι (a : α) : CardinalDirectedPoset κ :=
      { obj := .of a.1
        property := a.2.2.down.down }
    refine ⟨.ofObj ι, inferInstance, fun J ⟨hJ, _⟩ => ?_⟩
    obtain ⟨f⟩ : Cardinal.mk J.obj <= Cardinal.mk X := by
      simpa [hX] using ((hasCardinalLT_iff_cardinal_mk_lt _ _).1 hJ).le
    let e := Equiv.ofInjective _ f.injective
    let : PartialOrder (Set.range f) := PartialOrder.lift _ e.symm.injective
    let e' : Set.range f ≃o J.obj := { toEquiv := e.symm, map_rel_iff' := by rfl }
    exact ⟨_, ⟨⟨Set.range f, inferInstance,
      ⟨⟨IsCardinalFiltered.of_equivalence κ e'.symm.equivalence⟩⟩⟩⟩,
        ⟨CardinalDirectedPoset.ι.preimageIso (PartOrdEmb.Iso.mk (by exact e'.symm))⟩⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `isCardinalPresentable_of_hasCardinalLT_of_le` / 引理 `isCardinalPresentable_of_hasCardinalLT_of_le`

English:
lemma isCardinalPresentable_of_hasCardinalLT_of_le
  statement: (J : CardinalDirectedPoset κ)
  proof: ⟨fun {F} => ⟨fun {c} hc => ⟨by
  · have := isFiltered_of_isCardinalFiltered A κ'
    have := IsCardinalFiltered.of_le A h
    replace hc := isColimitOfPreserves (forget _) hc
    refine Types.FilteredColimit.isColimitOf' _ _ (fun f => ?_) (fun j f g h => ?_)
    · dsimp at f
      choose j g hg usin

中文:
引理 isCardinalPresentable_of_hasCardinalLT_of_le
  结论: (J : CardinalDirectedPoset κ)
  证明: ⟨fun {F} => ⟨fun {c} hc => ⟨by
  · have := isFiltered_of_isCardinalFiltered A κ'
    have := IsCardinalFiltered.of_le A h
    replace hc := isColimitOfPreserves (forget _) hc
    refine Types.FilteredColimit.isColimitOf' _ _ (fun f => ?_) (fun j f g h => ?_)
    · dsimp at f
      choose j g hg usin

Depends on / 依赖: F.map, F.obj, FilteredColimit, IsCardinalFiltered, IsCardinalFiltered.max, IsCardinalFiltered.of_le, IsCardinalFiltered.toMax, J.obj, Types.FilteredColimit.isColimitOf, Types.jointly_surjective_of_isColimit, forget, isColimitOf, isColimitOfPreserves, isFiltered_of_isCardinalFiltered, jointly_surjective_of_isColimit, of_le, replace
-/
lemma isCardinalPresentable_of_hasCardinalLT_of_le (J : CardinalDirectedPoset κ)
    {κ' : Cardinal.{u}} [Fact κ'.IsRegular] (hJ : HasCardinalLT J.obj κ') (h : κ <= κ') :
    IsCardinalPresentable J κ' where
  preservesColimitOfShape A _ _ := ⟨fun {F} => ⟨fun {c} hc => ⟨by
  · have := isFiltered_of_isCardinalFiltered A κ'
    have := IsCardinalFiltered.of_le A h
    replace hc := isColimitOfPreserves (forget _) hc
    refine Types.FilteredColimit.isColimitOf' _ _ (fun f => ?_) (fun j f g h => ?_)
    · dsimp at f
      choose j g hg using fun (x : J.obj) => Types.jointly_surjective_of_isColimit hc (f x)
      let m := IsCardinalFiltered.max j hJ
      let φ (x : J.obj) : (F.obj m).obj := F.map (IsCardinalFiltered.toMax j hJ x) (g x)
      have hφ (x : J.obj) : f x = c.ι.app _ (φ x) := by
        dsimp [φ]
        rw [← hg]; rw [← ConcreteCategory.comp_apply]; rw [c.w]
        rfl
      refine ⟨m,
        ObjectProperty.homMk (PartOrdEmb.ofHom
          { toFun := φ
            inj' x y h := Hom.injective f (by simpa [hφ])
            map_rel_iff' {x y} := ?_ }), ?_⟩
      · simp [← Hom.le_iff_le f, hφ]
      · dsimp
        ext x
        trans c.ι.app (j x) (g x)
        · exact (hg x).symm
        · exact (ConcreteCategory.congr_hom (c.w (IsCardinalFiltered.toMax j hJ x)).symm (g x))
    · choose k a hk using fun (x : J.obj) =>
        (Types.FilteredColimit.isColimit_eq_iff' hc _ _).1 (ConcreteCategory.congr_hom h x)
      dsimp at f g h k a hk ⊢
      obtain ⟨l, b, c, hl⟩ : exists (l : A) (c : j ⟶ l) (b : forall x, k x ⟶ l),
          forall x, a x ≫ b x = c := by
        let φ (x : J.obj) : j ⟶ IsCardinalFiltered.max k hJ :=
          a x ≫ IsCardinalFiltered.toMax k hJ x
        exact ⟨IsCardinalFiltered.coeq φ hJ,
          IsCardinalFiltered.toCoeq φ hJ,
          fun x => IsCardinalFiltered.toMax k hJ x ≫ IsCardinalFiltered.coeqHom φ hJ,
          fun x => by simpa [φ] using IsCardinalFiltered.coeq_condition φ hJ x⟩
      refine ⟨l, b, ?_⟩
      ext x
      simpa only [← hl x, Functor.map_comp, ObjectProperty.FullSubcategory.comp_hom,
        PartOrdEmb.hom_comp, RelEmbedding.coe_trans, Function.comp_apply]
          using! congr_arg _ (hk x)⟩⟩⟩

section

variable (J : CardinalDirectedPoset κ)

-- `@[nolint unusedArguments]` allows to setup some instances which uses
-- the fact that `κ'` is regular.
/-- Given `J : CardinalFilteredPoset κ` and a regular cardinal `κ'`,
this is the predicate on `Set J.withTop.obj` that is satisfied by
subsets that are of cardinality `< κ'` and contain `⊤`. -/
@[nolint unusedArguments]
/--
Definition of `PropSetWithTop` / `PropSetWithTop` 的定义

English:
definition PropSetWithTop
  signature: (κ' : Cardinal.{u}) [Fact κ'.IsRegular]
  body: HasCardinalLT S κ' ∧ ⊤ in S

中文:
定义 PropSetWithTop
  签名: (κ' : 基数.{u}) [Fact κ'.是正则]
  定义体: HasCardinalLT S κ' ∧ ⊤ in S

Depends on / 依赖: HasCardinalLT
-/
def PropSetWithTop (κ' : Cardinal.{u}) [Fact κ'.IsRegular]
    (S : Set J.withTop.obj) : Prop :=
  HasCardinalLT S κ' ∧ ⊤ in S

variable (κ' : Cardinal.{u}) [Fact κ'.IsRegular]

instance (S : Subtype (J.PropSetWithTop κ')) : HasTerminal S :=
  IsTerminal.hasTerminal (X := ⟨⊤, S.2.2⟩)
    (IsTerminal.ofUniqueHom (fun _ => homOfLE (by rw [Subtype.mk_le_mk]; exact le_top))
      (fun _ _ => rfl))

instance (S : Subtype (J.PropSetWithTop κ')) : IsCardinalFiltered S κ :=
  isCardinalFiltered_of_hasTerminal _ _

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsCardinalFiltered (Subtype (J.PropSetWithTop κ')) κ'
  body: isCardinalFiltered_preorder _ _ (fun K α hK => by
    rw [← hasCardinalLT_iff_cardinal_mk_lt] at hK
    have hκ' : Cardinal.aleph0 <= κ' := Cardinal.IsRegular.aleph0_le Fact.out
    refine ⟨⟨(⋃ (k : K), α k) union {⊤},
      hasCardinalLT_union hκ' (hasCardinalLT_iUnion _ hK (fun k => (α k).property

中文:
实例 :
  签名: 是CardinalFiltered (子类型 (J.PropSetWithTop κ')) κ'
  定义体: isCardinalFiltered_preorder _ _ (fun K α hK => by
    rw [← hasCardinalLT_iff_cardinal_mk_lt] at hK
    have hκ' : Cardinal.aleph0 <= κ' := Cardinal.IsRegular.aleph0_le Fact.out
    refine ⟨⟨(⋃ (k : K), α k) union {⊤},
      hasCardinalLT_union hκ' (hasCardinalLT_iUnion _ hK (fun k => (α k).property

Depends on / 依赖: Cardinal, Cardinal.IsRegular.aleph0_le, Cardinal.aleph0, Fact.out, IsRegular, Set.subset_iUnion, Set.subset_union_left, Subtype, Subtype.mk_le_mk, aleph0, aleph0_le, hasCardinalLT_iUnion, hasCardinalLT_iff_cardinal_mk_lt, hasCardinalLT_of_finite, hasCardinalLT_union, isCardinalFiltered_preorder, mk_le_mk, property, property.left, subset_iUnion
-/
instance : IsCardinalFiltered (Subtype (J.PropSetWithTop κ')) κ' :=
  isCardinalFiltered_preorder _ _ (fun K α hK => by
    rw [← hasCardinalLT_iff_cardinal_mk_lt] at hK
    have hκ' : Cardinal.aleph0 <= κ' := Cardinal.IsRegular.aleph0_le Fact.out
    refine ⟨⟨(⋃ (k : K), α k) union {⊤},
      hasCardinalLT_union hκ' (hasCardinalLT_iUnion _ hK (fun k => (α k).property.left))
        (hasCardinalLT_of_finite _ _ hκ'), by simp⟩, fun k => ?_⟩
    rw [Subtype.mk_le_mk]
    exact subset_trans (Set.subset_iUnion (fun i => (α i).1) k) Set.subset_union_left)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsFiltered (Subtype (J.PropSetWithTop κ'))
  body: isFiltered_of_isCardinalFiltered _ κ'

中文:
实例 :
  签名: 是Filtered (子类型 (J.PropSetWithTop κ'))
  定义体: isFiltered_of_isCardinalFiltered _ κ'

Depends on / 依赖: isFiltered_of_isCardinalFiltered
-/
instance : IsFiltered (Subtype (J.PropSetWithTop κ')) :=
  isFiltered_of_isCardinalFiltered _ κ'

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsDirectedOrder (Subtype (J.PropSetWithTop κ'))
  body: IsFiltered.isDirectedOrder _

中文:
实例 :
  签名: IsDirectedOrder (子类型 (J.PropSetWithTop κ'))
  定义体: IsFiltered.isDirectedOrder _

Depends on / 依赖: IsFiltered, IsFiltered.isDirectedOrder, isDirectedOrder
-/
instance : IsDirectedOrder (Subtype (J.PropSetWithTop κ')) :=
  IsFiltered.isDirectedOrder _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Nonempty (Subtype (J.PropSetWithTop κ'))
  body: IsFiltered.nonempty

中文:
实例 :
  签名: 非空 (子类型 (J.PropSetWithTop κ'))
  定义体: IsFiltered.nonempty

Depends on / 依赖: IsFiltered, IsFiltered.nonempty, nonempty
-/
instance : Nonempty (Subtype (J.PropSetWithTop κ')) :=
  IsFiltered.nonempty

variable {J} in
/--
lemma `propSetWithTop_pair` / 引理 `propSetWithTop_pair`

English:
lemma propSetWithTop_pair
  given: (j : J.obj)
  statement: J.PropSetWithTop κ' {WithTop.some j, ⊤}
  proof: ⟨hasCardinalLT_of_finite _ _ (Cardinal.IsRegular.aleph0_le Fact.out),
    Set.mem_insert_of_mem _ (by simp)⟩

中文:
引理 propSetWithTop_pair
  条件: (j : J.obj)
  结论: J.PropSetWithTop κ' {WithTop.some j, ⊤}
  证明: ⟨hasCardinalLT_of_finite _ _ (Cardinal.IsRegular.aleph0_le Fact.out),
    Set.mem_insert_of_mem _ (by simp)⟩

Depends on / 依赖: Cardinal, Cardinal.IsRegular.aleph0_le, Fact.out, IsRegular, Set.mem_insert_of_mem, aleph0_le, hasCardinalLT_of_finite, mem_insert_of_mem
-/
lemma propSetWithTop_pair (j : J.obj) : J.PropSetWithTop κ' {WithTop.some j, ⊤} :=
  ⟨hasCardinalLT_of_finite _ _ (Cardinal.IsRegular.aleph0_le Fact.out),
    Set.mem_insert_of_mem _ (by simp)⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `exists_mem_propSetWithTop` / 引理 `exists_mem_propSetWithTop`

English:
lemma exists_mem_propSetWithTop
  given: (a : J.withTop.obj)
  proof: by
  induction a with
  | some a => exact ⟨_, propSetWithTop_pair _ a, by aesop⟩
  | none => exact ⟨_, propSetWithTop_pair _ (Classical.arbitrary _), by aesop⟩

中文:
引理 存在_mem_propSetWithTop
  条件: (a : J.withTop.obj)
  证明: by
  induction a with
  | some a => exact ⟨_, propSetWithTop_pair _ a, by aesop⟩
  | none => exact ⟨_, propSetWithTop_pair _ (Classical.arbitrary _), by aesop⟩

Depends on / 依赖: Classical, Classical.arbitrary, arbitrary, propSetWithTop_pair
-/
lemma exists_mem_propSetWithTop (a : J.withTop.obj) :
    exists S, J.PropSetWithTop κ' S ∧ a in S := by
  induction a with
  | some a => exact ⟨_, propSetWithTop_pair _ a, by aesop⟩
  | none => exact ⟨_, propSetWithTop_pair _ (Classical.arbitrary _), by aesop⟩

/--
Definition of `coconeWithTop` / `coconeWithTop` 的定义

English:
abbreviation coconeWithTop
  signature: : Cocone (functorOfPredicateSet (J.PropSetWithTop κ'))
  body: coconeOfPredicateSet (PropSetWithTop J κ')

中文:
缩写 coconeWithTop
  签名: : 余锥 (functorOfPredicateSet (J.PropSetWithTop κ'))
  定义体: coconeOfPredicateSet (PropSetWithTop J κ')

Depends on / 依赖: PropSetWithTop, coconeOfPredicateSet
-/
abbrev coconeWithTop : Cocone (functorOfPredicateSet (J.PropSetWithTop κ')) :=
  coconeOfPredicateSet (PropSetWithTop J κ')

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `isColimitCoconeWithTop` / `isColimitCoconeWithTop` 的定义

English:
definition isColimitCoconeWithTop
  signature: : IsColimit (coconeWithTop J κ')
  body: isColimitCoconeOfPredicateSet _ (fun a => by
    induction a with
    | some a => exact ⟨_, propSetWithTop_pair _ a, by aesop⟩
    | none => exact ⟨_, propSetWithTop_pair _ (Classical.arbitrary _), by aesop⟩)

中文:
定义 isColimitCoconeWithTop
  签名: : 是余极限 (coconeWithTop J κ')
  定义体: isColimitCoconeOfPredicateSet _ (fun a => by
    induction a with
    | some a => exact ⟨_, propSetWithTop_pair _ a, by aesop⟩
    | none => exact ⟨_, propSetWithTop_pair _ (Classical.arbitrary _), by aesop⟩)

Depends on / 依赖: Classical, Classical.arbitrary, arbitrary, isColimitCoconeOfPredicateSet, propSetWithTop_pair
-/
noncomputable def isColimitCoconeWithTop : IsColimit (coconeWithTop J κ') :=
  isColimitCoconeOfPredicateSet _ (fun a => by
    induction a with
    | some a => exact ⟨_, propSetWithTop_pair _ a, by aesop⟩
    | none => exact ⟨_, propSetWithTop_pair _ (Classical.arbitrary _), by aesop⟩)

variable {κ'} in
/--
lemma `isCardinalPresentable_iff` / 引理 `isCardinalPresentable_iff`

English:
lemma isCardinalPresentable_iff
  given: (h : κ <= κ')
  proof: by
  refine ⟨fun _ => ?_, fun hJ => isCardinalPresentable_of_hasCardinalLT_of_le _ hJ h⟩
  obtain ⟨X, f, hf⟩ :=
    IsCardinalPresentable.exists_hom_of_isColimit κ' (isColimitCoconeWithTop J κ')
      (ObjectProperty.homMk (PartOrdEmb.ofHom WithTop.coeOrderHom))
  replace hf : OrderEmbedding.subtype

中文:
引理 isCardinalPresentable_iff
  条件: (h : κ <= κ')
  证明: by
  refine ⟨fun _ => ?_, fun hJ => isCardinalPresentable_of_hasCardinalLT_of_le _ hJ h⟩
  obtain ⟨X, f, hf⟩ :=
    IsCardinalPresentable.exists_hom_of_isColimit κ' (isColimitCoconeWithTop J κ')
      (ObjectProperty.homMk (PartOrdEmb.ofHom WithTop.coeOrderHom))
  replace hf : OrderEmbedding.subtype
-/
protected lemma isCardinalPresentable_iff (h : κ <= κ') :
    IsCardinalPresentable J κ' ↔ HasCardinalLT J.obj κ' := by
  refine ⟨fun _ => ?_, fun hJ => isCardinalPresentable_of_hasCardinalLT_of_le _ hJ h⟩
  obtain ⟨X, f, hf⟩ :=
    IsCardinalPresentable.exists_hom_of_isColimit κ' (isColimitCoconeWithTop J κ')
      (ObjectProperty.homMk (PartOrdEmb.ofHom WithTop.coeOrderHom))
  replace hf : OrderEmbedding.subtype (· in X.1) ∘ f = WithTop.coeOrderHom := by
    ext x
    exact ConcreteCategory.congr_hom hf x
  refine X.2.1.of_injective f (Function.Injective.of_comp
    (f := OrderEmbedding.subtype (· in X.1)) ?_)
  dsimp at hf ⊢
  rw [hf]
  exact WithTop.coe_injective

end

/--
lemma `isCardinalPresentable_iff'` / 引理 `isCardinalPresentable_iff'`

English:
lemma isCardinalPresentable_iff'
  given: (J : CardinalDirectedPoset κ)
  proof: CardinalDirectedPoset.isCardinalPresentable_iff _ (le_refl _)

中文:
引理 isCardinalPresentable_iff'
  条件: (J : CardinalDirectedPoset κ)
  证明: CardinalDirectedPoset.isCardinalPresentable_iff _ (le_refl _)
-/
protected lemma isCardinalPresentable_iff' (J : CardinalDirectedPoset κ) :
    IsCardinalPresentable J κ ↔ HasCardinalLT J.obj κ :=
  CardinalDirectedPoset.isCardinalPresentable_iff _ (le_refl _)

section

variable (J : CardinalDirectedPoset κ)

/--
Definition of `PropSet` / `PropSet` 的定义

English:
definition PropSet
  signature: (S : Set J.obj)
  body: HasCardinalLT S κ ∧ HasTerminal S

中文:
定义 PropSet
  签名: (S : 集合 J.obj)
  定义体: HasCardinalLT S κ ∧ HasTerminal S

Depends on / 依赖: HasCardinalLT, HasTerminal
-/
def PropSet (S : Set J.obj) : Prop :=
  HasCardinalLT S κ ∧ HasTerminal S

instance (S : Subtype J.PropSet) : HasTerminal S := S.prop.2

instance (S : Subtype J.PropSet) : IsCardinalFiltered S κ :=
  isCardinalFiltered_of_hasTerminal _ _

variable {J} in
/--
lemma `propSet_singleton` / 引理 `propSet_singleton`

English:
lemma propSet_singleton
  given: (j : J.obj)
  statement: J.PropSet {j}
  proof: ⟨hasCardinalLT_of_finite _ _ (Cardinal.IsRegular.aleph0_le Fact.out), by
    let : OrderTop ({j} : Set J.obj) := { top := ⟨j, rfl⟩, le_top := by simp }
    exact isTerminalTop.hasTerminal⟩

中文:
引理 propSet_singleton
  条件: (j : J.obj)
  结论: J.PropSet {j}
  证明: ⟨hasCardinalLT_of_finite _ _ (Cardinal.IsRegular.aleph0_le Fact.out), by
    let : OrderTop ({j} : Set J.obj) := { top := ⟨j, rfl⟩, le_top := by simp }
    exact isTerminalTop.hasTerminal⟩

Depends on / 依赖: Cardinal, Cardinal.IsRegular.aleph0_le, Fact.out, IsRegular, J.obj, OrderTop, aleph0_le, hasCardinalLT_of_finite, hasTerminal, isTerminalTop, isTerminalTop.hasTerminal, le_top
-/
lemma propSet_singleton (j : J.obj) : J.PropSet {j} :=
  ⟨hasCardinalLT_of_finite _ _ (Cardinal.IsRegular.aleph0_le Fact.out), by
    let : OrderTop ({j} : Set J.obj) := { top := ⟨j, rfl⟩, le_top := by simp }
    exact isTerminalTop.hasTerminal⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsCardinalFiltered (Subtype J.PropSet) κ
  body: isCardinalFiltered_preorder _ _ (fun K α hK => by
    rw [← hasCardinalLT_iff_cardinal_mk_lt] at hK
    let t (k : K) : (α k).val := ⊤_ _
    let m := IsCardinalFiltered.max (fun k => (t k).val) hK
    let S : Set J.obj := (⋃ (k : K), α k) union {m}
    let : OrderTop S :=
      { top := ⟨m, by simp

中文:
实例 :
  签名: 是CardinalFiltered (子类型 J.PropSet) κ
  定义体: isCardinalFiltered_preorder _ _ (fun K α hK => by
    rw [← hasCardinalLT_iff_cardinal_mk_lt] at hK
    let t (k : K) : (α k).val := ⊤_ _
    let m := IsCardinalFiltered.max (fun k => (t k).val) hK
    let S : Set J.obj := (⋃ (k : K), α k) union {m}
    let : OrderTop S :=
      { top := ⟨m, by simp

Depends on / 依赖: IsCardinalFiltered, IsCardinalFiltered.max, J.obj, OrderTop, Set.mem_iUnion, Set.mem_insert_iff, Set.union_singleton, Subtype, Subtype.mk_le_mk, hasCardinalLT_iff_cardinal_mk_lt, isCardinalFiltered_preorder, leOfHom, le_top, mem_iUnion, mem_insert_iff, mk_le_mk, terminal, terminal.from, union_singleton
-/
instance : IsCardinalFiltered (Subtype J.PropSet) κ :=
  isCardinalFiltered_preorder _ _ (fun K α hK => by
    rw [← hasCardinalLT_iff_cardinal_mk_lt] at hK
    let t (k : K) : (α k).val := ⊤_ _
    let m := IsCardinalFiltered.max (fun k => (t k).val) hK
    let S : Set J.obj := (⋃ (k : K), α k) union {m}
    let : OrderTop S :=
      { top := ⟨m, by simp [S]⟩
        le_top := by
          rintro ⟨s, hs⟩
          simp only [Set.union_singleton, Set.mem_insert_iff, Set.mem_iUnion, S] at hs
          obtain rfl | ⟨k, hs⟩ := hs
          · simp
          · simp only [Subtype.mk_le_mk]
            exact leOfHom ((by exact terminal.from (C := (α k).val) ⟨_, hs⟩) ≫
              IsCardinalFiltered.toMax _ hK k) }
    refine ⟨⟨S, ?_, isTerminalTop.hasTerminal⟩, fun k => ?_⟩
    · have hκ : Cardinal.aleph0 <= κ := Cardinal.IsRegular.aleph0_le Fact.out
      exact hasCardinalLT_union hκ (hasCardinalLT_iUnion _ hK (fun k => (α k).2.1))
        (hasCardinalLT_of_finite _ _ hκ)
    · simp only [← Subtype.coe_le_coe]
      exact subset_trans (Set.subset_iUnion_of_subset k (subset_refl _)) Set.subset_union_left )

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsFiltered (Subtype J.PropSet)
  body: isFiltered_of_isCardinalFiltered _ κ

中文:
实例 :
  签名: 是Filtered (子类型 J.PropSet)
  定义体: isFiltered_of_isCardinalFiltered _ κ

Depends on / 依赖: isFiltered_of_isCardinalFiltered
-/
instance : IsFiltered (Subtype J.PropSet) := isFiltered_of_isCardinalFiltered _ κ

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsDirectedOrder (Subtype J.PropSet)
  body: IsFiltered.isDirectedOrder _

中文:
实例 :
  签名: IsDirectedOrder (子类型 J.PropSet)
  定义体: IsFiltered.isDirectedOrder _

Depends on / 依赖: IsFiltered, IsFiltered.isDirectedOrder, isDirectedOrder
-/
instance : IsDirectedOrder (Subtype J.PropSet) :=
  IsFiltered.isDirectedOrder _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Nonempty (Subtype J.PropSet)
  body: IsFiltered.nonempty

中文:
实例 :
  签名: 非空 (子类型 J.PropSet)
  定义体: IsFiltered.nonempty

Depends on / 依赖: IsFiltered, IsFiltered.nonempty, nonempty
-/
instance : Nonempty (Subtype J.PropSet) :=
  IsFiltered.nonempty

/--
Definition of `cocone` / `cocone` 的定义

English:
abbreviation cocone
  signature: : Cocone (functorOfPredicateSet J.PropSet)
  body: coconeOfPredicateSet J.PropSet

中文:
缩写 cocone
  签名: : 余锥 (functorOfPredicateSet J.PropSet)
  定义体: coconeOfPredicateSet J.PropSet

Depends on / 依赖: J.PropSet, PropSet, coconeOfPredicateSet
-/
abbrev cocone : Cocone (functorOfPredicateSet J.PropSet) :=
  coconeOfPredicateSet J.PropSet

/--
Definition of `isColimitCocone` / `isColimitCocone` 的定义

English:
definition isColimitCocone
  signature: (J : CardinalDirectedPoset κ)
  body: isColimitCoconeOfPredicateSet _ (fun a => ⟨_, propSet_singleton a, by simp⟩)

中文:
定义 isColimitCocone
  签名: (J : CardinalDirectedPoset κ)
  定义体: isColimitCoconeOfPredicateSet _ (fun a => ⟨_, propSet_singleton a, by simp⟩)

Depends on / 依赖: isColimitCoconeOfPredicateSet, propSet_singleton
-/
noncomputable def isColimitCocone (J : CardinalDirectedPoset κ) :
    IsColimit (cocone J) :=
  isColimitCoconeOfPredicateSet _ (fun a => ⟨_, propSet_singleton a, by simp⟩)

end

variable (κ) in
/--
lemma `isCardinalFilteredGenerator_hasCardinalLTWithTerminal` / 引理 `isCardinalFilteredGenerator_hasCardinalLTWithTerminal`

English:
lemma isCardinalFilteredGenerator_hasCardinalLTWithTerminal
  proof: by
    rintro J ⟨_, _⟩
    rwa [isCardinalPresentable_iff, J.isCardinalPresentable_iff']
  exists_colimitsOfShape J :=
    ⟨_, inferInstance, inferInstance, ⟨{
      diag := _
      ι := _
      isColimit := isColimitCocone J
      prop_diag_obj j := j.prop }⟩⟩

中文:
引理 isCardinalFilteredGenerator_hasCardinalLTWithTerminal
  证明: by
    rintro J ⟨_, _⟩
    rwa [isCardinalPresentable_iff, J.isCardinalPresentable_iff']
  exists_colimitsOfShape J :=
    ⟨_, inferInstance, inferInstance, ⟨{
      diag := _
      ι := _
      isColimit := isColimitCocone J
      prop_diag_obj j := j.prop }⟩⟩

Depends on / 依赖: J.isCardinalPresentable_iff, exists_colimitsOfShape, isCardinalPresentable_iff, isColimit, isColimitCocone, j.prop, prop_diag_obj
-/
lemma isCardinalFilteredGenerator_hasCardinalLTWithTerminal :
    (hasCardinalLTWithTerminal κ).IsCardinalFilteredGenerator κ where
  le_isCardinalPresentable := by
    rintro J ⟨_, _⟩
    rwa [isCardinalPresentable_iff, J.isCardinalPresentable_iff']
  exists_colimitsOfShape J :=
    ⟨_, inferInstance, inferInstance, ⟨{
      diag := _
      ι := _
      isColimit := isColimitCocone J
      prop_diag_obj j := j.prop }⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsCardinalAccessibleCategory (CardinalDirectedPoset κ) κ
  body: ⟨hasCardinalLTWithTerminal κ, inferInstance,
      isCardinalFilteredGenerator_hasCardinalLTWithTerminal κ⟩

中文:
实例 :
  签名: 是CardinalAccessible范畴 (CardinalDirectedPoset κ) κ
  定义体: ⟨hasCardinalLTWithTerminal κ, inferInstance,
      isCardinalFilteredGenerator_hasCardinalLTWithTerminal κ⟩

Depends on / 依赖: hasCardinalLTWithTerminal, isCardinalFilteredGenerator_hasCardinalLTWithTerminal
-/
instance : IsCardinalAccessibleCategory (CardinalDirectedPoset κ) κ where
  exists_generator :=
    ⟨hasCardinalLTWithTerminal κ, inferInstance,
      isCardinalFilteredGenerator_hasCardinalLTWithTerminal κ⟩

variable (κ) (X : Type u)

/--
Definition of `SetCardinalLT` / `SetCardinalLT` 的定义

English:
abbreviation SetCardinalLT
  body: Subtype (fun (S : Set X) => HasCardinalLT S κ)

中文:
缩写 SetCardinalLT
  定义体: Subtype (fun (S : Set X) => HasCardinalLT S κ)

Depends on / 依赖: HasCardinalLT, Subtype
-/
abbrev SetCardinalLT := Subtype (fun (S : Set X) => HasCardinalLT S κ)

variable {X} in
/--
Definition of `SetCardinalLT.singleton` / `SetCardinalLT.singleton` 的定义

English:
abbreviation SetCardinalLT.singleton
  signature: (x : X)
  body: ⟨{x}, hasCardinalLT_of_finite _ _ (Cardinal.IsRegular.aleph0_le Fact.out)⟩

中文:
缩写 SetCardinalLT.singleton
  签名: (x : X)
  定义体: ⟨{x}, hasCardinalLT_of_finite _ _ (Cardinal.IsRegular.aleph0_le Fact.out)⟩

Depends on / 依赖: Cardinal, Cardinal.IsRegular.aleph0_le, Fact.out, IsRegular, aleph0_le, hasCardinalLT_of_finite
-/
abbrev SetCardinalLT.singleton (x : X) : SetCardinalLT κ X :=
  ⟨{x}, hasCardinalLT_of_finite _ _ (Cardinal.IsRegular.aleph0_le Fact.out)⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsCardinalFiltered (SetCardinalLT κ X) κ
  body: isCardinalFiltered_preorder _ _
    (fun K f hK =>
      ⟨⟨⋃ (k : K), (f k).val, hasCardinalLT_iUnion _
        (by rwa [hasCardinalLT_iff_cardinal_mk_lt]) (fun k => (f k).prop)⟩,
      Set.subset_iUnion (fun k => (f k).val)⟩)

中文:
实例 :
  签名: 是CardinalFiltered (SetCardinalLT κ X) κ
  定义体: isCardinalFiltered_preorder _ _
    (fun K f hK =>
      ⟨⟨⋃ (k : K), (f k).val, hasCardinalLT_iUnion _
        (by rwa [hasCardinalLT_iff_cardinal_mk_lt]) (fun k => (f k).prop)⟩,
      Set.subset_iUnion (fun k => (f k).val)⟩)

Depends on / 依赖: Set.subset_iUnion, hasCardinalLT_iUnion, hasCardinalLT_iff_cardinal_mk_lt, isCardinalFiltered_preorder, subset_iUnion
-/
instance : IsCardinalFiltered (SetCardinalLT κ X) κ :=
  isCardinalFiltered_preorder _ _
    (fun K f hK =>
      ⟨⟨⋃ (k : K), (f k).val, hasCardinalLT_iUnion _
        (by rwa [hasCardinalLT_iff_cardinal_mk_lt]) (fun k => (f k).prop)⟩,
      Set.subset_iUnion (fun k => (f k).val)⟩)

/--
Definition of `setCardinalLT` / `setCardinalLT` 的定义

English:
abbreviation setCardinalLT
  signature: : CardinalDirectedPoset κ
  body: .of (PartOrdEmb.of (SetCardinalLT κ X))

中文:
缩写 setCardinalLT
  签名: : CardinalDirectedPoset κ
  定义体: .of (PartOrdEmb.of (SetCardinalLT κ X))

Depends on / 依赖: PartOrdEmb, PartOrdEmb.of, SetCardinalLT
-/
abbrev setCardinalLT : CardinalDirectedPoset κ :=
  .of (PartOrdEmb.of (SetCardinalLT κ X))

end CardinalDirectedPoset

@[deprecated (since := "2026-06-24")] alias CardinalFilteredPoset :=
  CardinalDirectedPoset

namespace CardinalFilteredPoset

@[deprecated (since := "2026-06-24")] alias ι := CardinalDirectedPoset.ι
@[deprecated (since := "2026-06-24")] alias of := CardinalDirectedPoset.of
@[deprecated (since := "2026-06-24")] alias Hom.injective := CardinalDirectedPoset.Hom.injective
@[deprecated (since := "2026-06-24")] alias Hom.le_iff_le := CardinalDirectedPoset.Hom.le_iff_le
@[deprecated (since := "2026-06-24")] alias withTop := CardinalDirectedPoset.withTop
@[deprecated (since := "2026-06-24")]
alias functorOfPredicateSet := CardinalDirectedPoset.functorOfPredicateSet
@[deprecated (since := "2026-06-24")]
alias coconeOfPredicateSet := CardinalDirectedPoset.coconeOfPredicateSet
@[deprecated (since := "2026-06-24")]
alias isColimitCoconeOfPredicateSet := CardinalDirectedPoset.isColimitCoconeOfPredicateSet
@[deprecated (since := "2026-06-24")]
alias hasCardinalLTWithTerminal := CardinalDirectedPoset.hasCardinalLTWithTerminal
@[deprecated (since := "2026-06-24")]
alias isCardinalPresentable_of_hasCardinalLT_of_le :=
  CardinalDirectedPoset.isCardinalPresentable_of_hasCardinalLT_of_le
@[deprecated (since := "2026-06-24")]
alias PropSetWithTop := CardinalDirectedPoset.PropSetWithTop
@[deprecated (since := "2026-06-24")]
alias propSetWithTop_pair := CardinalDirectedPoset.propSetWithTop_pair
@[deprecated (since := "2026-06-24")]
alias exists_mem_propSetWithTop := CardinalDirectedPoset.exists_mem_propSetWithTop
@[deprecated (since := "2026-06-24")]
alias coconeWithTop := CardinalDirectedPoset.coconeWithTop
@[deprecated (since := "2026-06-24")]
alias isColimitCoconeWithTop := CardinalDirectedPoset.isColimitCoconeWithTop
@[deprecated (since := "2026-06-24")]
alias isCardinalPresentable_iff := CardinalDirectedPoset.isCardinalPresentable_iff
@[deprecated (since := "2026-06-24")]
alias isCardinalPresentable_iff' := CardinalDirectedPoset.isCardinalPresentable_iff'
@[deprecated (since := "2026-06-24")] alias PropSet := CardinalDirectedPoset.PropSet
@[deprecated (since := "2026-06-24")]
alias propSet_singleton := CardinalDirectedPoset.propSet_singleton
@[deprecated (since := "2026-06-24")] alias cocone := CardinalDirectedPoset.cocone
@[deprecated (since := "2026-06-24")] alias isColimitCocone := CardinalDirectedPoset.isColimitCocone

end CardinalFilteredPoset

end CategoryTheory
