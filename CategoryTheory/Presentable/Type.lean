/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Generator.Type
public import Mathlib.CategoryTheory.Presentable.StrongGenerator
public import Mathlib.CategoryTheory.Types.Set

/-!
# Presentable objects in Type

In this file, we show that if `κ : Cardinal.{u}` is a regular cardinal,
then `X : Type u` is `κ`-presentable in the category of types iff
`HasCardinalLT X κ` holds, i.e. the cardinal number of `X` is less than `κ`.

-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite ConcreteCategory

namespace HasCardinalLT

variable (X : Type u) (κ : Cardinal.{u})

set_option backward.defeqAttrib.useBackward true in
variable {X κ} in
/--
lemma `isCardinalPresentable` / 引理 `isCardinalPresentable`

English:
lemma isCardinalPresentable
  given: (hX : HasCardinalLT X κ) [Fact κ.IsRegular]
  proof: ⟨fun {F} => ⟨fun {c} hc => ⟨by
      have := isFiltered_of_isCardinalFiltered J κ
      refine Types.FilteredColimit.isColimitOf' _ _ (fun f => ?_) (fun j f g h => ?_)
      · dsimp at f
        choose j g hg using fun x => Types.jointly_surjective_of_isColimit hc (f x)
        refine ⟨IsCardinalFil

中文:
引理 isCardinalPresentable
  条件: (hX : HasCardinalLT X κ) [Fact κ.是正则]
  证明: ⟨fun {F} => ⟨fun {c} hc => ⟨by
      have := isFiltered_of_isCardinalFiltered J κ
      refine Types.FilteredColimit.isColimitOf' _ _ (fun f => ?_) (fun j f g h => ?_)
      · dsimp at f
        choose j g hg using fun x => Types.jointly_surjective_of_isColimit hc (f x)
        refine ⟨IsCardinalFil

Depends on / 依赖: F.map, FilteredCo, FilteredColimit, IsCardinalFiltered, IsCardinalFiltered.max, IsCardinalFiltered.toMax, Types.FilteredCo, Types.FilteredColimit.isColimitOf, Types.jointly_surjective_of_isColimit, congr_hom, isColimitOf, isFiltered_of_isCardinalFiltered, jointly_surjective_of_isColimit
-/
lemma isCardinalPresentable (hX : HasCardinalLT X κ) [Fact κ.IsRegular] :
    IsCardinalPresentable X κ where
  preservesColimitOfShape J _ _ :=
    ⟨fun {F} => ⟨fun {c} hc => ⟨by
      have := isFiltered_of_isCardinalFiltered J κ
      refine Types.FilteredColimit.isColimitOf' _ _ (fun f => ?_) (fun j f g h => ?_)
      · dsimp at f
        choose j g hg using fun x => Types.jointly_surjective_of_isColimit hc (f x)
        refine ⟨IsCardinalFiltered.max j hX,
          ↾fun x => F.map (IsCardinalFiltered.toMax j hX x) (g x), ?_⟩
        dsimp
        ext x
        dsimp at j g hg x ⊢
        rw [← hg]
        exact congr_hom (c.w (IsCardinalFiltered.toMax j hX x)).symm (g x)
      · choose k a hk using fun x =>
          (Types.FilteredColimit.isColimit_eq_iff' hc _ _).1 (congr_hom h x)
        dsimp at f g h k a hk ⊢
        replace hk : forall x, F.map (a x) (f x) = F.map (a x) (g x) := by assumption
        obtain ⟨l, b, c, hl⟩ : exists (l : J) (c : j ⟶ l) (b : forall x, k x ⟶ l),
            forall x, a x ≫ b x = c := by
          let φ (x : X) : j ⟶ IsCardinalFiltered.max k hX :=
            a x ≫ IsCardinalFiltered.toMax k hX x
          exact ⟨IsCardinalFiltered.coeq φ hX,
            IsCardinalFiltered.toCoeq φ hX,
            fun x => IsCardinalFiltered.toMax k hX x ≫ IsCardinalFiltered.coeqHom φ hX,
            fun x => by simpa [φ] using IsCardinalFiltered.coeq_condition φ hX x⟩
        refine ⟨l, b, by ext x; simp [← hl x, hk]⟩⟩⟩⟩

/--
Definition of `Set` / `Set` 的定义

English:
abbreviation Set
  body: { A : Set X // HasCardinalLT A κ }

中文:
缩写 集合
  定义体: { A : Set X // HasCardinalLT A κ }
-/
protected abbrev Set := { A : Set X // HasCardinalLT A κ }

namespace Set

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Fact
  signature: κ.IsRegular] :
  body: isCardinalFiltered_preorder _ _
    (fun ι A hι => ⟨⟨⋃ (i : ι), (A i).val,
      hasCardinalLT_iUnion _
        (by rwa [hasCardinalLT_iff_cardinal_mk_lt]) (fun i => (A i).prop)⟩,
      le_iSup (fun i => (A i).1)⟩)

中文:
实例 [Fact
  签名: κ.是正则] :
  定义体: isCardinalFiltered_preorder _ _
    (fun ι A hι => ⟨⟨⋃ (i : ι), (A i).val,
      hasCardinalLT_iUnion _
        (by rwa [hasCardinalLT_iff_cardinal_mk_lt]) (fun i => (A i).prop)⟩,
      le_iSup (fun i => (A i).1)⟩)

Depends on / 依赖: hasCardinalLT_iUnion, hasCardinalLT_iff_cardinal_mk_lt, isCardinalFiltered_preorder, le_iSup
-/
instance [Fact κ.IsRegular] :
    IsCardinalFiltered (HasCardinalLT.Set X κ) κ :=
  isCardinalFiltered_preorder _ _
    (fun ι A hι => ⟨⟨⋃ (i : ι), (A i).val,
      hasCardinalLT_iUnion _
        (by rwa [hasCardinalLT_iff_cardinal_mk_lt]) (fun i => (A i).prop)⟩,
      le_iSup (fun i => (A i).1)⟩)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Fact
  signature: κ.IsRegular] :
  body: isFiltered_of_isCardinalFiltered _ κ

中文:
实例 [Fact
  签名: κ.是正则] :
  定义体: isFiltered_of_isCardinalFiltered _ κ

Depends on / 依赖: isFiltered_of_isCardinalFiltered
-/
instance [Fact κ.IsRegular] :
    IsFiltered (HasCardinalLT.Set X κ) :=
  isFiltered_of_isCardinalFiltered _ κ

/--
lemma `isFiltered_of_aleph0_le` / 引理 `isFiltered_of_aleph0_le`

English:
lemma isFiltered_of_aleph0_le
  given: (hκ : Cardinal.aleph0 <= κ)
  proof: ⟨⟨∅, hasCardinalLT_of_finite _ _ hκ⟩⟩
  toIsFilteredOrEmpty := by
    have : IsDirectedOrder (HasCardinalLT.Set X κ) :=
      ⟨fun A B => ⟨⟨A.val union B.val, hasCardinalLT_union hκ A.prop B.prop⟩,
        Set.subset_union_left, Set.subset_union_right⟩⟩
    exact isFilteredOrEmpty_of_directed_le _

中文:
引理 isFiltered_of_aleph0_le
  条件: (hκ : 基数.aleph0 <= κ)
  证明: ⟨⟨∅, hasCardinalLT_of_finite _ _ hκ⟩⟩
  toIsFilteredOrEmpty := by
    have : IsDirectedOrder (HasCardinalLT.Set X κ) :=
      ⟨fun A B => ⟨⟨A.val union B.val, hasCardinalLT_union hκ A.prop B.prop⟩,
        Set.subset_union_left, Set.subset_union_right⟩⟩
    exact isFilteredOrEmpty_of_directed_le _

Depends on / 依赖: hasCardinalLT_of_finite
-/
lemma isFiltered_of_aleph0_le (hκ : Cardinal.aleph0 <= κ) :
    IsFiltered (HasCardinalLT.Set X κ) where
  nonempty := ⟨⟨∅, hasCardinalLT_of_finite _ _ hκ⟩⟩
  toIsFilteredOrEmpty := by
    have : IsDirectedOrder (HasCardinalLT.Set X κ) :=
      ⟨fun A B => ⟨⟨A.val union B.val, hasCardinalLT_union hκ A.prop B.prop⟩,
        Set.subset_union_left, Set.subset_union_right⟩⟩
    exact isFilteredOrEmpty_of_directed_le _

/-- The functor `HasCardinalLT.Set X κ ⥤ Type u` which sends a subset of `X`
of cardinality `κ` to the corresponding subtype. -/
@[simps! +dsimpLhs]
/--
Definition of `functor` / `functor` 的定义

English:
definition functor
  signature: : HasCardinalLT.Set X κ ⥤ Type u
  body: Monotone.functor (f := Subtype.val) (by tauto) ⋙ Set.functorToTypes (X := X)

中文:
定义 functor
  签名: : HasCardinalLT.集合 X κ ⥤ 类型u
  定义体: Monotone.functor (f := Subtype.val) (by tauto) ⋙ Set.functorToTypes (X := X)

Depends on / 依赖: Monotone, Monotone.functor, Set.functorToTypes, Subtype, Subtype.val, functor, functorToTypes
-/
def functor : HasCardinalLT.Set X κ ⥤ Type u :=
  Monotone.functor (f := Subtype.val) (by tauto) ⋙ Set.functorToTypes (X := X)

/-- The cocone for `Set.functor X κ : HasCardinalLT.Set X κ ⥤ Type u` with point `X`. -/
@[simps]
/--
Definition of `cocone` / `cocone` 的定义

English:
definition cocone
  signature: : Cocone (Set.functor X κ) where
  body: X
  ι.app _ := ↾(Subtype.val)

中文:
定义 cocone
  签名: : 余锥 (集合.functor X κ) where
  定义体: X
  ι.app _ := ↾(Subtype.val)
-/
def cocone : Cocone (Set.functor X κ) where
  pt := X
  ι.app _ := ↾(Subtype.val)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `isColimitCocone` / `isColimitCocone` 的定义

English:
definition isColimitCocone
  body: by
  have := isFiltered_of_aleph0_le X κ hκ
  refine Types.FilteredColimit.isColimitOf' _ _ (fun x => ?_) ?_
  · exact ⟨⟨{x}, hasCardinalLT_of_finite _ _ hκ⟩, ⟨x, by simp⟩, rfl⟩
  · rintro A ⟨x, hx⟩ ⟨y, hy⟩ rfl
    exact ⟨A, 𝟙 _, rfl⟩

中文:
定义 isColimitCocone
  定义体: by
  have := isFiltered_of_aleph0_le X κ hκ
  refine Types.FilteredColimit.isColimitOf' _ _ (fun x => ?_) ?_
  · exact ⟨⟨{x}, hasCardinalLT_of_finite _ _ hκ⟩, ⟨x, by simp⟩, rfl⟩
  · rintro A ⟨x, hx⟩ ⟨y, hy⟩ rfl
    exact ⟨A, 𝟙 _, rfl⟩

Depends on / 依赖: FilteredColimit, Types.FilteredColimit.isColimitOf, hasCardinalLT_of_finite, isColimitOf, isFiltered_of_aleph0_le
-/
noncomputable def isColimitCocone
    (hκ : Cardinal.aleph0 <= κ) : IsColimit (cocone X κ) := by
  have := isFiltered_of_aleph0_le X κ hκ
  refine Types.FilteredColimit.isColimitOf' _ _ (fun x => ?_) ?_
  · exact ⟨⟨{x}, hasCardinalLT_of_finite _ _ hκ⟩, ⟨x, by simp⟩, rfl⟩
  · rintro A ⟨x, hx⟩ ⟨y, hy⟩ rfl
    exact ⟨A, 𝟙 _, rfl⟩

end Set

end HasCardinalLT

namespace CategoryTheory

namespace Types

variable {X : Type u}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `isCardinalPresentable_iff` / 引理 `isCardinalPresentable_iff`

English:
lemma isCardinalPresentable_iff
  given: (κ : Cardinal.{u}) [Fact κ.IsRegular]
  proof: by
  refine ⟨fun _ => ?_, fun hX => hX.isCardinalPresentable⟩
  have := preservesColimitsOfShape_of_isCardinalPresentable X κ
  obtain ⟨⟨A, hA⟩, f, hf⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (coyoneda.obj (op X))
      (HasCardinalLT.Set.isColimitCocone X κ
        (Cardi

中文:
引理 isCardinalPresentable_iff
  条件: (κ : 基数.{u}) [Fact κ.是正则]
  证明: by
  refine ⟨fun _ => ?_, fun hX => hX.isCardinalPresentable⟩
  have := preservesColimitsOfShape_of_isCardinalPresentable X κ
  obtain ⟨⟨A, hA⟩, f, hf⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (coyoneda.obj (op X))
      (HasCardinalLT.Set.isColimitCocone X κ
        (Cardi

Depends on / 依赖: Cardinal, Cardinal.IsRegular.aleph0_le, Equiv.Set.univ, Fact.out, HasCardinalLT, HasCardinalLT.Set.isColimitCocone, IsRegular, Types.jointly_surjective_of_isColimit, aleph0_le, congr_hom, coyoneda, coyoneda.obj, hX.isCardinalPresentable, hasCardinalLT_iff_of_equiv, isCardinalPresentable, isColimitCocone, isColimitOfPreserves, jointly_surjective_of_isColimit, preservesColimitsOfShape_of_isCardinalPresentable
-/
lemma isCardinalPresentable_iff (κ : Cardinal.{u}) [Fact κ.IsRegular] :
    IsCardinalPresentable X κ ↔ HasCardinalLT X κ := by
  refine ⟨fun _ => ?_, fun hX => hX.isCardinalPresentable⟩
  have := preservesColimitsOfShape_of_isCardinalPresentable X κ
  obtain ⟨⟨A, hA⟩, f, hf⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (coyoneda.obj (op X))
      (HasCardinalLT.Set.isColimitCocone X κ
        (Cardinal.IsRegular.aleph0_le Fact.out))) (𝟙 X)
  obtain rfl : A = .univ := by
    ext x
    have := congr_hom hf x
    dsimp at this
    rw [← this]
    simp
  exact (hasCardinalLT_iff_of_equiv (Equiv.Set.univ X) _).1 hA

instance (X : Type u) : IsPresentable.{u} X := by
  obtain ⟨κ, hκ, hX⟩ := HasCardinalLT.exists_regular_cardinal.{u} X
  have : Fact κ.IsRegular := ⟨hκ⟩
  have := hX.isCardinalPresentable
  exact isPresentable_of_isCardinalPresentable X κ

/--
lemma `isStrongGenerator_punit` / 引理 `isStrongGenerator_punit`

English:
lemma isStrongGenerator_punit
  proof: by
  rw [ObjectProperty.isStrongGenerator_iff]
  refine ⟨isSeparator_punit, fun _ _ i hi₁ hi₂ => ?_⟩
  · rw [mono_iff_injective] at hi₁
    rw [isIso_iff_bijective]
    refine ⟨hi₁, fun y => ?_⟩
    obtain ⟨f, hf⟩ := hi₂ PUnit ⟨.unit⟩ (↾fun _ => y)
    exact ⟨f .unit, ConcreteCategory.congr_hom hf .

中文:
引理 isStrongGenerator_punit
  证明: by
  rw [ObjectProperty.isStrongGenerator_iff]
  refine ⟨isSeparator_punit, fun _ _ i hi₁ hi₂ => ?_⟩
  · rw [mono_iff_injective] at hi₁
    rw [isIso_iff_bijective]
    refine ⟨hi₁, fun y => ?_⟩
    obtain ⟨f, hf⟩ := hi₂ PUnit ⟨.unit⟩ (↾fun _ => y)
    exact ⟨f .unit, ConcreteCategory.congr_hom hf .

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, ObjectProperty, ObjectProperty.isStrongGenerator_iff, congr_hom, isIso_iff_bijective, isSeparator_punit, isStrongGenerator_iff, mono_iff_injective
-/
lemma isStrongGenerator_punit :
    (ObjectProperty.singleton (PUnit.{u + 1})).IsStrongGenerator := by
  rw [ObjectProperty.isStrongGenerator_iff]
  refine ⟨isSeparator_punit, fun _ _ i hi₁ hi₂ => ?_⟩
  · rw [mono_iff_injective] at hi₁
    rw [isIso_iff_bijective]
    refine ⟨hi₁, fun y => ?_⟩
    obtain ⟨f, hf⟩ := hi₂ PUnit ⟨.unit⟩ (↾fun _ => y)
    exact ⟨f .unit, ConcreteCategory.congr_hom hf .unit⟩

instance (κ : Cardinal.{u}) [Fact κ.IsRegular] :
    IsCardinalLocallyPresentable (Type u) κ := by
  rw [IsCardinalLocallyPresentable.iff_exists_isStrongGenerator]
  exact ⟨.singleton PUnit, inferInstance, isStrongGenerator_punit, by
    simp only [ObjectProperty.singleton_le_iff,
      CategoryTheory.isCardinalPresentable_iff, isCardinalPresentable_iff]
    exact hasCardinalLT_of_finite _ _ (Cardinal.IsRegular.aleph0_le Fact.out)⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsLocallyPresentable.{u} (Type u)
  body: ⟨_, Cardinal.fact_isRegular_aleph0, inferInstance⟩

中文:
实例 :
  签名: 是LocallyPresentable.{u} (类型u)
  定义体: ⟨_, Cardinal.fact_isRegular_aleph0, inferInstance⟩

Depends on / 依赖: Cardinal, Cardinal.fact_isRegular_aleph0, fact_isRegular_aleph0
-/
instance : IsLocallyPresentable.{u} (Type u) where
  exists_cardinal := ⟨_, Cardinal.fact_isRegular_aleph0, inferInstance⟩

end Types

end CategoryTheory
