/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Shapes.WideEqualizers
public import Mathlib.CategoryTheory.Comma.CardinalArrow
public import Mathlib.SetTheory.Cardinal.Cofinality.Ordinal
public import Mathlib.SetTheory.Cardinal.HasCardinalLT
public import Mathlib.SetTheory.Cardinal.Arithmetic

/-! # κ-filtered category

If `κ` is a regular cardinal, we introduce the notion of `κ`-filtered
category `J`: it means that any functor `A ⥤ J` from a small category such
that `Arrow A` is of cardinality `< κ` admits a cocone.
This generalizes the notion of filtered category.
Indeed, we obtain the equivalence `IsCardinalFiltered J ℵ₀ ↔ IsFiltered J`.
The API is mostly parallel to that of filtered categories.

A preordered type `J` is a `κ`-filtered category (i.e. `κ`-directed set)
if any subset of `J` of cardinality `< κ` has an upper bound.

## References
* [Adámek, J. and Rosický, J., *Locally presentable and accessible categories*][Adamek_Rosicky_1994]

-/

@[expose] public section

universe w v' v u' u

namespace CategoryTheory

open Limits Opposite

/--
Definition of `IsCardinalFiltered` / `IsCardinalFiltered` 的定义

English:
class IsCardinalFiltered
  parameters: (J : Type u) [Category.{v} J]
  axioms and operations (1):
    - nonempty_cocone({A : Type w} [SmallCategory A] (F : A ⥤ J) (hA : HasCardinalLT (Arrow A) κ)) : Nonempty (Cocone F)

中文:
类 IsCardinalFiltered
  参数: (J : 类型u) [Category.{v} J]
  公理与运算 (1 个):
    - nonempty_cocone({A : Type w} [SmallCategory A] (F : A ⥤ J) (hA : HasCardinalLT (Arrow A) κ)) : Nonempty (Cocone F)
-/
class IsCardinalFiltered (J : Type u) [Category.{v} J]
    (κ : Cardinal.{w}) [Fact κ.IsRegular] : Prop where
  nonempty_cocone {A : Type w} [SmallCategory A] (F : A ⥤ J)
    (hA : HasCardinalLT (Arrow A) κ) : Nonempty (Cocone F)

/--
lemma `hasCardinalLT_arrow_walkingParallelFamily` / 引理 `hasCardinalLT_arrow_walkingParallelFamily`

English:
lemma hasCardinalLT_arrow_walkingParallelFamily
  statement: {T : Type u}
  proof: by
  simpa only [hasCardinalLT_iff_of_equiv (WalkingParallelFamily.arrowEquiv T),
    hasCardinalLT_option_iff _ _ hκ] using hT

中文:
引理 hasCardinalLT_arrow_walkingParallelFamily
  结论: {T : 类型u}
  证明: by
  simpa only [hasCardinalLT_iff_of_equiv (WalkingParallelFamily.arrowEquiv T),
    hasCardinalLT_option_iff _ _ hκ] using hT

Depends on / 依赖: WalkingParallelFamily, WalkingParallelFamily.arrowEquiv, arrowEquiv, hasCardinalLT_iff_of_equiv, hasCardinalLT_option_iff
-/
lemma hasCardinalLT_arrow_walkingParallelFamily {T : Type u}
    {κ : Cardinal.{w}} (hT : HasCardinalLT T κ) (hκ : Cardinal.aleph0 <= κ) :
    HasCardinalLT (Arrow (WalkingParallelFamily T)) κ := by
  simpa only [hasCardinalLT_iff_of_equiv (WalkingParallelFamily.arrowEquiv T),
    hasCardinalLT_option_iff _ _ hκ] using hT

namespace IsCardinalFiltered

variable {J : Type u} [Category.{v} J] {κ : Cardinal.{w}} [hκ : Fact κ.IsRegular]
  [IsCardinalFiltered J κ]

/--
Definition of `cocone` / `cocone` 的定义

English:
definition cocone
  signature: {A : Type v'} [Category.{u'} A]
  body: by
  have := hA.small
  have := small_of_small_arrow.{w} A
  have := locallySmall_of_small_arrow.{w} A
  let e := (Shrink.equivalence.{w} A).trans (ShrinkHoms.equivalence.{w} (Shrink.{w} A))
  exact (Cocone.equivalenceOfReindexing e.symm (Iso.refl _)).inverse.obj
    (nonempty_cocone (κ := κ) (e.inv

中文:
定义 cocone
  签名: {A : 类型v'} [Category.{u'} A]
  定义体: by
  have := hA.small
  have := small_of_small_arrow.{w} A
  have := locallySmall_of_small_arrow.{w} A
  let e := (Shrink.equivalence.{w} A).trans (ShrinkHoms.equivalence.{w} (Shrink.{w} A))
  exact (Cocone.equivalenceOfReindexing e.symm (Iso.refl _)).inverse.obj
    (nonempty_cocone (κ := κ) (e.inv

Depends on / 依赖: Cocone, Cocone.equivalenceOfReindexing, Iso.refl, Shrink, Shrink.equivalence, ShrinkHoms, ShrinkHoms.equivalence, e.inverse, e.symm, equivalence, equivalenceOfReindexing, hA.small, inverse, inverse.obj, locallySmall_of_small_arrow, nonempty_cocone, small_of_small_arrow
-/
noncomputable def cocone {A : Type v'} [Category.{u'} A]
    (F : A ⥤ J) (hA : HasCardinalLT (Arrow A) κ) :
    Cocone F := by
  have := hA.small
  have := small_of_small_arrow.{w} A
  have := locallySmall_of_small_arrow.{w} A
  let e := (Shrink.equivalence.{w} A).trans (ShrinkHoms.equivalence.{w} (Shrink.{w} A))
  exact (Cocone.equivalenceOfReindexing e.symm (Iso.refl _)).inverse.obj
    (nonempty_cocone (κ := κ) (e.inverse ⋙ F) (by simpa)).some

variable (J) in
/--
lemma `of_le` / 引理 `of_le`

English:
lemma of_le
  given: {κ' : Cardinal.{w}} [Fact κ'.IsRegular] (h : κ' <= κ)
  proof: ⟨cocone F (hA.of_le h)⟩

中文:
引理 of_le
  条件: {κ' : Cardinal.{w}} [Fact κ'.IsRegular] (h : κ' <= κ)
  证明: ⟨cocone F (hA.of_le h)⟩

Depends on / 依赖: cocone, hA.of_le, of_le
-/
lemma of_le {κ' : Cardinal.{w}} [Fact κ'.IsRegular] (h : κ' <= κ) :
    IsCardinalFiltered J κ' where
  nonempty_cocone F hA := ⟨cocone F (hA.of_le h)⟩

variable (κ) in
/--
lemma `of_equivalence` / 引理 `of_equivalence`

English:
lemma of_equivalence
  given: {J' : Type u'} [Category.{v'} J'] (e : J ≌ J')
  proof: ⟨e.inverse.mapCoconeInv (cocone (F ⋙ e.inverse) hA)⟩

中文:
引理 of_equivalence
  条件: {J' : 类型u'} [Category.{v'} J'] (e : J ≌ J')
  证明: ⟨e.inverse.mapCoconeInv (cocone (F ⋙ e.inverse) hA)⟩

Depends on / 依赖: IsLoopAt, cocone, e.inverse, e.inverse.mapCoconeInv, eq_of_isLink, inverse, mapCoconeInv
-/
lemma of_equivalence {J' : Type u'} [Category.{v'} J'] (e : J ≌ J') :
    IsCardinalFiltered J' κ where
  nonempty_cocone F hA := ⟨e.inverse.mapCoconeInv (cocone (F ⋙ e.inverse) hA)⟩

section max

variable {K : Type u'} (S : K -> J) (hS : HasCardinalLT K κ)

/--
Definition of `max` / `max` 的定义

English:
definition max
  signature: : J
  body: (cocone (κ := κ) (Discrete.functor S) (by simpa using hS)).pt

中文:
定义 max
  签名: : J
  定义体: (cocone (κ := κ) (Discrete.functor S) (by simpa using hS)).pt

Depends on / 依赖: Discrete, Discrete.functor, cocone, functor
-/
noncomputable def max : J :=
  (cocone (κ := κ) (Discrete.functor S) (by simpa using hS)).pt

/--
Definition of `toMax` / `toMax` 的定义

English:
definition toMax
  signature: (k : K)
  body: (cocone (κ := κ) (Discrete.functor S) (by simpa using hS)).ι.app ⟨k⟩

中文:
定义 toMax
  签名: (k : K)
  定义体: (cocone (κ := κ) (Discrete.functor S) (by simpa using hS)).ι.app ⟨k⟩

Depends on / 依赖: Discrete, Discrete.functor, cocone, functor
-/
noncomputable def toMax (k : K) :
    S k ⟶ max S hS :=
  (cocone (κ := κ) (Discrete.functor S) (by simpa using hS)).ι.app ⟨k⟩

end max

section coeq

variable {K : Type v'} {j j' : J} (f : K -> (j ⟶ j')) (hK : HasCardinalLT K κ)

/--
Definition of `coeq` / `coeq` 的定义

English:
definition coeq
  signature: : J
  body: (cocone (parallelFamily f)
    (hasCardinalLT_arrow_walkingParallelFamily hK hκ.out.aleph0_le)).pt

中文:
定义 coeq
  签名: : J
  定义体: (cocone (parallelFamily f)
    (hasCardinalLT_arrow_walkingParallelFamily hK hκ.out.aleph0_le)).pt

Depends on / 依赖: aleph0_le, cocone, hasCardinalLT_arrow_walkingParallelFamily, out.aleph0_le, parallelFamily
-/
noncomputable def coeq : J :=
  (cocone (parallelFamily f)
    (hasCardinalLT_arrow_walkingParallelFamily hK hκ.out.aleph0_le)).pt

/--
Definition of `coeqHom` / `coeqHom` 的定义

English:
definition coeqHom
  signature: : j' ⟶ coeq f hK
  body: (cocone (parallelFamily f)
    (hasCardinalLT_arrow_walkingParallelFamily hK hκ.out.aleph0_le)).ι.app .one

中文:
定义 coeqHom
  签名: : j' ⟶ coeq f hK
  定义体: (cocone (parallelFamily f)
    (hasCardinalLT_arrow_walkingParallelFamily hK hκ.out.aleph0_le)).ι.app .one

Depends on / 依赖: aleph0_le, cocone, hasCardinalLT_arrow_walkingParallelFamily, out.aleph0_le, parallelFamily
-/
noncomputable def coeqHom : j' ⟶ coeq f hK :=
  (cocone (parallelFamily f)
    (hasCardinalLT_arrow_walkingParallelFamily hK hκ.out.aleph0_le)).ι.app .one

/--
Definition of `toCoeq` / `toCoeq` 的定义

English:
definition toCoeq
  signature: : j ⟶ coeq f hK
  body: (cocone (parallelFamily f)
    (hasCardinalLT_arrow_walkingParallelFamily hK hκ.out.aleph0_le)).ι.app .zero

@[reassoc]

中文:
定义 toCoeq
  签名: : j ⟶ coeq f hK
  定义体: (cocone (parallelFamily f)
    (hasCardinalLT_arrow_walkingParallelFamily hK hκ.out.aleph0_le)).ι.app .zero

@[reassoc]

Depends on / 依赖: aleph0_le, cocone, hasCardinalLT_arrow_walkingParallelFamily, out.aleph0_le, parallelFamily
-/
noncomputable def toCoeq : j ⟶ coeq f hK :=
  (cocone (parallelFamily f)
    (hasCardinalLT_arrow_walkingParallelFamily hK hκ.out.aleph0_le)).ι.app .zero

@[reassoc]
/--
lemma `coeq_condition` / 引理 `coeq_condition`

English:
lemma coeq_condition
  given: (k : K)
  statement: f k ≫ coeqHom f hK = toCoeq f hK
  proof: (cocone (parallelFamily f)
    (hasCardinalLT_arrow_walkingParallelFamily hK hκ.out.aleph0_le)).w
    (.line k)

中文:
引理 coeq_condition
  条件: (k : K)
  结论: f k ≫ coeqHom f hK = toCoeq f hK
  证明: (cocone (parallelFamily f)
    (hasCardinalLT_arrow_walkingParallelFamily hK hκ.out.aleph0_le)).w
    (.line k)

Depends on / 依赖: aleph0_le, cocone, hasCardinalLT_arrow_walkingParallelFamily, out.aleph0_le, parallelFamily
-/
lemma coeq_condition (k : K) : f k ≫ coeqHom f hK = toCoeq f hK :=
  (cocone (parallelFamily f)
    (hasCardinalLT_arrow_walkingParallelFamily hK hκ.out.aleph0_le)).w
    (.line k)

end coeq

/--
lemma `wideSpan` / 引理 `wideSpan`

English:
lemma wideSpan
  statement: {ι : Type v'} {j : J} {k : ι -> J}
  proof: by
  let φ (i : ι) := f i ≫ toMax k hι i
  exact ⟨coeq φ hι, fun i => toMax k hι i ≫ coeqHom φ hι,
    toCoeq φ hι, by simpa [φ] using coeq_condition φ hι⟩

中文:
引理 wideSpan
  结论: {ι : 类型v'} {j : J} {k : ι -> J}
  证明: by
  let φ (i : ι) := f i ≫ toMax k hι i
  exact ⟨coeq φ hι, fun i => toMax k hι i ≫ coeqHom φ hι,
    toCoeq φ hι, by simpa [φ] using coeq_condition φ hι⟩

Depends on / 依赖: coeqHom, coeq_condition, toCoeq
-/
lemma wideSpan {ι : Type v'} {j : J} {k : ι -> J}
    (f : forall i, j ⟶ k i) (hι : HasCardinalLT ι κ) :
    exists (m : J) (a : forall i, k i ⟶ m) (b : j ⟶ m), forall i, f i ≫ a i = b := by
  let φ (i : ι) := f i ≫ toMax k hι i
  exact ⟨coeq φ hι, fun i => toMax k hι i ≫ coeqHom φ hι,
    toCoeq φ hι, by simpa [φ] using coeq_condition φ hι⟩

end IsCardinalFiltered

open IsCardinalFiltered in
/--
lemma `isFiltered_of_isCardinalFiltered` / 引理 `isFiltered_of_isCardinalFiltered`

English:
lemma isFiltered_of_isCardinalFiltered
  statement: (J : Type u) [Category.{v} J]
  proof: by
  rw [IsFiltered.iff_cocone_nonempty.{w}]
  intro A _ _ F
  have hA : HasCardinalLT (Arrow A) κ := by
    refine HasCardinalLT.of_le ?_ hκ.out.aleph0_le
    simp only [hasCardinalLT_aleph0_iff]
    infer_instance
  exact ⟨cocone F hA⟩

中文:
引理 isFiltered_of_isCardinalFiltered
  结论: (J : 类型u) [Category.{v} J]
  证明: by
  rw [IsFiltered.iff_cocone_nonempty.{w}]
  intro A _ _ F
  have hA : HasCardinalLT (Arrow A) κ := by
    refine HasCardinalLT.of_le ?_ hκ.out.aleph0_le
    simp only [hasCardinalLT_aleph0_iff]
    infer_instance
  exact ⟨cocone F hA⟩

Depends on / 依赖: HasCardinalLT, HasCardinalLT.of_le, IsFiltered, IsFiltered.iff_cocone_nonempty, aleph0_le, cocone, hasCardinalLT_aleph0_iff, iff_cocone_nonempty, infer_instance, of_le, out.aleph0_le
-/
lemma isFiltered_of_isCardinalFiltered (J : Type u) [Category.{v} J]
    (κ : Cardinal.{w}) [hκ : Fact κ.IsRegular] [IsCardinalFiltered J κ] :
    IsFiltered J := by
  rw [IsFiltered.iff_cocone_nonempty.{w}]
  intro A _ _ F
  have hA : HasCardinalLT (Arrow A) κ := by
    refine HasCardinalLT.of_le ?_ hκ.out.aleph0_le
    simp only [hasCardinalLT_aleph0_iff]
    infer_instance
  exact ⟨cocone F hA⟩

/--
lemma `IsCardinalFiltered.nonempty` / 引理 `IsCardinalFiltered.nonempty`

English:
lemma IsCardinalFiltered.nonempty
  statement: (J : Type u) [Category.{v} J]
  proof: have := isFiltered_of_isCardinalFiltered J κ
  IsFiltered.nonempty

中文:
引理 IsCardinalFiltered.nonempty
  结论: (J : 类型u) [Category.{v} J]
  证明: have := isFiltered_of_isCardinalFiltered J κ
  IsFiltered.nonempty

Depends on / 依赖: IsFiltered, IsFiltered.nonempty, isFiltered_of_isCardinalFiltered, nonempty
-/
lemma IsCardinalFiltered.nonempty (J : Type u) [Category.{v} J]
    (κ : Cardinal.{w}) [hκ : Fact κ.IsRegular] [IsCardinalFiltered J κ] : Nonempty J :=
  have := isFiltered_of_isCardinalFiltered J κ
  IsFiltered.nonempty

attribute [local instance] Cardinal.fact_isRegular_aleph0

/--
lemma `isCardinalFiltered_aleph0_iff` / 引理 `isCardinalFiltered_aleph0_iff`

English:
lemma isCardinalFiltered_aleph0_iff
  given: (J : Type u) [Category.{v} J]
  proof: by
  constructor
  · intro
    exact isFiltered_of_isCardinalFiltered J Cardinal.aleph0
  · intro
    constructor
    intro A _ F hA
    rw [hasCardinalLT_aleph0_iff] at hA
    have := ((Arrow.finite_iff A).1 hA).some
    exact ⟨IsFiltered.cocone F⟩

中文:
引理 isCardinalFiltered_aleph0_iff
  条件: (J : 类型u) [Category.{v} J]
  证明: by
  constructor
  · intro
    exact isFiltered_of_isCardinalFiltered J Cardinal.aleph0
  · intro
    constructor
    intro A _ F hA
    rw [hasCardinalLT_aleph0_iff] at hA
    have := ((Arrow.finite_iff A).1 hA).some
    exact ⟨IsFiltered.cocone F⟩

Depends on / 依赖: Arrow.finite_iff, Cardinal, Cardinal.aleph0, IsFiltered, IsFiltered.cocone, aleph0, cocone, finite_iff, hasCardinalLT_aleph0_iff, isFiltered_of_isCardinalFiltered
-/
lemma isCardinalFiltered_aleph0_iff (J : Type u) [Category.{v} J] :
    IsCardinalFiltered J Cardinal.aleph0.{w} ↔ IsFiltered J := by
  constructor
  · intro
    exact isFiltered_of_isCardinalFiltered J Cardinal.aleph0
  · intro
    constructor
    intro A _ F hA
    rw [hasCardinalLT_aleph0_iff] at hA
    have := ((Arrow.finite_iff A).1 hA).some
    exact ⟨IsFiltered.cocone F⟩

-- TODO: make a version specialized to linear orders.
-- In a linear order, `h` is equivalent to `κ ≤ Order.cof J`
/--
lemma `isCardinalFiltered_preorder` / 引理 `isCardinalFiltered_preorder`

English:
lemma isCardinalFiltered_preorder
  statement: (J : Type w) [Preorder J]
  proof: by
    obtain ⟨j, hj⟩ := h F.obj (by simpa only [hasCardinalLT_iff_cardinal_mk_lt] using
        hasCardinalLT_of_hasCardinalLT_arrow hA)
    exact ⟨Cocone.mk j
      { app a := homOfLE (hj a)
        naturality _ _ _ := rfl }⟩

中文:
引理 isCardinalFiltered_preorder
  结论: (J : Type w) [Preorder J]
  证明: by
    obtain ⟨j, hj⟩ := h F.obj (by simpa only [hasCardinalLT_iff_cardinal_mk_lt] using
        hasCardinalLT_of_hasCardinalLT_arrow hA)
    exact ⟨Cocone.mk j
      { app a := homOfLE (hj a)
        naturality _ _ _ := rfl }⟩

Depends on / 依赖: Cocone, Cocone.mk, F.obj, hasCardinalLT_iff_cardinal_mk_lt, hasCardinalLT_of_hasCardinalLT_arrow, homOfLE, naturality
-/
lemma isCardinalFiltered_preorder (J : Type w) [Preorder J]
    (κ : Cardinal.{w}) [Fact κ.IsRegular]
    (h : forall ⦃K : Type w⦄ (s : K -> J) (_ : Cardinal.mk K < κ),
      exists (j : J), forall (k : K), s k <= j) :
    IsCardinalFiltered J κ where
  nonempty_cocone {A _ F hA} := by
    obtain ⟨j, hj⟩ := h F.obj (by simpa only [hasCardinalLT_iff_cardinal_mk_lt] using
        hasCardinalLT_of_hasCardinalLT_arrow hA)
    exact ⟨Cocone.mk j
      { app a := homOfLE (hj a)
        naturality _ _ _ := rfl }⟩

set_option backward.isDefEq.respectTransparency.types false in
instance (κ : Cardinal.{w}) [hκ : Fact κ.IsRegular] :
    IsCardinalFiltered κ.ord.ToType κ :=
  isCardinalFiltered_preorder _ _ (fun ι f hs => by
    have h : Function.Surjective (fun i => (⟨f i, i, rfl⟩ : Set.range f)) := fun _ => by aesop
    contrapose! hs
    rw [← hκ.out.cof_ord]; rw [← Ordinal.cof_toType]
    refine (Order.cof_le fun j => ?_).trans (Cardinal.mk_le_of_surjective h)
    obtain ⟨k, hk⟩ := hs j
    exact ⟨_, Set.mem_range_self k, hk.le⟩)

open IsCardinalFiltered

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Instance `isCardinalFiltered_under` / 实例 `isCardinalFiltered_under`

English:
instance isCardinalFiltered_under
  body: ⟨by
    have := isFiltered_of_isCardinalFiltered J κ
    let c := cocone (F ⋙ Under.forget j₀) hA
    let x (a : A) : j₀ ⟶ IsFiltered.max j₀ c.pt := (F.obj a).hom ≫ c.ι.app a ≫
      IsFiltered.rightToMax j₀ c.pt
    have hκ' : HasCardinalLT A κ := hasCardinalLT_of_hasCardinalLT_arrow hA
    exact
 

中文:
实例 isCardinalFiltered_under
  定义体: ⟨by
    have := isFiltered_of_isCardinalFiltered J κ
    let c := cocone (F ⋙ Under.forget j₀) hA
    let x (a : A) : j₀ ⟶ IsFiltered.max j₀ c.pt := (F.obj a).hom ≫ c.ι.app a ≫
      IsFiltered.rightToMax j₀ c.pt
    have hκ' : HasCardinalLT A κ := hasCardinalLT_of_hasCardinalLT_arrow hA
    exact
 

Depends on / 依赖: F.obj, HasCardinalLT, IsFiltered, IsFiltered.max, IsFiltered.rightToMax, Under.forget, Under.homMk, Under.mk, c.pt, cocone, coeqHom, coeq_condition, forget, hasCardinalLT_of_hasCardinalLT_arrow, isFiltered_of_isCardinalFiltered, naturality, rightToMax, toCoeq
-/
instance isCardinalFiltered_under
    (J : Type u) [Category.{v} J] (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [IsCardinalFiltered J κ] (j₀ : J) : IsCardinalFiltered (Under j₀) κ where
  nonempty_cocone {A _} F hA := ⟨by
    have := isFiltered_of_isCardinalFiltered J κ
    let c := cocone (F ⋙ Under.forget j₀) hA
    let x (a : A) : j₀ ⟶ IsFiltered.max j₀ c.pt := (F.obj a).hom ≫ c.ι.app a ≫
      IsFiltered.rightToMax j₀ c.pt
    have hκ' : HasCardinalLT A κ := hasCardinalLT_of_hasCardinalLT_arrow hA
    exact
      { pt := Under.mk (toCoeq x hκ')
        ι :=
          { app a := Under.homMk (c.ι.app a ≫ IsFiltered.rightToMax j₀ c.pt ≫ coeqHom x hκ')
              (by simpa [x] using coeq_condition x hκ' a)
            naturality a b f := by
              ext
              have := c.w f
              dsimp at this ⊢
              simp only [reassoc_of% this, Category.comp_id] } }⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Instance `isCardinalFiltered_prod` / 实例 `isCardinalFiltered_prod`

English:
instance isCardinalFiltered_prod
  signature: (J₁ : Type u) (J₂ : Type u')
  body: ⟨by
    let c₁ := cocone (F ⋙ Prod.fst _ _) hC
    let c₂ := cocone (F ⋙ Prod.snd _ _) hC
    exact
      { pt := (c₁.pt, c₂.pt)
        ι.app i := (c₁.ι.app i, c₂.ι.app i)
        ι.naturality {i j} f := by
          ext
          · simpa using c₁.w f
          · simpa using c₂.w f }⟩

中文:
实例 isCardinalFiltered_prod
  签名: (J₁ : 类型u) (J₂ : 类型u')
  定义体: ⟨by
    let c₁ := cocone (F ⋙ Prod.fst _ _) hC
    let c₂ := cocone (F ⋙ Prod.snd _ _) hC
    exact
      { pt := (c₁.pt, c₂.pt)
        ι.app i := (c₁.ι.app i, c₂.ι.app i)
        ι.naturality {i j} f := by
          ext
          · simpa using c₁.w f
          · simpa using c₂.w f }⟩

Depends on / 依赖: Prod.fst, Prod.snd, cocone, naturality
-/
instance isCardinalFiltered_prod (J₁ : Type u) (J₂ : Type u')
    [Category.{v} J₁] [Category.{v'} J₂] (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [IsCardinalFiltered J₁ κ] [IsCardinalFiltered J₂ κ] :
    IsCardinalFiltered (J₁ × J₂) κ where
  nonempty_cocone F hC := ⟨by
    let c₁ := cocone (F ⋙ Prod.fst _ _) hC
    let c₂ := cocone (F ⋙ Prod.snd _ _) hC
    exact
      { pt := (c₁.pt, c₂.pt)
        ι.app i := (c₁.ι.app i, c₂.ι.app i)
        ι.naturality {i j} f := by
          ext
          · simpa using c₁.w f
          · simpa using c₂.w f }⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `isCardinalFiltered_pi` / 实例 `isCardinalFiltered_pi`

English:
instance isCardinalFiltered_pi
  signature: {ι : Type u'} (J : ι -> Type u) [forall i, Category.{v} (J i)]
  body: ⟨by
    let c (i : ι) := cocone (F ⋙ Pi.eval J i) hC
    exact
      { pt i := (c i).pt
        ι.app X i := (c i).ι.app X
        ι.naturality {X Y} f := by
          ext i
          simpa using! (c i).ι.naturality f }⟩

中文:
实例 isCardinalFiltered_pi
  签名: {ι : 类型u'} (J : ι -> 类型u) [对任意 i, Category.{v} (J i)]
  定义体: ⟨by
    let c (i : ι) := cocone (F ⋙ Pi.eval J i) hC
    exact
      { pt i := (c i).pt
        ι.app X i := (c i).ι.app X
        ι.naturality {X Y} f := by
          ext i
          simpa using! (c i).ι.naturality f }⟩

Depends on / 依赖: Pi.eval, cocone, naturality
-/
instance isCardinalFiltered_pi {ι : Type u'} (J : ι -> Type u) [forall i, Category.{v} (J i)]
    (κ : Cardinal.{w}) [Fact κ.IsRegular] [forall i, IsCardinalFiltered (J i) κ] :
    IsCardinalFiltered (forall i, J i) κ where
  nonempty_cocone F hC := ⟨by
    let c (i : ι) := cocone (F ⋙ Pi.eval J i) hC
    exact
      { pt i := (c i).pt
        ι.app X i := (c i).ι.app X
        ι.naturality {X Y} f := by
          ext i
          simpa using! (c i).ι.naturality f }⟩

section

variable {J : Type u} [Category.{v} J] {κ : Cardinal.{w}} [Fact κ.IsRegular]
  (h₁ : (forall ⦃ι : Type w⦄ (j : ι -> J) (_ : HasCardinalLT ι κ),
          exists (k : J), forall (i : ι), Nonempty (j i ⟶ k)))
  (h₂ : forall ⦃ι : Type w⦄ ⦃j k : J⦄ (f : ι -> (j ⟶ k)) (_ : HasCardinalLT ι κ),
      exists (l : J) (a : k ⟶ l) (b : j ⟶ l), forall (i : ι), f i ≫ a = b)

include h₁ h₂ in
omit [Fact κ.IsRegular] in
/--
lemma `isCardinalFiltered_iff_aux₁` / 引理 `isCardinalFiltered_iff_aux₁`

English:
lemma isCardinalFiltered_iff_aux₁
  statement: {ι : Type w} {j : J} {k : ι -> J}
  proof: by
  obtain ⟨l, hl⟩ := h₁ k hι
  let a (i : ι) := (hl i).some
  obtain ⟨m, b, c, hm⟩ := h₂ (fun i => f i ≫ a i) hι
  exact ⟨m, fun i => a i ≫ b, c, by grind⟩

include h₁ h₂ in

中文:
引理 isCardinalFiltered_iff_aux₁
  结论: {ι : Type w} {j : J} {k : ι -> J}
  证明: by
  obtain ⟨l, hl⟩ := h₁ k hι
  let a (i : ι) := (hl i).some
  obtain ⟨m, b, c, hm⟩ := h₂ (fun i => f i ≫ a i) hι
  exact ⟨m, fun i => a i ≫ b, c, by grind⟩

include h₁ h₂ in
-/
lemma isCardinalFiltered_iff_aux₁ {ι : Type w} {j : J} {k : ι -> J}
    (f : forall i, j ⟶ k i) (hι : HasCardinalLT ι κ) :
    exists (m : J) (a : forall i, k i ⟶ m) (b : j ⟶ m), forall i, f i ≫ a i = b := by
  obtain ⟨l, hl⟩ := h₁ k hι
  let a (i : ι) := (hl i).some
  obtain ⟨m, b, c, hm⟩ := h₂ (fun i => f i ≫ a i) hι
  exact ⟨m, fun i => a i ≫ b, c, by grind⟩

include h₁ h₂ in
/--
lemma `isCardinalFiltered_iff_aux₂` / 引理 `isCardinalFiltered_iff_aux₂`

English:
lemma isCardinalFiltered_iff_aux₂
  statement: {ι : Type w} {j : ι -> J} {k : J}
  proof: by
  have (i : ι) : exists (l : J) (p : k ⟶ l), f₁ i ≫ p = f₂ i ≫ p := by
    obtain ⟨l, a, b, hl⟩ := h₂ (Sum.elim (fun (_ : PUnit.{w + 1}) => f₁ i)
      (fun (_ : PUnit.{w + 1}) => f₂ i))
        (hasCardinalLT_of_finite _ _ (Cardinal.IsRegular.aleph0_le Fact.out))
    exact ⟨l, a, (hl (Sum.inl .u

中文:
引理 isCardinalFiltered_iff_aux₂
  结论: {ι : Type w} {j : ι -> J} {k : J}
  证明: by
  have (i : ι) : exists (l : J) (p : k ⟶ l), f₁ i ≫ p = f₂ i ≫ p := by
    obtain ⟨l, a, b, hl⟩ := h₂ (Sum.elim (fun (_ : PUnit.{w + 1}) => f₁ i)
      (fun (_ : PUnit.{w + 1}) => f₂ i))
        (hasCardinalLT_of_finite _ _ (Cardinal.IsRegular.aleph0_le Fact.out))
    exact ⟨l, a, (hl (Sum.inl .u

Depends on / 依赖: Cardinal, Cardinal.IsRegular.aleph0_le, Fact.out, IsRegular, Sum.elim, Sum.inl, Sum.inr, aleph0_le, hasCardinalLT_of_finite
-/
lemma isCardinalFiltered_iff_aux₂ {ι : Type w} {j : ι -> J} {k : J}
    (f₁ f₂ : forall i, j i ⟶ k) (hι : HasCardinalLT ι κ) :
    exists (l : J) (a : k ⟶ l), forall i, f₁ i ≫ a = f₂ i ≫ a := by
  have (i : ι) : exists (l : J) (p : k ⟶ l), f₁ i ≫ p = f₂ i ≫ p := by
    obtain ⟨l, a, b, hl⟩ := h₂ (Sum.elim (fun (_ : PUnit.{w + 1}) => f₁ i)
      (fun (_ : PUnit.{w + 1}) => f₂ i))
        (hasCardinalLT_of_finite _ _ (Cardinal.IsRegular.aleph0_le Fact.out))
    exact ⟨l, a, (hl (Sum.inl .unit)).trans (hl (Sum.inr .unit)).symm⟩
  choose l p hp using this
  obtain ⟨l, a, b, h⟩ := isCardinalFiltered_iff_aux₁ h₁ h₂ p hι
  exact ⟨l, b, fun i => by grind⟩

set_option backward.defeqAttrib.useBackward true in
variable (J κ) in
/--
lemma `isCardinalFiltered_iff` / 引理 `isCardinalFiltered_iff`

English:
lemma isCardinalFiltered_iff
  proof: by
  refine ⟨fun _ => ⟨fun ι j hι => ⟨_, fun i => ⟨toMax j hι i⟩⟩,
    fun ι j k f hι => ⟨_, _, _, coeq_condition f hι⟩⟩,
    fun ⟨h₁, h₂⟩ => ⟨fun {A _} F hA => ?_⟩⟩
  obtain ⟨j, hj⟩ := h₁ F.obj (hasCardinalLT_of_hasCardinalLT_arrow hA)
  let a (i : A) : F.obj i ⟶ j := (hj i).some
  obtain ⟨l, b, hb

中文:
引理 isCardinalFiltered_iff
  证明: by
  refine ⟨fun _ => ⟨fun ι j hι => ⟨_, fun i => ⟨toMax j hι i⟩⟩,
    fun ι j k f hι => ⟨_, _, _, coeq_condition f hι⟩⟩,
    fun ⟨h₁, h₂⟩ => ⟨fun {A _} F hA => ?_⟩⟩
  obtain ⟨j, hj⟩ := h₁ F.obj (hasCardinalLT_of_hasCardinalLT_arrow hA)
  let a (i : A) : F.obj i ⟶ j := (hj i).some
  obtain ⟨l, b, hb

Depends on / 依赖: Arrow.mk, F.map, F.obj, coeq_condition, f.hom, f.left, f.right, hasCardinalLT_of_hasCardinalLT_arrow, naturality
-/
lemma isCardinalFiltered_iff :
    IsCardinalFiltered J κ ↔
      (forall ⦃ι : Type w⦄ (j : ι -> J) (_ : HasCardinalLT ι κ),
        exists (k : J), forall (i : ι), Nonempty (j i ⟶ k)) ∧
      forall ⦃ι : Type w⦄ ⦃j k : J⦄ (f : ι -> (j ⟶ k)) (_ : HasCardinalLT ι κ),
        exists (l : J) (a : k ⟶ l) (b : j ⟶ l), forall (i : ι), f i ≫ a = b := by
  refine ⟨fun _ => ⟨fun ι j hι => ⟨_, fun i => ⟨toMax j hι i⟩⟩,
    fun ι j k f hι => ⟨_, _, _, coeq_condition f hι⟩⟩,
    fun ⟨h₁, h₂⟩ => ⟨fun {A _} F hA => ?_⟩⟩
  obtain ⟨j, hj⟩ := h₁ F.obj (hasCardinalLT_of_hasCardinalLT_arrow hA)
  let a (i : A) : F.obj i ⟶ j := (hj i).some
  obtain ⟨l, b, hb⟩ := isCardinalFiltered_iff_aux₂ h₁ h₂
    (fun (f : Arrow A) => F.map f.hom ≫ a f.right)
    (fun (f : Arrow A) => a f.left) hA
  exact ⟨{
    pt := l
    ι.app i := a i ≫ b
    ι.naturality _ _ f := by simpa using hb (Arrow.mk f) }⟩

end

/--
lemma `IsCardinalFiltered.multicoequalizer` / 引理 `IsCardinalFiltered.multicoequalizer`

English:
lemma IsCardinalFiltered.multicoequalizer
  proof: by
  have := isFiltered_of_isCardinalFiltered J κ
  obtain ⟨l, a, b, h⟩ := IsCardinalFiltered.wideSpan
    (fun i => IsFiltered.coeqHom (f₁ i) (f₂ i)) hι
  exact ⟨l, b, fun i => by rw [← h i, IsFiltered.coeq_condition_assoc]⟩

中文:
引理 IsCardinalFiltered.multicoequalizer
  证明: by
  have := isFiltered_of_isCardinalFiltered J κ
  obtain ⟨l, a, b, h⟩ := IsCardinalFiltered.wideSpan
    (fun i => IsFiltered.coeqHom (f₁ i) (f₂ i)) hι
  exact ⟨l, b, fun i => by rw [← h i, IsFiltered.coeq_condition_assoc]⟩

Depends on / 依赖: IsCardinalFiltered, IsCardinalFiltered.wideSpan, IsFiltered, IsFiltered.coeqHom, IsFiltered.coeq_condition_assoc, coeqHom, coeq_condition_assoc, isFiltered_of_isCardinalFiltered, wideSpan
-/
lemma IsCardinalFiltered.multicoequalizer
    {J : Type u} [Category.{v} J] {κ : Cardinal.{w}} [Fact κ.IsRegular]
    [IsCardinalFiltered J κ] {ι : Type v'} {j : ι -> J} {k : J}
    (f₁ f₂ : forall i, j i ⟶ k) (hι : HasCardinalLT ι κ) :
    exists (l : J) (a : k ⟶ l), forall i, f₁ i ≫ a = f₂ i ≫ a := by
  have := isFiltered_of_isCardinalFiltered J κ
  obtain ⟨l, a, b, h⟩ := IsCardinalFiltered.wideSpan
    (fun i => IsFiltered.coeqHom (f₁ i) (f₂ i)) hι
  exact ⟨l, b, fun i => by rw [← h i, IsFiltered.coeq_condition_assoc]⟩

/--
lemma `IsCardinalFiltered.of_final` / 引理 `IsCardinalFiltered.of_final`

English:
lemma IsCardinalFiltered.of_final
  proof: by
  have := isFiltered_of_isCardinalFiltered J₁ κ
  obtain ⟨h₁, h₂⟩ := (Functor.final_iff_of_isFiltered F).1 inferInstance
  rw [isCardinalFiltered_iff]
  refine ⟨fun ι j hι => ?_, fun ι j k f hι => ?_⟩
  · choose a ha using fun i => h₁ (j i)
    exact ⟨F.obj (IsCardinalFiltered.max a hι),
      fu

中文:
引理 IsCardinalFiltered.of_final
  证明: by
  have := isFiltered_of_isCardinalFiltered J₁ κ
  obtain ⟨h₁, h₂⟩ := (Functor.final_iff_of_isFiltered F).1 inferInstance
  rw [isCardinalFiltered_iff]
  refine ⟨fun ι j hι => ?_, fun ι j k f hι => ?_⟩
  · choose a ha using fun i => h₁ (j i)
    exact ⟨F.obj (IsCardinalFiltered.max a hι),
      fu

Depends on / 依赖: Category, Category.assoc, F.map, F.obj, Functor, Functor.final_iff_of_isFiltered, IsCardinalFiltered, IsCardinalFiltered.max, Nonempty, Prod.forall, final_iff_of_isFiltered, isCardinalFiltered_iff, isFiltered_of_isCardinalFiltered
-/
lemma IsCardinalFiltered.of_final
    {J₁ : Type u} [Category.{v} J₁] {J₂ : Type u'} [Category.{v'} J₂]
    (F : J₁ ⥤ J₂) [F.Final] (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [IsCardinalFiltered J₁ κ] :
    IsCardinalFiltered J₂ κ := by
  have := isFiltered_of_isCardinalFiltered J₁ κ
  obtain ⟨h₁, h₂⟩ := (Functor.final_iff_of_isFiltered F).1 inferInstance
  rw [isCardinalFiltered_iff]
  refine ⟨fun ι j hι => ?_, fun ι j k f hι => ?_⟩
  · choose a ha using fun i => h₁ (j i)
    exact ⟨F.obj (IsCardinalFiltered.max a hι),
      fun i => ⟨(ha i).some ≫ F.map (toMax a hι i)⟩⟩
  · by_cases h : Nonempty ι
    · obtain ⟨l, ⟨a⟩⟩ := h₁ k
      choose m b hb using fun (i : ι × ι) => h₂ (f i.1 ≫ a) (f i.2 ≫ a)
      simp only [Category.assoc, Prod.forall] at hb
      obtain ⟨n, c, d, hn⟩ := wideSpan b
        (hasCardinalLT_prod (Cardinal.IsRegular.aleph0_le Fact.out) hι hι)
      let i₀ : ι := Classical.arbitrary _
      exact ⟨F.obj n, a ≫ F.map d, f i₀ ≫ a ≫ F.map d,
        fun i => by rw [← hn (i₀, i), Functor.map_comp, reassoc_of% (hb i₀ i)]⟩
    · simp only [not_nonempty_iff] at h
      obtain ⟨j', ⟨a⟩⟩ := h₁ j
      obtain ⟨k', ⟨b⟩⟩ := h₁ k
      exact ⟨F.obj (IsFiltered.max j' k'), b ≫ F.map (IsFiltered.rightToMax _ _),
        a ≫ F.map (IsFiltered.leftToMax _ _), by simp⟩

set_option backward.defeqAttrib.useBackward true in
/--
lemma `Limits.IsTerminal.isCardinalFiltered` / 引理 `Limits.IsTerminal.isCardinalFiltered`

English:
lemma Limits.IsTerminal.isCardinalFiltered
  statement: {J : Type u} [Category.{v} J]
  proof: ⟨{ pt := X, ι.app _ := hX.from _ }⟩

中文:
引理 Limits.IsTerminal.isCardinalFiltered
  结论: {J : 类型u} [Category.{v} J]
  证明: ⟨{ pt := X, ι.app _ := hX.from _ }⟩

Depends on / 依赖: hX.from
-/
lemma Limits.IsTerminal.isCardinalFiltered {J : Type u} [Category.{v} J]
    {X : J} (hX : IsTerminal X) (κ : Cardinal.{w}) [Fact κ.IsRegular] :
    IsCardinalFiltered J κ where
  nonempty_cocone _ _ := ⟨{ pt := X, ι.app _ := hX.from _ }⟩

/--
lemma `isCardinalFiltered_of_hasTerminal` / 引理 `isCardinalFiltered_of_hasTerminal`

English:
lemma isCardinalFiltered_of_hasTerminal
  statement: (J : Type u) [Category.{v} J]
  proof: terminalIsTerminal.isCardinalFiltered _

中文:
引理 isCardinalFiltered_of_hasTerminal
  结论: (J : 类型u) [Category.{v} J]
  证明: terminalIsTerminal.isCardinalFiltered _

Depends on / 依赖: isCardinalFiltered, terminalIsTerminal, terminalIsTerminal.isCardinalFiltered
-/
lemma isCardinalFiltered_of_hasTerminal (J : Type u) [Category.{v} J]
    [HasTerminal J] (κ : Cardinal.{w}) [Fact κ.IsRegular] :
    IsCardinalFiltered J κ :=
  terminalIsTerminal.isCardinalFiltered _

end CategoryTheory
