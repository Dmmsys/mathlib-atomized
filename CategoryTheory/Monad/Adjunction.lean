/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Adjunction.Reflective
public import Mathlib.CategoryTheory.Monad.Algebra

/-!
# Adjunctions and (co)monads

We develop the basic relationship between adjunctions and (co)monads.

Given an adjunction `h : L ⊣ R`, we have `h.toMonad : Monad C` and `h.toComonad : Comonad D`.
We then have
`Monad.comparison (h : L ⊣ R) : D ⥤ h.toMonad.algebra`
sending `Y : D` to the Eilenberg-Moore algebra for `L ⋙ R` with underlying object `R.obj X`,
and dually `Comonad.comparison`.

We say `R : D ⥤ C` is `MonadicRightAdjoint`, if it is a right adjoint and its `Monad.comparison`
is an equivalence of categories. (Similarly for `ComonadicLeftAdjoint`.)

Finally we prove that reflective functors are `MonadicRightAdjoint` and coreflective functors are
`ComonadicLeftAdjoint`.
-/

@[expose] public section


namespace CategoryTheory

open Category CategoryTheory.Functor

universe v₁ v₂ u₁ u₂

-- morphism levels before object levels. See note [category_theory universes].
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable {L : C ⥤ D} {R : D ⥤ C}

namespace Adjunction

set_option backward.defeqAttrib.useBackward true in
/-- For a pair of functors `L : C ⥤ D`, `R : D ⥤ C`, an adjunction `h : L ⊣ R` induces a monad on
the category `C`.
-/
@[simps! coe η μ]
/--
Definition of `toMonad` / `toMonad` 的定义

English:
definition toMonad
  signature: (h : L ⊣ R)
  body: L ⋙ R
  η := h.unit
  μ := whiskerRight (whiskerLeft L h.counit) R
  assoc X := by
    dsimp
    rw [← R.map_comp]
    simp
  right_unit X := by
    dsimp
    rw [← R.map_comp]
    simp

中文:
定义 toMonad
  签名: (h : L ⊣ R)
  定义体: L ⋙ R
  η := h.unit
  μ := whiskerRight (whiskerLeft L h.counit) R
  assoc X := by
    dsimp
    rw [← R.map_comp]
    simp
  right_unit X := by
    dsimp
    rw [← R.map_comp]
    simp
-/
def toMonad (h : L ⊣ R) : Monad C where
  toFunctor := L ⋙ R
  η := h.unit
  μ := whiskerRight (whiskerLeft L h.counit) R
  assoc X := by
    dsimp
    rw [← R.map_comp]
    simp
  right_unit X := by
    dsimp
    rw [← R.map_comp]
    simp

set_option backward.defeqAttrib.useBackward true in
/-- For a pair of functors `L : C ⥤ D`, `R : D ⥤ C`, an adjunction `h : L ⊣ R` induces a comonad on
the category `D`.
-/
@[simps coe ε δ]
/--
Definition of `toComonad` / `toComonad` 的定义

English:
definition toComonad
  signature: (h : L ⊣ R)
  body: R ⋙ L
  ε := h.counit
  δ := whiskerRight (whiskerLeft R h.unit) L
  coassoc X := by
    dsimp
    rw [← L.map_comp]
    simp
  right_counit X := by
    dsimp
    rw [← L.map_comp]
    simp

中文:
定义 toComonad
  签名: (h : L ⊣ R)
  定义体: R ⋙ L
  ε := h.counit
  δ := whiskerRight (whiskerLeft R h.unit) L
  coassoc X := by
    dsimp
    rw [← L.map_comp]
    simp
  right_counit X := by
    dsimp
    rw [← L.map_comp]
    simp
-/
def toComonad (h : L ⊣ R) : Comonad D where
  toFunctor := R ⋙ L
  ε := h.counit
  δ := whiskerRight (whiskerLeft R h.unit) L
  coassoc X := by
    dsimp
    rw [← L.map_comp]
    simp
  right_counit X := by
    dsimp
    rw [← L.map_comp]
    simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The monad induced by the Eilenberg-Moore adjunction is the original monad. -/
@[simps!]
/--
Definition of `adjToMonadIso` / `adjToMonadIso` 的定义

English:
definition adjToMonadIso
  signature: (T : Monad C)
  body: MonadIso.mk (NatIso.ofComponents fun _ => Iso.refl _)

中文:
定义 adjToMonadIso
  签名: (T : 单子 C)
  定义体: MonadIso.mk (NatIso.ofComponents fun _ => Iso.refl _)

Depends on / 依赖: Iso.refl, MonadIso, MonadIso.mk, NatIso, NatIso.ofComponents, ofComponents
-/
def adjToMonadIso (T : Monad C) : T.adj.toMonad ≅ T :=
  MonadIso.mk (NatIso.ofComponents fun _ => Iso.refl _)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The comonad induced by the Eilenberg-Moore adjunction is the original comonad. -/
@[simps!]
/--
Definition of `adjToComonadIso` / `adjToComonadIso` 的定义

English:
definition adjToComonadIso
  signature: (G : Comonad C)
  body: ComonadIso.mk (NatIso.ofComponents fun _ => Iso.refl _)

中文:
定义 adjToComonadIso
  签名: (G : 余单子 C)
  定义体: ComonadIso.mk (NatIso.ofComponents fun _ => Iso.refl _)

Depends on / 依赖: ComonadIso, ComonadIso.mk, Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def adjToComonadIso (G : Comonad C) : G.adj.toComonad ≅ G :=
  ComonadIso.mk (NatIso.ofComponents fun _ => Iso.refl _)

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `unitAsIsoOfIso` / `unitAsIsoOfIso` 的定义

English:
definition unitAsIsoOfIso
  signature: (adj : L ⊣ R) (i : L ⋙ R ≅ 𝟭 C)
  body: adj.unit
  inv := i.hom ≫ (adj.toMonad.transport i).μ
  hom_inv_id := by
    rw [← assoc]
    ext X
    exact (adj.toMonad.transport i).right_unit X
  inv_hom_id := by
    rw [assoc]; rw [← Iso.eq_inv_comp]; rw [comp_id]; rw [← id_comp i.inv]; rw [Iso.eq_comp_inv]; rw [assoc]; rw [NatTrans.id_comm]
    ext X
    exact (adj.toMonad.transport i).right_unit X

中文:
定义 unitAsIsoOfIso
  签名: (adj : L ⊣ R) (i : L ⋙ R ≅ 𝟭 C)
  定义体: adj.unit
  inv := i.hom ≫ (adj.toMonad.transport i).μ
  hom_inv_id := by
    rw [← assoc]
    ext X
    exact (adj.toMonad.transport i).right_unit X
  inv_hom_id := by
    rw [assoc]; rw [← Iso.eq_inv_comp]; rw [comp_id]; rw [← id_comp i.inv]; rw [Iso.eq_comp_inv]; rw [assoc]; rw [NatTrans.id_comm]
    ext X
    exact (adj.toMonad.transport i).right_unit X

Depends on / 依赖: adj.unit
-/
def unitAsIsoOfIso (adj : L ⊣ R) (i : L ⋙ R ≅ 𝟭 C) : 𝟭 C ≅ L ⋙ R where
  hom := adj.unit
  inv := i.hom ≫ (adj.toMonad.transport i).μ
  hom_inv_id := by
    rw [← assoc]
    ext X
    exact (adj.toMonad.transport i).right_unit X
  inv_hom_id := by
    rw [assoc]; rw [← Iso.eq_inv_comp]; rw [comp_id]; rw [← id_comp i.inv]; rw [Iso.eq_comp_inv]; rw [assoc]; rw [NatTrans.id_comm]
    ext X
    exact (adj.toMonad.transport i).right_unit X

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `isIso_unit_of_iso` / 引理 `isIso_unit_of_iso`

English:
lemma isIso_unit_of_iso
  given: (adj : L ⊣ R) (i : L ⋙ R ≅ 𝟭 C)
  statement: IsIso adj.unit
  proof: (inferInstanceAs (IsIso (unitAsIsoOfIso adj i).hom))

中文:
引理 isIso_unit_of_iso
  条件: (adj : L ⊣ R) (i : L ⋙ R ≅ 𝟭 C)
  结论: 是同构 adj.unit
  证明: (inferInstanceAs (IsIso (unitAsIsoOfIso adj i).hom))

Depends on / 依赖: unitAsIsoOfIso
-/
lemma isIso_unit_of_iso (adj : L ⊣ R) (i : L ⋙ R ≅ 𝟭 C) : IsIso adj.unit :=
  (inferInstanceAs (IsIso (unitAsIsoOfIso adj i).hom))

/--
Definition of `fullyFaithfulLOfCompIsoId` / `fullyFaithfulLOfCompIsoId` 的定义

English:
definition fullyFaithfulLOfCompIsoId
  signature: (adj : L ⊣ R) (i : L ⋙ R ≅ 𝟭 C)
  body: haveI := adj.isIso_unit_of_iso i
  adj.fullyFaithfulLOfIsIsoUnit

中文:
定义 fullyFaithfulLOfCompIsoId
  签名: (adj : L ⊣ R) (i : L ⋙ R ≅ 𝟭 C)
  定义体: haveI := adj.isIso_unit_of_iso i
  adj.fullyFaithfulLOfIsIsoUnit

Depends on / 依赖: adj.fullyFaithfulLOfIsIsoUnit, adj.isIso_unit_of_iso, fullyFaithfulLOfIsIsoUnit, isIso_unit_of_iso
-/
noncomputable def fullyFaithfulLOfCompIsoId (adj : L ⊣ R) (i : L ⋙ R ≅ 𝟭 C) : L.FullyFaithful :=
  haveI := adj.isIso_unit_of_iso i
  adj.fullyFaithfulLOfIsIsoUnit

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `counitAsIsoOfIso` / `counitAsIsoOfIso` 的定义

English:
definition counitAsIsoOfIso
  signature: (adj : L ⊣ R) (j : R ⋙ L ≅ 𝟭 D)
  body: adj.counit
  inv := (adj.toComonad.transport j).δ ≫ j.inv
  hom_inv_id := by
    rw [← assoc]; rw [Iso.comp_inv_eq]; rw [id_comp]; rw [← comp_id j.hom]; rw [← Iso.inv_comp_eq]; rw [← assoc]; rw [NatTrans.id_comm]
    ext X
    exact (adj.toComonad.transport j).right_counit X
  inv_hom_id := by
    rw [assoc]
    ext X
    exact (adj.toComonad.transport j).right_counit X

中文:
定义 counitAsIsoOfIso
  签名: (adj : L ⊣ R) (j : R ⋙ L ≅ 𝟭 D)
  定义体: adj.counit
  inv := (adj.toComonad.transport j).δ ≫ j.inv
  hom_inv_id := by
    rw [← assoc]; rw [Iso.comp_inv_eq]; rw [id_comp]; rw [← comp_id j.hom]; rw [← Iso.inv_comp_eq]; rw [← assoc]; rw [NatTrans.id_comm]
    ext X
    exact (adj.toComonad.transport j).right_counit X
  inv_hom_id := by
    rw [assoc]
    ext X
    exact (adj.toComonad.transport j).right_counit X

Depends on / 依赖: adj.counit, counit
-/
def counitAsIsoOfIso (adj : L ⊣ R) (j : R ⋙ L ≅ 𝟭 D) : R ⋙ L ≅ 𝟭 D where
  hom := adj.counit
  inv := (adj.toComonad.transport j).δ ≫ j.inv
  hom_inv_id := by
    rw [← assoc]; rw [Iso.comp_inv_eq]; rw [id_comp]; rw [← comp_id j.hom]; rw [← Iso.inv_comp_eq]; rw [← assoc]; rw [NatTrans.id_comm]
    ext X
    exact (adj.toComonad.transport j).right_counit X
  inv_hom_id := by
    rw [assoc]
    ext X
    exact (adj.toComonad.transport j).right_counit X

/--
lemma `isIso_counit_of_iso` / 引理 `isIso_counit_of_iso`

English:
lemma isIso_counit_of_iso
  given: (adj : L ⊣ R) (j : R ⋙ L ≅ 𝟭 D)
  statement: IsIso adj.counit
  proof: inferInstanceAs (IsIso (counitAsIsoOfIso adj j).hom)

中文:
引理 isIso_counit_of_iso
  条件: (adj : L ⊣ R) (j : R ⋙ L ≅ 𝟭 D)
  结论: 是同构 adj.counit
  证明: inferInstanceAs (IsIso (counitAsIsoOfIso adj j).hom)

Depends on / 依赖: counitAsIsoOfIso
-/
lemma isIso_counit_of_iso (adj : L ⊣ R) (j : R ⋙ L ≅ 𝟭 D) : IsIso adj.counit :=
  inferInstanceAs (IsIso (counitAsIsoOfIso adj j).hom)

/--
Definition of `fullyFaithfulROfCompIsoId` / `fullyFaithfulROfCompIsoId` 的定义

English:
definition fullyFaithfulROfCompIsoId
  signature: (adj : L ⊣ R) (j : R ⋙ L ≅ 𝟭 D)
  body: haveI := adj.isIso_counit_of_iso j
  adj.fullyFaithfulROfIsIsoCounit

中文:
定义 fullyFaithfulROfCompIsoId
  签名: (adj : L ⊣ R) (j : R ⋙ L ≅ 𝟭 D)
  定义体: haveI := adj.isIso_counit_of_iso j
  adj.fullyFaithfulROfIsIsoCounit

Depends on / 依赖: adj.fullyFaithfulROfIsIsoCounit, adj.isIso_counit_of_iso, fullyFaithfulROfIsIsoCounit, isIso_counit_of_iso
-/
noncomputable def fullyFaithfulROfCompIsoId (adj : L ⊣ R) (j : R ⋙ L ≅ 𝟭 D) : R.FullyFaithful :=
  haveI := adj.isIso_counit_of_iso j
  adj.fullyFaithfulROfIsIsoCounit

end Adjunction

set_option backward.defeqAttrib.useBackward true in
/-- Given any adjunction `L ⊣ R`, there is a comparison functor `CategoryTheory.Monad.comparison R`
sending objects `Y : D` to Eilenberg-Moore algebras for `L ⋙ R` with underlying object `R.obj X`.

We later show that this is full when `R` is full, faithful when `R` is faithful,
and essentially surjective when `R` is reflective.
-/
@[simps]
/--
Definition of `Monad.comparison` / `Monad.comparison` 的定义

English:
definition Monad.comparison
  signature: (h : L ⊣ R)
  body: { A := R.obj X
      a := R.map (h.counit.app X)
      assoc := by
        dsimp
        rw [← R.map_comp]; rw [← Adjunction.counit_naturality]; rw [R.map_comp] }
  map f :=
    { f := R.map f
      h := by
        dsimp
        rw [← R.map_comp]; rw [Adjunction.counit_naturality]; rw [R.map_comp] }

中文:
定义 单子.comparison
  签名: (h : L ⊣ R)
  定义体: { A := R.obj X
      a := R.map (h.counit.app X)
      assoc := by
        dsimp
        rw [← R.map_comp]; rw [← Adjunction.counit_naturality]; rw [R.map_comp] }
  map f :=
    { f := R.map f
      h := by
        dsimp
        rw [← R.map_comp]; rw [Adjunction.counit_naturality]; rw [R.map_comp] }

Depends on / 依赖: Adjunction, Adjunction.counit_naturality, R.map, R.map_comp, R.obj, counit, counit_naturality, h.counit.app, map_comp
-/
def Monad.comparison (h : L ⊣ R) : D ⥤ h.toMonad.Algebra where
  obj X :=
    { A := R.obj X
      a := R.map (h.counit.app X)
      assoc := by
        dsimp
        rw [← R.map_comp]; rw [← Adjunction.counit_naturality]; rw [R.map_comp] }
  map f :=
    { f := R.map f
      h := by
        dsimp
        rw [← R.map_comp]; rw [Adjunction.counit_naturality]; rw [R.map_comp] }

set_option backward.defeqAttrib.useBackward true in
/-- The underlying object of `(Monad.comparison R).obj X` is just `R.obj X`.
-/
@[simps]
/--
Definition of `Monad.comparisonForget` / `Monad.comparisonForget` 的定义

English:
definition Monad.comparisonForget
  signature: (h : L ⊣ R)
  body: { app := fun _ => 𝟙 _ }
  inv := { app := fun _ => 𝟙 _ }

中文:
定义 单子.comparisonForget
  签名: (h : L ⊣ R)
  定义体: { app := fun _ => 𝟙 _ }
  inv := { app := fun _ => 𝟙 _ }
-/
def Monad.comparisonForget (h : L ⊣ R) : Monad.comparison h ⋙ h.toMonad.forget ≅ R where
  hom := { app := fun _ => 𝟙 _ }
  inv := { app := fun _ => 𝟙 _ }

/--
theorem `Monad.left_comparison` / 定理 `Monad.left_comparison`

English:
theorem Monad.left_comparison
  given: (h : L ⊣ R)
  statement: L ⋙ Monad.comparison h = h.toMonad.free
  proof: rfl

中文:
定理 单子.left_comparison
  条件: (h : L ⊣ R)
  结论: L ⋙ 单子.comparison h = h.toMonad.free
  证明: rfl
-/
theorem Monad.left_comparison (h : L ⊣ R) : L ⋙ Monad.comparison h = h.toMonad.free :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [R.Faithful]
  signature: (h : L ⊣ R)
  body: R.map_injective (congr_arg Monad.Algebra.Hom.f w :)

中文:
实例 [R.忠实]
  签名: (h : L ⊣ R)
  定义体: R.map_injective (congr_arg Monad.Algebra.Hom.f w :)

Depends on / 依赖: Algebra, Monad.Algebra.Hom.f, R.map_injective, congr_arg, map_injective
-/
instance [R.Faithful] (h : L ⊣ R) : (Monad.comparison h).Faithful where
  map_injective {_ _} _ _ w := R.map_injective (congr_arg Monad.Algebra.Hom.f w :)

instance (T : Monad C) : (Monad.comparison T.adj).Full where
  map_surjective {_ _} f := ⟨⟨f.f, by simpa using! f.h⟩, rfl⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
instance (T : Monad C) : (Monad.comparison T.adj).EssSurj where
  mem_essImage X :=
    ⟨{ A := X.A
        a := X.a
        unit := by simpa using X.unit
        assoc := by simpa using X.assoc },
    ⟨Monad.Algebra.isoMk (Iso.refl _)⟩⟩

set_option backward.defeqAttrib.useBackward true in
/--
Given any adjunction `L ⊣ R`, there is a comparison functor `CategoryTheory.Comonad.comparison L`
sending objects `X : C` to Eilenberg-Moore coalgebras for `L ⋙ R` with underlying object
`L.obj X`.
-/
@[simps]
/--
Definition of `Comonad.comparison` / `Comonad.comparison` 的定义

English:
definition Comonad.comparison
  signature: (h : L ⊣ R)
  body: { A := L.obj X
      a := L.map (h.unit.app X)
      coassoc := by
        dsimp
        rw [← L.map_comp]; rw [← Adjunction.unit_naturality]; rw [L.map_comp] }
  map f :=
    { f := L.map f
      h := by
        dsimp
        rw [← L.map_comp]
        simp }

中文:
定义 余单子.comparison
  签名: (h : L ⊣ R)
  定义体: { A := L.obj X
      a := L.map (h.unit.app X)
      coassoc := by
        dsimp
        rw [← L.map_comp]; rw [← Adjunction.unit_naturality]; rw [L.map_comp] }
  map f :=
    { f := L.map f
      h := by
        dsimp
        rw [← L.map_comp]
        simp }

Depends on / 依赖: Adjunction, Adjunction.unit_naturality, L.map, L.map_comp, L.obj, coassoc, h.unit.app, map_comp, unit_naturality
-/
def Comonad.comparison (h : L ⊣ R) : C ⥤ h.toComonad.Coalgebra where
  obj X :=
    { A := L.obj X
      a := L.map (h.unit.app X)
      coassoc := by
        dsimp
        rw [← L.map_comp]; rw [← Adjunction.unit_naturality]; rw [L.map_comp] }
  map f :=
    { f := L.map f
      h := by
        dsimp
        rw [← L.map_comp]
        simp }

set_option backward.defeqAttrib.useBackward true in
/-- The underlying object of `(Comonad.comparison L).obj X` is just `L.obj X`.
-/
@[simps]
/--
Definition of `Comonad.comparisonForget` / `Comonad.comparisonForget` 的定义

English:
definition Comonad.comparisonForget
  signature: {L : C ⥤ D} {R : D ⥤ C} (h : L ⊣ R)
  body: { app := fun _ => 𝟙 _ }
  inv := { app := fun _ => 𝟙 _ }

中文:
定义 余单子.comparisonForget
  签名: {L : C ⥤ D} {R : D ⥤ C} (h : L ⊣ R)
  定义体: { app := fun _ => 𝟙 _ }
  inv := { app := fun _ => 𝟙 _ }
-/
def Comonad.comparisonForget {L : C ⥤ D} {R : D ⥤ C} (h : L ⊣ R) :
    Comonad.comparison h ⋙ h.toComonad.forget ≅ L where
  hom := { app := fun _ => 𝟙 _ }
  inv := { app := fun _ => 𝟙 _ }

/--
theorem `Comonad.left_comparison` / 定理 `Comonad.left_comparison`

English:
theorem Comonad.left_comparison
  given: (h : L ⊣ R)
  statement: R ⋙ Comonad.comparison h = h.toComonad.cofree
  proof: rfl

中文:
定理 余单子.left_comparison
  条件: (h : L ⊣ R)
  结论: R ⋙ 余单子.comparison h = h.toComonad.cofree
  证明: rfl
-/
theorem Comonad.left_comparison (h : L ⊣ R) : R ⋙ Comonad.comparison h = h.toComonad.cofree :=
  rfl

/--
Instance `Comonad.comparison_faithful_of_faithful` / 实例 `Comonad.comparison_faithful_of_faithful`

English:
instance Comonad.comparison_faithful_of_faithful
  signature: [L.Faithful] (h : L ⊣ R)
  body: L.map_injective (congr_arg Comonad.Coalgebra.Hom.f w :)

中文:
实例 余单子.comparison_faithful_of_faithful
  签名: [L.忠实] (h : L ⊣ R)
  定义体: L.map_injective (congr_arg Comonad.Coalgebra.Hom.f w :)

Depends on / 依赖: Coalgebra, Comonad, Comonad.Coalgebra.Hom.f, L.map_injective, congr_arg, map_injective
-/
instance Comonad.comparison_faithful_of_faithful [L.Faithful] (h : L ⊣ R) :
    (Comonad.comparison h).Faithful where
  map_injective {_ _} _ _ w := L.map_injective (congr_arg Comonad.Coalgebra.Hom.f w :)

instance (G : Comonad C) : (Comonad.comparison G.adj).Full where
  map_surjective f := ⟨⟨f.f, by simpa using! f.h⟩, rfl⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
instance (G : Comonad C) : (Comonad.comparison G.adj).EssSurj where
  mem_essImage X :=
    ⟨{ A := X.A
        a := X.a
        counit := by simpa using X.counit
        coassoc := by simpa using X.coassoc },
      ⟨Comonad.Coalgebra.isoMk (Iso.refl _)⟩⟩

/--
Definition of `MonadicRightAdjoint` / `MonadicRightAdjoint` 的定义

English:
class MonadicRightAdjoint
  parameters: (R : D ⥤ C)
  axioms and operations (3):
    - L : C ⥤ D
    - adj : L ⊣ R
    - eqv : (Monad.comparison adj).IsEquivalence

中文:
类 MonadicRightAdjoint
  参数: (R : D ⥤ C)
  公理与运算 (3 个):
    - L : C ⥤ D
    - adj : L ⊣ R
    - eqv : (单子.comparison adj).是等价
-/
class MonadicRightAdjoint (R : D ⥤ C) where
  /-- a choice of left adjoint for `R` -/
  L : C ⥤ D
  /-- `R` is a right adjoint -/
  adj : L ⊣ R
  eqv : (Monad.comparison adj).IsEquivalence

/--
Definition of `monadicLeftAdjoint` / `monadicLeftAdjoint` 的定义

English:
definition monadicLeftAdjoint
  signature: (R : D ⥤ C) [MonadicRightAdjoint R]
  body: MonadicRightAdjoint.L (R := R)

中文:
定义 monadicLeftAdjoint
  签名: (R : D ⥤ C) [MonadicRightAdjoint R]
  定义体: MonadicRightAdjoint.L (R := R)

Depends on / 依赖: MonadicRightAdjoint, MonadicRightAdjoint.L
-/
def monadicLeftAdjoint (R : D ⥤ C) [MonadicRightAdjoint R] : C ⥤ D :=
  MonadicRightAdjoint.L (R := R)

/--
Definition of `monadicAdjunction` / `monadicAdjunction` 的定义

English:
definition monadicAdjunction
  signature: (R : D ⥤ C) [MonadicRightAdjoint R]
  body: MonadicRightAdjoint.adj

中文:
定义 monadicAdjunction
  签名: (R : D ⥤ C) [MonadicRightAdjoint R]
  定义体: MonadicRightAdjoint.adj

Depends on / 依赖: MonadicRightAdjoint, MonadicRightAdjoint.adj
-/
def monadicAdjunction (R : D ⥤ C) [MonadicRightAdjoint R] :
    monadicLeftAdjoint R ⊣ R :=
  MonadicRightAdjoint.adj

instance (R : D ⥤ C) [MonadicRightAdjoint R] :
    (Monad.comparison (monadicAdjunction R)).IsEquivalence :=
  MonadicRightAdjoint.eqv

instance (R : D ⥤ C) [MonadicRightAdjoint R] : R.IsRightAdjoint :=
  (monadicAdjunction R).isRightAdjoint

noncomputable instance (T : Monad C) : MonadicRightAdjoint T.forget where
  L := T.free
  adj := T.adj
  eqv := { }

/--
Definition of `ComonadicLeftAdjoint` / `ComonadicLeftAdjoint` 的定义

English:
class ComonadicLeftAdjoint
  parameters: (L : C ⥤ D)
  axioms and operations (3):
    - R : D ⥤ C
    - adj : L ⊣ R
    - eqv : (Comonad.comparison adj).IsEquivalence

中文:
类 余monadicLeftAdjoint
  参数: (L : C ⥤ D)
  公理与运算 (3 个):
    - R : D ⥤ C
    - adj : L ⊣ R
    - eqv : (余单子.comparison adj).是等价
-/
class ComonadicLeftAdjoint (L : C ⥤ D) where
  /-- a choice of right adjoint for `L` -/
  R : D ⥤ C
  /-- `L` is a left adjoint -/
  adj : L ⊣ R
  eqv : (Comonad.comparison adj).IsEquivalence

/--
Definition of `comonadicRightAdjoint` / `comonadicRightAdjoint` 的定义

English:
definition comonadicRightAdjoint
  signature: (L : C ⥤ D) [ComonadicLeftAdjoint L]
  body: ComonadicLeftAdjoint.R (L := L)

中文:
定义 comonadicRightAdjoint
  签名: (L : C ⥤ D) [余monadicLeftAdjoint L]
  定义体: ComonadicLeftAdjoint.R (L := L)

Depends on / 依赖: ComonadicLeftAdjoint, ComonadicLeftAdjoint.R
-/
def comonadicRightAdjoint (L : C ⥤ D) [ComonadicLeftAdjoint L] : D ⥤ C :=
  ComonadicLeftAdjoint.R (L := L)

/--
Definition of `comonadicAdjunction` / `comonadicAdjunction` 的定义

English:
definition comonadicAdjunction
  signature: (L : C ⥤ D) [ComonadicLeftAdjoint L]
  body: ComonadicLeftAdjoint.adj

中文:
定义 comonadicAdjunction
  签名: (L : C ⥤ D) [余monadicLeftAdjoint L]
  定义体: ComonadicLeftAdjoint.adj

Depends on / 依赖: ComonadicLeftAdjoint, ComonadicLeftAdjoint.adj
-/
def comonadicAdjunction (L : C ⥤ D) [ComonadicLeftAdjoint L] :
    L ⊣ comonadicRightAdjoint L :=
  ComonadicLeftAdjoint.adj

instance (L : C ⥤ D) [ComonadicLeftAdjoint L] :
    (Comonad.comparison (comonadicAdjunction L)).IsEquivalence :=
  ComonadicLeftAdjoint.eqv

instance (L : C ⥤ D) [ComonadicLeftAdjoint L] : L.IsLeftAdjoint :=
  (comonadicAdjunction L).isLeftAdjoint

noncomputable instance (G : Comonad C) : ComonadicLeftAdjoint G.forget where
  R := G.cofree
  adj := G.adj
  eqv := { }

set_option backward.defeqAttrib.useBackward true in
-- TODO: This holds more generally for idempotent adjunctions, not just reflective adjunctions.
/--
Instance `μ_iso_of_reflective` / 实例 `μ_iso_of_reflective`

English:
instance μ_iso_of_reflective
  signature: [Reflective R]
  body: by
  dsimp
  infer_instance

中文:
实例 μ_iso_of_reflective
  签名: [反射 R]
  定义体: by
  dsimp
  infer_instance

Depends on / 依赖: infer_instance
-/
instance μ_iso_of_reflective [Reflective R] : IsIso (reflectorAdjunction R).toMonad.μ := by
  dsimp
  infer_instance

set_option backward.defeqAttrib.useBackward true in
/--
Instance `δ_iso_of_coreflective` / 实例 `δ_iso_of_coreflective`

English:
instance δ_iso_of_coreflective
  signature: [Coreflective R]
  body: by
  dsimp
  infer_instance

中文:
实例 δ_iso_of_coreflective
  签名: [余反射 R]
  定义体: by
  dsimp
  infer_instance

Depends on / 依赖: infer_instance
-/
instance δ_iso_of_coreflective [Coreflective R] : IsIso (coreflectorAdjunction R).toComonad.δ := by
  dsimp
  infer_instance

attribute [instance] MonadicRightAdjoint.eqv
attribute [instance] ComonadicLeftAdjoint.eqv

namespace Reflective

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Reflective
  signature: R] (X
  body: ⟨⟨X.a,
      ⟨X.unit, by
        dsimp only [Functor.id_obj]
        rw [← (reflectorAdjunction R).unit_naturality]
        dsimp only [Functor.comp_obj, Adjunction.toMonad_coe]
        rw [unit_obj_eq_map_unit]; rw [← Functor.map_comp]; rw [← Functor.map_comp]
        dsimp [X.unit]
        simpa using congrArg (fun t => R.map ((reflector R).map t)) X.unit ⟩⟩⟩

中文:
实例 [反射
  签名: R] (X
  定义体: ⟨⟨X.a,
      ⟨X.unit, by
        dsimp only [Functor.id_obj]
        rw [← (reflectorAdjunction R).unit_naturality]
        dsimp only [Functor.comp_obj, Adjunction.toMonad_coe]
        rw [unit_obj_eq_map_unit]; rw [← Functor.map_comp]; rw [← Functor.map_comp]
        dsimp [X.unit]
        simpa using congrArg (fun t => R.map ((reflector R).map t)) X.unit ⟩⟩⟩

Depends on / 依赖: Adjunction, Adjunction.toMonad_coe, Functor, Functor.comp_obj, Functor.id_obj, Functor.map_comp, R.map, X.unit, comp_obj, id_obj, map_comp, reflector, reflectorAdjunction, toMonad_coe, unit_naturality, unit_obj_eq_map_unit
-/
instance [Reflective R] (X : (reflectorAdjunction R).toMonad.Algebra) :
    IsIso ((reflectorAdjunction R).unit.app X.A) :=
  ⟨⟨X.a,
      ⟨X.unit, by
        dsimp only [Functor.id_obj]
        rw [← (reflectorAdjunction R).unit_naturality]
        dsimp only [Functor.comp_obj, Adjunction.toMonad_coe]
        rw [unit_obj_eq_map_unit]; rw [← Functor.map_comp]; rw [← Functor.map_comp]
        dsimp [X.unit]
        simpa using congrArg (fun t => R.map ((reflector R).map t)) X.unit ⟩⟩⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `comparison_essSurj` / 实例 `comparison_essSurj`

English:
instance comparison_essSurj
  signature: [Reflective R]
  body: by
  refine ⟨fun X => ⟨(reflector R).obj X.A, ⟨?_⟩⟩⟩
  symm
  refine Monad.Algebra.isoMk ?_ ?_
  · exact asIso ((reflectorAdjunction R).unit.app X.A)
  dsimp only [Functor.comp_map, Monad.comparison_obj_a, asIso_hom, Functor.comp_obj,
    Monad.comparison_obj_A, Adjunction.toMonad_coe]
  rw [← cancel_epi ((reflectorAdjunction R).unit.app X.A)]
  dsimp only [Functor.id_obj, Functor.comp_obj]
  rw [Adjunction.unit_naturality_assoc]; rw [Adjunction.right_triangle_components]; rw [comp_id]
  apply (X.unit_assoc _).symm

中文:
实例 comparison_essSurj
  签名: [反射 R]
  定义体: by
  refine ⟨fun X => ⟨(reflector R).obj X.A, ⟨?_⟩⟩⟩
  symm
  refine Monad.Algebra.isoMk ?_ ?_
  · exact asIso ((reflectorAdjunction R).unit.app X.A)
  dsimp only [Functor.comp_map, Monad.comparison_obj_a, asIso_hom, Functor.comp_obj,
    Monad.comparison_obj_A, Adjunction.toMonad_coe]
  rw [← cancel_epi ((reflectorAdjunction R).unit.app X.A)]
  dsimp only [Functor.id_obj, Functor.comp_obj]
  rw [Adjunction.unit_naturality_assoc]; rw [Adjunction.right_triangle_components]; rw [comp_id]
  apply (X.unit_assoc _).symm

Depends on / 依赖: Adjunction, Adjunction.right_triangle_components, Adjunction.toMonad_coe, Adjunction.unit_naturality_assoc, Algebra, Functor, Functor.comp_map, Functor.comp_obj, Functor.id_obj, Monad.Algebra.isoMk, Monad.comparison_obj_A, Monad.comparison_obj_a, X.unit_assoc, asIso_hom, cancel_epi, comp_id, comp_map, comp_obj, comparison_obj_A, comparison_obj_a
-/
instance comparison_essSurj [Reflective R] :
    (Monad.comparison (reflectorAdjunction R)).EssSurj := by
  refine ⟨fun X => ⟨(reflector R).obj X.A, ⟨?_⟩⟩⟩
  symm
  refine Monad.Algebra.isoMk ?_ ?_
  · exact asIso ((reflectorAdjunction R).unit.app X.A)
  dsimp only [Functor.comp_map, Monad.comparison_obj_a, asIso_hom, Functor.comp_obj,
    Monad.comparison_obj_A, Adjunction.toMonad_coe]
  rw [← cancel_epi ((reflectorAdjunction R).unit.app X.A)]
  dsimp only [Functor.id_obj, Functor.comp_obj]
  rw [Adjunction.unit_naturality_assoc]; rw [Adjunction.right_triangle_components]; rw [comp_id]
  apply (X.unit_assoc _).symm

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `comparison_full` / 引理 `comparison_full`

English:
lemma comparison_full
  given: [R.Full] {L : C ⥤ D} (adj : L ⊣ R)
  proof: ⟨R.preimage f.f, by cat_disch⟩

中文:
引理 comparison_full
  条件: [R.满] {L : C ⥤ D} (adj : L ⊣ R)
  证明: ⟨R.preimage f.f, by cat_disch⟩

Depends on / 依赖: R.preimage, cat_disch, preimage
-/
lemma comparison_full [R.Full] {L : C ⥤ D} (adj : L ⊣ R) :
    (Monad.comparison adj).Full where
  map_surjective f := ⟨R.preimage f.f, by cat_disch⟩

end Reflective

namespace Coreflective

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Coreflective
  signature: R] (X
  body: ⟨⟨X.a,
      ⟨by
        dsimp only [Functor.id_obj]
        rw [← (coreflectorAdjunction R).counit_naturality]
        dsimp only [Functor.comp_obj, Adjunction.toMonad_coe]
        rw [counit_obj_eq_map_counit]; rw [← Functor.map_comp]; rw [← Functor.map_comp]
        simpa using congrArg (fun t => R.map ((coreflector R).map t)) X.counit, X.counit⟩⟩⟩

中文:
实例 [余反射
  签名: R] (X
  定义体: ⟨⟨X.a,
      ⟨by
        dsimp only [Functor.id_obj]
        rw [← (coreflectorAdjunction R).counit_naturality]
        dsimp only [Functor.comp_obj, Adjunction.toMonad_coe]
        rw [counit_obj_eq_map_counit]; rw [← Functor.map_comp]; rw [← Functor.map_comp]
        simpa using congrArg (fun t => R.map ((coreflector R).map t)) X.counit, X.counit⟩⟩⟩

Depends on / 依赖: Adjunction, Adjunction.toMonad_coe, Functor, Functor.comp_obj, Functor.id_obj, Functor.map_comp, R.map, X.counit, comp_obj, coreflector, coreflectorAdjunction, counit, counit_naturality, counit_obj_eq_map_counit, id_obj, map_comp, toMonad_coe
-/
instance [Coreflective R] (X : (coreflectorAdjunction R).toComonad.Coalgebra) :
    IsIso ((coreflectorAdjunction R).counit.app X.A) :=
  ⟨⟨X.a,
      ⟨by
        dsimp only [Functor.id_obj]
        rw [← (coreflectorAdjunction R).counit_naturality]
        dsimp only [Functor.comp_obj, Adjunction.toMonad_coe]
        rw [counit_obj_eq_map_counit]; rw [← Functor.map_comp]; rw [← Functor.map_comp]
        simpa using congrArg (fun t => R.map ((coreflector R).map t)) X.counit, X.counit⟩⟩⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `comparison_essSurj` / 实例 `comparison_essSurj`

English:
instance comparison_essSurj
  signature: [Coreflective R]
  body: by
  refine ⟨fun X => ⟨(coreflector R).obj X.A, ⟨?_⟩⟩⟩
  refine Comonad.Coalgebra.isoMk ?_ ?_
  · exact (asIso ((coreflectorAdjunction R).counit.app X.A))
  rw [← cancel_mono ((coreflectorAdjunction R).counit.app X.A)]
  simp only [Functor.comp_obj, Functor.id_obj,
    assoc]
  simpa using (coreflectorAdjunction R).counit.app X.A ≫= X.counit.symm

中文:
实例 comparison_essSurj
  签名: [余反射 R]
  定义体: by
  refine ⟨fun X => ⟨(coreflector R).obj X.A, ⟨?_⟩⟩⟩
  refine Comonad.Coalgebra.isoMk ?_ ?_
  · exact (asIso ((coreflectorAdjunction R).counit.app X.A))
  rw [← cancel_mono ((coreflectorAdjunction R).counit.app X.A)]
  simp only [Functor.comp_obj, Functor.id_obj,
    assoc]
  simpa using (coreflectorAdjunction R).counit.app X.A ≫= X.counit.symm

Depends on / 依赖: Coalgebra, Comonad, Comonad.Coalgebra.isoMk, Functor, Functor.comp_obj, Functor.id_obj, X.counit.symm, cancel_mono, comp_obj, coreflector, coreflectorAdjunction, counit, counit.app, id_obj
-/
instance comparison_essSurj [Coreflective R] :
    (Comonad.comparison (coreflectorAdjunction R)).EssSurj := by
  refine ⟨fun X => ⟨(coreflector R).obj X.A, ⟨?_⟩⟩⟩
  refine Comonad.Coalgebra.isoMk ?_ ?_
  · exact (asIso ((coreflectorAdjunction R).counit.app X.A))
  rw [← cancel_mono ((coreflectorAdjunction R).counit.app X.A)]
  simp only [Functor.comp_obj, Functor.id_obj,
    assoc]
  simpa using (coreflectorAdjunction R).counit.app X.A ≫= X.counit.symm

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `comparison_full` / 引理 `comparison_full`

English:
lemma comparison_full
  given: [R.Full] {L : C ⥤ D} (adj : R ⊣ L)
  proof: ⟨R.preimage f.f, by cat_disch⟩

中文:
引理 comparison_full
  条件: [R.满] {L : C ⥤ D} (adj : R ⊣ L)
  证明: ⟨R.preimage f.f, by cat_disch⟩

Depends on / 依赖: R.preimage, cat_disch, preimage
-/
lemma comparison_full [R.Full] {L : C ⥤ D} (adj : R ⊣ L) :
    (Comonad.comparison adj).Full where
  map_surjective f := ⟨R.preimage f.f, by cat_disch⟩

end Coreflective

-- It is possible to do this computably since the construction gives the data of the inverse, not
-- just the existence of an inverse on each object.
-- see Note [lower instance priority]
/-- Any reflective inclusion has a monadic right adjoint.
cf Prop 5.3.3 of [Riehl][riehl2017] -/
instance (priority := 100) monadicOfReflective [Reflective R] :
    MonadicRightAdjoint R where
  L := reflector R
  adj := reflectorAdjunction R
  eqv := { full := Reflective.comparison_full _ }

/-- Any coreflective inclusion has a comonadic left adjoint.
cf Dual statement of Prop 5.3.3 of [Riehl][riehl2017] -/
instance (priority := 100) comonadicOfCoreflective [Coreflective R] :
    ComonadicLeftAdjoint R where
  R := coreflector R
  adj := coreflectorAdjunction R
  eqv := { full := Coreflective.comparison_full _ }

end CategoryTheory
