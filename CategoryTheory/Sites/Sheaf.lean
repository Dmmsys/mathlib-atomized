/-
Copyright (c) 2020 Kevin Buzzard, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Yoneda
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
public import Mathlib.CategoryTheory.Sites.SheafOfTypes
public import Mathlib.CategoryTheory.Sites.EqualizerSheafCondition
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Terminal

/-!
# Sheaves taking values in a category

If C is a category with a Grothendieck topology, we define the notion of a sheaf taking values in
an arbitrary category `A`. We follow the definition in https://stacks.math.columbia.edu/tag/00VR,
noting that the presheaf of sets "defined above" can be seen in the comments between tags 00VQ and
00VR on the page <https://stacks.math.columbia.edu/tag/00VL>. The advantage of this definition is
that we need no assumptions whatsoever on `A` other than the assumption that the morphisms in `C`
and `A` live in the same universe.

* An `A`-valued presheaf `P : Cᵒᵖ ⥤ A` is defined to be a sheaf (for the topology `J`) iff for
  every `E : A`, the type-valued presheaves of sets given by sending `U : Cᵒᵖ` to `Hom_{A}(E, P U)`
  are all sheaves of sets, see `CategoryTheory.Presheaf.IsSheaf`.
* When `A = Type`, this recovers the basic definition of sheaves of sets, see
  `CategoryTheory.isSheaf_iff_isSheaf_of_type`.
* An alternate definition in terms of limits, unconditionally equivalent to the original one:
  see `CategoryTheory.Presheaf.isSheaf_iff_isLimit`.
* An alternate definition when `C` is small, has pullbacks and `A` has products is given by an
  equalizer condition `CategoryTheory.Presheaf.IsSheaf'`. This is equivalent to the earlier
  definition, shown in `CategoryTheory.Presheaf.isSheaf_iff_isSheaf'`.
* When `A = Type`, this is *definitionally* equal to the equalizer condition for presieves in
  `CategoryTheory.Sites.SheafOfTypes`.
* When `A` has limits and there is a functor `s : A ⥤ Type` which is faithful, reflects isomorphisms
  and preserves limits, then `P : Cᵒᵖ ⥤ A` is a sheaf iff the underlying presheaf of types
  `P ⋙ s : Cᵒᵖ ⥤ Type` is a sheaf (`CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget`).
  Cf https://stacks.math.columbia.edu/tag/0073, which is a weaker version of this statement (it's
  only over spaces, not sites) and https://stacks.math.columbia.edu/tag/00YR (a), which
  additionally assumes filtered colimits.

## Implementation notes

Occasionally we need to take a limit in `A` of a collection of morphisms of `C` indexed
by a collection of objects in `C`. This turns out to force the morphisms of `A` to be
in a sufficiently large universe. Rather than use `UnivLE` we prove some results for
a category `A'` instead, whose morphism universe of `A'` is defined to be `max u₁ v₁`, where
`u₁, v₁` are the universes for `C`. Perhaps after we get better at handling universe
inequalities this can be changed.

-/

@[expose] public section


universe w v₁ v₂ v₃ u₁ u₂ u₃

noncomputable section

namespace CategoryTheory

open Opposite CategoryTheory Category Limits Sieve

namespace Presheaf

variable {C : Type u₁} [Category.{v₁} C]
variable {A : Type u₂} [Category.{v₂} A]
variable (J : GrothendieckTopology C)

-- We follow https://stacks.math.columbia.edu/tag/00VL definition 00VR
/-- A sheaf of A is a presheaf `P : Cᵒᵖ ⥤ A` such that for every `E : A`, the
presheaf of types given by sending `U : C` to `Hom_{A}(E, P U)` is a sheaf of types. -/
@[stacks 00VR]
/--
Definition of `IsSheaf` / `IsSheaf` 的定义

English:
definition IsSheaf
  signature: (P : Cᵒᵖ ⥤ A)
  body: forall E : A, Presieve.IsSheaf J (P ⋙ coyoneda.obj (op E))

中文:
定义 是层
  签名: (P : Cᵒᵖ ⥤ A)
  定义体: forall E : A, Presieve.IsSheaf J (P ⋙ coyoneda.obj (op E))

Depends on / 依赖: IsSheaf, Presieve, Presieve.IsSheaf, coyoneda, coyoneda.obj
-/
def IsSheaf (P : Cᵒᵖ ⥤ A) : Prop :=
  forall E : A, Presieve.IsSheaf J (P ⋙ coyoneda.obj (op E))

/--
Definition of `IsSeparated` / `IsSeparated` 的定义

English:
definition IsSeparated
  signature: (P : Cᵒᵖ ⥤ A) {FA : A -> A -> Type*} {CA : A -> Type*}
  body: forall (X : C) (S : Sieve X) (_ : S in J X) (x y : ToType (P.obj (op X))),
    (forall (Y : C) (f : Y ⟶ X) (_ : S f), P.map f.op x = P.map f.op y) -> x = y

中文:
定义 是分离
  签名: (P : Cᵒᵖ ⥤ A) {FA : A -> A -> 类型} {CA : A -> 类型}
  定义体: forall (X : C) (S : Sieve X) (_ : S in J X) (x y : ToType (P.obj (op X))),
    (forall (Y : C) (f : Y ⟶ X) (_ : S f), P.map f.op x = P.map f.op y) -> x = y

Depends on / 依赖: P.map, P.obj, ToType, f.op
-/
def IsSeparated (P : Cᵒᵖ ⥤ A) {FA : A -> A -> Type*} {CA : A -> Type*}
    [forall X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA] : Prop :=
  forall (X : C) (S : Sieve X) (_ : S in J X) (x y : ToType (P.obj (op X))),
    (forall (Y : C) (f : Y ⟶ X) (_ : S f), P.map f.op x = P.map f.op y) -> x = y

section LimitSheafCondition

open Presieve Presieve.FamilyOfElements Limits

variable (P : Cᵒᵖ ⥤ A) {X : C} (S : Sieve X) (R : Presieve X) (E : Aᵒᵖ)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `conesEquivSieveCompatibleFamily` / `conesEquivSieveCompatibleFamily` 的定义

English:
definition conesEquivSieveCompatibleFamily
  signature: :
  body: ⟨fun _ f h => π.app (op ⟨Over.mk f, h⟩), fun X Y f g hf => by
      let φ : S.arrows.categoryMk (g ≫ f) (S.downward_closed hf g) ⟶
        S.arrows.categoryMk f hf := ObjectProperty.homMk (Over.homMk _ rfl)
      simpa using! π.naturality φ.op⟩
  invFun x :=
    { app := fun f => x.1 f.unop.1.hom f.unop.2
      naturality := fun f f' g => by
        have := x.2 f.unop.1.hom g.unop.hom.left f.unop.2
        dsimp at this ⊢
        rw [id_comp]; rw [← this]
        convert! rfl
        simp only [Over.w] }

中文:
定义 conesEquivSieveCompatibleFamily
  签名: :
  定义体: ⟨fun _ f h => π.app (op ⟨Over.mk f, h⟩), fun X Y f g hf => by
      let φ : S.arrows.categoryMk (g ≫ f) (S.downward_closed hf g) ⟶
        S.arrows.categoryMk f hf := ObjectProperty.homMk (Over.homMk _ rfl)
      simpa using! π.naturality φ.op⟩
  invFun x :=
    { app := fun f => x.1 f.unop.1.hom f.unop.2
      naturality := fun f f' g => by
        have := x.2 f.unop.1.hom g.unop.hom.left f.unop.2
        dsimp at this ⊢
        rw [id_comp]; rw [← this]
        convert! rfl
        simp only [Over.w] }

Depends on / 依赖: ObjectProperty, ObjectProperty.homMk, Over.homMk, Over.mk, Over.w, S.arrows.categoryMk, S.downward_closed, arrows, categoryMk, convert, downward_closed, f.unop, g.unop.hom.left, id_comp, invFun, naturality
-/
def conesEquivSieveCompatibleFamily :
    (S.arrows.diagram.op ⋙ P).cones.obj E ≃
      { x : FamilyOfElements (P ⋙ coyoneda.obj E) (S : Presieve X) // x.SieveCompatible } where
  toFun π :=
    ⟨fun _ f h => π.app (op ⟨Over.mk f, h⟩), fun X Y f g hf => by
      let φ : S.arrows.categoryMk (g ≫ f) (S.downward_closed hf g) ⟶
        S.arrows.categoryMk f hf := ObjectProperty.homMk (Over.homMk _ rfl)
      simpa using! π.naturality φ.op⟩
  invFun x :=
    { app := fun f => x.1 f.unop.1.hom f.unop.2
      naturality := fun f f' g => by
        have := x.2 f.unop.1.hom g.unop.hom.left f.unop.2
        dsimp at this ⊢
        rw [id_comp]; rw [← this]
        convert! rfl
        simp only [Over.w] }

variable {P S E}
variable {x : FamilyOfElements (P ⋙ coyoneda.obj E) S.arrows} (hx : SieveCompatible x)

/-- The cone corresponding to a `SieveCompatible` family of elements, dot notation enabled. -/
@[simp]
/--
Definition of `_root_.CategoryTheory.Presieve.FamilyOfElements.SieveCompatible.cone` / `_root_.CategoryTheory.Presieve.FamilyOfElements.SieveCompatible.cone` 的定义

English:
definition _root_.CategoryTheory.Presieve.FamilyOfElements.SieveCompatible.cone
  signature: :
  body: E.unop
  π := (conesEquivSieveCompatibleFamily P S E).invFun ⟨x, hx⟩

中文:
定义 _root_.范畴论.Presieve.FamilyOfElements.SieveCompatible.cone
  签名: :
  定义体: E.unop
  π := (conesEquivSieveCompatibleFamily P S E).invFun ⟨x, hx⟩

Depends on / 依赖: E.unop
-/
def _root_.CategoryTheory.Presieve.FamilyOfElements.SieveCompatible.cone :
    Cone (S.arrows.diagram.op ⋙ P) where
  pt := E.unop
  π := (conesEquivSieveCompatibleFamily P S E).invFun ⟨x, hx⟩

/--
Definition of `homEquivAmalgamation` / `homEquivAmalgamation` 的定义

English:
definition homEquivAmalgamation
  signature: :
  body: ⟨l.hom, fun _ f hf => l.w (op ⟨Over.mk f, hf⟩)⟩
  invFun t := ⟨t.1, fun f => t.2 f.unop.1.hom f.unop.2⟩

中文:
定义 homEquivAmalgamation
  签名: :
  定义体: ⟨l.hom, fun _ f hf => l.w (op ⟨Over.mk f, hf⟩)⟩
  invFun t := ⟨t.1, fun f => t.2 f.unop.1.hom f.unop.2⟩

Depends on / 依赖: Over.mk, l.hom
-/
def homEquivAmalgamation :
    (hx.cone ⟶ P.mapCone S.arrows.cocone.op) ≃ { t // x.IsAmalgamation t } where
  toFun l := ⟨l.hom, fun _ f hf => l.w (op ⟨Over.mk f, hf⟩)⟩
  invFun t := ⟨t.1, fun f => t.2 f.unop.1.hom f.unop.2⟩

variable (P S)

/--
theorem `isLimit_iff_isSheafFor` / 定理 `isLimit_iff_isSheafFor`

English:
theorem isLimit_iff_isSheafFor
  proof: by
  dsimp [IsSheafFor]; simp_rw [compatible_iff_sieveCompatible]
  rw [((Cone.isLimitEquivIsTerminal _).trans (isTerminalEquivUnique _ _)).nonempty_congr]
  rw [Classical.nonempty_pi]; constructor
  · intro hu E x hx
    specialize hu hx.cone
    rw [(homEquivAmalgamation hx).uniqueCongr.nonempty_congr] at hu
    exact (unique_subtype_iff_existsUnique _).1 hu
  · rintro h ⟨E, π⟩
    let eqv := conesEquivSieveCompatibleFamily P S (op E)
    rw [← eqv.left_inv π]
    erw [(homEquivAmalgamation (eqv π).2).uniqueCongr.nonempty_congr]
    rw [unique_subtype_iff_existsUnique]
    exact h _ _ (eqv π).2

中文:
定理 isLimit_iff_isSheafFor
  证明: by
  dsimp [IsSheafFor]; simp_rw [compatible_iff_sieveCompatible]
  rw [((Cone.isLimitEquivIsTerminal _).trans (isTerminalEquivUnique _ _)).nonempty_congr]
  rw [Classical.nonempty_pi]; constructor
  · intro hu E x hx
    specialize hu hx.cone
    rw [(homEquivAmalgamation hx).uniqueCongr.nonempty_congr] at hu
    exact (unique_subtype_iff_existsUnique _).1 hu
  · rintro h ⟨E, π⟩
    let eqv := conesEquivSieveCompatibleFamily P S (op E)
    rw [← eqv.left_inv π]
    erw [(homEquivAmalgamation (eqv π).2).uniqueCongr.nonempty_congr]
    rw [unique_subtype_iff_existsUnique]
    exact h _ _ (eqv π).2

Depends on / 依赖: Classical, Classical.nonempty_pi, Cone.isLimitEquivIsTerminal, IsSheafFor, compatible_iff_sieveCompatible, conesEquivSieveCompatibleFamily, eqv.left_inv, homEquivAmalgamation, hx.cone, isLimitEquivIsTerminal, isTerminalEquivUnique, left_inv, nonempty_cong, nonempty_congr, nonempty_pi, simp_rw, specialize, uniqueCongr, uniqueCongr.nonempty_cong, uniqueCongr.nonempty_congr
-/
theorem isLimit_iff_isSheafFor :
    Nonempty (IsLimit (P.mapCone S.arrows.cocone.op)) ↔
      forall E : Aᵒᵖ, IsSheafFor (P ⋙ coyoneda.obj E) S.arrows := by
  dsimp [IsSheafFor]; simp_rw [compatible_iff_sieveCompatible]
  rw [((Cone.isLimitEquivIsTerminal _).trans (isTerminalEquivUnique _ _)).nonempty_congr]
  rw [Classical.nonempty_pi]; constructor
  · intro hu E x hx
    specialize hu hx.cone
    rw [(homEquivAmalgamation hx).uniqueCongr.nonempty_congr] at hu
    exact (unique_subtype_iff_existsUnique _).1 hu
  · rintro h ⟨E, π⟩
    let eqv := conesEquivSieveCompatibleFamily P S (op E)
    rw [← eqv.left_inv π]
    erw [(homEquivAmalgamation (eqv π).2).uniqueCongr.nonempty_congr]
    rw [unique_subtype_iff_existsUnique]
    exact h _ _ (eqv π).2

/--
theorem `subsingleton_iff_isSeparatedFor` / 定理 `subsingleton_iff_isSeparatedFor`

English:
theorem subsingleton_iff_isSeparatedFor
  proof: by
  constructor
  · intro hs E x t₁ t₂ h₁ h₂
    have hx := is_compatible_of_exists_amalgamation x ⟨t₁, h₁⟩
    rw [compatible_iff_sieveCompatible] at hx
    specialize hs hx.cone
    rcases hs with ⟨hs⟩
    simpa only [Subtype.mk.injEq] using (show Subtype.mk t₁ h₁ = ⟨t₂, h₂⟩ from
      (homEquivAmalgamation hx).symm.injective (hs _ _))
  · rintro h ⟨E, π⟩
    let eqv := conesEquivSieveCompatibleFamily P S (op E)
    constructor
    rw [← eqv.left_inv π]
    intro f₁ f₂
    let eqv' := homEquivAmalgamation (eqv π).2
    apply eqv'.injective
    ext
    apply h _ (eqv π).1 <;> exact (eqv' _).2

中文:
定理 subsingleton_iff_isSeparatedFor
  证明: by
  constructor
  · intro hs E x t₁ t₂ h₁ h₂
    have hx := is_compatible_of_exists_amalgamation x ⟨t₁, h₁⟩
    rw [compatible_iff_sieveCompatible] at hx
    specialize hs hx.cone
    rcases hs with ⟨hs⟩
    simpa only [Subtype.mk.injEq] using (show Subtype.mk t₁ h₁ = ⟨t₂, h₂⟩ from
      (homEquivAmalgamation hx).symm.injective (hs _ _))
  · rintro h ⟨E, π⟩
    let eqv := conesEquivSieveCompatibleFamily P S (op E)
    constructor
    rw [← eqv.left_inv π]
    intro f₁ f₂
    let eqv' := homEquivAmalgamation (eqv π).2
    apply eqv'.injective
    ext
    apply h _ (eqv π).1 <;> exact (eqv' _).2

Depends on / 依赖: Subtype, Subtype.mk, Subtype.mk.injEq, compatible_iff_sieveCompatible, conesEquivSieveCompatibleFamily, eqv.left_inv, homEquivAmalgamation, hx.cone, injective, is_compatible_of_exists_amalgamation, left_inv, specialize, symm.injective
-/
theorem subsingleton_iff_isSeparatedFor :
    (forall c, Subsingleton (c ⟶ P.mapCone S.arrows.cocone.op)) ↔
      forall E : Aᵒᵖ, IsSeparatedFor (P ⋙ coyoneda.obj E) S.arrows := by
  constructor
  · intro hs E x t₁ t₂ h₁ h₂
    have hx := is_compatible_of_exists_amalgamation x ⟨t₁, h₁⟩
    rw [compatible_iff_sieveCompatible] at hx
    specialize hs hx.cone
    rcases hs with ⟨hs⟩
    simpa only [Subtype.mk.injEq] using (show Subtype.mk t₁ h₁ = ⟨t₂, h₂⟩ from
      (homEquivAmalgamation hx).symm.injective (hs _ _))
  · rintro h ⟨E, π⟩
    let eqv := conesEquivSieveCompatibleFamily P S (op E)
    constructor
    rw [← eqv.left_inv π]
    intro f₁ f₂
    let eqv' := homEquivAmalgamation (eqv π).2
    apply eqv'.injective
    ext
    apply h _ (eqv π).1 <;> exact (eqv' _).2

/--
theorem `isSheaf_iff_isLimit` / 定理 `isSheaf_iff_isLimit`

English:
theorem isSheaf_iff_isLimit
  proof: ⟨fun h _ S hS => (isLimit_iff_isSheafFor P S).2 fun E => h E.unop S hS, fun h E _ S hS =>
    (isLimit_iff_isSheafFor P S).1 (h S hS) (op E)⟩

中文:
定理 isSheaf_iff_isLimit
  证明: ⟨fun h _ S hS => (isLimit_iff_isSheafFor P S).2 fun E => h E.unop S hS, fun h E _ S hS =>
    (isLimit_iff_isSheafFor P S).1 (h S hS) (op E)⟩

Depends on / 依赖: E.unop, isLimit_iff_isSheafFor
-/
theorem isSheaf_iff_isLimit :
    IsSheaf J P ↔
      forall ⦃X : C⦄ (S : Sieve X), S in J X -> Nonempty (IsLimit (P.mapCone S.arrows.cocone.op)) :=
  ⟨fun h _ S hS => (isLimit_iff_isSheafFor P S).2 fun E => h E.unop S hS, fun h E _ S hS =>
    (isLimit_iff_isSheafFor P S).1 (h S hS) (op E)⟩

/--
theorem `isSeparated_iff_subsingleton` / 定理 `isSeparated_iff_subsingleton`

English:
theorem isSeparated_iff_subsingleton
  proof: ⟨fun h _ S hS => (subsingleton_iff_isSeparatedFor P S).2 fun E => h E.unop S hS, fun h E _ S hS =>
    (subsingleton_iff_isSeparatedFor P S).1 (h S hS) (op E)⟩

中文:
定理 isSeparated_iff_subsingleton
  证明: ⟨fun h _ S hS => (subsingleton_iff_isSeparatedFor P S).2 fun E => h E.unop S hS, fun h E _ S hS =>
    (subsingleton_iff_isSeparatedFor P S).1 (h S hS) (op E)⟩

Depends on / 依赖: E.unop, subsingleton_iff_isSeparatedFor
-/
theorem isSeparated_iff_subsingleton :
    (forall E : A, Presieve.IsSeparated J (P ⋙ coyoneda.obj (op E))) ↔
      forall ⦃X : C⦄ (S : Sieve X), S in J X -> forall c, Subsingleton (c ⟶ P.mapCone S.arrows.cocone.op) :=
  ⟨fun h _ S hS => (subsingleton_iff_isSeparatedFor P S).2 fun E => h E.unop S hS, fun h E _ S hS =>
    (subsingleton_iff_isSeparatedFor P S).1 (h S hS) (op E)⟩

/--
theorem `isLimit_iff_isSheafFor_presieve` / 定理 `isLimit_iff_isSheafFor_presieve`

English:
theorem isLimit_iff_isSheafFor_presieve
  proof: (isLimit_iff_isSheafFor P _).trans (forall_congr' fun _ => (isSheafFor_iff_generate _).symm)

中文:
定理 isLimit_iff_isSheafFor_presieve
  证明: (isLimit_iff_isSheafFor P _).trans (forall_congr' fun _ => (isSheafFor_iff_generate _).symm)

Depends on / 依赖: forall_congr, isLimit_iff_isSheafFor, isSheafFor_iff_generate
-/
theorem isLimit_iff_isSheafFor_presieve :
    Nonempty (IsLimit (P.mapCone (generate R).arrows.cocone.op)) ↔
      forall E : Aᵒᵖ, IsSheafFor (P ⋙ coyoneda.obj E) R :=
  (isLimit_iff_isSheafFor P _).trans (forall_congr' fun _ => (isSheafFor_iff_generate _).symm)

/--
theorem `isSheaf_iff_isLimit_pretopology` / 定理 `isSheaf_iff_isLimit_pretopology`

English:
theorem isSheaf_iff_isLimit_pretopology
  given: [HasPullbacks C] (K : Pretopology C)
  proof: by
  dsimp [IsSheaf]
  simp_rw [isSheaf_pretopology]
  exact
    ⟨fun h X R hR => (isLimit_iff_isSheafFor_presieve P R).2 fun E => h E.unop R hR,
      fun h E X R hR => (isLimit_iff_isSheafFor_presieve P R).1 (h R hR) (op E)⟩

中文:
定理 isSheaf_iff_isLimit_pretopology
  条件: [有Pullbacks C] (K : Pretopology C)
  证明: by
  dsimp [IsSheaf]
  simp_rw [isSheaf_pretopology]
  exact
    ⟨fun h X R hR => (isLimit_iff_isSheafFor_presieve P R).2 fun E => h E.unop R hR,
      fun h E X R hR => (isLimit_iff_isSheafFor_presieve P R).1 (h R hR) (op E)⟩

Depends on / 依赖: E.unop, IsSheaf, isLimit_iff_isSheafFor_presieve, isSheaf_pretopology, simp_rw
-/
theorem isSheaf_iff_isLimit_pretopology [HasPullbacks C] (K : Pretopology C) :
    IsSheaf K.toGrothendieck P ↔
      forall ⦃X : C⦄ (R : Presieve X),
        R in K X -> Nonempty (IsLimit (P.mapCone (generate R).arrows.cocone.op)) := by
  dsimp [IsSheaf]
  simp_rw [isSheaf_pretopology]
  exact
    ⟨fun h X R hR => (isLimit_iff_isSheafFor_presieve P R).2 fun E => h E.unop R hR,
      fun h E X R hR => (isLimit_iff_isSheafFor_presieve P R).1 (h R hR) (op E)⟩

end LimitSheafCondition

variable {J}

/--
Definition of `IsSheaf.amalgamate` / `IsSheaf.amalgamate` 的定义

English:
definition IsSheaf.amalgamate
  signature: {A : Type u₂} [Category.{v₂} A] {E : A} {X : C} {P : Cᵒᵖ ⥤ A}
  body: (hP _ _ S.condition).amalgamate (fun Y f hf => x ⟨Y, f, hf⟩) fun _ _ _ _ _ _ _ h₁ h₂ w =>
    @hx { hf := h₁, .. } { hf := h₂, .. } { w := w, .. }

@[reassoc (attr := simp)]

中文:
定义 是层.amalgamate
  签名: {A : 类型u₂} [范畴.{v₂} A] {E : A} {X : C} {P : Cᵒᵖ ⥤ A}
  定义体: (hP _ _ S.condition).amalgamate (fun Y f hf => x ⟨Y, f, hf⟩) fun _ _ _ _ _ _ _ h₁ h₂ w =>
    @hx { hf := h₁, .. } { hf := h₂, .. } { w := w, .. }

@[reassoc (attr := simp)]

Depends on / 依赖: S.condition, amalgamate, condition
-/
def IsSheaf.amalgamate {A : Type u₂} [Category.{v₂} A] {E : A} {X : C} {P : Cᵒᵖ ⥤ A}
    (hP : Presheaf.IsSheaf J P) (S : J.Cover X) (x : forall I : S.Arrow, E ⟶ P.obj (op I.Y))
    (hx : forall ⦃I₁ I₂ : S.Arrow⦄ (r : I₁.Relation I₂),
       x I₁ ≫ P.map r.g₁.op = x I₂ ≫ P.map r.g₂.op) : E ⟶ P.obj (op X) :=
  (hP _ _ S.condition).amalgamate (fun Y f hf => x ⟨Y, f, hf⟩) fun _ _ _ _ _ _ _ h₁ h₂ w =>
    @hx { hf := h₁, .. } { hf := h₂, .. } { w := w, .. }

@[reassoc (attr := simp)]
/--
theorem `IsSheaf.amalgamate_map` / 定理 `IsSheaf.amalgamate_map`

English:
theorem IsSheaf.amalgamate_map
  statement: {A : Type u₂} [Category.{v₂} A] {E : A} {X : C} {P : Cᵒᵖ ⥤ A}
  proof: by
  apply (hP _ _ S.condition).valid_glue

中文:
定理 是层.amalgamate_map
  结论: {A : 类型u₂} [范畴.{v₂} A] {E : A} {X : C} {P : Cᵒᵖ ⥤ A}
  证明: by
  apply (hP _ _ S.condition).valid_glue

Depends on / 依赖: S.condition, condition, valid_glue
-/
theorem IsSheaf.amalgamate_map {A : Type u₂} [Category.{v₂} A] {E : A} {X : C} {P : Cᵒᵖ ⥤ A}
    (hP : Presheaf.IsSheaf J P) (S : J.Cover X) (x : forall I : S.Arrow, E ⟶ P.obj (op I.Y))
    (hx : forall ⦃I₁ I₂ : S.Arrow⦄ (r : I₁.Relation I₂),
       x I₁ ≫ P.map r.g₁.op = x I₂ ≫ P.map r.g₂.op)
    (I : S.Arrow) :
    hP.amalgamate S x hx ≫ P.map I.f.op = x _ := by
  apply (hP _ _ S.condition).valid_glue

/--
theorem `IsSheaf.hom_ext` / 定理 `IsSheaf.hom_ext`

English:
theorem IsSheaf.hom_ext
  statement: {A : Type u₂} [Category.{v₂} A] {E : A} {X : C} {P : Cᵒᵖ ⥤ A}
  proof: (hP _ _ S.condition).isSeparatedFor.ext fun Y f hf => h ⟨Y, f, hf⟩

中文:
定理 是层.hom_ext
  结论: {A : 类型u₂} [范畴.{v₂} A] {E : A} {X : C} {P : Cᵒᵖ ⥤ A}
  证明: (hP _ _ S.condition).isSeparatedFor.ext fun Y f hf => h ⟨Y, f, hf⟩

Depends on / 依赖: S.condition, condition, isSeparatedFor, isSeparatedFor.ext
-/
theorem IsSheaf.hom_ext {A : Type u₂} [Category.{v₂} A] {E : A} {X : C} {P : Cᵒᵖ ⥤ A}
    (hP : Presheaf.IsSheaf J P) (S : J.Cover X) (e₁ e₂ : E ⟶ P.obj (op X))
    (h : forall I : S.Arrow, e₁ ≫ P.map I.f.op = e₂ ≫ P.map I.f.op) : e₁ = e₂ :=
  (hP _ _ S.condition).isSeparatedFor.ext fun Y f hf => h ⟨Y, f, hf⟩

/--
lemma `IsSheaf.hom_ext_ofArrows` / 引理 `IsSheaf.hom_ext_ofArrows`

English:
lemma IsSheaf.hom_ext_ofArrows
  proof: by
  apply hP.hom_ext ⟨_, hf⟩
  rintro ⟨Z, _, _, g, _, ⟨i⟩, rfl⟩
  dsimp
  rw [P.map_comp]; rw [reassoc_of% (h i)]

中文:
引理 是层.hom_ext_ofArrows
  证明: by
  apply hP.hom_ext ⟨_, hf⟩
  rintro ⟨Z, _, _, g, _, ⟨i⟩, rfl⟩
  dsimp
  rw [P.map_comp]; rw [reassoc_of% (h i)]

Depends on / 依赖: P.map_comp, hP.hom_ext, hom_ext, map_comp, reassoc_of
-/
lemma IsSheaf.hom_ext_ofArrows
    {P : Cᵒᵖ ⥤ A} (hP : Presheaf.IsSheaf J P) {I : Type*} {S : C} {X : I -> C}
    (f : forall i, X i ⟶ S) (hf : Sieve.ofArrows _ f in J S) {E : A}
    {x y : E ⟶ P.obj (op S)} (h : forall i, x ≫ P.map (f i).op = y ≫ P.map (f i).op) :
    x = y := by
  apply hP.hom_ext ⟨_, hf⟩
  rintro ⟨Z, _, _, g, _, ⟨i⟩, rfl⟩
  dsimp
  rw [P.map_comp]; rw [reassoc_of% (h i)]

section

variable {P : Cᵒᵖ ⥤ A} (hP : Presheaf.IsSheaf J P) {I : Type*} {S : C} {X : I -> C}
  (f : forall i, X i ⟶ S) (hf : Sieve.ofArrows _ f in J S) {E : A}
  (x : forall i, E ⟶ P.obj (op (X i)))
  (hx : forall ⦃W : C⦄ ⦃i j : I⦄ (a : W ⟶ X i) (b : W ⟶ X j),
    a ≫ f i = b ≫ f j -> x i ≫ P.map a.op = x j ≫ P.map b.op)
include hP hf hx

/--
lemma `IsSheaf.existsUnique_amalgamation_ofArrows` / 引理 `IsSheaf.existsUnique_amalgamation_ofArrows`

English:
lemma IsSheaf.existsUnique_amalgamation_ofArrows
  proof: (Presieve.isSheafFor_arrows_iff _ _).1
    ((Presieve.isSheafFor_iff_generate _).2 (hP E _ hf)) x (fun _ _ _ _ _ w => hx _ _ w)

中文:
引理 是层.存在Unique_amalgamation_ofArrows
  证明: (Presieve.isSheafFor_arrows_iff _ _).1
    ((Presieve.isSheafFor_iff_generate _).2 (hP E _ hf)) x (fun _ _ _ _ _ w => hx _ _ w)

Depends on / 依赖: Presieve, Presieve.isSheafFor_arrows_iff, Presieve.isSheafFor_iff_generate, isSheafFor_arrows_iff, isSheafFor_iff_generate
-/
lemma IsSheaf.existsUnique_amalgamation_ofArrows :
    exists! (g : E ⟶ P.obj (op S)), forall (i : I), g ≫ P.map (f i).op = x i :=
  (Presieve.isSheafFor_arrows_iff _ _).1
    ((Presieve.isSheafFor_iff_generate _).2 (hP E _ hf)) x (fun _ _ _ _ _ w => hx _ _ w)

/--
Definition of `IsSheaf.amalgamateOfArrows` / `IsSheaf.amalgamateOfArrows` 的定义

English:
definition IsSheaf.amalgamateOfArrows
  signature: : E ⟶ P.obj (op S)
  body: (hP.existsUnique_amalgamation_ofArrows f hf x hx).choose

@[reassoc (attr := simp)]

中文:
定义 是层.amalgamateOfArrows
  签名: : E ⟶ P.obj (op S)
  定义体: (hP.existsUnique_amalgamation_ofArrows f hf x hx).choose

@[reassoc (attr := simp)]

Depends on / 依赖: existsUnique_amalgamation_ofArrows, hP.existsUnique_amalgamation_ofArrows
-/
def IsSheaf.amalgamateOfArrows : E ⟶ P.obj (op S) :=
  (hP.existsUnique_amalgamation_ofArrows f hf x hx).choose

@[reassoc (attr := simp)]
/--
lemma `IsSheaf.amalgamateOfArrows_map` / 引理 `IsSheaf.amalgamateOfArrows_map`

English:
lemma IsSheaf.amalgamateOfArrows_map
  given: (i : I)
  proof: (hP.existsUnique_amalgamation_ofArrows f hf x hx).choose_spec.1 i

中文:
引理 是层.amalgamateOfArrows_map
  条件: (i : I)
  证明: (hP.existsUnique_amalgamation_ofArrows f hf x hx).choose_spec.1 i

Depends on / 依赖: choose_spec, existsUnique_amalgamation_ofArrows, hP.existsUnique_amalgamation_ofArrows
-/
lemma IsSheaf.amalgamateOfArrows_map (i : I) :
    hP.amalgamateOfArrows f hf x hx ≫ P.map (f i).op = x i :=
  (hP.existsUnique_amalgamation_ofArrows f hf x hx).choose_spec.1 i

end

/--
theorem `isSheaf_of_iso_iff` / 定理 `isSheaf_of_iso_iff`

English:
theorem isSheaf_of_iso_iff
  given: {P P' : Cᵒᵖ ⥤ A} (e : P ≅ P')
  statement: IsSheaf J P ↔ IsSheaf J P'
  proof: forall_congr' fun _ =>
    ⟨Presieve.isSheaf_iso J (Functor.isoWhiskerRight e _),
      Presieve.isSheaf_iso J (Functor.isoWhiskerRight e.symm _)⟩

中文:
定理 isSheaf_of_iso_iff
  条件: {P P' : Cᵒᵖ ⥤ A} (e : P ≅ P')
  结论: 是层 J P ↔ 是层 J P'
  证明: forall_congr' fun _ =>
    ⟨Presieve.isSheaf_iso J (Functor.isoWhiskerRight e _),
      Presieve.isSheaf_iso J (Functor.isoWhiskerRight e.symm _)⟩

Depends on / 依赖: Functor, Functor.isoWhiskerRight, Presieve, Presieve.isSheaf_iso, e.symm, forall_congr, isSheaf_iso, isoWhiskerRight
-/
theorem isSheaf_of_iso_iff {P P' : Cᵒᵖ ⥤ A} (e : P ≅ P') : IsSheaf J P ↔ IsSheaf J P' :=
  forall_congr' fun _ =>
    ⟨Presieve.isSheaf_iso J (Functor.isoWhiskerRight e _),
      Presieve.isSheaf_iso J (Functor.isoWhiskerRight e.symm _)⟩

variable (J)

/--
theorem `isSheaf_of_isTerminal` / 定理 `isSheaf_of_isTerminal`

English:
theorem isSheaf_of_isTerminal
  given: {X : A} (hX : IsTerminal X)
  proof: fun _ _ _ _ _ _ =>
  ⟨hX.from _, fun _ _ _ => hX.hom_ext _ _, fun _ _ => hX.hom_ext _ _⟩

中文:
定理 isSheaf_of_isTerminal
  条件: {X : A} (hX : 是终止 X)
  证明: fun _ _ _ _ _ _ =>
  ⟨hX.from _, fun _ _ _ => hX.hom_ext _ _, fun _ _ => hX.hom_ext _ _⟩
-/
theorem isSheaf_of_isTerminal {X : A} (hX : IsTerminal X) :
    Presheaf.IsSheaf J ((CategoryTheory.Functor.const _).obj X) := fun _ _ _ _ _ _ =>
  ⟨hX.from _, fun _ _ _ => hX.hom_ext _ _, fun _ _ => hX.hom_ext _ _⟩

end Presheaf

variable {C : Type u₁} [Category.{v₁} C]
variable (J : GrothendieckTopology C)
variable (A : Type u₂) [Category.{v₂} A]

/--
Definition of `Sheaf` / `Sheaf` 的定义

English:
abbreviation Sheaf
  body: ObjectProperty.FullSubcategory (Presheaf.IsSheaf J (A := A))

中文:
缩写 层
  定义体: ObjectProperty.FullSubcategory (Presheaf.IsSheaf J (A := A))

Depends on / 依赖: FullSubcategory, IsSheaf, ObjectProperty, ObjectProperty.FullSubcategory, Presheaf, Presheaf.IsSheaf
-/
abbrev Sheaf := ObjectProperty.FullSubcategory (Presheaf.IsSheaf J (A := A))

section

variable {J A}

/-- The underlying presheaf of a sheaf. -/
@[deprecated "Use ObjectProperty.obj" (since := "2026-03-03")]
/--
Definition of `Sheaf.val` / `Sheaf.val` 的定义

English:
abbreviation Sheaf.val
  signature: (F : Sheaf J A)
  body: F.obj

@[deprecated "Use ObjectProperty.FullSubcategory.property" (since := "2026-03-03")]

中文:
缩写 层.val
  签名: (F : 层 J A)
  定义体: F.obj

@[deprecated "Use ObjectProperty.FullSubcategory.property" (since := "2026-03-03")]

Depends on / 依赖: F.obj
-/
abbrev Sheaf.val (F : Sheaf J A) : Cᵒᵖ ⥤ A := F.obj

@[deprecated "Use ObjectProperty.FullSubcategory.property" (since := "2026-03-03")]
/--
lemma `Sheaf.cond` / 引理 `Sheaf.cond`

English:
lemma Sheaf.cond
  given: (F : Sheaf J A)
  statement: Presheaf.IsSheaf J F.obj
  proof: F.property

@[deprecated (since := "2026-03-03")]
alias Sheaf.Hom.mk := ObjectProperty.homMk

中文:
引理 层.cond
  条件: (F : 层 J A)
  结论: 预层.是层 J F.obj
  证明: F.property

@[deprecated (since := "2026-03-03")]
alias Sheaf.Hom.mk := ObjectProperty.homMk

Depends on / 依赖: F.property, property
-/
lemma Sheaf.cond (F : Sheaf J A) : Presheaf.IsSheaf J F.obj := F.property

@[deprecated (since := "2026-03-03")]
alias Sheaf.Hom.mk := ObjectProperty.homMk

/--
lemma `Sheaf.hom_ext_iff` / 引理 `Sheaf.hom_ext_iff`

English:
lemma Sheaf.hom_ext_iff
  given: {F G : Sheaf J A} {f g : F ⟶ G}
  proof: by
  cat_disch

中文:
引理 层.hom_ext_iff
  条件: {F G : 层 J A} {f g : F ⟶ G}
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
lemma Sheaf.hom_ext_iff {F G : Sheaf J A} {f g : F ⟶ G} :
    f = g ↔ f.hom = g.hom := by
  cat_disch

/--
lemma `Sheaf.hom_ext` / 引理 `Sheaf.hom_ext`

English:
lemma Sheaf.hom_ext
  given: {F G : Sheaf J A} {f g : F ⟶ G} (h : f.hom = g.hom)
  proof: by
  cat_disch

中文:
引理 层.hom_ext
  条件: {F G : 层 J A} {f g : F ⟶ G} (h : f.hom = g.hom)
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
lemma Sheaf.hom_ext {F G : Sheaf J A} {f g : F ⟶ G} (h : f.hom = g.hom) :
    f = g := by
  cat_disch

end

/--
Definition of `sheafToPresheaf` / `sheafToPresheaf` 的定义

English:
abbreviation sheafToPresheaf
  signature: : Sheaf J A ⥤ Cᵒᵖ ⥤ A
  body: ObjectProperty.ι _

中文:
缩写 sheafToPresheaf
  签名: : 层 J A ⥤ Cᵒᵖ ⥤ A
  定义体: ObjectProperty.ι _

Depends on / 依赖: ObjectProperty
-/
abbrev sheafToPresheaf : Sheaf J A ⥤ Cᵒᵖ ⥤ A := ObjectProperty.ι _

/--
Definition of `sheafSections` / `sheafSections` 的定义

English:
abbreviation sheafSections
  signature: : Cᵒᵖ ⥤ Sheaf J A ⥤ A
  body: (sheafToPresheaf J A).flip

中文:
缩写 sheafSections
  签名: : Cᵒᵖ ⥤ 层 J A ⥤ A
  定义体: (sheafToPresheaf J A).flip

Depends on / 依赖: sheafToPresheaf
-/
abbrev sheafSections : Cᵒᵖ ⥤ Sheaf J A ⥤ A := (sheafToPresheaf J A).flip

/-- The sheaf sections functor on `X` is given by evaluation of presheaves on `X`. -/
@[simps!]
/--
Definition of `sheafSectionsNatIsoEvaluation` / `sheafSectionsNatIsoEvaluation` 的定义

English:
definition sheafSectionsNatIsoEvaluation
  signature: {X : C}
  body: Iso.refl _

中文:
定义 sheafSections自然数IsoEvaluation
  签名: {X : C}
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def sheafSectionsNatIsoEvaluation {X : C} :
    (sheafSections J A).obj (op X) ≅ sheafToPresheaf J A ⋙ (evaluation _ _).obj (op X) :=
  Iso.refl _

/--
Definition of `fullyFaithfulSheafToPresheaf` / `fullyFaithfulSheafToPresheaf` 的定义

English:
abbreviation fullyFaithfulSheafToPresheaf
  signature: : (sheafToPresheaf J A).FullyFaithful
  body: ObjectProperty.fullyFaithfulι _

中文:
缩写 fullyFaithfulSheafToPresheaf
  签名: : (sheafToPresheaf J A).满忠实
  定义体: ObjectProperty.fullyFaithfulι _

Depends on / 依赖: ObjectProperty, ObjectProperty.fullyFaithful
-/
abbrev fullyFaithfulSheafToPresheaf : (sheafToPresheaf J A).FullyFaithful :=
  ObjectProperty.fullyFaithfulι _

section

variable {J A}

/--
Definition of `Sheaf.homEquiv` / `Sheaf.homEquiv` 的定义

English:
abbreviation Sheaf.homEquiv
  signature: {X Y : Sheaf J A}
  body: (fullyFaithfulSheafToPresheaf J A).homEquiv

#adaptation_note

中文:
缩写 层.homEquiv
  签名: {X Y : 层 J A}
  定义体: (fullyFaithfulSheafToPresheaf J A).homEquiv

#adaptation_note

Depends on / 依赖: fullyFaithfulSheafToPresheaf, homEquiv
-/
abbrev Sheaf.homEquiv {X Y : Sheaf J A} : (X ⟶ Y) ≃ (X.obj ⟶ Y.obj) :=
  (fullyFaithfulSheafToPresheaf J A).homEquiv

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- `Sheaf.homEquiv` as a natural isomorphism. -/
@[simps! +dsimpLhs]
/--
Definition of `sheafToPresheafCompYonedaCompWhiskeringLeftSheafToPresheaf` / `sheafToPresheafCompYonedaCompWhiskeringLeftSheafToPresheaf` 的定义

English:
definition sheafToPresheafCompYonedaCompWhiskeringLeftSheafToPresheaf
  signature: :
  body: Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight uliftYonedaIsoYoneda.{max u₁ v₂}.symm _) ≪≫
    (fullyFaithfulSheafToPresheaf J A).compUliftYonedaCompWhiskeringLeft ≪≫
    uliftYonedaIsoYoneda

中文:
定义 sheafToPresheafCompYonedaCompWhiskeringLeftSheafToPresheaf
  签名: :
  定义体: Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight uliftYonedaIsoYoneda.{max u₁ v₂}.symm _) ≪≫
    (fullyFaithfulSheafToPresheaf J A).compUliftYonedaCompWhiskeringLeft ≪≫
    uliftYonedaIsoYoneda

Depends on / 依赖: Functor, Functor.isoWhiskerLeft, Functor.isoWhiskerRight, compUliftYonedaCompWhiskeringLeft, fullyFaithfulSheafToPresheaf, isoWhiskerLeft, isoWhiskerRight, uliftYonedaIsoYoneda
-/
def sheafToPresheafCompYonedaCompWhiskeringLeftSheafToPresheaf :
    sheafToPresheaf J A ⋙ yoneda ⋙ (Functor.whiskeringLeft _ _ _).obj (sheafToPresheaf J A).op ≅
      yoneda :=
  Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight uliftYonedaIsoYoneda.{max u₁ v₂}.symm _) ≪≫
    (fullyFaithfulSheafToPresheaf J A).compUliftYonedaCompWhiskeringLeft ≪≫
    uliftYonedaIsoYoneda

/--
lemma `sheafToPresheafCompYonedaCompWhiskeringLeftSheafToPresheaf_app_app` / 引理 `sheafToPresheafCompYonedaCompWhiskeringLeftSheafToPresheaf_app_app`

English:
lemma sheafToPresheafCompYonedaCompWhiskeringLeftSheafToPresheaf_app_app
  given: {X Y : Sheaf J A}
  proof: rfl

#adaptation_note

中文:
引理 sheafToPresheafCompYonedaCompWhiskeringLeftSheafToPresheaf_app_app
  条件: {X Y : 层 J A}
  证明: rfl

#adaptation_note
-/
lemma sheafToPresheafCompYonedaCompWhiskeringLeftSheafToPresheaf_app_app {X Y : Sheaf J A} :
    (sheafToPresheafCompYonedaCompWhiskeringLeftSheafToPresheaf.app X).app (op Y) =
      Sheaf.homEquiv.symm.toIso :=
  rfl

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- `Sheaf.homEquiv` as a natural isomorphism, using coyoneda. -/
@[simps! +dsimpLhs]
/--
Definition of `sheafToPresheafCompCoyonedaCompWhiskeringLeftSheafToPresheaf` / `sheafToPresheafCompCoyonedaCompWhiskeringLeftSheafToPresheaf` 的定义

English:
definition sheafToPresheafCompCoyonedaCompWhiskeringLeftSheafToPresheaf
  signature: :
  body: Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight uliftCoyonedaIsoCoyoneda.{max u₁ v₂}.symm _) ≪≫
    (fullyFaithfulSheafToPresheaf J A).compUliftCoyonedaCompWhiskeringLeft ≪≫
    uliftCoyonedaIsoCoyoneda

中文:
定义 sheafToPresheafCompCoyonedaCompWhiskeringLeftSheafToPresheaf
  签名: :
  定义体: Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight uliftCoyonedaIsoCoyoneda.{max u₁ v₂}.symm _) ≪≫
    (fullyFaithfulSheafToPresheaf J A).compUliftCoyonedaCompWhiskeringLeft ≪≫
    uliftCoyonedaIsoCoyoneda

Depends on / 依赖: Functor, Functor.isoWhiskerLeft, Functor.isoWhiskerRight, compUliftCoyonedaCompWhiskeringLeft, fullyFaithfulSheafToPresheaf, isoWhiskerLeft, isoWhiskerRight, uliftCoyonedaIsoCoyoneda
-/
def sheafToPresheafCompCoyonedaCompWhiskeringLeftSheafToPresheaf :
    (sheafToPresheaf J A).op ⋙ coyoneda ⋙
      (Functor.whiskeringLeft _ _ _).obj (sheafToPresheaf J A) ≅
      coyoneda :=
  Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight uliftCoyonedaIsoCoyoneda.{max u₁ v₂}.symm _) ≪≫
    (fullyFaithfulSheafToPresheaf J A).compUliftCoyonedaCompWhiskeringLeft ≪≫
    uliftCoyonedaIsoCoyoneda

/--
lemma `sheafToPresheafCompCoyonedaCompWhiskeringLeftSheafToPresheaf_app_app` / 引理 `sheafToPresheafCompCoyonedaCompWhiskeringLeftSheafToPresheaf_app_app`

English:
lemma sheafToPresheafCompCoyonedaCompWhiskeringLeftSheafToPresheaf_app_app
  given: {X Y : Sheaf J A}
  proof: rfl

中文:
引理 sheafToPresheafCompCoyonedaCompWhiskeringLeftSheafToPresheaf_app_app
  条件: {X Y : 层 J A}
  证明: rfl
-/
lemma sheafToPresheafCompCoyonedaCompWhiskeringLeftSheafToPresheaf_app_app {X Y : Sheaf J A} :
    (sheafToPresheafCompCoyonedaCompWhiskeringLeftSheafToPresheaf.app (op X)).app Y =
      Sheaf.homEquiv.symm.toIso :=
  rfl

end

/--
theorem `Sheaf.Hom.mono_of_presheaf_mono` / 定理 `Sheaf.Hom.mono_of_presheaf_mono`

English:
theorem Sheaf.Hom.mono_of_presheaf_mono
  given: {F G : Sheaf J A} (f : F ⟶ G) [h : Mono f.1]
  statement: Mono f
  proof: (sheafToPresheaf J A).mono_of_mono_map h

中文:
定理 层.态射.mono_of_presheaf_mono
  条件: {F G : 层 J A} (f : F ⟶ G) [h : 单态射 f.1]
  结论: 单态射 f
  证明: (sheafToPresheaf J A).mono_of_mono_map h

Depends on / 依赖: mono_of_mono_map, sheafToPresheaf
-/
theorem Sheaf.Hom.mono_of_presheaf_mono {F G : Sheaf J A} (f : F ⟶ G) [h : Mono f.1] : Mono f :=
  (sheafToPresheaf J A).mono_of_mono_map h

/--
Instance `Sheaf.Hom.epi_of_presheaf_epi` / 实例 `Sheaf.Hom.epi_of_presheaf_epi`

English:
instance Sheaf.Hom.epi_of_presheaf_epi
  signature: {F G : Sheaf J A} (f : F ⟶ G) [h : Epi f.1]
  body: (sheafToPresheaf J A).epi_of_epi_map h

中文:
实例 层.态射.epi_of_presheaf_epi
  签名: {F G : 层 J A} (f : F ⟶ G) [h : 满态射 f.1]
  定义体: (sheafToPresheaf J A).epi_of_epi_map h

Depends on / 依赖: epi_of_epi_map, sheafToPresheaf
-/
instance Sheaf.Hom.epi_of_presheaf_epi {F G : Sheaf J A} (f : F ⟶ G) [h : Epi f.1] : Epi f :=
  (sheafToPresheaf J A).epi_of_epi_map h

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
theorem `isSheaf_iff_isSheaf_of_type` / 定理 `isSheaf_iff_isSheaf_of_type`

English:
theorem isSheaf_iff_isSheaf_of_type
  given: (P : Cᵒᵖ ⥤ Type w)
  proof: by
  constructor
  · intro hP
    refine Presieve.isSheaf_iso J ?_ (hP (PUnit))
    exact Functor.isoWhiskerLeft _ Coyoneda.punitIso ≪≫ P.rightUnitor
  · intro hP X Y S hS z hz
    refine ⟨↾fun x => (hP S hS).amalgamate (fun Z f hf =>
      (ConcreteCategory.hom (z f hf)) x) ?_, ?_, ?_⟩
    · intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ h
      exact (ConcreteCategory.congr_hom (hz g₁ g₂ hf₁ hf₂ h)) x
    · intro Z f hf
      apply ConcreteCategory.hom_ext
      intro x
      simp only [Functor.comp_obj, Functor.flip_obj_obj, yoneda_obj_obj, Functor.comp_map,
        Functor.flip_obj_map, yoneda_map_app, ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk,
        comp_apply]
      apply Presieve.IsSheafFor.valid_glue
    · intro y hy
      apply ConcreteCategory.hom_ext
      intro x
      apply (hP S hS).isSeparatedFor.ext
      intro Y' f hf
      simp [Presieve.IsSheafFor.valid_glue _ _ _ hf, ← hy _ hf]

中文:
定理 isSheaf_iff_isSheaf_of_type
  条件: (P : Cᵒᵖ ⥤ 类型 w)
  证明: by
  constructor
  · intro hP
    refine Presieve.isSheaf_iso J ?_ (hP (PUnit))
    exact Functor.isoWhiskerLeft _ Coyoneda.punitIso ≪≫ P.rightUnitor
  · intro hP X Y S hS z hz
    refine ⟨↾fun x => (hP S hS).amalgamate (fun Z f hf =>
      (ConcreteCategory.hom (z f hf)) x) ?_, ?_, ?_⟩
    · intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ h
      exact (ConcreteCategory.congr_hom (hz g₁ g₂ hf₁ hf₂ h)) x
    · intro Z f hf
      apply ConcreteCategory.hom_ext
      intro x
      simp only [Functor.comp_obj, Functor.flip_obj_obj, yoneda_obj_obj, Functor.comp_map,
        Functor.flip_obj_map, yoneda_map_app, ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk,
        comp_apply]
      apply Presieve.IsSheafFor.valid_glue
    · intro y hy
      apply ConcreteCategory.hom_ext
      intro x
      apply (hP S hS).isSeparatedFor.ext
      intro Y' f hf
      simp [Presieve.IsSheafFor.valid_glue _ _ _ hf, ← hy _ hf]

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, ConcreteCategory.hom, ConcreteCategory.hom_ext, Coyoneda, Coyoneda.punitIso, Functor, Functor.comp_map, Functor.comp_obj, Functor.flip_obj_obj, Functor.isoWhiskerLeft, P.rightUnitor, Presieve, Presieve.isSheaf_iso, amalgamate, comp_map, comp_obj, congr_hom, flip_obj_obj, hom_ext
-/
theorem isSheaf_iff_isSheaf_of_type (P : Cᵒᵖ ⥤ Type w) :
    Presheaf.IsSheaf J P ↔ Presieve.IsSheaf J P := by
  constructor
  · intro hP
    refine Presieve.isSheaf_iso J ?_ (hP (PUnit))
    exact Functor.isoWhiskerLeft _ Coyoneda.punitIso ≪≫ P.rightUnitor
  · intro hP X Y S hS z hz
    refine ⟨↾fun x => (hP S hS).amalgamate (fun Z f hf =>
      (ConcreteCategory.hom (z f hf)) x) ?_, ?_, ?_⟩
    · intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ h
      exact (ConcreteCategory.congr_hom (hz g₁ g₂ hf₁ hf₂ h)) x
    · intro Z f hf
      apply ConcreteCategory.hom_ext
      intro x
      simp only [Functor.comp_obj, Functor.flip_obj_obj, yoneda_obj_obj, Functor.comp_map,
        Functor.flip_obj_map, yoneda_map_app, ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk,
        comp_apply]
      apply Presieve.IsSheafFor.valid_glue
    · intro y hy
      apply ConcreteCategory.hom_ext
      intro x
      apply (hP S hS).isSeparatedFor.ext
      intro Y' f hf
      simp [Presieve.IsSheafFor.valid_glue _ _ _ hf, ← hy _ hf]

/-- The sheaf of sections guaranteed by the sheaf condition. -/
@[simps]
/--
Definition of `sheafOver` / `sheafOver` 的定义

English:
definition sheafOver
  signature: {A : Type u₂} [Category.{v₂} A] {J : GrothendieckTopology C} (ℱ : Sheaf J A) (E : A)
  body: ℱ.obj ⋙ coyoneda.obj (op E)
  property := by
    rw [isSheaf_iff_isSheaf_of_type]
    exact ℱ.property E

中文:
定义 sheafOver
  签名: {A : 类型u₂} [范畴.{v₂} A] {J : Grothendieck拓扑 C} (ℱ : 层 J A) (E : A)
  定义体: ℱ.obj ⋙ coyoneda.obj (op E)
  property := by
    rw [isSheaf_iff_isSheaf_of_type]
    exact ℱ.property E

Depends on / 依赖: coyoneda, coyoneda.obj
-/
def sheafOver {A : Type u₂} [Category.{v₂} A] {J : GrothendieckTopology C} (ℱ : Sheaf J A) (E : A) :
    Sheaf J (Type _) where
  obj := ℱ.obj ⋙ coyoneda.obj (op E)
  property := by
    rw [isSheaf_iff_isSheaf_of_type]
    exact ℱ.property E

variable {J} in
/--
lemma `Presheaf.IsSheaf.isSheafFor` / 引理 `Presheaf.IsSheaf.isSheafFor`

English:
lemma Presheaf.IsSheaf.isSheafFor
  statement: {P : Cᵒᵖ ⥤ Type w} (hP : Presheaf.IsSheaf J P)
  proof: by
  rw [isSheaf_iff_isSheaf_of_type] at hP
  exact hP S hS

中文:
引理 预层.是层.isSheafFor
  结论: {P : Cᵒᵖ ⥤ 类型 w} (hP : 预层.是层 J P)
  证明: by
  rw [isSheaf_iff_isSheaf_of_type] at hP
  exact hP S hS

Depends on / 依赖: isSheaf_iff_isSheaf_of_type
-/
lemma Presheaf.IsSheaf.isSheafFor {P : Cᵒᵖ ⥤ Type w} (hP : Presheaf.IsSheaf J P)
    {X : C} (S : Sieve X) (hS : S in J X) : Presieve.IsSheafFor P S.arrows := by
  rw [isSheaf_iff_isSheaf_of_type] at hP
  exact hP S hS

variable {A} in
/--
lemma `Presheaf.isSheaf_bot` / 引理 `Presheaf.isSheaf_bot`

English:
lemma Presheaf.isSheaf_bot
  given: (P : Cᵒᵖ ⥤ A)
  statement: IsSheaf ⊥ P
  proof: fun _ => Presieve.isSheaf_bot

中文:
引理 预层.isSheaf_bot
  条件: (P : Cᵒᵖ ⥤ A)
  结论: 是层 ⊥ P
  证明: fun _ => Presieve.isSheaf_bot

Depends on / 依赖: Presieve, Presieve.isSheaf_bot, isSheaf_bot
-/
lemma Presheaf.isSheaf_bot (P : Cᵒᵖ ⥤ A) : IsSheaf ⊥ P := fun _ => Presieve.isSheaf_bot

variable {A J} in
/--
lemma `Presheaf.IsSheaf.of_le` / 引理 `Presheaf.IsSheaf.of_le`

English:
lemma Presheaf.IsSheaf.of_le
  statement: {K : GrothendieckTopology C} {F : Cᵒᵖ ⥤ A} (hle : J <= K)
  proof: fun _ _ _ hS => h _ _ (hle _ hS)

中文:
引理 预层.是层.of_le
  结论: {K : Grothendieck拓扑 C} {F : Cᵒᵖ ⥤ A} (hle : J <= K)
  证明: fun _ _ _ hS => h _ _ (hle _ hS)
-/
lemma Presheaf.IsSheaf.of_le {K : GrothendieckTopology C} {F : Cᵒᵖ ⥤ A} (hle : J <= K)
    (h : Presheaf.IsSheaf K F) :
    Presheaf.IsSheaf J F :=
  fun _ _ _ hS => h _ _ (hle _ hS)

set_option backward.isDefEq.respectTransparency.types false in
/--
The category of sheaves on the bottom (trivial) Grothendieck topology is
equivalent to the category of presheaves.
-/
@[simps]
/--
Definition of `sheafBotEquivalence` / `sheafBotEquivalence` 的定义

English:
definition sheafBotEquivalence
  signature: : Sheaf (⊥ : GrothendieckTopology C) A ≌ Cᵒᵖ ⥤ A where
  body: sheafToPresheaf _ _
  inverse :=
    { obj := fun P => ⟨P, Presheaf.isSheaf_bot P⟩
      map := fun f => ⟨f⟩ }
  unitIso := Iso.refl _
  counitIso := Iso.refl _

中文:
定义 sheafBotEquivalence
  签名: : 层 (⊥ : Grothendieck拓扑 C) A ≌ Cᵒᵖ ⥤ A where
  定义体: sheafToPresheaf _ _
  inverse :=
    { obj := fun P => ⟨P, Presheaf.isSheaf_bot P⟩
      map := fun f => ⟨f⟩ }
  unitIso := Iso.refl _
  counitIso := Iso.refl _

Depends on / 依赖: sheafToPresheaf
-/
def sheafBotEquivalence : Sheaf (⊥ : GrothendieckTopology C) A ≌ Cᵒᵖ ⥤ A where
  functor := sheafToPresheaf _ _
  inverse :=
    { obj := fun P => ⟨P, Presheaf.isSheaf_bot P⟩
      map := fun f => ⟨f⟩ }
  unitIso := Iso.refl _
  counitIso := Iso.refl _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Sheaf (⊥ : GrothendieckTopology C) (Type w))
  body: ⟨(sheafBotEquivalence _).inverse.obj ((Functor.const _).obj default)⟩

中文:
实例 :
  签名: 可居 (层 (⊥ : Grothendieck拓扑 C) (类型 w))
  定义体: ⟨(sheafBotEquivalence _).inverse.obj ((Functor.const _).obj default)⟩

Depends on / 依赖: Functor, Functor.const, inverse, inverse.obj, sheafBotEquivalence
-/
instance : Inhabited (Sheaf (⊥ : GrothendieckTopology C) (Type w)) :=
  ⟨(sheafBotEquivalence _).inverse.obj ((Functor.const _).obj default)⟩

variable {J} {A}

/--
Definition of `Sheaf.isTerminalOfBotCover` / `Sheaf.isTerminalOfBotCover` 的定义

English:
definition Sheaf.isTerminalOfBotCover
  signature: (F : Sheaf J A) (X : C) (H : ⊥ in J X)
  body: by
  refine @IsTerminal.ofUnique _ _ _ ?_
  intro Y
  choose t h using F.2 Y _ H (by tauto) (by tauto)
  exact ⟨⟨t⟩, fun a => h.2 a (by tauto)⟩

中文:
定义 层.isTerminalOfBotCover
  签名: (F : 层 J A) (X : C) (H : ⊥ in J X)
  定义体: by
  refine @IsTerminal.ofUnique _ _ _ ?_
  intro Y
  choose t h using F.2 Y _ H (by tauto) (by tauto)
  exact ⟨⟨t⟩, fun a => h.2 a (by tauto)⟩

Depends on / 依赖: IsTerminal, IsTerminal.ofUnique, ofUnique
-/
def Sheaf.isTerminalOfBotCover (F : Sheaf J A) (X : C) (H : ⊥ in J X) :
    IsTerminal (F.1.obj (op X)) := by
  refine @IsTerminal.ofUnique _ _ _ ?_
  intro Y
  choose t h using F.2 Y _ H (by tauto) (by tauto)
  exact ⟨⟨t⟩, fun a => h.2 a (by tauto)⟩

variable (J) in
/-- A terminal object in `A` gives rise to a terminal object in `Sheaf J` -/
@[simps]
/--
Definition of `Sheaf.terminal` / `Sheaf.terminal` 的定义

English:
definition Sheaf.terminal
  signature: {X : A} (hX : IsTerminal X)
  body: (CategoryTheory.Functor.const _).obj X
  property := Presheaf.isSheaf_of_isTerminal J hX

中文:
定义 层.terminal
  签名: {X : A} (hX : 是终止 X)
  定义体: (CategoryTheory.Functor.const _).obj X
  property := Presheaf.isSheaf_of_isTerminal J hX

Depends on / 依赖: CategoryTheory, CategoryTheory.Functor.const, Functor
-/
def Sheaf.terminal {X : A} (hX : IsTerminal X) : Sheaf J A where
  obj := (CategoryTheory.Functor.const _).obj X
  property := Presheaf.isSheaf_of_isTerminal J hX

variable (J) in
/--
Definition of `Sheaf.isTerminalTerminal` / `Sheaf.isTerminalTerminal` 的定义

English:
definition Sheaf.isTerminalTerminal
  signature: {X : A} (hX : IsTerminal X)
  body: .ofUniqueHom (⟨(Functor.isTerminalConst _ hX).from ·.obj⟩)
    (by intros; ext; simpa using! hX.hom_ext _ _)

@[simp]

中文:
定义 层.isTerminalTerminal
  签名: {X : A} (hX : 是终止 X)
  定义体: .ofUniqueHom (⟨(Functor.isTerminalConst _ hX).from ·.obj⟩)
    (by intros; ext; simpa using! hX.hom_ext _ _)

@[simp]

Depends on / 依赖: Functor, Functor.isTerminalConst, hX.hom_ext, hom_ext, intros, isTerminalConst, ofUniqueHom
-/
def Sheaf.isTerminalTerminal {X : A} (hX : IsTerminal X) : IsTerminal (Sheaf.terminal J hX) :=
  .ofUniqueHom (⟨(Functor.isTerminalConst _ hX).from ·.obj⟩)
    (by intros; ext; simpa using! hX.hom_ext _ _)

@[simp]
/--
lemma `Sheaf.isTerminalTerminal_from_hom` / 引理 `Sheaf.isTerminalTerminal_from_hom`

English:
lemma Sheaf.isTerminalTerminal_from_hom
  given: {X : A} (hX : IsTerminal X) (G : Sheaf J A)
  proof: rfl

中文:
引理 层.isTerminalTerminal_from_hom
  条件: {X : A} (hX : 是终止 X) (G : 层 J A)
  证明: rfl
-/
lemma Sheaf.isTerminalTerminal_from_hom {X : A} (hX : IsTerminal X) (G : Sheaf J A) :
    ((Sheaf.isTerminalTerminal J hX).from G).hom = (Functor.isTerminalConst _ hX).from G.obj := rfl

/--
Definition of `Sheaf.isTerminalOfEqTop` / `Sheaf.isTerminalOfEqTop` 的定义

English:
definition Sheaf.isTerminalOfEqTop
  signature: (H : J = ⊤) (F : Sheaf J A)
  body: by
  refine IsTerminal.isTerminalOfObj (sheafToPresheaf _ _) _ ?_
  refine Functor.isTerminal fun X => Sheaf.isTerminalOfBotCover _ _ ?_
  simp [H]

@[simp]

中文:
定义 层.isTerminalOfEqTop
  签名: (H : J = ⊤) (F : 层 J A)
  定义体: by
  refine IsTerminal.isTerminalOfObj (sheafToPresheaf _ _) _ ?_
  refine Functor.isTerminal fun X => Sheaf.isTerminalOfBotCover _ _ ?_
  simp [H]

@[simp]

Depends on / 依赖: Functor, Functor.isTerminal, IsTerminal, IsTerminal.isTerminalOfObj, Sheaf.isTerminalOfBotCover, isTerminal, isTerminalOfBotCover, isTerminalOfObj, sheafToPresheaf
-/
noncomputable def Sheaf.isTerminalOfEqTop (H : J = ⊤) (F : Sheaf J A) :
    IsTerminal F := by
  refine IsTerminal.isTerminalOfObj (sheafToPresheaf _ _) _ ?_
  refine Functor.isTerminal fun X => Sheaf.isTerminalOfBotCover _ _ ?_
  simp [H]

@[simp]
/--
theorem `Sheaf.Hom.add_app` / 定理 `Sheaf.Hom.add_app`

English:
theorem Sheaf.Hom.add_app
  given: [Preadditive A] {P Q : Sheaf J A} (f g : P ⟶ Q) (U : Cᵒᵖ)
  proof: rfl

中文:
定理 层.态射.add_app
  条件: [预加性 A] {P Q : 层 J A} (f g : P ⟶ Q) (U : Cᵒᵖ)
  证明: rfl
-/
theorem Sheaf.Hom.add_app [Preadditive A] {P Q : Sheaf J A} (f g : P ⟶ Q) (U : Cᵒᵖ) :
    (f + g).1.app U = f.1.app U + g.1.app U :=
  rfl

end CategoryTheory

namespace CategoryTheory

open Opposite CategoryTheory Category Limits Sieve

namespace Presheaf

-- Under here is the equalizer story, which is equivalent if A has products (and doesn't
-- make sense otherwise). It's described in https://stacks.math.columbia.edu/tag/00VL,
-- between 00VQ and 00VR.
variable {C : Type u₁} [Category.{v₁} C]

-- `A` is a general category; `A'` is a variant where the morphisms live in a large enough
-- universe to guarantee that we can take limits in A of things coming from C.
-- I would have liked to use something like `UnivLE.{max v₁ u₁, v₂}` as a hypothesis on
-- `A`'s morphism universe rather than introducing `A'` but I can't get it to work.
-- So, for now, results which need max v₁ u₁ ≤ v₂ are just stated for `A'` and `P' : Cᵒᵖ ⥤ A'`
-- instead.
variable {A : Type u₂} [Category.{v₂} A]
variable {A' : Type u₂} [Category.{max v₁ u₁} A']
variable {B : Type u₃} [Category.{v₃} B]
variable (J : GrothendieckTopology C)
variable {U : C} (R : Presieve U)
variable (P : Cᵒᵖ ⥤ A) (P' : Cᵒᵖ ⥤ A')

section MultiequalizerConditions

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `isLimitOfIsSheaf` / `isLimitOfIsSheaf` 的定义

English:
definition isLimitOfIsSheaf
  signature: {X : C} (S : J.Cover X) (hP : IsSheaf J P)
  body: fun E : Multifork _ => hP.amalgamate S (fun _ => E.ι _)
    (fun _ _ r => E.condition ⟨r⟩)
  fac := by
    rintro (E : Multifork _) (a | b)
    · apply hP.amalgamate_map
    · rw [← E.w (WalkingMulticospan.Hom.fst b),
        ← (S.multifork P).w (WalkingMulticospan.Hom.fst b), ← assoc]
      congr 1
      apply hP.amalgamate_map
  uniq := by
    rintro (E : Multifork _) m hm
    apply hP.hom_ext S
    intro I
    erw [hm (WalkingMulticospan.left I)]
    symm
    apply hP.amalgamate_map

中文:
定义 isLimitOfIsSheaf
  签名: {X : C} (S : J.Cover X) (hP : 是层 J P)
  定义体: fun E : Multifork _ => hP.amalgamate S (fun _ => E.ι _)
    (fun _ _ r => E.condition ⟨r⟩)
  fac := by
    rintro (E : Multifork _) (a | b)
    · apply hP.amalgamate_map
    · rw [← E.w (WalkingMulticospan.Hom.fst b),
        ← (S.multifork P).w (WalkingMulticospan.Hom.fst b), ← assoc]
      congr 1
      apply hP.amalgamate_map
  uniq := by
    rintro (E : Multifork _) m hm
    apply hP.hom_ext S
    intro I
    erw [hm (WalkingMulticospan.left I)]
    symm
    apply hP.amalgamate_map

Depends on / 依赖: Multifork, amalgamate, hP.amalgamate
-/
def isLimitOfIsSheaf {X : C} (S : J.Cover X) (hP : IsSheaf J P) : IsLimit (S.multifork P) where
  lift := fun E : Multifork _ => hP.amalgamate S (fun _ => E.ι _)
    (fun _ _ r => E.condition ⟨r⟩)
  fac := by
    rintro (E : Multifork _) (a | b)
    · apply hP.amalgamate_map
    · rw [← E.w (WalkingMulticospan.Hom.fst b),
        ← (S.multifork P).w (WalkingMulticospan.Hom.fst b), ← assoc]
      congr 1
      apply hP.amalgamate_map
  uniq := by
    rintro (E : Multifork _) m hm
    apply hP.hom_ext S
    intro I
    erw [hm (WalkingMulticospan.left I)]
    symm
    apply hP.amalgamate_map

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `isSheaf_iff_multifork` / 定理 `isSheaf_iff_multifork`

English:
theorem isSheaf_iff_multifork
  proof: by
  refine ⟨fun hP X S => ⟨isLimitOfIsSheaf _ _ _ hP⟩, ?_⟩
  intro h E X S hS x hx
  let T : J.Cover X := ⟨S, hS⟩
  obtain ⟨hh⟩ := h _ T
  let K : Multifork (T.index P) := Multifork.ofι _ E (fun I => x I.f I.hf)
    (fun I => hx _ _ _ _ I.r.w)
  use hh.lift K
  dsimp; constructor
  · intro Y f hf
    apply hh.fac K (WalkingMulticospan.left ⟨Y, f, hf⟩)
  · intro e he
    apply hh.uniq K
    rintro (a | b)
    · apply he
    · rw [← K.w (WalkingMulticospan.Hom.fst b), ←
        (T.multifork P).w (WalkingMulticospan.Hom.fst b), ← assoc]
      congr 1
      apply he

中文:
定理 isSheaf_iff_multifork
  证明: by
  refine ⟨fun hP X S => ⟨isLimitOfIsSheaf _ _ _ hP⟩, ?_⟩
  intro h E X S hS x hx
  let T : J.Cover X := ⟨S, hS⟩
  obtain ⟨hh⟩ := h _ T
  let K : Multifork (T.index P) := Multifork.ofι _ E (fun I => x I.f I.hf)
    (fun I => hx _ _ _ _ I.r.w)
  use hh.lift K
  dsimp; constructor
  · intro Y f hf
    apply hh.fac K (WalkingMulticospan.left ⟨Y, f, hf⟩)
  · intro e he
    apply hh.uniq K
    rintro (a | b)
    · apply he
    · rw [← K.w (WalkingMulticospan.Hom.fst b), ←
        (T.multifork P).w (WalkingMulticospan.Hom.fst b), ← assoc]
      congr 1
      apply he

Depends on / 依赖: I.hf, I.r.w, J.Cover, Multifork, Multifork.of, T.index, T.multifork, WalkingMulticospan, WalkingMulticospan.Hom.fst, WalkingMulticospan.left, hh.fac, hh.lift, hh.uniq, isLimitOfIsSheaf, multifork
-/
theorem isSheaf_iff_multifork :
    IsSheaf J P ↔ forall (X : C) (S : J.Cover X), Nonempty (IsLimit (S.multifork P)) := by
  refine ⟨fun hP X S => ⟨isLimitOfIsSheaf _ _ _ hP⟩, ?_⟩
  intro h E X S hS x hx
  let T : J.Cover X := ⟨S, hS⟩
  obtain ⟨hh⟩ := h _ T
  let K : Multifork (T.index P) := Multifork.ofι _ E (fun I => x I.f I.hf)
    (fun I => hx _ _ _ _ I.r.w)
  use hh.lift K
  dsimp; constructor
  · intro Y f hf
    apply hh.fac K (WalkingMulticospan.left ⟨Y, f, hf⟩)
  · intro e he
    apply hh.uniq K
    rintro (a | b)
    · apply he
    · rw [← K.w (WalkingMulticospan.Hom.fst b), ←
        (T.multifork P).w (WalkingMulticospan.Hom.fst b), ← assoc]
      congr 1
      apply he

variable {J P} in
/--
Definition of `IsSheaf.isLimitMultifork` / `IsSheaf.isLimitMultifork` 的定义

English:
definition IsSheaf.isLimitMultifork
  body: by
  rw [Presheaf.isSheaf_iff_multifork] at hP
  exact (hP X S).some

中文:
定义 是层.isLimitMultifork
  定义体: by
  rw [Presheaf.isSheaf_iff_multifork] at hP
  exact (hP X S).some

Depends on / 依赖: Presheaf, Presheaf.isSheaf_iff_multifork, isSheaf_iff_multifork
-/
def IsSheaf.isLimitMultifork
    (hP : Presheaf.IsSheaf J P) {X : C} (S : J.Cover X) : IsLimit (S.multifork P) := by
  rw [Presheaf.isSheaf_iff_multifork] at hP
  exact (hP X S).some

set_option backward.isDefEq.respectTransparency false in
/--
theorem `isSheaf_iff_multiequalizer` / 定理 `isSheaf_iff_multiequalizer`

English:
theorem isSheaf_iff_multiequalizer
  given: [forall (X : C) (S : J.Cover X), HasMultiequalizer (S.index P)]
  proof: by
  rw [isSheaf_iff_multifork]
  refine forall₂_congr fun X S => ⟨?_, ?_⟩
  · rintro ⟨h⟩
    let e : P.obj (op X) ≅ multiequalizer (S.index P) :=
      h.conePointUniqueUpToIso (limit.isLimit _)
    exact (inferInstance : IsIso e.hom)
  · intro h
    refine ⟨IsLimit.ofIsoLimit (limit.isLimit _) (Cone.ext ?_ ?_)⟩
    · apply (@asIso _ _ _ _ _ h).symm
    · intro a
      symm
      simp

中文:
定理 isSheaf_iff_multiequalizer
  条件: [对任意 (X : C) (S : J.Cover X), HasMultiequalizer (S.index P)]
  证明: by
  rw [isSheaf_iff_multifork]
  refine forall₂_congr fun X S => ⟨?_, ?_⟩
  · rintro ⟨h⟩
    let e : P.obj (op X) ≅ multiequalizer (S.index P) :=
      h.conePointUniqueUpToIso (limit.isLimit _)
    exact (inferInstance : IsIso e.hom)
  · intro h
    refine ⟨IsLimit.ofIsoLimit (limit.isLimit _) (Cone.ext ?_ ?_)⟩
    · apply (@asIso _ _ _ _ _ h).symm
    · intro a
      symm
      simp

Depends on / 依赖: Cone.ext, IsLimit, IsLimit.ofIsoLimit, P.obj, S.index, conePointUniqueUpToIso, e.hom, h.conePointUniqueUpToIso, isLimit, isSheaf_iff_multifork, limit.isLimit, multiequalizer, ofIsoLimit
-/
theorem isSheaf_iff_multiequalizer [forall (X : C) (S : J.Cover X), HasMultiequalizer (S.index P)] :
    IsSheaf J P ↔ forall (X : C) (S : J.Cover X), IsIso (S.toMultiequalizer P) := by
  rw [isSheaf_iff_multifork]
  refine forall₂_congr fun X S => ⟨?_, ?_⟩
  · rintro ⟨h⟩
    let e : P.obj (op X) ≅ multiequalizer (S.index P) :=
      h.conePointUniqueUpToIso (limit.isLimit _)
    exact (inferInstance : IsIso e.hom)
  · intro h
    refine ⟨IsLimit.ofIsoLimit (limit.isLimit _) (Cone.ext ?_ ?_)⟩
    · apply (@asIso _ _ _ _ _ h).symm
    · intro a
      symm
      simp

end MultiequalizerConditions

section

variable [HasProducts.{max u₁ v₁} A]
variable [HasProducts.{max u₁ v₁} A']

/-- The middle object of the fork diagram given in Equation (3) of [MM92], as well as the fork
diagram of the Stacks entry. -/
@[stacks 00VM "The middle object of the fork diagram there."]
/--
Definition of `firstObj` / `firstObj` 的定义

English:
definition firstObj
  signature: : A
  body: ∏ᶜ fun f : Σ V, { f : V ⟶ U // R f } => P.obj (op f.1)

中文:
定义 firstObj
  签名: : A
  定义体: ∏ᶜ fun f : Σ V, { f : V ⟶ U // R f } => P.obj (op f.1)

Depends on / 依赖: P.obj
-/
def firstObj : A :=
  ∏ᶜ fun f : Σ V, { f : V ⟶ U // R f } => P.obj (op f.1)

/-- The left morphism of the fork diagram given in Equation (3) of [MM92], as well as the fork
diagram of the Stacks entry. -/
@[stacks 00VM "The left morphism the fork diagram there."]
/--
Definition of `forkMap` / `forkMap` 的定义

English:
definition forkMap
  signature: : P.obj (op U) ⟶ firstObj R P
  body: Pi.lift fun f => P.map f.2.1.op

中文:
定义 forkMap
  签名: : P.obj (op U) ⟶ firstObj R P
  定义体: Pi.lift fun f => P.map f.2.1.op

Depends on / 依赖: P.map, Pi.lift
-/
def forkMap : P.obj (op U) ⟶ firstObj R P :=
  Pi.lift fun f => P.map f.2.1.op

variable [HasPullbacks C]

/-- The rightmost object of the fork diagram of the Stacks entry, which
contains the data used to check a family of elements for a presieve is compatible.
-/
@[stacks 00VM "The rightmost object of the fork diagram there."]
/--
Definition of `secondObj` / `secondObj` 的定义

English:
definition secondObj
  signature: : A
  body: ∏ᶜ fun fg : (Σ V, { f : V ⟶ U // R f }) × Σ W, { g : W ⟶ U // R g } =>
    P.obj (op (pullback fg.1.2.1 fg.2.2.1))

中文:
定义 secondObj
  签名: : A
  定义体: ∏ᶜ fun fg : (Σ V, { f : V ⟶ U // R f }) × Σ W, { g : W ⟶ U // R g } =>
    P.obj (op (pullback fg.1.2.1 fg.2.2.1))

Depends on / 依赖: P.obj, pullback
-/
def secondObj : A :=
  ∏ᶜ fun fg : (Σ V, { f : V ⟶ U // R f }) × Σ W, { g : W ⟶ U // R g } =>
    P.obj (op (pullback fg.1.2.1 fg.2.2.1))

/-- The map `pr₀*` of the Stacks entry. -/
@[stacks 00VM "The map `pr₀*` there."]
/--
Definition of `firstMap` / `firstMap` 的定义

English:
definition firstMap
  signature: : firstObj R P ⟶ secondObj R P
  body: Pi.lift fun _ => Pi.π _ _ ≫ P.map (pullback.fst _ _).op

中文:
定义 firstMap
  签名: : firstObj R P ⟶ secondObj R P
  定义体: Pi.lift fun _ => Pi.π _ _ ≫ P.map (pullback.fst _ _).op

Depends on / 依赖: P.map, Pi.lift, pullback, pullback.fst
-/
def firstMap : firstObj R P ⟶ secondObj R P :=
  Pi.lift fun _ => Pi.π _ _ ≫ P.map (pullback.fst _ _).op

/-- The map `pr₁*` of the Stacks entry. -/
@[stacks 00VM "The map `pr₁*` there."]
/--
Definition of `secondMap` / `secondMap` 的定义

English:
definition secondMap
  signature: : firstObj R P ⟶ secondObj R P
  body: Pi.lift fun _ => Pi.π _ _ ≫ P.map (pullback.snd _ _).op

中文:
定义 secondMap
  签名: : firstObj R P ⟶ secondObj R P
  定义体: Pi.lift fun _ => Pi.π _ _ ≫ P.map (pullback.snd _ _).op

Depends on / 依赖: P.map, Pi.lift, pullback, pullback.snd
-/
def secondMap : firstObj R P ⟶ secondObj R P :=
  Pi.lift fun _ => Pi.π _ _ ≫ P.map (pullback.snd _ _).op

set_option backward.isDefEq.respectTransparency false in
/--
theorem `w` / 定理 `w`

English:
theorem w
  statement: forkMap R P ≫ firstMap R P = forkMap R P ≫ secondMap R P
  proof: by
  apply limit.hom_ext
  rintro ⟨⟨Y, f, hf⟩, ⟨Z, g, hg⟩⟩
  simp only [firstMap, secondMap, forkMap, limit.lift_π, limit.lift_π_assoc, assoc, Fan.mk_π_app,
    Subtype.coe_mk]
  rw [← P.map_comp]; rw [← op_comp]; rw [pullback.condition]
  simp

中文:
定理 w
  结论: forkMap R P ≫ firstMap R P = forkMap R P ≫ secondMap R P
  证明: by
  apply limit.hom_ext
  rintro ⟨⟨Y, f, hf⟩, ⟨Z, g, hg⟩⟩
  simp only [firstMap, secondMap, forkMap, limit.lift_π, limit.lift_π_assoc, assoc, Fan.mk_π_app,
    Subtype.coe_mk]
  rw [← P.map_comp]; rw [← op_comp]; rw [pullback.condition]
  simp

Depends on / 依赖: Fan.mk_, P.map_comp, Subtype, Subtype.coe_mk, coe_mk, condition, firstMap, forkMap, hom_ext, limit.hom_ext, limit.lift_, map_comp, op_comp, pullback, pullback.condition, secondMap
-/
theorem w : forkMap R P ≫ firstMap R P = forkMap R P ≫ secondMap R P := by
  apply limit.hom_ext
  rintro ⟨⟨Y, f, hf⟩, ⟨Z, g, hg⟩⟩
  simp only [firstMap, secondMap, forkMap, limit.lift_π, limit.lift_π_assoc, assoc, Fan.mk_π_app,
    Subtype.coe_mk]
  rw [← P.map_comp]; rw [← op_comp]; rw [pullback.condition]
  simp

/--
Definition of `IsSheaf'` / `IsSheaf'` 的定义

English:
definition IsSheaf'
  signature: (P : Cᵒᵖ ⥤ A)
  body: forall (U : C) (R : Presieve U) (_ : generate R in J U), Nonempty (IsLimit (Fork.ofι _ (w R P)))

中文:
定义 是层'
  签名: (P : Cᵒᵖ ⥤ A)
  定义体: forall (U : C) (R : Presieve U) (_ : generate R in J U), Nonempty (IsLimit (Fork.ofι _ (w R P)))

Depends on / 依赖: Fork.of, IsLimit, Nonempty, Presieve, generate
-/
def IsSheaf' (P : Cᵒᵖ ⥤ A) : Prop :=
  forall (U : C) (R : Presieve U) (_ : generate R in J U), Nonempty (IsLimit (Fork.ofι _ (w R P)))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
-- Again I wonder whether `UnivLE` can somehow be used to allow `s` to take
-- values in a more general universe.
/--
Definition of `isSheafForIsSheafFor'` / `isSheafForIsSheafFor'` 的定义

English:
definition isSheafForIsSheafFor'
  signature: (P : Cᵒᵖ ⥤ A) (s : A ⥤ Type (max v₁ u₁))
  body: by
  let e : parallelPair (s.map (firstMap R P)) (s.map (secondMap R P)) ≅
    parallelPair (Equalizer.Presieve.firstMap (P ⋙ s) R)
      (Equalizer.Presieve.secondMap (P ⋙ s) R) := by
    refine parallelPair.ext (PreservesProduct.iso s _) ((PreservesProduct.iso s _))
      (limit.hom_ext (fun j => ?_)) (limit.hom_ext (fun j => ?_))
    · dsimp [Equalizer.Presieve.firstMap, firstMap]
      simp only [map_lift_piComparison, Functor.map_comp, limit.lift_π, Fan.mk_pt,
        Fan.mk_π_app, assoc, piComparison_comp_π_assoc]
    · dsimp [Equalizer.Presieve.secondMap, secondMap]
      simp only [map_lift_piComparison, Functor.map_comp, limit.lift_π, Fan.mk_pt,
        Fan.mk_π_app, assoc, piComparison_comp_π_assoc]
  refine Equiv.trans (isLimitMapConeForkEquiv _ _) ?_
  refine (IsLimit.postcomposeHomEquiv e _).symm.trans
    (IsLimit.equivIsoLimit (Fork.ext (Iso.refl _) ?_))
  dsimp [Equalizer.forkMap, forkMap, e, Fork.ι]
  simp only [id_comp, map_lift_piComparison]

中文:
定义 isSheafForIsSheafFor'
  签名: (P : Cᵒᵖ ⥤ A) (s : A ⥤ 类型 (最大值 v₁ u₁))
  定义体: by
  let e : parallelPair (s.map (firstMap R P)) (s.map (secondMap R P)) ≅
    parallelPair (Equalizer.Presieve.firstMap (P ⋙ s) R)
      (Equalizer.Presieve.secondMap (P ⋙ s) R) := by
    refine parallelPair.ext (PreservesProduct.iso s _) ((PreservesProduct.iso s _))
      (limit.hom_ext (fun j => ?_)) (limit.hom_ext (fun j => ?_))
    · dsimp [Equalizer.Presieve.firstMap, firstMap]
      simp only [map_lift_piComparison, Functor.map_comp, limit.lift_π, Fan.mk_pt,
        Fan.mk_π_app, assoc, piComparison_comp_π_assoc]
    · dsimp [Equalizer.Presieve.secondMap, secondMap]
      simp only [map_lift_piComparison, Functor.map_comp, limit.lift_π, Fan.mk_pt,
        Fan.mk_π_app, assoc, piComparison_comp_π_assoc]
  refine Equiv.trans (isLimitMapConeForkEquiv _ _) ?_
  refine (IsLimit.postcomposeHomEquiv e _).symm.trans
    (IsLimit.equivIsoLimit (Fork.ext (Iso.refl _) ?_))
  dsimp [Equalizer.forkMap, forkMap, e, Fork.ι]
  simp only [id_comp, map_lift_piComparison]

Depends on / 依赖: Equalizer, Equalizer.Presieve.firstMap, Equalizer.Presieve.secondMap, Fan.mk_, Fan.mk_pt, Functor, Functor.map_comp, PreservesProduct, PreservesProduct.iso, Presieve, firstMap, hom_ext, limit.hom_ext, limit.lift_, map_comp, map_lift_piComparison, mk_pt, parallelPair, parallelPair.ext, s.map
-/
def isSheafForIsSheafFor' (P : Cᵒᵖ ⥤ A) (s : A ⥤ Type (max v₁ u₁))
    [forall J, PreservesLimitsOfShape (Discrete.{max v₁ u₁} J) s] (U : C) (R : Presieve U) :
    IsLimit (s.mapCone (Fork.ofι _ (w R P))) ≃
      IsLimit (Fork.ofι _ (Equalizer.Presieve.w (P ⋙ s) R)) := by
  let e : parallelPair (s.map (firstMap R P)) (s.map (secondMap R P)) ≅
    parallelPair (Equalizer.Presieve.firstMap (P ⋙ s) R)
      (Equalizer.Presieve.secondMap (P ⋙ s) R) := by
    refine parallelPair.ext (PreservesProduct.iso s _) ((PreservesProduct.iso s _))
      (limit.hom_ext (fun j => ?_)) (limit.hom_ext (fun j => ?_))
    · dsimp [Equalizer.Presieve.firstMap, firstMap]
      simp only [map_lift_piComparison, Functor.map_comp, limit.lift_π, Fan.mk_pt,
        Fan.mk_π_app, assoc, piComparison_comp_π_assoc]
    · dsimp [Equalizer.Presieve.secondMap, secondMap]
      simp only [map_lift_piComparison, Functor.map_comp, limit.lift_π, Fan.mk_pt,
        Fan.mk_π_app, assoc, piComparison_comp_π_assoc]
  refine Equiv.trans (isLimitMapConeForkEquiv _ _) ?_
  refine (IsLimit.postcomposeHomEquiv e _).symm.trans
    (IsLimit.equivIsoLimit (Fork.ext (Iso.refl _) ?_))
  dsimp [Equalizer.forkMap, forkMap, e, Fork.ι]
  simp only [id_comp, map_lift_piComparison]

-- Remark : this lemma uses `A'` not `A`; `A'` is `A` but with a universe
-- restriction. Can it be generalised?
/--
theorem `isSheaf_iff_isSheaf'` / 定理 `isSheaf_iff_isSheaf'`

English:
theorem isSheaf_iff_isSheaf'
  statement: IsSheaf J P' ↔ IsSheaf' J P'
  proof: by
  constructor
  · intro h U R hR
    refine ⟨?_⟩
    apply coyonedaJointlyReflectsLimits
    intro X
    have q : Presieve.IsSheafFor (P' ⋙ coyoneda.obj X) _ := h X.unop _ hR
    rw [← Presieve.isSheafFor_iff_generate] at q
    rw [Equalizer.Presieve.sheaf_condition] at q
    replace q := Classical.choice q
    apply (isSheafForIsSheafFor' _ _ _ _).symm q
  · intro h U X S hS
    rw [Equalizer.Presieve.sheaf_condition]
    refine ⟨?_⟩
    refine isSheafForIsSheafFor' _ _ _ _ ?_
    letI := preservesSmallestLimits_of_preservesLimits (coyoneda.obj (op U))
    apply isLimitOfPreserves
    apply Classical.choice (h _ S.arrows _)
    simpa

中文:
定理 isSheaf_iff_isSheaf'
  结论: 是层 J P' ↔ 是层' J P'
  证明: by
  constructor
  · intro h U R hR
    refine ⟨?_⟩
    apply coyonedaJointlyReflectsLimits
    intro X
    have q : Presieve.IsSheafFor (P' ⋙ coyoneda.obj X) _ := h X.unop _ hR
    rw [← Presieve.isSheafFor_iff_generate] at q
    rw [Equalizer.Presieve.sheaf_condition] at q
    replace q := Classical.choice q
    apply (isSheafForIsSheafFor' _ _ _ _).symm q
  · intro h U X S hS
    rw [Equalizer.Presieve.sheaf_condition]
    refine ⟨?_⟩
    refine isSheafForIsSheafFor' _ _ _ _ ?_
    letI := preservesSmallestLimits_of_preservesLimits (coyoneda.obj (op U))
    apply isLimitOfPreserves
    apply Classical.choice (h _ S.arrows _)
    simpa

Depends on / 依赖: Classical, Classical.choice, Equalizer, Equalizer.Presieve.sheaf_condition, IsSheafFor, Presieve, Presieve.IsSheafFor, Presieve.isSheafFor_iff_generate, X.unop, choice, coyoneda, coyoneda.obj, coyonedaJointlyReflectsLimits, isSheafForIsSheafFor, isSheafFor_iff_generate, preservesSmallestLimits_of_preservesLimits, replace, sheaf_condition
-/
theorem isSheaf_iff_isSheaf' : IsSheaf J P' ↔ IsSheaf' J P' := by
  constructor
  · intro h U R hR
    refine ⟨?_⟩
    apply coyonedaJointlyReflectsLimits
    intro X
    have q : Presieve.IsSheafFor (P' ⋙ coyoneda.obj X) _ := h X.unop _ hR
    rw [← Presieve.isSheafFor_iff_generate] at q
    rw [Equalizer.Presieve.sheaf_condition] at q
    replace q := Classical.choice q
    apply (isSheafForIsSheafFor' _ _ _ _).symm q
  · intro h U X S hS
    rw [Equalizer.Presieve.sheaf_condition]
    refine ⟨?_⟩
    refine isSheafForIsSheafFor' _ _ _ _ ?_
    letI := preservesSmallestLimits_of_preservesLimits (coyoneda.obj (op U))
    apply isLimitOfPreserves
    apply Classical.choice (h _ S.arrows _)
    simpa

end

section Concrete

/--
theorem `isSheaf_of_isSheaf_comp` / 定理 `isSheaf_of_isSheaf_comp`

English:
theorem isSheaf_of_isSheaf_comp
  statement: (s : A ⥤ B) [ReflectsLimitsOfSize.{v₁, max v₁ u₁} s]
  proof: by
  rw [isSheaf_iff_isLimit] at h ⊢
  exact fun X S hS => (h S hS).map fun t => isLimitOfReflects s t

中文:
定理 isSheaf_of_isSheaf_comp
  结论: (s : A ⥤ B) [ReflectsLimitsOfSize.{v₁, 最大值 v₁ u₁} s]
  证明: by
  rw [isSheaf_iff_isLimit] at h ⊢
  exact fun X S hS => (h S hS).map fun t => isLimitOfReflects s t

Depends on / 依赖: isLimitOfReflects, isSheaf_iff_isLimit
-/
theorem isSheaf_of_isSheaf_comp (s : A ⥤ B) [ReflectsLimitsOfSize.{v₁, max v₁ u₁} s]
    (h : IsSheaf J (P ⋙ s)) : IsSheaf J P := by
  rw [isSheaf_iff_isLimit] at h ⊢
  exact fun X S hS => (h S hS).map fun t => isLimitOfReflects s t

/--
theorem `isSheaf_comp_of_isSheaf` / 定理 `isSheaf_comp_of_isSheaf`

English:
theorem isSheaf_comp_of_isSheaf
  statement: (s : A ⥤ B) [PreservesLimitsOfSize.{v₁, max v₁ u₁} s]
  proof: by
  rw [isSheaf_iff_isLimit] at h ⊢
  apply fun X S hS => (h S hS).map fun t => isLimitOfPreserves s t

中文:
定理 isSheaf_comp_of_isSheaf
  结论: (s : A ⥤ B) [保持LimitsOfSize.{v₁, 最大值 v₁ u₁} s]
  证明: by
  rw [isSheaf_iff_isLimit] at h ⊢
  apply fun X S hS => (h S hS).map fun t => isLimitOfPreserves s t

Depends on / 依赖: isLimitOfPreserves, isSheaf_iff_isLimit
-/
theorem isSheaf_comp_of_isSheaf (s : A ⥤ B) [PreservesLimitsOfSize.{v₁, max v₁ u₁} s]
    (h : IsSheaf J P) : IsSheaf J (P ⋙ s) := by
  rw [isSheaf_iff_isLimit] at h ⊢
  apply fun X S hS => (h S hS).map fun t => isLimitOfPreserves s t

/--
theorem `isSheaf_iff_isSheaf_comp` / 定理 `isSheaf_iff_isSheaf_comp`

English:
theorem isSheaf_iff_isSheaf_comp
  statement: (s : A ⥤ B) [HasLimitsOfSize.{v₁, max v₁ u₁} A]
  proof: by
  let : ReflectsLimitsOfSize s := reflectsLimits_of_reflectsIsomorphisms
  exact ⟨isSheaf_comp_of_isSheaf J P s, isSheaf_of_isSheaf_comp J P s⟩

中文:
定理 isSheaf_iff_isSheaf_comp
  结论: (s : A ⥤ B) [有LimitsOfSize.{v₁, 最大值 v₁ u₁} A]
  证明: by
  let : ReflectsLimitsOfSize s := reflectsLimits_of_reflectsIsomorphisms
  exact ⟨isSheaf_comp_of_isSheaf J P s, isSheaf_of_isSheaf_comp J P s⟩

Depends on / 依赖: ReflectsLimitsOfSize, isSheaf_comp_of_isSheaf, isSheaf_of_isSheaf_comp, reflectsLimits_of_reflectsIsomorphisms
-/
theorem isSheaf_iff_isSheaf_comp (s : A ⥤ B) [HasLimitsOfSize.{v₁, max v₁ u₁} A]
    [PreservesLimitsOfSize.{v₁, max v₁ u₁} s] [s.ReflectsIsomorphisms] :
    IsSheaf J P ↔ IsSheaf J (P ⋙ s) := by
  let : ReflectsLimitsOfSize s := reflectsLimits_of_reflectsIsomorphisms
  exact ⟨isSheaf_comp_of_isSheaf J P s, isSheaf_of_isSheaf_comp J P s⟩

/--
theorem `isSheaf_iff_isSheaf_forget` / 定理 `isSheaf_iff_isSheaf_forget`

English:
theorem isSheaf_iff_isSheaf_forget
  statement: (s : A' ⥤ Type (max v₁ u₁)) [HasLimits A'] [PreservesLimits s]
  proof: by
  have : HasLimitsOfSize.{v₁, max v₁ u₁} A' := hasLimitsOfSizeShrink.{_, _, u₁, 0} A'
  have : PreservesLimitsOfSize.{v₁, max v₁ u₁} s := preservesLimitsOfSize_shrink.{_, 0, _, u₁} s
  apply isSheaf_iff_isSheaf_comp

中文:
定理 isSheaf_iff_isSheaf_forget
  结论: (s : A' ⥤ 类型 (最大值 v₁ u₁)) [有极限 A'] [PreservesLimits s]
  证明: by
  have : HasLimitsOfSize.{v₁, max v₁ u₁} A' := hasLimitsOfSizeShrink.{_, _, u₁, 0} A'
  have : PreservesLimitsOfSize.{v₁, max v₁ u₁} s := preservesLimitsOfSize_shrink.{_, 0, _, u₁} s
  apply isSheaf_iff_isSheaf_comp

Depends on / 依赖: HasLimitsOfSize, PreservesLimitsOfSize, hasLimitsOfSizeShrink, isSheaf_iff_isSheaf_comp, preservesLimitsOfSize_shrink
-/
theorem isSheaf_iff_isSheaf_forget (s : A' ⥤ Type (max v₁ u₁)) [HasLimits A'] [PreservesLimits s]
    [s.ReflectsIsomorphisms] : IsSheaf J P' ↔ IsSheaf J (P' ⋙ s) := by
  have : HasLimitsOfSize.{v₁, max v₁ u₁} A' := hasLimitsOfSizeShrink.{_, _, u₁, 0} A'
  have : PreservesLimitsOfSize.{v₁, max v₁ u₁} s := preservesLimitsOfSize_shrink.{_, 0, _, u₁} s
  apply isSheaf_iff_isSheaf_comp

end Concrete

end Presheaf

end CategoryTheory
