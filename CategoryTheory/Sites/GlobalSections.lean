/-
Copyright (c) 2025 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf

/-!
# Global sections of sheaves

In this file we define a global sections functor `Sheaf.Γ : Sheaf J A ⥤ A` and show that it
is isomorphic to several other constructions when they exist, most notably evaluation of sheaves
on a terminal object and `Functor.sectionsFunctor`.

## Main definitions / results

* `HasGlobalSectionsFunctor J A`: typeclass stating that the constant sheaf functor `A ⥤ Sheaf J A`
  has a right-adjoint.
* `Sheaf.Γ J A`: the global sections functor `Sheaf J A ⥤ A`, defined as the right-adjoint of the
  constant sheaf functor, whenever that exists.
* `constantSheafΓAdj J A`: the adjunction between the constant sheaf functor and `Sheaf.Γ J A`.
* `Sheaf.ΓNatIsoSheafSections J A hT`: on sites with a terminal object `T`, `Sheaf.Γ J A` exists and
  is isomorphic to the functor evaluating sheaves at `T`.
* `Sheaf.ΓNatIsoLim J A`: when `A` has limits of shape `Cᵒᵖ`, `Sheaf.Γ J A` exists and is isomorphic
  to the functor taking each sheaf to the limit of its underlying presheaf.
* `Sheaf.isLimitConeΓ F`: global sections are limits even when not all limits of shape `Cᵒᵖ` exist.
* `Sheaf.ΓRes F U`: the restriction morphism from global sections of `F` to sections of `F` on `U`.
* `Sheaf.natTransΓRes J A U`: the natural transformation from the global sections functor to
  the sections functor on `U`.
* `Sheaf.ΓNatIsoSectionsFunctor J`: for sheaves of types, `Sheaf.Γ J A` is isomorphic to the
  functor taking each sheaf to the type of sections of its underlying presheaf in the sense of
  `Functor.sections`.
* `Sheaf.ΓNatIsoCoyoneda J`: for sheaves of types, `Sheaf.Γ J A` is isomorphic to the
  coyoneda embedding of the terminal sheaf, i.e. the functor sending each sheaf `F` to the type
  of morphisms from the terminal sheaf to `F`.

## TODO

* Generalise `Sheaf.ΓNatIsoSectionsFunctor` and `Sheaf.ΓNatIsoCoyoneda` from `Type max u v` to
  `Type max u v w`. This should hopefully be doable by relaxing the universe constraints of
  `instHasSheafifyOfHasFiniteLimits`.

-/

@[expose] public section

universe u v w u₂ v₂

open CategoryTheory Limits Sheaf Opposite GrothendieckTopology

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (A : Type u₂) [Category.{v₂} A] [HasWeakSheafify J A]

/--
Definition of `HasGlobalSectionsFunctor` / `HasGlobalSectionsFunctor` 的定义

English:
abbreviation HasGlobalSectionsFunctor
  body: (constantSheaf J A).IsLeftAdjoint

中文:
缩写 HasGlobalSectionsFunctor
  定义体: (constantSheaf J A).IsLeftAdjoint

Depends on / 依赖: IsLeftAdjoint, constantSheaf
-/
abbrev HasGlobalSectionsFunctor := (constantSheaf J A).IsLeftAdjoint

/--
Definition of `Sheaf.Γ` / `Sheaf.Γ` 的定义

English:
definition Sheaf.Γ
  signature: [HasGlobalSectionsFunctor J A]
  body: (constantSheaf J A).rightAdjoint
deriving Functor.IsRightAdjoint

中文:
定义 层.Γ
  签名: [HasGlobalSectionsFunctor J A]
  定义体: (constantSheaf J A).rightAdjoint
deriving Functor.IsRightAdjoint

Depends on / 依赖: constantSheaf, rightAdjoint
-/
noncomputable def Sheaf.Γ [HasGlobalSectionsFunctor J A] : Sheaf J A ⥤ A :=
  (constantSheaf J A).rightAdjoint
deriving Functor.IsRightAdjoint

/--
Definition of `constantSheafΓAdj` / `constantSheafΓAdj` 的定义

English:
definition constantSheafΓAdj
  signature: [HasGlobalSectionsFunctor J A]
  body: Adjunction.ofIsLeftAdjoint (constantSheaf J A)

中文:
定义 constantSheafΓAdj
  签名: [HasGlobalSectionsFunctor J A]
  定义体: Adjunction.ofIsLeftAdjoint (constantSheaf J A)

Depends on / 依赖: Adjunction, Adjunction.ofIsLeftAdjoint, constantSheaf, ofIsLeftAdjoint
-/
noncomputable def constantSheafΓAdj [HasGlobalSectionsFunctor J A] :
    constantSheaf J A ⊣ Γ J A :=
  Adjunction.ofIsLeftAdjoint (constantSheaf J A)

/--
Instance `hasGlobalSectionsFunctor_of_hasTerminal` / 实例 `hasGlobalSectionsFunctor_of_hasTerminal`

English:
instance hasGlobalSectionsFunctor_of_hasTerminal
  signature: [HasTerminal C]
  body: ⟨_, ⟨constantSheafAdj J A terminalIsTerminal⟩⟩

中文:
实例 hasGlobalSectionsFunctor_of_hasTerminal
  签名: [有终止 C]
  定义体: ⟨_, ⟨constantSheafAdj J A terminalIsTerminal⟩⟩

Depends on / 依赖: constantSheafAdj, terminalIsTerminal
-/
instance hasGlobalSectionsFunctor_of_hasTerminal [HasTerminal C] :
    HasGlobalSectionsFunctor J A :=
  ⟨_, ⟨constantSheafAdj J A terminalIsTerminal⟩⟩

/--
Definition of `Sheaf.ΓNatIsoSheafSections` / `Sheaf.ΓNatIsoSheafSections` 的定义

English:
definition Sheaf.ΓNatIsoSheafSections
  signature: [HasTerminal C] {T : C} (hT : IsTerminal T)
  body: (constantSheafΓAdj J A).rightAdjointUniq (constantSheafAdj J A hT)

中文:
定义 层.Γ自然数IsoSheafSections
  签名: [有终止 C] {T : C} (hT : 是终止 T)
  定义体: (constantSheafΓAdj J A).rightAdjointUniq (constantSheafAdj J A hT)

Depends on / 依赖: constantSheafAdj, rightAdjointUniq
-/
noncomputable def Sheaf.ΓNatIsoSheafSections [HasTerminal C] {T : C} (hT : IsTerminal T) :
    Γ J A ≅ (sheafSections J A).obj (op T) :=
  (constantSheafΓAdj J A).rightAdjointUniq (constantSheafAdj J A hT)

/--
Instance `hasGlobalSectionsFunctor_of_hasLimitsOfShape` / 实例 `hasGlobalSectionsFunctor_of_hasLimitsOfShape`

English:
instance hasGlobalSectionsFunctor_of_hasLimitsOfShape
  signature: [HasLimitsOfShape Cᵒᵖ A]
  body: ⟨sheafToPresheaf J A ⋙ lim, ⟨constLimAdj.comp (sheafificationAdjunction J A)⟩⟩

中文:
实例 hasGlobalSectionsFunctor_of_hasLimitsOfShape
  签名: [有形状极限 Cᵒᵖ A]
  定义体: ⟨sheafToPresheaf J A ⋙ lim, ⟨constLimAdj.comp (sheafificationAdjunction J A)⟩⟩

Depends on / 依赖: constLimAdj, constLimAdj.comp, sheafToPresheaf, sheafificationAdjunction
-/
instance hasGlobalSectionsFunctor_of_hasLimitsOfShape [HasLimitsOfShape Cᵒᵖ A] :
    HasGlobalSectionsFunctor J A :=
  ⟨sheafToPresheaf J A ⋙ lim, ⟨constLimAdj.comp (sheafificationAdjunction J A)⟩⟩

/--
Definition of `Sheaf.ΓNatIsoLim` / `Sheaf.ΓNatIsoLim` 的定义

English:
definition Sheaf.ΓNatIsoLim
  signature: [HasLimitsOfShape Cᵒᵖ A]
  body: (constantSheafΓAdj J A).rightAdjointUniq (constLimAdj.comp (sheafificationAdjunction J A))

中文:
定义 层.Γ自然数IsoLim
  签名: [有形状极限 Cᵒᵖ A]
  定义体: (constantSheafΓAdj J A).rightAdjointUniq (constLimAdj.comp (sheafificationAdjunction J A))

Depends on / 依赖: constLimAdj, constLimAdj.comp, rightAdjointUniq, sheafificationAdjunction
-/
noncomputable def Sheaf.ΓNatIsoLim [HasLimitsOfShape Cᵒᵖ A] :
    Γ J A ≅ sheafToPresheaf J A ⋙ lim :=
  (constantSheafΓAdj J A).rightAdjointUniq (constLimAdj.comp (sheafificationAdjunction J A))

variable {J A}

/--
Definition of `Sheaf.ΓHomEquiv` / `Sheaf.ΓHomEquiv` 的定义

English:
definition Sheaf.ΓHomEquiv
  signature: [HasGlobalSectionsFunctor J A] {X : A} {F : Sheaf J A}
  body: ((sheafificationAdjunction J A).homEquiv _ _).symm.trans
    ((constantSheafΓAdj J A).homEquiv _ _)

中文:
定义 层.ΓHomEquiv
  签名: [HasGlobalSectionsFunctor J A] {X : A} {F : 层 J A}
  定义体: ((sheafificationAdjunction J A).homEquiv _ _).symm.trans
    ((constantSheafΓAdj J A).homEquiv _ _)

Depends on / 依赖: homEquiv, sheafificationAdjunction, symm.trans
-/
noncomputable def Sheaf.ΓHomEquiv [HasGlobalSectionsFunctor J A] {X : A} {F : Sheaf J A} :
    ((Functor.const _).obj X ⟶ F.obj) ≃ (X ⟶ (Γ J A).obj F) :=
  ((sheafificationAdjunction J A).homEquiv _ _).symm.trans
    ((constantSheafΓAdj J A).homEquiv _ _)

/--
lemma `Sheaf.ΓHomEquiv_naturality_left` / 引理 `Sheaf.ΓHomEquiv_naturality_left`

English:
lemma Sheaf.ΓHomEquiv_naturality_left
  statement: [HasGlobalSectionsFunctor J A] {X' X : A} {F : Sheaf J A}
  proof: (congrArg _ ((sheafificationAdjunction J A).homEquiv_naturality_left_symm _ _)).trans
    ((constantSheafΓAdj J A).homEquiv_naturality_left _ _)

中文:
引理 层.ΓHomEquiv_naturality_left
  结论: [HasGlobalSectionsFunctor J A] {X' X : A} {F : 层 J A}
  证明: (congrArg _ ((sheafificationAdjunction J A).homEquiv_naturality_left_symm _ _)).trans
    ((constantSheafΓAdj J A).homEquiv_naturality_left _ _)

Depends on / 依赖: homEquiv_naturality_left, homEquiv_naturality_left_symm, sheafificationAdjunction
-/
lemma Sheaf.ΓHomEquiv_naturality_left [HasGlobalSectionsFunctor J A] {X' X : A} {F : Sheaf J A}
    (f : X' ⟶ X) (g : (Functor.const _).obj X ⟶ F.obj) :
    ΓHomEquiv ((Functor.const _).map f ≫ g) = f ≫ ΓHomEquiv g :=
  (congrArg _ ((sheafificationAdjunction J A).homEquiv_naturality_left_symm _ _)).trans
    ((constantSheafΓAdj J A).homEquiv_naturality_left _ _)

/--
lemma `Sheaf.ΓHomEquiv_naturality_left_symm` / 引理 `Sheaf.ΓHomEquiv_naturality_left_symm`

English:
lemma Sheaf.ΓHomEquiv_naturality_left_symm
  statement: [HasGlobalSectionsFunctor J A] {X' X : A} {F : Sheaf J A}
  proof: (congrArg _ ((constantSheafΓAdj J A).homEquiv_naturality_left_symm _ _)).trans
    ((sheafificationAdjunction J A).homEquiv_naturality_left _ _)

中文:
引理 层.ΓHomEquiv_naturality_left_symm
  结论: [HasGlobalSectionsFunctor J A] {X' X : A} {F : 层 J A}
  证明: (congrArg _ ((constantSheafΓAdj J A).homEquiv_naturality_left_symm _ _)).trans
    ((sheafificationAdjunction J A).homEquiv_naturality_left _ _)

Depends on / 依赖: homEquiv_naturality_left, homEquiv_naturality_left_symm, sheafificationAdjunction
-/
lemma Sheaf.ΓHomEquiv_naturality_left_symm [HasGlobalSectionsFunctor J A] {X' X : A} {F : Sheaf J A}
    (f : X' ⟶ X) (g : X ⟶ (Γ J A).obj F) :
    ΓHomEquiv.symm (f ≫ g) = (Functor.const _).map f ≫ ΓHomEquiv.symm g :=
  (congrArg _ ((constantSheafΓAdj J A).homEquiv_naturality_left_symm _ _)).trans
    ((sheafificationAdjunction J A).homEquiv_naturality_left _ _)

/--
lemma `Sheaf.ΓHomEquiv_naturality_right` / 引理 `Sheaf.ΓHomEquiv_naturality_right`

English:
lemma Sheaf.ΓHomEquiv_naturality_right
  statement: [HasGlobalSectionsFunctor J A] {X : A} {F F' : Sheaf J A}
  proof: (congrArg _ ((sheafificationAdjunction J A).homEquiv_naturality_right_symm _ _)).trans
    ((constantSheafΓAdj J A).homEquiv_naturality_right _ _)

中文:
引理 层.ΓHomEquiv_naturality_right
  结论: [HasGlobalSectionsFunctor J A] {X : A} {F F' : 层 J A}
  证明: (congrArg _ ((sheafificationAdjunction J A).homEquiv_naturality_right_symm _ _)).trans
    ((constantSheafΓAdj J A).homEquiv_naturality_right _ _)

Depends on / 依赖: homEquiv_naturality_right, homEquiv_naturality_right_symm, sheafificationAdjunction
-/
lemma Sheaf.ΓHomEquiv_naturality_right [HasGlobalSectionsFunctor J A] {X : A} {F F' : Sheaf J A}
    (f : (Functor.const _).obj X ⟶ F.obj) (g : F ⟶ F') :
    ΓHomEquiv (f ≫ g.hom) = ΓHomEquiv f ≫ (Γ J A).map g :=
  (congrArg _ ((sheafificationAdjunction J A).homEquiv_naturality_right_symm _ _)).trans
    ((constantSheafΓAdj J A).homEquiv_naturality_right _ _)

/--
lemma `Sheaf.ΓHomEquiv_naturality_right_symm` / 引理 `Sheaf.ΓHomEquiv_naturality_right_symm`

English:
lemma Sheaf.ΓHomEquiv_naturality_right_symm
  statement: [HasGlobalSectionsFunctor J A] {X : A}
  proof: (congrArg _ ((constantSheafΓAdj J A).homEquiv_naturality_right_symm _ _)).trans
    ((sheafificationAdjunction J A).homEquiv_naturality_right _ _)

中文:
引理 层.ΓHomEquiv_naturality_right_symm
  结论: [HasGlobalSectionsFunctor J A] {X : A}
  证明: (congrArg _ ((constantSheafΓAdj J A).homEquiv_naturality_right_symm _ _)).trans
    ((sheafificationAdjunction J A).homEquiv_naturality_right _ _)

Depends on / 依赖: homEquiv_naturality_right, homEquiv_naturality_right_symm, sheafificationAdjunction
-/
lemma Sheaf.ΓHomEquiv_naturality_right_symm [HasGlobalSectionsFunctor J A] {X : A}
    {F F' : Sheaf J A} (f : X ⟶ (Γ J A).obj F) (g : F ⟶ F') :
    ΓHomEquiv.symm (f ≫ (Γ J A).map g) = ΓHomEquiv.symm f ≫ g.hom :=
  (congrArg _ ((constantSheafΓAdj J A).homEquiv_naturality_right_symm _ _)).trans
    ((sheafificationAdjunction J A).homEquiv_naturality_right _ _)

/-- The cone over a given sheaf whose cone point is the global sections and whose components are
the restriction maps. -/
@[simps pt]
/--
Definition of `Sheaf.coneΓ` / `Sheaf.coneΓ` 的定义

English:
definition Sheaf.coneΓ
  signature: [HasGlobalSectionsFunctor J A] (F : Sheaf J A)
  body: (Γ J A).obj F
  π := ΓHomEquiv.symm (𝟙 _)

中文:
定义 层.coneΓ
  签名: [HasGlobalSectionsFunctor J A] (F : 层 J A)
  定义体: (Γ J A).obj F
  π := ΓHomEquiv.symm (𝟙 _)
-/
noncomputable def Sheaf.coneΓ [HasGlobalSectionsFunctor J A] (F : Sheaf J A) : Cone F.obj where
  pt := (Γ J A).obj F
  π := ΓHomEquiv.symm (𝟙 _)

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `Sheaf.isLimitConeΓ` / `Sheaf.isLimitConeΓ` 的定义

English:
definition Sheaf.isLimitConeΓ
  signature: [HasGlobalSectionsFunctor J A] (F : Sheaf J A)
  body: F.ΓHomEquiv c.π
  fac c j := by
    suffices h : ((Functor.const Cᵒᵖ).map (ΓHomEquiv c.π)) ≫ F.coneΓ.π = c.π from congr_app h j
    simp [coneΓ, ← ΓHomEquiv_naturality_left_symm]
  uniq c f hf := by
    replace hf : ((Functor.const Cᵒᵖ).map f) ≫ F.coneΓ.π = c.π := by ext j; exact hf j
    simpa [coneΓ, ← ΓHomEquiv_naturality_left_symm, Equiv.symm_apply_eq] using hf

中文:
定义 层.isLimitConeΓ
  签名: [HasGlobalSectionsFunctor J A] (F : 层 J A)
  定义体: F.ΓHomEquiv c.π
  fac c j := by
    suffices h : ((Functor.const Cᵒᵖ).map (ΓHomEquiv c.π)) ≫ F.coneΓ.π = c.π from congr_app h j
    simp [coneΓ, ← ΓHomEquiv_naturality_left_symm]
  uniq c f hf := by
    replace hf : ((Functor.const Cᵒᵖ).map f) ≫ F.coneΓ.π = c.π := by ext j; exact hf j
    simpa [coneΓ, ← ΓHomEquiv_naturality_left_symm, Equiv.symm_apply_eq] using hf
-/
noncomputable def Sheaf.isLimitConeΓ [HasGlobalSectionsFunctor J A] (F : Sheaf J A) :
    IsLimit F.coneΓ where
  lift c := F.ΓHomEquiv c.π
  fac c j := by
    suffices h : ((Functor.const Cᵒᵖ).map (ΓHomEquiv c.π)) ≫ F.coneΓ.π = c.π from congr_app h j
    simp [coneΓ, ← ΓHomEquiv_naturality_left_symm]
  uniq c f hf := by
    replace hf : ((Functor.const Cᵒᵖ).map f) ≫ F.coneΓ.π = c.π := by ext j; exact hf j
    simpa [coneΓ, ← ΓHomEquiv_naturality_left_symm, Equiv.symm_apply_eq] using hf

/--
Definition of `Sheaf.ΓRes` / `Sheaf.ΓRes` 的定义

English:
definition Sheaf.ΓRes
  signature: [HasGlobalSectionsFunctor J A] (F : Sheaf J A) (U : Cᵒᵖ)
  body: F.coneΓ.π.app U

@[reassoc (attr := simp)]

中文:
定义 层.ΓRes
  签名: [HasGlobalSectionsFunctor J A] (F : 层 J A) (U : Cᵒᵖ)
  定义体: F.coneΓ.π.app U

@[reassoc (attr := simp)]

Depends on / 依赖: F.cone
-/
noncomputable def Sheaf.ΓRes [HasGlobalSectionsFunctor J A] (F : Sheaf J A) (U : Cᵒᵖ) :
    (Γ J A).obj F ⟶ F.obj.obj U :=
  F.coneΓ.π.app U

@[reassoc (attr := simp)]
/--
lemma `Sheaf.ΓRes_map` / 引理 `Sheaf.ΓRes_map`

English:
lemma Sheaf.ΓRes_map
  given: [HasGlobalSectionsFunctor J A] (F : Sheaf J A) {V U : Cᵒᵖ} (f : U ⟶ V)
  proof: F.coneΓ.w f

@[simp]

中文:
引理 层.ΓRes_map
  条件: [HasGlobalSectionsFunctor J A] (F : 层 J A) {V U : Cᵒᵖ} (f : U ⟶ V)
  证明: F.coneΓ.w f

@[simp]

Depends on / 依赖: F.cone
-/
lemma Sheaf.ΓRes_map [HasGlobalSectionsFunctor J A] (F : Sheaf J A) {V U : Cᵒᵖ} (f : U ⟶ V) :
    F.ΓRes U ≫ F.obj.map f = F.ΓRes V :=
  F.coneΓ.w f

@[simp]
/--
lemma `Sheaf.coneΓ_π_app` / 引理 `Sheaf.coneΓ_π_app`

English:
lemma Sheaf.coneΓ_π_app
  given: [HasGlobalSectionsFunctor J A] (F : Sheaf J A) (U : Cᵒᵖ)
  proof: rfl

中文:
引理 层.coneΓ_π_app
  条件: [HasGlobalSectionsFunctor J A] (F : 层 J A) (U : Cᵒᵖ)
  证明: rfl
-/
lemma Sheaf.coneΓ_π_app [HasGlobalSectionsFunctor J A] (F : Sheaf J A) (U : Cᵒᵖ) :
    F.coneΓ.π.app U = F.ΓRes U := rfl

/--
lemma `Sheaf.ΓRes_naturality` / 引理 `Sheaf.ΓRes_naturality`

English:
lemma Sheaf.ΓRes_naturality
  given: [HasGlobalSectionsFunctor J A] {F G : Sheaf J A} (f : F ⟶ G) (U : Cᵒᵖ)
  proof: by
refine .trans ?_ congr_app (ΓHomEquiv_naturality_right_symm _ _) U
  exact (congr_app (ΓHomEquiv_naturality_left_symm ((Γ J A).map f) (𝟙 _)) U).symm.trans (by simp)

中文:
引理 层.ΓRes_naturality
  条件: [HasGlobalSectionsFunctor J A] {F G : 层 J A} (f : F ⟶ G) (U : Cᵒᵖ)
  证明: by
refine .trans ?_ congr_app (ΓHomEquiv_naturality_right_symm _ _) U
  exact (congr_app (ΓHomEquiv_naturality_left_symm ((Γ J A).map f) (𝟙 _)) U).symm.trans (by simp)

Depends on / 依赖: congr_app, symm.trans
-/
lemma Sheaf.ΓRes_naturality [HasGlobalSectionsFunctor J A] {F G : Sheaf J A} (f : F ⟶ G) (U : Cᵒᵖ) :
    (Γ J A).map f ≫ ΓRes G U = ΓRes F U ≫ f.hom.app U := by
refine .trans ?_ congr_app (ΓHomEquiv_naturality_right_symm _ _) U
  exact (congr_app (ΓHomEquiv_naturality_left_symm ((Γ J A).map f) (𝟙 _)) U).symm.trans (by simp)

variable (J A)

/-- The natural transformation from the global sections functor to the sections functor on any
object `U`. -/
@[simps!]
/--
Definition of `Sheaf.natTransΓRes` / `Sheaf.natTransΓRes` 的定义

English:
definition Sheaf.natTransΓRes
  signature: [HasGlobalSectionsFunctor J A] (U : Cᵒᵖ)
  body: ΓRes F U
  naturality _ _ f := ΓRes_naturality f U

中文:
定义 层.natTransΓRes
  签名: [HasGlobalSectionsFunctor J A] (U : Cᵒᵖ)
  定义体: ΓRes F U
  naturality _ _ f := ΓRes_naturality f U
-/
noncomputable def Sheaf.natTransΓRes [HasGlobalSectionsFunctor J A] (U : Cᵒᵖ) :
    Γ J A ⟶ (sheafSections J A).obj U where
  app F := ΓRes F U
  naturality _ _ f := ΓRes_naturality f U

/--
Definition of `Sheaf.ΓObjEquivSections` / `Sheaf.ΓObjEquivSections` 的定义

English:
definition Sheaf.ΓObjEquivSections
  signature: [HasWeakSheafify J (Type w)]
  body: (Equiv.trans (by exact (Equiv.funUnique (PUnit) _).symm.trans TypeCat.homEquiv.symm)
    ΓHomEquiv.symm).trans (F.obj.sectionsEquivHom PUnit).symm

中文:
定义 层.ΓObjEquivSections
  签名: [HasWeakSheafify J (类型 w)]
  定义体: (Equiv.trans (by exact (Equiv.funUnique (PUnit) _).symm.trans TypeCat.homEquiv.symm)
    ΓHomEquiv.symm).trans (F.obj.sectionsEquivHom PUnit).symm

Depends on / 依赖: Equiv.funUnique, Equiv.trans, F.obj.sectionsEquivHom, HomEquiv.symm, TypeCat, TypeCat.homEquiv.symm, funUnique, homEquiv, sectionsEquivHom, symm.trans
-/
noncomputable def Sheaf.ΓObjEquivSections [HasWeakSheafify J (Type w)]
    [HasGlobalSectionsFunctor J (Type w)] (F : Sheaf J (Type w)) :
      (Γ J (Type w)).obj F ≃ F.obj.sections :=
  (Equiv.trans (by exact (Equiv.funUnique (PUnit) _).symm.trans TypeCat.homEquiv.symm)
    ΓHomEquiv.symm).trans (F.obj.sectionsEquivHom PUnit).symm

/--
lemma `Sheaf.ΓObjEquivSections_naturality` / 引理 `Sheaf.ΓObjEquivSections_naturality`

English:
lemma Sheaf.ΓObjEquivSections_naturality
  statement: [HasWeakSheafify J (Type w)]
  proof: by
  dsimp [ΓObjEquivSections]
  exact (congr_arg _ (ΓHomEquiv_naturality_right_symm (↾(uniqueElim x)) f)).trans
    (Functor.sectionsEquivHom_naturality_symm _ _ _)

中文:
引理 层.ΓObjEquivSections_naturality
  结论: [HasWeakSheafify J (类型 w)]
  证明: by
  dsimp [ΓObjEquivSections]
  exact (congr_arg _ (ΓHomEquiv_naturality_right_symm (↾(uniqueElim x)) f)).trans
    (Functor.sectionsEquivHom_naturality_symm _ _ _)

Depends on / 依赖: Functor, Functor.sectionsEquivHom_naturality_symm, congr_arg, sectionsEquivHom_naturality_symm, uniqueElim
-/
lemma Sheaf.ΓObjEquivSections_naturality [HasWeakSheafify J (Type w)]
    [HasGlobalSectionsFunctor J (Type w)] {F G : Sheaf J (Type w)} (f : F ⟶ G)
    (x : (Γ J (Type w)).obj F) :
    (ΓObjEquivSections J G) ((Γ J _).map f x) =
      (Functor.sectionsFunctor _).map f.hom ((ΓObjEquivSections J F) x) := by
  dsimp [ΓObjEquivSections]
  exact (congr_arg _ (ΓHomEquiv_naturality_right_symm (↾(uniqueElim x)) f)).trans
    (Functor.sectionsEquivHom_naturality_symm _ _ _)

/--
lemma `Sheaf.ΓObjEquivSections_naturality_symm` / 引理 `Sheaf.ΓObjEquivSections_naturality_symm`

English:
lemma Sheaf.ΓObjEquivSections_naturality_symm
  statement: [HasWeakSheafify J (Type w)]
  proof: ConcreteCategory.congr_hom (ΓHomEquiv_naturality_right (F.obj.sectionsEquivHom _ x) f) _

中文:
引理 层.ΓObjEquivSections_naturality_symm
  结论: [HasWeakSheafify J (类型 w)]
  证明: ConcreteCategory.congr_hom (ΓHomEquiv_naturality_right (F.obj.sectionsEquivHom _ x) f) _

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, F.obj.sectionsEquivHom, congr_hom, sectionsEquivHom
-/
lemma Sheaf.ΓObjEquivSections_naturality_symm [HasWeakSheafify J (Type w)]
    [HasGlobalSectionsFunctor J (Type w)] {F G : Sheaf J (Type w)} (f : F ⟶ G)
    (x : F.obj.sections) : (ΓObjEquivSections J G).symm ((Functor.sectionsFunctor _).map f.hom x) =
      (Γ J _).map f ((ΓObjEquivSections J F).symm x) :=
  ConcreteCategory.congr_hom (ΓHomEquiv_naturality_right (F.obj.sectionsEquivHom _ x) f) _

/--
Definition of `Sheaf.ΓNatIsoSectionsFunctor` / `Sheaf.ΓNatIsoSectionsFunctor` 的定义

English:
definition Sheaf.ΓNatIsoSectionsFunctor
  signature: :
  body: NatIso.ofComponents (fun F => (ΓObjEquivSections J F).toIso) fun f => by
    ext x
    exact ΓObjEquivSections_naturality J f x

中文:
定义 层.Γ自然数IsoSectionsFunctor
  签名: :
  定义体: NatIso.ofComponents (fun F => (ΓObjEquivSections J F).toIso) fun f => by
    ext x
    exact ΓObjEquivSections_naturality J f x

Depends on / 依赖: NatIso, NatIso.ofComponents, ofComponents
-/
noncomputable def Sheaf.ΓNatIsoSectionsFunctor :
    Γ J (Type (max u v)) ≅ sheafToPresheaf J _ ⋙ Functor.sectionsFunctor _ :=
  NatIso.ofComponents (fun F => (ΓObjEquivSections J F).toIso) fun f => by
    ext x
    exact ΓObjEquivSections_naturality J f x

/--
Definition of `Sheaf.ΓObjEquivHom` / `Sheaf.ΓObjEquivHom` 的定义

English:
definition Sheaf.ΓObjEquivHom
  signature: [HasWeakSheafify J (Type w)]
  body: ((Equiv.funUnique X _).symm.trans TypeCat.homEquiv.symm).trans
    ((constantSheafΓAdj J (Type w)).homEquiv _ _).symm

中文:
定义 层.ΓObjEquivHom
  签名: [HasWeakSheafify J (类型 w)]
  定义体: ((Equiv.funUnique X _).symm.trans TypeCat.homEquiv.symm).trans
    ((constantSheafΓAdj J (Type w)).homEquiv _ _).symm

Depends on / 依赖: Equiv.funUnique, TypeCat, TypeCat.homEquiv.symm, funUnique, homEquiv, symm.trans
-/
noncomputable def Sheaf.ΓObjEquivHom [HasWeakSheafify J (Type w)]
    [HasGlobalSectionsFunctor J (Type w)] (F : Sheaf J (Type w)) (X : Type w)
    [Unique X] : (Γ J (Type w)).obj F ≃ ((constantSheaf J (Type w)).obj X ⟶ F) :=
  ((Equiv.funUnique X _).symm.trans TypeCat.homEquiv.symm).trans
    ((constantSheafΓAdj J (Type w)).homEquiv _ _).symm

/--
lemma `Sheaf.ΓObjEquivHom_naturality` / 引理 `Sheaf.ΓObjEquivHom_naturality`

English:
lemma Sheaf.ΓObjEquivHom_naturality
  statement: [HasWeakSheafify J (Type w)]
  proof: (constantSheafΓAdj J (Type w)).homEquiv_naturality_right_symm
    (↾(uniqueElim x)) f

中文:
引理 层.ΓObjEquivHom_naturality
  结论: [HasWeakSheafify J (类型 w)]
  证明: (constantSheafΓAdj J (Type w)).homEquiv_naturality_right_symm
    (↾(uniqueElim x)) f

Depends on / 依赖: homEquiv_naturality_right_symm, uniqueElim
-/
lemma Sheaf.ΓObjEquivHom_naturality [HasWeakSheafify J (Type w)]
    [HasGlobalSectionsFunctor J (Type w)] (X : Type w) [Unique X]
    {F G : Sheaf J (Type w)} (f : F ⟶ G) (x : (Γ J (Type w)).obj F) :
    (ΓObjEquivHom J G X) ((Γ J (Type w)).map f x) = (ΓObjEquivHom J F X) x ≫ f :=
  (constantSheafΓAdj J (Type w)).homEquiv_naturality_right_symm
    (↾(uniqueElim x)) f

/--
lemma `Sheaf.ΓObjEquivHom_naturality_symm` / 引理 `Sheaf.ΓObjEquivHom_naturality_symm`

English:
lemma Sheaf.ΓObjEquivHom_naturality_symm
  statement: [HasWeakSheafify J (Type w)]
  proof: ConcreteCategory.congr_hom ((constantSheafΓAdj J _).homEquiv_naturality_right x f) default

中文:
引理 层.ΓObjEquivHom_naturality_symm
  结论: [HasWeakSheafify J (类型 w)]
  证明: ConcreteCategory.congr_hom ((constantSheafΓAdj J _).homEquiv_naturality_right x f) default

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, congr_hom, homEquiv_naturality_right
-/
lemma Sheaf.ΓObjEquivHom_naturality_symm [HasWeakSheafify J (Type w)]
    [HasGlobalSectionsFunctor J (Type w)] {X : Type w} [Unique X]
    {F G : Sheaf J (Type w)} (f : F ⟶ G) (x : (constantSheaf J _).obj X ⟶ F) :
    (ΓObjEquivHom J G X).symm (x ≫ f) = (Γ J _).map f ((ΓObjEquivHom J F X).symm x) :=
  ConcreteCategory.congr_hom ((constantSheafΓAdj J _).homEquiv_naturality_right x f) default

/--
Definition of `Sheaf.ΓNatIsoCoyoneda` / `Sheaf.ΓNatIsoCoyoneda` 的定义

English:
definition Sheaf.ΓNatIsoCoyoneda
  signature: (X : Type (max u v)) [Unique X]
  body: NatIso.ofComponents (fun F => (F.ΓObjEquivHom J X).toIso) fun f => by
    ext x
    exact ΓObjEquivHom_naturality J X f x

中文:
定义 层.Γ自然数IsoCoyoneda
  签名: (X : 类型 (最大值 u v)) [唯一 X]
  定义体: NatIso.ofComponents (fun F => (F.ΓObjEquivHom J X).toIso) fun f => by
    ext x
    exact ΓObjEquivHom_naturality J X f x

Depends on / 依赖: NatIso, NatIso.ofComponents, ofComponents
-/
noncomputable def Sheaf.ΓNatIsoCoyoneda (X : Type (max u v)) [Unique X] :
    Γ J (Type (max u v)) ≅ coyoneda.obj (op ((constantSheaf J (Type (max u v))).obj X)) :=
  NatIso.ofComponents (fun F => (F.ΓObjEquivHom J X).toIso) fun f => by
    ext x
    exact ΓObjEquivHom_naturality J X f x

end CategoryTheory
