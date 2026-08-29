/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Junyan Xu
-/
module

public import Mathlib.Topology.Sheaves.PUnit
public import Mathlib.Topology.Sheaves.Stalks
public import Mathlib.Topology.Sheaves.Functors

/-!
# Skyscraper (pre)sheaves

A skyscraper (pre)sheaf `𝓕 : (Pre)Sheaf C X` is the (pre)sheaf with value `A` at point `p₀` that is
supported only at open sets contain `p₀`, i.e. `𝓕(U) = A` if `p₀ ∈ U` and `𝓕(U) = *` if `p₀ ∉ U`
where `*` is a terminal object of `C`. In terms of stalks, `𝓕` is supported at all specializations
of `p₀`, i.e. if `p₀ ⤳ x` then `𝓕ₓ ≅ A` and if `¬ p₀ ⤳ x` then `𝓕ₓ ≅ *`.

## Main definitions

* `skyscraperPresheaf`: `skyscraperPresheaf p₀ A` is the skyscraper presheaf at point `p₀` with
  value `A`.
* `skyscraperSheaf`: the skyscraper presheaf satisfies the sheaf condition.

## Main statements

* `skyscraperPresheafStalkOfSpecializes`: if `y ∈ closure {p₀}` then the stalk of
  `skyscraperPresheaf p₀ A` at `y` is `A`.
* `skyscraperPresheafStalkOfNotSpecializes`: if `y ∉ closure {p₀}` then the stalk of
  `skyscraperPresheaf p₀ A` at `y` is `*` the terminal object.

TODO: generalize universe level when calculating stalks, after generalizing universe level of stalk.
TODO(@joelriou): refactor the definitions in this file so as to make them
particular cases of general constructions for points of sites from
`Mathlib/CategoryTheory/Sites/Point/Skyscraper.lean`.

-/

@[expose] public section

noncomputable section

open TopologicalSpace TopCat CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe u v w

variable {X : TopCat.{u}} (p₀ : X) [forall U : Opens X, Decidable (p₀ in U)]

section

variable {C : Type v} [Category.{w} C] [HasTerminal C] (A : C)

/-- A skyscraper presheaf is a presheaf supported at a single point: if `p₀ ∈ X` is a specified
point, then the skyscraper presheaf `𝓕` with value `A` is defined by `U ↦ A` if `p₀ ∈ U` and
`U ↦ *` if `p₀ ∉ A` where `*` is some terminal object.
-/
@[simps]
/--
Definition of `skyscraperPresheaf` / `skyscraperPresheaf` 的定义

English:
definition skyscraperPresheaf
  signature: : Presheaf C X where
  body: if p₀ in unop U then A else terminal C
  map {U V} i :=
if h : p₀ in unop V then eqToHom by rw [if_pos h, if_pos (by simpa using i.unop.le h)]
    else ((if_neg h).symm.ndrec terminalIsTerminal).from _
  map_id U :=
    (em (p₀ in U.unop)).elim (fun h => dif_pos h) fun h =>
      ((if_neg h).symm.nd

中文:
定义 skyscraperPresheaf
  签名: : 预层 C X where
  定义体: if p₀ in unop U then A else terminal C
  map {U V} i :=
if h : p₀ in unop V then eqToHom by rw [if_pos h, if_pos (by simpa using i.unop.le h)]
    else ((if_neg h).symm.ndrec terminalIsTerminal).from _
  map_id U :=
    (em (p₀ in U.unop)).elim (fun h => dif_pos h) fun h =>
      ((if_neg h).symm.nd

Depends on / 依赖: terminal
-/
def skyscraperPresheaf : Presheaf C X where
  obj U := if p₀ in unop U then A else terminal C
  map {U V} i :=
if h : p₀ in unop V then eqToHom by rw [if_pos h, if_pos (by simpa using i.unop.le h)]
    else ((if_neg h).symm.ndrec terminalIsTerminal).from _
  map_id U :=
    (em (p₀ in U.unop)).elim (fun h => dif_pos h) fun h =>
      ((if_neg h).symm.ndrec terminalIsTerminal).hom_ext _ _
  map_comp {U V W} iVU iWV := by
    by_cases hW : p₀ in unop W
    · have hV : p₀ in unop V := leOfHom iWV.unop hW
      simp only [dif_pos hW, dif_pos hV, eqToHom_trans]
    · dsimp; rw [dif_neg hW]; apply ((if_neg hW).symm.ndrec terminalIsTerminal).hom_ext

/--
theorem `skyscraperPresheaf_eq_pushforward` / 定理 `skyscraperPresheaf_eq_pushforward`

English:
theorem skyscraperPresheaf_eq_pushforward
  proof: by
  convert_to @skyscraperPresheaf X p₀ (fun U => hd <| (Opens.map <| ofHom <|
      ContinuousMap.const _ p₀).obj U)
    C _ _ A = _ <;> congr

中文:
定理 skyscraperPresheaf_eq_pushforward
  证明: by
  convert_to @skyscraperPresheaf X p₀ (fun U => hd <| (Opens.map <| ofHom <|
      ContinuousMap.const _ p₀).obj U)
    C _ _ A = _ <;> congr

Depends on / 依赖: ContinuousMap, ContinuousMap.const, Opens.map, PUnit.unit, TopCat, TopCat.of, convert_to, skyscraperPresheaf
-/
theorem skyscraperPresheaf_eq_pushforward
    [hd : forall U : Opens (TopCat.of PUnit.{u + 1}), Decidable (PUnit.unit in U)] :
    skyscraperPresheaf p₀ A =
      (ofHom (ContinuousMap.const (TopCat.of PUnit) p₀)) _*
        skyscraperPresheaf (X := TopCat.of PUnit) PUnit.unit A := by
  convert_to @skyscraperPresheaf X p₀ (fun U => hd <| (Opens.map <| ofHom <|
      ContinuousMap.const _ p₀).obj U)
    C _ _ A = _ <;> congr

set_option backward.defeqAttrib.useBackward true in
/-- Taking skyscraper presheaf at a point is functorial: `c ↦ skyscraper p₀ c` defines a functor by
sending every `f : a ⟶ b` to the natural transformation `α` defined as: `α(U) = f : a ⟶ b` if
`p₀ ∈ U` and the unique morphism to a terminal object in `C` if `p₀ ∉ U`.
-/
@[simps]
/--
Definition of `SkyscraperPresheafFunctor.map'` / `SkyscraperPresheafFunctor.map'` 的定义

English:
definition SkyscraperPresheafFunctor.map'
  signature: {a b : C} (f : a ⟶ b)
  body: if h : p₀ in U.unop then eqToHom (if_pos h) ≫ f ≫ eqToHom (if_pos h).symm
    else ((if_neg h).symm.ndrec terminalIsTerminal).from _
  naturality U V i := by
    simp only [skyscraperPresheaf_map]
    by_cases hV : p₀ in V.unop
    · have hU : p₀ in U.unop := leOfHom i.unop hV
      simp only [skysc

中文:
定义 SkyscraperPresheafFunctor.map'
  签名: {a b : C} (f : a ⟶ b)
  定义体: if h : p₀ in U.unop then eqToHom (if_pos h) ≫ f ≫ eqToHom (if_pos h).symm
    else ((if_neg h).symm.ndrec terminalIsTerminal).from _
  naturality U V i := by
    simp only [skyscraperPresheaf_map]
    by_cases hV : p₀ in V.unop
    · have hU : p₀ in U.unop := leOfHom i.unop hV
      simp only [skysc

Depends on / 依赖: Category, Category.assoc, U.unop, V.unop, eqToHom, eqToHom_trans, eqToHom_trans_assoc, hom_ext, i.unop, if_neg, if_pos, leOfHom, naturality, reduceDIte, skyscraperPresheaf_map, skyscraperPresheaf_obj, symm.ndrec, terminalIsTerminal
-/
def SkyscraperPresheafFunctor.map' {a b : C} (f : a ⟶ b) :
    skyscraperPresheaf p₀ a ⟶ skyscraperPresheaf p₀ b where
  app U :=
    if h : p₀ in U.unop then eqToHom (if_pos h) ≫ f ≫ eqToHom (if_pos h).symm
    else ((if_neg h).symm.ndrec terminalIsTerminal).from _
  naturality U V i := by
    simp only [skyscraperPresheaf_map]
    by_cases hV : p₀ in V.unop
    · have hU : p₀ in U.unop := leOfHom i.unop hV
      simp only [skyscraperPresheaf_obj, hU, hV, ↓reduceDIte, eqToHom_trans_assoc, Category.assoc,
        eqToHom_trans]
    · apply ((if_neg hV).symm.ndrec terminalIsTerminal).hom_ext

set_option backward.defeqAttrib.useBackward true in
/--
theorem `SkyscraperPresheafFunctor.map'_id` / 定理 `SkyscraperPresheafFunctor.map'_id`

English:
theorem SkyscraperPresheafFunctor.map'_id
  given: {a : C}
  proof: by
  ext U
  simp only [SkyscraperPresheafFunctor.map'_app]; split_ifs <;> cat_disch

中文:
定理 SkyscraperPresheafFunctor.map'_id
  条件: {a : C}
  证明: by
  ext U
  simp only [SkyscraperPresheafFunctor.map'_app]; split_ifs <;> cat_disch
-/
theorem SkyscraperPresheafFunctor.map'_id {a : C} :
    SkyscraperPresheafFunctor.map' p₀ (𝟙 a) = 𝟙 _ := by
  ext U
  simp only [SkyscraperPresheafFunctor.map'_app]; split_ifs <;> cat_disch

set_option backward.defeqAttrib.useBackward true in
/--
theorem `SkyscraperPresheafFunctor.map'_comp` / 定理 `SkyscraperPresheafFunctor.map'_comp`

English:
theorem SkyscraperPresheafFunctor.map'_comp
  given: {a b c : C} (f : a ⟶ b) (g : b ⟶ c)
  proof: by
  ext U
  simp only [SkyscraperPresheafFunctor.map'_app]
  split_ifs with h <;> cat_disch

中文:
定理 SkyscraperPresheafFunctor.map'_comp
  条件: {a b c : C} (f : a ⟶ b) (g : b ⟶ c)
  证明: by
  ext U
  simp only [SkyscraperPresheafFunctor.map'_app]
  split_ifs with h <;> cat_disch
-/
theorem SkyscraperPresheafFunctor.map'_comp {a b c : C} (f : a ⟶ b) (g : b ⟶ c) :
    SkyscraperPresheafFunctor.map' p₀ (f ≫ g) =
      SkyscraperPresheafFunctor.map' p₀ f ≫ SkyscraperPresheafFunctor.map' p₀ g := by
  ext U
  simp only [SkyscraperPresheafFunctor.map'_app]
  split_ifs with h <;> cat_disch

/-- Taking skyscraper presheaf at a point is functorial: `c ↦ skyscraper p₀ c` defines a functor by
sending every `f : a ⟶ b` to the natural transformation `α` defined as: `α(U) = f : a ⟶ b` if
`p₀ ∈ U` and the unique morphism to a terminal object in `C` if `p₀ ∉ U`.
-/
@[simps]
/--
Definition of `skyscraperPresheafFunctor` / `skyscraperPresheafFunctor` 的定义

English:
definition skyscraperPresheafFunctor
  signature: : C ⥤ Presheaf C X where
  body: skyscraperPresheaf p₀
  map := SkyscraperPresheafFunctor.map' p₀
  map_id _ := SkyscraperPresheafFunctor.map'_id p₀
  map_comp := SkyscraperPresheafFunctor.map'_comp p₀

中文:
定义 skyscraperPresheafFunctor
  签名: : C ⥤ 预层 C X where
  定义体: skyscraperPresheaf p₀
  map := SkyscraperPresheafFunctor.map' p₀
  map_id _ := SkyscraperPresheafFunctor.map'_id p₀
  map_comp := SkyscraperPresheafFunctor.map'_comp p₀

Depends on / 依赖: skyscraperPresheaf
-/
def skyscraperPresheafFunctor : C ⥤ Presheaf C X where
  obj := skyscraperPresheaf p₀
  map := SkyscraperPresheafFunctor.map' p₀
  map_id _ := SkyscraperPresheafFunctor.map'_id p₀
  map_comp := SkyscraperPresheafFunctor.map'_comp p₀

end

section

-- In this section, we calculate the stalks for skyscraper presheaves.
-- We need to restrict universe level.
variable {C : Type v} [Category.{u} C] (A : C) [HasTerminal C]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The cocone at `A` for the stalk functor of `skyscraperPresheaf p₀ A` when `y ∈ closure {p₀}`
-/
@[simps]
/--
Definition of `skyscraperPresheafCoconeOfSpecializes` / `skyscraperPresheafCoconeOfSpecializes` 的定义

English:
definition skyscraperPresheafCoconeOfSpecializes
  signature: {y : X} (h : p₀ ⤳ y)
  body: A
  ι :=
    { app := fun U => eqToHom <| if_pos <| h.mem_open U.unop.1.2 U.unop.2
      naturality := fun U V inc => by
        change dite _ _ _ ≫ _ = _; rw [dif_pos]
        swap
        · exact h.mem_open V.unop.1.2 V.unop.2
        · simp only [Functor.comp_obj, Functor.op_obj, skyscraperPreshe

中文:
定义 skyscraperPresheafCoconeOfSpecializes
  签名: {y : X} (h : p₀ ⤳ y)
  定义体: A
  ι :=
    { app := fun U => eqToHom <| if_pos <| h.mem_open U.unop.1.2 U.unop.2
      naturality := fun U V inc => by
        change dite _ _ _ ≫ _ = _; rw [dif_pos]
        swap
        · exact h.mem_open V.unop.1.2 V.unop.2
        · simp only [Functor.comp_obj, Functor.op_obj, skyscraperPreshe
-/
def skyscraperPresheafCoconeOfSpecializes {y : X} (h : p₀ ⤳ y) :
    Cocone ((OpenNhds.inclusion y).op ⋙ skyscraperPresheaf p₀ A) where
  pt := A
  ι :=
    { app := fun U => eqToHom <| if_pos <| h.mem_open U.unop.1.2 U.unop.2
      naturality := fun U V inc => by
        change dite _ _ _ ≫ _ = _; rw [dif_pos]
        swap
        · exact h.mem_open V.unop.1.2 V.unop.2
        · simp only [Functor.comp_obj, Functor.op_obj, skyscraperPresheaf_obj, unop_op,
            Functor.const_obj_obj, eqToHom_trans, Functor.const_obj_map, Category.comp_id] }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `skyscraperPresheafCoconeIsColimitOfSpecializes` / `skyscraperPresheafCoconeIsColimitOfSpecializes` 的定义

English:
definition skyscraperPresheafCoconeIsColimitOfSpecializes
  signature: {y : X} (h : p₀ ⤳ y)
  body: eqToHom (if_pos trivial).symm ≫ c.ι.app (op ⊤)
  fac c U := by
    dsimp
    rw [← c.w (homOfLE <| (le_top : unop U <= _)).op]
    change _ ≫ _ ≫ dite _ _ _ ≫ _ = _
    rw [dif_pos]
    · simp only [eqToHom_trans_assoc,
        eqToHom_refl, Category.id_comp, op_unop]
    · exact h.mem_open U.unop.1

中文:
定义 skyscraperPresheafCoconeIsColimitOfSpecializes
  签名: {y : X} (h : p₀ ⤳ y)
  定义体: eqToHom (if_pos trivial).symm ≫ c.ι.app (op ⊤)
  fac c U := by
    dsimp
    rw [← c.w (homOfLE <| (le_top : unop U <= _)).op]
    change _ ≫ _ ≫ dite _ _ _ ≫ _ = _
    rw [dif_pos]
    · simp only [eqToHom_trans_assoc,
        eqToHom_refl, Category.id_comp, op_unop]
    · exact h.mem_open U.unop.1

Depends on / 依赖: eqToHom, if_pos
-/
noncomputable def skyscraperPresheafCoconeIsColimitOfSpecializes {y : X} (h : p₀ ⤳ y) :
    IsColimit (skyscraperPresheafCoconeOfSpecializes p₀ A h) where
  desc c := eqToHom (if_pos trivial).symm ≫ c.ι.app (op ⊤)
  fac c U := by
    dsimp
    rw [← c.w (homOfLE <| (le_top : unop U <= _)).op]
    change _ ≫ _ ≫ dite _ _ _ ≫ _ = _
    rw [dif_pos]
    · simp only [eqToHom_trans_assoc,
        eqToHom_refl, Category.id_comp, op_unop]
    · exact h.mem_open U.unop.1.2 U.unop.2
  uniq c f h := by
    dsimp
    rw [← h]; rw [skyscraperPresheafCoconeOfSpecializes_ι_app]; rw [eqToHom_trans_assoc]; rw [eqToHom_refl]; rw [Category.id_comp]

/--
Definition of `skyscraperPresheafStalkOfSpecializes` / `skyscraperPresheafStalkOfSpecializes` 的定义

English:
definition skyscraperPresheafStalkOfSpecializes
  signature: [HasColimits C] {y : X} (h : p₀ ⤳ y)
  body: colimit.isoColimitCocone ⟨_, skyscraperPresheafCoconeIsColimitOfSpecializes p₀ A h⟩

@[reassoc (attr := simp)]

中文:
定义 skyscraperPresheafStalkOfSpecializes
  签名: [有余极限 C] {y : X} (h : p₀ ⤳ y)
  定义体: colimit.isoColimitCocone ⟨_, skyscraperPresheafCoconeIsColimitOfSpecializes p₀ A h⟩

@[reassoc (attr := simp)]

Depends on / 依赖: colimit, colimit.isoColimitCocone, isoColimitCocone, skyscraperPresheafCoconeIsColimitOfSpecializes
-/
noncomputable def skyscraperPresheafStalkOfSpecializes [HasColimits C] {y : X} (h : p₀ ⤳ y) :
    (skyscraperPresheaf p₀ A).stalk y ≅ A :=
  colimit.isoColimitCocone ⟨_, skyscraperPresheafCoconeIsColimitOfSpecializes p₀ A h⟩

@[reassoc (attr := simp)]
/--
lemma `germ_skyscraperPresheafStalkOfSpecializes_hom` / 引理 `germ_skyscraperPresheafStalkOfSpecializes_hom`

English:
lemma germ_skyscraperPresheafStalkOfSpecializes_hom
  given: [HasColimits C] {y : X} (h : p₀ ⤳ y) (U hU)
  proof: colimit.isoColimitCocone_ι_hom _ _

中文:
引理 germ_skyscraperPresheafStalkOfSpecializes_hom
  条件: [有余极限 C] {y : X} (h : p₀ ⤳ y) (U hU)
  证明: colimit.isoColimitCocone_ι_hom _ _

Depends on / 依赖: colimit, colimit.isoColimitCocone_
-/
lemma germ_skyscraperPresheafStalkOfSpecializes_hom [HasColimits C] {y : X} (h : p₀ ⤳ y) (U hU) :
    (skyscraperPresheaf p₀ A).germ U y hU ≫
      (skyscraperPresheafStalkOfSpecializes p₀ A h).hom = eqToHom (if_pos (h.mem_open U.2 hU)) :=
  colimit.isoColimitCocone_ι_hom _ _

/-- The cocone at `*` for the stalk functor of `skyscraperPresheaf p₀ A` when `y ∉ closure {p₀}`
-/
@[simps]
/--
Definition of `skyscraperPresheafCocone` / `skyscraperPresheafCocone` 的定义

English:
definition skyscraperPresheafCocone
  signature: (y : X)
  body: terminal C
  ι :=
    { app := fun _ => terminal.from _
      naturality := fun _ _ _ => terminalIsTerminal.hom_ext _ _ }

中文:
定义 skyscraperPresheafCocone
  签名: (y : X)
  定义体: terminal C
  ι :=
    { app := fun _ => terminal.from _
      naturality := fun _ _ _ => terminalIsTerminal.hom_ext _ _ }

Depends on / 依赖: terminal
-/
def skyscraperPresheafCocone (y : X) :
    Cocone ((OpenNhds.inclusion y).op ⋙ skyscraperPresheaf p₀ A) where
  pt := terminal C
  ι :=
    { app := fun _ => terminal.from _
      naturality := fun _ _ _ => terminalIsTerminal.hom_ext _ _ }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `skyscraperPresheafCoconeIsColimitOfNotSpecializes` / `skyscraperPresheafCoconeIsColimitOfNotSpecializes` 的定义

English:
definition skyscraperPresheafCoconeIsColimitOfNotSpecializes
  signature: {y : X} (h : ¬p₀ ⤳ y)
  body: let h1 : exists U : OpenNhds y, p₀ ∉ U.1 :=
    let ⟨U, ho, h₀, hy⟩ := not_specializes_iff_exists_open.mp h
    ⟨⟨⟨U, ho⟩, h₀⟩, hy⟩
  { desc := fun c => eqToHom (if_neg h1.choose_spec).symm ≫ c.ι.app (op h1.choose)
    fac := fun c U => by
      change _ = c.ι.app (op U.unop)
      simp only [← c.w 

中文:
定义 skyscraperPresheafCoconeIsColimitOfNotSpecializes
  签名: {y : X} (h : ¬p₀ ⤳ y)
  定义体: let h1 : exists U : OpenNhds y, p₀ ∉ U.1 :=
    let ⟨U, ho, h₀, hy⟩ := not_specializes_iff_exists_open.mp h
    ⟨⟨⟨U, ho⟩, h₀⟩, hy⟩
  { desc := fun c => eqToHom (if_neg h1.choose_spec).symm ≫ c.ι.app (op h1.choose)
    fac := fun c U => by
      change _ = c.ι.app (op U.unop)
      simp only [← c.w 

Depends on / 依赖: Category, Category.assoc, OpenNhds, U.unop, choose_spe, choose_spec, eqToHom, h1.choose, h1.choose_spe, h1.choose_spec, homOfLE, hom_ext, if_neg, inf_le_left, inf_le_right, not_specializes_iff_exists_open, not_specializes_iff_exists_open.mp, symm.ndrec, terminalIsTerminal
-/
noncomputable def skyscraperPresheafCoconeIsColimitOfNotSpecializes {y : X} (h : ¬p₀ ⤳ y) :
    IsColimit (skyscraperPresheafCocone p₀ A y) :=
  let h1 : exists U : OpenNhds y, p₀ ∉ U.1 :=
    let ⟨U, ho, h₀, hy⟩ := not_specializes_iff_exists_open.mp h
    ⟨⟨⟨U, ho⟩, h₀⟩, hy⟩
  { desc := fun c => eqToHom (if_neg h1.choose_spec).symm ≫ c.ι.app (op h1.choose)
    fac := fun c U => by
      change _ = c.ι.app (op U.unop)
      simp only [← c.w (homOfLE <| @inf_le_left _ _ h1.choose U.unop).op, ←
        c.w (homOfLE <| @inf_le_right _ _ h1.choose U.unop).op, ← Category.assoc]
      congr 1
      refine ((if_neg ?_).symm.ndrec terminalIsTerminal).hom_ext _ _
      exact fun h => h1.choose_spec h.1
    uniq := fun c f H => by
      dsimp
      rw [← Category.id_comp f]; rw [← H]; rw [← Category.assoc]
      congr 1; apply terminalIsTerminal.hom_ext }

/--
Definition of `skyscraperPresheafStalkOfNotSpecializes` / `skyscraperPresheafStalkOfNotSpecializes` 的定义

English:
definition skyscraperPresheafStalkOfNotSpecializes
  signature: [HasColimits C] {y : X} (h : ¬p₀ ⤳ y)
  body: colimit.isoColimitCocone ⟨_, skyscraperPresheafCoconeIsColimitOfNotSpecializes _ A h⟩

中文:
定义 skyscraperPresheafStalkOfNotSpecializes
  签名: [有余极限 C] {y : X} (h : ¬p₀ ⤳ y)
  定义体: colimit.isoColimitCocone ⟨_, skyscraperPresheafCoconeIsColimitOfNotSpecializes _ A h⟩

Depends on / 依赖: colimit, colimit.isoColimitCocone, isoColimitCocone, skyscraperPresheafCoconeIsColimitOfNotSpecializes
-/
noncomputable def skyscraperPresheafStalkOfNotSpecializes [HasColimits C] {y : X} (h : ¬p₀ ⤳ y) :
    (skyscraperPresheaf p₀ A).stalk y ≅ terminal C :=
  colimit.isoColimitCocone ⟨_, skyscraperPresheafCoconeIsColimitOfNotSpecializes _ A h⟩

/--
Definition of `skyscraperPresheafStalkOfNotSpecializesIsTerminal` / `skyscraperPresheafStalkOfNotSpecializesIsTerminal` 的定义

English:
definition skyscraperPresheafStalkOfNotSpecializesIsTerminal
  signature: [HasColimits C] {y : X} (h : ¬p₀ ⤳ y)
  body: IsTerminal.ofIso terminalIsTerminal (skyscraperPresheafStalkOfNotSpecializes _ _ h).symm

中文:
定义 skyscraperPresheafStalkOfNotSpecializesIsTerminal
  签名: [有余极限 C] {y : X} (h : ¬p₀ ⤳ y)
  定义体: IsTerminal.ofIso terminalIsTerminal (skyscraperPresheafStalkOfNotSpecializes _ _ h).symm

Depends on / 依赖: IsTerminal, IsTerminal.ofIso, skyscraperPresheafStalkOfNotSpecializes, terminalIsTerminal
-/
def skyscraperPresheafStalkOfNotSpecializesIsTerminal [HasColimits C] {y : X} (h : ¬p₀ ⤳ y) :
    IsTerminal ((skyscraperPresheaf p₀ A).stalk y) :=
IsTerminal.ofIso terminalIsTerminal (skyscraperPresheafStalkOfNotSpecializes _ _ h).symm

/--
theorem `skyscraperPresheaf_isSheaf` / 定理 `skyscraperPresheaf_isSheaf`

English:
theorem skyscraperPresheaf_isSheaf
  statement: (skyscraperPresheaf p₀ A).IsSheaf
  proof: by
  classical exact
(Presheaf.isSheaf_iso_iff (eqToIso <| skyscraperPresheaf_eq_pushforward p₀ A)).mpr
      (Sheaf.pushforward_sheaf_of_sheaf _
        (Presheaf.isSheaf_on_punit_of_isTerminal _ (by
          dsimp [skyscraperPresheaf]
          rw [if_neg]
          · exact terminalIsTerminal
   

中文:
定理 skyscraperPresheaf_isSheaf
  结论: (skyscraperPresheaf p₀ A).是层
  证明: by
  classical exact
(Presheaf.isSheaf_iso_iff (eqToIso <| skyscraperPresheaf_eq_pushforward p₀ A)).mpr
      (Sheaf.pushforward_sheaf_of_sheaf _
        (Presheaf.isSheaf_on_punit_of_isTerminal _ (by
          dsimp [skyscraperPresheaf]
          rw [if_neg]
          · exact terminalIsTerminal
   

Depends on / 依赖: PUnit.unit, Presheaf, Presheaf.isSheaf_iso_iff, Presheaf.isSheaf_on_punit_of_isTerminal, Previously, Set.notMem_empty, Sheaf.pushforward_sheaf_of_sheaf, adaptation_note, annotation, classical, eqToIso, if_neg, isSheaf_iso_iff, isSheaf_on_punit_of_isTerminal, needed, notMem_empty, pushforward_sheaf_of_sheaf, skyscraperPresheaf, skyscraperPresheaf_eq_pushforward, terminalIsTerminal
-/
theorem skyscraperPresheaf_isSheaf : (skyscraperPresheaf p₀ A).IsSheaf := by
  classical exact
(Presheaf.isSheaf_iso_iff (eqToIso <| skyscraperPresheaf_eq_pushforward p₀ A)).mpr
      (Sheaf.pushforward_sheaf_of_sheaf _
        (Presheaf.isSheaf_on_punit_of_isTerminal _ (by
          dsimp [skyscraperPresheaf]
          rw [if_neg]
          · exact terminalIsTerminal
          · #adaptation_note /-- 2024-03-24
            Previously the universe annotation was not needed here. -/
            exact Set.notMem_empty PUnit.unit.{u + 1})))

/--
The skyscraper presheaf supported at `p₀` with value `A` is the sheaf that assigns `A` to all opens
`U` that contain `p₀` and assigns `*` otherwise.
-/
@[simps!]
/--
Definition of `skyscraperSheaf` / `skyscraperSheaf` 的定义

English:
definition skyscraperSheaf
  signature: : Sheaf C X
  body: ⟨skyscraperPresheaf p₀ A, skyscraperPresheaf_isSheaf _ _⟩

中文:
定义 skyscraperSheaf
  签名: : 层 C X
  定义体: ⟨skyscraperPresheaf p₀ A, skyscraperPresheaf_isSheaf _ _⟩

Depends on / 依赖: skyscraperPresheaf, skyscraperPresheaf_isSheaf
-/
def skyscraperSheaf : Sheaf C X :=
  ⟨skyscraperPresheaf p₀ A, skyscraperPresheaf_isSheaf _ _⟩

/--
Definition of `skyscraperSheafFunctor` / `skyscraperSheafFunctor` 的定义

English:
definition skyscraperSheafFunctor
  signature: : C ⥤ Sheaf C X where
  body: skyscraperSheaf p₀ c
map f := ObjectProperty.homMk (skyscraperPresheafFunctor p₀).map f
map_id _ := Sheaf.hom_ext (skyscraperPresheafFunctor p₀).map_id _
map_comp _ _ := Sheaf.hom_ext (skyscraperPresheafFunctor p₀).map_comp _ _

中文:
定义 skyscraperSheafFunctor
  签名: : C ⥤ 层 C X where
  定义体: skyscraperSheaf p₀ c
map f := ObjectProperty.homMk (skyscraperPresheafFunctor p₀).map f
map_id _ := Sheaf.hom_ext (skyscraperPresheafFunctor p₀).map_id _
map_comp _ _ := Sheaf.hom_ext (skyscraperPresheafFunctor p₀).map_comp _ _

Depends on / 依赖: skyscraperSheaf
-/
def skyscraperSheafFunctor : C ⥤ Sheaf C X where
  obj c := skyscraperSheaf p₀ c
map f := ObjectProperty.homMk (skyscraperPresheafFunctor p₀).map f
map_id _ := Sheaf.hom_ext (skyscraperPresheafFunctor p₀).map_id _
map_comp _ _ := Sheaf.hom_ext (skyscraperPresheafFunctor p₀).map_comp _ _

namespace StalkSkyscraperPresheafAdjunctionAuxs

variable [HasColimits C]

set_option backward.defeqAttrib.useBackward true in
/-- If `f : 𝓕.stalk p₀ ⟶ c`, then a natural transformation `𝓕 ⟶ skyscraperPresheaf p₀ c` can be
defined by: `𝓕.germ p₀ ≫ f : 𝓕(U) ⟶ c` if `p₀ ∈ U` and the unique morphism to a terminal object
if `p₀ ∉ U`.
-/
@[simps]
/--
Definition of `toSkyscraperPresheaf` / `toSkyscraperPresheaf` 的定义

English:
definition toSkyscraperPresheaf
  signature: {𝓕 : Presheaf C X} {c : C} (f : 𝓕.stalk p₀ ⟶ c)
  body: if h : p₀ in U.unop then 𝓕.germ _ p₀ h ≫ f ≫ eqToHom (if_pos h).symm
    else ((if_neg h).symm.ndrec terminalIsTerminal).from _
  naturality U V inc := by
    dsimp
    by_cases hV : p₀ in V.unop
    · have hU : p₀ in U.unop := leOfHom inc.unop hV
      split_ifs
      rw [← Category.assoc]; rw [𝓕.g

中文:
定义 toSkyscraperPresheaf
  签名: {𝓕 : 预层 C X} {c : C} (f : 𝓕.stalk p₀ ⟶ c)
  定义体: if h : p₀ in U.unop then 𝓕.germ _ p₀ h ≫ f ≫ eqToHom (if_pos h).symm
    else ((if_neg h).symm.ndrec terminalIsTerminal).from _
  naturality U V inc := by
    dsimp
    by_cases hV : p₀ in V.unop
    · have hU : p₀ in U.unop := leOfHom inc.unop hV
      split_ifs
      rw [← Category.assoc]; rw [𝓕.g

Depends on / 依赖: Category, Category.assoc, U.unop, V.unop, eqToHom, eqToHom_trans, germ_res, hom_ext, if_neg, if_pos, inc.unop, leOfHom, naturality, split_ifs, symm.ndrec, terminalIsTerminal
-/
def toSkyscraperPresheaf {𝓕 : Presheaf C X} {c : C} (f : 𝓕.stalk p₀ ⟶ c) :
    𝓕 ⟶ skyscraperPresheaf p₀ c where
  app U :=
    if h : p₀ in U.unop then 𝓕.germ _ p₀ h ≫ f ≫ eqToHom (if_pos h).symm
    else ((if_neg h).symm.ndrec terminalIsTerminal).from _
  naturality U V inc := by
    dsimp
    by_cases hV : p₀ in V.unop
    · have hU : p₀ in U.unop := leOfHom inc.unop hV
      split_ifs
      rw [← Category.assoc]; rw [𝓕.germ_res' inc]; rw [Category.assoc]; rw [Category.assoc]; rw [eqToHom_trans]
    · split_ifs
      exact ((if_neg hV).symm.ndrec terminalIsTerminal).hom_ext ..

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `fromStalk` / `fromStalk` 的定义

English:
definition fromStalk
  signature: {𝓕 : Presheaf C X} {c : C} (f : 𝓕 ⟶ skyscraperPresheaf p₀ c)
  body: let χ : Cocone ((OpenNhds.inclusion p₀).op ⋙ 𝓕) :=
Cocone.mk c
      { app := fun U => f.app ((OpenNhds.inclusion p₀).op.obj U) ≫ eqToHom (if_pos U.unop.2)
        naturality := fun U V inc => by
          dsimp only [Functor.const_obj_map, Functor.const_obj_obj, Functor.comp_map,
            Functo

中文:
定义 fromStalk
  签名: {𝓕 : 预层 C X} {c : C} (f : 𝓕 ⟶ skyscraperPresheaf p₀ c)
  定义体: let χ : Cocone ((OpenNhds.inclusion p₀).op ⋙ 𝓕) :=
Cocone.mk c
      { app := fun U => f.app ((OpenNhds.inclusion p₀).op.obj U) ≫ eqToHom (if_pos U.unop.2)
        naturality := fun U V inc => by
          dsimp only [Functor.const_obj_map, Functor.const_obj_obj, Functor.comp_map,
            Functo

Depends on / 依赖: Category, Category.assoc, Category.comp_id, Cocone, Cocone.mk, Functor, Functor.comp_map, Functor.comp_obj, Functor.const_obj_map, Functor.const_obj_obj, Functor.op_obj, OpenNhds, OpenNhds.i, OpenNhds.inclusion, U.unop, comp_eqToHom_iff, comp_id, comp_map, comp_obj, const_obj_map
-/
def fromStalk {𝓕 : Presheaf C X} {c : C} (f : 𝓕 ⟶ skyscraperPresheaf p₀ c) : 𝓕.stalk p₀ ⟶ c :=
  let χ : Cocone ((OpenNhds.inclusion p₀).op ⋙ 𝓕) :=
Cocone.mk c
      { app := fun U => f.app ((OpenNhds.inclusion p₀).op.obj U) ≫ eqToHom (if_pos U.unop.2)
        naturality := fun U V inc => by
          dsimp only [Functor.const_obj_map, Functor.const_obj_obj, Functor.comp_map,
            Functor.comp_obj, Functor.op_obj, skyscraperPresheaf_obj]
          rw [Category.comp_id]; rw [← Category.assoc]; rw [comp_eqToHom_iff]; rw [Category.assoc]; rw [eqToHom_trans]; rw [f.naturality]; rw [skyscraperPresheaf_map]
          have hV : p₀ in (OpenNhds.inclusion p₀).obj V.unop := V.unop.2
          simp only [dif_pos hV] }
  colimit.desc _ χ

@[reassoc (attr := simp)]
/--
lemma `germ_fromStalk` / 引理 `germ_fromStalk`

English:
lemma germ_fromStalk
  given: {𝓕 : Presheaf C X} {c : C} (f : 𝓕 ⟶ skyscraperPresheaf p₀ c) (U) (hU)
  proof: colimit.ι_desc _ _

中文:
引理 germ_fromStalk
  条件: {𝓕 : 预层 C X} {c : C} (f : 𝓕 ⟶ skyscraperPresheaf p₀ c) (U) (hU)
  证明: colimit.ι_desc _ _

Depends on / 依赖: colimit
-/
lemma germ_fromStalk {𝓕 : Presheaf C X} {c : C} (f : 𝓕 ⟶ skyscraperPresheaf p₀ c) (U) (hU) :
    𝓕.germ U p₀ hU ≫ fromStalk p₀ f = f.app (op U) ≫ eqToHom (if_pos hU) :=
  colimit.ι_desc _ _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
theorem `to_skyscraper_fromStalk` / 定理 `to_skyscraper_fromStalk`

English:
theorem to_skyscraper_fromStalk
  given: {𝓕 : Presheaf C X} {c : C} (f : 𝓕 ⟶ skyscraperPresheaf p₀ c)
  proof: by
  apply NatTrans.ext
  ext U
  dsimp
  split_ifs with h
  · simp
  · exact ((if_neg h).symm.ndrec terminalIsTerminal).hom_ext ..

中文:
定理 to_skyscraper_fromStalk
  条件: {𝓕 : 预层 C X} {c : C} (f : 𝓕 ⟶ skyscraperPresheaf p₀ c)
  证明: by
  apply NatTrans.ext
  ext U
  dsimp
  split_ifs with h
  · simp
  · exact ((if_neg h).symm.ndrec terminalIsTerminal).hom_ext ..

Depends on / 依赖: NatTrans, NatTrans.ext, hom_ext, if_neg, split_ifs, symm.ndrec, terminalIsTerminal
-/
theorem to_skyscraper_fromStalk {𝓕 : Presheaf C X} {c : C} (f : 𝓕 ⟶ skyscraperPresheaf p₀ c) :
    toSkyscraperPresheaf p₀ (fromStalk _ f) = f := by
  apply NatTrans.ext
  ext U
  dsimp
  split_ifs with h
  · simp
  · exact ((if_neg h).symm.ndrec terminalIsTerminal).hom_ext ..

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `fromStalk_to_skyscraper` / 定理 `fromStalk_to_skyscraper`

English:
theorem fromStalk_to_skyscraper
  given: {𝓕 : Presheaf C X} {c : C} (f : 𝓕.stalk p₀ ⟶ c)
  proof: by
  refine 𝓕.stalk_hom_ext fun U hxU => ?_
  rw [germ_fromStalk]; rw [toSkyscraperPresheaf_app]; rw [dif_pos hxU]; rw [Category.assoc]; rw [Category.assoc]; rw [eqToHom_trans]; rw [eqToHom_refl]; rw [Category.comp_id]; rw [Presheaf.germ]

中文:
定理 fromStalk_to_skyscraper
  条件: {𝓕 : 预层 C X} {c : C} (f : 𝓕.stalk p₀ ⟶ c)
  证明: by
  refine 𝓕.stalk_hom_ext fun U hxU => ?_
  rw [germ_fromStalk]; rw [toSkyscraperPresheaf_app]; rw [dif_pos hxU]; rw [Category.assoc]; rw [Category.assoc]; rw [eqToHom_trans]; rw [eqToHom_refl]; rw [Category.comp_id]; rw [Presheaf.germ]

Depends on / 依赖: Category, Category.assoc, Category.comp_id, Presheaf, Presheaf.germ, comp_id, dif_pos, eqToHom_refl, eqToHom_trans, germ_fromStalk, stalk_hom_ext, toSkyscraperPresheaf_app
-/
theorem fromStalk_to_skyscraper {𝓕 : Presheaf C X} {c : C} (f : 𝓕.stalk p₀ ⟶ c) :
    fromStalk p₀ (toSkyscraperPresheaf _ f) = f := by
  refine 𝓕.stalk_hom_ext fun U hxU => ?_
  rw [germ_fromStalk]; rw [toSkyscraperPresheaf_app]; rw [dif_pos hxU]; rw [Category.assoc]; rw [Category.assoc]; rw [eqToHom_trans]; rw [eqToHom_refl]; rw [Category.comp_id]; rw [Presheaf.germ]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The unit in `Presheaf.stalkFunctor ⊣ skyscraperPresheafFunctor`
-/
@[simps]
/--
Definition of `unit` / `unit` 的定义

English:
definition unit
  signature: :
  body: toSkyscraperPresheaf _ 𝟙 _
  naturality 𝓕 𝓖 f := by
    ext U; dsimp
    split_ifs with h
    · simp only [Category.id_comp, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
        Presheaf.stalkFunctor_map_germ_assoc, Presheaf.stalkFunctor_obj]
    · apply ((if_neg h).symm.ndrec terminalIsTermin

中文:
定义 unit
  签名: :
  定义体: toSkyscraperPresheaf _ 𝟙 _
  naturality 𝓕 𝓖 f := by
    ext U; dsimp
    split_ifs with h
    · simp only [Category.id_comp, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
        Presheaf.stalkFunctor_map_germ_assoc, Presheaf.stalkFunctor_obj]
    · apply ((if_neg h).symm.ndrec terminalIsTermin
-/
protected def unit :
    𝟭 (Presheaf C X) ⟶ Presheaf.stalkFunctor C p₀ ⋙ skyscraperPresheafFunctor p₀ where
app _ := toSkyscraperPresheaf _ 𝟙 _
  naturality 𝓕 𝓖 f := by
    ext U; dsimp
    split_ifs with h
    · simp only [Category.id_comp, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
        Presheaf.stalkFunctor_map_germ_assoc, Presheaf.stalkFunctor_obj]
    · apply ((if_neg h).symm.ndrec terminalIsTerminal).hom_ext

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The counit in `Presheaf.stalkFunctor ⊣ skyscraperPresheafFunctor`
-/
@[simps]
/--
Definition of `counit` / `counit` 的定义

English:
definition counit
  signature: :
  body: (skyscraperPresheafStalkOfSpecializes p₀ c specializes_rfl).hom
  naturality x y f := TopCat.Presheaf.stalk_hom_ext _ fun U hxU => by simp [hxU]

中文:
定义 counit
  签名: :
  定义体: (skyscraperPresheafStalkOfSpecializes p₀ c specializes_rfl).hom
  naturality x y f := TopCat.Presheaf.stalk_hom_ext _ fun U hxU => by simp [hxU]
-/
protected def counit :
    skyscraperPresheafFunctor p₀ ⋙ (Presheaf.stalkFunctor C p₀ : Presheaf C X ⥤ C) ⟶ 𝟭 C where
  app c := (skyscraperPresheafStalkOfSpecializes p₀ c specializes_rfl).hom
  naturality x y f := TopCat.Presheaf.stalk_hom_ext _ fun U hxU => by simp [hxU]

end StalkSkyscraperPresheafAdjunctionAuxs

section

open StalkSkyscraperPresheafAdjunctionAuxs

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `skyscraperPresheafStalkAdjunction` / `skyscraperPresheafStalkAdjunction` 的定义

English:
definition skyscraperPresheafStalkAdjunction
  signature: [HasColimits C]
  body: StalkSkyscraperPresheafAdjunctionAuxs.unit _
  counit := StalkSkyscraperPresheafAdjunctionAuxs.counit _
  left_triangle_components X := by
    dsimp [Presheaf.stalkFunctor, toSkyscraperPresheaf]
    ext
    simp only [Functor.comp_obj, Functor.op_obj, ι_colimMap_assoc, skyscraperPresheaf_obj,
      

中文:
定义 skyscraperPresheafStalkAdjunction
  签名: [有余极限 C]
  定义体: StalkSkyscraperPresheafAdjunctionAuxs.unit _
  counit := StalkSkyscraperPresheafAdjunctionAuxs.counit _
  left_triangle_components X := by
    dsimp [Presheaf.stalkFunctor, toSkyscraperPresheaf]
    ext
    simp only [Functor.comp_obj, Functor.op_obj, ι_colimMap_assoc, skyscraperPresheaf_obj,
      

Depends on / 依赖: StalkSkyscraperPresheafAdjunctionAuxs, StalkSkyscraperPresheafAdjunctionAuxs.unit
-/
def skyscraperPresheafStalkAdjunction [HasColimits C] :
    (Presheaf.stalkFunctor C p₀ : Presheaf C X ⥤ C) ⊣ skyscraperPresheafFunctor p₀ where
  unit := StalkSkyscraperPresheafAdjunctionAuxs.unit _
  counit := StalkSkyscraperPresheafAdjunctionAuxs.counit _
  left_triangle_components X := by
    dsimp [Presheaf.stalkFunctor, toSkyscraperPresheaf]
    ext
    simp only [Functor.comp_obj, Functor.op_obj, ι_colimMap_assoc, skyscraperPresheaf_obj,
      Functor.whiskerLeft_app, Category.comp_id]
    split_ifs with h
    · simp [skyscraperPresheafStalkOfSpecializes]
      rfl
    · simp only [skyscraperPresheafStalkOfSpecializes, colimit.isoColimitCocone_ι_hom,
        skyscraperPresheafCoconeOfSpecializes_pt, skyscraperPresheafCoconeOfSpecializes_ι_app,
        Functor.comp_obj, Functor.op_obj, skyscraperPresheaf_obj, Functor.const_obj_obj]
      rw [comp_eqToHom_iff]
      apply ((if_neg h).symm.ndrec terminalIsTerminal).hom_ext
  right_triangle_components Y := by
    ext
    simp only [skyscraperPresheafFunctor_obj, Functor.id_obj, skyscraperPresheaf_obj,
      Presheaf.stalkFunctor_obj, unit_app, counit_app,
      skyscraperPresheafStalkOfSpecializes, skyscraperPresheafFunctor_map, Presheaf.comp_app,
      toSkyscraperPresheaf_app, Category.id_comp, SkyscraperPresheafFunctor.map'_app]
    split_ifs with h
    · simp [Presheaf.germ]
      rfl
    · simp
      rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasColimits
  signature: C] : (skyscraperPresheafFunctor p₀
  body: (skyscraperPresheafStalkAdjunction _).isRightAdjoint

中文:
实例 [有余极限
  签名: C] : (skyscraperPresheafFunctor p₀
  定义体: (skyscraperPresheafStalkAdjunction _).isRightAdjoint

Depends on / 依赖: isRightAdjoint, skyscraperPresheafStalkAdjunction
-/
instance [HasColimits C] : (skyscraperPresheafFunctor p₀ : C ⥤ Presheaf C X).IsRightAdjoint :=
  (skyscraperPresheafStalkAdjunction _).isRightAdjoint

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasColimits
  signature: C] : (Presheaf.stalkFunctor C p₀).IsLeftAdjoint
  body: -- Use a classical instance instead of the one from `variable`s
  have : forall U : Opens X, Decidable (p₀ in U) := fun _ => Classical.dec _
  (skyscraperPresheafStalkAdjunction _).isLeftAdjoint

中文:
实例 [有余极限
  签名: C] : (预层.stalkFunctor C p₀).是左伴随
  定义体: -- Use a classical instance instead of the one from `variable`s
  have : forall U : Opens X, Decidable (p₀ in U) := fun _ => Classical.dec _
  (skyscraperPresheafStalkAdjunction _).isLeftAdjoint
-/
instance [HasColimits C] : (Presheaf.stalkFunctor C p₀).IsLeftAdjoint :=
  -- Use a classical instance instead of the one from `variable`s
  have : forall U : Opens X, Decidable (p₀ in U) := fun _ => Classical.dec _
  (skyscraperPresheafStalkAdjunction _).isLeftAdjoint

/--
Definition of `stalkSkyscraperSheafAdjunction` / `stalkSkyscraperSheafAdjunction` 的定义

English:
definition stalkSkyscraperSheafAdjunction
  signature: [HasColimits C]
  body: { app := fun 𝓕 => ⟨(StalkSkyscraperPresheafAdjunctionAuxs.unit p₀).app 𝓕.1⟩
naturality := fun 𝓐 𝓑 f => Sheaf.hom_ext by
        apply (StalkSkyscraperPresheafAdjunctionAuxs.unit p₀).naturality }
  counit := StalkSkyscraperPresheafAdjunctionAuxs.counit p₀
  left_triangle_components X :=
    ((skyscra

中文:
定义 stalkSkyscraperSheafAdjunction
  签名: [有余极限 C]
  定义体: { app := fun 𝓕 => ⟨(StalkSkyscraperPresheafAdjunctionAuxs.unit p₀).app 𝓕.1⟩
naturality := fun 𝓐 𝓑 f => Sheaf.hom_ext by
        apply (StalkSkyscraperPresheafAdjunctionAuxs.unit p₀).naturality }
  counit := StalkSkyscraperPresheafAdjunctionAuxs.counit p₀
  left_triangle_components X :=
    ((skyscra

Depends on / 依赖: Sheaf.hom_ext, StalkSkyscraperPresheafAdjunctionAuxs, StalkSkyscraperPresheafAdjunctionAuxs.counit, StalkSkyscraperPresheafAdjunctionAuxs.unit, X.obj, counit, hom_ext, left_triangle_components, naturality, right_triangle_components, skyscraperPresheafStalkAdjunction
-/
def stalkSkyscraperSheafAdjunction [HasColimits C] :
    Sheaf.forget C X ⋙ Presheaf.stalkFunctor _ p₀ ⊣ skyscraperSheafFunctor p₀ where
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): `ext1` is changed to `Sheaf.Hom.ext`,
  unit :=
    { app := fun 𝓕 => ⟨(StalkSkyscraperPresheafAdjunctionAuxs.unit p₀).app 𝓕.1⟩
naturality := fun 𝓐 𝓑 f => Sheaf.hom_ext by
        apply (StalkSkyscraperPresheafAdjunctionAuxs.unit p₀).naturality }
  counit := StalkSkyscraperPresheafAdjunctionAuxs.counit p₀
  left_triangle_components X :=
    ((skyscraperPresheafStalkAdjunction p₀).left_triangle_components X.obj)
  right_triangle_components _ :=
    Sheaf.hom_ext ((skyscraperPresheafStalkAdjunction p₀).right_triangle_components _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasColimits
  signature: C] : (Sheaf.forget C X ⋙ Presheaf.stalkFunctor C p₀).IsLeftAdjoint
  body: have : forall U : Opens X, Decidable (p₀ in U) := fun _ => Classical.dec _
  (stalkSkyscraperSheafAdjunction p₀).isLeftAdjoint

中文:
实例 [有余极限
  签名: C] : (层.forget C X ⋙ 预层.stalkFunctor C p₀).是左伴随
  定义体: have : forall U : Opens X, Decidable (p₀ in U) := fun _ => Classical.dec _
  (stalkSkyscraperSheafAdjunction p₀).isLeftAdjoint

Depends on / 依赖: Classical, Classical.dec, Decidable, isLeftAdjoint, stalkSkyscraperSheafAdjunction
-/
instance [HasColimits C] : (Sheaf.forget C X ⋙ Presheaf.stalkFunctor C p₀).IsLeftAdjoint :=
  have : forall U : Opens X, Decidable (p₀ in U) := fun _ => Classical.dec _
  (stalkSkyscraperSheafAdjunction p₀).isLeftAdjoint

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasColimits
  signature: C] : (skyscraperSheafFunctor p₀
  body: (stalkSkyscraperSheafAdjunction _).isRightAdjoint

中文:
实例 [有余极限
  签名: C] : (skyscraperSheafFunctor p₀
  定义体: (stalkSkyscraperSheafAdjunction _).isRightAdjoint

Depends on / 依赖: isRightAdjoint, stalkSkyscraperSheafAdjunction
-/
instance [HasColimits C] : (skyscraperSheafFunctor p₀ : C ⥤ Sheaf C X).IsRightAdjoint :=
  (stalkSkyscraperSheafAdjunction _).isRightAdjoint

/--
Definition of `skyscraperSheafForgetAdjunction` / `skyscraperSheafForgetAdjunction` 的定义

English:
definition skyscraperSheafForgetAdjunction
  signature: [HasColimits C]
  body: skyscraperPresheafStalkAdjunction p₀

中文:
定义 skyscraperSheafForgetAdjunction
  签名: [有余极限 C]
  定义体: skyscraperPresheafStalkAdjunction p₀

Depends on / 依赖: skyscraperPresheafStalkAdjunction
-/
noncomputable def skyscraperSheafForgetAdjunction [HasColimits C] :
    Presheaf.stalkFunctor C p₀ ⊣ skyscraperSheafFunctor p₀ ⋙ Sheaf.forget C X :=
  skyscraperPresheafStalkAdjunction p₀

set_option backward.defeqAttrib.useBackward true in
variable {A p₀} in
/--
On an open set not containing `p₀`, the value of skyscraper sheaf supported at `p₀` is a terminal
object.
-/
noncomputable
/--
Definition of `isTerminalSkyscraperSheafObjObjOfNotMem` / `isTerminalSkyscraperSheafObjObjOfNotMem` 的定义

English:
definition isTerminalSkyscraperSheafObjObjOfNotMem
  signature: {U : (Opens X)ᵒᵖ} (h : p₀ ∉ unop U)
  body: by
  dsimp
  rw [if_neg h]
  exact terminalIsTerminal

中文:
定义 isTerminalSkyscraperSheafObjObjOfNotMem
  签名: {U : (Opens X)ᵒᵖ} (h : p₀ ∉ unop U)
  定义体: by
  dsimp
  rw [if_neg h]
  exact terminalIsTerminal

Depends on / 依赖: if_neg, terminalIsTerminal
-/
def isTerminalSkyscraperSheafObjObjOfNotMem {U : (Opens X)ᵒᵖ} (h : p₀ ∉ unop U) :
    IsTerminal ((skyscraperSheaf p₀ A).obj.obj U) := by
  dsimp
  rw [if_neg h]
  exact terminalIsTerminal

end

end
