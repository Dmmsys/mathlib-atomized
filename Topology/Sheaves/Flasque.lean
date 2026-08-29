/-
Copyright (c) 2026 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent
-/

module

public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.Topology.Sheaves.AddCommGrpCat
public import Mathlib.Topology.Sheaves.LocallySurjective

/-!
# Flasque Sheaves

We define and prove basic properties about flasque sheaves on topological spaces.

## Main definition

* `TopCat.Sheaf.IsFlasque`: A sheaf is flasque if all of the restriction morphisms are epimorphisms.

## Main results

* `TopCat.Sheaf.IsFlasque.epi_of_shortExact`: Given a short exact sequence of sheaves,
  `0 ⟶ 𝓕 ⟶ 𝓖 ⟶ 𝓗 ⟶ 0`, if `𝓕` is flasque then `𝓖(U) ⟶ 𝓗(U)` is surjective, for any open `U`.

* `TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂ `: Given a short exact sequence of
  sheaves, `0 ⟶ 𝓕 ⟶ 𝓖 ⟶ 𝓗 ⟶ 0`, if `𝓕` and `𝓖` are flasque, then `𝓗` is flasque.

-/

public section

universe u v w

open TopCat TopologicalSpace Opposite CategoryTheory Presheaf Limits
open scoped AlgebraicGeometry

variable {X : TopCat.{u}}

namespace TopCat

namespace Presheaf

variable {C : Type v} [Category.{w} C] (F : Presheaf C X)

/--
Definition of `IsFlasque` / `IsFlasque` 的定义

English:
class IsFlasque
  parameters: : Prop where
  axioms and operations (1):
    - epi : forall {U V : (Opens X)ᵒᵖ} (i : U ⟶ V), Epi (F.map i)

中文:
类 IsFlasque
  参数: : 命题 where
  公理与运算 (1 个):
    - epi : 对任意 {U V : (Opens X)ᵒᵖ} (i : U ⟶ V), Epi (F.map i)
-/
class IsFlasque : Prop where
  epi : forall {U V : (Opens X)ᵒᵖ} (i : U ⟶ V), Epi (F.map i)

namespace IsFlasque

attribute [instance low] IsFlasque.epi

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Instance `pushforward_isFlasque` / 实例 `pushforward_isFlasque`

English:
instance pushforward_isFlasque
  signature: {Y : TopCat.{u}} [IsFlasque F] (f : X ⟶ Y)
  body: by
    simp only [pushforward_obj_obj, pushforward_obj_map]
    infer_instance

中文:
实例 pushforward_isFlasque
  签名: {Y : TopCat.{u}} [IsFlasque F] (f : X ⟶ Y)
  定义体: by
    simp only [pushforward_obj_obj, pushforward_obj_map]
    infer_instance

Depends on / 依赖: infer_instance, pushforward_obj_map, pushforward_obj_obj
-/
instance pushforward_isFlasque {Y : TopCat.{u}} [IsFlasque F] (f : X ⟶ Y) :
    IsFlasque (f _* F) where
  epi {U V} i := by
    simp only [pushforward_obj_obj, pushforward_obj_map]
    infer_instance

end IsFlasque

end Presheaf

namespace Sheaf

/--
Definition of `IsFlasque` / `IsFlasque` 的定义

English:
abbreviation IsFlasque
  signature: {C : Type v} [Category.{w} C] (F : Sheaf C X)
  body: Presheaf.IsFlasque F.obj

中文:
缩写 IsFlasque
  签名: {C : 类型v} [Category.{w} C] (F : Sheaf C X)
  定义体: Presheaf.IsFlasque F.obj

Depends on / 依赖: F.obj, IsFlasque, Presheaf, Presheaf.IsFlasque
-/
abbrev IsFlasque {C : Type v} [Category.{w} C] (F : Sheaf C X) := Presheaf.IsFlasque F.obj

namespace IsFlasque

/--
Instance `pushforward_isFlasque` / 实例 `pushforward_isFlasque`

English:
instance pushforward_isFlasque
  signature: {C : Type v} [Category.{w} C] {Y : TopCat.{u}} (F : Sheaf C X)
  body: Presheaf.IsFlasque.pushforward_isFlasque F.1 f

中文:
实例 pushforward_isFlasque
  签名: {C : 类型v} [Category.{w} C] {Y : TopCat.{u}} (F : Sheaf C X)
  定义体: Presheaf.IsFlasque.pushforward_isFlasque F.1 f

Depends on / 依赖: IsFlasque, Presheaf, Presheaf.IsFlasque.pushforward_isFlasque, pushforward_isFlasque
-/
instance pushforward_isFlasque {C : Type v} [Category.{w} C] {Y : TopCat.{u}} (F : Sheaf C X)
    [IsFlasque F] (f : X ⟶ Y) : IsFlasque ((pushforward C f).obj F) :=
  Presheaf.IsFlasque.pushforward_isFlasque F.1 f

variable {U : Opens X} {F G : Sheaf AddCommGrpCat X} (g : F ⟶ G) (s : G.obj.obj (op U))

/--
Definition of `Under` / `Under` 的定义

English:
abbreviation Under
  body: StructuredArrow ⟨op U, s⟩ (Functor.whiskerRight g.hom
  (CategoryTheory.forget AddCommGrpCat.{u})).mapElements

中文:
缩写 Under
  定义体: StructuredArrow ⟨op U, s⟩ (Functor.whiskerRight g.hom
  (CategoryTheory.forget AddCommGrpCat.{u})).mapElements

Depends on / 依赖: Functor, Functor.whiskerRight, StructuredArrow, g.hom, whiskerRight
-/
abbrev Under := StructuredArrow ⟨op U, s⟩ (Functor.whiskerRight g.hom
  (CategoryTheory.forget AddCommGrpCat.{u})).mapElements

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `structured_arrows_elements_sheaf_chains_bounded` / 引理 `structured_arrows_elements_sheaf_chains_bounded`

English:
lemma structured_arrows_elements_sheaf_chains_bounded
  statement: (c : Set (Under g s))
  proof: by
  let f : c -> (Opens X) := fun x => x.1.right.1.unop
  obtain ⟨t, ht, _⟩ : exists! s_1, IsGluing F.obj f (fun x => x.val.right.2) s_1 := by
    refine Sheaf.existsUnique_gluing F _ _ (fun i j => ?_)
    obtain (rfl | h₁ | h₁) : i = j ∨ Nonempty (i.val ⟶ j.val) ∨ Nonempty (j.val ⟶ i.val) := by
  

中文:
引理 structured_arrows_elements_sheaf_chains_bounded
  结论: (c : Set (Under g s))
  证明: by
  let f : c -> (Opens X) := fun x => x.1.right.1.unop
  obtain ⟨t, ht, _⟩ : exists! s_1, IsGluing F.obj f (fun x => x.val.right.2) s_1 := by
    refine Sheaf.existsUnique_gluing F _ _ (fun i j => ?_)
    obtain (rfl | h₁ | h₁) : i = j ∨ Nonempty (i.val ⟶ j.val) ∨ Nonempty (j.val ⟶ i.val) := by
  

Depends on / 依赖: CategoryOfElements, CategoryOfElements.map_snd, F.obj, Functor, Functor.map_comp_apply, IsGluing, Nonempty, Sheaf.existsUnique_gluing, Subtype, Subtype.ext_iff, all_goals, existsUnique_gluing, ext_iff, i.property, i.val, iSup_le, j.property, j.val, leOfHom, map_comp_apply
-/
lemma structured_arrows_elements_sheaf_chains_bounded (c : Set (Under g s))
    (h : IsChain (fun x y => Nonempty (y ⟶ x)) c) : exists ub, forall a in c, Nonempty (ub ⟶ a) := by
  let f : c -> (Opens X) := fun x => x.1.right.1.unop
  obtain ⟨t, ht, _⟩ : exists! s_1, IsGluing F.obj f (fun x => x.val.right.2) s_1 := by
    refine Sheaf.existsUnique_gluing F _ _ (fun i j => ?_)
    obtain (rfl | h₁ | h₁) : i = j ∨ Nonempty (i.val ⟶ j.val) ∨ Nonempty (j.val ⟶ i.val) := by
      grind [Subtype.ext_iff, h i.property j.property]
    · rfl
    all_goals
      rw [← CategoryOfElements.map_snd h₁.some.2]
      dsimp
      rw [← Functor.map_comp_apply]
      rfl
have le₁ : iSup f <= U := iSup_le fun j => leOfHom j.1.hom.1.unop
  have le₂ : forall i, i in c -> unop i.right.1 <= iSup f := fun i hi => le_iSup f ⟨i, hi⟩
  use StructuredArrow.mk (CategoryOfElements.homMk _ _ (homOfLE le₁).op (eq_app_of_locally_eq ht
      (fun i => leOfHom i.1.hom.1.unop) (fun i => (CategoryOfElements.map_snd i.1.hom).symm)).symm :
      ⟨op U, s⟩ ⟶ (Functor.whiskerRight g.hom
      (CategoryTheory.forget AddCommGrpCat)).mapElements.obj ⟨op (iSup f), t⟩)
  exact fun i hi => Nonempty.intro (StructuredArrow.homMk (CategoryOfElements.homMk _ _
    (homOfLE (le₂ i hi)).op (ht ⟨i, hi⟩)) (by cat_disch))

set_option backward.isDefEq.respectTransparency false in
/--
theorem `epi_of_shortExact` / 定理 `epi_of_shortExact`

English:
theorem epi_of_shortExact
  statement: {S : ShortComplex (Sheaf AddCommGrpCat X)} (hS : S.ShortExact)
  proof: by
  refine (AddCommGrpCat.epi_iff_surjective _).mpr (fun s => ?_)
  -- We want to find a preimage of `s` by `S.g`.
  -- We apply Zorn's lemma to obtain a term `t` of `Under S.g s` that is maximal.
  obtain ⟨t, ht⟩ := exists_maximal_of_chains_bounded
    (structured_arrows_elements_sheaf_chains_boun

中文:
定理 epi_of_shortExact
  结论: {S : ShortComplex (Sheaf AddCommGrpCat X)} (hS : S.ShortExact)
  证明: by
  refine (AddCommGrpCat.epi_iff_surjective _).mpr (fun s => ?_)
  -- We want to find a preimage of `s` by `S.g`.
  -- We apply Zorn's lemma to obtain a term `t` of `Under S.g s` that is maximal.
  obtain ⟨t, ht⟩ := exists_maximal_of_chains_bounded
    (structured_arrows_elements_sheaf_chains_boun

Depends on / 依赖: AddCommGrpCat, AddCommGrpCat.epi_iff_surjective, epi_iff_surjective
-/
theorem epi_of_shortExact {S : ShortComplex (Sheaf AddCommGrpCat X)} (hS : S.ShortExact)
    [IsFlasque S.X₁] : Epi (S.g.1.app (op U)) := by
  refine (AddCommGrpCat.epi_iff_surjective _).mpr (fun s => ?_)
  -- We want to find a preimage of `s` by `S.g`.
  -- We apply Zorn's lemma to obtain a term `t` of `Under S.g s` that is maximal.
  obtain ⟨t, ht⟩ := exists_maximal_of_chains_bounded
    (structured_arrows_elements_sheaf_chains_bounded S.g s)
    (fun ⟨f⟩ ⟨g⟩ => ⟨g ≫ f⟩)
  have tle : t.right.1.unop <= U := leOfHom t.hom.1.unop
  have tcomp : s |_ t.right.1.unop = S.g.hom.app t.right.1 t.right.2 :=
      CategoryOfElements.map_snd t.hom
  -- We get a section `t.right.2` of `S.g` defined on an open subset `t.right.1.unop` of `U`,
  -- that is sent to the restriction of `s` by `S.g`.
  have : U <= t.right.1.unop := by
  -- Prove that the set of definition of `t.right.2` contains `U`.
    intro x hx
    have := (isLocallySurjective_iff_epi S.g).mpr hS.epi_g
    -- We use local surjectivity to find a section `t₁` of `S.X₂` on a neighborhood `W` of `x`
    -- that maps to `s |_ W` by `S.g`.
    obtain ⟨W, Wle, ⟨t₁, ht₁⟩, hW⟩ := (isLocallySurjective_iff S.g.hom).mp this U s x hx
    --`t.right.2` and `t₁` need not agree on their overlap so we need to deal with their
    -- difference `t₂`
    let t₂ := t.right.2 |_ (t.right.1.unop ⊓ W) - t₁ |_ (t.right.1.unop ⊓ W)
    have : (S.g.hom.app (op (t.right.1.unop ⊓ W))) t₂ = 0 := by
      simp [map_restrict, ← tcomp, restrict_restrict, ht₁, t₂]
    -- Since `S` is exact and `t₂` maps to zero, we can lift it to a section `t₃` of `S.X₁`
    obtain ⟨t₃, ht₃⟩ := Sheaf.sections_exact_of_left_exact hS.1 hS.2 t₂ this
    -- Using that `S.X₁` is flasque, we can lift `t₃` to a section on `W`.
    obtain ⟨t₄, (ht₄ : t₄ |_ (t.right.1.unop ⊓ W) = t₃)⟩ := (AddCommGrpCat.epi_iff_surjective
      (S.X₁.obj.map (homOfLE inf_le_right).op)).mp inferInstance t₃
    let f : Fin 2 -> Opens X := ![t.right.1.unop, W]
    let sf : (i : Fin 2) -> S.X₂.obj.obj (op (f i))
    | 0 => t.right.2
    | 1 => t₁ + (S.f.hom.app (op W)) t₄
    have : sf 0 |_ (t.right.1.unop ⊓ W) = sf 1 |_ (t.right.1.unop ⊓ W) := by
      dsimp [sf, f]
      simp only [restrict_sum, ← map_restrict, ht₄, ht₃, t₂, add_sub_cancel]
    -- We glue `t.right.2` and `t₁ + (S.f.hom.app (op W)) t₄` together to form `t₅`
    obtain ⟨t₅, ht₅, _⟩ : exists! t₅, IsGluing S.X₂.obj f sf t₅ := by
      apply Sheaf.existsUnique_gluing
      simp only [IsCompatible, Fin.forall_fin_two]
      refine ⟨⟨rfl, this⟩, Eq.symm ?_, rfl⟩
      apply_fun (fun s => restrictOpen s (W ⊓ t.right.1.unop) (le_of_eq (inf_comm _ _))) at this
      rw [restrict_restrict]; rw [restrict_restrict] at this
      exact this
    have le : iSup f <= U := iSup_le_iff.mpr (Fin.forall_fin_two.mpr ⟨tle, Wle⟩)
    -- We upgrade `t₅` to an object in `Under S.g s` that is defined on `t.right.1.unop ⊔ W`.
    let t₆ : Under S.g s :=
      StructuredArrow.mk (S := ⟨op U, s⟩)
        (T := (Functor.whiskerRight S.g.hom (CategoryTheory.forget AddCommGrpCat)).mapElements)
(Y := ⟨op (iSup f), t₅⟩) CategoryOfElements.homMk _ _ (homOfLE le).op (by
          refine (eq_app_of_locally_eq ht₅ (by rw [Fin.forall_fin_two]; exact ⟨tle, Wle⟩) ?_).symm
          rw [Fin.forall_fin_two]
          refine ⟨tcomp.symm, ?_⟩
          simp only [Fin.isValue, map_add, homOfLE_leOfHom, sf, f]
          have : (S.f.hom.app (op W) ≫ S.g.hom.app (op W)) = 0 := by
            rw [← NatTrans.comp_app]; rw [← ObjectProperty.FullSubcategory.comp_hom]; rw [S.zero]
            rfl
          simp [← CategoryTheory.comp_apply, this, ht₁]
          rfl)
    -- We prove that `t₆` is bigger than `t` for the preorder used on `Under S.g s`.
    have : Nonempty (t₆ ⟶ t) := Nonempty.intro (StructuredArrow.homMk (CategoryOfElements.homMk _ _
      (homOfLE (le_iSup f 0)).op (ht₅ 0)) (by cat_disch))
    exact leOfHom ((ht t₆) this).some.right.1.unop ((le_iSup f 1) hW)
  exact ⟨t.right.2 |_ U, by simp [map_restrict, ← tcomp, restrict_restrict]⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `of_shortExact_of_isFlasque₁₂` / 定理 `of_shortExact_of_isFlasque₁₂`

English:
theorem of_shortExact_of_isFlasque₁₂
  statement: {S : ShortComplex (Sheaf AddCommGrpCat X)}
  proof: by
    have : Epi (S.g.1.app U ≫ S.X₃.obj.map i) := by
      rw [← S.g.hom.naturality i]
      exact CategoryTheory.epi_comp' inferInstance (epi_of_shortExact hS)
    exact CategoryTheory.epi_of_epi (S.g.1.app U) (S.X₃.obj.map i)

中文:
定理 of_shortExact_of_isFlasque₁₂
  结论: {S : ShortComplex (Sheaf AddCommGrpCat X)}
  证明: by
    have : Epi (S.g.1.app U ≫ S.X₃.obj.map i) := by
      rw [← S.g.hom.naturality i]
      exact CategoryTheory.epi_comp' inferInstance (epi_of_shortExact hS)
    exact CategoryTheory.epi_of_epi (S.g.1.app U) (S.X₃.obj.map i)

Depends on / 依赖: CategoryTheory, CategoryTheory.epi_comp, CategoryTheory.epi_of_epi, S.g.hom.naturality, epi_comp, epi_of_epi, epi_of_shortExact, naturality, obj.map
-/
theorem of_shortExact_of_isFlasque₁₂ {S : ShortComplex (Sheaf AddCommGrpCat X)}
    (hS : S.ShortExact) [IsFlasque S.X₁] [IsFlasque S.X₂] : IsFlasque S.X₃ where
  epi {U V} i := by
    have : Epi (S.g.1.app U ≫ S.X₃.obj.map i) := by
      rw [← S.g.hom.naturality i]
      exact CategoryTheory.epi_comp' inferInstance (epi_of_shortExact hS)
    exact CategoryTheory.epi_of_epi (S.g.1.app U) (S.X₃.obj.map i)

end TopCat.Sheaf.IsFlasque

set_option backward.defeqAttrib.useBackward true in
/--
theorem `isFlasque_skyscraperSheaf_of_epi_from` / 定理 `isFlasque_skyscraperSheaf_of_epi_from`

English:
theorem isFlasque_skyscraperSheaf_of_epi_from
  statement: {X : TopCat} (p₀ : ↑X)
  proof: by
    by_cases h1 : p₀ in unop U
    · by_cases h2 : p₀ in unop V
      · simp_all only [skyscraperSheaf_obj_obj, skyscraperSheaf_obj_map, ↓reduceDIte]
        infer_instance
      · simp
        grind
    · have h2 : p₀ ∉ unop V := fun hV => h1 (r.unop.le hV)
      have := isIso_of_isTerminal (isT

中文:
定理 isFlasque_skyscraperSheaf_of_epi_from
  结论: {X : TopCat} (p₀ : ↑X)
  证明: by
    by_cases h1 : p₀ in unop U
    · by_cases h2 : p₀ in unop V
      · simp_all only [skyscraperSheaf_obj_obj, skyscraperSheaf_obj_map, ↓reduceDIte]
        infer_instance
      · simp
        grind
    · have h2 : p₀ ∉ unop V := fun hV => h1 (r.unop.le hV)
      have := isIso_of_isTerminal (isT

Depends on / 依赖: infer_instance, isIso_of_isTerminal, isTerminalSkyscraperSheafObjObjOfNotMem, obj.map, r.unop.le, reduceDIte, skyscraperSheaf, skyscraperSheaf_obj_map, skyscraperSheaf_obj_obj
-/
theorem isFlasque_skyscraperSheaf_of_epi_from {X : TopCat} (p₀ : ↑X)
    [(U : Opens ↑X) -> Decidable (p₀ in U)] {C : Type*} [Category* C] (A : C) [HasTerminal C]
    [Epi <| terminalIsTerminal.from A] :
    (skyscraperSheaf p₀ A).IsFlasque where
  epi {U V} r := by
    by_cases h1 : p₀ in unop U
    · by_cases h2 : p₀ in unop V
      · simp_all only [skyscraperSheaf_obj_obj, skyscraperSheaf_obj_map, ↓reduceDIte]
        infer_instance
      · simp
        grind
    · have h2 : p₀ ∉ unop V := fun hV => h1 (r.unop.le hV)
      have := isIso_of_isTerminal (isTerminalSkyscraperSheafObjObjOfNotMem h1)
        (isTerminalSkyscraperSheafObjObjOfNotMem h2) ((skyscraperSheaf p₀ A).obj.map r)
      infer_instance

/--
theorem `isFlasque_skyscraperSheaf_of_hasZeroObject` / 定理 `isFlasque_skyscraperSheaf_of_hasZeroObject`

English:
theorem isFlasque_skyscraperSheaf_of_hasZeroObject
  statement: {X : TopCat} (p₀ : ↑X)
  proof: isFlasque_skyscraperSheaf_of_epi_from p₀ A

中文:
定理 isFlasque_skyscraperSheaf_of_hasZeroObject
  结论: {X : TopCat} (p₀ : ↑X)
  证明: isFlasque_skyscraperSheaf_of_epi_from p₀ A

Depends on / 依赖: isFlasque_skyscraperSheaf_of_epi_from
-/
theorem isFlasque_skyscraperSheaf_of_hasZeroObject {X : TopCat} (p₀ : ↑X)
    [(U : Opens ↑X) -> Decidable (p₀ in U)] {C : Type*} [Category* C] (A : C) [HasZeroObject C] :
    (skyscraperSheaf p₀ A).IsFlasque := isFlasque_skyscraperSheaf_of_epi_from p₀ A
