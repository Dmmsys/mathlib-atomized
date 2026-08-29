/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Types.Coproducts

/-!
# `sigmaConst.obj` preserves colimits

Given an object `R` in a category `C` with coproducts of size `w`,
the functor `sigmaConst.obj R : Type w ⥤ C` which sends
a type `T` to the coproduct of copies of `R` indexed by `T`
preserves all colimits.

-/

@[expose] public section

universe w v' v u' u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasCoproducts.{w}
  signature: C] (R
  body: ⟨fun {K} => ⟨fun {c} hc => ⟨by
    replace hc := (Types.isColimit_iff_coconeTypesIsColimit ..).1 ⟨hc⟩
    let coconeTypes (s : Cocone (K ⋙ sigmaConst.obj R)) : K.CoconeTypes :=
      { pt := R ⟶ s.pt
        ι j k := Sigma.ι (fun _ => R) k ≫ s.ι.app j
        ι_naturality g := by ext; simp [← s.w g] }
    exact {
      desc s := Sigma.desc (hc.desc (coconeTypes s))
      fac s j := by
        dsimp
        ext k
        simp [dsimp% hc.fac_apply, dsimp% Sigma.ι_desc (hc.desc (coconeTypes s)), coconeTypes]
      uniq s m hm := by
        dsimp
        ext x
        obtain ⟨j, k, rfl⟩ := Functor.CoconeTypes.IsColimit.ι_jointly_surjective hc x
        simp [coconeTypes, ← hm, dsimp% hc.fac_apply,
          dsimp% Sigma.ι_desc (hc.desc (coconeTypes s))] }⟩⟩⟩

中文:
实例 [HasCoproducts.{w}
  签名: C] (R
  定义体: ⟨fun {K} => ⟨fun {c} hc => ⟨by
    replace hc := (Types.isColimit_iff_coconeTypesIsColimit ..).1 ⟨hc⟩
    let coconeTypes (s : Cocone (K ⋙ sigmaConst.obj R)) : K.CoconeTypes :=
      { pt := R ⟶ s.pt
        ι j k := Sigma.ι (fun _ => R) k ≫ s.ι.app j
        ι_naturality g := by ext; simp [← s.w g] }
    exact {
      desc s := Sigma.desc (hc.desc (coconeTypes s))
      fac s j := by
        dsimp
        ext k
        simp [dsimp% hc.fac_apply, dsimp% Sigma.ι_desc (hc.desc (coconeTypes s)), coconeTypes]
      uniq s m hm := by
        dsimp
        ext x
        obtain ⟨j, k, rfl⟩ := Functor.CoconeTypes.IsColimit.ι_jointly_surjective hc x
        simp [coconeTypes, ← hm, dsimp% hc.fac_apply,
          dsimp% Sigma.ι_desc (hc.desc (coconeTypes s))] }⟩⟩⟩

Depends on / 依赖: Cocone, CoconeTypes, Functor, K.CoconeTypes, Sigma.desc, Types.isColimit_iff_coconeTypesIsColimit, coconeTypes, fac_apply, hc.desc, hc.fac_apply, isColimit_iff_coconeTypesIsColimit, replace, s.pt, sigmaConst, sigmaConst.obj
-/
instance [HasCoproducts.{w} C] (R : C) :
    PreservesColimitsOfSize.{v', u'} (sigmaConst.{w}.obj R) where
  preservesColimitsOfShape {J _} := ⟨fun {K} => ⟨fun {c} hc => ⟨by
    replace hc := (Types.isColimit_iff_coconeTypesIsColimit ..).1 ⟨hc⟩
    let coconeTypes (s : Cocone (K ⋙ sigmaConst.obj R)) : K.CoconeTypes :=
      { pt := R ⟶ s.pt
        ι j k := Sigma.ι (fun _ => R) k ≫ s.ι.app j
        ι_naturality g := by ext; simp [← s.w g] }
    exact {
      desc s := Sigma.desc (hc.desc (coconeTypes s))
      fac s j := by
        dsimp
        ext k
        simp [dsimp% hc.fac_apply, dsimp% Sigma.ι_desc (hc.desc (coconeTypes s)), coconeTypes]
      uniq s m hm := by
        dsimp
        ext x
        obtain ⟨j, k, rfl⟩ := Functor.CoconeTypes.IsColimit.ι_jointly_surjective hc x
        simp [coconeTypes, ← hm, dsimp% hc.fac_apply,
          dsimp% Sigma.ι_desc (hc.desc (coconeTypes s))] }⟩⟩⟩

variable [HasZeroMorphisms C] (R : C)

section

variable {α β : Type*} (f : α -> β)
  [HasCoproduct (fun (_ : α) => R)] [HasCoproduct (fun (_ : β) => R)]
  [HasCoproduct (fun (_ : ((Set.range f)ᶜ : Set _)) => R)]

open scoped Classical in
/-- A colimit cokernel cofork for the map
`∐ fun (_ : α) ↦ R ⟶ ∐ fun (_ : β) ↦ R` induced by a map `f : α → β`. -/
@[simps! pt, implicit_reducible]
/--
Definition of `sigmaConstCokernelCofork` / `sigmaConstCokernelCofork` 的定义

English:
definition sigmaConstCokernelCofork
  signature: :
  body: CokernelCofork.ofπ (Z := ∐ fun (_ : ((Set.range f)ᶜ : Set _)) => R)
    (Sigma.desc (fun b =>
      if hb : b in (Set.range f)ᶜ then Sigma.ι (fun _ => R) ⟨b, hb⟩ else 0))
    (by ext; simp)

中文:
定义 sigmaConstCokernelCofork
  签名: :
  定义体: CokernelCofork.ofπ (Z := ∐ fun (_ : ((Set.range f)ᶜ : Set _)) => R)
    (Sigma.desc (fun b =>
      if hb : b in (Set.range f)ᶜ then Sigma.ι (fun _ => R) ⟨b, hb⟩ else 0))
    (by ext; simp)
-/
noncomputable def sigmaConstCokernelCofork :
    CokernelCofork
      (Sigma.map' (f := fun (_ : α) => R) (g := fun (_ : β) => R) f (fun _ => 𝟙 R)) :=
  CokernelCofork.ofπ (Z := ∐ fun (_ : ((Set.range f)ᶜ : Set _)) => R)
    (Sigma.desc (fun b =>
      if hb : b in (Set.range f)ᶜ then Sigma.ι (fun _ => R) ⟨b, hb⟩ else 0))
    (by ext; simp)

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/--
lemma `ι_sigmaConstCokernelCofork_π` / 引理 `ι_sigmaConstCokernelCofork_π`

English:
lemma ι_sigmaConstCokernelCofork_π
  given: (b : β) (hb : b ∉ Set.range f)
  proof: by
  dsimp [sigmaConstCokernelCofork]
  rw [Sigma.ι_desc]
  apply dif_pos

中文:
引理 ι_sigmaConstCokernelCofork_π
  条件: (b : β) (hb : b ∉ 集合.range f)
  证明: by
  dsimp [sigmaConstCokernelCofork]
  rw [Sigma.ι_desc]
  apply dif_pos

Depends on / 依赖: dif_pos, sigmaConstCokernelCofork
-/
lemma ι_sigmaConstCokernelCofork_π (b : β) (hb : b ∉ Set.range f) :
    dsimp% Sigma.ι (fun _ => R) b ≫ (sigmaConstCokernelCofork R f).π =
      Sigma.ι (fun _ => R) ⟨b, hb⟩ := by
  dsimp [sigmaConstCokernelCofork]
  rw [Sigma.ι_desc]
  apply dif_pos

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
lemma `ι_sigmaConstCokernelCofork_π_eq_zero` / 引理 `ι_sigmaConstCokernelCofork_π_eq_zero`

English:
lemma ι_sigmaConstCokernelCofork_π_eq_zero
  given: (a : α)
  proof: by
  dsimp [sigmaConstCokernelCofork]
  rw [Sigma.ι_desc]
  exact dif_neg (by simp)

中文:
引理 ι_sigmaConstCokernelCofork_π_eq_zero
  条件: (a : α)
  证明: by
  dsimp [sigmaConstCokernelCofork]
  rw [Sigma.ι_desc]
  exact dif_neg (by simp)

Depends on / 依赖: dif_neg, sigmaConstCokernelCofork
-/
lemma ι_sigmaConstCokernelCofork_π_eq_zero (a : α) :
    dsimp% Sigma.ι (fun _ => R) (f a) ≫ (sigmaConstCokernelCofork R f).π = 0 := by
  dsimp [sigmaConstCokernelCofork]
  rw [Sigma.ι_desc]
  exact dif_neg (by simp)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isColimitSigmaConstCokernelCofork` / `isColimitSigmaConstCokernelCofork` 的定义

English:
definition isColimitSigmaConstCokernelCofork
  signature: :
  body: Cofork.IsColimit.mk _
    (fun s => Sigma.desc (fun ⟨b, _⟩ => Sigma.ι (fun _ => R) b ≫ s.π))
    (fun s => by
      ext b
      by_cases hb : b in Set.range f
      · obtain ⟨a, rfl⟩ := hb
        simpa [-CokernelCofork.condition] using Sigma.ι (fun _ => R) a ≫= s.condition.symm
      · simp [ι_sigmaConstCokernelCofork_π_assoc _ _ _ hb])
    (fun s m hm => by
      dsimp
      ext ⟨b, hb⟩
      rw [Sigma.ι_desc]; rw [← hm]; rw [ι_sigmaConstCokernelCofork_π_assoc])

中文:
定义 isColimitSigmaConstCokernelCofork
  签名: :
  定义体: Cofork.IsColimit.mk _
    (fun s => Sigma.desc (fun ⟨b, _⟩ => Sigma.ι (fun _ => R) b ≫ s.π))
    (fun s => by
      ext b
      by_cases hb : b in Set.range f
      · obtain ⟨a, rfl⟩ := hb
        simpa [-CokernelCofork.condition] using Sigma.ι (fun _ => R) a ≫= s.condition.symm
      · simp [ι_sigmaConstCokernelCofork_π_assoc _ _ _ hb])
    (fun s m hm => by
      dsimp
      ext ⟨b, hb⟩
      rw [Sigma.ι_desc]; rw [← hm]; rw [ι_sigmaConstCokernelCofork_π_assoc])

Depends on / 依赖: Cofork, Cofork.IsColimit.mk, CokernelCofork, CokernelCofork.condition, IsColimit, Set.range, Sigma.desc, condition, s.condition.symm
-/
noncomputable def isColimitSigmaConstCokernelCofork :
    IsColimit (sigmaConstCokernelCofork R f) :=
  Cofork.IsColimit.mk _
    (fun s => Sigma.desc (fun ⟨b, _⟩ => Sigma.ι (fun _ => R) b ≫ s.π))
    (fun s => by
      ext b
      by_cases hb : b in Set.range f
      · obtain ⟨a, rfl⟩ := hb
        simpa [-CokernelCofork.condition] using Sigma.ι (fun _ => R) a ≫= s.condition.symm
      · simp [ι_sigmaConstCokernelCofork_π_assoc _ _ _ hb])
    (fun s m hm => by
      dsimp
      ext ⟨b, hb⟩
      rw [Sigma.ι_desc]; rw [← hm]; rw [ι_sigmaConstCokernelCofork_π_assoc])

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  body: ⟨_, isColimitSigmaConstCokernelCofork R f⟩

中文:
实例 :
  定义体: ⟨_, isColimitSigmaConstCokernelCofork R f⟩
-/
instance :
    HasCokernel (Sigma.map' (f := fun (_ : α) => R) (g := fun (_ : β) => R) f (fun _ => 𝟙 R)) :=
  ⟨_, isColimitSigmaConstCokernelCofork R f⟩

end

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasCoproducts.{w}
  signature: C] {α β
  body: by
  dsimp; infer_instance

中文:
实例 [HasCoproducts.{w}
  签名: C] {α β
  定义体: by
  dsimp; infer_instance

Depends on / 依赖: infer_instance
-/
instance [HasCoproducts.{w} C] {α β : Type w} (f : α ⟶ β) :
    HasCokernel ((sigmaConst.obj R).map f) := by
  dsimp; infer_instance

end CategoryTheory.Limits
