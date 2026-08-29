/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma
public import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory

/-!
# Exactness of short complexes in concrete abelian categories

If an additive concrete category `C` has an additive forgetful functor to `Ab`
which preserves homology, then a short complex `S` in `C` is exact
if and only if it is so after applying the functor `forget₂ C Ab`.

-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Limits

section

variable {C : Type u} [Category.{v} C] {FC : C -> C -> Type*} {CC : C -> Type w}
variable [forall X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{w} C FC] [HasForget₂ C Ab]

@[simp]
/--
lemma `ShortComplex.zero_apply` / 引理 `ShortComplex.zero_apply`

English:
lemma ShortComplex.zero_apply
  proof: by
  rw [← ConcreteCategory.comp_apply]; rw [← Functor.map_comp]; rw [S.zero]; rw [Functor.map_zero]
  rfl

中文:
引理 短复形.zero_apply
  证明: by
  rw [← ConcreteCategory.comp_apply]; rw [← Functor.map_comp]; rw [S.zero]; rw [Functor.map_zero]
  rfl

Depends on / 依赖: ConcreteCategory, ConcreteCategory.comp_apply, Functor, Functor.map_comp, Functor.map_zero, Iso.refl, S.op_, S.zero, ShortComplex, ShortComplex.isoMk, comp_apply, comp_id, id_comp, map_comp, map_zero
-/
lemma ShortComplex.zero_apply
    [Limits.HasZeroMorphisms C] [(forget₂ C Ab).PreservesZeroMorphisms]
    (S : ShortComplex C) (x : (forget₂ C Ab).obj S.X₁) :
    ((forget₂ C Ab).map S.g) (((forget₂ C Ab).map S.f) x) = 0 := by
  rw [← ConcreteCategory.comp_apply]; rw [← Functor.map_comp]; rw [S.zero]; rw [Functor.map_zero]
  rfl

section preadditive

variable [Preadditive C] [(forget₂ C Ab).Additive] [(forget₂ C Ab).PreservesHomology]
  (S : ShortComplex C)

section
variable [HasZeroObject C]

/--
lemma `Preadditive.mono_iff_injective` / 引理 `Preadditive.mono_iff_injective`

English:
lemma Preadditive.mono_iff_injective
  given: {X Y : C} (f : X ⟶ Y)
  proof: by
  rw [← AddCommGrpCat.mono_iff_injective]
  constructor
  · intro
    infer_instance
  · apply Functor.mono_of_mono_map

中文:
引理 预加性.mono_iff_injective
  条件: {X Y : C} (f : X ⟶ Y)
  证明: by
  rw [← AddCommGrpCat.mono_iff_injective]
  constructor
  · intro
    infer_instance
  · apply Functor.mono_of_mono_map

Depends on / 依赖: AddCommGrpCat, AddCommGrpCat.mono_iff_injective, Functor, Functor.mono_of_mono_map, S.op.L, _exact, exact_iff_of_iso, exact_op_iff, infer_instance, mono_iff_injective, mono_of_mono_map
-/
lemma Preadditive.mono_iff_injective {X Y : C} (f : X ⟶ Y) :
    Mono f ↔ Function.Injective ((forget₂ C Ab).map f) := by
  rw [← AddCommGrpCat.mono_iff_injective]
  constructor
  · intro
    infer_instance
  · apply Functor.mono_of_mono_map

/--
lemma `Preadditive.mono_iff_injective'` / 引理 `Preadditive.mono_iff_injective'`

English:
lemma Preadditive.mono_iff_injective'
  given: {X Y : C} (f : X ⟶ Y)
  proof: by
  simp only [mono_iff_injective, ← CategoryTheory.ofHom_mono_iff_injective]
  apply (MorphismProperty.monomorphisms (Type w)).arrow_mk_iso_iff
  have e : forget₂ C Ab ⋙ forget Ab ≅ forget C := eqToIso (HasForget₂.forget_comp)
  exact Arrow.isoOfNatIso e (Arrow.mk f)

中文:
引理 预加性.mono_iff_injective'
  条件: {X Y : C} (f : X ⟶ Y)
  证明: by
  simp only [mono_iff_injective, ← CategoryTheory.ofHom_mono_iff_injective]
  apply (MorphismProperty.monomorphisms (Type w)).arrow_mk_iso_iff
  have e : forget₂ C Ab ⋙ forget Ab ≅ forget C := eqToIso (HasForget₂.forget_comp)
  exact Arrow.isoOfNatIso e (Arrow.mk f)

Depends on / 依赖: Arrow.isoOfNatIso, Arrow.mk, CategoryTheory, CategoryTheory.ofHom_mono_iff_injective, MorphismProperty, MorphismProperty.monomorphisms, arrow_mk_iso_iff, eqToIso, forget, forget_comp, isoOfNatIso, mono_iff_injective, monomorphisms, ofHom_mono_iff_injective
-/
lemma Preadditive.mono_iff_injective' {X Y : C} (f : X ⟶ Y) :
    Mono f ↔ Function.Injective f := by
  simp only [mono_iff_injective, ← CategoryTheory.ofHom_mono_iff_injective]
  apply (MorphismProperty.monomorphisms (Type w)).arrow_mk_iso_iff
  have e : forget₂ C Ab ⋙ forget Ab ≅ forget C := eqToIso (HasForget₂.forget_comp)
  exact Arrow.isoOfNatIso e (Arrow.mk f)

/--
lemma `Preadditive.epi_iff_surjective` / 引理 `Preadditive.epi_iff_surjective`

English:
lemma Preadditive.epi_iff_surjective
  given: {X Y : C} (f : X ⟶ Y)
  proof: by
  rw [← AddCommGrpCat.epi_iff_surjective]
  constructor
  · intro
    infer_instance
  · apply Functor.epi_of_epi_map

中文:
引理 预加性.epi_iff_surjective
  条件: {X Y : C} (f : X ⟶ Y)
  证明: by
  rw [← AddCommGrpCat.epi_iff_surjective]
  constructor
  · intro
    infer_instance
  · apply Functor.epi_of_epi_map

Depends on / 依赖: AddCommGrpCat, AddCommGrpCat.epi_iff_surjective, Functor, Functor.epi_of_epi_map, epi_iff_surjective, epi_of_epi_map, infer_instance
-/
lemma Preadditive.epi_iff_surjective {X Y : C} (f : X ⟶ Y) :
    Epi f ↔ Function.Surjective ((forget₂ C Ab).map f) := by
  rw [← AddCommGrpCat.epi_iff_surjective]
  constructor
  · intro
    infer_instance
  · apply Functor.epi_of_epi_map

/--
lemma `Preadditive.epi_iff_surjective'` / 引理 `Preadditive.epi_iff_surjective'`

English:
lemma Preadditive.epi_iff_surjective'
  given: {X Y : C} (f : X ⟶ Y)
  proof: by
  simp only [epi_iff_surjective, ← CategoryTheory.ofHom_epi_iff_surjective]
  apply (MorphismProperty.epimorphisms (Type w)).arrow_mk_iso_iff
  have e : forget₂ C Ab ⋙ forget Ab ≅ forget C := eqToIso (HasForget₂.forget_comp)
  exact Arrow.isoOfNatIso e (Arrow.mk f)

中文:
引理 预加性.epi_iff_surjective'
  条件: {X Y : C} (f : X ⟶ Y)
  证明: by
  simp only [epi_iff_surjective, ← CategoryTheory.ofHom_epi_iff_surjective]
  apply (MorphismProperty.epimorphisms (Type w)).arrow_mk_iso_iff
  have e : forget₂ C Ab ⋙ forget Ab ≅ forget C := eqToIso (HasForget₂.forget_comp)
  exact Arrow.isoOfNatIso e (Arrow.mk f)

Depends on / 依赖: Arrow.isoOfNatIso, Arrow.mk, CategoryTheory, CategoryTheory.ofHom_epi_iff_surjective, MorphismProperty, MorphismProperty.epimorphisms, arrow_mk_iso_iff, epi_iff_surjective, epimorphisms, eqToIso, forget, forget_comp, isoOfNatIso, ofHom_epi_iff_surjective
-/
lemma Preadditive.epi_iff_surjective' {X Y : C} (f : X ⟶ Y) :
    Epi f ↔ Function.Surjective f := by
  simp only [epi_iff_surjective, ← CategoryTheory.ofHom_epi_iff_surjective]
  apply (MorphismProperty.epimorphisms (Type w)).arrow_mk_iso_iff
  have e : forget₂ C Ab ⋙ forget Ab ≅ forget C := eqToIso (HasForget₂.forget_comp)
  exact Arrow.isoOfNatIso e (Arrow.mk f)

end

namespace ShortComplex

/--
lemma `exact_iff_exact_map_forget₂` / 引理 `exact_iff_exact_map_forget₂`

English:
lemma exact_iff_exact_map_forget₂
  given: [S.HasHomology]
  proof: (S.exact_map_iff_of_faithful (forget₂ C Ab)).symm

中文:
引理 exact_iff_exact_map_forget₂
  条件: [S.有同调]
  证明: (S.exact_map_iff_of_faithful (forget₂ C Ab)).symm

Depends on / 依赖: S.exact_map_iff_of_faithful, exact_map_iff_of_faithful
-/
lemma exact_iff_exact_map_forget₂ [S.HasHomology] :
    S.Exact ↔ (S.map (forget₂ C Ab)).Exact :=
  (S.exact_map_iff_of_faithful (forget₂ C Ab)).symm

/--
lemma `exact_iff_of_hasForget` / 引理 `exact_iff_of_hasForget`

English:
lemma exact_iff_of_hasForget
  given: [S.HasHomology]
  proof: by
  rw [S.exact_iff_exact_map_forget₂]; rw [ab_exact_iff]
  rfl

中文:
引理 exact_iff_of_hasForget
  条件: [S.有同调]
  证明: by
  rw [S.exact_iff_exact_map_forget₂]; rw [ab_exact_iff]
  rfl

Depends on / 依赖: S.exact_iff_exact_map_forget, ab_exact_iff
-/
lemma exact_iff_of_hasForget [S.HasHomology] :
    S.Exact ↔ forall (x₂ : (forget₂ C Ab).obj S.X₂) (_ : ((forget₂ C Ab).map S.g) x₂ = 0),
      exists (x₁ : (forget₂ C Ab).obj S.X₁), ((forget₂ C Ab).map S.f) x₁ = x₂ := by
  rw [S.exact_iff_exact_map_forget₂]; rw [ab_exact_iff]
  rfl

variable {S}

/--
lemma `ShortExact.injective_f` / 引理 `ShortExact.injective_f`

English:
lemma ShortExact.injective_f
  given: [HasZeroObject C] (hS : S.ShortExact)
  proof: by
  rw [← Preadditive.mono_iff_injective]
  exact hS.mono_f

中文:
引理 短正合.injective_f
  条件: [有ZeroObject C] (hS : S.短正合)
  证明: by
  rw [← Preadditive.mono_iff_injective]
  exact hS.mono_f

Depends on / 依赖: Preadditive, Preadditive.mono_iff_injective, hS.mono_f, mono_f, mono_iff_injective
-/
lemma ShortExact.injective_f [HasZeroObject C] (hS : S.ShortExact) :
    Function.Injective ((forget₂ C Ab).map S.f) := by
  rw [← Preadditive.mono_iff_injective]
  exact hS.mono_f

/--
lemma `ShortExact.surjective_g` / 引理 `ShortExact.surjective_g`

English:
lemma ShortExact.surjective_g
  given: [HasZeroObject C] (hS : S.ShortExact)
  proof: by
  rw [← Preadditive.epi_iff_surjective]
  exact hS.epi_g

中文:
引理 短正合.surjective_g
  条件: [有ZeroObject C] (hS : S.短正合)
  证明: by
  rw [← Preadditive.epi_iff_surjective]
  exact hS.epi_g

Depends on / 依赖: Preadditive, Preadditive.epi_iff_surjective, epi_g, epi_iff_surjective, hS.epi_g
-/
lemma ShortExact.surjective_g [HasZeroObject C] (hS : S.ShortExact) :
    Function.Surjective ((forget₂ C Ab).map S.g) := by
  rw [← Preadditive.epi_iff_surjective]
  exact hS.epi_g

variable (S)

/--
Definition of `cyclesMk` / `cyclesMk` 的定义

English:
definition cyclesMk
  signature: [S.HasHomology] (x₂ : (forget₂ C Ab).obj S.X₂)
  body: (S.mapCyclesIso (forget₂ C Ab)).hom ((ShortComplex.abCyclesIso _).inv ⟨x₂, hx₂⟩)

中文:
定义 cyclesMk
  签名: [S.有同调] (x₂ : (forget₂ C Ab).obj S.X₂)
  定义体: (S.mapCyclesIso (forget₂ C Ab)).hom ((ShortComplex.abCyclesIso _).inv ⟨x₂, hx₂⟩)

Depends on / 依赖: S.mapCyclesIso, ShortComplex, ShortComplex.abCyclesIso, abCyclesIso, mapCyclesIso
-/
noncomputable def cyclesMk [S.HasHomology] (x₂ : (forget₂ C Ab).obj S.X₂)
    (hx₂ : ((forget₂ C Ab).map S.g) x₂ = 0) :
    (forget₂ C Ab).obj S.cycles :=
  (S.mapCyclesIso (forget₂ C Ab)).hom ((ShortComplex.abCyclesIso _).inv ⟨x₂, hx₂⟩)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `i_cyclesMk` / 引理 `i_cyclesMk`

English:
lemma i_cyclesMk
  statement: [S.HasHomology] (x₂ : (forget₂ C Ab).obj S.X₂)
  proof: by
  dsimp [cyclesMk]
  -- `abCyclesIso_inv_apply_iCycles` is not in `simp`-normal form, so we first
  -- have to simplify it.
  have := abCyclesIso_inv_apply_iCycles (S.map (forget₂ C Ab)) ⟨x₂, hx₂⟩
  simp only [map_X₂, map_X₃, map_g] at this
  rw [← ConcreteCategory.comp_apply]; rw [S.mapCyclesIso_hom_iCycles (forget₂ C Ab)]; rw [this]

中文:
引理 i_cyclesMk
  结论: [S.有同调] (x₂ : (forget₂ C Ab).obj S.X₂)
  证明: by
  dsimp [cyclesMk]
  -- `abCyclesIso_inv_apply_iCycles` is not in `simp`-normal form, so we first
  -- have to simplify it.
  have := abCyclesIso_inv_apply_iCycles (S.map (forget₂ C Ab)) ⟨x₂, hx₂⟩
  simp only [map_X₂, map_X₃, map_g] at this
  rw [← ConcreteCategory.comp_apply]; rw [S.mapCyclesIso_hom_iCycles (forget₂ C Ab)]; rw [this]

Depends on / 依赖: cyclesMk
-/
lemma i_cyclesMk [S.HasHomology] (x₂ : (forget₂ C Ab).obj S.X₂)
    (hx₂ : ((forget₂ C Ab).map S.g) x₂ = 0) :
    (forget₂ C Ab).map S.iCycles (S.cyclesMk x₂ hx₂) = x₂ := by
  dsimp [cyclesMk]
  -- `abCyclesIso_inv_apply_iCycles` is not in `simp`-normal form, so we first
  -- have to simplify it.
  have := abCyclesIso_inv_apply_iCycles (S.map (forget₂ C Ab)) ⟨x₂, hx₂⟩
  simp only [map_X₂, map_X₃, map_g] at this
  rw [← ConcreteCategory.comp_apply]; rw [S.mapCyclesIso_hom_iCycles (forget₂ C Ab)]; rw [this]

end ShortComplex

end preadditive

end

section abelian

variable {C : Type u} [Category.{v} C] {FC : C -> C -> Type*} {CC : C -> Type v}
  [forall X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{v} C FC] [HasForget₂ C Ab]
  [Abelian C] [(forget₂ C Ab).Additive] [(forget₂ C Ab).PreservesHomology]

namespace ShortComplex

namespace SnakeInput

variable (D : SnakeInput C)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `δ_apply` / 引理 `δ_apply`

English:
lemma δ_apply
  statement: (x₃ : ToType (D.L₀.X₃)) (x₂ : ToType (D.L₁.X₂)) (x₁ : ToType (D.L₂.X₁))
  proof: by
  have := (forget₂ C Ab).preservesFiniteLimits_of_preservesHomology
  have : PreservesFiniteLimits (forget C) := by
    have : forget₂ C Ab ⋙ forget Ab = forget C := HasForget₂.forget_comp
    simpa only [← this] using comp_preservesFiniteLimits _ _
  have eq := CategoryTheory.congr_fun (D.snd_δ)
    (Limits.Concrete.pullbackMk D.L₁.g D.v₀₁.τ₃ x₂ x₃ h₂)
  have eq₁ := Concrete.pullbackMk_fst D.L₁.g D.v₀₁.τ₃ x₂ x₃ h₂
  have eq₂ := Concrete.pullbackMk_snd D.L₁.g D.v₀₁.τ₃ x₂ x₃ h₂
  rw [ConcreteCategory.comp_apply]; rw [ConcreteCategory.comp_apply] at eq
  rw [eq₂] at eq
  refine eq.trans (CategoryTheory.congr_arg (D.v₂₃.τ₁) ?_)
  apply (Preadditive.mono_iff_injective' D.L₂.f).1 inferInstance
  rw [← ConcreteCategory.comp_apply]; rw [φ₁_L₂_f]
  dsimp [φ₂]
  rw [ConcreteCategory.comp_apply]; rw [eq₁]
  exact h₁.symm

中文:
引理 δ_apply
  结论: (x₃ : ToType (D.L₀.X₃)) (x₂ : ToType (D.L₁.X₂)) (x₁ : ToType (D.L₂.X₁))
  证明: by
  have := (forget₂ C Ab).preservesFiniteLimits_of_preservesHomology
  have : PreservesFiniteLimits (forget C) := by
    have : forget₂ C Ab ⋙ forget Ab = forget C := HasForget₂.forget_comp
    simpa only [← this] using comp_preservesFiniteLimits _ _
  have eq := CategoryTheory.congr_fun (D.snd_δ)
    (Limits.Concrete.pullbackMk D.L₁.g D.v₀₁.τ₃ x₂ x₃ h₂)
  have eq₁ := Concrete.pullbackMk_fst D.L₁.g D.v₀₁.τ₃ x₂ x₃ h₂
  have eq₂ := Concrete.pullbackMk_snd D.L₁.g D.v₀₁.τ₃ x₂ x₃ h₂
  rw [ConcreteCategory.comp_apply]; rw [ConcreteCategory.comp_apply] at eq
  rw [eq₂] at eq
  refine eq.trans (CategoryTheory.congr_arg (D.v₂₃.τ₁) ?_)
  apply (Preadditive.mono_iff_injective' D.L₂.f).1 inferInstance
  rw [← ConcreteCategory.comp_apply]; rw [φ₁_L₂_f]
  dsimp [φ₂]
  rw [ConcreteCategory.comp_apply]; rw [eq₁]
  exact h₁.symm

Depends on / 依赖: CategoryTheory, CategoryTheory.congr_fun, Concrete, Concrete.pullbackMk_fst, Concrete.pullbackMk_snd, ConcreteCategory, ConcreteCategory.comp_apply, D.snd_, Limits, Limits.Concrete.pullbackMk, PreservesFiniteLimits, comp_apply, comp_preservesFiniteLimits, congr_fun, forget, forget_comp, preservesFiniteLimits_of_preservesHomology, pullbackMk, pullbackMk_fst, pullbackMk_snd
-/
lemma δ_apply (x₃ : ToType (D.L₀.X₃)) (x₂ : ToType (D.L₁.X₂)) (x₁ : ToType (D.L₂.X₁))
    (h₂ : D.L₁.g x₂ = D.v₀₁.τ₃ x₃) (h₁ : D.L₂.f x₁ = D.v₁₂.τ₂ x₂) :
    D.δ x₃ = D.v₂₃.τ₁ x₁ := by
  have := (forget₂ C Ab).preservesFiniteLimits_of_preservesHomology
  have : PreservesFiniteLimits (forget C) := by
    have : forget₂ C Ab ⋙ forget Ab = forget C := HasForget₂.forget_comp
    simpa only [← this] using comp_preservesFiniteLimits _ _
  have eq := CategoryTheory.congr_fun (D.snd_δ)
    (Limits.Concrete.pullbackMk D.L₁.g D.v₀₁.τ₃ x₂ x₃ h₂)
  have eq₁ := Concrete.pullbackMk_fst D.L₁.g D.v₀₁.τ₃ x₂ x₃ h₂
  have eq₂ := Concrete.pullbackMk_snd D.L₁.g D.v₀₁.τ₃ x₂ x₃ h₂
  rw [ConcreteCategory.comp_apply]; rw [ConcreteCategory.comp_apply] at eq
  rw [eq₂] at eq
  refine eq.trans (CategoryTheory.congr_arg (D.v₂₃.τ₁) ?_)
  apply (Preadditive.mono_iff_injective' D.L₂.f).1 inferInstance
  rw [← ConcreteCategory.comp_apply]; rw [φ₁_L₂_f]
  dsimp [φ₂]
  rw [ConcreteCategory.comp_apply]; rw [eq₁]
  exact h₁.symm

/--
lemma `δ_apply'` / 引理 `δ_apply'`

English:
lemma δ_apply'
  statement: (x₃ : (forget₂ C Ab).obj D.L₀.X₃)
  proof: by
  have e : forget₂ C Ab ⋙ forget Ab ≅ forget C := eqToIso (HasForget₂.forget_comp)
  apply (ofHom_mono_iff_injective (e.hom.app _)).1 inferInstance
  refine ((ConcreteCategory.congr_hom (e.hom.naturality D.δ) x₃).trans ?_).trans
    (ConcreteCategory.congr_hom (e.hom.naturality D.v₂₃.τ₁).symm x₁)
  exact D.δ_apply _ _ _
    (((ConcreteCategory.congr_hom (e.hom.naturality D.L₁.g) x₂).symm.trans (by simp_all)).trans
      (ConcreteCategory.congr_hom (e.hom.naturality D.v₀₁.τ₃) x₃))
    (((ConcreteCategory.congr_hom (e.hom.naturality D.L₂.f) x₁).symm.trans (by simp_all)).trans
      (ConcreteCategory.congr_hom (e.hom.naturality D.v₁₂.τ₂) x₂))

中文:
引理 δ_apply'
  结论: (x₃ : (forget₂ C Ab).obj D.L₀.X₃)
  证明: by
  have e : forget₂ C Ab ⋙ forget Ab ≅ forget C := eqToIso (HasForget₂.forget_comp)
  apply (ofHom_mono_iff_injective (e.hom.app _)).1 inferInstance
  refine ((ConcreteCategory.congr_hom (e.hom.naturality D.δ) x₃).trans ?_).trans
    (ConcreteCategory.congr_hom (e.hom.naturality D.v₂₃.τ₁).symm x₁)
  exact D.δ_apply _ _ _
    (((ConcreteCategory.congr_hom (e.hom.naturality D.L₁.g) x₂).symm.trans (by simp_all)).trans
      (ConcreteCategory.congr_hom (e.hom.naturality D.v₀₁.τ₃) x₃))
    (((ConcreteCategory.congr_hom (e.hom.naturality D.L₂.f) x₁).symm.trans (by simp_all)).trans
      (ConcreteCategory.congr_hom (e.hom.naturality D.v₁₂.τ₂) x₂))

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, congr_hom, e.hom.app, e.hom.naturality, eqToIso, forget, forget_comp, naturality, ofHom_mono_iff_injective, symm.trans
-/
lemma δ_apply' (x₃ : (forget₂ C Ab).obj D.L₀.X₃)
    (x₂ : (forget₂ C Ab).obj D.L₁.X₂) (x₁ : (forget₂ C Ab).obj D.L₂.X₁)
    (h₂ : (forget₂ C Ab).map D.L₁.g x₂ = (forget₂ C Ab).map D.v₀₁.τ₃ x₃)
    (h₁ : (forget₂ C Ab).map D.L₂.f x₁ = (forget₂ C Ab).map D.v₁₂.τ₂ x₂) :
    (forget₂ C Ab).map D.δ x₃ = (forget₂ C Ab).map D.v₂₃.τ₁ x₁ := by
  have e : forget₂ C Ab ⋙ forget Ab ≅ forget C := eqToIso (HasForget₂.forget_comp)
  apply (ofHom_mono_iff_injective (e.hom.app _)).1 inferInstance
  refine ((ConcreteCategory.congr_hom (e.hom.naturality D.δ) x₃).trans ?_).trans
    (ConcreteCategory.congr_hom (e.hom.naturality D.v₂₃.τ₁).symm x₁)
  exact D.δ_apply _ _ _
    (((ConcreteCategory.congr_hom (e.hom.naturality D.L₁.g) x₂).symm.trans (by simp_all)).trans
      (ConcreteCategory.congr_hom (e.hom.naturality D.v₀₁.τ₃) x₃))
    (((ConcreteCategory.congr_hom (e.hom.naturality D.L₂.f) x₁).symm.trans (by simp_all)).trans
      (ConcreteCategory.congr_hom (e.hom.naturality D.v₁₂.τ₂) x₂))

end SnakeInput

end ShortComplex

end abelian

end CategoryTheory
