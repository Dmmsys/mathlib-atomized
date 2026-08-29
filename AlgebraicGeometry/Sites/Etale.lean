/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Sites.BigZariski
public import Mathlib.AlgebraicGeometry.Sites.Small
public import Mathlib.CategoryTheory.Limits.Elements
public import Mathlib.CategoryTheory.Sites.Point.Basic

/-!

# The étale site

In this file we define the big étale site, i.e. the étale topology as a Grothendieck topology
on the category of schemes.

-/

@[expose] public section

universe v u

open CategoryTheory MorphismProperty Limits

namespace AlgebraicGeometry.Scheme

/--
Definition of `etalePrecoverage` / `etalePrecoverage` 的定义

English:
definition etalePrecoverage
  signature: : Precoverage Scheme.{u}
  body: precoverage @Etale

中文:
定义 etalePrecoverage
  签名: : Precoverage Scheme.{u}
  定义体: precoverage @Etale

Depends on / 依赖: precoverage
-/
def etalePrecoverage : Precoverage Scheme.{u} :=
  precoverage @Etale

/--
Definition of `etalePretopology` / `etalePretopology` 的定义

English:
definition etalePretopology
  signature: : Pretopology Scheme.{u}
  body: pretopology @Etale

中文:
定义 etalePretopology
  签名: : Pretopology Scheme.{u}
  定义体: pretopology @Etale

Depends on / 依赖: pretopology
-/
def etalePretopology : Pretopology Scheme.{u} :=
  pretopology @Etale

/--
Definition of `etaleTopology` / `etaleTopology` 的定义

English:
abbreviation etaleTopology
  signature: : GrothendieckTopology Scheme.{u}
  body: grothendieckTopology @Etale

中文:
缩写 etaleTopology
  签名: : GrothendieckTopology Scheme.{u}
  定义体: grothendieckTopology @Etale

Depends on / 依赖: grothendieckTopology
-/
abbrev etaleTopology : GrothendieckTopology Scheme.{u} :=
  grothendieckTopology @Etale

/--
lemma `zariskiTopology_le_etaleTopology` / 引理 `zariskiTopology_le_etaleTopology`

English:
lemma zariskiTopology_le_etaleTopology
  statement: zariskiTopology <= etaleTopology
  proof: by
  apply grothendieckTopology_monotone
  intro X Y f hf
  infer_instance

中文:
引理 zariskiTopology_le_etaleTopology
  结论: zariskiTopology <= etaleTopology
  证明: by
  apply grothendieckTopology_monotone
  intro X Y f hf
  infer_instance

Depends on / 依赖: grothendieckTopology_monotone, infer_instance
-/
lemma zariskiTopology_le_etaleTopology : zariskiTopology <= etaleTopology := by
  apply grothendieckTopology_monotone
  intro X Y f hf
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `smallEtaleTopology` / `smallEtaleTopology` 的定义

English:
definition smallEtaleTopology
  signature: (X : Scheme.{u})
  body: X.smallGrothendieckTopology (P := @Etale)

中文:
定义 smallEtaleTopology
  签名: (X : Scheme.{u})
  定义体: X.smallGrothendieckTopology (P := @Etale)

Depends on / 依赖: X.smallGrothendieckTopology, smallGrothendieckTopology
-/
def smallEtaleTopology (X : Scheme.{u}) : GrothendieckTopology X.Etale :=
  X.smallGrothendieckTopology (P := @Etale)

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `smallEtalePretopology` / `smallEtalePretopology` 的定义

English:
definition smallEtalePretopology
  signature: (X : Scheme.{u})
  body: X.smallPretopology (Q := @Etale) (P := @Etale)

中文:
定义 smallEtalePretopology
  签名: (X : Scheme.{u})
  定义体: X.smallPretopology (Q := @Etale) (P := @Etale)

Depends on / 依赖: X.smallPretopology, smallPretopology
-/
def smallEtalePretopology (X : Scheme.{u}) : Pretopology X.Etale :=
  X.smallPretopology (Q := @Etale) (P := @Etale)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `ofArrows_mem_smallEtaleTopology_iff` / 引理 `ofArrows_mem_smallEtaleTopology_iff`

English:
lemma ofArrows_mem_smallEtaleTopology_iff
  proof: by
  refine ⟨fun hf => ?_, fun hf => (mem_smallGrothendieckTopology _ _).2 ?_⟩
  · obtain ⟨U, _, _, hU⟩ := (mem_smallGrothendieckTopology _ _).1 hf
    ext y
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    obtain ⟨i, ⟨u, rfl⟩⟩ := ((ofArrows_mem_precoverage_iff _).1 U.mem₀).

中文:
引理 ofArrows_mem_smallEtaleTopology_iff
  证明: by
  refine ⟨fun hf => ?_, fun hf => (mem_smallGrothendieckTopology _ _).2 ?_⟩
  · obtain ⟨U, _, _, hU⟩ := (mem_smallGrothendieckTopology _ _).1 hf
    ext y
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    obtain ⟨i, ⟨u, rfl⟩⟩ := ((ofArrows_mem_precoverage_iff _).1 U.mem₀).

Depends on / 依赖: CategoryTheory, CategoryTheory.Over.forget, Etale.forget, Set.mem_iUnion, Set.mem_range, Set.mem_univ, U.mem, W.left, b.left, congr_map, forget, iff_true, mem_iUnion, mem_range, mem_smallGrothendieckTopology, mem_univ, ofArrows_mem_precoverage_iff, replace
-/
lemma ofArrows_mem_smallEtaleTopology_iff
    {X : Scheme.{u}} {W : X.Etale} {ι : Type*}
    {Z : ι -> X.Etale} (f : forall i, Z i ⟶ W) :
    Sieve.ofArrows _ f in smallEtaleTopology _ _ ↔
      ⋃ i, Set.range (f i).left = .univ := by
  refine ⟨fun hf => ?_, fun hf => (mem_smallGrothendieckTopology _ _).2 ?_⟩
  · obtain ⟨U, _, _, hU⟩ := (mem_smallGrothendieckTopology _ _).1 hf
    ext y
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    obtain ⟨i, ⟨u, rfl⟩⟩ := ((ofArrows_mem_precoverage_iff _).1 U.mem₀).1 y
    obtain ⟨_, b, _, ⟨j⟩, fac⟩ := hU _ _ ⟨i⟩
    replace fac : b.left ≫ (f j).left = U.f i :=
      (Etale.forget _ ⋙ CategoryTheory.Over.forget _).congr_map fac
    exact ⟨j, b.left u, by simp [← fac]⟩
  · have (w : W.left) : exists (i : ι), w in Set.range (f i).left := by
      have := Set.mem_univ w
      simpa [← hf]
    choose i z hz using this
    let V : Cover (precoverage @Etale) W.left :=
      Cover.mkOfCovers W.left (fun w => (Z (i w)).left)
        (fun w => (f (i w)).left) (fun w => ⟨_, _, hz w⟩) inferInstance
    let : Cover.Over X V :=
      { over w := ⟨(Z (i w)).hom⟩
        isOver_map w := by cat_disch }
    have (w : W.left) : Etale (V.X w ↘ X) := (Z (i w)).prop
    refine ⟨V, inferInstance, inferInstance, ?_⟩
    rintro _ _ ⟨w⟩
    refine ⟨_, 𝟙 _, _, ⟨i w⟩, by cat_disch⟩

instance {S : Scheme.{u}} (𝒰 : S.Cover (precoverage @Etale)) (i : 𝒰.I₀) : Etale (𝒰.f i) :=
  𝒰.map_prop i

set_option backward.isDefEq.respectTransparency false in
/-- A separably closed field `Ω` defines a point on the étale topology by the fiber
functor `X ↦ Hom(Spec Ω, X)`. -/
noncomputable
/--
Definition of `geometricFiber` / `geometricFiber` 的定义

English:
definition geometricFiber
  signature: (Ω : Type u) [Field Ω] [IsSepClosed Ω]
  body: coyoneda.obj ⟨Spec (.of Ω)⟩
  jointly_surjective {S} R hR (f : Spec (.of Ω) ⟶ S) := by
    obtain ⟨⟨x, a⟩, rfl⟩ := (Scheme.SpecToEquivOfField Ω S).symm.surjective f
    rw [mem_grothendieckTopology_iff] at hR
    obtain ⟨𝒰, hle⟩ := hR
    obtain ⟨i, y, rfl⟩ := 𝒰.exists_eq x
    refine ⟨𝒰.X i, 𝒰.f i,

中文:
定义 geometricFiber
  签名: (Ω : 类型u) [Field Ω] [IsSepClosed Ω]
  定义体: coyoneda.obj ⟨Spec (.of Ω)⟩
  jointly_surjective {S} R hR (f : Spec (.of Ω) ⟶ S) := by
    obtain ⟨⟨x, a⟩, rfl⟩ := (Scheme.SpecToEquivOfField Ω S).symm.surjective f
    rw [mem_grothendieckTopology_iff] at hR
    obtain ⟨𝒰, hle⟩ := hR
    obtain ⟨i, y, rfl⟩ := 𝒰.exists_eq x
    refine ⟨𝒰.X i, 𝒰.f i,

Depends on / 依赖: coyoneda, coyoneda.obj
-/
def geometricFiber (Ω : Type u) [Field Ω] [IsSepClosed Ω] : etaleTopology.Point where
  fiber := coyoneda.obj ⟨Spec (.of Ω)⟩
  jointly_surjective {S} R hR (f : Spec (.of Ω) ⟶ S) := by
    obtain ⟨⟨x, a⟩, rfl⟩ := (Scheme.SpecToEquivOfField Ω S).symm.surjective f
    rw [mem_grothendieckTopology_iff] at hR
    obtain ⟨𝒰, hle⟩ := hR
    obtain ⟨i, y, rfl⟩ := 𝒰.exists_eq x
    refine ⟨𝒰.X i, 𝒰.f i, hle _ _ ⟨i⟩, ?_⟩
    let k := (𝒰.X i).residueField y
    let m : S.residueField (𝒰.f i y) ⟶ (𝒰.X i).residueField y :=
      (𝒰.f i).residueFieldMap y
    algebraize [((𝒰.f i).residueFieldMap y).hom, a.hom]
    let b : (𝒰.X i).residueField y ->ₐ[S.residueField (𝒰.f i y)] Ω :=
      IsSepClosed.lift
    have hfac : (𝒰.f i).residueFieldMap y ≫ CommRingCat.ofHom b.toRingHom = a := by
      ext1; exact b.comp_algebraMap
    use Spec.map (CommRingCat.ofHom b.toRingHom) ≫ (𝒰.X i).fromSpecResidueField y
    simp [SpecToEquivOfField, ← hfac]

end AlgebraicGeometry.Scheme
