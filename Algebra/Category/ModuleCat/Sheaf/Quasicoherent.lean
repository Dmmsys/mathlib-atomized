/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.CategoryTheory.Sites.CoversTop.Over

/-!
# Quasicoherent sheaves

A sheaf of modules is quasi-coherent if it admits locally a presentation as the
cokernel of a morphism between coproducts of copies of the sheaf of rings.
When these coproducts are finite, we say that the sheaf is of finite presentation.

## References

* https://stacks.math.columbia.edu/tag/01BD

-/

@[expose] public section

universe w u v₁ v₂ u₁ u₂

open CategoryTheory Limits

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}

namespace SheafOfModules

section

variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/--
Definition of `Presentation` / `Presentation` 的定义

English:
structure Presentation
  parameters: (M : SheafOfModules.{u} R)
  axioms and operations (2):
    - generators : M.GeneratingSections
    - relations : (kernel generators.π).GeneratingSections

中文:
结构 Presentation
  参数: (M : SheafOfModules.{u} R)
  公理与运算 (2 个):
    - generators : M.GeneratingSections
    - relations : (kernel generators.π).GeneratingSections
-/
structure Presentation (M : SheafOfModules.{u} R) where
  /-- generators -/
  generators : M.GeneratingSections
  /-- relations -/
  relations : (kernel generators.π).GeneratingSections

/--
Definition of `Presentation.IsFinite` / `Presentation.IsFinite` 的定义

English:
class Presentation.IsFinite
  parameters: {M : SheafOfModules.{u} R} (p : M.Presentation)
  axioms and operations (2):
    - isFiniteType_generators : p.generators.IsFiniteType  [default: by infer_instance]
    - isFiniteType_relations : p.relations.IsFiniteType  [default: by infer_instance]

中文:
类 Presentation.IsFinite
  参数: {M : SheafOfModules.{u} R} (p : M.Presentation)
  公理与运算 (2 个):
    - isFiniteType_generators : p.generators.IsFiniteType  [默认: by infer_instance]
    - isFiniteType_relations : p.relations.IsFiniteType  [默认: by infer_instance]

Depends on / 依赖: IsFiniteType, infer_instance, isFiniteType_relations, p.relations.IsFiniteType, relations
-/
class Presentation.IsFinite {M : SheafOfModules.{u} R} (p : M.Presentation) : Prop where
  isFiniteType_generators : p.generators.IsFiniteType := by infer_instance
  isFiniteType_relations : p.relations.IsFiniteType := by infer_instance

attribute [instance] Presentation.IsFinite.isFiniteType_generators
  Presentation.IsFinite.isFiniteType_relations

@[deprecated Presentation.IsFinite.isFiniteType_relations (since := "2026-04-14")]
/--
lemma `Presentation.IsFinite.finite_relations` / 引理 `Presentation.IsFinite.finite_relations`

English:
lemma Presentation.IsFinite.finite_relations
  statement: {M : SheafOfModules.{u} R} (p : M.Presentation)
  proof: GeneratingSections.IsFiniteType.finite

中文:
引理 Presentation.IsFinite.finite_relations
  结论: {M : SheafOfModules.{u} R} (p : M.Presentation)
  证明: GeneratingSections.IsFiniteType.finite

Depends on / 依赖: GeneratingSections, GeneratingSections.IsFiniteType.finite, IsFiniteType, finite
-/
lemma Presentation.IsFinite.finite_relations {M : SheafOfModules.{u} R} (p : M.Presentation)
    [p.IsFinite] : Finite p.relations.I := GeneratingSections.IsFiniteType.finite

end

noncomputable section

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat]
  {ι σ : Type u}

/-- Given two morphisms of sheaves of `R`-modules `f : free ι ⟶ free σ` and `g : free σ ⟶ M`
satisfying `H : f ≫ g = 0` and `IsColimit (CokernelCofork.ofπ g H)`, we obtain
generators of `Presentation M`. -/
@[simps! I s]
/--
Definition of `generatorsOfIsCokernelFree` / `generatorsOfIsCokernelFree` 的定义

English:
definition generatorsOfIsCokernelFree
  signature: {M : SheafOfModules.{u} R}
  body: σ
  s := M.freeHomEquiv g
  epi := by simpa using! epi_of_isColimit_cofork H'

@[simp]

中文:
定义 generatorsOfIsCokernelFree
  签名: {M : SheafOfModules.{u} R}
  定义体: σ
  s := M.freeHomEquiv g
  epi := by simpa using! epi_of_isColimit_cofork H'

@[simp]
-/
def generatorsOfIsCokernelFree {M : SheafOfModules.{u} R}
    (f : free ι ⟶ free σ) (g : free σ ⟶ M) (H : f ≫ g = 0)
    (H' : IsColimit (CokernelCofork.ofπ g H)) : M.GeneratingSections where
  I := σ
  s := M.freeHomEquiv g
  epi := by simpa using! epi_of_isColimit_cofork H'

@[simp]
/--
theorem `generatorsOfIsCokernelFree_π` / 定理 `generatorsOfIsCokernelFree_π`

English:
theorem generatorsOfIsCokernelFree_π
  statement: {M : SheafOfModules.{u} R}
  proof: M.freeHomEquiv.symm_apply_apply g

中文:
定理 generatorsOfIsCokernelFree_π
  结论: {M : SheafOfModules.{u} R}
  证明: M.freeHomEquiv.symm_apply_apply g

Depends on / 依赖: M.freeHomEquiv.symm_apply_apply, freeHomEquiv, symm_apply_apply
-/
theorem generatorsOfIsCokernelFree_π {M : SheafOfModules.{u} R}
    (f : free ι ⟶ free σ) (g : free σ ⟶ M) (H : f ≫ g = 0)
    (H' : IsColimit (CokernelCofork.ofπ g H)) :
    (generatorsOfIsCokernelFree f g H H').π = g := M.freeHomEquiv.symm_apply_apply g

set_option backward.isDefEq.respectTransparency false in
/-- Given two morphisms of sheaves of `R`-modules `f : free ι ⟶ free σ` and `g : free σ ⟶ M`
satisfying `H : f ≫ g = 0` and `IsColimit (CokernelCofork.ofπ g H)`, we obtain
relations of `Presentation M`. -/
@[simps! I s]
/--
Definition of `relationsOfIsCokernelFree` / `relationsOfIsCokernelFree` 的定义

English:
definition relationsOfIsCokernelFree
  signature: {M : SheafOfModules.{u} R}
  body: ι
s := (kernel (generatorsOfIsCokernelFree f g H H').π).freeHomEquiv kernel.lift
    (generatorsOfIsCokernelFree f g H H').π f (by simp [H])
  epi := by
    let h : cokernel f ≅ M := (H'.coconePointUniqueUpToIso (colimit.isColimit _)).symm
    let h' : Abelian.image f ≅ kernel (generatorsOfIsCokerne

中文:
定义 relationsOfIsCokernelFree
  签名: {M : SheafOfModules.{u} R}
  定义体: ι
s := (kernel (generatorsOfIsCokernelFree f g H H').π).freeHomEquiv kernel.lift
    (generatorsOfIsCokernelFree f g H H').π f (by simp [H])
  epi := by
    let h : cokernel f ≅ M := (H'.coconePointUniqueUpToIso (colimit.isColimit _)).symm
    let h' : Abelian.image f ≅ kernel (generatorsOfIsCokerne
-/
def relationsOfIsCokernelFree {M : SheafOfModules.{u} R}
    (f : free ι ⟶ free σ) (g : free σ ⟶ M) (H : f ≫ g = 0)
    (H' : IsColimit (CokernelCofork.ofπ g H)) :
    (kernel (generatorsOfIsCokernelFree f g H H').π).GeneratingSections where
  I := ι
s := (kernel (generatorsOfIsCokernelFree f g H H').π).freeHomEquiv kernel.lift
    (generatorsOfIsCokernelFree f g H H').π f (by simp [H])
  epi := by
    let h : cokernel f ≅ M := (H'.coconePointUniqueUpToIso (colimit.isColimit _)).symm
    let h' : Abelian.image f ≅ kernel (generatorsOfIsCokernelFree f g H H').π :=
      kernel.mapIso (cokernel.π f) (generatorsOfIsCokernelFree f g H H').π
        (Iso.refl _) h (by simp [h])
    have comp_aux : Abelian.factorThruImage f ≫ h'.hom =
      (kernel.lift (generatorsOfIsCokernelFree f g H H').π f (by simp [H])) :=
equalizer.hom_ext by simp [h']
    rw [← comp_aux]; rw [Equiv.symm_apply_apply]
    infer_instance

/-- Given two morphisms of sheaves of `R`-modules `f : free ι ⟶ free σ` and `g : free σ ⟶ M`
satisfying `H : f ≫ g = 0` and `IsColimit (CokernelCofork.ofπ g H)`, we obtain a
`Presentation M`. -/
@[simps]
/--
Definition of `presentationOfIsCokernelFree` / `presentationOfIsCokernelFree` 的定义

English:
definition presentationOfIsCokernelFree
  signature: {M : SheafOfModules.{u} R}
  body: generatorsOfIsCokernelFree f g H H'
  relations := relationsOfIsCokernelFree f g H H'

中文:
定义 presentationOfIsCokernelFree
  签名: {M : SheafOfModules.{u} R}
  定义体: generatorsOfIsCokernelFree f g H H'
  relations := relationsOfIsCokernelFree f g H H'

Depends on / 依赖: generatorsOfIsCokernelFree
-/
def presentationOfIsCokernelFree {M : SheafOfModules.{u} R}
    (f : free ι ⟶ free σ) (g : free σ ⟶ M) (H : f ≫ g = 0)
    (H' : IsColimit (CokernelCofork.ofπ g H)) : Presentation M where
  generators := generatorsOfIsCokernelFree f g H H'
  relations := relationsOfIsCokernelFree f g H H'

/--
Definition of `Presentation.isColimit` / `Presentation.isColimit` 的定义

English:
definition Presentation.isColimit
  signature: {M : SheafOfModules.{u} R} (P : Presentation M)
  body: isCokernelEpiComp (c := CokernelCofork.ofπ _ (kernel.condition P.generators.π))
      (Abelian.epiIsCokernelOfKernel _ <| limit.isLimit _) _ rfl

中文:
定义 Presentation.isColimit
  签名: {M : SheafOfModules.{u} R} (P : Presentation M)
  定义体: isCokernelEpiComp (c := CokernelCofork.ofπ _ (kernel.condition P.generators.π))
      (Abelian.epiIsCokernelOfKernel _ <| limit.isLimit _) _ rfl

Depends on / 依赖: P.relations.s, freeHomEquiv, kernel, relations
-/
def Presentation.isColimit {M : SheafOfModules.{u} R} (P : Presentation M) :
    IsColimit (CokernelCofork.ofπ (f := (freeHomEquiv _).symm P.relations.s ≫ (kernel.ι _))
      P.generators.π (by simp)) :=
  isCokernelEpiComp (c := CokernelCofork.ofπ _ (kernel.condition P.generators.π))
      (Abelian.epiIsCokernelOfKernel _ <| limit.isLimit _) _ rfl

set_option backward.defeqAttrib.useBackward true in
/-- Mapping a presentation under an isomorphism. -/
@[simps]
/--
Definition of `Presentation.ofIsIso` / `Presentation.ofIsIso` 的定义

English:
definition Presentation.ofIsIso
  signature: {M N : SheafOfModules.{u} R} (f : M ⟶ N) [IsIso f]
  body: σ.generators.ofEpi f
  relations := σ.relations.ofEpi ((kernelCompMono _ f).symm.trans <| eqToIso (by simp)).hom

@[deprecated (since := "2026-04-15")] alias Presentation.of_isIso := Presentation.ofIsIso

中文:
定义 Presentation.ofIsIso
  签名: {M N : SheafOfModules.{u} R} (f : M ⟶ N) [IsIso f]
  定义体: σ.generators.ofEpi f
  relations := σ.relations.ofEpi ((kernelCompMono _ f).symm.trans <| eqToIso (by simp)).hom

@[deprecated (since := "2026-04-15")] alias Presentation.of_isIso := Presentation.ofIsIso

Depends on / 依赖: generators, generators.ofEpi
-/
noncomputable def Presentation.ofIsIso {M N : SheafOfModules.{u} R} (f : M ⟶ N) [IsIso f]
    (σ : M.Presentation) : N.Presentation where
  generators := σ.generators.ofEpi f
  relations := σ.relations.ofEpi ((kernelCompMono _ f).symm.trans <| eqToIso (by simp)).hom

@[deprecated (since := "2026-04-15")] alias Presentation.of_isIso := Presentation.ofIsIso

set_option backward.isDefEq.respectTransparency.types false in
instance {M N : SheafOfModules.{u} R} (f : M ⟶ N) [IsIso f]
    (σ : M.Presentation) [σ.IsFinite] : (σ.ofIsIso f).IsFinite where
  isFiniteType_generators := inferInstanceAs (σ.generators.ofEpi _).IsFiniteType
  isFiniteType_relations := inferInstanceAs (σ.relations.ofEpi _).IsFiniteType

variable {C' : Type u₂} [Category.{v₂} C'] {J' : GrothendieckTopology C'} {S : Sheaf J' RingCat.{u}}
  [HasSheafify J' AddCommGrpCat] [J'.WEqualsLocallyBijective AddCommGrpCat]

variable {M : SheafOfModules.{u} R} (P : Presentation M)
  (F : SheafOfModules.{u} R ⥤ SheafOfModules.{u} S) [PreservesColimitsOfSize.{u, u} F]
  (η : unit S ≅ F.obj (unit R))

-- `preservesColimitsOfSize_shrink` is not a global instance because it loops indefinitely.
-- But here it is fine as an instance since the universe `u` is inferrable from the type of `F`.
local instance : PreservesColimitsOfSize.{0, 0} F := preservesColimitsOfSize_shrink _

/--
Definition of `Presentation.mapRelations` / `Presentation.mapRelations` 的定义

English:
definition Presentation.mapRelations
  signature: : free P.relations.I (R := S) ⟶ free P.generators.I
  body: (mapFreeIso F P.relations.I η).hom ≫ F.map ((freeHomEquiv _).symm P.relations.s) ≫
    F.map (kernel.ι _) ≫ (mapFreeIso F P.generators.I η).inv

中文:
定义 Presentation.mapRelations
  签名: : free P.relations.I (R := S) ⟶ free P.generators.I
  定义体: (mapFreeIso F P.relations.I η).hom ≫ F.map ((freeHomEquiv _).symm P.relations.s) ≫
    F.map (kernel.ι _) ≫ (mapFreeIso F P.generators.I η).inv

Depends on / 依赖: P.generators.I, generators
-/
def Presentation.mapRelations : free P.relations.I (R := S) ⟶ free P.generators.I :=
  (mapFreeIso F P.relations.I η).hom ≫ F.map ((freeHomEquiv _).symm P.relations.s) ≫
    F.map (kernel.ι _) ≫ (mapFreeIso F P.generators.I η).inv

/--
Definition of `Presentation.mapGenerators` / `Presentation.mapGenerators` 的定义

English:
abbreviation Presentation.mapGenerators
  signature: : free P.generators.I ⟶ F.obj M
  body: P.generators.mapFreeHom F η

@[reassoc (attr := simp)]

中文:
缩写 Presentation.mapGenerators
  签名: : free P.generators.I ⟶ F.obj M
  定义体: P.generators.mapFreeHom F η

@[reassoc (attr := simp)]

Depends on / 依赖: P.generators.mapFreeHom, generators, mapFreeHom
-/
abbrev Presentation.mapGenerators : free P.generators.I ⟶ F.obj M := P.generators.mapFreeHom F η

@[reassoc (attr := simp)]
/--
theorem `Presentation.mapRelations_mapGenerators` / 定理 `Presentation.mapRelations_mapGenerators`

English:
theorem Presentation.mapRelations_mapGenerators
  proof: by
  simp only [mapRelations, GeneratingSections.mapFreeHom, Category.assoc, Iso.inv_hom_id_assoc,
    ← Functor.map_comp, kernel.condition, Functor.map_zero, comp_zero]

中文:
定理 Presentation.mapRelations_mapGenerators
  证明: by
  simp only [mapRelations, GeneratingSections.mapFreeHom, Category.assoc, Iso.inv_hom_id_assoc,
    ← Functor.map_comp, kernel.condition, Functor.map_zero, comp_zero]

Depends on / 依赖: Category, Category.assoc, Functor, Functor.map_comp, Functor.map_zero, GeneratingSections, GeneratingSections.mapFreeHom, Iso.inv_hom_id_assoc, comp_zero, condition, inv_hom_id_assoc, kernel, kernel.condition, mapFreeHom, mapRelations, map_comp, map_zero
-/
theorem Presentation.mapRelations_mapGenerators :
    P.mapRelations F η ≫ P.mapGenerators F η = 0 := by
  simp only [mapRelations, GeneratingSections.mapFreeHom, Category.assoc, Iso.inv_hom_id_assoc,
    ← Functor.map_comp, kernel.condition, Functor.map_zero, comp_zero]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Let `F` be a functor from sheaf of `R`-module to sheaf of `S`-module, if `F` preserves
colimits and `F.obj (unit R) ≅ unit S`, given a `P : Presentation M`, then we will get a
`Presentation (F.obj M)`. -/
@[simps! generators_I relations_I]
/--
Definition of `Presentation.map` / `Presentation.map` 的定义

English:
definition Presentation.map
  signature: : Presentation (F.obj M)
  body: presentationOfIsCokernelFree (P.mapRelations F η) (P.mapGenerators F η)
(P.mapRelations_mapGenerators F η) by
    refine IsColimit.equivOfNatIsoOfIso
      (parallelPairIsoMk (mapFreeIso F _ η).symm (mapFreeIso F _ η).symm
        (by simp [Presentation.mapRelations]) (by simp)) _ _ ?_ (isColimitOfP

中文:
定义 Presentation.map
  签名: : Presentation (F.obj M)
  定义体: presentationOfIsCokernelFree (P.mapRelations F η) (P.mapGenerators F η)
(P.mapRelations_mapGenerators F η) by
    refine IsColimit.equivOfNatIsoOfIso
      (parallelPairIsoMk (mapFreeIso F _ η).symm (mapFreeIso F _ η).symm
        (by simp [Presentation.mapRelations]) (by simp)) _ _ ?_ (isColimitOfP

Depends on / 依赖: Cocone, Cocone.ext, Functor, Functor.map_comp, GeneratingSections, GeneratingSections.mapFreeHom, IsColimit, IsColimit.equivOfNatIsoOfIso, Iso.refl, P.isColimit, P.mapGenerators, P.mapRelations, P.mapRelations_mapGenerators, Presentation, Presentation.mapRelations, equivOfNatIsoOfIso, isColimit, isColimitOfPreserves, mapFreeHom, mapFreeIso
-/
def Presentation.map : Presentation (F.obj M) :=
  presentationOfIsCokernelFree (P.mapRelations F η) (P.mapGenerators F η)
(P.mapRelations_mapGenerators F η) by
    refine IsColimit.equivOfNatIsoOfIso
      (parallelPairIsoMk (mapFreeIso F _ η).symm (mapFreeIso F _ η).symm
        (by simp [Presentation.mapRelations]) (by simp)) _ _ ?_ (isColimitOfPreserves F P.isColimit)
    exact (Cocone.ext (Iso.refl _) <| by rintro (_ | _)
      <;> simp [Presentation.mapRelations, GeneratingSections.mapFreeHom, ← Functor.map_comp])

/--
theorem `Presentation.map_π_eq` / 定理 `Presentation.map_π_eq`

English:
theorem Presentation.map_π_eq
  proof: (F.obj M).freeHomEquiv.symm_apply_eq.mpr rfl

中文:
定理 Presentation.map_π_eq
  证明: (F.obj M).freeHomEquiv.symm_apply_eq.mpr rfl

Depends on / 依赖: F.obj, freeHomEquiv, freeHomEquiv.symm_apply_eq.mpr, symm_apply_eq
-/
theorem Presentation.map_π_eq :
    (P.map F η).generators.π = (mapFreeIso F _ η).hom ≫ F.map (P.generators.π) :=
  (F.obj M).freeHomEquiv.symm_apply_eq.mpr rfl

end

section

variable [forall X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [forall X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/--
Definition of `QuasicoherentData` / `QuasicoherentData` 的定义

English:
structure QuasicoherentData
  parameters: (M : SheafOfModules.{u} R)
  axioms and operations (4):
    - I : Type w
    - X : I -> C
    - coversTop : J.CoversTop X
    - presentation((i : I)) : (M.over (X i)).Presentation

中文:
结构 QuasicoherentData
  参数: (M : SheafOfModules.{u} R)
  公理与运算 (4 个):
    - I : Type w
    - X : I -> C
    - coversTop : J.CoversTop X
    - presentation((i : I)) : (M.over (X i)).Presentation
-/
structure QuasicoherentData (M : SheafOfModules.{u} R) where
  /-- the index type of the covering -/
  I : Type w
  /-- a family of objects which cover the terminal object -/
  X : I -> C
  coversTop : J.CoversTop X
  /-- a presentation of the sheaf of modules `M.over (X i)` for any `i : I` -/
  presentation (i : I) : (M.over (X i)).Presentation

namespace QuasicoherentData

/-- Shrink the indexing type of `QuasicoherentData` into the universe of the site. -/
noncomputable
/--
Definition of `shrink` / `shrink` 的定义

English:
definition shrink
  signature: {M : SheafOfModules.{u} R} (q : M.QuasicoherentData)
  body: Set.range q.X
  X i := q.X i.2.choose
  coversTop X := by
    refine J.superset_covering (fun Y hY H => ?_) (q.coversTop X)
    obtain ⟨i, ⟨hi⟩⟩ := (Sieve.mem_ofObjects_iff ..).mp H
    exact ⟨⟨_, i, rfl⟩, ⟨hi ≫ eqToHom (by grind)⟩⟩
  presentation i := q.presentation i.2.choose

中文:
定义 shrink
  签名: {M : SheafOfModules.{u} R} (q : M.QuasicoherentData)
  定义体: Set.range q.X
  X i := q.X i.2.choose
  coversTop X := by
    refine J.superset_covering (fun Y hY H => ?_) (q.coversTop X)
    obtain ⟨i, ⟨hi⟩⟩ := (Sieve.mem_ofObjects_iff ..).mp H
    exact ⟨⟨_, i, rfl⟩, ⟨hi ≫ eqToHom (by grind)⟩⟩
  presentation i := q.presentation i.2.choose

Depends on / 依赖: Set.range
-/
def shrink {M : SheafOfModules.{u} R} (q : M.QuasicoherentData) :
    QuasicoherentData.{u₁} M where
  I := Set.range q.X
  X i := q.X i.2.choose
  coversTop X := by
    refine J.superset_covering (fun Y hY H => ?_) (q.coversTop X)
    obtain ⟨i, ⟨hi⟩⟩ := (Sieve.mem_ofObjects_iff ..).mp H
    exact ⟨⟨_, i, rfl⟩, ⟨hi ≫ eqToHom (by grind)⟩⟩
  presentation i := q.presentation i.2.choose

/-- If `M` is quasicoherent, it is locally generated by sections. -/
@[simps]
/--
Definition of `localGeneratorsData` / `localGeneratorsData` 的定义

English:
definition localGeneratorsData
  signature: {M : SheafOfModules.{u} R} (q : M.QuasicoherentData)
  body: q.I
  X := q.X
  coversTop := q.coversTop
  generators i := (q.presentation i).generators

中文:
定义 localGeneratorsData
  签名: {M : SheafOfModules.{u} R} (q : M.QuasicoherentData)
  定义体: q.I
  X := q.X
  coversTop := q.coversTop
  generators i := (q.presentation i).generators

Depends on / 依赖: Function, Function.Injective.module, Hom.hom, Injective, hom_add, hom_injective, hom_zero, map_add, map_zero, module
-/
def localGeneratorsData {M : SheafOfModules.{u} R} (q : M.QuasicoherentData) :
    M.LocalGeneratorsData where
  I := q.I
  X := q.X
  coversTop := q.coversTop
  generators i := (q.presentation i).generators

/--
Definition of `IsFinitePresentation` / `IsFinitePresentation` 的定义

English:
class IsFinitePresentation
  parameters: {M : SheafOfModules.{u} R} (q : M.QuasicoherentData)
  axioms and operations (1):
    - isFinite_presentation((i : q.I)) : (q.presentation i).IsFinite  [default: by infer_instance]

中文:
类 IsFinitePresentation
  参数: {M : SheafOfModules.{u} R} (q : M.QuasicoherentData)
  公理与运算 (1 个):
    - isFinite_presentation((i : q.I)) : (q.presentation i).IsFinite  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
class IsFinitePresentation {M : SheafOfModules.{u} R} (q : M.QuasicoherentData) : Prop where
  isFinite_presentation (i : q.I) : (q.presentation i).IsFinite := by infer_instance

attribute [instance] IsFinitePresentation.isFinite_presentation

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance {M : SheafOfModules.{u} R} (q : M.QuasicoherentData) [q.IsFinitePresentation] :
    q.localGeneratorsData.IsFiniteType where
  isFiniteType := by dsimp; infer_instance

end QuasicoherentData

/--
Definition of `IsQuasicoherent` / `IsQuasicoherent` 的定义

English:
class IsQuasicoherent
  parameters: (M : SheafOfModules.{u} R)
  axioms and operations (1):
    - nonempty_quasicoherentData : Nonempty (QuasicoherentData.{u₁} M)  [default: by infer_instance]

中文:
类 IsQuasicoherent
  参数: (M : SheafOfModules.{u} R)
  公理与运算 (1 个):
    - nonempty_quasicoherentData : Nonempty (QuasicoherentData.{u₁} M)  [默认: by infer_instance]

Depends on / 依赖: Algebra, SemimoduleCat, SemimoduleCat.Algebra.instLinear, infer_instance, instLinear
-/
class IsQuasicoherent (M : SheafOfModules.{u} R) : Prop where
  nonempty_quasicoherentData : Nonempty (QuasicoherentData.{u₁} M) := by infer_instance

/--
lemma `QuasicoherentData.isQuasicoherent` / 引理 `QuasicoherentData.isQuasicoherent`

English:
lemma QuasicoherentData.isQuasicoherent
  given: {M : SheafOfModules.{u} R} (q : M.QuasicoherentData)
  proof: ⟨⟨q.shrink⟩⟩

中文:
引理 QuasicoherentData.isQuasicoherent
  条件: {M : SheafOfModules.{u} R} (q : M.QuasicoherentData)
  证明: ⟨⟨q.shrink⟩⟩

Depends on / 依赖: q.shrink, shrink
-/
lemma QuasicoherentData.isQuasicoherent {M : SheafOfModules.{u} R} (q : M.QuasicoherentData) :
    M.IsQuasicoherent := ⟨⟨q.shrink⟩⟩

variable (R) in
@[inherit_doc IsQuasicoherent]
/--
Definition of `isQuasicoherent` / `isQuasicoherent` 的定义

English:
abbreviation isQuasicoherent
  signature: : ObjectProperty (SheafOfModules.{u} R)
  body: IsQuasicoherent

中文:
缩写 isQuasicoherent
  签名: : Object命题erty (SheafOfModules.{u} R)
  定义体: IsQuasicoherent

Depends on / 依赖: IsQuasicoherent
-/
abbrev isQuasicoherent : ObjectProperty (SheafOfModules.{u} R) :=
  IsQuasicoherent

instance (M : (isQuasicoherent R).FullSubcategory) : M.obj.IsQuasicoherent :=
  M.property

/--
Definition of `IsFinitePresentation` / `IsFinitePresentation` 的定义

English:
class IsFinitePresentation
  parameters: (M : SheafOfModules.{u} R)
  axioms and operations (1):
    - exists_quasicoherentData((M)) : exists (σ : QuasicoherentData.{u₁} M), σ.IsFinitePresentation

中文:
类 IsFinitePresentation
  参数: (M : SheafOfModules.{u} R)
  公理与运算 (1 个):
    - exists_quasicoherentData((M)) : 存在 (σ : QuasicoherentData.{u₁} M), σ.IsFinitePresentation
-/
class IsFinitePresentation (M : SheafOfModules.{u} R) : Prop where
  exists_quasicoherentData (M) :
    exists (σ : QuasicoherentData.{u₁} M), σ.IsFinitePresentation

variable (R) in
@[inherit_doc IsFinitePresentation]
/--
Definition of `isFinitePresentation` / `isFinitePresentation` 的定义

English:
abbreviation isFinitePresentation
  signature: : ObjectProperty (SheafOfModules.{u} R)
  body: IsFinitePresentation

中文:
缩写 isFinitePresentation
  签名: : Object命题erty (SheafOfModules.{u} R)
  定义体: IsFinitePresentation

Depends on / 依赖: IsFinitePresentation
-/
abbrev isFinitePresentation : ObjectProperty (SheafOfModules.{u} R) :=
  IsFinitePresentation

instance (M : SheafOfModules.{u} R) [M.IsFinitePresentation] :
    M.IsQuasicoherent where
  nonempty_quasicoherentData :=
    ⟨(IsFinitePresentation.exists_quasicoherentData M).choose⟩

instance (M : SheafOfModules.{u} R) [M.IsFinitePresentation] :
    M.IsFiniteType where
  exists_localGeneratorsData := by
    obtain ⟨σ, _⟩ := IsFinitePresentation.exists_quasicoherentData M
    exact ⟨σ.localGeneratorsData, inferInstance⟩

section map

variable {D : Type u₂} [Category.{v₂, u₂} D] {K : GrothendieckTopology D}
  {S : Sheaf K RingCat.{u}} [forall (X : D), (K.over X).WEqualsLocallyBijective AddCommGrpCat]

variable [forall (X : C), HasSheafify (J.over X) AddCommGrpCat.{u}]
  [forall (X : D), HasSheafify (K.over X) AddCommGrpCat.{u}]

variable (G : D ⥤ C) [G.IsContinuous K J] [G.IsCocontinuous K J]
  (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{u} K J).obj R)

/-- The pushforward of `SheafOfModules.QuasicoherentData` along a continuous
and cocontinuous functor. -/
-- TODO: Remove the continuous assumption on `Over.post` here and below.
@[simps I X]
/--
Definition of `QuasicoherentData.pushforward` / `QuasicoherentData.pushforward` 的定义

English:
definition QuasicoherentData.pushforward
  signature: (η : (pushforward φ).obj (unit R) ≅ unit S)
  body: Σ (X : D) (i : P.I), G.obj X ⟶ P.X i
  X i := i.1
  coversTop Y := by
refine K.superset_covering ?_ G.cover_lift K _ (P.coversTop (G.obj Y))
    intro Z g ⟨i, ⟨v⟩⟩
    exact ⟨⟨Z, i, v⟩, ⟨𝟙 _⟩⟩
  presentation i := by
    letI overS : SheafOfModules.{u} S ⥤ SheafOfModules.{u} (S.over i.1) :=
      She

中文:
定义 QuasicoherentData.pushforward
  签名: (η : (pushforward φ).obj (unit R) ≅ unit S)
  定义体: Σ (X : D) (i : P.I), G.obj X ⟶ P.X i
  X i := i.1
  coversTop Y := by
refine K.superset_covering ?_ G.cover_lift K _ (P.coversTop (G.obj Y))
    intro Z g ⟨i, ⟨v⟩⟩
    exact ⟨⟨Z, i, v⟩, ⟨𝟙 _⟩⟩
  presentation i := by
    letI overS : SheafOfModules.{u} S ⥤ SheafOfModules.{u} (S.over i.1) :=
      She

Depends on / 依赖: Over.map, Over.post, R.over
-/
noncomputable def QuasicoherentData.pushforward (η : (pushforward φ).obj (unit R) ≅ unit S)
    [forall (X : D), (Over.post G).IsContinuous (K.over X) (J.over _)]
    (h : forall (X : D) (Y : C) (f : G.obj X ⟶ Y),
PreservesColimitsOfSize.{u, u}
      pushforward.{u} (R := (R.over Y)) (F := Over.post (X := X) G ⋙ Over.map f)
        (((Over.forget X).sheafPushforwardContinuous RingCat.{u} (K.over X) K).map φ))
    {M : SheafOfModules.{u} R} (P : M.QuasicoherentData) :
    QuasicoherentData ((pushforward φ).obj M) where
  I := Σ (X : D) (i : P.I), G.obj X ⟶ P.X i
  X i := i.1
  coversTop Y := by
refine K.superset_covering ?_ G.cover_lift K _ (P.coversTop (G.obj Y))
    intro Z g ⟨i, ⟨v⟩⟩
    exact ⟨⟨Z, i, v⟩, ⟨𝟙 _⟩⟩
  presentation i := by
    letI overS : SheafOfModules.{u} S ⥤ SheafOfModules.{u} (S.over i.1) :=
      SheafOfModules.pushforward (𝟙 _)
    letI G' := Over.post (X := i.1) G ⋙ Over.map i.2.2
    letI ψ : S.over i.1 ⟶
        (G'.sheafPushforwardContinuous RingCat.{u} (K.over i.1) (J.over (P.X i.2.1))).obj
          (R.over (P.X i.2.1)) :=
      ((Over.forget i.1).sheafPushforwardContinuous RingCat.{u} (K.over i.1) K).map φ
    letI e : (SheafOfModules.pushforward ψ).obj (unit (R.over (P.X i.snd.fst))) ≅
      unit (S.over i.fst) := overS.mapIso η
    haveI : PreservesColimitsOfSize.{u, u, _} (SheafOfModules.pushforward ψ) := h _ _ _
    exact (P.presentation i.2.1).map (SheafOfModules.pushforward ψ) e.symm

/--
lemma `isQuasicoherent_pushforward` / 引理 `isQuasicoherent_pushforward`

English:
lemma isQuasicoherent_pushforward
  statement: (η : (pushforward φ).obj (unit R) ≅ unit S)
  proof: .isQuasicoherent IsQuasicoherent.nonempty_quasicoherentData.some.pushforward G φ η h

中文:
引理 isQuasicoherent_pushforward
  结论: (η : (pushforward φ).obj (unit R) ≅ unit S)
  证明: .isQuasicoherent IsQuasicoherent.nonempty_quasicoherentData.some.pushforward G φ η h

Depends on / 依赖: Over.map, Over.post, R.over, homLinearEquiv, homLinearEquiv.toLinearMap, toLinearMap
-/
lemma isQuasicoherent_pushforward (η : (pushforward φ).obj (unit R) ≅ unit S)
    [forall (X : D), (Over.post G).IsContinuous (K.over X) (J.over _)]
    (h : forall (X : D) (Y : C) (f : G.obj X ⟶ Y),
PreservesColimitsOfSize.{u, u}
      pushforward.{u} (R := (R.over Y)) (F := Over.post (X := X) G ⋙ Over.map f)
        (((Over.forget X).sheafPushforwardContinuous RingCat.{u} (K.over X) K).map φ))
    {M : SheafOfModules.{u} R} [IsQuasicoherent M] :
    IsQuasicoherent ((pushforward φ).obj M) :=
.isQuasicoherent IsQuasicoherent.nonempty_quasicoherentData.some.pushforward G φ η h

set_option backward.isDefEq.respectTransparency false in
/--
lemma `isQuasicoherent_pushforward_of_isLeftAdjoint` / 引理 `isQuasicoherent_pushforward_of_isLeftAdjoint`

English:
lemma isQuasicoherent_pushforward_of_isLeftAdjoint
  statement: (η : (pushforward φ).obj (unit R) ≅ unit S)
  proof: by
  apply +allowSynthFailures isQuasicoherent_pushforward G φ η _
  intro X Y f
  let G' := Over.post (X := X) G ⋙ Over.map f
  have : G'.IsContinuous (K.over X) (J.over Y) := Functor.isContinuous_comp _ _ _ (J.over _) _
  have : G'.IsCocontinuous (K.over X) (J.over Y) := isCocontinuous_comp _ _ _ 

中文:
引理 isQuasicoherent_pushforward_of_isLeftAdjoint
  结论: (η : (pushforward φ).obj (unit R) ≅ unit S)
  证明: by
  apply +allowSynthFailures isQuasicoherent_pushforward G φ η _
  intro X Y f
  let G' := Over.post (X := X) G ⋙ Over.map f
  have : G'.IsContinuous (K.over X) (J.over Y) := Functor.isContinuous_comp _ _ _ (J.over _) _
  have : G'.IsCocontinuous (K.over X) (J.over Y) := isCocontinuous_comp _ _ _ 

Depends on / 依赖: J.over, K.over
-/
lemma isQuasicoherent_pushforward_of_isLeftAdjoint (η : (pushforward φ).obj (unit R) ≅ unit S)
    [G.IsLeftAdjoint] [IsIso φ]
    [forall X, Functor.IsContinuous (Over.post (X := X) G) (K.over _) (J.over _)]
    [HasPullbacks C] [HasPullbacks D]
    {M : SheafOfModules.{u} R} [IsQuasicoherent M] :
    IsQuasicoherent ((pushforward φ).obj M) := by
  apply +allowSynthFailures isQuasicoherent_pushforward G φ η _
  intro X Y f
  let G' := Over.post (X := X) G ⋙ Over.map f
  have : G'.IsContinuous (K.over X) (J.over Y) := Functor.isContinuous_comp _ _ _ (J.over _) _
  have : G'.IsCocontinuous (K.over X) (J.over Y) := isCocontinuous_comp _ _ _ (J.over _)
  let a : S.over X ⟶
      (G'.sheafPushforwardContinuous RingCat.{u} (K.over X) (J.over Y)).obj (R.over Y) :=
    ((Over.forget X).sheafPushforwardContinuous RingCat.{u} (K.over X) K).map φ
  have : (pushforward.{u} a).IsLeftAdjoint := isLeftAdjoint_pushforward_of_isIso a
  infer_instance

end map

end

noncomputable section

open CategoryTheory Limits

variable {C : Type u₁} [Category.{v₁} C] [HasBinaryProducts C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}} [HasSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat]

variable [forall X, HasSheafify (J.over X) AddCommGrpCat]
  [forall X, (J.over X).WEqualsLocallyBijective AddCommGrpCat]

/-- Given a sheaf of `R`-modules `M` and a `Presentation M`, we may construct the quasi-coherent
data on the trivial cover. -/
@[simps]
/--
Definition of `Presentation.quasicoherentData` / `Presentation.quasicoherentData` 的定义

English:
definition Presentation.quasicoherentData
  signature: {M : SheafOfModules.{u} R} (P : Presentation M)
  body: C
  X := id
coversTop x := GrothendieckTopology.covering_of_eq_top J by
    rw [Sieve.ext_iff]
    intro _ f
    simp [Sieve.top_apply]
  presentation x := P.map (pushforward (𝟙 (R.over x))) (by rfl)

中文:
定义 Presentation.quasicoherentData
  签名: {M : SheafOfModules.{u} R} (P : Presentation M)
  定义体: C
  X := id
coversTop x := GrothendieckTopology.covering_of_eq_top J by
    rw [Sieve.ext_iff]
    intro _ f
    simp [Sieve.top_apply]
  presentation x := P.map (pushforward (𝟙 (R.over x))) (by rfl)
-/
def Presentation.quasicoherentData {M : SheafOfModules.{u} R} (P : Presentation M) :
    QuasicoherentData M where
  I := C
  X := id
coversTop x := GrothendieckTopology.covering_of_eq_top J by
    rw [Sieve.ext_iff]
    intro _ f
    simp [Sieve.top_apply]
  presentation x := P.map (pushforward (𝟙 (R.over x))) (by rfl)

/--
theorem `Presentation.isQuasicoherent` / 定理 `Presentation.isQuasicoherent`

English:
theorem Presentation.isQuasicoherent
  given: {M : SheafOfModules.{u} R} (P : Presentation M)
  proof: Nonempty.intro (Presentation.quasicoherentData P)

中文:
定理 Presentation.isQuasicoherent
  条件: {M : SheafOfModules.{u} R} (P : Presentation M)
  证明: Nonempty.intro (Presentation.quasicoherentData P)

Depends on / 依赖: Nonempty, Nonempty.intro, Presentation, Presentation.quasicoherentData, quasicoherentData
-/
theorem Presentation.isQuasicoherent {M : SheafOfModules.{u} R} (P : Presentation M) :
    IsQuasicoherent M where
  nonempty_quasicoherentData := Nonempty.intro (Presentation.quasicoherentData P)

/-- Mapping quasicoherent data under an isomorphism. -/
@[simps]
/--
Definition of `QuasicoherentData.ofIsIso` / `QuasicoherentData.ofIsIso` 的定义

English:
definition QuasicoherentData.ofIsIso
  signature: {M N : SheafOfModules.{u} R} (f : M ⟶ N) [IsIso f]
  body: σ.I
  X := σ.X
  coversTop := σ.coversTop
  presentation i := Presentation.ofIsIso (f.over (σ.X i)) (σ.presentation i)

中文:
定义 QuasicoherentData.ofIsIso
  签名: {M N : SheafOfModules.{u} R} (f : M ⟶ N) [IsIso f]
  定义体: σ.I
  X := σ.X
  coversTop := σ.coversTop
  presentation i := Presentation.ofIsIso (f.over (σ.X i)) (σ.presentation i)
-/
noncomputable def QuasicoherentData.ofIsIso {M N : SheafOfModules.{u} R} (f : M ⟶ N) [IsIso f]
    (σ : M.QuasicoherentData) : N.QuasicoherentData where
  I := σ.I
  X := σ.X
  coversTop := σ.coversTop
  presentation i := Presentation.ofIsIso (f.over (σ.X i)) (σ.presentation i)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (isQuasicoherent R).IsClosedUnderIsomorphisms
  body: by
    intro ⟨⟨q⟩⟩
    exact ⟨⟨q.ofIsIso e.hom⟩⟩

中文:
实例 :
  签名: (isQuasicoherent R).IsClosedUnderIsomorphisms
  定义体: by
    intro ⟨⟨q⟩⟩
    exact ⟨⟨q.ofIsIso e.hom⟩⟩

Depends on / 依赖: e.hom, ofIsIso, q.ofIsIso
-/
instance : (isQuasicoherent R).IsClosedUnderIsomorphisms where
  of_iso e := by
    intro ⟨⟨q⟩⟩
    exact ⟨⟨q.ofIsIso e.hom⟩⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
instance {M N : SheafOfModules.{u} R} (f : M ⟶ N) [IsIso f] (σ : M.QuasicoherentData)
    [σ.IsFinitePresentation] : (σ.ofIsIso f).IsFinitePresentation where
  isFinite_presentation i := by
    dsimp
    exact inferInstanceAs ((σ.presentation i).ofIsIso _).IsFinite

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (isFinitePresentation R).IsClosedUnderIsomorphisms
  body: by
    intro ⟨σ, hσ⟩
    exact ⟨σ.ofIsIso e.hom, inferInstance⟩

中文:
实例 :
  签名: (isFinitePresentation R).IsClosedUnderIsomorphisms
  定义体: by
    intro ⟨σ, hσ⟩
    exact ⟨σ.ofIsIso e.hom, inferInstance⟩

Depends on / 依赖: e.hom, ofIsIso
-/
instance : (isFinitePresentation R).IsClosedUnderIsomorphisms where
  of_iso e := by
    intro ⟨σ, hσ⟩
    exact ⟨σ.ofIsIso e.hom, inferInstance⟩

end

section bind

variable [forall X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [forall X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [forall X Y, HasSheafify ((J.over X).over Y) AddCommGrpCat.{u}]
  [forall X Y, ((J.over X).over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]

/--
Definition of `QuasicoherentData.bind` / `QuasicoherentData.bind` 的定义

English:
definition QuasicoherentData.bind
  signature: {R : Sheaf J RingCat.{u}}
  body: (i : I) × (D i).I
  X ij := ((D ij.1).X ij.2).left
  coversTop := hX.over (fun i => (D i).coversTop)
  presentation i :=
    letI e := pushforwardPushforwardEquivalence (Over.iteratedSliceEquiv ((D i.1).X i.2))
      (S := (R.over _).over _) (R := R.over _) (𝟙 _) (𝟙 _)
      (by ext : 2; exact R.1.m

中文:
定义 QuasicoherentData.bind
  签名: {R : Sheaf J RingCat.{u}}
  定义体: (i : I) × (D i).I
  X ij := ((D ij.1).X ij.2).left
  coversTop := hX.over (fun i => (D i).coversTop)
  presentation i :=
    letI e := pushforwardPushforwardEquivalence (Over.iteratedSliceEquiv ((D i.1).X i.2))
      (S := (R.over _).over _) (R := R.over _) (𝟙 _) (𝟙 _)
      (by ext : 2; exact R.1.m
-/
noncomputable def QuasicoherentData.bind {R : Sheaf J RingCat.{u}}
    (M : SheafOfModules.{u} R) {I : Type u}
    (X : I -> C) (hX : J.CoversTop X) (D : Π i, QuasicoherentData (M.over (X i))) :
    M.QuasicoherentData where
  I := (i : I) × (D i).I
  X ij := ((D ij.1).X ij.2).left
  coversTop := hX.over (fun i => (D i).coversTop)
  presentation i :=
    letI e := pushforwardPushforwardEquivalence (Over.iteratedSliceEquiv ((D i.1).X i.2))
      (S := (R.over _).over _) (R := R.over _) (𝟙 _) (𝟙 _)
      (by ext : 2; exact R.1.map_id _) (by ext : 2; exact R.1.map_id _)
    (((D i.1).presentation i.2).map e.inverse (.refl _)).ofIsIso
      (e.fullyFaithfulFunctor.preimageIso
      (by exact e.counitIso.app ((M.over (X i.1)).over ((D i.1).X i.2)))).hom

/--
lemma `IsQuasicoherent.of_coversTop` / 引理 `IsQuasicoherent.of_coversTop`

English:
lemma IsQuasicoherent.of_coversTop
  statement: {R : Sheaf J RingCat.{u}}
  proof: (QuasicoherentData.bind M X hX fun _ =>
    IsQuasicoherent.nonempty_quasicoherentData.some).isQuasicoherent

中文:
引理 IsQuasicoherent.of_coversTop
  结论: {R : Sheaf J RingCat.{u}}
  证明: (QuasicoherentData.bind M X hX fun _ =>
    IsQuasicoherent.nonempty_quasicoherentData.some).isQuasicoherent

Depends on / 依赖: IsQuasicoherent, IsQuasicoherent.nonempty_quasicoherentData.some, QuasicoherentData, QuasicoherentData.bind, isQuasicoherent, nonempty_quasicoherentData
-/
lemma IsQuasicoherent.of_coversTop {R : Sheaf J RingCat.{u}}
    (M : SheafOfModules.{u} R) {I : Type u}
    (X : I -> C) (hX : J.CoversTop X) [forall i, IsQuasicoherent (M.over (X i))] :
    IsQuasicoherent M :=
  (QuasicoherentData.bind M X hX fun _ =>
    IsQuasicoherent.nonempty_quasicoherentData.some).isQuasicoherent

set_option backward.isDefEq.respectTransparency false in
/--
lemma `isQuasicoherent_over` / 引理 `isQuasicoherent_over`

English:
lemma isQuasicoherent_over
  proof: isQuasicoherent_pushforward_of_isLeftAdjoint _ _ (Iso.refl _)

中文:
引理 isQuasicoherent_over
  证明: isQuasicoherent_pushforward_of_isLeftAdjoint _ _ (Iso.refl _)

Depends on / 依赖: Iso.refl, isQuasicoherent_pushforward_of_isLeftAdjoint
-/
lemma isQuasicoherent_over
    [HasPullbacks C] [HasBinaryProducts C] (M : SheafOfModules.{u} R) (X : C) [IsQuasicoherent M] :
    IsQuasicoherent (M.over X) :=
  isQuasicoherent_pushforward_of_isLeftAdjoint _ _ (Iso.refl _)

end bind

end SheafOfModules
