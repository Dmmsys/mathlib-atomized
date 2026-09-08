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

/-- A global presentation of a sheaf of modules `M` consists of a family `generators.s`
of sections `s` which generate `M`, and a family of sections which generate
the kernel of the morphism `generators.π : free (generators.I) ⟶ M`. -/
/-
**SheafOfModules.Presentation** 是 Mathlib 中的一个归纳类型，位于命名空间 `SheafOfModules`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {J : C
ategoryTheory.GrothendieckTopology C} →       {R : CategoryTheory.Sheaf J RingCa
t} →         [CategoryTheory.HasWeakSheafify J AddCommGrpCat] →           [J.WEq
ualsLocallyBijective AddCommGrpCat] → SheafOfModules R → Type (max (u + 1) u₁)
参数：max (u + 1) u₁。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A global presentation of a sheaf of modules `M` consists of a family `generators
.s`
of sections `s` which generate `M`, and a family of sections which generate
the kernel of the morphism `generators.π : free (generators.I) ⟶ M`.
-/
structure Presentation (M : SheafOfModules.{u} R) where
  /-- generators -/
  generators : M.GeneratingSections
  /-- relations -/
  relations : (kernel generators.π).GeneratingSections

/-- A global presentation of a sheaf of module if finite if the type
of generators and relations are finite. -/
/-
**SheafOfModules.Presentation.IsFinite** 是 Mathlib 中的一个归纳类型，位于命名空间 `SheafOfModul
es.Presentation`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {J : C
ategoryTheory.GrothendieckTopology C} →       {R : CategoryTheory.Sheaf J RingCa
t} →         [inst_1 : CategoryTheory.HasWeakSheafify J AddCommGrpCat] →        
   [inst_2 : J.WEqualsLocallyBijective AddCommGrpCat] → {M : SheafOfModules R} →
 M.Presentation → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A global presentation of a sheaf of module if finite if the type
of generators and relations are finite.
-/
class Presentation.IsFinite {M : SheafOfModules.{u} R} (p : M.Presentation) : Prop where
  isFiniteType_generators : p.generators.IsFiniteType := by infer_instance
  isFiniteType_relations : p.relations.IsFiniteType := by infer_instance

attribute [instance] Presentation.IsFinite.isFiniteType_generators
  Presentation.IsFinite.isFiniteType_relations

@[deprecated Presentation.IsFinite.isFiniteType_relations (since := "2026-04-14")]
/-
**SheafOfModules.Presentation.IsFinite.finite_relations** 是 Mathlib 中的一个定理，位于命名空
间 `SheafOfModules.Presentation.IsFinite`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {J : CategoryT
heory.GrothendieckTopology C}   {R : CategoryTheory.Sheaf J RingCat} [inst_1 : C
ategoryTheory.HasWeakSheafify J AddCommGrpCat]   [inst_2 : J.WEqualsLocallyBijec
tive AddCommGrpCat] {M : SheafOfModules R} (p : M.Presentation) [p.IsFinite],   
Finite p.relations.I
参数：p : M.Presentation。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SheafOfModules.GeneratingSections.IsFiniteType.finite`：∀ {C : Type u'} {
inst : CategoryTheory.Category.{v', u'} C} {J : CategoryTheory.GrothendieckTopol
ogy C}   {R : CategoryTheory.Sheaf J RingCa…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `AddCommGrpCat.hasLimitsOfShape`：∀ {J : Type v} [inst : CategoryTheory.Ca
tegory.{w, v} J] [Small.{u, v} J],   CategoryTheory.Limits.HasLimitsOfShape J Ad
dCommGrpCat
· 使用定理 `SheafOfModules.Presentation.IsFinite.isFiniteType_relations`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {J : CategoryTheory.Grothendiec
kTopology C}   {R : CategoryTheory.Sheaf J RingCa…
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
/-
**SheafOfModules.generatorsOfIsCokernelFree** 是 Mathlib 中的一个定义，位于命名空间 `SheafOfMo
dules`。
形式化陈述：generatorsOfIsCokernelFree {M : SheafOfModules.{u} R} (f : free ι ⟶ free σ
) (g : free σ ⟶ M) (H : f ≫ g = 0) (H' : IsColimit (CokernelCofork.ofπ g H)) : M
.GeneratingSections where I
参数：f : free ι ⟶ free σ；g : free σ ⟶ M；H : f ≫ g = 0；H' : IsColimit (CokernelCofo
rk.ofπ g H)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instHasWeakSheafifyOfHasSheafify`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] (J : CategoryTheory.GrothendieckTopology C)
 (A : Type u₂)   [inst_1 : CategoryTh…

--- 原说明 ---
Given two morphisms of sheaves of `R`-modules `f : free ι ⟶ free σ` and `g : fre
e σ ⟶ M`
satisfying `H : f ≫ g = 0` and `IsColimit (CokernelCofork.ofπ g H)`, we obtain
generators of `Presentation M`.
-/
def generatorsOfIsCokernelFree {M : SheafOfModules.{u} R}
    (f : free ι ⟶ free σ) (g : free σ ⟶ M) (H : f ≫ g = 0)
    (H' : IsColimit (CokernelCofork.ofπ g H)) : M.GeneratingSections where
  I := σ
  s := M.freeHomEquiv g
  epi := by simpa using! epi_of_isColimit_cofork H'

@[simp]
/-
**SheafOfModules.generatorsOfIsCokernelFree_** 是 Mathlib 中的一个定理，位于命名空间 `SheafOfM
odules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**SheafOfModules.relationsOfIsCokernelFree** 是 Mathlib 中的一个定义，位于命名空间 `SheafOfMod
ules`。
形式化陈述：relationsOfIsCokernelFree {M : SheafOfModules.{u} R} (f : free ι ⟶ free σ)
 (g : free σ ⟶ M) (H : f ≫ g = 0) (H' : IsColimit (CokernelCofork.ofπ g H)) : (k
ernel (generatorsOfIsCokernelFree f g H H').π).GeneratingSections where I
参数：f : free ι ⟶ free σ；g : free σ ⟶ M；H : f ≫ g = 0；H' : IsColimit (CokernelCofo
rk.ofπ g H)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instHasWeakSheafifyOfHasSheafify`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] (J : CategoryTheory.GrothendieckTopology C)
 (A : Type u₂)   [inst_1 : CategoryTh…

--- 原说明 ---
Given two morphisms of sheaves of `R`-modules `f : free ι ⟶ free σ` and `g : fre
e σ ⟶ M`
satisfying `H : f ≫ g = 0` and `IsColimit (CokernelCofork.ofπ g H)`, we obtain
relations of `Presentation M`.
-/
def relationsOfIsCokernelFree {M : SheafOfModules.{u} R}
    (f : free ι ⟶ free σ) (g : free σ ⟶ M) (H : f ≫ g = 0)
    (H' : IsColimit (CokernelCofork.ofπ g H)) :
    (kernel (generatorsOfIsCokernelFree f g H H').π).GeneratingSections where
  I := ι
  s := (kernel (generatorsOfIsCokernelFree f g H H').π).freeHomEquiv <| kernel.lift
    (generatorsOfIsCokernelFree f g H H').π f (by simp [H])
  epi := by
    let h : cokernel f ≅ M := (H'.coconePointUniqueUpToIso (colimit.isColimit _)).symm
    let h' : Abelian.image f ≅ kernel (generatorsOfIsCokernelFree f g H H').π :=
      kernel.mapIso (cokernel.π f) (generatorsOfIsCokernelFree f g H H').π
        (Iso.refl _) h (by simp [h])
    have comp_aux : Abelian.factorThruImage f ≫ h'.hom =
      (kernel.lift (generatorsOfIsCokernelFree f g H H').π f (by simp [H])) :=
        equalizer.hom_ext <| by simp [h']
    rw [← comp_aux, Equiv.symm_apply_apply]
    infer_instance

/-- Given two morphisms of sheaves of `R`-modules `f : free ι ⟶ free σ` and `g : free σ ⟶ M`
satisfying `H : f ≫ g = 0` and `IsColimit (CokernelCofork.ofπ g H)`, we obtain a
`Presentation M`. -/
@[simps]
/-
**SheafOfModules.presentationOfIsCokernelFree** 是 Mathlib 中的一个定义，位于命名空间 `SheafOf
Modules`。
形式化陈述：presentationOfIsCokernelFree {M : SheafOfModules.{u} R} (f : free ι ⟶ free
 σ) (g : free σ ⟶ M) (H : f ≫ g = 0) (H' : IsColimit (CokernelCofork.ofπ g H)) :
 Presentation M where generators
参数：f : free ι ⟶ free σ；g : free σ ⟶ M；H : f ≫ g = 0；H' : IsColimit (CokernelCofo
rk.ofπ g H)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instHasWeakSheafifyOfHasSheafify`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] (J : CategoryTheory.GrothendieckTopology C)
 (A : Type u₂)   [inst_1 : CategoryTh…

--- 原说明 ---
Given two morphisms of sheaves of `R`-modules `f : free ι ⟶ free σ` and `g : fre
e σ ⟶ M`
satisfying `H : f ≫ g = 0` and `IsColimit (CokernelCofork.ofπ g H)`, we obtain a
`Presentation M`.
-/
def presentationOfIsCokernelFree {M : SheafOfModules.{u} R}
    (f : free ι ⟶ free σ) (g : free σ ⟶ M) (H : f ≫ g = 0)
    (H' : IsColimit (CokernelCofork.ofπ g H)) : Presentation M where
  generators := generatorsOfIsCokernelFree f g H H'
  relations := relationsOfIsCokernelFree f g H H'

/-- Given a sheaf of `R`-modules `M` and a `Presentation M`, there is two morphism of
sheaves of `R`-modules `f : free ι ⟶ free σ` and `g : free σ ⟶ M` satisfying `H : f ≫ g = 0`
and `IsColimit (CokernelCofork.ofπ g H)`. -/
/-
**SheafOfModules.Presentation.isColimit** 是 Mathlib 中的一个定义，位于命名空间 `SheafOfModule
s.Presentation`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {J : C
ategoryTheory.GrothendieckTopology C} →       {R : CategoryTheory.Sheaf J RingCa
t} →         [inst_1 : CategoryTheory.HasSheafify J AddCommGrpCat] →           [
inst_2 : J.WEqualsLocallyBijective AddCommGrpCat] →             {M : SheafOfModu
les R} →               (P : M.Presentation) →                 CategoryTheory.Lim
its.IsColimit (CategoryTheory.Limits.CokernelCofork.ofπ P.generators.π ⋯)
参数：P : M.Presentation；CategoryTheory.Limits.CokernelCofork.ofπ P.generators.π ⋯。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instHasWeakSheafifyOfHasSheafify`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] (J : CategoryTheory.GrothendieckTopology C)
 (A : Type u₂)   [inst_1 : CategoryTh…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Given a sheaf of `R`-modules `M` and a `Presentation M`, there is two morphism o
f
sheaves of `R`-modules `f : free ι ⟶ free σ` and `g : free σ ⟶ M` satisfying `H 
: f ≫ g = 0`
and `IsColimit (CokernelCofork.ofπ g H)`.
-/
def Presentation.isColimit {M : SheafOfModules.{u} R} (P : Presentation M) :
    IsColimit (CokernelCofork.ofπ (f := (freeHomEquiv _).symm P.relations.s ≫ (kernel.ι _))
      P.generators.π (by simp)) :=
  isCokernelEpiComp (c := CokernelCofork.ofπ _ (kernel.condition P.generators.π))
      (Abelian.epiIsCokernelOfKernel _ <| limit.isLimit _) _ rfl

set_option backward.defeqAttrib.useBackward true in
/-- Mapping a presentation under an isomorphism. -/
@[simps]
/-
**SheafOfModules.Presentation.ofIsIso** 是 Mathlib 中的一个定义，位于命名空间 `SheafOfModules.
Presentation`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {J : C
ategoryTheory.GrothendieckTopology C} →       {R : CategoryTheory.Sheaf J RingCa
t} →         [inst_1 : CategoryTheory.HasSheafify J AddCommGrpCat] →           [
inst_2 : J.WEqualsLocallyBijective AddCommGrpCat] →             {M N : SheafOfMo
dules R} → (f : M ⟶ N) → [CategoryTheory.IsIso f] → M.Presentation → N.Presentat
ion
参数：f : M ⟶ N。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instHasWeakSheafifyOfHasSheafify`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] (J : CategoryTheory.GrothendieckTopology C)
 (A : Type u₂)   [inst_1 : CategoryTh…

--- 原说明 ---
Mapping a presentation under an isomorphism.
-/
noncomputable def Presentation.ofIsIso {M N : SheafOfModules.{u} R} (f : M ⟶ N) [IsIso f]
    (σ : M.Presentation) : N.Presentation where
  generators := σ.generators.ofEpi f
  relations := σ.relations.ofEpi ((kernelCompMono _ f).symm.trans <| eqToIso (by simp)).hom

@[deprecated (since := "2026-04-15")] alias Presentation.of_isIso := Presentation.ofIsIso

set_option backward.isDefEq.respectTransparency.types false in
/-
**SheafOfModules.** 是 Mathlib 中的一个实例，位于命名空间 `SheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
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

/-- Let `F` be a functor from sheaf of `R`-module to sheaf of `S`-module, if `F` preserves
colimits and `F.obj (unit R) ≅ unit S`, given a `P : Presentation M`, then we will obtain
relations of `Presentation (F.obj M)`. -/
/-
**SheafOfModules.Presentation.mapRelations** 是 Mathlib 中的一个定义，位于命名空间 `SheafOfMod
ules.Presentation`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {J : C
ategoryTheory.GrothendieckTopology C} →       {R : CategoryTheory.Sheaf J RingCa
t} →         [inst_1 : CategoryTheory.HasSheafify J AddCommGrpCat] →           [
inst_2 : J.WEqualsLocallyBijective AddCommGrpCat] →             {C' : Type u₂} →
               [inst_3 : CategoryTheory.Category.{v₂, u₂} C'] →                 
{J' : CategoryTheory.GrothendieckTopology C'} →                   {S : CategoryT
heory.Sheaf J' RingCat} →                     [inst_4 : CategoryTheory.HasSheafi
fy J' AddCommGrpCat] →                       [inst_5 : J'.WEqualsLocallyBijectiv
e AddCommGrpCat] →                         {M : SheafOfModules R} →             
              (P : M.Presentation) →                             (F : CategoryTh
eory.Functor (SheafOfModules R) (SheafOfModules S)) →                           
    [CategoryTheory.Limits.PreservesColimitsOfSize.{u, u, max u u₁, max u u₂,   
                                    max (max (u + 1) u₁) v₁, max (max (u + 1) u₂
) v₂}                                     F] →                                 (
SheafOfModules.unit S ≅ F.obj (SheafOfModules.unit R)) →                        
           (SheafOfModules.free P.relations.I ⟶ SheafOfModules.free P.generators
.I)
参数：P : M.Presentation；F : CategoryTheory.Functor (SheafOfModules R) (SheafOfModu
les S)；max (u + 1) u₁；max (u + 1) u₂；SheafOfModules.unit S ≅ F.obj (SheafOfModul
es.unit R)；SheafOfModules.free P.relations.I ⟶ SheafOfModules.free P.generators.
I。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instHasWeakSheafifyOfHasSheafify`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] (J : CategoryTheory.GrothendieckTopology C)
 (A : Type u₂)   [inst_1 : CategoryTh…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Let `F` be a functor from sheaf of `R`-module to sheaf of `S`-module, if `F` pre
serves
colimits and `F.obj (unit R) ≅ unit S`, given a `P : Presentation M`, then we wi
ll obtain
relations of `Presentation (F.obj M)`.
-/
def Presentation.mapRelations : free P.relations.I (R := S) ⟶ free P.generators.I :=
  (mapFreeIso F P.relations.I η).hom ≫ F.map ((freeHomEquiv _).symm P.relations.s) ≫
    F.map (kernel.ι _) ≫ (mapFreeIso F P.generators.I η).inv

/-- Let `F` be a functor from sheaf of `R`-module to sheaf of `S`-module, if `F` preserves
colimits and `F.obj (unit R) ≅ unit S`, given a `P : Presentation M`, then we will obtain
generators of `Presentation (F.obj M)`. -/
/-
**SheafOfModules.Presentation.mapGenerators** 是 Mathlib 中的一个定义，位于命名空间 `SheafOfMo
dules.Presentation`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {J : C
ategoryTheory.GrothendieckTopology C} →       {R : CategoryTheory.Sheaf J RingCa
t} →         [inst_1 : CategoryTheory.HasSheafify J AddCommGrpCat] →           [
inst_2 : J.WEqualsLocallyBijective AddCommGrpCat] →             {C' : Type u₂} →
               [inst_3 : CategoryTheory.Category.{v₂, u₂} C'] →                 
{J' : CategoryTheory.GrothendieckTopology C'} →                   {S : CategoryT
heory.Sheaf J' RingCat} →                     [inst_4 : CategoryTheory.HasSheafi
fy J' AddCommGrpCat] →                       [inst_5 : J'.WEqualsLocallyBijectiv
e AddCommGrpCat] →                         {M : SheafOfModules R} →             
              (P : M.Presentation) →                             (F : CategoryTh
eory.Functor (SheafOfModules R) (SheafOfModules S)) →                           
    [CategoryTheory.Limits.PreservesColimitsOfSize.{u, u, max u u₁, max u u₂,   
                                    max (max (u + 1) u₁) v₁, max (max (u + 1) u₂
) v₂}                                     F] →                                 (
SheafOfModules.unit S ≅ F.obj (SheafOfModules.unit R)) →                        
           (SheafOfModules.free P.generators.I ⟶ F.obj M)
参数：P : M.Presentation；F : CategoryTheory.Functor (SheafOfModules R) (SheafOfModu
les S)；max (u + 1) u₁；max (u + 1) u₂；SheafOfModules.unit S ≅ F.obj (SheafOfModul
es.unit R)；SheafOfModules.free P.generators.I ⟶ F.obj M。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instHasWeakSheafifyOfHasSheafify`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] (J : CategoryTheory.GrothendieckTopology C)
 (A : Type u₂)   [inst_1 : CategoryTh…

--- 原说明 ---
Let `F` be a functor from sheaf of `R`-module to sheaf of `S`-module, if `F` pre
serves
colimits and `F.obj (unit R) ≅ unit S`, given a `P : Presentation M`, then we wi
ll obtain
generators of `Presentation (F.obj M)`.
-/
abbrev Presentation.mapGenerators : free P.generators.I ⟶ F.obj M := P.generators.mapFreeHom F η

@[reassoc (attr := simp)]
/-
**SheafOfModules.Presentation.mapRelations_mapGenerators** 是 Mathlib 中的一个定理，位于命名
空间 `SheafOfModules.Presentation`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {J : CategoryT
heory.GrothendieckTopology C}   {R : CategoryTheory.Sheaf J RingCat} [inst_1 : C
ategoryTheory.HasSheafify J AddCommGrpCat]   [inst_2 : J.WEqualsLocallyBijective
 AddCommGrpCat] {C' : Type u₂} [inst_3 : CategoryTheory.Category.{v₂, u₂} C']   
{J' : CategoryTheory.GrothendieckTopology C'} {S : CategoryTheory.Sheaf J' RingC
at}   [inst_4 : CategoryTheory.HasSheafify J' AddCommGrpCat] [inst_5 : J'.WEqual
sLocallyBijective AddCommGrpCat]   {M : SheafOfModules R} (P : M.Presentation) (
F : CategoryTheory.Functor (SheafOfModules R) (SheafOfModules S))   [inst_6 :   
  CategoryTheory.Limits.PreservesColimitsOfSize.{u, u, max u u₁, max u u₂, max (
max (u + 1) u₁) v₁,         max (max (u + 1) u₂) v₂}       F]   (η : SheafOfModu
les.unit S ≅ F.obj (SheafOfModules.unit R)),   CategoryTheory.CategoryStruct.com
p (P.mapRelations F η) (P.mapGenerators F η) = 0
参数：P : M.Presentation；F : CategoryTheory.Functor (SheafOfModules R) (SheafOfModu
les S)；max (u + 1) u₁；max (u + 1) u₂；η : SheafOfModules.unit S ≅ F.obj (SheafOfM
odules.unit R)；P.mapRelations F η；P.mapGenerators F η。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instHasWeakSheafifyOfHasSheafify`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] (J : CategoryTheory.GrothendieckTopology C)
 (A : Type u₂)   [inst_1 : CategoryTh…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `AddCommGrpCat.hasLimitsOfShape`：∀ {J : Type v} [inst : CategoryTheory.Ca
tegory.{w, v} J] [Small.{u, v} J],   CategoryTheory.Limits.HasLimitsOfShape J Ad
dCommGrpCat
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `SheafOfModules.GeneratingSections.mapFreeHom.eq_1`：∀ {C : Type u'} [inst
 : CategoryTheory.Category.{v', u'} C] {J : CategoryTheory.GrothendieckTopology 
C}   {R : CategoryTheory.Sheaf J RingCa…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.Limits.kernel.condition`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X 
Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Functor.map_zero`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   [inst_2 : Category…
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_preserves_initial_objec
t`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [in
st_1 : CategoryTheory.Category.{v₂, u₂} D]   [CategoryTheory.Li…
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteColimits.preservesFiniteColimits`：∀
 {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1
 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfSize0.preservesFiniteColimits`：
∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_
1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `SheafOfModules.instPreservesColimitsOfSize_1`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {J : CategoryTheory.GrothendieckTopology C}   
{R : CategoryTheory.Sheaf J RingCa…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
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
/-
**SheafOfModules.Presentation.map** 是 Mathlib 中的一个定义，位于命名空间 `SheafOfModules.Pres
entation`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {J : C
ategoryTheory.GrothendieckTopology C} →       {R : CategoryTheory.Sheaf J RingCa
t} →         [inst_1 : CategoryTheory.HasSheafify J AddCommGrpCat] →           [
inst_2 : J.WEqualsLocallyBijective AddCommGrpCat] →             {C' : Type u₂} →
               [inst_3 : CategoryTheory.Category.{v₂, u₂} C'] →                 
{J' : CategoryTheory.GrothendieckTopology C'} →                   {S : CategoryT
heory.Sheaf J' RingCat} →                     [inst_4 : CategoryTheory.HasSheafi
fy J' AddCommGrpCat] →                       [inst_5 : J'.WEqualsLocallyBijectiv
e AddCommGrpCat] →                         {M : SheafOfModules R} →             
              M.Presentation →                             (F : CategoryTheory.F
unctor (SheafOfModules R) (SheafOfModules S)) →                               [C
ategoryTheory.Limits.PreservesColimitsOfSize.{u, u, max u u₁, max u u₂,         
                              max (max (u + 1) u₁) v₁, max (max (u + 1) u₂) v₂} 
                                    F] →                                 (SheafO
fModules.unit S ≅ F.obj (SheafOfModules.unit R)) → (F.obj M).Presentation
参数：F : CategoryTheory.Functor (SheafOfModules R) (SheafOfModules S)；max (u + 1) 
u₁；max (u + 1) u₂；SheafOfModules.unit S ≅ F.obj (SheafOfModules.unit R)；F.obj M。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instHasWeakSheafifyOfHasSheafify`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] (J : CategoryTheory.GrothendieckTopology C)
 (A : Type u₂)   [inst_1 : CategoryTh…
· 使用定理 `SheafOfModules.Presentation.mapRelations_mapGenerators`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {J : CategoryTheory.GrothendieckTopo
logy C}   {R : CategoryTheory.Sheaf J RingCa…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Let `F` be a functor from sheaf of `R`-module to sheaf of `S`-module, if `F` pre
serves
colimits and `F.obj (unit R) ≅ unit S`, given a `P : Presentation M`, then we wi
ll get a
`Presentation (F.obj M)`.
-/
def Presentation.map : Presentation (F.obj M) :=
  presentationOfIsCokernelFree (P.mapRelations F η) (P.mapGenerators F η)
    (P.mapRelations_mapGenerators F η) <| by
    refine IsColimit.equivOfNatIsoOfIso
      (parallelPairIsoMk (mapFreeIso F _ η).symm (mapFreeIso F _ η).symm
        (by simp [Presentation.mapRelations]) (by simp)) _ _ ?_ (isColimitOfPreserves F P.isColimit)
    exact (Cocone.ext (Iso.refl _) <| by rintro (_ | _)
      <;> simp [Presentation.mapRelations, GeneratingSections.mapFreeHom, ← Functor.map_comp])
/-
**SheafOfModules.Presentation.map_** 是 Mathlib 中的一个定理，位于命名空间 `SheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Presentation.map_π_eq :
    (P.map F η).generators.π = (mapFreeIso F _ η).hom ≫ F.map (P.generators.π) :=
  (F.obj M).freeHomEquiv.symm_apply_eq.mpr rfl

end

section

variable [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- This structure contains the data of a family of objects `X i` which cover
the terminal object, and of a presentation of `M.over (X i)` for all `i`. -/
/-
**SheafOfModules.QuasicoherentData** 是 Mathlib 中的一个归纳类型，位于命名空间 `SheafOfModules`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {J : C
ategoryTheory.GrothendieckTopology C} →       {R : CategoryTheory.Sheaf J RingCa
t} →         [∀ (X : C), CategoryTheory.HasWeakSheafify (J.over X) AddCommGrpCat
] →           [∀ (X : C), (J.over X).WEqualsLocallyBijective AddCommGrpCat] →   
          SheafOfModules R → Type (max (max (max (u + 1) u₁) v₁) (w + 1))
参数：X : C；J.over X；X : C；J.over X；max (max (max (u + 1) u₁) v₁) (w + 1)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This structure contains the data of a family of objects `X i` which cover
the terminal object, and of a presentation of `M.over (X i)` for all `i`.
-/
structure QuasicoherentData (M : SheafOfModules.{u} R) where
  /-- the index type of the covering -/
  I : Type w
  /-- a family of objects which cover the terminal object -/
  X : I → C
  coversTop : J.CoversTop X
  /-- a presentation of the sheaf of modules `M.over (X i)` for any `i : I` -/
  presentation (i : I) : (M.over (X i)).Presentation

namespace QuasicoherentData

/-- Shrink the indexing type of `QuasicoherentData` into the universe of the site. -/
noncomputable
/-
**SheafOfModules.QuasicoherentData.shrink** 是 Mathlib 中的一个定义，位于命名空间 `SheafOfModu
les.QuasicoherentData`。
形式化陈述：shrink {M : SheafOfModules.{u} R} (q : M.QuasicoherentData) : Quasicoheren
tData.{u₁} M where I
参数：q : M.QuasicoherentData。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def shrink {M : SheafOfModules.{u} R} (q : M.QuasicoherentData) :
    QuasicoherentData.{u₁} M where
  I := Set.range q.X
  X i := q.X i.2.choose
  coversTop X := by
    refine J.superset_covering (fun Y hY H ↦ ?_) (q.coversTop X)
    obtain ⟨i, ⟨hi⟩⟩ := (Sieve.mem_ofObjects_iff ..).mp H
    exact ⟨⟨_, i, rfl⟩, ⟨hi ≫ eqToHom (by grind)⟩⟩
  presentation i := q.presentation i.2.choose

/-- If `M` is quasicoherent, it is locally generated by sections. -/
@[simps]
/-
**SheafOfModules.QuasicoherentData.localGeneratorsData** 是 Mathlib 中的一个定义，位于命名空间
 `SheafOfModules.QuasicoherentData`。
形式化陈述：localGeneratorsData {M : SheafOfModules.{u} R} (q : M.QuasicoherentData) :
 M.LocalGeneratorsData where I
参数：q : M.QuasicoherentData。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SheafOfModules.QuasicoherentData.coversTop`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {J : CategoryTheory.GrothendieckTopology C}   {R
 : CategoryTheory.Sheaf J RingCa…

--- 原说明 ---
If `M` is quasicoherent, it is locally generated by sections.
-/
def localGeneratorsData {M : SheafOfModules.{u} R} (q : M.QuasicoherentData) :
    M.LocalGeneratorsData where
  I := q.I
  X := q.X
  coversTop := q.coversTop
  generators i := (q.presentation i).generators

/-- A (local) presentation of a sheaf of module `M` is a finite presentation
if each given presentation of `M.over (X i)` is a finite presentation. -/
/-
**SheafOfModules.QuasicoherentData.IsFinitePresentation** 是 Mathlib 中的一个类，位于命名空间
 `SheafOfModules.QuasicoherentData`。
形式化陈述：IsFinitePresentation {M : SheafOfModules.{u} R} (q : M.QuasicoherentData) 
: Prop where isFinite_presentation (i : q.I) : (q.presentation i).IsFinite
参数：q : M.QuasicoherentData。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A (local) presentation of a sheaf of module `M` is a finite presentation
if each given presentation of `M.over (X i)` is a finite presentation.
-/
class IsFinitePresentation {M : SheafOfModules.{u} R} (q : M.QuasicoherentData) : Prop where
  isFinite_presentation (i : q.I) : (q.presentation i).IsFinite := by infer_instance

attribute [instance] IsFinitePresentation.isFinite_presentation

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**SheafOfModules.QuasicoherentData.** 是 Mathlib 中的一个实例，位于命名空间 `SheafOfModules.Qu
asicoherentData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {M : SheafOfModules.{u} R} (q : M.QuasicoherentData) [q.IsFinitePresentation] :
    q.localGeneratorsData.IsFiniteType where
  isFiniteType := by dsimp; infer_instance

end QuasicoherentData

/-- A sheaf of modules is quasi-coherent if it is locally the cokernel of a
morphism between coproducts of copies of the sheaf of rings. -/
/-
**SheafOfModules.IsQuasicoherent** 是 Mathlib 中的一个类，位于命名空间 `SheafOfModules`。
形式化陈述：IsQuasicoherent (M : SheafOfModules.{u} R) : Prop where nonempty_quasicohe
rentData : Nonempty (QuasicoherentData.{u₁} M)
参数：M : SheafOfModules.{u} R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A sheaf of modules is quasi-coherent if it is locally the cokernel of a
morphism between coproducts of copies of the sheaf of rings.
-/
class IsQuasicoherent (M : SheafOfModules.{u} R) : Prop where
  nonempty_quasicoherentData : Nonempty (QuasicoherentData.{u₁} M) := by infer_instance
/-
**SheafOfModules.QuasicoherentData.isQuasicoherent** 是 Mathlib 中的一个定理，位于命名空间 `Sh
eafOfModules.QuasicoherentData`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {J : CategoryT
heory.GrothendieckTopology C}   {R : CategoryTheory.Sheaf J RingCat} [inst_1 : ∀
 (X : C), CategoryTheory.HasWeakSheafify (J.over X) AddCommGrpCat]   [inst_2 : ∀
 (X : C), (J.over X).WEqualsLocallyBijective AddCommGrpCat] {M : SheafOfModules 
R}   (q : M.QuasicoherentData), M.IsQuasicoherent
参数：X : C；J.over X；X : C；J.over X；q : M.QuasicoherentData。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma QuasicoherentData.isQuasicoherent {M : SheafOfModules.{u} R} (q : M.QuasicoherentData) :
    M.IsQuasicoherent := ⟨⟨q.shrink⟩⟩

variable (R) in
@[inherit_doc IsQuasicoherent]
/-
**SheafOfModules.isQuasicoherent** 是 Mathlib 中的一个缩写定义，位于命名空间 `SheafOfModules`。
形式化陈述：isQuasicoherent : ObjectProperty (SheafOfModules.{u} R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev isQuasicoherent : ObjectProperty (SheafOfModules.{u} R) :=
  IsQuasicoherent
/-
**SheafOfModules.** 是 Mathlib 中的一个实例，位于命名空间 `SheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (M : (isQuasicoherent R).FullSubcategory) : M.obj.IsQuasicoherent :=
  M.property

/-- A sheaf of modules is finitely presented if it is locally the cokernel of a
morphism between coproducts of finitely many copies of the sheaf of rings. -/
/-
**SheafOfModules.IsFinitePresentation** 是 Mathlib 中的一个归纳类型，位于命名空间 `SheafOfModule
s`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {J : C
ategoryTheory.GrothendieckTopology C} →       {R : CategoryTheory.Sheaf J RingCa
t} →         [∀ (X : C), CategoryTheory.HasWeakSheafify (J.over X) AddCommGrpCat
] →           [∀ (X : C), (J.over X).WEqualsLocallyBijective AddCommGrpCat] → Sh
eafOfModules R → Prop
参数：X : C；J.over X；X : C；J.over X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A sheaf of modules is finitely presented if it is locally the cokernel of a
morphism between coproducts of finitely many copies of the sheaf of rings.
-/
class IsFinitePresentation (M : SheafOfModules.{u} R) : Prop where
  exists_quasicoherentData (M) :
    ∃ (σ : QuasicoherentData.{u₁} M), σ.IsFinitePresentation

variable (R) in
@[inherit_doc IsFinitePresentation]
/-
**SheafOfModules.isFinitePresentation** 是 Mathlib 中的一个缩写定义，位于命名空间 `SheafOfModule
s`。
形式化陈述：isFinitePresentation : ObjectProperty (SheafOfModules.{u} R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev isFinitePresentation : ObjectProperty (SheafOfModules.{u} R) :=
  IsFinitePresentation
/-
**SheafOfModules.** 是 Mathlib 中的一个实例，位于命名空间 `SheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (M : SheafOfModules.{u} R) [M.IsFinitePresentation] :
    M.IsQuasicoherent where
  nonempty_quasicoherentData :=
    ⟨(IsFinitePresentation.exists_quasicoherentData M).choose⟩
/-
**SheafOfModules.** 是 Mathlib 中的一个实例，位于命名空间 `SheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (M : SheafOfModules.{u} R) [M.IsFinitePresentation] :
    M.IsFiniteType where
  exists_localGeneratorsData := by
    obtain ⟨σ, _⟩ := IsFinitePresentation.exists_quasicoherentData M
    exact ⟨σ.localGeneratorsData, inferInstance⟩

section map

variable {D : Type u₂} [Category.{v₂, u₂} D] {K : GrothendieckTopology D}
  {S : Sheaf K RingCat.{u}} [∀ (X : D), (K.over X).WEqualsLocallyBijective AddCommGrpCat]

variable [∀ (X : C), HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ (X : D), HasSheafify (K.over X) AddCommGrpCat.{u}]

variable (G : D ⥤ C) [G.IsContinuous K J] [G.IsCocontinuous K J]
  (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{u} K J).obj R)

/-- The pushforward of `SheafOfModules.QuasicoherentData` along a continuous
and cocontinuous functor. -/
-- TODO: Remove the continuous assumption on `Over.post` here and below.
@[simps I X]
/-
**SheafOfModules.QuasicoherentData.pushforward** 是 Mathlib 中的一个定义，位于命名空间 `SheafO
fModules.QuasicoherentData`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {J : C
ategoryTheory.GrothendieckTopology C} →       {R : CategoryTheory.Sheaf J RingCa
t} →         [inst_1 : ∀ (X : C), CategoryTheory.HasWeakSheafify (J.over X) AddC
ommGrpCat] →           [inst_2 : ∀ (X : C), (J.over X).WEqualsLocallyBijective A
ddCommGrpCat] →             {D : Type u₂} →               [inst_3 : CategoryTheo
ry.Category.{v₂, u₂} D] →                 {K : CategoryTheory.GrothendieckTopolo
gy D} →                   {S : CategoryTheory.Sheaf K RingCat} →                
     [inst_4 : ∀ (X : D), (K.over X).WEqualsLocallyBijective AddCommGrpCat] →   
                    [∀ (X : C), CategoryTheory.HasSheafify (J.over X) AddCommGrp
Cat] →                         [inst_6 : ∀ (X : D), CategoryTheory.HasSheafify (
K.over X) AddCommGrpCat] →                           (G : CategoryTheory.Functor
 D C) →                             [inst_7 : G.IsContinuous K J] →             
                  [G.IsCocontinuous K J] →                                 (φ : 
S ⟶ (G.sheafPushforwardContinuous RingCat K J).obj R) →                         
          ((SheafOfModules.pushforward φ).obj (SheafOfModules.unit R) ≅ SheafOfM
odules.unit S) →                                     [inst_9 :                  
                       ∀ (X : D),                                           (Cat
egoryTheory.Over.post G).IsContinuous (K.over X) (J.over (G.obj X))] →          
                             (∀ (X : D) (Y : C) (f : G.obj X ⟶ Y),              
                             CategoryTheory.Limits.PreservesColimitsOfSize.{u, u
, max (max u u₁) v₁,                                               max (max u u₂
) v₂, max (max (u + 1) u₁) v₁, max (max (u + 1) u₂) v₂}                         
                    (SheafOfModules.pushforward                                 
              (((CategoryTheory.Over.forget X).sheafPushforwardContinuous RingCa
t                                                     (K.over X) K).map         
                                        φ))) →                                  
       {M : SheafOfModules R} →                                           M.Quas
icoherentData → ((SheafOfModules.pushforward φ).obj M).QuasicoherentData
参数：X : C；J.over X；X : C；J.over X；X : D；K.over X；X : C；J.over X；X : D；K.over X；G 
: CategoryTheory.Functor D C；φ : S ⟶ (G.sheafPushforwardContinuous RingCat K J).
obj R；(SheafOfModules.pushforward φ).obj (SheafOfModules.unit R) ≅ SheafOfModule
s.unit S；X : D；CategoryTheory.Over.post G；K.over X；J.over (G.obj X)；∀ (X : D) (Y
 : C) (f : G.obj X ⟶ Y),                                           CategoryTheor
y.Limits.PreservesColimitsOfSize.{u, u, max (max u u₁) v₁,                      
                         max (max u u₂) v₂, max (max (u + 1) u₁) v₁, max (max (u
 + 1) u₂) v₂}                                             (SheafOfModules.pushfo
rward                                               (((CategoryTheory.Over.forge
t X).sheafPushforwardContinuous RingCat                                         
            (K.over X) K).map                                                 φ)
)；(SheafOfModules.pushforward φ).obj M。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.instIsContinuousOverForgetOver`：∀ {C
 : Type u} [inst : CategoryTheory.Category.{v, u} C] (J : CategoryTheory.Grothen
dieckTopology C) (X : C),   (CategoryTheory.Over.forget …
-/
noncomputable def QuasicoherentData.pushforward (η : (pushforward φ).obj (unit R) ≅ unit S)
    [∀ (X : D), (Over.post G).IsContinuous (K.over X) (J.over _)]
    (h : ∀ (X : D) (Y : C) (f : G.obj X ⟶ Y),
      PreservesColimitsOfSize.{u, u} <|
      pushforward.{u} (R := (R.over Y)) (F := Over.post (X := X) G ⋙ Over.map f)
        (((Over.forget X).sheafPushforwardContinuous RingCat.{u} (K.over X) K).map φ))
    {M : SheafOfModules.{u} R} (P : M.QuasicoherentData) :
    QuasicoherentData ((pushforward φ).obj M) where
  I := Σ (X : D) (i : P.I), G.obj X ⟶ P.X i
  X i := i.1
  coversTop Y := by
    refine K.superset_covering ?_ <| G.cover_lift K _ (P.coversTop (G.obj Y))
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
/-
**SheafOfModules.isQuasicoherent_pushforward** 是 Mathlib 中的一个引理，位于命名空间 `SheafOfM
odules`。
形式化陈述：isQuasicoherent_pushforward (η : (pushforward φ).obj (unit R) ≅ unit S) [f
orall (X : D), (Over.post G).IsContinuous (K.over X) (J.over _)] (h : forall (X 
: D) (Y : C) (f : G.obj X ⟶ Y), PreservesColimitsOfSize.{u, u} pushforward.{u} (
R
参数：η : (pushforward φ).obj (unit R) ≅ unit S；X : D；Over.post G；K.over X；J.over _
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.instIsContinuousOverForgetOver`：∀ {C
 : Type u} [inst : CategoryTheory.Category.{v, u} C] (J : CategoryTheory.Grothen
dieckTopology C) (X : C),   (CategoryTheory.Over.forget …
· 使用定理 `CategoryTheory.GrothendieckTopology.instIsContinuousOverCompObjPostMapOv
er`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u_1} [ins
t_1 : CategoryTheory.Category.{v_1, u_1} D]   {J : CategoryTheor…
· 使用定理 `SheafOfModules.QuasicoherentData.isQuasicoherent`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {J : CategoryTheory.GrothendieckTopology C
}   {R : CategoryTheory.Sheaf J RingCa…
· 使用定理 `CategoryTheory.instHasWeakSheafifyOfHasSheafify`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] (J : CategoryTheory.GrothendieckTopology C)
 (A : Type u₂)   [inst_1 : CategoryTh…
· 使用定理 `SheafOfModules.IsQuasicoherent.nonempty_quasicoherentData`：∀ {C : Type u
₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {J : CategoryTheory.GrothendieckT
opology C}   {R : CategoryTheory.Sheaf J RingCa…
-/
lemma isQuasicoherent_pushforward (η : (pushforward φ).obj (unit R) ≅ unit S)
    [∀ (X : D), (Over.post G).IsContinuous (K.over X) (J.over _)]
    (h : ∀ (X : D) (Y : C) (f : G.obj X ⟶ Y),
      PreservesColimitsOfSize.{u, u} <|
      pushforward.{u} (R := (R.over Y)) (F := Over.post (X := X) G ⋙ Over.map f)
        (((Over.forget X).sheafPushforwardContinuous RingCat.{u} (K.over X) K).map φ))
    {M : SheafOfModules.{u} R} [IsQuasicoherent M] :
    IsQuasicoherent ((pushforward φ).obj M) :=
  IsQuasicoherent.nonempty_quasicoherentData.some.pushforward G φ η h |>.isQuasicoherent

set_option backward.isDefEq.respectTransparency false in
/-
**SheafOfModules.isQuasicoherent_pushforward_of_isLeftAdjoint** 是 Mathlib 中的一个引理
，位于命名空间 `SheafOfModules`。
形式化陈述：isQuasicoherent_pushforward_of_isLeftAdjoint (η : (pushforward φ).obj (uni
t R) ≅ unit S) [G.IsLeftAdjoint] [IsIso φ] [forall X, Functor.IsContinuous (Over
.post (X
参数：η : (pushforward φ).obj (unit R) ≅ unit S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SheafOfModules.isQuasicoherent_pushforward`：isQuasicoherent_pushforward 
(η : (pushforward φ).obj (unit R) ≅ unit S) [forall (X : D), (Over.post G).IsCon
tinuous (K.over X) (J.over _)] (…
· 使用引理 `CategoryTheory.Functor.isContinuous_comp`：isContinuous_comp (F₁ : C ⥤ D)
 (F₂ : D ⥤ E) (J : GrothendieckTopology C) (K : GrothendieckTopology D) (L : Gro
thendieckTopology E) [Functor.…
· 使用定理 `CategoryTheory.GrothendieckTopology.instIsContinuousOverMapOver`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] (J : CategoryTheory.Grothendie
ckTopology C) {X Y : C}   (f : X ⟶ Y), (CategoryTheor…
· 使用定理 `CategoryTheory.isCocontinuous_comp`：isCocontinuous_comp [G.IsCocontinuou
s J K] [G'.IsCocontinuous K L] : (G ⋙ G').IsCocontinuous J L where cover_lift h
· 使用定理 `CategoryTheory.GrothendieckTopology.instIsCocontinuousOverObjPostOver`：∀
 {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (J : CategoryTheory.Grot
hendieckTopology C) {D : Type u_1}   [inst_1 : CategoryTheo…
· 使用定理 `CategoryTheory.GrothendieckTopology.instIsCocontinuousOverMapOver`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] (J : CategoryTheory.Grothend
ieckTopology C) {X Y : C}   (f : X ⟶ Y), (CategoryTheor…
· 使用定理 `CategoryTheory.GrothendieckTopology.instIsContinuousOverForgetOver`：∀ {C
 : Type u} [inst : CategoryTheory.Category.{v, u} C] (J : CategoryTheory.Grothen
dieckTopology C) (X : C),   (CategoryTheory.Over.forget …
· 使用定理 `CategoryTheory.Over.instIsLeftAdjointMapOfHasPullbacksAlong`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y)   [CategoryT
heory.Limits.HasPullbacksAlong f], (CategoryTheor…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.GrothendieckTopology.instIsContinuousOverCompObjPostMapOv
er`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u_1} [ins
t_1 : CategoryTheory.Category.{v_1, u_1} D]   {J : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.instPreservesColimitsOfSizeOfIsLeftAdjoint`：∀ {C 
: Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_2, u_2} C]   [inst
_1 : CategoryTheory.Category.{v_3, u_3} D] (F : Categor…
-/
lemma isQuasicoherent_pushforward_of_isLeftAdjoint (η : (pushforward φ).obj (unit R) ≅ unit S)
    [G.IsLeftAdjoint] [IsIso φ]
    [∀ X, Functor.IsContinuous (Over.post (X := X) G) (K.over _) (J.over _)]
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

variable [∀ X, HasSheafify (J.over X) AddCommGrpCat]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat]

/-- Given a sheaf of `R`-modules `M` and a `Presentation M`, we may construct the quasi-coherent
data on the trivial cover. -/
@[simps]
/-
**SheafOfModules.Presentation.quasicoherentData** 是 Mathlib 中的一个定义，位于命名空间 `Sheaf
OfModules.Presentation`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [Categ
oryTheory.Limits.HasBinaryProducts C] →       {J : CategoryTheory.GrothendieckTo
pology C} →         {R : CategoryTheory.Sheaf J RingCat} →           [inst_2 : C
ategoryTheory.HasSheafify J AddCommGrpCat] →             [inst_3 : J.WEqualsLoca
llyBijective AddCommGrpCat] →               [inst_4 : ∀ (X : C), CategoryTheory.
HasSheafify (J.over X) AddCommGrpCat] →                 [inst_5 : ∀ (X : C), (J.
over X).WEqualsLocallyBijective AddCommGrpCat] →                   {M : SheafOfM
odules R} → M.Presentation → M.QuasicoherentData
参数：X : C；J.over X；X : C；J.over X。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instHasWeakSheafifyOfHasSheafify`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] (J : CategoryTheory.GrothendieckTopology C)
 (A : Type u₂)   [inst_1 : CategoryTh…
· 使用定理 `CategoryTheory.GrothendieckTopology.instIsContinuousOverForgetOver`：∀ {C
 : Type u} [inst : CategoryTheory.Category.{v, u} C] (J : CategoryTheory.Grothen
dieckTopology C) (X : C),   (CategoryTheory.Over.forget …

--- 原说明 ---
Given a sheaf of `R`-modules `M` and a `Presentation M`, we may construct the qu
asi-coherent
data on the trivial cover.
-/
def Presentation.quasicoherentData {M : SheafOfModules.{u} R} (P : Presentation M) :
    QuasicoherentData M where
  I := C
  X := id
  coversTop x := GrothendieckTopology.covering_of_eq_top J <| by
    rw [Sieve.ext_iff]
    intro _ f
    simp [Sieve.top_apply]
  presentation x := P.map (pushforward (𝟙 (R.over x))) (by rfl)

/-- If a sheaf of `R`-modules `M` has a presentation, then `M` is quasi-coherent. -/
/-
**SheafOfModules.Presentation.isQuasicoherent** 是 Mathlib 中的一个定理，位于命名空间 `SheafOf
Modules.Presentation`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheor
y.Limits.HasBinaryProducts C]   {J : CategoryTheory.GrothendieckTopology C} {R :
 CategoryTheory.Sheaf J RingCat}   [inst_2 : CategoryTheory.HasSheafify J AddCom
mGrpCat] [inst_3 : J.WEqualsLocallyBijective AddCommGrpCat]   [inst_4 : ∀ (X : C
), CategoryTheory.HasSheafify (J.over X) AddCommGrpCat]   [inst_5 : ∀ (X : C), (
J.over X).WEqualsLocallyBijective AddCommGrpCat] {M : SheafOfModules R} (P : M.P
resentation),   M.IsQuasicoherent
参数：X : C；J.over X；X : C；J.over X；P : M.Presentation。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instHasWeakSheafifyOfHasSheafify`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] (J : CategoryTheory.GrothendieckTopology C)
 (A : Type u₂)   [inst_1 : CategoryTh…

--- 原说明 ---
If a sheaf of `R`-modules `M` has a presentation, then `M` is quasi-coherent.
-/
theorem Presentation.isQuasicoherent {M : SheafOfModules.{u} R} (P : Presentation M) :
    IsQuasicoherent M where
  nonempty_quasicoherentData := Nonempty.intro (Presentation.quasicoherentData P)

/-- Mapping quasicoherent data under an isomorphism. -/
@[simps]
/-
**SheafOfModules.QuasicoherentData.ofIsIso** 是 Mathlib 中的一个定义，位于命名空间 `SheafOfMod
ules.QuasicoherentData`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {J : C
ategoryTheory.GrothendieckTopology C} →       {R : CategoryTheory.Sheaf J RingCa
t} →         [inst_1 : ∀ (X : C), CategoryTheory.HasSheafify (J.over X) AddCommG
rpCat] →           [inst_2 : ∀ (X : C), (J.over X).WEqualsLocallyBijective AddCo
mmGrpCat] →             {M N : SheafOfModules R} →               (f : M ⟶ N) → [
CategoryTheory.IsIso f] → M.QuasicoherentData → N.QuasicoherentData
参数：X : C；J.over X；X : C；J.over X；f : M ⟶ N。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Mapping quasicoherent data under an isomorphism.
-/
noncomputable def QuasicoherentData.ofIsIso {M N : SheafOfModules.{u} R} (f : M ⟶ N) [IsIso f]
    (σ : M.QuasicoherentData) : N.QuasicoherentData where
  I := σ.I
  X := σ.X
  coversTop := σ.coversTop
  presentation i := Presentation.ofIsIso (f.over (σ.X i)) (σ.presentation i)
/-
**SheafOfModules.** 是 Mathlib 中的一个实例，位于命名空间 `SheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (isQuasicoherent R).IsClosedUnderIsomorphisms where
  of_iso e := by
    intro ⟨⟨q⟩⟩
    exact ⟨⟨q.ofIsIso e.hom⟩⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**SheafOfModules.** 是 Mathlib 中的一个实例，位于命名空间 `SheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {M N : SheafOfModules.{u} R} (f : M ⟶ N) [IsIso f] (σ : M.QuasicoherentData)
    [σ.IsFinitePresentation] : (σ.ofIsIso f).IsFinitePresentation where
  isFinite_presentation i := by
    dsimp
    exact inferInstanceAs ((σ.presentation i).ofIsIso _).IsFinite
/-
**SheafOfModules.** 是 Mathlib 中的一个实例，位于命名空间 `SheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (isFinitePresentation R).IsClosedUnderIsomorphisms where
  of_iso e := by
    intro ⟨σ, hσ⟩
    exact ⟨σ.ofIsIso e.hom, inferInstance⟩

end

section bind

variable [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X Y, HasSheafify ((J.over X).over Y) AddCommGrpCat.{u}]
  [∀ X Y, ((J.over X).over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Given an cover `X` and a quasicoherent data for `M` restricted onto each `Mᵢ`, we may glue them
into a quasicoherent data of `M` itself. -/
/-
**SheafOfModules.QuasicoherentData.bind** 是 Mathlib 中的一个定义，位于命名空间 `SheafOfModule
s.QuasicoherentData`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {J : C
ategoryTheory.GrothendieckTopology C} →       [inst_1 : ∀ (X : C), CategoryTheor
y.HasSheafify (J.over X) AddCommGrpCat] →         [inst_2 : ∀ (X : C), (J.over X
).WEqualsLocallyBijective AddCommGrpCat] →           [inst_3 :               ∀ (
X : C) (Y : CategoryTheory.Over X), CategoryTheory.HasSheafify ((J.over X).over 
Y) AddCommGrpCat] →             [inst_4 :                 ∀ (X : C) (Y : Categor
yTheory.Over X), ((J.over X).over Y).WEqualsLocallyBijective AddCommGrpCat] →   
            {R : CategoryTheory.Sheaf J RingCat} →                 (M : SheafOfM
odules R) →                   {I : Type u} →                     (X : I → C) → J
.CoversTop X → ((i : I) → (M.over (X i)).QuasicoherentData) → M.QuasicoherentDat
a
参数：X : C；J.over X；X : C；J.over X；X : C；Y : CategoryTheory.Over X；(J.over X).over
 Y；X : C；Y : CategoryTheory.Over X；(J.over X).over Y；M : SheafOfModules R；X : I 
→ C；(i : I) → (M.over (X i)).QuasicoherentData。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an cover `X` and a quasicoherent data for `M` restricted onto each `Mᵢ`, w
e may glue them
into a quasicoherent data of `M` itself.
-/
noncomputable def QuasicoherentData.bind {R : Sheaf J RingCat.{u}}
    (M : SheafOfModules.{u} R) {I : Type u}
    (X : I → C) (hX : J.CoversTop X) (D : Π i, QuasicoherentData (M.over (X i))) :
    M.QuasicoherentData where
  I := (i : I) × (D i).I
  X ij := ((D ij.1).X ij.2).left
  coversTop := hX.over (fun i ↦ (D i).coversTop)
  presentation i :=
    letI e := pushforwardPushforwardEquivalence (Over.iteratedSliceEquiv ((D i.1).X i.2))
      (S := (R.over _).over _) (R := R.over _) (𝟙 _) (𝟙 _)
      (by ext : 2; exact R.1.map_id _) (by ext : 2; exact R.1.map_id _)
    (((D i.1).presentation i.2).map e.inverse (.refl _)).ofIsIso
      (e.fullyFaithfulFunctor.preimageIso
      (by exact e.counitIso.app ((M.over (X i.1)).over ((D i.1).X i.2)))).hom
/-
**SheafOfModules.IsQuasicoherent.of_coversTop** 是 Mathlib 中的一个定理，位于命名空间 `SheafOf
Modules.IsQuasicoherent`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {J : CategoryT
heory.GrothendieckTopology C}   [inst_1 : ∀ (X : C), CategoryTheory.HasSheafify 
(J.over X) AddCommGrpCat]   [inst_2 : ∀ (X : C), (J.over X).WEqualsLocallyBiject
ive AddCommGrpCat]   [inst_3 : ∀ (X : C) (Y : CategoryTheory.Over X), CategoryTh
eory.HasSheafify ((J.over X).over Y) AddCommGrpCat]   [inst_4 : ∀ (X : C) (Y : C
ategoryTheory.Over X), ((J.over X).over Y).WEqualsLocallyBijective AddCommGrpCat
]   {R : CategoryTheory.Sheaf J RingCat} (M : SheafOfModules R) {I : Type u} (X 
: I → C),   J.CoversTop X → ∀ [∀ (i : I), (M.over (X i)).IsQuasicoherent], M.IsQ
uasicoherent
参数：X : C；J.over X；X : C；J.over X；X : C；Y : CategoryTheory.Over X；(J.over X).over
 Y；X : C；Y : CategoryTheory.Over X；(J.over X).over Y；M : SheafOfModules R；X : I 
→ C；i : I；M.over (X i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instHasWeakSheafifyOfHasSheafify`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] (J : CategoryTheory.GrothendieckTopology C)
 (A : Type u₂)   [inst_1 : CategoryTh…
· 使用定理 `SheafOfModules.QuasicoherentData.isQuasicoherent`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {J : CategoryTheory.GrothendieckTopology C
}   {R : CategoryTheory.Sheaf J RingCa…
· 使用定理 `SheafOfModules.IsQuasicoherent.nonempty_quasicoherentData`：∀ {C : Type u
₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {J : CategoryTheory.GrothendieckT
opology C}   {R : CategoryTheory.Sheaf J RingCa…
-/
lemma IsQuasicoherent.of_coversTop {R : Sheaf J RingCat.{u}}
    (M : SheafOfModules.{u} R) {I : Type u}
    (X : I → C) (hX : J.CoversTop X) [∀ i, IsQuasicoherent (M.over (X i))] :
    IsQuasicoherent M :=
  (QuasicoherentData.bind M X hX fun _ ↦
    IsQuasicoherent.nonempty_quasicoherentData.some).isQuasicoherent

set_option backward.isDefEq.respectTransparency false in
/-
**SheafOfModules.isQuasicoherent_over** 是 Mathlib 中的一个引理，位于命名空间 `SheafOfModules`
。
形式化陈述：isQuasicoherent_over [HasPullbacks C] [HasBinaryProducts C] (M : SheafOfMo
dules.{u} R) (X : C) [IsQuasicoherent M] : IsQuasicoherent (M.over X)
参数：M : SheafOfModules.{u} R；X : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instHasWeakSheafifyOfHasSheafify`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] (J : CategoryTheory.GrothendieckTopology C)
 (A : Type u₂)   [inst_1 : CategoryTh…
· 使用引理 `SheafOfModules.isQuasicoherent_pushforward_of_isLeftAdjoint`：isQuasicohe
rent_pushforward_of_isLeftAdjoint (η : (pushforward φ).obj (unit R) ≅ unit S) [G
.IsLeftAdjoint] [IsIso φ] [forall X, Functor.IsCo…
· 使用定理 `CategoryTheory.GrothendieckTopology.instIsContinuousOverForgetOver`：∀ {C
 : Type u} [inst : CategoryTheory.Category.{v, u} C] (J : CategoryTheory.Grothen
dieckTopology C) (X : C),   (CategoryTheory.Over.forget …
· 使用定理 `CategoryTheory.GrothendieckTopology.instIsCocontinuousOverForgetOver`：∀ 
{C : Type u} [inst : CategoryTheory.Category.{v, u} C] (J : CategoryTheory.Groth
endieckTopology C) (X : C),   (CategoryTheory.Over.forget …
· 使用定理 `CategoryTheory.Over.instIsLeftAdjointForget`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] (X : C) [CategoryTheory.Limits.HasBinaryProducts C
],   (CategoryTheory.Over.forget …
· 使用定理 `CategoryTheory.Functor.instIsContinuousOfPreservesOneHypercovers`：∀ {C :
 Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Ca
tegoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.GrothendieckTopology.instPreservesOneHypercoversOverObjPo
stOver`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u_1} 
[inst_1 : CategoryTheory.Category.{v_1, u_1} D]   {J : CategoryTheor…
· 使用定理 `CategoryTheory.GrothendieckTopology.instPreservesOneHypercoversOverForge
tOver`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : CategoryThe
ory.GrothendieckTopology C} (X : C),   (CategoryTheory.Over.forget …
· 使用定理 `CategoryTheory.Over.hasLimitsOfShape_of_isConnected`：∀ {J : Type u'} [in
st : CategoryTheory.Category.{v', u'} J] {C : Type u} [inst_1 : CategoryTheory.C
ategory.{v, u} C]   {B : C} [CategoryTheo…
· 使用定理 `CategoryTheory.instIsConnectedWidePullbackShape`：∀ {J : Type u_1}, Categ
oryTheory.IsConnected (CategoryTheory.Limits.WidePullbackShape J)
-/
lemma isQuasicoherent_over
    [HasPullbacks C] [HasBinaryProducts C] (M : SheafOfModules.{u} R) (X : C) [IsQuasicoherent M] :
    IsQuasicoherent (M.over X) :=
  isQuasicoherent_pushforward_of_isLeftAdjoint _ _ (Iso.refl _)

end bind

end SheafOfModules

