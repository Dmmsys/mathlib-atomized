/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.Condensed.Discrete.Colimit
public import Mathlib.Condensed.Discrete.Module
/-!

# Characterizing discrete condensed sets and `R`-modules.

This file proves a characterization of discrete condensed sets, discrete condensed `R`-modules over
a ring `R`, discrete light condensed sets, and discrete light condensed `R`-modules over a ring `R`.
see `CondensedSet.isDiscrete_tfae`, `CondensedMod.isDiscrete_tfae`, `LightCondSet.isDiscrete_tfae`,
and `LightCondMod.isDiscrete_tfae`.

Informally, we can say: The following conditions characterize a condensed set `X` as discrete
(`CondensedSet.isDiscrete_tfae`):

1. There exists a set `X'` and an isomorphism `X ≅ cst X'`, where `cst X'` denotes the constant
   sheaf on `X'`.
2. The counit induces an isomorphism `cst X(*) ⟶ X`.
3. There exists a set `X'` and an isomorphism `X ≅ LocallyConstant · X'`.
4. The counit induces an isomorphism `LocallyConstant · X(*) ⟶ X`.
5. For every profinite set `S = limᵢSᵢ`, the canonical map `colimᵢX(Sᵢ) ⟶ X(S)` is an isomorphism.

The analogues for light condensed sets, condensed `R`-modules over any ring, and light
condensed `R`-modules are nearly identical (`CondensedMod.isDiscrete_tfae`,
`LightCondSet.isDiscrete_tfae`, and `LightCondMod.isDiscrete_tfae`).
-/

public section

universe u

open CategoryTheory Limits Functor FintypeCat

namespace Condensed

variable {C : Type*} [Category* C] [HasWeakSheafify (coherentTopology CompHaus.{u}) C]

/--
A condensed object is *discrete* if it is constant as a sheaf, i.e. isomorphic to a constant sheaf.
-/
/-
**Condensed.IsDiscrete** 是 Mathlib 中的一个缩写定义，位于命名空间 `Condensed`。
形式化陈述：IsDiscrete (X : Condensed.{u} C)
参数：X : Condensed.{u} C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A condensed object is *discrete* if it is constant as a sheaf, i.e. isomorphic t
o a constant sheaf.
-/
abbrev IsDiscrete (X : Condensed.{u} C) := X.IsConstant (coherentTopology CompHaus)

end Condensed

namespace CondensedSet

open CompHausLike.LocallyConstant

/-
**CondensedSet.mem_locallyConstant_essImage_of_isColimit_mapCocone** 是 Mathlib 中
的一个引理，位于命名空间 `CondensedSet`。
形式化陈述：mem_locallyConstant_essImage_of_isColimit_mapCocone (X : CondensedSet.{u})
 (h : forall S : Profinite.{u}, IsColimit <| (profiniteToCompHaus.op ⋙ X.obj).ma
pCocone S.asLimitCone.op) : CondensedSet.LocallyConstant.functor.essImage X
参数：X : CondensedSet.{u}；h : forall S : Profinite.{u}, IsColimit <| (profiniteToC
ompHaus.op ⋙ X.obj).mapCocone S.asLimitCone.op。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instPrecoherentOfFinitaryPreExtensiveOfPreregular`：∀ (C :
 Type u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.Finitar
yPreExtensive C]   [CategoryTheory.Preregular C], Cate…
· 使用定理 `CategoryTheory.FinitaryExtensive.toFinitaryPreExtensive`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.FinitaryExtensive C], 
  CategoryTheory.FinitaryPreExtensive C
· 使用定理 `CompHausLike.instFinitaryExtensiveOfHasExplicitPullbacksOfInclusions`：∀ 
{P : TopCat → Prop} [inst : CompHausLike.HasExplicitFiniteCoproducts P]   [CompH
ausLike.HasExplicitPullbacksOfInclusions P], CategoryTheor…
· 使用定理 `Profinite.instHasExplicitFiniteCoproductsTotallyDisconnectedSpaceCarrier
`：CompHausLike.HasExplicitFiniteCoproducts fun Y => TotallyDisconnectedSpace ↑Y
· 使用定理 `CompHausLike.instHasExplicitPullbacksOfInclusionsOfHasExplicitPullbacks`
：∀ {P : TopCat → Prop} [CompHausLike.HasExplicitPullbacks P] [inst : CompHausLik
e.HasExplicitFiniteCoproducts P],   CompHausLike.HasExplicitP…
· 使用定理 `Profinite.instHasExplicitPullbacksTotallyDisconnectedSpaceCarrier`：CompH
ausLike.HasExplicitPullbacks fun Y => TotallyDisconnectedSpace ↑Y
· 使用定理 `Profinite.instPreregular`：CategoryTheory.Preregular Profinite
· 使用定理 `CategoryTheory.Limits.Types.hasLimitsOfShape`：∀ {J : Type v} [inst : Cat
egoryTheory.Category.{w, v} J] [Small.{u, v} J],   CategoryTheory.Limits.HasLimi
tsOfShape J (Type u)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Presheaf.instPreservesFiniteProductsOppositeObjFunctorIsS
heafCoherentTopology`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1
} C] {A : Type u₃}   [inst_1 : CategoryTheory.Category.{v₃, u₃} A] [inst_2 : Cat
eg…
-/
lemma mem_locallyConstant_essImage_of_isColimit_mapCocone (X : CondensedSet.{u})
    (h : ∀ S : Profinite.{u}, IsColimit <|
      (profiniteToCompHaus.op ⋙ X.obj).mapCocone S.asLimitCone.op) :
    CondensedSet.LocallyConstant.functor.essImage X := by
  let e : CondensedSet.{u} ≌ Sheaf (coherentTopology Profinite) _ :=
    (Condensed.ProfiniteCompHaus.equivalence (Type (u + 1))).symm
  let i : (e.functor.obj X).obj ≅ (e.functor.obj (LocallyConstant.functor.obj _)).obj :=
    Condensed.isoLocallyConstantOfIsColimit _ h
  exact ⟨_, ⟨e.functor.preimageIso ((sheafToPresheaf _ _).preimageIso i.symm)⟩⟩

/--
`CondensedSet.LocallyConstant.functor` is left adjoint to the forgetful functor from condensed
sets to sets.
-/
/-
**CondensedSet.LocallyConstant.adjunction** 是 Mathlib 中的一个定义，位于命名空间 `CondensedSe
t.LocallyConstant`。
形式化陈述：CondensedSet.LocallyConstant.functor ⊣ Condensed.underlying (Type (u + 1))
参数：Type (u + 1)。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CompHaus.instHasPropTrue`：∀ (X : Type u_1) [inst : TopologicalSpace X], 
CompHausLike.HasProp (fun x => True) X
· 使用定理 `CompHaus.instHasExplicitFiniteCoproductsTrue`：CompHausLike.HasExplicitFi
niteCoproducts fun x => True
· 使用定理 `CompHaus.instHasExplicitPullbacksTrue`：CompHausLike.HasExplicitPullbacks
 fun x => True

--- 原说明 ---
`CondensedSet.LocallyConstant.functor` is left adjoint to the forgetful functor 
from condensed
sets to sets.
-/
noncomputable abbrev LocallyConstant.adjunction :
    CondensedSet.LocallyConstant.functor ⊣ Condensed.underlying (Type (u + 1)) :=
  CompHausLike.LocallyConstant.adjunction _ _

open Condensed

open CondensedSet.LocallyConstant List in
/-
**CondensedSet.isDiscrete_tfae** 是 Mathlib 中的一个定理，位于命名空间 `CondensedSet`。
形式化陈述：isDiscrete_tfae (X : CondensedSet.{u}) : TFAE [ X.IsDiscrete , IsIso ((Con
densed.discreteUnderlyingAdj _).counit.app X) , (Condensed.discrete _).essImage 
X , CondensedSet.LocallyConstant.functor.essImage X , IsIso (CondensedSet.Locall
yConstant.adjunction.counit.app X) , Sheaf.IsConstant (coherentTopology Profinit
e) ((Condensed.ProfiniteCompHaus.equivalence _).inverse.obj X) , forall S : Prof
inite.{u}, Nonempty (IsColimit <| (profiniteToCompHaus.op ⋙ X.obj).mapCocone S.a
sLimitCone.op) ]
参数：X : CondensedSet.{u}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instPrecoherentOfFinitaryPreExtensiveOfPreregular`：∀ (C :
 Type u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.Finitar
yPreExtensive C]   [CategoryTheory.Preregular C], Cate…
· 使用定理 `CategoryTheory.FinitaryExtensive.toFinitaryPreExtensive`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.FinitaryExtensive C], 
  CategoryTheory.FinitaryPreExtensive C
· 使用定理 `CompHausLike.instFinitaryExtensiveOfHasExplicitPullbacksOfInclusions`：∀ 
{P : TopCat → Prop} [inst : CompHausLike.HasExplicitFiniteCoproducts P]   [CompH
ausLike.HasExplicitPullbacksOfInclusions P], CategoryTheor…
· 使用定理 `CompHaus.instHasExplicitFiniteCoproductsTrue`：CompHausLike.HasExplicitFi
niteCoproducts fun x => True
· 使用定理 `CompHausLike.instHasExplicitPullbacksOfInclusionsOfHasExplicitPullbacks`
：∀ {P : TopCat → Prop} [CompHausLike.HasExplicitPullbacks P] [inst : CompHausLik
e.HasExplicitFiniteCoproducts P],   CompHausLike.HasExplicitP…
· 使用定理 `CompHaus.instHasExplicitPullbacksTrue`：CompHausLike.HasExplicitPullbacks
 fun x => True
· 使用定理 `CompHaus.instPreregular`：CategoryTheory.Preregular CompHaus
· 使用定理 `CategoryTheory.Functor.instPreservesLimitsOfShapeOfIsRightAdjoint`：∀ {J 
: Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1, 
u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Functor.isRightAdjoint_of_isEquivalence`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Types.instIsEquivalenceForgetTypeFun`：(CategoryTheory.for
get (Type u)).IsEquivalence
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.Limits.Types.hasColimitsOfShape`：∀ {J : Type v} [inst : C
ategoryTheory.Category.{w, v} J] [Small.{u, v} J],   CategoryTheory.Limits.HasCo
limitsOfShape J (Type u)
· 使用定理 `CategoryTheory.Functor.instPreservesColimitsOfShapeOfIsLeftAdjoint`：∀ {J
 : Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1,
 u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Functor.isLeftAdjoint_of_isEquivalence`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheor
y.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.instReflectsIsomorphismsForgetTypeFun`：(CategoryTheory.fo
rget (Type u_1)).ReflectsIsomorphisms
· 使用引理 `CategoryTheory.Sheaf.isConstant_iff_isIso_counit_app`：isConstant_iff_isI
so_counit_app [(constantSheaf J D).Faithful] [(constantSheaf J D).Full] (F : She
af J D) {T : C} (hT : IsTerminal T) : IsCo…
· 使用定理 `CondensedMod.LocallyConstant.instFaithfulSheafCompHausCoherentTopologyTy
peConstantSheaf`：(CategoryTheory.constantSheaf (CategoryTheory.coherentTopology 
CompHaus) (Type (u + 1))).Faithful
· 使用定理 `CondensedMod.LocallyConstant.instFullSheafCompHausCoherentTopologyTypeCo
nstantSheaf`：(CategoryTheory.constantSheaf (CategoryTheory.coherentTopology Comp
Haus) (Type (u + 1))).Full
· 使用定理 `instCompactSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Indiscrete
Topology X], CompactSpace X
· 使用定理 `instIndiscreteTopologyPUnit`：IndiscreteTopology PUnit.{u_1 + 1}
· 使用引理 `CategoryTheory.Sheaf.isConstant_iff_mem_essImage`：isConstant_iff_mem_ess
Image {L : D ⥤ Sheaf J D} {T : C} (hT : IsTerminal T) (adj : L ⊣ (sheafSections 
J D).obj ⟨T⟩) (F : Sheaf J D) : IsCons…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `CondensedSet.LocallyConstant.instFaithfulFunctor`：CondensedSet.LocallyCo
nstant.functor.Faithful
· 使用定理 `CondensedSet.LocallyConstant.instFullFunctor`：CondensedSet.LocallyConsta
nt.functor.Full
· 使用引理 `CategoryTheory.Sheaf.isConstant_iff_isIso_counit_app'`：isConstant_iff_is
Iso_counit_app' {L : D ⥤ Sheaf J D} {T : C} (hT : IsTerminal T) (adj : L ⊣ (shea
fSections J D).obj ⟨T⟩) [L.Faithful] [L.Ful…
· 使用定理 `Profinite.instHasExplicitFiniteCoproductsTotallyDisconnectedSpaceCarrier
`：CompHausLike.HasExplicitFiniteCoproducts fun Y => TotallyDisconnectedSpace ↑Y
· 使用定理 `Profinite.instHasExplicitPullbacksTotallyDisconnectedSpaceCarrier`：CompH
ausLike.HasExplicitPullbacks fun Y => TotallyDisconnectedSpace ↑Y
· 使用定理 `Profinite.instPreregular`：CategoryTheory.Preregular Profinite
· 使用定理 `CategoryTheory.Limits.Types.hasLimitsOfShape`：∀ {J : Type v} [inst : Cat
egoryTheory.Category.{w, v} J] [Small.{u, v} J],   CategoryTheory.Limits.HasLimi
tsOfShape J (Type u)
（共 49 条，此处仅展示前 30 条）
-/
theorem isDiscrete_tfae (X : CondensedSet.{u}) :
    TFAE
    [ X.IsDiscrete
    , IsIso ((Condensed.discreteUnderlyingAdj _).counit.app X)
    , (Condensed.discrete _).essImage X
    , CondensedSet.LocallyConstant.functor.essImage X
    , IsIso (CondensedSet.LocallyConstant.adjunction.counit.app X)
    , Sheaf.IsConstant (coherentTopology Profinite)
        ((Condensed.ProfiniteCompHaus.equivalence _).inverse.obj X)
    , ∀ S : Profinite.{u}, Nonempty
        (IsColimit <| (profiniteToCompHaus.op ⋙ X.obj).mapCocone S.asLimitCone.op)
    ] := by
  tfae_have 1 ↔ 2 := Sheaf.isConstant_iff_isIso_counit_app _ _ _
  tfae_have 1 ↔ 3 := ⟨fun ⟨h⟩ ↦ h, fun h ↦ ⟨h⟩⟩
  tfae_have 1 ↔ 4 := Sheaf.isConstant_iff_mem_essImage _ CompHaus.isTerminalPUnit adjunction _
  tfae_have 1 ↔ 5 :=
    have : functor.Faithful := inferInstance
    have : functor.Full := inferInstance
    -- These `have` statements above shouldn't be needed, but they are.
    Sheaf.isConstant_iff_isIso_counit_app' _ CompHaus.isTerminalPUnit adjunction _
  tfae_have 1 ↔ 6 :=
    (Sheaf.isConstant_iff_of_equivalence (coherentTopology Profinite)
      (coherentTopology CompHaus) profiniteToCompHaus Profinite.isTerminalPUnit
      CompHaus.isTerminalPUnit _).symm
  tfae_have 7 → 4 := fun h ↦
    mem_locallyConstant_essImage_of_isColimit_mapCocone X (fun S ↦ (h S).some)
  tfae_have 4 → 7 := fun ⟨Y, ⟨i⟩⟩ S ↦
    ⟨IsColimit.mapCoconeEquiv (isoWhiskerLeft profiniteToCompHaus.op
      ((sheafToPresheaf _ _).mapIso i))
      (Condensed.isColimitLocallyConstantPresheafDiagram Y S)⟩
  tfae_finish

end CondensedSet

namespace CondensedMod

variable (R : Type (u + 1)) [Ring R]

/-
**CondensedMod.isDiscrete_iff_isDiscrete_forget** 是 Mathlib 中的一个引理，位于命名空间 `Conde
nsedMod`。
形式化陈述：isDiscrete_iff_isDiscrete_forget (M : CondensedMod R) : M.IsDiscrete ↔ ((C
ondensed.forget R).obj M).IsDiscrete
参数：M : CondensedMod R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sheaf.isConstant_iff_forget`：∀ {C : Type u_1} [inst : Cat
egoryTheory.Category.{v_1, u_1} C] (J : CategoryTheory.GrothendieckTopology C)  
 {D : Type u_2} [inst_1 : Catego…
· 使用定理 `CategoryTheory.instPrecoherentOfFinitaryPreExtensiveOfPreregular`：∀ (C :
 Type u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.Finitar
yPreExtensive C]   [CategoryTheory.Preregular C], Cate…
· 使用定理 `CategoryTheory.FinitaryExtensive.toFinitaryPreExtensive`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.FinitaryExtensive C], 
  CategoryTheory.FinitaryPreExtensive C
· 使用定理 `CompHausLike.instFinitaryExtensiveOfHasExplicitPullbacksOfInclusions`：∀ 
{P : TopCat → Prop} [inst : CompHausLike.HasExplicitFiniteCoproducts P]   [CompH
ausLike.HasExplicitPullbacksOfInclusions P], CategoryTheor…
· 使用定理 `CompHaus.instHasExplicitFiniteCoproductsTrue`：CompHausLike.HasExplicitFi
niteCoproducts fun x => True
· 使用定理 `CompHausLike.instHasExplicitPullbacksOfInclusionsOfHasExplicitPullbacks`
：∀ {P : TopCat → Prop} [CompHausLike.HasExplicitPullbacks P] [inst : CompHausLik
e.HasExplicitFiniteCoproducts P],   CompHausLike.HasExplicitP…
· 使用定理 `CompHaus.instHasExplicitPullbacksTrue`：CompHausLike.HasExplicitPullbacks
 fun x => True
· 使用定理 `CompHaus.instPreregular`：CategoryTheory.Preregular CompHaus
· 使用定理 `CategoryTheory.Functor.instPreservesLimitsOfShapeOfIsRightAdjoint`：∀ {J 
: Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1, 
u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `ModuleCat.instIsRightAdjointForgetLinearMapIdCarrier`：∀ (R : Type u) [in
st : Ring R], (CategoryTheory.forget (ModuleCat R)).IsRightAdjoint
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `ModuleCat.hasColimitsOfShape`：∀ (R : Type w) [inst : Ring R] (J : Type u
) [inst_1 : CategoryTheory.Category.{v, u} J]   [CategoryTheory.Limits.HasColimi
tsOfShape J AddCom…
· 使用定理 `AddCommGrpCat.hasColimitsOfShape`：∀ {J : Type u} [inst : CategoryTheory.
Category.{v, u} J] [Small.{w, u} J],   CategoryTheory.Limits.HasColimitsOfShape 
J AddCommGrpCat
· 使用定理 `CategoryTheory.Limits.PreservesFilteredColimitsOfSize.preserves_filtered
_colimits`：∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type
 u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.isCofiltered_of_directed_ge_nonempty`：∀ (α : Type u) [ins
t : Preorder α] [IsCodirectedOrder α] [Nonempty α], CategoryTheory.IsCofiltered 
α
· 使用定理 `SemilatticeInf.instIsCodirectedOrder`：∀ {α : Type u_1} [inst : Semilatti
ceInf α], IsCodirectedOrder α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `ModuleCat.instReflectsIsomorphismsForgetLinearMapIdCarrier`：∀ {R : Type 
u} [inst : Ring R], (CategoryTheory.forget (ModuleCat R)).ReflectsIsomorphisms
· 使用定理 `CategoryTheory.Functor.isRightAdjoint_of_isEquivalence`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Types.instIsEquivalenceForgetTypeFun`：(CategoryTheory.for
get (Type u)).IsEquivalence
· 使用定理 `CategoryTheory.Limits.Types.hasColimitsOfShape`：∀ {J : Type v} [inst : C
ategoryTheory.Category.{w, v} J] [Small.{u, v} J],   CategoryTheory.Limits.HasCo
limitsOfShape J (Type u)
· 使用定理 `CategoryTheory.Functor.instPreservesColimitsOfShapeOfIsLeftAdjoint`：∀ {J
 : Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1,
 u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Functor.isLeftAdjoint_of_isEquivalence`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheor
y.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.instReflectsIsomorphismsForgetTypeFun`：(CategoryTheory.fo
rget (Type u_1)).ReflectsIsomorphisms
· 使用定理 `CategoryTheory.GrothendieckTopology.instPreservesSheafificationForgetOfP
reservesLimitsOfHasColimitsOfShapeOfPreservesColimitsOfShapeOppositeCoverOfHasLi
mitsOfShapeWalkingMulticospanOfReflectsIsomorphisms`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] (J : CategoryTheory.GrothendieckTopology C) {D : T
ype u_3}   [inst_1 : CategoryTheo…
· 使用定理 `CategoryTheory.Limits.instHasLimitsOfShapeOfHasLimitsOfSize`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTh
eory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `ModuleCat.hasLimits'`：∀ {R : Type u} [inst : Ring R], CategoryTheory.Lim
its.HasLimits (ModuleCat R)
· 使用定理 `CategoryTheory.hasSheafCompose_of_preservesMulticospan`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {A : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} A]   {B : Type u₃} [ins…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CondensedMod.LocallyConstant.instFaithfulModuleCatSheafCompHausCoherentT
opologyConstantSheaf`：∀ (R : Type (u + 1)) [inst : Ring R],   (CategoryTheory.co
nstantSheaf (CategoryTheory.coherentTopology CompHaus) (ModuleCat R)).Faithful
（共 38 条，此处仅展示前 30 条）
-/
lemma isDiscrete_iff_isDiscrete_forget (M : CondensedMod R) :
    M.IsDiscrete ↔ ((Condensed.forget R).obj M).IsDiscrete :=
  Sheaf.isConstant_iff_forget (coherentTopology CompHaus)
    (forget (ModuleCat R)) M CompHaus.isTerminalPUnit
/-
**CondensedMod.** 是 Mathlib 中的一个实例，位于命名空间 `CondensedMod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasLimitsOfSize.{u, u + 1} (ModuleCat.{u + 1} R) :=
  hasLimitsOfSizeShrink.{u, u + 1, u + 1, u + 1} _

open CondensedMod.LocallyConstant List in
/-
**CondensedMod.isDiscrete_tfae** 是 Mathlib 中的一个定理，位于命名空间 `CondensedMod`。
形式化陈述：isDiscrete_tfae (M : CondensedMod.{u} R) : TFAE [ M.IsDiscrete , IsIso ((C
ondensed.discreteUnderlyingAdj _).counit.app M) , (Condensed.discrete _).essImag
e M , (CondensedMod.LocallyConstant.functor R).essImage M , IsIso ((CondensedMod
.LocallyConstant.adjunction R).counit.app M) , Sheaf.IsConstant (coherentTopolog
y Profinite) ((Condensed.ProfiniteCompHaus.equivalence _).inverse.obj M) , foral
l S : Profinite.{u}, Nonempty (IsColimit <| (profiniteToCompHaus.op ⋙ M.obj).map
Cocone S.asLimitCone.op) ]
参数：M : CondensedMod.{u} R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instPrecoherentOfFinitaryPreExtensiveOfPreregular`：∀ (C :
 Type u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.Finitar
yPreExtensive C]   [CategoryTheory.Preregular C], Cate…
· 使用定理 `CategoryTheory.FinitaryExtensive.toFinitaryPreExtensive`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.FinitaryExtensive C], 
  CategoryTheory.FinitaryPreExtensive C
· 使用定理 `CompHausLike.instFinitaryExtensiveOfHasExplicitPullbacksOfInclusions`：∀ 
{P : TopCat → Prop} [inst : CompHausLike.HasExplicitFiniteCoproducts P]   [CompH
ausLike.HasExplicitPullbacksOfInclusions P], CategoryTheor…
· 使用定理 `CompHaus.instHasExplicitFiniteCoproductsTrue`：CompHausLike.HasExplicitFi
niteCoproducts fun x => True
· 使用定理 `CompHausLike.instHasExplicitPullbacksOfInclusionsOfHasExplicitPullbacks`
：∀ {P : TopCat → Prop} [CompHausLike.HasExplicitPullbacks P] [inst : CompHausLik
e.HasExplicitFiniteCoproducts P],   CompHausLike.HasExplicitP…
· 使用定理 `CompHaus.instHasExplicitPullbacksTrue`：CompHausLike.HasExplicitPullbacks
 fun x => True
· 使用定理 `CompHaus.instPreregular`：CategoryTheory.Preregular CompHaus
· 使用定理 `CategoryTheory.Functor.instPreservesLimitsOfShapeOfIsRightAdjoint`：∀ {J 
: Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1, 
u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `ModuleCat.instIsRightAdjointForgetLinearMapIdCarrier`：∀ (R : Type u) [in
st : Ring R], (CategoryTheory.forget (ModuleCat R)).IsRightAdjoint
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `ModuleCat.hasColimitsOfShape`：∀ (R : Type w) [inst : Ring R] (J : Type u
) [inst_1 : CategoryTheory.Category.{v, u} J]   [CategoryTheory.Limits.HasColimi
tsOfShape J AddCom…
· 使用定理 `AddCommGrpCat.hasColimitsOfShape`：∀ {J : Type u} [inst : CategoryTheory.
Category.{v, u} J] [Small.{w, u} J],   CategoryTheory.Limits.HasColimitsOfShape 
J AddCommGrpCat
· 使用定理 `CategoryTheory.Limits.PreservesFilteredColimitsOfSize.preserves_filtered
_colimits`：∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type
 u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.isCofiltered_of_directed_ge_nonempty`：∀ (α : Type u) [ins
t : Preorder α] [IsCodirectedOrder α] [Nonempty α], CategoryTheory.IsCofiltered 
α
· 使用定理 `SemilatticeInf.instIsCodirectedOrder`：∀ {α : Type u_1} [inst : Semilatti
ceInf α], IsCodirectedOrder α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `ModuleCat.instReflectsIsomorphismsForgetLinearMapIdCarrier`：∀ {R : Type 
u} [inst : Ring R], (CategoryTheory.forget (ModuleCat R)).ReflectsIsomorphisms
· 使用引理 `CategoryTheory.Sheaf.isConstant_iff_isIso_counit_app`：isConstant_iff_isI
so_counit_app [(constantSheaf J D).Faithful] [(constantSheaf J D).Full] (F : She
af J D) {T : C} (hT : IsTerminal T) : IsCo…
· 使用定理 `CondensedMod.LocallyConstant.instFaithfulModuleCatSheafCompHausCoherentT
opologyConstantSheaf`：∀ (R : Type (u + 1)) [inst : Ring R],   (CategoryTheory.co
nstantSheaf (CategoryTheory.coherentTopology CompHaus) (ModuleCat R)).Faithful
· 使用定理 `CondensedMod.LocallyConstant.instFullModuleCatSheafCompHausCoherentTopol
ogyConstantSheaf`：∀ (R : Type (u + 1)) [inst : Ring R],   (CategoryTheory.consta
ntSheaf (CategoryTheory.coherentTopology CompHaus) (ModuleCat R)).Full
· 使用定理 `instCompactSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Indiscrete
Topology X], CompactSpace X
· 使用定理 `instIndiscreteTopologyPUnit`：IndiscreteTopology PUnit.{u_1 + 1}
· 使用引理 `CategoryTheory.Sheaf.isConstant_iff_mem_essImage`：isConstant_iff_mem_ess
Image {L : D ⥤ Sheaf J D} {T : C} (hT : IsTerminal T) (adj : L ⊣ (sheafSections 
J D).obj ⟨T⟩) (F : Sheaf J D) : IsCons…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `CondensedMod.LocallyConstant.instFaithfulModuleCatFunctor`：∀ (R : Type (
u + 1)) [inst : Ring R], (CondensedMod.LocallyConstant.functor R).Faithful
· 使用定理 `CondensedMod.LocallyConstant.instFullModuleCatFunctor`：∀ (R : Type (u + 
1)) [inst : Ring R], (CondensedMod.LocallyConstant.functor R).Full
· 使用引理 `CategoryTheory.Sheaf.isConstant_iff_isIso_counit_app'`：isConstant_iff_is
Iso_counit_app' {L : D ⥤ Sheaf J D} {T : C} (hT : IsTerminal T) (adj : L ⊣ (shea
fSections J D).obj ⟨T⟩) [L.Faithful] [L.Ful…
· 使用定理 `Profinite.instHasExplicitFiniteCoproductsTotallyDisconnectedSpaceCarrier
`：CompHausLike.HasExplicitFiniteCoproducts fun Y => TotallyDisconnectedSpace ↑Y
· 使用定理 `Profinite.instHasExplicitPullbacksTotallyDisconnectedSpaceCarrier`：CompH
ausLike.HasExplicitPullbacks fun Y => TotallyDisconnectedSpace ↑Y
（共 67 条，此处仅展示前 30 条）
-/
theorem isDiscrete_tfae (M : CondensedMod.{u} R) :
    TFAE
    [ M.IsDiscrete
    , IsIso ((Condensed.discreteUnderlyingAdj _).counit.app M)
    , (Condensed.discrete _).essImage M
    , (CondensedMod.LocallyConstant.functor R).essImage M
    , IsIso ((CondensedMod.LocallyConstant.adjunction R).counit.app M)
    , Sheaf.IsConstant (coherentTopology Profinite)
        ((Condensed.ProfiniteCompHaus.equivalence _).inverse.obj M)
    , ∀ S : Profinite.{u}, Nonempty
        (IsColimit <| (profiniteToCompHaus.op ⋙ M.obj).mapCocone S.asLimitCone.op)
    ] := by
  tfae_have 1 ↔ 2 := Sheaf.isConstant_iff_isIso_counit_app _ _ _
  tfae_have 1 ↔ 3 := ⟨fun ⟨h⟩ ↦ h, fun h ↦ ⟨h⟩⟩
  tfae_have 1 ↔ 4 := Sheaf.isConstant_iff_mem_essImage _ CompHaus.isTerminalPUnit (adjunction R) _
  tfae_have 1 ↔ 5 :=
    have : (functor R).Faithful := inferInstance
    have : (functor R).Full := inferInstance
    -- These `have` statements above shouldn't be needed, but they are.
    Sheaf.isConstant_iff_isIso_counit_app' _ CompHaus.isTerminalPUnit (adjunction R) _
  tfae_have 1 ↔ 6 :=
    (Sheaf.isConstant_iff_of_equivalence (coherentTopology Profinite)
      (coherentTopology CompHaus) profiniteToCompHaus Profinite.isTerminalPUnit
      CompHaus.isTerminalPUnit _).symm
  tfae_have 7 → 1 := by
    intro h
    rw [isDiscrete_iff_isDiscrete_forget, ((CondensedSet.isDiscrete_tfae _).out 0 6 :)]
    intro S
    let : PreservesFilteredColimitsOfSize.{u, u} (forget (ModuleCat R)) :=
      preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
    exact ⟨isColimitOfPreserves (forget (ModuleCat R)) (h S).some⟩
  tfae_have 1 → 7 := by
    intro h S
    rw [isDiscrete_iff_isDiscrete_forget, ((CondensedSet.isDiscrete_tfae _).out 0 6 :)] at h
    let : ReflectsFilteredColimitsOfSize.{u, u} (forget (ModuleCat R)) :=
      reflectsFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
    exact ⟨isColimitOfReflects (forget (ModuleCat R)) (h S).some⟩
  tfae_finish

end CondensedMod

namespace LightCondensed

variable {C : Type*} [Category* C] [HasWeakSheafify (coherentTopology LightProfinite.{u}) C]

/--
A light condensed object is *discrete* if it is constant as a sheaf, i.e. isomorphic to a constant
sheaf.
-/
/-
**LightCondensed.IsDiscrete** 是 Mathlib 中的一个缩写定义，位于命名空间 `LightCondensed`。
形式化陈述：IsDiscrete (X : LightCondensed.{u} C)
参数：X : LightCondensed.{u} C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A light condensed object is *discrete* if it is constant as a sheaf, i.e. isomor
phic to a constant
sheaf.
-/
abbrev IsDiscrete (X : LightCondensed.{u} C) := X.IsConstant (coherentTopology LightProfinite)

end LightCondensed

namespace LightCondSet

/-
**LightCondSet.mem_locallyConstant_essImage_of_isColimit_mapCocone** 是 Mathlib 中
的一个引理，位于命名空间 `LightCondSet`。
形式化陈述：mem_locallyConstant_essImage_of_isColimit_mapCocone (X : LightCondSet.{u})
 (h : forall S : LightProfinite.{u}, IsColimit <| X.obj.mapCocone (coconeRightOp
OfCone S.asLimitCone)) : LightCondSet.LocallyConstant.functor.essImage X
参数：X : LightCondSet.{u}；h : forall S : LightProfinite.{u}, IsColimit <| X.obj.ma
pCocone (coconeRightOpOfCone S.asLimitCone)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Presheaf.instPreservesFiniteProductsOppositeObjFunctorIsS
heafCoherentTopology`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1
} C] {A : Type u₃}   [inst_1 : CategoryTheory.Category.{v₃, u₃} A] [inst_2 : Cat
eg…
· 使用定理 `LightProfinite.instPreregular`：CategoryTheory.Preregular LightProfinite
· 使用定理 `CompHausLike.instFinitaryExtensiveOfHasExplicitPullbacksOfInclusions`：∀ 
{P : TopCat → Prop} [inst : CompHausLike.HasExplicitFiniteCoproducts P]   [CompH
ausLike.HasExplicitPullbacksOfInclusions P], CategoryTheor…
· 使用定理 `LightProfinite.instHasExplicitFiniteCoproductsAndTotallyDisconnectedSpac
eCarrierSecondCountableTopology`：CompHausLike.HasExplicitFiniteCoproducts fun Y 
=> TotallyDisconnectedSpace ↑Y ∧ SecondCountableTopology ↑Y
· 使用定理 `CompHausLike.instHasExplicitPullbacksOfInclusionsOfHasExplicitPullbacks`
：∀ {P : TopCat → Prop} [CompHausLike.HasExplicitPullbacks P] [inst : CompHausLik
e.HasExplicitFiniteCoproducts P],   CompHausLike.HasExplicitP…
· 使用定理 `LightProfinite.instHasExplicitPullbacksAndTotallyDisconnectedSpaceCarrie
rSecondCountableTopology`：CompHausLike.HasExplicitPullbacks fun Y => TotallyDisc
onnectedSpace ↑Y ∧ SecondCountableTopology ↑Y
-/
lemma mem_locallyConstant_essImage_of_isColimit_mapCocone (X : LightCondSet.{u})
    (h : ∀ S : LightProfinite.{u}, IsColimit <|
      X.obj.mapCocone (coconeRightOpOfCone S.asLimitCone)) :
    LightCondSet.LocallyConstant.functor.essImage X := by
  let i : X.obj ≅ (LightCondSet.LocallyConstant.functor.obj _).obj :=
    LightCondensed.isoLocallyConstantOfIsColimit _ h
  exact ⟨_, ⟨((sheafToPresheaf _ _).preimageIso i.symm)⟩⟩

/--
`LightCondSet.LocallyConstant.functor` is left adjoint to the forgetful functor from light condensed
sets to sets.
-/
/-
**LightCondSet.LocallyConstant.adjunction** 是 Mathlib 中的一个定义，位于命名空间 `LightCondSe
t.LocallyConstant`。
形式化陈述：LightCondSet.LocallyConstant.functor ⊣ LightCondensed.underlying (Type u)
参数：Type u。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LightCondSet.LocallyConstant.instHasPropAndTotallyDisconnectedSpaceCarri
erSecondCountableTopologySubtypeToTop`：∀ (S : LightProfinite) (p : ↑S.toTop → Pr
op),   CompHausLike.HasProp (fun X => TotallyDisconnectedSpace ↑X ∧ SecondCounta
bleTopology ↑X) (Su…
· 使用定理 `LightProfinite.instHasPropAndTotallyDisconnectedSpaceCarrierSecondCounta
bleTopology`：∀ (X : Type u_1) [inst : TopologicalSpace X] [TotallyDisconnectedSp
ace X] [SecondCountableTopology X],   CompHausLike.HasProp (fun Y => Tota…
· 使用定理 `LightProfinite.instHasExplicitFiniteCoproductsAndTotallyDisconnectedSpac
eCarrierSecondCountableTopology`：CompHausLike.HasExplicitFiniteCoproducts fun Y 
=> TotallyDisconnectedSpace ↑Y ∧ SecondCountableTopology ↑Y
· 使用定理 `LightProfinite.instHasExplicitPullbacksAndTotallyDisconnectedSpaceCarrie
rSecondCountableTopology`：CompHausLike.HasExplicitPullbacks fun Y => TotallyDisc
onnectedSpace ↑Y ∧ SecondCountableTopology ↑Y

--- 原说明 ---
`LightCondSet.LocallyConstant.functor` is left adjoint to the forgetful functor 
from light condensed
sets to sets.
-/
noncomputable abbrev LocallyConstant.adjunction :
    LightCondSet.LocallyConstant.functor ⊣ LightCondensed.underlying (Type u) :=
  CompHausLike.LocallyConstant.adjunction _ _

open LightCondSet.LocallyConstant List in
/-
**LightCondSet.isDiscrete_tfae** 是 Mathlib 中的一个定理，位于命名空间 `LightCondSet`。
形式化陈述：isDiscrete_tfae (X : LightCondSet.{u}) : TFAE [ X.IsDiscrete , IsIso ((Lig
htCondensed.discreteUnderlyingAdj _).counit.app X) , (LightCondensed.discrete _)
.essImage X , LightCondSet.LocallyConstant.functor.essImage X , IsIso (LightCond
Set.LocallyConstant.adjunction.counit.app X) , forall S : LightProfinite.{u}, No
nempty (IsColimit <| X.obj.mapCocone (coconeRightOpOfCone S.asLimitCone)) ]
参数：X : LightCondSet.{u}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instHasWeakSheafifyOfHasSheafify`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] (J : CategoryTheory.GrothendieckTopology C)
 (A : Type u₂)   [inst_1 : CategoryTh…
· 使用定理 `CategoryTheory.instPrecoherentOfFinitaryPreExtensiveOfPreregular`：∀ (C :
 Type u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.Finitar
yPreExtensive C]   [CategoryTheory.Preregular C], Cate…
· 使用定理 `CategoryTheory.FinitaryExtensive.toFinitaryPreExtensive`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.FinitaryExtensive C], 
  CategoryTheory.FinitaryPreExtensive C
· 使用定理 `CompHausLike.instFinitaryExtensiveOfHasExplicitPullbacksOfInclusions`：∀ 
{P : TopCat → Prop} [inst : CompHausLike.HasExplicitFiniteCoproducts P]   [CompH
ausLike.HasExplicitPullbacksOfInclusions P], CategoryTheor…
· 使用定理 `LightProfinite.instHasExplicitFiniteCoproductsAndTotallyDisconnectedSpac
eCarrierSecondCountableTopology`：CompHausLike.HasExplicitFiniteCoproducts fun Y 
=> TotallyDisconnectedSpace ↑Y ∧ SecondCountableTopology ↑Y
· 使用定理 `CompHausLike.instHasExplicitPullbacksOfInclusionsOfHasExplicitPullbacks`
：∀ {P : TopCat → Prop} [CompHausLike.HasExplicitPullbacks P] [inst : CompHausLik
e.HasExplicitFiniteCoproducts P],   CompHausLike.HasExplicitP…
· 使用定理 `LightProfinite.instHasExplicitPullbacksAndTotallyDisconnectedSpaceCarrie
rSecondCountableTopology`：CompHausLike.HasExplicitPullbacks fun Y => TotallyDisc
onnectedSpace ↑Y ∧ SecondCountableTopology ↑Y
· 使用定理 `LightProfinite.instPreregular`：CategoryTheory.Preregular LightProfinite
· 使用引理 `CategoryTheory.Sheaf.isConstant_iff_isIso_counit_app`：isConstant_iff_isI
so_counit_app [(constantSheaf J D).Faithful] [(constantSheaf J D).Full] (F : She
af J D) {T : C} (hT : IsTerminal T) : IsCo…
· 使用定理 `LightCondMod.LocallyConstant.instFaithfulSheafLightProfiniteCoherentTopo
logyTypeConstantSheaf`：(CategoryTheory.constantSheaf (CategoryTheory.coherentTop
ology LightProfinite) (Type u)).Faithful
· 使用定理 `LightCondMod.LocallyConstant.instFullSheafLightProfiniteCoherentTopology
TypeConstantSheaf`：(CategoryTheory.constantSheaf (CategoryTheory.coherentTopolog
y LightProfinite) (Type u)).Full
· 使用定理 `instCompactSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Indiscrete
Topology X], CompactSpace X
· 使用定理 `instIndiscreteTopologyPUnit`：IndiscreteTopology PUnit.{u_1 + 1}
· 使用定理 `LightProfinite.instHasPropAndTotallyDisconnectedSpaceCarrierSecondCounta
bleTopology`：∀ (X : Type u_1) [inst : TopologicalSpace X] [TotallyDisconnectedSp
ace X] [SecondCountableTopology X],   CompHausLike.HasProp (fun Y => Tota…
· 使用引理 `CategoryTheory.Sheaf.isConstant_iff_mem_essImage`：isConstant_iff_mem_ess
Image {L : D ⥤ Sheaf J D} {T : C} (hT : IsTerminal T) (adj : L ⊣ (sheafSections 
J D).obj ⟨T⟩) (F : Sheaf J D) : IsCons…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `TotallySeparatedSpace.totallyDisconnectedSpace`：∀ (α : Type u) [inst : T
opologicalSpace α] [TotallySeparatedSpace α], TotallyDisconnectedSpace α
· 使用定理 `TotallySeparatedSpace.of_discrete`：∀ (α : Type u_3) [inst : TopologicalS
pace α] [DiscreteTopology α], TotallySeparatedSpace α
· 使用定理 `instDiscreteTopologyPUnit`：DiscreteTopology PUnit.{u_1 + 1}
· 使用定理 `TopologicalSpace.instSecondCountableTopologyOfLindelofSpaceOfPseudoMetri
zableSpace`：∀ (X : Type u_5) [inst : TopologicalSpace X] [LindelofSpace X] [Topo
logicalSpace.PseudoMetrizableSpace X],   SecondCountableTopology X
· 使用定理 `Countable.LindelofSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Cou
ntable X], LindelofSpace X
· 使用定理 `instCountablePUnit`：Countable PUnit.{u}
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `LightCondSet.LocallyConstant.instFaithfulFunctor`：LightCondSet.LocallyCo
nstant.functor.Faithful
· 使用定理 `LightCondSet.LocallyConstant.instFullFunctor`：LightCondSet.LocallyConsta
nt.functor.Full
· 使用引理 `CategoryTheory.Sheaf.isConstant_iff_isIso_counit_app'`：isConstant_iff_is
Iso_counit_app' {L : D ⥤ Sheaf J D} {T : C} (hT : IsTerminal T) (adj : L ⊣ (shea
fSections J D).obj ⟨T⟩) [L.Faithful] [L.Ful…
· 使用引理 `LightCondSet.mem_locallyConstant_essImage_of_isColimit_mapCocone`：mem_lo
callyConstant_essImage_of_isColimit_mapCocone (X : LightCondSet.{u}) (h : forall
 S : LightProfinite.{u}, IsColimit <| X.obj.mapCocone …
· 使用定理 `List.tfae_of_cycle`：tfae_of_cycle {a b} {l : List Prop} (h_chain : List.
IsChain (· -> ·) (a :: b :: l)) (h_last : getLastD l b -> a) : TFAE (a :: b :: l
)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
（共 31 条，此处仅展示前 30 条）
-/
theorem isDiscrete_tfae (X : LightCondSet.{u}) :
    TFAE
    [ X.IsDiscrete
    , IsIso ((LightCondensed.discreteUnderlyingAdj _).counit.app X)
    , (LightCondensed.discrete _).essImage X
    , LightCondSet.LocallyConstant.functor.essImage X
    , IsIso (LightCondSet.LocallyConstant.adjunction.counit.app X)
    , ∀ S : LightProfinite.{u}, Nonempty
        (IsColimit <| X.obj.mapCocone (coconeRightOpOfCone S.asLimitCone))
    ] := by
  tfae_have 1 ↔ 2 := Sheaf.isConstant_iff_isIso_counit_app _ _ _
  tfae_have 1 ↔ 3 := ⟨fun ⟨h⟩ ↦ h, fun h ↦ ⟨h⟩⟩
  tfae_have 1 ↔ 4 := Sheaf.isConstant_iff_mem_essImage _ LightProfinite.isTerminalPUnit adjunction X
  tfae_have 1 ↔ 5 :=
    have : functor.Faithful := inferInstance
    have : functor.Full := inferInstance
    -- These `have` statements above shouldn't be needed, but they are.
    Sheaf.isConstant_iff_isIso_counit_app' _ LightProfinite.isTerminalPUnit adjunction X
  tfae_have 6 → 4 := fun h ↦
    mem_locallyConstant_essImage_of_isColimit_mapCocone X (fun S ↦ (h S).some)
  tfae_have 4 → 6 := fun ⟨Y, ⟨i⟩⟩ S ↦
    ⟨IsColimit.mapCoconeEquiv ((sheafToPresheaf _ _).mapIso i)
      (LightCondensed.isColimitLocallyConstantPresheafDiagram Y S)⟩
  tfae_finish

end LightCondSet

namespace LightCondMod

variable (R : Type u) [Ring R]

/-
**LightCondMod.isDiscrete_iff_isDiscrete_forget** 是 Mathlib 中的一个引理，位于命名空间 `Light
CondMod`。
形式化陈述：isDiscrete_iff_isDiscrete_forget (M : LightCondMod R) : M.IsDiscrete ↔ ((L
ightCondensed.forget R).obj M).IsDiscrete
参数：M : LightCondMod R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sheaf.isConstant_iff_forget`：∀ {C : Type u_1} [inst : Cat
egoryTheory.Category.{v_1, u_1} C] (J : CategoryTheory.GrothendieckTopology C)  
 {D : Type u_2} [inst_1 : Catego…
· 使用定理 `CategoryTheory.instPrecoherentOfFinitaryPreExtensiveOfPreregular`：∀ (C :
 Type u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.Finitar
yPreExtensive C]   [CategoryTheory.Preregular C], Cate…
· 使用定理 `CategoryTheory.FinitaryExtensive.toFinitaryPreExtensive`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.FinitaryExtensive C], 
  CategoryTheory.FinitaryPreExtensive C
· 使用定理 `CompHausLike.instFinitaryExtensiveOfHasExplicitPullbacksOfInclusions`：∀ 
{P : TopCat → Prop} [inst : CompHausLike.HasExplicitFiniteCoproducts P]   [CompH
ausLike.HasExplicitPullbacksOfInclusions P], CategoryTheor…
· 使用定理 `LightProfinite.instHasExplicitFiniteCoproductsAndTotallyDisconnectedSpac
eCarrierSecondCountableTopology`：CompHausLike.HasExplicitFiniteCoproducts fun Y 
=> TotallyDisconnectedSpace ↑Y ∧ SecondCountableTopology ↑Y
· 使用定理 `CompHausLike.instHasExplicitPullbacksOfInclusionsOfHasExplicitPullbacks`
：∀ {P : TopCat → Prop} [CompHausLike.HasExplicitPullbacks P] [inst : CompHausLik
e.HasExplicitFiniteCoproducts P],   CompHausLike.HasExplicitP…
· 使用定理 `LightProfinite.instHasExplicitPullbacksAndTotallyDisconnectedSpaceCarrie
rSecondCountableTopology`：CompHausLike.HasExplicitPullbacks fun Y => TotallyDisc
onnectedSpace ↑Y ∧ SecondCountableTopology ↑Y
· 使用定理 `LightProfinite.instPreregular`：CategoryTheory.Preregular LightProfinite
· 使用定理 `CategoryTheory.instHasWeakSheafifyOfHasSheafify`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] (J : CategoryTheory.GrothendieckTopology C)
 (A : Type u₂)   [inst_1 : CategoryTh…
· 使用定理 `LightCondMod.LocallyConstant.instHasSheafifyLightProfiniteCoherentTopolo
gyModuleCat`：∀ (R : Type u) [inst : Ring R],   CategoryTheory.HasSheafify (Categ
oryTheory.coherentTopology LightProfinite) (ModuleCat R)
· 使用定理 `CategoryTheory.GrothendieckTopology.instPreservesSheafification_1`：∀ {C 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] (J : CategoryTheory.Groth
endieckTopology C) {A : Type u₃}   [inst_1 : CategoryTh…
· 使用定理 `instEssentiallySmallLightProfinite`：CategoryTheory.EssentiallySmall.{u, 
u, u + 1} LightProfinite
· 使用定理 `CategoryTheory.Limits.instHasLimitsOfShapeOfHasLimitsOfSize`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTh
eory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `ModuleCat.hasLimits'`：∀ {R : Type u} [inst : Ring R], CategoryTheory.Lim
its.HasLimits (ModuleCat R)
· 使用定理 `CategoryTheory.Limits.Types.hasLimitsOfShape`：∀ {J : Type v} [inst : Cat
egoryTheory.Category.{w, v} J] [Small.{u, v} J],   CategoryTheory.Limits.HasLimi
tsOfShape J (Type u)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.GrothendieckTopology.instPreservesSheafificationForgetOfP
reservesLimitsOfHasColimitsOfShapeOfPreservesColimitsOfShapeOppositeCoverOfHasLi
mitsOfShapeWalkingMulticospanOfReflectsIsomorphisms`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] (J : CategoryTheory.GrothendieckTopology C) {D : T
ype u_3}   [inst_1 : CategoryTheo…
· 使用定理 `ModuleCat.hasColimitsOfShape`：∀ (R : Type w) [inst : Ring R] (J : Type u
) [inst_1 : CategoryTheory.Category.{v, u} J]   [CategoryTheory.Limits.HasColimi
tsOfShape J AddCom…
· 使用定理 `AddCommGrpCat.hasColimitsOfShape`：∀ {J : Type u} [inst : CategoryTheory.
Category.{v, u} J] [Small.{w, u} J],   CategoryTheory.Limits.HasColimitsOfShape 
J AddCommGrpCat
· 使用定理 `CategoryTheory.Limits.PreservesFilteredColimitsOfSize.preserves_filtered
_colimits`：∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type
 u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.isCofiltered_of_directed_ge_nonempty`：∀ (α : Type u) [ins
t : Preorder α] [IsCodirectedOrder α] [Nonempty α], CategoryTheory.IsCofiltered 
α
· 使用定理 `SemilatticeInf.instIsCodirectedOrder`：∀ {α : Type u_1} [inst : Semilatti
ceInf α], IsCodirectedOrder α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `ModuleCat.instReflectsIsomorphismsForgetLinearMapIdCarrier`：∀ {R : Type 
u} [inst : Ring R], (CategoryTheory.forget (ModuleCat R)).ReflectsIsomorphisms
· 使用定理 `CategoryTheory.hasSheafCompose_of_preservesMulticospan`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {A : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} A]   {B : Type u₃} [ins…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Functor.instPreservesLimitsOfShapeOfIsRightAdjoint`：∀ {J 
: Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1, 
u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `ModuleCat.instIsRightAdjointForgetLinearMapIdCarrier`：∀ (R : Type u) [in
st : Ring R], (CategoryTheory.forget (ModuleCat R)).IsRightAdjoint
· 使用定理 `LightCondMod.LocallyConstant.instFaithfulModuleCatSheafLightProfiniteCoh
erentTopologyConstantSheaf`：∀ (R : Type u) [inst : Ring R],   (CategoryTheory.co
nstantSheaf (CategoryTheory.coherentTopology LightProfinite) (ModuleCat R)).Fait
hful
· 使用定理 `LightCondMod.LocallyConstant.instFullModuleCatSheafLightProfiniteCoheren
tTopologyConstantSheaf`：∀ (R : Type u) [inst : Ring R],   (CategoryTheory.consta
ntSheaf (CategoryTheory.coherentTopology LightProfinite) (ModuleCat R)).Full
（共 44 条，此处仅展示前 30 条）
-/
lemma isDiscrete_iff_isDiscrete_forget (M : LightCondMod R) :
    M.IsDiscrete ↔ ((LightCondensed.forget R).obj M).IsDiscrete :=
  Sheaf.isConstant_iff_forget (coherentTopology LightProfinite.{u})
    (forget (ModuleCat R)) M LightProfinite.isTerminalPUnit.{u}

open LightCondMod.LocallyConstant List in
/-
**LightCondMod.isDiscrete_tfae** 是 Mathlib 中的一个定理，位于命名空间 `LightCondMod`。
形式化陈述：isDiscrete_tfae (M : LightCondMod.{u} R) : TFAE [ M.IsDiscrete , IsIso ((L
ightCondensed.discreteUnderlyingAdj _).counit.app M) , (LightCondensed.discrete 
_).essImage M , (LightCondMod.LocallyConstant.functor R).essImage M , IsIso ((Li
ghtCondMod.LocallyConstant.adjunction R).counit.app M) , forall S : LightProfini
te.{u}, Nonempty (IsColimit <| M.obj.mapCocone (coconeRightOpOfCone S.asLimitCon
e)) ]
参数：M : LightCondMod.{u} R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instHasWeakSheafifyOfHasSheafify`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] (J : CategoryTheory.GrothendieckTopology C)
 (A : Type u₂)   [inst_1 : CategoryTh…
· 使用定理 `CategoryTheory.instPrecoherentOfFinitaryPreExtensiveOfPreregular`：∀ (C :
 Type u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.Finitar
yPreExtensive C]   [CategoryTheory.Preregular C], Cate…
· 使用定理 `CategoryTheory.FinitaryExtensive.toFinitaryPreExtensive`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.FinitaryExtensive C], 
  CategoryTheory.FinitaryPreExtensive C
· 使用定理 `CompHausLike.instFinitaryExtensiveOfHasExplicitPullbacksOfInclusions`：∀ 
{P : TopCat → Prop} [inst : CompHausLike.HasExplicitFiniteCoproducts P]   [CompH
ausLike.HasExplicitPullbacksOfInclusions P], CategoryTheor…
· 使用定理 `LightProfinite.instHasExplicitFiniteCoproductsAndTotallyDisconnectedSpac
eCarrierSecondCountableTopology`：CompHausLike.HasExplicitFiniteCoproducts fun Y 
=> TotallyDisconnectedSpace ↑Y ∧ SecondCountableTopology ↑Y
· 使用定理 `CompHausLike.instHasExplicitPullbacksOfInclusionsOfHasExplicitPullbacks`
：∀ {P : TopCat → Prop} [CompHausLike.HasExplicitPullbacks P] [inst : CompHausLik
e.HasExplicitFiniteCoproducts P],   CompHausLike.HasExplicitP…
· 使用定理 `LightProfinite.instHasExplicitPullbacksAndTotallyDisconnectedSpaceCarrie
rSecondCountableTopology`：CompHausLike.HasExplicitPullbacks fun Y => TotallyDisc
onnectedSpace ↑Y ∧ SecondCountableTopology ↑Y
· 使用定理 `LightProfinite.instPreregular`：CategoryTheory.Preregular LightProfinite
· 使用定理 `LightCondMod.LocallyConstant.instHasSheafifyLightProfiniteCoherentTopolo
gyModuleCat`：∀ (R : Type u) [inst : Ring R],   CategoryTheory.HasSheafify (Categ
oryTheory.coherentTopology LightProfinite) (ModuleCat R)
· 使用引理 `CategoryTheory.Sheaf.isConstant_iff_isIso_counit_app`：isConstant_iff_isI
so_counit_app [(constantSheaf J D).Faithful] [(constantSheaf J D).Full] (F : She
af J D) {T : C} (hT : IsTerminal T) : IsCo…
· 使用定理 `LightCondMod.LocallyConstant.instFaithfulModuleCatSheafLightProfiniteCoh
erentTopologyConstantSheaf`：∀ (R : Type u) [inst : Ring R],   (CategoryTheory.co
nstantSheaf (CategoryTheory.coherentTopology LightProfinite) (ModuleCat R)).Fait
hful
· 使用定理 `LightCondMod.LocallyConstant.instFullModuleCatSheafLightProfiniteCoheren
tTopologyConstantSheaf`：∀ (R : Type u) [inst : Ring R],   (CategoryTheory.consta
ntSheaf (CategoryTheory.coherentTopology LightProfinite) (ModuleCat R)).Full
· 使用定理 `instCompactSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Indiscrete
Topology X], CompactSpace X
· 使用定理 `instIndiscreteTopologyPUnit`：IndiscreteTopology PUnit.{u_1 + 1}
· 使用定理 `LightProfinite.instHasPropAndTotallyDisconnectedSpaceCarrierSecondCounta
bleTopology`：∀ (X : Type u_1) [inst : TopologicalSpace X] [TotallyDisconnectedSp
ace X] [SecondCountableTopology X],   CompHausLike.HasProp (fun Y => Tota…
· 使用引理 `CategoryTheory.Sheaf.isConstant_iff_mem_essImage`：isConstant_iff_mem_ess
Image {L : D ⥤ Sheaf J D} {T : C} (hT : IsTerminal T) (adj : L ⊣ (sheafSections 
J D).obj ⟨T⟩) (F : Sheaf J D) : IsCons…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `TotallySeparatedSpace.totallyDisconnectedSpace`：∀ (α : Type u) [inst : T
opologicalSpace α] [TotallySeparatedSpace α], TotallyDisconnectedSpace α
· 使用定理 `TotallySeparatedSpace.of_discrete`：∀ (α : Type u_3) [inst : TopologicalS
pace α] [DiscreteTopology α], TotallySeparatedSpace α
· 使用定理 `instDiscreteTopologyPUnit`：DiscreteTopology PUnit.{u_1 + 1}
· 使用定理 `TopologicalSpace.instSecondCountableTopologyOfLindelofSpaceOfPseudoMetri
zableSpace`：∀ (X : Type u_5) [inst : TopologicalSpace X] [LindelofSpace X] [Topo
logicalSpace.PseudoMetrizableSpace X],   SecondCountableTopology X
· 使用定理 `Countable.LindelofSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Cou
ntable X], LindelofSpace X
· 使用定理 `instCountablePUnit`：Countable PUnit.{u}
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `LightCondMod.LocallyConstant.instFaithfulModuleCatFunctor`：∀ (R : Type u
) [inst : Ring R], (LightCondMod.LocallyConstant.functor R).Faithful
· 使用定理 `LightCondMod.LocallyConstant.instFullModuleCatFunctor`：∀ (R : Type u) [i
nst : Ring R], (LightCondMod.LocallyConstant.functor R).Full
· 使用引理 `CategoryTheory.Sheaf.isConstant_iff_isIso_counit_app'`：isConstant_iff_is
Iso_counit_app' {L : D ⥤ Sheaf J D} {T : C} (hT : IsTerminal T) (adj : L ⊣ (shea
fSections J D).obj ⟨T⟩) [L.Faithful] [L.Ful…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LightCondMod.isDiscrete_iff_isDiscrete_forget`：isDiscrete_iff_isDiscrete
_forget (M : LightCondMod R) : M.IsDiscrete ↔ ((LightCondensed.forget R).obj M).
IsDiscrete
（共 46 条，此处仅展示前 30 条）
-/
theorem isDiscrete_tfae (M : LightCondMod.{u} R) :
    TFAE
    [ M.IsDiscrete
    , IsIso ((LightCondensed.discreteUnderlyingAdj _).counit.app M)
    , (LightCondensed.discrete _).essImage M
    , (LightCondMod.LocallyConstant.functor R).essImage M
    , IsIso ((LightCondMod.LocallyConstant.adjunction R).counit.app M)
    , ∀ S : LightProfinite.{u}, Nonempty
        (IsColimit <| M.obj.mapCocone (coconeRightOpOfCone S.asLimitCone))
    ] := by
  tfae_have 1 ↔ 2 := Sheaf.isConstant_iff_isIso_counit_app _ _ _
  tfae_have 1 ↔ 3 := ⟨fun ⟨h⟩ ↦ h, fun h ↦ ⟨h⟩⟩
  tfae_have 1 ↔ 4 := Sheaf.isConstant_iff_mem_essImage _
    LightProfinite.isTerminalPUnit (adjunction R) _
  tfae_have 1 ↔ 5 :=
    have : (functor R).Faithful := inferInstance
    have : (functor R).Full := inferInstance
    -- These `have` statements above shouldn't be needed, but they are.
    Sheaf.isConstant_iff_isIso_counit_app' _ LightProfinite.isTerminalPUnit (adjunction R) _
  tfae_have 6 → 1 := by
    intro h
    rw [isDiscrete_iff_isDiscrete_forget, ((LightCondSet.isDiscrete_tfae _).out 0 5 :)]
    intro S
    let : PreservesFilteredColimitsOfSize.{0, 0} (forget (ModuleCat R)) :=
      preservesFilteredColimitsOfSize_shrink.{0, u, 0, u} _
    exact ⟨isColimitOfPreserves (forget (ModuleCat R)) (h S).some⟩
  tfae_have 1 → 6 := by
    intro h S
    rw [isDiscrete_iff_isDiscrete_forget, ((LightCondSet.isDiscrete_tfae _).out 0 5 :)] at h
    let : ReflectsFilteredColimitsOfSize.{0, 0} (forget (ModuleCat R)) :=
      reflectsFilteredColimitsOfSize_shrink.{0, u, 0, u} _
    exact ⟨isColimitOfReflects (forget (ModuleCat R)) (h S).some⟩
  tfae_finish

end LightCondMod

