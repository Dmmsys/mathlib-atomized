/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.Condensed.TopComparison
public import Mathlib.Topology.Category.CompactlyGenerated
/-!

# The adjunction between condensed sets and topological spaces

This file defines the functor `condensedSetToTopCat : CondensedSet.{u} ⥤ TopCat.{u + 1}` which is
left adjoint to `topCatToCondensedSet : TopCat.{u + 1} ⥤ CondensedSet.{u}`. We prove that the counit
is bijective (but not in general an isomorphism) and conclude that the right adjoint is faithful.

The counit is an isomorphism for compactly generated spaces, and we conclude that the functor
`topCatToCondensedSet` is fully faithful when restricted to compactly generated spaces.
-/

@[expose] public section

universe u

open Condensed CondensedSet CategoryTheory CompHaus

variable (X : CondensedSet.{u})

set_option backward.privateInPublic true in
/-- Auxiliary definition to define the topology on `X(*)` for a condensed set `X`. -/
/-
**CondensedSet.coinducingCoprod** 是 Mathlib 中的一个定义，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition to define the topology on `X(*)` for a condensed set `X`.
-/
private def CondensedSet.coinducingCoprod :
    (Σ (i : (S : CompHaus.{u}) × X.obj.obj ⟨S⟩), i.fst) → X.obj.obj ⟨of PUnit⟩ :=
  fun ⟨⟨_, i⟩, s⟩ ↦ X.obj.map ((of PUnit.{u + 1}).const s).op i

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Let `X` be a condensed set. We define a topology on `X(*)` as the quotient topology of
all the maps from compact Hausdorff `S` spaces to `X(*)`, corresponding to elements of `X(S)`.
In other words, the topology coinduced by the map `CondensedSet.coinducingCoprod` above. -/
local instance : TopologicalSpace (X.obj.obj ⟨CompHaus.of PUnit⟩) :=
  TopologicalSpace.coinduced (coinducingCoprod X) inferInstance

/-- The object part of the functor `CondensedSet ⥤ TopCat` -/
/-
**CondensedSet.toTopCat** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：CondensedSet.toTopCat : TopCat.{u + 1}
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instCompactSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Indiscrete
Topology X], CompactSpace X
· 使用定理 `instIndiscreteTopologyPUnit`：IndiscreteTopology PUnit.{u_1 + 1}

--- 原说明 ---
The object part of the functor `CondensedSet ⥤ TopCat`
-/
abbrev CondensedSet.toTopCat : TopCat.{u + 1} := TopCat.of (X.obj.obj ⟨of PUnit⟩)

namespace CondensedSet

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**CondensedSet.continuous_coinducingCoprod** 是 Mathlib 中的一个引理，位于命名空间 `CondensedS
et`。
形式化陈述：continuous_coinducingCoprod {S : CompHaus.{u}} (x : X.obj.obj ⟨S⟩) : Conti
nuous fun a => (X.coinducingCoprod ⟨⟨S, x⟩, a⟩)
参数：x : X.obj.obj ⟨S⟩。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instCompactSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Indiscrete
Topology X], CompactSpace X
· 使用定理 `instIndiscreteTopologyPUnit`：IndiscreteTopology PUnit.{u_1 + 1}
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `continuous_sigma_iff`：continuous_sigma_iff {f : Sigma σ -> X} : Continuo
us f ↔ forall i, Continuous fun a => f ⟨i, a⟩
· 使用定理 `continuous_coinduced_rng`：continuous_coinduced_rng {t : TopologicalSpace
 α} : Continuous[t, coinduced f t] f
-/
lemma continuous_coinducingCoprod {S : CompHaus.{u}} (x : X.obj.obj ⟨S⟩) :
    Continuous fun a ↦ (X.coinducingCoprod ⟨⟨S, x⟩, a⟩) := by
  suffices ∀ (i : (T : CompHaus.{u}) × X.obj.obj ⟨T⟩),
      Continuous (fun (a : i.fst) ↦ X.coinducingCoprod ⟨i, a⟩) from this ⟨_, _⟩
  rw [← continuous_sigma_iff]
  apply continuous_coinduced_rng

variable {X} {Y : CondensedSet} (f : X ⟶ Y)

/-- The map part of the functor `CondensedSet ⥤ TopCat` -/
@[simps!]
/-
**CondensedSet.toTopCatMap** 是 Mathlib 中的一个定义，位于命名空间 `CondensedSet`。
形式化陈述：toTopCatMap : X.toTopCat ⟶ Y.toTopCat
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instCompactSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Indiscrete
Topology X], CompactSpace X
· 使用定理 `instIndiscreteTopologyPUnit`：IndiscreteTopology PUnit.{u_1 + 1}

--- 原说明 ---
The map part of the functor `CondensedSet ⥤ TopCat`
-/
def toTopCatMap : X.toTopCat ⟶ Y.toTopCat :=
  TopCat.ofHom
  { toFun := f.hom.app ⟨of PUnit⟩
    continuous_toFun := by
      rw [continuous_coinduced_dom]
      apply continuous_sigma
      intro ⟨S, x⟩
      simp only [Function.comp_apply, coinducingCoprod]
      rw [show (fun (a : S) ↦
          f.hom.app ⟨of PUnit⟩ (X.obj.map ((of PUnit.{u + 1}).const a).op x)) = _
        from funext fun a ↦ NatTrans.naturality_apply f.hom ((of PUnit.{u + 1}).const a).op x]
      exact continuous_coinducingCoprod Y _ }

end CondensedSet

/-- The functor `CondensedSet ⥤ TopCat` -/
@[simps]
/-
**condensedSetToTopCat** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：condensedSetToTopCat : CondensedSet.{u} ⥤ TopCat.{u + 1} where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `CondensedSet ⥤ TopCat`
-/
def condensedSetToTopCat : CondensedSet.{u} ⥤ TopCat.{u + 1} where
  obj X := X.toTopCat
  map f := toTopCatMap f

namespace CondensedSet

set_option backward.isDefEq.respectTransparency.types false in
/-- The counit of the adjunction `condensedSetToTopCat ⊣ topCatToCondensedSet` -/
/-
**CondensedSet.topCatAdjunctionCounit** 是 Mathlib 中的一个定义，位于命名空间 `CondensedSet`。
形式化陈述：topCatAdjunctionCounit (X : TopCat.{u + 1}) : X.toCondensedSet.toTopCat ⟶ 
X
参数：X : TopCat.{u + 1}。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instCompactSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Indiscrete
Topology X], CompactSpace X
· 使用定理 `instIndiscreteTopologyPUnit`：IndiscreteTopology PUnit.{u_1 + 1}

--- 原说明 ---
The counit of the adjunction `condensedSetToTopCat ⊣ topCatToCondensedSet`
-/
noncomputable def topCatAdjunctionCounit (X : TopCat.{u + 1}) : X.toCondensedSet.toTopCat ⟶ X :=
  TopCat.ofHom
  { toFun x := x.1 PUnit.unit
    continuous_toFun := by
      rw [continuous_coinduced_dom]
      continuity }

set_option backward.isDefEq.respectTransparency.types false in
/-- `simp`-normal form of the lemma that `@[simps]` would generate. -/
/-
**CondensedSet.topCatAdjunctionCounit_hom_apply** 是 Mathlib 中的一个定理，位于命名空间 `Conde
nsedSet`。
形式化陈述：∀ (X : TopCat) (x : C(PUnit.{u_1 + 1}, ↑X)), (TopCat.Hom.hom (CondensedSet
.topCatAdjunctionCounit X)) x = x PUnit.unit
参数：X : TopCat；x : C(PUnit.{u_1 + 1}, ↑X)；TopCat.Hom.hom (CondensedSet.topCatAdju
nctionCounit X)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`simp`-normal form of the lemma that `@[simps]` would generate.
-/
@[simp] lemma topCatAdjunctionCounit_hom_apply (X : TopCat) (x) :
    -- We have to specify here to not infer the `TopologicalSpace` instance on `C(PUnit, X)`,
    -- which suggests type synonyms are being unfolded too far somewhere.
    DFunLike.coe (F := @ContinuousMap C(PUnit, X) X (_) _)
        (TopCat.Hom.hom (topCatAdjunctionCounit X)) x =
      x PUnit.unit := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- The counit of the adjunction `condensedSetToTopCat ⊣ topCatToCondensedSet` is always bijective,
but not an isomorphism in general (the inverse isn't continuous unless `X` is compactly generated).
-/
/-
**CondensedSet.topCatAdjunctionCounitEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CondensedS
et`。
形式化陈述：topCatAdjunctionCounitEquiv (X : TopCat.{u + 1}) : X.toCondensedSet.toTopC
at ≃ X where toFun
参数：X : TopCat.{u + 1}。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instCompactSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Indiscrete
Topology X], CompactSpace X
· 使用定理 `instIndiscreteTopologyPUnit`：IndiscreteTopology PUnit.{u_1 + 1}

--- 原说明 ---
The counit of the adjunction `condensedSetToTopCat ⊣ topCatToCondensedSet` is al
ways bijective,
but not an isomorphism in general (the inverse isn't continuous unless `X` is co
mpactly generated).
-/
noncomputable def topCatAdjunctionCounitEquiv (X : TopCat.{u + 1}) :
    X.toCondensedSet.toTopCat ≃ X where
  toFun := topCatAdjunctionCounit X
  invFun x := ContinuousMap.const _ x
/-
**CondensedSet.topCatAdjunctionCounit_bijective** 是 Mathlib 中的一个引理，位于命名空间 `Conde
nsedSet`。
形式化陈述：topCatAdjunctionCounit_bijective (X : TopCat.{u + 1}) : Function.Bijective
 (topCatAdjunctionCounit X)
参数：X : TopCat.{u + 1}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
-/
lemma topCatAdjunctionCounit_bijective (X : TopCat.{u + 1}) :
    Function.Bijective (topCatAdjunctionCounit X) :=
  (topCatAdjunctionCounitEquiv X).bijective

set_option backward.isDefEq.respectTransparency.types false in
/-- The unit of the adjunction `condensedSetToTopCat ⊣ topCatToCondensedSet` -/
@[simps hom_app]
/-
**CondensedSet.topCatAdjunctionUnit** 是 Mathlib 中的一个定义，位于命名空间 `CondensedSet`。
形式化陈述：topCatAdjunctionUnit (X : CondensedSet.{u}) : X ⟶ X.toTopCat.toCondensedSe
t where hom
参数：X : CondensedSet.{u}。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instCompactSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Indiscrete
Topology X], CompactSpace X
· 使用定理 `instIndiscreteTopologyPUnit`：IndiscreteTopology PUnit.{u_1 + 1}

--- 原说明 ---
The unit of the adjunction `condensedSetToTopCat ⊣ topCatToCondensedSet`
-/
noncomputable def topCatAdjunctionUnit (X : CondensedSet.{u}) : X ⟶ X.toTopCat.toCondensedSet where
  hom := {
    app S := ↾fun x ↦ {
      toFun := fun s ↦ X.obj.map ((of PUnit.{u + 1}).const s).op x
      continuous_toFun := by
        suffices ∀ (i : (T : CompHaus.{u}) × X.obj.obj ⟨T⟩),
          Continuous (fun (a : i.fst) ↦ X.coinducingCoprod ⟨i, a⟩) from this ⟨_, _⟩
        rw [← continuous_sigma_iff]
        apply continuous_coinduced_rng }
    naturality := fun _ _ _ ↦ by
      ext
      simp only [TypeCat.Fun.toFun_apply,
        comp_apply, TopCat.toSheafCompHausLike_obj_map, ConcreteCategory.hom_ofHom,
        TypeCat.Fun.coe_mk, ← Functor.map_comp_apply]
      rfl }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The adjunction `condensedSetToTopCat ⊣ topCatToCondensedSet` -/
/-
**CondensedSet.topCatAdjunction** 是 Mathlib 中的一个定义，位于命名空间 `CondensedSet`。
形式化陈述：topCatAdjunction : condensedSetToTopCat.{u} ⊣ topCatToCondensedSet where u
nit.app
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The adjunction `condensedSetToTopCat ⊣ topCatToCondensedSet`
-/
noncomputable def topCatAdjunction : condensedSetToTopCat.{u} ⊣ topCatToCondensedSet where
  unit.app := topCatAdjunctionUnit
  counit.app := topCatAdjunctionCounit
  left_triangle_components Y := by
    ext
    change Y.obj.map (𝟙 _) _ = _
    simp

set_option backward.isDefEq.respectTransparency.types false in
/-
**CondensedSet.** 是 Mathlib 中的一个实例，位于命名空间 `CondensedSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : TopCat) : Epi (topCatAdjunction.counit.app X) := by
  rw [TopCat.epi_iff_surjective]
  exact (topCatAdjunctionCounit_bijective _).2
/-
**CondensedSet.** 是 Mathlib 中的一个实例，位于命名空间 `CondensedSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : topCatToCondensedSet.Faithful := topCatAdjunction.faithful_R_of_epi_counit_app

open CompactlyGenerated
/-
**CondensedSet.** 是 Mathlib 中的一个实例，位于命名空间 `CondensedSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : CondensedSet.{u}) : UCompactlyGeneratedSpace.{u, u + 1} X.toTopCat := by
  apply uCompactlyGeneratedSpace_of_continuous_maps
  intro Y _ f h
  rw [continuous_coinduced_dom, continuous_sigma_iff]
  exact fun ⟨S, s⟩ ↦ h S ⟨_, continuous_coinducingCoprod X _⟩
/-
**CondensedSet.** 是 Mathlib 中的一个实例，位于命名空间 `CondensedSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : CondensedSet.{u}) :
    UCompactlyGeneratedSpace.{u, u + 1} (condensedSetToTopCat.obj X) :=
  inferInstanceAs (UCompactlyGeneratedSpace.{u, u + 1} X.toTopCat)

/-- The functor from condensed sets to topological spaces lands in compactly generated spaces. -/
/-
**CondensedSet.condensedSetToCompactlyGenerated** 是 Mathlib 中的一个定义，位于命名空间 `Conde
nsedSet`。
形式化陈述：condensedSetToCompactlyGenerated : CondensedSet.{u} ⥤ CompactlyGenerated.{
u, u + 1} where obj X
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CondensedSet.instUCompactlyGeneratedSpaceCarrierObjTopCatCondensedSetToT
opCat`：∀ (X : CondensedSet), UCompactlyGeneratedSpace ↑(condensedSetToTopCat.obj
 X)

--- 原说明 ---
The functor from condensed sets to topological spaces lands in compactly generat
ed spaces.
-/
def condensedSetToCompactlyGenerated : CondensedSet.{u} ⥤ CompactlyGenerated.{u, u + 1} where
  obj X := CompactlyGenerated.of (condensedSetToTopCat.obj X)
  map f := InducedCategory.homMk (toTopCatMap f)

/--
The functor from topological spaces to condensed sets restricted to compactly generated spaces.
-/
/-
**CondensedSet.compactlyGeneratedToCondensedSet** 是 Mathlib 中的一个定义，位于命名空间 `Conde
nsedSet`。
形式化陈述：compactlyGeneratedToCondensedSet : CompactlyGenerated.{u, u + 1} ⥤ Condens
edSet.{u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor from topological spaces to condensed sets restricted to compactly ge
nerated spaces.
-/
noncomputable def compactlyGeneratedToCondensedSet :
    CompactlyGenerated.{u, u + 1} ⥤ CondensedSet.{u} :=
  compactlyGeneratedToTop ⋙ topCatToCondensedSet


/--
The adjunction `condensedSetToTopCat ⊣ topCatToCondensedSet` restricted to compactly generated
spaces.
-/
/-
**CondensedSet.compactlyGeneratedAdjunction** 是 Mathlib 中的一个定义，位于命名空间 `Condensed
Set`。
形式化陈述：compactlyGeneratedAdjunction : condensedSetToCompactlyGenerated ⊣ compactl
yGeneratedToCondensedSet
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The adjunction `condensedSetToTopCat ⊣ topCatToCondensedSet` restricted to compa
ctly generated
spaces.
-/
noncomputable def compactlyGeneratedAdjunction :
    condensedSetToCompactlyGenerated ⊣ compactlyGeneratedToCondensedSet :=
  topCatAdjunction.restrictFullyFaithful (iC := 𝟭 _) (iD := compactlyGeneratedToTop)
    (Functor.FullyFaithful.id _) fullyFaithfulCompactlyGeneratedToTop
    (Iso.refl _) (Iso.refl _)

/--
The counit of the adjunction `condensedSetToCompactlyGenerated ⊣ compactlyGeneratedToCondensedSet`
is a homeomorphism.
-/
/-
**CondensedSet.compactlyGeneratedAdjunctionCounitHomeo** 是 Mathlib 中的一个定义，位于命名空间
 `CondensedSet`。
形式化陈述：compactlyGeneratedAdjunctionCounitHomeo (X : TopCat.{u + 1}) [UCompactlyGe
neratedSpace.{u} X] : X.toCondensedSet.toTopCat ≃ₜ X where toEquiv
参数：X : TopCat.{u + 1}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The counit of the adjunction `condensedSetToCompactlyGenerated ⊣ compactlyGenera
tedToCondensedSet`
is a homeomorphism.
-/
noncomputable def compactlyGeneratedAdjunctionCounitHomeo
    (X : TopCat.{u + 1}) [UCompactlyGeneratedSpace.{u} X] :
    X.toCondensedSet.toTopCat ≃ₜ X where
  toEquiv := topCatAdjunctionCounitEquiv X
  continuous_invFun := by
    apply continuous_from_uCompactlyGeneratedSpace
    exact fun _ _ ↦ continuous_coinducingCoprod X.toCondensedSet _

/--
The counit of the adjunction `condensedSetToCompactlyGenerated ⊣ compactlyGeneratedToCondensedSet`
is an isomorphism.
-/
/-
**CondensedSet.compactlyGeneratedAdjunctionCounitIso** 是 Mathlib 中的一个定义，位于命名空间 `
CondensedSet`。
形式化陈述：compactlyGeneratedAdjunctionCounitIso (X : CompactlyGenerated.{u, u + 1}) 
: condensedSetToCompactlyGenerated.obj (compactlyGeneratedToCondensedSet.obj X) 
≅ X
参数：X : CompactlyGenerated.{u, u + 1}。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CompactlyGenerated.is_compactly_generated`：∀ (self : CompactlyGenerated)
, UCompactlyGeneratedSpace ↑self.toTop

--- 原说明 ---
The counit of the adjunction `condensedSetToCompactlyGenerated ⊣ compactlyGenera
tedToCondensedSet`
is an isomorphism.
-/
noncomputable def compactlyGeneratedAdjunctionCounitIso (X : CompactlyGenerated.{u, u + 1}) :
    condensedSetToCompactlyGenerated.obj (compactlyGeneratedToCondensedSet.obj X) ≅ X :=
  isoOfHomeo (compactlyGeneratedAdjunctionCounitHomeo X.toTop)
/-
**CondensedSet.** 是 Mathlib 中的一个实例，位于命名空间 `CondensedSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsIso compactlyGeneratedAdjunction.counit := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  exact inferInstanceAs (IsIso (compactlyGeneratedAdjunctionCounitIso X).hom)

/--
The functor from topological spaces to condensed sets restricted to compactly generated spaces
is fully faithful.
-/
/-
**CondensedSet.fullyFaithfulCompactlyGeneratedToCondensedSet** 是 Mathlib 中的一个定义，
位于命名空间 `CondensedSet`。
形式化陈述：fullyFaithfulCompactlyGeneratedToCondensedSet : compactlyGeneratedToConden
sedSet.FullyFaithful
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CondensedSet.instIsIsoFunctorCompactlyGeneratedCounitCompactlyGeneratedA
djunction`：CategoryTheory.IsIso CondensedSet.compactlyGeneratedAdjunction.counit

--- 原说明 ---
The functor from topological spaces to condensed sets restricted to compactly ge
nerated spaces
is fully faithful.
-/
noncomputable def fullyFaithfulCompactlyGeneratedToCondensedSet :
    compactlyGeneratedToCondensedSet.FullyFaithful :=
  compactlyGeneratedAdjunction.fullyFaithfulROfIsIsoCounit

end CondensedSet

